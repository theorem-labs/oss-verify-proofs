(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
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
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM15.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MallocTree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MallocKit_A.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM11.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM09. Import SM09.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Malloc.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM08. Import SM08.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM01. Import SM01.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Malloc_fp.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM14.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require ASlot_W1.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Common Require RunDraw.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM13.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM12.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MallocFacts_A.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MM08.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require F_malloc_entry.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MallocFacts_AM.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require MallocFacts_AS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ASlot_W2.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Tac. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Image. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Walk. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import ITree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Decode. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import MallocKit_A.
Import MM11. Import MM11.MallocKit_AB.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM01. Import SM01. Import SM01.Monad.
Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import Malloc_fp.
Import MM14. Import MM14.MallocKit_A2.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import ASlot_W1.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.

Section CANSEC1. Context {rc : runConstT}.
Definition ta_frame (s1v s2v rav : word) (j0 j1 : list byte) : list cell :=
  [CB 64 j0; C8 s2v; C8 s1v; CB 8 j1; C8 rav].

Section FIN.
Variables (st : mstate) (m : mem) (g : aptr) (mask : Z) (lo : Z).
Let G := conc st g.
Hypothesis MSL : meta_slot st g.
Hypothesis MASK : 0 < mask < 2^32.
Hypothesis CLO : ATOP <= lo.
End FIN.



End CANSEC1.
End ASlot_W2.

Module F_ntf_B.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Tac. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Image. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Walk. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import MallocTree.
Import MM13. Import MM13.MallocKit_B.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition fm_facts (st : mstate) (g : aptr) : Prop :=
  forall head, c_free_meta_head (ctx st) = Some head ->
    head <> g /\ meta_slot st head /\
    exists pv, m_prev (get_meta_rec st head) = Some pv /\ pv <> g /\ meta_slot st pv.

Lemma meta_word_meta0 : meta_word meta0 = 0. Proof. reflexivity. Qed.

End CANSEC1.
End F_ntf_B.

Module F_am_A.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Tac. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Image. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Walk. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import MallocTree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
Import MM13. Import MM13.MallocKit_B. Import MM12. Import MM12.MallocModel_B. Import MM14. Import MM14.MallocKit_B3. Import F_ntf_B.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.


Section CANSEC1. Context {rc : runConstT}.
Definition am_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
  lo <= a < sp
  \/ CTX <= a < CTX + 928
  \/ exists rid r, (s_regions st) !! rid = Some r /\ r_kind r <> RKGroup /\ lr_lo r <= a < r_base r + round_up_pg (r_len r).

Lemma am_fp_alloc_fp st lo sp a : am_fp st lo sp a -> alloc_fp (fun k => k <> RKGroup) st lo sp a.
Proof. unfold am_fp, alloc_fp. tauto. Qed.
Lemma am_fp_stack st lo sp a : lo <= a < sp -> am_fp st lo sp a.
Proof. intros; left; assumption. Qed.
Lemma am_fp_ctx st lo sp a : CTX <= a < CTX + 928 -> am_fp st lo sp a.
Proof. intros; right; left; assumption. Qed.
Lemma am_fp_region st lo sp a rid r : (s_regions st) !! rid = Some r -> r_kind r <> RKGroup ->
  lr_lo r <= a < r_base r + round_up_pg (r_len r) -> am_fp st lo sp a.
Proof. intros; right; right. exists rid, r. auto. Qed.
Lemma am_fp_not_errno st lo sp a : am_fp st lo sp a -> regions_wf st -> ATOP <= lo ->
  ~ (errno_addr (Z_to_bv 64 0x1a620) <= a < errno_addr (Z_to_bv 64 0x1a620) + 4).
Proof.
  intros [H|[H|(rid & r & Hr & _ & H)]] (_ & WR & _) LO; unfold CTX in *; rewrite ?unsigned_lit by lia; try lia.
  destruct (WR _ _ Hr) as (_ & _ & _ & RBC & RF). destruct (reserved_disjoint _ _ RF) as [_ D2].
  pose proof (lr_lo_ge r). atop_facts. lia.
Qed.
Lemma am_fp_same st st' lo sp a : s_regions st' = s_regions st -> am_fp st' lo sp a <-> am_fp st lo sp a.
Proof. intros ER. unfold am_fp. rewrite ER. tauto. Qed.

Definition am_took (st : mstate) (q : aptr) (cnt : Z) : mstate :=
  upd_meta q clr_links (upd_ctx (fun c => set_avail_meta (Some (aadd q META_SIZE)) (set_avail_meta_count cnt c)) st).

End CANSEC1.
End F_am_A.

Module F_am_K.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Tac. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Image. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Walk. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import MallocTree.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
Import MM13. Import MM13.MallocKit_B. Import MM12. Import MM12.MallocModel_B. Import MM14. Import MM14.MallocKit_B3. Import F_ntf_B.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.


Section CANSEC1. Context {rc : runConstT}.
Lemma zeros_length n : length (zeros n) = n. Proof. unfold zeros. apply repeat_length. Qed.

Lemma le8_zero : le8 (wz 0) = zeros 8. Proof. reflexivity. Qed.
Lemma le4_zero : le4 (wz 0) = zeros 4. Proof. reflexivity. Qed.

Lemma meta_cells_meta0 st : meta_cells st meta0 = [C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0)].
Proof. reflexivity. Qed.


Definition carve_st (st : mstate) (p : aptr) : mstate :=
  let st1 := upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st in
  let st2 := match c_meta_area_tail (ctx st1) with
             | Some tl => set_areas (<[tl := match (s_areas st1) !! tl with
                                              | Some a => mkArea (a_check a) (Some p) (a_nslots a)
                                              | None => mkArea 0 (Some p) 0 end]> (s_areas st1)) st1
             | None => upd_ctx (set_meta_area_head (Some p)) st1
             end in
  let st3 := upd_ctx (set_meta_area_tail (Some p)) st2 in
  let old := default (mkArea 0 None 0) ((s_areas st3) !! p) in
  set_areas (<[p := mkArea (c_secret (ctx st3)) (a_next old) NSLOTS]> (s_areas st3)) st3.

Lemma am_carve_eq {R} st p (k : mstate -> optr -> M R) bail :
  am_carve st p k bail = am_take (upd_ctx (fun c => set_avail_meta (Some (aadd p AREA_HDR)) (set_avail_meta_count NSLOTS c)) (carve_st st p)) k bail.
Proof. reflexivity. Qed.

End CANSEC1.
End F_am_K.

Module F_malloc_core.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Tac. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Image. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Walk. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import ITree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Decode. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import MallocFacts_A. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import MallocKit_A.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM01. Import SM01. Import SM01.Monad.
Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import Malloc_fp. Import MM08. Import MM08.F_malloc_enf. Import MM08.AllocSlot_iface. Import MM12. Import MM12.Malloc_iface. Import MM12.MallocHINV. Import MM08.F_malloc_join. Import MM08.F_malloc_small. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import F_malloc_entry.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section CORE.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis AS_PRE : forall st LB t sc n, AREACH st LB -> MFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
End CORE.



End CANSEC1.
End F_malloc_core.

Module F_malloc_big.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Tac. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Image. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Walk. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import ITree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Decode. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import MallocFacts_A. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import MallocKit_A. Import MM12. Import MM12.F_mm_syscalls.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM01. Import SM01. Import SM01.Monad.
Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import Malloc_fp. Import MM08. Import MM08.AllocSlot_iface. Import MM08.F_malloc_join. Import F_malloc_core. Import MM12. Import MM12.MallocHINV.
Import MM11. Import MM11.MallocKit_AB.
Import MM14. Import MM14.MallocKit_A2. Import MM08. Import MM08.F_malloc_bigw.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Section CANSEC1. Context {rc : runConstT}.
Definition big_final (st3 : mstate) (g : aptr) (rid : N) (n : Z) : mstate :=
  let needed := n + IB + UNIT in
  let st4 := upd_meta g (fun mr =>
               m_set_freed 0 (m_set_avail 0 (m_set_maplen ((needed + 4095) / 4096)
               (m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (rid, 0)) mr))))))) st3 in
  let st5 := put_group (rid, 0) (Some g) (group_active_idx st4 (rid, 0)) (lh_hdr full_lay st4 (rid, 0)) in
  let st6 := add_slots g (rid, 0) (get_stride (get_meta_rec st5 g)) 1 st5 in
  upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st6.

Section FINAL.
Variables (st3 : mstate) (g : aptr) (rid : N) (xa n c : Z).
Hypothesis G0 : get_meta_rec st3 g = meta0.
Hypothesis GN : (s_groups st3) !! (rid, 0) = None.
Hypothesis HC : c_mmap_counter (ctx st3) = c.
Hypothesis NR : 0 <= n < 2^32.
Hypothesis RR : (s_regions st3) !! rid = Some (mkRegion RKGroup xa (n + IB + UNIT)).

Let stF := big_final st3 g rid n.
Let stM := big_st st3 g rid n (u32 (c + 1)).

Lemma bf_meta : get_meta_rec stF g = big_meta rid n.
Proof.
  unfold stF, big_final, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_eq. cbn [default from_option id].
  rewrite G0. reflexivity.
Qed.

Lemma bf_meta_other q : q <> g -> get_meta_rec stF q = get_meta_rec st3 q.
Proof.
  intros NE. unfold stF, big_final, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma bm_meta : get_meta_rec stM g = big_meta rid n.
Proof. unfold stM, big_st, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_eq. reflexivity. Qed.
Lemma bm_meta_other q : q <> g -> get_meta_rec stM q = get_meta_rec st3 q.
Proof.
  intros NE. unfold stM, big_st, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land].
  rewrite lookup_insert_ne by congruence. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma bf_regions : s_regions stF = s_regions st3. Proof. reflexivity. Qed.
Lemma bf_areas : s_areas stF = s_areas st3. Proof. reflexivity. Qed.
Lemma bf_reserved : s_reserved stF = s_reserved st3. Proof. reflexivity. Qed.
Lemma bf_next : s_next_rid stF = s_next_rid st3. Proof. reflexivity. Qed.
Lemma bf_groups : s_groups stF = <[(rid, 0) := mkGhdr (Some g) 0]> (s_groups st3).
Proof.
  unfold stF, big_final. cbn -[Z.add Z.mul Z.div Z.land]. unfold group_active_idx, get_group. cbn -[Z.add Z.mul Z.div Z.land].
  rewrite GN. reflexivity.
Qed.
Lemma bm_groups : s_groups stM = <[(rid, 0) := mkGhdr (Some g) 0]> (s_groups st3).
Proof. reflexivity. Qed.
Lemma bf_shadow q : get_shadow stF q = get_shadow stM q.
Proof. reflexivity. Qed.
Lemma bf_shadow_other q : q <> rid -> get_shadow stF q = get_shadow st3 q.
Proof.
  intros NE. unfold stF, big_final, get_shadow. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
Lemma bf_ctx : ctx stF = ctx stM.
Proof. unfold stF, stM, big_final, big_st, ctx. cbn -[Z.add Z.mul Z.div Z.land u32]. unfold ctx in HC. rewrite HC. reflexivity. Qed.
Lemma bf_counter : c_mmap_counter (ctx stF) = u32 (c + 1).
Proof. rewrite bf_ctx. reflexivity. Qed.

Lemma ticks_ok_big_final : ticks_ok stM -> ticks_ok stF.
Proof. intros H; exact H. Qed.

Lemma bf_stride : get_stride (big_meta rid n) = big_ml n * 4096 - 16.
Proof.
  unfold get_stride, big_meta. cbn [m_last_idx m_maplen]. rewrite big_ml_eq by lia.
  replace ((n + 4115) / 4096 =? 0) with false by (symmetry; apply Z.eqb_neq; Z.div_mod_to_equations; lia).
  cbn. rewrite <- big_ml_eq by lia. unfold UNIT. reflexivity.
Qed.

Lemma bf_slots : s_slots stF = <[(rid, 16) := (g, 0)]> (s_slots st3).
Proof.
  unfold stF, big_final. cbn -[Z.add Z.mul Z.div Z.land get_stride get_meta_rec Z.sub].
  unfold aadd. cbn [fst snd]. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
Qed.
End FINAL.


Lemma malloc_core_big_eq st1 n : MMAP_THRESHOLD <= n < 2^32 ->
  malloc_core full_lay st1 n =
    SVis (EMmap 0 (n + IB + UNIT) PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
      if negb (mmap_answer_ok (s_atop st1) (live_ranges st1) (n + IB + UNIT) r) then bad_answer (ret (st1, @None (aptr * Z))) else
      if is_err r then ret (st1, None) else
      let '(st2, rid) := new_region RKGroup r (n + IB + UNIT) st1 in
      alloc_meta (step_seq st2) (fun st3 go =>
        match go with
        | None => SVis (EMunmap r (n + IB + UNIT)) (fun ru => if munmap_answer_ok ru then ret (drop_region rid st3, @None (aptr * Z)) else bad_answer (ret (st1, None)))
        | Some g => ret (big_final st3 g rid n, Some (g, 0))
        end) (ret (st1, None))).
Proof.
  intros Hn. unfold malloc_core.
  replace (size_overflows n) with false by (symmetry; unfold size_overflows; apply Z.leb_gt; lia).
  replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; lia).
  reflexivity.
Qed.

Lemma unk_agree_transfer st st' o m m' :
  unk_agree st o m ->
  (forall rid r, (s_regions st') !! rid = Some r -> r_kind r = RKGroup ->
     ((s_regions st) !! rid = Some r /\ get_shadow st' rid = get_shadow st rid /\
       (forall off, grp_hdr_cov st rid off -> grp_hdr_cov st' rid off) /\
       (forall off h, 0 <= off < round_up_pg (r_len r) -> cell_read (get_shadow st rid) off = Unknown h ->
          ~ grp_hdr_cov st' rid off -> m' (wa (r_base r + off)) = m (wa (r_base r + off))))
     \/ (forall off h, 0 <= off < round_up_pg (r_len r) -> cell_read (get_shadow st' rid) off = Unknown h -> grp_hdr_cov st' rid off)) ->
  unk_agree st' o m'.
Proof.
  intros UA H rid r off h Hr Hk Ho Hc NG.
  destruct (H rid r Hr Hk) as [(Hr0 & ES & GM & AG)|NEW].
  - rewrite ES in Hc. rewrite (AG off h Ho Hc NG). apply (UA rid r off h Hr0 Hk Ho Hc). intros X. apply NG, GM, X.
  - exfalso. apply NG. eapply NEW; eauto.
Qed.

Lemma grp_hdr_cov_same st st' rid off : s_groups st' = s_groups st -> grp_hdr_cov st rid off -> grp_hdr_cov st' rid off.
Proof. intros EG (b & gh & Hb & E & R). exists b, gh. rewrite EG. auto. Qed.

Lemma munmap_answer_ok_range a : match a with RgErr e => 1 <= e <= 4095 | RgDone _ => True end -> munmap_answer_ok (range_val a) = true.
Proof.
  destruct a as [e|b]; cbn [range_val]; intros He.
  - unfold munmap_answer_ok, is_errno_form, neg_errno, TWO64.
    replace (2 ^ 64 - 4095 <=? 2 ^ 64 - e) with true by (symmetry; apply Z.leb_le; lia).
    replace (2 ^ 64 - e <? 2 ^ 64) with true by (symmetry; apply Z.ltb_lt; lia).
    destruct (2 ^ 64 - e =? 0); reflexivity.
  - reflexivity.
Qed.

Lemma mmap_answer_ok_err live len e : 1 <= e <= 4095 -> mmap_answer_ok ATOP live len (neg_errno e) = true /\ is_err (neg_errno e) = true.
Proof.
  intros He. unfold mmap_answer_ok, is_errno_form, is_err, neg_errno, TWO64. split.
  - replace (2 ^ 64 - 4095 <=? 2 ^ 64 - e) with true by (symmetry; apply Z.leb_le; lia).
    replace (2 ^ 64 - e <? 2 ^ 64) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - apply Z.ltb_lt. lia.
Qed.

Lemma mmap_answer_ok_addr live len xa : 0 <= len ->
  mmap_addr_ok ATOP len [] xa = true -> mmap_answer_ok ATOP live len xa = true ->
  0 < xa /\ xa mod 4096 = 0 /\ xa + round_up_pg len <= ATOP /\ ranges_free live xa (round_up_pg len) = true /\ is_err xa = false.
Proof.
  intros L0 A B. pose proof (round_up_pg_ge len) as RG. unfold mmap_addr_ok in A. rewrite !Bool.andb_true_iff in A. destruct A as [[[A1 A2] A3] _].
  apply Z.eqb_eq in A1. apply Z.ltb_lt in A2. apply Z.leb_le in A3. rewrite mmap_len_round_up in A3.
  change page_size with 4096 in A1.
  unfold mmap_answer_ok in B. apply Bool.orb_prop in B.
  assert (NE : is_errno_form xa = false).
  { unfold is_errno_form, TWO64. replace (2 ^ 64 - 4095 <=? xa) with false by (symmetry; apply Z.leb_gt; atop_facts; lia). reflexivity. }
  destruct B as [B|B]; [rewrite NE in B; discriminate|].
  rewrite !Bool.andb_true_iff in B. destruct B as [[[_ _] _] B4].
  repeat split; auto. unfold is_err, TWO64. apply Z.ltb_ge. atop_facts. lia.
Qed.

Lemma brk_link_ps_ext st st' s :
  c_brk (ctx st') = c_brk (ctx st) ->
  (forall rid off, c_brk (ctx st) = BrkLive rid off -> conc st' (rid, off) = conc st (rid, off)) ->
  brk_link_ps st s -> brk_link_ps st' s.
Proof.
  intros EB EC BL. unfold brk_link_ps in *. rewrite EB. destruct (c_brk (ctx st)) as [| |rid off] eqn:E; auto.
  rewrite (EC rid off eq_refl). exact BL.
Qed.

Lemma munch_of_pointwise (lo hi : Z) (m m' : mem) :
  0 <= lo -> hi <= 2^64 ->
  (forall a, 0 <= a < 2^64 -> (a < lo \/ hi <= a) -> m' (wa a) = m (wa a)) -> munch [(lo, hi)] m m'.
Proof.
  intros H0 H1 AG x Hx. cbn in Hx. pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with (2^64) in R.
  rewrite <- (wa_unsigned_id x). apply AG; lia.
Qed.

Lemma cell_read_hh0 st rid off : (s_shadow st) !! rid = None -> 0 <= off ->
  cell_read (get_shadow (hdr_havoc (rid, 0) st) rid) off = if off <? 12 then Unknown 0 else Known 0.
Proof.
  intros SH Ho. unfold hdr_havoc, get_shadow, upd_shadow. cbn [s_shadow set_shadow fst snd].
  rewrite lookup_insert_eq. cbn [default from_option id]. unfold get_shadow. rewrite SH. cbn [default from_option id r_cells r_hav r_havp shadow0].
  unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite !lookup_empty. change (0 / 16) with 0.
  destruct (Z.eq_dec (off / 16) 0) as [E|NE].
  - rewrite E, lookup_insert_eq. cbn [default from_option id]. unfold hav_add. cbn.
    replace (off mod 16) with off by (Z.div_mod_to_equations; lia). destruct (off <? 12); reflexivity.
  - rewrite lookup_insert_ne by congruence. rewrite lookup_empty. cbn.
    replace (off <? 12) with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia). reflexivity.
Qed.

Lemma round_up_pg_4115 n : 0 <= n -> round_up_pg (n + IB + UNIT) = (n + 4115) / 4096 * 4096.
Proof. intros Hn. unfold IB, UNIT. rewrite round_up_pg_eq. Z.div_mod_to_equations. lia. Qed.

Lemma big_stride n rid : 0 <= n < 2^32 -> get_stride (big_meta rid n) = round_up_pg (n + IB + UNIT) - 16.
Proof. intros Hn. rewrite bf_stride, big_ml_eq, round_up_pg_4115 by lia. reflexivity. Qed.


Definition AMP_BIG (am_pre : mstate -> Prop) : Prop :=
  forall st LB t xa n, AREACH st LB -> MMAP_THRESHOLD <= n < 2^32 ->
  mmap_answer_ok (s_atop (set_tick t st)) (live_ranges (set_tick t st)) (n + IB + UNIT) xa = true -> is_err xa = false ->
  am_pre (step_seq (fst (new_region RKGroup xa (n + IB + UNIT) (set_tick t st)))).

Section BIG.
Variable am_pre : mstate -> Prop.
Hypothesis AMP : AMP_BIG am_pre.
End BIG.


End CANSEC1.
End F_malloc_big.

Module MallocFacts_AMP.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
Import MM15. Import MM15.MallocRep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import MallocFacts_A. Import MM12. Import MM12.MallocHINV. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import MallocFacts_AM. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import MallocFacts_AS. Import F_malloc_big.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Common Require Import RunDraw.
Open Scope Z_scope.


End MallocFacts_AMP.

Module MallocKit_B2.
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Tac. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Image. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Walk. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Arr. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import ITree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Lib Require Import Decode.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Common Require Import SFModel.
Import MM15. Import MM15.MallocRep. Import MM15.F_malloc_free. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Malloc Require Import MallocTree. Import MM13. Import MM13.MallocKit_B.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM01. Import SM01. Import SM01.Monad.
Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma peek_ok_pans o p c h : peek_answer_ok (pans_mem o p c h) = true.
Proof.
  pose proof (pans_mem_range o p c h). unfold peek_answer_ok.
  apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
Qed.



Definition grp_region_addr (st : mstate) (a : Z) : Prop :=
  exists rid r, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup /\ r_base r <= a < r_base r + round_up_pg (r_len r).

End CANSEC1.
End MallocKit_B2.
