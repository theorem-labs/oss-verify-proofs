(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (6 recorded proofs replaced by written proofs (am_fp_alloc_fp, am_fp_stack, am_fp_ctx and 3 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_B MallocModel_B MallocKit_B3 F_ntf_B.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_am_A () := "C35stdpp4base6lookupC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init9Datatypes6option00I35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupC59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC59OSSVerify5KrLib6Malloc9MallocRep5lr_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03I47Corelib4Init5Logic2or00I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or01C47Corelib4Init5Logic7and_indK47Corelib4Init5Logic2or02C47Corelib4Init5Logic6or_indc59OSSVerify5KrLib6Malloc6F_am_A5am_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree8alloc_fpC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib6Malloc9MallocRep3CTXC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib6Malloc9MallocRep:regions_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib6Malloc9MallocRepAreserved_disjointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8lr_lo_geC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4Spec6Malloc;ranges_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00C59OSSVerify5KrLib6Malloc9MallocRep>agent_reservedC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00C47Corelib4Init5Logic3iff".
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition am_took (st : mstate) (q : aptr) (cnt : Z) : mstate :=
  upd_meta q clr_links (upd_ctx (fun c => set_avail_meta (Some (aadd q META_SIZE)) (set_avail_meta_count cnt c)) st).

End CANSEC1.
