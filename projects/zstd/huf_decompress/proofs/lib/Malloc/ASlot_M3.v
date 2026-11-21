(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (1 recorded proof replaced by written proofs (halve_big_pos)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp MallocKit_A2 AllocSlot_iface F_malloc_join Malloc_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W1 ASlot_W9 ASlot_W10 ASlot_W11 ASlot_I ASlot_M0.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require MallocFacts_inv4.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASlot_M3 () := "K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C59OSSVerify5KrLib4Spec6Malloc9halve_bigC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z8leb_specC56Stdlib6ZArith6BinInt1Z3lebI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega7EnvRing3Pol03K46Stdlib9micromega7EnvRing3Pol02K46Stdlib9micromega=RingMicromega5Psatz03K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes7nat_indK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00".
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
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
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis CLO : ATOP <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK (S f).
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Let F0 : ISTF st LB := MallocFacts_inv4.ist_facts_proof st0 LB st AR IS.
End LEVEL.


End CANSEC1.
