(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs replaced by tactic proofs; the auxv as a list of pairs; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/CJ/Tgt/RF_malloc_join.v, lines 72-82, 90-91, 96-100, 106-122, 129-133. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import Malloc_fp F_malloc_enf F_malloc_join.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Tgt Require Import RMallocRep RMallocTree RMallocKit_A RMalloc_fp RF_malloc_enf RAllocSlot_iface.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_RF_malloc_join () := "c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt>RF_malloc_join8renf_hypC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt;RMallocTree6rimplTC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc1MC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt>RF_malloc_join9rfail_hypC13~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep5rmrepC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep;rregions_wfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep9rmrep_ctxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep=rmrep_globalsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep;rmrep_areasC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep<rmrep_groupsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep<rmrep_shadowC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMalloc_fp:rmalloc_fpC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP=alloc_ceilingC13~~~I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:s_reservedC13~~~I47Corelib4Init5Logic2eq00I35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6r_baseC13~~~K47Corelib7Numbers7BinNums1Z02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5r_lenC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;round_up_pgC13~~~C56Stdlib6ZArith6BinInt1Z3addC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9s_regionsC13~~~C47Corelib4Init5Logic3notC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep5lr_loC13~~~C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableK47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic3and00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunPCalloc_ceiling_rangeC13~~~K47Corelib7Numbers7BinNums8positive01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt;RMallocTree9ralloc_fpC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9Malloc_fp<new_reg_addrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9Malloc_fp>free_slot_addrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9Malloc_fp<grp_hdr_addrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree:fresh_addrC13~~~C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init5Logic2or01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState<unsigned_litC13~~~C47Corelib4Init5Logic6eq_indK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic2or02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<get_meta_recC13~~~I47Corelib4Init5Logic2ex00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;live_rangesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;ranges_freeC13~~~C35stdpp4base6lookupC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7s_areasC13~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6r_kindC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8s_groupsC13~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula08C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocFacts_A9sstart_ofC13~~~C56Stdlib6ZArith6BinInt1Z3subC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:get_strideC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7m_availC13~~~C56Stdlib6ZArith6BinInt1Z7testbitC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7m_freedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5m_memC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6region00C13~~~I47Corelib7Numbers7BinNums1N00K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4bool00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep<ref_reservedC13~~~K47Corelib4Init9Datatypes4bool01I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4area00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5rkind00C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5rkind03C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4ghdr00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep4RCTXC13~~~K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc2IBC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4optrC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~K47Corelib7Numbers7BinNums8positive03C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt;RMallocTree<rpres_exceptC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step8rw_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells:cells_sizeC13~~~C56Stdlib6ZArith6BinInt1Z6of_natc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt>RF_malloc_join@rmalloc_fp_casesC13~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt;RMallocTreeErpres_except_rw_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree3memC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:F_syscalls5rsegsC13~~~I47Corelib4Init5Logic5False00I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9Malloc_fp4mrel00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:s_next_ridC13~~~C56Stdlib6NArith6BinNat1N2leC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMalloc_fp?rmalloc_fp_monoC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMalloc_fpCrreserved_disjoint2C13~~~C47Corelib4Init5Logic9False_indK47Corelib4Init5Logic3and01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep8lr_lo_geC13~~~C47Corelib4Init5Logic5proj2C47Corelib4Init5Logic5proj1C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt;RMallocTree<rfresh_imageC13~~~K46Stdlib9micromega5Tauto8GFormula06C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt;RMallocTree8rauxv_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree9auxv_listC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Arr4u64sC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP:secret_valC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2wzC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3le8C13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt>RF_malloc_join@rmalloc_fp_imageC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt<RMallocKit_A=rauxv_ok_presC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8bytes_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep:RAUXV_CELLC13~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


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
              F (Z_to_bv 64 0xa08ec) fc None m1 (seg_rom rsegs)).

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

Lemma rmalloc_fp_cases st st2 lo sp m0 m2 a :
  rmrep st m0 -> rmrep st2 m2 -> rmalloc_fp st st2 lo sp a ->
  lo <= a < sp \/ a < alloc_ceiling.
Proof.
  intros (WF & _) (WF2 & _) H. pose proof WF as (_ & WR & _). pose proof WF2 as (_ & WR2 & _).
  pose_ceil.
  destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC _]]]]].
  - left; exact H.
  - right. rewrite unsigned_lit in H by lia. lia.
  - right. unfold RCTX in H. lia.
  - right. destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). pose_ceil. lia.
  - right. destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). pose_ceil. lia.
  - right. destruct (WR (fst b) r Hr) as (_ & _ & _ & RC & _). pose_ceil. lia.
  - right. destruct (WR (fst b) r Hr) as (_ & _ & _ & RC & _). pose_ceil. lia.
  - right. pose_ceil. lia.
Qed.

Lemma rframe_after_call st st2 lo sp' m0 m m' m2 A cs :
  rmrep st m0 -> rmrep st2 m2 ->
  rpres_except (rmalloc_fp st st2 lo sp') m m' -> rw_cells rsegs m A cs ->
  sp' <= A -> alloc_ceiling <= A -> rw_cells rsegs m' A cs.
Proof.
  intros MR0 MR2 PE H HA HC. eapply rpres_except_rw_cells; [exact PE| exact H|].
  intros a Ha Hfp. destruct (rmalloc_fp_cases st st2 lo sp' m0 m2 a MR0 MR2 Hfp); lia.
Qed.

Lemma rmalloc_fp_sp_mono st st2 lo sp1 sp2 a : sp1 <= sp2 -> rmalloc_fp st st2 lo sp1 a -> rmalloc_fp st st2 lo sp2 a.
Proof.
  intros H [[X|X]|X]; [left; left; lia| left; right; exact X| right; exact X].
Qed.

Lemma rmalloc_fp_st_mono st sta stb lo sp a : mrel sta stb -> rmalloc_fp st sta lo sp a -> rmalloc_fp st stb lo sp a.
Proof. intros [HR _ _] H. eapply rmalloc_fp_mono; [exact HR| exact H]. Qed.

Lemma rmalloc_fp_image st st2 lo sp m0 m2 a :
  rmrep st m0 -> rmrep st2 m2 -> rmalloc_fp st st2 lo sp a -> alloc_ceiling <= lo ->
  0xb4000 <= a < 0xee000 -> RCTX <= a < RCTX + 928 \/ 0xccb1c <= a < 0xccb20.
Proof.
  intros (WF & _) (WF2 & _) H CLO HA. pose proof WF as (_ & WR & _). pose proof WF2 as (_ & WR2 & _).
  pose_ceil.
  assert (IMG : forall P : Prop, (forall rid r, (s_regions st) !! rid = Some r -> r_base r <= a < r_base r + round_up_pg (r_len r) -> P)
                 /\ (forall rid r, (s_regions st2) !! rid = Some r -> r_base r <= a < r_base r + round_up_pg (r_len r) -> P)).
  { intros P. split; intros rid r Hr Ha.
    - destruct (WR rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint2 _ _ RF ltac:(lia)) as [D1 D2]. exfalso. lia.
    - destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint2 _ _ RF ltac:(lia)) as [D1 D2]. exfalso. lia. }
  destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC FR]]]]].
  - exfalso. lia.
  - right. rewrite unsigned_lit in H by lia. lia.
  - left. exact H.
  - pose proof (lr_lo_ge r). apply (proj2 (IMG _) rid r Hr ltac:(lia)).
  - pose proof (lr_lo_ge r). apply (proj2 (IMG _) rid r Hr ltac:(lia)).
  - apply (proj1 (IMG _) (fst b) r Hr Ha).
  - apply (proj1 (IMG _) (fst b) r Hr Ha).
  -
    exfalso. pose proof WF as (RS & _). pose proof (rfresh_image st a (conj FC FR) RS). lia.
Qed.

Lemma rauxv_ok_malloc_fp st st2 lo sp m0 m2 m m' B :
  rmrep st m0 -> rmrep st2 m2 -> rauxv_ok m B -> rpres_except (rmalloc_fp st st2 lo sp) m m' ->
  alloc_ceiling <= lo -> sp <= B -> rauxv_ok m' B.
Proof.
  intros MR0 MR2 AUX PE CLO SB. eapply rauxv_ok_pres; [exact AUX| exact PE| |].
  - intros a Ha Hfp. destruct (rmalloc_fp_cases st st2 lo sp m0 m2 a MR0 MR2 Hfp); [lia|].
    destruct AUX as (av & vs & rnd & _ & _ & _ & HH & _). pose_ceil. lia.
  - intros a Ha Hfp. unfold RAUXV_CELL, RLIBC in Ha.
    destruct (rmalloc_fp_image st st2 lo sp m0 m2 a MR0 MR2 Hfp CLO ltac:(lia)) as [X|X]; unfold RCTX in X; lia.
Qed.
End CEIL_WRAP_1.

