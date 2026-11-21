(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx. (* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Tac.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Image.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require SysStep.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Walk.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require ITree.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM15.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require F_malloc_entry.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM11.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MallocTree.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MallocFacts_A.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MallocKit_A.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM14.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM08.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM13.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM12.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Malloc.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Malloc_fp.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MallocNat.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MallocFacts_AS.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require ASlot_W0.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require ASlot_W1.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require ASlot_I.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM05.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require RMallocRep.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require RMallocTree.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require PM21.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require RMallocKit_B.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require PM22.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require PM02.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require PM03.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require PM18.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require PM20.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require RASlot_W2.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require RASlot_W4.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require PM01.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM06.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM07.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM09.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require PM15.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require F_memcpy.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM10.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module RASlot_W15.
(* [comment removed for export] *)
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. Import MM15.F_malloc_fast. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import F_malloc_entry. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM11. Import MM11. Import MM11.F_malloc_enframe. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocFacts_A. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocKit_A. Import MM11.MallocKit_AB. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM14. Import MM14. Import MM14.MallocKit_A2. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM08. Import MM08. Import MM08.MallocKit_A3. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM13. Import MM13. Import MM13.MallocKit_B. Import MM14.MallocKit_B3. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM12. Import MM12. Import MM12.MallocModel_B. Import MM08.F_malloc_bigw.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.Monad.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM15. Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import Malloc_fp. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocNat. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocFacts_AS. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import ASlot_W0. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import ASlot_W1. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import ASlot_I. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM05. Import MM05. Import MM05.ASlot_W15.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require Import RMallocRep. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require Import RMallocTree. Import PM21. Import PM21.RF_get_meta. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require Import RMallocKit_B. Import PM22. Import PM22.RMallocKit_B2. Import PM02. Import PM02.RMallocKit_B3. Import PM22.RMallocKit_A. Import PM03. Import PM03.RMallocKit_A2. Import PM22.RMalloc_fp. Import PM02.RAllocSlot_iface. Import PM02.RASlot_I. Import PM18. Import PM18.RMallocKit_A3. Import PM20. Import PM20.RF_ntf_A. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require Import RASlot_W2. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require Import RASlot_W4.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *) Context {rc : runConstT}.
Section SEQ.
Variables (sc : Z).
Hypothesis SC : 0 <= sc < 48.

Definition rseqW : list (Z * Z) := [(RCTX + 848, RCTX + 913)]%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rbounce_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) (m : mem),
  rmrep st m -> 0 <= c_seq (ctx st) < 256 -> (forall i, 0 <= bounces st i < 256) -> (forall i, 0 <= unmap_seq st i < 256) ->
  mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (fun ms' => exists (t0' t1' a3' a5' a7' : word) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3' a4 a5' (wz (c_seq (ctx st))) a7' s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x1a6c8) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
      /\ a3' = Z_to_bv 64 (Z.b2z (is_bouncing sc st))
      /\ munch rseqW m m' /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m' /\ rmrep (account_bounce sc st) m')
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1a414) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until m. intros MR SEQ BR USR MI.
  pose proof (munch_refl rseqW m) as MU. pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m) as WM. unfold rseqW in MU.
  unfold RCTX, RMLOCK in *. atop_facts.
  (* [comment removed for export] *)
  assert (EXIT : forall stX mX (t0v t1v a3v a5v a6v a7v : word),
    rmrep stX mX -> stX = account_bounce sc st -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) mX -> a3v = Z_to_bv 64 (Z.b2z (is_bouncing sc st)) ->
    munch [(602800 + 848, 602800 + 913)]%Z m mX -> wmono (run_segments psegs rc_inp rc_sp rc_mb) m mX ->
    evt (run_segments psegs rc_inp rc_sp rc_mb) (fun ms' => exists (t0' t1' a3' a5' a7' : word) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3' a4 a5' (wz (c_seq (ctx st))) a7' s2 s3 s4 s5 (Z_to_bv 64 602792) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x1a6c8) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
      /\ a3' = Z_to_bv 64 (Z.b2z (is_bouncing sc st))
      /\ munch [(602800 + 848, 602800 + 913)]%Z m m' /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m' /\ rmrep (account_bounce sc st) m')
    (MS (mkR ra sp gp tp t0v t1v t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3v a4 a5v a6v a7v s2 s3 s4 s5 (Z_to_bv 64 602792) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1a6c4) fc None mX (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)))).
  { intros stX mX t0v t1v a3v a5v a6v a7v MRX EX MIX -> MUX WMX.
    pose proof (rmrep_seq_read stX mX (wa (602800 + 912)) MRX eq_refl) as RDS.
    replace (wa (602800 + 912)) with (Z_to_bv 64 (602792 + 920)) in RDS by (unfold wa; f_equal; lia).
    assert (SQX : c_seq (ctx stX) = c_seq (ctx st)).
    { rewrite EX. unfold account_bounce. destruct (sc_in_seq_range sc); [|reflexivity].
      destruct (negb _ && _); [|reflexivity]. destruct (_ <? 100); reflexivity. }
    rewrite SQX in RDS.
    step. rewrite ?zxb_b8 by lia. clear RDS.
    apply evt_done. do 6 eexists. split; [reflexivity|]. split; [reflexivity|].
    split; [exact MUX|]. split; [exact WMX|]. split; [exact MIX| rewrite <- EX; exact MRX]. }
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit sc) by lia. step.
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  { (* [comment removed for export] *)
    assert (HO : sc_in_seq_range sc = false).
    { unfold sc_in_seq_range. destruct (Z.lt_ge_cases sc 7) as [L7|G7].
      - replace (7 <=? sc) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      - rewrite swrap32_small in K by lia. change 18446744073709551615 with (Z.ones 64) in K. rewrite Z.land_ones, Z.mod_small in K by lia.
        replace (sc <? 39) with false by (symmetry; apply Z.ltb_ge; lia). apply Bool.andb_false_r. }
    step. step.
    eapply EXIT; [exact MR| | exact MI| | exact MU| exact WM].
    - unfold account_bounce. rewrite HO. reflexivity.
    - unfold is_bouncing. rewrite HO. reflexivity. }
  rewrite swrap32_small in K |- * by lia. change 18446744073709551615 with (Z.ones 64) in K. rewrite Z.land_ones in K by lia.
  destruct (Z.lt_ge_cases sc 7) as [L7|G7].
  { exfalso. clear -K L7 SC. Z.div_mod_to_equations. lia. }
  rewrite Z.mod_small in K by lia.
  assert (IN : sc_in_seq_range sc = true) by (unfold sc_in_seq_range; rewrite (proj2 (Z.leb_le 7 sc)), (proj2 (Z.ltb_lt sc 39)) by lia; reflexivity).
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (sc + -7)) by lia.
  pose proof (rmrep_bounces_read st m (sc - 7) (wa (602800 + 880 + (sc - 7))) MR ltac:(lia) eq_refl) as RDB.
  replace (wa (602800 + 880 + (sc - 7))) with (Z_to_bv 64 (602792 + (sc + -7) + 888)) in RDB by (unfold wa; f_equal; lia).
  pose proof (BR (sc - 7)) as BR7. pose proof (USR (sc - 7)) as USR7.
  step. rewrite ?zxb_b8 by lia. clear RDB.
  pose proof MR as (_ & (_ & _ & _ & US & _) & _).
  pose proof (u8arr_read (run_segments psegs rc_inp rc_sp rc_mb) m _ (unmap_seqs st) (sc - 7) _ (Z_to_bv 64 (602792 + (sc + -7) + 856)) US (unmap_seqs_nth st (sc - 7) ltac:(lia)) ltac:(lia)
                ltac:(unfold wa, RCTX; f_equal; lia)) as RDU. clear US.
  step. rewrite ?zxb_b8 by lia. clear RDU.
  (* [comment removed for export] *)
  step. step.
  set (nos := 100 <=? bounces st (sc - 7)).
  assert (NOSE : is_bouncing sc st = nos) by (unfold is_bouncing; rewrite IN; reflexivity).
  assert (A3 : Z_to_bv 64 (Z.lxor (bv_unsigned (v_sltiu (wz (bounces st (sc - 7))) 100)) 1) = Z_to_bv 64 (Z.b2z (is_bouncing sc st))).
  { rewrite NOSE. unfold v_sltiu, c_ltu, bv_ltu, nos. rewrite (wz_unsigned (bounces st (sc - 7))) by lia.
    change (bv_wrap 64 100) with 100.
    destruct (Z.ltb_spec (bounces st (sc - 7)) 100); destruct (Z.leb_spec 100 (bounces st (sc - 7))); try lia; reflexivity. }
  rewrite A3. clear A3.
  assert (AB : account_bounce sc st =
    (if negb (unmap_seq st (sc - 7) =? 0) && (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10)
     then if bounces st (sc - 7) + 1 <? 100 then set_bounce (sc - 7) (bounces st (sc - 7) + 1) st else set_bounce (sc - 7) 150 st
     else st)) by (unfold account_bounce; rewrite IN; reflexivity).
  (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1; rewrite ?(wz_unsigned (unmap_seq st (sc - 7))) in K1 by lia.
  { eapply EXIT; [exact MR| | exact MI| reflexivity| exact MU| exact WM]. rewrite AB, K1. reflexivity. }
  (* [comment removed for export] *)
  pose proof (rmrep_seq_read st m (wa (602800 + 912)) MR eq_refl) as RDS.
  replace (wa (602800 + 912)) with (Z_to_bv 64 (602792 + 920)) in RDS by (unfold wa; f_equal; lia).
  step. rewrite ?zxb_b8 by lia. clear RDS.
  step. rewrite (wz_unsigned (c_seq (ctx st))), (wz_unsigned (unmap_seq st (sc - 7))) by lia.
  step. step. if_cases K2; unfold bv_lts in K2; rewrite !signed_lit_small in K2 by lia.
  { (* [comment removed for export] *)
    apply Z.ltb_lt in K2.
    apply evt_done. do 6 eexists. split; [reflexivity|]. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    rewrite AB. replace (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite Bool.andb_false_r. exact MR. }
  apply Z.ltb_ge in K2.
  assert (AB2 : account_bounce sc st =
    (if bounces st (sc - 7) + 1 <? 100 then set_bounce (sc - 7) (bounces st (sc - 7) + 1) st else set_bounce (sc - 7) 150 st)).
  { rewrite AB. replace (unmap_seq st (sc - 7) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  clear AB K1 K2.
  pose proof MR as (_ & (_ & _ & _ & _ & BA & _) & _).
  pose proof (u8arr_store_ok (run_segments psegs rc_inp rc_sp rc_mb) _ _ (bouncess st) (sc - 7) (Z_to_bv 64 (602792 + (sc + -7) + 888)) BA
                ltac:(rewrite bouncess_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear BA.
  (* [comment removed for export] *)
  step. step. if_cases K3; zify_cond K3; rewrite ?(wz_unsigned (bounces st (sc - 7))), ?unsigned_lit in K3 by lia.
  - (* [comment removed for export] *)
    step. rewrite (wz_unsigned (bounces st (sc - 7))) by lia.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_bounce st mX (sc - 7) (bounces st (sc - 7) + 1) MR ltac:(lia)) as MR2; unfold RCTX in MR2 end.
    rraw_store_finish0 (602800 + 880 + (sc - 7)) [b8 (bounces st (sc - 7) + 1)] MU WM SOK.
    eapply EXIT; [exact MR2| | assumption| reflexivity| exact MU| exact WM].
    rewrite AB2. replace (bounces st (sc - 7) + 1 <? 100) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - (* [comment removed for export] *)
    step. step. st1. (* [comment removed for export] *)
    first [rewrite (le1_lit 150) by lia | change [Z_to_bv 8 150] with [b8 150]].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_bounce st mX (sc - 7) 150 MR ltac:(lia)) as MR2; unfold RCTX in MR2 end.
    rraw_store_finish0 (602800 + 880 + (sc - 7)) [b8 150] MU WM SOK.
    eapply EXIT; [exact MR2| | assumption| reflexivity| exact MU| exact WM].
    rewrite AB2. replace (bounces st (sc - 7) + 1 <? 100) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
(* [comment removed for export] *)
Lemma rseq_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) (m0 m : mem),
  rmrep st m -> 0 <= c_seq (ctx st) < 256 -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m ->
  munch rseqW m0 m -> wmono (run_segments psegs rc_inp rc_sp rc_mb) m0 m ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (fun ms' => exists (a6' : word) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 (Z_to_bv 64 31) a6' a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x1a6f4) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
      /\ munch rseqW m0 m' /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m0 m' /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m' /\ rmrep (step_seq st) m')
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 (wz (c_seq (ctx st))) a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1a6c8) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until m. intros MR SEQ MI MU WM. unfold rseqW in *.
  set (q := c_seq (ctx st)) in *.
  pose proof MR as (_ & (_ & _ & _ & US & _ & C6) & _).
  unfold RCTX, RMLOCK in *. atop_facts. unfold ctx_tail_cells in C6.
  replace (602800 + 912) with 603712 in C6 by reflexivity. replace (602800 + 848) with 603648 in US by reflexivity.
  (* [comment removed for export] *)
  assert (TL : forall (mj : mem) (stj : mstate) (ns : Z),
    0 <= ns < 256 -> rmrep stj mj -> ctx_tail_cells stj = ctx_tail_cells st -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) mj ->
    munch [(602800 + 848, 602800 + 913)]%Z m0 mj -> wmono (run_segments psegs rc_inp rc_sp rc_mb) m0 mj ->
    evt (run_segments psegs rc_inp rc_sp rc_mb) (fun ms' => exists (a6' : word) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 (Z_to_bv 64 31) a6' a7 s2 s3 s4 s5 (Z_to_bv 64 602792) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x1a6f4) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
      /\ munch [(602800 + 848, 602800 + 913)]%Z m0 m' /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m0 m' /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m' /\ rmrep (upd_ctx (set_seq ns) stj) m')
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 (Z_to_bv 64 255) (Z_to_bv 64 ns) a7 s2 s3 s4 s5 (Z_to_bv 64 602792) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1a6ec) fc None mj (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)))).
  { intros mj stj ns NS MRj CTj MIj MUj WMj.
    pose proof MRj as (_ & (_ & _ & _ & _ & _ & C6j) & _). rewrite CTj in C6j. unfold ctx_tail_cells in C6j. unfold RCTX in C6j.
    replace (602800 + 912) with 603712 in C6j by reflexivity.
    pose proof (rw_cells_store_ok_at (run_segments psegs rc_inp rc_sp rc_mb) _ _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 (Z_to_bv 64 (602792 + 920)) C6j eq_refl eq_refl
                  ltac:(unfold wa; f_equal; lia)) as SOK.
    clear C6j.
    (* [comment removed for export] *)
    step. st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (rmrep_set_seq stj mX ns MRj NS) as MR1; unfold RCTX in MR1 end.
    rraw_store_finish0 (602800 + 912) [b8 ns] MUj WMj SOK.
    apply evt_done. do 2 eexists. split; [reflexivity|].
    split; [exact MUj|]. split; [exact WMj|]. split; [assumption| exact MR1]. }
  (* [comment removed for export] *)
  step. step. if_cases K2; zify_cond K2; rewrite ?(wz_unsigned q), ?unsigned_lit in K2 by lia.
  - (* [comment removed for export] *)
    step. rewrite (wz_unsigned q) by lia.
    eapply evt_mono; [eapply (TL m st (q + 1)); [lia| exact MR| reflexivity| exact MI| exact MU| exact WM]|].
    intros ms' PO. rewrite (step_seq_eq st). fold q. replace (q =? 255) with false by (symmetry; apply Z.eqb_neq; lia). exact PO.
  - (* [comment removed for export] *)
    pose proof (rw_cells_of_u8arr (run_segments psegs rc_inp rc_sp rc_mb) _ _ _ US) as USC. rewrite unmap_seqs_length in USC. clear US C6.
    pose proof (munch_refl [(602800 + 848, 602800 + 880)]%Z m) as MUz. pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m) as WMz.
    step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (UZ : u8arr (run_segments psegs rc_inp rc_sp rc_mb) mX 603648 (zeros 32));
    [ apply (u8arr_of_rw_cells (run_segments psegs rc_inp rc_sp rc_mb) mX 603648 32);
      lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) mX 603648 _ |- _ =>
        apply (rw_cells_congr (run_segments psegs rc_inp rc_sp rc_mb) mX 603648 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] [CB 32 (zeros 32)]); [reflexivity| reflexivity| cbn; split; [reflexivity| exact I]| exact H] end |] end.
    set (stz := upd_ctx (fun c => set_unmap_seq_map ∅ c) st).
    pose proof MR as (_ & (_ & _ & _ & _ & _ & C6) & _). unfold ctx_tail_cells, RCTX in C6.
    lazymatch goal with MUc : munch _ m ?mX, WMc : wmono (run_segments psegs rc_inp rc_sp rc_mb) m ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRz : rmrep stz mX);
    [ eapply (rmrep_ctx_frameW st stz _ mX _ MR MUc WMc); try reflexivity;
      [ intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia
      | right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
      | right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
      | right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
      | left; unfold stz; rewrite unmap_seqs_empty; unfold RCTX; exact UZ
      | right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia]
      | right; split; [| intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia];
        unfold ctx_tail_cells, brk_word, ctx, stz; cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]; reflexivity ]
    | clear MUc WMc ] end.
    (* [comment removed for export] *)
    step. step.
    lazymatch goal with MUc : munch _ m0 ?mX, WMc : wmono (run_segments psegs rc_inp rc_sp rc_mb) m0 ?mX, MIc : mem_inv (run_segments psegs rc_inp rc_sp rc_mb) ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      eapply evt_mono; [eapply (TL mX stz 1); [lia| exact MRz| reflexivity| exact MIc| exact MUc| exact WMc]|] end.
    intros ms' PO. rewrite (step_seq_eq st). fold q. rewrite K2. cbn [Z.eqb Pos.eqb]. exact PO.
Qed.
(* [comment removed for export] *)
Lemma rmm_seq_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) (m : mem),
  rmrep st m -> 0 <= c_seq (ctx st) < 256 -> (forall i, 0 <= bounces st i < 256) -> (forall i, 0 <= unmap_seq st i < 256) ->
  mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (fun ms' => exists (t0' t1' a3' a6' a7' : word) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3' a4 (Z_to_bv 64 31) a6' a7' s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x1a6f4) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
      /\ a3' = Z_to_bv 64 (Z.b2z (is_bouncing sc st))
      /\ munch rseqW m m' /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m' /\ rmrep (step_seq (account_bounce sc st)) m')
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 RMLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1a414) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until m. intros MR SEQ BR USR MI.
  eapply evt_cut; [eapply rbounce_walk; eassumption|].
  cbv beta. intros ms' (t0' & t1' & a3' & a5' & a7' & m' & -> & A3 & MU & WM & MI' & MR').
  assert (SEQ' : c_seq (ctx (account_bounce sc st)) = c_seq (ctx st)).
  { unfold account_bounce. destruct (sc_in_seq_range sc); [|reflexivity].
    destruct (negb _ && _); [|reflexivity]. destruct (_ <? 100); reflexivity. }
  rewrite <- SEQ'.
  eapply evt_mono; [eapply (rseq_walk _ _ _ _ t0' t1'); [exact MR'| rewrite SEQ'; exact SEQ| exact MI'| exact MU| exact WM]|].
  cbv beta. intros ms'' (a6'' & m'' & -> & MU'' & WM'' & MI'' & MR'').
  do 6 eexists. split; [reflexivity|]. subst a3'.
  repeat (split; [first [reflexivity| assumption]|]). exact MR''.
Qed.
End SEQ.
End CANSEC1.
End RASlot_W15.

Module RF_am_D.
(* [comment removed for export] *)
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM12. Import MM12. Import MM12.MallocModel_B. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM06. Import MM06. Import MM06.F_ntf_A. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM07. Import MM07. Import MM07.F_ntf_B. Import MM06.F_ntf_C. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM13. Import MM13. Import MM13.MallocKit_B. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM14. Import MM14. Import MM14.MallocKit_B3. Import MM07.F_am_A. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM09. Import MM09. Import MM09.F_am_D.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require Import RMallocRep. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require Import RMallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require Import RMallocKit_B. Import PM02. Import PM02.RMallocKit_B3. Import PM20. Import PM20.RF_ntf_A. Import PM20.RF_ntf_C. Import PM15. Import PM15.RF_am_A.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ctx_cells_cbn :=
  cbn [ctx set_head upd_ctx s_ctx set_free_meta_head set_avail_meta set_avail_meta_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
       c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *) Context {rc : runConstT}.
Lemma ram_deq : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (h nx pv : aptr),
  rmrep st m -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m ->
  c_free_meta_head (ctx st) = Some h -> meta_slot st h ->
  m_next (get_meta_rec st h) = Some nx -> m_prev (get_meta_rec st h) = Some pv ->
  meta_slot st nx -> meta_slot st pv -> (nx = h <-> pv = h) ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp + -64) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m (dequeue LFree h st) (Z_to_bv 64 (conc st h)))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19bb4) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until pv. intros MR MI FMH MSh HN HP MSn MSp SELF FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st m h MR MSh) as (HB0 & HB1 & HB2 & _).
  pose proof (rmeta_slot_bounds st m nx MR MSn) as (NB0 & NB1 & NB2 & _).
  pose proof (rmeta_slot_bounds st m pv MR MSp) as (PB0 & PB1 & PB2 & _).
  pose proof MR as (WF & (C1 & _) & _). unfold rctx_head_cells, rsecw in C1. rewrite FMH in C1.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. atop_facts.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (conc st h, conc st h + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40); (602800, 602800 + 928)]%Z m) as MU.
  pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m) as WM.
  (* [comment removed for export] *)
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  st1. st1.
  assert (CF : bv_eqb (Z_to_bv 64 (conc st h)) (Z_to_bv 64 0) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.
  (* [comment removed for export] *)
  rmeta_chunk MR MSh CH. rewrite HN, HP in CH. cbn [oconc] in CH.
  st1. clear CH.
  (* [comment removed for export] *)
  st1. if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    assert (Enx : nx = h).
    { rewrite ?unsigned_lit in K by lia. exact (rconc_meta_inj st m h nx MR MSh MSn ltac:(first [exact K | symmetry; exact K])). }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (munch_refl [(RCTX + 16, RCTX + 24)]%Z mX) as MUc; pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) mX) as WMc end.
    unfold RCTX in MUc.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR1 : rmrep (set_head LFree None st) mX) end.
    { eapply (rmrep_ctx_frameW st _ _ _ _ MR MUc WMc); try reflexivity.
      - intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - left. unfold rctx_head_cells, rsecw, RCTX. ctx_cells_cbn. unfold pw at 1. cbn [oconc]. unfold pw. unfold wz at 4.
        lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX 602800 _ |- _ => exact H end.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia. }
    clear MUc WMc C1.
    st1.
    assert (EQ : dequeue LFree h st = upd_meta h clr_links (set_head LFree None st)).
    { rewrite dequeue_mid. unfold deq_mid. rewrite HN, <- Enx, optr_eqb_refl. reflexivity. }
    rewrite EQ.
    change (conc st h) with (conc (set_head LFree None st) h). change (Z_to_bv 64 602648) with (Z_to_bv 64 RSSP_GUARD).
    eapply evt_mono.
    { eapply (ram_tail sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo (set_head LFree None st) h);
        [exact MR1 | | apply meta_slot_same_areas with st; [reflexivity| exact MSh] | | | atop_facts; lia | lia].
      - lazymatch goal with H : mem_inv (run_segments psegs rc_inp rc_sp rc_mb) ?mX |- _ => exact H end.
      - lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
      - lazymatch goal with H : stk (run_segments psegs rc_inp rc_sp rc_mb) ?mX lo _ |- _ => exact H end. }
    intros ms' RP. unfold ram_ret_post in RP |- *.
    destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
    do 15 eexists. split; [reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
      - eapply rpres_except_trans; [exact MU|]. eapply rpres_except_mono; [exact PE'|]. intros a Ha. apply (proj1 (ram_fp_same st _ lo _ a eq_refl)). exact Ha.
      - cbn [ivs_covered]. repeat split; intros x Hx.
        + apply ram_fp_stack. lia.
        + eapply ram_fp_meta; [exact MR | exact MSh | lia].
        + eapply ram_fp_meta; [exact MR | exact MSp | lia].
        + eapply ram_fp_meta; [exact MR | exact MSn | lia].
        + apply ram_fp_ctx. unfold RCTX. lia. }
    split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
  - (* [comment removed for export] *)
    assert (NEn : nx <> h) by (intros ->; apply K; reflexivity).
    assert (NEp : pv <> h) by (intros E; apply NEn; apply (proj2 SELF); exact E).
    (* [comment removed for export] *)
    rmeta_chunk MR MSh CH. rewrite HN, HP in CH. cbn [oconc] in CH.
    st1. clear CH.
    (* [comment removed for export] *)
    rmeta_open (conc st pv) MUp WMp.
    rmeta_chunk MR MSp CH.
    st1.
    rmeta_close2 MR MSp MUp WMp CH (put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) MR1 HP HN.
    set (st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st) in MR1.
    assert (MSh1 : meta_slot st1 h) by (apply meta_slot_put_meta; exact MSh).
    assert (MSn1 : meta_slot st1 nx) by (apply meta_slot_put_meta; exact MSn).
    (* [comment removed for export] *)
    rmeta_chunk MR1 MSh1 CH. unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
    rewrite HN, HP in CH. cbn [oconc] in CH.
    st1. st1. clear CH.
    (* [comment removed for export] *)
    rmeta_open (conc st nx) MUn WMn.
    rmeta_chunk MR1 MSn1 CH.
    st1.
    rmeta_close2 MR1 MSn1 MUn WMn CH (put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) MR2 HP HN.
    set (st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1) in MR2.
    assert (MSh2 : meta_slot st2 h) by (apply meta_slot_put_meta; exact MSh1).
    (* [comment removed for export] *)
    st1. st1.
    rewrite bv_eqb_refl. cbn [negb]. cbv iota.
    (* [comment removed for export] *)
    rmeta_chunk MR2 MSh2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEn; symmetry; exact E).
    unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
    rewrite HN, HP in CH. cbn [oconc] in CH.
    st1. clear CH.
    (* [comment removed for export] *)
    clear C1. pose proof MR2 as (_ & (C1 & _) & _). unfold rctx_head_cells, rsecw, RCTX in C1.
    replace (c_free_meta_head (ctx st2)) with (Some h) in C1 by (symmetry; exact FMH).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (munch_refl [(RCTX + 16, RCTX + 24)]%Z mX) as MUc; pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) mX) as WMc end.
    unfold RCTX in MUc.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR3 : rmrep (set_head LFree (Some nx) st2) mX) end.
    { eapply (rmrep_ctx_frameW st2 _ _ _ _ MR2 MUc WMc); try reflexivity.
      - intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - left. unfold rctx_head_cells, rsecw, RCTX. ctx_cells_cbn. unfold pw at 1. cbn [oconc]. change (conc (set_head LFree (Some nx) st2) nx) with (conc st nx).
        unfold pw. unfold wz at 4.
        lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX 602800 _ |- _ => exact H end.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia. }
    clear MUc WMc C1.
    (* [comment removed for export] *)
    st1.
    assert (EQ : dequeue LFree h st = upd_meta h clr_links (set_head LFree (Some nx) st2)).
    { rewrite dequeue_mid. unfold deq_mid. rewrite HN, HP. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx h NEn). cbn [negb get_head].
      rewrite !upd_meta_put. fold st1. fold st2. rewrite ctx_put_meta. unfold st1. rewrite ctx_put_meta. rewrite FMH, optr_eqb_refl. reflexivity. }
    rewrite EQ.
    change (conc st h) with (conc (set_head LFree (Some nx) st2) h). change (Z_to_bv 64 602648) with (Z_to_bv 64 RSSP_GUARD).
    eapply evt_mono.
    { eapply (ram_tail sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo (set_head LFree (Some nx) st2) h);
        [exact MR3 | | apply meta_slot_same_areas with st; [reflexivity| exact MSh] | | | atop_facts; lia | lia].
      - lazymatch goal with H : mem_inv (run_segments psegs rc_inp rc_sp rc_mb) ?mX |- _ => exact H end.
      - lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX (bv_unsigned sp + -64) _ |- _ => exact H end.
      - lazymatch goal with H : stk (run_segments psegs rc_inp rc_sp rc_mb) ?mX lo _ |- _ => exact H end. }
    intros ms' RP. unfold ram_ret_post in RP |- *.
    destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR').
    do 15 eexists. split; [reflexivity|].
    split.
    { apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
      - eapply rpres_except_trans; [exact MU|]. eapply rpres_except_mono; [exact PE'|]. intros a Ha. apply (proj1 (ram_fp_same st _ lo _ a eq_refl)). exact Ha.
      - cbn [ivs_covered]. repeat split; intros x Hx.
        + apply ram_fp_stack. lia.
        + eapply ram_fp_meta; [exact MR | exact MSh | lia].
        + eapply ram_fp_meta; [exact MR | exact MSp | lia].
        + eapply ram_fp_meta; [exact MR | exact MSn | lia].
        + apply ram_fp_ctx. unfold RCTX. lia. }
    split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_take_walk : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (q : aptr),
  rmrep st m -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m ->
  c_free_meta_head (ctx st) = None -> c_avail_meta_count (ctx st) <> 0 -> 0 <= c_avail_meta_count (ctx st) < 2^64 ->
  c_avail_meta (ctx st) = Some q -> meta_slot st q ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp + -64) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m
               (am_took st q (c_avail_meta_count (ctx st) - 1)) (Z_to_bv 64 (conc st q)))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19bb4) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until q. intros MR MI FMH CNT CR AVM MSq FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rmeta_slot_bounds st m q MR MSq) as (QB0 & QB1 & QB2 & _).
  pose proof MR as (WF & (C1 & _) & _). unfold rctx_head_cells, rsecw in C1. rewrite FMH, AVM in C1.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. atop_facts.
  (* [comment removed for export] *)
  st1. st1.
  rewrite bv_eqb_refl. cbv iota.
  st1. st1.
  assert (CF : bv_eqb (Z_to_bv 64 (c_avail_meta_count (ctx st))) (Z_to_bv 64 0) = false)
    by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; exact CNT).
  rewrite CF; clear CF.
  st1. st1. st1. rewrite ?(unsigned_lit (c_avail_meta_count (ctx st))) by lia.
  replace (c_avail_meta_count (ctx st) + -1) with (c_avail_meta_count (ctx st) - 1) by lia.
  change (Z_to_bv 64 602648) with (Z_to_bv 64 RSSP_GUARD). change (Z_to_bv 64 602792) with (Z_to_bv 64 RMLOCK).
  eapply (ram_b0 sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc m junk lo _ st q);
    [exact MR | exact MI | exact MSq | lia | exact FR | exact ST | atop_facts; lia | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ram_disp0 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate),
  rmrep st m -> c_free_meta_head (ctx st) = None -> c_avail_meta_count (ctx st) = 0 ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
                                   s2 (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19c08) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb)))
      (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x19bb4) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until st. intros MR FMH CNT.
  pose proof MR as (WF & (C1 & _) & _). unfold rctx_head_cells, rsecw in C1. rewrite FMH, CNT in C1.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1. unfold RCTX, RMLOCK in *.
  st1. st1. rewrite bv_eqb_refl. cbv iota.
  st1. st1. rewrite bv_eqb_refl. cbv iota.
  apply evt_done. reflexivity.
Qed.
End CANSEC1.
End RF_am_D.

Module RF_am_E.
(* [comment removed for export] *)
From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require Import F_memcpy.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM15. Import MM15. Import MM15.F_malloc_free. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM12. Import MM12. Import MM12.MallocModel_B. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM06. Import MM06. Import MM06.F_ntf_A. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM07. Import MM07. Import MM07.F_ntf_B. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM13. Import MM13. Import MM13.MallocKit_B. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM14. Import MM14. Import MM14.MallocKit_B3. Import MM07.F_am_A. Import MM07.F_am_K. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM10. Import MM10. Import MM10.F_am_E.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require Import RMallocRep. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require Import RMallocTree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require Import RMallocKit_B. Import PM02. Import PM02.RMallocKit_B3. Import PM20. Import PM20.RF_ntf_A. Import PM15. Import PM15.RF_am_A.
Import PM01. Import PM01.RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *) Context {rc : runConstT}.
Lemma rmemcpy_callZ3 : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D S n : Z) (src junk : list byte),
  bytes_at (run_segments psegs rc_inp rc_sp rc_mb) m S src -> length src = Z.to_nat n ->
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m D [CB (Z.to_nat n) junk] ->
  0 <= D -> D + n <= 2^64 -> 0 <= S -> S + n <= 2^64 -> 0 < n ->
  (S + n <= D \/ D + n <= S) ->
  mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
    /\ munch [(D, D + n)]%Z m m' /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m'
    /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m' D [CB (Z.to_nat n) src])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x201b0) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until junk. intros SRC LEN DST D0 D1 S0 S1 N0 SEP MI.
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (memcpy_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n)); rewrite ?ED, ?ES, ?EN;
      [exact SRC | exact LEN | exact DST | exact SEP | exact MI]. }
  intros ms' P. unfold memcpy_post in P. rewrite !ED, !EN in P.
  destruct P as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m' & -> & MU & WM & MI' & DST' & _).
  do 15 eexists. split; [reflexivity|]. auto.
Qed.

Lemma ru64s_read : forall m A ws (i : Z) w a,
  bytes_at (run_segments psegs rc_inp rc_sp rc_mb) m A (u64s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> a = wa (A + 8 * i) ->
  ov_read_bytes (run_segments psegs rc_inp rc_sp rc_mb) m a 8 = Some (le8 w).
Proof.
  intros m A ws i w a Hb Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read (run_segments psegs rc_inp rc_sp rc_mb) m A (u64s ws) (8 * Z.to_nat i) 8 Hb).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
  rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rrw_cells_app_split : forall m A cs1 cs2,
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m A (cs1 ++ cs2) -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m A cs1 /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 H. split; [eapply rw_cells_prefix; exact H|].
  destruct H as [[WF B] W].
  apply cells_wf_app in WF. destruct WF as [WF1 WF2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [_ B2]. rewrite cells_bytes_length in B2 by exact WF1.
  split; [split; [exact WF2 | exact B2] |].
  rewrite cells_size_app in W. eapply wr_at_sub; [exact W | lia | lia].
Qed.

Lemma rrw_cells_app_join : forall m A cs1 cs2,
  rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m A cs1 -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[WF1 B1] W1] [[WF2 B2] W2]. split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite cells_bytes_length by exact WF1. exact B2.
  - rewrite cells_size_app. destruct W1 as (H0 & H1 & X1). destruct W2 as (H2 & H3 & X2). split; [lia|]. split; [lia|].
    intros i Hi. destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))).
    + apply X1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply X2. lia.
Qed.

Definition ram_entry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 s1x s4x a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' junk,
    ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19bb4) fc None m' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 16)]%Z m m' /\ wmono (run_segments psegs rc_inp rc_sp rc_mb) m m' /\ mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m'
    /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m' (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)
    /\ stk (run_segments psegs rc_inp rc_sp rc_mb) m' lo (bv_unsigned sp + -64)
    /\ rmrep (am_init_st st) m'.

Lemma ram_entry : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (lo : Z) (st : mstate),
  rmrep st m -> mem_inv (run_segments psegs rc_inp rc_sp rc_mb) m -> rauxv_ok m (bv_unsigned sp) ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  (c_init_done (ctx st) = 0 \/ c_init_done (ctx st) = 1) -> s_secret st = 0 -> 0 <= c_secret (ctx st) < 2^64 ->
  evt (run_segments psegs rc_inp rc_sp rc_mb) (ram_entry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19b00) fc None m (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))).
Proof.
  intros until st. intros MR MI AUX ST LO LOLE INIT SEC0 SECR.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR as (WF & (C1 & _) & (_ & _ & PGS & G4 & G5) & _). unfold rctx_head_cells, rsecw in C1.
  unfold RCTX, RGOT_SSP, RSSP_GUARD, RPAGE_SIZE in *. atop_facts. unfold wz in G4.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 16)]%Z m) as MU.
  pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) m) as WM. unfold RCTX in MU.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MUh.
  destruct AUX as (av & vs & r & rnd & AVC & AVL & RND & AB & BAV & AVH & BR & RH & XR).
  Ltac skip_iter i key HB :=
    let RD := fresh "RD" in
    st1;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (ru64s_read mX _ _ i (wz key) (wa (_ + 8 * i)) HB eq_refl ltac:(lia) eq_refl) as RD end;
    st1; try clear RD;
    st1; change (bv_eqb (wz key) (Z_to_bv 64 25)) with false; cbv iota;
    st1; change (negb (bv_eqb (wz key) (Z_to_bv 64 0))) with true; cbv iota;
    st1.
  (* The scan is the same for both kernels up to AT_EXECFN; a CONFIG_RSEQ
     kernel lays two more pairs before AT_NULL. *)
  destruct r.
  - try (unfold rauxv_list in AVH; rewrite length_map in AVH; cbn [length app] in AVH).
    pose proof sec_range as SECR'.
    unfold RAUXV_CELL in AVC.
    (* [comment removed for export] *)
    st1. carve_frame 64%nat ST. st1. st1. st1. st1. st1. st1.
    (* [comment removed for export] *)
    st1. st1. st1. st1. st1. st1.
    (* [comment removed for export] *)
    st1. rewrite sx32_wz by lia. st1. st1.
    (* [comment removed for export] *)
    st1.
    lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) _ (bv_unsigned sp + -64) (CB 8 ?j :: _) |- _ => set (junk8 := j) in H; clearbody junk8 end.
    destruct INIT as [I0|I1].
    2:{ (* [comment removed for export] *)
        rewrite I1. change (negb (bv_eqb (wz 1) (Z_to_bv 64 0))) with true. cbv iota.
        st1. st1. st1. change (bv_ltu (Z_to_bv 64 4096) (wz 4096)) with false. cbv iota. st1.
        apply evt_done. unfold ram_entry_post, RCTX, RSSP_GUARD, RMLOCK. do 20 eexists. split; [reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FR|]. split; [exact ST|].
        unfold am_init_st. rewrite I1. cbn [Z.eqb Pos.eqb].
        eapply rmrep_transport_high; [exact MR| exact MUh| exact WM|]. intros l h [E|[]]; inversion E; subst; atop_facts; lia. }
    (* [comment removed for export] *)
    rewrite I0. change (negb (bv_eqb (wz 0) (Z_to_bv 64 0))) with false. cbv iota.
    (* [comment removed for export] *)
    st1. st1. st1. st1. st1. st1. st1. st1. st1.
    (* [comment removed for export] *)
    skip_iter 0 33 AVL.
    skip_iter 2 40 AVL. skip_iter 4 41 AVL. skip_iter 6 42 AVL. skip_iter 8 43 AVL.
    skip_iter 10 44 AVL. skip_iter 12 45 AVL. skip_iter 14 46 AVL. skip_iter 16 47 AVL.
    skip_iter 18 51 AVL. skip_iter 20 16 AVL. skip_iter 22 6 AVL. skip_iter 24 17 AVL.
    skip_iter 26 3 AVL. skip_iter 28 4 AVL. skip_iter 30 5 AVL. skip_iter 32 7 AVL.
    skip_iter 34 8 AVL. skip_iter 36 9 AVL. skip_iter 38 11 AVL. skip_iter 40 12 AVL.
    skip_iter 42 13 AVL. skip_iter 44 14 AVL. skip_iter 46 23 AVL.
    (* [comment removed for export] *)
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (ru64s_read mX _ _ 48 (wz 25) (wa (_ + 8 * 48)) AVL eq_refl ltac:(lia) eq_refl) as RD end.
    st1. try clear RD.
    st1. change (bv_eqb (wz 25) (Z_to_bv 64 25)) with true. cbv iota.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (ru64s_read mX _ _ 49 (wz rnd) (wa (_ + 8 * 49)) AVL eq_refl ltac:(lia) eq_refl) as RD end.
    st1. try clear RD. st1. st1. st1.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      lazymatch type of FR with rw_cells _ _ _ (?c1 :: ?rest) =>
        destruct (rrw_cells_app_split mX _ [c1] rest FR) as [FRm FRc];
        cbn [cells_size csize Nat.add] in FRc;
        replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) in FRc by lia;
        apply (rw_cells_merge (run_segments psegs rc_inp rc_sp rc_mb) mX _ [] [c1] []) in FRm; cbn [cells_size csize Nat.add cells_bytes cbytes app] in FRm;
        rewrite app_nil_r in FRm; clear FR
      end end.
    (* [comment removed for export] *)
    st1.
    call rmemcpy_callZ3.
    1:{ exact RND. } 1:{ reflexivity. } 1:{ exact FRm. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
    1:{ lazymatch goal with H : mem_inv (run_segments psegs rc_inp rc_sp rc_mb) ?mX |- mem_inv (run_segments psegs rc_inp rc_sp rc_mb) ?mX => exact H end. }
    lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX (bv_unsigned sp + -64) [CB _ (le8 (wz SECRET))] |- _ => rename H into DST end.
    (* [comment removed for export] *)
    st1. st1.
    (* [comment removed for export] *)
    (* AT_EXECFN and the CONFIG_RSEQ pair follow AT_RANDOM. *)
    skip_iter 50 31 AVL. skip_iter 52 27 AVL. skip_iter 54 28 AVL.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (ru64s_read mX _ _ 56 (wz 0) (wa (_ + 8 * 56)) AVL eq_refl ltac:(lia) eq_refl) as RD end.
    st1. try clear RD.
    st1. change (bv_eqb (wz 0) (Z_to_bv 64 25)) with false. cbv iota.
    st1. change (negb (bv_eqb (wz 0) (Z_to_bv 64 0))) with false. cbv iota.
    (* [comment removed for export] *)
    lazymatch type of DST with rw_cells _ ?mX _ _ =>
      assert (DST8 : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) mX (bv_unsigned sp + -64) [C8 (wz SECRET)])
        by (destruct DST as [[_ B] W]; cbn [cells_bytes cbytes app] in B; rewrite app_nil_r in B;
            split; [split; [cbn; tauto| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact B]| exact W]);
      clear DST end.
    st1.
    (* [comment removed for export] *)
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MRX : rmrep st mX) by (eapply rmrep_transport_high; [exact MR| exact MUh| exact WM|]; intros l h [E|[]]; inversion E; subst; atop_facts; lia);
      pose proof (munch_refl [(RCTX, RCTX + 16)]%Z mX) as MUc; pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) mX) as WMc end.
    clear MUh. unfold RCTX in MUc.
    (* [comment removed for export] *)
    st1. st1.
    set (stI := upd_ctx (fun c => set_init_done 1 (set_secret 0 c)) st).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRI : rmrep stI mX) end.
    { eapply (rmrep_ctx_frameW st stI _ _ _ MRX MUc WMc); try reflexivity.
      - intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - left. unfold rctx_head_cells, rsecw, RCTX. cbn [ctx stI upd_ctx s_ctx set_init_done set_secret c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
              c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
        change (pw stI ?q) with (pw st q). unfold wz at 2. rewrite Z.mul_1_r.
        lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX 602800 _ |- _ => exact H end.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia. }
    clear MUc WMc MRX.
    (* [comment removed for export] *)
    st1. st1. st1. change (bv_ltu (Z_to_bv 64 4096) (wz 4096)) with false. cbv iota. st1.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      lazymatch goal with Hm : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) mX (bv_unsigned sp + -64) ?csm, Hc : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) mX (bv_unsigned sp + -56) ?csc |- _ =>
        pose proof (rrw_cells_app_join mX _ csm csc Hm ltac:(cbn [cells_size csize Nat.add]; replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) by lia; exact Hc)) as J2;
        cbn [app] in J2; clear Hm Hc;
        lazymatch type of J2 with rw_cells _ _ _ (?c1 :: ?rest) =>
          apply (rw_cells_merge (run_segments psegs rc_inp rc_sp rc_mb) mX _ [] [c1] rest) in J2; cbn [cells_size csize Nat.add cells_bytes cbytes app] in J2; rewrite app_nil_r in J2 end
      end end.
    apply evt_done. unfold ram_entry_post, RCTX, RSSP_GUARD, RMLOCK. do 20 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact J2|]. split; [exact ST|].
    unfold am_init_st. rewrite I0, SEC0. cbn [Z.eqb]. exact MRI.
  - try (unfold rauxv_list in AVH; rewrite length_map in AVH; cbn [length app] in AVH).
    pose proof sec_range as SECR'.
    unfold RAUXV_CELL in AVC.
    (* [comment removed for export] *)
    st1. carve_frame 64%nat ST. st1. st1. st1. st1. st1. st1.
    (* [comment removed for export] *)
    st1. st1. st1. st1. st1. st1.
    (* [comment removed for export] *)
    st1. rewrite sx32_wz by lia. st1. st1.
    (* [comment removed for export] *)
    st1.
    lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) _ (bv_unsigned sp + -64) (CB 8 ?j :: _) |- _ => set (junk8 := j) in H; clearbody junk8 end.
    destruct INIT as [I0|I1].
    2:{ (* [comment removed for export] *)
        rewrite I1. change (negb (bv_eqb (wz 1) (Z_to_bv 64 0))) with true. cbv iota.
        st1. st1. st1. change (bv_ltu (Z_to_bv 64 4096) (wz 4096)) with false. cbv iota. st1.
        apply evt_done. unfold ram_entry_post, RCTX, RSSP_GUARD, RMLOCK. do 20 eexists. split; [reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FR|]. split; [exact ST|].
        unfold am_init_st. rewrite I1. cbn [Z.eqb Pos.eqb].
        eapply rmrep_transport_high; [exact MR| exact MUh| exact WM|]. intros l h [E|[]]; inversion E; subst; atop_facts; lia. }
    (* [comment removed for export] *)
    rewrite I0. change (negb (bv_eqb (wz 0) (Z_to_bv 64 0))) with false. cbv iota.
    (* [comment removed for export] *)
    st1. st1. st1. st1. st1. st1. st1. st1. st1.
    (* [comment removed for export] *)
    skip_iter 0 33 AVL.
    skip_iter 2 40 AVL. skip_iter 4 41 AVL. skip_iter 6 42 AVL. skip_iter 8 43 AVL.
    skip_iter 10 44 AVL. skip_iter 12 45 AVL. skip_iter 14 46 AVL. skip_iter 16 47 AVL.
    skip_iter 18 51 AVL. skip_iter 20 16 AVL. skip_iter 22 6 AVL. skip_iter 24 17 AVL.
    skip_iter 26 3 AVL. skip_iter 28 4 AVL. skip_iter 30 5 AVL. skip_iter 32 7 AVL.
    skip_iter 34 8 AVL. skip_iter 36 9 AVL. skip_iter 38 11 AVL. skip_iter 40 12 AVL.
    skip_iter 42 13 AVL. skip_iter 44 14 AVL. skip_iter 46 23 AVL.
    (* [comment removed for export] *)
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (ru64s_read mX _ _ 48 (wz 25) (wa (_ + 8 * 48)) AVL eq_refl ltac:(lia) eq_refl) as RD end.
    st1. try clear RD.
    st1. change (bv_eqb (wz 25) (Z_to_bv 64 25)) with true. cbv iota.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (ru64s_read mX _ _ 49 (wz rnd) (wa (_ + 8 * 49)) AVL eq_refl ltac:(lia) eq_refl) as RD end.
    st1. try clear RD. st1. st1. st1.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      lazymatch type of FR with rw_cells _ _ _ (?c1 :: ?rest) =>
        destruct (rrw_cells_app_split mX _ [c1] rest FR) as [FRm FRc];
        cbn [cells_size csize Nat.add] in FRc;
        replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) in FRc by lia;
        apply (rw_cells_merge (run_segments psegs rc_inp rc_sp rc_mb) mX _ [] [c1] []) in FRm; cbn [cells_size csize Nat.add cells_bytes cbytes app] in FRm;
        rewrite app_nil_r in FRm; clear FR
      end end.
    (* [comment removed for export] *)
    st1.
    call rmemcpy_callZ3.
    1:{ exact RND. } 1:{ reflexivity. } 1:{ exact FRm. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
    1:{ lazymatch goal with H : mem_inv (run_segments psegs rc_inp rc_sp rc_mb) ?mX |- mem_inv (run_segments psegs rc_inp rc_sp rc_mb) ?mX => exact H end. }
    lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX (bv_unsigned sp + -64) [CB _ (le8 (wz SECRET))] |- _ => rename H into DST end.
    (* [comment removed for export] *)
    st1. st1.
    (* [comment removed for export] *)
    (* AT_EXECFN follows AT_RANDOM; this kernel lays no CONFIG_RSEQ pair. *)
    skip_iter 50 31 AVL.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (ru64s_read mX _ _ 52 (wz 0) (wa (_ + 8 * 52)) AVL eq_refl ltac:(lia) eq_refl) as RD end.
    st1. try clear RD.
    st1. change (bv_eqb (wz 0) (Z_to_bv 64 25)) with false. cbv iota.
    st1. change (negb (bv_eqb (wz 0) (Z_to_bv 64 0))) with false. cbv iota.
    (* [comment removed for export] *)
    lazymatch type of DST with rw_cells _ ?mX _ _ =>
      assert (DST8 : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) mX (bv_unsigned sp + -64) [C8 (wz SECRET)])
        by (destruct DST as [[_ B] W]; cbn [cells_bytes cbytes app] in B; rewrite app_nil_r in B;
            split; [split; [cbn; tauto| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact B]| exact W]);
      clear DST end.
    st1.
    (* [comment removed for export] *)
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MRX : rmrep st mX) by (eapply rmrep_transport_high; [exact MR| exact MUh| exact WM|]; intros l h [E|[]]; inversion E; subst; atop_facts; lia);
      pose proof (munch_refl [(RCTX, RCTX + 16)]%Z mX) as MUc; pose proof (wmono_refl (run_segments psegs rc_inp rc_sp rc_mb) mX) as WMc end.
    clear MUh. unfold RCTX in MUc.
    (* [comment removed for export] *)
    st1. st1.
    set (stI := upd_ctx (fun c => set_init_done 1 (set_secret 0 c)) st).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRI : rmrep stI mX) end.
    { eapply (rmrep_ctx_frameW st stI _ _ _ MRX MUc WMc); try reflexivity.
      - intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - left. unfold rctx_head_cells, rsecw, RCTX. cbn [ctx stI upd_ctx s_ctx set_init_done set_secret c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
              c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
        change (pw stI ?q) with (pw st q). unfold wz at 2. rewrite Z.mul_1_r.
        lazymatch goal with H : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) ?mX 602800 _ |- _ => exact H end.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia. }
    clear MUc WMc MRX.
    (* [comment removed for export] *)
    st1. st1. st1. change (bv_ltu (Z_to_bv 64 4096) (wz 4096)) with false. cbv iota. st1.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      lazymatch goal with Hm : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) mX (bv_unsigned sp + -64) ?csm, Hc : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) mX (bv_unsigned sp + -56) ?csc |- _ =>
        pose proof (rrw_cells_app_join mX _ csm csc Hm ltac:(cbn [cells_size csize Nat.add]; replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) by lia; exact Hc)) as J2;
        cbn [app] in J2; clear Hm Hc;
        lazymatch type of J2 with rw_cells _ _ _ (?c1 :: ?rest) =>
          apply (rw_cells_merge (run_segments psegs rc_inp rc_sp rc_mb) mX _ [] [c1] rest) in J2; cbn [cells_size csize Nat.add cells_bytes cbytes app] in J2; rewrite app_nil_r in J2 end
      end end.
    apply evt_done. unfold ram_entry_post, RCTX, RSSP_GUARD, RMLOCK. do 20 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact J2|]. split; [exact ST|].
    unfold am_init_st. rewrite I0, SEC0. cbn [Z.eqb]. exact MRI.
Qed.
End CANSEC1.
End RF_am_E.
