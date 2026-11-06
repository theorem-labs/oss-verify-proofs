(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib Arr. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzDefs. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzModel. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac BzTac2 BzInv. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTables. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzContracts BzContracts0 DecCut DecAux.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecAuxM DecTac DecTac2 DecTacM BzWalkArith3 S0_dec_U13 S0_decCuts.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_decCuts7.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_decCuts7.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_hbCreate.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_hbCreate.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzDefs OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAux OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac.DecAuxB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecAuxM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_dec_U13 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_decCuts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_decCuts7.S0_decCutsB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_decCuts7 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_hbCreate.S0_hbCreateB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_hbCreate.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import DecFast DecFastT.
Local Ltac DecCut.revive H MUL WML AOK ::= DecFast.revive_cached H MUL WML AOK.
Local Ltac DecCut.dpure_from DP ::= DecFast.dpure_from_fast DP.
Local Ltac DecCut.open_dmem DM ::= DecFast.open_dmem_red DM.
Local Ltac DecTac.gb_next keep Wloc IB ::= DecFastT.gb_next_red keep Wloc IB.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import DecFastM.
Local Ltac DecTacM.revive_f H MUL WML AOK ::= DecFastM.revive_f_fast H MUL WML AOK.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import  BzImg0Tac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require RelLia. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require RelLiaR.
Local Ltac lia ::= RelLia.lia_rf3.
Local Ltac StoreFast.tlia ::= RelLiaR.tlia_rr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Definition S0_hbCreateZ_post (ra : word) (spz : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (DS t : Z) (lws bws pws : list word) (lbs : list byte) (minLen maxLen alpha lo : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' lws' bws' pws',
    ms' = MS (mkR ra (Z_to_bv 64 spz) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom s0segs)
    /\ munch [(DS + 45436 + 1032 * t, DS + 45436 + 1032 * t + 1032);
              (DS + 51628 + 1032 * t, DS + 51628 + 1032 * t + 1032);
              (DS + 57820 + 1032 * t, DS + 57820 + 1032 * t + 1032);
              (spz + -64, spz)]%Z m m'
    /\ wmono s0segs m m' /\ mem_inv s0segs m'
    /\ u32arr s0segs m' (DS + 45436 + 1032 * t) lws' /\ length lws' = 258%nat
    /\ u32arr s0segs m' (DS + 51628 + 1032 * t) bws' /\ length bws' = 258%nat
    /\ u32arr s0segs m' (DS + 57820 + 1032 * t) pws' /\ length pws' = 258%nat
    /\ u8arr s0segs m' (DS + 43888 + 258 * t) lbs
    /\ stk s0segs m' lo spz
    /\ (let '(limit, base, perm) := hb_create (sv32 lws) (sv32 bws) (sv32 pws) (uv8 lbs) minLen maxLen alpha in
        ag32s lws' limit 258 /\ ag32s bws' base 258 /\ ag32s pws' perm 258).

Lemma S0_hbCreate_specZ :
  forall (DS t : Z) (lws bws pws : list word) (lbs : list byte) (minLen maxLen alpha lo spz : Z)
         (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  u32arr s0segs m (DS + 45436 + 1032 * t) lws -> length lws = 258%nat ->
  u32arr s0segs m (DS + 51628 + 1032 * t) bws -> length bws = 258%nat ->
  u32arr s0segs m (DS + 57820 + 1032 * t) pws -> length pws = 258%nat ->
  u8arr s0segs m (DS + 43888 + 258 * t) lbs -> length lbs = 258%nat ->
  (0 <= DS)%Z /\ (DS mod 16 = 0)%Z /\ (0 <= t < 6)%Z ->
  (DS + 64144 <= lo)%Z /\ (lo + 64 <= spz)%Z -> (0 <= spz < 2^64)%Z ->
  stk s0segs m lo spz -> mem_inv s0segs m ->
  (1 <= alpha <= 258)%Z -> (1 <= minLen /\ minLen <= maxLen <= 20)%Z ->
  (forall j, (0 <= j < alpha)%Z -> (minLen <= uv8 lbs j <= maxLen)%Z) ->
  a0 = Z_to_bv 64 (DS + 45436 + 1032 * t) -> a1 = Z_to_bv 64 (DS + 51628 + 1032 * t) ->
  a2 = Z_to_bv 64 (DS + 57820 + 1032 * t) -> a3 = Z_to_bv 64 (DS + 43888 + 258 * t) ->
  a4 = Z_to_bv 64 minLen -> a5 = Z_to_bv 64 maxLen -> a6 = Z_to_bv 64 alpha ->
  evt s0segs (S0_hbCreateZ_post ra spz gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DS t lws bws pws lbs minLen maxLen alpha lo m)
      (MS (mkR ra (Z_to_bv 64 spz) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x242d4) fc None m (seg_rom s0segs)).
Proof.
  intros DS t lws bws pws lbs minLen maxLen alpha lo spz ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros ARL LENl ARB LENb ARP LENp AR8 LEN8 HS HLO Hsp ST MI Halpha Hmm Hlen E0 E1 E2 E3 E4 E5 E6.
  assert (E : bv_unsigned (Z_to_bv 64 spz) = spz) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { apply (S0_hbCreate_spec ra (Z_to_bv 64 spz) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             DS t lws bws pws lbs minLen maxLen alpha lo ARL LENl ARB LENb ARP LENp AR8 LEN8 HS);
      [ rewrite E; exact HLO | rewrite E; exact ST | exact MI | exact Halpha | exact Hmm | exact Hlen
      | exact E0 | exact E1 | exact E2 | exact E3 | exact E4 | exact E5 | exact E6 ]. }
  intros ms' PO. unfold S0_hbCreate_post in PO. rewrite E in PO. exact PO.
Qed.


End ACeilS1.
