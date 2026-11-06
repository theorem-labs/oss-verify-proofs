(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg RtCells AProto ABase ARep F_apoison APoisonR_iface I_asan_memmove.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import AU_kit AU_steptac AU_h_kit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import ShadowTac.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import UM_guards.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Stdlib.micromega.Lia.lia ::=
  first [ OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.LiaTuning.zify_prune_relevant; OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.LiaTuning.zify_noeuclid_nosat; Z.euclidean_division_equations_cleanup; xlia zchecker
        | Zify.zify; xlia zchecker ].
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_tight | solve_load_image ].
Local Ltac solve_store ::= solve_store_tight.

Section CANSEC1. Context {rc : runConstT}.
Definition ACOPY : Z := 0xb35b0.
Definition ACOPY_STACK : Z := 48 + 2224.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition win_facts (RNG : footprint) (m : amem) (D k : Z) : Prop :=
  app_blk D (D + k) /\ unpoisoned m D (D + k) /\ rng RNG D k
  /\ exists RLO RHI, (RLO <= D /\ D + k <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)
     /\ wr_at bsegs m (shad RLO) (shad RHI - shad RLO) /\ rng RNG (shad RLO) (shad RHI - shad RLO).

Definition acopy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S D k : Z) (src : list byte) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (S + k)) (Z_to_bv 64 (D + k)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - ACOPY_STACK, bv_unsigned sp); (D, D + k)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' D [CB (Z.to_nat k) src]
    /\ bytes_at bsegs m' S src.

Lemma acopy_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (S D k lo : Z) (src junk : list byte),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - ACOPY_STACK -> bv_unsigned sp + 16 <= 2^47 ->
  rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m ->
  a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 (S + k) -> a2 = Z_to_bv 64 D ->
  0 < k <= 2^40 -> 0 < S -> S + k <= lo -> 0 < D -> D + k <= lo ->
  (S + k <= D \/ D + k <= S) ->
  bytes_at bsegs m S src -> length src = Z.to_nat k ->
  rw_cells bsegs m D [CB (Z.to_nat k) junk] ->
  win_facts RNG m S k -> win_facts RNG m D k ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (acopy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S D k src lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ACOPY) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros MI ST LOA LOS SPH GOT RIC SHB INI LAY -> -> -> KK S0 SL D0 DL SEP SRC LEN DST WFS WFD RIMG RSTK.
  unfold ACOPY, ACOPY_STACK in *. pose proof atop_range as ATR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold acopy_post.
  pose proof (munch_refl [(bv_unsigned sp - 2272, bv_unsigned sp); (D, D + k)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  (* [comment removed for export] *)
  pose proof SRC as SRC0. change (?P) with (sf_hide P) in SRC0.
  carve_frame 48%nat ST.
  zstep. zstep. zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
  zstep. zstep. zstep.                    (* [comment removed for export] *)
  zstep.                                  (* [comment removed for export] *)
  try replace (S + k - S) with k by lia.
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K KK; lia| clear K]).   (* [comment removed for export] *)
  zstep. zstep. zstep.                    (* [comment removed for export] *)
  zstep.                                  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MUx : munch _ m mm, WMx : wmono bsegs m mm, DSTx : rw_cells bsegs mm D _ |- _ =>
    unfold sf_hide in SRC0;
    assert (SRC1 : bytes_at bsegs mm S src)
      by (eapply bytes_at_transport; [exact SRC0| exact MUx| cbn [disjoint_from]; rewrite LEN, Z2Nat.id by lia; clear - LOS SL SEP KK; lia]);
    change (bytes_at bsegs m S src) with (sf_hide (bytes_at bsegs m S src)) in SRC0;
    destruct WFS as (APPs & UNPs0 & RWs & RLOs & RHIs & HUs & WHs0 & RHs);
    destruct WFD as (APPd & UNPd0 & RWd & RLOd & RHId & HUd & WHd0 & RHd);
    assert (UNPs : unpoisoned mm S (S + k))
      by (eapply unpoisoned_munch; [exact UNPs0| exact MUx|]; cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF; unfold app_blk, KLOW, KHIGH, KEND in APPs, APPd;
          clear - LOS LOA ATR SL DL S0 D0 SEP KK APPs APPd; Z.div_mod_to_equations; lia);
    assert (UNPd : unpoisoned mm D (D + k))
      by (eapply unpoisoned_munch; [exact UNPd0| exact MUx|]; cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF; unfold app_blk, KLOW, KHIGH, KEND in APPs, APPd;
          clear - LOS LOA ATR SL DL S0 D0 SEP KK APPs APPd; Z.div_mod_to_equations; lia);
    pose proof (wr_at_transport bsegs m mm _ _ WHs0 WMx) as WHs; pose proof (wr_at_transport bsegs m mm _ _ WHd0 WMx) as WHd;
    clear UNPs0 UNPd0 WHs0 WHd0;
    name_sp sp (-48)%Z;
    eapply evtF_cut;
    [ eapply (asan_memmove_spec RNG) with (lo := lo) (src := src) (RLO1 := RLOs) (RHI1 := RHIs) (RLO2 := RLOd) (RHI2 := RHId);
      rewrite ?Hsp; rewrite ?unsigned_lit by lia;
      first [ exact SRC1 | exact LEN | exact DSTx | exact APPs | exact APPd | exact UNPs | exact UNPd | exact RWs | exact RWd | exact HUs | exact HUd | exact WHs | exact WHd | exact RHs | exact RHd
            | exact RIMG | eassumption
            | (unfold KHIGH; clear - LOA ATR; lia)
            | (clear - SEP; lia)
            | (left; clear - SL LOS; lia)
            | (left; clear - DL LOS; lia)
            | (eapply rng_sub'; [exact RSTK| clear - LOS LOA LO0; lia])
            | (clear - KK; lia) | lia ]
    | cbv beta; unfold asan_memmove_post; rewrite ?Hsp; rewrite ?unsigned_lit by lia;
      clear APPs APPd UNPs UNPd RWs RWd HUs HUd WHs WHd RHs RHd SRC1; post_call bsegs mm ]
    end end.
  all: rewrite ?unsigned_lit in * by lia.
  try unname_sp.
  (* [comment removed for export] *)
  zstep.                                  (* [comment removed for export] *)
  try replace (k + D) with (D + k) by lia.
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K KK D0 DL LOS RSP; lia| clear K]).   (* [comment removed for export] *)
  zstep. zstep. zstep.                    (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K KK D0 DL LOS RSP; ubguard K; lia| clear K]).   (* [comment removed for export] *)
  zstep. zstep.                           (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K KK S0 SL LOS RSP; ubguard K; lia| clear K]).   (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.             (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K KK S0 SL LOS RSP; ubguard K; lia| clear K]).   (* [comment removed for export] *)
  zstep; (let K := fresh "Kz" in if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; clear - K KK; ubguard K; lia| clear K]).   (* [comment removed for export] *)
  zstep.                                  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep.   (* [comment removed for export] *)
  lazymatch goal with H : stk bsegs _ lo _ |- _ => release_frame FR H (bv_unsigned sp) end.
  zstep.                                  (* [comment removed for export] *)
  apply evtF_done.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
    lazymatch goal with MUx : munch _ m mm, WMx : wmono bsegs m mm, MIx : mem_inv bsegs mm, STx : stk bsegs mm lo _, BLKx : rw_cells bsegs mm D [CB _ src], SRCx : bytes_at bsegs mm S src |- _ =>
    do 13 eexists; exists mm; split; [reflexivity|];
    split; [exact MUx|]; split; [exact WMx|]; split; [exact MIx|]; split; [exact STx|]; split; [exact BLKx| exact SRCx]
    end end.
Qed.
End CANSEC1.
