(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import decidable.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes
  PureModel VmLedger AllocIface AsanCeil AgentLib.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocShape RefLrSc RefStep RefStmts RefSys RefPieces RefStep3.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng Require Import RefStepR.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Loops.
Context {fx : FPState} {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL}.
#[local] Existing Instance reloc_layout.

(* [comment removed for export] *)
Lemma span_run : forall fuel (a6 t0 a4 a5 cnt : word) (R : bvmap 5 word) M rom md T,
  md_pure md ->
  m_span_loop fuel a6 t0 a4 a5 = Some cnt ->
  getr R 16 = a6 -> getr R 5 = t0 -> getr R 14 = a4 -> getr R 15 = a5 -> getr R 17 = Z_to_bv 64 4096 ->
  (forall R' : bvmap 5 word,
     (forall r, wreg [5;6;14;16]%Z r = false -> getr R' r = getr R r) -> getr R' 14 = cnt ->
     realizes ml_segs (mkCfg (mkst R' (pc+ PC_ALLOC_SLOT 0x530) M rom) md) T) ->
  realizes ml_segs (mkCfg (mkst R (pc+ PC_ALLOC_SLOT 0x51c) M rom) md) T.
Proof.
  induction fuel as [|fuel IH]; intros a6 t0 a4 a5 cnt R M rom md T Hp Hsp H16 H5 H14 H15 H17 HK.
  { discriminate Hsp. }
  pose proof I as HS.
  cbn [m_span_loop] in Hsp. unfold MallocOps.wlit in Hsp.
  mach Hp HS. mach Hp HS. mach Hp HS. mach Hp HS.
  destruct (c_lts (v_xor a6 t0) (Z_to_bv 64 4096)) eqn:Hc.
  - mach_br_dir Hp HS true ltac:(by_bool Hc).
    eapply (IH _ _ _ _ cnt); [ exact Hp | exact Hsp | val_tac | val_tac | val_tac | val_tac | val_tac | ].
    intros R' Hkeep' HR. keep_facts Hkeep'. apply HK; [ keep_tac | exact HR ].
  - mach_br_dir Hp HS false ltac:(by_bool Hc).
    injection Hsp as <-. apply HK; [ keep_tac | val_tac ].
Qed.

(* [comment removed for export] *)
Lemma halve_run : forall j (x usage : word) (R : bvmap 5 word) M rom md T,
  md_pure md ->
  getr R 13 = x -> getr R 10 = usage ->
  MallocOps.is0 (v_andi x 1) = true -> bv_unsigned x < 2 ^ Z.of_nat j -> bv_unsigned x < 2^31 ->
  (forall R' : bvmap 5 word,
     (forall r, wreg [12;13;14]%Z r = false -> getr R' r = getr R r) -> getr R' 12 = halveF usage j x ->
     realizes ml_segs (mkCfg (mkst R' (pc+ PC_ALLOC_SLOT 0x290) M rom) md) T) ->
  realizes ml_segs (mkCfg (mkst R (pc+ PC_ALLOC_SLOT 0x268) M rom) md) T.
Proof.
  induction j as [|j IH]; intros x usage R M rom md T Hp H13 H10 Hev Hxj Hx31 HK.
  - (* [comment removed for export] *)
    pose proof I as HS. pose proof (u64_range x) as Hx0. change (2 ^ Z.of_nat 0) with 1 in Hxj.
    mach Hp HS.
    mach_br_dir Hp HS true ltac:(rewrite c_ltu_u, (u_slliw2_0 x) by lia; pose proof (u64_range usage); apply Z.ltb_ge; lia).
    mach Hp HS. apply HK; [ keep_tac | rewrite halveF_O; val_tac ].
  - pose proof I as HS. pose proof (u64_range x) as Hx0.
    mach Hp HS.
    destruct (c_ltu usage (v_slliw x 2)) eqn:Hc.
    + mach_br_dir Hp HS false ltac:(by_bool Hc).
      mach Hp HS. mach Hp HS. mach Hp HS.
      pose proof (u_srliw1 x Hx31) as Hux.
      destruct (c_eq (v_andi x 2) (Z_to_bv 64 0)) eqn:Hb.
      * (* [comment removed for export] *)
        mach_br_dir Hp HS true ltac:(by_bool Hb).
        eapply (IH (v_srliw x 1) usage); [ exact Hp | val_tac | val_tac | | | | ].
        -- rewrite andi2_srliw by exact Hx31. exact Hb.
        -- rewrite Hux. rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hxj by lia. lia.
        -- rewrite Hux. lia.
        -- intros R' Hkeep' HR. keep_facts Hkeep'. apply HK; [ keep_tac |].
           rewrite HR, halveF_S, Hev, Hc. reflexivity.
      * mach_br_dir Hp HS false ltac:(by_bool Hb). mach Hp HS.
        apply HK; [ keep_tac |].
        rewrite halveF_S, Hev, Hc. cbn [negb].
        rewrite halveF_odd by (rewrite andi2_srliw by exact Hx31; exact Hb). val_tac.
    + mach_br_dir Hp HS true ltac:(by_bool Hc). mach Hp HS.
      apply HK; [ keep_tac |]. rewrite halveF_S, Hev, Hc. val_tac.
Qed.

(* [comment removed for export] *)
Lemma shrink_run : forall j (y size : word) (R : bvmap 5 word) M rom md T,
  md_pure md ->
  getr R 12 = y -> getr R 24 = size ->
  bv_unsigned y < 2 ^ Z.of_nat j -> bv_unsigned y < 2^31 ->
  (forall R' : bvmap 5 word,
     (forall r, wreg [12;13;19]%Z r = false -> getr R' r = getr R r) -> getr R' 19 = shrinkF size j y ->
     realizes ml_segs (mkCfg (mkst R' (pc+ PC_ALLOC_SLOT 0x2a4) M rom) md) T) ->
  realizes ml_segs (mkCfg (mkst R (pc+ PC_ALLOC_SLOT 0x290) M rom) md) T.
Proof.
  induction j as [|j IH]; intros y size R M rom md T Hp H12 H24 Hyj Hy31 HK.
  - pose proof I as HS. pose proof (u64_range y) as Hy0. change (2 ^ Z.of_nat 0) with 1 in Hyj.
    mach Hp HS. mach Hp HS. mach Hp HS. mach Hp HS.
    mach_br_dir Hp HS false ltac:(rewrite c_eq_u, (u_srli_mul_0 size y 20) by lia; reflexivity).
    apply HK; [ keep_tac | rewrite shrinkF_O; val_tac ].
  - pose proof I as HS. pose proof (u64_range y) as Hy0.
    mach Hp HS. mach Hp HS. mach Hp HS. mach Hp HS.
    destruct (MallocOps.is0 (v_srli (v_mul size y) 20)) eqn:Hc.
    + mach_br_dir Hp HS false ltac:(by_bool Hc).
      apply HK; [ keep_tac | rewrite shrinkF_S, Hc; val_tac ].
    + mach_br_dir Hp HS true ltac:(by_bool Hc).
      pose proof (u_srliw1 y Hy31) as Huy.
      eapply (IH (v_srliw y 1) size); [ exact Hp | val_tac | val_tac | | | ].
      * rewrite Huy. rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hyj by lia. lia.
      * rewrite Huy. lia.
      * intros R' Hkeep' HR. keep_facts Hkeep'. apply HK; [ keep_tac |].
        rewrite HR, shrinkF_S, Hc. reflexivity.
Qed.

End Loops.

Section ZL.
Context {fx : FPState} {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL}.
#[local] Existing Instance reloc_layout.
Lemma zl_run {B} : forall k (a2 size : word) md (R : bvmap 5 word) mm rom (s0 s : mstate)
    (K : unit -> M B) (P : B -> mstate -> Prop) (L : B -> mstate -> TSet),
  md_pure md -> magree s mm -> minv s0 s ->
  getr R 12 = a2 -> getr R 24 = size -> getr R 11 = Z_to_bv 64 (Z.of_nat (S k)) -> Z.of_nat (S k) < 2^64 ->
  tsafe (MallocTree.mbind (zlF size (S k) a2) K s) P ->
  (forall s' mm' R',
     magree s' mm' -> minv s0 s' ->
     (forall a, ms_lo s0 <= bv_unsigned a < ms_hi s0 -> mm' a = mm a) ->
     (forall r, wreg [11;12]%Z r = false -> getr R' r = getr R r) ->
     tsafe (K tt s') P ->
     realizes ml_segs (mkCfg (mkst R' (pc+ PC_ALLOC_SLOT 0x448) mm' rom) (with_vmmaps (ms_vm s') md)) (tshape (K tt s') L)) ->
  realizes ml_segs (mkCfg (mkst R (pc+ PC_ALLOC_SLOT 0x438) mm rom) (with_vmmaps (ms_vm s) md))
           (tshape (MallocTree.mbind (zlF size (S k) a2) K s) L).
Proof.
  induction k as [|k IH]; intros a2 size md R mm rom s0 s K P L Hp Hag HI H12 H24 H11 Hk HS HK.
  - pose proof I as HW. note_win HI.
    rewrite zlF_S, zlF_O in HS |- *. munf. mnorm HS.
    mach_st Hp HS Hag HI. mach Hp HS. mach Hp HS.
    mach_br_dir Hp HS false ltac:(vm_compute; reflexivity).
    cur_mstate HS ltac:(fun sb => eapply (HK sb)); [ exact Hag | exact HI | win_same | keep_tac | exact HS ].
  - pose proof I as HW. note_win HI.
    rewrite zlF_S in HS |- *. munf. mnorm HS.
    mach_st Hp HS Hag HI. mach Hp HS. mach Hp HS.
    mach_br_dir Hp HS true ltac:(rewrite word_pred_nat by lia; rewrite c_eq0_nat by lia; apply Z.eqb_neq; lia).
    cur_mstate HS ltac:(fun sb => eapply (IH (v_add a2 size) size md _ _ rom s0 sb));
      [ exact Hp | exact Hag | exact HI | val_tac | val_tac
      | regnorm; apply word_pred_nat; lia | lia | exact HS | ].
    intros s' mm' R' Hag' HI' HJ Hkeep' HS'. keep_facts Hkeep'.
    cur_mstate HS' ltac:(fun sb => eapply (HK sb)); [ exact Hag' | exact HI' | | keep_tac | exact HS' ].
    intros x Hw. rewrite (HJ x Hw). uaddrH Hw. peel x; try reflexivity.
Qed.
End ZL.
