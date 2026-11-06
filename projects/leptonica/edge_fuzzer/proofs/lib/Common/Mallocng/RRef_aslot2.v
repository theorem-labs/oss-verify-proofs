(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import decidable.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes
  PureModel VmLedger AllocIface AsanCeil AgentLib.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocShape RefLrSc RefStep RefStmts RefSys RefPieces RefStep3.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require Import RRef_syswrap RRef_enframe RRef_ameta RRef_loops RRef_aslot1.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require Import RefStepR.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Pieces2.
Context {fx : FPState} {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL}.
#[local] Existing Instance reloc_layout.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition as_tav_pc (x : option (word * word)) : word :=
  match x with None => (pc+ PC_ALLOC_SLOT 0x1e0) | Some _ => (pc+ PC_ALLOC_SLOT 0x1a0) end.
Definition as_tav_xr (x : option (word * word)) (R' : bvmap 5 word) : Prop :=
  match x with Some (a, b) => getr R' 10 = a /\ getr R' 11 = b | None => True end.

Lemma as_tav_piece {B} : forall md (R : bvmap 5 word) mm rom (s0 s : mstate) (pm m0 : word)
    (K : option (word * word) -> M B) (P : B -> mstate -> Prop) (L : B -> mstate -> TSet),
  md_pure md -> magree s mm -> minv s0 s ->
  getr R 12 = m0 -> getr R 21 = pm -> getr R 22 = A_LOCK ->
  tsafe (MallocTree.mbind (as_tav pm m0) K s) P ->
  (forall x s' mm' R',
     magree s' mm' -> minv s0 s' ->
     (forall a, ms_lo s0 <= bv_unsigned a < ms_hi s0 -> mm' a = mm a) ->
     (forall r, wreg [5;6;10;11;12;13;14;15;16;17]%Z r = false -> getr R' r = getr R r) ->
     as_tav_xr x R' ->
     tsafe (K x s') P ->
     realizes ml_segs (mkCfg (mkst R' (as_tav_pc x) mm' rom) (with_vmmaps (ms_vm s') md)) (tshape (K x s') L)) ->
  realizes ml_segs (mkCfg (mkst R (pc+ PC_ALLOC_SLOT 0x60) mm rom) (with_vmmaps (ms_vm s) md))
           (tshape (MallocTree.mbind (as_tav pm m0) K s) L).
Proof.
  intros md R mm rom s0 s pm m0 K P L Hp Hag HI H12 H21 H22 HS HK.
  pose proof I as HW. pose proof I as Hret. note_win HI. sys_hyps.
  unfold as_tav, as_tav_xr in HS |- *. munf. mnorm HS.
  (* [comment removed for export] *)
  mstepx Hp HS Hag HI HW HK Hret as_calls.
  all: piece_exit_k_at (bv_unsigned PC_ALLOC_SLOT + 0x1e0) HK K Hag HI HS.
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x68).
  mstepx Hp HS Hag HI HW HK Hret as_calls.
  all: run_exit_k_not_at (bv_unsigned PC_ALLOC_SLOT + 0x74) Hp HS Hag HI HW HK Hret K as_tav_pc.
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x7c).
  mach_cutk HS Hag HI HW (option word)
    (fun x : option word => match x with Some _ => (pc+ PC_ALLOC_SLOT 0xc8) | None => (pc+ PC_ALLOC_SLOT 0x1e0) end)
    [10;11;12]%Z (fun (x : option word) (R' : bvmap 5 word) => match x with Some m => getr R' 10 = m | None => True end)
    as CUT1 K1.
  { as_run Hp HS Hag HI HW HK Hret K1
      (fun x : option word => match x with Some _ => (pc+ PC_ALLOC_SLOT 0xc8) | None => (pc+ PC_ALLOC_SLOT 0x1e0) end).
    all: use_cut_k CUT1 K1 Hag HI HS. }
  intros [m|] HX HS; mnorm HS.
  2: { piece_exit_k HK K Hag HI HS. }
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0xd8).
  mach_join Hp HS Hag HI HW (bv_unsigned PC_ALLOC_SLOT + 0xf4) [10;11;13]%Z [10;13]%Z.
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x108).
  mach_cutk HS Hag HI HW (option word) (fun _ : option word => (pc+ PC_ALLOC_SLOT 0x11c))
    [5;6;10;11;12;13;14;15;16;17]%Z
    (fun (x : option word) (R' : bvmap 5 word) => match x with Some m3 => getr R' 10 = m3 | None => False end)
    as CUT2 K2.
  { (* [comment removed for export] *)
    mstepx Hp HS Hag HI HW HK Hret as_calls.
    all: use_cut_k_at (bv_unsigned PC_ALLOC_SLOT + 0x11c) CUT2 K2 Hag HI HS.
    (* [comment removed for export] *)
    mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x110).
    mstepx Hp HS Hag HI HW HK Hret as_calls.
    all: run_cut_k_not_at (bv_unsigned PC_ALLOC_SLOT + 0x4d4) Hp HS Hag HI HW HK Hret CUT2 K2 (fun _ : option word => (pc+ PC_ALLOC_SLOT 0x11c)).
    (* [comment removed for export] *)
    mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x51c).
    lazymatch goal with
    | |- context [m_span_loop ?f ?a ?b ?c ?d] =>
        let HSP := fresh "HSP" in
        destruct (m_span_loop f a b c d) as [cnt|] eqn:HSP;
        [ try rewrite HSP in HS
        | exfalso; try rewrite HSP in HS; clear -HS; cbn [MallocTree.mbind mcrash tbind tsafe] in HS; exact HS ]
    end.
    mnorm HS.
    eapply (span_run 40); [ mpure Hp | exact HSP | val_tac | val_tac | val_tac | val_tac | val_tac | ].
    intros Rs Hkeeps HRs. keep_facts Hkeeps.
    (* [comment removed for export] *)
    mach Hp HS. mach Hp HS.
    lazymatch type of HS with tsafe (MallocTree.mbind (m_sb _ (v_or (v_andi (v_addi ?cnt' (-1)) 31) _)) _ _) _ =>
      mach_vjoin (bv_unsigned PC_ALLOC_SLOT + 0x540) [14]%Z (fun R' : bvmap 5 word => getr R' 14 = cnt') as CUT3
    end.
    { mach_pure Hp HS (bv_unsigned PC_ALLOC_SLOT + 0x540). all: use_vcut CUT3. }
    mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x554).
    (* [comment removed for export] *)
    subst K2. mnorm HS.
    mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x128).
    use_piece as_actg_piece Hp Hag HI HW HS.
    intros [[xa xb]|] HX3 HS; [ destruct HX3 as [HXa HXb] | destruct HX3 ].
    mnorm HS. piece_exit_k HK K Hag HI HS. }
  intros [m3|] HX2 HS; [ | destruct HX2 ]. mnorm HS.
  mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x128).
  use_piece as_actg_piece Hp Hag HI HW HS.
  intros [[xa xb]|] HX' HS; [ destruct HX' as [HXa HXb] | destruct HX' ].
  mnorm HS. piece_exit_k HK K Hag HI HS.
Qed.

End Pieces2.


Lemma halveF_odd' : forall usage k x, c_eq (v_andi x 1) (Z_to_bv 64 0) = false -> halveF usage k x = x.
Proof. intros usage k x H. apply halveF_odd. exact H. Qed.

Lemma cnt_bound : forall size usage (t : word),
  bv_unsigned t < 256 -> bv_unsigned (shrinkF size 40 (halveF usage 8 t)) < 256.
Proof.
  intros size usage t Ht.
  pose proof (halveF_le usage 8 t ltac:(lia)).
  pose proof (shrinkF_le size 40 (halveF usage 8 t) ltac:(lia)). lia.
Qed.

Ltac xr_extra ::= first [ apply u_lbu | apply cnt_bound; assumption ].

Section Pieces3.
Context {fx : FPState} {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL}.
#[local] Existing Instance reloc_layout.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition as_cnt_xr (x : word) (R' : bvmap 5 word) : Prop :=
  getr R' 19 = x /\ bv_unsigned x < 256.

Lemma as_cnt_piece {B} : forall md (R : bvmap 5 word) mm rom (s0 s : mstate) (sc usage size : word)
    (K : word -> M B) (P : B -> mstate -> Prop) (L : B -> mstate -> TSet),
  md_pure md -> magree s mm -> minv s0 s ->
  getr R 8 = sc -> getr R 10 = usage -> getr R 24 = size -> getr R 19 = v_slli sc 1 -> getr R 12 = Z_to_bv 64 8 ->
  tsafe (MallocTree.mbind (as_cnt sc usage size) K s) P ->
  (forall x s' mm' R',
     magree s' mm' -> minv s0 s' ->
     (forall a, ms_lo s0 <= bv_unsigned a < ms_hi s0 -> mm' a = mm a) ->
     (forall r, wreg [12;13;14;19]%Z r = false -> getr R' r = getr R r) ->
     as_cnt_xr x R' ->
     tsafe (K x s') P ->
     realizes ml_segs (mkCfg (mkst R' (pc+ PC_ALLOC_SLOT 0x2a4) mm' rom) (with_vmmaps (ms_vm s') md)) (tshape (K x s') L)) ->
  realizes ml_segs (mkCfg (mkst R (pc+ PC_ALLOC_SLOT 0x218) mm rom) (with_vmmaps (ms_vm s) md))
           (tshape (MallocTree.mbind (as_cnt sc usage size) K s) L).
Proof.
  intros md R mm rom s0 s sc usage size K P L Hp Hag HI H8 H10 H24 H19 H12 HS HK.
  pose proof I as HW. pose proof I as Hret. note_win HI. sys_hyps.
  unfold as_cnt, as_cnt_xr in HS |- *. munf. mnorm HS.
  (* [comment removed for export] *)
  mstepx Hp HS Hag HI HW HK Hret as_calls.
  all: run_exit_k_not_at (bv_unsigned PC_ALLOC_SLOT + 0x24c) Hp HS Hag HI HW HK Hret K (fun _ : word => (pc+ PC_ALLOC_SLOT 0x2a4)).
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret as_calls (bv_unsigned PC_ALLOC_SLOT + 0x260).
  mach Hp HS.
  match goal with Hr : rdn ml_segs _ _ 1 = Some [?b] |- _ => pose proof (u_lbu b) as Htb end.
  mach_brc Hp HS.
  - (* [comment removed for export] *)
    lazymatch goal with
    | |- realizes _ _ (tshape (K (shrinkF ?sz 40 (halveF ?us 8 ?t)) _) _) =>
        eapply (halve_run 8 t us);
        [ mpure Hp | val_tac | val_tac | assumption
        | change (2 ^ Z.of_nat 8) with 256; exact Htb | clear -Htb; lia | ];
        let Rh := fresh "Rh" in let Hkh := fresh "Hkeeph" in let HRh := fresh "HRh" in
        intros Rh Hkh HRh; keep_facts Hkh;
        pose proof (halveF_le us 8 t ltac:(clear -Htb; lia)) as Hhb;
        eapply (shrink_run 40 (halveF us 8 t) sz);
        [ mpure Hp | val_tac | val_tac
        | change (2 ^ Z.of_nat 40) with (2^40); clear -Htb Hhb; lia
        | clear -Htb Hhb; lia
        | ]
    end.
    intros Rs Hkeeps HRs. keep_facts Hkeeps.
    piece_exit_k HK K Hag HI HS.
  - (* [comment removed for export] *)
    mach Hp HS. mach Hp HS.
    lazymatch goal with
    | |- realizes _ _ (tshape (K (shrinkF ?sz 40 (halveF ?us 8 ?t)) _) _) =>
        eapply (shrink_run 40 (halveF us 8 t) sz);
        [ mpure Hp
        | rewrite halveF_odd' by assumption; val_tac
        | val_tac
        | rewrite halveF_odd' by assumption; change (2 ^ Z.of_nat 40) with (2^40); clear -Htb; lia
        | rewrite halveF_odd' by assumption; clear -Htb; lia
        | ]
    end.
    intros Rs Hkeeps HRs. keep_facts Hkeeps.
    piece_exit_k HK K Hag HI HS.
Qed.

End Pieces3.
