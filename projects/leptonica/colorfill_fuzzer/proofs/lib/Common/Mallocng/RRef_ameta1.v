(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import decidable.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes
  PureModel VmLedger AllocIface AsanCeil AgentLib.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocShape RefLrSc RefStep RefStmts RefSys RefPieces RefStep3.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require Import RefStepR.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac am_calls Hp HS Hag HI HW t := sys_calls Hp HS Hag HI HW t ltac:(fun t => mach_jal Hp HS).
Ltac am_run Hp HS Hag HI HW HK Hret K PCF := piece_run Hp HS Hag HI HW HK Hret am_calls K PCF.
(* [comment removed for export] *)
Ltac sys_hyps := idtac.

Section Pieces.
Context {fx : FPState} {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL}.
#[local] Existing Instance reloc_layout.
Hypothesis MM : forall k, mmap_stmt k.
Hypothesis MF : mmap_fixed_stmt.
Hypothesis MP : mprotect_stmt.
Hypothesis MU : munmap_stmt.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma am_tail_piece {B} : forall md (R : bvmap 5 word) mm rom (s0 s : mstate) (p : word)
    (K : word -> M B) (P : B -> mstate -> Prop) (L : B -> mstate -> TSet),
  md_pure md -> magree s mm -> minv s0 s ->
  getr R 19 = A_LOCK -> getr R 9 = p ->
  tsafe (MallocTree.mbind (am_tail p) K s) P ->
  (forall m s' mm' R',
     magree s' mm' -> minv s0 s' ->
     (forall a, ms_lo s0 <= bv_unsigned a < ms_hi s0 -> mm' a = mm a) ->
     (forall r, wreg [10;11;12]%Z r = false -> getr R' r = getr R r) ->
     getr R' 10 = m ->
     tsafe (K m s') P ->
     realizes ml_segs (mkCfg (mkst R' (pc+ PC_ALLOC_META 0x27c) mm' rom) (with_vmmaps (ms_vm s') md)) (tshape (K m s') L)) ->
  realizes ml_segs (mkCfg (mkst R (pc+ PC_ALLOC_META 0x218) mm rom) (with_vmmaps (ms_vm s) md))
           (tshape (MallocTree.mbind (am_tail p) K s) L).
Proof.
  intros md R mm rom s0 s p K P L Hp Hag HI H19 H9 HS HK.
  pose proof I as HW. pose proof I as Hret. note_win HI. sys_hyps.
  unfold am_tail in HS |- *. munf. mnorm HS.
  mrunx_until Hp HS Hag HI HW HK Hret no_calls (bv_unsigned PC_ALLOC_META + 0x234).
  mach_join Hp HS Hag HI HW (bv_unsigned PC_ALLOC_META + 0x244) (@nil Z) (@nil Z).
  mrunx_until Hp HS Hag HI HW HK Hret no_calls (bv_unsigned PC_ALLOC_META + 0x27c).
  lazymatch goal with
  | |- realizes _ _ (tshape (K ?x ?sb) _) =>
      eapply (HK x sb); [ exact Hag | exact HI | win_same | keep_tac
                        | regnorm; imm_norm; rewrite ?v_addi_0; klitsg; first [reflexivity | bveq] | exact HS ]
  end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition am_newarea_pc (x : option (word * bool)) : word :=
  match x with None => (pc+ PC_ALLOC_META 0x2cc) | Some _ => (pc+ PC_ALLOC_META 0x20c) end.
Definition am_newarea_xr (x : option (word * bool)) (R' : bvmap 5 word) : Prop :=
  match x with
  | None => True
  | Some (p, b) => b = true /\ getr R' 9 = p /\ getr R' 8 = Z_to_bv 64 4096
  end.

Lemma am_newarea_piece {B} : forall md (R : bvmap 5 word) mm rom (s0 s : mstate) (sp : word)
    (K : option (word * bool) -> M B) (P : B -> mstate -> Prop) (L : B -> mstate -> TSet),
  md_pure md -> magree s mm -> minv s0 s ->
  getr R 19 = A_LOCK -> getr R 8 = Z_to_bv 64 4096 -> getr R 2 = v_addi sp (-64) ->
  getr R 4 = A_TP ->
  bv_unsigned sp mod 16 = 0 ->
  ms_lo s0 <= bv_unsigned sp - 144 -> bv_unsigned sp <= ms_hi s0 ->
  (forall a, bv_unsigned sp - 144 <= bv_unsigned a < bv_unsigned sp -> mm a <> None) ->
  tsafe (MallocTree.mbind (am_newarea (Z_to_bv 64 4096)) K s) P ->
  (forall x s' mm' R',
     magree s' mm' -> minv s0 s' ->
     (forall a, ms_lo s0 <= bv_unsigned a < ms_hi s0 ->
                ~ (bv_unsigned sp - 144 <= bv_unsigned a < bv_unsigned sp - 64) -> mm' a = mm a) ->
     (forall a, bv_unsigned sp - 144 <= bv_unsigned a < bv_unsigned sp - 64 -> mm' a <> None) ->
     (forall r, wreg [1;5;6;9;10;11;12;13;14;15;16;17;20]%Z r = false -> getr R' r = getr R r) ->
     am_newarea_xr x R' ->
     tsafe (K x s') P ->
     realizes ml_segs (mkCfg (mkst R' (am_newarea_pc x) mm' rom) (with_vmmaps (ms_vm s') md)) (tshape (K x s') L)) ->
  realizes ml_segs (mkCfg (mkst R (pc+ PC_ALLOC_META 0x1b8) mm rom) (with_vmmaps (ms_vm s) md))
           (tshape (MallocTree.mbind (am_newarea (Z_to_bv 64 4096)) K s) L).
Proof.
  intros md R mm rom s0 s sp K P L Hp Hag HI H19 H8 H2 H4 Hal Hlo Hhi Hstk HS HK.
  pose proof I as Hret. note_win HI. sys_hyps.
  pose proof HI as HI0. destruct HI0 as (_ & _ & _ & Hlo0 & _ & Hhi64 & _).
  pose proof (mwin_init s0 mm sp 144 Hstk) as HW.
  unfold am_newarea, am_newarea_xr in HS |- *. munf. mnorm HS.
  am_run Hp HS Hag HI HW HK Hret K am_newarea_pc.
  all: piece_exit HK K Hag HI HS.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition am_brk_pc (x : option (word * bool)) : word :=
  match x with
  | None => (pc+ PC_ALLOC_META 0x1ac)
  | Some (_, true) => (pc+ PC_ALLOC_META 0x18c)
  | Some (_, false) => (pc+ PC_ALLOC_META 0x1a0)
  end.
Definition am_brk_xr (a0 : word) (x : option (word * bool)) (R' : bvmap 5 word) : Prop :=
  match x with
  | None => getr R' 10 = a0
  | Some (new, true) => getr R' 9 = new
  | Some (_, false) => True
  end.

Lemma am_brk_piece {B} : forall md (R : bvmap 5 word) mm rom (s0 s : mstate) (sp cb a0 : word)
    (K : option (word * bool) -> M B) (P : B -> mstate -> Prop) (L : B -> mstate -> TSet),
  md_pure md -> magree s mm -> minv s0 s ->
  getr R 19 = A_LOCK -> getr R 8 = Z_to_bv 64 4096 -> getr R 2 = v_addi sp (-64) ->
  getr R 4 = A_TP -> getr R 9 = cb -> getr R 10 = a0 ->
  bv_unsigned sp mod 16 = 0 ->
  ms_lo s0 <= bv_unsigned sp - 144 -> bv_unsigned sp <= ms_hi s0 ->
  (forall a, bv_unsigned sp - 144 <= bv_unsigned a < bv_unsigned sp -> mm a <> None) ->
  tsafe (MallocTree.mbind (am_brk (Z_to_bv 64 4096) cb) K s) P ->
  (forall x s' mm' R',
     magree s' mm' -> minv s0 s' ->
     (forall a, ms_lo s0 <= bv_unsigned a < ms_hi s0 ->
                ~ (bv_unsigned sp - 144 <= bv_unsigned a < bv_unsigned sp - 64) -> mm' a = mm a) ->
     (forall a, bv_unsigned sp - 144 <= bv_unsigned a < bv_unsigned sp - 64 -> mm' a <> None) ->
     (forall r, wreg [1;5;6;9;10;11;12;13;14;15;16;17]%Z r = false -> getr R' r = getr R r) ->
     am_brk_xr a0 x R' ->
     tsafe (K x s') P ->
     realizes ml_segs (mkCfg (mkst R' (am_brk_pc x) mm' rom) (with_vmmaps (ms_vm s') md)) (tshape (K x s') L)) ->
  realizes ml_segs (mkCfg (mkst R (pc+ PC_ALLOC_META 0x114) mm rom) (with_vmmaps (ms_vm s) md))
           (tshape (MallocTree.mbind (am_brk (Z_to_bv 64 4096) cb) K s) L).
Proof.
  intros md R mm rom s0 s sp cb a0 K P L Hp Hag HI H19 H8 H2 H4 H9 H10 Hal Hlo Hhi Hstk HS HK.
  pose proof I as Hret. note_win HI. sys_hyps.
  pose proof HI as HI0. destruct HI0 as (_ & _ & _ & Hlo0 & _ & Hhi64 & _).
  pose proof (mwin_init s0 mm sp 144 Hstk) as HW.
  unfold am_brk, am_brk_xr in HS |- *. munf. mnorm HS.
  am_run Hp HS Hag HI HW HK Hret K am_brk_pc.
  (* [comment removed for export] *)
  all: try (lazymatch goal with
            | |- realizes _ _ (tshape (?Kv (Some (_, c_eq ?r ?nw)) _) _) =>
                is_var Kv;
                let Hc := fresh "Hc" in
                destruct (c_eq r nw) eqn:Hc;
                [ mach_br_dir Hp HS true ltac:(by_bool Hc) | mach_br_dir Hp HS false ltac:(by_bool Hc) ];
                am_run Hp HS Hag HI HW HK Hret K am_brk_pc
            end).
  all: piece_exit HK K Hag HI HS.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma am_some_piece {B} : forall md (R : bvmap 5 word) mm rom (s0 s : mstate) (sp p : word)
    (K : word -> M B) (P : B -> mstate -> Prop) (L : B -> mstate -> TSet),
  md_pure md -> magree s mm -> minv s0 s ->
  getr R 19 = A_LOCK -> getr R 8 = Z_to_bv 64 4096 -> getr R 2 = v_addi sp (-64) ->
  getr R 4 = A_TP -> getr R 9 = p ->
  bv_unsigned sp mod 16 = 0 ->
  ms_lo s0 <= bv_unsigned sp - 144 -> bv_unsigned sp <= ms_hi s0 ->
  (forall a, bv_unsigned sp - 144 <= bv_unsigned a < bv_unsigned sp -> mm a <> None) ->
  tsafe (MallocTree.mbind (am_some (Z_to_bv 64 4096) p true) K s) P ->
  (forall x s' mm' R',
     magree s' mm' -> minv s0 s' ->
     (forall a, ms_lo s0 <= bv_unsigned a < ms_hi s0 ->
                ~ (bv_unsigned sp - 144 <= bv_unsigned a < bv_unsigned sp - 64) -> mm' a = mm a) ->
     (forall a, bv_unsigned sp - 144 <= bv_unsigned a < bv_unsigned sp - 64 -> mm' a <> None) ->
     (forall r, wreg [1;5;6;10;11;12;13;14;15;16;17]%Z r = false -> getr R' r = getr R r) ->
     getr R' 10 = x ->
     tsafe (K x s') P ->
     realizes ml_segs (mkCfg (mkst R' (pc+ PC_ALLOC_META 0x27c) mm' rom) (with_vmmaps (ms_vm s') md)) (tshape (K x s') L)) ->
  realizes ml_segs (mkCfg (mkst R (pc+ PC_ALLOC_META 0x20c) mm rom) (with_vmmaps (ms_vm s) md))
           (tshape (MallocTree.mbind (am_some (Z_to_bv 64 4096) p true) K s) L).
Proof.
  intros md R mm rom s0 s sp p K P L Hp Hag HI H19 H8 H2 H4 H9 Hal Hlo Hhi Hstk HS HK.
  pose proof I as Hret. note_win HI. sys_hyps.
  pose proof HI as HI0. destruct HI0 as (_ & _ & _ & Hlo0 & _ & Hhi64 & _).
  pose proof (mwin_init s0 mm sp 144 Hstk) as HW.
  unfold am_some, am_okc in HS |- *. munf. mnorm HS.
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret am_calls (bv_unsigned PC_ALLOC_META + 0x214).
  mstepx Hp HS Hag HI HW HK Hret am_calls.
  - (* [comment removed for export] *)
    mrunx_until Hp HS Hag HI HW HK Hret am_calls (bv_unsigned PC_ALLOC_META + 0x2b8).
    all: mrunx_until Hp HS Hag HI HW HK Hret am_calls (bv_unsigned PC_ALLOC_META + 0x218).
    all: try (lazymatch goal with
              | |- realizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
                  let u := rl_name_of_pc pc in
                  let t := rl_name_of (bv_unsigned PC_ALLOC_META + 0x218)%Z in constr_eq u t; use_piece am_tail_piece Hp Hag HI HW HS;
                  let m := fresh "m" in let HX := fresh "HX" in
                  intros m HX HS; mnorm HS; piece_exit HK K Hag HI HS
              end).
    all: mrunx_until Hp HS Hag HI HW HK Hret am_calls (bv_unsigned PC_ALLOC_META + 0x27c).
    all: piece_exit HK K Hag HI HS.
  - (* [comment removed for export] *)
    use_piece am_tail_piece Hp Hag HI HW HS.
    intros m HX HS; mnorm HS. piece_exit HK K Hag HI HS.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac am_fin_some Hp HS Hag HI HW HK Hret K :=
  let x := fresh "x" in let HX := fresh "HX" in
  intros x HX HS; mnorm HS; piece_exit HK K Hag HI HS.

(* [comment removed for export] *)
Ltac am_fin_newarea Hp HS Hag HI HW HK Hret K :=
  let p := fresh "p" in let b := fresh "b" in let HX := fresh "HX" in
  let HX1 := fresh "HX" in let HX2 := fresh "HX" in
  intros [[p b]|] HX HS;
  [ cbn [am_newarea_pc am_newarea_xr] in HX |- *; destruct HX as (-> & HX1 & HX2); mnorm HS;
    use_piece am_some_piece Hp Hag HI HW HS; am_fin_some Hp HS Hag HI HW HK Hret K
  | cbn [am_newarea_pc am_newarea_xr] in HX |- *; mnorm HS;
    mrun_to_k Hp HS Hag HI HW HK Hret am_calls K (fun _ : word => (pc+ PC_ALLOC_META 0x27c));
    piece_exit HK K Hag HI HS ].

Lemma am_res_piece {B} : forall md (R : bvmap 5 word) mm rom (s0 s : mstate) (sp : word)
    (K : word -> M B) (P : B -> mstate -> Prop) (L : B -> mstate -> TSet),
  md_pure md -> magree s mm -> minv s0 s ->
  getr R 19 = A_LOCK -> getr R 8 = Z_to_bv 64 4096 -> getr R 2 = v_addi sp (-64) ->
  getr R 4 = A_TP ->
  bv_unsigned sp mod 16 = 0 ->
  ms_lo s0 <= bv_unsigned sp - 144 -> bv_unsigned sp <= ms_hi s0 ->
  (forall a, bv_unsigned sp - 144 <= bv_unsigned a < bv_unsigned sp -> mm a <> None) ->
  tsafe (MallocTree.mbind (am_res (Z_to_bv 64 4096)) K s) P ->
  (forall x s' mm' R',
     magree s' mm' -> minv s0 s' ->
     (forall a, ms_lo s0 <= bv_unsigned a < ms_hi s0 ->
                ~ (bv_unsigned sp - 144 <= bv_unsigned a < bv_unsigned sp - 64) -> mm' a = mm a) ->
     (forall a, bv_unsigned sp - 144 <= bv_unsigned a < bv_unsigned sp - 64 -> mm' a <> None) ->
     (forall r, wreg [1;5;6;8;9;10;11;12;13;14;15;16;17;20]%Z r = false -> getr R' r = getr R r) ->
     getr R' 10 = x ->
     tsafe (K x s') P ->
     realizes ml_segs (mkCfg (mkst R' (pc+ PC_ALLOC_META 0x27c) mm' rom) (with_vmmaps (ms_vm s') md)) (tshape (K x s') L)) ->
  realizes ml_segs (mkCfg (mkst R (pc+ PC_ALLOC_META 0xb4) mm rom) (with_vmmaps (ms_vm s) md))
           (tshape (MallocTree.mbind (am_res (Z_to_bv 64 4096)) K s) L).
Proof.
  intros md R mm rom s0 s sp K P L Hp Hag HI H19 H8 H2 H4 Hal Hlo Hhi Hstk HS HK.
  pose proof I as Hret. note_win HI. sys_hyps.
  pose proof HI as HI0. destruct HI0 as (_ & _ & _ & Hlo0 & _ & Hhi64 & _).
  pose proof (mwin_init s0 mm sp 144 Hstk) as HW.
  unfold am_res in HS |- *. munf. mnorm HS.
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret am_calls (bv_unsigned PC_ALLOC_META + 0xb8).
  mstepx Hp HS Hag HI HW HK Hret am_calls.
  2: { (* [comment removed for export] *)
    mrunx_until Hp HS Hag HI HW HK Hret am_calls (bv_unsigned PC_ALLOC_META + 0xc0).
    mach_join Hp HS Hag HI HW (bv_unsigned PC_ALLOC_META + 0x274) [11;12]%Z (@nil Z).
    mrun_to_k Hp HS Hag HI HW HK Hret am_calls K (fun _ : word => (pc+ PC_ALLOC_META 0x27c)).
    piece_exit HK K Hag HI HS. }
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret am_calls (bv_unsigned PC_ALLOC_META + 0xf0).
  mstepx Hp HS Hag HI HW HK Hret am_calls.
  2: { (* [comment removed for export] *)
    mrun_to_k Hp HS Hag HI HW HK Hret am_calls K (fun _ : word => (pc+ PC_ALLOC_META 0x27c)).
    piece_exit HK K Hag HI HS. }
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret am_calls (bv_unsigned PC_ALLOC_META + 0x10c).
  unfold am_prov in HS |- *. mnorm HS.
  mstepx Hp HS Hag HI HW HK Hret am_calls.
  2: { (* [comment removed for export] *)
    mrunx_until Hp HS Hag HI HW HK Hret am_calls (bv_unsigned PC_ALLOC_META + 0x20c).
    use_piece am_some_piece Hp Hag HI HW HS. am_fin_some Hp HS Hag HI HW HK Hret K. }
  (* [comment removed for export] *)
  mrunx_until Hp HS Hag HI HW HK Hret am_calls (bv_unsigned PC_ALLOC_META + 0x114).
  use_piece am_brk_piece Hp Hag HI HW HS.
  intros [[new [|]]|] HX HS; cbn [am_brk_pc am_brk_xr] in HX |- *; mnorm HS.
  - (* [comment removed for export] *)
    mrunx_until Hp HS Hag HI HW HK Hret am_calls (bv_unsigned PC_ALLOC_META + 0x218).
    unfold am_some, am_okc in HS |- *; mnorm HS.
    use_piece am_tail_piece Hp Hag HI HW HS. am_fin_some Hp HS Hag HI HW HK Hret K.
  - (* [comment removed for export] *)
    mrunx_until Hp HS Hag HI HW HK Hret am_calls (bv_unsigned PC_ALLOC_META + 0x1ac).
    unfold am_areas in HS |- *; mnorm HS.
    mstepx Hp HS Hag HI HW HK Hret am_calls.
    + (* [comment removed for export] *)
      use_piece am_newarea_piece Hp Hag HI HW HS. am_fin_newarea Hp HS Hag HI HW HK Hret K.
    + mrunx_until Hp HS Hag HI HW HK Hret am_calls (bv_unsigned PC_ALLOC_META + 0x20c).
      use_piece am_some_piece Hp Hag HI HW HS. am_fin_some Hp HS Hag HI HW HK Hret K.
  - (* [comment removed for export] *)
    unfold am_areas in HS |- *; mnorm HS.
    mstepx Hp HS Hag HI HW HK Hret am_calls.
    use_piece am_newarea_piece Hp Hag HI HW HS. am_fin_newarea Hp HS Hag HI HW HK Hret K.
Qed.
End Pieces.
