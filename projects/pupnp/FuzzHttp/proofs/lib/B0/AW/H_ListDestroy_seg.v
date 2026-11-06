(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0 AllocA0 ATacAp.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import HttpAllocA HttpRepA AWKit AWAuto HObjA H_freelist H_ListAddTail H_httpheader_free AWUb.
Import ListNotations.
Open Scope Z_scope.

Definition ListDestroy_entryA : Z := 0x8bd44.

Notation DFRA m q pad s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra :=
  (rw_cells asegs m q [CB 8 pad; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
Notation FFc m L ffree fcmp := (rw_cells asegs m (L + 80) [C8 (wz ffree); C8 (wz fcmp)]).

Notation LSTA L cur x1 q gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 s10 s11 t3 t4 t5 t6 F fc pc mm :=
  (MS (mkR x1 (wz q) gp tp t0 t1 t2 (wz L) (wz (L + 48)) a0 a1 a2 a3 a4 a5 a6 a7 (wz (L + 56)) (wz cur) (wz (L + 80)) x21
           (wz 0x7fff8000) (wz (L + 24)) (wz (Z.shiftr (L + 48) 3 + 2147450880)) (wz (Z.shiftr (L + 80) 3 + 2147450880)) s10 s11 t3 t4 t5 t6)
      F (wz pc) fc None mm (seg_rom asegs)).

Notation XSTA L x1 q gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x24 x25 s10 s11 t3 t4 t5 t6 F fc pc mm :=
  (MS (mkR x1 (wz q) gp tp t0 t1 t2 (wz L) (wz (L + 48)) a0 a1 a2 a3 a4 a5 a6 a7 (wz (L + 56)) x19 x20 x21
           (wz 0x7fff8000) (wz (L + 24)) x24 x25 s10 s11 t3 t4 t5 t6)
      F (wz pc) fc None mm (seg_rom asegs)).

Section W.
Context {HC : HasCeiling}.
Hypothesis IC : icpt_contracts.

#[using="Type"] Lemma dsegA : forall (lo L first last size : Z) ra (q : Z) gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc m,
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 96 -> q < 2^64 -> mem_inv asegs m -> asan_env asegs m ->
  rw_cells asegs m L (lhead_cells first last size) -> 0x609000 <= L -> L + 96 <= alloc_ceiling -> L mod 8 = 0 -> shw m L 96 ->
  0 <= first < 2^64 ->
  evt asegs (fun ms' => exists m' pad,
      munch [(lo, q)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (q + -96) /\ DFRA m' (q + -96) pad s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra
      /\ rw_cells asegs m' L (lhead_cells first last size)
      /\ ((first = L + 24 /\ exists a0' a1' a2', ms' = XSTA L ra (q + -96) gp tp t0 t1 t2 a0' a1' a2' a3 a4 a5 a6 a7 (wz first) s4 s5 s8 s9 s10 s11 t3 t4 t5 t6 F fc 0x8bf9c m')
          \/ (first <> L + 24 /\ exists a0' a1' a2', ms' = LSTA L first ra (q + -96) gp tp t0 t1 t2 a0' a1' a2' a3 a4 a5 a6 a7 s5 s10 s11 t3 t4 t5 t6 F fc 0x8bdd8 m')))
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz L) (wz 1) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ListDestroy_entryA) fc None m (seg_rom asegs)).
Proof.
  intros lo L first last size ra q gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  intros ST CLO LO QHI MI AE0 LC LLO LHI LAL SHWL FR0. unfold ListDestroy_entryA, lhead_cells in *.
  a0_prologue AE0 [(lo, q)]%Z m.
  carve_frame 96%nat ST.
  walk_lia_to 0x8bd7c%Z. ub_align.
  walk_lia_to 0x8bdb4%Z.

  step. if_cases K1; zify_cond K1.
  - apply evt_done. exists m0. eexists. repeat (split; [eassumption|]).
    left. split; [lia|]. do 3 eexists. reflexivity.
  - walk_lia_to 0x8bdd8%Z.
    apply evt_done. exists m0. eexists. repeat (split; [eassumption|]).
    right. split; [lia|]. do 3 eexists. reflexivity.
Qed.

Definition unlink_postA (L N next it last size : Z) (nextnode : option (Z * Z)) (q : Z) (gp tp : word)
    (t0 t1 t2 a6 a7 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists m' a2' a3' a4' a5',
    ms' = MS (mkR (wz 0x8be88) (wz q) gp tp t0 t1 t2 (wz L) (wz (L + 48)) (wz (L + 56)) (wz N) a2' a3' a4' a5' a6 a7 (wz (L + 56)) (wz next) (wz (L + 80)) (wz it)
                  (wz 0x7fff8000) (wz (L + 24)) (wz (Z.shiftr (L + 48) 3 + 2147450880)) (wz (Z.shiftr (L + 80) 3 + 2147450880)) s10 s11 t3 t4 t5 t6)
             F (wz FreeListFree_entryA) fc None m' (seg_rom asegs)
    /\ munch ((L, L + 56) :: match nextnode with None => [] | Some _ => [(next, next + 24)] end)%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' L (lhead_cells next (match nextnode with None => L | Some _ => last end) size)
    /\ rw_cells asegs m' N (node_cells L next it)
    /\ match nextnode with None => True | Some (nx2, it2) => rw_cells asegs m' next (node_cells L nx2 it2) end.

#[using="Type"] Lemma dsegB : forall (L N next it last size : Z) (nextnode : option (Z * Z)) (q : Z) gp tp
    t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 s10 s11 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
  mem_inv asegs m ->
  rw_cells asegs m L (lhead_cells N last size) -> 0x609000 <= L -> L + 96 <= alloc_ceiling -> L mod 8 = 0 -> shw m L 96 ->
  0 <= size < 2^63 -> 0 <= last < 2^64 ->
  rw_cells asegs m N (node_cells L next it) -> 0x609000 <= N -> N + 24 <= alloc_ceiling -> N mod 8 = 0 -> shw m N 24 -> 0 <= it < 2^64 ->
  (L + 96 <= N \/ N + 24 <= L) ->
  match nextnode with
  | None => next = L + 24
  | Some (nx2, it2) => rw_cells asegs m next (node_cells N nx2 it2) /\ 0x609000 <= next /\ next + 24 <= alloc_ceiling /\ next mod 8 = 0
                      /\ shw m next 24 /\ (N + 24 <= next \/ next + 24 <= N) /\ (L + 96 <= next \/ next + 24 <= L)
                      /\ 0 <= nx2 < 2^64 /\ 0 <= it2 < 2^64
  end ->
  evt asegs (unlink_postA L N next it last size nextnode q gp tp t0 t1 t2 a6 a7 s10 s11 t3 t4 t5 t6 F fc m)
    (LSTA L N x1 q gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 s10 s11 t3 t4 t5 t6 F fc 0x8bdd8 m).
Proof.
  intros L N next it last size nextnode q gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 s10 s11 t3 t4 t5 t6 x1 F fc m.
  intros MI LC LLO LHI LAL SHWL SZ LASTR NC NLO NHI NAL SHWN ITR DJLN NXH. unfold lhead_cells, node_cells, FreeListFree_entryA in *.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  destruct nextnode as [[nx2 it2]|].
  - destruct NXH as (NXC & XLO & XHI & XAL & SHWX & DJNX & DJLX & NX2R & IT2R).
    pose proof (munch_refl [(L, L + 56); (next, next + 24)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ub_null. zstep. ub_align.
    walk_lia_to 0x8be2c%Z.
    ub_null. ub_align.
    walk_lia_to 0x8be60%Z.
    ub_null. ub_align.
    walk_lia_to 0x8be84%Z.
    step.
    apply evt_done. unfold unlink_postA, lhead_cells, node_cells. do 5 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  - subst next.
    pose proof (munch_refl [(L, L + 56)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    ub_null. zstep. ub_align.
    walk_lia_to 0x8be2c%Z.
    ub_null. ub_align.
    walk_lia_to 0x8be60%Z.
    ub_null. ub_align.
    walk_lia_to 0x8be84%Z. step.
    apply evt_done. unfold unlink_postA, lhead_cells, node_cells. do 5 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact I.
Qed.

#[using="Type"] Lemma dsegC : forall (L cur first last size fcmp it : Z) (q : Z) gp tp
    t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
  mem_inv asegs m ->
  rw_cells asegs m L (lhead_cells first last size) -> FFc m L httpheader_free_entryA fcmp ->
  0x609000 <= L -> L + 96 <= alloc_ceiling -> L mod 8 = 0 -> shw m L 96 -> 1 <= size < 2^63 -> 0 <= it < 2^64 ->
  evt asegs (fun ms' => exists m' a2',
      ms' = LSTA L cur (wz httpheader_free_raA) q gp tp t0 t1 t2 (wz it) (wz httpheader_free_entryA) a2' a3 a4 a5 a6 a7 (wz it) s10 s11 t3 t4 t5 t6 F fc httpheader_free_entryA m'
      /\ munch [(L + 48, L + 56)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' L (lhead_cells first last (size - 1)) /\ FFc m' L httpheader_free_entryA fcmp)
    (LSTA L cur x1 q gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz it) s10 s11 t3 t4 t5 t6 F fc 0x8be88 m).
Proof.
  intros L cur first last size fcmp it q gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 x1 F fc m.
  intros MI LC FF LLO LHI LAL SHWL SZ ITR. unfold lhead_cells, httpheader_free_entryA, httpheader_free_raA in *.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (munch_refl [(L + 48, L + 56)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  walk_lia_to 0x8be98%Z.
  step. ubr_by ltac:(rewrite ?signed_lit in KU by lia; lia).
  walk_lia_to 0x8bebc%Z.
  step.
  apply evt_done. do 2 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
Qed.

#[using="Type"] Lemma dsegD : forall (L cur : Z) (q : Z) gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 s10 s11 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
  0 <= cur < 2^64 -> 0 <= L -> L + 96 < 2^64 ->
  evt asegs (fun ms' => ms' = LSTA L cur x1 q gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 s10 s11 t3 t4 t5 t6 F fc
                                    (if cur =? L + 24 then 0x8bf9c else 0x8bdd8) m)
    (LSTA L cur x1 q gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 s10 s11 t3 t4 t5 t6 F fc 0x8bec0 m).
Proof.
  intros L cur q gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 s10 s11 t3 t4 t5 t6 x1 F fc m CR L0 LHI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  step. step. if_cases K1; zify_cond K1.
  - replace (cur =? L + 24) with true by (symmetry; apply Z.eqb_eq; lia). apply evt_done. reflexivity.
  - replace (cur =? L + 24) with false by (symmetry; apply Z.eqb_neq; lia). apply evt_done. reflexivity.
Qed.

#[using="Type"] Lemma dsegE : forall (L first last size : Z) (q : Z) gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x24 x25 s10 s11 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
  mem_inv asegs m -> rw_cells asegs m L (lhead_cells first last size) ->
  0x609000 <= L -> L + 96 <= alloc_ceiling -> L mod 8 = 0 -> shw m L 96 ->
  evt asegs (fun ms' => exists m' a0',
      ms' = XSTA L (wz 0x8bfb8) q gp tp t0 t1 t2 a0' a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x24 x25 s10 s11 t3 t4 t5 t6 F fc FreeListDestroy_entryA m'
      /\ a0' = wz (L + 56)
      /\ munch [(L + 48, L + 56)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' L (lhead_cells first last 0))
    (XSTA L x1 q gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x24 x25 s10 s11 t3 t4 t5 t6 F fc 0x8bf9c m).
Proof.
  intros L first last size q gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x24 x25 s10 s11 t3 t4 t5 t6 x1 F fc m.
  intros MI LC LLO LHI LAL SHWL. unfold lhead_cells, FreeListDestroy_entryA in *.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (munch_refl [(L + 48, L + 56)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  walk_lia_to 0x8bfb4%Z. step.
  apply evt_done. do 2 eexists. split; [reflexivity|]. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
Qed.

#[using="Type"] Lemma dsegF : forall (lo : Z) (pad : list byte) ra (q : Z) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 (F : bvmap 5 word) fc m,
  stk asegs m lo (q + -96) -> alloc_ceiling <= lo -> lo <= q - 96 -> q < 2^64 -> mem_inv asegs m ->
  DFRA m (q + -96) pad s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra ->
  evt asegs (fun ms' => ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom asegs) /\ stk asegs m lo q)
    (MS (mkR x1 (wz (q + -96)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 t3 t4 t5 t6)
        F (wz 0x8bfb8) fc None m (seg_rom asegs)).
Proof.
  intros lo pad ra q gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 F fc m.
  intros ST CLO LO QHI MI FR.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  walk_lia_to 0x8bfe8%Z. release_to q. step. step.
  apply evt_done. split; [reflexivity| assumption].
Qed.

End W.
