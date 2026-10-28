(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode Tac InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase F_apoison.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Export ACanary.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition zeros (n : Z) : list byte := repeat (Z_to_bv 8 0) (Z.to_nat n).

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition PZR_STACK : Z := 592.

(* [comment removed for export] *)
Definition premap_cells (m : amem) : Prop :=
     rw_cells bsegs m 0xc72e8 [C8 (Z_to_bv 64 0x15f7a0)]                 (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x15f7a0 [C8 (Z_to_bv 64 4096)]                     (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x1618b8 [C8 (Z_to_bv 64 0)]                        (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x161900 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1);
                               C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]   (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x161918 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
                               C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]   (* [comment removed for export] *)
  /\ (exists cb : list byte, rw_cells bsegs m 0x622cf0 [CB 8 cb])        (* [comment removed for export] *)
  /\ rw_cells bsegs m 0x622f70 [C8 (Z_to_bv 64 4096)].                    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition arelro0 (m : amem) : Prop := forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None.

Lemma arelro0_munch : forall W m m', arelro0 m -> munch W m m' ->
  Forall (fun iv => ARELRO_HI <= fst iv \/ snd iv <= ARELRO_LO) W -> arelro0 m'.
Proof.
  intros W m m' RR MU HW i Hi. rewrite <- (RR i Hi). pose proof (MU (wa i)) as E.
  rewrite wa_unsigned in E by (unfold ARELRO_LO, ARELRO_HI in Hi; lia). apply E.
  clear -HW Hi. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *.
  split; [lia| apply IH; assumption].
Qed.

Lemma premap_cells_frame : forall m m' W, premap_cells m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv) W -> premap_cells m'.
Proof.
  intros m m' W (R1 & R2 & R3 & R4 & R5 & R6 & R7) MU WM HW. unfold AIMG_HI in HW.
  assert (D : forall A k, 0 <= k -> A + k <= 0x625000 -> disjoint_from W A k).
  { clear -HW. intros A k Hk HA. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
  unfold premap_cells. repeat lazymatch goal with |- _ /\ _ => split end;
    first [ apply premap_canary_any
          | (eapply rw_cells_transport; [eassumption | exact MU | exact WM | cbn; apply D; lia]) ].
Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma bytes_eq_of_unsigned : forall (bs bs' : list byte), map bv_unsigned bs = map bv_unsigned bs' -> bs = bs'.
Proof.
  induction bs as [|b bs IH]; intros [|b' bs'] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1| apply IH; exact H2].
Qed.
Lemma premap_word_212a00 : forall m,
  rw_cells bsegs m 0x161900 [C8 (Z_to_bv 64 0x10101000100)] ->
  rw_cells bsegs m 0x161900 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1);
                            C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof. intros m H. eapply rw_cells_recast; [exact H| cbn; tauto| apply bytes_eq_of_unsigned; vm_compute; reflexivity| reflexivity]. Qed.
Lemma premap_word_212a18 : forall m,
  rw_cells bsegs m 0x161918 [C8 (Z_to_bv 64 0x101000100000000)] ->
  rw_cells bsegs m 0x161918 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
                            C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)].
Proof. intros m H. eapply rw_cells_recast; [exact H| cbn; tauto| apply bytes_eq_of_unsigned; vm_compute; reflexivity| reflexivity]. Qed.

(* [comment removed for export] *)
Definition premap_post (RNG : footprint) (sp : word) (addr size lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG'                                         (* [comment removed for export] *)
  /\ munch [(bv_unsigned sp - PZR_STACK, bv_unsigned sp); (shad addr, shad addr + shlen size)] m m' /\ wmono bsegs m m'
  /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
  /\ rw_cells bsegs m' (shad addr) [CB (Z.to_nat (shlen size)) (zeros (shlen size))]     (* [comment removed for export] *)
  /\ rng RNG' (shad addr) (shlen size)
  /\ poison_cells m' /\ premap_cells m'.

Definition poison_remap_stmt : Prop :=
  forall (R : Type) (k : AM R) (Q : R -> footprint -> machine_state -> Prop) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (addr size lo : Z) (junk : list byte),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PZR_STACK ->
  mem_inv bsegs m ->
  poison_cells m -> premap_cells m -> (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 0 ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> ablk addr (addr + size) -> addr + size <= 2^47 ->     (* [comment removed for export] *)
  0x10000 <= shlen size ->                                     (* [comment removed for export] *)
  rw_cells bsegs m (shad addr) [CB (Z.to_nat (shlen size)) junk] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) (shlen size) ->
  (* [comment removed for export] *)
  (forall RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      premap_post RNG sp addr size lo m RNG' m' ->
      implS bsegs RNG' (aembed ATOP k) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (aembed ATOP (poison0 addr size k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x55d68) fc None m (seg_rom bsegs)).
End CANSEC1.
