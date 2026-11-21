(* SPDX-License-Identifier: MIT *)
(* The launch ledger of LPS 727298f3 (res_launch, res_launch_split). vdso_reserved_small is copied from
   projects/coturn/FuzzStunClient/proofs/lib/Common/RefNodes.v of this tree, lines 820-829,
   its last step closed through Z_to_bv_small. *)
(* LPS 727298f3: the reserved ledger a launch installs is [State.init_reserved], the image's
   reservations followed by the vdso/vvar pair ([State.vdso_reserved]) below
   [page_round_down_Z (min mbase (sp - stack_max_size))].  The stage invariants of this unit's
   walks state their ledger through [res_launch], which keeps the image part literal and leaves
   the pair's kernel build free.
   [vdso_reserved_small] is coturn's [Common/RefNodes.vdso_reserved_small], from the lines
   that the comment above names. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
Import ListNotations.

Definition res_launch (segres : list (word * word)) (VM : VmMaps) : Prop :=
  exists kb : KernelBuild, vm_reserved VM = init_reserved segres (vm_mmap_base VM) (vm_init_sp VM) kb.

(** The vdso/vvar pair is at most two ledger entries, each at most 16 pages
    ([vdso_text_pages_le]), for every kernel build. *)
Lemma vdso_reserved_small : forall kb top,
  Forall (fun p : word * word => bv_unsigned (snd p) <= 2 ^ 30)%Z (vdso_reserved kb top)
  /\ (length (vdso_reserved kb top) <= 2)%nat.
Proof.
  intros kb top. pose proof (vdso_text_pages_pos kb). pose proof (vdso_text_pages_le kb).
  unfold vdso_reserved. cbv zeta.
  destruct (top - vdso_len kb <? page_size)%Z; [split; [constructor | cbn; lia]|].
  split; [|cbn; lia].
  repeat constructor; cbn [snd]; unfold vdso_vvar_pages, page_size;
    rewrite Z_to_bv_small by (unfold bv_modulus; lia); lia.
Qed.

(** What a walk over a [res_launch] ledger uses: the image part, then at most two entries
    of at most [2 ^ 30] bytes. *)
Lemma res_launch_split : forall segres VM, res_launch segres VM ->
  exists vx, vm_reserved VM = segres ++ vx
    /\ Forall (fun p : word * word => bv_unsigned (snd p) <= 2 ^ 30)%Z vx /\ (length vx <= 2)%nat.
Proof.
  intros segres VM [kb H]. unfold init_reserved in H.
  eexists. split; [exact H|]. apply vdso_reserved_small.
Qed.
