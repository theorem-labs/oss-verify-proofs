(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prog.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_dview Z_drep.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState DeflateSafe ZApiInst ZTaint BoundPat.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition zd_blocks (b : bptr * bptr * bptr * bptr * bptr) (L : dlay) : list block :=
  let '(sp, wp, pp, hp, bp) := b in
  [(bp, dl_Ab L, 65536); (hp, dl_Ah L, 65536); (pp, dl_Ap L, 65536); (wp, dl_Aw L, 65536); (sp, dl_As L, 5968)].

Section WithCeiling0. Context {CE__ : Ceiling}.

(* [comment removed for export] *)
Definition dlay_ceil (L : dlay) : Prop :=
  dl_As L + 5968 <= alloc_ceiling /\ dl_Aw L + 65536 <= alloc_ceiling /\ dl_Ap L + 65536 <= alloc_ceiling
  /\ dl_Ah L + 65536 <= alloc_ceiling /\ dl_Ab L + 65536 <= alloc_ceiling.

Definition zr_d (m : mem) (S : Z) (LBz : list block) (x : dstream) : Prop :=
  exists (L : dlay) (sa : deflate_state) (b : bptr * bptr * bptr * bptr * bptr),
    LBz = zd_blocks b L /\ dl_S L = S /\ DREPq m L sa (dz_z x) /\ DREL sa x /\ PAT sa /\ dlay_ceil L /\ zstrm_okP (dz_z x).

(* [comment removed for export] *)

Lemma in_zd_blocks : forall b L a,
  (dl_As L <= a < dl_As L + 5968 \/ dl_Aw L <= a < dl_Aw L + 65536 \/ dl_Ap L <= a < dl_Ap L + 65536
   \/ dl_Ah L <= a < dl_Ah L + 65536 \/ dl_Ab L <= a < dl_Ab L + 65536) -> in_block (zd_blocks b L) a.
Proof.
  intros [[[[sp wp] pp] hp] bp] L a H. unfold in_block, zd_blocks.
  destruct H as [H|[H|[H|[H|H]]]].
  - exists (sp, dl_As L, 5968). split; [cbn; tauto| exact H].
  - exists (wp, dl_Aw L, 65536). split; [cbn; tauto| exact H].
  - exists (pp, dl_Ap L, 65536). split; [cbn; tauto| exact H].
  - exists (hp, dl_Ah L, 65536). split; [cbn; tauto| exact H].
  - exists (bp, dl_Ab L, 65536). split; [cbn; tauto| exact H].
Qed.

End WithCeiling0.
