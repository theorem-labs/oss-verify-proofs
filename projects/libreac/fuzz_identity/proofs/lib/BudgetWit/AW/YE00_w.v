(* Modified by Theorem Labs, 2026-11: made from Reusable/YE00.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-10-29: taken from grant's no-file sink form,
   released lib/Reusable/YE00.v (projects/libreac/fuzz_grant/proofs/lib/Reusable/YE00.v), with fuzz_grant -> fuzz_identity.
   identity writes no file (no fopen / fclose symbol; the bytes `rwa\0`, `wb\0` and `TRAILER` occur zero
   times in its PT_LOADs), so the four file-string fields are 0 and `asink_strs` is never stated. This
   version splits the string obligations out of `astdio_env` into `asink_strs`, adds `aenv_core`, and
   rebases `aenv_addr` on the new `ak_owned` list instead of the string ranges. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/YE00.v, with its module paths changed; asink_syms has the field ak_owned (the sink's own static cells), aenv_addr is those cells and the 8-byte ofl head, aenv_core names the four cells astdio_env reads and the frame lemmas frame over aenv_core, and astdio_env no longer states the path, mode, "rwa" and trailer strings: asink_strs states them, only for a harness that writes a file (astdio_env_trailer becomes asink_strs_trailer). *)
(* Modified by Theorem Labs, 2026-11: internal commit ids in comments replaced by public commits or removed. *)
(* Theorem Labs, 2026-11: cut for the usage path at 16 GiB: the pruning removed declarations that this path does not use; some unused declarations can remain. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Namei.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YP09 YI04 YI00 YI16 YK04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require YG0n_w.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition AMETA_SIZE : Z := 3727360.
Record asink_syms : Type := mkASink {
ak_read : Z; ak_write : Z; ak_seek : Z; ak_close : Z;
ak_path : Z;
ak_mode : Z;
ak_rwa : Z;
ak_trailer : Z;
ak_threaded : Z;
ak_need_locks : Z;
ak_ofl_lock : Z;
ak_meta_ptr : Z;
ak_meta_mem : Z;
ak_can_got : Z;
ak_canary : Z;
ak_icells : list (Z * Z);
ak_owned : list (Z * Z)
}.
Definition ak_ofl_head (K : asink_syms) : Z := ak_ofl_lock K + 8.
Section b.
Variable segs : list Segment.
Variable K : asink_syms.
Local Notation fld m f off n v := (val_mem segs m (f + off) n v).
Definition astdio_env (m : word -> option byte) : Prop :=
val_mem segs m (ak_threaded K) 1 0 /\
val_mem segs m (ak_need_locks K) 1 0 /\
val_mem segs m (ak_ofl_lock K) 4 0 /\
(exists cval, 0 <= cval < 2 ^ 64 /\ val_mem segs m (ak_canary K) 8 cval).
Definition ameta_ok (m : word -> option byte) (M : Z) : Prop :=
val_mem segs m (ak_meta_ptr K) 8 (ak_meta_mem K) /\
val_mem segs m (ak_meta_mem K) 8 M /\
0 <= M /\ M + AMETA_SIZE <= 2 ^ 47 /\ M mod 4096 = 0 /\
(forall a, M <= a < M + AMETA_SIZE -> mbyte segs m a = Some (Z_to_bv 8 0)).
Definition aenv_core (a : Z) : Prop :=
a = ak_threaded K \/ a = ak_need_locks K \/ (ak_ofl_lock K <= a < ak_ofl_lock K + 4) \/
(ak_canary K <= a < ak_canary K + 8).
Definition aenv_addr (a : Z) : Prop :=
Exists (YG0n_w.in_zr a) (ak_owned K) \/ (ak_ofl_head K <= a < ak_ofl_head K + 8).

Lemma val_mem_frame : forall (m m' : word -> option byte) a n v,
(forall x, a <= x < a + Z.of_nat n -> mbyte segs m' x = mbyte segs m x) ->
val_mem segs m a n v -> val_mem segs m' a n v.
Proof. intros m m' a n v Hfr Hv k Hk. rewrite Hfr by lia. exact (Hv k Hk). Qed.

Lemma astdio_env_frame : forall (m m' : word -> option byte),
(forall a, aenv_core a -> mbyte segs m' a = mbyte segs m a) -> astdio_env m -> astdio_env m'.
Proof.
intros m m' Hfr (H1 & H2 & H3 & (cv & Hcv & H8)). unfold astdio_env.
split; [eapply val_mem_frame; [|exact H1]; intros x Hx; apply Hfr; unfold aenv_core; cbn in Hx; lia|].
split; [eapply val_mem_frame; [|exact H2]; intros x Hx; apply Hfr; unfold aenv_core; cbn in Hx; lia|].
split; [eapply val_mem_frame; [|exact H3]; intros x Hx; apply Hfr; unfold aenv_core; cbn in Hx; lia|].
exists cv. split; [exact Hcv|]. eapply val_mem_frame; [|exact H8]; intros x Hx; apply Hfr; unfold aenv_core; cbn in Hx; lia.
Qed.

Lemma ameta_ok_frame : forall (m m' : word -> option byte) M,
(forall a, (ak_meta_ptr K <= a < ak_meta_ptr K + 8) \/ (ak_meta_mem K <= a < ak_meta_mem K + 8) \/ (M <= a < M + AMETA_SIZE) ->
mbyte segs m' a = mbyte segs m a) ->
ameta_ok m M -> ameta_ok m' M.
Proof.
intros m m' M Hfr (H1 & H2 & H3 & H4 & H5 & HZ). unfold ameta_ok.
split; [eapply val_mem_frame; [|exact H1]; intros x Hx; apply Hfr; cbn in Hx; lia|].
split; [eapply val_mem_frame; [|exact H2]; intros x Hx; apply Hfr; cbn in Hx; lia|].
split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
intros a Ha. rewrite Hfr by lia. exact (HZ a Ha).
Qed.
End b.
