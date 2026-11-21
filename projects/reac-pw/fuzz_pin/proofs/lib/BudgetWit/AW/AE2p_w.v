(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE2p.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AE2p.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_pin's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AE2p.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK0s.

From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.

From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0p_w YA0q_w.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.BudgetWit.AW Require Import YG0n_w YG0d_w.

From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import AB1v AE34 AF0l AF0m AE3e.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.BudgetWit.AW Require Import AE3f_w AE3g_w AE6g_w AF0x_w.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import AE20.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.BudgetWit.AW Require Import AE2y_w AE7f_w.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section c.
Definition F_STDERR : Z := 0x9d618.
Definition STDERR_BUF : Z := 0x5f4ca0.
Definition A_GOT_canary : Z := 0x99cd8.
Definition A_canary : Z := 0x5f45d8.
Definition FILE_SZ : Z := 232.
Definition stderr_fields : list (Z * N * Z) :=
[(0, 4%N, 5); (4, 4%N, 0); (8, 8%N, 0); (16, 8%N, 0); (24, 8%N, 0x8cdc0); (32, 8%N, 0); (40, 8%N, 0); (48, 8%N, 0); (56, 8%N, 0); (64, 8%N, 0);
(72, 8%N, 0x8cf0c); (80, 8%N, 0x8cf04); (88, 8%N, STDERR_BUF); (96, 8%N, 0); (104, 8%N, 0); (112, 8%N, 0); (120, 8%N, 2);
(128, 8%N, 0); (136, 4%N, 0); (140, 4%N, 0xffffffff); (144, 8%N, 0xffffffff);
(152, 8%N, 0); (160, 8%N, 0); (168, 8%N, 0); (176, 8%N, 0); (184, 8%N, 0); (192, 8%N, 0); (200, 8%N, 0); (208, 8%N, 0);
(216, 8%N, 0); (224, 8%N, 0)].
Definition file_is (flds : list (Z * N * Z)) (m : word -> option byte) : Prop :=
Forall (fun f => match f with (o, n, v) => val_mem tfibsegs m (F_STDERR + o) (N.to_nat n) v end) flds.
Definition stderr_pristine : (word -> option byte) -> Prop := file_is stderr_fields.
Definition fw_file_chunks : list YP09.chunk :=
map (fun f => match f with (o, n, v) => YP09.mkChunk (F_STDERR + o) (CVal n (SLit v)) end) stderr_fields.
Section S.
Definition le_bytes (n : nat) (v : Z) : list Z := map (fun k => le_byte v n k) (seq 0 n).
Lemma val_mem_of_lit : forall E m rs a n v,
mem_ok tfibsegs E m rs -> lit_buf tfibsegs rs (SLit a) n = Some (le_bytes n v) -> val_mem tfibsegs m a n v.
Proof.
intros E m rs a n v HM Hl k Hk.
pose proof (lit_buf_sound tfibsegs E m rs (SLit a) n _ HM Hl) as Hr. cbn [sv_denot] in Hr.
apply (proj1 (rdn_mbytes tfibsegs m n a _)) in Hr as [_ Hr].
rewrite (Hr k Hk). unfold le_bytes. rewrite !nth_error_map.
rewrite (nth_error_nth' (seq 0 n) 0%nat) by (rewrite length_seq; exact Hk). rewrite seq_nth by exact Hk. reflexivity.
Qed.
End S.
End c.
