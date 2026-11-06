(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require Import X1rw X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X01x X0ec X00a X001 X00b X00c X000.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X0sw X14x X0r9 X0r0 X0ra X0rb X0qz.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0sw OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz.
Import ListNotations.
Open Scope Z_scope.

Definition IO_FPA : list (Z * Z) := [(0x1007b0, 0x100898); (0x1008a0, 0x100988); (0x659398, 0x659be8)].
Definition OUT_repA (so : stdout_st) (m : mem) : Prop := stdout_file m so.
Definition ERR_repA (m : mem) : Prop := stderr_wfile0 m.

Lemma in_IO_FPA : forall lo hi x, In (lo, hi) IO_FPA -> lo <= x < hi -> in_ranges IO_FPA x.
Proof. intros lo hi x H1 H2. exists lo, hi. split; assumption. Qed.

Lemma OUT_locA : forall so, fp_local IO_FPA (OUT_repA so).
Proof.
intros so m m' (flags & mode & tail & bb & FC & FL & BUF & BP & BL & INA) AG.
exists flags, mode, tail, bb. split; [| split; [exact FL| split; [| split; [exact BP| split; [exact BL| exact INA]]]]].
- apply (rw_cells_agree_nw bsegs m m' _ _ FC). intros a Ha. apply AG.
apply (in_IO_FPA 0x1008a0 0x100988); [cbn; tauto|]. unfold file_cells in Ha. cbn [cells_size csize] in Ha. lia.
- apply (rw_cells_agree_nw bsegs m m' _ _ BUF). intros a Ha. apply AG.
apply (in_IO_FPA 0x659398 0x659be8); [cbn; tauto|]. cbn [cells_size csize] in Ha. lia.
Qed.

Lemma ERR_locA : fp_local IO_FPA ERR_repA.
Proof.
intros m m' (flags & mode & e & wend & tail & FC & REST) AG.
exists flags, mode, e, wend, tail. split; [| exact REST].
apply (rw_cells_agree_nw bsegs m m' _ _ FC). intros a Ha. apply AG.
apply (in_IO_FPA 0x1007b0 0x100898); [cbn; tauto|]. unfold file_cells in Ha. cbn [cells_size csize] in Ha. lia.
Qed.

Lemma IO_imgA : forall x, in_ranges IO_FPA x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Proof.
intros x (lo & hi & Hin & Hx). cbn in Hin.
split; [| split].
- apply client_static_intro. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
- unfold drv_cell, ERRNO_A, TP_A, SSP_GUARD, TR_INIT, g_read_stage. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
- unfold LIB_FP. cbn. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; (repeat (split; [lia|])); try exact I.
Qed.

Lemma stdout_file_agree : forall so m m',
agree_on (fun x => (0x1008a0 <= x < 0x100988) \/ (0x6593a8 <= x < 0x659be8)) m m' -> wmono bsegs m m' ->
OUT_repA so m -> OUT_repA so m'.
Proof.
intros so m m' AG WM (flags & mode & tail & bb & FC & FL & BUF & BP & BL & INA).
exists flags, mode, tail, bb. split; [| split; [exact FL| split; [| split; [exact BP| split; [exact BL| exact INA]]]]].
- apply (rw_cells_agree bsegs m m' _ _ FC); [| exact WM]. intros a Ha. apply AG.
left. unfold file_cells in Ha. cbn [cells_size csize] in Ha. lia.
- apply (rw_cells_agree bsegs m m' _ _ BUF); [| exact WM]. intros a Ha. apply AG.
right. cbn [cells_size csize] in Ha. lia.
Qed.

Lemma stderr_wfile0_agree : forall m m',
agree_on (fun x => 0x1007b0 <= x < 0x100898) m m' -> wmono bsegs m m' -> ERR_repA m -> ERR_repA m'.
Proof.
intros m m' AG WM (flags & mode & e & wend & tail & FC & REST).
exists flags, mode, e, wend, tail. split; [| exact REST].
apply (rw_cells_agree bsegs m m' _ _ FC); [| exact WM]. intros a Ha. apply AG.
unfold file_cells in Ha. cbn [cells_size csize] in Ha. lia.
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Definition IO_FPA : list (Z * Z) := [(0xf7f30, 0xf8018); (0xf8020, 0xf8108); (0x650b58, 0x6513a8)].
Definition OUT_repA (so : stdout_st) (m : mem) : Prop := stdout_file m so.
Definition ERR_repA (m : mem) : Prop := stderr_wfile0 m.

Lemma in_IO_FPA : forall lo hi x, In (lo, hi) IO_FPA -> lo <= x < hi -> in_ranges IO_FPA x.
Proof. intros lo hi x H1 H2. exists lo, hi. split; assumption. Qed.

Lemma OUT_locA : forall so, fp_local IO_FPA (OUT_repA so).
Proof.
intros so m m' (flags & mode & tail & bb & FC & FL & BUF & BP & BL & INA) AG.
exists flags, mode, tail, bb. split; [| split; [exact FL| split; [| split; [exact BP| split; [exact BL| exact INA]]]]].
- apply (rw_cells_agree_nw asegs m m' _ _ FC). intros a Ha. apply AG.
apply (in_IO_FPA 0xf8020 0xf8108); [cbn; tauto|]. unfold file_cells in Ha. cbn [cells_size csize] in Ha. lia.
- apply (rw_cells_agree_nw asegs m m' _ _ BUF). intros a Ha. apply AG.
apply (in_IO_FPA 0x650b58 0x6513a8); [cbn; tauto|]. cbn [cells_size csize] in Ha. lia.
Qed.

Lemma ERR_locA : fp_local IO_FPA ERR_repA.
Proof.
intros m m' (flags & mode & e & wend & tail & FC & REST) AG.
exists flags, mode, e, wend, tail. split; [| exact REST].
apply (rw_cells_agree_nw asegs m m' _ _ FC). intros a Ha. apply AG.
apply (in_IO_FPA 0xf7f30 0xf8018); [cbn; tauto|]. unfold file_cells in Ha. cbn [cells_size csize] in Ha. lia.
Qed.

Lemma IO_imgA : forall x, in_ranges IO_FPA x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Proof.
intros x (lo & hi & Hin & Hx). cbn in Hin.
split; [| split].
- apply client_static_intro. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
- unfold drv_cell, ERRNO_A, TP_A, SSP_GUARD, TR_INIT, g_read_stage. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
- unfold LIB_FP. cbn. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; (repeat (split; [lia|])); try exact I.
Qed.

Lemma stdout_file_agree : forall so m m',
agree_on (fun x => (0xf8020 <= x < 0xf8108) \/ (0x650b68 <= x < 0x6513a8)) m m' -> wmono asegs m m' ->
OUT_repA so m -> OUT_repA so m'.
Proof.
intros so m m' AG WM (flags & mode & tail & bb & FC & FL & BUF & BP & BL & INA).
exists flags, mode, tail, bb. split; [| split; [exact FL| split; [| split; [exact BP| split; [exact BL| exact INA]]]]].
- apply (rw_cells_agree asegs m m' _ _ FC); [| exact WM]. intros a Ha. apply AG.
left. unfold file_cells in Ha. cbn [cells_size csize] in Ha. lia.
- apply (rw_cells_agree asegs m m' _ _ BUF); [| exact WM]. intros a Ha. apply AG.
right. cbn [cells_size csize] in Ha. lia.
Qed.

Lemma stderr_wfile0_agree : forall m m',
agree_on (fun x => 0xf7f30 <= x < 0xf8018) m m' -> wmono asegs m m' -> ERR_repA m -> ERR_repA m'.
Proof.
intros m m' AG WM (flags & mode & e & wend & tail & FC & REST).
exists flags, mode, e, wend, tail. split; [| exact REST].
apply (rw_cells_agree asegs m m' _ _ FC); [| exact WM]. intros a Ha. apply AG.
unfold file_cells in Ha. cbn [cells_size csize] in Ha. lia.
Qed.
