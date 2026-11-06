(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Cells.v, with its module paths and module names changed; 79 of its 99 lines of code are new or changed and 171 lines of the source are left out. *)
(* reac-pw/fuzz_link, PLAIN build: the FILE block fmemopen("w") leaves is lib/MemFile.v's memory FILE.

   fmemopen_tail ends with `rw_cells rsegs m h (mfw_cells h b n ung buf)`: the 1304-byte block as cells (FILE,
   cookie, unget bytes, buffer). `mfw_props` reads each word `memfile_at` (MemFile.v), `mf_win` and `mf_dyn`
   (memfile_c.v) name from those cells, for the caller's buffer (b = g_said, n = 4096): flags F_NORD, the window
   empty, the cookie's pos = len = 0, size 4096, buf g_said, mode 'w', lock / fd / lbf = -1, the four m*
   function pointers, prev = next = 0, and the block writable. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import MState Mem Cells Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0f YO0d YP09 YI04 YI14 YH02.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require KindBGlue MemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import StdioModel StdioKB fmemopen_tail.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require memfile_c link_mem link_spec.
Import ListNotations.
Local Open Scope Z_scope.

(* the bytes of one cell of a cell list, at its offset *)
Lemma mfw_cell_bytes : forall m A cs k c, cells_at rsegs m A cs -> cell_at cs k = Some c ->
  bytes_at rsegs m (A + Z.of_nat k) (cbytes c).
Proof.
  intros m A cs k c [Hwf Hb] Hc.
  destruct (cell_at_split _ _ _ c Hc) as (pre & post & Ecs & Hsz & _).
  rewrite Ecs in Hwf, Hb. apply cells_wf_app in Hwf. destruct Hwf as [Hwpre [Hwc Hwpost]].
  rewrite cells_bytes_app in Hb. cbn [cells_bytes] in Hb.
  apply bytes_at_app in Hb. destruct Hb as [_ Hb].
  rewrite cells_bytes_length in Hb by assumption. rewrite Hsz in Hb.
  apply bytes_at_app in Hb. destruct Hb as [Hb _]. exact Hb.
Qed.

Lemma le_byte4_bv : forall v k, 0 <= v < 2 ^ 32 ->
  Z_to_bv 8 (YO0f.le_byte v 4 k) = Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k)).
Proof.
  intros v k Hv. unfold YO0f.le_byte. change (8 * Z.of_nat 4) with 32.
  rewrite (Z.mod_small v (2 ^ 32)) by lia.
  apply Z_to_bv8_mod. change 256 with (2 ^ 8). apply Z.mod_mod. lia.
Qed.

(* an 8-byte cell holding v is the field `val_mem _ 8 v` *)
Lemma mfw_fld8 : forall m A cs off v w, cells_at rsegs m A cs -> 0 <= off ->
  cell_at cs (Z.to_nat off) = Some (C8 w) -> w = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  YI04.val_mem rsegs m (A + off) 8 v.
Proof.
  intros m A cs off v w Hc Ho Hk -> Hv.
  pose proof (mfw_cell_bytes m A cs _ _ Hc Hk) as Hb. cbn [cbytes] in Hb.
  rewrite Z2Nat.id in Hb by exact Ho.
  apply (proj2 (YI04.val_mem_word_mem rsegs m (A + off) v)).
  pose proof (KindBGlue.bytes_at_le8_word rsegs m (A + off) _ Hb) as Hw.
  rewrite unsigned_lit in Hw by lia. exact Hw.
Qed.

(* a 4-byte cell holding v < 2^32 is the field `val_mem _ 4 v` *)
Lemma mfw_fld4 : forall m A cs off v w, cells_at rsegs m A cs -> 0 <= off ->
  cell_at cs (Z.to_nat off) = Some (C4 w) -> w = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  YI04.val_mem rsegs m (A + off) 4 v.
Proof.
  intros m A cs off v w Hc Ho Hk -> Hv.
  pose proof (mfw_cell_bytes m A cs _ _ Hc Hk) as Hb. cbn [cbytes] in Hb.
  rewrite Z2Nat.id in Hb by exact Ho.
  destruct Hb as (Ha & Hl & H). intros k Hk'.
  rewrite length_le4 in H. specialize (H k Hk'). unfold le4 in H.
  rewrite unsigned_lit in H by lia. rewrite KindBGlue.kb_nth_le_bytes in H by exact Hk'.
  rewrite le_byte4_bv by exact Hv. exact H.
Qed.

Ltac mfw_ar :=
  unfold MemFile.MF_BUF, MemFile.MF_BUFSIZ, MemFile.MF_COOKIE, MemFile.F_NORD, YI14.U32M1,
    link_mem.A_G_SAID, link_spec.SAID_SIZE in *;
  cbn [MemFile.mf_close MemFile.mf_read MemFile.mf_write MemFile.mf_seek MemFile.mf_size MemFile.mf_buf
    MemFile.mf_mode MemFile.link_mf];
  lia.

Lemma mfw_props : forall m h ung buf,
  rw_cells rsegs m h (mfw_cells h link_mem.A_G_SAID link_spec.SAID_SIZE ung buf) ->
  0 < h -> h + MemFile.MF_BLOCK <= 2 ^ 64 -> h mod 16 = 0 ->
  MemFile.memfile_at YH02.src0_msyms MemFile.link_mf m h /\ memfile_c.mf_win m h 0 /\
  memfile_c.mf_dyn m h MemFile.F_NORD 0 0 0 0 0 0 /\ wr_at rsegs m h MemFile.MF_BLOCK.
Proof.
  intros m h ung buf HC H0 H1 H2.
  pose proof HC as [CA WR].
  set (CS := mfw_cells h link_mem.A_G_SAID link_spec.SAID_SIZE ung buf) in *.
  assert (F8 : forall off v w, 0 <= off -> cell_at CS (Z.to_nat off) = Some (C8 w) -> w = Z_to_bv 64 v ->
                 0 <= v < 2 ^ 64 -> YI04.val_mem rsegs m (h + off) 8 v)
    by (intros off v w; exact (mfw_fld8 m h CS off v w CA)).
  assert (F4 : forall off v w, 0 <= off -> cell_at CS (Z.to_nat off) = Some (C4 w) -> w = Z_to_bv 64 v ->
                 0 <= v < 2 ^ 32 -> YI04.val_mem rsegs m (h + off) 4 v)
    by (intros off v w; exact (mfw_fld4 m h CS off v w CA)).
  unfold MemFile.MF_BLOCK in H1.
  split; [|split; [|split]].
  - unfold MemFile.memfile_at, MemFile.memfile_static, MemFile.memfile_flags, MemFile.memfile_omode,
      MemFile.memfile_window, MemFile.memfile_cookie.
    change (YO0d.ms_segs YH02.src0_msyms) with rsegs.
    split; [exact H0|]. split; [unfold MemFile.MF_BLOCK; lia|]. split; [exact H2|].
    split; [|split; [|split; [|split]]].
    + repeat match goal with |- _ /\ _ => split end;
        first [ eapply F8; [mfw_ar | reflexivity | reflexivity | mfw_ar]
              | eapply F4; [mfw_ar | reflexivity | reflexivity | mfw_ar] ].
    + left. eapply F4; [mfw_ar | reflexivity | reflexivity | mfw_ar].
    + left. eapply F4; [mfw_ar | reflexivity | reflexivity | mfw_ar].
    + split; [eapply F8; [mfw_ar | reflexivity | reflexivity | mfw_ar]|].
      split; [eapply F8; [mfw_ar | reflexivity | reflexivity | mfw_ar]|].
      left. split; [|split]; (eapply F8; [mfw_ar | reflexivity | reflexivity | mfw_ar]).
    + exists 0, 0. split; [lia|]. split; [mfw_ar|].
      split; (eapply F8; [mfw_ar | reflexivity | reflexivity | mfw_ar]).
  - unfold memfile_c.mf_win, memfile_c.mf_fld. left. split; [reflexivity|].
    split; [|split]; (eapply F8; [mfw_ar | reflexivity | reflexivity | mfw_ar]).
  - unfold memfile_c.mf_dyn, memfile_c.mf_fld.
    repeat match goal with |- _ /\ _ => split end;
      first [ eapply F8; [mfw_ar | reflexivity | reflexivity | mfw_ar]
            | eapply F4; [mfw_ar | reflexivity | reflexivity | mfw_ar]
            | mfw_ar ].
  - assert (SZ : cells_size CS = 1304%nat) by reflexivity.
    rewrite SZ in WR. exact WR.
Qed.
