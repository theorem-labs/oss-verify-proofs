(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN0j.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YN0j.v, with its module paths and module names changed; 546 of its 584 lines of code are new or changed and 260 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segC.v, with its module names changed; 1538 of its 1613 lines of code are new or changed and 509 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segC2.v, with its module names changed; 66 of its 123 lines of code are new or changed and 1556 lines of the source are left out. *)
(* rule 24: proves no function (kind: inner boundary invariants of check_round_trip's D1 segment lemma, PORTED from
   a working branch d25a984c903 proofs/omx-clap-core/fuzz_state/lib/A/Prog/check_round_trip_stdefs.v St17
   :521 / St18 :535 - the holdings of the two fuzz_free stages, restated in the S0 form of FSH_crt_base.crt_inv).

   check_round_trip 0x81a9c, fs.asan (sha256 64b53ff86172bb07...), lane D1 (segments 30-33, a Theorem Labs lane): the THREE boundary
   invariants INSIDE the lane, between the lane's published ends crt_INV_82268 (entry, base) and crt_INV_822ac (exit,
   base). They are this lane's own; no other lane names them.
     crtD1_INV_82274  the return of the second preset_base64_decode: its block `got` is live and holds b64_dec of the
                      text, the length cell at F + 0x1a0 holds |bs|, `file` is still live;
     crtD1_INV_82298  the return of the bcmp thunk (or the empty-body arm that skips it): the same holdings, with the
                      compared block in s7 (atom 23) and a0 = 0;
     crtD1_INV_822a4  the return of fuzz_free (got): got is gone from the blocks and its head from U, `file` is the
                      next to go.
   Budgets, in the base's callee terms: the decode's success arm costs EV_fuzz_malloc ticks, one g_count bump and
   dec_size tb2 + HEAD bytes; bcmp costs nothing; each fuzz_free costs EV_fuzz_free ticks and gives bytes back, so the
   prefix bounds chain to the base's K_822ac / CNT_822ac / LIVE_822ac exactly. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_rres FSW_frame
FSH_Fn_reader FSH_Fn_writer FSH_Fn_alloc FSH_Fn_crt FSH_crt_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec HState PjStruct
  check_round_trip_stages_b.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section d1. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* ---- the lane's prefix budgets, in the base's callee terms ---- *)
Definition K_82274 (cx : crt_cx) : Z := K_82268 cx + EV_fuzz_malloc.
Definition CNT_82274 (cx : crt_cx) : Z := CNT_82268 cx + 1.
Definition LIVE_82274 (cx : crt_cx) : Z :=
  LIVE_82268 cx + (FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD).
Definition K_822a4 (cx : crt_cx) : Z := K_82274 cx + EV_fuzz_free.

(* ---- what the three inner boundaries share: the trees, the text and back blocks, the frame objects, and the
   bookkeeping. `got` is the second decode's block (0 bytes of it are read after the bcmp), `file` pj_write's text. ---- *)
Definition crtD1_common (cx : crt_cx) (ly3 : alayout) (S3 : astate) (W3 : world tfibsegs)
    (mem : word -> option byte) (back : Z) (Ddoc Dback : list (Z * Z)) (tback : PjTree.jv) : Prop :=
  let F := crt_F cx in let len := Z.of_nat (length (c_bs cx)) in
  let tb2 := WriterSpec.b64_enc (c_bs cx) in
  fs_rblock tfibsegs B ly3 S3 W3 mem (c_text cx) (FSH_Fn_writer.enc_size len) /\
  fs_rblock tfibsegs B ly3 S3 W3 mem back (FSH_Fn_writer.dec_size tb2) /\
  rtree tfibsegs B ly3 S3 W3 mem (F + 0x20) (PjTree.JObj (check_round_trip_stages_b.crt_doc tb2)) Ddoc /\
  rnode tfibsegs B ly3 S3 W3 mem (Ddoc ++ Dback) (F + 0x140) tback Dback /\ (PjTree.depth tback <= 2)%nat /\
  pobj tfibsegs B ly3 S3 W3 mem (F + 0x140) /\ pobj tfibsegs B ly3 S3 W3 mem (F + 0x20).

(* ---- 0x82274, the return of the second preset_base64_decode. Its block `got` holds b64_dec of the text, i.e. the
   body bs, and the length cell at F + 0x1a0 holds |bs| (the `bne a0, s4` at 0x82280 reads it). ---- *)
Definition crtD1_INV_82274 : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  let mem := ms_mem ms3 in let F := crt_F cx in let len := Z.of_nat (length (c_bs cx)) in
  let tb2 := WriterSpec.b64_enc (c_bs cx) in
  ew E 18 = Z_to_bv 64 (F + 0x140) /\ ew E 20 = Z_to_bv 64 len /\ ew E 21 = Z_to_bv 64 (c_bd cx) /\
  ew E 26 = Z_to_bv 64 (F + 0x20) /\ ew E 27 = Z_to_bv 64 (F + 0x1a0) /\
  (exists (same nsame file nfile back got : Z) (Dback Ddoc : list (Z * Z)) (tback : PjTree.jv) (live peak cnt : Z),
     ew E 22 = Z_to_bv 64 file /\ ew E 24 = Z_to_bv 64 same /\ ew E 25 = Z_to_bv 64 back /\
     ew E 10 = Z_to_bv 64 got /\ 4096 + HEAD <= got /\
     Permutation (ablocks B ly3 S3)
       (ablocks B (c_ly cx) (c_S cx) ++
        [(c_text cx - HEAD, FSH_Fn_writer.enc_size len + HEAD); (c_want cx, FSH_Fn_writer.enc_size len);
         (same, nsame); (back - HEAD, FSH_Fn_writer.dec_size tb2 + HEAD); (file - HEAD, nfile + HEAD);
         (got - HEAD, FSH_Fn_writer.dec_size tb2 + HEAD)] ++ rd_hblocks (Ddoc ++ Dback)) /\
     Permutation U3 (c_U cx ++ [(c_text cx - HEAD, HEAD); (back - HEAD, HEAD); (file - HEAD, HEAD);
        (got - HEAD, HEAD)] ++ rd_heads (Ddoc ++ Dback)) /\
     FSupoisonU.fs_heads B ly3 S3 U3 /\
     crtD1_common cx ly3 S3 W3 mem back Ddoc Dback tback /\
     fs_rblock tfibsegs B ly3 S3 W3 mem file nfile /\
     fs_rblock tfibsegs B ly3 S3 W3 mem got (FSH_Fn_writer.dec_size tb2) /\
     zbytes_at tfibsegs W3 mem got (c_bs cx) /\
     val_mem tfibsegs (mrestrict (w_H W3) mem) (F + 0x1a0) 8 len /\
     range_addressable (aview tfibsegs (w_H W3) mem) SHADOW_OFF (F + 0x1a0) 8 /\
     fs_glob tfibsegs W3 mem live peak cnt SIZE_MAXZ /\
     live = c_live cx + FSH_Fn_writer.enc_size len + FSH_Fn_writer.dec_size tb2 + nfile +
            FSH_Fn_writer.dec_size tb2 + rd_sum (Ddoc ++ Dback) /\
     blocks_bytes S3 <= blocks_bytes (c_S cx) + LIVE_82274 cx /\
     c_cnt cx <= cnt <= c_cnt cx + CNT_82274 cx /\ k <= K_82274 cx /\
     (* the remaining allowance (base v20, crt_INV_82268's last conjunct, less the decode's EV_fuzz_malloc) *)
     k + 2 * EV_fuzz_free + EV_pj_free Dback + EV_pj_free Ddoc + 2 * EV_fuzz_free + 2 * CRT_EV_WRAP
       <= EV_check_round_trip).

(* ---- 0x82298, the return of the bcmp thunk, and the join point of the empty-body arm (0x8229c): the same holdings,
   with got in s7 (atom 23) and a0 = 0, which the `bnez a0` at 0x82298 needs. The length cell is not read again. ---- *)
Definition crtD1_INV_82298 : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  let mem := ms_mem ms3 in let F := crt_F cx in let len := Z.of_nat (length (c_bs cx)) in
  let tb2 := WriterSpec.b64_enc (c_bs cx) in
  ew E 10 = Z_to_bv 64 0 /\
  ew E 18 = Z_to_bv 64 (F + 0x140) /\ ew E 20 = Z_to_bv 64 len /\ ew E 21 = Z_to_bv 64 (c_bd cx) /\
  ew E 26 = Z_to_bv 64 (F + 0x20) /\ ew E 27 = Z_to_bv 64 (F + 0x1a0) /\
  (exists (same nsame file nfile back got : Z) (Dback Ddoc : list (Z * Z)) (tback : PjTree.jv) (live peak cnt : Z),
     ew E 22 = Z_to_bv 64 file /\ ew E 24 = Z_to_bv 64 same /\ ew E 25 = Z_to_bv 64 back /\
     ew E 23 = Z_to_bv 64 got /\ 4096 + HEAD <= got /\
     Permutation (ablocks B ly3 S3)
       (ablocks B (c_ly cx) (c_S cx) ++
        [(c_text cx - HEAD, FSH_Fn_writer.enc_size len + HEAD); (c_want cx, FSH_Fn_writer.enc_size len);
         (same, nsame); (back - HEAD, FSH_Fn_writer.dec_size tb2 + HEAD); (file - HEAD, nfile + HEAD);
         (got - HEAD, FSH_Fn_writer.dec_size tb2 + HEAD)] ++ rd_hblocks (Ddoc ++ Dback)) /\
     Permutation U3 (c_U cx ++ [(c_text cx - HEAD, HEAD); (back - HEAD, HEAD); (file - HEAD, HEAD);
        (got - HEAD, HEAD)] ++ rd_heads (Ddoc ++ Dback)) /\
     FSupoisonU.fs_heads B ly3 S3 U3 /\
     crtD1_common cx ly3 S3 W3 mem back Ddoc Dback tback /\
     fs_rblock tfibsegs B ly3 S3 W3 mem file nfile /\
     fs_rblock tfibsegs B ly3 S3 W3 mem got (FSH_Fn_writer.dec_size tb2) /\
     fs_glob tfibsegs W3 mem live peak cnt SIZE_MAXZ /\
     live = c_live cx + FSH_Fn_writer.enc_size len + FSH_Fn_writer.dec_size tb2 + nfile +
            FSH_Fn_writer.dec_size tb2 + rd_sum (Ddoc ++ Dback) /\
     blocks_bytes S3 <= blocks_bytes (c_S cx) + LIVE_82274 cx /\
     c_cnt cx <= cnt <= c_cnt cx + CNT_82274 cx /\ k <= K_82274 cx /\
     (* bcmp ticks nothing: the same allowance as at 0x82274 *)
     k + 2 * EV_fuzz_free + EV_pj_free Dback + EV_pj_free Ddoc + 2 * EV_fuzz_free + 2 * CRT_EV_WRAP
       <= EV_check_round_trip).

(* ---- 0x822a4, the return of fuzz_free (got): got is out of the blocks and its head out of U; `file` is in s6
   (atom 22) and is the next to go. ---- *)
Definition crtD1_INV_822a4 : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  let mem := ms_mem ms3 in let F := crt_F cx in let len := Z.of_nat (length (c_bs cx)) in
  let tb2 := WriterSpec.b64_enc (c_bs cx) in
  ew E 18 = Z_to_bv 64 (F + 0x140) /\ ew E 20 = Z_to_bv 64 len /\ ew E 21 = Z_to_bv 64 (c_bd cx) /\
  ew E 26 = Z_to_bv 64 (F + 0x20) /\ ew E 27 = Z_to_bv 64 (F + 0x1a0) /\
  (exists (same nsame file nfile back : Z) (Dback Ddoc : list (Z * Z)) (tback : PjTree.jv) (live peak cnt : Z),
     ew E 22 = Z_to_bv 64 file /\ ew E 24 = Z_to_bv 64 same /\ ew E 25 = Z_to_bv 64 back /\
     Permutation (ablocks B ly3 S3)
       (ablocks B (c_ly cx) (c_S cx) ++
        [(c_text cx - HEAD, FSH_Fn_writer.enc_size len + HEAD); (c_want cx, FSH_Fn_writer.enc_size len);
         (same, nsame); (back - HEAD, FSH_Fn_writer.dec_size tb2 + HEAD); (file - HEAD, nfile + HEAD)] ++
        rd_hblocks (Ddoc ++ Dback)) /\
     Permutation U3 (c_U cx ++ [(c_text cx - HEAD, HEAD); (back - HEAD, HEAD); (file - HEAD, HEAD)] ++
        rd_heads (Ddoc ++ Dback)) /\
     FSupoisonU.fs_heads B ly3 S3 U3 /\
     crtD1_common cx ly3 S3 W3 mem back Ddoc Dback tback /\
     fs_rblock tfibsegs B ly3 S3 W3 mem file nfile /\
     fs_glob tfibsegs W3 mem live peak cnt SIZE_MAXZ /\
     live = c_live cx + FSH_Fn_writer.enc_size len + FSH_Fn_writer.dec_size tb2 + nfile +
            rd_sum (Ddoc ++ Dback) /\
     (* the TIGHT bound (a Theorem Labs lane 05:4xZ): freeing got gave back exactly dec_size tb2 + HEAD, i.e.
        LIVE_82274 cx - (dec_size tb2 + HEAD) = LIVE_82268 cx = LIVE_822ac cx, and segment 33 needs that form,
        since nothing here bounds nfile below *)
     blocks_bytes S3 <= blocks_bytes (c_S cx) + LIVE_822ac cx /\
     c_cnt cx <= cnt <= c_cnt cx + CNT_822ac cx /\ k <= K_822a4 cx /\
     (* one fuzz_free paid: the allowance less EV_fuzz_free; the next free leaves crt_INV_822ac's exactly *)
     k + EV_fuzz_free + EV_pj_free Dback + EV_pj_free Ddoc + 2 * EV_fuzz_free + 2 * CRT_EV_WRAP
       <= EV_check_round_trip).
End d1.
