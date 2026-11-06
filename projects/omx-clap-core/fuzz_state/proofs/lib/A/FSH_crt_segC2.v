(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN0j.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YN0j.v, with its module paths and module names changed; 546 of its 584 lines of code are new or changed and 260 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segC.v, with its module names changed; 1538 of its 1613 lines of code are new or changed and 509 lines of the source are left out. *)
(* check_round_trip 0x81a9c (fuzz_state.c:278-314 with round_trip_document fs.c:229-264 inlined), fs.asan (image
   tfibsegs, the pinned fuzz_state.asan sha256 64b53ff86172bb07f93f146e67b81a0354bca88e0a580e93fb1da01406fb76e0): the ASan
   walk of FSH_Fn_crt.v check_round_trip_spec, segment group C2 = segments 25-29, from the return of the last pj_set at
   0x82214 (0x82218) to the return of pj_get_str at 0x82264 (0x82268), with the class-3 fake frame live
   (own = [(3, pos)]).
   Rule 24 (Released proofs first), checker verdict a Theorem Labs lane (role check, 22:47Z): CONFIRM "none for build A,
   by name or address: the released `check_round_trip` proofs are plain/ubsan only, 0x138ac/0x139ac, not the same bytes
   as A 0x81a9c." This file proves NO function: it holds segment lemmas of that walk, whose function-level lookup and
   CONFIRM are the walk owner's (a Theorem Labs lane, checker a Theorem Labs lane).

   The five calls (MEASURED, capstone 5.0.7 over the pinned fs.asan; return address in brackets):
     25  0x82218..0x82224  pj_write (&doc, 1)                      [0x82228]
     26  0x82228..0x82234  strlen (file) through the thunk 0x42654 [0x82238]  (FsRt.fr_strlen)
     27  0x82238..0x82244  pj_parse (file, len, &back)             [0x82248]
     28  0x82248..0x82258  pj_get (&back, "state" 0x20f00)         [0x8225c]
     29  0x8225c..0x82264  pj_get_str (r, "bytes" 0x20fc0)         [0x82268]
   F = frame_addr ly 3 pos, the class-3 fake frame (fs_frame_bytes 3 = 512): doc [0x20, 0x58), state [0x80, 0xb8),
   v [0xe0, 0x118), back [0x140, 0x178), the two size_t n at 0x1a0 and 0x1c0.

   The shared interface is lib/A/FSH_crt_base.v (crt_from, crt_INV_82218, crt_INV_82268, crt_rodata, crt_wst) and
   lib/A/FSH_crt_site.v (crt_seg_call / crt_seg_call_br / crt_hcall: one segment = a store-free run from crt_ss2 to the
   callee, then the call). Each segment here is an instance of it; c2_chain composes the five.
   lib/A/FSH_crt_segC.v does NOT build on the CTX-free S0 (line 283 names
   crt_ctx_at, which S0 f32db4da382 removed), and its engine runs start from crt_ss_ret, not crt_ss2; so this file does
   not import it, and keeps its own four small ingredients (c2_key, c2_in_bytes / c2_in_state, the c2_fpsub lemmas).

   rule 24: proves no function (kind: segment lemma of check_round_trip's walk, PORTED from d25a984c903
   check_round_trip_sd15.v / check_round_trip_sd16.v / check_round_trip_stdefs.v St14 / St15 / St16). That branch
   (a working branch) holds a bespoke ASan proof of these same bytes (0x81a9c) in the AsanAllocAPI
   framework; this file keeps its route, its boundary contents and its premise discharges, restated in the lane's
   ajournal / crt_from framework, which is the one FSH_crt_base.v fixes. The function-level lookup and its CONFIRM
   are the walk owner's (a Theorem Labs lane, checker a Theorem Labs lane). *)
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
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_ret FSW_K3 FSH_Fn_reader
FSH_Fn_writer FSH_Fn_crt FSW_frame FSW_frame3 FSW_rres FSW_rd FSW_crt_tbl FSW_strkit FSH_crt_base FSH_crt_site.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AF0x FSH_crt_room.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterSpecFacts HState B64Canon
  ReaderRes pj_set_c PjStruct check_round_trip_st8 check_round_trip_stages_b.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree PjGrammar PjRoundTrip.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (S0): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= the group's boundary states (FSH_crt_base.crt_ss_ret at each return address) ================= *)
Definition c2_ss_218 : sstate := crt_ss_ret 0x82218 crt_cs1 crt_csF.   (* return of the last pj_set *)
Definition c2_ss_228 : sstate := crt_ss_ret 0x82228 crt_cs1 crt_csF.   (* return of pj_write *)
Definition c2_ss_238 : sstate := crt_ss_ret 0x82238 crt_cs1 crt_csF.   (* return of the strlen thunk *)
Definition c2_ss_248 : sstate := crt_ss_ret 0x82248 crt_cs1 crt_csF.   (* return of pj_parse *)
Definition c2_ss_25c : sstate := crt_ss_ret 0x8225c crt_cs1 crt_csF.   (* return of pj_get *)
Definition c2_ss_268 : sstate := crt_ss_ret 0x82268 crt_cs1 crt_csF.   (* return of pj_get_str: the exit *)


(* ================= the image keys of segment group C2 =================
   The two read-only strings the group passes (FS_RO_STRS entries): "state" 0x20f00 (pj_get's key at 0x82258) and
   "bytes" 0x20fc0 (pj_get_str's key at 0x82264). At every state of the walk each is cstr_ok on the machine's memory
   (FSW_strkit.cstr_ok_kept_tbl from the image facts IMG, ARU and the read-only image crt_rodata carries) and
   cstr_kept by its table arm. *)
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis IMG : fs_img_facts tfibsegs B.
Lemma c2_key : forall cx k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3 p l,
  crt_base B cx ->
  @ajournal rc SK tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 ->
  In (p, l) FS_RO_STRS ->
  cstr_ok tfibsegs W3 (ms_mem ms3) p l /\ cstr_kept B ly3 S3 U3 p l.
Proof.
intros cx k ly3 S3 U3 W3 ms3 md3 p l HB HJ HARU3 Hin. split.
- exact (cstr_ok_kept_tbl B ly3 S3 U3 W3 (ms_mem ms3) md3 p l IMG HARU3
    (crt_rodata SK B cx k ly3 S3 U3 W3 ms3 md3 HB HJ HARU3) (or_introl Hin)).
- right. left. exact Hin.
Qed.
End k.
Lemma c2_in_bytes : In (0x20fc0, [98; 121; 116; 101; 115]) FS_RO_STRS.
Proof. unfold FS_RO_STRS. cbn [In]. repeat (first [left; reflexivity | right]). Qed.
Lemma c2_in_state : In (0x20f00, [115; 116; 97; 116; 101]) FS_RO_STRS.
Proof. unfold FS_RO_STRS. cbn [In]. repeat (first [left; reflexivity | right]). Qed.

(* ================= the FP relation of each call (FSW_K3.fsw_fp_sub, the after-call's four arms) ================= *)
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Lemma c2_fpsub_static : forall ly S lyc Sc own, fsw_fp_sub B ly S lyc Sc own FS_PSTAT_FP FS_PSTAT_FP.
Proof. intros ly S lyc Sc own a Ha. right; right; left. split; [exact Ha | exact (crt_pstat_img a Ha)]. Qed.
Lemma c2_fpsub_nil : forall ly S lyc Sc own FP, fsw_fp_sub B ly S lyc Sc own FP [].
Proof. intros ly S lyc Sc own FP a Ha. exfalso. exact (inFP_nil a Ha). Qed.
(* one object of crt's frame (pj_parse's out = F + 0x140), then the statics *)
Lemma c2_fpsub_obj : forall ly S lyc Sc pos off,
  0 <= off -> off + 56 <= 512 ->
  fsw_fp_sub B ly S lyc Sc [(3, pos)] FS_PSTAT_FP
    ([(frame_addr lyc 3 pos + off, frame_addr lyc 3 pos + off + 56)] ++ FS_PSTAT_FP).
Proof.
intros ly S lyc Sc pos off H0 H1 a Ha. apply inFP_app in Ha as [Ha | Ha].
- right; right; right; left. apply inFP_cons in Ha as [Ha | Ha]; [|exfalso; exact (inFP_nil a Ha)].
  exists 3, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite crt_frame3. lia.
- exact (c2_fpsub_static ly S lyc Sc [(3, pos)] a Ha).
Qed.
End f.


(* ================= the four INNER boundary invariants of segment group C2 =================
   One `c2_INV_<pc>` per boundary strictly inside the group (0x82218 is the base's crt_INV_82218, C1's text; 0x82268
   is the base's crt_INV_82268). Each is the document / buffer state the program holds at that pc, ported from the
   bespoke ASan proof d25a984c903: check_round_trip_stdefs.v St15 (0x82228, after pj_write: the written text joins
   the holdings) and St16 (0x82238, at pj_parse: file in s6 = x22 and a0, its length in a1, &back in a2 = x18),
   with the two boundaries St16's own proof (check_round_trip_sd16.v crt16_runA) crosses inside pj_get / pj_get_str
   stated here as 0x82248 and 0x8225c.
   The register facts are the boundary env's atoms 10 .. 27 (after a call the env is Ereg regs' (crt_extra cx), so
   atom n < 32 is register n). The budgets: the two boundaries before pj_parse carry pj_write's BY-TRACE terms on top of
   crt_INV_82218's (K_82218 + wev0 (crt_wst cx), CNT_82218 + wcalls (crt_wst cx), LIVE_82218 + the file's block), which
   with crt_room_C2 (FSH_crt_room.crt_room_C2_holds) give pj_parse's room; the two after carry the base's by-trace
   K_82268 / CNT_82268 / LIVE_82268, which are the exit's three bounds. ================= *)
Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.


(* ---- 0x82228, the return of pj_write: the document still stands in the frame, and the written text (file, nfile)
   has joined the holdings; a0 is pj_write's answer, which the four instructions 0x82228..0x82234 test and keep ---- *)
Definition c2_INV_82228 : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  let mem := ms_mem ms3 in let F := crt_F cx in let len := Z.of_nat (length (c_bs cx)) in
  let tb2 := WriterSpec.b64_enc (c_bs cx) in
  ew E 18 = Z_to_bv 64 (c_text cx) /\ ew E 20 = Z_to_bv 64 len /\ ew E 21 = Z_to_bv 64 (c_bd cx) /\
  ew E 22 = Z_to_bv 64 (F + 0xe0) /\ ew E 23 = Z_to_bv 64 (F + 0x80) /\ ew E 26 = Z_to_bv 64 (F + 0x20) /\
  ew E 27 = Z_to_bv 64 (F + 0x1a0) /\
  (exists (same nsame back file nfile : Z) (Ddoc : list (Z * Z)) (live peak cnt : Z),
     ew E 24 = Z_to_bv 64 same /\ ew E 25 = Z_to_bv 64 back /\ ew E 10 = Z_to_bv 64 file /\ file <> 0 /\
     Permutation (ablocks B ly3 S3)
       (ablocks B (c_ly cx) (c_S cx) ++
        [(c_text cx - HEAD, FSH_Fn_writer.enc_size len + HEAD); (c_want cx, FSH_Fn_writer.enc_size len);
         (same, nsame); (back - HEAD, FSH_Fn_writer.dec_size tb2 + HEAD); (file - HEAD, nfile + HEAD)] ++
        rd_hblocks Ddoc) /\
     Permutation U3 (c_U cx ++ [(c_text cx - HEAD, HEAD); (back - HEAD, HEAD); (file - HEAD, HEAD)] ++
        rd_heads Ddoc) /\
     FSupoisonU.fs_heads B ly3 S3 U3 /\
     fs_rblock tfibsegs B ly3 S3 W3 mem (c_text cx) (FSH_Fn_writer.enc_size len) /\
     fs_rblock tfibsegs B ly3 S3 W3 mem back (FSH_Fn_writer.dec_size tb2) /\
     zbytes_at tfibsegs W3 mem back (c_bs cx) /\
     (* pj_write's own post (FSH_Fn_writer.pjw_succ at the document and pretty = 1) *)
     fs_rblock tfibsegs B ly3 S3 W3 mem file nfile /\
     zbytes_at tfibsegs W3 mem file (WriterValue.wdoc (PjTree.JObj (check_round_trip_stages_b.crt_doc tb2)) true ++ [0]) /\
     Z.of_nat (length (WriterValue.wdoc (PjTree.JObj (check_round_trip_stages_b.crt_doc tb2)) true)) < nfile /\
     4096 + HEAD <= file /\
     rtree tfibsegs B ly3 S3 W3 mem (F + 0x20) (PjTree.JObj (check_round_trip_stages_b.crt_doc tb2)) Ddoc /\
     pobj tfibsegs B ly3 S3 W3 mem (F + 0x20) /\ pobj tfibsegs B ly3 S3 W3 mem (F + 0x140) /\
     val_mem tfibsegs (mrestrict (w_H W3) mem) (F + 0x1a0) 8 0 /\
     range_addressable (aview tfibsegs (w_H W3) mem) SHADOW_OFF (F + 0x1a0) 8 /\
     live = c_live cx + FSH_Fn_writer.enc_size len + FSH_Fn_writer.dec_size tb2 + nfile + rd_sum Ddoc /\
     fs_glob tfibsegs W3 mem live peak cnt SIZE_MAXZ /\
     nfile = WriterApp.w_cap (crt_wst cx) /\
     blocks_bytes S3 <= blocks_bytes (c_S cx) + LIVE_82218 cx + (nfile + HEAD) /\
     c_cnt cx <= cnt <= c_cnt cx + CNT_82218 cx + FSH_Fn_writer.wcalls (crt_wst cx) /\
     k <= K_82218 cx + FSH_Fn_writer.wev0 (crt_wst cx)).

(* ---- 0x82238, the return of the strlen thunk: s2 = x18 is now &back = F + 0x140 (the `ld s2, 0x18(s1)` of
   0x82228..0x82234), s6 = x22 is file, and a0 is |wdoc| (the thunk's answer) ---- *)
Definition c2_INV_82238 : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  let mem := ms_mem ms3 in let F := crt_F cx in let len := Z.of_nat (length (c_bs cx)) in
  let tb2 := WriterSpec.b64_enc (c_bs cx) in
  let wd := WriterValue.wdoc (PjTree.JObj (check_round_trip_stages_b.crt_doc tb2)) true in
  ew E 18 = Z_to_bv 64 (F + 0x140) /\ ew E 20 = Z_to_bv 64 len /\ ew E 21 = Z_to_bv 64 (c_bd cx) /\
  ew E 23 = Z_to_bv 64 (F + 0x80) /\ ew E 26 = Z_to_bv 64 (F + 0x20) /\ ew E 27 = Z_to_bv 64 (F + 0x1a0) /\
  (exists (same nsame back file nfile : Z) (Ddoc : list (Z * Z)) (live peak cnt : Z),
     ew E 22 = Z_to_bv 64 file /\ ew E 24 = Z_to_bv 64 same /\ ew E 25 = Z_to_bv 64 back /\
     ew E 10 = Z_to_bv 64 (Z.of_nat (length wd)) /\ file <> 0 /\
     Permutation (ablocks B ly3 S3)
       (ablocks B (c_ly cx) (c_S cx) ++
        [(c_text cx - HEAD, FSH_Fn_writer.enc_size len + HEAD); (c_want cx, FSH_Fn_writer.enc_size len);
         (same, nsame); (back - HEAD, FSH_Fn_writer.dec_size tb2 + HEAD); (file - HEAD, nfile + HEAD)] ++
        rd_hblocks Ddoc) /\
     Permutation U3 (c_U cx ++ [(c_text cx - HEAD, HEAD); (back - HEAD, HEAD); (file - HEAD, HEAD)] ++
        rd_heads Ddoc) /\
     FSupoisonU.fs_heads B ly3 S3 U3 /\
     fs_rblock tfibsegs B ly3 S3 W3 mem (c_text cx) (FSH_Fn_writer.enc_size len) /\
     fs_rblock tfibsegs B ly3 S3 W3 mem back (FSH_Fn_writer.dec_size tb2) /\
     zbytes_at tfibsegs W3 mem back (c_bs cx) /\
     fs_rblock tfibsegs B ly3 S3 W3 mem file nfile /\
     zbytes_at tfibsegs W3 mem file (wd ++ [0]) /\ Z.of_nat (length wd) < nfile /\ 4096 + HEAD <= file /\
     rtree tfibsegs B ly3 S3 W3 mem (F + 0x20) (PjTree.JObj (check_round_trip_stages_b.crt_doc tb2)) Ddoc /\
     pobj tfibsegs B ly3 S3 W3 mem (F + 0x20) /\ pobj tfibsegs B ly3 S3 W3 mem (F + 0x140) /\
     val_mem tfibsegs (mrestrict (w_H W3) mem) (F + 0x1a0) 8 0 /\
     range_addressable (aview tfibsegs (w_H W3) mem) SHADOW_OFF (F + 0x1a0) 8 /\
     live = c_live cx + FSH_Fn_writer.enc_size len + FSH_Fn_writer.dec_size tb2 + nfile + rd_sum Ddoc /\
     fs_glob tfibsegs W3 mem live peak cnt SIZE_MAXZ /\
     nfile = WriterApp.w_cap (crt_wst cx) /\
     blocks_bytes S3 <= blocks_bytes (c_S cx) + LIVE_82218 cx + (nfile + HEAD) /\
     c_cnt cx <= cnt <= c_cnt cx + CNT_82218 cx + FSH_Fn_writer.wcalls (crt_wst cx) /\
     k <= K_82218 cx + FSH_Fn_writer.wev0 (crt_wst cx)).

(* ---- 0x82248, the return of pj_parse: `back` (the frame object F + 0x140) now holds the parsed document, whose
   tree is the one pj_write wrote (pj_parse's narrow-success post), and a0 = 0 ---- *)
Definition c2_INV_82248 : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  let mem := ms_mem ms3 in let F := crt_F cx in let len := Z.of_nat (length (c_bs cx)) in
  let tb2 := WriterSpec.b64_enc (c_bs cx) in
  let wd := WriterValue.wdoc (PjTree.JObj (check_round_trip_stages_b.crt_doc tb2)) true in
  ew E 10 = Z_to_bv 64 0 /\ ew E 18 = Z_to_bv 64 (F + 0x140) /\ ew E 20 = Z_to_bv 64 len /\
  ew E 21 = Z_to_bv 64 (c_bd cx) /\ ew E 23 = Z_to_bv 64 (F + 0x80) /\ ew E 26 = Z_to_bv 64 (F + 0x20) /\
  ew E 27 = Z_to_bv 64 (F + 0x1a0) /\
  (exists (same nsame back file nfile : Z) (Ddoc Dback : list (Z * Z)) (live peak cnt : Z),
     ew E 22 = Z_to_bv 64 file /\ ew E 24 = Z_to_bv 64 same /\ ew E 25 = Z_to_bv 64 back /\
     Permutation (ablocks B ly3 S3)
       (ablocks B (c_ly cx) (c_S cx) ++
        [(c_text cx - HEAD, FSH_Fn_writer.enc_size len + HEAD); (c_want cx, FSH_Fn_writer.enc_size len);
         (same, nsame); (back - HEAD, FSH_Fn_writer.dec_size tb2 + HEAD); (file - HEAD, nfile + HEAD)] ++
        rd_hblocks (Ddoc ++ Dback)) /\
     Permutation U3 (c_U cx ++ [(c_text cx - HEAD, HEAD); (back - HEAD, HEAD); (file - HEAD, HEAD)] ++
        rd_heads (Ddoc ++ Dback)) /\
     FSupoisonU.fs_heads B ly3 S3 U3 /\
     fs_rblock tfibsegs B ly3 S3 W3 mem (c_text cx) (FSH_Fn_writer.enc_size len) /\
     fs_rblock tfibsegs B ly3 S3 W3 mem back (FSH_Fn_writer.dec_size tb2) /\
     zbytes_at tfibsegs W3 mem back (c_bs cx) /\
     fs_rblock tfibsegs B ly3 S3 W3 mem file nfile /\
     zbytes_at tfibsegs W3 mem file (wd ++ [0]) /\ Z.of_nat (length wd) < nfile /\ 4096 + HEAD <= file /\
     rtree tfibsegs B ly3 S3 W3 mem (F + 0x20) (PjTree.JObj (check_round_trip_stages_b.crt_doc tb2)) Ddoc /\
     rnode tfibsegs B ly3 S3 W3 mem (Ddoc ++ Dback) (F + 0x140)
       (PjTree.JObj (check_round_trip_stages_b.crt_doc tb2)) Dback /\
     pobj tfibsegs B ly3 S3 W3 mem (F + 0x140) /\ pobj tfibsegs B ly3 S3 W3 mem (F + 0x20) /\
     val_mem tfibsegs (mrestrict (w_H W3) mem) (F + 0x1a0) 8 0 /\
     range_addressable (aview tfibsegs (w_H W3) mem) SHADOW_OFF (F + 0x1a0) 8 /\
     live = c_live cx + FSH_Fn_writer.enc_size len + FSH_Fn_writer.dec_size tb2 + nfile + rd_sum (Ddoc ++ Dback) /\
     fs_glob tfibsegs W3 mem live peak cnt SIZE_MAXZ /\
     blocks_bytes S3 <= blocks_bytes (c_S cx) + LIVE_82268 cx /\
     c_cnt cx <= cnt <= c_cnt cx + CNT_82268 cx /\
     k <= K_82218 cx + FSH_Fn_writer.wev0 (crt_wst cx) + rd_ev (crt_TR cx) /\
     (length Dback <= length (crt_TR cx))%nat).

(* ---- 0x8225c, the return of pj_get: a0 is the "state" member of the parsed document, a node of its kids block
   (rd_get_res's hit arm), so it is a tree node of the state object with its own blocks Dz ---- *)
Definition c2_INV_8225c : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  let mem := ms_mem ms3 in let F := crt_F cx in let len := Z.of_nat (length (c_bs cx)) in
  let tb2 := WriterSpec.b64_enc (c_bs cx) in
  let wd := WriterValue.wdoc (PjTree.JObj (check_round_trip_stages_b.crt_doc tb2)) true in
  ew E 18 = Z_to_bv 64 (F + 0x140) /\ ew E 20 = Z_to_bv 64 len /\
  ew E 21 = Z_to_bv 64 (c_bd cx) /\ ew E 23 = Z_to_bv 64 (F + 0x80) /\ ew E 26 = Z_to_bv 64 (F + 0x20) /\
  ew E 27 = Z_to_bv 64 (F + 0x1a0) /\
  (exists (same nsame back file nfile z : Z) (Ddoc Dback Dz : list (Z * Z)) (live peak cnt : Z),
     ew E 22 = Z_to_bv 64 file /\ ew E 24 = Z_to_bv 64 same /\ ew E 25 = Z_to_bv 64 back /\
     ew E 10 = Z_to_bv 64 z /\ z <> 0 /\
     Permutation (ablocks B ly3 S3)
       (ablocks B (c_ly cx) (c_S cx) ++
        [(c_text cx - HEAD, FSH_Fn_writer.enc_size len + HEAD); (c_want cx, FSH_Fn_writer.enc_size len);
         (same, nsame); (back - HEAD, FSH_Fn_writer.dec_size tb2 + HEAD); (file - HEAD, nfile + HEAD)] ++
        rd_hblocks (Ddoc ++ Dback)) /\
     Permutation U3 (c_U cx ++ [(c_text cx - HEAD, HEAD); (back - HEAD, HEAD); (file - HEAD, HEAD)] ++
        rd_heads (Ddoc ++ Dback)) /\
     FSupoisonU.fs_heads B ly3 S3 U3 /\
     fs_rblock tfibsegs B ly3 S3 W3 mem (c_text cx) (FSH_Fn_writer.enc_size len) /\
     fs_rblock tfibsegs B ly3 S3 W3 mem back (FSH_Fn_writer.dec_size tb2) /\
     zbytes_at tfibsegs W3 mem back (c_bs cx) /\
     fs_rblock tfibsegs B ly3 S3 W3 mem file nfile /\
     zbytes_at tfibsegs W3 mem file (wd ++ [0]) /\ Z.of_nat (length wd) < nfile /\ 4096 + HEAD <= file /\
     rtree tfibsegs B ly3 S3 W3 mem (F + 0x20) (PjTree.JObj (check_round_trip_stages_b.crt_doc tb2)) Ddoc /\
     rnode tfibsegs B ly3 S3 W3 mem (Ddoc ++ Dback) (F + 0x140)
       (PjTree.JObj (check_round_trip_stages_b.crt_doc tb2)) Dback /\
     (* pj_get's answer: the state object, a node inside back's kids block, with its own blocks (rd_get_hit's
        incl Di D at D = Dback) *)
     rnode tfibsegs B ly3 S3 W3 mem (Ddoc ++ Dback) z
       (PjTree.JObj (check_round_trip_stages_b.crt_st tb2)) Dz /\
     pobj tfibsegs B ly3 S3 W3 mem z /\ incl Dz Dback /\
     pobj tfibsegs B ly3 S3 W3 mem (F + 0x140) /\ pobj tfibsegs B ly3 S3 W3 mem (F + 0x20) /\
     val_mem tfibsegs (mrestrict (w_H W3) mem) (F + 0x1a0) 8 0 /\
     range_addressable (aview tfibsegs (w_H W3) mem) SHADOW_OFF (F + 0x1a0) 8 /\
     live = c_live cx + FSH_Fn_writer.enc_size len + FSH_Fn_writer.dec_size tb2 + nfile + rd_sum (Ddoc ++ Dback) /\
     fs_glob tfibsegs W3 mem live peak cnt SIZE_MAXZ /\
     blocks_bytes S3 <= blocks_bytes (c_S cx) + LIVE_82268 cx /\
     c_cnt cx <= cnt <= c_cnt cx + CNT_82268 cx /\
     k <= K_82218 cx + FSH_Fn_writer.wev0 (crt_wst cx) + rd_ev (crt_TR cx) /\
     (length Dback <= length (crt_TR cx))%nat).
End i.


(* ================= cstr_ok for a string that lives in a reader block =================
   The kit only KEEPS a cstr_ok (FSW_strkit.cstr_ok_kept_blk / _blkU / _keptU / _tbl); this BUILDS one, from the block
   and its bytes: crt_INV_82268's `cstr_ok z zs` (out of pj_get_str's post, pj_cstr + In (z, n) D) and the strlen
   argument at 0x82234 (pj_write's file). All eight conjuncts of S0's cstr_ok (FSH_Gen.v, its eighth
   `p + |l| + 1 <= alloc_ceiling`, a Theorem Labs lane 2d9cdf6a160) follow from the block. ================= *)
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Lemma cstr_ok_of_rblockU : forall ly S U (W : world tfibsegs) mem md z n (s : list Z),
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U ->
  fs_rblock tfibsegs B ly S W mem z n -> Z.of_nat (length s) + 1 <= n ->
  garr8 tfibsegs (mrestrict (w_H W) mem) z (s ++ [0]) -> Forall (fun c => c <> 0) s ->
  cstr_ok tfibsegs W mem z s.
Proof.
intros ly S U W mem md z n s HARU HH HB Hlen Hg Hnz.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HARU as (HAR & OKU & POU).
pose proof HB as (Hin & Hal & Hn & Hv).
assert (Hrq : req_size (n + HEAD) = n + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (n + 16) 0); lia).
destruct (al_blocks tfibsegs B LAWS ly S W (unpoison U mem) md (z - HEAD) (n + HEAD) HAR Hin)
  as (_ & H4096 & Hceil2 & Happ & _ & _ & Hmm).
rewrite Hrq in Hceil2, Happ.
assert (HMM : MALLOC_MAX <= 2 ^ 32) by (apply Z.leb_le; vm_compute; reflexivity).
split; [split; [exact Hg | exact Hnz]|].
split; [unfold HEAD in H4096; lia|].
split; [unfold HEAD in Hceil2; lia|].
split; [unfold HEAD in Hmm; lia|].
split.
{ unfold in_app in Happ. destruct Happ as (_ & [Hlow | (Hhi1 & Hhi2)]).
  - unfold amem_range. left. unfold kLowShadowBeg, kLowMemEnd, HEAD in *. lia.
  - unfold amem_range. right. unfold kHighMemBeg, HEAD, ASAN_CEIL in *. split; [lia | lia]. }
split.
{ apply (fsw_block_body_addressable B ly S U W mem md (z - HEAD) (n + HEAD) z (Z.of_nat (length s) + 1) HARU HH Hin);
    [unfold HEAD; lia | lia | rewrite Hrq; unfold HEAD; lia]. }
split.
{ destruct (al_shadow tfibsegs B LAWS ly S W (unpoison U mem) md (z - HEAD) (n + HEAD) HAR Hin) as (_ & Hh).
  assert (Hsub : shadow_hull_vis (aview tfibsegs (w_H W) (unpoison U mem)) z (Z.of_nat (length s) + 1)).
  { apply (shadow_hull_vis_sub _ (z - HEAD) (req_size (n + HEAD)) z (Z.of_nat (length s) + 1) Hh);
      [unfold HEAD; lia | rewrite Hrq; unfold HEAD; lia | lia]. }
  intros x Hx. exact (aview_unpoison_vis U W mem x POU (Hsub x Hx)). }
intros a Ha.
apply (aview_unpoison_vis U W mem a POU).
apply (block_word_tail_vis B ly S W (unpoison U mem) md (z - HEAD) (n + HEAD) HAR Hin ltac:(unfold HEAD; lia)).
pose proof (word_end_mono (z + Z.of_nat (length s)) (z - HEAD + (n + HEAD) - 1) ltac:(unfold HEAD; lia)) as Hw.
unfold HEAD in *. lia.
Qed.
End g.

(* ================= helpers of segment group C2's call crossings ================= *)
(* the s-register atoms a call keeps: after the call the boundary env is Ereg regs' (crt_extra cx), and a callee-saved
   register the run left as its entry atom still holds that atom's value *)
Lemma c2_keep_s : forall E (ssC : sstate) regsC regs' extra n,
  (forall rr : bv 5, YK11.getr regsC rr = sv_denot E (sr_get (ss_regs ssC) rr)) ->
  aregs_preserved regsC regs' -> acallee_saved (Z.of_nat n) ->
  sr_get (ss_regs ssC) (Z_to_bv 5 (Z.of_nat n)) = SOff n 0 ->
  ew (Ereg regs' extra) n = ew E n.
Proof.
intros E ssC regsC regs' extra n RG HP Hc Hr.
assert (Hn : Z.of_nat n = bv_unsigned (Z_to_bv 5 (Z.of_nat n))).
{ rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|].
  change (bv_modulus 5) with 32. unfold acallee_saved in Hc. lia. }
rewrite (ew_Ereg_nat regs' extra n _ Hn), (HP _ Hc), RG, Hr. apply fsw_SOff0.
Qed.
(* a one-byte val_mem is the byte itself *)
Lemma c2_le_byte1 : forall v, 0 <= v < 256 -> le_byte v 1 0 = v.
Proof.
intros v Hv. unfold le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r, (Z.mod_small v 256) by lia. apply Z.mod_small. lia.
Qed.
(* pj_get_str's string bytes (PjStruct.pj_cbytes) as the walk reads them *)
Lemma c2_garr8_of_cbytes : forall m a s, PjStruct.pj_cbytes tfibsegs m a s ->
  garr8 tfibsegs m a (s ++ [0]) /\ Forall (fun c => c <> 0) s.
Proof.
intros m a s (HF & _ & _ & HB). split.
- intros j Hj.
  assert (Hr : 0 <= nth j (s ++ [0]) 0 < 256).
  { destruct (Nat.lt_ge_cases j (length s)) as [Hl | Hl].
    - rewrite app_nth1 by exact Hl. rewrite Forall_forall in HF. pose proof (HF (nth j s 0) (nth_In s 0 Hl)). lia.
    - rewrite length_app in Hj. cbn [length] in Hj. rewrite app_nth2 by exact Hl.
      replace (j - length s)%nat with 0%nat by lia. cbn. lia. }
  split; [|exact Hr].
  intros k Hk. assert (k = 0%nat) as -> by lia. change (Z.of_nat 0) with 0. rewrite Z.add_0_r, c2_le_byte1 by exact Hr.
  pose proof (HB j ltac:(rewrite length_map; exact Hj)) as Hb.
  rewrite nth_error_map, (nth_error_nth' (s ++ [0]) 0 Hj) in Hb. exact Hb.
- eapply Forall_impl; [|exact HF]. intros c Hc. cbv beta in *. lia.
Qed.
(* the second decode's block holds the body: |bs| <= dec_size (b64_enc bs) *)
Lemma c2_bs_dec : forall bs : list Z, Z.of_nat (length bs) <= FSH_Fn_writer.dec_size (WriterSpec.b64_enc bs).
Proof.
intros bs. unfold FSH_Fn_writer.dec_size. rewrite WriterSpecFacts.b64_enc_length.
rewrite Nat2Z.inj_mul, Nat2Z.inj_div, Nat2Z.inj_add.
change (Z.of_nat 2) with 2. change (Z.of_nat 3) with 3. change (Z.of_nat 4) with 4.
Z.div_mod_to_equations. lia.
Qed.
Lemma c2_rq : forall n, 0 < n -> req_size (n + HEAD) = n + HEAD.
Proof. intros n Hn. unfold req_size, HEAD. destruct (Z.eqb_spec (n + 16) 0); lia. Qed.
(* the "bytes" member of the state object is its third, the base64 text *)
Lemma c2_st_bytes : forall es i v,
  nth_error (check_round_trip_stages_b.crt_st es) i = Some ([98; 121; 116; 101; 115], v) -> v = PjTree.JStr es.
Proof.
intros es i v H. unfold check_round_trip_stages_b.crt_st in H.
destruct i as [|[|[|i]]]; cbn [nth_error] in H.
- cbv [check_round_trip_stages_b.K_ENCODING] in H. discriminate H.
- cbv [check_round_trip_stages_b.K_CONTEXT] in H. discriminate H.
- injection H as H. symmetry. exact H.
- destruct i; cbn [nth_error] in H; discriminate H.
Qed.
Lemma c2_st_has_bytes : forall es, In ([98; 121; 116; 101; 115], PjTree.JStr es) (check_round_trip_stages_b.crt_st es).
Proof. intros es. unfold check_round_trip_stages_b.crt_st. right; right; left. reflexivity. Qed.
(* the parsed document has depth 2 (the state object's strings at depth 2) *)
Lemma c2_depth : forall es, (PjTree.depth (PjTree.JObj (check_round_trip_stages_b.crt_doc es)) <= 2)%nat.
Proof. intros es. cbn. lia. Qed.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.

(* ---- what a callee's journal keeps (raw memories): a block's bytes, a frame's bytes, a frame's shadow ---- *)
Lemma c2_garr8_kept_blk : forall STK1 sp1 FP1 lyc Sc Uc (W : world tfibsegs) memc mdc ly' S' U' (W' : world tfibsegs)
  mem' md' kc P N p l,
  @ajournal rc SK tfibsegs B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memc mdc -> upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  In (P, N) (ablocks B lyc Sc) -> P <= p -> p + Z.of_nat (length l) <= P + req_size N ->
  (forall x, p <= x < p + Z.of_nat (length l) -> ~ inFP FP1 x) ->
  garr8 tfibsegs (mrestrict (w_H W) memc) p l -> garr8 tfibsegs (mrestrict (w_H W') mem') p l.
Proof.
intros STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc P N p l HJ HU HO' HP' Hin H1 H2 HF Hg j Hj.
destruct (Hg j Hj) as (Hv & Hr). split; [|exact Hr].
intros k Hk. pose proof (Hv k Hk) as Hv0. assert (k = 0%nat) as -> by lia. unfold mbyte in *.
rewrite (proj2 (fsw_journal_kept_byte B STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc
  (p + Z.of_nat j + Z.of_nat 0) HJ HU HO' HP' ltac:(left; exists P, N; split; [exact Hin | lia]) ltac:(apply HF; lia))).
exact Hv0.
Qed.
Lemma c2_val_kept_frame : forall STK1 sp1 FP1 lyc Sc Uc (W : world tfibsegs) memc mdc ly' S' U' (W' : world tfibsegs)
  mem' md' kc cid pos a (n : nat) v,
  @ajournal rc SK tfibsegs B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memc mdc -> upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  In (cid, pos) (frames Sc) -> frame_addr lyc cid pos <= a ->
  a + Z.of_nat n <= frame_addr lyc cid pos + fs_frame_bytes cid ->
  (forall x, a <= x < a + Z.of_nat n -> ~ inFP FP1 x) ->
  val_mem tfibsegs (mrestrict (w_H W) memc) a n v -> val_mem tfibsegs (mrestrict (w_H W') mem') a n v.
Proof.
intros STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc cid pos a n v HJ HU HO' HP' Hin H1 H2 HF Hv k Hk.
pose proof (Hv k Hk) as Hv0. unfold mbyte in *.
rewrite (proj2 (fsw_journal_kept_byte B STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc
  (a + Z.of_nat k) HJ HU HO' HP' ltac:(right; exists cid, pos; split; [exact Hin | lia]) ltac:(apply HF; lia))).
exact Hv0.
Qed.
Lemma c2_ra_kept_frame : forall STK1 sp1 FP1 lyc Sc Uc (W : world tfibsegs) memc mdc ly' S' U' (W' : world tfibsegs)
  mem' md' kc cid pos p n,
  @ajournal rc SK tfibsegs B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memc mdc -> upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  (forall a, inFP FP1 a -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) -> FSupoisonU.fs_heads B ly' S' U' ->
  In (cid, pos) (frames Sc) -> frame_addr lyc cid pos <= p -> p + n <= frame_addr lyc cid pos + fs_frame_bytes cid ->
  range_addressable (aview tfibsegs (w_H W) memc) SHADOW_OFF p n ->
  range_addressable (aview tfibsegs (w_H W') mem') SHADOW_OFF p n.
Proof.
intros STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc cid pos p n HJ HU HO' HP' HFsh HH Hin H1 H2 Hra x Hx.
pose proof HU as (_ & _ & HPUc).
destruct (Hra x Hx) as (sv & Esv & Hok). exists sv. split; [|exact Hok].
rewrite <- Esv.
apply (fsw_journal_kept_shadow B STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc x HJ HU HO' HP' HFsh HH).
- right. exists cid, pos. split; [exact Hin | lia].
- destruct (in_ush Uc (shadow_of_addr SHADOW_OFF x)) eqn:E; [|reflexivity]. exfalso.
  pose proof (HPUc _ E) as E247. rewrite Esv in E247. injection E247 as ->. unfold saddr_ok in Hok. lia.
Qed.
(* ---- the same, across a store-free run (same_below alloc_ceiling) ---- *)
Lemma c2_garr8_below : forall (H : word -> bool) m m' p l, same_below m m' alloc_ceiling -> 0 <= p ->
  p + Z.of_nat (length l) <= alloc_ceiling -> garr8 tfibsegs (mrestrict H m) p l -> garr8 tfibsegs (mrestrict H m') p l.
Proof.
intros H m m' p l Hs H0 H1 Hg j Hj. destruct (Hg j Hj) as (Hv & Hr). split; [|exact Hr].
apply (val_mem_below H m m' alloc_ceiling (p + Z.of_nat j) 1 _ Hs); [lia | lia | exact Hv].
Qed.
End h.

(* ================= the boundary data every C2 boundary from 0x82228 on carries, and its two transports =================
   c2_dat0: text's and back's blocks, back's bytes (bs), the document tree at doc = F + 0x20 and its object, the n cell
   at F + 0x1a0 (value 0, addressable). c2_datf: pj_write's file (its block and the written text with its NUL). Both are
   kept by a store-free run (same_below alloc_ceiling) and by a call whose footprint is image bytes or back's object
   [F + 0x140, F + 0x178) (pj_get / pj_get_str: [], pj_write: the statics, pj_parse: back and the statics). *)
Lemma c2_img_range : forall a, in_img tfibsegs a -> 0 <= a < 0x5fd000.
Proof.
intros a (sg & Hin & Hr).
assert (Hx : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x5fd000) tfibsegs = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in Hx. pose proof (Hx sg Hin) as Hs. apply Z.leb_le in Hs. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

Definition c2_dat0 (cx : crt_cx) ly S (W : world tfibsegs) mem (back : Z) (Ddoc : list (Z * Z)) : Prop :=
  fs_rblock tfibsegs B ly S W mem (c_text cx) (FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx)))) /\
  fs_rblock tfibsegs B ly S W mem back (FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx))) /\
  zbytes_at tfibsegs W mem back (c_bs cx) /\
  rtree tfibsegs B ly S W mem (crt_F cx + 0x20)
    (PjTree.JObj (check_round_trip_stages_b.crt_doc (WriterSpec.b64_enc (c_bs cx)))) Ddoc /\
  pobj tfibsegs B ly S W mem (crt_F cx + 0x20) /\
  val_mem tfibsegs (mrestrict (w_H W) mem) (crt_F cx + 0x1a0) 8 0 /\
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF (crt_F cx + 0x1a0) 8.
Definition c2_datf (cx : crt_cx) ly S (W : world tfibsegs) mem (file nfile : Z) : Prop :=
  let wd := WriterValue.wdoc (PjTree.JObj (check_round_trip_stages_b.crt_doc (WriterSpec.b64_enc (c_bs cx)))) true in
  fs_rblock tfibsegs B ly S W mem file nfile /\ zbytes_at tfibsegs W mem file (wd ++ [0]) /\
  Z.of_nat (length wd) < nfile.

Lemma c2_dat0_below : forall cx ly S (W : world tfibsegs) mx md m m' back Ddoc,
  AR tfibsegs B ly S W mx md -> same_below m m' alloc_ceiling ->
  4096 <= crt_F cx -> crt_F cx + 512 <= alloc_ceiling ->
  c2_dat0 cx ly S W m back Ddoc -> c2_dat0 cx ly S W m' back Ddoc.
Proof.
intros cx ly S W mx md m m' back Ddoc HAR HSB HF1 HF2 (Rt & Rb & Zb & Ht & Hpd & Hv & Hra).
destruct (fsw_rblock_low B ly S W mx md m back _ HAR Rb) as (Lb1 & Lb2).
pose proof (c2_bs_dec (c_bs cx)) as Lbs.
assert (HEADv : HEAD = 16) by reflexivity.
split; [exact (fs_rblock_below B ly S W mx md m m' _ _ HAR HSB Rt)|].
split; [exact (fs_rblock_below B ly S W mx md m m' _ _ HAR HSB Rb)|].
split; [exact (c2_garr8_below (w_H W) m m' back (c_bs cx) HSB ltac:(lia) ltac:(lia) Zb)|].
split; [exact (rnode_below B ly S W mx md m m' Ddoc (crt_F cx + 0x20) _ Ddoc HAR HSB ltac:(lia) ltac:(lia) Ht)|].
split; [exact (pobj_below B ly S W mx md m m' _ HAR HSB Hpd)|].
split; [exact (val_mem_below (w_H W) m m' alloc_ceiling (crt_F cx + 0x1a0) 8 0 HSB ltac:(lia)
  ltac:(change (Z.of_nat 8) with 8; lia) Hv)|].
exact (fsw_range_addressable_below (w_H W) m m' (crt_F cx + 0x1a0) 8 HSB ltac:(lia) ltac:(lia) Hra).
Qed.
Lemma c2_datf_below : forall cx ly S (W : world tfibsegs) mx md m m' file nfile,
  AR tfibsegs B ly S W mx md -> same_below m m' alloc_ceiling ->
  c2_datf cx ly S W m file nfile -> c2_datf cx ly S W m' file nfile.
Proof.
intros cx ly S W mx md m m' file nfile HAR HSB (Rf & Zf & Hwd).
destruct (fsw_rblock_low B ly S W mx md m file _ HAR Rf) as (L1 & L2).
assert (HEADv : HEAD = 16) by reflexivity.
split; [exact (fs_rblock_below B ly S W mx md m m' _ _ HAR HSB Rf)|].
split; [|exact Hwd].
apply (c2_garr8_below (w_H W) m m' file _ HSB ltac:(lia)); [rewrite length_app; cbn [length]; lia | exact Zf].
Qed.

(* the footprints the group's calls write: image bytes, and back's object at the pj_parse call *)
Definition c2_fpok (cx : crt_cx) (FP1 : list (Z * Z)) : Prop :=
  forall x, inFP FP1 x -> in_img tfibsegs x \/ crt_F cx + 0x140 <= x < crt_F cx + 0x178.
Lemma c2_fpok_nil : forall cx, c2_fpok cx [].
Proof. intros cx x Hx. exfalso. exact (inFP_nil x Hx). Qed.
Lemma c2_fpok_pstat : forall cx, c2_fpok cx FS_PSTAT_FP.
Proof. intros cx x Hx. left. exact (crt_pstat_img x Hx). Qed.
Lemma c2_fpok_back : forall cx,
  c2_fpok cx ([(crt_F cx + 0x140, crt_F cx + 0x140 + 56)] ++ FS_PSTAT_FP).
Proof.
intros cx x Hx. apply inFP_app in Hx as [Hx | Hx]; [|left; exact (crt_pstat_img x Hx)].
apply inFP_cons in Hx as [Hx | Hx]; [|exfalso; exact (inFP_nil x Hx)].
right. unfold in_zr in Hx. cbn [fst snd] in Hx. lia.
Qed.

(* what such a footprint spares: every heap block byte, and every frame byte outside back's object *)
Lemma c2_fpok_blk : forall cx FP1 ly S (W : world tfibsegs) mem md p n x,
  c2_fpok cx FP1 -> AR tfibsegs B ly S W mem md -> In (3, c_pos cx) (frames S) ->
  frame_addr ly 3 (c_pos cx) = crt_F cx ->
  In (p, n) (ablocks B ly S) -> p <= x < p + req_size n -> ~ inFP FP1 x.
Proof.
intros cx FP1 ly S W mem md p n x HFP HAR Hin3 EF Hin Hx Hf.
destruct (HFP x Hf) as [Himg | Hb].
- exact (blk_img tfibsegs B LAWS ly S W mem md p n x HAR Hin Hx Himg).
- pose proof (sep_block_frame tfibsegs B LAWS ly S W mem md p n 3 (c_pos cx) HAR Hin Hin3) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EF, crt_frame3 in Hd. lia.
Qed.
Lemma c2_fpok_frm : forall cx FP1 ly S (W : world tfibsegs) mem md x,
  c2_fpok cx FP1 -> AR tfibsegs B ly S W mem md -> In (3, c_pos cx) (frames S) ->
  frame_addr ly 3 (c_pos cx) = crt_F cx ->
  crt_F cx <= x < crt_F cx + 512 -> ~ (crt_F cx + 0x140 <= x < crt_F cx + 0x178) -> ~ inFP FP1 x.
Proof.
intros cx FP1 ly S W mem md x HFP HAR Hin3 EF Hx Hnb Hf.
destruct (HFP x Hf) as [Himg | Hb]; [|exact (Hnb Hb)].
exact (frm_img tfibsegs B LAWS ly S W mem md 3 (c_pos cx) x HAR Hin3 ltac:(rewrite EF, crt_frame3; lia) Himg).
Qed.
Lemma c2_fpok_sh : forall cx FP1 ly S (W : world tfibsegs) mx md m,
  c2_fpok cx FP1 -> AR tfibsegs B ly S W mx md -> pobj tfibsegs B ly S W m (crt_F cx + 0x140) ->
  forall a, inFP FP1 a -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44).
Proof.
intros cx FP1 ly S W mx md m HFP HAR Hpb a Ha.
destruct (HFP a Ha) as [Himg | Hb].
- pose proof (c2_img_range a Himg). unfold SHADOW_OFF. lia.
- exact (fsw_pobj_off_shadow B ly S W mx md m _ HAR Hpb a ltac:(lia)).
Qed.

Lemma c2_dat0_call : forall cx STK1 sp1 FP1 lyc Sc Uc (W : world tfibsegs) memc mdc ly' S' U' (W' : world tfibsegs)
  mem' md' kc back Ddoc,
  @ajournal rc SK tfibsegs B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memc mdc -> upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  FSupoisonU.fs_heads B ly' S' U' -> c2_fpok cx FP1 ->
  In (3, c_pos cx) (frames Sc) -> frame_addr lyc 3 (c_pos cx) = crt_F cx ->
  pobj tfibsegs B lyc Sc W memc (crt_F cx + 0x140) ->
  c2_dat0 cx lyc Sc W memc back Ddoc -> c2_dat0 cx ly' S' W' mem' back Ddoc.
Proof.
intros cx STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc back Ddoc HJ HU OK' PO' HH' HFP Hin3 EF Hpb
  (Rt & Rb & Zb & Ht & Hpd & Hv & Hra).
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HU) as HAR.
assert (HEADv : HEAD = 16) by reflexivity.
pose proof (c2_bs_dec (c_bs cx)) as Lbs.
assert (AB : forall p n x, fs_rblock tfibsegs B lyc Sc W memc p n -> p - HEAD <= x < p + n -> ~ inFP FP1 x).
{ intros p n x (Hin & _ & Hn & _) Hx. apply (c2_fpok_blk cx FP1 lyc Sc W _ mdc (p - HEAD) (n + HEAD) x HFP HAR Hin3 EF Hin).
  rewrite c2_rq by exact Hn. lia. }
assert (SH := c2_fpok_sh cx FP1 lyc Sc W _ mdc memc HFP HAR Hpb).
destruct (fsw_pobj_low B lyc Sc W _ mdc memc _ HAR Hpd) as (Ld1 & Ld2).
split; [eapply (fs_rblock_kept_call B); [exact HJ | exact HU | exact OK' | exact PO' | intros x Hx; exact (AB _ _ x Rt Hx)
  | exact Rt]|].
split; [eapply (fs_rblock_kept_call B); [exact HJ | exact HU | exact OK' | exact PO' | intros x Hx; exact (AB _ _ x Rb Hx)
  | exact Rb]|].
split.
{ pose proof Rb as (Hinb & _ & Hnb & _). unfold zbytes_at.
  apply (c2_garr8_kept_blk SK B _ _ _ lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc (back - HEAD)
    (FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD) back (c_bs cx) HJ HU OK' PO' Hinb);
    [lia | rewrite c2_rq by exact Hnb; lia | intros x Hx; apply (AB _ _ x Rb); lia | exact Zb]. }
split.
{ eapply (rtree_kept_call B); [exact HJ | exact HU | exact OK' | exact PO'
  | intros x Hx; apply (c2_fpok_frm cx FP1 lyc Sc W _ mdc x HFP HAR Hin3 EF); lia
  | intros a kk x Hak Hx; destruct Ht as (_ & HBd & _); exact (AB a kk x (HBd a kk Hak) Hx) | exact Hpd | exact Ht]. }
split.
{ eapply (pobj_kept_call B); [exact HJ | exact HU | exact OK' | exact PO'
  | intros x Hx; apply (c2_fpok_frm cx FP1 lyc Sc W _ mdc x HFP HAR Hin3 EF); lia | exact SH | exact HH' | exact Hpd]. }
split.
{ apply (c2_val_kept_frame SK B _ _ _ lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc 3 (c_pos cx) (crt_F cx + 0x1a0) 8 0
    HJ HU OK' PO' Hin3); [rewrite EF; lia | rewrite EF, crt_frame3; change (Z.of_nat 8) with 8; lia
    | intros x Hx; change (Z.of_nat 8) with 8 in Hx; apply (c2_fpok_frm cx FP1 lyc Sc W _ mdc x HFP HAR Hin3 EF); lia
    | exact Hv]. }
apply (c2_ra_kept_frame SK B _ _ _ lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc 3 (c_pos cx) (crt_F cx + 0x1a0) 8
  HJ HU OK' PO' SH HH' Hin3); [rewrite EF; lia | rewrite EF, crt_frame3; lia | exact Hra].
Qed.
Lemma c2_datf_call : forall cx STK1 sp1 FP1 lyc Sc Uc (W : world tfibsegs) memc mdc ly' S' U' (W' : world tfibsegs)
  mem' md' kc file nfile,
  @ajournal rc SK tfibsegs B STK1 sp1 FP1 lyc Sc W (unpoison Uc memc) mdc [] ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memc mdc -> upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  c2_fpok cx FP1 -> In (3, c_pos cx) (frames Sc) -> frame_addr lyc 3 (c_pos cx) = crt_F cx ->
  c2_datf cx lyc Sc W memc file nfile -> c2_datf cx ly' S' W' mem' file nfile.
Proof.
intros cx STK1 sp1 FP1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc file nfile HJ HU OK' PO' HFP Hin3 EF
  (Rf & Zf & Hwd).
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HU) as HAR.
assert (HEADv : HEAD = 16) by reflexivity.
pose proof Rf as (Hinf & _ & Hnf & _).
assert (AB : forall x, file - HEAD <= x < file + nfile -> ~ inFP FP1 x).
{ intros x Hx. apply (c2_fpok_blk cx FP1 lyc Sc W _ mdc (file - HEAD) (nfile + HEAD) x HFP HAR Hin3 EF Hinf).
  rewrite c2_rq by exact Hnf. lia. }
split; [eapply (fs_rblock_kept_call B); [exact HJ | exact HU | exact OK' | exact PO' | exact AB | exact Rf]|].
split; [|exact Hwd].
unfold zbytes_at.
apply (c2_garr8_kept_blk SK B _ _ _ lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc (file - HEAD) (nfile + HEAD) file _
  HJ HU OK' PO' Hinf); [lia | rewrite c2_rq by exact Hnf; rewrite length_app; cbn [length]; lia
  | intros x Hx; apply AB; rewrite length_app in Hx; cbn [length] in Hx; lia | exact Zf].
Qed.

(* ---- a node of an object's kids array is a pobj (heap arm), and an object's i-th member lies in its kids block ---- *)
Lemma c2_pobj_kid : forall ly S U (W : world tfibsegs) mem md kids cap v,
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U ->
  fs_rblock tfibsegs B ly S W mem kids (56 * cap) -> kids <= v -> v + 56 <= kids + 56 * cap -> (v - kids) mod 8 = 0 ->
  pobj tfibsegs B ly S W mem v.
Proof.
intros ly S U W mem md kids cap v HARU HH (Hin & Hal & Hn & _) H1 H2 H8.
pose proof (c2_rq (56 * cap) Hn) as Hrq.
pose proof HARU as (HAR & _ & _).
assert (HEADv : HEAD = 16) by reflexivity.
destruct (al_blocks tfibsegs B LAWS ly S W (unpoison U mem) md (kids - HEAD) (56 * cap + HEAD) HAR Hin)
  as (_ & _ & _ & _ & Hpr & _ & _).
rewrite Hrq in Hpr.
split.
- right. split; [exists (kids - HEAD), (56 * cap + HEAD); split; [exact Hin|]; rewrite Hrq; lia|].
  split; [Z.div_mod_to_equations; lia|].
  apply (fsw_block_body_addressable B ly S U W mem md (kids - HEAD) (56 * cap + HEAD) v 56 HARU HH Hin);
    [lia | lia | rewrite Hrq; lia].
- intros i Hi. destruct (Hpr (v + i) ltac:(lia)) as (Hp & Hno).
  assert (Hp' : apresent (w_H W) mem (v + i)).
  { eapply (fsw_apresent_notowned B ly S U W mem md (v + i) HARU); [| exact Hno | exact Hp].
    pose proof (fsw_ablock_low B ly S W _ md (kids - HEAD) (56 * cap + HEAD) HAR Hin) as (L1 & L2 & _).
    rewrite Hrq in L2. pose proof (@alloc_ceiling_lt rc) as HC47. lia. }
  destruct Hp' as (Hh & b & Hb). unfold writable_at, wview, mrestrict. rewrite Hh, Hb. discriminate.
Qed.
End d.
Lemma c2_obj_kid : forall segs m lblk p ms D i nm v kids,
  PjStruct.pj_node segs m lblk p (PjTree.JObj ms) D -> nth_error ms i = Some (nm, v) ->
  PjStruct.pj_u64 segs m (p + 24) kids -> exists cap, Z.of_nat i < cap /\ lblk kids (56 * cap).
Proof.
intros segs m lblk p ms D i nm v kids H Hi Hk. cbn [PjStruct.pj_node PjTree.tag] in H.
destruct H as (_ & _ & num & str & kids' & keys & n & cap & Hh & _ & Hn & Hc & Hkk & _).
assert (Hl : (i < length ms)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
destruct Hh as (_ & _ & _ & _ & Hkids & _).
rewrite (PjStruct.pj_u64_uniq segs m (p + 24) kids kids' Hk Hkids).
exists cap. destruct Hkk as [(C0 & _) | (C & L & _)]; [lia|]. split; [lia | exact L].
Qed.
(* the "state" member of the document is its third, the state object *)
Lemma c2_doc_state : forall es i v,
  nth_error (check_round_trip_stages_b.crt_doc es) i = Some ([115; 116; 97; 116; 101], v) ->
  i = 2%nat /\ v = PjTree.JObj (check_round_trip_stages_b.crt_st es).
Proof.
intros es i v H. unfold check_round_trip_stages_b.crt_doc in H.
destruct i as [|[|[|i]]]; cbn [nth_error] in H.
- cbv [check_round_trip_st8.CRT_FORMAT] in H. discriminate H.
- cbv [check_round_trip_st8.CRT_CARRIES] in H. discriminate H.
- injection H as H. split; [reflexivity | symmetry; exact H].
- destruct i; cbn [nth_error] in H; discriminate H.
Qed.
Lemma c2_doc_has_state : forall es,
  In ([115; 116; 97; 116; 101], PjTree.JObj (check_round_trip_stages_b.crt_st es)) (check_round_trip_stages_b.crt_doc es).
Proof. intros es. unfold check_round_trip_stages_b.crt_doc. right; right; left. reflexivity. Qed.

(* the decoded length (ported from FSH_crt_segC1.v at a working branch 725a5b225fe, crtC1_six_len /
   crtC1_dec_len, which port lib/Prog/check_no_overread.v:125-139) *)
Lemma c2_six_len : forall six, (length (WriterSpec.six_bytes six) * 4 <= length six * 3)%nat.
Proof.
  fix IH 1. intros [|a [|b [|c [|e r]]]]; cbn [WriterSpec.six_bytes length]; try lia.
  specialize (IH r). lia.
Qed.
Lemma c2_dec_len : forall tb bs, WriterSpec.b64_dec tb = Some bs -> (length bs * 4 <= length tb * 3)%nat.
Proof.
  intros tb bs H. unfold WriterSpec.b64_dec in H.
  destruct (WriterSpec.b64_scan 0 [] tb) as [[six pad]|] eqn:E; [|discriminate].
  destruct ((pad <=? 2) && WriterSpec.six_tail_ok six); [|discriminate]. injection H as <-.
  destruct (WriterSpecFacts.scan_inv tb 0 [] six pad E) as [H1 _]. cbn [length] in H1.
  pose proof (c2_six_len six). lia.
Qed.
(* the written document's facts (check_round_trip_stages_b.crt_doc_ok) at crt's body: bytes_ok from back's bytes, the
   length bound from crt_base's text (|tb| <= 3 * 2^20 and b64_dec) *)
Section bs. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Lemma c2_bs_len : forall cx, crt_base B cx -> Z.of_nat (length (c_bs cx)) <= 9 * 2 ^ 18.
Proof.
intros cx HB. destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Htb & _ & _ & Hdec & _).
pose proof (c2_dec_len _ _ Hdec) as Hl. unfold HState.zs in Hl. rewrite length_map in Hl. lia.
Qed.
End bs.

(* ---- the document's block count: 15 (its two objects' kids and keys arrays, six keys, five string values); an
   object of three members has its arrays (n = 3 <= cap), each member its key string and its value's blocks ---- *)
Lemma c2_str_blocks : forall segs m lblk p s D, PjStruct.pj_node segs m lblk p (PjTree.JStr s) D -> length D = 1%nat.
Proof.
intros segs m lblk p s D H. cbn [PjStruct.pj_node PjTree.tag] in H.
destruct H as (_ & _ & num & str & kids & keys & n & cap & _ & _ & _ & _ & _ & k & _ & ->). reflexivity.
Qed.
Lemma c2_obj3_blocks : forall segs m lblk p (n1 n2 n3 : list Z) (u1 u2 u3 : PjTree.jv) D,
  PjStruct.pj_node segs m lblk p (PjTree.JObj [(n1, u1); (n2, u2); (n3, u3)]) D ->
  exists a1 a2 a3 D1 D2 D3, PjStruct.pj_node segs m lblk a1 u1 D1 /\ PjStruct.pj_node segs m lblk a2 u2 D2 /\
    PjStruct.pj_node segs m lblk a3 u3 D3 /\ length D = (5 + length D1 + length D2 + length D3)%nat.
Proof.
intros segs m lblk p n1 n2 n3 u1 u2 u3 D H. cbn [PjStruct.pj_node PjTree.tag] in H.
destruct H as (_ & _ & num & str & kids & keys & n & cap & _ & _ & Hn & Hc & Hk & Di & -> & Hm).
cbn [length] in Hn. destruct Hk as [(C0 & _) | (C & _)]; [lia|].
rewrite (proj2 (Z.eqb_neq cap 0)) by lia.
cbn [PjStruct.pj_mems] in Hm.
destruct Hm as (x1 & k1 & D1 & D2' & -> & _ & _ & H1 & x2 & k2 & D2 & D3' & -> & _ & _ & H2 &
  x3 & k3 & D3 & D4 & -> & _ & _ & H3 & ->).
exists kids, (kids + 56), (kids + 56 + 56), D1, D2, D3.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
repeat (first [rewrite List.length_app | rewrite List.app_nil_r | progress cbn [length]]).
lia.
Qed.
Lemma c2_doc_blocks : forall segs m lblk p es D,
  PjStruct.pj_node segs m lblk p (PjTree.JObj (check_round_trip_stages_b.crt_doc es)) D -> length D = 15%nat.
Proof.
intros segs m lblk p es D H. unfold check_round_trip_stages_b.crt_doc in H.
destruct (c2_obj3_blocks _ _ _ _ _ _ _ _ _ _ _ H) as (a1 & a2 & a3 & D1 & D2 & D3 & H1 & H2 & H3 & ->).
rewrite (c2_str_blocks _ _ _ _ _ _ H1), (c2_str_blocks _ _ _ _ _ _ H2).
unfold check_round_trip_stages_b.crt_st in H3.
destruct (c2_obj3_blocks _ _ _ _ _ _ _ _ _ _ _ H3) as (b1 & b2 & b3 & E1 & E2 & E3 & G1 & G2 & G3 & ->).
rewrite (c2_str_blocks _ _ _ _ _ _ G1), (c2_str_blocks _ _ _ _ _ _ G2), (c2_str_blocks _ _ _ _ _ _ G3).
reflexivity.
Qed.
(* ---- the budget arithmetic of the group (closed values MEASURED by vm_compute) ---- *)
Lemma c2_TR15 : forall es,
  rd_ev (PjRoundTrip.ttrace (PjTree.JObj (check_round_trip_stages_b.crt_doc es))) = 15 /\
  Z.of_nat (length (PjRoundTrip.ttrace (PjTree.JObj (check_round_trip_stages_b.crt_doc es)))) = 15.
Proof. intros es. split; vm_compute; reflexivity. Qed.
Lemma c2_KC_vals : forall cx, K_82218 cx = 19 /\ CNT_82218 cx = 17.
Proof. intros cx. split; vm_compute; reflexivity. Qed.
Lemma c2_rd_live_ge : forall tr, PjGrammar.held tr + HEAD * Z.of_nat (length tr) <= rd_live tr /\ 0 <= rd_live tr.
Proof.
induction tr as [|e tr IH]; [cbn; lia|].
cbn [PjGrammar.held length rd_live fold_right]. fold (rd_live tr). rewrite Nat2Z.inj_succ.
assert (He : PjGrammar.held_ev e <= Z.of_nat (PjGrammar.esize e)) by (destruct e; cbn [PjGrammar.held_ev PjGrammar.esize]; lia).
unfold HEAD in *. lia.
Qed.
Lemma c2_LIVE18_nonneg : forall cx, 0 <= LIVE_82218 cx.
Proof.
intros cx. pose proof (proj2 (c2_rd_live_ge (pj_set_c.set_trace 0 0 6))).
pose proof (proj2 (c2_rd_live_ge (pj_set_c.set_trace 1 8 7))). pose proof (proj2 (c2_rd_live_ge (pj_set_c.set_trace 0 0 8))).
pose proof (proj2 (c2_rd_live_ge (pj_set_c.set_trace 2 8 5))).
unfold LIVE_82218, LIVE_821ac, LIVE_82068, crt_len, FSH_Fn_writer.enc_size, FSH_Fn_writer.dec_size, HEAD.
Z.div_mod_to_equations. lia.
Qed.
Lemma c2_wcalls_le : forall st, 3 * FSH_Fn_writer.wcalls st <= FSH_Fn_writer.wev0 st + 2 /\ 0 <= FSH_Fn_writer.wev0 st.
Proof.
intros st. unfold FSH_Fn_writer.wcalls, FSH_Fn_writer.wev0.
destruct (WriterApp.w_calls st) as [|c r]; cbn [length]; unfold EV_fuzz_malloc, EV_fuzz_realloc; lia.
Qed.
(* blocks_bytes across a boundary whose block list is the entry's plus L plus the reader blocks of D (FSH_crt_segC1.v
   crtC1_bsum_rd_hblocks / crtC1_rd_sum_le at a working branch 725a5b225fe, restated) *)
Lemma c2_bsum_rd_hblocks : forall D, YCbq.bsum (rd_hblocks D) = rd_sum D + HEAD * Z.of_nat (length D).
Proof.
  induction D as [|b D IH]; [reflexivity|].
  change (rd_hblocks (b :: D)) with ((fst b - HEAD, snd b + HEAD) :: rd_hblocks D).
  change (rd_sum (b :: D)) with (snd b + rd_sum D).
  rewrite YCbq.bsum_cons, IH. cbn [snd length]. rewrite Nat2Z.inj_succ. unfold HEAD. lia.
Qed.
Section c2b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Lemma c2_rd_sum_le : forall ly3 S3 ly0 S0 L D,
  Permutation (ablocks B ly3 S3) (ablocks B ly0 S0 ++ L ++ rd_hblocks D) ->
  blocks_bytes S3 = blocks_bytes S0 + YCbq.bsum L + rd_sum D + HEAD * Z.of_nat (length D).
Proof.
  intros ly3 S3 ly0 S0 L D HP.
  rewrite (YCbq.blocks_bytes_bsum B ly3 S3), (YCbq.blocks_bytes_bsum B ly0 S0), (YCbq.bsum_perm _ _ HP).
  rewrite !YCbq.bsum_app, c2_bsum_rd_hblocks. lia.
Qed.
(* crt_base's room facts (its quiet, live, event and block-byte conjuncts) *)
Lemma c2_base_room : forall cx, crt_base B cx ->
  quiet (c_cnt cx) SIZE_MAXZ EV_check_round_trip /\ c_live cx + LIVE_check_round_trip < 2 ^ 64 /\
  st_nev (c_S cx) + EV_check_round_trip <= EV_MAX /\ blocks_bytes (c_S cx) + LIVE_check_round_trip <= LIVE_MAX.
Proof.
intros cx HB.
destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hq & Hl & _ & _ & Hev & Hbb & _).
exact (conj Hq (conj Hl (conj Hev Hbb))).
Qed.
End c2b.

(* ================= segment 25: 0x82218 .. `bnez a0` .. pj_write (&doc, 1) at 0x82224 .. 0x82228 =================
   The last pj_set returned 0 (crt_INV_82218's a0), so the `bnez a0` to the abort tail is not taken; the run reaches
   pj_write 0x83d08 with a0 = s10 = &doc (atom 26), a1 = 1, ra = 0x82228 (MEASURED by the engine). An instance of
   FSH_crt_site.crt_seg_call_br; HCALL is pj_write's contract at v = doc, t = the document, D = UL = Ddoc, pretty = 1,
   under the by-trace room crt_room_C2 (FSH_crt_room.crt_room_C2_holds). Its writer state is crt_wst's at any g_count
   (WriterAppFacts.putN_ok), so the refused-allocation arm is empty and the run's ticks, count bumps and buffer are
   crt_wst's. *)
Lemma c2_putN : forall cx cnt, 0 <= cnt -> cnt + FSH_Fn_writer.wcalls (crt_wst cx) < 2 ^ 63 ->
  WriterApp.putN (WriterApp.w0 cnt SIZE_MAXZ) (crt_wpieces cx) =
  WriterApp.mkW 0 (concat (crt_wpieces cx)) (WriterApp.w_cap (crt_wst cx))
    (cnt + FSH_Fn_writer.wcalls (crt_wst cx)) SIZE_MAXZ (WriterApp.w_calls (crt_wst cx)).
Proof.
intros cx cnt H0 H1.
assert (Ewc : FSH_Fn_writer.wcalls (crt_wst cx) =
  Z.of_nat (length (WriterSpec.grow_calls 0 0 (WriterSpec.piece_lens (crt_wpieces cx))))) by reflexivity.
rewrite Ewc in H1.
assert (Hlt : cnt + Z.of_nat (length (WriterSpec.grow_calls 0 0 (WriterSpec.piece_lens (crt_wpieces cx)))) < 2 ^ 64)
  by lia.
assert (Hle : cnt + Z.of_nat (length (WriterSpec.grow_calls 0 0 (WriterSpec.piece_lens (crt_wpieces cx)))) <= SIZE_MAXZ)
  by (unfold SIZE_MAXZ; lia).
rewrite (WriterAppFacts.putN_ok (crt_wpieces cx) (WriterApp.w0 cnt SIZE_MAXZ)).
- reflexivity.
- reflexivity.
- exact H0.
- exact Hlt.
- right. exact Hle.
Qed.
(* a block inserted into the middle of a list joins the permutation *)
Lemma c2_perm_ins : forall (L1 L2 C1 C2 : list (Z * Z)) x,
  Permutation (C1 ++ C2) (L1 ++ L2) -> Permutation (C1 ++ x :: C2) (L1 ++ x :: L2).
Proof.
intros L1 L2 C1 C2 x H.
exact (perm_trans (Permutation_sym (Permutation_middle C1 C2 x)) (perm_trans (perm_skip x H) (Permutation_middle L1 L2 x))).
Qed.

Definition c2_b25 : sstate := Eval vm_compute in fst (sym_runN tfibsegs crt_tbl FUEL (crt_ss2 0x82218)).
Lemma c2_run25a :
  sym_runN tfibsegs crt_tbl FUEL (crt_ss2 0x82218) = (c2_b25, RS_stopped (SR_branch BC_NE (SOff 10 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition c2_s25 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL A_pj_write (add_cond c2_b25 crt_c0)).
Lemma c2_run25b : sym_run_toN tfibsegs crt_tbl FUEL A_pj_write (add_cond c2_b25 crt_c0) = (c2_s25, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma c2_s25_site : crt_site c2_b25 c2_s25 A_pj_write 0x82228.
Proof. split; [vm_compute; reflexivity|]. repeat (split; [vm_compute; reflexivity|]). vm_compute. reflexivity. Qed.
Lemma c2_s25_args : sr_get (ss_regs c2_s25) 10%bv = SOff 26 0 /\ sr_get (ss_regs c2_s25) 11%bv = SLit 1.
Proof. split; vm_compute; reflexivity. Qed.
Lemma c2_s25_save : crt_ssave c2_s25.
Proof. apply crt_ssave_dec. vm_compute. reflexivity. Qed.

Section s25. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis PJW : pj_write_spec (SK := SK) B tfibsegs.

Lemma c2_call25 : crt_hcall SK B c2_s25 A_pj_write 0x82228 STK_pj_write (crt_INV_82218 B) (c2_INV_82228 B).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE HINV HJC HARUC Hfr HSB RG HPREc HFRL HTOPc.
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARUC) as HARC.
assert (HEADv : HEAD = 16) by reflexivity.
destruct HINV as (E10 & E18 & E20 & E21 & E22 & E23 & E26 & E27 &
  (same & nsame & dec & Ddoc & live & peak & cnt & E24 & E25 & HPB & HPU & HH & Rtext & Ztext & Ctext & Rdec & Zdec &
   Htree & Hpd & Hps & Hpv & Hpb & Hzs & Hzv & Hval & Hra & Hglob & Hlivee & Hlive & Hcnt & Hk)).
set (m3 := ms_mem ms3) in *.
destruct (crt_F_facts SK B cx _ _ _ _ _ _ _ HJC HARUC Hfr) as (HFal & HF4096 & HFceil & HFapp & HSF1 & HSF2).
pose proof HJC as (_ & HlyC & _). pose proof (crt_F_ly cx _ ly3 HlyC) as EF.
pose proof HJC as (_ & _ & _ & _ & _ & _ & Hnev & Hk0 & _).
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
destruct c2_s25_args as (R10 & R11).
pose proof (@YM05.alloc_ceiling_lt rc) as HC47.
(* ---- the budgets ---- *)
destruct (c2_base_room B cx HB) as ((_ & Hc0 & Hc78) & Hl0 & Hev0 & Hbb0).
pose proof (crt_live0 B cx HB) as Hlv0.
destruct (FSH_crt_room.crt_room_C2_holds B cx HB) as (RK & RC & RL).
unfold crt_TR, crt_trlen, crt_es in RK, RC, RL. unfold EV_fuzz_malloc, EV_fuzz_free, CRT_EV_WRAP in RK.
destruct (c2_TR15 (WriterSpec.b64_enc (c_bs cx))) as (Tev & Tlen).
destruct (c2_KC_vals cx) as (KV & CV).
pose proof (c2_wcalls_le (crt_wst cx)) as (Hwc & Hwv).
pose proof (c2_rd_live_ge (PjRoundTrip.ttrace (PjTree.JObj
  (check_round_trip_stages_b.crt_doc (WriterSpec.b64_enc (c_bs cx)))))) as (Hrl & Hrl0).
pose proof (c2_LIVE18_nonneg cx) as HL18.
unfold EV_check_round_trip in *.
(* ---- the boundary's data at the call's memory ---- *)
pose proof (c2_dat0_below B cx ly3 S3 W3 _ _ m3 memC dec Ddoc HARC HSB HF4096 HFceil
  (conj Rtext (conj Rdec (conj Zdec (conj Htree (conj Hpd (conj Hval Hra))))))) as D0c.
pose proof D0c as (_ & _ & _ & Htree1 & Hpd1 & _).
pose proof (pobj_below B ly3 S3 W3 _ _ m3 memC _ HARC HSB Hpb) as Hpbc.
pose proof (fs_glob_below W3 m3 memC live peak cnt SIZE_MAXZ HSB Hglob) as Hglob1.
(* ---- the document's facts ---- *)
pose proof (garr8_bytes_ok tfibsegs _ _ _ Zdec) as Hbok.
destruct (check_round_trip_stages_b.crt_doc_ok (c_bs cx) Hbok ltac:(pose proof (c2_bs_len B cx HB); lia))
  as (WF & Hdd & _ & _ & WL & _ & _ & _ & _).
(* ---- the live bytes held so far ---- *)
assert (Hns : 0 <= nsame).
{ assert (Hin : In (same, nsame) (ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPB)). apply in_or_app. right. apply in_or_app. left. cbn. tauto. }
  destruct (al_blocks tfibsegs B (AR_laws_ok tfibsegs B) ly3 S3 W3 _ mdC same nsame HARC Hin) as (_ & _ & _ & _ & _ & _ & Hm).
  lia. }
pose proof (c2_rd_sum_le B ly3 S3 (c_ly cx) (c_S cx) _ Ddoc HPB) as Hbb.
unfold YCbq.bsum in Hbb. cbn [fold_right snd] in Hbb.
pose proof Rtext as (_ & _ & Hent & _).
pose proof Htree as (_ & HBdoc & _).
pose proof (crt_rd_sum_pos B ly3 S3 W3 m3 Ddoc HBdoc) as Hsd.
(* ---- pj_write (&doc, 1) ---- *)
assert (G10 : YK11.getr regsC 10%bv = w64 (crt_F cx + 0x20)) by (rewrite RG, R10, fsw_SOff0; exact E26).
assert (G11 : YK11.getr regsC 11%bv = w64 1) by (rewrite RG, R11; reflexivity).
assert (Hra1 : raZ regsC = 0x82228).
{ unfold raZ. rewrite RG. destruct c2_s25_site as (_ & _ & _ & _ & G1 & _). rewrite G1. reflexivity. }
pose proof Htree1 as (HN1 & HB1 & _).
assert (Hcnt0 : 0 <= cnt) by lia.
assert (Hcw : cnt + FSH_Fn_writer.wcalls (crt_wst cx) < 2 ^ 63) by lia.
pose proof (c2_putN cx cnt Hcnt0 Hcw) as Est.
assert (Hst : WriterApp.putN (WriterApp.w0 cnt SIZE_MAXZ) (WriterValue.wdpieces
    (PjTree.JObj (check_round_trip_stages_b.crt_doc (WriterSpec.b64_enc (c_bs cx)))) (negb (1 =? 0))) =
  WriterApp.mkW 0 (concat (crt_wpieces cx)) (WriterApp.w_cap (crt_wst cx))
    (cnt + FSH_Fn_writer.wcalls (crt_wst cx)) SIZE_MAXZ (WriterApp.w_calls (crt_wst cx))) by exact Est.
assert (Ewev : FSH_Fn_writer.wev0 (WriterApp.putN (WriterApp.w0 cnt SIZE_MAXZ) (WriterValue.wdpieces
    (PjTree.JObj (check_round_trip_stages_b.crt_doc (WriterSpec.b64_enc (c_bs cx)))) (negb (1 =? 0)))) =
  FSH_Fn_writer.wev0 (crt_wst cx)) by (rewrite Hst; reflexivity).
assert (Ewcl : FSH_Fn_writer.wcalls (WriterApp.putN (WriterApp.w0 cnt SIZE_MAXZ) (WriterValue.wdpieces
    (PjTree.JObj (check_round_trip_stages_b.crt_doc (WriterSpec.b64_enc (c_bs cx)))) (negb (1 =? 0)))) =
  FSH_Fn_writer.wcalls (crt_wst cx)) by (rewrite Hst; reflexivity).
assert (Ecap : WriterApp.w_cap (WriterApp.putN (WriterApp.w0 cnt SIZE_MAXZ) (WriterValue.wdpieces
    (PjTree.JObj (check_round_trip_stages_b.crt_doc (WriterSpec.b64_enc (c_bs cx)))) (negb (1 =? 0)))) =
  WriterApp.w_cap (crt_wst cx)) by (rewrite Hst; reflexivity).
pose proof (PJW ly3 S3 U3 W3 regsC memC mdC _ (crt_F cx + 0x20) 1
  (PjTree.JObj (check_round_trip_stages_b.crt_doc (WriterSpec.b64_enc (c_bs cx)))) Ddoc Ddoc live peak cnt SIZE_MAXZ
  HPREc HH HFRL G10 G11 ltac:(lia) HN1 Hpd1 HB1 (fun a kk H => H) Hglob1 (FSDocStrs.fs_doc_jv_plain (c_bs cx) Hbok) Hdd
  ltac:(change (negb (1 =? 0)) with true; unfold WMAX; change (2 ^ 27) with 134217728; change (2 ^ 22) with 4194304 in WL;
        lia)) as HC.
specialize (HC ltac:(cbv zeta; rewrite Ewev, Ecap, Ewcl; unfold EV_fuzz_free, HEAD in *; split; [lia|]; split; [lia|];
  split; lia)).
exists FS_PSTAT_FP, (FSH_Fn_writer.wev0 (crt_wst cx)). eexists. split; [exact HC|].
split; [exact (c2_fpsub_static B _ _ _ _ _)|].
split.
{ intros a Ha Hf.
  exact (frm_img tfibsegs B (AR_laws_ok tfibsegs B) ly3 S3 W3 _ mdC 3 (c_pos cx) a HARC Hin3
    ltac:(rewrite EF, crt_frame3; rewrite crt_frame3 in Ha; lia) (crt_pstat_img a Hf)). }
intros W' c' HPc. cbv zeta in HPc. rewrite Hst in HPc.
cbn [WriterApp.w_failed WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail] in HPc.
destruct HPc as [(q & _ & ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HP & HQ) | (Hfl & _)];
  [|exfalso; exact (Hfl eq_refl)].
exists ly', S', (U3 ++ [(q - HEAD, HEAD)]), regs', mem', md'.
split; [exact Ec|]. split; [exact HJc|]. split; [exact OK'|]. split; [exact PO'|]. split; [exact HP|].
intros HJ' HARU'.
destruct HQ as (Gq & (Hq0 & Hq4 & _ & Hwq & Rq & Zq) & (C1 & C2 & EC & EC12) & _ & (peak' & Hpk & Hglob2)).
set (cap := WriterApp.w_cap (crt_wst cx)) in *.
pose proof Rq as (_ & _ & Hcap0 & _).
(* ---- the heads after the call: U's and the file's ---- *)
assert (HH' : FSupoisonU.fs_heads B ly' S' (U3 ++ [(q - HEAD, HEAD)])).
{ intros r Hr. apply in_app_or in Hr as [Hr | [<- | []]].
  - destruct (HH r Hr) as (H16 & m & Hm & Hrq). split; [exact H16|]. exists m. split; [|exact Hrq].
    rewrite EC. rewrite <- EC12 in Hm. apply in_app_or in Hm as [Hm | Hm]; apply in_or_app; [left | right; right]; exact Hm.
  - cbn [fst snd]. split; [reflexivity|]. exists (cap + HEAD). split.
    + rewrite EC. apply in_or_app. right. left. reflexivity.
    + rewrite c2_rq by exact Hcap0. lia. }
(* ---- the boundary's data after the call (pj_write writes the statics only, outside its own frame) ---- *)
destruct (c2_dat0_call SK B cx _ _ _ ly3 S3 U3 W3 memC mdC ly' S' (U3 ++ [(q - HEAD, HEAD)]) W' mem' md' _ dec Ddoc HJc
  HARUC OK' PO' HH' (c2_fpok_pstat cx) Hin3 EF Hpbc D0c) as (Rtext2 & Rdec2 & Zdec2 & Htree2 & Hpd2 & Hval2 & Hra2).
assert (Hpb2 : pobj tfibsegs B ly' S' W' mem' (crt_F cx + 0x140)).
{ eapply (pobj_kept_call B); [exact HJc | exact HARUC | exact OK' | exact PO'
  | intros x Hx Hf; exact (frm_img tfibsegs B (AR_laws_ok tfibsegs B) ly3 S3 W3 _ mdC 3 (c_pos cx) x HARC Hin3
      ltac:(rewrite EF, crt_frame3; lia) (crt_pstat_img x Hf))
  | exact (c2_fpok_sh B cx FS_PSTAT_FP ly3 S3 W3 _ mdC memC (c2_fpok_pstat cx) HARC Hpbc) | exact HH' | exact Hpbc]. }
(* ---- the blocks after the call ---- *)
assert (Hbb' : blocks_bytes S' = blocks_bytes S3 + (cap + HEAD)).
{ rewrite (YCbq.blocks_bytes_bsum B ly' S'), (YCbq.blocks_bytes_bsum B ly3 S3), EC, <- EC12.
  rewrite !YCbq.bsum_app, YCbq.bsum_cons. cbn [snd]. lia. }
(* ---- the next boundary ---- *)
assert (K : forall n, acallee_saved (Z.of_nat n) -> sr_get (ss_regs c2_s25) (Z_to_bv 5 (Z.of_nat n)) = SOff n 0 ->
  ew (Ereg regs' (crt_extra cx)) n = ew E n)
  by (intros n Hc Hr; exact (c2_keep_s E c2_s25 regsC regs' (crt_extra cx) n RG HP Hc Hr)).
hnf.
split; [rewrite (K 18%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s25_save; lia)); exact E18|].
split; [rewrite (K 20%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s25_save; lia)); exact E20|].
split; [rewrite (K 21%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s25_save; lia)); exact E21|].
split; [rewrite (K 22%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s25_save; lia)); exact E22|].
split; [rewrite (K 23%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s25_save; lia)); exact E23|].
split; [rewrite (K 26%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s25_save; lia)); exact E26|].
split; [rewrite (K 27%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s25_save; lia)); exact E27|].
exists same, nsame, dec, q, cap, Ddoc, (live + cap), peak', (cnt + FSH_Fn_writer.wcalls (crt_wst cx)).
split; [rewrite (K 24%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s25_save; lia)); exact E24|].
split; [rewrite (K 25%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s25_save; lia)); exact E25|].
split; [rewrite (ew_Ereg_nat regs' (crt_extra cx) 10 10%bv eq_refl); exact Gq|].
split; [exact Hq0|].
split.
{ rewrite EC. replace (ablocks B (c_ly cx) (c_S cx) ++
    [(c_text cx - HEAD, FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + HEAD);
     (c_want cx, FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx)))); (same, nsame);
     (dec - HEAD, FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD); (q - HEAD, cap + HEAD)] ++
    rd_hblocks Ddoc)
  with ((ablocks B (c_ly cx) (c_S cx) ++
    [(c_text cx - HEAD, FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))) + HEAD);
     (c_want cx, FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx)))); (same, nsame);
     (dec - HEAD, FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD)]) ++ (q - HEAD, cap + HEAD) ::
    rd_hblocks Ddoc) by (rewrite <- app_assoc; reflexivity).
  apply c2_perm_ins. rewrite EC12. rewrite <- app_assoc. exact HPB. }
split.
{ eapply perm_trans; [apply Permutation_app_tail; exact HPU|].
  rewrite <- !app_assoc. apply Permutation_app_head. cbn [app]. apply perm_skip. apply perm_skip.
  apply Permutation_sym. apply Permutation_cons_append. }
split; [exact HH'|].
split; [exact Rtext2|]. split; [exact Rdec2|]. split; [exact Zdec2|]. split; [exact Rq|].
split; [exact Zq|]. split; [exact Hwq|]. split; [exact Hq4|].
split; [exact Htree2|]. split; [exact Hpd2|]. split; [exact Hpb2|].
split; [exact Hval2|]. split; [exact Hra2|].
split; [lia|].
split; [exact Hglob2|].
split; [reflexivity|].
split; [lia|].
assert (Hwc0 : 0 <= FSH_Fn_writer.wcalls (crt_wst cx)) by (unfold FSH_Fn_writer.wcalls; lia).
split; [lia|].
lia.
Qed.

(* segment 25: crt_from at the return of pj_write under c2_INV_82228 gives crt_from at the return of the last pj_set
   under crt_INV_82218 *)
Lemma c2_seg25 : crt_from SK B c2_ss_228 (c2_INV_82228 B) -> crt_from SK B c2_ss_218 (crt_INV_82218 B).
Proof.
exact (crt_seg_call_br SK B 0x82218 A_pj_write 0x82228 c2_b25 c2_s25 (crt_INV_82218 B) (c2_INV_82228 B) STK_pj_write
  c2_run25a c2_run25b c2_s25_site ltac:(lia) eq_refl ltac:(apply Z.leb_le; vm_compute; reflexivity)
  ltac:(apply Z.leb_le; vm_compute; reflexivity) (fun _ _ _ _ _ _ _ _ _ H => proj1 H) c2_call25).
Qed.
End s25.

(* ================= segment 26: 0x82228 .. `beqz a0` .. strlen (file) through the thunk 0x42654 .. 0x82238 =================
   pj_write returned the file (c2_INV_82228's a0 = file, nonzero), so the `beqz a0` to the abort tail is not taken
   (FSH_crt_site.crt_no_trap_eq); the run (`mv s6, a0`, `ld s2, 0x18(s1)` = &back) reaches the strlen thunk with a0 =
   file, ra = 0x82238 (MEASURED by the engine). The call is a RUNTIME call (FsRt.fr_strlen, astrlen_realizesU), so its
   post is rt_post_roU, not a program fpostU: it fits crt_hcall's generic post P, the callee journal being the caller's
   own restricted to the call's stack window (YCbq.ajournal_sub_init) and moved over the call's write
   (YCbq.ajournal_after_write, Wr = the STK_RT_STR window). The `beqz` arm is crt_seg_call_br's with BC_EQ. *)
(* fs's allocator statics are image bytes, so a step that keeps the visible image keeps fs_glob (segD's crt_glob_img /
   crt_glob_keep at 6b0ff16eb7c FSH_crt_segD.v:139-181, restated) *)
Lemma c2_glob_img : forall a, (G_FAIL <= a < G_FAIL + 8 \/ G_LIVE <= a < G_LIVE + 8 \/ G_PEAK <= a < G_PEAK + 8 \/
  G_COUNT <= a < G_COUNT + 8) -> in_img tfibsegs a.
Proof.
intros a Ha.
assert (Hx : existsb (fun s => (Z.of_N (seg_base s) <=? 0xa1000) && (0x5fd000 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))
  tfibsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in Hx as (sg & Hin & Hc). apply andb_prop in Hc as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
exists sg. split; [exact Hin|]. unfold G_FAIL, G_LIVE, G_PEAK, G_COUNT in Ha. lia.
Qed.
Lemma c2_glob_keep : forall (W : world tfibsegs) (m m' : word -> option byte) live peak cnt fail,
  (forall a, in_img tfibsegs a -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W m' live peak cnt fail.
Proof.
intros W m m' live peak cnt fail Hk (G1 & G2 & G3 & G4 & R).
assert (VB : forall g v, (G_FAIL <= g /\ g + 8 <= G_FAIL + 8 \/ G_LIVE <= g /\ g + 8 <= G_LIVE + 8 \/
    G_PEAK <= g /\ g + 8 <= G_PEAK + 8 \/ G_COUNT <= g /\ g + 8 <= G_COUNT + 8) ->
  val_mem tfibsegs (mrestrict (w_H W) m) g 8 v -> val_mem tfibsegs (mrestrict (w_H W) m') g 8 v).
{ intros g v Hg Hv kk Hkk. assert (Hi : in_img tfibsegs (g + Z.of_nat kk)) by (apply c2_glob_img; lia).
  rewrite (mbyte_of_aview tfibsegs (w_H W) (w_H W) m m' _ (Hk _ Hi)). exact (Hv kk Hkk). }
unfold fs_glob, fs_glob_at in *.
split; [apply VB; [lia | exact G1]|]. split; [apply VB; [lia | exact G2]|].
split; [apply VB; [lia | exact G3]|]. split; [apply VB; [lia | exact G4]|]. exact R.
Qed.
(* a register the run set to an atom plus an offset *)
Lemma c2_SOff : forall E n z v, bv_unsigned (ew E n) = v -> 0 <= v + z < 2 ^ 64 ->
  sv_denot E (SOff n z) = Z_to_bv 64 (v + z).
Proof.
intros E n z v H Hr. apply bv_eq. rewrite denot_SOff, H, zcanon_id by (unfold M64; lia).
rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity | change (bv_modulus 64) with (2 ^ 64); lia].
Qed.

(* the `beqz a0` form of crt_seg_call_br (FSH_crt_site.v:578-614, BC_EQ for BC_NE, crt_no_trap_eq for _ne): a0 is a
   nonzero pointer the previous call returned *)
Definition c2_c1 : acond := mkAC BC_NE (SOff 10 0) (SLit 0).
Section beq. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Lemma c2_seg_call_beq : forall r0 A_c r sb ssC (INV INV' : crt_inv) STKc,
  sym_runN tfibsegs crt_tbl FUEL (crt_ss2 r0) = (sb, RS_stopped (SR_branch BC_EQ (SOff 10 0) (SLit 0))) ->
  sym_run_toN tfibsegs crt_tbl FUEL A_c (add_cond sb c2_c1) = (ssC, RS_running) ->
  crt_site sb ssC A_c r -> 4096 <= r < 2 ^ 64 -> r mod 2 = 0 ->
  0 <= STKc -> STKc + 208 <= STK_check_round_trip ->
  (forall cx E k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3, INV cx E k ly3 S3 U3 W3 ms3 md3 ->
     ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 -> ew E 10 <> Z_to_bv 64 0) ->
  crt_hcall SK B ssC A_c r STKc INV INV' ->
  crt_from SK B (crt_ss_ret r crt_cs1 crt_csF) INV' ->
  crt_from SK B (crt_ss_ret r0 crt_cs1 crt_csF) INV.
Proof.
intros r0 A_c r sb ssC INV INV' STKc HRUN1 HRUN2 (Hmem1 & HCS) Hr Hr2 HSTKc HSTK HZ HCALL NEXT.
intros cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU HFO HINV HS.
assert (AWR : forall ssx, ss_mem ssx = [crt_s0_region; crt_slot_region crt_cs1] ->
  awr_ok tfibsegs B E (ss_mem ssx) STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP
    (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3 [(3, c_pos cx)] (frames (c_S cx)))
  by (intros ssx Hx; rewrite Hx; eapply crt_awr2; eassumption).
pose proof (st_ok_submem tfibsegs E _ _ _ HS (crt_sub2 r0) ltac:(vm_compute; reflexivity)) as HS2.
change (st_ok tfibsegs E (crt_ss2 r0) (restrict (w_H W3) ms3)) in HS2.
(* run 1: to the `beqz a0` *)
eapply (fsw_run_AJU B crt_tbl crt_tbl_ok W3 FUEL E (crt_ss2 r0) sb _ ms3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  HS2 HRUN1 I HARU HJ (AWR (crt_ss2 r0) eq_refl)).
intros ms1 mat1 HS1 HJ1 HARU1 HF1 HFr1 HG1.
(* the not-taken arm: a0 <> 0 *)
pose proof (HZ _ _ _ _ _ _ _ _ _ HINV HARU) as Hne.
assert (Ez : ew E 10 = Z_to_bv 64 (bv_unsigned (ew E 10))) by (symmetry; apply Z_to_bv_bv_unsigned).
pose proof (u64_range (ew E 10)) as Hz.
assert (Hz0 : bv_unsigned (ew E 10) <> 0) by (intros H0; apply Hne; rewrite Ez, H0; reflexivity).
pose proof (st_ok_add_cond_neg tfibsegs E sb _ BC_EQ (SOff 10 0) (SLit 0) HS1
  (crt_no_trap_eq E _ Ez Hz Hz0)) as HS1c.
change (add_cond sb (mkAC (neg_bc BC_EQ) (SOff 10 0) (SLit 0))) with (add_cond sb c2_c1) in HS1c.
(* run 2: to the callee *)
eapply (fsw_run_to_AJU B crt_tbl crt_tbl_ok W3 FUEL A_c E (add_cond sb c2_c1) ssC RS_running ms1
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS1c HRUN2 I HARU1 HJ1 (AWR (add_cond sb c2_c1) Hmem1)).
intros ms mat HSC HJC HARUC HF HFr HG.
assert (HF1' : frame_of E [crt_s0_region; crt_slot_region crt_cs1] (ms_mem ms3) (ms_mem ms1)) by exact HF1.
assert (HF' : frame_of E [crt_s0_region; crt_slot_region crt_cs1] (ms_mem ms1) (ms_mem ms))
  by (rewrite <- Hmem1; exact HF).
assert (SB1 : same_below (ms_mem ms3) (ms_mem ms1) alloc_ceiling) by (eapply crt_sb; [exact HB | exact HE | exact HF1']).
assert (SB2 : same_below (ms_mem ms1) (ms_mem ms) alloc_ceiling) by (eapply crt_sb; [exact HB | exact HE | exact HF']).
exact (crt_call_core SK B ssC A_c r INV INV' STKc cx E k ly3 S3 U3 W3 ms3 md3 ms _ HCS Hr Hr2 HSTKc HSTK HCALL NEXT
  HB HE HFO HINV HSC HJC HARUC (same_below_trans _ _ _ _ SB1 SB2)).
Qed.
End beq.

Definition c2_b26 : sstate := Eval vm_compute in fst (sym_runN tfibsegs crt_tbl FUEL (crt_ss2 0x82228)).
Lemma c2_run26a :
  sym_runN tfibsegs crt_tbl FUEL (crt_ss2 0x82228) = (c2_b26, RS_stopped (SR_branch BC_EQ (SOff 10 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition c2_s26 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL PC_strlen (add_cond c2_b26 c2_c1)).
Lemma c2_run26b : sym_run_toN tfibsegs crt_tbl FUEL PC_strlen (add_cond c2_b26 c2_c1) = (c2_s26, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma c2_s26_site : crt_site c2_b26 c2_s26 PC_strlen 0x82238.
Proof. split; [vm_compute; reflexivity|]. repeat (split; [vm_compute; reflexivity|]). vm_compute. reflexivity. Qed.
Lemma c2_s26_args : sr_get (ss_regs c2_s26) 10%bv = SOff 10 0 /\ sr_get (ss_regs c2_s26) 18%bv = SOff 47 0x140 /\
  sr_get (ss_regs c2_s26) 22%bv = SOff 10 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

Section s26. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis RTS : astrlen_realizesU tfibsegs B PC_strlen.

(* the read-only image view a runtime string reader asks (fs_img_facts' rom_view, at the unpoisoned memory, read back on
   the machine's: a read-only byte is an image byte below the shadow band, which unpoison leaves) *)
Lemma c2_rom_view : forall ly S U (W : world tfibsegs) mem md,
  ARU tfibsegs B ly S U W mem md -> arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) ->
  rom_view tfibsegs W mem.
Proof.
intros ly S U W mem md H HRO. pose proof H as (HAR & _ & _).
assert (LOW : forall a, in_img tfibsegs a -> unpoison U mem (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ intros a Ha. pose proof (c2_img_range a Ha). apply (fsw_unpoison_app B ly S U W mem md a H); [lia|].
  unfold SHADOW_OFF. lia. }
assert (HROu : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (unpoison U mem))).
{ intros a Hro Ho He. rewrite (aview_at tfibsegs (w_H W) (unpoison U mem) mem a); [exact (HRO a Hro Ho He)|].
  exact (LOW a (fsw_roP_img a Hro)). }
destruct (proj2 IMG ly S W (unpoison U mem) md HAR HROu) as (Hrv & _).
intros a Ha. rewrite <- (Hrv a Ha). symmetry. apply (aview_at tfibsegs (w_H W) (unpoison U mem) mem a).
apply LOW. destruct Ha as (sg & Hsg & _ & Hr). exists sg. split; [exact Hsg | exact Hr].
Qed.

Lemma c2_call26 : crt_hcall SK B c2_s26 PC_strlen 0x82238 STK_RT_STR (c2_INV_82228 B) (c2_INV_82238 B).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE HINV HJC HARUC Hfr HSB RG HPREc HFRL HTOPc.
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARUC) as HARC.
pose proof HARUC as (_ & OK0 & _).
assert (HEADv : HEAD = 16) by reflexivity.
destruct HINV as (E18 & E20 & E21 & E22 & E23 & E26 & E27 &
  (same & nsame & back & file & nfile & Ddoc & live & peak & cnt &
   E24 & E25 & E10 & Hf0 & HPB & HPU & HH & Rtext & Rback & Zback & Rfile & Zfile & Hwd & Hfile4 &
   Htree & Hpobj2 & Hpobj1 & Hval & Hra & Hlivee & Hglob & Hnfc & Hlive & Hcnt & Hk)).
set (m3 := ms_mem ms3) in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (crt_F_facts SK B cx _ _ _ _ _ _ _ HJC HARUC Hfr) as (HFal & HF4096 & HFceil & HFapp & HSF1 & HSF2).
pose proof HJC as (_ & HlyC & _). pose proof (crt_F_ly cx _ ly3 HlyC) as EF.
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
destruct c2_s26_args as (R10 & R18 & R22).
pose proof HE as (E2v & E3v & E4v & E8v & E9v & E19v & _).
pose proof HB as ((HPRE0 & _) & _). destruct HPRE0 as ((_ & _ & _ & Hgp0 & Htp0 & _) & _).
pose proof HJC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
assert (HSTKv : 8192 + 208 <= STK_check_round_trip) by (apply Z.leb_le; vm_compute; reflexivity).
pose proof (proj1 YM05.alloc_ceiling_val) as HCV.
pose proof (@YM05.alloc_ceiling_lt rc) as HC47.
destruct (crt_sp1_facts cx Hal16 ltac:(lia)) as (Hsp1b & _ & Hsp1m).
assert (R1 : YK11.getr regsC 1%bv = Z_to_bv 64 0x82238).
{ rewrite RG. destruct c2_s26_site as (_ & _ & _ & _ & G1 & _). rewrite G1. reflexivity. }
assert (R2 : spZ regsC = crt_sp1 cx).
{ unfold spZ. rewrite RG. destruct c2_s26_site as (_ & _ & _ & _ & _ & G2 & _). rewrite G2, fsw_SOff0. exact E2v. }
assert (R3 : YK11.getr regsC 3%bv = YK11.getr (c_regs cx) 3%bv).
{ rewrite RG. destruct c2_s26_site as (_ & _ & _ & _ & _ & _ & G3 & _). rewrite G3, fsw_SOff0. exact E3v. }
assert (R4 : YK11.getr regsC 4%bv = YK11.getr (c_regs cx) 4%bv).
{ rewrite RG. destruct c2_s26_site as (_ & _ & _ & _ & _ & _ & _ & G4 & _). rewrite G4, fsw_SOff0. exact E4v. }
(* ---- the boundary's data at the call's memory ---- *)
pose proof (c2_dat0_below B cx ly3 S3 W3 _ _ m3 memC back Ddoc HARC HSB HF4096 HFceil
  (conj Rtext (conj Rback (conj Zback (conj Htree (conj Hpobj2 (conj Hval Hra))))))) as D0c.
pose proof (c2_datf_below B cx ly3 S3 W3 _ _ m3 memC file nfile HARC HSB (conj Rfile (conj Zfile Hwd))) as DFc.
pose proof (pobj_below B ly3 S3 W3 _ _ m3 memC _ HARC HSB Hpobj1) as Hpobj1c.
pose proof (fs_glob_below W3 m3 memC live peak cnt SIZE_MAXZ HSB Hglob) as Hglob1.
(* ---- strlen (file): the runtime pre, the read-only view, file's text as a C string ---- *)
assert (HPRT : ecall_preU_k tfibsegs B STK_RT_STR ly3 S3 U3 W3 regsC memC mdC).
{ eapply (fsw_ecall_preU_k_at B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 U3 W3 memC mdC k regsC
    (crt_sp1 cx - spZ (c_regs cx)) STK_RT_STR HJC HARUC).
  - rewrite R2. lia.
  - rewrite Zminus_mod, Hsp1m, Hal16. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - unfold STK_RT_STR, ESTACK. lia.
  - unfold STK_RT_STR, ESTACK. lia.
  - rewrite R1. vm_compute. reflexivity.
  - rewrite R3. exact Hgp0.
  - rewrite R4. exact Htp0. }
assert (HROc := crt_rodata SK B cx k ly3 S3 U3 W3 (mkst regsC (Z_to_bv 64 PC_strlen) memC (seg_rom tfibsegs)) mdC
  HB HJC HARUC).
pose proof (c2_rom_view ly3 S3 U3 W3 memC mdC HARUC HROc) as Hrom.
pose proof (garr8_bytes_ok tfibsegs _ _ _ Zback) as Hbok.
destruct (check_round_trip_stages_b.crt_doc_ok (c_bs cx) Hbok ltac:(pose proof (c2_bs_len B cx HB); lia))
  as (_ & _ & _ & _ & _ & WNZ & _).
destruct DFc as (Rfile1 & Zfile1 & Hwd1).
pose proof (cstr_ok_of_rblockU B ly3 S3 U3 W3 memC mdC file nfile
  (WriterValue.wdoc (PjTree.JObj (check_round_trip_stages_b.crt_doc (WriterSpec.b64_enc (c_bs cx)))) true)
  HARUC HH Rfile1 ltac:(lia) Zfile1 WNZ) as Hcs.
assert (G10 : YK11.getr regsC 10%bv = w64 file) by (rewrite RG, R10, fsw_SOff0; exact E10).
pose proof (RTS ly3 S3 U3 W3 regsC memC mdC file _ HPRT Hrom G10 Hcs) as HC.
exists [], 0. eexists. split; [exact HC|].
split; [exact (c2_fpsub_nil B _ _ _ _ _ _)|].
split; [intros a _ Ha; exact (inFP_nil a Ha)|].
intros W' c' (-> & regs' & mem' & md' & v & Ec & HAR' & PO' & HP & Hsame & Gv & Hv64 & Hvl & Hfrr & Hgr).
(* the callee's journal: the caller's, restricted to the call's window, moved over its write *)
assert (HJ0 : @ajournal rc SK tfibsegs B STK_RT_STR (spZ regsC) [] ly3 S3 W3 (unpoison U3 memC) mdC []
  ly3 S3 W3 (unpoison U3 memC) mdC 0).
{ eapply ajournal_sub_init with (o := crt_sp1 cx - spZ (c_regs cx)).
  all: first [ exact HJC | (rewrite R2; lia) | (rewrite Zminus_mod, Hsp1m, Hal16; reflexivity)
             | (unfold STK_RT_STR, ESTACK; lia) | lia ]. }
assert (HJ1 : @ajournal rc SK tfibsegs B STK_RT_STR (spZ regsC) [] ly3 S3 W3 (unpoison U3 memC) mdC []
  ly3 S3 W3 (unpoison U3 mem') md' 0).
{ apply (ajournal_after_write tfibsegs B (AR_laws_ok tfibsegs B) fs_segs_low STK_RT_STR (spZ regsC) [] ly3 S3 W3
    (unpoison U3 memC) mdC [] ly3 S3 W3 (unpoison U3 memC) mdC 0 (unpoison U3 mem') md'
    (fun a => spZ regsC - STK_RT_STR <= a < spZ regsC) S3 [] HJ0).
  - exact (crt_unpoison_keep (w_H W3) U3 memC mem' _ Hfrr).
  - exact (crt_unpoison_present (w_H W3) U3 memC mem' Hgr).
  - exact Hsame.
  - intros a Ha. left. left. left. exact Ha.
  - exact HAR'.
  - reflexivity.
  - reflexivity.
  - lia.
  - reflexivity.
  - exact HQT. }
assert (HARU' : ARU tfibsegs B ly3 S3 U3 W3 mem' md') by (split; [exact HAR' | split; [exact OK0 | exact PO']]).
exists ly3, S3, U3, regs', mem', md'.
split; [rewrite Ec; unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [exact HJ1|]. split; [exact OK0|]. split; [exact PO'|]. split; [exact HP|].
intros HJ' _.
(* ---- the boundary's data after the call ---- *)
destruct (c2_dat0_call SK B cx _ _ _ ly3 S3 U3 W3 memC mdC ly3 S3 U3 W3 mem' md' 0 back Ddoc HJ1 HARUC OK0 PO' HH
  (c2_fpok_nil cx) Hin3 EF Hpobj1c D0c) as (Rtext2 & Rback2 & Zback2 & Htree2 & Hpobj2' & Hval2 & Hra2).
destruct (c2_datf_call SK B cx _ _ _ ly3 S3 U3 W3 memC mdC ly3 S3 U3 W3 mem' md' 0 file nfile HJ1 HARUC OK0 PO'
  (c2_fpok_nil cx) Hin3 EF (conj Rfile1 (conj Zfile1 Hwd1))) as (Rfile2 & Zfile2 & _).
assert (NF : forall x, ~ inFP [] x) by (intros x Hx; exact (inFP_nil x Hx)).
assert (Hpobj1' : pobj tfibsegs B ly3 S3 W3 mem' (crt_F cx + 0x140)).
{ eapply (pobj_kept_call B); [exact HJ1 | exact HARUC | exact OK0 | exact PO' | intros x _; exact (NF x)
  | intros a Ha; exfalso; exact (NF a Ha) | exact HH | exact Hpobj1c]. }
assert (Hglob2 : fs_glob tfibsegs W3 mem' live peak cnt SIZE_MAXZ).
{ apply (c2_glob_keep W3 memC mem' live peak cnt SIZE_MAXZ); [|exact Hglob1].
  intros a Ha. pose proof (c2_img_range a Ha). apply Hfrr; [lia|]. rewrite R2. unfold STK_RT_STR, ESTACK. lia. }
(* ---- the next boundary ---- *)
assert (K : forall n, acallee_saved (Z.of_nat n) -> sr_get (ss_regs c2_s26) (Z_to_bv 5 (Z.of_nat n)) = SOff n 0 ->
  ew (Ereg regs' (crt_extra cx)) n = ew E n)
  by (intros n Hc Hr; exact (c2_keep_s E c2_s26 regsC regs' (crt_extra cx) n RG HP Hc Hr)).
assert (E47v : bv_unsigned (ew E 47) = crt_F cx) by (rewrite (crt_E_F cx E HE); apply wz; lia).
hnf.
split.
{ rewrite (ew_Ereg_nat regs' (crt_extra cx) 18 18%bv eq_refl),
    (fsw_pres regsC regs' 18%bv HP ltac:(change (bv_unsigned 18%bv) with 18; unfold acallee_saved; lia)).
  rewrite RG, R18. apply c2_SOff; [exact E47v | lia]. }
split; [rewrite (K 20%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(vm_compute; reflexivity)); exact E20|].
split; [rewrite (K 21%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(vm_compute; reflexivity)); exact E21|].
split; [rewrite (K 23%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(vm_compute; reflexivity)); exact E23|].
split; [rewrite (K 26%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(vm_compute; reflexivity)); exact E26|].
split; [rewrite (K 27%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(vm_compute; reflexivity)); exact E27|].
exists same, nsame, back, file, nfile, Ddoc, live, peak, cnt.
split.
{ rewrite (ew_Ereg_nat regs' (crt_extra cx) 22 22%bv eq_refl),
    (fsw_pres regsC regs' 22%bv HP ltac:(change (bv_unsigned 22%bv) with 22; unfold acallee_saved; lia)).
  rewrite RG, R22, fsw_SOff0. exact E10. }
split; [rewrite (K 24%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(vm_compute; reflexivity)); exact E24|].
split; [rewrite (K 25%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(vm_compute; reflexivity)); exact E25|].
split; [rewrite (ew_Ereg_nat regs' (crt_extra cx) 10 10%bv eq_refl), Gv, Hvl; reflexivity|].
split; [exact Hf0|].
split; [exact HPB|]. split; [exact HPU|]. split; [exact HH|].
split; [exact Rtext2|]. split; [exact Rback2|]. split; [exact Zback2|]. split; [exact Rfile2|].
split; [exact Zfile2|]. split; [exact Hwd|]. split; [exact Hfile4|].
split; [exact Htree2|]. split; [exact Hpobj2'|]. split; [exact Hpobj1'|].
split; [exact Hval2|]. split; [exact Hra2|]. split; [exact Hlivee|]. split; [exact Hglob2|].
split; [exact Hnfc|]. split; [exact Hlive|]. split; [exact Hcnt | lia].
Qed.

(* segment 26: crt_from at the return of the strlen thunk under c2_INV_82238 gives crt_from at the return of pj_write
   under c2_INV_82228 *)
Lemma c2_seg26 : crt_from SK B c2_ss_238 (c2_INV_82238 B) -> crt_from SK B c2_ss_228 (c2_INV_82228 B).
Proof.
apply (c2_seg_call_beq SK B 0x82228 PC_strlen 0x82238 c2_b26 c2_s26 (c2_INV_82228 B) (c2_INV_82238 B) STK_RT_STR
  c2_run26a c2_run26b c2_s26_site ltac:(lia) eq_refl ltac:(unfold STK_RT_STR, ESTACK; lia)
  ltac:(unfold STK_RT_STR, ESTACK; apply Z.leb_le; vm_compute; reflexivity)).
- intros cx E k ly3 S3 U3 W3 ms3 md3 H HARU Hz.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & (same & nsame & back & file & nfile & Ddoc & live & peak & cnt &
    _ & _ & E10 & Hf0 & _ & _ & _ & _ & _ & _ & Rfile & _)).
  pose proof Rfile as (_ & _ & Hnf & _).
  destruct (fsw_rblock_low B ly3 S3 W3 _ _ _ file nfile (ARU_AR tfibsegs B _ _ _ _ _ _ HARU) Rfile) as (L1 & L2).
  pose proof (@YM05.alloc_ceiling_lt rc) as HC47.
  rewrite E10 in Hz. apply (f_equal (@bv_unsigned 64)) in Hz.
  rewrite !Z_to_bv_unsigned, !bv_wrap_small in Hz by (change (bv_modulus 64) with (2 ^ 64); unfold HEAD in *; lia).
  exact (Hf0 Hz).
- exact c2_call26.
Qed.
End s26.

(* ================= segment 27: 0x82238 .. pj_parse (file, len, &back) at 0x82244 .. 0x82248 =================
   The store-free run reaches pj_parse 0x82eac with a0 = s6 = file (atom 22), a1 = the strlen answer |wd| (atom 10),
   a2 = s2 = &back = F + 0x140 (atom 18), ra = 0x82248 (MEASURED by the engine). An instance of
   FSH_crt_site.crt_seg_call; HCALL is pj_parse's contract at text = file (pj_write's block), out = back's object,
   t = the written document, pr = true, under the by-trace room crt_room_C2 (FSH_crt_room.crt_room_C2_holds).
   pj_parse's post (S0, READER e9dc3b32681 / fd1c15a7141) gives `rd_sum D = PjGrammar.held tr` and
   `(length D <= length tr)%nat`: the exit's live equation, and |Dback| for the D groups' allowance and the block bytes. *)
Definition c2_s27 : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL A_pj_parse (crt_ss2 0x82238)).
Lemma c2_run27 : sym_run_toN tfibsegs crt_tbl FUEL A_pj_parse (crt_ss2 0x82238) = (c2_s27, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma c2_s27_site : crt_csite c2_s27 A_pj_parse 0x82248.
Proof. repeat (split; [vm_compute; reflexivity|]). vm_compute. reflexivity. Qed.
Lemma c2_s27_args : sr_get (ss_regs c2_s27) 10%bv = SOff 22 0 /\ sr_get (ss_regs c2_s27) 11%bv = SOff 10 0 /\
  sr_get (ss_regs c2_s27) 12%bv = SOff 18 0.
Proof. repeat split; vm_compute; reflexivity. Qed.
Lemma c2_s27_save : crt_ssave c2_s27.
Proof. apply crt_ssave_dec. vm_compute. reflexivity. Qed.


Section s27. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis PJP : pj_parse_spec (SK := SK) tfibsegs B.

Lemma c2_call27 : crt_hcall SK B c2_s27 A_pj_parse 0x82248 STK_pj_parse (c2_INV_82238 B) (c2_INV_82248 B).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE HINV HJC HARUC Hfr HSB RG HPREc HFRL HTOPc.
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARUC) as HARC.
assert (HEADv : HEAD = 16) by reflexivity.
destruct HINV as (E18 & E20 & E21 & E23 & E26 & E27 &
  (same & nsame & back & file & nfile & Ddoc & live & peak & cnt &
   E22 & E24 & E25 & E10 & Hf0 & HPB & HPU & HH & Rtext & Rback & Zback & Rfile & Zfile & Hwd & Hfile4 &
   Htree & Hpobj2 & Hpobj1 & Hval & Hra & Hlivee & Hglob & Hnfc & Hlive & Hcnt & Hk)).
set (m3 := ms_mem ms3) in *.
set (es := WriterSpec.b64_enc (c_bs cx)) in *.
destruct (crt_F_facts SK B cx _ _ _ _ _ _ _ HJC HARUC Hfr) as (HFal & HF4096 & HFceil & HFapp & HSF1 & HSF2).
pose proof HJC as (_ & HlyC & _). pose proof (crt_F_ly cx _ ly3 HlyC) as EF.
pose proof HJC as (_ & _ & _ & _ & _ & _ & Hnev & Hk0 & _).
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
destruct c2_s27_args as (R10 & R11 & R12).
pose proof (@YM05.alloc_ceiling_lt rc) as HC47.
(* ---- the budgets: crt_base's reserve, the room by trace, the closed values ---- *)
destruct (c2_base_room B cx HB) as ((_ & Hc0 & Hc78) & Hl0 & Hev0 & Hbb0).
pose proof (crt_live0 B cx HB) as Hlv0.
destruct (FSH_crt_room.crt_room_C2_holds B cx HB) as (RK & RC & RL).
unfold crt_TR, crt_trlen, crt_es in RK, RC, RL. fold es in RK, RC, RL. unfold EV_fuzz_malloc, EV_fuzz_free, CRT_EV_WRAP in RK.
destruct (c2_TR15 es) as (Tev & Tlen).
destruct (c2_KC_vals cx) as (KV & CV).
pose proof (c2_wcalls_le (crt_wst cx)) as (Hwc & Hwv).
pose proof (c2_rd_live_ge (PjRoundTrip.ttrace (PjTree.JObj (check_round_trip_stages_b.crt_doc es)))) as (Hrl & Hrl0).
pose proof (c2_LIVE18_nonneg cx) as HL18.
(* ---- the boundary's data at the call's memory ---- *)
pose proof (c2_dat0_below B cx ly3 S3 W3 _ _ m3 memC back Ddoc HARC HSB HF4096 HFceil
  (conj Rtext (conj Rback (conj Zback (conj Htree (conj Hpobj2 (conj Hval Hra))))))) as D0c.
pose proof (c2_datf_below B cx ly3 S3 W3 _ _ m3 memC file nfile HARC HSB (conj Rfile (conj Zfile Hwd))) as DFc.
pose proof (pobj_below B ly3 S3 W3 _ _ m3 memC _ HARC HSB Hpobj1) as Hpobj1c.
pose proof (fs_glob_below W3 m3 memC live peak cnt SIZE_MAXZ HSB Hglob) as Hglob1.
destruct DFc as (Rfile1 & Zfile1 & Hwd1).
(* ---- the document's facts ---- *)
pose proof (garr8_bytes_ok tfibsegs _ _ _ Zback) as Hbok.
destruct (check_round_trip_stages_b.crt_doc_ok (c_bs cx) Hbok ltac:(pose proof (c2_bs_len B cx HB); lia))
  as (WF & Hdd & _ & TF & _ & _ & _ & _ & _).
fold es in WF, Hdd, TF.
(* ---- the live bytes held so far: crt_INV_82218's blocks plus the file ---- *)
assert (Hns : 0 <= nsame).
{ assert (Hin : In (same, nsame) (ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPB)). apply in_or_app. right. apply in_or_app. left. cbn. tauto. }
  destruct (al_blocks tfibsegs B (AR_laws_ok tfibsegs B) ly3 S3 W3 _ mdC same nsame HARC Hin) as (_ & _ & _ & _ & _ & _ & Hm).
  lia. }
pose proof (c2_rd_sum_le B ly3 S3 (c_ly cx) (c_S cx) _ Ddoc HPB) as Hbb.
unfold YCbq.bsum in Hbb. cbn [fold_right snd] in Hbb.
pose proof Rtext as (_ & _ & Hent & _).
destruct Htree as (_ & HBdoc & _).
pose proof (crt_rd_sum_pos B ly3 S3 W3 m3 Ddoc HBdoc) as Hsd.
(* ---- pj_parse (file, |wd|, &back) ---- *)
assert (G10 : YK11.getr regsC 10%bv = w64 file) by (rewrite RG, R10, fsw_SOff0; exact E22).
assert (G11 : YK11.getr regsC 11%bv =
  w64 (Z.of_nat (length (WriterValue.wdoc (PjTree.JObj (check_round_trip_stages_b.crt_doc es)) true))))
  by (rewrite RG, R11, fsw_SOff0; exact E10).
assert (G12 : YK11.getr regsC 12%bv = w64 (crt_F cx + 0x140)) by (rewrite RG, R12, fsw_SOff0; exact E18).
assert (Hra1 : raZ regsC = 0x82248).
{ unfold raZ. rewrite RG. destruct c2_s27_site as (_ & _ & _ & G1 & _). rewrite G1. reflexivity. }
pose proof HPREc as (((_ & _ & _ & _ & _ & (_ & _ & Hac & Hstp & _) & _) & _) & _).
pose proof (sep_block_frame tfibsegs B (AR_laws_ok tfibsegs B) ly3 S3 W3 _ mdC (file - HEAD) (nfile + HEAD) 3 (c_pos cx)
  HARC (proj1 Rfile1) Hin3) as Hdisj.
unfold zdisjoint in Hdisj. cbn [fst snd] in Hdisj. rewrite EF, crt_frame3, c2_rq in Hdisj by (pose proof Rfile1 as (_ & _ & Hn & _); exact Hn).
pose proof (PJP ly3 S3 U3 W3 regsC memC mdC _ file
  (Z.of_nat (length (WriterValue.wdoc (PjTree.JObj (check_round_trip_stages_b.crt_doc es)) true)))
  (crt_F cx + 0x140) nfile (PjTree.JObj (check_round_trip_stages_b.crt_doc es)) true live peak cnt SIZE_MAXZ
  HPREc HH HFRL G10 G11 G12 (conj Hfile4 (conj Rfile1 Hwd1)) Zfile1 eq_refl WF Hdd
  (FSDocStrs.FS_DOC_STRS_values es) (FSDocStrs.FS_DOC_STRS_strings (c_bs cx) Hbok) Hpobj1c
  ltac:(left; lia) ltac:(lia) Hglob1 ltac:(split; [reflexivity | split; lia])
  ltac:(eapply Forall_impl; [|exact TF]; intros e He; cbv beta in *;
        unfold check_round_trip_c.CRT_SIZE, MALLOC_MAX, HEAD in *; change (2 ^ 25) with 33554432 in He;
        change (2 ^ 28) with 268435456; lia)
  ltac:(lia) ltac:(lia) ltac:(lia)) as HC.
exists ([(crt_F cx + 0x140, crt_F cx + 0x140 + 56)] ++ FS_PSTAT_FP),
  (rd_ev (PjRoundTrip.ttrace (PjTree.JObj (check_round_trip_stages_b.crt_doc es)))).
eexists. split; [exact HC|].
split.
{ pose proof (c2_fpsub_obj B (c_ly cx) (c_S cx) ly3 S3 (c_pos cx) 0x140 ltac:(lia) ltac:(lia)) as X.
  rewrite EF in X. exact X. }
split.
{ intros a Ha Hf. apply inFP_app in Hf as [Hf | Hf].
  - apply inFP_cons in Hf as [Hf | Hf]; [|exact (inFP_nil a Hf)].
    unfold in_zr in Hf. cbn [fst snd] in Hf. rewrite crt_frame3 in Ha. lia.
  - exact (frm_img tfibsegs B (AR_laws_ok tfibsegs B) ly3 S3 W3 _ mdC 3 (c_pos cx) a HARC Hin3
      ltac:(rewrite EF, crt_frame3; rewrite crt_frame3 in Ha; lia) (crt_pstat_img a Hf)). }
intros W' c' (D & Da & HDa & ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HP & HQ).
exists ly', S', (U3 ++ rd_heads Da), regs', mem', md'.
split; [exact Ec|]. split; [exact HJc|]. split; [exact OK'|]. split; [exact PO'|]. split; [exact HP|].
intros HJ' HARU'.
destruct HQ as (G0 & HPerm & HtreeD & HheldD & HlenD & Hpobjb & _ & _ & (peak' & Hpk & Hglob2)).
pose proof HtreeD as (HND & HBD & _).
(* ---- the heads after the call: U's and the parsed tree's ---- *)
assert (HH' : FSupoisonU.fs_heads B ly' S' (U3 ++ rd_heads Da)).
{ intros r Hr. apply in_app_or in Hr as [Hr | Hr].
  - destruct (HH r Hr) as (H16 & m & Hm & Hrq). split; [exact H16|]. exists m. split; [|exact Hrq].
    apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. left. exact Hm.
  - unfold rd_heads in Hr. apply in_map_iff in Hr as ((a & kk) & <- & Hak).
    apply (Permutation_in _ HDa) in Hak.
    pose proof (HBD a kk Hak) as (_ & _ & Hkk & _).
    cbn [fst snd]. split; [reflexivity|]. exists (kk + HEAD). split.
    + apply (Permutation_in _ (Permutation_sym HPerm)). apply in_or_app. right. unfold rd_hblocks.
      apply in_map_iff. exists (a, kk). split; [reflexivity | exact Hak].
    + rewrite c2_rq by exact Hkk. lia. }
(* ---- the boundary's data after the call (pj_parse writes back's object and the statics only) ---- *)
destruct (c2_dat0_call SK B cx _ _ _ ly3 S3 U3 W3 memC mdC ly' S' (U3 ++ rd_heads Da) W' mem' md' _ back Ddoc HJc HARUC
  OK' PO' HH' (c2_fpok_back cx) Hin3 EF Hpobj1c D0c) as (Rtext2 & Rback2 & Zback2 & Htree2 & Hpobj2' & Hval2 & Hra2).
destruct (c2_datf_call SK B cx _ _ _ ly3 S3 U3 W3 memC mdC ly' S' (U3 ++ rd_heads Da) W' mem' md' _ file nfile HJc HARUC
  OK' PO' (c2_fpok_back cx) Hin3 EF (conj Rfile1 (conj Zfile1 Hwd1))) as (Rfile2 & Zfile2 & _).
pose proof Htree2 as (_ & HBd2 & _).
assert (Hnode2 : rnode tfibsegs B ly' S' W' mem' (Ddoc ++ D) (crt_F cx + 0x140)
  (PjTree.JObj (check_round_trip_stages_b.crt_doc es)) D).
{ split; [|split].
  - apply (PjStruct.pj_node_frame tfibsegs _ (mrestrict (w_H W') mem') (fun a k => In (a, k) D)
      (mrestrict (w_H W') mem') (fun a k => In (a, k) (Ddoc ++ D)) _ D HND).
    + intros a kk Hak. apply in_or_app. right. exact Hak.
    + intros x _. reflexivity.
  - intros a kk Hak. apply in_app_or in Hak as [Hak | Hak]; [exact (HBd2 a kk Hak) | exact (HBD a kk Hak)].
  - intros bk Hbk. apply in_or_app. right. exact Hbk. }
(* ---- the budgets after the call ---- *)
pose proof (c2_rd_sum_le B ly' S' ly3 S3 [] D ltac:(rewrite app_nil_l; exact HPerm)) as Hbb'.
unfold YCbq.bsum in Hbb'. cbn [fold_right] in Hbb'.
(* ---- the next boundary ---- *)
assert (K : forall n, acallee_saved (Z.of_nat n) -> sr_get (ss_regs c2_s27) (Z_to_bv 5 (Z.of_nat n)) = SOff n 0 ->
  ew (Ereg regs' (crt_extra cx)) n = ew E n)
  by (intros n Hc Hr; exact (c2_keep_s E c2_s27 regsC regs' (crt_extra cx) n RG HP Hc Hr)).
hnf.
split; [rewrite (ew_Ereg_nat regs' (crt_extra cx) 10 10%bv eq_refl); exact G0|].
split; [rewrite (K 18%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s27_save; lia)); exact E18|].
split; [rewrite (K 20%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s27_save; lia)); exact E20|].
split; [rewrite (K 21%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s27_save; lia)); exact E21|].
split; [rewrite (K 23%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s27_save; lia)); exact E23|].
split; [rewrite (K 26%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s27_save; lia)); exact E26|].
split; [rewrite (K 27%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s27_save; lia)); exact E27|].
exists same, nsame, back, file, nfile, Ddoc, D,
  (live + PjGrammar.held (PjRoundTrip.ttrace (PjTree.JObj (check_round_trip_stages_b.crt_doc es)))), peak',
  (cnt + Z.of_nat (length (PjRoundTrip.ttrace (PjTree.JObj (check_round_trip_stages_b.crt_doc es))))).
split; [rewrite (K 22%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s27_save; lia)); exact E22|].
split; [rewrite (K 24%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s27_save; lia)); exact E24|].
split; [rewrite (K 25%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s27_save; lia)); exact E25|].
split.
{ eapply perm_trans; [exact HPerm|]. eapply perm_trans; [apply Permutation_app_tail; exact HPB|].
  unfold rd_hblocks. rewrite map_app. fold (rd_hblocks Ddoc). fold (rd_hblocks D).
  rewrite <- !app_assoc. apply Permutation_refl. }
split.
{ eapply perm_trans; [apply Permutation_app_tail; exact HPU|].
  unfold rd_heads. rewrite map_app. fold (rd_heads Ddoc). fold (rd_heads D).
  rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_head.
  apply Permutation_map. exact HDa. }
split; [exact HH'|].
split; [exact Rtext2|]. split; [exact Rback2|]. split; [exact Zback2|]. split; [exact Rfile2|].
split; [exact Zfile2|]. split; [exact Hwd|]. split; [exact Hfile4|].
split; [exact Htree2|]. split; [exact Hnode2|]. split; [exact Hpobjb|]. split; [exact Hpobj2'|].
split; [exact Hval2|]. split; [exact Hra2|].
unfold es in *.
split; [rewrite crt_rd_sum_app; lia|].
split; [exact Hglob2|].
assert (HlD : Z.of_nat (length D) <=
  Z.of_nat (length (PjRoundTrip.ttrace (PjTree.JObj (check_round_trip_stages_b.crt_doc (WriterSpec.b64_enc (c_bs cx)))))))
  by (apply Nat2Z.inj_le; exact HlenD).
split.
{ rewrite Hbb', HheldD. unfold LIVE_82268, crt_TR, crt_es. unfold HEAD in *. lia. }
split; [unfold CNT_82268, crt_trlen, crt_TR, crt_es; lia|].
unfold crt_TR, crt_es.
split; [lia | exact HlenD].
Qed.

(* segment 27: crt_from at the return of pj_parse under c2_INV_82248 gives crt_from at the return of the strlen thunk
   under c2_INV_82238 *)
Lemma c2_seg27 : crt_from SK B c2_ss_248 (c2_INV_82248 B) -> crt_from SK B c2_ss_238 (c2_INV_82238 B).
Proof.
exact (crt_seg_call SK B 0x82238 A_pj_parse 0x82248 c2_s27 (c2_INV_82238 B) (c2_INV_82248 B) STK_pj_parse
  c2_run27 c2_s27_site ltac:(lia) eq_refl ltac:(apply Z.leb_le; vm_compute; reflexivity)
  ltac:(apply Z.leb_le; vm_compute; reflexivity) c2_call27).
Qed.
End s27.

(* ================= segment 28: 0x82248 .. `bnez a0` .. pj_get (&back, "state") at 0x82258 .. 0x8225c =================
   pj_parse returned 0 (c2_INV_82248's a0), so the `bnez a0` to the abort tail is not taken; the run then reaches
   pj_get 0x83720 with a0 = s2 = &back (atom 18), a1 = "state" 0x20f00, ra = 0x8225c (MEASURED by the engine). An
   instance of FSH_crt_site.crt_seg_call_br; HCALL is pj_get_spec at o = &back (the parsed document), D = Dback,
   UL = Ddoc ++ Dback; FP = [], no tick, U unchanged. Its answer is the "state" member: a node of back's kids array
   (rd_get_hit), so a heap pobj (c2_pobj_kid) with its own blocks inside Dback. *)
Definition c2_b28 : sstate := Eval vm_compute in fst (sym_runN tfibsegs crt_tbl FUEL (crt_ss2 0x82248)).
Lemma c2_run28a :
  sym_runN tfibsegs crt_tbl FUEL (crt_ss2 0x82248) = (c2_b28, RS_stopped (SR_branch BC_NE (SOff 10 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition c2_s28 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL A_pj_get (add_cond c2_b28 crt_c0)).
Lemma c2_run28b : sym_run_toN tfibsegs crt_tbl FUEL A_pj_get (add_cond c2_b28 crt_c0) = (c2_s28, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma c2_s28_site : crt_site c2_b28 c2_s28 A_pj_get 0x8225c.
Proof. split; [vm_compute; reflexivity|]. repeat (split; [vm_compute; reflexivity|]). vm_compute. reflexivity. Qed.
Lemma c2_s28_args : sr_get (ss_regs c2_s28) 10%bv = SOff 18 0 /\ sr_get (ss_regs c2_s28) 11%bv = SLit 0x20f00.
Proof. split; vm_compute; reflexivity. Qed.
Lemma c2_s28_save : crt_ssave c2_s28.
Proof. apply crt_ssave_dec. vm_compute. reflexivity. Qed.

Section s28. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis PJG : pj_get_spec (SK := SK) tfibsegs B.

Lemma c2_call28 : crt_hcall SK B c2_s28 A_pj_get 0x8225c STK_pj_get (c2_INV_82248 B) (c2_INV_8225c B).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE HINV HJC HARUC Hfr HSB RG HPREc HFRL HTOPc.
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARUC) as HARC.
assert (HEADv : HEAD = 16) by reflexivity.
destruct HINV as (E10 & E18 & E20 & E21 & E23 & E26 & E27 &
  (same & nsame & back & file & nfile & Ddoc & Dback & live & peak & cnt &
   E22 & E24 & E25 & HPB & HPU & HH & Rtext & Rback & Zback & Rfile & Zfile & Hwd & Hfile4 &
   Htree & Hnode & Hpobj1 & Hpobj2 & Hval & Hra & Hlivee & Hglob & Hlive & Hcnt & Hk & HlD)).
set (m3 := ms_mem ms3) in *.
destruct (crt_F_facts SK B cx _ _ _ _ _ _ _ HJC HARUC Hfr) as (HFal & HF4096 & HFceil & HFapp & HSF1 & HSF2).
pose proof HJC as (_ & HlyC & _). pose proof (crt_F_ly cx _ ly3 HlyC) as EF.
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
destruct c2_s28_args as (R10 & R11).
(* ---- the boundary's data at the call's memory ---- *)
destruct (fsw_pobj_low B ly3 S3 W3 _ _ m3 (crt_F cx + 0x140) HARC Hpobj1) as (L1a & L1b).
pose proof (c2_dat0_below B cx ly3 S3 W3 _ _ m3 memC back Ddoc HARC HSB HF4096 HFceil
  (conj Rtext (conj Rback (conj Zback (conj Htree (conj Hpobj2 (conj Hval Hra))))))) as D0c.
pose proof (c2_datf_below B cx ly3 S3 W3 _ _ m3 memC file nfile HARC HSB (conj Rfile (conj Zfile Hwd))) as DFc.
pose proof (rnode_below B ly3 S3 W3 _ _ m3 memC (Ddoc ++ Dback) (crt_F cx + 0x140) _ Dback HARC HSB ltac:(lia) ltac:(lia)
  Hnode) as Hnode1.
pose proof (pobj_below B ly3 S3 W3 _ _ m3 memC _ HARC HSB Hpobj1) as Hpobj1c.
pose proof (fs_glob_below W3 m3 memC live peak cnt SIZE_MAXZ HSB Hglob) as Hglob1.
(* ---- pj_get (&back, "state") ---- *)
assert (G10 : YK11.getr regsC 10%bv = w64 (crt_F cx + 0x140)) by (rewrite RG, R10, fsw_SOff0; exact E18).
assert (G11 : YK11.getr regsC 11%bv = w64 0x20f00) by (rewrite RG, R11; reflexivity).
destruct (c2_key SK B IMG cx k ly3 S3 U3 W3 (mkst regsC (Z_to_bv 64 A_pj_get) memC (seg_rom tfibsegs)) mdC
  0x20f00 [115; 116; 97; 116; 101] HB HJC HARUC c2_in_state) as (Hkok & Hkept).
pose proof (PJG ly3 S3 U3 W3 regsC memC mdC _ (crt_F cx + 0x140) 0x20f00 [115; 116; 97; 116; 101]
  (PjTree.JObj (check_round_trip_stages_b.crt_doc (WriterSpec.b64_enc (c_bs cx)))) Dback (Ddoc ++ Dback) live peak cnt
  SIZE_MAXZ HPREc HH G10 G11 (or_intror (conj Hnode1 Hpobj1c)) Hkok Hkept Hglob1) as HC.
exists [], 0. eexists. split; [exact HC|].
split; [exact (c2_fpsub_nil B _ _ _ _ _ _)|].
split; [intros a _ Ha; exact (inFP_nil a Ha)|].
intros W' c' (ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HP & HQ).
exists ly', S', U3, regs', mem', md'.
split; [exact Ec|]. split; [exact HJc|]. split; [exact OK'|]. split; [exact PO'|]. split; [exact HP|].
intros HJ' HARU'.
destruct HQ as (Hab & _ & _ & Hglob2 & [(Hzz & _) | (_ & Hnode2 & z & Gz & Hres)]); [lia|].
pose proof HARU' as (HAR' & _ & _).
assert (HH' : FSupoisonU.fs_heads B ly' S' U3) by (intros rr Hr; rewrite Hab; exact (HH rr Hr)).
(* ---- the answer: the "state" member, a node of back's kids array ---- *)
cbn [rd_get_res] in Hres.
destruct Hres as [(Hnm & _) | (i & v & kids & Di & Hnth & _ & Hk24 & Ez & Hnd & Hincl)].
{ exfalso. exact (Hnm _ _ (c2_doc_has_state (WriterSpec.b64_enc (c_bs cx))) eq_refl). }
destruct (c2_doc_state _ _ _ Hnth) as (-> & ->).
pose proof Hnode2 as (HNb & HBb & HIb).
destruct (c2_obj_kid _ _ _ _ _ _ _ _ _ kids HNb Hnth Hk24) as (cap & Hcap & Hkb).
pose proof (HBb kids (56 * cap) Hkb) as Rkids.
pose proof (c2_pobj_kid B ly' S' U3 W' mem' md' kids cap z HARU' HH' Rkids ltac:(lia) ltac:(lia)
  ltac:(rewrite Ez; Z.div_mod_to_equations; lia)) as Hzpobj.
destruct (fsw_pobj_low B ly' S' W' _ _ mem' z HAR' Hzpobj) as (Lz1 & _).
(* ---- the boundary's data after the call ---- *)
assert (NF : forall x, ~ inFP [] x) by (intros x Hx; exact (inFP_nil x Hx)).
destruct (c2_dat0_call SK B cx _ _ _ ly3 S3 U3 W3 memC mdC ly' S' U3 W' mem' md' 0 back Ddoc HJc HARUC OK' PO' HH'
  (c2_fpok_nil cx) Hin3 EF Hpobj1c D0c) as (Rtext2 & Rback2 & Zback2 & Htree2 & Hpobj2' & Hval2 & Hra2).
destruct (c2_datf_call SK B cx _ _ _ ly3 S3 U3 W3 memC mdC ly' S' U3 W' mem' md' 0 file nfile HJc HARUC OK' PO'
  (c2_fpok_nil cx) Hin3 EF DFc) as (Rfile2 & Zfile2 & _).
assert (Hpobj1' : pobj tfibsegs B ly' S' W' mem' (crt_F cx + 0x140)).
{ eapply (pobj_kept_call B); [exact HJc | exact HARUC | exact OK' | exact PO' | intros x _; exact (NF x)
  | intros a Ha; exfalso; exact (NF a Ha) | exact HH' | exact Hpobj1c]. }
(* ---- the next boundary ---- *)
assert (K : forall n, acallee_saved (Z.of_nat n) -> sr_get (ss_regs c2_s28) (Z_to_bv 5 (Z.of_nat n)) = SOff n 0 ->
  ew (Ereg regs' (crt_extra cx)) n = ew E n)
  by (intros n Hc Hr; exact (c2_keep_s E c2_s28 regsC regs' (crt_extra cx) n RG HP Hc Hr)).
hnf.
split; [rewrite (K 18%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s28_save; lia)); exact E18|].
split; [rewrite (K 20%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s28_save; lia)); exact E20|].
split; [rewrite (K 21%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s28_save; lia)); exact E21|].
split; [rewrite (K 23%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s28_save; lia)); exact E23|].
split; [rewrite (K 26%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s28_save; lia)); exact E26|].
split; [rewrite (K 27%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s28_save; lia)); exact E27|].
exists same, nsame, back, file, nfile, z, Ddoc, Dback, Di, live, peak, cnt.
split; [rewrite (K 22%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s28_save; lia)); exact E22|].
split; [rewrite (K 24%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s28_save; lia)); exact E24|].
split; [rewrite (K 25%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s28_save; lia)); exact E25|].
split; [rewrite (ew_Ereg_nat regs' (crt_extra cx) 10 10%bv eq_refl); exact Gz|].
split; [lia|].
split; [rewrite Hab; exact HPB|]. split; [exact HPU|]. split; [exact HH'|].
split; [exact Rtext2|]. split; [exact Rback2|]. split; [exact Zback2|]. split; [exact Rfile2|].
split; [exact Zfile2|]. split; [exact Hwd|]. split; [exact Hfile4|].
split; [exact Htree2|]. split; [exact Hnode2|].
split; [split; [exact Hnd|]; split; [exact HBb|]; intros bk Hbk; exact (HIb bk (Hincl bk Hbk))|].
split; [exact Hzpobj|]. split; [exact Hincl|].
split; [exact Hpobj1'|]. split; [exact Hpobj2'|].
split; [exact Hval2|]. split; [exact Hra2|]. split; [exact Hlivee|]. split; [exact Hglob2|].
split; [rewrite (blocks_bytes_bsum B ly' S'), Hab, <- (blocks_bytes_bsum B ly3 S3); exact Hlive|].
split; [exact Hcnt|]. split; [lia | exact HlD].
Qed.

(* segment 28: crt_from at the return of pj_get under c2_INV_8225c gives crt_from at the return of pj_parse under
   c2_INV_82248 *)
Lemma c2_seg28 : crt_from SK B c2_ss_25c (c2_INV_8225c B) -> crt_from SK B c2_ss_248 (c2_INV_82248 B).
Proof.
exact (crt_seg_call_br SK B 0x82248 A_pj_get 0x8225c c2_b28 c2_s28 (c2_INV_82248 B) (c2_INV_8225c B) STK_pj_get
  c2_run28a c2_run28b c2_s28_site ltac:(lia) eq_refl ltac:(apply Z.leb_le; vm_compute; reflexivity)
  ltac:(apply Z.leb_le; vm_compute; reflexivity) (fun _ _ _ _ _ _ _ _ _ H => proj1 H) c2_call28).
Qed.
End s28.

(* ================= segment 29: 0x8225c .. pj_get_str (r, "bytes") at 0x82264 .. 0x82268 =================
   The run from the boundary without the frame's regions (FSH_crt_site.crt_ss2) is store-free and reaches pj_get_str 0x83868 with
   a0 = r (pj_get's answer, atom 10), a1 = "bytes" 0x20fc0, ra = 0x82268 (MEASURED by the engine). The segment is an
   instance of FSH_crt_site.crt_seg_call; its HCALL (crt_hcall) is pj_get_str_spec at o = r (the state object), D = Dz, UL = Ddoc ++ Dback; FP = [], no tick, U
   unchanged. The exit's cstr_ok is built from the string's block (cstr_ok_of_rblockU); its D allowance (base v20) is
   paid from the by-trace budget (the base's crt_room_C2), |Dback| <= |crt_TR cx| (pj_parse's post) and |Ddoc| = 15
   (c2_doc_blocks). *)
Definition c2_s29 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crt_tbl FUEL A_pj_get_str (crt_ss2 0x8225c)).
Lemma c2_run29 : sym_run_toN tfibsegs crt_tbl FUEL A_pj_get_str (crt_ss2 0x8225c) = (c2_s29, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma c2_s29_site : crt_csite c2_s29 A_pj_get_str 0x82268.
Proof. repeat (split; [vm_compute; reflexivity|]). vm_compute. reflexivity. Qed.
Lemma c2_s29_args : sr_get (ss_regs c2_s29) 10%bv = SOff 10 0 /\ sr_get (ss_regs c2_s29) 11%bv = SLit 0x20fc0.
Proof. split; vm_compute; reflexivity. Qed.
Lemma c2_s29_save : crt_ssave c2_s29.
Proof. apply crt_ssave_dec. vm_compute. reflexivity. Qed.

Section s29. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis PJGS : pj_get_str_spec (SK := SK) tfibsegs B.

Lemma c2_call29 : crt_hcall SK B c2_s29 A_pj_get_str 0x82268 STK_pj_get_str (c2_INV_8225c B) (crt_INV_82268 B).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE HINV HJC HARUC Hfr HSB RG HPREc HFRL HTOPc.
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARUC) as HARC.
assert (HEADv : HEAD = 16) by reflexivity.
destruct HINV as (E18 & E20 & E21 & E23 & E26 & E27 &
  (same & nsame & back & file & nfile & z & Ddoc & Dback & Dz & live & peak & cnt &
   E22 & E24 & E25 & E10 & Hz0 & HPB & HPU & HH & Rtext & Rback & Zback & Rfile & Zfile & Hwd & Hfile4 &
   Htree & Hnode & Hznode & Hzpobj & Hzincl & Hpobj1 & Hpobj2 & Hval & Hra & Hlivee & Hglob & Hlive & Hcnt & Hk & HlD)).
set (m3 := ms_mem ms3) in *.
pose proof (c2_doc_blocks _ _ _ _ _ _ (proj1 Htree)) as HDdoc.
destruct (crt_F_facts SK B cx _ _ _ _ _ _ _ HJC HARUC Hfr) as (HFal & HF4096 & HFceil & HFapp & HSF1 & HSF2).
pose proof HJC as (_ & HlyC & _). pose proof (crt_F_ly cx _ ly3 HlyC) as EF.
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
destruct c2_s29_args as (R10 & R11).
(* ---- the boundary's data at the call's memory (the run wrote only stack) ---- *)
destruct (fsw_rblock_low B ly3 S3 W3 _ _ m3 back _ HARC Rback) as (Lb1 & Lb2).
pose proof (c2_bs_dec (c_bs cx)) as Lbs.
destruct (fsw_pobj_low B ly3 S3 W3 _ _ m3 (crt_F cx + 0x140) HARC Hpobj1) as (L1a & L1b).
destruct (fsw_pobj_low B ly3 S3 W3 _ _ m3 (crt_F cx + 0x20) HARC Hpobj2) as (L2a & L2b).
destruct (fsw_pobj_low B ly3 S3 W3 _ _ m3 z HARC Hzpobj) as (Lza & Lzb).
pose proof (fs_rblock_below B ly3 S3 W3 _ _ m3 memC _ _ HARC HSB Rtext) as Rtext1.
pose proof (fs_rblock_below B ly3 S3 W3 _ _ m3 memC _ _ HARC HSB Rback) as Rback1.
pose proof (fs_rblock_below B ly3 S3 W3 _ _ m3 memC _ _ HARC HSB Rfile) as Rfile1.
pose proof (c2_garr8_below (w_H W3) m3 memC back (c_bs cx) HSB ltac:(lia) ltac:(lia) Zback) as Zback1.
pose proof (rnode_below B ly3 S3 W3 _ _ m3 memC Ddoc (crt_F cx + 0x20) _ Ddoc HARC HSB ltac:(lia) ltac:(lia) Htree)
  as Htree1.
pose proof (rnode_below B ly3 S3 W3 _ _ m3 memC (Ddoc ++ Dback) (crt_F cx + 0x140) _ Dback HARC HSB ltac:(lia) ltac:(lia)
  Hnode) as Hnode1.
pose proof (rnode_below B ly3 S3 W3 _ _ m3 memC (Ddoc ++ Dback) z _ Dz HARC HSB ltac:(lia) ltac:(lia) Hznode)
  as Hznode1.
pose proof (pobj_below B ly3 S3 W3 _ _ m3 memC _ HARC HSB Hpobj1) as Hpobj1c.
pose proof (pobj_below B ly3 S3 W3 _ _ m3 memC _ HARC HSB Hpobj2) as Hpobj2c.
pose proof (pobj_below B ly3 S3 W3 _ _ m3 memC _ HARC HSB Hzpobj) as Hzpobjc.
pose proof (val_mem_below (w_H W3) m3 memC alloc_ceiling (crt_F cx + 0x1a0) 8 0 HSB ltac:(lia)
  ltac:(change (Z.of_nat 8) with 8; lia) Hval) as Hval1.
pose proof (fsw_range_addressable_below (w_H W3) m3 memC (crt_F cx + 0x1a0) 8 HSB ltac:(lia) ltac:(lia) Hra) as Hra1.
pose proof (fs_glob_below W3 m3 memC live peak cnt SIZE_MAXZ HSB Hglob) as Hglob1.
(* ---- pj_get_str (r, "bytes") ---- *)
assert (G10 : YK11.getr regsC 10%bv = w64 z) by (rewrite RG, R10, fsw_SOff0; exact E10).
assert (G11 : YK11.getr regsC 11%bv = w64 0x20fc0) by (rewrite RG, R11; reflexivity).
destruct (c2_key SK B IMG cx k ly3 S3 U3 W3 (mkst regsC (Z_to_bv 64 A_pj_get_str) memC (seg_rom tfibsegs)) mdC
  0x20fc0 [98; 121; 116; 101; 115] HB HJC HARUC c2_in_bytes) as (Hkok & Hkept).
pose proof (PJGS ly3 S3 U3 W3 regsC memC mdC _ z 0x20fc0 [98; 121; 116; 101; 115]
  (PjTree.JObj (check_round_trip_stages_b.crt_st (WriterSpec.b64_enc (c_bs cx)))) Dz (Ddoc ++ Dback) live peak cnt
  SIZE_MAXZ HPREc HH G10 G11 (or_intror (conj Hznode1 Hzpobjc)) Hkok Hkept Hglob1) as HC.
exists [], 0. eexists. split; [exact HC|].
split; [exact (c2_fpsub_nil B _ _ _ _ _ _)|].
split; [intros a _ Ha; exact (inFP_nil a Ha)|].
intros W' c' (ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HP & HQ).
exists ly', S', U3, regs', mem', md'.
split; [exact Ec|]. split; [exact HJc|]. split; [exact OK'|]. split; [exact PO'|]. split; [exact HP|].
intros HJ' HARU'.
destruct HQ as (Hab & _ & _ & Hglob2 & [(Hzz & _) | (_ & Hzn2 & z' & Gz & Hres)]); [exfalso; exact (Hz0 Hzz)|].
pose proof HARU' as (HAR' & _ & _).
assert (HH' : FSupoisonU.fs_heads B ly' S' U3) by (intros rr Hr; rewrite Hab; exact (HH rr Hr)).
assert (NF : forall x, ~ inFP [] x) by (intros x Hx; exact (inFP_nil x Hx)).
(* ---- the answer: the "bytes" string of the state object, a block of Dz ---- *)
cbn [rd_get_str_res] in Hres.
destruct Hres as [(Hnm & _) | (i & v & kids & Hnth & _ & _ & Hv)].
{ exfalso. exact (Hnm _ _ (c2_st_has_bytes (WriterSpec.b64_enc (c_bs cx))) eq_refl). }
pose proof (c2_st_bytes _ _ _ Hnth) as ->.
destruct Hv as (_ & nz & (Hul & Hlen & Hcb) & Hinz).
destruct Hzn2 as (_ & HBz & _).
pose proof (HBz z' nz Hul) as Rz.
destruct (fsw_rblock_low B ly' S' W' _ _ mem' z' nz HAR' Rz) as (Lz1 & _).
destruct (c2_garr8_of_cbytes _ _ _ Hcb) as (Gg & Gnz).
(* ---- the boundary's data after the call (FP = []: the journal keeps every block and frame byte) ---- *)
assert (Rtext2 : fs_rblock tfibsegs B ly' S' W' mem' (c_text cx)
  (FSH_Fn_writer.enc_size (Z.of_nat (length (c_bs cx))))).
{ eapply (fs_rblock_kept_call B); [exact HJc | exact HARUC | exact OK' | exact PO' | intros x _; exact (NF x) | exact Rtext1]. }
assert (Rback2 : fs_rblock tfibsegs B ly' S' W' mem' back
  (FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)))).
{ eapply (fs_rblock_kept_call B); [exact HJc | exact HARUC | exact OK' | exact PO' | intros x _; exact (NF x) | exact Rback1]. }
assert (Rfile2 : fs_rblock tfibsegs B ly' S' W' mem' file nfile).
{ eapply (fs_rblock_kept_call B); [exact HJc | exact HARUC | exact OK' | exact PO' | intros x _; exact (NF x) | exact Rfile1]. }
assert (Zback2 : zbytes_at tfibsegs W' mem' back (c_bs cx)).
{ pose proof Rback1 as (Hinb & _ & Hnb & _). unfold zbytes_at.
  apply (c2_garr8_kept_blk SK B _ _ _ ly3 S3 U3 W3 memC mdC ly' S' U3 W' mem' md' 0 (back - HEAD)
    (FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD) back (c_bs cx) HJc HARUC OK' PO' Hinb);
    [lia | rewrite c2_rq by exact Hnb; lia | intros x _; exact (NF x) | exact Zback1]. }
assert (Htree2 : rtree tfibsegs B ly' S' W' mem' (crt_F cx + 0x20)
  (PjTree.JObj (check_round_trip_stages_b.crt_doc (WriterSpec.b64_enc (c_bs cx)))) Ddoc).
{ eapply (rtree_kept_call B); [exact HJc | exact HARUC | exact OK' | exact PO' | intros x _; exact (NF x)
  | intros a kk x _ _; exact (NF x) | exact Hpobj2c | exact Htree1]. }
assert (Hnode2 : rnode tfibsegs B ly' S' W' mem' (Ddoc ++ Dback) (crt_F cx + 0x140)
  (PjTree.JObj (check_round_trip_stages_b.crt_doc (WriterSpec.b64_enc (c_bs cx)))) Dback).
{ eapply (rnode_kept_call B); [exact HJc | exact HARUC | exact OK' | exact PO' | intros x _; exact (NF x)
  | intros a kk x _ _; exact (NF x) | exact Hpobj1c | exact Hnode1]. }
assert (Hpobj1' : pobj tfibsegs B ly' S' W' mem' (crt_F cx + 0x140)).
{ eapply (pobj_kept_call B); [exact HJc | exact HARUC | exact OK' | exact PO' | intros x _; exact (NF x)
  | intros a Ha; exfalso; exact (NF a Ha) | exact HH' | exact Hpobj1c]. }
assert (Hpobj2' : pobj tfibsegs B ly' S' W' mem' (crt_F cx + 0x20)).
{ eapply (pobj_kept_call B); [exact HJc | exact HARUC | exact OK' | exact PO' | intros x _; exact (NF x)
  | intros a Ha; exfalso; exact (NF a Ha) | exact HH' | exact Hpobj2c]. }
assert (Hval2 : val_mem tfibsegs (mrestrict (w_H W') mem') (crt_F cx + 0x1a0) 8 0).
{ apply (c2_val_kept_frame SK B _ _ _ ly3 S3 U3 W3 memC mdC ly' S' U3 W' mem' md' 0 3 (c_pos cx) (crt_F cx + 0x1a0) 8 0
    HJc HARUC OK' PO' Hin3); [rewrite EF; lia | rewrite EF, crt_frame3; change (Z.of_nat 8) with 8; lia
    | intros x _; exact (NF x) | exact Hval1]. }
assert (Hra2 : range_addressable (aview tfibsegs (w_H W') mem') SHADOW_OFF (crt_F cx + 0x1a0) 8).
{ apply (c2_ra_kept_frame SK B _ _ _ ly3 S3 U3 W3 memC mdC ly' S' U3 W' mem' md' 0 3 (c_pos cx) (crt_F cx + 0x1a0) 8
    HJc HARUC OK' PO' ltac:(intros a Ha; exfalso; exact (NF a Ha)) HH' Hin3);
    [rewrite EF; lia | rewrite EF, crt_frame3; lia | exact Hra1]. }
(* ---- the exit boundary ---- *)
assert (K : forall n, acallee_saved (Z.of_nat n) -> sr_get (ss_regs c2_s29) (Z_to_bv 5 (Z.of_nat n)) = SOff n 0 ->
  ew (Ereg regs' (crt_extra cx)) n = ew E n)
  by (intros n Hc Hr; exact (c2_keep_s E c2_s29 regsC regs' (crt_extra cx) n RG HP Hc Hr)).
hnf.
split; [rewrite (K 18%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s29_save; lia)); exact E18|].
split; [rewrite (K 20%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s29_save; lia)); exact E20|].
split; [rewrite (K 21%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s29_save; lia)); exact E21|].
split; [rewrite (K 23%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s29_save; lia)); exact E23|].
split; [rewrite (K 26%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s29_save; lia)); exact E26|].
split; [rewrite (K 27%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s29_save; lia)); exact E27|].
exists same, nsame, file, nfile, back, z', (WriterSpec.b64_enc (c_bs cx)), Dback, Ddoc,
  (PjTree.JObj (check_round_trip_stages_b.crt_doc (WriterSpec.b64_enc (c_bs cx)))), live, peak, cnt.
split; [rewrite (K 22%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s29_save; lia)); exact E22|].
split; [rewrite (K 24%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s29_save; lia)); exact E24|].
split; [rewrite (K 25%nat ltac:(unfold acallee_saved; cbn; lia) ltac:(apply c2_s29_save; lia)); exact E25|].
split; [rewrite (ew_Ereg_nat regs' (crt_extra cx) 10 10%bv eq_refl); exact Gz|].
split; [lia|].
split; [rewrite Hab; exact HPB|]. split; [exact HPU|]. split; [exact HH'|].
split; [exact Rtext2|]. split; [exact Rback2|]. split; [exact Zback2|]. split; [exact Rfile2|].
split; [exact Htree2|]. split; [exact Hnode2|]. split; [exact Hpobj1'|]. split; [exact Hpobj2'|].
split; [exact (cstr_ok_of_rblockU B ly' S' U3 W' mem' md' z' nz _ HARU' HH' Rz Hlen Gg Gnz)|].
split; [apply WriterSpecFacts.b64_dec_enc; exact (garr8_bytes_ok tfibsegs _ _ _ Zback)|].
split; [reflexivity|].
split; [exists nz; split; [exact (Hzincl _ Hinz) | exact Hlen]|].
split; [apply c2_depth|].
split; [exact Hlivee|].
split; [exact Hval2|]. split; [exact Hra2|]. split; [exact Hglob2|].
split; [rewrite (blocks_bytes_bsum B ly' S'), Hab, <- (blocks_bytes_bsum B ly3 S3); exact Hlive|].
split; [exact Hcnt|].
(* the budgets at the exit: the by-trace ticks against K_82268 and the D groups' allowance *)
destruct (FSH_crt_room.crt_room_C2_holds B cx HB) as (RK & _ & _).
destruct (c2_TR15 (crt_es cx)) as (Tev & Tlen).
unfold K_82268.
unfold crt_trlen, crt_TR in RK, HlD, Hk |- *.
apply Nat2Z.inj_le in HlD.
unfold EV_pj_free, EV_check_round_trip, EV_fuzz_malloc, EV_fuzz_free, CRT_EV_WRAP in *.
split; lia.
Qed.

(* segment 29: crt_from at the return of pj_get_str under crt_INV_82268 gives crt_from at the return of pj_get under
   c2_INV_8225c *)
Lemma c2_seg29 : crt_from SK B c2_ss_268 (crt_INV_82268 B) -> crt_from SK B c2_ss_25c (c2_INV_8225c B).
Proof.
exact (crt_seg_call SK B 0x8225c A_pj_get_str 0x82268 c2_s29 (c2_INV_8225c B) (crt_INV_82268 B) STK_pj_get_str
  c2_run29 c2_s29_site ltac:(lia) eq_refl ltac:(apply Z.leb_le; vm_compute; reflexivity)
  ltac:(apply Z.leb_le; vm_compute; reflexivity) c2_call29).
Qed.
End s29.

(* ================= the C2 chain: crt_from at the exit 0x82268 under crt_INV_82268 gives crt_from at the entry 0x82218
   under crt_INV_82218 (segments 29, 28, 27, 26, 25 composed) =================
   Premises: the five callees' contracts (S0 specs, sink head SK passed explicitly) and the image facts; the by-trace
   room is FSH_crt_room.crt_room_C2_holds, a lemma over crt_base. *)
Section chain. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis PJW : pj_write_spec (SK := SK) B tfibsegs.
Hypothesis RTS : astrlen_realizesU tfibsegs B PC_strlen.
Hypothesis PJP : pj_parse_spec (SK := SK) tfibsegs B.
Hypothesis PJG : pj_get_spec (SK := SK) tfibsegs B.
Hypothesis PJGS : pj_get_str_spec (SK := SK) tfibsegs B.
Lemma c2_chain :
  crt_from SK B (crt_ss_ret 0x82268 crt_cs1 crt_csF) (crt_INV_82268 B) ->
  crt_from SK B (crt_ss_ret 0x82218 crt_cs1 crt_csF) (crt_INV_82218 B).
Proof.
intros H29.
exact (@c2_seg25 fx rc SK B PJW
        (@c2_seg26 fx rc SK B IMG RTS
          (@c2_seg27 fx rc SK B PJP
            (@c2_seg28 fx rc SK B IMG PJG
              (@c2_seg29 fx rc SK B IMG PJGS H29))))).
Qed.
End chain.
