(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YE05.v, with its module paths changed; 2671 of its 2756 lines of code are new or changed and 333 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segA.v, with its module paths changed; 33 of its 76 lines of code are new or changed and 2713 lines of the source are left out. *)
(* lib/B (fs.asan-ubsan) twin of lib/A/FSH_crt_cstr.v: cstr_ok of a heap string from the facts a crt boundary invariant
   carries: the string's bytes and NUL (zbytes_at), no NUL inside it, and the live block it lies in. Shared by every crt
   lane of the B walk (check_round_trip, build B). Owner: a Theorem Labs lane (lane CRT); B twin written by a Theorem Labs lane.
   PORT SOURCE: a working branch e377e99a5c4 proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_cstr.v (95 lines),
   itself moved VERBATIM from a Theorem Labs lane's lib/A/FSH_crt_a23cstr.v at a working branch c2f01f092c5 (written by its
   sub-lane), renamed: a23_enc_nz -> crt_enc_nz, a23_cstr_blk -> crt_cstr_of_block, a23_cstr -> crt_cstr_of_rblock.
   Same Lemma names, same statements, same proofs, over image B. Imports: lib.A.X -> lib.B.X where lib/B/X.v exists
   (AB1v -> YB1v, and every FSH_* / FSW_* / FSPstat kit file); FSupoison, FSupoisonU, FSH_YC20 and FSH_Gen stay lib/A's,
   exactly as lib/B/FSW_K.v and lib/B/FSH_crt_site.v import them.
     crt_enc_nz         : the base64 encoding of a byte list holds no NUL (WriterSpecFacts.b64_enc_chars).
     crt_cstr_of_block  : a string at p inside a live block (b, m), past its 16-byte head, is cstr_ok on the machine's
                          memory (AR_blocks_law, FSW_rd.fsw_block_body_addressable, FSW_strkit.shadow_hull_vis_sub /
                          block_word_tail_vis / aview_unpoison_vis).
     crt_cstr_of_rblock : the same for a string that fills its block exactly, at (p - HEAD, n + HEAD).
   rule 24: proves no function (kind: segment lemma of check_round_trip's walk, PORTED from e377e99a5c4 lib/A/FSH_crt_cstr.v)
   (the A file's own line: PORTED from a working branch d25a984c903
   proofs/omx-clap-core/fuzz_state/lib/A/Prog/check_round_trip_sd2.v - sd2_enc_nz :52 and the cstr_ok premises of
   sd2_tail :494). The function-level reuse search is crt-lane-head.md lines 6-21.

   A -> B TABLE: none. No name of this file carries a pc, and no statement or proof uses a pc, frame offset, register or
   image constant: the asyms B is a Section variable, and the image enters only through tfibsegs (lib/B/YB1v) and the
   B kit's fsw_block_body_addressable (lib/B/FSW_rd.v:316) / shadow_hull_vis_sub, word_end_mono, aview_unpoison_vis,
   block_word_tail_vis (lib/B/FSW_strkit.v:59, :70, :132, :227), whose statements are the A kit's word for word. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n YN0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_rres FSW_frame FSW_rd FSW_strkit
FSH_Fn_reader FSH_Fn_writer FSH_Fn_alloc FSH_Fn_crt FSH_crt_base FSH_crt_site FSW_crt_tbl.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterSpec B64Canon.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require HState check_round_trip_loops.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
(* SINK GUARD: a SUCCESS here (the build errors naming this line) means a wrong sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* the base64 alphabet and its pad '=' hold no NUL (port of sd2_enc_nz, check_round_trip_sd2.v:52, on plain list Z) *)
Lemma crt_enc_nz : forall bs, Forall (fun b => 0 <= b < 256) bs -> ~ In 0 (WriterSpec.b64_enc bs).
Proof.
intros bs Hb H.
pose proof (WriterSpecFacts.b64_enc_chars bs Hb) as Hc.
rewrite Forall_forall in Hc. specialize (Hc 0 H). cbv beta in Hc. lia.
Qed.

(* a string inside a live block, past its 16-byte head, is cstr_ok on the machine's memory *)
Lemma crt_cstr_of_block : forall ly S U (W : world tfibsegs) mem md p (l : list Z) b m,
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U ->
  In (b, m) (ablocks B ly S) -> b + HEAD <= p -> p + Z.of_nat (length l) + 1 <= b + m ->
  zbytes_at tfibsegs W mem p (l ++ [0]) -> ~ In 0 l ->
  cstr_ok tfibsegs W mem p l.
Proof.
intros ly S U W mem md p l b m HARU FH Hin Hb Hbm Hz Hnz.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
pose proof HARU as (_ & _ & PO).
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md b m HAR Hin) as (_ & H4096 & Hc & Happ & _ & _ & Hmax).
unfold HEAD in Hb. unfold MALLOC_MAX in Hmax.
assert (Hm : 0 < m) by lia.
assert (Hrq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
rewrite Hrq in Hc, Happ.
pose proof (proj1 (@YM05.alloc_ceiling_value rc)) as HCV.
split; [split; [exact Hz|]|].
{ apply Forall_forall. intros c Hc0 E. subst c. exact (Hnz Hc0). }
split; [lia|]. split; [lia|]. split; [lia|].
split.
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd.
  destruct Happ as (_ & [Hlo | (Hh1 & Hh2)]); [left | right]; lia. }
split.
{ apply (fsw_block_body_addressable B ly S U W mem md b m p (Z.of_nat (length l) + 1) HARU FH Hin); lia. }
split.
{ destruct (al_shadow _ _ LAWS ly S W (unpoison U mem) md b m HAR Hin) as (_ & Hhv). rewrite Hrq in Hhv.
  intros s Hs. eapply aview_unpoison_vis; [exact PO|].
  exact (shadow_hull_vis_sub _ b m p (Z.of_nat (length l) + 1) Hhv ltac:(lia) ltac:(lia) ltac:(lia) s Hs). }
intros a Ha. eapply aview_unpoison_vis; [exact PO|].
apply (block_word_tail_vis B ly S W (unpoison U mem) md b m HAR Hin Hm).
pose proof (word_end_mono (p + Z.of_nat (length l)) (b + m - 1) ltac:(lia)). lia.
Qed.

(* a string that fills its block's body exactly: the block is (p - HEAD, n + HEAD) and the string with its NUL is n bytes *)
Lemma crt_cstr_of_rblock : forall ly S U (W : world tfibsegs) mem md p (l : list Z) n,
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U ->
  In (p - HEAD, n + HEAD) (ablocks B ly S) -> p mod 16 = 0 ->
  Z.of_nat (length l) + 1 = n ->
  zbytes_at tfibsegs W mem p (l ++ [0]) -> ~ In 0 l ->
  cstr_ok tfibsegs W mem p l.
Proof.
intros ly S U W mem md p l n HARU FH Hin _ Hn Hz Hnz.
apply (crt_cstr_of_block ly S U W mem md p l (p - HEAD) (n + HEAD) HARU FH Hin); [unfold HEAD; lia | unfold HEAD; lia | exact Hz | exact Hnz].
Qed.
End c.
