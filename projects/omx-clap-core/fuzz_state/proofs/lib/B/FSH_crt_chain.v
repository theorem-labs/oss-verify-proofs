(* check_round_trip's ASan walk (build B, fs.asan-ubsan, check_round_trip at 0x81b9c), the CHAIN of the closed lanes:
   from the function's entry B 0x81b9c to the final ret, and check_round_trip_holds. A0 (segments 0-5) -> L5 (the
   encode loop; A0's |bs| = 0 arm goes straight to the join B 0x820a4) -> A23 seg 6 -> L7 (seg 7) -> A23 segs 8-9 ->
   B1 (segments 10-13) -> B2 (14-19) -> C1 (20-24) -> C2 (25-29, a Theorem Labs lane) -> D1 (30-33) -> D2 (34-39) -> the tail
   (crt_tail). Each lemma is applied to its lane's named Section hypotheses, which this Section lists once.
   rule 24: proves no function (kind: composition of check_round_trip's segment lemmas, PORTED from be1fe777656)
   rule 24: proves no function (kind: segment lemmas of check_round_trip's walk, PORTED from 317e6575975 / c159ab19cb1 /
   06a2ee3f7d8) - the room hypotheses HROOM / HROOM2 dropped: the lanes' lemmas on those shas (B2, D1, and C2 at
   a Theorem Labs lane's 53c958d574c) take crt_room_D1_holds / crt_room_C2_holds themselves.
   PORT SOURCE: a working branch be1fe777656 proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_chain.v (blob
   977e30cec3f; the first B twin was of 036d41a098c; the function-level line is crt-lane-head.md lines 6-21). Same
   Definition / Lemma names, statement shapes and Section hypotheses as the A file, over image B and the B lane lemmas:
   crtB0_seg10_11 (lib/B/FSH_crt_segB0.v), crtB_from_8209c / crtB_from_820a0 (lib/B/FSH_crt_segB.v), crtB2_from_8212c
   (lib/B/FSH_crt_segB2.v), crtC1_from (lib/B/FSH_crt_segC1.v), c2_chain (lib/B/FSH_crt_segC2.v), crtD1_main
   (lib/B/FSH_crt_segD1_main.v), crtD2_main (lib/B/FSH_crt_segD2_top.v), crt_tail (lib/B/FSH_crt_segD.v), and the tail's
   runtime premise from FsRt, crt_setsh_of_rt (lib/B/FSH_crt_setsh.v). B twin written by a Theorem Labs lane.
   A name -> A pc -> B pc (MEASURED, crt.A.s / crt.B.s; crt.A2B.tsv `equal` rows except two first instructions of
   `replace` blocks, mapped by meaning: A 0x820a0 -> B 0x821fc, the `beqz s4` target and first shadow store
   (lib/B/FSH_crt_segB.v), and the tail's entry A 0x82354 -> B 0x824b4, the return of free (same)
   (lib/B/FSH_crt_segD.v); names keep their A form):
     crt_from_82068 / crt_INV_82068   A 0x82068   B 0x821c4   (B1's entry, segments 10-11, crtB0_seg10_11)
     crtB_INV_8209c / crtB_INV_820a0  A 0x8209c / 0x820a0   B 0x821f8 / 0x821fc   (segment 11 -> 12, both arms)
     crt_from_8212c / crt_INV_8212c   A 0x8212c   B 0x82288   (B1 -> B2, return of the second pj_object)
     crt_from_821ac / crt_INV_821ac   A 0x821ac   B 0x82308   (B2 -> C1, return of the third pj_set)
     crt_from_82218 / crt_INV_82218   A 0x82218   B 0x82374   (C1 -> C2, return of the sixth pj_set)
     crt_INV_82268                    A 0x82268   B 0x823c0   (C2 -> D1, inside c2_chain / crtD1_main)
     crt_INV_822ac (crt_ss34)         A 0x822ac   B 0x82408   (D1 -> D2, inside crtD1_main / crtD2_main)
     crt_INV_T (crt_ssT)              A 0x82354   B 0x824b4   (D2 -> tail, return of free (same); crtD2_main / crt_tail)
   Non-mechanical changes: the composition is A's (the B content is in the lane files); the Section hypotheses' types
   are A's with the lib/B module qualifiers written `lib.B.X.` (see the Section's comment).
   EXTENSION, PORTED from a working branch 69f9837ef88 lib/A/FSH_crt_chain.v (rule 24: proves no function,
   kind: composition of check_round_trip's segment lemmas): the walk's middle, A23 segs 8-9 o L7 o A23 seg 6, over
   a23_seg89 / a23_seg6 / a23_stable7 (lib/B/FSH_crt_segA23.v) and crt_l7_seg (lib/B/FSH_crt_loop7.v, at R := crt_R7).
   Same names and statement shapes as A; the crt_ss_ret pcs are B's (lib/B/FSH_crt_segA23.v's A -> B table):
     crt_from_82028 / crt_INV_82028   A 0x82028   B 0x82180 ~ crt_cs1    (L7's exit, a23_seg89's entry; carries crt_R7)
     crt_from_81fb8 / crt_INV_81fb8   A 0x81fb8   B 0x8210c ~ crt_cs1    (L7's head = L7_HEAD, a23_seg6's exit)
     crt_from_81f58 / crt_INV_81f58   A 0x81f58   B 0x820a4 = crt_cs1e   (the join of both A0 exits; carries crt_R5)
   rule 24: proves no function (kind: composition of check_round_trip's segment lemmas, PORTED from 1ab57ca7ad7) - the
   runtime hypothesis is A's CrtRt form (a working branch 1ab57ca7ad7): the seven RT_* contracts and
   `Let RT := Build_CrtRt ..` over lib/B/FSH_crt_base.v's Record CrtRt (B base a working branch
   95b912432dc), in place of FsRt and RTS.
   EXTENSION 2, PORTED from a working branch 1ab57ca7ad7 lib/A/FSH_crt_chain.v (rule 24: proves no function,
   kind: composition of check_round_trip's segment lemmas): L5 o A23 seg 6 over crt5_seg5 (lib/B/FSH_crt_loop5.v, at
   R := crt_R5, with a23_stable5), and the theorem check_round_trip_holds = crt_spec_of_base (lib/B/FSH_crt_base.v) o
   crtA_from_entry (lib/B/FSH_crt_segA.v) at both of its exits:
     crt_from_81d0c / crt_INV_81d0c   A 0x81d0c   B 0x81e18 = crt_cs1L   (L5's head, A0's loop-arm exit; carries crt_R5)
   B differences: L5's head state is crt_ss_ret 0x81e18 crt_cs1L crt_csF (B's loop arm spills 0x28 := En and 0x38 := F;
   A: crt_cs1e), and L5 hands over at the join B 0x820a4 (A 0x81f58). crtA_from_entry's image facts HSS / HGUAR /
   HUCELL and its encode contract ENCODE are A's four extra Section hypotheses, with lib/B qualifiers. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_rres FSW_frame FSH_Fn_reader FSH_Fn_writer FSH_Fn_alloc FSH_Fn_crt.
(* lib/B/FSH_Fn_crt.v's own import list last, so every short name below resolves as it does in the statement *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSH_Base FSH_Rt FSPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec HState B64Canon ReaderRes pj_set_c
  PjStruct check_round_trip_st8 check_round_trip_stages_b WriterValue WriterApp.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree PjGrammar PjRoundTrip.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSH_crt_base FSH_crt_segD FSH_crt_segC2
  FSH_crt_segD1_main FSH_crt_segD2_top FSH_crt_segC1 FSH_crt_segB2 FSH_crt_segB FSH_crt_segB0 FSH_crt_setsh
  FSH_crt_loop7 FSH_crt_segA23 FSH_crt_loop5 FSH_crt_segA.
(* SINK GUARD *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section chain. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : YG0f.asyms.
(* callee contracts and image / runtime facts, the lanes' names. B: the lib/B module qualifiers carry `lib.B.`, since
   the lane files' Require closure also loads lib/A modules of the same short name, which can shadow a bare qualifier
   (measured: a bare `FSH_Rt.fs_img_facts` resolved to lib/A's, over lib/A's FS_PSTAT_FP) *)
Hypothesis IMG : lib.B.FSH_Rt.fs_img_facts tfibsegs B.
Hypothesis PJW : lib.B.FSH_Fn_writer.pj_write_spec B tfibsegs.
Hypothesis PJP : lib.B.FSH_Fn_reader.pj_parse_spec tfibsegs B.
Hypothesis PJG : lib.B.FSH_Fn_reader.pj_get_spec tfibsegs B.
Hypothesis PJGS : lib.B.FSH_Fn_reader.pj_get_str_spec tfibsegs B.
Hypothesis DECODE : lib.B.FSH_Fn_writer.decode_spec_ff B tfibsegs.
Hypothesis FUZZ_FREE : lib.B.FSH_Fn_alloc.fuzz_free_spec tfibsegs B.
(* the runtime contracts the walk calls: the seven fields of lib/B/FSH_crt_base.v's CrtRt (S0's lib/B FsRt fields at
   segs := tfibsegs), not the whole FsRt (A's form at a working branch 1ab57ca7ad7). RT_STRLEN is also lane
   C2's strlen contract (c2_chain); crt_tail's set_shadow premise comes from RT_SETSH alone (crt_setsh_of_rt). *)
Hypothesis RT_STRLEN : FSH_Gen.astrlen_realizesU tfibsegs B lib.B.FSH_Base.PC_strlen.
Hypothesis RT_STRCMP : FSH_Gen.astrcmp_realizesU tfibsegs B lib.B.FSH_Base.PC_strcmp.
Hypothesis RT_BCMP : FSupoisonU.abcmp_realizesU tfibsegs B lib.B.FSH_Base.PC_bcmp.
Hypothesis RT_SETSH : SetShadowDefU.aset_shadow_realizesU tfibsegs B lib.B.FSH_Base.PC_set_shadow_f5 0xf5.
Hypothesis RT_MALLOC :
  YG0f.pc_wrap_malloc (YG0f.as_code B) = lib.B.FSH_Base.PC_malloc /\ FSupoisonU.amalloc_realizesU tfibsegs B.
Hypothesis RT_FREE :
  YG0f.pc_wrap_free (YG0f.as_code B) = lib.B.FSH_Base.PC_free /\ FSupoisonU.afree_realizesU tfibsegs B.
Hypothesis RT_SM3 :
  YG0f.pc_stack_malloc (YG0f.as_code B) 3 = lib.B.FSH_Base.PC_stack_malloc_3 /\
  FSupoisonU.astack_malloc_realizesU tfibsegs B 3.
Let RT : lib.B.FSH_crt_base.CrtRt B :=
  lib.B.FSH_crt_base.Build_CrtRt B RT_STRLEN RT_STRCMP RT_BCMP RT_SETSH RT_MALLOC RT_FREE RT_SM3.
Hypothesis HENV : YCbq.api_env tfibsegs B.
Hypothesis PJ_FREE : lib.B.FSH_Fn_reader.pj_free_spec tfibsegs B 0.
Hypothesis PJ_STRING : @lib.B.FSH_Fn_reader.pj_string_spec fx rc SK tfibsegs B.
Hypothesis PJ_SET : @lib.B.FSH_Fn_reader.pj_set_spec fx rc SK tfibsegs B.
Hypothesis PJ_OBJECT : @lib.B.FSH_Fn_reader.pj_object_spec fx rc SK tfibsegs B.
Hypothesis ML : YG0d.model_laws (YG0f.as_universe B).
Hypothesis ASF : YG0d.astack_free_law tfibsegs B.
Hypothesis FFL : YCbq.frame_flag_lawP tfibsegs B.
(* crtA_from_entry's (lib/B/FSH_crt_segA.v's Section W): image B's shadow and UAR GOT cells, and preset_base64_encode's
   contract *)
Hypothesis HSS : lib.B.FSH_Base.FsShadowSyms B.
Hypothesis HGUAR : YG0f.as_got_uar B = lib.B.FSW_K.fs_D_GOT_uar.
Hypothesis HUCELL : YG0f.as_uar_cell B = lib.B.FSW_K.fs_D_uar_cell.
Hypothesis ENCODE : @lib.B.FSH_Fn_writer.encode_spec fx rc SK B tfibsegs.
(* the room premises are no hypotheses (base v33): c2_chain takes crt_room_C2 from FSH_crt_room.crt_room_C2_holds and
   crtD1_main / crtB2_from_8212c take crt_room_D1 from FSH_crt_room.crt_room_D1_holds *)

(* C2 o D1 o D2 o tail: B 0x82374 (A 0x82218) -> the final ret *)
Lemma crt_from_82218 : crt_from SK B (crt_ss_ret 0x82374 crt_cs1 crt_csF) (crt_INV_82218 B).
Proof.
apply (c2_chain SK B IMG PJW RT_STRLEN PJP PJG PJGS).
apply (crtD1_main SK B DECODE FUZZ_FREE RT HENV).
apply (crtD2_main SK B PJ_FREE FUZZ_FREE RT HENV IMG ML).
exact (crt_tail SK B ASF FFL (crt_setsh_of_rt B RT_SETSH)).
Qed.
(* C1 (segments 20-24): B 0x82308 -> 0x82374 (A 0x821ac -> 0x82218) *)
Lemma crt_from_821ac : crt_from SK B (crt_ss_ret 0x82308 crt_cs1 crt_csF) (crt_INV_821ac B).
Proof.
eapply crtC1_from; try eassumption.
exact crt_from_82218.
Qed.
(* B2 (segments 14-19): B 0x82288 -> 0x82308 (A 0x8212c -> 0x821ac) *)
Lemma crt_from_8212c : crt_from SK B (crt_ss_ret 0x82288 crt_cs1 crt_csF) (crt_INV_8212c B).
Proof.
eapply crtB2_from_8212c; try eassumption.
exact crt_from_821ac.
Qed.
(* B1 (segments 10-13): B 0x821c4 -> 0x82288 (A 0x82068 -> 0x8212c), both arms of segment 11 (a Theorem Labs lane's front half,
   a Theorem Labs lane's back half) *)
Lemma crt_from_82068 : crt_from SK B (crt_ss_ret 0x821c4 crt_cs1 crt_csF) (crt_INV_82068 B).
Proof.
exact (crtB0_seg10_11 SK B DECODE RT HENV
  (crtB_from_8209c SK B PJ_OBJECT crt_from_8212c) (crtB_from_820a0 SK B PJ_OBJECT crt_from_8212c)).
Qed.
(* A23 segments 8-9: B 0x82180 -> 0x821c4 (A 0x82028 -> 0x82068), carrying crt_R7 *)
Lemma crt_from_82028 : crt_from SK B (crt_ss_ret 0x82180 crt_cs1 crt_csF)
  (fun cx E k ly3 S3 U3 W3 ms3 md3 => crt_INV_82028 cx E k ly3 S3 U3 W3 ms3 md3 /\ crt_R7 B cx E k ly3 S3 U3 W3 ms3 md3).
Proof. eapply a23_seg89; try eassumption. exact crt_from_82068. Qed.
(* L7, the copy loop: B 0x8210c -> 0x82180 (A 0x81fb8 -> 0x82028), frame-generic, at R := crt_R7 *)
Lemma crt_from_81fb8 : crt_from SK B (crt_ss_ret 0x8210c crt_cs1 crt_csF)
  (fun cx E k ly3 S3 U3 W3 ms3 md3 => crt_INV_81fb8 B cx E k ly3 S3 U3 W3 ms3 md3 /\ crt_R7 B cx E k ly3 S3 U3 W3 ms3 md3).
Proof. exact (crt_l7_seg SK B (crt_R7 B) (a23_stable7 B) crt_from_82028). Qed.
(* A23 segment 6: B 0x820a4 -> 0x8210c (A 0x81f58 -> 0x81fb8), crt_R5 in, crt_R7 out *)
Lemma crt_from_81f58 : crt_from SK B (crt_ss_ret 0x820a4 crt_cs1e crt_csF)
  (fun cx E k ly3 S3 U3 W3 ms3 md3 => crt_INV_81f58 B cx E k ly3 S3 U3 W3 ms3 md3 /\ crt_R5 B cx E k ly3 S3 U3 W3 ms3 md3).
Proof. eapply a23_seg6; try eassumption. exact crt_from_81fb8. Qed.
(* L5, the encode loop: B 0x81e18 -> 0x820a4 (A 0x81d0c -> 0x81f58), frame-generic, at R := crt_R5; B's loop head
   state is crt_ss_ret 0x81e18 crt_cs1L crt_csF *)
Lemma crt_from_81d0c : crt_from SK B (crt_ss_ret 0x81e18 crt_cs1L crt_csF)
  (fun cx E k ly3 S3 U3 W3 ms3 md3 => crt_INV_81d0c B cx E k ly3 S3 U3 W3 ms3 md3 /\ crt_R5 B cx E k ly3 S3 U3 W3 ms3 md3).
Proof. exact (crt5_seg5 SK B (crt_R5 B) (a23_stable5 B) crt_from_81f58). Qed.

(* ================= THE THEOREM: check_round_trip's ASan contract, build B =================
   A0's entry theorem from the function's entry, taking both of its exits: the loop arm into L5 at B 0x81e18 (A
   0x81d0c, crt_cs1L), and the |bs| = 0 arm straight to the join at B 0x820a4 (A 0x81f58). crt_spec_of_base turns it
   into check_round_trip_spec. crtA_from_entry's Section hypotheses (HSS HGUAR HUCELL HENV RT ENCODE IMG) are this
   Section's. *)
Theorem check_round_trip_holds : @check_round_trip_spec fx rc SK tfibsegs B.
Proof.
apply (crt_spec_of_base SK B).
eapply (crtA_from_entry SK B); try eassumption.
- exact crt_from_81d0c.
- exact crt_from_81f58.
Qed.
End chain.
Print Assumptions crt_from_82218.
Print Assumptions crt_from_82068.
Print Assumptions crt_from_81f58.
