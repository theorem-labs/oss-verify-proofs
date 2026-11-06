(* check_round_trip's ASan walk (build A), the CHAIN of the closed lanes: from crt_INV_82218 at 0x82218 to the final ret.
   B1 (segments 10-13) -> B2 (14-19) -> C1 (20-24) -> C2 (25-29, a Theorem Labs lane) -> D1 (30-33) -> D2 (34-39) -> the tail (crt_tail). Each lemma is applied to its lane's
   named Section hypotheses, which this Section lists once. Owner: a Theorem Labs lane (lane CRT).
   rule 24: proves no function (kind: composition of check_round_trip's segment lemmas, build A; the function-level line
   is crt-lane-head.md lines 6-21). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_rres FSW_frame FSH_Fn_reader FSH_Fn_writer FSH_Fn_alloc FSH_Fn_crt.
(* FSH_Fn_crt.v's own import list last, so every short name below resolves as it does in the statement *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec HState B64Canon ReaderRes pj_set_c
  PjStruct check_round_trip_st8 check_round_trip_stages_b WriterValue WriterApp.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree PjGrammar PjRoundTrip.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSH_crt_base FSH_crt_segD FSH_crt_segC2
  FSH_crt_segD1_main FSH_crt_segD2_top FSH_crt_segC1 FSH_crt_segB2 FSH_crt_segB FSH_crt_segB0 FSH_crt_setsh FSH_crt_loop7 FSH_crt_segA23 FSH_crt_loop5 FSH_crt_segA.
(* SINK GUARD *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.

Section chain. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : YG0f.asyms.
(* callee contracts and image / runtime facts, the lanes' names *)
Hypothesis IMG : FSH_Rt.fs_img_facts tfibsegs B.
Hypothesis PJW : FSH_Fn_writer.pj_write_spec B tfibsegs.
Hypothesis PJP : FSH_Fn_reader.pj_parse_spec tfibsegs B.
Hypothesis PJG : FSH_Fn_reader.pj_get_spec tfibsegs B.
Hypothesis PJGS : FSH_Fn_reader.pj_get_str_spec tfibsegs B.
Hypothesis DECODE : FSH_Fn_writer.decode_spec_ff B tfibsegs.
Hypothesis FUZZ_FREE : FSH_Fn_alloc.fuzz_free_spec tfibsegs B.
(* the runtime contracts the walk calls: the seven fields of FSH_crt_base.v's CrtRt (S0's FsRt fields at
   segs := tfibsegs), not the whole FsRt. RT_STRLEN is also lane C2's strlen contract (c2_chain). *)
Hypothesis RT_STRLEN : FSH_Gen.astrlen_realizesU tfibsegs B FSH_Base.PC_strlen.
Hypothesis RT_STRCMP : FSH_Gen.astrcmp_realizesU tfibsegs B FSH_Base.PC_strcmp.
Hypothesis RT_BCMP : FSupoisonU.abcmp_realizesU tfibsegs B FSH_Base.PC_bcmp.
Hypothesis RT_SETSH : SetShadowDefU.aset_shadow_realizesU tfibsegs B FSH_Base.PC_set_shadow_f5 0xf5.
Hypothesis RT_MALLOC :
  YG0f.pc_wrap_malloc (YG0f.as_code B) = FSH_Base.PC_malloc /\ FSupoisonU.amalloc_realizesU tfibsegs B.
Hypothesis RT_FREE : YG0f.pc_wrap_free (YG0f.as_code B) = FSH_Base.PC_free /\ FSupoisonU.afree_realizesU tfibsegs B.
Hypothesis RT_SM3 :
  YG0f.pc_stack_malloc (YG0f.as_code B) 3 = FSH_Base.PC_stack_malloc_3 /\ FSupoisonU.astack_malloc_realizesU tfibsegs B 3.
Let RT : CrtRt B := Build_CrtRt B RT_STRLEN RT_STRCMP RT_BCMP RT_SETSH RT_MALLOC RT_FREE RT_SM3.
Hypothesis HENV : YCbq.api_env tfibsegs B.
Hypothesis PJ_FREE : FSH_Fn_reader.pj_free_spec tfibsegs B 0.
Hypothesis PJ_STRING : @FSH_Fn_reader.pj_string_spec fx rc SK tfibsegs B.
Hypothesis PJ_SET : @FSH_Fn_reader.pj_set_spec fx rc SK tfibsegs B.
Hypothesis PJ_OBJECT : @FSH_Fn_reader.pj_object_spec fx rc SK tfibsegs B.
Hypothesis ML : YG0d.model_laws (YG0f.as_universe B).
Hypothesis ASF : YG0d.astack_free_law tfibsegs B.
Hypothesis FFL : YCbq.frame_flag_lawP tfibsegs B.
Hypothesis HSS : FSH_Base.FsShadowSyms B.
Hypothesis HGUAR : YG0f.as_got_uar B = FSW_K.fs_D_GOT_uar.
Hypothesis HUCELL : YG0f.as_uar_cell B = FSW_K.fs_D_uar_cell.
Hypothesis ENCODE : FSH_Fn_writer.encode_spec B tfibsegs.

Lemma crt_from_82218 : crt_from SK B (crt_ss_ret 0x82218 crt_cs1 crt_csF) (crt_INV_82218 B).
Proof.
apply (c2_chain SK B IMG PJW RT_STRLEN PJP PJG PJGS).
apply (crtD1_main SK B DECODE FUZZ_FREE RT HENV).
apply (crtD2_main SK B PJ_FREE FUZZ_FREE RT HENV IMG ML).
exact (crt_tail SK B ASF FFL (crt_setsh_of_rt B RT_SETSH)).
Qed.
(* C1 (segments 20-24): 0x821ac -> 0x82218 *)
Lemma crt_from_821ac : crt_from SK B (crt_ss_ret 0x821ac crt_cs1 crt_csF) (crt_INV_821ac B).
Proof.
eapply crtC1_from; try eassumption.
exact crt_from_82218.
Qed.
(* B2 (segments 14-19): 0x8212c -> 0x821ac *)
Lemma crt_from_8212c : crt_from SK B (crt_ss_ret 0x8212c crt_cs1 crt_csF) (crt_INV_8212c B).
Proof.
eapply crtB2_from_8212c; try eassumption.
exact crt_from_821ac.
Qed.
(* B1 (segments 10-13): 0x82068 -> 0x8212c, both arms of segment 11 (a Theorem Labs lane's front half, a Theorem Labs lane's back half) *)
Lemma crt_from_82068 : crt_from SK B (crt_ss_ret 0x82068 crt_cs1 crt_csF) (crt_INV_82068 B).
Proof.
exact (crtB0_seg10_11 SK B DECODE RT HENV
  (crtB_from_8209c SK B PJ_OBJECT crt_from_8212c) (crtB_from_820a0 SK B PJ_OBJECT crt_from_8212c)).
Qed.
(* A23 segments 8-9: 0x82028 -> 0x82068, carrying crt_R7 *)
Lemma crt_from_82028 : crt_from SK B (crt_ss_ret 0x82028 crt_cs1 crt_csF)
  (fun cx E k ly3 S3 U3 W3 ms3 md3 => crt_INV_82028 cx E k ly3 S3 U3 W3 ms3 md3 /\ crt_R7 B cx E k ly3 S3 U3 W3 ms3 md3).
Proof. eapply a23_seg89; try eassumption. exact crt_from_82068. Qed.
(* L7, the copy loop: 0x81fb8 -> 0x82028, frame-generic, at R := crt_R7 *)
Lemma crt_from_81fb8 : crt_from SK B (crt_ss_ret 0x81fb8 crt_cs1 crt_csF)
  (fun cx E k ly3 S3 U3 W3 ms3 md3 => crt_INV_81fb8 B cx E k ly3 S3 U3 W3 ms3 md3 /\ crt_R7 B cx E k ly3 S3 U3 W3 ms3 md3).
Proof. exact (crt_l7_seg SK B (crt_R7 B) (a23_stable7 B) crt_from_82028). Qed.
(* A23 segment 6: 0x81f58 -> 0x81fb8, crt_R5 in, crt_R7 out *)
Lemma crt_from_81f58 : crt_from SK B (crt_ss_ret 0x81f58 crt_cs1e crt_csF)
  (fun cx E k ly3 S3 U3 W3 ms3 md3 => crt_INV_81f58 B cx E k ly3 S3 U3 W3 ms3 md3 /\ crt_R5 B cx E k ly3 S3 U3 W3 ms3 md3).
Proof. eapply a23_seg6; try eassumption. exact crt_from_81fb8. Qed.
(* L5, the encode loop: 0x81d0c -> 0x81f58, frame-generic, at R := crt_R5 *)
Lemma crt_from_81d0c : crt_from SK B (crt_ss_ret 0x81d0c crt_cs1e crt_csF)
  (fun cx E k ly3 S3 U3 W3 ms3 md3 => crt_INV_81d0c B cx E k ly3 S3 U3 W3 ms3 md3 /\ crt_R5 B cx E k ly3 S3 U3 W3 ms3 md3).
Proof. exact (crt5_seg5 SK B (crt_R5 B) (a23_stable5 B) crt_from_81f58). Qed.

(* ================= THE THEOREM: check_round_trip's ASan contract, build A =================
   A0's entry theorem from the function's entry, taking both of its exits: the loop arm into L5 at 0x81d0c, and the
   |bs| = 0 arm straight to the join at 0x81f58. crt_spec_of_base turns it into check_round_trip_spec. *)
Theorem check_round_trip_holds : @check_round_trip_spec fx rc SK tfibsegs B.
Proof.
apply (crt_spec_of_base SK B).
exact (crtA_from_entry SK B HSS HGUAR HUCELL HENV RT ENCODE IMG crt_from_81d0c crt_from_81f58).
Qed.
End chain.
Print Assumptions crt_from_82218.
Print Assumptions crt_from_82068.
Print Assumptions crt_from_81f58.
Print Assumptions check_round_trip_holds.
About check_round_trip_holds.
