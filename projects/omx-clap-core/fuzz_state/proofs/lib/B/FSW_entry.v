(* fs program part, lane ENTRY, IMAGE B (fs.asan-ubsan, pinned 5ac5ce0954f8): LLVMFuzzerTestOneInput's ASan walk
   (fs.asan-ubsan 0x80f8c-0x81248, 176 instructions) closes lib/B/FSH_Fn_entry.v's fs_entry_goal (a Theorem Labs lane's
   post-drop stage-4 statement) at the sink head FSH_Base.fsB_sink_head and B's sink / meta cells lib/B/YE2k.v tfib_K:
   the segments S01 .. S9 (lib/B/FSW_entry_s*.v) chained backwards from the post, the entry facts from the goal's
   premises (YCeg.TfibLib B, YF0m.TfibSyms B, FsEntryRt, fs_img_facts, the CTX-free callee specs FsEntryFns), and
   the walk's post turned into lib/B/FSH_Harness.v's fs_lib_post_x (lib/B/FSW_entry_post.v, under the sink's image laws
   lib/B/YD1u.v tfib_AIL from TfibSyms B). The B twin of lib/A/FSW_entry.v fs_entry_proof, with the CTX lists and their
   trace premises dropped.
   rule 24: proves function LLVMFuzzerTestOneInput (segment top; reuse search: proof-index LLVMFuzzerTestOneInput,
   no released asan or asan-ubsan proof of fuzz_state's LLVMFuzzerTestOneInput; ported from a working branch
   08ad70da3bf).
   Ported from: lib/A/FSW_entry.v (a working branch 0d34d65d2b7), itself from cgif_file_fuzzer
   lib/A/ACfj.v:230-257 and lib/A/ACfi.v:103-141.
   Section t hypotheses: none. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YCbp YC5d YI00 YI04 YI16 YK06 YO09 YM05
YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YE00 YE01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v FSH_Base FSH_Rt FSPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YCfn FSH_Harness.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
FSH_Fn_alloc FSH_Fn_checks FSH_Fn_cno FSH_Fn_crt FSH_Fn_writer FSH_Fn_entry.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
FSW_entry_defs FSW_entry_link FSW_entry_post
FSW_entry_s01 FSW_entry_s2 FSW_entry_s3 FSW_entry_s5 FSW_entry_s6 FSW_entry_s7 FSW_entry_s8 FSW_entry_s9.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YCeg YF0m YE2k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.

Theorem fs_entry_proof : @fs_entry_goal fx rc LS FSH_Base.fsB_sink_head YE2k.tfib_K B.
Proof.
intros HLS TL TS [fe_sm0 ASF fe_ma fe_fr fe_mc fe_mch] IMG
  [en_no_overread en_alloc_live en_alloc_peak_reset en_decode en_alloc_peak en_bounded_alloc en_as_written
   en_round_trip en_reject_clean en_starved en_free].
pose proof (fe_tl_got_shadow B TL) as tl_got_shadow. pose proof (fe_tl_shadow_cell B TL) as tl_shadow_cell.
pose proof (fe_tl_got_uar B TL) as tl_got_uar. pose proof (fe_tl_uar_cell B TL) as tl_uar_cell.
pose proof (YCeg.tl_code B TL) as tl_code.
pose proof (fe_api_env B TL) as errno_low. pose proof (fe_model_laws B TL) as ML.
pose proof (@fe_frame_flag_law fx rc B) as FFL.
(* the segments, from the post backwards *)
assert (P9 : fe_from (SK := FSH_Base.fsB_sink_head) B FS_PSTAT_FP (fe_post (SK := FSH_Base.fsB_sink_head) B FS_PSTAT_FP)
  (fe_ss PC_epi []) (INV_C9 B))
  by (eapply fe_seg9; eassumption).
assert (P8 : fe_from (SK := FSH_Base.fsB_sink_head) B FS_PSTAT_FP (fe_post (SK := FSH_Base.fsB_sink_head) B FS_PSTAT_FP)
  (fe_ss RA_crc [fe_len_atom 46]) (INV_C7 B))
  by (eapply fe_seg8; eassumption).
assert (P7 : fe_from (SK := FSH_Base.fsB_sink_head) B FS_PSTAT_FP (fe_post (SK := FSH_Base.fsB_sink_head) B FS_PSTAT_FP)
  (fe_ss RA_caw [fe_len_atom 46]) (INV_C6 B))
  by (eapply fe_seg7; eassumption).
assert (P6 : fe_from (SK := FSH_Base.fsB_sink_head) B FS_PSTAT_FP (fe_post (SK := FSH_Base.fsB_sink_head) B FS_PSTAT_FP)
  (fe_ss PC_C5 [fe_len_lit (-1)]) (INV_C5 B))
  by (eapply fe_seg6; eassumption).
assert (P5 : fe_from (SK := FSH_Base.fsB_sink_head) B FS_PSTAT_FP (fe_post (SK := FSH_Base.fsB_sink_head) B FS_PSTAT_FP)
  (fe_ss RA_cno [fe_len_lit (-1)]) (INV_C2 B))
  by (eapply fe_seg5; eassumption).
assert (P3 : fe_from (SK := FSH_Base.fsB_sink_head) B FS_PSTAT_FP (fe_post (SK := FSH_Base.fsB_sink_head) B FS_PSTAT_FP)
  (fe_ss RA_memchr []) (INV_C1 B))
  by (eapply fe_seg3; eassumption).
assert (P2 : fe_from (SK := FSH_Base.fsB_sink_head) B FS_PSTAT_FP (fe_post (SK := FSH_Base.fsB_sink_head) B FS_PSTAT_FP)
  ss_B2 (INV_B2 B))
  by (eapply fe_seg2; eassumption).
assert (P01 : fe_enter (SK := FSH_Base.fsB_sink_head) B FS_PSTAT_FP (fe_post (SK := FSH_Base.fsB_sink_head) B FS_PSTAT_FP)
  ss_B2 (INV_B2 B))
  by (eapply fe_seg01; eassumption).
(* the contract *)
unfold fs_lib_contract_x. intros ly S W regs mem md p n pl M K' live cnt HAI HPRE HST Hc0 Hc1 Hl HK.
rewrite HLS.
assert (HB : forall fpos, fe_base B (mkFECX ly S W regs mem md p n pl M live cnt fpos)).
{ intros fpos. split; [exact HPRE|]. split; [exact HST|]. split; [exact Hc0|].
  split; [exact Hc1 | exact Hl]. }
apply (P01 ly S W regs mem md p n pl M live cnt HB P2 HAI).
intros W' c' Hwle HAI' (fpos & HPOST).
destruct (fe_post_lib (SK := FSH_Base.fsB_sink_head) B TS _ W' c' (HB fpos) HPOST)
  as (ly' & S' & regs' & mem' & md' & k & cnt' & Ec & HP & Hst & Hcnt).
apply (HK (LL 0 (m_fs md) []) W' c' Hwle HAI').
exists ly', S', regs', mem', md', k, cnt'. split; [exact Ec|]. split; [exact HP|]. split; [exact Hst|].
cbn [c_cnt] in Hcnt. unfold FE_CNT_MAX, CRT_ALLOCS in Hcnt. unfold FS_CNT_LIB. lia.
Qed.
End t.
