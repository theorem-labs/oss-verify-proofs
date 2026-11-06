(* fs program part, lane ENTRY, IMAGE B (fs.asan-ubsan, pinned sha256 5ac5ce0954f8...): the LLVMFuzzerTestOneInput
   walk's post fe_post (lib/B/FSW_entry_defs.v, over the walk's closed footprint FS_PSTAT_FP at the walk's sink head)
   gives lib/B/FSH_Harness.v's fs_lib_post_x at the leaf LL 0 (m_fs md) [] (the checksum shape's leaf), at B's sink
   head FSH_Base.fsB_sink_head and B's sink / meta cells YE2k.tfib_K, plus fs_stat: the journal widened to
   sink_token :: FS_PSTAT_FP and moved to fsB_sink_head (FSW_entry_link.fe_ajournal_widen), the descriptor table and the
   file system from the closed footprint's same_io, the sink and meta invariants by YE01's kept lemmas under the sink's
   image laws, lib/B/YD1u.v tfib_AIL from YF0m.TfibSyms B (YD1u's sink head YE2k.tfib_sink_head and
   FSH_Base.fsB_sink_head are both {| sk_ofl_head := 0x5fbb28 |}, so its laws are the laws at fsB_sink_head by
   conversion). Also fe_lib_pre_of_fs: the harness pre fs_lib_pre_x at tfib_K is fe_base's tfib_lib_pre_x (B.YCfn),
   by conversion (the same constants under B's two names).
   rule 24: proves function LLVMFuzzerTestOneInput (the walk's post; reuse search: proof-index
   LLVMFuzzerTestOneInput, ported from a working branch 08ad70da3bf).
   Ported from: lib/A/FSW_entry_post.v (a working branch 0d34d65d2b7), A's names; A's conclusion
   ACfn.tfib_lib_post_x is B's FSH_Harness.fs_lib_post_x (A's ACfn post restated at build B). fe_aenv_off / fe_meta_off
   are proved here from tfib_K's cells (the proof text of lib/B/YD1u.v tfib_aenv_off_lib_fp / tfib_meta_off_lib_fp).
   Section p hypotheses: TS : YF0m.TfibSyms B, a premise of lib/B/FSH_Fn_entry.v fs_entry_goal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YCbp YC5d YI00 YI04 YI16 YK06 YO09 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YE00 YE01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v FSH_Base FSH_Rt FSPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YCfn FSH_Harness FSH_Fn_entry FSW_entry_defs FSW_entry_link.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YE2k YF0m YD1u.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Lemma fe_pstat_closed : ~ YI16.sink_open_fp FS_PSTAT_FP.
Proof. apply sink_closed_pos. unfold FS_PSTAT_FP. repeat constructor; cbn; lia. Qed.
Lemma fe_inFP_widen : forall a, inFP FS_PSTAT_FP a -> inFP (YI16.sink_token :: FS_PSTAT_FP) a.
Proof. intros a (r & Hr & Ha). exists r. split; [right; exact Hr | exact Ha]. Qed.
(* the stdio and meta cells of B's sink (lib/B/YE2k.v tfib_K) are off the walk's footprint; the proof text of
   lib/B/YD1u.v tfib_aenv_off_lib_fp / tfib_meta_off_lib_fp, for the wider library footprint *)
Ltac fe_kcst := unfold YE2k.A_threaded, YE2k.A_need_locks, YE2k.A_ofl_lock, YE2k.A_ofl_head, YE2k.FF_canary,
  YE2k.FF_got_canary, YE2k.FF_meta_ptr, YE2k.FF_meta_mem, YE2k.A_stdio_read, YE2k.A_stdio_write, YE2k.A_stdio_seek,
  YE2k.A_stdio_close in *.
Lemma fe_aenv_off_lib_fp : forall a, aenv_addr YE2k.tfib_K a -> ~ inFP (YI16.sink_token :: FS_PSTAT_FP) a.
Proof.
intros a Ha (r & Hr & Hra).
unfold FS_PSTAT_FP, YI16.sink_token in Hr. cbn [In] in Hr.
destruct Ha as [Ha|Ha].
- apply Exists_exists in Ha as (x & Hx & Hz). unfold YE2k.tfib_K, YE2k.tfib_owned in Hx. cbn [ak_owned In] in Hx.
  unfold in_zr in Hz.
  destruct Hx as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hz; fe_kcst;
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hra; lia.
- unfold ak_ofl_head, YE2k.tfib_K in Ha. cbn [ak_ofl_lock] in Ha. fe_kcst.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hra; lia.
Qed.
Lemma fe_meta_off_lib_fp : forall a, ak_meta_mem YE2k.tfib_K <= a < ak_meta_mem YE2k.tfib_K + 8 ->
  ~ inFP (YI16.sink_token :: FS_PSTAT_FP) a.
Proof.
intros a Ha (r & Hr & Hra). unfold YE2k.tfib_K in Ha. cbn [ak_meta_mem] in Ha. fe_kcst.
unfold FS_PSTAT_FP, YI16.sink_token in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hra; lia.
Qed.
Lemma fe_aenv_off : forall a, aenv_addr YE2k.tfib_K a -> ~ inFP FS_PSTAT_FP a.
Proof. intros a Ha HF. exact (fe_aenv_off_lib_fp a Ha (fe_inFP_widen a HF)). Qed.
Lemma fe_meta_off : forall a, ak_meta_mem YE2k.tfib_K <= a < ak_meta_mem YE2k.tfib_K + 8 -> ~ inFP FS_PSTAT_FP a.
Proof. intros a Ha HF. exact (fe_meta_off_lib_fp a Ha (fe_inFP_widen a HF)). Qed.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

(* the harness pre at B's sink / meta cells is fe_base's pre: the same constants under B's two names (FSH_Base
   FS_RA_LLVMF / FS_EMPTY / FS_EV_LIB and ACfn's policy LLVMF_STK / LIVE_LIB against YCfn's RA_LLVMF / A_EMPTY / EV_LIB /
   LLVMF_STK / LIVE_LIB, fsbsegs against tfibsegs) *)
Lemma fe_lib_pre_of_fs : forall regs ly S (W : world tfibsegs) mem md p n pl M,
  fs_lib_pre_x B ameter_triv XL0 YE2k.tfib_K regs ly S W mem md p n pl M ->
  tfib_lib_pre_x B ameter_triv XL0 FS_RLO FS_RHI regs ly S W mem md p n pl M.
Proof. intros regs ly S W mem md p n pl M H. exact H. Qed.

(* B's symbol facts, a premise of fs_entry_goal: they give the sink's image laws (lib/B/YD1u.v tfib_AIL) *)
Hypothesis TS : YF0m.TfibSyms B.

Lemma fe_post_lib : forall cx W' c', fe_base B cx -> fe_post B FS_PSTAT_FP cx W' c' ->
  exists ly' S' regs' mem' md' k cnt',
    c' = cfg_at tfibsegs RA_LLVMF regs' mem' md' /\
    fs_lib_post_x (SK := FSH_Base.fsB_sink_head) B ameter_triv XL0 YE2k.tfib_K (c_regs cx) (c_ly cx) (c_S cx) (c_W cx)
      (c_mem cx) (c_md cx) (c_p cx) (c_n cx) (c_M cx) (LL 0 (m_fs (c_md cx)) []) ly' S' W' regs' mem' md' k /\
    fs_stat tfibsegs W' mem' (c_live cx) cnt' /\ c_cnt cx <= cnt' <= c_cnt cx + FE_CNT_MAX.
Proof.
intros cx W' c' HB (ly' & S' & regs' & mem' & md' & k & cnt' & -> & HJ & Hk & HP & H10 & Hperm & Hio & Hpay & Hst & Hcnt).
(* the sink's image laws at B's sink head: YD1u's, at YE2k.tfib_sink_head, convertible to FSH_Base.fsB_sink_head *)
pose proof (YD1u.tfib_AIL B TS : @asink_img_laws FSH_Base.fsB_sink_head tfibsegs B YE2k.tfib_K) as AIL.
destruct HB as ((HPRE0 & Hra & Hp & Hn & Hpn & Hnpl & HPL & Hfr0 & Hev & Hlive & HROS & HSNK & HFD & HSORT & HAM & HMOK) & _).
exists ly', S', regs', mem', md', k, cnt'. split; [reflexivity|]. split; [|split; [exact Hst | exact Hcnt]].
pose proof (fe_ajournal_sk SK FSH_Base.fsB_sink_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fe_pstat_closed HJ) as HJt.
destruct Hio as (Efd & Eio & Efsys & Eproc).
unfold fs_lib_post_x.
split; [exact (fe_ajournal_widen SK FSH_Base.fsB_sink_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  fe_pstat_closed fe_inFP_widen HJ)|].
split; [exact Hk|]. split; [exact HP|]. split; [exact H10|]. split; [exact Hperm|].
split; [intros fd; unfold m_fds; rewrite Efd; reflexivity|].
split; [cbn [ll_fs]; unfold m_fs; rewrite Efsys; reflexivity|].
split; [reflexivity|]. split; [reflexivity|]. split; [cbn [ll_fs]; exact HSORT|].
split.
{ eapply (asink_none_kept (SK := FSH_Base.fsB_sink_head) tfibsegs B YE2k.tfib_K AIL);
    [exact HJt | exact fe_pstat_closed | | exact HSNK].
  exact fe_aenv_off. }
split.
{ eapply (ameta_inv_kept (SK := FSH_Base.fsB_sink_head) tfibsegs B YE2k.tfib_K AIL); [exact HJt | | exact HAM].
  exact fe_meta_off. }
split; [exact I|]. exact Hpay.
Qed.
End p.
