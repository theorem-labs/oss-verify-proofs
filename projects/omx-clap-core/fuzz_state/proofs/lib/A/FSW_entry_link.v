(* fs program part, lane ENTRY: the facts about B the LLVMFuzzerTestOneInput walk takes as Section hypotheses, derived
   from fs_entry_goal's premises (TfibLib B, A/ACeg.v, owner RELOC): the four ASan cells in the kit's constants, the
   engine's api_env and model_laws, the stack_malloc progress law (every B) and the frame flag law.
   rule 24: no function proved (fs's harness entry).
   Port-from: cgif_file_fuzzer lib/A/ACfi.v:61-75 (link_ML, link_SMP, link_FFL) and lib/A/ACeg.v:38-42 (tl_env); here
   over fs's relocated ACeg (TFIB_IMG_END = IMG_TOP) and YCbq's api_env / frame_flag_lawP. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YCbp YC5d YI00 YI04 YI16 YK06 YO09 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YG05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require ACeg ACej AF0l.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section l. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TL : ACeg.TfibLib B.

Lemma fe_tl_got_shadow : as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address.
Proof. rewrite (ACeg.tl_got_shadow B TL). reflexivity. Qed.
Lemma fe_tl_shadow_cell : as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address.
Proof. rewrite (ACeg.tl_shadow_cell B TL). reflexivity. Qed.
Lemma fe_tl_got_uar : as_got_uar B = fs_D_GOT_uar.
Proof. rewrite (ACeg.tl_got_uar B TL). reflexivity. Qed.
Lemma fe_tl_uar_cell : as_uar_cell B = fs_D_uar_cell.
Proof. rewrite (ACeg.tl_uar_cell B TL). reflexivity. Qed.

(* ACeg.v:38 tl_env's proof, over YCbq's api_env *)
Lemma fe_api_env : api_env tfibsegs B.
Proof.
split; [exact (ACeg.tl_errno B TL)|]. split; [exact (ACeg.tl_errno_img B TL)|].
rewrite (ACeg.tl_code B TL), (ACeg.tl_universe B TL).
split; apply ACej.memZL_In; vm_compute; reflexivity.
Qed.

(* cgif ACfi.v:61-62 link_ML *)
Lemma fe_model_laws : model_laws (as_universe B).
Proof. rewrite (ACeg.tl_universe B TL). exact (YG05.model_laws_ok ACej.Tfib_universe ACej.Tfib_universe_ok). Qed.
End l.

(* cgif ACfi.v:63-64 link_SMP: every B *)
Lemma fe_stack_malloc_progress : forall B, stack_malloc_progressP B.
Proof. intros B s cid W Hc Hn. exact (YG05.stack_malloc_progress (as_universe B) s cid W Hc Hn). Qed.

(* cgif ACfi.v:65-75 link_FFL: every B, from AR's flag / client-image laws and the image cover *)
Lemma fe_frame_flag_law : forall {fx : YK11.FPState} {rc : YM05.RunCeil} B, frame_flag_lawP tfibsegs B.
Proof.
intros fx rc B ly S W mem md cid pos HAR Hin.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct (al_flag _ _ LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (ACeg.tfib_img_cover ly S md L) as [C1 C2].
unfold ACeg.TFIB_IMG_LO, ACeg.TFIB_IMG_END in C1, C2.
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil]. unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* ---- the sink head of a journal with a closed footprint does not matter ----
   ajournal mentions the sink head only in its image clause's fp_spares (YCbq.v:87), which holds at any head when the
   footprint holds no sink token. fs_entry_goal's callee specs run at the goal's sink head SK, the walk's journal at
   the head ACfn's tfib_lib_post_x was elaborated with (A/AE2k.v tfib_sink_head); every callee footprint of the entry
   (FS_PSTAT_FP, decode's FS_PSTAT_FP ++ [*lenp], fuzz_free's FS_PSTAT_FP ++ its block, []) is closed. *)
Lemma fe_ajournal_sk : forall {rc : YM05.RunCeil} (SK1 SK2 : YI16.sink_head) (segs : list Segment) (B : asyms) STK sp0 FP
  ly S W mem md own ly' S' W' mem' md' k,
  ~ YI16.sink_open_fp FP ->
  ajournal (SK := SK1) segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  ajournal (SK := SK2) segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Proof.
intros rc SK1 SK2 segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k Hcl
  (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
repeat (split; [eassumption|]).
split; [intros a Hi Hns He Hnf _; exact (F3 a Hi Hns He Hnf (@fp_spares_closed SK1 FP a Hcl))|].
repeat (split; [eassumption|]). exact HQT.
Qed.

(* ---- widening the footprint of a closed-footprint journal (and moving its sink head) ----
   The walk journals over FS_PSTAT_FP, which holds no sink token, so its model step is the closed one (same_io) and the
   sink cells are kept; at the end the footprint is widened to ACfn's tfib_lib_post_x footprint
   sink_token :: FS_PSTAT_FP: every clause protects fewer bytes under a larger footprint. *)
Lemma fe_ajournal_widen : forall {rc : YM05.RunCeil} (SK1 SK2 : YI16.sink_head) (segs : list Segment) (B : asyms) STK sp0
  FP FP' ly S W mem md own ly' S' W' mem' md' k,
  ~ YI16.sink_open_fp FP -> (forall a, inFP FP a -> inFP FP' a) ->
  ajournal (SK := SK1) segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  ajournal (SK := SK2) segs B STK sp0 FP' ly S W mem md own ly' S' W' mem' md' k.
Proof.
intros rc SK1 SK2 segs B STK sp0 FP FP' ly S W mem md own ly' S' W' mem' md' k Hcl HFP
  (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
split; [exact HAR|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
split; [exact (aos_step_mono FP FP' md md' (fun H => False_ind _ (Hcl H)) Hio)|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|]. split; [exact F1|].
split; [intros p n i H1 H2 Hi Hnf; exact (F2 p n i H1 H2 Hi (fun H => Hnf (HFP _ H)))|].
split; [intros a Hi Hns He Hnf _; exact (F3 a Hi Hns He (fun H => Hnf (HFP _ H)) (@fp_spares_closed SK1 FP a Hcl))|].
split; [intros cid pos a Hin Hr Hnf; exact (F4 cid pos a Hin Hr (fun H => Hnf (HFP _ H)))|].
split; [intros p n i H1 H2 Hi; exact (HFP _ (Hgone p n i H1 H2 Hi))|].
split; [exact Hpres|]. split; [exact Hstatic|]. split; [exact F5|]. exact HQT.
Qed.

