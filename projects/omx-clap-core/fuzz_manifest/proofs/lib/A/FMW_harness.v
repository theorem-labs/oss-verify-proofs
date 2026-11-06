(* fm program part, the harness assembly: fm_lib_contract_x (FMH_Harness.v) at LS := checksum_shape, MT := ameter_triv,
   XM_LIB = XN_LIB := 0, from the LLVMFuzzerTestOneInput walk (FMW_llvmfZ.v llvmf_walk, with check_round_trip's contract
   from FMW_crt.v check_round_trip_holds) and the journal facts that give the rest of the donor post tfib_lib_post_x
   (A/ACfn.v): footprint FM_PSTAT_FP widened to sink_token :: FM_PSTAT_FP, no file opened (the footprint does not open the
   sink: file descriptors and file system as they were), the sink and meta invariants of the driver's image (YE01
   asink_none_kept, ameta_inv_kept), the trivial meter. The Section hypotheses are the contracts of the callees below
   LLVMFuzzerTestOneInput other than check_round_trip (runtime: FMH_Rt.v; program: FMH_Fn.v) and the image facts. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d YCbp YC20.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI16 YK06 YO09 YM05 YE00 YE01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest Require Import lib.ZTraceSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AF0l ACej FMPstat AE2k ACfn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMH_Fn FMH_Harness.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_kit FMW_seg FMW_llvmf0 FMW_crt FMW_llvmfZ.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require ACeg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the universe row of fm_lib_x's Section hypotheses (UNIV : fm_univ B) comes from the TfibLib form: tl_universe *)
Lemma fm_univ_of_tl : forall B, ACeg.TfibLib B -> fm_univ B.
Proof. intros B TL. unfold fm_univ. rewrite (ACeg.tl_universe B TL). apply incl_refl. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* a journal stays a journal under a larger footprint *)
Lemma ajournal_fp_widen : forall (B : asyms) STK sp0 FP FP' ly S (W : world tfibsegs) mem md own ly' S' W' mem' md' k,
  (forall a, inFP FP a -> inFP FP' a) ->
  ajournal tfibsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  ajournal tfibsegs B STK sp0 FP' ly S W mem md own ly' S' W' mem' md' k.
Proof.
intros B STK sp0 FP FP' ly S W mem md own ly' S' W' mem' md' k HI
  (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
assert (HO : YI16.sink_open_fp FP -> YI16.sink_open_fp FP').
{ intros (r & Hr & H0). destruct (HI 0 (ex_intro _ r (conj Hr H0))) as (r' & Hr' & H0'). exists r'. split; [exact Hr' | exact H0']. }
split; [exact HAR|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
split; [exact (aos_step_mono FP FP' md md' HO Hio)|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|]. split; [exact F1|].
split; [intros p n i H1 H2 Hi Hn; apply (F2 p n i H1 H2 Hi); intros Hf; exact (Hn (HI _ Hf))|].
split.
{ intros a Hi Hns He Hn Hsp. apply (F3 a Hi Hns He); [intros Hf; exact (Hn (HI _ Hf))|].
  intros Ho. exact (Hsp (HO Ho)). }
split; [intros cid pos a H1 H2 Hn; apply (F4 cid pos a H1 H2); intros Hf; exact (Hn (HI _ Hf))|].
split; [intros p n i H1 H2 Hi; exact (HI _ (Hgone p n i H1 H2 Hi))|].
split; [exact Hpres|]. split; [exact Hstatic|]. split; [exact F5 | exact HQT].
Qed.

(* the AI-wrapped run gives the srealizes leaf (cgif_file A/ACfh.v srz_enter) *)
Lemma srz_enter : forall (W : world tfibsegs) (c : config) (T : TSet),
  AI tfibsegs (w_H W) (w_A W) (cfg_model c) ->
  SRr tfibsegs W c (fun W' c' => AI tfibsegs (w_H W') (w_A W') (cfg_model c') -> srealizes tfibsegs c' T) ->
  srealizes tfibsegs c T.
Proof. intros W c T HAI HS. apply (HS HAI T). intros W' c' _ HAI' HK. exact (HK HAI'). Qed.

(* the journal of a footprint that does not open the sink keeps file descriptors and the file system *)
Lemma ajournal_closed_io : forall (B : asyms) STK sp0 FP ly S (W : world tfibsegs) mem md own ly' S' W' mem' md' k,
  ~ YI16.sink_open_fp FP ->
  ajournal tfibsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof.
intros B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k Hcl HJ. pose proof HJ as (_ & _ & _ & _ & Hos & _).
destruct (aos_step_closed FP md md' Hcl Hos) as (Efd & Efsys & _ & _).
unfold m_fds, m_fs. rewrite Efd, Efsys. split; reflexivity.
Qed.

Lemma pstat_in_lib_fp : forall a, inFP FM_PSTAT_FP a -> inFP (YI16.sink_token :: FM_PSTAT_FP) a.
Proof. intros a (r & Hr & Ha). exists r. split; [right; exact Hr | exact Ha]. Qed.
Lemma pstat_closed' : ~ YI16.sink_open_fp FM_PSTAT_FP.
Proof. intros (r & Hr & H0). unfold FM_PSTAT_FP in Hr. destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in H0; lia. Qed.
Lemma aenv_off_pstat : forall a, aenv_addr tfib_K a -> ~ inFP FM_PSTAT_FP a.
Proof.
intros a Ha Hf. unfold aenv_addr in Ha. rewrite tfib_K_head in Ha. cbn [ak_owned tfib_K] in Ha.
destruct Hf as (r & Hr & Hra). unfold FM_PSTAT_FP in Hr.
destruct Ha as [Ha | Ha].
- apply Exists_exists in Ha as (x & Hx & Hz). unfold tfib_owned in Hx. unfold YG0n.in_zr in Hz.
  unfold A_threaded, A_need_locks, A_ofl_lock, FF_canary in Hx.
  destruct Hx as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hz;
    destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hra; lia.
- unfold A_ofl_head in Ha. destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hra; lia.
Qed.
Lemma meta_off_pstat : forall a, ak_meta_mem tfib_K <= a < ak_meta_mem tfib_K + 8 -> ~ inFP FM_PSTAT_FP a.
Proof.
intros a Ha Hf. cbn [ak_meta_mem tfib_K] in Ha. unfold FF_meta_mem in Ha.
destruct Hf as (r & Hr & Hra). unfold FM_PSTAT_FP in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hra; lia.
Qed.

Section h.
Variable B : asyms.
Hypothesis AIL : asink_img_laws tfibsegs B tfib_K.
Hypothesis FB : FmB B.
Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis UNIV : fm_univ B.
Hypothesis AMALLOC : amalloc04_rule tfibsegs B ameter_triv.
Hypothesis AFREE : afree04_rule tfibsegs B ameter_triv.
Hypothesis AICPY : aintrin_realizes tfibsegs B OCpy FM_asan_memcpy.
Hypothesis STRLEN : astrlen_realizes tfibsegs B PC_strlen.
Hypothesis MEMCHR : amemchr_realizes tfibsegs B PC_memchr.
Hypothesis SNP : asnprintf_realizes tfibsegs B PC_snprintf.
Hypothesis ALIVE : fuzz_alloc_live_spec tfibsegs B.
Hypothesis APRESET : fuzz_alloc_peak_reset_spec tfibsegs B.
Hypothesis APEAK : fuzz_alloc_peak_spec tfibsegs B.
Hypothesis NAMES : names_spec tfibsegs B CTX_lv2_locate_manifest_names.
Hypothesis PLAIN : plain_spec tfibsegs B.
Hypothesis ASR : as_ruled_spec tfibsegs B CTX_as_ruled.
Hypothesis CNO : check_no_overread_spec tfibsegs B CTX_check_no_overread.
Hypothesis CBA : check_bounded_alloc_spec tfibsegs B.
Hypothesis CAW : check_as_written_spec tfibsegs B.
Hypothesis CRC : check_reject_clean_spec tfibsegs B.
Hypothesis STARVED : check_reject_clean_starved_spec tfibsegs B CTX_check_reject_clean_starved.

Theorem fm_lib_x : fm_lib_contract_x (LS := checksum_shape) B ameter_triv (fun _ => 0) (fun _ => 0).
Proof.
pose proof (check_round_trip_holds B) as CRT; repeat specialize (CRT ltac:(assumption)).
pose proof (llvmf_walk B) as WALK; repeat specialize (WALK ltac:(assumption)).
intros ly S W regs mem md p n pl M K ci Hci (cnt & HST & Hc) HAI HPRE HK.
change (@LIBK checksum_shape pl (m_fs md) K) with (K (LL 0 (m_fs md) [])).
apply (srz_enter W (cfg_at tfibsegs A_LLVMF regs mem md) _ HAI).
eapply SRr_mono; [apply (WALK regs ly S W mem md p n pl M 0 cnt);
  split; [exact HPRE | split; [exact HST | unfold CNT_LIB in *; lia]]|].
cbv beta. intros W' c' Hwle (ly' & S' & regs' & mem' & md' & k & cnt' & -> & HJ & Hk & HP & H10 & Hperm & Hbytes & HST' & Hcnt) HAI'.
apply (HK (LL 0 (m_fs md) []) W'); [exact Hwle | exact HAI' |].
exists ly', S', regs', mem', md', k. split; [reflexivity|].
split; [|exists cnt'; split; [exact HST' | unfold CNT_LIB in *; lia]].
pose proof HPRE as (HAP & Hra & H10p & H11p & Hpn & Hlen & Hga & Hfr & Hev & Hbb & Haro & Hsink & Hfd & Hsorted & Hmeta & Hmo).
destruct (ajournal_closed_io B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pstat_closed' HJ) as [Efds Efs].
unfold tfib_lib_post_x.
split; [exact (ajournal_fp_widen B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pstat_in_lib_fp HJ)|].
split; [unfold EV_LLVMF, EV_check_no_overread, EV_check_reject_clean_starved, EV_check_round_trip, EV_names, EV_LIB in *; lia|].
split; [exact HP|]. split; [exact H10|]. split; [exact Hperm|].
split; [intros fd; rewrite Efds; reflexivity|].
split; [exact Efs|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hsorted|].
split; [exact (asink_none_kept tfibsegs B tfib_K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ pstat_closed' aenv_off_pstat Hsink)|].
split; [exact (ameta_inv_kept tfibsegs B tfib_K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ meta_off_pstat Hmeta)|].
split; [exact I | exact Hbytes].
Qed.
End h.
End d.
