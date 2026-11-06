(* fs program part, lane ENTRY: the LLVMFuzzerTestOneInput walk's post fe_post (FSW_entry_defs.v, over the walk's closed
   footprint FS_PSTAT_FP at the walk's sink head) gives ACfn's tfib_lib_post_x at the leaf LL 0 (m_fs md) [] (the
   checksum shape's leaf) plus fs_stat: the journal widened to sink_token :: FS_PSTAT_FP and moved to ACfn's sink head
   (FSW_entry_link.fe_ajournal_widen), the descriptor table and the file system from the closed footprint's same_io,
   the sink and meta invariants by YE01's kept lemmas under the sink's image laws (AIL; fs's A/AD1u.v tfib_AIL gives
   them for TfibB).
   rule 24: no function proved (fs's harness entry).
   Port-from: cgif_file_fuzzer lib/A/ACfj.v (lx_E / tfib_lib_x_body: the post's model and sink clauses from the walk's
   journal) and lib/Reusable/YE01.v asink_none_kept / ameta_inv_kept. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YCbp YC5d YI00 YI04 YI16 YK06 YO09 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YE00 YE01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import ACfn FSH_Harness FSH_Fn_entry FSW_entry_defs FSW_entry_link.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AE2k AD1u.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Lemma fe_pstat_closed : ~ YI16.sink_open_fp FS_PSTAT_FP.
Proof. apply sink_closed_pos. unfold FS_PSTAT_FP. repeat constructor; cbn; lia. Qed.
Lemma fe_inFP_widen : forall a, inFP FS_PSTAT_FP a -> inFP (YI16.sink_token :: FS_PSTAT_FP) a.
Proof. intros a (r & Hr & Ha). exists r. split; [right; exact Hr | exact Ha]. Qed.
(* the stdio and meta cells of fs's sink (A/AE2k.v tfib_K) are off the walk's footprint: A/AD1u.v states it for the
   wider library footprint *)
Lemma fe_aenv_off : forall a, aenv_addr AE2k.tfib_K a -> ~ inFP FS_PSTAT_FP a.
Proof. intros a Ha HF. exact (AD1u.tfib_aenv_off_lib_fp a Ha (fe_inFP_widen a HF)). Qed.
Lemma fe_meta_off : forall a, ak_meta_mem AE2k.tfib_K <= a < ak_meta_mem AE2k.tfib_K + 8 -> ~ inFP FS_PSTAT_FP a.
Proof. intros a Ha HF. exact (AD1u.tfib_meta_off_lib_fp a Ha (fe_inFP_widen a HF)). Qed.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the sink's image laws at ACfn's sink head (FSW_entry.v gives them by A/AD1u.v tfib_AIL from TfibSyms B) *)
Hypothesis AIL : @asink_img_laws AE2k.tfib_sink_head tfibsegs B AE2k.tfib_K.

Lemma fe_post_lib : forall cx W' c', fe_base B cx -> fe_post B FS_PSTAT_FP cx W' c' ->
  exists ly' S' regs' mem' md' k cnt',
    c' = cfg_at tfibsegs RA_LLVMF regs' mem' md' /\
    tfib_lib_post_x B ameter_triv XL0 (c_regs cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) (c_p cx) (c_n cx)
      (c_M cx) (LL 0 (m_fs (c_md cx)) []) ly' S' W' regs' mem' md' k /\
    fs_stat tfibsegs W' mem' (c_live cx) cnt' /\ c_cnt cx <= cnt' <= c_cnt cx + FE_CNT_MAX.
Proof.
intros cx W' c' HB (ly' & S' & regs' & mem' & md' & k & cnt' & -> & HJ & Hk & HP & H10 & Hperm & Hio & Hpay & Hst & Hcnt).
destruct HB as ((HPRE0 & Hra & Hp & Hn & Hpn & Hnpl & HPL & Hfr0 & Hev & Hlive & HROS & HSNK & HFD & HSORT & HAM & HMOK) & _).
exists ly', S', regs', mem', md', k, cnt'. split; [reflexivity|]. split; [|split; [exact Hst | exact Hcnt]].
pose proof (fe_ajournal_sk SK AE2k.tfib_sink_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fe_pstat_closed HJ) as HJt.
destruct Hio as (Efd & Eio & Efsys & Eproc).
unfold tfib_lib_post_x.
split; [exact (fe_ajournal_widen SK AE2k.tfib_sink_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fe_pstat_closed fe_inFP_widen HJ)|].
split; [exact Hk|]. split; [exact HP|]. split; [exact H10|]. split; [exact Hperm|].
split; [intros fd; unfold m_fds; rewrite Efd; reflexivity|].
split; [cbn [ll_fs]; unfold m_fs; rewrite Efsys; reflexivity|].
split; [reflexivity|]. split; [reflexivity|]. split; [cbn [ll_fs]; exact HSORT|].
split.
{ eapply (asink_none_kept (SK := AE2k.tfib_sink_head) tfibsegs B AE2k.tfib_K AIL);
    [exact HJt | exact fe_pstat_closed | | exact HSNK].
  exact fe_aenv_off. }
split.
{ eapply (ameta_inv_kept (SK := AE2k.tfib_sink_head) tfibsegs B AE2k.tfib_K AIL); [exact HJt | | exact HAM].
  exact fe_meta_off. }
split; [exact I|]. exact Hpay.
Qed.
End p.
