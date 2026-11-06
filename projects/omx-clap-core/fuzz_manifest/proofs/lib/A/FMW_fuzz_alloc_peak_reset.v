(* fuzz_alloc_peak_reset 0x81bac (alloc.c:128-131): auipc/ld g_live; auipc/sd g_peak; ret. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI00 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_fuzz_alloc_base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HB : TfibSyms B.

Definition ss_pr : sstate :=
  mkSS A_fuzz_alloc_peak_reset sr_atoms [fm_rcell G_LIVE 32; fm_wcell G_PEAK 33] None (mkFacts [] [] []).

Theorem fuzz_alloc_peak_reset_holds : fuzz_alloc_peak_reset_spec tfibsegs B.
Proof.
intros ly S W regs mem md ch live peak cnt fail HPRE HG.
pose proof HPRE as (HAN & _).
pose proof HAN as (HAR & Hra & _ & _ & _ & Hstk & HpresE & _). unfold YK0s.ret_ok in Hra.
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
pose proof HG as (GL & GP & GC & GF & Hlp & Hp64 & Hc64 & Hf64).
pose proof fma_wx as Hwx.
assert (HS : st_ok tfibsegs (Ereg regs [w64 live; w64 peak]) ss_pr
  (restrict (w_H W) (mkst regs (Z_to_bv 64 A_fuzz_alloc_peak_reset) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. apply entry_st_ok.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (region_ok_fm_rcell _ _ G_LIVE 32 live); [exact GL | | lia | unfold G_LIVE; lia | unfold G_LIVE; lia].
      exact (ew_Ereg_extra regs [w64 live; w64 peak] 0).
    + apply (region_ok_fm_wcell _ _ G_PEAK 33 peak); [exact GP | | lia | unfold G_PEAK; lia | unfold G_PEAK; lia].
      exact (ew_Ereg_extra regs [w64 live; w64 peak] 1).
  - cbn. repeat split; try exact I; unfold extent_disjoint, fm_rcell, fm_wcell, G_LIVE, G_PEAK;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; lia.
  - exact I. }
unfold cfg_at. change (w64 A_fuzz_alloc_peak_reset) with (Z_to_bv 64 A_fuzz_alloc_peak_reset).
remember (Ereg regs [w64 live; w64 peak]) as E eqn:HE.
srr_run_with tbl_fma_ok HS.
eapply (SRr_ret_at tfibsegs tbl_fma tbl_fma_ok Hwx W E); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat2. rewrite wvb_collapse.
assert (E1 : ew E 1 = getr regs 1) by (rewrite HE; exact (ew_Ereg_nat regs [w64 live; w64 peak] 1 1%bv eq_refl)).
assert (E32 : ew E 32 = w64 live) by (rewrite HE; exact (ew_Ereg_extra regs [w64 live; w64 peak] 0)).
rreg HS (1%bv : bv 5) R1.
(* the write window of the run is exactly g_peak's 8 bytes *)
assert (WIN : forall a, in_wrange E (ss_mem ss_pr) a -> G_PEAK <= a < G_PEAK + 8).
{ intros a (r & Hin & Hw). cbn [ss_pr ss_mem In] in Hin.
  destruct Hin as [<-|[<-|[]]]; cbn [fm_rcell fm_wcell YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia. }
assert (RAW : forall x : word, ~ (G_PEAK <= bv_unsigned x < G_PEAK + 8) -> ms_mem ms x = mem x).
{ intros x Hx. apply HF. intros Hin. exact (Hx (WIN _ Hin)). }
assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ (G_PEAK <= a < G_PEAK + 8) ->
  aview tfibsegs (w_H W) (ms_mem ms) a = aview tfibsegs (w_H W) mem a).
{ intros a Ha Hc. apply aview_eq_of. unfold mrestrict. rewrite RAW; [reflexivity|].
  rewrite unsigned_lit_small by lia. exact Hc. }
(* g_peak now holds g_live's value *)
assert (VP : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) G_PEAK 8 live).
{ eapply (val_mem_of_chunk8 E _ (ss_mem _) 1%nat G_PEAK (SOff 32 0) live);
  [ exact (st_ok_mem_ok E _ (w_H W) ms HS) | vm_compute; reflexivity
  | cbn [sv_denot]; rewrite E32; cbn [YG0d.w64]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | lia ]. }
assert (HVIS : forall i, 0 <= i < 8 -> aview tfibsegs (w_H W) (ms_mem ms) (G_PEAK + i) <> None).
{ intros i Hi. exact (aview_some_of_val_mem (w_H W) (ms_mem ms) G_PEAK 8 live i VP ltac:(cbn; lia)). }
assert (HAR2 : AR tfibsegs B ly S W (ms_mem ms) md).
{ apply (AR_write_static B HB ly S W mem md (ms_mem ms) G_PEAK HAR
    ltac:(vm_compute; tauto) RAW HVIS). }
unfold fpost, apost_base.
exists ly, S, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md) mat2 md).
split; [rewrite R1, E1, Hra; reflexivity|].
split.
{ apply (ajournal_materialize tfibsegs B (AR_laws_ok tfibsegs B) fma_segs_low).
  apply (ajournal_pstat1 B STK_fuzz_alloc ly S W regs mem md ch (ms_mem ms) G_PEAK HAN
    ltac:(vm_compute; tauto) HAR2).
  - intros a Ha _ Hc. exact (AV a Ha Hc).
  - intros a Ha. destruct (HpresE a Ha) as [Hh [b Hb]].
    split; [exact Hh|]. exists b. rewrite RAW; [exact Hb|].
    rewrite unsigned_lit_small by (unfold STK_fuzz_alloc in *; lia). unfold G_PEAK, STK_fuzz_alloc in *. lia. }
split.
{ eapply aregs_preserved_of_st_ok; [exact HS | rewrite HE; apply env_agree_refl | vm_compute; reflexivity]. }
split; [reflexivity|].
split; [| split; [exact VP | split; [| split; [| lia]]]].
- eapply val_mem_kept; [exact GL|]. intros i Hi. apply AV; unfold G_LIVE, G_PEAK; cbn in Hi; lia.
- eapply val_mem_kept; [exact GC|]. intros i Hi. apply AV; unfold G_COUNT, G_PEAK; cbn in Hi; lia.
- eapply val_mem_kept; [exact GF|]. intros i Hi. apply AV; unfold G_FAIL, G_PEAK; cbn in Hi; lia.
Qed.

End c.
