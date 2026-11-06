(* check_round_trip's exit after the split loop (fuzz_manifest.c:290, 0x810ac): a0 := t, the epilogue (13 registers back
   from their slots, sp back up), and the tail call `j free` (0x810e8) with ra = the caller's return address: free (t)
   returns straight to the caller. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d YC20.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI16 YK06 YM05 YC85 YCbp.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AF0l ACej FMPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_kit FMW_K FMW_kitS FMW_seg FMW_crt0 FMW_crtB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the split points from k on make at most one reader call each: rt_used counts at most the positions k .. |u| - 1 *)
Lemma rt_used_le : forall u fuel k, (rt_used u k fuel <= length u - k)%nat.
Proof.
intros u fuel. induction fuel as [|f IH]; intros k; cbn [rt_used]; [lia|].
destruct ((k <? length u)%nat && negb (ManifestModel.byte_at u (k - 1) =? 62)) eqn:Ec; [|lia].
apply andb_prop in Ec as [Ec _]. apply Nat.ltb_lt in Ec. specialize (IH (S k)).
destruct (ManifestModel.plain_name (skipn k u)); lia.
Qed.
(* reader calls check_round_trip makes for a URI of at most 255 bytes *)
Lemma rt_calls_le : forall u, (length u <= 255)%nat -> rt_calls u <= 3 + 4 * 254.
Proof.
intros [|c u] H; cbn [rt_calls]; [lia|]. unfold rt_nk.
pose proof (rt_used_le (c :: u) (length (c :: u)) 1). cbn [length] in *. lia.
Qed.
(* blocks with disjoint extents are distinct *)
Lemma crt_nodup_pw : forall l : list (Z * Z), Forall (fun b => 0 < req_size (snd b)) l ->
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l) -> List.NoDup l.
Proof.
induction l as [|x t IH]; intros HF HP; constructor.
- intros Hin. cbn [map pairwise] in HP. destruct HP as [F _].
  pose proof (proj1 (Forall_forall _ _) F _ (in_map (fun b => (fst b, req_size (snd b))) t x Hin)) as Hd.
  apply Forall_inv in HF. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- apply Forall_inv_tail in HF. cbn [map pairwise] in HP. exact (IH HF (proj2 HP)).
Qed.

Section X. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis FB : FmB B.
Hypothesis UNIV : fm_univ B.
Hypothesis AFREE : afree04_rule tfibsegs B ameter_triv.

Lemma crt_segX : forall cx ly' S' W' regs' mem' md' k0 t,
  crt_base B cx -> crt_X B cx ly' S' W' regs' mem' md' k0 t ->
  SRr tfibsegs W' (cfg_at tfibsegs CRT_X regs' mem' md') (crt_post B cx).
Proof.
intros cx ly' S' W' regs' mem' md' k0 t HB HX.
destruct HX as (HC & Hk & Hn1 & H9 & H18 & Ht & Hperm & HGl).
pose proof (crt_epi_st B cx ly' S' W' regs' mem' md' k0 CRT_X HB HC) as HS.
pose proof HB as (HPRE & HCTX & H10 & Hu & Hku & Hlu & HG & HQ & Hlive & Hev & Hbb).
destruct HPRE as [HAP HRO].
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
destruct HC as (HJ & HFR & Hsp & H3 & H4 & H8 & H26 & Hu' & Hku' & HRO').
unfold crt_J, cx_sp0, CRT_FRAME in *.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof (fmw_sp B _ _ _ _ _ _ _ _ HAP) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
assert (FS : STK_check_round_trip = 16784) by reflexivity.
assert (FE : EV_check_round_trip = 2040) by reflexivity.
pose proof (rt_calls_le _ Hlu) as Hrc.
assert (E2s : bv_unsigned (ew (fmw_env regs' (crt_vals cx)) 2) = spZ (cx_regs cx) - 112).
{ rewrite (fmw_env_reg regs' _ 2 2%bv eq_refl). change (bv_unsigned (getr regs' 2)) with (spZ regs'). exact Hsp. }
assert (E2 : bv_unsigned (ew (fmw_env regs' (crt_vals cx)) 2) = spZ (cx_regs cx) + -112) by lia.
(* CTX_check_round_trip: the caller's ra is 0x80ab8 and the frame chain is empty *)
unfold CTX_check_round_trip in HCTX. destruct HCTX as [HCTX|[]]. injection HCTX as Hra0 Hsp0.
assert (Ech : cx_ch cx = []).
{ destruct (cx_ch cx) as [|x l] eqn:Ec; [reflexivity|]. try rewrite Ec in Hsp0. cbn in Hsp0. discriminate Hsp0. }
rewrite Ech in Hch.
(* 0x810ac .. 0x810e8: a0 := t, the epilogue, j free *)
unfold cfg_at. change (w64 CRT_X) with (Z_to_bv 64 CRT_X).
aj_run_to fmw_tbl_crt_ok HS HJ 0x52db8.
{ unfold crt_epi_ss; cbn [ss_mem].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -112);
    [reflexivity | exact E2 | cbn [fmw_frame_region YP09.r_wlo YP09.r_whi]; unfold CRT_FRAME; lia
    | cbn [fmw_frame_region YP09.r_wlo YP09.r_whi]; unfold CRT_FRAME; lia | apply awr_ok_nil]. }
lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
pose proof (crt_reg_slot _ regs' cx _ ms1 1%bv 1%bv 0 HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as R1.
pose proof (crt_reg_slot _ regs' cx _ ms1 8%bv 8%bv 1 HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as R8.
pose proof (fmw_reg_off _ _ _ ms1 2%bv 2 112 (spZ (cx_regs cx) - 112) HS ltac:(vm_compute; reflexivity) E2s ltac:(lia)) as R2.
pose proof (fmw_reg_atom _ regs' _ _ ms1 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl) as R3.
pose proof (fmw_reg_atom _ regs' _ _ ms1 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl) as R4.
pose proof (fmw_reg_atom _ regs' _ _ ms1 10%bv 18%bv 18 HS ltac:(vm_compute; reflexivity) eq_refl) as R10.
assert (Hsp1 : spZ (ms_regs ms1) = spZ (cx_regs cx)) by (unfold spZ at 1; rewrite R2; lia).
assert (SB : same_below mem' (ms_mem ms1) alloc_ceiling).
{ unfold crt_epi_ss in HF; cbn [ss_mem] in HF.
  apply (same_below_frame1 _ _ mem' (ms_mem ms1) alloc_ceiling HF); [|lia].
  cbn [fmw_frame_region YP09.r_base YP09.r_wlo base_val]. rewrite E2. lia. }
pose proof HJ as (HAR1 & Hly1 & _ & _ & _ & _ & Hnev & _ & F1 & _).
(* t's block is live now and was not at the entry *)
assert (Hin : In (t, crt_tsz (cx_n cx)) (ablocks B ly' S'))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
assert (Hnot : ~ In (t, crt_tsz (cx_n cx)) (ablocks B (cx_ly cx) (cx_S cx))).
{ assert (ND : List.NoDup (ablocks B ly' S')).
  { apply crt_nodup_pw.
    - apply Forall_forall. intros [p m] Hpm.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HAR1 Hpm) as (_ & _ & _ & _ & _ & _ & Hm).
      cbn [snd]. unfold req_size. destruct (Z.eqb_spec m 0); lia.
    - destruct (al_sep _ _ LAWS _ _ _ _ _ HAR1) as [Hp _]. apply pairwise_app_l in Hp as [Hp _]. exact Hp. }
  pose proof (Permutation.Permutation_NoDup Hperm ND) as ND2. apply List.NoDup_cons_iff in ND2 as [ND2 _]. exact ND2. }
(* the entry frame chain, read through the journal (memory at and above sp0 is the entry's) *)
assert (Hchain : chain_pre ly' (aview tfibsegs (w_H W') (ms_mem ms1)) (ms_regs ms1) []).
{ apply (achain_chain_pre ly' _ (spZ (cx_regs cx)) (s0Z (cx_regs cx)) [] (ms_regs ms1)).
  - destruct Hly1 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
    apply (achain_ly_top (cx_ly cx) ly' _ _ _ _ Etop).
    pose proof Hstk as (_ & _ & _ & _ & _ & Hs6 & _ & Hs8 & Hs9).
    apply (achain_kept (cx_ly cx) (aview tfibsegs (w_H (cx_W cx)) (cx_mem cx)) _ _ _ [] (spZ (cx_regs cx)) Hch);
      [lia | lia |].
    intros a Ha. apply F1; lia.
  - rewrite Hsp1. lia.
  - unfold s0Z. rewrite R8. reflexivity.
  - unfold raZ. rewrite R1. exact Hra4. }
assert (HU : In (call_trace0 (pc_free_ra0 (as_code B)) (ms_regs ms1) []) (as_universe B)).
{ apply UNIV. rewrite call_trace_nil, (fb_code B FB).
  assert (RA : raZ (ms_regs ms1) = 0x80ab8) by (unfold raZ; rewrite R1; exact (eq_sym Hra0)).
  rewrite RA. apply memZL_In. vm_compute. reflexivity. }
(* free (t): returns to the caller *)
rewrite (st_ok_restrict_mkst tfibsegs (w_H W') _ _ ms1 HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 0x52db8) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite (fb_code B FB); reflexivity).
eapply SRr_mono.
{ apply (afree04_sub tfibsegs B LAWS HSL ameter_triv AFREE W' (ms_regs ms1) (ms_mem ms1) STK_check_round_trip
    (spZ (cx_regs cx)) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx) [] ly' S' _ k0 t
    (crt_tsz (cx_n cx)) 0 (getr (cx_regs cx) 1) []).
  - exact HJ.
  - exact Hin.
  - rewrite R10. exact H18.
  - rewrite Hsp1. lia.
  - reflexivity.
  - lia.
  - unfold ASTACK. lia.
  - rewrite R3, H3. exact Hgp.
  - rewrite R4, H4. exact Htp.
  - exact R1.
  - exact Hra.
  - lia.
  - exact Hchain.
  - exact HU.
  - intros Hx. exfalso. exact (Hnot Hx).
  - exact I. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & Hl1 & Hl2) & _ & HK & _ & _).
unfold crt_post, fpost, apost_base.
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|].
split.
{ eapply (ajournal_mono_k tfibsegs B); [exact HJ2 | lia]. }
split.
{ apply (aregs_preserved_trans _ (ms_regs ms1)); [|exact HP2].
  apply (fmw_preserved _ _ _ ms1 (cx_regs cx) crt_expect HS); [vm_compute; reflexivity|].
  crt_cs_cases cx regs' E2s H3 H4. }
split.
{ rewrite Hl2. apply (Permutation_cons_inv (a := (t, crt_tsz (cx_n cx)))).
  eapply Permutation_trans; [apply Permutation_middle|]. rewrite <- Hl1. exact Hperm. }
destruct HK as (_ & _ & KK3 & _).
apply (crt_glob_img W' W2 (ms_mem ms1) mem2).
{ intros a Ha. destruct (fb_pstat B FB a Ha) as [N1 N2]. exact (KK3 a (pstat_img a Ha) N1 N2). }
apply (fm_glob_below W' mem' (ms_mem ms1) _ _ _ _ SB).
unfold crt_glob in HGl.
assert (Hrc0 : (rt_calls (cx_ub cx) =? 0) = false).
{ unfold cx_n in Hn1. destruct (cx_ub cx) as [|c ub']; [cbn in Hn1; lia|]. cbn [rt_calls]. apply Z.eqb_neq. lia. }
rewrite Hrc0 in HGl. exact HGl.
Qed.
End X.
