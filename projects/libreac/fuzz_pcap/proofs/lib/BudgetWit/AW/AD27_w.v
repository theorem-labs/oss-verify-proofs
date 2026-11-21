(* Modified by Theorem Labs, 2026-11: made from A/AD27.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD27.v, with its module paths changed, names TfibSyms -> PcapSyms and its addresses moved to libreac/fuzz_pcap's ASan build. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3, with libreac/fuzz_boxreg's port of its copy of this file (changed us_run, tfib_usage). *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.libreac.fuzz_pcap.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0d YO0f.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK00 YK0h YK14 YK1b YK15 YK0k.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK0p YP0n YK0s YM02 YP0m YP09 YP02 YP0l YP0k YP06 YP01 YP08 YP03 YP0g YP0e YN3q YN3v YI04 YL0a YL09 YL02 YL04 YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0p_w YA0m_w.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit.AW Require Import YA0e_w.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG01 YG0k YG0f YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit.AW Require Import YG0n_w YG0d_w YCe5_w.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB1v AB12 AF0l.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit.AW Require Import AB1h_w.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB13 AF0m AD2j.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit.AW Require Import AD2i_w AD1t_w AD20_w AD1v_w AD1y_w AD26_w.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit.AW Require Import AD25_w AD2h_w AD1w_w AD2f_w AD1s_w AD29_w AD1x_w AD28_w.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Lemma ret_oks : YK0s.ret_ok (Z_to_bv 64 (symaddr (Symbols.Asan.s_main + 0x290)%Z)) /\ YK0s.ret_ok (Z_to_bv 64 (symaddr Symbols.Asan.s___copy_tls)) /\ YK0s.ret_ok (Z_to_bv 64 (symaddr (Symbols.Asan.s_main + 0x288)%Z)) /\ YK0s.ret_ok (Z_to_bv 64 (symaddr (Symbols.Asan.s_main + 0x264)%Z))
/\ YK0s.ret_ok (Z_to_bv 64 (symaddr (Symbols.Asan.s_main + 0x1f4)%Z)) /\ YK0s.ret_ok (Z_to_bv 64 (symaddr (Symbols.Asan.s_main + 0x1b4)%Z)) /\ YK0s.ret_ok (Z_to_bv 64 RA_JF).
Proof. unfold YK0s.ret_ok. repeat split; apply bv_eq; vm_compute; reflexivity. Qed.
Definition X_a0 : list sv := [SLit 2; SLit 2; SOff 206 0; SLit 2; SLit 2].
Definition X_spo : list Z := [-128; -128; -48; -48; -48].
Definition X_ra : list Z := [(symaddr (Symbols.Asan.s_main + 0x290)%Z); (symaddr (Symbols.Asan.s_main + 0x290)%Z); (symaddr Symbols.Asan.s___copy_tls); (symaddr Symbols.Asan.s___copy_tls); (symaddr Symbols.Asan.s___copy_tls)].
Definition X_mspo : list Z := [-128; -128; -48; -128; -128].
Definition X_wf : list bool := [false; false; false; true; true].
Definition X_img : list smem := [IMG_X; IMG_X; IMG_XL; IMG_X; IMG_X].
Lemma XSTS_row : forall i, (i < 5)%nat ->
sr_get (ss_regs (nth i XSTS S_J7x)) 10%bv = nth i X_a0 (SLit 0) /\ sr_get (ss_regs (nth i XSTS S_J7x)) 2%bv = SOff 0 (nth i X_spo 0) /\
sr_get (ss_regs (nth i XSTS S_J7x)) 1%bv = SLit (nth i X_ra 0) /\ ss_mem (nth i XSTS S_J7x) = jmemI (nth i X_img IMG_X) (nth i X_mspo 0) (nth i X_wf false) /\
YK0s.ret_ok (Z_to_bv 64 (nth i X_ra 0)) /\ (nth i X_spo 0 = -128 \/ nth i X_spo 0 = -48) /\ (nth i X_mspo 0 = -128 \/ nth i X_mspo 0 = -48)
/\ XIok (nth i X_img IMG_X) /\ ((nth i X_img IMG_X = IMG_XL /\ i = 2%nat) \/ (nth i X_img IMG_X = IMG_X /\ i <> 2%nat)).
Proof.
pose proof ret_oks as (K1 & K2 & _).
intros [|[|[|[|[|i]]]]] Hi; [..|cbn in Hi; lia]; cbn [nth X_a0 X_spo X_ra X_mspo X_wf X_img XSTS];
(split; [vm_compute; reflexivity|]); (split; [vm_compute; reflexivity|]); (split; [vm_compute; reflexivity|]); (split; [vm_compute; reflexivity|]);
(split; [assumption|]); (split; [lia|]); (split; [lia|]); (split; [first [left; reflexivity | right; reflexivity] | first [left; split; [reflexivity | lia] | right; split; [reflexivity | lia]]]).
Qed.
Lemma img_sub_US : submem IMG_REGIONS (ss_mem S_US).
Proof.
change (ss_mem S_US) with (firstn 3 (ss_mem S_US) ++ IMG_REGIONS ++ skipn 36 (ss_mem S_US)).
do 3 apply submem_drop. induction IMG_REGIONS as [|r rs IH]; cbn; [apply submem_nil | apply submem_keep; [repeat split; try lia; auto | exact IH]].
Qed.
Lemma US_checks : atom_lookup (f_atoms (ss_facts S_US)) 8%nat = Some (mkAF 1 4194303 0) /\ ss_mem S_US <> [] /\ regions_wf (ss_mem (ss_main false)) = true
/\ atom_lookup (f_atoms (ss_facts (ss_main false))) 8%nat = Some (mkAF 1 4194303 0).
Proof. vm_compute. repeat split; try reflexivity; discriminate. Qed.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit.AW Require Import AD1u_w.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PcapImgEnd YImgTop.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section f.
Variable B : asyms.
Hypothesis HB : PcapSyms B.
Hypothesis ARL : AR_laws tfibsegs B.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Variable est : (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis XFR : xst_frame_tfa xst.
Hypothesis ESTF : est_frame_tfa est.
Hypothesis FPU : fprintf_s_site_tfa B est (symaddr (Symbols.Asan.Sec.s_rodata + 0x553c)%Z) (strB "usage: "%string) (strB " INPUT"%string ++ nlB).
Hypothesis EXS : exit_site_tfa B est xst.
Let HWXi : wx_segs_nowrap tfibsegs := Hwx_tfa.
Lemma est_frame_run : forall H E rs m m',
frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb se_win_ok rs = true -> sp_window_lo <= bv_unsigned (ew E 0) ->
est H m -> est H m'.
Proof.
intros H E rs m m' HF Hok U0 HE. apply (ESTF H H m m' HE). intros a Ha.
apply (aview_kept_run F_STDERR_LO F_STDERR_HI E rs H m m' a HF Hok U0); unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI in *; try unfold pcap_img_end, YImgTop.IMG_TOP; lia.
Qed.
Lemma so_state_run : forall k H E rs m m',
frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb sx_win_ok rs = true -> sp_window_lo <= bv_unsigned (ew E 0) ->
so_state xst k H m -> so_state xst k H m'.
Proof.
intros k H E rs m m' HF Hok U0 HS. apply (so_state_keep xst XFR k H H m m'); [| exact HS]. intros a Ha.
assert (H1 : forallb (win_avoids STDOUT_LO STDOUT_HI) rs = true /\ forallb (win_avoids SOBUF_LO SOBUF_HI) rs = true).
{ split; apply forallb_forall; intros r Hr; pose proof (proj1 (forallb_forall _ _) Hok r Hr) as X; unfold sx_win_ok in X; apply andb_prop in X; tauto. }
destruct Ha as [Ha|Ha].
- apply (aview_kept_run STDOUT_LO STDOUT_HI E rs H m m' a HF (proj1 H1) U0); unfold STDOUT_LO, STDOUT_HI in *; try unfold pcap_img_end, YImgTop.IMG_TOP; lia.
- apply (aview_kept_run SOBUF_LO SOBUF_HI E rs H m m' a HF (proj2 H1) U0); unfold SOBUF_LO, SOBUF_HI in *; try unfold pcap_img_end, YImgTop.IMG_TOP; lia.
Qed.
Lemma img_kept_site : forall E (H : word -> bool) m m' (slo shi : Z),
mem_ok tfibsegs E (mrestrict H m) IMG_X ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> ~ STDERR_MUT a -> aview tfibsegs H m' a = aview tfibsegs H m a) ->
pcap_img_end <= slo ->
mem_ok tfibsegs E (mrestrict H m') IMG_X.
Proof.
intros E H m m' slo shi HM Hfr Hslo.
apply (mem_ok_kept tfibsegs E _ (mrestrict H m') IMG_X HM IMG_X_nocdata).
apply Forall_forall. intros r Hr. unfold region_kept.
pose proof (proj1 (Forall_forall _ _) (proj1 (proj2 HM)) r Hr) as (B1 & B2 & _).
pose proof (proj1 (forallb_forall _ _) IMG_X_keep r Hr) as Hc. unfold drv_keep_ok in Hc.
pose proof (proj1 (forallb_forall _ _) IMG_X_abs r Hr) as Ha. unfold is_abs in Ha.
pose proof (proj1 (forallb_forall _ _) IMG_X_se r Hr) as Hx. unfold se_ext_ok, ext_avoids in Hx. cbn [fst snd] in Hx.
destruct (r_base r) as [bb|]; [discriminate Ha|]. cbn [base_val] in B1, B2 |- *.
apply andb_prop in Hc as [Hc Hw]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2.
split; intros a Hra.
- apply (mbyte_of_aview tfibsegs). apply Hfr; [lia | lia |].
unfold STDERR_MUT. apply orb_prop in Hx as [Hx|Hx]; apply Z.leb_le in Hx; unfold F_STDERR_LO, F_STDERR_HI in *; lia.
- intros _. apply orb_prop in Hw as [Hw|Hw]; [apply Z.leb_le in Hw; lia|].
apply andb_prop in Hw as [Hw1 Hw2]. apply Z.leb_le in Hw1. apply Z.leb_le in Hw2.
unfold writable_at. apply tfib_rw_window. rewrite u64_lit by (unfold pcap_img_end, YImgTop.IMG_TOP in *; lia). lia.
Qed.
Lemma jfr_kept_site : forall E (H : word -> bool) m m' (usp slo shi : Z),
Forall (YP09.chunk_ok tfibsegs E (mrestrict H m) usp) JFR_chunks ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> ~ STDERR_MUT a -> aview tfibsegs H m' a = aview tfibsegs H m a) ->
shi <= usp - 128 -> sp_window_lo <= usp <= sp_window_hi ->
Forall (YP09.chunk_ok tfibsegs E (mrestrict H m') usp) JFR_chunks.
Proof.
intros E H m m' usp slo shi HC Hfr Hshi [Ulo Uhi]. unfold sp_window_lo, sp_window_hi in *.
apply Forall_forall. intros c Hc i Hi. destruct (proj1 (Forall_forall _ _) HC c Hc i Hi) as (b & Hb1 & Hb2). exists b. split; [exact Hb1|].
assert (Hoff : -128 <= YP09.c_off c /\ YP09.c_off c + c_len c <= -48).
{ clear - Hc. cbn in Hc. repeat (destruct Hc as [<-|Hc]; [cbn; lia|]). destruct Hc. }
rewrite <- Hb2. apply (mbyte_of_aview tfibsegs). apply Hfr; [lia | lia |].
unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI. lia.
Qed.
Lemma jfr_of_region : forall E (H : word -> bool) m rs lo hi wlo whi usp,
mem_ok tfibsegs E (mrestrict H m) rs -> In (YP09.mkRegion (Some 0%nat) lo hi wlo whi JFR_chunks) rs -> bv_unsigned (ew E 0) = usp ->
Forall (YP09.chunk_ok tfibsegs E (mrestrict H m) usp) JFR_chunks.
Proof.
intros E H m rs lo hi wlo whi usp (_ & Hok & _) Hin E0. pose proof (proj1 (Forall_forall _ _) Hok _ Hin) as (_ & _ & _ & HC).
cbn [r_chunks r_base base_val] in HC. rewrite E0 in HC. exact HC.
Qed.
Lemma jmemI_present : forall XI spo wf E (H : word -> bool) mem usp,
mem_ok tfibsegs E (mrestrict H mem) (jmemI XI spo wf) -> bv_unsigned (ew E 0) = usp -> sp_window_lo <= usp <= sp_window_hi -> (spo = -128 \/ spo = -48) ->
forall a, usp - 65536 <= a < usp -> apresent H mem a.
Proof.
intros XI spo wf E H mem usp (_ & Hok & _) E0 [Ulo Uhi] Hspo a Ha. unfold sp_window_lo, sp_window_hi in *. pose proof (u64_range (ew E 0)).
assert (X : forall lo hi wlo whi cs, In (YP09.mkRegion (Some 0%nat) lo hi wlo whi cs) (jmemI XI spo wf) -> usp + wlo <= a < usp + whi -> apresent H mem a).
{ intros lo hi wlo whi cs Hin Hr. pose proof (proj1 (Forall_forall _ _) Hok _ Hin) as (_ & _ & Wr & _). cbn [r_base r_wlo r_whi base_val] in Wr. rewrite E0 in Wr.
apply apresent_of_writable; [unfold pcap_img_end, YImgTop.IMG_TOP; lia|]. replace a with (usp + (a - usp)) by lia. apply Wr. lia. }
destruct (Z.lt_ge_cases a (usp + spo)).
- apply (X (-65536) spo (-65536) spo []); [left; reflexivity | lia].
- destruct wf.
+ apply (X (-128) 0 (-128) 0 JFR_chunks); [right; left; reflexivity | destruct Hspo as [-> | ->]; [lia|]].
lia.
+ apply (X spo 0 spo 0 []); [right; left; reflexivity | lia].
Qed.
Lemma ju_run : forall E (W : world tfibsegs) ms md, st_ok tfibsegs E S_JU (restrict (w_H W) ms) ->
SRr tfibsegs W (mkCfg ms md) (at_rs (jmem (-128) true) S_JUx E W (ms_mem ms) md).
Proof. intros E W ms md HS. pose proof HWXi as HWX. rewrite <- (proj1 (proj2 (proj2 (proj2 S_Jx_eq)))). unfold run_x. srr_run_with tbl_x_ok HS.
apply SRr_ret; (split; [reflexivity|]);
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end; eexists; (split; [reflexivity|]); (split; [exact HS|]); split; [exact HF | exact HFr]. Qed.
Lemma run_to_exit : forall (i : nat) ss0 E (W : world tfibsegs) ms md ly S (usp : Z) fs (code : Z) (k : nat) (I0 : smem) spo0 wf0,
(i < 5)%nat ->
SRr tfibsegs W (mkCfg ms md) (at_rs (ss_mem ss0) (nth i XSTS S_J7x) E W (ms_mem ms) md) ->
ss_mem ss0 = jmemI I0 spo0 wf0 -> XIok I0 -> (spo0 = -128 \/ spo0 = -48) -> (i = 2%nat \/ k = 0%nat) ->
bv_unsigned (ew E 0) = usp -> sp_window_lo <= usp <= sp_window_hi -> usp mod 16 = 0 -> 1 <= bv_unsigned (ew E 8) <= 4194303 ->
sv_denot E (nth i X_a0 (SLit 0)) = w64 code -> (code = 0 \/ code = 2) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly S W (ms_mem ms) md -> top_ok usp ly -> st_nev S < EV_MAX ->
est (w_H W) (ms_mem ms) -> so_state xst k (w_H W) (ms_mem ms) ->
((1 <= k)%nat -> fd_lookup (m_fds md) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) ->
(* [fdchan] at LPS 727298f3 asks for the model's channel reader beside the descriptor,
   and only a run that writes a line needs it, so it is guarded as that one is. *)
((1 <= k)%nat -> m_channel_reader md = true) -> m_fs md = fs ->
srealizes tfibsegs (mkCfg ms md) (wr ch_stdout (concat (repeat line0 (k - 1))) (ex code fs)).
Proof.
intros i ss0 E W ms md ly S usp fs code k I0 spo0 wf0 Hi HRUN Hm0 HI0 Hspo0 Hik E0 [Ulo Uhi] U16 Htid Hcode Hc02 HAI HAR HTOP Hnev HE HSO Hfd1 Hcr Hfs.
pose proof (u64_range (ew E 0)) as U0.
set (ssx := nth i XSTS S_J7x) in *.
pose proof (proj1 (Forall_forall _ _) XSTS_facts ssx ltac:(subst ssx; apply nth_In; cbn; lia)) as (Hpc & G3 & G4 & Hrv & _).
pose proof (XSTS_row i Hi) as (Ra0 & Rsp & Rra & Mx & Hret & Hspo & Hmspo & HXI & HXlate). fold ssx in Ra0, Rsp, Rra, Mx.
set (spo := nth i X_spo 0) in *. set (rav := nth i X_ra 0) in *. set (mspo := nth i X_mspo 0) in *. set (wf := nth i X_wf false) in *. set (XI := nth i X_img IMG_X) in *.
pose proof (jmemI_checks I0 spo0 wf0 HI0 Hspo0) as (WOK0 & SEK0 & SXK0 & _). pose proof (jmemI_checks XI mspo wf HXI Hmspo) as (WOK & SEK & SXK & JWF & _).
apply (SRr_srealizes tfibsegs W (mkCfg ms md) _ _ HRUN HAI).
intros W1 c1 _ HAI1 (-> & msX & matX & -> & HSX & HFX & HFrX). cbn [cfg_model] in HAI1. rewrite Hm0 in HFX, HFrX.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E ssx msX HSX Hrv) as Hshape.
pose proof (st_ok_mem_ok tfibsegs E ssx _ HSX) as HMX. cbn [restrict ms_mem] in HMX. rewrite Mx in HMX.
pose proof (jmemI_present XI mspo wf E (w_H W) (ms_mem msX) usp HMX E0 (conj Ulo Uhi) Hmspo) as HwinX.
assert (RG : forall r, getr (ms_regs msX) r = sv_denot E (sr_get (ss_regs ssx) r)) by (intros r; exact (st_ok_restrict_reg tfibsegs (w_H W) E ssx msX r HSX)).
rewrite Hshape, Hpc. change (Z_to_bv 64 A_exit) with (w64 A_exit).
apply (EXS XI E W (ms_regs msX) (ms_mem msX) (with_vm_backing (m_vm_lazy md) matX md) ly S usp (- spo) fs code k).
-
destruct HXlate as [[HL _] | [HX Hne]]; [right; exact HL | left]. split; [exact HX|]. destruct Hik as [Hik | Hk]; [exfalso; exact (Hne Hik) | exact Hk].
- exact E0.
- lia.
- exact U16.
- exact Htid.
- rewrite (RG 10%bv), Ra0. exact Hcode.
- exact Hc02.
- unfold spZ. rewrite (RG 2%bv), Rsp. cbn [sv_denot]. rewrite E0, u64_lit by (unfold sp_window_lo in Ulo; lia). lia.
- lia.
- rewrite (RG 1%bv), Rra. cbn [sv_denot]. exact Hret.
- rewrite (RG 3%bv), G3. reflexivity.
- rewrite (RG 4%bv), G4. reflexivity.
- apply (mem_ok_sub tfibsegs E _ (jmemI XI mspo wf)); [unfold jmemI; do 2 apply submem_drop; apply submem_refl | exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (XI_checks XI HXI))))))) | exact HMX].
- exact HwinX.
- exact HAI1.
- apply (AR_after_run B HB ARL ly S W E (jmemI I0 spo0 wf0) (ms_mem ms) (ms_mem msX) md matX HAR WOK0); [rewrite E0; exact Ulo | rewrite E0; exact (top_ok_ceil _ _ HTOP) | exact HFX |].
rewrite E0. intros a Ha. exact (apresent_some' _ _ _ (HwinX a Ha)).
- exact HTOP.
- exact Hnev.
- exact (est_frame_run (w_H W) E (jmemI I0 spo0 wf0) _ _ HFrX SEK0 ltac:(rewrite E0; exact Ulo) HE).
- exact (so_state_run k (w_H W) E (jmemI I0 spo0 wf0) _ _ HFrX SXK0 ltac:(rewrite E0; exact Ulo) HSO).
- intros Hk. rewrite wvb_fds'. exact (Hfd1 Hk).
- intros Hk. exact (Hcr Hk).
- rewrite wvb_fs'. exact Hfs.
Qed.
Lemma sbm_fs_eq : forall md md', same_but_materialized md md' -> m_fs md' = m_fs md.
Proof. intros md md' Hs. rewrite Hs. apply wvb_fs'. Qed.
Lemma win0_present : forall E (H : word -> bool) mem rs cs usp,
mem_ok tfibsegs E (mrestrict H mem) rs -> hd R_errno rs = YP09.mkRegion (Some 0%nat) (-65536) 0 (-65536) 0 cs -> rs <> [] ->
bv_unsigned (ew E 0) = usp -> sp_window_lo <= usp <= sp_window_hi ->
forall a, usp - 65536 <= a < usp -> apresent H mem a.
Proof.
intros E H mem rs cs usp (_ & Hok & _) Hhd Hne E0 [Ulo Uhi] a Ha. unfold sp_window_lo, sp_window_hi in *. pose proof (u64_range (ew E 0)).
destruct rs as [|r rs]; [congruence|]. cbn [hd] in Hhd. subst r.
pose proof (Forall_inv Hok) as (_ & _ & Wr & _). cbn [r_base r_wlo r_whi base_val] in Wr. rewrite E0 in Wr.
apply apresent_of_writable; [unfold pcap_img_end, YImgTop.IMG_TOP; lia|]. replace a with (usp + (a - usp)) by lia. apply Wr. lia.
Qed.
Lemma us_run : forall (sp brk mbase : word) (inp : ProcInput) (rnd : EntryDraw) xw xd
(W : world tfibsegs) ms md,
valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
(length (in_argv inp) <> 2)%nat ->
st_ok tfibsegs (YP08.E0 sp (ed_top rnd) (kb_rseq (in_kernel inp))
(in_argv inp) (in_envp inp) (in_execfn inp) xw xd) (ss_main false) (restrict (w_H W) ms) ->
SRr tfibsegs W (mkCfg ms md) (at_st (ss_main false) S_US (YP08.E0 sp (ed_top rnd)
(kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp) (in_execfn inp) xw xd) W (ms_mem ms) md).
Proof.
intros sp brk mbase inp rnd xw xd W ms md Hsp Hva Hve Hvl Hlau Hvi Hlen HS. pose proof HWXi as HWX.
srr_run_with tfibtbl_drv_ok HS. rename HF into HF1. rename HFr into HFr1.
srr_branch_with tfibtbl_drv_ok HS.
2:{ exfalso. cbn [Sem.branch_taken sv_denot] in Hc. rewrite Z.add_0_r in Hc.
assert (E3 : bv_unsigned (ew (YP08.E0 sp (ed_top rnd) (kb_rseq (in_kernel inp))
(in_argv inp) (in_envp inp) (in_execfn inp) xw xd) 3) = Z.of_nat (length (in_argv inp)))
by (exact (YP08.ew3 TSEGS TPH inp mbase Asan.M.init_pc sp brk rnd Hsp Hva Hve Hvl Hlau
1 ltac:(lia) xw xd)).
apply Bool.negb_false_iff in Hc. apply (proj1 (Fs.bv_eqb_eq _ _)) in Hc.
apply (f_equal bv_unsigned) in Hc. rewrite Z_to_bv_bv_unsigned, E3, u64_lit in Hc by lia. lia. }
pose proof (proj1 (proj2 (proj2 S_COUS_eq))) as QU. unfold run_x in QU.
srr_run_with tbl_x_ok HS.
apply SRr_ret. split; [reflexivity|].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split; [exact HS|]. split.
- eapply frame_of_trans; [| exact HF1 | exact HF]. vm_compute. reflexivity.
- eapply frame_of_trans; [| exact HFr1 | exact HFr]. vm_compute. reflexivity.
Qed.
Theorem tfib_usage : forall (sp brk mbase : word) (inp : ProcInput) (rnd : EntryDraw)
(xw : nat -> word) (xd : nat -> list byte)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout),
valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
(length (in_argv inp) <> 2)%nat ->
YP0l.st_ok tfibsegs (YP08.E0 sp (ed_top rnd) (kb_rseq (in_kernel inp))
(in_argv inp) (in_envp inp) (in_execfn inp) xw xd) (ss_main false) (restrict (w_H W) ms) ->
runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms))
(runs_main_tfa false sp (ed_top rnd) (in_argv inp) (in_envp inp) (in_execfn inp)) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly init_state W (ms_mem ms) md -> top_ok (bv_unsigned sp) ly ->
m_fs md = in_fs inp -> m_fds md = APSG.fds_std -> m_channel_reader md = true ->
srealizes tfibsegs (mkCfg ms md) (diag (msg_usage (nth 0 (in_argv inp) [])) (in_fs inp)).
Proof.
intros sp brk mbase inp rnd xw xd W ms md ly Hsp Hva Hve Hvl Hlau Hvi Hlen HS HR HAI HAR HTOP Hfs Hfds Hcr.
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp.
set (argv := in_argv inp) in *. set (envp := in_envp inp) in *. set (efn := in_execfn inp) in *.
set (EL := YP08.E0 sp (ed_top rnd) (kb_rseq (in_kernel inp)) argv envp efn xw xd) in *.
set (usp := bv_unsigned sp) in *. set (ztop := bv_unsigned (ed_top rnd)) in *.
(* [z_strs] counts down from [ztop], so the old "[z_strs] unfolds to [usp + head]" step is
   gone; the [usp <= z_strs] half now comes from [YP08.str_bounds] (YP08.v:665-671). *)
assert (SB : usp <= z_strs ztop argv envp efn
/\ z_strs ztop argv envp efn + Z.of_nat (total_arg_bytes_nat argv) + Z.of_nat (total_arg_bytes_nat envp)
+ Z.of_nat (length efn) + 1 + 8 = ztop)
by (exact (YP08.str_bounds TSEGS TPH inp mbase Asan.M.init_pc sp brk rnd Hsp Hva Hve Hvl Hlau)).
assert (Htl : ztop <= kHighMemEnd).
{ pose proof (YP08.top_le TSEGS TPH inp mbase Asan.M.init_pc sp brk rnd Hsp Hva Hve Hvl Hlau) as H.
unfold SP_HI, kHighMemEnd in *. lia. }
assert (EL0 : bv_unsigned (ew EL 0) = usp) by reflexivity.
assert (Hargc : (1 <= length argv)%nat) by (pose proof (proj1 Hva); lia).
pose proof US_checks as (TIDf & NEus & WF0 & TID0).
pose proof (tid_of_st_ok EL (ss_main false) _ HS TID0) as Htid.
apply (SRr_srealizes tfibsegs W _ _ _
(us_run sp brk mbase inp rnd xw xd W ms md Hsp Hva Hve Hvl Hlau Hvi Hlen HS) HAI).
intros Wb cb _ HAIb (-> & ms2 & mat2 & -> & HS2 & HFb & HFrb). cbn [cfg_model] in HAIb.
pose proof S_US_facts as (Ppc & Pra & Psp & Pa0 & Pa1 & Pa2 & Pgp & Ptp & Ps0 & Prv & _).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) EL S_US ms2 HS2 Prv) as Hshape. rewrite Hshape, Ppc.
change (mkCfg (mkst (ms_regs ms2) (Z_to_bv 64 (symaddr Symbols.Asan.s___wrap_fprintf)) (ms_mem ms2) (seg_rom tfibsegs)) _) with (cfg_at tfibsegs A_icpt_fprintf (ms_regs ms2) (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md)).
pose proof (st_ok_mem_ok tfibsegs EL S_US _ HS2) as HM2. cbn [restrict ms_mem] in HM2.
assert (RG : forall r, getr (ms_regs ms2) r = sv_denot EL (sr_get (ss_regs S_US) r)) by (intros r; exact (st_ok_restrict_reg tfibsegs (w_H W) EL S_US ms2 r HS2)).
set (regs := ms_regs ms2) in *. set (mem := ms_mem ms2) in *.
assert (HR2 : runs_at usp (mrestrict (w_H W) mem) (runs_main_tfa false sp (ed_top rnd) argv envp efn)).
{ pose proof S_CO_ext as (_ & _ & _ & _ & WBu & WBp & _).
eapply (runs_at_frame EL (ss_facts S_US) (ss_mem (ss_main false))); [exact (st_ok_facts_ok tfibsegs EL S_US _ HS2) | | exact HFrb | rewrite EL0; lia | exact HR].
vm_compute. reflexivity. }
pose proof (runs_at_nth _ _ _ 1 _ _ HR2 eq_refl) as HBr. cbn [nth] in HBr.
pose proof S_US_mem as (Hhd & _ & _).
pose proof (win0_present EL (w_H W) mem (ss_mem S_US) JFR_chunks usp HM2 Hhd NEus EL0 (conj Ulo Uhi)) as Hwin2.
pose proof (jfr_of_region EL (w_H W) mem (ss_mem S_US) (-65536) 0 (-65536) 0 usp HM2 ltac:(rewrite <- Hhd; destruct (ss_mem S_US); [exact (NEus eq_refl) | left; reflexivity]) EL0) as HJ2.
pose proof (mem_ok_sub tfibsegs EL _ _ IMG_REGIONS img_sub_US img_regions_wf HM2) as HMR. pose proof (imgs_of_R EL (w_H W) mem HMR) as [HSO HSE].
assert (HAR2 : AR tfibsegs B ly init_state W mem (with_vm_backing (m_vm_lazy md) mat2 md)).
{ apply (AR_after_run B HB ARL ly init_state W EL (ss_mem (ss_main false)) (ms_mem ms) mem md mat2 HAR (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 S_CO_ext))))))); [rewrite EL0; exact Ulo | rewrite EL0; exact (top_ok_ceil _ _ HTOP) | exact HFb |].
rewrite EL0. intros a Ha. exact (apresent_some' _ _ _ (Hwin2 a Ha)). }
assert (Hsp2 : spZ regs = usp - 128) by (unfold spZ; rewrite (RG 2%bv), Psp; cbn [sv_denot]; rewrite EL0; apply u64_lit; unfold sp_window_lo in Ulo; lia).
assert (Hra : raZ regs = (symaddr (Symbols.Asan.s_main + 0x1b4)%Z)) by (unfold raZ; rewrite (RG 1%bv), Pra; reflexivity).
assert (E1z : bv_unsigned (ew EL 1) = z_argv ztop argv envp efn 0).
{ assert (H1 : bv_unsigned (ew EL 1) = z_strs ztop argv envp efn)
by (subst EL; exact (YP08.ew1 TSEGS TPH inp mbase Asan.M.init_pc sp brk rnd Hsp Hva Hve Hvl Hlau
1 ltac:(lia) xw xd)).
rewrite H1. unfold z_argv. rewrite firstn_O. cbn [total_arg_bytes_nat fold_right]. lia. }
unfold diag, msg_usage.
apply (FPU ly init_state W regs mem _ EL (z_argv ztop argv envp efn 0) (nth 0 argv []) (ex 2 (in_fs inp))).
- split; [exact HAR2|]. split; [rewrite (RG 1%bv), Pra; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 ret_oks))))))|]. split; [rewrite Hra; lia|].
split; [rewrite Hsp2, <- Zminus_mod_idemp_l, U16; reflexivity|]. split; [rewrite Hsp2; unfold sp_window_lo, sp_window_hi in *; lia|].
split; [rewrite Hsp2; unfold top_ok in HTOP; lia|]. split; [unfold top_ok in HTOP; tauto|]. split; [unfold top_ok in HTOP; tauto|].
split; [rewrite Hsp2; intros a Ha; apply Hwin2; unfold DIAG_STK in Ha; lia|].
rewrite (ts_gp B HB), (ts_tp B HB), (RG 3%bv), (RG 4%bv), Pgp, Ptp. split; reflexivity.
- rewrite (RG 10%bv), Pa0. reflexivity.
- rewrite (RG 11%bv), Pa1. reflexivity.
- rewrite (RG 12%bv), Pa2. cbn [sv_denot]. rewrite Z.add_0_r, E1z. reflexivity.
- eapply (YP08.argv_str_len TSEGS TPH inp mbase Asan.M.init_pc sp brk rnd Hsp Hva Hve Hvl Hlau); exact Hargc.
- eapply (YP08.argv_no_nul TSEGS TPH inp mbase Asan.M.init_pc sp brk rnd Hsp Hva Hve Hvl Hlau); exact Hargc.
- rewrite Hsp2.
(* TOP-anchored: [usp <= z_strs] is [SB], and [z_strs <= z_argv _ 0] is conjunct 1 of
   [YP08.z_argv_bounds]; the old "[unfold z_strs] gives [usp + head]" step no longer holds. *)
assert (ZB : z_strs ztop argv envp efn <= z_argv ztop argv envp efn 0
/\ z_argv ztop argv envp efn 0 + Z.of_nat (length (nth 0 argv [])) + 1
<= z_strs ztop argv envp efn + Z.of_nat (total_arg_bytes_nat argv))
by (eapply (YP08.z_argv_bounds TSEGS TPH inp mbase Asan.M.init_pc sp brk rnd Hsp Hva Hve Hvl Hlau); exact Hargc).
subst usp. lia.
- exact (argv_str_fits' (ed_top rnd) argv envp efn 0 Htl ltac:(lia)).
- exact HBr.
- subst usp. exact (argv_over_read sp argv envp false _ 0 ltac:(lia) HR2).
- exact HMR.
- rewrite wvb_fds', Hfds. reflexivity.
- exact Hcr.
- exact HAIb.
-
intros regs' mem' md' HAR' HP Hsbm Ha0 HE' Hfr Hpres HAI'. unfold cfg_at. rewrite Hra.
assert (P2 : getr regs' 2%bv = getr regs 2%bv) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs' 3%bv = getr regs 3%bv) by exact (HP 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs' 4%bv = getr regs 4%bv) by exact (HP 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs' 8%bv = getr regs 8%bv) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
assert (Hwin' : forall a, usp - 65536 <= a < usp -> apresent (w_H W) mem' a).
{ intros a Ha. pose proof (Hwin2 a Ha) as Pa. unfold sp_window_lo, sp_window_hi in Ulo, Uhi. apply Hpres; [lia | unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI; lia | exact Pa]. }
assert (HMX : mem_ok tfibsegs EL (mrestrict (w_H W) mem') IMG_X).
{ apply (img_kept_site EL (w_H W) mem mem' (spZ regs - DIAG_STK) (spZ regs) (mem_ok_X_of_R EL _ HMR) Hfr). rewrite Hsp2. unfold DIAG_STK, sp_window_lo, pcap_img_end, YImgTop.IMG_TOP in *. lia. }
assert (HJ' : Forall (YP09.chunk_ok tfibsegs EL (mrestrict (w_H W) mem') usp) JFR_chunks).
{ apply (jfr_kept_site EL (w_H W) mem mem' usp (spZ regs - DIAG_STK) (spZ regs) HJ2 Hfr); [rewrite Hsp2; lia | exact (conj Ulo Uhi)]. }
pose proof (regs_ok_J EL regs' (-128) usp EL0 ltac:(unfold spZ; rewrite P2; fold (spZ regs); rewrite Hsp2; lia) Ulo ltac:(lia)
ltac:(rewrite P3, (RG 3%bv), Pgp; reflexivity) ltac:(rewrite P4, (RG 4%bv), Ptp; reflexivity)) as HRJ.
pose proof (regs_ok_ovr (E_J EL regs') (jregs (-128)) regs' 8%bv (SLit 2) HRJ eq_refl ltac:(rewrite P8, (RG 8%bv), Ps0; reflexivity)) as HRJ'.
pose proof (st_ok_J IMG_X EL regs' _ (-128) (symaddr (Symbols.Asan.s_main + 0x1b4)%Z) usp true (w_H W) mem' (or_introl eq_refl) HRJ' EL0 Ulo ltac:(left; reflexivity) HMX Hwin' ltac:(intros _; exact HJ')) as HSJ.
rewrite <- (proj1 (proj2 (proj2 (proj2 S_J_defs)))), <- restrict_mkst_fx in HSJ.
set (E2 := E_J EL regs') in *.
assert (E2_0 : bv_unsigned (ew E2 0) = usp) by (subst E2; rewrite E_J_old by (unfold KJ; lia); exact EL0).
apply (srz_conseq tfibsegs _ (wr ch_stdout (concat (repeat line0 (0 - 1))) (ex 2 (in_fs inp)))).
2:{ cbn [Nat.sub repeat concat]. unfold wr. cbn [map]. apply t_emit_nil_eq. unfold ex, t_exit. apply t_emit_has_nil. }
pose proof S_JFc_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MU & _).
apply (run_to_exit 3%nat S_JU E2 W _ md' ly init_state usp (in_fs inp) 2 0%nat IMG_X (-128) true ltac:(lia)); [| | left; reflexivity | | right; reflexivity | ..].
+ cbn [nth XSTS]. rewrite MU. exact (ju_run E2 W _ md' HSJ).
+ exact MU.
+ left. reflexivity.
+ exact E2_0.
+ exact (conj Ulo Uhi).
+ exact U16.
+ subst E2. rewrite E_J_old by (unfold KJ; lia). exact Htid.
+ reflexivity.
+ right. reflexivity.
+ exact HAI'.
+ exact HAR'.
+ exact HTOP.
+ cbn. unfold EV_MAX. lia.
+ exact HE'.
+ left. split; [reflexivity|]. cbn [ms_mem mkst]. intros a Ha.
rewrite (Hfr a); [exact (HSO a Ha) | unfold STDOUT_LO, STDOUT_HI in Ha; lia | rewrite Hsp2; unfold STDOUT_LO, STDOUT_HI, DIAG_STK, sp_window_lo in *; lia
| unfold STDERR_MUT, F_STDERR_LO, F_STDERR_HI, STDOUT_LO, STDOUT_HI in *; lia].
+ intros Hk. exfalso. lia.
+ intros Hk. exfalso. lia.
+ rewrite (sbm_fs_eq _ md' Hsbm), wvb_fs'. exact Hfs.
Qed.
End f.
End d.
