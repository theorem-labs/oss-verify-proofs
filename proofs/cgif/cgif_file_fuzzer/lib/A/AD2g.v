(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK00 YK0h YK14 YK1b YK15 YK18 YK0p YP0n YK0s YM02 YP0m YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YP0e YN3q YN3v YI04 YL0a YL09 YL02 YL04 YK04 YA0i YA0n YA0o YA0p YA0m YK09 YA0e YG00 YG01 YG0f YG0v YG0n YG0d YCe5.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB12 AF0l AB1h AB13 AF0m AD2j AD2i AD1t AD20 AD1v AD1y AD26 AD24.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AD21 AD25 AD23 AD2h AD1w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO05 YO09 YO06 YO01.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Lemma list_len2 {X} : forall (l : list X), (2 <= length l)%nat -> exists a b r, l = a :: b :: r.
Proof. intros [|a [|b r]] H; cbn in H; try lia. exists a, b, r. reflexivity. Qed.
Lemma S_HDR_hlo : forallb (fun r => match r_base r with None => (0x10000 <=? r_lo r) | _ => true end) (ss_mem S_HDR) = true.
Proof. vm_compute. reflexivity. Qed.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k AD1u.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Section d.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis ARL : AR_laws tfibsegs B.
Hypothesis SHORT : short_leaf_tfa B.
Hypothesis OVERRUN : overrun_leaf_tfa B.
Hypothesis POSTP : post_P_tfa B.
Variables (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (a0 p : list byte).
Hypothesis Hargv : in_argv inp = [a0; p].
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv [a0; p].
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hvfs : valid_fs (in_fs inp).
#[local] Notation EL := (YP08.E0 sp [a0; p] (in_envp inp) xw xd).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation envp := (in_envp inp).
Let HWXi : wx_segs_nowrap tfibsegs := Hwx_tfa.
Lemma EL6 : usp <= bv_unsigned (ew EL 6).
Proof.
change (ew EL 6) with (Z_to_bv 64 (z_rand usp [a0; p] envp)).
pose proof (YP08.z_rand_end sp [a0; p] envp Hsp Hva Hve) as Hz. pose proof (u64_range sp).
unfold z_rand in *. rewrite u64_lit by lia. lia.
Qed.
Lemma short_run : forall E (W : world tfibsegs) ms md,
st_ok tfibsegs E (add_cond S_HDR cond_SH) (restrict (w_H W) ms) ->
SRr tfibsegs W (mkCfg ms md) (at_st S_HDR S_SHORT E W (ms_mem ms) md).
Proof.
intros E W ms md HS. pose proof HWXi as HWX. srr_run_with tfibtbl_lp_ok HS.
apply SRr_ret. split; [reflexivity|].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split; [exact HS|]. split; [exact HF | exact HFr].
Qed.
Lemma h1_run : forall E (W : world tfibsegs) ms md,
st_ok tfibsegs E S_H6 (restrict (w_H W) ms) ->
SRr tfibsegs W (mkCfg ms md) (at_st S_H6 S_H1 E W (ms_mem ms) md).
Proof.
intros E W ms md HS. pose proof HWXi as HWX. srr_run_with tfibtbl_lp_ok HS.
apply SRr_ret. split; [reflexivity|].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split; [exact HS|]. split; [exact HF | exact HFr].
Qed.
Lemma ovr_run : forall E (W : world tfibsegs) ms md,
st_ok tfibsegs E (add_cond S_H1 cond_OV) (restrict (w_H W) ms) ->
SRr tfibsegs W (mkCfg ms md) (at_st S_H6 S_OVR E W (ms_mem ms) md).
Proof.
intros E W ms md HS. pose proof HWXi as HWX. srr_run_with tfibtbl_lp_ok HS.
apply SRr_ret. split; [reflexivity|].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split; [exact HS|]. split; [exact HF | exact HFr].
Qed.
Lemma p_run : forall E (W : world tfibsegs) ms md,
st_ok tfibsegs E (add_cond S_H1 cond_OK) (restrict (w_H W) ms) ->
SRr tfibsegs W (mkCfg ms md) (at_st S_H6 S_P E W (ms_mem ms) md).
Proof.
intros E W ms md HS. pose proof HWXi as HWX. srr_run_with tfibtbl_lp_ok HS.
apply SRr_ret. split; [reflexivity|].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end. eexists. split; [reflexivity|].
split; [exact HS|]. split; [exact HF | exact HFr].
Qed.
Lemma tail_after : forall ss rs E (W : world tfibsegs) ms md ly S (pb : sptr) cap data ms' mat,
forallb drv_win_ok rs = true -> wr_below_sp (ss_facts ss) rs = true ->
(exists c1 c2 rest, ss_mem ss = YP09.mkRegion (Some 0%nat) (-65536) (-128) (-65536) (-128) c1
:: YP09.mkRegion (Some 0%nat) (-128) 0 (-128) 0 c2 :: rest) ->
bv_unsigned (ew E 0) = usp ->
st_ok tfibsegs E ss (restrict (w_H W) ms') ->
frame_of E rs (ms_mem ms) (ms_mem ms') -> frame_of E rs (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
bv_unsigned (ew E A_BUF) = sptr_addr B ly pb -> bv_unsigned (ew E A_LEN) = dlen data ->
runs_at usp (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp [a0; p] envp) ->
AI tfibsegs (w_H W) (w_A W) (with_vm_backing (m_vm_lazy md) mat md) -> AR tfibsegs B ly S W (ms_mem ms) md -> top_ok usp ly ->
blocks S = [(pb, cap)] -> st_nev S <= 64 -> 65536 <= cap <= 2 ^ 26 -> dlen data < cap ->
blk (w_H W) (ms_mem ms) (sptr_addr B ly pb) (dlen data) data ->
m_fs md = in_fs inp -> m_fds md = APSG.fds_std -> drv_minv S cap (dlen data) ->
FINV ly (w_H W) (ms_mem ms) ->
tail_at B ss E sp inp a0 p data W ms' (with_vm_backing (m_vm_lazy md) mat md) ly S pb cap.
Proof.
intros ss rs E W ms md ly S pb cap data ms' mat Hok Hwbs (c1 & c2 & rest & Hm) E0' HS HF HFr E41 E42 HR HAI HAR HTOP Hbl Hnev Hcap HLc HBLK Hfs Hfds Hminv HFI.
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp. pose proof (top_ok_ceil _ _ HTOP) as HCT.
pose proof (YM05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.
assert (Hin : In (sptr_addr B ly pb, cap) (ablocks B ly S)) by (unfold ablocks; rewrite Hbl; left; reflexivity).
pose proof (al_blocks _ _ ARL ly S W (ms_mem ms) md _ _ HAR Hin) as (_ & Hb4096 & Hbce & _).
assert (Hcap' : cap <= req_size cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia). unfold dlen in *.
assert (NIMG : forall a, sptr_addr B ly pb <= a < sptr_addr B ly pb + cap -> ~ in_img tfibsegs a).
{ intros a Ha. assert (Ha' : sptr_addr B ly pb <= a < sptr_addr B ly pb + req_size cap) by lia.
exact (proj2 (al_client_img _ _ ARL ly S W (ms_mem ms) md a HAR (or_introl (ex_intro _ _ (ex_intro _ cap (conj Hin Ha')))))). }
pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as HM. cbn [restrict ms_mem] in HM. rewrite Hm in HM.
assert (Hwin : forall a, usp - 65536 <= a < usp -> apresent (w_H W) (ms_mem ms') a).
{ intros a Ha. destruct (Z.lt_ge_cases a (usp - 128)).
- eapply (win_present sp Hsp E (w_H W) (ms_mem ms')); [exact HM | left; reflexivity | exact E0' | lia | lia | lia].
- eapply (win_present sp Hsp E (w_H W) (ms_mem ms')); [exact HM | right; left; reflexivity | exact E0' | lia | lia | lia]. }
split; [exact HS|]. split; [exact E41|]. split; [exact E42|]. split.
{ eapply (runs_at_frame E (ss_facts ss) rs); [exact (st_ok_facts_ok tfibsegs E ss _ HS) | exact Hwbs | exact HFr | rewrite E0'; lia | exact HR]. }
split; [exact HAI|]. split.
{ apply (AR_after_run B HB ARL ly S W E rs (ms_mem ms) (ms_mem ms') md mat HAR Hok); [rewrite E0'; exact Ulo | rewrite E0'; exact HCT | exact HF |].
rewrite E0'. intros a Ha. exact (apresent_some' _ _ _ (Hwin a Ha)). }
split; [exact HTOP|]. split; [exact Hbl|]. split; [exact Hnev|]. split; [exact Hcap|]. split; [unfold dlen; lia|]. split.
{ unfold dlen. apply (blk_of_frame_r _ _ _ _ _ (sptr_addr B ly pb) (Z.of_nat (length data)) data usp HFr Hok E0' Ulo); [intros a Ha; apply NIMG; lia | lia | lia | exact HBLK]. }
split; [rewrite wvb_fs'; exact Hfs |]. split; [rewrite wvb_fds'; exact Hfds |]. split; [exact Hminv|].
exact (finv_run B ly S W (ms_mem ms) md (w_H W) E rs _ _ usp HAR HFr Hok E0' Ulo Uhi HTOP HFI).
Qed.
Theorem tfib_hdr_at : forall ws (W : world tfibsegs) ms md ly S data (pb : sptr) cap,
fs_lookup (in_fs inp) p = Some data -> dlen data < cap ->
st_ok tfibsegs (havoc EL K_M1 ws) S_HDR (restrict (w_H W) ms) ->
runs_at usp (mrestrict (w_H W) (ms_mem ms)) (runs_main_tfa true sp [a0; p] envp) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly S W (ms_mem ms) md -> top_ok usp ly ->
blocks S = [(pb, cap)] -> sptr_addr B ly pb = bv_unsigned (ew (havoc EL K_M1 ws) A_BUF) ->
bv_unsigned (ew (havoc EL K_M1 ws) A_LEN) = dlen data -> 65536 <= cap <= 2 ^ 26 -> st_nev S <= 64 ->
drv_minv S cap (dlen data) ->
YP03.bytes_at (mrestrict (w_H W) (ms_mem ms)) (sptr_addr B ly pb) data ->
FINV ly (w_H W) (ms_mem ms) ->
m_fs md = in_fs inp -> m_fds md = APSG.fds_std ->
srealizes tfibsegs (mkCfg ms md) (POSTX data (in_fs inp)).
Proof.
intros ws W ms md ly S data pb cap Hlk HLc HS HR HAI HAR HTOP Hbl Hpb H42 Hcap Hnev Hminv Hbytes HFI Hfs Hfds.
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp. pose proof (top_ok_ceil _ _ HTOP) as HCT.
pose proof (YM05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.
set (ER := havoc EL K_M1 ws) in *.
assert (E0' : bv_unsigned (ew ER 0) = usp) by (subst ER; rewrite ew_havoc_old by (unfold K_M1; lia); reflexivity).
assert (Hin : In (sptr_addr B ly pb, cap) (ablocks B ly S)) by (unfold ablocks; rewrite Hbl; left; reflexivity).
pose proof (al_blocks _ _ ARL ly S W (ms_mem ms) md _ _ HAR Hin) as (_ & Hb4096 & Hbce & _ & Hpres0 & _).
assert (NIMG : forall a, sptr_addr B ly pb <= a < sptr_addr B ly pb + cap -> ~ in_img tfibsegs a).
{ intros a Ha. assert (Ha' : sptr_addr B ly pb <= a < sptr_addr B ly pb + req_size cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
exact (proj2 (al_client_img _ _ ARL ly S W (ms_mem ms) md a HAR (or_introl (ex_intro _ _ (ex_intro _ cap (conj Hin Ha')))))). }
assert (Hcap' : cap <= req_size cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
assert (HBLK : blk (w_H W) (ms_mem ms) (sptr_addr B ly pb) (dlen data) data).
{ intros i Hi. unfold dlen in Hi. rewrite <- (Hbytes (Z.to_nat i)) by lia. rewrite Z2Nat.id by lia. reflexivity. }
unfold POSTX, HDR_MIN. unfold dlen in *.
destruct (Z.lt_ge_cases (Z.of_nat (length data)) 6) as [Hsh | Hge].
-
rewrite (proj2 (Z.ltb_lt _ _) Hsh).
assert (HS1 : st_ok tfibsegs ER (add_cond S_HDR cond_SH) (restrict (w_H W) ms)).
{ apply (st_ok_add_cond tfibsegs ER S_HDR _ BC_GEU (SLit 5) (SOff A_LEN 0) HS).
rewrite branch_geu_U, U_SLit, U_SOff, H42, Z.add_0_r, !zcanon_id by (unfold M64; lia). apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
apply (SRr_srealizes tfibsegs W (mkCfg ms md) _ _ (short_run ER W ms md HS1) HAI).
intros W0 c' _ HAI' (-> & ms' & mat & -> & HS' & HF & HFr). cbn [cfg_model] in HAI'.
apply (SHORT sp inp xw xd ws W ms' _ ly S a0 p data pb cap Hargv Hsp Hva Hve Hvfs Hlk ltac:(unfold dlen; lia)).
apply (tail_after S_SHORT (ss_mem S_HDR) ER W ms md ly S pb cap data ms' mat S_HDR_win_ok wbs_SHORT ltac:(do 3 eexists; reflexivity)
E0' HS' HF HFr (eq_sym Hpb) H42 HR HAI' HAR HTOP Hbl Hnev Hcap ltac:(unfold dlen; lia) HBLK Hfs Hfds Hminv HFI).
-
assert (Hltb : (Z.of_nat (length data) <? 6) = false) by (apply Z.ltb_ge; lia). rewrite Hltb.
destruct (list_len2 data ltac:(lia)) as (d0 & d1 & rest & Ed).
pose proof (config_len_bound data) as Hcl.
assert (HS1 : st_ok tfibsegs ER S_H0c (restrict (w_H W) ms)).
{ change S_H0c with (add_cond S_HDR cond_H6).
apply (st_ok_add_cond tfibsegs ER S_HDR _ BC_LTU (SLit 5) (SOff A_LEN 0) HS).
rewrite branch_ltu_U, U_SLit, U_SOff, H42, Z.add_0_r, !zcanon_id by (unfold M64; lia). apply Z.ltb_lt. lia. }
set (E' := edset ER 2 data).
assert (HS2 : st_ok tfibsegs E' S_H0c (restrict (w_H W) ms)) by (apply (st_ok_edset tfibsegs ER 2 data S_H0c _ HS1 S_H0c_data2)).
assert (E'0 : bv_unsigned (ew E' 0) = usp) by exact E0'.
assert (E'41 : bv_unsigned (ew E' A_BUF) = sptr_addr B ly pb) by exact (eq_sym Hpb).
assert (E'42 : bv_unsigned (ew E' A_LEN) = Z.of_nat (length data)) by exact H42.
assert (Hd : ed E' 2 = d0 :: d1 :: rest) by (rewrite <- Ed; reflexivity).
assert (HS3 : st_ok tfibsegs E' S_H6 (restrict (w_H W) ms)).
{ pose proof S_H1_regs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hrv0 & _).
unfold S_H6. rewrite <- Hrv0.
apply (st_ok_app_regions E' S_H0c (restrict (w_H W) ms) [blkreg6] HS2 blkreg6_wf).
- constructor; [| constructor]. cbn [ms_mem restrict].
split; [cbn [base_val r_base r_lo blkreg6]; rewrite E'41; lia|].
split; [cbn [base_val r_base r_hi blkreg6]; rewrite E'41; lia|].
split; [cbn [r_wlo r_whi blkreg6]; intros o Ho; lia|].
constructor; [| constructor]. intros i Hi. cbn in Hi. cbn [c_off c_val c_len cv_len blkreg6 base_val r_base r_chunks]. rewrite E'41.
pose proof (HBLK i ltac:(lia)) as Hb. rewrite Z.add_0_r.
destruct (nth_error data (Z.to_nat i)) as [b|] eqn:En; [| apply nth_error_None in En; lia].
exists b. split; [unfold cbyte; change (ed E' 2) with data; rewrite ?Z.add_0_l; exact En|].
unfold mbyte. rewrite ?Z.add_0_r in Hb. rewrite ?Z.add_0_r. rewrite Hb. reflexivity.
- cbn. exact (conj I I).
- intros r1 r2 Hr1 [<-|[]].
pose proof S_H1_regs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hm0). rewrite Hm0 in Hr1.
pose proof (proj1 (forallb_forall _ _) S_HDR_hext r1 Hr1) as Y. unfold hext_chk in Y.
pose proof (proj1 (forallb_forall _ _) S_HDR_hlo r1 Hr1) as Y2. cbn beta in Y2.
unfold extent_disjoint. cbn [base_val r_base r_lo r_hi blkreg6]. rewrite E'41.
destruct (r_base r1) as [[|[|[|[|[|[|[|n]]]]]]]|]; try discriminate Y; cbn [base_val].
+ apply Z.leb_le in Y. rewrite E'0. unfold sp_window_lo in Ulo. right. lia.
+ apply Z.leb_le in Y. change (ew E' 6) with (ew ER 6). subst ER. rewrite ew_havoc_old by (unfold K_M1; lia). pose proof EL6 as R6.
unfold sp_window_lo in Ulo. right. lia.
+ apply Z.leb_le in Y. apply Z.leb_le in Y2.
destruct (Z.le_gt_cases (r_hi r1) (sptr_addr B ly pb)) as [|Hgt]; [left; lia|].
destruct (Z.le_gt_cases (sptr_addr B ly pb + 6) (r_lo r1)) as [|Hgt2]; [right; lia|].
exfalso. apply (NIMG (Z.max (sptr_addr B ly pb) 0x10000)); [lia|]. apply in_img_hull. lia. }
apply (SRr_srealizes tfibsegs W (mkCfg ms md) _ _ (h1_run E' W ms md HS3) HAI).
intros W0 c' _ HAI' (-> & ms' & mat & -> & HS4 & HF & HFr). cbn [cfg_model] in HAI'.
pose proof (tail_after S_H1 (ss_mem S_H6) E' W ms md ly S pb cap data ms' mat S_H6_win_ok wbs_H1 ltac:(do 3 eexists; reflexivity)
E'0 HS4 HF HFr E'41 E'42 HR HAI' HAR HTOP Hbl Hnev Hcap ltac:(unfold dlen; lia) HBLK Hfs Hfds Hminv HFI)
as (_ & _ & _ & HR4 & _ & HAR4 & _ & _ & _ & _ & _ & HBLK4 & Hfs4 & Hfds4 & _ & HFI4).
set (md4 := with_vm_backing (m_vm_lazy md) mat md) in *.
assert (UC6 : U E' sv_cl6 = config_len data + 6).
{ transitivity (config_len (d0 :: d1 :: rest) + 6); [exact (U_cl6 E' d0 d1 rest Hd) | rewrite <- Ed; reflexivity]. }
assert (U42 : U E' (SOff A_LEN 0) = Z.of_nat (length data)) by (rewrite U_SOff, E'42, Z.add_0_r; apply zcanon_id; unfold M64; lia).
destruct (Z.lt_ge_cases (Z.of_nat (length data)) (6 + config_len data)) as [Hov | Hok].
+
assert (Hovb : (Z.of_nat (length data) <? 6 + config_len data) = true) by (apply Z.ltb_lt; exact Hov). rewrite Hovb.
assert (HS5 : st_ok tfibsegs E' (add_cond S_H1 cond_OV) (restrict (w_H W) ms')).
{ apply (st_ok_add_cond tfibsegs E' S_H1 _ BC_LTU (SOff A_LEN 0) sv_cl6 HS4). rewrite branch_ltu_U, UC6, U42. apply Z.ltb_lt. lia. }
apply (SRr_srealizes tfibsegs W (mkCfg ms' md4) _ _ (ovr_run E' W ms' md4 HS5) HAI').
intros W1 c1 _ HAI5 (-> & ms5 & mat5 & -> & HS6 & HF5 & HFr5). cbn [cfg_model] in HAI5.
apply (OVERRUN sp inp xw xd ws W ms5 _ ly S a0 p data pb cap Hargv Hsp Hva Hve Hvfs Hlk ltac:(unfold dlen; lia)).
apply (tail_after S_OVR (ss_mem S_H6) E' W ms' md4 ly S pb cap data ms5 mat5 S_H6_win_ok wbs_OVR ltac:(do 3 eexists; reflexivity)
E'0 HS6 HF5 HFr5 E'41 E'42 HR4 HAI5 HAR4 HTOP Hbl Hnev Hcap ltac:(unfold dlen; lia) HBLK4 Hfs4 Hfds4 Hminv HFI4).
+
assert (Hokb : (Z.of_nat (length data) <? 6 + config_len data) = false) by (apply Z.ltb_ge; exact Hok). rewrite Hokb.
assert (HS5 : st_ok tfibsegs E' (add_cond S_H1 cond_OK) (restrict (w_H W) ms')).
{ apply (st_ok_add_cond tfibsegs E' S_H1 _ BC_GEU (SOff A_LEN 0) sv_cl6 HS4). rewrite branch_geu_U, UC6, U42. apply Bool.negb_true_iff. apply Z.ltb_ge. lia. }
apply (SRr_srealizes tfibsegs W (mkCfg ms' md4) _ _ (p_run E' W ms' md4 HS5) HAI').
intros W1 c1 _ HAI5 (-> & ms5 & mat5 & -> & HS6 & HF5 & HFr5). cbn [cfg_model] in HAI5.
apply (POSTP sp inp xw xd ws W ms5 _ ly S a0 p data pb cap Hargv Hsp Hva Hve Hvfs Hlk ltac:(unfold dlen; lia)).
apply (tail_after S_P (ss_mem S_H6) E' W ms' md4 ly S pb cap data ms5 mat5 S_H6_win_ok wbs_P ltac:(do 3 eexists; reflexivity)
E'0 HS6 HF5 HFr5 E'41 E'42 HR4 HAI5 HAR4 HTOP Hbl Hnev Hcap ltac:(unfold dlen; lia) HBLK4 Hfs4 Hfds4 Hminv HFI4).
Qed.
End d.
Theorem tfib_hdr (B : asyms) (HB : TfibSyms B) (ARL : AR_laws tfibsegs B)
(SHORT : short_leaf_tfa B) (OVERRUN : overrun_leaf_tfa B) (POSTP : post_P_tfa B) : hdr_tfa B.
Proof.
intros sp inp xw xd ws W ms md ly S a0 p data pb cap Hargv Hsp Hva Hve Hvfs Hlk HLc HS HR HAI HAR HTOP Hbl Hpb H42 Hcap Hnev Hminv Hbytes HFI Hfs Hfds.
exact (tfib_hdr_at B HB ARL SHORT OVERRUN POSTP sp inp xw xd a0 p Hargv Hsp Hva Hve Hvfs ws W ms md ly S data pb cap
Hlk HLc HS HR HAI HAR HTOP Hbl Hpb H42 Hcap Hnev Hminv Hbytes HFI Hfs Hfds).
Qed.
End c.
