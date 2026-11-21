(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AD2g.v (donor image sha256 7093581aab04), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from A/AD2g.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut for the usage path at 16 GiB: the pruning removed declarations that this path does not use; some unused declarations can remain. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (changed POSTP, Hva, Hvfs, EL, HWXi, EL6 and 3 more; added Hvl, Hlau, Hvi); the channel reader that fdchan asks for at LPS 727298f3 carried beside the descriptor fact, from cs_ok's co_rdr. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.libreac.fuzz_identity.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0d YO0f.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK00 YK0h YK14 YK1b YK15.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK0p YP0n YK0s YM02 YP0m YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YP0e YN3q YN3v YI04 YL0a YL09 YL02 YL04 YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0p_w YA0m_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0e_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG01 YG0f YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG0n_w YG0d_w YCe5_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1v AB12 AF0l.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AB1h_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB13 AF0m AD2j.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AD2i_w AD1t_w AD20_w AD1v_w AD1y_w AD26_w AD24_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AD21_w AD25_w AD23_w AD2h_w AD1w_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO05 YO09 YO06 YO01.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AE2k_w AD1u_w.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Section d.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis ARL : AR_laws tfibsegs B.
Hypothesis SHORT : short_leaf_tfa B.
Hypothesis OVERRUN : overrun_leaf_tfa B.
Hypothesis POSTP : post_P_tfa B.
Variables (sp brk mbase : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (a0 p : list byte) (rnd : EntryDraw).
(* Shape copied from the in-tree ported donor AD1v_w.v:121-127 / YL0q.v Section b: binders
   [sp brk mbase] .. [inp] .. [a0 p] .. [rnd], premises
   [valid_sp; in_argv =; valid_argv (in_argv inp); valid_envp; valid_launch;
    entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp; valid_input].
   [entry_stack_fits] is DROPPED: implied by [entry_launch_ok_va]
   ([entry_launch_ok_va_fits], 75d69e00 Run.v:3718-3722); this section never carried it. *)
Hypothesis Hargv : in_argv inp = [a0; p].
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp.
Hypothesis Hvi : valid_input inp.
Hypothesis Hvfs : valid_fs (in_fs inp).
(* [YP08.E0] is TOP-anchored and launch-indexed at 75d69e00 (YP08.v:209-210). *)
#[local] Notation EL := (YP08.E0 sp (ed_top rnd) (kb_rseq (in_kernel inp)) [a0; p] (in_envp inp) (in_execfn inp) xw xd).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation envp := (in_envp inp).
Let HWXi : wx_segs_nowrap tfibsegs := Hwx_tfa.
(* Pin the whole entry-layout section, including the image fields absent from the bound. *)
Lemma EL6 : usp <= bv_unsigned (ew EL 6).
Proof.
change (ew EL 6) with (Z_to_bv 64 (z_rand usp (kb_rseq (in_kernel inp)) [a0; p] envp)).
assert (Hz : z_rand usp (kb_rseq (in_kernel inp)) (in_argv inp) envp + 16 < 2 ^ 63)
by exact (YP08.z_rand_end TSEGS TPH inp mbase Asan.M.init_pc sp brk rnd Hsp Hva Hve Hvl Hlau).
rewrite Hargv in Hz. pose proof (u64_range sp).
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
Lemma tail_after : forall ss rs E (W : world tfibsegs) ms md ly S (pb : sptr) cap data ms' mat,
forallb drv_win_ok rs = true -> wr_below_sp (ss_facts ss) rs = true ->
(exists c1 c2 rest, ss_mem ss = YP09.mkRegion (Some 0%nat) (-65536) (-128) (-65536) (-128) c1
:: YP09.mkRegion (Some 0%nat) (-128) 0 (-128) 0 c2 :: rest) ->
bv_unsigned (ew E 0) = usp ->
st_ok tfibsegs E ss (restrict (w_H W) ms') ->
frame_of E rs (ms_mem ms) (ms_mem ms') -> frame_of E rs (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
bv_unsigned (ew E A_BUF) = sptr_addr B ly pb -> bv_unsigned (ew E A_LEN) = dlen data ->
(* [tail_at]'s [runs_at] conjunct is EXISTENTIAL at 75d69e00 (AD1w_w.v:69-70) and
   [runs_main_tfa] is SIX-argument.  [tail_after] only re-frames that conjunct, so it takes
   and returns it in the existential form; the one caller that holds the PLAIN fact
   ([tfib_hdr_at], whose premise comes from [hdr_tfa]) packs it once, below. *)
(exists rnd0 : EntryDraw, runs_at usp (mrestrict (w_H W) (ms_mem ms))
(runs_main_tfa true sp (ed_top rnd0) [a0; p] envp (in_execfn inp))) ->
AI tfibsegs (w_H W) (w_A W) (with_vm_backing (m_vm_lazy md) mat md) -> AR tfibsegs B ly S W (ms_mem ms) md -> top_ok usp ly ->
blocks S = [(pb, cap)] -> st_nev S <= 64 -> 65536 <= cap <= 2 ^ 26 -> dlen data < cap ->
blk (w_H W) (ms_mem ms) (sptr_addr B ly pb) (dlen data) data ->
m_fs md = in_fs inp -> m_fds md = APSG.fds_std -> m_channel_reader md = true -> drv_minv S cap (dlen data) ->
FINV ly (w_H W) (ms_mem ms) ->
tail_at B ss E sp inp a0 p data W ms' (with_vm_backing (m_vm_lazy md) mat md) ly S pb cap.
Proof.
intros ss rs E W ms md ly S pb cap data ms' mat Hok Hwbs (c1 & c2 & rest & Hm) E0' HS HF HFr E41 E42 HR HAI HAR HTOP Hbl Hnev Hcap HLc HBLK Hfs Hfds Hcr Hminv HFI.
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
{ destruct HR as (rnd0 & HR0). exists rnd0.
eapply (runs_at_frame E (ss_facts ss) rs); [exact (st_ok_facts_ok tfibsegs E ss _ HS) | exact Hwbs | exact HFr | rewrite E0'; lia | exact HR0]. }
split; [exact HAI|]. split.
{ apply (AR_after_run B HB ARL ly S W E rs (ms_mem ms) (ms_mem ms') md mat HAR Hok); [rewrite E0'; exact Ulo | rewrite E0'; exact HCT | exact HF |].
rewrite E0'. intros a Ha. exact (apresent_some' _ _ _ (Hwin a Ha)). }
split; [exact HTOP|]. split; [exact Hbl|]. split; [exact Hnev|]. split; [exact Hcap|]. split; [unfold dlen; lia|]. split.
{ unfold dlen. apply (blk_of_frame_r _ _ _ _ _ (sptr_addr B ly pb) (Z.of_nat (length data)) data usp HFr Hok E0' Ulo); [intros a Ha; apply NIMG; lia | lia | lia | exact HBLK]. }
split; [rewrite wvb_fs'; exact Hfs |]. split; [rewrite wvb_fds'; exact Hfds |]. split; [exact Hminv|].
(* [tail_at]'s last conjunct, the channel reader [fdchan] asks for at LPS 727298f3. *)
split; [exact (finv_run B ly S W (ms_mem ms) md (w_H W) E rs _ _ usp HAR HFr Hok E0' Ulo Uhi HTOP HFI) | exact Hcr].
Qed.
Theorem tfib_hdr_at : forall ws (W : world tfibsegs) ms md ly S data (pb : sptr) cap,
fs_lookup (in_fs inp) p = Some data -> dlen data < cap ->
st_ok tfibsegs (havoc EL K_M1 ws) S_HDR (restrict (w_H W) ms) ->
runs_at usp (mrestrict (w_H W) (ms_mem ms))
(runs_main_tfa true sp (ed_top rnd) [a0; p] envp (in_execfn inp)) ->
AI tfibsegs (w_H W) (w_A W) md -> AR tfibsegs B ly S W (ms_mem ms) md -> top_ok usp ly ->
blocks S = [(pb, cap)] -> sptr_addr B ly pb = bv_unsigned (ew (havoc EL K_M1 ws) A_BUF) ->
bv_unsigned (ew (havoc EL K_M1 ws) A_LEN) = dlen data -> 65536 <= cap <= 2 ^ 26 -> st_nev S <= 64 ->
drv_minv S cap (dlen data) ->
YP03.bytes_at (mrestrict (w_H W) (ms_mem ms)) (sptr_addr B ly pb) data ->
FINV ly (w_H W) (ms_mem ms) ->
m_fs md = in_fs inp -> m_fds md = APSG.fds_std -> m_channel_reader md = true ->
dlen data < HDR_MIN ->
srealizes tfibsegs (mkCfg ms md) (POSTX data (in_fs inp)).
Proof.
intros ws W ms md ly S data pb cap Hlk HLc HS HR HAI HAR HTOP Hbl Hpb H42 Hcap Hnev Hminv Hbytes HFI Hfs Hfds Hcr HSH.
unfold HDR_MIN in HSH.
(* [tail_after] now takes the [runs_at] fact in [tail_at]'s EXISTENTIAL form
   (AD1w_w.v:69-70); [hdr_tfa] hands this proof the plain one, so pack it once here. *)
pose proof (ex_intro (fun rnd0 : EntryDraw => runs_at usp (mrestrict (w_H W) (ms_mem ms))
(runs_main_tfa true sp (ed_top rnd0) [a0; p] envp (in_execfn inp))) rnd HR) as HRx.
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
apply (SHORT sp brk mbase inp xw xd ws W ms' _ ly S a0 p data pb cap rnd Hsp Hargv Hva Hve Hvl Hlau Hvi Hvfs Hlk ltac:(unfold dlen; lia)).
apply (tail_after S_SHORT (ss_mem S_HDR) ER W ms md ly S pb cap data ms' mat S_HDR_win_ok wbs_SHORT ltac:(do 3 eexists; reflexivity)
E0' HS' HF HFr (eq_sym Hpb) H42 HRx HAI' HAR HTOP Hbl Hnev Hcap ltac:(unfold dlen; lia) HBLK Hfs Hfds Hcr Hminv HFI).
- (* Theorem Labs, 2026-11: the header, overrun and harness branches are cut: this twin's contract (AD1v_w.hdr_tfa)
     asks dlen data < HDR_MIN. *)
exfalso. lia.
Qed.
End d.
(* Theorem Labs, 2026-11: from the short leaf only, for files shorter than the header (AD1v_w.hdr_tfa). *)
Theorem tfib_hdr (B : asyms) (HB : TfibSyms B) (ARL : AR_laws tfibsegs B)
(SHORT : short_leaf_tfa B) : hdr_tfa B.
Proof.
intros sp brk mbase inp xw xd ws W ms md ly S a0 p data pb cap rnd
Hsp Hargv Hva Hve Hvl Hlau Hvi Hvfs Hlk HLc HS HR HAI HAR HTOP Hbl Hpb H42 Hcap Hnev Hminv Hbytes HFI Hfs Hfds Hcr HSH.
exact (tfib_hdr_at B HB ARL SHORT sp brk mbase inp xw xd a0 p rnd Hargv Hsp Hva Hve Hvl Hlau Hvi Hvfs ws W ms md ly S data pb cap
Hlk HLc HS HR HAI HAR HTOP Hbl Hpb H42 Hcap Hnev Hminv Hbytes HFI Hfs Hfds Hcr HSH).
Qed.
End c.
