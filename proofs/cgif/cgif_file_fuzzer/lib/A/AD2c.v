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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AD21 AD25 AD23 AD2h AD1w AD2f AD2b AD2g.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO05 YO09 YO06 YO01.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Lemma U_add0 : forall E x, U E (add0 x) = U E x.
Proof.
intros E x. unfold add0. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0) with 0.
rewrite Z.add_0_r. apply zcanon_id. unfold U, M64. apply u64_range.
Qed.
Lemma U_hdr_b2 : forall E b0 b1 b2 rest, ed E 2 = b0 :: b1 :: b2 :: rest -> U E (SData 2 2 1) = bv_unsigned b2.
Proof.
intros E b0 b1 b2 rest Hd. unfold U. cbn [sv_denot]. unfold data_word. rewrite Hd.
change (bytes_le_to_Z _) with (Z.lor (bv_unsigned b2) (Z.shiftl 0 8)).
rewrite Z.shiftl_0_l, Z.lor_0_r. pose proof (u8_range b2). apply unsigned_lit_small. lia.
Qed.
Lemma U_calls : forall E data b0 b1 b2 rest, ed E 2 = data -> data = b0 :: b1 :: b2 :: rest -> config_len data <> 0 ->
U E sv_calls = Z.of_nat (calls data).
Proof.
intros E data b0 b1 b2 rest Hd Ed Hcl. unfold sv_calls. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_hdr_b2 E b0 b1 b2 rest) by (rewrite Hd; exact Ed). rewrite !U_SLit. change (zcanon 3) with (Z.ones 2). change (zcanon 1) with 1.
rewrite Z.land_ones by lia. pose proof (u8_range b2). pose proof (Z.mod_pos_bound (bv_unsigned b2) (2 ^ 2) ltac:(lia)).
rewrite (zcanon_id (bv_unsigned b2 mod 2 ^ 2)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia).
unfold calls, cfg_byte. rewrite (proj2 (Z.eqb_neq _ _) Hcl). unfold dbyte. rewrite Ed. cbn [nth]. change (2 ^ 2) with 4. rewrite Z2Nat.id by lia. lia.
Qed.
Lemma list_len3 {X} : forall (l : list X), (3 <= length l)%nat -> exists a b c r, l = a :: b :: c :: r.
Proof. intros [|a [|b [|c r]]] H; cbn in H; try lia. exists a, b, c, r. reflexivity. Qed.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k AD1u.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Lemma st_ok_setreg : forall E ss ms (r : bv 5) v,
st_ok tfibsegs E ss ms -> bv_eqb r 0 = false -> sv_denot E v = sv_denot E (sr_get (ss_regs ss) r) -> st_ok tfibsegs E (setreg_ r v ss) ms.
Proof.
intros E ss ms r v (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) Hr Hv. unfold st_ok, setreg_. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
repeat (split; [assumption|]). split; [| split; assumption].
intros r'. destruct (decide (r' = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr. rewrite Hv. apply H7.
- rewrite sr_get_set_other by exact Hne. apply H7.
Qed.
Section e.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis ARL : AR_laws tfibsegs B.
Hypothesis RUNQ : run_Q_tfa B.
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
Lemma pb_run : forall (c0 : bool) E (W : world tfibsegs) ms md,
st_ok tfibsegs E (if c0 then ssP0 else ssP1) (restrict (w_H W) ms) ->
SRr tfibsegs W (mkCfg ms md) (at_st (if c0 then ssP0 else ssP1) (if c0 then sB0 else sB1) E W (ms_mem ms) md).
Proof.
intros c0 E W ms md HS. pose proof HWXi as HWX. destruct c0; srr_run_with tfibtbl_lp_ok HS;
apply SRr_ret; (split; [reflexivity|]);
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end; eexists; (split; [reflexivity|]);
(split; [exact HS|]); split; [exact HF | exact HFr | exact HF | exact HFr].
Qed.
Lemma bq_run : forall (c0 : bool) E (W : world tfibsegs) ms md,
st_ok tfibsegs E (add_cond (if c0 then sB0 else sB1) (if c0 then cond_CL0 else cond_CL1)) (restrict (w_H W) ms) ->
SRr tfibsegs W (mkCfg ms md) (at_st (if c0 then sB0 else sB1) (if c0 then sQ0 else sQ1) E W (ms_mem ms) md).
Proof.
intros c0 E W ms md HS. pose proof HWXi as HWX. destruct c0; srr_run_with tfibtbl_lp_ok HS;
apply SRr_ret; (split; [reflexivity|]);
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end; eexists; (split; [reflexivity|]);
(split; [exact HS|]); split; [exact HF | exact HFr | exact HF | exact HFr].
Qed.
Theorem tfib_post_P_at : forall ws (W : world tfibsegs) ms md ly S data (pb : sptr) cap,
fs_lookup (in_fs inp) p = Some data -> 6 + config_len data <= dlen data ->
tail_at B S_P (edset (havoc EL K_M1 ws) 2 data) sp inp a0 p data W ms md ly S pb cap ->
srealizes tfibsegs (mkCfg ms md) (run_shape (payload data) (calls data) (in_fs inp)).
Proof.
intros ws W ms md ly S data pb cap Hlk Hok HT.
pose proof (tfib_to_P B ARL sp inp xw xd a0 p Hsp Hva Hve ws W ms md ly S data pb cap Hok HT) as [HSP E60].
destruct HT as (HS & E41 & E42 & HR & HAI & HAR & HTOP & Hbl & Hnev & Hcap & HLc & HBLK & Hfs & Hfds & Hminv & HFI).
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp.
pose proof (top_ok_ceil _ _ HTOP) as HCT. pose proof (YM05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.
set (E' := edset (havoc EL K_M1 ws) 2 data) in *. set (buf := sptr_addr B ly pb) in *.
set (E3 := E_P E' data (buf + 2 + config_len data)) in *.
pose proof (config_len_bound data) as Hcl. unfold dlen in *.
assert (Hin : In (buf, cap) (ablocks B ly S)) by (unfold ablocks; rewrite Hbl; left; reflexivity).
pose proof (al_blocks _ _ ARL ly S W (ms_mem ms) md _ _ HAR Hin) as (_ & Hb4096 & Hbce & _).
assert (Hcap' : cap <= req_size cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
assert (NIMG : forall a, buf <= a < buf + cap -> ~ in_img tfibsegs a).
{ intros a Ha. assert (Ha' : buf <= a < buf + req_size cap) by lia.
exact (proj2 (al_client_img _ _ ARL ly S W (ms_mem ms) md a HAR (or_introl (ex_intro _ _ (ex_intro _ cap (conj Hin Ha')))))). }
assert (E3_0 : bv_unsigned (ew E3 0) = usp) by (subst E3 E'; rewrite E_P_old by lia; cbn [ew edset]; rewrite ew_havoc_old by (unfold K_M1; lia); reflexivity).
assert (E3_41 : bv_unsigned (ew E3 A_BUF) = buf) by (subst E3; rewrite E_P_old by (unfold A_BUF; lia); exact E41).
assert (E3_42 : bv_unsigned (ew E3 A_LEN) = Z.of_nat (length data)) by (subst E3; rewrite E_P_old by (unfold A_LEN; lia); exact E42).
assert (Ed2 : ed E3 2 = data) by (subst E3 E'; rewrite E_P_ed by lia; reflexivity).
destruct (list_len3 data ltac:(lia)) as (d0 & d1 & d2 & rest & Ed).
assert (Hd' : ed E3 2 = d0 :: d1 :: (d2 :: rest)) by (rewrite Ed2; exact Ed).
assert (UCL : U E3 sv_cl00 = config_len data).
{ unfold sv_cl00. rewrite !U_add0. transitivity (config_len (d0 :: d1 :: d2 :: rest)); [exact (U_cl E3 d0 d1 (d2 :: rest) Hd') | rewrite <- Ed; reflexivity]. }
set (c0 := config_len data =? 0) in *.
apply (SRr_srealizes tfibsegs W (mkCfg ms md) _ _ (pb_run c0 E3 W ms md HSP) HAI).
intros W0 c' _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [cfg_model] in HAI1.
assert (HS2 : st_ok tfibsegs E3 (add_cond (if c0 then sB0 else sB1) (if c0 then cond_CL0 else cond_CL1)) (restrict (w_H W) ms1)).
{ subst c0. destruct (Z.eqb_spec (config_len data) 0) as [Hz|Hnz].
- apply (st_ok_add_cond tfibsegs E3 sB0 _ BC_EQ sv_cl00 (SLit 0) HS1). rewrite branch_eq_U, UCL, U_SLit, Hz. reflexivity.
- apply (st_ok_add_cond tfibsegs E3 sB1 _ BC_NE sv_cl00 (SLit 0) HS1). rewrite branch_ne_U, UCL, U_SLit. change (zcanon 0) with 0.
apply Bool.negb_true_iff. apply Z.eqb_neq. exact Hnz. }
apply (SRr_srealizes tfibsegs W _ _ _ (bq_run c0 E3 W ms1 _ HS2) HAI1).
intros W1 c2 _ HAI2 (-> & ms2 & mat2 & -> & HS3 & HF2 & HFr2). cbn [cfg_model] in HAI2. rewrite wvb_collapse in HAI2 |- *.
assert (HS4 : st_ok tfibsegs E3 (sQ c0 (Z.of_nat (calls data))) (restrict (w_H W) ms2)).
{ unfold sQ. subst c0. destruct (Z.eqb_spec (config_len data) 0) as [Hz|Hnz]; [exact HS3|].
unfold sQ1k. apply (st_ok_setreg E3 sQ1 _ 21%bv (SLit (Z.of_nat (calls data))) HS3 eq_refl).
pose proof sBQ_facts as (_ & _ & _ & _ & _ & _ & _ & Q20 & _). rewrite Q20.
rewrite (denot_lit_U E3 (SLit _)), (denot_lit_U E3 sv_calls). f_equal. rewrite U_SLit, (U_calls E3 data d0 d1 d2 rest Ed2 Ed Hnz).
pose proof (calls_bound data). apply zcanon_id. unfold M64. lia. }
pose proof skel_B as [SK0 SK1].
assert (SK : skeleton (ss_mem (if c0 then sB0 else sB1)) = skeleton (ss_mem (if c0 then ssP0 else ssP1))) by (destruct c0; [exact SK0 | exact SK1]).
assert (WOK : forallb drv_win_ok (ss_mem (if c0 then ssP0 else ssP1)) = true) by (destruct c0; [exact ssP0_win_ok | exact ssP1_win_ok]).
assert (HF : frame_of E3 (ss_mem (if c0 then ssP0 else ssP1)) (ms_mem ms) (ms_mem ms2)).
{ apply (frame_of_trans E3 _ _ _ _ _ eq_refl HF1). exact (frame_of_skel' E3 _ _ _ _ (eq_sym SK) HF2). }
assert (HFr : frame_of E3 (ss_mem (if c0 then ssP0 else ssP1)) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms2))).
{ apply (frame_of_trans E3 _ _ _ _ _ eq_refl HFr1). exact (frame_of_skel' E3 _ _ _ _ (eq_sym SK) HFr2). }
pose proof (st_ok_mem_ok tfibsegs E3 _ _ HS4) as HM4. cbn [restrict ms_mem] in HM4.
assert (Hwin : forall a, usp - 65536 <= a < usp -> apresent (w_H W) (ms_mem ms2) a).
{ intros a Ha. unfold sQ, sQ1k, setreg_ in HM4. cbn [ss_mem] in HM4.
destruct c0; destruct (Z.lt_ge_cases a (usp - 128)).
- eapply (win_present sp Hsp E3 (w_H W) (ms_mem ms2) (ss_mem sQ0)); [exact HM4 | left; reflexivity | exact E3_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E3 (w_H W) (ms_mem ms2) (ss_mem sQ0)); [exact HM4 | right; left; reflexivity | exact E3_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E3 (w_H W) (ms_mem ms2) (ss_mem sQ1)); [exact HM4 | left; reflexivity | exact E3_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E3 (w_H W) (ms_mem ms2) (ss_mem sQ1)); [exact HM4 | right; left; reflexivity | exact E3_0 | lia | lia | cbn; lia]. }
apply (RUNQ sp inp xw xd ws W ms2 _ ly S a0 p data pb cap Hargv Hsp Hva Hve Hvfs Hlk ltac:(unfold dlen; lia)); [| exact E60].
split; [exact HS4|]. split; [exact E3_41|]. split; [exact E3_42|]. split.
{ eapply (runs_at_frame E3 (ss_facts (sQ c0 (Z.of_nat (calls data)))) (ss_mem (if c0 then ssP0 else ssP1)));
[exact (st_ok_facts_ok tfibsegs E3 _ _ HS4) | | exact HFr | rewrite E3_0; lia | exact HR].
unfold sQ, sQ1k, setreg_. cbn [ss_facts]. pose proof wbs_Q as [WQ0 WQ1]. destruct c0; [exact WQ0 | exact WQ1]. }
split; [exact HAI2|]. split.
{ apply (AR_after_run B HB ARL ly S W E3 _ (ms_mem ms) (ms_mem ms2) md mat2 HAR WOK); [rewrite E3_0; exact Ulo | rewrite E3_0; exact HCT | exact HF |].
rewrite E3_0. intros a Ha. exact (apresent_some' _ _ _ (Hwin a Ha)). }
split; [exact HTOP|]. split; [exact Hbl|]. split; [exact Hnev|]. split; [exact Hcap|]. split; [unfold dlen; lia|]. split.
{ unfold dlen. apply (blk_of_frame_r _ _ _ _ _ buf (Z.of_nat (length data)) data usp HFr WOK E3_0 Ulo); [intros a Ha; apply NIMG; lia | lia | lia | exact HBLK]. }
split; [rewrite wvb_fs'; exact Hfs |]. split; [rewrite wvb_fds'; exact Hfds |]. split; [exact Hminv|].
exact (finv_run B ly S W (ms_mem ms) md (w_H W) E3 _ _ _ usp HAR HFr WOK E3_0 Ulo Uhi HTOP HFI).
Qed.
End e.
Theorem tfib_post_P (B : asyms) (HB : TfibSyms B) (ARL : AR_laws tfibsegs B) (RUNQ : run_Q_tfa B) : post_P_tfa B.
Proof.
intros sp inp xw xd ws W ms md ly S a0 p data pb cap Hargv Hsp Hva Hve Hvfs Hlk Hok HT.
exact (tfib_post_P_at B HB ARL RUNQ sp inp xw xd a0 p Hargv Hsp Hva Hve Hvfs ws W ms md ly S data pb cap Hlk Hok HT).
Qed.
End d.
