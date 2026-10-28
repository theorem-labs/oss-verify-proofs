(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK00 YK0h YK14 YK1b YK15 YK18 YK0p YP0n YK0s YM02 YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YN3q YN3v YI04 YL0a YL0b YL09 YK04 YA0i YA0n YA0o YA0p YA0m YK09 YA0e YG00 YG0a YG01 YG0k YG0f YG0v YG0n YG0d YCe5.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB12 AF0l AB1h AB13 AF0m AD2j AD2i AD1t AD1y AD20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YD2n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AD1v AD26 AD24 AD21 AD25.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO05 YO09 YO06 YO01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Lemma skipn3_dir : ss_mem S_DIR = firstn 3 (ss_mem S_DIR) ++ IMG_REGIONS ++ skipn 36 (ss_mem S_DIR) /\ length (ss_mem S_DIR) = 39%nat.
Proof. vm_compute. split; reflexivity. Qed.
Lemma submem_skipn' : forall n rs, submem (skipn n rs) rs.
Proof.
induction n as [|n IH]; intros rs.
- apply submem_refl.
- destruct rs as [|r rs]; cbn; [constructor|]. apply submem_drop. apply IH.
Qed.
Lemma submem_app_l : forall l1 l2, submem l1 (l1 ++ l2).
Proof.
induction l1 as [|r l1 IH]; intros l2; cbn.
- induction l2; [constructor | apply submem_drop; assumption].
- apply submem_keep; [apply subregion_refl || (repeat split; try lia; auto) | apply IH].
Qed.
Lemma submem_mid : forall pre l1 l2, submem l1 (pre ++ l1 ++ l2).
Proof. induction pre as [|r pre IH]; intros; cbn; [apply submem_app_l | apply submem_drop; apply IH]. Qed.
Lemma img_sub_DIR : submem IMG_REGIONS (ss_mem S_DIR).
Proof. rewrite (proj1 skipn3_dir). apply submem_mid. Qed.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k AD1u.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Section c.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis ARL : AR_laws tfibsegs B.
Hypothesis RDERR : rderr_leaf_tfa B.
Theorem tfib_rd0_dir : rd0_dir_tfa B.
Proof.
intros sp inp xw xd ws W ms md ly S a0 p pb Hargv Hsp Hva Hve Hfit Hdot HS HR HAI HAR HTOP Hbl Hpb Hnev Hfs Hfds.
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp. pose proof (top_ok_ceil _ _ HTOP) as HCT.
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR. unfold ASAN_CEIL in CR.
set (EL := YP08.E0 sp [a0; p] (in_envp inp) xw xd) in *.
set (E1 := havoc EL K_M1 ws) in *.
assert (HE1 : eagree sp inp xw xd a0 p E1) by (subst E1 EL; split; [intros k Hk; apply ew_havoc_old; exact Hk | reflexivity]).
pose proof (eagree_0 sp inp xw xd a0 p E1 HE1) as E1_0.
assert (Hin : In (sptr_addr B ly pb, 65536) (ablocks B ly S)) by (unfold ablocks; rewrite Hbl; left; reflexivity).
pose proof (al_blocks _ _ ARL ly S W (ms_mem ms) md _ _ HAR Hin) as (Hal & Hb4096 & Hbce & _).
pose proof (add_rt B HB sp inp xw xd a0 p Hsp E1 ss_rd0 W ms ly S md HE1 HS HAR (proj1 rd0_ext)) as HS'.
rewrite (proj1 with_rt_eqs) in HS'.
pose proof (reabs_RD EL E1 ss_rd0_rt ms (w_H W) (proj1 HE1) (proj2 HE1) HS' (proj1 (proj2 (proj2 (proj2 mem_RD_rt)))) (proj1 reabs_chk_RD)
ltac:(rewrite (proj1 mem_RD_rt); apply submem_refl)) as HSR.
cbn [ms_regs restrict] in HSR.
set (ER := E_RD EL (ms_regs ms)) in *.
pose proof ss_rd0_regs as (Q9 & Q19 & Q21 & _).
assert (R9 : getr (ms_regs ms) 9%bv = ew E1 A_BUF) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E1 ss_rd0 ms 9%bv HS), Q9; cbn [sv_denot]; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).
assert (R19 : getr (ms_regs ms) 19%bv = Z_to_bv 64 0) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E1 ss_rd0 ms 19%bv HS), Q19; reflexivity).
assert (R21 : getr (ms_regs ms) 21%bv = Z_to_bv 64 65536) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E1 ss_rd0 ms 21%bv HS), Q21; reflexivity).
assert (A58 : ew ER A_LEN = Z_to_bv 64 0) by (subst ER; unfold A_LEN; change 58%nat with (K_M1 + 16)%nat; rewrite (E_RD_new EL _ 16) by (cbn; lia); exact R19).
assert (A59 : ew ER A_CAP = Z_to_bv 64 65536) by (subst ER; unfold A_CAP; change 59%nat with (K_M1 + 17)%nat; rewrite (E_RD_new EL _ 17) by (cbn; lia); exact R21).
specialize (HSR ltac:(unfold afact_ok, fact_len, fact_cap; cbn [af_lo af_hi af_al2]; rewrite A58, A59, !u64_lit by lia; repeat split; first [lia | rewrite Z.mod_1_r; reflexivity | change (2 ^ 16) with 65536; reflexivity])).
assert (HER : eagree sp inp xw xd a0 p ER) by (subst ER; split; [intros k Hk; apply E_RD_old; exact Hk | reflexivity]).
pose proof (eagree_0 sp inp xw xd a0 p ER HER) as ER0.
apply (SRr_srealizes tfibsegs W (mkCfg ms md) _ _
(rd_to_RW sp inp xw xd a0 p ER W ms md 0 65536 HER HSR ltac:(rewrite A58; apply u64_lit; lia) ltac:(rewrite A59; apply u64_lit; lia) ltac:(lia) ltac:(lia)) HAI).
intros W0 c0 _ HAI0 (-> & ms0 & mat0 & -> & HS0 & HF0 & HFr0). cbn [cfg_model] in HAI0.
rewrite Z.min_r in HS0 by lia.
set (E2 := ewset ER A_WANT (Z_to_bv 64 65536)) in *. set (md0 := with_vm_backing (m_vm_lazy md) mat0 md) in *.
assert (HE2 : eagree sp inp xw xd a0 p E2) by (subst E2; apply eagree_ewset; [exact HER | unfold A_WANT, K_M1; lia]).
pose proof (eagree_0 sp inp xw xd a0 p E2 HE2) as E2_0.
assert (HAR0 : AR tfibsegs B ly S W (ms_mem ms0) md0).
{ apply (AR_after_run B HB ARL ly S W ER LH_mem (ms_mem ms) (ms_mem ms0) md mat0 HAR (proj1 win_ok_iter)); [rewrite ER0; exact Ulo | rewrite ER0; exact HCT | exact HF0 |].
rewrite ER0. intros a Ha. apply (apresent_some' (w_H W)). apply (winP sp Hsp E2 S_RW ms0 W (or_introl HS0) E2_0); [| exact Ha]. do 3 eexists; reflexivity. }
assert (HR0 : runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms0)) (runs_main_tfa true sp [a0; p] (in_envp inp))).
{ eapply (runs_at_frame ER RD_facts LH_mem); [exact (st_ok_facts_ok tfibsegs ER S_RD _ HSR) | exact (proj1 (proj2 wbs_iter2)) | exact HFr0 | rewrite ER0; lia | exact HR]. }
apply (SRr_srealizes tfibsegs W (mkCfg ms0 md0) _ _
(rd_dir B HB ARL sp inp xw xd a0 p Hsp E2 W ms0 md0 ly S 65536 HE2 HS0 ltac:(subst E2; rewrite ew_ewset_same; apply u64_lit; lia)
ltac:(lia) HAR0 HTOP ltac:(subst md0; rewrite wvb_fds'; exact Hfds)) HAI0).
intros W' c' _ HAI' (-> & ms' & md' & -> & HS2 & HAI2 & HAR2 & Hfds2 & Hfs2 & HF & HFr). cbn [cfg_model] in HAI'.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E2 S_DIR ms' HS2 eq_refl) as Hshape. rewrite Hshape.
change (Z_to_bv 64 (ss_pc S_DIR)) with (w64 0x4192c).
pose proof (st_ok_mem_ok tfibsegs E2 S_DIR _ HS2) as HM2. cbn [restrict ms_mem] in HM2.
assert (HR2 : runs_at (bv_unsigned sp) (mrestrict (w_H W) (ms_mem ms')) (runs_main_tfa true sp [a0; p] (in_envp inp))).
{ eapply (runs_at_frame E2 (ss_facts S_DIR) LH_mem); [exact (st_ok_facts_ok tfibsegs E2 S_DIR _ HS2) | exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 wbs_iter)))))) | exact HFr | rewrite E2_0; lia | exact HR0]. }
pose proof (runs_at_nth _ _ _ 2 _ _ HR2 eq_refl) as HBr. cbn [nth] in HBr.
pose proof (runs_at_bounds _ _ _ 2 _ _ HR2 eq_refl) as HBb. cbn [nth fst snd] in HBb. rewrite length_app in HBb. cbn [length] in HBb.
subst md0. rewrite ?wvb_fs in Hfs2. rewrite ?Hfs in Hfs2.
apply (RDERR E2 W (ms_regs ms') (ms_mem ms') md' ly S (bv_unsigned sp) p (z_argv (bv_unsigned sp) [a0; p] (in_envp inp) 1) (in_fs inp)).
- exact E2_0.
- lia.
- exact U16.
- exact (tid_of_st_ok E2 S_DIR _ HS2 ltac:(vm_compute; reflexivity)).
- rewrite (st_ok_restrict_reg tfibsegs (w_H W) E2 S_DIR ms' 10%bv HS2); reflexivity.
- rewrite (st_ok_restrict_reg tfibsegs (w_H W) E2 S_DIR ms' 11%bv HS2); reflexivity.
- rewrite (st_ok_restrict_reg tfibsegs (w_H W) E2 S_DIR ms' 12%bv HS2). pose proof S_DIR_facts as (_ & _ & _ & D12 & _). rewrite D12. cbn [sv_denot]. rewrite Z.add_0_r.
rewrite (proj1 HE2 2%nat) by (unfold K_M1; lia). subst EL. rewrite (YP08.ew2' sp [a0; p] (in_envp inp) Hsp Hva Hve) by (cbn; lia). reflexivity.
- rewrite (st_ok_restrict_reg tfibsegs (w_H W) E2 S_DIR ms' 1%bv HS2); reflexivity.
- unfold spZ. rewrite (st_ok_restrict_reg tfibsegs (w_H W) E2 S_DIR ms' 2%bv HS2). pose proof S_DIR_facts as (_ & _ & _ & _ & _ & D2 & _). rewrite D2. cbn [sv_denot]. rewrite E2_0. apply u64_lit. unfold sp_window_lo in Ulo; lia.
- rewrite (st_ok_restrict_reg tfibsegs (w_H W) E2 S_DIR ms' 3%bv HS2); reflexivity.
- rewrite (st_ok_restrict_reg tfibsegs (w_H W) E2 S_DIR ms' 4%bv HS2); reflexivity.
- lia.
- pose proof (argv_str_fits' sp [a0; p] (in_envp inp) 1 Hfit ltac:(cbn; lia)) as Z1. cbn [nth] in Z1. exact Z1.
- exact (argv_no_nul [a0; p] Hva 1 ltac:(cbn; lia)).
- exact (argv_str_len [a0; p] Hva 1 ltac:(cbn; lia)).
- exact HBr.
- pose proof (argv_over_read sp (StackLayout.mkDraw (Z_to_bv 128 0) (fun _ => Z_to_bv 8 0)) [a0; p] (in_envp inp) true _ 1 Hsp ltac:(cbn; lia) HR2) as OR1. cbn [nth] in OR1. exact OR1.
- exact (mem_ok_sub tfibsegs E2 _ _ IMG_REGIONS img_sub_DIR ltac:(reflexivity) HM2).
- intros a Ha. apply (winP sp Hsp E2 S_DIR ms' W (or_introl HS2) E2_0); [| exact Ha]. do 3 eexists; reflexivity.
- exact HAI2.
- exact HAR2.
- exact HTOP.
- unfold EV_MAX. lia.
- rewrite Hfds2. rewrite wvb_fds'. rewrite Hfds. reflexivity.
- rewrite Hfs2. rewrite wvb_fs'. exact Hfs.
Qed.
End c.
End b.
