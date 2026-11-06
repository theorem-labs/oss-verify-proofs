(* lv2_locate_manifest_readings, PRE piece c5 (FMW_rd_pre_cuts.v rdp_seg_C5). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YCbm.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI00 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_g3kit FMW_rd_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_rd_cuts FMW_rd_ret ACej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_rd_pre_k FMW_rd_pre_cuts.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* a slot written from a register atom plus a constant *)
Lemma rdc5_soff {fx : YK11.FPState} : forall regs (r : bv 5) n k x v, Z.of_nat n = bv_unsigned r ->
  getr regs r = w64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + k < 2 ^ 64 -> v = x + k ->
  sv_denot (Ereg regs []) (SOff n k) = Z_to_bv 64 v.
Proof.
intros regs r n k x v Hn Hr Hx Hxk ->. apply bv_eq. rewrite denot_SOff, (ew_Ereg_nat regs [] n r Hn), Hr. unfold w64.
rewrite (unsigned_lit_small x Hx), (unsigned_lit_small (x + k) Hxk). apply zcanon_id. unfold M64. lia.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable CTX : list (list Z).
Hypothesis IMG : fm_img_facts tfibsegs B.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Abbreviation rdJ cx := (ajournal tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx)
  (cx_W cx) (cx_mem cx) (cx_md cx) []).

(* RD_C5 = 0x81ca8, after fuzz_free: beqz s5; found -> s5 = 1 -> RD_R; else the frame locals -> RD_L *)
Theorem rdp_C5_holds : (forall f, rd_seg_L B CTX f) -> rdp_seg_C5 B CTX.
Proof.
intros SEGL cx m1 ly5 S5 W5 regs5 mem5 md5 v HB HJ HR R22 R21 Hv HPRO KE HPm HG Hcf Hub HSS.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof g3_wx as Hwx. pose proof g3_segs_low as Hsegs.
pose proof HB as (HAN & _ & _ & H10 & H11 & H12 & _ & _ & _ & _ & Ct & Cu & _).
pose proof HAN as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Cu as (_ & Hu4 & Hucl & _). pose proof Ct as (_ & Ht4 & Htcl & _).
assert (FFR : STK_readings = 16624) by reflexivity.
assert (Esp : cx_sp cx = spZ (cx_regs cx)) by reflexivity. assert (HF : cx_F cx = cx_sp cx - 208) by reflexivity.
pose proof (u64_range (getr (cx_regs cx) 2)) as Sp64.
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R24).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (Hlen0 : (length (cx_ub cx) =? 0)%nat = false).
{ apply Nat.eqb_neq. intros H0. apply Hub. apply length_zero_iff_nil. exact H0. }
assert (Hcf0 : (cx_cnt cx =? cx_fail cx) = false) by (apply Z.eqb_neq; exact Hcf).
assert (HS : st_ok tfibsegs (Ereg regs5 []) rdp_ss5 (restrict (w_H W5) (mkst regs5 (Z_to_bv 64 RD_C5) mem5 (seg_rom tfibsegs)))).
{ apply (rdp_ss5_ok W5 regs5 [] mem5 (cx_F cx) R2); [lia | |].
  - rewrite HF. replace (cx_sp cx - 208) with (spZ (cx_regs cx) + (-13) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
  - intros a Ha. apply Hpres. lia. }
set (E5 := Ereg regs5 []) in HS.
assert (E2 : bv_unsigned (ew E5 2) = cx_sp cx + 16 + -224).
{ subst E5. rewrite (ew_Ereg_nat regs5 [] 2 2%bv eq_refl), R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (E21 : ew E5 21 = Z_to_bv 64 v) by (subst E5; rewrite (ew_Ereg_nat regs5 [] 21 21%bv eq_refl); exact R21).
change mem5 with (ms_mem (mkst regs5 (Z_to_bv 64 RD_C5) mem5 (seg_rom tfibsegs))) in HJ.
srr_branch_with rd_tbl_ok HS.
- (* s5 = 0: the uri is found nowhere as "<uri>": the frame locals, then the scan *)
  rewrite branch_eq_U, (U_atom _ 21 v E21 Hv), U_SLit in Hc. change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc. subst v.
  assert (Hwh : whole (cx_tb cx) (cx_ub cx) = false).
  { destruct HSS as [(_ & Hno) | (j & _ & Hj)]; [exact (rdp_whole_no _ _ Hno) | lia]. }
  aj_run_to rd_tbl_ok HS HJ RD_L.
  { rdp_awr (-224) E2. }
  rdp_name HS ms3.
  assert (KE3 : rdp_ke cx m1 W5 (ms_mem ms3) /\ g3_low_kept W5 W5 mem5 (ms_mem ms3)).
  { assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ (cx_F cx <= a < cx_F cx + 0x68) ->
      aview tfibsegs (w_H W5) (ms_mem ms3) a = aview tfibsegs (w_H W5) mem5 a).
    { intros a Ha Hn. apply (g3_aview_frame E5 _ (w_H W5) mem5 (ms_mem ms3) HFr a Ha).
      intros (r & Hin & Hr). cbv [add_cond rdp_ss5 ss_mem In] in Hin. destruct Hin as [<-|[]].
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite E2 in Hr. apply Hn. lia. }
    split; intros a Ha; [rewrite AV by lia; exact (KE a ltac:(lia)) | apply AV; lia]. }
  destruct KE3 as [KE3 LK3].
  pose proof (rdp_regs4_run cx _ regs5 _ ms3 HS ltac:(vm_compute; reflexivity) HR) as (Q2 & Q3 & Q4 & Q8).
  rreg HS (9%bv : bv 5) Q9. rreg HS (18%bv : bv 5) Q18. rreg HS (20%bv : bv 5) Q20. rreg HS (24%bv : bv 5) Q24.
  (* the frame locals rd_loc_list cx 0 *)
  assert (SL : rd_slots_ok cx W5 (ms_mem ms3) (rd_loc_list cx 0)).
  { assert (Hb : bv_unsigned (ew E5 2) = cx_F cx) by (rewrite E2; unfold cx_F; lia).
    lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
      let r := eval vm_compute in (nth_error (ss_mem ssx) 0) in
      lazymatch r with Some (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
        unfold rd_slots_ok, rd_loc_list; cbn [fst snd];
        repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
        (split; [eapply (rdp_slot Ex ssx W5 msx lo hi wlo whi cs); [exact HS | reflexivity | vm_compute; reflexivity | exact Hb | |] |])
      end end.
    all: subst E5.
    all: try (first [ eapply (rdc5_soff regs5 9%bv 9 _ (cx_sp cx) _ eq_refl R9)
                    | eapply (rdc5_soff regs5 18%bv 18 _ (cx_u cx) _ eq_refl R18)
                    | eapply (rdc5_soff regs5 22%bv 22 _ (cx_ulen cx) _ eq_refl R22)
                    | eapply (rdc5_soff regs5 24%bv 24 _ (cx_t cx) _ eq_refl R24) ]).
    all: try (unfold RD_MASK1, RD_MASK2, RD_PREFIX; reflexivity).
    all: unfold RD_MASK1, RD_MASK2, RD_PREFIX, cx_ulen, cx_sp, spZ in *; lia. }
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc]. rdp_cfg RD_L.
  apply (SEGL (S (length (cx_tb cx))) cx 0%nat 0%nat ly5 S5 W5 (ms_regs ms3) (ms_mem ms3) _ HB).
  unfold rd_L, rd_loop.
  split; [|split; [|split]].
  + split; [eapply (rdp_com_of B CTX IMG cx EV_names ly5 S5 W5 (ms_regs ms3) (ms_mem ms3) _ m1 HB HJ);
      [unfold EV_names; lia | exact Q2 | exact Q3 | exact Q4 | exact Q8 | exact HPRO | exact KE3
      | intros x Hx; exact (Permutation_in x (Permutation_sym HPm) Hx)]|].
    split; [rewrite Q9; reflexivity|]. split; [rewrite Q18; reflexivity|].
    split; [exact SL|].
    split; [rewrite ?Nat2Z.inj_0, ?Z.add_0_r; exact (rdp_rp B CTX cx m1 W5 (ms_mem ms3) HB HPRO KE3)|].
    split; [exact HPm|].
    split; [exact (g3_fm_glob_kept W5 W5 mem5 (ms_mem ms3) _ _ _ _ HG LK3)|].
    split; [exact Hcf|]. split; [exact Hub|]. split; [exact Hwh | lia].
  + unfold rd_acc. split; [lia|]. split; [lia|].
    split; [unfold names; rewrite Hlen0, Hwh; reflexivity | unfold nreadings; rewrite Hlen0, Hwh; reflexivity].
  + rewrite Q20. reflexivity.
  + rewrite Q24. subst E5. rewrite ?(ew_Ereg_nat regs5 [] 24 24%bv eq_refl), R24, ?Nat2Z.inj_0, ?Z.add_0_r. reflexivity.
- (* s5 <> 0: "<uri>" found: s5 = 1, return *)
  rewrite branch_eq_U, (U_atom _ 21 v E21 Hv), U_SLit in Hc. change (zcanon 0) with 0 in Hc. apply Z.eqb_neq in Hc.
  assert (Hwh : whole (cx_tb cx) (cx_ub cx) = true).
  { destruct HSS as [(Hv0 & _) | (j & Hfo & _)]; [lia | exact (rdp_whole_occ _ _ j (proj1 Hfo))]. }
  aj_run_to rd_tbl_ok HS HJ RD_R.
  { rdp_awr (-224) E2. }
  rdp_name HS ms3.
  assert (KE3 : rdp_ke cx m1 W5 (ms_mem ms3) /\ g3_low_kept W5 W5 mem5 (ms_mem ms3)).
  { assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ (cx_F cx <= a < cx_F cx + 0x68) ->
      aview tfibsegs (w_H W5) (ms_mem ms3) a = aview tfibsegs (w_H W5) mem5 a).
    { intros a Ha Hn. apply (g3_aview_frame E5 _ (w_H W5) mem5 (ms_mem ms3) HFr a Ha).
      intros (r & Hin & Hr). cbv [add_cond rdp_ss5 ss_mem In] in Hin. destruct Hin as [<-|[]].
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite E2 in Hr. apply Hn. lia. }
    split; intros a Ha; [rewrite AV by lia; exact (KE a ltac:(lia)) | apply AV; lia]. }
  destruct KE3 as [KE3 LK3].
  pose proof (rdp_regs4_run cx _ regs5 _ ms3 HS ltac:(vm_compute; reflexivity) HR) as (Q2 & Q3 & Q4 & Q8).
  rreg HS (21%bv : bv 5) Q21.
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc]. rdp_cfg RD_R.
  apply (rd_ret_holds B CTX cx EV_names ly5 S5 W5 (ms_regs ms3) (ms_mem ms3) _ 1 HB).
  + eapply (rdp_com_of B CTX IMG cx EV_names ly5 S5 W5 (ms_regs ms3) (ms_mem ms3) _ m1 HB HJ);
      [unfold EV_names; lia | exact Q2 | exact Q3 | exact Q4 | exact Q8 | exact HPRO | exact KE3
      | intros x Hx; exact (Permutation_in x (Permutation_sym HPm) Hx)].
  + rewrite Q21. reflexivity.
  + lia.
  + unfold rd_ret_facts. split; [exact HPm|]. split.
    * right. right. split; [exact Hub|]. split; [exact Hcf|]. split; [unfold names; rewrite Hlen0, Hwh; reflexivity|].
      exact (g3_fm_glob_kept W5 W5 mem5 (ms_mem ms3) _ _ _ _ HG LK3).
    * rewrite Hlen0, Hcf0. cbn [orb]. unfold nreadings. rewrite Hlen0, Hwh. cbn [Z.of_nat]. rewrite Z.add_0_r.
      exact (rdp_rp B CTX cx m1 W5 (ms_mem ms3) HB HPRO KE3).
Qed.
End c.
