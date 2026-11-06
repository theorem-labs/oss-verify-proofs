(* has_prefixed on fm.asan-ubsan (G2, image B), loop segment NCMP 0x824a8..0x824b8 (lv2_locate.c:67): a0 = start =
   t + a - plen - 1 (s2), a1 = the prefix t + q (frame slot sp + 16), a2 = plen (s1), `jal` the strncmp interceptor
   (PC_strncmp 0x41334, FMH_Rt.astrncmp_realizes, a Section hypothesis); at the return 0x824b8 `bnez a0` -> the loop
   tail 0x82520, else the prefix segment 0x824bc. No UBSan guard lies in 0x824a8..0x824bc. Proves the kit's
   seg_ncmp_ok (lib/B/FMW_hp_kit.v). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI04 YN3v YI08.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YA0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YC20 YI16 YI00 YM05 YG0q YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_g2rt FMW_hp_kit FMW_hp_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel has_prefixed_model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* a register after a run, as Z_to_bv 64 (U E e) of the engine's term e *)
Lemma hpn_sv_denot_U : forall E e, sv_denot E e = Z_to_bv 64 (U E e).
Proof. intros E e. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Ltac hpn_rregU HS r Hr :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    assert (Hr : getr (ms_regs ms) r = Z_to_bv 64 (U E e))
      by (rewrite <- hpn_sv_denot_U; exact (st_ok_restrict_reg segs H E ss ms r HS))
  end.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Hypothesis IMGF : fm_img_facts tfibsegs B.
Hypothesis ASTRNCMP : astrncmp_realizes tfibsegs B PC_strncmp.

Lemma hpn_keep_run : forall L E ss H ms regs0 extra,
  st_ok tfibsegs E ss (restrict H ms) -> env_agree 32 (Ereg regs0 extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) L = true ->
  regs_keep L regs0 (ms_regs ms).
Proof.
intros L E ss H ms regs0 extra HS HA Hc. exact (regs_keep_of_st_ok L E ss (restrict H ms) regs0 extra HS HA Hc).
Qed.

Lemma seg_ncmp : seg_ncmp_ok B.
Proof.
intros cx a KT KP lyc Sc W regs m mdc H (Ha & R18 & R22).
pose proof g2_segs_low as Hsegs. pose proof g2_wx as Hwx.
pose proof (hp_sp B cx a lyc Sc W regs m mdc H) as (Hsp1 & Hsp2 & Hspc).
pose proof (hp_cstr B IMGF cx a lyc Sc W regs m mdc H) as (Ht & Hl).
pose proof Ht as (_ & Ht4 & Htc & _).
pose proof H as (HE & HJ & Hab & Q3 & Q4 & Hsp & HF & HSL & Q8 & Q9 & Q19 & Q20 & Q21 & Q23 & Q24 & Q25 & Q26 & Q27
  & Hmt & Hgl).
pose proof HE as (_ & _ & _ & _ & _ & _ & _ & Hlb & Hq & Hplen & Hqp & Htmax & _).
pose proof (has_prefixed_model.mt_len _ _ _ Hmt) as Halen.
ceil2. unfold MANIFEST_MAX in Htmax.
(* the two string indices strncmp reads: start = a - plen - 1 and q *)
set (k := (a - Z.to_nat (cx_plen cx) - 1)%nat).
assert (Ek : Z.of_nat k = Z.of_nat a - cx_plen cx - 1) by (unfold k; lia).
assert (Hk : (k <= length (cx_tb cx))%nat) by (unfold k; lia).
assert (Hqn : (Z.to_nat (cx_q cx) <= length (cx_tb cx))%nat) by lia.
assert (Eq : Z.of_nat (Z.to_nat (cx_q cx)) = cx_q cx) by lia.
(* 0x824a8..0x824b4: a0 = s2, a1 = [sp + 16], a2 = s1, jal strncmp *)
pose proof (hp_seat B IMGF cx a lyc Sc W regs m mdc HP_NCMP H) as HS.
set (E := Ereg regs [w64 (Z.of_nat (length (cx_lb cx))); w64 (cx_t cx + cx_q cx)]) in HS.
assert (HAE : env_agree 32 (Ereg regs [w64 (Z.of_nat (length (cx_lb cx))); w64 (cx_t cx + cx_q cx)]) E)
  by (split; [intros; reflexivity | reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (X9 : ew E 9 = Z_to_bv 64 (cx_plen cx)) by (unfold E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact Q9).
assert (X18 : ew E 18 = Z_to_bv 64 (cx_t cx + Z.of_nat a - cx_plen cx - 1))
  by (unfold E; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact R18).
assert (X33 : ew E 33 = Z_to_bv 64 (cx_t cx + cx_q cx)) by exact (ew_Ereg_extra regs _ 1).
unfold cfg_at. change (w64 HP_NCMP) with (Z_to_bv 64 HP_NCMP).
aj_run tbl_hp_ok HS HJ.
{ awr_ok_tac. }
pose proof (gframe_of_frame tfibsegs W E _ 2 8 8 (spZ regs) (spZ (cx_regs0 cx) - STK_has_prefixed)
  (spZ (cx_regs0 cx) - 120) _ _ HFr ltac:(vm_compute; reflexivity) Usp ltac:(rewrite hp_stk; lia) ltac:(lia)) as G1.
clear HF HFr HG.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?ms1) =>
  hpn_rregU HS (1%bv : bv 5) NR1; hpn_rregU HS (10%bv : bv 5) NR10; hpn_rregU HS (11%bv : bv 5) NR11;
  hpn_rregU HS (12%bv : bv 5) NR12;
  pose proof (hpn_keep_run HP_KEEP E _ _ ms1 regs _ HS HAE ltac:(vm_compute; reflexivity)) as K1;
  pose proof (hpn_keep_run [21%bv; 18%bv; 22%bv] E _ _ ms1 regs _ HS HAE ltac:(vm_compute; reflexivity)) as K1b;
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms1 HS eq_refl); cbn [ss_pc];
  set (regs1 := ms_regs ms1) in *; set (m1 := ms_mem ms1) in *
end.
lazymatch goal with |- context [mkCfg _ ?d] => set (md1 := d) in * end.
(* the call's arguments: ra = 0x824b8, a0 = t + start, a1 = t + q, a2 = plen *)
assert (V1 : getr regs1 1 = Z_to_bv 64 HP_NCR) by (rewrite NR1, U_lit; reflexivity).
assert (V10 : getr regs1 10 = w64 (cx_t cx + Z.of_nat k)).
{ rewrite NR10, (U_atom_mod E 18 0 _ X18). unfold w64. f_equal. rewrite Z.add_0_r, Z.mod_small by lia. lia. }
assert (V11 : getr regs1 11 = w64 (cx_t cx + Z.of_nat (Z.to_nat (cx_q cx)))).
{ rewrite NR11, (U_atom_mod E 33 0 _ X33). unfold w64. f_equal. rewrite Z.add_0_r, Z.mod_small by lia. lia. }
assert (V12 : getr regs1 12 = w64 (cx_plen cx)).
{ rewrite NR12, (U_atom_mod E 9 0 _ X9). unfold w64. f_equal. rewrite Z.add_0_r, Z.mod_small by lia. reflexivity. }
clear NR1 NR10 NR11 NR12.
assert (H1 : hp_st B cx a lyc Sc W regs1 m1 md1)
  by exact (hp_st_keep B cx a lyc Sc W regs m mdc _ _ _ H HJ G1 K1 (K1b 21%bv ltac:(cbv; tauto))).
apply (hp_call_rt B cx a lyc Sc W regs1 m1 md1 STK_RT_STR PC_strncmp HP_NCR
  (fun v => v = 0 <-> strn_eq (Z.to_nat (cx_plen cx)) (skipn k (cx_tb cx)) (skipn (Z.to_nat (cx_q cx)) (cx_tb cx))) H1).
- unfold STK_RT_STR, ESTACK; lia.
- exact V1.
- unfold HP_NCR; lia.
- reflexivity.
- (* strncmp's contract: both strings are suffixes of the text, plen < 2 ^ 63 *)
  intros HPK. pose proof (hp_rom B IMGF cx a lyc Sc W regs1 m1 md1 H1) as (HN & HO).
  pose proof (hp_cstr B IMGF cx a lyc Sc W regs1 m1 md1 H1) as (Ht1 & _).
  exact (ASTRNCMP lyc Sc W regs1 m1 md1 _ _ _ _ _ HPK HN HO V10 V11 V12 ltac:(lia)
    (g2_cstr_suffix W m1 (cx_t cx) (cx_tb cx) k Hk Ht1)
    (g2_cstr_suffix W m1 (cx_t cx) (cx_tb cx) (Z.to_nat (cx_q cx)) Hqn Ht1)).
- (* 0x824b8: the return, bnez a0 *)
  intros regs2 m2 md2 v H2 HP2 Ha0 Hv HRv. cbv beta in HRv. destruct HRv as [HRv1 HRv2].
  pose proof (hp_seat B IMGF cx a lyc Sc W regs2 m2 md2 HP_NCR H2) as HS2.
  pose proof H2 as (_ & HJ2 & _).
  set (E2 := Ereg regs2 [w64 (Z.of_nat (length (cx_lb cx))); w64 (cx_t cx + cx_q cx)]) in HS2.
  assert (HAE2 : env_agree 32 (Ereg regs2 [w64 (Z.of_nat (length (cx_lb cx))); w64 (cx_t cx + cx_q cx)]) E2)
    by (split; [intros; reflexivity | reflexivity]).
  assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs2)
    by (unfold E2; rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl); reflexivity).
  assert (HspR2 : spZ regs2 = spZ (cx_regs0 cx) - 128)
    by (pose proof H2 as (_ & _ & _ & _ & _ & S2 & _); exact S2).
  assert (U10 : U E2 (SOff 10 0) = v).
  { rewrite (U_atom_mod E2 10 0 v); [rewrite Z.add_0_r; apply Z.mod_small; lia|].
    unfold E2. rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl). exact Ha0. }
  clear HS.
  unfold cfg_at. change (w64 HP_NCR) with (Z_to_bv 64 HP_NCR).
  srr_branch_with tbl_hp_ok HS2.
  + (* a0 <> 0: the prefix does not match -> tail *)
    lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
      rewrite branch_ne_U, U10, U_lit, Zmod_0_l in Hb; apply negb_true_iff, Z.eqb_neq in Hb; rename Hb into Hne end.
    aj_run_to tbl_hp_ok HS2 HJ2 HP_TAIL.
    { awr_ok_tac. }
    lazymatch type of HS2 with st_ok _ _ _ (restrict _ ?ms3) =>
      pose proof (gframe_of_frame tfibsegs W E2 _ 2 8 8 (spZ regs2) (spZ (cx_regs0 cx) - STK_has_prefixed)
        (spZ (cx_regs0 cx) - 120) _ _ HFr ltac:(vm_compute; reflexivity) Usp2 ltac:(rewrite hp_stk; lia) ltac:(lia))
        as G3;
      pose proof (hpn_keep_run HP_KEEP E2 _ _ ms3 regs2 _ HS2 HAE2 ltac:(vm_compute; reflexivity)) as K3;
      pose proof (hpn_keep_run [21%bv] E2 _ _ ms3 regs2 _ HS2 HAE2 ltac:(vm_compute; reflexivity)) as K3b;
      rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E2 _ ms3 HS2 eq_refl); cbn [ss_pc];
      set (regs3 := ms_regs ms3) in *; set (m3 := ms_mem ms3) in *
    end.
    apply (KT lyc Sc W regs3 m3 _).
    * exact (hp_st_keep B cx a lyc Sc W regs2 m2 md2 _ _ _ H2 HJ2 G3 K3 (K3b 21%bv (or_introl eq_refl))).
    * cbv beta. intros Hs. exact (Hne (HRv2 Hs)).
  + (* a0 = 0: the prefix matches -> the prefix segment, s2 / s6 kept across the call *)
    lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
      rewrite branch_ne_U, U10, U_lit, Zmod_0_l in Hb; apply negb_false_iff, Z.eqb_eq in Hb; rename Hb into Hv0 end.
    aj_run_to tbl_hp_ok HS2 HJ2 HP_PRE.
    { awr_ok_tac. }
    lazymatch type of HS2 with st_ok _ _ _ (restrict _ ?ms3) =>
      pose proof (gframe_of_frame tfibsegs W E2 _ 2 8 8 (spZ regs2) (spZ (cx_regs0 cx) - STK_has_prefixed)
        (spZ (cx_regs0 cx) - 120) _ _ HFr ltac:(vm_compute; reflexivity) Usp2 ltac:(rewrite hp_stk; lia) ltac:(lia))
        as G3;
      pose proof (hpn_keep_run HP_KEEP E2 _ _ ms3 regs2 _ HS2 HAE2 ltac:(vm_compute; reflexivity)) as K3;
      pose proof (hpn_keep_run [21%bv; 18%bv; 22%bv] E2 _ _ ms3 regs2 _ HS2 HAE2 ltac:(vm_compute; reflexivity)) as K3b;
      rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E2 _ ms3 HS2 eq_refl); cbn [ss_pc];
      set (regs3 := ms_regs ms3) in *; set (m3 := ms_mem ms3) in *
    end.
    apply (KP lyc Sc W regs3 m3 _).
    * exact (hp_st_keep B cx a lyc Sc W regs2 m2 md2 _ _ _ H2 HJ2 G3 K3 (K3b 21%bv ltac:(cbv; tauto))).
    * cbv beta. split; [|exact (HRv1 Hv0)]. split; [exact Ha|]. split.
      -- rewrite (K3b 18%bv ltac:(cbv; tauto)), (preserved_reg regs1 regs2 18%bv HP2 cs18),
           (K1b 18%bv ltac:(cbv; tauto)). exact R18.
      -- rewrite (K3b 22%bv ltac:(cbv; tauto)), (preserved_reg regs1 regs2 22%bv HP2 cs22),
           (K1b 22%bv ltac:(cbv; tauto)). exact R22.
Qed.
End s.
