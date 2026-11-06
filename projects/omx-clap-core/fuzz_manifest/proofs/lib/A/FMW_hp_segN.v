(* has_prefixed (G2) loop segment ncmp: 0x821dc..0x821ec, kit lib/A/FMW_hp_kit.v. strncmp (start, t + q, plen)
   (0x821e8, lv2_locate.c:65) through the runtime contract ASTRNCMP (hp_call_rt), then `bnez a0` (0x821ec): a nonzero
   answer goes to the loop tail 0x82240, a zero answer to the prefix-matched point 0x821f0. The segment holds no inline
   ASan check (no report site). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI04 YN3v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YA0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC20 YI16 YI00 YM05 YG0q YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_g2rt FMW_name_char FMW_hp_kit FMW_hp_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel has_prefixed_model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Hypothesis TL : TfibLib B.
Hypothesis IMGF : fm_img_facts tfibsegs B.
Hypothesis ASTRNCMP : astrncmp_realizes tfibsegs B PC_strncmp.

(* 0x821ec: back from strncmp with a0 = v, `bnez a0`; v <> 0 -> tail 0x82240, v = 0 -> 0x821f0 *)
Lemma sgN_ret : forall cx a (P : Prop) lyc Sc W regs m mdc v,
  hp_cont B cx HP_TAIL a (fun _ => ~ P) ->
  hp_cont B cx HP_PRE a (fun r => hp_s69 cx a r /\ P) ->
  hp_st B cx a lyc Sc W regs m mdc -> hp_s69 cx a regs ->
  getr regs 10 = w64 v -> 0 <= v < 2 ^ 64 -> (v = 0 <-> P) ->
  SRr tfibsegs W (cfg_at tfibsegs 0x821ec regs m mdc) (hp_post B cx).
Proof.
intros cx a P lyc Sc W regs m mdc v KT KN Hst H69 H10 Hv HR.
pose proof g2_segs_low as Hsegs. pose proof g2_wx as Hwx.
pose proof Hst as (_ & HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q21 & _ & _ & _ & _ & Hmt & _).
pose proof (hp_seat B cx a lyc Sc W regs m mdc 0x821ec Hst) as HS.
set (E := Ereg regs []) in HS.
assert (HAE : env_agree 32 (Ereg regs []) E) by (split; [intros; reflexivity | reflexivity]).
assert (E10 : ew E 10 = getr regs 10) by exact (ew_Ereg_nat regs _ 10 10%bv eq_refl).
assert (U10 : U E (SOff 10 0) = v) by (apply (U_atom E 10 v); [rewrite E10; exact H10 | exact Hv]).
unfold cfg_at. change (w64 0x821ec) with (Z_to_bv 64 0x821ec).
srr_branch_with tbl_hp_ok HS.
- (* v <> 0: the prefix differs, on to the loop tail *)
  rewrite branch_ne_U, U10, U_SLit in Hc. change (zcanon 0) with 0 in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  aj_run_to tbl_hp_ok HS HJ HP_TAIL.
  { apply awr_ok_nil. }
  assert (Em : ms_mem ms = m) by (eapply frame_of_read_only; [|exact HF]; reflexivity).
  clear HF HFr HG.
  assert (HK : regs_keep HP_KEEP regs (ms_regs ms)).
  { eapply (regs_keep_of_st_ok HP_KEEP E _ _ regs [] HS HAE). vm_compute. reflexivity. }
  assert (HK' : regs_keep ([21; 22; 25]%bv : list (bv 5)) regs (ms_regs ms)).
  { eapply (regs_keep_of_st_ok _ E _ _ regs [] HS HAE). vm_compute. reflexivity. }
  assert (K' : forall r, In r ([21; 22; 25]%bv : list (bv 5)) -> getr (ms_regs ms) r = getr regs r) by exact HK'.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
    rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ msx HS eq_refl); cbn [ss_pc];
    set (MD := mdx) in * end.
  assert (Hst' : hp_st B cx a lyc Sc W (ms_regs ms) (ms_mem ms) MD).
  { apply (hp_st_move B cx a a lyc Sc W regs m mdc (ms_regs ms) (ms_mem ms) MD Hst HJ);
      [rewrite Em; apply gframe_refl | exact HK | | exact Hmt].
    rewrite K' by (cbv; tauto). exact Q21. }
  exact (KT lyc Sc W (ms_regs ms) (ms_mem ms) MD Hst' (fun HP => Hc (proj2 HR HP))).
- (* v = 0: the prefix matches, on to 0x821f0 *)
  rewrite branch_ne_U, U10, U_SLit in Hc. change (zcanon 0) with 0 in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc.
  aj_run_to tbl_hp_ok HS HJ HP_PRE.
  { apply awr_ok_nil. }
  assert (Em : ms_mem ms = m) by (eapply frame_of_read_only; [|exact HF]; reflexivity).
  clear HF HFr HG.
  assert (HK : regs_keep HP_KEEP regs (ms_regs ms)).
  { eapply (regs_keep_of_st_ok HP_KEEP E _ _ regs [] HS HAE). vm_compute. reflexivity. }
  assert (HK' : regs_keep ([21; 22; 25]%bv : list (bv 5)) regs (ms_regs ms)).
  { eapply (regs_keep_of_st_ok _ E _ _ regs [] HS HAE). vm_compute. reflexivity. }
  assert (K' : forall r, In r ([21; 22; 25]%bv : list (bv 5)) -> getr (ms_regs ms) r = getr regs r) by exact HK'.
  lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
    rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ msx HS eq_refl); cbn [ss_pc];
    set (MD := mdx) in * end.
  assert (Hst' : hp_st B cx a lyc Sc W (ms_regs ms) (ms_mem ms) MD).
  { apply (hp_st_move B cx a a lyc Sc W regs m mdc (ms_regs ms) (ms_mem ms) MD Hst HJ);
      [rewrite Em; apply gframe_refl | exact HK | | exact Hmt].
    rewrite K' by (cbv; tauto). exact Q21. }
  assert (H69' : hp_s69 cx a (ms_regs ms)).
  { destruct H69 as (H1 & H22 & H25). split; [exact H1|].
    split; rewrite K' by (cbv; tauto); assumption. }
  exact (KN lyc Sc W (ms_regs ms) (ms_mem ms) MD Hst' (conj H69' (proj1 HR Hc))).
Qed.

Lemma hp_seg_ncmp : seg_ncmp_ok B.
Proof.
intros cx a KT KN lyc Sc W regs m mdc Hst H69.
pose proof g2_segs_low as Hsegs. pose proof g2_wx as Hwx.
pose proof Hst as (HE & HJ & _ & _ & _ & _ & _ & _ & Q9 & Q18 & _ & _ & Q21 & _ & _ & _ & _ & Hmt & _).
pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & Hq & Hplen & Hqp & Hmax & _).
unfold MANIFEST_MAX in Hmax.
pose proof (has_prefixed_model.mt_len _ _ _ Hmt) as Hlen.
pose proof H69 as (Ha & Q22 & _).
pose proof (hp_seat B cx a lyc Sc W regs m mdc 0x821dc Hst) as HS.
set (E := Ereg regs []) in HS.
assert (HAE : env_agree 32 (Ereg regs []) E) by (split; [intros; reflexivity | reflexivity]).
assert (E9 : ew E 9 = getr regs 9) by exact (ew_Ereg_nat regs _ 9 9%bv eq_refl).
assert (E18 : ew E 18 = getr regs 18) by exact (ew_Ereg_nat regs _ 18 18%bv eq_refl).
assert (E22 : ew E 22 = getr regs 22) by exact (ew_Ereg_nat regs _ 22 22%bv eq_refl).
unfold cfg_at, HP_NCMP. change (w64 0x821dc) with (Z_to_bv 64 0x821dc).
(* 0x821dc..0x821e8: a0 = s6 = t + start, a1 = s2 = t + q, a2 = s1 = plen, `jal strncmp` (ra = 0x821ec) *)
aj_run tbl_hp_ok HS HJ.
{ apply awr_ok_nil. }
assert (Em : ms_mem ms = m) by (eapply frame_of_read_only; [|exact HF]; reflexivity).
clear HF HFr HG.
assert (HK : regs_keep HP_KEEP regs (ms_regs ms)).
{ eapply (regs_keep_of_st_ok HP_KEEP E _ _ regs [] HS HAE). vm_compute. reflexivity. }
assert (HK' : regs_keep ([21; 22; 25]%bv : list (bv 5)) regs (ms_regs ms)).
{ eapply (regs_keep_of_st_ok _ E _ _ regs [] HS HAE). vm_compute. reflexivity. }
assert (K' : forall r, In r ([21; 22; 25]%bv : list (bv 5)) -> getr (ms_regs ms) r = getr regs r) by exact HK'.
rreg HS (1%bv : bv 5) R1. rreg HS (10%bv : bv 5) R10. rreg HS (11%bv : bv 5) R11. rreg HS (12%bv : bv 5) R12.
lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ msx HS eq_refl); cbn [ss_pc];
  set (MD := mdx) in * end.
assert (Hst1 : hp_st B cx a lyc Sc W (ms_regs ms) (ms_mem ms) MD).
{ apply (hp_st_move B cx a a lyc Sc W regs m mdc (ms_regs ms) (ms_mem ms) MD Hst HJ);
    [rewrite Em; apply gframe_refl | exact HK | | exact Hmt].
  rewrite K' by (cbv; tauto). exact Q21. }
(* the call: strncmp (t + start, t + q, plen) with start = a - plen - 1 *)
apply (hp_call_rt B cx a lyc Sc W (ms_regs ms) (ms_mem ms) MD STK_RT_STR PC_strncmp 0x821ec
  (fun v => v = 0 <-> strn_eq (Z.to_nat (cx_plen cx)) (skipn (a - Z.to_nat (cx_plen cx) - 1) (cx_tb cx))
                                (skipn (Z.to_nat (cx_q cx)) (cx_tb cx))) Hst1).
- unfold STK_RT_STR, ESTACK. lia.
- exact R1.
- lia.
- reflexivity.
- intros HPK.
  destruct (hp_rom B IMGF cx a lyc Sc W (ms_regs ms) (ms_mem ms) MD Hst1) as (HN & HO).
  destruct (hp_cstr B IMGF cx a lyc Sc W (ms_regs ms) (ms_mem ms) MD Hst1) as (Ht & _).
  apply (ASTRNCMP lyc Sc W (ms_regs ms) (ms_mem ms) MD
    (cx_t cx + Z.of_nat (a - Z.to_nat (cx_plen cx) - 1)) (cx_t cx + Z.of_nat (Z.to_nat (cx_q cx))) (cx_plen cx)
    _ _ HPK HN HO).
  + rewrite R10, E22, Q22. f_equal. lia.
  + rewrite R11, E18, Q18. f_equal. lia.
  + rewrite R12, E9. exact Q9.
  + lia.
  + apply g2_cstr_suffix; [lia | exact Ht].
  + apply g2_cstr_suffix; [lia | exact Ht].
- (* back at 0x821ec: s6/s9 are callee-saved across strncmp *)
  intros regs2 m2 md2 v Hst2 HP2 Ha0 Hv HRv. cbv beta in HRv.
  apply (sgN_ret cx a _ lyc Sc W regs2 m2 md2 v KT KN Hst2); [| exact Ha0 | exact Hv | exact HRv].
  assert (P22 : getr regs2 22 = getr (ms_regs ms) 22).
  { replace (22%bv : bv 5) with (Z_to_bv 5 22) by (apply bv_eq; reflexivity). apply HP2. unfold acallee_saved. lia. }
  assert (P25 : getr regs2 25 = getr (ms_regs ms) 25).
  { replace (25%bv : bv 5) with (Z_to_bv 5 25) by (apply bv_eq; reflexivity). apply HP2. unfold acallee_saved. lia. }
  destruct H69 as (H1 & H22 & H25). split; [exact H1|].
  split; [rewrite P22, K' by (cbv; tauto); exact H22 | rewrite P25, K' by (cbv; tauto); exact H25].
Qed.

End s.
