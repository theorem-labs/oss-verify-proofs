(* has_prefixed (G2) loop segment pre: 0x821f0..0x8221c (lv2_locate.c:68-71), kit lib/A/FMW_hp_kit.v.
   start = a - plen - 1. `bgeu s3, s6` (t >= t + start) sends start = 0 to the location's end check (0x82220).
   Otherwise the byte start[-1] = t[a - plen - 2] is checked (0x821f8..0x82204) and loaded (0x82208), name_char runs
   on it (0x82210), and '.' (0x82218) or a name character (0x8221c) sends the walk to the loop tail (0x82240); any
   other byte goes on to 0x82220.
   The report site of this segment, `jal __asan_report_load1` at 0x82278 (slow path 0x82270: `andi a2, a0, 7`;
   `blt a2, a1, ->82208`), is REFUTED: the checked byte t[a - plen - 2] is a byte of the text, addressable by its
   cstr_ok (hp_shok), so the token engine discharges the check from the shadow entry and takes the fall-through. *)
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

(* the memory after a run from a seat whose regions are all read-only is the seat's memory *)
Ltac sgP_mem_as HF Em :=
  lazymatch type of HF with frame_of _ _ ?m0 ?m1 =>
    assert (Em : m1 = m0) by (eapply frame_of_read_only; [| exact HF]; vm_compute; reflexivity) end.
(* the goal's machine state in mkst form at the run's pc *)
Ltac sgP_mkst HS :=
  lazymatch goal with |- SRr _ ?W (mkCfg ?msx _) _ =>
    rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ msx HS eq_refl); cbn [ss_pc] end.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Hypothesis TL : TfibLib B.
Hypothesis IMGF : fm_img_facts tfibsegs B.
Hypothesis AISALNUM : aisalnum_realizes tfibsegs B PC_isalnum.

Lemma sgP_agree_refl : forall E, env_agree 32 E E.
Proof. intros E. split; [intros; reflexivity | reflexivity]. Qed.

(* the loop state after a run that wrote nothing and kept HP_KEEP and s5 *)
Lemma sgP_move : forall cx a lyc Sc W regs m mdc E ss ms md' extra,
  hp_st B cx a lyc Sc W regs m mdc ->
  st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  ajournal tfibsegs B STK_has_prefixed (spZ (cx_regs0 cx)) [] (cx_ly cx) (cx_S cx) (cx_W0 cx) (cx_mem cx) (cx_md cx)
    [] lyc Sc W (ms_mem ms) md' 0 ->
  env_agree 32 (Ereg regs extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) HP_KEEP = true ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) [21%bv] = true ->
  ms_mem ms = m ->
  hp_st B cx a lyc Sc W (ms_regs ms) (ms_mem ms) md'.
Proof.
intros cx a lyc Sc W regs m mdc E ss ms md' extra H HS HJ HA HK H21 Em.
pose proof H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q21 & _ & _ & _ & _ & Hmt & _).
apply (hp_st_move B cx a a lyc Sc W regs m mdc (ms_regs ms) (ms_mem ms) md' H HJ).
- rewrite Em. apply gframe_refl.
- exact (regs_keep_of_st_ok HP_KEEP E ss (restrict (w_H W) ms) regs extra HS HA HK).
- rewrite <- Q21. exact (regs_keep_of_st_ok [21%bv] E ss (restrict (w_H W) ms) regs extra HS HA H21 21%bv (or_introl eq_refl)).
- exact Hmt.
Qed.

(* a register whose value v reads back as c *)
Lemma sgP_byte : forall E ss ms r v c, st_ok tfibsegs E ss ms -> sr_get (ss_regs ss) r = v -> U E v = c ->
  getr (ms_regs ms) r = w64 c.
Proof.
intros E ss ms r v c HS Hr HU. rewrite (st_ok_reg tfibsegs E ss ms r HS), Hr, denot_lit_U, HU. reflexivity.
Qed.
(* the zero-extended checked byte (atom 32 = c), as lbu leaves it, and after `mv` *)
Lemma sgP_U_byte : forall E c, ew E 32 = w64 c -> 0 <= c < 256 -> U E (SExt false 8 (SOff 32 0)) = c.
Proof.
intros E c H32 Hc. rewrite U_zext, (U_atom E 32 c H32) by lia.
change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia.
Qed.
Lemma sgP_U_byte0 : forall E c, ew E 32 = w64 c -> 0 <= c < 256 ->
  U E (SAlu ALU_ADD (SExt false 8 (SOff 32 0)) (SLit 0)) = c.
Proof.
intros E c H32 Hc. rewrite U_add2, (sgP_U_byte E c H32 Hc), U_SLit. change (zcanon 0) with 0.
rewrite Z.add_0_r. apply Z.mod_small. lia.
Qed.

Lemma hp_seg_pre : seg_pre_ok B.
Proof.
unfold seg_pre_ok. intros cx a KT KN lyc Sc W regs m mdc Hst H69.
pose proof g2_segs_low as Hsegs. pose proof g2_wx as Hwx.
destruct H69 as (Ha & Q22 & Q25).
pose proof Hst as (HE & _ & _ & _ & _ & _ & _ & _ & Q9 & _ & Q19 & _ & Q21 & _ & _ & _ & _ & Hmt & _).
pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & Hq & Hplen & Hqp & _).
pose proof (has_prefixed_model.mt_len _ _ _ Hmt) as Hlen.
pose proof (proj1 (hp_cstr B IMGF cx a lyc Sc W regs m mdc Hst)) as Htc.
pose proof Htc as (_ & Ht4096 & Htcl & _).
ceil2.
assert (HP : Z.of_nat (Z.to_nat (cx_plen cx)) = cx_plen cx) by (apply Z2Nat.id; lia).
assert (E19 : ew (Ereg regs []) 19 = Z_to_bv 64 (cx_t cx))
  by (rewrite (ew_Ereg_nat regs [] 19 19%bv eq_refl); exact Q19).
assert (E22 : ew (Ereg regs []) 22 = Z_to_bv 64 (cx_t cx + Z.of_nat a - cx_plen cx - 1))
  by (rewrite (ew_Ereg_nat regs [] 22 22%bv eq_refl); exact Q22).
assert (E25 : ew (Ereg regs []) 25 = Z_to_bv 64 (cx_t cx + Z.of_nat a - cx_plen cx))
  by (rewrite (ew_Ereg_nat regs [] 25 25%bv eq_refl); exact Q25).
pose proof (hp_seat B cx a lyc Sc W regs m mdc HP_PRE Hst) as HS.
pose proof Hst as (_ & HJ & _).
unfold cfg_at. change (w64 HP_PRE) with (Z_to_bv 64 HP_PRE).
(* 0x821f0: bgeu s3, s6 *)
srr_branch_with tbl_hp_ok HS.
- (* t >= t + start: start = 0, on to 0x82220 *)
  rewrite branch_geu_U, (U_atom _ 19 _ E19), (U_atom _ 22 _ E22) in Hc by lia.
  apply negb_true_iff, Z.ltb_ge in Hc.
  aj_run_to tbl_hp_ok HS HJ HP_POST.
  { apply awr_ok_nil. }
  sgP_mem_as HF Em.
  pose proof (sgP_move cx a lyc Sc W regs m mdc _ _ _ _ [] Hst HS HJ (sgP_agree_refl _)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Em) as Hst1.
  sgP_mkst HS.
  refine (KN _ _ _ _ _ _ Hst1 _).
  left. lia.
- (* start > 0: check and load start[-1] = t[a - plen - 2] *)
  rewrite branch_geu_U, (U_atom _ 19 _ E19), (U_atom _ 22 _ E22) in Hc by lia.
  apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hpos.
  assert (Ei' : exists i, i = (a - Z.to_nat (cx_plen cx) - 2)%nat) by eauto. destruct Ei' as (i & Ei).
  assert (Hi : (i <= length (cx_tb cx))%nat) by lia.
  assert (Hiz : Z.of_nat i = Z.of_nat a - cx_plen cx - 2) by lia.
  (* 0x821f0..0x821f4: a0 = s9 - 2 = t + i *)
  aj_run_to tbl_hp_ok HS HJ 0x821f8.
  { apply awr_ok_nil. }
  sgP_mem_as HF Em.
  pose proof (sgP_move cx a lyc Sc W regs m mdc _ _ _ _ [] Hst HS HJ (sgP_agree_refl _)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Em) as Hst1.
  rreg HS (10%bv : bv 5) R10.
  assert (H10 : getr (ms_regs ms) 10 = w64 (cx_t cx + Z.of_nat i)).
  { rewrite R10, E25, unsigned_lit_small by lia. unfold w64. f_equal. lia. }
  sgP_mkst HS.
  clear HS HJ HF HFr HG R10 Em.
  pose proof (hp_tbyte B IMGF cx a lyc Sc W _ _ _ i Hst1 Hi) as (Hv & Hc8).
  assert (Ec' : exists c, c = ManifestModel.byte_at (cx_tb cx) i) by eauto. destruct Ec' as (c & Ec).
  rewrite <- Ec in Hv, Hc8.
  pose proof (hp_seat_chk B cx a lyc Sc W _ _ _ 0x821f8 (cx_t cx + Z.of_nat i) c Hst1 H10 ltac:(lia) Hv Hc8) as HS.
  pose proof (hp_shok B IMGF cx a lyc Sc W _ _ _ c i Hst1 H10 Hi) as SHOK.
  pose proof Hst1 as (_ & HJ & _).
  (* 0x821f8..0x82210: the shadow check of t + i (its report 0x82278 refuted), s6 = a0 = t[i], call name_char *)
  aj_run_tok tbl_hp_ok HS HJ SHOK hp_Bspan.
  { apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  sgP_mem_as HF Em.
  pose proof (sgP_move cx a lyc Sc W (ms_regs ms) (ms_mem ms) _ _ _ _ _ [w64 c] Hst1 HS HJ
    ltac:(env_agree_chain (sgP_agree_refl (Ereg (ms_regs ms) [w64 c])))
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Em) as Hst2.
  lazymatch type of HS with st_ok _ ?E _ _ =>
    assert (X32 : ew E 32 = w64 c)
      by (rewrite ?ew_ewset_other by lia; exact (ew_Ereg_extra (ms_regs ms) [w64 c] 0)) end.
  pose proof (sgP_byte _ _ _ (10%bv : bv 5) (SAlu ALU_ADD (SExt false 8 (SOff 32 0)) (SLit 0)) c HS
    ltac:(vm_compute; reflexivity) (sgP_U_byte0 _ c X32 Hc8)) as R10.
  pose proof (sgP_byte _ _ _ (22%bv : bv 5) (SExt false 8 (SOff 32 0)) c HS
    ltac:(vm_compute; reflexivity) (sgP_U_byte _ c X32 Hc8)) as R22.
  cbn [ms_regs restrict] in R10, R22.
  rreg HS (1%bv : bv 5) R1.
  sgP_mkst HS.
  clear HS SHOK HJ HF HFr HG X32 Em.
  apply (hp_call_nc B IMGF AISALNUM cx a lyc Sc W _ _ _ 0x82214 c Hst2 R1 ltac:(lia) eq_refl R10 Hc8).
  intros ly2 S2 W2 regs2 m2 md2 Hst4 HP4 H10n.
  assert (Q22' : getr regs2 22 = w64 c).
  { rewrite <- R22. replace (22%bv : bv 5) with (Z_to_bv 5 22) by (apply bv_eq; reflexivity).
    apply HP4. unfold acallee_saved. lia. }
  assert (F22 : ew (Ereg regs2 []) 22 = Z_to_bv 64 c)
    by (rewrite (ew_Ereg_nat regs2 [] 22 22%bv eq_refl); exact Q22').
  assert (F10 : ew (Ereg regs2 []) 10 = Z_to_bv 64 (if ManifestModel.name_char c then 1 else 0))
    by (rewrite (ew_Ereg_nat regs2 [] 10 10%bv eq_refl); exact H10n).
  pose proof (hp_seat B cx a ly2 S2 W2 regs2 m2 md2 0x82214 Hst4) as HS.
  pose proof Hst4 as (_ & HJ & _).
  unfold cfg_at. change (w64 0x82214) with (Z_to_bv 64 0x82214).
  (* 0x82214: li a1, 46; 0x82218: beq s6, a1 *)
  aj_run tbl_hp_ok HS HJ.
  { apply awr_ok_nil. }
  sgP_mem_as HF Em1. clear HF HFr HG.
  srr_branch_with tbl_hp_ok HS.
  + (* c = '.': tail *)
    rewrite branch_eq_U, (U_atom _ 22 _ F22), U_SLit in Hc by lia. change (zcanon 46) with 46 in Hc.
    apply Z.eqb_eq in Hc.
    aj_run_to tbl_hp_ok HS HJ HP_TAIL.
    { apply awr_ok_nil. }
    sgP_mem_as HF Em.
    pose proof (sgP_move cx a ly2 S2 W2 regs2 m2 md2 _ _ _ _ [] Hst4 HS HJ (sgP_agree_refl _)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (eq_trans Em Em1)) as Hst5.
    sgP_mkst HS.
    refine (KT _ _ _ _ _ _ Hst5 _).
    split; [lia|]. left. rewrite <- Ei, <- Ec. exact Hc.
  + rewrite branch_eq_U, (U_atom _ 22 _ F22), U_SLit in Hc by lia. change (zcanon 46) with 46 in Hc.
    apply Z.eqb_neq in Hc. rename Hc into H46.
    (* 0x8221c: bnez a0 (name_char c) *)
    aj_run tbl_hp_ok HS HJ.
    { apply awr_ok_nil. }
    sgP_mem_as HF Em. pose proof (eq_trans Em Em1) as Em2. clear HF HFr HG Em.
    srr_branch_with tbl_hp_ok HS.
    * (* name_char c: tail *)
      rewrite branch_ne_U, (U_atom _ 10 _ F10), U_SLit in Hc by (destruct (ManifestModel.name_char c); lia).
      change (zcanon 0) with 0 in Hc.
      assert (HNC : ManifestModel.name_char c = true)
        by (revert Hc; destruct (ManifestModel.name_char c); cbn; intros Hc; [reflexivity | discriminate Hc]).
      aj_run_to tbl_hp_ok HS HJ HP_TAIL.
      { apply awr_ok_nil. }
      sgP_mem_as HF Em.
      pose proof (sgP_move cx a ly2 S2 W2 regs2 m2 md2 _ _ _ _ [] Hst4 HS HJ (sgP_agree_refl _)
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (eq_trans Em Em2)) as Hst5.
      sgP_mkst HS.
      refine (KT _ _ _ _ _ _ Hst5 _).
      split; [lia|]. right. rewrite <- Ei, <- Ec. exact HNC.
    * (* neither: on to 0x82220 *)
      rewrite branch_ne_U, (U_atom _ 10 _ F10), U_SLit in Hc by (destruct (ManifestModel.name_char c); lia).
      change (zcanon 0) with 0 in Hc.
      assert (HNC : ManifestModel.name_char c = false)
        by (revert Hc; destruct (ManifestModel.name_char c); cbn; intros Hc; [discriminate Hc | reflexivity]).
      aj_run_to tbl_hp_ok HS HJ HP_POST.
      { apply awr_ok_nil. }
      sgP_mem_as HF Em.
      pose proof (sgP_move cx a ly2 S2 W2 regs2 m2 md2 _ _ _ _ [] Hst4 HS HJ (sgP_agree_refl _)
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (eq_trans Em Em2)) as Hst5.
      sgP_mkst HS.
      refine (KN _ _ _ _ _ _ Hst5 _).
      right. split; [lia|]. rewrite <- Ei, <- Ec. split; [exact H46 | exact HNC].
Qed.
End s.
