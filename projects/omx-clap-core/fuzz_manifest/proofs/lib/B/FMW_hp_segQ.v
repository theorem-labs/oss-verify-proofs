(* has_prefixed on fm.asan-ubsan (G2, image B), loop segment POST 0x824f0..0x8251c (lv2_locate.c:71-73): the byte
   after the location occurrence at = t + a. The UBSan pointer-overflow guard of `at + |location|` (0x824f8
   bltu ~at, |location|; trap `unimp` 0x825a0) is shown not taken inline with B5's fm_kill_trap (lib/B/FMTrapB.v,
   FM-B-TRAPS.md row 7, class K2 fmt_not_ltu_not: t + a + |location| < 2 ^ 64); the ASan check of at[|location|]
   (0x82504..0x82510, slow path 0x82548, report 0x825a8) runs on the token engine; name_char (at[|location|]) is
   called at 0x82518 (kit hp_call_nc); its answer 0 -> return 1 (0x82560, epilogue 0x82564), else the loop tail.
   Proves the kit's seg_post_ok (lib/B/FMW_hp_kit.v). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require FMTrapB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel has_prefixed_model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- reading the engine's terms back as Z ---- *)
Lemma sv_denot_U : forall E e, sv_denot E e = Z_to_bv 64 (U E e).
Proof. intros E e. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma mod_small_eq : forall x y, x = y -> 0 <= y < 2 ^ 64 -> x mod 2 ^ 64 = y.
Proof. intros x y -> H. apply Z.mod_small. exact H. Qed.

(* the pc of a state after a branch (add_cond ...) as a literal *)
Ltac pcnorm := repeat lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?s)] =>
  let p := eval vm_compute in (ss_pc s) in change (ss_pc s) with p end.
(* getr of the register r after a run, as Z_to_bv 64 (U E e) *)
Ltac rregU HS r Hr :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    assert (Hr : getr (ms_regs ms) r = Z_to_bv 64 (U E e))
      by (rewrite <- sv_denot_U; exact (st_ok_restrict_reg segs H E ss ms r HS))
  end.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Hypothesis HGOTS : as_got_shadow B = HP_GOT_shadow.
Hypothesis HCELL : as_shadow_cell B = HP_shadow_cell.
Hypothesis IMGF : fm_img_facts tfibsegs B.
Hypothesis NC : name_char_spec tfibsegs B.

Lemma keep_run : forall L E ss H ms regs0 extra,
  st_ok tfibsegs E ss (restrict H ms) -> env_agree 32 (Ereg regs0 extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) L = true ->
  regs_keep L regs0 (ms_regs ms).
Proof. intros L E ss H ms regs0 extra HS HA Hc. exact (regs_keep_of_st_ok L E ss (restrict H ms) regs0 extra HS HA Hc). Qed.

Lemma seg_post : seg_post_ok B.
Proof.
intros cx a HRES KT lyc Sc W regs m mdc H _.
pose proof g2_segs_low as Hsegs. pose proof g2_wx as Hwx.
pose proof (hp_sp B cx a lyc Sc W regs m mdc H) as (Hsp1 & Hsp2 & Hspc).
pose proof (hp_cstr B IMGF cx a lyc Sc W regs m mdc H) as (Ht & _).
pose proof Ht as (_ & Ht4 & Htc & _).
pose proof H as (_ & HJ & _ & _ & _ & Hsp & _ & _ & _ & _ & _ & _ & Q21 & _ & _ & _ & _ & _ & Hmt & _).
pose proof (has_prefixed_model.mt_len _ _ _ Hmt) as Halen.
ceil2.
pose proof (hp_seat B IMGF cx a lyc Sc W regs m mdc HP_POST H) as HS.
set (E := Ereg regs [w64 (Z.of_nat (length (cx_lb cx))); w64 (cx_t cx + cx_q cx)]) in HS.
assert (HAE : env_agree 32 (Ereg regs [w64 (Z.of_nat (length (cx_lb cx))); w64 (cx_t cx + cx_q cx)]) E)
  by (split; [intros; reflexivity | reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (X21 : ew E 21 = Z_to_bv 64 (cx_t cx + Z.of_nat a))
  by (unfold E; rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact Q21).
assert (X32 : ew E 32 = Z_to_bv 64 (Z.of_nat (length (cx_lb cx)))) by exact (ew_Ereg_extra regs _ 0).
assert (U21 : U E (SOff 21 0) = cx_t cx + Z.of_nat a) by (apply (U_atom E 21); [exact X21 | lia]).
assert (U32 : U E (SOff 32 0) = Z.of_nat (length (cx_lb cx))) by (apply (U_atom E 32); [exact X32 | lia]).
unfold cfg_at. change (w64 HP_POST) with (Z_to_bv 64 HP_POST).
(* 0x824f0..0x824f8: a0 = ~at, a1 = |location| (sp + 8); UBSan guard bltu a0, a1 *)
aj_run tbl_hp_ok HS HJ.
{ awr_ok_tac. }
pose proof (gframe_of_frame tfibsegs W E _ 2 8 8 (spZ regs) (spZ (cx_regs0 cx) - STK_has_prefixed)
  (spZ (cx_regs0 cx) - 120) m _ HFr ltac:(vm_compute; reflexivity) Usp ltac:(rewrite hp_stk; lia) ltac:(lia)) as G1.
clear HF HFr HG.
srr_branch_with tbl_hp_ok HS.
{ (* UBSan guard 0x824f8 (FM-B-TRAPS.md row 7, K2 fmt_not_ltu_not): ~at <u |location| needs
     U at + U |location| >= 2 ^ 64, but at + |location| <= t + |text| < alloc_ceiling < 2 ^ 47 *)
  FMTrapB.fm_kill_trap Hc. }
clear Hc.
(* 0x824fc..0x82500: a0 = at + |location|; stop at the check *)
aj_run_to tbl_hp_ok HS HJ HP_C3.
{ awr_ok_tac. }
pose proof (gframe_of_frame tfibsegs W E _ 2 8 8 (spZ regs) (spZ (cx_regs0 cx) - STK_has_prefixed)
  (spZ (cx_regs0 cx) - 120) _ _ HFr ltac:(vm_compute; reflexivity) Usp ltac:(rewrite hp_stk; lia) ltac:(lia)) as G2.
clear HF HFr HG.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?ms2) =>
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms2 HS eq_refl); cbn [ss_pc]; pcnorm;
  pose proof (keep_run HP_KEEP E _ _ ms2 regs _ HS HAE ltac:(vm_compute; reflexivity)) as K2;
  pose proof (keep_run [21%bv] E _ _ ms2 regs _ HS HAE ltac:(vm_compute; reflexivity)) as K21;
  rregU HS (10%bv : bv 5) R10;
  set (regs2 := ms_regs ms2) in *; set (m2 := ms_mem ms2) in *
end.
lazymatch goal with |- context [mkCfg _ ?d] => set (md2 := d) in * end.
assert (G : gframe tfibsegs W (spZ (cx_regs0 cx) - STK_has_prefixed) (spZ (cx_regs0 cx) - 120) m m2)
  by (eapply (gframe_seq tfibsegs W _ _ m _ m2); [exact G1 | exact G2]).
assert (H2 : hp_st B cx a lyc Sc W regs2 m2 md2)
  by exact (hp_st_keep B cx a lyc Sc W regs m mdc _ _ _ H HJ G K2 (K21 21%bv (or_introl eq_refl))).
assert (V10 : getr regs2 10 = w64 (cx_t cx + Z.of_nat (a + length (cx_lb cx)))).
{ rewrite R10. unfold w64. f_equal. rewrite U_add2, U21, U32. apply mod_small_eq; lia. }
clear R10 G1 G2 G K2 K21.
(* 0x82504..0x82518: the ASan check of at[|location|] (index a + |location| <= |text| by mt_len), c = that byte,
   jal name_char (c) *)
pose proof (hp_tbyte B IMGF cx a lyc Sc W regs2 m2 md2 (a + length (cx_lb cx)) H2 Halen) as (Vc & Rc).
set (c := ManifestModel.byte_at (cx_tb cx) (a + length (cx_lb cx))) in *.
pose proof (hp_seat_chk B cx a lyc Sc W regs2 m2 md2 HP_C3 (cx_t cx + Z.of_nat (a + length (cx_lb cx))) c H2 V10
  ltac:(lia) Vc Rc) as HS2.
pose proof (hp_shok B IMGF cx a lyc Sc W regs2 m2 md2 c (a + length (cx_lb cx)) H2 V10 Halen) as SHOK.
pose proof H2 as (_ & HJ2 & _).
clear HS. rename HS2 into HS.
set (E2 := Ereg regs2 [w64 c]) in HS, SHOK.
assert (HAE2 : env_agree 32 (Ereg regs2 [w64 c]) E2) by (split; [intros; reflexivity | reflexivity]).
assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs2)
  by (unfold E2; rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl); reflexivity).
assert (Hspr2 : spZ regs2 = spZ (cx_regs0 cx) - 128) by (pose proof H2 as (_ & _ & _ & _ & _ & S5 & _); exact S5).
change m2 with (ms_mem (mkst regs2 (Z_to_bv 64 HP_C3) m2 (seg_rom tfibsegs))) in HJ2.
aj_run_tok tbl_hp_ok HS HJ2 SHOK hp_Bspan.
{ awr_ok_tac. }
pose proof (gframe_of_frame tfibsegs W E2 _ 2 8 8 (spZ regs2) (spZ (cx_regs0 cx) - STK_has_prefixed)
  (spZ (cx_regs0 cx) - 120) _ _ HFr ltac:(vm_compute; reflexivity) Usp2 ltac:(rewrite hp_stk; lia) ltac:(lia)) as G3.
clear HF HFr HG.
lazymatch type of HS with st_ok _ ?Ex _ _ => set (E3 := Ex) in * end.
assert (HAE3 : env_agree 32 (Ereg regs2 [w64 c]) E3) by (unfold E3; env_agree_chain HAE2).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?ms3) =>
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E3 _ ms3 HS eq_refl); cbn [ss_pc]; pcnorm;
  pose proof (keep_run HP_KEEP E3 _ _ ms3 regs2 _ HS HAE3 ltac:(vm_compute; reflexivity)) as K3;
  pose proof (keep_run [21%bv] E3 _ _ ms3 regs2 _ HS HAE3 ltac:(vm_compute; reflexivity)) as K21;
  rregU HS (1%bv : bv 5) R1; rregU HS (10%bv : bv 5) R10;
  set (regs3 := ms_regs ms3) in *; set (m3 := ms_mem ms3) in *
end.
lazymatch goal with |- context [mkCfg _ ?d] => set (md3 := d) in * end.
assert (X32c : ew E3 32 = Z_to_bv 64 c)
  by (unfold E3; rewrite !ew_ewset_other by lia; unfold E2; exact (ew_Ereg_extra regs2 _ 0)).
assert (V1 : getr regs3 1 = Z_to_bv 64 HP_QNR) by (rewrite R1, U_lit; reflexivity).
assert (V10c : getr regs3 10 = w64 c).
{ rewrite R10. unfold w64. f_equal. rewrite U_SExt, (U_atom E3 32 c X32c) by lia. change (2 ^ Z.of_N 8) with (2 ^ 8).
  rewrite Z.mod_small by lia. apply zcanon_id. unfold M64. lia. }
assert (H3 : hp_st B cx a lyc Sc W regs3 m3 md3)
  by exact (hp_st_keep B cx a lyc Sc W regs2 m2 md2 _ _ _ H2 HJ2 G3 K3 (K21 21%bv (or_introl eq_refl))).
clear R1 R10 K3 K21 G3.
(* name_char (c) returns to 0x8251c with a0 = name_char c *)
apply (hp_call_nc B IMGF NC cx a lyc Sc W regs3 m3 md3 HP_QNR c H3 V1 ltac:(unfold HP_QNR; lia) ltac:(reflexivity)
  V10c Rc).
intros ly4 S4 W4 regs4 m4 md4 H4 _ R10r.
pose proof (hp_sp B cx a ly4 S4 W4 regs4 m4 md4 H4) as (Hsp41 & Hsp42 & Hsp4c).
pose proof H4 as (_ & HJ4 & _ & _ & _ & Hsp4 & _).
pose proof (hp_seat B IMGF cx a ly4 S4 W4 regs4 m4 md4 HP_QNR H4) as HS4.
set (E4 := Ereg regs4 [w64 (Z.of_nat (length (cx_lb cx))); w64 (cx_t cx + cx_q cx)]) in HS4.
assert (HAE4 : env_agree 32 (Ereg regs4 [w64 (Z.of_nat (length (cx_lb cx))); w64 (cx_t cx + cx_q cx)]) E4)
  by (split; [intros; reflexivity | reflexivity]).
assert (Usp4 : bv_unsigned (ew E4 2) = spZ regs4)
  by (unfold E4; rewrite (ew_Ereg_nat regs4 _ 2 2%bv eq_refl); reflexivity).
assert (U10 : U E4 (SOff 10 0) = if ManifestModel.name_char c then 1 else 0).
{ apply (U_atom E4 10); [unfold E4; rewrite (ew_Ereg_nat regs4 _ 10 10%bv eq_refl); exact R10r
  | destruct (ManifestModel.name_char c); lia]. }
unfold cfg_at. change (w64 HP_QNR) with (Z_to_bv 64 HP_QNR).
(* 0x8251c: beqz a0 *)
srr_branch_with tbl_hp_ok HS4.
- (* name_char c = false: 0x82560 a0 = 1, epilogue *)
  assert (HNC : ManifestModel.name_char c = false).
  { rewrite branch_eq_U, U10 in Hc. FMTrapB.fm_U_lits Hc. apply Z.eqb_eq in Hc.
    destruct (ManifestModel.name_char c); [exfalso; cbn in Hc; lia | reflexivity]. }
  aj_run_to tbl_hp_ok HS4 HJ4 A_hp_epi.
  { awr_ok_tac. }
  pose proof (gframe_of_frame tfibsegs W4 E4 _ 2 8 8 (spZ regs4) (spZ (cx_regs0 cx) - STK_has_prefixed)
    (spZ (cx_regs0 cx) - 120) _ _ HFr ltac:(vm_compute; reflexivity) Usp4 ltac:(rewrite hp_stk; lia) ltac:(lia)) as G5.
  clear HF HFr HG.
  lazymatch type of HS4 with st_ok _ _ _ (restrict _ ?ms5) =>
    rewrite (st_ok_restrict_mkst tfibsegs (w_H W4) E4 _ ms5 HS4 eq_refl); cbn [ss_pc]; pcnorm;
    pose proof (keep_run HP_KEEP E4 _ _ ms5 regs4 _ HS4 HAE4 ltac:(vm_compute; reflexivity)) as K5;
    rregU HS4 (10%bv : bv 5) R10f;
    apply (hp_ret B HGOTS HCELL cx ly4 S4 W4 (ms_regs ms5) (ms_mem ms5) _);
    [ exact (hp_fin_of_st B cx a ly4 S4 W4 regs4 m4 md4 _ _ _ H4 HJ4 G5 K5)
    | rewrite R10f, (HRES HNC), U_lit; reflexivity ]
  end.
- (* name_char c = true: the loop tail *)
  assert (HNC : ManifestModel.name_char c = true).
  { rewrite branch_eq_U, U10 in Hc. FMTrapB.fm_U_lits Hc. apply Z.eqb_neq in Hc.
    destruct (ManifestModel.name_char c); [reflexivity | exfalso; apply Hc; reflexivity]. }
  aj_run_to tbl_hp_ok HS4 HJ4 HP_TAIL.
  { awr_ok_tac. }
  pose proof (gframe_of_frame tfibsegs W4 E4 _ 2 8 8 (spZ regs4) (spZ (cx_regs0 cx) - STK_has_prefixed)
    (spZ (cx_regs0 cx) - 120) _ _ HFr ltac:(vm_compute; reflexivity) Usp4 ltac:(rewrite hp_stk; lia) ltac:(lia)) as G5.
  clear HF HFr HG.
  lazymatch type of HS4 with st_ok _ _ _ (restrict _ ?ms5) =>
    rewrite (st_ok_restrict_mkst tfibsegs (w_H W4) E4 _ ms5 HS4 eq_refl); cbn [ss_pc]; pcnorm;
    pose proof (keep_run HP_KEEP E4 _ _ ms5 regs4 _ HS4 HAE4 ltac:(vm_compute; reflexivity)) as K5;
    pose proof (keep_run [21%bv] E4 _ _ ms5 regs4 _ HS4 HAE4 ltac:(vm_compute; reflexivity)) as K21;
    apply (KT ly4 S4 W4 (ms_regs ms5) (ms_mem ms5) _);
    [ exact (hp_st_keep B cx a ly4 S4 W4 regs4 m4 md4 _ _ _ H4 HJ4 G5 K5 (K21 21%bv (or_introl eq_refl)))
    | exact HNC ]
  end.
Qed.
End s.
