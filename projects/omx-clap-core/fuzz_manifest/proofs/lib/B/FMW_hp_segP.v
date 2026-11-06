(* has_prefixed on fm.asan-ubsan (G2, image B), loop segment PRE 0x824bc..0x824ec (lv2_locate.c:68-71): the prefix
   matched at start = a - plen - 1; start = 0 (0x824bc bgeu t, t + start) -> post; else the UBSan pointer-overflow
   guard of `t + start - 1` (0x824c0 beq t + start, 1; trap `unimp` 0x825a0) is shown not taken inline with B5's
   FMTrapB.fm_kill_trap (FM-B-TRAPS.md row 6, K1 fmt_eq_not); the ASan check of start[-1] (0x824c8..0x824d4, slow
   path 0x82554, report 0x8255c) runs on the token engine; c = start[-1] (0x824d8), name_char (c) (0x824e0, the kit's
   hp_call_nc under name_char_spec); c = '.' (0x824e8) or name_char c (0x824ec) -> tail, else post. Proves the kit's
   seg_pre_ok (lib/B/FMW_hp_kit.v). *)
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
Lemma segP_denot_U : forall E e, sv_denot E e = Z_to_bv 64 (U E e).
Proof. intros E e. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma segP_mod_small : forall x y, x = y -> 0 <= y < 2 ^ 64 -> x mod 2 ^ 64 = y.
Proof. intros x y -> H. apply Z.mod_small. exact H. Qed.

Local Ltac umod := repeat first [ rewrite U_add2 | rewrite U_mul2 | rewrite U_lit ].
Local Ltac zmods := repeat first [ rewrite Zmult_mod_idemp_l | rewrite Zmult_mod_idemp_r | rewrite Zplus_mod_idemp_l
                                 | rewrite Zplus_mod_idemp_r | rewrite <- Z.add_assoc ].
(* the pc of a state after a branch (add_cond ...) as a literal *)
Local Ltac pcnorm := repeat lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?s)] =>
  let p := eval vm_compute in (ss_pc s) in change (ss_pc s) with p end.
(* getr of the register r after a run, as Z_to_bv 64 (U E e) *)
Local Ltac rregU HS r Hr :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    assert (Hr : getr (ms_regs ms) r = Z_to_bv 64 (U E e))
      by (rewrite <- segP_denot_U; exact (st_ok_restrict_reg segs H E ss ms r HS))
  end.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Hypothesis IMGF : fm_img_facts tfibsegs B.
Hypothesis NC : name_char_spec tfibsegs B.

Lemma segP_keep : forall L E ss H ms regs0 extra,
  st_ok tfibsegs E ss (restrict H ms) -> env_agree 32 (Ereg regs0 extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) L = true ->
  regs_keep L regs0 (ms_regs ms).
Proof. intros L E ss H ms regs0 extra HS HA Hc. exact (regs_keep_of_st_ok L E ss (restrict H ms) regs0 extra HS HA Hc). Qed.

(* ---- 0x824e4 (HP_PNR): name_char (start[-1]) returned; c = '.' or name_char c -> tail, else post ---- *)
Lemma segP_pnr : forall cx a,
  hp_cont B cx HP_TAIL a (fun _ => (0 < a - Z.to_nat (cx_plen cx) - 1)%nat /\
    (ManifestModel.byte_at (cx_tb cx) (a - Z.to_nat (cx_plen cx) - 2) = 46 \/
     ManifestModel.name_char (ManifestModel.byte_at (cx_tb cx) (a - Z.to_nat (cx_plen cx) - 2)) = true)) ->
  hp_cont B cx HP_POST a (fun _ => (a - Z.to_nat (cx_plen cx) - 1)%nat = O \/
    ((0 < a - Z.to_nat (cx_plen cx) - 1)%nat /\
     ManifestModel.byte_at (cx_tb cx) (a - Z.to_nat (cx_plen cx) - 2) <> 46 /\
     ManifestModel.name_char (ManifestModel.byte_at (cx_tb cx) (a - Z.to_nat (cx_plen cx) - 2)) = false)) ->
  forall lyc Sc W regs m mdc, hp_st B cx a lyc Sc W regs m mdc ->
  (0 < a - Z.to_nat (cx_plen cx) - 1)%nat ->
  getr regs 22 = w64 (ManifestModel.byte_at (cx_tb cx) (a - Z.to_nat (cx_plen cx) - 2)) ->
  getr regs 10 = w64 (if ManifestModel.name_char (ManifestModel.byte_at (cx_tb cx) (a - Z.to_nat (cx_plen cx) - 2))
                      then 1 else 0) ->
  SRr tfibsegs W (cfg_at tfibsegs HP_PNR regs m mdc) (hp_post B cx).
Proof.
intros cx a KT KP lyc Sc W regs m mdc H Hpos R22 R10.
pose proof g2_segs_low as Hsegs. pose proof g2_wx as Hwx.
pose proof (hp_sp B cx a lyc Sc W regs m mdc H) as (Hsp1 & Hsp2 & Hspc).
pose proof (hp_cstr B IMGF cx a lyc Sc W regs m mdc H) as (Ht & Hl).
pose proof Ht as (_ & Ht4 & Htc & _).
pose proof H as (HE & HJ & _ & _ & _ & Hsp & _).
pose proof HE as (_ & _ & _ & _ & _ & _ & _ & Hlb & Hq & Hplen & Hqp & Htmax & _).
pose proof H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmt & _).
pose proof (has_prefixed_model.mt_len _ _ _ Hmt) as Halen.
ceil2. unfold MANIFEST_MAX in Htmax.
set (sp0 := spZ (cx_regs0 cx)) in *.
pose proof (hp_tbyte B IMGF cx a lyc Sc W regs m mdc (a - Z.to_nat (cx_plen cx) - 2) H ltac:(lia)) as (_ & Rc).
set (c := ManifestModel.byte_at (cx_tb cx) (a - Z.to_nat (cx_plen cx) - 2)) in *.
pose proof (hp_seat B IMGF cx a lyc Sc W regs m mdc HP_PNR H) as HS.
set (E := Ereg regs [w64 (Z.of_nat (length (cx_lb cx))); w64 (cx_t cx + cx_q cx)]) in HS.
assert (HAE : env_agree 32 (Ereg regs [w64 (Z.of_nat (length (cx_lb cx))); w64 (cx_t cx + cx_q cx)]) E)
  by (split; [intros; reflexivity | reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (U22 : U E (SOff 22 0) = c).
{ apply (U_atom E 22 c); [unfold E; rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact R22 | lia]. }
assert (U10 : U E (SOff 10 0) = if ManifestModel.name_char c then 1 else 0).
{ apply (U_atom E 10); [unfold E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact R10 |].
  destruct (ManifestModel.name_char c); lia. }
unfold cfg_at. change (w64 HP_PNR) with (Z_to_bv 64 HP_PNR).
(* 0x824e4: a1 = '.'; beq s6, a1 *)
aj_run tbl_hp_ok HS HJ.
{ awr_ok_tac. }
pose proof (gframe_of_frame tfibsegs W E _ 2 8 8 (spZ regs) (sp0 - STK_has_prefixed) (sp0 - 120) m _
  HFr ltac:(vm_compute; reflexivity) Usp ltac:(rewrite hp_stk; lia) ltac:(lia)) as G1.
clear HF HFr HG.
srr_branch_with tbl_hp_ok HS.
- (* c = '.' -> tail *)
  rewrite branch_eq_U, U22, U_lit, (Z.mod_small 46) in Hc by lia. apply Z.eqb_eq in Hc.
  aj_run_to tbl_hp_ok HS HJ HP_TAIL.
  { awr_ok_tac. }
  pose proof (gframe_of_frame tfibsegs W E _ 2 8 8 (spZ regs) (sp0 - STK_has_prefixed) (sp0 - 120) _ _
    HFr ltac:(vm_compute; reflexivity) Usp ltac:(rewrite hp_stk; lia) ltac:(lia)) as G2.
  clear HF HFr HG.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?ms) =>
    rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms HS eq_refl); cbn [ss_pc]; pcnorm;
    pose proof (segP_keep HP_KEEP E _ _ ms regs _ HS HAE ltac:(vm_compute; reflexivity)) as K1;
    pose proof (segP_keep [21%bv] E _ _ ms regs _ HS HAE ltac:(vm_compute; reflexivity)) as K21;
    apply (KT lyc Sc W (ms_regs ms) (ms_mem ms) _);
    [ apply (hp_st_keep B cx a lyc Sc W regs m mdc _ _ _ H HJ (gframe_seq tfibsegs W _ _ _ _ _ G1 G2) K1
        (K21 21%bv (or_introl eq_refl)))
    | split; [exact Hpos | left; exact Hc] ]
  end.
- rewrite branch_eq_U, U22, U_lit, (Z.mod_small 46) in Hc by lia. apply Z.eqb_neq in Hc.
  (* 0x824ec: bnez a0 *)
  aj_run tbl_hp_ok HS HJ.
  { awr_ok_tac. }
  pose proof (gframe_of_frame tfibsegs W E _ 2 8 8 (spZ regs) (sp0 - STK_has_prefixed) (sp0 - 120) _ _
    HFr ltac:(vm_compute; reflexivity) Usp ltac:(rewrite hp_stk; lia) ltac:(lia)) as G2.
  clear HF HFr HG.
  srr_branch_with tbl_hp_ok HS.
  + (* name_char c -> tail *)
    rewrite branch_ne_U, U10, U_lit in Hc0.
    destruct (ManifestModel.name_char c) eqn:Enc; rewrite ?Enc in Hc0;
      [| exfalso; vm_compute in Hc0; discriminate Hc0].
    aj_run_to tbl_hp_ok HS HJ HP_TAIL.
    { awr_ok_tac. }
    pose proof (gframe_of_frame tfibsegs W E _ 2 8 8 (spZ regs) (sp0 - STK_has_prefixed) (sp0 - 120) _ _
      HFr ltac:(vm_compute; reflexivity) Usp ltac:(rewrite hp_stk; lia) ltac:(lia)) as G3.
    clear HF HFr HG.
    lazymatch type of HS with st_ok _ _ _ (restrict _ ?ms) =>
      rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms HS eq_refl); cbn [ss_pc]; pcnorm;
      pose proof (segP_keep HP_KEEP E _ _ ms regs _ HS HAE ltac:(vm_compute; reflexivity)) as K1;
      pose proof (segP_keep [21%bv] E _ _ ms regs _ HS HAE ltac:(vm_compute; reflexivity)) as K21;
      apply (KT lyc Sc W (ms_regs ms) (ms_mem ms) _);
      [ apply (hp_st_keep B cx a lyc Sc W regs m mdc _ _ _ H HJ
          (gframe_seq tfibsegs W _ _ _ _ _ (gframe_seq tfibsegs W _ _ _ _ _ G1 G2) G3) K1
          (K21 21%bv (or_introl eq_refl)))
      | split; [exact Hpos | right; first [exact Enc | reflexivity]] ]
    end.
  + (* neither -> post *)
    rewrite branch_ne_U, U10, U_lit in Hc0.
    destruct (ManifestModel.name_char c) eqn:Enc; rewrite ?Enc in Hc0;
      [exfalso; vm_compute in Hc0; discriminate Hc0 |].
    aj_run_to tbl_hp_ok HS HJ HP_POST.
    { awr_ok_tac. }
    pose proof (gframe_of_frame tfibsegs W E _ 2 8 8 (spZ regs) (sp0 - STK_has_prefixed) (sp0 - 120) _ _
      HFr ltac:(vm_compute; reflexivity) Usp ltac:(rewrite hp_stk; lia) ltac:(lia)) as G3.
    clear HF HFr HG.
    lazymatch type of HS with st_ok _ _ _ (restrict _ ?ms) =>
      rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms HS eq_refl); cbn [ss_pc]; pcnorm;
      pose proof (segP_keep HP_KEEP E _ _ ms regs _ HS HAE ltac:(vm_compute; reflexivity)) as K1;
      pose proof (segP_keep [21%bv] E _ _ ms regs _ HS HAE ltac:(vm_compute; reflexivity)) as K21;
      apply (KP lyc Sc W (ms_regs ms) (ms_mem ms) _);
      [ apply (hp_st_keep B cx a lyc Sc W regs m mdc _ _ _ H HJ
          (gframe_seq tfibsegs W _ _ _ _ _ (gframe_seq tfibsegs W _ _ _ _ _ G1 G2) G3) K1
          (K21 21%bv (or_introl eq_refl)))
      | right; split; [exact Hpos | split; [exact Hc | first [exact Enc | reflexivity]]] ]
    end.
Qed.

(* ---- 0x824c8 (HP_C2): the ASan check of start[-1], c = start[-1], name_char (c) ---- *)
Lemma segP_c2 : forall cx a,
  hp_cont B cx HP_TAIL a (fun _ => (0 < a - Z.to_nat (cx_plen cx) - 1)%nat /\
    (ManifestModel.byte_at (cx_tb cx) (a - Z.to_nat (cx_plen cx) - 2) = 46 \/
     ManifestModel.name_char (ManifestModel.byte_at (cx_tb cx) (a - Z.to_nat (cx_plen cx) - 2)) = true)) ->
  hp_cont B cx HP_POST a (fun _ => (a - Z.to_nat (cx_plen cx) - 1)%nat = O \/
    ((0 < a - Z.to_nat (cx_plen cx) - 1)%nat /\
     ManifestModel.byte_at (cx_tb cx) (a - Z.to_nat (cx_plen cx) - 2) <> 46 /\
     ManifestModel.name_char (ManifestModel.byte_at (cx_tb cx) (a - Z.to_nat (cx_plen cx) - 2)) = false)) ->
  forall lyc Sc W regs m mdc, hp_st B cx a lyc Sc W regs m mdc ->
  (0 < a - Z.to_nat (cx_plen cx) - 1)%nat ->
  getr regs 10 = w64 (cx_t cx + Z.of_nat (a - Z.to_nat (cx_plen cx) - 2)) ->
  SRr tfibsegs W (cfg_at tfibsegs HP_C2 regs m mdc) (hp_post B cx).
Proof.
intros cx a KT KP lyc Sc W regs m mdc H Hpos R10.
pose proof g2_segs_low as Hsegs. pose proof g2_wx as Hwx.
pose proof (hp_sp B cx a lyc Sc W regs m mdc H) as (Hsp1 & Hsp2 & Hspc).
pose proof (hp_cstr B IMGF cx a lyc Sc W regs m mdc H) as (Ht & Hl).
pose proof Ht as (_ & Ht4 & Htc & _).
pose proof H as (HE & HJ & _ & _ & _ & Hsp & _).
pose proof HE as (_ & _ & _ & _ & _ & _ & _ & Hlb & Hq & Hplen & Hqp & Htmax & _).
pose proof H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmt & _).
pose proof (has_prefixed_model.mt_len _ _ _ Hmt) as Halen.
ceil2. unfold MANIFEST_MAX in Htmax.
set (sp0 := spZ (cx_regs0 cx)) in *.
pose proof (hp_tbyte B IMGF cx a lyc Sc W regs m mdc (a - Z.to_nat (cx_plen cx) - 2) H ltac:(lia)) as (Vc & Rc).
set (c := ManifestModel.byte_at (cx_tb cx) (a - Z.to_nat (cx_plen cx) - 2)) in *.
pose proof (hp_seat_chk B cx a lyc Sc W regs m mdc HP_C2 (cx_t cx + Z.of_nat (a - Z.to_nat (cx_plen cx) - 2)) c H R10
  ltac:(lia) Vc Rc) as HS.
pose proof (hp_shok B IMGF cx a lyc Sc W regs m mdc c (a - Z.to_nat (cx_plen cx) - 2) H R10 ltac:(lia)) as SHOK.
set (E2 := Ereg regs [w64 c]) in HS, SHOK.
assert (HAE2 : env_agree 32 (Ereg regs [w64 c]) E2) by (split; [intros; reflexivity | reflexivity]).
assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs)
  by (unfold E2; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (U32 : U E2 (SOff 32 0) = c)
  by (apply (U_atom E2 32 c); [unfold E2; exact (ew_Ereg_extra regs _ 0) | lia]).
unfold cfg_at. change (w64 HP_C2) with (Z_to_bv 64 HP_C2).
change m with (ms_mem (mkst regs (Z_to_bv 64 HP_C2) m (seg_rom tfibsegs))) in HJ.
(* 0x824c8..0x824e0: shadow check of start[-1], s6 = c, a0 = c, jal name_char *)
aj_run_tok tbl_hp_ok HS HJ SHOK hp_Bspan.
{ awr_ok_tac. }
pose proof (gframe_of_frame tfibsegs W E2 _ 2 8 8 (spZ regs) (sp0 - STK_has_prefixed) (sp0 - 120) _ _
  HFr ltac:(vm_compute; reflexivity) Usp2 ltac:(rewrite hp_stk; lia) ltac:(lia)) as G1.
clear HF HFr HG.
(* the check's tokens may add atoms 33.. (the shadow byte); s6 = a0 = zext8 of atom 32 = c *)
lazymatch type of HS with st_ok _ ?Ex _ _ => set (E3 := Ex) in * end.
assert (X32 : ew E3 32 = Z_to_bv 64 c)
  by (unfold E3; rewrite ?ew_ewset_other by lia; unfold E2; exact (ew_Ereg_extra regs _ 0)).
assert (HAE3 : env_agree 32 (Ereg regs [w64 c]) E3) by (unfold E3; env_agree_chain HAE2).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?ms1) =>
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E3 _ ms1 HS eq_refl); cbn [ss_pc]; pcnorm;
  pose proof (segP_keep HP_KEEP E3 _ _ ms1 regs _ HS HAE3 ltac:(vm_compute; reflexivity)) as K1;
  pose proof (segP_keep [21%bv] E3 _ _ ms1 regs _ HS HAE3 ltac:(vm_compute; reflexivity)) as K21;
  rregU HS (1%bv : bv 5) R1; rregU HS (10%bv : bv 5) R10b; rregU HS (22%bv : bv 5) R22;
  set (regs1 := ms_regs ms1) in *; set (m1 := ms_mem ms1) in *
end.
lazymatch goal with |- context [mkCfg _ ?d] => set (md1 := d) in * end.
assert (H1 : hp_st B cx a lyc Sc W regs1 m1 md1).
{ apply (hp_st_keep B cx a lyc Sc W regs m mdc _ _ _ H HJ G1 K1 (K21 21%bv (or_introl eq_refl))). }
assert (Uc : U E3 (SExt false 8 (SOff 32 0)) = c).
{ rewrite U_SExt, (U_atom E3 32 c X32) by lia. change (2 ^ Z.of_N 8) with (2 ^ 8).
  rewrite Z.mod_small by lia. apply zcanon_id. unfold M64. lia. }
assert (Rra : getr regs1 1 = Z_to_bv 64 0x824e4) by (rewrite R1; f_equal; umod; reflexivity).
assert (Ra0 : getr regs1 10 = w64 c).
{ rewrite R10b. unfold w64. f_equal. umod. rewrite Uc, (Z.mod_small 0) by lia. apply segP_mod_small; lia. }
assert (Rs6 : getr regs1 22 = w64 c) by (rewrite R22, Uc; reflexivity).
apply (hp_call_nc B IMGF NC cx a lyc Sc W regs1 m1 md1 0x824e4 c H1 Rra ltac:(lia) ltac:(reflexivity) Ra0 Rc).
intros ly2 S2 W2 regs2 m2 md2 H2 HP2 Ha0.
apply (segP_pnr cx a KT KP ly2 S2 W2 regs2 m2 md2 H2 Hpos).
- rewrite (preserved_reg regs1 regs2 22%bv HP2 cs22). exact Rs6.
- exact Ha0.
Qed.

(* ---- 0x824bc (HP_PRE): start = 0 -> post; [UBSan guard 0x824c0]; a0 = start - 1 ---- *)
Lemma seg_pre : seg_pre_ok B.
Proof.
intros cx a KT KP lyc Sc W regs m mdc H HP.
destruct HP as (Hpa & P18 & P22).
pose proof g2_segs_low as Hsegs. pose proof g2_wx as Hwx.
pose proof (hp_sp B cx a lyc Sc W regs m mdc H) as (Hsp1 & Hsp2 & Hspc).
pose proof (hp_cstr B IMGF cx a lyc Sc W regs m mdc H) as (Ht & Hl).
pose proof Ht as (_ & Ht4 & Htc & _).
pose proof H as (HE & HJ & Hab & Q3 & Q4 & Hsp & HF & HSL & Q8 & Q9 & Q19 & Q20 & Q21 & Q23 & Q24 & Q25 & Q26 & Q27
  & Hmt & Hgl).
pose proof HE as (_ & _ & _ & _ & _ & _ & _ & Hlb & Hq & Hplen & Hqp & Htmax & _).
pose proof (has_prefixed_model.mt_len _ _ _ Hmt) as Halen.
ceil2. unfold MANIFEST_MAX in Htmax.
set (t := cx_t cx) in *. set (plen := cx_plen cx) in *.
set (sp0 := spZ (cx_regs0 cx)) in *.
pose proof (hp_seat B IMGF cx a lyc Sc W regs m mdc HP_PRE H) as HS.
set (E := Ereg regs [w64 (Z.of_nat (length (cx_lb cx))); w64 (cx_t cx + cx_q cx)]) in HS.
assert (HAE : env_agree 32 (Ereg regs [w64 (Z.of_nat (length (cx_lb cx))); w64 (cx_t cx + cx_q cx)]) E)
  by (split; [intros; reflexivity | reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (X18 : ew E 18 = Z_to_bv 64 (t + Z.of_nat a - plen - 1))
  by (unfold E; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact P18).
assert (X19 : ew E 19 = Z_to_bv 64 t) by (unfold E; rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact Q19).
assert (X22 : ew E 22 = Z_to_bv 64 (t + Z.of_nat a - plen))
  by (unfold E; rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact P22).
assert (X27 : ew E 27 = Z_to_bv 64 1) by (unfold E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact Q27).
assert (U18 : U E (SOff 18 0) = t + Z.of_nat a - plen - 1)
  by (rewrite (U_atom_mod E 18 0 _ X18); apply segP_mod_small; lia).
assert (U19 : U E (SOff 19 0) = t) by (rewrite (U_atom_mod E 19 0 _ X19); apply segP_mod_small; lia).
assert (U27 : U E (SOff 27 0) = 1) by (rewrite (U_atom_mod E 27 0 _ X27); apply segP_mod_small; lia).
unfold cfg_at. change (w64 HP_PRE) with (Z_to_bv 64 HP_PRE).
(* 0x824bc: bgeu s3, s2 (t >=u t + start) *)
srr_branch_with tbl_hp_ok HS.
- (* start = 0 -> post *)
  rewrite branch_geu_U, U19, U18 in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
  aj_run_to tbl_hp_ok HS HJ HP_POST.
  { awr_ok_tac. }
  pose proof (gframe_of_frame tfibsegs W E _ 2 8 8 (spZ regs) (sp0 - STK_has_prefixed) (sp0 - 120) m _
    HFr ltac:(vm_compute; reflexivity) Usp ltac:(rewrite hp_stk; lia) ltac:(lia)) as G1.
  clear HF HFr HG.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?ms) =>
    rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms HS eq_refl); cbn [ss_pc]; pcnorm;
    pose proof (segP_keep HP_KEEP E _ _ ms regs _ HS HAE ltac:(vm_compute; reflexivity)) as K1;
    pose proof (segP_keep [21%bv] E _ _ ms regs _ HS HAE ltac:(vm_compute; reflexivity)) as K21;
    apply (KP lyc Sc W (ms_regs ms) (ms_mem ms) _);
    [ apply (hp_st_keep B cx a lyc Sc W regs m mdc _ _ _ H HJ G1 K1 (K21 21%bv (or_introl eq_refl)))
    | left; lia ]
  end.
- rewrite branch_geu_U, U19, U18 in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
  assert (Hpos : (0 < a - Z.to_nat plen - 1)%nat) by lia.
  (* 0x824c0: UBSan guard beq s2, s11 (t + start = 1), FM-B-TRAPS.md row 6 *)
  aj_run tbl_hp_ok HS HJ.
  { awr_ok_tac. }
  pose proof (gframe_of_frame tfibsegs W E _ 2 8 8 (spZ regs) (sp0 - STK_has_prefixed) (sp0 - 120) m _
    HFr ltac:(vm_compute; reflexivity) Usp ltac:(rewrite hp_stk; lia) ltac:(lia)) as G1.
  clear HF HFr HG.
  srr_branch_with tbl_hp_ok HS.
  { lazymatch goal with Hb : branch_taken _ _ _ = true |- _ => FMTrapB.fm_kill_trap Hb end. }
  (* 0x824c4: a0 = s6 - 2 = t + start - 1; stop at the check *)
  aj_run_to tbl_hp_ok HS HJ HP_C2.
  { awr_ok_tac. }
  pose proof (gframe_of_frame tfibsegs W E _ 2 8 8 (spZ regs) (sp0 - STK_has_prefixed) (sp0 - 120) _ _
    HFr ltac:(vm_compute; reflexivity) Usp ltac:(rewrite hp_stk; lia) ltac:(lia)) as G2.
  clear HF HFr HG.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?ms2) =>
    rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms2 HS eq_refl); cbn [ss_pc]; pcnorm;
    pose proof (segP_keep HP_KEEP E _ _ ms2 regs _ HS HAE ltac:(vm_compute; reflexivity)) as K2;
    pose proof (segP_keep [21%bv] E _ _ ms2 regs _ HS HAE ltac:(vm_compute; reflexivity)) as K21;
    rregU HS (10%bv : bv 5) R10;
    set (regs2 := ms_regs ms2) in *; set (m2 := ms_mem ms2) in *
  end.
  lazymatch goal with |- context [mkCfg _ ?d] => set (md2 := d) in * end.
  assert (H2 : hp_st B cx a lyc Sc W regs2 m2 md2).
  { apply (hp_st_keep B cx a lyc Sc W regs m mdc _ _ _ H HJ (gframe_seq tfibsegs W _ _ _ _ _ G1 G2) K2
      (K21 21%bv (or_introl eq_refl))). }
  assert (V10 : getr regs2 10 = w64 (t + Z.of_nat (a - Z.to_nat plen - 2))).
  { rewrite R10. unfold w64. f_equal. umod. rewrite ?(U_atom_mod E 22 _ _ X22). zmods.
    apply segP_mod_small; lia. }
  apply (segP_c2 cx a KT KP lyc Sc W regs2 m2 md2 H2 Hpos V10).
Qed.
End s.
