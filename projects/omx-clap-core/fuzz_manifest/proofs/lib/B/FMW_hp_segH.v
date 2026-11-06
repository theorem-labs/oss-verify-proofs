(* has_prefixed on fm.asan-ubsan (G2, image B), loop segment HEAD 0x8246c..0x824a4 (lv2_locate.c:63-66): a = at - t;
   a < plen + 1 -> tail; the three UBSan pointer-overflow guards of `at - plen - 1` (0x82474 bgeu plen, at;
   0x8247c beq at - plen, 1; 0x82484 bltu -(at - plen), plen; trap `unimp` 0x825a0) are shown not taken inline
   (cgif lib/YCh0.v kill_not_trap form); the ASan check of at[-1] (0x82490..0x8249c, slow path 0x8253c, report
   0x825a4) runs on the token engine; at[-1] <> ':' -> tail, else the strncmp segment. Proves the kit's
   seg_head_ok (lib/B/FMW_hp_kit.v). *)
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
Lemma mod_wrap_eq : forall x y, x + 2 ^ 64 = y -> 0 <= y < 2 ^ 64 -> x mod 2 ^ 64 = y.
Proof. intros x y E Hy. rewrite <- (Z_mod_plus_full x 1). rewrite Z.mul_1_l, E. apply Z.mod_small. exact Hy. Qed.
Lemma regs_keep_trans : forall L r1 r2 r3, regs_keep L r1 r2 -> regs_keep L r2 r3 -> regs_keep L r1 r3.
Proof. intros L r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

(* the trap arm of a UBSan guard: B5's fm_kill_trap (lib/B/FMTrapB.v) with the operands' U facts in context *)
Ltac trap_kill := lazymatch goal with Hb : branch_taken _ _ _ = true |- _ => FMTrapB.fm_kill_trap Hb end.
Ltac trap_pass Hn := lazymatch goal with Hb : branch_taken _ _ _ = false |- _ => rename Hb into Hn end.
Ltac umod := repeat first [ rewrite U_add2 | rewrite U_mul2 | rewrite U_lit ].
Ltac zmods := repeat first [ rewrite Zmult_mod_idemp_l | rewrite Zmult_mod_idemp_r | rewrite Zplus_mod_idemp_l
                           | rewrite Zplus_mod_idemp_r | rewrite <- Z.add_assoc ].
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
Hypothesis IMGF : fm_img_facts tfibsegs B.
Lemma keep_run : forall L E ss H ms regs0 extra,
  st_ok tfibsegs E ss (restrict H ms) -> env_agree 32 (Ereg regs0 extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) L = true ->
  regs_keep L regs0 (ms_regs ms).
Proof. intros L E ss H ms regs0 extra HS HA Hc. exact (regs_keep_of_st_ok L E ss (restrict H ms) regs0 extra HS HA Hc). Qed.

Lemma seg_head : seg_head_ok B.
Proof.
intros cx a KT KN lyc Sc W regs m mdc H _.
pose proof g2_segs_low as Hsegs. pose proof g2_wx as Hwx.
pose proof (hp_sp B cx a lyc Sc W regs m mdc H) as (Hsp1 & Hsp2 & Hspc).
pose proof (hp_cstr B IMGF cx a lyc Sc W regs m mdc H) as (Ht & Hl).
pose proof Ht as (_ & Ht4 & Htc & _).
pose proof H as (HE & HJ & Hab & Q3 & Q4 & Hsp & HF & HSL & Q8 & Q9 & Q19 & Q20 & Q21 & Q23 & Q24 & Q25 & Q26 & Q27
  & Hmt & Hgl).
pose proof HE as (_ & _ & _ & _ & _ & _ & _ & Hlb & Hq & Hplen & Hqp & Htmax & _).
pose proof (has_prefixed_model.mt_len _ _ _ Hmt) as Halen.
assert (Hlbpos : (1 <= length (cx_lb cx))%nat) by (destruct (cx_lb cx); [contradiction | cbn; lia]).
ceil2. unfold MANIFEST_MAX in Htmax.
set (t := cx_t cx) in *. set (plen := cx_plen cx) in *.
set (sp0 := spZ (cx_regs0 cx)) in *.
pose proof (hp_seat B IMGF cx a lyc Sc W regs m mdc HP_HEAD H) as HS.
set (E := Ereg regs [w64 (Z.of_nat (length (cx_lb cx))); w64 (cx_t cx + cx_q cx)]) in HS.
assert (HAE : env_agree 32 (Ereg regs [w64 (Z.of_nat (length (cx_lb cx))); w64 (cx_t cx + cx_q cx)]) E)
  by (split; [intros; reflexivity | reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (X9 : ew E 9 = Z_to_bv 64 plen) by (unfold E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact Q9).
assert (X19 : ew E 19 = Z_to_bv 64 t) by (unfold E; rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact Q19).
assert (X21 : ew E 21 = Z_to_bv 64 (t + Z.of_nat a)) by (unfold E; rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact Q21).
assert (X24 : ew E 24 = Z_to_bv 64 (plen + 1)) by (unfold E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact Q24).
assert (X25 : ew E 25 = Z_to_bv 64 (- plen)) by (unfold E; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact Q25).
assert (X27 : ew E 27 = Z_to_bv 64 1) by (unfold E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact Q27).
assert (Rplen : 0 <= plen <= Z.of_nat (length (cx_tb cx))) by lia.
assert (Rta : 4096 <= t /\ t + Z.of_nat (length (cx_tb cx)) + 8 <= alloc_ceiling) by lia.
(* the engine's values *)
assert (Ua : U E (SAlu ALU_ADD (SMd M_MUL (SOff 19 0) (SLit (-1))) (SOff 21 0)) = Z.of_nat a).
{ umod. rewrite (U_atom_mod E 19 0 t X19), (U_atom_mod E 21 0 (t + Z.of_nat a) X21). zmods.
  apply mod_small_eq; lia. }
assert (U24 : U E (SOff 24 0) = plen + 1) by (rewrite (U_atom_mod E 24 0 (plen + 1) X24); apply mod_small_eq; lia).
assert (U9 : U E (SOff 9 0) = plen) by (rewrite (U_atom_mod E 9 0 plen X9); apply mod_small_eq; lia).
assert (U21 : U E (SOff 21 0) = t + Z.of_nat a) by (rewrite (U_atom_mod E 21 0 _ X21); apply mod_small_eq; lia).
assert (U27 : U E (SOff 27 0) = 1) by (rewrite (U_atom_mod E 27 0 1 X27); apply mod_small_eq; lia).
unfold cfg_at. change (w64 HP_HEAD) with (Z_to_bv 64 HP_HEAD).
(* 0x8246c: a0 = at - t; blt a0, s8 *)
aj_run tbl_hp_ok HS HJ.
{ awr_ok_tac. }
pose proof (gframe_of_frame tfibsegs W E _ 2 8 8 (spZ regs) (sp0 - STK_has_prefixed) (sp0 - 120) m _
  HFr ltac:(vm_compute; reflexivity) Usp ltac:(rewrite hp_stk; lia) ltac:(lia)) as G1.
clear HF HFr HG.
srr_branch_with tbl_hp_ok HS.
- (* a < plen + 1 -> tail *)
  rewrite (branch_lt_small E _ _ ltac:(rewrite Ua; lia) ltac:(rewrite U24; lia)), Ua, U24 in Hc.
  apply Z.ltb_lt in Hc.
  aj_run_to tbl_hp_ok HS HJ HP_TAIL.
  { awr_ok_tac. }
  pose proof (gframe_of_frame tfibsegs W E _ 2 8 8 (spZ regs) (sp0 - STK_has_prefixed) (sp0 - 120) _ _
    HFr ltac:(vm_compute; reflexivity) Usp ltac:(rewrite hp_stk; lia) ltac:(lia)) as G1b.
  clear HF HFr HG.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?ms) =>
    rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms HS eq_refl); cbn [ss_pc]; pcnorm;
    pose proof (keep_run HP_KEEP E _ _ ms regs _ HS HAE ltac:(vm_compute; reflexivity)) as K1;
    pose proof (keep_run [21%bv] E _ _ ms regs _ HS HAE ltac:(vm_compute; reflexivity)) as K21;
    apply (KT lyc Sc W (ms_regs ms) (ms_mem ms) _);
    [ apply (hp_st_keep B cx a lyc Sc W regs m mdc _ _ _ H HJ (gframe_seq tfibsegs W _ _ _ _ _ G1 G1b) K1
        (K21 21%bv (or_introl eq_refl)))
    | left; lia ]
  end.
- rewrite (branch_lt_small E _ _ ltac:(rewrite Ua; lia) ltac:(rewrite U24; lia)), Ua, U24 in Hc.
  apply Z.ltb_ge in Hc.
  (* 0x82474: UBSan guard bgeu plen, at *)
  aj_run tbl_hp_ok HS HJ.
  { awr_ok_tac. }
  pose proof (gframe_of_frame tfibsegs W E _ 2 8 8 (spZ regs) (sp0 - STK_has_prefixed) (sp0 - 120) _ _
    HFr ltac:(vm_compute; reflexivity) Usp ltac:(rewrite hp_stk; lia) ltac:(lia)) as G2.
  clear HF HFr HG.
  srr_branch_with tbl_hp_ok HS.
  { trap_kill. }   (* FM-B-TRAPS.md row 3: K5 bgeu bound, U s1 = plen < U s5 = t + a *)
  trap_pass Hg1. rewrite branch_geu_U, U9, U21 in Hg1. apply negb_false_iff, Z.ltb_lt in Hg1.
  (* 0x8247c: UBSan guard beq at - plen, 1 *)
  assert (U6 : U E (SAlu ALU_ADD (SOff 21 0) (SOff 25 0)) = t + Z.of_nat a - plen).
  { umod. rewrite (U_atom_mod E 21 0 _ X21), (U_atom_mod E 25 0 _ X25). zmods. apply mod_small_eq; lia. }
  aj_run tbl_hp_ok HS HJ.
  { awr_ok_tac. }
  pose proof (gframe_of_frame tfibsegs W E _ 2 8 8 (spZ regs) (sp0 - STK_has_prefixed) (sp0 - 120) _ _
    HFr ltac:(vm_compute; reflexivity) Usp ltac:(rewrite hp_stk; lia) ltac:(lia)) as G3.
  clear HF HFr HG.
  srr_branch_with tbl_hp_ok HS.
  { trap_kill. }   (* FM-B-TRAPS.md row 4: K1 eq, U (s5 + s9) = t + a - plen <> 1 *)
  trap_pass Hg2. clear Hg2.
  (* 0x82484: UBSan guard bltu -(at - plen), plen *)
  assert (Un : U E (SAlu ALU_ADD (SMd M_MUL (SOff 21 0) (SLit (-1))) (SMd M_MUL (SOff 25 0) (SLit (-1))))
               = 2 ^ 64 - (t + Z.of_nat a - plen)).
  { umod. rewrite (U_atom_mod E 21 0 _ X21), (U_atom_mod E 25 0 _ X25). zmods.
    apply mod_wrap_eq; lia. }
  aj_run tbl_hp_ok HS HJ.
  { awr_ok_tac. }
  pose proof (gframe_of_frame tfibsegs W E _ 2 8 8 (spZ regs) (sp0 - STK_has_prefixed) (sp0 - 120) _ _
    HFr ltac:(vm_compute; reflexivity) Usp ltac:(rewrite hp_stk; lia) ltac:(lia)) as G4.
  clear HF HFr HG.
  srr_branch_with tbl_hp_ok HS.
  { trap_kill. }   (* FM-B-TRAPS.md row 5: K4 bltu bound, U (-(s5 + s9)) = 2^64 - (t + a - plen) >= plen *)
  trap_pass Hg3. clear Hg3.
  (* 0x82488..0x8248c: s2 = at - plen - 1, a0 = at - 1; stop at the check *)
  aj_run_to tbl_hp_ok HS HJ HP_C1.
  { awr_ok_tac. }
  pose proof (gframe_of_frame tfibsegs W E _ 2 8 8 (spZ regs) (sp0 - STK_has_prefixed) (sp0 - 120) _ _
    HFr ltac:(vm_compute; reflexivity) Usp ltac:(rewrite hp_stk; lia) ltac:(lia)) as G5.
  clear HF HFr HG.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?ms5) =>
    rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms5 HS eq_refl); cbn [ss_pc]; pcnorm;
    pose proof (keep_run HP_KEEP E _ _ ms5 regs _ HS HAE ltac:(vm_compute; reflexivity)) as K5;
    pose proof (keep_run [21%bv] E _ _ ms5 regs _ HS HAE ltac:(vm_compute; reflexivity)) as K21;
    rregU HS (10%bv : bv 5) R10; rregU HS (18%bv : bv 5) R18; rregU HS (22%bv : bv 5) R22;
    set (regs5 := ms_regs ms5) in *; set (m5 := ms_mem ms5) in *
  end.
  lazymatch goal with |- context [mkCfg _ ?d] => set (md5 := d) in * end.
  assert (G : gframe tfibsegs W (sp0 - STK_has_prefixed) (sp0 - 120) m m5).
  { eapply (gframe_seq tfibsegs W _ _ m _ m5); [|exact G5].
    eapply (gframe_seq tfibsegs W _ _ m _ _); [|exact G4].
    eapply (gframe_seq tfibsegs W _ _ m _ _); [|exact G3].
    eapply (gframe_seq tfibsegs W _ _ m _ _); [exact G1 | exact G2]. }
  assert (H5 : hp_st B cx a lyc Sc W regs5 m5 md5).
  { apply (hp_st_keep B cx a lyc Sc W regs m mdc _ _ _ H HJ G K5 (K21 21%bv (or_introl eq_refl))). }
  assert (V10 : getr regs5 10 = w64 (t + Z.of_nat (a - 1))).
  { rewrite R10. unfold w64. f_equal. umod. rewrite (U_atom_mod E 9 _ _ X9), (U_atom_mod E 21 _ _ X21),
      (U_atom_mod E 25 _ _ X25). zmods. apply mod_small_eq; lia. }
  assert (V18 : getr regs5 18 = w64 (t + Z.of_nat a - plen - 1)).
  { rewrite R18. unfold w64. f_equal. umod. rewrite (U_atom_mod E 21 _ _ X21), (U_atom_mod E 25 _ _ X25).
    zmods. apply mod_small_eq; lia. }
  assert (V22 : getr regs5 22 = w64 (t + Z.of_nat a - plen)).
  { rewrite R22. unfold w64. f_equal. umod. rewrite (U_atom_mod E 21 _ _ X21), (U_atom_mod E 25 _ _ X25).
    zmods. apply mod_small_eq; lia. }
  clear R10 R18 R22.
  (* 0x82490..0x824a4: the ASan check of at[-1], c = at[-1]; bne c, ':' *)
  pose proof (hp_tbyte B IMGF cx a lyc Sc W regs5 m5 _ (a - 1) H5 ltac:(lia)) as (Vc & Rc).
  set (c := ManifestModel.byte_at (cx_tb cx) (a - 1)) in *.
  pose proof (hp_seat_chk B cx a lyc Sc W regs5 m5 _ HP_C1 (t + Z.of_nat (a - 1)) c H5 V10 ltac:(lia) Vc Rc) as HS2.
  pose proof (hp_shok B IMGF cx a lyc Sc W regs5 m5 _ c (a - 1) H5 V10 ltac:(lia)) as SHOK.
  pose proof H5 as (_ & HJ5 & _).
  clear HS. rename HS2 into HS.
  set (E2 := Ereg regs5 [w64 c]) in HS, SHOK.
  assert (HAE2 : env_agree 32 (Ereg regs5 [w64 c]) E2) by (split; [intros; reflexivity | reflexivity]).
  assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs5)
    by (unfold E2; rewrite (ew_Ereg_nat regs5 _ 2 2%bv eq_refl); reflexivity).
  assert (Hsp5 : spZ regs5 = sp0 - 128) by (pose proof H5 as (_ & _ & _ & _ & _ & S5 & _); exact S5).
  change m5 with (ms_mem (mkst regs5 (Z_to_bv 64 HP_C1) m5 (seg_rom tfibsegs))) in HJ5.
  aj_run_tok tbl_hp_ok HS HJ5 SHOK hp_Bspan.
  { awr_ok_tac. }
  pose proof (gframe_of_frame tfibsegs W E2 _ 2 8 8 (spZ regs5) (sp0 - STK_has_prefixed) (sp0 - 120) _ _
    HFr ltac:(vm_compute; reflexivity) Usp2 ltac:(rewrite hp_stk; lia) ltac:(lia)) as G6.
  clear HF HFr HG.
  (* the check's tokens added atoms 33, 34 (the shadow byte); a0 = zext8 of atom 32 = c *)
  lazymatch type of HS with st_ok _ ?Ex _ _ => set (E3 := Ex) in * end.
  pose proof H5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P20 & _).
  assert (X32 : ew E3 32 = Z_to_bv 64 c)
    by (unfold E3; rewrite !ew_ewset_other by lia; unfold E2; exact (ew_Ereg_extra regs5 _ 0)).
  assert (X20b : ew E3 20 = Z_to_bv 64 58)
    by (unfold E3; rewrite !ew_ewset_other by lia; unfold E2; rewrite (ew_Ereg_nat regs5 _ 20 20%bv eq_refl); exact P20).
  assert (Ua0 : U E3 (SExt false 8 (SOff 32 0)) = c).
  { rewrite U_SExt, (U_atom E3 32 c X32) by lia. change (2 ^ Z.of_N 8) with (2 ^ 8).
    rewrite Z.mod_small by lia. apply zcanon_id. unfold M64. lia. }
  assert (U20 : U E3 (SOff 20 0) = 58) by (apply (U_atom E3 20 58 X20b); lia).
  assert (HAE3 : env_agree 32 (Ereg regs5 [w64 c]) E3) by (unfold E3; env_agree_chain HAE2).
  assert (Usp3 : bv_unsigned (ew E3 2) = spZ regs5) by (unfold E3; rewrite !ew_ewset_other by lia; exact Usp2).
  srr_branch_with tbl_hp_ok HS.
  + (* at[-1] <> ':' -> tail *)
    lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
      rewrite branch_ne_U, Ua0, U20 in Hb; apply negb_true_iff, Z.eqb_neq in Hb; rename Hb into Hne end.
    aj_run_to tbl_hp_ok HS HJ5 HP_TAIL.
    { awr_ok_tac. }
    pose proof (gframe_of_frame tfibsegs W E3 _ 2 8 8 (spZ regs5) (sp0 - STK_has_prefixed) (sp0 - 120) _ _
      HFr ltac:(vm_compute; reflexivity) Usp3 ltac:(rewrite hp_stk; lia) ltac:(lia)) as G6b.
    clear HF HFr HG.
    lazymatch type of HS with st_ok _ _ _ (restrict _ ?ms6) =>
      rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E3 _ ms6 HS eq_refl); cbn [ss_pc]; pcnorm;
      pose proof (keep_run HP_KEEP E3 _ _ ms6 regs5 _ HS HAE3 ltac:(vm_compute; reflexivity)) as K6;
      pose proof (keep_run [21%bv] E3 _ _ ms6 regs5 _ HS HAE3 ltac:(vm_compute; reflexivity)) as K21b;
      apply (KT lyc Sc W (ms_regs ms6) (ms_mem ms6) _);
      [ apply (hp_st_keep B cx a lyc Sc W regs5 m5 _ _ _ _ H5 HJ5 (gframe_seq tfibsegs W _ _ _ _ _ G6 G6b) K6
          (K21b 21%bv (or_introl eq_refl)))
      | right; exact Hne ]
    end.
  + (* at[-1] = ':' -> strncmp *)
    lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
      rewrite branch_ne_U, Ua0, U20 in Hb; apply negb_false_iff, Z.eqb_eq in Hb; rename Hb into Heq end.
    aj_run_to tbl_hp_ok HS HJ5 HP_NCMP.
    { awr_ok_tac. }
    pose proof (gframe_of_frame tfibsegs W E3 _ 2 8 8 (spZ regs5) (sp0 - STK_has_prefixed) (sp0 - 120) _ _
      HFr ltac:(vm_compute; reflexivity) Usp3 ltac:(rewrite hp_stk; lia) ltac:(lia)) as G6b.
    clear HF HFr HG.
    lazymatch type of HS with st_ok _ _ _ (restrict _ ?ms6) =>
      rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E3 _ ms6 HS eq_refl); cbn [ss_pc]; pcnorm;
      pose proof (keep_run HP_KEEP E3 _ _ ms6 regs5 _ HS HAE3 ltac:(vm_compute; reflexivity)) as K6;
      pose proof (keep_run [21%bv; 18%bv; 22%bv] E3 _ _ ms6 regs5 _ HS HAE3 ltac:(vm_compute; reflexivity)) as K6b;
      apply (KN lyc Sc W (ms_regs ms6) (ms_mem ms6) _);
      [ apply (hp_st_keep B cx a lyc Sc W regs5 m5 _ _ _ _ H5 HJ5 (gframe_seq tfibsegs W _ _ _ _ _ G6 G6b) K6
          (K6b 21%bv (or_introl eq_refl)))
      | split; [split; [lia | split] | exact Heq] ]
    end.
    * rewrite (K6b 18%bv ltac:(cbv; tauto)). rewrite V18. reflexivity.
    * rewrite (K6b 22%bv ltac:(cbv; tauto)). rewrite V22. reflexivity.
Qed.
End s.
