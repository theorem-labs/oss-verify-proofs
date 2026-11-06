(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:180-183, 357-361,
   for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue.v, with its module paths and numbers changed; 204 of its 254 lines of code are new or changed and 319 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/check_ignore.v, with its module paths and module names changed; 175 of its 209 lines of code are new or changed and 220 lines of the source are left out. *)
(* reac_declared_vlan_split on fuzz_segconf image B (fuzz_segconf.asan-ubsan): the image-B port of
   lib/A/Prog/reac_declared_vlan_split_s6.v (commit ceb7e39832b2), plus image B's alignment test
   of the vid cell before its store (0x8a3b4 `andi a0,s0,1`, 0x8a3b8 `bnez a0` to the UBSan trap `unimp` 0x8a3d8).
   The point K6 (0x8a3b0), after name_ok. `beqz a0` returns 0 when name_ok refused the parent; else the alignment
   test (refuted: vid mod 2 = 0, split_pre), the check of the 2-byte store to the vid cell (0x8a3bc-0x8a3c8, killed by
   the cell's shadow), `sh s5,0(s0)`, `li a0,1`, and on to the epilogue KR. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0p YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_lem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_k reac_declared_vlan_split_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_r reac_declared_vlan_split_h.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition vs_vid_r : YP09.region := YP09.mkRegion (Some 8%nat) 0 2 0 2 [].
Definition vs_Bx : sv := SOff 22 0.
Definition vs_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition vs_SH6 : list shent := [mkSHE 8 0 2].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variables gotw guard : Z.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Lemma vs_K6 : vs_KR_stmt B gotw guard -> vs_K6_stmt B gotw guard.
Proof using.
intros HKR. unfold vs_K6_stmt. intros e ly' S' W' regs' mem' md' di v HE HJ HR HSL Hdi Hdi0 Hne Hdig Hv Hvr R21 R10 HPZ HNA HVP HVA HKP.
pose proof HE as (HPRE & HROD & H10 & B10 & H11 & B11 & H12 & H13 & B13 & HSP & Hnev).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HR as (Hsp & G3 & G4 & G8 & G9 & G18 & G19 & G22 & G27).
pose proof HSP as (Hs0 & Hstr & Hlen & Hsadd & Hamr & Hsloc & Hp0 & Hcap & Hpdst & Hpadd & Hpdisj & Hv0 & Hv2 & Hvdst & Hvadd & Hvdisj & Hssp).
assert (HVS : VS_STK = 12352) by reflexivity.
unfold e_sp in *.
(* the model: vlan_split is name_ok's verdict on p = firstn di s *)
set (p := firstn di (e_s e)) in *.
assert (Hnul : SegModel.nulfree (e_s e)) by exact (proj2 (proj1 Hstr)).
assert (Hvs : SegModel.vlan_split (e_s e) = if SegModel.name_ok p then Some (p, v) else None).
{ rewrite (vs_code_eq _ Hnul Hlen). subst v. apply vs_name; [exact Hdi | exact Hdi0 | exact Hne | exact Hdig |].
  apply orb_false_iff. split; [apply Z.ltb_ge | apply Z.ltb_ge]; unfold vs_tail in Hvr; lia. }
assert (Hcopy : split_copy (e_s e) = Some di)
  by (apply vs_copy_some; [exact Hnul | exact Hlen | exact Hdi | exact Hdi0 | exact Hne | exact Hdig | unfold vs_tail in Hv; lia]).
pose proof (vs_di_lt _ _ Hnul Hdi) as Hdil.
destruct (vs_dst_facts B _ _ _ _ _ _ _ _ 16 HAR Hstk ltac:(lia) Hpdst) as (Plo & Phi & Pplace).
(* the vid cell *)
destruct (vs_dst_facts B _ _ _ _ _ _ _ _ 2 HAR Hstk ltac:(lia) Hvdst) as (Vlo & Vhi & Vplace).
set (E := Eimg (Ereg regs' (vs_xs (e_regs e) ++ []))).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EV : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs' r)
  by (intros n r Hn; subst E; apply vs_EE; exact Hn).
assert (HS : st_ok_pi SEGS VAL E (vs_ssK VS_K6 [(10%nat, mkAF 0 1 0); (8%nat, mkAF 4096 (2 ^ 47 - 2) 1); (21%nat, mkAF 1 4094 0)])
  (restrict (w_H W') (mkst regs' (Z_to_bv 64 (BASE + VS_K6)) mem' (seg_rom SEGS)))).
{ apply vs_seedK.
  - replace (spZ regs' + 64) with (spZ (e_regs e)) by lia. exact HSL.
  - lia.
  - rewrite Hsp. replace (spZ (e_regs e) - 64) with (spZ (e_regs e) + (-4) * 16) by lia.
    rewrite Z_mod_plus_full. exact Hal16.
  - exact G22.
  - cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E.
    rewrite (EV 10%nat 10%bv eq_refl), (EV 8%nat 8%bv eq_refl), (EV 21%nat 21%bv eq_refl), R10, G8, R21.
    unfold w64. rewrite !unsigned_lit_small by (unfold seg_spec.b2z; destruct (SegModel.name_ok p); lia).
    rewrite Z.pow_0_r, Z.mod_1_r, Z.pow_1_r.
    unfold seg_spec.b2z. destruct (SegModel.name_ok p); repeat split; first [exact I | lia]. }
assert (UB : U E vs_Bx = SHADOW_OFF).
{ unfold vs_Bx. apply U_atom; [rewrite (EV 22%nat 22%bv eq_refl), G22; reflexivity | unfold SHADOW_OFF; lia]. }
assert (SHOK0 : sh_ok SEGS vs_Bx [] E (mrestrict (w_H W') mem')) by (unfold sh_ok; apply Forall_nil).
unfold vs_goal, vs_cfg.
psrr_branch_tok RUN BR HS SHOK0 vs_Bspan.
- (* name_ok refused p: return 0 *)
  assert (Hno : SegModel.name_ok p = false).
  { rewrite branch_eq_U in Hc. rewrite U_lit in Hc by lia.
    rewrite (U_atom E 10 (seg_spec.b2z (SegModel.name_ok p))) in Hc;
      [| rewrite (EV 10%nat 10%bv eq_refl), R10; reflexivity | unfold seg_spec.b2z; destruct (SegModel.name_ok p); lia].
    unfold seg_spec.b2z in Hc. destruct (SegModel.name_ok p); [discriminate Hc | reflexivity]. }
  rewrite Hno in Hvs.
  paj_run_to_tok RUNTO HS HJ SHOK0 vs_Bspan VS_KR.
  { vs_awr_ro. }
  idtac "X1". pmkst HS. idtac "X2".
  lazymatch goal with H : frame_of _ _ _ _ |- _ => idtac "found" H end.
  lazymatch goal with H : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ => idtac "found2" H end.
  lazymatch goal with Hfr : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) Hfr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin; repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn in Hrr; lia|]); destruct Hin)) as UN end.
  apply (vs_exit_KR B gotw guard HKR e ly' S' W' regs' mem' (ms_regs ms) (ms_mem ms) _ 0 HE HR HSL HJ).
  + intros r Hr.
    assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct Hcases as [-> | Hcases]); try subst r;
    lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
      let n := eval compute in (Z.to_nat k) in
      eapply (vs_reg_atom _ _ _ _ _ n _ HS); [apply EV; reflexivity | vm_compute; reflexivity] end.
  + intros a Ha. unfold e_sp in Ha. exact (UN a ltac:(lia) (fun x => x)).
  + rewrite (vs_reg_atom _ _ _ _ _ 10%nat _ HS (EV 10%nat 10%bv eq_refl) ltac:(vm_compute; reflexivity)), R10, Hno.
    reflexivity.
  + intros regs'' md'' H10''. unfold vs_Q. rewrite Hvs. split; [exact H10''|]. split; [exact I|]. split; [|exact HNA].
    apply (vs_kept_step _ _ _ mem'); [apply (vs_kept_mono _ _ _ _ _ _ _ _ HKP)|].
    * intros a Ha. unfold split_E. rewrite Hcopy. left. exact Ha.
    * intros a Ha Hw He. exact (UN a Ha (fun x => x)).
- (* name_ok accepted p: the store of v to the vid cell, return 1 *)
  assert (Hyes : SegModel.name_ok p = true).
  { rewrite branch_eq_U in Hc. rewrite U_lit in Hc by lia.
    rewrite (U_atom E 10 (seg_spec.b2z (SegModel.name_ok p))) in Hc;
      [| rewrite (EV 10%nat 10%bv eq_refl), R10; reflexivity | unfold seg_spec.b2z; destruct (SegModel.name_ok p); lia].
    unfold seg_spec.b2z in Hc. destruct (SegModel.name_ok p); [reflexivity | discriminate Hc]. }
  rewrite Hyes in Hvs.
  assert (EV8 : bv_unsigned (ew E 8) = e_vid e) by (rewrite (EV 8%nat 8%bv eq_refl), G8; unfold w64; apply unsigned_lit_small; lia).
  assert (EV2 : bv_unsigned (ew E 2) = spZ (e_regs e) - 64) by (rewrite (EV 2%nat 2%bv eq_refl); exact Hsp).
  assert (Rok : region_ok SEGS E (mrestrict (w_H W') mem') vs_vid_r).
  { unfold region_ok, vs_vid_r. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite EV8. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); apply HVP; lia | constructor]. }
  assert (BV8 : base_val E (Some 8%nat) = e_vid e) by (cbn [base_val]; exact EV8).
  assert (BV2 : base_val E (Some 2%nat) = spZ (e_regs e) - 64) by (cbn [base_val]; exact EV2).
  lazymatch type of HS with st_ok_pi _ _ _ ?ss ?msx =>
  assert (Rdj : all_disjoint E vs_vid_r (ss_mem ss));
  [ cbn [ss_mem add_cond vs_ssK all_disjoint extent_disjoint vs_vid_r vs_slots_r YP09.r_base YP09.r_lo YP09.r_hi];
    unfold extent_disjoint; cbn [vs_vid_r vs_slots_r YP09.r_base YP09.r_lo YP09.r_hi];
    rewrite BV8, BV2; split; [|exact I]; destruct Vplace as [(_ & Hv1) | (Hv1 & _)]; lia
  | pose proof (st_ok_pi_add_region E ss msx vs_vid_r HS eq_refl Rok Rdj) as HS2; clear HS; rename HS2 into HS ] end.
  assert (SHOK6 : sh_ok SEGS vs_Bx vs_SH6 E (mrestrict (w_H W') mem')).
  { unfold sh_ok, vs_SH6. constructor; [|constructor].
    apply (shent_ok_of_range SEGS (w_H W') mem' E vs_Bx 8 (e_vid e) 2 (e_vid e) 0 2 HVA UB).
    - apply U_atom; [rewrite (EV 8%nat 8%bv eq_refl), G8; reflexivity | lia].
    - lia.
    - lia.
    - intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF.
      destruct Vplace as [(Hia & _) | (Hsv & _)]; [unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hia | ]; lia. }
  (* 0x8a3b4 `andi a0,s0,1`, 0x8a3b8 `bnez a0` -> unimp 0x8a3d8: refuted at the branch by the run itself: the seed
     fact of s0 (atom 8 in [4096, 2^47 - 2], 2-aligned, from split_pre's vid mod 2 = 0) makes decide_cond2 answer
     "not taken", so the run passes the branch to the store check 0x8a3bc. *)
  paj_run_to_tok RUNTO HS HJ SHOK6 vs_Bspan VS_KR.
  { lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr0 lyx own) end.
    eapply (@awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 8%nat (e_vid e)); [reflexivity | exact EV8 | |].
    - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
      destruct HNA as (HP & Ely & _).
      apply (vs_dst_awr B (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) (e_regs e) _ _ ly' S' [] (e_vid e) 2 a HAR Hvdst Ely HP);
        [| lia].
      unfold e_FP, split_W. rewrite Hvs. exists (e_vid e, e_vid e + 2).
      split; [apply in_or_app; right; left; reflexivity | cbn [fst snd]; lia].
    - repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  pmkst HS.
  lazymatch goal with Hfr : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => e_vid e <= a < e_vid e + 2) Hfr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?EV8 in Hrr; cbv beta; lia|]);
      destruct Hin)) as UN end.
  apply (vs_exit_KR B gotw guard HKR e ly' S' W' regs' mem' (ms_regs ms) (ms_mem ms) _ 1 HE HR HSL HJ).
  + intros r Hr.
    assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct Hcases as [-> | Hcases]); try subst r;
    lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
      let n := eval compute in (Z.to_nat k) in
      eapply (vs_reg_atom _ _ _ _ _ n _ HS); [repeat (rewrite ew_ewset_other by lia); apply EV; reflexivity | vm_compute; reflexivity] end.
  + intros a Ha. unfold e_sp in Ha. apply UN; [lia|]. cbv beta. destruct Vplace as [(_ & Hv1) | (Hv1 & _)]; lia.
  + pose proof (st_ok_pi_restrict_reg (w_H W') _ _ ms 10%bv HS) as F10.
    lazymatch type of F10 with _ = sv_denot _ (sr_get ?a ?r) =>
      let x := eval vm_compute in (sr_get a r) in change (sr_get a r) with x in F10 end.
    rewrite F10. reflexivity.
  + intros regs'' md'' H10''. unfold vs_Q. rewrite Hvs. split; [exact H10''|].
    assert (Hlp : length p = di) by (subst p; rewrite length_firstn; lia).
    split; [split|split].
    * destruct HPZ as [HPb HPn]. split; [|exact HPn]. intros i Hi. rewrite length_app, Hlp in Hi. cbn [length] in Hi.
      rewrite UN; [exact (HPb i ltac:(rewrite length_app, Hlp; cbn [length]; lia)) | lia |].
      cbv beta. unfold sa_disj in Hvdisj. lia.
    * lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
        let r := eval vm_compute in (nth 0 (ss_mem ss) vs_vid_r) in
        pose proof (st_ok_pi_region_nth _ ss _ 0 r HS ltac:(vm_compute; reflexivity)) as Rv end.
      pose proof (region_ok_chunk SEGS _ _ _ (YP09.mkChunk 0 (CVal 2 (SOff 21 0))) Rv (or_introl eq_refl)) as Hck.
      cbn [YP09.r_base base_val] in Hck. rewrite !ew_ewset_other in Hck by lia. rewrite EV8 in Hck.
      assert (Hsv : sv_denot (ewset (ewset E 1024 w) 1025 w0) (SOff 21 0) = Z_to_bv 64 v).
      { cbn [sv_denot]. rewrite !ew_ewset_other by lia. rewrite (EV 21%nat 21%bv eq_refl), R21.
        unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      pose proof (val_of_chunk_ok SEGS _ _ (e_vid e) 0 2 (SOff 21 0) v Hck Hsv ltac:(cbn; lia) ltac:(cbn; lia)) as Hval.
      intros k Hk. specialize (Hval k Hk). cbn [ms_mem restrict] in Hval. rewrite Z.add_0_r in Hval.
      unfold aview. rewrite Hval. cbn [option_map]. f_equal. change (N.to_nat 2) with 2%nat.
      rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small.
      cbv [YG0f.le_byte]. apply Z.mod_pos_bound. lia.
    * apply (vs_kept_step _ _ _ mem'); [apply (vs_kept_mono _ _ _ _ _ _ _ _ HKP)|].
      -- intros a Ha. unfold split_E. rewrite Hcopy. left. exact Ha.
      -- intros a Ha Hw He. apply UN; [exact Ha|]. cbv beta. intros Hva. apply He. unfold split_E. rewrite Hvs. right. exact Hva.
    * exact HNA.
Qed.
End e.
End f.
End d.
