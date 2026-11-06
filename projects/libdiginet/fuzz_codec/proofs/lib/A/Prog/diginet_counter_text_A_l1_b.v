(* Part b of one pass of diginet_counter_text's first loop in image A (diginet_counter_text_A_l1_base.v): the call
   of diginet_seg7 (0x860b4) through its contract cdc_seg7_specX, then from its return address 0x862e4: a1 := the
   pattern v, a0 := -11; bltz a1 (a character seg7 does not draw) or beq s11,8 (a ninth digit) to 0x864c0 (E_RANGE);
   else for a dot dot[n] := 1 (0x862fc .. 0x86318), s[n] := v and n := n + 1 (0x8631c .. 0x86334), to 0x86338. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YCeo.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_text.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgEncC CPgChkC CPgWalk CPgWalkKept CPgWalkFrame CPgWalkCall.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import diginet_counter_text_A_inv diginet_counter_text_A_l1_base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Ltac csv := unfold acallee_saved; vm_compute; repeat (first [ left; reflexivity | right ]); split; discriminate.

(* seg7 draws a byte as -1 or a 7-bit pattern *)
Lemma ctb_seg7_range : forall c, 0 <= c < 256 -> seg7_spec c = -1 \/ 0 <= seg7_spec c < 128.
Proof. intros c Hc. rewrite seg7_agree by exact Hc. apply owed_seg7_range. Qed.
Lemma ctb_inv_mono : forall n dot, ct_inv n dot -> n < 8 -> ct_inv (n + 1) dot.
Proof. intros n dot (Hn & Hl & Hz) H. split; [lia|]. split; [exact Hl|]. intros j Hj. apply Hz. lia. Qed.
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* the frame's shadow bytes kept by runs that wrote only bytes of the frame's variables *)
Lemma ctb_sh_now : forall (H : word -> bool) (m0 m : word -> option byte) F (Zn : Z -> Prop),
  F = 8 * (F / 8) -> in_app F 128 -> (forall a, Zn a -> F + 32 <= a < F + 96) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview tfibsegs H m a = aview tfibsegs H m0 a) ->
  garr8 tfibsegs (mrestrict H m0) (SB + F / 8) CT_FRAME_SHADOW ->
  garr8 tfibsegs (mrestrict H m) (SB + F / 8) CT_FRAME_SHADOW.
Proof.
intros H m0 m F Zn HF8 Happ HZ KE Hsh. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
apply (ctl_garr8_kept H H m0 m); [|exact Hsh]. intros x Hx. cbn [length CT_FRAME_SHADOW] in Hx.
change (Z.of_nat 16) with 16 in Hx. apply KE; [unfold SB in *; lia|]. intros Hz. pose proof (HZ x Hz). unfold SB in *. lia.
Qed.
End s.
(* the write windows of the run: dot[n] (atom 33) and s[n] (atom 34), inside the walk's own frame *)
Ltac hE34 := lazymatch goal with H : ew _ 34 = Z_to_bv 64 _ |- _ => rewrite H end.
Ltac hE34_in Hb := lazymatch goal with H : ew _ 34 = Z_to_bv 64 _ |- _ => rewrite H in Hb end.
Ltac awr_b :=
  cbn [ss_mem];
  lazymatch goal with |- awr_ok ?Ev ?rs _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat first
  [ apply awr_ok_nil
  | eapply awr_ok_cons_gen;
    [ reflexivity | ewpeel; first [hE33 | hE34]; apply unsigned_lit_small; lia
    | let a := fresh "a" in let Ha := fresh "Ha" in
      intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; exists 1; eexists;
      split; [left; reflexivity|];
      left; unfold in_zr; cbn [fst snd]; hEfa; change (fs_frame_bytes 1) with 128; hFa; lia
    | ] ].
Ltac kwr_b :=
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb); cbv beta;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  repeat (destruct Hr as [<- | Hr];
          [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; ewpeel_in Hb;
            first [hE33_in Hb | hE34_in Hb]; rewrite unsigned_lit_small in Hb by lia; lia | ]);
  destruct Hr.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables RLO RHI SEG7TBL : Z.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis SEG7 : cdc_seg7_specX tfibsegs B MT RLO RHI SEG7TBL A_SEG7.

Theorem ct_part_b_holds : ct_part_b B MT RLO RHI SEG7TBL.
Proof.
unfold ct_part_b. intros g pos fuel W2 c2 Hpre Hnow Hc.
destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HK & HP & Hni & Hio & Hmo & HC & HL).
destruct HL as (j & n & ch & s & dot & Rra & R10 & R24 & R18 & R19 & R22 & R20 & R21 & R26 & R27 & Hj & Hfuel & Hch &
  Hch0 & Hnz & Hct1 & Hnd & Hl1 & Harr & Hsj & Hdj).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (ctl_stack B g Hpre) as (Hceil & H47 & H46 & Hal & Hsp1 & Hsp1a & Hwin & Hsp0).
destruct (ctl_frame B LAWS g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (Hfr & Efa & Efl & HF0 & HFc & HF64 & HFapp & HFp).
pose proof HC as (R8 & R2 & R9 & R3 & R4 & R23 & R25 & _).
pose proof Hpre as ((HJc & _ & _ & Hgp & Htp & _ & _ & _ & Hev & Hlive) & _ & (Hq0 & Htb0 & Hin0 & _) & _ & _ & _ &
  Lsj & _).
pose proof (Hnow pos ly2 S2 W2 mem2 md2 HJ HK HP Hni) as ((Htb & _) & _ & _ & (Hrod & Hrot & Hcrd7)).
assert (Hjl : j + 1 < cg_len g) by (unfold cg_len; exact (ctl_tb_len (cg_tb g) j Hj Hin0 Hnz)).
assert (Hch8 : 0 <= ch < 256).
{ rewrite <- Hch. apply (proj2 (Htb (Z.to_nat j) ltac:(unfold cg_len in Hjl; lia))). }
assert (Hc8 : 0 <= ct_c ch < 256) by (unfold ct_c; destruct (ch =? 46); lia).
unfold T_counter_text, ESTACK in Hceil, Hwin, H46.
assert (Esp1 : spZ regs2 = cg_sp1 g) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
(* the call *)
eapply SRr_bind.
{ apply (SEG7 (cg_STK g) (cg_sp0 g) (cg_FP g) (cg_ly g) (cg_S g) (cg_W0 g) (cg_mem0 g) (cg_md0 g)
    ((1, pos) :: cg_own g) ly2 S2 W2 mem2 md2 (cg_k g) regs2 (ct_c ch)).
  - apply (cpw_entry B _ _ _ _ _ _ _ _ _ (cg_lyc g) (cg_Sc g)); [exact HJ | | | | | | | | exact Hev | exact HP | exact Hlive].
    + rewrite Rra. apply ret_ok_even. vm_compute. reflexivity.
    + unfold raZ. rewrite Rra. vm_compute. discriminate.
    + rewrite R3. exact Hgp.
    + rewrite R4. exact Htp.
    + rewrite Esp1. pose proof (Z.div_mod (cg_sp1 g) 32 ltac:(lia)) as D. rewrite Hsp1a, Z.add_0_r in D.
      rewrite D. replace (32 * (cg_sp1 g / 32)) with ((2 * (cg_sp1 g / 32)) * 16) by lia. apply Z_mod_mult.
    + rewrite Esp1. unfold T_seg7. lia.
    + rewrite Esp1. lia.
  - exact R10.
  - lia.
  - exact Hrod.
  - exact Hrot.
  - rewrite Esp1. exact Hcrd7. }
cbv beta. intros W3 c3 Hwle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hfrs3 & HPm3 & HIO3 & HMLE3 & HK3 & Rv).
rewrite Z.mod_small in Rv by lia. fold (ct1_v ch) in Rv. rewrite Esp1 in HK3.
unfold EV_CDC in HJ3. rewrite Z.add_0_r in HJ3.
(* what the walk carries across the call *)
assert (HPR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs3 r = getr regs2 r)
  by (intros r Hr; exact (ctl_pres regs2 regs3 r HP3 Hr)).
assert (G8 : getr regs3 8 = getr regs2 8) by (apply HPR; csv).
assert (G2 : getr regs3 2 = getr regs2 2) by (apply HPR; csv).
assert (G9 : getr regs3 9 = getr regs2 9) by (apply HPR; csv).
assert (G3 : getr regs3 3 = getr regs2 3) by (apply HPR; csv).
assert (G4 : getr regs3 4 = getr regs2 4) by (apply HPR; csv).
assert (G23 : getr regs3 23 = getr regs2 23) by (apply HPR; csv).
assert (G25 : getr regs3 25 = getr regs2 25) by (apply HPR; csv).
destruct (ctl_keep_call B LAWS g pos ly2 S2 regs2 mem2 md2 W2 regs3 mem3 W3 Hpre HJ HP HC HK3 G8 G2 G9 G3 G4 G23 G25)
  as (HC3 & KF3 & Ksj3 & Kdj3).
assert (HK3' : tcj_kept tfibsegs B T_counter_text (cg_lyc g) (cg_Sc g) (cg_W g) (cg_memc g) W3 mem3 (cg_sp g) (ct_wr g)).
{ apply (cw_kept_cj B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ W3 mem3 T_counter_text T_seg7
    (cg_sp g) (cg_sp1 g) (ct_wr g) cno_wr HJc HJ); [rewrite Hfr; intros x Hx; right; exact Hx | exact HP
  | unfold T_counter_text, ESTACK; lia | lia | unfold T_counter_text, T_seg7, ESTACK; lia | lia | intros a [] | exact HK
  | exact HK3]. }
destruct (cw_frame_step MT MTL B (cg_lyc g) (cg_Sc g) ly2 S2 ly3 S3 HP Hmo HPm3 HMLE3) as (HP3' & Hmo3).
pose proof (same_io_trans _ _ _ Hio HIO3) as Hio3.
destruct (ctl_frame B LAWS g pos ly3 S3 W3 mem3 md3 Hpre HJ3) as (Hfr3 & Efa3 & _ & _ & _ & _ & _ & HFp3).
pose proof HC3 as (R8' & R2' & R9' & R3' & R4' & R23' & R25' & _).
assert (Harr3 : ct_arrays g pos W3 mem3 n s dot).
{ destruct Harr as (Hd & Hs). split.
  - intros i Hi. apply (cw_val_mem_kept (w_H W2) (w_H W3) mem2 mem3); [|exact (Hd i Hi)].
    intros x Hx. cbn in Hx. apply KF3. lia.
  - intros i Hi. pose proof Hl1 as ((Hn0 & _) & _). apply (cw_val_mem_kept (w_H W2) (w_H W3) mem2 mem3); [|exact (Hs i Hi)].
    intros x Hx. cbn in Hx. apply KF3. lia. }
pose proof (Ksj3 Hsj) as Hsj3. pose proof (Kdj3 Hdj) as Hdj3.
clear HJ HK HP Hio Hmo HC Harr Hsj Hdj KF3 Ksj3 Kdj3 HK3 HPm3 HMLE3 HIO3 Hnow Hrod Hrot Hcrd7.
(* the state at 0x862e4 *)
set (F := cg_F g pos) in *.
assert (HFa : frame_addr (cg_lyc g) 1 pos = F) by reflexivity.
pose proof Hl1 as ((Hn0 & Hdl & Hdz) & Hd01 & Hsl & Hs128).
set (xs := [F + 64 + 4 * n; F + 32 + n]).
remember (Ereg regs3 (cw_extra xs)) as E eqn:HEE.
assert (EW : forall (i : nat) (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs3 r)
  by (intros i r Hi; subst E; exact (ew_Ereg_nat regs3 _ i r Hi)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (E33 : ew E 33 = Z_to_bv 64 (F + 64 + 4 * n)) by (subst E; exact (cw_ew_x regs3 xs 0)).
assert (E34 : ew E 34 = Z_to_bv 64 (F + 32 + n)) by (subst E; exact (cw_ew_x regs3 xs 1)).
assert (E10 : ew E 10 = w64 (ct1_v ch)) by (rewrite (EW 10%nat 10%bv eq_refl); exact Rv).
assert (E24 : ew E 24 = w64 ch) by (rewrite (EW 24%nat 24%bv eq_refl), HPR by csv; exact R24).
assert (E18 : ew E 18 = w64 46) by (rewrite (EW 18%nat 18%bv eq_refl), HPR by csv; exact R18).
assert (E19 : ew E 19 = w64 (cg_q g + j + 1)) by (rewrite (EW 19%nat 19%bv eq_refl), HPR by csv; exact R19).
assert (E22 : ew E 22 = w64 (cg_q g + j + 1)) by (rewrite (EW 22%nat 22%bv eq_refl), HPR by csv; exact R22).
assert (E20 : ew E 20 = w64 (cg_sg g)) by (rewrite (EW 20%nat 20%bv eq_refl), HPR by csv; exact R20).
assert (E21 : ew E 21 = w64 (F + 64)) by (rewrite (EW 21%nat 21%bv eq_refl), HPR by csv; exact R21).
assert (E26 : ew E 26 = w64 (F + 32)) by (rewrite (EW 26%nat 26%bv eq_refl), HPR by csv; exact R26).
assert (E27 : ew E 27 = w64 n) by (rewrite (EW 27%nat 27%bv eq_refl), HPR by csv; exact R27).
assert (YS : YP0l.st_ok tfibsegs E (mkSS PC_RET7 sr_atoms [] None
    (mkFacts [(32%nat, mkAF SB SB 0); (27%nat, mkAF 0 8 0); (33%nat, mkAF 4096 (2 ^ 47 - 8) 0);
              (34%nat, mkAF 4096 (2 ^ 47 - 8) 0)] [] []))
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 PC_RET7) mem3 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply entry_st_ok_full.
  - apply regs_ok_Ereg.
  - reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite cw_ew_SB, (ew_Ereg_nat regs3 _ 27 27%bv eq_refl), HPR by csv. rewrite R27, E33, E34. unfold w64.
    rewrite !unsigned_lit_small by (unfold SB; lia). rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB.
    repeat split; first [exact I | lia]. }
pose proof (ast_ok_set_reg_fp tfibsegs E _ _ (25%bv : bv 5) (SOff 32 0) YS eq_refl
  ltac:(cbn [ms_regs restrict mkst]; rewrite sv_denot_SOff0, E32, G25, R25; reflexivity)) as HS.
clear YS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W3) mem3)) by apply Forall_nil.
rename HJ3 into HJ. cw_keep_j0 HJ HJ0.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W3) mem3 a)
  by (intros; reflexivity).
assert (KP : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem3 a) by (intros; assumption).
(* the Gallina side of the pass *)
assert (Hvr : ct1_v ch = -1 \/ 0 <= ct1_v ch < 128) by (unfold ct1_v; apply ctb_seg7_range; exact Hc8).
assert (Hskip : skipn (Z.to_nat j) (cg_tb g) = ch :: skipn (S (Z.to_nat j)) (cg_tb g))
  by (rewrite <- Hch; apply skipn_cons_nth; unfold cg_len in Hjl; lia).
pose proof (ctl_ct1_digit ch (skipn (S (Z.to_nat j)) (cg_tb g)) n s dot Hch0 Hnd) as Hdig.
rewrite <- Hskip, Hct1 in Hdig.
rewrite Rra. change (w64 PC_RET7) with (Z_to_bv 64 PC_RET7).
cw_run_to awr_nil PC_X. ctk_keep cw_kwr_ro.
cw_branch Hb1.
all: rewrite (ctl_blt0 E 10 (ct1_v ch) E10 ltac:(lia)) in Hb1.
- (* v < 0: E_RANGE *)
  apply Z.ltb_lt in Hb1.
  assert (Hspec : counter_text_spec (cg_tb g) = (E_RANGE, [], 0))
    by (unfold counter_text_spec; rewrite Hdig, (proj2 (Z.ltb_lt _ _) Hb1); reflexivity).
  cw_run_to awr_nil PC_X. ctk_keep cw_kwr_ro.
  apply SRr_ret. cbv beta. right.
  lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
    apply (ctl_cut_close B MT LAWS g pos PC_X (P_X g) ly3 S3 regs3 mem3 md3 W3 msv _ Hpre HJ0 HK3' HP3' Hni Hio3
      Hmo3 HC3 HJ);
    [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
    | rfin | rfin | rfin | rfin | rfin | rfin | rfin
    | intros a Ha _; apply KE; [exact Ha | tauto] | exact KP | exact Hsj3 | exact Hdj3 | ] end.
  intros Ksj Kdj. unfold P_X, ct_res. rewrite Hspec.
  split; [rv; apply bv_eq; reflexivity|].
  split; [intros Hr; exfalso; unfold E_RANGE in Hr; lia|].
  intros _. exists (cg_sj g), (cg_dj g). split; [exact Ksj|]. split; [exact Lsj | exact Kdj].
- (* v >= 0: beq s11,8 *)
  apply Z.ltb_ge in Hb1.
  cw_run_to awr_nil PC_X. ctk_keep cw_kwr_ro.
  cw_branch Hb2.
  all: lazymatch type of Hb2 with branch_taken _ (sv_denot ?Ev _) _ = _ =>
    rewrite branch_eq_U, (U_atom Ev 27 n ltac:(ewpeel; exact E27) ltac:(lia)), U_lit in Hb2 by lia end.
  + (* n = 8: E_RANGE *)
    apply Z.eqb_eq in Hb2.
    assert (Hspec : counter_text_spec (cg_tb g) = (E_RANGE, [], 0))
      by (unfold counter_text_spec; rewrite Hdig; replace (n =? 8) with true by (symmetry; apply Z.eqb_eq; exact Hb2);
          rewrite orb_true_r; reflexivity).
    cw_run_to awr_nil PC_X. ctk_keep cw_kwr_ro.
    apply SRr_ret. cbv beta. right.
    lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
      apply (ctl_cut_close B MT LAWS g pos PC_X (P_X g) ly3 S3 regs3 mem3 md3 W3 msv _ Hpre HJ0 HK3' HP3' Hni Hio3
        Hmo3 HC3 HJ);
      [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
      | rfin | rfin | rfin | rfin | rfin | rfin | rfin
      | intros a Ha _; apply KE; [exact Ha | tauto] | exact KP | exact Hsj3 | exact Hdj3 | ] end.
    intros Ksj Kdj. unfold P_X, ct_res. rewrite Hspec.
    split; [rv; apply bv_eq; reflexivity|].
    split; [intros Hr; exfalso; unfold E_RANGE in Hr; lia|].
    intros _. exists (cg_sj g), (cg_dj g). split; [exact Ksj|]. split; [exact Lsj | exact Kdj].
  + (* n < 8: bne s8,s2 *)
    apply Z.eqb_neq in Hb2.
    cw_run_to awr_nil PC_X. ctk_keep cw_kwr_ro.
    cw_branch Hb3.
    all: lazymatch type of Hb3 with branch_taken _ (sv_denot ?Ev _) _ = _ =>
      rewrite branch_ne_U, (U_atom Ev 24 ch ltac:(ewpeel; exact E24) ltac:(lia)),
        (U_atom Ev 18 46 ltac:(ewpeel; exact E18) ltac:(lia)) in Hb3 end.
    * (* ch <> 46 *)
      apply negb_true_iff, Z.eqb_neq in Hb3.
      cw_run_to awr_nil 0x86320. ctk_keep cw_kwr_ro.
      pose proof HC3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsh3).
      assert (HF8 : F = 8 * (F / 8)).
      { pose proof (Z.div_mod F 64 ltac:(lia)) as D. pose proof (Z.div_mod F 8 ltac:(lia)) as D8.
        pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M8. lia. }
      (* a0 = s10 + s11 = F + 32 + n: atom 34 *)
      lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv (restrict ?Hh ?msv) |- _ =>
        pose proof (ast_ok_set_reg_fp tfibsegs Ev ssv (restrict Hh msv) (10%bv : bv 5) (SOff 34 0) HS eq_refl
          ltac:(cbn [ms_regs restrict]; rv0; rewrite sv_denot_SOff0; ewpeel; rewrite E34; symmetry;
                apply (ctl_den_add Ev 26 27 (F + 32) n); [ewpeel; exact E26 | ewpeel; exact E27 | lia | lia | lia]))
          as YS end.
      clear HS. rename YS into HS. norm_ss HS.
      lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
        assert (Hsn : garr8 tfibsegs (mrestrict (w_H W3) (ms_mem msv)) (SB + F / 8) CT_FRAME_SHADOW)
          by (apply (ctb_sh_now (w_H W3) mem3 (ms_mem msv) F (fun _ => False) HF8 HFapp);
              [intros a [] | exact KE | exact Hsh3]);
        assert (Hs_ok : region_ok tfibsegs Ev (mrestrict (w_H W3) (ms_mem msv)) (YP09.mkRegion (Some 34%nat) 0 1 0 1 []))
          by (unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
              ewpeel; rewrite E34, unsigned_lit_small by lia;
              split; [lia|]; split; [lia|];
              split; [intros o Ho; apply (YCbq.apresent_writable tfibsegs); apply KP; apply HFp3; lia | apply Forall_nil]);
        pose proof (ast_ok_add_region tfibsegs Ev ssv (restrict (w_H W3) msv) (YP09.mkRegion (Some 34%nat) 0 1 0 1 [])
          HS eq_refl Hs_ok I) as YS;
        clear HS; rename YS into HS; norm_ss HS;
        clear SHOK;
        assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 34 0 1] Ev (mrestrict (w_H W3) (ms_mem msv)))
          by (apply Forall_cons; [|apply Forall_nil];
              apply (cw_shent_ra W3 (ms_mem msv) Ev 34 (F + 32 + n) 1);
              [ replace (F + 32 + n) with (F + (32 + n)) by lia;
                apply ctl_ra_var; [rewrite HF8, Z.mul_comm; apply Z_mod_mult | lia | left; lia | exact Hsn]
              | unfold amem_range, in_app, kLowShadowBeg, ASAN_CEIL in *; rewrite C3, C4, C5 in *; lia
              | lia | lia | lia | ewpeel; exact E34 | ewpeel; exact E32 ]);
        assert (KE' : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 + n <= a < F + 33 + n) ->
          aview tfibsegs (w_H W3) (ms_mem msv) a = aview tfibsegs (w_H W3) mem3 a)
          by (intros a Ha _; apply KE; [exact Ha | tauto]) end.
      clear KE. rename KE' into KE.
      cw_run_to awr_b PC_NEXT. ctk_keep kwr_b.
      lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
        pose proof (st_ok_region_nth Ev ssv (restrict (w_H W3) msv) 0 _ HS eq_refl) as HR;
        cbn [ms_mem restrict] in HR;
        pose proof (field_of_region Ev _ 34 (F + 32 + n) _ 0 1 0 1 0 1%N (SOff 10 0) (ct1_v ch) HR
          ltac:(ewpeel; rewrite E34; apply unsigned_lit_small; lia) ltac:(left; reflexivity)
          ltac:(rewrite sv_denot_SOff0; ewpeel; exact E10) ltac:(cbn; lia) ltac:(cbn; lia)) as Vs end.
      rewrite Z.add_0_r in Vs. change (N.to_nat 1) with 1%nat in Vs.
      assert (Hct1' : ct1_lib (skipn (S (Z.to_nat j)) (cg_tb g)) (n + 1) (s ++ [ct1_v ch]) dot =
                      ct1_lib (cg_tb g) 0 [] (repeat 0 8)).
      { rewrite Hdig, (proj2 (Z.ltb_ge _ _) Hb1), (proj2 (Z.eqb_neq _ _) Hb2), (proj2 (Z.eqb_neq _ _) Hb3).
        reflexivity. }
      apply SRr_ret. cbv beta. left.
      lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
        apply (ctl_cut_close B MT LAWS g pos PC_NEXT (P_N g pos fuel) ly3 S3 regs3 mem3 md3 W3 msv _ Hpre HJ0 HK3' HP3'
          Hni Hio3 Hmo3 HC3 HJ);
        [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
        | rfin | rfin | rfin | rfin | rfin | rfin | rfin
        | intros a Ha Hz; apply KE; [exact Ha | intros Hd; apply Hz; unfold ct_zv; lia]
        | exact KP | exact Hsj3 | exact Hdj3 | ] end.
      intros Ksj Kdj. exists j, (n + 1), (s ++ [ct1_v ch]), dot.
      split; [rfin|]. split; [rfin|]. split; [rfin|]. split; [rfin|]. split; [rfin|]. split; [rfin|].
      split; [rv0; lazymatch goal with HS : YP0l.st_ok _ ?Ev _ _ |- _ =>
        rewrite denot_lit_U, (U_atom_off Ev 27 n 1 ltac:(ewpeel; exact E27) ltac:(lia) ltac:(lia)) end; reflexivity|].
      split; [exact Hj|]. split; [exact Hfuel|]. split; [exact Hnz|]. split; [exact Hct1'|].
      split; [split; [exact (ctb_inv_mono n dot (conj Hn0 (conj Hdl Hdz)) ltac:(lia))|];
              split; [exact Hd01|]; split; [rewrite length_app, Hsl; cbn [length]; lia|];
              apply Forall_app; split; [exact Hs128 | constructor; [lia | constructor]]|].
      split; [|split; [exact Ksj | exact Kdj]].
      apply (ctl_arrays_next g pos W3 mem3 _ n s dot dot (ct1_v ch) false ltac:(lia) Hsl Hdl eq_refl);
        [ intros a Ha Hne _; apply KE; [lia | lia] | exact Vs | intros Hf; discriminate Hf | exact Harr3 ].
    * (* ch = 46: dot[n] := 1 first *)
      apply negb_false_iff, Z.eqb_eq in Hb3.
      cw_run_to awr_nil 0x86304. ctk_keep cw_kwr_ro.
      pose proof HC3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsh3).
      assert (HF8 : F = 8 * (F / 8)).
      { pose proof (Z.div_mod F 64 ltac:(lia)) as D. pose proof (Z.div_mod F 8 ltac:(lia)) as D8.
        pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M8. lia. }
      (* a0 = s5 + (s11 << 2) = F + 64 + 4 n: atom 33 *)
      lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv (restrict ?Hh ?msv) |- _ =>
        pose proof (ast_ok_set_reg_fp tfibsegs Ev ssv (restrict Hh msv) (10%bv : bv 5) (SOff 33 0) HS eq_refl
          ltac:(cbn [ms_regs restrict]; rv0; rewrite sv_denot_SOff0; ewpeel; rewrite E33; symmetry;
                replace (F + 64 + 4 * n) with (F + 64 + 0 + 4 * n) by lia;
                apply (ctl_den_dot Ev 21 27 (F + 64) n 0); [ewpeel; exact E21 | ewpeel; exact E27 | lia | lia | lia | lia]))
          as YS end.
      clear HS. rename YS into HS. norm_ss HS.
      lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
        assert (Hsn : garr8 tfibsegs (mrestrict (w_H W3) (ms_mem msv)) (SB + F / 8) CT_FRAME_SHADOW)
          by (apply (ctb_sh_now (w_H W3) mem3 (ms_mem msv) F (fun _ => False) HF8 HFapp);
              [intros a [] | exact KE | exact Hsh3]);
        assert (Hd_ok : region_ok tfibsegs Ev (mrestrict (w_H W3) (ms_mem msv)) (YP09.mkRegion (Some 33%nat) 0 4 0 4 []))
          by (unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
              ewpeel; rewrite E33, unsigned_lit_small by lia;
              split; [lia|]; split; [lia|];
              split; [intros o Ho; apply (YCbq.apresent_writable tfibsegs); apply KP; apply HFp3; lia | apply Forall_nil]);
        pose proof (ast_ok_add_region tfibsegs Ev ssv (restrict (w_H W3) msv) (YP09.mkRegion (Some 33%nat) 0 4 0 4 [])
          HS eq_refl Hd_ok I) as YS;
        clear HS; rename YS into HS; norm_ss HS;
        clear SHOK;
        assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 33 0 4] Ev (mrestrict (w_H W3) (ms_mem msv)))
          by (apply Forall_cons; [|apply Forall_nil];
              apply (cw_shent_ra W3 (ms_mem msv) Ev 33 (F + 64 + 4 * n) 4);
              [ replace (F + 64 + 4 * n) with (F + (64 + 4 * n)) by lia;
                apply ctl_ra_var; [rewrite HF8, Z.mul_comm; apply Z_mod_mult | lia | right; lia | exact Hsn]
              | unfold amem_range, in_app, kLowShadowBeg, ASAN_CEIL in *; rewrite C3, C4, C5 in *; lia
              | lia | lia | lia | ewpeel; exact E33 | ewpeel; exact E32 ]);
        assert (KE' : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 64 + 4 * n <= a < F + 68 + 4 * n) ->
          aview tfibsegs (w_H W3) (ms_mem msv) a = aview tfibsegs (w_H W3) mem3 a)
          by (intros a Ha _; apply KE; [exact Ha | tauto]) end.
      clear KE. rename KE' into KE.
      cw_run_to awr_b 0x86320. ctk_keep kwr_b.
      (* a0 = s10 + s11 = F + 32 + n: atom 34 *)
      lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv (restrict ?Hh ?msv) |- _ =>
        pose proof (ast_ok_set_reg_fp tfibsegs Ev ssv (restrict Hh msv) (10%bv : bv 5) (SOff 34 0) HS eq_refl
          ltac:(cbn [ms_regs restrict]; rv0; rewrite sv_denot_SOff0; ewpeel; rewrite E34; symmetry;
                apply (ctl_den_add Ev 26 27 (F + 32) n); [ewpeel; exact E26 | ewpeel; exact E27 | lia | lia | lia]))
          as YS end.
      clear HS. rename YS into HS. norm_ss HS.
      lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
        assert (Hsn2 : garr8 tfibsegs (mrestrict (w_H W3) (ms_mem msv)) (SB + F / 8) CT_FRAME_SHADOW)
          by (apply (ctb_sh_now (w_H W3) mem3 (ms_mem msv) F (fun a => F + 64 + 4 * n <= a < F + 68 + 4 * n) HF8 HFapp);
              [intros a Ha; lia | exact KE | exact Hsh3]);
        assert (Hs_ok : region_ok tfibsegs Ev (mrestrict (w_H W3) (ms_mem msv)) (YP09.mkRegion (Some 34%nat) 0 1 0 1 []))
          by (unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
              ewpeel; rewrite E34, unsigned_lit_small by lia;
              split; [lia|]; split; [lia|];
              split; [intros o Ho; apply (YCbq.apresent_writable tfibsegs); apply KP; apply HFp3; lia | apply Forall_nil]);
        assert (Hs_dj : all_disjoint Ev (YP09.mkRegion (Some 34%nat) 0 1 0 1 []) (ss_mem ssv))
          by (cbn [ss_mem all_disjoint]; unfold extent_disjoint;
              cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; ewpeel; rewrite E33, E34, !unsigned_lit_small by lia;
              split; [lia | exact I]);
        pose proof (ast_ok_add_region tfibsegs Ev ssv (restrict (w_H W3) msv) (YP09.mkRegion (Some 34%nat) 0 1 0 1 [])
          HS eq_refl Hs_ok Hs_dj) as YS;
        clear HS; rename YS into HS; norm_ss HS;
        clear SHOK;
        assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 33 0 4; mkSHE 34 0 1] Ev (mrestrict (w_H W3) (ms_mem msv)))
          by (apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
              [ apply (cw_shent_ra W3 (ms_mem msv) Ev 33 (F + 64 + 4 * n) 4);
                [ replace (F + 64 + 4 * n) with (F + (64 + 4 * n)) by lia;
                  apply ctl_ra_var; [rewrite HF8, Z.mul_comm; apply Z_mod_mult | lia | right; lia | exact Hsn2]
                | unfold amem_range, in_app, kLowShadowBeg, ASAN_CEIL in *; rewrite C3, C4, C5 in *; lia
                | lia | lia | lia | ewpeel; exact E33 | ewpeel; exact E32 ]
              | apply (cw_shent_ra W3 (ms_mem msv) Ev 34 (F + 32 + n) 1);
                [ replace (F + 32 + n) with (F + (32 + n)) by lia;
                  apply ctl_ra_var; [rewrite HF8, Z.mul_comm; apply Z_mod_mult | lia | left; lia | exact Hsn2]
                | unfold amem_range, in_app, kLowShadowBeg, ASAN_CEIL in *; rewrite C3, C4, C5 in *; lia
                | lia | lia | lia | ewpeel; exact E34 | ewpeel; exact E32 ] ]);
        assert (KE' : forall a, 0 <= a < 2 ^ 64 ->
          ~ (F + 64 + 4 * n <= a < F + 68 + 4 * n \/ F + 32 + n <= a < F + 33 + n) ->
          aview tfibsegs (w_H W3) (ms_mem msv) a = aview tfibsegs (w_H W3) mem3 a)
          by (intros a Ha Hz; apply KE; [exact Ha | tauto]) end.
      clear KE. rename KE' into KE.
      cw_run_to awr_b PC_NEXT. ctk_keep kwr_b.
      lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
        pose proof (st_ok_region_nth Ev ssv (restrict (w_H W3) msv) 0 _ HS eq_refl) as HR;
        pose proof (st_ok_region_nth Ev ssv (restrict (w_H W3) msv) 1 _ HS eq_refl) as HR1;
        cbn [ms_mem restrict] in HR, HR1;
        pose proof (field_of_region Ev _ 34 (F + 32 + n) _ 0 1 0 1 0 1%N (SOff 10 0) (ct1_v ch) HR
          ltac:(ewpeel; rewrite E34; apply unsigned_lit_small; lia) ltac:(left; reflexivity)
          ltac:(rewrite sv_denot_SOff0; ewpeel; exact E10) ltac:(cbn; lia) ltac:(cbn; lia)) as Vs;
        pose proof (field_of_region Ev _ 33 (F + 64 + 4 * n) _ 0 4 0 4 0 4%N (SLit 1) 1 HR1
          ltac:(ewpeel; rewrite E33; apply unsigned_lit_small; lia) ltac:(left; reflexivity) eq_refl
          ltac:(cbn; lia) ltac:(cbn; lia)) as Vd end.
      rewrite Z.add_0_r in Vs, Vd. change (N.to_nat 1) with 1%nat in Vs. change (N.to_nat 4) with 4%nat in Vd.
      assert (Hct1' : ct1_lib (skipn (S (Z.to_nat j)) (cg_tb g)) (n + 1) (s ++ [ct1_v ch]) (upd_at dot n 1) =
                      ct1_lib (cg_tb g) 0 [] (repeat 0 8)).
      { rewrite Hdig, (proj2 (Z.ltb_ge _ _) Hb1), (proj2 (Z.eqb_neq _ _) Hb2), (proj2 (Z.eqb_eq _ _) Hb3).
        reflexivity. }
      apply SRr_ret. cbv beta. left.
      lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
        apply (ctl_cut_close B MT LAWS g pos PC_NEXT (P_N g pos fuel) ly3 S3 regs3 mem3 md3 W3 msv _ Hpre HJ0 HK3' HP3'
          Hni Hio3 Hmo3 HC3 HJ);
        [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
        | rfin | rfin | rfin | rfin | rfin | rfin | rfin
        | intros a Ha Hz; apply KE; [exact Ha | intros Hd; apply Hz; unfold ct_zv; lia]
        | exact KP | exact Hsj3 | exact Hdj3 | ] end.
      intros Ksj Kdj. exists j, (n + 1), (s ++ [ct1_v ch]), (upd_at dot n 1).
      split; [rfin|]. split; [rfin|]. split; [rfin|]. split; [rfin|]. split; [rfin|]. split; [rfin|].
      split; [rv0; lazymatch goal with HS : YP0l.st_ok _ ?Ev _ _ |- _ =>
        rewrite denot_lit_U, (U_atom_off Ev 27 n 1 ltac:(ewpeel; exact E27) ltac:(lia) ltac:(lia)) end; reflexivity|].
      split; [exact Hj|]. split; [exact Hfuel|]. split; [exact Hnz|]. split; [exact Hct1'|].
      split; [split; [exact (ct_inv_next n dot 1 (conj Hn0 (conj Hdl Hdz)) ltac:(lia))|];
              split; [apply ctl_Forall_upd_at; [exact Hd01 | lia]|]; split; [rewrite length_app, Hsl; cbn [length]; lia|];
              apply Forall_app; split; [exact Hs128 | constructor; [lia | constructor]]|].
      split; [|split; [exact Ksj | exact Kdj]].
      apply (ctl_arrays_next g pos W3 mem3 _ n s dot (upd_at dot n 1) (ct1_v ch) true ltac:(lia) Hsl Hdl eq_refl);
        [ intros a Ha Hne Hnd'; apply KE; [lia | intros [Hz | Hz]; [apply Hnd'; split; [reflexivity | lia] | lia]]
        | exact Vs | intros _; exact Vd | exact Harr3 ].
Time Qed.
End d.
