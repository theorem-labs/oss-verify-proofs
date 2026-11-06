(* Part a of one pass of diginet_counter_text's first loop in image B (diginet_counter_text_B_l1_base.v): from the
   loop head 0x86b74 (s5 := zext.b a1 = ch) a byte that is not a dot, a dot with n = 0, or a dot after a digit whose
   dot is set runs to the call of diginet_seg7 (a0 = ct_c ch, ra = 0x86bc0). A dot after a digit whose dot is clear
   passes the UBSan checks of 0x86b84 (n < 9) and 0x86b90 (4 n - 4 <= ~(F + 64): no wrap), the instrumented check of
   the 4-byte word dot[n - 1] at a0 = F + 60 + 4 n (its shadow byte is 00, so the error paths 0x86c74 / 0x86c94 are
   not taken), and with dot[n - 1] = 0 stores 1 there (0x86c60) and goes to 0x86c28. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_text.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgEncU CPgChkU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkU CPgWalkKeptU CPgWalkFrameU CPgWalkCallU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import diginet_counter_text_B_inv diginet_counter_text_B_l1_base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the write window of dot[n - 1] (atom 33, F + 60 + 4 n) is the walk's own frame *)
Ltac awr_dp :=
  cbn [ss_mem];
  lazymatch goal with |- awr_ok ?Ev _ _ _ _ _ _ _ _ =>
    eapply (awr_ok_cons_gen Ev _ _ _ _ _ _ _ _ _ 33%nat);
    [ reflexivity | ewpeel; hE33; apply unsigned_lit_small; lia | | apply awr_ok_nil ] end;
  let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; exists 1; eexists; split; [left; reflexivity|];
  left; unfold in_zr; cbn [fst snd]; hEfa; change (fs_frame_bytes 1) with 128; hFa; lia.
Ltac kwr_dp :=
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb); cbv beta;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; ewpeel_in Hb;
  hE33_in Hb; rewrite unsigned_lit_small in Hb by lia; lia.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables RLO RHI SEG7TBL : Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

Theorem ct_part_a_holds : ct_part_a B MT RLO RHI SEG7TBL.
Proof.
unfold ct_part_a. intros g pos fuel W2 c2 Hpre Hnow Hc.
destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HK & HP & Hni & Hio & Hmo & HC & HL).
destruct HL as (j & n & ch & s & dot & R11 & R20 & R22 & R23 & R25 & R27 & R29 & R18 & R19 & Hj & Hfuel & Hch & Hch0 &
  Hnz & Hct1 & Hl1 & Harr & Hsj & Hdj).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (ctl_stack B g Hpre) as (Hceil & H47 & H46 & Hal & Hsp1 & Hsp1a & Hwin & Hsp0).
destruct (ctl_frame B LAWS g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (Hfr & Efa & Efl & HF0 & HFc & HF64 & HFapp & HFp).
pose proof HC as (R8 & R2 & R9 & R3 & R4 & R24 & R26 & _).
set (F := cg_F g pos) in *.
assert (HFa : frame_addr (cg_lyc g) 1 pos = F) by reflexivity.
set (xs := [F + 60 + 4 * n; nth (Z.to_nat (n - 1)) dot 0]).
remember (Ereg regs2 (cw_extra xs)) as E eqn:HEE.
pose proof Hl1 as ((Hn0 & Hdl & Hdz) & Hd01 & Hsl & Hs128).
assert (Hn8 : n <= 8) by lia.
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (E11 : ew E 11 = Z_to_bv 64 ch) by (subst E; rewrite (ew_Ereg_nat regs2 _ 11 11%bv eq_refl), R11; reflexivity).
assert (E25 : ew E 25 = Z_to_bv 64 n) by (subst E; rewrite (ew_Ereg_nat regs2 _ 25 25%bv eq_refl), R25; reflexivity).
assert (E29 : ew E 29 = Z_to_bv 64 (F + 64)) by (subst E; rewrite (ew_Ereg_nat regs2 _ 29 29%bv eq_refl), R29; reflexivity).
assert (E19 : ew E 19 = Z_to_bv 64 (cw_not (F + 64)))
  by (subst E; rewrite (ew_Ereg_nat regs2 _ 19 19%bv eq_refl), R19; reflexivity).
assert (E33 : ew E 33 = Z_to_bv 64 (F + 60 + 4 * n)) by (subst E; exact (cw_ew_x regs2 xs 0)).
assert (E34 : ew E 34 = Z_to_bv 64 (nth (Z.to_nat (n - 1)) dot 0)) by (subst E; exact (cw_ew_x regs2 xs 1)).
(* the head's registers the boundaries carry, in their w64 form (rfin's assumption) *)
assert (E22w : ew E 22 = w64 (cg_q g + j)) by (subst E; rewrite (ew_Ereg_nat regs2 _ 22 22%bv eq_refl); exact R22).
assert (E23w : ew E 23 = w64 (cg_q g + j + 1)) by (subst E; rewrite (ew_Ereg_nat regs2 _ 23 23%bv eq_refl); exact R23).
assert (E25w : ew E 25 = w64 n) by exact E25.
assert (E27w : ew E 27 = w64 (F + 32)) by (subst E; rewrite (ew_Ereg_nat regs2 _ 27 27%bv eq_refl); exact R27).
assert (E29w : ew E 29 = w64 (F + 64)) by exact E29.
assert (E18w : ew E 18 = w64 (cw_not (F + 32))) by (subst E; rewrite (ew_Ereg_nat regs2 _ 18 18%bv eq_refl); exact R18).
assert (E19w : ew E 19 = w64 (cw_not (F + 64))) by exact E19.
(* the start: s10 = SB (atom 32), s4 = 46; n in [0, 8], s3 = ~(F + 64) at least 2 ^ 63 *)
assert (YS : YP0l.st_ok tfibsegs E (mkSS PC_L1 sr_atoms [] None
  (mkFacts [(32%nat, mkAF SB SB 0); (25%nat, mkAF 0 8 0); (19%nat, mkAF (2 ^ 63) (2 ^ 64 - 1) 0)] [] []))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 PC_L1) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply entry_st_ok_full.
  - apply regs_ok_Ereg.
  - reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite cw_ew_SB, (ew_Ereg_nat regs2 _ 25 25%bv eq_refl), (ew_Ereg_nat regs2 _ 19 19%bv eq_refl), R25, R19.
    unfold w64, cw_not. rewrite !unsigned_lit_small by (unfold SB; lia). rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB.
    repeat split; first [exact I | lia]. }
pose proof (ast_ok_set_reg_fp tfibsegs E _ _ (26%bv : bv 5) (SOff 32 0) YS eq_refl
  ltac:(cbn [ms_regs restrict mkst]; rewrite sv_denot_SOff0, E32, R26; reflexivity)) as HS.
clear YS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
pose proof (ast_ok_set_reg_fp tfibsegs E _ _ (20%bv : bv 5) (SLit 46) HS eq_refl
  ltac:(cbn [ms_regs restrict mkst]; rewrite R20; reflexivity)) as YS.
clear HS. rename YS into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W2) mem2)) by apply Forall_nil.
cw_keep_j0 HJ HJ0.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a)
  by (intros; reflexivity).
assert (KP : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem2 a) by (intros; assumption).
(* values of the boundary *)
pose proof Hpre as (_ & _ & (Hq0 & Htb0 & Hin0 & Hqcrd) & _).
specialize (Hnow pos ly2 S2 W2 mem2 md2 HJ0 HK HP Hni) as ((Htb & Htra) & Hsgra & Hdtra & (Hrod & Hrot & Hcrd7)).
assert (Hjl : j + 1 < cg_len g) by (unfold cg_len; exact (ctl_tb_len (cg_tb g) j Hj Hin0 Hnz)).
assert (Hch8 : 0 <= ch < 256).
{ rewrite <- Hch. apply (proj2 (Htb (Z.to_nat j) ltac:(unfold cg_len in Hjl; lia))). }
assert (HF8 : F = 8 * (F / 8)).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. pose proof (Z.div_mod F 8 ltac:(lia)) as D8.
  pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M8. lia. }
unfold cfg_at. change (w64 PC_L1) with (Z_to_bv 64 PC_L1).
cw_run_to awr_nil B_SEG7. ctk_keep cw_kwr_ro.
cw_branch Hc1.
all: rewrite branch_ne_U, U_and_lit, (U_atom E 11 ch E11 ltac:(lia)), U_lit, ctl_land255 in Hc1 by lia.
- (* ch <> 46: to the call *)
  apply negb_true_iff, Z.eqb_neq in Hc1.
  cw_run_to awr_nil B_SEG7. ctk_keep cw_kwr_ro.
  apply SRr_ret. cbv beta. left.
  lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
    apply (ctl_cut_close B MT LAWS g pos B_SEG7 (P_C g pos fuel) ly2 S2 regs2 mem2 md2 W2 msv _ Hpre HJ0 HK HP Hni Hio
      Hmo HC HJ);
    [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
    | rfin | rfin | rfin | rfin | rfin | rfin | rfin
    | intros a Ha _; apply KE; [exact Ha | tauto] | exact KP | exact Hsj | exact Hdj | ] end.
  intros Ksj Kdj. exists j, n, ch, s, dot.
  split; [rfin|]. split; [rand; unfold ct_c, w64; rewrite (proj2 (Z.eqb_neq ch 46) Hc1); reflexivity|].
  split; [rand; reflexivity|].
  split; [rfin|]. split; [rfin|]. split; [rfin|]. split; [rfin|]. split; [rfin|]. split; [rfin|]. split; [rfin|].
  split; [exact Hj|]. split; [exact Hfuel|]. split; [exact Hch|]. split; [exact Hch0|]. split; [exact Hnz|].
  split; [exact Hct1|]. split; [intros (Hx46 & _); exact (Hc1 Hx46)|]. split; [exact Hl1|].
  split; [|split; [exact Ksj | exact Kdj]].
  apply (ctl_arrays_kept g pos W2 mem2 _ n s dot); [intros a Ha; apply KE; [lia | tauto] | exact Hn8 | exact Harr].
- (* ch = 46: blez s9 *)
  apply negb_false_iff, Z.eqb_eq in Hc1.
  cw_run_to awr_nil B_SEG7. ctk_keep cw_kwr_ro.
  cw_branch Hc2.
  all: rewrite (ctl_bge0 E 25 n E25 ltac:(lia)) in Hc2.
  + (* n <= 0: the dot draws as ' ' *)
    apply Z.leb_le in Hc2.
    cw_run_to awr_nil B_SEG7. ctk_keep cw_kwr_ro.
    apply SRr_ret. cbv beta. left.
    lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
      apply (ctl_cut_close B MT LAWS g pos B_SEG7 (P_C g pos fuel) ly2 S2 regs2 mem2 md2 W2 msv _ Hpre HJ0 HK HP Hni Hio
        Hmo HC HJ);
      [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
      | rfin | rfin | rfin | rfin | rfin | rfin | rfin
      | intros a Ha _; apply KE; [exact Ha | tauto] | exact KP | exact Hsj | exact Hdj | ] end.
    intros Ksj Kdj. exists j, n, ch, s, dot.
    split; [rfin|]. split; [rv; rewrite Hc1; reflexivity|].
    split; [rand; reflexivity|].
    split; [rfin|]. split; [rfin|]. split; [rfin|]. split; [rfin|]. split; [rfin|]. split; [rfin|]. split; [rfin|].
    split; [exact Hj|]. split; [exact Hfuel|]. split; [exact Hch|]. split; [exact Hch0|]. split; [exact Hnz|].
    split; [exact Hct1|]. split; [intros (_ & Hn' & _); lia|]. split; [exact Hl1|].
    split; [|split; [exact Ksj | exact Kdj]].
    apply (ctl_arrays_kept g pos W2 mem2 _ n s dot); [intros a Ha; apply KE; [lia | tauto] | exact Hn8 | exact Harr].
  + (* n > 0: the UBSan checks, then dot[n - 1] *)
    apply Z.leb_gt in Hc2.
    cw_run_to awr_nil 0x86b98. ctk_keep cw_kwr_ro.
    (* bltu s3,a0 (0x86b90): ~(F + 64) is at least 2 ^ 63, a0 = 4 n - 4 is small, so the trap is not taken *)
    cw_branch Hub.
    all: lazymatch type of Hub with branch_taken _ (sv_denot ?Ev _) _ = _ =>
      rewrite branch_ltu_U, (U_atom Ev 19 (cw_not (F + 64)) ltac:(ewpeel; exact E19) ltac:(unfold cw_not; lia)),
        (cw_U_m4 Ev 25 n ltac:(ewpeel; exact E25) ltac:(lia)) in Hub end.
    all: try (exfalso; apply Z.ltb_lt in Hub; unfold cw_not in Hub; lia).
    cw_run_to awr_nil 0x86b98. ctk_keep cw_kwr_ro.
    (* a0 = t4 + 4 n - 4 = F + 60 + 4 n, the address of dot[n - 1]: pinned to atom 33 *)
    lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv (restrict ?Hh ?msv) |- _ =>
      pose proof (ast_ok_set_reg_fp tfibsegs Ev ssv (restrict Hh msv) (10%bv : bv 5) (SOff 33 0) HS eq_refl
        ltac:(cbn [ms_regs restrict]; rv0; rewrite sv_denot_SOff0; ewpeel; rewrite E33;
              replace (F + 60 + 4 * n) with ((F + 64) - 4 + 4 * n) by lia; symmetry;
              apply (cw_den_dot Ev 29 25 (F + 64) n); [ewpeel; exact E29 | ewpeel; exact E25 | lia | lia | lia]))
        as YS end.
    clear HS. rename YS into HS. norm_ss HS.
    set (dv := nth (Z.to_nat (n - 1)) dot 0) in *.
    assert (Hdv : 0 <= dv <= 1) by (apply (nth_Forall (fun x => 0 <= x <= 1)); [exact Hd01 | lia]).
    add_fact HS 33%nat 4096 (2 ^ 47 - 8) E33 lia.
    add_fact HS 34%nat 0 1 E34 lia.
    norm_ss HS.
    (* the shadow and dot[n - 1] at the current memory *)
    pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & Hsh).
    lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
      assert (Hsh1 : garr8 tfibsegs (mrestrict (w_H W2) (ms_mem msv)) (SB + F / 8) CT_FRAME_SHADOW)
        by (apply (ctl_garr8_kept (w_H W2) (w_H W2) mem2 (ms_mem msv)); [|exact Hsh];
            intros x Hx; cbn [length CT_FRAME_SHADOW] in Hx; change (Z.of_nat 16) with 16 in Hx;
            apply KE; [unfold SB in *; lia | tauto]);
      assert (Vdp : val_mem tfibsegs (mrestrict (w_H W2) (ms_mem msv)) (F + 60 + 4 * n) 4 dv)
        by (apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 (ms_mem msv)); [intros x Hx; apply KE; [lia | tauto]|];
            replace (F + 60 + 4 * n) with (F + 64 + 4 * (n - 1)) by lia; exact (proj1 Harr (n - 1) ltac:(lia)));
      assert (Hdp_ok : region_ok tfibsegs Ev (mrestrict (w_H W2) (ms_mem msv))
          (YP09.mkRegion (Some 33%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 34 0))]))
        by (unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
            ewpeel; rewrite E33, unsigned_lit_small by lia;
            split; [lia|]; split; [lia|]; split;
            [ intros o Ho; apply (YCbq.apresent_writable tfibsegs); apply KP; apply HFp; lia
            | apply Forall_cons; [|apply Forall_nil];
              apply (chunk_ok_val tfibsegs Ev _ (F + 60 + 4 * n) 0 4 (SOff 34 0) dv);
              [ rewrite sv_denot_SOff0; ewpeel; exact E34 | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vdp ] ]);
      pose proof (ast_ok_add_region tfibsegs Ev ssv (restrict (w_H W2) msv)
        (YP09.mkRegion (Some 33%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 34 0))]) HS eq_refl Hdp_ok I) as YS;
      clear HS; rename YS into HS; norm_ss HS;
      clear SHOK;
      assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 33 0 4] Ev (mrestrict (w_H W2) (ms_mem msv)))
        by (apply Forall_cons; [|apply Forall_nil];
            apply (cw_shent_ra W2 (ms_mem msv) Ev 33 (F + 60 + 4 * n) 4);
            [ replace (F + 60 + 4 * n) with (F + (60 + 4 * n)) by lia;
              apply ctl_ra_var; [rewrite HF8, Z.mul_comm; apply Z_mod_mult | lia | right; lia | exact Hsh1]
            | unfold amem_range, in_app, kLowShadowBeg, ASAN_CEIL in *; rewrite C3, C4, C5 in *; lia
            | lia | lia | lia | ewpeel; exact E33 | ewpeel; exact E32 ]) end.
    lazymatch goal with HS : YP0l.st_ok _ _ _ (restrict _ ?msv) |- _ =>
      assert (KE' : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 60 + 4 * n <= a < F + 64 + 4 * n) ->
        aview tfibsegs (w_H W2) (ms_mem msv) a = aview tfibsegs (w_H W2) mem2 a)
        by (intros a Ha _; apply KE; [exact Ha | tauto]) end.
    clear KE. rename KE' into KE.
    cw_run_to awr_dp B_SEG7. ctk_keep kwr_dp.
    cw_branch Hc3.
    all: lazymatch type of Hc3 with branch_taken _ (sv_denot ?Ev _) _ = _ =>
      rewrite branch_eq_U, (U_atom Ev 34 dv ltac:(ewpeel; exact E34) ltac:(lia)), U_lit in Hc3 by lia end.
    * (* dot[n - 1] = 0: dot[n - 1] := 1, to 0x86c28 *)
      apply Z.eqb_eq in Hc3.
      cw_run_to awr_dp PC_NEXT. ctk_keep kwr_dp.
      lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
        pose proof (st_ok_region_nth Ev ssv (restrict (w_H W2) msv) 0 _ HS eq_refl) as HR end.
      cbn [ms_mem restrict] in HR.
      pose proof (field_of_region _ _ 33 (F + 60 + 4 * n) _ 0 4 0 4 0 4%N (SLit 1) 1 HR
        ltac:(ewpeel; rewrite E33; apply unsigned_lit_small; lia) ltac:(left; reflexivity) eq_refl
        ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew.
      rewrite Z.add_0_r in Vnew. change (N.to_nat 4) with 4%nat in Vnew.
      assert (Hct1' : ct1_lib (skipn (S (Z.to_nat j)) (cg_tb g)) n s (upd_at dot (n - 1) 1) =
                      ct1_lib (cg_tb g) 0 [] (repeat 0 8)).
      { rewrite <- Hct1. rewrite (skipn_cons_nth (cg_tb g) (Z.to_nat j) 0) by (unfold cg_len in Hjl; lia).
        rewrite Hch, Hc1. symmetry. apply ctl_ct1_dotset; [lia | exact Hc3]. }
      apply SRr_ret. cbv beta. right.
      lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
        apply (ctl_cut_close B MT LAWS g pos PC_NEXT (P_N g pos fuel) ly2 S2 regs2 mem2 md2 W2 msv _ Hpre HJ0 HK HP Hni
          Hio Hmo HC HJ);
        [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
        | rfin | rfin | rfin | rfin | rfin | rfin | rfin
        | intros a Ha Hz; apply KE; [exact Ha | intros Hd; apply Hz; unfold ct_zv; lia]
        | exact KP | exact Hsj | exact Hdj | ] end.
      intros Ksj Kdj. exists j, n, s, (upd_at dot (n - 1) 1).
      split; [rfin|]. split; [rfin|]. split; [rfin|]. split; [rfin|]. split; [rfin|]. split; [rfin|]. split; [rfin|].
      split; [rfin|].
      split; [exact Hj|]. split; [exact Hfuel|]. split; [exact Hnz|]. split; [exact Hct1'|].
      split; [split; [exact (ct_inv_dot n dot (conj Hn0 (conj Hdl Hdz)) ltac:(lia))|];
              split; [apply ctl_Forall_upd_at; [exact Hd01 | lia]|]; split; [exact Hsl | exact Hs128]|].
      split; [|split; [exact Ksj | exact Kdj]].
      apply (ctl_arrays_word g pos W2 mem2 _ n s dot 1); [lia | exact Hdl | | exact Vnew | exact Harr].
      intros a Ha Hz. apply KE; [lia | exact Hz].
    * (* dot[n - 1] <> 0: the dot draws as ' ' *)
      apply Z.eqb_neq in Hc3.
      cw_run_to awr_dp B_SEG7. ctk_keep kwr_dp.
      lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
        pose proof (st_ok_region_nth Ev ssv (restrict (w_H W2) msv) 0 _ HS eq_refl) as HR end.
      cbn [ms_mem restrict] in HR.
      pose proof (field_of_region _ _ 33 (F + 60 + 4 * n) _ 0 4 0 4 0 4%N (SOff 34 0) dv HR
        ltac:(ewpeel; rewrite E33; apply unsigned_lit_small; lia) ltac:(left; reflexivity)
        ltac:(rewrite sv_denot_SOff0; ewpeel; exact E34) ltac:(cbn; lia) ltac:(cbn; lia)) as Vold.
      rewrite Z.add_0_r in Vold. change (N.to_nat 4) with 4%nat in Vold.
      apply SRr_ret. cbv beta. left.
      lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
        apply (ctl_cut_close B MT LAWS g pos B_SEG7 (P_C g pos fuel) ly2 S2 regs2 mem2 md2 W2 msv _ Hpre HJ0 HK HP Hni
          Hio Hmo HC HJ);
        [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
        | rfin | rfin | rfin | rfin | rfin | rfin | rfin
        | intros a Ha Hz; apply KE; [exact Ha | intros Hd; apply Hz; unfold ct_zv; lia]
        | exact KP | exact Hsj | exact Hdj | ] end.
      intros Ksj Kdj. exists j, n, ch, s, dot.
      split; [rfin|]. split; [rv; rewrite Hc1; reflexivity|].
      split; [rand; reflexivity|].
      split; [rfin|]. split; [rfin|]. split; [rfin|]. split; [rfin|]. split; [rfin|]. split; [rfin|]. split; [rfin|].
      split; [exact Hj|]. split; [exact Hfuel|]. split; [exact Hch|]. split; [exact Hch0|]. split; [exact Hnz|].
      split; [exact Hct1|]. split; [intros (_ & _ & Hd0); exact (Hc3 Hd0)|]. split; [exact Hl1|].
      split; [|split; [exact Ksj | exact Kdj]].
      assert (Hu : upd_at dot (n - 1) dv = dot) by (unfold dv; apply upd_same; lia).
      rewrite <- Hu.
      apply (ctl_arrays_word g pos W2 mem2 _ n s dot dv); [lia | exact Hdl | | exact Vold | exact Harr].
      intros a Ha Hz. apply KE; [lia | exact Hz].
Time Qed.
End d.
