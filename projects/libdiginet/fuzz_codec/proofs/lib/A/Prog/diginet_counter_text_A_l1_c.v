(* Part c of one pass of diginet_counter_text's first loop in image A (diginet_counter_text_A_l1_base.v): from
   0x86338 the check of the next text byte at s6 = q + j + 1 (paid by its usable mark), lbu a1,0(s3), s3 and s6
   one on; a byte not 0 goes back to the loop head 0x862a4, a 0 ends the first loop (0x863c0: s11 := n - 8,
   a3 = a2 = 0, a4 = 8, a5 = 1, a0 = s4) at the loop-2 head 0x863d8. The run writes nothing. *)
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

(* a state whose regions have no write window *)
Ltac awr_ro := cbn [ss_mem]; repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [azlit_tac|] ].
Lemma ctc_firstn_S : forall (l : list Z) k, (k < length l)%nat -> firstn (S k) l = firstn k l ++ [nth k l 0].
Proof.
induction l as [|x l IH]; intros k Hk; cbn in Hk; [lia|].
destruct k as [|k]; [reflexivity|]. cbn [firstn nth app]. rewrite (IH k) by lia. reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables RLO RHI SEG7TBL : Z.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

Theorem ct_part_c_holds : ct_part_c B MT RLO RHI SEG7TBL.
Proof.
unfold ct_part_c. intros g pos fuel W2 c2 Hpre Hnow Hc.
destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HK & HP & Hni & Hio & Hmo & HC & HL).
destruct HL as (j & n & s & dot & R18 & R19 & R22 & R20 & R21 & R26 & R27 & Hj & Hfuel & Hnz & Hct1 & Hl1 & Harr &
  Hsj & Hdj).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (ctl_frame B LAWS g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (Hfr & Efa & Efl & HF0 & HFc & HF64 & HFapp & HFp).
pose proof HC as (R8 & R2 & R9 & R3 & R4 & R23 & R25 & _).
pose proof Hpre as (_ & _ & (Hq0 & Htb0 & Hin0 & (Hqc0 & Hqc63 & _ & _ & _ & Hqam & _)) & _).
pose proof (Hnow pos ly2 S2 W2 mem2 md2 HJ HK HP Hni) as ((Htb & Htra) & _).
assert (Hjl : j + 1 < cg_len g) by (unfold cg_len; exact (ctl_tb_len (cg_tb g) j Hj Hin0 Hnz)).
unfold cg_len in Hjl, Hqc63, Hqam. pose proof Hqam as Hqam'. unfold amem_range in Hqam'. rewrite C3, C4, C5 in Hqam'.
set (chn := nth (S (Z.to_nat j)) (cg_tb g) 0).
pose proof (Htb (S (Z.to_nat j)) ltac:(lia)) as (Vch & Hch8). fold chn in Vch, Hch8.
replace (cg_q g + Z.of_nat (S (Z.to_nat j))) with (cg_q g + j + 1) in Vch by lia.
pose proof Hl1 as ((Hn0 & Hdl & Hdz) & Hd01 & Hsl & Hs128).
set (xs := [chn]).
remember (Ereg regs2 (cw_extra xs)) as E eqn:HEE.
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (E33 : ew E 33 = Z_to_bv 64 chn) by (subst E; exact (cw_ew_x regs2 xs 0)).
assert (E18 : ew E 18 = w64 46) by (subst E; rewrite (ew_Ereg_nat regs2 _ 18 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = w64 (cg_q g + j + 1)) by (subst E; rewrite (ew_Ereg_nat regs2 _ 19 19%bv eq_refl); exact R19).
assert (E22 : ew E 22 = w64 (cg_q g + j + 1)) by (subst E; rewrite (ew_Ereg_nat regs2 _ 22 22%bv eq_refl); exact R22).
assert (E20 : ew E 20 = w64 (cg_sg g)) by (subst E; rewrite (ew_Ereg_nat regs2 _ 20 20%bv eq_refl); exact R20).
assert (E21 : ew E 21 = w64 (cg_F g pos + 64)) by (subst E; rewrite (ew_Ereg_nat regs2 _ 21 21%bv eq_refl); exact R21).
assert (E26 : ew E 26 = w64 (cg_F g pos + 32)) by (subst E; rewrite (ew_Ereg_nat regs2 _ 26 26%bv eq_refl); exact R26).
assert (E27 : ew E 27 = w64 n) by (subst E; rewrite (ew_Ereg_nat regs2 _ 27 27%bv eq_refl); exact R27).
(* the start: the text byte at s3 (atom 19), read only; s9 = SB *)
assert (YS : YP0l.st_ok tfibsegs E
  (mkSS PC_NEXT sr_atoms [YP09.mkRegion (Some 19%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))]] None
    (mkFacts [(32%nat, mkAF SB SB 0); (22%nat, mkAF 0 (2 ^ 47 - 2) 0); (33%nat, mkAF 0 255 0)] [] []))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 PC_NEXT) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply entry_st_ok_full.
  - apply regs_ok_Ereg.
  - reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E19. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val tfibsegs _ _ (cg_q g + j + 1) 0 1 (SOff 33 0) chn).
    + rewrite sv_denot_SOff0. exact E33.
    + cbn. lia.
    + cbn. lia.
    + rewrite Z.add_0_r. exact Vch.
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E32, E22, E33. unfold w64. rewrite !unsigned_lit_small by (unfold SB; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; first [exact I | lia]. }
pose proof (ast_ok_set_reg_fp tfibsegs E _ _ (25%bv : bv 5) (SOff 32 0) YS eq_refl
  ltac:(cbn [ms_regs restrict mkst]; rewrite sv_denot_SOff0, E32, R25; reflexivity)) as HS.
clear YS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 22 0 1] E (mrestrict (w_H W2) mem2)).
{ apply Forall_cons; [|apply Forall_nil].
  apply (cw_shent_ra W2 mem2 E 22 (cg_q g + j + 1) 1); [| | lia | lia | lia | exact E22 | exact E32].
  - eapply range_addressable_sub; [exact Htra | lia | unfold cg_len; lia].
  - unfold amem_range. rewrite C3, C4, C5. lia. }
cw_keep_j0 HJ HJ0.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a)
  by (intros; reflexivity).
assert (KP : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem2 a) by (intros; assumption).
unfold cfg_at. change (w64 PC_NEXT) with (Z_to_bv 64 PC_NEXT).
cw_run_to awr_ro PC_L1. ctk_keep cw_kwr_ro.
assert (Hskip : skipn (S (Z.to_nat j)) (cg_tb g) = chn :: skipn (S (S (Z.to_nat j))) (cg_tb g))
  by (apply skipn_cons_nth; lia).
cw_branch Hc.
all: lazymatch type of Hc with branch_taken _ (sv_denot ?Ev _) _ = _ =>
  rewrite branch_ne_U, (U_atom Ev 33 chn ltac:(ewpeel; exact E33) ltac:(lia)), U_lit in Hc by lia end.
- (* tb[j + 1] <> 0: back to the loop head *)
  apply negb_true_iff, Z.eqb_neq in Hc.
  cw_run_to awr_ro PC_L1. ctk_keep cw_kwr_ro.
  lazymatch goal with HS : YP0l.st_ok _ _ _ (restrict _ ?msv) |- _ =>
    assert (KF : forall a, cg_F g pos <= a < cg_F g pos + 128 ->
      aview tfibsegs (w_H W2) (ms_mem msv) a = aview tfibsegs (w_H W2) mem2 a)
      by (intros a Ha; apply KE; [lia | tauto]) end.
  apply SRr_ret. cbv beta. left.
  lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
    apply (ctl_cut_close B MT LAWS g pos PC_L1 (P_L1 g pos fuel) ly2 S2 regs2 mem2 md2 W2 msv _ Hpre HJ0 HK HP Hni Hio
      Hmo HC HJ);
    [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
    | rfin | rfin | rfin | rfin | rfin | rfin | rfin
    | intros a Ha _; apply KE; [exact Ha | tauto] | exact KP | exact Hsj | exact Hdj | ] end.
  intros Ksj Kdj. exists (j + 1), n, chn, s, dot.
  split; [rfin|]. split; [rfin|].
  split; [rv0; lazymatch goal with HS : YP0l.st_ok _ ?Ev _ _ |- _ =>
    rewrite denot_lit_U, (U_atom_off Ev 19 (cg_q g + j + 1) 1 ltac:(ewpeel; exact E19) ltac:(lia) ltac:(lia)) end;
    unfold w64; f_equal; lia|].
  split; [rv0; lazymatch goal with HS : YP0l.st_ok _ ?Ev _ _ |- _ =>
    rewrite denot_lit_U, (U_atom_off Ev 22 (cg_q g + j + 1) 1 ltac:(ewpeel; exact E22) ltac:(lia) ltac:(lia)) end;
    unfold w64; f_equal; lia|].
  split; [rfin|]. split; [rfin|]. split; [rfin|]. split; [rfin|].
  split; [lia|]. split; [unfold cg_len in *; lia|].
  split; [unfold chn; f_equal; lia|]. split; [exact Hc|].
  split; [replace (S (Z.to_nat (j + 1))) with (S (S (Z.to_nat j))) by lia;
          rewrite (ctc_firstn_S (cg_tb g) (S (Z.to_nat j))) by lia; apply Forall_app; split;
          [exact Hnz | constructor; [exact Hc | constructor]]|].
  split; [replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia; exact Hct1|].
  split; [exact Hl1|].
  split; [apply (ctl_arrays_kept g pos W2 mem2 _ n s dot); [exact KF | lia | exact Harr]|].
  split; [exact Ksj | exact Kdj].
- (* tb[j + 1] = 0: the first loop is done *)
  apply negb_false_iff, Z.eqb_eq in Hc.
  cw_run_to awr_ro PC_L2. ctk_keep cw_kwr_ro.
  lazymatch goal with HS : YP0l.st_ok _ _ _ (restrict _ ?msv) |- _ =>
    assert (KF : forall a, cg_F g pos <= a < cg_F g pos + 128 ->
      aview tfibsegs (w_H W2) (ms_mem msv) a = aview tfibsegs (w_H W2) mem2 a)
      by (intros a Ha; apply KE; [lia | tauto]) end.
  apply SRr_ret. cbv beta. right.
  lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
    apply (ctl_cut_close B MT LAWS g pos PC_L2 (P_L2 g pos 8) ly2 S2 regs2 mem2 md2 W2 msv _ Hpre HJ0 HK HP Hni Hio
      Hmo HC HJ);
    [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
    | rfin | rfin | rfin | rfin | rfin | rfin | rfin
    | intros a Ha _; apply KE; [exact Ha | tauto] | exact KP | exact Hsj | exact Hdj | ] end.
  intros Ksj Kdj. exists 0, n, 0, s, dot, [].
  rewrite !Z.add_0_r.
  split; [rfin|]. split; [rfin|]. split; [rfin|]. split; [rfin|]. split; [rfin|]. split; [rfin|].
  split; [rfin|]. split; [rfin|].
  split; [rv0; cbn [sv_denot]; ewpeel; rewrite E27; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|].
  split; [reflexivity|]. split; [lia|].
  split; [unfold counter_text_spec; rewrite <- Hct1, Hskip, Hc; reflexivity|].
  split; [exact Hl1|]. split; [reflexivity|]. split; [constructor|]. split; [lia|].
  split; [apply (ctl_arrays_kept g pos W2 mem2 _ n s dot); [exact KF | lia | exact Harr]|].
  split; [exact Ksj | exact Kdj].
Time Qed.
End d.
