(* Segment E of check_text_scribble's walk in image B (fuzz_codec.asan-ubsan 0x83dbc): bs_seg_E of
   check_text_scribble_B_inv.v. 0x83fb8 bgeu a1,s3: o = n goes to the memset 0x83ff4 (want holds the owed text: w and
   no spaces), o < n goes through `li a3,32` to the pad loop's head 0x83fc0. No memory access. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgWalkU CPgWalkKeptU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkFrameU check_text_scribble_B_inv.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

Theorem bs_e_holds : bs_seg_E B MT.
Proof.
unfold bs_seg_E. intros g pos W2 c2 Hpre Hnow Hc.
destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HK & HP & Hni & Hio & Hmo & HC & HL).
destruct HL as (i & o & w & R11 & R26 & R12 & R20 & Hi & Ho & Hwl & Hw1 & Hw2 & Hwg).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof HC as (R8 & R2 & R9 & R3 & R4 & R18 & R24 & R22 & R23 & R25 & R19 & R21 & _).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hn & _).
remember (Ereg regs2 (cw_extra [])) as E eqn:HEE.
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs2 r)
  by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
assert (E11 : ew E 11 = Z_to_bv 64 o) by (rewrite (EE 11%nat 11%bv eq_refl); exact R11).
assert (E19 : ew E 19 = Z_to_bv 64 (bs_n g)) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E26 : ew E 26 = w64 i) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
assert (E12 : ew E 12 = w64 (bnot (bs_F g pos + 32))) by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
assert (E20 : ew E 20 = w64 (bs_ch g)) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (HS : st_ok tfibsegs E (mkSS PC_E sr_atoms [] None (mkFacts [(32%nat, mkAF SB SB 0)] [] []))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 PC_E) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite cw_ew_SB, unsigned_lit_small by (unfold SB; lia). unfold SB. split; [|exact I]. split; [lia|].
    split; [reflexivity | lia]. }
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a)
  by (intros; reflexivity).
assert (KP : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem2 a) by (intros; assumption).
cw_keep_j0 HJ HJ0.
unfold cfg_at. change (w64 PC_E) with (Z_to_bv 64 PC_E).
assert (KW : forall (W3 : world tfibsegs) m3, (forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview tfibsegs (w_H W3) m3 a = aview tfibsegs (w_H W2) mem2 a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ bs_zv g pos a -> aview tfibsegs (w_H W3) m3 a = aview tfibsegs (w_H W2) mem2 a)
  by (intros W3 m3 K a Ha _; apply K; [exact Ha | tauto]).
cw_branch Hc.
all: rewrite branch_geu_U in Hc;
  lazymatch type of Hc with context [U ?Ev _] =>
    rewrite (U_atom Ev 11 o ltac:(ewpeel; exact E11) ltac:(lia)), (U_atom Ev 19 (bs_n g) ltac:(ewpeel; exact E19) ltac:(lia)) in Hc end.
- (* o = n: to the memset *)
  assert (Hon : o = bs_n g) by (destruct (Z.ltb_spec o (bs_n g)); [discriminate Hc | lia]).
  cw_run_to ltac:(cbn [ss_mem]; apply awr_ok_nil) 0x83ff4. ctk_keep cw_kwr_ro.
  apply SRr_ret. cbv beta. right.
  lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- context [mkCfg _ ?md3] =>
    apply (bs_cut_close B MT LAWS g pos PC_M (P_M g pos) ly2 S2 regs2 mem2 md2 W2 msv md3 Hpre HJ0 HK HP Hni Hio
      Hmo HC HJ);
    [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
    | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin
    | bs_rfin | bs_rfin
    | exact (KW W2 (ms_mem msv) KE) | exact KP | ] end.
  rewrite Hon, Z.sub_diag in Hw1. cbn [Z.to_nat repeat] in Hw1. rewrite app_nil_r in Hw1.
  split; [rewrite Hw2; bs_rfin|]. split; [bs_rfin|].
  rewrite Hw1. apply (bs_garr8_kept (w_H W2) (w_H W2) mem2 _); [|exact Hwg].
  intros a Ha. apply KE; [|tauto]. pose proof (bs_frame B LAWS g pos ly2 S2 W2 mem2 md2 Hpre HJ0) as
    (_ & _ & _ & HF0 & HFc & _). pose proof alloc_ceiling_val. unfold bs_F in *. lia.
- (* o < n: a3 = ' ', to the pad loop *)
  assert (Hon : o < bs_n g) by (destruct (Z.ltb_spec o (bs_n g)); [lia | discriminate Hc]).
  cw_run_to ltac:(cbn [ss_mem]; apply awr_ok_nil) 0x83fc0. ctk_keep cw_kwr_ro.
  apply SRr_ret. cbv beta. left.
  lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- context [mkCfg _ ?md3] =>
    apply (bs_cut_close B MT LAWS g pos PC_P (P_P g pos 8) ly2 S2 regs2 mem2 md2 W2 msv md3 Hpre HJ0 HK HP Hni Hio
      Hmo HC HJ);
    [ kio | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
    | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin | bs_rfin
    | bs_rfin | bs_rfin
    | exact (KW W2 (ms_mem msv) KE) | exact KP | ] end.
  exists i, o, w.
  split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|]. split; [bs_rfin|].
  split; [exact Hi|]. split; [lia|]. split; [lia|]. split; [exact Hwl|]. split; [exact Hw1|]. split; [exact Hw2|].
  apply (bs_garr8_kept (w_H W2) (w_H W2) mem2 _); [|exact Hwg].
  intros a Ha. apply KE; [|tauto]. pose proof (bs_frame B LAWS g pos ly2 S2 W2 mem2 md2 Hpre HJ0) as
    (_ & _ & _ & HF0 & HFc & _). pose proof alloc_ceiling_val. unfold bs_F in *. lia.
Qed.
End s.
