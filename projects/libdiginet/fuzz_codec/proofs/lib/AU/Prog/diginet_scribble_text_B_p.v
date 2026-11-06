(* diginet_scribble_text in image B (fuzz_codec.asan-ubsan, 0x86500): the segment P of
   diginet_scribble_text_B_inv.v -- the test of the padding at 0x8664c (sc_seg_P).

   The code: 0x8664c bgeu a7,a2 (j >= n goes to the return 0x86698); a3 := a7 + a1 = o + j; a4 := 32; a1 := a3;
   to the padding loop 0x8665c. No memory access. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgWalkU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import diginet_scribble_text_B_inv.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0l.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Ltac ewpeel := repeat (first [ rewrite ew_havoc_old by nat_side | rewrite ew_ewset_other by nat_side ]).
Ltac sreg := lazymatch goal with HS : st_ok ?segs ?Ev ?ss (restrict ?H ?msv) |- context [getr (ms_regs ?msv) ?r] =>
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  let R := fresh "R" in
  assert (R : getr (ms_regs msv) r = sv_denot Ev e)
    by (refine (eq_trans (st_ok_restrict_reg segs H Ev ss msv r HS) _); reflexivity);
  rewrite R; clear R end.
(* a register the run did not write: its atom, the boundary's register *)
Ltac skeep := sreg; rewrite sv_denot_SOff0; ewpeel;
  lazymatch goal with EE : forall n (rr : bv 5), _ -> ew ?Ev n = _ |- _ => apply EE; reflexivity end.
Ltac awr_nil := cbn [ss_mem]; apply awr_ok_nil.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws tfibsegs B.

Theorem sp_holds : sc_seg_P B.
Proof.
unfold sc_seg_P. intros g W2 c2 Hpre Hcut.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
destruct Hcut as (-> & regs2 & mem2 & md2 & -> & HJ & Hio & HC & HPP).
destruct HPP as (r & j & outs & R10 & R17 & R11 & Hj & Hlen & Hout & Hspec).
destruct (sc_out B g Hpre) as (Ho0 & Hon & Hn & _).
pose proof HC as (_ & _ & R12 & _).
set (E := Ereg regs2 (cw_extra [])).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs2 rr)
  by (intros nn rr Hnn; unfold E; apply ew_Ereg_nat; exact Hnn).
assert (E17 : ew E 17 = Z_to_bv 64 j) by (rewrite (EE 17%nat 17%bv eq_refl); exact R17).
assert (E12 : ew E 12 = Z_to_bv 64 (sg_n g)) by (unfold E; rewrite (ew_Ereg_nat regs2 _ 12 12%bv eq_refl); exact R12).
assert (E11 : ew E 11 = Z_to_bv 64 (sg_o g)) by (unfold E; rewrite (ew_Ereg_nat regs2 _ 11 11%bv eq_refl); exact R11).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (apply cw_ew_SB).
assert (HS : st_ok tfibsegs E (mkSS PC_P sr_atoms [] None (mkFacts [(32%nat, mkAF SB SB 0)] [] []))
  (restrict (w_H (sg_W g)) (mkst regs2 (Z_to_bv 64 PC_P) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. apply entry_st_ok_full.
  - apply regs_ok_Ereg.
  - reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite cw_ew_SB, unsigned_lit_small by (unfold SB; lia). unfold SB. split; [|exact I]. split; [lia|].
    split; [reflexivity | lia]. }
clearbody E.
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H (sg_W g)) mem2)) by apply Forall_nil.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False ->
  aview tfibsegs (w_H (sg_W g)) mem2 a = aview tfibsegs (w_H (sg_W g)) mem2 a) by (intros; reflexivity).
assert (KP : forall a, apresent (w_H (sg_W g)) mem2 a -> apresent (w_H (sg_W g)) mem2 a) by (intros; assumption).
unfold cfg_at. change (w64 PC_P) with (Z_to_bv 64 PC_P).
cw_branch Hb.
all: rewrite branch_geu_U, (U_atom E 17 j E17 ltac:(lia)), (U_atom E 12 (sg_n g) E12 ltac:(lia)) in Hb.
- (* taken: j >= n, so j = n: to the return *)
  apply negb_true_iff, Z.ltb_ge in Hb.
  replace (sg_n g - j) with 0 in Hspec by lia.
  cw_run_to awr_nil PC_X.
  lazymatch goal with HG : mem_grows (mrestrict ?H ?m1) (mrestrict ?H ?m2) |- _ =>
    let KQ := fresh "KQ" in
    assert (KQ : forall a, apresent H mem2 a -> apresent H m2 a)
      by (intros a Ha; eapply apresent_grows; [exact HG | exact (KP a Ha)]);
    clear KP; rename KQ into KP end.
  cw_keep cw_kwr_ro.
  apply SRr_ret. right.
  lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
    apply (sc_cut_close B g PC_X (P_X g) regs2 mem2 md2 msv _ Hpre Hio HC HJ);
    [ eapply same_io_trans; [apply same_io_refl | apply cw_same_io_wvb]
    | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
    | unfold sc_kregs, sc_lregs; cbn [app]; repeat (apply Forall_cons; [cbv beta; skeep|]); apply Forall_nil
    | intros a Ha _; apply KE; [exact Ha | tauto]
    | exact KP | ] end.
  split.
  + sreg. rewrite sv_denot_SOff0. ewpeel. rewrite (EE 10%nat 10%bv eq_refl). rewrite R10.
    rewrite Hspec. reflexivity.
  + rewrite Hspec. cbn [fst Z.to_nat repeat]. rewrite app_nil_r.
    apply (sc_garr8_kept (mrestrict (w_H (sg_W g)) mem2)); [|exact Hout].
    intros x Hx. apply (mbyte_of_aview tfibsegs). apply KE; [lia | tauto].
- (* not taken: j < n, to the padding loop with a1 = a3 = o + j, a4 = 32 *)
  apply negb_false_iff, Z.ltb_lt in Hb.
  cw_run_to awr_nil PC_L.
  lazymatch goal with HG : mem_grows (mrestrict ?H ?m1) (mrestrict ?H ?m2) |- _ =>
    let KQ := fresh "KQ" in
    assert (KQ : forall a, apresent H mem2 a -> apresent H m2 a)
      by (intros a Ha; eapply apresent_grows; [exact HG | exact (KP a Ha)]);
    clear KP; rename KQ into KP end.
  cw_keep cw_kwr_ro.
  apply SRr_ret. left. exists (Z.to_nat (sg_n g - j)).
  lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
    apply (sc_cut_close B g PC_L (P_L g (Z.to_nat (sg_n g - j))) regs2 mem2 md2 msv _ Hpre Hio HC HJ);
    [ eapply same_io_trans; [apply same_io_refl | apply cw_same_io_wvb]
    | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
    | unfold sc_kregs, sc_lregs; cbn [app]; repeat (apply Forall_cons; [cbv beta; skeep|]); apply Forall_nil
    | intros a Ha _; apply KE; [exact Ha | tauto]
    | exact KP | ] end.
  exists r, j, outs.
  assert (Hoj : forall e, sv_denot E e = Z_to_bv 64 (sg_o g + j) -> sv_denot E e = w64 (sg_o g + j))
    by (intros e He; exact He).
  split; [skeep || (sreg; rewrite sv_denot_SOff0; ewpeel; rewrite (EE 10%nat 10%bv eq_refl); exact R10)|].
  split; [skeep || (sreg; rewrite sv_denot_SOff0; ewpeel; rewrite (EE 17%nat 17%bv eq_refl); exact R17)|].
  split; [sreg; rewrite denot_lit_U; unfold w64; f_equal;
          lazymatch goal with |- U ?Ev _ = _ =>
            first [ rewrite U_SAlu; cbn [zalu_raw];
                    rewrite (U_atom Ev 17 j ltac:(ewpeel; exact E17) ltac:(lia)),
                            (U_atom Ev 11 (sg_o g) ltac:(ewpeel; exact E11) ltac:(lia));
                    apply zcanon_id; unfold M64; lia
                  | idtac "PREG11" ] end|].
  split; [sreg; rewrite denot_lit_U; unfold w64; f_equal;
          lazymatch goal with |- U ?Ev _ = _ =>
            first [ rewrite U_SAlu; cbn [zalu_raw];
                    rewrite (U_atom Ev 17 j ltac:(ewpeel; exact E17) ltac:(lia)),
                            (U_atom Ev 11 (sg_o g) ltac:(ewpeel; exact E11) ltac:(lia));
                    apply zcanon_id; unfold M64; lia
                  | idtac "PREG13" ] end|].
  split; [sreg; reflexivity|].
  split; [lia|]. split; [lia|]. split; [exact Hlen|].
  split; [apply (sc_garr8_kept (mrestrict (w_H (sg_W g)) mem2)); [|exact Hout];
          intros x Hx; apply (mbyte_of_aview tfibsegs); apply KE; [lia | tauto]|].
  exact Hspec.
Time Qed.
End h.
End d.
