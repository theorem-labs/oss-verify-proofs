(* diginet_scribble_text in image A (fuzz_codec.asan, 0x85cc4): the segment P of diginet_scribble_text_A_inv.v --
   the padding at 0x85de0 (sc_seg_P).

   The code: 0x85de0 bgeu a5,a2 (j >= n goes to the return 0x85df4); a0 := a1 + a5 = o + j; a2 := a2 - a5 = n - j;
   a1 := 32; 0x85df0 jal __asan_memset, which returns to 0x85df4. No memory access before the call; the call writes
   [o + j, o + n) and, below the frame, its own window. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0m.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YCeo.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YC85.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgChkC CPgWalk CPgWalkIntr.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import diginet_scribble_text_A_inv.
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
(* a register index of CLOB's complement, as acallee_saved reads it *)
Ltac sp_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?x] =>
    let z := eval vm_compute in (bv_unsigned x) in
    replace (bv_unsigned x) with z by (vm_compute; reflexivity) end; lia.
(* the model's input and output across runs and a runtime call *)
Ltac sp_io := let rec kio := first [assumption | apply same_io_refl
  | eapply same_io_trans; [| apply cw_same_io_wvb]; kio
  | eapply same_io_trans; [| apply same_io_materialized; eassumption]; kio] in kio.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis AMEMSET : aintrin_realizes tfibsegs B OSet 0x51e34.

Theorem sp_holds : sc_seg_P B.
Proof.
unfold sc_seg_P. intros g W2 c2 Hpre Hcut.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hcut as (-> & regs2 & mem2 & md2 & -> & HJ & Hio & HC & HPP).
destruct HPP as (r & j & outs & R8 & R15 & R11 & R12 & Hr & Hj & Hlen & Hout & Hspec).
destruct (sc_stack B g Hpre) as (Hceil & H47 & H46 & Hal & Hwin & Hsp0 & Hprs).
destruct (sc_out B g Hpre) as (Ho0 & Hon & Hn & Hoff & HTD & HTW & HRAo & Hhull & Hamo & _).
pose proof (sc_amem47 (sg_o g) (sg_n g) ltac:(lia) ltac:(lia) Hamo) as Ho47.
pose proof Hpre as (HE & _).
pose proof HE as (HJ0 & Hra & Hra4 & Hgp & Htp & _).
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _ & _).
pose proof Hstatic as (Hsp0al & _).
pose proof HC as (HK & R2 & Vra & Vs0 & KC & KPc).
pose proof HK as HK'. repeat (apply Forall_cons_iff in HK' as (? & HK')). cbv beta in *.
unfold sg_sp in *. unfold T_scribble_text, ESTACK in *.
set (E := Ereg regs2 (cw_extra [])).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs2 rr)
  by (intros nn rr Hnn; unfold E; apply ew_Ereg_nat; exact Hnn).
assert (E15 : ew E 15 = Z_to_bv 64 j) by (rewrite (EE 15%nat 15%bv eq_refl); exact R15).
assert (E12 : ew E 12 = Z_to_bv 64 (sg_n g)) by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
assert (E11 : ew E 11 = Z_to_bv 64 (sg_o g)) by (rewrite (EE 11%nat 11%bv eq_refl); exact R11).
assert (E8 : ew E 8 = Z_to_bv 64 r) by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
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
pose proof HJ as HJ1. clear HJ. rename HJ1 into HJ.
unfold cfg_at. change (w64 PC_P) with (Z_to_bv 64 PC_P).
cw_branch Hb.
all: rewrite branch_geu_U, (U_atom E 15 j E15 ltac:(lia)), (U_atom E 12 (sg_n g) E12 ltac:(lia)) in Hb.
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
  apply SRr_ret.
  lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
    apply (sc_cut_close B g PC_X (P_X g) regs2 mem2 md2 msv _ Hpre Hio HC HJ);
    [ sp_io
    | exact (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl)
    | unfold sc_kregs; cbn [app]; repeat (apply Forall_cons; [cbv beta; skeep|]); apply Forall_nil
    | intros a Ha _; apply KE; [exact Ha | tauto]
    | exact KP | ] end.
  split.
  + sreg. rewrite sv_denot_SOff0. ewpeel. rewrite (EE 8%nat 8%bv eq_refl), R8. rewrite Hspec. reflexivity.
  + rewrite Hspec. cbn [fst Z.to_nat repeat]. rewrite app_nil_r.
    apply (sc_garr8_kept (mrestrict (w_H (sg_W g)) mem2)); [|exact Hout].
    intros x Hx. apply (mbyte_of_aview tfibsegs). apply KE; [lia | tauto].
- (* not taken: j < n: a0 := o + j, a2 := n - j, a1 := 32, the call *)
  apply negb_false_iff, Z.ltb_lt in Hb.
  cw_run awr_nil.
  lazymatch goal with HG : mem_grows (mrestrict ?H ?m1) (mrestrict ?H ?m2) |- _ =>
    let KQ := fresh "KQ" in
    assert (KQ : forall a, apresent H mem2 a -> apresent H m2 a)
      by (intros a Ha; eapply apresent_grows; [exact HG | exact (KP a Ha)]);
    clear KP; rename KQ into KP end.
  cw_keep cw_kwr_ro.
  lazymatch goal with HSv : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
    assert (Ra0 : getr (ms_regs msv) 10 = w64 (sg_o g + j))
      by (sreg; apply (denot_add2 Ev 11 15 (sg_o g) j); [ewpeel; exact E11 | ewpeel; exact E15 | lia | lia | lia]);
    assert (Ra1 : getr (ms_regs msv) 11 = w64 32) by (sreg; reflexivity);
    assert (Ra2 : getr (ms_regs msv) 12 = w64 (sg_n g - j))
      by (sreg; apply (sc_denot_sub Ev 12 15 (sg_n g) j); [ewpeel; exact E12 | ewpeel; exact E15 | lia | lia]);
    assert (Rsp : spZ (ms_regs msv) = spZ (sg_regs g) - 16)
      by (unfold spZ at 1; sreg; rewrite sv_denot_SOff0; ewpeel; rewrite (EE 2%nat 2%bv eq_refl), R2;
          unfold w64; rewrite unsigned_lit_small by lia; reflexivity);
    assert (Rgp : getr (ms_regs msv) 3 = w64 (as_gp B))
      by (sreg; rewrite sv_denot_SOff0; ewpeel; rewrite (EE 3%nat 3%bv eq_refl);
          lazymatch goal with H3 : getr regs2 3 = getr (sg_regs g) 3 |- _ => rewrite H3 end; exact Hgp);
    assert (Rtp : getr (ms_regs msv) 4 = w64 (as_tp B))
      by (sreg; rewrite sv_denot_SOff0; ewpeel; rewrite (EE 4%nat 4%bv eq_refl);
          lazymatch goal with H4 : getr regs2 4 = getr (sg_regs g) 4 |- _ => rewrite H4 end; exact Htp);
    assert (Rk : Forall (fun rr => getr (ms_regs msv) rr = getr regs2 rr) (sc_kregs ++ [2%bv; 8%bv]))
      by (unfold sc_kregs; cbn [app]; repeat (apply Forall_cons; [cbv beta; skeep|]); apply Forall_nil);
    assert (KEc : sc_kept g (ms_mem msv))
      by (intros a Ha Hz; rewrite (KE a Ha ltac:(tauto)); exact (KC a Ha Hz));
    assert (HG0 : mem_grows (mrestrict (w_H (sg_W g)) (sg_memc g)) (mrestrict (w_H (sg_W g)) (ms_mem msv)))
      by (apply sc_grow_of_apresent; intros a Ha; apply KP; apply KPc; exact Ha)
  end.
  eapply (cw_intrin_call B LAWS OSet CA_MEMSET AMEMSET (sg_W g) _ _ _ _ (sg_STK g) (sg_sp0 g) (sg_FP g) (sg_ly g)
            (sg_S g) (sg_W0 g) (sg_mem0 g) (sg_md0 g) (sg_own g) (sg_lyc g) (sg_Sc g) (sg_k g)
            (sg_o g + j) 32 (sg_n g - j) 0x85df4 90%nat []);
    try eassumption; try reflexivity; try unfold ESTACK in *.
  + lia.
  + lia.
  + lia.
  + rewrite Rsp; lia.
  + rewrite Rsp; lia.
  + rewrite Rsp. replace (spZ (sg_regs g) - 16) with (spZ (sg_regs g) + (-1) * 16) by lia.
    rewrite Z_mod_plus_full. exact Hal.
  + lia.
  + intros a Ha. split; [exact (proj1 (HTW a ltac:(lia)))|]. rewrite Rsp. lia.
  + unfold amem_range in Hamo |- *; rewrite C3, C4, C5 in Hamo |- *; lia.
  + eapply range_addressable_sub;
      [exact (sc_ra_kept B g _ Hpre KEc (sg_o g) (sg_n g) ltac:(lia) ltac:(lia) Hamo HRAo) | lia | lia].
  + intros Hpos.
    apply (sc_hull_sub _ (sg_o g) (sg_n g) (sg_o g + j) (sg_n g - j)); [| lia | lia | lia].
    intros s Hs. exact (aview_keeps_vis tfibsegs (w_H (sg_W g)) (sg_memc g) _ s HG0 (Hhull ltac:(lia) s Hs)).
  + cbn [ss_mem]; apply submem_nil.
  + apply Forall_nil.
  + intros regs3 mem3 md3 HJ3 HP3 Hd3 Heff Hfr3 Hpres3 HSM3 HS3.
    apply SRr_ret.
    apply (sc_cut_close B g PC_X (P_X g) regs2 mem2 md2 (mkst regs3 (Z_to_bv 64 0x85df4) mem3 (seg_rom tfibsegs)) md3
             Hpre Hio HC HJ3).
    * sp_io.
    * reflexivity.
    * rewrite Forall_forall in Rk |- *. intros rr Hrr.
      etransitivity; [apply (sc_pres_at _ _ _ HP3); exact (sc_kregs_cs rr Hrr) | apply Rk; unfold sc_kregs in Hrr |- *; cbn [app In] in Hrr |- *; tauto].
    * cbn [ms_mem mkst]. intros a Ha Hz. unfold sc_wz, sg_sp, T_scribble_text, ESTACK in Hz.
      rewrite (Hfr3 a Ha ltac:(lia) ltac:(rewrite Rsp; unfold ESTACK; lia)). apply KE; [exact Ha | tauto].
    * cbn [ms_mem mkst]. intros a Ha. apply Hpres3. apply KP. exact Ha.
    * cbn [ms_regs ms_mem mkst]. rewrite Forall_forall in Rk. split.
      { etransitivity; [apply (sc_pres_at _ _ _ HP3); sp_cs |].
        etransitivity; [apply Rk; unfold sc_kregs; cbn [app In]; tauto |].
        rewrite R8, Hspec. cbn [snd]. reflexivity. }
      rewrite Hspec. cbn [fst].
      apply (sc_garr8_snoc_rep (sg_W g) mem2 mem3 (sg_o g) outs (Z.to_nat (sg_n g - j))).
      -- exact Hout.
      -- intros x Hx. apply (mbyte_of_aview tfibsegs).
         rewrite (Hfr3 x ltac:(lia) ltac:(lia) ltac:(rewrite Rsp; unfold ESTACK; lia)). apply KE; [lia | tauto].
      -- intros i Hi. rewrite Hlen. replace (sg_o g + (j + Z.of_nat i)) with (sg_o g + j + Z.of_nat i) by lia.
         rewrite (Heff (Z.of_nat i) ltac:(lia)). reflexivity.
Time Qed.
End h.
End d.
