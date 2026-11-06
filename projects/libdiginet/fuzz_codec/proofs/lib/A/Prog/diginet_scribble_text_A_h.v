(* diginet_scribble_text in image A (fuzz_codec.asan, 0x85cc4): the segment H of diginet_scribble_text_A_inv.v --
   the loop head 0x85d1c to the store 0x85d64 (sc_seg_H).

   The code: 0x85d1c zext.b a3,t1; t1 <> '.' goes to 0x85d54. For '.': a3 := a6 + s0 = q + i + 1, the instrumented
   check of it, lbu a3 := q[i + 1]; (a3 - 49) & 255 > 8 (not a digit 1..9) goes to 0x85d54; else t1 := a3 - 26,
   t2 := 2 and the store. At 0x85d54: t1 << 56 >= 0 (t1 below 0x80) keeps t1, else t1 := 0x3f; t2 := 1.
   The segment writes no memory.

   The state at 0x85d1c is built over the boundary's own registers (atoms 0 .. 31), the shadow offset (32) and two
   values of its own: 33 the text byte at i + 1 and 34 its address q + i + 1. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgChkC CPgWalk.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import diginet_scribble_text_A_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition h_xs (g : sc_ctx) (i : Z) : list Z := [nth (Z.to_nat i + 1)%nat (sg_tb g) 0; sg_q g + i + 1].
Definition h_AF : list (nat * afact) :=
[(32%nat, mkAF SB SB 0); (6%nat, mkAF 1 255 0); (8%nat, mkAF 0 (2 ^ 47 - 1) 0);
 (10%nat, mkAF 1 (2 ^ 47 - 1) 0); (11%nat, mkAF 1 (2 ^ 47 - 1) 0); (12%nat, mkAF 0 4294967295 0);
 (15%nat, mkAF 0 4294967295 0); (33%nat, mkAF 0 255 0); (34%nat, mkAF 1 (2 ^ 47 - 1) 0)].
(* the byte at q + i + 1, a one-byte region based at atom 34 *)
Definition h_rtx : YP09.region := YP09.mkRegion (Some 34%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].

Ltac ewpeel := repeat (first [ rewrite ew_havoc_old by nat_side | rewrite ew_ewset_other by nat_side ]).
Ltac sreg := lazymatch goal with HS : st_ok ?segs ?Ev ?ss (restrict ?H ?msv) |- context [getr (ms_regs ?msv) ?r] =>
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  let R := fresh "R" in
  assert (R : getr (ms_regs msv) r = sv_denot Ev e)
    by (refine (eq_trans (st_ok_restrict_reg segs H Ev ss msv r HS) _); reflexivity);
  rewrite R; clear R end.
Ltac slit := sreg; reflexivity.
Ltac sval H := sreg; rewrite sv_denot_SOff0; ewpeel; exact H.
(* a register the segment did not write, still the boundary's *)
Ltac h_kregs :=
  let HKf := fresh "HKf" in
  lazymatch goal with HKv : Forall _ sc_kregs |- _ => pose proof (proj1 (Forall_forall _ _) HKv) as HKf end;
  rewrite Forall_forall; intros rr Hrr;
  etransitivity; [| exact (HKf rr Hrr)];
  unfold sc_kregs in Hrr; cbn in Hrr;
  destruct Hrr as [Ex|[Ex|[Ex|[Ex|[Ex|[Ex|[Ex|[Ex|[Ex|[Ex|[Ex|[Ex|[Ex|[]]]]]]]]]]]]]];
  rewrite <- Ex; sreg; rewrite sv_denot_SOff0; ewpeel;
  lazymatch goal with EEv : forall n (r0 : bv 5), _ -> ew _ n = _ |- _ =>
    lazymatch goal with |- ew _ ?nn = getr _ ?r0 => exact (EEv nn r0 eq_refl) end end.
Ltac h_io := let rec kio := first [assumption | apply same_io_refl
  | eapply same_io_trans; [| apply cw_same_io_wvb]; kio
  | eapply same_io_trans; [| apply same_io_materialized; eassumption]; kio] in kio.
Ltac h_cfg := lazymatch goal with HSv : st_ok _ _ _ (restrict _ _) |- _ =>
  norm_ss HSv; unfold cfg_at, w64; cbv [PC_T];
  let Hms := fresh "Hms" in
  pose proof (st_ok_restrict_mkst tfibsegs _ _ _ _ HSv eq_refl) as Hms; cbn [ss_pc] in Hms;
  rewrite <- Hms; reflexivity end.
Ltac h_kp m0 := lazymatch goal with HG : mem_grows (mrestrict ?Hh _) (mrestrict ?Hh ?m2) |- _ =>
  let KQ := fresh "KQ" in
  lazymatch goal with KPv : forall a, apresent _ m0 a -> apresent _ _ a |- _ =>
    assert (KQ : forall a, apresent Hh m0 a -> apresent Hh m2 a)
      by (intros a Ha; eapply apresent_grows; [exact HG | exact (KPv a Ha)]);
    clear KPv; rename KQ into KP end end.
Ltac h_awr := idtac;
lazymatch goal with |- awr_ok ?Ev ?rs ?stk ?sp0v ?fp ?b0 ?bc ?lyv ?ownv =>
  let rs' := eval vm_compute in rs in change (awr_ok Ev rs' stk sp0v fp b0 bc lyv ownv) end;
repeat first [apply awr_ok_nil | apply awr_ok_cons_ro; [azlit_tac|]].

(* the close at the store 0x85d64, for a step that writes vv and uses dv text bytes *)
Ltac hval := sreg; rewrite sv_denot_SOff0; ewpeel; eassumption.
Ltac hoff33 := sreg; rewrite denot_lit_U; unfold w64; f_equal;
  lazymatch goal with |- U ?Ev (SOff 33 (-26)) = _ =>
    rewrite (cw_U_offx Ev 33 _ (-26) ltac:(ewpeel; eassumption) ltac:(lia)) end;
  rewrite Z.mod_small by lia; lia.
Ltac h_close_T gg memb outsv KEv KCv KPv KPcv iv jv vv dv :=
  apply SRr_ret;
  lazymatch goal with HSv : st_ok _ _ _ (restrict _ ?msv) |- _ =>
    split; [reflexivity|]; exists (ms_regs msv), (ms_mem msv); eexists end;
  split; [h_cfg|]; split; [eassumption|]; split; [h_io|];
  split;
  [ split; [h_kregs|];
    split; [sreg; rewrite sv_denot_SOff0; ewpeel;
            etransitivity;
            [ lazymatch goal with EEv : forall n (r0 : bv 5), _ -> ew _ n = _ |- _ =>
                exact (EEv 2%nat 2%bv eq_refl) end
            | assumption]|];
    split; [unfold sg_sp; apply (sc_val_mem_kept (mrestrict (w_H (sg_W gg)) memb));
            [intros xx Hxx; apply (mbyte_of_aview tfibsegs); apply KEv; [lia | tauto] | assumption]|];
    split; [unfold sg_sp; apply (sc_val_mem_kept (mrestrict (w_H (sg_W gg)) memb));
            [intros xx Hxx; apply (mbyte_of_aview tfibsegs); apply KEv; [lia | tauto] | assumption]|];
    split; [intros aa Haa Hzz; rewrite (KEv aa Haa ltac:(tauto)); exact (KCv aa Haa Hzz)|];
    intros aa Haa; apply KPv; apply KPcv; exact Haa
  |];
  exists iv, jv, vv, dv, outsv;
  split; [hval|]; split; [hval|]; split; [first [hval | slit | hoff33]|]; split; [slit|];
  split;
  [ split; [hval|]; split; [hval|]; split; [hval|]; split; [hval|];
    split; [hval|]; split; [hval|]; hval |];
  split; [lia|]; split; [lia|]; split; [lia|];
  split; [first [ replace (Z.to_nat (iv + dv)) with (Z.to_nat iv + 1)%nat by lia; assumption
                | replace (Z.to_nat (iv + dv)) with (S (Z.to_nat iv + 1))%nat by lia;
                  apply (sc_in0_S (sg_tb gg) (Z.to_nat iv + 1)); [assumption | lia] ]|];
  split; [unfold sg_len; lia|]; split; [lia|]; split; [assumption|];
  split; [apply (sc_garr8_kept (mrestrict (w_H (sg_W gg)) memb));
          [intros xx Hxx; apply (mbyte_of_aview tfibsegs); apply KEv; [lia | tauto] | assumption]|].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

Theorem sh_holds : sc_seg_H B.
Proof.
unfold sc_seg_H. intros g fuel W2 c2 Hpre Hcut.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hcut as (-> & regs2 & mem2 & md2 & -> & HJ & Hio & HC & HPH).
destruct HPH as (i & j & b & outs & R8 & R15 & R6 & HL & Hi0 & Hbnth & Hbnz & Hin1 & Hfuel & Hj & Hlen & Hout & Hspec).
destruct HL as (R10 & R11 & R12 & R14 & R16 & R17 & R5).
destruct (sc_stack B g Hpre) as (Hceil & H47 & H46 & Hal & Hwin & Hsp0 & Hprs).
destruct (sc_text B g Hpre) as (Hq0 & Hql & Hin0 & Hlen0 & HGT & HRAq & Hamq & Hoffq).
destruct (sc_out B g Hpre) as (Ho0 & Hon & Hn & Hoff & HTD & HTW & HRAo & Hhull & Hamo & _).
pose proof (sc_amem47 (sg_q g) (sg_len g) ltac:(lia) ltac:(lia) Hamq) as Hq47.
pose proof (sc_amem47 (sg_o g) (sg_n g) ltac:(lia) ltac:(lia) Hamo) as Ho47.
pose proof Hpre as (HE & _). pose proof HE as (HJ0 & Hra & Hra4 & Hgp & Htp & _).
destruct HC as (HK & R2 & Vra & Vs0 & KC & KPc).
pose proof HK as HK'. repeat (apply Forall_cons_iff in HK' as (? & HK')). cbv beta in *.
unfold sg_sp, sg_len in *. unfold T_scribble_text, ESTACK in *.
pose proof (sc_in_skipn_lt 0 (sg_tb g) (Z.to_nat i + 1)%nat Hin1) as Hilt.
destruct (HGT (Z.to_nat i) ltac:(lia)) as (_ & Hbr). rewrite Hbnth in Hbr.
destruct (HGT (Z.to_nat i + 1)%nat ltac:(lia)) as (Hyv & Hyr).
set (y := nth (Z.to_nat i + 1)%nat (sg_tb g) 0) in *.
assert (Hiq : 0 <= sg_q g + i + 1 <= 2 ^ 47 - 1) by lia.
(* ---- the state at 0x85d1c ---- *)
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr ->
  ew (Ereg regs2 (cw_extra (h_xs g i))) n = getr regs2 rr)
  by (intros nn rr Hnn; apply ew_Ereg_nat; exact Hnn).
assert (E33 : ew (Ereg regs2 (cw_extra (h_xs g i))) 33 = Z_to_bv 64 y)
  by exact (cw_ew_x regs2 (h_xs g i) 0).
assert (E34 : ew (Ereg regs2 (cw_extra (h_xs g i))) 34 = Z_to_bv 64 (sg_q g + i + 1))
  by exact (cw_ew_x regs2 (h_xs g i) 1).
assert (E32 : ew (Ereg regs2 (cw_extra (h_xs g i))) 32 = Z_to_bv 64 SB) by apply cw_ew_SB.
assert (E5 : ew (Ereg regs2 (cw_extra (h_xs g i))) 5 = Z_to_bv 64 8)
  by (rewrite (EE 5%nat 5%bv eq_refl); exact R5).
assert (E6 : ew (Ereg regs2 (cw_extra (h_xs g i))) 6 = Z_to_bv 64 b)
  by (rewrite (EE 6%nat 6%bv eq_refl); exact R6).
assert (E8 : ew (Ereg regs2 (cw_extra (h_xs g i))) 8 = Z_to_bv 64 i)
  by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
assert (E10 : ew (Ereg regs2 (cw_extra (h_xs g i))) 10 = Z_to_bv 64 (sg_q g))
  by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
assert (E11 : ew (Ereg regs2 (cw_extra (h_xs g i))) 11 = Z_to_bv 64 (sg_o g))
  by (rewrite (EE 11%nat 11%bv eq_refl); exact R11).
assert (E12 : ew (Ereg regs2 (cw_extra (h_xs g i))) 12 = Z_to_bv 64 (sg_n g))
  by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
assert (E15 : ew (Ereg regs2 (cw_extra (h_xs g i))) 15 = Z_to_bv 64 j)
  by (rewrite (EE 15%nat 15%bv eq_refl); exact R15).
assert (E16 : ew (Ereg regs2 (cw_extra (h_xs g i))) 16 = Z_to_bv 64 (sg_q g + 1))
  by (rewrite (EE 16%nat 16%bv eq_refl); exact R16).
assert (E17 : ew (Ereg regs2 (cw_extra (h_xs g i))) 17 = Z_to_bv 64 46)
  by (rewrite (EE 17%nat 17%bv eq_refl); exact R17).
assert (HAF : atoms_ok (Ereg regs2 (cw_extra (h_xs g i))) h_AF).
{ unfold h_AF. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E32, E6, E8, E10, E11, E12, E15, E33, E34.
  rewrite !unsigned_lit_small by (try unfold SB; lia).
  rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB.
  repeat split; lia. }
assert (HS : st_ok tfibsegs (Ereg regs2 (cw_extra (h_xs g i)))
  (mkSS PC_H sr_atoms [] None (mkFacts h_AF [] []))
  (restrict (w_H (sg_W g)) (mkst regs2 (Z_to_bv 64 PC_H) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. apply entry_st_ok_full.
  - apply regs_ok_Ereg.
  - reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [exact HAF | split; exact I]. }
remember (Ereg regs2 (cw_extra (h_xs g i))) as E eqn:HEE. clear HEE.
(* a4 holds the shadow offset: the engine's checks read it as atom 32 *)
lazymatch goal with HSv : st_ok _ ?Ev ?ssv ?msv |- _ =>
  let HS3 := fresh "HS" in
  pose proof (st_ok_pin_rege Ev ssv msv (14%bv : bv 5) (SOff 32 0) HSv ltac:(intros X; discriminate X)
    ltac:(cbn [sv_denot]; rewrite E32, unsigned_lit_small, Z.add_0_r by (unfold SB; lia);
          cbn [ms_regs restrict mkst]; symmetry; exact R14)) as HS3;
  clear HSv; rename HS3 into HS; norm_ss HS end.

assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H (sg_W g)) mem2)) by apply Forall_nil.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False ->
  aview tfibsegs (w_H (sg_W g)) mem2 a = aview tfibsegs (w_H (sg_W g)) mem2 a) by (intros; reflexivity).
assert (KP : forall a, apresent (w_H (sg_W g)) mem2 a -> apresent (w_H (sg_W g)) mem2 a) by (intros; assumption).
unfold cfg_at. change (w64 PC_H) with (Z_to_bv 64 PC_H).
pose proof HJ as HJ1. clear HJ. rename HJ1 into HJ.
cw_run h_awr. h_kp mem2. cw_keep cw_kwr_ro.
(* the step's two Gallina facts: the count and the next byte *)
assert (Hk : Z.to_nat (sg_n g - j) = S (Z.to_nat (sg_n g - (j + 1)))) by lia.
pose proof (sc_lib_next (sg_tb g) (Z.to_nat i) (Z.to_nat (sg_n g - (j + 1))) ltac:(lia)
  ltac:(rewrite Hbnth; exact Hbnz)) as Hnext.
replace (S (Z.to_nat i)) with (Z.to_nat i + 1)%nat in Hnext by lia.
replace (S (Z.to_nat i + 1)) with (Z.to_nat (i + 2)) in Hnext by lia.
rewrite Hbnth in Hnext. fold y in Hnext.
rewrite Hk, Hnext in Hspec. cbv [fst snd] in Hspec. clear Hk Hnext.
cw_branch Hb.
all: hc_bool Hb ltac:(fun H => rewrite (cw_U_atom0 _ 6 b ltac:(ewpeel; exact E6) ltac:(lia)) in H);
     hc_prop Hb;
     rewrite (cw_U_atom0 _ 17 46 ltac:(ewpeel; exact E17) ltac:(lia)) in Hb;
     rewrite (sc_and255 b ltac:(lia)) in Hb; rewrite Z.mod_small in Hb by lia.
- (* t1 is not '.': the byte itself below 0x80, else 0x3f *)
  assert (Hbool : (b =? 0x2e) && (0x31 <=? y) && (y <=? 0x39) = false)
    by (rewrite (proj2 (Z.eqb_neq b 0x2e) Hb); reflexivity).
  rewrite Hbool in Hspec. clear Hbool.
  cw_run h_awr. h_kp mem2. cw_keep cw_kwr_ro.
  cw_branch Hs.
  all: lazymatch type of Hs with context [sv_denot ?Ev (SAlu ALU_SLL (SOff 6 0) (SLit 56))] =>
         rewrite (sc_br_sign Ev 6 b ltac:(ewpeel; exact E6) ltac:(lia)) in Hs end.
  + (* below 0x80: the byte itself *)
    apply Z.ltb_lt in Hs.
    cw_run_to h_awr PC_T. h_kp mem2. cw_keep cw_kwr_ro.
    h_close_T g mem2 outs KE KC KP KPc i j b 1.
    rewrite Hspec. cbv [fst snd]. replace (Z.to_nat (i + 1)) with (Z.to_nat i + 1)%nat by lia.
    rewrite (proj2 (Z.ltb_lt b 0x80) Hs). rewrite <- app_assoc. cbn [app].
    f_equal; first [reflexivity | lia].
  + (* 0x80 and above: 0x3f *)
    apply Z.ltb_ge in Hs.
    cw_run_to h_awr PC_T. h_kp mem2. cw_keep cw_kwr_ro.
    h_close_T g mem2 outs KE KC KP KPc i j 0x3f 1.
    rewrite Hspec. cbv [fst snd]. replace (Z.to_nat (i + 1)) with (Z.to_nat i + 1)%nat by lia.
    rewrite (proj2 (Z.ltb_ge b 0x80) Hs). rewrite ?sc_app_snoc. f_equal; first [reflexivity | lia].
- (* t1 is '.': the byte after it decides *)
  cw_run_to h_awr 0x85d28. h_kp mem2. cw_keep cw_kwr_ro.
  lazymatch goal with HSv : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- _ =>
    assert (Ra3 : getr (ms_regs msv) 13 = Z_to_bv 64 (sg_q g + i + 1))
      by (sreg; rewrite (denot_add2 Ev 8 16 i (sg_q g + 1)
            ltac:(ewpeel; exact E8) ltac:(ewpeel; exact E16) ltac:(lia) ltac:(lia) ltac:(lia));
          f_equal; lia) end.
  lazymatch goal with HSv : st_ok _ ?Ev ?ssv ?msv |- _ =>
    let HS3 := fresh "HS" in
    pose proof (st_ok_pin_rege Ev ssv msv (13%bv : bv 5) (SOff 34 0) HSv ltac:(intros X; discriminate X)
      ltac:(cbn [ms_regs restrict mkst]; rewrite Ra3; cbn [sv_denot]; ewpeel;
            rewrite E34; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity)) as HS3;
    clear HSv; rename HS3 into HS; norm_ss HS end.
  lazymatch goal with HSv : st_ok _ ?Ev ?ssv ?msv |- _ =>
    let HS3 := fresh "HS" in
    pose proof (ast_ok_add_region tfibsegs Ev ssv msv h_rtx HSv eq_refl
      ltac:(unfold region_ok, h_rtx;
            cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
            ewpeel; rewrite E34; rewrite unsigned_lit_small by lia;
            split; [lia|]; split; [lia|]; split; [intros oo Hoo; lia|];
            apply Forall_cons; [|apply Forall_nil];
            apply (chunk_ok_val tfibsegs Ev _ (sg_q g + i + 1) 0 1 (SOff 33 0) y);
            [ cbn [sv_denot]; ewpeel; rewrite E33; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
            | cbn; lia | cbn; lia |];
            rewrite Z.add_0_r;
            pose proof (proj1 (sc_text_val B g _ Hpre
              ltac:(intros aa Haa Hzz; rewrite (KE aa Haa ltac:(tauto)); exact (KC aa Haa Hzz))
              (Z.to_nat i + 1)%nat ltac:(lia))) as Hv1;
            replace (sg_q g + Z.of_nat (Z.to_nat i + 1)) with (sg_q g + i + 1) in Hv1 by lia;
            exact Hv1)
      ltac:(unfold h_rtx;
            lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
              let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
            cbn [all_disjoint]; exact I)) as HS3;
    clear HSv; rename HS3 into HS; norm_ss HS end.
  cw_run_ob h_awr
    ltac:(idtac; rewrite (cw_U_atom0 _ 34 (sg_q g + i + 1) ltac:(ewpeel; exact E34) ltac:(lia));
          apply (sc_obl_of (sg_W g) _ _ _ _ (sg_q g) (Z.of_nat (length (sg_tb g))));
          [ apply (sc_ra_kept B g _ Hpre);
            first [ intros aa Haa Hzz; rewrite (KE aa Haa ltac:(tauto)); exact (KC aa Haa Hzz)
                  | exact Hamq | exact HRAq | lia ]
          | ewpeel; exact E32 | lia | lia ]).
  h_kp mem2. cw_keep cw_kwr_ro.
  cw_branch Hd.
  all: hc_bool Hd ltac:(fun H =>
         lazymatch type of H with context [U ?Ev (SOff 33 (-49))] =>
           rewrite (cw_U_offx Ev 33 y (-49) ltac:(ewpeel; exact E33) ltac:(lia)) in H;
           rewrite (cw_U_atom0 Ev 5 8 ltac:(ewpeel; exact E5) ltac:(lia)) in H end);
       hc_prop Hd;
       replace (y + -49) with (y - 49) in Hd by lia;
       rewrite (sc_and255 _ (proj1 (Z.mod_pos_bound (y - 49) (2 ^ 64) ltac:(lia)))) in Hd;
       rewrite (sc_mod_sub y ltac:(lia)) in Hd.
  + (* not a digit: the byte itself *)
    assert (Hbool : ((b =? 0x2e) && (0x31 <=? y) && (y <=? 0x39))%bool = false).
    { assert (Hdg : ((0x31 <=? y) && (y <=? 0x39))%bool = false)
        by (rewrite <- (sc_digit y ltac:(lia)); apply Z.leb_gt; lia).
      destruct (b =? 0x2e); destruct (0x31 <=? y); destruct (y <=? 0x39); cbn in *; congruence. }
    rewrite Hbool in Hspec. clear Hbool.
  cw_run h_awr. h_kp mem2. cw_keep cw_kwr_ro.
  cw_branch Hs.
  all: lazymatch type of Hs with context [sv_denot ?Ev (SAlu ALU_SLL (SOff 6 0) (SLit 56))] =>
         rewrite (sc_br_sign Ev 6 b ltac:(ewpeel; exact E6) ltac:(lia)) in Hs end.
  * apply Z.ltb_lt in Hs.
    cw_run_to h_awr PC_T. h_kp mem2. cw_keep cw_kwr_ro.
    h_close_T g mem2 outs KE KC KP KPc i j b 1.
    rewrite Hspec. cbv [fst snd]. replace (Z.to_nat (i + 1)) with (Z.to_nat i + 1)%nat by lia.
    rewrite (proj2 (Z.ltb_lt b 0x80) Hs). rewrite ?sc_app_snoc. f_equal; first [reflexivity | lia].
  * apply Z.ltb_ge in Hs.
    cw_run_to h_awr PC_T. h_kp mem2. cw_keep cw_kwr_ro.
    h_close_T g mem2 outs KE KC KP KPc i j 0x3f 1.
    rewrite Hspec. cbv [fst snd]. replace (Z.to_nat (i + 1)) with (Z.to_nat i + 1)%nat by lia.
    rewrite (proj2 (Z.ltb_ge b 0x80) Hs). rewrite ?sc_app_snoc. f_equal; first [reflexivity | lia].
  + (* a digit: the byte minus 26, two text bytes *)
    assert (Hy49 : 0x31 <= y <= 0x39).
    { assert (Hdg : ((0x31 <=? y) && (y <=? 0x39))%bool = true)
        by (rewrite <- (sc_digit y ltac:(lia)); apply Z.leb_le; lia).
      apply andb_prop in Hdg. destruct Hdg as (Hd1 & Hd2).
      split; [apply Z.leb_le; exact Hd1 | apply Z.leb_le; exact Hd2]. }
    assert (Hbool : ((b =? 0x2e) && (0x31 <=? y) && (y <=? 0x39))%bool = true)
      by (rewrite (proj2 (Z.eqb_eq b 0x2e) Hb), (proj2 (Z.leb_le 0x31 y) ltac:(lia)),
                  (proj2 (Z.leb_le y 0x39) ltac:(lia)); reflexivity).
    rewrite Hbool in Hspec. clear Hbool.
    cw_run_to h_awr PC_T. h_kp mem2. cw_keep cw_kwr_ro.
    h_close_T g mem2 outs KE KC KP KPc i j (y - 26) 2.
    rewrite Hspec. cbv [fst snd]. rewrite ?sc_app_snoc. f_equal; first [reflexivity | lia].
Time Qed.

End h.
End d.
