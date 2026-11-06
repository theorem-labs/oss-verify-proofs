(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:138-139
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:148-161 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh5.v:99 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACja.v:107-117
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:367-369 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC8w.v:289-290 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan build
   (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACai.v:156-159. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/sb_dec_A.v, with its module paths and module names changed; 231 of its 263 lines of code are new or changed and 973 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/AU/Prog/check_text_counter_B_s0a.v, with its module names changed; 164 of its 201 lines of code are new or changed and 226 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/AU/Prog/check_text_counter_B_n1a.v, with its module names changed; 222 of its 292 lines of code are new or changed and 131 lines of the source are left out. *)
(* Segment N1b of check_text_counter's walk in image B (check_text_counter_B_inv.v): from the entry of __asan_memset
   0x51f84 (cc_cut .. CC_CM) through the runtime's contract (cw_intrin_call: the record's 24 bytes := 0xa5) to its
   return 0x842f4, then s11 = SB + dt / 8, the instrumented check of the store to dt (0x842fc .. 0x84300, its shadow
   entry), dt := 0xa5 (0x84304), a0 = q, a1 = sg, a2 = dt, jal diginet_counter_text: to its entry 0x869e4
   (cc_cut .. B_COUNTER_TEXT). The memset writes the record and its stack below sp1; the run writes dt. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require YE2y.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgWalkU CPgWalkKeptU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkFrameU CPgWalkIntrU check_text_scribble_B_inv.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_s0a check_text_scribble_B_s0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_base check_text_scribble_B_lst.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_l check_text_scribble_B_f.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_mi check_text_scribble_B_m2.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_counter_B_inv check_text_counter_B_base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the state at 0x842f4: s8 = SB (atom 32), dt a writable byte at atom 20 *)
Definition cc_dtr : YP09.region := YP09.mkRegion (Some 20%nat) 0 1 0 1 [].

(* the zone of the run's writes: dt *)
Ltac cc_kwr :=
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb); cbv beta;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  repeat (destruct Hr as [<- | Hr];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; ewpeel_in Hb;
      lazymatch goal with U20 : bv_unsigned (ew _ 20) = _ |- _ => rewrite U20 in Hb end; lia | ]);
  destruct Hr.
(* the byte the run stored into dt, the state's one region *)
Ltac cc_vn Vn :=
  lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict ?Hh ?msv), U20 : bv_unsigned (ew _ 20) = ?b |- _ =>
    let HR := fresh "HR" in
    pose proof (st_ok_region_nth Ev ssv (restrict Hh msv) 0 _ HS eq_refl) as HR;
    cbn [ms_mem restrict] in HR;
    pose proof (field_of_region_any _ _ 20 b _ 0 1 0 1 0 1%N _ HR ltac:(ewpeel; exact U20) ltac:(left; reflexivity)
      ltac:(cbn; lia)) as Vn;
    clear HR; change (N.to_nat 1) with 1%nat in Vn; rewrite Z.add_0_r in Vn end.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables SEG7TBL GLYPHA : Z.
Variable ROSTRS : list (Z * Z).
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis MSET : aintrin_realizes tfibsegs B OSet CC_CM.

Theorem cc_n1b_holds : cc_seg_N1b B MT SEG7TBL GLYPHA ROSTRS.
Proof.
unfold cc_seg_N1b. intros g pos W2 c2 Hpre Hnow Hc.
destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HK & HP & Hni & Hio & Hmo & HC & HL).
destruct HL as (R1 & R10 & R11 & R12 & R18 & R19 & R23 & Howres).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as Hac.
pose proof HC as (R8 & R2 & R9 & R3 & R4 & R25 & R22 & R26 & R24 & R21 & R20 & _).
pose proof Hpre as (HE & _ & _ & _ & Hosg & Hodt & _ & (Hsg0 & Hsgn & Hsgtd & Hsgtw & _ & _ & Hsgam & Hsgwin) & _ & _ & _ &
  (Hdt0 & Hdtn & Hdttd & Hdttw & _ & _ & Hdtam & Hdtwin) & _ & Hd1 & _ & _ & _ & _ & _).
pose proof HE as (_ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hlive).
pose proof (proj1 (proj1 HE)) as HARc.
destruct (cc_stack B SEG7TBL GLYPHA ROSTRS g Hpre) as (Hceil & H47 & H46 & Hal & Hsp1 & Hsp1a & Hwin & Hsp0).
destruct (cc_frame B SEG7TBL GLYPHA ROSTRS LAWS g pos ly2 S2 W2 mem2 md2 Hpre HJ)
  as (Hfr & Efa & Efl & HF0 & HFc & HF64 & HFapp & HFp).
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & _) & _).
specialize (Hnow pos ly2 S2 W2 mem2 md2 HJ HK HP Hni) as (_ & (Hsgra & Hsghull) & (Hdtra & _)).
assert (Hsp1m : cc_sp1 g mod 16 = 0).
{ pose proof (Z.div_mod (cc_sp1 g) 32 ltac:(lia)) as D. rewrite Hsp1a, Z.add_0_r in D. rewrite D.
  replace (32 * (cc_sp1 g / 32)) with ((2 * (cc_sp1 g / 32)) * 16) by lia. apply Z_mod_mult. }
assert (HsgS : cc_sg g + 24 <= cc_sp g - 8384 \/ cc_sp g <= cc_sg g)
  by (unfold coff_win, TB_check_text_counter, ESTACK in Hsgwin; lia).
assert (HdtS : cc_dt g + 1 <= cc_sp g - 8384 \/ cc_sp g <= cc_dt g)
  by (unfold coff_win, TB_check_text_counter, ESTACK in Hdtwin; lia).
assert (HF8 : 0 <= cc_F g pos / 8 /\ 8 * (cc_F g pos / 8) <= cc_F g pos)
  by (split; [apply Z.div_pos | apply Z.mul_div_le]; lia).
assert (Hbl : forall b m, In (b, m) (ablocks B (cc_lyc g) (cc_Sc g)) -> In (b, m) (ablocks B ly2 S2))
  by (intros b m Hin; exact (Permutation_in _ (Permutation_sym HP) Hin)).
assert (Hfi : forall c p, In (c, p) (frames (cc_Sc g)) -> In (c, p) (frames S2))
  by (intros c p Hin; rewrite Hfr; right; exact Hin).
assert (Hsgapp : forall a, cc_sg g <= a < cc_sg g + 24 -> 4096 <= a < alloc_ceiling /\
  (a + 1 <= kLowShadowBeg \/ kHighMemBeg <= a))
  by (intros a Ha; exact (cj_dst_byte tfibsegs B LAWS _ _ _ _ _ _ _ a HARc Hsgtd Ha)).
assert (Hdtapp : 4096 <= cc_dt g < alloc_ceiling /\ (cc_dt g + 1 <= kLowShadowBeg \/ kHighMemBeg <= cc_dt g))
  by (exact (cj_dst_byte tfibsegs B LAWS _ _ _ _ _ _ _ (cc_dt g) HARc Hdttd ltac:(lia))).
(* the state at 0x51f84: ra = 0x842f4, s8 = SB *)
set (E := Ereg regs2 (cw_extra [])).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs2 r)
  by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (HS : st_ok tfibsegs E (mkSS CC_CM (sr_set (sr_set sr_atoms 1%bv (SLit 0x842f4)) 24%bv (SOff 32 0)) [] None
    (mkFacts [(32%nat, mkAF SB SB 0)] [] []))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 CC_CM) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_pin; [apply regs_ok_pin; [subst E; apply regs_ok_Ereg | intros Hx; discriminate Hx |]
      | intros Hx; discriminate Hx |].
    all: first [ rewrite R24; cbn [sv_denot]; rewrite cw_ew_SB, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
               | rewrite R1; reflexivity ].
  - reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite cw_ew_SB, unsigned_lit_small by (unfold SB; lia). unfold SB. split; [|exact I]. split; [lia|].
    split; [reflexivity | lia]. }
clearbody E.
cw_keep_j0 HJ HJ0.
unfold cfg_at. change (w64 CC_CM) with (Z_to_bv 64 CC_CM).
eapply (cw_intrin_call B LAWS OSet CC_CM MSET W2 E _ _ md2 (cc_STK g) (cc_sp0 g) (cc_FP g) (cc_ly g) (cc_S g)
    (cc_W0 g) (cc_mem0 g) (cc_md0 g) ((0, pos) :: cc_own g) ly2 S2 (cc_k g) (cc_sg g) 165 24 0x842f4
    (run_K 0 (SOff 32 0) [] (mkSS CC_CM (sr_set (sr_set sr_atoms 1%bv (SLit 0x842f4)) 24%bv (SOff 32 0)) [] None
      (mkFacts [(32%nat, mkAF SB SB 0)] [] []))) [] _ HS eq_refl eq_refl HJ);
  [ exact R10 | exact R11 | exact R12
  | lia | lia | lia
  | unfold mkst; cbn [ms_regs]; unfold spZ; rewrite R2, unsigned_lit_small by lia; unfold ESTACK; lia
  | unfold mkst; cbn [ms_regs]; unfold spZ; rewrite R2, unsigned_lit_small by lia; lia
  | unfold mkst; cbn [ms_regs]; unfold spZ; rewrite R2, unsigned_lit_small by lia; exact Hsp1m
  | exact Hsp0al
  | unfold mkst; cbn [ms_regs]; rewrite R3; exact Hgp
  | unfold mkst; cbn [ms_regs]; rewrite R4; exact Htp
  | reflexivity
  | lia
  | apply ret_ok_even; vm_compute; reflexivity
  | intros a Ha; destruct (Hsgtw a Ha) as (Haw & _ & _ & _);
    split;
    [ apply (bsm_awr_mono _ _ _ _ _ _ _ _ _ _ _ Haw); [exact Hbl | apply incl_tl, incl_refl | exact Efa]
    | unfold mkst; cbn [ms_regs]; unfold spZ; rewrite R2, unsigned_lit_small by lia; unfold ESTACK; lia ]
  | exact Hsgam
  | exact Hsgra
  | intros _; exact Hsghull
  | exact I
  | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
  | cbn [ss_mem]; submem_to
  | apply Forall_nil
  | ].
intros regs3 mem3 md3 HJm HPm3 Ha0m Hset Hkeptm Hpresm Hsbm HSm.
clear HSm HS E32. clear HJ. rename HJm into HJ.
pose proof (same_io_materialized _ _ Hsbm) as HIOm. clear Hsbm.
unfold mkst in Hkeptm, HPm3. cbn [ms_regs ms_mem] in Hkeptm, HPm3, Hpresm.
unfold spZ in Hkeptm. rewrite R2, unsigned_lit_small in Hkeptm by lia. unfold ESTACK in Hkeptm.
assert (CS : forall r, acallee_saved r -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) by exact HPm3.
assert (G : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> acallee_saved (Z.of_nat nn) -> getr regs3 r = getr regs2 r).
{ intros nn r Hnn Hcs. pose proof (CS _ Hcs) as Hc. rewrite Hnn, !Z_to_bv_bv_unsigned in Hc. exact Hc. }
assert (Q20 : getr regs3 20 = w64 (cc_dt g)) by (rewrite (G 20%nat 20%bv eq_refl ltac:(unfold acallee_saved; lia)); exact R20).
assert (Q24 : getr regs3 24 = w64 SB) by (rewrite (G 24%nat 24%bv eq_refl ltac:(unfold acallee_saved; lia)); exact R24).
assert (Q18 : getr regs3 18 = w64 165) by (rewrite (G 18%nat 18%bv eq_refl ltac:(unfold acallee_saved; lia)); exact R18).
(* the usable mark of dt and its presence, after the memset *)
assert (Hdtpr : apresent (w_H W2) mem2 (cc_dt g)).
{ apply (bsm_tdst_present B LAWS ly2 S2 W2 mem2 md2 (cc_dt g) 1 (cc_dt g) HAR2); [|lia].
  exact (bsm_tdst_mono B (cc_lyc g) (cc_Sc g) ly2 S2 (cc_dt g) 1 Hdttd Hbl Hfi Efa). }
assert (Hdtra3 : range_addressable (aview tfibsegs (w_H W2) mem3) SHADOW_OFF (cc_dt g) 1).
{ intros x Hx. destruct (Hdtra x Hx) as (sv & Hs & Hok). exists sv. split; [|exact Hok].
  rewrite Hkeptm; [exact Hs | | |];
  unfold shadow_of_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *;
  assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia);
  [lia | intros Hr; destruct (Hsgapp _ Hr) as (_ & [Hz|Hz]); lia | lia]. }
(* the state at 0x842f4: s8 = SB (atom 32), dt a writable byte at atom 20 *)
set (E3 := Ereg regs3 (cw_extra [])).
assert (EE3 : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E3 nn = getr regs3 r)
  by (intros nn r Hnn; subst E3; apply ew_Ereg_nat; exact Hnn).
assert (E32 : ew E3 32 = Z_to_bv 64 SB) by (subst E3; apply cw_ew_SB).
assert (E20 : ew E3 20 = Z_to_bv 64 (cc_dt g)) by (rewrite (EE3 20%nat 20%bv eq_refl); exact Q20).
assert (U20 : bv_unsigned (ew E3 20) = cc_dt g) by (rewrite E20; apply unsigned_lit_small; lia).
assert (HS : st_ok tfibsegs E3 (mkSS 0x842f4 (sr_set sr_atoms 24%bv (SOff 32 0)) [cc_dtr] None
    (mkFacts [(32%nat, mkAF SB SB 0); (20%nat, mkAF 4096 (2 ^ 47 - 2) 0)] [] []))
  (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 0x842f4) mem3 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs); change (Ereg regs3 (cw_extra [])) with E3.
  - apply regs_ok_pin; [subst E3; apply regs_ok_Ereg | intros Hx; discriminate Hx |].
    rewrite Q24. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold region_ok, cc_dtr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U20. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros oo Hoo. apply (apresent_writable tfibsegs). replace (cc_dt g + oo) with (cc_dt g) by lia.
    exact (Hpresm _ Hdtpr).
  - apply pairwise_disjoint_of_extents. unfold cc_dtr, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E32, U20, unsigned_lit_small by (unfold SB; lia). rewrite Z.pow_0_r, !Z.mod_1_r.
    unfold SB. split; [repeat split; lia|]. split; [repeat split; unfold amem_range, kHighMemEnd in *; lia|]. exact I. }
clearbody E3.
assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 20 0 1] E3 (mrestrict (w_H W2) mem3)).
{ apply Forall_cons; [|apply Forall_nil].
  exact (cw_shent_ra W2 mem3 E3 20 (cc_dt g) 1 Hdtra3 ltac:(unfold amem_range in *; lia) ltac:(lia) ltac:(lia) ltac:(lia)
    E20 E32). }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (a = cc_dt g) ->
  aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem3 a) by (intros; reflexivity).
assert (KP : forall a, apresent (w_H W2) mem3 a -> apresent (w_H W2) mem3 a) by (intros; assumption).
(* 0x842f4 .. 0x84314: s11 = SB + dt / 8, the instrumented check, dt := 0xa5, a0 = q, a1 = sg, a2 = dt *)
cw_run_to ltac:(cw_awrA;
  lazymatch goal with |- awr_ok ?Ev ?rs ?stk ?s0 ?fp ?b0 ?bc ?lyv ?ownv =>
    let rs' := eval vm_compute in rs in change (awr_ok Ev rs' stk s0 fp b0 bc lyv ownv) end;
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 20%nat);
  [ reflexivity | exact U20
  | let a := fresh "a" in let Ha := fresh "Ha" in let Haw := fresh "Haw" in
    intros a Ha; cbn in Ha; destruct (Hdttw a ltac:(lia)) as (Haw & _);
    exact (bsm_awr_mono _ _ _ _ _ _ _ _ _ _ _ Haw Hbl (incl_tl _ (incl_refl _)) Efa)
  | apply awr_ok_nil ]) B_COUNTER_TEXT.
ctk_keep cc_kwr.
cc_vn Vn.
lazymatch type of Vn with context [bv_unsigned (sv_denot ?Ev ?e) mod _] =>
  rewrite (bsl_byte_of Ev e 165 ltac:(apply (U_atom Ev 18 165); [ewpeel; rewrite (EE3 18%nat 18%bv eq_refl); exact Q18 | lia])
    ltac:(lia)) in Vn end.
assert (EC : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> acallee_saved (Z.of_nat nn) -> ew E3 nn = getr regs2 r)
  by (intros nn r Hnn Hcs; rewrite (EE3 nn r Hnn); exact (G nn r Hnn Hcs)).
assert (E19 : ew E3 19 = w64 (cc_sg g)) by (rewrite (EC 19%nat 19%bv eq_refl ltac:(unfold acallee_saved; lia)); exact R19).
assert (E21 : ew E3 21 = w64 (cc_q g)) by (rewrite (EC 21%nat 21%bv eq_refl ltac:(unfold acallee_saved; lia)); exact R21).
assert (E23 : ew E3 23 = w64 (cc_ro g)) by (rewrite (EC 23%nat 23%bv eq_refl ltac:(unfold acallee_saved; lia)); exact R23).
assert (E20' : ew E3 20 = w64 (cc_dt g)) by exact E20.
(* everything but the record, the memset's stack and dt is as at the memset's entry *)
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msv) |- _ =>
  assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (cc_sg g <= a < cc_sg g + 24) -> ~ (cc_sp1 g - 4096 <= a < cc_sp1 g) ->
    ~ (a = cc_dt g) -> aview tfibsegs (w_H W2) (ms_mem msv) a = aview tfibsegs (w_H W2) mem2 a)
    by (intros a Ha H1 H2 H3; rewrite (KE a Ha H3); exact (Hkeptm a Ha H1 H2));
  assert (KPALL : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msv) a)
    by (intros a Hp; exact (KP a (Hpresm a Hp)))
end.
assert (HFF : forall a, (cc_F g pos <= a < cc_F g pos + 64) \/ (SB + cc_F g pos / 8 <= a < SB + cc_F g pos / 8 + 8) ->
  cw_fresh B (cc_lyc g) (cc_Sc g) a)
  by (intros a Ha; exact (cc_fresh B SEG7TBL GLYPHA ROSTRS LAWS g pos ly2 S2 W2 mem2 md2 a Hpre HJ0 HP Ha)).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
assert (KOFF : forall a, (cc_sp g - 104 <= a < cc_sp g) \/ (cc_F g pos + 56 <= a < cc_F g pos + 64) \/
    (SB + cc_F g pos / 8 <= a < SB + cc_F g pos / 8 + 8) \/ (cc_sp1 g + 24 <= a < cc_sp1 g + 32) ->
    aview tfibsegs (w_H W2) (ms_mem ms) a = aview tfibsegs (w_H W2) mem2 a).
{ intros a Ha. apply KALL.
  - unfold SB in *. lia.
  - intros Hr. destruct Ha as [Ha | [Ha | [Ha | Ha]]]; [lia | | | lia].
    + exact (cc_obj_not_fresh B _ _ _ _ a Hosg Hr (HFF a ltac:(left; lia))).
    + destruct (Hsgapp a Hr) as (_ & [Hz|Hz]); unfold SB, kLowShadowBeg, kHighMemBeg in *; lia.
  - unfold SB in *. lia.
  - intros ->. destruct Ha as [Ha | [Ha | [Ha | Ha]]]; [lia | | | lia].
    + exact (cc_obj_not_fresh B _ _ _ _ (cc_dt g) Hodt ltac:(lia) (HFF (cc_dt g) ltac:(left; lia))).
    + destruct Hdtapp as (_ & [Hz|Hz]); unfold SB, kLowShadowBeg, kHighMemBeg in *; lia. }
apply SRr_ret.
lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- context [mkCfg _ ?md4] =>
  pose proof (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) as Hms;
  exists ly2, S2, (ms_regs msv), (ms_mem msv), md4;
  split; [unfold cfg_at, w64; rewrite Hms at 1; reflexivity|]
end.
split; [exact HJ|].
split.
{ apply (cw_kept_step B LAWS TB_check_text_counter (cc_lyc g) (cc_Sc g) (cc_W g) (cc_memc g) (cc_mdc g) W2 mem2
    (ms_mem ms) (cc_sp g) (cc_wr g)
    (fun a => (cc_sg g <= a < cc_sg g + 24) \/ (cc_sp1 g - 4096 <= a < cc_sp1 g) \/ a = cc_dt g));
  [ unfold TB_check_text_counter, ESTACK; lia | exact HARc | exact HK
  | intros a Ha Hx; apply KALL; [exact Ha | intros H; apply Hx; left; exact H | intros H; apply Hx; right; left; exact H
                                | intros H; apply Hx; right; right; exact H]
  | intros a [Ha | [Ha | Ha]];
    [ right; left; split; [left; exact Ha|]; intros Him;
      exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low _ _ _ _ _ _ _ a HARc Hsgtd Ha Him)
    | left; unfold TB_check_text_counter, ESTACK; lia
    | subst a; right; left; split; [right; lia|]; intros Him;
      exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low _ _ _ _ _ _ _ (cc_dt g) HARc Hdttd ltac:(lia) Him) ]
  | exact KPALL ]. }
split; [exact HP|]. split; [exact Hni|].
lazymatch type of HIOm with same_io ?mA _ =>
  assert (HIO1 : same_io (cc_mdc g) mA) by (eapply same_io_trans; [exact Hio | kio]) end.
split; [eapply same_io_trans; [exact (same_io_trans _ _ _ HIO1 HIOm) | kio]|].
split; [exact Hmo|].
split.
{ apply (cc_common_keep g pos regs2 mem2 W2 _ _ W2 HC);
  [ bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf
  | rv; rewrite ?sv_denot_SOff0; ewpeel; rewrite E32, R24; reflexivity
  | bsm_rf | bsm_rf | exact KOFF ]. }
split; [bsm_rf|]. split; [bsm_rf|]. split; [bsm_rf|]. split; [bsm_rf|]. split; [bsm_rf|]. split; [bsm_rf|].
split.
{ lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msv) |- _ => bs_rreg0 HS (27%bv : bv 5) G27 end.
  rewrite G27.
  lazymatch goal with |- sv_denot ?Ev _ = _ =>
    rewrite (denot_shx Ev 20 32 0 (cc_dt g) SB ltac:(ewpeel; exact E20) ltac:(ewpeel; exact E32) ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(unfold SB; lia)), Z.add_0_r end.
  reflexivity. }
split.
{ intros j Hj. rewrite repeat_length in Hj. rewrite (bsf_nth_repeat 24 j 165 0 Hj). split; [|lia].
  apply YE2y.val_mem1_of_aview. rewrite KE by (first [lia | intros He; destruct Hd1; lia]).
  rewrite (Hset (Z.of_nat j) ltac:(lia)). reflexivity. }
split; [exact Vn|].
destruct Howres as (sw & v2 & Gw & Lw & Vw & Hw).
exists sw, v2.
split; [apply (bs_garr8_kept (w_H W2) (w_H W2) mem2 _); [|exact Gw]; intros a Ha; rewrite Lw in Ha;
        apply KALL; [lia | | lia |];
        [ intros Hr; exact (cc_obj_not_fresh B _ _ _ _ a Hosg Hr (HFF a ltac:(left; lia)))
        | intros ->; exact (cc_obj_not_fresh B _ _ _ _ (cc_dt g) Hodt ltac:(lia) (HFF (cc_dt g) ltac:(left; lia))) ]|].
split; [exact Lw|].
split; [apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 _ _ 1 _); [|exact Vw]; intros a Ha; cbn in Ha;
        apply KALL; [lia | | lia | lia];
        intros Hr; unfold coff_win, TB_check_text_counter, ESTACK in Hsgwin; lia|].
exact Hw.
Qed.
End s.
