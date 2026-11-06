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
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/AU/Prog/check_text_counter_B_n1a.v, with its module names changed; 190 of its 263 lines of code are new or changed and 128 lines of the source are left out. *)
(* Segment N3 of check_text_counter's walk in image B (check_text_counter_B_inv.v): from the entry of the compare
   wrapper 0x42430 (cc_cut .. CC_CB, both results 0) through its contract (abcmp_realizes: the record's first 8 bytes
   and want's, equal, so a0 = 0) to its return 0x84330, then 0x84330 bnez a0 (not taken); the instrumented check of
   the load of dt (0x84334 .. 0x84338 through s11 = SB + dt / 8, its shadow entry); dt against the want dots byte
   55(s1) (0x8433c .. 0x84344: the two bytes are the same d, so bne is not taken); the UBSan check of sg + 8 at
   0x8434c (not taken: sg is below 2 ^ 47), s3 = sg + 8, a1 = 0, a2 = 0xa5, a3 = ~(sg + 8), a4 = 16: to the fuzz_all
   loop's head 0x84364 (cc_cut .. CC_FL). The wrapper writes only its 2 * 4096 bytes below sp1. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkFrameU CPgWalkCallU check_text_scribble_B_inv.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_base check_text_scribble_B_l.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_s0a check_text_scribble_B_s0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_f check_text_scribble_B_mi.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_m2 check_text_scribble_B_m3.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_counter_B_inv check_text_counter_B_base.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_counter_B_n2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the state at 0x84330: s8 = SB, s11 = SB + dt / 8 as the shadow address the instrumented check computes; dt and
   the want dots byte hold the same d (atom 33) *)
Definition cc3_sr : list sv :=
  sr_set (sr_set sr_atoms 24%bv (SOff 32 0)) 27%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 20 0) (SLit 3)) (SOff 32 0)).
Definition cc3_dt : YP09.region := YP09.mkRegion (Some 20%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition cc3_dot : YP09.region := YP09.mkRegion (Some 9%nat) 55 56 55 55 [YP09.mkChunk 55 (CVal 1 (SOff 33 0))].
Definition cc3_G : facts :=
  mkFacts [(32%nat, mkAF SB SB 0); (20%nat, mkAF 4096 (2 ^ 47 - 2) 0); (33%nat, mkAF 0 255 0)] [] [].

Lemma cc_vm1_mod : forall (m : word -> option byte) a x, val_mem tfibsegs m a 1 x -> val_mem tfibsegs m a 1 (x mod 256).
Proof.
intros m a x Hv k Hk. rewrite (Hv k Hk). f_equal. f_equal. unfold YO0f.le_byte.
change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables SEG7TBL GLYPHA : Z.
Variable ROSTRS : list (Z * Z).
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ABCMP : abcmp_realizes tfibsegs B CC_CB.

Theorem cc_n3_holds : cc_seg_N3 B MT SEG7TBL GLYPHA ROSTRS.
Proof.
unfold cc_seg_N3. intros g pos W2 c2 Hpre Hnow Hc.
destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HK & HP & Hni & Hio & Hmo & HC & HL).
destruct HL as (R1 & R10 & R11 & R12 & R19 & R27 & s & d & Ls & Grec & Gw & Vdt & Vdot).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as Hac.
pose proof HC as (R8 & R2 & R9 & R3 & R4 & R25 & R22 & R26 & R24 & R21 & R20 & _).
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsh & _).
pose proof Hpre as (HE & _ & _ & _ & Hosg & Hodt & _ & (Hsg0 & Hsgn & Hsgtd & Hsgtw & _ & _ & Hsgam & Hsgwin) & _ & _ & _ &
  (Hdt0 & Hdtn & Hdttd & Hdttw & _ & _ & Hdtam & Hdtwin) & _ & Hd1 & _ & _ & _ & _ & _).
pose proof HE as (_ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hlive).
pose proof (proj1 HE) as HJc. pose proof (proj1 HJc) as HARc.
destruct (cc_stack B SEG7TBL GLYPHA ROSTRS g Hpre) as (Hceil & H47 & H46 & Hal & Hsp1 & Hsp1a & Hwin & Hsp0).
destruct (cc_frame B SEG7TBL GLYPHA ROSTRS LAWS g pos ly2 S2 W2 mem2 md2 Hpre HJ)
  as (Hfr & Efa & Efl & HF0 & HFc & HF64 & HFapp & HFp).
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & _) & _).
specialize (Hnow pos ly2 S2 W2 mem2 md2 HJ HK HP Hni) as (_ & (Hsgra & Hsghull) & (Hdtra & _)).
assert (Hsp1m : cc_sp1 g mod 16 = 0).
{ pose proof (Z.div_mod (cc_sp1 g) 32 ltac:(lia)) as D. rewrite Hsp1a, Z.add_0_r in D. rewrite D.
  replace (32 * (cc_sp1 g / 32)) with ((2 * (cc_sp1 g / 32)) * 16) by lia. apply Z_mod_mult. }
assert (Esp : spZ regs2 = cc_sp1 g) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
assert (HsgS : cc_sg g + 24 <= cc_sp g - 8384 \/ cc_sp g <= cc_sg g)
  by (unfold coff_win, TB_check_text_counter, ESTACK in Hsgwin; lia).
assert (HdtS : cc_dt g + 1 <= cc_sp g - 8384 \/ cc_sp g <= cc_dt g)
  by (unfold coff_win, TB_check_text_counter, ESTACK in Hdtwin; lia).
unfold in_app in HFapp.
assert (HF8 : cc_F g pos mod 8 = 0).
{ pose proof (Z.div_mod (cc_F g pos) 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
  replace (64 * (cc_F g pos / 64)) with ((8 * (cc_F g pos / 64)) * 8) by lia. apply Z.mod_mul. lia. }
assert (Hsgapp : forall a, cc_sg g <= a < cc_sg g + 24 -> 4096 <= a < alloc_ceiling /\
  (a + 1 <= kLowShadowBeg \/ kHighMemBeg <= a))
  by (intros a Ha; exact (cj_dst_byte tfibsegs B LAWS _ _ _ _ _ _ _ a HARc Hsgtd Ha)).
assert (Hdtapp : 4096 <= cc_dt g < alloc_ceiling /\ (cc_dt g + 1 <= kLowShadowBeg \/ kHighMemBeg <= cc_dt g))
  by (exact (cj_dst_byte tfibsegs B LAWS _ _ _ _ _ _ _ (cc_dt g) HARc Hdttd ltac:(lia))).
(* the record's first 8 bytes and want's agree *)
assert (Heq : forall i, 0 <= i < 8 ->
  aview tfibsegs (w_H W2) mem2 (cc_sg g + i) = aview tfibsegs (w_H W2) mem2 (cc_F g pos + 32 + i)).
{ intros i Hi. destruct (Grec (Z.to_nat i)) as (V1 & B1); [rewrite length_app, repeat_length, Ls; lia|].
  destruct (Gw (Z.to_nat i) ltac:(rewrite Ls; lia)) as (V2 & B2).
  rewrite app_nth1 in V1, B1 by (rewrite Ls; lia).
  rewrite Z2Nat.id in V1, V2 by lia.
  rewrite (aview_of_val_mem1 tfibsegs _ _ _ _ V1 B1), (aview_of_val_mem1 tfibsegs _ _ _ _ V2 B2). reflexivity. }
eapply SRr_bind.
{ apply (cw_bcmp_at B LAWS CC_CB ABCMP W2 regs2 mem2 (cc_STK g) (cc_sp0 g) (cc_FP g) (cc_ly g) (cc_S g) (cc_W0 g)
    (cc_mem0 g) (cc_md0 g) ((0, pos) :: cc_own g) ly2 S2 md2 (cc_k g) (cc_sg g) (cc_F g pos + 32) 8
    (cc_sp1 g - cc_sp0 g) (w64 0x84330)).
  - exact HJ.
  - exact R10.
  - exact R11.
  - exact R12.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - rewrite Esp. lia.
  - rewrite Zminus_mod, Hsp1m, Hsp0al. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact R1.
  - apply ret_ok_even. vm_compute. reflexivity.
  - intros a Ha. split; [|rewrite Esp; unfold ESTACK; lia].
    destruct (Grec (Z.to_nat (a - cc_sg g))) as (Va & Ba); [rewrite length_app, repeat_length, Ls; lia|].
    rewrite Z2Nat.id in Va by lia. replace (cc_sg g + (a - cc_sg g)) with a in Va by lia.
    rewrite (aview_of_val_mem1 tfibsegs _ _ _ _ Va Ba). discriminate.
  - intros a Ha. split; [|rewrite Esp; unfold ESTACK; lia].
    destruct (Gw (Z.to_nat (a - (cc_F g pos + 32)))) as (Va & Ba); [rewrite Ls; lia|].
    rewrite Z2Nat.id in Va by lia. replace (cc_F g pos + 32 + (a - (cc_F g pos + 32))) with a in Va by lia.
    rewrite (aview_of_val_mem1 tfibsegs _ _ _ _ Va Ba). discriminate.
  - intros a Ha. unfold ESTACK. lia.
  - intros a Ha. unfold ESTACK. lia.
  - unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg in *. lia.
  - unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg, kLowShadowBeg, ASAN_CEIL in *. lia.
  - intros x Hx. apply Hsgra. lia.
  - intros Hn0. exact (bsm_hull_sub _ (cc_sg g) 8 24 ltac:(lia) ltac:(lia) Hsghull).
  - apply (bs_ra_want (w_H W2) mem2 (cc_F g pos) 32 8); [exact HF8 | lia | lia | lia | exact Hsh].
  - intros Hn0. apply (bsm_want_hull (w_H W2) mem2 (cc_F g pos) 8 HF64 ltac:(lia) ltac:(lia) Hsh). }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & v & -> & HJ3 & HP3 & Hv & Hcmp & Hkept & Hpres3 & Hsame).
assert (Hv0 : v = w64 0) by (apply Hcmp; exact Heq).
pose proof (same_io_materialized _ _ Hsame) as HIO3. clear Hsame.
unfold ESTACK in Hkept. replace (cc_sp0 g + (cc_sp1 g - cc_sp0 g)) with (cc_sp1 g) in Hkept by lia.
assert (CS : forall r, acallee_saved r -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) by exact HP3.
assert (G : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> acallee_saved (Z.of_nat nn) -> getr regs3 r = getr regs2 r).
{ intros nn r Hnn Hcs. pose proof (CS _ Hcs) as Hc. rewrite Hnn, !Z_to_bv_bv_unsigned in Hc. exact Hc. }
(* what the wrapper kept: everything but its stack below sp1 *)
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (cc_sp1 g - 8192 <= a < cc_sp1 g) ->
  aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) by exact Hkept.
pose proof (cc_vm1_mod _ _ _ Vdt) as Vdt1. pose proof (cc_vm1_mod _ _ _ Vdot) as Vdot1.
assert (Hd8 : 0 <= d mod 256 < 256) by (apply Z.mod_pos_bound; lia).
(* the state at 0x84330 *)
set (E := Ereg regs3 (cw_extra [d mod 256])).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs3 r)
  by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
assert (EC : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> acallee_saved (Z.of_nat nn) -> ew E nn = getr regs2 r)
  by (intros nn r Hnn Hcs; rewrite (EE nn r Hnn); exact (G nn r Hnn Hcs)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (E33 : ew E 33 = Z_to_bv 64 (d mod 256)) by (subst E; exact (cw_ew_x regs3 [d mod 256] 0)).
assert (E20 : ew E 20 = Z_to_bv 64 (cc_dt g)) by (rewrite (EC 20%nat 20%bv eq_refl ltac:(unfold acallee_saved; lia)); exact R20).
assert (E9 : ew E 9 = Z_to_bv 64 (cc_sp1 g)) by (rewrite (EC 9%nat 9%bv eq_refl ltac:(unfold acallee_saved; lia)); exact R9).
assert (U20 : bv_unsigned (ew E 20) = cc_dt g) by (rewrite E20; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = cc_sp1 g) by (rewrite E9; apply unsigned_lit_small; lia).
assert (Hdtra3 : range_addressable (aview tfibsegs (w_H W2) mem3) SHADOW_OFF (cc_dt g) 1).
{ intros x Hx. destruct (Hdtra x Hx) as (sv & Hs & Hok). exists sv. split; [|exact Hok].
  rewrite KW; [exact Hs | |];
  unfold shadow_of_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *;
  assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia); lia. }
assert (HS : st_ok tfibsegs E (mkSS 0x84330 cc3_sr [cc3_dt; cc3_dot] None cc3_G)
  (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 0x84330) mem3 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs); change (Ereg regs3 (cw_extra [d mod 256])) with E.
  - unfold cc3_sr. apply regs_ok_pin; [apply regs_ok_pin; [subst E; apply regs_ok_Ereg | intros Hx; discriminate Hx |]
      | intros Hx; discriminate Hx |].
    + rewrite (G 24%nat 24%bv eq_refl ltac:(unfold acallee_saved; lia)), R24.
      cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    + rewrite (G 27%nat 27%bv eq_refl ltac:(unfold acallee_saved; lia)), R27.
      rewrite (denot_shx E 20 32 0 (cc_dt g) SB E20 E32 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)), Z.add_0_r.
      reflexivity.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold region_ok, cc3_dt. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U20. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ (cc_dt g) 0 1 (SOff 33 0) (d mod 256));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3 _ 1 _); [|exact Vdt1].
      intros x Hx. cbn in Hx. apply KW; [lia | lia].
    + unfold region_ok, cc3_dot. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ (cc_sp1 g) 55 1 (SOff 33 0) (d mod 256));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3 _ 1 _); [|exact Vdot1].
      intros x Hx. cbn in Hx. apply KW; [lia | lia].
  - apply pairwise_disjoint_of_extents. unfold cc3_dt, cc3_dot, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U20, U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok cc3_G]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E32, U20, unsigned_lit_small by (unfold SB; lia). rewrite E33, unsigned_lit_small by lia.
    rewrite Z.pow_0_r, !Z.mod_1_r.
    unfold SB. split; [repeat split; lia|]. split; [repeat split; unfold amem_range, kHighMemEnd in *; lia|].
    split; [repeat split; lia|]. exact I. }
clearbody E.
assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 20 0 1] E (mrestrict (w_H W2) mem3)).
{ apply Forall_cons; [|apply Forall_nil].
  exact (cw_shent_ra W2 mem3 E 20 (cc_dt g) 1 Hdtra3 ltac:(unfold amem_range in *; lia) ltac:(lia) ltac:(lia) ltac:(lia)
    E20 E32). }
assert (E10 : ew E 10 = w64 0) by (rewrite (EE 10%nat 10%bv eq_refl), Hv; exact Hv0).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem3 a)
  by (intros; reflexivity).
assert (KP : forall a, apresent (w_H W2) mem3 a -> apresent (w_H W2) mem3 a) by (intros; assumption).
(* 0x84330 bnez a0: not taken, the bytes agree *)
cw_branch Hc.
{ exfalso. rewrite branch_ne_U, (U_atom E 10 0 E10 ltac:(lia)), U_lit in Hc by lia. cbn in Hc. discriminate Hc. }
cw_run_to ltac:(cbn [ss_mem]; repeat first [apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]]) CC_FL.
ctk_keep cw_kwr_ro.
assert (E19 : ew E 19 = w64 (cc_sg g)) by (rewrite (EC 19%nat 19%bv eq_refl ltac:(unfold acallee_saved; lia)); exact R19).
assert (Hsgout : forall x, cc_sg g <= x < cc_sg g + 24 -> ~ (cc_sp1 g - 8192 <= x < cc_sp1 g))
  by (intros x Hx Hx'; destruct HsgS; lia).
assert (Hdtout : ~ (cc_sp1 g - 8192 <= cc_dt g < cc_sp1 g)) by (intros Hx'; destruct HdtS; lia).
clear HsgS HdtS Hd1 HFapp Hdtapp Hsgwin Hdtwin.
assert (HF8b : 0 <= cc_F g pos / 8 < 2 ^ 44)
  by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
(* 0x8434c bgeu s3,-8: the UBSan check of sg + 8, not taken *)
cw_branch Hc3.
{ exfalso. rewrite branch_geu_U in Hc3.
  lazymatch type of Hc3 with context [U ?Ev (SOff 19 0)] =>
    rewrite (U_atom Ev 19 (cc_sg g) ltac:(ewpeel; exact E19) ltac:(lia)), U_SLit in Hc3 end.
  apply negb_true_iff, Z.ltb_ge in Hc3. rewrite zcanon_id in Hc3 by (unfold M64; lia).
  destruct (Hsgapp (cc_sg g) ltac:(lia)) as ((_ & Hlt) & _). lia. }
cw_run_to ltac:(cbn [ss_mem]; repeat first [apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]]) CC_FL.
ctk_keep cw_kwr_ro.
apply SRr_ret.
lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- context [mkCfg _ ?md4] =>
  pose proof (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) as Hms;
  exists ly2, S2, (ms_regs msv), (ms_mem msv), md4;
  split; [unfold cfg_at, w64; rewrite Hms at 1; reflexivity|]
end.
split; [exact HJ3|].
split.
{ apply (cw_kept_step B LAWS TB_check_text_counter (cc_lyc g) (cc_Sc g) (cc_W g) (cc_memc g) (cc_mdc g) W2 mem2
    _ (cc_sp g) (cc_wr g) (fun a => cc_sp1 g - 8192 <= a < cc_sp1 g));
  [ unfold TB_check_text_counter, ESTACK; lia | exact HARc | exact HK
  | intros a Ha Hx; rewrite KE by (first [lia | tauto]); apply KW; [exact Ha | intros H; apply Hx; lia]
  | intros a Ha; left; unfold TB_check_text_counter, ESTACK; lia
  | intros a Hp; apply KP; apply Hpres3; exact Hp ]. }
split; [exact HP|]. split; [exact Hni|].
split; [eapply same_io_trans; [exact (same_io_trans _ _ _ Hio HIO3) | kio]|].
split; [exact Hmo|].
split.
{ apply (cc_common_keep g pos regs2 mem2 W2 _ _ W2 HC);
  [ bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf
  | rv; rewrite ?sv_denot_SOff0; ewpeel; rewrite E32, R24; reflexivity
  | bsm_rf | bsm_rf
  | intros a Ha; rewrite KE by (first [unfold SB in *; lia | tauto]); apply KW; unfold SB in *; lia ]. }
exists 0.
split; [bsm_rf|].
split; [bsm_rv0; rewrite denot_lit_U;
        lazymatch goal with |- Z_to_bv 64 (U ?Ev _) = _ =>
          rewrite (U_atom_off Ev 19 (cc_sg g) 8 ltac:(ewpeel; exact E19) ltac:(lia) ltac:(lia)) end; reflexivity|].
split; [bsm_rf|].
split; [bsm_rv0; lazymatch goal with |- sv_denot ?Ev _ = _ =>
          exact (bs_den_not Ev 19 (cc_sg g) 8 ltac:(ewpeel; exact E19) ltac:(lia) ltac:(lia)) end|].
split; [bsm_rf|].
split; [lia|]. split; [cbn; lia|].
exists s, d. split; [exact Ls|]. split.
- apply (bs_garr8_kept (w_H W2) (w_H W2) mem2 _); [|exact Grec].
  intros x Hx. rewrite length_app, repeat_length, Ls in Hx. rewrite KE by (first [lia | tauto]).
  apply KW; [lia | exact (Hsgout x ltac:(lia))].
- apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 _ _ 1 _); [|exact Vdt].
  intros x Hx. cbn in Hx. rewrite KE by (first [lia | tauto]). replace x with (cc_dt g) by lia.
  apply KW; [lia | exact Hdtout].
Qed.
End s.
