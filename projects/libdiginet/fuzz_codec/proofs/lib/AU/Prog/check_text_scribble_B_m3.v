(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, a working branch), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, with its module paths changed; 453 of its 506 lines of code are new or changed and 528 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/diginet_scribble_encode_A_lib.v, with its module paths and module names changed; 242 of its 285 lines of code are new or changed and 463 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/AU/Prog/check_text_scribble_B_m2.v, with its addresses changed; 162 of its 253 lines of code are new or changed and 194 lines of the source are left out. *)
(* Part M3 of segment M of check_text_scribble's walk in image B (check_text_scribble_B_mi.v): from the entry of the
   compare wrapper 0x42430 (bs_cut .. PC_C2) through its contract (abcmp_realizes: the record's first n bytes and
   want's, equal, so a0 = 0) to its return 0x84028, then 0x84028 bnez a0 (not taken), 0x8402c not a0,s4 and the UBSan
   check of ch + n at 0x84030 (not taken: ~ch is at least 2 ^ 64 - 2 ^ 47 and n at most 8), 0x84038 bne s3,24 (taken:
   n is at most 8), 0x84084 .. 0x84094 a1 = 0, s4 = ch + n, a2 = 24 - n, a3 = ~(ch + n), a4 = 0xa5: to the fuzz_all
   loop's head 0x84098 (bs_cut .. PC_F, j = 0). The wrapper writes only its 2 * 4096 bytes below sp1. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_base check_text_scribble_B_l.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_f check_text_scribble_B_mi.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_m2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition B_BCMP : Z := 0x42430.

(* a register of the stop as the denotation of its symbolic value, unsimplified *)
Ltac bsm_rv0 := lazymatch goal with HS : st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) |- context [getr (ms_regs ?ms) ?r] =>
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  let H := fresh "R" in
  assert (H : getr (ms_regs ms) r = sv_denot Ex e) by exact (st_ok_restrict_reg segs Hh Ex ss ms r HS);
  rewrite H; clear H end.

(* the shadow window of want[0 .. n) is the frame's own 8 shadow bytes *)
Lemma bsm_want_hull : forall (H : word -> bool) (m : word -> option byte) F n, F mod 64 = 0 -> 0 <= F -> 0 < n <= 8 ->
  garr8 tfibsegs (mrestrict H m) (SB + F / 8) BS_FRAME_SHADOW ->
  shadow_hull_vis (aview tfibsegs H m) (F + 32) n.
Proof.
intros H m F n HF HF0 Hn Hsh s Hs.
pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF, Z.add_0_r in D. set (k := F / 64) in *.
assert (Hk : 0 <= k) by (subst k; apply Z.div_pos; lia).
assert (E1 : shadow_addr (F + 32) / 8 * 8 = SB + 8 * k).
{ unfold shadow_addr. rewrite <- SB_SHADOW_OFF. rewrite D.
  replace (64 * k + 32) with ((8 * k + 4) * 8) by lia. rewrite Z.div_mul by lia.
  unfold SB. replace (2147450880 + (8 * k + 4)) with ((268431360 + k) * 8 + 4) by lia.
  rewrite <- (Z.div_unique_pos ((268431360 + k) * 8 + 4) 8 (268431360 + k) 4) by lia. lia. }
assert (E2 : shadow_addr (F + 32 + n - 1) / 8 * 8 = SB + 8 * k).
{ unfold shadow_addr. rewrite <- SB_SHADOW_OFF. rewrite D.
  rewrite <- (Z.div_unique_pos (64 * k + 32 + n - 1) 8 (8 * k + 4) (n - 1)) by lia.
  unfold SB. replace (2147450880 + (8 * k + 4)) with ((268431360 + k) * 8 + 4) by lia.
  rewrite <- (Z.div_unique_pos ((268431360 + k) * 8 + 4) 8 (268431360 + k) 4) by lia. lia. }
rewrite E1, E2 in Hs.
assert (EF : F / 8 = 8 * k) by (rewrite D; replace (64 * k) with ((8 * k) * 8) by lia; apply Z.div_mul; lia).
rewrite EF in Hsh.
destruct (Hsh (Z.to_nat (s - (SB + 8 * k))) ltac:(cbn [length BS_FRAME_SHADOW]; lia)) as (Vs & Bs).
rewrite Z2Nat.id in Vs by lia. replace (SB + 8 * k + (s - (SB + 8 * k))) with s in Vs by lia.
rewrite (aview_of_val_mem1 tfibsegs H m s _ Vs Bs). discriminate.
Qed.

(* the registers of the fuzz_all loop's head, as the engine leaves them *)
Lemma bsm_U_sub : forall E k v, ew E k = Z_to_bv 64 v -> 0 <= v <= 24 ->
  U E (SAlu ALU_SUB (SLit 0) (SOff k (-24))) = 24 - v.
Proof.
intros E k v Hk Hv. rewrite U_SAlu, U_SLit, U_SOff, Hk. rewrite unsigned_lit_small by lia.
cbn [zalu_raw]. unfold zcanon, M64. rewrite Zmod_0_l, Zminus_mod_idemp_r, Z.mod_small by lia. lia.
Qed.
Lemma bsm_U_add : forall E a b va vb, ew E a = Z_to_bv 64 va -> ew E b = Z_to_bv 64 vb ->
  0 <= va -> 0 <= vb -> va + vb < 2 ^ 64 -> U E (SAlu ALU_ADD (SOff a 0) (SOff b 0)) = va + vb.
Proof.
intros E a b va vb Ha Hb H1 H2 H3. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E a va Ha ltac:(lia)), (U_atom E b vb Hb ltac:(lia)). apply zcanon_id. unfold M64. lia.
Qed.
Lemma bsm_U_not_add : forall E a b va vb, ew E a = Z_to_bv 64 va -> ew E b = Z_to_bv 64 vb ->
  0 <= va -> 0 <= vb -> va + vb < 2 ^ 64 ->
  U E (SAlu ALU_XOR (SAlu ALU_ADD (SOff a 0) (SOff b 0)) (SLit (-1))) = 2 ^ 64 - 1 - (va + vb).
Proof.
intros E a b va vb Ha Hb H1 H2 H3. rewrite U_SAlu. cbn [zalu_raw].
rewrite (bsm_U_add E a b va vb Ha Hb H1 H2 H3), U_SLit.
change (zcanon (-1)) with (2 ^ 64 - 1). rewrite lxor_allones by lia. apply zcanon_id. unfold M64. lia.
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis ABCMP : abcmp_realizes tfibsegs B B_BCMP.

Theorem bsm3_holds : forall g pos W2 c2, bs_pre B g -> bs_now B g -> bs_cut B MT g pos PC_C2 (P_C2 g pos) W2 c2 ->
  SRr tfibsegs W2 c2 (bs_cut B MT g pos PC_F (P_F g pos 24)).
Proof.
intros g pos W2 c2 Hpre Hnow Hc.
destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HK & HP & Hni & Hio & Hmo & HC & HL).
destruct HL as (R1 & R10 & R11 & R12 & R20 & Hrec & Hwg).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as Hac.
pose proof HC as (R8 & R2 & R9 & R3 & R4 & R18 & R24 & R22 & R23 & R25 & R19 & R21 & R27 & _).
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsh).
pose proof Hpre as (HE & _ & _ & _ & Hoch & _ & (Hch0 & Hchn & Hchtd & Hchtw & _ & _ & Hcham & Hchwin) & _ & _ & _ &
  Hn & _).
pose proof HE as (_ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hlive).
pose proof (proj1 HE) as HJc. pose proof (proj1 HJc) as HARc.
destruct (bs_stack B g Hpre) as (Hceil & H47 & H46 & Hal & Hsp1 & Hsp1a & Hwin & Hsp0).
destruct (bs_frame B LAWS g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (Hfr & Efa & Efl & HF0 & HFc & HF64 & HFapp & HFp).
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & _) & _).
specialize (Hnow pos ly2 S2 W2 mem2 md2 HJ HK HP Hni) as ((Htb & Htra) & Hchra2 & Hchhull2 & _).
unfold TB_check_text_scribble, ESTACK in Hceil, Hwin, H46.
assert (Hsp1m : bs_sp1 g mod 16 = 0).
{ pose proof (Z.div_mod (bs_sp1 g) 32 ltac:(lia)) as D. rewrite Hsp1a, Z.add_0_r in D. rewrite D.
  replace (32 * (bs_sp1 g / 32)) with ((2 * (bs_sp1 g / 32)) * 16) by lia. apply Z_mod_mult. }
assert (Esp : spZ regs2 = bs_sp1 g) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
assert (HchS : bs_ch g + 24 <= bs_sp g - 8352 \/ bs_sp g <= bs_ch g)
  by (unfold coff_win, TB_check_text_scribble, ESTACK in Hchwin; lia).
pose proof (bsf_owe_len (Z.to_nat (bs_n g)) (bs_tb g)) as HOL.
assert (HwL : length (fst (bs_owe g)) = Z.to_nat (bs_n g)) by exact HOL.
unfold in_app in HFapp.
assert (HF8 : bs_F g pos mod 8 = 0).
{ pose proof (Z.div_mod (bs_F g pos) 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
  replace (64 * (bs_F g pos / 64)) with ((8 * (bs_F g pos / 64)) * 8) by lia. apply Z.mod_mul. lia. }
(* the record's first n bytes and want's agree *)
assert (Heq : forall i, 0 <= i < bs_n g ->
  aview tfibsegs (w_H W2) mem2 (bs_ch g + i) = aview tfibsegs (w_H W2) mem2 (bs_F g pos + 32 + i)).
{ intros i Hi. destruct (Hrec (Z.to_nat i)) as (V1 & B1).
  { unfold scribble_bytes. fold (bs_owe g). rewrite length_app, repeat_length, HwL. lia. }
  destruct (Hwg (Z.to_nat i) ltac:(rewrite HwL; lia)) as (V2 & B2).
  unfold scribble_bytes in V1, B1. fold (bs_owe g) in V1, B1. rewrite app_nth1 in V1, B1 by (rewrite HwL; lia).
  rewrite Z2Nat.id in V1, V2 by lia.
  rewrite (aview_of_val_mem1 tfibsegs _ _ _ _ V1 B1), (aview_of_val_mem1 tfibsegs _ _ _ _ V2 B2). reflexivity. }
eapply SRr_bind.
{ apply (cw_bcmp_at B LAWS B_BCMP ABCMP W2 regs2 mem2 (bs_STK g) (bs_sp0 g) (bs_FP g) (bs_ly g) (bs_S g) (bs_W0 g)
    (bs_mem0 g) (bs_md0 g) ((0, pos) :: bs_own g) ly2 S2 md2 (bs_k g) (bs_ch g) (bs_F g pos + 32) (bs_n g)
    (bs_sp1 g - bs_sp0 g) (w64 0x84028)).
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
    destruct (Hrec (Z.to_nat (a - bs_ch g))) as (Va & Ba).
    { unfold scribble_bytes. rewrite length_app, repeat_length. fold (bs_owe g). rewrite HwL. lia. }
    rewrite Z2Nat.id in Va by lia. replace (bs_ch g + (a - bs_ch g)) with a in Va by lia.
    rewrite (aview_of_val_mem1 tfibsegs _ _ _ _ Va Ba). discriminate.
  - intros a Ha. split; [|rewrite Esp; unfold ESTACK; lia].
    destruct (Hwg (Z.to_nat (a - (bs_F g pos + 32)))) as (Va & Ba); [rewrite HwL; lia|].
    rewrite Z2Nat.id in Va by lia. replace (bs_F g pos + 32 + (a - (bs_F g pos + 32))) with a in Va by lia.
    rewrite (aview_of_val_mem1 tfibsegs _ _ _ _ Va Ba). discriminate.
  - intros a Ha. unfold ESTACK. lia.
  - intros a Ha. unfold ESTACK. lia.
  - unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg in *. lia.
  - unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg, kLowShadowBeg, ASAN_CEIL in *. lia.
  - intros x Hx. apply Hchra2. lia.
  - intros Hn0. exact (bsm_hull_sub _ (bs_ch g) (bs_n g) 24 ltac:(lia) ltac:(lia) Hchhull2).
  - apply (bs_ra_want (w_H W2) mem2 (bs_F g pos) 32 (bs_n g)); [exact HF8 | lia | lia | lia | exact Hsh].
  - intros Hn0. apply (bsm_want_hull (w_H W2) mem2 (bs_F g pos) (bs_n g) HF64 ltac:(lia) ltac:(lia) Hsh). }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & v & -> & HJ3 & HP3 & Hv & Hcmp & Hkept & Hpres3 & Hsame).
assert (Hv0 : v = w64 0) by (apply Hcmp; exact Heq).
pose proof (same_io_materialized _ _ Hsame) as HIO3. clear Hsame.
unfold ESTACK in Hkept. replace (bs_sp0 g + (bs_sp1 g - bs_sp0 g)) with (bs_sp1 g) in Hkept by lia.
assert (CS : forall r, acallee_saved r -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) by exact HP3.
(* the state at 0x84028 *)
set (E := Ereg regs3 (cw_extra [])).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs3 r)
  by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
assert (HS : st_ok tfibsegs E (mkSS 0x84028 sr_atoms [] None (mkFacts [(32%nat, mkAF SB SB 0)] [] []))
  (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 0x84028) mem3 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite cw_ew_SB, unsigned_lit_small by (unfold SB; lia). unfold SB. split; [|exact I]. split; [lia|].
    split; [reflexivity | lia]. }
clearbody E.
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W2) mem3)) by constructor.
assert (EC : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> acallee_saved (Z.of_nat nn) -> ew E nn = getr regs2 r).
{ intros nn r Hnn Hcs. rewrite (EE nn r Hnn). pose proof (CS _ Hcs) as Hc. rewrite Hnn, !Z_to_bv_bv_unsigned in Hc.
  exact Hc. }
assert (E10 : ew E 10 = w64 0) by (rewrite (EE 10%nat 10%bv eq_refl), Hv; exact Hv0).
assert (E20 : ew E 20 = w64 (bs_ch g)) by (rewrite (EC 20%nat 20%bv eq_refl ltac:(unfold acallee_saved; lia)); exact R20).
assert (E19 : ew E 19 = w64 (bs_n g)) by (rewrite (EC 19%nat 19%bv eq_refl ltac:(unfold acallee_saved; lia)); exact R19).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem3 a)
  by (intros; reflexivity).
assert (KP : forall a, apresent (w_H W2) mem3 a -> apresent (w_H W2) mem3 a) by (intros; assumption).
(* 0x84028 bnez a0: not taken, the bytes agree *)
cw_branch Hc.
{ exfalso. rewrite branch_ne_U, (U_atom E 10 0 E10 ltac:(lia)), U_lit in Hc by lia. cbn in Hc. discriminate Hc. }
(* 0x8402c not a0,s4; 0x84030 bltu a0,s3: the UBSan check of ch + n, not taken *)
cw_run_to ltac:(cbn [ss_mem]; apply awr_ok_nil) PC_F. ctk_keep cw_kwr_ro.
cw_branch Hc2.
{ exfalso. lazymatch type of Hc2 with context [sv_denot ?Ev _] =>
    rewrite branch_ltu_U, (U_not Ev 20 (bs_ch g) ltac:(ewpeel; exact E20) ltac:(lia)),
      (U_atom Ev 19 (bs_n g) ltac:(ewpeel; exact E19) ltac:(lia)) in Hc2 end.
  apply Z.ltb_lt in Hc2. lia. }
(* 0x84034 li a0,24; 0x84038 bne s3,a0: taken, n is at most 8 *)
cw_run_to ltac:(cbn [ss_mem]; apply awr_ok_nil) PC_F. ctk_keep cw_kwr_ro.
cw_branch Hc3.
2: { exfalso. lazymatch type of Hc3 with context [sv_denot ?Ev _] =>
       rewrite branch_ne_U, (U_atom Ev 19 (bs_n g) ltac:(ewpeel; exact E19) ltac:(lia)), U_lit in Hc3 by lia end.
     apply negb_false_iff, Z.eqb_eq in Hc3. lia. }
(* 0x84084 .. 0x84094: a1 = 0, s4 = ch + n, a2 = 24 - n, a3 = ~(ch + n), a4 = 0xa5 *)
cw_run_to ltac:(cbn [ss_mem]; apply awr_ok_nil) PC_F. ctk_keep cw_kwr_ro.
assert (HF8b : bs_F g pos / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (HF8c : 0 <= bs_F g pos / 8) by (apply Z.div_pos; lia).
apply SRr_ret.
lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- context [mkCfg _ ?md4] =>
  pose proof (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) as Hms;
  exists ly2, S2, (ms_regs msv), (ms_mem msv), md4;
  split; [unfold cfg_at, w64; rewrite Hms at 1; reflexivity|]
end.
split; [exact HJ3|].
split.
{ apply (cw_kept_step B LAWS TB_check_text_scribble (bs_lyc g) (bs_Sc g) (bs_W g) (bs_memc g) (bs_mdc g) W2 mem2
    _ (bs_sp g) (bs_wr g) (fun a => bs_sp1 g - 8192 <= a < bs_sp1 g));
  [ unfold TB_check_text_scribble, ESTACK; lia | exact HARc | exact HK
  | intros a Ha Hx; rewrite KE by (first [lia | tauto]); apply Hkept; [exact Ha | intros H; apply Hx; lia]
  | intros a Ha; left; unfold TB_check_text_scribble, ESTACK; lia
  | intros a Hp; apply KP; apply Hpres3; exact Hp ]. }
split; [exact HP|].
split; [exact Hni|].
split; [eapply same_io_trans; [exact (same_io_trans _ _ _ Hio HIO3) | kio]|].
split; [exact Hmo|].
split.
{ apply (bsm_common_keep g pos regs2 mem2 W2 _ _ W2 HC);
  [ bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf
  | bsm_rf | bsm_rf | bsm_rf
  | intros a Ha; rewrite KE by (first [unfold SB in *; lia | tauto]); apply Hkept; [unfold SB in *; lia | unfold SB in *; lia] ]. }
exists 0.
split; [bsm_rf|].
split.
{ bsm_rv0. rewrite denot_lit_U. lazymatch goal with |- Z_to_bv 64 (U ?Ev _) = _ =>
    rewrite (bsm_U_add Ev 19 20 (bs_n g) (bs_ch g) ltac:(ewpeel; exact E19) ltac:(ewpeel; exact E20) ltac:(lia)
      ltac:(lia) ltac:(lia)) end. unfold w64. f_equal. lia. }
split.
{ bsm_rv0. rewrite denot_lit_U. lazymatch goal with |- Z_to_bv 64 (U ?Ev _) = _ =>
    rewrite (bsm_U_sub Ev 19 (bs_n g) ltac:(ewpeel; exact E19) ltac:(lia)) end. reflexivity. }
split.
{ bsm_rv0. rewrite denot_lit_U. lazymatch goal with |- Z_to_bv 64 (U ?Ev _) = _ =>
    rewrite (bsm_U_not_add Ev 19 20 (bs_n g) (bs_ch g) ltac:(ewpeel; exact E19) ltac:(ewpeel; exact E20) ltac:(lia)
      ltac:(lia) ltac:(lia)) end. unfold w64, bnot. f_equal. lia. }
split; [bsm_rf|].
split; [lia|]. split; [lia|].
apply (bs_garr8_kept (w_H W2) (w_H W2) mem2 _); [|exact Hrec].
intros a Ha. unfold scribble_bytes in Ha. fold (bs_owe g) in Ha. rewrite length_app, repeat_length, HwL in Ha.
rewrite KE by (first [lia | tauto]). apply Hkept; lia.
Qed.
End s.
