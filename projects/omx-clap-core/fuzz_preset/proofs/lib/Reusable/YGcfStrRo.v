(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-29 (PresetStrRo, c-libc-stdio lane): the step from c-libc-stdio's ARcf strcmp / strlen rows
   (lib/Reusable/YGcfStr.v, the memnorm twins astrcmp_realizes_cfm / astrlen_realizes_cfm) to the call-site texts with
   the NARROW read-only premise. rule 24: no function is proved here; these are implications between statements,
   plus one decision procedure.

   WHY. Our rows take `rom_view segs W mem` (the view equals the image at EVERY non-writable byte): their proof
   normalises the store for the ported kits (MemNorm.evt_normalize_cj needs ro_agree of the whole store,
   lib/MemNorm.v:861-862). The consumers state the narrower `arodata_okP segs rlo rhi B (aview ..)` (the image view at
   the NON-owned read-only bytes), because runtime-owned statics lie in each image's read-only PT_LOAD (63 ranges,
   1680 bytes, in both images; the internal file MARKED-LAW-AUDIT.md, a Theorem Labs lane). The two meet through the const cells: when every
   owned non-writable byte is a const cell holding its image byte (AF0m.v's and YF0m.v's rom_clean rows), ARcf's
   amc_const (or AR_laws_x's alx_const_cells) gives the view there, arodata_okP gives it elsewhere, and rom_view
   follows. `ro_clean_check` decides that condition for a table by computation; `rom_view_of_cells` is the
   implication. The per-image instances are lib/A/PSstrRo.v and lib/AU/PSstrRo.v.

   THE TARGET TEXTS are c-omx-alloc's family 1b, lib/Reusable/YGcallMxmn.v (origin/cold/c-omx-alloc-mxmn
   fb5888279f17, blob f08aa5a90052): `astrcmp_realizes_xrom` / `astrlen_realizes_xrom` = the consumers' texts
   (ExvB_StrcmpRo.v / ExwB_StrlenRo.v, `astrcmp_realizes_xro` / `astrlen_realizes_xro` there too) with the keep
   `MN.memnorm segs mem -> MN.memnorm segs mem'` (MN = YAkMemnorm) LAST, and `astrlen_realizes_xm` = YGcallMx.v's
   astrlen_realizes_x (WITH rom_view, for walks that hold rom_view but not arodata_okP) with the same keep LAST. The
   read-only premise is the one home `PresetRodata.arodata_okP` (lib/Spec/PresetRodata.v, blob 4eb7e95e7e93), the
   name YGcallMxmn's texts use; no copy here. The plain _xro rows follow from the _xrom ones by YGcallMxmn's
   `_forget`, and the ARcf /\ xs_placed_cf rows by its `_conj` lifts. The _xm rows need no read-only bridge
   (section 3). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0dcf YG0d2cf YGcfStr YGcfHeadSh YGcfStrX.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRodata.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------- *)
(* 1. rom_view from arodata_okP and the const cells.                              *)
Section core.
Variable segs : list Segment.
Variable cells : list acell.
Variable owned : list (Z * Z).
Variable errno : Z.

(* cell c is an absolute const cell that covers byte a and holds the image byte rb there *)
Definition cell_cov (a rb : Z) (c : acell) : bool :=
  match c_at c, c_val c with
  | ANum z, AV (ANum v) =>
      if (z <=? a) && (a <? z + Z.of_nat (c_w c)) then le_byte v (c_w c) (Z.to_nat (a - z)) =? rb else false
  | _, _ => false
  end.

Definition byte_ok (a : Z) : bool :=
  match seg_rom segs (Z_to_bv 64 a) with
  | Some b => existsb (cell_cov a (bv_unsigned b)) cells
  | None => false
  end.

Fixpoint range_ok (a : Z) (n : nat) : bool :=
  match n with O => true | S n' => byte_ok a && range_ok (a + 1) n' end.

(* a non-writable segment: every owned byte in it is pinned, and errno is not in it. `if`, not `||`: vm_compute
   evaluates both arguments of orb, and the writable segments hold multi-megabyte owned ranges *)
Definition seg_ok (s : Segment) : bool :=
  if seg_writable s then true else
  (forallb (fun r =>
     range_ok (Z.max (fst r) (Z.of_N (seg_base s)))
       (Z.to_nat (Z.min (fst r + snd r) (Z.of_N (seg_base s) + Z.of_N (seg_size s)) - Z.max (fst r) (Z.of_N (seg_base s)))))
     owned
   && ((Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? errno) || (errno + 4 <=? Z.of_N (seg_base s)))).

Definition ro_clean_check : bool := forallb seg_ok segs.

Lemma range_ok_spec : forall n a, range_ok a n = true -> forall x, a <= x < a + Z.of_nat n -> byte_ok x = true.
Proof.
  induction n as [|n IH]; intros a H x Hx; [lia|].
  cbn [range_ok] in H. apply andb_true_iff in H as [H1 H2].
  destruct (Z.eq_dec x a) as [->|Hne]; [exact H1|].
  apply (IH (a + 1) H2). lia.
Qed.

Lemma rom_view_of_cells : ro_clean_check = true ->
  forall (B : asyms) ly (W : world segs) mem rlo rhi,
  as_owned_static B = owned -> as_errno B = errno ->
  Forall (cell_holds B ly (aview segs (w_H W) mem)) cells ->
  PresetRodata.arodata_okP segs rlo rhi B (aview segs (w_H W) mem) ->
  rom_view segs W mem.
Proof.
  intros CHK B ly W mem rlo rhi Eown Eerr HC HRO a Ha.
  pose proof Ha as (sg & Hin & Hw & Hlo & Hhi).
  unfold ro_clean_check in CHK. rewrite forallb_forall in CHK. specialize (CHK sg Hin).
  unfold seg_ok in CHK. rewrite Hw in CHK. cbv beta iota in CHK.
  apply andb_true_iff in CHK as [CO CE]. rewrite forallb_forall in CO.
  assert (Hdec : forall r, {in_zr a r} + {~ in_zr a r}).
  { intros r. unfold in_zr. destruct (Z_le_dec (fst r) a); destruct (Z_lt_dec a (fst r + snd r));
    [left; lia | right; lia | right; lia | right; lia]. }
  destruct (Exists_dec (in_zr a) (as_owned_static B) Hdec) as [Hown|Hno].
  - rewrite Eown in Hown. apply Exists_exists in Hown as (r & Hr & Har).
    pose proof (range_ok_spec _ _ (CO r Hr) a) as Hb.
    assert (Hb' : byte_ok a = true) by (apply Hb; unfold in_zr in Har; lia).
    unfold byte_ok in Hb'. destruct (seg_rom segs (Z_to_bv 64 a)) as [b|] eqn:Er; [|discriminate Hb'].
    apply existsb_exists in Hb' as (c & Hc & Hcov).
    rewrite Forall_forall in HC. pose proof (HC c Hc) as Hh.
    unfold cell_cov in Hcov. destruct c as [ca cw cv]. cbn [c_at c_val c_w] in Hcov.
    destruct ca; try discriminate Hcov. destruct cv as [e|]; try discriminate Hcov. destruct e; try discriminate Hcov.
    destruct ((z <=? a) && (a <? z + Z.of_nat cw)) eqn:Hrange; [|discriminate Hcov].
    apply andb_true_iff in Hrange as [R1 R2]. apply Z.leb_le in R1. apply Z.ltb_lt in R2.
    apply Z.eqb_eq in Hcov.
    unfold cell_holds in Hh. cbn [c_at c_val c_w aeval] in Hh.
    specialize (Hh (Z.to_nat (a - z)) ltac:(lia)).
    rewrite Z2Nat.id in Hh by lia. replace (z + (a - z)) with a in Hh by lia.
    rewrite Hh. cbn [option_map]. rewrite Hcov. reflexivity.
  - apply HRO; [left; exact Ha | exact Hno |].
    rewrite Eerr. apply orb_true_iff in CE as [E|E]; apply Z.leb_le in E; lia.
Qed.
End core.

(* ---------------------------------------------------------------------------- *)
(* 2. Our ARcf memnorm twins to the target texts, at ARcf and ARcf /\ xs_placed_cf; the plain _xro texts by _forget *)
Section cf. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable segs : list Segment.
Variable B : asyms.
Variables rlo rhi : Z.
Local Abbreviation ARc := (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md).
Local Abbreviation ARcx := (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ xs_placed_cf ly S).
(* the per-image fact (lib/A/PSstrRo.v, lib/AU/PSstrRo.v: rom_view_of_cells at the image's table) *)
Hypothesis RV : forall ly S Hp W mem md, ARcf segs B ly S Hp W mem md ->
  PresetRodata.arodata_okP segs rlo rhi B (aview segs (w_H W) mem) -> rom_view segs W mem.

(* astrlen: by conversion (ecall_pre_x at ARcf IS ecall_pre_cf, src_ok_cf IS src_ok; YGcfStrX.v), rom_view by RV *)
Theorem astrlen_cfm_xrom : forall pc, astrlen_realizes_cfm segs B pc -> astrlen_realizes_xrom segs B ARc rlo rhi pc.
Proof.
  intros pc H ly S Hp W regs mem md x k Hpre H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 Hro.
  exact (H ly S Hp W regs mem md x k Hpre H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14
    (RV ly S Hp W mem md (proj1 Hpre) Hro)).
Qed.

(* astrcmp: YGcfStrX.astrcmp_realizes_cf_x's proof (the stop index by first_stop, the per-string premises cut to
   it), rom_view by RV, the keep carried as the last conjunct *)
Theorem astrcmp_cfm_xrom : forall pc, astrcmp_realizes_cfm segs B pc -> astrcmp_realizes_xrom segs B ARc rlo rhi pc.
Proof.
intros pc AC ly S Hp W regs mem md x y kx ky Hpre Hstk Hwin Ha0 Ha1 Hx Hy Hkx0 Hkx1 Hxk Hky0 Hky1 Hyk Hfbx Hfby
  Hsrcx Hsrcy Hwx Hwy Hamrx Hamry Hrax Hshvx Hray Hshvy _ _ Hro.
pose proof (RV ly S Hp W mem md (proj1 Hpre) Hro) as Hrom.
destruct Hfbx as (_ & Hnzx & Hzx). specialize (Hzx ltac:(lia)).
destruct Hfby as (_ & Hnzy & Hzy). specialize (Hzy ltac:(lia)).
destruct (first_stop (aview segs (w_H W) mem) x y kx ky Hkx0 Hky0 Hnzx Hzx Hnzy Hzy)
  as (k & Hkx & Hky & Heq & bx & by_ & Hbx & Hby & Hstop).
assert (Hpre' : ecall_pre_cf segs B ly S Hp W regs mem md) by exact Hpre.
assert (Hmeet : str_meet segs W mem x y k bx by_).
{ unfold str_meet. split; [lia|]. exact (conj Heq (conj Hbx (conj Hby Hstop))). }
eapply SRr_mono; [exact (AC ly S Hp W regs mem md x y k bx by_ Hpre' Hstk Hwin Ha0 Ha1 Hx Hy
  ltac:(lia) ltac:(lia) ltac:(lia) Hmeet
  (src_ok_cut segs W regs mem x (kx + 1) (k + 1) ltac:(lia) Hsrcx)
  (src_ok_cut segs W regs mem y (ky + 1) (k + 1) ltac:(lia) Hsrcy)
  (fun a Ha => Hwx a ltac:(lia)) (fun a Ha => Hwy a ltac:(lia))
  (amem_range8_cut x (kx + 1) (k + 1) ltac:(lia) Hamrx)
  (amem_range8_cut y (ky + 1) (k + 1) ltac:(lia) Hamry)
  (range_addressable_sub _ SHADOW_OFF x (kx + 1) x (k + 1) Hrax ltac:(lia) ltac:(lia))
  (shadow_hull_vis_sub_cf _ x (kx + 1) x (k + 1) Hshvx ltac:(lia) ltac:(lia))
  (range_addressable_sub _ SHADOW_OFF y (ky + 1) y (k + 1) Hray ltac:(lia) ltac:(lia))
  (shadow_hull_vis_sub_cf _ y (ky + 1) y (k + 1) Hshvy ltac:(lia) ltac:(lia))
  Hrom)|].
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & Hc & HAR & Hpres & Hsbm & Hv & Hfr & Hap & Hmn).
split; [reflexivity|]. exists regs', mem', md', (Z_to_bv 64 (strcmp_res bx by_)).
refine (conj Hc (conj HAR (conj Hpres (conj Hsbm (conj Hv (conj _ (conj Hfr (conj Hap Hmn)))))))).
refine (iff_trans (strcmp_res_zero bx by_) _). split.
- intros <-. destruct Hstop as [Hne|H0]; [congruence|]. subst bx.
  assert (Ekx : k = kx).
  { destruct (Z.eq_dec k kx) as [E|E]; [exact E|]. destruct (Hnzx k ltac:(lia)) as (b & Hb & Hb0).
    rewrite Hbx in Hb. injection Hb as <-. congruence. }
  assert (Eky : k = ky).
  { destruct (Z.eq_dec k ky) as [E|E]; [exact E|]. destruct (Hnzy k ltac:(lia)) as (b & Hb & Hb0).
    rewrite Hby in Hb. injection Hb as <-. congruence. }
  split; [lia|]. intros i Hi. destruct (Heq i ltac:(lia)) as (b & Hb1 & Hb2 & _). rewrite Hb1, Hb2. reflexivity.
- intros (Ek & Hall).
  assert (Ekx : k = kx).
  { destruct (Z.eq_dec k kx) as [E|E]; [exact E|]. exfalso.
    pose proof (Hall k ltac:(lia)) as Hxy. rewrite Hbx, Hby in Hxy. injection Hxy as Hxy.
    destruct (Hnzx k ltac:(lia)) as (b & Hb & Hb0). rewrite Hbx in Hb. injection Hb as <-.
    destruct Hstop as [Hne|H0]; [exact (Hne Hxy) | exact (Hb0 H0)]. }
  subst k. rewrite Hzx in Hbx. injection Hbx as <-. rewrite Ek, Hzy in Hby. injection Hby as <-. reflexivity.
Qed.

Theorem astrlen_cfm_xrom_xs : forall pc, astrlen_realizes_cfm segs B pc -> astrlen_realizes_xrom segs B ARcx rlo rhi pc.
Proof.
  intros pc H. exact (astrlen_realizes_xrom_conj segs B ARc rlo rhi (fun ly S => xs_placed_cf ly S) pc
    (astrlen_cfm_xrom pc H)).
Qed.

Theorem astrcmp_cfm_xrom_xs : forall pc, astrcmp_realizes_cfm segs B pc -> astrcmp_realizes_xrom segs B ARcx rlo rhi pc.
Proof.
  intros pc H. exact (astrcmp_realizes_xrom_conj segs B ARc rlo rhi (fun ly S => xs_placed_cf ly S) pc
    (astrcmp_cfm_xrom pc H)).
Qed.

(* the plain consumers' texts, by YGcallMxmn's _forget *)
Theorem astrlen_cfm_xro : forall pc, astrlen_realizes_cfm segs B pc -> astrlen_realizes_xro segs B ARc rlo rhi pc.
Proof. intros pc H. exact (astrlen_realizes_xrom_forget segs B ARc rlo rhi pc (astrlen_cfm_xrom pc H)). Qed.
Theorem astrcmp_cfm_xro : forall pc, astrcmp_realizes_cfm segs B pc -> astrcmp_realizes_xro segs B ARc rlo rhi pc.
Proof. intros pc H. exact (astrcmp_realizes_xrom_forget segs B ARc rlo rhi pc (astrcmp_cfm_xrom pc H)). Qed.
Theorem astrlen_cfm_xro_xs : forall pc, astrlen_realizes_cfm segs B pc -> astrlen_realizes_xro segs B ARcx rlo rhi pc.
Proof. intros pc H. exact (astrlen_realizes_xrom_forget segs B ARcx rlo rhi pc (astrlen_cfm_xrom_xs pc H)). Qed.
Theorem astrcmp_cfm_xro_xs : forall pc, astrcmp_realizes_cfm segs B pc -> astrcmp_realizes_xro segs B ARcx rlo rhi pc.
Proof. intros pc H. exact (astrcmp_realizes_xrom_forget segs B ARcx rlo rhi pc (astrcmp_cfm_xrom_xs pc H)). Qed.
End cf.

(* ---------------------------------------------------------------------------- *)
(* 3. The rom_view form: the strlen memnorm twin to YGcallMxmn's astrlen_realizes_xm needs no read-only bridge (the *)
(*    text keeps rom_view): conversion, as YGcfStrX.astrlen_realizes_cf_x, and YGcallMxmn's conj lift.          *)
Section cfxm. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable segs : list Segment.
Variable B : asyms.
Local Abbreviation ARc := (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md).
Local Abbreviation ARcx := (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ xs_placed_cf ly S).

Theorem astrlen_cfm_xm : forall pc, astrlen_realizes_cfm segs B pc -> astrlen_realizes_xm segs B ARc pc.
Proof. intros pc H. exact H. Qed.

Theorem astrlen_cfm_xm_xs : forall pc, astrlen_realizes_cfm segs B pc -> astrlen_realizes_xm segs B ARcx pc.
Proof.
  intros pc H. exact (astrlen_realizes_xm_conj segs B ARc (fun ly S => xs_placed_cf ly S) pc (astrlen_cfm_xm pc H)).
Qed.
End cfxm.
