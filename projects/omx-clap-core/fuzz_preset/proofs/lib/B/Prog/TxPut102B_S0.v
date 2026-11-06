(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 620 of its 675 lines of code are new or changed and 1869 lines of the source are left out. *)
(* fuzz_preset lib/B, the #102 re-walk of tx_put on image B' (asan-ubsan pin d663f82d7f488d30): segment S0 of
   lib/B/Prog/TxPut102B_Base.v (tp_seg_S0): from tx_put's entry (B' 0x851d0) to the three cuts it reaches - END
   (+400, the FAILED AT ENTRY arm A0), FIT (+256, the buffer fits) and GROW (+180, it does not).
   rule 24: proves function tx_put (reuse search: the internal file REWALK-102-PLAN.md section T3)
   tp_seg_S0_ok : forall P, srr_inv_laws segs P -> tp_seg_S0 B SK CTX0 P. The walk: s0_entry (the symbolic entry
   state), the paj runs to the three cuts, every inline check of S0 discharged - the UBSan alignment trap of t
   (+60 `andi a0, a0, 7`, +64 `bnez -> +488 unimp`, not taken: prhtx_place's t mod 8 = 0, atom 10's af_al2 3), the
   ASan 4-byte load check of t + 24 (+88 .. +104, slow path +492, report +508 refuted) and the 8-byte load checks of
   t + 8 / t + 16 (reports +544 / +552 refuted), all three from prhtx_place's range_addressable SHADOW_OFF t 28 - and
   at each cut s0_cut
   (TxPutCarry102.txc_carry: the carry across a frame-plus-record-only write).
   Image facts: tp_img (Base) and HHI : pa_hi <= 2 ^ 40 (PAImg_prog.v's PI_prog_B: 0x601000, by vm_compute). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00cf YG01cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0lawscf YGcallx YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YSRrMemnorm YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger TxModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PLB102.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import TxPutCall102.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require TxPutCarry102.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import TxPut102B_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YGcfRhLift.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- S0's symbolic entry state ----
   atoms: 2 = entry sp, 10 = t, 11 = s, 12 = n, 32 = the shadow offset, 33 = b0, 34 = len0, 35 = cap0, 36 = f0.
   Regions: the 112-byte frame, the shadow-offset GOT word and cell (read-only), the record's 28 accessed bytes at t
   (b, n, cap 8 bytes each, failed 4). *)
Definition s0_Bx : sv := SOff 32 0.
Definition s0_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition s0_rec : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 28 0 28
    [YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0));
     YP09.mkChunk 16 (CVal 8 (SOff 35 0)); YP09.mkChunk 24 (CVal 4 (SOff 36 0))].
Definition s0_regions : smem := [stack_region TP_FRAME; got_regionP; bcell_regionP 32; s0_rec].
Definition s0_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF (2 ^ 46) (2 ^ 47 - 32) 3);
           (12%nat, mkAF 0 (2 ^ 28) 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 0 (2 ^ 47 - 2 ^ 23) 0); (34%nat, mkAF 0 (2 ^ 28) 0);
           (35%nat, mkAF 0 (2 ^ 47 - 2 ^ 23) 0); (36%nat, mkAF 0 1 0)] [] [].
Definition ss_s0 : sstate := mkSS TP_OFF sr_atoms s0_regions None s0_facts.
Definition s0_X (b0 len0 cap0 f0 : Z) : list Z := [SHADOW_OFF; b0; len0; cap0; f0].

Section s0. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {PA : PAImg B_prog_listing}.
#[local] Existing Instance TP_PrhImg.
#[local] Existing Instance TP_PAListing.
#[local] Existing Instance TP_RL.
#[local] Notation segs := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
Definition s0_E (regs : bvmap 5 word) (xs : list Z) : env :=
  @Eimg _ B_prog_listing PA (Ereg regs (map (Z_to_bv 64) xs)).
Variable B : asyms.
Variable SK : YI16.sink_head.
Variable CTX0 : list (list Z).
#[local] Notation ARX := (ARcfx B).
(* the image fact of the instance beyond tp_img: the image lies below 2^40, so it is disjoint from the stack (>= 2^46)
   and the record (PAImg_prog.v's PI_prog_B: pa_hi = 0x601000, by vm_compute at the instance) *)
Hypothesis HHI : @pa_hi _ B_prog_listing PA <= 2 ^ 40.

Lemma s0_E_extra : forall regs b0 len0 cap0 f0,
  ew (s0_E regs (s0_X b0 len0 cap0 f0)) 32 = Z_to_bv 64 SHADOW_OFF /\
  ew (s0_E regs (s0_X b0 len0 cap0 f0)) 33 = Z_to_bv 64 b0 /\
  ew (s0_E regs (s0_X b0 len0 cap0 f0)) 34 = Z_to_bv 64 len0 /\
  ew (s0_E regs (s0_X b0 len0 cap0 f0)) 35 = Z_to_bv 64 cap0 /\
  ew (s0_E regs (s0_X b0 len0 cap0 f0)) 36 = Z_to_bv 64 f0.
Proof.
intros. unfold s0_E, s0_X. rewrite !Eimg_low by (unfold A_TEXT; lia). repeat split.
Qed.

Lemma s0_entry : forall STK ly S Hp (W : world segs) regs mem md ch dw t n b0 len0 cap0 f0,
  PALibCore (L := B_prog_listing) (PI := PA) B ->
  afn_pre_x segs B ARX STK ly S Hp W regs mem md ch -> TP_FRAME <= STK ->
  getr regs 10 = w64 t -> getr regs 12 = w64 n -> 0 <= n <= 2 ^ 28 ->
  fwin ly W regs mem dw ->
  spZ regs + 16 <= t -> t + 28 <= spZ regs + dw -> t mod 8 = 0 ->
  (forall a, t <= a < t + 28 -> writable_at segs (mrestrict (w_H W) mem) a) ->
  prhtx_rec W mem t b0 len0 cap0 f0 ->
  0 <= len0 <= 2 ^ 28 -> 0 <= b0 <= 2 ^ 47 - 2 ^ 23 -> 0 <= cap0 <= 2 ^ 47 - 2 ^ 23 ->
  st_ok_pi segs VAL (s0_E regs (s0_X b0 len0 cap0 f0)) ss_s0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + TP_OFF)) mem (seg_rom segs)))
  /\ sh_ok segs s0_Bx [] (s0_E regs (s0_X b0 len0 cap0 f0)) (mrestrict (w_H W) mem).
Proof.
intros STK ly S Hp W regs mem md ch dw t n b0 len0 cap0 f0 HPAL HPRE H112 H10 H12 Hn HFW Ht1 Ht2 Hta Hwrit HREC
  Hlen Hb0 Hcap0.
unfold TP_FRAME in H112.
pose proof HPRE as ([HAR HXS] & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HFW as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HREC as (Rb & Rl & Rc & Rf & Mb & Ml & Mc & Mf).
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Htop47 : spZ regs + dw <= 2 ^ 47) by lia.
rewrite restrict_mkst_fx.
set (E := s0_E regs (s0_X b0 len0 cap0 f0)) in *.
destruct (s0_E_extra regs b0 len0 cap0 f0) as (E32 & E33 & E34 & E35 & E36).
fold E in E32, E33, E34, E35, E36.
assert (Usp : bv_unsigned (ew E 2) = spZ regs).
{ subst E. unfold s0_E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl).
  reflexivity. }
assert (Ut : bv_unsigned (ew E 10) = t).
{ subst E. unfold s0_E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10.
  apply unsigned_lit_small; lia. }
assert (Un : bv_unsigned (ew E 12) = n).
{ subst E. unfold s0_E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl), H12.
  apply unsigned_lit_small; lia. }
assert (Uimg : forall j, (A_TEXT <= j < A_LIM)%nat -> bv_unsigned (ew E j) = VAL j).
{ intros j Hj. subst E. unfold s0_E. rewrite Eimg_img by exact Hj. apply unsigned_lit_small. apply pa_val_range. }
assert (Dv : forall (x : nat) v, ew E x = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff x 0) = Z_to_bv 64 v).
{ intros x v Hx Hv. cbn [sv_denot]. rewrite Hx, Z.add_0_r, unsigned_lit_small by exact Hv. reflexivity. }
assert (Di : forall j, (A_TEXT <= j < A_LIM)%nat -> sv_denot E (SOff j 0) = Z_to_bv 64 (VAL j)).
{ intros j Hj. cbn [sv_denot]. rewrite Uimg by exact Hj. rewrite Z.add_0_r. reflexivity. }
assert (BV : forall j, (A_TEXT <= j < A_LIM)%nat -> base_val E (Some j) = VAL j)
  by (intros j Hj; cbn [base_val]; apply Uimg; exact Hj).
assert (Hobj : forall j, (j < 39)%nat -> pa_lo <= VAL (A_OBJ j) /\ VAL (A_OBJ j) + 8 <= pa_hi)
  by (intros j Hj; exact (pa_obj_img j Hj)).
destruct (alc_const _ _ (AR_laws_ok_cf segs B) ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (palc_got_shadow B HPAL), (palc_cell B HPAL) in Kgot. rewrite (palc_cell B HPAL) in Kcell.
pose proof (palc_got_cell B HPAL) as HgcD.
split.
- unfold ss_s0. apply pa_entry_st_ok_full.
  + subst E. unfold s0_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold s0_regions, stack_region, got_regionP, bcell_regionP, s0_rec, TP_FRAME.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
    rewrite ?BV by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros q Hq. apply (apresent_writable segs). apply Hpres. lia.
    * pose proof (pa_val_range (A_OBJ 0)). pose proof (pa_val_range (A_OBJ 12)).
      pose proof (Hobj 0%nat ltac:(lia)). pose proof (Hobj 12%nat ltac:(lia)).
      split; [lia|]. split; [lia|]. split; [intros q Hq; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ _ 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [apply Di; unfold A_OBJ, A_TEXT, A_LIM; lia | lia | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kgot).
    * pose proof (pa_val_range (A_OBJ 12)). pose proof (Hobj 12%nat ltac:(lia)).
      split; [lia|]. split; [lia|]. split; [intros q Hq; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ _ 0 8 (SOff 32 0) SHADOW_OFF);
      [apply Dv; [exact E32 | unfold SHADOW_OFF; lia] | unfold SHADOW_OFF; lia | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kcell).
    * cbn [base_val]. rewrite Ut.
      split; [lia|]. split; [lia|].
      split; [intros q Hq; exact (Hwrit (t + q) ltac:(lia))|].
      constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
      { apply (chunk_ok_val segs E _ t 0 8 (SOff 33 0) b0); [apply Dv; [exact E33 | lia] | lia | lia |].
        rewrite Z.add_0_r. exact Mb. }
      { apply (chunk_ok_val segs E _ t 8 8 (SOff 34 0) len0); [apply Dv; [exact E34 | lia] | lia | lia | exact Ml]. }
      { apply (chunk_ok_val segs E _ t 16 8 (SOff 35 0) cap0); [apply Dv; [exact E35 | lia] | lia | lia | exact Mc]. }
      { apply (chunk_ok_val segs E _ t 24 4 (SOff 36 0) f0); [apply Dv; [exact E36 | lia] | lia | lia | exact Mf]. }
  + unfold s0_regions, stack_region, got_regionP, bcell_regionP, s0_rec, TP_FRAME.
    cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp, Ut.
    rewrite !(Uimg (A_OBJ 0)) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    rewrite !(Uimg (A_OBJ 12)) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    pose proof (Hobj 0%nat ltac:(lia)) as I0. pose proof (Hobj 12%nat ltac:(lia)) as I12.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  + split; [|split; [exact I | exact I]].
    unfold s0_facts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, Ut, Un, E32, E33, E34, E35, E36.
    rewrite !unsigned_lit_small by (unfold SHADOW_OFF, YM05.alloc_ceiling in *; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Ht32 : t <= 2 ^ 47 - 32) by (pose proof (Z.div_mod t 8 ltac:(lia)) as Hdm; rewrite Hta in Hdm; lia).
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
- unfold sh_ok. apply Forall_nil.
Qed.

(* ---- small engine facts (the earlier tx_put walk's template, blob 185d37e0973 :131-133, :269-287) ---- *)
Lemma s0_U_ewset : forall E m w k c, (k < m)%nat -> U (ewset E m w) (SOff k c) = U E (SOff k c).
Proof. intros E m w k c Hk. rewrite !U_SOff, ew_ewset_other by lia. reflexivity. Qed.
Lemma s0_aview_of_frame : forall (Wx : world segs) (E' : env) rs (m m' : word -> option byte) a,
  frame_of E' rs (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') ->
  ~ in_wrange E' rs a -> 0 <= a < 2 ^ 64 ->
  aview segs (w_H Wx) m' a = aview segs (w_H Wx) m a.
Proof.
intros Wx E' rs m m' a HF Hn Ha. unfold aview. f_equal. unfold mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. exact Hn.
Qed.
Lemma s0_shadow_lo : forall x, 0 <= x <= 2 ^ 47 -> 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 45.
Proof.
intros x Hx. unfold shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
assert (x / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia.
Qed.
Lemma s0_rd_of : forall (Wx : world segs) m, rd_of segs (mrestrict (w_H Wx) m) = aview segs (w_H Wx) m.
Proof. intros Wx m. reflexivity. Qed.
(* S0's runs write only its own frame (window [sp - 112, sp)) and the record (window [t, t + 28)) *)
Ltac s0_keepw K HFr :=
lazymatch type of HFr with
| frame_of ?Ex ?rsx ?mA ?mB =>
  assert (K : forall x : word,
     ~ (bv_unsigned (ew Ex 2) - 112 <= bv_unsigned x < bv_unsigned (ew Ex 2)) ->
     ~ (bv_unsigned (ew Ex 10) <= bv_unsigned x < bv_unsigned (ew Ex 10) + 28) -> mB x = mA x)
  by (intros x Hn1 Hn2; apply HFr;
      intros (r & Hin & Hr); vm_compute in Hin;
      repeat (destruct Hin as [Hin | Hin]); try contradiction;
      rewrite <- Hin in Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia)
end.
Ltac s0_keep K HFr Wx :=
lazymatch type of HFr with
| frame_of ?Ex ?rsx (mrestrict _ ?mA) (mrestrict _ ?mB) =>
  assert (K : forall a, 0 <= a < 2 ^ 64 ->
     ~ (bv_unsigned (ew Ex 2) - 112 <= a < bv_unsigned (ew Ex 2)) ->
     ~ (bv_unsigned (ew Ex 10) <= a < bv_unsigned (ew Ex 10) + 28) ->
     aview segs (w_H Wx) mB a = aview segs (w_H Wx) mA a)
  by (intros a Ha Hn1 Hn2; apply (s0_aview_of_frame Wx Ex rsx mA mB a HFr); [|exact Ha];
      intros (r & Hin & Hr); vm_compute in Hin;
      repeat (destruct Hin as [Hin | Hin]); try contradiction;
      rewrite <- Hin in Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia)
end.

Let LAWS : AR_laws_x segs B ARX cf_head := AR_laws_x_xs segs B (AR_laws_ok_cf segs B).

(* the write permission of S0's regions: its own frame and the record in the caller window (both inside
   [sp0 - (STK + dw), sp0 + dw), the window journal's own range), the GOT word and the shadow cell read-only
   (the earlier tx_put walk's template, blob 185d37e0973, its tp_awr) *)
(* the entry atoms sp (2) and t (10) keep their values in every later env of the walk (fresh atoms are >= 512) *)
Ltac s0_envl := repeat rewrite ew_ewset_other by lia;
  repeat match goal with H : bv_unsigned (ew _ ?k) = _ |- context [bv_unsigned (ew _ ?k)] => rewrite H end; lia.
Ltac s0_awr :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
| lazymatch goal with |- awr_ok ?Ex (YP09.mkRegion (Some ?m) _ _ _ _ _ :: _) _ ?sp0' _ _ _ _ _ =>
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ m (bv_unsigned (ew Ex m) - sp0')) end;
  [reflexivity | s0_envl | cbn [YP09.r_wlo]; s0_envl | cbn [YP09.r_whi]; s0_envl |] ].

(* the region list every S0 state reaches after the prologue: the frame now holds the thirteen saved words (ra at
   -8, s0 at -16, s1 at -24, s2 .. s11 at -32 .. -104), the rest as at entry *)
Definition s0_frame_saved : YP09.region :=
  YP09.mkRegion (Some 2%nat) (- TP_FRAME) 0 (- TP_FRAME) 0
    [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
     YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
     YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
     YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
     YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
     YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Definition s0_mem_saved : smem := [s0_frame_saved; got_regionP; bcell_regionP 32; s0_rec].

Lemma s0_chunk_val : forall E (m : word -> option byte) rs i r off n e v,
  mem_ok segs E m rs -> nth_error rs i = Some r -> In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem segs m (base_val E (YP09.r_base r) + off) (N.to_nat n) v.
Proof.
intros E m rs i r off n e v (Hwf & Hrs & Hpd) Hi Hc He Hv Hn.
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as (_ & _ & _ & Hcs).
exact (val_of_chunk_ok segs E m _ off n e v (proj1 (Forall_forall _ _) Hcs _ Hc) He Hv Hn).
Qed.

(* what a state over s0_mem_saved says of the memory: the saved words, the record's entry values, its writable bytes *)
Lemma s0_mem_facts : forall D (E : env) (m : word -> option byte),
  mem_ok segs E (mrestrict (w_H (tp_W D)) m) s0_mem_saved ->
  bv_unsigned (ew E 2) = tp_sp0 D -> bv_unsigned (ew E 10) = tp_t D ->
  (forall k (r : bv 5), (k = 1 \/ k = 8 \/ k = 9 \/ (18 <= k <= 27))%nat -> Z.of_nat k = bv_unsigned r ->
     ew E k = getr (tp_regs D) r) ->
  ew E 33 = Z_to_bv 64 (tp_b0 D) -> ew E 34 = Z_to_bv 64 (tp_len0 D) -> ew E 35 = Z_to_bv 64 (tp_cap0 D) ->
  ew E 36 = Z_to_bv 64 (tp_f0 D) ->
  0 <= tp_b0 D < 2 ^ 64 -> 0 <= tp_len0 D < 2 ^ 64 -> 0 <= tp_cap0 D < 2 ^ 64 -> (tp_f0 D = 0 \/ tp_f0 D = 1) ->
  tp_saved D (tp_W D) m /\
  prhtx_rec (tp_W D) m (tp_t D) (tp_b0 D) (tp_len0 D) (tp_cap0 D) (tp_f0 D) /\
  (forall a, tp_t D <= a < tp_t D + 28 -> writable_at segs (mrestrict (w_H (tp_W D)) m) a).
Proof.
intros D E m HMO Hsp Ht HR E33 E34 E35 E36 Rb Rl Rc Rf.
assert (Dr : forall k (r : bv 5), (k = 1 \/ k = 8 \/ k = 9 \/ (18 <= k <= 27))%nat -> Z.of_nat k = bv_unsigned r ->
  sv_denot E (SOff k 0) = Z_to_bv 64 (bv_unsigned (getr (tp_regs D) r))).
{ intros k r Hk Hr. cbn [sv_denot]. rewrite Z.add_0_r, (HR k r Hk Hr), !Z_to_bv_bv_unsigned. reflexivity. }
assert (Dv : forall (x : nat) v, ew E x = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff x 0) = Z_to_bv 64 v).
{ intros x v Hx Hv. cbn [sv_denot]. rewrite Hx, Z.add_0_r, unsigned_lit_small by exact Hv. reflexivity. }
assert (Hbv : forall w : word, 0 <= bv_unsigned w < 2 ^ (8 * Z.of_N 8)).
{ intros w. pose proof (bv_unsigned_in_range _ w) as Hw. unfold bv_modulus in Hw. exact Hw. }
assert (SV : forall off k (r : bv 5), (k = 1 \/ k = 8 \/ k = 9 \/ (18 <= k <= 27))%nat -> Z.of_nat k = bv_unsigned r ->
  In (YP09.mkChunk off (CVal 8 (SOff k 0))) (YP09.r_chunks s0_frame_saved) ->
  val_mem segs (mrestrict (w_H (tp_W D)) m) (tp_sp0 D + off) 8 (bv_unsigned (getr (tp_regs D) r))).
{ intros off k r Hk Hr Hin.
  pose proof (s0_chunk_val E _ s0_mem_saved 0 s0_frame_saved off 8 (SOff k 0) (bv_unsigned (getr (tp_regs D) r))
    HMO eq_refl Hin (Dr k r Hk Hr) (Hbv _) ltac:(lia)) as H.
  cbn [base_val YP09.r_base s0_frame_saved] in H. rewrite Hsp in H. exact H. }
split.
{ unfold tp_saved, raZ.
  repeat split;
  [ replace (tp_sp0 D - 8) with (tp_sp0 D + -8) by lia; apply (SV _ 1%nat 1%bv); [lia|reflexivity|cbn; tauto]
  | replace (tp_sp0 D - 16) with (tp_sp0 D + -16) by lia; apply (SV _ 8%nat 8%bv); [lia|reflexivity|cbn; tauto]
  | replace (tp_sp0 D - 24) with (tp_sp0 D + -24) by lia; apply (SV _ 9%nat 9%bv); [lia|reflexivity|cbn; tauto]
  | replace (tp_sp0 D - 32) with (tp_sp0 D + -32) by lia; apply (SV _ 18%nat 18%bv); [lia|reflexivity|cbn; tauto]
  | replace (tp_sp0 D - 40) with (tp_sp0 D + -40) by lia; apply (SV _ 19%nat 19%bv); [lia|reflexivity|cbn; tauto]
  | replace (tp_sp0 D - 48) with (tp_sp0 D + -48) by lia; apply (SV _ 20%nat 20%bv); [lia|reflexivity|cbn; tauto]
  | replace (tp_sp0 D - 56) with (tp_sp0 D + -56) by lia; apply (SV _ 21%nat 21%bv); [lia|reflexivity|cbn; tauto]
  | replace (tp_sp0 D - 64) with (tp_sp0 D + -64) by lia; apply (SV _ 22%nat 22%bv); [lia|reflexivity|cbn; tauto]
  | replace (tp_sp0 D - 72) with (tp_sp0 D + -72) by lia; apply (SV _ 23%nat 23%bv); [lia|reflexivity|cbn; tauto]
  | replace (tp_sp0 D - 80) with (tp_sp0 D + -80) by lia; apply (SV _ 24%nat 24%bv); [lia|reflexivity|cbn; tauto]
  | replace (tp_sp0 D - 88) with (tp_sp0 D + -88) by lia; apply (SV _ 25%nat 25%bv); [lia|reflexivity|cbn; tauto]
  | replace (tp_sp0 D - 96) with (tp_sp0 D + -96) by lia; apply (SV _ 26%nat 26%bv); [lia|reflexivity|cbn; tauto]
  | replace (tp_sp0 D - 104) with (tp_sp0 D + -104) by lia; apply (SV _ 27%nat 27%bv); [lia|reflexivity|cbn; tauto] ]. }
assert (RV : forall off n x v, In (YP09.mkChunk off (CVal n (SOff x 0))) (YP09.r_chunks s0_rec) ->
  ew E x = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem segs (mrestrict (w_H (tp_W D)) m) (tp_t D + off) (N.to_nat n) v).
{ intros off n x v Hin Hx Hv Hvn Hn.
  pose proof (s0_chunk_val E _ s0_mem_saved 3 s0_rec off n (SOff x 0) v HMO eq_refl Hin (Dv x v Hx Hv) Hvn Hn) as H.
  cbn [base_val YP09.r_base s0_rec] in H. rewrite Ht in H. exact H. }
split.
{ unfold prhtx_rec. split; [exact Rb|]. split; [exact Rl|]. split; [exact Rc|]. split; [exact Rf|].
  split; [rewrite <- (Z.add_0_r (tp_t D)); exact (RV 0 8%N 33%nat _ ltac:(cbn; tauto) E33 Rb ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(lia))|].
  split; [exact (RV 8 8%N 34%nat _ ltac:(cbn; tauto) E34 Rl ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(lia))|].
  split; [exact (RV 16 8%N 35%nat _ ltac:(cbn; tauto) E35 Rc ltac:(change (8 * Z.of_N 8) with 64; lia) ltac:(lia))|].
  exact (RV 24 4%N 36%nat _ ltac:(cbn; tauto) E36 ltac:(lia) ltac:(change (8 * Z.of_N 4) with 32; lia) ltac:(lia)). }
intros a Ha. destruct HMO as (_ & Hrs & _).
pose proof (proj1 (Forall_forall _ _) Hrs s0_rec ltac:(cbn; tauto)) as (_ & _ & Hw & _).
cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi s0_rec] in Hw. rewrite Ht in Hw.
replace a with (tp_t D + (a - tp_t D)) by lia. apply Hw. lia.
Qed.

(* the shadow-address registers S0 leaves: (t + c) >> 3 plus the shadow base, and t >> 3 *)
Lemma s0_U_add : forall E a b, U E (SAlu ALU_ADD a b) = (U E a + U E b) mod 2 ^ 64.
Proof. intros E a b. rewrite U_SAlu. cbn [zalu_raw]. unfold zcanon, M64. reflexivity. Qed.
Lemma s0_U_srl3 : forall E a, 0 <= U E a -> U E (SAlu ALU_SRL a (SLit 3)) = U E a / 8.
Proof.
intros E a Ha. rewrite U_SAlu, U_SLit. cbn [zalu_raw].
pose proof (U_range E a) as Hr.
assert (Z3 : zcanon 3 = 3) by (apply zcanon_id; unfold M64; lia). rewrite Z3. change (Z.land 3 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
apply zcanon_id. unfold M64 in *. split; [apply Z.div_pos; lia|].
apply (Z.le_lt_trans _ (U E a)); [apply Z.div_le_upper_bound; lia | lia].
Qed.
Lemma s0_shreg : forall E t c, bv_unsigned (ew E 10) = t -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  0 <= t -> 0 <= c -> t + c < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 c) (SLit 3)) (SOff 32 0)) = w64 (SHADOW_OFF + (t + c) / 8).
Proof.
intros E t c Ht H32 H0 Hc Hlt. apply bv_eq. unfold w64. rewrite Z_to_bv_unsigned.
change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 c) (SLit 3)) (SOff 32 0))))
  with (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 c) (SLit 3)) (SOff 32 0))).
assert (U10 : U E (SOff 10 c) = t + c) by (rewrite U_SOff, Ht; apply zcanon_id; unfold M64; lia).
assert (U32 : U E (SOff 32 0) = SHADOW_OFF).
{ rewrite U_SOff, H32, Z.add_0_r, unsigned_lit_small by (unfold SHADOW_OFF; lia). apply zcanon_id. unfold M64, SHADOW_OFF; lia. }
rewrite s0_U_add, s0_U_srl3, U10, U32 by (rewrite U10; lia).
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
assert (0 <= (t + c) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
rewrite !Z.mod_small by (unfold SHADOW_OFF; lia). lia.
Qed.
Lemma s0_tshr : forall E t, bv_unsigned (ew E 10) = t -> 0 <= t < 2 ^ 47 ->
  sv_denot E (SAlu ALU_SRL (SOff 10 0) (SLit 3)) = w64 (t / 8).
Proof.
intros E t Ht Hr. apply bv_eq. unfold w64. rewrite Z_to_bv_unsigned.
change (bv_unsigned (sv_denot E (SAlu ALU_SRL (SOff 10 0) (SLit 3)))) with (U E (SAlu ALU_SRL (SOff 10 0) (SLit 3))).
assert (U10 : U E (SOff 10 0) = t) by (rewrite U_SOff, Ht, Z.add_0_r; apply zcanon_id; unfold M64; lia).
rewrite s0_U_srl3, U10 by (rewrite U10; lia).
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
assert (0 <= t / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
rewrite Z.mod_small by lia. reflexivity.
Qed.

(* ---- small facts for the branches ---- *)
Lemma s0_sv_U : forall E e, sv_denot E e = Z_to_bv 64 (U E e).
Proof. intros E e. change (U E e) with (bv_unsigned (sv_denot E e)). symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma s0_denot0 : forall E x, sv_denot E (SOff x 0) = ew E x.
Proof. intros E x. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma s0_soff : forall E k c v, bv_unsigned (ew E k) = v -> sv_denot E (SOff k c) = Z_to_bv 64 (v + c).
Proof. intros E k c v H. cbn [sv_denot]. rewrite H. reflexivity. Qed.
Lemma s0_need : forall E n len0, bv_unsigned (ew E 12) = n -> ew E 34 = Z_to_bv 64 len0 ->
  0 <= n -> 0 <= len0 -> len0 + n + 1 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff 12 1) (SOff 34 0)) = Z_to_bv 64 (len0 + n + 1).
Proof.
intros E n len0 Hn Hl H0 H1 H2. rewrite s0_sv_U, s0_U_add, !U_SOff, Hn, Hl, unsigned_lit_small by lia.
rewrite Z.add_0_r, !zcanon_id by (unfold M64; lia). rewrite Z.mod_small by lia. f_equal. lia.
Qed.
Lemma s0_bne : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_NE (Z_to_bv 64 x) (Z_to_bv 64 y) = negb (x =? y).
Proof. intros x y Hx Hy. cbn [branch_taken]. unfold c_eq, bv_eqb. rewrite !unsigned_lit_small by lia. reflexivity. Qed.
Lemma s0_bgeu : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_GEU (Z_to_bv 64 x) (Z_to_bv 64 y) = (y <=? x).
Proof.
intros x y Hx Hy. cbn [branch_taken]. unfold bv_ltu. rewrite !unsigned_lit_small by lia.
destruct (Z.ltb_spec x y), (Z.leb_spec y x); cbn; try reflexivity; lia.
Qed.

(* ---- THE CUT at a state S0 reaches: the state is the entry's (no allocator call), the memory differs from the
   entry's only in tx_put's frame [sp0 - 112, sp0) and the record's window [t, t + 28) (the walk's frame_of facts),
   and the symbolic memory is s0_mem_saved: the carry (TxPutCarry102.txc_carry), the record's entry values, and
   the buffer / place / trace / side facts at the cut's memory ---- *)
Lemma s0_cut : forall D (E : env) (m3 : word -> option byte) (regs3 : bvmap 5 word) md3 k,
  tp_pre B CTX0 D -> tp_img B ->
  mem_ok segs E (mrestrict (w_H (tp_W D)) m3) s0_mem_saved ->
  bv_unsigned (ew E 2) = tp_sp0 D -> bv_unsigned (ew E 10) = tp_t D ->
  (forall k (r : bv 5), (k = 1 \/ k = 8 \/ k = 9 \/ (18 <= k <= 27))%nat -> Z.of_nat k = bv_unsigned r ->
     ew E k = getr (tp_regs D) r) ->
  ew E 33 = Z_to_bv 64 (tp_b0 D) -> ew E 34 = Z_to_bv 64 (tp_len0 D) -> ew E 35 = Z_to_bv 64 (tp_cap0 D) ->
  ew E 36 = Z_to_bv 64 (tp_f0 D) ->
  tp_J B SK D (tp_ly D) (tp_S D) (tp_Hp D) (tp_W D) m3 md3 k [] ->
  (forall x : word, ~ (tp_sp0 D - TP_FRAME <= bv_unsigned x < tp_sp0 D) ->
     ~ (tp_t D <= bv_unsigned x < tp_t D + 28) ->
     mrestrict (w_H (tp_W D)) m3 x = mrestrict (w_H (tp_W D)) (tp_mem D) x) ->
  same_but_materialized (tp_md D) md3 ->
  spZ regs3 = tp_sp0 D - TP_FRAME -> getr regs3 3 = getr (tp_regs D) 3 -> getr regs3 4 = getr (tp_regs D) 4 ->
  tp_carry B SK CTX0 D (tp_ly D) (tp_S D) (tp_Hp D) (tp_W D) regs3 m3 md3 k [] /\
  prhtx_rec (tp_W D) m3 (tp_t D) (tp_b0 D) (tp_len0 D) (tp_cap0 D) (tp_f0 D) /\
  prhtx_inv B (tp_Lam D) (tp_ly D) (tp_S D) (tp_W D) m3 (tp_b0 D) (tp_len0 D) (tp_cap0 D) (tp_txt D) /\
  prhtx_place (tp_ly D) (tp_S D) (tp_W D) (tp_regs D) m3 (tp_dw D) (tp_t D) /\
  prhtx_trace B (tp_ly D) (tp_W D) m3 (tp_t D) /\
  tp_side B D (tp_ly D) (tp_S D) (tp_Hp D) (tp_W D) m3 (tp_own D) /\
  bytes_at (tp_W D) m3 (tp_s D) (tp_src D).
Proof.
intros D E m3 regs3 md3 k HPRE HIMG HMO Hsp Ht HR E33 E34 E35 E36 HJ HK Hsame Hsp3 R3 R4.
pose proof HPRE as (HFPRE & HUNIV & HRL & HPOS & HLIVE & H10 & H11 & H12 & HFW & HPLACE & HTRACE & HREC & HINV &
  HSRC & HSLEN & HKEPT & HDISJ & HNEED & HLED & HEVP & HBB & HREQ & HLEN).
pose proof HREC as (Rb0 & Rl0 & Rc0 & Rf0 & _).
destruct (s0_mem_facts D E m3 HMO Hsp Ht HR E33 E34 E35 E36 Rb0 Rl0 Rc0 Rf0) as (HSV & HREC3 & HW3).
destruct (TxPutCarry102.txc_carry (SK := SK) B ARX LAWS TP_FRAME (tp_ly D) (tp_S D) (tp_Hp D) (tp_W D) (tp_regs D)
  (tp_mem D) (tp_md D) (tp_ch D) m3 md3 (tp_dw D) (tp_t D) (tp_b0 D) (tp_cap0 D) HFPRE
  ltac:(unfold TP_FRAME; lia) ltac:(unfold TP_FRAME; vm_compute; discriminate) HFW HPLACE HK Hsame HW3
  (TxPutCarry102.txc_present_of_rec _ _ _ _ _ _ _ HREC3) (tpi_pst_img _ HIMG))
  as (HKEPT3 & HROD3 & HPL3 & KINV & KTR & KLED & KOWN & KSRC).
destruct (KSRC _ _ HSRC) as [HSRC3 HBY3].
split.
{ split; [exact HPRE|]. split; [exact HJ|]. split; [exact HKEPT3|].
  split; [intros r Hr; destruct Hr as [<- | [<- | []]]; assumption|].
  split; [exact Hsp3|]. split; [exact HSV|]. split; [reflexivity | exact HROD3]. }
split; [exact HREC3|]. split; [exact (KINV _ _ _ _ _ HINV)|]. split; [exact HPL3|].
split; [exact (KTR HTRACE)|].
split; [|exact HBY3].
split; [exact (KLED _ _ _ _ _ _ _ _ HLED)|]. split; [exact HSRC3 | exact HRL].
Qed.

(* ---- the cut tactics: the memory facts of the final state, and the configuration in tp_cfg form ---- *)
Ltac s0_hmo HMO :=
  lazymatch goal with HSx : st_ok_pi _ _ ?Ef ?ssx (restrict ?H ?msc) |- _ =>
    pose proof (st_ok_mem_ok segs Ef (abs_ss VAL ssx) (restrict H msc) HSx) as HMO;
    cbn [abs_ss setpc ss_mem restrict ms_mem] in HMO;
    change (mem_ok segs Ef (mrestrict H (ms_mem msc)) s0_mem_saved) in HMO
  end.
Ltac s0_cfg o :=
  lazymatch goal with HSx : st_ok_pi _ _ ?Ef ?ssx (restrict ?H ?msc) |- SRr _ _ {| cfg_ms := ?msc; cfg_model := ?mdc |} _ =>
    rewrite (st_ok_pi_restrict_mkst _ _ _ _ HSx eq_refl) at 1; cbn [ss_pc];
    lazymatch goal with |- context [Z_to_bv 64 (?bs + ?lit)] =>
      replace (bs + lit) with (tp_pc o) by (unfold tp_pc; rewrite TP_OFF_val; unfold o; lia) end;
    lazymatch goal with |- SRr ?sg ?Wx _ ?QQ => change (SRr sg Wx (tp_cfg o (ms_regs msc) (ms_mem msc) mdc) QQ) end
  end.

(* the registers of the final state (no normalisation of the symbolic expression) *)
Ltac s0_reg r R :=
  lazymatch goal with HSx : st_ok_pi _ _ _ ?ssx (restrict ?H ?msc) |- _ =>
    pose proof (st_ok_pi_restrict_reg H _ ssx msc r HSx) as R;
    let e := eval vm_compute in (sr_get (ss_regs ssx) r) in change (sr_get (ss_regs ssx) r) with e in R
  end.

(* ---- the cuts after the GROW's realloc (FIT, END) carry the journal and the keep at wle' segs RZ_cf: S0 runs at one
   world (no allocator call), so its plain carry lifts (YA0nH.wle_wle') ---- *)
Lemma s0_carry_lift : forall D ly3 S3 Hp3 (W3 : world segs) regs3 mem3 md3 k WS,
  tp_carry B SK CTX0 D ly3 S3 Hp3 W3 regs3 mem3 md3 k WS ->
  tp_carryR B SK CTX0 (wle' segs YGcfRehidePost.RZ_cf) D ly3 S3 Hp3 W3 regs3 mem3 md3 k WS.
Proof.
intros D ly3 S3 Hp3 W3 regs3 mem3 md3 k WS (HP & HJ & HK & HR).
split; [exact HP|]. split.
- unfold tp_JR. unfold tp_J in HJ.
  exact (ajournal_xwR_mono (SK := SK) segs B prh_pst ARX (@wle segs) (wle' segs YGcfRehidePost.RZ_cf)
    (wle_wle' segs YGcfRehidePost.RZ_cf) _ _ _ _ _ (tp_Hp D) _ _ _ _ _ _ _ _ _ _ _ _ HJ).
- split; [|exact HR]. unfold tp_KR. unfold tp_K in HK.
  destruct HK as (K1 & K2 & K3 & K4).
  exact (conj K1 (conj K2 (conj (wle_wle' segs YGcfRehidePost.RZ_cf _ _ K3) K4))).
Qed.

Lemma tp_seg_S0_ok : forall P, srr_inv_laws segs P -> tp_seg_S0 B SK CTX0 P.
Proof.
intros P PLAW Q D HPRE HK1 HIMG KEND KFIT KGROW HP0.
pose proof HPRE as (HFPRE & HUNIV & HRL & HPOS & HLIVE & H10 & H11 & H12 & HFW & HPLACE & HTRACE & HREC & HINV &
  HSRC & HSLEN & HKEPT & HDISJ & HNEED & HLED & HEVP & HBB & HREQ & HLEN).
destruct HFPRE as (HPRE0 & HROD & HSTKHI & HRAC).
pose proof HPRE0 as ([HAR HXS] & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FTP : @STK_tx_put TP_PrhImg = 16496) by (vm_compute; reflexivity).
pose proof HFW as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HPLACE as (Hta & Ht1 & Ht2 & Hwrit & Hra28).
pose proof HREC as (Rb0 & Rl0 & Rc0 & Rf0 & Mb & Ml & Mc & Mf).
pose proof HINV as (Hltxt & Hinv).
unfold tp_need in HNEED. unfold tp_req, tp_need in HREQ.
set (t := tp_t D) in *. set (n := tp_n D) in *. set (b0 := tp_b0 D) in *. set (len0 := tp_len0 D) in *.
set (cap0 := tp_cap0 D) in *. set (f0 := tp_f0 D) in *. set (regs := tp_regs D) in *. set (mem := tp_mem D) in *.
set (W := tp_W D) in *. set (ly := tp_ly D) in *. set (S := tp_S D) in *.
assert (Hn0 : 0 <= n) by (rewrite <- HSLEN; lia).
assert (Hbc : 0 <= b0 <= 2 ^ 47 - 2 ^ 23 /\ 0 <= cap0 <= 2 ^ 47 - 2 ^ 23).
{ destruct Hinv as [(Ec & Eb & El) | (Hc0 & Hlc & Hblk & Hby & H4096 & Hceil8 & Hamr & Hw & Hra' & Hhull & Hnb)];
  lia. }
destruct (s0_entry (@STK_tx_put TP_PrhImg) ly S (tp_Hp D) W regs mem (tp_md D) (tp_ch D) (tp_dw D) t n b0 len0 cap0 f0
  (tpi_pal _ HIMG) HPRE0 ltac:(unfold TP_FRAME; lia) H10 H12 ltac:(lia) HFW Ht1 Ht2 Hta Hwrit HREC ltac:(lia) ltac:(lia) ltac:(lia))
  as [HS SHOK].
pose proof (ajournal_x_init_W (SK := SK) segs B prh_pst ARX (@STK_tx_put TP_PrhImg) (tp_dw D) (tp_FP D)
  ly S (tp_Hp D) W regs mem (tp_md D) (tp_ch D) HPRE0 ltac:(unfold fwin_x; exact HFW)) as HJ.
assert (HPM : P mem) by exact HP0.
remember (s0_E regs (s0_X b0 len0 cap0 f0)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold s0_E; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (map (Z_to_bv 64) (s0_X b0 len0 cap0 f0))) k)
  by (intros k Hk; subst E; unfold s0_E; apply Eimg_low; exact Hk).
assert (ER : forall (r : bv 5) k, Z.of_nat k = bv_unsigned r -> ew E k = getr regs r).
{ intros r k Hk. pose proof (u5_range r) as Hr. rewrite EL by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ k r Hk). }
destruct (s0_E_extra regs b0 len0 cap0 f0) as (X32 & X33 & X34 & X35 & X36). rewrite <- HE in X32, X33, X34, X35, X36.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (ER 2%bv 2%nat eq_refl); reflexivity).
assert (Ut : bv_unsigned (ew E 10) = t) by (rewrite (ER 10%bv 10%nat eq_refl), H10; apply unsigned_lit_small; lia).
assert (HAE : env_agree 32 (Ereg regs (map (Z_to_bv 64) (s0_X b0 len0 cap0 f0))) E).
{ split; [|subst E; reflexivity]. intros k Hk. rewrite (EL k ltac:(unfold A_TEXT; lia)). reflexivity. }
clear HE.
pose (RUN := @paj_run_x_inv fx rc SK B_prog_listing TP_PAListing PA B prh_pst ARX _ LAWS P PLAW).
pose (BR := paj_branch (PI := PA)).
pose (RET := paj_ret_at (PL := TP_PAListing) (PI := PA)).
unfold tp_cfg0, cfg_at. rewrite (tpi_entry _ HIMG).
change (w64 (BASE + TP_OFF)) with (Z_to_bv 64 (BASE + TP_OFF)).
(* the run is plain SRr (no allocator call), lifted once into SRr' segs RZ_cf, the continuations' relation *)
apply (YGcfRhLift.ra_rh_of_SRr segs YGcfRehidePost.RZ_cf).
assert (UB : U E s0_Bx = SHADOW_OFF).
{ unfold s0_Bx. rewrite U_SOff, X32, Z.add_0_r, unsigned_lit_small by (unfold SHADOW_OFF; lia).
  apply zcanon_id. unfold M64, SHADOW_OFF. lia. }
assert (UB0 : U E (SOff 32 0) = SHADOW_OFF) by exact UB.
assert (UT : forall c, 0 <= c <= 28 -> U E (SOff 10 c) = t + c).
{ intros c Hc. rewrite U_SOff, Ut. apply zcanon_id. unfold M64. lia. }
(* ---- the prologue, the alignment check, the shadow base, the 4-byte check of t + 24, failed ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM s0_Bspan.
{ rewrite UB, UT by lia. cbn [ms_mem mkst].
  apply (range_addressable_sub (aview segs (w_H W) mem) SHADOW_OFF t 28 (t + 24) 4 Hra28); lia. }
{ unfold s0_regions, TP_FRAME. s0_awr. }
rename HFr into HFr1. clear HF.
s0_keep K1 HFr1 W. rewrite Usp, Ut in K1.
pose (RUNTO := @paj_run_to_x_inv fx rc SK B_prog_listing TP_PAListing PA B prh_pst ARX _ LAWS P PLAW).
psrr_branch_tok RUN BR HS SHOK s0_Bspan.
- (* failed <> 0: A0 FAILED AT ENTRY, straight to the epilogue *)
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM s0_Bspan (TP_OFF + TP_PC_END).
  { unfold s0_regions, TP_FRAME. s0_awr. }
  rename HFr into HFr2. clear HF.
  s0_keepw KW1 HFr1. s0_keepw KW2 HFr2.
  repeat (rewrite ew_ewset_other in KW2 by lia). rewrite Usp, Ut in KW1, KW2.
  assert (KA : forall x : word, ~ (tp_sp0 D - TP_FRAME <= bv_unsigned x < tp_sp0 D) ->
     ~ (t <= bv_unsigned x < t + 28) -> mrestrict (w_H W) (ms_mem ms0) x = mrestrict (w_H W) mem x).
  { intros x H1 H2. unfold tp_sp0, TP_FRAME in H1. rewrite (KW2 x H1 H2). exact (KW1 x H1 H2). }
  rewrite s0_denot0 in Hc. repeat (rewrite ew_ewset_other in Hc by lia). rewrite X36 in Hc. cbn [sv_denot] in Hc.
  rewrite s0_bne in Hc by lia. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
  s0_hmo HMO.
  prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
  rewrite wvb_collapse in HJ.
  s0_cfg TP_PC_END. apply SRr_ret. cbv beta.
  lazymatch goal with |- SRr' _ _ _ (tp_cfg _ _ _ ?mdc) _ =>
    apply (KEND ly S (tp_Hp D) W (ms_regs ms0) (ms_mem ms0) mdc 0); [|assumption];
    destruct (s0_cut D _ (ms_mem ms0) (ms_regs ms0) mdc 0 HPRE HIMG HMO
      ltac:(repeat (rewrite ew_ewset_other by lia); exact Usp) ltac:(repeat (rewrite ew_ewset_other by lia); exact Ut)
      ltac:(intros kk r Hk Hr; repeat (rewrite ew_ewset_other by lia); exact (ER r kk Hr))
      ltac:(repeat (rewrite ew_ewset_other by lia); exact X33) ltac:(repeat (rewrite ew_ewset_other by lia); exact X34)
      ltac:(repeat (rewrite ew_ewset_other by lia); exact X35) ltac:(repeat (rewrite ew_ewset_other by lia); exact X36)
      HJ KA ltac:(apply same_but_materialized_wvb_any)
      ltac:(unfold spZ; rewrite R2, Usp; unfold tp_sp0, TP_FRAME; rewrite unsigned_lit_small by lia; fold regs; lia)
      ltac:(rewrite R3; exact (ER 3%bv 3%nat eq_refl)) ltac:(rewrite R4; exact (ER 4%bv 4%nat eq_refl)))
      as (HCAR & HREC3 & HINV3 & HPL3 & HTR3 & HSIDE3 & HBY3)
  end.
  exists []. split; [exact (tp_budget_nil D)|].
  split; [exact (s0_carry_lift _ _ _ _ _ _ _ _ _ _ HCAR)|].
  pose proof HSIDE3 as (HLED3 & HSRC3 & HRL3).
  exists b0, cap0, f0, (tp_own D), [].
  cbn [length]. rewrite Z.add_0_r, app_nil_r.
  split.
  { split; [exact HREC3|]. split; [exact HINV3|]. split; [exact HPL3|]. split; [reflexivity|].
    split; [left; split; [reflexivity|]; split; reflexivity | change (tp_S D) with S; change (tp_cap0 D) with cap0; lia]. }
  split; [right; left; repeat split; auto|].
  split; [intros Hz; exfalso; exact (Hc Hz)|].
  split; [exact HBY3|]. split; [exact HRL3|].
  split; [intros H0; exfalso; exact (Hc H0)|].
  split; [intros _; exact HPOS | exact HLED3].
- (* failed = 0: the checks of t + 8 / t + 16, the need test *)
  paj_run_tok_x_inv RUN HS HJ SHOK HPM s0_Bspan.
  { rewrite s0_rd_of. unfold s0_Bx. rewrite !s0_U_ewset by lia. rewrite UB0, (UT 16 ltac:(lia)).
    eapply (range_addressable_agree (aview segs (w_H W) mem)).
    { intros x Hx. pose proof (s0_shadow_lo x ltac:(lia)). apply K1; lia. }
    apply (range_addressable_sub (aview segs (w_H W) mem) SHADOW_OFF t 28 (t + 16) 8 Hra28); lia. }
  { rewrite s0_rd_of. unfold s0_Bx. rewrite !s0_U_ewset by lia. rewrite UB0, (UT 8 ltac:(lia)).
    eapply (range_addressable_agree (aview segs (w_H W) mem)).
    { intros x Hx. pose proof (s0_shadow_lo x ltac:(lia)). apply K1; lia. }
    apply (range_addressable_sub (aview segs (w_H W) mem) SHADOW_OFF t 28 (t + 8) 8 Hra28); lia. }
  { unfold s0_regions, TP_FRAME. s0_awr. }
  rename HFr into HFr2. clear HF.
  rename Hc into HcF.
  rewrite s0_denot0 in HcF. repeat (rewrite ew_ewset_other in HcF by lia). rewrite X36 in HcF. cbn [sv_denot] in HcF.
  rewrite s0_bne in HcF by lia. apply Bool.negb_false_iff, Z.eqb_eq in HcF. rename HcF into Hf0.
  assert (Un : bv_unsigned (ew E 12) = n) by (rewrite (ER 12%bv 12%nat eq_refl), H12; apply unsigned_lit_small; lia).
  psrr_branch_tok RUN BR HS SHOK s0_Bspan.
  + (* need <= cap0: the buffer fits; the bgeu to FIT *)
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM s0_Bspan (TP_OFF + TP_PC_FIT).
    { unfold s0_regions, TP_FRAME. s0_awr. }
    rename HFr into HFr3. clear HF.
    rewrite s0_denot0 in Hc. repeat (rewrite ew_ewset_other in Hc by lia). rewrite X35 in Hc.
    rewrite (s0_need _ n len0) in Hc by (repeat (rewrite ew_ewset_other by lia); first [exact Un | exact X34 | lia]).
    rewrite s0_bgeu in Hc by lia. apply Z.leb_le in Hc.
    s0_keepw KW1 HFr1. s0_keepw KW2 HFr2. s0_keepw KW3 HFr3.
    repeat (rewrite ew_ewset_other in KW2 by lia). repeat (rewrite ew_ewset_other in KW3 by lia).
    rewrite Usp, Ut in KW1, KW2, KW3.
    lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msc) |- _ =>
      assert (KA : forall x : word, ~ (tp_sp0 D - TP_FRAME <= bv_unsigned x < tp_sp0 D) ->
        ~ (t <= bv_unsigned x < t + 28) -> mrestrict (w_H W) (ms_mem msc) x = mrestrict (w_H W) mem x)
      by (intros x H1 H2; unfold tp_sp0, TP_FRAME in H1; rewrite (KW3 x H1 H2), (KW2 x H1 H2); exact (KW1 x H1 H2))
    end.
    rewrite !wvb_collapse in HJ.
    s0_reg (8%bv : bv 5) R8. s0_reg (9%bv : bv 5) R9. s0_reg (18%bv : bv 5) R18. s0_reg (22%bv : bv 5) R22.
    s0_reg (19%bv : bv 5) R19. s0_reg (21%bv : bv 5) R21. s0_reg (23%bv : bv 5) R23. s0_reg (25%bv : bv 5) R25.
    s0_reg (26%bv : bv 5) R26.
    rewrite s0_denot0 in R8, R9, R18, R22. repeat (rewrite ew_ewset_other in R8 by lia). repeat (rewrite ew_ewset_other in R9 by lia). repeat (rewrite ew_ewset_other in R18 by lia). repeat (rewrite ew_ewset_other in R22 by lia).
    rewrite (ER 10%bv 10%nat eq_refl), H10 in R8. rewrite (ER 12%bv 12%nat eq_refl), H12 in R9.
    rewrite (ER 11%bv 11%nat eq_refl), H11 in R18. rewrite X32 in R22.
    rewrite (s0_soff _ 10 8 t) in R19 by (repeat (rewrite ew_ewset_other by lia); exact Ut).
    rewrite (s0_soff _ 10 16 t) in R21 by (repeat (rewrite ew_ewset_other by lia); exact Ut).
    rewrite (s0_shreg _ t 8) in R23 by (repeat (rewrite ew_ewset_other by lia); first [exact Ut | exact X32 | lia]).
    rewrite (s0_shreg _ t 16) in R25 by (repeat (rewrite ew_ewset_other by lia); first [exact Ut | exact X32 | lia]).
    rewrite (s0_tshr _ t) in R26 by (repeat (rewrite ew_ewset_other by lia); first [exact Ut | lia]).
    s0_cfg TP_PC_FIT. apply SRr_ret. cbv beta.
    lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msc) |- SRr' _ _ _ (tp_cfg _ _ _ ?mdc) _ =>
      apply (KFIT ly S (tp_Hp D) W (ms_regs msc) (ms_mem msc) mdc 0 b0 cap0); [|assumption] end.
    s0_hmo HMO. s0_reg (2%bv : bv 5) R2. s0_reg (3%bv : bv 5) R3. s0_reg (4%bv : bv 5) R4.
    rewrite s0_denot0 in R3, R4. repeat (rewrite ew_ewset_other in R3 by lia). repeat (rewrite ew_ewset_other in R4 by lia).
    lazymatch goal with HSx : st_ok_pi _ _ ?Ef _ (restrict _ ?msc) |- _ =>
    lazymatch type of HJ with ?fj ?mdc ?kj =>
    destruct (s0_cut D Ef (ms_mem msc) (ms_regs msc) mdc kj HPRE HIMG HMO
      ltac:(repeat (rewrite ew_ewset_other by lia); exact Usp) ltac:(repeat (rewrite ew_ewset_other by lia); exact Ut)
      ltac:(intros kk r Hk Hr; repeat (rewrite ew_ewset_other by lia); exact (ER r kk Hr))
      ltac:(repeat (rewrite ew_ewset_other by lia); exact X33) ltac:(repeat (rewrite ew_ewset_other by lia); exact X34)
      ltac:(repeat (rewrite ew_ewset_other by lia); exact X35) ltac:(repeat (rewrite ew_ewset_other by lia); exact X36)
      HJ KA ltac:(apply same_but_materialized_wvb_any)
      ltac:(unfold spZ; rewrite R2, (s0_soff _ 2 (-112) (spZ regs)) by (repeat (rewrite ew_ewset_other by lia); exact Usp);
            unfold tp_sp0, TP_FRAME; rewrite unsigned_lit_small by lia; fold regs; lia)
      ltac:(rewrite R3; exact (ER 3%bv 3%nat eq_refl)) ltac:(rewrite R4; exact (ER 4%bv 4%nat eq_refl)))
      as (HCAR & HREC3 & HINV3 & HPL3 & HTR3 & HSIDE3 & HBY3)
    end end.
    pose proof HINV3 as (Hl3 & [(Ec & _ & _) | (Hc0 & Hlc & Hblk & Hby & H4096 & Hbceil & Hamr & Hw & Hra' & Hhull & Hnb)]);
      [unfold tp_need in *; lia|].
    (* the buffer's + 8 margin: the batch-kit prhtx_inv states the block below the ceiling only; the margin is the
       allocator's (AR_laws_x's alx_blocks_ceil8, F21b), at the entry state where the block is live *)
    assert (Hce8 : b0 + cap0 + 8 <= YM05.alloc_ceiling).
    { pose proof HPRE0 as ([HARe HXSe] & _).
      pose proof (alx_blocks_ceil8 segs B (ARcfx B) LAWS _ _ _ _ _ _ _ _ (conj HARe HXSe) Hblk) as X.
      unfold req_size in X. unfold b0, cap0 in *. destruct (Z.eqb_spec (tp_cap0 D) 0); lia. }
    exists []. split; [exact (tp_budget_nil D)|].
    split; [exact (s0_carry_lift _ _ _ _ _ _ _ _ _ _ HCAR)|].
    split; [unfold tp_shregs; repeat split; assumption|].
    split; [exact Hf0|].
    do 5 (split; [assumption|]).
    split; [unfold tp_recat; rewrite <- Hf0; exact HREC3|].
    split; [repeat split; assumption|].
    split; [exact (proj1 (proj1 (garr8_app segs _ _ _ _) Hby))|].
    split; [unfold tp_need; lia|].
    split; [intros a Ha; exact (proj2 (HDISJ a Ha))|].
    split; [exact HKEPT|].
    split; [left; unfold tp_need; repeat split; lia|].
    split; [exact HSIDE3|].
    split; [intros _ _ Hlt; unfold tp_need in *; lia | intros _; exact HPOS].
  + (* cap0 < need: fall into the grow block *)
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM s0_Bspan (TP_OFF + TP_PC_GROW).
    { unfold s0_regions, TP_FRAME. s0_awr. }
    rename HFr into HFr3. clear HF.
    rewrite s0_denot0 in Hc. repeat (rewrite ew_ewset_other in Hc by lia). rewrite X35 in Hc.
    rewrite (s0_need _ n len0) in Hc by (repeat (rewrite ew_ewset_other by lia); first [exact Un | exact X34 | lia]).
    rewrite s0_bgeu in Hc by lia. apply Z.leb_gt in Hc.
    s0_keepw KW1 HFr1. s0_keepw KW2 HFr2. s0_keepw KW3 HFr3.
    repeat (rewrite ew_ewset_other in KW2 by lia). repeat (rewrite ew_ewset_other in KW3 by lia).
    rewrite Usp, Ut in KW1, KW2, KW3.
    lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msc) |- _ =>
      assert (KA : forall x : word, ~ (tp_sp0 D - TP_FRAME <= bv_unsigned x < tp_sp0 D) ->
        ~ (t <= bv_unsigned x < t + 28) -> mrestrict (w_H W) (ms_mem msc) x = mrestrict (w_H W) mem x)
      by (intros x H1 H2; unfold tp_sp0, TP_FRAME in H1; rewrite (KW3 x H1 H2), (KW2 x H1 H2); exact (KW1 x H1 H2))
    end.
    rewrite !wvb_collapse in HJ.
    s0_reg (8%bv : bv 5) R8. s0_reg (9%bv : bv 5) R9. s0_reg (18%bv : bv 5) R18. s0_reg (22%bv : bv 5) R22.
    s0_reg (19%bv : bv 5) R19. s0_reg (21%bv : bv 5) R21. s0_reg (23%bv : bv 5) R23. s0_reg (25%bv : bv 5) R25.
    s0_reg (26%bv : bv 5) R26.
    rewrite s0_denot0 in R8, R9, R18, R22. repeat (rewrite ew_ewset_other in R8 by lia). repeat (rewrite ew_ewset_other in R9 by lia). repeat (rewrite ew_ewset_other in R18 by lia). repeat (rewrite ew_ewset_other in R22 by lia).
    rewrite (ER 10%bv 10%nat eq_refl), H10 in R8. rewrite (ER 12%bv 12%nat eq_refl), H12 in R9.
    rewrite (ER 11%bv 11%nat eq_refl), H11 in R18. rewrite X32 in R22.
    rewrite (s0_soff _ 10 8 t) in R19 by (repeat (rewrite ew_ewset_other by lia); exact Ut).
    rewrite (s0_soff _ 10 16 t) in R21 by (repeat (rewrite ew_ewset_other by lia); exact Ut).
    rewrite (s0_shreg _ t 8) in R23 by (repeat (rewrite ew_ewset_other by lia); first [exact Ut | exact X32 | lia]).
    rewrite (s0_shreg _ t 16) in R25 by (repeat (rewrite ew_ewset_other by lia); first [exact Ut | exact X32 | lia]).
    rewrite (s0_tshr _ t) in R26 by (repeat (rewrite ew_ewset_other by lia); first [exact Ut | lia]).
    s0_reg (11%bv : bv 5) R11. s0_reg (12%bv : bv 5) R12. s0_reg (20%bv : bv 5) R20. s0_reg (24%bv : bv 5) R24.
    rewrite (s0_need _ n len0) in R11 by (repeat (rewrite ew_ewset_other by lia); first [exact Un | exact X34 | lia]).
    rewrite s0_denot0 in R12. repeat (rewrite ew_ewset_other in R12 by lia). rewrite X35 in R12.
    rewrite (s0_soff _ 10 24 t) in R20 by (repeat (rewrite ew_ewset_other by lia); exact Ut).
    rewrite (s0_shreg _ t 24) in R24 by (repeat (rewrite ew_ewset_other by lia); first [exact Ut | exact X32 | lia]).
    s0_cfg TP_PC_GROW. apply SRr_ret. cbv beta.
    lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msc) |- SRr' _ _ _ (tp_cfg _ _ _ ?mdc) _ =>
      apply (KGROW ly S (tp_Hp D) W (ms_regs msc) (ms_mem msc) mdc 0); [|assumption] end.
    s0_hmo HMO. s0_reg (2%bv : bv 5) R2. s0_reg (3%bv : bv 5) R3. s0_reg (4%bv : bv 5) R4.
    rewrite s0_denot0 in R3, R4. repeat (rewrite ew_ewset_other in R3 by lia). repeat (rewrite ew_ewset_other in R4 by lia).
    lazymatch goal with HSx : st_ok_pi _ _ ?Ef _ (restrict _ ?msc) |- _ =>
    lazymatch type of HJ with ?fj ?mdc ?kj =>
    destruct (s0_cut D Ef (ms_mem msc) (ms_regs msc) mdc kj HPRE HIMG HMO
      ltac:(repeat (rewrite ew_ewset_other by lia); exact Usp) ltac:(repeat (rewrite ew_ewset_other by lia); exact Ut)
      ltac:(intros kk r Hk Hr; repeat (rewrite ew_ewset_other by lia); exact (ER r kk Hr))
      ltac:(repeat (rewrite ew_ewset_other by lia); exact X33) ltac:(repeat (rewrite ew_ewset_other by lia); exact X34)
      ltac:(repeat (rewrite ew_ewset_other by lia); exact X35) ltac:(repeat (rewrite ew_ewset_other by lia); exact X36)
      HJ KA ltac:(apply same_but_materialized_wvb_any)
      ltac:(unfold spZ; rewrite R2, (s0_soff _ 2 (-112) (spZ regs)) by (repeat (rewrite ew_ewset_other by lia); exact Usp);
            unfold tp_sp0, TP_FRAME; rewrite unsigned_lit_small by lia; fold regs; lia)
      ltac:(rewrite R3; exact (ER 3%bv 3%nat eq_refl)) ltac:(rewrite R4; exact (ER 4%bv 4%nat eq_refl)))
      as (HCAR & HREC3 & HINV3 & HPL3 & HTR3 & HSIDE3 & HBY3)
    end end.
    split; [exact HK1|].
    split; [exact HCAR|].
    split; [unfold tp_shregs; repeat split; assumption|].
    split; [exact Hf0|]. split; [unfold tp_need; lia|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact R11|]. split; [exact R12|].
    do 7 (split; [assumption|]).
    split; [unfold tp_recat; rewrite <- Hf0; exact HREC3|].
    split; [exact HINV3|]. split; [exact HTR3 | exact HSIDE3].
Qed.

End s0.
