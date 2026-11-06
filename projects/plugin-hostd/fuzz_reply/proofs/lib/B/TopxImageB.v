(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Theorem Labs, 2026-10 (a Theorem Labs lane): image B's .str.3 shadow pin over a generic ARx, the hypothesis
     HSTR3S : ashp_x ARx (VAL (A_OBJ 25)) 1
   of lib/B/W_LLVMFuzzerTestOneInput_remove_x.v (Section wrx; a Theorem Labs lane's B ARM_remove over ARx,
   a working branch f9a2a493730), read there only through rm_ashp_str3_x at check_shape_ends' .str.3
   premises.  It is the image-B analogue of image A's HSTR2S (lib/A/W_LLVMFuzzerTestOneInput_remove_x.v at
   a working branch bb9dae5d905), which lib/A/W_shadow_pin_x.v's ashp_str2_1_fr_x / ashp_str2_1_fr_cf discharge
   (WriteX, 31c12112315).  The METHOD is that file's; every numeral is image B's (fuzz_reply.asan-ubsan, sha256
   10ffb5f9202ae2bd):
     .str.3   ""   A_OBJ 25 = 0x20ee0 (lib/B/W_place.v fr_obj 25), 1 byte (the NUL), in B's "r--" segment
              [0x10000, 0x2f9ec); its ASan global descriptor (beg 0x20ee0, size 1, size_with_redzone 32, ".str.3")
              poisons granule 0x20ee0 to 1 and [0x20ee8, 0x20f00) to 0xf9.
     shadow_of_addr 0x20ee0 = SHADOW_OFF (0x7fff8000, Reusable/YG0f.v) + 0x20ee0 / 8 = 0x7fffc1dc;
     the 8-aligned hull [0x7fffc1d8, 0x7fffc1e0): f9 f9 f9 f9 01 f9 f9 f9, each a const cell of image B's start-up
     table lib/B/YF0m.v Tfib_const_shadow (0x7fffc1d8-db: .str.1's redzone; 0x7fffc1dc = 1; 0x7fffc1dd-df: .str.3's
     redzone).  shp_check decides it by vm_compute over YF0m.Tfib_const_shadow / Tfib_zero_shadow.
   - THE LAWS READ.  The proof reads two facts of the relation and nothing else: every const cell of as_const B ly
     holds (YCbqG.v ARx_const_cells_law, AR_laws_x field alx_const_cells) and every zero-shadow range reads 0
     (YCbqG.v ARx_zshadow_law, field alx_zshadow).  Section a states them as their law BODIES (LCC, LZS), so no
     carrier's name is in the core.  ashp_str3_1_fr_x takes them from the Section's own LAWS : AR_laws_x segs B ARx
     hl, the Reusable YCbqG record that remove_x's Section wrx binds (remove_x Requires Reusable YCbqG, as the B ARx
     kit's W_kit_x / W_journal_x / W_contract_x do); the two projections convert to LCC / LZS.  No off-image fact of
     the YCbq carry (its image top, which is image A's, or its off-image block lemmas) is used anywhere in this file.
   - ashp_str3_1_fr_x: for every B with lib/B/YF0m.TfibSyms B and every ARx with AR_laws_x: its type is HSTR3S's
     text at remove_x's Section variables B HT ARx LAWS (so `ashp_str3_1_fr_x B HT ARx LAWS` discharges HSTR3S).
   - ashp_str3_1_fr_cf: at the cf instance of image B's top_x (B := TfibB of lib/B/YD2l.v, ARx := ARcf segs TfibB
     /\ Hp = [], the ARX of lib/B/W_LLVMFuzzerTestOneInput_top_x.v:132-133 at a working branch
     2cde0860a09, there at cp := CfParams_reply), for every CfParams cp: the two laws are projections of ARcf's first
     conjunct ARmcf (YG0ncf.v amc_const, amc_zshadow), so no AR_laws_x record is built. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YM05 YP0b YA0n YG00 YG0a YG01 YG0f YG0n YG0d YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_tbl W_kit W_img W_contract W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YF0l YF0m.
(* the generic carry remove_x's Section takes (remove_x.v:58), and B's ashp_x *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_x.
(* the cf instance: image B's start-up instance and the cf live state *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* YCbqG.v ARx_const_cells_law and ARx_zshadow_law, by their bodies *)
Hypothesis LCC : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md ->
  Forall (cell_holds B ly (aview SEGS (w_H W) mem)) (as_const B ly).
Hypothesis LZS : forall ly S Hp (W : world SEGS) mem md r, ARx ly S Hp W mem md ->
  In r (YG0n.zero_shadow_ranges B ly) -> zero_shadow (aview SEGS (w_H W) mem) SHADOW_OFF (fst r) (snd r).

Section b.
Variable cs : list acell.
Variable zs : list (Z * Z).
Hypothesis HCS : forall ly c, In c cs -> In c (as_const B ly).
Hypothesis HZS : forall r, In r zs -> In r (as_zero_shadow B).

(* lib/B/W_shadow_pin.v:112 shp_val_ok, over ARx: am_const -> LCC, am_zshadow -> LZS *)
Lemma shp_val_ok_x : forall ly S Hp (W : world SEGS) mem md s v, ARx ly S Hp W mem md -> shp_val cs zs s = Some v ->
aview SEGS (w_H W) mem s = Some v.
Proof.
intros ly S Hp W mem md s v HAR H. unfold shp_val in H.
destruct (shp_cells_at s cs) as [u|] eqn:Ec.
- injection H as <-. apply shp_cells_at_ok in Ec as (c & Hc & Hu).
  pose proof (proj1 (Forall_forall _ _) (LCC ly S Hp W mem md HAR) c (HCS ly c Hc)) as Hh.
  exact (shp_cell_at_ok B s c u ly _ Hu Hh).
- destruct (shp_zs_at s zs) eqn:Ez; [|discriminate H]. injection H as <-.
  unfold shp_zs_at in Ez. apply existsb_exists in Ez as (r & Hr & Hb).
  apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  assert (Hin : In r (YG0n.zero_shadow_ranges B ly)) by (right; exact (HZS r Hr)).
  pose proof (LZS ly S Hp W mem md r HAR Hin) as Hzr. red in Hzr.
  specialize (Hzr (s - (SHADOW_OFF + fst r / 8)) ltac:(lia)). unfold YG0v.shadow_of_addr in Hzr.
  replace (SHADOW_OFF + fst r / 8 + (s - (SHADOW_OFF + fst r / 8))) with s in Hzr by lia. exact Hzr.
Qed.

(* lib/B/W_shadow_pin.v:130 shp_ashp, over ARx *)
Theorem shp_ashp_x : forall a n, shp_check cs zs a n = true -> ashp_x ARx a n.
Proof.
intros a n Hc ly S Hp W mem md HAR. unfold shp_check in Hc. apply andb_true_iff in Hc as [Hr Hh]. split.
- intros x Hx. rewrite forallb_forall in Hr. specialize (Hr x (shp_zseq_in a n x Hx)). cbv beta in Hr.
  destruct (shp_val cs zs (shadow_of_addr SHADOW_OFF x)) as [s|] eqn:Ev; [|discriminate Hr].
  exists s. split; [exact (shp_val_ok_x ly S Hp W mem md _ s HAR Ev)|].
  unfold shp_saddrb in Hr. unfold saddr_ok. apply orb_true_iff in Hr as [Hr|Hr]; [left; apply Z.eqb_eq; exact Hr|right].
  apply andb_true_iff in Hr as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. split; assumption.
- intros Hn s Hs. apply orb_true_iff in Hh as [Hh|Hh]; [apply Z.leb_le in Hh; lia|].
  rewrite forallb_forall in Hh.
  assert (Hin : In s (shp_zseq (shadow_addr a / 8 * 8)
    (shadow_addr (a + n - 1) / 8 * 8 + 8 - shadow_addr a / 8 * 8))) by (apply shp_zseq_in; lia).
  specialize (Hh s Hin). cbv beta in Hh.
  destruct (shp_val cs zs s) as [v|] eqn:Ev; [|discriminate Hh].
  rewrite (shp_val_ok_x ly S Hp W mem md s v HAR Ev). discriminate.
Qed.
End b.
End a.

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
Variable B : asyms.
Hypothesis HT : YF0m.TfibSyms B.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.

(* lib/B/W_shadow_pin_fr.v:38 tfib_shp, over ARx and the two law bodies *)
Lemma tfib_shp_x :
  (forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md ->
     Forall (cell_holds B ly (aview segs (w_H W) mem)) (as_const B ly)) ->
  (forall ly S Hp (W : world segs) mem md r, ARx ly S Hp W mem md ->
     In r (YG0n.zero_shadow_ranges B ly) -> zero_shadow (aview segs (w_H W) mem) SHADOW_OFF (fst r) (snd r)) ->
  forall a n, shp_check YF0m.Tfib_const_shadow YF0m.Tfib_zero_shadow a n = true -> ashp_x ARx a n.
Proof.
intros LCC LZS a n H. apply (shp_ashp_x B ARx LCC LZS YF0m.Tfib_const_shadow YF0m.Tfib_zero_shadow); [| | exact H].
- intros ly c Hc. rewrite (YF0m.ts_const _ HT ly). unfold YF0m.Tfib_const.
  apply in_or_app. right. apply in_or_app. right. exact Hc.
- intros r Hr. rewrite (YF0m.ts_zsh _ HT). exact Hr.
Qed.

(* remove_x's Section wrx: Context {hl : Z}, Hypothesis LAWS (remove_x.v:89-90) *)
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.

(* HSTR3S (remove_x.v:239): .str.3 "" (check_shape_ends' prefix operand, a1 at 0x84878 before the call at 0x84884),
   A_OBJ 25 = 0x20ee0, 1 byte; 0x7fffc1dc = 1 *)
Lemma ashp_str3_1_fr_x : ashp_x ARx (VAL (A_OBJ 25)) 1.
Proof.
apply tfib_shp_x.
- intros ly S Hp W mem md HAR. exact (alx_const_cells _ _ _ LAWS ly S Hp W mem md HAR).
- intros ly S Hp W mem md r HAR Hr. exact (alx_zshadow _ _ _ LAWS ly S Hp W mem md r HAR Hr).
- vm_compute. reflexivity.
Qed.

(* the address, on image B's placement (a wrong object index fails here) *)
Example str3_addr_b : VAL (A_OBJ 25) = 0x20ee0.
Proof. vm_compute. reflexivity. Qed.
End f.

(* ------------------------------------------------------------------ at the cf instance of image B's top_x *)
Section cf. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
(* top_x's ARX (lib/B/W_LLVMFuzzerTestOneInput_top_x.v:132-133 Definition ARX at 2cde0860a09, there at
   cp := CfParams_reply): the laws are ARmcf's amc_const and amc_zshadow (YG0ncf.v), the first conjunct of ARcf *)
Lemma ashp_str3_1_fr_cf :
  ashp_x (fun ly S Hp (W : world segs) mem md => ARcf segs TfibB ly S Hp W mem md /\ Hp = [])
    (VAL (A_OBJ 25)) 1.
Proof.
apply (tfib_shp_x TfibB TfibB_syms _).
- intros ly S Hp W mem md ((M & _) & _). exact (amc_const _ _ _ _ _ M).
- intros ly S Hp W mem md r ((M & _) & _) Hr. exact (proj1 (Forall_forall _ _) (amc_zshadow _ _ _ _ _ M) r Hr).
- vm_compute. reflexivity.
Qed.
End cf.
