(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset (asan-ubsan image B), the reader form of the read-only bytes
   (YCeg.arodata_ok) at a driver state, from its symbolic memory: drv_pre_cf's last conjunct (lib/AU/PresetD1sitesB.v),
   which cf layer field round 3's call boundary needs (YG0dcf.v acall_pre_cf: arodata_ok_cf; at CfImg_B it follows
   from this form by CfAroPresetB.arodata_ok_cf_preset_AU). The asan image's twin is lib/A/PresetDrvAroA.v.
   YD2d.v's img_facts_of reads the same bytes off the image cells of ONE region list whose cells are YD2d.IMG_CELLS
   exactly; the driver's states carry the image regions in other forms, whose cells differ. drv_arodata_img takes any
   region list I inside the state's memory and asks the cover check of YD2d (cover_from) directly over I's image
   cells, the owned static data and errno, which vm_compute decides at each state. drv_img_cells_view is
   YD2d.img_cells_view with its cell premise over I's own cells.
   Rule 24: no function is proved here (an image fact of a driver state). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YImgCellsB.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK00 YK0h YK14 YK1b YK15 YK18
YK0p YP0n YK0s YM02 YP0m YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YP0e YN3q YN3v YI04 YL0a YL09 YL02 YL04 YK04 YA0i
YA0n YA0o YA0p YA0m YK09 YA0e YG00 YG01 YG0f YG0v YG0n YG0d YCe5 YB1v YB12 YF0l YB1h YB13 YF0m YD2j YD2i YD1t YD20
YD1v YD1y YD26 YD24.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YCeg YD2d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis HB : TfibSyms B.

(* YD2d.img_cells_view, over the cells of I itself *)
Lemma drv_img_cells_view : forall (I : smem) E (H : word -> bool) m rs clo cl,
  mem_ok tfibsegs E (mrestrict H m) rs -> (forall r, In r I -> In r rs) -> In (clo, cl) (img_cells I) ->
  forall a, clo <= a < clo + cl ->
  aview tfibsegs H m a = option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 a)).
Proof.
intros I E H m rs clo cl (_ & Hok & _) Hsub Hin a Ha. unfold img_cells in Hin.
apply in_flat_map in Hin as (r & Hr & Hin).
pose proof (proj1 (Forall_forall _ _) Hok _ (Hsub r Hr)) as (_ & _ & _ & HC).
destruct (r_base r) as [n|] eqn:Eb; [destruct Hin|]. cbn [base_val] in HC.
apply in_flat_map in Hin as (c & Hc & Hin). destruct (YP09.c_val c) as [w v|zl|il|d s0 dl] eqn:Ev; try (destruct Hin; fail); [].
destruct Hin as [Heq|[]]. injection Heq as E1 E2.
pose proof (proj1 (Forall_forall _ _) HC _ Hc (a - clo)) as Hck. rewrite E2, E1, Ev in Hck.
destruct (Hck ltac:(lia)) as (b & Hb1 & Hb2). cbn [cbyte] in Hb1. unfold img_byte in Hb1.
replace (0 + clo + (a - clo)) with a in Hb1, Hb2 by lia. unfold aview. rewrite Hb2, <- Hb1. reflexivity.
Qed.

(* THE READ-ONLY BYTES at a state whose memory rs holds the regions I, when I's image cells with the owned static
   data and errno cover the image's read-only ranges (the two cover checks, by vm_compute at each state) *)
Lemma drv_arodata_img : forall (I rs : smem) E (H : word -> bool) m,
  cover_from 2000 (img_cells I ++ Tfib_owned_static ++ [(TFIB_ERRNO, 4)]) 0x10000 YImgCellsB.B_SEG1_PAGE_HI = true ->
  cover_from 2000 (img_cells I ++ Tfib_owned_static ++ [(TFIB_ERRNO, 4)]) TFIB_RELRO_LO TFIB_RELRO_HI = true ->
  mem_ok tfibsegs E (mrestrict H m) rs -> (forall r, In r I -> In r rs) ->
  arodata_ok B (aview tfibsegs H m).
Proof.
intros I rs E H m C1 C2 HM Hsub a Hrin Hno Herr.
assert (Hro : 0x10000 <= a < YImgCellsB.B_SEG1_PAGE_HI \/ TFIB_RELRO_LO <= a < TFIB_RELRO_HI).
{ destruct Hrin as [(s & Hs & Hws & Hrg) | Hrel]; [left | right; exact Hrel].
  cbn in Hs. destruct Hs as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hws, Hrg; try discriminate Hws; lia. }
assert (Hc : exists c, In c (img_cells I ++ Tfib_owned_static ++ [(TFIB_ERRNO, 4)]) /\ fst c <= a < fst c + snd c).
{ destruct Hro as [Hro|Hro]; [exact (cover_from_sound _ _ _ _ C1 a Hro) | exact (cover_from_sound _ _ _ _ C2 a Hro)]. }
destruct Hc as ([clo cl] & Hin & Hca). cbn [fst snd] in Hca.
apply in_app_iff in Hin as [Hin | Hin]; [exact (drv_img_cells_view I E H m rs clo cl HM Hsub Hin a Hca)|].
apply in_app_iff in Hin as [Hin | [Heq | []]].
- exfalso. apply Hno. rewrite (ts_owned B HB). apply Exists_exists. exists (clo, cl). split; [exact Hin | unfold in_zr; cbn; lia].
- exfalso. apply Herr. rewrite (ts_errno B HB). injection Heq as <- <-. exact Hca.
Qed.

(* the common case: the state's whole memory list as I *)
Lemma drv_arodata_mem : forall (rs : smem) E (H : word -> bool) m,
  cover_from 2000 (img_cells rs ++ Tfib_owned_static ++ [(TFIB_ERRNO, 4)]) 0x10000 YImgCellsB.B_SEG1_PAGE_HI = true ->
  cover_from 2000 (img_cells rs ++ Tfib_owned_static ++ [(TFIB_ERRNO, 4)]) TFIB_RELRO_LO TFIB_RELRO_HI = true ->
  mem_ok tfibsegs E (mrestrict H m) rs -> arodata_ok B (aview tfibsegs H m).
Proof. intros rs E H m C1 C2 HM. exact (drv_arodata_img rs rs E H m C1 C2 HM (fun r Hr => Hr)). Qed.
End a.
