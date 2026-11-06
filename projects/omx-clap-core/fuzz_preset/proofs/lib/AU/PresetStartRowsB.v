(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-31: the three start-up rows of the B driver walk
   (lib/AU/PresetD1pB.v section 4), PROVED in their exact statements at the asan-ubsan image of #102 (pin d663f82d)
   from the B start-up table (lib/Reusable/YB01.v, the 50 hand-off states HS_tfib) and the image's CfImg_B
   (lib/AU/CfImgB.v). rule 24: no function proved (kind: start-up facts).
   - start_lazy_B (H_start_lazy_B): ARcf's alc_lazy_in_maps at main, from cs_ok's co_nasub and co_lzsub (field of
     YA0e.v, proved at init in YA02.v, kept by YA08.v / YA09.v) by YCsokLazyMaps.cs_ok_lazy_in_maps_cf. Its statement
     and proof are fuzz_reply's token for token in its YCsokLazyMaps.v (sha256 ccbc12c58fbc; internal record) :16-25.
   - start_cells_B (H_start_cells_B): the start witness YG0ncf.start_cells_cf at the start-up world W1. The 31
     exhausted bytes RegionInfo + 128 c + cf_exh_off lie in [RegionInfo, + 4096), which every hand-off state knows
     zero (a KZero entry); the errbuf object's 56 bytes [cf_errbuf_obj, + 56) lie in .bss inside a KImg range, so
     every hand-off state knows them zero (kn_zcover TFIB_BSS; YB13.tfib_bss_rom). YGcfInstBase.exh_cell_cf_init /
     errb_cells_cf_init put the zero cells in the layer's form (the draft's YG0ncf.v:129-145 definitions).
   - start_pf_B (H_start_pf_B): YG0ncf.start_pf_cf at W1. Every hand-off state holds the two 8-byte words
     __asan::AsanInitInternal stores: cf_toolname_cell = 0xa4718 holds cf_toolname_val = 0x20449 and
     cf_pfcb_cell = 0x13d410 holds cf_pfcb_val = 0x55df8 (YB01.v's KWord entries at 673560 and 1299472, the facts
     lib/AU/PresetImg_su_tool.v su_tool_cell_B and lib/AU/PresetImg_su_printf.v presetB_su_printf_handoff read).
   Each hand-off fact is read by YD1g's checkers (xzero / xcell, sound by YD1g.xzero_sound / xcell_sound from Hch and
   HC alone) and checked at all 50 hand-off states by vm_compute (start_chk_all). It holds in the hand-off's reader
   (hreader of Mr = aview of hid), so in aview of every world W' above W1: W' hides less than W1's H1, and H1 less
   than hid (start_rd_ext, by YG0n.aview_ext). The rows' binders carry no Hve / Hfit / HE / HM / Hceil, so the route
   through YD1f.tfib_AR (AR at W1) is not open.
   PORTED (reuse search: ossv-find, 2026-10-31; no released donor): the cells route is not new. It is the route of
   BD2iExhErrb.v (sha256 74de721716dd; internal record): hs_cells_B :34-35, rd_ext_W :64-71, main_cells_zero_B
   :73-83, a file not in this tree, here taken onto this tree's YG0ncf.v field definitions instead of the CasanR2
   copy in an earlier YGcfCellsInit.v (sha256 cbee65370778; internal record) :32-54, whose bodies equal
   YG0ncf.v:129-145 token for token once ly is a parameter; the same route reads the pf cells by xcell.
   fuzz_reply's twin is start_cells_B in ReplyStartWitB.v (sha256 c3b8a02c5aa4; internal record) :21-32. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YP09 YK00 YK04 YA0i YA0n YK0g YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j
YB12 YB1h YB13 YB01 YB1v YG00 YG01 YG0f YG0v YG0n YF0m YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG0ncf YGcfInstBase YCsokLazyMaps.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0r YG0scf YD1g YD2i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetD1pB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Open Scope Z_scope.

#[local] Existing Instance YK11.fx0.
#[local] Existing Instance CfImg_B.

(* ---------------------------------------------------------------------- *)
(* 1. The lazy row: lazy_in_maps at every cs_ok state, so at the hand-off. *)
Theorem start_lazy_B : PresetD1pB.H_start_lazy_B.
Proof.
intros sp rdraw brk inp h ch E R FULL model Hch HC x Hx.
exact (cs_ok_lazy_in_maps_cf _ _ _ _ _ _ _ _ _ _ _ _ HC x Hx).
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. The hand-off's reader, extended to every world above W1. *)
Lemma rz_ext' : forall (B : asyms) (ly : alayout) (rd rd' : reader) (r : aexp * Z),
  rd_ext rd rd' -> range_zero B ly rd r -> range_zero B ly rd' r.
Proof. intros B ly rd rd' r X H i Hi. apply X. apply H. exact Hi. Qed.

Lemma start_rd_ext : forall {rc : YM05.RunCeil} (sp : word) (rdraw : EntryDraw) (inp : ProcInput)
  (Hsp : valid_sp sp) (Hva : valid_argv (in_argv inp)) (ch : acs) (E : env) (model : Model) (FULL : word -> option byte)
  (H1_8 : forall a : Z, YG0f.in_band_rw a ->
    YD2i.H1 sp rdraw inp ch E model (Z_to_bv 64 a) = YD2i.H1 sp rdraw inp ch E model (Z_to_bv 64 (a - a mod 8)))
  (W' : world TSEGS),
  wle (YD2i.W1 sp rdraw inp Hsp Hva ch E model H1_8) W' ->
  rd_ext (hreader TSEGS (Mr TFIB (YA02.TOP sp) (YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
            E ch model FULL))
    (aview TSEGS (w_H W') FULL).
Proof.
intros rc sp rdraw inp Hsp Hva ch E model FULL H1_8 W' HW.
change (hreader TSEGS (Mr TFIB (YA02.TOP sp) (YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
          E ch model FULL))
  with (aview TSEGS (hid TFIB (YA02.TOP sp) (YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
          E ch model) FULL).
apply aview_ext.
- exact (ho_H_off TSEGS TFIB (YA02.TOP sp) (YA02.argH0 TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
    tfib_in_hull (YA02.top_ok0 sp Hsp) tfib_hull_ok
    (YA02.argH0_high TPH sp rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) Hsp Hva) E ch model).
- intros a Ha. pose proof (HW a Ha) as Hb. cbn [YD2i.W1 w_H] in Hb. unfold YD2i.H1 in Hb.
  apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. exact Hb.
Qed.

(* ---------------------------------------------------------------------- *)
(* 3. The start-up table's facts, checked at all 50 hand-off states (YB01.v). *)
Definition start_chk (ch0 : acs) : bool :=
  (YD1g.xzero ch0 (ASp kRegionInfoOff, 4096)
   && YD1g.xzero ch0 (ANum (@cf_errbuf_obj CfImg_B), 56)
   && YD1g.xcell ch0 (z8 (ANum (@cf_toolname_cell CfImg_B)) (@cf_toolname_val CfImg_B))
   && YD1g.xcell ch0 (z8 (ANum (@cf_pfcb_cell CfImg_B)) (@cf_pfcb_val CfImg_B)))%bool.

Lemma start_chk_all : forallb start_chk HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.

Lemma start_chk_at : forall (h : nat) (ch : acs), HS_tfib h = Some ch -> start_chk ch = true.
Proof. intros h ch H. exact (proj1 (forallb_forall _ _) start_chk_all ch (HS_tfib_In h ch H)). Qed.

(* YD1g's Section a0 lemmas at the rows' binders, whichever of them each lemma takes (YD1f.v's inst). *)
Ltac inst H B HB sp rdraw brk inp Hsp Hva h ch E R FULL model Hch HC rc :=
  try specialize (H YK11.fx0); try specialize (H B); try specialize (H HB); try specialize (H sp);
  try specialize (H rdraw); try specialize (H brk); try specialize (H inp); try specialize (H Hsp);
  try specialize (H Hva); try specialize (H h); try specialize (H ch); try specialize (H E); try specialize (H R);
  try specialize (H FULL); try specialize (H model); try specialize (H Hch); try specialize (H HC);
  try specialize (H rc).

(* ---------------------------------------------------------------------- *)
(* 4. The cells row: the 31 exhausted bytes and the errbuf object's five cells read 0 at every world above W1. *)
Theorem start_cells_B : PresetD1pB.H_start_cells_B.
Proof.
intros rc sp rdraw brk inp Hsp Hva h ch E R FULL model Hch HC H1_8 B HB W' HW.
pose proof (@start_rd_ext rc sp rdraw inp Hsp Hva ch E model FULL H1_8 W' HW) as X.
pose proof (start_chk_at h ch Hch) as C. unfold start_chk in C.
apply andb_prop in C as [C _]. apply andb_prop in C as [C _]. apply andb_prop in C as [CR CE].
pose proof (@YD1g.xzero_sound) as ZS. inst ZS B HB sp rdraw brk inp Hsp Hva h ch E R FULL model Hch HC rc.
unfold YD1g.rd in ZS.
pose proof (rz_ext' _ _ _ _ _ X (ZS _ CR)) as ZR.
pose proof (rz_ext' _ _ _ _ _ X (ZS _ CE)) as ZE.
split.
- apply exh_cell_cf_init. intros c Hc. unfold z1, c1.
  pose proof (eq_refl : @cf_exh_off CfImg_B = 68) as EO.
  apply (YG0r.cell_zero_of_range B _ _ (ASp kRegionInfoOff) 4096); [exact ZR | cbn [aoff aeval]; lia | cbn [aoff aeval]; lia].
- apply errb_cells_cf_init; unfold z8, c8;
    (apply (YG0r.cell_zero_of_range B _ _ (ANum (@cf_errbuf_obj CfImg_B)) 56);
      [exact ZE | cbn [aeval]; lia | cbn [aeval]; lia]).
Qed.

(* ---------------------------------------------------------------------- *)
(* 5. The pf row: Printf's two image cells hold their start-up values at every world above W1. *)
Theorem start_pf_B : PresetD1pB.H_start_pf_B.
Proof.
intros rc sp rdraw brk inp Hsp Hva h ch E R FULL model Hch HC H1_8 B HB W' HW.
pose proof (@start_rd_ext rc sp rdraw inp Hsp Hva ch E model FULL H1_8 W' HW) as X.
pose proof (start_chk_at h ch Hch) as C. unfold start_chk in C.
apply andb_prop in C as [C CP]. apply andb_prop in C as [_ CT].
pose proof (@YD1g.xcell_sound) as CS. inst CS B HB sp rdraw brk inp Hsp Hva h ch E R FULL model Hch HC rc.
unfold YD1g.rd in CS.
eapply YG0scf.pf_cells_cf_ext; [exact X |].
exact (conj (CS _ CT) (CS _ CP)).
Qed.
