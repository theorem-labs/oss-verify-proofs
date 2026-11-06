(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30: fuzz_preset's two IAL rows of the cf instance (field round 3, YG0ncf.v), at both images.
   PER-UNIT file, not in the shared set.
   - errb_ial_apart_t: the errbuf object [cf_errbuf_obj, + 56) is apart from the internal allocator's arena
     [as_ialloc_lo B, as_ialloc_hi B) and its 4-byte flag (amc_cells_owned's third conjunct).
   - pf_ial_apart_t: the same for Printf's two cells, the tool-name pointer and the callback cell (pf_cells_owned_t's
     second conjunct; in the layer since commit d0377850faab).
   Values, from the generated facts (no raw dump):
   - A' (CfImg_A, lib/A/CfImgA.v:34 / :74 / :78; TfibSyms lib/A/AF0m.v:16-17, fields :1798 / :1799 / :1801):
     errbuf 0xaa728 + 56 = 0xaa760 and toolname 0xa3ed8 + 8 = 0xa3ee0, both below IAL_LO 0xac0c0; pfcb 0x13cbd0 above
     IAL_HI 0x12d0f0 and above the flag's last byte 0x13a94b.
   - B' (CfImg_B, lib/AU/CfImgB.v:34 / :74 / :78; TfibSyms lib/Reusable/YF0m.v:17-18, fields :1803 / :1804 / :1806):
     errbuf 0xaaf68 + 56 = 0xaafa0 and toolname 0xa4718 + 8 = 0xa4720, both below 0xac900; pfcb 0x13d410 above
     0x12d930 and above the flag's last byte 0x13b18b.
   - pf_cells_apart_t (YG0ncf.v, layer 5034424e29db; not an ARmcf field): every toolname / pfcb cell byte is below
     as_store B, is not as_oom_byte B and is outside the errbuf object. A': cells 0xa3ed8 / 0x13cbd0 (+8) vs STORE
     0x17cd88 (AF0m.v:15), OOM 0x12d120 (:17), errbuf [0xaa728, +56); B': 0xa4718 / 0x13d410 vs 0x17d5c8 (YF0m.v:16),
     0x12d960 (:18), [0xaaf68, +56) (the same numbers are checked by lia in the layer; the cgif model proof is
     YGcfImgcgif.pf_cells_apart_cgif).
   The IAL rows are premises of the fresh builder YGcfNilInit.ARcf_nil_init; this file is where a unit's driver takes
   them; pf_cells_apart_t is where the walks' PF_APART / PF_SEP / PF_AG premises project from. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0f YGcfNames YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AF0m CfImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YF0m YG0n YGcfImgRows.
Local Open Scope Z_scope.

Section A.
Lemma errb_ial_apart_A : forall B, AF0m.TfibSyms B -> errb_ial_apart_t (ci := CfImgA.CfImg_A) B.
Proof.
intros B TB a Ha. rewrite (AF0m.ts_ial_lo _ TB), (AF0m.ts_ial_hi _ TB), (AF0m.ts_ial_flag _ TB).
cbn [cf_errbuf_obj CfImgA.CfImg_A] in Ha. unfold AF0m.TFIB_IAL_LO, AF0m.TFIB_IAL_HI, AF0m.TFIB_IAL_FLAG. lia.
Qed.

Lemma pf_ial_apart_A : forall B, AF0m.TfibSyms B -> pf_ial_apart_t (ci := CfImgA.CfImg_A) B.
Proof.
intros B TB a Ha. rewrite (AF0m.ts_ial_lo _ TB), (AF0m.ts_ial_hi _ TB), (AF0m.ts_ial_flag _ TB).
cbn [cf_toolname_cell cf_pfcb_cell CfImgA.CfImg_A] in Ha. unfold AF0m.TFIB_IAL_LO, AF0m.TFIB_IAL_HI, AF0m.TFIB_IAL_FLAG. lia.
Qed.

Lemma pf_cells_apart_A : forall B, AF0m.TfibSyms B -> pf_cells_apart_t (ci := CfImgA.CfImg_A) B.
Proof.
intros B TB a Ha. rewrite (AF0m.ts_store _ TB), (AF0m.ts_oom _ TB).
cbn [cf_toolname_cell cf_pfcb_cell cf_errbuf_obj CfImgA.CfImg_A] in Ha |- *. unfold AF0m.TFIB_STORE, AF0m.TFIB_OOM. lia.
Qed.

(* The start-up builder's image rows (YGcfNilInit.ARcf_nil_init): the exhausted byte's offset, the errbuf object's
   ownership, and Printf's two cells' ownership apart from the allocator instance. Owned rows of Tfib_owned_static
   (AF0m.v:1784): row 0 [0xa3d20, +0x2878) holds the toolname cell 0xa3ed8; row 3 [0xaa710, +0x522e00) holds the
   errbuf object [0xaa728, +56) and the pfcb cell 0x13cbd0. The instance is [0xa7858, +3632) (AF0m.v:14). *)
Lemma exh_off_A : YGcfImgRows.EXH_OFF_t (ci := CfImgA.CfImg_A).
Proof. reflexivity. Qed.

Lemma errb_obj_owned_A : forall B, AF0m.TfibSyms B -> errb_obj_owned_t (ci := CfImgA.CfImg_A) B.
Proof.
intros B TB a Ha. rewrite (AF0m.ts_owned _ TB). cbn [cf_errbuf_obj CfImgA.CfImg_A] in Ha.
apply Exists_exists. exists (0xaa710, 0x522e00). split.
- unfold AF0m.Tfib_owned_static. do 3 right. left. reflexivity.
- unfold YG0n.in_zr. cbn [fst snd]. lia.
Qed.

Lemma pf_cells_static_A : forall B, AF0m.TfibSyms B -> pf_cells_static_t (ci := CfImgA.CfImg_A) B.
Proof.
intros B TB a Ha. rewrite (AF0m.ts_owned _ TB), (AF0m.ts_inst _ TB).
cbn [cf_toolname_cell cf_pfcb_cell CfImgA.CfImg_A] in Ha. unfold AF0m.TFIB_INST, kInstObjSize.
destruct Ha as [Ha | Ha]; split.
- apply Exists_exists. exists (0xa3d20, 0x2878). split.
  + unfold AF0m.Tfib_owned_static. left. reflexivity.
  + unfold YG0n.in_zr. cbn [fst snd]. lia.
- lia.
- apply Exists_exists. exists (0xaa710, 0x522e00). split.
  + unfold AF0m.Tfib_owned_static. do 3 right. left. reflexivity.
  + unfold YG0n.in_zr. cbn [fst snd]. lia.
- lia.
Qed.

Lemma pf_cells_owned_A : forall B, AF0m.TfibSyms B -> pf_cells_owned_t (ci := CfImgA.CfImg_A) B.
Proof. intros B TB. exact (conj (pf_cells_static_A B TB) (pf_ial_apart_A B TB)). Qed.
End A.

Section B.
Lemma errb_ial_apart_B : forall B, YF0m.TfibSyms B -> errb_ial_apart_t (ci := CfImgB.CfImg_B) B.
Proof.
intros B TB a Ha. rewrite (YF0m.ts_ial_lo _ TB), (YF0m.ts_ial_hi _ TB), (YF0m.ts_ial_flag _ TB).
cbn [cf_errbuf_obj CfImgB.CfImg_B] in Ha. unfold YF0m.TFIB_IAL_LO, YF0m.TFIB_IAL_HI, YF0m.TFIB_IAL_FLAG. lia.
Qed.

Lemma pf_ial_apart_B : forall B, YF0m.TfibSyms B -> pf_ial_apart_t (ci := CfImgB.CfImg_B) B.
Proof.
intros B TB a Ha. rewrite (YF0m.ts_ial_lo _ TB), (YF0m.ts_ial_hi _ TB), (YF0m.ts_ial_flag _ TB).
cbn [cf_toolname_cell cf_pfcb_cell CfImgB.CfImg_B] in Ha. unfold YF0m.TFIB_IAL_LO, YF0m.TFIB_IAL_HI, YF0m.TFIB_IAL_FLAG. lia.
Qed.

Lemma pf_cells_apart_B : forall B, YF0m.TfibSyms B -> pf_cells_apart_t (ci := CfImgB.CfImg_B) B.
Proof.
intros B TB a Ha. rewrite (YF0m.ts_store _ TB), (YF0m.ts_oom _ TB).
cbn [cf_toolname_cell cf_pfcb_cell cf_errbuf_obj CfImgB.CfImg_B] in Ha |- *. unfold YF0m.TFIB_STORE, YF0m.TFIB_OOM. lia.
Qed.

(* The same four rows at B': Tfib_owned_static (YF0m.v) row 0 [0xa4560, +0x2878) holds the toolname cell 0xa4718;
   row 3 [0xaaf50, +0x522e00) holds the errbuf object [0xaaf68, +56) and the pfcb cell 0x13d410. The instance is
   [0xa8098, +3632). *)
Lemma exh_off_B : YGcfImgRows.EXH_OFF_t (ci := CfImgB.CfImg_B).
Proof. reflexivity. Qed.

Lemma errb_obj_owned_B : forall B, YF0m.TfibSyms B -> errb_obj_owned_t (ci := CfImgB.CfImg_B) B.
Proof.
intros B TB a Ha. rewrite (YF0m.ts_owned _ TB). cbn [cf_errbuf_obj CfImgB.CfImg_B] in Ha.
apply Exists_exists. exists (0xaaf50, 0x522e00). split.
- unfold YF0m.Tfib_owned_static. do 3 right. left. reflexivity.
- unfold YG0n.in_zr. cbn [fst snd]. lia.
Qed.

Lemma pf_cells_static_B : forall B, YF0m.TfibSyms B -> pf_cells_static_t (ci := CfImgB.CfImg_B) B.
Proof.
intros B TB a Ha. rewrite (YF0m.ts_owned _ TB), (YF0m.ts_inst _ TB).
cbn [cf_toolname_cell cf_pfcb_cell CfImgB.CfImg_B] in Ha. unfold YF0m.TFIB_INST, kInstObjSize.
destruct Ha as [Ha | Ha]; split.
- apply Exists_exists. exists (0xa4560, 0x2878). split.
  + unfold YF0m.Tfib_owned_static. left. reflexivity.
  + unfold YG0n.in_zr. cbn [fst snd]. lia.
- lia.
- apply Exists_exists. exists (0xaaf50, 0x522e00). split.
  + unfold YF0m.Tfib_owned_static. do 3 right. left. reflexivity.
  + unfold YG0n.in_zr. cbn [fst snd]. lia.
- lia.
Qed.

Lemma pf_cells_owned_B : forall B, YF0m.TfibSyms B -> pf_cells_owned_t (ci := CfImgB.CfImg_B) B.
Proof. intros B TB. exact (conj (pf_cells_static_B B TB) (pf_ial_apart_B B TB)). Qed.
End B.

Print Assumptions exh_off_A.
Print Assumptions errb_obj_owned_A.
Print Assumptions pf_cells_static_A.
Print Assumptions pf_cells_owned_A.
Print Assumptions exh_off_B.
Print Assumptions errb_obj_owned_B.
Print Assumptions pf_cells_static_B.
Print Assumptions pf_cells_owned_B.
