(* fuzz_preset lib/B, the #102 re-walk of tx_put on image B' (asan-ubsan pin d663f82d7f488d30): THE INSTANCE.
   Mirror of the A' walk's lib/A/Prog/TxPut102A_Inst.v (sha256 36bfc43c2fe9; internal record).
   The walk (TxPut102B_Base.v .. TxPut102B_All.v) is parametric over {PA : PAImg B_prog_listing}; this
   file binds it to the whole-program image PI_prog_B of lib/B/PAImg_prog.v (blob 15fab93fe702, listings v3),
   buildable on IMG_TOP_B (lib/Reusable/YImgTop.v
   blob d2a97d3111ce; no tx_put file cites YImgTop's bounds), with CfImg_B (lib/AU/CfImgB.v (sha256 de1ed50dae9d; internal record),
   core class, YGcfNames.v (sha256 352348a043fb; internal record)), and proves HHI and tp_img's image fields by computation.
   rule 24: proves function tx_put (reuse search: the internal file REWALK-102-PLAN.md section T3)
   THE IMAGE BINDING OF B: ONE `TB : TfibSyms B` (owner 17:1xZ: switch once the code record matches), from the B' YF0m.v
   (sha256 b9ab0e46c6c4; internal record) over the #102 YF0l 4a405a3dba65 / YImgCellsB f1cc7493a79d (17:14Z); tpi_pal,
   tpi_pst_owned / tpi_pst_errno and tpi_img_shvis are DERIVED from it by TxPut102B_Wit.v (tp_pal_of_tfib_B,
   tp_pst_of_tfib_B, tp_shvis_of_tfib_B). The code record was checked field by field against the B' listing's SIGMA
   (all EQUAL; the planted pc_wrap_malloc + 4 control FAILS), so TB and PALibCore are consistent here (the old-pin YF0l
   ac4053c456c9 gave +0xfc and would have refuted PALibCore).
   The callee texts AREAL / AREALN and AI are named Hypotheses, as on A'.
   ALL FOUR ROWS by their Qed lemmas (S0, END, FIT, GROW).
   Numerals: the two CfImg_B bounds (0x10000 / 0x601000, CfImgB.v :60-62) in the bounds bridge; no ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP YP0d YP0c YC80 YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfAmx2.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00cf YG01cf YG0ncf YG0dcf YGcallcf YGcallMx YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnTx CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB PLB102 TxPut102B_Base TxPut102B_All TxPut102B_Wit.
(* the hull facts of tp_img at preset's CfParams: the budget at a run position and the realloc call's entry headroom *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetHullPay.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetDrvHeadroomB.
(* the image rows of the call memory's RELRO fact at image B' (relro_seg_t / errno_relro_t / ro_reads_nw_t) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfAroPresetB.
(* the cf laws, whose field 25 gives ARX_DEPOT *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0lawscf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section inst. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfImg_B.
#[local] Existing Instance CfParams_preset.
#[local] Instance TPB_PrhImg : PrhImg := prh_img_B.
#[local] Instance TPB_RL : PrhRoomLive := prh_room_live_a8.
#[local] Notation PA := PI_prog_B.
#[local] Notation segs := (@pa_segs _ B_prog_listing PA).
Variable B : asyms.
Variable SK : YI16.sink_head.
Variable CTX0 : list (list Z).
(* THE IMAGE BINDING OF B: ONE TfibSyms B (the B' YF0m.v (sha256 b9ab0e46c6c4; internal record) over the #102 YF0l 4a405a3dba65 /
   YImgCellsB f1cc7493a79d); PALibCore, the statics' facts and the image shadow are DERIVED from it
   (TxPut102B_Wit.v). *)
Hypothesis TB : TfibSyms B.
(* the callee texts: the realloc wrapper's two (tp_AREAL: the cf layer's primed row with room and the memnorm keep,
   tp_AREALN: the null row with the keep, TxPut102B_Base.v) and __asan_memcpy's (AI, the runtime row aintrin_realizes_xm) *)
Hypothesis AREAL : tp_AREAL (PA := PA) B.
Hypothesis AREALN : tp_AREALN (PA := PA) B.
(* ARX_DEPOT, the depot of every ARcfx state has no repeats (the GROW row's admission of the call's WILD trace needs
   it, YCbqGwild.wild_room_admits): AR_laws_x's field 25 (YCbqG.v ARx_depot_nodup_law) at ARcfx, the projection
   alx_depot_nodup of the cf laws AR_laws_ok_cf at YGcallcf's bridge AR_laws_x_xs (as TxPut102B_GROW.v binds them) *)
Lemma tp_arx_depot_B : tp_ARX_DEPOT (PA := PA) B.
Proof. exact (alx_depot_nodup _ _ _ (AR_laws_x_xs segs B (YG0lawscf.AR_laws_ok_cf segs B))). Qed.
Hypothesis AI : aintrin_realizes_xm segs B (ARcfx (PA := PA) B) OCpy (@pa_sigma _ B_prog_listing PA AS___asan_memcpy).

(* ---- HHI and the image facts: the PA / CfImg ones by computation, the B ones from the stand-ins ---- *)
Lemma tp_hhi_B : @pa_hi _ B_prog_listing PA <= 2 ^ 40.
Proof. vm_compute. discriminate. Qed.

Lemma tp_img_B : tp_img (PA := PA) B.
Proof.
constructor.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- exact (tp_pal_of_tfib_B B TB).
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- exact pst_not_ro_B.
- exact pst_in_img_B.
- intros a Ha. exact (proj1 (tp_pst_of_tfib_B B TB a Ha)).
- intros a Ha. exact (proj2 (tp_pst_of_tfib_B B TB a Ha)).
- unfold prh_head_wide. vm_compute. intros H. discriminate H.
- exact (tp_shvis_of_tfib_B B TB).
- split; vm_compute; reflexivity.
- (* tpi_hull_ok: the budget a run position of at most 4 calls leaves for the empty list *)
  intros sm x os i H0 hist S Hl HP.
  apply (PresetHullPay.hull_ok_of_budget S []).
  apply (PresetHullPay.hull_budget_of_room_pos sm x os i H0 hist S [] Hl HP); vm_compute; intros Hc; discriminate Hc.
- (* tpi_hull_adm: the realloc call's entry headroom at the run's HRe event *)
  intros sm x os i H0 hist S m n Hl HP He.
  exact (PresetDrvHeadroomB.drv_cf_headroom_at_call_B sm x os i H0 hist S m n Hl HP He).
- (* tpi_relro_seg: the CfImg's RELRO range and each cf_ro_reads range lie in one segment of the image (rsegs is
     YB1v.tfibsegs) *)
  exact CfAroPresetB.relro_seg_preset_AU.
- (* tpi_errno_relro: errno's four bytes (TfibSyms' ts_errno) are apart from the RELRO range and each cf_ro_reads
     range *)
  exact (CfAroPresetB.errno_relro_preset_AU B TB).
- (* tpi_relro_bounds: the listing's RELRO bounds are the CfImg's, below 2 ^ 64 *)
  split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. exact CfAroPresetB.relro_top_preset_AU.
- (* tpi_relro_pst: no program-written static lies at an aro_addr_cf address (the RELRO range, a cf_ro_reads range),
     decided over prh_pst *)
  intros a Ha HX. apply Exists_exists in HX as (r & Hin & Hr). unfold in_zr in Hr.
  destruct Ha as [Ha | Ha].
  + assert (Hb : forallb (fun r => ((fst r + snd r <=? @cf_relro_lo CfImg_B) || (@cf_relro_hi CfImg_B <=? fst r))%bool)
      prh_pst = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in Hb. specialize (Hb r Hin).
    apply orb_true_iff in Hb as [Hb | Hb]; apply Z.leb_le in Hb; lia.
  + apply Exists_exists in Ha as (r' & Hin' & Hr'). unfold in_zr in Hr'.
    assert (Hb : forallb (fun r => forallb (fun r' => ((fst r + snd r <=? fst r') || (fst r' + snd r' <=? fst r))%bool)
      (@cf_ro_reads CfImg_B)) prh_pst = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in Hb. specialize (Hb r Hin). rewrite forallb_forall in Hb. specialize (Hb r' Hin').
    apply orb_true_iff in Hb as [Hb | Hb]; apply Z.leb_le in Hb; lia.
- (* tpi_ro_reads_nw: each cf_ro_reads range lies in a non-writable segment, inside 2 ^ 64 *)
  exact CfAroPresetB.ro_reads_nw_preset_AU.
Qed.

(* ---- THE FUNCTION'S THEOREM at the instance: the kit's ttx_put_specX (PRH_FnTx.v 88468bf162d8, the batch kit
   c23331281d07), every row by its Qed lemma (TxPut102B_All.tx_put_holds_B_rows; no NULL row: the batch kit's text has no
   refused path) ---- *)
Theorem tx_put_holds_B_inst : ttx_put_specX (PA := PA) B (ARcfx (PA := PA) B) SK CTX0.
Proof. exact (tx_put_holds_B_rows (PA := PA) B SK CTX0 tp_hhi_B tp_img_B AREAL AREALN tp_arx_depot_B AI). Qed.

End inst.
Print Assumptions tx_put_holds_B_inst.
