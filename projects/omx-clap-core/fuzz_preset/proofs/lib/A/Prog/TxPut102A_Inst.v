(* fuzz_preset lib/A, the #102 re-walk of tx_put on image A': THE INSTANCE.
   The walk (TxPut102A_Base.v / TxPut102A_Top.v) is parametric over {PA : PAImg A_prog_listing}; this file binds it
   to the whole-program image PI_prog_A of lib/A/PAImg_prog.v (sha256 04074e99eb62; internal record) (listing lib/A/Listing_prog.v
   (sha256 62db5cdc9519; internal record), A' pin sha256 1be0f53d96cb9d6c), proves the image facts tp_img by
   computation, discharges the twin's named premise tp_live from the text's OWN iface_room_pos premise, and states
   the function's theorem: the ttx_put_specX.
   rule 24: proves function tx_put (reuse search: the internal file REWALK-102-PLAN.md section T3)
   tp_live (TxPutCall102.v; this walk's 14:3xZ report): the live-set bounds YGcfRoomLive's realloc keeps need.
   They follow from the text's iface_room_pos by counts_of_room_pos_ok / _rl, since 19:19Z in the
   image-free leaf lib/Spec/PresetRoomCounts.v 8a4dfa84e8be (moved there
   verbatim from lib/A/PresetCfnA.v (sha256 78e117e3837c; internal record)), so tp_live is closed here in one lemma. (They could not
   be built on the #102-pins base until the plain re-pin landed: lib/ZImage.v 9f6813318c43, lib/U/ZImage.v
   ff3aa7cf9e5e, lib/Reusable/YH02.v 7a3823f5e466, YH03.v 73819dfee58e, YI5c.v dd77e1845212, taken by path.)
   THE UNIT'S SYMBOL BINDING OF B, which the top supplies: ONE hypothesis TB : AF0m.TfibSyms B (lib/A/AF0m.v blob
   97f423adf6eb, the #102 A' AF0m, generated from ELF sha256 bff8519bbe3ea0e4; its code record
   Tfib_code is lib/A/AF0l.v blob dfca6bb1a8d7, the audited A' AF0l). Every image fact of B that tp_img needs is
   PROVED from TB in TxPut102A_Wit.v (tp_pal_of_tfib, tp_pst_of_tfib, tp_shvis_of_tfib), replacing the three named
   stand-ins pal_core / pal_pst_ok / img_shvis this file took until the code record was audited (owner 17:14Z).
   Numerals: none of its own. No ADDRESS (every address is pa_sigma / pa_val of PAImg_prog.v or a CfImg field). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP YP0d YP0c YC80 YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YImgTop YGcfAmx2.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00cf YG01cf YG0ncf YG0dcf YGcallcf YGcallMx YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PresetRoomCounts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
Img0 Listing_prog PAImg_prog PRH_Base PRH_Img PRH_FnTx CfImgA CfParamsPreset AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import
S1ImgA TxPutCall102 TxPut102A_Base TxPut102A_Top TxPut102A_S0 TxPut102A_End TxPut102A_Fit TxPut102A_Grow
TxPut102A_Wit.
(* the hull facts of tp_img at preset's CfParams: the budget at a run position and the realloc call's entry headroom *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetHullPay PresetDrvHeadroomA.
(* the image rows of the arodata bridge at image A' (the RELRO segment, errno apart, the non-writable read ranges) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfAroPresetA.
(* the cf laws, for AR_laws_x's field 25 at ARcfx *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0lawscf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section inst. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfImg_A.
#[local] Existing Instance CfParams_preset.
#[local] Instance TPI_PrhImg : PrhImg := prh_img_A.
#[local] Instance TPI_RL : PrhRoomLive := prh_room_live_a8.
#[local] Notation PA := PI_prog_A.
Variable B : asyms.
Variable SK : YI16.sink_head.
Variable CTX0 : list (list Z).

(* THE UNIT'S SYMBOL BINDING OF B, which the top supplies (FuzzStrdup.v:248's TB): every image fact of B below is
   proved from it in TxPut102A_Wit.v *)
Hypothesis TB : TfibSyms B.
(* __asan_memcpy's callee text with the memnorm keep (YGcallMxmn.aintrin_realizes_xm at OCpy, taken at the listing's
   own SIGMA AS___asan_memcpy; row po_asan_memcpy_cf of CfApiPreset.v) - the FIT row's one Section
   hypothesis *)
Hypothesis AI : aintrin_realizes_xm (@pa_segs _ A_prog_listing PA) B
  (fun ly S Hp W mem md => ARcf (@pa_segs _ A_prog_listing PA) B ly S Hp W mem md) OCpy
  (@pa_sigma _ A_prog_listing PA AS___asan_memcpy).
(* the realloc wrapper's callee texts (tp_AREAL: the cf layer's primed keep row with room,
   YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep at every headroom k; tp_AREALN:
   YGcfReallocComposeKeep.arealloc_null_realizes_cf_keep; TxPut102A_Base.v), named premises of the GROW row
   (TxPut102A_Base.tp_seg_GROW_stmt). They stay Section hypotheses here, but both are PROVED at image A', with no
   premise, at PI_prog_A's pa_segs: AllocAssembleA.arealloc_realizes_cf_A (lib/A/AllocAssembleA.v:58) and
   AllocAssembleA.arealloc_null_realizes_cf_A (:91); lib/A/Prog/ATxValueInst.v (:16) passes them to tx_put_holds_A
   at the crt instance *)
Hypothesis AREAL : tp_AREAL (PA := PA) B.
Hypothesis AREALN : tp_AREALN (PA := PA) B.

(* ARX_DEPOT, the depot of every ARcfx state has no repeats (the GROW row's admission of the call's WILD trace needs
   it, YCbqGwild.wild_room_admits): AR_laws_x's field 25 (YCbqG.v ARx_depot_nodup_law) at ARcfx, the projection
   alx_depot_nodup of the cf laws AR_laws_ok_cf at YGcallcf's bridge AR_laws_x_xs (as TxPut102A_Grow.v binds them) *)
Lemma tp_arx_depot_A : tp_ARX_DEPOT (PA := PA) B.
Proof.
exact (alx_depot_nodup _ _ _ (AR_laws_x_xs (@pa_segs _ A_prog_listing PA) B
  (YG0lawscf.AR_laws_ok_cf (@pa_segs _ A_prog_listing PA) B))).
Qed.

(* ---- the image facts: the PA / CfImg ones by computation, the B ones from TB (TxPut102A_Wit.v) ---- *)
Lemma tp_img_A : tp_img (PA := PA) B.
Proof.
constructor.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- exact (tp_pal_of_tfib (rc := rc) B TB).
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- exact pst_not_ro_A.
- exact pst_in_img_A.
- intros a Ha. exact (proj1 (tp_pst_of_tfib B TB a Ha)).
- intros a Ha. exact (proj2 (tp_pst_of_tfib B TB a Ha)).
- unfold prh_head_wide. vm_compute. discriminate.
- intros ly S Hp W mem md a HAR Ha. apply (tp_shvis_of_tfib (rc := rc) B TB ly S Hp W mem md a HAR).
  assert (Elo : @pa_lo _ _ PA = @cf_img_lo CfImg_A) by (vm_compute; reflexivity).
  assert (Ehi : @pa_hi _ _ PA = @cf_img_top CfImg_A) by (vm_compute; reflexivity).
  rewrite Elo, Ehi in Ha. exact Ha.
- (* tpi_hull_ok: the budget a run position of at most 4 calls leaves for the empty list *)
  intros sm x os i H0 hist S Hl HP.
  apply (PresetHullPay.hull_ok_of_budget S []).
  apply (PresetHullPay.hull_budget_of_room_pos sm x os i H0 hist S [] Hl HP); vm_compute; intros Hc; discriminate Hc.
- (* tpi_hull_adm: the realloc call's entry headroom at the run's HRe event *)
  exact (fun sm x os i H0 hist S m n Hl HP He =>
    PresetDrvHeadroomA.drv_cf_headroom_at_call_A sm x os i H0 hist S m n Hl HP He).
- (* tpi_relro_seg: the CfImg's RELRO range and each cf_ro_reads range lie in one segment of the image (the
     image row of lib/A/CfAroPresetA.v; the listing's segments are its tfibsegs) *)
  exact CfAroPresetA.relro_seg_preset_A.
- (* tpi_errno_relro: errno's four bytes (TfibSyms' ts_errno) are apart from the RELRO range and the cf_ro_reads
     ranges *)
  exact (CfAroPresetA.errno_relro_preset_A B TB).
- (* tpi_relro_bounds: the listing's RELRO bounds are the CfImg's, below 2 ^ 64 *)
  split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. cbv [cf_relro_hi CfImg_A]. lia.
- (* tpi_relro_pst: no program-written static lies in the RELRO range or in a cf_ro_reads range, decided over
     prh_pst *)
  intros a Ha HX. apply Exists_exists in HX as (r & Hin & Hr). unfold in_zr in Hr.
  destruct Ha as [Ha | Ha].
  + assert (Hb : forallb (fun r => ((fst r + snd r <=? @cf_relro_lo CfImg_A) || (@cf_relro_hi CfImg_A <=? fst r))%bool)
      prh_pst = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in Hb. specialize (Hb r Hin).
    apply orb_true_iff in Hb as [Hb | Hb]; apply Z.leb_le in Hb; lia.
  + apply Exists_exists in Ha as (q & Hq & Hqa). unfold in_zr in Hqa.
    assert (Hb : forallb (fun r => forallb (fun q => ((fst r + snd r <=? fst q) || (fst q + snd q <=? fst r))%bool)
      (@cf_ro_reads CfImg_A)) prh_pst = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in Hb. specialize (Hb r Hin). rewrite forallb_forall in Hb. specialize (Hb q Hq).
    apply orb_true_iff in Hb as [Hb | Hb]; apply Z.leb_le in Hb; lia.
- (* tpi_ro_reads_nw: each cf_ro_reads range lies in a non-writable segment, inside 2 ^ 64 (lib/A/CfAroPresetA.v) *)
  exact CfAroPresetA.ro_reads_nw_preset_A.
Qed.

(* ---- the twin's named premise, from the text's own run-position premise (counts_of_room_pos) ---- *)
Lemma tp_live_of_pos : forall rp_sm rp_x rp_os rp_i rp_H0 rp_hist S,
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S -> TxPutCall102.tp_live S.
Proof.
intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist S HP.
destruct (counts_of_room_pos_ok rp_sm rp_x rp_os rp_i rp_H0 rp_hist S HP) as [Hs Hb].
destruct (counts_of_room_pos_rl rp_sm rp_x rp_os rp_i rp_H0 rp_hist S HP) as [_ Hc].
split; [exact Hs|]. split; [exact Hb | lia].
Qed.

(* ---- THE FUNCTION'S THEOREM: the text ttx_put_specX at the instance (SRr' segs RZ_cf, the post's journal at
   wle' segs RZ_cf, the run-length premise length rp_os <= 4, which the twin threads to tp_pre's last conjunct), every
   row by its Qed lemma: S0 and END cross no call (their call keep is dropped), FIT is taken at the memcpy text AI,
   GROW at the realloc wrapper's texts AREAL / AREALN and ARX_DEPOT (tp_seg_GROW_stmt; ARX_DEPOT is
   tp_arx_depot_A). The kit's text has no live refused path (its refused arm is DEAD: the GROW row refutes the realloc's NULL), so there is no NULL
   row. tp_live from the text's own iface_room_pos. ---- *)
Theorem tx_put_holds_A : ttx_put_specX (PA := PA) B (ARcfx (PA := PA) B) SK CTX0.
Proof.
eapply TxPutCall102.ttx_put_specX_of_pos; [exact tp_live_of_pos|].
exact (tx_put_holds_ev (PA := PA) B SK CTX0
  (fun P HL _ => tp_seg_S0_holds (PA := PA) B SK CTX0 P HL)
  AREAL AREALN tp_arx_depot_A (tp_seg_GROW_holds (PA := PA) B SK CTX0)
  (tp_seg_FIT_holds (PA := PA) B SK CTX0 AI)
  (fun P HL _ => tp_seg_END_holds (PA := PA) B SK CTX0 P HL)
  tp_img_A).
Qed.

End inst.

Print Assumptions tx_put_holds_A.
