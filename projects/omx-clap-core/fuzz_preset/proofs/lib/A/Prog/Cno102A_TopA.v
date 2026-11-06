(* fuzz_preset, image A' (#102 pins: asan sha256 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4; binaries
   pau-preset-102): the cno A' top (Cno102A_Top.v, the kit cut 7cdbb61b5fa0's text) AT THE A' INSTANCE:
   PA := PI_prog_A, B := AD2l.TfibB (the #102 A' runtime symbol record), cp := CfParams_preset (fixed in Top.v). Row
   R7-5 (holder a Theorem Labs lane); the lead's rulings 17:46Z, 18:47Z, 20:58Z, 22:59Z and 10-30 06:40Z (re-state on the cut;
   compose when the cut's segment shas land).
   rule 24: no function proved. rule 24: proves no function (kind: instance corollary of the composition).
   ROUND 8 (the cut re-statement): Top.v carries its four stretches CA0_4 / CA5_9 / CA10 / CA11 as Section hypotheses
   until the cut's segment re-fits land, so the _inst corollaries below take them at the instance; the discharges of
   the cited lemmas' named arguments are proved here, ready for the composition (blobs in this tree):
     IMG    (cn_img TfibB at PI_prog_A), cn_img_A below, field by field:
              cni_base / cni_entry / cni_own / cni_pst_seg / cni_hi9: Cno102A_ImgA.v's witnesses;
              cni_pst_rw: S1ImgA.pst_not_ro_A, by conversion;
              cni_pst_ok: S1ImgA.pst_in_img_A + cn_A_pst_owned_b; cni_pst_errno: cn_A_pst_errno_b. The two checks
              are vm_compute on CLOSED goals over lib/A/AF0m.v Tfib_owned_static / TFIB_ERRNO (the fields of
              AD2l.TfibB) over prh_pst of lib/A/PRH_Img.v 934516a622e8 (seven cells);
     PAL    PALibA.palib_A; ENV PALibA.palib_errno_A;
     SYMS   (asyms_ok TfibB) AD2l.TfibB_ok, as proj1 AD2l.TfibB_pair;
     SM3    (pc_stack_malloc (as_code TfibB) CN_CID = pa_sigma PI_prog_A AS___asan_stack_malloc_3) cn_sm3_A below: a
              vm_compute on the CLOSED goal over lib/A/AF0l.v Tfib_code (TfibB's as_code) and PAImg_prog.A_prog_sigma,
              the instance statement by conversion;
     IMGSH  (the image shadow mapped in every ARcf state, over [pa_lo, pa_hi) of PI_prog_A) cn_imgsh_A below:
              lib/A/AImgShadowVisCf.v tfib_img_shadow_vis_cf at ci := CfImg_A (bounds = PI_prog_A's by conversion),
              its TfibSyms by AD2l.TfibB_pair;
     MEMSET (cn_R's MEMSET = cn_E's ASET) cn_memset_A_inst: Cno102A_Mset.cn_memset_A at ARcfx, AR_laws_x by
              AR_laws_x_xs (AR_laws_ok_cf), TfibSyms by AD2l.TfibB_pair;
     ACPY   (cn_E's __asan_memcpy row) cn_memcpy_A_inst: a Theorem Labs lane's PRowCpy.prow_asan_memcpy_xm_A at ARcfx, over
              tfibsegs (lib/A/AB1v.v) at pc_asan_memcpy (as_code TfibB): pa_segs / pa_sigma AS___asan_memcpy of
              PI_prog_A by conversion;
     ASM3   (cn_E's __asan_stack_malloc_3 row at class CN_CID) cn_asm3_A_inst: a Theorem Labs lane's
              FCxmCfx.stack_malloc3_contract_xm_cfx AD2l.TfibB (lib/A/FCxmCfx.v 09530d68c9b0, in the cut tree), TfibSyms
              by AD2l.TfibB_pair (owner's 01:11Z ruling; agreed 01:25Z to take it at this rebind);
    SS5M   (FE's __asan_set_shadow_f5 row) cn_ss5m_A_inst: FCxmCfx.set_shadow_f5_contract_xm_cfx, the same way;
    HSAME  (the kit's tsame_specX at DOC_D) a Theorem Labs lane's SameAp_inst.same_holds_Ap_HSAME_fit_s (A' same walk with its
              strcmp and bcmp rows discharged at the A' instance, a working branch e6023510cb8a).
  NOT DISCHARGED (premises the cited lemmas will add): AMALLOC (a Theorem Labs lane's malloc row), AFREE (a Theorem Labs lane), HRO /
    HPN / HPJFREE (the kit's texts; their walks). HTIE is gone: K0-PJF-TIE is CLOSED at the cut (Cno102A_F.v).
   This file Requires PAImg_prog.v, whose certificate checks the #102 A' bytes: it builds on the pins102 route only.
   NAME GUARD (a Theorem Labs lane 19:32Z): the short `Img0.rsegs` / `Img0` may resolve to the PLAIN lib.Img0, so the instance's
   listing, segments and sigma are FULLY QUALIFIED (IMG_*_A), and cn_topa_segs checks by reflexivity that pa_segs at
   PI_prog_A IS lib/A/Img0's rsegs.
   Numerals: 4 (LENGTH: errno's width, as cni_pst_errno spells it); 3 (the frame class, FCxmCfx's spelling of CN_CID).
   No ADDRESS typed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05 YI16 YCbq YGcfNames YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP09 YP08 YL0b YG00 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PRH_Base PRH_Img Img0 PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset AF0l AF0m AD2l AB1v PALibA PRowCpy
  CfImgA CfAroPresetA AImgShadowVisCf FCxmCfx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Cno102A_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1ImgA S1ImgCheck Cno102A_ImgA Cno102A_Mset Cno102A_Top
  SameAp_inst.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqG YG0ncf YGcallcf YG0lawscf YGcallMxmn YPsym.
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Open Scope Z_scope.

(* the #102 A' listing, segments, sigma and code record, FULLY QUALIFIED (never the plain lib/Img0.v / plain listing) *)
#[local] Notation IMG_SEGS_A := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs.
#[local] Notation IMG_LST_A := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Listing_prog.A_prog_listing.
#[local] Notation IMG_PI_A := (@OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PAImg_prog.PI_prog_A).
#[local] Notation IMG_SIGMA_A := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PAImg_prog.A_prog_sigma.
#[local] Notation IMG_CODE_A := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.AF0l.Tfib_code.
#[local] Notation IMG_TFIBSEGS_A := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.AB1v.tfibsegs.
#[local] Notation CP := CfParamsPreset.CfParams_preset.

(* ---- closed checks (vm_compute on closed goals only) ---- *)
Lemma cn_A_pst_owned_b :
  S1ImgCheck.pst_allb (fun a => negb (existsb (fun r : Z * Z => (fst r <=? a) && (a <? fst r + snd r))
                                    AF0m.Tfib_owned_static)) (@prh_pst prh_img_A) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cn_A_pst_errno_b :
  S1ImgCheck.pst_allb (fun a => negb ((AF0m.TFIB_ERRNO <=? a) && (a <? AF0m.TFIB_ERRNO + 4))) (@prh_pst prh_img_A) = true.
Proof. vm_compute. reflexivity. Qed.
(* the class-3 stack_malloc entry of TfibB's code is the listing's __asan_stack_malloc_3 *)
Lemma cn_A_sm3 : pc_stack_malloc IMG_CODE_A CN_CID = IMG_SIGMA_A AS___asan_stack_malloc_3.
Proof. vm_compute. reflexivity. Qed.
Lemma cn_not_in_zr_b : forall a (l : list (Z * Z)),
  existsb (fun r : Z * Z => (fst r <=? a) && (a <? fst r + snd r)) l = false -> ~ Exists (in_zr a) l.
Proof.
intros a l H HE. induction HE as [r t Hr | r t _ IH]; cbn [existsb] in H; apply orb_false_iff in H as [H1 H2].
- unfold in_zr in Hr. destruct Hr as [Hlo Hhi].
  rewrite (proj2 (Z.leb_le _ _) Hlo), (proj2 (Z.ltb_lt _ _) Hhi) in H1. discriminate H1.
- exact (IH H2).
Qed.

Section topA. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {SK : YI16.sink_head}.

(* THE GUARD: the instance's segments ARE lib/A/Img0's rsegs (the #102 A' image) *)
Lemma cn_topa_segs : @pa_segs rc IMG_LST_A (IMG_PI_A rc) = IMG_SEGS_A.
Proof. reflexivity. Qed.

(* IMG: the image record at the A' instance *)
Lemma cn_img_A : cn_img (rc := rc) (ci := CfImgA.CfImg_A) (PA := IMG_PI_A rc) AD2l.TfibB.
Proof.
constructor.
- exact Cno102A_ImgA.cn_img_A_base.
- exact Cno102A_ImgA.cn_img_A_entry.
- exact Cno102A_ImgA.cn_img_A_own.
- intros a Ha. exact (S1ImgA.pst_not_ro_A a Ha).
- exact Cno102A_ImgA.cn_img_A_pst_seg.
- intros a Ha. split; [exact (S1ImgA.pst_in_img_A a Ha)|].
  change (as_owned_static AD2l.TfibB) with AF0m.Tfib_owned_static.
  apply cn_not_in_zr_b.
  pose proof (S1ImgCheck.pst_allb_sound _ _ a cn_A_pst_owned_b Ha) as H. cbv beta in H.
  apply negb_true_iff in H. exact H.
- exact Cno102A_ImgA.cn_img_A_hi9.
- intros a Ha [Hl Hh].
  change (as_errno AD2l.TfibB) with AF0m.TFIB_ERRNO in Hl, Hh.
  pose proof (S1ImgCheck.pst_allb_sound _ _ a cn_A_pst_errno_b Ha) as H. cbv beta in H.
  rewrite (proj2 (Z.leb_le _ _) Hl), (proj2 (Z.ltb_lt _ _) Hh) in H. discriminate H.
- exact CfAroPresetA.relro_seg_preset_A.
- exact (CfAroPresetA.errno_relro_preset_A AD2l.TfibB (proj2 AD2l.TfibB_pair)).
- exact CfAroPresetA.relro_top_preset_A.
- split; vm_compute; reflexivity.
- exact CfAroPresetA.ro_reads_nw_preset_A.
Qed.

(* SM3 at the instance *)
Lemma cn_sm3_A : pc_stack_malloc (as_code AD2l.TfibB) CN_CID = @pa_sigma rc IMG_LST_A (IMG_PI_A rc) AS___asan_stack_malloc_3.
Proof. change (pc_stack_malloc IMG_CODE_A CN_CID = IMG_SIGMA_A AS___asan_stack_malloc_3). exact cn_A_sm3. Qed.

(* IMGSH at the instance: image A's shadow is mapped in every ARcf state (AImgShadowVisCf, at CfImg_A's bounds) *)
Lemma cn_imgsh_A : forall ly S Hp W mem md a,
  @ARcf rc CfImgA.CfImg_A CP (@pa_segs rc IMG_LST_A (IMG_PI_A rc)) AD2l.TfibB ly S Hp W mem md ->
  @pa_lo rc IMG_LST_A (IMG_PI_A rc) <= a < @pa_hi rc IMG_LST_A (IMG_PI_A rc) ->
  aview (@pa_segs rc IMG_LST_A (IMG_PI_A rc)) (w_H W) mem (shadow_addr a) <> None.
Proof.
intros ly S Hp W mem md a HAR Ha.
exact (AImgShadowVisCf.tfib_img_shadow_vis_cf (cp := CP) _ AD2l.TfibB (proj2 AD2l.TfibB_pair)
  ly S Hp W mem md a HAR Ha).
Qed.

(* MEMSET (= cn_E's ASET): the __asan_memset row at ARcfx (Cno102A_Mset.cn_memset_A) *)
Lemma cn_memset_A_inst : forall fz : YK11.FPState,
  aintrin_realizes_xm (fx := fz) (@pa_segs rc IMG_LST_A (IMG_PI_A rc)) AD2l.TfibB
    (fun ly S Hp W mem md =>
       @ARcf rc CfImgA.CfImg_A CP (@pa_segs rc IMG_LST_A (IMG_PI_A rc)) AD2l.TfibB ly S Hp W mem md /\
       @xs_placed_cf rc ly S)
    OSet (@pa_sigma rc IMG_LST_A (IMG_PI_A rc) AS___asan_memset).
Proof.
exact (Cno102A_Mset.cn_memset_A (rc := rc) (cp := CP) AD2l.TfibB _
  (AR_laws_x_xs (cp := CP) _ AD2l.TfibB (AR_laws_ok_cf (cp := CP) _ AD2l.TfibB))
  (proj2 AD2l.TfibB_pair)).
Qed.

(* ACPY: the __asan_memcpy row at ARcfx (PRowCpy.prow_asan_memcpy_xm_A) *)
Lemma cn_memcpy_A_inst : forall fz : YK11.FPState,
  aintrin_realizes_xm (fx := fz) (@pa_segs rc IMG_LST_A (IMG_PI_A rc)) AD2l.TfibB
    (fun ly S Hp W mem md =>
       @ARcf rc CfImgA.CfImg_A CP (@pa_segs rc IMG_LST_A (IMG_PI_A rc)) AD2l.TfibB ly S Hp W mem md /\
       @xs_placed_cf rc ly S)
    OCpy (@pa_sigma rc IMG_LST_A (IMG_PI_A rc) AS___asan_memcpy).
Proof.
intros fz.
change (@pa_sigma rc IMG_LST_A (IMG_PI_A rc) AS___asan_memcpy) with (pc_asan_memcpy (as_code AD2l.TfibB)).
change (@pa_segs rc IMG_LST_A (IMG_PI_A rc)) with IMG_TFIBSEGS_A.
exact (PRowCpy.prow_asan_memcpy_xm_A (fx := fz) AD2l.TfibB _ _
  (AR_laws_x_xs (cp := CP) IMG_TFIBSEGS_A AD2l.TfibB (AR_laws_ok_cf (cp := CP) IMG_TFIBSEGS_A AD2l.TfibB))
  (proj2 AD2l.TfibB_pair)).
Qed.

(* ASM3: the __asan_stack_malloc_3 row at ARcfx, class CN_CID (FCxmCfx.stack_malloc3_contract_xm_cfx) *)
Lemma cn_asm3_A_inst :
  astack_malloc_realizes_xm (fx := fx) (@pa_segs rc IMG_LST_A (IMG_PI_A rc)) AD2l.TfibB
    (fun ly S Hp W mem md =>
       @ARcf rc CfImgA.CfImg_A CP (@pa_segs rc IMG_LST_A (IMG_PI_A rc)) AD2l.TfibB ly S Hp W mem md /\
       @xs_placed_cf rc ly S)
    CN_CID.
Proof. exact (FCxmCfx.stack_malloc3_contract_xm_cfx (fx := fx) (cp := CP) AD2l.TfibB (proj2 AD2l.TfibB_pair)). Qed.

(* SS5M: the __asan_set_shadow_f5 row at ARcfx (FCxmCfx.set_shadow_f5_contract_xm_cfx) *)
Lemma cn_ss5m_A_inst : forall fz : YK11.FPState,
  @YGcallMxmn.aset_shadow_realizes_xm fz (@pa_segs rc IMG_LST_A (IMG_PI_A rc)) AD2l.TfibB
    (fun ly S Hp W mem md =>
       @ARcf rc CfImgA.CfImg_A CP (@pa_segs rc IMG_LST_A (IMG_PI_A rc)) AD2l.TfibB ly S Hp W mem md /\
       @xs_placed_cf rc ly S)
    (@pa_sigma rc IMG_LST_A (IMG_PI_A rc) AS___asan_set_shadow_f5) 245.
Proof. exact (FCxmCfx.set_shadow_f5_contract_xm_cfx (cp := CP) AD2l.TfibB (proj2 AD2l.TfibB_pair)). Qed.

(* HSAME at the instance: a Theorem Labs lane's premise-free fit of the A' same walk, at DOC_D *)
Definition cn_same_A_inst := fun (fz : YK11.FPState) =>
  @SameAp_inst.same_holds_Ap_HSAME_fit_s rc SK DOC_D fz.

(* the text at one record, at the A' instance (round 9: every stretch is cited in Top.v; what remains are the premises
   of other owners' rows and the kit's callee texts, each AT THE CALL'S OWN CTX0, a Theorem Labs lane 11:01Z) *)
Definition check_no_overread_walk_A_inst :=
  fun CTX0 AMALLOC AFREE HRO HPN HPJFREE =>
  @Cno102A_Top.check_no_overread_walk_A fx rc CfImgA.CfImg_A SK (IMG_PI_A rc) AD2l.TfibB CTX0
    cn_img_A PALibA.palib_A (proj1 AD2l.TfibB_pair) cn_sm3_A cn_imgsh_A AMALLOC cn_asm3_A_inst
    cn_memcpy_A_inst cn_memset_A_inst AFREE cn_ss5m_A_inst PALibA.palib_errno_A HRO cn_same_A_inst HPN HPJFREE.

(* The kit's text (the cut 7cdbb61b5fa0) at the A' instance: the same discharges *)
Definition check_no_overread_holds_A_inst :=
  fun CTX0 AMALLOC AFREE HRO HPN HPJFREE =>
  @Cno102A_Top.check_no_overread_holds_A fx rc CfImgA.CfImg_A SK (IMG_PI_A rc) AD2l.TfibB CTX0
    cn_img_A PALibA.palib_A (proj1 AD2l.TfibB_pair) cn_sm3_A cn_imgsh_A AMALLOC cn_asm3_A_inst
    cn_memcpy_A_inst cn_memset_A_inst AFREE cn_ss5m_A_inst PALibA.palib_errno_A HRO cn_same_A_inst HPN HPJFREE.
End topA.
