(* fuzz_preset image A, slice S6 (WalkS6): the INSTANCE WITNESSES of the S6 walks' image premises (owner 16:45Z: every
   Section hypothesis that asserts a fact about the image has a lemma closed by vm_compute at the real instance beside
   it). Each lemma below is the Section hypothesis's text, verbatim, at PA := PI_prog_A (lib/A/PAImg_prog.v), B :=
   AD2l.TfibB where the text names B:
     Hent (S6PjGet.v, S6PjGetStr.v, S6PjString.v, S6PjFreeEnt.v)    s6w_ent_pj_get / _pj_get_str / _pj_string / _pj_free
     Hobj (the same files, S6PjFree.v)                                s6w_obj
     PAB (S6PjGet.v, S6PjGetStr.v, S6PjString.v, S6PjFreeEnt.v)       s6w_pab
     pal_pst_img (S6PjString.v, S6PjFreeEnt.v)                        s6w_pst_img (S1ImgA.v pst_in_img_A)
     pal_pst_ro (S6PjFreeKeep.v)                                      s6w_pst_ro (S1ImgA.v pst_not_ro_A)
     pal_ret_free (pj_free's segment files)                           s6w_ret_free
     pal_lit (S6PjString.v)                                           S6PalLitRefute.v pal_lit_A
     AIM (S6PjFreeTail.v, S6PjFreeTop.v, S6PjString.v; the A' memset row)  s6w_aim, by citation of c-libc-stdio's
                                                                      PRowSet.v prow_asan_memset_xm_A_lit (lib/A/PRow*
                                                                      set from origin/cold/c-libc-stdio-rows102
                                                                      599a4cefc740), under that lemma's own premises
   Not here, other hands' witnesses: TL : PALib B (lib/A/PALibA.v palib_A), LAWS (palib_laws_A, same file; 88c72c8175cf
   on the kit's cut 7cdbb61b5fa0). Not image facts (no witness asked): the callee texts (ASCR, STRDUP, FREE), the allocator facts VISF and
   pal_lit_sh (STATE claims on every allocator state).
   Every goal is closed: vm_compute only after the instance projections are reduced (no Section variable, no abstract
   model term). rule 24: proves no function (kind: image-premise witnesses). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YCbqGcallW YC80xf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YC80xf_inv YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnReader PRH_FnAlloc PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger PRW_StepKit S6PjCommon.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PjStringCommon.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1ImgA S1ImgCheck S6PjGet S6PjGetStr S6PjString S6PjFree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AF0m AB1v PRowSet.
Import ListNotations.
Local Open Scope Z_scope.


Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* GUARD (h-rw-pre-5 18:3xZ, CrcBp's wrong-image trap: a short `Img0.rsegs` resolves to the PLAIN image's lib/Img0.v in a
   closure that loads it): the segments this file computes over are written fully qualified, and they are the ones the
   walks use at the instance (PI_prog_A's pa_segs), by reflexivity *)
Lemma s6w_segs_A : @pa_segs _ A_prog_listing PI_prog_A = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs.
Proof. reflexivity. Qed.


(* Hent: the entries (DERIVED: slot * 4) *)
Lemma s6w_ent_pj_get :
  @pa_sigma _ A_prog_listing PI_prog_A AS_pj_get = @pa_val _ A_prog_listing PI_prog_A A_TEXT + S6PjGet.AF_pg.
Proof. cbn [pa_sigma pa_val PI_prog_A]. unfold S6PjGet.AF_pg. vm_compute. reflexivity. Qed.
Lemma s6w_ent_pj_get_str :
  @pa_sigma _ A_prog_listing PI_prog_A AS_pj_get_str = @pa_val _ A_prog_listing PI_prog_A A_TEXT + S6PjGetStr.AF_gs.
Proof. cbn [pa_sigma pa_val PI_prog_A]. unfold S6PjGetStr.AF_gs. vm_compute. reflexivity. Qed.
Lemma s6w_ent_pj_string :
  @pa_sigma _ A_prog_listing PI_prog_A AS_pj_string = @pa_val _ A_prog_listing PI_prog_A A_TEXT + S6PjString.AF_ps.
Proof. cbn [pa_sigma pa_val PI_prog_A]. unfold S6PjString.AF_ps. vm_compute. reflexivity. Qed.
Lemma s6w_ent_pj_free :
  @pa_sigma _ A_prog_listing PI_prog_A AS_pj_free = @pa_val _ A_prog_listing PI_prog_A A_TEXT + S6PjFree.AF_pf.
Proof. cbn [pa_sigma pa_val PI_prog_A]. unfold S6PjFree.AF_pf. vm_compute. reflexivity. Qed.

(* Hobj: the GOT word of the shadow base and the shadow cell lie in the image *)
Lemma s6w_obj : forall i, 0 <= i < 8 ->
  in_img (@pa_segs _ A_prog_listing PI_prog_A) (@pa_val _ A_prog_listing PI_prog_A (A_OBJ 0) + i) /\
  in_img (@pa_segs _ A_prog_listing PI_prog_A) (@pa_val _ A_prog_listing PI_prog_A (A_OBJ 12) + i).
Proof.
cbn [pa_segs pa_val PI_prog_A].
assert (Hb : forallb (fun i => S1ImgCheck.in_img_b OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs (A_prog_val (A_OBJ 0) + i) &&
                               S1ImgCheck.in_img_b OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs (A_prog_val (A_OBJ 12) + i)) [0; 1; 2; 3; 4; 5; 6; 7] = true)
  by (vm_compute; reflexivity).
intros i Hi. rewrite forallb_forall in Hb.
assert (Hin : In i [0; 1; 2; 3; 4; 5; 6; 7]) by (cbn [In]; lia).
specialize (Hb i Hin). apply andb_prop in Hb as [H1 H2].
split; [exact (S1ImgCheck.in_img_b_sound _ _ H1) | exact (S1ImgCheck.in_img_b_sound _ _ H2)].
Qed.

(* PAB: the image starts at YImgTop.IMG_LO *)
Lemma s6w_pab : @pa_lo _ A_prog_listing PI_prog_A = IMG_LO.
Proof. reflexivity. Qed.

(* pal_pst_img / pal_pst_ro: alloc.c's statics are image bytes and no read-only bytes *)
Lemma s6w_pst_img : forall a, Exists (in_zr a) (@prh_pst prh_img_A) -> in_img (@pa_segs _ A_prog_listing PI_prog_A) a.
Proof. exact S1ImgA.pst_in_img_A. Qed.
Lemma s6w_pst_ro : forall a, Exists (in_zr a) (@prh_pst prh_img_A) ->
  ~ in_roP (@pa_segs _ A_prog_listing PI_prog_A) (@pa_relro_lo _ _ PI_prog_A) (@pa_relro_hi _ _ PI_prog_A) a.
Proof. exact S1ImgA.pst_not_ro_A. Qed.

(* pal_ret_free: the four `jal fuzz_free` of pj_free return at its listed return sites (DERIVED: slots 50, 63, 69, 76) *)
Lemma s6w_ret_free : forall off, In off [200; 252; 276; 304] ->
  In (@pa_val _ A_prog_listing PI_prog_A A_TEXT + S6PjFree.AF_pf + off) (@pi_ret_sites prh_img_A F_pj_free RT_fuzz_free).
Proof.
cbn [pa_val PI_prog_A].
assert (Hb : forallb (fun off => existsb (Z.eqb (A_prog_val A_TEXT + S6PjFree.AF_pf + off))
                                   (@pi_ret_sites prh_img_A F_pj_free RT_fuzz_free)) [200; 252; 276; 304] = true)
  by (vm_compute; reflexivity).
intros off Hoff. rewrite forallb_forall in Hb. specialize (Hb off Hoff).
apply existsb_exists in Hb as (x & Hx & E). apply Z.eqb_eq in E. rewrite E. exact Hx.
Qed.
(* AIM, the A' memset row: the walks' premise at the instance is c-libc-stdio's row for __asan_memset (the segments of
   PI_prog_A are AB1v.tfibsegs by delta: both are Asan.M.loaded_segments; the listing's pc of __asan_memset is the
   row's, checked by vm_compute on the closed term) *)
Lemma s6w_aim : forall (B : asyms)
    (ARx : alayout -> astate -> list Z -> world (@pa_segs _ A_prog_listing PI_prog_A) -> (word -> option byte) -> Model -> Prop)
    (hl : Z),
  YCbqG.AR_laws_x (@pa_segs _ A_prog_listing PI_prog_A) B ARx hl -> AF0m.TfibSyms B ->
  YGcallMxmn.aintrin_realizes_xm (@pa_segs _ A_prog_listing PI_prog_A) B ARx YG0d.OSet
    (@pa_sigma _ A_prog_listing PI_prog_A AS___asan_memset).
Proof.
intros B ARx hl HL HS.
assert (E : @pa_sigma _ A_prog_listing PI_prog_A AS___asan_memset = 0x52880)
  by (cbn [pa_sigma PI_prog_A]; lazymatch goal with |- A_prog_sigma AS___asan_memset = _ => vm_compute; reflexivity end).
rewrite E. exact (PRowSet.prow_asan_memset_xm_A_lit B ARx hl HL HS).
Qed.
End w.

Print Assumptions s6w_ent_pj_free.
Print Assumptions s6w_obj.
Print Assumptions s6w_ret_free.
Print Assumptions s6w_aim.
