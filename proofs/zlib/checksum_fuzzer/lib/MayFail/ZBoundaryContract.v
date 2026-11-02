(** Connect the actual zero/oversize RISC-V return proof to the same library
    contract used by the full driver. The valid-size checksum case remains. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0o.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0o.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YI16.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YI14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YI5b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YI5c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail Require Import ZImage.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail Require Import ZFuzzerBounds.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail Require Import ZTraceSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section Pure.
Context {fx : FPState} {rc : RunCeil}.
Variable API : AllocAPI src0_msyms.
Let MR := aa_MR API.
Lemma boundary_frame_raw : forall regs mem mem' a,
  frame_of (zbound_env regs) zbound_mem mem mem' ->
  0 <= a < 2^64 ->
  (a < spZ regs - 112 \/ spZ regs <= a) ->
  mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
  intros regs mem mem' a HF Ha Hout. apply HF.
  rewrite Z_to_bv_unsigned. change (bv_wrap 64 a) with (a mod 2^64).
  rewrite Z.mod_small by lia. intros [r [Hin Hw]].
  unfold zbound_mem in Hin. destruct Hin as [<-|[]].
  change (spZ regs + -112 <= a < spZ regs + 0) in Hw. lia.
Qed.
Lemma boundary_frame_low : forall regs mem mem' a,
  alloc_ceiling + LIB_STACK <= spZ regs ->
  frame_of (zbound_env regs) zbound_mem mem mem' ->
  0 <= a < alloc_ceiling -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
  intros regs mem mem' a Hsp HF Ha. apply (boundary_frame_raw regs); [exact HF| |left];
    unfold LIB_STACK in *; pose proof alloc_ceiling_lt; lia.
Qed.
Lemma boundary_mbyte : forall regs mem mem' a,
  alloc_ceiling + LIB_STACK <= spZ regs ->
  frame_of (zbound_env regs) zbound_mem mem mem' ->
  0 <= a < alloc_ceiling -> mbyte zsegs mem' a = mbyte zsegs mem a.
Proof.
  intros regs mem mem' a Hsp HF Ha. unfold mbyte.
  rewrite (boundary_frame_low regs mem mem' a Hsp HF Ha). reflexivity.
Qed.
Lemma boundary_writable_eq : forall mem mem' a,
  mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a) ->
  (writable_at zsegs mem' a <-> writable_at zsegs mem a).
Proof. intros mem mem' a H. unfold writable_at, wview. rewrite H. reflexivity. Qed.
Lemma boundary_MR : forall L A regs mem mem' md,
  MR L A mem md -> alloc_ceiling + LIB_STACK <= spZ regs ->
  frame_of (zbound_env regs) zbound_mem mem mem' -> MR L A mem' md.
Proof.
  intros L A regs mem mem' md HM Hsp HF.
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM) as [Hh [Hl Hmat]].
  eapply (mr_frame _ _ (aa_laws API)); [exact HM| | | |reflexivity|exact Hh|exact Hl|exact Hmat].
  - intros a Ha. apply (boundary_mbyte regs); [exact Hsp|exact HF|].
    eapply mr_owned_low; eassumption || apply aa_laws.
  - intros a Ha [b Hb]. exists b. rewrite (boundary_frame_low regs mem mem'); [exact Hb|exact Hsp|exact HF|].
    eapply mr_owned_low; eassumption || apply aa_laws.
  - intros p n i Hin Hi.
    destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p n i HM Hin Hi) as [[b Hb] [Hp [Hn Howned]]].
    exists b. rewrite (boundary_frame_low regs mem mem'); [exact Hb|exact Hsp|exact HF|]. lia.
Qed.
Lemma boundary_block_bytes : forall L A regs mem mem' md p n i,
  MR L A mem md -> alloc_ceiling + LIB_STACK <= spZ regs ->
  frame_of (zbound_env regs) zbound_mem mem mem' ->
  In (p,n) (user_blocks A) -> 0 <= i < n ->
  mbyte zsegs mem' (ptr_addr L p+i) = mbyte zsegs mem (ptr_addr L p+i).
Proof.
  intros L A regs mem mem' md p n i HM Hsp HF Hin Hi.
  destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p n i HM Hin Hi) as [Hpresent [Hp [Hn Howned]]].
  apply (boundary_mbyte regs); [exact Hsp|exact HF|lia].
Qed.
Definition boundary_region large := hd (YP09.mkRegion None 0 0 0 0 []) (ss_mem (zbound_final large)).
Lemma boundary_region_shape : forall large,
  In (boundary_region large) (ss_mem (zbound_final large)) /\
  r_base (boundary_region large) = Some 2%nat /\
  r_wlo (boundary_region large) = -112 /\ r_whi (boundary_region large) = 0.
Proof. intros []; vm_compute; repeat split; auto. Qed.
Lemma boundary_final_writable : forall large regs final a,
  st_ok zsegs (zbound_env regs) (zbound_final large) final ->
  spZ regs - 112 <= a < spZ regs -> writable_at zsegs (ms_mem final) a.
Proof.
  intros large regs final a HS Ha.
  destruct (boundary_region_shape large) as [Hin [Hb [Hl Hhi]]].
  pose proof (mem_ok_region zsegs (zbound_env regs) (ms_mem final) _ _
    (st_ok_mem_ok zsegs _ _ _ HS) Hin) as HR.
  unfold region_ok in HR. destruct HR as [_ [_ [HW Hchunks]]].
  specialize (HW (a-spZ regs)). rewrite Hl, Hhi in HW.
  specialize (HW ltac:(lia)). rewrite Hb in HW.
  change (writable_at zsegs (ms_mem final) (spZ regs + (a-spZ regs))) in HW.
  replace (spZ regs + (a-spZ regs)) with a in HW by lia. exact HW.
Qed.


Lemma boundary_checksum_post : forall L A regs mem md p n pl b regs' mem',
  lib_pre_x src0_msyms API LIB_STACK EMPTY L A regs mem md RA_LIB p n pl b ->
  getr regs' (Z_to_bv 5 10) = Z_to_bv 64 0 ->
  regs_preserved regs regs' ->
  frame_of (zbound_env regs) zbound_mem mem mem' ->
  (forall a, lib_scratch src0_msyms LIB_STACK regs a -> writable_at zsegs mem' a) ->
  lib_post_x src0_msyms API LIB_STACK L A regs mem md p n b
    (LL 0 (m_fs md) []) L A regs' mem' md.
Proof.
  intros L A regs mem md p n pl b regs' mem' HP Hr Hregs HF HWnew.
  destruct HP as [HP [Hlen [HD [Hres [Hroom [HSink [Hfd [Hsorted Hsp47]]]]]]]].
  destruct HP as [HM [HW [HB [Hid [Hra [Hal [Hsp [HspHi [HWstack [Htp [HWerrno
    [Hptr [Hsize [Hlive Hro]]]]]]]]]]]]]].
  unfold lib_post_x. cbn [ll_ret ll_fs ll_out].
  split; [eapply boundary_MR; eassumption|].
  split; [exact HW|]. split; [exact HB|]. split; [exact Hid|].
  split; [exact Hr|]. split; [exact Hregs|].
  split.
  { exists (m_vmmaps md), (m_fds md), (m_statpins md).
    split; [apply os_upd_self|]. intros k. reflexivity. }
  split.
  { intros q k Hin. exists q. auto. }
  split.
  { intros a Ha Hnot.
    assert (Hout : a < spZ regs - 112 \/ spZ regs <= a).
    { destruct (Z_lt_le_dec a (spZ regs-112)); [auto|]. right.
      destruct (Z_le_gt_dec (spZ regs) a); [assumption|]. exfalso. apply Hnot.
      unfold lib_scratch. left. unfold LIB_STACK in *. lia. }
    assert (HR : mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a))
      by (eapply (boundary_frame_raw regs); eassumption || (pose proof alloc_ceiling_val; lia)).
    split; [unfold mbyte; rewrite HR; reflexivity|].
    apply iff_sym; apply boundary_writable_eq. exact HR. }
  split.
  { intros a Himg Hstatic Hctx Herr.
    pose proof (so_img_hi _ src0_syms_ok a Himg) as Ha.
    split; [eapply (boundary_mbyte regs); eassumption|]. apply iff_sym; apply boundary_writable_eq.
    eapply (boundary_frame_low regs); eassumption. }
  split.
  { intros q k i Hin Hneq Hi. eapply boundary_block_bytes; eassumption. }
  split; [exact HWnew|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact Hsorted|]. split.
  { eapply sink_none_frame; [|exact HSink]. intros a Ha.
    pose proof (src0_env_addr_range a Ha) as Har.
    apply (boundary_mbyte regs); [exact Hsp|exact HF|]. pose proof alloc_ceiling_val. lia. }
  split.
  { change (res_ok A b). exact Hres. }
  intros i Hi. destruct Hlive as [[-> Hempty]|[Hpos [q [Hin Hq]]]].
  - lia.
  - rewrite <- Hq. eapply boundary_block_bytes; eassumption.
Qed.

Theorem checksum_boundary_contract : forall L A regs mem md p n pl b (K : lleaf -> TSet),
  lib_pre_x src0_msyms API LIB_STACK EMPTY L A regs mem md RA_LIB p n pl b ->
  (n = 0 \/ 1048576 < n) -> frm_zero fp_csr ->
  (forall l c',
    (exists (fx' : FPState) L' A' regs' mem' md',
      c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 RA_LIB) mem' (seg_rom zsegs)) md' /\
      frm_zero (@fp_csr fx') /\
      lib_post_x src0_msyms API LIB_STACK L A regs mem md p n b l L' A' regs' mem' md') ->
    realizes zsegs c' (K l)) ->
  realizes zsegs (mkCfg (mkst regs (Z_to_bv 64 LIBPC) mem (seg_rom zsegs)) md)
    (LIBK pl (m_fs md) K).
Proof.
  intros L A regs mem md p n pl b K HP Hcase Hfrm HK.
  pose proof HP as [HP0 _].
  destruct HP0 as [HM [HW [HB [Hid [Hra [Hal [Hsp [HspHi [HWstack [Htp [HWerrno
    [Hptr [Hsize [Hlive Hro]]]]]]]]]]]]]].
  assert (HN : 0 <= n < 2^64).
  { destruct Hlive as [[-> He]|[Hn [q [Hq Eq]]]]; [lia|].
    destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ q n HM Hq) as [Hlo Hhi].
    pose proof alloc_ceiling_lt. lia. }
  assert (Hchoose : exists large : bool,
    if large then 1048577 <= bv_unsigned (getr regs (Z_to_bv 5 11))
    else getr regs (Z_to_bv 5 11) = Z_to_bv 64 0).
  { destruct Hcase as [Hz|Hb].
    - exists false. change (getr regs (Z_to_bv 5 11) = Z_to_bv 64 0).
      rewrite Hz in Hsize. exact Hsize.
    - exists true. change (1048577 <= bv_unsigned (getr regs (Z_to_bv 5 11))).
      replace (getr regs (Z_to_bv 5 11)) with (Z_to_bv 64 n) by (symmetry; exact Hsize).
      rewrite Z_to_bv_unsigned.
      change (1048577 <= n mod 2^64). rewrite Z.mod_small by lia. lia. }
  destruct Hchoose as [large Hchoose].
  assert (Hra' : getr regs (Z_to_bv 5 1) = Z_to_bv 64 zbound_return) by exact Hra.
  assert (Hsp' : 65536 <= bv_unsigned (getr regs (Z_to_bv 5 2)) < 2^63).
  { change (65536 <= spZ regs < 2^63). pose proof alloc_ceiling_val. unfold LIB_STACK in Hsp. lia. }
  assert (Hstack112 : forall a, bv_unsigned (getr regs (Z_to_bv 5 2))-112 <= a <
    bv_unsigned (getr regs (Z_to_bv 5 2)) -> writable_at zsegs mem a).
  { intros a Ha. apply HWstack. change (spZ regs-112 <= a < spZ regs) in Ha.
    unfold LIB_STACK. lia. }
  pose proof (zbound_entry_st_ok large regs mem Hra' Hsp' Hal Hchoose Hstack112) as HS.
  destruct (zbound_machine_certificate large (zbound_env regs) _ HS)
    as [final [Hsteps [HSfinal HF]]].
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM) as [Hh [Hl Hmat]].
  change (realizes zsegs (mkCfg (mkst regs (Z_to_bv 64 0x141f0) mem (seg_rom zsegs)) md)
    (K (LL 0 (m_fs md) []))).
  eapply (rz_msteps zsegs _ final md); [exact Hh|exact Hl|exact Hsteps|].
  apply HK.
  exists fx, L, A, (ms_regs final), (ms_mem final), md.
  assert (Hresv : ss_resv (zbound_final large) = None) by
    (destruct large; vm_compute; reflexivity).
  pose proof (st_ok_mkst zsegs _ _ _ HSfinal Hresv) as Hshape.
  rewrite (proj1 (zbound_reaches_return large)) in Hshape.
  split; [f_equal; exact Hshape|]. split; [exact Hfrm|].
  eapply (boundary_checksum_post L A regs mem md p n pl b); [exact HP| | |exact HF|].
  - rewrite (st_ok_reg zsegs _ _ _ (Z_to_bv 5 10) HSfinal).
    rewrite (proj1 (proj2 (zbound_reaches_return large))). reflexivity.
  - intros r Hr. assert (Hin : In r [1;2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]).
    { unfold callee_saved in Hr. cbn. lia. }
    rewrite (st_ok_reg zsegs _ _ _ (Z_to_bv 5 r) HSfinal).
    rewrite zbound_saved_symbolic by exact Hin. symmetry.
    apply (zbound_regs_ok large regs Hra'). destruct large; [exact I|exact Hchoose].
  - intros a [Ha|Ha].
    + destruct (Z_lt_le_dec a (spZ regs-112)) as [Hlow|Hhigh].
      * apply (proj2 (boundary_writable_eq mem (ms_mem final) a
          (boundary_frame_raw regs mem _ a HF ltac:(pose proof alloc_ceiling_val; lia) (or_introl Hlow)))).
        apply HWstack. exact Ha.
      * apply (boundary_final_writable large regs final a HSfinal). lia.
    + assert (Hraw : ms_mem final (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
      { apply (boundary_frame_low regs mem (ms_mem final) a Hsp HF).
        change (195084 <= a < 195088) in Ha. pose proof alloc_ceiling_val. lia. }
      apply (proj2 (boundary_writable_eq mem (ms_mem final) a Hraw)).
      apply HWerrno. exact Ha.
Qed.
End Pure.
