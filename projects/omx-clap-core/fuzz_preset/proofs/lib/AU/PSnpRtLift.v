(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bignum/lib/BnP/BnKit2.v, with its module paths and module names changed; 1014 of its 1028 lines of code are new or changed and 33 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/tx_put.v; 64 of its 422 lines of code are new or changed and 670 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/TxGlue.v, with its module paths and module names changed; 647 of its 739 lines of code are new or changed and 330 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/U/Prog/WriterRet.v, with its module paths and module names changed; 702 of its 749 lines of code are new or changed and 692 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/pj_write.v, with its module paths and module names changed; 496 of its 536 lines of code are new or changed and 709 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Prog/ReaderKB.v; 125 of its 147 lines of code are new or changed and 514 lines of the source are left out. *)
(* fm's runtime contracts in the donor's form, the generic half (RtStr lane).
   - A walk proved over the machine state alone (lib/Lib `evt`, its registers written `mkR ...`) is
     read at a donor call site (`SRr` from `cfg_at`, YG0d.v:213): the register map is moved with
     lib/Lib/RegisterBridge.v (canonical_contract_transport), and each step of the walk is a step of
     the donor's `msteps`, which `SRr_msteps` (YA0n.v:149) lifts.
   - A walk that returns to ra with the callee-saved registers kept and changes nothing but a window
     of K <= STK bytes below sp gives the donor-form post `rt_post_ro` (FMH_Rt.v:88); AR is kept by
     the donor's frame law (al_frame, YG0d.v:439), as cgif_file A/AE2j.v:142 keeps it.  Inside fm's
     user-poison window the same walk gives `rt_post_roU` (FMH_Rt.v:96), ARU kept by
     FMupoison.ARU_frame.
   - A body walk of lib/A/Bz (its own copy of `evt`) is read the same way (srr_of_canon_bz). *)
(* Modified by Theorem Labs, 2026-10: c-libc-stdio's copy for fuzz_preset image A (route (a) P2, ASan's printf_common over ARx; parent c-libc-stdio 13:0xZ) of proofs/omx-clap-core/fuzz_manifest/lib/A/FMrt_lift.v at origin/cold/port-fm-rtprintf-param 7e395de08f5: module paths fuzz_manifest -> fuzz_preset, lib/A/Bz -> lib/A/PSnpBz (the Bz files relocated to image A by c-asan's alreloc), FM glue modules -> their PSnp twins; Section p (rt_post_ro_win over AR_laws and rt_post_roU_win over ARU) is left out: the ARx printf_common contract keeps its own post (PSnpPcom.v pcm_post over alx_frame / alx_stack), as port-fm's RT_pf_shU.v does. No numeral. *)
(* Modified by Theorem Labs, 2026-10: image B twin (fuzz_preset.asan-ubsan f8f98a95) of lib/A/PSnpRtLift.v, by the unit's image-B convention (lib/AU/FCxA.v's rule): module paths lib/A/PSnpBz -> lib/AU/PSnpBz (alreloc's image-B relocation), the image-A core A<x> -> image B's Y<x> (lib/Reusable), lib/A/Img0 -> lib/B/Img0, the PSnp glue lib/A -> lib/AU. Sentences above that name image A describe the A twin. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YK0i YK14 YP03 YA0i YA0n YA0o YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI04 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0x.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Img0.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Exec.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.MState.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.RegisterBridge.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Lib.Exec.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Lib.ImageA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".

Module LE := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Exec.
Module LMS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.MState.
Module R6 := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Regs6ss.
Module RB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.RegisterBridge.
Module BzE := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Lib.Exec.
Module BzI := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Lib.ImageA.

Section l. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- registers ---- *)
Open Scope bv_scope.

(* a register a walk ends with is the register the machine ends with *)
Lemma ms_eqv_getr : forall ms0 ms' (r : bv 5), R6.ms_eqv ms0 ms' -> getr (ms_regs ms') r = getr (ms_regs ms0) r.
Proof.
  intros ms0 ms' r (HR & _). unfold getr. destruct (bv_eqb _ _) eqn:E; [reflexivity|].
  symmetry. apply HR. unfold is_x0. apply Z.eqb_neq. intros H0.
  assert (r = 0%bv) by (apply bv_eq; rewrite H0; reflexivity). subst r. rewrite bv_eqb_refl in E. discriminate.
Qed.

Open Scope Z_scope.

(* one step of a lib/Lib walk is one step of the donor's walk *)
Lemma lib_msteps_tfib : forall ms ms', LE.msteps Img0.rsegs ms ms' -> YK0i.msteps tfibsegs ms ms'.
Proof.
  intros ms ms' H. induction H as [ms | ms ms1 ms2 Hstep _ IH].
  - apply YK0i.mst_refl.
  - destruct Hstep as [Hsvc Hok]. eapply YK0i.mst_step; [exact Hsvc | exact Hok | exact IH].
Qed.

(* the donor's entry configuration, with its registers written out as a walk states them *)
Definition canon_at (regs : bvmap 5 word) (pc : Z) (m : word -> option byte) : machine_state :=
  LMS.MS (R6.mkR_of regs) fp_regs (w64 pc) fp_csr None m (seg_rom tfibsegs).

(* a walk from the call site, read in the donor's form *)
Theorem srr_of_canon : forall (W : world tfibsegs) (pc : Z) regs mem md
  (Q : machine_state -> Prop) (POST : world tfibsegs -> config -> Prop),
  LE.evt Img0.rsegs Q (canon_at regs pc (mrestrict (w_H W) mem)) ->
  (forall ms0 ms' model', Q ms0 -> R6.ms_eqv ms0 ms' -> same_but_materialized md model' ->
     hclean (w_H W) ms' -> POST W (mkCfg (unrestrict (w_H W) mem ms') model')) ->
  SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) POST.
Proof.
  intros W pc regs mem md Q POST Hev HK.
  destruct (RB.canonical_contract_transport Img0.rsegs Q
              (mkst regs (w64 pc) (mrestrict (w_H W) mem) (seg_rom tfibsegs)) Hev)
    as (ms' & Hms & ms0 & HQ & Heqv).
  unfold cfg_at.
  eapply (SRr_msteps tfibsegs Hwx_tfa W (mkst regs (w64 pc) mem (seg_rom tfibsegs)) ms' md POST).
  - rewrite restrict_mkst_fx. exact (lib_msteps_tfib _ _ Hms).
  - intros model' Hsame Hcl. apply SRr_ret. exact (HK ms0 ms' model' HQ Heqv Hsame Hcl).
Qed.

(* a lib/A/Bz body walk is a lib/Lib walk: the two trees' step relations have one body *)
Lemma bz_evt_lib : forall (Q : machine_state -> Prop) ms, BzE.evt BzI.asegs Q ms -> LE.evt Img0.rsegs Q ms.
Proof.
  intros Q ms (ms' & H & HQ). exists ms'. split; [|exact HQ]. clear HQ.
  induction H as [ms | ms ms1 ms2 Hs _ IH]; [apply LE.msteps_refl | eapply LE.msteps_cons; [exact Hs | exact IH]].
Qed.

Theorem srr_of_canon_bz : forall (W : world tfibsegs) (pc : Z) regs mem md
  (Q : machine_state -> Prop) (POST : world tfibsegs -> config -> Prop),
  BzE.evt BzI.asegs Q (canon_at regs pc (mrestrict (w_H W) mem)) ->
  (forall ms0 ms' model', Q ms0 -> R6.ms_eqv ms0 ms' -> same_but_materialized md model' ->
     hclean (w_H W) ms' -> POST W (mkCfg (unrestrict (w_H W) mem ms') model')) ->
  SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) POST.
Proof. intros W pc regs mem md Q POST Hev HK. exact (srr_of_canon W pc regs mem md Q POST (bz_evt_lib Q _ Hev) HK). Qed.

(* ---- the return configuration ---- *)
Lemma ret_pc_ok : forall k, YK0s.ret_ok k -> LMS.ret_pc k = k.
Proof.
  intros k H.
  assert (E : bv_unsigned k mod 2 = 0).
  { unfold YK0s.ret_ok, YK14.v_jalr, jalr_tgtZ in H. apply (f_equal bv_unsigned) in H.
    rewrite Z_to_bv_unsigned in H. rewrite <- H. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    assert (M : Z.land (bv_unsigned k + 0) (-2) mod 2 = 0).
    { change (-2) with (Z.lnot 1). rewrite <- Z.ldiff_land.
      replace 1 with (Z.ones 1) by reflexivity. rewrite Z.ldiff_ones_r by lia.
      rewrite Z.shiftl_mul_pow2 by lia. apply Z.mod_mul. lia. }
    set (y := Z.land (bv_unsigned k + 0) (-2)) in *. Z.div_mod_to_equations. lia. }
  pose proof (bv_unsigned_in_range 64 k) as R. change (bv_modulus 64) with (2 ^ 64) in R.
  rewrite <- (Z_to_bv_bv_unsigned _ k). apply LMS.ret_pc_even; [exact R | exact E].
Qed.

Lemma unrestrict_ret : forall regs (H : word -> bool) mem ms0 ms',
  R6.ms_eqv ms0 ms' -> YK0s.ret_ok (getr regs 1) ->
  ms_pc_val ms0 = LMS.ret_pc (getr regs 1) -> ms_fregs ms0 = fp_regs -> ms_svc_pending ms0 = None ->
  ms_resv ms0 = None -> ms_fcsr ms0 = fp_csr -> ms_rom ms0 = seg_rom tfibsegs ->
  unrestrict H mem ms' = mkst (ms_regs ms') (w64 (raZ regs)) (munrestrict H mem (ms_mem ms')) (seg_rom tfibsegs).
Proof.
  intros regs H mem ms0 ms' (_ & Ef & Ep & Es & Er & Ec & _ & Ero) Hra P0 F0 S0 R0 C0 RO0.
  unfold unrestrict, mkst.
  rewrite <- Ef, <- Ep, <- Es, <- Er, <- Ec, <- Ero, F0, P0, S0, R0, C0, RO0, (ret_pc_ok _ Hra).
  unfold raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* ---- reading the donor's view ---- *)
Lemma Z_to_bv64_mod : forall a, Z_to_bv 64 (a mod 2 ^ 64) = Z_to_bv 64 a.
Proof.
  intros a. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  apply Z.mod_mod. lia.
Qed.

Lemma aview_mod : forall H (m : word -> option byte) a, aview tfibsegs H m a = aview tfibsegs H m (a mod 2 ^ 64).
Proof. intros H m a. unfold aview, mbyte. rewrite Z_to_bv64_mod. reflexivity. Qed.

Lemma apresent_mod : forall H (m : word -> option byte) a, apresent H m a = apresent H m (a mod 2 ^ 64).
Proof. intros H m a. unfold apresent. rewrite Z_to_bv64_mod. reflexivity. Qed.

Lemma aview_some_of_apresent : forall H mem a, apresent H mem a -> aview tfibsegs H mem a <> None.
Proof. intros H mem a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate. Qed.

(* ---- the donor-form post of a walk that writes only below sp ---- *)

(* the store after a walk that changed only [lo, hi), which it leaves present: the donor's view is the old
   one outside the window, nothing visible goes away, hidden bytes are the old ones, nothing present goes away *)
Lemma win_mem : forall (H : word -> bool) mem (m : word -> option byte) (lo hi : Z),
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> m x = mrestrict H mem x) ->
  (forall a, lo <= a < hi -> m (Z_to_bv 64 a) <> None) ->
  (forall a, lo <= a < hi -> apresent H mem a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs H (munrestrict H mem m) a = aview tfibsegs H mem a) /\
  (forall a, aview tfibsegs H mem a <> None -> aview tfibsegs H (munrestrict H mem m) a <> None) /\
  (forall a, H (w64 a) = true -> munrestrict H mem m (w64 a) = mem (w64 a)) /\
  (forall a, apresent H mem a -> apresent H (munrestrict H mem m) a).
Proof.
  intros H mem m lo hi MOUT MIN PRES.
  set (mem' := munrestrict H mem m).
  assert (MO : forall x : word, ~ (lo <= bv_unsigned x < hi) -> mem' x = mem x).
  { intros x Hx. unfold mem', munrestrict. destruct (H x) eqn:EH; [reflexivity|].
    rewrite (MOUT x Hx). unfold mrestrict. rewrite EH. reflexivity. }
  assert (PW : forall a, lo <= a < hi -> apresent H mem' a).
  { intros a Ha. destruct (PRES a Ha) as [HH _]. split; [exact HH|].
    unfold mem', munrestrict. rewrite HH.
    destruct (m (Z_to_bv 64 a)) as [b|] eqn:E; [exists b; reflexivity|].
    exfalso. exact (MIN a Ha E). }
  assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs H mem' a = aview tfibsegs H mem a).
  { intros a Ha Hn. apply aview_same. apply MO. rewrite unsigned_lit_small by lia. exact Hn. }
  split; [exact AV|]. split; [|split].
  - intros a Hva. rewrite (aview_mod _ mem' a). rewrite (aview_mod _ mem a) in Hva.
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Hr. set (a' := a mod 2 ^ 64) in *.
    destruct (Z_lt_le_dec a' lo) as [L1|L1]; [rewrite AV by lia; exact Hva|].
    destruct (Z_lt_le_dec a' hi) as [L3|L3]; [|rewrite AV by lia; exact Hva].
    apply aview_some_of_apresent. apply PW. lia.
  - intros a Hh. unfold mem', munrestrict. cbv beta. rewrite Hh. reflexivity.
  - intros a Hp. rewrite apresent_mod. rewrite apresent_mod in Hp.
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Hr. set (a' := a mod 2 ^ 64) in *.
    destruct (Z_lt_le_dec a' lo) as [L1|L1];
      [| destruct (Z_lt_le_dec a' hi) as [L3|L3]; [apply PW; lia|]];
      (apply (apresent_same H mem mem' a'); [apply MO; rewrite unsigned_lit_small by lia; lia | exact Hp]).
Qed.

End l.

(* the callee-saved registers of a walk that keeps them, read as the donor reads them *)
Ltac keep_regs :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; unfold acallee_saved in Hr;
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  clear Hr;
  repeat (destruct Hr' as [Hr'|Hr']; [subst r; vm_compute; reflexivity|]);
  subst r; vm_compute; reflexivity.
