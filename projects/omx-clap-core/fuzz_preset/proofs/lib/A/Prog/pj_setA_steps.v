(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the STEP LEMMAS and tactics every segment of pj_set's image-A' walk shares (fuzz_preset
   asan, A 0x8685c; the cuts of lib/A/Prog/pj_setA_defs.v), split out of pj_setA_seg_tail.v unchanged so that the
   segment files build against them independently: pjsA_regne / pjsA_regval / pjsA_kept_ne / pjsA_cs / pjsA_fd,
   pjsA_hull_bounds, the concrete steps pjsA_step_addi / pjsA_step_jal / pjsA_step_j, pjsA_dest_block, pjsA_pres /
   pjsA_pres_sp, and the memory-growth lemma pjsnA_grows (from pj_setA_seg_ent.v).
   proves no function (kind: step lemmas). Numerals: as pj_setA_seg_tail.v's. No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YCbqGcallW FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgA pj_setA_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.
#[local] Existing Instance prh_img_A.

(* ---- small tactics: register disequality, the word at an offset and its decoding (over this file's listing) ---- *)
Ltac pjsA_regne :=
  let E := fresh "E" in
  intros E; apply (f_equal (fun x : bv 5 => bv_unsigned x)) in E; vm_compute in E; discriminate E.
Ltac pjsA_regval := repeat (rewrite getr_other by pjsA_regne); try (rewrite getr_same by pjsA_regne).
Ltac pjsA_kept_ne :=
  let H := fresh "Hk" in
  lazymatch goal with Hr : In ?r PJSA_KEPT |- _ =>
    pose proof Hr as H; unfold PJSA_KEPT in H; cbn [In] in H;
    repeat (destruct H as [<- | H]; [pjsA_regne |]); destruct H end.
Ltac pjsA_cs :=
  lazymatch goal with |- acallee_saved (bv_unsigned ?x) =>
    let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end;
  unfold acallee_saved; lia.
Ltac pjsA_fd k Hl Hd :=
  let r := eval vm_compute in
    (clookup (@pa_tbl _ A_prog_listing PI_prog_A) (@pa_val _ A_prog_listing PI_prog_A A_TEXT + k)) in
  lazymatch r with
  | Some ?w =>
    assert (Hl : clookup (@pa_tbl _ A_prog_listing PI_prog_A) (@pa_val _ A_prog_listing PI_prog_A A_TEXT + k) = Some w)
      by (vm_compute; reflexivity);
    let dz := eval vm_compute in (decode_any (Z_to_bv 32 w)) in
    assert (Hd : decode_any (Z_to_bv 32 w) = dz) by (vm_compute; reflexivity)
  | _ => fail "pjsA_fd: no image word at offset" k
  end.

(* the shadow hull of an application range below kHighMemEnd lies in the shadow region [kLowMemEnd, kHighShadowEnd)
   *)
Lemma pjsA_hull_bounds : forall x n s, 0 <= x -> 0 < n -> x + n <= kHighMemEnd ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> kLowMemEnd <= s < kHighShadowEnd.
Proof.
intros x n s H0 Hn Hx Hs. unfold shadow_addr, kLowMemEnd, kHighShadowEnd, kHighMemEnd, SHADOW_OFF in *.
pose proof (Z.div_pos x 8 H0 ltac:(lia)) as P1.
assert (P3 : (x + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
pose proof (Z.div_mod (SHADOW_OFF + x / 8) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (SHADOW_OFF + x / 8) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as M2.
unfold SHADOW_OFF in *.
lia.
Qed.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation PA := PI_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).

(* one concrete step at a listing offset: addi (mv / li), jal with a link, and the unconditional j (rd = zero) *)
Lemma pjsA_step_addi : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z) w (rd rs : bv 5) (imm : bv 12) (rd' : bv 5) (v : word),
  clookup (@pa_tbl _ A_prog_listing PA) (BASE + k) = Some w ->
  decode_any (Z_to_bv 32 w) = Some (OpImm ALU_ADD rd rs imm, 4%Z) ->
  bv_eqb rd (0%bv : bv 5) = false -> rd = rd' ->
  v_addi (getr regs rs) (bv_signed imm) = v ->
  (forall X, SRr SEGS W (mkCfg (@YK11.mkst fx (regupd regs rd' v) (v_addi (Z_to_bv 64 (BASE + k)) 4) mem
     (YK11.seg_rom SEGS)) (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w rd rs imm rd' v Hl Hd Hrd Erd Hv HK. subst rd'.
eapply (SRr_step SEGS (@pa_wx _ A_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  exact (step_addi_at (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rd rs imm v (pa_fetch_ok (PI := PA) _ _ Hl) (not_ecall_of_decode _ _ _ Hd ltac:(discriminate))
    Hd Hrd Hv).
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)). apply HK.
Qed.

Lemma pjsA_step_jal : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z) w (rd : bv 5) (imm : bv 21) (rd' : bv 5) (ra pc' : word),
  clookup (@pa_tbl _ A_prog_listing PA) (BASE + k) = Some w ->
  decode_any (Z_to_bv 32 w) = Some (Jal rd imm, 4%Z) ->
  bv_eqb rd (0%bv : bv 5) = false -> rd = rd' ->
  v_addi (Z_to_bv 64 (BASE + k)) 4 = ra ->
  btgt (Z_to_bv 64 (BASE + k)) (bv_signed imm) = pc' ->
  (forall X, SRr SEGS W (mkCfg (@YK11.mkst fx (regupd regs rd' ra) pc' mem (YK11.seg_rom SEGS))
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w rd imm rd' ra pc' Hl Hd Hrd Erd Era Hpc HK. subst rd' ra pc'.
eapply (SRr_step SEGS (@pa_wx _ A_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  rewrite (step_jal_link (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rd imm (pa_fetch_ok (PI := PA) _ _ Hl) (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd).
  rewrite Hrd. cbv beta iota. reflexivity.
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)). apply HK.
Qed.

Lemma pjsA_step_j : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z) w (rd : bv 5) (imm : bv 21) (pc' : word),
  clookup (@pa_tbl _ A_prog_listing PA) (BASE + k) = Some w ->
  decode_any (Z_to_bv 32 w) = Some (Jal rd imm, 4%Z) ->
  bv_eqb rd (0%bv : bv 5) = true ->
  btgt (Z_to_bv 64 (BASE + k)) (bv_signed imm) = pc' ->
  (forall X, SRr SEGS W (mkCfg (@YK11.mkst fx regs pc' mem (YK11.seg_rom SEGS))
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w rd imm pc' Hl Hd Hrd Hpc HK. subst pc'.
eapply (SRr_step SEGS (@pa_wx _ A_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  rewrite (step_jal_link (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rd imm (pa_fetch_ok (PI := PA) _ _ Hl) (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd).
  rewrite Hrd. cbv beta iota. reflexivity.
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)). apply HK.
Qed.
End h.

Section tl. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation PST := (prh_pst (PI := prh_img_A)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.

(* the placement a 56-byte struct of this walk has (the contract's prhPj_slot, minus what only the entry state knows):
   every byte is a byte of a live allocator block or of a live fake frame, so the intrinsic's destination premise
   holds and the byte is not an image byte *)
Lemma pjsA_dest_block : forall dd en ly S Lam W regs mem p,
  prhPj_slot (PA := PA) B (STK_pj_set dd) (jsA_d en) ly S Lam W regs mem p ->
  (exists a k, In (a, k) Lam /\ a <= p /\ p + 56 <= a + k) \/
  (exists b m, In (b, m) (ablocks B ly S) /\ b <= p /\ p + 56 <= b + m) \/
  (exists cid pos, In (cid, pos) (frames S) /\
     frame_addr ly cid pos <= p /\ p + 56 <= frame_addr ly cid pos + fs_frame_bytes cid) \/
  (spZ regs <= p /\ p + 56 <= spZ regs + jsA_d en).
Proof.
  intros dd en ly S Lam W regs mem p (_ & Hat & _).
  destruct Hat as [H | [(b & m & Hin & _ & Hb & Hm) | [H | H]]];
    [left; exact H | right; left; exists b, m; split; [exact Hin | split; [exact Hb | exact Hm]]
    | right; right; left; exact H | right; right; right; exact H].
Qed.

(* registers across an intrinsic call: a callee-saved register is the caller's (the argument registers 1, 10, 11
   and 12 the call sets are not callee-saved) *)
Lemma pjsA_pres : forall (regs regs' : bvmap 5 word) (r : bv 5), aregs_preserved regs regs' ->
  acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). exact (HP _ Hr). Qed.
Lemma pjsA_pres_sp : forall (regs regs' : bvmap 5 word), aregs_preserved regs regs' -> spZ regs' = spZ regs.
Proof.
  intros regs regs' HP. unfold spZ. f_equal.
  apply (pjsA_pres regs regs' (2%bv : bv 5) HP). unfold acallee_saved. vm_compute. lia.
Qed.

End tl.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation PA := PI_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
(* the memory only grows when every present byte stays present *)
Lemma pjsnA_grows : forall (H : word -> bool) m m',
  (forall a, apresent H m a -> apresent H m' a) -> mem_grows (mrestrict H m) (mrestrict H m').
Proof.
intros H m m' Hp x Hx. unfold mrestrict in *. destruct (H x) eqn:Ehx; [exact Hx|].
destruct (m x) as [b|] eqn:Em; [|exfalso; exact (Hx eq_refl)].
assert (Ha : apresent H m (bv_unsigned x))
  by (unfold apresent; rewrite Z_to_bv_bv_unsigned; split; [exact Ehx | exists b; exact Em]).
destruct (Hp _ Ha) as [_ [b' Hb']]. rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate.
Qed.
End g.
