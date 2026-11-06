(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image B' (asan-ubsan, harness fix #102, pin sha256
   d663f82d7f488d30f8e8d7496cb814e595a2f3cbbf16bde81a65cb3ea9af0994, unstripped twin c90d4fa54d43160b): the SHARED
   SUPPORT LEMMAS of the B' walk of LLVMFuzzerTestOneInput (entry 0x816cc): the two generic step rules over the listing
   at a GENERIC image ({PA : PAImg B_prog_listing}, the PAListing PL_102_B), the frame geometry, the class-24 count from
   the model-run position, and pure list / byte facts. No function is proved here, no slot word and no address is read.
   THE B' TWIN of lib/A/Prog/Ent102L6AfLem.v (blob a37e0dc13d12, the A' L6f lane's shared file), ported by port/a2b.py
   (sha256 f5113cbc90e503da) and then by hand: L := B_prog_listing, PL := PL_102_B, the statement file
   lib/AU/Ent102CutsB.v in place of lib/A/Ent102CutsA.v (the same definitions over a generic listing). Written for row
   LL3B (lib/AU/Prog/Ent102L3B.v); no B' twin existed (the tree, preset-tree-at-2026-10-29T16-15-10Z.tsv (sha256 397234f0b973; internal record) and the
   B' row branches LL4jB / LL5aB / LL5dB, 16:4xZ).
   STATEMENT read: lib/AU/Ent102CutsB.v (blob 3fe279272cb8: ec_ARx, ec_frame_shadow, EC_FRAME_BYTES, LLVMF_FS_CLASS).
   LISTING: lib/B/Listing_prog.v blob 8bcc2c9e7809 (slot k = byte offset 4k from the entry), through the PAListing
   PL_102_B of lib/B/Ent102PLB.v (blob e0348e1212c9); lib/B/PAImg_prog.v is not loaded, no vm_compute on pa_val /
   pa_sigma (only the listing's own slots are computed).
   THE KIT TEXTS: lib/A/PRH_Base.v (names only), lib/A/PRH_FnPj.v (the class-24 premise of tpj_free_specX this file's
   l6f_ccnt24 supplies): generic over the listing class, the same files on both images.
   rule 24: proves no function (support lemmas of the B' walk of LLVMFuzzerTestOneInput; its reuse search is row
   LL3B's, a Theorem Labs lane's internal file rule24-LL3B.txt, and the A' file's).
   TAKEN BY PATH (image-free; each restated under an l6f_ name), as the A' file:
   - l6f_land_neg32: lib/A/Prog/Ent102L0A.v l0_land_neg32 (a Theorem Labs lane; from
     H6_Base.v (sha256 f6829081650b; internal record));
   - l6f_rd64_val / l6f_geom: lib/A/Prog/Ent102L6AEnt.v l6_rd64_val / l6_geom (a working branch);
   - l6f_step_addi: lib/B/Prog/pj_set_seg_tail.v pjs_step_addi (pj_set_seg_tail.v (sha256 db6f21c9e67c; internal record)), the
     fetch taken from the PAListing (YC1fP.v pa_fetch_pw) in place of the image table; l6f_step_call is its jal twin
     over a PCall slot, the target read off the certificate (YP0d.v cert_slot, as YP0d.v sym_step_pi_call does);
   - l6f_slot_img: YC1fP.v pa_slot_img's proof, ending at in_img;
   - l6f_rdword_of_rd64: YCem.v rdword_of_val_mem's proof over a reader;
   - l6f_hruns_big / l6f_ccnt24: lib/AU/PresetCfnB.v iface_hruns_big / counts_of_room_pos (its class-24 half) /
     counts_of_room_pos_rl, which this walk may not Require (PresetCfnB's closure is red on the #102 facts).
   NUMERALS: 128 / 32 / 16 / 8 / 4 are LENGTHs (the frame, its alignment, its shadow bytes, the granule, an instruction);
   2 ^ 40 / 2 ^ 64 are the engine's code-span and word ranges; 0x7fff8000 / 0x7fff7000 / 0x10007fff8000 /
   0x7fffff800000 are ASan constants. No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK1d YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require
PresetRoomPos PresetRoom PresetReqAt PresetRun PresetLiveSec PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfRoomLivePreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog Ent102PLB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import Ent102CutsB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope bv_scope.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. Tactics: register disequality, callee-saved membership, the listing slot at an offset and its decoding. *)
Ltac l6f_regne :=
  let E := fresh "E" in
  intros E; apply (f_equal (fun x : bv 5 => bv_unsigned x)) in E; vm_compute in E; discriminate E.
Ltac l6f_cs :=
  lazymatch goal with |- acallee_saved (bv_unsigned ?x) =>
    let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end;
  unfold acallee_saved; lia.
Ltac l6f_fd k Hpl Hd :=
  let r := eval vm_compute in (plookup (@pl_tpi _ PL_102_B) k) in
  lazymatch r with
  | Some (PW ?w) =>
    assert (Hpl : plookup (@pl_tpi _ PL_102_B) k = Some (PW w)) by (vm_compute; reflexivity);
    let dz := eval vm_compute in (decode_any (Z_to_bv 32 w)) in
    assert (Hd : decode_any (Z_to_bv 32 w) = dz) by (vm_compute; reflexivity)
  | _ => fail "l6f_fd: no plain word at offset" k
  end.
Ltac l6f_fdc k Hpl :=
  let r := eval vm_compute in (plookup (@pl_tpi _ PL_102_B) k) in
  lazymatch r with
  | Some (PCall ?s ?rd) =>
    assert (Hpl : plookup (@pl_tpi _ PL_102_B) k = Some (PCall s rd)) by (vm_compute; reflexivity)
  | _ => fail "l6f_fdc: no call slot at offset" k
  end.

(* ---------------------------------------------------------------------- *)
(* 2. Pure facts. *)
(* the prologue's `andi sp, sp, -32` as the statement writes it (Ent102L0A.v l0_land_neg32, by path) *)
Lemma l6f_land_neg32 : forall x, 0 <= x -> Z.land x (-32) = x / 32 * 32.
Proof.
intros x Hx.
assert (E2 : x / 32 * 32 = Z.shiftl (Z.shiftr x 5) 5)
  by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; reflexivity).
assert (E1 : (-32) = Z.lnot (Z.ones 5)) by (vm_compute; reflexivity).
rewrite E1, E2. apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec, Z.shiftl_spec, Z.lnot_spec by lia.
destruct (Z.lt_ge_cases i 5) as [H5|H5].
- rewrite (Z.testbit_neg_r _ (i - 5)) by lia. rewrite Z.ones_spec_low by lia. apply Bool.andb_false_r.
- rewrite Z.ones_spec_high by lia. rewrite Bool.andb_true_r.
  rewrite Z.shiftr_spec by lia. f_equal. lia.
Qed.

Lemma l6f_zmaxl_in : forall x l, In x l -> x <= zmaxl l.
Proof.
intros x l. induction l as [|y t IH]; intros H; [destruct H|].
unfold zmaxl in *. cbn [fold_right]. destruct H as [<-|H]; [lia | specialize (IH H); lia].
Qed.

Lemma l6f_zmaxl_nonneg : forall l, 0 <= zmaxl l.
Proof. intros l. induction l as [|y t IH]; unfold zmaxl in *; cbn [fold_right]; lia. Qed.

Lemma l6f_bsum_perm : forall l l', Permutation l l' -> prh_bsum l = prh_bsum l'.
Proof.
intros l l' H. induction H as [|x l l' H IH|x y l|l l' l'' H1 IH1 H2 IH2]; cbn [prh_bsum]; lia.
Qed.

(* distinct blocks of a pairwise disjoint list, every size at least 1 *)
Lemma l6f_nodup_pw : forall (l : list (Z * Z)), Forall (fun b => 0 <= snd b) l ->
  YG0f.pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l) -> List.NoDup l.
Proof.
intros l. induction l as [|x t IH]; intros HF HP; [constructor|].
cbn [map YG0f.pairwise] in HP. destruct HP as [HPx HPt].
pose proof (Forall_inv HF) as Hx. pose proof (Forall_inv_tail HF) as HFt.
constructor; [|exact (IH HFt HPt)].
intros Hin. rewrite Forall_forall in HPx.
specialize (HPx (fst x, req_size (snd x)) (in_map (fun b => (fst b, req_size (snd b))) t x Hin)).
unfold zdisjoint in HPx. cbn [fst snd] in HPx.
pose proof (req_size_pos (snd x) Hx) as (Hr & _). lia.
Qed.

Lemma l6f_nodup_app_l : forall (l1 l2 : list (Z * Z)) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
intros l1. induction l1 as [|y t IH]; intros l2 x HN Hx; [destruct Hx|].
cbn [app] in HN. apply NoDup_cons_iff in HN as [Hy HN].
destruct Hx as [<-|Hx].
- intros Hin. apply Hy. apply in_or_app. right. exact Hin.
- exact (IH l2 x HN Hx).
Qed.

Lemma l6f_pw_cross : forall {X : Type} (R : X -> X -> Prop) (l1 l2 : list X) x y,
  YG0f.pairwise R (l1 ++ l2) -> In x l1 -> In y l2 -> R x y.
Proof.
intros X R l1. induction l1 as [|z t IH]; intros l2 x y H Hx Hy; [destruct Hx|].
cbn [app YG0f.pairwise] in H. destruct H as [Hf Ht].
destruct Hx as [<-|Hx].
- rewrite Forall_forall in Hf. apply Hf. apply in_or_app. right. exact Hy.
- exact (IH l2 x y Ht Hx Hy).
Qed.

(* a callee-saved register across a call (pj_set_seg_tail.v pjs_pres, by path) *)
Lemma l6f_pres : forall (regs regs' : bvmap 5 word) (r : bv 5), aregs_preserved regs regs' ->
  acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). exact (HP _ Hr). Qed.

Lemma l6f_rd64_kept : forall (rd rd' : reader) a v,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rd64 rd a v -> rd64 rd' a v.
Proof. intros rd rd' a v Hk H k Hk8. rewrite Hk by lia. exact (H k Hk8). Qed.

(* the eight bytes of a little-endian read as one word (YCem.v rdword_of_val_mem, by path, over a reader) *)
Lemma l6f_rdword_of_rd64 : forall (rd : reader) a v, rd64 rd a v -> 0 <= v < 2 ^ 64 -> rdword rd a = Some v.
Proof.
intros rd a v H Hv.
assert (B0 : rd a = Some (le_byte v 8 0)) by (pose proof (H 0%nat ltac:(lia)) as X; rewrite Z.add_0_r in X; exact X).
assert (B1 : rd (a + 1) = Some (le_byte v 8 1)) by exact (H 1%nat ltac:(lia)).
assert (B2 : rd (a + 2) = Some (le_byte v 8 2)) by exact (H 2%nat ltac:(lia)).
assert (B3 : rd (a + 3) = Some (le_byte v 8 3)) by exact (H 3%nat ltac:(lia)).
assert (B4 : rd (a + 4) = Some (le_byte v 8 4)) by exact (H 4%nat ltac:(lia)).
assert (B5 : rd (a + 5) = Some (le_byte v 8 5)) by exact (H 5%nat ltac:(lia)).
assert (B6 : rd (a + 6) = Some (le_byte v 8 6)) by exact (H 6%nat ltac:(lia)).
assert (B7 : rd (a + 7) = Some (le_byte v 8 7)) by exact (H 7%nat ltac:(lia)).
unfold rdword. rewrite B0, B1, B2, B3, B4, B5, B6, B7. f_equal. apply le_bytes8. exact Hv.
Qed.

(* ---------------------------------------------------------------------- *)
(* 3. The class-24 count at a position of the model run (PresetCfnB.v iface_hruns_big / counts_of_room_pos's
      class-24 half / counts_of_room_pos_rl, by path). *)
Lemma l6f_hruns_big : forall sm x os, PresetReqAt.MAXB < Z.of_nat (length x) -> PresetRun.hruns sm x os = [].
Proof.
intros sm x os Hx. induction os as [|[[o1 o2] o0] os IH]; [reflexivity|].
rewrite PresetRun.hruns_cons, IH, app_nil_r. unfold PresetRun.call_evs. cbv zeta.
rewrite (proj2 (Z.ltb_lt _ _) Hx). reflexivity.
Qed.

Lemma l6f_ccnt24 : forall sm x os i H0 hist S, PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof.
intros sm x os i H0 hist S ((d & Hd & Hp) & _).
apply CfRoomLivePreset.preset_ccnt24.
destruct (Z_le_gt_dec (Z.of_nat (length x)) PresetReqAt.MAXB) as [Hx|Hx].
- exact (PresetLiveSec.live_c24_state sm x os i _ d Hx Hd Hp).
- rewrite (l6f_hruns_big sm x os ltac:(lia)), List.firstn_nil in Hp.
  pose proof (PresetLiveSec.cnt_state (PresetRoom.in_cls 24) _ _ d Hd Hp) as C2.
  assert (Z0 : forall f, PresetReqAt.cnt f (PresetReqAt.hlive []) = 0%nat) by reflexivity.
  rewrite Z0 in C2. rewrite PresetLiveBounds.L24_value. unfold PresetLiveBounds.DRV.
  lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. The two concrete steps at a generic image: a plain `addi` slot and a `jal ra, f` call slot. *)
Section S. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {PA : @PAImg rc B_prog_listing}.
#[local] Notation SEGS := (@pa_segs rc B_prog_listing PA).
#[local] Notation VAL := (@pa_val rc B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma rc B_prog_listing PA).
#[local] Notation BASE := (@pa_val rc B_prog_listing PA A_TEXT).

Lemma l6f_pc4 : forall k, 0 <= k < 2 ^ 40 -> v_addi (Z_to_bv 64 (BASE + k)) 4 = Z_to_bv 64 (BASE + (k + 4)).
Proof.
intros k Hk. pose proof (@pa_B_ok rc B_prog_listing PA) as (HB0 & HB1 & _).
unfold v_addi. rewrite unsigned_lit_small by lia. f_equal. lia.
Qed.

(* THE TWO STEPS OVER A WORLD RELATION R (YA0nH.SRrG; the free move): the lanes after check_no_overread run at
   wle' segs RZ_cf. A step does not change the world, so the proofs are the plain ones over YSRrG.SRrG_step; the plain
   names below are the instances at wle (YA0n.SRr IS SRrG at wle). *)
Lemma l6f_step_addiR : forall (R : world SEGS -> world SEGS -> Prop) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k w : Z) (rd rs : bv 5) (imm : bv 12) (rd' : bv 5) (v : word),
  0 <= k < 2 ^ 40 ->
  plookup (@pl_tpi _ PL_102_B) k = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (OpImm ALU_ADD rd rs imm, 4%Z) ->
  bv_eqb rd (0%bv : bv 5) = false -> rd = rd' ->
  v_addi (getr regs rs) (bv_signed imm) = v ->
  (forall X, SRrG SEGS R W (mkCfg (@YK11.mkst fx (regupd regs rd' v) (Z_to_bv 64 (BASE + (k + 4))) mem
     (YK11.seg_rom SEGS)) (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRrG SEGS R W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros R W regs mem md Q k w rd rs imm rd' v Hk Hpl Hd Hrd Erd Hv HK. subst rd'.
pose proof (pa_fetch_pw (PL := PL_102_B) (PI := PA) k w Hpl) as Hf.
eapply (SRrG_step SEGS R (@pa_wx rc B_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  exact (step_addi_at (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rd rs imm v Hf (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd Hrd Hv).
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)).
  rewrite (l6f_pc4 k Hk). apply HK.
Qed.
Lemma l6f_step_addi : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k w : Z) (rd rs : bv 5) (imm : bv 12) (rd' : bv 5) (v : word),
  0 <= k < 2 ^ 40 ->
  plookup (@pl_tpi _ PL_102_B) k = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (OpImm ALU_ADD rd rs imm, 4%Z) ->
  bv_eqb rd (0%bv : bv 5) = false -> rd = rd' ->
  v_addi (getr regs rs) (bv_signed imm) = v ->
  (forall X, SRr SEGS W (mkCfg (@YK11.mkst fx (regupd regs rd' v) (Z_to_bv 64 (BASE + (k + 4))) mem
     (YK11.seg_rom SEGS)) (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof. exact (l6f_step_addiR (@wle SEGS)). Qed.

Lemma l6f_step_callR : forall (R : world SEGS -> world SEGS -> Prop) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z) (s : asym) (rd rd' : bv 5),
  0 <= k < 2 ^ 40 ->
  plookup (@pl_tpi _ PL_102_B) k = Some (PCall s rd) -> rd = rd' ->
  (forall X, SRrG SEGS R W (mkCfg (@YK11.mkst fx (regupd regs rd' (Z_to_bv 64 (BASE + (k + 4))))
     (Z_to_bv 64 (SIGMA s)) mem (YK11.seg_rom SEGS)) (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRrG SEGS R W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros R W regs mem md Q k s rd rd' Hk Hpl Erd HK. subst rd'.
pose proof (@pa_B_ok rc B_prog_listing PA) as (HB0 & HB1 & _).
pose proof Hpl as Hpl'. rewrite <- (@pl_tpi_eq _ PL_102_B) in Hpl'.
pose proof (cert_slot asym (clookup pa_tbl) VAL SIGMA B_prog_listing pa_cert _ _ Hpl') as (Hck & _ & _).
unfold pi_slot_check in Hck. cbv zeta in Hck.
destruct (clookup pa_tbl (VAL A_TEXT + k)) as [wz|] eqn:Hl; [|discriminate Hck].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; [|discriminate Hck].
apply andb_prop in Hck as [Hsz Hck]. apply Z.eqb_eq in Hsz. subst isz.
destruct i; try discriminate Hck.
lazymatch type of Hdec with decode_any _ = Some (Jal ?r ?im, _) => rename r into rdj; rename im into immj end.
apply andb_prop in Hck as [Hck Ht]. apply andb_prop in Hck as [Hrd Hnz].
apply reg_eqb_eq in Hrd. subst rdj. apply Z.eqb_eq in Ht.
assert (Hrd0 : bv_eqb rd (0%bv : bv 5) = false).
{ destruct (bv_eqb rd (Z_to_bv 5 0)) eqn:E3; [discriminate Hnz|]. rewrite <- E3. unfold bv_eqb. reflexivity. }
pose proof (pa_fetch_ok (PI := PA) _ _ Hl) as Hf.
eapply (SRrG_step SEGS R (@pa_wx rc B_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  rewrite (step_jal_link (fx := fx) SEGS regs (Z_to_bv 64 (VAL A_TEXT + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 wz) rd immj Hf (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
  rewrite Hrd0. cbv beta iota. reflexivity.
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)).
  rewrite (l6f_pc4 k Hk).
  replace (btgt (Z_to_bv 64 (VAL A_TEXT + k)) (bv_signed immj)) with (Z_to_bv 64 (SIGMA s)).
  + apply HK.
  + unfold btgt, v_addi. rewrite unsigned_lit_small by lia. apply bv_eq. rewrite !Z_to_bv_unsigned.
    rewrite <- Ht. unfold zcanon, M64, bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma l6f_step_call : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z) (s : asym) (rd rd' : bv 5),
  0 <= k < 2 ^ 40 ->
  plookup (@pl_tpi _ PL_102_B) k = Some (PCall s rd) -> rd = rd' ->
  (forall X, SRr SEGS W (mkCfg (@YK11.mkst fx (regupd regs rd' (Z_to_bv 64 (BASE + (k + 4))))
     (Z_to_bv 64 (SIGMA s)) mem (YK11.seg_rom SEGS)) (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof. exact (l6f_step_callR (@wle SEGS)). Qed.

(* a listing slot is an image byte (YC1fP.v pa_slot_img's proof, ending at in_img) *)
Lemma l6f_slot_img : forall k e, 0 <= k < 2 ^ 40 -> plookup (@pl_tpi _ PL_102_B) k = Some e -> in_img SEGS (BASE + k).
Proof.
intros k e Hk40 Hk. pose proof (@pa_B_ok rc B_prog_listing PA) as (HB0 & HB1 & _).
rewrite <- (@pl_tpi_eq _ PL_102_B) in Hk.
pose proof (cert_slot asym (clookup pa_tbl) VAL SIGMA B_prog_listing pa_cert k e Hk) as [Hc Hk0].
unfold pi_slot_check in Hc.
destruct (clookup pa_tbl (VAL A_TEXT + k)) as [wz|] eqn:Hf; [|discriminate].
pose proof (pa_tbl_ok _ _ Hf) as Hfw.
unfold fetch_word in Hfw. destruct (negb _); [discriminate|].
unfold code_read in Hfw.
destruct (find_segment SEGS (bv_unsigned (Z_to_bv 64 (VAL A_TEXT + k))) (Z.of_N 4)) as [sg|] eqn:Hfs; [|discriminate].
destruct (find_segment_hit _ _ _ _ Hfs) as (Hin & Hlo & Hhi).
rewrite unsigned_lit_small in Hlo, Hhi by lia.
exists sg. split; [exact Hin|]. change (Z.of_N 4) with 4 in Hhi. lia.
Qed.
End S.

(* ---------------------------------------------------------------------- *)
(* 5. The frame of the cut: geometry, the image band, block / frame separation, the frame's shadow bytes. *)
Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {PA : @PAImg rc B_prog_listing}.
Variable B : asyms.
#[local] Notation SEGS := (@pa_segs rc B_prog_listing PA).
#[local] Notation ARc := (@ec_ARx rc ci cp B_prog_listing PA B).

Lemma l6f_LAWS : AR_laws_x SEGS B ARc cf_head.
Proof. exact (AR_laws_x_xs SEGS B (AR_laws_ok_cf SEGS B)). Qed.

(* the reader's eight bytes, in the representation the chunks are stated over (Ent102L6AEnt.v l6_rd64_val) *)
Lemma l6f_rd64_val : forall (H : word -> bool) (m : word -> option byte) a v,
  rd64 (aview SEGS H m) a v -> val_mem SEGS (mrestrict H m) a 8 v.
Proof.
intros H m a v Hr k Hk.
specialize (Hr k Hk). unfold aview in Hr.
destruct (mbyte SEGS (mrestrict H m) (a + Z.of_nat k)) as [b|] eqn:Eb;
cbn [option_map] in Hr; [|discriminate Hr].
injection Hr as Hr. f_equal.
transitivity (Z_to_bv 8 (bv_unsigned b)); [symmetry; apply Z_to_bv_bv_unsigned|].
f_equal. exact Hr.
Qed.

(* THE GEOMETRY of the call's fake frame (Ent102L6AEnt.v l6_geom, by path) *)
Lemma l6f_geom : forall ly S Hp (W : world SEGS) mem md pos fr,
  ARcf SEGS B ly S Hp W mem md -> In (LLVMF_FS_CLASS, pos) (frames S) ->
  fr = frame_addr ly LLVMF_FS_CLASS pos ->
  fr mod 32 = 0 /\ 4096 <= fr /\ fr + EC_FRAME_BYTES <= YM05.alloc_ceiling /\ in_app fr EC_FRAME_BYTES /\
  (forall a, fr <= a < fr + EC_FRAME_BYTES ->
     apresent (w_H W) mem a /\ ~ aowned B ly S a /\ ~ in_img SEGS a) /\
  (forall i, 0 <= i < EC_FRAME_BYTES / 8 ->
     apresent (w_H W) mem (shadow_addr fr + i) /\ ~ aowned B ly S (shadow_addr fr + i)).
Proof.
intros ly S Hp W mem md pos fr HAR Hin ->.
assert (HFB : fs_frame_bytes LLVMF_FS_CLASS = EC_FRAME_BYTES) by (vm_compute; reflexivity).
assert (HFB8 : fs_frame_bytes LLVMF_FS_CLASS / 8 = 16) by (vm_compute; reflexivity).
change (EC_FRAME_BYTES / 8) with 16.
destruct (alc_frames SEGS B (AR_laws_ok_cf SEGS B) ly S Hp W mem md LLVMF_FS_CLASS pos HAR Hin)
  as (Hal & Happ & Hfpres & Hshpres).
destruct (alc_sep SEGS B (AR_laws_ok_cf SEGS B) ly S Hp W mem md HAR) as (_ & Hfor).
rewrite Forall_forall in Hfor.
destruct (Hfor (LLVMF_FS_CLASS, pos) Hin) as (Hlo & Hhi). cbn [fst snd] in Hlo, Hhi.
rewrite HFB in Happ, Hfpres, Hhi. rewrite HFB8 in Hshpres.
assert (HIMG : forall a, frame_addr ly LLVMF_FS_CLASS pos <= a < frame_addr ly LLVMF_FS_CLASS pos + EC_FRAME_BYTES ->
  ~ in_img SEGS a).
{ intros a Ha.
  assert (Hcase : (exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
    (exists cid ps, In (cid, ps) (frames S) /\
       frame_addr ly cid ps <= a < frame_addr ly cid ps + fs_frame_bytes cid) \/
    (exists cid ps, In (cid, ps) (frames S) /\ a = flag_addr ly cid ps)).
  { right; left. exists LLVMF_FS_CLASS, pos. split; [exact Hin|]. rewrite HFB. exact Ha. }
  exact (proj2 (alc_client_img SEGS B (AR_laws_ok_cf SEGS B) ly S Hp W mem md a HAR Hcase)). }
split; [exact Hal|].
split; [exact Hlo|].
split; [exact Hhi|].
split; [exact Happ|].
split; [intros a Ha; destruct (Hfpres a Ha) as (P & O);
        split; [exact P|]; split; [exact O|]; apply HIMG; exact Ha|].
exact Hshpres.
Qed.

(* every image byte is in [kImgLo, kImgEnd): ARx's image law and layout_ok's lo_img *)
Lemma l6f_img_bounds : forall ly S Hp (W : world SEGS) mem md a,
  ARc ly S Hp W mem md -> in_img SEGS a -> kImgLo <= a < kImgEnd.
Proof.
intros ly S Hp W mem md a HAR (sg & Hsg & Hlo & Hhi).
destruct (alx_img SEGS B ARc l6f_LAWS ly S Hp W mem md HAR) as [Hseg _].
destruct (Hseg sg Hsg) as [A1 A2].
pose proof (lo_img _ (alx_layout_ok SEGS B ARc l6f_LAWS ly S Hp W mem md HAR)) as (E1 & _ & E3 & _).
lia.
Qed.

(* a live block and a live fake frame share no byte (ARx's separation law) *)
Lemma l6f_blk_frame : forall ly S Hp (W : world SEGS) mem md b m cid pos a,
  ARc ly S Hp W mem md -> In (b, m) (ablocks B ly S) -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid -> ~ (b <= a < b + req_size m).
Proof.
intros ly S Hp W mem md b m cid pos a HAR Hb Hf Ha Hba.
destruct (alx_sep SEGS B ARc l6f_LAWS ly S Hp W mem md HAR) as (Hpw & _).
pose proof (l6f_pw_cross zdisjoint _ _ _ _ Hpw
  (in_map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) _ (b, m) Hb)
  (in_map (fun f : Z * Z => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) _ (cid, pos) Hf)) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* a byte string is kept where the view is kept *)
Lemma l6f_garr8_kept : forall (H H' : word -> bool) (m m' : word -> option byte) base l,
  (forall i, 0 <= i < Z.of_nat (length l) -> aview SEGS H' m' (base + i) = aview SEGS H m (base + i)) ->
  garr8 SEGS (mrestrict H m) base l -> garr8 SEGS (mrestrict H' m') base l.
Proof.
intros H H' m m' base l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
intros q Hq. replace q with 0%nat by lia. rewrite <- (Hv 0%nat ltac:(lia)).
apply prh_mbyte_of_aview.
replace (base + Z.of_nat j + Z.of_nat 0) with (base + Z.of_nat j) by lia.
apply Hk. lia.
Qed.

(* bytes 4 .. 10 of the frame's sixteen shadow bytes read 0 (ec_frame_shadow) *)
Lemma l6f_shadow_zero : forall (H : word -> bool) (m : word -> option byte) s,
  garr8 SEGS (mrestrict H m) s ec_frame_shadow -> forall j, 4 <= j <= 10 -> aview SEGS H m (s + j) = Some 0.
Proof.
intros H m s Hg j Hj.
replace j with (Z.of_nat (Z.to_nat j)) by lia.
assert (Hj' : (4 <= Z.to_nat j <= 10)%nat) by lia.
set (n := Z.to_nat j) in *. clearbody n. clear j Hj.
assert (Hn : nth n ec_frame_shadow 0 = 0).
{ do 11 (destruct n as [|n]; [first [vm_compute; reflexivity | lia] |]). lia. }
destruct (Hg n ltac:(change (length ec_frame_shadow) with 16%nat; lia)) as [Hv _].
specialize (Hv 0%nat ltac:(lia)).
replace (s + Z.of_nat n + Z.of_nat 0) with (s + Z.of_nat n) in Hv by lia. rewrite Hn in Hv.
unfold aview. rewrite Hv. vm_compute. reflexivity.
Qed.
End G.
