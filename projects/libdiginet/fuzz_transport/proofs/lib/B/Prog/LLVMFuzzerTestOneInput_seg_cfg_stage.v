(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AFip.v (segA: the run of a
   wrapper over its own instruction table, the application of a runtime-entry contract at a call site and the
   rebuilding of the symbolic state after the call), A/AFis.v (at_ST's frame and window conjuncts,
   kept_of_frame, chunk_val_at) and A/AF0x.v (st_ok_pin_reg, the val_mem / apresent / fpchain helpers) to
   libreac/fuzz_decode's calloc wrapper in image A (fuzz_decode.asan); module paths changed, and every address,
   cell and offset below is decode's own. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/DecodeCallocWrap.v, with its module paths and module names changed; 3365 of its 3449 lines of code are new or changed and 788 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/LLVMFuzzerTestOneInput_seg_cfg.v; 602 of its 796 lines of code are new or changed and 3255 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_cfg_stage: proves no function (kind: the stage of the CFG segment of
   LLVMFuzzerTestOneInput's image-B walk).

   Lemma lc_cfg_stage_ok : lc_cfg_stage_stmt B MT XL RLO RHI (lib/B/Prog/LLVMFuzzerTestOneInput_seg_cfg_cut.v), from
   the return of diginet_session_config_default (+0x358, lc_st_cfgd of LLVMFuzzerTestOneInput_segs.v) to the return of
   the second __asan_memcpy (+0x3a0, the cut file's lc_st_cfgc).

   The code (lib/B/Prog/DgnTransportBList.v; offsets from the entry 0x812a0):
     run 1   +0x358 .. +0x368  a1 = HOST (object 6), a2 = 6, a0 = s5 (g_cfg), `jal __asan_memcpy` (0x81608);
     call 1                    __asan_memcpy (g_cfg, HOST, 6);
     run 2   +0x36c .. +0x39c  a0 = s8 & 1, a1 = bit 1 of s8, s6 = bit 2 of s8 (`slli; srli`), `sw s6, 12(s5)`,
                               `sw a0, 16(s5)`, `sw a1, 20(s5)`, a0 = s5 + 6, a1 = DESK (object 7), a2 = 6,
                               `jal __asan_memcpy` (0x8163c);
     call 2                    __asan_memcpy (g_cfg + 6, DESK, 6).
   No instrumented check and no UBSan test is on the stage.

   The walk. Each run is lib/B/Prog/TransportGRunB.v paj_run_x over the walk's G journal from a fresh symbolic state
   (the registers at the run's start as atoms 0 .. 31); run 2's three stores are bytes of G (awr_ok_x_cons_g). Each
   call is lib/A/Prog/TransportGCg.v gx_intrin_at at lp_memcpy: the destination lies in g_cfg (a row of G), its shadow
   from the record fact trans_scfg_cells (lp_scfg_cells); the source's facts are the kit statement K2
   (lc_src_ro_stmt at TRANS_HOST and TRANS_DESK) through DgnTransportBCg.v trans_src_ok_rd at the call state, where
   lc_core holds by LLVMFuzzerTestOneInput_st.v lc_core_kept_run; HOST's and DESK's bytes are K1's (lc_rom_view_stmt)
   at the same state, read by st.v lc_rom_bytes. The world moves by the cut file's lc_cfg_b1: TWorldG.v tw_fill for
   the two copies and tw_write for the three flag words, over a reader patched range by range (cs_rdp), closed by
   cs_wclose. The core, the frame's shadow, io and the spill slots are kept: the stage writes g_cfg [0, 24) and the
   ESTACK window below s1 only (cs_wr). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YI16 YE00 YE01 YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v YE2k YCfn Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBCg TransportGRwB TransportGRunB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_config_default_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st
LLVMFuzzerTestOneInput_seg_cfg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TSess0 TOps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* ------------------------------------------------------------------ *)
(* 0. The stage's constants and the image's values                     *)
(* ------------------------------------------------------------------ *)

(* The return offset of the first __asan_memcpy (+0x36c); that of the second is the cut file's CF_RC2 (+0x3a0). *)
Definition CS_RET1 : Z := 0x36c.
Definition CS_B0 : Z * Z := (0, 0).
Definition CS_Bx : sv := SLit 0.

Section vals. Context {rc : YM05.RunCeil}.
(* The listing's objects the stage names: HOST (object 6) and DESK (object 7). *)
Lemma cs_vals : VAL (A_OBJ 6) = TRANS_HOST /\ VAL (A_OBJ 7) = TRANS_DESK.
Proof. vm_compute. repeat split. Qed.

Lemma cs_pc_cfgd : w64 (transportb_text + LO_CFGD) = Z_to_bv 64 (BASE + LO_CFGD).
Proof. unfold w64. f_equal; vm_compute; reflexivity. Qed.

Lemma cs_pc_ret2 : Z_to_bv 64 (BASE + CF_RC2) = w64 (transportb_text + CF_RC2).
Proof. unfold w64. f_equal; vm_compute; reflexivity. Qed.
End vals.

(* ------------------------------------------------------------------ *)
(* 1. The flag bits and the world                                      *)
(* ------------------------------------------------------------------ *)

(* The three flag words the code stores: `srli (slli s8 61) 63`, `srli (slli s8 62) 63` and `andi s8, 1`, decided over
   every byte value. *)
Lemma cs_bit_chk :
  tw_allz (fun f =>
    (zalu64 ALU_SRL (zalu64 ALU_SLL f 61) 63 =? Z.land (Z.shiftr f 2) 1) &&
    (zalu64 ALU_SRL (zalu64 ALU_SLL f 62) 63 =?
       (if Z.land f 2 =? 0 then TS0.DIGINET_SUM_BODY else TC.DIGINET_SUM_ZERO)) &&
    (zalu64 ALU_AND f 1 =? Z.land f 1)) 0 (Z.to_nat 256) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cs_bits : forall f, 0 <= f < 256 ->
  zalu64 ALU_SRL (zalu64 ALU_SLL f 61) 63 = Z.land (Z.shiftr f 2) 1 /\
  zalu64 ALU_SRL (zalu64 ALU_SLL f 62) 63 =
    (if Z.land f 2 =? 0 then TS0.DIGINET_SUM_BODY else TC.DIGINET_SUM_ZERO) /\
  zalu64 ALU_AND f 1 = Z.land f 1.
Proof.
intros f Hf.
pose proof (tw_allz_ok _ (Z.to_nat 256) 0 cs_bit_chk f ltac:(rewrite Z2Nat.id by lia; lia)) as H.
cbv beta in H. apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H. destruct H as [H1 H2].
split; [apply Z.eqb_eq; exact H1|]. split; [apply Z.eqb_eq; exact H2 | apply Z.eqb_eq; exact H3].
Qed.

Lemma cs_land1 : forall x, 0 <= x -> 0 <= Z.land x 1 <= 1.
Proof.
intros x Hx. split; [apply Z.land_nonneg; left; exact Hx|].
replace (Z.land x 1) with (x mod 2 ^ 1) by (rewrite <- (Z.land_ones x 1) by lia; reflexivity).
pose proof (Z.mod_pos_bound x (2 ^ 1) ltac:(lia)). lia.
Qed.

Lemma cs_at8 : forall D i, 0 <= DSpec.at8 D i < 256.
Proof.
intros D i. unfold DSpec.at8, DSpec.bz. pose proof (bv_unsigned_in_range 8 (nth i D (DSpec.b8 0))) as R.
unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

Lemma cs_flags_rng : forall D, 0 <= lc_flags D < 256.
Proof.
intros D. unfold lc_flags, TOP.fuzz_u8_m. destruct (TOP.fi_n (TOP.fuzz_in_m (Z.of_nat (length D))) =? 0).
- cbn [snd]. lia.
- cbn [snd]. apply cs_at8.
Qed.

(* The bytes written so far, as a list of (base, length) ranges, and the reader that is the stage's last memory on
   them and the cut's memory elsewhere. Each write of the stage extends the list by its own range, so the kept side
   of TWorldG.v tw_write / tw_fill holds by the list's own shape. *)
Definition cs_in (l : list (Z * Z)) (a : Z) : bool :=
  existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) l.
Definition cs_rdp (l : list (Z * Z)) (rd' rd : Z -> option Z) : Z -> option Z :=
  fun a => if cs_in l a then rd' a else rd a.

Lemma cs_rdp_hd : forall b n l rd' rd a, b <= a < b + n -> cs_rdp ((b, n) :: l) rd' rd a = rd' a.
Proof.
intros b n l rd' rd a Ha. unfold cs_rdp, cs_in. cbn [existsb fst snd].
rewrite (proj2 (Z.leb_le b a) ltac:(lia)), (proj2 (Z.ltb_lt a (b + n)) ltac:(lia)). reflexivity.
Qed.

Lemma cs_rdp_tl : forall b n l rd' rd a, ~ (b <= a < b + n) -> cs_rdp ((b, n) :: l) rd' rd a = cs_rdp l rd' rd a.
Proof.
intros b n l rd' rd a Ha. unfold cs_rdp, cs_in. cbn [existsb fst snd].
destruct (Z.leb_spec b a) as [H1|H1]; destruct (Z.ltb_spec a (b + n)) as [H2|H2];
  cbn [andb orb]; first [reflexivity | lia].
Qed.

(* One store of m bytes of v at offset k of the row (o, b, n). *)
Lemma cs_wstep : forall (l : list (Z * Z)) (rd rd' : Z -> option Z) Bw o b n k (m : nat) (v : Z),
  In (o, b, n) TMAP_B -> 0 <= k -> k + Z.of_nat m <= n ->
  tw_at TMAP_B (cs_rdp l rd' rd) Bw ->
  (forall j, (j < m)%nat -> rd' (b + k + Z.of_nat j) = Some (YO0f.le_byte v m j)) ->
  tw_at TMAP_B (cs_rdp ((b + k, Z.of_nat m) :: l) rd' rd) (TW.upd Bw (o + k) (TW.put m v)).
Proof.
intros l rd rd' Bw o b n k m v Hin Hk Hkm Hat Hv.
apply (tw_write TMAP_B (cs_rdp l rd' rd) _ Bw o b n k m v TMAP_B_ok Hat Hin Hk Hkm).
- intros j Hj. pose proof (inj_lt j m Hj) as Hjz. pose proof (Nat2Z.is_nonneg j) as Hj0.
  rewrite (cs_rdp_hd (b + k) (Z.of_nat m) l rd' rd (b + k + Z.of_nat j) ltac:(lia)). exact (Hv j Hj).
- intros x Hx Hn. exact (cs_rdp_tl (b + k) (Z.of_nat m) l rd' rd x Hn).
Qed.

(* One span filled with the byte list src at offset k of the row (o, b, n): the __asan_memcpy post's form. *)
Lemma cs_fstep : forall (l : list (Z * Z)) (rd rd' : Z -> option Z) Bw o b n k (src : list byte),
  In (o, b, n) TMAP_B -> 0 <= k -> k + Z.of_nat (length src) <= n ->
  tw_at TMAP_B (cs_rdp l rd' rd) Bw ->
  (forall i, 0 <= i < Z.of_nat (length src) ->
     rd' (b + k + i) = Some (bv_unsigned (nth (Z.to_nat i) src (Z_to_bv 8 0)))) ->
  tw_at TMAP_B (cs_rdp ((b + k, Z.of_nat (length src)) :: l) rd' rd) (TW.upd Bw (o + k) src).
Proof.
intros l rd rd' Bw o b n k src Hin Hk Hkm Hat Hv.
apply (tw_fill TMAP_B (cs_rdp l rd' rd) _ Bw o b n k src TMAP_B_ok Hat Hin Hk Hkm).
- intros i Hi. rewrite (cs_rdp_hd (b + k) (Z.of_nat (length src)) l rd' rd (b + k + i) ltac:(lia)).
  exact (Hv i Hi).
- intros x Hx Hn. exact (cs_rdp_tl (b + k) (Z.of_nat (length src)) l rd' rd x Hn).
Qed.

(* Once every written range is in the list, the patched reader is the last memory's. *)
Lemma cs_wclose : forall l (rd rd' : Z -> option Z) Bw,
  tw_at TMAP_B (cs_rdp l rd' rd) Bw ->
  (forall x, tw_in TMAP_B x -> cs_in l x = false -> rd' x = rd x) ->
  tw_at TMAP_B rd' Bw.
Proof.
intros l rd rd' Bw Hat Hk. apply (tw_kept TMAP_B (cs_rdp l rd' rd) rd' Bw Hat).
intros x Hx. unfold cs_rdp. destruct (cs_in l x) eqn:E; [reflexivity | exact (Hk x Hx E)].
Qed.

(* the first range of a cs_in list that holds x; the scan is linear in the list *)
Ltac cs_hit :=
  repeat (apply orb_true_iff;
          ((left; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia) || right)).

(* The world after the stage's five updates (lc_cfg_b1's chain: host_mac, auto_wake, sum_mode, desk_mac_set,
   desk_mac), from the relation at the world before and the bytes the view rd' shows in g_cfg [0, 24). *)
Lemma cs_tw : forall (rd rd' : Z -> option Z) (B1 : list byte) (aw sm dms : Z),
  tw_at TMAP_B rd B1 ->
  (forall i, 0 <= i < Z.of_nat (length TC.HOST) ->
     rd' (TB_g_cfg + 0 + i) = Some (bv_unsigned (nth (Z.to_nat i) TC.HOST (Z_to_bv 8 0)))) ->
  (forall j, (j < 4)%nat -> rd' (TB_g_cfg + 16 + Z.of_nat j) = Some (YO0f.le_byte aw 4 j)) ->
  (forall j, (j < 4)%nat -> rd' (TB_g_cfg + 20 + Z.of_nat j) = Some (YO0f.le_byte sm 4 j)) ->
  (forall j, (j < 4)%nat -> rd' (TB_g_cfg + 12 + Z.of_nat j) = Some (YO0f.le_byte dms 4 j)) ->
  (forall i, 0 <= i < Z.of_nat (length TC.DESK) ->
     rd' (TB_g_cfg + 6 + i) = Some (bv_unsigned (nth (Z.to_nat i) TC.DESK (Z_to_bv 8 0)))) ->
  (forall x, tw_in TMAP_B x -> ~ (TB_g_cfg <= x < TB_g_cfg + 24) -> rd' x = rd x) ->
  tw_at TMAP_B rd'
    (TW.set_Cfg_desk_mac
       (TW.set_Cfg_desk_mac_set
          (TW.set_Cfg_sum_mode (TW.set_Cfg_auto_wake (TW.set_Cfg_host_mac B1 TC.HOST) aw) sm) dms) TC.DESK).
Proof.
intros rd rd' B1 aw sm dms HTW H0 H16 H20 H12 H6 Hkept.
assert (LH : Z.of_nat (length TC.HOST) = 6) by reflexivity.
assert (LD : Z.of_nat (length TC.DESK) = 6) by reflexivity.
assert (S0 : tw_at TMAP_B (cs_rdp [] rd' rd) B1).
{ apply (tw_kept TMAP_B rd); [exact HTW|]. intros x Hx. reflexivity. }
unfold TW.set_Cfg_desk_mac, TW.set_Cfg_desk_mac_set, TW.set_Cfg_sum_mode, TW.set_Cfg_auto_wake,
  TW.set_Cfg_host_mac, TW.A_Cfg_desk_mac, TW.A_Cfg_desk_mac_set, TW.A_Cfg_sum_mode, TW.A_Cfg_auto_wake,
  TW.A_Cfg_host_mac.
pose proof (cs_fstep _ rd rd' _ TW.OFF_g_cfg TB_g_cfg TW.SZ_g_cfg 0 TC.HOST TMAP_B_g_cfg
  ltac:(lia) ltac:(rewrite LH; unfold TW.SZ_g_cfg; lia) S0 H0) as S1.
pose proof (cs_wstep _ rd rd' _ TW.OFF_g_cfg TB_g_cfg TW.SZ_g_cfg 16 4 aw TMAP_B_g_cfg
  ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia) S1 H16) as S2.
pose proof (cs_wstep _ rd rd' _ TW.OFF_g_cfg TB_g_cfg TW.SZ_g_cfg 20 4 sm TMAP_B_g_cfg
  ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia) S2 H20) as S3.
pose proof (cs_wstep _ rd rd' _ TW.OFF_g_cfg TB_g_cfg TW.SZ_g_cfg 12 4 dms TMAP_B_g_cfg
  ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia) S3 H12) as S4.
pose proof (cs_fstep _ rd rd' _ TW.OFF_g_cfg TB_g_cfg TW.SZ_g_cfg 6 TC.DESK TMAP_B_g_cfg
  ltac:(lia) ltac:(rewrite LD; unfold TW.SZ_g_cfg; lia) S4 H6) as S5.
apply (cs_wclose _ rd rd' _ S5).
intros x Hx Hf. apply Hkept; [exact Hx|]. intros Hr.
rewrite LH, LD in Hf. change (Z.of_nat 4) with 4 in Hf. unfold cs_in in Hf. cbn [existsb fst snd] in Hf.
rewrite <- Bool.not_true_iff_false in Hf. apply Hf. cs_hit.
Qed.

(* A value read back from a region's chunk, as the view's bytes. *)
Lemma cs_vb : forall (Hh : word -> bool) (mm : word -> option byte) a (w : nat) v,
  YI04.val_mem tfibsegs (mrestrict Hh mm) a w v ->
  forall j, (j < w)%nat -> aview tfibsegs Hh mm (a + Z.of_nat j) = Some (YO0f.le_byte v w j).
Proof.
intros Hh mm a w v HV j Hj. unfold aview. rewrite (HV j Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. apply bv_wrap_small.
change (bv_modulus 8) with 256. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

(* A payload byte of g_cfg is a byte of G. *)
Lemma cs_inG : forall a, TB_g_cfg <= a < TB_g_cfg + 60 -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (TB_g_cfg, TW.SZ_g_cfg).
split; [exact (TMAP_B_in_G _ _ _ TMAP_B_g_cfg) | unfold in_zr, TW.SZ_g_cfg; cbn [fst snd]; lia].
Qed.

(* HOST's and DESK's six bytes are read-only bytes the walk reads (TRANS_RO_RD). *)
Lemma cs_host_ro : forall i, 0 <= i < 6 -> trans_in_ro_rd (TRANS_HOST + i).
Proof.
intros i Hi. unfold trans_in_ro_rd. apply Exists_exists. exists (TRANS_HOST, 6). split.
- unfold TRANS_RO_RD, TRANS_RO_GLOBALS. apply in_or_app. right. cbn [In]. right. left. reflexivity.
- unfold in_zr. cbn [fst snd]. lia.
Qed.
Lemma cs_desk_ro : forall i, 0 <= i < 6 -> trans_in_ro_rd (TRANS_DESK + i).
Proof.
intros i Hi. unfold trans_in_ro_rd. apply Exists_exists. exists (TRANS_DESK, 6). split.
- unfold TRANS_RO_RD, TRANS_RO_GLOBALS. apply in_or_app. right. cbn [In]. do 2 right. left. reflexivity.
- unfold in_zr. cbn [fst snd]. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The symbolic states of the two runs                              *)
(* ------------------------------------------------------------------ *)

(* run 2, from +0x36c: s5 (atom 21) = g_cfg; the three flag words g_cfg [12, 24). *)
Definition cs_rg : YP09.region := YP09.mkRegion (Some 21%nat) 12 24 12 24 [].
Definition cs_ss2 : sstate :=
  mkSS CS_RET1 sr_atoms [cs_rg] None (mkFacts [(21%nat, mkAF TB_g_cfg TB_g_cfg 5)] [] []).

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac cs_reg HS r v H tac :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* The awr obligation's regions, computed. *)
Ltac cs_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* The windows of a run, each closed by tac. *)
Ltac cs_win tac :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in
  let x := fresh "x" in let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros b wlo whi x Hin Hx;
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.
(* Region i of the symbolic state HS, at the machine state's memory. *)
Ltac cs_region HS i HR :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (apply (can_region_nth Ex ssx (restrict Hh msx) i r0 HS); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.
Ltac cs_name HS x :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ _ _ (restrict _ ?m) => rename m into x
  | st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into x
  end.

Section ent. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.

Definition cs_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs []).

Lemma cs_ew_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (cs_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold cs_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma cs_env_img : forall regs, img_env VAL A_LIM (cs_E regs).
Proof. intros regs. unfold cs_E. apply Eimg_env. Qed.
Lemma cs_img_val : forall regs (a : nat) v, (A_TEXT <= a < A_LIM)%nat -> VAL a = v -> bv_unsigned (ew (cs_E regs) a) = v.
Proof. intros regs a v Ha Hv. rewrite (cs_env_img regs a Ha). exact Hv. Qed.

(* The callee-saved registers the stage's runs carry (sp, gp, tp, s0, s1, s2, s3, s4, s5, s7, s8, s10); run 2 writes
   s6. *)
Definition cs_rk (r0 r1 : bvmap 5 word) : Prop :=
  forall n, n = 2 \/ n = 3 \/ n = 4 \/ n = 8 \/ n = 9 \/ n = 18 \/ n = 19 \/ n = 20 \/ n = 21 \/ n = 23 \/ n = 24 \/
    n = 26 -> YK11.getr r1 (Z_to_bv 5 n) = YK11.getr r0 (Z_to_bv 5 n).
Lemma cs_rk_cs : forall n : Z, n = 2 \/ n = 3 \/ n = 4 \/ n = 8 \/ n = 9 \/ n = 18 \/ n = 19 \/ n = 20 \/ n = 21 \/
  n = 23 \/ n = 24 \/ n = 26 -> acallee_saved n.
Proof. intros n Hn. unfold acallee_saved. repeat (destruct Hn as [-> | Hn]; [lia|]). subst n. lia. Qed.
Lemma cs_rk_pres : forall r0 r1 r2, cs_rk r0 r1 -> aregs_preserved r1 r2 -> cs_rk r0 r2.
Proof. intros r0 r1 r2 H1 H2 n Hn. rewrite (H2 n (cs_rk_cs n Hn)). exact (H1 n Hn). Qed.

(* A symbolic state with no region holds of any machine state at its pc (run 1). *)
Lemma cs_entry0 : forall (W : world segs) regs mem (pc : Z),
  st_ok_pi segs VAL (cs_E regs) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem pc. rewrite restrict_mkst_fx.
  apply (pa_entry_st_ok_full (PI := PI_transportb)).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* The entry state of run 2. *)
Lemma cs_entry2 : forall (W : world segs) regs mem,
  YK11.getr regs 21 = w64 TB_g_cfg ->
  st_ok_pi segs VAL (cs_E regs) cs_ss2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + CS_RET1)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem R21.
  rewrite restrict_mkst_fx. unfold cs_ss2.
  assert (U21 : bv_unsigned (ew (cs_E regs) 21) = TB_g_cfg)
    by (rewrite (cs_ew_reg regs 21 21%bv eq_refl), R21; apply unsigned_lit_small; unfold TB_g_cfg; lia).
  apply (pa_entry_st_ok_full (PI := PI_transportb)).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [cs_rg YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U21. split; [unfold TB_g_cfg; lia|]. split; [unfold TB_g_cfg; lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (TB_g_cfg + o) G_HARNESS_B_rw). apply cs_inG. lia.
  - apply pairwise_disjoint_of_extents. unfold cs_rg, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U21. change (2 ^ 5) with 32.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold TB_g_cfg; first [lia | reflexivity].
Qed.

(* A symbolic register whose value is an atom: the machine register is that atom's value. *)
Lemma cs_reg_atom : forall (W : world segs) E ss ms (n : nat) (r : bv 5) v,
  st_ok segs E ss (restrict (w_H W) ms) -> sr_get (ss_regs ss) r = SOff n 0 -> ew E n = v ->
  YK11.getr (ms_regs ms) r = v.
Proof.
intros W E ss ms n r v HS Hg He. rewrite (st_ok_restrict_reg segs (w_H W) E ss ms r HS), Hg. cbn [sv_denot].
rewrite He, Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.
End ent.
(* A run that writes none of those registers keeps them: each is its atom at the run's end. *)
Ltac cs_rk_one HS rg :=
  lazymatch goal with |- YK11.getr (ms_regs ?m) ?r = ?v =>
    refine (cs_reg_atom _ (cs_E rg) _ m _ r v HS _ _); [reflexivity | apply cs_ew_reg; reflexivity] end.
Ltac cs_rk_run HS rg :=
  let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn;
  repeat (destruct Hn as [-> | Hn]; [cs_rk_one HS rg |]);
  subst n; cs_rk_one HS rg.

(* The value of a symbolic word, one constructor at a time. *)
Lemma cs_dn_off : forall E n k x, bv_unsigned (ew E n) = x -> sv_denot E (SOff n k) = Z_to_bv 64 (x + k).
Proof. intros E n k x H. cbn [sv_denot]. rewrite H. reflexivity. Qed.
Lemma cs_dn_alu : forall E op a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
  sv_denot E (SAlu op a b) = Z_to_bv 64 (zalu64 op x y).
Proof. intros E op a b x y Ha Hb. cbn [sv_denot]. rewrite Ha, Hb. apply zalu64_sound. Qed.
Lemma cs_dn_lit : forall E z, sv_denot E (SLit z) = Z_to_bv 64 z.
Proof. reflexivity. Qed.
Ltac cs_dn U :=
  lazymatch goal with
  | |- sv_denot ?E (SLit ?z) = _ => apply cs_dn_lit
  | |- sv_denot ?E (SOff ?n ?k) = _ => apply (cs_dn_off E n k _ U)
  | |- sv_denot ?E (SAlu ?op ?a ?b) = _ => eapply cs_dn_alu; [cs_dn U | cs_dn U]
  end.
(* the range goal of a value read back, its power computed *)
Ltac cs_rng :=
  lazymatch goal with |- 0 <= ?v < 2 ^ (8 * Z.of_N ?w) =>
    let p := eval vm_compute in (8 * Z.of_N w) in change (0 <= v < 2 ^ p) end.

(* ------------------------------------------------------------------ *)
(* 3. g_cfg's shadow, the bytes the stage writes, the cut              *)
(* ------------------------------------------------------------------ *)

Section stage. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.

(* A range of g_cfg is addressable at every AR state: the shadow of g_cfg's 7 whole granules is 0 and the shadow
   byte of its last granule is 4 (trans_scfg_cells). *)
Lemma cs_cfg_ra : forall ly S (W : world segs) mem md q n,
  trans_scfg_cells B -> @AR rc segs B ly S W mem md ->
  TB_g_cfg <= q -> q + n <= TB_g_cfg + 60 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF q n.
Proof.
intros ly S W mem md q n [HZ HC] HAR Hq Hn x Hx.
assert (EC : SCFG_C = 6155520) by reflexivity.
assert (EG : TB_g_cfg = 6155520) by reflexivity.
rewrite EG in Hq, Hn.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
unfold shadow_of_addr.
destruct (Z_lt_le_dec x (SCFG_C + 56)) as [Hlt|Hge].
- exists 0. split; [|left; reflexivity].
  assert (Hz := decode_zshadow_rd B ly S W mem md SCFG_C (SCFG_C + 56) (8 * (x / 8)) HAR
    ltac:(rewrite Z.mul_comm; apply Z_mod_mult) ltac:(lia) ltac:(lia) HZ).
  replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
  unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
- exists 4. split; [|right; split; lia].
  specialize (HC ly). destruct HAR as (Mm & _).
  pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mm) _ HC) as Hh.
  unfold cell_holds in Hh. cbn [c_at c_w YG0f.c_val z1 c1 aeval] in Hh.
  specialize (Hh 0%nat ltac:(lia)). cbn [Z.of_nat] in Hh. rewrite Z.add_0_r in Hh.
  change (YG0f.le_byte 4 1 0) with 4 in Hh.
  replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (SCFG_C + 56)); [exact Hh|].
  unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF.
  replace ((SCFG_C + 56) / 8) with 769447 by (rewrite EC; reflexivity). rewrite EC in *. lia.
Qed.

(* The shadow hull of a range of g_cfg is visible: its shadow bytes are g_cfg's eight. *)
Lemma cs_cfg_hull : forall ly S (W : world segs) mem md a n,
  trans_scfg_cells B -> @AR rc segs B ly S W mem md ->
  TB_g_cfg <= a -> 0 < n -> a + n <= TB_g_cfg + 60 ->
  shadow_hull_vis (aview segs (w_H W) mem) a n.
Proof.
intros ly S W mem md a n HSC HAR H1 Hn H2 s Hs.
assert (EG : TB_g_cfg = 6155520) by reflexivity. rewrite EG in H1, H2.
unfold shadow_addr, SHADOW_OFF in Hs.
assert (Ha8 : 769440 <= a / 8) by (apply Z.div_le_lower_bound; lia).
assert (Hb8 : (a + n - 1) / 8 < 769448) by (apply Z.div_lt_upper_bound; lia).
assert (Hlo : 268527540 <= (2147450880 + a / 8) / 8) by (apply Z.div_le_lower_bound; lia).
assert (Hhi : (2147450880 + (a + n - 1) / 8) / 8 < 268527541) by (apply Z.div_lt_upper_bound; lia).
assert (Hs2 : 2148220320 <= s < 2148220328) by lia.
destruct (cs_cfg_ra ly S W mem md (6155520 + 8 * (s - 2148220320)) 1 HSC HAR ltac:(rewrite EG; lia)
  ltac:(rewrite EG; lia) (6155520 + 8 * (s - 2148220320)) ltac:(lia)) as (v & Hv & _).
unfold shadow_of_addr, SHADOW_OFF in Hv.
replace (2147450880 + (6155520 + 8 * (s - 2148220320)) / 8) with s in Hv; [rewrite Hv; discriminate|].
replace (6155520 + 8 * (s - 2148220320)) with ((769440 + (s - 2148220320)) * 8) by lia.
rewrite Z.div_mul by lia. lia.
Qed.

(* HOST's and DESK's bytes at a state where K1 holds (st.v lc_rom_bytes at the rows of lc_rom_tab). *)
Lemma cs_host_bytes : forall (W : world tfibsegs) m, trans_rom_view_rd W m ->
  forall i, 0 <= i < 6 -> aview tfibsegs (w_H W) m (TRANS_HOST + i) =
    Some (bv_unsigned (nth (Z.to_nat i) TC.HOST (Z_to_bv 8 0))).
Proof.
intros W m HRO i Hi. rewrite HRO by (apply cs_host_ro; exact Hi).
replace (TRANS_HOST + i) with (TRANS_HOST + Z.of_nat (Z.to_nat i)) by lia.
apply lc_rom_bytes; [unfold lc_rom_tab; cbn [In]; left; reflexivity | change (length TC.HOST) with 6%nat; lia].
Qed.
Lemma cs_desk_bytes : forall (W : world tfibsegs) m, trans_rom_view_rd W m ->
  forall i, 0 <= i < 6 -> aview tfibsegs (w_H W) m (TRANS_DESK + i) =
    Some (bv_unsigned (nth (Z.to_nat i) TC.DESK (Z_to_bv 8 0))).
Proof.
intros W m HRO i Hi. rewrite HRO by (apply cs_desk_ro; exact Hi).
replace (TRANS_DESK + i) with (TRANS_DESK + Z.of_nat (Z.to_nat i)) by lia.
apply lc_rom_bytes; [unfold lc_rom_tab; cbn [In]; right; left; reflexivity | change (length TC.DESK) with 6%nat; lia].
Qed.

(* The bytes the stage may write: g_cfg [0, 24) and the ESTACK window below s1 (the two __asan_memcpy calls). *)
Definition cs_wr (cx : lcx) (a : Z) : Prop :=
  (TB_g_cfg <= a < TB_g_cfg + 24) \/ (lc_sp1 cx - ESTACK <= a < lc_sp1 cx).

(* What the core and the slot's pre fix about the stack, the frame and the input. *)
Lemma cs_num : forall cx ly' S' (W' : world segs) regs' mem' md' e,
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx -> @lc_core rc B cx ly' S' W' regs' mem' md' e ->
  alloc_ceiling + 32432 <= lc_sp1 cx /\ lc_sp0 cx - 336 <= lc_sp1 cx <= lc_sp0 cx - 320 /\
  lc_sp1 cx mod 32 = 0 /\ lc_sp0 cx <= 2 ^ 47 /\ lc_sp0 cx mod 16 = 0 /\
  4096 <= lc_F cx /\ lc_F cx mod 64 = 0 /\ lc_F cx + 256 <= alloc_ceiling /\
  (forall a, lc_F cx <= a < lc_F cx + 256 -> ~ in_img segs a) /\
  0 <= l_n cx < 2 ^ 26 /\ l_n cx = Z.of_nat (length (l_pl cx)) /\
  (0 < l_n cx -> In (l_p cx, l_n cx) (ablocks B ly' S') /\ 4096 <= l_p cx /\ l_p cx + l_n cx <= alloc_ceiling /\
     l_p cx mod 8 = 0 /\ in_app (l_p cx) (l_n cx) /\
     (forall a, l_p cx <= a < l_p cx + l_n cx -> ~ in_img segs a)) /\
  @AR rc segs B ly' S' W' mem' md'.
Proof.
intros cx ly' S' W' regs' mem' md' e LAWS HB HC.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as G.
destruct G as [HAR Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & Hsp1al & _ & HF4096 & HFal & HFceil & _).
destruct Hstk as (Hceil & Hslo & Hshi & H47).
unfold LF_FBYTES, LF_FRAME in *.
split; [exact Hsp1c|]. split; [lia|]. split; [exact Hsp1al|]. split; [lia|]. split; [exact Hsp0al|].
split; [exact HF4096|]. split; [exact HFal|]. split; [exact HFceil|].
split.
{ intros a Ha. apply (frm_img segs B LAWS ly' S' W' mem' md' LF_CID (l_fpos cx) a HAR HFin).
  rewrite HFaddr. change (fs_frame_bytes LF_CID) with 256. exact Ha. }
split; [exact (proj1 Hn)|]. split; [exact (proj2 Hn)|].
split; [|exact HAR].
intros Hn0. pose proof (HINg Hn0) as Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hp4 & Hpc & Hpapp & _).
destruct (al_shadow _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as ((Hp8 & _ & _) & _).
assert (RQ : req_size (l_n cx) = l_n cx) by (unfold req_size; destruct (Z.eqb_spec (l_n cx) 0); lia).
rewrite RQ in Hpc, Hpapp.
split; [exact Hin|]. split; [exact Hp4|]. split; [exact Hpc|]. split; [exact Hp8|]. split; [exact Hpapp|].
intros a Ha. apply (blk_img segs B LAWS ly' S' W' mem' md' (l_p cx) (l_n cx) a HAR Hin). rewrite RQ. exact Ha.
Qed.

(* The bytes the core, the kept spill slots, the frame's shadow and io read lie outside cs_wr. *)
Lemma cs_apart : forall cx ly' S' (W' : world segs) regs' mem' md' e,
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx -> @lc_core rc B cx ly' S' W' regs' mem' md' e ->
  forall a, (lc_sp0 cx - 104 <= a < lc_sp0 cx) \/ (lc_F cx <= a < lc_F cx + 256) \/
            (0 < l_n cx /\ l_p cx <= a < l_p cx + l_n cx) \/ (lc_SH cx <= a < lc_SH cx + 32) \/
            (lc_sp1 cx + 128 <= a < lc_sp1 cx + 144) ->
    ~ cs_wr cx a /\ 0 <= a < 2 ^ 64.
Proof.
intros cx ly' S' W' regs' mem' md' e LAWS HB HC.
destruct (cs_num cx ly' S' W' regs' mem' md' e LAWS HB HC)
  as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & _).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
assert (HF8 : 0 <= lc_F cx / 8 < 2 ^ 44)
  by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
assert (EG : TB_g_cfg = 6155520) by reflexivity.
intros a Ha. unfold cs_wr, lc_SH, SHADOW_OFF, ESTACK in *.
destruct Ha as [Ha | [Ha | [[Hn0 Ha] | [Ha | Ha]]]].
- split; [intros [C|C]; lia | lia].
- split; [|lia]. intros [C|C]; [|lia].
  apply (N9 a Ha). apply trans_g_img. apply cs_inG. lia.
- destruct (N12 Hn0) as (_ & Gp4 & Gpc & _ & _ & Gpimg).
  split; [|lia]. intros [C|C]; [|lia].
  apply (Gpimg a Ha). apply trans_g_img. apply cs_inG. lia.
- split; [intros [C|C]; lia | lia].
- split; [intros [C|C]; lia | lia].
Qed.

(* lc_core at a state of the stage: the journal there, sp / gp / tp / s0 / s1 kept and every byte outside cs_wr
   kept. *)
Lemma cs_core : forall cx ly' S' (W : world segs) regs' mem' md' regsF memF mdF,
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx -> @lc_core rc B cx ly' S' W regs' mem' md' 0 ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] LLVMF_STK (lc_sp0 cx) []
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly' S' W memF mdF 0 ->
  (forall r, In r [2; 3; 4; 8; 9] -> YK11.getr regsF (Z_to_bv 5 r) = YK11.getr regs' (Z_to_bv 5 r)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ cs_wr cx a -> aview segs (w_H W) memF a = aview segs (w_H W) mem' a) ->
  (forall a, apresent (w_H W) mem' a -> apresent (w_H W) memF a) ->
  @lc_core rc B cx ly' S' W regsF memF mdF 0.
Proof.
intros cx ly' S' W regs' mem' md' regsF memF mdF LAWS HB HC HJF HR KV GP.
pose proof (cs_apart cx ly' S' W regs' mem' md' 0 LAWS HB HC) as AP.
apply (lc_core_kept_run B MT XL RLO RHI cx ly' S' W regs' mem' md' 0 ly' S' W regsF memF mdF 0 HB HC HJF
  eq_refl (Permutation_refl _)).
- exact HR.
- intros a Ha. destruct (AP a ltac:(left; exact Ha)) as [Hw Hr]. exact (KV a Hr Hw).
- intros i Hi. destruct (AP (l_p cx + i) ltac:(right; right; left; split; lia)) as [Hw Hr].
  exact (KV _ Hr Hw).
- intros a Ha. destruct (AP a ltac:(right; left; unfold LF_FBYTES in *; lia)) as [Hw Hr].
  exact (KV a Hr Hw).
- intros a Ha Hp. exact (GP a Hp).
Qed.

(* The cut at +0x3a0, from the facts the stage leaves. *)
Lemma cs_close : forall (cx : lcx) ly' S' (W : world segs) regs' mem' md' Bw0 B1 regsF memF mdF,
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_core rc B cx ly' S' W regs' mem' md' 0 -> lc_fr cx regs' ->
  lc_spills cx (lf_spill_sm (lc_F cx)) (aview segs (w_H W) mem') ->
  lc_fsh cx (aview segs (w_H W) mem') false false -> lc_io cx W mem' -> lc_meter MT cx S' 0 ->
  lc_w0 cx Bw0 -> TS0.diginet_session_config_default_m Bw0 = Some (B1, tt) ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] LLVMF_STK (lc_sp0 cx) []
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly' S' W memF mdF 0 ->
  (forall r, In r [2; 3; 4; 8; 9] -> YK11.getr regsF (Z_to_bv 5 r) = YK11.getr regs' (Z_to_bv 5 r)) ->
  YK11.getr regsF 18 = YK11.getr regs' 18 -> YK11.getr regsF 26 = YK11.getr regs' 26 ->
  lc_cur cx regsF 19 23 (lc_c1 (l_pl cx)) -> YK11.getr regsF 24 = w64 (lc_flags (l_pl cx)) ->
  YK11.getr regsF 21 = w64 TB_g_cfg -> YK11.getr regsF 20 = w64 (lc_F cx + 176) ->
  YK11.getr regsF 22 = w64 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ cs_wr cx a -> aview segs (w_H W) memF a = aview segs (w_H W) mem' a) ->
  (forall a, apresent (w_H W) mem' a -> apresent (w_H W) memF a) ->
  lc_tw W memF (lc_cfg_b1 (l_pl cx) B1) ->
  @lc_st_cfgc rc B MT cx W (lc_cfg cx CF_RC2 regsF memF mdF).
Proof.
intros cx ly' S' W regs' mem' md' Bw0 B1 regsF memF mdF LAWS HB HC HFR HSP HFSH HIO HMT HW0 HSC HJF
  HR R18 R26 HCUR R24 R21 R20 R22 KV GP HTWF.
pose proof (cs_apart cx ly' S' W regs' mem' md' 0 LAWS HB HC) as AP.
exists ly', S', regsF, memF, mdF, Bw0, B1.
split; [reflexivity|].
split; [exact (cs_core cx ly' S' W regs' mem' md' regsF memF mdF LAWS HB HC HJF HR KV GP)|].
destruct HFR as (F18 & F26).
split; [split; [rewrite R18; exact F18 | rewrite R26; exact F26]|].
split.
{ unfold lc_spills, lf_spill_sm in *.
  rewrite Forall_forall in HSP.
  pose proof (HSP (128, lc_F cx) ltac:(cbn [In]; tauto)) as H128.
  pose proof (HSP (136, lc_F cx) ltac:(cbn [In]; tauto)) as H136.
  cbn [fst snd] in H128, H136.
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - rewrite (rdword_ext (aview segs (w_H W) mem') (aview segs (w_H W) memF) (lc_sp1 cx + 128))
      by (intros j Hj; destruct (AP (lc_sp1 cx + 128 + j) ltac:(right; right; right; right; lia)) as [Hw Hr];
          exact (KV _ Hr Hw)).
    exact H128.
  - rewrite (rdword_ext (aview segs (w_H W) mem') (aview segs (w_H W) memF) (lc_sp1 cx + 136))
      by (intros j Hj; destruct (AP (lc_sp1 cx + 136 + j) ltac:(right; right; right; right; lia)) as [Hw Hr];
          exact (KV _ Hr Hw)).
    exact H136. }
split.
{ apply (lc_fsh_kept cx (aview segs (w_H W) mem')); [|exact HFSH].
  intros a Ha. destruct (AP a ltac:(right; right; right; left; exact Ha)) as [Hw Hr]. exact (KV a Hr Hw). }
split.
{ unfold lc_io in *. apply (lc_garr8_kept (w_H W) (w_H W) mem' memF (lc_F cx + 176) _); [|exact HIO].
  intros j Hj.
  lazymatch type of Hj with context [length ?l] =>
    assert (Lio : length l = 32%nat) by (vm_compute; reflexivity); rewrite Lio in Hj end.
  destruct (AP (lc_F cx + 176 + j) ltac:(right; left; unfold LF_FBYTES in *; lia)) as [Hw Hr].
  exact (KV _ Hr Hw). }
split; [exact HMT|].
split; [exact HCUR|].
split; [exact R24|]. split; [exact R21|]. split; [exact R20|]. split; [exact R22|].
split; [exact HW0|]. split; [exact HSC | exact HTWF].
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The stage                                                        *)
(* ------------------------------------------------------------------ *)

Lemma lc_cfg_stage_ok : @lc_cfg_stage_stmt rc B MT XL RLO RHI.
Proof.
unfold lc_cfg_stage_stmt. intros K1 K2 HP cx W' c' HB HST.
destruct HST as (ly' & S' & regs' & mem' & md' & Bw0 & B1 & -> & HC & HFR & HSP & HFSH & HIO & HMET & HCUR &
  R24 & R21 & R20 & HW0 & HCD & HTW).
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (lp_scfg_cells _ _ _ _ _ HP) as HSC.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
destruct (cs_num cx ly' S' W' regs' mem' md' 0 LAWS HB HC) as (N1 & N2 & N3 & N4 & N5 & _).
pose proof (@alloc_ceiling_value rc) as ((Hcmin & Hcmax) & _).
pose proof HC as (HJ & _ & _ & _ & Rsp & R8 & R9 & Rgp & Rtp & _).
pose proof HFR as (R18 & R26). pose proof HCUR as (R19 & R23).
pose proof (cs_flags_rng (l_pl cx)) as HFL.
destruct cs_vals as (VO6 & VO7).
assert (EST : ESTACK = 4096) by reflexivity.
assert (EG : TB_g_cfg = 6155520) by reflexivity.
assert (ETH : TRANS_HOST = 0x20fe0) by reflexivity.
assert (ETD : TRANS_DESK = 0x21000) by reflexivity.
assert (H16 : (lc_sp1 cx - lc_sp0 cx) mod 16 = 0).
{ pose proof (Z.div_mod (lc_sp1 cx) 32 ltac:(lia)) as D1. pose proof (Z.div_mod (lc_sp0 cx) 16 ltac:(lia)) as D2.
  replace (lc_sp1 cx - lc_sp0 cx) with ((2 * (lc_sp1 cx / 32) - lc_sp0 cx / 16) * 16) by lia. apply Z_mod_mult. }
(* ---- run 1, +0x358 .. +0x368 ---- *)
pose proof (@cs_entry0 (l_fx cx) rc W' regs' mem' LO_CFGD) as HS.
assert (HEI : img_env VAL A_LIM (cs_E regs')) by apply cs_env_img.
assert (SHOK : sh_ok segs CS_Bx (@nil shent) (cs_E regs') (mrestrict (w_H W') mem')) by constructor.
pose proof (@paj_run_x (l_fx cx) rc YE2k.tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
unfold lc_cfg. rewrite cs_pc_cfgd.
paj_run_tok RUN HS HJ SHOK CS_B0.
{ cs_awr_rs. apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md') mat md') in *. clearbody md1. clear mat.
cs_name HS ms1.
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W') (ms_mem ms1) a = aview segs (w_H W') mem' a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [cs_win ltac:(idtac) | exact Ha | intros []]. }
assert (GA1 : forall a, apresent (w_H W') mem' a -> apresent (w_H W') (ms_mem ms1) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
assert (RK1 : cs_rk regs' (ms_regs ms1)) by (cs_rk_run HS regs').
cs_reg HS (Z_to_bv 5 10) (w64 TB_g_cfg) Q10
  ltac:(cbn [sv_denot]; rewrite (eq_trans (cs_ew_reg regs' 21 21%bv eq_refl) R21), Z.add_0_r;
        apply Z_to_bv_bv_unsigned).
cs_reg HS (Z_to_bv 5 11) (w64 TRANS_HOST) Q11
  ltac:(cbn [sv_denot]; rewrite (cs_img_val regs' 247 TRANS_HOST ltac:(unfold A_TEXT, A_LIM; lia) VO6), Z.add_0_r;
        reflexivity).
cs_reg HS (Z_to_bv 5 12) (w64 6) Q12 ltac:(reflexivity).
cs_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + CS_RET1)) Q1 ltac:(apply codeptr_val; apply cs_env_img).
assert (Q2 : YK11.getr (ms_regs ms1) (2%bv : bv 5) = w64 (lc_sp1 cx)) by exact (eq_trans (RK1 2 ltac:(lia)) Rsp).
assert (Q3 : YK11.getr (ms_regs ms1) (3%bv : bv 5) = w64 (as_gp B)) by exact (eq_trans (RK1 3 ltac:(lia)) Rgp).
assert (Q4 : YK11.getr (ms_regs ms1) (4%bv : bv 5) = w64 (as_tp B)) by exact (eq_trans (RK1 4 ltac:(lia)) Rtp).
assert (HSP1 : spZ (ms_regs ms1) = lc_sp1 cx) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR1.
assert (HC1 : @lc_core rc B cx ly' S' W' (ms_regs ms1) (ms_mem ms1) md1 0).
{ apply (cs_core cx ly' S' W' regs' mem' md' (ms_regs ms1) (ms_mem ms1) md1 LAWS HB HC HJ).
  - intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; apply RK1; lia.
  - intros a Ha _. exact (KA1 a Ha).
  - exact GA1. }
pose proof (K1 HP cx ly' S' W' (ms_regs ms1) (ms_mem ms1) md1 0 HB HC1) as HRO1.
pose proof (K2 HP cx ly' S' W' (ms_regs ms1) (ms_mem ms1) md1 0 TRANS_HOST 6 HB HC1
  ltac:(cbn [In]; left; reflexivity)) as HSRC1.
destruct (trans_src_ok_rd B LAWS ly' S' W' (ms_mem ms1) md1 TRANS_HOST 6 HAR1 HSRC1 ltac:(lia))
  as (RV1 & RRA1 & RHULL1 & RAM1 & _ & _).
clear HSRC1.
(* ---- +0x368: __asan_memcpy (g_cfg, HOST, 6) ---- *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 (transportb_sigma TB___asan_memcpy)) mm rom) mdx) Q)
end.
eapply SRr_bind.
{ apply (@gx_intrin_at (l_fx cx) rc YE2k.tfib_sink_head segs B LAWS transportb_segs_low OCpy
    (transportb_sigma TB___asan_memcpy) (lp_memcpy _ _ _ _ _ HP (l_fx cx)) TG.G_HARNESS_B W' (ms_regs ms1)
    (ms_mem ms1) _ _ _ _ _ _ _ _ _ ly' S' md1 0 TB_g_cfg TRANS_HOST 6 (lc_sp1 cx - lc_sp0 cx)
    (Z_to_bv 64 (BASE + CS_RET1)) HGX G_HARNESS_B_rw HJ Q10 Q11 Q12).
  - lia.
  - unfold TB_g_cfg; lia.
  - unfold TB_g_cfg; lia.
  - rewrite HSP1. lia.
  - exact H16.
  - lia.
  - unfold LLVMF_STK. rewrite EST. lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PI_transportb)); [unfold CS_RET1; lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|]. intros a Ha. right. apply cs_inG. lia.
  - left. unfold kLowMemEnd, TB_g_cfg. lia.
  - apply (cs_cfg_ra _ _ _ _ _ _ _ HSC HAR1); lia.
  - intros _. apply (cs_cfg_hull _ _ _ _ _ _ _ HSC HAR1); lia.
  - split; [unfold TRANS_HOST; lia|]. split; [unfold TRANS_HOST; lia|].
    split; [intros a Ha; split; [exact (RV1 a Ha)|]; rewrite HSP1; lia|].
    split; [right; lia|].
    split; [exact RAM1|]. split; [exact RRA1|]. intros _. exact RHULL1. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hcpy1 & Heff1 & Hgr1).
assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> ~ cs_wr cx a -> aview segs (w_H W') mem2 a = aview segs (w_H W') mem' a).
{ intros a Ha Hn.
  rewrite (Heff1 a Ha) by (intros C; apply Hn; unfold cs_wr; first [left; lia | right; lia]).
  exact (KA1 a Ha). }
assert (GA2 : forall a, apresent (w_H W') mem' a -> apresent (w_H W') mem2 a)
  by (intros a Ha; exact (Hgr1 a (GA1 a Ha))).
assert (HOST2 : forall i, 0 <= i < 6 -> aview segs (w_H W') mem2 (TB_g_cfg + 0 + i) =
  Some (bv_unsigned (nth (Z.to_nat i) TC.HOST (Z_to_bv 8 0)))).
{ intros i Hi. replace (TB_g_cfg + 0 + i) with (TB_g_cfg + i) by lia. rewrite (Hcpy1 i Hi).
  exact (cs_host_bytes W' (ms_mem ms1) HRO1 i Hi). }
clear Heff1 Hcpy1.
assert (RK2 : cs_rk regs' regs2) by exact (cs_rk_pres _ _ _ RK1 HP2).
assert (P21 : YK11.getr regs2 21 = w64 TB_g_cfg) by exact (eq_trans (RK2 21 ltac:(lia)) R21).
(* ---- run 2, +0x36c .. +0x39c ---- *)
repeat match goal with H : img_env _ _ _ |- _ => clear H end. clear HS SHOK.
pose proof (@cs_entry2 (l_fx cx) rc W' regs2 mem2 P21) as HS.
assert (HEI : img_env VAL A_LIM (cs_E regs2)) by apply cs_env_img.
assert (SHOK : sh_ok segs CS_Bx (@nil shent) (cs_E regs2) (mrestrict (w_H W') mem2)) by constructor.
assert (U21 : bv_unsigned (ew (cs_E regs2) 21) = TB_g_cfg)
  by (rewrite (cs_ew_reg regs2 21 21%bv eq_refl), P21; apply unsigned_lit_small; unfold TB_g_cfg; lia).
assert (U24 : bv_unsigned (ew (cs_E regs2) 24) = lc_flags (l_pl cx))
  by (rewrite (cs_ew_reg regs2 24 (Z_to_bv 5 24) eq_refl), (eq_trans (RK2 24 ltac:(lia)) R24);
      apply unsigned_lit_small; lia).
paj_run_tok RUN HS HJ2 SHOK CS_B0.
{ cs_awr_rs.
  apply awr_ok_x_cons_g;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U21 in Ha; apply cs_inG; lia |].
  apply awr_ok_x_nil. }
set (md3 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md3. clear mat.
cs_name HS ms2.
assert (KA3 : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_g_cfg + 12 <= a < TB_g_cfg + 24) ->
  aview segs (w_H W') (ms_mem ms2) a = aview segs (w_H W') mem2 a).
{ intros a Ha Hn.
  apply (kept_of_frame _ _ _ _ _ (fun x => TB_g_cfg + 12 <= x < TB_g_cfg + 24) HFr); [| exact Ha | exact Hn].
  cs_win ltac:(rewrite ?U21 in Hx; cbv beta; lia). }
assert (GA3 : forall a, apresent (w_H W') mem' a -> apresent (w_H W') (ms_mem ms2) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA2 a Ha))).
clear HF HFr HG.
assert (RKr : cs_rk regs2 (ms_regs ms2)) by (cs_rk_run HS regs2).
assert (RK3 : cs_rk regs' (ms_regs ms2)) by (intros n Hn; exact (eq_trans (RKr n Hn) (RK2 n Hn))).
cs_region HS 0%nat RG0.
(* the three flag words, read back from the run's region *)
assert (HB12 : forall j, (j < 4)%nat -> aview segs (w_H W') (ms_mem ms2) (TB_g_cfg + 12 + Z.of_nat j) =
  Some (YO0f.le_byte (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1) 4 j)).
{ intros j Hj. refine (cs_vb (w_H W') (ms_mem ms2) (TB_g_cfg + 12) 4 _ _ j Hj).
  lazymatch type of RG0 with YP09.region_ok _ _ _ (YP09.mkRegion (Some ?nb) _ _ _ _ ?cs) =>
    lazymatch cs with context [YP09.mkChunk 12 (CVal ?w ?e)] =>
      refine (can_field_of_region _ _ nb _ cs _ _ _ _ 12 w e _ RG0 U21 _ _ _ _) end end.
  - cbn [In]. repeat (first [left; reflexivity | right]).
  - etransitivity; [cs_dn U24|]. rewrite ?Z.add_0_r.
    destruct (cs_bits (lc_flags (l_pl cx)) HFL) as (Cb & _ & _). rewrite Cb. reflexivity.
  - cs_rng. pose proof (cs_land1 (Z.shiftr (lc_flags (l_pl cx)) 2) ltac:(apply Z.shiftr_nonneg; lia)). lia.
  - cbn. lia. }
assert (HB16 : forall j, (j < 4)%nat -> aview segs (w_H W') (ms_mem ms2) (TB_g_cfg + 16 + Z.of_nat j) =
  Some (YO0f.le_byte (Z.land (lc_flags (l_pl cx)) 1) 4 j)).
{ intros j Hj. refine (cs_vb (w_H W') (ms_mem ms2) (TB_g_cfg + 16) 4 _ _ j Hj).
  lazymatch type of RG0 with YP09.region_ok _ _ _ (YP09.mkRegion (Some ?nb) _ _ _ _ ?cs) =>
    lazymatch cs with context [YP09.mkChunk 16 (CVal ?w ?e)] =>
      refine (can_field_of_region _ _ nb _ cs _ _ _ _ 16 w e _ RG0 U21 _ _ _ _) end end.
  - cbn [In]. repeat (first [left; reflexivity | right]).
  - etransitivity; [cs_dn U24|]. rewrite ?Z.add_0_r.
    destruct (cs_bits (lc_flags (l_pl cx)) HFL) as (_ & _ & Cb). rewrite Cb. reflexivity.
  - cs_rng. pose proof (cs_land1 (lc_flags (l_pl cx)) ltac:(lia)). lia.
  - cbn. lia. }
assert (HB20 : forall j, (j < 4)%nat -> aview segs (w_H W') (ms_mem ms2) (TB_g_cfg + 20 + Z.of_nat j) =
  Some (YO0f.le_byte (if Z.land (lc_flags (l_pl cx)) 2 =? 0 then TS0.DIGINET_SUM_BODY else TC.DIGINET_SUM_ZERO)
    4 j)).
{ intros j Hj. refine (cs_vb (w_H W') (ms_mem ms2) (TB_g_cfg + 20) 4 _ _ j Hj).
  lazymatch type of RG0 with YP09.region_ok _ _ _ (YP09.mkRegion (Some ?nb) _ _ _ _ ?cs) =>
    lazymatch cs with context [YP09.mkChunk 20 (CVal ?w ?e)] =>
      refine (can_field_of_region _ _ nb _ cs _ _ _ _ 20 w e _ RG0 U21 _ _ _ _) end end.
  - cbn [In]. repeat (first [left; reflexivity | right]).
  - etransitivity; [cs_dn U24|]. rewrite ?Z.add_0_r.
    destruct (cs_bits (lc_flags (l_pl cx)) HFL) as (_ & Cb & _). rewrite Cb. reflexivity.
  - cs_rng. unfold TS0.DIGINET_SUM_BODY, TC.DIGINET_SUM_ZERO.
    destruct (Z.land (lc_flags (l_pl cx)) 2 =? 0); lia.
  - cbn. lia. }
clear RG0.
(* the registers at the second call *)
cs_reg HS (Z_to_bv 5 10) (w64 (TB_g_cfg + 6)) Q10b ltac:(cbn [sv_denot]; rewrite U21; reflexivity).
cs_reg HS (Z_to_bv 5 11) (w64 TRANS_DESK) Q11b
  ltac:(cbn [sv_denot]; rewrite (cs_img_val regs2 248 TRANS_DESK ltac:(unfold A_TEXT, A_LIM; lia) VO7), Z.add_0_r;
        reflexivity).
cs_reg HS (Z_to_bv 5 12) (w64 6) Q12b ltac:(reflexivity).
cs_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + CF_RC2)) Q1b ltac:(apply codeptr_val; apply cs_env_img).
cs_reg HS (Z_to_bv 5 22) (w64 (Z.land (Z.shiftr (lc_flags (l_pl cx)) 2) 1)) Q22b
  ltac:(unfold w64; etransitivity; [cs_dn U24|]; rewrite ?Z.add_0_r;
        destruct (cs_bits (lc_flags (l_pl cx)) HFL) as (Cb & _ & _); rewrite Cb; reflexivity).
assert (Q2b : YK11.getr (ms_regs ms2) (2%bv : bv 5) = w64 (lc_sp1 cx)) by exact (eq_trans (RK3 2 ltac:(lia)) Rsp).
assert (Q3b : YK11.getr (ms_regs ms2) (3%bv : bv 5) = w64 (as_gp B)) by exact (eq_trans (RK3 3 ltac:(lia)) Rgp).
assert (Q4b : YK11.getr (ms_regs ms2) (4%bv : bv 5) = w64 (as_tp B)) by exact (eq_trans (RK3 4 ltac:(lia)) Rtp).
assert (HSP2 : spZ (ms_regs ms2) = lc_sp1 cx) by (unfold spZ; rewrite Q2b; unfold w64; apply unsigned_lit_small; lia).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR3.
assert (KA3' : forall a, 0 <= a < 2 ^ 64 -> ~ cs_wr cx a ->
  aview segs (w_H W') (ms_mem ms2) a = aview segs (w_H W') mem' a).
{ intros a Ha Hn. rewrite (KA3 a Ha) by (intros C; apply Hn; unfold cs_wr; left; lia). exact (KA2 a Ha Hn). }
assert (HC2 : @lc_core rc B cx ly' S' W' (ms_regs ms2) (ms_mem ms2) md3 0).
{ apply (cs_core cx ly' S' W' regs' mem' md' (ms_regs ms2) (ms_mem ms2) md3 LAWS HB HC HJ2).
  - intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; apply RK3; lia.
  - exact KA3'.
  - exact GA3. }
pose proof (K1 HP cx ly' S' W' (ms_regs ms2) (ms_mem ms2) md3 0 HB HC2) as HRO2.
pose proof (K2 HP cx ly' S' W' (ms_regs ms2) (ms_mem ms2) md3 0 TRANS_DESK 6 HB HC2
  ltac:(cbn [In]; right; left; reflexivity)) as HSRC2.
destruct (trans_src_ok_rd B LAWS ly' S' W' (ms_mem ms2) md3 TRANS_DESK 6 HAR3 HSRC2 ltac:(lia))
  as (RV2 & RRA2 & RHULL2 & RAM2 & _ & _).
clear HSRC2.
(* ---- +0x39c: __asan_memcpy (g_cfg + 6, DESK, 6) ---- *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 (transportb_sigma TB___asan_memcpy)) mm rom) mdx) Q)
end.
eapply SRr_bind.
{ apply (@gx_intrin_at (l_fx cx) rc YE2k.tfib_sink_head segs B LAWS transportb_segs_low OCpy
    (transportb_sigma TB___asan_memcpy) (lp_memcpy _ _ _ _ _ HP (l_fx cx)) TG.G_HARNESS_B W' (ms_regs ms2)
    (ms_mem ms2) _ _ _ _ _ _ _ _ _ ly' S' md3 0 (TB_g_cfg + 6) TRANS_DESK 6 (lc_sp1 cx - lc_sp0 cx)
    (Z_to_bv 64 (BASE + CF_RC2)) HGX G_HARNESS_B_rw HJ2 Q10b Q11b Q12b).
  - lia.
  - unfold TB_g_cfg; lia.
  - unfold TB_g_cfg; lia.
  - rewrite HSP2. lia.
  - exact H16.
  - lia.
  - unfold LLVMF_STK. rewrite EST. lia.
  - exact Q3b.
  - exact Q4b.
  - exact Q1b.
  - apply (ret_ok_codeptr_v (PI := PI_transportb)); [unfold CF_RC2; lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ2|]. intros a Ha. right. apply cs_inG. lia.
  - left. unfold kLowMemEnd, TB_g_cfg. lia.
  - apply (cs_cfg_ra _ _ _ _ _ _ _ HSC HAR3); lia.
  - intros _. apply (cs_cfg_hull _ _ _ _ _ _ _ HSC HAR3); lia.
  - split; [unfold TRANS_DESK; lia|]. split; [unfold TRANS_DESK; lia|].
    split; [intros a Ha; split; [exact (RV2 a Ha)|]; rewrite HSP2; lia|].
    split; [right; lia|].
    split; [exact RAM2|]. split; [exact RRA2|]. intros _. exact RHULL2. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & _ & Hcpy2 & Heff2 & Hgr2).
assert (K4m : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_g_cfg + 6 <= a < TB_g_cfg + 12) ->
  ~ (lc_sp1 cx - ESTACK <= a < lc_sp1 cx) -> aview segs (w_H W') mem4 a = aview segs (w_H W') (ms_mem ms2) a).
{ intros a Ha H1 H2. apply Heff2; [exact Ha | lia | lia]. }
assert (KV4 : forall a, 0 <= a < 2 ^ 64 -> ~ cs_wr cx a -> aview segs (w_H W') mem4 a = aview segs (w_H W') mem' a).
{ intros a Ha Hn. rewrite (K4m a Ha) by (intros C; apply Hn; unfold cs_wr; first [left; lia | right; lia]).
  exact (KA3' a Ha Hn). }
assert (GA4 : forall a, apresent (w_H W') mem' a -> apresent (w_H W') mem4 a)
  by (intros a Ha; exact (Hgr2 a (GA3 a Ha))).
assert (RK4 : cs_rk regs' regs4) by exact (cs_rk_pres _ _ _ RK3 HP4).
(* the world at the cut *)
assert (HTW4 : lc_tw W' mem4 (lc_cfg_b1 (l_pl cx) B1)).
{ unfold lc_tw in HTW |- *. unfold lc_cfg_b1. cbv zeta.
  apply (cs_tw (aview segs (w_H W') mem') (aview segs (w_H W') mem4) B1 _ _ _ HTW).
  - intros i Hi. change (Z.of_nat (length TC.HOST)) with 6 in Hi.
    rewrite K4m by lia. rewrite KA3 by lia. exact (HOST2 i Hi).
  - intros j Hj. rewrite K4m by lia. exact (HB16 j Hj).
  - intros j Hj. rewrite K4m by lia. exact (HB20 j Hj).
  - intros j Hj. rewrite K4m by lia. exact (HB12 j Hj).
  - intros i Hi. change (Z.of_nat (length TC.DESK)) with 6 in Hi.
    rewrite (Hcpy2 i Hi). exact (cs_desk_bytes W' (ms_mem ms2) HRO2 i Hi).
  - intros x Hx Hn. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
    apply KV4; [lia|]. intros [C|C]; [exact (Hn C) | lia]. }
(* ---- the cut +0x3a0 ---- *)
apply SRr_ret. rewrite cs_pc_ret2.
apply (cs_close cx ly' S' W' regs' mem' md' Bw0 B1 regs4 mem4 md4 LAWS HB HC HFR HSP HFSH HIO HMET HW0 HCD HJ4).
- intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; apply RK4; lia.
- exact (RK4 18 ltac:(lia)).
- exact (RK4 26 ltac:(lia)).
- split; [exact (eq_trans (RK4 19 ltac:(lia)) R19) | exact (eq_trans (RK4 23 ltac:(lia)) R23)].
- exact (eq_trans (RK4 24 ltac:(lia)) R24).
- exact (eq_trans (RK4 21 ltac:(lia)) R21).
- exact (eq_trans (RK4 20 ltac:(lia)) R20).
- exact (eq_trans (HP4 22 ltac:(unfold acallee_saved; lia)) Q22b).
- exact KV4.
- exact GA4.
- exact HTW4.
Qed.

End stage.
