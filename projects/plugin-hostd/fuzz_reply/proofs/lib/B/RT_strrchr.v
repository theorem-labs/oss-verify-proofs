(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contract astrrchr_realizes (lib/A/W_sites.v) proved for
   fuzz_reply.asan-ubsan's strrchr interceptor, entered at the trampoline __interceptor_trampoline_strrchr 0x421fc. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/RT_strrchr.v at commit debcdf3fa6a, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (19 numerals; per-numeral report). *)
(* Route (R2Cmp, a Theorem Labs lane, 2026-10-29): the body walk is lib/A/Bz/A/I_strrchr.v istrrchr_spec (new: no other pinned
   binary has this code), with its two Section hypotheses met by R_isPoisoned.rip_proof and FRsl.sl_proof; the bridge
   is R1's RT_kit / RT_post, as in RT_strlen.v.  rchr_fn reads the walk's answer (the last index of c among the k + 1
   bytes up to and including the NUL, or none) as W_sites' disjunction. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.MemNorm.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Regs6ss.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Img0.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.FRsl.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Exec.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Frame.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.MState.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.ImageA.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Cells.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Step.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.D_kit.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_consts.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_qck.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.R_m2s.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.R_isPoisoned.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strnlenw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strlen.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strrchr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0s YK04 YK0i YK14 YP09 YP02 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI00 YI04 YK06 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
YB1v W_syms W_listing W_kit W_tbl W_place W_img W_sites.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require FRbz_bridge RT_kit RT_post YE2k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module NM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.MemNorm.
Module L6 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Regs6ss.
Module I0 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Img0.
Module SL := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.FRsl.
Module BE := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Exec.
Module BM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Mem.
Module BF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Frame.
Module BMS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.MState.
Module BI := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.ImageA.
Module BC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Cells.
Module BSt := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Step.
Module BD := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.D_kit.
Module BK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_consts.
Module BQ := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_qck.
Module BR := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.R_m2s.
Module BP := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.R_isPoisoned.
Module BN := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strnlenw.
Module BL := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strlen.
Module SR := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strrchr.
Module FSB := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.FRbz_bridge.
Module K := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_kit.
Module RP := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_post.

(* ---- the walk's answer, read on the bytes the reader sees ---- *)
Section fn.
Variable rd : Z -> option Z.

Lemma rchr_idx_spec : forall (x c : Z) (bs : list byte) (j : nat),
  (j <= length bs)%nat ->
  (forall i z, nth_error bs i = Some z -> rd (x + Z.of_nat i) = Some (bv_unsigned z)) ->
  match SR.rchr_idx c bs j with
  | None => forall i, 0 <= i < Z.of_nat j -> rd (x + i) <> Some c
  | Some i => (i < j)%nat /\ rd (x + Z.of_nat i) = Some c /\
              forall i', Z.of_nat i < i' < Z.of_nat j -> rd (x + i') <> Some c
  end.
Proof.
  intros x c bs j. induction j as [|j IH]; intros Hj R.
  - cbn [SR.rchr_idx]. intros i Hi. lia.
  - cbn [SR.rchr_idx].
    destruct (nth_error bs j) as [b|] eqn:E; [| apply nth_error_None in E; lia].
    pose proof (R _ _ E) as Vb.
    destruct (Z.eqb_spec (bv_unsigned b) c) as [Ec|Nc].
    + split; [lia|]. split; [rewrite Vb, Ec; reflexivity|]. intros i' Hi'. lia.
    + specialize (IH ltac:(lia) R).
      destruct (SR.rchr_idx c bs j) as [i|] eqn:Ei.
      * destruct IH as (Hi & Vi & Hafter). split; [lia|]. split; [exact Vi|].
        intros i' Hi'. destruct (Z.eq_dec i' (Z.of_nat j)) as [->|Ne].
        -- rewrite Vb. intros Eq. injection Eq as Eq. lia.
        -- apply Hafter. lia.
      * intros i Hi. destruct (Z.eq_dec i (Z.of_nat j)) as [->|Ne].
        -- rewrite Vb. intros Eq. injection Eq as Eq. lia.
        -- apply IH. lia.
Qed.

(* W_sites' disjunction from the walk's answer, over the k + 1 bytes [x, x + k] *)
Theorem rchr_fn : forall (x c k : Z) (bs : list byte),
  0 <= k -> Z.of_nat (length bs) = k + 1 ->
  (forall i z, nth_error bs i = Some z -> rd (x + Z.of_nat i) = Some (bv_unsigned z)) ->
  ((forall i, 0 <= i <= k -> rd (x + i) <> Some c) /\ SR.rchr_res x c bs (length bs) = 0) \/
  (exists i, 0 <= i <= k /\ rd (x + i) = Some c /\ (forall j, i < j <= k -> rd (x + j) <> Some c) /\
     SR.rchr_res x c bs (length bs) = x + i).
Proof.
  intros x c k bs Hk L R.
  pose proof (rchr_idx_spec x c bs (length bs) (Nat.le_refl _) R) as H.
  unfold SR.rchr_res.
  destruct (SR.rchr_idx c bs (length bs)) as [i|].
  - right. destruct H as (Hi & Vi & Hafter). exists (Z.of_nat i).
    split; [lia|]. split; [exact Vi|]. split; [intros j Hj; apply Hafter; lia | reflexivity].
  - left. split; [intros i Hi; apply H; lia | reflexivity].
Qed.
End fn.

(* Build identity: this is fuzz_reply.asan-ubsan (ofl_head 0x5fa0e8 is the ASan sink head YE2k.tfib_sink_head carries;
   main and LLVMFuzzerTestOneInput begin with their frame allocations at 0x81ea4 and 0x84408), the entry the walks
   call as WS_strrchr is 0x421fc, and its word is `j 0x438b0` (into ___interceptor_strrchr). *)
Lemma rt_strrchr_build_id :
  YE2k.A_ofl_head = 0x5fa0e8 /\ @YI16.sk_ofl_head YE2k.tfib_sink_head = 0x5fa0e8 /\
  fr_sigma WS_strrchr = 0x421fc /\
  option_map bv_unsigned (fetch_word frsegs (w64 0x81ea4)) = Some 0xfb010113 /\
  option_map bv_unsigned (fetch_word frsegs (w64 0x84408)) = Some 0xec010113 /\
  option_map bv_unsigned (fetch_word frsegs (w64 0x421fc)) = Some 0x6b40106f.
Proof.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [vm_compute; reflexivity|]. split; vm_compute; reflexivity.
Qed.

(* the walk from the trampoline, at the canonical register tree (istrrchr_spec with RIP and SL met) *)
Lemma bz_strrchr : forall regs F fc m0 (s c : Z) (str slack : list byte) (lo : Z),
  reg_get regs 10 = Z_to_bv 64 s -> reg_get regs 11 = Z_to_bv 64 c -> 0 <= c < 256 ->
  BF.stk BI.asegs m0 lo (bv_unsigned (reg_get regs 2)) -> lo <= bv_unsigned (reg_get regs 2) - 4400 ->
  BR.kHighShadowEnd < lo -> bv_unsigned (reg_get regs 2) < 2 ^ 63 ->
  0 <= s <= 2 ^ 47 -> Z.of_nat (length str) < 2 ^ 40 -> s + Z.of_nat (length str) + 1 <= 2 ^ 47 ->
  BM.bytes_at BI.asegs m0 s (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  (s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned (reg_get regs 2) - 4400 \/
   bv_unsigned (reg_get regs 2) <= s) ->
  BQ.chk_ok m0 s (Z.of_nat (length str) + 1) -> BR.m2s_cells m0 -> BN.icells_sn m0 -> BL.icells_sl m0 ->
  SR.icells_srr m0 -> BM.mem_inv BI.asegs m0 ->
  BE.evt BI.asegs
    (SR.istrrchr_post (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) F fc (SR.rchr_res s c (str ++ [Z_to_bv 8 0]) (S (length str))) lo m0)
    (BMS.MS (L6.mkR_of regs) F (Z_to_bv 64 0x421fc) fc None m0 (YK11.seg_rom BI.asegs)).
Proof.
  intros regs F fc m0 s c str slack lo Ha0 Ha1 C0 ST LO LOLO SPH S0 L40 SH BUF NZ PAD SEPS CS M2S IC ICL ISR MI.
  change (L6.mkR_of regs) with (BF.mkR (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 5) (reg_get regs 6) (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (reg_get regs 10) (reg_get regs 11) (reg_get regs 12) (reg_get regs 13) (reg_get regs 14) (reg_get regs 15) (reg_get regs 16) (reg_get regs 17) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) (reg_get regs 28) (reg_get regs 29) (reg_get regs 30) (reg_get regs 31)).
  eapply (SR.istrrchr_spec BP.rip_proof SL.sl_proof); eassumption.
Qed.

(* the string's bytes [x, x + k), its NUL and the rest of the NUL's 8-byte word, as the walk reads them
   (R1Str's RT_strlen.v str_buf, copied: RT_strlen.v is R1's file and is not in this file's Require closure) *)
Lemma str_buf : forall (W : world frsegs) mem x k,
  0 < x -> 0 <= k -> x + k + 8 <= 2 ^ 64 ->
  first_byte frsegs W mem x (k + 1) 0 k ->
  (forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview frsegs (w_H W) mem a <> None) ->
  let mR := mrestrict (w_H W) mem in
  BM.bytes_at BI.asegs mR x
    (K.mk_slack mR x (Z.to_nat k) ++ Z_to_bv 8 0 :: K.mk_slack mR (x + k + 1) (K.slack_len (x + k + 1))) /\
  ~ In (Z_to_bv 8 0) (K.mk_slack mR x (Z.to_nat k)) /\
  Z.of_nat (K.slack_len (x + k + 1)) = 7 - (x + k) mod 8.
Proof.
  intros W mem x k Hx Hk Hxk (Hkn & Hbef & Hlast) Htail mR.
  assert (Hs : Z.of_nat (K.slack_len (x + k + 1)) = 7 - (x + k) mod 8).
  { unfold K.slack_len. rewrite Z2Nat.id by (apply Z.mod_pos_bound; lia). Z.div_mod_to_equations. lia. }
  pose proof (Z.mod_pos_bound (x + k) 8 ltac:(lia)) as Hm.
  assert (E0 : K.byte_at mR (x + k) = Z_to_bv 8 0) by exact (proj1 (K.byte_at_view (w_H W) mem (x + k) 0 (Hlast ltac:(lia)))).
  assert (E1 : K.mk_slack mR (x + Z.of_nat (Z.to_nat k)) 1 = [Z_to_bv 8 0]).
  { unfold K.mk_slack. cbn [seq map]. rewrite <- E0. f_equal. f_equal. lia. }
  split; [|split; [|exact Hs]].
  - assert (Eb : K.mk_slack mR x (Z.to_nat k) ++ Z_to_bv 8 0 :: K.mk_slack mR (x + k + 1) (K.slack_len (x + k + 1))
                 = K.mk_slack mR x (Z.to_nat k + 1 + K.slack_len (x + k + 1))).
    { rewrite (K.mk_slack_app mR x (Z.to_nat k + 1)), (K.mk_slack_app mR x (Z.to_nat k) 1), E1.
      rewrite <- app_assoc. cbn [app]. do 3 f_equal. lia. }
    rewrite Eb. apply K.bytes_at_mk; [lia | lia |].
    intros a Ha. destruct (Z_lt_le_dec a (x + k)) as [L1|L1].
    + destruct (Hbef (a - x) ltac:(lia)) as (b & Hb & _). replace (x + (a - x)) with a in Hb by lia.
      rewrite Hb. discriminate.
    + destruct (Z.eq_dec a (x + k)) as [->|N]; [rewrite (Hlast ltac:(lia)); discriminate|].
      apply Htail. lia.
  - intros Hin. unfold K.mk_slack in Hin. apply in_map_iff in Hin as (j & Ej & Hj). apply in_seq in Hj.
    destruct (Hbef (Z.of_nat j) ltac:(lia)) as (b & Hb & Hb0).
    destruct (K.byte_at_view (w_H W) mem (x + Z.of_nat j) b Hb) as (Eb & Rb).
    fold mR in Eb. rewrite Eb in Ej. exact (K.bv8_ne0 b Rb Hb0 Ej).
Qed.

Section core. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The interceptor's own two cells, common_flags()->intercept_strchr (0x138265 = 1) and REAL(strrchr) (0x9fc90 =
   0x9740c), are fr_rt_rest's last two conjuncts (RT_kit.v), so FrRtCells carries them. *)
Theorem rt_strrchr : forall B, AR_laws frsegs B -> K.FrShadowSyms B -> K.FrRtCells B ->
  astrrchr_realizes (PI := PB_fr) B (fr_sigma WS_strrchr).
Proof.
  intros B LAWS TL CELLS ly S W regs mem md x c k Hpre (Hslo2 & Hpres2) Hx Hc Hc256 Hx0 Hk0 Hxk Hk40
    Hfb Hin Htail Hrom (Ham1 & Hra & Hhull) Ham8.
  change (@pa_segs _ fr_prog_listing PB_fr) with tfibsegs in *.
  pose proof LAWS as LAWS'. change frsegs with tfibsegs in LAWS'.
  change (fr_sigma WS_strrchr) with 0x421fc.
  pose proof Hpre as (HAR & Hret & Hal & Hlo1 & Hhi & HpresE & Hgp & Htp).
  pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
  pose proof (lo_top ly HLY) as (_ & _ & _ & Lhi & _ & _ & Lbeg).
  unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
  assert (HK : 2 * ESTACK = 8192) by reflexivity.
  pose proof (RP.ro_agree_of_rom_view W mem Hrom) as RO.
  pose proof (K.walk_cells B LAWS TL CELLS ly S W mem md HAR) as (M2S & ICN & _ & ICL & _ & _ & _).
  assert (ISR : SR.icells_srr (NM.normalize_cj I0.rsegs (mrestrict (w_H W) mem))).
  { pose proof (K.walk_rest B CELLS ly S W mem md HAR) as REST. unfold K.fr_rt_rest in REST.
    repeat match type of REST with _ /\ (_ /\ _) => destruct REST as [_ REST] end.
    destruct REST as [C1 C2]. split; [exact C1 | exact C2]. }
  assert (Esp : bv_unsigned (reg_get regs 2) = spZ regs) by (unfold spZ; rewrite RP.getr_nz by reflexivity; reflexivity).
  assert (Ha0 : reg_get regs 10 = Z_to_bv 64 x) by (rewrite <- RP.getr_nz by reflexivity; exact Hx).
  assert (Ha1 : reg_get regs 11 = Z_to_bv 64 c) by (rewrite <- RP.getr_nz by reflexivity; exact Hc).
  assert (Hamr : (0 <= x /\ x + (k + 1) <= 0x7fff7fff /\ x + 8 <= 0x7fff7fff) \/
                 (0x10007fff8000 <= x /\ x + (k + 1) <= 0x7fffffffffff /\ x + 8 <= 0x7fffffffffff))
    by (unfold amem_range, YG0f.kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham1, Ham8; lia).
  destruct (str_buf W mem x k Hx0 Hk0 ltac:(lia) Hfb Htail) as (BUF & NZ & Hs).
  pose proof Hfb as (Hkn & Hbef & Hlast).
  set (H := w_H W) in *. set (mR := mrestrict H mem) in *. set (sp := spZ regs) in *.
  set (lo := sp - 2 * ESTACK).
  set (str := K.mk_slack mR x (Z.to_nat k)) in *.
  set (slack := K.mk_slack mR (x + k + 1) (K.slack_len (x + k + 1))) in *.
  assert (Lstr : Z.of_nat (length str) = k) by (unfold str; rewrite K.length_mk_slack; lia).
  assert (Lsl : Z.of_nat (length slack) = 7 - (x + k) mod 8) by (unfold slack; rewrite K.length_mk_slack; exact Hs).
  pose proof (Z.mod_pos_bound (x + k) 8 ltac:(lia)) as Hm8.
  assert (Hfr : x + k < sp - 8192 \/ sp <= x).
  { assert (Hw : forall a, x <= a < x + (k + 1) -> ~ (sp - 2 * ESTACK <= a < sp)) by (intros a Ha; exact (proj2 (Hin a Ha))).
    destruct (K.off_window sp (2 * ESTACK) x (k + 1) ltac:(lia) ltac:(lia) Hw) as [L|L]; [left; lia | right; exact L]. }
  (* the k + 1 bytes the walk's answer is about, each as the donor's reader sees it *)
  assert (RB : forall i z, nth_error (str ++ [Z_to_bv 8 0]) i = Some z ->
                 aview tfibsegs H mem (x + Z.of_nat i) = Some (bv_unsigned z)).
  { intros i z Hi.
    destruct (Nat.lt_ge_cases i (length str)) as [Li|Li].
    - rewrite nth_error_app1 in Hi by exact Li.
      assert (Li' : (i < Z.to_nat k)%nat) by (unfold str in Li; rewrite K.length_mk_slack in Li; exact Li).
      unfold str in Hi. rewrite K.nth_mk_slack in Hi by exact Li'. injection Hi as <-.
      destruct (Hbef (Z.of_nat i) ltac:(lia)) as (v & Hv & _).
      destruct (K.byte_at_view H mem _ v Hv) as (Eb & Rv). fold mR in Eb. rewrite Eb, Hv.
      rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. reflexivity.
    - rewrite nth_error_app2 in Hi by exact Li.
      destruct (i - length str)%nat as [|q] eqn:Eq; [|destruct q; discriminate Hi].
      cbn in Hi. injection Hi as <-.
      replace (x + Z.of_nat i) with (x + k) by lia. rewrite (Hlast ltac:(lia)). reflexivity. }
  assert (LB : Z.of_nat (length (str ++ [Z_to_bv 8 0])) = k + 1) by (rewrite length_app; cbn [length]; lia).
  assert (ELB : length (str ++ [Z_to_bv 8 0]) = Datatypes.S (length str)) by (rewrite length_app; cbn [length]; lia).
  destruct (rchr_fn (aview tfibsegs H mem) x c k (str ++ [Z_to_bv 8 0]) Hk0 LB RB) as [(NONE & E0)|(i & Hi & Vi & AFT & Ei)];
    rewrite ELB in *.
  all: apply (FSB.srr_of_evt K.Hwx_fr W 0x421fc regs mem md
    (RP.walk_at (SR.istrrchr_post (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) fp_regs fp_csr (SR.rchr_res x c (str ++ [Z_to_bv 8 0]) (Datatypes.S (length str))) lo
                  (NM.normalize_cj I0.rsegs mR)) mR)).
  all: try (refine (_ : BE.evt BI.asegs _ (RP.st_at regs fp_regs (Z_to_bv 64 0x421fc) fp_csr mR));
    apply RP.bz_transport; [exact RO|];
    apply (bz_strrchr regs fp_regs fp_csr _ x c str slack lo);
    [ exact Ha0 | exact Ha1 | exact Hc256
    | rewrite Esp; apply RP.stk_norm_high; [unfold lo, RP.FR_IMG_TOP; lia | unfold TASK_SIZE; lia |];
      apply FSB.stk_of_apresent; [unfold lo; lia | lia | exact Hpres2]
    | rewrite Esp; unfold lo; lia
    | unfold BR.kHighShadowEnd, lo; lia
    | rewrite Esp; lia
    | lia
    | rewrite Lstr; lia
    | rewrite Lstr; lia
    | refine (NM.bytes_at_normalize_cj_low I0.rsegs mR x (str ++ Z_to_bv 8 0 :: slack) RO _ BUF);
      rewrite length_app; cbn [length]; unfold TASK_SIZE; lia
    | exact NZ
    | rewrite Lstr, Lsl; Z.div_mod_to_equations; lia
    | rewrite Esp, Lstr, Lsl; lia
    | rewrite Lstr; apply RP.chk_norm; [lia | lia | lia | lia | | exact Hra | exact (Hhull ltac:(lia))];
      unfold BK.region_in_mem, BR.kLowMemEnd, BR.kHighShadowEnd, BR.kHighMemEnd; lia
    | exact M2S | exact ICN | exact ICL | exact ISR | apply RP.bz_mem_inv_normalize ]).
  all: intros ms' model' (cc & s0 & HQ & Hrel & Hsame & Heqv) Hsbm _;
    destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Es0 & MU & _ & _ & ST');
    subst s0; rewrite Esp in MU, ST';
    apply (RP.aentry_post_of_walk B LAWS (2 * ESTACK) 4400 [] (fun _ => False) _
      (SR.rchr_res x c (str ++ [Z_to_bv 8 0]) (Datatypes.S (length str)))
      ly S W regs mem md ms' model' cc m' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6);
    [ exact Hpre | exact Hslo2 | exact RO | lia | intros a Ha; inversion Ha | intros a [] | intros a []
    | exact Hrel | exact Hsame | exact Heqv | rewrite app_nil_r; exact MU | exact ST' | exact Hsbm |].
  - intros regs'' mem'' Hr _. rewrite Hr, E0. left. split; [exact NONE | reflexivity].
  - intros regs'' mem'' Hr _. rewrite Hr, Ei. right. exists i. split; [exact Hi|]. split; [exact Vi|].
    split; [exact AFT | reflexivity].
Qed.

End core.
