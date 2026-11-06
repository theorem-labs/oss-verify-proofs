(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contract astrlen_realizes (lib/B/W_contract.v) proved for
   fuzz_reply.asan-ubsan's strlen interceptor, entered at the trampoline __wrap_strlen 0x421e4. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/RT_strlen.v at commit debcdf3fa6a, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), and its fuzz_reply.asan-ubsan addresses relocated from fuzz_reply.asan (25 numerals; per-numeral report). *)
(* Ported from: a working branch 3210d71ee38 proofs/omx-clap-core/fuzz_state/lib/A/FSstrlen.v:207-243,
   752-830 (bz_strlen, fs_strlen_core).  Changes (R1Str, 2026-10-29): fuzz_reply.asan-ubsan's addresses (trampoline
   0x421e4 `j 0x42288`, ___interceptor_strlen 0x42288); the premises are W_contract.v's astrlen_realizes, not fs's
   cstr_ok: the string is the first_byte fact over aview (str and slack are the bytes the donor's reader sees,
   mk_slack), the frame separation comes from the W_sites "no byte in the scratch window" premise (RT_kit.off_window),
   region_in_mem from amem_range x (k + 1) and amem_range x 8; U-free; the post is W_sites' aentry_post
   (RT_post.aentry_post_of_walk) read back as astrlen_realizes' post.
   The body walk is the relocated Bz tree's I_strlen.v istrlen_spec, with its two section hypotheses discharged:
   RIP by R_isPoisoned.rip_proof (__asan_region_is_poisoned 0x559b4) and SL by FRsl.sl_proof (musl strlen 0x970cc,
   lib/B/R_strlen.v).  Named premises beyond AR_laws: RT_kit.FrShadowSyms and RT_kit.FrRtCells. *)
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
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_consts.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_qck.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.R_m2s.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.R_isPoisoned.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strnlenw.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strlen.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0s YK04 YK0i YK14 YP09 YP02 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI00 YI04 YK06 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
YB1v W_syms W_listing W_kit W_tbl W_place W_img W_contract W_sites.
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
Module BK := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_consts.
Module BQ := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_qck.
Module BR := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.R_m2s.
Module BP := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.R_isPoisoned.
Module BN := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strnlenw.
Module BL := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A.I_strlen.
Module FSB := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.FRbz_bridge.
Module K := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_kit.
Module RP := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.RT_post.

(* Build identity: this is fuzz_reply.asan-ubsan (ofl_head 0x5fa0e8 is the ASan sink head YE2k.tfib_sink_head carries;
   main and LLVMFuzzerTestOneInput begin with their frame allocations at 0x81ea4 and 0x84408), the entry the walks
   call as WS_strlen is 0x421e4, and its word is `j 0x42288` (into ___interceptor_strlen). *)
Lemma rt_strlen_build_id :
  YE2k.A_ofl_head = 0x5fa0e8 /\ @YI16.sk_ofl_head YE2k.tfib_sink_head = 0x5fa0e8 /\
  fr_sigma WS_strlen = 0x421e4 /\
  option_map bv_unsigned (fetch_word frsegs (w64 0x81ea4)) = Some 0xfb010113 /\
  option_map bv_unsigned (fetch_word frsegs (w64 0x84408)) = Some 0xec010113 /\
  option_map bv_unsigned (fetch_word frsegs (w64 0x421e4)) = Some 0x0a40006f.
Proof.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [vm_compute; reflexivity|]. split; vm_compute; reflexivity.
Qed.

(* ---- the trampoline and the interceptor walk, in the Bz tree's words ---- *)
Module W.
Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Tac.
Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.ImageA.
Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Exec.
Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.MState.
Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.Step.
Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib.StoreFast.
Import OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.P.Str_tac.

(* __wrap_strlen 0x421e4: `j 0x42288` *)
Lemma tramp_strlen : forall (Q : machine_state -> Prop) R F fc m,
  evt asegs Q (MS R F (Z_to_bv 64 0x42288) fc None m (YK11.seg_rom asegs)) ->
  evt asegs Q (MS R F (Z_to_bv 64 0x421e4) fc None m (YK11.seg_rom asegs)).
Proof. intros Q R F fc m H. lstep. exact H. Qed.
End W.

(* the interceptor walk from the trampoline, at the canonical register tree (I_strlen.v istrlen_spec, RIP / SL met) *)
Lemma bz_strlen : forall regs F fc m0 (s : Z) (str slack : list byte) (lo : Z),
  reg_get regs 10 = Z_to_bv 64 s ->
  BF.stk BI.asegs m0 lo (bv_unsigned (reg_get regs 2)) -> lo <= bv_unsigned (reg_get regs 2) - 2224 ->
  BR.kHighShadowEnd < lo -> bv_unsigned (reg_get regs 2) < 2 ^ 63 ->
  0 <= s <= 2 ^ 47 -> Z.of_nat (length str) < 2 ^ 40 -> s + Z.of_nat (length str) + 1 <= 2 ^ 47 ->
  BM.bytes_at BI.asegs m0 s (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  (s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned (reg_get regs 2) - 2224 + 7 \/
   bv_unsigned (reg_get regs 2) <= s) ->
  BQ.chk_ok m0 s (Z.of_nat (length str) + 1) -> BR.m2s_cells m0 -> BN.icells_sn m0 -> BL.icells_sl m0 ->
  BM.mem_inv BI.asegs m0 ->
  BE.evt BI.asegs
    (BL.istrlen_post (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 8)
       (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
       (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) F fc
       (Z.of_nat (length str)) lo m0)
    (BMS.MS (L6.mkR_of regs) F (Z_to_bv 64 0x421e4) fc None m0 (YK11.seg_rom BI.asegs)).
Proof.
  intros regs F fc m0 s str slack lo Ha0 ST LO LOLO SPH S0 L40 SH BUF NZ PAD SEPS CS M2S IC ICL MI.
  apply W.tramp_strlen.
  change (L6.mkR_of regs) with (BF.mkR (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4)
    (reg_get regs 5) (reg_get regs 6) (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (reg_get regs 10)
    (reg_get regs 11) (reg_get regs 12) (reg_get regs 13) (reg_get regs 14) (reg_get regs 15) (reg_get regs 16)
    (reg_get regs 17) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
    (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) (reg_get regs 28)
    (reg_get regs 29) (reg_get regs 30) (reg_get regs 31)).
  exact (BL.istrlen_spec BP.rip_proof SL.sl_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F fc m0 s str slack lo Ha0 ST LO LOLO SPH S0 L40 SH BUF NZ PAD SEPS CS M2S IC ICL MI).
Qed.

Section core. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* the string's bytes [x, x + k), its NUL and the rest of the NUL's 8-byte word, as the walk reads them *)
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

Theorem rt_strlen : forall B, AR_laws frsegs B -> K.FrShadowSyms B -> K.FrRtCells B ->
  astrlen_realizes (PI := PB_fr) B (fr_sigma WS_strlen).
Proof.
  intros B LAWS TL CELLS ly S W regs mem md x k Hpre Hslo2 Hpres2 Hx Hx0 Hk0 Hk32 Hxk Hfb Hsrc Hband Hamr Ham8
    Hra Hhull Htail Hrom.
  change (@pa_segs _ fr_prog_listing PB_fr) with frsegs in *.
  change (fr_sigma WS_strlen) with 0x421e4.
  pose proof Hpre as (HAR & Hret & Hal & Hlo1 & Hhi & HpresE & Hgp & Htp).
  pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
  pose proof (lo_top ly HLY) as (_ & _ & _ & Lhi & _ & _ & Lbeg).
  unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
  assert (HK : 2 * ESTACK = 8192) by reflexivity.
  pose proof (RP.ro_agree_of_rom_view W mem Hrom) as RO.
  pose proof (K.walk_cells B LAWS TL CELLS ly S W mem md HAR) as (M2S & ICN & _ & ICL & _ & _ & _).
  assert (Esp : bv_unsigned (reg_get regs 2) = spZ regs) by (unfold spZ; rewrite RP.getr_nz by reflexivity; reflexivity).
  assert (Ha0 : reg_get regs 10 = Z_to_bv 64 x) by (rewrite <- RP.getr_nz by reflexivity; exact Hx).
  assert (Hamr' : (0 <= x /\ x + k + 1 <= 0x7fff7fff /\ x + 8 <= 0x7fff7fff) \/
                  (0x10007fff8000 <= x /\ x + k + 1 <= 0x7fffffffffff /\ x + 8 <= 0x7fffffffffff))
    by (unfold amem_range, YG0f.kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr, Ham8; lia).
  destruct (str_buf W mem x k Hx0 Hk0 ltac:(lia) Hfb Htail) as (BUF & NZ & Hs).
  set (H := w_H W) in *. set (mR := mrestrict H mem) in *. set (sp := spZ regs) in *.
  set (lo := sp - 2 * ESTACK).
  set (str := K.mk_slack mR x (Z.to_nat k)) in *.
  set (slack := K.mk_slack mR (x + k + 1) (K.slack_len (x + k + 1))) in *.
  assert (Lstr : Z.of_nat (length str) = k) by (unfold str; rewrite K.length_mk_slack; lia).
  assert (Lsl : Z.of_nat (length slack) = 7 - (x + k) mod 8) by (unfold slack; rewrite K.length_mk_slack; exact Hs).
  pose proof (Z.mod_pos_bound (x + k) 8 ltac:(lia)) as Hm8.
  assert (Hfr : x + k < sp - 8192 \/ sp <= x).
  { assert (Hw : forall a, x <= a < x + (k + 1) -> ~ (sp - 2 * ESTACK <= a < sp)) by (intros a Ha; apply Hband; lia).
    destruct (K.off_window sp (2 * ESTACK) x (k + 1) ltac:(lia) ltac:(lia) Hw) as [L|L]; [left; lia | right; exact L]. }
  eapply SRr_mono.
  { apply (FSB.srr_of_evt K.Hwx_fr W 0x421e4 regs mem md
      (RP.walk_at (BL.istrlen_post (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 8)
         (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
         (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) fp_regs fp_csr
         (Z.of_nat (length str)) lo (NM.normalize_cj I0.rsegs mR)) mR)
      (aentry_post (PI := PB_fr) B (2 * ESTACK) ly S W regs mem md (fun _ => False)
         (fun regs' _ => YK11.getr regs' 10 = w64 k))).
    - refine (_ : BE.evt BI.asegs _ (RP.st_at regs fp_regs (Z_to_bv 64 0x421e4) fp_csr mR)).
      apply RP.bz_transport; [exact RO|].
      apply (bz_strlen regs fp_regs fp_csr _ x str slack lo).
      + exact Ha0.
      + rewrite Esp. apply RP.stk_norm_high; [unfold lo, RP.FR_IMG_TOP; lia | unfold TASK_SIZE; lia |].
        apply FSB.stk_of_apresent; [unfold lo; lia | lia | exact Hpres2].
      + rewrite Esp. unfold lo. lia.
      + unfold BR.kHighShadowEnd, lo. lia.
      + rewrite Esp. lia.
      + lia.
      + rewrite Lstr. lia.
      + rewrite Lstr. lia.
      + refine (NM.bytes_at_normalize_cj_low I0.rsegs mR x (str ++ Z_to_bv 8 0 :: slack) RO _ BUF).
        rewrite length_app. cbn [length]. unfold TASK_SIZE. lia.
      + exact NZ.
      + rewrite Lstr, Lsl. Z.div_mod_to_equations. lia.
      + rewrite Esp, Lstr, Lsl. lia.
      + rewrite Lstr. apply RP.chk_norm; [lia | lia | lia | lia | | exact Hra | exact Hhull].
        unfold BK.region_in_mem, BR.kLowMemEnd, BR.kHighShadowEnd, BR.kHighMemEnd. lia.
      + exact M2S.
      + exact ICN.
      + exact ICL.
      + apply RP.bz_mem_inv_normalize.
    - intros ms' model' (c & s0 & HQ & Hrel & Hsame & Heqv) Hsbm _.
      destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Es0 & MU & _ & _ & ST').
      subst s0. rewrite Esp in MU, ST'.
      refine (RP.aentry_post_of_walk B LAWS (2 * ESTACK) 2224 [] (fun _ => False) _ (Z.of_nat (length str)) ly S W regs mem md
        ms' model' c m' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hpre Hslo2 RO ltac:(lia) _ _ _ Hrel Hsame Heqv _ ST' Hsbm _).
      + intros a Ha. inversion Ha.
      + intros a [].
      + intros a [].
      + cbn [app]. exact MU.
      + intros regs'' mem'' Hr _. rewrite Hr, Lstr. reflexivity. }
  cbv beta. intros W' c' _ (EW & regs' & mem' & md' & Ec & HAR' & Hpre' & Hsbm' & Hres & Hfr' & Hp').
  split; [exact EW|]. exists regs', mem', md'.
  split; [exact Ec|]. split; [exact HAR'|]. split; [exact Hpre'|]. split; [exact Hsbm'|]. split; [exact Hres|].
  split; [intros a Ha Hn; apply Hfr'; [exact Ha | intros [] | exact Hn] | exact Hp'].
Qed.

End core.
