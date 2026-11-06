(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_headamp_tx_init on fuzz_grant.asan, written for libreac/fuzz_grant: the entry seat and the return are adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v, the __asan_memset call from proofs/cgif/cgif_file_fuzzer/lib/A/AC8y.v, the reseat after it from proofs/cgif/cgif_file_fuzzer/lib/A/ACbl.v, and further proof steps from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v and proofs/cgif/cgif_file_fuzzer/lib/A/AE6j.v; the contract is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/HeadampTxInit.v, with its module paths and module names changed; 223 of its 297 lines of code are new or changed and 113 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/ReacDiscoGateInit.v, with its module names changed; 239 of its 282 lines of code are new or changed and 254 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YA0o YCbm YA0q YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require FpStep.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YA0f YK0e YK0o.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require FP.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_rate_snap_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing} {PH : PAHiImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Definition REAC_RATE_SNAP_STK : Z := ESTACK.
Definition treac_rate_snap_post (fq : YK11.FPState) (regs : bvmap 5 word) ly S (W : world SEGS) mem md
  : world SEGS -> config -> Prop :=
  fun W' c' => exists fq' : YK11.FPState,
    @YK11.fp_regs fq' = bvmap_set (Z_to_bv 5 14) (Z_to_bv 64 D3837)
                          (bvmap_set (Z_to_bv 5 15) (Z_to_bv 64 D6000) (@YK11.fp_regs fq)) /\
    @YK11.fp_csr fq' = reac_rate_snap_fcsr (Sem.reg_get (@YK11.fp_regs fq) (Z_to_bv 5 10)) (@YK11.fp_csr fq) /\
    apost_base (fx := fq') SEGS B REAC_RATE_SNAP_STK [] regs ly S W mem md 0
      (fun ly' S' W' regs' mem' md' =>
         getr regs' 10 = w64 (reac_rate_snap_model (Sem.reg_get (@YK11.fp_regs fq) (Z_to_bv 5 10))) /\
         Permutation (ablocks B ly' S') (ablocks B ly S) /\
         W' = W /\ (forall x, mem' x = mem x)) W' c'.
Definition treac_rate_snap_spec : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch,
  afn_pre SEGS B REAC_RATE_SNAP_STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_HI 99) + 1608) 8 D6000 ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_HI 98) + 1812) 8 D3837 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_rate_snap) regs mem md)
    (treac_rate_snap_post fq regs ly S W mem md).
Section w.
Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
Import YN3v YI04 YI09 YI08 YG0v YK04 YA0i YA0n YA0o YCbm YA0q.
Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0s YP0d YP0c YI0w YI0z YC4a YC8i YC80 YC1f YC8g YM05.
Context {fx : YK11.FPState}.
Let HB := @pa_B_ok _ _ PI.
Definition RS_SB : Z := 0x7fff8000.
Definition RS_Bx : sv := SLit RS_SB.
Definition RS_Bspan : Z * Z := (RS_SB, RS_SB + 2 ^ 44 - 1).
Definition ss_rs : sstate := mkSS AF_both3_reac_rate_snap sr_atoms [] None (mkFacts [] [] []).
Lemma rs_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem,
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss_rs
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_both3_reac_rate_snap)) mem (seg_rom SEGS)))
/\ sh_ok SEGS RS_Bx [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
intros W regs mem. split; [|constructor].
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- reflexivity.
- constructor.
- exact I.
- split; [exact I | split; exact I].
Qed.
Lemma rs_keep : forall (fa fb : YK11.FPState) (W : world SEGS) E ss ms md Q (STK sp0 : Z) FPl ly S W0 mem0 md0 own lyc Sc k,
st_ok_pi (fx := fa) SEGS VAL E ss (restrict (w_H W) ms) ->
ss_resv ss = None -> 0 <= ss_pc ss < 2 ^ 39 ->
RiscvSemantics.step SEGS (@mkst fa (ms_regs ms) (Z_to_bv 64 (BASE + ss_pc ss)) (mrestrict (w_H W) (ms_mem ms)) (seg_rom SEGS)) =
MachineOk (@mkst fb (ms_regs ms) (Z_to_bv 64 (BASE + (ss_pc ss + 4))) (mrestrict (w_H W) (ms_mem ms)) (seg_rom SEGS)) ->
ajournal SEGS B STK sp0 FPl ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k ->
(forall md', st_ok_pi (fx := fb) SEGS VAL E (setpc ss (ss_pc ss + 4))
(restrict (w_H W) (@mkst fb (ms_regs ms) (Z_to_bv 64 (BASE + (ss_pc ss + 4))) (ms_mem ms) (seg_rom SEGS))) ->
ajournal SEGS B STK sp0 FPl ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md' k ->
SRr SEGS W (mkCfg (@mkst fb (ms_regs ms) (Z_to_bv 64 (BASE + (ss_pc ss + 4))) (ms_mem ms) (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg ms md) Q.
Proof.
intros fa fb W E ss ms md Q STK sp0 FPl ly S W0 mem0 md0 own lyc Sc k HS Hrv Hk Hst HJ HK.
pose proof (@pa_segs_low _ _ PI) as Hsegs. pose proof (@pa_B_ok _ _ PI) as HB0.
pose proof (st_ok_pi_restrict_mkst (fx := fa) (w_H W) E ss ms HS Hrv) as Hms.
rewrite Hms. rewrite Hms in HS.
eapply (FpStep.fp_keep_step SEGS B LAWS (@pa_wx _ _ PI) Hsegs W fa fb (ms_regs ms) (ms_regs ms) _ _ (ms_mem ms) md Q STK sp0 FPl ly S W0 mem0 md0 own lyc Sc k Hst HJ).
intros md' HJ'. apply HK; [|exact HJ'].
pose proof (FpStep.fp_switch SEGS fa fb E (abs_ss VAL ss) (@mkst fa (ms_regs ms) (Z_to_bv 64 (BASE + ss_pc ss)) (ms_mem ms) (seg_rom SEGS)) (w_H W)
(ss_regs ss) (ms_regs ms) (Z_to_bv 64 (BASE + (ss_pc ss + 4))) HS) as H1.
assert (HR : regs_ok E (ss_regs ss) (ms_regs ms)) by (destruct HS as (_ & _ & _ & _ & _ & _ & H7 & _); exact H7).
specialize (H1 HR). unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in H1 |- *.
rewrite Hrv. rewrite unsigned_lit_small in H1 by lia. exact H1.
Qed.
Lemma rs_set : forall (fa fb : YK11.FPState) (W : world SEGS) E ss ms md Q (STK sp0 : Z) FPl ly S W0 mem0 md0 own lyc Sc k (rd : bv 5) (e : sv) (v : word),
st_ok_pi (fx := fa) SEGS VAL E ss (restrict (w_H W) ms) ->
ss_resv ss = None -> 0 <= ss_pc ss < 2 ^ 39 -> sv_denot E e = v ->
RiscvSemantics.step SEGS (@mkst fa (ms_regs ms) (Z_to_bv 64 (BASE + ss_pc ss)) (mrestrict (w_H W) (ms_mem ms)) (seg_rom SEGS)) =
MachineOk (@mkst fb (if bv_eqb rd 0 then ms_regs ms else regupd (ms_regs ms) rd v) (Z_to_bv 64 (BASE + (ss_pc ss + 4))) (mrestrict (w_H W) (ms_mem ms)) (seg_rom SEGS)) ->
ajournal SEGS B STK sp0 FPl ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k ->
(forall md', st_ok_pi (fx := fb) SEGS VAL E (mkSS (ss_pc ss + 4) (sr_set (ss_regs ss) rd e) (ss_mem ss) None (ss_facts ss))
(restrict (w_H W) (@mkst fb (if bv_eqb rd 0 then ms_regs ms else regupd (ms_regs ms) rd v) (Z_to_bv 64 (BASE + (ss_pc ss + 4))) (ms_mem ms) (seg_rom SEGS))) ->
ajournal SEGS B STK sp0 FPl ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md' k ->
SRr SEGS W (mkCfg (@mkst fb (if bv_eqb rd 0 then ms_regs ms else regupd (ms_regs ms) rd v) (Z_to_bv 64 (BASE + (ss_pc ss + 4))) (ms_mem ms) (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg ms md) Q.
Proof.
intros fa fb W E ss ms md Q STK sp0 FPl ly S W0 mem0 md0 own lyc Sc k rd e v HS Hrv Hk Hv Hst HJ HK.
pose proof (@pa_segs_low _ _ PI) as Hsegs. pose proof (@pa_B_ok _ _ PI) as HB0.
pose proof (st_ok_pi_restrict_mkst (fx := fa) (w_H W) E ss ms HS Hrv) as Hms.
rewrite Hms. rewrite Hms in HS.
eapply (FpStep.fp_keep_step SEGS B LAWS (@pa_wx _ _ PI) Hsegs W fa fb (ms_regs ms) _ _ _ (ms_mem ms) md Q STK sp0 FPl ly S W0 mem0 md0 own lyc Sc k Hst HJ).
intros md' HJ'. apply HK; [|exact HJ'].
pose proof (FpStep.fp_switch SEGS fa fb E (abs_ss VAL ss) (@mkst fa (ms_regs ms) (Z_to_bv 64 (BASE + ss_pc ss)) (ms_mem ms) (seg_rom SEGS)) (w_H W)
(sr_set (ss_regs ss) rd e) (if bv_eqb rd 0 then ms_regs ms else regupd (ms_regs ms) rd v) (Z_to_bv 64 (BASE + (ss_pc ss + 4))) HS) as H1.
assert (HR : regs_ok E (sr_set (ss_regs ss) rd e) (if bv_eqb rd 0 then ms_regs ms else regupd (ms_regs ms) rd v)).
{ apply regs_ok_set; [|exact Hv]. destruct HS as (_ & _ & _ & _ & _ & _ & H7 & _). exact H7. }
specialize (H1 HR). unfold st_ok_pi, abs_ss. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in H1 |- *.
rewrite unsigned_lit_small in H1 by lia. exact H1.
Qed.
Lemma rs_rdn8 : forall (m : word -> option byte) a v, 0 <= a -> a + 8 <= 2 ^ 64 -> val_mem SEGS m a 8 v ->
rdn SEGS m (Z_to_bv 64 a) 8 = Some (map (fun j => Z_to_bv 8 (YO0f.le_byte v 8 j)) (seq 0 8)).
Proof.
intros m a v Ha Ha8 V. apply YA0f.APSXG.rdn_of_nth; [rewrite unsigned_lit_small by lia; lia|].
intros j Hj. rewrite unsigned_lit_small by lia. apply YK0e.AX2S.rdn_one. exact (V j Hj).
Qed.
Lemma rs_val_mem_eq : forall H (m m' : word -> option byte) a n v, (forall x, m' x = m x) ->
val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v.
Proof. intros H m m' a n v Hm V k Hk. unfold mbyte, mrestrict in *. rewrite Hm. exact (V k Hk). Qed.
Lemma rs_kept_step : forall E (ss : sstate) (m0 m1 m2 : word -> option byte), ss_mem ss = [] ->
frame_of E (ss_mem ss) m1 m2 -> (forall x, m1 x = m0 x) -> forall x, m2 x = m0 x.
Proof.
intros E ss m0 m1 m2 Hm HF K x. rewrite (HF x); [exact (K x)|]. rewrite Hm. intros (r & [] & _).
Qed.
Lemma rs_fcsr_nan : forall (x : word) (fc : bv 32),
Z_to_bv 32 (Z.lor (bv_unsigned (Z_to_bv 32 (Z.lor (bv_unsigned fc)
(Fpu.fflags_bits (FP.fcmp_fl F_LT Fpu.fmt_double (bv_unsigned x) (bv_unsigned (Z_to_bv 64 D6000)))))))
(Fpu.fflags_bits (FP.fcmp_fl F_LT Fpu.fmt_double (bv_unsigned x) (bv_unsigned (Z_to_bv 64 D3837)))))
= reac_rate_snap_fcsr x fc.
Proof.
intros x fc. unfold reac_rate_snap_fcsr.
change (bv_unsigned (Z_to_bv 64 D6000)) with 4663319084467748864.
change (bv_unsigned (Z_to_bv 64 D3837)) with 4660657166816903168.
cbv beta iota delta [FP.fcmp_fl FP.fcmp_sem Fpu.fp_lt]. cbn [snd].
replace (Fpu.fp_is_nan Fpu.fmt_double 4663319084467748864) with false by (vm_compute; reflexivity).
replace (Fpu.fp_is_nan Fpu.fmt_double 4660657166816903168) with false by (vm_compute; reflexivity).
rewrite !orb_false_r.
pose proof (bv_unsigned_in_range 32 fc) as Hf. unfold bv_modulus in Hf.
destruct (Fpu.fp_is_nan Fpu.fmt_double (bv_unsigned x)).
- replace (Fpu.fflags_bits Fpu.nv_flag) with 16 by reflexivity.
assert (HR : 0 <= Z.lor (bv_unsigned fc) 16 < 2 ^ 32).
{ assert (Hn : 0 <= Z.lor (bv_unsigned fc) 16) by (apply Z.lor_nonneg; lia).
assert (Hz : Z.lor (bv_unsigned fc) 16 <> 0) by (intros X; apply Z.lor_eq_0_iff in X; lia).
split; [exact Hn|]. apply Z.log2_lt_pow2; [lia|]. rewrite Z.log2_lor by lia.
apply Z.max_lub_lt; [|cbv; reflexivity].
destruct (Z.eq_dec (bv_unsigned fc) 0) as [->|Hf0]; [cbv; reflexivity|].
apply Z.log2_lt_pow2; lia. }
rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia).
rewrite <- Z.lor_assoc, Z.lor_diag. reflexivity.
- replace (Fpu.fflags_bits Fpu.no_flags) with 0 by reflexivity. rewrite !Z.lor_0_r.
rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia). reflexivity.
Qed.
Ltac rs_fld k rsr Eat Hcv Kp :=
lazymatch goal with HS : st_ok_pi _ _ _ ?ss (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
let Ra := fresh "Ra" in let Rd := fresh "Rd" in
prreg HS rsr Ra; rewrite Eat in Ra;
lazymatch type of Hcv with val_mem _ _ ?ad _ _ => pose proof (rs_rdn8 _ ad _ ltac:(lia) ltac:(lia) (rs_val_mem_eq _ _ _ _ _ _ Kp Hcv)) as Rd end;
let w := eval vm_compute in (match plookup both3_0_tpi k with Some (PW w) => w | _ => 0 end) in
let d := eval vm_compute in (decode_any (Z_to_bv 32 w)) in
lazymatch d with Some (FLoad FMT_D ?rd ?rs ?im, _) =>
lazymatch type of HS with @st_ok_pi _ _ ?fa _ _ _ =>
lazymatch type of Rd with _ = Some ?bs =>
eapply (rs_keep fa (YK11.mkFP (bvmap_set rd (bv_extract 0 64 (le_bytes_to_word bs)) (@YK11.fp_regs fa)) (@YK11.fp_csr fa)) _ _ ss ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS eq_refl ltac:(change (ss_pc ss) with k; lia));
[ change (ss_pc ss) with k; etransitivity;
  [ exact (YK0o.fp_step_fld fa SEGS (ms_regs ms) _ _ _ (Z_to_bv 32 w) rd rs im _ _
      (pa_fetch_pw (PL := PL_both3_0) k w ltac:(vm_compute; reflexivity)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(cbn [ms_regs mkst]; replace rs with rsr by (apply bv_eq; reflexivity); rewrite Ra, YCbn.v_addi_lit; f_equal) Rd)
  | rewrite YCbn.v_addi_lit; replace (BASE + k + 4) with (BASE + (k + 4)) by lia; reflexivity ]
| exact HJ
| let md' := fresh "md" in let HS' := fresh "HS" in let HJ' := fresh "HJ" in intros md' HS' HJ'; clear HS HJ ]
end end end end.
Ltac rs_flt k rsx rsy Hx Hy C :=
lazymatch goal with HS : st_ok_pi _ _ _ ?ss (restrict _ ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
let w := eval vm_compute in (match plookup both3_0_tpi k with Some (PW w) => w | _ => 0 end) in
let d := eval vm_compute in (decode_any (Z_to_bv 32 w)) in
lazymatch d with Some (Fcmp F_LT FMT_D ?rd ?rs1 ?rs2, _) =>
lazymatch type of HS with @st_ok_pi _ _ (YK11.mkFP ?F ?fc) _ _ _ =>
let b := lazymatch type of C with _ = true => constr:(1) | _ = false => constr:(0) end in
eapply (rs_set (YK11.mkFP F fc) (YK11.mkFP F (Z_to_bv 32 (Z.lor (bv_unsigned fc) (Fpu.fflags_bits (FP.fcmp_fl F_LT Fpu.fmt_double (bv_unsigned rsx) (bv_unsigned rsy)))))) _ _ ss ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ rd (SLit b) (Z_to_bv 64 b) HS eq_refl ltac:(change (ss_pc ss) with k; lia) eq_refl);
[ change (ss_pc ss) with k; etransitivity;
  [ exact (FpStep.fp_step_flt_d F fc SEGS (ms_regs ms) _ _ _ (Z_to_bv 32 w) rd rs1 rs2 rsx rsy
      (pa_fetch_pw (PL := PL_both3_0) k w ltac:(vm_compute; reflexivity)) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(Hx rs1) ltac:(Hy rs2))
  | rewrite C, YCbn.v_addi_lit; replace (BASE + k + 4) with (BASE + (k + 4)) by lia; reflexivity ]
| exact HJ
| let md' := fresh "md" in let HS' := fresh "HS" in let HJ' := fresh "HJ" in intros md' HS' HJ'; clear HS HJ ]
end end end.
Lemma rs_walk : forall ly S W (regs : bvmap 5 word) mem md ch,
afn_pre SEGS B REAC_RATE_SNAP_STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_HI 99) + 1608) 8 D6000 ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_HI 98) + 1812) 8 D3837 ->
SRr SEGS W (cfg_at SEGS (BASE + AF_both3_reac_rate_snap) regs mem md)
(treac_rate_snap_post fx regs ly S W mem md).
Proof.
intros ly S W regs mem md ch HPRE Hc6 Hc3.
pose proof (@pa_segs_low _ _ PI) as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
rewrite FpStep.fp_getr_upd in Hra by (cbv; lia).
destruct (rs_entry W regs mem) as [HS SHOK].
pose proof (ajournal_init SEGS B REAC_RATE_SNAP_STK [] ly S W _ mem md ch HPRE) as HJ.
rewrite FpStep.fp_spZ_upd in HJ by (cbv; lia).
pose proof (pa_hi_img 99 ltac:(vm_compute; lia)) as HH99. pose proof (pa_hi_img 98 ltac:(vm_compute; lia)) as HH98.
unfold YImgTop.IMG_TOP in HH99, HH98.
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E418 : ew E 418%nat = Z_to_bv 64 (VAL (A_HI 98))) by (subst E; apply Eimg_img; unfold A_HI, A_TEXT, A_LIM; lia).
assert (E419 : ew E 419%nat = Z_to_bv 64 (VAL (A_HI 99))) by (subst E; apply Eimg_img; unfold A_HI, A_TEXT, A_LIM; lia).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
assert (KEPT : forall x : word, mem x = mem x) by reflexivity.
unfold cfg_at. change (w64 (BASE + AF_both3_reac_rate_snap)) with (Z_to_bv 64 (BASE + AF_both3_reac_rate_snap)).
paj_run_tok (paj_run (fx := fx) (PL := PL_both3_0) (PI := PI) B LAWS) HS HJ SHOK RS_Bspan; [awr_ok_tac |].
lazymatch goal with HF : frame_of ?Ex (ss_mem ?ss) mem ?m2 |- _ => pose proof (rs_kept_step Ex ss mem mem m2 eq_refl HF KEPT) as K1 end.
clear KEPT. rename K1 into KEPT.
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
rs_fld 32016 (11%bv : bv 5) E419 Hc6 KEPT.
rs_fld 32020 (10%bv : bv 5) E418 Hc3 KEPT.
destruct (FP.flt_d (Sem.reg_get (@YK11.fp_regs fx) (Z_to_bv 5 10)) (Z_to_bv 64 D6000)) eqn:C6;
destruct (FP.flt_d (Sem.reg_get (@YK11.fp_regs fx) (Z_to_bv 5 10)) (Z_to_bv 64 D3837)) eqn:C3.
all: rs_flt 32024 (Sem.reg_get (@YK11.fp_regs fx) (Z_to_bv 5 10)) (Z_to_bv 64 D6000)
  ltac:(fun r => cbn [YK11.fp_regs]; rewrite !FpStep.fp_rg_other by (vm_compute; lia); f_equal; apply bv_eq; reflexivity)
  ltac:(fun r => cbn [YK11.fp_regs]; rewrite FpStep.fp_rg_other by (vm_compute; lia);
        match goal with |- Sem.reg_get (bvmap_set ?k _ _) _ = _ => replace r with k by (apply bv_eq; reflexivity) end;
        rewrite FpStep.fp_rg_same; apply bv_eq; vm_compute; reflexivity) C6.
all: rs_flt 32028 (Sem.reg_get (@YK11.fp_regs fx) (Z_to_bv 5 10)) (Z_to_bv 64 D3837)
  ltac:(fun r => cbn [YK11.fp_regs]; rewrite !FpStep.fp_rg_other by (vm_compute; lia); f_equal; apply bv_eq; reflexivity)
  ltac:(fun r => cbn [YK11.fp_regs];
        match goal with |- Sem.reg_get (bvmap_set ?k _ _) _ = _ => replace r with k by (apply bv_eq; reflexivity) end;
        rewrite FpStep.fp_rg_same; apply bv_eq; vm_compute; reflexivity) C3.
all: lazymatch goal with HS : @st_ok_pi _ _ ?f4 _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
paj_run_tok (paj_run (fx := f4) (PL := PL_both3_0) (PI := PI) B LAWS) HS HJ SHOK RS_Bspan; [awr_ok_tac |] end.
all: lazymatch goal with HF : frame_of ?Ex (ss_mem ?ss) ?m1 ?m2, K : forall x : word, ?m1 x = ?m0 x |- _ =>
pose proof (rs_kept_step Ex ss m0 m1 m2 eq_refl HF K) as K2; clear K end.
all: repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
all: lazymatch goal with HS : @st_ok_pi _ _ ?f4 _ ?ssx (restrict _ ?msc), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
prreg HS (10%bv : bv 5) R10; prreg HS (1%bv : bv 5) R1;
eapply (paj_ret_at (fx := f4) (PL := PL_both3_0) (PI := PI) _ _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
let mat' := fresh "mat" in intros mat';
unfold treac_rate_snap_post; cbv beta;
exists f4; split;
[ cbn [YK11.fp_regs];
  match goal with |- bvmap_set ?a ?b (bvmap_set ?c ?d _) = _ =>
    replace a with (Z_to_bv 5 14) by (apply bv_eq; reflexivity);
    replace c with (Z_to_bv 5 15) by (apply bv_eq; reflexivity);
    replace b with (Z_to_bv 64 D3837) by (apply bv_eq; vm_compute; reflexivity);
    replace d with (Z_to_bv 64 D6000) by (apply bv_eq; vm_compute; reflexivity) end; reflexivity |];
split; [cbn [YK11.fp_csr]; exact (rs_fcsr_nan _ _)|]; apply apost_base_same_fx;
exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|];
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ _ _ HS); [exact HAE | vm_compute; reflexivity]|];
split; [cbn [ms_regs]; rewrite R10; unfold reac_rate_snap_model, w64; rewrite ?C3, ?C6; reflexivity|];
split; [apply Permutation_refl|]; split; [reflexivity|];
exact K2 end.
Qed.
End w.
Theorem pb_reac_rate_snap : treac_rate_snap_spec.
Proof. intros fq ly S W regs mem md ch HPRE _ H6 H3. exact (rs_walk (fx := fq) ly S W regs mem md ch HPRE H6 H3). Qed.
End h.
End f.
End d.
