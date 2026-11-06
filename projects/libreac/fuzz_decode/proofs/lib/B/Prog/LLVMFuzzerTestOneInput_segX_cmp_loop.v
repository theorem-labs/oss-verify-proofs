(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* LLVMFuzzerTestOneInput_segX_cmp_loop: the bcmp double loop L3 / L4 of image B's LLVMFuzzerTestOneInput cmp segment,
   the path the accepted plain decode takes (a0 = ns > 0 at +0x6f0):
     L3 +0x7c0 s3 = s2; s10 = s6; s8 = 56(s1) = ns; +0x7d0 blez 72(s1) -> +0x80c (refuted, ns > 0)
     L4 +0x7d4 bltu s5, s3 -> +0xb84; +0x7d8 bltu s9, s10 -> +0xb84   (UBSan: out + s3 / copy + 50 + s10 wrap; refuted)
        +0x7dc .. +0x7f0 bcmp(out + s3, copy + 50 + s10, 3)
        +0x7f4 .. +0x808 s4 |= (a0 != 0); s3 += 3; s10 += 3 * nch; s8 -= 1; bnez s8 -> +0x7d4
     +0x80c .. +0x820 s11 += 1; s6 += 3; s2 += 48(s1) = 3 * ns; bne s11, 64(s1) = nch -> +0x7c0
     +0x824 .. +0x82c s6 = len; s11 = copy; bnez s4 -> +0xb88 (abort; refuted, every bcmp returned 0)
     +0x830 ld a0, 88(s1); +0x834 jal free
   Turn (j, k) compares the decoder's output bytes 3 * (j * ns + k) .. + 2 with the frame's bytes
   50 + 3 * (k * nch + j) .. + 2, which plain_out's definition makes equal (cm_plain_byte_at of
   lib/B/Prog/LLVMFuzzerTestOneInput_segX_cmp_defs.v), so bcmp returns 0 (abcmp_realizes through lib/Reusable/YCbq.v
   aj_bcmp_at). The inner loop is by induction on ns - k, the outer on nch - j, each turn's state built afresh at
   its head (a Theorem Labs lane's GrantEntrySweepS2.v:236 gsw_rows_loop; the bcmp call and the facts carried across it as
   GrantEntrySweepS4.v:1094 gb_turn does). *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YN1y.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YC5d YI16 YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaJournal.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import
DecodeBSyms DecodeBList DecodeBAddr DecodeBPa DecodeBImg DecodeBPaLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import
check_round_trip_cg LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_segX_cmp_defs
LLVMFuzzerTestOneInput_segX_cmp_kit LLVMFuzzerTestOneInput_segX_cmp_st.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require reac_decode_plain_le_c.
Import ListNotations.
Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Module CPlainL := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_decode_plain_le_c.

(* a Theorem Labs lane's GrantEntrySweepS4.v:71 gb_nth_unsigned. *)
Lemma cm_nth_unsigned : forall (l : list byte) n,
  nth n (map (fun b : byte => bv_unsigned b) l) 0 = bv_unsigned (nth n l (Z_to_bv 8 0)).
Proof.
  induction l as [|b l IH]; intros n; destruct n as [|n]; cbn [map nth]; try reflexivity. apply IH.
Qed.

Section loop. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation SEGS := decodesegsB0.
#[local] Notation VAL := decodeb_val.
#[local] Notation BASE := (@pa_val _ decodeb_listing PI_decodeb A_TEXT).

(* A byte of a garr8 array, read through the view. *)
Lemma cm_garr8_aview : forall (H : word -> bool) mem base l n,
  garr8 SEGS (mrestrict H mem) base l -> (n < length l)%nat ->
  aview SEGS H mem (base + Z.of_nat n) = Some (nth n l 0).
Proof.
intros H mem base l n Hg Hn. destruct (Hg n Hn) as [Hv Hr].
specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
unfold aview. rewrite Hv. cbn [option_map]. f_equal.
rewrite (le_byte_small (nth n l 0) 1 0) by (cbn; lia). change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.

Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HPCF : pc_wrap_free (as_code B) = decodeb_sigma DB___interceptor_trampoline_free.
Hypothesis HCELLS : dec_crt_cells B.
Hypothesis HROS : dec_ro_rd_unowned B.
Hypothesis HRNE : dec_rom_no_errno B.
Hypothesis ABCMP : @abcmp_realizes fx rc SEGS B (decodeb_sigma DB___interceptor_trampoline_bcmp).
Variable cx : dctx.
(* The entry's read-only view, which the journal carries to every state (cm_rom_rd). *)
Hypothesis HROMcx : rom_view SEGS (d_W cx) (d_mem cx).
Hypothesis Hnlen : d_n cx = Z.of_nat (length (d_pl cx)).
Variables (ly : alayout) (S : astate) (W : world SEGS) (out res mode nch ns : Z).
Hypothesis Hinout : In (out, dec_b_olen nch ns) (ablocks B ly S).
Hypothesis Hinres : In (res, dec_b_len (d_n cx)) (ablocks B ly S).
Hypothesis Hok : CPlainL.plain_ok (dec_b_len (d_n cx)) (d_body cx) nch ns = true.
Hypothesis Hnch : nch <= 127.
Hypothesis Hns : ns <= 127.
Variable Q : world SEGS -> config -> Prop.
(* What the rest of the segment does from the call of free #1 (cm_tail of
   lib/B/Prog/LLVMFuzzerTestOneInput_segX_cmp_tail.v). *)
Hypothesis KFREE : forall regs mem md,
  dec_b_core B cx ly S W regs mem md dec_ev_6f0 -> cm_mem cx out res mode nch ns W mem ->
  YK11.getr regs 10 = w64 out -> YK11.getr regs 1 = w64 (DEC_A_LLVMF + 0x838) ->
  YK11.getr regs 22 = w64 (dec_b_len (d_n cx)) -> YK11.getr regs 27 = w64 res ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (pc_wrap_free (as_code B))) mem (YK11.seg_rom SEGS)) md) Q.

Let RUN := @paj_run fx rc dec_B_sink_head decodeb_listing PL_decodeb PI_decodeb B LAWS.
Let RUNTO := @paj_run_to fx rc dec_B_sink_head decodeb_listing PL_decodeb PI_decodeb B LAWS.
Let BR := @paj_branch fx rc decodeb_listing PI_decodeb.

(* The memory the loops read: the cut point's clauses, 48(s1) = 3 * ns (stored at +0x7bc), and the decoder's output. *)
Definition cm_memL (mem : word -> option byte) : Prop :=
  cm_mem cx out res mode nch ns W mem /\
  dec_b_slot cx (aview SEGS (w_H W) mem) 48 (3 * ns) /\
  garr8 SEGS (mrestrict (w_H W) mem) out
    (map (fun b : byte => bv_unsigned b) (CPlainL.plain_out (d_body cx) nch ns)).

(* The registers of the outer head +0x7c0 at turn j, and of the inner head +0x7d4 at turn (j, k). *)
Definition cm_rL3 (j : Z) (regs : bvmap 5 word) : Prop :=
  YK11.getr regs 18 = w64 (3 * j * ns) /\ YK11.getr regs 20 = w64 0 /\
  YK11.getr regs 21 = w64 (18446744073709551615 - out) /\ YK11.getr regs 22 = w64 (3 * j) /\
  YK11.getr regs 23 = w64 (3 * nch) /\ YK11.getr regs 25 = w64 (18446744073709551615 - (res + 50)) /\
  YK11.getr regs 27 = w64 j.
Definition cm_rL4 (j k : Z) (regs : bvmap 5 word) : Prop :=
  cm_rL3 j regs /\ YK11.getr regs 19 = w64 (3 * (j * ns + k)) /\ YK11.getr regs 24 = w64 (ns - k) /\
  YK11.getr regs 26 = w64 (3 * j + 3 * k * nch).

Lemma cm_facts : dec_b_len (d_n cx) = 1492 /\ 0 < nch /\ 0 < ns /\ nch * ns <= 480 /\
  dec_b_olen nch ns = 3 * nch * ns /\ Z.of_nat (length (d_body cx)) = 1492 /\
  nch mod 2 ^ 32 = nch /\ ns mod 2 ^ 32 = ns /\ ns mod 2 ^ 64 = ns.
Proof.
destruct (cm_plain_ok_facts _ _ _ _ Hok) as (Hlen & Hnch0 & Hns0 & Hprod).
split; [exact Hlen|]. split; [exact Hnch0|]. split; [exact Hns0|]. split; [exact Hprod|].
split; [unfold dec_b_olen; rewrite (proj2 (Z.ltb_lt 0 nch) Hnch0), (proj2 (Z.ltb_lt 0 ns) Hns0); reflexivity|].
split.
{ unfold d_body. rewrite length_skipn. revert Hlen. unfold dec_b_len, dec_b_u. rewrite Hnlen. lia. }
split; [apply Z.mod_small; lia|]. split; [apply Z.mod_small; lia | apply Z.mod_small; lia].
Qed.

(* Turn (j, k)'s two triples agree (plain_out's definition, cm_plain_byte_at). *)
Lemma cm_byte_match : forall (H : word -> bool) mem j k r,
  garr8 SEGS (mrestrict H mem) out (map (fun b : byte => bv_unsigned b) (CPlainL.plain_out (d_body cx) nch ns)) ->
  garr8 SEGS (mrestrict H mem) res (map (fun b : byte => bv_unsigned b) (d_body cx)) ->
  0 <= j < nch -> 0 <= k < ns -> 0 <= r < 3 ->
  aview SEGS H mem (out + 3 * (j * ns + k) + r) = aview SEGS H mem (res + 50 + (3 * j + 3 * k * nch) + r).
Proof.
intros H mem j k r Go Gr Hj Hk Hr.
destruct cm_facts as (Hlen & Hnch0 & Hns0 & Hprod & Holen & Hbl & _).
assert (Hkj : k * nch + j < nch * ns) by (clear - Hj Hk Hnch0 Hns0; nia).
assert (Hjk : j * ns + k < nch * ns) by (clear - Hj Hk Hnch0 Hns0; nia).
replace (out + 3 * (j * ns + k) + r) with (out + Z.of_nat (Z.to_nat (3 * (j * ns + k) + r))) by lia.
replace (res + 50 + (3 * j + 3 * k * nch) + r) with (res + Z.of_nat (Z.to_nat (50 + 3 * (k * nch + j) + r))) by lia.
rewrite (cm_garr8_aview H mem out _ _ Go).
2:{ rewrite length_map, cm_plain_len. lia. }
rewrite (cm_garr8_aview H mem res _ _ Gr).
2:{ rewrite length_map. lia. }
rewrite !cm_nth_unsigned. f_equal. f_equal.
rewrite cm_nth_plain by lia.
apply cm_plain_byte_at; lia.
Qed.

(* What a call that keeps every byte outside its stack window below d_sp1 (bcmp) leaves of the frame invariant
   and of the loops' memory clauses. *)
Lemma cm_after_call : forall regs mem md regs2 mem2 md2,
  dec_b_core B cx ly S W regs mem md dec_ev_6f0 -> cm_memL mem ->
  @ajournal rc dec_B_sink_head SEGS B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly S W mem2 md2 dec_ev_6f0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx - 2 * ESTACK <= a < d_sp1 cx) ->
     aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
  YK11.getr regs2 2 = YK11.getr regs 2 -> YK11.getr regs2 3 = YK11.getr regs 3 ->
  YK11.getr regs2 4 = YK11.getr regs 4 -> YK11.getr regs2 8 = YK11.getr regs 8 ->
  YK11.getr regs2 9 = YK11.getr regs 9 ->
  dec_b_core B cx ly S W regs2 mem2 md2 dec_ev_6f0 /\ cm_memL mem2.
Proof.
intros regs mem md regs2 mem2 md2 HC (HM & H48 & HPO) HJ2 HK Hpr E2 E3 E4 E8 E9.
pose proof HC as (HJ & Hfrs & Hs0 & Hs1 & Hsp & Hsp1r & Hsp1al & Hgp & Htp & Hsaved & HF4096 & HFal & HFpres &
  HFLw & Hpay & Hgarr).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk00 & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly as (_ & _ & _ & _ & _ & HlyF & _).
pose proof HJ2 as (HAR2 & _).
assert (FFS : DEC_LLVMF_STK = 32768) by reflexivity.
assert (ESV : ESTACK = 4096) by reflexivity.
assert (SHV : SHADOW_OFF = 0x7fff8000) by reflexivity.
pose proof (@alloc_ceiling_val rc) as [ACR _].
assert (Hin0 : In (DEC_FCLASS, d_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr ly DEC_FCLASS (d_fpos cx) = d_F cx) by (unfold d_F, frame_addr; rewrite HlyF; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S W mem md DEC_FCLASS (d_fpos cx) HAR Hin0) as (Hfb1 & Hfb2 & _).
rewrite EFA in Hfb1, Hfb2. change (fs_frame_bytes DEC_FCLASS) with 64 in Hfb2.
destruct (al_blocks _ _ LAWS _ _ _ _ _ out _ HAR Hinout) as (_ & Ho4096 & Hoceil & _ & _ & _ & Hom).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res _ HAR Hinres) as (_ & Hr4096 & Hrceil & _ & _ & _ & Hrm).
pose proof (req_size_pos (dec_b_olen nch ns) ltac:(lia)) as [_ Hrqo].
pose proof (req_size_pos (dec_b_len (d_n cx)) ltac:(lia)) as [_ Hrqr].
destruct cm_facts as (Hlen & Hnch0 & Hns0 & Hprod & Holen & Hbl & _).
assert (KS : forall a, d_sp1 cx <= a < d_sp0 cx -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a)
  by (intros a Ha; apply HK; lia).
assert (KF : forall a, d_F cx <= a < d_F cx + 64 -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a)
  by (intros a Ha; apply HK; lia).
assert (KH : forall a, d_SH cx <= a < d_SH cx + 8 -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. unfold d_SH, shadow_addr in Ha.
  pose proof (Z.div_pos (d_F cx) 8 ltac:(lia) ltac:(lia)).
  assert (d_F cx / 8 <= 17592186044416)
    by (change 17592186044416 with (2 ^ 47 / 8); apply Z.div_le_mono; lia).
  rewrite SHV in Ha. apply HK; lia. }
split.
- apply (cm_core_kept B cx ly S W regs mem md dec_ev_6f0 ly S W regs2 mem2 md2 dec_ev_6f0 HC HJ2).
  + exact Hfrs.
  + exact E8.
  + exact E9.
  + unfold spZ. rewrite E2. reflexivity.
  + exact E3.
  + exact E4.
  + intros a Ha. apply KS. lia.
  + exact KF.
  + intros a Ha. apply Hpr. exact (HFpres a Ha).
  + exact Hpay.
  + intros i Hi. rewrite <- Hnlen in Hi.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ (d_p cx) (d_n cx) HAR (Hpay ltac:(lia))) as (_ & Hp4096 & Hpceil & _).
    pose proof (req_size_pos (d_n cx) ltac:(lia)) as [_ Hrqp].
    apply HK; lia.
- split; [|split].
  + apply (cm_mem_kept B cx ly S W mem md ly S W mem2 md2 out res mode nch ns HCELLS HAR HAR2
      (cm_rom_rd B cx _ _ _ _ _ _ _ _ HROS HRNE HROMcx HJ) (cm_rom_rd B cx _ _ _ _ _ _ _ _ HROS HRNE HROMcx HJ2)).
    * intros a Ha _. apply KS. lia.
    * exact KF.
    * exact KH.
    * intros i Hi. apply HK; lia.
    * exact HM.
  + unfold dec_b_slot in *. rewrite <- H48. apply rdword_ext. intros j Hj. apply KS. lia.
  + apply (cm_garr8_kept (w_H W) (w_H W) mem mem2); [|exact HPO].
    rewrite length_map, cm_plain_len. intros i Hi. apply HK; lia.
Qed.

Lemma cm_inner : forall j, 0 <= j < nch ->
  (forall regs mem md, 0 <= j + 1 < nch ->
     dec_b_core B cx ly S W regs mem md dec_ev_6f0 -> cm_memL mem -> cm_rL3 (j + 1) regs ->
     SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 0x7c0)) mem (YK11.seg_rom SEGS)) md) Q) ->
  forall (n : nat) k regs mem md,
  Z.to_nat (ns - k) = n -> 0 <= k < ns ->
  dec_b_core B cx ly S W regs mem md dec_ev_6f0 -> cm_memL mem -> cm_rL4 j k regs ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 0x7d4)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros j Hj KL3 n. induction n as [|n IH]; intros k regs mem md Hn Hk HC HML HR; [lia|].
destruct cm_facts as (Hlen & Hnch0 & Hns0 & Hprod & Holen & Hbl & Hn32 & Hs32 & Hs64).
pose proof HML as (HM & H48 & HPO).
pose proof HM as (_ & _ & _ & HRB & _).
destruct HR as ((R18 & R20 & R21 & R22 & R23 & R25 & R27) & R19 & R24 & R26).
pose proof HC as (HJ & Hfrs & Hs0 & Hs1 & Hsp & Hsp1r & Hsp1al & Hgp & Htp & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk00 & Hceil & Hslo & Hshi & H47 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ out _ HAR Hinout) as (_ & Ho4096 & Hoceil & Hoapp & Hopres & _ & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res _ HAR Hinres) as (_ & Hr4096 & Hrceil & Hrapp & Hrpres & _ & _).
pose proof (req_size_pos (dec_b_olen nch ns) ltac:(lia)) as [_ Hrqo].
pose proof (req_size_pos (dec_b_len (d_n cx)) ltac:(lia)) as [_ Hrqr].
pose proof (@alloc_ceiling_val rc) as [ACR _].
assert (FFS : DEC_LLVMF_STK = 32768) by reflexivity.
assert (ESV : ESTACK = 4096) by reflexivity.
assert (Hjk : j * ns + k < nch * ns) by (clear - Hj Hk Hnch0 Hns0; nia).
assert (Hkj : k * nch + j < nch * ns) by (clear - Hj Hk Hnch0 Hns0; nia).
(* ---- the state at +0x7d4 ---- *)
pose proof (@cm_stokL fx rc B cx W ly S regs mem md dec_ev_6f0 out res mode nch ns 0x7d4 HC HM H48
  ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
assert (EPC : w64 (DEC_A_LLVMF + 0x7d4) = Z_to_bv 64 (BASE + 0x7d4)) by (unfold w64; f_equal; vm_compute; reflexivity).
rewrite EPC in HS. clear EPC.
remember (cm_env cx regs out res (dec_b_len (d_n cx)) (ns mod 2 ^ 64) (nch mod 2 ^ 32) (ns mod 2 ^ 32) 0 (3 * ns))
  as E eqn:HE.
assert (SHOK : sh_ok SEGS cm_Bx [] E (mrestrict (w_H W) mem)) by constructor.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply cm_env_img).
assert (ER : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = YK11.getr regs r)
  by (intros kk r Hkk; subst E; apply cm_env_reg; exact Hkk).
assert (E2 : ew E 2 = YK11.getr regs 2) by exact (ER 2%nat 2%bv eq_refl).
assert (E3 : ew E 3 = YK11.getr regs 3) by exact (ER 3%nat 3%bv eq_refl).
assert (E4 : ew E 4 = YK11.getr regs 4) by exact (ER 4%nat 4%bv eq_refl).
assert (E8 : ew E 8 = YK11.getr regs 8) by exact (ER 8%nat 8%bv eq_refl).
assert (E9 : ew E 9 = YK11.getr regs 9) by exact (ER 9%nat 9%bv eq_refl).
assert (E18 : ew E 18 = w64 (3 * j * ns)) by (rewrite (ER 18%nat 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = w64 (3 * (j * ns + k))) by (rewrite (ER 19%nat 19%bv eq_refl); exact R19).
assert (E20 : ew E 20 = w64 0) by (rewrite (ER 20%nat 20%bv eq_refl); exact R20).
assert (E21 : ew E 21 = w64 (18446744073709551615 - out)) by (rewrite (ER 21%nat 21%bv eq_refl); exact R21).
assert (E22 : ew E 22 = w64 (3 * j)) by (rewrite (ER 22%nat 22%bv eq_refl); exact R22).
assert (E23 : ew E 23 = w64 (3 * nch)) by (rewrite (ER 23%nat 23%bv eq_refl); exact R23).
assert (E24 : ew E 24 = w64 (ns - k)) by (rewrite (ER 24%nat 24%bv eq_refl); exact R24).
assert (E25 : ew E 25 = w64 (18446744073709551615 - (res + 50))) by (rewrite (ER 25%nat 25%bv eq_refl); exact R25).
assert (E26 : ew E 26 = w64 (3 * j + 3 * k * nch)) by (rewrite (ER 26%nat 26%bv eq_refl); exact R26).
assert (E27 : ew E 27 = w64 j) by (rewrite (ER 27%nat 27%bv eq_refl); exact R27).
assert (E33 : ew E 33 = w64 out) by (subst E; apply cm_env_33).
assert (E39 : ew E 39 = w64 (res + 50)) by (subst E; apply cm_env_39).
clear HE ER.
(* +0x7d4 `bltu s5, s3` into the UBSan trap: out + 3 * (j * ns + k) does not wrap *)
psrr_branch_tok RUN BR HS SHOK cm_Bspan.
{ exfalso. rewrite branch_ltu_U in Hc.
  rewrite (U_atom E 21 (18446744073709551615 - out)) in Hc by first [exact E21 | lia].
  rewrite (U_atom E 19 (3 * (j * ns + k))) in Hc by first [exact E19 | lia].
  apply Z.ltb_lt in Hc. lia. }
clear Hc.
paj_run_tok RUN HS HJ SHOK cm_Bspan; [cm_awr_ro|].
cm_memeq HF.
(* +0x7d8 `bltu s9, s10` into the UBSan trap: copy + 50 + 3 * j + 3 * k * nch does not wrap *)
psrr_branch_tok RUN BR HS SHOK cm_Bspan.
{ exfalso. cm_norm Hc. rewrite cm_bltu in Hc. unfold w64 in Hc. cm_unlit Hc. apply Z.ltb_lt in Hc. lia. }
clear Hc.
paj_run_tok RUN HS HJ SHOK cm_Bspan; [cm_awr_ro|].
cm_memeq HF.
(* ---- +0x7f0: bcmp(out + 3 * (j * ns + k), copy + 50 + 3 * j + 3 * k * nch, 3) ---- *)
pmkst HS. rewrite Hmem. rewrite Hmem in HJ.
change (pa_sigma DB___interceptor_trampoline_bcmp) with (decodeb_sigma DB___interceptor_trampoline_bcmp).
lazymatch type of HS with context [restrict _ ?msf] =>
  assert (Q2 : YK11.getr (ms_regs msf) 2 = YK11.getr regs 2) by (cm_val HS);
  assert (Q3 : YK11.getr (ms_regs msf) 3 = YK11.getr regs 3) by (cm_val HS);
  assert (Q4 : YK11.getr (ms_regs msf) 4 = YK11.getr regs 4) by (cm_val HS);
  assert (Q8 : YK11.getr (ms_regs msf) 8 = YK11.getr regs 8) by (cm_val HS);
  assert (Q9 : YK11.getr (ms_regs msf) 9 = YK11.getr regs 9) by (cm_val HS);
  assert (Q18 : YK11.getr (ms_regs msf) 18 = w64 (3 * j * ns)) by (cm_val HS);
  assert (Q19 : YK11.getr (ms_regs msf) 19 = w64 (3 * (j * ns + k))) by (cm_val HS);
  assert (Q20 : YK11.getr (ms_regs msf) 20 = w64 0) by (cm_val HS);
  assert (Q21 : YK11.getr (ms_regs msf) 21 = w64 (18446744073709551615 - out)) by (cm_val HS);
  assert (Q22 : YK11.getr (ms_regs msf) 22 = w64 (3 * j)) by (cm_val HS);
  assert (Q23 : YK11.getr (ms_regs msf) 23 = w64 (3 * nch)) by (cm_val HS);
  assert (Q24 : YK11.getr (ms_regs msf) 24 = w64 (ns - k)) by (cm_val HS);
  assert (Q25 : YK11.getr (ms_regs msf) 25 = w64 (18446744073709551615 - (res + 50))) by (cm_val HS);
  assert (Q26 : YK11.getr (ms_regs msf) 26 = w64 (3 * j + 3 * k * nch)) by (cm_val HS);
  assert (Q27 : YK11.getr (ms_regs msf) 27 = w64 j) by (cm_val HS);
  assert (Ta0 : YK11.getr (ms_regs msf) 10 = w64 (out + 3 * (j * ns + k))) by (cm_val HS);
  assert (Ta1 : YK11.getr (ms_regs msf) 11 = w64 (res + 50 + (3 * j + 3 * k * nch))) by (cm_val HS);
  assert (Ta2 : YK11.getr (ms_regs msf) 12 = w64 3) by (cm_val HS);
  assert (Tra : YK11.getr (ms_regs msf) 1 = w64 (DEC_A_LLVMF + 0x7f4))
    by (cm_ra HS; unfold w64; f_equal; vm_compute; reflexivity);
  set (rT := ms_regs msf) in *
end.
assert (Tsp : spZ rT = d_sp1 cx) by (unfold spZ in *; rewrite Q2; exact Hsp).
eapply SRr_bind.
{ eapply (aj_bcmp_at (SK := dec_B_sink_head) SEGS B LAWS decodeb_segs_low _ ABCMP W rT mem DEC_LLVMF_STK
            (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly S _
            dec_ev_6f0 (out + 3 * (j * ns + k)) (res + 50 + (3 * j + 3 * k * nch)) 3
            (d_sp1 cx - d_sp0 cx) (YK11.getr rT 1) HJ).
  - exact Ta0.
  - exact Ta1.
  - exact Ta2.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - rewrite Tsp. lia.
  - rewrite Z.mod_divide in Hsp0al, Hsp1al by lia. rewrite Z.mod_divide by lia.
    destruct Hsp0al as [q0 Hq0]. destruct Hsp1al as [q1 Hq1]. exists (2 * q1 - q0). lia.
  - lia.
  - lia.
  - rewrite Q3. exact Hgp.
  - rewrite Q4. exact Htp.
  - reflexivity.
  - rewrite Tra. unfold w64. rewrite <- cm_base_eqS.
    apply (ret_ok_codeptr_v (PI := PI_decodeb)); first [lia | reflexivity].
  - intros a Ha. split; [apply (aview_some_of_apresent SEGS); apply (proj1 (Hopres a ltac:(lia)))|].
    rewrite Tsp. lia.
  - intros a Ha. split; [apply (aview_some_of_apresent SEGS); apply (proj1 (Hrpres a ltac:(lia)))|].
    rewrite Tsp. lia.
  - intros a Ha. lia.
  - intros a Ha. lia.
  - apply (amem_range_of_block SEGS B LAWS ly S W mem _ out _ _ 3 HAR Hinout); lia.
  - apply (amem_range_of_block SEGS B LAWS ly S W mem _ res _ _ 3 HAR Hinres); lia.
  - apply (range_addressable_of_block SEGS B LAWS ly S W mem _ out _ _ 3 HAR Hinout); lia.
  - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly S W mem _ out _ _ 3 HAR Hinout); lia.
  - apply (range_addressable_of_block SEGS B LAWS ly S W mem _ res _ _ 3 HAR Hinres); lia.
  - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly S W mem _ res _ _ 3 HAR Hinres); lia. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & v4 & -> & HJ4 & HP4 & Hv4 & Hcmp4 & Hkp4 & Hpr4).
replace (d_sp0 cx + (d_sp1 cx - d_sp0 cx)) with (d_sp1 cx) in Hkp4 by lia.
(* the triples agree, so bcmp returns 0 *)
assert (Hv0 : v4 = w64 0).
{ apply Hcmp4. intros r Hr. exact (cm_byte_match (w_H W) mem j k r HPO HRB Hj Hk Hr). }
rewrite Hv0 in Hv4. clear Hv0 Hcmp4.
assert (P : forall r, acallee_saved r -> YK11.getr regs4 (Z_to_bv 5 r) = YK11.getr rT (Z_to_bv 5 r)) by exact HP4.
assert (P2 : YK11.getr regs4 2 = YK11.getr regs 2) by (rewrite <- Q2; exact (P 2 ltac:(unfold acallee_saved; lia))).
assert (P3 : YK11.getr regs4 3 = YK11.getr regs 3) by (rewrite <- Q3; exact (P 3 ltac:(unfold acallee_saved; lia))).
assert (P4 : YK11.getr regs4 4 = YK11.getr regs 4) by (rewrite <- Q4; exact (P 4 ltac:(unfold acallee_saved; lia))).
assert (P8 : YK11.getr regs4 8 = YK11.getr regs 8) by (rewrite <- Q8; exact (P 8 ltac:(unfold acallee_saved; lia))).
assert (P9 : YK11.getr regs4 9 = YK11.getr regs 9) by (rewrite <- Q9; exact (P 9 ltac:(unfold acallee_saved; lia))).
assert (P18 : YK11.getr regs4 18 = w64 (3 * j * ns)) by (rewrite <- Q18; exact (P 18 ltac:(unfold acallee_saved; lia))).
assert (P19 : YK11.getr regs4 19 = w64 (3 * (j * ns + k))) by (rewrite <- Q19; exact (P 19 ltac:(unfold acallee_saved; lia))).
assert (P20 : YK11.getr regs4 20 = w64 0) by (rewrite <- Q20; exact (P 20 ltac:(unfold acallee_saved; lia))).
assert (P21 : YK11.getr regs4 21 = w64 (18446744073709551615 - out)) by (rewrite <- Q21; exact (P 21 ltac:(unfold acallee_saved; lia))).
assert (P22 : YK11.getr regs4 22 = w64 (3 * j)) by (rewrite <- Q22; exact (P 22 ltac:(unfold acallee_saved; lia))).
assert (P23 : YK11.getr regs4 23 = w64 (3 * nch)) by (rewrite <- Q23; exact (P 23 ltac:(unfold acallee_saved; lia))).
assert (P24 : YK11.getr regs4 24 = w64 (ns - k)) by (rewrite <- Q24; exact (P 24 ltac:(unfold acallee_saved; lia))).
assert (P25 : YK11.getr regs4 25 = w64 (18446744073709551615 - (res + 50))) by (rewrite <- Q25; exact (P 25 ltac:(unfold acallee_saved; lia))).
assert (P26 : YK11.getr regs4 26 = w64 (3 * j + 3 * k * nch)) by (rewrite <- Q26; exact (P 26 ltac:(unfold acallee_saved; lia))).
assert (P27 : YK11.getr regs4 27 = w64 j) by (rewrite <- Q27; exact (P 27 ltac:(unfold acallee_saved; lia))).
destruct (cm_after_call regs mem md regs4 mem4 md4 HC HML HJ4 Hkp4 Hpr4 P2 P3 P4 P8 P9) as [HC4 HML4].
clear HS SHOK HEI HJ Hmem.
rewrite Tra.
(* ---- the state at +0x7f4 ---- *)
pose proof HML4 as (HM4 & H484 & HPO4).
pose proof (@cm_stokL fx rc B cx W ly S regs4 mem4 md4 dec_ev_6f0 out res mode nch ns 0x7f4 HC4 HM4 H484
  ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
pose proof HC4 as (HJ & _).
remember (cm_env cx regs4 out res (dec_b_len (d_n cx)) (ns mod 2 ^ 64) (nch mod 2 ^ 32) (ns mod 2 ^ 32) 0 (3 * ns))
  as E' eqn:HE'.
assert (SHOK : sh_ok SEGS cm_Bx [] E' (mrestrict (w_H W) mem4)) by constructor.
assert (HEI : img_env VAL A_LIM E') by (subst E'; apply cm_env_img).
assert (ER : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E' k = YK11.getr regs4 r)
  by (intros kk r Hkk; subst E'; apply cm_env_reg; exact Hkk).
assert (F2 : ew E' 2 = YK11.getr regs4 2) by exact (ER 2%nat 2%bv eq_refl).
assert (F3 : ew E' 3 = YK11.getr regs4 3) by exact (ER 3%nat 3%bv eq_refl).
assert (F4 : ew E' 4 = YK11.getr regs4 4) by exact (ER 4%nat 4%bv eq_refl).
assert (F8 : ew E' 8 = YK11.getr regs4 8) by exact (ER 8%nat 8%bv eq_refl).
assert (F9 : ew E' 9 = YK11.getr regs4 9) by exact (ER 9%nat 9%bv eq_refl).
assert (F10 : ew E' 10 = w64 0) by (rewrite (ER 10%nat 10%bv eq_refl); exact Hv4).
assert (F18 : ew E' 18 = w64 (3 * j * ns)) by (rewrite (ER 18%nat 18%bv eq_refl); exact P18).
assert (F19 : ew E' 19 = w64 (3 * (j * ns + k))) by (rewrite (ER 19%nat 19%bv eq_refl); exact P19).
assert (F20 : ew E' 20 = w64 0) by (rewrite (ER 20%nat 20%bv eq_refl); exact P20).
assert (F21 : ew E' 21 = w64 (18446744073709551615 - out)) by (rewrite (ER 21%nat 21%bv eq_refl); exact P21).
assert (F22 : ew E' 22 = w64 (3 * j)) by (rewrite (ER 22%nat 22%bv eq_refl); exact P22).
assert (F23 : ew E' 23 = w64 (3 * nch)) by (rewrite (ER 23%nat 23%bv eq_refl); exact P23).
assert (F24 : ew E' 24 = w64 (ns - k)) by (rewrite (ER 24%nat 24%bv eq_refl); exact P24).
assert (F25 : ew E' 25 = w64 (18446744073709551615 - (res + 50))) by (rewrite (ER 25%nat 25%bv eq_refl); exact P25).
assert (F26 : ew E' 26 = w64 (3 * j + 3 * k * nch)) by (rewrite (ER 26%nat 26%bv eq_refl); exact P26).
assert (F27 : ew E' 27 = w64 j) by (rewrite (ER 27%nat 27%bv eq_refl); exact P27).
assert (F33 : ew E' 33 = w64 out) by (subst E'; apply cm_env_33).
assert (F34 : ew E' 34 = w64 res) by (subst E'; apply cm_env_34).
assert (F35 : ew E' 35 = w64 (dec_b_len (d_n cx))) by (subst E'; apply cm_env_35).
assert (F37 : ew E' 37 = w64 nch) by (subst E'; rewrite cm_env_37, Hn32; reflexivity).
assert (F45 : ew E' 45 = w64 (3 * ns)) by (subst E'; apply cm_env_45).
clear HE' ER.
clear E2 E3 E4 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 E33 E39.
paj_run_tok RUN HS HJ SHOK cm_Bspan; [cm_awr_ro|].
cm_memeq HF.
(* +0x808 `bnez s8`: another sample, or the next channel *)
psrr_branch_tok RUN BR HS SHOK cm_Bspan.
- (* k + 1 < ns: back to +0x7d4 *)
  cm_norm Hc. rewrite cm_bne in Hc. unfold w64 in Hc. cm_unlit Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK cm_Bspan 0x7d4; [cm_awr_ro|].
  cm_memeq HF. pmkst HS. rewrite Hmem. rewrite Hmem in HJ.
  lazymatch goal with |- context [mkCfg _ ?mdx] => set (md5 := mdx) end.
  lazymatch type of HS with context [restrict _ ?msf] =>
    assert (G2 : YK11.getr (ms_regs msf) 2 = YK11.getr regs4 2) by (cm_val HS);
    assert (G3 : YK11.getr (ms_regs msf) 3 = YK11.getr regs4 3) by (cm_val HS);
    assert (G4 : YK11.getr (ms_regs msf) 4 = YK11.getr regs4 4) by (cm_val HS);
    assert (G8 : YK11.getr (ms_regs msf) 8 = YK11.getr regs4 8) by (cm_val HS);
    assert (G9 : YK11.getr (ms_regs msf) 9 = YK11.getr regs4 9) by (cm_val HS);
    apply (IH (k + 1) (ms_regs msf) mem4 md5); [lia | lia | | exact HML4 |];
    [ exact (cm_core_regs B cx ly S W regs4 mem4 md4 dec_ev_6f0 (ms_regs msf) md5 HC4 HJ G2 G3 G4 G8 G9)
    | unfold cm_rL4, cm_rL3; repeat split; cm_val HS ]
  end.
- (* k + 1 = ns *)
  cm_norm Hc. rewrite cm_bne in Hc. unfold w64 in Hc. cm_unlit Hc.
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hks.
  paj_run_tok RUN HS HJ SHOK cm_Bspan; [cm_awr_ro|].
  cm_memeq HF.
  (* +0x820 `bne s11, nch`: another channel, or done *)
  psrr_branch_tok RUN BR HS SHOK cm_Bspan.
  + (* j + 1 < nch: back to +0x7c0 *)
    cm_norm Hc. rewrite cm_bne in Hc. unfold w64 in Hc. cm_unlit Hc.
    apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK cm_Bspan 0x7c0; [cm_awr_ro|].
    cm_memeq HF. pmkst HS. rewrite Hmem. rewrite Hmem in HJ.
    lazymatch goal with |- context [mkCfg _ ?mdx] => set (md5 := mdx) end.
    lazymatch type of HS with context [restrict _ ?msf] =>
      assert (G2 : YK11.getr (ms_regs msf) 2 = YK11.getr regs4 2) by (cm_val HS);
      assert (G3 : YK11.getr (ms_regs msf) 3 = YK11.getr regs4 3) by (cm_val HS);
      assert (G4 : YK11.getr (ms_regs msf) 4 = YK11.getr regs4 4) by (cm_val HS);
      assert (G8 : YK11.getr (ms_regs msf) 8 = YK11.getr regs4 8) by (cm_val HS);
      assert (G9 : YK11.getr (ms_regs msf) 9 = YK11.getr regs4 9) by (cm_val HS);
      apply (KL3 (ms_regs msf) mem4 md5); [lia | | exact HML4 |];
      [ exact (cm_core_regs B cx ly S W regs4 mem4 md4 dec_ev_6f0 (ms_regs msf) md5 HC4 HJ G2 G3 G4 G8 G9)
      | unfold cm_rL3; repeat split; cm_val HS ]
    end.
  + (* j + 1 = nch: every comparison found equal bytes *)
    clear Hc.
    paj_run_tok RUN HS HJ SHOK cm_Bspan; [cm_awr_ro|].
    cm_memeq HF.
    (* +0x82c `bnez s4` into the abort: s4 = 0 | (0 != 0) *)
    psrr_branch_tok RUN BR HS SHOK cm_Bspan.
    { exfalso. cm_norm Hc. vm_compute in Hc. discriminate Hc. }
    clear Hc.
    paj_run_tok RUN HS HJ SHOK cm_Bspan; [cm_awr_ro|].
    cm_memeq HF. pmkst HS. rewrite Hmem. rewrite Hmem in HJ.
    change (pa_sigma DB___interceptor_trampoline_free) with (decodeb_sigma DB___interceptor_trampoline_free).
    rewrite <- HPCF.
    lazymatch goal with |- context [mkCfg _ ?mdx] => set (md5 := mdx) end.
    lazymatch type of HS with context [restrict _ ?msf] =>
      assert (G2 : YK11.getr (ms_regs msf) 2 = YK11.getr regs4 2) by (cm_val HS);
      assert (G3 : YK11.getr (ms_regs msf) 3 = YK11.getr regs4 3) by (cm_val HS);
      assert (G4 : YK11.getr (ms_regs msf) 4 = YK11.getr regs4 4) by (cm_val HS);
      assert (G8 : YK11.getr (ms_regs msf) 8 = YK11.getr regs4 8) by (cm_val HS);
      assert (G9 : YK11.getr (ms_regs msf) 9 = YK11.getr regs4 9) by (cm_val HS);
      apply (KFREE (ms_regs msf) mem4 md5
               (cm_core_regs B cx ly S W regs4 mem4 md4 dec_ev_6f0 (ms_regs msf) md5 HC4 HJ G2 G3 G4 G8 G9) HM4);
      [cm_val HS | cm_ra HS; unfold w64; f_equal; vm_compute; reflexivity | cm_val HS | cm_val HS]
    end.
Qed.

Lemma cm_outer : forall (n : nat) j regs mem md,
  Z.to_nat (nch - j) = n -> 0 <= j < nch ->
  dec_b_core B cx ly S W regs mem md dec_ev_6f0 -> cm_memL mem -> cm_rL3 j regs ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 0x7c0)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros n. induction n as [|n IH]; intros j regs mem md Hn Hj HC HML HR; [lia|].
destruct cm_facts as (Hlen & Hnch0 & Hns0 & Hprod & Holen & Hbl & Hn32 & Hs32 & Hs64).
pose proof HML as (HM & H48 & HPO).
pose proof HR as (R18 & R20 & R21 & R22 & R23 & R25 & R27).
pose proof HC as (HJ & _).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ out _ HAR Hinout) as (_ & Ho4096 & Hoceil & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res _ HAR Hinres) as (_ & Hr4096 & Hrceil & _).
pose proof (req_size_pos (dec_b_olen nch ns) ltac:(lia)) as [_ Hrqo].
pose proof (req_size_pos (dec_b_len (d_n cx)) ltac:(lia)) as [_ Hrqr].
pose proof (@cm_stokL fx rc B cx W ly S regs mem md dec_ev_6f0 out res mode nch ns 0x7c0 HC HM H48
  ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
assert (EPC : w64 (DEC_A_LLVMF + 0x7c0) = Z_to_bv 64 (BASE + 0x7c0)) by (unfold w64; f_equal; vm_compute; reflexivity).
rewrite EPC in HS. clear EPC.
remember (cm_env cx regs out res (dec_b_len (d_n cx)) (ns mod 2 ^ 64) (nch mod 2 ^ 32) (ns mod 2 ^ 32) 0 (3 * ns))
  as E eqn:HE.
assert (SHOK : sh_ok SEGS cm_Bx [] E (mrestrict (w_H W) mem)) by constructor.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply cm_env_img).
assert (ER : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = YK11.getr regs r)
  by (intros kk r Hkk; subst E; apply cm_env_reg; exact Hkk).
assert (E2 : ew E 2 = YK11.getr regs 2) by exact (ER 2%nat 2%bv eq_refl).
assert (E3 : ew E 3 = YK11.getr regs 3) by exact (ER 3%nat 3%bv eq_refl).
assert (E4 : ew E 4 = YK11.getr regs 4) by exact (ER 4%nat 4%bv eq_refl).
assert (E8 : ew E 8 = YK11.getr regs 8) by exact (ER 8%nat 8%bv eq_refl).
assert (E9 : ew E 9 = YK11.getr regs 9) by exact (ER 9%nat 9%bv eq_refl).
assert (E18 : ew E 18 = w64 (3 * j * ns)) by (rewrite (ER 18%nat 18%bv eq_refl); exact R18).
assert (E20 : ew E 20 = w64 0) by (rewrite (ER 20%nat 20%bv eq_refl); exact R20).
assert (E21 : ew E 21 = w64 (18446744073709551615 - out)) by (rewrite (ER 21%nat 21%bv eq_refl); exact R21).
assert (E22 : ew E 22 = w64 (3 * j)) by (rewrite (ER 22%nat 22%bv eq_refl); exact R22).
assert (E23 : ew E 23 = w64 (3 * nch)) by (rewrite (ER 23%nat 23%bv eq_refl); exact R23).
assert (E25 : ew E 25 = w64 (18446744073709551615 - (res + 50))) by (rewrite (ER 25%nat 25%bv eq_refl); exact R25).
assert (E27 : ew E 27 = w64 j) by (rewrite (ER 27%nat 27%bv eq_refl); exact R27).
assert (E36 : ew E 36 = w64 ns) by (subst E; rewrite cm_env_36, Hs64; reflexivity).
assert (E38 : ew E 38 = w64 ns) by (subst E; rewrite cm_env_38, Hs32; reflexivity).
clear HE ER.
paj_run_tok RUN HS HJ SHOK cm_Bspan; [cm_awr_ro|].
cm_memeq HF.
(* +0x7d0 `blez ns`: refuted, ns > 0 *)
psrr_branch_tok RUN BR HS SHOK cm_Bspan.
{ exfalso. cm_norm Hc. unfold w64 in Hc. rewrite cm_bge in Hc by lia. apply negb_true_iff, Z.ltb_ge in Hc. lia. }
clear Hc.
paj_run_to_tok RUNTO HS HJ SHOK cm_Bspan 0x7d4; [cm_awr_ro|].
cm_memeq HF. pmkst HS. rewrite Hmem. rewrite Hmem in HJ.
lazymatch goal with |- context [mkCfg _ ?mdx] => set (md5 := mdx) end.
lazymatch type of HS with context [restrict _ ?msf] =>
  assert (G2 : YK11.getr (ms_regs msf) 2 = YK11.getr regs 2) by (cm_val HS);
  assert (G3 : YK11.getr (ms_regs msf) 3 = YK11.getr regs 3) by (cm_val HS);
  assert (G4 : YK11.getr (ms_regs msf) 4 = YK11.getr regs 4) by (cm_val HS);
  assert (G8 : YK11.getr (ms_regs msf) 8 = YK11.getr regs 8) by (cm_val HS);
  assert (G9 : YK11.getr (ms_regs msf) 9 = YK11.getr regs 9) by (cm_val HS);
  apply (cm_inner j Hj (fun regs' mem' md' Hj' HC' HML' HR' =>
           IH (j + 1) regs' mem' md' ltac:(lia) Hj' HC' HML' HR')
           (Z.to_nat ns) 0 (ms_regs msf) mem md5); [lia | lia | | exact HML |];
  [ exact (cm_core_regs B cx ly S W regs mem md dec_ev_6f0 (ms_regs msf) md5 HC HJ G2 G3 G4 G8 G9)
  | unfold cm_rL4, cm_rL3; repeat split; cm_val HS ]
end.
Qed.
End loop.
