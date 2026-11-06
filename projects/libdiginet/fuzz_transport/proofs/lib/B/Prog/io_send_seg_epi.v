(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/B/Prog/LLVMFuzzerTestOneInput_segD.v, with its module paths, module names and numbers changed; 221 of its 258 lines of code are new or changed and 1995 lines of the source are left out. *)
(* io_send_seg_epi: the epilogue segment of the image-B walk of io_send (fuzz_transport.asan-ubsan 41113a03c82f,
   entry 0x82ffc = TImgB.v ti_io_send timg_B; the statement is lib/B/Prog/io_send_cg.v), from the cut IOS_EPI
   (lib/B/Prog/io_send_seg_cut.v, 0x83310 = IOS_AT 0x314) to the return. It proves io_send_seg_cut.v ios_epi_stmt.

   The code (listing slots IOS_AT 0x314 .. IOS_AT 0x348 of lib/B/Prog/DgnTransportBList.v):
     0x83310 - 0x83318  slli s3, s3, 63; srai a0, s3, 63; andi a0, a0, -5: a0 = -5 when bit 0 of s3 is set, else 0
                        (fuzz_transport.c:898);
     0x8331c - 0x8333c  ld ra, 152(sp) .. ld s7, 88(sp): the nine words the prologue saved (io_send_seg_cut.v
                        IOS_SAVED);
     0x83340 - 0x83344  addi sp, sp, 160; ret.
   No store, no call, no instrumented check, no branch to the trap word.

   The walk of the stretch is ONE run (lib/B/Prog/TransportGRunB.v paj_run_x, shadow entry SH = []) from the
   symbolic state ie_ss, whose only region is the nine saved words of io_send's frame, read-only (ie_entry). ios_epi
   closes the walk's post ios_post at the return: the journal of the cut, the callee-saved registers (ra and s0 .. s7
   reloaded from the frame, sp the entry sp again, gp, tp and s8 .. s11 as the cut holds them), the cut's kept fact
   and world relation (the run writes nothing: ie_frame_all), and a0 = ios_ret Bw (lib/A/Prog/io_send_segs.v): s3 is
   the byte of g_fail_next the entry read, 0 or 1 under ios_fix's g_fail_next Bw <= 1 (ie_ret_bits). The port of
   image A's lib/A/Prog/io_send_seg_epi.v (same code shape) at image B's listing and names. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg io_send_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TWorldLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.

(* ------------------------------------------------------------------ *)
(* a0                                                                  *)
(* ------------------------------------------------------------------ *)

(* `slli 63; srai 63; andi -5` of the byte f, 0 or 1: -EIO when f is set, else 0 (:898). *)
Lemma ie_ret_bits : forall f, 0 <= f <= 1 ->
  alu64 ALU_AND (alu64 ALU_SRA (alu64 ALU_SLL (w64 f) (Z_to_bv 64 63)) (Z_to_bv 64 63)) (Z_to_bv 64 (-5)) =
  w64 (if TC.truth f then - TC.EIO else 0).
Proof. intros f Hf. assert (H : f = 0 \/ f = 1) by lia. destruct H as [-> | ->]; apply bv_eq; vm_compute; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The symbolic state at the cut                                       *)
(* ------------------------------------------------------------------ *)

(* Atoms: 0 .. 31 the registers at the cut (regs2), 32 the shadow base, 33 .. 41 the nine saved words as the entry
   registers held them (ra, s0, s1, s2, s3, s4, s5, s6, s7). The one region: the frame bytes [sp + 88, sp + 160) of
   the saved words, read-only (no window), one 8-byte chunk per word at sp + 160 - d for IOS_SAVED's (d, r). *)
Definition ie_region : YP09.region :=
  YP09.mkRegion (Some 2%nat) 88 160 0 0
    [YP09.mkChunk 152 (CVal 8 (SOff 33 0)); YP09.mkChunk 144 (CVal 8 (SOff 34 0));
     YP09.mkChunk 136 (CVal 8 (SOff 35 0)); YP09.mkChunk 128 (CVal 8 (SOff 36 0));
     YP09.mkChunk 120 (CVal 8 (SOff 37 0)); YP09.mkChunk 112 (CVal 8 (SOff 38 0));
     YP09.mkChunk 104 (CVal 8 (SOff 39 0)); YP09.mkChunk 96 (CVal 8 (SOff 40 0));
     YP09.mkChunk 88 (CVal 8 (SOff 41 0))].
Definition ie_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ie_ss : sstate := mkSS IOS_EPI sr_atoms [ie_region] None ie_facts.
(* No instrumented check on the stretch: no shadow entry. *)
Definition IE_SH : list shent := [].
Definition IE_Bx : sv := SOff 32 0.

(* The run's valuation: the registers at the cut, the shadow base, the nine saved words. *)
Definition ie_extra (regs : bvmap 5 word) : list word :=
  [w64 SHADOW_OFF; YK11.getr regs (Z_to_bv 5 1); YK11.getr regs (Z_to_bv 5 8); YK11.getr regs (Z_to_bv 5 9);
   YK11.getr regs (Z_to_bv 5 18); YK11.getr regs (Z_to_bv 5 19); YK11.getr regs (Z_to_bv 5 20);
   YK11.getr regs (Z_to_bv 5 21); YK11.getr regs (Z_to_bv 5 22); YK11.getr regs (Z_to_bv 5 23)].

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac ie_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "ie_reg: no match for" T; fail
  end.

(* A reloaded word: the atom n's value, given by Ek : ew E n = w. *)
Ltac ie_saved Ek := cbn [sv_denot]; rewrite Ek, Z.add_0_r; apply Z_to_bv_bv_unsigned.

(* A run from ie_ss writes nothing: its frame keeps every byte. *)
Lemma ie_frame_all : forall E (m m' : word -> option byte),
  frame_of E (ss_mem ie_ss) m m' -> forall x, m' x = m x.
Proof.
intros E m m' HF x. unfold frame_of in HF. apply HF.
intros (r & Hin & Hr). destruct Hin as [<- | []].
unfold ie_region in Hr. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr. lia.
Qed.

Section epi. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Definition ie_E (regs2 regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs2 (ie_extra regs)).

(* One saved word: the 8 bytes at a = base + off read as the word w the atom n holds. *)
Lemma ie_chunk : forall (E : env) (H : word -> bool) (mem : word -> option byte) (base off a : Z) (n : nat)
    (w : word),
  ew E n = w -> base + off = a -> rdword (aview segs H mem) a = Some (bv_unsigned w) ->
  YP09.chunk_ok segs E (mrestrict H mem) base (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
intros E H mem base off a n w Hn Ha Hr.
apply (chunk_ok_val segs E (mrestrict H mem) base off 8 (SOff n 0) (bv_unsigned w)).
- cbn [sv_denot]. rewrite Hn, Z.add_0_r. reflexivity.
- pose proof (bv_unsigned_in_range 64 w) as R. change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in R. exact R.
- cbn. lia.
- rewrite Ha. exact (val_mem_of_rdword segs H mem a (bv_unsigned w) Hr).
Qed.

(* The state at the cut: sp is the entry sp less IOSEND_FRAME, and the nine saved words are in the frame. *)
Lemma ie_entry : forall (W2 : world segs) (regs regs2 : bvmap 5 word) (mem2 : word -> option byte),
  YK11.getr regs2 2 = w64 (spZ regs - IOSEND_FRAME) ->
  2 ^ 46 <= spZ regs - IOSEND_FRAME <= 2 ^ 47 -> (spZ regs - IOSEND_FRAME) mod 16 = 0 ->
  ios_saved W2 mem2 regs ->
  st_ok_pi segs VAL (ie_E regs2 regs) ie_ss
    (restrict (w_H W2) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + IOS_EPI)) mem2 (YK11.seg_rom segs)))
  /\ sh_ok segs IE_Bx IE_SH (ie_E regs2 regs) (mrestrict (w_H W2) mem2).
Proof.
intros W2 regs regs2 mem2 Hsp Hr H16 HSV.
assert (FR : IOSEND_FRAME = 160) by reflexivity.
set (E := ie_E regs2 regs).
assert (E2 : ew E 2 = w64 (spZ regs - IOSEND_FRAME)).
{ unfold E, ie_E. refine (eq_trans (ew_Eimg_Ereg_nat regs2 (ie_extra regs) 2 2%bv eq_refl) _). exact Hsp. }
assert (Usp : bv_unsigned (ew E 2) = spZ regs - IOSEND_FRAME) by (rewrite E2; apply unsigned_lit_small; lia).
assert (EX : forall j, (j < 10)%nat -> ew E (32 + j) = nth j (ie_extra regs) (Z_to_bv 64 0)).
{ intros j Hj. unfold E, ie_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs2 _ j). }
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by exact (EX 0%nat ltac:(lia)).
unfold ios_saved, IOS_SAVED in HSV.
pose proof (Forall_inv HSV) as S1. apply Forall_inv_tail in HSV.
pose proof (Forall_inv HSV) as S2. apply Forall_inv_tail in HSV.
pose proof (Forall_inv HSV) as S3. apply Forall_inv_tail in HSV.
pose proof (Forall_inv HSV) as S4. apply Forall_inv_tail in HSV.
pose proof (Forall_inv HSV) as S5. apply Forall_inv_tail in HSV.
pose proof (Forall_inv HSV) as S6. apply Forall_inv_tail in HSV.
pose proof (Forall_inv HSV) as S7. apply Forall_inv_tail in HSV.
pose proof (Forall_inv HSV) as S8. apply Forall_inv_tail in HSV.
pose proof (Forall_inv HSV) as S9. clear HSV.
cbn [fst snd] in S1, S2, S3, S4, S5, S6, S7, S8, S9.
split.
- rewrite restrict_mkst_fx. unfold ie_ss.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil].
    unfold ie_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. rewrite FR in *.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [apply (ie_chunk E _ _ _ 152 (spZ regs - 8) 33 _ (EX 1%nat ltac:(lia))); [lia | exact S1]|].
    apply Forall_cons; [apply (ie_chunk E _ _ _ 144 (spZ regs - 16) 34 _ (EX 2%nat ltac:(lia))); [lia | exact S2]|].
    apply Forall_cons; [apply (ie_chunk E _ _ _ 136 (spZ regs - 24) 35 _ (EX 3%nat ltac:(lia))); [lia | exact S3]|].
    apply Forall_cons; [apply (ie_chunk E _ _ _ 128 (spZ regs - 32) 36 _ (EX 4%nat ltac:(lia))); [lia | exact S4]|].
    apply Forall_cons; [apply (ie_chunk E _ _ _ 120 (spZ regs - 40) 37 _ (EX 5%nat ltac:(lia))); [lia | exact S5]|].
    apply Forall_cons; [apply (ie_chunk E _ _ _ 112 (spZ regs - 48) 38 _ (EX 6%nat ltac:(lia))); [lia | exact S6]|].
    apply Forall_cons; [apply (ie_chunk E _ _ _ 104 (spZ regs - 56) 39 _ (EX 7%nat ltac:(lia))); [lia | exact S7]|].
    apply Forall_cons; [apply (ie_chunk E _ _ _ 96 (spZ regs - 64) 40 _ (EX 8%nat ltac:(lia))); [lia | exact S8]|].
    apply Forall_cons; [apply (ie_chunk E _ _ _ 88 (spZ regs - 72) 41 _ (EX 9%nat ltac:(lia))); [lia | exact S9]|].
    apply Forall_nil.
  + split; exact I.
  + unfold ie_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [exact H16 | lia].
- unfold sh_ok, IE_SH. apply Forall_nil.
Qed.

(* ------------------------------------------------------------------ *)
(* The epilogue                                                        *)
(* ------------------------------------------------------------------ *)

(* From the cut IOS_EPI to the return: the walk's post at the model's world Bw' and result ios_ret Bw. The
   registers the stretch reads: sp (the entry sp less IOSEND_FRAME), s3 (the byte of g_fail_next the entry read),
   and the nine saved words (ios_saved); gp, tp and s8 .. s11 are what the cut holds and the return gives back. *)
Lemma ios_epi : @ios_epi_stmt fx rc B MT.
Proof.
unfold ios_epi_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw Bw' ly2 S2 W2 mem2 md2 regs2
  HLAWS HFIX HCUR HSV Hsp Hgp Htp Hs3 H811 HTW.
destruct HLAWS as (_ & _ & _ & _ & LAWS & _ & HGX & _).
destruct HFIX as (HJc & Hra & _ & _ & _ & _ & _ & Hsp16 & Hlo & Hhi & _ & _ & _ & _ & _ & Hfail & _).
destruct HCUR as (HJ & Hfrm & Hperm & Hmo & HK).
pose proof HJc as (_ & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS HJc.
pose proof asan_consts as (C1 & _).
assert (FR : IOSEND_FRAME = 160) by reflexivity.
assert (IS : 160 <= IOSEND_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Hsp2 : 2 ^ 46 <= spZ regs - IOSEND_FRAME <= 2 ^ 47) by (rewrite FR; lia).
assert (Hsp16' : (spZ regs - IOSEND_FRAME) mod 16 = 0).
{ rewrite FR. replace (spZ regs - 160) with (spZ regs + (-10) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16. }
(* the byte of g_fail_next: 0 or 1 *)
pose proof (TWL.u_at_range Bw TW.OFF_g_fail_next 1) as Rf.
change (TW.u_at Bw TW.OFF_g_fail_next 1) with (TW.g_fail_next Bw) in Rf.
assert (HF01 : 0 <= TW.g_fail_next Bw <= 1) by lia.
(* the valuation *)
destruct (ie_entry W2 regs regs2 mem2 Hsp Hsp2 Hsp16' HSV) as [HS SHOK].
set (E0 := ie_E regs2 regs) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, ie_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs2 r)
  by (intros n r Hn; unfold E0, ie_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 10)%nat -> ew E0 (32 + j) = nth j (ie_extra regs) (Z_to_bv 64 0)).
{ intros j Hj. unfold E0, ie_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs2 _ j). }
assert (Usp : bv_unsigned (ew E0 2) = spZ regs - IOSEND_FRAME).
{ rewrite (EE 2%nat 2%bv eq_refl). rewrite Hsp. apply unsigned_lit_small. lia. }
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
pose proof (paj_ret_at (fx := fx) (PL := PL_transportb) (PI := PI_transportb)) as RET.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + IOS_EPI)) mem2 (YK11.seg_rom segs)) md2) Q) end.
(* the run, +0x314 .. +0x348: a0, the nine reloads, sp + 160; it stops at `ret` *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ intros a (r & Hin & Hr). destruct Hin as [<- | []].
  unfold ie_region in Hr. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr. lia. }
set (mdF := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody mdF. clear mat.
rename ms into msF.
(* the run wrote nothing *)
assert (HM : forall x, ms_mem msF x = mem2 x) by exact (ie_frame_all _ _ _ HF).
assert (HMr : forall x, mrestrict (w_H W2) (ms_mem msF) x = mrestrict (w_H W2) mem2 x)
  by exact (ie_frame_all _ _ _ HFr).
clear HF HFr HG.
(* the registers at the return *)
assert (E19 : ew E0 19 = w64 (TW.g_fail_next Bw)) by (refine (eq_trans (EE 19%nat 19%bv eq_refl) _); exact Hs3).
assert (E33 : ew E0 33 = YK11.getr regs 1) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E0 34 = YK11.getr regs (Z_to_bv 5 8)) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E0 35 = YK11.getr regs (Z_to_bv 5 9)) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew E0 36 = YK11.getr regs (Z_to_bv 5 18)) by exact (EX 4%nat ltac:(lia)).
assert (E37 : ew E0 37 = YK11.getr regs (Z_to_bv 5 19)) by exact (EX 5%nat ltac:(lia)).
assert (E38 : ew E0 38 = YK11.getr regs (Z_to_bv 5 20)) by exact (EX 6%nat ltac:(lia)).
assert (E39 : ew E0 39 = YK11.getr regs (Z_to_bv 5 21)) by exact (EX 7%nat ltac:(lia)).
assert (E40 : ew E0 40 = YK11.getr regs (Z_to_bv 5 22)) by exact (EX 8%nat ltac:(lia)).
assert (E41 : ew E0 41 = YK11.getr regs (Z_to_bv 5 23)) by exact (EX 9%nat ltac:(lia)).
ie_reg HS (10%bv : bv 5) (w64 (ios_ret Bw)) RA0
  ltac:(cbn [sv_denot]; rewrite E19, Z.add_0_r, Z_to_bv_bv_unsigned; exact (ie_ret_bits _ HF01)).
ie_reg HS (1%bv : bv 5) (YK11.getr regs 1) R1 ltac:(ie_saved E33).
ie_reg HS (2%bv : bv 5) (YK11.getr regs (Z_to_bv 5 2)) R2
  ltac:(cbn [sv_denot]; rewrite Usp, FR; replace (spZ regs - 160 + 160) with (spZ regs) by lia;
        apply Z_to_bv_bv_unsigned).
ie_reg HS (3%bv : bv 5) (YK11.getr regs (Z_to_bv 5 3)) R3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
ie_reg HS (4%bv : bv 5) (YK11.getr regs (Z_to_bv 5 4)) R4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
ie_reg HS (8%bv : bv 5) (YK11.getr regs (Z_to_bv 5 8)) R8 ltac:(ie_saved E34).
ie_reg HS (9%bv : bv 5) (YK11.getr regs (Z_to_bv 5 9)) R9 ltac:(ie_saved E35).
ie_reg HS (18%bv : bv 5) (YK11.getr regs (Z_to_bv 5 18)) R18 ltac:(ie_saved E36).
ie_reg HS (19%bv : bv 5) (YK11.getr regs (Z_to_bv 5 19)) R19 ltac:(ie_saved E37).
ie_reg HS (20%bv : bv 5) (YK11.getr regs (Z_to_bv 5 20)) R20 ltac:(ie_saved E38).
ie_reg HS (21%bv : bv 5) (YK11.getr regs (Z_to_bv 5 21)) R21 ltac:(ie_saved E39).
ie_reg HS (22%bv : bv 5) (YK11.getr regs (Z_to_bv 5 22)) R22 ltac:(ie_saved E40).
ie_reg HS (23%bv : bv 5) (YK11.getr regs (Z_to_bv 5 23)) R23 ltac:(ie_saved E41).
ie_reg HS (24%bv : bv 5) (YK11.getr regs (Z_to_bv 5 24)) R24
  ltac:(cbn [sv_denot]; rewrite (EE 24%nat 24%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (H811 24 ltac:(lia))).
ie_reg HS (25%bv : bv 5) (YK11.getr regs (Z_to_bv 5 25)) R25
  ltac:(cbn [sv_denot]; rewrite (EE 25%nat 25%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (H811 25 ltac:(lia))).
ie_reg HS (26%bv : bv 5) (YK11.getr regs (Z_to_bv 5 26)) R26
  ltac:(cbn [sv_denot]; rewrite (EE 26%nat 26%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (H811 26 ltac:(lia))).
ie_reg HS (27%bv : bv 5) (YK11.getr regs (Z_to_bv 5 27)) R27
  ltac:(cbn [sv_denot]; rewrite (EE 27%nat 27%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (H811 27 ltac:(lia))).
assert (HPF : aregs_preserved regs (ms_regs msF)).
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
    [exact R2 | exact R3 | exact R4 | exact R8 | exact R9 | exact R18 | exact R19 | exact R20 | exact R21
    | exact R22 | exact R23 | exact R24 | exact R25 | exact R26 | exact R27]. }
(* the return *)
eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
unfold ios_post, transport_io_send_post, transport_cg_post.
exists ly2, S2, (ms_regs msF), (ms_mem msF), (with_vm_backing (m_vm_lazy mdF) mat' mdF), 0.
split.
{ rewrite R1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split; [unfold IOSEND_EV; lia|].
split; [apply (ajournal_gx_materialize segs B LAWS transportb_segs_low); exact HJ|].
split; [exact HPF|].
split; [exact Hfrm|].
split; [exact Hperm|].
split; [exact (acall_kept_g_mem_ext segs B TG.G_HARNESS_B lyc Sc W memc W2 mem2 (ms_mem msF) _ _ _ HM HK)|].
split; [exact Hmo|].
split; [exact RA0|].
apply (tw_kept TMAP_B (aview segs (w_H W2) mem2) (aview segs (w_H W2) (ms_mem msF)) Bw' HTW).
intros x _. unfold aview, mbyte. rewrite HMr. reflexivity.
Qed.

End epi.
