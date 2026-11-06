(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the kit of segment F of LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, 0x86974 .. 0x8699c: the three frees of the words blocks and the latch), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACbk.v (wcb_entry: the symbolic seed of a point of the function) and A/ACh2.v:122-290 (the step through a call and back, with the facts carried over it). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/LLVMFuzzerTestOneInput_s70.v, with its module paths changed; 855 of its 936 lines of code are new or changed and 347 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_s24k.v; 598 of its 666 lines of code are new or changed and 868 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): file group _s24, the segments S16 ..
   S20 of the test harness's entry function LLVMFuzzerTestOneInput (0x84d34), cuts K85bd0 -> K85c1c -> K85c24 ->
   K85c2c -> K85c34 -> K85c44:
   - S16 0x85bd0 .. 0x85c18: reac_segconf_declared(c, tab, cap, &n), check_declared(got, want, tab, n, mt, mn, cap),
     free(mt);
   - S17 0x85c1c .. 0x85c20: free(tab); S18 0x85c24 .. 0x85c28: free(m); S19 0x85c2c .. 0x85c30: free(c);
   - S20 0x85c34 .. 0x85c40: n out of scope (its shadow byte SH(FR) + 32 := 0xf8), a6 / a7 := 24(s1) / 8(s1).
   Each lemma proves its statement lt_seg_S<k>_stmt of LLVMFuzzerTestOneInput_defs.v exactly; the callee contracts
   and the free wrapper's rule are Section hypotheses at every FP state, as fuzz_command's walk files take them. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaNoChain PaDenot PaSB
  PaLibF PaLibG.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c SegInstA
  LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
  reac_declared_vlan_add_c reac_segconf_declared_c check_declared_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_s10k
  LLVMFuzzerTestOneInput_s24k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.

(* S16's two runs: 0x85bd0 .. the jal of reac_segconf_declared, reading 32(s1) cap, 48(s1) &n, 160(s1) c (atoms 32,
   33, 34); 0x85bf4 .. the jal of check_declared, reading n = lw 0(s6) (atom 32, at most 39, so its sign extension is
   itself), 104(s1) want, 112(s1) mt, 120(s1) mn (atoms 33, 34, 35). No region has a write window. *)
Definition s24_rA : YP09.region := YP09.mkRegion (Some 9%nat) 32 168 0 0
  [YP09.mkChunk 32 (CVal 8 (SOff 32 0)); YP09.mkChunk 48 (CVal 8 (SOff 33 0)); YP09.mkChunk 160 (CVal 8 (SOff 34 0))].
Definition s24_ssA : sstate := mkSS LO_K85bd0 sr_atoms [s24_rA] None (mkFacts [] [] []).
Definition LO_S16C : Z := 0xec0.
Definition s24_rC1 : YP09.region := YP09.mkRegion (Some 22%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))].
Definition s24_rC2 : YP09.region := YP09.mkRegion (Some 9%nat) 104 128 0 0
  [YP09.mkChunk 104 (CVal 8 (SOff 33 0)); YP09.mkChunk 112 (CVal 8 (SOff 34 0)); YP09.mkChunk 120 (CVal 8 (SOff 35 0))].
Definition s24_ssC : sstate := mkSS LO_S16C sr_atoms [s24_rC1; s24_rC2] None (mkFacts [(32%nat, mkAF 0 39 0)] [] []).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the walk's hypotheses: the listing's trampolines (PALib), the two image facts of _s10's bundle and the
   record's symbols (AR's stack-protector cells), the call targets of the program functions, the meter's laws *)
Hypothesis TL : PALib B.
Hypothesis IMGS : s10_img.
Hypothesis BSYM : AF0m.SegBSyms B.
Hypothesis SIGP : seg_sig_prog.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
(* the free wrapper's rule and the two callees' contracts, at every FP state *)
Hypothesis AFREE4 : forall fx0 : YK11.FPState, afree04_rule (fx := fx0) SEGS B MT.
Hypothesis HDECL : forall fx0 : YK11.FPState, reac_segconf_declared_contract (fx := fx0) SEGS B
  (BASE + AF_reac_segconf_declared) STK_reac_segconf_declared RLO_A RHI_A gotwA guardA.
Hypothesis HCHKD : forall fx0 : YK11.FPState, check_declared_contract (fx := fx0) SEGS B
  (BASE + AF_check_declared) STK_check_declared RLO_A RHI_A.

Ltac s24_reg P n R := exact (eq_trans (P n ltac:(unfold acallee_saved; lia)) R).

(* ============================== S17 0x85c1c .. 0x85c20: free(tab) ============================== *)
Lemma lt_seg_S17 : lt_seg_S17_stmt B MT.
Proof.
intros K24 cx ly S W regs mem md k acc c m tab HBASE HFRM HCORE Hc Hm Htab R18 R19 R21 R24 HSL.
pose proof HCORE as (HFR & HIMG & HBL & HBUD).
pose proof HFR as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & _).
pose proof (proj1 HJ) as HAR.
destruct (s24_blk_head B cx ly S W mem md tab (x_tabn cx) _ HAR HBL) as (Hin & Hnb0 & _).
destruct (s24_bud_free B MT MTL cx ly S W mem md k acc 3 HBASE HJ HBUD ltac:(lia)) as (Hnev & MOK & HBUD').
apply (s24_free B MT (AFREE4 fx) TL cx ly S W regs mem md k tab (x_tabn cx) 0xee8 24%bv _ HBASE
  (or_intror (or_introl (conj eq_refl eq_refl))) HJ R2 R3 R4 R8 HSV R24 Hin Hnb0 Hnev MOK).
intros ly2 S2 W2 regs2 mem2 md2 HJ2 HP2 Hbl Hfr2 HK MLE.
pose proof (proj1 HJ2) as HAR2.
assert (HBL2 : lt_blocks B cx ly2 S2 [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)])
  by exact (s24_perm_free _ _ _ _ _ HBL Hbl).
pose proof (HBUD' S2 MLE) as HBUD2.
assert (HC2 : lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_free MT) (3 - 1) LFO_N
  [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)]) by (eapply s24_core_step; eassumption).
assert (P : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) by exact HP2.
exact (K24 fx cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_free MT) c m HBASE HFRM HC2
  (s24_hblk B ly2 S2 W2 mem2 md2 c _ HAR2 (s24_blk_in B cx ly2 S2 _ _ HBL2 ltac:(right; left; reflexivity)))
  (s24_hblk B ly2 S2 W2 mem2 md2 m _ HAR2 (s24_blk_in B cx ly2 S2 _ _ HBL2 ltac:(left; reflexivity)))
  ltac:(s24_reg P 18 R18) ltac:(s24_reg P 19 R19) ltac:(s24_reg P 21 R21)
  (s24_slots_kept B MT cx W W2 mem mem2 _ HBASE HSL
    ltac:(intros o v Hov; cbn [In] in Hov; destruct Hov as [Hov | [Hov | []]]; injection Hov as <- <-; lia) HK)).
Qed.

(* ============================== S18 0x85c24 .. 0x85c28: free(m) ============================== *)
Lemma lt_seg_S18 : lt_seg_S18_stmt B MT.
Proof.
intros K2c cx ly S W regs mem md k acc c m HBASE HFRM HCORE Hc Hm R18 R19 R21 HSL.
pose proof HCORE as (HFR & HIMG & HBL & HBUD).
pose proof HFR as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & _).
pose proof (proj1 HJ) as HAR.
destruct (s24_blk_head B cx ly S W mem md m seg_spec.SEG_M_SIZE _ HAR HBL) as (Hin & Hnb0 & _).
destruct (s24_bud_free B MT MTL cx ly S W mem md k acc 2 HBASE HJ HBUD ltac:(lia)) as (Hnev & MOK & HBUD').
apply (s24_free B MT (AFREE4 fx) TL cx ly S W regs mem md k m seg_spec.SEG_M_SIZE 0xef0 19%bv _ HBASE
  (or_intror (or_intror (or_introl (conj eq_refl eq_refl)))) HJ R2 R3 R4 R8 HSV R19 Hin Hnb0 Hnev MOK).
intros ly2 S2 W2 regs2 mem2 md2 HJ2 HP2 Hbl Hfr2 HK MLE.
pose proof (proj1 HJ2) as HAR2.
assert (HBL2 : lt_blocks B cx ly2 S2 [(c, seg_spec.SEG_C_SIZE)]) by exact (s24_perm_free _ _ _ _ _ HBL Hbl).
pose proof (HBUD' S2 MLE) as HBUD2.
assert (HC2 : lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_free MT) (2 - 1) LFO_N
  [(c, seg_spec.SEG_C_SIZE)]) by (eapply s24_core_step; eassumption).
assert (P : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) by exact HP2.
exact (K2c fx cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_free MT) c HBASE HFRM HC2
  (s24_hblk B ly2 S2 W2 mem2 md2 c _ HAR2 (s24_blk_in B cx ly2 S2 _ _ HBL2 ltac:(left; reflexivity)))
  ltac:(s24_reg P 18 R18) ltac:(s24_reg P 21 R21)
  (s24_slots_kept B MT cx W W2 mem mem2 _ HBASE HSL
    ltac:(intros o v Hov; cbn [In] in Hov; destruct Hov as [Hov | [Hov | []]]; injection Hov as <- <-; lia) HK)).
Qed.

(* ============================== S19 0x85c2c .. 0x85c30: free(c) ============================== *)
Lemma lt_seg_S19 : lt_seg_S19_stmt B MT.
Proof.
intros K34 cx ly S W regs mem md k acc c HBASE HFRM HCORE Hc R18 R21 HSL.
pose proof HCORE as (HFR & HIMG & HBL & HBUD).
pose proof HFR as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & _).
pose proof (proj1 HJ) as HAR.
destruct (s24_blk_head B cx ly S W mem md c seg_spec.SEG_C_SIZE _ HAR HBL) as (Hin & Hnb0 & _).
destruct (s24_bud_free B MT MTL cx ly S W mem md k acc 1 HBASE HJ HBUD ltac:(lia)) as (Hnev & MOK & HBUD').
apply (s24_free B MT (AFREE4 fx) TL cx ly S W regs mem md k c seg_spec.SEG_C_SIZE 0xef8 18%bv _ HBASE
  (or_intror (or_intror (or_intror (conj eq_refl eq_refl)))) HJ R2 R3 R4 R8 HSV R18 Hin Hnb0 Hnev MOK).
intros ly2 S2 W2 regs2 mem2 md2 HJ2 HP2 Hbl Hfr2 HK MLE.
assert (HBL2 : lt_blocks B cx ly2 S2 []) by exact (s24_perm_free _ _ _ _ _ HBL Hbl).
pose proof (HBUD' S2 MLE) as HBUD2.
assert (HC2 : lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_free MT) (1 - 1) LFO_N [])
  by (eapply s24_core_step; eassumption).
assert (P : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) by exact HP2.
exact (K34 fx cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_free MT) HBASE HFRM HC2 ltac:(s24_reg P 21 R21)
  (s24_slots_kept B MT cx W W2 mem mem2 _ HBASE HSL
    ltac:(intros o v Hov; cbn [In] in Hov; destruct Hov as [Hov | [Hov | []]]; injection Hov as <- <-; lia) HK)).
Qed.


(* ============================== S16 0x85bd0 .. 0x85c18 ============================== *)
Lemma lt_seg_S16 : lt_seg_S16_stmt B MT.
Proof.
intros K1c cx ly S W regs mem md k acc c m tab mt HBASE HFRM HCORE Hhc Hhm Hht Hhmt R16 R21 R24 HSL HCM HTABS.
pose proof (paj_run B LAWS) as RUN.
pose proof HCORE as (HFR & HIMG & HBL & HBUD).
pose proof HFR as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & _).
pose proof (proj1 HJ) as HAR.
pose proof (s24_nums B MT cx HBASE) as (Hal16 & Hs1al & Hs1 & Hceil & H47 & Htop & Htop2).
pose proof HBASE as (HPRE0 & _).
pose proof HPRE0 as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBok. pose proof pa_base_lo as HBLO.
destruct (s24_frame_at B cx ly S W mem md k HJ) as (Hin3 & EFA & HF4 & HFc & HFapp & HF32 & HFp & HFsp).
destruct (s24_low B MT cx ly S W mem md k HBASE HJ) as (L1 & L2 & L3).
destruct (s24_blk_two B cx ly S W mem md _ _ _ HAR HBL) as (Hmt_tab & Hmt0 & Htab0).
pose proof Hhmt as (HinMT & HmtF & HmtA & _). pose proof Hht as (HinT & HtF & HtA & _).
pose proof Hhc as (HinC & HcF & HcA & _).
pose proof (al_blocks _ _ LAWS ly S W mem md tab _ HAR HinT) as (_ & _ & HtC & _).
pose proof (al_blocks _ _ LAWS ly S W mem md mt _ HAR HinMT) as (_ & _ & HmtC & _).
pose proof (al_blocks _ _ LAWS ly S W mem md c _ HAR HinC) as (_ & _ & HcC & _).
pose proof HTABS as (Hcap & _ & _ & _ & _ & HmnLe).
assert (Hreqt : req_size (x_tabn cx) = x_tabn cx) by (apply s24n_req; unfold x_tabn, seg_spec.RVLAN_SIZE; lia).
assert (Hreqm : req_size (x_mtn cx) = x_mtn cx) by (apply s24n_req; unfold x_mtn, seg_spec.MVLAN_SIZE; lia).
rewrite Hreqt in HtC. rewrite Hreqm in HmtC.
assert (Hc64 : 0 <= c < 2 ^ 64)
  by (pose proof (req_size_pos seg_spec.SEG_C_SIZE ltac:(unfold seg_spec.SEG_C_SIZE; lia)); lia).
(* the model: the reader's answer and table (gd) against the model's (wd) *)
set (gd := SegModel.r_declared (seg_spec.seg_rc (x_run cx)) (x_tab0 cx) (x_cap cx)) in *.
set (wd := SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx)) in *.
destruct (s24_vlans_parts gd wd (x_cap cx) (s24_vlans (x_pl cx))) as (Hgw & Hlt1).
assert (Hmc32 : (length (SegModel.mc_seg (x_mcF cx)) <= 32)%nat).
{ destruct HCM as [_ Hm]. unfold sa_mconf, sa_mconfp in Hm. destruct Hm as (bs & _ & Henc).
  unfold seg_spec.mconf_encp in Henc. destruct Henc as (_ & Hle & _). exact Hle. }
(* the slots the two runs read *)
assert (S32 : rdword (rdW W mem) (x_s1 cx + 32) = Some (x_cap cx))
  by (apply HSL; cbn [In]; repeat (first [left; reflexivity | right])).
assert (S48 : rdword (rdW W mem) (x_s1 cx + 48) = Some (x_fr cx + FO_N))
  by (apply HSL; cbn [In]; repeat (first [left; reflexivity | right])).
assert (S104 : rdword (rdW W mem) (x_s1 cx + 104) = Some (fst wd mod 2 ^ 64))
  by (apply HSL; cbn [In]; repeat (first [left; reflexivity | right])).
assert (S112 : rdword (rdW W mem) (x_s1 cx + 112) = Some mt)
  by (apply HSL; cbn [In]; repeat (first [left; reflexivity | right])).
assert (S120 : rdword (rdW W mem) (x_s1 cx + 120) = Some (Z.of_nat (length (snd wd))))
  by (apply HSL; cbn [In]; repeat (first [left; reflexivity | right])).
assert (S160 : rdword (rdW W mem) (x_s1 cx + 160) = Some c)
  by (apply HSL; cbn [In]; repeat (first [left; reflexivity | right])).
pose proof (Z.mod_pos_bound (fst wd) (2 ^ 64) ltac:(lia)) as Hwm.
(* ---- 0x85bd0 .. 0x85bec, the jal of reac_segconf_declared ---- *)
set (EA := Eimg (Ereg regs [w64 (x_cap cx); w64 (x_fr cx + FO_N); w64 c])).
assert (EAr : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew EA n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst EA. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EAx : forall j, (j < 3)%nat ->
  ew EA (32 + j) = nth j [w64 (x_cap cx); w64 (x_fr cx + FO_N); w64 c] (Z_to_bv 64 0)).
{ intros j Hj. subst EA. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
pose proof (EAx 0%nat ltac:(lia)) as EA32. pose proof (EAx 1%nat ltac:(lia)) as EA33.
pose proof (EAx 2%nat ltac:(lia)) as EA34. cbn [Nat.add nth] in EA32, EA33, EA34. clear EAx.
assert (EA9 : ew EA 9 = getr regs 9) by (apply EAr; reflexivity).
assert (EA16 : ew EA 16 = getr regs 16) by (apply EAr; reflexivity).
assert (EA24 : ew EA 24 = getr regs 24) by (apply EAr; reflexivity).
assert (EA9u : bv_unsigned (ew EA 9) = x_s1 cx) by (rewrite EA9, R9; unfold w64; apply unsigned_lit_small; lia).
assert (HEIA : img_env VAL A_LIM EA) by (subst EA; apply Eimg_env).
assert (HAEA : env_agree 32 (Ereg regs [w64 (x_cap cx); w64 (x_fr cx + FO_N); w64 c]) EA)
  by (subst EA; split; [intros i Hi; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (SHA : sh_ok SEGS S24x [] EA (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HSA : st_ok_pi SEGS VAL EA s24_ssA
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K85bd0)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold s24_ssA. apply pa_entry_st_ok_full.
  - subst EA. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold s24_rA, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite EA9u. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + apply (chunk_ok_val SEGS EA _ (x_s1 cx) 32 8 (SOff 32 0) (x_cap cx));
        [cbn [sv_denot]; rewrite EA32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact (val_mem_of_rdword SEGS (w_H W) mem _ _ S32).
    + apply (chunk_ok_val SEGS EA _ (x_s1 cx) 48 8 (SOff 33 0) (x_fr cx + FO_N));
        [cbn [sv_denot]; rewrite EA33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | unfold FO_N; zside | zside |].
      exact (val_mem_of_rdword SEGS (w_H W) mem _ _ S48).
    + apply (chunk_ok_val SEGS EA _ (x_s1 cx) 160 8 (SOff 34 0) c);
        [cbn [sv_denot]; rewrite EA34, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact (val_mem_of_rdword SEGS (w_H W) mem _ _ S160).
  - exact (conj I I).
  - unfold facts_ok. cbn. tauto. }
clearbody EA. clear EAr.
pose proof HJ as HJ'. unfold s24_J in HJ'.
unfold cfg_at. change (w64 (BASE + LO_K85bd0)) with (Z_to_bv 64 (BASE + LO_K85bd0)).
paj_run_tok RUN HSA HJ' SHA s24_span.
{ apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdA := d) in *; clearbody mdA end.
lazymatch goal with
| HFr : frame_of ?E0 _ (mrestrict _ _) (mrestrict _ ?m1) |- _ =>
  assert (KEEPA0 : forall a, 0 <= a < 2 ^ 64 -> rdW W m1 a = rdW W mem a)
    by (intros a Ha; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
        [ intros b wlo whi a' Hin' Hrr'; vm_compute in Hin'; destruct Hin' as [Heq | []]; inversion Heq; subst; lia
        | exact Ha | intros Hff; destruct Hff ])
end.
pmkst HSA.
rewrite (SIGP SS_reac_segconf_declared ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_reac_segconf_declared) with AF_reac_segconf_declared by (vm_compute; reflexivity).
prreg HSA (1%bv : bv 5) PA1. prreg HSA (10%bv : bv 5) PA10. prreg HSA (11%bv : bv 5) PA11.
prreg HSA (12%bv : bv 5) PA12. prreg HSA (13%bv : bv 5) PA13. prreg HSA (18%bv : bv 5) PA18.
prreg HSA (19%bv : bv 5) PA19. prreg HSA (20%bv : bv 5) PA20. prreg HSA (22%bv : bv 5) PA22.
pose proof (regs_kept_of_st_ok SEGS _ _ _ regs _ ([2; 3; 4; 8; 9; 16; 21; 24]%bv : list (bv 5)) HSA HAEA
  ltac:(vm_compute; reflexivity)) as HKA.
cbn [ms_regs restrict] in HKA.
set (regsA := ms_regs ms) in *. set (memA := ms_mem ms) in *.
assert (KEEPA : forall a, rdW W memA a = rdW W mem a) by exact (s24_keep_all (w_H W) mem memA KEEPA0).
assert (HFRA : s24_fregs regs regsA).
{ intros r Hr. destruct Hr as [-> | [-> | [-> | [-> | ->]]]]; apply HKA; cbn [In];
    repeat (first [left; apply bv_eq; reflexivity | right]). }
assert (QA : forall r, In r ([2; 3; 4; 8; 9; 16; 21; 24]%bv : list (bv 5)) -> getr regsA r = getr regs r) by exact HKA.
(* the cut's facts at the run's end (it wrote nothing) *)
pose proof (s24_core_step_f B MT IMGS BSYM cx ly S W regs mem md k acc 4 LFO_N _ ly S W regsA memA mdA k acc 4 _
  HBASE HCORE HJ' HFRA (s24_kept_all B cx W W mem memA KEEPA) HBL HBUD) as HCOREA.
pose proof (s24_cm_ext _ _ c m (x_run cx) KEEPA HCM) as HCMA.
pose proof (s24_tabs_ext cx _ _ tab mt _ KEEPA HTABS) as HTABSA.
pose proof HCOREA as ((_ & _ & _ & _ & _ & _ & HSVA & _) & (HRODA & _) & _).
destruct (s24_decl_pre B MT cx ly S W regsA memA mdA k acc c m tab mt HBASE HCOREA HCMA HTABSA)
  as (HDP & HROOM & HEVD).
destruct (s24_chain B MT cx ly S W memA mdA k HBASE HJ' HSVA) as (ch1 & HCH1).
(* the registers at the call *)
assert (PA10' : getr regsA 10 = w64 c) by exact (eq_trans PA10 EA34).
assert (PA11' : getr regsA 11 = w64 tab) by exact (eq_trans PA11 (eq_trans EA24 R24)).
assert (PA12' : getr regsA 12 = w64 (x_cap cx)) by exact (eq_trans PA12 EA32).
assert (PA13' : getr regsA 13 = w64 (x_fr cx + FO_N)) by exact (eq_trans PA13 EA33).
assert (Hspc : spZ regsA = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
{ unfold spZ. transitivity (bv_unsigned (w64 (x_s1 cx)));
    [f_equal; exact (eq_trans (QA 2%bv ltac:(left; reflexivity)) R2) | unfold w64; rewrite unsigned_lit_small by lia; lia]. }
assert (Hs0A : s0Z regsA = x_sp0 cx).
{ unfold s0Z. transitivity (bv_unsigned (w64 (x_sp0 cx)));
    [f_equal; exact (eq_trans (QA 8%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) R8)
    | unfold w64; apply unsigned_lit_small; lia]. }
assert (HgpA : getr regsA 3 = w64 (as_gp B))
  by exact (eq_trans (QA 3%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) (eq_trans R3 Hgp0)).
assert (HtpA : getr regsA 4 = w64 (as_tp B))
  by exact (eq_trans (QA 4%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) (eq_trans R4 Htp0)).
assert (HraA : YK0s.ret_ok (getr regsA 1)) by (rewrite PA1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra4A : 4096 <= bv_unsigned (getr regsA 1)) by (rewrite PA1, unsigned_lit_small by lia; lia).
assert (HCH1' : achain ly (rdW W memA) (x_sp0 cx + (x_s1 cx - x_sp0 cx)) (s0Z regsA) ch1)
  by (rewrite Hs0A; replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) by lia; exact HCH1).
assert (HSTKD : STK_reac_segconf_declared = 12560) by reflexivity.
assert (Ht64 : 0 <= tab < 2 ^ 64) by (unfold x_tabn, seg_spec.RVLAN_SIZE in HtC; lia).
(* the call of reac_segconf_declared (cl_callS_wide: its footprint holds the count cell n in this function's frame) *)
pose proof (fun HPRE1 => HDECL fx ly S W regsA memA mdA ch1 c tab (x_cap cx) (x_fr cx + FO_N)
  (seg_spec.seg_rc (x_run cx)) (x_tab0 cx) HPRE1 HRODA PA10' Hc64 PA11' Ht64 PA12' ltac:(lia) PA13'
  ltac:(unfold FO_N; lia) HDP HROOM HEVD) as HCALL.
lazymatch type of HCALL with _ -> SRr _ _ _ (apost_base _ _ _ _ _ _ _ _ _ _ _ ?Kq) => set (KQ := Kq) in HCALL end.
set (FP1 := declared_W tab (x_fr cx + FO_N) (x_tab0 cx) (snd gd)) in *.
assert (HFP1 : forall a, inFP FP1 a -> (tab <= a < tab + x_tabn cx) \/ (x_fr cx + FO_N <= a < x_fr cx + FO_N + 4)).
{ intros a Ha. destruct (s24_vtab_in tab (x_fr cx + FO_N) (x_tab0 cx) (snd gd) (x_cap cx) a Hlt1 Ha) as [H | H];
    [left; unfold x_tabn, seg_spec.RVLAN_SIZE; lia | right; exact H]. }
eapply SRr_bind.
{ apply (cl_callS_wide B LAWS W regsA memA (Z_to_bv 64 (BASE + AF_reac_segconf_declared)) STK_LLVMFuzzerTestOneInput
    (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S mdA k
    STK_reac_segconf_declared FP1 EV_reac_segconf_declared (x_s1 cx - x_sp0 cx) (getr regsA 1) ch1 KQ HJ' Hspc
    ltac:(rewrite Zminus_mod, Hs1al, Hal16; reflexivity) ltac:(lia) ltac:(rewrite HSTKD; lia)
    ltac:(rewrite HSTKD; unfold STK_LLVMFuzzerTestOneInput; lia) HgpA HtpA eq_refl HraA Hra4A HCH1').
  - intros HPRE1. eapply SRr_mono; [exact (HCALL HPRE1)|].
    unfold apost_base. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & Ec & HJ3 & HP3 & HQ3).
    exists ly3, S3, regs3, mem3, md3. split; [exact Ec|]. split; [exact HJ3|]. split; [exact HP3 | exact HQ3].
  - intros a Ha. destruct (HFP1 a Ha) as [H | H].
    + right; right; left. exists tab, (x_tabn cx). split; [exact HinT|]. split; [exact Htab0|]. rewrite Hreqt. exact H.
    + right; right; right; left. exists 3, (x_fpos cx). split; [left; reflexivity|]. left.
      unfold in_zr; cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 3) with 512. unfold FO_N in H. lia.
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso. destruct (HFP1 a Ha) as [H | H];
      unfold STK_LLVMFuzzerTestOneInput, FO_N in *; lia. }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & HK3).
unfold KQ in HK3. destruct HK3 as (R10d & HRT3 & HNV3 & HGD3 & (HPerm3 & -> & (f3 & ES3))).
rewrite PA1.
change EV_reac_segconf_declared with 0 in HJ3, HJc3. rewrite Z.add_0_r in HJ3.
replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) in HJc3 by lia.
assert (HSTKD' : 0 <= STK_reac_segconf_declared <= ASTACK) by (rewrite HSTKD; unfold ASTACK; lia).
(* what reac_segconf_declared kept: the cut's parts and the table mt *)
assert (HFP1b : forall a, inFP FP1 a -> (exists b n, In (b, n) (ablocks B ly S) /\ b <= a < b + req_size n) \/
  (x_fr cx + FO_N <= a < x_fr cx + FO_N + 4)).
{ intros a Ha. destruct (HFP1 a Ha) as [H | H];
    [left; exists tab, (x_tabn cx); rewrite Hreqt; split; [exact HinT | exact H] | right; exact H]. }
pose proof (s24_kept_of_journal B MT cx ly S W memA mdA k _ FP1 ly S3 W3 mem3 md3 0 HBASE HJ' HJc3 HSTKD' HFP1b) as K3.
pose proof (s24_kept_trans B cx W W W3 mem memA mem3 (s24_kept_all B cx W W mem memA KEEPA) K3) as K03.
assert (HinMT3 : In (mt, x_mtn cx) (ablocks B ly S3)) by (apply (Permutation_in _ (Permutation_sym HPerm3)); exact HinMT).
assert (HinT3 : In (tab, x_tabn cx) (ablocks B ly S3)) by (apply (Permutation_in _ (Permutation_sym HPerm3)); exact HinT).
pose proof HTABSA as (_ & _ & HGDA & _ & HMTA & _).
assert (HMT3 : sa_mtab (rdW W3 mem3) mt (snd wd)).
{ apply (s24_mtab_range (rdW W memA) _ mt _ HMTA). intros i Hi.
  apply (s24_blk_kept B cx ly S W memA mdA k _ FP1 ly S3 W3 mem3 md3 0 mt (x_mtn cx) HJ' HJc3 HinMT HinMT3).
  - intros a Ha. destruct (HFP1 a Ha) as [H | H]; [left | right; exact H].
    exists tab, (x_tabn cx). split; [exact HinT|]. split; [intros E; apply Hmt_tab; symmetry; exact E|].
    rewrite Hreqt. exact H.
  - rewrite Hreqm. unfold x_mtn, seg_spec.MVLAN_SIZE. lia. }
pose proof (HGD3 HGDA) as HGD3'.
(* the registers after the call *)
assert (P3 : forall r, acallee_saved r -> getr regs3 (Z_to_bv 5 r) = getr regsA (Z_to_bv 5 r)) by exact HP3.
assert (R3_9 : getr regs3 9 = w64 (x_s1 cx))
  by exact (eq_trans (P3 9 ltac:(unfold acallee_saved; lia)) (eq_trans (QA 9%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) R9)).
assert (R3_22 : getr regs3 22 = w64 (x_fr cx + FO_N))
  by exact (eq_trans (P3 22 ltac:(unfold acallee_saved; lia)) (eq_trans PA22 EA33)).
(* ---- 0x85bf4 .. 0x85c0c, the jal of check_declared ---- *)
set (len1 := Z.of_nat (length (snd gd))) in *. set (mn := Z.of_nat (length (snd wd))) in *.
set (EC := Eimg (Ereg regs3 [w64 len1; w64 (fst wd mod 2 ^ 64); w64 mt; w64 mn])).
assert (ECr : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew EC n = getr regs3 rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst EC. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (ECx : forall j, (j < 4)%nat ->
  ew EC (32 + j) = nth j [w64 len1; w64 (fst wd mod 2 ^ 64); w64 mt; w64 mn] (Z_to_bv 64 0)).
{ intros j Hj. subst EC. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
pose proof (ECx 0%nat ltac:(lia)) as EC32. pose proof (ECx 1%nat ltac:(lia)) as EC33.
pose proof (ECx 2%nat ltac:(lia)) as EC34. pose proof (ECx 3%nat ltac:(lia)) as EC35.
cbn [Nat.add nth] in EC32, EC33, EC34, EC35. clear ECx.
assert (EC9u : bv_unsigned (ew EC 9) = x_s1 cx)
  by (rewrite (ECr 9%nat 9%bv eq_refl), R3_9; unfold w64; apply unsigned_lit_small; lia).
assert (EC22u : bv_unsigned (ew EC 22) = x_fr cx + FO_N)
  by (rewrite (ECr 22%nat 22%bv eq_refl), R3_22; unfold w64; apply unsigned_lit_small; unfold FO_N; lia).
assert (EC20 : ew EC 20 = getr regs3 20) by (apply ECr; reflexivity).
assert (EC24 : ew EC 24 = getr regs3 24) by (apply ECr; reflexivity).
assert (HEIC : img_env VAL A_LIM EC) by (subst EC; apply Eimg_env).
assert (HAEC : env_agree 32 (Ereg regs3 [w64 len1; w64 (fst wd mod 2 ^ 64); w64 mt; w64 mn]) EC)
  by (subst EC; split; [intros i Hi; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (SHC : sh_ok SEGS S24x [] EC (mrestrict (w_H W3) mem3)) by apply Forall_nil.
assert (Hlen1 : 0 <= len1 <= 39) by (unfold len1; lia).
assert (Hmn : 0 <= mn <= 39) by (unfold mn; lia).
assert (Hmt64 : 0 <= mt < 2 ^ 64) by (unfold x_mtn, seg_spec.MVLAN_SIZE in HmtC; lia).
assert (S104' : rdword (rdW W3 mem3) (x_s1 cx + 104) = Some (fst wd mod 2 ^ 64))
  by (rewrite <- S104; apply rdword_ext; intros q Hq; apply (proj1 K03); lia).
assert (S112' : rdword (rdW W3 mem3) (x_s1 cx + 112) = Some mt)
  by (rewrite <- S112; apply rdword_ext; intros q Hq; apply (proj1 K03); lia).
assert (S120' : rdword (rdW W3 mem3) (x_s1 cx + 120) = Some mn)
  by (rewrite <- S120; apply rdword_ext; intros q Hq; apply (proj1 K03); lia).
assert (HSC : st_ok_pi SEGS VAL EC s24_ssC
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + LO_S16C)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold s24_ssC. apply pa_entry_st_ok_full.
  - subst EC. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold s24_rC1, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite EC22u. split; [unfold FO_N; lia|]. split; [unfold FO_N; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS EC _ (x_fr cx + FO_N) 0 4 (SOff 32 0) len1);
        [cbn [sv_denot]; rewrite EC32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W3) mem3 _ _ HNV3).
    + unfold s24_rC2, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite EC9u. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      * apply (chunk_ok_val SEGS EC _ (x_s1 cx) 104 8 (SOff 33 0) (fst wd mod 2 ^ 64));
          [cbn [sv_denot]; rewrite EC33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        exact (val_mem_of_rdword SEGS (w_H W3) mem3 _ _ S104').
      * apply (chunk_ok_val SEGS EC _ (x_s1 cx) 112 8 (SOff 34 0) mt);
          [cbn [sv_denot]; rewrite EC34, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        exact (val_mem_of_rdword SEGS (w_H W3) mem3 _ _ S112').
      * apply (chunk_ok_val SEGS EC _ (x_s1 cx) 120 8 (SOff 35 0) mn);
          [cbn [sv_denot]; rewrite EC35, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        exact (val_mem_of_rdword SEGS (w_H W3) mem3 _ _ S120').
  - unfold s24_rC1, s24_rC2. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite EC22u, EC9u.
    split; [split; [left; unfold FO_N; lia | exact I] | split; exact I].
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite EC32. unfold w64. rewrite unsigned_lit_small by lia.
    rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia. }
clearbody EC. clear ECr.
change (getr regs3 9) with (getr regs3 9) in R3_9.
paj_run_tok RUN HSC HJ3 SHC s24_span.
{ apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdC := d) in *; clearbody mdC end.
lazymatch goal with
| HFr : frame_of ?E0 _ (mrestrict _ _) (mrestrict _ ?m1) |- _ =>
  assert (KEEPC0 : forall a, 0 <= a < 2 ^ 64 -> rdW W3 m1 a = rdW W3 mem3 a)
    by (intros a Ha; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
        [ intros b wlo whi a' Hin' Hrr'; vm_compute in Hin'; destruct Hin' as [Heq | [Heq | []]];
          inversion Heq; subst; lia
        | exact Ha | intros Hff; destruct Hff ])
end.
pmkst HSC.
rewrite (SIGP SS_check_declared ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_check_declared) with AF_check_declared by (vm_compute; reflexivity).
prreg HSC (1%bv : bv 5) PC1. prreg HSC (11%bv : bv 5) PC11. prreg HSC (12%bv : bv 5) PC12.
prreg HSC (13%bv : bv 5) PC13. prreg HSC (14%bv : bv 5) PC14. prreg HSC (15%bv : bv 5) PC15.
prreg HSC (16%bv : bv 5) PC16. prreg HSC (22%bv : bv 5) PC22.
pose proof (regs_kept_of_st_ok SEGS _ _ _ regs3 _ ([2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 24]%bv : list (bv 5)) HSC HAEC
  ltac:(vm_compute; reflexivity)) as HKC.
cbn [ms_regs restrict] in HKC.
lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rr _ ?mm _ |} _ => set (regsC := rr) in *; set (memC := mm) in * end.
assert (QC : forall r, In r ([2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 24]%bv : list (bv 5)) -> getr regsC r = getr regs3 r)
  by exact HKC.
Ltac s24_inbv := cbn [In]; repeat (first [left; reflexivity | left; apply bv_eq; reflexivity | right]).
assert (KEEPC : forall a, rdW W3 memC a = rdW W3 mem3 a) by exact (s24_keep_all (w_H W3) mem3 memC KEEPC0).
assert (HFR3C : s24_fregs regs3 regsC).
{ intros r Hr. destruct Hr as [-> | [-> | [-> | [-> | ->]]]]; apply HKC; cbn [In];
    repeat (first [left; apply bv_eq; reflexivity | right]). }
assert (HFRAC : s24_fregs regs regsC)
  by exact (s24_fregs_trans _ _ _ HFRA (s24_fregs_trans _ _ _ (s24_fregs_of_pres _ _ HP3) HFR3C)).
pose proof (s24_kept_trans B cx W W3 W3 mem mem3 memC K03 (s24_kept_all B cx W3 W3 mem3 memC KEEPC)) as K0C.
assert (HBL3 : lt_blocks B cx ly S3 [(mt, x_mtn cx); (tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)])
  by exact (Permutation_trans HPerm3 HBL).
assert (HBUD3 : lt_bud MT cx S3 k acc 4) by (rewrite ES3; exact (s24_bud_noalloc MT MTFL cx S k acc 4 f3 HBUD)).
pose proof (s24_core_step_f B MT IMGS BSYM cx ly S W regs mem md k acc 4 LFO_N _ ly S3 W3 regsC memC mdC k acc 4 _
  HBASE HCORE HJ3 HFRAC K0C HBL3 HBUD3) as HCOREC.
pose proof HCOREC as ((_ & _ & _ & _ & _ & _ & HSVC & _) & (HRODC & _) & _).
destruct (s24_chain B MT cx ly S3 W3 memC mdC k HBASE HJ3 HSVC) as (ch2 & HCH2).
(* check_declared's premises *)
set (got := fst gd mod 2 ^ 64) in *. set (want := fst wd mod 2 ^ 64) in *.
pose proof (proj1 HJ3) as HARC.
assert (HCPRE : check_declared_pre B ly S3 (rdW W3 memC) got want tab len1 mt mn (x_cap cx) (fst gd) (fst wd) (snd gd) (snd wd)).
{ apply (s24_chk_pre B MT cx ly S3 W3 memC mdC tab mt got want HBASE HARC HinT3 HinMT3 Hmc32 eq_refl eq_refl
    ltac:(lia) (s24_rtab_ext _ _ tab _ KEEPC HRT3) (s24_guard_ext _ _ tab _ KEEPC HGD3')
    (s24_mtab_ext _ _ mt _ KEEPC HMT3) HmnLe). }
pose proof (Z.mod_pos_bound (fst gd) (2 ^ 64) ltac:(lia)) as Hgm.
assert (PC10' : getr regsC 10 = w64 got)
  by (unfold got; rewrite s24_w64_mod; exact (eq_trans (QC 10%bv ltac:(s24_inbv)) R10d)).
assert (PC11' : getr regsC 11 = w64 want) by exact (eq_trans PC11 EC33).
assert (PC12' : getr regsC 12 = w64 tab)
  by exact (eq_trans PC12 (eq_trans EC24 (eq_trans (P3 24 ltac:(unfold acallee_saved; lia))
    (eq_trans (QA 24%bv ltac:(s24_inbv)) R24)))).
assert (PC13' : getr regsC 13 = w64 len1) by exact (eq_trans PC13 EC32).
assert (PC14' : getr regsC 14 = w64 mt) by exact (eq_trans PC14 EC34).
assert (PC15' : getr regsC 15 = w64 mn) by exact (eq_trans PC15 EC35).
assert (PC16' : getr regsC 16 = w64 (x_cap cx))
  by exact (eq_trans PC16 (eq_trans EC20 (eq_trans (P3 20 ltac:(unfold acallee_saved; lia)) (eq_trans PA20 EA32)))).
assert (HEVC : st_nev S3 + EV_check_declared <= EV_MAX).
{ pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _). pose proof HBUD3 as (Hk0 & _ & Hkr & _).
  pose proof HBASE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEV0 & _). unfold EV_check_declared. lia. }
assert (HspC : spZ regsC = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
{ unfold spZ. transitivity (bv_unsigned (w64 (x_s1 cx)));
    [f_equal; exact (eq_trans (HFRAC 2 ltac:(lia)) R2) | unfold w64; rewrite unsigned_lit_small by lia; lia]. }
assert (Hs0C : s0Z regsC = x_sp0 cx).
{ unfold s0Z. transitivity (bv_unsigned (w64 (x_sp0 cx)));
    [f_equal; exact (eq_trans (HFRAC 8 ltac:(lia)) R8) | unfold w64; apply unsigned_lit_small; lia]. }
assert (HgpC : getr regsC 3 = w64 (as_gp B)) by exact (eq_trans (HFRAC 3 ltac:(lia)) (eq_trans R3 Hgp0)).
assert (HtpC : getr regsC 4 = w64 (as_tp B)) by exact (eq_trans (HFRAC 4 ltac:(lia)) (eq_trans R4 Htp0)).
assert (HraC : YK0s.ret_ok (getr regsC 1)) by (rewrite PC1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra4C : 4096 <= bv_unsigned (getr regsC 1)) by (rewrite PC1, unsigned_lit_small by lia; lia).
assert (HCH2' : achain ly (rdW W3 memC) (x_sp0 cx + (x_s1 cx - x_sp0 cx)) (s0Z regsC) ch2)
  by (rewrite Hs0C; replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) by lia; exact HCH2).
assert (HSTKC : STK_check_declared = 8272) by reflexivity.
pose proof (fun HPRE1 => HCHKD fx ly S3 W3 regsC memC mdC ch2 got want tab len1 mt mn (x_cap cx) (fst gd) (fst wd)
  (snd gd) (snd wd) HPRE1 HRODC PC10' Hgm PC11' Hwm PC12' Ht64 PC13' ltac:(lia) PC14' Hmt64 PC15' ltac:(lia)
  PC16' ltac:(lia) HCPRE HEVC) as HCALL2.
lazymatch type of HCALL2 with _ -> SRr _ _ _ (apost_base _ _ _ _ _ _ _ _ _ _ _ ?Kq) => set (KQ2 := Kq) in HCALL2 end.
eapply SRr_bind.
{ apply (cl_callS B LAWS W3 regsC memC (Z_to_bv 64 (BASE + AF_check_declared)) STK_LLVMFuzzerTestOneInput
    (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S3 mdC k
    STK_check_declared [] EV_check_declared (x_s1 cx - x_sp0 cx) (getr regsC 1) ch2 KQ2 HJ3 HspC
    ltac:(rewrite Zminus_mod, Hs1al, Hal16; reflexivity) ltac:(lia) ltac:(rewrite HSTKC; lia)
    ltac:(rewrite HSTKC; unfold STK_LLVMFuzzerTestOneInput; lia) HgpC HtpC eq_refl HraC Hra4C HCH2').
  - intros HPRE1. eapply SRr_mono; [exact (HCALL2 HPRE1)|].
    unfold apost_base. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & Ec & HJ5 & HP5 & HQ5).
    exists ly5, S5, regs5, mem5, md5. split; [exact Ec|]. split; [exact HJ5|]. split; [exact HP5 | exact HQ5].
  - intros a (r & [] & _). }
cbv beta. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HJc5 & HP5 & HK5).
unfold KQ2 in HK5. destruct HK5 as (HSK5 & (HPerm5 & -> & (f5 & ES5))).
change EV_check_declared with 0 in HJ5. rewrite Z.add_0_r in HJ5.
rewrite PC1.
(* what check_declared kept, and the cut's facts at its return *)
pose proof (s24_kept_of_sa_kept B MT cx ly S3 W3 memC mdC k W5 mem5 regsC STK_check_declared HBASE HJ3
  ltac:(rewrite HspC; lia) ltac:(rewrite HSTKC; unfold ASTACK; lia) HSK5) as K5.
assert (HBL5 : lt_blocks B cx ly S5 [(mt, x_mtn cx); (tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)])
  by exact (Permutation_trans HPerm5 HBL3).
assert (HBUD5 : lt_bud MT cx S5 k acc 4) by (rewrite ES5; exact (s24_bud_noalloc MT MTFL cx S3 k acc 4 f5 HBUD3)).
pose proof (s24_core_step B MT IMGS BSYM cx ly S3 W3 regsC memC mdC k acc 4 LFO_N _ ly S5 W5 regs5 mem5 md5 k acc 4 _
  HBASE HCOREC HJ5 HP5 K5 HBL5 HBUD5) as HCORE5.
pose proof (s24_kept_trans B cx W W3 W5 mem memC mem5 K0C K5) as K05.
(* ---- 0x85c14 .. 0x85c18: free(mt), back at K85c1c ---- *)
pose proof HCORE5 as ((HJ5' & R5_2 & R5_3 & R5_4 & R5_8 & R5_9 & HSV5 & _) & _ & _ & _).
pose proof (proj1 HJ5) as HAR5.
destruct (s24_blk_head B cx ly S5 W5 mem5 md5 mt (x_mtn cx) _ HAR5 HBL5) as (HinMT5 & Hnb05 & _).
destruct (s24_bud_free B MT MTL cx ly S5 W5 mem5 md5 k acc 4 HBASE HJ5 HBUD5 ltac:(lia)) as (Hnev5 & MOK5 & HBUD').
assert (P5 : forall r, acallee_saved r -> getr regs5 (Z_to_bv 5 r) = getr regsC (Z_to_bv 5 r)) by exact HP5.
assert (R5_22 : getr regs5 22 = w64 mt) by exact (eq_trans (P5 22 ltac:(unfold acallee_saved; lia)) (eq_trans PC22 EC34)).
apply (s24_free B MT (AFREE4 fx) TL cx ly S5 W5 regs5 mem5 md5 k mt (x_mtn cx) 0xee0 22%bv _ HBASE
  (or_introl (conj eq_refl eq_refl)) HJ5 R5_2 R5_3 R5_4 R5_8 HSV5 R5_22 HinMT5 Hnb05 Hnev5 MOK5).
intros ly6 S6 W6 regs6 mem6 md6 HJ6 HP6 Hbl6 Hfr6 HK6 MLE6.
pose proof (proj1 HJ6) as HAR6.
assert (HBL6 : lt_blocks B cx ly6 S6 [(tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)])
  by exact (s24_perm_free _ _ _ _ _ HBL5 Hbl6).
pose proof (HBUD' S6 MLE6) as HBUD6.
pose proof (s24_core_step B MT IMGS BSYM cx ly S5 W5 regs5 mem5 md5 k acc 4 LFO_N _ ly6 S6 W6 regs6 mem6 md6 (k + 1)
  (acc + mo_free MT) (4 - 1) _ HBASE HCORE5 HJ6 HP6 HK6 HBL6 HBUD6) as HCORE6.
pose proof (s24_kept_trans B cx W W5 W6 mem mem5 mem6 K05 HK6) as K06.
assert (P6 : forall r, acallee_saved r -> getr regs6 (Z_to_bv 5 r) = getr regs5 (Z_to_bv 5 r)) by exact HP6.
(* a callee-saved register of the cut, from the run of 0x85bd0 through both calls, the run of 0x85bf4 and free *)
assert (KR : forall (n : Z) (rr : bv 5), acallee_saved n -> Z_to_bv 5 n = rr -> In rr ([18; 19; 20; 21; 24]%bv : list (bv 5)) ->
  getr regs6 rr = getr regsA rr).
{ intros n rr Hn <- Hin. rewrite (P6 n Hn), (P5 n Hn). rewrite (QC (Z_to_bv 5 n)).
  - exact (P3 n Hn).
  - destruct Hin as [E | [E | [E | [E | [E | []]]]]]; rewrite <- E; s24_inbv. }
assert (R6_18 : getr regs6 18 = w64 c)
  by exact (eq_trans (KR 18 18%bv ltac:(unfold acallee_saved; lia) eq_refl ltac:(s24_inbv)) (eq_trans PA18 EA34)).
assert (R6_19 : getr regs6 19 = w64 m)
  by exact (eq_trans (KR 19 19%bv ltac:(unfold acallee_saved; lia) eq_refl ltac:(s24_inbv)) (eq_trans PA19 (eq_trans EA16 R16))).
assert (R6_21 : getr regs6 21 = w64 (x_sh cx))
  by exact (eq_trans (KR 21 21%bv ltac:(unfold acallee_saved; lia) eq_refl ltac:(s24_inbv)) (eq_trans (QA 21%bv ltac:(s24_inbv)) R21)).
assert (R6_24 : getr regs6 24 = w64 tab)
  by exact (eq_trans (KR 24 24%bv ltac:(unfold acallee_saved; lia) eq_refl ltac:(s24_inbv)) (eq_trans (QA 24%bv ltac:(s24_inbv)) R24)).
assert (HSL6 : lt_slots cx (rdW W6 mem6) [(8, x_fr cx); (24, x_fr cx)]).
{ apply (s24_slots_kept B MT cx W W6 mem mem6 _ HBASE); [| |exact K06].
  - intros o v Hov. apply HSL. cbn [In] in Hov |- *. destruct Hov as [Hov | [Hov | []]]; rewrite <- Hov; s24_inbv.
  - intros o v Hov. cbn [In] in Hov. destruct Hov as [Hov | [Hov | []]]; injection Hov as <- <-; lia. }
exact (K1c fx cx ly6 S6 W6 regs6 mem6 md6 (k + 1) (acc + mo_free MT) c m tab HBASE HFRM HCORE6
  (s24_hblk B ly6 S6 W6 mem6 md6 c _ HAR6 (s24_blk_in B cx ly6 S6 _ _ HBL6 ltac:(right; right; left; reflexivity)))
  (s24_hblk B ly6 S6 W6 mem6 md6 m _ HAR6 (s24_blk_in B cx ly6 S6 _ _ HBL6 ltac:(right; left; reflexivity)))
  (s24_hblk B ly6 S6 W6 mem6 md6 tab _ HAR6 (s24_blk_in B cx ly6 S6 _ _ HBL6 ltac:(left; reflexivity)))
  R6_18 R6_19 R6_21 R6_24 HSL6).
Qed.

(* ============================== S20 0x85c34 .. 0x85c40: n out of scope, a6 / a7 reloaded ============================== *)
(* the seed at 0x85c34: every register its own atom, atom 32 = FR; the region of n's shadow byte SH(FR) + 32 (base
   s5, a one-byte write window) and the two slots 8(s1) and 24(s1) holding FR (read only); s5 is a shadow address.
   The run's shadow span is (0, 0): no shadow check is run here, and the write window lies in the shadow band, so
   the span must miss it (sh_static_ok's cells_safe_b) *)
Definition s24p_rsh : YP09.region := YP09.mkRegion (Some 21%nat) 32 33 32 33 [].
Definition s24p_rsl : YP09.region := YP09.mkRegion (Some 9%nat) 8 32 0 0
  [YP09.mkChunk 8 (CVal 8 (SOff 32 0)); YP09.mkChunk 24 (CVal 8 (SOff 32 0))].
Definition s24p_facts : facts := mkFacts [(21%nat, mkAF SB (SB + 2 ^ 44) 0)] [] [].
Definition s24p_ss : sstate := mkSS LO_K85c34 sr_atoms [s24p_rsh; s24p_rsl] None s24p_facts.
Definition s24p_span : Z * Z := (0, 0).

(* the 36 shadow bytes after n's byte (index 32) is set to 0xf8: the LFO0 pattern *)
Lemma s24p_fsh_n0 : forall (rd rd' : reader) sh,
  sa_zs rd sh (lt_fsh LFO_N) -> (forall i, 0 <= i < 36 -> i <> 32 -> rd' (sh + i) = rd (sh + i)) ->
  rd' (sh + 32) = Some 0xf8 -> sa_zs rd' sh (lt_fsh LFO0).
Proof.
intros rd rd' sh H HK H32 i Hi. rewrite lt_fsh_len in Hi.
destruct (Nat.eq_dec i 32) as [-> | Hne].
- exact H32.
- rewrite (HK (Z.of_nat i)) by lia.
  replace (nth i (lt_fsh LFO0) 0) with (nth i (lt_fsh LFO_N) 0).
  + exact (H i ltac:(rewrite lt_fsh_len; exact Hi)).
  + do 36 (destruct i as [|i]; [first [reflexivity | lia] |]). lia.
Qed.


Let RUNTO := paj_run_to B LAWS.

Lemma lt_seg_S20 : lt_seg_S20_stmt B MT.
Proof.
intros K44 cx ly S W regs mem md k acc HBASE HFRM HCORE R21 HSL.
pose proof HCORE as (HFR & HIMG & HBL & HBUD).
pose proof HFR as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & _ & _ & _ & _ & _ & HSH).
pose proof (proj1 HJ) as HAR.
pose proof (s24_nums B MT cx HBASE) as (Hal16 & Hs1al & Hs1 & Hceil & H47 & Htop & Htop2).
destruct (s24_frame_at B cx ly S W mem md k HJ) as (Hin3 & EFA & HF4 & HFc & HFapp & HF32 & HFpres & HFSpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBok.
assert (HSHr : SB + 512 <= x_sh cx <= SB + 17592184995840).
{ assert (HFc' : x_fr cx <= 0x7fffff800000) by lia.
  pose proof (Z.div_le_mono 4096 (x_fr cx) 8 ltac:(lia) HF4) as D1.
  pose proof (Z.div_le_mono (x_fr cx) 0x7fffff800000 8 ltac:(lia) HFc') as D2.
  change (4096 / 8) with 512 in D1. change (0x7fffff800000 / 8) with 17592184995840 in D2.
  unfold x_sh, shadow_addr, SHADOW_OFF, SB. lia. }
unfold SB in HSHr.
(* the slots 8(s1) and 24(s1) *)
assert (SL8 : rdword (rdW W mem) (x_s1 cx + 8) = Some (x_fr cx)) by (apply HSL; left; reflexivity).
assert (SL24 : rdword (rdW W mem) (x_s1 cx + 24) = Some (x_fr cx)) by (apply HSL; right; left; reflexivity).
(* the seed *)
set (E := Eimg (Ereg regs [w64 (x_fr cx)])).
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (HAE : env_agree 32 (Ereg regs [w64 (x_fr cx)]) E)
  by (split; [intros i Hi; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E32 : ew E 32 = w64 (x_fr cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs [w64 (x_fr cx)] 0)).
assert (U21 : bv_unsigned (ew E 21) = x_sh cx)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = x_s1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E s24p_ss
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K85c34)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold s24p_ss. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold s24p_rsh, s24p_rsl. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U21. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). replace (x_sh cx + o) with (x_sh cx + 32) by lia.
      exact (HFSpres 32 ltac:(lia)).
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      assert (DF : sv_denot E (SOff 32 0) = Z_to_bv 64 (x_fr cx))
        by (cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E _ (x_s1 cx) 8 8 (SOff 32 0) (x_fr cx) DF); [cbn; lia | cbn; lia |].
        exact (val_mem_of_rdword SEGS (w_H W) mem _ _ SL8).
      * apply (chunk_ok_val SEGS E _ (x_s1 cx) 24 8 (SOff 32 0) (x_fr cx) DF); [cbn; lia | cbn; lia |].
        exact (val_mem_of_rdword SEGS (w_H W) mem _ _ SL24).
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, s24p_rsh, s24p_rsl.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U21, U9.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  - unfold facts_ok, s24p_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U21, Z.pow_0_r, Z.mod_1_r.
    unfold SB. repeat match goal with |- _ /\ _ => split end; try exact I; try reflexivity; lia. }
assert (SHOK : sh_ok SEGS S24x [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
pose proof HJ as HJ'. unfold s24_J in HJ'.
unfold cfg_at. change (w64 (BASE + LO_K85c34)) with (Z_to_bv 64 (BASE + LO_K85c34)).
paj_run_to_tok RUNTO HS HJ' SHOK s24p_span 0xf10.
- (* what the run may write: n's shadow byte, a shadow byte of the frame (3, x_fpos cx) *)
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_gen with (n := 21%nat) (b := x_sh cx); [reflexivity | exact U21 | |].
  + intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
    right; right; right; left. exists 3, (x_fpos cx). split; [left; reflexivity|].
    right. rewrite EFA. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 3 / 8) with 64. unfold x_sh in Ha. lia.
  + apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil.
- lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
  pmkst HS.
  lazymatch type of HS with context [restrict _ ?m] => rename m into msK end.
  prreg HS (16%bv : bv 5) P16. prreg HS (17%bv : bv 5) P17.
  assert (G16 : getr (ms_regs msK) 16 = w64 (x_fr cx))
    by (rewrite P16; first [exact E32 | rewrite E32; unfold w64; rewrite ?Z_to_bv_bv_unsigned; reflexivity]).
  assert (G17 : getr (ms_regs msK) 17 = w64 (x_fr cx))
    by (rewrite P17; first [exact E32 | rewrite E32; unfold w64; rewrite ?Z_to_bv_bv_unsigned; reflexivity]).
  assert (HPT : aregs_preserved regs (ms_regs msK))
    by (eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs [w64 (x_fr cx)] HS); [exact HAE | vm_compute; reflexivity]).
  assert (G21 : getr (ms_regs msK) 21 = w64 (x_sh cx))
    by exact (eq_trans (HPT 21 ltac:(unfold acallee_saved; lia)) R21).
  (* every byte but SH(FR) + 32 is kept *)
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> a <> x_sh cx + 32 -> rdW W (ms_mem msK) a = rdW W mem a).
  { intros a Ha Hne. apply (kept_of_frame (segs := SEGS) E _ _ _ _ (fun y => y = x_sh cx + 32) HFr); [|exact Ha | exact Hne].
    intros b wlo whi a' Hw Ha'. vm_compute in Hw.
    destruct Hw as [Hw | [Hw | []]]; injection Hw as <- <- <-; cbn [base_val] in Ha'; rewrite ?U21, ?U9 in Ha'; lia. }
  (* the new byte SH(FR) + 32: 0xf8, from the shadow region's chunk *)
  assert (HN32 : sa_zs (rdW W (ms_mem msK)) (x_sh cx + 32) [0xf8]).
  { lazymatch type of HS with st_ok_pi _ _ _ ?ssB _ =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssB) (YP09.mkRegion None 0 0 0 0 [])) in
    pose proof (PaLibG.st_ok_pi_region_nth E _ (restrict (w_H W) msK) 0 r0 HS ltac:(vm_compute; reflexivity)) as RSH end.
    destruct RSH as (_ & _ & _ & CSH). cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in CSH.
    rewrite U21 in CSH.
    exact (s10_zs_ok E (w_H W) (ms_mem msK) (x_sh cx) _ [0xf8] 32 CSH ltac:(vm_compute; reflexivity)). }
  assert (HSH0 : sa_zs (rdW W (ms_mem msK)) (x_sh cx) (lt_fsh LFO0)).
  { apply (s24p_fsh_n0 (rdW W mem) _ _ HSH).
    - intros i Hi Hne. apply KEEP; [|lia]. split; [lia|]. lia.
    - pose proof (HN32 0%nat ltac:(cbn; lia)) as H0. rewrite Z.add_0_r in H0. exact H0. }
  assert (KS : forall a, x_s1 cx <= a < x_sp0 cx -> rdW W (ms_mem msK) a = rdW W mem a)
    by (intros a Ha; apply KEEP; lia).
  assert (KF : forall a, x_fr cx <= a < x_fr cx + 24 \/ x_fr cx + 504 <= a < x_fr cx + 512 ->
    rdW W (ms_mem msK) a = rdW W mem a)
    by (intros a Ha; apply KEEP; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *; lia).
  assert (KI : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
    rdW W (ms_mem msK) a = rdW W mem a).
  { intros a Himg _ _. pose proof (pa_img_range _ Himg) as HIR. unfold kImgEnd in HIR. apply KEEP; lia. }
  apply (K44 fx cx ly S W (ms_regs msK) (ms_mem msK) mdv k acc HBASE HFRM).
  + split; [|split; [|split]].
    * exact (s24_frame_kept B MT cx ly S W regs mem md k LFO_N ly S W (ms_regs msK) (ms_mem msK) mdv k LFO0
        HBASE HFR HJ' (s24_fregs_of_pres _ _ HPT) KS KF HSH0).
    * exact (s10_lt_img_kept B IMGS BSYM cx W (ms_mem msK) (rdW W mem) (proj1 HJ') KI HIMG).
    * exact HBL.
    * exact HBUD.
  + exact G16.
  + exact G17.
  + exact G21.
Qed.

End e.
End f.
End d.

Print Assumptions lt_seg_S16.
Print Assumptions lt_seg_S17.
Print Assumptions lt_seg_S18.
Print Assumptions lt_seg_S19.
Print Assumptions lt_seg_S20.
