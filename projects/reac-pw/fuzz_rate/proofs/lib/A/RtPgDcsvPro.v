(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, a working branch), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, with its module paths and module names changed; 676 of its 753 lines of code are new or changed and 504 lines of the source are left out. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; addresses measured on its unstripped twin sha256
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): PART 1 of the walk of
   reac_rate_drivable_csv (0x84074), lib/A/RtPgDcsvDefs.v dc_pro_stmt: from the entry to the loop head 0x8420c with
   the class-1 side-stack frame seated. Proves no function (kind: segment lemma of reac_rate_drivable_csv's walk).

   THE WALK (the code is RtPgDcsvDefs.v's header, PART 1):
   - block A, entry state at 0x84074 over env Ereg regs [SHADOW_OFF; R] (slot 33 = R = 32 * ((S - 224) / 32)): the
     stack region [S - 224, S) and the four read-only cells (the two .got cells 0x9bec8 / 0x9be70, the use-after-return
     cell 0xa4c40 holding the 4-byte value 1, the shadow-offset cell 0xa4c38). One run to 0x840b8, right after
     `andi sp,sp,-32`; sp is pinned to atom 33 (R); the stack region is cut to the 13 saves [S - 104, S) and the real
     frame [R, R + 120) is added on atom 33. One run to the frame call: `beqz a2` at 0x840e4 is decided not taken
     (a2 = 1), the engine stops at 0x3cf9c with ra = 0x840f0.
   - the frame call: the class-1 astack_malloc_realizes of the runtime (dcp_sm, the kernel's aj_stack_malloc_at with
     the state, the frame's index bound and the law's own memory clause kept in the conclusion).
   - block B, entry state at 0x840f0 over env Ereg regs2 [SHADOW_OFF; shF; buf; n; mask]: the real frame on s1's
     atom with the four cells block A wrote, the frame F on a0's atom (window [F, F + 40)), its 16 shadow bytes on
     atom 33 = shadow_addr F. `bnez a0` at 0x840fc is decided taken (the atom's fact: F >= 4096), so the real-stack arm
     0x84100 .. 0x84118 is never stepped. One run to 0x8418c, s4 pinned to atom 33, one run to the loop head.
   - the cut: every conjunct of dc_loop c 0 at fq = fx. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05 YG0q YF0v YL07 YN0d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Model Layout RateCfg RateCsv.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgSiteA RtPgSteps RtPgDcsvDefs.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Rt Require Import SnprintfRateDef.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ======================================== arithmetic ======================================== *)
Lemma dcp_land32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
replace (2 ^ 64 - 32) with (Z.land (Z.lnot (Z.ones 5)) (Z.ones 64)) by reflexivity.
rewrite (Z.land_comm (Z.lnot (Z.ones 5)) (Z.ones 64)), Z.land_assoc, (Z.land_ones x 64) by lia.
rewrite (Z.mod_small x (2 ^ 64)) by lia.
rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.

(* `andi sp,sp,-32` after `addi sp,sp,-224`, as the engine writes it *)
Lemma dcp_and_denot : forall E (n : nat) s, bv_unsigned (ew E n) = s -> 224 <= s < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff n (-224)) (SLit (-32))) = Z_to_bv 64 (32 * ((s - 224) / 32)).
Proof.
intros E n s Hn Hs.
assert (Hq : 0 <= 32 * ((s - 224) / 32) <= s - 224).
{ pose proof (Z.div_mod (s - 224) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (s - 224) 32 ltac:(lia)).
  pose proof (Z.div_pos (s - 224) 32 ltac:(lia) ltac:(lia)). lia. }
apply bv_eq. rewrite (unsigned_lit_small (32 * ((s - 224) / 32))) by lia.
change (bv_unsigned (sv_denot E (SAlu ALU_AND (SOff n (-224)) (SLit (-32)))))
  with (U E (SAlu ALU_AND (SOff n (-224)) (SLit (-32)))).
rewrite U_SAlu, U_SOff, U_SLit, Hn. cbn [zalu_raw]. unfold zcanon, M64.
replace ((-32) mod 2 ^ 64) with (2 ^ 64 - 32) by reflexivity.
rewrite (Z.mod_small (s + -224) (2 ^ 64)) by lia.
replace (s + -224) with (s - 224) by lia.
rewrite dcp_land32 by lia. apply Z.mod_small. lia.
Qed.

Section mem. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* a 4-byte constant the runtime law states with rd32, as the val_mem a region chunk needs *)
Lemma dcp_vm_rd32 : forall H mem a v,
rd32 (aview rsegs H mem) a v -> val_mem rsegs (mrestrict H mem) a 4 v.
Proof.
intros H mem a v Hr k Hk. specialize (Hr k Hk).
apply aview_byte in Hr as (b & Hb & Hv & _). rewrite Hb. f_equal.
unfold YO0f.le_byte, YG0f.le_byte in *. rewrite Hv. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* the bytes of a CVal chunk of a region of a state, as val_mem *)
Lemma dcp_chunk_vm : forall E ss ms i r off (w : N) v val,
st_ok rsegs E ss ms -> nth_error (ss_mem ss) i = Some r -> In (YP09.mkChunk off (CVal w v)) (r_chunks r) ->
bv_unsigned (sv_denot E v) mod 2 ^ (8 * Z.of_N w) = val mod 2 ^ (8 * Z.of_N w) ->
val_mem rsegs (ms_mem ms) (base_val E (r_base r) + off) (N.to_nat w) val.
Proof.
intros E ss ms i r off w v val HS Hi Hc Hv k Hk.
exact (chunk_bytes_cval rsegs E (ms_mem ms) (base_val E (r_base r)) off w v val
  (st_ok_chunk rsegs E ss ms i r _ HS Hi Hc) Hv k Hk).
Qed.
(* a run keeps every byte outside the zone its write windows lie in (lib/A/RtPgCheck.v ck_kept_run) *)
Lemma dcp_kept_run : forall (Zn : Z -> Prop) E rs (H : word -> bool) (m0 m1 m2 : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m1 a = aview rsegs H m0 a) ->
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall a, in_wrange E rs a -> Zn a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m2 a = aview rsegs H m0 a.
Proof.
intros Zn E rs H m0 m1 m2 HK HF HW a Ha Hz. rewrite <- (HK a Ha Hz). unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.
End mem.
Lemma dcp_den0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof.
intros E n. apply bv_eq. rewrite denot_SOff, Z.add_0_r. unfold zcanon, M64. apply Z.mod_small.
pose proof (bv_unsigned_in_range _ (ew E n)) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb. exact Hb.
Qed.
Lemma dcp_w64_mod : forall x, bv_unsigned (w64 x) mod 2 ^ (8 * Z.of_N 8) = x mod 2 ^ (8 * Z.of_N 8).
Proof.
intros x. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.

Section own. Context {rc : YM05.RunCeil}.
Variable B : asyms.
(* what a side-stack frame call owns afterwards it owned before: the chunks and sections are the state's, the
   client set only grows by the new frame *)
Lemma dcp_aowned_back : forall ly Sc f cid pos a,
frames (set_fs f Sc) = (cid, pos) :: frames Sc -> aowned B ly (set_fs f Sc) a -> aowned B ly Sc a.
Proof.
intros ly Sc f cid pos a Hfr [Hst Hnc]. split; [exact Hst|].
intros [Hk | (cp & Hcp & Hr)]; apply Hnc; [left; exact Hk|].
right. exists cp. split; [rewrite Hfr; right; exact Hcp | exact Hr].
Qed.
End own.

(* ======================================== the frame call ======================================== *)
Section sm. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
(* YCbq aj_stack_malloc_at at class 1, also keeping the state the model returns, the frame's index bound, the
   callee's same_but_materialized and the law's own memory clause (owned bytes of the call and of the result) *)
Lemma dcp_sm : AR_laws rsegs B -> api_env rsegs B -> model_laws (as_universe B) -> stack_malloc_progressP B ->
astack_malloc_realizes rsegs B DC_CID -> pc_stack_malloc (as_code B) DC_CID = A_SM1 ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw,
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
count_cid DC_CID (frames Sc) < fs_frames DC_CID ->
SRr rsegs W (mkCfg (mkst regsT (Z_to_bv 64 A_SM1) memT (seg_rom rsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists S2 regs2 mem2 md2 pos f,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem md ((DC_CID, pos) :: own) lyc S2 W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (frame_addr lyc DC_CID pos) /\
same_but_materialized mdc md2 /\
S2 = set_fs f Sc /\ 0 <= pos < fs_frames DC_CID /\
frames S2 = (DC_CID, pos) :: frames Sc /\ ~ In (DC_CID, pos) (frames Sc) /\
zero_shadow (aview rsegs (w_H W) mem2) SHADOW_OFF (frame_addr lyc DC_CID pos) (fs_frame_bytes DC_CID) /\
rdword (aview rsegs (w_H W) mem2) (frame_addr lyc DC_CID pos + fs_frame_bytes DC_CID - 8) = Some (flag_addr lyc DC_CID pos) /\
(forall a, frame_addr lyc DC_CID pos <= a < frame_addr lyc DC_CID pos + fs_frame_bytes DC_CID -> apresent (w_H W) mem2 a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B lyc Sc a -> ~ aowned B lyc S2 a -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
  aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memT a)).
Proof.
intros LAWS AENV ML SMP ASM Epc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw
HJ Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hcnt.
pose proof rts_segs_low as Hsegs.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (ASTACK = 16384) as Has by reflexivity. assert (ESTACK = 4096) as Hes by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HstkC : astk_ok ESTACK lyc (spZ regsT)).
{ unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
  all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
assert (HPRE : ecall_pre rsegs B lyc Sc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|]. split; [destruct HstkC as (Q1 & _); exact Q1|].
  split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
  split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
assert (Hcid : 0 <= DC_CID <= 10) by (unfold DC_CID; lia).
pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
destruct (SMP Sc DC_CID HWF Hcid Hcnt) as (pos & S2 & Hpath).
pose proof (ml_stack_malloc _ ML Sc DC_CID HWF Hcid) as HTOK.
destruct (atok_apath _ _ _ [] (PFake DC_CID pos, S2) HTOK Hpath) as (ns' & HQ). unfold stack_malloc_post in HQ.
destruct HQ as (HWF2 & (f & ES2) & _ & Hpos & Hfrs2 & Hfresh).
rewrite <- Epc. change (Z_to_bv 64 (pc_stack_malloc (as_code B) DC_CID)) with (w64 (pc_stack_malloc (as_code B) DC_CID)).
eapply SRr_mono; [exact (ASM lyc Sc W regsT memT mdc pos S2 HPRE Hcnt Hpath)|].
cbv beta. intros W2 c2 HwleW (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hz & Hflag & Hfpres & Hfr & Hpres2).
assert (Hblk : blocks S2 = blocks Sc) by (rewrite ES2; reflexivity).
assert (Eab2 : ablocks B lyc S2 = ablocks B lyc Sc) by (unfold ablocks; rewrite Hblk; reflexivity).
assert (Hsecs2 : st_secs S2 = st_secs Sc) by (rewrite ES2; reflexivity).
assert (HJ1 : ajournal rsegs B ESTACK (spZ regsT) [] lyc Sc W memT mdc [(DC_CID, pos)] lyc S2 W mem2 md2 0).
{ eapply (call_effect_journal rsegs B LAWS Hsegs AENV ESTACK lyc Sc W regsT memT mdc lyc S2 W mem2 md2 (fun _ => False) [] [(DC_CID, pos)] 0);
  [exact HAR2 | apply layout_le_refl | apply wle_refl | apply same_io_materialized; exact Hsame | | exact Hpres2 | exact HAR | exact HstkC
  | cbn; exact Hfrs2 | rewrite ES2; cbn; zlia | zlia | rewrite Hsecs2; zlia | intros a [] | | ].
  - intros a H0 H1 H2 H3 _. apply (Hfr a H0 H1 H2). intros H. apply H3. left. exact H.
  - intros p n i Hp Hnp. exfalso. apply Hnp. rewrite Eab2. exact Hp.
  - rewrite ES2. apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT]. }
split; [reflexivity|]. exists S2, regs2, mem2, md2, pos, f.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ rewrite Hsp' in HJ1. replace k with (k + 0) by zlia. change ((DC_CID, pos) :: own) with ([(DC_CID, pos)] ++ own).
  eapply (ajournal_sub rsegs B LAWS Hsegs); [exact HJ | exact HJ1 | zlia | zlia | intros a (rg & [] & _)]. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hsame|]. split; [exact ES2|]. split; [exact Hpos|].
split; [exact Hfrs2|]. split; [exact Hfresh|]. split; [exact Hz|]. split; [exact Hflag|]. split; [exact Hfpres|].
intros a Ha H1 H2 H3. rewrite Hsp' in Hfr. exact (Hfr a Ha H1 H2 H3).
Qed.
End sm.

(* ======================================== block A: the entry to the frame call ========================================
   env slot 32 = the shadow offset, slot 33 = R; the stack region [S - 224, S) (the probe word and the 13 saves) and
   the four read-only cells the two .got loads and the two cell loads read. *)
Definition dcp_extraA (R : Z) : list word := [w64 SHADOW_OFF; w64 R].
Definition dcpA_stack : YP09.region := YP09.mkRegion (Some 2%nat) (-224) 0 (-224) 0 [].
Definition dcpA_gotu : YP09.region :=
  YP09.mkRegion None A_GOT_UAR (A_GOT_UAR + 8) 0 0 [YP09.mkChunk A_GOT_UAR (CVal 8 (SLit A_UAR_CELL))].
Definition dcpA_gots : YP09.region :=
  YP09.mkRegion None A_GOT_SHADOW (A_GOT_SHADOW + 8) 0 0 [YP09.mkChunk A_GOT_SHADOW (CVal 8 (SLit A_SHADOW_CELL))].
Definition dcpA_cells : YP09.region :=
  YP09.mkRegion None A_SHADOW_CELL (A_SHADOW_CELL + 8) 0 0 [YP09.mkChunk A_SHADOW_CELL (CVal 8 (SOff 32 0))].
Definition dcpA_cellu : YP09.region :=
  YP09.mkRegion None A_UAR_CELL (A_UAR_CELL + 4) 0 0 [YP09.mkChunk A_UAR_CELL (CVal 4 (SLit 1))].
Definition dcpA_facts : facts := mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) ] [] [].
Definition dcpA_ss : sstate :=
  mkSS A_DCSV sr_atoms [dcpA_stack; dcpA_gotu; dcpA_gots; dcpA_cells; dcpA_cellu] None dcpA_facts.
(* the real frame [R, R + 120) on atom 33 *)
Definition dcpA_real : YP09.region := YP09.mkRegion (Some 33%nat) 0 120 0 120 [].

Section ea. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma dcp_entryA : forall (W : world rsegs) regs memc R,
spZ regs mod 16 = 0 -> 2 ^ 46 <= spZ regs <= 2 ^ 47 ->
(forall a, spZ regs - 224 <= a < spZ regs -> apresent (w_H W) memc a) ->
rdword (aview rsegs (w_H W) memc) A_GOT_UAR = Some A_UAR_CELL ->
rdword (aview rsegs (w_H W) memc) A_GOT_SHADOW = Some A_SHADOW_CELL ->
rdword (aview rsegs (w_H W) memc) A_SHADOW_CELL = Some SHADOW_OFF ->
rd32 (aview rsegs (w_H W) memc) A_UAR_CELL 1 ->
st_ok rsegs (Ereg regs (dcp_extraA R)) dcpA_ss
  (restrict (w_H W) (mkst regs (Z_to_bv 64 A_DCSV) memc (seg_rom rsegs))).
Proof.
intros W regs memc R Hal Hsp Hpres Kgu Kgs Kcs Kcu.
rewrite restrict_mkst_fx.
set (E := Ereg regs (dcp_extraA R)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (subst E; exact (ew_Ereg_extra regs _ 0)).
unfold dcpA_ss. apply (entry_st_ok_full rsegs); change (Ereg regs (dcp_extraA R)) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold dcpA_stack, dcpA_gotu, dcpA_gots, dcpA_cells, dcpA_cellu.
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]];
  unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). apply Hpres. lia.
  + split; [unfold A_GOT_UAR; lia|]. split; [unfold A_GOT_UAR; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs E _ 0 A_GOT_UAR 8 (SLit A_UAR_CELL) A_UAR_CELL);
    [reflexivity | unfold A_UAR_CELL; lia | lia |]. exact (val_mem_of_rdword rsegs (w_H W) memc _ _ Kgu).
  + split; [unfold A_GOT_SHADOW; lia|]. split; [unfold A_GOT_SHADOW; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs E _ 0 A_GOT_SHADOW 8 (SLit A_SHADOW_CELL) A_SHADOW_CELL);
    [reflexivity | unfold A_SHADOW_CELL; lia | lia |]. exact (val_mem_of_rdword rsegs (w_H W) memc _ _ Kgs).
  + split; [unfold A_SHADOW_CELL; lia|]. split; [unfold A_SHADOW_CELL; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs E _ 0 A_SHADOW_CELL 8 (SOff 32 0) SHADOW_OFF);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; lia | lia |].
    exact (val_mem_of_rdword rsegs (w_H W) memc _ _ Kcs).
  + split; [unfold A_UAR_CELL; lia|]. split; [unfold A_UAR_CELL; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs E _ 0 A_UAR_CELL 4 (SLit 1) 1); [reflexivity | lia | lia |].
    exact (dcp_vm_rd32 (w_H W) memc _ _ Kcu).
- apply pairwise_disjoint_of_extents.
  unfold dcpA_stack, dcpA_gotu, dcpA_gots, dcpA_cells, dcpA_cellu, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp.
  unfold A_GOT_UAR, A_GOT_SHADOW, A_SHADOW_CELL, A_UAR_CELL.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]]. cbn [dcpA_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp. change (2 ^ 4) with 16. repeat split; lia.
Qed.
End ea.

(* `srli s4,t3,3` then `add s4,s4,a0` with a0 the shadow offset, as the engine writes it: the frame's shadow address *)
Lemma dcp_sh_denot : forall E (a b : nat) F, bv_unsigned (ew E a) = F -> bv_unsigned (ew E b) = SHADOW_OFF ->
0 <= F < 2 ^ 47 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff a 0) (SLit 3)) (SOff b 0)) = Z_to_bv 64 (shadow_addr F).
Proof.
intros E a b F Ha Hb HF.
assert (H8 : 0 <= F / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
apply bv_eq. unfold shadow_addr. rewrite (unsigned_lit_small (SHADOW_OFF + F / 8)) by (unfold SHADOW_OFF; lia).
change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff a 0) (SLit 3)) (SOff b 0))))
  with (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff a 0) (SLit 3)) (SOff b 0))).
rewrite !U_SAlu, !U_SOff, U_SLit, Ha, Hb. cbn [zalu_raw]. unfold zcanon, M64.
rewrite !Z.add_0_r. rewrite (Z.mod_small F) by lia. rewrite (Z.mod_small 3) by lia.
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (Z.mod_small (F / 8)) by lia. rewrite (Z.mod_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
rewrite Z.mod_small by (unfold SHADOW_OFF; lia). lia.
Qed.

(* ======================================== block B: from the frame call's return to the loop head ========================================
   env slot 32 = the shadow offset, 33 = shadow_addr F, 34 / 35 / 36 = buf / buflen / mask (the cells block A wrote);
   the real frame on s1's atom with those four cells, the frame's header and tmp[0 .. 8) on a0's atom (F), the
   frame's 16 shadow bytes on atom 33; the fact on a0's atom (F >= 4096, 32-aligned) decides `bnez a0`. *)
Definition dcp_extraB (shF buf n mask : Z) : list word := [w64 SHADOW_OFF; w64 shF; w64 buf; w64 n; w64 mask].
Definition dcpB_real : YP09.region := YP09.mkRegion (Some 9%nat) 0 120 0 120
  [YP09.mkChunk 8 (CVal 8 (SOff 34 0)); YP09.mkChunk 16 (CVal 8 (SOff 35 0));
   YP09.mkChunk 80 (CVal 8 (SOff 36 0)); YP09.mkChunk 88 (CVal 8 (SOff 32 0))].
Definition dcpB_frame : YP09.region := YP09.mkRegion (Some 10%nat) 0 40 0 40 [].
Definition dcpB_sh : YP09.region := YP09.mkRegion (Some 33%nat) 0 16 0 16 [].
Definition dcpB_facts : facts := mkFacts [ (10%nat, mkAF 4096 (2 ^ 47) 5) ] [] [].
Definition dcpB_ss : sstate := mkSS DC_RA_SM1 sr_atoms [dcpB_real; dcpB_frame; dcpB_sh] None dcpB_facts.
(* the literals the engine stores at the frame's 16 shadow bytes (li a3,-15 / a5,-14 / s9,-8 / a4,-13 and zero) *)
Definition dcp_shlits : list Z :=
  [2 ^ 64 - 15; 2 ^ 64 - 15; 2 ^ 64 - 15; 2 ^ 64 - 15; 0; 0; 0; 0;
   2 ^ 64 - 14; 2 ^ 64 - 14; 2 ^ 64 - 14; 2 ^ 64 - 14; 2 ^ 64 - 8; 2 ^ 64 - 8; 2 ^ 64 - 13; 2 ^ 64 - 13].

Lemma dcp_vm_mod : forall (m : word -> option byte) a v, val_mem rsegs m a 8 v -> val_mem rsegs m a 8 (v mod 2 ^ 64).
Proof.
intros m a v H k Hk. rewrite (H k Hk). f_equal. f_equal. unfold YO0f.le_byte.
change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Section eb. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma dcp_entryB : forall (W : world rsegs) regs2 mem2 R F buf n mask,
getr regs2 9 = w64 R -> getr regs2 10 = w64 F ->
alloc_ceiling <= R -> R + 120 <= 2 ^ 47 ->
4096 <= F -> F + 128 <= alloc_ceiling -> F mod 32 = 0 -> in_app F 128 ->
(forall a, R <= a < R + 120 -> apresent (w_H W) mem2 a) ->
(forall a, F <= a < F + 128 -> apresent (w_H W) mem2 a) ->
(forall a, shadow_addr F <= a < shadow_addr F + 16 -> apresent (w_H W) mem2 a) ->
val_mem rsegs (mrestrict (w_H W) mem2) (R + 8) 8 buf -> val_mem rsegs (mrestrict (w_H W) mem2) (R + 16) 8 n ->
val_mem rsegs (mrestrict (w_H W) mem2) (R + 80) 8 mask -> val_mem rsegs (mrestrict (w_H W) mem2) (R + 88) 8 SHADOW_OFF ->
st_ok rsegs (Ereg regs2 (dcp_extraB (shadow_addr F) buf n mask)) dcpB_ss
  (restrict (w_H W) (mkst regs2 (Z_to_bv 64 DC_RA_SM1) mem2 (seg_rom rsegs))).
Proof.
intros W regs2 mem2 R F buf n mask H9 H10 HRlo HRhi HF0 HFc HF32 HFapp PR PF PS V8 V16 V80 V88.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Ereg regs2 (dcp_extraB (shadow_addr F) buf n mask)).
assert (E9 : ew E 9 = w64 R) by (subst E; rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl); exact H9).
assert (E10 : ew E 10 = w64 F) by (subst E; rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = w64 SHADOW_OFF) by (subst E; exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = w64 (shadow_addr F)) by (subst E; exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = w64 buf) by (subst E; exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E 35 = w64 n) by (subst E; exact (ew_Ereg_extra regs2 _ 3)).
assert (E36 : ew E 36 = w64 mask) by (subst E; exact (ew_Ereg_extra regs2 _ 4)).
assert (Hsh : SHADOW_OFF <= shadow_addr F <= SHADOW_OFF + 2 ^ 44)
  by (unfold shadow_addr; pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia));
      assert (F / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia); change (2 ^ 47 / 8) with (2 ^ 44) in *; lia).
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = F) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = shadow_addr F) by (rewrite E33; apply unsigned_lit_small; unfold SHADOW_OFF in Hsh; lia).
assert (Hlit : forall (x : nat) v, ew E x = w64 v -> sv_denot E (SOff x 0) = Z_to_bv 64 (v mod 2 ^ 64)).
{ intros x v Hx. rewrite dcp_den0, Hx. unfold w64. symmetry. apply Z_to_bv_mod64. }
unfold dcpB_ss. apply (entry_st_ok_full rsegs); change (Ereg regs2 (dcp_extraB (shadow_addr F) buf n mask)) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold dcpB_real, dcpB_frame, dcpB_sh.
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
  unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U9. split; [lia|]. split; [lia|]. split.
    { intros o Ho. apply (apresent_writable rsegs). apply PR. lia. }
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val rsegs E _ R 8 8 (SOff 34 0) (buf mod 2 ^ 64)); [exact (Hlit 34%nat buf E34) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia | lia |].
      exact (dcp_vm_mod _ _ _ V8).
    * apply (chunk_ok_val rsegs E _ R 16 8 (SOff 35 0) (n mod 2 ^ 64)); [exact (Hlit 35%nat n E35) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia | lia |].
      exact (dcp_vm_mod _ _ _ V16).
    * apply (chunk_ok_val rsegs E _ R 80 8 (SOff 36 0) (mask mod 2 ^ 64)); [exact (Hlit 36%nat mask E36) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia | lia |].
      exact (dcp_vm_mod _ _ _ V80).
    * apply (chunk_ok_val rsegs E _ R 88 8 (SOff 32 0) (SHADOW_OFF mod 2 ^ 64)); [exact (Hlit 32%nat SHADOW_OFF E32) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia | lia |].
      exact (dcp_vm_mod _ _ _ V88).
  + rewrite U10. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). apply PF. lia.
  + rewrite U33. split; [unfold SHADOW_OFF in Hsh; lia|]. split; [unfold SHADOW_OFF in Hsh; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). apply PS. lia.
- apply pairwise_disjoint_of_extents.
  unfold dcpB_real, dcpB_frame, dcpB_sh, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U10, U33.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  pose proof (Z.div_mod F 8 ltac:(lia)) as HF8. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as HF8b.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, shadow_addr, SHADOW_OFF in *.
  repeat split; lia.
- split; [|split; [exact I | exact I]]. cbn [dcpB_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U10. change (2 ^ 5) with 32. repeat split; lia.
Qed.
End eb.

(* ======================================== the walk ======================================== *)
Ltac dcp_rs_eval :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end.
Ltac dcp_ss_eval HS :=
lazymatch type of HS with st_ok ?sg ?E ?ss ?ms => let ss' := eval vm_compute in ss in change (st_ok sg E ss' ms) in HS end.
(* every write window of a run's state lies in the zone Zn (rwt rewrites the base atoms' values in Hb and closes) *)
Ltac dcp_kwr rwt :=
let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rwt Hb | ]);
destruct Hr.
Ltac dcp_keep Zn KE rwt :=
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
let KS := fresh "KS" in
pose proof (dcp_kept_run Zn _ _ _ _ _ _ KE HFr) as KS;
lazymatch type of KS with ?P -> _ => let KW := fresh "KW" in assert (KW : P) by (dcp_kwr rwt); specialize (KS KW); clear KW end;
clear KE HFr; rename KS into KE end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* the same for a second zone over the same run, leaving the run's frame_of for dcp_keep *)
Ltac dcp_keep_only Zn KE rwt :=
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
let KS := fresh "KS" in
pose proof (dcp_kept_run Zn _ _ _ _ _ _ KE HFr) as KS;
lazymatch type of KS with ?P -> _ => let KW := fresh "KW" in assert (KW : P) by (dcp_kwr rwt); specialize (KS KW); clear KW end;
clear KE; rename KS into KE end.
Ltac dcp_srget := repeat match goal with |- context [sr_get ?l ?r] =>
  let x := eval vm_compute in (sr_get l r) in change (sr_get l r) with x end.
Ltac dcp_in := vm_compute; repeat (first [left; reflexivity | right]).
Lemma dcp_pres : forall regs regs2 (r : bv 5), aregs_preserved regs regs2 -> acallee_saved (bv_unsigned r) ->
  getr regs2 r = getr regs r.
Proof. intros regs regs2 r HP Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). exact (HP _ Hr). Qed.
(* a one-byte literal chunk of a region of a state, as the byte the reader sees *)
Lemma dcp_chunk_byte : forall {fx : YK11.FPState} E ss (H : word -> bool) ms i r off c,
st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r -> In (YP09.mkChunk off (CVal 1 (SLit c))) (r_chunks r) ->
aview rsegs H (ms_mem ms) (base_val E (r_base r) + off) = Some (bv_unsigned (byte_of_word (Z_to_bv 64 c) 0)).
Proof.
intros fx E ss H ms i r off c HS Hi Hc.
destruct (st_ok_chunk rsegs E ss (restrict H ms) i r _ HS Hi Hc 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
cbn [YP09.c_off YP09.c_val cbyte sv_denot] in Hb1, Hb2. injection Hb1 as <-.
unfold aview. rewrite Z.add_0_r in Hb2. cbn [ms_mem restrict] in Hb2. rewrite Hb2. reflexivity.
Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Lemma dcp_main : forall c : dcx, dc_pre B c ->
AR_laws rsegs B -> model_laws (as_universe B) -> stack_malloc_progressP B -> api_env rsegs B ->
astack_malloc_realizes rsegs B DC_CID -> pc_stack_malloc (as_code B) DC_CID = A_SM1 ->
as_got_shadow B = A_GOT_SHADOW -> as_shadow_cell B = A_SHADOW_CELL ->
as_got_uar B = A_GOT_UAR -> as_uar_cell B = A_UAR_CELL ->
rate_A_img_facts rsegs B ->
SRr rsegs (dx_W c) (cfg_at rsegs A_DCSV (dx_regs c) (dx_memc c) (dx_mdc c)) (dc_loop_cfg B c 0).
Proof.
intros c Hpre LAWS ML SMP AENV ASM Esm Egs Ecs Egu Ecu IMG.
pose proof Hpre as Hpre0.
destruct c as [STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs mask buf n].
unfold dc_pre, dx_S0 in Hpre.
cbn [dx_STK dx_sp0 dx_FP dx_ly dx_S dx_W0 dx_mem0 dx_md0 dx_own dx_k dx_lyc dx_Sc dx_W dx_memc dx_mdc
  dx_regs dx_mask dx_buf dx_n] in Hpre |- *.
destruct Hpre as ((HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev) & H10 & Hmask & H11 & H12 & Hn & Hbuf
  & Hcnt & Hfmt & Hcomma & Hempty & Hord & Hrom & Hfrm).
pose proof rts_wx as Hwx. pose proof rts_segs_low as Hsegs.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs0 & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Tv : T_dcsv_STK = 8432) by reflexivity. rewrite Tv in Hwlo.
assert (Hes : ESTACK = 4096) by reflexivity.
set (S0 := spZ regs) in *.
set (R := 32 * ((S0 - 224) / 32)).
assert (HR : R mod 32 = 0 /\ S0 - 240 <= R <= S0 - 224).
{ subst R. pose proof (Z.div_mod (S0 - 224) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (S0 - 224) 32 ltac:(lia)).
  pose proof (Z.div_mod S0 16 ltac:(lia)) as HS16. rewrite Hal16 in HS16.
  split; [rewrite Z.mul_comm; apply Z_mod_mult | lia]. }
destruct HR as (HR32 & HRlo & HRhi).
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcs & Kcu & Kgs & Kgu).
rewrite Ecs in Kcs, Kgs. rewrite Egs in Kgs. rewrite Ecu in Kcu, Kgu. rewrite Egu in Kgu.
pose proof (dcp_entryA W regs memc R Hal16 ltac:(lia) ltac:(intros a Ha; apply Hpres; lia) Kgu Kgs Kcs Kcu) as HS.
remember (Ereg regs (dcp_extraA R)) as E eqn:HE.
assert (B2 : bv_unsigned (ew E 2) = S0) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E33 : ew E 33 = w64 R) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (B33 : bv_unsigned (ew E 33) = R) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 SHADOW_OFF) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (EA : forall (r : bv 5) nn, Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs r)
  by (intros r nn Hrn; subst E; apply ew_Ereg_nat; exact Hrn).
clear HE.
set (WZ := fun a : Z => S0 - 8432 <= a < S0).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ WZ a -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
  by reflexivity.
unfold cfg_at. change (w64 A_DCSV) with (Z_to_bv 64 A_DCSV).
(* A1: the prologue to 0x840b8, right after `andi sp,sp,-32` *)
aj_run_to dc_tbl_ok HS HJ 0x840b8.
{ dcp_rs_eval.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (S0 - sp0)); [reflexivity | rewrite B2; lia | cbn; lia | cbn; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
dcp_keep WZ KE ltac:(fun H => rewrite ?B2 in H; unfold WZ; lia).
(* sp := atom 33 (R) *)
lazymatch type of HS with st_ok _ _ ?ss (restrict ?H ?ms) =>
  let e := eval vm_compute in (sr_get (ss_regs ss) 2%bv) in
  assert (R2 : getr (ms_regs (restrict H ms)) 2%bv = sv_denot E e)
    by exact (st_ok_reg rsegs E ss (restrict H ms) 2%bv HS);
  pose proof (st_ok_pin_sv rsegs E ss (restrict H ms) 2%bv (SOff 33 0) HS eq_refl) as HSp
end.
specialize (HSp ltac:(rewrite R2, (dcp_and_denot E 2 S0 B2 ltac:(lia)); exact (rts_den_atom E 33 R E33 ltac:(lia)))).
clear HS R2. rename HSp into HS.
(* the stack region cut to the 13 saves [S - 104, S); the real frame [R, R + 120) on atom 33 *)
lazymatch type of HS with st_ok _ _ ?ss ?msx =>
  let rs := eval vm_compute in (ss_mem ss) in
  pose proof (st_ok_relayout rsegs E ss msx
    [(0%nat, trim_lo (nth 0 rs dcpA_stack) (-104)); (1%nat, dcpA_gotu); (2%nat, dcpA_gots); (3%nat, dcpA_cells);
     (4%nat, dcpA_cellu)] HS ltac:(vm_compute; reflexivity)) as HSr
end.
clear HS. dcp_ss_eval HSr.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresA & _).
lazymatch type of HSr with st_ok _ _ ?ss ?msx =>
  assert (ROK : region_ok rsegs E (ms_mem msx) dcpA_real);
  [| assert (RDJ : all_disjoint E dcpA_real (ss_mem ss));
     [| pose proof (ast_ok_add_region rsegs E ss msx dcpA_real HSr eq_refl ROK RDJ) as HS ] ]
end.
{ unfold region_ok, dcpA_real. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
  rewrite B33. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable rsegs). apply HpresA. lia. }
{ apply all_disjoint_of_extents. unfold dcpA_real, extent_of_region. cbn [map ss_mem YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite B33, B2. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia. }
clear HSr ROK RDJ. dcp_ss_eval HS.
(* A2: to the frame call, `jal 0x3cf9c` at 0x840ec *)
aj_run dc_tbl_ok HS HJ.
{ dcp_rs_eval.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 33%nat (R - sp0)); [reflexivity | rewrite B33; lia | cbn; lia | cbn; lia |].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (S0 - sp0)); [reflexivity | rewrite B2; lia | cbn; lia | cbn; lia |].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
dcp_keep WZ KE ltac:(fun H => rewrite ?B2, ?B33 in H; unfold WZ; lia).
(* the state at the call: the registers, the four cells of the real frame, the 13 saves *)
lazymatch type of HS with st_ok _ _ ?ss _ =>
  let rs := eval vm_compute in (ss_mem ss) in
  let r0v := eval vm_compute in (nth 0 rs dcpA_stack) in
  let r1v := eval vm_compute in (nth 1 rs dcpA_stack) in
  assert (N0 : nth_error (ss_mem ss) 0 = Some r0v) by (vm_compute; reflexivity);
  assert (N1 : nth_error (ss_mem ss) 1 = Some r1v) by (vm_compute; reflexivity);
  set (r0 := r0v) in N0; set (r1 := r1v) in N1
end.
lazymatch type of HS with st_ok _ _ ?ss (restrict ?H ?msx) =>
  rename msx into msA;
  assert (RA : forall (r : bv 5), getr (ms_regs msA) r = sv_denot E (sr_get (ss_regs ss) r))
    by (intros r; exact (st_ok_restrict_reg rsegs H E ss msA r HS))
end.
assert (RA1 : getr (ms_regs msA) 1 = w64 DC_RA_SM1) by (rewrite RA; dcp_srget; reflexivity).
assert (RA2 : getr (ms_regs msA) 2 = w64 R) by (rewrite RA; dcp_srget; rewrite dcp_den0; exact E33).
assert (RA3 : getr (ms_regs msA) 3 = w64 (as_gp B)) by (rewrite RA; dcp_srget; rewrite dcp_den0, (EA 3%bv 3%nat eq_refl); exact Hgp).
assert (RA4 : getr (ms_regs msA) 4 = w64 (as_tp B)) by (rewrite RA; dcp_srget; rewrite dcp_den0, (EA 4%bv 4%nat eq_refl); exact Htp).
assert (RA8 : getr (ms_regs msA) 8 = w64 S0)
  by (rewrite RA; dcp_srget; rewrite dcp_den0, (EA 2%bv 2%nat eq_refl); unfold S0, spZ, w64; symmetry; apply Z_to_bv_bv_unsigned).
assert (RA9 : getr (ms_regs msA) 9 = w64 R) by (rewrite RA; dcp_srget; rewrite dcp_den0; exact E33).
assert (HspA : spZ (ms_regs msA) = R) by (unfold spZ; rewrite RA2; apply unsigned_lit_small; lia).
(* the cells of the real frame and the saves, at the call *)
assert (VA : forall off v (val : Z), In (YP09.mkChunk off (CVal 8 v)) (YP09.r_chunks r0) ->
  bv_unsigned (sv_denot E v) mod 2 ^ (8 * Z.of_N 8) = val mod 2 ^ (8 * Z.of_N 8) ->
  val_mem rsegs (mrestrict (w_H W) (ms_mem msA)) (R + off) 8 val).
{ intros off v val Hin Hv. pose proof (dcp_chunk_vm E _ _ 0 _ off 8 v val HS N0 Hin Hv) as V.
  unfold r0 in V. cbn [YP09.r_base base_val ms_mem restrict] in V. rewrite B33 in V. exact V. }
assert (VA8 : val_mem rsegs (mrestrict (w_H W) (ms_mem msA)) (R + 8) 8 buf).
{ apply (VA 8 (SOff 11 0)); [dcp_in|]. rewrite dcp_den0, (EA 11%bv 11%nat eq_refl), H11. apply dcp_w64_mod. }
assert (VA16 : val_mem rsegs (mrestrict (w_H W) (ms_mem msA)) (R + 16) 8 n).
{ apply (VA 16 (SOff 12 0)); [dcp_in|]. rewrite dcp_den0, (EA 12%bv 12%nat eq_refl), H12. apply dcp_w64_mod. }
assert (VA80 : val_mem rsegs (mrestrict (w_H W) (ms_mem msA)) (R + 80) 8 mask).
{ apply (VA 80 (SOff 10 0)); [dcp_in|]. rewrite dcp_den0, (EA 10%bv 10%nat eq_refl), H10. apply dcp_w64_mod. }
assert (VA88 : val_mem rsegs (mrestrict (w_H W) (ms_mem msA)) (R + 88) 8 SHADOW_OFF).
{ apply (VA 88 (SOff 32 0)); [dcp_in|]. rewrite dcp_den0, E32. apply dcp_w64_mod. }
assert (VSA : forall j, (j < 13)%nat -> val_mem rsegs (mrestrict (w_H W) (ms_mem msA)) (S0 - 8 - 8 * Z.of_nat j) 8
  (bv_unsigned (getr regs (nth j dc_saved 0%bv)))).
{ intros j Hj.
  assert (Hc : In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat (bv_unsigned (nth j dc_saved 0%bv))) 0)))
    (YP09.r_chunks r1)).
  { do 13 (destruct j as [|j]; [dcp_in |]). lia. }
  pose proof (dcp_chunk_vm E _ _ 1 _ _ 8 _ (bv_unsigned (getr regs (nth j dc_saved 0%bv))) HS N1 Hc) as V.
  unfold r1 in V. cbn [YP09.r_base base_val ms_mem restrict] in V. rewrite B2 in V.
  replace (S0 - 8 - 8 * Z.of_nat j) with (S0 + (-8 - 8 * Z.of_nat j)) by lia. apply V.
  pose proof (bv_unsigned_in_range _ (nth j dc_saved 0%bv)) as Hjr.
  rewrite dcp_den0, (EA (nth j dc_saved 0%bv) _ ltac:(rewrite Z2Nat.id; [reflexivity | lia])). reflexivity. }
clear VA N0 N1.
(* the frame call: __asan_stack_malloc_1(128), ra = 0x840f0 *)
assert (HR16 : R mod 16 = 0) by (unfold R; replace (32 * ((S0 - 224) / 32)) with ((2 * ((S0 - 224) / 32)) * 16) by ring; apply Z_mod_mult).
rewrite (st_ok_restrict_mkst rsegs (w_H W) E _ msA HS eq_refl).
eapply SRr_bind.
{ eapply (dcp_sm B LAWS AENV ML SMP ASM Esm W (ms_regs msA) (ms_mem msA) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k
    (R - sp0) (w64 DC_RA_SM1) HJ).
  - lia.
  - rewrite Zminus_mod, HR16, Hsp0al. reflexivity.
  - lia.
  - rewrite Hes. lia.
  - exact RA3.
  - exact RA4.
  - exact RA1.
  - vm_compute. reflexivity.
  - exact Hcnt. }
cbv beta. intros W2 c2 Hw2 (-> & S2 & regs2 & mem2 & md2 & pos & f & -> & HJ2 & HP & Ha0 & Hsame & ES2 & Hpos & Hfrs2
  & Hnin & Hz & Hflag & Hfpres & Hfr).
(* ---- the state the call returns ---- *)
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _ & _ & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (Hin2 : In (DC_CID, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds rsegs B LAWS lyc S2 W mem2 md2 DC_CID pos HAR2 Hin2) as (HF4096 & HFceil & HFapp).
destruct (al_frames _ _ LAWS lyc S2 W mem2 md2 DC_CID pos HAR2 Hin2) as (HF32 & _ & HFb & HFsh).
change (fs_frame_bytes DC_CID) with 128 in HFceil, HFapp, HFb, HFsh, Hz, Hflag, Hfpres.
change (128 / 8) with 16 in HFsh.
set (F := frame_addr lyc DC_CID pos) in *.
set (shF := shadow_addr F) in *.
assert (HRc : alloc_ceiling <= R) by lia.
(* the stack of the caller's window outside the call's ESTACK is kept by the call *)
assert (KC : forall a, sp0 - STK <= a < sp0 -> ~ (R - 4096 <= a < R) ->
  aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) (ms_mem msA) a).
{ intros a Ha Hne. apply Hfr; [lia | | | rewrite Hes; lia].
  - apply (al_stack _ _ LAWS lyc Sc W memc mdc a HAR). rewrite Eslo, Eshi. lia.
  - apply (al_stack _ _ LAWS lyc S2 W mem2 md2 a HAR2). rewrite Eslo, Eshi. lia. }
assert (KV : forall a (nb : nat) v, sp0 - STK <= a -> a + Z.of_nat nb <= sp0 -> R <= a ->
  val_mem rsegs (mrestrict (w_H W) (ms_mem msA)) a nb v -> val_mem rsegs (mrestrict (w_H W) mem2) a nb v).
{ intros a nb v H1 H2 H3 Hv. apply (rts_val_kept (w_H W) (ms_mem msA) mem2 a nb v); [|exact Hv].
  intros kk Hk. apply KC; lia. }
assert (V2_8 := KV (R + 8) 8%nat buf ltac:(lia) ltac:(cbn; lia) ltac:(lia) VA8).
assert (V2_16 := KV (R + 16) 8%nat n ltac:(lia) ltac:(cbn; lia) ltac:(lia) VA16).
assert (V2_80 := KV (R + 80) 8%nat mask ltac:(lia) ltac:(cbn; lia) ltac:(lia) VA80).
assert (V2_88 := KV (R + 88) 8%nat SHADOW_OFF ltac:(lia) ltac:(cbn; lia) ltac:(lia) VA88).
assert (VS2 : forall j, (j < 13)%nat -> val_mem rsegs (mrestrict (w_H W) mem2) (S0 - 8 - 8 * Z.of_nat j) 8
  (bv_unsigned (getr regs (nth j dc_saved 0%bv)))).
{ intros j Hj. apply KV; [lia | cbn; lia | lia | exact (VSA j Hj)]. }
clear KV VA8 VA16 VA80 VA88 VSA.
(* every byte outside the window and not owned at the call is as at the call *)
set (WZB := fun a : Z => WZ a \/ aowned B lyc Sc a).
assert (KE2 : forall a, 0 <= a < 2 ^ 64 -> ~ WZB a -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a).
{ intros a Ha Hz2. rewrite (Hfr a Ha).
  - apply KE; [exact Ha|]. intros X. apply Hz2. left. exact X.
  - intros X. apply Hz2. right. exact X.
  - intros X. apply Hz2. right. rewrite ES2 in X.
    exact (dcp_aowned_back B lyc Sc f DC_CID pos a ltac:(rewrite <- ES2; exact Hfrs2) X).
  - intros X. apply Hz2. left. unfold WZ. rewrite Hes in X. lia. }
clear KE.
(* the frame and its shadow bytes were the runtime's at the call *)
assert (OWF : forall a, F <= a < F + 128 -> aowned B lyc Sc a).
{ intros a Ha. apply (own_free_frame B lyc Sc _ DC_CID pos a (proj1 HAR) ltac:(unfold DC_CID; lia) Hpos Hnin). exact Ha. }
assert (OWS : forall a, shF <= a < shF + 16 -> aowned B lyc Sc a).
{ intros a Ha. apply (own_free_frame_shadow B lyc Sc _ DC_CID pos a (proj1 HAR) ltac:(unfold DC_CID; lia) Hpos Hnin). exact Ha. }
(* ---- block B ---- *)
assert (P9 : getr regs2 9 = w64 R) by (rewrite (dcp_pres _ _ 9%bv HP ltac:(cbv; lia)); exact RA9).
clear HS RA.
pose proof (dcp_entryB W regs2 mem2 R F buf n mask P9 Ha0 HRc ltac:(lia) HF4096 HFceil HF32 HFapp
  ltac:(intros a Ha; apply Hpres2; lia) ltac:(intros a Ha; exact (proj1 (HFb a Ha)))
  ltac:(intros a Ha; replace a with (shF + (a - shF)) by lia; exact (proj1 (HFsh (a - shF) ltac:(lia))))
  V2_8 V2_16 V2_80 V2_88) as HS.
fold shF in HS.
remember (Ereg regs2 (dcp_extraB shF buf n mask)) as E2 eqn:HE2.
assert (U9 : bv_unsigned (ew E2 9) = R) by (subst E2; rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl), P9; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E2 10) = F) by (subst E2; rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl), Ha0; apply unsigned_lit_small; lia).
assert (Hsh : SHADOW_OFF <= shF <= SHADOW_OFF + 2 ^ 44)
  by (unfold shF, shadow_addr; pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia));
      assert (F / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia); change (2 ^ 47 / 8) with (2 ^ 44) in *; lia).
assert (U33 : bv_unsigned (ew E2 33) = shF) by (subst E2; rewrite (ew_Ereg_extra regs2 _ 1); apply unsigned_lit_small; unfold SHADOW_OFF in Hsh; lia).
assert (E2_32 : ew E2 32 = w64 SHADOW_OFF) by (subst E2; exact (ew_Ereg_extra regs2 _ 0)).
assert (E2A : forall (r : bv 5) nn, Z.of_nat nn = bv_unsigned r -> ew E2 nn = getr regs2 r)
  by (intros r nn Hrn; subst E2; apply ew_Ereg_nat; exact Hrn).
assert (E2_34 : ew E2 34 = w64 buf) by (subst E2; exact (ew_Ereg_extra regs2 _ 2)).
assert (E2_35 : ew E2 35 = w64 n) by (subst E2; exact (ew_Ereg_extra regs2 _ 3)).
assert (E2_36 : ew E2 36 = w64 mask) by (subst E2; exact (ew_Ereg_extra regs2 _ 4)).
assert (E2_33 : ew E2 33 = w64 shF) by (subst E2; exact (ew_Ereg_extra regs2 _ 1)).
clear HE2.
(* block B's own write windows: the bytes outside them are as the call left them *)
set (ZB := fun a : Z => (R <= a < R + 120) \/ (F <= a < F + 40) \/ (shF <= a < shF + 16)).
assert (KSB : forall a, 0 <= a < 2 ^ 64 -> ~ ZB a -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) mem2 a)
  by reflexivity.
change (w64 DC_RA_SM1) with (Z_to_bv 64 DC_RA_SM1).
(* B1: to 0x8418c, right after `add s4,s4,a0` *)
aj_run_to dc_tbl_ok HS HJ2 0x8418c.
{ dcp_rs_eval.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0)); [reflexivity | rewrite U9; lia | cbn; lia | cbn; lia |].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat F); [reflexivity | exact U10 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists DC_CID, pos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes DC_CID) with 128. fold F. lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat shF); [reflexivity | exact U33 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists DC_CID, pos. split; [left; reflexivity|].
    right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes DC_CID / 8) with 16. fold F. fold shF. lia. }
  apply awr_ok_nil. }
dcp_keep_only ZB KSB ltac:(fun H => rewrite ?U9, ?U10, ?U33 in H; unfold ZB; lia).
dcp_keep WZB KE2 ltac:(fun H => rewrite ?U9, ?U10, ?U33 in H;
  first [left; unfold WZ; lia | right; apply OWF; lia | right; apply OWS; lia]).
(* s4 := atom 33 (shadow_addr F) *)
lazymatch type of HS with st_ok _ _ ?ss (restrict ?H ?ms) =>
  let e := eval vm_compute in (sr_get (ss_regs ss) 20%bv) in
  assert (R20 : getr (ms_regs (restrict H ms)) 20%bv = sv_denot E2 e)
    by exact (st_ok_reg rsegs E2 ss (restrict H ms) 20%bv HS);
  pose proof (st_ok_pin_sv rsegs E2 ss (restrict H ms) 20%bv (SOff 33 0) HS eq_refl) as HSp
end.
specialize (HSp ltac:(rewrite R20, (dcp_sh_denot E2 10 32 F U10 ltac:(rewrite E2_32; apply unsigned_lit_small; unfold SHADOW_OFF; lia) ltac:(lia));
  rewrite dcp_den0; apply bv_eq; rewrite U33; symmetry; apply unsigned_lit_small; unfold SHADOW_OFF in Hsh; lia)).
clear HS R20. rename HSp into HS. dcp_ss_eval HS.
(* B2: the frame's shadow bytes and the loop registers, to the loop head 0x8420c *)
aj_run_to dc_tbl_ok HS HJ2 DC_LOOP.
{ dcp_rs_eval.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0)); [reflexivity | rewrite U9; lia | cbn; lia | cbn; lia |].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat F); [reflexivity | exact U10 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists DC_CID, pos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes DC_CID) with 128. fold F. lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat shF); [reflexivity | exact U33 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists DC_CID, pos. split; [left; reflexivity|].
    right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes DC_CID / 8) with 16. fold F. fold shF. lia. }
  apply awr_ok_nil. }
dcp_keep_only ZB KSB ltac:(fun H => rewrite ?U9, ?U10, ?U33 in H; unfold ZB; lia).
dcp_keep WZB KE2 ltac:(fun H => rewrite ?U9, ?U10, ?U33 in H;
  first [left; unfold WZ; lia | right; apply OWF; lia | right; apply OWS; lia]).
(* ---- the loop head: the cut ---- *)
lazymatch type of HS with st_ok _ _ ?ss (restrict ?H ?msx) =>
  rename msx into msB;
  assert (RB : forall (r : bv 5), getr (ms_regs msB) r = sv_denot E2 (sr_get (ss_regs ss) r))
    by (intros r; exact (st_ok_restrict_reg rsegs H E2 ss msB r HS));
  let rs := eval vm_compute in (ss_mem ss) in
  let q0 := eval vm_compute in (nth 0 rs dcpB_real) in
  let q1 := eval vm_compute in (nth 1 rs dcpB_real) in
  let q2 := eval vm_compute in (nth 2 rs dcpB_real) in
  assert (M0 : nth_error (ss_mem ss) 0 = Some q0) by (vm_compute; reflexivity);
  assert (M1 : nth_error (ss_mem ss) 1 = Some q1) by (vm_compute; reflexivity);
  assert (M2 : nth_error (ss_mem ss) 2 = Some q2) by (vm_compute; reflexivity);
  set (b0 := q0) in M0; set (b1 := q1) in M1; set (b2 := q2) in M2
end.
pose proof HJ2 as (HARf & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
assert (VB : forall off v (val : Z), In (YP09.mkChunk off (CVal 8 v)) (YP09.r_chunks b0) ->
  bv_unsigned (sv_denot E2 v) mod 2 ^ (8 * Z.of_N 8) = val mod 2 ^ (8 * Z.of_N 8) ->
  val_mem rsegs (mrestrict (w_H W) (ms_mem msB)) (R + off) 8 val).
{ intros off v val Hin Hv. pose proof (dcp_chunk_vm E2 _ _ 0 _ off 8 v val HS M0 Hin Hv) as V.
  unfold b0 in V. cbn [YP09.r_base base_val ms_mem restrict] in V. rewrite U9 in V. exact V. }
assert (SB : forall a, 0 <= a < 2 ^ 64 -> ~ ZB a -> aview rsegs (w_H W) (ms_mem msB) a = aview rsegs (w_H W) mem2 a)
  by exact KSB.
assert (Hlit : forall c, bv_unsigned (sv_denot E2 (SLit c)) mod 2 ^ (8 * Z.of_N 8) = c mod 2 ^ (8 * Z.of_N 8))
  by (intros cc; apply dcp_w64_mod).
assert (Hatm : forall (x : nat) v, ew E2 x = w64 v -> bv_unsigned (sv_denot E2 (SOff x 0)) mod 2 ^ (8 * Z.of_N 8) = v mod 2 ^ (8 * Z.of_N 8))
  by (intros x v Hx; rewrite dcp_den0, Hx; apply dcp_w64_mod).
assert (E2_10 : ew E2 10 = w64 F) by (rewrite (E2A 10%bv 10%nat eq_refl); exact Ha0).
clear KSB.
rewrite (st_ok_restrict_mkst rsegs (w_H W) E2 _ msB HS eq_refl).
apply SRr_ret. unfold dc_loop_cfg.
exists fx, pos, S2, (ms_regs msB), (ms_mem msB). eexists. split; [reflexivity|].
unfold dc_loop, dc_core, dx_R, dx_S0.
cbn [dx_STK dx_sp0 dx_FP dx_ly dx_S dx_W0 dx_mem0 dx_md0 dx_own dx_k dx_lyc dx_Sc dx_W dx_memc dx_mdc
  dx_regs dx_mask dx_buf dx_n].
cbv zeta. change (spZ regs) with S0. change (32 * ((S0 - 224) / 32)) with R.
change (frame_addr lyc DC_CID pos) with F. change (shadow_addr F) with shF. rewrite Tv.
change (RateCsv.csv_prefix mask 0) with (@nil Z). cbn [length app Z.of_nat].
assert (Eab : ablocks B lyc S2 = ablocks B lyc Sc) by (rewrite ES2; reflexivity).
split.
{ (* dc_core *)
split; [lia|].
split; [split; [intros; reflexivity | exact Hfrm]|].
split; [exact HJ2|].
split; [exact Hfrs2|]. split; [exact Hnin|]. split; [exists f; exact ES2|]. split; [exact Hpos|].
split; [exact Eab|].
split; [rewrite ES2; reflexivity|]. split; [rewrite ES2; reflexivity|]. split; [rewrite ES2; reflexivity|].
split.
{ eapply same_io_trans; [| apply same_io_wvb].
  eapply same_io_trans; [| apply same_io_materialized; exact Hsame].
  eapply same_io_trans; apply same_io_wvb. }
split; [apply wle_refl|].
split; [exact HR32|]. split; [lia|].
(* the registers *)
split; [rewrite RB; dcp_srget; rewrite dcp_den0, (E2A 2%bv 2%nat eq_refl), (dcp_pres _ _ 2%bv HP ltac:(cbv; lia)); exact RA2|].
split; [rewrite RB; dcp_srget; rewrite dcp_den0, (E2A 3%bv 3%nat eq_refl), (dcp_pres _ _ 3%bv HP ltac:(cbv; lia)); exact RA3|].
split; [rewrite RB; dcp_srget; rewrite dcp_den0, (E2A 4%bv 4%nat eq_refl), (dcp_pres _ _ 4%bv HP ltac:(cbv; lia)); exact RA4|].
split; [rewrite RB; dcp_srget; rewrite dcp_den0, (E2A 8%bv 8%nat eq_refl), (dcp_pres _ _ 8%bv HP ltac:(cbv; lia)); exact RA8|].
split; [rewrite RB; dcp_srget; rewrite dcp_den0, (E2A 9%bv 9%nat eq_refl); exact P9|].
split; [rewrite RB; dcp_srget; rewrite dcp_den0; exact E2_33|].
split; [rewrite RB; dcp_srget; reflexivity|].
(* the cells of the real frame *)
split; [apply (VB 8 (SOff 34 0)); [dcp_in | exact (Hatm 34%nat buf E2_34)]|].
split; [apply (VB 16 (SOff 35 0)); [dcp_in | exact (Hatm 35%nat n E2_35)]|].
split; [apply (VB 24 (SOff 10 0)); [dcp_in | exact (Hatm 10%nat F E2_10)]|].
split; [apply (VB 32 (SOff 10 0)); [dcp_in | exact (Hatm 10%nat F E2_10)]|].
split; [apply (VB 40 (SOff 10 32)); [dcp_in | rewrite denot_SOff, U10; unfold zcanon, M64; apply Z.mod_mod; lia]|].
split; [apply (VB 48 (SLit SNP_COMMA)); [dcp_in | apply Hlit]|].
split; [apply (VB 56 (SLit 48000)); [dcp_in | apply Hlit]|].
split; [apply (VB 64 (SLit SNP_FMT)); [dcp_in | apply Hlit]|].
split; [apply (VB 72 (SLit SNP_EMPTY)); [dcp_in | apply Hlit]|].
split; [apply (VB 80 (SOff 36 0)); [dcp_in | exact (Hatm 36%nat mask E2_36)]|].
split; [apply (VB 88 (SOff 32 0)); [dcp_in | exact (Hatm 32%nat SHADOW_OFF E2_32)]|].
split; [apply (VB 112 (SOff 10 0)); [dcp_in | exact (Hatm 10%nat F E2_10)]|].
(* the 13 saves *)
assert (HshB : shF + 16 <= alloc_ceiling) by (unfold SHADOW_OFF in Hsh; lia).
assert (HFsep : F + 128 <= shF \/ shF + 16 <= F).
{ pose proof (Z.div_mod F 8 ltac:(lia)) as HF8. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as HF8b.
  unfold shF, shadow_addr. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia. }
split.
{ intros j Hj. apply (rts_val_kept (w_H W) mem2 (ms_mem msB) _ 8 _); [|exact (VS2 j Hj)].
  intros kk Hk. change (Z.of_nat 8) with 8 in Hk. apply SB; [lia|]. unfold ZB. lia. }
(* the frame's flag pointer, tmp, its shadow bytes, its presence *)
split.
{ change DC_FSZ with 128. rewrite <- Hflag. apply rdword_ext. intros kk Hk. apply SB; [lia|]. unfold ZB. lia. }
split.
{ intros j Hj. cbn [length] in Hj. assert (j = 0%nat) as -> by lia. cbn [nth]. split; [|lia].
  pose proof (dcp_chunk_vm E2 _ _ 1 _ 32 1 (SLit 0) 0 HS M1 ltac:(dcp_in) ltac:(vm_compute; reflexivity)) as V.
  unfold b1 in V. cbn [YP09.r_base base_val ms_mem restrict] in V. rewrite U10 in V.
  change (Z.of_nat 0) with 0. rewrite Z.add_0_r. exact V. }
split.
{ intros i Hi. change (shadow_addr F) with shF. change (Z.of_nat (length dc_shA)) with 16 in Hi.
  replace i with (Z.of_nat (Z.to_nat i)) by lia.
  assert (Hj : (Z.to_nat i < 16)%nat) by lia. generalize dependent (Z.to_nat i). intros j Hj. clear i Hi.
  assert (Hc : In (YP09.mkChunk (Z.of_nat j) (CVal 1 (SLit (nth j dcp_shlits 0)))) (YP09.r_chunks b2)).
  { do 16 (destruct j as [|j]; [dcp_in |]). lia. }
  pose proof (dcp_chunk_byte E2 _ (w_H W) msB 2 _ _ _ HS M2 Hc) as X.
  unfold b2 in X. cbn [YP09.r_base base_val] in X. rewrite U33 in X. rewrite X. f_equal. rewrite Nat2Z.id.
  do 16 (destruct j as [|j]; [vm_compute; reflexivity |]). lia. }
destruct (al_frames _ _ LAWS lyc S2 W (ms_mem msB) _ DC_CID pos HARf Hin2) as (_ & _ & HFbf & HFshf).
change (fs_frame_bytes DC_CID) with 128 in HFbf, HFshf. change (128 / 8) with 16 in HFshf.
split; [intros a Ha; change DC_FSZ with 128 in Ha; exact (proj1 (HFbf a Ha))|].
split.
{ intros a Ha. change (DC_FSZ / 8) with 16 in Ha. replace a with (shF + (a - shF)) by lia.
  exact (proj1 (HFshf (a - shF) ltac:(lia))). }
(* the image facts: their bytes are no owned static, so the kept conjunct keeps them, and dc_img_carry rebuilds
   the four facts at the journal's AR state *)
assert (KEf : forall a, 0 <= a < 2 ^ 64 -> ~ (S0 - T_dcsv_STK <= a < S0) -> ~ aowned B lyc Sc a ->
  aview rsegs (w_H W) (ms_mem msB) a = aview rsegs (w_H W) memc a).
{ intros a Ha Hw Ho. apply KE2; [exact Ha|]. intros [X|X]; [apply Hw; unfold WZ in X; lia | exact (Ho X)]. }
destruct (dc_img_carry B LAWS IMG _ lyc S2 W (ms_mem msB) _ Hpre0 HARf KEf) as (I1 & I2 & I3 & I4).
split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. split; [exact I4|].
split.
{ intros a Hro Hos Her. pose proof Hro as (sg & Hsg & _ & Hsr). assert (Hia : in_img rsegs a) by (exists sg; split; [exact Hsg | lia]).
  pose proof (Hsegs a Hia) as Hal.
  rewrite (KE2 a ltac:(lia)); [exact (Hrom a Hro Hos Her)|].
  intros [X|X]; [unfold WZ in X; lia|].
  exact (Hos (proj1 (al_owned_image _ _ LAWS lyc Sc W memc mdc a HAR Hia) X)). }
split.
{ intros Hn0. destruct (Hbuf Hn0) as (Hb0 & Hbn & (m & Hinm & _ & Hnm) & _).
  rewrite <- Eab in Hinm. pose proof (req_size_pos m ltac:(lia)) as Hrq.
  split; [exact (range_addressable_of_block rsegs B LAWS lyc S2 W (ms_mem msB) _ buf m buf n HARf Hinm ltac:(lia) ltac:(lia))|].
  split; [exact (shadow_hull_vis_of_block rsegs B LAWS lyc S2 W (ms_mem msB) _ buf m buf n HARf Hinm ltac:(lia) ltac:(lia) Hn0)|].
  intros a Ha. destruct (al_blocks _ _ LAWS lyc S2 W (ms_mem msB) _ buf m HARf Hinm) as (_ & _ & _ & _ & Hpb & _).
  exact (proj1 (Hpb a ltac:(lia))). }
intros a Ha Hw Ho. apply KE2; [exact Ha|]. intros [X|X]; [apply Hw; unfold WZ in X; lia | exact (Ho X)]. }
(* the loop registers *)
split; [lia|].
split.
{ rewrite RB; dcp_srget. apply bv_eq. rewrite denot_SOff, U10. unfold w64. rewrite unsigned_lit_small by lia.
  unfold zcanon, M64. apply Z.mod_small. lia. }
split; [rewrite RB; dcp_srget; reflexivity|].
split; [rewrite RB; dcp_srget; reflexivity|].
split; [rewrite RB; dcp_srget; apply bv_eq; vm_compute; reflexivity|].
split; [rewrite RB; dcp_srget; apply bv_eq; vm_compute; reflexivity|].
split; [rewrite RB; dcp_srget; apply bv_eq; vm_compute; reflexivity|].
rewrite RB; dcp_srget; apply bv_eq; vm_compute; reflexivity.
Qed.
End w.

(* ======================================== PART 1 ======================================== *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis RT : dc_rt B MT.
Theorem dc_pro : dc_pro_stmt B.
Proof using RT.
unfold dc_pro_stmt. intros c Hpre.
destruct RT as (LAWS & ML & SMP & _ & _ & AENV & _ & _ & IMG & ASM & _ & _ & _ & Esm & Egs & Ecs & Egu & Ecu).
exact (dcp_main B c Hpre LAWS ML SMP AENV (ASM fx) Esm Egs Ecs Egu Ecu IMG).
Qed.
End b.

Print Assumptions dc_pro.

