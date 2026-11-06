(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the contract of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACfn.v:33-69
   (tfib_lib_pre_x, tfib_lib_post_x, tfib_lib_contract_x) restated for libreac/fuzz_identity's ASan+UBSan
   build: the module paths are this unit's lib.B, the image is the position-abstract one (pa_segs,
   BASE + AF_LLVMFuzzerTestOneInput of identb_listing), the library shape and every constant of the unit's
   relocated core are parameters of the Section, and the measured needs of this build's entry (events, live
   bytes, stack) are stated beside it. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput.v; 2146 of its 2207 lines of code are new or changed and 166 lines of the source are left out. *)
(* Segment G of LLVMFuzzerTestOneInput's ASan+UBSan walk (image B): +0x1128 .. +0x11c4 (0x8189c .. 0x81938).
   seg_G of lib/B/Prog/LLVMFuzzerTestOneInput_inv.v: from inv_F_end (the slot of the first buf_of call) to
   inv_G_end. Pieces g_p1 .. g_p7 walk +0x1128 .. +0x11b4 (the two heap buffers, their formatters, check_str and
   free); g_stores (LLVMFuzzerTestOneInput_seg_G_hand_stores.v) walks the four stores +0x11b4 .. +0x11c4. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo IdentBlkTail YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_seg_G_hand2_stmt LLVMFuzzerTestOneInput_seg_G_hand_stores.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require
buf_of check_str reac_identity_fw_str reac_identity_reac_ver_str.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import WrapRo.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_identity_fw_str_c reac_identity_reac_ver_str_c.
Import ListNotations.
(* reac_box_name_seg_*.v set lia's euclidean-division flag to false for every file that loads reac_box_name
   (through the contract); this file was proved with it on, so it turns it back on. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The contract's Section, in its order (LLVMFuzzerTestOneInput.v). *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Hypothesis HLIVE : LIVE_LLVMF <= LIVE_LIB.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis PSIG : identb_prog_sig_ok (PI := PI).
Hypothesis MTL : ameter_laws MT.
Hypothesis HMT0 : forall s s' : astate, mo_le MT s s' 0.
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis HUMF : forall c, In c (LLVMF_FREE_CTX RA_LLVMF) ->
In (firstn kUnwindMax (pc_free_ra0 (as_code B)
:: flat_map (fun r => if r =? pc_free_ra0 (as_code B) then [] else [r]) c)) (as_universe B).
Hypothesis HCHK : check_str.tcheck_str_spec B.
Hypothesis HFWS : reac_identity_fw_str.treac_identity_fw_str_spec B.
Hypothesis HVS : reac_identity_reac_ver_str.treac_identity_reac_ver_str_spec B.
Hypothesis HBUF : buf_of.tbuf_of_spec B MT (CTX_BUF_OF RA_LLVMF).
Local Notation ACUT := (@acut fx rc SK PI B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
Local Notation ECOMMON := (@ecommon rc PI B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
Local Notation E_PRE := (@e_pre rc PI B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
Local Notation INV_F := (@inv_F_end fx rc SK PI B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
Local Notation INV_G := (@inv_G_end fx rc SK PI B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Let RUN := paj_run B LAWS.

(* ---- the bytes a call must keep -------------------------------------------------------------------- *)
(* The bytes the walk's facts read: the machine frame and the stack above it, the side-stack frame and its
   shadow, and the input block. *)
Definition g_zone (g : ectx) (pos mf a : Z) : Prop :=
  (mf <= a < 2 ^ 64) \/ (SFa g pos <= a < SFa g pos + 1024) \/
  (shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128) \/ (e_p g <= a < e_p g + e_n g).
Definition g_kept (g : ectx) (pos mf : Z) (W : world SEGS) (m : word -> option byte)
  (W2 : world SEGS) (m2 : word -> option byte) : Prop :=
  forall a, g_zone g pos mf a -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W) m a.
Lemma g_garr8_kept : forall (W W2 : world SEGS) m m2 a l,
  (forall j, 0 <= j < Z.of_nat (length l) -> aview SEGS (w_H W2) m2 (a + j) = aview SEGS (w_H W) m (a + j)) ->
  garr8 SEGS (rd W m) a l -> garr8 SEGS (rd W2 m2) a l.
Proof.
intros W W2 m m2 a l HK HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
eapply val_mem_kept; [|exact Hv].
intros k Hk. cbn in Hk. assert (k = 0) by lia. subst k. rewrite Z.add_0_r. apply HK. lia.
Qed.
Lemma g_zero_kept : forall (W W2 : world SEGS) m m2 a n,
  (forall i, 0 <= i < n / 8 -> aview SEGS (w_H W2) m2 (shadow_addr a + i) = aview SEGS (w_H W) m (shadow_addr a + i)) ->
  zero_shadow (aview SEGS (w_H W) m) SHADOW_OFF a n -> zero_shadow (aview SEGS (w_H W2) m2) SHADOW_OFF a n.
Proof.
intros W W2 m m2 a n HK HZ i Hi. unfold zero_shadow, shadow_of_addr in *. specialize (HK i Hi).
unfold shadow_addr in HK. rewrite HK. exact (HZ i Hi).
Qed.
Lemma g_blk_kept : forall (W W2 : world SEGS) m m2 a n,
  (forall i, 0 <= i < (n + 7) / 8 -> aview SEGS (w_H W2) m2 (shadow_addr a + i) = aview SEGS (w_H W) m (shadow_addr a + i)) ->
  block_shadow (aview SEGS (w_H W) m) SHADOW_OFF a n -> block_shadow (aview SEGS (w_H W2) m2) SHADOW_OFF a n.
Proof.
intros W W2 m m2 a n HK (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
intros i Hi. specialize (HK i Hi). unfold shadow_addr in HK. unfold shadow_of_addr in *. rewrite HK. exact (H3 i Hi).
Qed.
Lemma g_le1 : forall b, 0 <= b < 256 -> YO0f.le_byte b 1 0 = b.
Proof.
intros b Hb. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
change (2 ^ 8) with 256. rewrite Z.shiftr_0_r, (Z.mod_small b 256) by lia. apply Z.mod_small; lia.
Qed.
Lemma g_le20 : forall b0 b1, 0 <= b0 < 256 -> 0 <= b1 < 256 -> YO0f.le_byte (b0 + 256 * b1) 2 0 = b0.
Proof.
intros b0 b1 H0 H1. unfold YO0f.le_byte. change (8 * Z.of_nat 2) with 16. change (8 * Z.of_nat 0) with 0.
change (2 ^ 16) with 65536. rewrite Z.shiftr_0_r, (Z.mod_small _ 65536) by lia.
replace (b0 + 256 * b1) with (b0 + b1 * 256) by lia. rewrite Z_mod_plus_full. apply Z.mod_small; lia.
Qed.
Lemma g_le21 : forall b0 b1, 0 <= b0 < 256 -> 0 <= b1 < 256 -> YO0f.le_byte (b0 + 256 * b1) 2 1 = b1.
Proof.
intros b0 b1 H0 H1. unfold YO0f.le_byte. change (8 * Z.of_nat 2) with 16. change (8 * Z.of_nat 1) with 8.
change (2 ^ 16) with 65536. rewrite (Z.mod_small _ 65536) by lia. rewrite Z.shiftr_div_pow2 by lia.
change (2 ^ 8) with 256. replace (b0 + 256 * b1) with (b1 * 256 + b0) by lia.
rewrite Z.div_add_l by lia. rewrite (Z.div_small b0 256) by lia. rewrite Z.add_0_r. apply Z.mod_small; lia.
Qed.
Lemma g_vm2 : forall (W : world SEGS) m a l,
  garr8 SEGS (rd W m) a l -> (2 <= length l)%nat ->
  val_mem SEGS (rd W m) a 2 (nth 0 l 0 + 256 * nth 1 l 0).
Proof.
intros W m a l HG Hlen.
destruct (HG 0%nat ltac:(lia)) as (V0 & R0). destruct (HG 1%nat ltac:(lia)) as (V1 & R1).
intros k Hk. assert (k = 0 \/ k = 1)%nat as [-> | ->] by lia.
- specialize (V0 0%nat ltac:(lia)). rewrite (g_le20 _ _ R0 R1). rewrite (g_le1 _ R0) in V0.
  replace (a + Z.of_nat 0) with (a + Z.of_nat 0 + Z.of_nat 0) by (cbn; lia). exact V0.
- specialize (V1 0%nat ltac:(lia)). rewrite (g_le21 _ _ R0 R1). rewrite (g_le1 _ R1) in V1.
  replace (a + Z.of_nat 1) with (a + Z.of_nat 1 + Z.of_nat 0) by (cbn; lia). exact V1.
Qed.
Lemma g_vm_kept : forall g pos mf (W : world SEGS) m (W2 : world SEGS) m2 a n v,
  g_kept g pos mf W m W2 m2 -> (forall k, 0 <= k < Z.of_nat n -> g_zone g pos mf (a + k)) ->
  val_mem SEGS (rd W m) a n v -> val_mem SEGS (rd W2 m2) a n v.
Proof. intros g pos mf W m W2 m2 a n v HK HZ Hv. eapply val_mem_kept; [|exact Hv]. intros k Hk. apply HK, HZ, Hk. Qed.
Lemma g_pres_reg : forall (regs regs2 : bvmap 5 word) (r : bv 5),
  aregs_preserved regs regs2 -> reg_in r CLOB = false -> getr regs2 r = getr regs r.
Proof. intros regs regs2 r HP Hr. exact (regs_preserved_frame regs regs2 HP r Hr). Qed.
Lemma g_fs4 : fs_frame_bytes 4 = 1024.
Proof. reflexivity. Qed.
(* The registers the walk's facts name: ecommon's sp, gp, tp, s0, s1 and the tail values in s5 .. s11. *)
Definition G_REGS : list (bv 5) := [2; 3; 4; 8; 9; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition g_regs_eq (regs regs2 : bvmap 5 word) : Prop :=
  forall r : bv 5, In r G_REGS -> getr regs2 r = getr regs r.
Ltac ginr := cbn [G_REGS In]; repeat (first [left; reflexivity | right]).
Lemma g_regs_eq_of_st_ok : forall E ss (ms : machine_state) (H : word -> bool) regs extra,
  st_ok SEGS E ss (restrict H ms) -> env_agree 32 (Ereg regs extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) G_REGS = true ->
  g_regs_eq regs (ms_regs ms).
Proof.
intros E ss ms H regs extra HS HA Hf r Hr.
exact (regs_kept_of_st_ok SEGS E ss (restrict H ms) regs extra G_REGS HS HA Hf r Hr).
Qed.
Lemma g_mod16 : forall x, x mod 32 = 0 -> x mod 16 = 0.
Proof.
intros x H. pose proof (Z.div_mod x 32 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D.
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z.mod_mul. lia.
Qed.
Lemma g_regs_eq_pres : forall regs regs2, aregs_preserved regs regs2 -> g_regs_eq regs regs2.
Proof.
intros regs regs2 HP r Hr. apply (g_pres_reg regs regs2 r HP).
repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr.
Qed.
Lemma g_regs_eq_trans : forall r1 r2 r3, g_regs_eq r1 r2 -> g_regs_eq r2 r3 -> g_regs_eq r1 r3.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.
Lemma g_kept_trans : forall g pos mf (W1 W2 W3 : world SEGS) m1 m2 m3,
  g_kept g pos mf W1 m1 W2 m2 -> g_kept g pos mf W2 m2 W3 m3 -> g_kept g pos mf W1 m1 W3 m3.
Proof. intros g pos mf W1 W2 W3 m1 m2 m3 H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.
Lemma g_sh_off : forall F x, F mod 8 = 0 -> x mod 8 = 0 -> shadow_addr (F + x) = shadow_addr F + x / 8.
Proof.
intros F x HF Hx. unfold shadow_addr.
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. pose proof (Z.div_mod x 8 ltac:(lia)) as DX.
rewrite HF in DF. rewrite Hx in DX.
assert (E1 : (F + x) / 8 = F / 8 + x / 8).
{ replace (F + x) with ((F / 8 + x / 8) * 8) by lia. apply Z.div_mul. lia. }
lia.
Qed.

(* The facts every boundary of the segment gives about the stack and the frame. *)
Lemma g_facts : forall g pos mf k ly S W regs mem md,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly S W mem md k ->
  frames S = [(4, pos)] -> ECOMMON g pos mf ly S W regs mem md ->
  spZ regs = mf /\ alloc_ceiling + LLVMF_STK <= e_sp0 g /\ e_sp0 g <= 2 ^ 47 /\ e_sp0 g mod 16 = 0 /\
  e_sp0 g - 336 <= mf <= e_sp0 g - 320 /\ mf mod 32 = 0 /\
  4096 <= SFa g pos /\ SFa g pos + 1024 <= alloc_ceiling /\ SFa g pos mod 32 = 0 /\
  frame_addr ly 4 pos = SFa g pos.
Proof.
intros g pos mf k ly S W regs mem md HJ Hfr HC.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
destruct HC as (R2 & _ & _ & Hmf & Hmf32 & _).
pose proof asan_consts as (C1 & _).
assert (Hin : In (4, pos) (frames S)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S W mem md 4 pos HAR Hin) as (F1 & F2 & _).
destruct (al_frames _ _ LAWS ly S W mem md 4 pos HAR Hin) as (F3 & _).
assert (EF : frame_addr ly 4 pos = SFa g pos).
{ unfold SFa, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
rewrite g_fs4 in F2. rewrite EF in F1, F2, F3.
assert (Hsp : spZ regs = mf).
{ unfold spZ. rewrite R2. unfold w64. apply unsigned_lit_small. clear - Hmf Hceil Hslo H47 Hshi Hstk0 HSTK C1.
  unfold STK_LLVMF, ASTACK in *. lia. }
split; [exact Hsp|]. split; [clear - Hceil Hslo; lia|]. split; [clear - Hshi H47; lia|].
split; [exact Hal16|]. split; [exact Hmf|]. split; [exact Hmf32|].
split; [exact F1|]. split; [exact F2|]. split; [exact F3 | exact EF].
Qed.

(* ecommon at a later state: the registers it names are callee-saved, its bytes are in the zone, e_pre speaks of
   g alone, and the fds / fs come from the later journal. *)
Lemma g_ec_kept : forall g pos mf ly S W regs mem md ly2 S2 W2 regs2 mem2 md2 k2,
  ECOMMON g pos mf ly S W regs mem md ->
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem2 md2 k2 ->
  g_regs_eq regs regs2 -> g_kept g pos mf W mem W2 mem2 ->
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2.
Proof.
intros g pos mf ly S W regs mem md ly2 S2 W2 regs2 mem2 md2 k2 HC HJ2 HP HK.
destruct HC as (R2 & R9 & R8 & Hmf & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 & V24 & V32 & V40 &
  V48 & V56 & V64b & V72 & V80 & V88 & V96 & V104 & Vfl & HPRE & Hfds & Hfs & Hin).
pose proof HPRE as HPRE'.
destruct HPRE' as ((_ & _ & _ & _ & _ & Hstk & _) & _ & _ & _ & _ & Hlen & _).
pose proof Hstk as (_ & _ & _ & _ & Hshi & H47 & _).
fold (e_sp0 g) in Hshi.
assert (Hsp : e_sp0 g <= 2 ^ 47) by (clear - Hshi H47; lia).
assert (ZM : forall a, mf <= a < 2 ^ 64 -> g_zone g pos mf a) by (intros a Ha; left; exact Ha).
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as (Efd & Efs).
split; [rewrite (HP 2%bv ltac:(ginr)); exact R2|].
split; [rewrite (HP 9%bv ltac:(ginr)); exact R9|].
split; [rewrite (HP 8%bv ltac:(ginr)); exact R8|].
split; [exact Hmf|]. split; [exact Hmf32|].
split; [rewrite (HP 3%bv ltac:(ginr)); exact Rgp|].
split; [rewrite (HP 4%bv ltac:(ginr)); exact Rtp|].
do 4 (split; [eapply (g_vm_kept g pos mf W mem W2 mem2); [exact HK | intros k0 Hk0; apply ZM; cbn in Hk0;
  clear - Hk0 Hmf Hsp; lia | eassumption]|]).
do 13 (split; [eapply (g_vm_kept g pos mf W mem W2 mem2); [exact HK | intros k0 Hk0; apply ZM; cbn in Hk0;
  clear - Hk0 Hmf Hsp; lia | eassumption]|]).
split; [eapply (g_vm_kept g pos mf W mem W2 mem2); [exact HK | intros k0 Hk0; right; left; cbn in Hk0;
  clear - Hk0; lia | exact Vfl]|].
split; [exact HPRE|].
split; [intros fd; rewrite Efd; reflexivity|].
split; [exact Efs|].
unfold bytes_at8 in *. eapply g_garr8_kept; [|exact Hin].
intros j Hj. apply HK. right; right; right. rewrite length_map in Hj. clear - Hj Hlen. lia.
Qed.

(* ---- the budget at a boundary ----------------------------------------------------------------------- *)
Lemma g_live : forall g ly S hs, hblocks B g ly S hs -> blocks_bytes S = bsum hs + blocks_bytes (e_S g).
Proof.
intros g ly S hs (HP & _).
rewrite (blocks_bytes_bsum B (e_ly g) (e_S g)), (blocks_bytes_bsum B ly S).
rewrite (bsum_perm _ _ HP), bsum_app. reflexivity.
Qed.
Lemma g_epre_bud : forall g, E_PRE g ->
  st_nev (e_S g) + EV_LIB <= EV_MAX /\ blocks_bytes (e_S g) + LIVE_LIB <= LIVE_MAX /\
  (0 < e_n g -> In (e_p g, e_n g) (ablocks B (e_ly g) (e_S g))) /\
  arodata_okS SEGS B RLO RHI (aview SEGS (w_H (e_W g)) (e_mem g)).
Proof.
intros g HPRE.
destruct HPRE as (_ & _ & _ & _ & Hblk & _ & _ & _ & Hnev & Hlive & Hro & _).
split; [exact Hnev|]. split; [exact Hlive|]. split; [|exact Hro].
intros Hn. destruct Hblk as [(H0 & _) | (_ & Hin)]; [lia | exact Hin].
Qed.
Lemma g_inp : forall g ly S hs, hblocks B g ly S hs -> E_PRE g -> 0 < e_n g ->
  In (e_p g, e_n g) (ablocks B ly S).
Proof.
intros g ly S hs (HP & _) HPRE Hn. destruct (g_epre_bud g HPRE) as (_ & _ & Hin & _).
apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact (Hin Hn).
Qed.
Lemma g_nev : forall g pos (k : Z) ly S (W : world SEGS) mem md,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly S W mem md k ->
  st_nev S <= st_nev (e_S g) + k.
Proof. intros g pos k ly S W mem md (_ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
(* The read-only image at a later state, for the callees that read it (check_str's strlen). *)
Lemma g_aro : forall g pos (k : Z) ly S (W : world SEGS) mem md,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly S W mem md k ->
  E_PRE g -> aro_unowned SEGS B (aview SEGS (w_H W) mem).
Proof.
intros g pos k ly S W mem md HJ HPRE. destruct (g_epre_bud g HPRE) as (_ & _ & _ & Hro).
eapply (aro_unowned_of_arodata SEGS pa_relro_lo pa_relro_hi).
exact (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ (HRO _ Hro)).
Qed.
Lemma g_mev_pos : 0 <= MEV MT.
Proof.
unfold MEV. pose proof (mo_malloc_nonneg MT MTL 256 ltac:(lia)). pose proof (mo_free_nonneg MT MTL). lia.
Qed.
Lemma g_malloc_mev : forall n, 0 <= n <= 256 -> mo_malloc MT n <= MEV MT.
Proof.
intros n Hn. unfold MEV. pose proof (mo_malloc_mono MT MTL n 256 Hn). pose proof (mo_free_nonneg MT MTL). lia.
Qed.
Lemma g_free_mev : mo_free MT <= MEV MT.
Proof. unfold MEV. pose proof (mo_malloc_nonneg MT MTL 256 ltac:(lia)). lia. Qed.

(* ---- the facts the segment carries from call to call ------------------------------------------------- *)
Definition g_CG (g : ectx) (pos mf : Z) (W2 : world SEGS) (regs2 : bvmap 5 word) (mem2 : word -> option byte)
  : Prop :=
  id_at g pos (m_nrec g) W2 mem2 /\ mf_id3 g pos mf W2 mem2 /\ mf_id g pos mf W2 mem2 /\ sh_reg g pos regs2 /\
  getr regs2 22 = w64 (SlotModel.t_cap_ver (e_pl g)) /\ getr regs2 26 = w64 (SlotModel.t_cap_name (e_pl g)) /\
  getr regs2 21 = w64 (SlotModel.t_cap_tok (e_pl g)) /\ getr regs2 27 = w64 (SlotModel.t_fam_raw (e_pl g)) /\
  getr regs2 24 = w64 (SlotModel.t_any_fw (e_pl g)) /\ getr regs2 25 = w64 (SFa g pos + V_ef) /\
  val_mem SEGS (rd W2 mem2) (mf + 176) 8 (SlotModel.t_in (e_pl g)) /\
  val_mem SEGS (rd W2 mem2) (mf + 160) 8 (SlotModel.t_out (e_pl g)) /\
  val_mem SEGS (rd W2 mem2) (mf + 120) 8 (SlotModel.t_cap_disp (e_pl g)) /\
  val_mem SEGS (rd W2 mem2) (mf + 112) 8 (SlotModel.t_row (e_pl g)).
Lemma g_mid_len : forall g i, length (m_id g i) = 38%nat.
Proof. intros g i. unfold m_id. rewrite SlotModel.rec_id_length. reflexivity. Qed.
Lemma g_cg_kept : forall g pos mf (W W2 : world SEGS) regs regs2 mem mem2,
  g_CG g pos mf W regs mem -> g_regs_eq regs regs2 -> g_kept g pos mf W mem W2 mem2 ->
  SFa g pos mod 8 = 0 -> 0 <= mf -> mf + 256 <= 2 ^ 64 ->
  g_CG g pos mf W2 regs2 mem2.
Proof.
intros g pos mf W W2 regs regs2 mem mem2
  ((HIb & HIs & HIk) & HB & HD & HR23 & R22 & R26 & R21 & R27 & R24 & R25 & V176 & V160 & V120 & V112) HR HK H8 H0 H64.
assert (ZM : forall a, mf <= a < 2 ^ 64 -> g_zone g pos mf a) by (intros a Ha; left; exact Ha).
split; [split; [|split]|].
{ unfold bytes_at8 in *. eapply g_garr8_kept; [|exact HIb]. intros j Hj. apply HK. right; left.
  rewrite length_map, g_mid_len in Hj. unfold V_id. clear - Hj. cbn in Hj. lia. }
{ eapply g_zero_kept; [|exact HIs]. intros i Hi. apply HK. right; right; left.
  unfold N_id in Hi. unfold V_id. rewrite (g_sh_off (SFa g pos) 352 H8 eq_refl). clear - Hi. cbn in Hi |- *. lia. }
{ eapply g_blk_kept; [|exact HIk]. intros i Hi. apply HK. right; right; left.
  unfold N_id in Hi. unfold V_id. rewrite (g_sh_off (SFa g pos) 352 H8 eq_refl). clear - Hi. cbn in Hi |- *. lia. }
unfold mf_id3, mf_id, sh_reg in *.
split; [eapply (g_vm_kept g pos mf W mem W2 mem2); [exact HK | intros k Hk; apply ZM; cbn in Hk; clear - Hk H0 H64; lia
  | exact HB]|].
split; [eapply (g_vm_kept g pos mf W mem W2 mem2); [exact HK | intros k Hk; apply ZM; cbn in Hk; clear - Hk H0 H64; lia
  | exact HD]|].
split; [rewrite (HR 23%bv ltac:(ginr)); exact HR23|].
split; [rewrite (HR 22%bv ltac:(ginr)); exact R22|].
split; [rewrite (HR 26%bv ltac:(ginr)); exact R26|].
split; [rewrite (HR 21%bv ltac:(ginr)); exact R21|].
split; [rewrite (HR 27%bv ltac:(ginr)); exact R27|].
split; [rewrite (HR 24%bv ltac:(ginr)); exact R24|].
split; [rewrite (HR 25%bv ltac:(ginr)); exact R25|].
do 3 (split; [eapply (g_vm_kept g pos mf W mem W2 mem2); [exact HK | intros k Hk; apply ZM; cbn in Hk;
  clear - Hk H0 H64; lia | eassumption]|]).
eapply (g_vm_kept g pos mf W mem W2 mem2); [exact HK | intros k Hk; apply ZM; cbn in Hk; clear - Hk H0 H64; lia
  | exact V112].
Qed.

(* What a call keeps, from the three forms a callee's post gives (its own journal, IdentBCJ.tcj_kept,
   YCbq.acall_kept): the zone, when the bytes the call may change lie in a heap block other than the input. *)
Lemma g_kept_gen : forall g pos mf lo lyc Sc (W : world SEGS) memc mdc (W2 : world SEGS) mem2 (E : Z -> Prop),
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (lo <= a < mf) -> ~ E a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) ->
  (forall i, 0 < e_n g -> 0 <= i < e_n g -> ~ E (e_p g + i) ->
     aview SEGS (w_H W2) mem2 (e_p g + i) = aview SEGS (w_H W) memc (e_p g + i)) ->
  (forall a, (in_zr a (frame_rng lyc (4, pos)) \/ in_zr a (shadow_addr (frame_addr lyc 4 pos), fs_frame_bytes 4 / 8)) ->
     ~ E a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) ->
  AR SEGS B lyc Sc W memc mdc -> In (4, pos) (frames Sc) -> frame_addr lyc 4 pos = SFa g pos ->
  alloc_ceiling <= lo <= mf ->
  (forall a, E a -> exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= a < b + req_size m /\ (0 < e_n g -> b <> e_p g)) ->
  (0 < e_n g -> In (e_p g, e_n g) (ablocks B lyc Sc)) ->
  g_kept g pos mf W memc W2 mem2.
Proof.
intros g pos mf lo lyc Sc W memc mdc W2 mem2 E H1 H2 H3 HAR Hfin EF Hlo HE Hpin a Hz.
assert (NF : forall x, (in_zr x (frame_rng lyc (4, pos)) \/
  in_zr x (shadow_addr (frame_addr lyc 4 pos), fs_frame_bytes 4 / 8)) -> ~ E x).
{ intros x Hx He. destruct (HE x He) as (b & m & Hb & Hr & _).
  apply (block_not_frame_zone SEGS B LAWS lyc Sc W memc mdc b m (x - b) 4 pos HAR Hb Hfin); [lia|].
  replace (b + (x - b)) with x by lia. exact Hx. }
destruct Hz as [Hz | [Hz | [Hz | Hz]]].
- apply H1; [lia | lia |]. intros He. destruct (HE a He) as (b & m & Hb & Hr & _).
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & _ & Hbc & _). lia.
- assert (Hx : in_zr a (frame_rng lyc (4, pos))) by (unfold in_zr, frame_rng; cbn [fst snd]; rewrite EF, g_fs4; lia).
  apply H3; [left; exact Hx | apply NF; left; exact Hx].
- assert (Hx : in_zr a (shadow_addr (frame_addr lyc 4 pos), fs_frame_bytes 4 / 8))
    by (unfold in_zr; cbn [fst snd]; rewrite EF, g_fs4; cbn; lia).
  apply H3; [right; exact Hx | apply NF; right; exact Hx].
- assert (Hn : 0 < e_n g) by lia. replace a with (e_p g + (a - e_p g)) by lia.
  apply H2; [exact Hn | lia |]. intros He. destruct (HE _ He) as (b & m & Hb & Hr & Hne).
  specialize (Hne Hn). pose proof (Hpin Hn) as Hp.
  assert (Hd : (b, m) <> (e_p g, e_n g)) by (intros Eq; injection Eq as Eb _; exact (Hne Eb)).
  pose proof (sep_blocks SEGS B LAWS lyc Sc W memc mdc b m (e_p g) (e_n g) HAR Hb Hp Hd) as Hz2.
  unfold zdisjoint in Hz2. cbn [fst snd] in Hz2. unfold req_size in Hz2 at 2.
  rewrite (proj2 (Z.eqb_neq (e_n g) 0)) in Hz2 by lia. lia.
Qed.
Lemma g_kept_subj : forall g pos mf STK1 FP1 lyc Sc (W : world SEGS) memc mdc ly2 S2 (W2 : world SEGS) mem2 md2 k1,
  ajournal SEGS B STK1 mf FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
  AR SEGS B lyc Sc W memc mdc -> In (4, pos) (frames Sc) -> frame_addr lyc 4 pos = SFa g pos ->
  alloc_ceiling <= mf - STK1 <= mf ->
  (forall a, inFP FP1 a -> exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= a < b + req_size m /\
     (0 < e_n g -> b <> e_p g)) ->
  (0 < e_n g -> In (e_p g, e_n g) (ablocks B lyc Sc) /\ In (e_p g, e_n g) (ablocks B ly2 S2)) ->
  g_kept g pos mf W memc W2 mem2.
Proof.
intros g pos mf STK1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 HJ HAR Hfin EF Hlo HE Hpin.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & _ & F4 & _).
apply (g_kept_gen g pos mf (mf - STK1) lyc Sc W memc mdc W2 mem2 (inFP FP1)); try assumption.
- intros a Ha Hw _. exact (F1 a Ha Hw).
- intros i Hn Hi Hf. destruct (Hpin Hn) as (P1 & P2). apply (F2 _ _ i P1 P2); [|exact Hf].
  unfold req_size. rewrite (proj2 (Z.eqb_neq (e_n g) 0)) by lia. exact Hi.
- intros a Ha Hf. exact (F4 4 pos a Hfin Ha Hf).
- intros Hn. exact (proj1 (Hpin Hn)).
Qed.
Lemma g_kept_tcj : forall g pos mf STK1 lyc Sc (W : world SEGS) memc mdc (W2 : world SEGS) mem2 (E : Z -> Prop),
  tcj_kept B STK1 lyc Sc W memc W2 mem2 mf E ->
  AR SEGS B lyc Sc W memc mdc -> In (4, pos) (frames Sc) -> frame_addr lyc 4 pos = SFa g pos ->
  alloc_ceiling <= mf - STK1 <= mf ->
  (forall a, E a -> exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= a < b + req_size m /\ (0 < e_n g -> b <> e_p g)) ->
  (0 < e_n g -> In (e_p g, e_n g) (ablocks B lyc Sc)) ->
  g_kept g pos mf W memc W2 mem2.
Proof.
intros g pos mf STK1 lyc Sc W memc mdc W2 mem2 E (T1 & T2 & _ & T4 & _) HAR Hfin EF Hlo HE Hpin.
apply (g_kept_gen g pos mf (mf - STK1) lyc Sc W memc mdc W2 mem2 E); try assumption.
- intros i Hn Hi Hf. apply (T2 _ _ i (Hpin Hn)); [|exact Hf].
  unfold req_size. rewrite (proj2 (Z.eqb_neq (e_n g) 0)) by lia. exact Hi.
- intros a Ha Hf. exact (T4 4 pos a Hfin Ha Hf).
Qed.
Lemma g_kept_ack : forall g pos mf lo lyc Sc (W : world SEGS) memc mdc (W2 : world SEGS) mem2 (E : Z -> Prop),
  acall_kept SEGS B lyc Sc W memc W2 mem2 lo mf E ->
  AR SEGS B lyc Sc W memc mdc -> In (4, pos) (frames Sc) -> frame_addr lyc 4 pos = SFa g pos ->
  alloc_ceiling <= lo <= mf ->
  (forall a, E a -> exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= a < b + req_size m /\ (0 < e_n g -> b <> e_p g)) ->
  (0 < e_n g -> In (e_p g, e_n g) (ablocks B lyc Sc)) ->
  g_kept g pos mf W memc W2 mem2.
Proof.
intros g pos mf lo lyc Sc W memc mdc W2 mem2 E (A1 & A2 & _ & A4 & _) HAR Hfin EF Hlo HE Hpin.
apply (g_kept_gen g pos mf lo lyc Sc W memc mdc W2 mem2 E); try assumption.
- intros a Ha Hw _. exact (A1 a Ha Hw).
- intros i Hn Hi Hf. apply (A2 _ _ i (Hpin Hn)); [|exact Hf].
  unfold req_size. rewrite (proj2 (Z.eqb_neq (e_n g) 0)) by lia. exact Hi.
- intros a Ha Hf. exact (A4 4 pos a Hfin Ha Hf).
Qed.

(* The call chain at a call the entry makes with sp = mf: the entry's own record when the stack has room above
   sp0 for it, else none (the unwinder stops at once). *)
Lemma g_chain : forall g pos mf k ly S (W : world SEGS) regs mem md,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly S W mem md k ->
  ECOMMON g pos mf ly S W regs mem md ->
  exists ch, achain ly (aview SEGS (w_H W) mem) mf (e_sp0 g) ch /\
    (ch = [(e_sp0 g, RA_LLVMF, s0Z (e_regs g))] \/ ch = []).
Proof.
intros g pos mf k ly S W regs mem md HJ HC.
destruct HC as (_ & _ & _ & Hmf & _ & _ & _ & _ & _ & _ & _ & Vra & Vs0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & HPRE & _).
destruct HPRE as ((_ & _ & Hra4 & _ & _ & Hstk & _ & Hch & _) & Hra & _).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
pose proof HJ as (_ & Hly & _).
assert (Etop : ly_top ly = ly_top (e_ly g)) by (destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
fold (e_sp0 g) in *.
pose proof asan_consts as (C1 & _).
assert (Hal8 : e_sp0 g mod 8 = 0).
{ pose proof (Z.div_mod (e_sp0 g) 16 ltac:(lia)) as D. rewrite Hal16, Z.add_0_r in D. rewrite D.
  replace (16 * (e_sp0 g / 16)) with ((2 * (e_sp0 g / 16)) * 8) by lia. apply Z_mod_mult. }
destruct (Z_lt_ge_dec (e_sp0 g) (ly_top (e_ly g) - 16)) as [Hlt | Hge].
- exists [(e_sp0 g, RA_LLVMF, s0Z (e_regs g))]. split; [|left; reflexivity].
  apply (achain_ly_top (e_ly g)); [exact Etop|].
  apply (achain_push (e_ly g) (aview SEGS (w_H (e_W g)) (e_mem g)) _ (e_sp0 g) (s0Z (e_regs g)) RA_LLVMF [] mf Hch);
    [clear - H47 Htop2; lia | | | | | clear - Hceil Hslo HSTK0; lia | exact Hal8 | exact Hlt
    | clear - Hmf; lia].
  + intros a Ha. exact (aview_above_of_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a Ha).
  + apply rdword_of_val_mem; [exact Vra|]. rewrite <- Hra. unfold raZ. apply bv_unsigned_in_range.
  + apply rdword_of_val_mem; [exact Vs0|]. unfold s0Z. apply bv_unsigned_in_range.
  + rewrite <- Hra. exact Hra4.
- exists []. split; [|right; reflexivity]. left. split; [right; left; rewrite Etop; clear - Hge; lia | reflexivity].
Qed.
(* ---- piece 1: buf_of (cap_fw) at +0x1128 ------------------------------------------------------------ *)
Lemma g_p1 : forall g pos mf W c, INV_F g pos mf W c ->
  SRr SEGS W c (fun W3 c3 => exists res,
    ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 1) (BASE + 0x112c)
      (fun ly2 S2 W2 regs2 mem2 md2 =>
         g_CG g pos mf W2 regs2 mem2 /\
         hblocks B g ly2 S2 [(res, Z.max (SlotModel.t_cap_fw (e_pl g)) 1)] /\
         4096 <= res /\ getr regs2 10 = w64 res /\
         getr regs2 18 = w64 (SlotModel.t_cap_fw (e_pl g))) W3 c3).
Proof.
intros g pos mf W c (ly & S & regs & mem & md & -> & HJ & Hfr & Hk & MLE & MOK & HC & HP).
destruct HP as (HIa & HWa & HBL & HD3 & HDid & HR23 & R25 & R10 & R18 & R22 & R26 & R21 & R27 & R24 &
  V176 & V160 & V120 & V112).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (pa_base_lo (PL := PL_identb)) as HBLO. pose proof asan_consts as (C1 & _).
pose proof HC as HC0. pose proof (proj1 HJ) as HAR.
destruct (g_facts g pos mf _ ly S W regs mem md HJ Hfr HC) as
  (Hsp & Hceil & Hsp47 & Hsp16 & Hmf & Hmf32 & HF4096 & HFceil & HF32 & EF).
assert (HSTKv : STK_LLVMF = 16736) by reflexivity.
assert (HBOv : buf_of.BUF_OF_STK = 16400) by reflexivity.
assert (Hmf0 : 0 <= mf) by (clear - Hmf Hceil C1 HSTK HSTKv; lia).
assert (Hmf64 : mf + 256 <= 2 ^ 64) by (clear - Hmf Hsp47; lia).
assert (HmfS : alloc_ceiling <= mf - buf_of.BUF_OF_STK <= mf) by (clear - Hmf Hceil C1 HSTK HSTKv HBOv; lia).
destruct HC as (_ & _ & _ & _ & _ & Rgp & Rtp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & HPRE & _).
destruct (g_epre_bud g HPRE) as (Hnev0 & Hlive0 & Hin0 & _).
assert (HEVv : EV_LLVMF = 266) by reflexivity.
assert (HLv : LIVE_LLVMF = 511) by reflexivity.
assert (Hcap : 0 <= SlotModel.t_cap_fw (e_pl g) < 16)
  by (unfold SlotModel.t_cap_fw; apply Z.mod_pos_bound; lia).
assert (Hk265 : 4 * Z.of_nat (m_nrec g) + 1 <= EV_LLVMF) by (clear - Hk HEVv; lia).
(* the run: the call instruction at +0x1128 *)
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HS : st_ok_pi SEGS VAL E (mkSS 0x1128 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x1128)) mem (seg_rom SEGS)))).
{ subst E. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full;
  [apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | exact I
  | split; [cbn [atoms_ok f_atoms]; exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS buf_of.Bx_BO [] E (mrestrict (w_H W) mem)) by constructor.
clear HE.
unfold cfg_at. change (w64 (BASE + 0x1128)) with (Z_to_bv 64 (BASE + 0x1128)).
paj_run_tok RUN HS HJ SHOK buf_of.Bspan_BO; [awr_ok_tac |].
(* the state at the callee's entry *)
assert (Emem : forall x : word, ms_mem ms x = mem x) by (intros x; apply HF; intros (r & [] & _)).
assert (Hview : forall a, aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
  by (intros a; apply aview_eq_of; unfold mrestrict; rewrite Emem; reflexivity).
assert (HK : g_kept g pos mf W mem W (ms_mem ms)) by (intros a _; exact (Hview a)).
assert (HRE : g_regs_eq regs (ms_regs ms))
  by (exact (g_regs_eq_of_st_ok E _ ms (w_H W) regs [] HS HAE ltac:(vm_compute; reflexivity))).
assert (HC' : ECOMMON g pos mf ly S W (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md))
  by (exact (g_ec_kept g pos mf ly S W regs mem md ly S W (ms_regs ms) (ms_mem ms) _ _ HC0 HJ HRE HK)).
assert (HCG : g_CG g pos mf W (ms_regs ms) (ms_mem ms)).
{ eapply (g_cg_kept g pos mf W W regs (ms_regs ms) mem (ms_mem ms)).
  - exact (conj HIa (conj HD3 (conj HDid (conj HR23 (conj R22 (conj R26 (conj R21 (conj R27 (conj R24 (conj R25 (conj V176 (conj V160 (conj V120 V112)))))))))))))%type.
  - exact HRE.
  - exact HK.
  - apply mod32_mod8; exact HF32.
  - exact Hmf0.
  - exact Hmf64. }
destruct (g_chain g pos mf _ ly S W (ms_regs ms) (ms_mem ms) _ HJ HC') as (ch & Hch & Hchsp).
assert (Hs0 : s0Z (ms_regs ms) = e_sp0 g)
  by (unfold s0Z; destruct HC' as (_ & _ & R8' & _); rewrite R8'; apply unsigned_lit_small;
      clear - Hceil C1 HSTK HSTKv Hsp47; lia).
(* registers at the call *)
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (10%bv : bv 5) Ra0.
rewrite (EE 2%nat 2%bv eq_refl) in Rsp. rewrite (EE 10%nat 10%bv eq_refl) in Ra0.
rewrite R10 in Ra0.
assert (Qsp : spZ (ms_regs ms) = mf) by (unfold spZ; rewrite Rsp; exact Hsp).
assert (Qra : raZ (ms_regs ms) = BASE + 0x112c)
  by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear - HBLO HBASE; lia).
pmkst HS. rewrite (PSIG IB_buf_of AF_buf_of eq_refl).
eapply SRr_mono.
{ eapply (cl_callS B LAWS) with (STK1 := buf_of.BUF_OF_STK) (FP1 := []) (EV1 := buf_of.EV_BUF_OF)
    (o := mf - e_sp0 g) (ch1 := ch) (raw := getr (ms_regs ms) 1)
    (K := fun ly2 S2 (W2 : world SEGS) regs2 mem2 (md2 : Model) => exists res : Z,
       getr regs2 10 = w64 res /\ 4096 <= res /\ frames S2 = frames S /\
       ablocks B ly2 S2 = ablocks B ly S ++ [(res, Z.max (SlotModel.t_cap_fw (e_pl g)) 1)] /\
       mo_le MT S S2 (mo_malloc MT (Z.max (SlotModel.t_cap_fw (e_pl g)) 1))).
  - exact HJ.
  - clear - Qsp; lia.
  - rewrite Zminus_mod, (g_mod16 mf Hmf32), Hsp16; reflexivity.
  - clear - Hmf; lia.
  - unfold buf_of.BUF_OF_STK, ASTACK; lia.
  - unfold buf_of.BUF_OF_STK, ASTACK, STK_LLVMF, ASTACK in *; clear - Hmf HSTK; lia.
  - rewrite (HRE 3%bv ltac:(ginr)); exact Rgp.
  - rewrite (HRE 4%bv ltac:(ginr)); exact Rtp.
  - reflexivity.
  - rewrite Rra. apply ret_ok_codeptr_v; [clear - HBASE; lia | reflexivity].
  - change (4096 <= raZ (ms_regs ms)); rewrite Qra; clear - HBLO HBASE; lia.
  - replace (e_sp0 g + (mf - e_sp0 g)) with mf by (clear; lia). rewrite Hs0; exact Hch.
  - intros HPRE2.
    exact (HBUF ly S W (ms_regs ms) (ms_mem ms) _ ch (SlotModel.t_cap_fw (e_pl g)) HPRE2
      ltac:(rewrite Qra; destruct Hchsp as [-> | ->];
        [ unfold CTX_BUF_OF, BUF_OF_RAS; apply in_or_app; left; cbn [map spine In]; right; left; reflexivity
        | unfold CTX_BUF_OF, BUF_OF_RAS; apply in_or_app; right; cbn [map spine In]; right; left; reflexivity ])
      Ra0 ltac:(unfold MALLOC_MAX; clear - Hcap; lia)
      ltac:(unfold buf_of.EV_BUF_OF; pose proof (g_nev g pos _ ly S W (ms_mem ms) _ HJ);
            clear - Hnev0 HEV Hk HEVv H; lia)
      ltac:(rewrite (g_live g ly S [] HBL); cbn [bsum fold_right]; clear - Hlive0 HLIVE HLv Hcap; lia)
      ltac:(eapply (mo_ok_le MT MTL); [exact MOK|];
            pose proof (g_malloc_mev (Z.max (SlotModel.t_cap_fw (e_pl g)) 1) ltac:(clear - Hcap; lia));
            pose proof g_mev_pos; clear - H H0 Hk HEVv; nia)).
  - intros a (r & [] & _). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJsub & HPres & res & Ha0 & Hres & Hfrs & Eab & MLE2).
exists res, ly2, S2, regs2, mem2, md2.
split; [rewrite Rra; reflexivity|].
split; [exact HJ2|].
split; [rewrite Hfrs; exact Hfr|].
split; [clear - Hk Hk265; lia|].
split.
{ eapply (mle_weaken MT _ _ (4 * Z.of_nat (m_nrec g) * MEV MT + mo_malloc MT (Z.max (SlotModel.t_cap_fw (e_pl g)) 1)));
  [exact MTL | exact (mle_station MT _ _ _ _ _ MTL MLE MLE2)|].
  pose proof (g_malloc_mev (Z.max (SlotModel.t_cap_fw (e_pl g)) 1) ltac:(clear - Hcap; lia)). clear - H. nia. }
split.
{ eapply (mok_station MT S S2 ((EV_LLVMF - 4 * Z.of_nat (m_nrec g)) * MEV MT)
    (mo_malloc MT (Z.max (SlotModel.t_cap_fw (e_pl g)) 1)));
  [exact MTL | exact MOK | exact MLE2 | |].
  - pose proof g_mev_pos. clear - H Hk HEVv Hk265. nia.
  - pose proof (g_malloc_mev (Z.max (SlotModel.t_cap_fw (e_pl g)) 1) ltac:(clear - Hcap; lia)).
    clear - H. nia. }
assert (HKc : g_kept g pos mf W (ms_mem ms) W2 mem2).
{ eapply (g_kept_subj g pos mf buf_of.BUF_OF_STK [] ly S W (ms_mem ms) _ ly2 S2 W2 mem2 md2 buf_of.EV_BUF_OF);
  [ replace (e_sp0 g + (mf - e_sp0 g)) with mf in HJsub by (clear; lia); exact HJsub
  | exact (proj1 HJ) | rewrite Hfr; left; reflexivity | exact EF
  | exact HmfS
  | intros a (r & [] & _)
  | intros Hn; split; [exact (g_inp g ly S [] HBL HPRE Hn)|];
    rewrite Eab; apply in_or_app; left; exact (g_inp g ly S [] HBL HPRE Hn) ]. }
assert (HREc : g_regs_eq (ms_regs ms) regs2) by (apply g_regs_eq_pres; exact HPres).
split.
{ exact (g_ec_kept g pos mf ly S W (ms_regs ms) (ms_mem ms) _ ly2 S2 W2 regs2 mem2 md2 _ HC' HJ2 HREc HKc). }
split.
{ eapply (g_cg_kept g pos mf W W2 (ms_regs ms) regs2 (ms_mem ms) mem2);
  [exact HCG | exact HREc | exact HKc | apply mod32_mod8; exact HF32 | exact Hmf0 | exact Hmf64]. }
split.
{ split; [|apply Forall_cons; [cbn; split; [exact Hres | clear - Hcap; lia] | apply Forall_nil]].
  rewrite Eab. destruct HBL as (HPm & _).
  eapply Permutation_trans; [apply Permutation_app_tail; exact HPm|].
  cbn [app]. apply Permutation_app_comm. }
split; [exact Hres|]. split; [exact Ha0|].
assert (R18run : getr (ms_regs ms) 18 = getr regs 18)
  by (exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W) ms) regs [] [18%bv] HS HAE
       ltac:(vm_compute; reflexivity) 18%bv (or_introl eq_refl))).
rewrite (g_pres_reg (ms_regs ms) regs2 18%bv HPres ltac:(vm_compute; reflexivity)).
rewrite R18run. exact R18.
Qed.
(* ---- piece 2a: the id field and reac_identity_fw_str at +0x1144 ---------------------------------------- *)
(* The 16-bit value at id+0 (lhu a1,0(s3) at 0x818a4): the first two bytes of id. *)
Definition g_fwv (g : ectx) : Z :=
  nth 0 (map (fun b : byte => bv_unsigned b) (m_id g (m_nrec g))) 0 +
  256 * nth 1 (map (fun b : byte => bv_unsigned b) (m_id g (m_nrec g))) 0.
Lemma g_fwv_range : forall g, 0 <= g_fwv g < 65536.
Proof.
intros g. unfold g_fwv.
assert (R : forall j, 0 <= nth j (map (fun b : byte => bv_unsigned b) (m_id g (m_nrec g))) 0 < 256).
{ intros j. destruct (Nat.lt_ge_cases j (length (m_id g (m_nrec g)))) as [Hj | Hj].
  - rewrite (nth_indep _ _ (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
    rewrite (map_nth (fun b : byte => bv_unsigned b)). pose proof (bv_unsigned_in_range 8 (nth j (m_id g (m_nrec g)) (Z_to_bv 8 0))) as Q.
    change (bv_modulus 8) with 256 in Q. exact Q.
  - rewrite nth_overflow by (rewrite length_map; exact Hj). lia. }
pose proof (R 0%nat). pose proof (R 1%nat). lia.
Qed.
(* The run's memory: mf+184 holds &id (atom 32), and id's first two bytes (atom 33). *)
Definition g_rmf : YP09.region := YP09.mkRegion (Some 9%nat) 184 192 0 0 [YP09.mkChunk 184 (CVal 8 (SOff 32 0))].
Definition g_rid0 : YP09.region := YP09.mkRegion (Some 32%nat) 0 2 0 0 [YP09.mkChunk 0 (CVal 2 (SOff 33 0))].
Definition g_ss2a : sstate :=
  mkSS 0x112c sr_atoms [g_rmf; g_rid0] None
    (mkFacts [(32%nat, mkAF 4096 (2 ^ 47) 0); (33%nat, mkAF 0 65535 0)] [] []).

Lemma g_st2a : forall g pos mf (W : world SEGS) regs mem,
  getr regs 9 = w64 mf -> 0 <= mf -> mf + 256 <= 2 ^ 64 ->
  4096 <= SFa g pos -> SFa g pos + 1024 <= alloc_ceiling -> alloc_ceiling <= mf -> alloc_ceiling <= 2 ^ 47 ->
  mf_id g pos mf W mem -> id_at g pos (m_nrec g) W mem ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 (SFa g pos + V_id); Z_to_bv 64 (g_fwv g)])) g_ss2a
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x112c)) mem (seg_rom SEGS))).
Proof.
intros g pos mf W regs mem R9 H0 H64 HF0 HFc Hmc Hc47 HD HI.
set (E := Eimg (Ereg regs [Z_to_bv 64 (SFa g pos + V_id); Z_to_bv 64 (g_fwv g)])).
assert (E9 : ew E 9 = getr regs 9) by (unfold E; apply ew_Eimg_Ereg_nat; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 (SFa g pos + V_id))
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (g_fwv g))
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
pose proof (g_fwv_range g) as Hfw.
assert (U32 : bv_unsigned (ew E 32) = SFa g pos + V_id) by (rewrite E32; apply unsigned_lit_small; unfold V_id; lia).
assert (U33 : bv_unsigned (ew E 33) = g_fwv g) by (rewrite E33; apply unsigned_lit_small; lia).
assert (B9 : base_val E (Some 9%nat) = mf)
  by (cbn [base_val]; rewrite E9, R9; unfold w64; apply unsigned_lit_small; lia).
assert (B32 : base_val E (Some 32%nat) = SFa g pos + V_id) by (cbn [base_val]; exact U32).
rewrite restrict_mkst_fx. unfold g_ss2a. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
  + unfold region_ok, g_rmf. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite B9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ mf 184 8 (SOff 32 0) (SFa g pos + V_id)).
    * cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * unfold V_id. lia.
    * lia.
    * exact HD.
  + unfold region_ok, g_rid0. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite B32. split; [unfold V_id; lia|]. split; [unfold V_id; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (SFa g pos + V_id) 0 2 (SOff 33 0) (g_fwv g)).
    * cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * lia.
    * lia.
    * rewrite Z.add_0_r. destruct HI as (Hb & _). unfold bytes_at8 in Hb. unfold g_fwv.
      apply (g_vm2 W mem _ _ Hb). rewrite length_map, g_mid_len. lia.
- cbn [pairwise_disjoint all_disjoint]. split; [|exact (conj I I)]. split; [|exact I].
  unfold extent_disjoint, g_rmf, g_rid0. cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B9, B32. unfold V_id. right. lia.
- split; [|split; exact I]. cbn [atoms_ok f_atoms]. split; [|split; [|exact I]].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U32. unfold V_id. change (2 ^ 0) with 1. split; [lia|].
    split; [apply Z.mod_1_r | lia].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U33. change (2 ^ 0) with 1. split; [lia|].
    split; [apply Z.mod_1_r | lia].
Qed.

(* A block the segment allocated is not one of the entry's. *)
Lemma g_new_not_entry : forall g ly S (W : world SEGS) mem md res n,
  AR SEGS B ly S W mem md -> hblocks B g ly S [(res, n)] -> 0 <= n ->
  ~ In (res, n) (ablocks B (e_ly g) (e_S g)).
Proof.
intros g ly S W mem md res n HAR (HP & _) Hn Hin.
apply in_split in Hin as (l1 & l2 & Eq).
assert (HP2 : Permutation (ablocks B ly S) ((res, n) :: (res, n) :: (l1 ++ l2))).
{ eapply Permutation_trans; [exact HP|]. cbn [app]. rewrite Eq. apply perm_skip.
  apply Permutation_sym. apply Permutation_middle. }
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md _ _ _ HAR HP2) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. pose proof (req_size_pos n Hn) as [Hr _]. lia.
Qed.
Lemma g_blk_in : forall g ly S res n, hblocks B g ly S [(res, n)] -> In (res, n) (ablocks B ly S).
Proof. intros g ly S res n (HP & _). apply (Permutation_in _ (Permutation_sym HP)). left. reflexivity. Qed.
Lemma g_res_ne_inp : forall g ly S (W : world SEGS) mem md res n,
  AR SEGS B ly S W mem md -> hblocks B g ly S [(res, n)] -> E_PRE g -> 0 <= n ->
  0 < e_n g -> res <> e_p g.
Proof.
intros g ly S W mem md res n HAR HBL HPRE Hn0 Hn Heq.
pose proof (g_blk_in g ly S res n HBL) as Hb1. pose proof (g_inp g ly S _ HBL HPRE Hn) as Hb2.
destruct (g_epre_bud g HPRE) as (_ & _ & Hin0 & _).
destruct (Z.eq_dec n (e_n g)) as [En | En].
- apply (g_new_not_entry g ly S W mem md res n HAR HBL Hn0). rewrite Heq, En. exact (Hin0 Hn).
- assert (Hd : (res, n) <> (e_p g, e_n g)) by (intros E; injection E as _ E2; exact (En E2)).
  pose proof (sep_blocks SEGS B LAWS ly S W mem md res n (e_p g) (e_n g) HAR Hb1 Hb2 Hd) as Hz.
  unfold zdisjoint in Hz. cbn [fst snd] in Hz. pose proof (req_size_pos n Hn0) as [R1 _].
  pose proof (req_size_pos (e_n g) ltac:(lia)) as [R2 _]. lia.
Qed.

Lemma g_p2a : forall g pos mf res W c,
  ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 1) (BASE + 0x112c)
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       g_CG g pos mf W2 regs2 mem2 /\
       hblocks B g ly2 S2 [(res, Z.max (SlotModel.t_cap_fw (e_pl g)) 1)] /\
       4096 <= res /\ getr regs2 10 = w64 res /\
       getr regs2 18 = w64 (SlotModel.t_cap_fw (e_pl g))) W c ->
  SRr SEGS W c (ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 1) (BASE + 0x1148)
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       g_CG g pos mf W2 regs2 mem2 /\
       hblocks B g ly2 S2 [(res, Z.max (SlotModel.t_cap_fw (e_pl g)) 1)] /\ 4096 <= res /\
       getr regs2 18 = w64 (SlotModel.t_cap_fw (e_pl g)) /\
       getr regs2 19 = w64 (SFa g pos + V_id) /\ getr regs2 20 = w64 res /\
       (if reac_identity_fw_str.fw_writes res (SlotModel.t_cap_fw (e_pl g)) then
          getr regs2 10 = w64 (reac_identity_fw_str_c.L (g_fwv g)) /\
          garr8 SEGS (rd W2 mem2) res (reac_identity_fw_str.fw_bytes (g_fwv g))
        else getr regs2 10 = w64 (-1)))).
Proof.
intros g pos mf res W c (ly & S & regs & mem & md & -> & HJ & Hfr & Hk & MLE & MOK & HC & HP).
destruct HP as (HCG0 & HBL & Hres & R10 & R18).
pose proof HCG0 as (HIa & HD3 & HDid & HR23 & R22 & R26 & R21 & R27 & R24 & R25 & V176 & V160 & V120 & V112).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (pa_base_lo (PL := PL_identb)) as HBLO. pose proof asan_consts as (C1 & _).
pose proof HC as HC0. pose proof (proj1 HJ) as HAR.
destruct (g_facts g pos mf _ ly S W regs mem md HJ Hfr HC) as
  (Hsp & Hceil & Hsp47 & Hsp16 & Hmf & Hmf32 & HF4096 & HFceil & HF32 & EF).
assert (HSTKv : STK_LLVMF = 16736) by reflexivity.
assert (HFWv : reac_identity_fw_str.REAC_IDENTITY_FW_STR_STK = 4112) by reflexivity.
assert (Hmf0 : 0 <= mf) by (clear - Hmf Hceil C1 HSTK HSTKv; lia).
assert (Hmf64 : mf + 256 <= 2 ^ 64) by (clear - Hmf Hsp47; lia).
assert (Hmc : alloc_ceiling <= mf) by (clear - Hmf Hceil C1 HSTK HSTKv; lia).
assert (Hc47 : alloc_ceiling <= 2 ^ 47) by (clear - C1; lia).
assert (Hcap : 0 <= SlotModel.t_cap_fw (e_pl g) < 16)
  by (unfold SlotModel.t_cap_fw; apply Z.mod_pos_bound; lia).
destruct HC as (_ & R9 & _ & _ & _ & Rgp & Rtp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & HPRE & _).
pose proof (g_fwv_range g) as Hfw.
pose proof (g_blk_in g ly S _ _ HBL) as Hbin.
destruct (al_blocks _ _ LAWS ly S W mem md _ _ HAR Hbin) as (Hr16 & Hr4096 & Hrceil & _ & HrPres & _).
pose proof (req_size_pos (Z.max (SlotModel.t_cap_fw (e_pl g)) 1) ltac:(lia)) as [Hreq1 Hreqge].
assert (Hnent : ~ In (res, Z.max (SlotModel.t_cap_fw (e_pl g)) 1) (ablocks B (e_ly g) (e_S g)))
  by exact (g_new_not_entry g ly S W mem md res _ HAR HBL ltac:(lia)).
assert (Hn7 : reac_identity_fw_str.fw_n (g_fwv g) <= 7).
{ destruct (Z_lt_ge_dec (g_fwv g) 10000);
  [rewrite reac_identity_fw_str.fw_n_short by lia | rewrite reac_identity_fw_str.fw_n_long by lia]; lia. }
(* the run: ld s3,184(s1); lhu a1,0(s3); mv s4,a0; mv a0,a1; mv a1,s4; mv a2,s2; jal *)
pose proof (g_st2a g pos mf W regs mem R9 Hmf0 Hmf64 HF4096 HFceil Hmc Hc47 HDid HIa) as HS.
remember (Eimg (Ereg regs [Z_to_bv 64 (SFa g pos + V_id); Z_to_bv 64 (g_fwv g)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 (SFa g pos + V_id); Z_to_bv 64 (g_fwv g)]) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (SFa g pos + V_id))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (g_fwv g))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (SHOK : sh_ok SEGS buf_of.Bx_BO [] E (mrestrict (w_H W) mem)) by constructor.
clear HE.
unfold cfg_at. change (w64 (BASE + 0x112c)) with (Z_to_bv 64 (BASE + 0x112c)).
paj_run_tok RUN HS HJ SHOK buf_of.Bspan_BO; [awr_ok_tac |].
(* the state at reac_identity_fw_str's entry *)
assert (Emem : forall x : word, ms_mem ms x = mem x).
{ intros x. apply HF. intros (r & Hin & Ha). cbn in Hin.
  destruct Hin as [<- | [<- | []]]; cbn [YP09.r_wlo YP09.r_whi g_rmf g_rid0] in Ha; lia. }
assert (Hview : forall a, aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
  by (intros a; apply aview_eq_of; unfold mrestrict; rewrite Emem; reflexivity).
assert (HK : g_kept g pos mf W mem W (ms_mem ms)) by (intros a _; exact (Hview a)).
assert (HRE : g_regs_eq regs (ms_regs ms))
  by (exact (g_regs_eq_of_st_ok E _ ms (w_H W) regs _ HS HAE ltac:(vm_compute; reflexivity))).
assert (HC' : ECOMMON g pos mf ly S W (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md))
  by (exact (g_ec_kept g pos mf ly S W regs mem md ly S W (ms_regs ms) (ms_mem ms) _ _ HC0 HJ HRE HK)).
assert (HCG : g_CG g pos mf W (ms_regs ms) (ms_mem ms)).
{ eapply (g_cg_kept g pos mf W W regs (ms_regs ms) mem (ms_mem ms)).
  - exact HCG0.
  - exact HRE.
  - exact HK.
  - apply mod32_mod8; exact HF32.
  - exact Hmf0.
  - exact Hmf64. }
assert (HBLm : hblocks B g ly S [(res, Z.max (SlotModel.t_cap_fw (e_pl g)) 1)]) by exact HBL.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (19%bv : bv 5) Rs3. prreg HS (20%bv : bv 5) Rs4. prreg HS (18%bv : bv 5) Rs2.
rewrite (EE 2%nat 2%bv eq_refl) in Rsp. rewrite (EE 10%nat 10%bv eq_refl), R10 in Ra1, Rs4.
rewrite (EE 18%nat 18%bv eq_refl), R18 in Ra2, Rs2.
rewrite E33 in Ra0. rewrite E32 in Rs3.
assert (Qsp : spZ (ms_regs ms) = mf) by (unfold spZ; rewrite Rsp; exact Hsp).
destruct (al_blocks _ _ LAWS ly S W (ms_mem ms) _ _ _ (proj1 HJ) Hbin) as (_ & _ & _ & _ & HrPresM & _).
pmkst HS. rewrite (PSIG IB_reac_identity_fw_str AF_reac_identity_fw_str eq_refl).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) ?Q =>
  change (SRr SEGS W (cfg_at SEGS (BASE + AF_reac_identity_fw_str) rg mm mdx) Q) end.
eapply SRr_mono.
{ apply (HFWS LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly S W (ms_mem ms) _
    (4 * Z.of_nat (m_nrec g) + 1) (ms_regs ms) (g_fwv g) res (SlotModel.t_cap_fw (e_pl g)) HJ).
  - rewrite Rra. apply ret_ok_codeptr_v; [clear - HBASE; lia | reflexivity].
  - exact Ra0.
  - exact Ra1.
  - exact Ra2.
  - exact Hfw.
  - clear - Hres Hrceil Hreq1 Hc47; split; lia.
  - clear - Hcap; split; lia.
  - rewrite Qsp. apply g_mod16. exact Hmf32.
  - rewrite Qsp, HFWv. clear - Hmf HSTK HSTKv. lia.
  - rewrite Qsp. clear - Hmf. lia.
  - intros Hw. unfold reac_identity_fw_str.fw_writes in Hw. apply andb_prop in Hw as [_ Hc8].
    apply Z.leb_le in Hc8.
    assert (Hn0 : 0 < reac_identity_fw_str.fw_n (g_fwv g)).
    { destruct (Z_lt_ge_dec (g_fwv g) 10000);
      [rewrite reac_identity_fw_str.fw_n_short by lia | rewrite reac_identity_fw_str.fw_n_long by lia]; lia. }
    assert (Hfit : res + reac_identity_fw_str.fw_n (g_fwv g) <= res + req_size (Z.max (SlotModel.t_cap_fw (e_pl g)) 1)) by lia.
    split; [|split].
    + intros a Ha. left. exists res, (Z.max (SlotModel.t_cap_fw (e_pl g)) 1). split; [exact Hbin | lia].
    + intros a Ha. rewrite Qsp.
      destruct (HrPresM a ltac:(lia)) as (Hap & Hno). split; [|split; [|split]].
      * right; right; left. exists res, (Z.max (SlotModel.t_cap_fw (e_pl g)) 1).
        split; [exact Hbin|]. split; [exact Hnent | lia].
      * exact Hap.
      * exact Hno.
      * unfold ESTACK. clear - Ha Hfit Hrceil Hmc Hmf Hceil HSTK HSTKv. lia.
    + eapply (range_addressable_of_block SEGS B LAWS ly S W (ms_mem ms) _ res); [exact (proj1 HJ) | exact Hbin | lia | lia]. }
cbv beta. intros W2 c2 _ Hpost.
destruct Hpost as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HPres & Hfrs & Hperm & Hif).
assert (HKc : g_kept g pos mf W (ms_mem ms) W2 mem2).
{ destruct (reac_identity_fw_str.fw_writes res (SlotModel.t_cap_fw (e_pl g))) eqn:Hw.
  - destruct Hif as (_ & _ & Htcj).
    unfold reac_identity_fw_str.fw_writes in Hw. apply andb_prop in Hw as [_ Hc8]. apply Z.leb_le in Hc8.
    rewrite Qsp in Htcj.
    apply (g_kept_tcj g pos mf _ ly S W (ms_mem ms) _ W2 mem2 _ Htcj (proj1 HJ) ltac:(rewrite Hfr; left; reflexivity) EF).
    + rewrite HFWv. clear - Hmf Hceil HSTK HSTKv. lia.
    + intros a Ha. exists res, (Z.max (SlotModel.t_cap_fw (e_pl g)) 1). split; [exact Hbin|].
      split; [lia|]. intros Hn. exact (g_res_ne_inp g ly S W mem md res _ HAR HBL HPRE ltac:(lia) Hn).
    + intros Hn. exact (g_inp g ly S _ HBL HPRE Hn).
  - destruct Hif as (_ & Htcj). rewrite Qsp in Htcj.
    apply (g_kept_tcj g pos mf _ ly S W (ms_mem ms) _ W2 mem2 _ Htcj (proj1 HJ) ltac:(rewrite Hfr; left; reflexivity) EF).
    + rewrite HFWv. clear - Hmf Hceil HSTK HSTKv. lia.
    + intros a [].
    + intros Hn. exact (g_inp g ly S _ HBL HPRE Hn). }
assert (HREc : g_regs_eq (ms_regs ms) regs2) by (apply g_regs_eq_pres; exact HPres).
exists ly2, S2, regs2, mem2, md2.
split; [rewrite Rra; reflexivity|].
split; [exact HJ2|].
split; [rewrite Hfrs; exact Hfr|].
split; [exact Hk|].
split.
{ pose proof (mle_station MT _ _ _ _ _ MTL MLE (HMT0 S S2)) as X. rewrite Z.add_0_r in X. exact X. }
split.
{ apply (mok_station MT S S2 ((EV_LLVMF - (4 * Z.of_nat (m_nrec g) + 1)) * MEV MT) 0); [exact MTL | exact MOK | exact (HMT0 S S2) | | lia].
  pose proof g_mev_pos. clear - H Hk. nia. }
split.
{ exact (g_ec_kept g pos mf ly S W (ms_regs ms) (ms_mem ms) _ ly2 S2 W2 regs2 mem2 md2 _ HC' HJ2 HREc HKc). }
split.
{ eapply (g_cg_kept g pos mf W W2 (ms_regs ms) regs2 (ms_mem ms) mem2);
  [exact HCG | exact HREc | exact HKc | apply mod32_mod8; exact HF32 | exact Hmf0 | exact Hmf64]. }
split.
{ destruct HBL as (HPm & HFa). split; [eapply Permutation_trans; [exact Hperm | exact HPm] | exact HFa]. }
split; [exact Hres|].
split; [rewrite (g_pres_reg (ms_regs ms) regs2 18%bv HPres ltac:(vm_compute; reflexivity)); exact Rs2|].
split; [rewrite (g_pres_reg (ms_regs ms) regs2 19%bv HPres ltac:(vm_compute; reflexivity)); exact Rs3|].
split; [rewrite (g_pres_reg (ms_regs ms) regs2 20%bv HPres ltac:(vm_compute; reflexivity)); exact Rs4|].
destruct (reac_identity_fw_str.fw_writes res (SlotModel.t_cap_fw (e_pl g))).
- destruct Hif as (Ha0' & Hgar & _). split; [exact Ha0' | exact Hgar].
- destruct Hif as (Ha0' & _). exact Ha0'.
Qed.

(* ---- check_str at the callee's entry, used at 0x818c4, 0x818e0 and 0x8191c ---------------------------- *)
Lemma g_aview_garr8 : forall (W : world SEGS) m a l j, garr8 SEGS (rd W m) a l -> (j < length l)%nat ->
  aview SEGS (w_H W) m (a + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W m a l j HG Hj. destruct (HG j Hj) as (V & R). specialize (V 0%nat ltac:(lia)).
unfold aview. replace (a + Z.of_nat j) with (a + Z.of_nat j + Z.of_nat 0) by (cbn; lia). rewrite V.
cbn [option_map]. f_equal. rewrite (g_le1 _ R). rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. apply Z.mod_small; lia.
Qed.
Lemma g_chk_call : forall g pos mf k ly S (W : world SEGS) regsc memc mdc o n r c (bs : list Z) retk,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly S W memc mdc k ->
  frames S = [(4, pos)] -> ECOMMON g pos mf ly S W regsc memc mdc -> g_CG g pos mf W regsc memc ->
  In (o, n) (ablocks B ly S) -> 0 <= n -> (0 < e_n g -> In (e_p g, e_n g) (ablocks B ly S)) ->
  getr regsc 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr regsc 10 = w64 r -> getr regsc 11 = w64 o -> getr regsc 12 = w64 c ->
  - 2 ^ 31 <= r < 2 ^ 31 -> 0 <= c < 2 ^ 64 ->
  (0 <= r -> r < c /\ r + 1 <= req_size n /\ garr8 SEGS (rd W memc) o bs /\ Z.of_nat (length bs) = r + 1 /\
     nth (Z.to_nat r) bs 0 = 0 /\ (forall i, (i < Z.to_nat r)%nat -> nth i bs 0 <> 0)) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_check_str) regsc memc mdc)
    (fun W2 c2 => exists regs2 mem2 md2, c2 = cfg_at SEGS (BASE + retk) regs2 mem2 md2 /\ W2 = W /\
       ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly S W mem2 md2 k /\
       aregs_preserved regsc regs2 /\ ECOMMON g pos mf ly S W regs2 mem2 md2 /\ g_CG g pos mf W regs2 mem2 /\
       g_kept g pos mf W memc W mem2).
Proof.
intros g pos mf k ly S W regsc memc mdc o n r c bs retk HJ Hfr HC HCG Hbin Hn0 Hinp Rra Hrk Hrk2 Ra0 Ra1 Ra2 Hr Hc Hstr.
pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_identb)) as HBLO. pose proof asan_consts as (C1 & _).
pose proof (proj1 HJ) as HAR.
destruct (g_facts g pos mf _ ly S W regsc memc mdc HJ Hfr HC) as
  (Hsp & Hceil & Hsp47 & Hsp16 & Hmf & Hmf32 & HF4096 & HFceil & HF32 & EF).
assert (HSTKv : STK_LLVMF = 16736) by reflexivity.
assert (HCSv : check_str.CHECK_STR_STK = 8208) by reflexivity.
assert (Hmf0 : 0 <= mf) by (clear - Hmf Hceil C1 HSTK HSTKv; lia).
assert (Hmf64 : mf + 256 <= 2 ^ 64) by (clear - Hmf Hsp47; lia).
pose proof HC as HC0.
destruct HC as (_ & _ & R8 & _ & _ & Rgp & Rtp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & HPRE & _).
destruct (al_blocks _ _ LAWS ly S W memc mdc o n HAR Hbin) as (_ & Ho4096 & Hoceil & _).
pose proof (req_size_pos n Hn0) as [Hreq1 _].
destruct (g_chain g pos mf _ ly S W regsc memc _ HJ HC0) as (ch & Hch & _).
assert (Hs0 : s0Z regsc = e_sp0 g)
  by (unfold s0Z; rewrite R8; apply unsigned_lit_small; clear - Hceil C1 HSTK HSTKv Hsp47; lia).
assert (Qra : raZ regsc = BASE + retk) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear - HBASE Hrk; lia).
unfold cfg_at. change (w64 (BASE + AF_check_str)) with (Z_to_bv 64 (BASE + AF_check_str)).
eapply SRr_mono.
{ eapply (cl_callS B LAWS) with (STK1 := check_str.CHECK_STR_STK) (FP1 := []) (EV1 := 0)
    (o := mf - e_sp0 g) (ch1 := ch) (raw := getr regsc 1)
    (K := fun ly2 S2 (W2 : world SEGS) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) =>
       ly2 = ly /\ S2 = S /\ W2 = W).
  - exact HJ.
  - clear - Hsp; lia.
  - rewrite Zminus_mod, (g_mod16 mf Hmf32), Hsp16; reflexivity.
  - clear - Hmf; lia.
  - rewrite HCSv; lia.
  - rewrite HCSv. clear - Hmf HSTK HSTKv. lia.
  - exact Rgp.
  - exact Rtp.
  - reflexivity.
  - rewrite Rra. apply ret_ok_codeptr_v; [exact Hrk | exact Hrk2].
  - change (4096 <= raZ regsc); rewrite Qra; clear - HBLO Hrk; lia.
  - replace (e_sp0 g + (mf - e_sp0 g)) with mf by (clear; lia). rewrite Hs0; exact Hch.
  - intros HPRE2.
    apply (HCHK ly S W regsc memc mdc ch r o c HPRE2 (g_aro g pos k ly S W memc mdc HJ HPRE) Ra0 Ra1 Ra2 Hr Hc).
    intros Hr0. destruct (Hstr Hr0) as (Hrc & Hrn & Hgar & Hlen & Hlast & Hnz).
    assert (Hblk : o + r + 1 <= o + req_size n) by lia.
    split; [exact Hrc|]. split; [lia|].
    split.
    { destruct (blk_off_imgP B ly S W memc mdc o n HAR Hbin) as [X | X]; [left; lia | right; exact X]. }
    split.
    { split; [lia|]. split.
      - intros i Hi. exists (nth (Z.to_nat i) bs 0).
        replace (o + i) with (o + Z.of_nat (Z.to_nat i)) by lia.
        split; [apply g_aview_garr8; [exact Hgar | lia]|]. apply Hnz. lia.
      - intros _. replace (o + r) with (o + Z.of_nat (Z.to_nat r)) by lia.
        rewrite (g_aview_garr8 W memc o bs (Z.to_nat r) Hgar ltac:(lia)), Hlast. reflexivity. }
    split.
    { intros a Ha. rewrite Hsp, HCSv. clear - Ha Hblk Hoceil Hmf Hceil HSTK HSTKv. lia. }
    split; [eapply (amem_range_of_block SEGS B LAWS ly S W memc mdc o n); [exact HAR | exact Hbin | lia | lia]|].
    split; [eapply (range_addressable_of_block SEGS B LAWS ly S W memc mdc o n); [exact HAR | exact Hbin | lia | lia]|].
    split; [eapply (shadow_hull_vis_of_block SEGS B LAWS ly S W memc mdc o n); [exact HAR | exact Hbin | lia | lia | lia]|].
    intros a Ha. exact (blk_tail_present SEGS B LAWS ly S W memc mdc o n r a HAR Hbin ltac:(lia) Ha).
  - intros a (rr & [] & _). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJsub & HPres & -> & -> & ->).
assert (HKc : g_kept g pos mf W memc W mem2).
{ replace (e_sp0 g + (mf - e_sp0 g)) with mf in HJsub by (clear; lia).
  apply (g_kept_subj g pos mf check_str.CHECK_STR_STK [] ly S W memc mdc ly S W mem2 md2 0 HJsub HAR
    ltac:(rewrite Hfr; left; reflexivity) EF).
  - rewrite HCSv. clear - Hmf Hceil HSTK HSTKv C1. lia.
  - intros a (rr & [] & _).
  - intros Hn. split; exact (Hinp Hn). }
assert (HREc : g_regs_eq regsc regs2) by (apply g_regs_eq_pres; exact HPres).
rewrite Z.add_0_r in HJ2.
exists regs2, mem2, md2.
split; [unfold cfg_at; rewrite Rra; reflexivity|].
split; [reflexivity|].
split; [exact HJ2|].
split; [exact HPres|].
split; [exact (g_ec_kept g pos mf ly S W regsc memc mdc ly S W regs2 mem2 md2 k HC0 HJ2 HREc HKc)|].
split; [eapply (g_cg_kept g pos mf W W regsc regs2 memc mem2);
  [exact HCG | exact HREc | exact HKc | apply mod32_mod8; exact HF32 | exact Hmf0 | exact Hmf64]|].
exact HKc.
Qed.

(* The string reac_identity_fw_str writes, in the shape g_chk_call asks. *)
Lemma g_fw_str_ok : forall v, 0 <= v < 65536 ->
  Z.of_nat (length (reac_identity_fw_str.fw_bytes v)) = reac_identity_fw_str_c.L v + 1 /\
  nth (Z.to_nat (reac_identity_fw_str_c.L v)) (reac_identity_fw_str.fw_bytes v) 0 = 0 /\
  (forall i, (i < Z.to_nat (reac_identity_fw_str_c.L v))%nat -> nth i (reac_identity_fw_str.fw_bytes v) 0 <> 0) /\
  0 <= reac_identity_fw_str_c.L v <= 6.
Proof.
intros v Hv. unfold reac_identity_fw_str.fw_bytes.
pose proof (reac_identity_fw_str_c.reac_identity_fw_str_c3_len v Hv) as (_ & HL).
assert (EL : reac_identity_fw_str_c.L v = Z.of_nat (length (reac_identity_fw_str_c.FW v))) by reflexivity.
split; [rewrite length_map, length_app; cbn [length]; lia|].
split.
{ rewrite EL, Nat2Z.id, map_app, app_nth2 by (rewrite length_map; lia).
  rewrite length_map, Nat.sub_diag. reflexivity. }
split.
{ intros i Hi. rewrite EL, Nat2Z.id in Hi.
  rewrite map_app, app_nth1 by (rewrite length_map; exact Hi).
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0 : byte))) by (rewrite length_map; exact Hi).
  rewrite map_nth. apply (reac_identity_fw_str_c.reac_identity_fw_str_c3_nz v Hv). apply nth_In. exact Hi. }
destruct (v <? 10000); lia.
Qed.

(* ---- piece 2b: check_str at +0x1150 on the first firmware string ------------------------------------- *)
Lemma g_p2b : forall g pos mf res W c,
  ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 1) (BASE + 0x1148)
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       g_CG g pos mf W2 regs2 mem2 /\
       hblocks B g ly2 S2 [(res, Z.max (SlotModel.t_cap_fw (e_pl g)) 1)] /\ 4096 <= res /\
       getr regs2 18 = w64 (SlotModel.t_cap_fw (e_pl g)) /\
       getr regs2 19 = w64 (SFa g pos + V_id) /\ getr regs2 20 = w64 res /\
       (if reac_identity_fw_str.fw_writes res (SlotModel.t_cap_fw (e_pl g)) then
          getr regs2 10 = w64 (reac_identity_fw_str_c.L (g_fwv g)) /\
          garr8 SEGS (rd W2 mem2) res (reac_identity_fw_str.fw_bytes (g_fwv g))
        else getr regs2 10 = w64 (-1))) W c ->
  SRr SEGS W c (ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 1) (BASE + 0x1154)
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       g_CG g pos mf W2 regs2 mem2 /\
       hblocks B g ly2 S2 [(res, Z.max (SlotModel.t_cap_fw (e_pl g)) 1)] /\ 4096 <= res /\
       getr regs2 18 = w64 (SlotModel.t_cap_fw (e_pl g)) /\
       getr regs2 19 = w64 (SFa g pos + V_id) /\ getr regs2 20 = w64 res)).
Proof.
intros g pos mf res W c (ly & S & regs & mem & md & -> & HJ & Hfr & Hk & MLE & MOK & HC & HP).
destruct HP as (HCG0 & HBL & Hres & R18 & R19 & R20 & Hif).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & _). pose proof HC as HC0. pose proof (proj1 HJ) as HAR.
destruct (g_facts g pos mf _ ly S W regs mem md HJ Hfr HC) as
  (Hsp & Hceil & Hsp47 & Hsp16 & Hmf & Hmf32 & HF4096 & HFceil & HF32 & EF).
assert (HSTKv : STK_LLVMF = 16736) by reflexivity.
assert (Hmf0 : 0 <= mf) by (clear - Hmf Hceil C1 HSTK HSTKv; lia).
assert (Hmf64 : mf + 256 <= 2 ^ 64) by (clear - Hmf Hsp47; lia).
assert (Hcap : 0 <= SlotModel.t_cap_fw (e_pl g) < 16)
  by (unfold SlotModel.t_cap_fw; apply Z.mod_pos_bound; lia).
destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & HPRE & _).
pose proof (g_fwv_range g) as Hfw.
pose proof (g_blk_in g ly S _ _ HBL) as Hbin.
(* the run: mv a1,s4; mv a2,s2; jal *)
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HS : st_ok_pi SEGS VAL E (mkSS 0x1148 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x1148)) mem (seg_rom SEGS)))).
{ subst E. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full;
  [apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | exact I
  | split; [cbn [atoms_ok f_atoms]; exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS buf_of.Bx_BO [] E (mrestrict (w_H W) mem)) by constructor.
clear HE.
unfold cfg_at. change (w64 (BASE + 0x1148)) with (Z_to_bv 64 (BASE + 0x1148)).
paj_run_tok RUN HS HJ SHOK buf_of.Bspan_BO; [awr_ok_tac |].
assert (Emem : forall x : word, ms_mem ms x = mem x) by (intros x; apply HF; intros (r & [] & _)).
assert (Hview : forall a, aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
  by (intros a; apply aview_eq_of; unfold mrestrict; rewrite Emem; reflexivity).
assert (HK : g_kept g pos mf W mem W (ms_mem ms)) by (intros a _; exact (Hview a)).
assert (HRE : g_regs_eq regs (ms_regs ms))
  by (exact (g_regs_eq_of_st_ok E _ ms (w_H W) regs [] HS HAE ltac:(vm_compute; reflexivity))).
assert (HC' : ECOMMON g pos mf ly S W (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md))
  by (exact (g_ec_kept g pos mf ly S W regs mem md ly S W (ms_regs ms) (ms_mem ms) _ _ HC0 HJ HRE HK)).
assert (HCG : g_CG g pos mf W (ms_regs ms) (ms_mem ms)).
{ eapply (g_cg_kept g pos mf W W regs (ms_regs ms) mem (ms_mem ms)).
  - exact HCG0.
  - exact HRE.
  - exact HK.
  - apply mod32_mod8; exact HF32.
  - exact Hmf0.
  - exact Hmf64. }
prreg HS (1%bv : bv 5) Rra. prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (18%bv : bv 5) Rs2. prreg HS (19%bv : bv 5) Rs3. prreg HS (20%bv : bv 5) Rs4.
rewrite (EE 10%nat 10%bv eq_refl) in Ra0. rewrite (EE 20%nat 20%bv eq_refl), R20 in Ra1, Rs4.
rewrite (EE 18%nat 18%bv eq_refl), R18 in Ra2, Rs2. rewrite (EE 19%nat 19%bv eq_refl), R19 in Rs3.
pmkst HS. rewrite (PSIG IB_check_str AF_check_str eq_refl).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) ?Q =>
  change (SRr SEGS W (cfg_at SEGS (BASE + AF_check_str) rg mm mdx) Q) end.
assert (Hgen : forall r (bs : list Z), getr regs 10 = w64 r -> - 2 ^ 31 <= r < 2 ^ 31 ->
  (0 <= r -> r < SlotModel.t_cap_fw (e_pl g) /\ r + 1 <= req_size (Z.max (SlotModel.t_cap_fw (e_pl g)) 1) /\
     garr8 SEGS (rd W (ms_mem ms)) res bs /\ Z.of_nat (length bs) = r + 1 /\
     nth (Z.to_nat r) bs 0 = 0 /\ (forall i, (i < Z.to_nat r)%nat -> nth i bs 0 <> 0)) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_check_str) (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md))
    (ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 1) (BASE + 0x1154)
      (fun ly2 S2 W2 regs2 mem2 md2 =>
         g_CG g pos mf W2 regs2 mem2 /\
         hblocks B g ly2 S2 [(res, Z.max (SlotModel.t_cap_fw (e_pl g)) 1)] /\ 4096 <= res /\
         getr regs2 18 = w64 (SlotModel.t_cap_fw (e_pl g)) /\
         getr regs2 19 = w64 (SFa g pos + V_id) /\ getr regs2 20 = w64 res))).
{ intros r bs Hr0 Hr Hstr. eapply SRr_mono.
  { apply (g_chk_call g pos mf _ ly S W (ms_regs ms) (ms_mem ms) _ res (Z.max (SlotModel.t_cap_fw (e_pl g)) 1)
      r (SlotModel.t_cap_fw (e_pl g)) bs 0x1154 HJ Hfr HC' HCG Hbin ltac:(lia)
      (fun Hn => g_inp g ly S _ HBL HPRE Hn) Rra ltac:(clear - HBASE; lia) eq_refl).
    - rewrite Ra0. exact Hr0.
    - exact Ra1.
    - exact Ra2.
    - exact Hr.
    - clear - Hcap; split; lia.
    - exact Hstr. }
  cbv beta. intros W2 c2 _ (regs2 & mem2 & md2 & -> & -> & HJ2 & HPres & HC2 & HCG2 & _).
  exists ly, S, regs2, mem2, md2.
  split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hfr|]. split; [exact Hk|].
  split; [exact MLE|]. split; [exact MOK|]. split; [exact HC2|]. split; [exact HCG2|].
  split; [exact HBL|]. split; [exact Hres|].
  split; [rewrite (g_pres_reg (ms_regs ms) regs2 18%bv HPres ltac:(vm_compute; reflexivity)); exact Rs2|].
  split; [rewrite (g_pres_reg (ms_regs ms) regs2 19%bv HPres ltac:(vm_compute; reflexivity)); exact Rs3|].
  rewrite (g_pres_reg (ms_regs ms) regs2 20%bv HPres ltac:(vm_compute; reflexivity)); exact Rs4. }
destruct (reac_identity_fw_str.fw_writes res (SlotModel.t_cap_fw (e_pl g))) eqn:Hw.
- destruct Hif as (Hr10 & Hgar).
  unfold reac_identity_fw_str.fw_writes in Hw. apply andb_prop in Hw as [_ Hc8]. apply Z.leb_le in Hc8.
  destruct (g_fw_str_ok (g_fwv g) Hfw) as (Hlen & Hlast & Hnz & HLr).
  apply (Hgen _ (reac_identity_fw_str.fw_bytes (g_fwv g)) Hr10 ltac:(lia)).
  intros _. split; [lia|]. split; [pose proof (req_size_pos (Z.max (SlotModel.t_cap_fw (e_pl g)) 1) ltac:(lia)) as [_ Q]; lia|].
  split; [eapply g_garr8_kept; [|exact Hgar]; intros j _; exact (Hview (res + j))|].
  split; [exact Hlen|]. split; [exact Hlast | exact Hnz].
- apply (Hgen (-1) [] Hif ltac:(lia)). intros Hneg. lia.
Qed.

(* ---- pieces 3a / 3b: reac_identity_fw_str on t_any_fw (+0x1160) and check_str (+0x116c) ------------- *)
Lemma g_anyfw_range : forall g, 0 <= SlotModel.t_any_fw (e_pl g) < 65536.
Proof.
intros g. unfold SlotModel.t_any_fw, SlotModel.tb.
pose proof (SlotModel.inb_range (e_pl g) (SlotModel.cT (e_pl g) + 9)).
pose proof (SlotModel.inb_range (e_pl g) (SlotModel.cT (e_pl g) + 10)). lia.
Qed.
Lemma g_p3a : forall g pos mf res W c,
  ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 1) (BASE + 0x1154)
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       g_CG g pos mf W2 regs2 mem2 /\
       hblocks B g ly2 S2 [(res, Z.max (SlotModel.t_cap_fw (e_pl g)) 1)] /\ 4096 <= res /\
       getr regs2 18 = w64 (SlotModel.t_cap_fw (e_pl g)) /\
       getr regs2 19 = w64 (SFa g pos + V_id) /\ getr regs2 20 = w64 res) W c ->
  SRr SEGS W c (ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 1) (BASE + 0x1164)
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       g_CG g pos mf W2 regs2 mem2 /\
       hblocks B g ly2 S2 [(res, Z.max (SlotModel.t_cap_fw (e_pl g)) 1)] /\ 4096 <= res /\
       getr regs2 18 = w64 (SlotModel.t_cap_fw (e_pl g)) /\
       getr regs2 19 = w64 (SFa g pos + V_id) /\ getr regs2 20 = w64 res /\
       (if reac_identity_fw_str.fw_writes res (SlotModel.t_cap_fw (e_pl g)) then
          getr regs2 10 = w64 (reac_identity_fw_str_c.L (SlotModel.t_any_fw (e_pl g))) /\
          garr8 SEGS (rd W2 mem2) res (reac_identity_fw_str.fw_bytes (SlotModel.t_any_fw (e_pl g)))
        else getr regs2 10 = w64 (-1)))).
Proof.
intros g pos mf res W c (ly & S & regs & mem & md & -> & HJ & Hfr & Hk & MLE & MOK & HC & HP).
destruct HP as (HCG0 & HBL & Hres & R18 & R19 & R20).
pose proof HCG0 as (HIa & HD3 & HDid & HR23 & R22 & R26 & R21 & R27 & R24 & R25 & V176 & V160 & V120 & V112).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (pa_base_lo (PL := PL_identb)) as HBLO. pose proof asan_consts as (C1 & _).
pose proof HC as HC0. pose proof (proj1 HJ) as HAR.
destruct (g_facts g pos mf _ ly S W regs mem md HJ Hfr HC) as
  (Hsp & Hceil & Hsp47 & Hsp16 & Hmf & Hmf32 & HF4096 & HFceil & HF32 & EF).
assert (HSTKv : STK_LLVMF = 16736) by reflexivity.
assert (HFWv : reac_identity_fw_str.REAC_IDENTITY_FW_STR_STK = 4112) by reflexivity.
assert (Hmf0 : 0 <= mf) by (clear - Hmf Hceil C1 HSTK HSTKv; lia).
assert (Hmf64 : mf + 256 <= 2 ^ 64) by (clear - Hmf Hsp47; lia).
assert (Hmc : alloc_ceiling <= mf) by (clear - Hmf Hceil C1 HSTK HSTKv; lia).
assert (Hc47 : alloc_ceiling <= 2 ^ 47) by (clear - C1; lia).
assert (Hcap : 0 <= SlotModel.t_cap_fw (e_pl g) < 16)
  by (unfold SlotModel.t_cap_fw; apply Z.mod_pos_bound; lia).
destruct HC as (_ & R9 & _ & _ & _ & Rgp & Rtp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & HPRE & _).
pose proof (g_anyfw_range g) as Hfw.
pose proof (g_blk_in g ly S _ _ HBL) as Hbin.
destruct (al_blocks _ _ LAWS ly S W mem md _ _ HAR Hbin) as (Hr16 & Hr4096 & Hrceil & _ & HrPres & _).
pose proof (req_size_pos (Z.max (SlotModel.t_cap_fw (e_pl g)) 1) ltac:(lia)) as [Hreq1 Hreqge].
assert (Hnent : ~ In (res, Z.max (SlotModel.t_cap_fw (e_pl g)) 1) (ablocks B (e_ly g) (e_S g)))
  by exact (g_new_not_entry g ly S W mem md res _ HAR HBL ltac:(lia)).
assert (Hn7 : reac_identity_fw_str.fw_n (SlotModel.t_any_fw (e_pl g)) <= 7).
{ destruct (Z_lt_ge_dec (SlotModel.t_any_fw (e_pl g)) 10000);
  [rewrite reac_identity_fw_str.fw_n_short by lia | rewrite reac_identity_fw_str.fw_n_long by lia]; lia. }
(* the run: mv a0,s8; mv a1,s4; mv a2,s2; jal *)
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HS : st_ok_pi SEGS VAL E (mkSS 0x1154 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x1154)) mem (seg_rom SEGS)))).
{ subst E. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full;
  [apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | exact I
  | split; [cbn [atoms_ok f_atoms]; exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS buf_of.Bx_BO [] E (mrestrict (w_H W) mem)) by constructor.
clear HE.
unfold cfg_at. change (w64 (BASE + 0x1154)) with (Z_to_bv 64 (BASE + 0x1154)).
paj_run_tok RUN HS HJ SHOK buf_of.Bspan_BO; [awr_ok_tac |].
(* the state at reac_identity_fw_str's entry *)
assert (Emem : forall x : word, ms_mem ms x = mem x) by (intros x; apply HF; intros (r & [] & _)).
assert (Hview : forall a, aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
  by (intros a; apply aview_eq_of; unfold mrestrict; rewrite Emem; reflexivity).
assert (HK : g_kept g pos mf W mem W (ms_mem ms)) by (intros a _; exact (Hview a)).
assert (HRE : g_regs_eq regs (ms_regs ms))
  by (exact (g_regs_eq_of_st_ok E _ ms (w_H W) regs [] HS HAE ltac:(vm_compute; reflexivity))).
assert (HC' : ECOMMON g pos mf ly S W (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md))
  by (exact (g_ec_kept g pos mf ly S W regs mem md ly S W (ms_regs ms) (ms_mem ms) _ _ HC0 HJ HRE HK)).
assert (HCG : g_CG g pos mf W (ms_regs ms) (ms_mem ms)).
{ eapply (g_cg_kept g pos mf W W regs (ms_regs ms) mem (ms_mem ms)).
  - exact HCG0.
  - exact HRE.
  - exact HK.
  - apply mod32_mod8; exact HF32.
  - exact Hmf0.
  - exact Hmf64. }
assert (HBLm : hblocks B g ly S [(res, Z.max (SlotModel.t_cap_fw (e_pl g)) 1)]) by exact HBL.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (19%bv : bv 5) Rs3. prreg HS (20%bv : bv 5) Rs4. prreg HS (18%bv : bv 5) Rs2.
rewrite (EE 2%nat 2%bv eq_refl) in Rsp. rewrite (EE 20%nat 20%bv eq_refl), R20 in Ra1, Rs4.
rewrite (EE 18%nat 18%bv eq_refl), R18 in Ra2, Rs2.
rewrite (EE 24%nat 24%bv eq_refl), R24 in Ra0. rewrite (EE 19%nat 19%bv eq_refl), R19 in Rs3.
assert (Qsp : spZ (ms_regs ms) = mf) by (unfold spZ; rewrite Rsp; exact Hsp).
destruct (al_blocks _ _ LAWS ly S W (ms_mem ms) _ _ _ (proj1 HJ) Hbin) as (_ & _ & _ & _ & HrPresM & _).
pmkst HS. rewrite (PSIG IB_reac_identity_fw_str AF_reac_identity_fw_str eq_refl).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) ?Q =>
  change (SRr SEGS W (cfg_at SEGS (BASE + AF_reac_identity_fw_str) rg mm mdx) Q) end.
eapply SRr_mono.
{ apply (HFWS LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly S W (ms_mem ms) _
    (4 * Z.of_nat (m_nrec g) + 1) (ms_regs ms) (SlotModel.t_any_fw (e_pl g)) res (SlotModel.t_cap_fw (e_pl g)) HJ).
  - rewrite Rra. apply ret_ok_codeptr_v; [clear - HBASE; lia | reflexivity].
  - exact Ra0.
  - exact Ra1.
  - exact Ra2.
  - exact Hfw.
  - clear - Hres Hrceil Hreq1 Hc47; split; lia.
  - clear - Hcap; split; lia.
  - rewrite Qsp. apply g_mod16. exact Hmf32.
  - rewrite Qsp, HFWv. clear - Hmf HSTK HSTKv. lia.
  - rewrite Qsp. clear - Hmf. lia.
  - intros Hw. unfold reac_identity_fw_str.fw_writes in Hw. apply andb_prop in Hw as [_ Hc8].
    apply Z.leb_le in Hc8.
    assert (Hn0 : 0 < reac_identity_fw_str.fw_n (SlotModel.t_any_fw (e_pl g))).
    { destruct (Z_lt_ge_dec (SlotModel.t_any_fw (e_pl g)) 10000);
      [rewrite reac_identity_fw_str.fw_n_short by lia | rewrite reac_identity_fw_str.fw_n_long by lia]; lia. }
    assert (Hfit : res + reac_identity_fw_str.fw_n (SlotModel.t_any_fw (e_pl g)) <= res + req_size (Z.max (SlotModel.t_cap_fw (e_pl g)) 1)) by lia.
    split; [|split].
    + intros a Ha. left. exists res, (Z.max (SlotModel.t_cap_fw (e_pl g)) 1). split; [exact Hbin | lia].
    + intros a Ha. rewrite Qsp.
      destruct (HrPresM a ltac:(lia)) as (Hap & Hno). split; [|split; [|split]].
      * right; right; left. exists res, (Z.max (SlotModel.t_cap_fw (e_pl g)) 1).
        split; [exact Hbin|]. split; [exact Hnent | lia].
      * exact Hap.
      * exact Hno.
      * unfold ESTACK. clear - Ha Hfit Hrceil Hmc Hmf Hceil HSTK HSTKv. lia.
    + eapply (range_addressable_of_block SEGS B LAWS ly S W (ms_mem ms) _ res); [exact (proj1 HJ) | exact Hbin | lia | lia]. }
cbv beta. intros W2 c2 _ Hpost.
destruct Hpost as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HPres & Hfrs & Hperm & Hif).
assert (HKc : g_kept g pos mf W (ms_mem ms) W2 mem2).
{ destruct (reac_identity_fw_str.fw_writes res (SlotModel.t_cap_fw (e_pl g))) eqn:Hw.
  - destruct Hif as (_ & _ & Htcj).
    unfold reac_identity_fw_str.fw_writes in Hw. apply andb_prop in Hw as [_ Hc8]. apply Z.leb_le in Hc8.
    rewrite Qsp in Htcj.
    apply (g_kept_tcj g pos mf _ ly S W (ms_mem ms) _ W2 mem2 _ Htcj (proj1 HJ) ltac:(rewrite Hfr; left; reflexivity) EF).
    + rewrite HFWv. clear - Hmf Hceil HSTK HSTKv. lia.
    + intros a Ha. exists res, (Z.max (SlotModel.t_cap_fw (e_pl g)) 1). split; [exact Hbin|].
      split; [lia|]. intros Hn. exact (g_res_ne_inp g ly S W mem md res _ HAR HBL HPRE ltac:(lia) Hn).
    + intros Hn. exact (g_inp g ly S _ HBL HPRE Hn).
  - destruct Hif as (_ & Htcj). rewrite Qsp in Htcj.
    apply (g_kept_tcj g pos mf _ ly S W (ms_mem ms) _ W2 mem2 _ Htcj (proj1 HJ) ltac:(rewrite Hfr; left; reflexivity) EF).
    + rewrite HFWv. clear - Hmf Hceil HSTK HSTKv. lia.
    + intros a [].
    + intros Hn. exact (g_inp g ly S _ HBL HPRE Hn). }
assert (HREc : g_regs_eq (ms_regs ms) regs2) by (apply g_regs_eq_pres; exact HPres).
exists ly2, S2, regs2, mem2, md2.
split; [rewrite Rra; reflexivity|].
split; [exact HJ2|].
split; [rewrite Hfrs; exact Hfr|].
split; [exact Hk|].
split.
{ pose proof (mle_station MT _ _ _ _ _ MTL MLE (HMT0 S S2)) as X. rewrite Z.add_0_r in X. exact X. }
split.
{ apply (mok_station MT S S2 ((EV_LLVMF - (4 * Z.of_nat (m_nrec g) + 1)) * MEV MT) 0); [exact MTL | exact MOK | exact (HMT0 S S2) | | lia].
  pose proof g_mev_pos. clear - H Hk. nia. }
split.
{ exact (g_ec_kept g pos mf ly S W (ms_regs ms) (ms_mem ms) _ ly2 S2 W2 regs2 mem2 md2 _ HC' HJ2 HREc HKc). }
split.
{ eapply (g_cg_kept g pos mf W W2 (ms_regs ms) regs2 (ms_mem ms) mem2);
  [exact HCG | exact HREc | exact HKc | apply mod32_mod8; exact HF32 | exact Hmf0 | exact Hmf64]. }
split.
{ destruct HBL as (HPm & HFa). split; [eapply Permutation_trans; [exact Hperm | exact HPm] | exact HFa]. }
split; [exact Hres|].
split; [rewrite (g_pres_reg (ms_regs ms) regs2 18%bv HPres ltac:(vm_compute; reflexivity)); exact Rs2|].
split; [rewrite (g_pres_reg (ms_regs ms) regs2 19%bv HPres ltac:(vm_compute; reflexivity)); exact Rs3|].
split; [rewrite (g_pres_reg (ms_regs ms) regs2 20%bv HPres ltac:(vm_compute; reflexivity)); exact Rs4|].
destruct (reac_identity_fw_str.fw_writes res (SlotModel.t_cap_fw (e_pl g))).
- destruct Hif as (Ha0' & Hgar & _). split; [exact Ha0' | exact Hgar].
- destruct Hif as (Ha0' & _). exact Ha0'.
Qed.
Lemma g_p3b : forall g pos mf res W c,
  ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 1) (BASE + 0x1164)
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       g_CG g pos mf W2 regs2 mem2 /\
       hblocks B g ly2 S2 [(res, Z.max (SlotModel.t_cap_fw (e_pl g)) 1)] /\ 4096 <= res /\
       getr regs2 18 = w64 (SlotModel.t_cap_fw (e_pl g)) /\
       getr regs2 19 = w64 (SFa g pos + V_id) /\ getr regs2 20 = w64 res /\
       (if reac_identity_fw_str.fw_writes res (SlotModel.t_cap_fw (e_pl g)) then
          getr regs2 10 = w64 (reac_identity_fw_str_c.L (SlotModel.t_any_fw (e_pl g))) /\
          garr8 SEGS (rd W2 mem2) res (reac_identity_fw_str.fw_bytes (SlotModel.t_any_fw (e_pl g)))
        else getr regs2 10 = w64 (-1))) W c ->
  SRr SEGS W c (ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 1) (BASE + 0x1170)
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       g_CG g pos mf W2 regs2 mem2 /\
       hblocks B g ly2 S2 [(res, Z.max (SlotModel.t_cap_fw (e_pl g)) 1)] /\ 4096 <= res /\
       getr regs2 18 = w64 (SlotModel.t_cap_fw (e_pl g)) /\
       getr regs2 19 = w64 (SFa g pos + V_id) /\ getr regs2 20 = w64 res)).
Proof.
intros g pos mf res W c (ly & S & regs & mem & md & -> & HJ & Hfr & Hk & MLE & MOK & HC & HP).
destruct HP as (HCG0 & HBL & Hres & R18 & R19 & R20 & Hif).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & _). pose proof HC as HC0. pose proof (proj1 HJ) as HAR.
destruct (g_facts g pos mf _ ly S W regs mem md HJ Hfr HC) as
  (Hsp & Hceil & Hsp47 & Hsp16 & Hmf & Hmf32 & HF4096 & HFceil & HF32 & EF).
assert (HSTKv : STK_LLVMF = 16736) by reflexivity.
assert (Hmf0 : 0 <= mf) by (clear - Hmf Hceil C1 HSTK HSTKv; lia).
assert (Hmf64 : mf + 256 <= 2 ^ 64) by (clear - Hmf Hsp47; lia).
assert (Hcap : 0 <= SlotModel.t_cap_fw (e_pl g) < 16)
  by (unfold SlotModel.t_cap_fw; apply Z.mod_pos_bound; lia).
destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & HPRE & _).
pose proof (g_anyfw_range g) as Hfw.
pose proof (g_blk_in g ly S _ _ HBL) as Hbin.
(* the run: mv a1,s4; mv a2,s2; jal *)
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HS : st_ok_pi SEGS VAL E (mkSS 0x1164 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x1164)) mem (seg_rom SEGS)))).
{ subst E. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full;
  [apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | exact I
  | split; [cbn [atoms_ok f_atoms]; exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS buf_of.Bx_BO [] E (mrestrict (w_H W) mem)) by constructor.
clear HE.
unfold cfg_at. change (w64 (BASE + 0x1164)) with (Z_to_bv 64 (BASE + 0x1164)).
paj_run_tok RUN HS HJ SHOK buf_of.Bspan_BO; [awr_ok_tac |].
assert (Emem : forall x : word, ms_mem ms x = mem x) by (intros x; apply HF; intros (r & [] & _)).
assert (Hview : forall a, aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
  by (intros a; apply aview_eq_of; unfold mrestrict; rewrite Emem; reflexivity).
assert (HK : g_kept g pos mf W mem W (ms_mem ms)) by (intros a _; exact (Hview a)).
assert (HRE : g_regs_eq regs (ms_regs ms))
  by (exact (g_regs_eq_of_st_ok E _ ms (w_H W) regs [] HS HAE ltac:(vm_compute; reflexivity))).
assert (HC' : ECOMMON g pos mf ly S W (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md))
  by (exact (g_ec_kept g pos mf ly S W regs mem md ly S W (ms_regs ms) (ms_mem ms) _ _ HC0 HJ HRE HK)).
assert (HCG : g_CG g pos mf W (ms_regs ms) (ms_mem ms)).
{ eapply (g_cg_kept g pos mf W W regs (ms_regs ms) mem (ms_mem ms)).
  - exact HCG0.
  - exact HRE.
  - exact HK.
  - apply mod32_mod8; exact HF32.
  - exact Hmf0.
  - exact Hmf64. }
prreg HS (1%bv : bv 5) Rra. prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (18%bv : bv 5) Rs2. prreg HS (19%bv : bv 5) Rs3. prreg HS (20%bv : bv 5) Rs4.
rewrite (EE 10%nat 10%bv eq_refl) in Ra0. rewrite (EE 20%nat 20%bv eq_refl), R20 in Ra1, Rs4.
rewrite (EE 18%nat 18%bv eq_refl), R18 in Ra2, Rs2. rewrite (EE 19%nat 19%bv eq_refl), R19 in Rs3.
pmkst HS. rewrite (PSIG IB_check_str AF_check_str eq_refl).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) ?Q =>
  change (SRr SEGS W (cfg_at SEGS (BASE + AF_check_str) rg mm mdx) Q) end.
assert (Hgen : forall r (bs : list Z), getr regs 10 = w64 r -> - 2 ^ 31 <= r < 2 ^ 31 ->
  (0 <= r -> r < SlotModel.t_cap_fw (e_pl g) /\ r + 1 <= req_size (Z.max (SlotModel.t_cap_fw (e_pl g)) 1) /\
     garr8 SEGS (rd W (ms_mem ms)) res bs /\ Z.of_nat (length bs) = r + 1 /\
     nth (Z.to_nat r) bs 0 = 0 /\ (forall i, (i < Z.to_nat r)%nat -> nth i bs 0 <> 0)) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_check_str) (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md))
    (ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 1) (BASE + 0x1170)
      (fun ly2 S2 W2 regs2 mem2 md2 =>
         g_CG g pos mf W2 regs2 mem2 /\
         hblocks B g ly2 S2 [(res, Z.max (SlotModel.t_cap_fw (e_pl g)) 1)] /\ 4096 <= res /\
         getr regs2 18 = w64 (SlotModel.t_cap_fw (e_pl g)) /\
         getr regs2 19 = w64 (SFa g pos + V_id) /\ getr regs2 20 = w64 res))).
{ intros r bs Hr0 Hr Hstr. eapply SRr_mono.
  { apply (g_chk_call g pos mf _ ly S W (ms_regs ms) (ms_mem ms) _ res (Z.max (SlotModel.t_cap_fw (e_pl g)) 1)
      r (SlotModel.t_cap_fw (e_pl g)) bs 0x1170 HJ Hfr HC' HCG Hbin ltac:(lia)
      (fun Hn => g_inp g ly S _ HBL HPRE Hn) Rra ltac:(clear - HBASE; lia) eq_refl).
    - rewrite Ra0. exact Hr0.
    - exact Ra1.
    - exact Ra2.
    - exact Hr.
    - clear - Hcap; split; lia.
    - exact Hstr. }
  cbv beta. intros W2 c2 _ (regs2 & mem2 & md2 & -> & -> & HJ2 & HPres & HC2 & HCG2 & _).
  exists ly, S, regs2, mem2, md2.
  split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hfr|]. split; [exact Hk|].
  split; [exact MLE|]. split; [exact MOK|]. split; [exact HC2|]. split; [exact HCG2|].
  split; [exact HBL|]. split; [exact Hres|].
  split; [rewrite (g_pres_reg (ms_regs ms) regs2 18%bv HPres ltac:(vm_compute; reflexivity)); exact Rs2|].
  split; [rewrite (g_pres_reg (ms_regs ms) regs2 19%bv HPres ltac:(vm_compute; reflexivity)); exact Rs3|].
  rewrite (g_pres_reg (ms_regs ms) regs2 20%bv HPres ltac:(vm_compute; reflexivity)); exact Rs4. }
destruct (reac_identity_fw_str.fw_writes res (SlotModel.t_cap_fw (e_pl g))) eqn:Hw.
- destruct Hif as (Hr10 & Hgar).
  unfold reac_identity_fw_str.fw_writes in Hw. apply andb_prop in Hw as [_ Hc8]. apply Z.leb_le in Hc8.
  destruct (g_fw_str_ok (SlotModel.t_any_fw (e_pl g)) Hfw) as (Hlen & Hlast & Hnz & HLr).
  apply (Hgen _ (reac_identity_fw_str.fw_bytes (SlotModel.t_any_fw (e_pl g))) Hr10 ltac:(lia)).
  intros _. split; [lia|]. split; [pose proof (req_size_pos (Z.max (SlotModel.t_cap_fw (e_pl g)) 1) ltac:(lia)) as [_ Q]; lia|].
  split; [eapply g_garr8_kept; [|exact Hgar]; intros j _; exact (Hview (res + j))|].
  split; [exact Hlen|]. split; [exact Hlast | exact Hnz].
- apply (Hgen (-1) [] Hif ltac:(lia)). intros Hneg. lia.
Qed.

(* ---- free of a buffer the segment allocated, at the wrapper's entry (0x818e8, 0x81924) -------------- *)
Lemma g_free_call : forall g pos mf k ly S (W : world SEGS) regsc memc mdc res n retk,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly S W memc mdc k ->
  frames S = [(4, pos)] -> 0 <= k -> k + 1 <= EV_LLVMF ->
  mo_le MT (e_S g) S (k * MEV MT) -> mo_ok MT S ((EV_LLVMF - k) * MEV MT) ->
  ECOMMON g pos mf ly S W regsc memc mdc -> g_CG g pos mf W regsc memc ->
  hblocks B g ly S [(res, n)] -> 0 <= n ->
  getr regsc 1 = Z_to_bv 64 (BASE + retk) -> In retk LLVMF_FREE_RAS -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr regsc 10 = w64 res ->
  SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (pc_wrap_free (as_code B))) memc (seg_rom SEGS)) mdc)
    (fun W2 c2 => exists ly2 S2 regs2 mem2 md2, c2 = cfg_at SEGS (BASE + retk) regs2 mem2 md2 /\
       ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
         ly2 S2 W2 mem2 md2 (k + 1) /\
       frames S2 = [(4, pos)] /\ mo_le MT (e_S g) S2 ((k + 1) * MEV MT) /\
       mo_ok MT S2 ((EV_LLVMF - (k + 1)) * MEV MT) /\
       ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 /\ g_CG g pos mf W2 regs2 mem2 /\
       hblocks B g ly2 S2 [] /\ aregs_preserved regsc regs2).
Proof.
intros g pos mf k ly S W regsc memc mdc res n retk HJ Hfr Hk0 Hk1 MLE MOK HC HCG HBL Hn0 Rra Hras Hrk Hrk2 Ra0.
pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_identb)) as HBLO. pose proof asan_consts as (C1 & _).
pose proof (proj1 HJ) as HAR.
destruct (g_facts g pos mf _ ly S W regsc memc mdc HJ Hfr HC) as
  (Hsp & Hceil & Hsp47 & Hsp16 & Hmf & Hmf32 & HF4096 & HFceil & HF32 & EF).
assert (HSTKv : STK_LLVMF = 16736) by reflexivity.
assert (HASv : ASTACK = 16384) by reflexivity.
assert (HEVv : EV_LLVMF = 266) by reflexivity.
assert (Hmf0 : 0 <= mf) by (clear - Hmf Hceil C1 HSTK HSTKv; lia).
assert (Hmf64 : mf + 256 <= 2 ^ 64) by (clear - Hmf Hsp47; lia).
pose proof HC as HC0.
destruct HC as (_ & _ & R8 & _ & _ & Rgp & Rtp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & HPRE & _).
destruct (g_epre_bud g HPRE) as (Hnev0 & _ & _ & _).
pose proof (g_blk_in g ly S _ _ HBL) as Hbin.
destruct (al_blocks _ _ LAWS ly S W memc mdc res n HAR Hbin) as (_ & Hr4096 & Hrceil & _).
pose proof (req_size_pos n Hn0) as [Hreq1 _].
assert (Hnent : ~ In (res, n) (ablocks B (e_ly g) (e_S g))) by exact (g_new_not_entry g ly S W memc mdc res n HAR HBL Hn0).
destruct (g_chain g pos mf _ ly S W regsc memc _ HJ HC0) as (ch & Hch & Hchsp).
assert (Hs0 : s0Z regsc = e_sp0 g)
  by (unfold s0Z; rewrite R8; apply unsigned_lit_small; clear - Hceil C1 HSTK HSTKv Hsp47; lia).
assert (Qra : raZ regsc = BASE + retk) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear - HBASE Hrk; lia).
eapply SRr_mono.
{ apply (AFREE4 W regsc memc LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly S mdc k res n (mf - e_sp0 g) (getr regsc 1) ch HJ Hbin Ra0).
  - clear - Hsp; lia.
  - rewrite Zminus_mod, (g_mod16 mf Hmf32), Hsp16; reflexivity.
  - clear - Hmf; lia.
  - rewrite HASv. clear - Hmf HSTK HSTKv. lia.
  - exact Rgp.
  - exact Rtp.
  - reflexivity.
  - rewrite Rra. apply ret_ok_codeptr_v; [exact Hrk | exact Hrk2].
  - pose proof (g_nev g pos _ ly S W memc mdc HJ). clear - H Hnev0 HEV Hk1 HEVv. lia.
  - apply (achain_chain_pre ly _ mf (e_sp0 g) ch regsc Hch).
    + rewrite Hsp. clear - Hmf Hceil C1 HSTK HSTKv. lia.
    + exact Hs0.
    + rewrite Qra. clear - HBLO Hrk. lia.
  - rewrite call_trace_of_spine. apply HUMF. rewrite Qra.
    unfold LLVMF_FREE_CTX. apply in_or_app. destruct Hchsp as [-> | ->]; cbn [spine map fst snd].
    + left. exact (in_map (fun o => [BASE + o; RA_LLVMF]) LLVMF_FREE_RAS retk Hras).
    + right. exact (in_map (fun o => [BASE + o]) LLVMF_FREE_RAS retk Hras).
  - intros Hin. exfalso. exact (Hnent Hin).
  - eapply (mo_ok_le MT MTL); [exact MOK|]. pose proof g_free_mev. pose proof g_mev_pos.
    clear - H H0 Hk1. nia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HPres & (l1 & l2 & Eb1 & Eb2) & Hfrs & Hack & MLE2).
assert (HKc : g_kept g pos mf W memc W2 mem2).
{ replace (e_sp0 g + (mf - e_sp0 g)) with mf in Hack by (clear; lia).
  apply (g_kept_ack g pos mf (mf - ASTACK) ly S W memc mdc W2 mem2 _ Hack HAR ltac:(rewrite Hfr; left; reflexivity) EF).
  - rewrite HASv. clear - Hmf Hceil HSTK HSTKv C1. lia.
  - intros a Ha. exists res, n. split; [exact Hbin|]. split; [exact Ha|].
    intros Hn. exact (g_res_ne_inp g ly S W memc mdc res n HAR HBL HPRE Hn0 Hn).
  - intros Hn. exact (g_inp g ly S _ HBL HPRE Hn). }
assert (HREc : g_regs_eq regsc regs2) by (apply g_regs_eq_pres; exact HPres).
exists ly2, S2, regs2, mem2, md2.
split; [unfold cfg_at; rewrite Rra; reflexivity|].
split; [exact HJ2|].
split; [rewrite Hfrs; exact Hfr|].
split.
{ eapply (mle_weaken MT _ _ (k * MEV MT + mo_free MT)); [exact MTL | exact (mle_station MT _ _ _ _ _ MTL MLE MLE2)|].
  pose proof g_free_mev. clear - H. nia. }
split.
{ eapply (mok_station MT S S2 ((EV_LLVMF - k) * MEV MT) (mo_free MT)); [exact MTL | exact MOK | exact MLE2 | |].
  - pose proof g_mev_pos. clear - H Hk1. nia.
  - pose proof g_free_mev. clear - H. nia. }
split; [exact (g_ec_kept g pos mf ly S W regsc memc mdc ly2 S2 W2 regs2 mem2 md2 _ HC0 HJ2 HREc HKc)|].
split; [eapply (g_cg_kept g pos mf W W2 regsc regs2 memc mem2);
  [exact HCG | exact HREc | exact HKc | apply mod32_mod8; exact HF32 | exact Hmf0 | exact Hmf64]|].
split; [|exact HPres].
destruct HBL as (HPm & _). split; [|apply Forall_nil]. rewrite Eb2. cbn [app].
rewrite Eb1 in HPm. cbn [app] in HPm.
apply (Permutation_cons_inv (a := (res, n))).
eapply Permutation_trans; [apply Permutation_middle | exact HPm].
Qed.

(* ---- piece 4: free of the firmware buffer at +0x1174 ------------------------------------------------- *)
Lemma g_p4 : forall g pos mf res W c,
  ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 1) (BASE + 0x1170)
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       g_CG g pos mf W2 regs2 mem2 /\
       hblocks B g ly2 S2 [(res, Z.max (SlotModel.t_cap_fw (e_pl g)) 1)] /\ 4096 <= res /\
       getr regs2 18 = w64 (SlotModel.t_cap_fw (e_pl g)) /\
       getr regs2 19 = w64 (SFa g pos + V_id) /\ getr regs2 20 = w64 res) W c ->
  SRr SEGS W c (ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 2) (BASE + 0x1178)
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       g_CG g pos mf W2 regs2 mem2 /\ hblocks B g ly2 S2 [] /\ getr regs2 19 = w64 (SFa g pos + V_id))).
Proof.
intros g pos mf res W c (ly & S & regs & mem & md & -> & HJ & Hfr & Hk & MLE & MOK & HC & HP).
destruct HP as (HCG0 & HBL & Hres & R18 & R19 & R20).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & _). pose proof HC as HC0.
destruct (g_facts g pos mf _ ly S W regs mem md HJ Hfr HC) as
  (Hsp & Hceil & Hsp47 & Hsp16 & Hmf & Hmf32 & HF4096 & HFceil & HF32 & EF).
assert (HSTKv : STK_LLVMF = 16736) by reflexivity.
assert (HEVv : EV_LLVMF = 266) by reflexivity.
assert (Hmf0 : 0 <= mf) by (clear - Hmf Hceil C1 HSTK HSTKv; lia).
assert (Hmf64 : mf + 256 <= 2 ^ 64) by (clear - Hmf Hsp47; lia).
assert (Hcap : 0 <= SlotModel.t_cap_fw (e_pl g) < 16)
  by (unfold SlotModel.t_cap_fw; apply Z.mod_pos_bound; lia).
(* the run: mv a0,s4; jal *)
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HS : st_ok_pi SEGS VAL E (mkSS 0x1170 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x1170)) mem (seg_rom SEGS)))).
{ subst E. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full;
  [apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | exact I
  | split; [cbn [atoms_ok f_atoms]; exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS buf_of.Bx_BO [] E (mrestrict (w_H W) mem)) by constructor.
clear HE.
unfold cfg_at. change (w64 (BASE + 0x1170)) with (Z_to_bv 64 (BASE + 0x1170)).
paj_run_tok RUN HS HJ SHOK buf_of.Bspan_BO; [awr_ok_tac |].
assert (Emem : forall x : word, ms_mem ms x = mem x) by (intros x; apply HF; intros (r & [] & _)).
assert (Hview : forall a, aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
  by (intros a; apply aview_eq_of; unfold mrestrict; rewrite Emem; reflexivity).
assert (HK : g_kept g pos mf W mem W (ms_mem ms)) by (intros a _; exact (Hview a)).
assert (HRE : g_regs_eq regs (ms_regs ms))
  by (exact (g_regs_eq_of_st_ok E _ ms (w_H W) regs [] HS HAE ltac:(vm_compute; reflexivity))).
assert (HC' : ECOMMON g pos mf ly S W (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md))
  by (exact (g_ec_kept g pos mf ly S W regs mem md ly S W (ms_regs ms) (ms_mem ms) _ _ HC0 HJ HRE HK)).
assert (HCG : g_CG g pos mf W (ms_regs ms) (ms_mem ms)).
{ eapply (g_cg_kept g pos mf W W regs (ms_regs ms) mem (ms_mem ms)).
  - exact HCG0.
  - exact HRE.
  - exact HK.
  - apply mod32_mod8; exact HF32.
  - exact Hmf0.
  - exact Hmf64. }
prreg HS (1%bv : bv 5) Rra. prreg HS (10%bv : bv 5) Ra0. prreg HS (19%bv : bv 5) Rs3.
rewrite (EE 20%nat 20%bv eq_refl), R20 in Ra0. rewrite (EE 19%nat 19%bv eq_refl), R19 in Rs3.
pmkst HS. ppcs.
eapply SRr_mono.
{ apply (g_free_call g pos mf _ ly S W (ms_regs ms) (ms_mem ms) _ res (Z.max (SlotModel.t_cap_fw (e_pl g)) 1) 0x1178
    HJ Hfr ltac:(clear - Hk; lia) ltac:(clear - Hk HEVv; lia) MLE MOK HC' HCG HBL ltac:(lia) Rra
    ltac:(unfold LLVMF_FREE_RAS; cbn; tauto) ltac:(clear - HBASE; lia) eq_refl Ra0). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & Hfr2 & MLE2 & MOK2 & HC2 & HCG2 & HBL2 & HPres).
exists ly2, S2, regs2, mem2, md2.
replace (4 * Z.of_nat (m_nrec g) + 1 + 1) with (4 * Z.of_nat (m_nrec g) + 2) in HJ2, MLE2, MOK2 by (clear; lia).
split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hfr2|]. split; [clear - Hk HEVv; lia|].
split; [exact MLE2|]. split; [exact MOK2|]. split; [exact HC2|]. split; [exact HCG2|]. split; [exact HBL2|].
rewrite (g_pres_reg (ms_regs ms) regs2 19%bv HPres ltac:(vm_compute; reflexivity)). exact Rs3.
Qed.

(* ---- buf_of at its entry with no segment buffer live (0x8189c is piece 1's own; 0x818f0) ------------- *)
Lemma g_buf_call : forall g pos mf k ly S (W : world SEGS) regsc memc mdc n retk,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly S W memc mdc k ->
  frames S = [(4, pos)] -> 0 <= k -> k + 1 <= EV_LLVMF ->
  mo_le MT (e_S g) S (k * MEV MT) -> mo_ok MT S ((EV_LLVMF - k) * MEV MT) ->
  ECOMMON g pos mf ly S W regsc memc mdc -> g_CG g pos mf W regsc memc -> hblocks B g ly S [] ->
  getr regsc 1 = Z_to_bv 64 (BASE + retk) -> In retk BUF_OF_RAS -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr regsc 10 = w64 n -> 0 <= n < 256 ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_buf_of) regsc memc mdc)
    (fun W2 c2 => exists res ly2 S2 regs2 mem2 md2, c2 = cfg_at SEGS (BASE + retk) regs2 mem2 md2 /\
       ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
         ly2 S2 W2 mem2 md2 (k + 1) /\
       frames S2 = [(4, pos)] /\ mo_le MT (e_S g) S2 ((k + 1) * MEV MT) /\
       mo_ok MT S2 ((EV_LLVMF - (k + 1)) * MEV MT) /\
       ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 /\ g_CG g pos mf W2 regs2 mem2 /\
       hblocks B g ly2 S2 [(res, Z.max n 1)] /\ 4096 <= res /\ getr regs2 10 = w64 res /\
       aregs_preserved regsc regs2).
Proof.
intros g pos mf k ly S W regsc memc mdc n retk HJ Hfr Hk0 Hk1 MLE MOK HC HCG HBL Rra Hras Hrk Hrk2 Ra0 Hn.
pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_identb)) as HBLO. pose proof asan_consts as (C1 & _).
pose proof (proj1 HJ) as HAR.
destruct (g_facts g pos mf _ ly S W regsc memc mdc HJ Hfr HC) as
  (Hsp & Hceil & Hsp47 & Hsp16 & Hmf & Hmf32 & HF4096 & HFceil & HF32 & EF).
assert (HSTKv : STK_LLVMF = 16736) by reflexivity.
assert (HBOv : buf_of.BUF_OF_STK = 16400) by reflexivity.
assert (HEVv : EV_LLVMF = 266) by reflexivity.
assert (HLv : LIVE_LLVMF = 511) by reflexivity.
assert (Hmf0 : 0 <= mf) by (clear - Hmf Hceil C1 HSTK HSTKv; lia).
assert (Hmf64 : mf + 256 <= 2 ^ 64) by (clear - Hmf Hsp47; lia).
assert (HmfS : alloc_ceiling <= mf - buf_of.BUF_OF_STK <= mf) by (clear - Hmf Hceil C1 HSTK HSTKv HBOv; lia).
pose proof HC as HC0.
destruct HC as (_ & _ & R8 & _ & _ & Rgp & Rtp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & HPRE & _).
destruct (g_epre_bud g HPRE) as (Hnev0 & Hlive0 & _ & _).
destruct (g_chain g pos mf _ ly S W regsc memc _ HJ HC0) as (ch & Hch & Hchsp).
assert (Hs0 : s0Z regsc = e_sp0 g)
  by (unfold s0Z; rewrite R8; apply unsigned_lit_small; clear - Hceil C1 HSTK HSTKv Hsp47; lia).
assert (Qra : raZ regsc = BASE + retk) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear - HBASE Hrk; lia).
unfold cfg_at. change (w64 (BASE + AF_buf_of)) with (Z_to_bv 64 (BASE + AF_buf_of)).
eapply SRr_mono.
{ eapply (cl_callS B LAWS) with (STK1 := buf_of.BUF_OF_STK) (FP1 := []) (EV1 := buf_of.EV_BUF_OF)
    (o := mf - e_sp0 g) (ch1 := ch) (raw := getr regsc 1)
    (K := fun ly2 S2 (W2 : world SEGS) regs2 (mem2 : word -> option byte) (md2 : Model) => exists res : Z,
       getr regs2 10 = w64 res /\ 4096 <= res /\ frames S2 = frames S /\
       ablocks B ly2 S2 = ablocks B ly S ++ [(res, Z.max n 1)] /\
       mo_le MT S S2 (mo_malloc MT (Z.max n 1))).
  - exact HJ.
  - clear - Hsp; lia.
  - rewrite Zminus_mod, (g_mod16 mf Hmf32), Hsp16; reflexivity.
  - clear - Hmf; lia.
  - rewrite HBOv; lia.
  - rewrite HBOv. clear - Hmf HSTK HSTKv. lia.
  - exact Rgp.
  - exact Rtp.
  - reflexivity.
  - rewrite Rra. apply ret_ok_codeptr_v; [exact Hrk | exact Hrk2].
  - change (4096 <= raZ regsc); rewrite Qra; clear - HBLO Hrk; lia.
  - replace (e_sp0 g + (mf - e_sp0 g)) with mf by (clear; lia). rewrite Hs0; exact Hch.
  - intros HPRE2.
    exact (HBUF ly S W regsc memc mdc ch n HPRE2
      ltac:(rewrite Qra; unfold CTX_BUF_OF; apply in_or_app; destruct Hchsp as [-> | ->]; cbn [spine map fst snd];
        [left; exact (in_map (fun o => [BASE + o; RA_LLVMF]) BUF_OF_RAS retk Hras)
        | right; exact (in_map (fun o => [BASE + o]) BUF_OF_RAS retk Hras)])
      Ra0 ltac:(unfold MALLOC_MAX; clear - Hn; lia)
      ltac:(unfold buf_of.EV_BUF_OF; pose proof (g_nev g pos _ ly S W memc mdc HJ);
            clear - Hnev0 HEV Hk1 HEVv H; lia)
      ltac:(rewrite (g_live g ly S [] HBL); cbn [bsum fold_right]; clear - Hlive0 HLIVE HLv Hn; lia)
      ltac:(eapply (mo_ok_le MT MTL); [exact MOK|];
            pose proof (g_malloc_mev (Z.max n 1) ltac:(clear - Hn; lia));
            pose proof g_mev_pos; clear - H H0 Hk1; nia)).
  - intros a (r & [] & _). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJsub & HPres & res & Ha0 & Hres & Hfrs & Eab & MLE2).
assert (HKc : g_kept g pos mf W memc W2 mem2).
{ replace (e_sp0 g + (mf - e_sp0 g)) with mf in HJsub by (clear; lia).
  apply (g_kept_subj g pos mf buf_of.BUF_OF_STK [] ly S W memc _ ly2 S2 W2 mem2 md2 buf_of.EV_BUF_OF HJsub HAR
    ltac:(rewrite Hfr; left; reflexivity) EF HmfS).
  - intros a (r & [] & _).
  - intros Hn0. split; [exact (g_inp g ly S [] HBL HPRE Hn0)|].
    rewrite Eab; apply in_or_app; left; exact (g_inp g ly S [] HBL HPRE Hn0). }
assert (HREc : g_regs_eq regsc regs2) by (apply g_regs_eq_pres; exact HPres).
exists res, ly2, S2, regs2, mem2, md2.
split; [unfold cfg_at; rewrite Rra; reflexivity|].
split; [exact HJ2|].
split; [rewrite Hfrs; exact Hfr|].
split.
{ eapply (mle_weaken MT _ _ (k * MEV MT + mo_malloc MT (Z.max n 1)));
  [exact MTL | exact (mle_station MT _ _ _ _ _ MTL MLE MLE2)|].
  pose proof (g_malloc_mev (Z.max n 1) ltac:(clear - Hn; lia)). clear - H. nia. }
split.
{ eapply (mok_station MT S S2 ((EV_LLVMF - k) * MEV MT) (mo_malloc MT (Z.max n 1)));
  [exact MTL | exact MOK | exact MLE2 | |].
  - pose proof g_mev_pos. clear - H Hk1. nia.
  - pose proof (g_malloc_mev (Z.max n 1) ltac:(clear - Hn; lia)). clear - H. nia. }
split; [exact (g_ec_kept g pos mf ly S W regsc memc mdc ly2 S2 W2 regs2 mem2 md2 _ HC0 HJ2 HREc HKc)|].
split; [eapply (g_cg_kept g pos mf W W2 regsc regs2 memc mem2);
  [exact HCG | exact HREc | exact HKc | apply mod32_mod8; exact HF32 | exact Hmf0 | exact Hmf64]|].
split.
{ split; [|apply Forall_cons; [cbn; split; [exact Hres | clear - Hn; lia] | apply Forall_nil]].
  rewrite Eab. destruct HBL as (HPm & _).
  eapply Permutation_trans; [apply Permutation_app_tail; exact HPm|].
  cbn [app]. apply Permutation_app_comm. }
split; [exact Hres|]. split; [exact Ha0 | exact HPres].
Qed.

Lemma g_nrec_le : forall g, Z.of_nat (m_nrec g) <= 64.
Proof.
intros g. unfold m_nrec, SlotModel.nrecn. pose proof (SlotModel.nrec_range (e_pl g)) as R.
rewrite Z2Nat.id by lia. lia.
Qed.
(* ---- piece 5: buf_of (cap_ver) at +0x117c --------------------------------------------------------- *)
Lemma g_p5 : forall g pos mf W c,
  ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 2) (BASE + 0x1178)
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       g_CG g pos mf W2 regs2 mem2 /\ hblocks B g ly2 S2 [] /\ getr regs2 19 = w64 (SFa g pos + V_id)) W c ->
  SRr SEGS W c (fun W3 c3 => exists res,
    ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 3) (BASE + 0x1180)
      (fun ly2 S2 W2 regs2 mem2 md2 =>
         g_CG g pos mf W2 regs2 mem2 /\
         hblocks B g ly2 S2 [(res, Z.max (SlotModel.t_cap_ver (e_pl g)) 1)] /\
         4096 <= res /\ getr regs2 10 = w64 res /\ getr regs2 19 = w64 (SFa g pos + V_id)) W3 c3).
Proof.
intros g pos mf W c (ly & S & regs & mem & md & -> & HJ & Hfr & Hk & MLE & MOK & HC & HP).
destruct HP as (HCG0 & HBL & R19).
pose proof HCG0 as (_ & _ & _ & _ & R22 & _).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & _). pose proof HC as HC0.
destruct (g_facts g pos mf _ ly S W regs mem md HJ Hfr HC) as
  (Hsp & Hceil & Hsp47 & Hsp16 & Hmf & Hmf32 & HF4096 & HFceil & HF32 & EF).
assert (HSTKv : STK_LLVMF = 16736) by reflexivity.
assert (HEVv : EV_LLVMF = 266) by reflexivity.
assert (Hmf0 : 0 <= mf) by (clear - Hmf Hceil C1 HSTK HSTKv; lia).
assert (Hmf64 : mf + 256 <= 2 ^ 64) by (clear - Hmf Hsp47; lia).
assert (Hcap : 0 <= SlotModel.t_cap_ver (e_pl g) < 32)
  by (unfold SlotModel.t_cap_ver; apply Z.mod_pos_bound; lia).
pose proof (g_nrec_le g) as Hnr.
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HS : st_ok_pi SEGS VAL E (mkSS 0x1178 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x1178)) mem (seg_rom SEGS)))).
{ subst E. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full;
  [apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | exact I
  | split; [cbn [atoms_ok f_atoms]; exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS buf_of.Bx_BO [] E (mrestrict (w_H W) mem)) by constructor.
clear HE.
unfold cfg_at. change (w64 (BASE + 0x1178)) with (Z_to_bv 64 (BASE + 0x1178)).
paj_run_tok RUN HS HJ SHOK buf_of.Bspan_BO; [awr_ok_tac |].
assert (Emem : forall x : word, ms_mem ms x = mem x) by (intros x; apply HF; intros (r & [] & _)).
assert (Hview : forall a, aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
  by (intros a; apply aview_eq_of; unfold mrestrict; rewrite Emem; reflexivity).
assert (HK : g_kept g pos mf W mem W (ms_mem ms)) by (intros a _; exact (Hview a)).
assert (HRE : g_regs_eq regs (ms_regs ms))
  by (exact (g_regs_eq_of_st_ok E _ ms (w_H W) regs [] HS HAE ltac:(vm_compute; reflexivity))).
assert (HC' : ECOMMON g pos mf ly S W (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md))
  by (exact (g_ec_kept g pos mf ly S W regs mem md ly S W (ms_regs ms) (ms_mem ms) _ _ HC0 HJ HRE HK)).
assert (HCG : g_CG g pos mf W (ms_regs ms) (ms_mem ms)).
{ eapply (g_cg_kept g pos mf W W regs (ms_regs ms) mem (ms_mem ms)).
  - exact HCG0.
  - exact HRE.
  - exact HK.
  - apply mod32_mod8; exact HF32.
  - exact Hmf0.
  - exact Hmf64. }
prreg HS (1%bv : bv 5) Rra. prreg HS (10%bv : bv 5) Ra0. prreg HS (19%bv : bv 5) Rs3.
rewrite (EE 22%nat 22%bv eq_refl), R22 in Ra0. rewrite (EE 19%nat 19%bv eq_refl), R19 in Rs3.
pmkst HS. rewrite (PSIG IB_buf_of AF_buf_of eq_refl).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) ?Q =>
  change (SRr SEGS W (cfg_at SEGS (BASE + AF_buf_of) rg mm mdx) Q) end.
eapply SRr_mono.
{ apply (g_buf_call g pos mf _ ly S W (ms_regs ms) (ms_mem ms) _ (SlotModel.t_cap_ver (e_pl g)) 0x1180
    HJ Hfr ltac:(clear - Hk; lia) ltac:(clear - Hnr HEVv; lia) MLE MOK HC' HCG HBL Rra
    ltac:(unfold BUF_OF_RAS; cbn; tauto) ltac:(clear - HBASE; lia) eq_refl Ra0 ltac:(clear - Hcap; lia)). }
cbv beta. intros W2 c2 _ (res & ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & Hfr2 & MLE2 & MOK2 & HC2 & HCG2 & HBL2 & Hres & Ha0 & HPres).
exists res, ly2, S2, regs2, mem2, md2.
replace (4 * Z.of_nat (m_nrec g) + 2 + 1) with (4 * Z.of_nat (m_nrec g) + 3) in HJ2, MLE2, MOK2 by (clear; lia).
split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hfr2|]. split; [clear - Hnr HEVv; lia|].
split; [exact MLE2|]. split; [exact MOK2|]. split; [exact HC2|]. split; [exact HCG2|]. split; [exact HBL2|].
split; [exact Hres|]. split; [exact Ha0|].
rewrite (g_pres_reg (ms_regs ms) regs2 19%bv HPres ltac:(vm_compute; reflexivity)). exact Rs3.
Qed.

(* ---- piece 6a: id's three version fields and reac_identity_reac_ver_str at +0x119c ------------------ *)
Lemma g_vm2j : forall (W : world SEGS) m a l j,
  garr8 SEGS (rd W m) a l -> (S j < length l)%nat ->
  val_mem SEGS (rd W m) (a + Z.of_nat j) 2 (nth j l 0 + 256 * nth (S j) l 0).
Proof.
intros W m a l j HG Hlen.
destruct (HG j ltac:(lia)) as (V0 & R0). destruct (HG (S j) ltac:(lia)) as (V1 & R1).
intros k Hk. assert (k = 0 \/ k = 1)%nat as [-> | ->] by lia.
- specialize (V0 0%nat ltac:(lia)). rewrite (g_le20 _ _ R0 R1). rewrite (g_le1 _ R0) in V0.
  replace (a + Z.of_nat j + Z.of_nat 0) with (a + Z.of_nat j + Z.of_nat 0) by reflexivity. exact V0.
- specialize (V1 0%nat ltac:(lia)). rewrite (g_le21 _ _ R0 R1). rewrite (g_le1 _ R1) in V1.
  replace (a + Z.of_nat j + Z.of_nat 1) with (a + Z.of_nat (S j) + Z.of_nat 0) by lia. exact V1.
Qed.
(* The 16-bit field at id + j. *)
Definition g_v16 (g : ectx) (j : nat) : Z :=
  nth j (map (fun b : byte => bv_unsigned b) (m_id g (m_nrec g))) 0 +
  256 * nth (S j) (map (fun b : byte => bv_unsigned b) (m_id g (m_nrec g))) 0.
Lemma g_v16_range : forall g j, 0 <= g_v16 g j < 65536.
Proof.
intros g j. unfold g_v16.
assert (R : forall j, 0 <= nth j (map (fun b : byte => bv_unsigned b) (m_id g (m_nrec g))) 0 < 256).
{ intros j'. destruct (Nat.lt_ge_cases j' (length (m_id g (m_nrec g)))) as [Hj | Hj].
  - rewrite (nth_indep _ _ (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
    rewrite (map_nth (fun b : byte => bv_unsigned b)).
    pose proof (bv_unsigned_in_range 8 (nth j' (m_id g (m_nrec g)) (Z_to_bv 8 0))) as Q.
    change (bv_modulus 8) with 256 in Q. exact Q.
  - rewrite nth_overflow by (rewrite length_map; exact Hj). lia. }
pose proof (R j). pose proof (R (S j)). lia.
Qed.
Definition g_rid6 : YP09.region :=
  YP09.mkRegion (Some 19%nat) 22 28 0 0
    [YP09.mkChunk 22 (CVal 2 (SOff 32 0)); YP09.mkChunk 24 (CVal 2 (SOff 33 0)); YP09.mkChunk 26 (CVal 2 (SOff 34 0))].
Definition g_ss6a : sstate :=
  mkSS 0x1180 sr_atoms [g_rid6] None
    (mkFacts [(32%nat, mkAF 0 65535 0); (33%nat, mkAF 0 65535 0); (34%nat, mkAF 0 65535 0)] [] []).
Definition g_x6 (g : ectx) : list word := map (Z_to_bv 64) [g_v16 g 22; g_v16 g 24; g_v16 g 26].
Lemma g_st6a : forall g pos (W : world SEGS) regs mem,
  getr regs 19 = w64 (SFa g pos + V_id) -> 4096 <= SFa g pos -> SFa g pos + 1024 <= alloc_ceiling ->
  alloc_ceiling <= 2 ^ 47 -> id_at g pos (m_nrec g) W mem ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (g_x6 g))) g_ss6a
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x1180)) mem (seg_rom SEGS))).
Proof.
intros g pos W regs mem R19 HF0 HFc Hc47 HI.
set (E := Eimg (Ereg regs (g_x6 g))).
assert (E19 : ew E 19 = getr regs 19) by (unfold E; apply ew_Eimg_Ereg_nat; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 (g_v16 g 22))
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (g_v16 g 24))
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (g_v16 g 26))
  by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
pose proof (g_v16_range g 22) as R22. pose proof (g_v16_range g 24) as R24. pose proof (g_v16_range g 26) as R26.
assert (B19 : base_val E (Some 19%nat) = SFa g pos + V_id)
  by (cbn [base_val]; rewrite E19, R19; unfold w64; apply unsigned_lit_small; unfold V_id; lia).
destruct HI as (Hb & _). unfold bytes_at8 in Hb.
assert (Hl : length (map (fun b : byte => bv_unsigned b) (m_id g (m_nrec g))) = 38%nat)
  by (rewrite length_map; apply g_mid_len).
rewrite restrict_mkst_fx. unfold g_ss6a. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
  unfold region_ok, g_rid6. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite B19. split; [unfold V_id; lia|]. split; [unfold V_id; lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor; [|constructor; [|constructor]]].
  + apply (chunk_ok_val SEGS E _ (SFa g pos + V_id) 22 2 (SOff 32 0) (g_v16 g 22)).
    * cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * lia.
    * lia.
    * exact (g_vm2j W mem _ _ 22 Hb ltac:(lia)).
  + apply (chunk_ok_val SEGS E _ (SFa g pos + V_id) 24 2 (SOff 33 0) (g_v16 g 24)).
    * cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * lia.
    * lia.
    * exact (g_vm2j W mem _ _ 24 Hb ltac:(lia)).
  + apply (chunk_ok_val SEGS E _ (SFa g pos + V_id) 26 2 (SOff 34 0) (g_v16 g 26)).
    * cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * lia.
    * lia.
    * exact (g_vm2j W mem _ _ 26 Hb ltac:(lia)).
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split; exact I]. cbn [atoms_ok f_atoms]. split; [|split; [|split; [|exact I]]].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E32, unsigned_lit_small by lia. change (2 ^ 0) with 1.
    split; [lia|]. split; [apply Z.mod_1_r | lia].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E33, unsigned_lit_small by lia. change (2 ^ 0) with 1.
    split; [lia|]. split; [apply Z.mod_1_r | lia].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E34, unsigned_lit_small by lia. change (2 ^ 0) with 1.
    split; [lia|]. split; [apply Z.mod_1_r | lia].
Qed.

Lemma g_LV_le : forall ma mi pa, 0 <= reac_identity_reac_ver_str.rvs_LV ma mi pa <= 16.
Proof.
intros ma mi pa. rewrite reac_identity_reac_ver_str.rvs_LV_split.
pose proof (reac_identity_reac_ver_str.rvs_n_range ma). pose proof (reac_identity_reac_ver_str.rvs_n_range mi).
pose proof (reac_identity_reac_ver_str.rvs_n_range pa). destruct (pa <? 10); lia.
Qed.
Lemma g_p6a : forall g pos mf res W c,
  ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 3) (BASE + 0x1180)
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       g_CG g pos mf W2 regs2 mem2 /\
       hblocks B g ly2 S2 [(res, Z.max (SlotModel.t_cap_ver (e_pl g)) 1)] /\
       4096 <= res /\ getr regs2 10 = w64 res /\ getr regs2 19 = w64 (SFa g pos + V_id)) W c ->
  SRr SEGS W c (ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 3) (BASE + 0x11a0)
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       g_CG g pos mf W2 regs2 mem2 /\
       hblocks B g ly2 S2 [(res, Z.max (SlotModel.t_cap_ver (e_pl g)) 1)] /\ 4096 <= res /\
       getr regs2 18 = w64 res /\
       (if reac_identity_reac_ver_str.rvs_fails res (SlotModel.t_cap_ver (e_pl g)) then
          getr regs2 10 = w64 (-1)
        else getr regs2 10 = w64 (reac_identity_reac_ver_str.rvs_LV (g_v16 g 22) (g_v16 g 24) (g_v16 g 26)) /\
          garr8 SEGS (rd W2 mem2) res (reac_identity_reac_ver_str.rvs_bytes (g_v16 g 22) (g_v16 g 24) (g_v16 g 26))))).
Proof.
intros g pos mf res W c (ly & S & regs & mem & md & -> & HJ & Hfr & Hk & MLE & MOK & HC & HP).
destruct HP as (HCG0 & HBL & Hres & R10 & R19).
pose proof HCG0 as (HIa & HD3 & HDid & HR23 & R22 & R26 & R21 & R27 & R24 & R25 & V176 & V160 & V120 & V112).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (pa_base_lo (PL := PL_identb)) as HBLO. pose proof asan_consts as (C1 & _).
pose proof HC as HC0. pose proof (proj1 HJ) as HAR.
destruct (g_facts g pos mf _ ly S W regs mem md HJ Hfr HC) as
  (Hsp & Hceil & Hsp47 & Hsp16 & Hmf & Hmf32 & HF4096 & HFceil & HF32 & EF).
assert (HSTKv : STK_LLVMF = 16736) by reflexivity.
assert (HVSv : reac_identity_reac_ver_str.REAC_VER_STR_STK = 4224) by reflexivity.
assert (Hmf0 : 0 <= mf) by (clear - Hmf Hceil C1 HSTK HSTKv; lia).
assert (Hmf64 : mf + 256 <= 2 ^ 64) by (clear - Hmf Hsp47; lia).
assert (Hmc : alloc_ceiling <= mf) by (clear - Hmf Hceil C1 HSTK HSTKv; lia).
assert (Hc47 : alloc_ceiling <= 2 ^ 47) by (clear - C1; lia).
assert (Hcap : 0 <= SlotModel.t_cap_ver (e_pl g) < 32)
  by (unfold SlotModel.t_cap_ver; apply Z.mod_pos_bound; lia).
destruct HC as (_ & _ & _ & _ & _ & Rgp & Rtp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & HPRE & _).
pose proof (g_v16_range g 22) as Rma. pose proof (g_v16_range g 24) as Rmi. pose proof (g_v16_range g 26) as Rpa.
pose proof (g_LV_le (g_v16 g 22) (g_v16 g 24) (g_v16 g 26)) as HLV.
pose proof (g_blk_in g ly S _ _ HBL) as Hbin.
destruct (al_blocks _ _ LAWS ly S W mem md _ _ HAR Hbin) as (Hr16 & Hr4096 & Hrceil & _).
pose proof (req_size_pos (Z.max (SlotModel.t_cap_ver (e_pl g)) 1) ltac:(lia)) as [Hreq1 Hreqge].
assert (Hnent : ~ In (res, Z.max (SlotModel.t_cap_ver (e_pl g)) 1) (ablocks B (e_ly g) (e_S g)))
  by exact (g_new_not_entry g ly S W mem md res _ HAR HBL ltac:(lia)).
(* the run: lhu a3,22(s3); lhu a1,24(s3); lhu a2,26(s3); mv s2,a0; mv a0,a3; mv a3,s2; mv a4,s6; jal *)
pose proof (g_st6a g pos W regs mem R19 HF4096 HFceil Hc47 HIa) as HS.
remember (Eimg (Ereg regs (g_x6 g))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (g_x6 g)) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (g_v16 g 22))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (g_v16 g 24))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (g_v16 g 26))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (SHOK : sh_ok SEGS buf_of.Bx_BO [] E (mrestrict (w_H W) mem)) by constructor.
clear HE.
unfold cfg_at. change (w64 (BASE + 0x1180)) with (Z_to_bv 64 (BASE + 0x1180)).
paj_run_tok RUN HS HJ SHOK buf_of.Bspan_BO; [awr_ok_tac |].
assert (Emem : forall x : word, ms_mem ms x = mem x).
{ intros x. apply HF. intros (r & Hin & Ha). cbn in Hin.
  destruct Hin as [<- | []]; cbn [YP09.r_wlo YP09.r_whi g_rid6] in Ha; lia. }
assert (Hview : forall a, aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
  by (intros a; apply aview_eq_of; unfold mrestrict; rewrite Emem; reflexivity).
assert (HK : g_kept g pos mf W mem W (ms_mem ms)) by (intros a _; exact (Hview a)).
assert (HRE : g_regs_eq regs (ms_regs ms))
  by (exact (g_regs_eq_of_st_ok E _ ms (w_H W) regs _ HS HAE ltac:(vm_compute; reflexivity))).
assert (HC' : ECOMMON g pos mf ly S W (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md))
  by (exact (g_ec_kept g pos mf ly S W regs mem md ly S W (ms_regs ms) (ms_mem ms) _ _ HC0 HJ HRE HK)).
assert (HCG : g_CG g pos mf W (ms_regs ms) (ms_mem ms)).
{ eapply (g_cg_kept g pos mf W W regs (ms_regs ms) mem (ms_mem ms)).
  - exact HCG0.
  - exact HRE.
  - exact HK.
  - apply mod32_mod8; exact HF32.
  - exact Hmf0.
  - exact Hmf64. }
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (13%bv : bv 5) Ra3. prreg HS (14%bv : bv 5) Ra4. prreg HS (18%bv : bv 5) Rs2.
rewrite (EE 2%nat 2%bv eq_refl) in Rsp. rewrite (EE 10%nat 10%bv eq_refl), R10 in Ra3, Rs2.
rewrite (EE 22%nat 22%bv eq_refl), R22 in Ra4.
rewrite E32 in Ra0. rewrite E33 in Ra1. rewrite E34 in Ra2.
assert (Qsp : spZ (ms_regs ms) = mf) by (unfold spZ; rewrite Rsp; exact Hsp).
assert (Qra : raZ (ms_regs ms) = BASE + 0x11a0)
  by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear - HBASE; lia).
destruct (al_blocks _ _ LAWS ly S W (ms_mem ms) _ _ _ (proj1 HJ) Hbin) as (_ & _ & _ & _ & HrPresM & _).
pmkst HS. rewrite (PSIG IB_reac_identity_reac_ver_str AF_reac_identity_reac_ver_str eq_refl).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) ?Q =>
  change (SRr SEGS W (cfg_at SEGS reac_identity_reac_ver_str.A_reac_identity_reac_ver_str rg mm mdx) Q) end.
eapply SRr_mono.
{ apply (HVS LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly S W (ms_mem ms) _
    (4 * Z.of_nat (m_nrec g) + 3) (ms_regs ms) (g_v16 g 22) (g_v16 g 24) (g_v16 g 26) res
    (SlotModel.t_cap_ver (e_pl g)) HJ).
  - rewrite Rra. apply ret_ok_codeptr_v; [clear - HBASE; lia | reflexivity].
  - rewrite Qra. clear - HBLO HBASE. lia.
  - rewrite (HRE 3%bv ltac:(ginr)). exact Rgp.
  - rewrite (HRE 4%bv ltac:(ginr)). exact Rtp.
  - rewrite Qsp. apply g_mod16. exact Hmf32.
  - rewrite Qsp, HVSv. clear - Hmf HSTK HSTKv. lia.
  - rewrite Qsp. clear - Hmf. lia.
  - exact Ra0.
  - exact Ra1.
  - exact Ra2.
  - exact Ra3.
  - exact Ra4.
  - exact Rma.
  - exact Rmi.
  - exact Rpa.
  - clear - Hres Hrceil Hreq1 Hc47; split; lia.
  - clear - Hcap; split; lia.
  - intros Hf. unfold reac_identity_reac_ver_str.rvs_fails in Hf. apply orb_false_elim in Hf as [_ Hc20].
    apply Z.ltb_ge in Hc20.
    assert (Hfit : res + 20 <= res + req_size (Z.max (SlotModel.t_cap_ver (e_pl g)) 1)) by lia.
    split; [|split].
    + intros a Ha. rewrite Qsp.
      destruct (HrPresM a ltac:(lia)) as (Hap & Hno). split; [|split; [|split]].
      * right; right; left. exists res, (Z.max (SlotModel.t_cap_ver (e_pl g)) 1).
        split; [exact Hbin|]. split; [exact Hnent | lia].
      * exact Hap.
      * exact Hno.
      * unfold ESTACK. clear - Ha Hfit Hrceil Hmc Hmf Hceil HSTK HSTKv. lia.
    + left. exists res, (Z.max (SlotModel.t_cap_ver (e_pl g)) 1). split; [exact Hbin | lia].
    + eapply (range_addressable_of_block SEGS B LAWS ly S W (ms_mem ms) _ res); [exact (proj1 HJ) | exact Hbin | lia | lia].
  - rewrite Hfr. cbn. lia. }
cbv beta. intros W2 c2 _ (-> & ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HPres & Hperm & Hfrs & Hif).
unfold reac_identity_reac_ver_str.EV_REAC_VER_STR in HJ2. rewrite Z.add_0_r in HJ2.
assert (HKc : g_kept g pos mf W (ms_mem ms) W mem2).
{ destruct (reac_identity_reac_ver_str.rvs_fails res (SlotModel.t_cap_ver (e_pl g))) eqn:Hf.
  - destruct Hif as (_ & Htcj). rewrite Qsp in Htcj.
    apply (g_kept_tcj g pos mf _ ly S W (ms_mem ms) _ W mem2 _ Htcj (proj1 HJ) ltac:(rewrite Hfr; left; reflexivity) EF).
    + rewrite HVSv. clear - Hmf Hceil HSTK HSTKv. lia.
    + intros a [].
    + intros Hn. exact (g_inp g ly S _ HBL HPRE Hn).
  - destruct Hif as (_ & _ & Htcj). rewrite Qsp in Htcj.
    unfold reac_identity_reac_ver_str.rvs_fails in Hf. apply orb_false_elim in Hf as [_ Hc20].
    apply Z.ltb_ge in Hc20.
    apply (g_kept_tcj g pos mf _ ly S W (ms_mem ms) _ W mem2 _ Htcj (proj1 HJ) ltac:(rewrite Hfr; left; reflexivity) EF).
    + rewrite HVSv. clear - Hmf Hceil HSTK HSTKv. lia.
    + intros a Ha. exists res, (Z.max (SlotModel.t_cap_ver (e_pl g)) 1). split; [exact Hbin|].
      split; [lia|]. intros Hn. exact (g_res_ne_inp g ly S W mem md res _ HAR HBL HPRE ltac:(lia) Hn).
    + intros Hn. exact (g_inp g ly S _ HBL HPRE Hn). }
assert (HREc : g_regs_eq (ms_regs ms) regs2) by (apply g_regs_eq_pres; exact HPres).
exists ly2, S2, regs2, mem2, md2.
split; [rewrite Rra; reflexivity|].
split; [exact HJ2|].
split; [rewrite Hfrs; exact Hfr|].
split; [exact Hk|].
split.
{ pose proof (mle_station MT _ _ _ _ _ MTL MLE (HMT0 S S2)) as X. rewrite Z.add_0_r in X. exact X. }
split.
{ apply (mok_station MT S S2 ((EV_LLVMF - (4 * Z.of_nat (m_nrec g) + 3)) * MEV MT) 0); [exact MTL | exact MOK | exact (HMT0 S S2) | | lia].
  pose proof g_mev_pos. clear - H Hk. nia. }
split.
{ exact (g_ec_kept g pos mf ly S W (ms_regs ms) (ms_mem ms) _ ly2 S2 W regs2 mem2 md2 _ HC' HJ2 HREc HKc). }
split.
{ eapply (g_cg_kept g pos mf W W (ms_regs ms) regs2 (ms_mem ms) mem2);
  [exact HCG | exact HREc | exact HKc | apply mod32_mod8; exact HF32 | exact Hmf0 | exact Hmf64]. }
split.
{ destruct HBL as (HPm & HFa). split; [eapply Permutation_trans; [exact Hperm | exact HPm] | exact HFa]. }
split; [exact Hres|].
split; [rewrite (g_pres_reg (ms_regs ms) regs2 18%bv HPres ltac:(vm_compute; reflexivity)); exact Rs2|].
destruct (reac_identity_reac_ver_str.rvs_fails res (SlotModel.t_cap_ver (e_pl g))).
- destruct Hif as (Ha0' & _). exact Ha0'.
- destruct Hif as (Ha0' & Hgar & _). split; [exact Ha0' | exact Hgar].
Qed.

(* ---- piece 6b: check_str at +0x11a8 on the version string ------------------------------------------ *)
Lemma g_dg_nz : forall x, 0 <= x < 10 -> bv_unsigned (write_uint_c.write_uint_dg x) <> 0.
Proof.
intros x Hx. unfold write_uint_c.write_uint_dg. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. lia.
Qed.
Lemma g_lsd_nz : forall k v b, In b (write_uint_c.write_uint_lsd k v) -> bv_unsigned b <> 0.
Proof.
induction k as [|k IH]; intros v b H; cbn [write_uint_c.write_uint_lsd] in H; [destruct H|].
destruct H as [<- | H]; [apply g_dg_nz; apply Z.mod_pos_bound; lia|].
destruct (v <? 10); [destruct H | exact (IH _ _ H)].
Qed.
Lemma g_VER_nz : forall ma mi pa, 0 <= pa ->
  forall b, In b (reac_identity_reac_ver_str_c.reac_ver_str_VER ma mi pa) -> bv_unsigned b <> 0.
Proof.
intros ma mi pa Hpa b H.
unfold reac_identity_reac_ver_str_c.reac_ver_str_VER, reac_identity_reac_ver_str_c.reac_ver_str_DEC2,
  write_uint_c.write_uint_D in H.
rewrite !in_app_iff in H. destruct H as [H | [H | [H | H]]].
- rewrite <- in_rev in H. exact (g_lsd_nz _ _ _ H).
- destruct H as [<- | []]. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  rewrite Z.mod_small by lia. lia.
- rewrite <- in_rev in H. exact (g_lsd_nz _ _ _ H).
- destruct (pa <? 10) eqn:Hp.
  + apply Z.ltb_lt in Hp. destruct H as [<- | [<- | []]]; apply g_dg_nz; lia.
  + rewrite <- in_rev in H. exact (g_lsd_nz _ _ _ H).
Qed.
Lemma g_rvs_str_ok : forall ma mi pa, 0 <= pa ->
  Z.of_nat (length (reac_identity_reac_ver_str.rvs_bytes ma mi pa)) = reac_identity_reac_ver_str.rvs_LV ma mi pa + 1 /\
  nth (Z.to_nat (reac_identity_reac_ver_str.rvs_LV ma mi pa)) (reac_identity_reac_ver_str.rvs_bytes ma mi pa) 0 = 0 /\
  (forall i, (i < Z.to_nat (reac_identity_reac_ver_str.rvs_LV ma mi pa))%nat ->
     nth i (reac_identity_reac_ver_str.rvs_bytes ma mi pa) 0 <> 0).
Proof.
intros ma mi pa Hpa. unfold reac_identity_reac_ver_str.rvs_bytes.
assert (EL : reac_identity_reac_ver_str.rvs_LV ma mi pa =
  Z.of_nat (length (reac_identity_reac_ver_str_c.reac_ver_str_VER ma mi pa))) by reflexivity.
split; [rewrite length_app, length_map; cbn [length]; lia|].
split.
{ rewrite EL, Nat2Z.id, app_nth2 by (rewrite length_map; lia).
  rewrite length_map, Nat.sub_diag. reflexivity. }
intros i Hi. rewrite EL, Nat2Z.id in Hi.
rewrite app_nth1 by (rewrite length_map; exact Hi).
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0 : byte))) by (rewrite length_map; exact Hi).
rewrite map_nth. apply (g_VER_nz ma mi pa Hpa). apply nth_In. exact Hi.
Qed.
Lemma g_p6b : forall g pos mf res W c,
  ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 3) (BASE + 0x11a0)
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       g_CG g pos mf W2 regs2 mem2 /\
       hblocks B g ly2 S2 [(res, Z.max (SlotModel.t_cap_ver (e_pl g)) 1)] /\ 4096 <= res /\
       getr regs2 18 = w64 res /\
       (if reac_identity_reac_ver_str.rvs_fails res (SlotModel.t_cap_ver (e_pl g)) then
          getr regs2 10 = w64 (-1)
        else getr regs2 10 = w64 (reac_identity_reac_ver_str.rvs_LV (g_v16 g 22) (g_v16 g 24) (g_v16 g 26)) /\
          garr8 SEGS (rd W2 mem2) res (reac_identity_reac_ver_str.rvs_bytes (g_v16 g 22) (g_v16 g 24) (g_v16 g 26)))) W c ->
  SRr SEGS W c (ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 3) (BASE + 0x11ac)
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       g_CG g pos mf W2 regs2 mem2 /\
       hblocks B g ly2 S2 [(res, Z.max (SlotModel.t_cap_ver (e_pl g)) 1)] /\ 4096 <= res /\
       getr regs2 18 = w64 res)).
Proof.
intros g pos mf res W c (ly & S & regs & mem & md & -> & HJ & Hfr & Hk & MLE & MOK & HC & HP).
destruct HP as (HCG0 & HBL & Hres & R18 & Hif).
pose proof HCG0 as (_ & _ & _ & _ & R22 & _).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & _). pose proof HC as HC0. pose proof (proj1 HJ) as HAR.
destruct (g_facts g pos mf _ ly S W regs mem md HJ Hfr HC) as
  (Hsp & Hceil & Hsp47 & Hsp16 & Hmf & Hmf32 & HF4096 & HFceil & HF32 & EF).
assert (HSTKv : STK_LLVMF = 16736) by reflexivity.
assert (Hmf0 : 0 <= mf) by (clear - Hmf Hceil C1 HSTK HSTKv; lia).
assert (Hmf64 : mf + 256 <= 2 ^ 64) by (clear - Hmf Hsp47; lia).
assert (Hcap : 0 <= SlotModel.t_cap_ver (e_pl g) < 32)
  by (unfold SlotModel.t_cap_ver; apply Z.mod_pos_bound; lia).
destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & HPRE & _).
pose proof (g_blk_in g ly S _ _ HBL) as Hbin.
(* the run: mv a1,s2; mv a2,s6; jal *)
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HS : st_ok_pi SEGS VAL E (mkSS 0x11a0 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x11a0)) mem (seg_rom SEGS)))).
{ subst E. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full;
  [apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | exact I
  | split; [cbn [atoms_ok f_atoms]; exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS buf_of.Bx_BO [] E (mrestrict (w_H W) mem)) by constructor.
clear HE.
unfold cfg_at. change (w64 (BASE + 0x11a0)) with (Z_to_bv 64 (BASE + 0x11a0)).
paj_run_tok RUN HS HJ SHOK buf_of.Bspan_BO; [awr_ok_tac |].
assert (Emem : forall x : word, ms_mem ms x = mem x) by (intros x; apply HF; intros (r & [] & _)).
assert (Hview : forall a, aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
  by (intros a; apply aview_eq_of; unfold mrestrict; rewrite Emem; reflexivity).
assert (HK : g_kept g pos mf W mem W (ms_mem ms)) by (intros a _; exact (Hview a)).
assert (HRE : g_regs_eq regs (ms_regs ms))
  by (exact (g_regs_eq_of_st_ok E _ ms (w_H W) regs [] HS HAE ltac:(vm_compute; reflexivity))).
assert (HC' : ECOMMON g pos mf ly S W (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md))
  by (exact (g_ec_kept g pos mf ly S W regs mem md ly S W (ms_regs ms) (ms_mem ms) _ _ HC0 HJ HRE HK)).
assert (HCG : g_CG g pos mf W (ms_regs ms) (ms_mem ms)).
{ eapply (g_cg_kept g pos mf W W regs (ms_regs ms) mem (ms_mem ms)).
  - exact HCG0.
  - exact HRE.
  - exact HK.
  - apply mod32_mod8; exact HF32.
  - exact Hmf0.
  - exact Hmf64. }
prreg HS (1%bv : bv 5) Rra. prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (18%bv : bv 5) Rs2.
rewrite (EE 10%nat 10%bv eq_refl) in Ra0. rewrite (EE 18%nat 18%bv eq_refl), R18 in Ra1, Rs2.
rewrite (EE 22%nat 22%bv eq_refl), R22 in Ra2.
pmkst HS. rewrite (PSIG IB_check_str AF_check_str eq_refl).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) ?Q =>
  change (SRr SEGS W (cfg_at SEGS (BASE + AF_check_str) rg mm mdx) Q) end.
assert (Hgen : forall r (bs : list Z), getr regs 10 = w64 r -> - 2 ^ 31 <= r < 2 ^ 31 ->
  (0 <= r -> r < SlotModel.t_cap_ver (e_pl g) /\ r + 1 <= req_size (Z.max (SlotModel.t_cap_ver (e_pl g)) 1) /\
     garr8 SEGS (rd W (ms_mem ms)) res bs /\ Z.of_nat (length bs) = r + 1 /\
     nth (Z.to_nat r) bs 0 = 0 /\ (forall i, (i < Z.to_nat r)%nat -> nth i bs 0 <> 0)) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_check_str) (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md))
    (ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 3) (BASE + 0x11ac)
      (fun ly2 S2 W2 regs2 mem2 md2 =>
         g_CG g pos mf W2 regs2 mem2 /\
         hblocks B g ly2 S2 [(res, Z.max (SlotModel.t_cap_ver (e_pl g)) 1)] /\ 4096 <= res /\
         getr regs2 18 = w64 res))).
{ intros r bs Hr0 Hr Hstr. eapply SRr_mono.
  { apply (g_chk_call g pos mf _ ly S W (ms_regs ms) (ms_mem ms) _ res (Z.max (SlotModel.t_cap_ver (e_pl g)) 1)
      r (SlotModel.t_cap_ver (e_pl g)) bs 0x11ac HJ Hfr HC' HCG Hbin ltac:(lia)
      (fun Hn => g_inp g ly S _ HBL HPRE Hn) Rra ltac:(clear - HBASE; lia) eq_refl).
    - rewrite Ra0. exact Hr0.
    - exact Ra1.
    - exact Ra2.
    - exact Hr.
    - clear - Hcap; split; lia.
    - exact Hstr. }
  cbv beta. intros W2 c2 _ (regs2 & mem2 & md2 & -> & -> & HJ2 & HPres & HC2 & HCG2 & _).
  exists ly, S, regs2, mem2, md2.
  split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hfr|]. split; [exact Hk|].
  split; [exact MLE|]. split; [exact MOK|]. split; [exact HC2|]. split; [exact HCG2|].
  split; [exact HBL|]. split; [exact Hres|].
  rewrite (g_pres_reg (ms_regs ms) regs2 18%bv HPres ltac:(vm_compute; reflexivity)); exact Rs2. }
destruct (reac_identity_reac_ver_str.rvs_fails res (SlotModel.t_cap_ver (e_pl g))) eqn:Hf.
- apply (Hgen (-1) [] Hif ltac:(lia)). intros Hneg. lia.
- destruct Hif as (Hr10 & Hgar).
  unfold reac_identity_reac_ver_str.rvs_fails in Hf. apply orb_false_elim in Hf as [_ Hc20]. apply Z.ltb_ge in Hc20.
  pose proof (g_v16_range g 26) as Rpa.
  destruct (g_rvs_str_ok (g_v16 g 22) (g_v16 g 24) (g_v16 g 26) ltac:(lia)) as (Hlen & Hlast & Hnz).
  pose proof (g_LV_le (g_v16 g 22) (g_v16 g 24) (g_v16 g 26)) as HLV.
  apply (Hgen _ (reac_identity_reac_ver_str.rvs_bytes (g_v16 g 22) (g_v16 g 24) (g_v16 g 26)) Hr10 ltac:(lia)).
  intros _. split; [lia|]. split; [pose proof (req_size_pos (Z.max (SlotModel.t_cap_ver (e_pl g)) 1) ltac:(lia)) as [_ Q]; lia|].
  split; [eapply g_garr8_kept; [|exact Hgar]; intros j _; exact (Hview (res + j))|].
  split; [exact Hlen|]. split; [exact Hlast | exact Hnz].
Qed.

(* ---- piece 7: free of the version buffer at +0x11b0 ------------------------------------------------- *)
Lemma g_p7 : forall g pos mf res W c,
  ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 3) (BASE + 0x11ac)
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       g_CG g pos mf W2 regs2 mem2 /\
       hblocks B g ly2 S2 [(res, Z.max (SlotModel.t_cap_ver (e_pl g)) 1)] /\ 4096 <= res /\
       getr regs2 18 = w64 res) W c ->
  SRr SEGS W c (ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 4) (BASE + 0x11b4)
    (fun ly2 S2 W2 regs2 mem2 md2 => g_CG g pos mf W2 regs2 mem2 /\ hblocks B g ly2 S2 [])).
Proof.
intros g pos mf res W c (ly & S & regs & mem & md & -> & HJ & Hfr & Hk & MLE & MOK & HC & HP).
destruct HP as (HCG0 & HBL & Hres & R18).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & _). pose proof HC as HC0.
destruct (g_facts g pos mf _ ly S W regs mem md HJ Hfr HC) as
  (Hsp & Hceil & Hsp47 & Hsp16 & Hmf & Hmf32 & HF4096 & HFceil & HF32 & EF).
assert (HSTKv : STK_LLVMF = 16736) by reflexivity.
assert (HEVv : EV_LLVMF = 266) by reflexivity.
assert (Hmf0 : 0 <= mf) by (clear - Hmf Hceil C1 HSTK HSTKv; lia).
assert (Hmf64 : mf + 256 <= 2 ^ 64) by (clear - Hmf Hsp47; lia).
assert (Hcap : 0 <= SlotModel.t_cap_ver (e_pl g) < 32)
  by (unfold SlotModel.t_cap_ver; apply Z.mod_pos_bound; lia).
pose proof (g_nrec_le g) as Hnr.
(* the run: mv a0,s2; jal *)
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HS : st_ok_pi SEGS VAL E (mkSS 0x11ac sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x11ac)) mem (seg_rom SEGS)))).
{ subst E. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full;
  [apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | exact I
  | split; [cbn [atoms_ok f_atoms]; exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS buf_of.Bx_BO [] E (mrestrict (w_H W) mem)) by constructor.
clear HE.
unfold cfg_at. change (w64 (BASE + 0x11ac)) with (Z_to_bv 64 (BASE + 0x11ac)).
paj_run_tok RUN HS HJ SHOK buf_of.Bspan_BO; [awr_ok_tac |].
assert (Emem : forall x : word, ms_mem ms x = mem x) by (intros x; apply HF; intros (r & [] & _)).
assert (Hview : forall a, aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a)
  by (intros a; apply aview_eq_of; unfold mrestrict; rewrite Emem; reflexivity).
assert (HK : g_kept g pos mf W mem W (ms_mem ms)) by (intros a _; exact (Hview a)).
assert (HRE : g_regs_eq regs (ms_regs ms))
  by (exact (g_regs_eq_of_st_ok E _ ms (w_H W) regs [] HS HAE ltac:(vm_compute; reflexivity))).
assert (HC' : ECOMMON g pos mf ly S W (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md))
  by (exact (g_ec_kept g pos mf ly S W regs mem md ly S W (ms_regs ms) (ms_mem ms) _ _ HC0 HJ HRE HK)).
assert (HCG : g_CG g pos mf W (ms_regs ms) (ms_mem ms)).
{ eapply (g_cg_kept g pos mf W W regs (ms_regs ms) mem (ms_mem ms)).
  - exact HCG0.
  - exact HRE.
  - exact HK.
  - apply mod32_mod8; exact HF32.
  - exact Hmf0.
  - exact Hmf64. }
prreg HS (1%bv : bv 5) Rra. prreg HS (10%bv : bv 5) Ra0.
rewrite (EE 18%nat 18%bv eq_refl), R18 in Ra0.
pmkst HS. ppcs.
eapply SRr_mono.
{ apply (g_free_call g pos mf _ ly S W (ms_regs ms) (ms_mem ms) _ res (Z.max (SlotModel.t_cap_ver (e_pl g)) 1) 0x11b4
    HJ Hfr ltac:(clear - Hk; lia) ltac:(clear - Hnr HEVv; lia) MLE MOK HC' HCG HBL ltac:(lia) Rra
    ltac:(unfold LLVMF_FREE_RAS; cbn; tauto) ltac:(clear - HBASE; lia) eq_refl Ra0). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & Hfr2 & MLE2 & MOK2 & HC2 & HCG2 & HBL2 & HPres).
exists ly2, S2, regs2, mem2, md2.
replace (4 * Z.of_nat (m_nrec g) + 3 + 1) with (4 * Z.of_nat (m_nrec g) + 4) in HJ2, MLE2, MOK2 by (clear; lia).
split; [reflexivity|]. split; [exact HJ2|]. split; [exact Hfr2|]. split; [clear - Hnr HEVv; lia|].
split; [exact MLE2|]. split; [exact MOK2|]. split; [exact HC2|]. split; [exact HCG2 | exact HBL2].
Qed.

(* ---- seg_G: the pieces in order, then g_stores (+0x11b4 .. +0x11c4) ---------------------------------- *)
Lemma seg_G : @seg_G_stmt fx rc SK PI B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
unfold seg_G_stmt. intros g pos mf W c HF.
eapply SRr_bind; [exact (g_p1 g pos mf W c HF)|]. intros W1 c1 _ (res & H1).
eapply SRr_bind; [exact (g_p2a g pos mf res W1 c1 H1)|]. intros W2 c2 _ H2.
eapply SRr_bind; [exact (g_p2b g pos mf res W2 c2 H2)|]. intros W3 c3 _ H3.
eapply SRr_bind; [exact (g_p3a g pos mf res W3 c3 H3)|]. intros W4 c4 _ H4.
eapply SRr_bind; [exact (g_p3b g pos mf res W4 c4 H4)|]. intros W5 c5 _ H5.
eapply SRr_bind; [exact (g_p4 g pos mf res W5 c5 H5)|]. intros W6 c6 _ H6.
eapply SRr_bind; [exact (g_p5 g pos mf W6 c6 H6)|]. intros W7 c7 _ (res2 & H7).
eapply SRr_bind; [exact (g_p6a g pos mf res2 W7 c7 H7)|]. intros W8 c8 _ H8.
eapply SRr_bind; [exact (g_p6b g pos mf res2 W8 c8 H8)|]. intros W9 c9 _ H9.
eapply SRr_bind; [exact (g_p7 g pos mf res2 W9 c9 H9)|]. intros W10 c10 _ H10.
pose proof (g_stores B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
  ameta_inv arodata_okS) as GS. unfold g_stores_stmt in GS.
apply (GS LAWS TL HSTK AJ_NIL_IO g pos mf W10 c10).
destruct H10 as (ly & S & regs & mem & md & -> & HJ & Hfr & Hk & MLE & MOK & HC & HP).
destruct HP as ((HIa & HD3 & HDid & HR23 & R22 & R26 & R21 & R27 & R24 & R25 & V176 & V160 & V120 & V112) & HBL).
exists ly, S, regs, mem, md.
split; [reflexivity|]. split; [exact HJ|]. split; [exact Hfr|]. split; [exact Hk|].
split; [exact MLE|]. split; [exact MOK|]. split; [exact HC|].
exact (conj HIa (conj HBL (conj HR23 (conj HD3 (conj HDid (conj R24 (conj R25 (conj R21 (conj R26 (conj R27
  (conj V176 (conj V160 (conj V120 V112))))))))))))).
Qed.
Check (seg_G : @seg_G_stmt fx rc SK PI B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).

End c.
End b.
End a.

Print Assumptions seg_G.
