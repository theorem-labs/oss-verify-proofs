(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh9.v:106-109
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366 [Apache-2.0 OR MIT], for libreac/fuzz_identity's
   asan-ubsan build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_K_hand_def.v, with its addresses changed; 339 of its 438 lines of code are new or changed and 1064 lines of the source are left out. *)
(* The first piece of seg_K of LLVMFuzzerTestOneInput's ASan+UBSan walk (image B), +0x1988 .. +0x19a8
   (fuzz_identity.asan-ubsan 0x820fc .. 0x8211c): `k_name : k_name_stmt` of
   lib/B/Prog/LLVMFuzzerTestOneInput_seg_K_hand_stmt.v.

   The code, as offsets from the entry (the neutral listing of fuzz_identity.asan-ubsan):
     +0x1988  bnez s8,+0x1bec     not taken: s8 = n_r = 0 (the statement's getr regs 24 = w64 0)
     +0x198c  ld s2,152(s1)       nm, from the machine frame (s1 = mf)
     +0x1990  mv a0,s2
     +0x1994  jal wrapper_strlen  (k_strlen_at; answers r = n_ln, return +0x1998)
     +0x1998  sext.w a0,a0        r < 40 < 2^31, unchanged (kn_sextw)
     +0x199c  mv a1,s2
     +0x19a0  ld a2,144(s1)       cap_name, from the machine frame
     +0x19a4  jal check_str       (k_check_str_at; r < cap_name by n_fits; return +0x19a8)
   No ASan inline shadow check and no __asan_report_* call is in this stretch (the two loads read the machine
   frame at mf + 152 and mf + 144), so no report call can fall through into the next function here. The string
   facts both callees ask of nm come from ks_str (lib/B/Prog/LLVMFuzzerTestOneInput_seg_K_hand_str.v); what KC
   keeps across the two runs, the wrapper and check_str is kn_keep_all / kn_keep_cs. *)
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
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81 IdentBlkTail.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require
check_str reac_box_catalogue reac_box_catalogue_defect.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require AStrcmpDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrlenDef StrcmpDef WrapRo.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_seg_K_hand_stmt LLVMFuzzerTestOneInput_seg_K_base LLVMFuzzerTestOneInput_seg_K_hand_str.

(* +0x1988 (0x820fc): the symbolic state of the first run. Register s1 = mf; the machine frame's slot mf+152
   holds nm (atom 32), read-only. *)
Definition kn_r1 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 152 160 152 152 [YP09.mkChunk 152 (CVal 8 (SOff 32 0))].
Definition kn_ss1 : sstate := mkSS 0x1988 sr_atoms [kn_r1] None (mkFacts [] [] []).
(* +0x1998 (0x8210c): the return of the strlen wrapper; the slot mf+144 holds cap_name (atom 32), read-only. *)
Definition kn_r2 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 144 152 144 144 [YP09.mkChunk 144 (CVal 8 (SOff 32 0))].
Definition kn_ss2 : sstate := mkSS 0x1998 sr_atoms [kn_r2] None (mkFacts [] [] []).

(* The callee-saved side condition of aregs_preserved, with the register literal computed. *)
Ltac kn_cs :=
unfold acallee_saved;
match goal with
| |- context [bv_unsigned ?x] =>
  let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v
end; lia.

Lemma kn_pres : forall (r : bv 5) (regs regs' : bvmap 5 word),
  aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof.
intros r regs regs' H Hr. specialize (H (bv_unsigned r) Hr). rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.

(* `sext.w a0,a0` (addiw a0,a0,0) of a register that holds a value below 2^31: the strlen wrapper's answer at
   0x8210c. *)
Lemma kn_sextw : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 ->
  sv_denot E (SAluw ALU_ADD (SOff n 0) (SLit 0)) = Z_to_bv 64 v.
Proof.
intros E n v Hn Hv.
rewrite denot_lit_U. f_equal.
rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite U_SLit, (U_atom E n v Hn ltac:(lia)).
change (zcanon 0 mod 2 ^ 32) with 0. rewrite Z.add_0_r.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small v (2 ^ 32)) by lia.
rewrite (Z.mod_small (v + 2 ^ 31) (2 ^ 32)) by lia.
replace (v + 2 ^ 31 - 2 ^ 31) with v by lia.
apply Z.mod_small. lia.
Qed.

(* A register of a symbolic state, without prreg's normalization of the value (which unfolds sv_denot). *)
Ltac kn_reg HS r Hr :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.

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
Variable G : list (Z * Z).
#[local] Notation KPREn := (KPRE B RLO RHI LLVMF_STK arodata_okS G).
#[local] Notation KHn := (KH B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation KCn := (KC B LLVMF_STK).
Section h.
Hypothesis HPRE : KPREn.
Let LAWS : AR_laws SEGS B := k_laws B RLO RHI LLVMF_STK arodata_okS G HPRE.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (PI := PI).
Section run.
Variables (g : ectx) (pos mf nm tk dp : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
  (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model).
Hypothesis HKH : KHn g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2.

(* The string nm of the start state: a live heap block of KH's hblocks, its bytes n_EXP_NM ++ [0] (KH's n_r = 0
   conjunct), no zero byte before the end, and its length below the block's request size. *)
Lemma kn_nm :
  In (nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1) (ablocks B ly2 S2) /\
  bytes_at8 W2 mem2 nm (SlotModel.n_EXP_NM (e_pl g) ++ [RcIdentModel.zb 0]) /\
  KModel.nzb (SlotModel.n_EXP_NM (e_pl g)) = true /\
  0 <= SlotModel.n_ln (e_pl g) < SlotModel.t_cap_name (e_pl g) /\ SlotModel.t_cap_name (e_pl g) < 40 /\
  Z.of_nat (length (SlotModel.n_EXP_NM (e_pl g))) + 1 <= req_size (Z.max (SlotModel.t_cap_name (e_pl g)) 1).
Proof.
pose proof HKH as (_ & _ & _ & _ & _ & _ & HHB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  HBY & HNR).
destruct (KModel.n_r0 _ HNR) as [Hwok Hfits].
destruct (KModel.fits_unfold _ Hfits) as (Hln & _ & _).
destruct (HBY HNR) as (Hbnm & _ & _).
assert (Hc40 : 0 <= SlotModel.t_cap_name (e_pl g) < 40)
  by (unfold SlotModel.t_cap_name; apply Z.mod_pos_bound; lia).
assert (Hl0 : 0 <= SlotModel.n_ln (e_pl g)) by (unfold SlotModel.n_ln; lia).
split.
{ destruct HHB as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)).
  apply in_or_app. left. left. reflexivity. }
split; [exact Hbnm|].
split; [exact (KModel.nzb_EXP_NM _ Hwok)|].
split; [lia|]. split; [lia|].
unfold req_size. destruct (Z.eqb_spec (Z.max (SlotModel.t_cap_name (e_pl g)) 1) 0) as [E|E]; [lia|].
change (Z.of_nat (length (SlotModel.n_EXP_NM (e_pl g)))) with (SlotModel.n_ln (e_pl g)). lia.
Qed.

(* The facts the strlen wrapper and check_str ask of nm, at any state that keeps what KC keeps (ks_str). *)
Lemma kn_str : forall memX mdX, AR SEGS B ly2 S2 W2 memX mdX -> kkeep B g pos mf ly2 S2 W2 mem2 memX ->
  let r := SlotModel.n_ln (e_pl g) in
  0 < nm /\ nm + r + 1 <= alloc_ceiling /\
  first_byte SEGS W2 memX nm (r + 1) 0 r /\
  (forall a, nm <= a < nm + (r + 1) -> aview SEGS (w_H W2) memX a <> None) /\
  amem_range nm (r + 1) /\
  range_addressable (aview SEGS (w_H W2) memX) SHADOW_OFF nm (r + 1) /\
  shadow_hull_vis (aview SEGS (w_H W2) memX) nm (r + 1) /\
  (forall a, nm + r < a < nm + r - (nm + r) mod 8 + 8 -> aview SEGS (w_H W2) memX a <> None) /\
  (nm + r + 1 <= IMG_LO \/ IMG_TOP <= nm).
Proof.
intros memX mdX HAR HKPX. destruct kn_nm as (Hin & Hby & Hnz & _ & _ & Hlen).
exact (ks_str B RLO RHI LLVMF_STK arodata_okS G HPRE g pos mf ly2 S2 W2 mem2 memX mdX nm _ _ HAR HKPX Hin Hby Hnz
  Hlen).
Qed.

(* A step that changes nothing outside the callees' window [mf - (16 + 2 * ESTACK), mf) keeps what KC keeps:
   the live blocks, the entry frame and its shadow are all below alloc_ceiling, under the window. *)
Lemma kn_keep_all : forall mem mem', kkeep B g pos mf ly2 S2 W2 mem2 mem ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (mf - (16 + 2 * ESTACK) <= a < mf) ->
     aview SEGS (w_H W2) mem' a = aview SEGS (w_H W2) mem a) ->
  kkeep B g pos mf ly2 S2 W2 mem2 mem'.
Proof.
intros mem mem' (K1 & K2 & K3) HK.
pose proof (k_geom B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
  ameta_inv arodata_okS G HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH)
  as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
pose proof HKH as (HJ2 & _).
pose proof asan_consts as (C1 & _).
assert (Hes : ESTACK = 4096) by reflexivity.
split; [|split].
- intros a Ha Hw. rewrite (HK a ltac:(clear - Ha C1; lia) Hw). exact (K1 a Ha Hw).
- intros b n i Hb Hi.
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 b n (proj1 HJ2) Hb) as (_ & Hb0 & Hbc & _).
  rewrite (HK (b + i)); [exact (K2 b n i Hb Hi) | clear - Hb0 Hbc Hi C1; lia | clear - Hb0 Hbc Hi G1 Hes; lia].
- intros a Hfr Hc Hs.
  assert (Ha : 0 <= a < alloc_ceiling).
  { unfold in_zr, frame_rng in Hfr. cbn [fst snd] in Hfr. rewrite G12 in Hfr.
    change (fs_frame_bytes 4) with 1024 in Hfr. change (1024 / 8) with 128 in Hfr.
    clear - Hfr G8 G9 G14 G15. lia. }
  rewrite (HK a); [exact (K3 a Hfr Hc Hs) | clear - Ha C1; lia | clear - Ha G1 Hes; lia].
Qed.

(* check_str called at sp = mf keeps what KC keeps: its journal (window [mf - CHECK_STR_STK, mf), no block
   freed, the frames of S2 kept). *)
Lemma kn_keep_cs : forall mem mem' md md', kkeep B g pos mf ly2 S2 W2 mem2 mem ->
  ajournal SEGS B check_str.CHECK_STR_STK mf [] ly2 S2 W2 mem md [] ly2 S2 W2 mem' md' 0 ->
  kkeep B g pos mf ly2 S2 W2 mem2 mem'.
Proof.
intros mem mem' md md' (K1 & K2 & K3) HJc.
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & J9 & J10 & _ & J12 & _).
pose proof (k_geom B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
  ameta_inv arodata_okS G HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH)
  as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G16).
split; [|split].
- intros a Ha Hw. rewrite (J9 a Ha Hw). exact (K1 a Ha Hw).
- intros b n i Hb Hi. rewrite (J10 b n i Hb Hb Hi (inFP_nil _)). exact (K2 b n i Hb Hi).
- intros a Hfr Hc Hs. rewrite (J12 4 pos a G16 Hfr (inFP_nil _)). exact (K3 a Hfr Hc Hs).
Qed.

(* The engine stops at check_str's call slot at pa_sigma IB_check_str, its contract is at BASE + AF_check_str. *)
Lemma kn_psig : SIGMA IB_check_str = BASE + AF_check_str.
Proof.
pose proof (k_psig B RLO RHI LLVMF_STK arodata_okS G HPRE) as P. unfold identb_prog_sig_ok in P.
exact (P IB_check_str AF_check_str eq_refl).
Qed.

Lemma kn_run : forall regs mem md (Q : world SEGS -> config -> Prop),
  KCn g pos mf tk ly2 S2 W2 mem2 regs mem md -> KR g pos regs -> getr regs 24 = w64 0 ->
  (forall regs' mem' md', KCn g pos mf tk ly2 S2 W2 mem2 regs' mem' md' -> KR g pos regs' -> getr regs' 18 = w64 nm ->
    SRr SEGS W2 (cfg_at SEGS (BASE + 0x19a8) regs' mem' md') Q) ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x1988) regs mem md) Q.
Proof.
intros regs mem md Q (HJ & HKP & Rsp & Rs1 & Rs0 & Rgp & Rtp & Rtk & Rsh) (R22 & R25 & R26) R24 Hk.
pose proof (k_geom B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
  ameta_inv arodata_okS G HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH)
  as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HKH as (HJ2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V152 & _ & V144 & _).
destruct kn_nm as (Hinn & _ & _ & Hln & Hc40 & Hlen).
change (Z.of_nat (length (SlotModel.n_EXP_NM (e_pl g)))) with (SlotModel.n_ln (e_pl g)) in Hlen.
set (r := SlotModel.n_ln (e_pl g)) in *.
set (cap := SlotModel.t_cap_name (e_pl g)) in *.
assert (Hmf64 : 0 <= mf < 2 ^ 64) by (clear - G1 G2 G3 C1; lia).
assert (Hom : (mf - e_sp0 g) mod 16 = 0).
{ pose proof (Z.div_mod (e_sp0 g) 16 ltac:(lia)) as D1. rewrite G4, Z.add_0_r in D1.
  pose proof (Z.div_mod mf 32 ltac:(lia)) as D2. rewrite G6, Z.add_0_r in D2.
  replace (mf - e_sp0 g) with ((2 * (mf / 32) - e_sp0 g / 16) * 16) by (clear - D1 D2; lia). apply Z_mod_mult. }
unfold cfg_at. change (w64 (BASE + 0x1988)) with (Z_to_bv 64 (BASE + 0x1988)).
(* ================ run 1: +0x1988, bnez s8 (not taken), ld s2,152(s1), mv a0,s2, the strlen wrapper ========== *)
remember (Eimg (Ereg regs [Z_to_bv 64 nm])) as E1 eqn:HE1.
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply Eimg_env).
assert (EE1 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E1 n = getr regs r)
  by (intros n r' Hn; rewrite HE1; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E1_32 : ew E1 32 = Z_to_bv 64 nm)
  by (rewrite HE1, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (U1_9 : bv_unsigned (ew E1 9) = mf).
{ rewrite (EE1 9%nat 9%bv eq_refl), Rs1. unfold w64. apply unsigned_lit_small. exact Hmf64. }
assert (Hnm64 : 4096 <= nm /\ nm + r + 1 <= alloc_ceiling).
{ destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 nm _ (proj1 HJ2) Hinn) as (_ & Hn0 & Hnc & _).
  clear - Hn0 Hnc Hlen. lia. }
assert (L152 : val_mem SEGS (rd W2 mem) (mf + 152) 8 nm).
{ apply (k_vm_hi B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
    ameta_inv arodata_okS G HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH mem (mf + 152) 8 nm HKP);
  [clear; lia | clear - G2 G3; cbn; lia | exact V152]. }
assert (HS1 : st_ok_pi SEGS VAL E1 kn_ss1
  (restrict (w_H W2) (mkst regs (Z_to_bv 64 (BASE + 0x1988)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold kn_ss1. apply pa_entry_st_ok_full.
  - rewrite HE1. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold kn_r1, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U1_9. split; [clear - G1 C1; lia|]. split; [clear - G2 G3; lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E1 _ mf 152 8 (SOff 32 0) nm);
    [ cbn [sv_denot]; rewrite E1_32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | clear - Hnm64 Hln C1; cbn; lia | cbn; lia | exact L152 ].
  - cbn [pairwise_disjoint all_disjoint].
    repeat match goal with |- _ /\ _ => split end; exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [exact I | split; exact I]. }
assert (E1_24 : ew E1 24 = Z_to_bv 64 0) by (rewrite (EE1 24%nat 24%bv eq_refl), R24; reflexivity).
(* 0x820fc bnez s8: s8 = n_r = 0 (the statement's getr regs 24 = w64 0), so the branch to +0x1bec is not taken. *)
psrr_branch_pi RUNP BR HS1.
{ exfalso. rewrite branch_ne_U, (U_atom E1 24 0 E1_24), U_SLit in Hc by lia. vm_compute in Hc. discriminate Hc. }
clear Hc.
paj_run_shc RUNP RUNC HS1 HJ.
{ intros a (rg & Hr & Ha). cbn [add_cond kn_ss1 ss_mem In] in Hr.
  destruct Hr as [<- | []]. unfold kn_r1 in Ha.
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem a).
{ intros a Ha. apply (kept_of_frame E1 _ (w_H W2) mem (ms_mem ms) (fun _ => False) HFr);
  [| exact Ha | intros []].
  intros bb wlo whi aa Hin Hr. unfold kn_ss1, windows in Hin. cbn in Hin.
  destruct Hin as [Eq | []]. injection Eq as <- <- <-. cbn [base_val] in Hr. lia. }
clear HF HFr HG.
prreg HS1 (10%bv : bv 5) R1_10. prreg HS1 (1%bv : bv 5) R1_1. prreg HS1 (2%bv : bv 5) R1_2.
prreg HS1 (3%bv : bv 5) R1_3. prreg HS1 (4%bv : bv 5) R1_4. prreg HS1 (8%bv : bv 5) R1_8.
prreg HS1 (9%bv : bv 5) R1_9. prreg HS1 (18%bv : bv 5) R1_18. prreg HS1 (21%bv : bv 5) R1_21.
prreg HS1 (22%bv : bv 5) R1_22. prreg HS1 (23%bv : bv 5) R1_23. prreg HS1 (25%bv : bv 5) R1_25.
prreg HS1 (26%bv : bv 5) R1_26.
rewrite E1_32 in R1_10, R1_18.
rewrite (EE1 2%nat 2%bv eq_refl), Rsp in R1_2. rewrite (EE1 3%nat 3%bv eq_refl), Rgp in R1_3.
rewrite (EE1 4%nat 4%bv eq_refl), Rtp in R1_4. rewrite (EE1 8%nat 8%bv eq_refl), Rs0 in R1_8.
rewrite (EE1 9%nat 9%bv eq_refl), Rs1 in R1_9. rewrite (EE1 21%nat 21%bv eq_refl), Rtk in R1_21.
rewrite (EE1 22%nat 22%bv eq_refl), R22 in R1_22. rewrite (EE1 23%nat 23%bv eq_refl), Rsh in R1_23.
rewrite (EE1 25%nat 25%bv eq_refl), R25 in R1_25. rewrite (EE1 26%nat 26%bv eq_refl), R26 in R1_26.
assert (HKP1 : kkeep B g pos mf ly2 S2 W2 mem2 (ms_mem ms))
  by (apply (kn_keep_all mem (ms_mem ms) HKP); intros a Ha _; exact (KEEP1 a Ha)).
clear KEEP1.
destruct (kn_str (ms_mem ms) _ (proj1 HJ) HKP1) as (T0 & T1 & T2 & T3 & T4 & T5 & T6 & T7 & _).
destruct (k_aro B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
  ameta_inv arodata_okS G HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH (ms_mem ms) _ HJ) as [_ Haro1].
assert (Hsp1 : spZ (ms_regs ms) = e_sp0 g + (mf - e_sp0 g)).
{ unfold spZ. rewrite R1_2. unfold w64. rewrite unsigned_lit_small by exact Hmf64. lia. }
(* 0x82108: the strlen wrapper on nm; it answers r = n_ln and writes only [mf - 2 * ESTACK, mf). *)
pmkst HS1.
eapply SRr_bind.
{ apply (k_strlen_at B RLO RHI LLVMF_STK arodata_okS G HPRE W2 (ms_regs ms) (ms_mem ms) LLVMF_STK (e_sp0 g) []
    (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 _ (4 * Z.of_nat (m_nrec g) + 7) nm r
    (mf - e_sp0 g) (Z_to_bv 64 (BASE + 6552)) HJ R1_10).
  - clear - Hnm64. lia.
  - clear - Hln. lia.
  - clear - Hln Hc40. lia.
  - clear - Hnm64 Hln C1. lia.
  - exact Hsp1.
  - exact Hom.
  - clear - G2. lia.
  - clear - G7 Hes. lia.
  - exact R1_3.
  - exact R1_4.
  - exact R1_1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact T2.
  - intros a Ha. split; [apply T3; exact Ha|]. rewrite Hsp1. clear - Ha Hnm64 Hln G1 Hes. lia.
  - intros a Ha. clear - Ha Hnm64 Hln G1 Hes. lia.
  - exact T4.
  - exact T5.
  - exact T6.
  - exact T7.
  - exact Haro1. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Hfr3 & Hpres3).
clear T0 T1 T2 T3 T4 T5 T6 T7 Haro1.
assert (R3p : forall (q : bv 5), acallee_saved (bv_unsigned q) -> getr regs3 q = getr (ms_regs ms) q)
  by (intros q Hq; exact (kn_pres q _ _ HP3 Hq)).
assert (HKP3 : kkeep B g pos mf ly2 S2 W2 mem2 mem3).
{ apply (kn_keep_all (ms_mem ms) mem3 HKP1). intros a Ha Hw. apply Hfr3; [exact Ha|]. clear - Hw Hes. lia. }
clear Hfr3 Hpres3.
(* ================ run 2: +0x1998, sext.w a0,a0, mv a1,s2, ld a2,144(s1), check_str ================ *)
remember (Eimg (Ereg regs3 [Z_to_bv 64 cap])) as E2 eqn:HE2.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply Eimg_env).
assert (EE2 : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E2 n = getr regs3 q)
  by (intros n q Hn; rewrite HE2; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E2_32 : ew E2 32 = Z_to_bv 64 cap)
  by (rewrite HE2, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (U2_9 : bv_unsigned (ew E2 9) = mf).
{ rewrite (EE2 9%nat 9%bv eq_refl), (R3p 9%bv ltac:(kn_cs)), R1_9. unfold w64. apply unsigned_lit_small.
  exact Hmf64. }
assert (L144 : val_mem SEGS (rd W2 mem3) (mf + 144) 8 cap).
{ apply (k_vm_hi B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
    ameta_inv arodata_okS G HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH mem3 (mf + 144) 8 cap HKP3);
  [clear; lia | clear - G2 G3; cbn; lia | exact V144]. }
assert (HS2 : st_ok_pi SEGS VAL E2 kn_ss2
  (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 (BASE + 0x1998)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold kn_ss2. apply pa_entry_st_ok_full.
  - rewrite HE2. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold kn_r2, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U2_9. split; [clear - G1 C1; lia|]. split; [clear - G2 G3; lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E2 _ mf 144 8 (SOff 32 0) cap);
    [ cbn [sv_denot]; rewrite E2_32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | clear - Hln Hc40; cbn; lia | cbn; lia | exact L144 ].
  - cbn [pairwise_disjoint all_disjoint].
    repeat match goal with |- _ /\ _ => split end; exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [exact I | split; exact I]. }
paj_run_shc RUNP RUNC HS2 HJ3.
{ intros a (rg & Hr & Ha). cbn [kn_ss2 ss_mem In] in Hr.
  destruct Hr as [<- | []]. unfold kn_r2 in Ha.
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 ->
  aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem3 a).
{ intros a Ha. apply (kept_of_frame E2 _ (w_H W2) mem3 (ms_mem ms0) (fun _ => False) HFr);
  [| exact Ha | intros []].
  intros bb wlo whi aa Hin Hr. unfold kn_ss2, windows in Hin. cbn in Hin.
  destruct Hin as [Eq | []]. injection Eq as <- <- <-. cbn [base_val] in Hr. lia. }
clear HF HFr HG.
assert (HKP4 : kkeep B g pos mf ly2 S2 W2 mem2 (ms_mem ms0))
  by (apply (kn_keep_all mem3 (ms_mem ms0) HKP3); intros a Ha _; exact (KEEP2 a Ha)).
clear KEEP2.
(* 0x8210c sext.w a0,a0: a0 = r < 40, unchanged. *)
assert (X10 : ew E2 10 = Z_to_bv 64 r) by (rewrite (EE2 10%nat 10%bv eq_refl), Ha03; reflexivity).
kn_reg HS2 (10%bv : bv 5) R2_10. rewrite (kn_sextw E2 10 r X10 ltac:(clear - Hln Hc40; lia)) in R2_10.
prreg HS2 (11%bv : bv 5) R2_11. prreg HS2 (12%bv : bv 5) R2_12. prreg HS2 (1%bv : bv 5) R2_1.
prreg HS2 (2%bv : bv 5) R2_2. prreg HS2 (3%bv : bv 5) R2_3. prreg HS2 (4%bv : bv 5) R2_4.
prreg HS2 (8%bv : bv 5) R2_8. prreg HS2 (9%bv : bv 5) R2_9. prreg HS2 (18%bv : bv 5) R2_18.
prreg HS2 (21%bv : bv 5) R2_21. prreg HS2 (22%bv : bv 5) R2_22. prreg HS2 (23%bv : bv 5) R2_23.
prreg HS2 (25%bv : bv 5) R2_25. prreg HS2 (26%bv : bv 5) R2_26.
rewrite (EE2 18%nat 18%bv eq_refl), (R3p 18%bv ltac:(kn_cs)), R1_18 in R2_11, R2_18.
rewrite E2_32 in R2_12.
rewrite (EE2 2%nat 2%bv eq_refl), (R3p 2%bv ltac:(kn_cs)), R1_2 in R2_2.
rewrite (EE2 3%nat 3%bv eq_refl), (R3p 3%bv ltac:(kn_cs)), R1_3 in R2_3.
rewrite (EE2 4%nat 4%bv eq_refl), (R3p 4%bv ltac:(kn_cs)), R1_4 in R2_4.
rewrite (EE2 8%nat 8%bv eq_refl), (R3p 8%bv ltac:(kn_cs)), R1_8 in R2_8.
rewrite (EE2 9%nat 9%bv eq_refl), (R3p 9%bv ltac:(kn_cs)), R1_9 in R2_9.
rewrite (EE2 21%nat 21%bv eq_refl), (R3p 21%bv ltac:(kn_cs)), R1_21 in R2_21.
rewrite (EE2 22%nat 22%bv eq_refl), (R3p 22%bv ltac:(kn_cs)), R1_22 in R2_22.
rewrite (EE2 23%nat 23%bv eq_refl), (R3p 23%bv ltac:(kn_cs)), R1_23 in R2_23.
rewrite (EE2 25%nat 25%bv eq_refl), (R3p 25%bv ltac:(kn_cs)), R1_25 in R2_25.
rewrite (EE2 26%nat 26%bv eq_refl), (R3p 26%bv ltac:(kn_cs)), R1_26 in R2_26.
destruct (kn_str (ms_mem ms0) _ (proj1 HJ3) HKP4) as (T0 & T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8).
destruct (k_aro B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
  ameta_inv arodata_okS G HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH (ms_mem ms0) _ HJ3) as [_ Haro2].
destruct (k_achain B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
  ameta_inv arodata_okS G HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH (ms_mem ms0) HKP4) as [ch Hch].
assert (Hsp2 : spZ (ms_regs ms0) = e_sp0 g + (mf - e_sp0 g)).
{ unfold spZ. rewrite R2_2. unfold w64. rewrite unsigned_lit_small by exact Hmf64. lia. }
(* 0x82118: check_str (r, nm, cap_name), r < cap_name (n_fits); it returns to +0x19a8. *)
pmkst HS2. rewrite kn_psig.
eapply SRr_bind.
{ apply (k_check_str_at B RLO RHI LLVMF_STK arodata_okS G HPRE W2 (ms_regs ms0) (ms_mem ms0) LLVMF_STK (e_sp0 g) []
    (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 _ (4 * Z.of_nat (m_nrec g) + 7)
    (mf - e_sp0 g) (Z_to_bv 64 (BASE + 6568)) ch r nm cap HJ3 Hsp2 Hom).
  - clear - G2. lia.
  - unfold check_str.CHECK_STR_STK. clear - G7 Hes. lia.
  - exact R2_3.
  - exact R2_4.
  - exact R2_1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by (clear - HBASE; lia). clear - HBLO. lia.
  - replace (e_sp0 g + (mf - e_sp0 g)) with mf by lia.
    replace (s0Z (ms_regs ms0)) with (e_sp0 g); [exact Hch|].
    unfold s0Z. rewrite R2_8. unfold w64. rewrite unsigned_lit_small by (clear - G1 G2 G3 C1; lia). reflexivity.
  - exact Haro2.
  - exact R2_10.
  - exact R2_11.
  - exact R2_12.
  - clear - Hln Hc40. lia.
  - clear - Hln Hc40. lia.
  - intros _. unfold check_str.tcheck_str_ok.
    split; [clear - Hln; lia|]. split; [exact T0|]. split; [exact T8|]. split; [exact T2|].
    split; [intros a Ha; rewrite Hsp2; unfold check_str.CHECK_STR_STK; clear - Ha T1 Hln G1 Hes; lia|].
    split; [exact T4|]. split; [exact T5|]. split; [exact T6 | exact T7]. }
cbv beta. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc & HP4 & -> & -> & ->).
replace (e_sp0 g + (mf - e_sp0 g)) with mf in HJc by lia.
pose proof (kn_keep_cs (ms_mem ms0) mem4 _ _ HKP4 HJc) as HKP5.
assert (R5p : forall (q : bv 5), acallee_saved (bv_unsigned q) -> getr regs4 q = getr (ms_regs ms0) q)
  by (intros q Hq; exact (kn_pres q _ _ HP4 Hq)).
rewrite Z.add_0_r in HJ4.
apply Hk.
- split; [exact HJ4|]. split; [exact HKP5|].
  split; [rewrite (R5p 2%bv ltac:(kn_cs)); exact R2_2|].
  split; [rewrite (R5p 9%bv ltac:(kn_cs)); exact R2_9|].
  split; [rewrite (R5p 8%bv ltac:(kn_cs)); exact R2_8|].
  split; [rewrite (R5p 3%bv ltac:(kn_cs)); exact R2_3|].
  split; [rewrite (R5p 4%bv ltac:(kn_cs)); exact R2_4|].
  split; [rewrite (R5p 21%bv ltac:(kn_cs)); exact R2_21|].
  rewrite (R5p 23%bv ltac:(kn_cs)); exact R2_23.
- split; [rewrite (R5p 22%bv ltac:(kn_cs)); exact R2_22|].
  split; [rewrite (R5p 25%bv ltac:(kn_cs)); exact R2_25|].
  rewrite (R5p 26%bv ltac:(kn_cs)); exact R2_26.
- rewrite (R5p 18%bv ltac:(kn_cs)). exact R2_18.
Qed.

End run.
End h.

Lemma k_name : k_name_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS G.
Proof.
unfold k_name_stmt.
intros HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH regs mem md Q HKC HKR H24 Hk.
exact (kn_run HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH regs mem md Q HKC HKR H24 Hk).
Qed.

Check (k_name : k_name_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS G).

End c.
End b.
End a.
