(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YI08.v:162-174, 176-180;
   projects/cgif/cgif_file_fuzzer/proofs/lib/YN13.v:121-125; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC1n.v:201-203, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_D1.v, with its addresses and numbers changed; 338 of its 427 lines of code are new or changed and 5976 lines of the source are left out. *)
(* k_disp (LLVMFuzzerTestOneInput_seg_K_hand_stmt.v k_disp_stmt): the stretch +0x19c0 .. +0x19dc (fuzz_identity.asan-ubsan
   0x82134 .. 0x82150) of LLVMFuzzerTestOneInput's ASan+UBSan walk (image B), on the n_r = 0 path. The listing
   (the neutral disassembly of fuzz_identity.asan-ubsan): 0x82134 loads s3 from the machine
   frame's slot mf+184 (dp), 0x82138 copies it to a0, 0x8213c calls the strlen wrapper (returns n_ld), 0x82140
   sign-extends a0 from 32 bits, 0x82144 copies s3 to a1, 0x82148 copies s6 (cap_disp) to a2, 0x8214c calls
   check_str; the stretch ends at the return 0x82150. No inline ASan check and no __asan_report call is in it: the
   only load is from the machine frame (mf+184, above the shadowed side stack), and the reads of dp's bytes are the
   callees' (their contracts take the string facts of ks_str). *)
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

(* ---- the symbolic states -------------------------------------------------------------------------------- *)
(* +0x19c0: the machine frame's slot mf+184 (dp), read-only; atom 32 is dp. *)
Definition kd_r1mf : YP09.region :=
  YP09.mkRegion (Some 9%nat) 184 192 184 184 [YP09.mkChunk 184 (CVal 8 (SOff 32 0))].
Definition kd_ss1 : sstate := mkSS 0x19c0 sr_atoms [kd_r1mf] None (mkFacts [] [] []).
(* +0x19cc: the return of the strlen wrapper; no memory. *)
Definition kd_ss2 : sstate := mkSS 0x19cc sr_atoms [] None (mkFacts [] [] []).

(* The callee-saved side condition of aregs_preserved, decided on the computed register literal (no lia over the
   walk's context). *)
Lemma kd_cs_ok : forall r : Z,
  ((r =? 2) || (r =? 3) || (r =? 4) || (r =? 8) || (r =? 9) || ((18 <=? r) && (r <=? 27)))%bool = true ->
  acallee_saved r.
Proof.
intros r H. unfold acallee_saved.
destruct (Z.eqb_spec r 2), (Z.eqb_spec r 3), (Z.eqb_spec r 4), (Z.eqb_spec r 8), (Z.eqb_spec r 9),
  (Z.leb_spec 18 r), (Z.leb_spec r 27); cbn in H; first [discriminate H | lia].
Qed.
Ltac kd_cs := apply kd_cs_ok; vm_compute; reflexivity.

Lemma kd_pres : forall (r : bv 5) (regs regs' : bvmap 5 word),
  aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof.
intros r regs regs' H Hr. specialize (H (bv_unsigned r) Hr). rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.

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

(* kkeep through a step that changed no byte kkeep pins. *)
Lemma kd_kkeep_eq : forall (g : ectx) (pos mf : Z) ly2 S2 (W2 : world SEGS) (mem2 m m' : word -> option byte),
  kkeep B g pos mf ly2 S2 W2 mem2 m ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (mf - (16 + 2 * ESTACK) <= a < mf) ->
     aview SEGS (w_H W2) m' a = aview SEGS (w_H W2) m a) ->
  (forall b n i, In (b, n) (ablocks B ly2 S2) -> 0 <= i < req_size n ->
     aview SEGS (w_H W2) m' (b + i) = aview SEGS (w_H W2) m (b + i)) ->
  (forall a, (in_zr a (frame_rng ly2 (4, pos)) \/
              in_zr a (shadow_addr (frame_addr ly2 4 pos), fs_frame_bytes 4 / 8)) ->
     ~ (SFa g pos + V_cnt <= a < SFa g pos + V_cnt + 8) -> a <> shadow_addr (SFa g pos) + 90 ->
     aview SEGS (w_H W2) m' a = aview SEGS (w_H W2) m a) ->
  kkeep B g pos mf ly2 S2 W2 mem2 m'.
Proof.
intros g pos mf ly2 S2 W2 mem2 m m' (K1 & K2 & K3) E1 E2 E3. split; [|split].
- intros a Ha Hw. rewrite (E1 a Ha Hw). exact (K1 a Ha Hw).
- intros b n i Hb Hi. rewrite (E2 b n i Hb Hi). exact (K2 b n i Hb Hi).
- intros a Hr Hc Hs. rewrite (E3 a Hr Hc Hs). exact (K3 a Hr Hc Hs).
Qed.

Section h.
Hypothesis HPRE : KPREn.
Let LAWS : AR_laws SEGS B := k_laws B RLO RHI LLVMF_STK arodata_okS G HPRE.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Section run.
Variables (g : ectx) (pos mf nm tk dp : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
  (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model).
Hypothesis HKH : KHn g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2.
Let KG := k_geom B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
  ameta_inv arodata_okS G HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH.

(* kkeep through a step that changed no byte outside the callee window [mf - 2 * ESTACK, mf). *)
Lemma kd_kkeep_low : forall m m' md, AR SEGS B ly2 S2 W2 m md ->
  kkeep B g pos mf ly2 S2 W2 mem2 m ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (mf - 2 * ESTACK <= a < mf) ->
     aview SEGS (w_H W2) m' a = aview SEGS (w_H W2) m a) ->
  kkeep B g pos mf ly2 S2 W2 mem2 m'.
Proof.
intros m m' md HAR HKP HE.
pose proof KG as (G1 & G2 & G3 & _ & _ & _ & _ & G8 & G9 & _ & _ & G12 & _ & G14 & G15 & _).
pose proof asan_consts as (C1 & _).
apply (kd_kkeep_eq g pos mf ly2 S2 W2 mem2 m m' HKP).
- intros a Ha Hw. apply HE; [clear - Ha C1; lia | unfold ESTACK in *; clear - Hw; lia].
- intros b n i Hb Hi.
  destruct (al_blocks _ _ LAWS ly2 S2 W2 m md b n HAR Hb) as (_ & Hb0 & Hbc & _).
  apply HE; [clear - Hb0 Hbc Hi C1; lia | unfold ESTACK; clear - Hb0 Hbc Hi G1; lia].
- intros a Hr _ _. unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. rewrite G12 in Hr.
  change (fs_frame_bytes 4) with 1024 in Hr. change (1024 / 8) with 128 in Hr.
  apply HE; [clear - Hr G8 G9 G14 G15 C1; lia | unfold ESTACK; clear - Hr G1 G8 G9 G14 G15; lia].
Qed.

(* kkeep through check_str, from its own journal (no frame, no write range, the same layout and state). *)
Lemma kd_kkeep_cs : forall m m' md md',
  ajournal SEGS B check_str.CHECK_STR_STK mf [] ly2 S2 W2 m md [] ly2 S2 W2 m' md' 0 ->
  kkeep B g pos mf ly2 S2 W2 mem2 m -> kkeep B g pos mf ly2 S2 W2 mem2 m'.
Proof.
intros m m' md md' (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & _ & F4 & _) HKP.
pose proof KG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hin4).
apply (kd_kkeep_eq g pos mf ly2 S2 W2 mem2 m m' HKP).
- intros a Ha Hw. apply F1; [exact Ha | unfold check_str.CHECK_STR_STK; exact Hw].
- intros b n i Hb Hi. exact (F2 b n i Hb Hb Hi (inFP_nil _)).
- intros a Hr _ _. exact (F4 4 pos a Hin4 Hr (inFP_nil _)).
Qed.

(* dp's string: n_EXP_DP ++ [0] in the live block (dp, max cap_disp 1), n_ld < cap_disp < 64. *)
Lemma kd_ld : 0 <= SlotModel.n_ld (e_pl g) < SlotModel.t_cap_disp (e_pl g) /\ SlotModel.t_cap_disp (e_pl g) < 64.
Proof.
pose proof HKH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnr).
destruct (KModel.n_r0 _ Hnr) as [_ Hfits].
destruct (KModel.fits_unfold _ Hfits) as (_ & _ & Hldc).
assert (H0 : 0 <= SlotModel.n_ld (e_pl g)) by (unfold SlotModel.n_ld; lia).
assert (H64 : SlotModel.t_cap_disp (e_pl g) < 64)
  by (unfold SlotModel.t_cap_disp; apply Z.mod_pos_bound; lia).
clear - H0 H64 Hldc. lia.
Qed.

Lemma kd_dp_str : forall m md, AR SEGS B ly2 S2 W2 m md -> kkeep B g pos mf ly2 S2 W2 mem2 m ->
  let r := SlotModel.n_ld (e_pl g) in
  0 < dp /\ dp + r + 1 <= alloc_ceiling /\
  first_byte SEGS W2 m dp (r + 1) 0 r /\
  (forall a, dp <= a < dp + (r + 1) -> aview SEGS (w_H W2) m a <> None) /\
  amem_range dp (r + 1) /\
  range_addressable (aview SEGS (w_H W2) m) SHADOW_OFF dp (r + 1) /\
  shadow_hull_vis (aview SEGS (w_H W2) m) dp (r + 1) /\
  (forall a, dp + r < a < dp + r - (dp + r) mod 8 + 8 -> aview SEGS (w_H W2) m a <> None) /\
  (dp + r + 1 <= IMG_LO \/ IMG_TOP <= dp).
Proof.
intros m md HAR HKP.
pose proof HKH as (_ & _ & _ & _ & _ & _ & HHB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  HBY & Hnr).
destruct (HBY Hnr) as (_ & _ & HBdp).
destruct (KModel.n_r0 _ Hnr) as [Hwok _].
pose proof (KModel.nzb_EXP_DP _ Hwok) as Hnz.
pose proof kd_ld as ((Hld0 & Hldc) & _).
destruct HHB as (Hperm & _).
assert (Hind : In (dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1) (ablocks B ly2 S2)).
{ eapply Permutation_in; [apply Permutation_sym; exact Hperm | right; right; left; reflexivity]. }
assert (Hlen : Z.of_nat (length (SlotModel.n_EXP_DP (e_pl g))) + 1 <=
  req_size (Z.max (SlotModel.t_cap_disp (e_pl g)) 1)).
{ change (Z.of_nat (length (SlotModel.n_EXP_DP (e_pl g)))) with (SlotModel.n_ld (e_pl g)).
  unfold req_size. destruct (Z.eqb_spec (Z.max (SlotModel.t_cap_disp (e_pl g)) 1) 0) as [E | E];
  clear - Hld0 Hldc E; lia. }
exact (ks_str B RLO RHI LLVMF_STK arodata_okS G HPRE g pos mf ly2 S2 W2 mem2 m md dp _ _ HAR HKP Hind HBdp Hnz Hlen).
Qed.

(* sext.w of a value below 2 ^ 31 *)
Lemma kd_sextw : forall (E : env) (a : sv) v, sv_denot E a = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 ->
  sv_denot E (SAluw ALU_ADD a (SLit 0)) = Z_to_bv 64 v.
Proof.
intros E a v Ha Hv.
rewrite denot_lit_U. f_equal.
rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite U_SLit.
assert (Ua : U E a = v) by (unfold U; rewrite Ha; apply unsigned_lit_small; lia).
rewrite Ua. change (zcanon 0 mod 2 ^ 32) with 0. rewrite Z.add_0_r, Z.mod_small by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small (v + 2 ^ 31) (2 ^ 32)) by lia. rewrite Z.add_simpl_r. apply Z.mod_small. lia.
Qed.
(* The same in the form prreg leaves for `sext.w a0,a0` (SAluw ALU_ADD (SOff 10 0) (SLit 0), normalized). *)
Lemma kd_sextw_reg : forall (w : word) v, w = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 ->
  sext 64 (alu32 ALU_ADD (low32 w) (low32 (Z_to_bv 64 0))) = Z_to_bv 64 v.
Proof.
intros w v -> Hv. exact (kd_sextw (mkEnv (fun _ => Z_to_bv 64 0) (fun _ => [])) (SLit v) v eq_refl Hv).
Qed.

Lemma kd_main : forall regs mem md (Q : world SEGS -> config -> Prop),
  KCn g pos mf tk ly2 S2 W2 mem2 regs mem md -> KR g pos regs -> getr regs 18 = w64 nm ->
  (forall regs' mem' md', KCn g pos mf tk ly2 S2 W2 mem2 regs' mem' md' -> KR g pos regs' -> getr regs' 18 = w64 nm ->
    SRr SEGS W2 (cfg_at SEGS (BASE + 0x19dc) regs' mem' md') Q) ->
  SRr SEGS W2 (cfg_at SEGS (BASE + 0x19c0) regs mem md) Q.
Proof.
intros regs mem md Q (HJ & HKP & Rsp & Rs1 & Rs0 & Rgp & Rtp & Rs5 & Rs7) (Rs6 & Rs9 & Rs10) Rs2 HK.
pose proof KG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & Hin4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_identb)) as HBLO.
pose proof HKH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V184 & _).
pose proof kd_ld as ((Hld0 & Hldc) & Hcap).
pose proof (proj1 HJ) as HAR0.
destruct (kd_dp_str mem md HAR0 HKP) as (Hdp0 & Hdpc & _ & _ & _ & _ & _ & _ & Himg).
set (ld := SlotModel.n_ld (e_pl g)) in *.
set (cap := SlotModel.t_cap_disp (e_pl g)) in *.
assert (Eld : ld = SlotModel.n_ld (e_pl g)) by reflexivity.
assert (Ecap : cap = SlotModel.t_cap_disp (e_pl g)) by reflexivity.
clearbody ld cap.
assert (Hdp64 : 0 <= dp < 2 ^ 64) by (clear - Hdp0 Hdpc Hld0 C1; lia).
assert (Hmf64 : 0 <= mf < 2 ^ 64) by (clear - G1 G2 G3 C1; lia).
assert (Hsp064 : 0 <= e_sp0 g < 2 ^ 64) by (clear - G1 G2 G3 C1; lia).
unfold cfg_at. change (w64 (BASE + 0x19c0)) with (Z_to_bv 64 (BASE + 0x19c0)).
(* ================ run 1: +0x19c0, the load of dp, `mv a0,s3`, and the strlen wrapper ================ *)
remember (Eimg (Ereg regs [Z_to_bv 64 dp])) as E1 eqn:HE1.
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply Eimg_env).
assert (EE1 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E1 n = getr regs r)
  by (intros n r Hn; rewrite HE1; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E1_32 : ew E1 32 = Z_to_bv 64 dp)
  by (rewrite HE1, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (U1_9 : bv_unsigned (ew E1 9) = mf).
{ rewrite (EE1 9%nat 9%bv eq_refl), Rs1. unfold w64. apply unsigned_lit_small. exact Hmf64. }
assert (V184' : val_mem SEGS (rd W2 mem) (mf + 184) 8 dp).
{ apply (k_vm_hi B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
    ameta_inv arodata_okS G HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH mem (mf + 184) 8 dp HKP);
  [clear; lia | clear - G2 G3; lia | exact V184]. }
assert (HS1 : st_ok_pi SEGS VAL E1 kd_ss1
  (restrict (w_H W2) (mkst regs (Z_to_bv 64 (BASE + 0x19c0)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold kd_ss1. apply pa_entry_st_ok_full.
  - rewrite HE1. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold kd_r1mf, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U1_9. split; [clear - Hmf64; lia|]. split; [clear - G2 G3; lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E1 _ mf 184 8 (SOff 32 0) dp);
    [ cbn [sv_denot]; rewrite E1_32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | clear - Hdp64; cbn; lia | cbn; lia | exact V184' ].
  - cbn [pairwise_disjoint all_disjoint].
    repeat match goal with |- _ /\ _ => split end; exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [exact I | split; exact I]. }
paj_run_shc RUNP RUNC HS1 HJ.
{ intros a (r & Hr & Ha). unfold kd_ss1 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | []]. unfold kd_r1mf in Ha.
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. clear - Ha; lia. }
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem a).
{ intros a Ha. apply (kept_of_frame E1 _ (w_H W2) mem (ms_mem ms) (fun _ => False) HFr);
  [| exact Ha | intros []].
  intros bb wlo whi aa Hin Hr. unfold kd_ss1, windows in Hin. cbn in Hin.
  destruct Hin as [Eq | []]. injection Eq as <- <- <-. cbn [base_val] in Hr. clear - Hr; lia. }
clear HF HFr HG.
prreg HS1 (10%bv : bv 5) R1_10. prreg HS1 (1%bv : bv 5) R1_1. prreg HS1 (2%bv : bv 5) R1_2.
prreg HS1 (3%bv : bv 5) R1_3. prreg HS1 (4%bv : bv 5) R1_4. prreg HS1 (8%bv : bv 5) R1_8.
prreg HS1 (9%bv : bv 5) R1_9. prreg HS1 (18%bv : bv 5) R1_18. prreg HS1 (19%bv : bv 5) R1_19.
prreg HS1 (21%bv : bv 5) R1_21. prreg HS1 (22%bv : bv 5) R1_22. prreg HS1 (23%bv : bv 5) R1_23.
prreg HS1 (25%bv : bv 5) R1_25. prreg HS1 (26%bv : bv 5) R1_26.
rewrite E1_32 in R1_10, R1_19.
rewrite (EE1 2%nat 2%bv eq_refl), Rsp in R1_2. rewrite (EE1 3%nat 3%bv eq_refl), Rgp in R1_3.
rewrite (EE1 4%nat 4%bv eq_refl), Rtp in R1_4. rewrite (EE1 8%nat 8%bv eq_refl), Rs0 in R1_8.
rewrite (EE1 9%nat 9%bv eq_refl), Rs1 in R1_9. rewrite (EE1 18%nat 18%bv eq_refl), Rs2 in R1_18.
rewrite (EE1 21%nat 21%bv eq_refl), Rs5 in R1_21. rewrite (EE1 22%nat 22%bv eq_refl), Rs6 in R1_22.
rewrite (EE1 23%nat 23%bv eq_refl), Rs7 in R1_23. rewrite (EE1 25%nat 25%bv eq_refl), Rs9 in R1_25.
rewrite (EE1 26%nat 26%bv eq_refl), Rs10 in R1_26.
assert (K1 : kkeep B g pos mf ly2 S2 W2 mem2 (ms_mem ms))
  by (apply (kd_kkeep_low mem (ms_mem ms) md HAR0 HKP); intros a Ha _; exact (KEEP1 a Ha)).
clear KEEP1.
pose proof (proj1 HJ) as HAR1.
destruct (kd_dp_str (ms_mem ms) _ HAR1 K1) as (_ & _ & Hfb1 & Hpr1 & Hamr1 & Hras1 & Hhull1 & Htail1 & _).
rewrite <- Eld in Hfb1, Hpr1, Hamr1, Hras1, Hhull1, Htail1.
destruct (k_aro B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
  ameta_inv arodata_okS G HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH (ms_mem ms) _ HJ) as [_ Haro1].
assert (Hsp1 : spZ (ms_regs ms) = e_sp0 g + (mf - e_sp0 g)).
{ unfold spZ. rewrite R1_2. unfold w64. rewrite unsigned_lit_small by exact Hmf64. clear; lia. }
assert (Ho16 : (mf - e_sp0 g) mod 16 = 0).
{ pose proof (Z.div_mod mf 32 ltac:(discriminate)) as D1.
  pose proof (Z.div_mod (e_sp0 g) 16 ltac:(discriminate)) as D2.
  rewrite G6 in D1. rewrite G4 in D2.
  replace (mf - e_sp0 g) with ((2 * (mf / 32) - e_sp0 g / 16) * 16) by (clear - D1 D2; lia).
  apply Z_mod_mult. }
pmkst HS1.
eapply SRr_bind.
{ apply (k_strlen_at B RLO RHI LLVMF_STK arodata_okS G HPRE W2 (ms_regs ms) (ms_mem ms) LLVMF_STK (e_sp0 g) []
    (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 _ (4 * Z.of_nat (m_nrec g) + 7)
    dp ld (mf - e_sp0 g) (Z_to_bv 64 (BASE + 6604)) HJ R1_10).
  - exact Hdp0.
  - exact Hld0.
  - clear - Hldc Hcap; lia.
  - clear - Hdpc Hld0 C1; lia.
  - exact Hsp1.
  - exact Ho16.
  - clear - G2; lia.
  - unfold ESTACK. clear - G7; lia.
  - exact R1_3.
  - exact R1_4.
  - exact R1_1.
  - apply ret_ok_codeptr_v; [clear; lia | reflexivity].
  - exact Hfb1.
  - unfold src_ok. intros a Ha. split; [apply Hpr1; exact Ha|]. rewrite Hsp1. unfold ESTACK.
    clear - Ha Hdpc G1 Hld0; lia.
  - intros a Ha. unfold ESTACK. clear - Ha Hdpc G1 Hld0; lia.
  - exact Hamr1.
  - exact Hras1.
  - exact Hhull1.
  - exact Htail1.
  - exact Haro1. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Hfr3 & _).
assert (K2 : kkeep B g pos mf ly2 S2 W2 mem2 mem3).
{ apply (kd_kkeep_low (ms_mem ms) mem3 _ HAR1 K1). intros a Ha Hw. apply Hfr3; [exact Ha|]. clear - Hw; lia. }
clear Hfr3.
assert (R2p : forall (r : bv 5), acallee_saved (bv_unsigned r) -> getr regs3 r = getr (ms_regs ms) r)
  by (intros r Hr; exact (kd_pres r _ _ HP3 Hr)).
(* ================ run 2: +0x19cc, `sext.w a0,a0`, `mv a1,s3`, `mv a2,s6`, and check_str ================ *)
remember (Eimg (Ereg regs3 [])) as E2 eqn:HE2.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply Eimg_env).
assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs3 r)
  by (intros n r Hn; rewrite HE2; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HS2 : st_ok_pi SEGS VAL E2 kd_ss2
  (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 (BASE + 0x19cc)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold kd_ss2. apply pa_entry_st_ok_full.
  - rewrite HE2. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn [pairwise_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [exact I | split; exact I]. }
pose proof (proj1 HJ3) as HAR3.
paj_run_shc RUNP RUNC HS2 HJ3.
{ apply awr_ok_nil. }
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 ->
  aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem3 a).
{ intros a Ha. apply (kept_of_frame E2 _ (w_H W2) mem3 (ms_mem ms0) (fun _ => False) HFr);
  [| exact Ha | intros []].
  intros bb wlo whi aa Hin Hr. unfold kd_ss2, windows in Hin. cbn in Hin. destruct Hin. }
clear HF HFr HG.
prreg HS2 (10%bv : bv 5) R2_10. prreg HS2 (11%bv : bv 5) R2_11. prreg HS2 (12%bv : bv 5) R2_12.
prreg HS2 (1%bv : bv 5) R2_1. prreg HS2 (2%bv : bv 5) R2_2. prreg HS2 (3%bv : bv 5) R2_3.
prreg HS2 (4%bv : bv 5) R2_4. prreg HS2 (8%bv : bv 5) R2_8. prreg HS2 (9%bv : bv 5) R2_9.
prreg HS2 (18%bv : bv 5) R2_18. prreg HS2 (21%bv : bv 5) R2_21. prreg HS2 (22%bv : bv 5) R2_22.
prreg HS2 (23%bv : bv 5) R2_23. prreg HS2 (25%bv : bv 5) R2_25. prreg HS2 (26%bv : bv 5) R2_26.
rewrite (EE2 10%nat 10%bv eq_refl), Ha03 in R2_10.
rewrite (kd_sextw_reg (w64 ld) ld eq_refl ltac:(clear - Hld0 Hldc Hcap; lia)) in R2_10.
rewrite (EE2 19%nat 19%bv eq_refl), (R2p 19%bv ltac:(kd_cs)), R1_19 in R2_11.
rewrite (EE2 22%nat 22%bv eq_refl), (R2p 22%bv ltac:(kd_cs)), R1_22 in R2_12.
rewrite (EE2 2%nat 2%bv eq_refl), (R2p 2%bv ltac:(kd_cs)), R1_2 in R2_2.
rewrite (EE2 3%nat 3%bv eq_refl), (R2p 3%bv ltac:(kd_cs)), R1_3 in R2_3.
rewrite (EE2 4%nat 4%bv eq_refl), (R2p 4%bv ltac:(kd_cs)), R1_4 in R2_4.
rewrite (EE2 8%nat 8%bv eq_refl), (R2p 8%bv ltac:(kd_cs)), R1_8 in R2_8.
rewrite (EE2 9%nat 9%bv eq_refl), (R2p 9%bv ltac:(kd_cs)), R1_9 in R2_9.
rewrite (EE2 18%nat 18%bv eq_refl), (R2p 18%bv ltac:(kd_cs)), R1_18 in R2_18.
rewrite (EE2 21%nat 21%bv eq_refl), (R2p 21%bv ltac:(kd_cs)), R1_21 in R2_21.
rewrite (EE2 22%nat 22%bv eq_refl), (R2p 22%bv ltac:(kd_cs)), R1_22 in R2_22.
rewrite (EE2 23%nat 23%bv eq_refl), (R2p 23%bv ltac:(kd_cs)), R1_23 in R2_23.
rewrite (EE2 25%nat 25%bv eq_refl), (R2p 25%bv ltac:(kd_cs)), R1_25 in R2_25.
rewrite (EE2 26%nat 26%bv eq_refl), (R2p 26%bv ltac:(kd_cs)), R1_26 in R2_26.
assert (K3 : kkeep B g pos mf ly2 S2 W2 mem2 (ms_mem ms0))
  by (apply (kd_kkeep_low mem3 (ms_mem ms0) _ HAR3 K2); intros a Ha _; exact (KEEP2 a Ha)).
clear KEEP2.
pose proof (proj1 HJ3) as HAR4.
destruct (kd_dp_str (ms_mem ms0) _ HAR4 K3) as (_ & _ & Hfb4 & _ & Hamr4 & Hras4 & Hhull4 & Htail4 & _).
rewrite <- Eld in Hfb4, Hamr4, Hras4, Hhull4, Htail4.
destruct (k_aro B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
  ameta_inv arodata_okS G HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH (ms_mem ms0) _ HJ3) as [_ Haro4].
destruct (k_achain B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
  ameta_inv arodata_okS G HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH (ms_mem ms0) K3) as [ch Hch].
assert (Hsp4 : spZ (ms_regs ms0) = mf)
  by (unfold spZ; rewrite R2_2; unfold w64; apply unsigned_lit_small; exact Hmf64).
assert (Hs04 : s0Z (ms_regs ms0) = e_sp0 g)
  by (unfold s0Z; rewrite R2_8; unfold w64; apply unsigned_lit_small; exact Hsp064).
pmkst HS2.
rewrite (k_psig B RLO RHI LLVMF_STK arodata_okS G HPRE IB_check_str AF_check_str eq_refl).
eapply SRr_bind.
{ apply (k_check_str_at B RLO RHI LLVMF_STK arodata_okS G HPRE W2 (ms_regs ms0) (ms_mem ms0) LLVMF_STK (e_sp0 g) []
    (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 _ (4 * Z.of_nat (m_nrec g) + 7)
    (mf - e_sp0 g) (Z_to_bv 64 (BASE + 6620)) ch ld dp cap HJ3).
  - rewrite Hsp4. clear; lia.
  - exact Ho16.
  - clear - G2; lia.
  - unfold check_str.CHECK_STR_STK, ESTACK. clear - G7; lia.
  - exact R2_3.
  - exact R2_4.
  - exact R2_1.
  - apply ret_ok_codeptr_v; [clear; lia | reflexivity].
  - rewrite unsigned_lit_small by (clear - HBASE; lia). clear - HBLO; lia.
  - replace (e_sp0 g + (mf - e_sp0 g)) with mf by (clear; lia). rewrite Hs04. exact Hch.
  - exact Haro4.
  - exact R2_10.
  - exact R2_11.
  - exact R2_12.
  - clear - Hld0 Hldc Hcap; lia.
  - clear - Hld0 Hldc Hcap; lia.
  - intros _. unfold check_str.tcheck_str_ok.
    split; [exact Hldc|]. split; [exact Hdp0|]. split; [exact Himg|]. split; [exact Hfb4|].
    split; [intros a Ha; rewrite Hsp4; unfold check_str.CHECK_STR_STK, ESTACK; clear - Ha Hdpc G1 Hld0; lia|].
    split; [exact Hamr4|]. split; [exact Hras4|]. split; [exact Hhull4 | exact Htail4]. }
cbv beta. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HJcs & HP5 & -> & -> & ->).
replace (e_sp0 g + (mf - e_sp0 g)) with mf in HJcs by (clear; lia).
rewrite Z.add_0_r in HJ5.
assert (K4 : kkeep B g pos mf ly2 S2 W2 mem2 mem5) by exact (kd_kkeep_cs _ _ _ _ HJcs K3).
assert (R5p : forall (r : bv 5), acallee_saved (bv_unsigned r) -> getr regs5 r = getr (ms_regs ms0) r)
  by (intros r Hr; exact (kd_pres r _ _ HP5 Hr)).
rewrite Ecap in R2_22.
apply HK.
- split; [exact HJ5|]. split; [exact K4|].
  split; [rewrite (R5p 2%bv ltac:(kd_cs)); exact R2_2|].
  split; [rewrite (R5p 9%bv ltac:(kd_cs)); exact R2_9|].
  split; [rewrite (R5p 8%bv ltac:(kd_cs)); exact R2_8|].
  split; [rewrite (R5p 3%bv ltac:(kd_cs)); exact R2_3|].
  split; [rewrite (R5p 4%bv ltac:(kd_cs)); exact R2_4|].
  split; [rewrite (R5p 21%bv ltac:(kd_cs)); exact R2_21|].
  rewrite (R5p 23%bv ltac:(kd_cs)); exact R2_23.
- split; [rewrite (R5p 22%bv ltac:(kd_cs)); exact R2_22|].
  split; [rewrite (R5p 25%bv ltac:(kd_cs)); exact R2_25 | rewrite (R5p 26%bv ltac:(kd_cs)); exact R2_26].
- rewrite (R5p 18%bv ltac:(kd_cs)); exact R2_18.
Qed.

End run.
End h.

Lemma k_disp : k_disp_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS G.
Proof.
unfold k_disp_stmt.
intros HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH regs mem md Q HKC HKR H18 HK.
exact (kd_main HPRE g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HKH regs mem md Q HKC HKR H18 HK).
Qed.

Check (k_disp : k_disp_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS G).

End c.
End b.
End a.
