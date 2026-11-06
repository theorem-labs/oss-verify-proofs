(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Rebound onto the old-pin kit 4f18c75d4900 (base cold/h-rw-pre-7-b-ex_value-rebind): EXB carries exv_rm, the
   memnorm keep from the entry memory, across every run by ExvB_Loop_exw.v's _inv runners at P := exvl_P (e_mem E)
   and across the ex_ws call by its m-form post. Does not rest on tex_word_specX. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B, ex_value, segment CI: the ex_ws CALL, from the internal cut CUT_CM (entry
   + 0x440, B 0x8396c) to the internal cut CUT_CR (entry + 0x460, B 0x8398c, ex_ws's return site).
   - the stretch B 0x8396c .. 0x83988: in->p := p + 1 (UBSan `bgeu 1, p + 1` not taken: p >= 4096; ASan check of q's 8 bytes
     through s4), a0 := q, `jal ex_ws` (the run stops at ex_ws's entry, B_prog_sigma AS_ex_ws);
   - the call: YCbqGcallW.aj_call_xW_sp in the window form (e1 = exv_sp + d - s1, o = s1 - (exv_sp + d)), the callee's
     tex_ws_specX at the cursor i1 + 1 (exv_ws HYP fx), its footprint [(q, q + 8)] in exv_FP; the frame chain, the read-only
     view and EXB after the call are the shared kit (ExvB_Loop_kit.v: KIT_CALL_CHAIN, KIT_RODATA, KIT_EXB_CALL; proofs
     exv_kit_chain / exv_kit_rodata (ExvB_Loop_kitQ.v), exv_kit_call (ExvB_Loop_kitP.v));
   - after the call the cursor is ex_ws's: x0 + len - length (skip (skipn (i1 + 1) x)), the ip of CUT_CR.
   Rule 24: proves no function (kind: segment lemma). Numerals: 0x440, 0x460 (DERIVED: cut offsets, B entry + offset);
   16 (LENGTH: ex_ws's frame, STK_ex_ws); 64, 96, 104, 120, 144, 152, 176 (LENGTH: slot offsets); 8, 16, 20, 24, 32,
   36, 40 (LENGTH: struct ex); 2, 3, 4, 8, 9, 10, 11, 18-27 (WORD: register numbers); 2 ^ 46, 2 ^ 47, 2 ^ 64, 4096 (LENGTH).
   No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames FCiface YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Loop_exw.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import
ExvB_Stmt ExvB_Open_pure ExvB_Open_kt ExvB_Open_fin ExvB_Open_f1 ExvB_Loop_kit ExvB_Loop_kitQ ExvB_Loop_kitP.
Import ListNotations.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.
(* ExvB_Loop_kitQ.v Requires image A's S1ImgA, whose global PAImg instance is then the most recent: re-declare B's *)
#[local] Existing Instance PL_prog_B.
#[local] Existing Instance PI_prog_B.

(* ---- the stretch to the call ---- *)
Definition exo_regs_m : list sv :=
  sr_set (sr_set (sr_set sr_atoms 20%bv (exo_shx (SOff 19 0))) 22%bv (exo_shx (SOff 19 8))) 23%bv (SOff 19 8).
Definition exo_rgm : smem := [ YP09.mkRegion (Some 19%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 11 0))] ].
Definition exo_fcm : list (nat * afact) :=
[ (19%nat, exo_QF); (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (11%nat, exo_PF) ].
Definition ss_cm : sstate := mkSS EXO_CM exo_regs_m exo_rgm None (mkFacts exo_fcm [] []).
Definition exo_SHm : list shent := [mkSHE 19 0 40].
Definition EXO_CR : Z := exv_pc 0x460.

(* a value read through two different hidden-page views *)
Lemma exo_val_kept2 : forall (H H' : word -> bool) (m m' : word -> option byte) a (n : nat) v,
  (forall x, a <= x < a + Z.of_nat n -> aview rsegs H' m' x = aview rsegs H m x) ->
  val_mem rsegs (mrestrict H m) a n v -> val_mem rsegs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v HE Hv kk Hk. rewrite (mbyte_of_aview rsegs H H' m m' (a + Z.of_nat kk)); [exact (Hv kk Hk)|].
apply HE. lia.
Qed.

Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis HYP : EXV_HYP B ARx SK.
Let LAWS := eh_laws B ARx SK HYP.
Let RUNTO (mem0 : word -> option byte) := SRr_run_to_tok_AJx_inv (SK := SK) rsegs B (@prh_pst prh_img_B) ARx LAWS
  B_prog_segs_low B_prog_tbl B_prog_tbl_ok B_prog_wx (exvl_P mem0) (exvl_PLAW mem0).

(* ExvLoop's shared call kit (lib/B/Prog/ExvB_Loop_kit.v, proofs ExvB_Loop_kitQ.v / ExvB_Loop_kitP.v, on the base) *)
Let KCHAIN : KIT_CALL_CHAIN (fx := fx) B ARx SK :=
  ltac:(first [exact (exv_kit_chain B ARx SK HYP fx) | exact (exv_kit_chain B ARx SK fx)]).
Let KRO : KIT_RODATA (fx := fx) B ARx SK :=
  ltac:(first [exact (exv_kit_rodata B ARx SK HYP fx) | exact (exv_kit_rodata B ARx SK fx)]).
Let KCALL : KIT_EXB_CALL (fx := fx) B ARx SK :=
  ltac:(first [exact (exv_kit_call B ARx SK HYP fx) | exact (exv_kit_call B ARx SK fx)]).

(* the post of the ex_ws call, at the allocator state (lyc, Sc, Hpc) and memory memc of the call: the kit's
   tex_ws_specX Q (4f18c75d4900: S' = S) in its m-form (fQmn: the memnorm keep from the call memory) *)
Definition exo_KQ (Ex : exv_e) (lyc : alayout) (Sc : astate) (Hpc : list Z) (memc : word -> option byte)
    (ly' : alayout) (S' : astate) (Hp' : list Z)
    (W' : world rsegs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  ((room_live_cf Sc -> room_live_cf S') /\
   val_mem rsegs (mrestrict (w_H W') mem') (e_q Ex) 8
     (e_x0 Ex + Z.of_nat (length (e_x Ex)) - Z.of_nat (length (PjGrammar.skip (skipn (Z.to_nat (exv_i1 Ex + 1)) (e_x Ex))))) /\
   Hp' = Hpc /\ S' = Sc /\ ablocks B ly' S' = ablocks B lyc Sc /\
   prh_ledger B ly' S' Hp' W' mem' (e_Lam Ex) (e_peak Ex) (e_cnt Ex) (e_fail Ex) (e_ran Ex) (e_most Ex) (e_own Ex)) /\
  (YAkMemnorm.memnorm rsegs memc -> YAkMemnorm.memnorm rsegs mem').

Lemma exo_mid : forall n, CUT_CR (fx := fx) B ARx SK n -> CUT_CM (fx := fx) B ARx SK n.
Proof.
intros n HR. unfold CUT_CM.
intros Ex lyc Sc Hpc Wc regs memc mdc k pos c vv dlc Hn HPRE HB Hi1 Hnth Hcc Hd1 Hcur Hdlc Hdif R11 R27 R20 R22 R23
  S64 S96 S104 S120 S144 S152.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (exo_STK_ge Ex) as HSTK.
pose proof (exv_s1_le Ex) as ((S1a & S1b) & S1m).
pose proof HPRE as HPRE'. unfold EXV_PRE in HPRE'. cbv zeta in HPRE'.
destruct HPRE' as (HFP & _ & _ & _ & _ & _ & Hq8 & _ & Hspq & Hqd & Hwin & Hsrc0 & _ & Hlen3 & Hi0 & Hdep & _ & Hdl &
  _ & _ & _ & Hsq & _ & _).
destruct HFP as ((_ & _ & _ & _ & _ & Hastk & _) & _ & Hm64).
destruct Hastk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & _ & Htop).
destruct Hwin as (Hd0 & Hd16 & Hdtop & _).
destruct Hsrc0 as (_ & Hx4 & Hxc & _).
pose proof HB as (HJ & _ & _ & HFZ & _ & _ & HRM0 & _ & _ & R2 & R8 & R9 & R18 & R24 & R25 & R26 & R19 & R3 & R4 &
  _ & _ & _ & _ & _ & _ & _ & HQR & _).
pose proof (proj2 HRM0) as HPM.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehi & _).
pose proof Hcur as (V0 & V8 & V16 & V24 & V32).
assert (S1c : exv_sp Ex - 304 <= exv_s1 Ex).
{ unfold exv_s1. rewrite exv_land32. unfold exv_sp. lia. }
assert (Hi1' : 0 <= exv_i1 Ex).
{ unfold exv_i1, exv_len, exv_X. pose proof (PjGrammar.skip_len (skipn (Z.to_nat (e_i0 Ex)) (e_x Ex))).
  pose proof (length_skipn (Z.to_nat (e_i0 Ex)) (e_x Ex)). lia. }
assert (Hlen_def : exv_len Ex = Z.of_nat (length (e_x Ex))) by reflexivity.
unfold exv_sp, exv_STK in *.
assert (Hsp0 : 0 <= spZ (e_regs Ex)) by (pose proof (bv_unsigned_in_range _ (getr (e_regs Ex) 2%bv)); unfold spZ; lia).
set (q := e_q Ex) in *. set (s1 := exv_s1 Ex) in *. set (p := e_x0 Ex + exv_i1 Ex) in *.
assert (Hp_def : p = e_x0 Ex + exv_i1 Ex) by reflexivity.
(* the environment *)
remember (Ereg regs []) as En eqn:HE.
assert (E11 : ew En 11 = Z_to_bv 64 p) by (subst En; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact R11).
assert (E19 : ew En 19 = Z_to_bv 64 q) by (subst En; rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
assert (E25 : ew En 25 = Z_to_bv 64 SHADOW_OFF) by (subst En; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
assert (Uq : bv_unsigned (ew En 19) = q) by (rewrite E19; apply unsigned_lit_small; lia).
assert (Up : bv_unsigned (ew En 11) = p) by (rewrite E11; apply unsigned_lit_small; lia).
assert (Usb : bv_unsigned (ew En 25) = SHADOW_OFF) by (rewrite E25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (Dq0 : sv_denot En (exo_shx (SOff 19 0)) = Z_to_bv 64 (SHADOW_OFF + q / 8)).
{ rewrite (exo_denot_shx En 19 0 q SHADOW_OFF E19 E25) by (unfold SHADOW_OFF; lia). f_equal. lia. }
assert (Dq8 : sv_denot En (exo_shx (SOff 19 8)) = Z_to_bv 64 (SHADOW_OFF + (q + 8) / 8))
  by (rewrite (exo_denot_shx En 19 8 q SHADOW_OFF E19 E25) by (unfold SHADOW_OFF; lia); reflexivity).
assert (HS : st_ok rsegs En ss_cm (restrict (w_H Wc) (mkst regs (Z_to_bv 64 EXO_CM) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_cm. apply exw_st_ok_full.
  - unfold exo_regs_m.
    apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [rewrite HE; apply regs_ok_Ereg| |]| |]| |];
      try (intros X; discriminate X).
    + rewrite Dq0. exact R20.
    + rewrite Dq8. exact R22.
    + cbn [sv_denot]. rewrite Uq. exact R23.
  - vm_compute. reflexivity.
  - unfold exo_rgm. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Uq. split; [lia|]. split; [lia|].
    split; [intros o' Ho; apply (apresent_writable rsegs); apply Hpres; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs En _ q 0 8 (SOff 11 0) p);
      [cbn [sv_denot]; rewrite Up, Z.add_0_r; reflexivity | cbn; lia | zside | rewrite Z.add_0_r; exact V0].
  - apply pairwise_disjoint_of_extents. unfold exo_rgm. cbn [map]. unfold extent_of_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Uq.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok exo_fcm]. unfold afact_ok, exo_QF, exo_PF. cbn [af_lo af_hi af_al2].
    rewrite Uq, Usb, Up. change (2 ^ 3) with 8.
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia. }
assert (HBx : U En exo_Bx = SHADOW_OFF) by (unfold exo_Bx; rewrite (U_atom En 25 SHADOW_OFF E25) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok rsegs exo_Bx exo_SHm En (mrestrict (w_H Wc) memc)).
{ unfold exo_SHm. constructor; [|constructor].
  apply (shent_ok_of_range rsegs (w_H Wc) memc En exo_Bx 19 q 40 q 0 40 HQR HBx);
    [rewrite (U_atom En 19 q E19) by lia; reflexivity | lia | lia |].
  intros x Hx. unfold SHADOW_OFF. lia. }
unfold cfg_at. change (w64 (exv_pc 0x440)) with (Z_to_bv 64 EXO_CM).
(* ---- the stretch to ex_ws's entry ---- *)
exw_run_to (RUNTO (e_mem Ex)) HS HJ SHOK HPM (B_prog_sigma AS_ex_ws).
{ exo_awr Uq Uq. }
exw_kept_of HFr (fun a => q <= a < q + 8) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?Uq in h).
rename KEPT into K1. rename HG into G1.
clear HF HFr.
lazymatch type of HS with st_ok _ ?Ex' ?ssF (restrict _ ?msF) =>
  assert (AG1 : env_agree 32 (Ereg regs []) Ex')
    by (rewrite <- HE; split; [intros nn Hnn; repeat (rewrite ew_ewset_other by lia); reflexivity | reflexivity]);
  pose proof (regs_kept_of_st_ok rsegs _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 24; 25; 26; 27; 21]%bv HS AG1
    ltac:(vm_compute; reflexivity)) as KR;
  pose proof (st_ok_restrict_reg rsegs (w_H Wc) _ _ _ 20%bv HS) as P20;
  pose proof (st_ok_restrict_reg rsegs (w_H Wc) _ _ _ 22%bv HS) as P22;
  pose proof (st_ok_restrict_reg rsegs (w_H Wc) _ _ _ 23%bv HS) as P23;
  change (sr_get (ss_regs ssF) 20%bv) with (exo_shx (SOff 19 0)) in P20;
  change (sr_get (ss_regs ssF) 22%bv) with (exo_shx (SOff 19 8)) in P22;
  let e23 := eval vm_compute in (sr_get (ss_regs ssF) 23%bv) in change (sr_get (ss_regs ssF) 23%bv) with e23 in P23
end.
lazymatch type of HS with st_ok _ ?Ex' _ _ =>
  rewrite (exo_denot_shx Ex' 19 0 q SHADOW_OFF ltac:(exw_ew E19) ltac:(exw_ew E25)) in P20 by (unfold SHADOW_OFF; lia);
  rewrite (exo_denot_shx Ex' 19 8 q SHADOW_OFF ltac:(exw_ew E19) ltac:(exw_ew E25)) in P22 by (unfold SHADOW_OFF; lia)
end.
cbn [sv_denot ew ewset Nat.eqb] in P23. rewrite Uq in P23. cbn [ms_regs restrict] in P20, P22, P23, KR.
assert (Q20 : getr (ms_regs ms) 20 = getr regs 20) by (rewrite P20, R20; unfold w64, shadow_addr; f_equal; f_equal; f_equal; lia).
assert (Q22 : getr (ms_regs ms) 22 = getr regs 22) by (rewrite P22, R22; reflexivity).
assert (Q23 : getr (ms_regs ms) 23 = getr regs 23) by (rewrite P23, R23; reflexivity).
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. cbn [ew ewset Nat.eqb] in P10. rewrite E19 in P10.
pose proof (exw_region_nth rsegs _ _ _ 0 _ HS eq_refl) as RQ0. cbn [ms_mem restrict] in RQ0.
pose proof (exw_field rsegs _ _ 19%nat q _ _ _ _ _ 0 8 (SOff 11 1) (p + 1) RQ0 ltac:(cbn [ew ewset Nat.eqb]; exact Uq)
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite Up; reflexivity)
  ltac:(cbn; lia) ltac:(zside)) as VQ1. rewrite Z.add_0_r in VQ1.
lazymatch type of HS with st_ok _ _ ?ssF _ => assert (HSR : ss_resv ssF = None) by (vm_compute; reflexivity) end.
(* ---- EXB at the call state ---- *)
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?md0 |} _ => set (mdF := md0) in * end.
assert (SPm : spZ (ms_regs ms) = s1).
{ unfold spZ. rewrite (KR 2%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))), R2. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (EXB1 : EXB B ARx SK Ex lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) mdF k pos).
{ apply (exv_kt B ARx SK HYP Ex lyc Sc Hpc Wc regs memc mdc k pos (ms_regs ms) (ms_mem ms) mdF k HPRE HB HJ).
  - apply (exo_kept_T1 Ex Wc memc _ 64 64); [unfold exv_sp, exv_STK; lia | lia |].
    intros a Ha Hz. apply K1; [exact Ha | intros Hq; apply Hz; right; left; exact Hq].
  - intros a Ha. apply (apresent_grows _ _ _ a G1), Ha.
  - exact HPM.
  - intros r Hr. apply KR. cbn [In] in Hr |- *. tauto. }
pose proof EXB1 as (_ & _ & _ & _ & _ & _ & _ & HLED1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  HSRC1 & HTB1 & _ & _ & _ & _).
destruct (KCHAIN Ex lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) mdF k pos (ms_regs ms) HPRE EXB1
  ltac:(rewrite (KR 2%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact R2) ltac:(rewrite (KR 8%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))); exact R8)) as (ch1 & Hch1 & _).
destruct (KRO Ex lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) mdF k pos HPRE EXB1) as (ARO & _).
assert (V8' : val_mem rsegs (mrestrict (w_H Wc) (ms_mem ms)) (q + 8) 8 (e_x0 Ex + exv_len Ex)).
{ eapply exk_val_kept; [|exact V8]. intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply K1; lia. }
(* ---- the call ---- *)
set (e1 := spZ (e_regs Ex) + e_d Ex - s1).
set (o1 := s1 - (spZ (e_regs Ex) + e_d Ex)).
set (KQ := exo_KQ Ex lyc Sc Hpc (ms_mem ms)).
eapply SRr_bind.
{ eapply (YCbqGcallW.aj_call_xW_sp (SK := SK) rsegs B (@prh_pst prh_img_B) ARx LAWS B_prog_segs_low Wc _ _ ms
    (STK_ex_value (e_n Ex) + e_d Ex) (spZ (e_regs Ex) + e_d Ex) (exv_FP Ex) (e_ly Ex) (e_S Ex) (e_Hp Ex) (e_W Ex)
    (e_mem Ex) (e_md Ex) [(1, pos)] lyc Sc Hpc mdF k 16 e1 [(q, q + 8)] o1 (getr (ms_regs ms) 1) ch1 KQ HS HSR HJ).
  - rewrite SPm. unfold o1. lia.
  - unfold o1. lia.
  - unfold o1. lia.
  - lia.
  - unfold o1. lia.
  - unfold e1. lia.
  - unfold e1. lia.
  - unfold o1, e1. lia.
  - rewrite (KR 3%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). exact R3.
  - rewrite (KR 4%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). exact R4.
  - reflexivity.
  - rewrite P1. apply ret_ok_even. rewrite unsigned_lit_small by lia. reflexivity.
  - rewrite P1. rewrite unsigned_lit_small by lia. lia.
  - replace (spZ (e_regs Ex) + e_d Ex + o1) with s1 by (unfold o1; lia).
    replace (s0Z (ms_regs ms)) with (spZ (e_regs Ex)); [exact Hch1|].
    unfold s0Z. rewrite (KR 8%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))), R8. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - intros HPRE1 HWIN1.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst _ ?pcw _ _) _) _ =>
      replace pcw with (w64 (pa_sigma AS_ex_ws)) by (vm_compute; reflexivity) end.
    refine (SRr_mono rsegs _ _ _ _ (exv_ws B ARx SK HYP fx lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) mdF ch1 q (e_x0 Ex)
      (exv_i1 Ex + 1) e1 (e_x Ex) (e_Lam Ex) (e_peak Ex) (e_cnt Ex) (e_fail Ex) (e_ran Ex) (e_most Ex) (e_own Ex) _ _ _ _ _ _ _ _ _ _ _ _ _) _).
    + split; [exact HPRE1|]. split; [exact ARO|]. split; [rewrite SPm; lia|].
      (* fpre's raZ < alloc_ceiling: the jal's return pc, a listing literal *)
      split; [unfold raZ; rewrite P1, unsigned_lit_small by lia; pose proof (@alloc_ceiling_value rc) as (ACv & _); lia | exact HFZ].
    + exact P10.
    + replace (e_x0 Ex + (exv_i1 Ex + 1)) with (p + 1) by lia. exact VQ1.
    + exact V8'.
    + exact Hq8.
    + rewrite SPm. lia.
    + rewrite SPm. unfold e1. lia.
    + exact HWIN1.
    + exact HSRC1.
    + exact HTB1.
    + rewrite <- Hlen_def. exact Hlen3.
    + rewrite <- Hlen_def. lia.
    + exact HLED1.
    + cbv beta. intros W' c' _ HF. exact HF.
  - intros a Ha. left. destruct Ha as (r & [<-|[]] & Hr). exists (q, q + 8). split; [right; left; reflexivity | exact Hr]. }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJc & HXw & HPres & HK).
unfold KQ, exo_KQ in HK. destruct HK as ((HRM2 & VQ2 & HHp2 & HS2 & HAB2 & HLED2) & HMNw).
assert (R2r : forall r, In r [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv -> getr regs2 r = getr (ms_regs ms) r).
{ intros r Hr. cbn [In] in Hr.
  repeat destruct Hr as [<-|Hr]; try contradiction;
  match goal with |- getr _ ?b = _ =>
    let z := eval vm_compute in (bv_unsigned b) in exact (HPres z ltac:(unfold acallee_saved; lia)) end. }
replace (spZ (e_regs Ex) + e_d Ex + o1 + e1) with (spZ (e_regs Ex) + e_d Ex) in HJc by (unfold o1, e1; lia).
destruct (KCALL Ex lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) mdF k pos fx [(q, q + 8)] (16 + e1) ly2 S2 Hp2 W2 regs2 mem2 md2 k1
  HPRE EXB1) as (EXB2 & KF).
{ intros a (r & [<-|[]] & Hr). exists (q, q + 8). split; [right; left; reflexivity | exact Hr]. }
{ exact HJ2. }
{ exact HJc. }
{ intros a Ha Hf. apply HXw; [unfold o1, e1; unfold exv_sp in Ha; change (exv_s1 Ex) with s1 in Ha; lia | exact Hf]. }
{ exact R2r. }
{ intros r _. reflexivity. }
{ exact HFZ. }
{ rewrite HS2. apply exv_room_refl. }
{ intros H0. exact (HMNw (HPM H0)). }
{ exact HHp2. }
{ exact HAB2. }
{ rewrite HHp2 in HLED2 |- *. exact HLED2. }
(* ---- the return site: CUT_CR ---- *)
assert (KQC : forall x, q + 8 <= x < q + 40 -> aview rsegs (w_H W2) mem2 x = aview rsegs (w_H Wc) memc x).
{ intros x Hx. rewrite HXw.
  - apply K1; lia.
  - unfold o1, e1. lia.
  - intros (r & [<-|[]] & Hr). cbn [fst snd] in Hr. lia. }
assert (KSP : forall x, s1 + 8 <= x < s1 + 160 -> aview rsegs (w_H W2) mem2 x = aview rsegs (w_H Wc) memc x).
{ intros x Hx. rewrite KF by (unfold exv_sp; change (exv_s1 Ex) with s1; lia). apply K1; lia. }
assert (Hip : e_x0 Ex + Z.of_nat (length (e_x Ex)) - Z.of_nat (length (PjGrammar.skip (skipn (Z.to_nat (exv_i1 Ex + 1)) (e_x Ex))))
  = e_x0 Ex + (exv_len Ex - Z.of_nat (length (PjGrammar.skip (skipn (S (Z.to_nat (exv_i1 Ex))) (e_x Ex)))))).
{ replace (Z.to_nat (exv_i1 Ex + 1)) with (S (Z.to_nat (exv_i1 Ex))) by lia. rewrite Hlen_def. lia. }
rewrite Hip in VQ2.
rewrite P1.
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ ?ra _ _) _) _ =>
  replace ra with (w64 (exv_pc 0x460)) by (vm_compute; reflexivity) end.
change (mkCfg (mkst regs2 (w64 (exv_pc 0x460)) mem2 (seg_rom rsegs)) md2) with (cfg_at rsegs (exv_pc 0x460) regs2 mem2 md2).
apply (HR Ex ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) pos c vv dlc Hn HPRE EXB2 Hi1 Hnth Hcc Hd1).
- split; [exact VQ2|].
  split; [apply (exo_val_kept2 (w_H Wc) (w_H W2) memc mem2 _ 8 _); [intros x Hx; apply KQC; cbn in Hx; lia | exact V8]|].
  split; [apply (exo_val_kept2 (w_H Wc) (w_H W2) memc mem2 _ 4 _); [intros x Hx; apply KQC; cbn in Hx; lia | exact V16]|].
  split; [apply (exo_val_kept2 (w_H Wc) (w_H W2) memc mem2 _ 8 _); [intros x Hx; apply KQC; cbn in Hx; lia | exact V24]|].
  apply (exo_val_kept2 (w_H Wc) (w_H W2) memc mem2 _ 4 _); [intros x Hx; apply KQC; cbn in Hx; lia | exact V32].
- exact Hdlc.
- exact Hdif.
- transitivity (getr (ms_regs ms) 27%bv); [exact (HPres 27 ltac:(unfold acallee_saved; lia))|]. rewrite (KR 27%bv ltac:(cbn [In]; repeat (first [left; reflexivity | right]))). exact R27.
- transitivity (getr (ms_regs ms) 20%bv); [exact (HPres 20 ltac:(unfold acallee_saved; lia))|]. rewrite Q20. exact R20.
- transitivity (getr (ms_regs ms) 22%bv); [exact (HPres 22 ltac:(unfold acallee_saved; lia))|]. rewrite Q22. exact R22.
- transitivity (getr (ms_regs ms) 23%bv); [exact (HPres 23 ltac:(unfold acallee_saved; lia))|]. rewrite Q23. exact R23.
- apply (exo_val_kept2 (w_H Wc) (w_H W2) memc mem2 _ 8 _); [intros x Hx; apply KSP; cbn in Hx; lia | exact S64].
- apply (exo_val_kept2 (w_H Wc) (w_H W2) memc mem2 _ 8 _); [intros x Hx; apply KSP; cbn in Hx; lia | exact S96].
- apply (exo_val_kept2 (w_H Wc) (w_H W2) memc mem2 _ 8 _); [intros x Hx; apply KSP; cbn in Hx; lia | exact S104].
- pose proof (proj1 HJ) as HARm. cbv beta in HARm. pose proof HJc as (_ & Hly1 & _).
  destruct (alx_layout rsegs B ARx LAWS lyc Sc Hpc Wc (ms_mem ms) mdF ly2 HARm Hly1) as (_ & Hfr & _).
  rewrite (Hfr 1 pos).
  apply (exo_val_kept2 (w_H Wc) (w_H W2) memc mem2 _ 8 _); [intros x Hx; apply KSP; cbn in Hx; lia | exact S120].
- apply (exo_val_kept2 (w_H Wc) (w_H W2) memc mem2 _ 8 _); [intros x Hx; apply KSP; cbn in Hx; lia | exact S144].
- apply (exo_val_kept2 (w_H Wc) (w_H W2) memc mem2 _ 8 _); [intros x Hx; apply KSP; cbn in Hx; lia | exact S152].
Qed.
End m.
