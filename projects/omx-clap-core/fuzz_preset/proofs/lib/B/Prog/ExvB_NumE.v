(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Does not rest on tex_word_specX; memnorm only as EXN_keepM(_cur)'s keep: runs' frames, m-form call keeps (kit 4f18c75d4900). *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (asan-ubsan, rebuilt pin f8f98a95bc52, unstripped twin 3b5e1a099b53),
   ex_value's NUMBER SEGMENT, sub-piece Ec (lib/B/Prog/ExvB_NumCut.v EXN_Ec): the cut CC (exv_pc 0x910, B 0x83e3c) to
   the cut CD (exv_pc 0x9a8, B 0x83ed4), where in->differs is decided. Proves no function (kind: segment lemma).
   The states, seats, facts and the arms v = 0 (exe_arm_0) and after __wrap_bcmp (exe_arm_r2) are in ExvB_NumE_a.v.
   Code (neutral listing, the internal file ex_value.fuzz_preset.asan-ubsan.s, a Theorem Labs lane's listing of the B' pin, lines 582-619 and
   the slow paths 726, 785-791, 849-851; never a raw disassembly):
     0x83e3c ld a2,152(s1) / beqz a2 -> CD                          v = 0: exe_arm_0 (in->differs kept)
     0x83e44 andi a2,a2,7 / bnez a2 -> 0x8407c unimp                UBSan alignment check of v
     0x83e4c ld a0,152(s1) / srli / add s9 / lb / bnez -> 0x84168   ASan, 4-byte load of v->type
     0x83e60 lw a2,0(a0) / li a1,3 / bne a2,a1 -> 0x83eb8           v->type <> 3 (JNum): differs
     0x83e6c addi a0,a0,16 / srli / add s9 / lbu / bnez -> 0x84268  ASan, 8-byte load of v->str
     0x83e80 lbu a1,0(s11) / bnez a1 -> 0x8426c                     ASan, 8-byte load of in->scratch (s11: q + 24's)
     0x83e88 ld a0,0(a0) / ld a1,0(s4) / jal __wrap_strcmp          YGcallMxmn.aj_strcmp_at_xrom
     0x83e94 ld a1,152(s1) / ld a3,144(s1) / bnez a0 -> 0x83eb8     the texts differ: differs
     0x83ea0 addi a0,a1,8 / li a2,8 / ld a1,136(s1) / jal __wrap_bcmp   YGcallMxmn.aj_bcmp_at_xm (v->num, f + 64, 8)
     0x83eb0 ld a3,144(s1) / beqz a0 -> CD                          exe_arm_r2 (ExvB_NumE_a.v)
     0x83eb8 addi a0,s3,32 / srli / add s9 / lb / bnez -> 0x84174   ASan, 4-byte store to in->differs
     0x83ecc li a1,1 / sw a1,0(a0)                                  in->differs := 1, falls into CD
   Every check is taken inside the table runner's symbolic run (exw_run / exw_run_to / exw_branch, ExvB_Num_eng.v) and
   shown NOT taken from the run's facts: the UBSan trap guard 0x83e48 (-> unimp 0x8407c) from atom 32's alignment
   fact (v mod 8 = 0, exe_vfacts from pj_nodeR) in exe_arm_v; the ASan report sites 0x84170 (errpath_load4, guard
   0x83e5c; its slow path 0x84168 returns to 0x83e60 only for a partial granule) and 0x84268 (errpath_load8, guard
   0x83e7c) from v's shadow entry [v, v + 56) (exe_shv, prhex_tree's range_addressable), and 0x84270 (errpath_load8,
   guard 0x83e84) from q's entry [q, q + 40) (exe_shq, EXB's range_addressable), all three in exe_arm_v; 0x84180
   (errpath_store4, guard 0x83ec8, slow path 0x84174) from q's entry in exe_arm_v (v->type <> 3), exe_arm_r1
   (strcmp <> 0) and ExvB_NumE_a.v's exe_arm_r2 (bcmp <> 0). The strcmp call's operands are v->str (a Lam block:
   exe_hdr, exv_sh_lam) and in->scratch (prhex_inblk), both by exe_blk_op; its read-only premise is KIT_RODATA's
   first half (exv_kit_rodata); the bcmp call's operands are v's num field and the frame's num slot f + 64.
   Old-pin kit 4f18c75d4900 (rebind base a9d3e245c2b): EXN_keepM / EXN_keepM_cur and ExvB_Open_kt.exv_kt ask the
   memnorm keep from the cut's memory; each engine run gives it from its frame on the whole overlay (exe_mn_of /
   exe_mn_run, ExvB_NumE_a.v: the run writes only in->differs, on the real stack, where no image segment lies), each
   call from its m-form rule's last conjunct, and exv_kt's from EXB's exv_rm. Image A's
   proved number arm (exv/s8a/S8aNum*.v) was read for the proof shape only; nothing of it is Required or cited.
   Numerals: 0x910, 0x9a8 (DERIVED: cut offsets, through EXN_CC / EXN_CD); 3 (WORD: JNum's tag, the listing's
   li a1,3); 1, 0 (WORD: in->differs' values, x0); 1, 2, 3, 4, 9, 10, 11, 12, 13, 19, 24, 25 (WORD: register numbers);
   32, 33, 34, 35, 36 (LENGTH: the runner's extra atoms after the 32 registers, and env_agree's register count; 32 is
   also in->differs' offset in the cursor); 5 (LENGTH: the register index width); 8, 16, 40, 56, 64, 128, 160
   (LENGTH: bcmp's length and v's num offset, the frame's shadow bytes, the cursor's and the node's sizes, the frame's
   num slot, the frame's bytes, the end of the s1 spill slots); 4, 6 (LENGTH / WORD: in->differs' width, the largest
   tag); 3 * 2 ^ 20 (LENGTH: EXV_PRE's text bound); 4096, 2 ^ 44 = 17592186044416, 2 ^ 32, 2 ^ 47, 2 ^ 63, 2 ^ 64
   (LENGTH: the low page, the shadow's size, the length, address-space and word bounds). No ADDRESS: every pc is
   exv_pc of a DERIVED offset or a callee's B_prog_sigma; the hex addresses above name listing lines only. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMx YGcallMxmn YAkMemnorm YP08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1ImgCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require SoftFloat FloatScan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require S1ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import
ExvB_Stmt ExvB_Num_eng ExvB_Open_sh ExvB_Open_kt ExvB_Loop_kit ExvB_Loop_kitQ
ExvB_NumPure ExvB_NumCut ExvB_NumE_a.
Import ListNotations.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Section p. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variable E : exv_e.
Variable pos : Z.
Hypothesis HYP : EXV_HYP B ARx SK.
Hypothesis EF : EXN_F B ARx SK E pos.
Hypothesis MK : EXN_keepM B ARx SK E pos.
Hypothesis MC : EXN_keepM_cur B ARx SK E pos.
Hypothesis KS : EXN_keep_spill E.
Let LAWS := eh_laws B ARx SK HYP.

(* ---- after __wrap_strcmp: the text of v->str against in->scratch ---- *)
Lemma exe_arm_r1 : forall (fxc : YK11.FPState) lyc Sc Hpc Wc regs memc mdc k c j bits
    (regs2 : bvmap 5 word) mem2 md2 k2 (rv : word) txt2 bits2,
  EXV_PRE B ARx E -> EXN_CC_pre B ARx SK E pos fxc lyc Sc Hpc Wc regs memc mdc k c j bits -> e_v E <> 0 ->
  e_t E = PjTree.JNum txt2 bits2 ->
  PRH_Reader.rd_u64 rsegs (rdW Wc memc) (e_v E + 8) bits2 ->
  ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E)
    (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] lyc Sc Hpc Wc mem2 md2 k2 ->
  (forall z, 0 <= z < 2 ^ 64 -> ~ (exv_s1 E - 2 * ESTACK <= z < exv_s1 E) ->
     ~ (e_q E + 32 <= z < e_q E + 36) -> aview rsegs (w_H Wc) mem2 z = aview rsegs (w_H Wc) memc z) ->
  val_mem rsegs (rdW Wc mem2) (e_q E + 32) 4 (e_dl E) ->
  (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) mem2 a) ->
  (YAkMemnorm.memnorm rsegs memc -> YAkMemnorm.memnorm rsegs mem2) ->
  (forall r, In r exe_kept -> YK11.getr regs2 r = YK11.getr regs r) ->
  YK11.getr regs2 10 = rv -> (rv = w64 0 <-> txt2 = exn_sub (e_x E) (EXN_i1 E) j) ->
  SRr rsegs Wc (cfg_at (fx := fxc) rsegs EXE_R1 regs2 mem2 md2) (EXV_POST B ARx SK E).
Proof.
intros fxc lyc Sc Hpc Wc regs memc mdc k c j bits regs2 mem2 md2 k2 rv txt2 bits2
  HPRE HCC Hvn Het Hb2 HJ2 HK2 Cq32m HG2 HMN2 HR2 Hrv Hcmp.
pose proof HCC as HCC'. unfold EXN_CC_pre in HCC'. cbv zeta in HCC'.
destruct HCC' as (HBASE & HDISP & HCUR & HFSH & Hij & HN & Hgarr & Cnum & R22 & R13c & R21 & R20 & R27 & C136).
destruct HBASE as (HB & S144 & S152).
pose proof HB as HB0. unfold EXB in HB0. cbv zeta in HB0.
destruct HB0 as (HJ & HWIN & HFRG & HFZ & HHP & HAB & HRM & HLED & HCNT &
  R2 & R8 & R9 & R18 & R24 & R25 & R26 & R19 & R3 & R4 & HSAV & H176 & HFL & HSRC & HTB & HWD & HSB & HQRA & HTREE).
destruct (exe_geom B ARx SK HYP fxc E lyc Sc Hpc Wc regs memc mdc k pos HPRE HB)
  as (HAR & HIN & HSTK & Hd0 & Hd16 & Hsplo & Hspd & Hhi47 & Hcsp & Hlosp & Hclo & HS1 & HS132 & Hsp16 &
      Hspq & Hqd & Hq8 & Hf1 & Hf2 & Hf32 & Hpres).
destruct (exe_vfacts B ARx SK HYP fxc E lyc Sc Hpc Wc regs memc mdc k pos HPRE HB Hvn)
  as (Hnd & Hhome & HVRA & HVHULL & Hv4096 & Hv47 & Hv8 & HFOOT).
destruct (exe_v_rng B ARx SK HYP fxc E lyc Sc Hpc Wc regs memc mdc k pos HPRE HB Hvn)
  as (_ & _ & HVBAND & HVDJ).
pose proof (exe_vamem B ARx SK E pos HYP EF MK MC KS fxc lyc Sc Hpc Wc regs memc mdc k HPRE HB Hvn) as HVAM.
pose proof asan_consts as (AC & _ & _ & _ & _).
pose proof (exe_mod8 _ HS132) as Hs18. pose proof (exe_mod16 _ HS132) as Hs116.
assert (HESTK : ESTACK = 4096) by reflexivity.
assert (Hdl01 : e_dl E = 0 \/ e_dl E = 1).
{ pose proof HPRE as HP2. unfold EXV_PRE in HP2. cbv zeta in HP2.
  repeat lazymatch type of HP2 with
  | (e_dl E = 0 \/ e_dl E = 1) /\ _ => destruct HP2 as [HP2 _]
  | _ /\ _ => destruct HP2 as [_ HP2]
  end. exact HP2. }
assert (Hbits : 0 <= bits < 2 ^ 64).
{ destruct (exe_N_txt _ _ _ _ HN) as (_ & Hbt). rewrite Hbt. apply exe_jr_strtod_bits. }
destruct Hb2 as (Hb2r & Vb2).
destruct HCUR as (Cq0 & Cq8 & Cq16 & Cq24 & Cq32).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ & _).
assert (MV : forall a (n : nat) v, exv_s1 E <= a -> a + Z.of_nat n <= e_q E ->
  val_mem rsegs (rdW Wc memc) a n v -> val_mem rsegs (rdW Wc mem2) a n v).
{ intros a n v Ha Han Hv. apply (exe_val_move rsegs (w_H Wc) memc mem2 a n v); [|exact Hv].
  intros i Hi. apply HK2; lia. }
assert (G9 : YK11.getr regs2 9 = Z_to_bv 64 (exv_s1 E))
  by (rewrite (HR2 9%bv ltac:(cbv [exe_kept]; cbn [In]; repeat (first [left; reflexivity | right]))); exact R9).
assert (G19 : YK11.getr regs2 19 = Z_to_bv 64 (e_q E))
  by (rewrite (HR2 19%bv ltac:(cbv [exe_kept]; cbn [In]; repeat (first [left; reflexivity | right]))); exact R19).
assert (G24 : YK11.getr regs2 24 = Z_to_bv 64 (frame_addr lyc 1 pos))
  by (rewrite (HR2 24%bv ltac:(cbv [exe_kept]; cbn [In]; repeat (first [left; reflexivity | right]))); exact R24).
assert (G25 : YK11.getr regs2 25 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (HR2 25%bv ltac:(cbv [exe_kept]; cbn [In]; repeat (first [left; reflexivity | right]))); exact R25).
assert (G2s : YK11.getr regs2 2 = Z_to_bv 64 (exv_s1 E))
  by (rewrite (HR2 2%bv ltac:(cbv [exe_kept]; cbn [In]; repeat (first [left; reflexivity | right]))); exact R2).
assert (G3 : YK11.getr regs2 3 = w64 (as_gp B))
  by (rewrite (HR2 3%bv ltac:(cbv [exe_kept]; cbn [In]; repeat (first [left; reflexivity | right]))); exact R3).
assert (G4 : YK11.getr regs2 4 = w64 (as_tp B))
  by (rewrite (HR2 4%bv ltac:(cbv [exe_kept]; cbn [In]; repeat (first [left; reflexivity | right]))); exact R4).
assert (HS : st_ok rsegs (Ereg regs2 [Z_to_bv 64 (e_v E); Z_to_bv 64 (e_dl E)]) (ss_exe_r EXE_R1)
  (restrict (w_H Wc) (@YK11.mkst fxc regs2 (Z_to_bv 64 EXE_R1) mem2 (YK11.seg_rom rsegs)))).
{ apply (exe_st_r fxc Wc regs2 mem2 EXE_R1 (exv_s1 E) (e_q E) (frame_addr lyc 1 pos) (e_v E) (e_dl E)
           G9 G19 G24 G25); try lia.
  - apply MV; [lia | lia | exact C136].
  - apply MV; [lia | lia | exact S144].
  - apply MV; [lia | lia | exact S152].
  - exact Cq32m.
  - intros o Ho. apply (apresent_writable rsegs). apply HpresJ. lia. }
set (E2 := Ereg regs2 [Z_to_bv 64 (e_v E); Z_to_bv 64 (e_dl E)]) in HS.
assert (E10 : ew E2 10 = rv) by (unfold E2; rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl); exact Hrv).
assert (E19 : ew E2 19 = Z_to_bv 64 (e_q E)) by (unfold E2; exact (exe_ew regs2 _ 19 19%bv _ eq_refl G19)).
assert (E24 : ew E2 24 = Z_to_bv 64 (frame_addr lyc 1 pos))
  by (unfold E2; exact (exe_ew regs2 _ 24 24%bv _ eq_refl G24)).
assert (E25 : ew E2 25 = Z_to_bv 64 SHADOW_OFF) by (unfold E2; exact (exe_ew regs2 _ 25 25%bv _ eq_refl G25)).
assert (E32 : ew E2 32 = Z_to_bv 64 (e_v E)) by (unfold E2; exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E2 33 = Z_to_bv 64 (e_dl E)) by (unfold E2; exact (ew_Ereg_extra regs2 _ 1)).
assert (U19 : bv_unsigned (ew E2 19) = e_q E) by (apply exe_U; [exact E19 | lia]).
assert (U25 : bv_unsigned (ew E2 25) = SHADOW_OFF) by (apply exe_U; [exact E25 | unfold SHADOW_OFF; lia]).
assert (AG2 : env_agree 32 (Ereg regs2 [Z_to_bv 64 (e_v E); Z_to_bv 64 (e_dl E)]) E2)
  by (unfold E2; apply env_agree_refl).
assert (SHOK : sh_ok rsegs EXE_SB exe_SHr E2 (rdW Wc mem2)).
{ unfold sh_ok, exe_SHr. constructor; [|constructor].
  apply (exe_shq (w_H Wc) mem2 E2 (e_q E) U19 U25); [lia | lia |].
  apply (exv_ra_keep (aview rsegs (w_H Wc) memc)); [| lia | lia | exact HQRA].
  intros s0 Hs0. apply HK2; lia. }
clearbody E2.
unfold cfg_at. change (w64 EXE_R1) with (Z_to_bv 64 EXE_R1).
pose (RUN := SRr_run_tok_AJx (SK := SK) (fx := fxc) rsegs B prh_pst ARx LAWS B_prog_segs_low
  B_prog_tbl B_prog_tbl_ok B_prog_wx).
pose (RUNTO := SRr_run_to_tok_AJx (SK := SK) (fx := fxc) rsegs B prh_pst ARx LAWS B_prog_segs_low
  B_prog_tbl B_prog_tbl_ok B_prog_wx).
clear HJ.
exw_run RUN HS HJ2 SHOK.
{ exe_awr U19. }
exw_kept_of HFr (fun a => e_q E + 32 <= a < e_q E + 36) ltac:(fun h => rewrite ?U19 in h).
exe_mn_of HF (fun a => e_q E + 32 <= a < e_q E + 36) ltac:(fun h => rewrite ?U19 in h)
  ltac:(intros amn Hamn; cbv beta in Hamn; lia).
rename KEPT into K1. rename HG into G1. rename MNK into MN1. clear HF HFr.
exw_branch HS SHOK.
- (* strcmp <> 0: in->differs := 1 *)
  pose proof (exe_br_ne_t E2 10 rv E10 Hc) as Hrv0.
  assert (Hne : e_t E <> PjTree.JNum (exn_sub (e_x E) (EXN_i1 E) j) bits).
  { rewrite Het. intros Heq. injection Heq as Ht _. exact (Hrv0 (proj2 Hcmp Ht)). }
  exw_run_to RUNTO HS HJ2 SHOK EXE_CD.
  { exe_awr U19. }
  exw_kept_of HFr (fun a => e_q E + 32 <= a < e_q E + 36) ltac:(fun h => rewrite ?U19 in h).
  exe_mn_of HF (fun a => e_q E + 32 <= a < e_q E + 36) ltac:(fun h => rewrite ?U19 in h)
    ltac:(intros amn Hamn; cbv beta in Hamn; lia).
  rename KEPT into K2. rename HG into G2. rename MNK into MN2. clear HF HFr.
  lazymatch type of HS with
  | st_ok _ _ _ (restrict _ ?mx) =>
    assert (RK : forall r, In r exe_kept -> YK11.getr (ms_regs mx) r = YK11.getr regs2 r)
      by (intros r Hr; exact (regs_kept_of_st_ok rsegs _ _ _ regs2 _ exe_kept HS AG2
            ltac:(vm_compute; reflexivity) r Hr))
  end.
  pose proof (st_ok_restrict_reg rsegs (w_H Wc) _ _ _ 13%bv HS) as R13.
  lazymatch type of R13 with _ = sv_denot ?Ex (sr_get ?l _) =>
    change (sr_get l 13%bv) with (exe_shx 19 0) in R13 end.
  rewrite (exe_den_shx E2 19 0 (e_q E) E19 E25) in R13 by lia. rewrite Z.add_0_r in R13.
  cbn [ms_regs restrict] in R13.
  pose proof (exw_region_nth rsegs _ _ _ 1%nat _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
  pose proof (exw_field rsegs _ _ 19%nat (e_q E) _ _ _ _ _ 32 4 (SLit 1) 1 RQ U19
    ltac:(left; reflexivity) ltac:(apply exe_den_lit; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as VQ.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst ?f ?rg ?pc ?mm ?rom) ?md) _ =>
    replace pc with (w64 (exv_pc EXN_CD)) by (vm_compute; reflexivity) end.
  eapply (exe_close B ARx SK E pos HYP EF MK MC KS fxc lyc Sc Hpc Wc regs memc mdc k c j bits _ _ _ _ 1 HPRE HCC).
  + exact HJ2.
  + intros z Hz Hw Hq. rewrite (K2 z Hz Hq), (K1 z Hz Hq). exact (HK2 z Hz Hw Hq).
  + intros a Ha. apply (apresent_grows (w_H Wc) _ _ a G2), (apresent_grows (w_H Wc) _ _ a G1), HG2, Ha.
  + intros Hm. exact (MN2 (MN1 (HMN2 Hm))).
  + intros r Hr. rewrite (RK r Hr). exact (HR2 r Hr).
  + exact R13.
  + exact VQ.
  + right; reflexivity.
  + split; [intros _; right; split; [exact Hvn | exact Hne] | intros _; reflexivity].
- (* strcmp = 0: the texts agree; __wrap_bcmp (v + 8, f + 64, 8) *)
  pose proof (exe_br_ne_f E2 10 rv E10 Hc) as Hrv0.
  pose proof (proj1 Hcmp Hrv0) as Htxt.
  exw_run_to RUNTO HS HJ2 SHOK EXE_BCMP.
  { exe_awr U19. }
  exw_kept_of HFr (fun a => e_q E + 32 <= a < e_q E + 36) ltac:(fun h => rewrite ?U19 in h).
  exe_mn_of HF (fun a => e_q E + 32 <= a < e_q E + 36) ltac:(fun h => rewrite ?U19 in h)
    ltac:(intros amn Hamn; cbv beta in Hamn; lia).
  rename KEPT into K2. rename HG into G2. rename MNK into MN2. clear HF HFr.
  lazymatch type of HS with
  | st_ok _ _ _ (restrict _ ?mx) =>
    assert (KC : forall z, 0 <= z < 2 ^ 64 -> ~ (exv_s1 E - 2 * ESTACK <= z < exv_s1 E) ->
       ~ (e_q E + 32 <= z < e_q E + 36) ->
       aview rsegs (w_H Wc) (ms_mem mx) z = aview rsegs (w_H Wc) memc z)
      by (intros z Hz Hw Hq; rewrite (K2 z Hz Hq), (K1 z Hz Hq); exact (HK2 z Hz Hw Hq));
    assert (RK1 : forall r, In r exe_kept -> YK11.getr (ms_regs mx) r = YK11.getr regs2 r)
      by (intros r Hr; exact (regs_kept_of_st_ok rsegs _ _ _ regs2 _ exe_kept HS AG2
            ltac:(vm_compute; reflexivity) r Hr));
    assert (GC : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) (ms_mem mx) a)
      by (intros a Ha; apply (apresent_grows (w_H Wc) _ _ a G2), (apresent_grows (w_H Wc) _ _ a G1), HG2, Ha);
    assert (Vb2c : val_mem rsegs (rdW Wc (ms_mem mx)) (e_v E + 8) 8 bits2)
      by (apply (exe_val_move rsegs (w_H Wc) memc (ms_mem mx) (e_v E + 8) 8 bits2); [|exact Vb2];
          intros i Hi; apply KC;
            [lia | intros Hcon; destruct (HVDJ (e_v E + 8 + i) ltac:(lia)) as (Hst & _); apply Hst; lia
             | intros Hcon; destruct (HVDJ (e_v E + 8 + i) ltac:(lia)) as (_ & Hqq); apply Hqq; lia]);
    assert (Vfc : val_mem rsegs (rdW Wc (ms_mem mx)) (frame_addr lyc 1 pos + 64) 8 bits)
      by (apply (exe_val_move rsegs (w_H Wc) memc (ms_mem mx) (frame_addr lyc 1 pos + 64) 8 bits); [|exact Cnum];
          intros i Hi; apply KC; lia);
    assert (Cq32c : val_mem rsegs (rdW Wc (ms_mem mx)) (e_q E + 32) 4 (e_dl E))
      by (pose proof (exw_region_nth rsegs _ _ _ 1%nat _ HS eq_refl) as RQ0; cbn [ms_mem restrict] in RQ0;
          exact (exw_field rsegs _ _ 19%nat (e_q E) _ _ _ _ _ 32 4 (SOff 33 0) (e_dl E) RQ0 U19
            ltac:(left; reflexivity)
            ltac:(rewrite (exe_den_off E2 33 (e_dl E) 0 E33) by lia; rewrite Z.add_0_r; reflexivity)
            ltac:(cbn; lia) ltac:(cbn; lia)))
  end.
  pose proof (st_ok_restrict_reg rsegs (w_H Wc) _ _ _ 10%bv HS) as Pa0.
  lazymatch type of Pa0 with _ = sv_denot ?Ex (sr_get ?l _) =>
    change (sr_get l 10%bv) with (SOff 32 8) in Pa0 end.
  rewrite (exe_den_off E2 32 (e_v E) 8 E32) in Pa0 by lia. cbn [ms_regs restrict] in Pa0.
  pose proof (st_ok_restrict_reg rsegs (w_H Wc) _ _ _ 11%bv HS) as Pa1.
  lazymatch type of Pa1 with _ = sv_denot ?Ex (sr_get ?l _) =>
    change (sr_get l 11%bv) with (SOff 24 64) in Pa1 end.
  rewrite (exe_den_off E2 24 (frame_addr lyc 1 pos) 64 E24) in Pa1 by lia. cbn [ms_regs restrict] in Pa1.
  pose proof (st_ok_restrict_reg rsegs (w_H Wc) _ _ _ 12%bv HS) as Pa2.
  lazymatch type of Pa2 with _ = sv_denot ?Ex (sr_get ?l _) =>
    change (sr_get l 12%bv) with (SLit 8) in Pa2 end.
  rewrite (exe_den_lit E2 8 ltac:(lia)) in Pa2. cbn [ms_regs restrict] in Pa2.
  pose proof (st_ok_restrict_reg rsegs (w_H Wc) _ _ _ 1%bv HS) as Pra.
  lazymatch type of Pra with _ = sv_denot ?Ex (sr_get ?l _) =>
    change (sr_get l 1%bv) with (SLit EXE_R2) in Pra end.
  rewrite (exe_den_lit E2 EXE_R2 ltac:(vm_compute; split; [discriminate | reflexivity])) in Pra. cbn [ms_regs restrict] in Pra.
  lazymatch type of HS with
  | st_ok _ _ _ (restrict _ ?mx) =>
    assert (Usp : spZ (ms_regs mx) = exv_s1 E)
      by (unfold spZ; rewrite (RK1 2%bv ltac:(cbv [exe_kept]; cbn [In]; repeat (first [left; reflexivity | right])));
          rewrite G2s; apply unsigned_lit_small; lia)
  end.
  pmkst HS.
  eapply SRr_bind.
  { eapply (YGcallMxmn.aj_bcmp_at_xm (fx := fxc) (SK := SK) rsegs B prh_pst ARx LAWS B_prog_segs_low
      EXE_BCMP (eh_bcmp B ARx SK HYP fxc) Wc _ _
      (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E) (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E)
      [(1, pos)] lyc Sc Hpc _ k2 (e_v E + 8) (frame_addr lyc 1 pos + 64) 8
      (exv_s1 E - (exv_sp E + e_d E)) _ HJ2 Pa0 Pa1 Pa2).
    all: try (rewrite ?Usp; lia).
    - rewrite (RK1 3%bv ltac:(cbv [exe_kept]; cbn [In]; repeat (first [left; reflexivity | right]))). exact G3.
    - rewrite (RK1 4%bv ltac:(cbv [exe_kept]; cbn [In]; repeat (first [left; reflexivity | right]))). exact G4.
    - reflexivity.
    - rewrite Pra. vm_compute. reflexivity.
    - intros a Ha. split.
      + replace a with (e_v E + 8 + Z.of_nat (Z.to_nat (a - (e_v E + 8)))) by lia.
        apply (exe_val_aview rsegs (w_H Wc) _ (e_v E + 8) 8 bits2 _ Vb2c). lia.
      + destruct (HVDJ a ltac:(lia)) as (Hst & _). rewrite Usp. intros Hcon. apply Hst. lia.
    - intros a Ha. split.
      + replace a with (frame_addr lyc 1 pos + 64 + Z.of_nat (Z.to_nat (a - (frame_addr lyc 1 pos + 64)))) by lia.
        apply (exe_val_aview rsegs (w_H Wc) _ (frame_addr lyc 1 pos + 64) 8 bits _ Vfc). lia.
      + rewrite Usp. lia.
    - intros a Ha. destruct (HVDJ a ltac:(lia)) as (Hst & _). intros Hcon. apply Hst. lia.
    - exact HVAM.
    - apply exe_in_app_amem.
      destruct (alx_frames rsegs B ARx LAWS lyc Sc Hpc Wc _ _ 1 pos (proj1 HJ2) HIN) as (_ & Happ & _ & _).
      apply (in_app_sub _ _ _ _ Happ); change (fs_frame_bytes 1) with 128; lia.
    - apply (exv_ra_keep (aview rsegs (w_H Wc) memc)); [| lia | lia |].
      + intros s0 Hs0. apply KC; [lia | lia | lia].
      + apply (range_addressable_sub _ _ (e_v E) 56); [exact HVRA | lia | lia].
    - intros _. apply (exv_hull_keep (aview rsegs (w_H Wc) memc)); [| lia | lia |].
      + intros s0 Hs0. apply KC; [lia | lia | lia].
      + apply (exv_hull_sub _ (e_v E) 56); [exact HVHULL | lia | lia].
    - intros x0 Hx0. exists 0. split; [|left; reflexivity].
      replace (shadow_of_addr SHADOW_OFF x0) with (shadow_addr (frame_addr lyc 1 pos) + 8)
        by (unfold shadow_of_addr, shadow_addr; lia).
      rewrite (KC (shadow_addr (frame_addr lyc 1 pos) + 8)) by (unfold shadow_addr, SHADOW_OFF; lia).
      exact (proj2 HFSH).
    - intros _ s0 Hs0. unfold shadow_addr in Hs0.
      rewrite (KC s0) by (unfold SHADOW_OFF in *; lia).
      apply (exe_apresent_aview rsegs (w_H Wc)).
      destruct (alx_frames rsegs B ARx LAWS lyc Sc Hpc Wc memc mdc 1 pos HAR HIN) as (_ & _ & _ & Hfsh).
      replace s0 with (shadow_addr (frame_addr lyc 1 pos) + (s0 - shadow_addr (frame_addr lyc 1 pos))) by lia.
      apply (proj1 (Hfsh (s0 - shadow_addr (frame_addr lyc 1 pos))
        ltac:(change (fs_frame_bytes 1 / 8) with 16; unfold shadow_addr, SHADOW_OFF in *; lia))). }
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & rv2 & -> & HJ3 & HP3 & Hres3 & Hcmp2 & Hfr3 & Hpres3 & Hmn3).
  rewrite Pra.
  lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst ?f ?rg ?pc ?mm ?rom) ?md) _ =>
    replace pc with (w64 EXE_R2) by (vm_compute; reflexivity) end.
  lazymatch type of KC with
  | forall _, _ -> _ -> _ -> aview _ _ ?mx _ = _ =>
    apply (exe_arm_r2 B ARx SK E pos HYP EF MK MC KS fxc lyc Sc Hpc Wc regs memc mdc k c j bits regs3 mem3 md3 _ rv2 HPRE HCC Hvn HJ3);
    [ intros z Hz Hw Hq; rewrite (Hfr3 z Hz ltac:(lia)); exact (KC z Hz Hw Hq)
    | apply (exe_val_move rsegs (w_H Wc) mx mem3 (e_q E + 32) 4 (e_dl E));
        [intros i Hi; apply Hfr3; lia | exact Cq32c]
    | intros a Ha; apply Hpres3; apply GC; exact Ha
    | intros Hm; exact (Hmn3 (MN2 (MN1 (HMN2 Hm))))
    | intros r Hr; rewrite (exe_kept_of_pres _ _ HP3 r Hr); rewrite (RK1 r Hr); exact (HR2 r Hr)
    | exact Hres3
    | rewrite Hcmp2;
      rewrite (exe_bytes_eq8 rsegs (w_H Wc) mx (e_v E + 8) (frame_addr lyc 1 pos + 64) bits2 bits
                 Hb2r Hbits Vb2c Vfc);
      rewrite Het, Htxt; split; [intros ->; reflexivity | intros Heq; injection Heq as Hb; exact Hb] ]
  end.
Qed.

(* ---- v <> 0 at CC: the UBSan alignment check, v->type, and the two calls ---- *)
Lemma exe_arm_v : forall (fxc : YK11.FPState) lyc Sc Hpc Wc regs memc mdc k c j bits,
  EXV_PRE B ARx E -> EXN_CC_pre B ARx SK E pos fxc lyc Sc Hpc Wc regs memc mdc k c j bits -> e_v E <> 0 ->
  SRr rsegs Wc (cfg_at (fx := fxc) rsegs EXE_CC regs memc mdc) (EXV_POST B ARx SK E).
Proof.
intros fxc lyc Sc Hpc Wc regs memc mdc k c j bits HPRE HCC Hvn.
pose proof HCC as HCC'. unfold EXN_CC_pre in HCC'. cbv zeta in HCC'.
destruct HCC' as (HBASE & HDISP & HCUR & HFSH & Hij & HN & Hgarr & Cnum & R22 & R13c & R21 & R20 & R27 & C136).
destruct HBASE as (HB & S144 & S152).
pose proof HB as HB0. unfold EXB in HB0. cbv zeta in HB0.
destruct HB0 as (HJ & HWIN & HFRG & HFZ & HHP & HAB & HRM & HLED & HCNT &
  R2 & R8 & R9 & R18 & R24 & R25 & R26 & R19 & R3 & R4 & HSAV & H176 & HFL & HSRC & HTB & HWD & HSB & HQRA & HTREE).
destruct (exe_geom B ARx SK HYP fxc E lyc Sc Hpc Wc regs memc mdc k pos HPRE HB)
  as (HAR & HIN & HSTK & Hd0 & Hd16 & Hsplo & Hspd & Hhi47 & Hcsp & Hlosp & Hclo & HS1 & HS132 & Hsp16 &
      Hspq & Hqd & Hq8 & Hf1 & Hf2 & Hf32 & Hpres).
destruct (exe_vfacts B ARx SK HYP fxc E lyc Sc Hpc Wc regs memc mdc k pos HPRE HB Hvn)
  as (Hnd & Hhome & HVRA & HVHULL & Hv4096 & Hv47 & Hv8 & HFOOT).
destruct (exe_v_rng B ARx SK HYP fxc E lyc Sc Hpc Wc regs memc mdc k pos HPRE HB Hvn)
  as (_ & _ & HVBAND & HVDJ).
destruct (exe_hdr _ _ _ _ _ Hnd) as (_ & str & Htag & Hstr & Hnum3).
pose proof asan_consts as (AC & _ & _ & _ & _).
pose proof (@cf_head_nonneg cp) as CH0.
pose proof (exe_mod8 _ HS132) as Hs18. pose proof (exe_mod16 _ HS132) as Hs116.
assert (HESTK : ESTACK = 4096) by reflexivity.
assert (Hdl01 : e_dl E = 0 \/ e_dl E = 1).
{ pose proof HPRE as HP2. unfold EXV_PRE in HP2. cbv zeta in HP2.
  repeat lazymatch type of HP2 with
  | (e_dl E = 0 \/ e_dl E = 1) /\ _ => destruct HP2 as [HP2 _]
  | _ /\ _ => destruct HP2 as [_ HP2]
  end. exact HP2. }
assert (Hlen3 : exv_len E <= 3 * 2 ^ 20).
{ pose proof HPRE as HP2. unfold EXV_PRE in HP2. cbv zeta in HP2.
  repeat lazymatch type of HP2 with
  | (exv_len E <= 3 * 2 ^ 20) /\ _ => destruct HP2 as [HP2 _]
  | _ /\ _ => destruct HP2 as [_ HP2]
  end. exact HP2. }
assert (Hlen0 : 0 <= exv_len E) by (unfold exv_len; lia).
destruct HWD as (Hscr0 & Hscrc & Hscram & Hscrw & Hscrra & Hscrhull).
destruct HCUR as (Cq0 & Cq8 & Cq16 & Cq24 & Cq32).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ & _).
destruct Htag as (Htgr & Vtg). destruct Hstr as (Hstrr & Vstr).
assert (Htg6 : 0 <= PjTree.tag (e_t E) <= 6) by (destruct (e_t E); cbn [PjTree.tag]; lia).
assert (Hvq : e_q E + 40 <= e_v E \/ e_v E + 56 <= e_q E).
{ destruct (Z_le_gt_dec (e_q E + 40) (e_v E)) as [h|h]; [left; lia|].
  destruct (Z_le_gt_dec (e_v E + 56) (e_q E)) as [h2|h2]; [right; lia|].
  exfalso. destruct (HVDJ (Z.max (e_v E) (e_q E)) ltac:(lia)) as (_ & Hq'). apply Hq'. lia. }
assert (Hvs1 : exv_s1 E + 160 <= e_v E \/ e_v E + 56 <= exv_s1 E).
{ destruct (Z_le_gt_dec (exv_s1 E + 160) (e_v E)) as [h|h]; [left; lia|].
  destruct (Z_le_gt_dec (e_v E + 56) (exv_s1 E)) as [h2|h2]; [right; lia|].
  exfalso. destruct (HVDJ (Z.max (e_v E) (exv_s1 E)) ltac:(lia)) as (Hs' & _). apply Hs'. lia. }
assert (HS : st_ok rsegs (Ereg regs [Z_to_bv 64 (e_v E); Z_to_bv 64 (e_scr E); Z_to_bv 64 (e_dl E);
    Z_to_bv 64 (PjTree.tag (e_t E)); Z_to_bv 64 str]) ss_exe_v
  (restrict (w_H Wc) (@YK11.mkst fxc regs (Z_to_bv 64 EXE_CC) memc (YK11.seg_rom rsegs)))).
{ apply (exe_st_v fxc Wc regs memc (exv_s1 E) (e_q E) (frame_addr lyc 1 pos) (e_v E) (e_scr E) (e_dl E)
           (PjTree.tag (e_t E)) str R9 R19 R24 R25 R20 R27);
  [ lia | exact Hs18 | lia | lia | lia | exact Hq8 | lia | lia | lia | exact Hv8
  | lia | lia | exact Htg6 | lia | exact Hvq | exact Hvs1
  | exact C136 | exact S144 | exact S152 | exact Cq24 | exact Cq32
  | intros o Ho; apply (apresent_writable rsegs); apply HpresJ; lia
  | exact Vtg | exact Vstr ]. }
set (E1 := Ereg regs [Z_to_bv 64 (e_v E); Z_to_bv 64 (e_scr E); Z_to_bv 64 (e_dl E);
    Z_to_bv 64 (PjTree.tag (e_t E)); Z_to_bv 64 str]) in HS.
assert (E19 : ew E1 19 = Z_to_bv 64 (e_q E)) by (unfold E1; exact (exe_ew regs _ 19 19%bv _ eq_refl R19)).
assert (E25 : ew E1 25 = Z_to_bv 64 SHADOW_OFF) by (unfold E1; exact (exe_ew regs _ 25 25%bv _ eq_refl R25)).
assert (E24 : ew E1 24 = Z_to_bv 64 (frame_addr lyc 1 pos))
  by (unfold E1; exact (exe_ew regs _ 24 24%bv _ eq_refl R24)).
assert (E32 : ew E1 32 = Z_to_bv 64 (e_v E)) by (unfold E1; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E1 33 = Z_to_bv 64 (e_scr E)) by (unfold E1; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E1 34 = Z_to_bv 64 (e_dl E)) by (unfold E1; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E1 35 = Z_to_bv 64 (PjTree.tag (e_t E))) by (unfold E1; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E1 36 = Z_to_bv 64 str) by (unfold E1; exact (ew_Ereg_extra regs _ 4)).
assert (U19 : bv_unsigned (ew E1 19) = e_q E) by (apply exe_U; [exact E19 | lia]).
assert (U25 : bv_unsigned (ew E1 25) = SHADOW_OFF) by (apply exe_U; [exact E25 | unfold SHADOW_OFF; lia]).
assert (U32 : bv_unsigned (ew E1 32) = e_v E) by (apply exe_U; [exact E32 | lia]).
assert (AG1 : env_agree 32 (Ereg regs [Z_to_bv 64 (e_v E); Z_to_bv 64 (e_scr E); Z_to_bv 64 (e_dl E);
    Z_to_bv 64 (PjTree.tag (e_t E)); Z_to_bv 64 str]) E1) by (unfold E1; apply env_agree_refl).
assert (SHOK : sh_ok rsegs EXE_SB exe_SHv E1 (rdW Wc memc)).
{ unfold sh_ok, exe_SHv. constructor; [|constructor; [|constructor]].
  - apply (exe_shq (w_H Wc) memc E1 (e_q E) U19 U25); [lia | lia | exact HQRA].
  - apply (exe_shv (w_H Wc) memc E1 (e_v E) U32 U25); [lia | lia | | exact HVRA].
    intros x Hx. pose proof (HVBAND x Hx) as HB2. change (2 ^ 44) with 17592186044416 in HB2. exact HB2. }
clearbody E1.
unfold cfg_at. change (w64 EXE_CC) with (Z_to_bv 64 EXE_CC).
pose (RUN := SRr_run_tok_AJx (SK := SK) (fx := fxc) rsegs B prh_pst ARx LAWS B_prog_segs_low
  B_prog_tbl B_prog_tbl_ok B_prog_wx).
pose (RUNTO := SRr_run_to_tok_AJx (SK := SK) (fx := fxc) rsegs B prh_pst ARx LAWS B_prog_segs_low
  B_prog_tbl B_prog_tbl_ok B_prog_wx).
exw_run RUN HS HJ SHOK.
{ exe_awr U19. }
exw_kept_of HFr (fun a => e_q E + 32 <= a < e_q E + 36) ltac:(fun h => rewrite ?U19 in h).
exe_mn_of HF (fun a => e_q E + 32 <= a < e_q E + 36) ltac:(fun h => rewrite ?U19 in h)
  ltac:(intros amn Hamn; cbv beta in Hamn; lia).
rename KEPT into K1. rename HG into G1. rename MNK into MN1. clear HF HFr.
exw_branch HS SHOK.
- (* v->type <> 3: in->differs := 1 *)
  rewrite branch_ne_U, (U_atom E1 35 (PjTree.tag (e_t E)) E35 ltac:(lia)), (U_lit E1 3 ltac:(lia)) in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  assert (Hne : e_t E <> PjTree.JNum (exn_sub (e_x E) (EXN_i1 E) j) bits)
    by (intros Heq; rewrite Heq in Hc; cbn [PjTree.tag] in Hc; lia).
  exw_run_to RUNTO HS HJ SHOK EXE_CD.
  { exe_awr U19. }
  exw_kept_of HFr (fun a => e_q E + 32 <= a < e_q E + 36) ltac:(fun h => rewrite ?U19 in h).
  exe_mn_of HF (fun a => e_q E + 32 <= a < e_q E + 36) ltac:(fun h => rewrite ?U19 in h)
    ltac:(intros amn Hamn; cbv beta in Hamn; lia).
  rename KEPT into K2. rename HG into G2. rename MNK into MN2. clear HF HFr.
  lazymatch type of HS with
  | st_ok _ _ _ (restrict _ ?mx) =>
    assert (RK : forall r, In r exe_kept -> YK11.getr (ms_regs mx) r = YK11.getr regs r)
      by (intros r Hr; exact (regs_kept_of_st_ok rsegs _ _ _ regs _ exe_kept HS AG1
            ltac:(vm_compute; reflexivity) r Hr))
  end.
  lazymatch type of HS with
  | st_ok _ _ _ (restrict _ ?mx) =>
    assert (R13 : YK11.getr (ms_regs mx) 13 = YK11.getr regs 13)
      by (exact (regs_kept_of_st_ok rsegs _ _ _ regs _ [13%bv] HS AG1 ltac:(vm_compute; reflexivity) 13%bv
            (or_introl eq_refl)))
  end.
  pose proof (exw_region_nth rsegs _ _ _ 1%nat _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
  pose proof (exw_field rsegs _ _ 19%nat (e_q E) _ _ _ _ _ 32 4 (SLit 1) 1 RQ U19
    ltac:(left; reflexivity) ltac:(apply exe_den_lit; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as VQ.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst ?f ?rg ?pc ?mm ?rom) ?md) _ =>
    replace pc with (w64 (exv_pc EXN_CD)) by (vm_compute; reflexivity) end.
  eapply (exe_close B ARx SK E pos HYP EF MK MC KS fxc lyc Sc Hpc Wc regs memc mdc k c j bits _ _ _ _ 1 HPRE HCC).
  + exact HJ.
  + intros z Hz Hw Hq. rewrite (K2 z Hz Hq). exact (K1 z Hz Hq).
  + intros a Ha. exact (apresent_grows (w_H Wc) _ _ a G2 (apresent_grows (w_H Wc) _ _ a G1 Ha)).
  + intros Hm. exact (MN2 (MN1 Hm)).
  + exact RK.
  + rewrite R13. exact R13c.
  + exact VQ.
  + right; reflexivity.
  + split; [intros _; right; split; [exact Hvn | exact Hne] | intros _; reflexivity].
- (* v->type = 3: __wrap_strcmp (v->str, in->scratch) *)
  rewrite branch_ne_U, (U_atom E1 35 (PjTree.tag (e_t E)) E35 ltac:(lia)), (U_lit E1 3 ltac:(lia)) in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc.
  destruct (e_t E) as [| | | txt2 bits2 | s0 | its | ms0] eqn:Et; try (rewrite Et in Hc);
    cbn [PjTree.tag] in Hc; try lia.
  destruct (Hnum3 txt2 bits2 ltac:(first [exact Et | reflexivity])) as (Hb2 & kk & Hcs).
  destruct Hcs as (HLk & Hkk & Hl32 & Hcb).
  destruct Hcb as (Hnz2 & G0).
  assert (FX : Forall (fun z => z <> 0) txt2) by (eapply Forall_impl; [|exact Hnz2]; intros z Hz; cbv beta in *; lia).
  destruct (exe_N_txt _ _ _ _ HN) as (HTXTB & _).
  assert (FY : Forall (fun z => z <> 0) (exn_sub (e_x E) (EXN_i1 E) j))
    by (eapply Forall_impl; [|exact HTXTB]; intros z Hz; cbv beta in *; lia).
  assert (HTL : Z.of_nat (length (exn_sub (e_x E) (EXN_i1 E) j)) <= exv_len E).
  { unfold exn_sub, exv_len. rewrite length_firstn, length_skipn. lia. }
  pose proof HLED as HLED'. destruct HLED' as (_ & _ & HBL & _). rewrite Forall_forall in HBL.
  destruct (HBL (str, kk) HLk) as (Hkk0 & Hblk & Hhp & _ & _). cbn [fst snd] in Hblk, Hhp, Hkk0.
  destruct (alx_blocks rsegs B ARx LAWS lyc Sc Hpc Wc memc mdc (str - cf_head) (kk + cf_head) HAR Hblk)
    as (_ & Hstrlo & Hstrhi & _).
  assert (Hrq2 : kk + cf_head <= req_size (kk + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (kk + cf_head) 0); lia).
  destruct HSB as (b2 & m2 & Hin2 & Hb2l & Hm2 & Hhd2).
  exw_run_to RUNTO HS HJ SHOK EXE_SCMP.
  { exe_awr U19. }
  exw_kept_of HFr (fun a => e_q E + 32 <= a < e_q E + 36) ltac:(fun h => rewrite ?U19 in h).
  exe_mn_of HF (fun a => e_q E + 32 <= a < e_q E + 36) ltac:(fun h => rewrite ?U19 in h)
    ltac:(intros amn Hamn; cbv beta in Hamn; lia).
  rename KEPT into K2. rename HG into G2. rename MNK into MN2. clear HF HFr.
  lazymatch type of HS with
  | st_ok _ _ _ (restrict _ ?mx) =>
    assert (KC : forall z, 0 <= z < 2 ^ 64 -> ~ (e_q E + 32 <= z < e_q E + 36) ->
       aview rsegs (w_H Wc) (ms_mem mx) z = aview rsegs (w_H Wc) memc z)
      by (intros z Hz Hq; rewrite (K2 z Hz Hq); exact (K1 z Hz Hq));
    assert (GC : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) (ms_mem mx) a)
      by (intros a Ha; exact (apresent_grows (w_H Wc) _ _ a G2 (apresent_grows (w_H Wc) _ _ a G1 Ha)));
    assert (RK1 : forall r, In r exe_kept -> YK11.getr (ms_regs mx) r = YK11.getr regs r)
      by (intros r Hr; exact (regs_kept_of_st_ok rsegs _ _ _ regs _ exe_kept HS AG1
            ltac:(vm_compute; reflexivity) r Hr))
  end.
  lazymatch type of HS with
  | st_ok _ _ _ (restrict _ ?ms0) =>
    assert (GX : garr8 rsegs (rdW Wc (ms_mem ms0)) str (txt2 ++ [0]))
      by (apply (exe_garr_move rsegs (w_H Wc) memc (ms_mem ms0));
          [intros i Hi; rewrite length_app in Hi; cbn [length] in Hi; apply KC; lia | exact G0]);
    assert (GY : garr8 rsegs (rdW Wc (ms_mem ms0)) (e_scr E) (exn_sub (e_x E) (EXN_i1 E) j ++ [0]))
      by (apply (exe_garr_move rsegs (w_H Wc) memc (ms_mem ms0));
          [intros i Hi; rewrite length_app in Hi; cbn [length] in Hi; apply KC; lia | exact Hgarr]);
    assert (Cq32c : val_mem rsegs (rdW Wc (ms_mem ms0)) (e_q E + 32) 4 (e_dl E))
      by (pose proof (exw_region_nth rsegs _ _ _ 1%nat _ HS eq_refl) as RQ0; cbn [ms_mem restrict] in RQ0;
          exact (exw_field rsegs _ _ 19%nat (e_q E) _ _ _ _ _ 32 4 (SOff 34 0) (e_dl E) RQ0 U19
            ltac:(right; left; reflexivity)
            ltac:(rewrite (exe_den_off E1 34 (e_dl E) 0 E34) by lia; rewrite Z.add_0_r; reflexivity)
            ltac:(cbn; lia) ltac:(cbn; lia)));
    assert (Vb2c : PRH_Reader.rd_u64 rsegs (rdW Wc memc) (e_v E + 8) bits2) by exact Hb2;
    assert (HJc : ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E)
       (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] lyc Sc Hpc Wc (ms_mem ms0) _ k) by exact HJ;
    assert (HBc : EXB (fx := fxc) B ARx SK E lyc Sc Hpc Wc (ms_regs ms0) (ms_mem ms0) _ k pos)
      by (apply (exv_kt B ARx SK HYP E lyc Sc Hpc Wc regs memc mdc k pos (ms_regs ms0) (ms_mem ms0) _ k
            HPRE HB HJc);
          [ intros a Ha _ Hf; apply KC; [exact Ha|];
            intros Hq; apply Hf; split; [unfold exv_FP; exists (e_q E + 32, e_q E + 36);
              split; [cbn [In]; tauto | cbn [fst snd]; lia] | lia]
          | intros a Ha; apply GC; exact Ha
          | intros Hm0; exact (MN2 (MN1 (proj2 HRM Hm0)))
          | intros r Hr; apply RK1; cbv [exe_kept]; cbn [In] in Hr |- *; tauto ]);
    destruct (exv_kit_rodata B ARx SK HYP fxc E lyc Sc Hpc Wc (ms_regs ms0) (ms_mem ms0) _ k pos HPRE HBc)
      as (HROD & _);
    pose proof HBc as HBc0; unfold EXB in HBc0; cbv zeta in HBc0;
    destruct HBc0 as (_ & _ & _ & _ & _ & _ & _ & HLEDc & _);
    destruct (exe_blk_op B ARx SK HYP lyc Sc Hpc Wc (ms_mem ms0) _ (str - cf_head) (kk + cf_head) str txt2
       (proj1 HJc) Hblk ltac:(lia) ltac:(lia) GX FX) as (X1 & X2 & X3 & X4 & X5 & X6 & X7);
    destruct (exe_blk_op B ARx SK HYP lyc Sc Hpc Wc (ms_mem ms0) _ b2 m2 (e_scr E) (exn_sub (e_x E) (EXN_i1 E) j)
       (proj1 HJc) Hin2 Hb2l ltac:(lia) GY FY) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7);
    destruct (exv_sh_lam B ARx SK HYP lyc Sc Hpc Wc (ms_mem ms0) _ (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E)
       str kk str (Z.of_nat (length txt2) + 1) (proj1 HJc) HLEDc
       HLk ltac:(lia) ltac:(lia) ltac:(lia)) as (XS1 & XS2);
    assert (HYRA : range_addressable (aview rsegs (w_H Wc) (ms_mem ms0)) SHADOW_OFF (e_scr E)
                     (Z.of_nat (length (exn_sub (e_x E) (EXN_i1 E) j)) + 1))
      by (apply (exv_ra_keep (aview rsegs (w_H Wc) memc)); [intros s0 Hs0; apply KC; lia | lia | lia |];
          apply (range_addressable_sub _ _ (e_scr E) (exv_len E + 1)); [exact Hscrra | lia | lia]);
    assert (HYHU : shadow_hull_vis (aview rsegs (w_H Wc) (ms_mem ms0)) (e_scr E)
                     (Z.of_nat (length (exn_sub (e_x E) (EXN_i1 E) j)) + 1))
      by (apply (exv_hull_keep (aview rsegs (w_H Wc) memc)); [intros s0 Hs0; apply KC; lia | lia | lia |];
          apply (exv_hull_sub _ (e_scr E) (exv_len E + 1)); [apply Hscrhull; lia | lia | lia])
  end.
  pose proof (st_ok_restrict_reg rsegs (w_H Wc) _ _ _ 10%bv HS) as Pa0.
  lazymatch type of Pa0 with _ = sv_denot ?Ex (sr_get ?l _) =>
    change (sr_get l 10%bv) with (SOff 36 0) in Pa0 end.
  rewrite (exe_den_off E1 36 str 0 E36) in Pa0 by lia. rewrite Z.add_0_r in Pa0.
  cbn [ms_regs restrict] in Pa0.
  pose proof (st_ok_restrict_reg rsegs (w_H Wc) _ _ _ 11%bv HS) as Pa1.
  lazymatch type of Pa1 with _ = sv_denot ?Ex (sr_get ?l _) =>
    change (sr_get l 11%bv) with (SOff 33 0) in Pa1 end.
  rewrite (exe_den_off E1 33 (e_scr E) 0 E33) in Pa1 by lia. rewrite Z.add_0_r in Pa1.
  cbn [ms_regs restrict] in Pa1.
  pose proof (st_ok_restrict_reg rsegs (w_H Wc) _ _ _ 1%bv HS) as Pra.
  lazymatch type of Pra with _ = sv_denot ?Ex (sr_get ?l _) =>
    change (sr_get l 1%bv) with (SLit EXE_R1) in Pra end.
  rewrite (exe_den_lit E1 EXE_R1 ltac:(vm_compute; split; [discriminate | reflexivity])) in Pra. cbn [ms_regs restrict] in Pra.
  lazymatch type of HS with
  | st_ok _ _ _ (restrict _ ?mx) =>
    assert (Usp : spZ (ms_regs mx) = exv_s1 E)
      by (unfold spZ; rewrite (RK1 2%bv ltac:(cbv [exe_kept]; cbn [In]; repeat (first [left; reflexivity | right])));
          rewrite R2; unfold w64; apply unsigned_lit_small; lia)
  end.
  pmkst HS.
  eapply SRr_bind.
  { eapply (YGcallMxmn.aj_strcmp_at_xrom (SK := SK) rsegs B prh_pst ARx B_prog_relro_lo B_prog_relro_hi
      LAWS B_prog_segs_low (B_prog_sigma AS___wrap_strcmp) (eh_strcmp B ARx SK HYP fxc) Wc _ _
      (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E) (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E)
      [(1, pos)] lyc Sc Hpc _ k str (e_scr E) (Z.of_nat (length txt2))
      (Z.of_nat (length (exn_sub (e_x E) (EXN_i1 E) j))) (exv_s1 E - (exv_sp E + e_d E)) _ HJ Pa0 Pa1).
    all: try (rewrite ?Usp; lia).
    - rewrite (RK1 3%bv ltac:(cbv [exe_kept]; cbn [In]; repeat (first [left; reflexivity | right]))). exact R3.
    - rewrite (RK1 4%bv ltac:(cbv [exe_kept]; cbn [In]; repeat (first [left; reflexivity | right]))). exact R4.
    - reflexivity.
    - rewrite Pra. vm_compute. reflexivity.
    - exact X5.
    - exact Y5.
    - intros a Ha. split; [apply X6; lia | rewrite Usp; lia].
    - intros a Ha. split; [apply Y6; lia | rewrite Usp; lia].
    - exact X4.
    - exact Y4.
    - exact XS1.
    - exact XS2.
    - exact HYRA.
    - exact HYHU.
    - exact X7.
    - exact Y7.
    - exact HROD. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & rv & -> & HJ2 & HP2 & Hres2 & Hcmp & Hfr2 & Hpres2 & Hmn2).
  rewrite Pra.
  lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst ?f ?rg ?pc ?mm ?rom) ?md) _ =>
    replace pc with (w64 EXE_R1) by (vm_compute; reflexivity) end.
  lazymatch type of KC with
  | forall _, _ -> _ -> aview _ _ ?mx _ = _ =>
    apply (exe_arm_r1 fxc lyc Sc Hpc Wc regs memc mdc k c j bits regs2 mem2 md2 _ rv txt2 bits2
             HPRE HCC Hvn Et Vb2c HJ2);
    [ intros z Hz Hw Hq; rewrite (Hfr2 z Hz ltac:(lia)); exact (KC z Hz Hq)
    | apply (exe_val_move rsegs (w_H Wc) mx mem2 (e_q E + 32) 4 (e_dl E));
        [intros i Hi; apply Hfr2; lia | exact Cq32c]
    | intros a Ha; apply Hpres2; apply GC; exact Ha
    | intros Hm; exact (Hmn2 (MN2 (MN1 Hm)))
    | intros r Hr; rewrite (exe_kept_of_pres _ _ HP2 r Hr); exact (RK1 r Hr)
    | exact Hres2
    | rewrite Hcmp; exact (exe_str_eq rsegs (w_H Wc) mx str (e_scr E) txt2
        (exn_sub (e_x E) (EXN_i1 E) j) GX GY) ]
  end.
Qed.

(* ======== EXN_Ec: CC (exv_pc 0x910) to CD (exv_pc 0x9a8) ======== *)
Lemma exn_Ec : EXN_Ec B ARx SK E pos.
Proof.
unfold EXN_Ec. intros fxc lyc Sc Hpc Wc regs memc mdc k c j bits HPRE HCC.
destruct (Z.eq_dec (e_v E) 0) as [Hv0|Hvn].
- exact (exe_arm_0 B ARx SK E pos HYP EF MK MC KS fxc lyc Sc Hpc Wc regs memc mdc k c j bits HPRE HCC Hv0).
- exact (exe_arm_v fxc lyc Sc Hpc Wc regs memc mdc k c j bits HPRE HCC Hvn).
Qed.
End p.

Print Assumptions exn_Ec.
