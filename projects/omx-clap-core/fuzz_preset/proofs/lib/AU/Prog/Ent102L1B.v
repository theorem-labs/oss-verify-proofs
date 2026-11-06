(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image B' (asan-ubsan, harness fix #102, pin sha256
   d663f82d7f488d30f8e8d7496cb814e595a2f3cbbf16bde81a65cb3ea9af0994, unstripped twin c90d4fa54d43160b):
   SEGMENT L1 of LLVMFuzzerTestOneInput (entry 0x816cc): listing slots 73 .. 82 (+0x124 .. the return of the
   `jal check_no_overread` at +0x14c; B' 0x817f0 -> 0x81818), proved against lib/AU/Ent102CutsB.v's `seg_L1_stmt`
   (cut_s1 E fk -> cut_cno E fk).
   THE B' TWIN of lib/A/Prog/Ent102L1A.v (seg_L1_A as of its Qed at commit 90bcaf49278f
   on b1ed4e6c944d), ported by port/a2b.py (sha256 f5113cbc90e503da) and then by hand: L := B_prog_listing,
   PL := PL_102_B (lib/B/Ent102PLB.v), e_A -> e_B, ec_A -> ec_B, the B' twins lib/AU/Prog/Ent102L6BfLem.v /
   Ent102CallB.v of the shared A' files and the record's lib/AU/Ent102PosB.v; lib/A/Prog/Ent102GrantA.v,
   lib/A/Ent102ReqA.v and lib/A/Prog/S1Ledger.v are shared by both images. The B' body is A''s up to pc-relative
   fields; in this lane slot 74 (+0x128) is the one non-pc-relative difference (A' `sb zero,-0x1c4(s9)`, word
   0xe20c8e23; B' `sb zero,0x590(s9)`, word 0x580c8823; the other differing words are pc-relative with the same
   targets, cmpkit 4bbd3a74be89, by address), which is the B' cut file's one patched fact ei_own
   (pa_val (A_HI 4) + 0x590 = pi_g_own_ran_out): the symbolic region l1_r_own, its atom fact and the entry lemma take
   the B' displacement +1424; and ei_empty is over YImgTop.IMG_LO_B / IMG_TOP_B (l1_src_empty).
   WHAT THE LANE'S CODE DOES (fuzz_preset.c new:808-811):
     +0x124 auipc s9 (slot 73, PHi 4); +0x128 sb zero,0x590(s9)       g_own_ran_out := 0 (ei_own: the byte is the kit's
                                                                        pi_g_own_ran_out, of width 1)
     +0x12c jal fuzz_alloc_ran_out_reset                                g_ran_out := 0
     +0x130 slli a0,s3,8; +0x134 lui a1,5; +0x138 add a0,a0,a1         a0 = 256 n + 20480 = PJ_ALLOC_BOUND n
     +0x13c jal fuzz_alloc_most                                         g_most := PJ_ALLOC_BOUND n
     +0x140 mv a0,s4; +0x144 mv a1,s3; +0x148 jal check_no_overread    r = check_no_overread (data, size)
   fuzz_alloc_ran_out_reset and fuzz_alloc_most are closed by their kit TEXTS from ec_texts (ech_texts), and
   check_no_overread by GrantA's granted form tcheck_no_overread_grantedX, DERIVED from the batch kit's text (ec_texts'
   et_check_no_overread) by lib/A/Prog/Ent102OfPost.v tcheck_no_overread_grantedX_of_post, each at this body's context
   ec_ctx0 with ei_fp / ei_rets (Ent102CallB.v ec_ctx_call_img), never by walking the callee; check_no_overread's
   request bound is the PARSE arm of lib/A/Ent102ReqA.v's ec_req_bound (ec_rq_pj_parse + PjReqBoundW.rq_read_bound;
   a Theorem Labs lane 15:35Z), its LIVE premise is ec_pay's ecov_cno, its count is paid by epay_cno.
   The store and the first call are ONE run of YC80x.v's runner in its PST-write, memory-invariant form
   (YC1fPx.v paj_run_x_m_inv at P := YSRrMemnorm.v's memnorm instance): the write premise is the PST disjunct, the
   one written byte is the image's g_own_ran_out (ei_own), writable by ei_pst_w.
   STATEMENT: lib/AU/Ent102CutsB.v, read at commit b1ed4e6c944d
   (blob a74a7497b9d0, the batch kit's texts at the seam, the wild budget through the walk: seg_L1_stmt over ec_hyps, cut_s1 at
   spent budget 0, cut_cno at ec_wk_cno, with the exact room position and the return tie, ec_img, ec_pay),
   lib/AU/Ent102PosB.v (ec_supply_run). NO provisional argument: the granted form of check_no_overread
   (lib/A/Prog/Ent102GrantA.v tcheck_no_overread_grantedX, generic in the listing class: `rp_x = x`, R1, the batch kit's wild room
   and budgeted post) is derived from the batch kit's text by Ent102OfPost.v's bridge at L := B_prog_listing; its wild room is
   ec_room_at's from ec_pre's entry room and cut_s1's spent budget 0; its budgeted post makes cut_cno's spent budget
   ec_wk_cno; the cut file's ec_journal_plain (cut_s1's budget-0 journal) and ec_inv_wk_grow (the no-call stretches).
   LISTING: lib/B/Listing_prog.v (slot k = byte offset 4k from the entry), run with the PAListing PL_102_B of
   lib/B/Ent102PLB.v; the image half stays generic ({PA : PAImg B_prog_listing}; lib/B/PAImg_prog.v, PresetCfnA and
   PresetCfnB are not loaded, no vm_compute on pa_val / pa_sigma).
   The kit TEXTS (g_most / g_own_ran_out are ledger FIELDS): lib/A/PRH_FnAlloc.v (tfuzz_alloc_ran_out_reset_specX),
   lib/A/PRH_FnCheck.v (tfuzz_alloc_most_specX), lib/A/PRH_Base.v (fpre, fpost, prh_ledger and its projections
   prh_ledger_most / prh_ledger_own): generic over the listing class, the same files on both images.
   rule 24: proves function LLVMFuzzerTestOneInput, segment L1 on image B'. Lookup (the A' row's, the same function):
   `proof-index LLVMFuzzerTestOneInput` exit 0 (30 named, 1290 by address, 105 related, 7 released lemma(s);
   fuzz_preset hits are only the released plain/ubsan contract definitions lib/Prog/LLVMFuzzerTestOneInput_c.v:14,
   lib/U/Prog/LLVMFuzzerTestOneInput_c.v:15); `proof-index 0x815e0` exit 4 (0 named, 0 by address, 0 released);
   R24CheckLL CONFIRM 14:51Z: no released ASan proof, NEW walk. The A' twin is this lane's; this row ports it.
   SUPPORT: lib/AU/Prog/Ent102L1BHelp.v (this lane's), lib/AU/Prog/Ent102CallB.v and Ent102L6BfLem.v (shared B' twins).
   NUMERALS: 292 = 0x124 is the lane's first slot offset (EC_S1 - EC_BASE); 304 / 320 / 332 = 0x130 / 0x140 / 0x14c
   are the return-site offsets (EC_AR_RORESET / EC_AR_MOST / EC_AR_CNO - EC_BASE), the same on both images;
   1424 = 0x590 is the `sb`'s displacement (the listing's word 0x580c8823); 284 is A_HI 4; 8 / 16 / 128 / 144 are
   frame LENGTHs; 2 ^ 40 / 2 ^ 64 are the engine's code-span and word ranges. No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK1d YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PjReqBoundW PresetReqAt PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnAlloc PRH_FnPj PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Ent102ReqA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog Ent102PLB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import Ent102CutsB Ent102PosB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger Ent102GrantA Ent102OfPost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.Prog Require Import Ent102L6BfLem Ent102CallB Ent102L1BHelp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. The symbolic state of the store: the lane's first slot, the register atoms, ONE region - the byte the `sb`
      writes, based at the hi atom of slot 73 (A_HI 4) at displacement +1424 (0x590), written, no chunk - and the range fact
      of that atom: the written byte is an image byte (ei_pst), so it lies in [kImgLo, kImgEnd) (Ent102L6BfLem.v
      l6f_img_bounds), which keeps the region off the token span [0, 0]. *)
Definition L1_K : Z := 292.
Definition l1_r_own : YP09.region := YP09.mkRegion (Some (A_HI 4)) 1424 1425 1424 1425 [].
Definition l1_facts : facts := mkFacts [(A_HI 4, mkAF (kImgLo - 1424) (kImgEnd - 1424) 0)] [] [].
Definition ss_l1 : sstate := mkSS L1_K sr_atoms [l1_r_own] None l1_facts.
Definition L1_SH : list shent := [].
Definition L1_Bx : sv := SLit SHADOW_OFF.
Definition L1_Bspan : Z * Z := (0, 0).

(* a register read through register updates, the registers compared by their numbers (the decoder's register
   literals and the statement's are different terms of the same value) *)
Lemma l1_getr_same : forall regs (r r' : bv 5) v, bv_unsigned r = bv_unsigned r' -> bv_unsigned r <> 0 ->
  getr (regupd regs r v) r' = v.
Proof.
intros regs r r' v H H0. assert (E : r = r') by (apply bv_eq; exact H). subst r'.
apply getr_same. intros E. apply H0. rewrite E. reflexivity.
Qed.
Lemma l1_getr_other : forall regs (r r' : bv 5) v, bv_unsigned r <> bv_unsigned r' ->
  getr (regupd regs r v) r' = getr regs r'.
Proof. intros regs r r' v H. apply getr_other. intros E. apply H. rewrite E. reflexivity. Qed.
Ltac l1_gr := repeat first
  [ rewrite l1_getr_same by (vm_compute; first [reflexivity | (let Hx := fresh in intro Hx; discriminate Hx)])
  | rewrite l1_getr_other by (vm_compute; let Hx := fresh in intro Hx; discriminate Hx) ].
Lemma l1_getr_num : forall regs (r r' : bv 5), bv_unsigned r = bv_unsigned r' -> getr regs r = getr regs r'.
Proof. intros regs r r' H. assert (E : r = r') by (apply bv_eq; exact H). subst r'. reflexivity. Qed.
(* `mv rd, rs` is `addi rd, rs, 0` *)
Lemma l1_addi0 : forall (x : word) (imm : bv 12), bv_signed imm = 0 -> v_addi x (bv_signed imm) = x.
Proof. intros x imm H. rewrite H. unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Section L1. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {PA : @PAImg rc B_prog_listing}.
Variable B : asyms.
Variable SK : YI16.sink_head.
Variables EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP : Z.
Variable EC_SIO : reader -> Prop.
Variable EC_SIO_IMG : Z -> Prop.
Variables ec_ccut ec_lcut : @ecx rc B_prog_listing PA -> nat -> Z.

#[local] Notation SEGS := (@pa_segs rc B_prog_listing PA).
#[local] Notation VAL := (@pa_val rc B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma rc B_prog_listing PA).
#[local] Notation BASE := (@pa_val rc B_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst PI).
#[local] Notation ARc := (@ec_ARx rc ci cp B_prog_listing PA B).
(* lane L1 crosses check_no_overread's frees: it runs at wle' over the fixed zone (Ent102CutsB.v ec_laneR WLE') *)
#[local] Notation WLE' := (wle' SEGS (@YGcfRehidePost.RZ_cf rc)).

Definition L1_EI (regs : bvmap 5 word) : env := Eimg (L := B_prog_listing) (PI := PA) (Ereg regs []).

Lemma l1_entry_ok : forall (fz : YK11.FPState) (W : world SEGS) regs mem,
  writable_at SEGS (mrestrict (w_H W) mem) (VAL (A_HI 4) + 1424) ->
  kImgLo <= VAL (A_HI 4) + 1424 < kImgEnd ->
  st_ok_pi SEGS VAL (L1_EI regs) ss_l1
    (restrict (w_H W) (@YK11.mkst fz regs (Z_to_bv 64 (BASE + L1_K)) mem (YK11.seg_rom SEGS))).
Proof.
intros fz W regs mem Hw H0. unfold kImgLo, kImgEnd in H0.
pose proof (@pa_val_range rc B_prog_listing PA (A_HI 4)) as Hr.
assert (HEI : img_env VAL A_LIM (L1_EI regs)) by (unfold L1_EI; apply Eimg_env).
assert (U : bv_unsigned (ew (L1_EI regs) (A_HI 4)) = VAL (A_HI 4)) by (apply HEI; unfold A_HI, A_TEXT, A_LIM; lia).
rewrite (restrict_mkst_fx (fx := fz)).
unfold ss_l1. apply (pa_entry_st_ok_full (fx := fz)).
- unfold L1_EI. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok, l1_r_own.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. replace (VAL (A_HI 4) + o) with (VAL (A_HI 4) + 1424) by lia. exact Hw.
- apply pairwise_disjoint_of_extents. unfold extent_of_region, l1_r_own. cbn. repeat (constructor || split).
- split; [|split; [cbn; exact I | cbn; exact I]].
  cbn [l1_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U. rewrite Z.pow_0_r, Z.mod_1_r. unfold kImgLo, kImgEnd in *.
  repeat match goal with |- _ /\ _ => split end; try lia; try reflexivity; try exact I.
Qed.

Theorem seg_L1_B :
  @seg_L1_stmt fx rc ci cp PI RL B_prog_listing PA B SK EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG
    ec_ccut ec_lcut.
Proof.
unfold seg_L1_stmt, ec_laneR.
intros E fk HYP W c Hcut.
assert (HTX := HYP). apply ech_texts in HTX.
assert (HIMG := HYP). apply ech_img in HIMG.
assert (HUN := HYP). apply ech_univ in HUN.
assert (HCC := HYP). apply ech_ccut_ok in HCC.
assert (HLC := HYP). apply ech_lcut_ok in HLC.
assert (HPAY := HYP). apply ech_pay in HPAY.
destruct Hcut as (ly & S & Hp & regs & mem & md & own & peak & k & Hat & Hinv & HHp & HCB & HLB & Hrk & Hfrm & Hn).
destruct Hat as (fy & Hfz & Hkept & Hc).
subst Hp c.
(* cut_s1 is before any free (journal at wle): read it at wle' (Ent102CutsB.v ec_inv_wle') *)
apply ec_inv_wle' in Hinv.
pose proof (l1_geo B SK EC_RA EC_EMPTY EC_SIO WLE' E fk ly S [] W mem md own [] peak (e_cnt E) (e_ran E) k (e_os E) (e_i0 E)
  0%nat Hinv)
  as (G1 & G2 & G3 & G4 & G5 & G6).
pose proof Hinv as ((WS0 & HJW0 & Hwb0) & HOWN & (most0 & own0 & HLED) & _ & _ & HRL & HRP & HCNT & HPRE & HNC & HPERM
  & _ & HMN).
(* cut_s1's spent wild budget is 0: its journal is the plain one the runner takes (the cut file's ec_journal_plain) *)
assert (HJ : ajournal_xR (SK := SK) SEGS B PST ARc WLE' LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E)
  own ly S [] W mem md k) by (eapply ec_journal_plainR; [exact HJW0 | exact Hwb0]).
assert (Hwb00 : YCbqGwild.wbudget [] 0 []) by (unfold YCbqGwild.wbudget; apply Nat.le_refl).
(* ec_pre's parts BY NAME (Ent102CallB.v ec_pre_payload / ec_pre_len, Ent102L1BHelp.v l1_pre_frames / _i0 / _cnt) *)
pose proof (ec_pre_payload (fx := fx) (cp := cp) (PI := PI) (RL := RL) (PA := PA) B EC_RA EC_EMPTY EC_SIO HPRE) as HPN.
pose proof (ec_pre_len (fx := fx) (cp := cp) (PI := PI) (RL := RL) (PA := PA) B EC_RA EC_EMPTY EC_SIO HPRE) as HNL.
pose proof (l1_pre_frames B EC_RA EC_EMPTY EC_SIO E HPRE) as HFR0.
pose proof (l1_pre_i0 B EC_RA EC_EMPTY EC_SIO E HPRE) as HI0T.
pose proof (l1_pre_cnt B EC_RA EC_EMPTY EC_SIO E HPRE) as HC62.
pose proof (l1_pre_sm B EC_RA EC_EMPTY EC_SIO E HPRE) as HSM.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs0 & _).
assert (HLx : e_n E = Z.of_nat (length (e_x E))) by (unfold e_x, ec_bytes; rewrite length_map; exact HNL).
pose proof (ei_own _ _ _ _ _ _ HIMG) as (Eown & Wown).
pose proof (ei_pst _ _ _ _ _ _ HIMG) as Hpst.
pose proof (ei_pst_w _ _ _ _ _ _ HIMG) as Hpstw.
pose proof (ei_pst_sep _ _ _ _ _ _ HIMG) as Hsep.
set (a0 := @pi_g_own_ran_out PI) in *.
assert (Ha0P : Exists (in_zr a0) PST).
{ unfold prh_pst. do 6 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. rewrite Wown. lia. }
destruct (Hpst a0 Ha0P) as (_ & Hi0). pose proof (pa_segs_low a0 Hi0) as Hlo0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HW0 : writable_at SEGS (mrestrict (w_H W) mem) a0) by (apply l1_writable_any; apply Hpstw; exact Ha0P).
remember (L1_EI regs) as EE eqn:HEE.
assert (HEI : img_env VAL A_LIM EE) by (rewrite HEE; unfold L1_EI; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew EE n = ew (Ereg regs []) n)
  by (intros n Hn0; rewrite HEE; unfold L1_EI; apply Eimg_low; exact Hn0).
assert (U284 : bv_unsigned (ew EE (A_HI 4)) = VAL (A_HI 4)) by (apply HEI; unfold A_HI, A_TEXT, A_LIM; lia).
assert (HS : st_ok_pi SEGS VAL EE ss_l1
  (restrict (w_H W) (@YK11.mkst fy regs (Z_to_bv 64 (BASE + L1_K)) mem (YK11.seg_rom SEGS)))).
{ pose proof HJ as (HAR & _).
  pose proof (l6f_img_bounds (cp := cp) (PA := PA) B ly S [] W mem md a0 HAR Hi0) as Hb0.
  rewrite HEE. apply l1_entry_ok; replace (VAL (A_HI 4) + 1424) with a0 by lia; [exact HW0 | exact Hb0]. }
assert (SHOK : sh_ok SEGS L1_Bx L1_SH EE (mrestrict (w_H W) mem)) by constructor.
assert (PSTOK : forall a, Exists (in_zr a) PST -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B)).
{ intros a Ha. destruct (Hpst a Ha) as ((Hno & _) & Hi). split; [exact Hi | exact Hno]. }
pose (RUN := @paj_run_x_m_invR fy rc SK B_prog_listing PL_102_B PA B PST ARc cf_head
  (l1_LAWS (rc := rc) (cp := cp) (PA := PA) B) PSTOK (YAkMemnorm.memnorm SEGS) (srr_inv_laws_memnorm_k SEGS)
  WLE' (wle'_refl SEGS _) (wle'_trans SEGS _)).
unfold cfg_at. change (w64 EC_S1) with (Z_to_bv 64 (BASE + L1_K)).
clear HEE.
paj_run_tok_x_invR RUN HS HJ SHOK HMN L1_Bspan.
- (* the run's one written byte is g_own_ran_out, a PST cell (ei_own) *)
  intros a (r & Hr & Ha). cbn [ss_mem ss_l1 In] in Hr. destruct Hr as [<- | []].
  cbn [l1_r_own YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U284 in Ha.
  right. replace a with a0 by lia. exact Ha0P.
- (* THE CALL OF fuzz_alloc_ran_out_reset (+0x12c), from the run's stop at its entry *)
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
  prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9.
  prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
  prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  pose proof (st_ok_mem_ok SEGS _ _ _ HS) as HMO. cbn [ss_mem setpc] in HMO.
  destruct Hrk as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R26 & R27).
  assert (E2 : ew EE 2 = getr regs 2)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E3 : ew EE 3 = getr regs 3)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
  assert (E4 : ew EE 4 = getr regs 4)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
  assert (E8 : ew EE 8 = getr regs 8)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
  assert (E9 : ew EE 9 = getr regs 9)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
  assert (E18 : ew EE 18 = getr regs 18)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 18 18%bv eq_refl)).
  assert (E19 : ew EE 19 = getr regs 19)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 19 19%bv eq_refl)).
  assert (E20 : ew EE 20 = getr regs 20)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 20 20%bv eq_refl)).
  assert (E26 : ew EE 26 = getr regs 26)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 26 26%bv eq_refl)).
  assert (E27 : ew EE 27 = getr regs 27)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 27 27%bv eq_refl)).
  assert (E25 : ew EE 284 = w64 (VAL (A_HI 4))).
  { unfold w64. rewrite <- U284. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  rewrite E2, R2 in Q2. rewrite E3 in Q3. rewrite E4 in Q4. rewrite E8, R8 in Q8. rewrite E9, R9 in Q9.
  rewrite E18, R18 in Q18. rewrite E19, R19 in Q19. rewrite E20, R20 in Q20. rewrite E25 in Q25.
  rewrite E26, R26 in Q26. rewrite E27, R27 in Q27.
  destruct HMO as (_ & HMO & _). apply Forall_inv in HMO. destruct HMO as (_ & _ & _ & HCH).
  cbn [YP09.r_chunks YP09.r_base base_val] in HCH. apply Forall_inv in HCH.
  destruct (HCH 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2).
  cbn [YP09.cbyte c_off YP09.c_val] in Hb1, Hb2.
  cbn [ms_mem restrict] in Hb2.
  assert (Ea0 : bv_unsigned (ew EE 284) + 1424 + 0 = a0).
  { change 284%nat with (A_HI 4). rewrite U284. lia. }
  rewrite Ea0 in Hb2.
  (* g_own_ran_out = 0 after the store *)
  assert (HOWN0 : @prh_own rc PI B_prog_listing PA W (ms_mem ms) 0).
  { unfold prh_own. fold a0. split; [|left; reflexivity]. rewrite Wown. intros kk Hkk. replace kk with 0%nat by lia.
    cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite Hb2, <- Hb1. vm_compute. reflexivity. }
  (* every other byte is kept *)
  assert (Hrng : forall a, Exists (in_zr a) PST -> 0 <= a < 2 ^ 64).
  { intros a Ha. destruct (Hpst a Ha) as (_ & Hi). pose proof (pa_segs_low a Hi). lia. }
  assert (NW : forall a, 0 <= a < 2 ^ 64 -> a <> a0 -> ~ in_wrange EE (ss_mem ss_l1) a).
  { intros a Ha Hne (r & Hr & Hra). cbn [ss_mem ss_l1 In] in Hr. destruct Hr as [<- | []].
    cbn [l1_r_own YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra. rewrite U284 in Hra. apply Hne. lia. }
  assert (HKA : forall a, 0 <= a < 2 ^ 64 -> a <> a0 ->
    aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
  { intros a Ha Hne. apply aview_eq_of. apply HFr. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. exact (NW a Ha Hne). }
  assert (HKM : forall a, 0 <= a < 2 ^ 64 -> a <> a0 ->
    mbyte SEGS (mrestrict (w_H W) (ms_mem ms)) a = mbyte SEGS (mrestrict (w_H W) mem) a).
  { intros a Ha Hne. apply (prh_mbyte_of_mrestrict (in_wrange EE (ss_mem ss_l1)));
    [exact HFr | exact Ha | exact (NW a Ha Hne)]. }
  assert (HLED1 : @prh_ledger rc cp PI B_prog_listing PA B ly S [] W (ms_mem ms) [] peak (e_cnt E) SIZE_MAX (e_ran E)
    most0 0).
  { apply (l1_ledger_store B ly S [] W mem (ms_mem ms) peak (e_cnt E) SIZE_MAX (e_ran E) most0 own0 a0 HLED Hsep);
    [| exact Hrng | exact HKM | exact HOWN0].
    unfold in_zr. cbn [fst snd]. rewrite Wown. lia. }
  destruct (l1_inv_store B SK EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG WLE' E fk ly S [] W mem md
    (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md) own [] peak (e_cnt E) (e_ran E) k (e_os E) (e_i0 E) 0%nat []
    a0 HIMG Hinv Hfrm Ha0P HKA HJ Hwb00 (ex_intro _ most0 (ex_intro _ 0 HLED1)) HMN) as (HI1 & HF1).
  (* the stack the call sites may use (et_stk, ei_frame) *)
  pose proof (et_stk _ _ _ _ _ HTX) as Hstk. pose proof (ei_frame _ _ _ _ _ _ HIMG) as Hfr0.
  unfold STK_LLVMFuzzerTestOneInput in Hstk. unfold EC_SAVE in Hfr0.
  assert (STKS : forall s, In s ltac:(lazymatch type of Hstk with _ + zmaxl ?l <= _ => exact l end) ->
    s + 144 <= LLVMF_STK).
  { intros s Hs. pose proof (l6f_zmaxl_in s _ Hs). unfold LLVMF_STK in *. lia. }
  (* the return site +0x130 is a code address below the ceiling *)
  pose proof HJ as (HAR1 & _).
  l6f_fd 304 Hpl304 Hd304.
  pose proof (l6f_slot_img (PA := PA) 304 _ ltac:(lia) Hpl304) as Hi304.
  pose proof (l6f_img_bounds (cp := cp) (PA := PA) B ly S [] W (ms_mem ms) _ (BASE + 304) HAR1 Hi304) as Hb304.
  unfold kImgLo, kImgEnd in Hb304.
  eapply (l1_call_cut B SK EC_RA EC_EMPTY EC_SIO WLE' (wle'_trans SEGS _) fy E fk ly S W (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md)
    own [] peak (e_cnt E) (e_ran E) k (e_os E) (e_i0 E) 0%nat (ms_regs ms) (SIGMA AS_fuzz_alloc_ran_out_reset)
    (BASE + 304)
    STK_fuzz_alloc_ran_out_reset _ _ HI1 HF1 Q2 (eq_trans Q3 R3) (eq_trans Q4 R4) Q8 Q1
    (ret_ok_codeptr_v (PI := PA) 304 ltac:(lia) eq_refl) ltac:(lia) (pi_frame_nonneg _)
    (STKS STK_fuzz_alloc_ran_out_reset ltac:(cbn [In]; IN)) Hfz).
  { intros ch Hsp Hfpre.
    apply (l1_lift_call B SK PST WLE' (wle_wle' SEGS _)).
    exact (et_fuzz_alloc_ran_out_reset _ _ _ _ _ HTX fy ly S [] W (ms_regs ms) (ms_mem ms)
      (with_vm_backing (m_vm_lazy md) mat md) ch [] peak (e_cnt E) SIZE_MAX (e_ran E) most0 0 Hfpre HLED1). }
  intros W2 ly2 S2 Hp2 regs2 mem2 md2 k1 WS2 Hwle Hwb2 HJ2 HJ1 HP2 (HQ & HQmn).
  destruct HQ as (Hrl2 & EHp2 & ES2 & Eab2 & HLED2). subst Hp2 S2.
  pose proof (l1_inv_after B SK EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG WLE' E fk ly S [] W (ms_mem ms)
    (with_vm_backing (m_vm_lazy md) mat md) own [] peak (e_cnt E) (e_ran E) k (e_os E) (e_i0 E) 0%nat
    STK_fuzz_alloc_ran_out_reset (e_B E)
    ly2 S [] W2 mem2 md2 k1 (k + k1) [] peak (e_cnt E) 0 (e_os E) (e_i0 E) 0%nat [] WS2 HIMG HI1 HJ2 Hwb2 HJ1
    (ex_intro _ most0 (ex_intro _ 0 HLED2)) (Hrl2 HRL) HRP
    ltac:(unfold LCNT; lia) ltac:(rewrite Eab2; exact HPERM) (HQmn HMN)) as HI2.
  pose proof (l1_frame_keep B SK EC_RA EC_EMPTY EC_SIO WLE' E fk ly S [] W (ms_mem ms)
    (with_vm_backing (m_vm_lazy md) mat md) own [] peak (e_cnt E) (e_ran E) k (e_os E) (e_i0 E) 0%nat
    STK_fuzz_alloc_ran_out_reset (e_B E) ly2 S [] W2 mem2 md2 k1 [] HI1 HJ1 ltac:(lia) HF1) as HF2.
  pose proof HI2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMN2).
  (* the callee-saved registers across the call *)
  assert (P2 : getr regs2 2 = w64 (e_B E)) by (rewrite (l6f_pres _ _ 2%bv HP2 ltac:(l6f_cs)); exact Q2).
  assert (P3 : getr regs2 3 = getr (e_regs E) 3)
    by (rewrite (l6f_pres _ _ 3%bv HP2 ltac:(l6f_cs)); exact (eq_trans Q3 R3)).
  assert (P4 : getr regs2 4 = getr (e_regs E) 4)
    by (rewrite (l6f_pres _ _ 4%bv HP2 ltac:(l6f_cs)); exact (eq_trans Q4 R4)).
  assert (P8 : getr regs2 8 = w64 (e_sp0 E)) by (rewrite (l6f_pres _ _ 8%bv HP2 ltac:(l6f_cs)); exact Q8).
  assert (P9 : getr regs2 9 = w64 (e_B E)) by (rewrite (l6f_pres _ _ 9%bv HP2 ltac:(l6f_cs)); exact Q9).
  assert (P18 : getr regs2 18 = w64 fk) by (rewrite (l6f_pres _ _ 18%bv HP2 ltac:(l6f_cs)); exact Q18).
  assert (P19 : getr regs2 19 = w64 (e_n E)) by (rewrite (l6f_pres _ _ 19%bv HP2 ltac:(l6f_cs)); exact Q19).
  assert (P20 : getr regs2 20 = w64 (e_p E)) by (rewrite (l6f_pres _ _ 20%bv HP2 ltac:(l6f_cs)); exact Q20).
  assert (P25 : getr regs2 25 = w64 (VAL (A_HI 4))) by (rewrite (l6f_pres _ _ 25%bv HP2 ltac:(l6f_cs)); exact Q25).
  assert (P26 : getr regs2 26 = w64 (shadow_addr fk)) by (rewrite (l6f_pres _ _ 26%bv HP2 ltac:(l6f_cs)); exact Q26).
  assert (P27 : getr regs2 27 = w64 fk) by (rewrite (l6f_pres _ _ 27%bv HP2 ltac:(l6f_cs)); exact Q27).
  clear Q1 Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q20 Q25 Q26 Q27.
  (* +0x130 slli a0,s3,8; +0x134 lui a1,5; +0x138 add a0,a0,a1: a0 = PJ_ALLOC_BOUND n *)
  eapply (l1_step_genR (fx := fy) WLE' W2 regs2 _ mem2 md2 _ 304); [lia | |].
  { intros m. exact (step_slli_at (fx := fy) SEGS regs2 (Z_to_bv 64 (BASE + 304)) m (YK11.seg_rom SEGS) _ _ _ _ _
      (pa_fetch_pw (PL := PL_102_B) (PI := PA) 304 _ Hpl304) (not_ecall_of_decode _ _ _ Hd304 ltac:(discriminate))
      Hd304 eq_refl eq_refl). }
  intros X1.
  l6f_fd 308 Hpl308 Hd308.
  eapply (l1_step_genR (fx := fy) WLE' W2 _ _ mem2 _ _ 308); [lia | |].
  { intros m. exact (step_lui_at (fx := fy) SEGS _ (Z_to_bv 64 (BASE + 308)) m (YK11.seg_rom SEGS) _ _ _ _
      (pa_fetch_pw (PL := PL_102_B) (PI := PA) 308 _ Hpl308) (not_ecall_of_decode _ _ _ Hd308 ltac:(discriminate))
      Hd308 eq_refl eq_refl). }
  intros X2.
  l6f_fd 312 Hpl312 Hd312.
  eapply (l1_step_genR (fx := fy) WLE' W2 _ _ mem2 _ _ 312); [lia | |].
  { intros m. exact (step_add_at (fx := fy) SEGS _ (Z_to_bv 64 (BASE + 312)) m (YK11.seg_rom SEGS) _ _ _ _ _
      (pa_fetch_pw (PL := PL_102_B) (PI := PA) 312 _ Hpl312) (not_ecall_of_decode _ _ _ Hd312 ltac:(discriminate))
      Hd312 eq_refl eq_refl). }
  intros X3.
  l6f_fdc 316 Hpl316.
  eapply (l6f_step_callR (fx := fy) WLE' W2 _ mem2 _ _ (312 + 4) AS_fuzz_alloc_most _ _ ltac:(lia) Hpl316 eq_refl).
  intros X4.
  (* THE CALL OF fuzz_alloc_most (PJ_ALLOC_BOUND n) at +0x13c *)
  match goal with |- SRrG _ _ _ (mkCfg (@YK11.mkst _ ?r _ _ _) ?d) _ => set (regs3 := r); set (md3 := d) end.
  set (n' := PJ_ALLOC_BOUND (e_n E)).
  assert (Hn0 : 0 <= e_n E) by (rewrite HNL; lia).
  assert (HA0 : getr regs3 10 = w64 n').
  { unfold regs3. l1_gr. rewrite (l1_getr_num regs2 _ (19%bv : bv 5)) by (vm_compute; reflexivity). rewrite P19.
    match goal with |- context [v_slli _ (bv_unsigned ?s)] =>
      replace (bv_unsigned s) with 8 by (vm_compute; reflexivity) end.
    match goal with |- context [Z.shiftl (bv_signed ?s) 12] =>
      replace (Z.shiftl (bv_signed s) 12) with 20480 by (vm_compute; reflexivity) end.
    unfold v_add, v_slli, v_lui.
    rewrite (l1_w64u (e_n E)) by (unfold EC_NMAX in Hn; lia).
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
    rewrite !unsigned_lit_small by (unfold EC_NMAX in Hn; lia).
    unfold n', PJ_ALLOC_BOUND, w64. f_equal. lia. }
  pose proof (l1_inv_mat B SK EC_RA EC_EMPTY EC_SIO WLE' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1 HI2) as HI2a.
  pose proof (l1_inv_mat B SK EC_RA EC_EMPTY EC_SIO WLE' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X2 HI2a) as HI2b.
  pose proof (l1_inv_mat B SK EC_RA EC_EMPTY EC_SIO WLE' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X3 HI2b) as HI2c.
  pose proof (l1_inv_mat B SK EC_RA EC_EMPTY EC_SIO WLE' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X4 HI2c) as HI2d.
  pose proof HI2d as ((WS2d & HJ2d & _) & _).
  pose proof HJ2d as (HAR2 & _).
  l6f_fd 320 Hpl320 Hd320.
  pose proof (l6f_slot_img (PA := PA) 320 _ ltac:(lia) Hpl320) as Hi320.
  pose proof (l6f_img_bounds (cp := cp) (PA := PA) B ly2 S [] W2 mem2 _ (BASE + 320) HAR2 Hi320) as Hb320.
  unfold kImgLo, kImgEnd in Hb320.
  eapply (l1_call_cut B SK EC_RA EC_EMPTY EC_SIO WLE' (wle'_trans SEGS _) fy E fk ly2 S W2 mem2 md3 own [] peak (e_cnt E) 0 (k + k1)
    (e_os E) (e_i0 E) 0%nat regs3
    (SIGMA AS_fuzz_alloc_most) (BASE + 320) STK_fuzz_alloc_most _ _ HI2d HF2).
  { unfold regs3. l1_gr. exact P2. }
  { unfold regs3. l1_gr. exact P3. }
  { unfold regs3. l1_gr. exact P4. }
  { unfold regs3. l1_gr. exact P8. }
  { unfold regs3. l1_gr. reflexivity. }
  { exact (ret_ok_codeptr_v (PI := PA) 320 ltac:(lia) eq_refl). }
  { lia. }
  { apply pi_frame_nonneg. }
  { exact (STKS STK_fuzz_alloc_most ltac:(cbn [In]; IN)). }
  { exact Hfz. }
  { intros ch Hsp Hfpre.
    apply (l1_lift_call B SK PST WLE' (wle_wle' SEGS _)).
    exact (et_fuzz_alloc_most _ _ _ _ _ HTX fy ly2 S [] W2 regs3 mem2 md3 ch n' [] peak (e_cnt E) SIZE_MAX 0 most0 0
      Hfpre HA0 ltac:(unfold n', PJ_ALLOC_BOUND; unfold EC_NMAX in Hn; lia) HLED2). }
  intros W3 ly3 S3 Hp3 regs4 mem3 md4 k2 WS3 Hwle3 Hwb3 HJ3 HJ3c HP3 (HQ3 & HQmn3).
  destruct HQ3 as (Hrl3 & EHp3 & ES3 & Eab3 & HLED3). subst Hp3 S3.
  pose proof (l1_inv_after B SK EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG WLE' E fk ly2 S [] W2 mem2 md3 own []
    peak (e_cnt E) 0 (k + k1) (e_os E) (e_i0 E) 0%nat STK_fuzz_alloc_most (e_B E) ly3 S [] W3 mem3 md4 k2 (k + k1 + k2)
    [] peak (e_cnt E) 0 (e_os E) (e_i0 E) 0%nat [] WS3 HIMG HI2d HJ3 Hwb3 HJ3c (ex_intro _ n' (ex_intro _ 0 HLED3)) (Hrl3 HRL) HRP
    ltac:(unfold LCNT; lia)
    ltac:(rewrite Eab3, Eab2; exact HPERM) (HQmn3 HMN2)) as HI3.
  pose proof (l1_frame_keep B SK EC_RA EC_EMPTY EC_SIO WLE' E fk ly2 S [] W2 mem2 md3 own [] peak (e_cnt E) 0 (k + k1)
    (e_os E) (e_i0 E) 0%nat STK_fuzz_alloc_most (e_B E) ly3 S [] W3 mem3 md4 k2 [] HI2d HJ3c ltac:(lia) HF2) as HF3.
  pose proof HI3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMN3).
  assert (KR3 : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs4 r = getr regs3 r)
    by (intros r Hr; exact (l6f_pres _ _ r HP3 Hr)).
  assert (T2 : getr regs4 2 = w64 (e_B E)) by (rewrite (KR3 2%bv ltac:(l6f_cs)); unfold regs3; l1_gr; exact P2).
  assert (T3 : getr regs4 3 = getr (e_regs E) 3) by (rewrite (KR3 3%bv ltac:(l6f_cs)); unfold regs3; l1_gr; exact P3).
  assert (T4 : getr regs4 4 = getr (e_regs E) 4) by (rewrite (KR3 4%bv ltac:(l6f_cs)); unfold regs3; l1_gr; exact P4).
  assert (T8 : getr regs4 8 = w64 (e_sp0 E)) by (rewrite (KR3 8%bv ltac:(l6f_cs)); unfold regs3; l1_gr; exact P8).
  assert (T9 : getr regs4 9 = w64 (e_B E)) by (rewrite (KR3 9%bv ltac:(l6f_cs)); unfold regs3; l1_gr; exact P9).
  assert (T18 : getr regs4 18 = w64 fk) by (rewrite (KR3 18%bv ltac:(l6f_cs)); unfold regs3; l1_gr; exact P18).
  assert (T19 : getr regs4 19 = w64 (e_n E)) by (rewrite (KR3 19%bv ltac:(l6f_cs)); unfold regs3; l1_gr; exact P19).
  assert (T20 : getr regs4 20 = w64 (e_p E)) by (rewrite (KR3 20%bv ltac:(l6f_cs)); unfold regs3; l1_gr; exact P20).
  assert (T25 : getr regs4 25 = w64 (VAL (A_HI 4)))
    by (rewrite (KR3 25%bv ltac:(l6f_cs)); unfold regs3; l1_gr; exact P25).
  assert (T26 : getr regs4 26 = w64 (shadow_addr fk))
    by (rewrite (KR3 26%bv ltac:(l6f_cs)); unfold regs3; l1_gr; exact P26).
  assert (T27 : getr regs4 27 = w64 fk) by (rewrite (KR3 27%bv ltac:(l6f_cs)); unfold regs3; l1_gr; exact P27).
  clearbody regs3 md3.
  (* +0x140 mv a0,s4; +0x144 mv a1,s3 *)
  eapply (l1_step_genR (fx := fy) WLE' W3 regs4 _ mem3 md4 _ 320); [lia | |].
  { intros m. exact (step_addi_at (fx := fy) SEGS regs4 (Z_to_bv 64 (BASE + 320)) m (YK11.seg_rom SEGS) _ _ _ _ _
      (pa_fetch_pw (PL := PL_102_B) (PI := PA) 320 _ Hpl320) (not_ecall_of_decode _ _ _ Hd320 ltac:(discriminate))
      Hd320 eq_refl eq_refl). }
  intros Y1.
  l6f_fd 324 Hpl324 Hd324.
  eapply (l1_step_genR (fx := fy) WLE' W3 _ _ mem3 _ _ 324); [lia | |].
  { intros m. exact (step_addi_at (fx := fy) SEGS _ (Z_to_bv 64 (BASE + 324)) m (YK11.seg_rom SEGS) _ _ _ _ _
      (pa_fetch_pw (PL := PL_102_B) (PI := PA) 324 _ Hpl324) (not_ecall_of_decode _ _ _ Hd324 ltac:(discriminate))
      Hd324 eq_refl eq_refl). }
  intros Y2.
  l6f_fdc 328 Hpl328.
  eapply (l6f_step_callR (fx := fy) WLE' W3 _ mem3 _ _ (324 + 4) AS_check_no_overread _ _ ltac:(lia) Hpl328 eq_refl).
  intros Y3.
  (* THE CALL OF check_no_overread (p, n) at +0x148 *)
  match goal with |- SRrG _ _ _ (mkCfg (@YK11.mkst _ ?r _ _ _) ?d) _ => set (regs5 := r); set (md5 := d) end.
  pose proof (l1_inv_mat B SK EC_RA EC_EMPTY EC_SIO WLE' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Y1 HI3) as HI3a.
  pose proof (l1_inv_mat B SK EC_RA EC_EMPTY EC_SIO WLE' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Y2 HI3a) as HI3b.
  pose proof (l1_inv_mat B SK EC_RA EC_EMPTY EC_SIO WLE' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Y3 HI3b) as HI3c.
  pose proof HI3c as ((WS3c & HJ3d & Hwb3c) & _ & _ & _ & _ & _ & HRPc & _).
  pose proof HJ3d as (HAR3 & _).
  l6f_fd 332 Hpl332 Hd332.
  pose proof (l6f_slot_img (PA := PA) 332 _ ltac:(lia) Hpl332) as Hi332.
  pose proof (l6f_img_bounds (cp := cp) (PA := PA) B ly3 S [] W3 mem3 _ (BASE + 332) HAR3 Hi332) as Hb332.
  unfold kImgLo, kImgEnd in Hb332.
  assert (Hlen : Z.of_nat (length (e_x E)) <= EC_NMAX) by lia.
  assert (HSRC : src_rd W3 mem3 (e_p E) (e_x E) /\ (0 < Z.of_nat (length (e_x E)) ->
     PRH_FnReader.prhReader_home B ly3 S [] [] (e_p E) (Z.of_nat (length (e_x E))))).
  { destruct HPN as [(Hz & Hp0) | (Hpos & _)].
    - split; [|intros; lia]. eapply l1_src_empty; [exact HIMG | exact Hp0 | lia].
    - destruct (ec_src_home_cutR (fx := fx) (cp := cp) (PI := PI) (RL := RL) B SK EC_RA EC_EMPTY EC_SIO WLE' E fk ly3 S []
        W3 mem3 _ own [] peak (e_cnt E) 0 _ _ _ _ HI3c (proj1 Hpos)) as (Hs & Hh).
      split; [exact Hs|]. intros _. rewrite <- HLx. exact Hh. }
  destruct HRPc as (hist0 & Hroom0).
  assert (Hraz : raZ regs5 = @EC_AR_CNO rc B_prog_listing PA).
  { unfold raZ, regs5. l1_gr. rewrite unsigned_lit_small by lia. reflexivity. }
  assert (Hcap : 1 <= ck_FRAMES_CAP - FR_check_no_overread) by (vm_compute; let Hx := fresh in intro Hx; discriminate Hx).
  eapply (l1_call_cutF B SK EC_RA EC_EMPTY EC_SIO WLE' (wle'_trans SEGS _) fy E fk ly3 S W3 mem3 md5 own [] peak (e_cnt E) 0 (k + k1 + k2)
    (e_os E) (e_i0 E) 0%nat regs5
    (SIGMA AS_check_no_overread) (BASE + 332) STK_check_no_overread _ _ _ HI3c HF3).
  { unfold regs5. l1_gr. exact T2. }
  { unfold regs5. l1_gr. exact T3. }
  { unfold regs5. l1_gr. exact T4. }
  { unfold regs5. l1_gr. exact T8. }
  { unfold regs5. l1_gr. reflexivity. }
  { exact (ret_ok_codeptr_v (PI := PA) 332 ltac:(lia) eq_refl). }
  { lia. }
  { unfold STK_check_no_overread. pose proof (pi_frame_nonneg F_check_no_overread).
    match goal with |- 0 <= _ + zmaxl ?l => pose proof (l6f_zmaxl_nonneg l) end. lia. }
  { exact (STKS STK_check_no_overread ltac:(cbn [In]; IN)). }
  { exact Hfz. }
  { intros ch Hsp Hfpre.
    (* check_no_overread's granted form, DERIVED from the batch kit's text (ec_texts) by Ent102OfPost.v's bridge; it concludes
       SRr' segs RZ_cf, the lane's own relation *)
    eapply (tcheck_no_overread_grantedX_of_post (fx := fy) (L := B_prog_listing) (PA := PA) B ARc SK (ec_ctx0 EC_RA)
      (et_check_no_overread _ _ _ _ _ HTX fy) (e_sm E) (e_x E) (e_os E) (e_i0 E) (e_H0 E) hist0 ly3 S [] W3 regs5 mem3
      md5 ch (e_p E) (e_x E) [] peak (e_cnt E) 0 n').
    - exact HSM.
    - exact Hfpre.
    - exact HMN3.
    - apply eu_cno in HUN. exact HUN.
    - rewrite Hraz. eapply ec_ctx_call_img; [exact HIMG | cbn [ec_call_rets In]; IN | exact Hsp].
    - unfold regs5. l1_gr. rewrite l1_addi0 by (vm_compute; reflexivity). exact T20.
    - unfold regs5. l1_gr. rewrite l1_addi0 by (vm_compute; reflexivity).
      rewrite (l1_getr_num regs4 _ (19%bv : bv 5)) by (vm_compute; reflexivity). rewrite T19, HLx. reflexivity.
    - rewrite <- HLx. unfold EC_NMAX in Hn. lia.
    - exact (proj1 HSRC).
    - exact (proj2 HSRC).
    - exact HLED3.
    - unfold LCNT in HC62. lia.
    - reflexivity.
    - rewrite ec_rq_pj_parse. pose proof (PjReqBoundW.rq_read_bound prh_jr_strtod (e_x E)) as Hq.
      unfold n', PJ_ALLOC_BOUND. rewrite HLx. lia.
    - pose proof (ecov_cno _ _ HPAY E Hlen) as Hcov. lia.
    - pose proof (ei_malloc_max _ _ _ _ _ _ HIMG) as Hmm. pose proof cf_head_nonneg as Hch.
      unfold PRH_FnWriter.prhWriter_WMAX in Hmm. rewrite <- HLx. unfold EC_NMAX in Hn. lia.
    - pose proof (ei_malloc_max _ _ _ _ _ _ HIMG) as Hmm. unfold PRH_FnWriter.prhWriter_WMAX in Hmm.
      rewrite ec_rq_pj_parse. pose proof (PjReqBoundW.rq_read_bound_56 prh_jr_strtod (e_x E)) as Hq.
      rewrite <- HLx in Hq. unfold EC_NMAX in Hn. lia.
    - destruct HOWN as (pos & Hown & _). rewrite Hfrs0, Hown, HFR0. cbn [length app Z.of_nat]. lia.
    - exact HRL.
    - exact Hroom0.
    - (* the run of the whole call, for every triple, BY CONSTRUCTION (Ent102PosB.v ec_supply_run) at the entry index
         ec_pre ties to the earlier calls' events *)
      intros o1 o2 o0. rewrite HI0T. apply ec_supply_run.
    - (* rp_x = x: the run's bytes are the call's, e_x E both *)
      reflexivity.
    - (* R1: the entry position is the call boundary, ec_pre's e_i0 tie *)
      exact HI0T.
    - exact Hfz.
    - (* The batch kit's wild room at the call: ec_pre's entry room across the journal so far, at cut_s1's spent budget 0 (the
         two accessors store no wild trace) *)
      eapply (ec_room_atR (fx := fx)); [exact HPRE | exact HJ3d | exact Hwb3c |].
      apply Nat.leb_le. vm_compute. reflexivity.
    - (* THE HULL BUDGET at the call (route (b)): the cut file's ech_hull_pay at the cut's position, with ec_pre's
         length (e_os E) <= 3 (Ent102L1BHelp.v l1_cno_hull) *)
      rewrite HSM in Hroom0.
      apply (l1_cno_hull (cp := cp) (ech_hull_pay _ _ _ _ _ _ _ _ _ _ HYP) ReaderRes.jr_strtod (e_x E) (e_os E)
        (e_i0 E) (e_H0 E) hist0 S); [| exact Hroom0 |].
      + clear - HPRE. unfold ec_pre in HPRE. ec_conj_pick HPRE.
      + clear - Hlen. apply Z.ltb_ge. unfold PresetReqAt.MAXB, EC_NMAX in *. lia. }
  intros fx' W4 ly4 S4 Hp4 regs6 mem4 md6 k3 WS4 WS41 Hwle4 HFZ4 HFK4 Hwb4 Hpw4 HJ4 HJ4c HP4 (HQ4 & HQmn4).
  (* cut_cno's spent budget: cut_s1's 0 plus check_no_overread's prh_wk (its budgeted post) *)
  assert (Hwb4' : YCbqGwild.wbudget [] ec_wk_cno (WS4 ++ WS41))
    by exact (YCbqGwild.wbudget_app [] 0 (prh_wk F_check_no_overread) WS4 WS41 Hwb4 Hpw4).
  destruct HQ4 as (Hrl4 & Lam4 & peak4 & cnt4 & ran4 & own4 & HPL4 & HPB4 & _ & Hcnt4 & HLED4 & _ & r4 & Hr4 &
    Hown40 & Harms & Hexact).
  (* the granted form: the padded copies were granted (own' = 0), so the triple, the exact advance and the tie hold *)
  destruct (Hexact Hown40) as (o1 & o2 & o0 & (hist4 & Hroom4) & Htie4). subst own4.
  assert (EL4 : Lam4 = []) by (apply Permutation_nil; apply Permutation_sym; exact HPL4). subst Lam4.
  pose proof (PRH_Base.prh_ledger_heads B ly4 S4 Hp4 W4 mem4 [] peak4 cnt4 SIZE_MAXZ ran4 n' 0 HLED4) as HH4.
  cbn [map] in HH4.
  assert (EH4 : Hp4 = []) by (apply Permutation_nil; apply Permutation_sym; exact HH4). subst Hp4.
  pose proof (epay_cno _ _ HPAY E Hlen) as (Hpay1 & Hpay2).
  pose proof (HCC E 2%nat 2%nat) as ((Hcc2 & _) & _).
  assert (HPB4' : Permutation (ablocks B ly4 S4) (ablocks B ly S)).
  { eapply Permutation_trans; [exact HPB4|]. rewrite Eab3, Eab2. apply Permutation_refl. }
  (* the room position after check_no_overread (the post's advanced position, at least the entry's) *)
  assert (HRP4 : exists hist, PresetRoomPos.iface_room_pos (e_sm E) (e_x E) (e_os E ++ [(o1, o2, o0)])
    (e_i0 E + length (ec_cno_evs E (o1, o2, o0)))%nat (e_H0 E) hist S4).
  { exists hist4. rewrite l1_cno_evs_ec. exact Hroom4. }
  (* the return tie of cut_cno: the provisional exact text's return condition, at the run's bytes and oracle *)
  assert (HTIE : r4 = 1 <-> ec_ranout E (o1, o2, o0) = true) by exact Htie4.
  assert (HC4 : e_cnt E <= cnt4 <= e_cnt E + LCNT) by (unfold LCNT in *; lia).
  assert (HP4E : Permutation (ablocks B ly4 S4) (ck_hblks [] ++ ablocks B (e_ly E) (e_S E)))
    by (eapply Permutation_trans; [exact HPB4' | exact HPERM]).
  pose proof (l1_inv_after B SK EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG WLE' E fk ly3 S [] W3 mem3 md5 own []
    peak (e_cnt E) 0 (k + k1 + k2) (e_os E) (e_i0 E) 0%nat STK_check_no_overread (e_B E) ly4 S4 [] W4 mem4 md6 k3
    (k + k1 + k2 + k3) [] peak4 cnt4 ran4 (e_os E ++ [(o1, o2, o0)]) (e_i0 E + length (ec_cno_evs E (o1, o2, o0)))%nat
    ec_wk_cno WS41 (WS4 ++ WS41) HIMG HI3c HJ4 Hwb4' HJ4c (ex_intro _ n' (ex_intro _ 0 HLED4)) Hrl4 HRP4 HC4 HP4E (HQmn4 HMN3)) as HI4.
  pose proof (l1_frame_keep B SK EC_RA EC_EMPTY EC_SIO WLE' E fk ly3 S [] W3 mem3 md5 own [] peak (e_cnt E) 0 (k + k1 + k2)
    (e_os E) (e_i0 E) 0%nat STK_check_no_overread (e_B E) ly4 S4 [] W4 mem4 md6 k3 WS41 HI3c HJ4c ltac:(lia) HF3) as HF4.
  assert (KR4 : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs6 r = getr regs5 r)
    by (intros r Hr; exact (l6f_pres _ _ r HP4 Hr)).
  apply (SRr'_ret SEGS (@YGcfRehidePost.RZ_cf rc)).
  exists ly4, S4, [], regs6, mem4, md6, own, peak4, cnt4, ran4, (k + k1 + k2 + k3), r4, (o1, o2, o0).
  split.
  { exists fx'. split; [exact HFZ4|]. split; [exact (l1_fk_trans _ _ _ Hkept HFK4)|]. reflexivity. }
  split; [exact HI4|]. split; [reflexivity|]. split; [exact HTIE|].
  split; [unfold LCNT in *; lia|].
  split; [rewrite (KR4 25%bv ltac:(l6f_cs)); unfold regs5; l1_gr; exact T25|].
  split; [rewrite (l1_bb_perm B ly4 S4 ly S HPB4'); lia|].
  split.
  { unfold ec_rk.
    split; [rewrite (KR4 2%bv ltac:(l6f_cs)); unfold regs5; l1_gr; exact T2|].
    split; [rewrite (KR4 3%bv ltac:(l6f_cs)); unfold regs5; l1_gr; exact T3|].
    split; [rewrite (KR4 4%bv ltac:(l6f_cs)); unfold regs5; l1_gr; exact T4|].
    split; [rewrite (KR4 8%bv ltac:(l6f_cs)); unfold regs5; l1_gr; exact T8|].
    split; [rewrite (KR4 9%bv ltac:(l6f_cs)); unfold regs5; l1_gr; exact T9|].
    split; [rewrite (KR4 18%bv ltac:(l6f_cs)); unfold regs5; l1_gr; exact T18|].
    split; [rewrite (KR4 19%bv ltac:(l6f_cs)); unfold regs5; l1_gr; exact T19|].
    split; [rewrite (KR4 20%bv ltac:(l6f_cs)); unfold regs5; l1_gr; exact T20|].
    split; [rewrite (KR4 26%bv ltac:(l6f_cs)); unfold regs5; l1_gr; exact T26|].
    rewrite (KR4 27%bv ltac:(l6f_cs)); unfold regs5; l1_gr; exact T27. }
  (* g_most and g_own_ran_out after check_no_overread: the ledger's two #102 fields *)
  split; [exact HF4|]. split; [exact Hn|].
  split; [exact (PRH_Base.prh_ledger_most B ly4 S4 [] W4 mem4 [] peak4 cnt4 SIZE_MAXZ ran4 n' 0 HLED4)|].
  split; [exact Hr4|].
  exists 0. split; [exact (PRH_Base.prh_ledger_own B ly4 S4 [] W4 mem4 [] peak4 cnt4 SIZE_MAXZ ran4 n' 0 HLED4)|].
  destruct Harms as [(Er & Era) | (Er & Era)]; [left; split; [exact Er | right; exact Era] |
    right; split; [exact Er | split; [reflexivity | exact Era]]].
Qed.

End L1.
