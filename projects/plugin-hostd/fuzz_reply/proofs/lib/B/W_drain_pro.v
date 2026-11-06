(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: SEGMENT PRO of the ASan+UBSan walk (image B, fuzz_reply.asan-ubsan) of
   fuzz_reply's drain, 0x83278 .. 0x833bc (82 instructions, no call), from drain's entry to the outer loop's head
   DI 0x833c0.  The statement is lib/B/W_drain_cx.v dr_pro_stmt (FROZEN; this file adds no Section line to its
   header).  Proves no function (kind: segment lemma).
   DONORS (structure only; every number below is read from image B's own code, lib/B/W_listing.v slots 973 ..
   1054, and from lib/B/W_drain_cx.v / W_contract.v / W_kit.v / W_rep.v):
     1. lib/A/W_drain_pro.v of a working branch d15c44876c2 (commit 967069a33f7): the same segment in
        the same framework on image A (0x830dc .. 0x831f4): one entry state, the runner, the frame slots, the
        representations moved across the stores, the model at round 0.
     2. A working branch af5710f6d79 lib/B/Prog/drain_p_entry_step.v: a B prologue walk of the same
        machine code in the old framework (rsegs / munch); it does not transport, read for the code's shape only.

   B's prologue (fuzz_reply.asan-ubsan, sha256 10ffb5f9..): addi sp,sp,-352; the 13 callee-saved registers at
   248(sp) .. 344(sp) [s11; s10; ..; s0; ra] (W_drain_cx.v DR_SAVED / DR_SAVE_OFF); mv s5,a0 (SA, the relay
   entry s); andi a0,a0,7; bnez a0 -> 0x84004 (the ONE trap site of the stage, UBSan ALIGN8 on SA); then
   s11 / s6 / s4 / s8 = SA + 32 / 24 / 16 / 8, g_s by PAddHi (A_OBJ 19) into s0 with g_s >> 3 in s1 and
   (g_s + 4) >> 3 in s2, s10 = 384, the shadow base from the GOT (A_OBJ 0 -> A_OBJ 30), and the 23 one-time
   frame slots of dr_frame.  No call, no shadow check, no store outside [sp0 - 352, sp0).

   TRAP 0x832b8 (W_drain_cx.v census row PRO, FINDING 1): the entry state seats atom 10 (SA) with R1's range
   [4096, 140737479966720] (lib/B/W_traps.v seat recipe) and al2 0, so the runner stops at the `bnez`; the trap
   edge is refuted by lib/B/W_traps.v trap_align8 from DBASE's `dxSA cx mod 8 = 0`.  Every representation the
   outer loop's head carries lies below alloc_ceiling + 8 (a live block, the image band) and moves across the
   stores into the frame. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep gestures_end_b_c RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
send_line_c send_line_b_c RelayRunT RelayRunF ListTr drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_model.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_sites W_contract W_frame W_drain_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_traps.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AERRNO : aerrno_realizes B (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM SEGS B 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes B (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes B (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes B (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes B (SIGMA WS_strlen).
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HERRAL : as_errno B mod 4 = 0.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 19) = rg_s RG.
Hypothesis HLIT5 : dlit_at B 18 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at B 20 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at B 21 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 18), VAL (A_OBJ 18) + 14); (VAL (A_OBJ 20), VAL (A_OBJ 20) + 6); (VAL (A_OBJ 21), VAL (A_OBJ 21) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HSD : 0x10000 <= rg_send_dead RG /\ rg_send_dead RG + 1 <= IMG_TOP.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= IMG_TOP.
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c SEGS B MT MMAX CTX_R (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule_c SEGS B MT CTX_F.
Hypothesis ASTRNDUP : astrndup_cf_rule_c SEGS B MT MMAX CTX_S (SIGMA WS_strndup).
Hypothesis HCTX_re1 : In [BASE + AF_fr_drain + 0x19c] CTX_R.
Hypothesis HCTX_re2 : In [BASE + AF_fr_drain + 0x974] CTX_R.
Hypothesis HCTX_fr2 : In [BASE + AF_fr_drain + 0xa58] CTX_F.
Hypothesis HCTX_sd : In [BASE + AF_fr_drain + 0x994] CTX_S.
Hypothesis HCTX_ld : In [BASE + AF_fr_list_drop + 0x9c] CTX_F.
Let RUN := paj_run_x B LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.

Ltac pro_in := repeat (first [left; reflexivity | right]).

(* ---- The entry state at drain (0x83278).  Atom 10 = SA (R1's range, al2 0: the runner stops at the ALIGN8
   trap 0x832b8, which trap_align8 refutes); atom 32 = the shadow base SB. ---- *)
Definition pro_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition BxP : sv := SOff 32 0.
Definition pro_regions : smem := [ stack_region DRAIN_FRAME; got_regionP; bcell_regionP 32 ].
Definition pro_facts : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 140737479966720 0); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_pro : sstate := mkSS A_drain sr_atoms pro_regions None pro_facts.
Definition pro_extra : list word := map (Z_to_bv 64) [SB].

(* The table block holds the entry, so the entry pointer is a live address below the ASan user ceiling. *)
Lemma pro_SA_range : forall cx, DBASE B MT MMAX RG cx ->
4096 <= dxSA cx /\ dxSA cx + AENT <= alloc_ceiling /\ dxSA cx + AENT <= 140737479966720.
Proof.
intros cx HB.
pose proof HB as (HPRE & _ & HGin & HGle & HSAle & _).
pose proof HPRE as (HAR & _).
destruct (al_blocks SEGS B LAWS (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) (dxG cx) ATABLE HAR HGin)
  as (_ & H4096 & Hceil & _).
pose proof (@YM05.alloc_ceiling_value rc) as (ACV & _).
assert (RQ : req_size ATABLE = 896) by (vm_compute; reflexivity).
rewrite RQ in Hceil. unfold ATABLE in HSAle. lia.
Qed.

Lemma pro_entry_state : forall cx, DBASE B MT MMAX RG cx ->
st_ok_pi SEGS VAL (Eimg (Ereg (dxregs cx) pro_extra)) ss_pro
(restrict (w_H (dxW cx)) (mkst (dxregs cx) (Z_to_bv 64 (BASE + A_drain)) (dxmem cx) (seg_rom SEGS))).
Proof.
intros cx HB.
pose proof HB as (HPRE & HSA & _).
destruct (pro_SA_range cx HB) as (HSAlo & HSAhi & HSAr1).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : DRAIN_STK = 16880) by reflexivity.
destruct (al_const _ _ LAWS (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg (dxregs cx) pro_extra)). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr (dxregs cx) 2)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat (dxregs cx) _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = getr (dxregs cx) 10)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat (dxregs cx) _ 10 10%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra (dxregs cx) _ 0)).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO30 : ew E (A_OBJ 30) = Z_to_bv 64 (VAL (A_OBJ 30)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pa_obj_img 30 ltac:(lia)) as HcellR.
pose proof (pal_got_cell B TL) as HgcD.
assert (Usp : bv_unsigned (ew E 2) = spZ (dxregs cx)) by (rewrite E2; reflexivity).
assert (Usa : bv_unsigned (ew E 10) = dxSA cx)
  by (rewrite E10, HSA; apply unsigned_lit_small; unfold AENT in *; lia).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
unfold ss_pro. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold pro_regions, stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. unfold DRAIN_FRAME. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30)));
    [cbn [sv_denot]; rewrite EO30, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | pose proof (pa_val_range (A_OBJ 30)); zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H (dxW cx)) (dxmem cx) _ _ Kgot).
  + rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) EO30) by (pose proof (pa_val_range (A_OBJ 30)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 30)) 0 8 BxP SB);
    [cbn [sv_denot BxP]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H (dxW cx)) (dxmem cx) _ _ Kcell).
- apply pairwise_disjoint_of_extents. unfold pro_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) EO30) by (pose proof (pa_val_range (A_OBJ 30)); lia).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold DRAIN_FRAME.
  revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgotR HgcD. clear. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [pro_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, Usa, E32, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0 HSAlo HSAhi HSAr1. clear.
  unfold SB, AENT. intros.
  repeat match goal with |- _ /\ _ => split end; lia.
Qed.

(* ---- What the prologue's runs keep.  They store only into [sp0 - 352, sp0). ---- *)
Lemma pro_keep : forall E rs (W : world SEGS) mem m1 m2 sp0,
frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
(forall a, in_wrange E rs a -> sp0 - DRAIN_FRAME <= a < sp0) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - DRAIN_FRAME <= a < sp0) ->
   aview SEGS (w_H W) m1 a = aview SEGS (w_H W) mem a) ->
mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) m1) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - DRAIN_FRAME <= a < sp0) ->
   aview SEGS (w_H W) m2 a = aview SEGS (w_H W) mem a) /\
mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) m2).
Proof.
intros E rs W mem m1 m2 sp0 HF HGr Hwr KL GR. split.
- intros a Ha Hno. rewrite <- (KL a Ha Hno).
  apply (aview_kept_out E rs (w_H W) m1 m2 HF a Ha). intros Hw. exact (Hno (Hwr a Hw)).
- intros x Hx. apply HGr. apply GR. exact Hx.
Qed.

Ltac pro_wr_frame Usp :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr); cbn [ss_mem add_cond ss_pro pro_regions In] in Hin;
repeat (destruct Hin as [<- | Hin];
  [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val stack_region got_regionP bcell_regionP] in Hr;
   rewrite ?Usp in Hr; unfold DRAIN_FRAME in *; lia|]);
destruct Hin.

Lemma pro_kept_at : forall (W : world SEGS) mem m' sp0 a,
(forall x, 0 <= x < 2 ^ 64 -> ~ (sp0 - DRAIN_FRAME <= x < sp0) ->
   aview SEGS (w_H W) m' x = aview SEGS (w_H W) mem x) ->
mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) m') ->
0 <= a < 2 ^ 64 -> ~ (sp0 - DRAIN_FRAME <= a < sp0) -> abyte_kept W mem W m' a.
Proof.
intros W mem m' sp0 a HK HGr Ha Hno. split; [exact (HK a Ha Hno)|].
unfold arm. apply writable_kept. intros Hp. exact (apresent_grows _ _ _ _ HGr Hp).
Qed.

(* Every address the walk's representations touch lies below alloc_ceiling + 8 (a live block, the image band, or
   the granule tail of a key's block), and the frame is far above that. *)
Definition pro_low (a : Z) : Prop := 0 <= a < alloc_ceiling + 8.

Lemma pro_blk_low : forall ly S (W : world SEGS) mem md q n a,
AR SEGS B ly S W mem md -> In (q, n) (ablocks B ly S) -> q <= a -> a < q + req_size n + 8 -> pro_low a.
Proof.
intros ly S W mem md q n a HAR Hin H1 H2.
destruct (al_blocks SEGS B LAWS ly S W mem md q n HAR Hin) as (_ & H4096 & Hceil & _).
unfold pro_low. lia.
Qed.

Lemma pro_img_low : forall a lo hi, 0x10000 <= lo -> lo <= a -> a < hi -> hi <= IMG_TOP -> pro_low a.
Proof. intros a lo hi H1 H2 H3 H4. pose proof asan_consts as (C1 & _). unfold pro_low, IMG_TOP in *. lia. Qed.

Lemma pro_kept_low : forall (W : world SEGS) mem m' sp0 a,
(forall x, 0 <= x < 2 ^ 64 -> ~ (sp0 - DRAIN_FRAME <= x < sp0) ->
   aview SEGS (w_H W) m' x = aview SEGS (w_H W) mem x) ->
mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) m') ->
alloc_ceiling + 8 <= sp0 - DRAIN_FRAME -> pro_low a -> abyte_kept W mem W m' a.
Proof.
intros W mem m' sp0 a HK HGr Hlo Ha. pose proof asan_consts as (C1 & _). unfold pro_low in Ha.
apply (pro_kept_at W mem m' sp0 a HK HGr); lia.
Qed.
Lemma pro_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
intros ks. unfold key_ptrs. induction ks as [|k ks IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. cbn [length]. rewrite Mem.length_le8. lia.
Qed.

Lemma pro_recs_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !Mem.length_le8. lia.
Qed.

(* ---- Lowness of each footprint the segment moves. ---- *)
(* A held key's footprint is its |text| + 1 bytes (ruling (A)), inside its own block. *)
Lemma pro_aentry_fp_low : forall ly S (W : world SEGS) mem md e,
AR SEGS B ly S W mem md -> aentry_ok B ly S W mem e ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r -> pro_low a.
Proof.
intros ly S W mem md e HAR HE r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & _ & _ & Hbuf & _ & Hhp & _ & _ & Hks).
assert (HK : forall k, In k (re_keys e) -> key_addr k <= a < key_addr k + Z.of_nat (length (key_text k) + 1) ->
  pro_low a).
{ intros k Hk Hka. rewrite Forall_forall in Hks. destruct (Hks k Hk) as (Hin & _).
  apply (pro_blk_low ly S W mem md (key_addr k) (Z.of_nat (length (key_text k)) + 1) a HAR Hin); [lia|].
  pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)) as (_ & Hrq). lia. }
assert (HP : re_hp e <= a < re_hp e + Z.of_nat (length (bzs (key_ptrs (re_keys e)))) -> pro_low a).
{ intros Hpa. destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
  - rewrite Hke in Hpa. unfold bzs, key_ptrs in Hpa. cbn [map concat length] in Hpa. lia.
  - unfold bzs in Hpa. rewrite length_map, pro_key_ptrs_len in Hpa.
    apply (pro_blk_low ly S W mem md (re_hp e) (re_kh e) a HAR Hin); [lia|].
    pose proof (req_size_pos (re_kh e) ltac:(lia)) as (_ & Hrq).
    unfold re_nheld in Hk1. lia. }
unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
  rewrite length_map, length_app in Ha.
  destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  apply (pro_blk_low ly S W mem md (re_buf e) (re_cap e) a HAR Hin); [lia|].
  pose proof (req_size_pos (re_cap e) ltac:(lia)) as (_ & Hrq). lia.
- destruct Hr as [<- | Hr].
  + unfold gfp in Ha. cbn [fst snd] in Ha. exact (HP Ha).
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha. exact (HK k Hk Ha).
Qed.

Lemma pro_alist_fp_low : forall ly S (W : world SEGS) mem md LA l lines lo hi,
AR SEGS B ly S W mem md -> alist_at B ly S W mem LA l lines ->
0x10000 <= lo -> lo <= LA -> LA + 16 <= hi -> hi <= IMG_TOP ->
forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r -> pro_low a.
Proof.
intros ly S W mem md LA l lines lo hi HAR HL Hlo1 Hlo2 Hhi1 Hhi2 r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. apply (pro_img_low a lo hi); lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app, pro_recs_len in Ha.
    destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    apply (pro_blk_low ly S W mem md (hl_v l) (AREC * hl_cap l) a HAR Hin); [lia|].
    pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as (_ & Hrq).
    unfold hl_n in Hn, Hj. unfold AREC in *. clear - Ha Hn Hj Hrq. lia.
  + apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hrecs. destruct (Hrecs q Hq) as (Hin & _).
    apply (pro_blk_low ly S W mem md (fst q) (Z.of_nat (length (snd q)) + 1) a HAR Hin); [lia|].
    pose proof (req_size_pos (Z.of_nat (length (snd q)) + 1) ltac:(lia)) as (_ & Hrq). lia.
Qed.

Lemma pro_asrc_fp_low : forall ly S (W : world SEGS) mem md HA h,
AR SEGS B ly S W mem md -> asrc_at B ly S W mem HA h ->
rg_s RG <= HA -> HA + ASRC <= rg_s RG + 4 * ASRC ->
forall r, In r (asrc_fp HA h) -> forall a, fst r <= a < snd r -> pro_low a.
Proof.
intros ly S W mem md HA h HAR HS Hlo Hhi r Hr a Ha.
pose proof HGSB as (Hg1 & Hg2 & _).
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- cbn [fst snd] in Ha. apply (pro_img_low a (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC in *; lia.
- unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map in Ha.
  apply (pro_blk_low ly S W mem md (hs_partial h) APARTIAL a HAR Hpb); [lia|].
  pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrq). lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + refine (pro_alist_fp_low ly S W mem md (HA + 16) (hs_pending h) false (rg_s RG) (rg_s RG + 4 * ASRC)
      HAR Hpend _ _ _ _ r Hr a Ha); unfold ASRC in *; lia.
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * refine (pro_alist_fp_low ly S W mem md (HA + 64) (hs_expected h) true (rg_s RG) (rg_s RG + 4 * ASRC)
        HAR Hexp _ _ _ _ r Hr a Ha); unfold ASRC in *; lia.
    * refine (pro_alist_fp_low ly S W mem md (HA + 80) (hs_held h) true (rg_s RG) (rg_s RG + 4 * ASRC)
        HAR Hheld _ _ _ _ r Hr a Ha); unfold ASRC in *; lia.
Qed.

(* The output cells: G_DR's cells by gx_ok, g_client by HV9 (A_OBJ 9), g_send_dead / g_send_max by their image
   band HSD / HSM (they are not listing objects of image B, W_drain_cx.v OBJECTS), the buffer by its block. *)
Lemma pro_aout_fp_low : forall ly S (W : world SEGS) mem md c O mx no cap out,
AR SEGS B ly S W mem md -> aout_at B RG ly S W mem c O mx no cap out ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r -> pro_low a.
Proof.
intros ly S W mem md c O mx no cap out HAR HOUT r Hr a Ha.
pose proof asan_consts as (C1 & _ & _ & _ & C5).
assert (GL : forall x l, In (x, l) (G_DR B RG) -> x <= a < x + l -> pro_low a).
{ intros x l Hin Hx.
  assert (HI : inG (G_DR B RG) a)
    by (unfold inG; apply Exists_exists; exists (x, l); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
  pose proof (inG_low SEGS B pa_segs_low _ a HG HI). unfold pro_low. lia. }
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
- pose proof HSM as (Hs1 & Hs2). apply (pro_img_low a (rg_send_max RG) (rg_send_max RG + 8)); lia.
- apply (GL (rg_nout RG) 8); [unfold G_DR, G_SL; pro_in | lia].
- apply (GL (rg_capout RG) 8); [unfold G_DR, G_SL; pro_in | lia].
- apply (GL (rg_out RG) 8); [unfold G_DR, G_SL; pro_in | lia].
- pose proof (pa_obj_img 9 ltac:(lia)) as H9. rewrite HV9 in H9.
  apply (pro_img_low a (rg_client RG) (rg_client RG + 4)); unfold IMG_TOP; lia.
- apply (GL (rg_client_broken RG) 1); [unfold G_DR, G_SL; pro_in | lia].
- pose proof HSD as (Hs1 & Hs2). apply (pro_img_low a (rg_send_dead RG) (rg_send_dead RG + 1)); lia.
- apply (GL (rg_send_eintr RG) 1); [unfold G_DR, G_SL; pro_in | lia].
- apply (GL (as_errno B) 4); [unfold G_DR, G_SL; pro_in | lia].
- destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
  apply (pro_blk_low ly S W mem md out cap a HAR Hin); [lia|].
  pose proof (req_size_pos cap ltac:(lia)) as (_ & Hrq). lia.
Qed.

Lemma pro_rom_moved : forall (W : world SEGS) mem m' sp0,
(forall x, 0 <= x < 2 ^ 64 -> ~ (sp0 - DRAIN_FRAME <= x < sp0) ->
   aview SEGS (w_H W) m' x = aview SEGS (w_H W) mem x) ->
alloc_ceiling + 8 <= sp0 - DRAIN_FRAME -> rom_view SEGS W mem -> rom_view SEGS W m'.
Proof.
intros W mem m' sp0 KL Hlo HR a Ha. pose proof asan_consts as (C1 & _ & _ & _ & C5).
assert (Hl : 0 <= a < kLowMemEnd).
{ destruct Ha as (sg & Hsg & _ & Hr). exact (pa_segs_low a ltac:(exists sg; split; [exact Hsg | exact Hr])). }
rewrite (KL a ltac:(lia) ltac:(lia)). exact (HR a Ha).
Qed.

(* ---- The 13 saved registers, read off the frame's stack region: s11 at 248(sp) = chunk -104 .. ra at
   344(sp) = chunk -8 (W_drain_cx.v DR_SAVED / DR_SAVE_OFF). ---- *)
Definition pro_saved_atoms : list nat := [27; 26; 25; 24; 23; 22; 21; 20; 19; 18; 9; 8; 1]%nat.
Lemma pro_saved_of_region : forall E (W : world SEGS) memX regs lo hi wlo whi cs,
region_ok SEGS E (mrestrict (w_H W) memX) (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
(forall i, (i < 13)%nat -> In (YP09.mkChunk (-104 + 8 * Z.of_nat i) (CVal 8 (SOff (nth i pro_saved_atoms 0%nat) 0))) cs) ->
(forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) ->
dr_saved (PI := PI) W memX (bv_unsigned (ew E 2) - DRAIN_FRAME) regs.
Proof.
intros E W memX regs lo hi wlo whi cs HR Hin EREG i Hi.
assert (Hew : ew E (nth i pro_saved_atoms 0%nat) = getr regs (nth i DR_SAVED 0%bv)).
{ apply EREG; (do 13 (destruct i as [|i]; [first [reflexivity | cbn [nth pro_saved_atoms]; lia] |])); lia. }
replace (bv_unsigned (ew E 2) - DRAIN_FRAME + DR_SAVE_OFF + 8 * Z.of_nat i)
  with (bv_unsigned (ew E 2) + (-104 + 8 * Z.of_nat i)) by (unfold DRAIN_FRAME, DR_SAVE_OFF; lia).
apply (slot_of_region E _ _ cs lo hi wlo whi _ (SOff (nth i pro_saved_atoms 0%nat) 0) _ HR eq_refl (Hin i Hi)).
- cbn [sv_denot]. rewrite Hew, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (bv_unsigned_in_range 64 (getr regs (nth i DR_SAVED 0%bv))) as R.
  change (bv_modulus 64) with (2 ^ 64) in R. lia.
Qed.
Ltac pro_saved_in := let i := fresh "i" in let Hi := fresh "Hi" in
intros i Hi; do 13 (destruct i as [|i]; [cbn; pro_in|]); lia.

(* ---- Reading a frame slot's value. ---- *)
Lemma pro_den : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. rewrite <- H. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

(* A frame slot k(sp) of the 352-byte frame, read off the stack region's chunk at k - 352. *)
Lemma pro_slot : forall E m cs lo hi wlo whi sp0 k e v,
region_ok SEGS E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) -> bv_unsigned (ew E 2) = sp0 ->
In (YP09.mkChunk (k - DRAIN_FRAME) (CVal 8 e)) cs -> U E e = v -> 0 <= v < 2 ^ 64 ->
val_mem SEGS m (sp0 - DRAIN_FRAME + k) 8 v.
Proof.
intros E m cs lo hi wlo whi sp0 k e v HR Hsp Hin HU Hv.
replace (sp0 - DRAIN_FRAME + k) with (sp0 + (k - DRAIN_FRAME)) by lia.
exact (slot_of_region E m sp0 cs lo hi wlo whi (k - DRAIN_FRAME) e v HR Hsp Hin (pro_den E e v HU) Hv).
Qed.

Lemma pro_d8 : forall x, 0 <= x < 2 ^ 64 -> 0 <= x / 8 < 2 ^ 61.
Proof. intros x Hx. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.

(* A register of the reached symbolic state, as the denotation of its symbolic value (not normalized). *)
Ltac pro_rreg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.

Lemma pro_U_srl : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
U E (SAlu ALU_SRL (SOff n c) (SLit 3)) = (v + c) / 8.
Proof.
intros E n v c Hn Hv Hc. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E n v c Hn Hv Hc), U_SLit, (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
apply zcanon_id. unfold M64. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma pro_U_shadow : forall E n v c, ew E n = Z_to_bv 64 v -> ew E 32 = Z_to_bv 64 SB ->
0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff 32 0)) = SHADOW_OFF + (v + c) / 8.
Proof.
intros E n v c Hn H32 Hv Hc. rewrite U_SAlu. cbn [zalu_raw].
rewrite (pro_U_srl E n v c Hn Hv Hc), (U_atom E 32 SB H32) by (unfold SB; lia).
assert (Hd : 0 <= (v + c) / 8 < 2 ^ 61) by
  (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
replace (SB) with SHADOW_OFF by reflexivity.
rewrite Z.add_comm. apply zcanon_id. unfold M64, SHADOW_OFF. lia.
Qed.

Lemma pro_U_mod8 : forall E v, ew E 10 = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
U E (SAlu ALU_ADD (SAlu ALU_AND (SOff 10 0) (SLit 7)) (SLit 3)) = v mod 8 + 3.
Proof.
intros E v Hn Hv. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_and_lit by (unfold M64; lia). rewrite (U_atom E 10 v Hn Hv), U_SLit, (zcanon_id 3) by (unfold M64; lia).
change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
pose proof (Z.mod_pos_bound v 8 ltac:(lia)). apply zcanon_id. unfold M64. lia.
Qed.

(* ---- The model at round 0. ---- *)
Lemma pro_pstream_init : forall NO CAP e h,
pstream (drain_b_c.drain_init NO CAP e h) = bzs (pending_stream h).
Proof.
intros NO CAP e h. unfold pstream, prest, pending_stream, drain_b_c.drain_init.
cbn [drain_b_c.ds_pend drain_b_c.ds_off].
destruct (hl_recs (hs_pending h)) as [|r rs]; cbn [map]; [reflexivity|].
unfold bzs. rewrite map_app, concat_map, map_map. f_equal.
generalize (Z.to_nat (hs_off h)) as n. generalize (snd r) as l. clear.
induction l as [|x l IH]; intros [|n]; cbn; try reflexivity. apply IH.
Qed.

Lemma pro_dwf_init : forall NO CAP e h,
(hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
(exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r))) ->
dwf (drain_b_c.drain_init NO CAP e h).
Proof.
intros NO CAP e h HP. unfold dwf, drain_b_c.drain_init. cbn [drain_b_c.ds_off drain_b_c.ds_pend].
destruct HP as [(HR & HO)|(r & rs & HR & HO)]; rewrite HR; cbn [map].
- split; [lia|]. intros r rs Hc. discriminate Hc.
- split; [lia|]. intros r' rs' Hc. injection Hc as <- <-. unfold bzs. rewrite length_map. lia.
Qed.

Lemma pro_bzs_inj : forall x y : list byte, bzs x = bzs y -> x = y.
Proof.
induction x as [|a x IH]; intros [|b y] H; unfold bzs in H; cbn [map] in H; try discriminate H; [reflexivity|].
injection H as Hab Hxy. unfold bz in Hab. f_equal; [apply bv_eq; exact Hab | exact (IH y Hxy)].
Qed.

Lemma pro_nodup_kt : forall ks, NoDup (map key_text ks) -> NoDup (drain_b_c.keys_texts ks).
Proof.
intros ks H. unfold drain_b_c.keys_texts.
replace (map (fun k => bzs (key_text k)) ks) with (map bzs (map key_text ks)) by (rewrite map_map; reflexivity).
apply NoDup_ListNoDup. apply NoDup_ListNoDup in H.
revert H. generalize (map key_text ks) as l. induction l as [|x l IH]; intros HN; [constructor|].
inversion HN as [|y ys Hy Hl]; subst. cbn [map]. constructor; [|exact (IH Hl)].
intros Hin. apply in_map_iff in Hin as (z & Hz & Hzin). apply Hy.
rewrite <- (pro_bzs_inj z x Hz). exact Hzin.
Qed.

Lemma pro_nozero : forall U0, ~ In (Z_to_bv 8 0) U0 -> nozero (bzs U0).
Proof.
intros U0 H. unfold nozero, bzs. apply Forall_forall. intros b Hb.
apply in_map_iff in Hb as (x & <- & Hx). intros Ex. apply H.
replace (Z_to_bv 8 0) with x; [exact Hx|]. apply bv_eq. unfold bz in Ex. rewrite Ex. reflexivity.
Qed.

(* ---- The segment. ---- *)
Theorem dr_pro : dr_pro_stmt B MT MMAX RG.
Proof.
intros cx HB K.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (pro_entry_state cx HB) as HS.
pose proof HB as (HPRE & HSA & HGin & HGle & HSAle & HSA8 & HENT & HAWR & HEOK & Hj4 & HSRC & HOTH & HFD & HSK & HSW &
  HOUT & HROM & HPERM & HPS & HEC & HNH & HTM & HTA & HMO).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : DRAIN_STK = 16880) by reflexivity.
destruct (pro_SA_range cx HB) as (HSAlo & HSAhi & HSAr1).
assert (HSA64 : 4096 <= dxSA cx /\ dxSA cx + 56 <= 140737479966720) by (unfold AENT in *; lia).
pose proof (ajournal_gx_init SEGS B (G_DR B RG) 0 [] DRAIN_STK (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxregs cx)
  (dxmem cx) (dxmd cx) (dxch cx) HPRE ltac:(lia) eq_refl ltac:(lia) ltac:(intros a Ha; lia)) as HJ.
remember (Eimg (Ereg (dxregs cx) pro_extra)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr (dxregs cx) r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat (dxregs cx) _ n r Hr)).
assert (E2 : ew E 2 = getr (dxregs cx) 2) by (apply EREG; [lia | reflexivity]).
assert (E3 : ew E 3 = getr (dxregs cx) 3) by (apply EREG; [lia | reflexivity]).
assert (E4 : ew E 4 = getr (dxregs cx) 4) by (apply EREG; [lia | reflexivity]).
assert (E10 : ew E 10 = Z_to_bv 64 (dxSA cx)) by (rewrite (EREG 10%nat 10%bv) by (first [lia | reflexivity]); exact HSA).
assert (E32 : ew E 32 = Z_to_bv 64 SB)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra (dxregs cx) _ 0)).
assert (EO19 : ew E (A_OBJ 19) = Z_to_bv 64 (rg_s RG))
  by (rewrite <- HVS; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ (dxregs cx)) by (rewrite E2; reflexivity).
assert (SHOK : sh_ok SEGS BxP [] E (mrestrict (w_H (dxW cx)) (dxmem cx))) by constructor.
assert (KL0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (dxregs cx) - DRAIN_FRAME <= a < spZ (dxregs cx)) ->
  aview SEGS (w_H (dxW cx)) (dxmem cx) a = aview SEGS (w_H (dxW cx)) (dxmem cx) a) by reflexivity.
assert (GR0 : mem_grows (mrestrict (w_H (dxW cx)) (dxmem cx)) (mrestrict (w_H (dxW cx)) (dxmem cx)))
  by (intros x Hx; exact Hx).
clear HE.
unfold cfg_at, A_drainP. change (w64 (BASE + A_drain)) with (Z_to_bv 64 (BASE + A_drain)).
(* 0x83278 .. 0x832b4: the frame, the 13 saves, mv s5,a0 and andi a0,a0,7; the runner stops at the ALIGN8 trap *)
paj_run_tok RUN HS HJ SHOK pro_Bspan. { apply awr_ok_x_of0. awr_ok_tac. all: exact Usp. }
lazymatch type of HFr with frame_of ?Ev ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFr end.
destruct (pro_keep E _ (dxW cx) (dxmem cx) _ _ (spZ (dxregs cx)) HFr HG0 ltac:(pro_wr_frame Usp) KL0 GR0)
  as [KL1 GR1].
clear HF HFr HG0 KL0 GR0.
(* 0x832b8 bnez a0 -> 0x84004 (UBSan ALIGN8 on SA): the trap edge is refuted by W_traps.v trap_align8 from
   DBASE's dxSA cx mod 8 = 0 (W_drain_cx.v FINDING 1) *)
psrr_branch_tok RUN BR HS SHOK pro_Bspan.
{ exfalso.
  rewrite (W_traps.trap_align8 E (SOff 10 0) (dxSA cx) (U_atom E 10 (dxSA cx) E10 ltac:(lia)) HSA8) in Hc.
  discriminate Hc. }
(* 0x832bc .. 0x833bc: the field addresses, g_s, the shadow base and the one-time frame slots, to DI 0x833c0 *)
paj_run_to_tok RUNTO HS HJ SHOK pro_Bspan A_dr_top. { apply awr_ok_x_of0. awr_ok_tac. all: exact Usp. }
lazymatch type of HFr with frame_of ?Ev ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFr end.
destruct (pro_keep E _ (dxW cx) (dxmem cx) _ _ (spZ (dxregs cx)) HFr HG0 ltac:(pro_wr_frame Usp) KL1 GR1)
  as [KL2 GR2].
clear HF HFr HG0 KL1 GR1.
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into msF end.
repeat rewrite wvb_collapse in HJ.
(* the registers at the outer loop's head *)
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (20%bv : bv 5) R20. prreg HS (21%bv : bv 5) R21.
prreg HS (22%bv : bv 5) R22. prreg HS (24%bv : bv 5) R24. prreg HS (26%bv : bv 5) R26.
prreg HS (27%bv : bv 5) R27.
pro_rreg HS (9%bv : bv 5) R9. pro_rreg HS (18%bv : bv 5) R18.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
pmkst HS.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?md |} _ => set (md1 := md) end.
set (m1 := ms_mem msF) in *. set (regs1 := ms_regs msF) in *.
(* what the runs keep: everything below the frame *)
assert (Hlo : alloc_ceiling + 8 <= spZ (dxregs cx) - DRAIN_FRAME) by (unfold DRAIN_FRAME; lia).
assert (KEPT : forall a, pro_low a -> abyte_kept (dxW cx) (dxmem cx) (dxW cx) m1 a)
  by (intros a Ha; exact (pro_kept_low (dxW cx) (dxmem cx) m1 (spZ (dxregs cx)) a KL2 GR2 Hlo Ha)).
assert (HBin : forall b, In b ((dxG cx, ATABLE) :: aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++
  aout_blks (dxcap cx) (dxout cx) ++ dxrest cx) -> In b (ablocks B (dxly cx) (dxS cx)))
  by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact HPERM | exact Hb]).
pose proof HEOK as (Heof & Hsk01 & Hp1 & Hp2 & Hfd & Hcap & HUl & HUa & HU0 & Hbuf & Hnh & Hhp & Hnda & Hndt & Hks).
pose proof HSRC as (_ & _ & _ & _ & _ & _ & Hei01 & _ & _ & _ & _ & _ & _ & _ & Hpo & _ & _ & _ & _ & _ & _ &
  Hexp & _ & _).
pose proof Hexp as (_ & _ & _ & _ & Hen & _).
assert (HHA1 : rg_s RG <= dHA RG cx) by (unfold dHA, ASRC; lia).
assert (HHA2 : dHA RG cx + ASRC <= rg_s RG + 4 * ASRC) by (unfold dHA, ASRC; lia).
pose proof HGSB as (Hg1 & Hg2 & Hg3). unfold IMG_TOP in Hg2.
(* the representations, moved across the runs *)
assert (HEOK1 : aentry_ok B (dxly cx) (dxS cx) (dxW cx) m1 (dxe cx)).
{ apply (aentry_ok_kept B (dxly cx) (dxS cx) (dxW cx) (dxmem cx)); [exact HEOK | |].
  - intros r Hr a Ha. apply KEPT.
    exact (pro_aentry_fp_low (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) (dxe cx) HAR HEOK r Hr a Ha).
  - intros b Hb. apply HBin. right. apply in_or_app. left. exact Hb. }
assert (HSRC1 : asrc_at B (dxly cx) (dxS cx) (dxW cx) m1 (dHA RG cx) (dxh cx)).
{ apply (asrc_at_kept B (dxly cx) (dxS cx) (dxW cx) (dxmem cx)); [exact HSRC | |].
  - intros r Hr a Ha. apply KEPT.
    exact (pro_asrc_fp_low (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) (dHA RG cx) (dxh cx) HAR HSRC HHA1 HHA2
      r Hr a Ha).
  - intros b Hb. apply HBin. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
assert (HOUT1 : aout_at B RG (dxly cx) (dxS cx) (dxW cx) m1 (dxc cx) (dxO cx) (dxmx cx) (dxno cx) (dxcap cx)
  (dxout cx)).
{ apply (aout_at_kept B RG (dxly cx) (dxS cx) (dxW cx) (dxmem cx)); [exact HOUT | |].
  - intros r Hr a Ha. apply KEPT.
    exact (pro_aout_fp_low (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) (dxc cx) (dxO cx) (dxmx cx) (dxno cx)
      (dxcap cx) (dxout cx) HAR HOUT r Hr a Ha).
  - intros b Hb. apply HBin. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    exact Hb. }
assert (HEL : Z.of_nat (length (bzs (entry_bytes (dxe cx)))) = AENT).
{ unfold bzs, entry_bytes. rewrite length_map, !length_app, !Mem.length_le4, !Mem.length_le8, Hp1, Hp2.
  reflexivity. }
assert (KSA : forall x, dxSA cx <= x < dxSA cx + AENT -> abyte_kept (dxW cx) (dxmem cx) (dxW cx) m1 x).
{ intros x Hx. apply KEPT.
  apply (pro_blk_low (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) (dxG cx) ATABLE x HAR HGin); [lia|].
  pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as (_ & Hrq). lia. }
assert (KGS : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> abyte_kept (dxW cx) (dxmem cx) (dxW cx) m1 x).
{ intros x Hx. apply KEPT. apply (pro_img_low x (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC, IMG_TOP in *; lia. }
(* the model at round 0 *)
assert (Hlines0 : lines (dSTR cx) [] = []) by reflexivity.
assert (Hctl : dctl cx (Z.of_nat (length (with_nul (lines (dSTR cx) [])))) (ct_ev (dxc cx)) = dxc cx).
{ unfold dctl. rewrite Hlines0. change (Z.of_nat (length (with_nul []))) with 0.
  replace (send_line_c.send_off (ct_cl (dxc cx)) (ct_br (dxc cx)) 0) with true
    by (symmetry; unfold send_line_c.send_off; apply orb_true_r).
  destruct (dxc cx); reflexivity. }
assert (HPS0 : pstream (ds0 cx) = bzs (pending_stream (dxh cx))) by (unfold ds0; apply pro_pstream_init).
assert (HDWF : dwf (ds0 cx)) by (unfold ds0; exact (pro_dwf_init _ _ _ _ Hpo)).
apply K. unfold DI.
exists regs1, (dxly cx), (dxS cx), m1, md1, 0, (dxe cx), (dxh cx), (dxout cx), (ct_ev (dxc cx)), [], 0, 0%nat,
  drain_b_c.dadr0, (dtrc cx).
split; [unfold cfg_at; reflexivity|].
split.
{ (* dregs_top: s5 = SA, s8 = SA + 8, s4 = SA + 16, s6 = SA + 24, s11 = SA + 32, s0 = g_s, s1 = g_s >> 3,
     s2 = (g_s + 4) >> 3, s10 = 384 *)
  unfold dregs_top.
  split; [unfold spZ at 1; subst regs1; rewrite R2, Usp, unsigned_lit_small by (unfold DRAIN_FRAME; lia);
    unfold dsp0, DRAIN_FRAME; lia|].
  split; [subst regs1; rewrite R3; exact E3|]. split; [subst regs1; rewrite R4; exact E4|].
  split; [subst regs1; rewrite R21; exact E10|].
  split; [subst regs1; rewrite R24, E10, unsigned_lit_small by lia; reflexivity|].
  split; [subst regs1; rewrite R20, E10, unsigned_lit_small by lia; reflexivity|].
  split; [subst regs1; rewrite R22, E10, unsigned_lit_small by lia; reflexivity|].
  split; [subst regs1; rewrite R27, E10, unsigned_lit_small by lia; reflexivity|].
  split; [subst regs1; rewrite R8; exact EO19|].
  split; [subst regs1; rewrite R9; apply pro_den;
    replace (rg_s RG / 8) with ((rg_s RG + 0) / 8) by (rewrite Z.add_0_r; reflexivity);
    apply (pro_U_srl E 260 (rg_s RG) 0 EO19); unfold ASRC in *; lia|].
  split; [subst regs1; rewrite R18; apply pro_den; apply (pro_U_srl E 260 (rg_s RG) 4 EO19); unfold ASRC in *; lia|].
  subst regs1; rewrite R26; reflexivity. }
split.
{ (* DMEM *)
  unfold DMEM.
  split; [exact HJ|].
  split; [exact (pro_rom_moved (dxW cx) (dxmem cx) m1 (spZ (dxregs cx)) KL2 Hlo HROM)|].
  split; [intros a _ _ _ Hp; exact (apresent_grows _ _ _ _ GR2 Hp)|].
  split; [reflexivity|].
  split.
  { unfold dr_frame. cbv zeta.
    pose proof (pro_d8 (dxSA cx) ltac:(lia)) as D0. pose proof (pro_d8 (dxSA cx + 16) ltac:(lia)) as D16.
    pose proof (pro_d8 (dxSA cx + 24) ltac:(lia)) as D24. pose proof (pro_d8 (dxSA cx + 32) ltac:(lia)) as D32.
    pose proof (Z.mod_pos_bound (dxSA cx) 8 ltac:(lia)) as M8.
    assert (GD : forall c, 0 <= c <= 56 -> 0 <= (rg_s RG + c) / 8 < 2 ^ 61)
      by (intros c Hc'; apply pro_d8; unfold ASRC in *; lia).
    split; [apply (pro_slot E _ _ _ _ _ _ _ 8 (SAlu ALU_ADD (SAlu ALU_AND (SOff 10 0) (SLit 7)) (SLit 3)) _ HR0 Usp);
      [cbn; pro_in | apply (pro_U_mod8 E (dxSA cx) E10); lia | lia]|].
    split; [apply (pro_slot E _ _ _ _ _ _ _ 32 (SOff 10 48) _ HR0 Usp);
      [cbn; pro_in | apply (U_atom_off E 10 (dxSA cx) 48 E10); lia | lia]|].
    split; [apply (pro_slot E _ _ _ _ _ _ _ 40 (SAlu ALU_SRL (SOff 260 8) (SLit 3)) _ HR0 Usp);
      [cbn; pro_in | apply (pro_U_srl E 260 (rg_s RG) 8 EO19); unfold ASRC in *; lia
      | pose proof (GD 8 ltac:(lia)); lia]|].
    split; [apply (pro_slot E _ _ _ _ _ _ _ 48 (SAlu ALU_SRL (SOff 260 56) (SLit 3)) _ HR0 Usp);
      [cbn; pro_in | apply (pro_U_srl E 260 (rg_s RG) 56 EO19); unfold ASRC in *; lia
      | pose proof (GD 56 ltac:(lia)); lia]|].
    split; [apply (pro_slot E _ _ _ _ _ _ _ 56 (SAlu ALU_SRL (SOff 260 48) (SLit 3)) _ HR0 Usp);
      [cbn; pro_in | apply (pro_U_srl E 260 (rg_s RG) 48 EO19); unfold ASRC in *; lia
      | pose proof (GD 48 ltac:(lia)); lia]|].
    split; [apply (pro_slot E _ _ _ _ _ _ _ 64 (SAlu ALU_SRL (SOff 260 40) (SLit 3)) _ HR0 Usp);
      [cbn; pro_in | apply (pro_U_srl E 260 (rg_s RG) 40 EO19); unfold ASRC in *; lia
      | pose proof (GD 40 ltac:(lia)); lia]|].
    split; [apply (pro_slot E _ _ _ _ _ _ _ 72 (SAlu ALU_SRL (SOff 260 32) (SLit 3)) _ HR0 Usp);
      [cbn; pro_in | apply (pro_U_srl E 260 (rg_s RG) 32 EO19); unfold ASRC in *; lia
      | pose proof (GD 32 ltac:(lia)); lia]|].
    split; [apply (pro_slot E _ _ _ _ _ _ _ 80 (SAlu ALU_SRL (SOff 260 16) (SLit 3)) _ HR0 Usp);
      [cbn; pro_in | apply (pro_U_srl E 260 (rg_s RG) 16 EO19); unfold ASRC in *; lia
      | pose proof (GD 16 ltac:(lia)); lia]|].
    split; [apply (pro_slot E _ _ _ _ _ _ _ 88 (SOff 10 40) _ HR0 Usp);
      [cbn; pro_in | apply (U_atom_off E 10 (dxSA cx) 40 E10); lia | lia]|].
    split; [apply (pro_slot E _ _ _ _ _ _ _ 104 (SAlu ALU_SRL (SOff 260 24) (SLit 3)) _ HR0 Usp);
      [cbn; pro_in | apply (pro_U_srl E 260 (rg_s RG) 24 EO19); unfold ASRC in *; lia
      | pose proof (GD 24 ltac:(lia)); lia]|].
    split; [apply (pro_slot E _ _ _ _ _ _ _ 120 (SOff 260 0) _ HR0 Usp);
      [cbn; pro_in | apply (U_atom E 260 (rg_s RG) EO19); unfold ASRC in *; lia | unfold ASRC in *; lia]|].
    split; [apply (pro_slot E _ _ _ _ _ _ _ 128 (SOff 10 16) _ HR0 Usp);
      [cbn; pro_in | apply (U_atom_off E 10 (dxSA cx) 16 E10); lia | lia]|].
    split; [apply (pro_slot E _ _ _ _ _ _ _ 136 (SOff 10 24) _ HR0 Usp);
      [cbn; pro_in | apply (U_atom_off E 10 (dxSA cx) 24 E10); lia | lia]|].
    split; [apply (pro_slot E _ _ _ _ _ _ _ 144 (SOff 10 0) _ HR0 Usp);
      [cbn; pro_in | apply (U_atom E 10 (dxSA cx) E10); lia | lia]|].
    split; [apply (pro_slot E _ _ _ _ _ _ _ 152 (SAlu ALU_SRL (SOff 260 12) (SLit 3)) _ HR0 Usp);
      [cbn; pro_in | apply (pro_U_srl E 260 (rg_s RG) 12 EO19); unfold ASRC in *; lia
      | pose proof (GD 12 ltac:(lia)); lia]|].
    split; [apply (pro_slot E _ _ _ _ _ _ _ 176 (SOff 10 32) _ HR0 Usp);
      [cbn; pro_in | apply (U_atom_off E 10 (dxSA cx) 32 E10); lia | lia]|].
    split; [apply (pro_slot E _ _ _ _ _ _ _ 184 (SLit 6001) _ HR0 Usp);
      [cbn; pro_in | apply U_lit; lia | lia]|].
    split; [apply (pro_slot E _ _ _ _ _ _ _ 200
      (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 32 0)) _ HR0 Usp);
      [cbn; pro_in
      | replace (shadow_addr (dxSA cx)) with (SHADOW_OFF + (dxSA cx + 0) / 8)
          by (unfold shadow_addr; rewrite Z.add_0_r; reflexivity);
        apply (pro_U_shadow E 10 (dxSA cx) 0 E10 E32); lia
      | unfold shadow_addr, SHADOW_OFF; lia]|].
    split; [apply (pro_slot E _ _ _ _ _ _ _ 208 (SOff 10 8) _ HR0 Usp);
      [cbn; pro_in | apply (U_atom_off E 10 (dxSA cx) 8 E10); lia | lia]|].
    split; [apply (pro_slot E _ _ _ _ _ _ _ 216
      (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 32) (SLit 3)) (SOff 32 0)) _ HR0 Usp);
      [cbn; pro_in | apply (pro_U_shadow E 10 (dxSA cx) 32 E10 E32); lia
      | unfold shadow_addr, SHADOW_OFF; lia]|].
    split; [apply (pro_slot E _ _ _ _ _ _ _ 224
      (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 16) (SLit 3)) (SOff 32 0)) _ HR0 Usp);
      [cbn; pro_in | apply (pro_U_shadow E 10 (dxSA cx) 16 E10 E32); lia
      | unfold shadow_addr, SHADOW_OFF; lia]|].
    split; [apply (pro_slot E _ _ _ _ _ _ _ 232
      (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 24) (SLit 3)) (SOff 32 0)) _ HR0 Usp);
      [cbn; pro_in | apply (pro_U_shadow E 10 (dxSA cx) 24 E10 E32); lia
      | unfold shadow_addr, SHADOW_OFF; lia]|].
    split; [apply (pro_slot E _ _ _ _ _ _ _ 240 (SOff 32 0) _ HR0 Usp);
      [cbn; pro_in | apply (U_atom E 32 SB E32); unfold SB; lia | unfold SHADOW_OFF; lia]|].
    unfold dsp0. rewrite <- Usp.
    apply (pro_saved_of_region E (dxW cx) m1 (dxregs cx) _ _ _ _ _ HR0); [pro_saved_in | exact EREG]. }
  split; [apply (akept_garr8 (dxW cx) (dxmem cx)); [intros x Hx; apply KSA; lia | exact HENT]|].
  split; [apply (akept_awr (dxW cx) (dxmem cx)); [exact KSA | exact HAWR]|].
  split.
  { (* aentry_okx: aentry_ok with re_used <= re_cap in place of re_used <= APARTIAL and the NUL-freedom *)
    pose proof HEOK1 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15).
    unfold aentry_okx.
    split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|].
    split; [exact B6|]. split; [exact B7|].
    split; [destruct Hbuf as [(A1 & A2 & A3)|(A1 & _)]; unfold APARTIAL in *; lia|].
    split; [exact B10|]. split; [exact B11|]. split; [exact B12|]. split; [exact B13|]. split; [exact B14|].
    exact B15. }
  split; [exact HSRC1|].
  split.
  { intros i Hi Hij. destruct (HOTH i Hi Hij) as (f & o & V1 & V2 & V3). exists f, o.
    split; [apply (akept_vm (dxW cx) (dxmem cx)); [intros x Hx; apply KGS; unfold ASRC in *; lia | exact V1]|].
    split; [apply (akept_vm (dxW cx) (dxmem cx)); [intros x Hx; apply KGS; unfold ASRC in *; lia | exact V2]|].
    exact V3. }
  split; [intros x Hx _; exact (KGS x Hx)|].
  split; [rewrite Hctl, app_nil_r; destruct (dlive cx); exact HOUT1|].
  split; [intros _; split; reflexivity|].
  exact HPERM. }
split; [exact HU0|]. split; [exact HUa|].
split.
{ (* the relay's buffer, when there is one, is a live block: 8-aligned and below the user ceiling *)
  intros Hc0. destruct Hbuf as [(Hcz & _)|(Hcp & Hin & _)]; [lia|].
  destruct (al_blocks SEGS B LAWS (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) (re_buf (dxe cx)) (re_cap (dxe cx))
    HAR Hin) as (H16 & H4096 & Hceil' & _).
  pose proof (req_size_pos (re_cap (dxe cx)) ltac:(lia)) as (_ & Hrq).
  pose proof (@YM05.alloc_ceiling_value rc) as (ACV & _).
  unfold dinband, DCEIL. split; [lia|]. split; [lia|].
  apply Z.mod_divide in H16; [|lia]. destruct H16 as (q & Hq). rewrite Hq.
  apply Z.mod_divide; [lia|]. exists (2 * q). lia. }
split.
{ (* DLINK at round 0 *)
  unfold DLINK, ds0, drain_b_c.drain_init.
  cbn [drain_b_c.ds_cap drain_b_c.ds_u drain_b_c.ds_skip drain_b_c.ds_H drain_b_c.ds_ka drain_b_c.ds_eintr
       drain_b_c.ds_pend drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_en drain_b_c.ds_ecap].
  split; [reflexivity|]. split; [reflexivity|].
  split; [destruct Hsk01 as [Hs | Hs]; rewrite Hs; reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [destruct Hei01 as [Hs | Hs]; rewrite Hs; reflexivity|].
  do 5 (split; [reflexivity|]).
  exact HDWF. }
split.
{ (* DSAME *)
  unfold DSAME. do 9 (split; [reflexivity|]). left. split; reflexivity. }
split.
{ (* DHIST at round 0 *)
  unfold DHIST. rewrite Hlines0.
  split; [cbn [app]; rewrite HPS0; reflexivity|].
  split; [unfold ds0, drain_b_c.drain_init, dSTR; cbn [drain_b_c.ds_ref]; symmetry; apply feed_nil|].
  split; [cbn [map]; rewrite app_nil_r; reflexivity|].
  split; [apply firstn_all|].
  split; [lia|].
  split; [unfold ds0, drain_b_c.drain_init; cbn [drain_b_c.ds_no]; change (with_nul []) with (@nil Z); cbn; lia|].
  split; [reflexivity|].
  split; [unfold ds0, drain_b_c.drain_init; cbn [drain_b_c.ds_H]; exact (pro_nodup_kt _ Hndt)|].
  split; [unfold ds0, drain_b_c.drain_init; cbn [drain_b_c.ds_H]; intros y; reflexivity|].
  rewrite HPS0. unfold ds0, drain_b_c.drain_init. cbn [drain_b_c.ds_H drain_b_c.ds_en].
  unfold drain_b_c.keys_texts, bzs. rewrite !length_map. unfold re_nheld in HNH. lia. }
split.
{ (* J1 at round 0 *)
  unfold ds0, drain_b_c.drain_init, J1, hs_state. cbn [drain_b_c.ds_u drain_b_c.ds_skip drain_b_c.ds_ref ls_k ls_w].
  split; [rewrite HSK; reflexivity|].
  split; [intros Hk; destruct Hsk01 as [Hs | Hs]; [exact (HSW Hs) | rewrite Hs in Hk; discriminate Hk]|].
  split; [unfold bzs; rewrite length_map; apply Nat2Z.inj_le; rewrite HUl;
    change (Z.of_nat LINE_LIMIT) with 6000; exact HUa|].
  exact (pro_nozero _ HU0). }
split.
{ (* the rounds to come: the whole trace *)
  exists (S (S (length (pending_stream (dxh cx))))).
  split; [unfold dneed; rewrite HPS0; unfold bzs; rewrite length_map;
    destruct (drain_b_c.ds_eintr (ds0 cx)); cbn [Nat.b2n]; lia|].
  split; [exact HDWF|].
  split; [unfold dtrc, dr_tr, drain_b_c.drain_tr, drain_b_c.drain_go, dlive, ds0; reflexivity|].
  unfold dfin, dr_fin, drain_b_c.drain_fin, drain_b_c.drain_go, dlive, ds0. reflexivity. }
(* the budget: nothing spent *)
unfold dbud.
split; [exact (mo_le_refl MT MTL (dxS cx))|]. split; [lia|].
split; [unfold dcost, dr_cost, dtrc; lia|].
split; [exact HTA | exact HTM].
Qed.

End c.
End b.
End a.

(* ---- THE GENERIC WALK (an internal work row, the ARx drain walk DR_x; the image-B twin of lib/A/W_drain_pro.v's dr_pro_x,
   a working branch 6412dbf523c): dr_pro_x : lib/B/W_drain_cx_x.v dr_pro_stmt_x, the same segment over any
   allocator relation ARx with its laws, at the room parameter RP, under W_drain_cx_x.v Section c's hypotheses.  The
   segment makes no call and reads no block shadow, so it needs no HP0: the entry's ghost list Hp is DBASE_x's and the
   journal keeps it (ajournal_gx_init_x).  The lemmas of Section c that read AR are restated here with the suffix _x
   (pro_SA_range_x, pro_entry_state_x, pro_blk_low_x and the four footprint lemmas); the AR-free ones are Section c's,
   cited.  dbud_x's room and counts at the entry trace are DBASE_x's rp_RM and dr_pk premises, by conversion.
   The AR text above (dr_pro and Section c) is unchanged; it is compiled before the Requires below. ---- *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_drain_cx_x.
(* route R: SRrG (Reusable YA0nH) and the R specs (W_contract_xR.v), for the Section wR twins *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR.
(* the zify flag this file's AR text runs with (its own setting above), whatever the Requires above leave *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Abbreviation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Abbreviation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Section cx.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
Context {hl : Z}.
(* W_drain_cx_x.v Section c's hypotheses, word for word *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis AERRNO : aerrno_realizes_x B ARx (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM_x SEGS B ARx 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes_x B ARx (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes_x B ARx (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes_x B ARx (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes_x B ARx (SIGMA WS_strlen).
Hypothesis ALLOC_TAIL : forall ly S Hp W mem md p n a,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
Hypothesis SLSPEC : sl_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g_x B PST ARx MT RP MMAX (BASE + AF_fr_list_push).
Hypothesis RMM : forall S k k', (k' <= k)%nat -> rp_RM RP S k -> rp_RM RP S k'.
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HERRAL : as_errno B mod 4 = 0.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 19) = rg_s RG.
Hypothesis HLIT5 : dlit_at_x ARx 18 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at_x ARx 20 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at_x ARx 21 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 18), VAL (A_OBJ 18) + 14); (VAL (A_OBJ 20), VAL (A_OBJ 20) + 6); (VAL (A_OBJ 21), VAL (A_OBJ 21) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HSD : 0x10000 <= rg_send_dead RG /\ rg_send_dead RG + 1 <= IMG_TOP.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= IMG_TOP.
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_F.
Hypothesis ASTRNDUP : astrndup_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_S (SIGMA WS_strndup).
Hypothesis HCTX_re1 : In [BASE + AF_fr_drain + 0x19c] CTX_R.
Hypothesis HCTX_re2 : In [BASE + AF_fr_drain + 0x974] CTX_R.
Hypothesis HCTX_fr2 : In [BASE + AF_fr_drain + 0xa58] CTX_F.
Hypothesis HCTX_sd : In [BASE + AF_fr_drain + 0x994] CTX_S.
Hypothesis HCTX_ld : In [BASE + AF_fr_list_drop + 0x9c] CTX_F.
Let RUN := paj_run_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.

Local Ltac px_in := repeat (first [left; reflexivity | right]).
Local Ltac px_wr_frame Usp :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr); cbn [ss_mem add_cond ss_pro pro_regions In] in Hin;
repeat (destruct Hin as [<- | Hin];
  [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val stack_region got_regionP bcell_regionP] in Hr;
   rewrite ?Usp in Hr; unfold DRAIN_FRAME in *; lia|]);
destruct Hin.
Local Ltac px_saved_in := let i := fresh "i" in let Hi := fresh "Hi" in
intros i Hi; do 13 (destruct i as [|i]; [cbn; px_in|]); lia.
Local Ltac px_rreg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.

(* The table block holds the entry, so the entry pointer is a live address below the ASan user ceiling. *)
Lemma pro_SA_range_x : forall cx Hp kr, DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
4096 <= dxSA cx /\ dxSA cx + AENT <= alloc_ceiling /\ dxSA cx + AENT <= 140737479966720.
Proof.
intros cx Hp kr HB.
pose proof HB as (HPRE & _ & HGin & HGle & HSAle & _).
pose proof HPRE as (HAR & _).
destruct (alx_blocks SEGS B ARx LAWS (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) (dxG cx) ATABLE HAR HGin)
  as (_ & H4096 & Hceil & _).
pose proof (@YM05.alloc_ceiling_value rc) as (ACV & _).
assert (RQ : req_size ATABLE = 896) by (vm_compute; reflexivity).
rewrite RQ in Hceil. unfold ATABLE in HSAle. lia.
Qed.

Lemma pro_entry_state_x : forall cx Hp kr, DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
st_ok_pi SEGS VAL (Eimg (Ereg (dxregs cx) pro_extra)) ss_pro
(restrict (w_H (dxW cx)) (mkst (dxregs cx) (Z_to_bv 64 (BASE + A_drain)) (dxmem cx) (seg_rom SEGS))).
Proof.
intros cx Hp kr HB.
pose proof HB as (HPRE & HSA & _).
destruct (pro_SA_range_x cx Hp kr HB) as (HSAlo & HSAhi & HSAr1).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : DRAIN_STK_x = 17008) by reflexivity.
destruct (alx_const _ _ _ LAWS (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg (dxregs cx) pro_extra)). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr (dxregs cx) 2)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat (dxregs cx) _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = getr (dxregs cx) 10)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat (dxregs cx) _ 10 10%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra (dxregs cx) _ 0)).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO30 : ew E (A_OBJ 30) = Z_to_bv 64 (VAL (A_OBJ 30)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pa_obj_img 30 ltac:(lia)) as HcellR.
pose proof (pal_got_cell B TL) as HgcD.
assert (Usp : bv_unsigned (ew E 2) = spZ (dxregs cx)) by (rewrite E2; reflexivity).
assert (Usa : bv_unsigned (ew E 10) = dxSA cx)
  by (rewrite E10, HSA; apply unsigned_lit_small; unfold AENT in *; lia).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
unfold ss_pro. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold pro_regions, stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. unfold DRAIN_FRAME. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30)));
    [cbn [sv_denot]; rewrite EO30, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | pose proof (pa_val_range (A_OBJ 30)); zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H (dxW cx)) (dxmem cx) _ _ Kgot).
  + rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) EO30) by (pose proof (pa_val_range (A_OBJ 30)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 30)) 0 8 BxP SB);
    [cbn [sv_denot BxP]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H (dxW cx)) (dxmem cx) _ _ Kcell).
- apply pairwise_disjoint_of_extents. unfold pro_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) EO30) by (pose proof (pa_val_range (A_OBJ 30)); lia).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold DRAIN_FRAME.
  revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgotR HgcD. clear. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [pro_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, Usa, E32, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0 HSAlo HSAhi HSAr1. clear.
  unfold SB, AENT. intros.
  repeat match goal with |- _ /\ _ => split end; lia.
Qed.

Lemma pro_blk_low_x : forall ly S Hp (W : world SEGS) mem md q n a,
ARx ly S Hp W mem md -> In (q, n) (ablocks B ly S) -> q <= a -> a < q + req_size n + 8 -> pro_low a.
Proof.
intros ly S Hp W mem md q n a HAR Hin H1 H2.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md q n HAR Hin) as (_ & H4096 & Hceil & _).
unfold pro_low. lia.
Qed.

(* ---- Lowness of each footprint the segment moves. ---- *)
Lemma pro_aentry_fp_low_x : forall ly S Hp (W : world SEGS) mem md e,
ARx ly S Hp W mem md -> aentry_ok B ly S W mem e ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r -> pro_low a.
Proof.
intros ly S Hp W mem md e HAR HE r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & _ & _ & Hbuf & _ & Hhp & _ & _ & Hks).
assert (HK : forall k, In k (re_keys e) -> key_addr k <= a < key_addr k + Z.of_nat (length (key_text k) + 1) ->
  pro_low a).
{ intros k Hk Hka. rewrite Forall_forall in Hks. destruct (Hks k Hk) as (Hin & _).
  apply (pro_blk_low_x ly S Hp W mem md (key_addr k) (Z.of_nat (length (key_text k)) + 1) a HAR Hin); [lia|].
  pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)) as (_ & Hrq). lia. }
assert (HP : re_hp e <= a < re_hp e + Z.of_nat (length (bzs (key_ptrs (re_keys e)))) -> pro_low a).
{ intros Hpa. destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
  - rewrite Hke in Hpa. unfold bzs, key_ptrs in Hpa. cbn [map concat length] in Hpa. lia.
  - unfold bzs in Hpa. rewrite length_map, (pro_key_ptrs_len B RG) in Hpa.
    apply (pro_blk_low_x ly S Hp W mem md (re_hp e) (re_kh e) a HAR Hin); [lia|].
    pose proof (req_size_pos (re_kh e) ltac:(lia)) as (_ & Hrq).
    unfold re_nheld in Hk1. lia. }
unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
  rewrite length_map, length_app in Ha.
  destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  apply (pro_blk_low_x ly S Hp W mem md (re_buf e) (re_cap e) a HAR Hin); [lia|].
  pose proof (req_size_pos (re_cap e) ltac:(lia)) as (_ & Hrq). lia.
- destruct Hr as [<- | Hr].
  + unfold gfp in Ha. cbn [fst snd] in Ha. exact (HP Ha).
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha. exact (HK k Hk Ha).
Qed.

Lemma pro_alist_fp_low_x : forall ly S Hp (W : world SEGS) mem md LA l lines lo hi,
ARx ly S Hp W mem md -> alist_at B ly S W mem LA l lines ->
0x10000 <= lo -> lo <= LA -> LA + 16 <= hi -> hi <= IMG_TOP ->
forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r -> pro_low a.
Proof.
intros ly S Hp W mem md LA l lines lo hi HAR HL Hlo1 Hlo2 Hhi1 Hhi2 r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. apply (pro_img_low B RG HGSB a lo hi); lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app, (pro_recs_len B RG) in Ha.
    destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    apply (pro_blk_low_x ly S Hp W mem md (hl_v l) (AREC * hl_cap l) a HAR Hin); [lia|].
    pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as (_ & Hrq).
    unfold hl_n in Hn, Hj. unfold AREC in *. clear - Ha Hn Hj Hrq. lia.
  + apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hrecs. destruct (Hrecs q Hq) as (Hin & _).
    apply (pro_blk_low_x ly S Hp W mem md (fst q) (Z.of_nat (length (snd q)) + 1) a HAR Hin); [lia|].
    pose proof (req_size_pos (Z.of_nat (length (snd q)) + 1) ltac:(lia)) as (_ & Hrq). lia.
Qed.

Lemma pro_asrc_fp_low_x : forall ly S Hp (W : world SEGS) mem md HA h,
ARx ly S Hp W mem md -> asrc_at B ly S W mem HA h ->
rg_s RG <= HA -> HA + ASRC <= rg_s RG + 4 * ASRC ->
forall r, In r (asrc_fp HA h) -> forall a, fst r <= a < snd r -> pro_low a.
Proof.
intros ly S Hp W mem md HA h HAR HS Hlo Hhi r Hr a Ha.
pose proof HGSB as (Hg1 & Hg2 & _).
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- cbn [fst snd] in Ha. apply (pro_img_low B RG HGSB a (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC in *; lia.
- unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map in Ha.
  apply (pro_blk_low_x ly S Hp W mem md (hs_partial h) APARTIAL a HAR Hpb); [lia|].
  pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrq). lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + refine (pro_alist_fp_low_x ly S Hp W mem md (HA + 16) (hs_pending h) false (rg_s RG) (rg_s RG + 4 * ASRC)
      HAR Hpend _ _ _ _ r Hr a Ha); unfold ASRC in *; lia.
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * refine (pro_alist_fp_low_x ly S Hp W mem md (HA + 64) (hs_expected h) true (rg_s RG) (rg_s RG + 4 * ASRC)
        HAR Hexp _ _ _ _ r Hr a Ha); unfold ASRC in *; lia.
    * refine (pro_alist_fp_low_x ly S Hp W mem md (HA + 80) (hs_held h) true (rg_s RG) (rg_s RG + 4 * ASRC)
        HAR Hheld _ _ _ _ r Hr a Ha); unfold ASRC in *; lia.
Qed.

Lemma pro_aout_fp_low_x : forall ly S Hp (W : world SEGS) mem md c O mx no cap out,
ARx ly S Hp W mem md -> aout_at B RG ly S W mem c O mx no cap out ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r -> pro_low a.
Proof.
intros ly S Hp W mem md c O mx no cap out HAR HOUT r Hr a Ha.
pose proof asan_consts as (C1 & _ & _ & _ & C5).
assert (GL : forall x l, In (x, l) (G_DR B RG) -> x <= a < x + l -> pro_low a).
{ intros x l Hin Hx.
  assert (HI : inG (G_DR B RG) a)
    by (unfold inG; apply Exists_exists; exists (x, l); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
  pose proof (inG_low SEGS B pa_segs_low _ a HG HI). unfold pro_low. lia. }
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
- pose proof HSM as (Hs1 & Hs2). apply (pro_img_low B RG HGSB a (rg_send_max RG) (rg_send_max RG + 8)); lia.
- apply (GL (rg_nout RG) 8); [unfold G_DR, G_SL; px_in | lia].
- apply (GL (rg_capout RG) 8); [unfold G_DR, G_SL; px_in | lia].
- apply (GL (rg_out RG) 8); [unfold G_DR, G_SL; px_in | lia].
- pose proof (pa_obj_img 9 ltac:(lia)) as H9. rewrite HV9 in H9.
  apply (pro_img_low B RG HGSB a (rg_client RG) (rg_client RG + 4)); unfold IMG_TOP; lia.
- apply (GL (rg_client_broken RG) 1); [unfold G_DR, G_SL; px_in | lia].
- pose proof HSD as (Hs1 & Hs2). apply (pro_img_low B RG HGSB a (rg_send_dead RG) (rg_send_dead RG + 1)); lia.
- apply (GL (rg_send_eintr RG) 1); [unfold G_DR, G_SL; px_in | lia].
- apply (GL (as_errno B) 4); [unfold G_DR, G_SL; px_in | lia].
- destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
  apply (pro_blk_low_x ly S Hp W mem md out cap a HAR Hin); [lia|].
  pose proof (req_size_pos cap ltac:(lia)) as (_ & Hrq). lia.
Qed.

(* ---- The segment. ---- *)


(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the R twin of each relation-dependent lemma above.  Each
   twin is its strict text with the journal and the step relation at R: ajournal_gx_x -> ajournal_gx_xR .. R,
   SRr SEGS -> SRrG SEGS R, the runs and the branch are their SRrG forms (W_journal_x.v paj_run_x_xG /
   paj_run_to_x_xG, W_kit.v paj_branch_xR), each carrier X_x -> its twin X_xR (R last), the journal lemmas their _xR
   forms, and each lemma name L -> LR; the relation-free helpers above are cited as they are.  The strict text is
   untouched. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Let RUNG := paj_run_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let RUNTOG := paj_run_to_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).

Theorem dr_pro_xR : dr_pro_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
intros cx Hp kr HB K.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (pro_entry_state_x cx Hp kr HB) as HS.
pose proof HB as (HPRE & HSA & HGin & HGle & HSAle & HSA8 & HENT & HAWR & HEOK & Hj4 & HSRC & HOTH & HFD & HSK & HSW &
  HOUT & HROM & HPERM & HPS & HEC & HNH & HTM & HTA & HMO & HRM & HCNT).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : DRAIN_STK_x = 17008) by reflexivity.
destruct (pro_SA_range_x cx Hp kr HB) as (HSAlo & HSAhi & HSAr1).
assert (HSA64 : 4096 <= dxSA cx /\ dxSA cx + 56 <= 140737479966720) by (unfold AENT in *; lia).
pose proof (ajournal_gx_init_xR SEGS B PST ARx R_refl (G_DR B RG) 0 [] DRAIN_STK_x (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx)
  (dxregs cx) (dxmem cx) (dxmd cx) (dxch cx) HPRE ltac:(lia) eq_refl ltac:(lia) ltac:(intros a Ha; lia)) as HJ.
remember (Eimg (Ereg (dxregs cx) pro_extra)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr (dxregs cx) r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat (dxregs cx) _ n r Hr)).
assert (E2 : ew E 2 = getr (dxregs cx) 2) by (apply EREG; [lia | reflexivity]).
assert (E3 : ew E 3 = getr (dxregs cx) 3) by (apply EREG; [lia | reflexivity]).
assert (E4 : ew E 4 = getr (dxregs cx) 4) by (apply EREG; [lia | reflexivity]).
assert (E10 : ew E 10 = Z_to_bv 64 (dxSA cx)) by (rewrite (EREG 10%nat 10%bv) by (first [lia | reflexivity]); exact HSA).
assert (E32 : ew E 32 = Z_to_bv 64 SB)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra (dxregs cx) _ 0)).
assert (EO19 : ew E (A_OBJ 19) = Z_to_bv 64 (rg_s RG))
  by (rewrite <- HVS; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ (dxregs cx)) by (rewrite E2; reflexivity).
assert (SHOK : sh_ok SEGS BxP [] E (mrestrict (w_H (dxW cx)) (dxmem cx))) by constructor.
assert (KL0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (dxregs cx) - DRAIN_FRAME <= a < spZ (dxregs cx)) ->
  aview SEGS (w_H (dxW cx)) (dxmem cx) a = aview SEGS (w_H (dxW cx)) (dxmem cx) a) by reflexivity.
assert (GR0 : mem_grows (mrestrict (w_H (dxW cx)) (dxmem cx)) (mrestrict (w_H (dxW cx)) (dxmem cx)))
  by (intros x Hx; exact Hx).
clear HE.
unfold cfg_at, A_drainP. change (w64 (BASE + A_drain)) with (Z_to_bv 64 (BASE + A_drain)).
(* 0x83278 .. 0x832b4: the frame, the 13 saves, mv s5,a0 and andi a0,a0,7; the runner stops at the ALIGN8 trap *)
paj_run_tok_xR RUNG HS HJ SHOK pro_Bspan. { apply awr_ok_x_of0. awr_ok_tac. all: exact Usp. }
lazymatch type of HFr with frame_of ?Ev ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFr end.
destruct (pro_keep E _ (dxW cx) (dxmem cx) _ _ (spZ (dxregs cx)) HFr HG0 ltac:(px_wr_frame Usp) KL0 GR0)
  as [KL1 GR1].
clear HF HFr HG0 KL0 GR0.
(* 0x832b8 bnez a0 -> 0x84004 (UBSan ALIGN8 on SA): refuted by W_traps.v trap_align8 from DBASE_x's dxSA cx mod 8 = 0 *)
psrr_branch_tok RUNG BRR HS SHOK pro_Bspan.
{ exfalso.
  rewrite (W_traps.trap_align8 E (SOff 10 0) (dxSA cx) (U_atom E 10 (dxSA cx) E10 ltac:(lia)) HSA8) in Hc.
  discriminate Hc. }
(* 0x832bc .. 0x833bc: the field addresses, g_s, the shadow base and the one-time frame slots, to DI 0x833c0 *)
paj_run_to_tok_xR RUNTOG HS HJ SHOK pro_Bspan A_dr_top. { apply awr_ok_x_of0. awr_ok_tac. all: exact Usp. }
lazymatch type of HFr with frame_of ?Ev ?rs _ _ => let rs' := eval vm_compute in rs in change rs with rs' in HFr end.
destruct (pro_keep E _ (dxW cx) (dxmem cx) _ _ (spZ (dxregs cx)) HFr HG0 ltac:(px_wr_frame Usp) KL1 GR1)
  as [KL2 GR2].
clear HF HFr HG0 KL1 GR1.
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into msF end.
repeat rewrite wvb_collapse in HJ.
(* the registers at the outer loop's head *)
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (20%bv : bv 5) R20. prreg HS (21%bv : bv 5) R21.
prreg HS (22%bv : bv 5) R22. prreg HS (24%bv : bv 5) R24. prreg HS (26%bv : bv 5) R26.
prreg HS (27%bv : bv 5) R27.
px_rreg HS (9%bv : bv 5) R9. px_rreg HS (18%bv : bv 5) R18.
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
pmkst HS.
lazymatch goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?md |} _ => set (md1 := md) end.
set (m1 := ms_mem msF) in *. set (regs1 := ms_regs msF) in *.
(* what the runs keep: everything below the frame *)
assert (Hlo : alloc_ceiling + 8 <= spZ (dxregs cx) - DRAIN_FRAME) by (unfold DRAIN_FRAME; lia).
assert (KEPT : forall a, pro_low a -> abyte_kept (dxW cx) (dxmem cx) (dxW cx) m1 a)
  by (intros a Ha; exact (pro_kept_low B RG HGSB (dxW cx) (dxmem cx) m1 (spZ (dxregs cx)) a KL2 GR2 Hlo Ha)).
assert (HBin : forall b, In b ((dxG cx, ATABLE) :: aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++
  aout_blks (dxcap cx) (dxout cx) ++ dxrest cx) -> In b (ablocks B (dxly cx) (dxS cx)))
  by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact HPERM | exact Hb]).
pose proof HEOK as (Heof & Hsk01 & Hp1 & Hp2 & Hfd & Hcap & HUl & HUa & HU0 & Hbuf & Hnh & Hhp & Hnda & Hndt & Hks).
pose proof HSRC as (_ & _ & _ & _ & _ & _ & Hei01 & _ & _ & _ & _ & _ & _ & _ & Hpo & _ & _ & _ & _ & _ & _ &
  Hexp & _ & _).
pose proof Hexp as (_ & _ & _ & _ & Hen & _).
assert (HHA1 : rg_s RG <= dHA RG cx) by (unfold dHA, ASRC; lia).
assert (HHA2 : dHA RG cx + ASRC <= rg_s RG + 4 * ASRC) by (unfold dHA, ASRC; lia).
pose proof HGSB as (Hg1 & Hg2 & Hg3). unfold IMG_TOP in Hg2.
(* the representations, moved across the runs *)
assert (HEOK1 : aentry_ok B (dxly cx) (dxS cx) (dxW cx) m1 (dxe cx)).
{ apply (aentry_ok_kept B (dxly cx) (dxS cx) (dxW cx) (dxmem cx)); [exact HEOK | |].
  - intros r Hr a Ha. apply KEPT.
    exact (pro_aentry_fp_low_x (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) (dxe cx) HAR HEOK r Hr a Ha).
  - intros b Hb. apply HBin. right. apply in_or_app. left. exact Hb. }
assert (HSRC1 : asrc_at B (dxly cx) (dxS cx) (dxW cx) m1 (dHA RG cx) (dxh cx)).
{ apply (asrc_at_kept B (dxly cx) (dxS cx) (dxW cx) (dxmem cx)); [exact HSRC | |].
  - intros r Hr a Ha. apply KEPT.
    exact (pro_asrc_fp_low_x (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) (dHA RG cx) (dxh cx) HAR HSRC HHA1
      HHA2 r Hr a Ha).
  - intros b Hb. apply HBin. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
assert (HOUT1 : aout_at B RG (dxly cx) (dxS cx) (dxW cx) m1 (dxc cx) (dxO cx) (dxmx cx) (dxno cx) (dxcap cx)
  (dxout cx)).
{ apply (aout_at_kept B RG (dxly cx) (dxS cx) (dxW cx) (dxmem cx)); [exact HOUT | |].
  - intros r Hr a Ha. apply KEPT.
    exact (pro_aout_fp_low_x (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) (dxc cx) (dxO cx) (dxmx cx)
      (dxno cx) (dxcap cx) (dxout cx) HAR HOUT r Hr a Ha).
  - intros b Hb. apply HBin. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    exact Hb. }
assert (HEL : Z.of_nat (length (bzs (entry_bytes (dxe cx)))) = AENT).
{ unfold bzs, entry_bytes. rewrite length_map, !length_app, !Mem.length_le4, !Mem.length_le8, Hp1, Hp2.
  reflexivity. }
assert (KSA : forall x, dxSA cx <= x < dxSA cx + AENT -> abyte_kept (dxW cx) (dxmem cx) (dxW cx) m1 x).
{ intros x Hx. apply KEPT.
  apply (pro_blk_low_x (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) (dxG cx) ATABLE x HAR HGin); [lia|].
  pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as (_ & Hrq). lia. }
assert (KGS : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> abyte_kept (dxW cx) (dxmem cx) (dxW cx) m1 x).
{ intros x Hx. apply KEPT.
  apply (pro_img_low B RG HGSB x (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC, IMG_TOP in *; lia. }
(* the model at round 0 *)
assert (Hlines0 : lines (dSTR cx) [] = []) by reflexivity.
assert (Hctl : dctl cx (Z.of_nat (length (with_nul (lines (dSTR cx) [])))) (ct_ev (dxc cx)) = dxc cx).
{ unfold dctl. rewrite Hlines0. change (Z.of_nat (length (with_nul []))) with 0.
  replace (send_line_c.send_off (ct_cl (dxc cx)) (ct_br (dxc cx)) 0) with true
    by (symmetry; unfold send_line_c.send_off; apply orb_true_r).
  destruct (dxc cx); reflexivity. }
assert (HPS0 : pstream (ds0 cx) = bzs (pending_stream (dxh cx))) by (unfold ds0; apply pro_pstream_init).
assert (HDWF : dwf (ds0 cx)) by (unfold ds0; exact (pro_dwf_init B RG HGSB _ _ _ _ Hpo)).
apply K. unfold DI_xR.
exists regs1, (dxly cx), (dxS cx), Hp, m1, md1, 0, (dxe cx), (dxh cx), (dxout cx), (ct_ev (dxc cx)), [], 0, 0%nat,
  drain_b_c.dadr0, (dtrc cx).
split; [unfold cfg_at; reflexivity|].
split.
{ (* dregs_top: s5 = SA, s8 = SA + 8, s4 = SA + 16, s6 = SA + 24, s11 = SA + 32, s0 = g_s, s1 = g_s >> 3,
     s2 = (g_s + 4) >> 3, s10 = 384 *)
  unfold dregs_top.
  split; [unfold spZ at 1; subst regs1; rewrite R2, Usp, unsigned_lit_small by (unfold DRAIN_FRAME; lia);
    unfold dsp0, DRAIN_FRAME; lia|].
  split; [subst regs1; rewrite R3; exact E3|]. split; [subst regs1; rewrite R4; exact E4|].
  split; [subst regs1; rewrite R21; exact E10|].
  split; [subst regs1; rewrite R24, E10, unsigned_lit_small by lia; reflexivity|].
  split; [subst regs1; rewrite R20, E10, unsigned_lit_small by lia; reflexivity|].
  split; [subst regs1; rewrite R22, E10, unsigned_lit_small by lia; reflexivity|].
  split; [subst regs1; rewrite R27, E10, unsigned_lit_small by lia; reflexivity|].
  split; [subst regs1; rewrite R8; exact EO19|].
  split; [subst regs1; rewrite R9; apply pro_den;
    replace (rg_s RG / 8) with ((rg_s RG + 0) / 8) by (rewrite Z.add_0_r; reflexivity);
    apply (pro_U_srl B RG E 260 (rg_s RG) 0 EO19); unfold ASRC in *; lia|].
  split; [subst regs1; rewrite R18; apply pro_den; apply (pro_U_srl B RG E 260 (rg_s RG) 4 EO19);
    unfold ASRC in *; lia|].
  subst regs1; rewrite R26; reflexivity. }
split.
{ (* DMEM_xR *)
  unfold DMEM_xR.
  split; [exact HJ|].
  split; [exact (pro_rom_moved B RG HGSB (dxW cx) (dxmem cx) m1 (spZ (dxregs cx)) KL2 Hlo HROM)|].
  split; [intros a _ _ _ Hpr; exact (apresent_grows _ _ _ _ GR2 Hpr)|].
  split; [reflexivity|].
  split.
  { unfold dr_frame. cbv zeta.
    pose proof (pro_d8 B RG (dxSA cx) ltac:(lia)) as D0. pose proof (pro_d8 B RG (dxSA cx + 16) ltac:(lia)) as D16.
    pose proof (pro_d8 B RG (dxSA cx + 24) ltac:(lia)) as D24. pose proof (pro_d8 B RG (dxSA cx + 32) ltac:(lia)) as D32.
    pose proof (Z.mod_pos_bound (dxSA cx) 8 ltac:(lia)) as M8.
    assert (GD : forall c, 0 <= c <= 56 -> 0 <= (rg_s RG + c) / 8 < 2 ^ 61)
      by (intros c Hc'; apply (pro_d8 B RG); unfold ASRC in *; lia).
    split; [apply (pro_slot B RG E _ _ _ _ _ _ _ 8
      (SAlu ALU_ADD (SAlu ALU_AND (SOff 10 0) (SLit 7)) (SLit 3)) _ HR0 Usp);
      [cbn; px_in | apply (pro_U_mod8 B RG E (dxSA cx) E10); lia | lia]|].
    split; [apply (pro_slot B RG E _ _ _ _ _ _ _ 32 (SOff 10 48) _ HR0 Usp);
      [cbn; px_in | apply (U_atom_off E 10 (dxSA cx) 48 E10); lia | lia]|].
    split; [apply (pro_slot B RG E _ _ _ _ _ _ _ 40 (SAlu ALU_SRL (SOff 260 8) (SLit 3)) _ HR0 Usp);
      [cbn; px_in | apply (pro_U_srl B RG E 260 (rg_s RG) 8 EO19); unfold ASRC in *; lia
      | pose proof (GD 8 ltac:(lia)); lia]|].
    split; [apply (pro_slot B RG E _ _ _ _ _ _ _ 48 (SAlu ALU_SRL (SOff 260 56) (SLit 3)) _ HR0 Usp);
      [cbn; px_in | apply (pro_U_srl B RG E 260 (rg_s RG) 56 EO19); unfold ASRC in *; lia
      | pose proof (GD 56 ltac:(lia)); lia]|].
    split; [apply (pro_slot B RG E _ _ _ _ _ _ _ 56 (SAlu ALU_SRL (SOff 260 48) (SLit 3)) _ HR0 Usp);
      [cbn; px_in | apply (pro_U_srl B RG E 260 (rg_s RG) 48 EO19); unfold ASRC in *; lia
      | pose proof (GD 48 ltac:(lia)); lia]|].
    split; [apply (pro_slot B RG E _ _ _ _ _ _ _ 64 (SAlu ALU_SRL (SOff 260 40) (SLit 3)) _ HR0 Usp);
      [cbn; px_in | apply (pro_U_srl B RG E 260 (rg_s RG) 40 EO19); unfold ASRC in *; lia
      | pose proof (GD 40 ltac:(lia)); lia]|].
    split; [apply (pro_slot B RG E _ _ _ _ _ _ _ 72 (SAlu ALU_SRL (SOff 260 32) (SLit 3)) _ HR0 Usp);
      [cbn; px_in | apply (pro_U_srl B RG E 260 (rg_s RG) 32 EO19); unfold ASRC in *; lia
      | pose proof (GD 32 ltac:(lia)); lia]|].
    split; [apply (pro_slot B RG E _ _ _ _ _ _ _ 80 (SAlu ALU_SRL (SOff 260 16) (SLit 3)) _ HR0 Usp);
      [cbn; px_in | apply (pro_U_srl B RG E 260 (rg_s RG) 16 EO19); unfold ASRC in *; lia
      | pose proof (GD 16 ltac:(lia)); lia]|].
    split; [apply (pro_slot B RG E _ _ _ _ _ _ _ 88 (SOff 10 40) _ HR0 Usp);
      [cbn; px_in | apply (U_atom_off E 10 (dxSA cx) 40 E10); lia | lia]|].
    split; [apply (pro_slot B RG E _ _ _ _ _ _ _ 104 (SAlu ALU_SRL (SOff 260 24) (SLit 3)) _ HR0 Usp);
      [cbn; px_in | apply (pro_U_srl B RG E 260 (rg_s RG) 24 EO19); unfold ASRC in *; lia
      | pose proof (GD 24 ltac:(lia)); lia]|].
    split; [apply (pro_slot B RG E _ _ _ _ _ _ _ 120 (SOff 260 0) _ HR0 Usp);
      [cbn; px_in | apply (U_atom E 260 (rg_s RG) EO19); unfold ASRC in *; lia | unfold ASRC in *; lia]|].
    split; [apply (pro_slot B RG E _ _ _ _ _ _ _ 128 (SOff 10 16) _ HR0 Usp);
      [cbn; px_in | apply (U_atom_off E 10 (dxSA cx) 16 E10); lia | lia]|].
    split; [apply (pro_slot B RG E _ _ _ _ _ _ _ 136 (SOff 10 24) _ HR0 Usp);
      [cbn; px_in | apply (U_atom_off E 10 (dxSA cx) 24 E10); lia | lia]|].
    split; [apply (pro_slot B RG E _ _ _ _ _ _ _ 144 (SOff 10 0) _ HR0 Usp);
      [cbn; px_in | apply (U_atom E 10 (dxSA cx) E10); lia | lia]|].
    split; [apply (pro_slot B RG E _ _ _ _ _ _ _ 152 (SAlu ALU_SRL (SOff 260 12) (SLit 3)) _ HR0 Usp);
      [cbn; px_in | apply (pro_U_srl B RG E 260 (rg_s RG) 12 EO19); unfold ASRC in *; lia
      | pose proof (GD 12 ltac:(lia)); lia]|].
    split; [apply (pro_slot B RG E _ _ _ _ _ _ _ 176 (SOff 10 32) _ HR0 Usp);
      [cbn; px_in | apply (U_atom_off E 10 (dxSA cx) 32 E10); lia | lia]|].
    split; [apply (pro_slot B RG E _ _ _ _ _ _ _ 184 (SLit 6001) _ HR0 Usp);
      [cbn; px_in | apply U_lit; lia | lia]|].
    split; [apply (pro_slot B RG E _ _ _ _ _ _ _ 200
      (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 32 0)) _ HR0 Usp);
      [cbn; px_in
      | replace (shadow_addr (dxSA cx)) with (SHADOW_OFF + (dxSA cx + 0) / 8)
          by (unfold shadow_addr; rewrite Z.add_0_r; reflexivity);
        apply (pro_U_shadow B RG E 10 (dxSA cx) 0 E10 E32); lia
      | unfold shadow_addr, SHADOW_OFF; lia]|].
    split; [apply (pro_slot B RG E _ _ _ _ _ _ _ 208 (SOff 10 8) _ HR0 Usp);
      [cbn; px_in | apply (U_atom_off E 10 (dxSA cx) 8 E10); lia | lia]|].
    split; [apply (pro_slot B RG E _ _ _ _ _ _ _ 216
      (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 32) (SLit 3)) (SOff 32 0)) _ HR0 Usp);
      [cbn; px_in | apply (pro_U_shadow B RG E 10 (dxSA cx) 32 E10 E32); lia
      | unfold shadow_addr, SHADOW_OFF; lia]|].
    split; [apply (pro_slot B RG E _ _ _ _ _ _ _ 224
      (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 16) (SLit 3)) (SOff 32 0)) _ HR0 Usp);
      [cbn; px_in | apply (pro_U_shadow B RG E 10 (dxSA cx) 16 E10 E32); lia
      | unfold shadow_addr, SHADOW_OFF; lia]|].
    split; [apply (pro_slot B RG E _ _ _ _ _ _ _ 232
      (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 24) (SLit 3)) (SOff 32 0)) _ HR0 Usp);
      [cbn; px_in | apply (pro_U_shadow B RG E 10 (dxSA cx) 24 E10 E32); lia
      | unfold shadow_addr, SHADOW_OFF; lia]|].
    split; [apply (pro_slot B RG E _ _ _ _ _ _ _ 240 (SOff 32 0) _ HR0 Usp);
      [cbn; px_in | apply (U_atom E 32 SB E32); unfold SB; lia | unfold SHADOW_OFF; lia]|].
    unfold dsp0. rewrite <- Usp.
    apply (pro_saved_of_region B RG E (dxW cx) m1 (dxregs cx) _ _ _ _ _ HR0); [px_saved_in | exact EREG]. }
  split; [apply (akept_garr8 (dxW cx) (dxmem cx)); [intros x Hx; apply KSA; lia | exact HENT]|].
  split; [apply (akept_awr (dxW cx) (dxmem cx)); [exact KSA | exact HAWR]|].
  split.
  { (* aentry_okx: aentry_ok with re_used <= re_cap in place of re_used <= APARTIAL and the NUL-freedom *)
    pose proof HEOK1 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15).
    unfold aentry_okx.
    split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|].
    split; [exact B6|]. split; [exact B7|].
    split; [destruct Hbuf as [(A1 & A2 & A3)|(A1 & _)]; unfold APARTIAL in *; lia|].
    split; [exact B10|]. split; [exact B11|]. split; [exact B12|]. split; [exact B13|]. split; [exact B14|].
    exact B15. }
  split; [exact HSRC1|].
  split.
  { intros i Hi Hij. destruct (HOTH i Hi Hij) as (f & o & V1 & V2 & V3). exists f, o.
    split; [apply (akept_vm (dxW cx) (dxmem cx)); [intros x Hx; apply KGS; unfold ASRC in *; lia | exact V1]|].
    split; [apply (akept_vm (dxW cx) (dxmem cx)); [intros x Hx; apply KGS; unfold ASRC in *; lia | exact V2]|].
    exact V3. }
  split; [intros x Hx _; exact (KGS x Hx)|].
  split; [rewrite Hctl, app_nil_r; destruct (dlive cx); exact HOUT1|].
  split; [intros _; split; reflexivity|].
  exact HPERM. }
split; [exact HU0|]. split; [exact HUa|].
split.
{ (* the relay's buffer, when there is one, is a live block: 8-aligned and below the user ceiling *)
  intros Hc0. destruct Hbuf as [(Hcz & _)|(Hcp & Hin & _)]; [lia|].
  destruct (alx_blocks SEGS B ARx LAWS (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) (re_buf (dxe cx))
    (re_cap (dxe cx)) HAR Hin) as (H16 & H4096 & Hceil' & _).
  pose proof (req_size_pos (re_cap (dxe cx)) ltac:(lia)) as (_ & Hrq).
  pose proof (@YM05.alloc_ceiling_value rc) as (ACV & _).
  unfold dinband, DCEIL. split; [lia|]. split; [lia|].
  apply Z.mod_divide in H16; [|lia]. destruct H16 as (q & Hq). rewrite Hq.
  apply Z.mod_divide; [lia|]. exists (2 * q). lia. }
split.
{ (* DLINK at round 0 *)
  unfold DLINK, ds0, drain_b_c.drain_init.
  cbn [drain_b_c.ds_cap drain_b_c.ds_u drain_b_c.ds_skip drain_b_c.ds_H drain_b_c.ds_ka drain_b_c.ds_eintr
       drain_b_c.ds_pend drain_b_c.ds_off drain_b_c.ds_ref drain_b_c.ds_en drain_b_c.ds_ecap].
  split; [reflexivity|]. split; [reflexivity|].
  split; [destruct Hsk01 as [Hs | Hs]; rewrite Hs; reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [destruct Hei01 as [Hs | Hs]; rewrite Hs; reflexivity|].
  do 5 (split; [reflexivity|]).
  exact HDWF. }
split.
{ (* DSAME *)
  unfold DSAME. do 9 (split; [reflexivity|]). left. split; reflexivity. }
split.
{ (* DHIST at round 0 *)
  unfold DHIST. rewrite Hlines0.
  split; [cbn [app]; rewrite HPS0; reflexivity|].
  split; [unfold ds0, drain_b_c.drain_init, dSTR; cbn [drain_b_c.ds_ref]; symmetry; apply feed_nil|].
  split; [cbn [map]; rewrite app_nil_r; reflexivity|].
  split; [apply firstn_all|].
  split; [lia|].
  split; [unfold ds0, drain_b_c.drain_init; cbn [drain_b_c.ds_no]; change (with_nul []) with (@nil Z); cbn; lia|].
  split; [reflexivity|].
  split; [unfold ds0, drain_b_c.drain_init; cbn [drain_b_c.ds_H]; exact (pro_nodup_kt _ Hndt)|].
  split; [unfold ds0, drain_b_c.drain_init; cbn [drain_b_c.ds_H]; intros y; reflexivity|].
  rewrite HPS0. unfold ds0, drain_b_c.drain_init. cbn [drain_b_c.ds_H drain_b_c.ds_en].
  unfold drain_b_c.keys_texts, bzs. rewrite !length_map. unfold re_nheld in HNH. lia. }
split.
{ (* J1 at round 0 *)
  unfold ds0, drain_b_c.drain_init, J1, hs_state. cbn [drain_b_c.ds_u drain_b_c.ds_skip drain_b_c.ds_ref ls_k ls_w].
  split; [rewrite HSK; reflexivity|].
  split; [intros Hk; destruct Hsk01 as [Hs | Hs]; [exact (HSW Hs) | rewrite Hs in Hk; discriminate Hk]|].
  split; [unfold bzs; rewrite length_map; apply Nat2Z.inj_le; rewrite HUl;
    change (Z.of_nat LINE_LIMIT) with 6000; exact HUa|].
  exact (pro_nozero _ HU0). }
split.
{ (* the rounds to come: the whole trace *)
  exists (S (S (length (pending_stream (dxh cx))))).
  split; [unfold dneed; rewrite HPS0; unfold bzs; rewrite length_map;
    destruct (drain_b_c.ds_eintr (ds0 cx)); cbn [Nat.b2n]; lia|].
  split; [exact HDWF|].
  split; [unfold dtrc, dr_tr, drain_b_c.drain_tr, drain_b_c.drain_go, dlive, ds0; reflexivity|].
  unfold dfin, dr_fin, drain_b_c.drain_fin, drain_b_c.drain_go, dlive, ds0. reflexivity. }
(* the budget: nothing spent; the room and the counts are DBASE_x's, at the entry's trace (dbud_x by conversion) *)
unfold dbud_x, dbud.
split; [split; [exact (mo_le_refl MT MTL (dxS cx))|]; split; [lia|];
  split; [unfold dcost, dr_cost, dtrc; lia|]; split; [exact HTA | exact HTM]|].
split; [exact HRM | exact HCNT].
Qed.

End wR.

(* ---- the strict lemmas of this Section at R := wle: each is its R twin above at wle (wle_refl, wle_trans, the
   identity for WLE_R); the statements are the strict ones, checked by conversion. ---- *)
Theorem dr_pro_x : dr_pro_stmt_x B PST ARx MT RP MMAX RG.
Proof. eapply (dr_pro_xR (@wle SEGS)). all: first [ exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun (W W' : world SEGS) (H : @wle SEGS W W') => H) ]. Qed.
End cx.
End b.
End a.
