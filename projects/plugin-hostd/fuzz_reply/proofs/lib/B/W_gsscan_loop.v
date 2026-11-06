(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the held-key search loop of segment GS of the ASan+UBSan walk (image B,
   fuzz_reply.asan-ubsan) of fuzz_reply's drain, 0x83b34 .. 0x83b9c with its exits 0x83ba0 (GA), 0x83cb4 (GF)
   and 0x83d9c -> 0x839d4 (DLN (S q)).  Proves no function (kind: segment lemma of drain's image-B walk, GS piece
   gs_scan).  The statement is lib/B/W_gsscan_cx.v's gs_scan_loop_stmt; the Section header is lib/B/W_drain_gs.v's.
   In the form of image A's lib/A/W_gsscanb.v (a working branch 0c06ccc287f):
     gsc_body : GSL n (S kf) -> GSN n (S kf) | DLN (S q) | GF
     gsc_tail : GSN n (S kf) -> GSL (S n) kf (kf > 0) | GA (kf = 0)
   and gs_scan_loop is the induction on the external kf.  The loop's two UBSan traps the engine leaves open
   are refuted with the trap kit (lib/B/W_traps.v, a working branch 6c73ae99620): 0x83b38
   `bltu s10,s6` by trap_ptr_wrap_atom (s10 = atom 32 = hp + 8 n, s6 = atom 22 = hp), 0x83b44 `beqz (s9 xor
   0)` by trap_null_xor_folded (s9 = atom 25 = 1).  The third, 0x83b4c `beqz 168(sp)`, and the shadow check of
   &held[n] (0x83b60) are decided inside the run from the seat (atom 35 = 1; gl_SH over atom 32). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_model.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_sites W_contract W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_place W_drain_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_drain_gs W_drain_gs_model W_drain_gs_aux.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_traps W_gsscan_cx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Notation dtrace := (list (RelayRunT.rev YO0i.sptr)).
#[local] Notation dadrF := (RelayRunT.addr YO0i.sptr).

(* prreg without the denotation's normal form: the register's symbolic value as the state holds it *)
Ltac gsl_prreg_raw HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.

(* after a run whose regions have no write window: KP : GSKEEP cx W m1 m0 becomes GSKEEP cx W m1 m *)
Ltac gsl_absorb KP :=
lazymatch goal with
| Hf : frame_of _ _ (mrestrict (w_H ?W) ?m0) (mrestrict (w_H ?W) ?m),
  Hg : mem_grows (mrestrict (w_H ?W) ?m0) (mrestrict (w_H ?W) ?m) |- _ =>
  let K := fresh "KPn" in let ya := fresh "ya" in let Hya := fresh "Hya" in
  assert (K : GSKEEP _ W _ m) by
    (apply (gsc_keep_trans _ _ _ m0 m KP); split;
     [ intros ya Hya _; exact (gsc_frame_nil _ _ _ _ _ Hf ltac:(vm_compute; reflexivity) ya Hya)
     | intros ya Hya; exact (apresent_grows _ _ _ ya Hg Hya) ]);
  clear Hf Hg KP; rename K into KP
end.

Ltac gsl_clear_br := repeat match goal with Hb : branch_taken _ _ _ = _ |- _ => clear Hb end.

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

(* GSN from the head's body at a later memory: slot n not matched *)
Lemma gsl_exit_gsn : forall cx s1 D p q n kf W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg
  regs2 m2 md2,
DBASE B MT MMAX RG cx ->
GSBODY B MT MMAX RG cx s1 D p q n kf n W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m2 md2 k1 ->
GSKEEP cx W1 m1 m2 ->
GSREGS regs1 regs2 -> getr regs2 19 = getr regs1 19 -> getr regs2 20 = getr regs1 20 ->
nth n (dlH cx s1 p) [] <> firstn jj (dline s1 p q) ->
GSN B MT MMAX RG cx s1 D p q n kf W1 (cfg_at SEGS (BASE + A_dr_hnext) regs2 m2 md2).
Proof using LAWS HG HGSB HV9 HSD HSM.
intros cx s1 D p q n kf W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg regs2 m2 md2
  HB HBD HJ HKP HR Q19 Q20 Hn.
exists regs2, ly1, S1, m2, md2, k1, e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl, kd, jj, bg.
split; [reflexivity|].
apply (gsc_mk_gsn B MT MMAX RG cx s1 D p q n kf W1 regs1 ly1 S1 m2 md2 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg regs2);
  [| exact HR | exact Q19 | exact Q20 | exact Hn].
exact (gsc_body_keep B MT MMAX RG LAWS HG HGSB HV9 HSD HSM cx s1 D p q n kf n W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1
  LB1 spent jb a o ha ks tl kd jj bg m2 md2 HB HBD HJ HKP).
Qed.

(* ---- The loop's bottom: GSN n (S kf) -> GSL (S n) kf when a slot is left, GA when none is. ---- *)
Lemma gsl_tail : forall cx s1 D p q n kf W1 c1,
DBASE B MT MMAX RG cx -> GSN B MT MMAX RG cx s1 D p q n (S kf) W1 c1 ->
(forall W2 c2, GA B MT MMAX RG cx s1 D p q W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
((0 < kf)%nat -> forall c2, GSL B MT MMAX RG cx s1 D p q (S n) kf W1 c2 -> SRr SEGS W1 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).
Proof using LAWS HG ASTRNCMP ASTRLEN ALLOC_TAIL HGSB HV9 HSD HSM. clear HGR HROMO HGO MTL TL AERRNO AMEMCPY AMEMMOVE AMEMCHR HCROM ASTRRCHR ASTRCMP AREALLOC AFREE ASTRNDUP SLSPEC LPSPEC HERRNO HERRZ HERRW HERRAL HGSZ HVS HLIT5 HLIT6 HLIT7 HRGD HMMAX.
intros cx s1 D p q n kf W1 c1 HB HGN HGA HGL.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HGN as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & oo & ha & ks & tl
  & kd & jj & bg & Hcfg & HBD).
destruct (gsc_stack B MT MMAX RG cx HB) as (HSTK1 & HSTK2 & Hal16 & Hj4).
pose proof HBD as (HRG & M0 & M16 & M24 & M96 & M112 & M160 & M168 & M192 & R23 & R24 & R19 & R20 & R22 & R25
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hband & Hcap & Hgest & Hjjr & HGSF & HCORE & HFUT).
pose proof HRG as (Hsp & R3 & R4 & R8 & R9 & R18 & HFR).
pose proof HFR as (F8 & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F88 & F104 & F120 & F128 & F136 & F144 & F152
  & F176 & _).
pose proof HCORE as (HMEM & HLINK & _).
pose proof HMEM as (HJ & _ & _ & _ & _ & _ & _ & HOKX & _).
destruct (gsc_sa B MT MMAX RG LAWS cx _ _ _ _ _ _ _ _ _ _ _ _ _ HB HMEM) as (HSA1 & HSA2).
pose proof HOKX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hnheld & _).
assert (HNHR : 0 <= re_nheld e1 < 2 ^ 26) by (split; [unfold re_nheld; lia | exact Hnheld]).
assert (HDF : DRAIN_FRAME = 352) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
pose proof (gn_entry W1 regs1 m1 (dsp0 cx - DRAIN_FRAME) (8 * re_nheld e1) (dxSA cx) (Z.of_nat (S kf))
  Hsp ltac:(lia) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity)
  R19 ltac:(unfold re_nheld in HNHR; lia) ltac:(lia) ltac:(lia) ltac:(lia) M160 F176) as HS.
remember (Eimg (Ereg regs1 (gn_extra (8 * re_nheld e1) (dxSA cx)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n0 r Hn Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 (8 * re_nheld e1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (dxSA cx)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E19 : ew E 19 = Z_to_bv 64 (Z.of_nat (S kf))) by (rewrite (EREG 19%nat 19%bv ltac:(lia) eq_refl), R19; reflexivity).
assert (E20 : ew E 20 = Z_to_bv 64 (8 * Z.of_nat n)) by (rewrite (EREG 20%nat 20%bv ltac:(lia) eq_refl), R20; reflexivity).
assert (SHOK : sh_ok SEGS gn_Bx [] E (mrestrict (w_H W1) m1)) by constructor.
clear HE.
subst c1. unfold cfg_at. change (w64 (BASE + A_dr_hnext)) with (Z_to_bv 64 (BASE + A_dr_hnext)).
assert (KP : GSKEEP cx W1 m1 m1) by (split; [intros; reflexivity | intros; assumption]).
paj_run_tok RUN HS HJ SHOK gl_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
gsl_absorb KP.
assert (Hn8 : 0 <= 8 * Z.of_nat n + 8 < 2 ^ 64) by (unfold re_nheld in HNHR; lia).
assert (Hh8 : 0 <= 8 * re_nheld e1 < 2 ^ 64) by lia.
psrr_branch_tok RUN BR HS SHOK gl_Bspan.
- (* a slot is left (8 nheld <> 8 (n + 1)): back to the loop's head at S n *)
  rewrite branch_ne_U, (U_atom E 32 (8 * re_nheld e1) E32 Hh8), (U_atom_off E 20 (8 * Z.of_nat n) 8 E20 ltac:(lia) Hn8) in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  assert (Hkf0 : (0 < kf)%nat) by (clear - Hc Hnk; unfold re_nheld in Hc; lia).
  paj_run_to_tok RUNTO HS HJ SHOK gl_Bspan A_dr_hloop. { apply awr_ok_x_of0. awr_ok_tac. }
  gsl_absorb KP.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
  prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
  repeat rewrite wvb_collapse in HJ.
  match goal with |- SRr _ _ {| cfg_ms := mkst ?rx _ ?mx _; cfg_model := ?mdx |} _ =>
    set (mdF := mdx) in *; set (mF := mx) in *; set (regsF := rx) in * end.
  clear HS SHOK.
  assert (RK : forall (r : bv 5) (k : nat), getr regsF r = ew E k -> Nat.ltb k 32 = true ->
    Z.of_nat k = bv_unsigned r -> getr regsF r = getr regs1 r) by
    (intros r k Hr Hk Hkr; rewrite Hr; apply EREG; [apply Nat.ltb_lt; exact Hk | exact Hkr]).
  apply (HGL Hkf0).
  exists regsF, ly1, S1, mF, mdF, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, oo, ha, ks, tl, kd, jj, bg.
  split; [reflexivity|].
  apply (gsc_mk_loop B MT MMAX RG cx s1 D p q n kf W1 regs1 ly1 S1 mF mdF k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl kd jj bg).
  + exact (gsc_body_keep B MT MMAX RG LAWS HG HGSB HV9 HSD HSM cx s1 D p q n (S kf) (S n) W1 regs1 ly1 S1 m1 md1 k1 e1 h1
      out1 ev1 LB1 spent jb aa oo ha ks tl kd jj bg mF mdF HB HBD HJ KP).
  + exact Hkf0.
  + split; [exact (RK _ 2%nat P2 eq_refl eq_refl)|]. split; [exact (RK _ 3%nat P3 eq_refl eq_refl)|].
    split; [exact (RK _ 4%nat P4 eq_refl eq_refl)|]. split; [exact (RK _ 8%nat P8 eq_refl eq_refl)|].
    split; [exact (RK _ 9%nat P9 eq_refl eq_refl)|]. split; [exact (RK _ 18%nat P18 eq_refl eq_refl)|].
    split; [exact (RK _ 22%nat P22 eq_refl eq_refl)|]. split; [exact (RK _ 23%nat P23 eq_refl eq_refl)|].
    split; [exact (RK _ 24%nat P24 eq_refl eq_refl) | exact (RK _ 25%nat P25 eq_refl eq_refl)].
  + rewrite P19, E19, unsigned_lit_small by (unfold re_nheld in HNHR; lia). unfold w64. f_equal. lia.
  + rewrite P20, E20, unsigned_lit_small by (unfold re_nheld in HNHR; lia). unfold w64. f_equal. lia.
- (* no slot is left (8 nheld = 8 (n + 1)): s11 = 176(sp), on to GA *)
  rewrite branch_ne_U, (U_atom E 32 (8 * re_nheld e1) E32 Hh8), (U_atom_off E 20 (8 * Z.of_nat n) 8 E20 ltac:(lia) Hn8) in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc.
  assert (Hkf0 : kf = 0%nat) by (clear - Hc Hnk; unfold re_nheld in Hc; lia). subst kf.
  paj_run_to_tok RUNTO HS HJ SHOK gl_Bspan A_dr_add. { apply awr_ok_x_of0. awr_ok_tac. }
  gsl_absorb KP.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24.
  prreg HS (27%bv : bv 5) P27.
  repeat rewrite wvb_collapse in HJ.
  match goal with |- SRr _ _ {| cfg_ms := mkst ?rx _ ?mx _; cfg_model := ?mdx |} _ =>
    set (mdF := mdx) in *; set (mF := mx) in *; set (regsF := rx) in * end.
  clear HS SHOK.
  assert (RK : forall (r : bv 5) (k : nat), getr regsF r = ew E k -> Nat.ltb k 32 = true ->
    Z.of_nat k = bv_unsigned r -> getr regsF r = getr regs1 r) by
    (intros r k Hr Hk Hkr; rewrite Hr; apply EREG; [apply Nat.ltb_lt; exact Hk | exact Hkr]).
  apply HGA.
  apply (gsc_mk_ga B MT MMAX RG cx s1 D p q n W1 regs1 ly1 S1 mF mdF k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl kd jj bg
    _ (gsc_body_keep B MT MMAX RG LAWS HG HGSB HV9 HSD HSM cx s1 D p q n 1 (S n) W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1
      LB1 spent jb aa oo ha ks tl kd jj bg mF mdF HB HBD HJ KP)
    (RK _ 2%nat P2 eq_refl eq_refl) (RK _ 3%nat P3 eq_refl eq_refl) (RK _ 4%nat P4 eq_refl eq_refl)
    (RK _ 8%nat P8 eq_refl eq_refl) (RK _ 9%nat P9 eq_refl eq_refl) (RK _ 18%nat P18 eq_refl eq_refl)
    (RK _ 23%nat P23 eq_refl eq_refl) (RK _ 24%nat P24 eq_refl eq_refl)).
  rewrite P27, E33, unsigned_lit_small by lia. reflexivity.
Qed.

(* ---- The loop's body: GSL n (S kf) -> GSN n (S kf) (no match at slot n), DLN (S q) (a begin held at slot n)
   or GF (an end held at slot n). ---- *)
Lemma gsl_body : forall cx s1 D p q n kf W1 c1,
DBASE B MT MMAX RG cx -> GSL B MT MMAX RG cx s1 D p q n (S kf) W1 c1 ->
(forall W2 c2, DLN B MT MMAX RG cx s1 D (S q) W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
(forall W2 c2, GF B MT MMAX RG cx s1 D p q W2 c2 -> SRr SEGS W2 c2 (dPOST B MT RG cx)) ->
(forall c2, GSN B MT MMAX RG cx s1 D p q n (S kf) W1 c2 -> SRr SEGS W1 c2 (dPOST B MT RG cx)) ->
SRr SEGS W1 c1 (dPOST B MT RG cx).
Proof using LAWS HG ASTRNCMP ASTRLEN ALLOC_TAIL HGSB HV9 HSD HSM. clear HGR HROMO HGO MTL TL AERRNO AMEMCPY AMEMMOVE AMEMCHR HCROM ASTRRCHR ASTRCMP AREALLOC AFREE ASTRNDUP SLSPEC LPSPEC HERRNO HERRZ HERRW HERRAL HGSZ HVS HLIT5 HLIT6 HLIT7 HRGD HMMAX.
intros cx s1 D p q n kf W1 c1 HB HGL HDLN HGF HGN.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@ASAN_CEIL_range rc) as (HAC & _). unfold ASAN_CEIL in HAC.
destruct HGL as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & oo & ha & ks & tl
  & kd & jj & bg & Hcfg & HBD).
destruct (gsc_stack B MT MMAX RG cx HB) as (HSTK1 & HSTK2 & Hal16 & Hj4).
pose proof HBD as (HRG & M0 & M16 & M24 & M96 & M112 & M160 & M168 & M192 & R23 & R24 & R19 & R20 & R22 & R25
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hband & Hcap & Hgest & Hjjr & HGSF & HCORE & HFUT).
pose proof HRG as (Hsp & R3 & R4 & R8 & R9 & R18 & HFR).
pose proof HFR as (F8 & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F88 & F104 & F120 & F128 & F136 & F144 & F152
  & F176 & F184 & F200 & F208 & F216 & F224 & F232 & F240 & _).
pose proof HCORE as (HMEM & HLINK & _).
pose proof HMEM as (HJ & Hrom & _ & _ & _ & _ & _ & HOKX & _).
destruct (gsc_sa B MT MMAX RG LAWS cx _ _ _ _ _ _ _ _ _ _ _ _ _ HB HMEM) as (HSA1 & HSA2).
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
pose proof HOKX as (_ & _ & _ & _ & _ & Hcapr & HUlen & Husedr & Hbufc & Hnheld & Hheld & _ & _ & Hkeys).
assert (Hnlen : (n < length (re_keys e1))%nat) by lia.
destruct Hheld as [(Hz & Hk0) | (Hz & Hin & Hk1 & Hk2 & Hg8)]; [rewrite Hk0 in Hnlen; cbn [length] in Hnlen; lia|].
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (re_hp e1) (re_kh e1) HAR Hin) as (HH16 & HH4096 & HHceil & HHia & _).
assert (Hrq : re_kh e1 <= req_size (re_kh e1)) by (unfold req_size; destruct (Z.eqb_spec (re_kh e1) 0); lia).
assert (HHP8 : re_hp e1 mod 8 = 0).
{ rewrite (Z.div_mod (re_hp e1) 16) by lia. rewrite HH16, Z.add_0_r.
  replace (16 * (re_hp e1 / 16)) with ((2 * (re_hp e1 / 16)) * 8) by lia. apply Z.mod_mul. lia. }
set (kn := nth n (re_keys e1) (0, [], [])).
assert (Hkn : In kn (re_keys e1)) by (apply nth_In; exact Hnlen).
rewrite Forall_forall in Hkeys. destruct (Hkeys kn Hkn) as (HKin & HKg & HKnz & HKlen).
unfold APARTIAL in HKlen.
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (key_addr kn) (Z.of_nat (length (key_text kn)) + 1) HAR HKin)
  as (HK16 & HK4096 & HKceil & HKia & _).
assert (RQK : req_size (Z.of_nat (length (key_text kn)) + 1) = Z.of_nat (length (key_text kn)) + 1)
  by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length (key_text kn)) + 1) 0); lia).
rewrite RQK in HKceil, HKia.
pose proof (gsc_slot_val W1 m1 (re_hp e1) (re_keys e1) n Hg8 Hnlen ltac:(change (nth n (re_keys e1) (0, [], [])) with kn; lia))
  as MSL. fold kn in MSL.
pose proof (gsc_link_U _ _ _ _ _ _ _ _ _ HLINK) as HUW.
assert (HUL : re_used e1 = Z.of_nat (length (dW s1))) by (rewrite <- HUW, gsc_bzs_len; lia).
pose proof HGSF as (Hbd & Hpq & Hq0 & Hnzl & Hskp & Hlim).
assert (Hcap0 : re_cap e1 <> 0) by lia.
destruct Hbufc as [(Hc0 & _) | (Hcpos & Hbin & Hjunk & Hbuf8)]; [lia|].
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (re_buf e1) (re_cap e1) HAR Hbin) as (HB16 & HB4096 & HBceil & HBia & _).
assert (RQC : req_size (re_cap e1) = re_cap e1) by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
rewrite RQC in HBceil, HBia.
pose proof (gsc_line_garr8 W1 m1 s1 p q e1 Hbuf8 HUW ltac:(lia)) as HLg.
unfold re_nheld in Hnheld, Hk1.
assert (HDF : DRAIN_FRAME = 352) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
assert (HDS : DRAIN_STK = 16880) by reflexivity.
pose proof (gl_entry W1 regs1 m1 (dsp0 cx - DRAIN_FRAME) (re_hp e1) n (Z.of_nat (S kf)) (key_addr kn) (Z.of_nat jj)
  (dxSA cx) bg (8 * re_nheld e1)
  Hsp ltac:(lia) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity)
  R19 ltac:(lia) R20 ltac:(lia) R22 R25
  HH4096 HHP8 ltac:(unfold GL_PHI; lia) ltac:(lia) ltac:(unfold GL_PHI; lia)
  ltac:(lia) ltac:(lia) ltac:(lia) Hbgr ltac:(unfold re_nheld; lia)
  M24 F128 F136 F144 M160 M168 F176 M192 F240 MSL) as HS.
remember (Eimg (Ereg regs1 (gl_extra (re_hp e1 + 8 * Z.of_nat n) (key_addr kn) (Z.of_nat jj) (dxSA cx) bg
  (8 * re_nheld e1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall k (r : bv 5), (k < 32)%nat -> Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r).
{ intros k r Hk Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. lia. }
assert (E22 : ew E 22 = Z_to_bv 64 (re_hp e1)) by (rewrite (EREG 22%nat 22%bv ltac:(lia) eq_refl); exact R22).
assert (E25 : ew E 25 = Z_to_bv 64 1) by (rewrite (EREG 25%nat 25%bv ltac:(lia) eq_refl); exact R25).
assert (E32 : ew E 32 = Z_to_bv 64 (re_hp e1 + 8 * Z.of_nat n)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (key_addr kn)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E36 : ew E 36 = Z_to_bv 64 (Z.of_nat jj)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (dxSA cx)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 bg) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 6)).
assert (SHOK : sh_ok SEGS gl_Bx gl_SH E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W1) m1 E gl_Bx 32 (re_hp e1 + 8 * Z.of_nat n) 8 (re_hp e1 + 8 * Z.of_nat n) 0 8).
  - apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 m1 md1 (re_hp e1) (re_kh e1)); [exact HAR | exact Hin | lia | lia].
  - unfold gl_Bx. rewrite (U_atom E 34 SHADOW_OFF E34) by (unfold SHADOW_OFF; lia). reflexivity.
  - apply (U_atom E 32 _ E32). lia.
  - lia.
  - lia.
  - intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
    unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *. lia. }
clear HE.
subst c1. unfold cfg_at. change (w64 (BASE + A_dr_hloop)) with (Z_to_bv 64 (BASE + A_dr_hloop)).
assert (KP : GSKEEP cx W1 m1 m1) by (split; [intros; reflexivity | intros; assumption]).
(* 0x83b34 .. the PTR_BLTU trap at 0x83b38 *)
paj_run_tok RUN HS HJ SHOK gl_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
gsl_absorb KP.
psrr_branch_tok RUN BR HS SHOK gl_Bspan.
{ exfalso. rewrite (trap_ptr_wrap_atom E 32 22 (re_hp e1) (8 * Z.of_nat n) E32 E22 ltac:(lia) ltac:(lia) ltac:(lia)) in Hc.
  discriminate Hc. }
gsl_clear_br.
(* .. the folded NULL_XOR trap at 0x83b44 *)
paj_run_tok RUN HS HJ SHOK gl_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
gsl_absorb KP.
psrr_branch_tok RUN BR HS SHOK gl_Bspan.
{ exfalso. rewrite (trap_null_xor_folded E 25 E25) in Hc. discriminate Hc. }
gsl_clear_br.
(* .. 168(sp) and the shadow of &held[n] decided, held[n], to strlen at 0x83b6c *)
paj_run_tok RUN HS HJ SHOK gl_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
gsl_absorb KP.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10.
repeat rewrite wvb_collapse in HJ.
match goal with |- SRr _ _ {| cfg_ms := mkst ?rx _ ?mx _; cfg_model := ?mdx |} _ =>
  set (mdm := mdx) in *; set (mA := mx) in *; set (regsA := rx) in * end.
clearbody mdm.
pose proof KP as (KEEPA & PRESA).
assert (HARm : AR SEGS B ly1 S1 W1 mA mdm) by (eapply ajournal_gx_AR; exact HJ).
assert (KLA : forall y, 0 <= y < alloc_ceiling -> aview SEGS (w_H W1) mA y = aview SEGS (w_H W1) m1 y)
  by (intros y Hy; apply KEEPA; [lia | unfold ESTACK, DRAIN_FRAME in *; lia]).
assert (ROM1 : rom_view SEGS W1 mA).
{ intros y Hy. rewrite KLA; [exact (Hrom y Hy)|].
  destruct Hy as (sg & Hsg & _ & Hr). pose proof (pa_img_range y ltac:(exists sg; split; [exact Hsg | exact Hr])). lia. }
pose proof HB as (Hafn & _). pose proof Hafn as (_ & _ & _ & Hgp & Htp & _).
assert (Usp1 : spZ regsA = dsp0 cx - DRAIN_FRAME)
  by (unfold spZ; rewrite Q2, (EREG 2%nat 2%bv ltac:(lia) eq_refl); exact Hsp).
assert (G3 : getr regsA 3 = w64 (as_gp B)) by (rewrite Q3, (EREG 3%nat 3%bv ltac:(lia) eq_refl), R3; exact Hgp).
assert (G4 : getr regsA 4 = w64 (as_tp B)) by (rewrite Q4, (EREG 4%nat 4%bv ltac:(lia) eq_refl), R4; exact Htp).
set (x := key_addr kn) in *. set (klen := Z.of_nat (length (key_text kn))) in *.
assert (G10 : getr regsA 10 = w64 x) by (rewrite Q10, E33; reflexivity).
assert (HKg1 : garr8 SEGS (arm W1 mA) x (bzs (key_text kn ++ [Z_to_bv 8 0]))).
{ apply (gsc_garr8_kept W1 m1 W1 mA); [exact HKg|]. intros y Hy. apply KLA.
  rewrite gsc_bzs_len, length_app in Hy. cbn [length] in Hy. unfold klen, x in *. lia. }
assert (HKL : Z.to_nat klen = length (key_text kn)) by (unfold klen; lia).
(* strlen (held[n]) *)
eapply SRr_bind.
{ eapply (aj_gx_entry_at B LAWS (G_DR B RG) 0 ([] : list (Z * Z)) (2 * ESTACK) (SIGMA WS_strlen)
    (fun _ => False) (fun regs' (_ : word -> option byte) => getr regs' 10 = w64 klen)
    W1 regsA mA DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx)
    ([] : list (Z * Z)) ly1 S1 _ k1 (- DRAIN_FRAME) (Z_to_bv 64 (BASE + 6188)) HG eq_refl HJ).
  - rewrite Usp1. lia.
  - rewrite HDF. reflexivity.
  - lia.
  - lia.
  - lia.
  - exact G3.
  - exact G4.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros _. right. intros [].
  - intros y [].
  - intros y [].
  - intros HPRE HSC. eapply SRr_mono.
    { refine (ASTRLEN ly1 S1 W1 regsA mA mdm x klen HPRE (proj1 HSC) (proj2 HSC) G10
        ltac:(unfold x, klen in *; lia) ltac:(unfold x, klen in *; lia) ltac:(unfold x, klen in *; lia) ltac:(unfold x, klen in *; lia) _ _ _ _ _ _ _ _ ROM1).
      - apply (gsc_first_byte W1 mA x (bzs (key_text kn ++ [Z_to_bv 8 0])) (klen + 1) klen HKg1).
        + unfold klen in *; lia.
        + rewrite gsc_bzs_len, length_app. cbn [length]. unfold klen in *. lia.
        + intros i Hi. apply (gsc_key_nz _ HKnz). lia.
        + intros _. rewrite HKL. apply gsc_key_z.
      - intros y Hy. split.
        + replace y with (x + Z.of_nat (Z.to_nat (y - x))) by lia.
          rewrite (gsc_aview_garr8 W1 mA x _ _ HKg1); [discriminate|].
          rewrite gsc_bzs_len, length_app. cbn [length]. unfold klen in *. lia.
        + rewrite Usp1. unfold x, klen in *. lia.
      - intros y Hy. rewrite Usp1. unfold x, klen in *. lia.
      - unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in HKia |- *.
        unfold x, klen in *. lia.
      - unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in HKia |- *.
        unfold x, klen in *. lia.
      - apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 mA mdm x (klen + 1));
          [exact HARm | exact HKin | lia | unfold klen, x in *; rewrite RQK; lia].
      - apply (shadow_hull_vis_of_block SEGS B LAWS ly1 S1 W1 mA mdm x (klen + 1));
          [exact HARm | exact HKin | lia | unfold klen, x in *; rewrite RQK; lia | unfold klen in *; lia].
      - intros y Hy. apply (ALLOC_TAIL ly1 S1 W1 mA mdm x (klen + 1) y HARm HKin). unfold klen, x in *. rewrite RQK.
        replace (key_addr kn + (Z.of_nat (length (key_text kn)) + 1) - 1) with (key_addr kn + Z.of_nat (length (key_text kn))) by lia.
        exact Hy. }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpr).
    split; [reflexivity|]. exists regs2, mem2, md2.
    split; [reflexivity|]. split; [exact HAR2|]. split; [exact HP|]. split; [exact Hsame|]. split; [exact Hres|].
    split; [intros y Hy _ Hs; exact (Hfr y Hy Hs) | exact Hpr]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hres & Hfr2 & Hpres2).
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0%nat] HS2.
assert (Usp0 : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME)
  by (rewrite (EREG 2%nat 2%bv ltac:(lia) eq_refl); exact Hsp).
assert (HRK : region_kept SEGS E (mrestrict (w_H W1) mA) (mrestrict (w_H W1) mem2) gl_frame).
{ split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi gl_frame base_val]; rewrite Usp0;
    intros y Hy; [|lia].
  apply (mbyte_of_aview SEGS). apply Hfr2; [clear - Hy HSTK1 HSTK2 C1; unfold ESTACK, DRAIN_FRAME in *; lia | intros [] | clear - Hy; unfold ESTACK in *; lia]. }
specialize (HS2 ltac:(constructor; [exact HRK | constructor])).
clear HS HRK. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 40 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 40)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
prreg HS (10%bv : bv 5) R10b.
assert (A44 : ew Ea 44 = Z_to_bv 64 klen) by (rewrite <- R10b, Hres; reflexivity).
assert (A36 : ew Ea 36 = Z_to_bv 64 (Z.of_nat jj)) by (rewrite (OLDa 36%nat ltac:(lia)); exact E36).
assert (SHOK2 : sh_ok SEGS gl_Bx [] Ea (mrestrict (w_H W1) mem2)) by constructor.
assert (KP2 : GSKEEP cx W1 m1 mem2).
{ split.
  - intros y Hy Hs. rewrite (Hfr2 y Hy (fun H => H) ltac:(clear - Hs; unfold ESTACK in *; lia)). exact (KEEPA y Hy Hs).
  - intros y Hp. apply Hpres2. exact (PRESA y Hp). }
clear KP KEEPA PRESA Hfr2 Hpres2. rename KP2 into KP.
(* 0x83b70 ld a1,192(sp); bne a0,a1 *)
paj_run_tok RUN HS HJ2 SHOK2 gl_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
gsl_absorb KP.
assert (Hk64 : 0 <= klen < 2 ^ 64) by (unfold klen in *; lia).
assert (Hj64 : 0 <= Z.of_nat jj < 2 ^ 64) by lia.
psrr_branch_tok RUN BR HS SHOK2 gl_Bspan.
- (* |held[n]| <> jj: no match at slot n *)
  rewrite branch_ne_U, (U_atom Ea 44 klen A44 Hk64), (U_atom Ea 36 (Z.of_nat jj) A36 Hj64) in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ2 SHOK2 gl_Bspan A_dr_hnext. { apply awr_ok_x_of0. awr_ok_tac. }
  gsl_absorb KP.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
  prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
  repeat rewrite wvb_collapse in HJ2.
  match goal with |- SRr _ _ {| cfg_ms := mkst _ _ ?mx _; cfg_model := ?mdx |} _ => set (mdF := mdx) in *; set (mF := mx) in * end.
  clear HS SHOK2.
  assert (RK : forall (r : bv 5) (k : nat) rr, getr rr r = ew Ea k -> Nat.ltb k 32 = true ->
    Z.of_nat k = bv_unsigned r -> getr rr r = getr regs1 r).
  { intros r k rr Hr Hk Hkr. apply Nat.ltb_lt in Hk. rewrite Hr, (OLDa k ltac:(lia)). apply EREG; [exact Hk | exact Hkr]. }
  apply HGN.
  apply (gsl_exit_gsn cx s1 D p q n (S kf) W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl kd jj bg
    _ mF mdF HB HBD HJ2 KP).
  + split; [exact (RK _ 2%nat _ P2 eq_refl eq_refl)|]. split; [exact (RK _ 3%nat _ P3 eq_refl eq_refl)|].
    split; [exact (RK _ 4%nat _ P4 eq_refl eq_refl)|]. split; [exact (RK _ 8%nat _ P8 eq_refl eq_refl)|].
    split; [exact (RK _ 9%nat _ P9 eq_refl eq_refl)|]. split; [exact (RK _ 18%nat _ P18 eq_refl eq_refl)|].
    split; [exact (RK _ 22%nat _ P22 eq_refl eq_refl)|]. split; [exact (RK _ 23%nat _ P23 eq_refl eq_refl)|].
    split; [exact (RK _ 24%nat _ P24 eq_refl eq_refl) | exact (RK _ 25%nat _ P25 eq_refl eq_refl)].
  + exact (RK _ 19%nat _ P19 eq_refl eq_refl).
  + exact (RK _ 20%nat _ P20 eq_refl eq_refl).
  + rewrite (gsc_nth_H _ _ _ _ _ _ _ _ _ n HLINK Hnlen). fold kn. intros Heq.
    apply (f_equal (@length Z)) in Heq. rewrite gsc_bzs_len, length_firstn, (gs_dline_len s1 p q Hpq) in Heq.
    clear - Heq Hc Hjjr. unfold klen in Hc. lia.
- (* |held[n]| = jj: strncmp (held[n], s->buf + p, jj) *)
  rewrite branch_ne_U, (U_atom Ea 44 klen A44 Hk64), (U_atom Ea 36 (Z.of_nat jj) A36 Hj64) in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hkj.
  paj_run_tok RUN HS HJ2 SHOK2 gl_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
  gsl_absorb KP.
  pmkst HS.
  prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
  prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12.
  repeat rewrite wvb_collapse in HJ2.
  match goal with |- SRr _ _ {| cfg_ms := mkst ?rx _ ?mx _; cfg_model := ?mdx |} _ =>
    set (mdc := mdx) in *; set (mC := mx) in *; set (regsC := rx) in * end.
  clearbody mdc.
  assert (HARc : AR SEGS B ly1 S1 W1 mC mdc) by (eapply ajournal_gx_AR; exact HJ2).
  pose proof KP as (KC & PC).
  assert (KLC : forall z, 0 <= z < alloc_ceiling -> aview SEGS (w_H W1) mC z = aview SEGS (w_H W1) m1 z)
    by (intros z Hw; apply KC; [clear - Hw C1; lia | clear - Hw HSTK1; unfold ESTACK, DRAIN_FRAME in *; lia]).
  assert (ROMc : rom_view SEGS W1 mC).
  { intros z Hw. rewrite KLC; [exact (Hrom z Hw)|].
    destruct Hw as (sg & Hsg & _ & Hr). pose proof (pa_img_range z ltac:(exists sg; split; [exact Hsg | exact Hr])).
    clear - H C1. lia. }
  set (y := re_buf e1 + Z.of_nat p) in *.
  assert (Usp2 : spZ regsC = dsp0 cx - DRAIN_FRAME)
    by (unfold spZ; rewrite T2, (OLDa 2%nat ltac:(lia)), (EREG 2%nat 2%bv ltac:(lia) eq_refl); exact Hsp).
  assert (H3 : getr regsC 3 = w64 (as_gp B))
    by (rewrite T3, (OLDa 3%nat ltac:(lia)), (EREG 3%nat 3%bv ltac:(lia) eq_refl), R3; exact Hgp).
  assert (H4 : getr regsC 4 = w64 (as_tp B))
    by (rewrite T4, (OLDa 4%nat ltac:(lia)), (EREG 4%nat 4%bv ltac:(lia) eq_refl), R4; exact Htp).
  assert (H10 : getr regsC 10 = w64 x) by (rewrite T10, (OLDa 33%nat ltac:(lia)), E33; reflexivity).
  assert (H11 : getr regsC 11 = w64 y)
    by (rewrite T11, (OLDa 24%nat ltac:(lia)), (EREG 24%nat 24%bv ltac:(lia) eq_refl), R24; reflexivity).
  assert (H12 : getr regsC 12 = w64 (Z.of_nat jj)) by (rewrite T12, A36; reflexivity).
  assert (HKgC : garr8 SEGS (arm W1 mC) x (bzs (key_text kn ++ [Z_to_bv 8 0]))).
  { apply (gsc_garr8_kept W1 m1 W1 mC); [exact HKg|]. intros z Hw. apply KLC.
    rewrite gsc_bzs_len, length_app in Hw. cbn [length] in Hw. clear - Hw HK4096 HKceil. unfold klen, x in *. lia. }
  assert (HLgC : garr8 SEGS (arm W1 mC) y (dline s1 p q)).
  { apply (gsc_garr8_kept W1 m1 W1 mC); [exact HLg|]. intros z Hw. apply KLC.
    rewrite (gs_dline_len s1 p q Hpq) in Hw. clear - Hw Hpq HUL Husedr HBceil HB4096. unfold y in *. lia. }
  assert (HJJ : Z.to_nat (Z.of_nat jj) = jj) by lia.
  assert (Hjk : length (key_text kn) = jj) by (clear - Hkj; unfold klen in Hkj; lia).
  (* strncmp (held[n], s->buf + p, jj) *)
  eapply SRr_bind.
  { eapply (aj_gx_entry_at B LAWS (G_DR B RG) 0 ([] : list (Z * Z)) (2 * ESTACK) (SIGMA WS_strncmp)
      (fun _ => False)
      (fun regs' (_ : word -> option byte) => getr regs' 10 = w64 0 <-> astrn_agree W1 mC x y (Z.of_nat jj))
      W1 regsC mC DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx)
      ([] : list (Z * Z)) ly1 S1 _ k1 (- DRAIN_FRAME) (Z_to_bv 64 (BASE + 6212)) HG eq_refl HJ2).
    - rewrite Usp2. lia.
    - rewrite HDF. reflexivity.
    - lia.
    - lia.
    - lia.
    - exact H3.
    - exact H4.
    - exact T1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros _. right. intros [].
    - intros z [].
    - intros z [].
    - intros HPRE HSC.
      assert (HM : Z.min (Z.of_nat jj) (Z.of_nat jj + 1) = Z.of_nat jj) by lia.
      refine (ASTRNCMP ly1 S1 W1 regsC mC mdc x y (Z.of_nat jj) (Z.of_nat jj) (Z.of_nat jj)
        HPRE HSC H10 H11 H12 _ _ _ _ _ _ _ _ _ _ _ _ ROMc _); rewrite ?HM.
      + clear - Hjjr Hpq HUL Husedr HBceil HB4096 C1. lia.
      + clear - Hjjr Hpq HUL Husedr Hcapr. destruct Hcapr as [Hq | [Hq | Hq]]; lia.
      + clear - HK4096. unfold x in *. lia.
      + clear - HB4096. unfold y in *. lia.
      + apply (gsc_first_byte W1 mC x (bzs (key_text kn ++ [Z_to_bv 8 0])) (Z.of_nat jj) (Z.of_nat jj) HKgC).
        * lia.
        * rewrite gsc_bzs_len, length_app. cbn [length]. lia.
        * intros i Hi. apply (gsc_key_nz _ HKnz). lia.
        * intros Hlt. lia.
      + apply (gsc_first_byte W1 mC y (dline s1 p q) (Z.of_nat jj) (Z.of_nat jj) HLgC).
        * lia.
        * rewrite (gs_dline_len s1 p q Hpq). lia.
        * intros i Hi. apply (gsc_dline_nth_nz s1 p q Hpq Hnzl). lia.
        * intros Hlt. lia.
      + clear - HKceil HK4096 Hjk C1. unfold x, klen in *. lia.
      + clear - Hjjr Hpq HUL Husedr HBceil HB4096 C1. unfold y in *. lia.
      + intros z Hw. split.
        * replace z with (x + Z.of_nat (Z.to_nat (z - x))) by lia.
          rewrite (gsc_aview_garr8 W1 mC x _ _ HKgC); [discriminate|].
          rewrite gsc_bzs_len, length_app. cbn [length]. lia.
        * rewrite Usp2. clear - Hw HKceil HK4096 Hjk C1 HSTK1. unfold x, klen, ESTACK, DRAIN_FRAME in *. lia.
      + intros z Hw. split.
        * replace z with (y + Z.of_nat (Z.to_nat (z - y))) by lia.
          rewrite (gsc_aview_garr8 W1 mC y _ _ HLgC); [discriminate|].
          rewrite (gs_dline_len s1 p q Hpq). lia.
        * rewrite Usp2. clear - Hw Hjjr Hpq HUL Husedr HBceil HB4096 C1 HSTK1. unfold y, ESTACK, DRAIN_FRAME in *. lia.
      + split; [|split].
        * unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in HKia |- *.
          clear - HKia Hjk C1. unfold x, klen in *. lia.
        * apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 mC mdc x (klen + 1)); [exact HARc | exact HKin | lia |].
          unfold klen, x in *. rewrite RQK. clear - Hjk. lia.
        * intros Hp0. apply (shadow_hull_vis_of_block SEGS B LAWS ly1 S1 W1 mC mdc x (klen + 1));
            [exact HARc | exact HKin | lia | unfold klen, x in *; rewrite RQK; clear - Hjk; lia | exact Hp0].
      + split; [|split].
        * unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in HBia |- *.
          clear - HBia Hjjr Hpq HUL Husedr C1. unfold y in *. lia.
        * apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 mC mdc (re_buf e1) (re_cap e1)); [exact HARc | exact Hbin | unfold y in *; lia |].
          rewrite RQC. clear - Hjjr Hpq HUL Husedr. unfold y in *. lia.
        * intros Hp0. apply (shadow_hull_vis_of_block SEGS B LAWS ly1 S1 W1 mC mdc (re_buf e1) (re_cap e1));
            [exact HARc | exact Hbin | unfold y in *; lia | rewrite RQC; clear - Hjjr Hpq HUL Husedr; unfold y in *; lia | exact Hp0].
      + split.
        * unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in HKia |- *.
          clear - HKia HKlen C1. unfold x in *. lia.
        * unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in HBia |- *.
          clear - HBia Hjjr Hpq HUL Husedr HBceil C1. unfold y in *. lia. }
  cbv beta. intros W2 c2 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hres3 & Hfr3 & Hpres3).
  assert (HAG : astrn_agree W1 mC x y (Z.of_nat jj) <-> nth n (dlH cx s1 p) [] = firstn jj (dline s1 p q)).
  { rewrite (gsc_agree_iff W1 mC x y (Z.of_nat jj) _ _ HKgC HLgC);
      [| lia | rewrite gsc_bzs_len, length_app; cbn [length]; lia | rewrite (gs_dline_len s1 p q Hpq); lia
       | intros i Hi; apply (gsc_key_nz _ HKnz); lia].
    rewrite HJJ, (gsc_nth_H _ _ _ _ _ _ _ _ _ n HLINK Hnlen). fold kn.
    replace (firstn jj (bzs (key_text kn ++ [Z_to_bv 8 0]))) with (bzs (key_text kn))
      by (rewrite <- Hjk; symmetry; apply gsc_bzs_firstn_key).
    reflexivity. }
  jafter_call_keep_pi HS 56%nat regs3 (mrestrict (w_H W1) mem3) HP3 [0%nat] HS3.
  assert (UspA : bv_unsigned (ew Ea 2) = dsp0 cx - DRAIN_FRAME) by (rewrite (OLDa 2%nat ltac:(lia)); exact Usp0).
  assert (HRK : region_kept SEGS Ea (mrestrict (w_H W1) mC) (mrestrict (w_H W1) mem3) gl_frame).
  { split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi gl_frame base_val]; rewrite UspA;
      intros z Hw; [|lia].
    apply (mbyte_of_aview SEGS). apply Hfr3;
      [clear - Hw HSTK1 HSTK2 C1; unfold ESTACK, DRAIN_FRAME in *; lia | intros [] | clear - Hw; unfold ESTACK in *; lia]. }
  specialize (HS3 ltac:(constructor; [exact HRK | constructor])).
  clear HS HRK. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
  remember (havoc Ea 56 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
  assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
  assert (OLDb : forall m, (m < 56)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
  clear HEb.
  prreg HS (10%bv : bv 5) R10c.
  set (r0 := getr regs3 10) in *.
  assert (A60 : ew Eb 60 = Z_to_bv 64 (bv_unsigned r0)) by (rewrite <- R10c, Z_to_bv_bv_unsigned; reflexivity).
  assert (Hr0 : 0 <= bv_unsigned r0 < 2 ^ 64) by exact (bv_unsigned_in_range 64 r0).
  assert (SHOK3 : sh_ok SEGS gl_Bx [] Eb (mrestrict (w_H W1) mem3)) by constructor.
  assert (KP3 : GSKEEP cx W1 m1 mem3).
  { apply (gsc_keep_trans cx W1 m1 mC mem3 KP). split.
    - intros z Hw Hs. exact (Hfr3 z Hw (fun H => H) ltac:(clear - Hs; unfold ESTACK in *; lia)).
    - exact Hpres3. }
  clear KP KC PC Hfr3 Hpres3. rename KP3 into KP.
  (* 0x83b88 beqz a0 *)
  paj_run_tok RUN HS HJ3 SHOK3 gl_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
  gsl_absorb KP.
  assert (B22 : ew Eb 22 = Z_to_bv 64 (re_hp e1)) by (rewrite (OLDb 22%nat ltac:(lia)), (OLDa 22%nat ltac:(lia)); exact E22).
  assert (B32 : ew Eb 32 = Z_to_bv 64 (re_hp e1 + 8 * Z.of_nat n)) by (rewrite (OLDb 32%nat ltac:(lia)), (OLDa 32%nat ltac:(lia)); exact E32).
  assert (B34 : ew Eb 34 = Z_to_bv 64 SHADOW_OFF) by (rewrite (OLDb 34%nat ltac:(lia)), (OLDa 34%nat ltac:(lia)); exact E34).
  assert (B37 : ew Eb 37 = Z_to_bv 64 (dxSA cx)) by (rewrite (OLDb 37%nat ltac:(lia)), (OLDa 37%nat ltac:(lia)); exact E37).
  assert (B38 : ew Eb 38 = Z_to_bv 64 bg) by (rewrite (OLDb 38%nat ltac:(lia)), (OLDa 38%nat ltac:(lia)); exact E38).
  assert (RK : forall (r : bv 5) (k : nat) rr, getr rr r = ew Eb k -> Nat.ltb k 32 = true ->
    Z.of_nat k = bv_unsigned r -> getr rr r = getr regs1 r).
  { intros r k rr Hr Hk Hkr. apply Nat.ltb_lt in Hk. rewrite Hr, (OLDb k ltac:(lia)), (OLDa k ltac:(lia)).
    apply EREG; [exact Hk | exact Hkr]. }
  psrr_branch_tok RUN BR HS SHOK3 gl_Bspan.
  + (* strncmp = 0: the key is held at slot n *)
    rewrite branch_eq_U, (U_atom Eb 60 (bv_unsigned r0) A60 Hr0), (U_lit Eb 0) in Hc by lia.
    apply Z.eqb_eq in Hc. rename Hc into Hr0z.
    assert (Hmt : nth n (dlH cx s1 p) [] = firstn jj (dline s1 p q)).
    { apply HAG, Hres3. fold r0. apply bv_eq. rewrite Hr0z. reflexivity. }
    (* 0x83cac ld a0,24(sp); beqz a0 *)
    paj_run_tok RUN HS HJ3 SHOK3 gl_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
    gsl_absorb KP.
    gsl_clear_br.
    psrr_branch_tok RUN BR HS SHOK3 gl_Bspan.
    * (* bg = 0: a begin whose key is held: 0x83d9c, then DLN (S q) *)
      rewrite branch_eq_U, (U_atom Eb 38 bg B38 Hbgr), (U_lit Eb 0) in Hc by lia.
      apply Z.eqb_eq in Hc.
      paj_run_to_tok RUNTO HS HJ3 SHOK3 gl_Bspan A_dr_next. { apply awr_ok_x_of0. awr_ok_tac. }
      gsl_absorb KP.
      pmkst HS.
      prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
      prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (20%bv : bv 5) P20.
      prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (27%bv : bv 5) P27.
      repeat rewrite wvb_collapse in HJ3.
      match goal with |- SRr _ _ {| cfg_ms := mkst _ _ ?mx _; cfg_model := ?mdx |} _ => set (mdF := mdx) in *; set (mF := mx) in * end.
      clear HS SHOK3.
      pose proof (gsc_body_keep B MT MMAX RG LAWS HG HGSB HV9 HSD HSM cx s1 D p q n (S kf) n W1 regs1 ly1 S1 m1 md1 k1 e1
        h1 out1 ev1 LB1 spent jb aa oo ha ks tl kd jj bg mF mdF HB HBD HJ3 KP) as HBDF.
      apply (HDLN W1).
      apply (gsc_mk_dln B MT MMAX RG cx s1 D p q n (S kf) W1 regs1 ly1 S1 mF mdF k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks
        tl kd jj bg _ HBDF Hmt Hc
        (RK _ 2%nat _ P2 eq_refl eq_refl) (RK _ 3%nat _ P3 eq_refl eq_refl) (RK _ 4%nat _ P4 eq_refl eq_refl)
        (RK _ 8%nat _ P8 eq_refl eq_refl) (RK _ 9%nat _ P9 eq_refl eq_refl) (RK _ 18%nat _ P18 eq_refl eq_refl)
        (RK _ 23%nat _ P23 eq_refl eq_refl)).
      -- rewrite P21, B37. reflexivity.
      -- rewrite P20, B37, unsigned_lit_small by (clear - HSA1 HSA2 C1; lia). reflexivity.
      -- rewrite P22, B37, unsigned_lit_small by (clear - HSA1 HSA2 C1; lia). reflexivity.
      -- rewrite P27, B37, unsigned_lit_small by (clear - HSA1 HSA2 C1; lia). reflexivity.
    * (* bg <> 0: an end whose key is held: GF *)
      rewrite branch_eq_U, (U_atom Eb 38 bg B38 Hbgr), (U_lit Eb 0) in Hc by lia.
      apply Z.eqb_neq in Hc.
      paj_run_to_tok RUNTO HS HJ3 SHOK3 gl_Bspan A_dr_free. { apply awr_ok_x_of0. awr_ok_tac. }
      gsl_absorb KP.
      pmkst HS.
      prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
      prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (20%bv : bv 5) P20.
      gsl_prreg_raw HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
      prreg HS (24%bv : bv 5) P24. prreg HS (26%bv : bv 5) P26.
      repeat rewrite wvb_collapse in HJ3.
      match goal with |- SRr _ _ {| cfg_ms := mkst _ _ ?mx _; cfg_model := ?mdx |} _ => set (mdF := mdx) in *; set (mF := mx) in * end.
      clear HS SHOK3.
      pose proof (gsc_body_keep B MT MMAX RG LAWS HG HGSB HV9 HSD HSM cx s1 D p q n (S kf) n W1 regs1 ly1 S1 m1 md1 k1 e1
        h1 out1 ev1 LB1 spent jb aa oo ha ks tl kd jj bg mF mdF HB HBD HJ3 KP) as HBDF.
      apply (HGF W1).
      apply (gsc_mk_gf B MT MMAX RG cx s1 D p q n (S kf) W1 regs1 ly1 S1 mF mdF k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks
        tl kd jj bg _ HBDF Hmt Hc
        (RK _ 2%nat _ P2 eq_refl eq_refl) (RK _ 3%nat _ P3 eq_refl eq_refl) (RK _ 4%nat _ P4 eq_refl eq_refl)
        (RK _ 8%nat _ P8 eq_refl eq_refl) (RK _ 9%nat _ P9 eq_refl eq_refl) (RK _ 18%nat _ P18 eq_refl eq_refl)
        (RK _ 23%nat _ P23 eq_refl eq_refl) (RK _ 24%nat _ P24 eq_refl eq_refl)
        (RK _ 20%nat _ P20 eq_refl eq_refl) (RK _ 22%nat _ P22 eq_refl eq_refl)).
      -- rewrite P26, B32. reflexivity.
      -- rewrite P21, denot_lit_U.
         rewrite (gsc_U_shadow Eb 32 34 (re_hp e1 + 8 * Z.of_nat n) 0 B32 B34) by lia.
         rewrite Z.add_0_r. reflexivity.
  + (* strncmp <> 0: no match at slot n *)
    rewrite branch_eq_U, (U_atom Eb 60 (bv_unsigned r0) A60 Hr0), (U_lit Eb 0) in Hc by lia.
    apply Z.eqb_neq in Hc.
    assert (Hmis : nth n (dlH cx s1 p) [] <> firstn jj (dline s1 p q)).
    { intros Hm. apply HAG, Hres3 in Hm. fold r0 in Hm. apply Hc. rewrite Hm. reflexivity. }
    paj_run_to_tok RUNTO HS HJ3 SHOK3 gl_Bspan A_dr_hnext. { apply awr_ok_x_of0. awr_ok_tac. }
    gsl_absorb KP.
    pmkst HS.
    prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
    prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
    prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
    repeat rewrite wvb_collapse in HJ3.
    match goal with |- SRr _ _ {| cfg_ms := mkst _ _ ?mx _; cfg_model := ?mdx |} _ => set (mdF := mdx) in *; set (mF := mx) in * end.
    clear HS SHOK3.
    apply HGN.
    apply (gsl_exit_gsn cx s1 D p q n (S kf) W1 regs1 ly1 S1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl kd jj bg
      _ mF mdF HB HBD HJ3 KP).
    * split; [exact (RK _ 2%nat _ P2 eq_refl eq_refl)|]. split; [exact (RK _ 3%nat _ P3 eq_refl eq_refl)|].
      split; [exact (RK _ 4%nat _ P4 eq_refl eq_refl)|]. split; [exact (RK _ 8%nat _ P8 eq_refl eq_refl)|].
      split; [exact (RK _ 9%nat _ P9 eq_refl eq_refl)|]. split; [exact (RK _ 18%nat _ P18 eq_refl eq_refl)|].
      split; [exact (RK _ 22%nat _ P22 eq_refl eq_refl)|]. split; [exact (RK _ 23%nat _ P23 eq_refl eq_refl)|].
      split; [exact (RK _ 24%nat _ P24 eq_refl eq_refl) | exact (RK _ 25%nat _ P25 eq_refl eq_refl)].
    * exact (RK _ 19%nat _ P19 eq_refl eq_refl).
    * exact (RK _ 20%nat _ P20 eq_refl eq_refl).
    * exact Hmis.
Qed.

(* ---- The loop: by induction on the external kf, the number of slots left. ---- *)
Theorem gs_scan_loop : gs_scan_loop_stmt B MT MMAX RG.
Proof using LAWS HG ASTRNCMP ASTRLEN ALLOC_TAIL HGSB HV9 HSD HSM. clear HGR HROMO HGO MTL TL AERRNO AMEMCPY AMEMMOVE AMEMCHR HCROM ASTRRCHR ASTRCMP AREALLOC AFREE ASTRNDUP SLSPEC LPSPEC HERRNO HERRZ HERRW HERRAL HGSZ HVS HLIT5 HLIT6 HLIT7 HRGD HMMAX.
unfold gs_scan_loop_stmt. intros cx s1 D p q n kf. revert n.
induction kf as [|kf IH]; intros n W1 c1 HB HGL HDLN HGA HGF.
- exfalso. destruct HGL as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1
    & spent & jb & aa & oo & ha & ks & tl & kd & jj & bg & _ & HBD).
  unfold GSBODY in HBD. destruct HBD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hkf & _). lia.
- apply (gsl_body cx s1 D p q n kf W1 c1 HB HGL HDLN HGF).
  intros c2 HGN.
  apply (gsl_tail cx s1 D p q n kf W1 c2 HB HGN HGA).
  intros Hkf0 c3 HGL3.
  exact (IH (S n) W1 c3 HB HGL3 HDLN HGA HGF).
Qed.

End c.
End b.
End a.

(* ============================================================================================================
   THE ARx-GENERIC TWIN of this file (image B's DR_x slice D, 2026-10-30; the B twin of lib/A/W_gsscanb.v's Section cx
   at a working branch 50623273289): gs_scan_loop_x proves lib/B/W_gsscan_cx.v's gs_scan_loop_stmt_x over
   lib/B/W_drain_cx_x.v's Section variables (B PST ARx MT RP MMAX RG), with the entry's ghost list Hp and budget kr after
   cx and a cut's ghost list Hp1 after S1.  Everything above this line is unchanged.
   - The tactics above (gsl_prreg_raw, gsl_absorb, gsl_clear_br) and the AR-free names of lib/B/W_gsscan_cx.v are CITED;
     gsl_exit_gsn, gsl_tail, gsl_body and gs_scan_loop have their twins NAME_x below, with the AR proof's text: the run
     over W_journal_x's generic chain (paj_run_tok_x / paj_run_to_tok_x), the cut lemmas' _x twins of
     lib/B/W_gsscan_cx.v, and the strlen (0x83b6c) / strncmp (0x83b84) calls through W_sites_x.aj_gx_entry_at_x.
   - The loop calls strlen (ASTRLEN) and strncmp (ASTRNCMP) and no allocator rule: the Section takes no context table,
     no rule and no RMM, and the cut's dbud_x (with its trace tl) reaches every exit (GA_x, GF_x, DLN_x, or GSL_x at
     n + 1) unchanged.
   - A key's strlen reads to its granule end: the AR proof's ALLOC_TAIL is W_drain_cx_x.alloc_tail_x, a theorem of the
     laws.  A block's shadow facts are W_journal_x's _hp0_x lemmas under HP0. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_sites_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_drain_cx W_drain_cx_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_drain_gs W_gsscan_cx.
(* W_drain_cx_x.v loads FCiface, which sets Zify's euclidean flag: this file's setting again *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ax. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section bx.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Section cx.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
Context {hl : Z}.
(* the instance's laws, and HP0 (a Theorem Labs lane's ruling, lib/B/W_journal_x.v Section hp0; lib/A/W_gsscanb.v's HP0) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
(* lib/B/W_drain_cx_x.v's Section c items this walk uses, in that file's order and text *)
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis ASTRNCMP : astrncmp_realizes_x B ARx (SIGMA WS_strncmp).
Hypothesis ASTRLEN : astrlen_realizes_x B ARx (SIGMA WS_strlen).
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HSD : 0x10000 <= rg_send_dead RG /\ rg_send_dead RG + 1 <= IMG_TOP.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= IMG_TOP.
Let RUN := paj_run_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).






(* ==== route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) section 0): the R twins of this section's journal-carrying blocks.  Each X_xR
   is X_x with the carriers and engine texts replaced by their R twins (R after the carrier's section
   variables), ajournal_gx_x -> ajournal_gx_xR .. R, ajournal_x -> ajournal_xR .. R and SRr SEGS -> SRrG SEGS R;
   the strict text is untouched.  Blocks that name no journal, no step relation and no carrier have no twin. ==== *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
(* the symbolic runs at R: the G forms of W_journal_x.v Section g, and W_kit.v branch twin *)
Let RUNR := paj_run_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let RUNTOR := paj_run_to_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).

(* R twin of gsl_exit_gsn_x *)
Lemma gsl_exit_gsn_xR : forall cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks
  tl kd jj bg regs2 m2 md2,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
GSBODY_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q n kf n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o
  ha ks tl kd jj bg ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m2 md2 k1 ->
GSKEEP cx W1 m1 m2 ->
GSREGS regs1 regs2 -> getr regs2 19 = getr regs1 19 -> getr regs2 20 = getr regs1 20 ->
nth n (dlH cx s1 p) [] <> firstn jj (dline s1 p q) ->
GSN_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q n kf W1 (cfg_at SEGS (BASE + A_dr_hnext) regs2 m2 md2).
Proof.
intros cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg regs2 m2
  md2 HB HBD HJ HKP HR Q19 Q20 Hn.
exists regs2, ly1, S1, Hp1, m2, md2, k1, e1, h1, out1, ev1, LB1, spent, jb, a, o, ha, ks, tl, kd, jj, bg.
split; [reflexivity|].
apply (gsc_mk_gsn_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m2 md2 k1 e1 h1 out1 ev1 LB1
  spent jb a o ha ks tl kd jj bg regs2);
  [| exact HR | exact Q19 | exact Q20 | exact Hn].
exact (gsc_body_keep_xR B PST ARx MT RP MMAX RG LAWS HG HGSB HV9 HSD HSM R cx Hp kr s1 D p q n kf n W1 regs1 ly1 S1 Hp1
  m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl kd jj bg m2 md2 HB HBD HJ HKP).
Qed.

(* R twin of gsl_tail_x *)
Lemma gsl_tail_xR : forall cx Hp kr s1 D p q n kf W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> GSN_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q n (S kf) W1 c1 ->
(forall W2 c2, GA_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
((0 < kf)%nat -> forall c2, GSL_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q (S n) kf W1 c2 ->
   SRrG SEGS R W1 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx Hp kr).
Proof.
intros cx Hp kr s1 D p q n kf W1 c1 HB HGN HGA HGL.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HGN as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & oo & ha & ks
  & tl & kd & jj & bg & Hcfg & HBD).
destruct (gsc_stack_x B ARx MT RP MMAX RG cx Hp kr HB) as (HSTK1 & HSTK2 & Hal16 & Hj4).
pose proof HBD as (HRG & M0 & M16 & M24 & M96 & M112 & M160 & M168 & M192 & R23 & R24 & R19 & R20 & R22 & R25
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hband & Hcap & Hgest & Hjjr & HGSF & HCORE & HFUT).
pose proof HRG as (Hsp & R3 & R4 & R8 & R9 & R18 & HFR).
pose proof HFR as (F8 & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F88 & F104 & F120 & F128 & F136 & F144 & F152
  & F176 & _).
pose proof HCORE as (HMEM & HLINK & _).
pose proof HMEM as (HJ & _ & _ & _ & _ & _ & _ & HOKX & _).
destruct (gsc_sa_xR B PST ARx MT RP MMAX RG LAWS R cx Hp kr _ _ _ _ _ _ _ _ _ _ _ _ _ _ HB HMEM) as (HSA1 & HSA2).
pose proof HOKX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hnheld & _).
assert (HNHR : 0 <= re_nheld e1 < 2 ^ 26) by (split; [unfold re_nheld; lia | exact Hnheld]).
assert (HDF : DRAIN_FRAME = 352) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
pose proof (gn_entry W1 regs1 m1 (dsp0 cx - DRAIN_FRAME) (8 * re_nheld e1) (dxSA cx) (Z.of_nat (S kf))
  Hsp ltac:(lia) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity)
  R19 ltac:(unfold re_nheld in HNHR; lia) ltac:(lia) ltac:(lia) ltac:(lia) M160 F176) as HS.
remember (Eimg (Ereg regs1 (gn_extra (8 * re_nheld e1) (dxSA cx)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n0 r Hn Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 (8 * re_nheld e1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (dxSA cx)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E19 : ew E 19 = Z_to_bv 64 (Z.of_nat (S kf))) by (rewrite (EREG 19%nat 19%bv ltac:(lia) eq_refl), R19; reflexivity).
assert (E20 : ew E 20 = Z_to_bv 64 (8 * Z.of_nat n)) by (rewrite (EREG 20%nat 20%bv ltac:(lia) eq_refl), R20; reflexivity).
assert (SHOK : sh_ok SEGS gn_Bx [] E (mrestrict (w_H W1) m1)) by constructor.
clear HE.
subst c1. unfold cfg_at. change (w64 (BASE + A_dr_hnext)) with (Z_to_bv 64 (BASE + A_dr_hnext)).
assert (KP : GSKEEP cx W1 m1 m1) by (split; [intros; reflexivity | intros; assumption]).
paj_run_tok_xR RUNR HS HJ SHOK gl_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
gsl_absorb KP.
assert (Hn8 : 0 <= 8 * Z.of_nat n + 8 < 2 ^ 64) by (unfold re_nheld in HNHR; lia).
assert (Hh8 : 0 <= 8 * re_nheld e1 < 2 ^ 64) by lia.
psrr_branch_tok RUNR BRR HS SHOK gl_Bspan.
- (* a slot is left (8 nheld <> 8 (n + 1)): back to the loop's head at S n *)
  rewrite branch_ne_U, (U_atom E 32 (8 * re_nheld e1) E32 Hh8), (U_atom_off E 20 (8 * Z.of_nat n) 8 E20 ltac:(lia) Hn8) in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  assert (Hkf0 : (0 < kf)%nat) by (clear - Hc Hnk; unfold re_nheld in Hc; lia).
  paj_run_to_tok_xR RUNTOR HS HJ SHOK gl_Bspan A_dr_hloop. { apply awr_ok_x_of0. awr_ok_tac. }
  gsl_absorb KP.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
  prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) PX24. prreg HS (25%bv : bv 5) P25.
  repeat rewrite wvb_collapse in HJ.
  match goal with |- SRrG _ _ _ {| cfg_ms := mkst ?rx _ ?mx _; cfg_model := ?mdx |} _ =>
    set (mdF := mdx) in *; set (mF := mx) in *; set (regsF := rx) in * end.
  clear HS SHOK.
  assert (RK : forall (r : bv 5) (k : nat), getr regsF r = ew E k -> Nat.ltb k 32 = true ->
    Z.of_nat k = bv_unsigned r -> getr regsF r = getr regs1 r) by
    (intros r k Hr Hk Hkr; rewrite Hr; apply EREG; [apply Nat.ltb_lt; exact Hk | exact Hkr]).
  apply (HGL Hkf0).
  exists regsF, ly1, S1, Hp1, mF, mdF, k1, e1, h1, out1, ev1, LB1, spent, jb, aa, oo, ha, ks, tl, kd, jj, bg.
  split; [reflexivity|].
  apply (gsc_mk_loop_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 mF mdF k1 e1 h1 out1 ev1 LB1
    spent jb aa oo ha ks tl kd jj bg).
  + exact (gsc_body_keep_xR B PST ARx MT RP MMAX RG LAWS HG HGSB HV9 HSD HSM R cx Hp kr s1 D p q n (S kf) (S n) W1 regs1
      ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl kd jj bg mF mdF HB HBD HJ KP).
  + exact Hkf0.
  + split; [exact (RK _ 2%nat P2 eq_refl eq_refl)|]. split; [exact (RK _ 3%nat P3 eq_refl eq_refl)|].
    split; [exact (RK _ 4%nat P4 eq_refl eq_refl)|]. split; [exact (RK _ 8%nat P8 eq_refl eq_refl)|].
    split; [exact (RK _ 9%nat P9 eq_refl eq_refl)|]. split; [exact (RK _ 18%nat P18 eq_refl eq_refl)|].
    split; [exact (RK _ 22%nat P22 eq_refl eq_refl)|]. split; [exact (RK _ 23%nat P23 eq_refl eq_refl)|].
    split; [exact (RK _ 24%nat PX24 eq_refl eq_refl) | exact (RK _ 25%nat P25 eq_refl eq_refl)].
  + rewrite P19, E19, unsigned_lit_small by (unfold re_nheld in HNHR; lia). unfold w64. f_equal. lia.
  + rewrite P20, E20, unsigned_lit_small by (unfold re_nheld in HNHR; lia). unfold w64. f_equal. lia.
- (* no slot is left (8 nheld = 8 (n + 1)): s11 = 176(sp), on to GA_xR *)
  rewrite branch_ne_U, (U_atom E 32 (8 * re_nheld e1) E32 Hh8), (U_atom_off E 20 (8 * Z.of_nat n) 8 E20 ltac:(lia) Hn8) in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc.
  assert (Hkf0 : kf = 0%nat) by (clear - Hc Hnk; unfold re_nheld in Hc; lia). subst kf.
  paj_run_to_tok_xR RUNTOR HS HJ SHOK gl_Bspan A_dr_add. { apply awr_ok_x_of0. awr_ok_tac. }
  gsl_absorb KP.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) PX24.
  prreg HS (27%bv : bv 5) P27.
  repeat rewrite wvb_collapse in HJ.
  match goal with |- SRrG _ _ _ {| cfg_ms := mkst ?rx _ ?mx _; cfg_model := ?mdx |} _ =>
    set (mdF := mdx) in *; set (mF := mx) in *; set (regsF := rx) in * end.
  clear HS SHOK.
  assert (RK : forall (r : bv 5) (k : nat), getr regsF r = ew E k -> Nat.ltb k 32 = true ->
    Z.of_nat k = bv_unsigned r -> getr regsF r = getr regs1 r) by
    (intros r k Hr Hk Hkr; rewrite Hr; apply EREG; [apply Nat.ltb_lt; exact Hk | exact Hkr]).
  apply HGA.
  apply (gsc_mk_ga_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q n W1 regs1 ly1 S1 Hp1 mF mdF k1 e1 h1 out1 ev1 LB1 spent
    jb aa oo ha ks tl kd jj bg
    _ (gsc_body_keep_xR B PST ARx MT RP MMAX RG LAWS HG HGSB HV9 HSD HSM R cx Hp kr s1 D p q n 1 (S n) W1 regs1 ly1 S1 Hp1
      m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl kd jj bg mF mdF HB HBD HJ KP)
    (RK _ 2%nat P2 eq_refl eq_refl) (RK _ 3%nat P3 eq_refl eq_refl) (RK _ 4%nat P4 eq_refl eq_refl)
    (RK _ 8%nat P8 eq_refl eq_refl) (RK _ 9%nat P9 eq_refl eq_refl) (RK _ 18%nat P18 eq_refl eq_refl)
    (RK _ 23%nat P23 eq_refl eq_refl) (RK _ 24%nat PX24 eq_refl eq_refl)).
  rewrite P27, E33, unsigned_lit_small by lia. reflexivity.
Qed.

(* R twin of gsl_body_x *)
Lemma gsl_body_xR : forall cx Hp kr s1 D p q n kf W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> GSL_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q n (S kf) W1 c1 ->
(forall W2 c2, DLN_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D (S q) W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
(forall W2 c2, GF_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
(forall c2, GSN_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q n (S kf) W1 c2 ->
   SRrG SEGS R W1 c2 (dPOST_xR B PST ARx MT RP RG R cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOST_xR B PST ARx MT RP RG R cx Hp kr).
Proof.
intros cx Hp kr s1 D p q n kf W1 c1 HB HGL HDLN HGF HGN.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@ASAN_CEIL_range rc) as (HAC & _). unfold ASAN_CEIL in HAC.
destruct HGL as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & oo & ha & ks
  & tl & kd & jj & bg & Hcfg & HBD).
destruct (gsc_stack_x B ARx MT RP MMAX RG cx Hp kr HB) as (HSTK1 & HSTK2 & Hal16 & Hj4).
pose proof HBD as (HRG & M0 & M16 & M24 & M96 & M112 & M160 & M168 & M192 & R23 & R24 & R19 & R20 & R22 & R25
  & Hnk & Hkf & Hnm & Hbgr & Hbgk & Hband & Hcap & Hgest & Hjjr & HGSF & HCORE & HFUT).
pose proof HRG as (Hsp & R3 & R4 & R8 & R9 & R18 & HFR).
pose proof HFR as (F8 & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F88 & F104 & F120 & F128 & F136 & F144 & F152
  & F176 & F184 & F200 & F208 & F216 & F224 & F232 & F240 & _).
pose proof HCORE as (HMEM & HLINK & _).
pose proof HMEM as (HJ & Hrom & _ & _ & _ & _ & _ & HOKX & _).
destruct (gsc_sa_xR B PST ARx MT RP MMAX RG LAWS R cx Hp kr _ _ _ _ _ _ _ _ _ _ _ _ _ _ HB HMEM) as (HSA1 & HSA2).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof HOKX as (_ & _ & _ & _ & _ & Hcapr & HUlen & Husedr & Hbufc & Hnheld & Hheld & _ & _ & Hkeys).
assert (Hnlen : (n < length (re_keys e1))%nat) by lia.
destruct Hheld as [(Hz & Hk0) | (Hz & Hin & Hk1 & Hk2 & Hg8)]; [rewrite Hk0 in Hnlen; cbn [length] in Hnlen; lia|].
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (re_hp e1) (re_kh e1) HAR Hin) as (HH16 & HH4096 & HHceil & HHia & _).
assert (Hrq : re_kh e1 <= req_size (re_kh e1)) by (unfold req_size; destruct (Z.eqb_spec (re_kh e1) 0); lia).
assert (HHP8 : re_hp e1 mod 8 = 0).
{ rewrite (Z.div_mod (re_hp e1) 16) by lia. rewrite HH16, Z.add_0_r.
  replace (16 * (re_hp e1 / 16)) with ((2 * (re_hp e1 / 16)) * 8) by lia. apply Z.mod_mul. lia. }
set (kn := nth n (re_keys e1) (0, [], [])).
assert (Hkn : In kn (re_keys e1)) by (apply nth_In; exact Hnlen).
rewrite Forall_forall in Hkeys. destruct (Hkeys kn Hkn) as (HKin & HKg & HKnz & HKlen).
unfold APARTIAL in HKlen.
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (key_addr kn) (Z.of_nat (length (key_text kn)) + 1) HAR HKin)
  as (HK16 & HK4096 & HKceil & HKia & _).
assert (RQK : req_size (Z.of_nat (length (key_text kn)) + 1) = Z.of_nat (length (key_text kn)) + 1)
  by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length (key_text kn)) + 1) 0); lia).
rewrite RQK in HKceil, HKia.
pose proof (gsc_slot_val W1 m1 (re_hp e1) (re_keys e1) n Hg8 Hnlen ltac:(change (nth n (re_keys e1) (0, [], [])) with kn; lia))
  as MSL. fold kn in MSL.
pose proof (gsc_link_U _ _ _ _ _ _ _ _ _ HLINK) as HUW.
assert (HUL : re_used e1 = Z.of_nat (length (dW s1))) by (rewrite <- HUW, gsc_bzs_len; lia).
pose proof HGSF as (Hbd & Hpq & Hq0 & Hnzl & Hskp & Hlim).
assert (Hcap0 : re_cap e1 <> 0) by lia.
destruct Hbufc as [(Hc0 & _) | (Hcpos & Hbin & Hjunk & Hbuf8)]; [lia|].
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (re_buf e1) (re_cap e1) HAR Hbin) as (HB16 & HB4096 & HBceil & HBia & _).
assert (RQC : req_size (re_cap e1) = re_cap e1) by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
rewrite RQC in HBceil, HBia.
pose proof (gsc_line_garr8 W1 m1 s1 p q e1 Hbuf8 HUW ltac:(lia)) as HLg.
unfold re_nheld in Hnheld, Hk1.
assert (HDF : DRAIN_FRAME = 352) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
assert (HDS : DRAIN_STK_x = 17008) by reflexivity.
pose proof (gl_entry W1 regs1 m1 (dsp0 cx - DRAIN_FRAME) (re_hp e1) n (Z.of_nat (S kf)) (key_addr kn) (Z.of_nat jj)
  (dxSA cx) bg (8 * re_nheld e1)
  Hsp ltac:(lia) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity)
  R19 ltac:(lia) R20 ltac:(lia) R22 R25
  HH4096 HHP8 ltac:(unfold GL_PHI; lia) ltac:(lia) ltac:(unfold GL_PHI; lia)
  ltac:(lia) ltac:(lia) ltac:(lia) Hbgr ltac:(unfold re_nheld; lia)
  M24 F128 F136 F144 M160 M168 F176 M192 F240 MSL) as HS.
remember (Eimg (Ereg regs1 (gl_extra (re_hp e1 + 8 * Z.of_nat n) (key_addr kn) (Z.of_nat jj) (dxSA cx) bg
  (8 * re_nheld e1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall k (r : bv 5), (k < 32)%nat -> Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r).
{ intros k r Hk Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. lia. }
assert (E22 : ew E 22 = Z_to_bv 64 (re_hp e1)) by (rewrite (EREG 22%nat 22%bv ltac:(lia) eq_refl); exact R22).
assert (E25 : ew E 25 = Z_to_bv 64 1) by (rewrite (EREG 25%nat 25%bv ltac:(lia) eq_refl); exact R25).
assert (E32 : ew E 32 = Z_to_bv 64 (re_hp e1 + 8 * Z.of_nat n)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (key_addr kn)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E36 : ew E 36 = Z_to_bv 64 (Z.of_nat jj)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (dxSA cx)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 bg) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 6)).
assert (SHOK : sh_ok SEGS gl_Bx gl_SH E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W1) m1 E gl_Bx 32 (re_hp e1 + 8 * Z.of_nat n) 8 (re_hp e1 + 8 * Z.of_nat n) 0 8).
  - apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 m1 md1 (re_hp e1) (re_kh e1));
      [exact HAR | exact Hin | lia | lia].
  - unfold gl_Bx. rewrite (U_atom E 34 SHADOW_OFF E34) by (unfold SHADOW_OFF; lia). reflexivity.
  - apply (U_atom E 32 _ E32). lia.
  - lia.
  - lia.
  - intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
    unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *. lia. }
clear HE.
subst c1. unfold cfg_at. change (w64 (BASE + A_dr_hloop)) with (Z_to_bv 64 (BASE + A_dr_hloop)).
assert (KP : GSKEEP cx W1 m1 m1) by (split; [intros; reflexivity | intros; assumption]).
(* 0x83b34 .. the PTR_BLTU trap at 0x83b38 *)
paj_run_tok_xR RUNR HS HJ SHOK gl_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
gsl_absorb KP.
psrr_branch_tok RUNR BRR HS SHOK gl_Bspan.
{ exfalso. rewrite (trap_ptr_wrap_atom E 32 22 (re_hp e1) (8 * Z.of_nat n) E32 E22 ltac:(lia) ltac:(lia) ltac:(lia)) in Hc.
  discriminate Hc. }
gsl_clear_br.
(* .. the folded NULL_XOR trap at 0x83b44 *)
paj_run_tok_xR RUNR HS HJ SHOK gl_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
gsl_absorb KP.
psrr_branch_tok RUNR BRR HS SHOK gl_Bspan.
{ exfalso. rewrite (trap_null_xor_folded E 25 E25) in Hc. discriminate Hc. }
gsl_clear_br.
(* .. 168(sp) and the shadow of &held[n] decided, held[n], to strlen at 0x83b6c *)
paj_run_tok_xR RUNR HS HJ SHOK gl_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
gsl_absorb KP.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10.
repeat rewrite wvb_collapse in HJ.
match goal with |- SRrG _ _ _ {| cfg_ms := mkst ?rx _ ?mx _; cfg_model := ?mdx |} _ =>
  set (mdm := mdx) in *; set (mA := mx) in *; set (regsA := rx) in * end.
clearbody mdm.
pose proof KP as (KEEPA & PRESA).
assert (HARm : ARx ly1 S1 Hp1 W1 mA mdm) by (eapply ajournal_gx_AR_xR; exact HJ).
assert (KLA : forall y, 0 <= y < alloc_ceiling -> aview SEGS (w_H W1) mA y = aview SEGS (w_H W1) m1 y)
  by (intros y Hy; apply KEEPA; [lia | unfold ESTACK, DRAIN_FRAME in *; lia]).
assert (ROM1 : rom_view SEGS W1 mA).
{ intros y Hy. rewrite KLA; [exact (Hrom y Hy)|].
  destruct Hy as (sg & Hsg & _ & Hr). pose proof (pa_img_range y ltac:(exists sg; split; [exact Hsg | exact Hr])). lia. }
pose proof HB as (Hafn & _). pose proof Hafn as (_ & _ & _ & Hgp & Htp & _).
assert (Usp1 : spZ regsA = dsp0 cx - DRAIN_FRAME)
  by (unfold spZ; rewrite Q2, (EREG 2%nat 2%bv ltac:(lia) eq_refl); exact Hsp).
assert (G3 : getr regsA 3 = w64 (as_gp B)) by (rewrite Q3, (EREG 3%nat 3%bv ltac:(lia) eq_refl), R3; exact Hgp).
assert (G4 : getr regsA 4 = w64 (as_tp B)) by (rewrite Q4, (EREG 4%nat 4%bv ltac:(lia) eq_refl), R4; exact Htp).
set (x := key_addr kn) in *. set (klen := Z.of_nat (length (key_text kn))) in *.
assert (G10 : getr regsA 10 = w64 x) by (rewrite Q10, E33; reflexivity).
assert (HKg1 : garr8 SEGS (arm W1 mA) x (bzs (key_text kn ++ [Z_to_bv 8 0]))).
{ apply (gsc_garr8_kept W1 m1 W1 mA); [exact HKg|]. intros y Hy. apply KLA.
  rewrite gsc_bzs_len, length_app in Hy. cbn [length] in Hy. unfold klen, x in *. lia. }
assert (HKL : Z.to_nat klen = length (key_text kn)) by (unfold klen; lia).
(* strlen (held[n]) *)
eapply (SRrG_bind SEGS R R_trans).
{ eapply (@aj_gx_entry_at_xR _ _ _ _ B PST ARx _ LAWS R R_trans WLE_R (G_DR B RG) 0 ([] : list (Z * Z)) (2 * ESTACK) (SIGMA WS_strlen)
    (fun _ => False) (fun regs' (_ : word -> option byte) => getr regs' 10 = w64 klen)
    W1 regsA mA DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx)
    ([] : list (Z * Z)) ly1 S1 Hp1 _ k1 (- DRAIN_FRAME) (Z_to_bv 64 (BASE + 6188)) HG eq_refl HJ).
  - rewrite Usp1. lia.
  - rewrite HDF. reflexivity.
  - lia.
  - lia.
  - lia.
  - exact G3.
  - exact G4.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros _. right. intros [].
  - intros y [].
  - intros y [].
  - intros HPRE HSC. eapply SRr_mono.
    { refine (ASTRLEN ly1 S1 Hp1 W1 regsA mA mdm x klen HPRE (proj1 HSC) (proj2 HSC) G10
        ltac:(unfold x, klen in *; lia) ltac:(unfold x, klen in *; lia) ltac:(unfold x, klen in *; lia) ltac:(unfold x, klen in *; lia) _ _ _ _ _ _ _ _ ROM1).
      - apply (gsc_first_byte W1 mA x (bzs (key_text kn ++ [Z_to_bv 8 0])) (klen + 1) klen HKg1).
        + unfold klen in *; lia.
        + rewrite gsc_bzs_len, length_app. cbn [length]. unfold klen in *. lia.
        + intros i Hi. apply (gsc_key_nz _ HKnz). lia.
        + intros _. rewrite HKL. apply gsc_key_z.
      - intros y Hy. split.
        + replace y with (x + Z.of_nat (Z.to_nat (y - x))) by lia.
          rewrite (gsc_aview_garr8 W1 mA x _ _ HKg1); [discriminate|].
          rewrite gsc_bzs_len, length_app. cbn [length]. unfold klen in *. lia.
        + rewrite Usp1. unfold x, klen in *. lia.
      - intros y Hy. rewrite Usp1. unfold x, klen in *. lia.
      - unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in HKia |- *.
        unfold x, klen in *. lia.
      - unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in HKia |- *.
        unfold x, klen in *. lia.
      - apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 mA mdm x (klen + 1));
          [exact HARm | exact HKin | lia | unfold klen, x in *; rewrite RQK; lia].
      - apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 mA mdm x (klen + 1));
          [exact HARm | exact HKin | lia | unfold klen, x in *; rewrite RQK; lia | unfold klen in *; lia].
      - intros y Hy. apply (alloc_tail_x SEGS B ARx LAWS ly1 S1 Hp1 W1 mA mdm x (klen + 1) y HARm HKin).
        unfold klen, x in *. rewrite RQK.
        replace (key_addr kn + (Z.of_nat (length (key_text kn)) + 1) - 1) with (key_addr kn + Z.of_nat (length (key_text kn))) by lia.
        exact Hy. }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpr).
    split; [reflexivity|]. exists regs2, mem2, md2.
    split; [reflexivity|]. split; [exact HAR2|]. split; [exact HP|]. split; [exact Hsame|]. split; [exact Hres|].
    split; [intros y Hy _ Hs; exact (Hfr y Hy Hs) | exact Hpr]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hres & Hfr2 & Hpres2).
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0%nat] HS2.
assert (Usp0 : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME)
  by (rewrite (EREG 2%nat 2%bv ltac:(lia) eq_refl); exact Hsp).
assert (HRK : region_kept SEGS E (mrestrict (w_H W1) mA) (mrestrict (w_H W1) mem2) gl_frame).
{ split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi gl_frame base_val]; rewrite Usp0;
    intros y Hy; [|lia].
  apply (mbyte_of_aview SEGS). apply Hfr2; [clear - Hy HSTK1 HSTK2 C1; unfold ESTACK, DRAIN_FRAME in *; lia | intros [] | clear - Hy; unfold ESTACK in *; lia]. }
specialize (HS2 ltac:(constructor; [exact HRK | constructor])).
clear HS HRK. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 40 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 40)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
clear HEa.
prreg HS (10%bv : bv 5) R10b.
assert (A44 : ew Ea 44 = Z_to_bv 64 klen) by (rewrite <- R10b, Hres; reflexivity).
assert (A36 : ew Ea 36 = Z_to_bv 64 (Z.of_nat jj)) by (rewrite (OLDa 36%nat ltac:(lia)); exact E36).
assert (SHOK2 : sh_ok SEGS gl_Bx [] Ea (mrestrict (w_H W1) mem2)) by constructor.
assert (KP2 : GSKEEP cx W1 m1 mem2).
{ split.
  - intros y Hy Hs. rewrite (Hfr2 y Hy (fun H => H) ltac:(clear - Hs; unfold ESTACK in *; lia)). exact (KEEPA y Hy Hs).
  - intros y Hp'. apply Hpres2. exact (PRESA y Hp'). }
clear KP KEEPA PRESA Hfr2 Hpres2. rename KP2 into KP.
(* 0x83b70 ld a1,192(sp); bne a0,a1 *)
paj_run_tok_xR RUNR HS HJ2 SHOK2 gl_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
gsl_absorb KP.
assert (Hk64 : 0 <= klen < 2 ^ 64) by (unfold klen in *; lia).
assert (Hj64 : 0 <= Z.of_nat jj < 2 ^ 64) by lia.
psrr_branch_tok RUNR BRR HS SHOK2 gl_Bspan.
- (* |held[n]| <> jj: no match at slot n *)
  rewrite branch_ne_U, (U_atom Ea 44 klen A44 Hk64), (U_atom Ea 36 (Z.of_nat jj) A36 Hj64) in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_to_tok_xR RUNTOR HS HJ2 SHOK2 gl_Bspan A_dr_hnext. { apply awr_ok_x_of0. awr_ok_tac. }
  gsl_absorb KP.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
  prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
  prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) PX24. prreg HS (25%bv : bv 5) P25.
  repeat rewrite wvb_collapse in HJ2.
  match goal with |- SRrG _ _ _ {| cfg_ms := mkst _ _ ?mx _; cfg_model := ?mdx |} _ => set (mdF := mdx) in *; set (mF := mx) in * end.
  clear HS SHOK2.
  assert (RK : forall (r : bv 5) (k : nat) rr, getr rr r = ew Ea k -> Nat.ltb k 32 = true ->
    Z.of_nat k = bv_unsigned r -> getr rr r = getr regs1 r).
  { intros r k rr Hr Hk Hkr. apply Nat.ltb_lt in Hk. rewrite Hr, (OLDa k ltac:(lia)). apply EREG; [exact Hk | exact Hkr]. }
  apply HGN.
  apply (gsl_exit_gsn_xR cx Hp kr s1 D p q n (S kf) W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks
    tl kd jj bg _ mF mdF HB HBD HJ2 KP).
  + split; [exact (RK _ 2%nat _ P2 eq_refl eq_refl)|]. split; [exact (RK _ 3%nat _ P3 eq_refl eq_refl)|].
    split; [exact (RK _ 4%nat _ P4 eq_refl eq_refl)|]. split; [exact (RK _ 8%nat _ P8 eq_refl eq_refl)|].
    split; [exact (RK _ 9%nat _ P9 eq_refl eq_refl)|]. split; [exact (RK _ 18%nat _ P18 eq_refl eq_refl)|].
    split; [exact (RK _ 22%nat _ P22 eq_refl eq_refl)|]. split; [exact (RK _ 23%nat _ P23 eq_refl eq_refl)|].
    split; [exact (RK _ 24%nat _ PX24 eq_refl eq_refl) | exact (RK _ 25%nat _ P25 eq_refl eq_refl)].
  + exact (RK _ 19%nat _ P19 eq_refl eq_refl).
  + exact (RK _ 20%nat _ P20 eq_refl eq_refl).
  + rewrite (gsc_nth_H _ _ _ _ _ _ _ _ _ n HLINK Hnlen). fold kn. intros Heq.
    apply (f_equal (@length Z)) in Heq. rewrite gsc_bzs_len, length_firstn, (gs_dline_len s1 p q Hpq) in Heq.
    idtac. unfold klen in Hc. lia.
- (* |held[n]| = jj: strncmp (held[n], s->buf + p, jj) *)
  rewrite branch_ne_U, (U_atom Ea 44 klen A44 Hk64), (U_atom Ea 36 (Z.of_nat jj) A36 Hj64) in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hkj.
  paj_run_tok_xR RUNR HS HJ2 SHOK2 gl_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
  gsl_absorb KP.
  pmkst HS.
  prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
  prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12.
  repeat rewrite wvb_collapse in HJ2.
  match goal with |- SRrG _ _ _ {| cfg_ms := mkst ?rx _ ?mx _; cfg_model := ?mdx |} _ =>
    set (mdc := mdx) in *; set (mC := mx) in *; set (regsC := rx) in * end.
  clearbody mdc.
  assert (HARc : ARx ly1 S1 Hp1 W1 mC mdc) by (eapply ajournal_gx_AR_xR; exact HJ2).
  pose proof KP as (KC & PC).
  assert (KLC : forall z, 0 <= z < alloc_ceiling -> aview SEGS (w_H W1) mC z = aview SEGS (w_H W1) m1 z)
    by (intros z Hw; apply KC; [clear - Hw C1; lia | clear - Hw HSTK1; unfold ESTACK, DRAIN_FRAME in *; lia]).
  assert (ROMc : rom_view SEGS W1 mC).
  { intros z Hw. rewrite KLC; [exact (Hrom z Hw)|].
    destruct Hw as (sg & Hsg & _ & Hr). pose proof (pa_img_range z ltac:(exists sg; split; [exact Hsg | exact Hr])).
    idtac. lia. }
  set (y := re_buf e1 + Z.of_nat p) in *.
  assert (Usp2 : spZ regsC = dsp0 cx - DRAIN_FRAME)
    by (unfold spZ; rewrite T2, (OLDa 2%nat ltac:(lia)), (EREG 2%nat 2%bv ltac:(lia) eq_refl); exact Hsp).
  assert (H3 : getr regsC 3 = w64 (as_gp B))
    by (rewrite T3, (OLDa 3%nat ltac:(lia)), (EREG 3%nat 3%bv ltac:(lia) eq_refl), R3; exact Hgp).
  assert (H4 : getr regsC 4 = w64 (as_tp B))
    by (rewrite T4, (OLDa 4%nat ltac:(lia)), (EREG 4%nat 4%bv ltac:(lia) eq_refl), R4; exact Htp).
  assert (H10 : getr regsC 10 = w64 x) by (rewrite T10, (OLDa 33%nat ltac:(lia)), E33; reflexivity).
  assert (H11 : getr regsC 11 = w64 y)
    by (rewrite T11, (OLDa 24%nat ltac:(lia)), (EREG 24%nat 24%bv ltac:(lia) eq_refl), R24; reflexivity).
  assert (H12 : getr regsC 12 = w64 (Z.of_nat jj)) by (rewrite T12, A36; reflexivity).
  assert (HKgC : garr8 SEGS (arm W1 mC) x (bzs (key_text kn ++ [Z_to_bv 8 0]))).
  { apply (gsc_garr8_kept W1 m1 W1 mC); [exact HKg|]. intros z Hw. apply KLC.
    rewrite gsc_bzs_len, length_app in Hw. cbn [length] in Hw. clear - Hw HK4096 HKceil. unfold klen, x in *. lia. }
  assert (HLgC : garr8 SEGS (arm W1 mC) y (dline s1 p q)).
  { apply (gsc_garr8_kept W1 m1 W1 mC); [exact HLg|]. intros z Hw. apply KLC.
    rewrite (gs_dline_len s1 p q Hpq) in Hw. clear - Hw Hpq HUL Husedr HBceil HB4096. unfold y in *. lia. }
  assert (HJJ : Z.to_nat (Z.of_nat jj) = jj) by lia.
  assert (Hjk : length (key_text kn) = jj) by (clear - Hkj; unfold klen in Hkj; lia).
  (* strncmp (held[n], s->buf + p, jj) *)
  eapply (SRrG_bind SEGS R R_trans).
  { eapply (@aj_gx_entry_at_xR _ _ _ _ B PST ARx _ LAWS R R_trans WLE_R (G_DR B RG) 0 ([] : list (Z * Z)) (2 * ESTACK) (SIGMA WS_strncmp)
      (fun _ => False)
      (fun regs' (_ : word -> option byte) => getr regs' 10 = w64 0 <-> astrn_agree W1 mC x y (Z.of_nat jj))
      W1 regsC mC DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx)
      ([] : list (Z * Z)) ly1 S1 Hp1 _ k1 (- DRAIN_FRAME) (Z_to_bv 64 (BASE + 6212)) HG eq_refl HJ2).
    - rewrite Usp2. lia.
    - rewrite HDF. reflexivity.
    - lia.
    - lia.
    - lia.
    - exact H3.
    - exact H4.
    - exact T1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros _. right. intros [].
    - intros z [].
    - intros z [].
    - intros HPRE HSC.
      assert (HM : Z.min (Z.of_nat jj) (Z.of_nat jj + 1) = Z.of_nat jj) by lia.
      refine (ASTRNCMP ly1 S1 Hp1 W1 regsC mC mdc x y (Z.of_nat jj) (Z.of_nat jj) (Z.of_nat jj)
        HPRE HSC H10 H11 H12 _ _ _ _ _ _ _ _ _ _ _ _ ROMc _); rewrite ?HM.
      + clear - Hjjr Hpq HUL Husedr HBceil HB4096 C1. lia.
      + clear - Hjjr Hpq HUL Husedr Hcapr. destruct Hcapr as [Hq | [Hq | Hq]]; lia.
      + clear - HK4096. unfold x in *. lia.
      + clear - HB4096. unfold y in *. lia.
      + apply (gsc_first_byte W1 mC x (bzs (key_text kn ++ [Z_to_bv 8 0])) (Z.of_nat jj) (Z.of_nat jj) HKgC).
        * lia.
        * rewrite gsc_bzs_len, length_app. cbn [length]. lia.
        * intros i Hi. apply (gsc_key_nz _ HKnz). lia.
        * intros Hlt. lia.
      + apply (gsc_first_byte W1 mC y (dline s1 p q) (Z.of_nat jj) (Z.of_nat jj) HLgC).
        * lia.
        * rewrite (gs_dline_len s1 p q Hpq). lia.
        * intros i Hi. apply (gsc_dline_nth_nz s1 p q Hpq Hnzl). lia.
        * intros Hlt. lia.
      + clear - HKceil HK4096 Hjk C1. unfold x, klen in *. lia.
      + clear - Hjjr Hpq HUL Husedr HBceil HB4096 C1. unfold y in *. lia.
      + intros z Hw. split.
        * replace z with (x + Z.of_nat (Z.to_nat (z - x))) by lia.
          rewrite (gsc_aview_garr8 W1 mC x _ _ HKgC); [discriminate|].
          rewrite gsc_bzs_len, length_app. cbn [length]. lia.
        * rewrite Usp2. clear - Hw HKceil HK4096 Hjk C1 HSTK1. unfold x, klen, ESTACK, DRAIN_FRAME in *. lia.
      + intros z Hw. split.
        * replace z with (y + Z.of_nat (Z.to_nat (z - y))) by lia.
          rewrite (gsc_aview_garr8 W1 mC y _ _ HLgC); [discriminate|].
          rewrite (gs_dline_len s1 p q Hpq). lia.
        * rewrite Usp2. clear - Hw Hjjr Hpq HUL Husedr HBceil HB4096 C1 HSTK1. unfold y, ESTACK, DRAIN_FRAME in *. lia.
      + split; [|split].
        * unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in HKia |- *.
          idtac. unfold x, klen in *. lia.
        * apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 mC mdc x (klen + 1));
            [exact HARc | exact HKin | lia |].
          unfold klen, x in *. rewrite RQK. clear - Hjk. lia.
        * intros Hp0. apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 mC mdc x (klen + 1));
            [exact HARc | exact HKin | lia | unfold klen, x in *; rewrite RQK; clear - Hjk; lia | exact Hp0].
      + split; [|split].
        * unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in HBia |- *.
          idtac. unfold y in *. lia.
        * apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 mC mdc (re_buf e1) (re_cap e1));
            [exact HARc | exact Hbin | unfold y in *; lia |].
          rewrite RQC. clear - Hjjr Hpq HUL Husedr. unfold y in *. lia.
        * intros Hp0. apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 mC mdc (re_buf e1) (re_cap e1));
            [exact HARc | exact Hbin | unfold y in *; lia | rewrite RQC; clear - Hjjr Hpq HUL Husedr; unfold y in *; lia | exact Hp0].
      + split.
        * unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in HKia |- *.
          idtac. unfold x in *. lia.
        * unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in HBia |- *.
          idtac. unfold y in *. lia. }
  cbv beta. intros W2 c2 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hres3 & Hfr3 & Hpres3).
  assert (HAG : astrn_agree W1 mC x y (Z.of_nat jj) <-> nth n (dlH cx s1 p) [] = firstn jj (dline s1 p q)).
  { rewrite (gsc_agree_iff W1 mC x y (Z.of_nat jj) _ _ HKgC HLgC);
      [| lia | rewrite gsc_bzs_len, length_app; cbn [length]; lia | rewrite (gs_dline_len s1 p q Hpq); lia
       | intros i Hi; apply (gsc_key_nz _ HKnz); lia].
    rewrite HJJ, (gsc_nth_H _ _ _ _ _ _ _ _ _ n HLINK Hnlen). fold kn.
    replace (firstn jj (bzs (key_text kn ++ [Z_to_bv 8 0]))) with (bzs (key_text kn))
      by (rewrite <- Hjk; symmetry; apply gsc_bzs_firstn_key).
    reflexivity. }
  jafter_call_keep_pi HS 56%nat regs3 (mrestrict (w_H W1) mem3) HP3 [0%nat] HS3.
  assert (UspA : bv_unsigned (ew Ea 2) = dsp0 cx - DRAIN_FRAME) by (rewrite (OLDa 2%nat ltac:(lia)); exact Usp0).
  assert (HRK : region_kept SEGS Ea (mrestrict (w_H W1) mC) (mrestrict (w_H W1) mem3) gl_frame).
  { split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi gl_frame base_val]; rewrite UspA;
      intros z Hw; [|lia].
    apply (mbyte_of_aview SEGS). apply Hfr3;
      [clear - Hw HSTK1 HSTK2 C1; unfold ESTACK, DRAIN_FRAME in *; lia | intros [] | clear - Hw; unfold ESTACK in *; lia]. }
  specialize (HS3 ltac:(constructor; [exact HRK | constructor])).
  clear HS HRK. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
  remember (havoc Ea 56 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
  assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
  assert (OLDb : forall m, (m < 56)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
  clear HEb.
  prreg HS (10%bv : bv 5) R10c.
  set (r0 := getr regs3 10) in *.
  assert (A60 : ew Eb 60 = Z_to_bv 64 (bv_unsigned r0)) by (rewrite <- R10c, Z_to_bv_bv_unsigned; reflexivity).
  assert (Hr0 : 0 <= bv_unsigned r0 < 2 ^ 64) by exact (bv_unsigned_in_range 64 r0).
  assert (SHOK3 : sh_ok SEGS gl_Bx [] Eb (mrestrict (w_H W1) mem3)) by constructor.
  assert (KP3 : GSKEEP cx W1 m1 mem3).
  { apply (gsc_keep_trans cx W1 m1 mC mem3 KP). split.
    - intros z Hw Hs. exact (Hfr3 z Hw (fun H => H) ltac:(clear - Hs; unfold ESTACK in *; lia)).
    - exact Hpres3. }
  clear KP KC PC Hfr3 Hpres3. rename KP3 into KP.
  (* 0x83b88 beqz a0 *)
  paj_run_tok_xR RUNR HS HJ3 SHOK3 gl_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
  gsl_absorb KP.
  assert (B22 : ew Eb 22 = Z_to_bv 64 (re_hp e1)) by (rewrite (OLDb 22%nat ltac:(lia)), (OLDa 22%nat ltac:(lia)); exact E22).
  assert (B32 : ew Eb 32 = Z_to_bv 64 (re_hp e1 + 8 * Z.of_nat n)) by (rewrite (OLDb 32%nat ltac:(lia)), (OLDa 32%nat ltac:(lia)); exact E32).
  assert (B34 : ew Eb 34 = Z_to_bv 64 SHADOW_OFF) by (rewrite (OLDb 34%nat ltac:(lia)), (OLDa 34%nat ltac:(lia)); exact E34).
  assert (B37 : ew Eb 37 = Z_to_bv 64 (dxSA cx)) by (rewrite (OLDb 37%nat ltac:(lia)), (OLDa 37%nat ltac:(lia)); exact E37).
  assert (B38 : ew Eb 38 = Z_to_bv 64 bg) by (rewrite (OLDb 38%nat ltac:(lia)), (OLDa 38%nat ltac:(lia)); exact E38).
  assert (RK : forall (r : bv 5) (k : nat) rr, getr rr r = ew Eb k -> Nat.ltb k 32 = true ->
    Z.of_nat k = bv_unsigned r -> getr rr r = getr regs1 r).
  { intros r k rr Hr Hk Hkr. apply Nat.ltb_lt in Hk. rewrite Hr, (OLDb k ltac:(lia)), (OLDa k ltac:(lia)).
    apply EREG; [exact Hk | exact Hkr]. }
  psrr_branch_tok RUNR BRR HS SHOK3 gl_Bspan.
  + (* strncmp = 0: the key is held at slot n *)
    rewrite branch_eq_U, (U_atom Eb 60 (bv_unsigned r0) A60 Hr0), (U_lit Eb 0) in Hc by lia.
    apply Z.eqb_eq in Hc. rename Hc into Hr0z.
    assert (Hmt : nth n (dlH cx s1 p) [] = firstn jj (dline s1 p q)).
    { apply HAG, Hres3. fold r0. apply bv_eq. rewrite Hr0z. reflexivity. }
    (* 0x83cac ld a0,24(sp); beqz a0 *)
    paj_run_tok_xR RUNR HS HJ3 SHOK3 gl_Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
    gsl_absorb KP.
    gsl_clear_br.
    psrr_branch_tok RUNR BRR HS SHOK3 gl_Bspan.
    * (* bg = 0: a begin whose key is held: 0x83d9c, then DLN_xR (S q) *)
      rewrite branch_eq_U, (U_atom Eb 38 bg B38 Hbgr), (U_lit Eb 0) in Hc by lia.
      apply Z.eqb_eq in Hc.
      paj_run_to_tok_xR RUNTOR HS HJ3 SHOK3 gl_Bspan A_dr_next. { apply awr_ok_x_of0. awr_ok_tac. }
      gsl_absorb KP.
      pmkst HS.
      prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
      prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (20%bv : bv 5) P20.
      prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (27%bv : bv 5) P27.
      repeat rewrite wvb_collapse in HJ3.
      match goal with |- SRrG _ _ _ {| cfg_ms := mkst _ _ ?mx _; cfg_model := ?mdx |} _ => set (mdF := mdx) in *; set (mF := mx) in * end.
      clear HS SHOK3.
      pose proof (gsc_body_keep_xR B PST ARx MT RP MMAX RG LAWS HG HGSB HV9 HSD HSM R cx Hp kr s1 D p q n (S kf) n W1 regs1
        ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl kd jj bg mF mdF HB HBD HJ3 KP) as HBDF.
      apply (HDLN W1).
      apply (gsc_mk_dln_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q n (S kf) W1 regs1 ly1 S1 Hp1 mF mdF k1 e1 h1 out1
        ev1 LB1 spent jb aa oo ha ks tl kd jj bg _ HBDF Hmt Hc
        (RK _ 2%nat _ P2 eq_refl eq_refl) (RK _ 3%nat _ P3 eq_refl eq_refl) (RK _ 4%nat _ P4 eq_refl eq_refl)
        (RK _ 8%nat _ P8 eq_refl eq_refl) (RK _ 9%nat _ P9 eq_refl eq_refl) (RK _ 18%nat _ P18 eq_refl eq_refl)
        (RK _ 23%nat _ P23 eq_refl eq_refl)).
      -- rewrite P21, B37. reflexivity.
      -- rewrite P20, B37, unsigned_lit_small by (clear - HSA1 HSA2 C1; lia). reflexivity.
      -- rewrite P22, B37, unsigned_lit_small by (clear - HSA1 HSA2 C1; lia). reflexivity.
      -- rewrite P27, B37, unsigned_lit_small by (clear - HSA1 HSA2 C1; lia). reflexivity.
    * (* bg <> 0: an end whose key is held: GF_xR *)
      rewrite branch_eq_U, (U_atom Eb 38 bg B38 Hbgr), (U_lit Eb 0) in Hc by lia.
      apply Z.eqb_neq in Hc.
      paj_run_to_tok_xR RUNTOR HS HJ3 SHOK3 gl_Bspan A_dr_free. { apply awr_ok_x_of0. awr_ok_tac. }
      gsl_absorb KP.
      pmkst HS.
      prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
      prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (20%bv : bv 5) P20.
      gsl_prreg_raw HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
      prreg HS (24%bv : bv 5) PX24. prreg HS (26%bv : bv 5) P26.
      repeat rewrite wvb_collapse in HJ3.
      match goal with |- SRrG _ _ _ {| cfg_ms := mkst _ _ ?mx _; cfg_model := ?mdx |} _ => set (mdF := mdx) in *; set (mF := mx) in * end.
      clear HS SHOK3.
      pose proof (gsc_body_keep_xR B PST ARx MT RP MMAX RG LAWS HG HGSB HV9 HSD HSM R cx Hp kr s1 D p q n (S kf) n W1 regs1
        ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks tl kd jj bg mF mdF HB HBD HJ3 KP) as HBDF.
      apply (HGF W1).
      apply (gsc_mk_gf_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q n (S kf) W1 regs1 ly1 S1 Hp1 mF mdF k1 e1 h1 out1
        ev1 LB1 spent jb aa oo ha ks tl kd jj bg _ HBDF Hmt Hc
        (RK _ 2%nat _ P2 eq_refl eq_refl) (RK _ 3%nat _ P3 eq_refl eq_refl) (RK _ 4%nat _ P4 eq_refl eq_refl)
        (RK _ 8%nat _ P8 eq_refl eq_refl) (RK _ 9%nat _ P9 eq_refl eq_refl) (RK _ 18%nat _ P18 eq_refl eq_refl)
        (RK _ 23%nat _ P23 eq_refl eq_refl) (RK _ 24%nat _ PX24 eq_refl eq_refl)
        (RK _ 20%nat _ P20 eq_refl eq_refl) (RK _ 22%nat _ P22 eq_refl eq_refl)).
      -- rewrite P26, B32. reflexivity.
      -- rewrite P21, denot_lit_U.
         rewrite (gsc_U_shadow Eb 32 34 (re_hp e1 + 8 * Z.of_nat n) 0 B32 B34) by lia.
         rewrite Z.add_0_r. reflexivity.
  + (* strncmp <> 0: no match at slot n *)
    rewrite branch_eq_U, (U_atom Eb 60 (bv_unsigned r0) A60 Hr0), (U_lit Eb 0) in Hc by lia.
    apply Z.eqb_neq in Hc.
    assert (Hmis : nth n (dlH cx s1 p) [] <> firstn jj (dline s1 p q)).
    { intros Hm. apply HAG, Hres3 in Hm. fold r0 in Hm. apply Hc. rewrite Hm. reflexivity. }
    paj_run_to_tok_xR RUNTOR HS HJ3 SHOK3 gl_Bspan A_dr_hnext. { apply awr_ok_x_of0. awr_ok_tac. }
    gsl_absorb KP.
    pmkst HS.
    prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
    prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
    prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) PX24. prreg HS (25%bv : bv 5) P25.
    repeat rewrite wvb_collapse in HJ3.
    match goal with |- SRrG _ _ _ {| cfg_ms := mkst _ _ ?mx _; cfg_model := ?mdx |} _ => set (mdF := mdx) in *; set (mF := mx) in * end.
    clear HS SHOK3.
    apply HGN.
    apply (gsl_exit_gsn_xR cx Hp kr s1 D p q n (S kf) W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb aa oo ha ks
      tl kd jj bg _ mF mdF HB HBD HJ3 KP).
    * split; [exact (RK _ 2%nat _ P2 eq_refl eq_refl)|]. split; [exact (RK _ 3%nat _ P3 eq_refl eq_refl)|].
      split; [exact (RK _ 4%nat _ P4 eq_refl eq_refl)|]. split; [exact (RK _ 8%nat _ P8 eq_refl eq_refl)|].
      split; [exact (RK _ 9%nat _ P9 eq_refl eq_refl)|]. split; [exact (RK _ 18%nat _ P18 eq_refl eq_refl)|].
      split; [exact (RK _ 22%nat _ P22 eq_refl eq_refl)|]. split; [exact (RK _ 23%nat _ P23 eq_refl eq_refl)|].
      split; [exact (RK _ 24%nat _ PX24 eq_refl eq_refl) | exact (RK _ 25%nat _ P25 eq_refl eq_refl)].
    * exact (RK _ 19%nat _ P19 eq_refl eq_refl).
    * exact (RK _ 20%nat _ P20 eq_refl eq_refl).
    * exact Hmis.
Qed.

(* R twin of gs_scan_loop_x *)
Theorem gs_scan_loop_xR : gs_scan_loop_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
unfold gs_scan_loop_stmt_xR. intros cx Hp kr s1 D p q n kf. revert n.
induction kf as [|kf IH]; intros n W1 c1 HB HGL HDLN HGA HGF.
- exfalso. destruct HGL as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1
    & spent & jb & aa & oo & ha & ks & tl & kd & jj & bg & _ & HBD).
  unfold GSBODY_xR in HBD. destruct HBD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hkf & _). lia.
- apply (gsl_body_xR cx Hp kr s1 D p q n kf W1 c1 HB HGL HDLN HGF).
  intros c2 HGN.
  apply (gsl_tail_xR cx Hp kr s1 D p q n kf W1 c2 HB HGN HGA).
  intros Hkf0 c3 HGL3.
  exact (IH (S n) W1 c3 HB HGL3 HDLN HGA HGF).
Qed.

End wR.

(* commit (2): each strict lemma below is its R twin at R := wle (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) section 0) *)
Local Ltac wle_inst := first [ eassumption | intros ? ? H; exact H | intros ?; apply wle_refl
  | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] ].

(* GSN_x from the head's body at a later memory: slot n not matched *)
Lemma gsl_exit_gsn_x : forall cx Hp kr s1 D p q n kf W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks
  tl kd jj bg regs2 m2 md2,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
GSBODY_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q n kf n W1 regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o
  ha ks tl kd jj bg ->
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m2 md2 k1 ->
GSKEEP cx W1 m1 m2 ->
GSREGS regs1 regs2 -> getr regs2 19 = getr regs1 19 -> getr regs2 20 = getr regs1 20 ->
nth n (dlH cx s1 p) [] <> firstn jj (dline s1 p q) ->
GSN_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q n kf W1 (cfg_at SEGS (BASE + A_dr_hnext) regs2 m2 md2).
Proof. eapply (gsl_exit_gsn_xR (@wle SEGS)); wle_inst. Qed.

(* ---- The loop's bottom: GSN_x n (S kf) -> GSL_x (S n) kf when a slot is left, GA_x when none is. ---- *)
Lemma gsl_tail_x : forall cx Hp kr s1 D p q n kf W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> GSN_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q n (S kf) W1 c1 ->
(forall W2 c2, GA_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q W2 c2 ->
   SRr SEGS W2 c2 (dPOST_x B PST ARx MT RP RG cx Hp kr)) ->
((0 < kf)%nat -> forall c2, GSL_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q (S n) kf W1 c2 ->
   SRr SEGS W1 c2 (dPOST_x B PST ARx MT RP RG cx Hp kr)) ->
SRr SEGS W1 c1 (dPOST_x B PST ARx MT RP RG cx Hp kr).
Proof. eapply (gsl_tail_xR (@wle SEGS)); wle_inst. Qed.

(* ---- The loop's body: GSL_x n (S kf) -> GSN_x n (S kf) (no match at slot n), DLN_x (S q) (a begin held at slot n)
   or GF_x (an end held at slot n). ---- *)
Lemma gsl_body_x : forall cx Hp kr s1 D p q n kf W1 c1,
DBASE_x B ARx MT RP MMAX RG cx Hp kr -> GSL_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q n (S kf) W1 c1 ->
(forall W2 c2, DLN_x B PST ARx MT RP MMAX RG cx Hp kr s1 D (S q) W2 c2 ->
   SRr SEGS W2 c2 (dPOST_x B PST ARx MT RP RG cx Hp kr)) ->
(forall W2 c2, GF_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q W2 c2 ->
   SRr SEGS W2 c2 (dPOST_x B PST ARx MT RP RG cx Hp kr)) ->
(forall c2, GSN_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q n (S kf) W1 c2 ->
   SRr SEGS W1 c2 (dPOST_x B PST ARx MT RP RG cx Hp kr)) ->
SRr SEGS W1 c1 (dPOST_x B PST ARx MT RP RG cx Hp kr).
Proof. eapply (gsl_body_xR (@wle SEGS)); wle_inst. Qed.

(* ---- The loop: by induction on the external kf, the number of slots left. ---- *)
Theorem gs_scan_loop_x : gs_scan_loop_stmt_x B PST ARx MT RP MMAX RG.
Proof. eapply (gs_scan_loop_xR (@wle SEGS)); wle_inst. Qed.

End cx.
End bx.
End ax.
