(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: SEGMENTS EPI and END of the ASan+UBSan walk (image B, fuzz_reply.asan-ubsan)
   of fuzz_reply's drain.  The statements are lib/B/W_drain_cx.v dr_epi_stmt and dr_end_stmt (FROZEN; this file
   adds no Section line to its header).  Proves no function (kind: segment lemmas).
   DONORS (structure only; every number below is read from image B's own code, lib/B/W_listing.v slots 1748 ..
   1839 and 1164 .. 1176 (the errno tail the EAGAIN arm shares with TOP), and from lib/B/W_drain_cx.v /
   W_contract.v / W_kit.v / W_rep.v):
     1. lib/A/W_drain_epi.v of a working branch: the same two segments in the same framework on image A
        (A_dr_end 0x83bbc, A_dr_eof 0x83b64, A_dr_epi 0x83b80): the entry states, the runner, the errno call, the
        footprint lemmas (dend_* below) and dend_post.
     2. A working branch 1c09e330abe lib/B/Prog/drain_p_exit_step.v (a Theorem Labs lane's old-framework
        walk of image-B drain): the two arms of the tail (closed: bdr_closed, bdr_eof, bdr_epi; open: bdr_again, the
        __errno_location call 0x83eac -> 0x83eb0, bdr_eset, bdr_eexit, bdr_epi); its SR statements do not
        transport.

   EPI 0x83fc8 .. 0x84000: ld ra,344(sp); ld s0,336(sp) .. ld s11,248(sp); addi sp,sp,352; ret.  It writes nothing.

   END 0x83e94 .. 0x83fc4 (B's code, fuzz_reply.asan-ubsan):
     0x83e94 ld a0,40(sp); add s3,a0,s3; lb a1,0(s3); bnez -> 0x83f5c   the shadow of h->closed: frame slot 40 holds
             (g_s + 8) / 8 and s3 = SHADOW_OFF + 12 j, so s3 + slot 40 = shadow (HA + 8) (g_s mod 8 = 0)
     0x83ea4 lw a0,8(s7); bnez a0 -> 0x83fa8                         h->closed: the closed arm stores s->eof = 1
     0x83eac jal __errno_location (0x8cf28)                          the EAGAIN arm:
     0x83eb0 beqz a0 -> 0x84004 (NONNULL); 0x83eb8 andi a1,a0,3; bnez -> 0x84004 (ALIGN4); the errno shadow check
             against frame slot 240 (SHADOW_OFF); li a1,11; j 0x83574, the errno tail it shares with TOP:
     0x83574 sw a1,0(a0) (errno = 11); li a1,1; beqz a0 (NONNULL); beqz a1 (literal); the shadow check again;
             lw a2,0(a0); li a3,4; beq a2,a3 -> 0x833c0 (not taken: errno is 11); j 0x83f94; the shadow check
             again; lw a0,0(a0); li a1,11; beq a0,a1 -> 0x83fc8 (taken: EPI)
     0x83fa8 addi a0,s5,4; the shadow check against slot 240; li a1,1; sw a1,0(a0) (s->eof = 1); falls into EPI.
   TRAPS (W_drain_cx.v census rows END, and the TOP rows of the shared tail): 0x83eb0 NONNULL and 0x83eb8 ALIGN4 on
   errno, 0x8357c NONNULL and 0x83580 NONNULL_LIT; the errno atom is seated with lib/B/W_traps.v's seat recipe R1
   for an int* (lo 0x10000 >= 1, al2 2 from HERRAL), so the runner decides all four inside the run, with no
   branch stop (W_traps.v trap_nonnull / trap_align4 are the facts R1 encodes; this file has no trap lemma of its
   own).  The `bnez` to 0x83f5c (h->closed), 0x83f70 / 0x83ef8 / 0x84018 (errno) and 0x84008 (s->eof) are ASan
   slow paths, decided by the shadow entries dSH1 / errno's / dSH2.

   ARx FORM (an internal work row, the image-B twin of image A's slice B): Section cx proves dr_epi_x and dr_end_x,
   W_drain_cx_x.v's dr_epi_stmt_x and dr_end_stmt_x at the room texts, over any allocator relation ARx, its journal at
   W_contract_x.v's DRAIN_STK_x; the AR walk (Section c: dr_epi, dr_end) is unchanged. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_drain_cx_x.
(* route R: SRrG (Reusable YA0nH) and the R specs (W_contract_xR.v), for the Section wR twins *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR.
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
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).

(* ---- EPI: the epilogue 0x83fc8.  The entry state seats the 13 saves (atoms 32 .. 44 = the caller's s11 .. ra, the
   order of W_drain_cx.v DR_SAVED) at 248(sp) .. 344(sp) (DR_SAVE_OFF); atom 45 is the shadow base, unused. ---- *)
Definition dBxX : sv := SOff 45 0.
Definition depi_regions : smem :=
[ YP09.mkRegion (Some 2%nat) 248 DRAIN_FRAME 248 248
  (map (fun i => YP09.mkChunk (248 + 8 * Z.of_nat i) (CVal 8 (SOff (32 + i) 0))) (seq 0 13)) ].
Definition depi_facts : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (45%nat, mkAF SB SB 0) ] [] [].
Definition dss_epi : sstate := mkSS A_dr_epi sr_atoms depi_regions None depi_facts.
Definition depi_extra (regsE : bvmap 5 word) : list word := map (getr regsE) DR_SAVED ++ [Z_to_bv 64 SB].
Lemma nth_depi_extra : forall regsE i, (i < 13)%nat ->
  nth i (depi_extra regsE) (Z_to_bv 64 0) = getr regsE (nth i DR_SAVED 0%bv).
Proof.
intros regsE i Hi. unfold depi_extra. rewrite app_nth1 by (rewrite length_map; cbn; lia).
rewrite (nth_indep _ _ (getr regsE 0%bv)) by (rewrite length_map; cbn; lia). rewrite List.map_nth. reflexivity.
Qed.
Lemma dr_epi_entry : forall W regsX memX regsE,
alloc_ceiling <= spZ regsX -> spZ regsX + DRAIN_FRAME <= 2 ^ 47 -> 2 ^ 46 <= spZ regsX -> spZ regsX mod 16 = 0 ->
dr_saved (PI := PI) W memX (spZ regsX) regsE ->
st_ok_pi SEGS VAL (Eimg (Ereg regsX (depi_extra regsE))) dss_epi
(restrict (w_H W) (mkst regsX (Z_to_bv 64 (BASE + A_dr_epi)) memX (seg_rom SEGS))).
Proof.
intros W regsX memX regsE Hceil Htop Hlo Hal HSV.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regsX (depi_extra regsE))).
assert (E2 : ew E 2 = getr regsX 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsX _ 2 2%bv eq_refl)).
assert (E45 : ew E 45 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsX _ 13)).
assert (Usp : bv_unsigned (ew E 2) = spZ regsX) by (rewrite E2; reflexivity).
unfold dss_epi, A_dr_epi. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold depi_regions. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [unfold DRAIN_FRAME in *; lia|]. split; [unfold DRAIN_FRAME in *; lia|]. split; [intros o Ho; lia|].
  apply Forall_map. apply Forall_forall. intros i Hi. apply in_seq in Hi. cbn [Nat.add] in Hi.
  apply (chunk_ok_val SEGS E _ (spZ regsX) (248 + 8 * Z.of_nat i) 8 _ (bv_unsigned (getr regsE (nth i DR_SAVED 0%bv)))).
  + cbn [sv_denot]. subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    rewrite ew_Ereg_extra, nth_depi_extra by lia.
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + pose proof (bv_unsigned_in_range 64 (getr regsE (nth i DR_SAVED 0%bv))) as R. change (bv_modulus 64) with (2 ^ 64) in R. zside.
  + zside.
  + replace (spZ regsX + (248 + 8 * Z.of_nat i)) with (spZ regsX + DR_SAVE_OFF + 8 * Z.of_nat i)
      by (unfold DR_SAVE_OFF; lia).
    exact (HSV i ltac:(lia)).
- cbn [pairwise_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [depi_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E45, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold DRAIN_FRAME in Htop. revert Hceil Htop Hlo Hal. clear. unfold SB. intros. repeat match goal with |- _ /\ _ => split end; (exact I || lia).
Qed.

Theorem dr_epi : dr_epi_stmt B RG.
Proof.
unfold dr_epi_stmt. intros cx ly1 S1 W1 m1 md1 k1 regs1 Q HJ HspX H3 H4 HraE HSV HQ.
unfold cfg_at.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
rewrite !Z.add_0_r in Hal16, Hslo, Hshi, Hstk0.
assert (HDS : DRAIN_STK = 16880) by reflexivity.
pose proof (dr_epi_entry W1 regs1 m1 (dxregs cx) ltac:(unfold DRAIN_FRAME in *; lia) ltac:(unfold DRAIN_FRAME in *; lia)
  ltac:(unfold DRAIN_FRAME in *; lia) ltac:(unfold DRAIN_FRAME in *; rewrite HspX; rewrite Zminus_mod, Hal16; reflexivity)
  ltac:(rewrite HspX; exact HSV)) as HS.
remember (Eimg (Ereg regs1 (depi_extra (dxregs cx)))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EX : forall i, (i < 13)%nat -> ew E (32 + i) = getr (dxregs cx) (nth i DR_SAVED 0%bv)).
{ intros i Hi. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. exact (nth_depi_extra (dxregs cx) i Hi). }
assert (E2 : ew E 2 = getr regs1 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs1 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs1 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 4 4%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs1) by (rewrite E2; reflexivity).
assert (SHOK : sh_ok SEGS dBxX [] E (mrestrict (w_H W1) m1)) by constructor.
clear HE.
paj_run_tok RUN HS HJ SHOK Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19.
prreg HS (20%bv : bv 5) R20. prreg HS (21%bv : bv 5) R21. prreg HS (22%bv : bv 5) R22. prreg HS (23%bv : bv 5) R23.
prreg HS (24%bv : bv 5) R24. prreg HS (25%bv : bv 5) R25. prreg HS (26%bv : bv 5) R26. prreg HS (27%bv : bv 5) R27.
eapply (RET W1 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
assert (RA : getr (ms_regs ms) 1 = getr (dxregs cx) 1) by (rewrite R1; exact (EX 12%nat ltac:(lia))).
rewrite RA, HraE. apply HQ.
- intros r Hr. unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
  + replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R2, Usp, HspX.
    replace (dsp0 cx - DRAIN_FRAME + 352) with (dsp0 cx) by (unfold DRAIN_FRAME; lia).
    unfold dsp0, spZ. apply Z_to_bv_bv_unsigned.
  + replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R3, E3. exact H3.
  + replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R4, E4. exact H4.
  + replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R8. exact (EX 11%nat ltac:(lia)).
  + replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R9. exact (EX 10%nat ltac:(lia)).
  + replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R18. exact (EX 9%nat ltac:(lia)).
  + replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R19. exact (EX 8%nat ltac:(lia)).
  + replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R20. exact (EX 7%nat ltac:(lia)).
  + replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R21. exact (EX 6%nat ltac:(lia)).
  + replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R22. exact (EX 5%nat ltac:(lia)).
  + replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R23. exact (EX 4%nat ltac:(lia)).
  + replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R24. exact (EX 3%nat ltac:(lia)).
  + replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R25. exact (EX 2%nat ltac:(lia)).
  + replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R26. exact (EX 1%nat ltac:(lia)).
  + replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R27. exact (EX 0%nat ltac:(lia)).
- unfold arm. intros x. apply HFr. intros (r & Hin & Hr). cbn [ss_mem dss_epi depi_regions In] in Hin.
  destruct Hin as [<- | []]. cbn [YP09.r_wlo YP09.r_whi] in Hr. lia.
- apply (ajournal_gx_materialize SEGS B LAWS pa_segs_low). exact HJ.
Qed.

(* ---- END: DEND 0x83e94.  The entry state: the stack region holds frame slot 40 ((g_s + 8) / 8, read as
   (A_OBJ 19 + 8) >> 3) and slot 240 (the shadow base, atom 32 = SB); h->closed (cl) at HA + 8 is seated as a
   literal so the runner decides 0x83ea8.  s3 (atom 19) = SHADOW_OFF + 12 j is the shadow base of the first shadow
   check: s3 + slot 40 = SB + 12 j + (g_s + 8) / 8, the shent of g_s's slot j (dSH1, at A_OBJ 19's offsets
   0 .. 96 with base dBx1).  The checks against slot 240 (errno, s->eof) use dBx2 = atom 32. ---- *)
Lemma dend_den : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. rewrite <- H. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma dend_U_srl : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
U E (SAlu ALU_SRL (SOff n c) (SLit 3)) = (v + c) / 8.
Proof.
intros E n v c Hn Hv Hc. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E n v c Hn Hv Hc), U_SLit, (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
apply zcanon_id. unfold M64. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Lemma dend_d8 : forall x, 0 <= x < 2 ^ 64 -> 0 <= x / 8 < 2 ^ 61.
Proof. intros x Hx. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.

Definition dend_stack : YP09.region :=
YP09.mkRegion (Some 2%nat) 40 248 40 40
  [ YP09.mkChunk 40 (CVal 8 (SAlu ALU_SRL (SOff (A_OBJ 19) 8) (SLit 3)));
    YP09.mkChunk 240 (CVal 8 (SOff 32 0)) ].
Definition dend_hreg (cl : Z) : YP09.region :=
YP09.mkRegion (Some 23%nat) 8 12 8 8 [YP09.mkChunk 8 (CVal 4 (SLit cl))].
Definition dend_regions (cl : Z) : smem := [ dend_stack; dend_hreg cl ].
Definition dend_facts (j : nat) : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (19%nat, mkAF (SB + 12 * Z.of_nat j) (SB + 12 * Z.of_nat j) 0);
  (21%nat, mkAF 4096 0x7fffff800000 0); (32%nat, mkAF SB SB 0); (A_OBJ 19, mkAF 0x10000 IMG_TOP 3) ] [] [].
Definition dss_end (j : nat) (cl : Z) : sstate := mkSS A_dr_end sr_atoms (dend_regions cl) None (dend_facts j).
Definition dend_extra : list word := [Z_to_bv 64 SB].
Definition dBx1 : sv := SOff 19 0.
Definition dBx2 : sv := SOff 32 0.
Definition dSH1 : list shent := [ mkSHE (A_OBJ 19) 0 96 ].

Lemma dend_entry : forall (W : world SEGS) regs m (j : nat) cl SA,
(j < 4)%nat ->
getr regs 21 = w64 SA -> getr regs 23 = w64 (rg_s RG + ASRC * Z.of_nat j) ->
getr regs 19 = w64 (SHADOW_OFF + 12 * Z.of_nat j) ->
4096 <= SA <= 0x7fffff800000 ->
alloc_ceiling <= spZ regs -> spZ regs + DRAIN_FRAME <= 2 ^ 47 -> 2 ^ 46 <= spZ regs -> spZ regs mod 16 = 0 ->
val_mem SEGS (arm W m) (spZ regs + 40) 8 ((rg_s RG + 8) / 8) ->
val_mem SEGS (arm W m) (spZ regs + 240) 8 SHADOW_OFF ->
val_mem SEGS (arm W m) (rg_s RG + ASRC * Z.of_nat j + 8) 4 cl -> 0 <= cl <= 1 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs dend_extra)) (dss_end j cl)
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_end)) m (seg_rom SEGS))).
Proof.
intros W regs m j cl SA Hj R21 R23 R19 HSA Hceil Htop Hlo Hal V40 V240 Hcl Rcl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof HGSB as (G1 & G2 & G3). unfold IMG_TOP in G2.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs dend_extra)).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ n r Hr)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E260 : ew E (A_OBJ 19) = Z_to_bv 64 (rg_s RG))
  by (rewrite <- HVS; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (U2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EREG 2%nat 2%bv) by (first [lia | reflexivity]); reflexivity).
assert (U19 : bv_unsigned (ew E 19) = SB + 12 * Z.of_nat j)
  by (rewrite (EREG 19%nat 19%bv) by (first [lia | reflexivity]); rewrite R19, unsigned_lit_small by (unfold SHADOW_OFF; lia); reflexivity).
assert (U21 : bv_unsigned (ew E 21) = SA)
  by (rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); rewrite R21; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = rg_s RG + ASRC * Z.of_nat j)
  by (rewrite (EREG 23%nat 23%bv) by (first [lia | reflexivity]); rewrite R23; apply unsigned_lit_small; unfold ASRC in *; lia).
assert (U32 : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (U260 : bv_unsigned (ew E (A_OBJ 19)) = rg_s RG)
  by (rewrite E260; apply unsigned_lit_small; unfold ASRC in *; lia).
pose proof (dend_d8 (rg_s RG + 8) ltac:(unfold ASRC in *; lia)) as D8.
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold dend_regions, dend_stack, dend_hreg.
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U2. split; [unfold DRAIN_FRAME in *; lia|]. split; [unfold DRAIN_FRAME in *; lia|].
    split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * apply (chunk_ok_val SEGS E _ _ 40 8 _ ((rg_s RG + 8) / 8));
        [ apply dend_den; apply (dend_U_srl E (A_OBJ 19) (rg_s RG) 8 E260); unfold ASRC in *; lia
        | zside | zside | exact V40 ].
    * apply (chunk_ok_val SEGS E _ _ 240 8 _ SHADOW_OFF);
        [ apply dend_den; apply (U_atom E 32 SB E32); unfold SB; lia
        | unfold SHADOW_OFF; zside | zside | exact V240 ].
  + rewrite U23. split; [unfold ASRC in *; lia|]. split; [unfold ASRC in *; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ _ 8 4 (SLit cl) cl); [reflexivity | cbn; lia | cbn; lia | exact Hcl].
- unfold dend_regions, dend_stack, dend_hreg. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U23.
  split; [split; [|exact I] | split; [exact I | exact I]]. right. unfold ASRC in *. lia.
- split; [|split; [exact I | exact I]].
  cbn [dend_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U2, U19, U21, U32, U260.
  rewrite ?Z.pow_0_r, ?Z.mod_1_r. change (2 ^ 4) with 16. change (2 ^ 3) with 8.
  unfold SB, IMG_TOP, ASRC, DRAIN_FRAME in *.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma dend_shent1 : forall ly S (W : world SEGS) mem md E (j : nat),
AR SEGS B ly S W mem md -> (j < 4)%nat ->
U E dBx1 = SHADOW_OFF + 12 * Z.of_nat j -> U E (SOff (A_OBJ 19) 0) = rg_s RG ->
shent_ok SEGS dBx1 E (mrestrict (w_H W) mem) (mkSHE (A_OBJ 19) 0 96).
Proof.
intros ly S W mem md E j HAR Hj HB Hm.
pose proof HGSB as (G1 & G2 & G3). unfold IMG_TOP in G2.
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm. rewrite <- (aview_rd_of SEGS).
pose proof (azs_range_addressable B LAWS ly S W mem md (rg_s RG) (4 * ASRC) HAR HGSZ) as HRA.
split.
- intros x Hx. destruct (HRA (x + ASRC * Z.of_nat j) ltac:(unfold ASRC in *; lia)) as (s & Hs & Hok).
  exists s. split.
  + unfold shadow_of_addr in *. replace (SHADOW_OFF + 12 * Z.of_nat j + x / 8)
      with (SHADOW_OFF + (x + ASRC * Z.of_nat j) / 8); [exact Hs|].
    unfold ASRC. replace (x + 96 * Z.of_nat j) with (x + (12 * Z.of_nat j) * 8) by lia.
    rewrite Z.div_add by lia. lia.
  + unfold saddr_ok in *. unfold ASRC in Hok.
    replace ((x + 96 * Z.of_nat j) mod 8) with (x mod 8) in Hok; [exact Hok|].
    replace (x + 96 * Z.of_nat j) with (x + (12 * Z.of_nat j) * 8) by lia. rewrite Z.mod_add by lia. reflexivity.
- intros a Ha. unfold SHADOW_OFF, ASRC in *. lia.
Qed.

(* the frame facts the entry state needs, from the journal's stack window *)
Lemma dend_sp : forall cx ly1 S1 W1 m1 md1 k1 regs1,
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m1 md1 k1 ->
spZ regs1 = dsp0 cx - DRAIN_FRAME ->
alloc_ceiling <= spZ regs1 /\ spZ regs1 + DRAIN_FRAME <= 2 ^ 47 /\ 2 ^ 46 <= spZ regs1 /\ spZ regs1 mod 16 = 0.
Proof.
intros cx ly1 S1 W1 m1 md1 k1 regs1 HJ HspX.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
rewrite !Z.add_0_r in Hal16, Hslo, Hshi, Hstk0.
assert (HDS : DRAIN_STK = 16880) by reflexivity.
split; [unfold DRAIN_FRAME in *; lia|]. split; [unfold DRAIN_FRAME in *; lia|]. split; [unfold DRAIN_FRAME in *; lia|].
rewrite HspX, Zminus_mod, Hal16. reflexivity.
Qed.

Definition dr_eof_region : YP09.region := YP09.mkRegion (Some 21%nat) 4 8 4 8 [].
Definition dSH2 : list shent := [ mkSHE 21 4 8 ].

(* The closed arm: 0x83e94 .. 0x83fa4 to the eof store 0x83fa8 (A_dr_eof), then s->eof = 1 to EPI 0x83fc8. *)
Lemma dend_closed : forall cx ly1 S1 W1 m1 md1 k1 regs1 (Q : world SEGS -> config -> Prop),
DBASE B MT MMAX RG cx ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m1 md1 k1 ->
In (dxG cx, ATABLE) (ablocks B ly1 S1) ->
awr W1 m1 (dxSA cx) AENT ->
spZ regs1 = dsp0 cx - DRAIN_FRAME ->
getr regs1 21 = w64 (dxSA cx) -> getr regs1 23 = w64 (dHA RG cx) ->
getr regs1 19 = w64 (SHADOW_OFF + 12 * Z.of_nat (dxj cx)) ->
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 40) 8 ((rg_s RG + 8) / 8) ->
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 240) 8 SHADOW_OFF ->
val_mem SEGS (arm W1 m1) (dHA RG cx + 8) 4 1 ->
(forall regsF mF mdF,
  getr regsF 2 = getr regs1 2 -> getr regsF 3 = getr regs1 3 -> getr regsF 4 = getr regs1 4 ->
  @ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 mF mdF k1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (dxSA cx + 4 <= a < dxSA cx + 8) ->
     aview SEGS (w_H W1) mF a = aview SEGS (w_H W1) m1 a) ->
  (forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) mF a) ->
  val_mem SEGS (arm W1 mF) (dxSA cx + 4) 4 1 ->
  SRr SEGS W1 (cfg_at SEGS (BASE + A_dr_epi) regsF mF mdF) Q) ->
SRr SEGS W1 (cfg_at SEGS (BASE + A_dr_end) regs1 m1 md1) Q.
Proof.
intros cx ly1 S1 W1 m1 md1 k1 regs1 Q HB HJ HGin HAW Hsp R21 R23 R19 V40 V240 Hcl KC.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as (_ & _ & _ & HGle & HSAle & _ & _ & _ & _ & Hj & _).
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE HAR HGin) as (_ & HG4 & HGc & Hap & _).
assert (RQT : req_size ATABLE = 896) by reflexivity.
rewrite RQT in HGc, Hap.
assert (HSA : 4096 <= dxSA cx <= 0x7fffff800000) by (unfold AENT, ATABLE in *; lia).
destruct (dend_sp cx ly1 S1 W1 m1 md1 k1 regs1 HJ Hsp) as (Sp1 & Sp2 & Sp3 & Sp4).
unfold dHA in R23, Hcl.
rewrite <- Hsp in V40, V240.
pose proof (dend_entry W1 regs1 m1 (dxj cx) 1 (dxSA cx) Hj R21 R23 R19 HSA Sp1 Sp2 Sp3 Sp4 V40 V240 Hcl ltac:(lia)) as HS.
remember (Eimg (Ereg regs1 dend_extra)) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E260 : ew E (A_OBJ 19) = Z_to_bv 64 (rg_s RG))
  by (rewrite <- HVS; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (UB1 : U E dBx1 = SHADOW_OFF + 12 * Z.of_nat (dxj cx))
  by (unfold dBx1; apply U_atom; [rewrite (EREG 19%nat 19%bv) by (first [lia | reflexivity]); exact R19 | unfold SHADOW_OFF; lia]).
assert (U260 : U E (SOff (A_OBJ 19) 0) = rg_s RG)
  by (apply U_atom; [exact E260 | pose proof HGSB; unfold ASRC, IMG_TOP in *; lia]).
assert (UB2 : U E dBx2 = SHADOW_OFF) by (unfold dBx2; apply U_atom; [exact E32 | unfold SHADOW_OFF; lia]).
assert (U21 : U E (SOff 21 0) = dxSA cx)
  by (apply U_atom; [rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); exact R21 | lia]).
assert (B21 : bv_unsigned (ew E 21) = dxSA cx)
  by (rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); rewrite R21; apply unsigned_lit_small; lia).
assert (B2 : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME)
  by (rewrite (EREG 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp).
assert (SHOK : sh_ok SEGS dBx1 dSH1 E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor]. exact (dend_shent1 ly1 S1 W1 m1 md1 E (dxj cx) HAR Hj UB1 U260). }
clear HE.
unfold cfg_at. change (w64 (BASE + A_dr_end)) with (Z_to_bv 64 (BASE + A_dr_end)).
set (j := dxj cx) in *. clearbody j.
destruct j as [|[|[|[|jj]]]]; [| | | | exfalso; lia].
all: paj_run_to_tok RUNTO HS HJ SHOK Bspan A_dr_eof; [apply awr_ok_x_of0; awr_ok_tac|].
all: rename HFr into FR1; rename HG0 into GR1; clear HF.
all: pose proof (st_ok_pi_submem _ _ _ [dend_stack] HS ltac:(submem_tac) eq_refl) as HS0; clear HS.
all: assert (RGOK : region_ok SEGS E (ms_mem (restrict (w_H W1) ms)) dr_eof_region);
  [ unfold region_ok, dr_eof_region;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
    rewrite B21; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
    intros o Ho; apply (writable_kept (w_H W1) m1 (ms_mem ms)); [apply (apresent_grows _ _ _ _ GR1)|];
    exact (HAW o ltac:(unfold AENT; lia)) |].
all: pose proof (st_ok_pi_add_region _ _ _ dr_eof_region HS0 eq_refl RGOK) as HS1; clear HS0.
all: match type of HS1 with ?d -> _ => assert (HD1 : d); [|specialize (HS1 HD1); clear HD1] end;
  [ cbn [ss_mem all_disjoint]; unfold extent_disjoint, dr_eof_region, dend_stack;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite B21, B2;
    split; [left; unfold DRAIN_FRAME, AENT, ATABLE in *; lia | exact I] |].
all: cbn [ss_pc ss_regs ss_resv ss_facts ss_mem] in HS1.
all: assert (SHOK2 : sh_ok SEGS dBx2 dSH2 E (mrestrict (w_H W1) (ms_mem ms)));
  [ unfold sh_ok, dSH2; apply Forall_cons; [|apply Forall_nil];
    eapply (shent_ok_of_range SEGS (w_H W1) (ms_mem ms) E dBx2 21%nat (dxSA cx + 4) 4 (dxSA cx) 4 8);
    [ eapply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 (ms_mem ms) _ (dxG cx) ATABLE);
      [ exact (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) | exact HGin | lia
      | rewrite RQT; unfold AENT, ATABLE in *; lia ]
    | exact UB2 | exact U21 | lia | lia
    | intros x Hx; rewrite Z.min_l, Z.max_r in Hx by lia;
      unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, AENT, ATABLE in *; lia ] |].
all: paj_run_to_tok RUNTO HS1 HJ SHOK2 Bspan A_dr_epi;
  [ cbn [ss_mem]; apply awr_ok_x_cons;
    [ unfold dr_eof_region; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite B21;
      intros x Hx; left; split; [|lia];
      unfold awr_byte; right; left; split;
      [ exists (dxSA cx, dxSA cx + AENT); split; [left; reflexivity | cbn [fst snd]; unfold AENT; lia]
      | exists (dxG cx), ATABLE; split; [exact HGin | rewrite RQT; unfold AENT, ATABLE in *; lia] ]
    | apply awr_ok_x_cons; [ intros x Hx; unfold dend_stack in Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; lia
      | apply awr_ok_x_nil ] ] |].
all: rename HFr into FR2; rename HG0 into GR2; clear HF.
all: prreg HS1 (2%bv : bv 5) X2; prreg HS1 (3%bv : bv 5) X3; prreg HS1 (4%bv : bv 5) X4.
all: pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS1 eq_refl) as RF; cbn [ms_mem restrict] in RF.
all: pmkst HS1.
all: apply KC;
  [ rewrite X2; apply EREG; [lia | reflexivity]
  | rewrite X3; apply EREG; [lia | reflexivity]
  | rewrite X4; apply EREG; [lia | reflexivity]
  | exact HJ
  | intros a Ha Hn;
    rewrite (aview_kept_out _ _ (w_H W1) (ms_mem ms) (ms_mem ms0) FR2 a Ha);
    [ apply (aview_kept_out _ _ (w_H W1) m1 (ms_mem ms) FR1 a Ha);
      intros (r & Hin & Hr); cbn in Hin; destruct Hin as [<- | [<- | []]]; cbn in Hr; lia
    | intros (r & Hin & Hr); cbn in Hin; destruct Hin as [<- | [<- | []]];
      [ cbn [dr_eof_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite B21 in Hr; lia
      | cbn in Hr; lia ] ]
  | intros a Hp; apply (apresent_grows _ _ _ _ GR2); apply (apresent_grows _ _ _ _ GR1); exact Hp
  | unfold arm; eapply (field_of_region _ _ 21%nat (dxSA cx) _ 4 8 4 8 4 4%N (SLit 1) 1 RF);
    [ rewrite ?ew_ewset_other by lia; exact B21 | left; reflexivity | reflexivity | cbn; lia | cbn; lia ] ].
Qed.

(* The EAGAIN arm: 0x83e94 .. 0x83eac to the __errno_location call, then 0x83eb0 .. 0x83ed4, TOP's errno tail
   0x83574 .. 0x835a4 (errno = 11, read back twice) and 0x83f94 .. 0x83fa4 to EPI 0x83fc8.  After the call the
   stack region (slot 240) is kept and the errno atom (CLOB's a0, atom 44) gets R1's int* fact, al2 2 (HERRAL),
   which decides the traps 0x83eb0 / 0x83eb8 / 0x8357c; errno's 4 bytes are a G_DR cell. *)
Lemma dend_eagain : forall cx ly1 S1 W1 m1 md1 k1 regs1 (Q : world SEGS -> config -> Prop),
DBASE B MT MMAX RG cx ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m1 md1 k1 ->
In (dxG cx, ATABLE) (ablocks B ly1 S1) ->
awr W1 m1 (as_errno B) 4 ->
spZ regs1 = dsp0 cx - DRAIN_FRAME ->
getr regs1 3 = getr (dxregs cx) 3 -> getr regs1 4 = getr (dxregs cx) 4 ->
getr regs1 21 = w64 (dxSA cx) -> getr regs1 23 = w64 (dHA RG cx) ->
getr regs1 19 = w64 (SHADOW_OFF + 12 * Z.of_nat (dxj cx)) ->
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 40) 8 ((rg_s RG + 8) / 8) ->
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 240) 8 SHADOW_OFF ->
val_mem SEGS (arm W1 m1) (dHA RG cx + 8) 4 0 ->
(forall regsF mF mdF,
  getr regsF 2 = getr regs1 2 -> getr regsF 3 = getr regs1 3 -> getr regsF 4 = getr regs1 4 ->
  @ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 mF mdF k1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= a < dsp0 cx - DRAIN_FRAME) ->
     aview SEGS (w_H W1) mF a = aview SEGS (w_H W1) m1 a) ->
  (forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) mF a) ->
  val_mem SEGS (arm W1 mF) (as_errno B) 4 11 ->
  SRr SEGS W1 (cfg_at SEGS (BASE + A_dr_epi) regsF mF mdF) Q) ->
SRr SEGS W1 (cfg_at SEGS (BASE + A_dr_end) regs1 m1 md1) Q.
Proof.
intros cx ly1 S1 W1 m1 md1 k1 regs1 Q HB HJ HGin HAWE Hsp H3 H4 R21 R23 R19 V40 V240 Hcl KC.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as (HPRE0 & _ & _ & HGle & HSAle & _ & _ & _ & _ & Hj & _).
pose proof HPRE0 as (_ & _ & _ & Hgp & Htp & _).
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE HAR HGin) as (_ & HG4 & HGc & Hap & _).
assert (RQT : req_size ATABLE = 896) by reflexivity.
rewrite RQT in HGc, Hap.
assert (HSA : 4096 <= dxSA cx <= 0x7fffff800000) by (unfold AENT, ATABLE in *; lia).
destruct (dend_sp cx ly1 S1 W1 m1 md1 k1 regs1 HJ Hsp) as (Sp1 & Sp2 & Sp3 & Sp4).
unfold dHA in R23, Hcl.
rewrite <- Hsp in V40, V240.
pose proof (dend_entry W1 regs1 m1 (dxj cx) 0 (dxSA cx) Hj R21 R23 R19 HSA Sp1 Sp2 Sp3 Sp4 V40 V240 Hcl ltac:(lia)) as HS.
remember (Eimg (Ereg regs1 dend_extra)) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E260 : ew E (A_OBJ 19) = Z_to_bv 64 (rg_s RG))
  by (rewrite <- HVS; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (UB1 : U E dBx1 = SHADOW_OFF + 12 * Z.of_nat (dxj cx))
  by (unfold dBx1; apply U_atom; [rewrite (EREG 19%nat 19%bv) by (first [lia | reflexivity]); exact R19 | unfold SHADOW_OFF; lia]).
assert (U260 : U E (SOff (A_OBJ 19) 0) = rg_s RG)
  by (apply U_atom; [exact E260 | pose proof HGSB; unfold ASRC, IMG_TOP in *; lia]).
assert (SHOK : sh_ok SEGS dBx1 dSH1 E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor]. exact (dend_shent1 ly1 S1 W1 m1 md1 E (dxj cx) HAR Hj UB1 U260). }
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME)
  by (rewrite (EREG 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp).
assert (HERRI : 0x10000 <= as_errno B /\ as_errno B + 4 <= 0x5fc000).
{ assert (HI4 : forall i, 0 <= i < 4 -> in_img SEGS (as_errno B + i)).
  { intros i Hi. apply (proj1 (HG (as_errno B + i) ltac:(unfold G_DR, G_SL, inG; cbn [In];
      repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]))). }
  pose proof (pa_img_range _ (HI4 0 ltac:(lia))) as P0. pose proof (pa_img_range _ (HI4 3 ltac:(lia))) as P3.
  lia. }
clear HE.
unfold cfg_at. change (w64 (BASE + A_dr_end)) with (Z_to_bv 64 (BASE + A_dr_end)).
set (j := dxj cx) in *. clearbody j.
destruct j as [|[|[|[|jj]]]]; [| | | | exfalso; lia].
all: paj_run_tok RUN HS HJ SHOK Bspan; [apply awr_ok_x_of0; awr_ok_tac|].
all: rename HFr into FR1; rename HG0 into GR1; clear HF.
all: pmkst HS.
all: prreg HS (1%bv : bv 5) Q1; prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4.
all: eapply SRr_bind;
  [ eapply (aj_gx_entry_at B LAWS (G_DR B RG) 0 ([] : list (Z * Z)) ESTACK (SIGMA WS_errno_location)
      (fun _ => False) (fun regs' (_ : word -> option byte) => getr regs' 10 = w64 (as_tp B - 164))
      W1 (ms_regs ms) (ms_mem ms) DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx)
      ([] : list (Z * Z)) ly1 S1 _ k1 (- DRAIN_FRAME) _ HG eq_refl HJ);
    [ unfold spZ at 1; rewrite Q2, Usp; lia
    | reflexivity
    | unfold DRAIN_FRAME; lia
    | lia
    | unfold ESTACK, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK; lia
    | rewrite Q3, (EREG 3%nat 3%bv), H3 by (first [lia | reflexivity]); exact Hgp
    | rewrite Q4, (EREG 4%nat 4%bv), H4 by (first [lia | reflexivity]); exact Htp
    | exact Q1
    | apply ret_ok_codeptr_v; [lia | reflexivity]
    | intros _; right; intros []
    | intros a []
    | intros a []
    | intros HPRE _; exact (AERRNO ly1 S1 W1 (ms_regs ms) (ms_mem ms) _ HPRE) ] |].
all: cbv beta; intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Herr & Hfr2 & Hpres2).
all: jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0%nat] HS2.
all: match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end;
  [ apply Forall_cons; [|apply Forall_nil];
    split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val ms_mem restrict]; rewrite Usp;
    intros a Ha;
    [ apply (mbyte_of_aview SEGS); apply (Hfr2 a ltac:(unfold DRAIN_FRAME in *; lia) (fun x => x));
      unfold DRAIN_FRAME in *; lia
    | exfalso; lia ] |].
all: clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS.
all: remember (havoc E 40 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
all: assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
all: assert (OLDa : forall m, (m < 40)%nat -> ew Ea m = ew E m)
  by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
all: clear HEa.
all: prreg HS (10%bv : bv 5) R10.
all: assert (F44 : ew Ea 44 = Z_to_bv 64 (as_errno B)) by (rewrite <- R10, Herr, HERRNO; reflexivity).
all: assert (B44 : bv_unsigned (ew Ea 44) = as_errno B) by (rewrite F44; apply unsigned_lit_small; unfold IMG_TOP in *; lia).
all: apply (st_ok_pi_add_fact _ _ _ 44%nat (mkAF 0x10000 IMG_TOP 2)) in HS;
  [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite B44; change (2 ^ 2) with 4; rewrite HERRAL;
     unfold IMG_TOP in *; repeat split; lia ].
all: apply (st_ok_pi_add_region _ _ _ (YP09.mkRegion (Some 44%nat) 0 4 0 4 [])) in HS;
  [ | vm_compute; reflexivity
    | unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      rewrite B44; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
      intros o Ho; apply (writable_kept (w_H W1) m1 mem2);
      [ intros Hp; apply Hpres2; apply (apresent_grows _ _ _ _ GR1); exact Hp | exact (HAWE o Ho) ]
    | cbn [ss_mem add_atom all_disjoint]; unfold extent_disjoint;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite B44, (OLDa 2%nat) by lia; rewrite Usp;
      split; [left; unfold IMG_TOP, DRAIN_FRAME in *; lia | exact I] ].
all: assert (UB : U Ea dBx2 = SHADOW_OFF)
  by (unfold dBx2; apply U_atom; [rewrite (OLDa 32%nat) by lia; exact E32 | unfold SHADOW_OFF; lia]).
all: assert (UE44 : U Ea (SOff 44 0) = as_errno B) by (apply U_atom; [exact F44 | unfold IMG_TOP in *; lia]).
all: assert (SHOK3 : sh_ok SEGS dBx2 [mkSHE 44 0 4] Ea (mrestrict (w_H W1) mem2));
  [ unfold sh_ok; apply Forall_cons; [|apply Forall_nil];
    eapply (shent_ok_of_range SEGS (w_H W1) mem2 Ea dBx2 44%nat (as_errno B) 4 (as_errno B) 0 4);
    [ apply (azs_range_addressable B LAWS ly1 S1 W1 mem2 md2 (as_errno B) 4);
      [ exact (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) | exact HERRZ ]
    | exact UB | exact UE44 | lia | lia
    | intros x Hx; rewrite Z.min_l, Z.max_r in Hx by lia; unfold SHADOW_OFF, IMG_TOP in *; lia ] |].
all: paj_run_to_tok RUNTO HS HJ2 SHOK3 Bspan A_dr_epi;
  [ cbn [ss_mem]; apply awr_ok_x_cons_g;
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite B44;
      intros a Ha; unfold G_DR, G_SL, inG; cbn [In];
      repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
    | apply awr_ok_x_cons; [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia | apply awr_ok_x_nil ] ] |].
all: rename HFr into FR3; rename HG0 into GR3; clear HF.
all: prreg HS (2%bv : bv 5) X2; prreg HS (3%bv : bv 5) X3; prreg HS (4%bv : bv 5) X4.
all: pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RF; cbn [ms_mem restrict] in RF.
all: pmkst HS.
all: apply KC;
  [ rewrite X2, OLDa by lia; apply EREG; [lia | reflexivity]
  | rewrite X3, OLDa by lia; apply EREG; [lia | reflexivity]
  | rewrite X4, OLDa by lia; apply EREG; [lia | reflexivity]
  | exact HJ2
  | intros a Ha Hn Hsc;
    rewrite (aview_kept_out _ _ (w_H W1) mem2 (ms_mem ms0) FR3 a Ha);
    [ rewrite (Hfr2 a Ha (fun x => x)); [|intros Hs; apply Hsc; lia];
      apply (aview_kept_out _ _ (w_H W1) m1 (ms_mem ms) FR1 a Ha);
      intros (r & Hin & Hr); cbn in Hin; destruct Hin as [<- | [<- | []]]; cbn in Hr; lia
    | intros (r & Hin & Hr); cbn in Hin; destruct Hin as [<- | [<- | []]];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite B44 in Hr; lia
      | cbn in Hr; lia ] ]
  | intros a Hp; apply (apresent_grows _ _ _ _ GR3); apply Hpres2; apply (apresent_grows _ _ _ _ GR1); exact Hp
  | unfold arm; pose proof (field_of_region _ _ 44%nat (as_errno B) _ 0 4 0 4 0 4%N (SLit 11) 11 RF) as VF;
    rewrite Z.add_0_r in VF; apply VF;
    [ rewrite ?ew_ewset_other by lia; exact B44 | left; reflexivity | reflexivity | cbn; lia | cbn; lia ] ].
Qed.

Definition dset_eof (e : rentry) (v : Z) : rentry :=
RE (re_fd e) v (re_skip e) (re_pad1 e) (re_buf e) (re_used e) (re_cap e) (re_hp e) (re_kh e)
  (re_pad2 e) (re_keys e) (re_U e) (re_junk e).

Lemma dset_eof_id : forall e, dset_eof e (re_eof e) = e.
Proof. intros []. reflexivity. Qed.

Lemma dend_aentry_eof : forall ly S (W : world SEGS) m e v,
aentry_ok B ly S W m e -> v = 0 \/ v = 1 -> aentry_ok B ly S W m (dset_eof e v).
Proof. intros ly S W m e v (_ & H) Hv. split; [exact Hv | exact H]. Qed.

Lemma dend_garr8_one4 : forall m a, val_mem SEGS m a 4 1 -> garr8 SEGS m a [1; 0; 0; 0].
Proof.
intros m a H j Hj. cbn [length] in Hj.
split; [|destruct j as [|[|[|[|j]]]]; cbn; lia].
intros k Hk. destruct k as [|k]; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
rewrite (H j Hj). f_equal. destruct j as [|[|[|[|j]]]]; try (vm_compute; reflexivity). lia.
Qed.

Lemma dend_garr8_eof : forall (W : world SEGS) m m' SA e,
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) ->
(forall x, SA <= x < SA + AENT -> ~ (SA + 4 <= x < SA + 8) -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
val_mem SEGS (arm W m') (SA + 4) 4 1 ->
garr8 SEGS (arm W m') SA (bzs (entry_bytes (dset_eof e 1))).
Proof.
intros W m m' SA e HE0 KV Hp1 Hp2 VM.
unfold entry_bytes, dset_eof, re_nheld in HE0 |- *.
cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_kh re_pad2 re_keys re_U re_junk] in HE0 |- *.
unfold bzs in HE0 |- *. rewrite !map_app in HE0 |- *.
apply (garr8_app SEGS) in HE0 as [HA HE0]. apply (garr8_app SEGS) in HE0 as [_ HC].
apply (garr8_app SEGS). split.
- eapply (garr8_frame SEGS); [exact HA|]. intros x Hx. unfold arm. apply (mbyte_of_aview SEGS).
  rewrite length_map, Mem.length_le4 in Hx. apply KV; unfold AENT; lia.
- apply (garr8_app SEGS). rewrite !length_map, !Mem.length_le4 in HC |- *. split.
  + lazymatch goal with |- garr8 _ _ _ (map bz ?l) => replace (map bz l) with [1; 0; 0; 0] by (vm_compute; reflexivity) end.
    apply dend_garr8_one4. replace (SA + Z.of_nat 4) with (SA + 4) by lia. exact VM.
  + eapply (garr8_frame SEGS); [exact HC|]. intros x Hx. unfold arm. apply (mbyte_of_aview SEGS).
    rewrite !length_app, !length_map, !Mem.length_le4, !Mem.length_le8, Hp1, Hp2 in Hx.
    apply KV; unfold AENT; lia.
Qed.

Lemma dend_bk : forall (W : world SEGS) m m' (P : Z -> Prop) a,
(forall x, 0 <= x < 2 ^ 64 -> ~ P x -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
(forall x, apresent (w_H W) m x -> apresent (w_H W) m' x) ->
0 <= a < 2 ^ 64 -> ~ P a -> abyte_kept W m W m' a.
Proof.
intros W m m' P a KV PR Ha HP. split; [exact (KV a Ha HP)|].
unfold arm. apply writable_kept. apply PR.
Qed.

Definition dlow (cx : dcx) (a : Z) : Prop := 0 <= a < alloc_ceiling /\ ~ (dxG cx <= a < dxG cx + ATABLE).

Lemma dend_zall : forall a l j d, zall_disjoint a l -> (j < length l)%nat -> zdisj a (nth j l d).
Proof.
intros a l. induction l as [|b l IH]; intros j d H Hj; cbn in Hj; [lia|].
destruct H as [H1 H2]. destruct j as [|j]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.

Lemma dend_zpw : forall l i j d, zpairwise_disjoint l -> (i < j)%nat -> (j < length l)%nat ->
zdisj (nth i l d) (nth j l d).
Proof.
intros l. induction l as [|a l IH]; intros i j d H Hij Hj; cbn in Hj; [lia|].
destruct H as [H1 H2]. destruct i as [|i].
- destruct j as [|j]; [lia|]. cbn [nth]. apply dend_zall; [exact H1 | lia].
- destruct j as [|j]; [lia|]. cbn [nth]. apply IH; [exact H2 | lia | lia].
Qed.

Lemma dend_errno_sep : forall a,
(rg_s RG <= a < rg_s RG + 4 * ASRC \/ rg_client RG <= a < rg_client RG + 4 \/
 rg_client_broken RG <= a < rg_client_broken RG + 1 \/ rg_send_eintr RG <= a < rg_send_eintr RG + 1 \/
 rg_send_dead RG <= a < rg_send_dead RG + 1 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
 rg_nout RG <= a < rg_nout RG + 8 \/ rg_capout RG <= a < rg_capout RG + 8 \/ rg_out RG <= a < rg_out RG + 8) ->
~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha He.
pose proof (dend_zpw _ 2 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D2.
pose proof (dend_zpw _ 3 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D3.
pose proof (dend_zpw _ 4 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D4.
pose proof (dend_zpw _ 5 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D5.
pose proof (dend_zpw _ 6 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D6.
pose proof (dend_zpw _ 7 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D7.
pose proof (dend_zpw _ 8 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D8.
pose proof (dend_zpw _ 9 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D9.
pose proof (dend_zpw _ 10 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D10.
cbn [nth] in D2, D3, D4, D5, D6, D7, D8, D9, D10. unfold zdisj in *. cbn [fst snd] in *. lia.
Qed.

Lemma dend_low_img : forall cx ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> In (dxG cx, ATABLE) (ablocks B ly S) -> 0x10000 <= a < 0x5fc000 -> dlow cx a.
Proof.
intros cx ly S W mem md a HAR Hin Ha.
pose proof (blk_off_imgP B ly S W mem md _ _ HAR Hin) as Ho.
unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YCbq.off_img in Ho.
pose proof asan_consts as (C1 & _).
assert (RQT : req_size ATABLE = 896) by reflexivity. rewrite RQT in Ho.
unfold dlow, ATABLE in *. lia.
Qed.

Lemma dend_low_blk : forall cx ly S (W : world SEGS) mem md L p n a,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
In (p, n) L -> p <= a < p + req_size n ->
dlow cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S W mem md L p n a HAR HP HL Ha.
assert (Hin : In (p, n) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); right; exact HL).
destruct (al_blocks SEGS B LAWS ly S W mem md p n HAR Hin) as (_ & H4 & Hc & _).
destruct (in_split _ _ HL) as (l1 & l2 & ->).
assert (HP2 : Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: (p, n) :: l1 ++ l2))
  by (eapply Permutation_trans; [exact HP | apply perm_skip; apply Permutation_sym, Permutation_middle]).
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md _ _ _ HAR HP2) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
assert (RQT : req_size ATABLE = 896) by reflexivity. rewrite RQT in Hd.
split; [unfold dlow, ATABLE; lia|].
intros He. apply (blk_img SEGS B LAWS ly S W mem md p n a HAR Hin ltac:(lia)).
apply (proj1 (HG a ltac:(unfold G_DR, G_SL, inG; cbn [In];
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]))).
Qed.

Lemma dend_gs_ok : forall cx ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> In (dxG cx, ATABLE) (ablocks B ly S) -> rg_s RG <= a < rg_s RG + 4 * ASRC ->
dlow cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S W mem md a HAR Hin Ha. pose proof HGSB as (G1 & G2 & _). unfold IMG_TOP in G2.
split; [apply (dend_low_img cx ly S W mem md a HAR Hin); unfold ASRC in *; lia|].
apply dend_errno_sep. left. exact Ha.
Qed.

Lemma dend_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
intros ks. unfold key_ptrs. induction ks as [|k ks IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. cbn [length]. rewrite Mem.length_le8. lia.
Qed.

Lemma dend_recs_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !Mem.length_le8. lia.
Qed.

Lemma dend_fp_entry : forall cx ly S (W : world SEGS) mem md e L,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (aentry_blks e) -> In b L) -> aentry_ok B ly S W mem e ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r ->
dlow cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S W mem md e L HAR HP HB HE r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & _ & _ & Hbuf & _ & Hhp & _ & _ & Hks).
assert (BLK : forall p n, In (p, n) (aentry_blks e) -> 0 <= n -> p <= a < p + n ->
  dlow cx a /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros p n Hin Hn Hpa. pose proof (req_size_pos n Hn) as (_ & Hrq).
  exact (dend_low_blk cx ly S W mem md L p n a HAR HP (HB _ Hin) ltac:(lia)). }
unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
  rewrite length_map, length_app in Ha.
  destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  apply (BLK (re_buf e) (re_cap e)); [| lia | lia].
  unfold aentry_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
- cbn [In] in Hr. destruct Hr as [<- | Hr].
  + unfold gfp in Ha. cbn [fst snd] in Ha.
    destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
    * rewrite Hke in Ha. unfold bzs, key_ptrs in Ha. cbn [map concat length] in Ha. lia.
    * unfold bzs in Ha. rewrite length_map, dend_key_ptrs_len in Ha. unfold re_nheld in Hk1.
      apply (BLK (re_hp e) (re_kh e)); [| lia | lia].
      unfold aentry_blks. apply in_or_app. right. apply in_or_app. left.
      rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity.
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (BLK (key_addr k) (Z.of_nat (length (key_text k)) + 1)); [| lia | lia].
    unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
    apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk.
Qed.

Lemma dend_fp_list : forall cx ly S (W : world SEGS) mem md L LA l lines,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (alist_blks l) -> In b L) -> In (dxG cx, ATABLE) (ablocks B ly S) ->
alist_at B ly S W mem LA l lines -> rg_s RG <= LA -> LA + 16 <= rg_s RG + 4 * ASRC ->
forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r ->
dlow cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S W mem md L LA l lines HAR HP HB HGin HL Hlo Hhi r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
assert (BLK : forall p n, In (p, n) (alist_blks l) -> 0 <= n -> p <= a < p + n ->
  dlow cx a /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros p n Hin Hn0 Hpa. pose proof (req_size_pos n Hn0) as (_ & Hrq).
  exact (dend_low_blk cx ly S W mem md L p n a HAR HP (HB _ Hin) ltac:(lia)). }
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. apply (dend_gs_ok cx ly S W mem md a HAR HGin). lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app, dend_recs_len in Ha.
    destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    apply (BLK (hl_v l) (AREC * hl_cap l)); [| unfold AREC; lia | unfold hl_n, AREC in *; lia].
    unfold alist_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
  + apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (BLK (fst q) (Z.of_nat (length (snd q)) + 1)); [| lia | lia].
    unfold alist_blks. apply in_or_app. right.
    apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))). exact Hq.
Qed.

Lemma dend_fp_src : forall cx ly S (W : world SEGS) mem md L h,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (asrc_blks h) -> In b L) -> In (dxG cx, ATABLE) (ablocks B ly S) -> (dxj cx < 4)%nat ->
asrc_at B ly S W mem (dHA RG cx) h ->
forall r, In r (asrc_fp (dHA RG cx) h) -> forall a, fst r <= a < snd r ->
dlow cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S W mem md L h HAR HP HB HGin Hj HS r Hr a Ha.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
assert (HAr : rg_s RG <= dHA RG cx /\ dHA RG cx + ASRC <= rg_s RG + 4 * ASRC) by (unfold dHA, ASRC; lia).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- cbn [fst snd] in Ha. apply (dend_gs_ok cx ly S W mem md a HAR HGin). lia.
- unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map in Ha.
  pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrq).
  apply (dend_low_blk cx ly S W mem md L (hs_partial h) APARTIAL a HAR HP); [apply HB; left; reflexivity | lia].
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + exact (dend_fp_list cx ly S W mem md L (dHA RG cx + 16) (hs_pending h) false HAR HP
      (fun b Hb => HB b (or_intror (in_or_app _ _ _ (or_introl Hb)))) HGin Hpend
      ltac:(unfold ASRC in *; lia) ltac:(unfold ASRC in *; lia) r Hr a Ha).
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * exact (dend_fp_list cx ly S W mem md L (dHA RG cx + 64) (hs_expected h) true HAR HP
        (fun b Hb => HB b (or_intror (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hb)))))) HGin Hexp
        ltac:(unfold ASRC in *; lia) ltac:(unfold ASRC in *; lia) r Hr a Ha).
    * exact (dend_fp_list cx ly S W mem md L (dHA RG cx + 80) (hs_held h) true HAR HP
        (fun b Hb => HB b (or_intror (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror Hb)))))) HGin Hheld
        ltac:(unfold ASRC in *; lia) ltac:(unfold ASRC in *; lia) r Hr a Ha).
Qed.

Lemma dend_fp_out : forall cx ly S (W : world SEGS) mem md c O mx no cap out L,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (aout_blks cap out) -> In b L) ->
aout_at B RG ly S W mem c O mx no cap out ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r ->
dlow cx a /\ (r <> (as_errno B, as_errno B + 4) -> ~ (as_errno B <= a < as_errno B + 4)).
Proof.
intros cx ly S W mem md c O mx no cap out L HAR HP HB HOUT r Hr a Ha.
assert (GT : In (dxG cx, ATABLE) (ablocks B ly S))
  by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
assert (IMG : forall x, 0x10000 <= x < 0x5fc000 -> dlow cx x)
  by (intros x Hx; exact (dend_low_img cx ly S W mem md x HAR GT Hx)).
assert (GDR : forall x, inG (G_DR B RG) x -> 0x10000 <= x < 0x5fc000)
  by (intros x Hx; exact (pa_img_range _ (proj1 (HG x Hx)))).
pose proof (pa_obj_img 9 ltac:(lia)) as P9. rewrite HV9 in P9.
pose proof HSD as P12. unfold IMG_TOP in P12.
pose proof HSM as (Hs1 & Hs2). unfold IMG_TOP in Hs2.
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
- split; [apply IMG; lia | intros _; apply dend_errno_sep; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dend_errno_sep; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dend_errno_sep; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dend_errno_sep; tauto].
- split; [apply IMG; lia | intros _; apply dend_errno_sep; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dend_errno_sep; tauto].
- split; [apply IMG; lia | intros _; apply dend_errno_sep; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dend_errno_sep; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros Hne; exfalso; apply Hne; reflexivity].
- destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
  pose proof (req_size_pos cap ltac:(lia)) as (_ & Hrq).
  destruct (dend_low_blk cx ly S W mem md L out cap a HAR HP) as [D1 D2];
    [apply HB; unfold aout_blks; rewrite Hc0; left; reflexivity | lia |].
  split; [exact D1 | intros _; exact D2].
Qed.

Lemma dend_aout_ev : forall ly S (W : world SEGS) m m' c O mx no cap out ev,
aout_at B RG ly S W m c O mx no cap out ->
(forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r ->
   ~ (as_errno B <= a < as_errno B + 4) -> abyte_kept W m W m' a) ->
(cap <> 0 -> forall a, out <= a < out + cap -> ~ (as_errno B <= a < as_errno B + 4)) ->
val_mem SEGS (arm W m') (as_errno B) 4 ev -> awr W m' (as_errno B) 4 -> 0 <= ev < 2 ^ 32 ->
aout_at B RG ly S W m' (CTL (ct_cl c) (ct_br c) (ct_dd c) (ct_ei c) ev) O mx no cap out.
Proof.
intros ly S W m m' c O mx no cap out ev
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
   H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) HK HOB VE WE Hev.
assert (KC : forall a n, In (a, a + n) (aout_fp B RG cap out) -> forall x, a <= x < a + n ->
  ~ (as_errno B <= x < as_errno B + 4) -> abyte_kept W m W m' x)
  by (intros a n Hin x Hx Hne; exact (HK (a, a + n) Hin x Hx Hne)).
unfold aout_at. cbn [ct_cl ct_br ct_dd ct_ei ct_ev].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_send_max RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H1]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_send_max RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H2]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_nout RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H3]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_nout RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H4]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_capout RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H5]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_capout RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H6]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_out RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H7]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_out RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H8]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_client RG) 4); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H9]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_client RG) 4); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H10]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_client_broken RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H11]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_client_broken RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H12]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_send_dead RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H13]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_send_dead RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H14]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_send_eintr RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H15]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_send_eintr RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep; repeat (first [left; lia | right]); lia] | exact H16]|].
split; [exact VE|]. split; [exact WE|]. split; [exact Hev|].
do 6 (split; [assumption|]).
destruct H26 as [H26 | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; exact H26|right].
assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
split; [exact Hc|]. split; [exact Hno|]. split; [exact Hin|].
exists junk. split; [exact Hj|].
apply (akept_garr8 W m); [|exact Hg].
intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx.
apply (KC out cap); [unfold aout_fp; rewrite Ec; repeat (first [left; reflexivity | right]) | lia | apply (HOB ltac:(lia)); lia].
Qed.

Lemma dperm_mv : forall (x : Z * Z) l1 l2 l3 r, Permutation (x :: l1 ++ l2 ++ l3 ++ r) (l1 ++ l2 ++ l3 ++ x :: r).
Proof. intros. rewrite !app_assoc. apply Permutation_middle. Qed.

Lemma dend_post : forall cx s1 D ly1 S1 W1 m' md' k1 regs' e1 e' h1 out1 ev' LB1 spent jb a tl,
DBASE B MT MMAX RG cx ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m' md' k1 ->
aregs_preserved (dxregs cx) regs' ->
apres_kept B (dxW cx) (dxmem cx) W1 m' ->
e' = dset_eof e1 (if hs_closed h1 =? 1 then 1 else re_eof e1) ->
garr8 SEGS (arm W1 m') (dxSA cx) (bzs (entry_bytes e')) -> awr W1 m' (dxSA cx) AENT ->
aentry_ok B ly1 S1 W1 m' e' ->
asrc_at B ly1 S1 W1 m' (dHA RG cx) h1 ->
(forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> ~ (dHA RG cx <= x < dHA RG cx + ASRC) ->
   abyte_kept (dxW cx) (dxmem cx) W1 m' x) ->
aout_at B RG ly1 S1 W1 m' (dctl cx (Z.of_nat (length (with_nul (lines (dSTR cx) D)))) ev')
  (if dlive cx then dxO cx ++ LB1 else dxO cx) (dxmx cx)
  (if dlive cx then drain_b_c.ds_no s1 else dxno cx) (drain_b_c.ds_ocap s1) out1 ->
(dlive cx = false -> out1 = dxout cx /\ drain_b_c.ds_ocap s1 = dxcap cx) ->
Permutation (ablocks B ly1 S1)
  ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx) ->
DLINK s1 e1 h1 -> DSAME cx e1 h1 -> DHIST cx s1 D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 ->
J1 (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (drain_b_c.ds_ref s1) ->
drain_b_c.ds_pend s1 = [] -> drain_b_c.ds_eintr s1 = false -> 4096 <= drain_b_c.ds_cap s1 - ulen s1 ->
dlater cx s1 jb a tl -> dbud MT MMAX cx S1 spent tl ->
dPOST B MT RG cx W1 (mkCfg (mkst regs' (getr (dxregs cx) 1) m' (seg_rom SEGS)) md').
Proof.
intros cx s1 D ly1 S1 W1 m' md' k1 regs' e1 e' h1 out1 ev' LB1 spent jb a tl HB HJ HRP HAPK He' HEB HEW HEOK
  HSRC HGK HOUT HDEAD HPERM HDL HDS HDH HJ1 HPE HEIN HROOM HLAT HBUD.
destruct HLAT as (fuel & Hn & Hwf & Ht & Hf).
destruct fuel as [|f]; [unfold dneed in Hn; lia|].
rewrite (drun_end f (dlive cx) (dxmx cx) s1 jb a HROOM HEIN HPE) in Ht, Hf. cbn [fst snd] in Ht, Hf. subst tl.
pose proof HDH as (HPS & HREF & HEXP & HFST & HCAP & HNO & HLB & HND & HSS & _ & _).
assert (HD : D = dPS cx) by (rewrite HPS; unfold pstream, prest; rewrite HPE; symmetry; apply app_nil_r).
subst D.
pose proof HDL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & _).
pose proof HDS as (S1' & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
pose proof HBUD as (Bmo & Bsp & Bcost & _ & _).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPB & _).
pose proof HSRC as (_ & _ & _ & _ & _ & Hcl01 & _ & _ & _ & _ & _ & _ & _ & _ & Hoff & _ & Hov01 & _).
assert (HCAPX : (if dlive cx then drain_b_c.ds_ocap s1 else dxcap cx) = drain_b_c.ds_ocap s1)
  by (revert HDEAD; destruct (dlive cx); intros HDEAD; [reflexivity | symmetry; exact (proj2 (HDEAD eq_refl))]).
assert (HNOX : (if dlive cx then drain_b_c.ds_no s1 else dxno cx) =
  (if dlive cx then dxno cx + dr_tot (dxh cx) else dxno cx))
  by (destruct (dlive cx); [exact HNO | reflexivity]).
assert (HRECS : hl_recs (hs_pending h1) = []) by (rewrite HPE in L7; exact (map_eq_nil _ _ L7)).
subst e'.
unfold dPOST, dr_post.
exists ly1, S1, regs', m', md', k1, (dset_eof e1 (if hs_closed h1 =? 1 then 1 else re_eof e1)), h1, out1, ev', LB1,
  ((dxG cx, ATABLE) :: dxrest cx).
cbv zeta.
change (dr_fin (dxc cx) (dxmx cx) (dxno cx) (dxcap cx) (dxe cx) (dxh cx)) with (dfin cx).
change (dr_live (dxc cx) (dxh cx)) with (dlive cx).
rewrite <- Hf, HCAPX.
split; [reflexivity|].
split; [exact HJ|].
split; [exact HRP|].
split; [exact HAPK|].
split.
{ change (dr_cost MT (dxc cx) (dxmx cx) (dxno cx) (dxcap cx) (dxe cx) (dxh cx)) with (dcost MT cx).
  apply (mle_weaken MT _ _ spent _ MTL Bmo). unfold tr_cost in Bcost. cbn [fold_right] in Bcost. lia. }
split; [exact (Permutation_trans HPB (dperm_mv _ _ _ _ _))|].
split; [exact (Permutation_trans HPERM (dperm_mv _ _ _ _ _))|].
split; [exact HEB|]. split; [exact HEW|]. split; [exact HEOK|].
cbn [dset_eof re_fd re_eof re_cap re_U re_skip re_keys re_hp re_kh].
split; [exact S1'|].
split; [rewrite S5, S2; reflexivity|].
split; [rewrite L1; unfold ulen in HROOM; lia|].
split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|].
split; [exact L5|].
split; [exact S10|].
split; [rewrite L4; exact HND|].
split; [rewrite L4; exact HSS|].
split; [exact HSRC|].
split; [exact HGK|].
split; [exact L11|].
split; [exact HCAP|].
split; [exact S3|]. split; [exact S5|].
split; [rewrite L6, HEIN; reflexivity|].
split; [exact HRECS|].
split; [destruct Hoff as [(_ & Ho) | (r & rs & Hr & _)]; [exact Ho | rewrite HRECS in Hr; discriminate]|].
split; [exact S6|]. split; [exact S7|]. split; [exact S8|].
split; [rewrite L9, HREF; reflexivity|].
split; [exact HEXP|].
split; [exact HFST|].
split; [exact S9|].
split.
{ rewrite L3. destruct HJ1 as (JK & _). rewrite JK, <- L9. unfold hs_state. cbn [ls_k].
  destruct Hov01 as [-> | ->]; reflexivity. }
split.
{ intros H0. rewrite L2. destruct HJ1 as (JK & JW & _).
  assert (Hs : drain_b_c.ds_skip s1 = false)
    by (rewrite L3 in H0; destruct (drain_b_c.ds_skip s1); [discriminate | reflexivity]).
  rewrite (JW Hs), <- L9. reflexivity. }
split; [exact HLB|].
rewrite HNOX in HOUT. exact HOUT.
Qed.

(* ---- END: DEND 0x83e94 -> h->closed ? (s->eof = 1 at 0x83fa8) : (errno = EAGAIN, 0x83eac / 0x83574), then dr_epi. ---- *)
Theorem dr_end : dr_end_stmt B MT MMAX RG.
Proof.
intros HEPI cx s1 D W1 c1 HB HDE.
destruct HDE as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & tl &
  -> & Hsp & H3 & H4 & R21 & R23 & R19 & HFRM & HDM & HNZ & HUS & HDL & HDS & HDH & HJ1 & HPE & HEIN &
  HROOM & HLAT & HBUD).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HDM as (HJ & HROM & HAPK & HFRS & _ & HEB & HEW & HEX & HSRC & HOTH & HGK & HOUT & HDEAD & HPERM).
pose proof HB as (HPRE0 & _ & _ & HGle & HSAle & _ & _ & _ & _ & Hj & _).
pose proof HPRE0 as (_ & Hra & _).
pose proof HFRM as (_ & _ & F40 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F240 & HSV).
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
assert (HGin : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym HPERM)); left; reflexivity).
pose proof HJ as (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
rewrite !Z.add_0_r in Hal16, Hslo, Hshi, Hstk0.
assert (HDS0 : DRAIN_STK = 16880) by reflexivity.
assert (RQT : req_size ATABLE = 896) by reflexivity.
destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE HAR HGin) as (_ & HG4 & HGc & _).
rewrite RQT in HGc.
assert (HERRI : 0x10000 <= as_errno B /\ as_errno B + 4 <= 0x5fc000).
{ assert (HI4 : forall i, 0 <= i < 4 -> in_img SEGS (as_errno B + i)).
  { intros i Hi. apply (proj1 (HG (as_errno B + i) ltac:(unfold G_DR, G_SL, inG; cbn [In];
      repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]))). }
  pose proof (pa_img_range _ (HI4 0 ltac:(lia))) as P0. pose proof (pa_img_range _ (HI4 3 ltac:(lia))) as P3. lia. }
assert (TBE : forall x, dxSA cx <= x < dxSA cx + AENT -> ~ (as_errno B <= x < as_errno B + 4)).
{ intros x Hx He. apply (blk_img SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE x HAR HGin);
    [rewrite RQT; unfold AENT, ATABLE in *; lia|].
  apply (proj1 (HG x ltac:(unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]))). }
assert (HEOK : aentry_ok B ly1 S1 W1 m1 e1).
{ destruct HEX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & _ & X9 & X10 & X11 & X12 & X13 & X14).
  exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj X7 (conj HUS (conj HNZ
    (conj X9 (conj X10 (conj X11 (conj X12 (conj X13 X14)))))))))))))). }
pose proof HEOK as (_ & _ & Hp1 & Hp2 & _).
pose proof HSRC as (_ & _ & Vcl & _ & _ & Hcl01 & _).
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAWE & _).
set (L := aentry_blks e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx) in HPERM.
assert (INL : forall b, In b L -> In b (ablocks B ly1 S1))
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPERM)); right; exact Hb).
assert (FE : forall r, In r (aentry_fp e1) -> forall x, fst r <= x < snd r ->
  dlow cx x /\ ~ (as_errno B <= x < as_errno B + 4)).
{ apply (dend_fp_entry cx ly1 S1 W1 m1 md1 e1 L HAR HPERM); [|exact HEOK].
  intros b Hb. unfold L. apply in_or_app. left. exact Hb. }
assert (FS : forall r, In r (asrc_fp (dHA RG cx) h1) -> forall x, fst r <= x < snd r ->
  dlow cx x /\ ~ (as_errno B <= x < as_errno B + 4)).
{ apply (dend_fp_src cx ly1 S1 W1 m1 md1 L h1 HAR HPERM); [| exact HGin | exact Hj | exact HSRC].
  intros b Hb. unfold L. apply in_or_app. right. apply in_or_app. left. exact Hb. }
assert (FO : forall r, In r (aout_fp B RG (drain_b_c.ds_ocap s1) out1) -> forall x, fst r <= x < snd r ->
  dlow cx x /\ (r <> (as_errno B, as_errno B + 4) -> ~ (as_errno B <= x < as_errno B + 4))).
{ eapply (dend_fp_out cx ly1 S1 W1 m1 md1 _ _ _ _ _ _ L HAR HPERM); [| exact HOUT].
  intros b Hb. unfold L. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
assert (FB : drain_b_c.ds_ocap s1 <> 0 -> forall x, out1 <= x < out1 + drain_b_c.ds_ocap s1 ->
  ~ (as_errno B <= x < as_errno B + 4)).
{ intros Hc x Hx. pose proof (req_size_pos (drain_b_c.ds_ocap s1)) as Hrq.
  pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
  destruct Hblk as [(Hc0 & _) | (Hcp & _ & _)]; [lia|].
  destruct (Hrq ltac:(lia)) as (_ & Hrq').
  refine (proj2 (dend_low_blk cx ly1 S1 W1 m1 md1 L out1 (drain_b_c.ds_ocap s1) x HAR HPERM _ ltac:(lia))).
  unfold L. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
  unfold aout_blks. rewrite (proj2 (Z.eqb_neq _ _) Hc). left. reflexivity. }
assert (FG : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> dlow cx x /\ ~ (as_errno B <= x < as_errno B + 4))
  by (intros x Hx; exact (dend_gs_ok cx ly1 S1 W1 m1 md1 x HAR HGin Hx)).
destruct Hcl01 as [Hc0 | Hc1].
- apply (dend_eagain cx ly1 S1 W1 m1 md1 k1 regs1 _ HB HJ HGin HAWE Hsp H3 H4 R21 R23 R19 F40 F240
    ltac:(rewrite <- Hc0; exact Vcl)).
  intros regsF mF mdF F2 F3 F4 HJF KV PR VE.
  apply (HEPI cx ly1 S1 W1 mF mdF k1 regsF (dPOST B MT RG cx) HJF).
  + unfold spZ in *. rewrite F2. exact Hsp.
  + rewrite F3. exact H3.
  + rewrite F4. exact H4.
  + exact Hra.
  + intros i Hi. eapply val_mem_kept; [|exact (HSV i Hi)]. intros k Hk.
    apply KV; unfold DRAIN_FRAME, DR_SAVE_OFF, ESTACK in *; lia.
  + intros regs' m' md' HRP Harm HJ'.
    set (P := fun x => as_errno B <= x < as_errno B + 4 \/ dsp0 cx - DRAIN_FRAME - ESTACK <= x < dsp0 cx - DRAIN_FRAME).
    assert (KVP : forall x, 0 <= x < 2 ^ 64 -> ~ P x -> aview SEGS (w_H W1) m' x = aview SEGS (w_H W1) m1 x).
    { intros x Hx HP. rewrite (aview_eq_of SEGS _ mF m' x (Harm _)).
      apply KV; [exact Hx | intros H; apply HP; left; exact H | intros H; apply HP; right; exact H]. }
    assert (PR' : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) m' x).
    { intros x Hp. destruct (PR x Hp) as [Hh [b Hb]]. split; [exact Hh|]. exists b.
      specialize (Harm (Z_to_bv 64 x)). unfold arm, mrestrict in Harm. rewrite Hh in Harm. rewrite Harm. exact Hb. }
    assert (VE' : val_mem SEGS (arm W1 m') (as_errno B) 4 11).
    { eapply val_mem_kept; [|exact VE]. intros k Hk. apply aview_eq_of. apply Harm. }
    assert (BK : forall x, 0 <= x < alloc_ceiling -> ~ (as_errno B <= x < as_errno B + 4) ->
      abyte_kept W1 m1 W1 m' x).
    { intros x Hx Hne. apply (dend_bk W1 m1 m' P x KVP PR'); [lia|].
      intros [H | H]; [exact (Hne H) | unfold DRAIN_FRAME, ESTACK in *; lia]. }
    apply (dend_post cx s1 D ly1 S1 W1 m' md' k1 regs' e1 e1 h1 out1 11 LB1 spent jb a tl HB HJ' HRP).
    * intros x Hi Hno He Hp. apply PR'. exact (HAPK x Hi Hno He Hp).
    * rewrite Hc0. change (0 =? 1) with false. cbv iota. symmetry. apply dset_eof_id.
    * apply (akept_garr8 W1 m1); [|exact HEB]. intros x Hx. unfold bzs in Hx.
      rewrite length_map in Hx. apply BK; [| apply TBE]; unfold AENT, ATABLE in *;
      unfold entry_bytes, re_nheld in Hx; rewrite !length_app, !Mem.length_le4, !Mem.length_le8, Hp1, Hp2 in Hx; lia.
    * intros i Hi. unfold arm. apply (writable_kept (w_H W1) m1 m'); [apply PR' | exact (HEW i Hi)].
    * apply (aentry_ok_kept B ly1 S1 W1 m1 ly1 S1 W1 m' e1 HEOK);
        [|intros b Hb; apply INL; unfold L; apply in_or_app; left; exact Hb].
      intros r Hr x Hx. destruct (FE r Hr x Hx) as [[Hl _] Hne]. exact (BK x Hl Hne).
    * apply (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m' (dHA RG cx) h1 HSRC);
        [|intros b Hb; apply INL; unfold L; apply in_or_app; right; apply in_or_app; left; exact Hb].
      intros r Hr x Hx. destruct (FS r Hr x Hx) as [[Hl _] Hne]. exact (BK x Hl Hne).
    * intros x Hx Hn. pose proof (HGK x Hx Hn) as K1. destruct (FG x Hx) as [[Hl _] Hne].
      pose proof (BK x Hl Hne) as K2. split; [rewrite (proj1 K2); exact (proj1 K1)|].
      intros Hw. apply (proj2 K2). apply (proj2 K1). exact Hw.
    * apply (dend_aout_ev ly1 S1 W1 m1 m' _ _ _ _ _ _ 11 HOUT).
      -- intros r Hr x Hx Hne. destruct (FO r Hr x Hx) as [[Hl _] _]. exact (BK x Hl Hne).
      -- exact FB.
      -- exact VE'.
      -- intros i Hi. unfold arm. apply (writable_kept (w_H W1) m1 m'); [apply PR' | exact (HAWE i Hi)].
      -- lia.
    * exact HDEAD.
    * exact HPERM.
    * exact HDL.
    * exact HDS.
    * exact HDH.
    * exact HJ1.
    * exact HPE.
    * exact HEIN.
    * exact HROOM.
    * exact HLAT.
    * exact HBUD.
- apply (dend_closed cx ly1 S1 W1 m1 md1 k1 regs1 _ HB HJ HGin HEW Hsp R21 R23 R19 F40 F240
    ltac:(rewrite <- Hc1; exact Vcl)).
  intros regsF mF mdF F2 F3 F4 HJF KV PR VE.
  apply (HEPI cx ly1 S1 W1 mF mdF k1 regsF (dPOST B MT RG cx) HJF).
  + unfold spZ in *. rewrite F2. exact Hsp.
  + rewrite F3. exact H3.
  + rewrite F4. exact H4.
  + exact Hra.
  + intros i Hi. eapply val_mem_kept; [|exact (HSV i Hi)]. intros k Hk.
    apply KV; unfold DRAIN_FRAME, DR_SAVE_OFF, AENT, ATABLE in *; lia.
  + intros regs' m' md' HRP Harm HJ'.
    set (P := fun x => dxSA cx + 4 <= x < dxSA cx + 8).
    assert (KVP : forall x, 0 <= x < 2 ^ 64 -> ~ P x -> aview SEGS (w_H W1) m' x = aview SEGS (w_H W1) m1 x).
    { intros x Hx HP. rewrite (aview_eq_of SEGS _ mF m' x (Harm _)). exact (KV x Hx HP). }
    assert (PR' : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) m' x).
    { intros x Hp. destruct (PR x Hp) as [Hh [b Hb]]. split; [exact Hh|]. exists b.
      specialize (Harm (Z_to_bv 64 x)). unfold arm, mrestrict in Harm. rewrite Hh in Harm. rewrite Harm. exact Hb. }
    assert (VE' : val_mem SEGS (arm W1 m') (dxSA cx + 4) 4 1).
    { eapply val_mem_kept; [|exact VE]. intros k Hk. apply aview_eq_of. apply Harm. }
    assert (BK : forall x, dlow cx x -> abyte_kept W1 m1 W1 m' x).
    { intros x [Hx Hnt]. apply (dend_bk W1 m1 m' P x KVP PR'); [lia|].
      intros H. apply Hnt. unfold P, AENT, ATABLE in *. lia. }
    apply (dend_post cx s1 D ly1 S1 W1 m' md' k1 regs' e1 (dset_eof e1 1) h1 out1 ev1 LB1 spent jb a tl HB HJ' HRP).
    * intros x Hi Hno He Hp. apply PR'. exact (HAPK x Hi Hno He Hp).
    * rewrite Hc1. reflexivity.
    * apply (dend_garr8_eof W1 m1 m' (dxSA cx) e1 HEB); [| exact Hp1 | exact Hp2 | exact VE'].
      intros x Hx Hn. apply KVP; [unfold AENT, ATABLE in *; lia | exact Hn].
    * intros i Hi. unfold arm. apply (writable_kept (w_H W1) m1 m'); [apply PR' | exact (HEW i Hi)].
    * apply dend_aentry_eof; [|right; reflexivity].
      apply (aentry_ok_kept B ly1 S1 W1 m1 ly1 S1 W1 m' e1 HEOK);
        [|intros b Hb; apply INL; unfold L; apply in_or_app; left; exact Hb].
      intros r Hr x Hx. destruct (FE r Hr x Hx) as [Hl _]. exact (BK x Hl).
    * apply (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m' (dHA RG cx) h1 HSRC);
        [|intros b Hb; apply INL; unfold L; apply in_or_app; right; apply in_or_app; left; exact Hb].
      intros r Hr x Hx. destruct (FS r Hr x Hx) as [Hl _]. exact (BK x Hl).
    * intros x Hx Hn. pose proof (HGK x Hx Hn) as K1. destruct (FG x Hx) as [Hl _].
      pose proof (BK x Hl) as K2. split; [rewrite (proj1 K2); exact (proj1 K1)|].
      intros Hw. apply (proj2 K2). apply (proj2 K1). exact Hw.
    * apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m' _ _ _ _ _ _ HOUT);
        [|intros b Hb; apply INL; unfold L; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb].
      intros r Hr x Hx. destruct (FO r Hr x Hx) as [Hl _]. exact (BK x Hl).
    * exact HDEAD.
    * exact HPERM.
    * exact HDL.
    * exact HDS.
    * exact HDH.
    * exact HJ1.
    * exact HPE.
    * exact HEIN.
    * exact HROOM.
    * exact HLAT.
    * exact HBUD.
Qed.

End c.

(* ---- THE GENERIC WALK (an internal work row, the image-B twin of image A's slice B): the epilogue (dr_epi_stmt_x) and the end
   (dr_end_stmt_x) over any allocator relation ARx with its laws, at the room texts (the room record RP, the entry's
   budget kr).  The Section is W_drain_cx_x.v's Section c - its variables B PST ARx MT RP MMAX RG in that order, each
   hypothesis that file's text - with the three allocator rules in their caller-context forms (W_journal_x.v Section
   hc, one context table per allocator entry; these segments call no allocator, so no call-site fact HCTX_* is
   stated), and after LAWS the generic-relation fact the walk reads:
     HP0 (no hidden head in any ARx state, a Theorem Labs lane's ruling: the table's shadow facts are W_journal_x.v's
     range_addressable_of_block_hp0_x).  An image byte lies in no live block (YCbqG.v blk_img_x, the laws'
     client-image field): the image's cells (g_s, G_DR, HGO's three) are apart from the table without a numeric image
     band (in_img from HG / HGO).  The room: dr_post_x's rp_RM RP S' kr is the cut's room (dbud_x) with the requests'
     count dropped (RMM).
   The AR walk above (Section c) is unchanged.  Its Definitions are cited; its lemmas are restated here with an _x
   suffix (each over ARx where it reads the relation), so no lemma's Section generalization is relied on. ---- *)
Section cx.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
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
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_F.
Hypothesis ASTRNDUP : astrndup_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_S (SIGMA WS_strndup).
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
Let RUN := paj_run_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).


(* ---- EPI: the epilogue 0x83fc8.  The entry state seats the 13 saves (atoms 32 .. 44 = the caller's s11 .. ra, the
   order of W_drain_cx.v DR_SAVED) at 248(sp) .. 344(sp) (DR_SAVE_OFF); atom 45 is the shadow base, unused. ---- *)
Lemma nth_depi_extra_x : forall regsE i, (i < 13)%nat ->
  nth i (depi_extra regsE) (Z_to_bv 64 0) = getr regsE (nth i DR_SAVED 0%bv).
Proof.
intros regsE i Hi. unfold depi_extra. rewrite app_nth1 by (rewrite length_map; cbn; lia).
rewrite (nth_indep _ _ (getr regsE 0%bv)) by (rewrite length_map; cbn; lia). rewrite List.map_nth. reflexivity.
Qed.
Lemma dr_epi_entry_x : forall W regsX memX regsE,
alloc_ceiling <= spZ regsX -> spZ regsX + DRAIN_FRAME <= 2 ^ 47 -> 2 ^ 46 <= spZ regsX -> spZ regsX mod 16 = 0 ->
dr_saved (PI := PI) W memX (spZ regsX) regsE ->
st_ok_pi SEGS VAL (Eimg (Ereg regsX (depi_extra regsE))) dss_epi
(restrict (w_H W) (mkst regsX (Z_to_bv 64 (BASE + A_dr_epi)) memX (seg_rom SEGS))).
Proof.
intros W regsX memX regsE Hceil Htop Hlo Hal HSV.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regsX (depi_extra regsE))).
assert (E2 : ew E 2 = getr regsX 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsX _ 2 2%bv eq_refl)).
assert (E45 : ew E 45 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsX _ 13)).
assert (Usp : bv_unsigned (ew E 2) = spZ regsX) by (rewrite E2; reflexivity).
unfold dss_epi, A_dr_epi. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold depi_regions. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [unfold DRAIN_FRAME in *; lia|]. split; [unfold DRAIN_FRAME in *; lia|]. split; [intros o Ho; lia|].
  apply Forall_map. apply Forall_forall. intros i Hi. apply in_seq in Hi. cbn [Nat.add] in Hi.
  apply (chunk_ok_val SEGS E _ (spZ regsX) (248 + 8 * Z.of_nat i) 8 _ (bv_unsigned (getr regsE (nth i DR_SAVED 0%bv)))).
  + cbn [sv_denot]. subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    rewrite ew_Ereg_extra, nth_depi_extra_x by lia.
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + pose proof (bv_unsigned_in_range 64 (getr regsE (nth i DR_SAVED 0%bv))) as R. change (bv_modulus 64) with (2 ^ 64) in R. zside.
  + zside.
  + replace (spZ regsX + (248 + 8 * Z.of_nat i)) with (spZ regsX + DR_SAVE_OFF + 8 * Z.of_nat i)
      by (unfold DR_SAVE_OFF; lia).
    exact (HSV i ltac:(lia)).
- cbn [pairwise_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [depi_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E45, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold DRAIN_FRAME in Htop. revert Hceil Htop Hlo Hal. clear. unfold SB. intros. repeat match goal with |- _ /\ _ => split end; (exact I || lia).
Qed.


(* ---- END: DEND 0x83e94.  The entry state: the stack region holds frame slot 40 ((g_s + 8) / 8, read as
   (A_OBJ 19 + 8) >> 3) and slot 240 (the shadow base, atom 32 = SB); h->closed (cl) at HA + 8 is seated as a
   literal so the runner decides 0x83ea8.  s3 (atom 19) = SHADOW_OFF + 12 j is the shadow base of the first shadow
   check: s3 + slot 40 = SB + 12 j + (g_s + 8) / 8, the shent of g_s's slot j (dSH1, at A_OBJ 19's offsets
   0 .. 96 with base dBx1).  The checks against slot 240 (errno, s->eof) use dBx2 = atom 32. ---- *)
Lemma dend_den_x : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. rewrite <- H. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma dend_U_srl_x : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
U E (SAlu ALU_SRL (SOff n c) (SLit 3)) = (v + c) / 8.
Proof.
intros E n v c Hn Hv Hc. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E n v c Hn Hv Hc), U_SLit, (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
apply zcanon_id. unfold M64. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Lemma dend_d8_x : forall x, 0 <= x < 2 ^ 64 -> 0 <= x / 8 < 2 ^ 61.
Proof. intros x Hx. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.

Lemma dend_entry_x : forall (W : world SEGS) regs m (j : nat) cl SA,
(j < 4)%nat ->
getr regs 21 = w64 SA -> getr regs 23 = w64 (rg_s RG + ASRC * Z.of_nat j) ->
getr regs 19 = w64 (SHADOW_OFF + 12 * Z.of_nat j) ->
4096 <= SA <= 0x7fffff800000 ->
alloc_ceiling <= spZ regs -> spZ regs + DRAIN_FRAME <= 2 ^ 47 -> 2 ^ 46 <= spZ regs -> spZ regs mod 16 = 0 ->
val_mem SEGS (arm W m) (spZ regs + 40) 8 ((rg_s RG + 8) / 8) ->
val_mem SEGS (arm W m) (spZ regs + 240) 8 SHADOW_OFF ->
val_mem SEGS (arm W m) (rg_s RG + ASRC * Z.of_nat j + 8) 4 cl -> 0 <= cl <= 1 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs dend_extra)) (dss_end j cl)
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_end)) m (seg_rom SEGS))).
Proof.
intros W regs m j cl SA Hj R21 R23 R19 HSA Hceil Htop Hlo Hal V40 V240 Hcl Rcl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof HGSB as (G1 & G2 & G3). unfold IMG_TOP in G2.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs dend_extra)).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ n r Hr)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E260 : ew E (A_OBJ 19) = Z_to_bv 64 (rg_s RG))
  by (rewrite <- HVS; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (U2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EREG 2%nat 2%bv) by (first [lia | reflexivity]); reflexivity).
assert (U19 : bv_unsigned (ew E 19) = SB + 12 * Z.of_nat j)
  by (rewrite (EREG 19%nat 19%bv) by (first [lia | reflexivity]); rewrite R19, unsigned_lit_small by (unfold SHADOW_OFF; lia); reflexivity).
assert (U21 : bv_unsigned (ew E 21) = SA)
  by (rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); rewrite R21; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = rg_s RG + ASRC * Z.of_nat j)
  by (rewrite (EREG 23%nat 23%bv) by (first [lia | reflexivity]); rewrite R23; apply unsigned_lit_small; unfold ASRC in *; lia).
assert (U32 : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (U260 : bv_unsigned (ew E (A_OBJ 19)) = rg_s RG)
  by (rewrite E260; apply unsigned_lit_small; unfold ASRC in *; lia).
pose proof (dend_d8_x (rg_s RG + 8) ltac:(unfold ASRC in *; lia)) as D8.
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold dend_regions, dend_stack, dend_hreg.
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U2. split; [unfold DRAIN_FRAME in *; lia|]. split; [unfold DRAIN_FRAME in *; lia|].
    split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * apply (chunk_ok_val SEGS E _ _ 40 8 _ ((rg_s RG + 8) / 8));
        [ apply dend_den_x; apply (dend_U_srl_x E (A_OBJ 19) (rg_s RG) 8 E260); unfold ASRC in *; lia
        | zside | zside | exact V40 ].
    * apply (chunk_ok_val SEGS E _ _ 240 8 _ SHADOW_OFF);
        [ apply dend_den_x; apply (U_atom E 32 SB E32); unfold SB; lia
        | unfold SHADOW_OFF; zside | zside | exact V240 ].
  + rewrite U23. split; [unfold ASRC in *; lia|]. split; [unfold ASRC in *; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ _ 8 4 (SLit cl) cl); [reflexivity | cbn; lia | cbn; lia | exact Hcl].
- unfold dend_regions, dend_stack, dend_hreg. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U23.
  split; [split; [|exact I] | split; [exact I | exact I]]. right. unfold ASRC in *. lia.
- split; [|split; [exact I | exact I]].
  cbn [dend_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U2, U19, U21, U32, U260.
  rewrite ?Z.pow_0_r, ?Z.mod_1_r. change (2 ^ 4) with 16. change (2 ^ 3) with 8.
  unfold SB, IMG_TOP, ASRC, DRAIN_FRAME in *.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma dend_shent1_x : forall ly S Hp (W : world SEGS) mem md E (j : nat),
ARx ly S Hp W mem md -> (j < 4)%nat ->
U E dBx1 = SHADOW_OFF + 12 * Z.of_nat j -> U E (SOff (A_OBJ 19) 0) = rg_s RG ->
shent_ok SEGS dBx1 E (mrestrict (w_H W) mem) (mkSHE (A_OBJ 19) 0 96).
Proof.
intros ly S Hp W mem md E j HAR Hj HB Hm.
pose proof HGSB as (G1 & G2 & G3). unfold IMG_TOP in G2.
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm. rewrite <- (aview_rd_of SEGS).
pose proof (azs_range_addressable_x B ARx LAWS ly S Hp W mem md (rg_s RG) (4 * ASRC) HAR HGSZ) as HRA.
split.
- intros x Hx. destruct (HRA (x + ASRC * Z.of_nat j) ltac:(unfold ASRC in *; lia)) as (s & Hs & Hok).
  exists s. split.
  + unfold shadow_of_addr in *. replace (SHADOW_OFF + 12 * Z.of_nat j + x / 8)
      with (SHADOW_OFF + (x + ASRC * Z.of_nat j) / 8); [exact Hs|].
    unfold ASRC. replace (x + 96 * Z.of_nat j) with (x + (12 * Z.of_nat j) * 8) by lia.
    rewrite Z.div_add by lia. lia.
  + unfold saddr_ok in *. unfold ASRC in Hok.
    replace ((x + 96 * Z.of_nat j) mod 8) with (x mod 8) in Hok; [exact Hok|].
    replace (x + 96 * Z.of_nat j) with (x + (12 * Z.of_nat j) * 8) by lia. rewrite Z.mod_add by lia. reflexivity.
- intros a Ha. unfold SHADOW_OFF, ASRC in *. lia.
Qed.

(* the frame facts the entry state needs, from the journal's stack window *)

(* The closed arm: 0x83e94 .. 0x83fa4 to the eof store 0x83fa8 (A_dr_eof), then s->eof = 1 to EPI 0x83fc8. *)

(* The EAGAIN arm: 0x83e94 .. 0x83eac to the __errno_location call, then 0x83eb0 .. 0x83ed4, TOP's errno tail
   0x83574 .. 0x835a4 (errno = 11, read back twice) and 0x83f94 .. 0x83fa4 to EPI 0x83fc8.  After the call the
   stack region (slot 240) is kept and the errno atom (CLOB's a0, atom 44) gets R1's int* fact, al2 2 (HERRAL),
   which decides the traps 0x83eb0 / 0x83eb8 / 0x8357c; errno's 4 bytes are a G_DR cell. *)

Lemma dset_eof_id_x : forall e, dset_eof e (re_eof e) = e.
Proof. intros []. reflexivity. Qed.

Lemma dend_aentry_eof_x : forall ly S (W : world SEGS) m e v,
aentry_ok B ly S W m e -> v = 0 \/ v = 1 -> aentry_ok B ly S W m (dset_eof e v).
Proof. intros ly S W m e v (_ & H) Hv. split; [exact Hv | exact H]. Qed.

Lemma dend_garr8_one4_x : forall m a, val_mem SEGS m a 4 1 -> garr8 SEGS m a [1; 0; 0; 0].
Proof.
intros m a H j Hj. cbn [length] in Hj.
split; [|destruct j as [|[|[|[|j]]]]; cbn; lia].
intros k Hk. destruct k as [|k]; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
rewrite (H j Hj). f_equal. destruct j as [|[|[|[|j]]]]; try (vm_compute; reflexivity). lia.
Qed.

Lemma dend_garr8_eof_x : forall (W : world SEGS) m m' SA e,
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) ->
(forall x, SA <= x < SA + AENT -> ~ (SA + 4 <= x < SA + 8) -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
val_mem SEGS (arm W m') (SA + 4) 4 1 ->
garr8 SEGS (arm W m') SA (bzs (entry_bytes (dset_eof e 1))).
Proof.
intros W m m' SA e HE0 KV Hp1 Hp2 VM.
unfold entry_bytes, dset_eof, re_nheld in HE0 |- *.
cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_kh re_pad2 re_keys re_U re_junk] in HE0 |- *.
unfold bzs in HE0 |- *. rewrite !map_app in HE0 |- *.
apply (garr8_app SEGS) in HE0 as [HA HE0]. apply (garr8_app SEGS) in HE0 as [_ HC].
apply (garr8_app SEGS). split.
- eapply (garr8_frame SEGS); [exact HA|]. intros x Hx. unfold arm. apply (mbyte_of_aview SEGS).
  rewrite length_map, Mem.length_le4 in Hx. apply KV; unfold AENT; lia.
- apply (garr8_app SEGS). rewrite !length_map, !Mem.length_le4 in HC |- *. split.
  + lazymatch goal with |- garr8 _ _ _ (map bz ?l) => replace (map bz l) with [1; 0; 0; 0] by (vm_compute; reflexivity) end.
    apply dend_garr8_one4_x. replace (SA + Z.of_nat 4) with (SA + 4) by lia. exact VM.
  + eapply (garr8_frame SEGS); [exact HC|]. intros x Hx. unfold arm. apply (mbyte_of_aview SEGS).
    rewrite !length_app, !length_map, !Mem.length_le4, !Mem.length_le8, Hp1, Hp2 in Hx.
    apply KV; unfold AENT; lia.
Qed.

Lemma dend_bk_x : forall (W : world SEGS) m m' (P : Z -> Prop) a,
(forall x, 0 <= x < 2 ^ 64 -> ~ P x -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
(forall x, apresent (w_H W) m x -> apresent (w_H W) m' x) ->
0 <= a < 2 ^ 64 -> ~ P a -> abyte_kept W m W m' a.
Proof.
intros W m m' P a KV PR Ha HP. split; [exact (KV a Ha HP)|].
unfold arm. apply writable_kept. apply PR.
Qed.

Lemma dend_zall_x : forall a l j d, zall_disjoint a l -> (j < length l)%nat -> zdisj a (nth j l d).
Proof.
intros a l. induction l as [|b l IH]; intros j d H Hj; cbn in Hj; [lia|].
destruct H as [H1 H2]. destruct j as [|j]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.

Lemma dend_zpw_x : forall l i j d, zpairwise_disjoint l -> (i < j)%nat -> (j < length l)%nat ->
zdisj (nth i l d) (nth j l d).
Proof.
intros l. induction l as [|a l IH]; intros i j d H Hij Hj; cbn in Hj; [lia|].
destruct H as [H1 H2]. destruct i as [|i].
- destruct j as [|j]; [lia|]. cbn [nth]. apply dend_zall_x; [exact H1 | lia].
- destruct j as [|j]; [lia|]. cbn [nth]. apply IH; [exact H2 | lia | lia].
Qed.

Lemma dend_errno_sep_x : forall a,
(rg_s RG <= a < rg_s RG + 4 * ASRC \/ rg_client RG <= a < rg_client RG + 4 \/
 rg_client_broken RG <= a < rg_client_broken RG + 1 \/ rg_send_eintr RG <= a < rg_send_eintr RG + 1 \/
 rg_send_dead RG <= a < rg_send_dead RG + 1 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
 rg_nout RG <= a < rg_nout RG + 8 \/ rg_capout RG <= a < rg_capout RG + 8 \/ rg_out RG <= a < rg_out RG + 8) ->
~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha He.
pose proof (dend_zpw_x _ 2 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D2.
pose proof (dend_zpw_x _ 3 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D3.
pose proof (dend_zpw_x _ 4 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D4.
pose proof (dend_zpw_x _ 5 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D5.
pose proof (dend_zpw_x _ 6 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D6.
pose proof (dend_zpw_x _ 7 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D7.
pose proof (dend_zpw_x _ 8 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D8.
pose proof (dend_zpw_x _ 9 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D9.
pose proof (dend_zpw_x _ 10 11 (0, 0) HRGD ltac:(lia) ltac:(cbn; lia)) as D10.
cbn [nth] in D2, D3, D4, D5, D6, D7, D8, D9, D10. unfold zdisj in *. cbn [fst snd] in *. lia.
Qed.

(* an image byte is no byte of the table block (YCbqG.v blk_img_x, the laws' client-image field) *)
Lemma dend_low_img_x : forall cx ly S Hp (W : world SEGS) mem md a,
ARx ly S Hp W mem md -> In (dxG cx, ATABLE) (ablocks B ly S) -> in_img SEGS a -> dlow cx a.
Proof.
intros cx ly S Hp W mem md a HAR Hin Ha.
pose proof (pa_img_range a Ha) as Hr.
pose proof asan_consts as (C1 & _).
assert (NT : ~ (dxG cx <= a < dxG cx + req_size ATABLE))
  by (intros Ht; exact (blk_img_x SEGS B ARx LAWS ly S Hp W mem md _ _ a HAR Hin Ht Ha)).
assert (RQT : req_size ATABLE = 896) by reflexivity. rewrite RQT in NT.
unfold dlow, ATABLE in *. lia.
Qed.

Lemma dend_low_blk_x : forall cx ly S Hp (W : world SEGS) mem md L p n a,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
In (p, n) L -> p <= a < p + req_size n ->
dlow cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S Hp W mem md L p n a HAR HP HL Ha.
assert (Hin : In (p, n) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); right; exact HL).
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n HAR Hin) as (_ & H4 & Hc & _).
destruct (in_split _ _ HL) as (l1 & l2 & ->).
assert (HP2 : Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: (p, n) :: l1 ++ l2))
  by (eapply Permutation_trans; [exact HP | apply perm_skip; apply Permutation_sym, Permutation_middle]).
pose proof (sep_blocks_perm_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ HAR HP2) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
assert (RQT : req_size ATABLE = 896) by reflexivity. rewrite RQT in Hd.
split; [unfold dlow, ATABLE; lia|].
intros He. apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md p n a HAR Hin ltac:(lia)).
apply (proj1 (HG a ltac:(unfold G_DR, G_SL, inG; cbn [In];
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]))).
Qed.

Lemma dend_gs_ok_x : forall cx ly S Hp (W : world SEGS) mem md a,
ARx ly S Hp W mem md -> In (dxG cx, ATABLE) (ablocks B ly S) -> rg_s RG <= a < rg_s RG + 4 * ASRC ->
dlow cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S Hp W mem md a HAR Hin Ha. pose proof HGSB as (G1 & G2 & _). unfold IMG_TOP in G2.
split; [apply (dend_low_img_x cx ly S Hp W mem md a HAR Hin); refine (proj1 (HG a _)); unfold inG, G_DR;
  apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; exact Ha|].
apply dend_errno_sep_x. left. exact Ha.
Qed.

Lemma dend_key_ptrs_len_x : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
intros ks. unfold key_ptrs. induction ks as [|k ks IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. cbn [length]. rewrite Mem.length_le8. lia.
Qed.

Lemma dend_recs_len_x : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !Mem.length_le8. lia.
Qed.

Lemma dend_fp_entry_x : forall cx ly S Hp (W : world SEGS) mem md e L,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (aentry_blks e) -> In b L) -> aentry_ok B ly S W mem e ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r ->
dlow cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S Hp W mem md e L HAR HP HB HE r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & _ & _ & Hbuf & _ & Hhp & _ & _ & Hks).
assert (BLK : forall p n, In (p, n) (aentry_blks e) -> 0 <= n -> p <= a < p + n ->
  dlow cx a /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros p n Hin Hn Hpa. pose proof (req_size_pos n Hn) as (_ & Hrq).
  exact (dend_low_blk_x cx ly S Hp W mem md L p n a HAR HP (HB _ Hin) ltac:(lia)). }
unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
  rewrite length_map, length_app in Ha.
  destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  apply (BLK (re_buf e) (re_cap e)); [| lia | lia].
  unfold aentry_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
- cbn [In] in Hr. destruct Hr as [<- | Hr].
  + unfold gfp in Ha. cbn [fst snd] in Ha.
    destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
    * rewrite Hke in Ha. unfold bzs, key_ptrs in Ha. cbn [map concat length] in Ha. lia.
    * unfold bzs in Ha. rewrite length_map, dend_key_ptrs_len_x in Ha. unfold re_nheld in Hk1.
      apply (BLK (re_hp e) (re_kh e)); [| lia | lia].
      unfold aentry_blks. apply in_or_app. right. apply in_or_app. left.
      rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity.
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (BLK (key_addr k) (Z.of_nat (length (key_text k)) + 1)); [| lia | lia].
    unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
    apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk.
Qed.

Lemma dend_fp_list_x : forall cx ly S Hp (W : world SEGS) mem md L LA l lines,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (alist_blks l) -> In b L) -> In (dxG cx, ATABLE) (ablocks B ly S) ->
alist_at B ly S W mem LA l lines -> rg_s RG <= LA -> LA + 16 <= rg_s RG + 4 * ASRC ->
forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r ->
dlow cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S Hp W mem md L LA l lines HAR HP HB HGin HL Hlo Hhi r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
assert (BLK : forall p n, In (p, n) (alist_blks l) -> 0 <= n -> p <= a < p + n ->
  dlow cx a /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros p n Hin Hn0 Hpa. pose proof (req_size_pos n Hn0) as (_ & Hrq).
  exact (dend_low_blk_x cx ly S Hp W mem md L p n a HAR HP (HB _ Hin) ltac:(lia)). }
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. apply (dend_gs_ok_x cx ly S Hp W mem md a HAR HGin). lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app, dend_recs_len_x in Ha.
    destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    apply (BLK (hl_v l) (AREC * hl_cap l)); [| unfold AREC; lia | unfold hl_n, AREC in *; lia].
    unfold alist_blks. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hc0). left. reflexivity.
  + apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    apply (BLK (fst q) (Z.of_nat (length (snd q)) + 1)); [| lia | lia].
    unfold alist_blks. apply in_or_app. right.
    apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))). exact Hq.
Qed.

Lemma dend_fp_src_x : forall cx ly S Hp (W : world SEGS) mem md L h,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (asrc_blks h) -> In b L) -> In (dxG cx, ATABLE) (ablocks B ly S) -> (dxj cx < 4)%nat ->
asrc_at B ly S W mem (dHA RG cx) h ->
forall r, In r (asrc_fp (dHA RG cx) h) -> forall a, fst r <= a < snd r ->
dlow cx a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros cx ly S Hp W mem md L h HAR HP HB HGin Hj HS r Hr a Ha.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
assert (HAr : rg_s RG <= dHA RG cx /\ dHA RG cx + ASRC <= rg_s RG + 4 * ASRC) by (unfold dHA, ASRC; lia).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- cbn [fst snd] in Ha. apply (dend_gs_ok_x cx ly S Hp W mem md a HAR HGin). lia.
- unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map in Ha.
  pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrq).
  apply (dend_low_blk_x cx ly S Hp W mem md L (hs_partial h) APARTIAL a HAR HP); [apply HB; left; reflexivity | lia].
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + exact (dend_fp_list_x cx ly S Hp W mem md L (dHA RG cx + 16) (hs_pending h) false HAR HP
      (fun b Hb => HB b (or_intror (in_or_app _ _ _ (or_introl Hb)))) HGin Hpend
      ltac:(unfold ASRC in *; lia) ltac:(unfold ASRC in *; lia) r Hr a Ha).
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * exact (dend_fp_list_x cx ly S Hp W mem md L (dHA RG cx + 64) (hs_expected h) true HAR HP
        (fun b Hb => HB b (or_intror (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hb)))))) HGin Hexp
        ltac:(unfold ASRC in *; lia) ltac:(unfold ASRC in *; lia) r Hr a Ha).
    * exact (dend_fp_list_x cx ly S Hp W mem md L (dHA RG cx + 80) (hs_held h) true HAR HP
        (fun b Hb => HB b (or_intror (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror Hb)))))) HGin Hheld
        ltac:(unfold ASRC in *; lia) ltac:(unfold ASRC in *; lia) r Hr a Ha).
Qed.

Lemma dend_fp_out_x : forall cx ly S Hp (W : world SEGS) mem md c O mx no cap out L,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: L) ->
(forall b, In b (aout_blks cap out) -> In b L) ->
aout_at B RG ly S W mem c O mx no cap out ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r ->
dlow cx a /\ (r <> (as_errno B, as_errno B + 4) -> ~ (as_errno B <= a < as_errno B + 4)).
Proof.
intros cx ly S Hp W mem md c O mx no cap out L HAR HP HB HOUT r Hr a Ha.
assert (GT : In (dxG cx, ATABLE) (ablocks B ly S))
  by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
assert (IMG : forall x, in_img SEGS x -> dlow cx x)
  by (intros x Hx; exact (dend_low_img_x cx ly S Hp W mem md x HAR GT Hx)).
assert (GDR : forall x, inG (G_DR B RG) x -> in_img SEGS x) by (intros x Hx; exact (proj1 (HG x Hx))).
assert (GO : forall x, inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] x -> in_img SEGS x)
  by (intros x Hx; exact (proj1 (HGO x Hx))).
pose proof (pa_obj_img 9 ltac:(lia)) as P9. rewrite HV9 in P9.
pose proof HSD as P12. unfold IMG_TOP in P12.
pose proof HSM as (Hs1 & Hs2). unfold IMG_TOP in Hs2.
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
- split; [apply IMG, GO; unfold inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dend_errno_sep_x; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dend_errno_sep_x; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dend_errno_sep_x; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dend_errno_sep_x; tauto].
- split; [apply IMG, GO; unfold inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dend_errno_sep_x; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dend_errno_sep_x; tauto].
- split; [apply IMG, GO; unfold inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dend_errno_sep_x; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros _; apply dend_errno_sep_x; tauto].
- split; [apply IMG, GDR; unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
  | intros Hne; exfalso; apply Hne; reflexivity].
- destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
  pose proof (req_size_pos cap ltac:(lia)) as (_ & Hrq).
  destruct (dend_low_blk_x cx ly S Hp W mem md L out cap a HAR HP) as [D1 D2];
    [apply HB; unfold aout_blks; rewrite Hc0; left; reflexivity | lia |].
  split; [exact D1 | intros _; exact D2].
Qed.

Lemma dend_aout_ev_x : forall ly S (W : world SEGS) m m' c O mx no cap out ev,
aout_at B RG ly S W m c O mx no cap out ->
(forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r ->
   ~ (as_errno B <= a < as_errno B + 4) -> abyte_kept W m W m' a) ->
(cap <> 0 -> forall a, out <= a < out + cap -> ~ (as_errno B <= a < as_errno B + 4)) ->
val_mem SEGS (arm W m') (as_errno B) 4 ev -> awr W m' (as_errno B) 4 -> 0 <= ev < 2 ^ 32 ->
aout_at B RG ly S W m' (CTL (ct_cl c) (ct_br c) (ct_dd c) (ct_ei c) ev) O mx no cap out.
Proof.
intros ly S W m m' c O mx no cap out ev
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
   H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) HK HOB VE WE Hev.
assert (KC : forall a n, In (a, a + n) (aout_fp B RG cap out) -> forall x, a <= x < a + n ->
  ~ (as_errno B <= x < as_errno B + 4) -> abyte_kept W m W m' x)
  by (intros a n Hin x Hx Hne; exact (HK (a, a + n) Hin x Hx Hne)).
unfold aout_at. cbn [ct_cl ct_br ct_dd ct_ei ct_ev].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_send_max RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H1]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_send_max RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H2]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_nout RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H3]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_nout RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H4]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_capout RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H5]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_capout RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H6]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_out RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H7]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_out RG) 8); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H8]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_client RG) 4); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H9]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_client RG) 4); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H10]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_client_broken RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H11]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_client_broken RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H12]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_send_dead RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H13]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_send_dead RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H14]|].
split; [apply (akept_vm W m); [intros x Hx; apply (KC (rg_send_eintr RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H15]|].
split; [apply (akept_awr W m); [intros x Hx; apply (KC (rg_send_eintr RG) 1); [unfold aout_fp; repeat (first [left; reflexivity | right]) | lia | apply dend_errno_sep_x; repeat (first [left; lia | right]); lia] | exact H16]|].
split; [exact VE|]. split; [exact WE|]. split; [exact Hev|].
do 6 (split; [assumption|]).
destruct H26 as [H26 | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; exact H26|right].
assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
split; [exact Hc|]. split; [exact Hno|]. split; [exact Hin|].
exists junk. split; [exact Hj|].
apply (akept_garr8 W m); [|exact Hg].
intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx.
apply (KC out cap); [unfold aout_fp; rewrite Ec; repeat (first [left; reflexivity | right]) | lia | apply (HOB ltac:(lia)); lia].
Qed.

Lemma dperm_mv_x : forall (x : Z * Z) l1 l2 l3 r, Permutation (x :: l1 ++ l2 ++ l3 ++ r) (l1 ++ l2 ++ l3 ++ x :: r).
Proof. intros. rewrite !app_assoc. apply Permutation_middle. Qed.


(* ---- END: DEND 0x83e94 -> h->closed ? (s->eof = 1 at 0x83fa8) : (errno = EAGAIN, 0x83eac / 0x83574), then dr_epi_x. ---- *)


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

Theorem dr_epi_xR : dr_epi_stmt_xR B PST ARx RG R.
Proof.
unfold dr_epi_stmt_xR. intros cx Hp ly1 S1 Hp1 W1 m1 md1 k1 regs1 Q HJ HspX H3 H4 HraE HSV HQ.
unfold cfg_at.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
rewrite !Z.add_0_r in Hal16, Hslo, Hshi, Hstk0.
assert (HDS : DRAIN_STK_x = 17008) by reflexivity.
pose proof (dr_epi_entry_x W1 regs1 m1 (dxregs cx) ltac:(unfold DRAIN_FRAME in *; lia) ltac:(unfold DRAIN_FRAME in *; lia)
  ltac:(unfold DRAIN_FRAME in *; lia) ltac:(unfold DRAIN_FRAME in *; rewrite HspX; rewrite Zminus_mod, Hal16; reflexivity)
  ltac:(rewrite HspX; exact HSV)) as HS.
remember (Eimg (Ereg regs1 (depi_extra (dxregs cx)))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EX : forall i, (i < 13)%nat -> ew E (32 + i) = getr (dxregs cx) (nth i DR_SAVED 0%bv)).
{ intros i Hi. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. exact (nth_depi_extra_x (dxregs cx) i Hi). }
assert (E2 : ew E 2 = getr regs1 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs1 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs1 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 4 4%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs1) by (rewrite E2; reflexivity).
assert (SHOK : sh_ok SEGS dBxX [] E (mrestrict (w_H W1) m1)) by constructor.
clear HE.
paj_run_tok_xR RUNG HS HJ SHOK Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19.
prreg HS (20%bv : bv 5) R20. prreg HS (21%bv : bv 5) R21. prreg HS (22%bv : bv 5) R22. prreg HS (23%bv : bv 5) R23.
prreg HS (24%bv : bv 5) R24. prreg HS (25%bv : bv 5) R25. prreg HS (26%bv : bv 5) R26. prreg HS (27%bv : bv 5) R27.
(* the return moves no world: the strict step, lifted by SRr_SRrG (WLE_R) *)
apply (SRr_SRrG SEGS R WLE_R).
eapply (RET W1 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
assert (RA : getr (ms_regs ms) 1 = getr (dxregs cx) 1) by (rewrite R1; exact (EX 12%nat ltac:(lia))).
rewrite RA, HraE. apply HQ.
- intros r Hr. unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
  + replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R2, Usp, HspX.
    replace (dsp0 cx - DRAIN_FRAME + 352) with (dsp0 cx) by (unfold DRAIN_FRAME; lia).
    unfold dsp0, spZ. apply Z_to_bv_bv_unsigned.
  + replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R3, E3. exact H3.
  + replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R4, E4. exact H4.
  + replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R8. exact (EX 11%nat ltac:(lia)).
  + replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R9. exact (EX 10%nat ltac:(lia)).
  + replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R18. exact (EX 9%nat ltac:(lia)).
  + replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R19. exact (EX 8%nat ltac:(lia)).
  + replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R20. exact (EX 7%nat ltac:(lia)).
  + replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R21. exact (EX 6%nat ltac:(lia)).
  + replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R22. exact (EX 5%nat ltac:(lia)).
  + replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R23. exact (EX 4%nat ltac:(lia)).
  + replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R24. exact (EX 3%nat ltac:(lia)).
  + replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R25. exact (EX 2%nat ltac:(lia)).
  + replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R26. exact (EX 1%nat ltac:(lia)).
  + replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R27. exact (EX 0%nat ltac:(lia)).
- unfold arm. intros x. apply HFr. intros (r & Hin & Hr). cbn [ss_mem dss_epi depi_regions In] in Hin.
  destruct Hin as [<- | []]. cbn [YP09.r_wlo YP09.r_whi] in Hr. lia.
- apply (ajournal_gx_materialize_xR SEGS B PST ARx LAWS pa_segs_low). exact HJ.
Qed.

Lemma dend_sp_xR : forall cx Hpe ly1 S1 Hp1 W1 m1 md1 k1 regs1,
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hpe (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m1 md1 k1 ->
spZ regs1 = dsp0 cx - DRAIN_FRAME ->
alloc_ceiling <= spZ regs1 /\ spZ regs1 + DRAIN_FRAME <= 2 ^ 47 /\ 2 ^ 46 <= spZ regs1 /\ spZ regs1 mod 16 = 0.
Proof.
intros cx Hpe ly1 S1 Hp1 W1 m1 md1 k1 regs1 HJ HspX.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
rewrite !Z.add_0_r in Hal16, Hslo, Hshi, Hstk0.
assert (HDS : DRAIN_STK_x = 17008) by reflexivity.
split; [unfold DRAIN_FRAME in *; lia|]. split; [unfold DRAIN_FRAME in *; lia|]. split; [unfold DRAIN_FRAME in *; lia|].
rewrite HspX, Zminus_mod, Hal16. reflexivity.
Qed.

Lemma dend_closed_xR : forall cx Hpe kr ly1 S1 Hp1 W1 m1 md1 k1 regs1 (Q : world SEGS -> config -> Prop),
DBASE_x B ARx MT RP MMAX RG cx Hpe kr ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hpe (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m1 md1 k1 ->
In (dxG cx, ATABLE) (ablocks B ly1 S1) ->
awr W1 m1 (dxSA cx) AENT ->
spZ regs1 = dsp0 cx - DRAIN_FRAME ->
getr regs1 21 = w64 (dxSA cx) -> getr regs1 23 = w64 (dHA RG cx) ->
getr regs1 19 = w64 (SHADOW_OFF + 12 * Z.of_nat (dxj cx)) ->
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 40) 8 ((rg_s RG + 8) / 8) ->
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 240) 8 SHADOW_OFF ->
val_mem SEGS (arm W1 m1) (dHA RG cx + 8) 4 1 ->
(forall regsF mF mdF,
  getr regsF 2 = getr regs1 2 -> getr regsF 3 = getr regs1 3 -> getr regsF 4 = getr regs1 4 ->
  @ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) Hpe (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 mF mdF k1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (dxSA cx + 4 <= a < dxSA cx + 8) ->
     aview SEGS (w_H W1) mF a = aview SEGS (w_H W1) m1 a) ->
  (forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) mF a) ->
  val_mem SEGS (arm W1 mF) (dxSA cx + 4) 4 1 ->
  SRrG SEGS R W1 (cfg_at SEGS (BASE + A_dr_epi) regsF mF mdF) Q) ->
SRrG SEGS R W1 (cfg_at SEGS (BASE + A_dr_end) regs1 m1 md1) Q.
Proof.
intros cx Hpe kr ly1 S1 Hp1 W1 m1 md1 k1 regs1 Q HB HJ HGin HAW Hsp R21 R23 R19 V40 V240 Hcl KC.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as (_ & _ & _ & HGle & HSAle & _ & _ & _ & _ & Hj & _).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE HAR HGin) as (_ & HG4 & HGc & Hap & _).
assert (RQT : req_size ATABLE = 896) by reflexivity.
rewrite RQT in HGc, Hap.
assert (HSA : 4096 <= dxSA cx <= 0x7fffff800000) by (unfold AENT, ATABLE in *; lia).
destruct (dend_sp_xR cx Hpe ly1 S1 Hp1 W1 m1 md1 k1 regs1 HJ Hsp) as (Sp1 & Sp2 & Sp3 & Sp4).
unfold dHA in R23, Hcl.
rewrite <- Hsp in V40, V240.
pose proof (dend_entry_x W1 regs1 m1 (dxj cx) 1 (dxSA cx) Hj R21 R23 R19 HSA Sp1 Sp2 Sp3 Sp4 V40 V240 Hcl ltac:(lia)) as HS.
remember (Eimg (Ereg regs1 dend_extra)) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E260 : ew E (A_OBJ 19) = Z_to_bv 64 (rg_s RG))
  by (rewrite <- HVS; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (UB1 : U E dBx1 = SHADOW_OFF + 12 * Z.of_nat (dxj cx))
  by (unfold dBx1; apply U_atom; [rewrite (EREG 19%nat 19%bv) by (first [lia | reflexivity]); exact R19 | unfold SHADOW_OFF; lia]).
assert (U260 : U E (SOff (A_OBJ 19) 0) = rg_s RG)
  by (apply U_atom; [exact E260 | pose proof HGSB; unfold ASRC, IMG_TOP in *; lia]).
assert (UB2 : U E dBx2 = SHADOW_OFF) by (unfold dBx2; apply U_atom; [exact E32 | unfold SHADOW_OFF; lia]).
assert (U21 : U E (SOff 21 0) = dxSA cx)
  by (apply U_atom; [rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); exact R21 | lia]).
assert (B21 : bv_unsigned (ew E 21) = dxSA cx)
  by (rewrite (EREG 21%nat 21%bv) by (first [lia | reflexivity]); rewrite R21; apply unsigned_lit_small; lia).
assert (B2 : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME)
  by (rewrite (EREG 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp).
assert (SHOK : sh_ok SEGS dBx1 dSH1 E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor]. exact (dend_shent1_x ly1 S1 Hp1 W1 m1 md1 E (dxj cx) HAR Hj UB1 U260). }
clear HE.
unfold cfg_at. change (w64 (BASE + A_dr_end)) with (Z_to_bv 64 (BASE + A_dr_end)).
set (j := dxj cx) in *. clearbody j.
destruct j as [|[|[|[|jj]]]]; [| | | | exfalso; lia].
all: paj_run_to_tok_xR RUNTOG HS HJ SHOK Bspan A_dr_eof; [apply awr_ok_x_of0; awr_ok_tac|].
all: rename HFr into FR1; rename HG0 into GR1; clear HF.
all: pose proof (st_ok_pi_submem _ _ _ [dend_stack] HS ltac:(submem_tac) eq_refl) as HS0; clear HS.
all: assert (RGOK : region_ok SEGS E (ms_mem (restrict (w_H W1) ms)) dr_eof_region);
  [ unfold region_ok, dr_eof_region;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
    rewrite B21; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
    intros o Ho; apply (writable_kept (w_H W1) m1 (ms_mem ms)); [apply (apresent_grows _ _ _ _ GR1)|];
    exact (HAW o ltac:(unfold AENT; lia)) |].
all: pose proof (st_ok_pi_add_region _ _ _ dr_eof_region HS0 eq_refl RGOK) as HS1; clear HS0.
all: match type of HS1 with ?d -> _ => assert (HD1 : d); [|specialize (HS1 HD1); clear HD1] end;
  [ cbn [ss_mem all_disjoint]; unfold extent_disjoint, dr_eof_region, dend_stack;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite B21, B2;
    split; [left; unfold DRAIN_FRAME, AENT, ATABLE in *; lia | exact I] |].
all: cbn [ss_pc ss_regs ss_resv ss_facts ss_mem] in HS1.
all: assert (SHOK2 : sh_ok SEGS dBx2 dSH2 E (mrestrict (w_H W1) (ms_mem ms)));
  [ unfold sh_ok, dSH2; apply Forall_cons; [|apply Forall_nil];
    eapply (shent_ok_of_range SEGS (w_H W1) (ms_mem ms) E dBx2 21%nat (dxSA cx + 4) 4 (dxSA cx) 4 8);
    [ eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 (ms_mem ms) _ (dxG cx) ATABLE);
      [ eapply ajournal_gx_AR_xR; exact HJ | exact HGin | lia
      | rewrite RQT; unfold AENT, ATABLE in *; lia ]
    | exact UB2 | exact U21 | lia | lia
    | intros x Hx; rewrite Z.min_l, Z.max_r in Hx by lia;
      unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, AENT, ATABLE in *; lia ] |].
all: paj_run_to_tok_xR RUNTOG HS1 HJ SHOK2 Bspan A_dr_epi;
  [ cbn [ss_mem]; apply awr_ok_x_cons;
    [ unfold dr_eof_region; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite B21;
      intros x Hx; left; split; [|lia];
      unfold awr_byte; right; left; split;
      [ exists (dxSA cx, dxSA cx + AENT); split; [left; reflexivity | cbn [fst snd]; unfold AENT; lia]
      | exists (dxG cx), ATABLE; split; [exact HGin | rewrite RQT; unfold AENT, ATABLE in *; lia] ]
    | apply awr_ok_x_cons; [ intros x Hx; unfold dend_stack in Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; lia
      | apply awr_ok_x_nil ] ] |].
all: rename HFr into FR2; rename HG0 into GR2; clear HF.
all: prreg HS1 (2%bv : bv 5) X2; prreg HS1 (3%bv : bv 5) X3; prreg HS1 (4%bv : bv 5) X4.
all: pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS1 eq_refl) as RF; cbn [ms_mem restrict] in RF.
all: pmkst HS1.
all: apply KC;
  [ rewrite X2; apply EREG; [lia | reflexivity]
  | rewrite X3; apply EREG; [lia | reflexivity]
  | rewrite X4; apply EREG; [lia | reflexivity]
  | exact HJ
  | intros a Ha Hn;
    rewrite (aview_kept_out _ _ (w_H W1) (ms_mem ms) (ms_mem ms0) FR2 a Ha);
    [ apply (aview_kept_out _ _ (w_H W1) m1 (ms_mem ms) FR1 a Ha);
      intros (r & Hin & Hr); cbn in Hin; destruct Hin as [<- | [<- | []]]; cbn in Hr; lia
    | intros (r & Hin & Hr); cbn in Hin; destruct Hin as [<- | [<- | []]];
      [ cbn [dr_eof_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite B21 in Hr; lia
      | cbn in Hr; lia ] ]
  | intros a Hp; apply (apresent_grows _ _ _ _ GR2); apply (apresent_grows _ _ _ _ GR1); exact Hp
  | unfold arm; eapply (field_of_region _ _ 21%nat (dxSA cx) _ 4 8 4 8 4 4%N (SLit 1) 1 RF);
    [ rewrite ?ew_ewset_other by lia; exact B21 | left; reflexivity | reflexivity | cbn; lia | cbn; lia ] ].
Qed.

Lemma dend_eagain_xR : forall cx Hpe kr ly1 S1 Hp1 W1 m1 md1 k1 regs1 (Q : world SEGS -> config -> Prop),
DBASE_x B ARx MT RP MMAX RG cx Hpe kr ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hpe (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m1 md1 k1 ->
In (dxG cx, ATABLE) (ablocks B ly1 S1) ->
awr W1 m1 (as_errno B) 4 ->
spZ regs1 = dsp0 cx - DRAIN_FRAME ->
getr regs1 3 = getr (dxregs cx) 3 -> getr regs1 4 = getr (dxregs cx) 4 ->
getr regs1 21 = w64 (dxSA cx) -> getr regs1 23 = w64 (dHA RG cx) ->
getr regs1 19 = w64 (SHADOW_OFF + 12 * Z.of_nat (dxj cx)) ->
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 40) 8 ((rg_s RG + 8) / 8) ->
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 240) 8 SHADOW_OFF ->
val_mem SEGS (arm W1 m1) (dHA RG cx + 8) 4 0 ->
(forall regsF mF mdF,
  getr regsF 2 = getr regs1 2 -> getr regsF 3 = getr regs1 3 -> getr regsF 4 = getr regs1 4 ->
  @ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) Hpe (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 mF mdF k1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= a < dsp0 cx - DRAIN_FRAME) ->
     aview SEGS (w_H W1) mF a = aview SEGS (w_H W1) m1 a) ->
  (forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) mF a) ->
  val_mem SEGS (arm W1 mF) (as_errno B) 4 11 ->
  SRrG SEGS R W1 (cfg_at SEGS (BASE + A_dr_epi) regsF mF mdF) Q) ->
SRrG SEGS R W1 (cfg_at SEGS (BASE + A_dr_end) regs1 m1 md1) Q.
Proof.
intros cx Hpe kr ly1 S1 Hp1 W1 m1 md1 k1 regs1 Q HB HJ HGin HAWE Hsp H3 H4 R21 R23 R19 V40 V240 Hcl KC.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as (HPRE0 & _ & _ & HGle & HSAle & _ & _ & _ & _ & Hj & _).
pose proof HPRE0 as (_ & _ & _ & Hgp & Htp & _).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE HAR HGin) as (_ & HG4 & HGc & Hap & _).
assert (RQT : req_size ATABLE = 896) by reflexivity.
rewrite RQT in HGc, Hap.
assert (HSA : 4096 <= dxSA cx <= 0x7fffff800000) by (unfold AENT, ATABLE in *; lia).
destruct (dend_sp_xR cx Hpe ly1 S1 Hp1 W1 m1 md1 k1 regs1 HJ Hsp) as (Sp1 & Sp2 & Sp3 & Sp4).
unfold dHA in R23, Hcl.
rewrite <- Hsp in V40, V240.
pose proof (dend_entry_x W1 regs1 m1 (dxj cx) 0 (dxSA cx) Hj R21 R23 R19 HSA Sp1 Sp2 Sp3 Sp4 V40 V240 Hcl ltac:(lia)) as HS.
remember (Eimg (Ereg regs1 dend_extra)) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ n r Hr)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E260 : ew E (A_OBJ 19) = Z_to_bv 64 (rg_s RG))
  by (rewrite <- HVS; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (UB1 : U E dBx1 = SHADOW_OFF + 12 * Z.of_nat (dxj cx))
  by (unfold dBx1; apply U_atom; [rewrite (EREG 19%nat 19%bv) by (first [lia | reflexivity]); exact R19 | unfold SHADOW_OFF; lia]).
assert (U260 : U E (SOff (A_OBJ 19) 0) = rg_s RG)
  by (apply U_atom; [exact E260 | pose proof HGSB; unfold ASRC, IMG_TOP in *; lia]).
assert (SHOK : sh_ok SEGS dBx1 dSH1 E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor]. exact (dend_shent1_x ly1 S1 Hp1 W1 m1 md1 E (dxj cx) HAR Hj UB1 U260). }
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME)
  by (rewrite (EREG 2%nat 2%bv) by (first [lia | reflexivity]); exact Hsp).
assert (HERRI : 0x10000 <= as_errno B /\ as_errno B + 4 <= 0x5fc000).
{ assert (HI4 : forall i, 0 <= i < 4 -> in_img SEGS (as_errno B + i)).
  { intros i Hi. apply (proj1 (HG (as_errno B + i) ltac:(unfold G_DR, G_SL, inG; cbn [In];
      repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]))). }
  pose proof (pa_img_range _ (HI4 0 ltac:(lia))) as P0. pose proof (pa_img_range _ (HI4 3 ltac:(lia))) as P3.
  lia. }
clear HE.
unfold cfg_at. change (w64 (BASE + A_dr_end)) with (Z_to_bv 64 (BASE + A_dr_end)).
set (j := dxj cx) in *. clearbody j.
destruct j as [|[|[|[|jj]]]]; [| | | | exfalso; lia].
all: paj_run_tok_xR RUNG HS HJ SHOK Bspan; [apply awr_ok_x_of0; awr_ok_tac|].
all: rename HFr into FR1; rename HG0 into GR1; clear HF.
all: pmkst HS.
all: prreg HS (1%bv : bv 5) Q1; prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4.
all: eapply (SRrG_bind SEGS R R_trans);
  [ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R (G_DR B RG) 0 ([] : list (Z * Z)) ESTACK (SIGMA WS_errno_location)
      (fun _ => False) (fun regs' (_ : word -> option byte) => getr regs' 10 = w64 (as_tp B - 164))
      W1 (ms_regs ms) (ms_mem ms) DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hpe (dxW cx) (dxmem cx) (dxmd cx)
      ([] : list (Z * Z)) ly1 S1 Hp1 _ k1 (- DRAIN_FRAME) _ HG eq_refl HJ);
    [ unfold spZ at 1; rewrite Q2, Usp; lia
    | reflexivity
    | unfold DRAIN_FRAME; lia
    | lia
    | unfold ESTACK, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK; lia
    | rewrite Q3, (EREG 3%nat 3%bv), H3 by (first [lia | reflexivity]); exact Hgp
    | rewrite Q4, (EREG 4%nat 4%bv), H4 by (first [lia | reflexivity]); exact Htp
    | exact Q1
    | apply ret_ok_codeptr_v; [lia | reflexivity]
    | intros _; right; intros []
    | intros a []
    | intros a []
    | intros HPRE _; exact (AERRNO ly1 S1 Hp1 W1 (ms_regs ms) (ms_mem ms) _ HPRE) ] |].
all: cbv beta; intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Herr & Hfr2 & Hpres2).
all: jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0%nat] HS2.
all: match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end;
  [ apply Forall_cons; [|apply Forall_nil];
    split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val ms_mem restrict]; rewrite Usp;
    intros a Ha;
    [ apply (mbyte_of_aview SEGS); apply (Hfr2 a ltac:(unfold DRAIN_FRAME in *; lia) (fun x => x));
      unfold DRAIN_FRAME in *; lia
    | exfalso; lia ] |].
all: clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS.
all: remember (havoc E 40 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
all: assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
all: assert (OLDa : forall m, (m < 40)%nat -> ew Ea m = ew E m)
  by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
all: clear HEa.
all: prreg HS (10%bv : bv 5) R10.
all: assert (F44 : ew Ea 44 = Z_to_bv 64 (as_errno B)) by (rewrite <- R10, Herr, HERRNO; reflexivity).
all: assert (B44 : bv_unsigned (ew Ea 44) = as_errno B) by (rewrite F44; apply unsigned_lit_small; unfold IMG_TOP in *; lia).
all: apply (st_ok_pi_add_fact _ _ _ 44%nat (mkAF 0x10000 IMG_TOP 2)) in HS;
  [| unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite B44; change (2 ^ 2) with 4; rewrite HERRAL;
     unfold IMG_TOP in *; repeat split; lia ].
all: apply (st_ok_pi_add_region _ _ _ (YP09.mkRegion (Some 44%nat) 0 4 0 4 [])) in HS;
  [ | vm_compute; reflexivity
    | unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
      rewrite B44; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
      intros o Ho; apply (writable_kept (w_H W1) m1 mem2);
      [ intros Hp; apply Hpres2; apply (apresent_grows _ _ _ _ GR1); exact Hp | exact (HAWE o Ho) ]
    | cbn [ss_mem add_atom all_disjoint]; unfold extent_disjoint;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite B44, (OLDa 2%nat) by lia; rewrite Usp;
      split; [left; unfold IMG_TOP, DRAIN_FRAME in *; lia | exact I] ].
all: assert (UB : U Ea dBx2 = SHADOW_OFF)
  by (unfold dBx2; apply U_atom; [rewrite (OLDa 32%nat) by lia; exact E32 | unfold SHADOW_OFF; lia]).
all: assert (UE44 : U Ea (SOff 44 0) = as_errno B) by (apply U_atom; [exact F44 | unfold IMG_TOP in *; lia]).
all: assert (SHOK3 : sh_ok SEGS dBx2 [mkSHE 44 0 4] Ea (mrestrict (w_H W1) mem2));
  [ unfold sh_ok; apply Forall_cons; [|apply Forall_nil];
    eapply (shent_ok_of_range SEGS (w_H W1) mem2 Ea dBx2 44%nat (as_errno B) 4 (as_errno B) 0 4);
    [ apply (azs_range_addressable_x B ARx LAWS ly1 S1 Hp1 W1 mem2 md2 (as_errno B) 4);
      [ eapply ajournal_gx_AR_xR; exact HJ2 | exact HERRZ ]
    | exact UB | exact UE44 | lia | lia
    | intros x Hx; rewrite Z.min_l, Z.max_r in Hx by lia; unfold SHADOW_OFF, IMG_TOP in *; lia ] |].
all: paj_run_to_tok_xR RUNTOG HS HJ2 SHOK3 Bspan A_dr_epi;
  [ cbn [ss_mem]; apply awr_ok_x_cons_g;
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite B44;
      intros a Ha; unfold G_DR, G_SL, inG; cbn [In];
      repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]
    | apply awr_ok_x_cons; [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia | apply awr_ok_x_nil ] ] |].
all: rename HFr into FR3; rename HG0 into GR3; clear HF.
all: prreg HS (2%bv : bv 5) X2; prreg HS (3%bv : bv 5) X3; prreg HS (4%bv : bv 5) X4.
all: pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RF; cbn [ms_mem restrict] in RF.
all: pmkst HS.
all: apply KC;
  [ rewrite X2, OLDa by lia; apply EREG; [lia | reflexivity]
  | rewrite X3, OLDa by lia; apply EREG; [lia | reflexivity]
  | rewrite X4, OLDa by lia; apply EREG; [lia | reflexivity]
  | exact HJ2
  | intros a Ha Hn Hsc;
    rewrite (aview_kept_out _ _ (w_H W1) mem2 (ms_mem ms0) FR3 a Ha);
    [ rewrite (Hfr2 a Ha (fun x => x)); [|intros Hs; apply Hsc; lia];
      apply (aview_kept_out _ _ (w_H W1) m1 (ms_mem ms) FR1 a Ha);
      intros (r & Hin & Hr); cbn in Hin; destruct Hin as [<- | [<- | []]]; cbn in Hr; lia
    | intros (r & Hin & Hr); cbn in Hin; destruct Hin as [<- | [<- | []]];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite B44 in Hr; lia
      | cbn in Hr; lia ] ]
  | intros a Hp; apply (apresent_grows _ _ _ _ GR3); apply Hpres2; apply (apresent_grows _ _ _ _ GR1); exact Hp
  | unfold arm; pose proof (field_of_region _ _ 44%nat (as_errno B) _ 0 4 0 4 0 4%N (SLit 11) 11 RF) as VF;
    rewrite Z.add_0_r in VF; apply VF;
    [ rewrite ?ew_ewset_other by lia; exact B44 | left; reflexivity | reflexivity | cbn; lia | cbn; lia ] ].
Qed.

Lemma dend_post_xR : forall cx Hp kr s1 D ly1 S1 Hp1 W1 m' md' k1 regs' e1 e' h1 out1 ev' LB1 spent jb a tl,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m' md' k1 ->
aregs_preserved (dxregs cx) regs' ->
apres_kept B (dxW cx) (dxmem cx) W1 m' ->
e' = dset_eof e1 (if hs_closed h1 =? 1 then 1 else re_eof e1) ->
garr8 SEGS (arm W1 m') (dxSA cx) (bzs (entry_bytes e')) -> awr W1 m' (dxSA cx) AENT ->
aentry_ok B ly1 S1 W1 m' e' ->
asrc_at B ly1 S1 W1 m' (dHA RG cx) h1 ->
(forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> ~ (dHA RG cx <= x < dHA RG cx + ASRC) ->
   abyte_kept (dxW cx) (dxmem cx) W1 m' x) ->
aout_at B RG ly1 S1 W1 m' (dctl cx (Z.of_nat (length (with_nul (lines (dSTR cx) D)))) ev')
  (if dlive cx then dxO cx ++ LB1 else dxO cx) (dxmx cx)
  (if dlive cx then drain_b_c.ds_no s1 else dxno cx) (drain_b_c.ds_ocap s1) out1 ->
(dlive cx = false -> out1 = dxout cx /\ drain_b_c.ds_ocap s1 = dxcap cx) ->
Permutation (ablocks B ly1 S1)
  ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx) ->
DLINK s1 e1 h1 -> DSAME cx e1 h1 -> DHIST cx s1 D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 ->
J1 (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (drain_b_c.ds_ref s1) ->
drain_b_c.ds_pend s1 = [] -> drain_b_c.ds_eintr s1 = false -> 4096 <= drain_b_c.ds_cap s1 - ulen s1 ->
dlater cx s1 jb a tl -> dbud_x B MT RP MMAX cx kr ly1 S1 spent tl ->
dPOST_xR B PST ARx MT RP RG R cx Hp kr W1 (mkCfg (mkst regs' (getr (dxregs cx) 1) m' (seg_rom SEGS)) md').
Proof.
intros cx Hp kr s1 D ly1 S1 Hp1 W1 m' md' k1 regs' e1 e' h1 out1 ev' LB1 spent jb a tl HB HJ HRP HAPK He' HEB HEW HEOK
  HSRC HGK HOUT HDEAD HPERM HDL HDS HDH HJ1 HPE HEIN HROOM HLAT HBUD.
destruct HLAT as (fuel & Hn & Hwf & Ht & Hf).
destruct fuel as [|f]; [unfold dneed in Hn; lia|].
rewrite (drun_end f (dlive cx) (dxmx cx) s1 jb a HROOM HEIN HPE) in Ht, Hf. cbn [fst snd] in Ht, Hf. subst tl.
pose proof HDH as (HPS & HREF & HEXP & HFST & HCAP & HNO & HLB & HND & HSS & _ & _).
assert (HD : D = dPS cx) by (rewrite HPS; unfold pstream, prest; rewrite HPE; symmetry; apply app_nil_r).
subst D.
pose proof HDL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & _).
pose proof HDS as (S1' & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10).
pose proof HBUD as ((Bmo & Bsp & Bcost & _ & _) & Brm & _).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPB & _).
pose proof HSRC as (_ & _ & _ & _ & _ & Hcl01 & _ & _ & _ & _ & _ & _ & _ & _ & Hoff & _ & Hov01 & _).
assert (HCAPX : (if dlive cx then drain_b_c.ds_ocap s1 else dxcap cx) = drain_b_c.ds_ocap s1)
  by (revert HDEAD; destruct (dlive cx); intros HDEAD; [reflexivity | symmetry; exact (proj2 (HDEAD eq_refl))]).
assert (HNOX : (if dlive cx then drain_b_c.ds_no s1 else dxno cx) =
  (if dlive cx then dxno cx + dr_tot (dxh cx) else dxno cx))
  by (destruct (dlive cx); [exact HNO | reflexivity]).
assert (HRECS : hl_recs (hs_pending h1) = []) by (rewrite HPE in L7; exact (map_eq_nil _ _ L7)).
subst e'.
unfold dPOST_xR, dr_post_xR.
exists ly1, S1, Hp1, regs', m', md', k1, (dset_eof e1 (if hs_closed h1 =? 1 then 1 else re_eof e1)), h1, out1, ev', LB1,
  ((dxG cx, ATABLE) :: dxrest cx).
cbv zeta.
change (dr_fin (dxc cx) (dxmx cx) (dxno cx) (dxcap cx) (dxe cx) (dxh cx)) with (dfin cx).
change (dr_live (dxc cx) (dxh cx)) with (dlive cx).
rewrite <- Hf, HCAPX.
split; [reflexivity|].
split; [exact HJ|].
split; [exact HRP|].
split; [exact HAPK|].
split.
{ change (dr_cost MT (dxc cx) (dxmx cx) (dxno cx) (dxcap cx) (dxe cx) (dxh cx)) with (dcost MT cx).
  apply (mle_weaken MT _ _ spent _ MTL Bmo). unfold tr_cost in Bcost. cbn [fold_right] in Bcost. lia. }
(* the room left: the entry's kr under the cut's room (RMM drops the requests' own count) *)
split; [eapply (RMM S1); [|exact Brm]; lia|].
split; [exact (Permutation_trans HPB (dperm_mv_x _ _ _ _ _))|].
split; [exact (Permutation_trans HPERM (dperm_mv_x _ _ _ _ _))|].
split; [exact HEB|]. split; [exact HEW|]. split; [exact HEOK|].
cbn [dset_eof re_fd re_eof re_cap re_U re_skip re_keys re_hp re_kh].
split; [exact S1'|].
split; [rewrite S5, S2; reflexivity|].
split; [rewrite L1; unfold ulen in HROOM; lia|].
split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|].
split; [exact L5|].
split; [exact S10|].
split; [rewrite L4; exact HND|].
split; [rewrite L4; exact HSS|].
split; [exact HSRC|].
split; [exact HGK|].
split; [exact L11|].
split; [exact HCAP|].
split; [exact S3|]. split; [exact S5|].
split; [rewrite L6, HEIN; reflexivity|].
split; [exact HRECS|].
split; [destruct Hoff as [(_ & Ho) | (r & rs & Hr & _)]; [exact Ho | rewrite HRECS in Hr; discriminate]|].
split; [exact S6|]. split; [exact S7|]. split; [exact S8|].
split; [rewrite L9, HREF; reflexivity|].
split; [exact HEXP|].
split; [exact HFST|].
split; [exact S9|].
split.
{ rewrite L3. destruct HJ1 as (JK & _). rewrite JK, <- L9. unfold hs_state. cbn [ls_k].
  destruct Hov01 as [-> | ->]; reflexivity. }
split.
{ intros H0. rewrite L2. destruct HJ1 as (JK & JW & _).
  assert (Hs : drain_b_c.ds_skip s1 = false)
    by (rewrite L3 in H0; destruct (drain_b_c.ds_skip s1); [discriminate | reflexivity]).
  rewrite (JW Hs), <- L9. reflexivity. }
split; [exact HLB|].
rewrite HNOX in HOUT. exact HOUT.
Qed.

Theorem dr_end_xR : dr_end_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
intros HEPI cx Hpe kr s1 D W1 c1 HB HDE.
destruct HDE as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & tl &
  -> & Hsp & H3 & H4 & R21 & R23 & R19 & HFRM & HDM & HNZ & HUS & HDL & HDS & HDH & HJ1 & HPE & HEIN &
  HROOM & HLAT & HBUD).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HDM as (HJ & HROM & HAPK & HFRS & _ & HEB & HEW & HEX & HSRC & HOTH & HGK & HOUT & HDEAD & HPERM).
pose proof HB as (HPRE0 & _ & _ & HGle & HSAle & _ & _ & _ & _ & Hj & _).
pose proof HPRE0 as (_ & Hra & _).
pose proof HFRM as (_ & _ & F40 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F240 & HSV).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
assert (HGin : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym HPERM)); left; reflexivity).
pose proof HJ as (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
rewrite !Z.add_0_r in Hal16, Hslo, Hshi, Hstk0.
assert (HDS0 : DRAIN_STK_x = 17008) by reflexivity.
assert (RQT : req_size ATABLE = 896) by reflexivity.
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE HAR HGin) as (_ & HG4 & HGc & _).
rewrite RQT in HGc.
assert (HERRI : 0x10000 <= as_errno B /\ as_errno B + 4 <= 0x5fc000).
{ assert (HI4 : forall i, 0 <= i < 4 -> in_img SEGS (as_errno B + i)).
  { intros i Hi. apply (proj1 (HG (as_errno B + i) ltac:(unfold G_DR, G_SL, inG; cbn [In];
      repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]))). }
  pose proof (pa_img_range _ (HI4 0 ltac:(lia))) as P0. pose proof (pa_img_range _ (HI4 3 ltac:(lia))) as P3. lia. }
assert (TBE : forall x, dxSA cx <= x < dxSA cx + AENT -> ~ (as_errno B <= x < as_errno B + 4)).
{ intros x Hx He. apply (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE x HAR HGin);
    [rewrite RQT; unfold AENT, ATABLE in *; lia|].
  apply (proj1 (HG x ltac:(unfold G_DR, G_SL, inG; cbn [In];
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]))). }
assert (HEOK : aentry_ok B ly1 S1 W1 m1 e1).
{ destruct HEX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & _ & X9 & X10 & X11 & X12 & X13 & X14).
  exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj X7 (conj HUS (conj HNZ
    (conj X9 (conj X10 (conj X11 (conj X12 (conj X13 X14)))))))))))))). }
pose proof HEOK as (_ & _ & Hpd1 & Hpd2 & _).
pose proof HSRC as (_ & _ & Vcl & _ & _ & Hcl01 & _).
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAWE & _).
set (L := aentry_blks e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx) in HPERM.
assert (INL : forall b, In b L -> In b (ablocks B ly1 S1))
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPERM)); right; exact Hb).
assert (FE : forall r, In r (aentry_fp e1) -> forall x, fst r <= x < snd r ->
  dlow cx x /\ ~ (as_errno B <= x < as_errno B + 4)).
{ apply (dend_fp_entry_x cx ly1 S1 Hp1 W1 m1 md1 e1 L HAR HPERM); [|exact HEOK].
  intros b Hb. unfold L. apply in_or_app. left. exact Hb. }
assert (FS : forall r, In r (asrc_fp (dHA RG cx) h1) -> forall x, fst r <= x < snd r ->
  dlow cx x /\ ~ (as_errno B <= x < as_errno B + 4)).
{ apply (dend_fp_src_x cx ly1 S1 Hp1 W1 m1 md1 L h1 HAR HPERM); [| exact HGin | exact Hj | exact HSRC].
  intros b Hb. unfold L. apply in_or_app. right. apply in_or_app. left. exact Hb. }
assert (FO : forall r, In r (aout_fp B RG (drain_b_c.ds_ocap s1) out1) -> forall x, fst r <= x < snd r ->
  dlow cx x /\ (r <> (as_errno B, as_errno B + 4) -> ~ (as_errno B <= x < as_errno B + 4))).
{ eapply (dend_fp_out_x cx ly1 S1 Hp1 W1 m1 md1 _ _ _ _ _ _ L HAR HPERM); [| exact HOUT].
  intros b Hb. unfold L. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
assert (FB : drain_b_c.ds_ocap s1 <> 0 -> forall x, out1 <= x < out1 + drain_b_c.ds_ocap s1 ->
  ~ (as_errno B <= x < as_errno B + 4)).
{ intros Hc x Hx. pose proof (req_size_pos (drain_b_c.ds_ocap s1)) as Hrq.
  pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
  destruct Hblk as [(Hc0 & _) | (Hcp & _ & _)]; [lia|].
  destruct (Hrq ltac:(lia)) as (_ & Hrq').
  refine (proj2 (dend_low_blk_x cx ly1 S1 Hp1 W1 m1 md1 L out1 (drain_b_c.ds_ocap s1) x HAR HPERM _ ltac:(lia))).
  unfold L. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
  unfold aout_blks. rewrite (proj2 (Z.eqb_neq _ _) Hc). left. reflexivity. }
assert (FG : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> dlow cx x /\ ~ (as_errno B <= x < as_errno B + 4))
  by (intros x Hx; exact (dend_gs_ok_x cx ly1 S1 Hp1 W1 m1 md1 x HAR HGin Hx)).
destruct Hcl01 as [Hc0 | Hc1].
- apply (dend_eagain_xR cx Hpe kr ly1 S1 Hp1 W1 m1 md1 k1 regs1 _ HB HJ HGin HAWE Hsp H3 H4 R21 R23 R19 F40 F240
    ltac:(rewrite <- Hc0; exact Vcl)).
  intros regsF mF mdF F2 F3 F4 HJF KV PR VE.
  apply (HEPI cx Hpe ly1 S1 Hp1 W1 mF mdF k1 regsF (dPOST_xR B PST ARx MT RP RG R cx Hpe kr) HJF).
  + unfold spZ in *. rewrite F2. exact Hsp.
  + rewrite F3. exact H3.
  + rewrite F4. exact H4.
  + exact Hra.
  + intros i Hi. eapply val_mem_kept; [|exact (HSV i Hi)]. intros k Hk.
    apply KV; unfold DRAIN_FRAME, DR_SAVE_OFF, ESTACK in *; lia.
  + intros regs' m' md' HRP Harm HJ'.
    set (P := fun x => as_errno B <= x < as_errno B + 4 \/ dsp0 cx - DRAIN_FRAME - ESTACK <= x < dsp0 cx - DRAIN_FRAME).
    assert (KVP : forall x, 0 <= x < 2 ^ 64 -> ~ P x -> aview SEGS (w_H W1) m' x = aview SEGS (w_H W1) m1 x).
    { intros x Hx HP. rewrite (aview_eq_of SEGS _ mF m' x (Harm _)).
      apply KV; [exact Hx | intros H; apply HP; left; exact H | intros H; apply HP; right; exact H]. }
    assert (PR' : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) m' x).
    { intros x Hp. destruct (PR x Hp) as [Hh [b Hb]]. split; [exact Hh|]. exists b.
      specialize (Harm (Z_to_bv 64 x)). unfold arm, mrestrict in Harm. rewrite Hh in Harm. rewrite Harm. exact Hb. }
    assert (VE' : val_mem SEGS (arm W1 m') (as_errno B) 4 11).
    { eapply val_mem_kept; [|exact VE]. intros k Hk. apply aview_eq_of. apply Harm. }
    assert (BK : forall x, 0 <= x < alloc_ceiling -> ~ (as_errno B <= x < as_errno B + 4) ->
      abyte_kept W1 m1 W1 m' x).
    { intros x Hx Hne. apply (dend_bk_x W1 m1 m' P x KVP PR'); [lia|].
      intros [H | H]; [exact (Hne H) | unfold DRAIN_FRAME, ESTACK in *; lia]. }
    apply (dend_post_xR cx Hpe kr s1 D ly1 S1 Hp1 W1 m' md' k1 regs' e1 e1 h1 out1 11 LB1 spent jb a tl HB HJ' HRP).
    * intros x Hi Hno He Hp. apply PR'. exact (HAPK x Hi Hno He Hp).
    * rewrite Hc0. change (0 =? 1) with false. cbv iota. symmetry. apply dset_eof_id_x.
    * apply (akept_garr8 W1 m1); [|exact HEB]. intros x Hx. unfold bzs in Hx.
      rewrite length_map in Hx. apply BK; [| apply TBE]; unfold AENT, ATABLE in *;
      unfold entry_bytes, re_nheld in Hx; rewrite !length_app, !Mem.length_le4, !Mem.length_le8, Hpd1, Hpd2 in Hx; lia.
    * intros i Hi. unfold arm. apply (writable_kept (w_H W1) m1 m'); [apply PR' | exact (HEW i Hi)].
    * apply (aentry_ok_kept B ly1 S1 W1 m1 ly1 S1 W1 m' e1 HEOK);
        [|intros b Hb; apply INL; unfold L; apply in_or_app; left; exact Hb].
      intros r Hr x Hx. destruct (FE r Hr x Hx) as [[Hl _] Hne]. exact (BK x Hl Hne).
    * apply (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m' (dHA RG cx) h1 HSRC);
        [|intros b Hb; apply INL; unfold L; apply in_or_app; right; apply in_or_app; left; exact Hb].
      intros r Hr x Hx. destruct (FS r Hr x Hx) as [[Hl _] Hne]. exact (BK x Hl Hne).
    * intros x Hx Hn. pose proof (HGK x Hx Hn) as K1. destruct (FG x Hx) as [[Hl _] Hne].
      pose proof (BK x Hl Hne) as K2. split; [rewrite (proj1 K2); exact (proj1 K1)|].
      intros Hw. apply (proj2 K2). apply (proj2 K1). exact Hw.
    * apply (dend_aout_ev_x ly1 S1 W1 m1 m' _ _ _ _ _ _ 11 HOUT).
      -- intros r Hr x Hx Hne. destruct (FO r Hr x Hx) as [[Hl _] _]. exact (BK x Hl Hne).
      -- exact FB.
      -- exact VE'.
      -- intros i Hi. unfold arm. apply (writable_kept (w_H W1) m1 m'); [apply PR' | exact (HAWE i Hi)].
      -- lia.
    * exact HDEAD.
    * exact HPERM.
    * exact HDL.
    * exact HDS.
    * exact HDH.
    * exact HJ1.
    * exact HPE.
    * exact HEIN.
    * exact HROOM.
    * exact HLAT.
    * exact HBUD.
- apply (dend_closed_xR cx Hpe kr ly1 S1 Hp1 W1 m1 md1 k1 regs1 _ HB HJ HGin HEW Hsp R21 R23 R19 F40 F240
    ltac:(rewrite <- Hc1; exact Vcl)).
  intros regsF mF mdF F2 F3 F4 HJF KV PR VE.
  apply (HEPI cx Hpe ly1 S1 Hp1 W1 mF mdF k1 regsF (dPOST_xR B PST ARx MT RP RG R cx Hpe kr) HJF).
  + unfold spZ in *. rewrite F2. exact Hsp.
  + rewrite F3. exact H3.
  + rewrite F4. exact H4.
  + exact Hra.
  + intros i Hi. eapply val_mem_kept; [|exact (HSV i Hi)]. intros k Hk.
    apply KV; unfold DRAIN_FRAME, DR_SAVE_OFF, AENT, ATABLE in *; lia.
  + intros regs' m' md' HRP Harm HJ'.
    set (P := fun x => dxSA cx + 4 <= x < dxSA cx + 8).
    assert (KVP : forall x, 0 <= x < 2 ^ 64 -> ~ P x -> aview SEGS (w_H W1) m' x = aview SEGS (w_H W1) m1 x).
    { intros x Hx HP. rewrite (aview_eq_of SEGS _ mF m' x (Harm _)). exact (KV x Hx HP). }
    assert (PR' : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) m' x).
    { intros x Hp. destruct (PR x Hp) as [Hh [b Hb]]. split; [exact Hh|]. exists b.
      specialize (Harm (Z_to_bv 64 x)). unfold arm, mrestrict in Harm. rewrite Hh in Harm. rewrite Harm. exact Hb. }
    assert (VE' : val_mem SEGS (arm W1 m') (dxSA cx + 4) 4 1).
    { eapply val_mem_kept; [|exact VE]. intros k Hk. apply aview_eq_of. apply Harm. }
    assert (BK : forall x, dlow cx x -> abyte_kept W1 m1 W1 m' x).
    { intros x [Hx Hnt]. apply (dend_bk_x W1 m1 m' P x KVP PR'); [lia|].
      intros H. apply Hnt. unfold P, AENT, ATABLE in *. lia. }
    apply (dend_post_xR cx Hpe kr s1 D ly1 S1 Hp1 W1 m' md' k1 regs' e1 (dset_eof e1 1) h1 out1 ev1 LB1 spent jb a tl HB HJ' HRP).
    * intros x Hi Hno He Hp. apply PR'. exact (HAPK x Hi Hno He Hp).
    * rewrite Hc1. reflexivity.
    * apply (dend_garr8_eof_x W1 m1 m' (dxSA cx) e1 HEB); [| exact Hpd1 | exact Hpd2 | exact VE'].
      intros x Hx Hn. apply KVP; [unfold AENT, ATABLE in *; lia | exact Hn].
    * intros i Hi. unfold arm. apply (writable_kept (w_H W1) m1 m'); [apply PR' | exact (HEW i Hi)].
    * apply dend_aentry_eof_x; [|right; reflexivity].
      apply (aentry_ok_kept B ly1 S1 W1 m1 ly1 S1 W1 m' e1 HEOK);
        [|intros b Hb; apply INL; unfold L; apply in_or_app; left; exact Hb].
      intros r Hr x Hx. destruct (FE r Hr x Hx) as [Hl _]. exact (BK x Hl).
    * apply (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m' (dHA RG cx) h1 HSRC);
        [|intros b Hb; apply INL; unfold L; apply in_or_app; right; apply in_or_app; left; exact Hb].
      intros r Hr x Hx. destruct (FS r Hr x Hx) as [Hl _]. exact (BK x Hl).
    * intros x Hx Hn. pose proof (HGK x Hx Hn) as K1. destruct (FG x Hx) as [Hl _].
      pose proof (BK x Hl) as K2. split; [rewrite (proj1 K2); exact (proj1 K1)|].
      intros Hw. apply (proj2 K2). apply (proj2 K1). exact Hw.
    * apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m' _ _ _ _ _ _ HOUT);
        [|intros b Hb; apply INL; unfold L; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hb].
      intros r Hr x Hx. destruct (FO r Hr x Hx) as [Hl _]. exact (BK x Hl).
    * exact HDEAD.
    * exact HPERM.
    * exact HDL.
    * exact HDS.
    * exact HDH.
    * exact HJ1.
    * exact HPE.
    * exact HEIN.
    * exact HROOM.
    * exact HLAT.
    * exact HBUD.
Qed.

End wR.

(* ---- the strict lemmas of this Section at R := wle: each is its R twin above at wle (wle_refl, wle_trans, the
   identity for WLE_R); the statements are the strict ones, checked by conversion. ---- *)
Theorem dr_epi_x : dr_epi_stmt_x B PST ARx RG.
Proof. eapply (dr_epi_xR (@wle SEGS)). all: first [ exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun (W W' : world SEGS) (H : @wle SEGS W W') => H) ]. Qed.
Lemma dend_sp_x : forall cx Hpe ly1 S1 Hp1 W1 m1 md1 k1 regs1,
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hpe (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m1 md1 k1 ->
spZ regs1 = dsp0 cx - DRAIN_FRAME ->
alloc_ceiling <= spZ regs1 /\ spZ regs1 + DRAIN_FRAME <= 2 ^ 47 /\ 2 ^ 46 <= spZ regs1 /\ spZ regs1 mod 16 = 0.
Proof. eapply (dend_sp_xR (@wle SEGS)). all: first [ exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun (W W' : world SEGS) (H : @wle SEGS W W') => H) ]. Qed.
Lemma dend_closed_x : forall cx Hpe kr ly1 S1 Hp1 W1 m1 md1 k1 regs1 (Q : world SEGS -> config -> Prop),
DBASE_x B ARx MT RP MMAX RG cx Hpe kr ->
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hpe (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m1 md1 k1 ->
In (dxG cx, ATABLE) (ablocks B ly1 S1) ->
awr W1 m1 (dxSA cx) AENT ->
spZ regs1 = dsp0 cx - DRAIN_FRAME ->
getr regs1 21 = w64 (dxSA cx) -> getr regs1 23 = w64 (dHA RG cx) ->
getr regs1 19 = w64 (SHADOW_OFF + 12 * Z.of_nat (dxj cx)) ->
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 40) 8 ((rg_s RG + 8) / 8) ->
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 240) 8 SHADOW_OFF ->
val_mem SEGS (arm W1 m1) (dHA RG cx + 8) 4 1 ->
(forall regsF mF mdF,
  getr regsF 2 = getr regs1 2 -> getr regsF 3 = getr regs1 3 -> getr regsF 4 = getr regs1 4 ->
  @ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) Hpe (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 mF mdF k1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (dxSA cx + 4 <= a < dxSA cx + 8) ->
     aview SEGS (w_H W1) mF a = aview SEGS (w_H W1) m1 a) ->
  (forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) mF a) ->
  val_mem SEGS (arm W1 mF) (dxSA cx + 4) 4 1 ->
  SRr SEGS W1 (cfg_at SEGS (BASE + A_dr_epi) regsF mF mdF) Q) ->
SRr SEGS W1 (cfg_at SEGS (BASE + A_dr_end) regs1 m1 md1) Q.
Proof. eapply (dend_closed_xR (@wle SEGS)). all: first [ exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun (W W' : world SEGS) (H : @wle SEGS W W') => H) ]. Qed.
Lemma dend_eagain_x : forall cx Hpe kr ly1 S1 Hp1 W1 m1 md1 k1 regs1 (Q : world SEGS -> config -> Prop),
DBASE_x B ARx MT RP MMAX RG cx Hpe kr ->
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hpe (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m1 md1 k1 ->
In (dxG cx, ATABLE) (ablocks B ly1 S1) ->
awr W1 m1 (as_errno B) 4 ->
spZ regs1 = dsp0 cx - DRAIN_FRAME ->
getr regs1 3 = getr (dxregs cx) 3 -> getr regs1 4 = getr (dxregs cx) 4 ->
getr regs1 21 = w64 (dxSA cx) -> getr regs1 23 = w64 (dHA RG cx) ->
getr regs1 19 = w64 (SHADOW_OFF + 12 * Z.of_nat (dxj cx)) ->
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 40) 8 ((rg_s RG + 8) / 8) ->
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 240) 8 SHADOW_OFF ->
val_mem SEGS (arm W1 m1) (dHA RG cx + 8) 4 0 ->
(forall regsF mF mdF,
  getr regsF 2 = getr regs1 2 -> getr regsF 3 = getr regs1 3 -> getr regsF 4 = getr regs1 4 ->
  @ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) Hpe (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 mF mdF k1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ (dsp0 cx - DRAIN_FRAME - ESTACK <= a < dsp0 cx - DRAIN_FRAME) ->
     aview SEGS (w_H W1) mF a = aview SEGS (w_H W1) m1 a) ->
  (forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) mF a) ->
  val_mem SEGS (arm W1 mF) (as_errno B) 4 11 ->
  SRr SEGS W1 (cfg_at SEGS (BASE + A_dr_epi) regsF mF mdF) Q) ->
SRr SEGS W1 (cfg_at SEGS (BASE + A_dr_end) regs1 m1 md1) Q.
Proof. eapply (dend_eagain_xR (@wle SEGS)). all: first [ exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun (W W' : world SEGS) (H : @wle SEGS W W') => H) ]. Qed.
Lemma dend_post_x : forall cx Hp kr s1 D ly1 S1 Hp1 W1 m' md' k1 regs' e1 e' h1 out1 ev' LB1 spent jb a tl,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m' md' k1 ->
aregs_preserved (dxregs cx) regs' ->
apres_kept B (dxW cx) (dxmem cx) W1 m' ->
e' = dset_eof e1 (if hs_closed h1 =? 1 then 1 else re_eof e1) ->
garr8 SEGS (arm W1 m') (dxSA cx) (bzs (entry_bytes e')) -> awr W1 m' (dxSA cx) AENT ->
aentry_ok B ly1 S1 W1 m' e' ->
asrc_at B ly1 S1 W1 m' (dHA RG cx) h1 ->
(forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> ~ (dHA RG cx <= x < dHA RG cx + ASRC) ->
   abyte_kept (dxW cx) (dxmem cx) W1 m' x) ->
aout_at B RG ly1 S1 W1 m' (dctl cx (Z.of_nat (length (with_nul (lines (dSTR cx) D)))) ev')
  (if dlive cx then dxO cx ++ LB1 else dxO cx) (dxmx cx)
  (if dlive cx then drain_b_c.ds_no s1 else dxno cx) (drain_b_c.ds_ocap s1) out1 ->
(dlive cx = false -> out1 = dxout cx /\ drain_b_c.ds_ocap s1 = dxcap cx) ->
Permutation (ablocks B ly1 S1)
  ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx) ->
DLINK s1 e1 h1 -> DSAME cx e1 h1 -> DHIST cx s1 D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 ->
J1 (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (drain_b_c.ds_ref s1) ->
drain_b_c.ds_pend s1 = [] -> drain_b_c.ds_eintr s1 = false -> 4096 <= drain_b_c.ds_cap s1 - ulen s1 ->
dlater cx s1 jb a tl -> dbud_x B MT RP MMAX cx kr ly1 S1 spent tl ->
dPOST_x B PST ARx MT RP RG cx Hp kr W1 (mkCfg (mkst regs' (getr (dxregs cx) 1) m' (seg_rom SEGS)) md').
Proof. eapply (dend_post_xR (@wle SEGS)). all: first [ exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun (W W' : world SEGS) (H : @wle SEGS W W') => H) ]. Qed.
Theorem dr_end_x : dr_end_stmt_x B PST ARx MT RP MMAX RG.
Proof. eapply (dr_end_xR (@wle SEGS)). all: first [ exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun (W W' : world SEGS) (H : @wle SEGS W W') => H) ]. Qed.
End cx.
End b.
End a.
