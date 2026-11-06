(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the SEARCH stage of segment GS of the ASan+UBSan walk (image B,
   fuzz_reply.asan-ubsan) of fuzz_reply's drain -- gesture_seen's held-array search (relay.c:100-109, inlined),
   DGS 0x83aa4 -> GA 0x83ba0 / GF 0x83cb4 / DLN 0x839d4.  Proves no function (kind: segment lemma of drain's
   image-B walk, GS piece gs_scan): pb_gs_scan : gs_scan_stmt (lib/B/W_drain_gs.v:280), the Section arguments
   as in W_drain_gs.v.  In the form of image A's lib/A/W_gsscan_scratch.v gs_scan_of_loop (a working branch
   0c06ccc287f); every pc, register and frame slot is image B's (fuzz_reply.objdump.txt sha256 17f5c434bf57; internal record):
     0x83aa4 sd s9,24(sp)                              24(sp) = bg
     0x83aa8 .. 0x83ac0  ld 32(sp) (SA + 48); srli; ld 240(sp) (the shadow base); add; sd 16(sp); lb; bnez
                         the shadow byte of &e->nheld: folded by the token layer (gse_SH over SA + 40 .. SA + 56)
     0x83ac4 lw a1,0(a0)                               nheld (the engine folds the sign extension: atom 34 < 2^26)
     0x83ac8 sub a0,s3,s8; sd 192(sp)                  192(sp) = jj
     0x83ad0 ld 88(sp) (SA + 40); srli; sd 96(sp); sd a1,112(sp)
     0x83ae0 blez a1,0x83ba0                            nheld <= 0: nothing held, so GA
     0x83ae4 .. 0x83af8  0(sp) = shadow (SA + 40); lbu; bnez   folded
     0x83afc .. 0x83b30  s4 = 0; s6 = e->hp; s3 = nheld; s9 = snez hp; 168(sp) = (hp & 7 == 0) & snez hp;
                         160(sp) = 8 max(nheld, 0); then the loop head 0x83b34 (GSL at n = 0)
   The stage writes only 0, 16, 24, 96, 112, 160, 168 and 192 of drain's frame (gsW of lib/B/W_gsscan_cx.v), so
   dr_frame and the line loop's core move to the new memory (gsc_frame_keep, gsc_core_kept).  No trap site lies on
   this stretch (the stage's three are the loop's: lib/B/W_gsscan_loop.v). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_traps W_gsscan_cx W_gsscan_loop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Lemma gse_le4_bytes : forall v, 0 <= v < 2 ^ 32 -> Mem.le4 (Z_to_bv 64 v) = Z_to_le_bytes 4 v.
Proof.
intros v Hv. unfold Mem.le4. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. reflexivity.
Qed.

Ltac gse_len := rewrite ?length_app, ?gsc_bzs_len, ?Mem.length_le8, ?Mem.length_le4, ?length_Z_to_le_bytes; cbn [length].

(* a register's symbolic value as the state holds it *)
Ltac gse_rreg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?Ev ?ssv (restrict ?H ?msv) =>
  pose proof (st_ok_pi_restrict_reg H Ev ssv msv r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ssv) r) in
  change (sr_get (ss_regs ssv) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.

Ltac gse_in := cbn [In]; repeat first [left; reflexivity | right].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* the two cells of the relay entry the search reads: e->held at + 40 and e->nheld at + 48 *)
Lemma gse_entry_hp : forall (W : world SEGS) m SA e,
length (re_pad1 e) = 4%nat -> 0 <= re_hp e < 2 ^ 64 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) ->
val_mem SEGS (arm W m) (SA + 40) 8 (re_hp e).
Proof.
intros W m SA e Hp1 Hhp H.
unfold entry_bytes in H. rewrite !gsc_bzs_app, !app_assoc in H.
apply garr8_app in H as [H _]. apply garr8_app in H as [H _]. apply garr8_app in H as [_ H].
rewrite (gsc_le8_bytes (re_hp e) Hhp) in H.
apply (gsc_val_of_garr8 W m _ 8 _); [change (8 * Z.of_nat 8) with 64; exact Hhp|].
apply (gsc_garr8_at _ _ _ _ H). gse_len. lia.
Qed.

Lemma gse_entry_nheld : forall (W : world SEGS) m SA e,
length (re_pad1 e) = 4%nat -> 0 <= re_nheld e < 2 ^ 32 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) ->
val_mem SEGS (arm W m) (SA + 48) 4 (re_nheld e).
Proof.
intros W m SA e Hp1 Hnh H.
unfold entry_bytes in H. rewrite !gsc_bzs_app, !app_assoc in H.
apply garr8_app in H as [H _]. apply garr8_app in H as [_ H].
rewrite (gse_le4_bytes (re_nheld e) Hnh) in H.
apply (gsc_val_of_garr8 W m _ 4 _); [change (8 * Z.of_nat 4) with 32; exact Hnh|].
apply (gsc_garr8_at _ _ _ _ H). gse_len. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The symbolic state at DGS (0x83aa4), as the engine runs it.  Registers are their own atoms; atoms 32 = SA,
   33 = e->hp, 34 = e->nheld, 35 = SHADOW_OFF (240(sp), the shadow base Bx).  The frame is split into the six
   windows the stage writes (gsW) and the three slots it reads (32 = SA + 48, 88 = SA + 40, 240 = SHADOW_OFF);
   the entry region carries e->hp and e->nheld.
   --------------------------------------------------------------------------------------------------------- *)
Definition gse_regions : smem :=
[ YP09.mkRegion (Some 2%nat) 0 8 0 8 [];
  YP09.mkRegion (Some 2%nat) 16 32 16 32 [];
  YP09.mkRegion (Some 2%nat) 32 40 0 0 [YP09.mkChunk 32 (CVal 8 (SOff 32 48))];
  YP09.mkRegion (Some 2%nat) 88 96 0 0 [YP09.mkChunk 88 (CVal 8 (SOff 32 40))];
  YP09.mkRegion (Some 2%nat) 96 104 96 104 [];
  YP09.mkRegion (Some 2%nat) 112 120 112 120 [];
  YP09.mkRegion (Some 2%nat) 160 176 160 176 [];
  YP09.mkRegion (Some 2%nat) 192 200 192 200 [];
  YP09.mkRegion (Some 2%nat) 240 248 0 0 [YP09.mkChunk 240 (CVal 8 (SOff 35 0))];
  YP09.mkRegion (Some 32%nat) 40 52 0 0 [YP09.mkChunk 40 (CVal 8 (SOff 33 0)); YP09.mkChunk 48 (CVal 4 (SOff 34 0))] ].
Definition gse_facts : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (35%nat, mkAF SB SB 0);
          (32%nat, mkAF 4096 GL_PHI 3); (33%nat, mkAF 0 GL_PHI 0); (34%nat, mkAF 0 (2 ^ 26) 0) ] [] [].
Definition ss_gse : sstate := mkSS A_dr_seen sr_atoms gse_regions None gse_facts.
Definition gse_Bx : sv := SOff 35 0.
Definition gse_SH : list shent := [ mkSHE 32 40 56 ].
Definition gse_extra (SA HP NH : Z) : list word := map (Z_to_bv 64) [SA; HP; NH; SHADOW_OFF].

Lemma gse_entry : forall (W : world SEGS) regs1 m1 sp SA HP NH,
spZ regs1 = sp -> 2 ^ 46 <= sp -> sp + DRAIN_FRAME <= 2 ^ 47 -> sp mod 16 = 0 ->
4096 <= SA -> SA mod 8 = 0 -> SA + 56 <= GL_PHI -> SA + 56 <= sp ->
0 <= HP <= GL_PHI -> 0 <= NH < 2 ^ 26 ->
(forall o, gsW o -> writable_at SEGS (arm W m1) (sp + o)) ->
val_mem SEGS (arm W m1) (sp + 32) 8 (SA + 48) ->
val_mem SEGS (arm W m1) (sp + 88) 8 (SA + 40) ->
val_mem SEGS (arm W m1) (sp + 240) 8 SHADOW_OFF ->
val_mem SEGS (arm W m1) (SA + 40) 8 HP ->
val_mem SEGS (arm W m1) (SA + 48) 4 NH ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (gse_extra SA HP NH))) ss_gse
(restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_seen)) m1 (seg_rom SEGS))).
Proof.
intros W regs1 m1 sp SA HP NH Hsp Hlo Hhi Hal HSA1 HSA8 HSA2 HSA3 HHP HNH WR M32 M88 M240 MHP MNH.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs1 (gse_extra SA HP NH))).
assert (E2 : ew E 2 = getr regs1 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 HP) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 NH) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (Usp : bv_unsigned (ew E 2) = sp) by (rewrite E2; exact Hsp).
assert (Usa : bv_unsigned (ew E 32) = SA) by (rewrite E32; apply unsigned_lit_small; unfold GL_PHI in *; lia).
unfold GL_PHI in HSA2, HHP. unfold DRAIN_FRAME in Hhi.
unfold ss_gse. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold gse_regions.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?Usp, ?Usa.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; apply WR; unfold gsW; lia | apply Forall_nil].
  + split; [lia|]. split; [lia|]. split; [intros o Ho; apply WR; unfold gsW; lia | apply Forall_nil].
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ sp 32 8 (SOff 32 48) (SA + 48));
      [rewrite (den_atom E 32%nat SA 48 E32) by lia; reflexivity | cbn; lia | cbn; lia | exact M32].
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ sp 88 8 (SOff 32 40) (SA + 40));
      [rewrite (den_atom E 32%nat SA 40 E32) by lia; reflexivity | cbn; lia | cbn; lia | exact M88].
  + split; [lia|]. split; [lia|]. split; [intros o Ho; apply WR; unfold gsW; lia | apply Forall_nil].
  + split; [lia|]. split; [lia|]. split; [intros o Ho; apply WR; unfold gsW; lia | apply Forall_nil].
  + split; [lia|]. split; [lia|]. split; [intros o Ho; apply WR; unfold gsW; lia | apply Forall_nil].
  + split; [lia|]. split; [lia|]. split; [intros o Ho; apply WR; unfold gsW; lia | apply Forall_nil].
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ sp 240 8 (SOff 35 0) SHADOW_OFF);
      [rewrite (den_atom0 E 35%nat SHADOW_OFF E35) by (unfold SHADOW_OFF; lia); reflexivity
      | cbn; unfold SHADOW_OFF; lia | cbn; lia | exact M240].
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ SA 40 8 (SOff 33 0) HP);
        [rewrite (den_atom0 E 33%nat HP E33) by lia; reflexivity | cbn; lia | cbn; lia | exact MHP].
    * apply (chunk_ok_val SEGS E _ SA 48 4 (SOff 34 0) NH);
        [rewrite (den_atom0 E 34%nat NH E34) by lia; reflexivity | cbn; lia | cbn; lia | exact MNH].
- apply pairwise_disjoint_of_extents.
  unfold gse_regions, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Usa.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [gse_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, Usa, E35, E33, E34, !unsigned_lit_small by (unfold SB, SHADOW_OFF, GL_PHI; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SB, SHADOW_OFF, GL_PHI. repeat match goal with |- _ /\ _ => split end; (exact I || assumption || lia).
Qed.

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

(* The registers the stage leaves alone up to each exit. *)
Definition GS_KEPT1 : list (bv 5) := [2; 3; 4; 8; 9; 18; 23; 24; 27]%bv.
Definition GS_KEPT2 : list (bv 5) := [2; 3; 4; 8; 9; 18; 23; 24]%bv.

(* The stage, given the held-search loop (lib/B/W_gsscan_cx.v gs_scan_loop_stmt). *)
Theorem gs_scan_of_loop : gs_scan_loop_stmt B MT MMAX RG -> gs_scan_stmt B MT MMAX RG.
Proof using LAWS HG HGSB HV9 HSD HSM.
clear HGR HROMO HGO MTL TL AERRNO AMEMCPY AMEMMOVE AMEMCHR HCROM ASTRRCHR ASTRNCMP ASTRCMP ASTRLEN AREALLOC AFREE
  ASTRNDUP ALLOC_TAIL SLSPEC LPSPEC HERRNO HERRZ HERRW HERRAL HGSZ HVS HLIT5 HLIT6 HLIT7 HRGD HMMAX.
intros LOOP.
unfold gs_scan_stmt. intros cx s1 D p q W1 c1 HB HGS HDLN HGA HGF.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@ASAN_CEIL_range rc) as (HAC & _). unfold ASAN_CEIL in HAC.
assert (HES : ESTACK = 4096) by reflexivity. assert (HDF : DRAIN_FRAME = 352) by reflexivity.
assert (HDS : DRAIN_STK = 16880) by reflexivity.
unfold DGS in HGS.
destruct HGS as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & oo & ha & ks & tl
  & kd & jj & bg & Hcfg & Hregs & H23 & H24 & H19 & H26 & H25 & Hbgr & Hbgk & Hband & Hcap & Hgest & Hjjr
  & Hbd & Hpq & Hq0 & Hnz & Hskp & Hlim & HLC & HFUT).
pose proof Hregs as (Hsp & R3 & R4 & R21 & R20 & R22 & R27 & R8 & R9 & R18 & HFR).
pose proof HFR as (F8 & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F88 & F104 & F120 & F128 & F136 & F144 & F152
  & F176 & F184 & F200 & F208 & F216 & F224 & F232 & F240 & Hsaved).
pose proof HLC as HLC'. unfold LCORE in HLC'.
destruct HLC' as (HMEM & HLINK & HSAME & HHIST & HRS & HBUD).
pose proof HMEM as (HJ & Hrom & Hpresk & Hframes & _ & Hgarr & Hawr & HOKX & Hsrc & Hoth & Hgsk & Hout & Hlivout & Hperm).
assert (HAR : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
pose proof HB as (Hafn & HBx10 & Htbl & HSAlo & HSAhi & HSA8 & Hgarr0 & Hawr0 & Hent0 & HJ4 & HBrest).
destruct (gsc_stack B MT MMAX RG cx HB) as (HSTK1 & HSTK2 & Hal16 & _).
assert (HTB : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE HAR HTB) as (HG16 & HG4096 & HGceil & HGia & HGpres & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity). rewrite RQT in HGceil.
unfold ATABLE, AENT in *.
pose proof HOKX as (Heof & Hskipe & Hpad1 & Hpad2 & Hfd & Hcapr & HUlen & Husedr & Hbufc & Hnheld & Hheld & HND1 & HND2 & Hkeys).
(* the journal's stack: the frame is present, hence writable *)
pose proof HJ as (HSTKj & HXOj & (memS & HJi & HAGj) & HOUTj).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRESj & _).
assert (WRF : forall x, dsp0 cx - DRAIN_STK <= x < dsp0 cx -> writable_at SEGS (arm W1 m1) x)
  by (intros x Hx; apply (apresent_writable SEGS); apply HPRESj; lia).
(* the two cells the search reads off the relay entry *)
assert (HHPR : 0 <= re_hp e1 <= GL_PHI).
{ destruct Hheld as [(Hz & _)|(Hz & Hin & Hk1 & Hk2 & _)]; [unfold GL_PHI; lia|].
  destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (re_hp e1) (re_kh e1) HAR Hin) as (_ & H4 & Hc & _).
  pose proof (req_size_pos (re_kh e1) ltac:(lia)) as (Hr1 & Hr2). unfold GL_PHI. lia. }
assert (HNHR : 0 <= re_nheld e1 < 2 ^ 26) by (split; [unfold re_nheld; lia | exact Hnheld]).
pose proof (gse_entry_hp W1 m1 (dxSA cx) e1 Hpad1 ltac:(unfold GL_PHI in HHPR; lia) Hgarr) as MHP.
pose proof (gse_entry_nheld W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr) as MNH.
(* the symbolic state at 0x83aa4 *)
pose proof (gse_entry W1 regs1 m1 (dsp0 cx - DRAIN_FRAME) (dxSA cx) (re_hp e1) (re_nheld e1)
  Hsp ltac:(lia) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity)
  ltac:(lia) HSA8 ltac:(unfold GL_PHI; lia) ltac:(lia) HHPR HNHR
  ltac:(intros o Ho; apply WRF; unfold gsW in Ho; lia)
  F32 F88 F240 MHP MNH) as HS.
remember (Eimg (Ereg regs1 (gse_extra (dxSA cx) (re_hp e1) (re_nheld e1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (gse_extra (dxSA cx) (re_hp e1) (re_nheld e1))) E)
  by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EREG : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (re_hp e1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_nheld e1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (HBx : U E gse_Bx = SHADOW_OFF)
  by (unfold gse_Bx; rewrite (U_atom E 35 SHADOW_OFF E35) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok SEGS gse_Bx gse_SH E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W1) m1 E gse_Bx 32 (dxG cx) 896 (dxSA cx) 40 56).
  - apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) 896); [exact HAR | exact HTB | lia | rewrite RQT; lia].
  - exact HBx.
  - apply (U_atom E 32 (dxSA cx) E32). unfold GL_PHI in *. lia.
  - lia.
  - lia.
  - intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. rewrite RQT in HGia.
    unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *. lia. }
clear HE.
subst c1. unfold cfg_at. change (w64 (BASE + A_dr_seen)) with (Z_to_bv 64 (BASE + A_dr_seen)).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME)
  by (rewrite (EREG 2%nat 2%bv ltac:(lia) eq_refl); exact Hsp).
(* the write obligation: the six windows lie in drain's frame *)
paj_run_tok RUN HS HJ SHOK gl_Bspan.
{ apply awr_ok_x_of0; awr_ok_tac;
  repeat (eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (- DRAIN_FRAME));
          [ reflexivity
          | rewrite Usp; unfold DRAIN_FRAME; lia
          | cbn [YP09.r_wlo]; unfold DRAIN_FRAME; lia
          | cbn [YP09.r_whi]; unfold DRAIN_FRAME; lia
          | awr_ok_tac ]). }
match goal with Hg : mem_grows (mrestrict (w_H W1) m1) (mrestrict (w_H W1) (ms_mem ?mx)) |- _ =>
  rename Hg into GR1; rename mx into msA end.
match goal with Hf : frame_of _ _ (mrestrict (w_H W1) m1) (mrestrict (w_H W1) (ms_mem msA)) |- _ => rename Hf into HFr1 end.
(* the run wrote only the windows *)
assert (KEEP1 : forall x, 0 <= x < 2 ^ 64 -> ~ gsW (x - (dsp0 cx - DRAIN_FRAME)) ->
  aview SEGS (w_H W1) (ms_mem msA) x = aview SEGS (w_H W1) m1 x).
{ intros x Hx Hno. apply (aview_kept_out E _ (w_H W1) m1 (ms_mem msA) HFr1 x Hx).
  intros (r & Hri & Hr). cbn [ss_mem ss_gse gse_regions In] in Hri.
  repeat (destruct Hri as [<- | Hri];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; apply Hno; unfold gsW; lia |]).
  destruct Hri. }
assert (PRES1 : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msA) x)
  by (intros x Hp; exact (apresent_grows _ _ _ _ GR1 Hp)).
clear HFr1 GR1.
assert (E25 : ew E 25 = Z_to_bv 64 bg) by (rewrite (EREG 25%nat 25%bv ltac:(lia) eq_refl); exact H25).
assert (HUW : bzs (re_U e1) = dW s1)
  by (destruct HLINK as (_ & HU & _); unfold dvirt in HU; cbn [drain_b_c.ds_u] in HU; exact HU).
assert (HWlen : Z.of_nat (length (dW s1)) = re_used e1) by (rewrite <- HUW, gsc_bzs_len; exact HUlen).
assert (HBUF : In (re_buf e1, re_cap e1) (ablocks B ly1 S1) /\ 0 < re_cap e1).
{ destruct Hbufc as [(Hc0 & Hb0 & Hu0)|(Hcpos & Hbin & Hjunk & Hbuf8)]; [exfalso; lia | split; assumption]. }
destruct HBUF as (HBin & HBcap).
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (re_buf e1) (re_cap e1) HAR HBin) as (_ & HB4096 & HBceil & _).
assert (RQB : req_size (re_cap e1) = re_cap e1) by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
rewrite RQB in HBceil.
assert (HLINE : 0 <= re_buf e1 + Z.of_nat p /\ re_buf e1 + Z.of_nat p + Z.of_nat jj < 2 ^ 63).
{ split; [lia|]. assert (Z.of_nat q < re_used e1) by lia. lia. }
destruct HLINE as (HL1 & HL2).
assert (E24' : ew E 24 = Z_to_bv 64 (re_buf e1 + Z.of_nat p))
  by (rewrite (EREG 24%nat 24%bv ltac:(lia) eq_refl); exact H24).
assert (E19' : ew E 19 = Z_to_bv 64 (re_buf e1 + Z.of_nat p + Z.of_nat jj))
  by (rewrite (EREG 19%nat 19%bv ltac:(lia) eq_refl); exact H19).
psrr_branch_tok RUN BR HS SHOK gl_Bspan.
-
(* nheld <= 0: nothing is held, so the key is not held; on to GA (0x83ba0) *)
rewrite (gsc_bge0 E 34 (re_nheld e1) E34 ltac:(lia)) in Hc.
apply Z.leb_le in Hc.
assert (HN0 : re_nheld e1 = 0) by lia.
assert (HKE : re_keys e1 = []) by (apply length_zero_iff_nil; unfold re_nheld in HN0; lia).
paj_run_to_tok RUNTO HS HJ SHOK gl_Bspan A_dr_add.
{ apply awr_ok_x_of0; awr_ok_tac;
  repeat (eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (- DRAIN_FRAME));
          [ reflexivity
          | rewrite Usp; unfold DRAIN_FRAME; lia
          | cbn [YP09.r_wlo]; unfold DRAIN_FRAME; lia
          | cbn [YP09.r_whi]; unfold DRAIN_FRAME; lia
          | awr_ok_tac ]). }
match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem msA)) (mrestrict (w_H W1) (ms_mem ?mx)) |- _ =>
  rename Hg into GR2; rename mx into msB end.
match goal with Hf : frame_of _ _ (mrestrict (w_H W1) (ms_mem msA)) (mrestrict (w_H W1) (ms_mem msB)) |- _ => rename Hf into HFr2 end.
assert (KEEP2 : forall x, 0 <= x < 2 ^ 64 -> ~ gsW (x - (dsp0 cx - DRAIN_FRAME)) ->
  aview SEGS (w_H W1) (ms_mem msB) x = aview SEGS (w_H W1) m1 x).
{ intros x Hx Hno. rewrite <- (KEEP1 x Hx Hno).
  apply (aview_kept_out E _ (w_H W1) (ms_mem msA) (ms_mem msB) HFr2 x Hx).
  intros (r & Hri & Hr). cbn [ss_mem add_cond add_atom ss_gse gse_regions In] in Hri.
  repeat (destruct Hri as [<- | Hri];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; apply Hno; unfold gsW; lia |]).
  destruct Hri. }
assert (PRES2 : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msB) x)
  by (intros x Hp; exact (apresent_grows _ _ _ _ GR2 (PRES1 x Hp))).
pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ GS_KEPT1 HS HAE ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
(* the window slots the run wrote *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_region_nth Ev ssv msv 1 _ HS eq_refl) as HR1;
  pose proof (st_ok_pi_region_nth Ev ssv msv 4 _ HS eq_refl) as HR4;
  pose proof (st_ok_pi_region_nth Ev ssv msv 5 _ HS eq_refl) as HR5;
  pose proof (st_ok_pi_region_nth Ev ssv msv 7 _ HS eq_refl) as HR7 end.
cbn [ms_mem restrict] in HR1, HR4, HR5, HR7.
assert (N16 : val_mem SEGS (arm W1 (ms_mem msB)) (dsp0 cx - DRAIN_FRAME + 16) 8 ((dxSA cx + 48) / 8 + SHADOW_OFF)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 16 32 16 32 16
    (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 48) (SLit 3)) (SOff 35 0)) _ HR1 Usp ltac:(gse_in));
  [ apply gsc_den; apply (gsc_U_shadow E 32 35 (dxSA cx) 48 E32 E35); unfold GL_PHI in *; lia
  | apply gsc_shadow_range; unfold GL_PHI in *; lia ]. }
assert (N24 : val_mem SEGS (arm W1 (ms_mem msB)) (dsp0 cx - DRAIN_FRAME + 24) 8 bg).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 16 32 16 32 24 (SOff 25 0) _ HR1 Usp ltac:(gse_in));
  [ apply (den_atom0 E 25%nat bg E25); lia | lia ]. }
assert (N96 : val_mem SEGS (arm W1 (ms_mem msB)) (dsp0 cx - DRAIN_FRAME + 96) 8 ((dxSA cx + 40) / 8)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 96 104 96 104 96 (SAlu ALU_SRL (SOff 32 40) (SLit 3)) _ HR4 Usp
    ltac:(gse_in));
  [ apply gsc_den; apply (gsc_U_srl E 32 (dxSA cx) 40 E32); unfold GL_PHI in *; lia
  | split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; unfold GL_PHI in *; lia] ]. }
assert (N112 : val_mem SEGS (arm W1 (ms_mem msB)) (dsp0 cx - DRAIN_FRAME + 112) 8 (re_nheld e1)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 112 120 112 120 112 (SOff 34 0) _ HR5 Usp ltac:(gse_in));
  [ apply (den_atom0 E 34%nat (re_nheld e1) E34); lia | lia ]. }
assert (N192 : val_mem SEGS (arm W1 (ms_mem msB)) (dsp0 cx - DRAIN_FRAME + 192) 8 (Z.of_nat jj)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 192 200 192 200 192
    (SAlu ALU_ADD (SOff 19 0) (SMd M_MUL (SOff 24 0) (SLit (-1)))) _ HR7 Usp ltac:(gse_in));
  [ apply gsc_den; rewrite (gsc_U_sub2 E 24 19 (re_buf e1 + Z.of_nat p) (re_buf e1 + Z.of_nat p + Z.of_nat jj)
      E24' E19' ltac:(lia) ltac:(lia) ltac:(lia)); lia
  | lia ]. }
assert (FR2 : dr_frame RG cx W1 (ms_mem msB)).
{ apply (gsc_frame_keep RG cx W1 m1 (ms_mem msB)); [|exact HFR].
  intros x Hx Hno. apply KEEP2; [lia | exact Hno]. }
assert (HdlH : dlH cx s1 p = []).
{ destruct HLINK as (_ & _ & _ & HKT & _). unfold dvirt in HKT. cbn [drain_b_c.ds_H] in HKT.
  rewrite <- HKT, HKE. reflexivity. }
pmkst HS.
apply HGA. unfold GA.
exists (ms_regs msB), ly1, S1, (ms_mem msB). eexists. eexists.
exists e1, h1, out1, ev1, LB1, spent, jb, aa, oo, ha, ks, tl, kd, jj, bg.
split; [unfold cfg_at; reflexivity|].
split.
{ unfold dregs_gs.
  split; [unfold spZ; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Hsp|].
  split; [rewrite (HK 3%bv ltac:(cbv; tauto)); exact R3|].
  split; [rewrite (HK 4%bv ltac:(cbv; tauto)); exact R4|].
  split; [rewrite (HK 8%bv ltac:(cbv; tauto)); exact R8|].
  split; [rewrite (HK 9%bv ltac:(cbv; tauto)); exact R9|].
  split; [rewrite (HK 18%bv ltac:(cbv; tauto)); exact R18|].
  exact FR2. }
split; [rewrite (HK 27%bv ltac:(cbv; tauto)); exact R27|].
split; [rewrite (HK 23%bv ltac:(cbv; tauto)); exact H23|].
split; [rewrite (HK 24%bv ltac:(cbv; tauto)); exact H24|].
split; [exact N16|]. split; [exact N24|]. split; [exact N96|]. split; [exact N112|]. split; [exact N192|].
split; [exact Hbgr|]. split; [exact Hbgk|]. split; [exact Hband|]. split; [exact Hcap|].
split; [exact Hgest|]. split; [exact Hjjr|].
split; [rewrite HdlH; reflexivity|].
split; [unfold GSF; split; [exact Hbd|]; split; [exact Hpq|]; split; [exact Hq0|];
  split; [exact Hnz|]; split; [exact Hskp | exact Hlim]|].
split; [|exact HFUT].
apply (gsc_core_kept B MT MMAX RG LAWS HG HGSB HV9 HSD HSM cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl
  _ _ _ HJ4 ltac:(lia) ltac:(lia) HLC HJ).
+ intros x Hx. apply KEEP2; [lia | unfold gsW; lia].
+ exact PRES2.
+ exact FR2.
-
(* nheld > 0: the shadow check of &e->hp, the loop's seat, to 0x83b34 with n = 0 *)
rewrite (gsc_bge0 E 34 (re_nheld e1) E34 ltac:(lia)) in Hc.
apply Z.leb_gt in Hc.
destruct Hheld as [(Hz & Hk0)|(Hz & Hin & Hk1 & Hk2 & Hg8)]; [exfalso; unfold re_nheld in Hc; rewrite Hk0 in Hc; cbn in Hc; lia|].
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 (re_hp e1) (re_kh e1) HAR Hin) as (HH16 & HH4096 & _).
assert (HHP8 : re_hp e1 mod 8 = 0).
{ rewrite (Z.div_mod (re_hp e1) 16) by lia. rewrite HH16, Z.add_0_r.
  replace (16 * (re_hp e1 / 16)) with ((2 * (re_hp e1 / 16)) * 8) by lia. apply Z.mod_mul. lia. }
paj_run_to_tok RUNTO HS HJ SHOK gl_Bspan A_dr_hloop.
{ apply awr_ok_x_of0; awr_ok_tac;
  repeat (eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (- DRAIN_FRAME));
          [ reflexivity
          | rewrite Usp; unfold DRAIN_FRAME; lia
          | cbn [YP09.r_wlo]; unfold DRAIN_FRAME; lia
          | cbn [YP09.r_whi]; unfold DRAIN_FRAME; lia
          | awr_ok_tac ]). }
gse_rreg HS (19%bv : bv 5) P19. gse_rreg HS (20%bv : bv 5) P20.
gse_rreg HS (22%bv : bv 5) P22. gse_rreg HS (25%bv : bv 5) P25.
match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem msA)) (mrestrict (w_H W1) (ms_mem ?mx)) |- _ =>
  rename Hg into GR2; rename mx into msB end.
match goal with Hf : frame_of _ _ (mrestrict (w_H W1) (ms_mem msA)) (mrestrict (w_H W1) (ms_mem msB)) |- _ => rename Hf into HFr2 end.
assert (KEEP2 : forall x, 0 <= x < 2 ^ 64 -> ~ gsW (x - (dsp0 cx - DRAIN_FRAME)) ->
  aview SEGS (w_H W1) (ms_mem msB) x = aview SEGS (w_H W1) m1 x).
{ intros x Hx Hno. rewrite <- (KEEP1 x Hx Hno).
  apply (aview_kept_out E _ (w_H W1) (ms_mem msA) (ms_mem msB) HFr2 x Hx).
  intros (r & Hri & Hr). cbn [ss_mem add_cond add_atom ss_gse gse_regions In] in Hri.
  repeat (destruct Hri as [<- | Hri];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; apply Hno; unfold gsW; lia |]).
  destruct Hri. }
assert (PRES2 : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msB) x)
  by (intros x Hp; exact (apresent_grows _ _ _ _ GR2 (PRES1 x Hp))).
pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ GS_KEPT2 HS HAE ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
(* the eight window slots the setup wrote *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_region_nth Ev ssv msv 0 _ HS eq_refl) as HR0;
  pose proof (st_ok_pi_region_nth Ev ssv msv 1 _ HS eq_refl) as HR1;
  pose proof (st_ok_pi_region_nth Ev ssv msv 4 _ HS eq_refl) as HR4;
  pose proof (st_ok_pi_region_nth Ev ssv msv 5 _ HS eq_refl) as HR5;
  pose proof (st_ok_pi_region_nth Ev ssv msv 6 _ HS eq_refl) as HR6;
  pose proof (st_ok_pi_region_nth Ev ssv msv 7 _ HS eq_refl) as HR7 end.
cbn [ms_mem restrict] in HR0, HR1, HR4, HR5, HR6, HR7.
assert (N0 : val_mem SEGS (arm W1 (ms_mem msB)) (dsp0 cx - DRAIN_FRAME + 0) 8 ((dxSA cx + 40) / 8 + SHADOW_OFF)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 0 8 0 8 0
    (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 40) (SLit 3)) (SOff 35 0)) _ HR0 Usp ltac:(gse_in));
  [ apply gsc_den; apply (gsc_U_shadow E 32 35 (dxSA cx) 40 E32 E35); unfold GL_PHI in *; lia
  | apply gsc_shadow_range; unfold GL_PHI in *; lia ]. }
rewrite Z.add_0_r in N0.
assert (N16 : val_mem SEGS (arm W1 (ms_mem msB)) (dsp0 cx - DRAIN_FRAME + 16) 8 ((dxSA cx + 48) / 8 + SHADOW_OFF)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 16 32 16 32 16
    (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 48) (SLit 3)) (SOff 35 0)) _ HR1 Usp ltac:(gse_in));
  [ apply gsc_den; apply (gsc_U_shadow E 32 35 (dxSA cx) 48 E32 E35); unfold GL_PHI in *; lia
  | apply gsc_shadow_range; unfold GL_PHI in *; lia ]. }
assert (N24 : val_mem SEGS (arm W1 (ms_mem msB)) (dsp0 cx - DRAIN_FRAME + 24) 8 bg).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 16 32 16 32 24 (SOff 25 0) _ HR1 Usp ltac:(gse_in));
  [ apply (den_atom0 E 25%nat bg E25); lia | lia ]. }
assert (N96 : val_mem SEGS (arm W1 (ms_mem msB)) (dsp0 cx - DRAIN_FRAME + 96) 8 ((dxSA cx + 40) / 8)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 96 104 96 104 96 (SAlu ALU_SRL (SOff 32 40) (SLit 3)) _ HR4 Usp
    ltac:(gse_in));
  [ apply gsc_den; apply (gsc_U_srl E 32 (dxSA cx) 40 E32); unfold GL_PHI in *; lia
  | split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; unfold GL_PHI in *; lia] ]. }
assert (N112 : val_mem SEGS (arm W1 (ms_mem msB)) (dsp0 cx - DRAIN_FRAME + 112) 8 (re_nheld e1)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 112 120 112 120 112 (SOff 34 0) _ HR5 Usp ltac:(gse_in));
  [ apply (den_atom0 E 34%nat (re_nheld e1) E34); lia | lia ]. }
assert (N160 : val_mem SEGS (arm W1 (ms_mem msB)) (dsp0 cx - DRAIN_FRAME + 160) 8 (8 * re_nheld e1)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 160 176 160 176 160
    (SAlu ALU_SLL (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SOff 34 0))) (SOff 34 0)) (SLit 3))
    _ HR6 Usp ltac:(gse_in));
  [ apply gsc_den; apply (gsc_U_nh8 E 34 (re_nheld e1) E34); lia | lia ]. }
assert (N168 : val_mem SEGS (arm W1 (ms_mem msB)) (dsp0 cx - DRAIN_FRAME + 168) 8 1).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 160 176 160 176 168
    (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 33 0) (SLit 7)) (SLit 1)) (SAlu ALU_SLTU (SLit 0) (SOff 33 0)))
    _ HR6 Usp ltac:(gse_in));
  [ apply gsc_den; apply (trap_U_base_ok E (SOff 33 0) (re_hp e1)); [apply (U_atom E 33 (re_hp e1) E33); unfold GL_PHI in *; lia | exact HHP8 | exact Hz]
  | lia ]. }
assert (N192 : val_mem SEGS (arm W1 (ms_mem msB)) (dsp0 cx - DRAIN_FRAME + 192) 8 (Z.of_nat jj)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 192 200 192 200 192
    (SAlu ALU_ADD (SOff 19 0) (SMd M_MUL (SOff 24 0) (SLit (-1)))) _ HR7 Usp ltac:(gse_in));
  [ apply gsc_den; rewrite (gsc_U_sub2 E 24 19 (re_buf e1 + Z.of_nat p) (re_buf e1 + Z.of_nat p + Z.of_nat jj)
      E24' E19' ltac:(lia) ltac:(lia) ltac:(lia)); lia
  | lia ]. }
assert (FR2 : dr_frame RG cx W1 (ms_mem msB)).
{ apply (gsc_frame_keep RG cx W1 m1 (ms_mem msB)); [|exact HFR].
  intros x Hx Hno. apply KEEP2; [lia | exact Hno]. }
pmkst HS.
eapply (LOOP cx s1 D p q 0%nat (length (re_keys e1))); [exact HB | | exact HDLN | exact HGA | exact HGF].
unfold GSL.
exists (ms_regs msB), ly1, S1, (ms_mem msB). eexists. eexists.
exists e1, h1, out1, ev1, LB1, spent, jb, aa, oo, ha, ks, tl, kd, jj, bg.
split; [unfold cfg_at; reflexivity|].
unfold GSBODY.
split.
{ unfold dregs_gs.
  split; [unfold spZ; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Hsp|].
  split; [rewrite (HK 3%bv ltac:(cbv; tauto)); exact R3|].
  split; [rewrite (HK 4%bv ltac:(cbv; tauto)); exact R4|].
  split; [rewrite (HK 8%bv ltac:(cbv; tauto)); exact R8|].
  split; [rewrite (HK 9%bv ltac:(cbv; tauto)); exact R9|].
  split; [rewrite (HK 18%bv ltac:(cbv; tauto)); exact R18|].
  exact FR2. }
split; [exact N0|]. split; [exact N16|]. split; [exact N24|]. split; [exact N96|]. split; [exact N112|].
split; [exact N160|]. split; [exact N168|]. split; [exact N192|].
split; [rewrite (HK 23%bv ltac:(cbv; tauto)); exact H23|].
split; [rewrite (HK 24%bv ltac:(cbv; tauto)); exact H24|].
split; [rewrite P19, denot_lit_U, (U_atom E 34 (re_nheld e1) E34) by lia; reflexivity|].
split; [rewrite P20, denot_lit_U, U_lit by lia; reflexivity|].
split; [rewrite P22, denot_lit_U, (U_atom E 33 (re_hp e1) E33) by (unfold GL_PHI in *; lia); reflexivity|].
split; [rewrite P25, denot_lit_U, (trap_U_snez E (SOff 33 0) (re_hp e1)); [reflexivity | apply (U_atom E 33 (re_hp e1) E33); unfold GL_PHI in *; lia | exact Hz]|].
split; [lia|].
split; [unfold re_nheld in Hc; lia|].
split; [intros i Hi; lia|].
split; [exact Hbgr|]. split; [exact Hbgk|]. split; [exact Hband|]. split; [exact Hcap|].
split; [exact Hgest|]. split; [exact Hjjr|].
split; [unfold GSF; split; [exact Hbd|]; split; [exact Hpq|]; split; [exact Hq0|];
  split; [exact Hnz|]; split; [exact Hskp | exact Hlim]|].
split; [|exact HFUT].
apply (gsc_core_kept B MT MMAX RG LAWS HG HGSB HV9 HSD HSM cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl
  _ _ _ HJ4 ltac:(lia) ltac:(lia) HLC HJ).
+ intros x Hx. apply KEEP2; [lia | unfold gsW; lia].
+ exact PRES2.
+ exact FR2.
Qed.

(* ---- the piece: the search stage of image B's GS, Qed against W_drain_gs.v's gs_scan_stmt ---- *)
Theorem pb_gs_scan : gs_scan_stmt B MT MMAX RG.
Proof using LAWS HG ASTRNCMP ASTRLEN ALLOC_TAIL HGSB HV9 HSD HSM.
exact (gs_scan_of_loop (gs_scan_loop B MT MMAX RG LAWS HG ASTRNCMP ASTRLEN ALLOC_TAIL HGSB HV9 HSD HSM)).
Qed.

End c.
End b.
End a.

(* ============================================================================================================
   THE ARx-GENERIC TWIN of this file (image B's DR_x slice D, 2026-10-30; the B twin of lib/A/W_gsscan_scratch.v's
   Section cx at a working branch 50623273289): the stage's set-up over lib/B/W_drain_cx_x.v's Section
   variables (B PST ARx MT RP MMAX RG), the entry's ghost list Hp and budget kr after cx and the cut's own ghost list Hp1
   after S1 (lib/B/W_drain_gs.v's GA_x, lib/B/W_gsscan_cx.v's GSL_x).  Everything above this line is unchanged.
   - The stage calls no allocator rule: the cut's journal, its dbud_x and its trace pass unchanged from DGS_x to GA_x
     (nheld <= 0) and to GSL_x (the held-key loop's head at n = 0).
   - The AR-free names above are CITED (gse_le4_bytes, gse_entry_hp, gse_entry_nheld, the symbolic state gse_* with
     gse_entry, GS_KEPT1 / GS_KEPT2 and the tactics gse_len / gse_rreg / gse_in), with lib/B/W_gsscan_cx.v's AR-free
     names and its _x twins gsc_stack_x / gsc_core_kept_x.
   - The table block's shadow is read off the laws under HP0 (W_journal_x.v range_addressable_of_block_hp0_x).
   - pb_gs_scan_x composes gs_scan_of_loop_x with lib/B/W_gsscan_loop.v's gs_scan_loop_x: lib/B/W_drain_gs.v's
     gs_scan_stmt_x, its statement unchanged. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_sites_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_drain_cx W_drain_cx_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_drain_gs W_gsscan_cx W_gsscan_loop.
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
(* the instance's laws, and HP0 (a Theorem Labs lane's ruling, lib/B/W_journal_x.v Section hp0; lib/A/W_gsscan_scratch.v's HP0) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
(* lib/B/W_drain_cx_x.v's Section c items this stage uses, in that file's order and text *)
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

(* R twin of gs_scan_of_loop_x *)
Theorem gs_scan_of_loop_xR : gs_scan_loop_stmt_xR B PST ARx MT RP MMAX RG R -> gs_scan_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
intros LOOP.
unfold gs_scan_stmt_xR. intros cx Hp kr s1 D p q W1 c1 HB HGS HDLN HGA HGF.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@ASAN_CEIL_range rc) as (HAC & _). unfold ASAN_CEIL in HAC.
assert (HES : ESTACK = 4096) by reflexivity. assert (HDF : DRAIN_FRAME = 352) by reflexivity.
assert (HDS : DRAIN_STK_x = 17008) by reflexivity.
unfold DGS_xR in HGS.
destruct HGS as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & aa & oo & ha & ks
  & tl & kd & jj & bg & Hcfg & Hregs & H23 & H24 & H19 & H26 & H25 & Hbgr & Hbgk & Hband & Hcap & Hgest & Hjjr
  & Hbd & Hpq & Hq0 & Hnz & Hskp & Hlim & HLC & HFUT).
pose proof Hregs as (Hsp & R3 & R4 & R21 & R20 & R22 & R27 & R8 & R9 & R18 & HFR).
pose proof HFR as (F8 & F32 & F40 & F48 & F56 & F64 & F72 & F80 & F88 & F104 & F120 & F128 & F136 & F144 & F152
  & F176 & F184 & F200 & F208 & F216 & F224 & F232 & F240 & Hsaved).
pose proof HLC as HLC'. unfold LCORE_xR in HLC'.
destruct HLC' as (HMEM & HLINK & HSAME & HHIST & HRS & HBUD).
pose proof HMEM as (HJ & Hrom & Hpresk & Hframes & _ & Hgarr & Hawr & HOKX & Hsrc & Hoth & Hgsk & Hout & Hlivout & Hperm).
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof HB as (Hafn & HBx10 & Htbl & HSAlo & HSAhi & HSA8 & Hgarr0 & Hawr0 & Hent0 & HJ4 & HBrest).
destruct (gsc_stack_x B ARx MT RP MMAX RG cx Hp kr HB) as (HSTK1 & HSTK2 & Hal16 & _).
assert (HTB : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | left; reflexivity]).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE HAR HTB) as (HG16 & HG4096 & HGceil & HGia & HGpres & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity). rewrite RQT in HGceil.
unfold ATABLE, AENT in *.
pose proof HOKX as (Heof & Hskipe & Hpad1 & Hpad2 & Hfd & Hcapr & HUlen & Husedr & Hbufc & Hnheld & Hheld & HND1 & HND2 & Hkeys).
(* the journal's stack: the frame is present, hence writable *)
pose proof HJ as (HSTKj & HXOj & (memS & HJi & HAGj) & HOUTj).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRESj & _).
assert (WRF : forall x, dsp0 cx - DRAIN_STK_x <= x < dsp0 cx -> writable_at SEGS (arm W1 m1) x)
  by (intros x Hx; apply (apresent_writable SEGS); apply HPRESj; lia).
(* the two cells the search reads off the relay entry *)
assert (HHPR : 0 <= re_hp e1 <= GL_PHI).
{ destruct Hheld as [(Hz & _)|(Hz & Hin & Hk1 & Hk2 & _)]; [unfold GL_PHI; lia|].
  destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (re_hp e1) (re_kh e1) HAR Hin) as (_ & H4 & Hc & _).
  pose proof (req_size_pos (re_kh e1) ltac:(lia)) as (Hr1 & Hr2). unfold GL_PHI. lia. }
assert (HNHR : 0 <= re_nheld e1 < 2 ^ 26) by (split; [unfold re_nheld; lia | exact Hnheld]).
pose proof (gse_entry_hp W1 m1 (dxSA cx) e1 Hpad1 ltac:(unfold GL_PHI in HHPR; lia) Hgarr) as MHP.
pose proof (gse_entry_nheld W1 m1 (dxSA cx) e1 Hpad1 ltac:(lia) Hgarr) as MNH.
(* the symbolic state at 0x83aa4 *)
pose proof (gse_entry W1 regs1 m1 (dsp0 cx - DRAIN_FRAME) (dxSA cx) (re_hp e1) (re_nheld e1)
  Hsp ltac:(lia) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity)
  ltac:(lia) HSA8 ltac:(unfold GL_PHI; lia) ltac:(lia) HHPR HNHR
  ltac:(intros o Ho; apply WRF; unfold gsW in Ho; lia)
  F32 F88 F240 MHP MNH) as HS.
remember (Eimg (Ereg regs1 (gse_extra (dxSA cx) (re_hp e1) (re_nheld e1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (gse_extra (dxSA cx) (re_hp e1) (re_nheld e1))) E)
  by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EREG : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 (dxSA cx)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (re_hp e1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (re_nheld e1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 3)).
assert (HBx : U E gse_Bx = SHADOW_OFF)
  by (unfold gse_Bx; rewrite (U_atom E 35 SHADOW_OFF E35) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok SEGS gse_Bx gse_SH E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W1) m1 E gse_Bx 32 (dxG cx) 896 (dxSA cx) 40 56).
  - apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 m1 md1 (dxG cx) 896);
      [exact HAR | exact HTB | lia | rewrite RQT; lia].
  - exact HBx.
  - apply (U_atom E 32 (dxSA cx) E32). unfold GL_PHI in *. lia.
  - lia.
  - lia.
  - intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. rewrite RQT in HGia.
    unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *. lia. }
clear HE.
subst c1. unfold cfg_at. change (w64 (BASE + A_dr_seen)) with (Z_to_bv 64 (BASE + A_dr_seen)).
assert (Usp : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME)
  by (rewrite (EREG 2%nat 2%bv ltac:(lia) eq_refl); exact Hsp).
(* the write obligation: the six windows lie in drain's frame *)
paj_run_tok_xR RUNR HS HJ SHOK gl_Bspan.
{ apply awr_ok_x_of0; awr_ok_tac;
  repeat (eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (- DRAIN_FRAME));
          [ reflexivity
          | rewrite Usp; unfold DRAIN_FRAME; lia
          | cbn [YP09.r_wlo]; unfold DRAIN_FRAME; lia
          | cbn [YP09.r_whi]; unfold DRAIN_FRAME; lia
          | awr_ok_tac ]). }
match goal with Hg : mem_grows (mrestrict (w_H W1) m1) (mrestrict (w_H W1) (ms_mem ?mx)) |- _ =>
  rename Hg into GR1; rename mx into msA end.
match goal with Hf : frame_of _ _ (mrestrict (w_H W1) m1) (mrestrict (w_H W1) (ms_mem msA)) |- _ => rename Hf into HFr1 end.
(* the run wrote only the windows *)
assert (KEEP1 : forall x, 0 <= x < 2 ^ 64 -> ~ gsW (x - (dsp0 cx - DRAIN_FRAME)) ->
  aview SEGS (w_H W1) (ms_mem msA) x = aview SEGS (w_H W1) m1 x).
{ intros x Hx Hno. apply (aview_kept_out E _ (w_H W1) m1 (ms_mem msA) HFr1 x Hx).
  intros (r & Hri & Hr). cbn [ss_mem ss_gse gse_regions In] in Hri.
  repeat (destruct Hri as [<- | Hri];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; apply Hno; unfold gsW; lia |]).
  destruct Hri. }
assert (PRES1 : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msA) x)
  by (intros x Hpx; exact (apresent_grows _ _ _ _ GR1 Hpx)).
clear HFr1 GR1.
assert (E25 : ew E 25 = Z_to_bv 64 bg) by (rewrite (EREG 25%nat 25%bv ltac:(lia) eq_refl); exact H25).
assert (HUW : bzs (re_U e1) = dW s1)
  by (destruct HLINK as (_ & HU & _); unfold dvirt in HU; cbn [drain_b_c.ds_u] in HU; exact HU).
assert (HWlen : Z.of_nat (length (dW s1)) = re_used e1) by (rewrite <- HUW, gsc_bzs_len; exact HUlen).
assert (HBUF : In (re_buf e1, re_cap e1) (ablocks B ly1 S1) /\ 0 < re_cap e1).
{ destruct Hbufc as [(Hc0 & Hb0 & Hu0)|(Hcpos & Hbin & Hjunk & Hbuf8)]; [exfalso; lia | split; assumption]. }
destruct HBUF as (HBin & HBcap).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (re_buf e1) (re_cap e1) HAR HBin) as (_ & HB4096 & HBceil & _).
assert (RQB : req_size (re_cap e1) = re_cap e1) by (unfold req_size; destruct (Z.eqb_spec (re_cap e1) 0); lia).
rewrite RQB in HBceil.
assert (HLINE : 0 <= re_buf e1 + Z.of_nat p /\ re_buf e1 + Z.of_nat p + Z.of_nat jj < 2 ^ 63).
{ split; [lia|]. assert (Z.of_nat q < re_used e1) by lia. lia. }
destruct HLINE as (HL1 & HL2).
assert (E24' : ew E 24 = Z_to_bv 64 (re_buf e1 + Z.of_nat p))
  by (rewrite (EREG 24%nat 24%bv ltac:(lia) eq_refl); exact H24).
assert (E19' : ew E 19 = Z_to_bv 64 (re_buf e1 + Z.of_nat p + Z.of_nat jj))
  by (rewrite (EREG 19%nat 19%bv ltac:(lia) eq_refl); exact H19).
psrr_branch_tok RUNR BRR HS SHOK gl_Bspan.
-
(* nheld <= 0: nothing is held, so the key is not held; on to GA_xR (0x83ba0) *)
rewrite (gsc_bge0 E 34 (re_nheld e1) E34 ltac:(lia)) in Hc.
apply Z.leb_le in Hc.
assert (HN0 : re_nheld e1 = 0) by lia.
assert (HKE : re_keys e1 = []) by (apply length_zero_iff_nil; unfold re_nheld in HN0; lia).
paj_run_to_tok_xR RUNTOR HS HJ SHOK gl_Bspan A_dr_add.
{ apply awr_ok_x_of0; awr_ok_tac;
  repeat (eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (- DRAIN_FRAME));
          [ reflexivity
          | rewrite Usp; unfold DRAIN_FRAME; lia
          | cbn [YP09.r_wlo]; unfold DRAIN_FRAME; lia
          | cbn [YP09.r_whi]; unfold DRAIN_FRAME; lia
          | awr_ok_tac ]). }
match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem msA)) (mrestrict (w_H W1) (ms_mem ?mx)) |- _ =>
  rename Hg into GR2; rename mx into msB end.
match goal with Hf : frame_of _ _ (mrestrict (w_H W1) (ms_mem msA)) (mrestrict (w_H W1) (ms_mem msB)) |- _ => rename Hf into HFr2 end.
assert (KEEP2 : forall x, 0 <= x < 2 ^ 64 -> ~ gsW (x - (dsp0 cx - DRAIN_FRAME)) ->
  aview SEGS (w_H W1) (ms_mem msB) x = aview SEGS (w_H W1) m1 x).
{ intros x Hx Hno. rewrite <- (KEEP1 x Hx Hno).
  apply (aview_kept_out E _ (w_H W1) (ms_mem msA) (ms_mem msB) HFr2 x Hx).
  intros (r & Hri & Hr). cbn [ss_mem add_cond add_atom ss_gse gse_regions In] in Hri.
  repeat (destruct Hri as [<- | Hri];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; apply Hno; unfold gsW; lia |]).
  destruct Hri. }
assert (PRES2 : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msB) x)
  by (intros x Hpx; exact (apresent_grows _ _ _ _ GR2 (PRES1 x Hpx))).
pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ GS_KEPT1 HS HAE ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
(* the window slots the run wrote *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_region_nth Ev ssv msv 1 _ HS eq_refl) as HR1;
  pose proof (st_ok_pi_region_nth Ev ssv msv 4 _ HS eq_refl) as HR4;
  pose proof (st_ok_pi_region_nth Ev ssv msv 5 _ HS eq_refl) as HR5;
  pose proof (st_ok_pi_region_nth Ev ssv msv 7 _ HS eq_refl) as HR7 end.
cbn [ms_mem restrict] in HR1, HR4, HR5, HR7.
assert (N16 : val_mem SEGS (arm W1 (ms_mem msB)) (dsp0 cx - DRAIN_FRAME + 16) 8 ((dxSA cx + 48) / 8 + SHADOW_OFF)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 16 32 16 32 16
    (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 48) (SLit 3)) (SOff 35 0)) _ HR1 Usp ltac:(gse_in));
  [ apply gsc_den; apply (gsc_U_shadow E 32 35 (dxSA cx) 48 E32 E35); unfold GL_PHI in *; lia
  | apply gsc_shadow_range; unfold GL_PHI in *; lia ]. }
assert (N24 : val_mem SEGS (arm W1 (ms_mem msB)) (dsp0 cx - DRAIN_FRAME + 24) 8 bg).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 16 32 16 32 24 (SOff 25 0) _ HR1 Usp ltac:(gse_in));
  [ apply (den_atom0 E 25%nat bg E25); lia | lia ]. }
assert (N96 : val_mem SEGS (arm W1 (ms_mem msB)) (dsp0 cx - DRAIN_FRAME + 96) 8 ((dxSA cx + 40) / 8)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 96 104 96 104 96 (SAlu ALU_SRL (SOff 32 40) (SLit 3)) _ HR4 Usp
    ltac:(gse_in));
  [ apply gsc_den; apply (gsc_U_srl E 32 (dxSA cx) 40 E32); unfold GL_PHI in *; lia
  | split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; unfold GL_PHI in *; lia] ]. }
assert (N112 : val_mem SEGS (arm W1 (ms_mem msB)) (dsp0 cx - DRAIN_FRAME + 112) 8 (re_nheld e1)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 112 120 112 120 112 (SOff 34 0) _ HR5 Usp ltac:(gse_in));
  [ apply (den_atom0 E 34%nat (re_nheld e1) E34); lia | lia ]. }
assert (N192 : val_mem SEGS (arm W1 (ms_mem msB)) (dsp0 cx - DRAIN_FRAME + 192) 8 (Z.of_nat jj)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 192 200 192 200 192
    (SAlu ALU_ADD (SOff 19 0) (SMd M_MUL (SOff 24 0) (SLit (-1)))) _ HR7 Usp ltac:(gse_in));
  [ apply gsc_den; rewrite (gsc_U_sub2 E 24 19 (re_buf e1 + Z.of_nat p) (re_buf e1 + Z.of_nat p + Z.of_nat jj)
      E24' E19' ltac:(lia) ltac:(lia) ltac:(lia)); lia
  | lia ]. }
assert (FR2 : dr_frame RG cx W1 (ms_mem msB)).
{ apply (gsc_frame_keep RG cx W1 m1 (ms_mem msB)); [|exact HFR].
  intros x Hx Hno. apply KEEP2; [lia | exact Hno]. }
assert (HdlH : dlH cx s1 p = []).
{ destruct HLINK as (_ & _ & _ & HKT & _). unfold dvirt in HKT. cbn [drain_b_c.ds_H] in HKT.
  rewrite <- HKT, HKE. reflexivity. }
pmkst HS.
apply HGA. unfold GA_xR.
exists (ms_regs msB), ly1, S1, Hp1, (ms_mem msB). eexists. eexists.
exists e1, h1, out1, ev1, LB1, spent, jb, aa, oo, ha, ks, tl, kd, jj, bg.
split; [unfold cfg_at; reflexivity|].
split.
{ unfold dregs_gs.
  split; [unfold spZ; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Hsp|].
  split; [rewrite (HK 3%bv ltac:(cbv; tauto)); exact R3|].
  split; [rewrite (HK 4%bv ltac:(cbv; tauto)); exact R4|].
  split; [rewrite (HK 8%bv ltac:(cbv; tauto)); exact R8|].
  split; [rewrite (HK 9%bv ltac:(cbv; tauto)); exact R9|].
  split; [rewrite (HK 18%bv ltac:(cbv; tauto)); exact R18|].
  exact FR2. }
split; [rewrite (HK 27%bv ltac:(cbv; tauto)); exact R27|].
split; [rewrite (HK 23%bv ltac:(cbv; tauto)); exact H23|].
split; [rewrite (HK 24%bv ltac:(cbv; tauto)); exact H24|].
split; [exact N16|]. split; [exact N24|]. split; [exact N96|]. split; [exact N112|]. split; [exact N192|].
split; [exact Hbgr|]. split; [exact Hbgk|]. split; [exact Hband|]. split; [exact Hcap|].
split; [exact Hgest|]. split; [exact Hjjr|].
split; [rewrite HdlH; reflexivity|].
split; [unfold GSF; split; [exact Hbd|]; split; [exact Hpq|]; split; [exact Hq0|];
  split; [exact Hnz|]; split; [exact Hskp | exact Hlim]|].
split; [|exact HFUT].
apply (gsc_core_kept_xR B PST ARx MT RP MMAX RG LAWS HG HGSB HV9 HSD HSM R cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1
  h1 out1 ev1 LB1 spent tl _ _ _ HJ4 ltac:(lia) ltac:(lia) HLC HJ).
+ intros x Hx. apply KEEP2; [lia | unfold gsW; lia].
+ exact PRES2.
+ exact FR2.
-
(* nheld > 0: the shadow check of &e->hp, the loop's seat, to 0x83b34 with n = 0 *)
rewrite (gsc_bge0 E 34 (re_nheld e1) E34 ltac:(lia)) in Hc.
apply Z.leb_gt in Hc.
destruct Hheld as [(Hz & Hk0)|(Hz & Hin & Hk1 & Hk2 & Hg8)]; [exfalso; unfold re_nheld in Hc; rewrite Hk0 in Hc; cbn in Hc; lia|].
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (re_hp e1) (re_kh e1) HAR Hin) as (HH16 & HH4096 & _).
assert (HHP8 : re_hp e1 mod 8 = 0).
{ rewrite (Z.div_mod (re_hp e1) 16) by lia. rewrite HH16, Z.add_0_r.
  replace (16 * (re_hp e1 / 16)) with ((2 * (re_hp e1 / 16)) * 8) by lia. apply Z.mod_mul. lia. }
paj_run_to_tok_xR RUNTOR HS HJ SHOK gl_Bspan A_dr_hloop.
{ apply awr_ok_x_of0; awr_ok_tac;
  repeat (eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (- DRAIN_FRAME));
          [ reflexivity
          | rewrite Usp; unfold DRAIN_FRAME; lia
          | cbn [YP09.r_wlo]; unfold DRAIN_FRAME; lia
          | cbn [YP09.r_whi]; unfold DRAIN_FRAME; lia
          | awr_ok_tac ]). }
gse_rreg HS (19%bv : bv 5) P19. gse_rreg HS (20%bv : bv 5) P20.
gse_rreg HS (22%bv : bv 5) P22. gse_rreg HS (25%bv : bv 5) P25.
match goal with Hg : mem_grows (mrestrict (w_H W1) (ms_mem msA)) (mrestrict (w_H W1) (ms_mem ?mx)) |- _ =>
  rename Hg into GR2; rename mx into msB end.
match goal with Hf : frame_of _ _ (mrestrict (w_H W1) (ms_mem msA)) (mrestrict (w_H W1) (ms_mem msB)) |- _ => rename Hf into HFr2 end.
assert (KEEP2 : forall x, 0 <= x < 2 ^ 64 -> ~ gsW (x - (dsp0 cx - DRAIN_FRAME)) ->
  aview SEGS (w_H W1) (ms_mem msB) x = aview SEGS (w_H W1) m1 x).
{ intros x Hx Hno. rewrite <- (KEEP1 x Hx Hno).
  apply (aview_kept_out E _ (w_H W1) (ms_mem msA) (ms_mem msB) HFr2 x Hx).
  intros (r & Hri & Hr). cbn [ss_mem add_cond add_atom ss_gse gse_regions In] in Hri.
  repeat (destruct Hri as [<- | Hri];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; apply Hno; unfold gsW; lia |]).
  destruct Hri. }
assert (PRES2 : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msB) x)
  by (intros x Hpx; exact (apresent_grows _ _ _ _ GR2 (PRES1 x Hpx))).
pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ GS_KEPT2 HS HAE ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
(* the eight window slots the setup wrote *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_region_nth Ev ssv msv 0 _ HS eq_refl) as HR0;
  pose proof (st_ok_pi_region_nth Ev ssv msv 1 _ HS eq_refl) as HR1;
  pose proof (st_ok_pi_region_nth Ev ssv msv 4 _ HS eq_refl) as HR4;
  pose proof (st_ok_pi_region_nth Ev ssv msv 5 _ HS eq_refl) as HR5;
  pose proof (st_ok_pi_region_nth Ev ssv msv 6 _ HS eq_refl) as HR6;
  pose proof (st_ok_pi_region_nth Ev ssv msv 7 _ HS eq_refl) as HR7 end.
cbn [ms_mem restrict] in HR0, HR1, HR4, HR5, HR6, HR7.
assert (N0 : val_mem SEGS (arm W1 (ms_mem msB)) (dsp0 cx - DRAIN_FRAME + 0) 8 ((dxSA cx + 40) / 8 + SHADOW_OFF)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 0 8 0 8 0
    (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 40) (SLit 3)) (SOff 35 0)) _ HR0 Usp ltac:(gse_in));
  [ apply gsc_den; apply (gsc_U_shadow E 32 35 (dxSA cx) 40 E32 E35); unfold GL_PHI in *; lia
  | apply gsc_shadow_range; unfold GL_PHI in *; lia ]. }
rewrite Z.add_0_r in N0.
assert (N16 : val_mem SEGS (arm W1 (ms_mem msB)) (dsp0 cx - DRAIN_FRAME + 16) 8 ((dxSA cx + 48) / 8 + SHADOW_OFF)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 16 32 16 32 16
    (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 48) (SLit 3)) (SOff 35 0)) _ HR1 Usp ltac:(gse_in));
  [ apply gsc_den; apply (gsc_U_shadow E 32 35 (dxSA cx) 48 E32 E35); unfold GL_PHI in *; lia
  | apply gsc_shadow_range; unfold GL_PHI in *; lia ]. }
assert (N24 : val_mem SEGS (arm W1 (ms_mem msB)) (dsp0 cx - DRAIN_FRAME + 24) 8 bg).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 16 32 16 32 24 (SOff 25 0) _ HR1 Usp ltac:(gse_in));
  [ apply (den_atom0 E 25%nat bg E25); lia | lia ]. }
assert (N96 : val_mem SEGS (arm W1 (ms_mem msB)) (dsp0 cx - DRAIN_FRAME + 96) 8 ((dxSA cx + 40) / 8)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 96 104 96 104 96 (SAlu ALU_SRL (SOff 32 40) (SLit 3)) _ HR4 Usp
    ltac:(gse_in));
  [ apply gsc_den; apply (gsc_U_srl E 32 (dxSA cx) 40 E32); unfold GL_PHI in *; lia
  | split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; unfold GL_PHI in *; lia] ]. }
assert (N112 : val_mem SEGS (arm W1 (ms_mem msB)) (dsp0 cx - DRAIN_FRAME + 112) 8 (re_nheld e1)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 112 120 112 120 112 (SOff 34 0) _ HR5 Usp ltac:(gse_in));
  [ apply (den_atom0 E 34%nat (re_nheld e1) E34); lia | lia ]. }
assert (N160 : val_mem SEGS (arm W1 (ms_mem msB)) (dsp0 cx - DRAIN_FRAME + 160) 8 (8 * re_nheld e1)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 160 176 160 176 160
    (SAlu ALU_SLL (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) (SOff 34 0))) (SOff 34 0)) (SLit 3))
    _ HR6 Usp ltac:(gse_in));
  [ apply gsc_den; apply (gsc_U_nh8 E 34 (re_nheld e1) E34); lia | lia ]. }
assert (N168 : val_mem SEGS (arm W1 (ms_mem msB)) (dsp0 cx - DRAIN_FRAME + 168) 8 1).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 160 176 160 176 168
    (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 33 0) (SLit 7)) (SLit 1)) (SAlu ALU_SLTU (SLit 0) (SOff 33 0)))
    _ HR6 Usp ltac:(gse_in));
  [ apply gsc_den; apply (trap_U_base_ok E (SOff 33 0) (re_hp e1)); [apply (U_atom E 33 (re_hp e1) E33); unfold GL_PHI in *; lia | exact HHP8 | exact Hz]
  | lia ]. }
assert (N192 : val_mem SEGS (arm W1 (ms_mem msB)) (dsp0 cx - DRAIN_FRAME + 192) 8 (Z.of_nat jj)).
{ apply (slot_of_region E _ (dsp0 cx - DRAIN_FRAME) _ 192 200 192 200 192
    (SAlu ALU_ADD (SOff 19 0) (SMd M_MUL (SOff 24 0) (SLit (-1)))) _ HR7 Usp ltac:(gse_in));
  [ apply gsc_den; rewrite (gsc_U_sub2 E 24 19 (re_buf e1 + Z.of_nat p) (re_buf e1 + Z.of_nat p + Z.of_nat jj)
      E24' E19' ltac:(lia) ltac:(lia) ltac:(lia)); lia
  | lia ]. }
assert (FR2 : dr_frame RG cx W1 (ms_mem msB)).
{ apply (gsc_frame_keep RG cx W1 m1 (ms_mem msB)); [|exact HFR].
  intros x Hx Hno. apply KEEP2; [lia | exact Hno]. }
pmkst HS.
eapply (LOOP cx Hp kr s1 D p q 0%nat (length (re_keys e1))); [exact HB | | exact HDLN | exact HGA | exact HGF].
unfold GSL_xR.
exists (ms_regs msB), ly1, S1, Hp1, (ms_mem msB). eexists. eexists.
exists e1, h1, out1, ev1, LB1, spent, jb, aa, oo, ha, ks, tl, kd, jj, bg.
split; [unfold cfg_at; reflexivity|].
unfold GSBODY_xR.
split.
{ unfold dregs_gs.
  split; [unfold spZ; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Hsp|].
  split; [rewrite (HK 3%bv ltac:(cbv; tauto)); exact R3|].
  split; [rewrite (HK 4%bv ltac:(cbv; tauto)); exact R4|].
  split; [rewrite (HK 8%bv ltac:(cbv; tauto)); exact R8|].
  split; [rewrite (HK 9%bv ltac:(cbv; tauto)); exact R9|].
  split; [rewrite (HK 18%bv ltac:(cbv; tauto)); exact R18|].
  exact FR2. }
split; [exact N0|]. split; [exact N16|]. split; [exact N24|]. split; [exact N96|]. split; [exact N112|].
split; [exact N160|]. split; [exact N168|]. split; [exact N192|].
split; [rewrite (HK 23%bv ltac:(cbv; tauto)); exact H23|].
split; [rewrite (HK 24%bv ltac:(cbv; tauto)); exact H24|].
split; [rewrite P19, denot_lit_U, (U_atom E 34 (re_nheld e1) E34) by lia; reflexivity|].
split; [rewrite P20, denot_lit_U, U_lit by lia; reflexivity|].
split; [rewrite P22, denot_lit_U, (U_atom E 33 (re_hp e1) E33) by (unfold GL_PHI in *; lia); reflexivity|].
split; [rewrite P25, denot_lit_U, (trap_U_snez E (SOff 33 0) (re_hp e1)); [reflexivity | apply (U_atom E 33 (re_hp e1) E33); unfold GL_PHI in *; lia | exact Hz]|].
split; [lia|].
split; [unfold re_nheld in Hc; lia|].
split; [intros i Hi; lia|].
split; [exact Hbgr|]. split; [exact Hbgk|]. split; [exact Hband|]. split; [exact Hcap|].
split; [exact Hgest|]. split; [exact Hjjr|].
split; [unfold GSF; split; [exact Hbd|]; split; [exact Hpq|]; split; [exact Hq0|];
  split; [exact Hnz|]; split; [exact Hskp | exact Hlim]|].
split; [|exact HFUT].
apply (gsc_core_kept_xR B PST ARx MT RP MMAX RG LAWS HG HGSB HV9 HSD HSM R cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1
  h1 out1 ev1 LB1 spent tl _ _ _ HJ4 ltac:(lia) ltac:(lia) HLC HJ).
+ intros x Hx. apply KEEP2; [lia | unfold gsW; lia].
+ exact PRES2.
+ exact FR2.
Qed.

(* R twin of pb_gs_scan_x *)
Theorem pb_gs_scan_xR : gs_scan_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
apply gs_scan_of_loop_xR.
exact (gs_scan_loop_xR B PST ARx MT RP MMAX RG LAWS HP0 HG ASTRNCMP ASTRLEN HGSB HV9 HSD HSM R R_trans WLE_R).
Qed.

End wR.

(* commit (2): each strict lemma below is its R twin at R := wle (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) section 0) *)
Local Ltac wle_inst := first [ eassumption | intros ? ? H; exact H | intros ?; apply wle_refl
  | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] ].

(* The stage over ARx, given the held-search loop over ARx (lib/B/W_gsscan_cx.v gs_scan_loop_stmt_x). *)
Theorem gs_scan_of_loop_x : gs_scan_loop_stmt_x B PST ARx MT RP MMAX RG -> gs_scan_stmt_x B PST ARx MT RP MMAX RG.
Proof. eapply (gs_scan_of_loop_xR (@wle SEGS)); wle_inst. Qed.

(* ---- the piece over ARx: the search stage of image B's GS, Qed against lib/B/W_drain_gs.v's gs_scan_stmt_x ---- *)
Theorem pb_gs_scan_x : gs_scan_stmt_x B PST ARx MT RP MMAX RG.
Proof. eapply (pb_gs_scan_xR (@wle SEGS)); wle_inst. Qed.

End cx.
End bx.
End ax.
