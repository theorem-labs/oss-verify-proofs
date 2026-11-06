(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the GS-ADD arm of segment GS of the ASan walk of fuzz_reply's drain
   (fuzz_reply.asan 0x8389c .. 0x839b8, relay.c:112-118 inlined), in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v (allocator call sites) and of this lane's W_lp_tail-shaped
   W_drain_pro.v / W_send_line_entry.v.  The statement is lib/A/W_drain_gs.v's gs_add_stmt; the Section
   header below is lib/A/W_drain_cx.v's, verbatim.

   GA (0x8389c) -> DLN (S q) (0x836f4), in two arms:
     bnez s3  (s3 = bg <> 0)  an END whose key is not held: nothing changes, straight to DLN (S q);
     bg = 0                   a BEGIN not held: realloc(s->held, 8 * nheld + 8) at 0x838c0,
                              s->held = res (0x838d4), strndup(line, last - line) at 0x838e0,
                              s->nheld = nheld + 1 (0x83914), s->held[nheld] = copy (0x839b4),
                              then DLN (S q).
   The `bne a0, a1` at 0x838a0 is never taken (both hold s->nheld, pinned to one atom); the four shadow
   checks (0x838a8, 0x838c8, 0x838e8 of &s->held, 0x838f4 of &s->nheld, 0x83924 of the new slot) read a
   zero byte, so no __asan_report_* arm opens. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep gestures_end_b_c RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
send_line_c send_line_b_c RelayRunT RelayRunF ListTr drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_rebase W_sites W_contract W_frame W_drain_model W_send_line_cx
W_drain_cx W_drain_gs W_drain_tr W_gsaddb_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_tr_peak.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Notation dtrace := (list (RelayRunT.rev YO0i.sptr)).
#[local] Notation dadrF := (RelayRunT.addr YO0i.sptr).
#[local] Notation dnret := (RelayRunT.nret YO0i.sptr).

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
(* the instance's laws *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
(* the runtime entries drain calls, at their SIGMA pcs *)
Hypothesis AERRNO : aerrno_realizes B (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM SEGS B 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes B (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes B (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes B (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes B (SIGMA WS_strlen).
(* the allocator's site rules (W_journal.v), at the trampolines the program calls *)
Hypothesis AREALLOC : arealloc_cf_rule SEGS B MT MMAX (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule SEGS B MT.
Hypothesis ASTRNDUP : astrndup_cf_rule SEGS B MT MMAX (SIGMA WS_strndup).
Hypothesis ALLOC_TAIL : forall ly S W mem md p n a,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
(* the callees drain calls as a program *)
Hypothesis SLSPEC : sl_spec B MT MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
(* instance facts *)
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 22) = rg_s RG.
Hypothesis HLIT5 : dlit_at B 21 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at B 23 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at B 24 (W_END ++ [0]).
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 21), VAL (A_OBJ 21) + 14); (VAL (A_OBJ 23), VAL (A_OBJ 23) + 6); (VAL (A_OBJ 24), VAL (A_OBJ 24) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= 0x5fb000 /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.
Let RUN := paj_run_x B LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* ============================================================================================
   (1) THE ENTRY SEAT at GA (0x8389c).
   Atoms 0 .. 31 are the registers at the cut; atom 21 is the shadow base (dregs_line pins s5 to
   SHADOW_OFF), atom 22 the relay entry's address SA (dregs_line pins s6), atom 10 s->nheld (GA pins
   a0 and a1), atom 32 (the one extra) s->held.  a1 is SEATED AS ATOM 10 as well, so that the
   `bne a0, a1` at 0x838a0 is decided statically; a2 is seated as `(SA + 40) >> 3`, so that the
   `add s3, a2, s5` at 0x838a4 is YCbn's match_x form and the `lbu` reads a covered shadow byte.
   Two regions: the frame's three constant slots (72 / 96 / 128, read-only here) and the relay
   entry's 56 bytes with the two cells this arm writes as its window.  The frame slot 72 holds the
   SHADOW ADDRESS of &s->nheld as a match_x form, not a flat atom, or the walk stops at 0x838f4. *)
Definition gaBx : sv := SOff 21 0.
Definition gaBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition GA_HI : Z := 140737479966720.   (* a literal for ASAN_CEIL's ceiling: the abstract one hangs vm_compute *)

Definition ga_frame : YP09.region :=
YP09.mkRegion (Some 2%nat) 72 136 72 72
[YP09.mkChunk 72 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 22 48) (SLit 3)) (SOff 21 0)));
 YP09.mkChunk 96 (CVal 8 (SOff 22 48));
 YP09.mkChunk 128 (CVal 8 (SOff 22 40))].
Definition ga_ent : YP09.region :=
YP09.mkRegion (Some 22%nat) 0 56 40 52
[YP09.mkChunk 40 (CVal 8 (SOff 32 0)); YP09.mkChunk 48 (CVal 4 (SOff 10 0))].
Definition ga_regions : smem := [ga_frame; ga_ent].
Definition ga_facts : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 0 (2 ^ 26) 0);
          (21%nat, mkAF SB SB 0); (22%nat, mkAF 4096 GA_HI 0); (32%nat, mkAF 0 GA_HI 0) ] [] [].
Definition ga_regs : list sv :=
sr_set (sr_set sr_atoms 11%bv (SOff 10 0)) 12%bv (SAlu ALU_SRL (SOff 22 40) (SLit 3)).
Definition ss_ga : sstate := mkSS A_dr_add ga_regs ga_regions None ga_facts.
Definition ga_SH : list shent := [ mkSHE 22 0 56 ].
Definition ga_extra (hp : Z) : list word := [Z_to_bv 64 hp].

(* ---- small env helpers (the shapes every chunk and every register seat needs) ---- *)
Lemma ga_regs_ok_set : forall E sr regs (r : bv 5) e,
regs_ok E sr regs -> sv_denot E e = getr regs r -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e Hr Hv r'. unfold sr_set. destruct (bv_eqb r 0) eqn:Hr0; [apply Hr|].
specialize (Hr r'). unfold sr_get in *. destruct (bv_eqb r' 0) eqn:Hr'0; [exact Hr|].
rewrite nth_sr_upd. destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi; [|exact Hr].
apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. symmetry. exact Hv.
Qed.
Lemma ga_den_of_U : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v <-. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma ga_U_add : forall E x y, 0 <= U E x + U E y < 2 ^ 64 -> U E (SAlu ALU_ADD x y) = U E x + U E y.
Proof.
intros E x y H. rewrite U_SAlu. cbn [zalu_raw]. apply zcanon_id. unfold M64. lia.
Qed.
Lemma ga_den_srl3 : forall E n v c, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
U E (SAlu ALU_SRL (SOff n c) (SLit 3)) = (v + c) / 8.
Proof. intros E n v c Hn Hv Hc. rewrite U_srl3, (U_atom_off E n v c Hn Hv Hc). reflexivity. Qed.
Lemma ga_U_sll3_add8 : forall E n v, ew E n = w64 v -> 0 <= v < 2 ^ 26 ->
U E (SAlu ALU_ADD (SAlu ALU_SLL (SOff n 0) (SLit 3)) (SLit 8)) = 8 * v + 8.
Proof.
intros E n v Hn Hv.
assert (Hav : U E (SOff n 0) = v) by (apply (U_atom E n v Hn); lia).
rewrite !U_SAlu. cbn [zalu_raw]. rewrite Hav, !U_SLit.
replace (Z.land (zcanon 3) 63) with 3 by (vm_compute; reflexivity).
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
unfold zcanon, M64.
rewrite (Z.mod_small (v * 8)) by lia.
replace (8 mod 2 ^ 64) with 8 by (vm_compute; reflexivity).
rewrite Z.mod_small by lia. lia.
Qed.

(* ---- the seat itself ---- *)
Lemma ga_seat : forall (W1 : world SEGS) regs1 m1 (SA sp hp nh : Z),
getr regs1 2 = w64 sp ->
getr regs1 10 = w64 nh -> getr regs1 11 = w64 nh -> getr regs1 12 = w64 ((SA + 40) / 8) ->
getr regs1 21 = w64 SHADOW_OFF -> getr regs1 22 = w64 SA ->
4096 <= SA -> SA + 56 <= GA_HI -> SA + 56 + 16512 <= sp -> 0 <= hp <= GA_HI -> 0 <= nh <= 2 ^ 26 ->
2 ^ 46 <= sp -> sp + 336 <= 2 ^ 47 -> sp mod 16 = 0 ->
val_mem SEGS (arm W1 m1) (sp + 72) 8 ((SA + 48) / 8 + SHADOW_OFF) ->
val_mem SEGS (arm W1 m1) (sp + 96) 8 (SA + 48) ->
val_mem SEGS (arm W1 m1) (sp + 128) 8 (SA + 40) ->
val_mem SEGS (arm W1 m1) (SA + 40) 8 hp ->
val_mem SEGS (arm W1 m1) (SA + 48) 4 nh ->
(forall o, 40 <= o < 52 -> writable_at SEGS (arm W1 m1) (SA + o)) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (ga_extra hp))) ss_ga
(restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_dr_add)) m1 (seg_rom SEGS))).
Proof.
intros W1 regs1 m1 SA sp hp nh R2 R10 R11 R12 R21 R22 HSAlo HSAhi HSAsp Hhp Hnh Hsplo Hsphi Hsp16
  V72 V96 V128 V40 V48 HW.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs1 (ga_extra hp))).
assert (E2 : ew E 2 = w64 sp)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl); exact R2).
assert (E10 : ew E 10 = w64 nh)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 10 10%bv eq_refl); exact R10).
assert (E21 : ew E 21 = w64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 21 21%bv eq_refl); exact R21).
assert (E22 : ew E 22 = w64 SA)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 22 22%bv eq_refl); exact R22).
assert (E32 : ew E 32 = w64 hp)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (Usp : bv_unsigned (ew E 2) = sp) by (rewrite E2; apply unsigned_lit_small; lia).
assert (Usa : bv_unsigned (ew E 22) = SA) by (rewrite E22; apply unsigned_lit_small; unfold GA_HI in *; lia).
assert (Unh : bv_unsigned (ew E 10) = nh) by (rewrite E10; apply unsigned_lit_small; lia).
assert (Ub : bv_unsigned (ew E 21) = SHADOW_OFF) by (rewrite E21; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (Uhp : bv_unsigned (ew E 32) = hp) by (rewrite E32; apply unsigned_lit_small; unfold GA_HI in *; lia).
assert (U21 : U E (SOff 21 0) = SHADOW_OFF) by (apply (U_atom E 21 _ E21); unfold SHADOW_OFF; lia).
assert (HD48 : 0 <= (SA + 48) / 8 <= SA + 48)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HD40 : 0 <= (SA + 40) / 8 <= SA + 40)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (US48 : U E (SAlu ALU_SRL (SOff 22 48) (SLit 3)) = (SA + 48) / 8)
  by (apply (ga_den_srl3 E 22 SA 48 E22); unfold GA_HI in *; lia).
assert (US40 : U E (SAlu ALU_SRL (SOff 22 40) (SLit 3)) = (SA + 40) / 8)
  by (apply (ga_den_srl3 E 22 SA 40 E22); unfold GA_HI in *; lia).
assert (D72 : sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 22 48) (SLit 3)) (SOff 21 0))
            = Z_to_bv 64 ((SA + 48) / 8 + SHADOW_OFF)).
{ apply ga_den_of_U. rewrite ga_U_add by (rewrite US48, U21; unfold SHADOW_OFF, GA_HI in *; lia).
  rewrite US48, U21. reflexivity. }
assert (D96 : sv_denot E (SOff 22 48) = Z_to_bv 64 (SA + 48))
  by (apply ga_den_of_U; exact (U_atom_off E 22 SA 48 E22 ltac:(unfold GA_HI in *; lia) ltac:(unfold GA_HI in *; lia))).
assert (D128 : sv_denot E (SOff 22 40) = Z_to_bv 64 (SA + 40))
  by (apply ga_den_of_U; exact (U_atom_off E 22 SA 40 E22 ltac:(unfold GA_HI in *; lia) ltac:(unfold GA_HI in *; lia))).
assert (D40 : sv_denot E (SOff 32 0) = Z_to_bv 64 hp)
  by (apply ga_den_of_U; exact (U_atom E 32 hp E32 ltac:(unfold GA_HI in *; lia))).
assert (D48 : sv_denot E (SOff 10 0) = Z_to_bv 64 nh)
  by (apply ga_den_of_U; exact (U_atom E 10 nh E10 ltac:(lia))).
unfold ss_ga. apply pa_entry_st_ok_full.
- unfold ga_regs. apply ga_regs_ok_set; [apply ga_regs_ok_set; [apply regs_ok_Eimg_Ereg|]|].
  + rewrite R11. exact D48.
  + rewrite R12. apply ga_den_of_U. exact US40.
- vm_compute. reflexivity.
- unfold ga_regions, ga_frame, ga_ent.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ sp 72 8 _ ((SA + 48) / 8 + SHADOW_OFF));
      [exact D72 | unfold SHADOW_OFF, GA_HI in *; zside | zside | exact V72].
    * apply (chunk_ok_val SEGS E _ sp 96 8 _ (SA + 48)); [exact D96 | unfold GA_HI in *; zside | zside | exact V96].
    * apply (chunk_ok_val SEGS E _ sp 128 8 _ (SA + 40)); [exact D128 | unfold GA_HI in *; zside | zside | exact V128].
  + rewrite Usa. split; [lia|]. split; [unfold GA_HI in *; lia|]. split; [intros o Ho; exact (HW o Ho)|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ SA 40 8 _ hp); [exact D40 | unfold GA_HI in *; zside | zside | exact V40].
    * apply (chunk_ok_val SEGS E _ SA 48 4 _ nh); [exact D48 | zside | zside | exact V48].
- apply pairwise_disjoint_of_extents. unfold ga_regions, ga_frame, ga_ent, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Usa.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [ga_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, Unh, Ub, Usa, Uhp. rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 4) with 16.
  unfold SB, SHADOW_OFF, GA_HI in *. repeat match goal with |- _ /\ _ => split end; lia.
Qed.

(* ---- the shadow entry: the relay entry's 56 bytes sit inside the table block ---- *)
Lemma ga_shok : forall Ex ly S (W : world SEGS) mem md G SA,
AR SEGS B ly S W mem md -> In (G, ATABLE) (ablocks B ly S) -> G <= SA -> SA + AENT <= G + ATABLE ->
ew Ex 21 = w64 SHADOW_OFF -> ew Ex 22 = w64 SA -> 4096 <= SA -> SA + 56 <= GA_HI ->
sh_ok SEGS gaBx ga_SH Ex (mrestrict (w_H W) mem).
Proof.
intros Ex ly S W mem md G SA HAR Hin HGle HSAle E21 E22 HSAlo HSAhi.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks SEGS B LAWS ly S W mem md _ _ HAR Hin) as (_ & H4096 & Hceil & Happ & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
rewrite RQT in Hceil, Happ.
unfold sh_ok, ga_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem Ex gaBx 22 G 896 SA 0 56).
- apply (range_addressable_of_block SEGS B LAWS ly S W mem md G ATABLE);
  [exact HAR | exact Hin | lia | rewrite RQT; lia].
- unfold U, gaBx. cbn [sv_denot]. rewrite E21, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite E22, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold GA_HI in *; lia). reflexivity.
- lia.
- unfold AENT, ATABLE in HSAle. lia.
- intros y Hy. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
  unfold AENT, ATABLE in HSAle. unfold SHADOW_OFF. lia.
Qed.

(* ============================================================================================
   (2) THE BYTE IMAGE of the two cells gesture_seen writes and of the held array's slots.
   RelayRep.v:21 entry_bytes e = le4 fd ++ le4 eof ++ le4 skip ++ pad1 ++ le8 buf ++ le8 used ++
   le8 cap ++ le8 hp ++ le4 nheld ++ pad2, so s->held is at + 40 (8 bytes) and s->nheld at + 48
   (4 bytes); gestures_end_b_c.v:29 key_ptrs is 8 bytes per held key.  (The same text is Qed in the
   lane's W_gsbytes_scratch.v; it is carried here so this file stands alone.) *)
Definition gax_k0 : Z * list byte * list byte := (0, [], []).

Lemma gax_bzs_app : forall l1 l2, bzs (l1 ++ l2) = bzs l1 ++ bzs l2.
Proof. intros l1 l2. unfold bzs. apply map_app. Qed.
Lemma gax_bzs_len : forall l, length (bzs l) = length l.
Proof. intros l. unfold bzs. apply length_map. Qed.
Lemma gax_bz_bv8 : forall x, bz (Z_to_bv 8 x) = x mod 256.
Proof. intros x. unfold bz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. reflexivity. Qed.
Lemma gax_nth_zle : forall n z k d, (k < n)%nat ->
nth k (Z_to_le_bytes n z) d = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k d Hk; [lia|].
cbn [Z_to_le_bytes]. destruct k as [|k].
- cbn [nth]. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
- cbn [nth]. rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.
Lemma gax_nth_le_bytes : forall n v k, (k < n)%nat -> 0 <= v < 2 ^ (8 * Z.of_nat n) ->
nth k (bzs (Z_to_le_bytes n v)) 0 = YO0f.le_byte v n k.
Proof.
intros n v k Hk Hv. unfold bzs.
rewrite (nth_indep (map bz (Z_to_le_bytes n v)) 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_Z_to_le_bytes; exact Hk).
rewrite List.map_nth, gax_nth_zle by exact Hk. rewrite gax_bz_bv8.
unfold YO0f.le_byte. rewrite (Z.mod_small v) by exact Hv. reflexivity.
Qed.
Lemma gax_le_byte1 : forall x, 0 <= x < 256 -> YO0f.le_byte x 1 0 = x.
Proof.
intros x Hx. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !(Z.mod_small x 256) by lia. reflexivity.
Qed.
Lemma gax_garr8_at : forall mem b l b', garr8 SEGS mem b l -> b = b' -> garr8 SEGS mem b' l.
Proof. intros mem b l b' H <-. exact H. Qed.
Lemma gax_garr8_kept : forall (W : world SEGS) m (W' : world SEGS) m' a l,
garr8 SEGS (arm W m) a l ->
(forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W' m') a l.
Proof.
intros W m W' m' a l H K. apply (garr8_frame SEGS (arm W m) (arm W' m') a l H).
intros x Hx. unfold arm. apply (mbyte_of_aview SEGS). exact (K x Hx).
Qed.
Lemma gax_val_of_garr8 : forall (W : world SEGS) m a (n : nat) (v : Z),
0 <= v < 2 ^ (8 * Z.of_nat n) ->
garr8 SEGS (arm W m) a (bzs (Z_to_le_bytes n v)) -> val_mem SEGS (arm W m) a n v.
Proof.
intros W m a n v Hv H k Hk.
assert (Hl : (k < length (bzs (Z_to_le_bytes n v)))%nat) by (rewrite gax_bzs_len, length_Z_to_le_bytes; exact Hk).
rewrite (garr8_mbyte SEGS (arm W m) a _ k H Hl). rewrite gax_nth_le_bytes by assumption. reflexivity.
Qed.
Lemma gax_garr8_of_val : forall (W : world SEGS) m a (n : nat) (v : Z),
0 <= v < 2 ^ (8 * Z.of_nat n) ->
val_mem SEGS (arm W m) a n v -> garr8 SEGS (arm W m) a (bzs (Z_to_le_bytes n v)).
Proof.
intros W m a n v Hv H j Hj.
assert (Hjn : (j < n)%nat) by (rewrite gax_bzs_len, length_Z_to_le_bytes in Hj; exact Hj).
rewrite gax_nth_le_bytes by assumption.
assert (Hr : 0 <= YO0f.le_byte v n j < 256) by (unfold YO0f.le_byte; apply Z.mod_pos_bound; lia).
split; [|exact Hr].
intros k Hk. destruct k as [|k]; [|lia].
cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite (H j Hjn). rewrite gax_le_byte1 by exact Hr. reflexivity.
Qed.
Lemma gax_le8_bytes : forall v, 0 <= v < 2 ^ 64 -> Mem.le8 (Z_to_bv 64 v) = Z_to_le_bytes 8 v.
Proof.
intros v Hv. unfold Mem.le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by exact Hv. reflexivity.
Qed.
Lemma gax_le4_bytes : forall v, 0 <= v < 2 ^ 32 -> Mem.le4 (Z_to_bv 64 v) = Z_to_le_bytes 4 v.
Proof.
intros v Hv. unfold Mem.le4. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. reflexivity.
Qed.
Ltac gax_len := rewrite ?length_app, ?gax_bzs_len, ?Mem.length_le8, ?Mem.length_le4, ?length_Z_to_le_bytes; cbn [length].
Ltac gax_len_in H := rewrite ?length_app, ?gax_bzs_len, ?Mem.length_le8, ?Mem.length_le4, ?length_Z_to_le_bytes in H;
  cbn [length] in H.

Lemma gax_entry_hp : forall (W : world SEGS) m SA e,
length (re_pad1 e) = 4%nat -> 0 <= re_hp e < 2 ^ 64 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) ->
val_mem SEGS (arm W m) (SA + 40) 8 (re_hp e).
Proof.
intros W m SA e Hp1 Hhp H.
unfold entry_bytes in H. rewrite !gax_bzs_app, !app_assoc in H.
apply garr8_app in H as [H _]. apply garr8_app in H as [H _]. apply garr8_app in H as [_ H].
rewrite (gax_le8_bytes (re_hp e) Hhp) in H.
apply (gax_val_of_garr8 W m _ 8 _); [change (8 * Z.of_nat 8) with 64; exact Hhp|].
apply (gax_garr8_at _ _ _ _ H). gax_len. lia.
Qed.
Lemma gax_entry_nheld : forall (W : world SEGS) m SA e,
length (re_pad1 e) = 4%nat -> 0 <= re_nheld e < 2 ^ 32 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) ->
val_mem SEGS (arm W m) (SA + 48) 4 (re_nheld e).
Proof.
intros W m SA e Hp1 Hnh H.
unfold entry_bytes in H. rewrite !gax_bzs_app, !app_assoc in H.
apply garr8_app in H as [H _]. apply garr8_app in H as [_ H].
rewrite (gax_le4_bytes (re_nheld e) Hnh) in H.
apply (gax_val_of_garr8 W m _ 4 _); [change (8 * Z.of_nat 4) with 32; exact Hnh|].
apply (gax_garr8_at _ _ _ _ H). gax_len. lia.
Qed.
Lemma gax_entry_store : forall (W : world SEGS) m (W' : world SEGS) m' SA e e',
length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
re_fd e' = re_fd e -> re_eof e' = re_eof e -> re_skip e' = re_skip e -> re_pad1 e' = re_pad1 e ->
re_buf e' = re_buf e -> re_used e' = re_used e -> re_cap e' = re_cap e -> re_pad2 e' = re_pad2 e ->
0 <= re_hp e' < 2 ^ 64 -> 0 <= re_nheld e' < 2 ^ 32 ->
garr8 SEGS (arm W m) SA (bzs (entry_bytes e)) ->
val_mem SEGS (arm W' m') (SA + 40) 8 (re_hp e') ->
val_mem SEGS (arm W' m') (SA + 48) 4 (re_nheld e') ->
(forall x, SA <= x < SA + 40 -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
(forall x, SA + 52 <= x < SA + 56 -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W' m') SA (bzs (entry_bytes e')).
Proof.
intros W m W' m' SA e e' Hp1 Hp2 Efd Eeof Eskip Ep1 Ebuf Eused Ecap Ep2 Hhp Hnh H Vhp Vnh K1 K2.
unfold entry_bytes in H |- *. rewrite Efd, Eeof, Eskip, Ep1, Ebuf, Eused, Ecap, Ep2.
rewrite !gax_bzs_app, !app_assoc in H |- *.
apply garr8_app in H as [H HP2]. apply garr8_app in H as [H _]. apply garr8_app in H as [HZ _].
rewrite (gax_le8_bytes (re_hp e') Hhp), (gax_le4_bytes (re_nheld e') Hnh).
apply garr8_app. split; [apply garr8_app; split; [apply garr8_app; split|]|].
- apply (gax_garr8_kept W m); [exact HZ|]. intros x Hx. apply K1. gax_len_in Hx. lia.
- apply (gax_garr8_at _ (SA + 40)); [|gax_len; lia].
  apply gax_garr8_of_val; [change (8 * Z.of_nat 8) with 64; exact Hhp | exact Vhp].
- apply (gax_garr8_at _ (SA + 48)); [|gax_len; lia].
  apply gax_garr8_of_val; [change (8 * Z.of_nat 4) with 32; exact Hnh | exact Vnh].
- apply (gax_garr8_at _ (SA + 52)); [|gax_len; lia].
  apply (gax_garr8_kept W m).
  + apply (gax_garr8_at _ _ _ _ HP2). gax_len. lia.
  + intros x Hx. apply K2. gax_len_in Hx. lia.
Qed.
Lemma gax_ptrs_app : forall (W : world SEGS) m (W' : world SEGS) m' hp ks k,
0 <= key_addr k < 2 ^ 64 ->
garr8 SEGS (arm W m) hp (bzs (key_ptrs ks)) ->
val_mem SEGS (arm W' m') (hp + 8 * Z.of_nat (length ks)) 8 (key_addr k) ->
(forall x, hp <= x < hp + 8 * Z.of_nat (length ks) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
garr8 SEGS (arm W' m') hp (bzs (key_ptrs (ks ++ [k]))).
Proof.
intros W m W' m' hp ks k Hk H V K.
rewrite gs_key_ptrs_app, gax_bzs_app.
apply garr8_app. split.
- apply (gax_garr8_kept W m); [exact H|]. intros x Hx. apply K. rewrite gax_bzs_len, gs_key_ptrs_len in Hx. lia.
- apply (gax_garr8_at _ (hp + 8 * Z.of_nat (length ks))); [|rewrite gax_bzs_len, gs_key_ptrs_len; lia].
  rewrite (gax_le8_bytes _ Hk). apply gax_garr8_of_val; [change (8 * Z.of_nat 8) with 64; exact Hk | exact V].
Qed.

(* ---- the two branch shapes this arm meets ---- *)
Lemma ga_bnez : forall E n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 ->
branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = negb (v =? 0).
Proof.
intros E n v H Hv. rewrite branch_ne_U, (U_atom E n v H Hv), (U_lit E 0 ltac:(lia)). reflexivity.
Qed.
Lemma ga_beqz_pos : forall E n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 4096 <= v ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = false.
Proof.
intros E n v H Hv H4. rewrite branch_eq_U, (U_atom E n v H Hv), (U_lit E 0 ltac:(lia)).
apply Z.eqb_neq. lia.
Qed.

(* ---- The line loop's core across an END whose key is NOT held: the held set does not move, only the
   history's key-update list gains the line and the count of updates still to come drops by one. ---- *)
Lemma ga_lcore_end : forall cx s1 D sent kl kl' l x H ka no oc nk nk' sk
  ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl,
LCORE B MT MMAX RG cx s1 D sent kl H ka no oc nk sk ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
gesture l = Some (GEnd, x) -> index_of x H = None -> nk' <= nk -> kl' = kl ++ [l] ->
LCORE B MT MMAX RG cx s1 D sent kl' H ka no oc nk' sk ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl.
Proof.
intros cx s1 D sent kl kl' l x H ka no oc nk nk' sk ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl
  (HM & HLK & HDSM & HH & HR & HBU) Hg Hidx Hnk ->.
pose proof HH as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
assert (HnotH : ~ In x H) by (apply index_of_none; exact Hidx).
split; [exact HM|]. split; [exact HLK|]. split; [exact HDSM|].
split; [|split; [exact HR | exact HBU]].
split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. split; [exact D5|].
split; [exact D6|]. split; [exact D7|]. split; [exact D8|].
split.
- rewrite gs_upds_snoc. unfold upd. rewrite Hg. unfold same_set in D9 |- *.
  intros y. rewrite upd_in_end. split.
  + intros Hy. split; [apply D9; exact Hy|]. intros ->. apply HnotH. exact Hy.
  + intros (Hy & _). apply D9. exact Hy.
- split; [lia | exact D11].
Qed.

(* ============================================================================================
   (3) LOWNESS of the footprints this arm moves, and the frame lemmas over them.  Every byte a
   cut predicate reads lies below the allocator's ceiling: a live block's byte, or an image byte.
   (The same shapes are Qed in W_drain_pro.v as pro_*; they are carried here so this file stands
   alone and does not depend on another hand's file.) *)
Ltac ga_in := repeat (first [left; reflexivity | right]).
Definition ga_low (aa : Z) : Prop := 0 <= aa < alloc_ceiling.

Lemma ga_blk_low : forall ly S (W : world SEGS) mem md qq nn aa,
AR SEGS B ly S W mem md -> In (qq, nn) (ablocks B ly S) -> qq <= aa -> aa < qq + req_size nn -> ga_low aa.
Proof.
intros ly S W mem md qq nn aa HAR Hin H1 H2.
destruct (al_blocks SEGS B LAWS ly S W mem md qq nn HAR Hin) as (_ & H4096 & Hceil & _).
unfold ga_low. lia.
Qed.

Lemma ga_img_low : forall aa lo hi, 0x10000 <= lo -> lo <= aa -> aa < hi -> hi <= 0x5fb000 -> ga_low aa.
Proof. intros aa lo hi H1 H2 H3 H4. pose proof asan_consts as (C1 & _). unfold ga_low. lia. Qed.

Lemma ga_recs_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !Mem.length_le8. lia.
Qed.

Lemma ga_aentry_fp_low : forall ly S (W : world SEGS) mem md e,
AR SEGS B ly S W mem md -> aentry_okx B ly S W mem e ->
forall r, In r (aentry_fp e) -> forall aa, fst r <= aa < snd r -> ga_low aa.
Proof.
intros ly S W mem md e HAR HE r Hr aa Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & _ & Hbuf & _ & Hhp & _ & _ & Hks).
assert (HK : forall k, In k (re_keys e) -> key_addr k <= aa < key_addr k + Z.of_nat (length (key_text k) + 1) ->
  ga_low aa).
{ intros k Hk Hka. rewrite Forall_forall in Hks. destruct (Hks k Hk) as (Hin & _).
  apply (ga_blk_low ly S W mem md (key_addr k) (Z.of_nat (length (key_text k)) + 1) aa HAR Hin); [lia|].
  pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)) as (_ & Hrq). lia. }
assert (HP : re_hp e <= aa < re_hp e + Z.of_nat (length (bzs (key_ptrs (re_keys e)))) -> ga_low aa).
{ intros Hpa. destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
  - rewrite Hke in Hpa. unfold bzs, key_ptrs in Hpa. cbn [map concat length] in Hpa. lia.
  - unfold bzs in Hpa. rewrite length_map, gs_key_ptrs_len in Hpa.
    apply (ga_blk_low ly S W mem md (re_hp e) (re_kh e) aa HAR Hin); [lia|].
    pose proof (req_size_pos (re_kh e) ltac:(lia)) as (_ & Hrq).
    unfold re_nheld in Hk1. lia. }
unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
  rewrite length_map, length_app in Ha.
  destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  apply (ga_blk_low ly S W mem md (re_buf e) (re_cap e) aa HAR Hin); [lia|].
  pose proof (req_size_pos (re_cap e) ltac:(lia)) as (_ & Hrq). lia.
- destruct Hr as [<- | Hr].
  + unfold gfp in Ha. cbn [fst snd] in Ha. exact (HP Ha).
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha. exact (HK k Hk Ha).
Qed.

Lemma ga_alist_fp_low : forall ly S (W : world SEGS) mem md LA l lns lo hi,
AR SEGS B ly S W mem md -> alist_at B ly S W mem LA l lns ->
0x10000 <= lo -> lo <= LA -> LA + 16 <= hi -> hi <= 0x5fb000 ->
forall r, In r (alist_fp LA l) -> forall aa, fst r <= aa < snd r -> ga_low aa.
Proof.
intros ly S W mem md LA l lns lo hi HAR HL Hlo1 Hlo2 Hhi1 Hhi2 r Hr aa Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. apply (ga_img_low aa lo hi); lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app, ga_recs_len in Ha.
    destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    apply (ga_blk_low ly S W mem md (hl_v l) (AREC * hl_cap l) aa HAR Hin); [lia|].
    pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as (_ & Hrq).
    unfold hl_n in Hn, Hj. unfold AREC in *. clear - Ha Hn Hj Hrq. lia.
  + apply in_map_iff in Hr as (qq & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hrecs. destruct (Hrecs qq Hq) as (Hin & _).
    apply (ga_blk_low ly S W mem md (fst qq) (Z.of_nat (length (snd qq)) + 1) aa HAR Hin); [lia|].
    pose proof (req_size_pos (Z.of_nat (length (snd qq)) + 1) ltac:(lia)) as (_ & Hrq). lia.
Qed.

Lemma ga_asrc_fp_low : forall ly S (W : world SEGS) mem md HA h,
AR SEGS B ly S W mem md -> asrc_at B ly S W mem HA h ->
rg_s RG <= HA -> HA + ASRC <= rg_s RG + 4 * ASRC ->
forall r, In r (asrc_fp HA h) -> forall aa, fst r <= aa < snd r -> ga_low aa.
Proof.
intros ly S W mem md HA h HAR HS Hlo Hhi r Hr aa Ha.
pose proof HGSB as (Hg1 & Hg2 & _).
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- cbn [fst snd] in Ha. apply (ga_img_low aa (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC in *; lia.
- unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map in Ha.
  apply (ga_blk_low ly S W mem md (hs_partial h) APARTIAL aa HAR Hpb); [lia|].
  pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrq). lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + refine (ga_alist_fp_low ly S W mem md (HA + 16) (hs_pending h) false (rg_s RG) (rg_s RG + 4 * ASRC)
      HAR Hpend _ _ _ _ r Hr aa Ha); unfold ASRC in *; lia.
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * refine (ga_alist_fp_low ly S W mem md (HA + 64) (hs_expected h) true (rg_s RG) (rg_s RG + 4 * ASRC)
        HAR Hexp _ _ _ _ r Hr aa Ha); unfold ASRC in *; lia.
    * refine (ga_alist_fp_low ly S W mem md (HA + 80) (hs_held h) true (rg_s RG) (rg_s RG + 4 * ASRC)
        HAR Hheld _ _ _ _ r Hr aa Ha); unfold ASRC in *; lia.
Qed.

Lemma ga_aout_fp_low : forall ly S (W : world SEGS) mem md c O mx no cap out,
AR SEGS B ly S W mem md -> aout_at B RG ly S W mem c O mx no cap out ->
forall r, In r (aout_fp B RG cap out) -> forall aa, fst r <= aa < snd r -> ga_low aa.
Proof.
intros ly S W mem md c O mx no cap out HAR HOUT r Hr aa Ha.
pose proof asan_consts as (C1 & _ & _ & _ & C5).
assert (GL : forall xx l, In (xx, l) (G_DR B RG) -> xx <= aa < xx + l -> ga_low aa).
{ intros xx l Hin Hx.
  assert (HI : inG (G_DR B RG) aa)
    by (unfold inG; apply Exists_exists; exists (xx, l); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
  pose proof (inG_low SEGS B pa_segs_low _ aa HG HI). unfold ga_low. lia. }
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
- pose proof HSM as (Hs1 & Hs2). apply (ga_img_low aa (rg_send_max RG) (rg_send_max RG + 8)); lia.
- apply (GL (rg_nout RG) 8); [unfold G_DR, G_SL; ga_in | lia].
- apply (GL (rg_capout RG) 8); [unfold G_DR, G_SL; ga_in | lia].
- apply (GL (rg_out RG) 8); [unfold G_DR, G_SL; ga_in | lia].
- pose proof (pa_obj_img 9 ltac:(lia)) as H9. rewrite HV9 in H9.
  apply (ga_img_low aa (rg_client RG) (rg_client RG + 4)); lia.
- apply (GL (rg_client_broken RG) 1); [unfold G_DR, G_SL; ga_in | lia].
- pose proof (pa_obj_img 12 ltac:(lia)) as H12. rewrite HV12 in H12.
  apply (ga_img_low aa (rg_send_dead RG) (rg_send_dead RG + 1)); lia.
- apply (GL (rg_send_eintr RG) 1); [unfold G_DR, G_SL; ga_in | lia].
- apply (GL (as_errno B) 4); [unfold G_DR, G_SL; ga_in | lia].
- destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
  apply (ga_blk_low ly S W mem md out cap aa HAR Hin); [lia|].
  pose proof (req_size_pos cap ltac:(lia)) as (_ & Hrq). lia.
Qed.

(* ---- the frame lemmas over a memory that keeps every byte's view ---- *)
Lemma ga_not_wrange : forall E rs aa,
Forall (fun r => ~ (base_val E (YP09.r_base r) + YP09.r_wlo r <= aa < base_val E (YP09.r_base r) + YP09.r_whi r)) rs ->
~ in_wrange E rs aa.
Proof. intros E rs aa HF (r & Hin & Hr). rewrite Forall_forall in HF. exact (HF r Hin Hr). Qed.

Lemma ga_kept_of : forall (W : world SEGS) m m' aa,
(forall x, 0 <= x < 2 ^ 64 -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
(forall x, apresent (w_H W) m x -> apresent (w_H W) m' x) ->
ga_low aa -> abyte_kept W m W m' aa.
Proof.
intros W m m' aa HK HP Ha. pose proof asan_consts as (C1 & _). unfold ga_low in Ha.
split; [apply HK; lia|]. unfold arm. apply writable_kept. exact (HP aa).
Qed.

Lemma ga_val_kept : forall (W : world SEGS) m m' aa (n : nat) v,
(forall x, 0 <= x < 2 ^ 64 -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
0 <= aa -> aa + Z.of_nat n <= 2 ^ 64 ->
val_mem SEGS (arm W m) aa n v -> val_mem SEGS (arm W m') aa n v.
Proof.
intros W m m' aa n v HK H1 H2 Hv.
apply (val_mem_kept SEGS (w_H W) (w_H W) m m' aa n v); [intros kk Hk; apply HK; lia | exact Hv].
Qed.

(* ---- The line loop's core across a memory that keeps every byte's view and only grows presence
   (what a run that stores nothing leaves).  Everything in DMEM moves; nothing else depends on the
   memory. ---- *)
Lemma ga_lcore_mem : forall cx s1 D sent kl H ka no oc nk sk ly1 S1 (W1 : world SEGS) m1 md1 k1
  e1 h1 out1 ev1 LB1 spent tl m' md',
LCORE B MT MMAX RG cx s1 D sent kl H ka no oc nk sk ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
AR SEGS B ly1 S1 W1 m1 md1 ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m' md' k1 ->
(forall x, 0 <= x < 2 ^ 64 -> aview SEGS (w_H W1) m' x = aview SEGS (w_H W1) m1 x) ->
(forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) m' x) ->
alloc_ceiling + 8 <= dsp0 cx - DRAIN_FRAME -> dsp0 cx <= 2 ^ 47 ->
4096 <= dxSA cx -> dxSA cx + AENT <= alloc_ceiling ->
rg_s RG <= dHA RG cx -> dHA RG cx + ASRC <= rg_s RG + 4 * ASRC ->
LCORE B MT MMAX RG cx s1 D sent kl H ka no oc nk sk ly1 S1 W1 m' md' k1 e1 h1 out1 ev1 LB1 spent tl.
Proof.
intros cx s1 D sent kl H ka no oc nk sk ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl m' md'
  (HM & HLK & HDS & HH & HR & HBU) HAR1 HJ' KL HP Hsplo Hsphi HSAlo HSAhi HHAlo HHAhi.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WF : DRAIN_FRAME = 336) by reflexivity.
pose proof HM as (_ & HROM & HPRES & HFRS & HFRM & HENT & HAWRx & HOKX & HSRC & HOTH & HKEPTx & HOUT & HLIVE & HPERM).
assert (AKE : forall fp, (forall r, In r fp -> forall x, fst r <= x < snd r -> ga_low x) ->
              akept W1 m1 W1 m' fp)
  by (intros fp Hlow r Hr x Hx; exact (ga_kept_of W1 m1 m' x KL HP (Hlow r Hr x Hx))).
assert (VK : forall aa n v, 0 <= aa -> aa + Z.of_nat n <= 2 ^ 64 ->
             val_mem SEGS (arm W1 m1) aa n v -> val_mem SEGS (arm W1 m') aa n v)
  by (intros aa n v H1 H2 Hv; exact (ga_val_kept W1 m1 m' aa n v KL H1 H2 Hv)).
assert (BLK : forall b, In b (aentry_blks e1) -> In b (ablocks B ly1 S1))
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPERM)); right; apply in_or_app; left; exact Hb).
assert (BLS : forall b, In b (asrc_blks h1) -> In b (ablocks B ly1 S1))
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPERM)); right; apply in_or_app; right;
      apply in_or_app; left; exact Hb).
assert (BLO : forall b, In b (aout_blks (drain_b_c.ds_ocap (dvirt cx s1 sk H ka no oc)) out1) ->
              In b (ablocks B ly1 S1))
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPERM)); right; apply in_or_app; right;
      apply in_or_app; right; apply in_or_app; left; exact Hb).
split; [|split; [exact HLK | split; [exact HDS | split; [exact HH | split; [exact HR | exact HBU]]]]].
split; [exact HJ'|].
split.
{ intros aa Haa.
  assert (Hl : 0 <= aa < kLowMemEnd)
    by (destruct Haa as (sg & Hsg & _ & Hrr);
        exact (pa_segs_low aa ltac:(exists sg; split; [exact Hsg | exact Hrr]))).
  rewrite (KL aa ltac:(unfold kLowMemEnd in *; lia)). exact (HROM aa Haa). }
split; [intros aa Hi Ho He Hp; exact (HP aa (HPRES aa Hi Ho He Hp))|].
split; [exact HFRS|].
split.
{ pose proof HFRM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13 & M14 & M15 & M16 & MSV).
  unfold dr_frame. cbv zeta.
  repeat (split; [first [apply VK; [lia | lia | first [exact M1 | exact M2 | exact M3 | exact M4 | exact M5
    | exact M6 | exact M7 | exact M8 | exact M9 | exact M10 | exact M11 | exact M12 | exact M13 | exact M14
    | exact M15 | exact M16]] | idtac]|]).
  intros i Hi. apply VK; [lia | lia | exact (MSV i Hi)]. }
split.
{ apply (gax_garr8_kept W1 m1 W1 m'); [exact HENT|].
  intros x Hx. apply KL. rewrite gax_bzs_len in Hx.
  assert (Hlen : length (entry_bytes e1) = 56%nat).
  { pose proof HOKX as (_ & _ & Kp1 & Kp2 & _). unfold entry_bytes. gax_len. lia. }
  rewrite Hlen in Hx. unfold AENT in HSAhi. lia. }
split; [intros i Hi; apply (writable_kept (w_H W1) m1 m'); [exact (HP _) | exact (HAWRx i Hi)]|].
split; [exact (gs_aentry_okx_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m' e1 HOKX
          (AKE (aentry_fp e1) (ga_aentry_fp_low ly1 S1 W1 m1 md1 e1 HAR1 HOKX)) BLK)|].
split; [exact (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m' (dHA RG cx) h1 HSRC
          (AKE (asrc_fp (dHA RG cx) h1) (ga_asrc_fp_low ly1 S1 W1 m1 md1 (dHA RG cx) h1 HAR1 HSRC HHAlo HHAhi)) BLS)|].
split.
{ intros i Hi Hne. destruct (HOTH i Hi Hne) as (f & oo & V1 & V2 & Hd).
  pose proof HGSB as (Hg1 & Hg2 & _).
  exists f, oo. split; [apply VK; [unfold ASRC in *; lia | unfold ASRC in *; lia | exact V1]|].
  split; [apply VK; [unfold ASRC in *; lia | unfold ASRC in *; lia | exact V2] | exact Hd]. }
split.
{ intros x H1 H2. destruct (HKEPTx x H1 H2) as (Kv & Kw). pose proof HGSB as (Hg1 & Hg2 & _).
  split; [rewrite (KL x ltac:(unfold ASRC in *; lia)); exact Kv|].
  intros Hw. apply (writable_kept (w_H W1) m1 m'); [exact (HP x) | exact (Kw Hw)]. }
split; [exact (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m' _ _ _ _ _ out1 HOUT
          (AKE _ (ga_aout_fp_low ly1 S1 W1 m1 md1 _ _ _ _ _ out1 HAR1 HOUT)) BLO)|].
split; [exact HLIVE | exact HPERM].
Qed.

(* ============================================================================================
   (4) The shapes every allocator call site in this lane needs.  (The same text is Qed in the
   lane's W_gsfree_scratch.v as gm_* / gfr_*; it is carried here so this file stands alone.) *)

(* the entry after realloc #2 and the store s->held = res: only the held ARRAY moved *)
Definition ga_entry (e : rentry) (res kh : Z) : rentry :=
RE (re_fd e) (re_eof e) (re_skip e) (re_pad1 e) (re_buf e) (re_used e) (re_cap e) res kh
   (re_pad2 e) (re_keys e) (re_U e) (re_junk e).

Lemma ga_in_zr_dec : forall x r, {in_zr x r} + {~ in_zr x r}.
Proof.
intros x r. unfold in_zr. destruct (Z_le_gt_dec (fst r) x); destruct (Z_lt_ge_dec x (fst r + snd r));
[left; lia | right; lia | right; lia | right; lia].
Qed.

Lemma ga_bk_trans : forall (W0 : world SEGS) m0 (W1 : world SEGS) m1 (W2 : world SEGS) m2 x,
abyte_kept W0 m0 W1 m1 x -> abyte_kept W1 m1 W2 m2 x -> abyte_kept W0 m0 W2 m2 x.
Proof.
intros W0 m0 W1 m1 W2 m2 x [V1 P1] [V2 P2]. split; [rewrite V2; exact V1 | intros H; exact (P2 (P1 H))].
Qed.

Lemma ga_writable_kept : forall (H H2 : word -> bool) (m m2 : word -> option byte) a,
(apresent H m a -> apresent H2 m2 a) -> writable_at SEGS (mrestrict H m) a -> writable_at SEGS (mrestrict H2 m2) a.
Proof.
intros H H2 m m2 a Hp Hw. unfold writable_at, wview, mrestrict in *. revert Hw.
destruct (H (Z_to_bv 64 a)) eqn:EH; destruct (H2 (Z_to_bv 64 a)) eqn:EH2; intros Hw.
- exact Hw.
- destruct (m2 (Z_to_bv 64 a)); [discriminate | exact Hw].
- destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em; [|exact Hw].
  destruct (Hp (conj EH (ex_intro _ b Em))) as [Hc _]. rewrite Hc in EH2. discriminate.
- destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
  + destruct (Hp (conj EH (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
  + destruct (m2 (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.

Lemma ga_img_wr : forall (W : world SEGS) m a,
in_img SEGS a -> ~ in_rom SEGS a -> aview SEGS (w_H W) m a <> None -> writable_at SEGS (arm W m) a.
Proof.
intros W m a Hi Hr Hv.
assert (Ha : bv_unsigned (Z_to_bv 64 a) = a)
  by (apply unsigned_lit_small; pose proof (pa_segs_low a Hi); unfold kLowMemEnd in *; lia).
assert (HA : w_H W (Z_to_bv 64 a) = false) by (apply hidden_not_img; rewrite Ha; exact Hi).
assert (Hfn : find_segment SEGS a 1 <> None) by (apply find_segment_img; exact Hi).
destruct (find_segment SEGS a 1) as [sg|] eqn:Hf; [|exfalso; exact (Hfn eq_refl)].
destruct (find_segment_some_spec _ _ _ _ Hf) as (Hin & Hlo & Hhi).
assert (Hw : seg_writable sg = true).
{ destruct (seg_writable sg) eqn:E; [reflexivity|]. exfalso. apply Hr. exists sg.
  split; [exact Hin|]. split; [exact E|]. lia. }
revert Hv. unfold aview, writable_at, arm, mbyte, wview, mrestrict, seg_rom, memory_read.
rewrite HA. rewrite ?Ha.
destruct (m (Z_to_bv 64 a)) as [b|]; [intros _; discriminate|].
change (Z.of_N 1) with 1. rewrite Hf. cbv beta iota zeta. rewrite Hw. cbv beta iota.
destruct (seg_readable sg); [|intros H; exfalso; apply H; reflexivity].
change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
destruct (segment_byte_at _ _); [intros _; discriminate | intros H; exfalso; apply H; reflexivity].
Qed.

Lemma ga_sep_head : forall ly S (W : world SEGS) m md x L y,
AR SEGS B ly S W m md -> Permutation (ablocks B ly S) (x :: L) -> In y L ->
zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S W m md x L y HAR HP Hy. destruct (in_split _ _ Hy) as (l1 & l2 & ->).
apply (sep_blocks_perm SEGS B LAWS ly S W m md x y (l1 ++ l2) HAR).
eapply Permutation_trans; [exact HP|]. apply perm_skip. apply Permutation_sym, Permutation_middle.
Qed.

Lemma ga_list_fp : forall ly S (W : world SEGS) m LA l lines, alist_at B ly S W m LA l lines ->
forall r x, In r (alist_fp LA l) -> fst r <= x < snd r ->
(LA <= x < LA + 16) \/ exists b, In b (alist_blks l) /\ fst b <= x < fst b + req_size (snd b).
Proof.
intros ly S W m LA l lines HL r x Hr Hx. pose proof HL as (_ & _ & _ & _ & Hnc & H6 & _ & _ & H9).
unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [left; cbn in Hx; lia|]. right.
apply in_app_iff in Hr as [Hr|Hr].
- destruct (hl_cap l =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<-|[]].
  destruct H6 as [(Hc & _) | (Hc0 & Hin & Hj & _)]; [apply Z.eqb_neq in Ec; lia|].
  exists (hl_v l, AREC * hl_cap l).
  split; [unfold alist_blks; rewrite Ec; apply in_or_app; left; left; reflexivity|].
  unfold gfp in Hx. cbn [fst snd] in *.
  unfold bzs in Hx. rewrite length_map, length_app, ga_recs_len in Hx. unfold req_size, AREC, hl_n in *.
  destruct (16 * hl_cap l =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia|]. lia.
- apply in_map_iff in Hr as (t & <- & Ht).
  exists (fst t, Z.of_nat (length (snd t)) + 1).
  split; [unfold alist_blks; apply in_or_app; right;
    apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))); exact Ht|].
  unfold gfp in Hx. cbn [fst snd] in *.
  unfold bzs in Hx. rewrite length_map, length_app in Hx. cbn [length] in Hx. unfold req_size.
  destruct (Z.of_nat (length (snd t)) + 1 =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | lia].
Qed.

Lemma ga_src_fp : forall ly S (W : world SEGS) m HA h, asrc_at B ly S W m HA h ->
forall r x, In r (asrc_fp HA h) -> fst r <= x < snd r ->
(HA <= x < HA + ASRC) \/ exists b, In b (asrc_blks h) /\ fst b <= x < fst b + req_size (snd b).
Proof.
intros ly S W m HA h HS r x Hr Hx.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- left. cbn [fst snd] in Hx. exact Hx.
- right. exists (hs_partial h, APARTIAL). split; [left; reflexivity|].
  unfold gfp in Hx. cbn [fst snd] in *. unfold bzs in Hx. rewrite length_map in Hx.
  assert (RQ : req_size APARTIAL = APARTIAL) by reflexivity. rewrite RQ. lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (ga_list_fp ly S W m (HA + 16) (hs_pending h) false Hpend r x Hr Hx) as [H | (b & Hb & Hbx)];
      [left; unfold ASRC; lia | right; exists b; split; [right; apply in_or_app; left; exact Hb | exact Hbx]].
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * destruct (ga_list_fp ly S W m (HA + 64) (hs_expected h) true Hexp r x Hr Hx) as [H | (b & Hb & Hbx)];
        [left; unfold ASRC; lia
        | right; exists b; split; [right; apply in_or_app; right; apply in_or_app; left; exact Hb | exact Hbx]].
    * destruct (ga_list_fp ly S W m (HA + 80) (hs_held h) true Hheld r x Hr Hx) as [H | (b & Hb & Hbx)];
        [left; unfold ASRC; lia
        | right; exists b; split; [right; apply in_or_app; right; apply in_or_app; right; exact Hb | exact Hbx]].
Qed.

Lemma ga_out_fp : forall cap out r x, In r (aout_fp B RG cap out) -> fst r <= x < snd r ->
inG (G_DR B RG) x \/ inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] x \/
(cap <> 0 /\ out <= x < out + cap).
Proof.
intros cap out r x Hr Hx. unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Hx;
try (left; unfold G_DR, G_SL, inG;
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]; fail);
try (right; left; unfold inG;
  repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl ]; fail).
destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Hx.
right; right. split; [apply Z.eqb_neq in Hc0; exact Hc0 | exact Hx].
Qed.

Lemma ga_frame_kept : forall cx (W : world SEGS) m (W' : world SEGS) m',
(forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W m W' m' x) ->
dr_frame RG cx W m -> dr_frame RG cx W' m'.
Proof.
intros cx W m W' m' KF HF. unfold dr_frame in *. cbv zeta in *.
assert (V : forall off v, 0 <= off -> off + 8 <= DRAIN_FRAME ->
  val_mem SEGS (arm W m) (dsp0 cx - DRAIN_FRAME + off) 8 v -> val_mem SEGS (arm W' m') (dsp0 cx - DRAIN_FRAME + off) 8 v).
{ intros off v H1 H2 H. apply (akept_vm W m); [intros y Hy; apply KF; cbn in Hy; lia | exact H]. }
destruct HF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & HS).
unfold DRAIN_FRAME in V.
repeat (split; [apply V; [lia | lia | assumption]|]).
intros i Hi. specialize (HS i Hi).
replace (dsp0 cx - DRAIN_FRAME + 232 + 8 * Z.of_nat i) with (dsp0 cx - DRAIN_FRAME + (232 + 8 * Z.of_nat i)) in * by lia.
apply V; [lia | unfold DRAIN_FRAME; lia | exact HS].
Qed.

Lemma ga_dregs_kept : forall cx regs regs' (W : world SEGS) m (W' : world SEGS) m',
dregs_line RG cx regs W m ->
getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
getr regs' 22 = getr regs 22 -> getr regs' 27 = getr regs 27 -> getr regs' 18 = getr regs 18 ->
getr regs' 9 = getr regs 9 -> getr regs' 8 = getr regs 8 -> getr regs' 21 = getr regs 21 ->
(forall x, dsp0 cx - DRAIN_FRAME <= x < dsp0 cx -> abyte_kept W m W' m' x) ->
dregs_line RG cx regs' W' m'.
Proof.
intros cx regs regs' W m W' m' HR E2 E3 E4 E22 E27 E18 E9 E8 E21 KF.
destruct HR as (Hsp & R3 & R4 & R22 & R27 & R18 & R9 & R8 & R21 & HFR & M192 & M200 & M56 & M48 & M64).
assert (V : forall off v, 0 <= off -> off + 8 <= DRAIN_FRAME ->
  val_mem SEGS (arm W m) (dsp0 cx - DRAIN_FRAME + off) 8 v -> val_mem SEGS (arm W' m') (dsp0 cx - DRAIN_FRAME + off) 8 v).
{ intros off v H1 H2 H. apply (akept_vm W m); [intros y Hy; apply KF; cbn in Hy; lia | exact H]. }
unfold dregs_line. unfold spZ in *. rewrite E2, E3, E4, E22, E27, E18, E9, E8, E21.
do 9 (split; [assumption|]).
split; [exact (ga_frame_kept cx W m W' m' KF HFR)|].
unfold DRAIN_FRAME in V.
repeat (split; [apply V; [lia | lia | assumption]|]).
apply V; [lia | lia | assumption].
Qed.

Ltac ga_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let z := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with z end; lia.

Lemma ga_dup : forall ly S (W : world SEGS) mem md x l1 l2 l3,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (l1 ++ x :: l2 ++ x :: l3) -> 0 <= snd x -> False.
Proof.
intros ly S W mem md x l1 l2 l3 HAR HP Hx.
assert (HP2 : Permutation (l1 ++ x :: l2 ++ x :: l3) (x :: x :: (l1 ++ l2) ++ l3)).
{ eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|]. apply perm_skip.
  rewrite app_assoc. apply Permutation_sym, Permutation_middle. }
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md x x _ HAR (Permutation_trans HP HP2)) as D.
destruct x as [b m]. unfold zdisjoint, block_rng in D. cbn [fst snd] in D, Hx.
pose proof (req_size_pos m Hx). lia.
Qed.

Lemma ga_dup_in : forall ly S (W : world SEGS) mem md L1 L2 x,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (L1 ++ x :: L2) -> In x L2 -> 0 <= snd x -> False.
Proof.
intros ly S W mem md L1 L2 x HAR HP Hin Hx. apply in_split in Hin as (l2 & l3 & ->).
exact (ga_dup ly S W mem md x L1 l2 l3 HAR HP Hx).
Qed.

Lemma ga_shent : forall Ex ly S (W : world SEGS) mem md b m (mt : nat) p lo hi,
AR SEGS B ly S W mem md -> In (b, m) (ablocks B ly S) -> U Ex gaBx = SHADOW_OFF -> U Ex (SOff mt 0) = p ->
b <= p + lo -> lo <= hi -> p + hi <= b + req_size m ->
shent_ok SEGS gaBx Ex (mrestrict (w_H W) mem) (mkSHE mt lo hi).
Proof.
intros Ex ly S W mem md b m mt p lo hi HAR Hin HBx Hp H1 H2 H3.
pose proof asan_consts as (C1 & _).
destruct (al_blocks SEGS B LAWS ly S W mem md b m HAR Hin) as (_ & H4 & Hc & Happ & _).
eapply shent_ok_of_range.
- exact (range_addressable_of_block SEGS B LAWS ly S W mem md b m (p + lo) (hi - lo) HAR Hin H1 ltac:(lia)).
- exact HBx.
- exact Hp.
- lia.
- lia.
- intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold SHADOW_OFF. lia.
Qed.

Lemma ga_in_rm : forall (x y : Z * Z) l1 l2, In x (l1 ++ y :: l2) -> x <> y -> In x (l1 ++ l2).
Proof.
intros x y l1 l2 H Hne. apply in_app_or in H as [H | [H | H]].
- apply in_or_app. left. exact H.
- exfalso. apply Hne. symmetry. exact H.
- apply in_or_app. right. exact H.
Qed.

Lemma ga_fp : forall cx ly S (W : world SEGS) mem md e h OC out b m,
AR SEGS B ly S W mem md ->
Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: aentry_blks e ++ asrc_blks h ++ aout_blks OC out ++ dxrest cx) ->
Permutation (ablocks B (dxly cx) (dxS cx))
  ((dxG cx, ATABLE) :: aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++ aout_blks (dxcap cx) (dxout cx) ++ dxrest cx) ->
In (b, m) (aentry_blks e) -> 0 <= m -> In (b, m) (ablocks B (dxly cx) (dxS cx)) ->
forall i, 0 <= i < req_size m -> inFP (dFP cx) (b + i).
Proof.
intros cx ly S W mem md e h OC out b m HAR HP1 HP0 Hae Hm Hin0 i Hi.
apply (Permutation_in _ HP0) in Hin0.
assert (HFP : In (b, m) (aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++ aout_blks (dxcap cx) (dxout cx)) ->
  inFP (dFP cx) (b + i)).
{ intros Hx. unfold dFP, dr_fp. exists (b, b + req_size m).
  split; [right; exact (in_map (fun b0 => (fst b0, fst b0 + req_size (snd b0))) _ (b, m) Hx)|].
  cbn [fst snd]. lia. }
destruct Hin0 as [Hg | Hin0].
- exfalso. rewrite Hg in HP1.
  exact (ga_dup_in ly S W mem md [] _ (b, m) HAR HP1 (in_or_app _ _ _ (or_introl Hae)) Hm).
- apply in_app_or in Hin0 as [Hx | Hin0]; [apply HFP; apply in_or_app; left; exact Hx|].
  apply in_app_or in Hin0 as [Hx | Hin0]; [apply HFP; apply in_or_app; right; apply in_or_app; left; exact Hx|].
  apply in_app_or in Hin0 as [Hx | Hx]; [apply HFP; apply in_or_app; right; apply in_or_app; right; exact Hx|].
  exfalso. apply in_split in Hae as (a1 & a2 & Ea). rewrite Ea, <- app_assoc in HP1.
  apply (ga_dup_in ly S W mem md ((dxG cx, ATABLE) :: a1) (a2 ++ asrc_blks h ++ aout_blks OC out ++ dxrest cx)
    (b, m) HAR HP1); [|exact Hm].
  apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. exact Hx.
Qed.

Lemma ga_awr_blk : forall cx ly S (W : world SEGS) mem md e h OC out b m blc lyq ownq a,
AR SEGS B ly S W mem md ->
Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: aentry_blks e ++ asrc_blks h ++ aout_blks OC out ++ dxrest cx) ->
Permutation (ablocks B (dxly cx) (dxS cx))
  ((dxG cx, ATABLE) :: aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++ aout_blks (dxcap cx) (dxout cx) ++ dxrest cx) ->
In (b, m) (aentry_blks e) -> 0 <= m -> In (b, m) blc -> b <= a < b + req_size m ->
awr_byte DRAIN_STK (dsp0 cx) (dFP cx) (ablocks B (dxly cx) (dxS cx)) blc lyq ownq a.
Proof.
intros cx ly S W mem md e h OC out b m blc lyq ownq a HAR HP1 HP0 Hae Hm Hinc Ha.
assert (DZ : forall x y : Z * Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
destruct (in_dec DZ (b, m) (ablocks B (dxly cx) (dxS cx))) as [Hin0 | Hnin0].
- right; left. split.
  + replace a with (b + (a - b)) by lia.
    apply (ga_fp cx ly S W mem md e h OC out b m HAR HP1 HP0 Hae Hm Hin0). lia.
  + exists b, m. split; [exact Hinc | exact Ha].
- right; right; left. exists b, m. split; [exact Hinc|]. split; [exact Hnin0 | exact Ha].
Qed.

Lemma ga_kept_blk : forall E lyc Sc (W : world SEGS) memc (W2 : world SEGS) mem2 slo shi (Er : Z -> Prop)
  ly2 S2 md2 n lo hi wlo whi cs b m base,
acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi Er ->
AR SEGS B ly2 S2 W2 mem2 md2 -> In (b, m) (ablocks B ly2 S2) ->
bv_unsigned (ew E n) = base -> In (b, m) (ablocks B lyc Sc) ->
b <= base + lo -> base + hi <= b + req_size m -> lo <= wlo -> whi <= hi ->
(forall a, b <= a < b + req_size m -> ~ Er a) ->
region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er ly2 S2 md2 n lo hi wlo whi cs b m base (_ & K2 & _) HAR2 Hin2 Hn Hin
  H1 H2 H3 H4 HnE.
destruct (al_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 b m HAR2 Hin2) as (_ & _ & _ & _ & Hpres & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hin); [lia|].
  replace (b + (a - b)) with a by lia. apply HnE. lia.
- intros _. apply (apresent_writable SEGS). exact (proj1 (Hpres a ltac:(lia))).
Qed.

Lemma ga_apresent_grows : forall H (m m' : word -> option byte) a,
mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a Hg [Hh [b Hb]]. split; [exact Hh|].
assert (Hx : mrestrict H m (Z_to_bv 64 a) <> None) by (unfold mrestrict; rewrite Hh, Hb; discriminate).
specialize (Hg _ Hx). unfold mrestrict in Hg. rewrite Hh in Hg.
destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; apply Hg; reflexivity].
Qed.

(* ============================================================================================
   (5) GARB, the line loop's core at the cut GAR (W_gsaddb_cx.v:141), from the post of realloc #2
   and the store s->held = res: the held ARRAY is the new block (res, 8 * nheld + 8), holding the
   key pointers realloc copied; s->nheld and the keys are the old ones; every other byte DMEM reads
   keeps its view across run 1, the call and run 2.  (The FREE arm's gf_main, W_gsfree_scratch.v,
   is the same block for free #2.) *)

(* the bytes of l at a, read at a' instead *)
Lemma gb_garr8_move : forall (W : world SEGS) m (W' : world SEGS) m' a a' l,
garr8 SEGS (arm W m) a l ->
(forall i, 0 <= i < Z.of_nat (length l) -> aview SEGS (w_H W') m' (a' + i) = aview SEGS (w_H W) m (a + i)) ->
garr8 SEGS (arm W' m') a' l.
Proof.
intros W m W' m' a a' l H K j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. specialize (Hv k Hk).
assert (Hk0 : k = 0%nat) by lia. subst k. cbn [Z.of_nat] in Hv |- *. rewrite Z.add_0_r in Hv |- *.
pose proof (K (Z.of_nat j) ltac:(lia)) as E. unfold aview in E. unfold arm in Hv |- *.
assert (EM : mbyte SEGS (mrestrict (w_H W') m') (a' + Z.of_nat j) = mbyte SEGS (mrestrict (w_H W) m) (a + Z.of_nat j)).
{ clear Hv. destruct (mbyte SEGS (mrestrict (w_H W') m') (a' + Z.of_nat j)) as [b'|],
    (mbyte SEGS (mrestrict (w_H W) m) (a + Z.of_nat j)) as [b|]; cbn in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E. }
rewrite EM. exact Hv.
Qed.

(* the relay entry's invariant after realloc #2 and the store s->held = res *)
Lemma gb_okx : forall ly S (W : world SEGS) m ly' S' (W' : world SEGS) m' e res,
aentry_okx B ly S W m e -> res <> 0 ->
(forall b, In b (aentry_blks (ga_entry e res (8 * re_nheld e + 8))) -> In b (ablocks B ly' S')) ->
akept W m W' m'
  ((if re_cap e =? 0 then [] else [gfp (re_buf e) (bzs (re_U e ++ re_junk e))]) ++
   map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0]))) (re_keys e)) ->
garr8 SEGS (arm W' m') res (bzs (key_ptrs (re_keys e))) ->
aentry_okx B ly' S' W' m' (ga_entry e res (8 * re_nheld e + 8)).
Proof.
intros ly S W m ly' S' W' m' e res (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14)
  Hr HB HK HA.
assert (HB' : forall b, In b ((if re_cap e =? 0 then [] else [(re_buf e, re_cap e)]) ++
  (res, 8 * re_nheld e + 8) :: map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e)) ->
  In b (ablocks B ly' S')).
{ intros b Hb. apply HB. unfold aentry_blks, ga_entry. cbn [re_cap re_buf re_hp re_kh re_keys].
  rewrite (proj2 (Z.eqb_neq res 0) Hr). exact Hb. }
clear HB.
assert (N0 : 0 <= re_nheld e) by (unfold re_nheld; clear - Hr; lia).
assert (E : re_nheld (ga_entry e res (8 * re_nheld e + 8)) = re_nheld e) by reflexivity.
unfold aentry_okx. rewrite E. unfold ga_entry.
cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_kh re_pad2 re_keys re_U re_junk].
refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8
  (conj _ (conj H10 (conj _ (conj H12 (conj H13 _))))))))))))).
- (* s->buf *)
  destruct H9 as [H9 | (Hc & Hin & Hj & Hg)]; [left; exact H9|right].
  assert (Ec : (re_cap e =? 0) = false) by (apply Z.eqb_neq; clear - Hc; lia).
  split; [exact Hc|].
  split; [apply HB'; rewrite Ec; left; reflexivity|].
  split; [exact Hj|].
  apply (akept_garr8 W m); [|exact Hg].
  intros x Hx. apply (HK (gfp (re_buf e) (bzs (re_U e ++ re_junk e)))); [|exact Hx].
  rewrite Ec. left. reflexivity.
- (* s->held: the new block *)
  right. split; [exact Hr|].
  split; [apply HB'; apply in_or_app; right; left; reflexivity|].
  split; [clear - N0; lia|].
  split; [clear - N0; lia | exact HA].
- (* every held key *)
  rewrite Forall_forall in H14 |- *. intros k Hk.
  destruct (H14 k Hk) as (K1 & K2 & K3).
  split; [apply HB'; apply in_or_app; right; right;
    apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))); exact Hk|].
  split; [|exact K3].
  apply (akept_garr8 W m); [|exact K2].
  intros x Hx. apply (HK (gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))); [|exact Hx].
  apply in_or_app. right.
  apply (in_map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0])))). exact Hk.
Qed.

(* DLINK when only the array moved: ent_ka is the new size *)
Lemma gb_dlink : forall cx s1 sk H ka ka' no oc e1 res kh h1,
DLINK (dvirt cx s1 sk H ka no oc) e1 h1 -> res <> 0 -> kh = ka' ->
DLINK (dvirt cx s1 sk H ka' no oc) (ga_entry e1 res kh) h1.
Proof.
intros cx s1 sk H ka ka' no oc e1 res kh h1 (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12) Hr Hk.
refine (conj K1 (conj K2 (conj K3 (conj K4 (conj _ (conj K6 (conj K7 (conj K8 (conj K9 (conj K10 (conj K11 K12))))))))))).
unfold drain_b_c.ent_ka. cbn [ga_entry re_hp re_kh dvirt drain_b_c.ds_ka].
rewrite (proj2 (Z.eqb_neq res 0) Hr). exact Hk.
Qed.

(* DHIST does not read ds_ka *)
Lemma gb_dhist : forall cx s1 sk H ka ka' no oc D F sent kl h1 LB1 nk,
DHIST cx (dvirt cx s1 sk H ka no oc) D F sent kl h1 LB1 nk ->
DHIST cx (dvirt cx s1 sk H ka' no oc) D F sent kl h1 LB1 nk.
Proof. intros cx s1 sk H ka ka' no oc D F sent kl h1 LB1 nk HH. exact HH. Qed.

(* The cut's core from the arm's post: everything that is not the symbolic run. *)
Lemma gb_garb : forall cx s1 D p q ly1 S1 (W1 : world SEGS) m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl
  mR1 ly2 S2 (W2 : world SEGS) mem2 m2 md2 res xx tl2,
DBASE B MT MMAX RG cx ->
GSB B MT MMAX RG cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
gesture (dline s1 p q) = Some (GBegin, xx) -> index_of xx (dlH cx s1 p) = None ->
(8 * re_nheld e1 + 8) - drain_b_c.ent_ka e1 + tr_peak (RelayRunT.RMalloc (Z.of_nat (length xx) + 1) :: tl2) <=
  tr_peak tl ->
tr_cost MT tl = mo_malloc MT (8 * re_nheld e1 + 8) + mo_free MT +
  (mo_malloc MT (Z.of_nat (length xx) + 1) + mo_free MT + tr_cost MT tl2) ->
tr_max (RelayRunT.RMalloc (Z.of_nat (length xx) + 1) :: tl2) <= tr_max tl ->
@ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly2 S2 W2 m2 md2 (k1 + 3) ->
frames S2 = frames S1 -> 4096 <= res ->
Permutation (ablocks B ly2 S2)
  ((res, 8 * re_nheld e1 + 8) :: (dxG cx, ATABLE) ::
   (if re_cap e1 =? 0 then [] else [(re_buf e1, re_cap e1)]) ++
   map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e1) ++
   asrc_blks h1 ++ aout_blks (GSoc cx s1 p q) out1 ++ dxrest cx) ->
(re_hp e1 <> 0 -> forall i, 0 <= i < Z.min (re_kh e1) (8 * re_nheld e1 + 8) ->
  aview SEGS (w_H W2) mem2 (res + i) = aview SEGS (w_H W1) mR1 (re_hp e1 + i)) ->
acall_kept SEGS B ly1 S1 W1 mR1 W2 mem2 (dsp0 cx + - DRAIN_FRAME - ASTACK) (dsp0 cx + - DRAIN_FRAME)
  (fun a => res <= a < res + req_size (8 * re_nheld e1 + 8) \/
            re_hp e1 <> 0 /\ re_hp e1 <= a < re_hp e1 + req_size (re_kh e1)) ->
(forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W1) mR1 (as_errno B + i)) ->
(forall a, in_img SEGS a -> ~ aowned B ly1 S1 a -> ~ aowned B ly2 S2 a -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (res <= a < res + req_size (8 * re_nheld e1 + 8) \/
     re_hp e1 <> 0 /\ re_hp e1 <= a < re_hp e1 + req_size (re_kh e1)) ->
  apresent (w_H W1) mR1 a -> apresent (w_H W2) mem2 a) ->
mem_grows (mrestrict (w_H W1) m1) (mrestrict (w_H W1) mR1) ->
mem_grows (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) m2) ->
(forall aa, 0 <= aa < 2 ^ 64 -> ~ (dxSA cx + 40 <= aa < dxSA cx + 52) ->
  aview SEGS (w_H W1) mR1 aa = aview SEGS (w_H W1) m1 aa) ->
(forall aa, 0 <= aa < 2 ^ 64 -> ~ (dxSA cx + 40 <= aa < dxSA cx + 52) ->
  aview SEGS (w_H W2) m2 aa = aview SEGS (w_H W2) mem2 aa) ->
mo_le MT S1 S2 (mo_malloc MT (8 * re_nheld e1 + 8) + mo_free MT) ->
val_mem SEGS (arm W2 m2) (dxSA cx + 40) 8 res ->
val_mem SEGS (arm W2 m2) (dxSA cx + 48) 4 (re_nheld e1) ->
rom_view SEGS W2 m2 ->
(forall aa, dsp0 cx - DRAIN_FRAME <= aa < dsp0 cx -> abyte_kept W1 m1 W2 m2 aa) ->
GARB B MT MMAX RG cx s1 D p q ly2 S2 W2 m2 md2 (k1 + 3) (ga_entry e1 res (8 * re_nheld e1 + 8)) h1 out1 ev1 LB1
  (spent + (mo_malloc MT (8 * re_nheld e1 + 8) + mo_free MT))
  (RelayRunT.RMalloc (Z.of_nat (length xx) + 1) :: tl2).
Proof.
intros cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl mR1 ly2 S2 W2 mem2 m2 md2 res xx tl2
  HB HCORE Hges Hidx Etra Etrc HmxT HJ2 Hfr2 Hres4096 BASEP Hcopy (K1 & K2 & K3 & K4 & K5 & K6) Herr2 Hpres2
  HGr1 HGr2 KR1 KR2 Hmle2 V40 V48 ROM2 FK.
unfold GSB in HCORE.
destruct HCORE as (HDMEM & HLINK & HSAME & HHIST & HRST & HBUD).
destruct HDMEM as (HJ & HROM & HPRESK & HFRM & HFRAME & HENTB & HAWR & HOKX & HSRC & HOTH & HGSK & HOUT & HLIVE & HPERM).
cbn [dvirt drain_b_c.ds_ocap drain_b_c.ds_no] in HOUT, HPERM, HLIVE.
pose proof HB as (_ & _ & _ & HGle & HSAle & _ & _ & _ & Hj & _).
pose proof asan_consts as (C1 & _).
pose proof YM05.alloc_ceiling_lt as HAC.
assert (AR1 : AR SEGS B ly1 S1 W1 m1 md1) by (eapply ajournal_gx_AR; exact HJ).
assert (AR2 : AR SEGS B ly2 S2 W2 m2 md2) by (eapply ajournal_gx_AR; exact HJ2).
pose proof HOKX as (_ & _ & Hp1 & Hp2 & _ & _ & HU & _ & HBUF & Hnh & HHP & _ & _ & _).
assert (HNH : re_nheld e1 = Z.of_nat (length (re_keys e1))) by reflexivity.
assert (Hnh0 : 0 <= re_nheld e1) by (rewrite HNH; clear - Hnh; lia).
assert (RQT : req_size ATABLE = 896) by reflexivity.
assert (RQN : req_size (8 * re_nheld e1 + 8) = 8 * re_nheld e1 + 8)
  by (unfold req_size; destruct (Z.eqb_spec (8 * re_nheld e1 + 8) 0) as [E0|E0];
      [exfalso; clear - Hnh0 E0; lia | reflexivity]).
(* ---- the live blocks before and after ---- *)
match type of HPERM with Permutation _ (_ :: aentry_blks _ ++ ?r) => pose (R := r) end.
pose (TB := (dxG cx, ATABLE)).
pose (NB := (res, 8 * re_nheld e1 + 8)).
pose (BUF := if re_cap e1 =? 0 then [] else [(re_buf e1, re_cap e1)]).
pose (KEYS := map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e1)).
pose (X := BUF ++ KEYS ++ R).
assert (PN : Permutation (ablocks B ly2 S2) (NB :: TB :: X)) by exact BASEP.
assert (PT : Permutation (ablocks B ly2 S2) (TB :: NB :: X)) by exact (Permutation_trans PN (perm_swap TB NB X)).
assert (TB1 : In TB (ablocks B ly1 S1)) by (apply (Permutation_in _ (Permutation_sym HPERM)); left; reflexivity).
assert (TB2 : In TB (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym PT)); left; reflexivity).
assert (NB2 : In NB (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym PN)); left; reflexivity).
assert (X2 : forall b, In b X -> In b (ablocks B ly2 S2))
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym PN)); right; right; exact Hb).
assert (X1 : forall b, In b X -> In b (ablocks B ly1 S1)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym HPERM)). right. unfold aentry_blks. rewrite <- !app_assoc.
  unfold X in Hb. apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|].
  apply in_or_app; right. apply in_or_app; right. exact Hb. }
assert (PH1 : re_hp e1 <> 0 -> Permutation (ablocks B ly1 S1) ((re_hp e1, re_kh e1) :: TB :: X)).
{ intros Hz.
  assert (EA1 : aentry_blks e1 = BUF ++ (re_hp e1, re_kh e1) :: KEYS)
    by (unfold aentry_blks, BUF, KEYS; rewrite (proj2 (Z.eqb_neq (re_hp e1) 0) Hz); reflexivity).
  eapply Permutation_trans; [exact HPERM|]. rewrite EA1, <- app_assoc.
  eapply Permutation_trans; [apply perm_skip; apply Permutation_sym, Permutation_middle|].
  apply perm_swap. }
assert (DTN : zdisjoint (block_rng TB) (block_rng NB))
  by exact (ga_sep_head ly2 S2 W2 m2 md2 TB (NB :: X) NB AR2 PT (or_introl eq_refl)).
assert (DTX : forall b, In b X -> zdisjoint (block_rng TB) (block_rng b))
  by (intros b Hb; exact (ga_sep_head ly2 S2 W2 m2 md2 TB (NB :: X) b AR2 PT (or_intror Hb))).
assert (DNX : forall b, In b X -> zdisjoint (block_rng NB) (block_rng b))
  by (intros b Hb; exact (ga_sep_head ly2 S2 W2 m2 md2 NB (TB :: X) b AR2 PN (or_intror Hb))).
assert (DHX : re_hp e1 <> 0 -> forall b, In b X -> zdisjoint (block_rng (re_hp e1, re_kh e1)) (block_rng b))
  by (intros Hz b Hb; exact (ga_sep_head ly1 S1 W1 m1 md1 _ (TB :: X) b AR1 (PH1 Hz) (or_intror Hb))).
assert (DHT : re_hp e1 <> 0 -> zdisjoint (block_rng (re_hp e1, re_kh e1)) (block_rng TB))
  by (intros Hz; exact (ga_sep_head ly1 S1 W1 m1 md1 _ (TB :: X) TB AR1 (PH1 Hz) (or_introl eq_refl))).
(* ---- what the arm keeps ---- *)
assert (BKV : forall pb mb x, In (pb, mb) (ablocks B ly1 S1) -> pb <= x < pb + req_size mb ->
  ~ (dxSA cx + 40 <= x < dxSA cx + 52) -> ~ (res <= x < res + req_size (8 * re_nheld e1 + 8)) ->
  ~ (re_hp e1 <> 0 /\ re_hp e1 <= x < re_hp e1 + req_size (re_kh e1)) ->
  aview SEGS (w_H W2) m2 x = aview SEGS (w_H W1) m1 x).
{ intros pb mb x Hb Hx H40 Hn Ho.
  destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 pb mb AR1 Hb) as (_ & H4 & Hc & _).
  assert (Hr : 0 <= x < 2 ^ 64) by (clear - H4 Hc Hx C1; lia).
  rewrite (KR2 x Hr H40).
  pose proof (K2 pb mb (x - pb) Hb ltac:(clear - Hx; lia)) as E2.
  replace (pb + (x - pb)) with x in E2 by ring.
  rewrite E2; [exact (KR1 x Hr H40)|].
  cbv beta. intros [G1|G2]; [exact (Hn G1) | exact (Ho G2)]. }
assert (WK2 : forall pb mb x, In (pb, mb) (ablocks B ly2 S2) -> pb <= x < pb + req_size mb ->
  writable_at SEGS (arm W2 m2) x).
{ intros pb mb x Hb Hx. destruct (al_blocks SEGS B LAWS ly2 S2 W2 m2 md2 pb mb AR2 Hb) as (_ & _ & _ & _ & Hpr & _).
  apply (apresent_writable SEGS). exact (proj1 (Hpr x Hx)). }
assert (KO : forall b x, In b X -> fst b <= x < fst b + req_size (snd b) -> abyte_kept W1 m1 W2 m2 x).
{ intros [pb mb] x Hb Hx. cbn [fst snd] in Hx. split.
  - apply (BKV pb mb x (X1 _ Hb) Hx).
    + intros H40. pose proof (DTX _ Hb) as Dj. unfold zdisjoint, block_rng, TB in Dj. cbn [fst snd] in Dj.
      rewrite RQT in Dj. clear - Dj Hx H40 HGle HSAle. unfold AENT, ATABLE in *. lia.
    + intros Hn. pose proof (DNX _ Hb) as Dj. unfold zdisjoint, block_rng, NB in Dj. cbn [fst snd] in Dj.
      clear - Dj Hx Hn. lia.
    + intros (Hz & Ho). pose proof (DHX Hz _ Hb) as Dj. unfold zdisjoint, block_rng in Dj. cbn [fst snd] in Dj.
      clear - Dj Hx Ho. lia.
  - intros _. exact (WK2 pb mb x (X2 _ Hb) Hx). }
assert (TK : forall x, dxSA cx <= x < dxSA cx + AENT -> ~ (dxSA cx + 40 <= x < dxSA cx + 52) ->
  aview SEGS (w_H W2) m2 x = aview SEGS (w_H W1) m1 x).
{ intros x Hx H40.
  apply (BKV (dxG cx) ATABLE x TB1 ltac:(rewrite RQT; clear - Hx HGle HSAle; unfold AENT, ATABLE in *; lia) H40).
  - intros Hn. pose proof DTN as Dj. unfold zdisjoint, block_rng, TB, NB in Dj. cbn [fst snd] in Dj.
    rewrite RQT in Dj. clear - Dj Hx Hn HGle HSAle. unfold AENT, ATABLE in *. lia.
  - intros (Hz & Ho). pose proof (DHT Hz) as Dj. unfold zdisjoint, block_rng, TB in Dj. cbn [fst snd] in Dj.
    rewrite RQT in Dj. clear - Dj Hx Ho HGle HSAle. unfold AENT, ATABLE in *. lia. }
assert (NIMG : forall x, in_img SEGS x -> ~ (dxSA cx + 40 <= x < dxSA cx + 52)).
{ intros x Hx Hw. apply (blk_img SEGS B LAWS ly1 S1 W1 m1 md1 (dxG cx) ATABLE x AR1 TB1); [|exact Hx].
  rewrite RQT. clear - Hw HGle HSAle. unfold AENT, ATABLE in *. lia. }
assert (IMR : forall x, in_img SEGS x -> 0 <= x < 2 ^ 64)
  by (intros x Hi; pose proof (pa_segs_low x Hi) as Hl; unfold kLowMemEnd in Hl; clear - Hl; lia).
assert (Hnot : forall x ly0 S0 (W0 : world SEGS) mm md0, AR SEGS B ly0 S0 W0 mm md0 -> in_img SEGS x ->
  ~ Exists (in_zr x) (as_owned_static B) -> ~ aowned B ly0 S0 x).
{ intros x ly0 S0 W0 mm md0 HA Hi Ho Hw. apply Ho.
  exact (proj1 (al_owned_image SEGS B LAWS ly0 S0 W0 mm md0 x HA Hi) Hw). }
assert (NBLK : forall x, in_img SEGS x -> ~ (res <= x < res + req_size (8 * re_nheld e1 + 8) \/
    re_hp e1 <> 0 /\ re_hp e1 <= x < re_hp e1 + req_size (re_kh e1))).
{ intros x Hi [Hn | (Hz & Ho)].
  - exact (blk_img SEGS B LAWS ly2 S2 W2 m2 md2 res (8 * re_nheld e1 + 8) x AR2 NB2 Hn Hi).
  - destruct HHP as [(Hz0 & _) | (_ & Hin & _)]; [exact (Hz Hz0)|].
    exact (blk_img SEGS B LAWS ly1 S1 W1 m1 md1 _ _ x AR1 Hin Ho Hi). }
assert (PK : forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) ->
  ~ (as_errno B <= x < as_errno B + 4) -> apresent (w_H W1) m1 x -> apresent (w_H W2) m2 x).
{ intros x Hi Ho He Hp. apply (ga_apresent_grows _ _ _ _ HGr2).
  apply (Hpres2 x Hi (Hnot x _ _ _ _ _ AR1 Hi Ho) (Hnot x _ _ _ _ _ AR2 Hi Ho) He (NBLK x Hi)).
  exact (ga_apresent_grows _ _ _ _ HGr1 Hp). }
assert (IK : forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) ->
  ~ (as_errno B <= x < as_errno B + 4) -> aview SEGS (w_H W2) m2 x = aview SEGS (w_H W1) m1 x).
{ intros x Hi Ho He.
  rewrite (KR2 x (IMR x Hi) (NIMG x Hi)), (K3 x Hi Ho He). exact (KR1 x (IMR x Hi) (NIMG x Hi)). }
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VE & _).
assert (EK : forall x, as_errno B <= x < as_errno B + 4 -> abyte_kept W1 m1 W2 m2 x).
{ intros x Hx.
  assert (Hg : inG (G_DR B RG) x).
  { unfold G_DR, G_SL, inG.
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; clear - Hx; lia | apply Exists_cons_tl ]. }
  pose proof (proj1 (HG x Hg)) as Hi.
  assert (EV : aview SEGS (w_H W2) m2 x = aview SEGS (w_H W1) m1 x).
  { rewrite (KR2 x (IMR x Hi) (NIMG x Hi)).
    pose proof (Herr2 (x - as_errno B) ltac:(clear - Hx; lia)) as E2.
    replace (as_errno B + (x - as_errno B)) with x in E2 by ring.
    rewrite E2. exact (KR1 x (IMR x Hi) (NIMG x Hi)). }
  split; [exact EV|]. intros _.
  apply ga_img_wr; [exact Hi | exact (HGR x Hg) |].
  rewrite EV. unfold aview. unfold arm in VE.
  replace x with (as_errno B + Z.of_nat (Z.to_nat (x - as_errno B))) by (clear - Hx; lia).
  rewrite (VE (Z.to_nat (x - as_errno B)) ltac:(clear - Hx; lia)). cbn [option_map]. discriminate. }
assert (GK : forall x, inG (G_DR B RG) x \/ inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] x ->
  abyte_kept W1 m1 W2 m2 x).
{ intros x Hx.
  assert (IO : in_img SEGS x /\ ~ Exists (in_zr x) (as_owned_static B))
    by (destruct Hx as [Hx|Hx]; [exact (conj (proj1 (HG x Hx)) (proj1 (proj2 (HG x Hx)))) | exact (conj (proj1 (HGO x Hx)) (proj1 (proj2 (HGO x Hx))))]).
  destruct IO as [Hi Ho].
  assert (Hdec : (as_errno B <= x < as_errno B + 4) \/ ~ (as_errno B <= x < as_errno B + 4)) by (clear - Hi; lia).
  destruct Hdec as [He | Hne]; [exact (EK x He)|].
  split; [exact (IK x Hi Ho Hne)|].
  intros Hw. apply (ga_writable_kept (w_H W1) (w_H W2) m1 m2 x); [|exact Hw].
  intros Hp. exact (PK x Hi Ho Hne Hp). }
assert (GGS : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> abyte_kept W1 m1 W2 m2 x).
{ intros x Hx. apply GK. left. unfold G_DR, inG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Hx. }
(* ---- the memory core ---- *)
assert (PK2 : apres_kept B (dxW cx) (dxmem cx) W2 m2)
  by (intros x Hi Ho He Hp; exact (PK x Hi Ho He (HPRESK x Hi Ho He Hp))).
destruct (al_blocks SEGS B LAWS ly2 S2 W2 m2 md2 _ _ AR2 NB2) as (_ & _ & Hrc & _).
rewrite RQN in Hrc.
assert (Hres64 : 0 <= res < 2 ^ 64) by (clear - Hrc Hres4096 HAC Hnh0; lia).
assert (ENT2 : garr8 SEGS (arm W2 m2) (dxSA cx) (bzs (entry_bytes (ga_entry e1 res (8 * re_nheld e1 + 8))))).
{ refine (gax_entry_store W1 m1 W2 m2 (dxSA cx) e1 (ga_entry e1 res (8 * re_nheld e1 + 8)) Hp1 Hp2
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Hres64 _ HENTB V40 V48 _ _).
  - change (re_nheld (ga_entry e1 res (8 * re_nheld e1 + 8))) with (re_nheld e1). clear - Hnh Hnh0. lia.
  - intros x Hx. apply TK; [unfold AENT; clear - Hx; lia | clear - Hx; lia].
  - intros x Hx. apply TK; [unfold AENT; clear - Hx; lia | clear - Hx; lia]. }
assert (AWR2 : awr W2 m2 (dxSA cx) AENT).
{ intros i Hi. apply (WK2 (dxG cx) ATABLE (dxSA cx + i) TB2). rewrite RQT.
  clear - Hi HGle HSAle. unfold AENT, ATABLE in *. lia. }
assert (PERM2 : Permutation (ablocks B ly2 S2)
  ((dxG cx, ATABLE) :: aentry_blks (ga_entry e1 res (8 * re_nheld e1 + 8)) ++ R)).
{ assert (EA2 : aentry_blks (ga_entry e1 res (8 * re_nheld e1 + 8)) = BUF ++ NB :: KEYS).
  { unfold ga_entry, aentry_blks, BUF, KEYS, NB. cbn [re_cap re_buf re_hp re_kh re_keys].
    rewrite (proj2 (Z.eqb_neq res 0) ltac:(clear - Hres4096; lia)). reflexivity. }
  eapply Permutation_trans; [exact PT|]. apply perm_skip.
  rewrite EA2, <- app_assoc. change ((NB :: KEYS) ++ R) with (NB :: (KEYS ++ R)).
  apply Permutation_middle. }
assert (OKX2 : aentry_okx B ly2 S2 W2 m2 (ga_entry e1 res (8 * re_nheld e1 + 8))).
{ apply (gb_okx ly1 S1 W1 m1 ly2 S2 W2 m2 e1 res HOKX ltac:(clear - Hres4096; lia)).
  - intros b Hb. apply (Permutation_in _ (Permutation_sym PERM2)). right. apply in_or_app. left. exact Hb.
  - intros r Hr x Hx. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    + destruct (re_cap e1 =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []].
      destruct HBUF as [(Hc0 & _) | (Hcp & _ & HJk & _)]; [apply Z.eqb_neq in Ec; contradiction|].
      apply (KO (re_buf e1, re_cap e1) x).
      * unfold X, BUF. apply in_or_app. left. rewrite ?Ec. left. reflexivity.
      * unfold gfp in Hx. cbn [fst snd] in Hx |- *. unfold bzs in Hx. rewrite length_map, length_app in Hx.
        pose proof (req_size_pos (re_cap e1) ltac:(clear - Hcp; lia)) as (_ & RQ). clear - Hx HU HJk RQ. lia.
    + apply in_map_iff in Hr as (k & <- & Hk).
      apply (KO (key_addr k, Z.of_nat (length (key_text k)) + 1) x).
      * unfold X. apply in_or_app. right. apply in_or_app. left. unfold KEYS.
        apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk.
      * unfold gfp in Hx. cbn [fst snd] in Hx |- *. unfold bzs in Hx. rewrite length_map, length_app in Hx.
        cbn [length] in Hx.
        pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(clear - Hk; lia)) as (_ & RQ).
        clear - Hx RQ. lia.
  - (* the new array: its first 8 nheld bytes are the ones realloc copied from the old array *)
    destruct HHP as [(Hz & Hk0) | (Hz & Hin & Hk1 & Hk2 & Hg)].
    + rewrite Hk0. exact (garr8_nil SEGS (arm W2 m2) res).
    + destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 _ _ AR1 Hin) as (_ & Hh4 & Hhc & _).
      assert (RQH : req_size (re_kh e1) = re_kh e1)
        by (unfold req_size; destruct (Z.eqb_spec (re_kh e1) 0) as [E0|E0];
            [exfalso; clear - Hk2 E0; lia | reflexivity]).
      rewrite RQH in Hhc.
      pose proof (DHT Hz) as Dh. unfold zdisjoint, block_rng, TB in Dh. cbn [fst snd] in Dh. rewrite RQH, RQT in Dh.
      pose proof DTN as Dn. unfold zdisjoint, block_rng, TB, NB in Dn. cbn [fst snd] in Dn. rewrite RQT, RQN in Dn.
      apply (gb_garr8_move W1 m1 W2 m2 (re_hp e1) res _ Hg).
      intros i Hi. rewrite gax_bzs_len, gs_key_ptrs_len in Hi.
      assert (Hi8 : 0 <= i < 8 * re_nheld e1) by (rewrite HNH; clear - Hi; lia).
      assert (Hr1 : 0 <= res + i < 2 ^ 64) by (clear - Hi8 Hrc Hres4096 HAC; lia).
      assert (Hr2 : 0 <= re_hp e1 + i < 2 ^ 64) by (clear - Hi8 Hk1 Hhc Hh4 HAC; lia).
      rewrite (KR2 (res + i) Hr1 ltac:(clear - Dn Hi8 HGle HSAle; unfold AENT, ATABLE in *; lia)).
      rewrite (Hcopy Hz i ltac:(clear - Hi8 Hk1; lia)).
      exact (KR1 (re_hp e1 + i) Hr2 ltac:(clear - Dh Hi8 Hk1 HGle HSAle; unfold AENT, ATABLE in *; lia)). }
assert (SRC2 : asrc_at B ly2 S2 W2 m2 (dHA RG cx) h1).
{ apply (asrc_at_kept B ly1 S1 W1 m1 ly2 S2 W2 m2 (dHA RG cx) h1 HSRC).
  - intros r Hr x Hx. destruct (ga_src_fp ly1 S1 W1 m1 (dHA RG cx) h1 HSRC r x Hr Hx) as [Hg | (b & Hb & Hbx)].
    + apply GGS. unfold dHA in Hg. clear - Hg Hj. unfold ASRC in *. lia.
    + apply (KO b x); [|exact Hbx]. unfold X, R. apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. left. exact Hb.
  - intros b Hb. apply X2. unfold X, R. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    exact Hb. }
assert (OTH2 : aothers_at RG W2 m2 (dxj cx) (re_fd (dxe cx))).
{ intros i Hi Hij. destruct (HOTH i Hi Hij) as (f & o' & VV1 & VV2 & Ho). exists f, o'.
  assert (GV : forall a0 (nn : nat) v, rg_s RG <= a0 -> a0 + Z.of_nat nn <= rg_s RG + 4 * ASRC ->
    val_mem SEGS (arm W1 m1) a0 nn v -> val_mem SEGS (arm W2 m2) a0 nn v).
  { intros a0 nn v H1 H2 H. apply (akept_vm W1 m1); [|exact H]. intros y Hy. apply GGS. clear - H1 H2 Hy. lia. }
  split; [apply GV; [| | exact VV1] | split; [apply GV; [| | exact VV2] | exact Ho]]; clear - Hi; unfold ASRC; lia. }
assert (GSK2 : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> ~ (dHA RG cx <= x < dHA RG cx + ASRC) ->
  abyte_kept (dxW cx) (dxmem cx) W2 m2 x)
  by (intros x H1 H2; exact (ga_bk_trans _ _ W1 m1 W2 m2 x (HGSK x H1 H2) (GGS x H1))).
match type of HOUT with aout_at B RG ly1 S1 W1 m1 ?c ?O ?mx ?no ?cap ?out =>
  assert (OUT2 : aout_at B RG ly2 S2 W2 m2 c O mx no cap out) end.
{ apply (aout_at_kept B RG ly1 S1 W1 m1 ly2 S2 W2 m2 _ _ _ _ _ _ HOUT).
  - intros r Hr x Hx. destruct (ga_out_fp _ _ r x Hr Hx) as [Hg | [Hg | (Hc & Hx2)]];
      [apply GK; left; exact Hg | apply GK; right; exact Hg |].
    apply (KO (out1, GSoc cx s1 p q) x).
    + unfold X, R. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
      unfold aout_blks. rewrite (proj2 (Z.eqb_neq _ _) Hc). left. reflexivity.
    + cbn [fst snd]. unfold req_size. rewrite (proj2 (Z.eqb_neq _ _) Hc). exact Hx2.
  - intros b Hb. apply X2. unfold X, R. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
    apply in_or_app. left. exact Hb. }
(* ---- the model: only the array size moved, to seen_ka ---- *)
assert (Hlen_eq : Z.of_nat (length (dlH cx s1 p)) = re_nheld e1).
{ pose proof HLINK as (_ & _ & _ & DH & _). unfold re_nheld. do 2 f_equal. cbn [drain_b_c.ds_H dvirt] in DH.
  rewrite <- DH, gs_keys_texts_len. reflexivity. }
destruct (gs_seen_begin_new (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q) xx 0%nat RelayRunF.adr0 [] Hges Hidx)
  as (_ & _ & Eka).
assert (EKA : 8 * re_nheld e1 + 8 = seen_ka (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q))
  by (rewrite Eka, <- Hlen_eq; ring).
(* ---- the meter ---- *)
pose proof HBUD as (Hle & Hsp & Hcost & Hlv & Hmax).
(* C3: the live bytes after realloc #2, exactly: the old held array (ent_ka bytes; none when s->held is NULL) replaced
   by the new one *)
assert (BB : blocks_bytes S2 = blocks_bytes S1 - drain_b_c.ent_ka e1 + (8 * re_nheld e1 + 8)).
{ rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ PN), (bsum_perm _ _ HPERM).
  unfold X, BUF, KEYS, NB, TB, R, aentry_blks, drain_b_c.ent_ka. rewrite !bsum_cons, !bsum_app. cbn [fst snd].
  destruct (Z.eqb_spec (re_hp e1) 0) as [Hz|Hz]; cbn [bsum fold_right snd]; clear - Hz; lia. }
assert (DB2 : dbud MT MMAX cx S2 (spent + (mo_malloc MT (8 * re_nheld e1 + 8) + mo_free MT))
  (RelayRunT.RMalloc (Z.of_nat (length xx) + 1) :: tl2)).
{ pose proof (mo_free_nonneg MT MTL) as Hf0.
  assert (Hm0 : 0 <= mo_malloc MT (8 * re_nheld e1 + 8)) by (apply (mo_malloc_nonneg MT MTL); clear - Hnh0; lia).
  assert (CT : tr_cost MT (RelayRunT.RMalloc (Z.of_nat (length xx) + 1) :: tl2) =
    (mo_malloc MT (Z.of_nat (length xx) + 1) + mo_free MT) + tr_cost MT tl2) by reflexivity.
  split; [exact (mle_station MT (dxS cx) S1 S2 spent _ MTL Hle Hmle2)|].
  split; [clear - Hsp Hf0 Hm0; lia|].
  split; [rewrite CT; clear - Hcost Etrc; lia|].
  split; [clear - Hlv Etra BB; lia|].
  clear - Hmax HmxT; lia. }
(* ---- the cut's core ---- *)
unfold GARB, LCORE. cbv zeta.
split.
{ unfold DMEM. cbn [dvirt drain_b_c.ds_ocap drain_b_c.ds_no].
  refine (conj HJ2 (conj ROM2 (conj PK2 (conj (eq_trans Hfr2 HFRM) (conj (ga_frame_kept cx W1 m1 W2 m2 FK HFRAME)
    (conj ENT2 (conj AWR2 (conj OKX2 (conj SRC2 (conj OTH2 (conj GSK2 (conj OUT2 (conj HLIVE _))))))))))))).
  exact PERM2. }
split; [exact (gb_dlink cx s1 false (dlH cx s1 p) (dlka cx s1 p) _ (GSno cx s1 p q) (GSoc cx s1 p q) e1 res
  (8 * re_nheld e1 + 8) h1 HLINK ltac:(clear - Hres4096; lia) EKA)|].
split.
{ pose proof HSAME as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & _).
  refine (conj T1 (conj T2 (conj T3 (conj T4 (conj T5 (conj T6 (conj T7 (conj T8 (conj T9 (or_intror _)))))))))).
  cbn [ga_entry re_kh]. clear - Hnh Hnh0. lia. }
split; [exact (gb_dhist _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HHIST)|].
split; [exact HRST | exact DB2].
Qed.

Theorem gs_adda : gs_addb_stmt B MT MMAX RG -> gs_add_stmt B MT MMAX RG.
Proof.
intros ADDB. unfold gs_add_stmt. intros cx s1 D p q W1 c1 HB HGA HN.
destruct HGA as (regs1 & ly1 & S1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & o & ha & ks & tl &
  kd & jj & bg & Hc1 & HRL & R23 & R24 & R25 & R19 & R10 & R11 & R12 & V72 & Hbgr & Hbgk & Hges & Hjj & Hidx &
  HGSF & HCORE & HFUT).
pose proof HCORE as (HDMEM & HLINK & HSAME & HHIST & HRSTART & HBUD).
pose proof HDMEM as (HJ & HROM & HPRES & HFRS & HFRAME & HENT & HAWR & HOKX & HSRC & HOTH & HKEPT & HOUT & HLIVE & HPERM).
pose proof HRL as (Usp & R3 & R4 & R22 & R27 & R18 & R9 & R8 & R21 & HFR2 & V192 & V200 & V56 & V48 & V64).
pose proof HFR2 as (F208 & F96 & F128 & _).
pose proof HB as (HPRE & HSA & HGin & HGle & HSAle & HGARR & HAWR0 & HENT0 & HB9 & HB10 & HB11 & HB12 & HB13 &
  HB14 & HB15 & HB16 & HPERM0 & HB18 & HB19 & HB20 & HB21 & HB22 & HMOK).
pose proof HJ as (_ & _ & (memS & HJi & HAG) & _).
pose proof (ajournal_gx_AR SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 W1 m1 md1 k1 HJ) as HAR1.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
rewrite !Z.add_0_r in Hal16, Hslo, Hshi, Hstk0.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : DRAIN_STK = 16848) by reflexivity.
assert (Has : ASTACK = 16384) by reflexivity.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (HGin1 : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym HPERM)); left; reflexivity).
destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 _ _ HAR1 HGin1) as (HG16 & HG4096 & HGceil & HGapp & HGpres & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
rewrite RQT in HGceil, HGapp, HGpres.
assert (HSAlo : 4096 <= dxSA cx) by (unfold ATABLE in HGle; lia).
assert (HSAhi : dxSA cx + 56 <= alloc_ceiling) by (unfold ATABLE, AENT in *; lia).
assert (HSAhiG : dxSA cx + 56 <= GA_HI) by (unfold GA_HI; lia).
assert (WF : DRAIN_FRAME = 336) by reflexivity.
(* the relay entry's fields *)
pose proof HOKX as (K1 & K2 & Kp1 & Kp2 & K5 & K6 & K7 & K8 & KBUF & KNH & KHP & KND1 & KND2 & KF).
assert (Hnh0 : 0 <= re_nheld e1) by (unfold re_nheld; lia).
assert (Hhp : 0 <= re_hp e1 <= GA_HI).
{ destruct KHP as [(Hz & _) | (Hnz & Hin & Hle & H8 & Hg)].
  - rewrite Hz. unfold GA_HI. lia.
  - destruct (al_blocks SEGS B LAWS ly1 S1 W1 m1 md1 _ _ HAR1 Hin) as (_ & H4 & Hc & _).
    assert (RQH : req_size (re_kh e1) = re_kh e1)
      by (unfold req_size; destruct (Z.eqb_spec (re_kh e1) 0); lia).
    rewrite RQH in Hc. unfold GA_HI. lia. }
(* the frame base, and the bounds the seat wants *)
assert (R2 : getr regs1 2 = w64 (dsp0 cx - DRAIN_FRAME)).
{ unfold w64. rewrite <- Usp. unfold spZ. symmetry. apply Z_to_bv_bv_unsigned. }
assert (Hsp46 : 2 ^ 46 <= dsp0 cx - DRAIN_FRAME) by (rewrite WF; lia).
assert (Hsp47 : dsp0 cx - DRAIN_FRAME + 336 <= 2 ^ 47) by (rewrite WF; lia).
assert (Hsp16 : (dsp0 cx - DRAIN_FRAME) mod 16 = 0)
  by (rewrite WF, Zminus_mod, Hal16; reflexivity).
assert (HSAsp : dxSA cx + 56 + 16512 <= dsp0 cx - DRAIN_FRAME) by (rewrite WF; lia).
(* the two cells of the entry, read off its byte image *)
assert (VH40 : val_mem SEGS (arm W1 m1) (dxSA cx + 40) 8 (re_hp e1))
  by (apply (gax_entry_hp W1 m1 _ e1 Kp1 ltac:(unfold GA_HI in *; lia) HENT)).
assert (VH48 : val_mem SEGS (arm W1 m1) (dxSA cx + 48) 4 (re_nheld e1))
  by (apply (gax_entry_nheld W1 m1 _ e1 Kp1 ltac:(lia) HENT)).
assert (HWR : forall oo, 40 <= oo < 52 -> writable_at SEGS (arm W1 m1) (dxSA cx + oo))
  by (intros oo Hoo; apply HAWR; unfold AENT; lia).
assert (Hnh26 : 0 <= re_nheld e1 <= 2 ^ 26) by lia.
(* the seat *)
pose proof (ga_seat W1 regs1 m1 (dxSA cx) (dsp0 cx - DRAIN_FRAME) (re_hp e1) (re_nheld e1)
  R2 R10 R11 R12 R21 R22 HSAlo HSAhiG HSAsp Hhp Hnh26 Hsp46 Hsp47 Hsp16
  V72 F96 F128 VH40 VH48 HWR) as HS.
remember (Eimg (Ereg regs1 (ga_extra (re_hp e1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EA : forall i, (i < 32)%nat -> ew E i = getr regs1 (Z_to_bv 5 (Z.of_nat i))).
{ intros i Hi. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). unfold Ereg. cbn [ew].
  destruct (Nat.ltb_spec i 32); [reflexivity | lia]. }
assert (E32 : ew E 32 = w64 (re_hp e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
clear HE.
assert (E2 : ew E 2 = w64 (dsp0 cx - DRAIN_FRAME)) by exact (eq_trans (EA 2%nat ltac:(lia)) R2).
assert (E3 : ew E 3 = getr regs1 3) by exact (EA 3%nat ltac:(lia)).
assert (E4 : ew E 4 = getr regs1 4) by exact (EA 4%nat ltac:(lia)).
assert (E10 : ew E 10 = w64 (re_nheld e1)) by exact (eq_trans (EA 10%nat ltac:(lia)) R10).
assert (E19 : ew E 19 = w64 bg) by exact (eq_trans (EA 19%nat ltac:(lia)) R19).
assert (E21 : ew E 21 = w64 SHADOW_OFF) by exact (eq_trans (EA 21%nat ltac:(lia)) R21).
assert (E22 : ew E 22 = w64 (dxSA cx)) by exact (eq_trans (EA 22%nat ltac:(lia)) R22).
assert (E23 : ew E 23 = w64 (re_buf e1 + Z.of_nat q)) by exact (eq_trans (EA 23%nat ltac:(lia)) R23).
assert (E24 : ew E 24 = w64 (re_buf e1 + Z.of_nat p)) by exact (eq_trans (EA 24%nat ltac:(lia)) R24).
assert (E25 : ew E 25 = w64 (re_buf e1 + Z.of_nat p + Z.of_nat jj)) by exact (eq_trans (EA 25%nat ltac:(lia)) R25).
assert (U22 : bv_unsigned (ew E 22) = dxSA cx)
  by (rewrite E22; apply unsigned_lit_small; unfold GA_HI in *; lia).
assert (SHOK : sh_ok SEGS gaBx ga_SH E (mrestrict (w_H W1) m1))
  by exact (ga_shok E ly1 S1 W1 m1 md1 (dxG cx) (dxSA cx) HAR1 HGin1 HGle HSAle E21 E22 HSAlo HSAhiG).
subst c1. unfold cfg_at.
(* 0x8389c  bnez s3: an END not held returns at once; a BEGIN continues *)
psrr_branch_tok RUN BR HS SHOK gaBspan;
  rename Hc into BZ; rewrite (ga_bnez E 19 bg E19 ltac:(lia)) in BZ.
- (* bg <> 0: an END whose key is not held.  Nothing is written and nothing is called: the branch itself
     is the jump to DLN (S q), and the model's seen_arr / seen_tr / seen_ka are all the identity. *)
  assert (Hbgn : bg <> 0)
    by (destruct (Z.eqb_spec bg 0); [cbn [negb] in BZ; discriminate | assumption]).
  assert (Hkd : kd = GEnd) by (destruct kd; [exfalso; apply Hbgn, Hbgk; reflexivity | reflexivity]).
  subst kd.
  pose proof HGSF as (HB1 & HPQ & HQ0 & HNZ & HKs & HLL).
  destruct (gs_drl s1 p q HB1 HPQ HQ0 HNZ HKs HLL) as (Edrl & Edrlq & Edskp).
  destruct (gs_seen_end_new (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q)
              (firstn jj (dline s1 p q)) jb ha ks Hges Hidx) as (Earr & Etr & Eka).
  unfold GSfut, dsfut in HFUT. cbv zeta in HFUT. rewrite Etr in HFUT.
  cbn [fst snd] in HFUT. rewrite Earr, Eka in HFUT.
  destruct HFUT as (tl2 & HLF & Htl). cbn [app] in Htl. subst tl.
  (* the branch itself (0x8389c -> 0x836f4): one instruction, no store *)
  paj_run_to_tok RUNTO HS HJ SHOK gaBspan A_dr_next.
  { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
      let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_x_cons; [intros aa Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U22 in Ha.
    left. split; [|lia]. right; left. split.
    - unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
      cbn [fst snd]. unfold AENT. lia.
    - exists (dxG cx), ATABLE. split; [exact HGin1|]. rewrite RQT. unfold AENT, ATABLE in *. lia. }
  rename HFr into HFrE, HG0 into HGrE. clear HF.
  lazymatch goal with |- SRr _ _ (mkCfg ?mm ?mo) _ => rename mm into msE; set (matE := mo) in * end.
  (* every byte keeps its view: outside the entry's window by the run's frame, inside it because the two
     chunks the seat put there (s->held, s->nheld) are still the ones the region holds *)
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as REE. cbn [ms_mem restrict] in REE.
  assert (VE40 : val_mem SEGS (mrestrict (w_H W1) (ms_mem msE)) (dxSA cx + 40) (N.to_nat 8) (re_hp e1)).
  { eapply (field_of_region E _ 22 (dxSA cx)); [exact REE | exact U22 | ga_in | | unfold GA_HI in *; zside | zside].
    cbn [sv_denot]. rewrite E32, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (VE48 : val_mem SEGS (mrestrict (w_H W1) (ms_mem msE)) (dxSA cx + 48) (N.to_nat 4) (re_nheld e1)).
  { eapply (field_of_region E _ 22 (dxSA cx)); [exact REE | exact U22 | ga_in | | zside | zside].
    cbn [sv_denot]. rewrite E10, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  change (N.to_nat 8) with 8%nat in VE40. change (N.to_nat 4) with 4%nat in VE48.
  unfold arm in VH40, VH48.
  assert (KLE : forall x, 0 <= x < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem msE) x = aview SEGS (w_H W1) m1 x).
  { intros x Hx.
    assert (OUT : ~ (dxSA cx + 40 <= x < dxSA cx + 52) ->
                  aview SEGS (w_H W1) (ms_mem msE) x = aview SEGS (w_H W1) m1 x).
    { intros Hno. apply (aview_kept_out E _ (w_H W1) m1 (ms_mem msE) HFrE x Hx). apply ga_not_wrange.
      lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end.
      repeat constructor; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?U22; lia. }
    destruct (Z.lt_ge_cases x (dxSA cx + 40)) as [H1|H1]; [apply OUT; lia|].
    destruct (Z.lt_ge_cases x (dxSA cx + 52)) as [H2|H2]; [|apply OUT; lia].
    destruct (Z.lt_ge_cases x (dxSA cx + 48)) as [H3|H3].
    - replace x with (dxSA cx + 40 + Z.of_nat (Z.to_nat (x - (dxSA cx + 40)))) by lia.
      unfold aview. rewrite (VE40 (Z.to_nat (x - (dxSA cx + 40))) ltac:(lia)).
      rewrite (VH40 (Z.to_nat (x - (dxSA cx + 40))) ltac:(lia)). reflexivity.
    - replace x with (dxSA cx + 48 + Z.of_nat (Z.to_nat (x - (dxSA cx + 48)))) by lia.
      unfold aview. rewrite (VE48 (Z.to_nat (x - (dxSA cx + 48))) ltac:(lia)).
      rewrite (VH48 (Z.to_nat (x - (dxSA cx + 48))) ltac:(lia)). reflexivity. }
  assert (GRE : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msE) x)
    by (intros x Hp; exact (apresent_grows _ _ _ _ HGrE Hp)).
  assert (HHAb : rg_s RG <= dHA RG cx /\ dHA RG cx + ASRC <= rg_s RG + 4 * ASRC)
    by (unfold dHA, ASRC in *; lia).
  assert (HCOREE := ga_lcore_mem cx s1 D _ _ _ _ _ _ _ _ ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl2
    (ms_mem msE) matE HCORE HAR1 HJ KLE GRE ltac:(rewrite WF; lia) ltac:(lia) HSAlo
    ltac:(unfold AENT; lia) (proj1 HHAb) (proj2 HHAb)).
  pose proof HCOREE as (HDME & _). pose proof HDME as (_ & _ & _ & _ & HFRE & _).
  pmkst HS.
  prreg HS (2%bv : bv 5) X2. prreg HS (3%bv : bv 5) X3. prreg HS (4%bv : bv 5) X4.
  prreg HS (8%bv : bv 5) X8. prreg HS (9%bv : bv 5) X9. prreg HS (18%bv : bv 5) X18.
  prreg HS (21%bv : bv 5) X21. prreg HS (22%bv : bv 5) X22. prreg HS (23%bv : bv 5) X23.
  prreg HS (27%bv : bv 5) X27.
  assert (VKE : forall aa n v, 0 <= aa -> aa + Z.of_nat n <= 2 ^ 64 ->
                val_mem SEGS (arm W1 m1) aa n v -> val_mem SEGS (arm W1 (ms_mem msE)) aa n v)
    by (intros aa n v H1 H2 Hv; exact (ga_val_kept W1 m1 (ms_mem msE) aa n v KLE H1 H2 Hv)).
  apply HN. unfold DLN.
  exists (ms_regs msE), ly1, S1, (ms_mem msE), matE, k1, e1, h1, out1, ev1, LB1, spent.
  exists (jb + dnret (@nil (RelayRunT.rev YO0i.sptr)))%nat, a, o, ha, ks, tl2.
  split; [reflexivity|].
  split.
  { split; [unfold spZ; rewrite X2, E2; unfold w64; rewrite unsigned_lit_small by (rewrite WF; lia); reflexivity|].
    split; [rewrite X3, E3; exact R3|]. split; [rewrite X4, E4; exact R4|].
    split; [rewrite X22; exact E22|].
    split; [rewrite X27; exact (eq_trans (EA 27%nat ltac:(lia)) R27)|].
    split; [rewrite X18; exact (eq_trans (EA 18%nat ltac:(lia)) R18)|].
    split; [rewrite X9; exact (eq_trans (EA 9%nat ltac:(lia)) R9)|].
    split; [rewrite X8; exact (eq_trans (EA 8%nat ltac:(lia)) R8)|].
    split; [rewrite X21; exact E21|].
    split; [exact HFRE|].
    split; [apply VKE; [rewrite WF; lia | rewrite WF; lia | exact V192]|].
    split; [apply VKE; [rewrite WF; lia | rewrite WF; lia | exact V200]|].
    split; [apply VKE; [rewrite WF; lia | rewrite WF; lia | exact V56]|].
    split; [apply VKE; [rewrite WF; lia | rewrite WF; lia | exact V48]|].
    apply VKE; [rewrite WF; lia | rewrite WF; lia | exact V64]. }
  split; [rewrite X23, E23; f_equal; lia|].
  split; [split; [lia | right; replace (S q - 1)%nat with q by lia; exact HQ0]|].
  split; [lia|].
  split.
  + unfold DLC. rewrite Edrl, Edskp, (gs_dlH cx s1 p q Edrl), (gs_dlka cx s1 p q Edrl),
      (gs_dlno s1 p q Edrl), (gs_dloc cx s1 p q Edrl), Earr, Eka.
    unfold GSB, GSno, GSoc in HCOREE.
    eapply ga_lcore_end; [exact HCOREE | exact Hges | exact Hidx | lia | apply app_assoc].
  + unfold GSno, GSoc. rewrite (gs_dlH cx s1 p q Edrl), (gs_dlka cx s1 p q Edrl),
      (gs_dlno s1 p q Edrl), (gs_dloc cx s1 p q Edrl), Earr, Eka. exact HLF.
- (* bg = 0: a BEGIN not held *)
  assert (Hbg0 : bg = 0) by (destruct (Z.eqb_spec bg 0); [assumption | cbn [negb] in BZ; discriminate]).
  (* 0x838a0 .. 0x838c0: `bne a0, a1` is never taken (both hold s->nheld, one atom), the shadow byte of
     &s->held is covered and zero, a0 = s->held, a1 = 8 * nheld + 8, then the jal to realloc *)
  paj_run_tok RUN HS HJ SHOK gaBspan.
  { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
      let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_x_cons; [intros aa Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U22 in Ha.
    left. split; [|lia]. right; left. split.
    - unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
      cbn [fst snd]. unfold AENT. lia.
    - exists (dxG cx), ATABLE. split; [exact HGin1|]. rewrite RQT. unfold AENT, ATABLE in *. lia. }
  rename HFr into HFr1, HG0 into HGr1. clear HF.
  lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into ms1 end.
  pmkst HS.
  prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (1%bv : bv 5) P1.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8.
  (* the call's register values (K*/Hnh*/Hhp/VH* are in scope from the seat setup above) *)
  pose proof HPRE as (HAR0 & Hraok & Hra4 & Hgp0 & Htp0 & Hstk0p & Hpres0 & Hch0 & HQT0).
  assert (P11v : getr (ms_regs ms1) 11 = w64 (8 * re_nheld e1 + 8)).
  { rewrite P11, E10. unfold w64. rewrite !zalu64_sound. f_equal.
    unfold zalu64, zcanon, M64. cbn [zalu_raw].
    rewrite (Z.mod_small (re_nheld e1)) by lia.
    replace (Z.land (3 mod 2 ^ 64) 63) with 3 by (vm_compute; reflexivity).
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
    rewrite !Z.mod_mod by lia.
    rewrite (Z.mod_small (re_nheld e1 * 8)) by lia.
    replace (8 mod 2 ^ 64) with 8 by (vm_compute; reflexivity).
    rewrite Z.mod_small by lia. lia. }
  assert (P10v : getr (ms_regs ms1) 10 = w64 (re_hp e1)) by (rewrite P10, E32; reflexivity).
  assert (P3v : getr (ms_regs ms1) 3 = w64 (as_gp B)) by (rewrite P3, E3, R3; exact Hgp0).
  assert (P4v : getr (ms_regs ms1) 4 = w64 (as_tp B)) by (rewrite P4, E4, R4; exact Htp0).
  assert (Usp1 : spZ (ms_regs ms1) = dsp0 cx - DRAIN_FRAME)
    by (unfold spZ; rewrite P2, E2; unfold w64; rewrite unsigned_lit_small by (rewrite WF; lia); reflexivity).
  (* the model: kd = GBegin (bg = 0), so seen_tr owes the realloc then the strndup *)
  assert (Hkd : kd = GBegin) by (apply (proj1 Hbgk); exact Hbg0). subst kd.
  pose proof HGSF as (HB1 & HPQ & HQ0 & HNZ & HKs & HLL).
  pose proof HLINK as (_ & _ & _ & DH & Dka & _ & _ & _ & _ & Den & Decap & _).
  assert (Hlen_eq : Z.of_nat (length (dlH cx s1 p)) = re_nheld e1).
  { unfold re_nheld. do 2 f_equal. cbn [drain_b_c.ds_H dvirt] in DH.
    rewrite <- DH, gs_keys_texts_len. reflexivity. }
  set (x := firstn jj (dline s1 p q)) in *.
  (* tr_sizes_ok tl, from DrLines' W_drain_tr.v: the DGS cut's dnext signs, then gs_dsfut_sizes *)
  pose proof (gs_cut_facts B MT MMAX RG cx s1 D _ _ _ _ _ _ _ _ ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl HCORE)
    as (Hu0 & Hcap0 & Hmx0 & Hno0 & Hoc0 & Hka0 & Hen0 & Hec0).
  pose proof (gs_dgs_dnext_signs B MT MMAX RG cx s1 D _ _ _ _ _ _ _ _ ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl p q
    HB1 HPQ HQ0 HNZ HKs HLL eq_refl eq_refl (fun h => h) HCORE)
    as (HocG & Hcapn & Hocapn & Hnon & Henn & Hecapn & Hkan).
  assert (SZtl : tr_sizes_ok tl).
  { apply (gs_dsfut_sizes cx (dnext (dlive cx) (dxmx cx) s1) a (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q)
      (GSno cx s1 p q) (GSoc cx s1 p q) (drlq s1 (S q)) jb o ha ks tl
      Hmx0 HocG Hcapn Hocapn Hnon Henn Hecapn Hkan). unfold GSfut in HFUT. exact HFUT. }
  unfold GSfut, dsfut in HFUT. cbv zeta in HFUT.
  rewrite (proj1 (proj2 (gs_seen_begin_new (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q) x jb ha ks Hges Hidx))) in HFUT.
  cbn [fst snd] in HFUT. destruct HFUT as (tl2 & HLF & Htl).
  pose proof HBUD as (Hmle & Hsp0b & Hcost & Hbb & Hmx).
  rewrite Htl in SZtl.
  unfold tr_sizes_ok in SZtl. pose proof (Forall_inv_tail (Forall_inv_tail SZtl)) as SZtl2.
  assert (HnH : (Z.of_nat (length (dlH cx s1 p)) + 1) * 8 = 8 * re_nheld e1 + 8) by (rewrite Hlen_eq; ring).
  assert (Hcost2 : 0 <= tr_cost MT tl2) by (apply gs_tr_cost_nonneg; [exact MTL | exact SZtl2]).
  assert (Hmf : 0 <= mo_free MT) by (apply (mo_free_nonneg MT MTL)).
  assert (Hmm : 0 <= mo_malloc MT (Z.of_nat (length x) + 1)) by (apply (mo_malloc_nonneg MT MTL); lia).
  assert (Hmm2 : 0 <= mo_malloc MT (8 * re_nheld e1 + 8)) by (apply (mo_malloc_nonneg MT MTL); lia).
  assert (CTm : forall n (t : dtrace), tr_cost MT (RelayRunT.RMalloc n :: t) = (mo_malloc MT n + mo_free MT) + tr_cost MT t) by reflexivity.
  assert (CTr : forall k n aa (t : dtrace), tr_cost MT (RelayRunT.RRealloc k n aa :: t) = (mo_malloc MT n + mo_free MT) + tr_cost MT t) by reflexivity.
  assert (MTm : forall n (t : dtrace), tr_max (RelayRunT.RMalloc n :: t) = Z.max n (tr_max t)) by reflexivity.
  assert (MTr : forall k n aa (t : dtrace), tr_max (RelayRunT.RRealloc k n aa :: t) = Z.max n (tr_max t)) by reflexivity.
  (* C3: the trace still owed opens with realloc #2 (malloc when s->held is NULL), whose net change is the new array
     less the old (ent_ka), then strndup's request: the peak relation gb_garb's meter takes (W_tr_peak.v
     tr_peak_malloc / tr_peak_realloc) *)
  assert (Etra : (8 * re_nheld e1 + 8) - drain_b_c.ent_ka e1 +
    tr_peak (RelayRunT.RMalloc (Z.of_nat (length x) + 1) :: tl2) <= tr_peak tl).
  { pose proof Dka as Dka'. cbn [drain_b_c.ds_ka dvirt] in Dka'. rewrite Dka', Htl, <- HnH. cbn [app].
    pose proof (W_tr_peak.tr_peak_nonneg (RelayRunT.RMalloc (Z.of_nat (length x) + 1) :: tl2)) as P0.
    destruct (Z.eqb_spec (dlka cx s1 p) 0) as [Ek|Ek];
      [rewrite (W_tr_peak.tr_peak_malloc ((Z.of_nat (length (dlH cx s1 p)) + 1) * 8))
      |rewrite (W_tr_peak.tr_peak_realloc (dlka cx s1 p))]; lia. }
  assert (Etrc : tr_cost MT tl =
    (mo_malloc MT (8 * re_nheld e1 + 8) + mo_free MT)
    + ((mo_malloc MT (Z.of_nat (length x) + 1) + mo_free MT) + tr_cost MT tl2)).
  { rewrite Htl. destruct (dlka cx s1 p =? 0);
      repeat first [rewrite CTm | rewrite CTr]; rewrite HnH; reflexivity. }
  assert (HnMMAX : 8 * re_nheld e1 + 8 < MMAX).
  { eapply Z.le_lt_trans; [|exact Hmx]. rewrite Htl.
    destruct (dlka cx s1 p =? 0);
      repeat first [rewrite MTm | rewrite MTr]; rewrite HnH; apply Z.le_max_l. }
  (* realloc #2's live-bytes premise: its new array on top of the live bytes, the old one still live *)
  assert (HbbN : blocks_bytes S1 + (8 * re_nheld e1 + 8) <= LIVE_MAX).
  { assert (Pk1 : 8 * re_nheld e1 + 8 <= tr_peak tl).
    { rewrite Htl, <- HnH. cbn [app].
      pose proof (W_tr_peak.tr_peak_nonneg (RelayRunT.RMalloc (Z.of_nat (length x) + 1) :: tl2)) as P0.
      destruct (dlka cx s1 p =? 0);
        [rewrite (W_tr_peak.tr_peak_malloc ((Z.of_nat (length (dlH cx s1 p)) + 1) * 8))
        |rewrite (W_tr_peak.tr_peak_realloc (dlka cx s1 p))]; lia. }
    lia. }
  assert (DBmook : mo_ok MT (dxS cx) (dcost MT cx)).
  { pose proof HB as DB.
    destruct DB as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& Hmook). exact Hmook. }
  assert (HmokN : mo_ok MT S1 (mo_malloc MT (8 * re_nheld e1 + 8) + mo_free MT)).
  { apply (mok_station MT (dxS cx) S1 (dcost MT cx) spent
      (mo_malloc MT (8 * re_nheld e1 + 8) + mo_free MT)).
    - exact MTL.
    - exact DBmook.
    - exact Hmle.
    - lia.
    - rewrite Etrc in Hcost. lia. }
  assert (HoldFP : re_hp e1 <> 0 -> In (re_hp e1, re_kh e1) (ablocks B (dxly cx) (dxS cx)) ->
          forall i, 0 <= i < req_size (re_kh e1) -> inFP (dFP cx) (re_hp e1 + i)).
  { intros Hnz Hin0 i Hi.
    destruct KHP as [(Hz & _)|(_ & _ & _ & Hk2 & _)]; [contradiction|].
    assert (HHae : In (re_hp e1, re_kh e1) (aentry_blks e1)).
    { unfold aentry_blks. apply in_or_app; right. apply in_or_app; left.
      rewrite (proj2 (Z.eqb_neq (re_hp e1) 0) Hnz). apply in_eq. }
    exact (ga_fp cx ly1 S1 W1 m1 md1 e1 h1 _ out1 _ _ HAR1 HPERM HPERM0 HHae ltac:(lia) Hin0 i Hi). }
  destruct HJ as (_ & _ & (memS2 & HJi2 & HAG2) & _). rewrite !Z.add_0_r in HJi2.
  eapply SRr_bind.
  { eapply (AREALLOC W1 (ms_regs ms1) (ms_mem ms1) DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx)
      memS2 (dxmd cx) [] ly1 S1 _ k1 (re_hp e1) (re_kh e1) (8 * re_nheld e1 + 8) (- DRAIN_FRAME) _ [] HJi2).
    - destruct KHP as [(Hz & _)|(_ & Hin & _)]; [left; exact Hz | right; exact Hin].
    - exact P10v.
    - exact P11v.
    - lia.
    - exact HbbN.
    - rewrite Usp1. unfold DRAIN_FRAME. ring.
    - vm_compute; reflexivity.
    - unfold DRAIN_FRAME; lia.
    - rewrite Has, WS, WF. lia.
    - exact P3v.
    - exact P4v.
    - exact P1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - pose proof HGSB as (HG1 & HG2 & _).
      assert (HD8 : 0 <= (rg_s RG + 4) / 8 <= rg_s RG + 4)
        by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
      apply (achain_chain_pre ly1 _ (dsp0 cx - DRAIN_FRAME) ((rg_s RG + 4) / 8) [] (ms_regs ms1)).
      + apply achain_low. unfold ASRC in *. lia.
      + rewrite Usp1, WF. lia.
      + unfold s0Z. rewrite P8, (eq_trans (EA 8%nat ltac:(lia)) R8). unfold w64.
        apply unsigned_lit_small. unfold ASRC in *. lia.
      + unfold raZ. rewrite P1. rewrite unsigned_lit_small by lia. lia.
    - exact HoldFP.
    - exact HmokN. }
  cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2i & HPR2 & Hres10 & Hfr2 &
    Hres4096 & HpermZ & HpermN & Hcopy & Hkept2 & Hmle2 & Herr2 & Hpres2).
  pose proof (proj1 HJ2i) as HAR2.
  assert (Hres0 : res <> 0) by lia.
  assert (RQ2 : req_size (8 * re_nheld e1 + 8) = 8 * re_nheld e1 + 8)
    by (unfold req_size; destruct (Z.eqb_spec (8 * re_nheld e1 + 8) 0); lia).
  (* the live blocks after realloc #2: the entry's held array is the new block *)
  match type of HPERM with Permutation _ (_ :: aentry_blks _ ++ ?r) => pose (R := r) end.
  pose (BUF := if re_cap e1 =? 0 then [] else [(re_buf e1, re_cap e1)]).
  pose (KEYS := map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e1)).
  pose (NEW := (res, 8 * re_nheld e1 + 8)).
  pose (TBL := (dxG cx, ATABLE)).
  assert (EA2 : aentry_blks (ga_entry e1 res (8 * re_nheld e1 + 8)) = BUF ++ NEW :: KEYS).
  { unfold ga_entry, aentry_blks, BUF, KEYS, NEW. cbn [re_cap re_buf re_hp re_kh re_keys].
    rewrite (proj2 (Z.eqb_neq res 0) Hres0). reflexivity. }
  assert (BASEP : Permutation (ablocks B ly2 S2) (NEW :: TBL :: (BUF ++ KEYS ++ R))).
  { destruct (Z.eqb_spec (re_hp e1) 0) as [Hz | Hnz].
    - assert (EA1 : aentry_blks e1 = BUF ++ KEYS)
        by (unfold aentry_blks, BUF, KEYS; rewrite Hz; reflexivity).
      eapply Permutation_trans; [exact (HpermZ Hz)|]. apply perm_skip.
      eapply Permutation_trans; [exact HPERM|]. apply perm_skip.
      rewrite EA1, <- app_assoc. apply Permutation_refl.
    - assert (EA1 : aentry_blks e1 = BUF ++ (re_hp e1, re_kh e1) :: KEYS)
        by (unfold aentry_blks, BUF, KEYS; rewrite (proj2 (Z.eqb_neq (re_hp e1) 0) Hnz); reflexivity).
      destruct (HpermN Hnz) as (l1 & l2 & Ebl1 & Ebl2).
      eapply Permutation_trans; [exact Ebl2|]. apply perm_skip.
      apply (Permutation_cons_inv (a := (re_hp e1, re_kh e1))).
      eapply Permutation_trans; [apply Permutation_middle|].
      rewrite <- Ebl1.
      eapply Permutation_trans; [exact HPERM|].
      rewrite EA1, <- app_assoc.
      eapply Permutation_trans; [apply perm_skip; apply Permutation_sym, Permutation_middle|].
      apply perm_swap. }
  assert (PERM2 : Permutation (ablocks B ly2 S2)
    (TBL :: aentry_blks (ga_entry e1 res (8 * re_nheld e1 + 8)) ++ R)).
  { eapply Permutation_trans; [exact BASEP|].
    eapply Permutation_trans; [apply perm_swap|]. apply perm_skip.
    rewrite EA2, <- app_assoc. change ((NEW :: KEYS) ++ R) with (NEW :: (KEYS ++ R)).
    apply Permutation_middle. }
  assert (HGin2 : In TBL (ablocks B ly2 S2))
    by (apply (Permutation_in _ (Permutation_sym BASEP)); right; left; reflexivity).
  assert (HNin2 : In NEW (ablocks B ly2 S2))
    by (apply (Permutation_in _ (Permutation_sym BASEP)); left; reflexivity).
  (* the table block is apart from the new block and from the old held array *)
  assert (DTN : zdisjoint (block_rng NEW) (block_rng TBL))
    by exact (ga_sep_head ly2 S2 W2 mem2 md2 NEW (TBL :: BUF ++ KEYS ++ R) TBL HAR2 BASEP (or_introl eq_refl)).
  assert (DTH : re_hp e1 <> 0 -> zdisjoint (block_rng TBL) (block_rng (re_hp e1, re_kh e1))).
  { intros Hnz. apply (ga_sep_head ly1 S1 W1 m1 md1 TBL (aentry_blks e1 ++ R) _ HAR1 HPERM).
    apply in_or_app; left. unfold aentry_blks. apply in_or_app; right. apply in_or_app; left.
    rewrite (proj2 (Z.eqb_neq (re_hp e1) 0) Hnz). apply in_eq. }
  assert (NOEXC : forall aa, dxG cx <= aa < dxG cx + req_size ATABLE ->
    ~ ((res <= aa < res + req_size (8 * re_nheld e1 + 8)) \/
       (re_hp e1 <> 0 /\ re_hp e1 <= aa < re_hp e1 + req_size (re_kh e1)))).
  { intros aa Haa [Hx | (Hnz & Hx)].
    - unfold zdisjoint, block_rng in DTN. unfold NEW, TBL in DTN. cbn [fst snd] in DTN.
      rewrite RQ2 in Hx. rewrite RQT in Haa. lia.
    - pose proof (DTH Hnz) as DD. unfold zdisjoint, block_rng, TBL in DD. cbn [fst snd] in DD.
      rewrite RQT in Haa, DD. lia. }
  assert (B2 : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME)
    by (rewrite E2; apply unsigned_lit_small; rewrite WF; lia).
  jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W2) mem2) HPR2 [0; 1]%nat HS2.
  match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
    - eapply region_kept_stack_aj; [exact Hkept2 | exact HJ2i | exact B2 | ..]; rewrite ?WS, ?WF, ?Has; lia.
    - apply (ga_kept_blk E ly1 S1 W1 (ms_mem ms1) W2 mem2 _ _ _ ly2 S2 md2 22 0 56 40 52 _ (dxG cx) ATABLE
        (dxSA cx) Hkept2 HAR2 HGin2 U22 HGin1); rewrite ?RQT;
      [ unfold AENT, ATABLE in *; lia | unfold AENT, ATABLE in *; lia | lia | lia
      | cbv beta; intros aa Haa; apply NOEXC; rewrite RQT; exact Haa ]. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc E 48 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
  assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLDa : forall mm, (mm < 48)%nat -> ew Ea mm = ew E mm)
    by (intros mm Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
  assert (Ea52 : ew Ea 52 = w64 res).
  { rewrite HEa. replace 52%nat with (48 + 4)%nat by lia.
    rewrite (ew_havoc_new E 48 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0)) by (cbv; lia).
    unfold CLOB. cbn [map nth]. exact Hres10. }
  clear HEa.
  assert (B22a : bv_unsigned (ew Ea 22) = dxSA cx) by (rewrite OLDa by lia; exact U22).
  assert (UBxa : U Ea gaBx = SHADOW_OFF)
    by (unfold gaBx, U; cbn [sv_denot]; rewrite OLDa by lia; rewrite E21, Z.add_0_r;
        unfold w64; rewrite Z_to_bv_bv_unsigned; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (HJ2 : @ajournal_gx _ SK SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly2 S2 W2 mem2 md2 (k1 + 3)).
  { apply (ajournal_gx_pack SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) (dxW cx)
      (dxmem cx) (dxmd cx) [] ly2 S2 W2 mem2 md2 (k1 + 3) memS2);
      [lia | lia | rewrite !Z.add_0_r; exact HJ2i | exact HAG2 | intros aa Haa; lia]. }
  assert (SHOK2 : sh_ok SEGS gaBx ga_SH Ea (mrestrict (w_H W2) mem2)).
  { unfold sh_ok, ga_SH. constructor; [|constructor].
    apply (ga_shent Ea ly2 S2 W2 mem2 md2 (dxG cx) ATABLE 22 (dxSA cx) 0 56 HAR2 HGin2 UBxa
      ltac:(unfold U; cbn [sv_denot]; rewrite OLDa by lia; rewrite E22, Z.add_0_r; unfold w64;
            rewrite Z_to_bv_bv_unsigned; apply unsigned_lit_small; unfold GA_HI in *; lia));
      rewrite ?RQT; unfold AENT, ATABLE in *; lia. }
  destruct (al_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 HNin2) as (Hres16 & _ & Hresceil & Hresapp & Hrespres & _).
  rewrite RQ2 in Hresceil, Hresapp, Hrespres.
  assert (Hres64 : 0 <= res < 2 ^ 64) by lia.
  (* 0x838c4 beqz a0: realloc returned a block, not NULL *)
  psrr_branch_tok RUN BR HS SHOK2 gaBspan;
    rename Hc into BZ2;
    rewrite (ga_beqz_pos Ea 52 res Ea52 Hres64 Hres4096) in BZ2.
  { discriminate. }
  (* 0x838c8 .. 0x838d4: the shadow byte of &s->held is 0, then s->held = res *)
  paj_run_to_tok RUNTO HS HJ2 SHOK2 gaBspan A_dr_addb.
  { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
      let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_x_cons; [intros aa Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite B22a in Ha.
    left. split; [|lia]. right; left. split.
    - unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
      cbn [fst snd]. unfold AENT. lia.
    - exists (dxG cx), ATABLE. split; [exact HGin2|]. rewrite RQT. unfold AENT, ATABLE in *. lia. }
  rename HFr into HFr2, HG0 into HGr2. clear HF.
  lazymatch goal with |- SRr _ _ (mkCfg ?mm ?mo) _ => rename mm into msf; set (matf := mo) in * end.
  pmkst HS.
  prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4.
  prreg HS (8%bv : bv 5) F8. prreg HS (9%bv : bv 5) F9. prreg HS (18%bv : bv 5) F18.
  prreg HS (21%bv : bv 5) F21. prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23.
  prreg HS (24%bv : bv 5) F24. prreg HS (25%bv : bv 5) F25. prreg HS (27%bv : bv 5) F27.
  (* s3 keeps the shadow address of &s->held it entered with *)
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H Ev ss ms 19%bv HS) as F19;
    let e := eval vm_compute in (sr_get (ss_regs ss) 19%bv) in change (sr_get (ss_regs ss) 19%bv) with e in F19;
    set (Ef := Ev) in HS, F19 end.
  cbn [ms_regs restrict mkst] in F19.
  assert (UF : forall mm, (mm < 512)%nat -> ew Ef mm = ew Ea mm)
    by (intros mm Hm; subst Ef; rewrite ?ew_ewset_other by lia; reflexivity).
  assert (EF : forall mm, (mm < 48)%nat -> ew Ef mm = ew E mm)
    by (intros mm Hm; rewrite UF by lia; exact (OLDa mm Hm)).
  assert (Ef21 : ew Ef 21 = w64 SHADOW_OFF) by (rewrite EF by lia; exact E21).
  assert (Ef22 : ew Ef 22 = w64 (dxSA cx)) by (rewrite EF by lia; exact E22).
  assert (U21f : U Ef (SOff 21 0) = SHADOW_OFF)
    by (apply (U_atom Ef 21 _ Ef21); unfold SHADOW_OFF; lia).
  assert (HD40f : 0 <= (dxSA cx + 40) / 8 <= dxSA cx + 40)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (US40f : U Ef (SAlu ALU_SRL (SOff 22 40) (SLit 3)) = (dxSA cx + 40) / 8)
    by (apply (ga_den_srl3 Ef 22 (dxSA cx) 40 Ef22); unfold GA_HI in *; lia).
  (* every byte outside the two cells this arm writes keeps its view, across both runs and the call *)
  assert (KR1 : forall aa, 0 <= aa < 2 ^ 64 -> ~ (dxSA cx + 40 <= aa < dxSA cx + 52) ->
    aview SEGS (w_H W1) (ms_mem ms1) aa = aview SEGS (w_H W1) m1 aa).
  { intros aa Ha Hno. apply (aview_kept_out E _ (w_H W1) m1 (ms_mem ms1) HFr1 aa Ha). apply ga_not_wrange.
    lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end.
    repeat constructor; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?U22; lia. }
  assert (KR2 : forall aa, 0 <= aa < 2 ^ 64 -> ~ (dxSA cx + 40 <= aa < dxSA cx + 52) ->
    aview SEGS (w_H W2) (ms_mem msf) aa = aview SEGS (w_H W2) mem2 aa).
  { intros aa Ha Hno. apply (aview_kept_out Ea _ (w_H W2) mem2 (ms_mem msf) HFr2 aa Ha). apply ga_not_wrange.
    lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end.
    repeat constructor; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?B22a; lia. }
  pose proof Hkept2 as (KC1 & KC2 & KC3 & KC4 & KC5 & KC6).
  assert (FK : forall aa, dsp0 cx - DRAIN_FRAME <= aa < dsp0 cx -> abyte_kept W1 m1 W2 (ms_mem msf) aa).
  { intros aa Haa.
    assert (Hr : 0 <= aa < 2 ^ 64) by (rewrite WF in *; lia).
    assert (Hno : ~ (dxSA cx + 40 <= aa < dxSA cx + 52))
      by (unfold GA_HI in *; rewrite WF in *; lia).
    split.
    - rewrite (KR2 aa Hr Hno), (KC1 aa ltac:(rewrite WF in *; lia) ltac:(rewrite WF, Has in *; lia)).
      exact (KR1 aa Hr Hno).
    - intros Hw. apply (ga_writable_kept (w_H W1) (w_H W2) m1 (ms_mem msf) aa); [|exact Hw].
      intros Hp. apply (ga_apresent_grows _ _ _ _ HGr2).
      apply (KC5 aa ltac:(rewrite WF in *; lia) ltac:(rewrite WF, Has in *; lia)).
      exact (ga_apresent_grows _ _ _ _ HGr1 Hp). }
  (* rom_view at the cut: GAR carries it on its own and inside GARB's DMEM *)
  assert (ROM2 : rom_view SEGS W2 (ms_mem msf)).
  { pose proof (ajournal_gx_AR SEGS B (G_DR B RG) 0 [] DRAIN_STK (dsp0 cx) (dFP cx)
      (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxmd cx) [] ly2 S2 W2 (ms_mem msf) matf (k1 + 3) HJ2) as HAR2f.
    assert (HKI : forall xx, in_img SEGS xx -> ~ Exists (in_zr xx) (as_owned_static B) ->
      ~ (as_errno B <= xx < as_errno B + 4) ->
      aview SEGS (w_H W2) (ms_mem msf) xx = aview SEGS (w_H W1) m1 xx).
    { intros xx Hi Hno Hne.
      assert (Hr : 0 <= xx < 2 ^ 64) by (pose proof (pa_segs_low xx Hi); unfold kLowMemEnd in *; lia).
      assert (Hno2 : ~ (dxSA cx + 40 <= xx < dxSA cx + 52)).
      { intros Hx. exact (blk_img SEGS B LAWS ly1 S1 W1 m1 md1 _ _ xx HAR1 HGin1
          ltac:(rewrite RQT; unfold AENT, ATABLE in *; lia) Hi). }
      rewrite (KR2 xx Hr Hno2), (KC3 xx Hi Hno Hne). exact (KR1 xx Hr Hno2). }
    intros xx Hx. destruct (HROMO xx Hx) as (_ & Hpin & Hne & _).
    destruct (Exists_dec (in_zr xx) (as_owned_static B) (ga_in_zr_dec xx)) as [Hown | Hno].
    - eapply rom_pinned_view; [exact HAR2f | exact (Hpin Hown)].
    - assert (Hi : in_img SEGS xx)
        by (destruct Hx as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
      rewrite (HKI xx Hi Hno Hne). exact (HROM xx Hx). }
  (* the GAR cut *)
  apply (ADDB cx s1 D p q W2 _ HB); [|exact HN].
  unfold GAR.
  exists (ms_regs msf), ly2, S2, (ms_mem msf), matf, (k1 + 3),
    (ga_entry e1 res (8 * re_nheld e1 + 8)), h1, out1, ev1, LB1,
    (spent + (mo_malloc MT (8 * re_nheld e1 + 8) + mo_free MT)), a,
    (RelayRunT.RMalloc (Z.of_nat (length x) + 1) :: tl2), jj.
  split; [reflexivity|].
  split.
  { apply (ga_dregs_kept cx regs1 (ms_regs msf) W1 m1 W2 (ms_mem msf) HRL);
    [ rewrite F2, EF by lia; exact (EA 2%nat ltac:(lia))
    | rewrite F3, EF by lia; exact (EA 3%nat ltac:(lia))
    | rewrite F4, EF by lia; exact (EA 4%nat ltac:(lia))
    | rewrite F22, EF by lia; exact (EA 22%nat ltac:(lia))
    | rewrite F27, EF by lia; exact (EA 27%nat ltac:(lia))
    | rewrite F18, EF by lia; exact (EA 18%nat ltac:(lia))
    | rewrite F9, EF by lia; exact (EA 9%nat ltac:(lia))
    | rewrite F8, EF by lia; exact (EA 8%nat ltac:(lia))
    | rewrite F21, EF by lia; exact (EA 21%nat ltac:(lia))
    | exact FK ]. }
  split; [cbn [ga_entry re_buf]; rewrite F23, EF by lia; exact (eq_trans (EA 23%nat ltac:(lia)) R23)|].
  split; [cbn [ga_entry re_buf]; rewrite F24, EF by lia; exact (eq_trans (EA 24%nat ltac:(lia)) R24)|].
  split; [cbn [ga_entry re_buf]; rewrite F25, EF by lia; exact (eq_trans (EA 25%nat ltac:(lia)) R25)|].
  split.
  { rewrite F19. apply ga_den_of_U.
    rewrite ga_U_add by (rewrite US40f, U21f; unfold SHADOW_OFF; unfold GA_HI in *; lia).
    rewrite US40f, U21f. reflexivity. }
  split; [apply (akept_vm W1 m1); [intros y Hy; apply FK; cbn in Hy; rewrite WF in *; lia | exact V72]|].
  split; [cbn [ga_entry re_hp]; exact Hres0|].
  split; [cbn [ga_entry re_kh]; reflexivity|].
  split.
  { cbn [ga_entry re_hp re_kh]. intros blc lyq ownq i Hin Hi.
    apply (ga_awr_blk cx ly2 S2 W2 mem2 md2 (ga_entry e1 res (8 * re_nheld e1 + 8)) h1 _ out1
             res (8 * re_nheld e1 + 8) blc lyq ownq (res + i) HAR2 PERM2 HPERM0);
      [ rewrite EA2; apply in_or_app; right; apply in_eq | lia | exact Hin | rewrite RQ2 in Hi |- *; lia ]. }
  split; [exact ROM2|].
  split; [exact Hges|]. split; [exact Hjj|]. split; [exact Hidx|]. split; [exact HGSF|].
  (* GARB: gb_garb, with the entry's two cells read off the final regions *)
  split.
  { pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as REF. cbn [ms_mem restrict] in REF.
    assert (B22f : bv_unsigned (ew Ef 22) = dxSA cx) by (rewrite (UF 22%nat ltac:(lia)); exact B22a).
    assert (VF40 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (dxSA cx + 40) (N.to_nat 8) res).
    { eapply (field_of_region Ef _ 22 (dxSA cx)); [exact REF | exact B22f | ga_in | | |].
      - cbn [sv_denot]. rewrite (UF 52%nat ltac:(lia)), Ea52, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
        reflexivity.
      - change (8 * Z.of_N 8) with 64. clear - Hres64. lia.
      - apply (proj1 (Z.leb_le _ _)). reflexivity. }
    assert (VF48 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (dxSA cx + 48) (N.to_nat 4) (re_nheld e1)).
    { eapply (field_of_region Ef _ 22 (dxSA cx)); [exact REF | exact B22f | ga_in | | |].
      - cbn [sv_denot]. rewrite (EF 10%nat ltac:(lia)), E10, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
        reflexivity.
      - change (8 * Z.of_N 4) with 32. clear - Hnh26. lia.
      - apply (proj1 (Z.leb_le _ _)). reflexivity. }
    change (N.to_nat 8) with 8%nat in VF40. change (N.to_nat 4) with 4%nat in VF48.
    assert (HmxT : tr_max (RelayRunT.RMalloc (Z.of_nat (length x) + 1) :: tl2) <= tr_max tl).
    { rewrite Htl. destruct (dlka cx s1 p =? 0); repeat first [rewrite MTm | rewrite MTr]; apply Z.le_max_r. }
    exact (gb_garb cx s1 D p q ly1 S1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl (ms_mem ms1) ly2 S2 W2 mem2
      (ms_mem msf) matf res x tl2 HB HCORE Hges Hidx Etra Etrc HmxT HJ2 Hfr2 Hres4096 BASEP Hcopy Hkept2 Herr2
      Hpres2 HGr1 HGr2 KR1 KR2 Hmle2 VF40 VF48 ROM2 FK). }
  unfold GARfut. exists tl2. do 4 eexists. split; [exact HLF | reflexivity].
Qed.

End c.
End b.
End a.

(* ============================================================================================================
   THE ARx-GENERIC TWIN of this file (DR_x slice D, 2026-10-30): gs_adda over W_drain_cx_x.v's Section variables
   (B PST ARx MT RP MMAX RG), with the entry's ghost list Hp and budget kr after cx and the cut's own ghost list Hp1
   after S1, against the interfaces W_drain_gs.v's GA_x / gs_add_stmt_x and W_gsaddb_cx.v's GAR_x / GARB_x /
   gs_addb_stmt_x.  Everything above this line is unchanged.
   - The AR-free lemmas of Section c above are CITED, with the Section variables their proofs took (most take RG
     and HGSB).  Each lemma whose statement names AR, LCORE, GSB, GARB or the journal has its twin here (NAME_x),
     its proof the AR one with the AR -> ARx dictionary (alx_blocks for al_blocks, blk_img_x, ...).
   - Kit lemmas over AR that the AR proofs cite and that have no twin in the imports are stated here: YCbq.v's
     sep_blocks_perm (from YGcallx.v's sep_blocks_pos_x) and region_kept_stack_aj (over ajournal_x), and
     W_drain_tr.v's gs_cut_facts / gs_cut_dnext_signs / gs_dgs_dnext_signs over LCORE_x (their proofs read only
     model conjuncts).
   - The one allocator call is realloc #2 at 0x838c0, in its caller-context form (AREALLOC, HCTX_re2: it returns
     to 0x838c4).  The room round: the cut's dbud_x room holds MT_rk's charge 2 of seen_tr's first request on top of
     the budget of the requests after it (W_drain_room_x.gs_rm_take), so the rule runs at that budget and its post's room is
     GARB_x's; the count premise is gs_cnt_call; the counts after the call are gs_cnt_malloc (s->held NULL, a
     malloc) or gs_cnt_realloc (the old array (re_hp, re_kh), ent_ka = re_kh). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_sites_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_cx W_drain_cx_x W_drain_gs W_gsaddb_cx.
(* the room round's bookkeeping at an allocator call, the drain stages' one text *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_room_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcallx.
(* W_drain_cx_x.v loads FCiface, which sets Zify's euclidean flag: this file's setting again *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* the Section c tactics above, restated for the twin *)
Ltac ga_in_x := repeat (first [left; reflexivity | right]).
Ltac gax_len_x := rewrite ?length_app, ?gax_bzs_len, ?Mem.length_le8, ?Mem.length_le4, ?length_Z_to_le_bytes;
  cbn [length].
Ltac zlia_x := unfold app_addr, in_app, amem_range, ASAN_CEIL, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd,
  kHighShadowEnd, kImgLo in *; lia.

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
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
(* W_drain_cx_x.v:151-216, the ones this file's proofs use *)
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= 0x5fb000 /\ rg_s RG mod 8 = 0.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.
(* the realloc rule in its caller-context form over the generic journal (W_journal_x.v Section hc), and its one
   call site here (drain = 0x830dc; jal realloc 0x838c0) *)
Variable CTX_R : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis HCTX_re2 : In [BASE + AF_fr_drain + 0x7e8] CTX_R.   (* realloc #2 returns to 0x838c4 *)
Let RUN := paj_run_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_DR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).

(* ---- YCbq.v:2587 sep_blocks_perm and :2601 region_kept_stack_aj over ARx (their AR proofs) ---- *)
Lemma sep_blocks_perm_x : forall ly S Hp (W : world SEGS) mem md x y l,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) (x :: y :: l) ->
zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S Hp W mem md x y l HAR HP.
assert (Hx : In x (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HP | left; reflexivity]).
apply in_split in Hx as (a1 & a2 & E1).
assert (HP2 : Permutation (a1 ++ a2) (y :: l)).
{ apply Permutation_sym. apply (@Permutation_cons_app_inv _ _ a1 a2 x). rewrite <- E1. apply Permutation_sym. exact HP. }
assert (Hy : In y (a1 ++ a2)) by (eapply Permutation_in; [apply Permutation_sym; exact HP2 | left; reflexivity]).
apply in_app_or in Hy as [Hy | Hy]; apply in_split in Hy as (b1 & b2 & E2).
- pose proof (YGcallx.sep_blocks_pos_x SEGS B ARx LAWS ly S Hp W mem md y x b1 b2 a2 HAR
    ltac:(rewrite E1, E2, <- app_assoc; reflexivity)) as Hd.
  unfold zdisjoint, block_rng in *. cbn [fst snd] in *. lia.
- exact (YGcallx.sep_blocks_pos_x SEGS B ARx LAWS ly S Hp W mem md x y a1 b1 b2 HAR
    ltac:(rewrite E1, E2; reflexivity)).
Qed.

(* ---- (1) the shadow entry of the seat (ga_shok) ---- *)
Lemma ga_shok_x : forall Ex ly S Hp (W : world SEGS) mem md G SA,
ARx ly S Hp W mem md -> In (G, ATABLE) (ablocks B ly S) -> G <= SA -> SA + AENT <= G + ATABLE ->
ew Ex 21 = w64 SHADOW_OFF -> ew Ex 22 = w64 SA -> 4096 <= SA -> SA + 56 <= GA_HI ->
sh_ok SEGS gaBx ga_SH Ex (mrestrict (w_H W) mem).
Proof.
intros Ex ly S Hp W mem md G SA HAR Hin HGle HSAle E21 E22 HSAlo HSAhi.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hin) as (_ & H4096 & Hceil & Happ & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
rewrite RQT in Hceil, Happ.
unfold sh_ok, ga_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem Ex gaBx 22 G 896 SA 0 56).
- apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S Hp W mem md G ATABLE);
  [exact HAR | exact Hin | lia | rewrite RQT; lia].
- unfold U, gaBx. cbn [sv_denot]. rewrite E21, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite E22, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold GA_HI in *; lia). reflexivity.
- lia.
- unfold AENT, ATABLE in HSAle. lia.
- intros y Hy. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
  unfold AENT, ATABLE in HSAle. unfold SHADOW_OFF. lia.
Qed.

(* ---- (3) lowness of the footprints (ga_blk_low .. ga_aout_fp_low) ---- *)
Lemma ga_blk_low_x : forall ly S Hp (W : world SEGS) mem md qq nn aa,
ARx ly S Hp W mem md -> In (qq, nn) (ablocks B ly S) -> qq <= aa -> aa < qq + req_size nn -> ga_low aa.
Proof.
intros ly S Hp W mem md qq nn aa HAR Hin H1 H2.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md qq nn HAR Hin) as (_ & H4096 & Hceil & _).
unfold ga_low. lia.
Qed.

Lemma ga_aentry_fp_low_x : forall ly S Hp (W : world SEGS) mem md e,
ARx ly S Hp W mem md -> aentry_okx B ly S W mem e ->
forall r, In r (aentry_fp e) -> forall aa, fst r <= aa < snd r -> ga_low aa.
Proof.
intros ly S Hp W mem md e HAR HE r Hr aa Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & _ & Hbuf & _ & Hhp & _ & _ & Hks).
assert (HK : forall k, In k (re_keys e) -> key_addr k <= aa < key_addr k + Z.of_nat (length (key_text k) + 1) ->
  ga_low aa).
{ intros k Hk Hka. rewrite Forall_forall in Hks. destruct (Hks k Hk) as (Hin & _).
  apply (ga_blk_low_x ly S Hp W mem md (key_addr k) (Z.of_nat (length (key_text k)) + 1) aa HAR Hin); [lia|].
  pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(lia)) as (_ & Hrq). lia. }
assert (HP : re_hp e <= aa < re_hp e + Z.of_nat (length (bzs (key_ptrs (re_keys e)))) -> ga_low aa).
{ intros Hpa. destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
  - rewrite Hke in Hpa. unfold bzs, key_ptrs in Hpa. cbn [map concat length] in Hpa. lia.
  - unfold bzs in Hpa. rewrite length_map, gs_key_ptrs_len in Hpa.
    apply (ga_blk_low_x ly S Hp W mem md (re_hp e) (re_kh e) aa HAR Hin); [lia|].
    pose proof (req_size_pos (re_kh e) ltac:(lia)) as (_ & Hrq).
    unfold re_nheld in Hk1. lia. }
unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
  rewrite length_map, length_app in Ha.
  destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  apply (ga_blk_low_x ly S Hp W mem md (re_buf e) (re_cap e) aa HAR Hin); [lia|].
  pose proof (req_size_pos (re_cap e) ltac:(lia)) as (_ & Hrq). lia.
- destruct Hr as [<- | Hr].
  + unfold gfp in Ha. cbn [fst snd] in Ha. exact (HP Ha).
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha. exact (HK k Hk Ha).
Qed.

Lemma ga_alist_fp_low_x : forall ly S Hp (W : world SEGS) mem md LA l lns lo hi,
ARx ly S Hp W mem md -> alist_at B ly S W mem LA l lns ->
0x10000 <= lo -> lo <= LA -> LA + 16 <= hi -> hi <= 0x5fb000 ->
forall r, In r (alist_fp LA l) -> forall aa, fst r <= aa < snd r -> ga_low aa.
Proof.
intros ly S Hp W mem md LA l lns lo hi HAR HL Hlo1 Hlo2 Hhi1 Hhi2 r Hr aa Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. apply (ga_img_low RG HGSB aa lo hi); lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app, (ga_recs_len RG) in Ha.
    destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
    apply (ga_blk_low_x ly S Hp W mem md (hl_v l) (AREC * hl_cap l) aa HAR Hin); [lia|].
    pose proof (req_size_pos (AREC * hl_cap l) ltac:(unfold AREC; lia)) as (_ & Hrq).
    unfold hl_n in Hn, Hj. unfold AREC in *. clear - Ha Hn Hj Hrq. lia.
  + apply in_map_iff in Hr as (qq & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hrecs. destruct (Hrecs qq Hq) as (Hin & _).
    apply (ga_blk_low_x ly S Hp W mem md (fst qq) (Z.of_nat (length (snd qq)) + 1) aa HAR Hin); [lia|].
    pose proof (req_size_pos (Z.of_nat (length (snd qq)) + 1) ltac:(lia)) as (_ & Hrq). lia.
Qed.

Lemma ga_asrc_fp_low_x : forall ly S Hp (W : world SEGS) mem md HA h,
ARx ly S Hp W mem md -> asrc_at B ly S W mem HA h ->
rg_s RG <= HA -> HA + ASRC <= rg_s RG + 4 * ASRC ->
forall r, In r (asrc_fp HA h) -> forall aa, fst r <= aa < snd r -> ga_low aa.
Proof.
intros ly S Hp W mem md HA h HAR HS Hlo Hhi r Hr aa Ha.
pose proof HGSB as (Hg1 & Hg2 & _).
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- cbn [fst snd] in Ha. apply (ga_img_low RG HGSB aa (rg_s RG) (rg_s RG + 4 * ASRC)); unfold ASRC in *; lia.
- unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map in Ha.
  apply (ga_blk_low_x ly S Hp W mem md (hs_partial h) APARTIAL aa HAR Hpb); [lia|].
  pose proof (req_size_pos APARTIAL ltac:(unfold APARTIAL; lia)) as (_ & Hrq). lia.
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + refine (ga_alist_fp_low_x ly S Hp W mem md (HA + 16) (hs_pending h) false (rg_s RG) (rg_s RG + 4 * ASRC)
      HAR Hpend _ _ _ _ r Hr aa Ha); unfold ASRC in *; lia.
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * refine (ga_alist_fp_low_x ly S Hp W mem md (HA + 64) (hs_expected h) true (rg_s RG) (rg_s RG + 4 * ASRC)
        HAR Hexp _ _ _ _ r Hr aa Ha); unfold ASRC in *; lia.
    * refine (ga_alist_fp_low_x ly S Hp W mem md (HA + 80) (hs_held h) true (rg_s RG) (rg_s RG + 4 * ASRC)
        HAR Hheld _ _ _ _ r Hr aa Ha); unfold ASRC in *; lia.
Qed.

Lemma ga_aout_fp_low_x : forall ly S Hp (W : world SEGS) mem md c O mx no cap out,
ARx ly S Hp W mem md -> aout_at B RG ly S W mem c O mx no cap out ->
forall r, In r (aout_fp B RG cap out) -> forall aa, fst r <= aa < snd r -> ga_low aa.
Proof.
intros ly S Hp W mem md c O mx no cap out HAR HOUT r Hr aa Ha.
pose proof asan_consts as (C1 & _ & _ & _ & C5).
assert (GL : forall xx l, In (xx, l) (G_DR B RG) -> xx <= aa < xx + l -> ga_low aa).
{ intros xx l Hin Hx.
  assert (HI : inG (G_DR B RG) aa)
    by (unfold inG; apply Exists_exists; exists (xx, l); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
  pose proof (inG_low SEGS B pa_segs_low _ aa HG HI). unfold ga_low. lia. }
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
- pose proof HSM as (Hs1 & Hs2). apply (ga_img_low RG HGSB aa (rg_send_max RG) (rg_send_max RG + 8)); lia.
- apply (GL (rg_nout RG) 8); [unfold G_DR, G_SL; ga_in_x | lia].
- apply (GL (rg_capout RG) 8); [unfold G_DR, G_SL; ga_in_x | lia].
- apply (GL (rg_out RG) 8); [unfold G_DR, G_SL; ga_in_x | lia].
- pose proof (pa_obj_img 9 ltac:(lia)) as H9. rewrite HV9 in H9.
  apply (ga_img_low RG HGSB aa (rg_client RG) (rg_client RG + 4)); lia.
- apply (GL (rg_client_broken RG) 1); [unfold G_DR, G_SL; ga_in_x | lia].
- pose proof (pa_obj_img 12 ltac:(lia)) as H12. rewrite HV12 in H12.
  apply (ga_img_low RG HGSB aa (rg_send_dead RG) (rg_send_dead RG + 1)); lia.
- apply (GL (rg_send_eintr RG) 1); [unfold G_DR, G_SL; ga_in_x | lia].
- apply (GL (as_errno B) 4); [unfold G_DR, G_SL; ga_in_x | lia].
- destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
  apply (ga_blk_low_x ly S Hp W mem md out cap aa HAR Hin); [lia|].
  pose proof (req_size_pos cap ltac:(lia)) as (_ & Hrq). lia.
Qed.

(* ---- (4) the allocator call site's shapes (ga_sep_head .. ga_kept_blk) ---- *)
Lemma ga_sep_head_x : forall ly S Hp (W : world SEGS) m md x L y,
ARx ly S Hp W m md -> Permutation (ablocks B ly S) (x :: L) -> In y L ->
zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S Hp W m md x L y HAR HP Hy. destruct (in_split _ _ Hy) as (l1 & l2 & ->).
apply (sep_blocks_perm_x ly S Hp W m md x y (l1 ++ l2) HAR).
eapply Permutation_trans; [exact HP|]. apply perm_skip. apply Permutation_sym, Permutation_middle.
Qed.

Lemma ga_dup_x : forall ly S Hp (W : world SEGS) mem md x l1 l2 l3,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) (l1 ++ x :: l2 ++ x :: l3) -> 0 <= snd x -> False.
Proof.
intros ly S Hp W mem md x l1 l2 l3 HAR HP Hx.
assert (HP2 : Permutation (l1 ++ x :: l2 ++ x :: l3) (x :: x :: (l1 ++ l2) ++ l3)).
{ eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|]. apply perm_skip.
  rewrite app_assoc. apply Permutation_sym, Permutation_middle. }
pose proof (sep_blocks_perm_x ly S Hp W mem md x x _ HAR (Permutation_trans HP HP2)) as D.
destruct x as [b m]. unfold zdisjoint, block_rng in D. cbn [fst snd] in D, Hx.
pose proof (req_size_pos m Hx). lia.
Qed.

Lemma ga_dup_in_x : forall ly S Hp (W : world SEGS) mem md L1 L2 x,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) (L1 ++ x :: L2) -> In x L2 -> 0 <= snd x -> False.
Proof.
intros ly S Hp W mem md L1 L2 x HAR HP Hin Hx. apply in_split in Hin as (l2 & l3 & ->).
exact (ga_dup_x ly S Hp W mem md x L1 l2 l3 HAR HP Hx).
Qed.

Lemma ga_shent_x : forall Ex ly S Hp (W : world SEGS) mem md b m (mt : nat) p lo hi,
ARx ly S Hp W mem md -> In (b, m) (ablocks B ly S) -> U Ex gaBx = SHADOW_OFF -> U Ex (SOff mt 0) = p ->
b <= p + lo -> lo <= hi -> p + hi <= b + req_size m ->
shent_ok SEGS gaBx Ex (mrestrict (w_H W) mem) (mkSHE mt lo hi).
Proof.
intros Ex ly S Hp W mem md b m mt p lo hi HAR Hin HBx Hpp H1 H2 H3.
pose proof asan_consts as (C1 & _).
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b m HAR Hin) as (_ & H4 & Hc & Happ & _).
eapply shent_ok_of_range.
- exact (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S Hp W mem md b m (p + lo) (hi - lo) HAR Hin H1
    ltac:(lia)).
- exact HBx.
- exact Hpp.
- lia.
- lia.
- intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold SHADOW_OFF. lia.
Qed.

Lemma ga_fp_x : forall cx ly S Hp (W : world SEGS) mem md e h OC out b m,
ARx ly S Hp W mem md ->
Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: aentry_blks e ++ asrc_blks h ++ aout_blks OC out ++ dxrest cx) ->
Permutation (ablocks B (dxly cx) (dxS cx))
  ((dxG cx, ATABLE) :: aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++ aout_blks (dxcap cx) (dxout cx) ++ dxrest cx) ->
In (b, m) (aentry_blks e) -> 0 <= m -> In (b, m) (ablocks B (dxly cx) (dxS cx)) ->
forall i, 0 <= i < req_size m -> inFP (dFP cx) (b + i).
Proof.
intros cx ly S Hp W mem md e h OC out b m HAR HP1 HPd Hae Hm Hin0 i Hi.
apply (Permutation_in _ HPd) in Hin0.
assert (HFP : In (b, m) (aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++ aout_blks (dxcap cx) (dxout cx)) ->
  inFP (dFP cx) (b + i)).
{ intros Hx. unfold dFP, dr_fp. exists (b, b + req_size m).
  split; [right; exact (in_map (fun b0 => (fst b0, fst b0 + req_size (snd b0))) _ (b, m) Hx)|].
  cbn [fst snd]. lia. }
destruct Hin0 as [Hg | Hin0].
- exfalso. rewrite Hg in HP1.
  exact (ga_dup_in_x ly S Hp W mem md [] _ (b, m) HAR HP1 (in_or_app _ _ _ (or_introl Hae)) Hm).
- apply in_app_or in Hin0 as [Hx | Hin0]; [apply HFP; apply in_or_app; left; exact Hx|].
  apply in_app_or in Hin0 as [Hx | Hin0]; [apply HFP; apply in_or_app; right; apply in_or_app; left; exact Hx|].
  apply in_app_or in Hin0 as [Hx | Hx]; [apply HFP; apply in_or_app; right; apply in_or_app; right; exact Hx|].
  exfalso. apply in_split in Hae as (a1 & a2 & Ea). rewrite Ea, <- app_assoc in HP1.
  apply (ga_dup_in_x ly S Hp W mem md ((dxG cx, ATABLE) :: a1) (a2 ++ asrc_blks h ++ aout_blks OC out ++ dxrest cx)
    (b, m) HAR HP1); [|exact Hm].
  apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. exact Hx.
Qed.

Lemma ga_awr_blk_x : forall cx ly S Hp (W : world SEGS) mem md e h OC out b m blc lyq ownq a,
ARx ly S Hp W mem md ->
Permutation (ablocks B ly S) ((dxG cx, ATABLE) :: aentry_blks e ++ asrc_blks h ++ aout_blks OC out ++ dxrest cx) ->
Permutation (ablocks B (dxly cx) (dxS cx))
  ((dxG cx, ATABLE) :: aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++ aout_blks (dxcap cx) (dxout cx) ++ dxrest cx) ->
In (b, m) (aentry_blks e) -> 0 <= m -> In (b, m) blc -> b <= a < b + req_size m ->
awr_byte DRAIN_STK_x (dsp0 cx) (dFP cx) (ablocks B (dxly cx) (dxS cx)) blc lyq ownq a.
Proof.
intros cx ly S Hp W mem md e h OC out b m blc lyq ownq a HAR HP1 HPd Hae Hm Hinc Ha.
assert (DZ : forall x y : Z * Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
destruct (in_dec DZ (b, m) (ablocks B (dxly cx) (dxS cx))) as [Hin0 | Hnin0].
- right; left. split.
  + replace a with (b + (a - b)) by lia.
    apply (ga_fp_x cx ly S Hp W mem md e h OC out b m HAR HP1 HPd Hae Hm Hin0). lia.
  + exists b, m. split; [exact Hinc | exact Ha].
- right; right; left. exists b, m. split; [exact Hinc|]. split; [exact Hnin0 | exact Ha].
Qed.

Lemma ga_kept_blk_x : forall E lyc Sc (W : world SEGS) memc (W2 : world SEGS) mem2 slo shi (Er : Z -> Prop)
  ly2 S2 Hp2 md2 n lo hi wlo whi cs b m base,
acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi Er ->
ARx ly2 S2 Hp2 W2 mem2 md2 -> In (b, m) (ablocks B ly2 S2) ->
bv_unsigned (ew E n) = base -> In (b, m) (ablocks B lyc Sc) ->
b <= base + lo -> base + hi <= b + req_size m -> lo <= wlo -> whi <= hi ->
(forall a, b <= a < b + req_size m -> ~ Er a) ->
region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er ly2 S2 Hp2 md2 n lo hi wlo whi cs b m base (_ & K2 & _) HAR2 Hin2 Hn Hin
  H1 H2 H3 H4 HnE.
destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 b m HAR2 Hin2) as (_ & _ & _ & _ & Hpres & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hin); [lia|].
  replace (b + (a - b)) with a by lia. apply HnE. lia.
- intros _. apply (apresent_writable SEGS). exact (proj1 (Hpres a ltac:(lia))).
Qed.


(* The pieces of this Section at a world relation R (route R): each <name>R below is <name> with the journal
   ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, the cf rules and every carrier or statement it names
   -> their R twins; every other token is the strict text's. *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp W mem md, ARx ly S Hp W mem md -> RO mem.
Variable HA : alayout -> astate -> bvmap 5 word -> list (Z * Z * Z) -> Z -> Z -> Prop.
Hypothesis HA_call : forall lyc Sc regsT ch p n, mo_ok MT Sc (mo_malloc MT n + mo_free MT) -> HA lyc Sc regsT ch p n.
Hypothesis AREALLOCR : arealloc_cf_rule_c_xR SEGS B PST ARx MT MMAX RP RO HA CTX_R R (SIGMA WS_realloc).
Let RUNR := paj_run_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let RUNTOR := paj_run_to_x_xG B PST ARx LAWS R (G_DR B RG) HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).

Lemma region_kept_stack_aj_xR : forall E lyc Sc (W : world SEGS) memc (W2 : world SEGS) mem2 slo shi (Er : Z -> Prop)
    n lo hi wlo whi cs sp0 sp STK FP ly S Hp W0 mem md own ly2 S2 Hp2 md2 k,
  acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi Er ->
  ajournal_xR SEGS B PST ARx R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k ->
  bv_unsigned (ew E n) = sp -> shi <= sp + lo -> sp0 - STK <= sp + lo -> sp + hi <= sp0 -> lo <= wlo -> whi <= hi ->
  region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi wlo whi cs sp0 sp STK FP ly S Hp W0 mem md own ly2 S2 Hp2 md2 k
  (K1 & _) HJ Hn Hshi Hlo Hhi Hw1 Hw2.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hal & Hstk0 & Hceil & Hslo & Hsh & H47 & _)
  & _ & HQT).
pose proof asan_consts as (C1 & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply K1; zlia_x.
- intros _. apply (apresent_writable SEGS). apply Hpres. zlia_x.
Qed.
(* ---- W_drain_tr.v:408 gs_cut_facts, :444 gs_cut_dnext_signs, :516 gs_dgs_dnext_signs over LCORE_x ---- *)
Lemma gs_cut_facts_xR : forall cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl,
  LCORE_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1
    spent tl ->
  nozero (drain_b_c.ds_u s1) /\ 0 <= drain_b_c.ds_cap s1 /\ 0 <= dxmx cx /\ 0 <= no /\ 0 <= oc /\ 0 <= ka /\
  0 <= drain_b_c.ds_en (dnext (dlive cx) (dxmx cx) s1) /\ 0 <= drain_b_c.ds_ecap (dnext (dlive cx) (dxmx cx) s1).
Proof.
intros cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl HL.
unfold LCORE_xR in HL. cbv zeta in HL. destruct HL as (HM & HK & _ & HH & HR & _).
assert (Pno : drain_b_c.ds_no (dvirt cx s1 sk H ka no oc) = no) by reflexivity.
assert (Poc : drain_b_c.ds_ocap (dvirt cx s1 sk H ka no oc) = oc) by reflexivity.
assert (Pka : drain_b_c.ds_ka (dvirt cx s1 sk H ka no oc) = ka) by reflexivity.
assert (Pen : drain_b_c.ds_en (dvirt cx s1 sk H ka no oc) = drain_b_c.ds_en (dnext (dlive cx) (dxmx cx) s1))
  by reflexivity.
assert (Pec : drain_b_c.ds_ecap (dvirt cx s1 sk H ka no oc) = drain_b_c.ds_ecap (dnext (dlive cx) (dxmx cx) s1))
  by reflexivity.
unfold DMEM_xR in HM. destruct HM as (_ & _ & _ & _ & _ & _ & _ & HE & HS & _ & _ & HO & _).
unfold aentry_okx in HE. destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HHP & _).
unfold asrc_at in HS.
destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HX & _).
unfold alist_at in HX. destruct HX as (_ & _ & _ & _ & (HNC & _) & _).
unfold aout_at in HO.
destruct HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  Hmx & HOn & HOc).
unfold DLINK in HK. destruct HK as (_ & _ & _ & _ & Eka & _ & _ & _ & _ & Een & Eec & _).
unfold DHIST in HH. destruct HH as (_ & _ & _ & _ & _ & Eno & _).
unfold RSTART in HR. destruct HR as (_ & (_ & _ & _ & HU) & Hcap & _).
rewrite Pno in HOn, Eno. rewrite Poc in HOc. rewrite Pka in Eka. rewrite Pen in Een. rewrite Pec in Eec.
unfold ulen in Hcap.
split; [exact HU|]. split; [lia|]. split; [lia|]. split.
{ revert HOn. destruct (dlive cx); intros HOn; cbn beta iota in HOn; lia. }
split; [destruct HOc as [(Hc0 & _)|(Hc0 & _)]; lia|]. split.
{ rewrite <- Eka. unfold drain_b_c.ent_ka.
  destruct HHP as [(H0 & _)|(H0 & _ & _ & H8 & _)];
    [rewrite (proj2 (Z.eqb_eq _ _) H0) | rewrite (proj2 (Z.eqb_neq _ _) H0)]; lia. }
split; [rewrite <- Een; unfold hl_n; lia|].
rewrite <- Eec. unfold hl_n in HNC. lia.
Qed.
Lemma gs_cut_dnext_signs_xR : forall cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1
  spent tl p,
  0 <= dxmx cx -> dbound s1 p -> no = dlno s1 p -> oc = dloc cx s1 p -> (0 <= ka -> 0 <= dlka cx s1 p) ->
  LCORE_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1
    spent tl ->
  0 <= oc /\
  0 <= drain_b_c.ds_cap (dnext (dlive cx) (dxmx cx) s1) /\ 0 <= drain_b_c.ds_ocap (dnext (dlive cx) (dxmx cx) s1) /\
  0 <= drain_b_c.ds_no (dnext (dlive cx) (dxmx cx) s1) /\ 0 <= drain_b_c.ds_en (dnext (dlive cx) (dxmx cx) s1) /\
  0 <= drain_b_c.ds_ecap (dnext (dlive cx) (dxmx cx) s1) /\ 0 <= drain_b_c.ds_ka (dnext (dlive cx) (dxmx cx) s1).
Proof.
intros cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl p _ HB Eno Eoc Hka HL.
apply gs_cut_facts_xR in HL. destruct HL as (HU & Hc & _ & Hno & Hoc & Hk & Hen & Hec).
subst no oc.
destruct (gs_dnext_signs_at cx s1 p HU HB Hc Hno Hoc (Hka Hk)) as (D1 & D2 & D3 & D4).
repeat split; assumption.
Qed.
Lemma gs_dgs_dnext_signs_xR : forall cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1
  spent tl p q,
  dbound s1 p -> (p <= q < length (dW s1))%nat -> nth_error (dW s1) q = Some 0 ->
  (forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) -> dskp s1 p = false -> (q - p <= LINE_LIMIT)%nat ->
  no = dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1 ->
  oc = send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
         (Z.of_nat (length (dline s1 p q)) + 1) ->
  (0 <= ka -> 0 <= dlka cx s1 p) ->
  LCORE_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1
    spent tl ->
  0 <= oc /\
  0 <= drain_b_c.ds_cap (dnext (dlive cx) (dxmx cx) s1) /\ 0 <= drain_b_c.ds_ocap (dnext (dlive cx) (dxmx cx) s1) /\
  0 <= drain_b_c.ds_no (dnext (dlive cx) (dxmx cx) s1) /\ 0 <= drain_b_c.ds_en (dnext (dlive cx) (dxmx cx) s1) /\
  0 <= drain_b_c.ds_ecap (dnext (dlive cx) (dxmx cx) s1) /\ 0 <= drain_b_c.ds_ka (dnext (dlive cx) (dxmx cx) s1).
Proof.
intros cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl p q
  HB HPQ HQ HNZ HK HL Eno Eoc Hka HC.
pose proof (tr_drlp_line s1 p q HB HPQ HQ HNZ HK HL) as E.
assert (HB' : dbound s1 (S q)).
{ split; [lia|]. right. replace (S q - 1)%nat with q by lia. exact HQ. }
assert (ER : dlrun cx s1 (S q) =
  (send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p) (Z.of_nat (length (dline s1 p q)) + 1),
   seen_arr (dlH cx s1 p) (dline s1 p q), seen_ka (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q))).
{ unfold dlrun at 1. rewrite E, tr_lrun_app, tr_lrun_one. reflexivity. }
assert (EN : dlno s1 (S q) = dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1).
{ unfold dlno. rewrite E. unfold with_nul. rewrite map_app, concat_app. cbn [map concat].
  rewrite app_nil_r, !length_app. cbn [length]. lia. }
pose proof (gs_cut_facts_xR cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl
  HC) as (_ & _ & Hmx & _).
refine (gs_cut_dnext_signs_xR cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl
  (S q) Hmx HB' _ _ _ HC).
- rewrite EN. exact Eno.
- unfold dloc. rewrite ER. exact Eoc.
- intro Hk. unfold dlka. rewrite ER. cbn [snd]. unfold seen_ka. apply sz_seen_ka. exact (Hka Hk).
Qed.
(* ---- (2) the line loop's core across an END whose key is not held (ga_lcore_end) ---- *)
Lemma ga_lcore_end_xR : forall cx Hp kr s1 D sent kl kl' l x H ka no oc nk nk' sk
  ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl,
LCORE_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1
  spent tl ->
gesture l = Some (GEnd, x) -> index_of x H = None -> nk' <= nk -> kl' = kl ++ [l] ->
LCORE_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D sent kl' H ka no oc nk' sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1
  spent tl.
Proof.
intros cx Hp kr s1 D sent kl kl' l x H ka no oc nk nk' sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl
  (HM & HLK & HDSM & HH & HR & HBU) Hg Hidx Hnk ->.
pose proof HH as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
assert (HnotH : ~ In x H) by (apply index_of_none; exact Hidx).
split; [exact HM|]. split; [exact HLK|]. split; [exact HDSM|].
split; [|split; [exact HR | exact HBU]].
split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. split; [exact D5|].
split; [exact D6|]. split; [exact D7|]. split; [exact D8|].
split.
- rewrite gs_upds_snoc. unfold upd. rewrite Hg. unfold same_set in D9 |- *.
  intros y. rewrite upd_in_end. split.
  + intros Hy. split; [apply D9; exact Hy|]. intros ->. apply HnotH. exact Hy.
  + intros (Hy & _). apply D9. exact Hy.
- split; [lia | exact D11].
Qed.
(* ---- the line loop's core across a memory that keeps every byte's view (ga_lcore_mem) ---- *)
Lemma ga_lcore_mem_xR : forall cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 (W1 : world SEGS) m1 md1 k1
  e1 h1 out1 ev1 LB1 spent tl m' md',
LCORE_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1
  spent tl ->
ARx ly1 S1 Hp1 W1 m1 md1 ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m' md' k1 ->
(forall x, 0 <= x < 2 ^ 64 -> aview SEGS (w_H W1) m' x = aview SEGS (w_H W1) m1 x) ->
(forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) m' x) ->
alloc_ceiling + 8 <= dsp0 cx - DRAIN_FRAME -> dsp0 cx <= 2 ^ 47 ->
4096 <= dxSA cx -> dxSA cx + AENT <= alloc_ceiling ->
rg_s RG <= dHA RG cx -> dHA RG cx + ASRC <= rg_s RG + 4 * ASRC ->
LCORE_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m' md' k1 e1 h1 out1 ev1 LB1
  spent tl.
Proof.
intros cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl m' md'
  (HM & HLK & HDS & HH & HR & HBU) HAR1 HJ' KL HP Hsplo Hsphi HSAlo HSAhi HHAlo HHAhi.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WF : DRAIN_FRAME = 336) by reflexivity.
pose proof HM as (_ & HROM & HPRES & HFRS & HFRM & HENT & HAWRx & HOKX & HSRC & HOTH & HKEPTx & HOUT & HLIVE & HPERM).
assert (AKE : forall fp, (forall r, In r fp -> forall x, fst r <= x < snd r -> ga_low x) ->
              akept W1 m1 W1 m' fp)
  by (intros fp Hlow r Hr x Hx; exact (ga_kept_of RG HGSB W1 m1 m' x KL HP (Hlow r Hr x Hx))).
assert (VK : forall aa n v, 0 <= aa -> aa + Z.of_nat n <= 2 ^ 64 ->
             val_mem SEGS (arm W1 m1) aa n v -> val_mem SEGS (arm W1 m') aa n v)
  by (intros aa n v H1 H2 Hv; exact (ga_val_kept RG HGSB W1 m1 m' aa n v KL H1 H2 Hv)).
assert (BLK : forall b, In b (aentry_blks e1) -> In b (ablocks B ly1 S1))
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPERM)); right; apply in_or_app; left; exact Hb).
assert (BLS : forall b, In b (asrc_blks h1) -> In b (ablocks B ly1 S1))
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPERM)); right; apply in_or_app; right;
      apply in_or_app; left; exact Hb).
assert (BLO : forall b, In b (aout_blks (drain_b_c.ds_ocap (dvirt cx s1 sk H ka no oc)) out1) ->
              In b (ablocks B ly1 S1))
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPERM)); right; apply in_or_app; right;
      apply in_or_app; right; apply in_or_app; left; exact Hb).
split; [|split; [exact HLK | split; [exact HDS | split; [exact HH | split; [exact HR | exact HBU]]]]].
split; [exact HJ'|].
split.
{ intros aa Haa.
  assert (Hl : 0 <= aa < kLowMemEnd)
    by (destruct Haa as (sg & Hsg & _ & Hrr);
        exact (pa_segs_low aa ltac:(exists sg; split; [exact Hsg | exact Hrr]))).
  rewrite (KL aa ltac:(unfold kLowMemEnd in *; lia)). exact (HROM aa Haa). }
split; [intros aa Hi Ho He Hpx; exact (HP aa (HPRES aa Hi Ho He Hpx))|].
split; [exact HFRS|].
split.
{ pose proof HFRM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13 & M14 & M15 & M16 & MSV).
  unfold dr_frame. cbv zeta.
  repeat (split; [first [apply VK; [lia | lia | first [exact M1 | exact M2 | exact M3 | exact M4 | exact M5
    | exact M6 | exact M7 | exact M8 | exact M9 | exact M10 | exact M11 | exact M12 | exact M13 | exact M14
    | exact M15 | exact M16]] | idtac]|]).
  intros i Hi. apply VK; [lia | lia | exact (MSV i Hi)]. }
split.
{ apply (gax_garr8_kept W1 m1 W1 m'); [exact HENT|].
  intros x Hx. apply KL. rewrite gax_bzs_len in Hx.
  assert (Hlen : length (entry_bytes e1) = 56%nat).
  { pose proof HOKX as (_ & _ & Kp1 & Kp2 & _). unfold entry_bytes. gax_len_x. lia. }
  rewrite Hlen in Hx. unfold AENT in HSAhi. lia. }
split; [intros i Hi; apply (writable_kept (w_H W1) m1 m'); [exact (HP _) | exact (HAWRx i Hi)]|].
split; [exact (gs_aentry_okx_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m' e1 HOKX
          (AKE (aentry_fp e1) (ga_aentry_fp_low_x ly1 S1 Hp1 W1 m1 md1 e1 HAR1 HOKX)) BLK)|].
split; [exact (asrc_at_kept B ly1 S1 W1 m1 ly1 S1 W1 m' (dHA RG cx) h1 HSRC
          (AKE (asrc_fp (dHA RG cx) h1) (ga_asrc_fp_low_x ly1 S1 Hp1 W1 m1 md1 (dHA RG cx) h1 HAR1 HSRC HHAlo HHAhi))
          BLS)|].
split.
{ intros i Hi Hne. destruct (HOTH i Hi Hne) as (f & oo & V1 & V2 & Hd).
  pose proof HGSB as (Hg1 & Hg2 & _).
  exists f, oo. split; [apply VK; [unfold ASRC in *; lia | unfold ASRC in *; lia | exact V1]|].
  split; [apply VK; [unfold ASRC in *; lia | unfold ASRC in *; lia | exact V2] | exact Hd]. }
split.
{ intros x H1 H2. destruct (HKEPTx x H1 H2) as (Kv & Kw). pose proof HGSB as (Hg1 & Hg2 & _).
  split; [rewrite (KL x ltac:(unfold ASRC in *; lia)); exact Kv|].
  intros Hw. apply (writable_kept (w_H W1) m1 m'); [exact (HP x) | exact (Kw Hw)]. }
split; [exact (aout_at_kept B RG ly1 S1 W1 m1 ly1 S1 W1 m' _ _ _ _ _ out1 HOUT
          (AKE _ (ga_aout_fp_low_x ly1 S1 Hp1 W1 m1 md1 _ _ _ _ _ out1 HAR1 HOUT)) BLO)|].
split; [exact HLIVE | exact HPERM].
Qed.
(* ---- (5) GARB_x, the cut's core from the post of realloc #2 and the store s->held = res (gb_garb), with
   dbud_x's room and counts after the call as two more premises ---- *)
Lemma gb_garb_xR : forall cx Hp kr s1 D p q ly1 S1 Hp1 (W1 : world SEGS) m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl
  mR1 ly2 S2 Hp2 (W2 : world SEGS) mem2 m2 md2 res xx tl2,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
GSB_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
gesture (dline s1 p q) = Some (GBegin, xx) -> index_of xx (dlH cx s1 p) = None ->
(8 * re_nheld e1 + 8) - drain_b_c.ent_ka e1 + tr_peak (RelayRunT.RMalloc (Z.of_nat (length xx) + 1) :: tl2) <=
  tr_peak tl ->
tr_cost MT tl = mo_malloc MT (8 * re_nheld e1 + 8) + mo_free MT +
  (mo_malloc MT (Z.of_nat (length xx) + 1) + mo_free MT + tr_cost MT tl2) ->
tr_max (RelayRunT.RMalloc (Z.of_nat (length xx) + 1) :: tl2) <= tr_max tl ->
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly2 S2 Hp2 W2 m2 md2 (k1 + 3) ->
frames S2 = frames S1 -> 4096 <= res ->
Permutation (ablocks B ly2 S2)
  ((res, 8 * re_nheld e1 + 8) :: (dxG cx, ATABLE) ::
   (if re_cap e1 =? 0 then [] else [(re_buf e1, re_cap e1)]) ++
   map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e1) ++
   asrc_blks h1 ++ aout_blks (GSoc cx s1 p q) out1 ++ dxrest cx) ->
(re_hp e1 <> 0 -> forall i, 0 <= i < Z.min (re_kh e1) (8 * re_nheld e1 + 8) ->
  aview SEGS (w_H W2) mem2 (res + i) = aview SEGS (w_H W1) mR1 (re_hp e1 + i)) ->
acall_kept SEGS B ly1 S1 W1 mR1 W2 mem2 (dsp0 cx + - DRAIN_FRAME - ASTACK) (dsp0 cx + - DRAIN_FRAME)
  (fun a => res <= a < res + req_size (8 * re_nheld e1 + 8) \/
            re_hp e1 <> 0 /\ re_hp e1 <= a < re_hp e1 + req_size (re_kh e1)) ->
(forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W1) mR1 (as_errno B + i)) ->
(forall a, in_img SEGS a -> ~ aowned B ly1 S1 a -> ~ aowned B ly2 S2 a -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (res <= a < res + req_size (8 * re_nheld e1 + 8) \/
     re_hp e1 <> 0 /\ re_hp e1 <= a < re_hp e1 + req_size (re_kh e1)) ->
  apresent (w_H W1) mR1 a -> apresent (w_H W2) mem2 a) ->
mem_grows (mrestrict (w_H W1) m1) (mrestrict (w_H W1) mR1) ->
mem_grows (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) m2) ->
(forall aa, 0 <= aa < 2 ^ 64 -> ~ (dxSA cx + 40 <= aa < dxSA cx + 52) ->
  aview SEGS (w_H W1) mR1 aa = aview SEGS (w_H W1) m1 aa) ->
(forall aa, 0 <= aa < 2 ^ 64 -> ~ (dxSA cx + 40 <= aa < dxSA cx + 52) ->
  aview SEGS (w_H W2) m2 aa = aview SEGS (w_H W2) mem2 aa) ->
mo_le MT S1 S2 (mo_malloc MT (8 * re_nheld e1 + 8) + mo_free MT) ->
val_mem SEGS (arm W2 m2) (dxSA cx + 40) 8 res ->
val_mem SEGS (arm W2 m2) (dxSA cx + 48) 4 (re_nheld e1) ->
rom_view SEGS W2 m2 ->
(forall aa, dsp0 cx - DRAIN_FRAME <= aa < dsp0 cx -> abyte_kept W1 m1 W2 m2 aa) ->
rp_RM RP S2 (Z.to_nat (tr_cost MT_rk (RelayRunT.RMalloc (Z.of_nat (length xx) + 1) :: tl2)) + kr) ->
cnt_ok_pk RP (fun P => (Z.to_nat (tr_peakP P (RelayRunT.RMalloc (Z.of_nat (length xx) + 1) :: tl2)) + 2)%nat)
  (ablocks B ly2 S2) ->
GARB_xR B PST ARx MT RP MMAX RG R cx Hp kr s1 D p q ly2 S2 Hp2 W2 m2 md2 (k1 + 3) (ga_entry e1 res (8 * re_nheld e1 + 8))
  h1 out1 ev1 LB1 (spent + (mo_malloc MT (8 * re_nheld e1 + 8) + mo_free MT))
  (RelayRunT.RMalloc (Z.of_nat (length xx) + 1) :: tl2).
Proof.
intros cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl mR1 ly2 S2 Hp2 W2 mem2 m2 md2 res xx tl2
  HB HCORE Hges Hidx Etra Etrc HmxT HJ2 Hfr2 Hres4096 BASEP Hcopy (K1 & K2 & K3 & K4 & K5 & K6) Herr2 Hpres2
  HGr1 HGr2 KR1 KR2 Hmle2 V40 V48 ROM2 FK HRMn HCNTn.
unfold GSB_xR in HCORE.
destruct HCORE as (HDMEM & HLINK & HSAME & HHIST & HRST & HBUD).
destruct HDMEM as (HJ & HROM & HPRESK & HFRM & HFRAME & HENTB & HAWR & HOKX & HSRC & HOTH & HGSK & HOUT & HLIVE & HPERM).
cbn [dvirt drain_b_c.ds_ocap drain_b_c.ds_no] in HOUT, HPERM, HLIVE.
pose proof HB as (_ & _ & _ & HGle & HSAle & _ & _ & _ & Hj & _).
pose proof asan_consts as (C1 & _).
pose proof YM05.alloc_ceiling_lt as HAC.
assert (AR1 : ARx ly1 S1 Hp1 W1 m1 md1) by (destruct HJ as (_ & _ & (mS1 & HJ1 & _) & _); exact (proj1 HJ1)).
assert (AR2 : ARx ly2 S2 Hp2 W2 m2 md2) by (destruct HJ2 as (_ & _ & (mS2 & HJ2x & _) & _); exact (proj1 HJ2x)).
pose proof HOKX as (_ & _ & Kp1 & Kp2 & _ & _ & HU & _ & HBUF & Hnh & HHP & _ & _ & _).
assert (HNH : re_nheld e1 = Z.of_nat (length (re_keys e1))) by reflexivity.
assert (Hnh0 : 0 <= re_nheld e1) by (rewrite HNH; clear - Hnh; lia).
assert (RQT : req_size ATABLE = 896) by reflexivity.
assert (RQN : req_size (8 * re_nheld e1 + 8) = 8 * re_nheld e1 + 8)
  by (unfold req_size; destruct (Z.eqb_spec (8 * re_nheld e1 + 8) 0) as [E0|E0];
      [exfalso; clear - Hnh0 E0; lia | reflexivity]).
(* ---- the live blocks before and after ---- *)
match type of HPERM with Permutation _ (_ :: aentry_blks _ ++ ?r) => pose (Rbl := r) end.
pose (TB := (dxG cx, ATABLE)).
pose (NB := (res, 8 * re_nheld e1 + 8)).
pose (BUF := if re_cap e1 =? 0 then [] else [(re_buf e1, re_cap e1)]).
pose (KEYS := map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e1)).
pose (X := BUF ++ KEYS ++ Rbl).
assert (PN : Permutation (ablocks B ly2 S2) (NB :: TB :: X)) by exact BASEP.
assert (PT : Permutation (ablocks B ly2 S2) (TB :: NB :: X)) by exact (Permutation_trans PN (perm_swap TB NB X)).
assert (TB1 : In TB (ablocks B ly1 S1)) by (apply (Permutation_in _ (Permutation_sym HPERM)); left; reflexivity).
assert (TB2 : In TB (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym PT)); left; reflexivity).
assert (NB2 : In NB (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym PN)); left; reflexivity).
assert (X2 : forall b, In b X -> In b (ablocks B ly2 S2))
  by (intros b Hb; apply (Permutation_in _ (Permutation_sym PN)); right; right; exact Hb).
assert (X1 : forall b, In b X -> In b (ablocks B ly1 S1)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym HPERM)). right. unfold aentry_blks. rewrite <- !app_assoc.
  unfold X in Hb. apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|].
  apply in_or_app; right. apply in_or_app; right. exact Hb. }
assert (PH1 : re_hp e1 <> 0 -> Permutation (ablocks B ly1 S1) ((re_hp e1, re_kh e1) :: TB :: X)).
{ intros Hz.
  assert (EA1 : aentry_blks e1 = BUF ++ (re_hp e1, re_kh e1) :: KEYS)
    by (unfold aentry_blks, BUF, KEYS; rewrite (proj2 (Z.eqb_neq (re_hp e1) 0) Hz); reflexivity).
  eapply Permutation_trans; [exact HPERM|]. rewrite EA1, <- app_assoc.
  eapply Permutation_trans; [apply perm_skip; apply Permutation_sym, Permutation_middle|].
  apply perm_swap. }
assert (DTN : zdisjoint (block_rng TB) (block_rng NB))
  by exact (ga_sep_head_x ly2 S2 Hp2 W2 m2 md2 TB (NB :: X) NB AR2 PT (or_introl eq_refl)).
assert (DTX : forall b, In b X -> zdisjoint (block_rng TB) (block_rng b))
  by (intros b Hb; exact (ga_sep_head_x ly2 S2 Hp2 W2 m2 md2 TB (NB :: X) b AR2 PT (or_intror Hb))).
assert (DNX : forall b, In b X -> zdisjoint (block_rng NB) (block_rng b))
  by (intros b Hb; exact (ga_sep_head_x ly2 S2 Hp2 W2 m2 md2 NB (TB :: X) b AR2 PN (or_intror Hb))).
assert (DHX : re_hp e1 <> 0 -> forall b, In b X -> zdisjoint (block_rng (re_hp e1, re_kh e1)) (block_rng b))
  by (intros Hz b Hb; exact (ga_sep_head_x ly1 S1 Hp1 W1 m1 md1 _ (TB :: X) b AR1 (PH1 Hz) (or_intror Hb))).
assert (DHT : re_hp e1 <> 0 -> zdisjoint (block_rng (re_hp e1, re_kh e1)) (block_rng TB))
  by (intros Hz; exact (ga_sep_head_x ly1 S1 Hp1 W1 m1 md1 _ (TB :: X) TB AR1 (PH1 Hz) (or_introl eq_refl))).
(* ---- what the arm keeps ---- *)
assert (BKV : forall pb mb x, In (pb, mb) (ablocks B ly1 S1) -> pb <= x < pb + req_size mb ->
  ~ (dxSA cx + 40 <= x < dxSA cx + 52) -> ~ (res <= x < res + req_size (8 * re_nheld e1 + 8)) ->
  ~ (re_hp e1 <> 0 /\ re_hp e1 <= x < re_hp e1 + req_size (re_kh e1)) ->
  aview SEGS (w_H W2) m2 x = aview SEGS (w_H W1) m1 x).
{ intros pb mb x Hb Hx H40 Hn Ho.
  destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 pb mb AR1 Hb) as (_ & H4 & Hc & _).
  assert (Hr : 0 <= x < 2 ^ 64) by (clear - H4 Hc Hx C1; lia).
  rewrite (KR2 x Hr H40).
  pose proof (K2 pb mb (x - pb) Hb ltac:(clear - Hx; lia)) as E2.
  replace (pb + (x - pb)) with x in E2 by ring.
  rewrite E2; [exact (KR1 x Hr H40)|].
  cbv beta. intros [G1|G2]; [exact (Hn G1) | exact (Ho G2)]. }
assert (WK2 : forall pb mb x, In (pb, mb) (ablocks B ly2 S2) -> pb <= x < pb + req_size mb ->
  writable_at SEGS (arm W2 m2) x).
{ intros pb mb x Hb Hx. destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 m2 md2 pb mb AR2 Hb) as (_ & _ & _ & _ & Hpr & _).
  apply (apresent_writable SEGS). exact (proj1 (Hpr x Hx)). }
assert (KO : forall b x, In b X -> fst b <= x < fst b + req_size (snd b) -> abyte_kept W1 m1 W2 m2 x).
{ intros [pb mb] x Hb Hx. cbn [fst snd] in Hx. split.
  - apply (BKV pb mb x (X1 _ Hb) Hx).
    + intros H40. pose proof (DTX _ Hb) as Dj. unfold zdisjoint, block_rng, TB in Dj. cbn [fst snd] in Dj.
      rewrite RQT in Dj. clear - Dj Hx H40 HGle HSAle. unfold AENT, ATABLE in *. lia.
    + intros Hn. pose proof (DNX _ Hb) as Dj. unfold zdisjoint, block_rng, NB in Dj. cbn [fst snd] in Dj.
      clear - Dj Hx Hn. lia.
    + intros (Hz & Ho). pose proof (DHX Hz _ Hb) as Dj. unfold zdisjoint, block_rng in Dj. cbn [fst snd] in Dj.
      clear - Dj Hx Ho. lia.
  - intros _. exact (WK2 pb mb x (X2 _ Hb) Hx). }
assert (TK : forall x, dxSA cx <= x < dxSA cx + AENT -> ~ (dxSA cx + 40 <= x < dxSA cx + 52) ->
  aview SEGS (w_H W2) m2 x = aview SEGS (w_H W1) m1 x).
{ intros x Hx H40.
  apply (BKV (dxG cx) ATABLE x TB1 ltac:(rewrite RQT; clear - Hx HGle HSAle; unfold AENT, ATABLE in *; lia) H40).
  - intros Hn. pose proof DTN as Dj. unfold zdisjoint, block_rng, TB, NB in Dj. cbn [fst snd] in Dj.
    rewrite RQT in Dj. clear - Dj Hx Hn HGle HSAle. unfold AENT, ATABLE in *. lia.
  - intros (Hz & Ho). pose proof (DHT Hz) as Dj. unfold zdisjoint, block_rng, TB in Dj. cbn [fst snd] in Dj.
    rewrite RQT in Dj. clear - Dj Hx Ho HGle HSAle. unfold AENT, ATABLE in *. lia. }
assert (NIMG : forall x, in_img SEGS x -> ~ (dxSA cx + 40 <= x < dxSA cx + 52)).
{ intros x Hx Hw. apply (blk_img_x _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (dxG cx) ATABLE x AR1 TB1); [|exact Hx].
  rewrite RQT. clear - Hw HGle HSAle. unfold AENT, ATABLE in *. lia. }
assert (IMR : forall x, in_img SEGS x -> 0 <= x < 2 ^ 64)
  by (intros x Hi; pose proof (pa_segs_low x Hi) as Hl; unfold kLowMemEnd in Hl; clear - Hl; lia).
assert (Hnot : forall x ly0 S0 Hq0 (W0 : world SEGS) mm md0, ARx ly0 S0 Hq0 W0 mm md0 -> in_img SEGS x ->
  ~ Exists (in_zr x) (as_owned_static B) -> ~ aowned B ly0 S0 x).
{ intros x ly0 S0 Hq0 W0 mm md0 HAl Hi Ho Hw. apply Ho.
  exact (proj1 (alx_owned_image _ _ _ LAWS ly0 S0 Hq0 W0 mm md0 x HAl Hi) Hw). }
assert (NBLK : forall x, in_img SEGS x -> ~ (res <= x < res + req_size (8 * re_nheld e1 + 8) \/
    re_hp e1 <> 0 /\ re_hp e1 <= x < re_hp e1 + req_size (re_kh e1))).
{ intros x Hi [Hn | (Hz & Ho)].
  - exact (blk_img_x _ _ _ LAWS ly2 S2 Hp2 W2 m2 md2 res (8 * re_nheld e1 + 8) x AR2 NB2 Hn Hi).
  - destruct HHP as [(Hz0 & _) | (_ & Hin & _)]; [exact (Hz Hz0)|].
    exact (blk_img_x _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 _ _ x AR1 Hin Ho Hi). }
assert (PK : forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) ->
  ~ (as_errno B <= x < as_errno B + 4) -> apresent (w_H W1) m1 x -> apresent (w_H W2) m2 x).
{ intros x Hi Ho He Hpx. apply (ga_apresent_grows _ _ _ _ HGr2).
  apply (Hpres2 x Hi (Hnot x _ _ _ _ _ _ AR1 Hi Ho) (Hnot x _ _ _ _ _ _ AR2 Hi Ho) He (NBLK x Hi)).
  exact (ga_apresent_grows _ _ _ _ HGr1 Hpx). }
assert (IK : forall x, in_img SEGS x -> ~ Exists (in_zr x) (as_owned_static B) ->
  ~ (as_errno B <= x < as_errno B + 4) -> aview SEGS (w_H W2) m2 x = aview SEGS (w_H W1) m1 x).
{ intros x Hi Ho He.
  rewrite (KR2 x (IMR x Hi) (NIMG x Hi)), (K3 x Hi Ho He). exact (KR1 x (IMR x Hi) (NIMG x Hi)). }
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VE & _).
assert (EK : forall x, as_errno B <= x < as_errno B + 4 -> abyte_kept W1 m1 W2 m2 x).
{ intros x Hx.
  assert (Hg : inG (G_DR B RG) x).
  { unfold G_DR, G_SL, inG.
    repeat first [ apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; clear - Hx; lia | apply Exists_cons_tl ]. }
  pose proof (proj1 (HG x Hg)) as Hi.
  assert (EV : aview SEGS (w_H W2) m2 x = aview SEGS (w_H W1) m1 x).
  { rewrite (KR2 x (IMR x Hi) (NIMG x Hi)).
    pose proof (Herr2 (x - as_errno B) ltac:(clear - Hx; lia)) as E2.
    replace (as_errno B + (x - as_errno B)) with x in E2 by ring.
    rewrite E2. exact (KR1 x (IMR x Hi) (NIMG x Hi)). }
  split; [exact EV|]. intros _.
  apply (ga_img_wr RG); [exact Hi | exact (HGR x Hg) |].
  rewrite EV. unfold aview. unfold arm in VE.
  replace x with (as_errno B + Z.of_nat (Z.to_nat (x - as_errno B))) by (clear - Hx; lia).
  rewrite (VE (Z.to_nat (x - as_errno B)) ltac:(clear - Hx; lia)). cbn [option_map]. discriminate. }
assert (GK : forall x, inG (G_DR B RG) x \/ inG [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)] x ->
  abyte_kept W1 m1 W2 m2 x).
{ intros x Hx.
  assert (IO : in_img SEGS x /\ ~ Exists (in_zr x) (as_owned_static B))
    by (destruct Hx as [Hx|Hx]; [exact (conj (proj1 (HG x Hx)) (proj1 (proj2 (HG x Hx)))) | exact (conj (proj1 (HGO x Hx)) (proj1 (proj2 (HGO x Hx))))]).
  destruct IO as [Hi Ho].
  assert (Hdec : (as_errno B <= x < as_errno B + 4) \/ ~ (as_errno B <= x < as_errno B + 4)) by (clear - Hi; lia).
  destruct Hdec as [He | Hne]; [exact (EK x He)|].
  split; [exact (IK x Hi Ho Hne)|].
  intros Hw. apply (ga_writable_kept (w_H W1) (w_H W2) m1 m2 x); [|exact Hw].
  intros Hpx. exact (PK x Hi Ho Hne Hpx). }
assert (GGS : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> abyte_kept W1 m1 W2 m2 x).
{ intros x Hx. apply GK. left. unfold G_DR, inG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Hx. }
(* ---- the memory core ---- *)
assert (PK2 : apres_kept B (dxW cx) (dxmem cx) W2 m2)
  by (intros x Hi Ho He Hpx; exact (PK x Hi Ho He (HPRESK x Hi Ho He Hpx))).
destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 m2 md2 _ _ AR2 NB2) as (_ & _ & Hrc & _).
rewrite RQN in Hrc.
assert (Hres64 : 0 <= res < 2 ^ 64) by (clear - Hrc Hres4096 HAC Hnh0; lia).
assert (ENT2 : garr8 SEGS (arm W2 m2) (dxSA cx) (bzs (entry_bytes (ga_entry e1 res (8 * re_nheld e1 + 8))))).
{ refine (gax_entry_store RG HGSB W1 m1 W2 m2 (dxSA cx) e1 (ga_entry e1 res (8 * re_nheld e1 + 8)) Kp1 Kp2
    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Hres64 _ HENTB V40 V48 _ _).
  - change (re_nheld (ga_entry e1 res (8 * re_nheld e1 + 8))) with (re_nheld e1). clear - Hnh Hnh0. lia.
  - intros x Hx. apply TK; [unfold AENT; clear - Hx; lia | clear - Hx; lia].
  - intros x Hx. apply TK; [unfold AENT; clear - Hx; lia | clear - Hx; lia]. }
assert (AWR2 : awr W2 m2 (dxSA cx) AENT).
{ intros i Hi. apply (WK2 (dxG cx) ATABLE (dxSA cx + i) TB2). rewrite RQT.
  clear - Hi HGle HSAle. unfold AENT, ATABLE in *. lia. }
assert (PERM2 : Permutation (ablocks B ly2 S2)
  ((dxG cx, ATABLE) :: aentry_blks (ga_entry e1 res (8 * re_nheld e1 + 8)) ++ Rbl)).
{ assert (EA2 : aentry_blks (ga_entry e1 res (8 * re_nheld e1 + 8)) = BUF ++ NB :: KEYS).
  { unfold ga_entry, aentry_blks, BUF, KEYS, NB. cbn [re_cap re_buf re_hp re_kh re_keys].
    rewrite (proj2 (Z.eqb_neq res 0) ltac:(clear - Hres4096; lia)). reflexivity. }
  eapply Permutation_trans; [exact PT|]. apply perm_skip.
  rewrite EA2, <- app_assoc. change ((NB :: KEYS) ++ Rbl) with (NB :: (KEYS ++ Rbl)).
  apply Permutation_middle. }
assert (OKX2 : aentry_okx B ly2 S2 W2 m2 (ga_entry e1 res (8 * re_nheld e1 + 8))).
{ apply (gb_okx B ly1 S1 W1 m1 ly2 S2 W2 m2 e1 res HOKX ltac:(clear - Hres4096; lia)).
  - intros b Hb. apply (Permutation_in _ (Permutation_sym PERM2)). right. apply in_or_app. left. exact Hb.
  - intros r Hr x Hx. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    + destruct (re_cap e1 =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<- | []].
      destruct HBUF as [(Hc0 & _) | (Hcp & _ & HJk & _)]; [apply Z.eqb_neq in Ec; contradiction|].
      apply (KO (re_buf e1, re_cap e1) x).
      * unfold X, BUF. apply in_or_app. left. rewrite ?Ec. left. reflexivity.
      * unfold gfp in Hx. cbn [fst snd] in Hx |- *. unfold bzs in Hx. rewrite length_map, length_app in Hx.
        pose proof (req_size_pos (re_cap e1) ltac:(clear - Hcp; lia)) as (_ & RQ). clear - Hx HU HJk RQ. lia.
    + apply in_map_iff in Hr as (k & <- & Hk).
      apply (KO (key_addr k, Z.of_nat (length (key_text k)) + 1) x).
      * unfold X. apply in_or_app. right. apply in_or_app. left. unfold KEYS.
        apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk.
      * unfold gfp in Hx. cbn [fst snd] in Hx |- *. unfold bzs in Hx. rewrite length_map, length_app in Hx.
        cbn [length] in Hx.
        pose proof (req_size_pos (Z.of_nat (length (key_text k)) + 1) ltac:(clear - Hk; lia)) as (_ & RQ).
        clear - Hx RQ. lia.
  - (* the new array: its first 8 nheld bytes are the ones realloc copied from the old array *)
    destruct HHP as [(Hz & Hk0) | (Hz & Hin & Hk1 & Hk2 & Hg)].
    + rewrite Hk0. exact (garr8_nil SEGS (arm W2 m2) res).
    + destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 _ _ AR1 Hin) as (_ & Hh4 & Hhc & _).
      assert (RQH : req_size (re_kh e1) = re_kh e1)
        by (unfold req_size; destruct (Z.eqb_spec (re_kh e1) 0) as [E0|E0];
            [exfalso; clear - Hk2 E0; lia | reflexivity]).
      rewrite RQH in Hhc.
      pose proof (DHT Hz) as Dh. unfold zdisjoint, block_rng, TB in Dh. cbn [fst snd] in Dh. rewrite RQH, RQT in Dh.
      pose proof DTN as Dn. unfold zdisjoint, block_rng, TB, NB in Dn. cbn [fst snd] in Dn. rewrite RQT, RQN in Dn.
      apply (gb_garr8_move RG W1 m1 W2 m2 (re_hp e1) res _ Hg).
      intros i Hi. rewrite gax_bzs_len, gs_key_ptrs_len in Hi.
      assert (Hi8 : 0 <= i < 8 * re_nheld e1) by (rewrite HNH; clear - Hi; lia).
      assert (Hr1 : 0 <= res + i < 2 ^ 64) by (clear - Hi8 Hrc Hres4096 HAC; lia).
      assert (Hr2 : 0 <= re_hp e1 + i < 2 ^ 64) by (clear - Hi8 Hk1 Hhc Hh4 HAC; lia).
      rewrite (KR2 (res + i) Hr1 ltac:(clear - Dn Hi8 HGle HSAle; unfold AENT, ATABLE in *; lia)).
      rewrite (Hcopy Hz i ltac:(clear - Hi8 Hk1; lia)).
      exact (KR1 (re_hp e1 + i) Hr2 ltac:(clear - Dh Hi8 Hk1 HGle HSAle; unfold AENT, ATABLE in *; lia)). }
assert (SRC2 : asrc_at B ly2 S2 W2 m2 (dHA RG cx) h1).
{ apply (asrc_at_kept B ly1 S1 W1 m1 ly2 S2 W2 m2 (dHA RG cx) h1 HSRC).
  - intros r Hr x Hx.
    destruct (ga_src_fp B RG HGSB ly1 S1 W1 m1 (dHA RG cx) h1 HSRC r x Hr Hx) as [Hg | (b & Hb & Hbx)].
    + apply GGS. unfold dHA in Hg. clear - Hg Hj. unfold ASRC in *. lia.
    + apply (KO b x); [|exact Hbx]. unfold X, Rbl. apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. left. exact Hb.
  - intros b Hb. apply X2. unfold X, Rbl. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    exact Hb. }
assert (OTH2 : aothers_at RG W2 m2 (dxj cx) (re_fd (dxe cx))).
{ intros i Hi Hij. destruct (HOTH i Hi Hij) as (f & o' & VV1 & VV2 & Ho). exists f, o'.
  assert (GV : forall a0 (nn : nat) v, rg_s RG <= a0 -> a0 + Z.of_nat nn <= rg_s RG + 4 * ASRC ->
    val_mem SEGS (arm W1 m1) a0 nn v -> val_mem SEGS (arm W2 m2) a0 nn v).
  { intros a0 nn v H1 H2 H. apply (akept_vm W1 m1); [|exact H]. intros y Hy. apply GGS. clear - H1 H2 Hy. lia. }
  split; [apply GV; [| | exact VV1] | split; [apply GV; [| | exact VV2] | exact Ho]]; clear - Hi; unfold ASRC; lia. }
assert (GSK2 : forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> ~ (dHA RG cx <= x < dHA RG cx + ASRC) ->
  abyte_kept (dxW cx) (dxmem cx) W2 m2 x)
  by (intros x H1 H2; exact (ga_bk_trans _ _ W1 m1 W2 m2 x (HGSK x H1 H2) (GGS x H1))).
match type of HOUT with aout_at B RG ly1 S1 W1 m1 ?c ?O ?mx ?no ?cap ?out =>
  assert (OUT2 : aout_at B RG ly2 S2 W2 m2 c O mx no cap out) end.
{ apply (aout_at_kept B RG ly1 S1 W1 m1 ly2 S2 W2 m2 _ _ _ _ _ _ HOUT).
  - intros r Hr x Hx. destruct (ga_out_fp B RG _ _ r x Hr Hx) as [Hg | [Hg | (Hc & Hx2)]];
      [apply GK; left; exact Hg | apply GK; right; exact Hg |].
    apply (KO (out1, GSoc cx s1 p q) x).
    + unfold X, Rbl. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
      unfold aout_blks. rewrite (proj2 (Z.eqb_neq _ _) Hc). left. reflexivity.
    + cbn [fst snd]. unfold req_size. rewrite (proj2 (Z.eqb_neq _ _) Hc). exact Hx2.
  - intros b Hb. apply X2. unfold X, Rbl. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
    apply in_or_app. left. exact Hb. }
(* ---- the model: only the array size moved, to seen_ka ---- *)
assert (Hlen_eq : Z.of_nat (length (dlH cx s1 p)) = re_nheld e1).
{ pose proof HLINK as (_ & _ & _ & DH & _). unfold re_nheld. do 2 f_equal. cbn [drain_b_c.ds_H dvirt] in DH.
  rewrite <- DH, gs_keys_texts_len. reflexivity. }
destruct (gs_seen_begin_new (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q) xx 0%nat RelayRunF.adr0 [] Hges Hidx)
  as (_ & _ & Eka).
assert (EKA : 8 * re_nheld e1 + 8 = seen_ka (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q))
  by (rewrite Eka, <- Hlen_eq; ring).
(* ---- the meter ---- *)
pose proof HBUD as ((Hle & Hsp & Hcost & Hlv & Hmax) & _ & _).
assert (BB : blocks_bytes S2 = blocks_bytes S1 - drain_b_c.ent_ka e1 + (8 * re_nheld e1 + 8)).
{ rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ PN), (bsum_perm _ _ HPERM).
  unfold X, BUF, KEYS, NB, TB, Rbl, aentry_blks, drain_b_c.ent_ka. rewrite !bsum_cons, !bsum_app. cbn [fst snd].
  destruct (Z.eqb_spec (re_hp e1) 0) as [Hz|Hz]; cbn [bsum fold_right snd]; clear - Hz; lia. }
assert (DB2 : dbud MT MMAX cx S2 (spent + (mo_malloc MT (8 * re_nheld e1 + 8) + mo_free MT))
  (RelayRunT.RMalloc (Z.of_nat (length xx) + 1) :: tl2)).
{ pose proof (mo_free_nonneg MT MTL) as Hf0.
  assert (Hm0 : 0 <= mo_malloc MT (8 * re_nheld e1 + 8)) by (apply (mo_malloc_nonneg MT MTL); clear - Hnh0; lia).
  assert (CT : tr_cost MT (RelayRunT.RMalloc (Z.of_nat (length xx) + 1) :: tl2) =
    (mo_malloc MT (Z.of_nat (length xx) + 1) + mo_free MT) + tr_cost MT tl2) by reflexivity.
  split; [exact (mle_station MT (dxS cx) S1 S2 spent _ MTL Hle Hmle2)|].
  split; [clear - Hsp Hf0 Hm0; lia|].
  split; [rewrite CT; clear - Hcost Etrc; lia|].
  split; [clear - Hlv Etra BB; lia|].
  clear - Hmax HmxT; lia. }
(* ---- the cut's core ---- *)
unfold GARB_xR, LCORE_xR. cbv zeta.
split.
{ unfold DMEM_xR. cbn [dvirt drain_b_c.ds_ocap drain_b_c.ds_no].
  refine (conj HJ2 (conj ROM2 (conj PK2 (conj (eq_trans Hfr2 HFRM) (conj (ga_frame_kept RG HGSB cx W1 m1 W2 m2 FK HFRAME)
    (conj ENT2 (conj AWR2 (conj OKX2 (conj SRC2 (conj OTH2 (conj GSK2 (conj OUT2 (conj HLIVE _))))))))))))).
  exact PERM2. }
split; [exact (gb_dlink cx s1 false (dlH cx s1 p) (dlka cx s1 p) _ (GSno cx s1 p q) (GSoc cx s1 p q) e1 res
  (8 * re_nheld e1 + 8) h1 HLINK ltac:(clear - Hres4096; lia) EKA)|].
split.
{ pose proof HSAME as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & _).
  refine (conj T1 (conj T2 (conj T3 (conj T4 (conj T5 (conj T6 (conj T7 (conj T8 (conj T9 (or_intror _)))))))))).
  cbn [ga_entry re_kh]. clear - Hnh Hnh0. lia. }
split; [exact (gb_dhist _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HHIST)|].
split; [exact HRST | exact (conj DB2 (conj HRMn HCNTn))].
Qed.
(* ---- (6) GA (0x8389c) -> DLN (S q) over ARx, through GAR (0x838d8) ---- *)
Theorem gs_adda_xR : gs_addb_stmt_xR B PST ARx MT RP MMAX RG R -> gs_add_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
intros ADDB. unfold gs_add_stmt_xR. intros cx Hp kr s1 D p q W1 c1 HB HGA HN.
destruct HGA as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & e1 & h1 & out1 & ev1 & LB1 & spent & jb & a & o & ha & ks &
  tl & kd & jj & bg & Hc1 & HRL & R23 & R24 & R25 & R19 & R10 & R11 & R12 & V72 & Hbgr & Hbgk & Hges & Hjj & Hidx &
  HGSF & HCORE & HFUT).
pose proof HCORE as (HDMEM & HLINK & HSAME & HHIST & HRSTART & HBUD).
pose proof HDMEM as (HJ & HROM & HPRES & HFRS & HFRAME & HENT & HAWR & HOKX & HSRC & HOTH & HKEPT & HOUT & HLIVE & HPERM).
pose proof HRL as (Usp & R3 & R4 & R22 & R27 & R18 & R9 & R8 & R21 & HFR2 & V192 & V200 & V56 & V48 & V64).
pose proof HFR2 as (F208 & F96 & F128 & _).
pose proof HB as (HPRE & HSA & HGin & HGle & HSAle & HGARR & HAWR0 & HENT0 & HB9 & HB10 & HB11 & HB12 & HB13 &
  HB14 & HB15 & HB16 & HPERM0 & HB18 & HB19 & HB20 & HB21 & HB22 & HMOK & HRM0 & HCNT0).
pose proof HJ as (_ & _ & (memS & HJi & HAG) & _).
assert (HAR1 : ARx ly1 S1 Hp1 W1 m1 md1) by exact (proj1 HJi).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
rewrite !Z.add_0_r in Hal16, Hslo, Hshi, Hstk0.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : DRAIN_STK_x = 16976) by reflexivity.
assert (Has : ASTACK = 16384) by reflexivity.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (HGin1 : In (dxG cx, ATABLE) (ablocks B ly1 S1))
  by (apply (Permutation_in _ (Permutation_sym HPERM)); left; reflexivity).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 _ _ HAR1 HGin1) as (HG16 & HG4096 & HGceil & HGapp & HGpres & _).
assert (RQT : req_size ATABLE = 896) by (vm_compute; reflexivity).
rewrite RQT in HGceil, HGapp, HGpres.
assert (HSAlo : 4096 <= dxSA cx) by (unfold ATABLE in HGle; lia).
assert (HSAhi : dxSA cx + 56 <= alloc_ceiling) by (unfold ATABLE, AENT in *; lia).
assert (HSAhiG : dxSA cx + 56 <= GA_HI) by (unfold GA_HI; lia).
assert (WF : DRAIN_FRAME = 336) by reflexivity.
(* the relay entry's fields *)
pose proof HOKX as (K1 & K2 & Kp1 & Kp2 & K5 & K6 & K7 & K8 & KBUF & KNH & KHP & KND1 & KND2 & KF).
assert (Hnh0 : 0 <= re_nheld e1) by (unfold re_nheld; lia).
assert (Hhp : 0 <= re_hp e1 <= GA_HI).
{ destruct KHP as [(Hz & _) | (Hnz & Hin & Hle & H8 & Hg)].
  - rewrite Hz. unfold GA_HI. lia.
  - destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 _ _ HAR1 Hin) as (_ & H4 & Hc & _).
    assert (RQH : req_size (re_kh e1) = re_kh e1)
      by (unfold req_size; destruct (Z.eqb_spec (re_kh e1) 0); lia).
    rewrite RQH in Hc. unfold GA_HI. lia. }
(* the frame base, and the bounds the seat wants *)
assert (R2 : getr regs1 2 = w64 (dsp0 cx - DRAIN_FRAME)).
{ unfold w64. rewrite <- Usp. unfold spZ. symmetry. apply Z_to_bv_bv_unsigned. }
assert (Hsp46 : 2 ^ 46 <= dsp0 cx - DRAIN_FRAME) by (rewrite WF; lia).
assert (Hsp47 : dsp0 cx - DRAIN_FRAME + 336 <= 2 ^ 47) by (rewrite WF; lia).
assert (Hsp16 : (dsp0 cx - DRAIN_FRAME) mod 16 = 0)
  by (rewrite WF, Zminus_mod, Hal16; reflexivity).
assert (HSAsp : dxSA cx + 56 + 16512 <= dsp0 cx - DRAIN_FRAME) by (rewrite WF; lia).
(* the two cells of the entry, read off its byte image *)
assert (VH40 : val_mem SEGS (arm W1 m1) (dxSA cx + 40) 8 (re_hp e1))
  by (apply (gax_entry_hp RG HGSB W1 m1 _ e1 Kp1 ltac:(unfold GA_HI in *; lia) HENT)).
assert (VH48 : val_mem SEGS (arm W1 m1) (dxSA cx + 48) 4 (re_nheld e1))
  by (apply (gax_entry_nheld RG HGSB W1 m1 _ e1 Kp1 ltac:(lia) HENT)).
assert (HWR : forall oo, 40 <= oo < 52 -> writable_at SEGS (arm W1 m1) (dxSA cx + oo))
  by (intros oo Hoo; apply HAWR; unfold AENT; lia).
assert (Hnh26 : 0 <= re_nheld e1 <= 2 ^ 26) by lia.
(* the seat *)
pose proof (ga_seat RG HGSB W1 regs1 m1 (dxSA cx) (dsp0 cx - DRAIN_FRAME) (re_hp e1) (re_nheld e1)
  R2 R10 R11 R12 R21 R22 HSAlo HSAhiG HSAsp Hhp Hnh26 Hsp46 Hsp47 Hsp16
  V72 F96 F128 VH40 VH48 HWR) as HS.
remember (Eimg (Ereg regs1 (ga_extra (re_hp e1)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EA : forall i, (i < 32)%nat -> ew E i = getr regs1 (Z_to_bv 5 (Z.of_nat i))).
{ intros i Hi. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). unfold Ereg. cbn [ew].
  destruct (Nat.ltb_spec i 32); [reflexivity | lia]. }
assert (E32 : ew E 32 = w64 (re_hp e1))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
clear HE.
assert (E2 : ew E 2 = w64 (dsp0 cx - DRAIN_FRAME)) by exact (eq_trans (EA 2%nat ltac:(lia)) R2).
assert (E3 : ew E 3 = getr regs1 3) by exact (EA 3%nat ltac:(lia)).
assert (E4 : ew E 4 = getr regs1 4) by exact (EA 4%nat ltac:(lia)).
assert (E10 : ew E 10 = w64 (re_nheld e1)) by exact (eq_trans (EA 10%nat ltac:(lia)) R10).
assert (E19 : ew E 19 = w64 bg) by exact (eq_trans (EA 19%nat ltac:(lia)) R19).
assert (E21 : ew E 21 = w64 SHADOW_OFF) by exact (eq_trans (EA 21%nat ltac:(lia)) R21).
assert (E22 : ew E 22 = w64 (dxSA cx)) by exact (eq_trans (EA 22%nat ltac:(lia)) R22).
assert (E23 : ew E 23 = w64 (re_buf e1 + Z.of_nat q)) by exact (eq_trans (EA 23%nat ltac:(lia)) R23).
assert (E24 : ew E 24 = w64 (re_buf e1 + Z.of_nat p)) by exact (eq_trans (EA 24%nat ltac:(lia)) R24).
assert (E25 : ew E 25 = w64 (re_buf e1 + Z.of_nat p + Z.of_nat jj)) by exact (eq_trans (EA 25%nat ltac:(lia)) R25).
assert (U22 : bv_unsigned (ew E 22) = dxSA cx)
  by (rewrite E22; apply unsigned_lit_small; unfold GA_HI in *; lia).
assert (SHOK : sh_ok SEGS gaBx ga_SH E (mrestrict (w_H W1) m1))
  by exact (ga_shok_x E ly1 S1 Hp1 W1 m1 md1 (dxG cx) (dxSA cx) HAR1 HGin1 HGle HSAle E21 E22 HSAlo HSAhiG).
subst c1. unfold cfg_at.
(* 0x8389c  bnez s3: an END not held returns at once; a BEGIN continues *)
psrr_branch_tok RUNR BRR HS SHOK gaBspan;
  rename Hc into BZ; rewrite (ga_bnez RG E 19 bg E19 ltac:(lia)) in BZ.
- (* bg <> 0: an END whose key is not held; the branch itself is the jump to DLN (S q) *)
  assert (Hbgn : bg <> 0)
    by (destruct (Z.eqb_spec bg 0); [cbn [negb] in BZ; discriminate | assumption]).
  assert (Hkd : kd = GEnd) by (destruct kd; [exfalso; apply Hbgn, Hbgk; reflexivity | reflexivity]).
  subst kd.
  pose proof HGSF as (HB1 & HPQ & HQ0 & HNZ & HKs & HLL).
  destruct (gs_drl s1 p q HB1 HPQ HQ0 HNZ HKs HLL) as (Edrl & Edrlq & Edskp).
  destruct (gs_seen_end_new (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q)
              (firstn jj (dline s1 p q)) jb ha ks Hges Hidx) as (Earr & Etr & Eka).
  unfold GSfut, dsfut in HFUT. cbv zeta in HFUT. rewrite Etr in HFUT.
  cbn [fst snd] in HFUT. rewrite Earr, Eka in HFUT.
  destruct HFUT as (tl2 & HLF & Htl). cbn [app] in Htl. subst tl.
  (* the branch itself (0x8389c -> 0x836f4): one instruction, no store *)
  paj_run_to_tok_xR RUNTOR HS HJ SHOK gaBspan A_dr_next.
  { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
      let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_x_cons; [intros aa Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U22 in Ha.
    left. split; [|lia]. right; left. split.
    - unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
      cbn [fst snd]. unfold AENT. lia.
    - exists (dxG cx), ATABLE. split; [exact HGin1|]. rewrite RQT. unfold AENT, ATABLE in *. lia. }
  rename HFr into HFrE, HG0 into HGrE. clear HF.
  lazymatch goal with |- SRrG _ R _ (mkCfg ?mm ?mo) _ => rename mm into msE; set (matE := mo) in * end.
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as REE. cbn [ms_mem restrict] in REE.
  assert (VE40 : val_mem SEGS (mrestrict (w_H W1) (ms_mem msE)) (dxSA cx + 40) (N.to_nat 8) (re_hp e1)).
  { eapply (field_of_region E _ 22 (dxSA cx)); [exact REE | exact U22 | ga_in_x | | unfold GA_HI in *; zside | zside].
    cbn [sv_denot]. rewrite E32, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (VE48 : val_mem SEGS (mrestrict (w_H W1) (ms_mem msE)) (dxSA cx + 48) (N.to_nat 4) (re_nheld e1)).
  { eapply (field_of_region E _ 22 (dxSA cx)); [exact REE | exact U22 | ga_in_x | | zside | zside].
    cbn [sv_denot]. rewrite E10, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  change (N.to_nat 8) with 8%nat in VE40. change (N.to_nat 4) with 4%nat in VE48.
  unfold arm in VH40, VH48.
  assert (KLE : forall x, 0 <= x < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem msE) x = aview SEGS (w_H W1) m1 x).
  { intros x Hx.
    assert (OUT : ~ (dxSA cx + 40 <= x < dxSA cx + 52) ->
                  aview SEGS (w_H W1) (ms_mem msE) x = aview SEGS (w_H W1) m1 x).
    { intros Hno. apply (aview_kept_out E _ (w_H W1) m1 (ms_mem msE) HFrE x Hx). apply ga_not_wrange.
      lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end.
      repeat constructor; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?U22; lia. }
    destruct (Z.lt_ge_cases x (dxSA cx + 40)) as [H1|H1]; [apply OUT; lia|].
    destruct (Z.lt_ge_cases x (dxSA cx + 52)) as [H2|H2]; [|apply OUT; lia].
    destruct (Z.lt_ge_cases x (dxSA cx + 48)) as [H3|H3].
    - replace x with (dxSA cx + 40 + Z.of_nat (Z.to_nat (x - (dxSA cx + 40)))) by lia.
      unfold aview. rewrite (VE40 (Z.to_nat (x - (dxSA cx + 40))) ltac:(lia)).
      rewrite (VH40 (Z.to_nat (x - (dxSA cx + 40))) ltac:(lia)). reflexivity.
    - replace x with (dxSA cx + 48 + Z.of_nat (Z.to_nat (x - (dxSA cx + 48)))) by lia.
      unfold aview. rewrite (VE48 (Z.to_nat (x - (dxSA cx + 48))) ltac:(lia)).
      rewrite (VH48 (Z.to_nat (x - (dxSA cx + 48))) ltac:(lia)). reflexivity. }
  assert (GRE : forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) (ms_mem msE) x)
    by (intros x Hpx; exact (apresent_grows _ _ _ _ HGrE Hpx)).
  assert (HHAb : rg_s RG <= dHA RG cx /\ dHA RG cx + ASRC <= rg_s RG + 4 * ASRC)
    by (unfold dHA, ASRC in *; lia).
  assert (HCOREE := ga_lcore_mem_xR cx Hp kr s1 D _ _ _ _ _ _ _ _ ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl2
    (ms_mem msE) matE HCORE HAR1 HJ KLE GRE ltac:(rewrite WF; lia) ltac:(lia) HSAlo
    ltac:(unfold AENT; lia) (proj1 HHAb) (proj2 HHAb)).
  pose proof HCOREE as (HDME & _). pose proof HDME as (_ & _ & _ & _ & HFRE & _).
  pmkst HS.
  prreg HS (2%bv : bv 5) X2. prreg HS (3%bv : bv 5) X3. prreg HS (4%bv : bv 5) X4.
  prreg HS (8%bv : bv 5) X8. prreg HS (9%bv : bv 5) X9. prreg HS (18%bv : bv 5) X18.
  prreg HS (21%bv : bv 5) X21. prreg HS (22%bv : bv 5) X22. prreg HS (23%bv : bv 5) X23.
  prreg HS (27%bv : bv 5) X27.
  assert (VKE : forall aa n v, 0 <= aa -> aa + Z.of_nat n <= 2 ^ 64 ->
                val_mem SEGS (arm W1 m1) aa n v -> val_mem SEGS (arm W1 (ms_mem msE)) aa n v)
    by (intros aa n v H1 H2 Hv; exact (ga_val_kept RG HGSB W1 m1 (ms_mem msE) aa n v KLE H1 H2 Hv)).
  apply HN. unfold DLN_xR.
  exists (ms_regs msE), ly1, S1, Hp1, (ms_mem msE), matE, k1, e1, h1, out1, ev1, LB1, spent.
  exists (jb + dnret (@nil (RelayRunT.rev YO0i.sptr)))%nat, a, o, ha, ks, tl2.
  split; [reflexivity|].
  split.
  { split; [unfold spZ; rewrite X2, E2; unfold w64; rewrite unsigned_lit_small by (rewrite WF; lia); reflexivity|].
    split; [rewrite X3, E3; exact R3|]. split; [rewrite X4, E4; exact R4|].
    split; [rewrite X22; exact E22|].
    split; [rewrite X27; exact (eq_trans (EA 27%nat ltac:(lia)) R27)|].
    split; [rewrite X18; exact (eq_trans (EA 18%nat ltac:(lia)) R18)|].
    split; [rewrite X9; exact (eq_trans (EA 9%nat ltac:(lia)) R9)|].
    split; [rewrite X8; exact (eq_trans (EA 8%nat ltac:(lia)) R8)|].
    split; [rewrite X21; exact E21|].
    split; [exact HFRE|].
    split; [apply VKE; [rewrite WF; lia | rewrite WF; lia | exact V192]|].
    split; [apply VKE; [rewrite WF; lia | rewrite WF; lia | exact V200]|].
    split; [apply VKE; [rewrite WF; lia | rewrite WF; lia | exact V56]|].
    split; [apply VKE; [rewrite WF; lia | rewrite WF; lia | exact V48]|].
    apply VKE; [rewrite WF; lia | rewrite WF; lia | exact V64]. }
  split; [rewrite X23, E23; f_equal; lia|].
  split; [split; [lia | right; replace (S q - 1)%nat with q by lia; exact HQ0]|].
  split; [lia|].
  split.
  + unfold DLC_xR. rewrite Edrl, Edskp, (gs_dlH cx s1 p q Edrl), (gs_dlka cx s1 p q Edrl),
      (gs_dlno s1 p q Edrl), (gs_dloc cx s1 p q Edrl), Earr, Eka.
    unfold GSB_xR, GSno, GSoc in HCOREE.
    eapply ga_lcore_end_xR; [exact HCOREE | exact Hges | exact Hidx | lia | apply app_assoc].
  + unfold GSno, GSoc. rewrite (gs_dlH cx s1 p q Edrl), (gs_dlka cx s1 p q Edrl),
      (gs_dlno s1 p q Edrl), (gs_dloc cx s1 p q Edrl), Earr, Eka. exact HLF.
- (* bg = 0: a BEGIN not held *)
  assert (Hbg0 : bg = 0) by (destruct (Z.eqb_spec bg 0); [assumption | cbn [negb] in BZ; discriminate]).
  (* 0x838a0 .. 0x838c0: `bne a0, a1` is never taken, the shadow byte of &s->held is covered and zero,
     a0 = s->held, a1 = 8 * nheld + 8, then the jal to realloc *)
  paj_run_tok_xR RUNR HS HJ SHOK gaBspan.
  { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
      let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_x_cons; [intros aa Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U22 in Ha.
    left. split; [|lia]. right; left. split.
    - unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
      cbn [fst snd]. unfold AENT. lia.
    - exists (dxG cx), ATABLE. split; [exact HGin1|]. rewrite RQT. unfold AENT, ATABLE in *. lia. }
  rename HFr into HFr1, HG0 into HGr1. clear HF.
  lazymatch goal with |- SRrG _ R _ (mkCfg ?mm _) _ => rename mm into ms1 end.
  pmkst HS.
  prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (1%bv : bv 5) P1.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8.
  pose proof HPRE as (HAR0 & Hraok & Hra4 & Hgp0 & Htp0 & Hstk0p & Hpres0 & Hch0 & HQT0).
  assert (P11v : getr (ms_regs ms1) 11 = w64 (8 * re_nheld e1 + 8)).
  { rewrite P11, E10. unfold w64. rewrite !zalu64_sound. f_equal.
    unfold zalu64, zcanon, M64. cbn [zalu_raw].
    rewrite (Z.mod_small (re_nheld e1)) by lia.
    replace (Z.land (3 mod 2 ^ 64) 63) with 3 by (vm_compute; reflexivity).
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
    rewrite !Z.mod_mod by lia.
    rewrite (Z.mod_small (re_nheld e1 * 8)) by lia.
    replace (8 mod 2 ^ 64) with 8 by (vm_compute; reflexivity).
    rewrite Z.mod_small by lia. lia. }
  assert (P10v : getr (ms_regs ms1) 10 = w64 (re_hp e1)) by (rewrite P10, E32; reflexivity).
  assert (P3v : getr (ms_regs ms1) 3 = w64 (as_gp B)) by (rewrite P3, E3, R3; exact Hgp0).
  assert (P4v : getr (ms_regs ms1) 4 = w64 (as_tp B)) by (rewrite P4, E4, R4; exact Htp0).
  assert (Usp1 : spZ (ms_regs ms1) = dsp0 cx - DRAIN_FRAME)
    by (unfold spZ; rewrite P2, E2; unfold w64; rewrite unsigned_lit_small by (rewrite WF; lia); reflexivity).
  (* the model: kd = GBegin (bg = 0), so seen_tr owes the realloc then the strndup *)
  assert (Hkd : kd = GBegin) by (apply (proj1 Hbgk); exact Hbg0). subst kd.
  pose proof HGSF as (HB1 & HPQ & HQ0 & HNZ & HKs & HLL).
  pose proof HLINK as (_ & _ & _ & DH & Dka & _ & _ & _ & _ & Den & Decap & _).
  assert (Hlen_eq : Z.of_nat (length (dlH cx s1 p)) = re_nheld e1).
  { unfold re_nheld. do 2 f_equal. cbn [drain_b_c.ds_H dvirt] in DH.
    rewrite <- DH, gs_keys_texts_len. reflexivity. }
  set (x := firstn jj (dline s1 p q)) in *.
  (* tr_sizes_ok tl: the DGS cut's dnext signs over LCORE_x, then gs_dsfut_sizes *)
  pose proof (gs_cut_facts_xR cx Hp kr s1 D _ _ _ _ _ _ _ _ ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl HCORE)
    as (Hu0 & Hcap0 & Hmx0 & Hno0 & Hoc0 & Hka0 & Hen0 & Hec0).
  pose proof (gs_dgs_dnext_signs_xR cx Hp kr s1 D _ _ _ _ _ _ _ _ ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl
    p q HB1 HPQ HQ0 HNZ HKs HLL eq_refl eq_refl (fun h => h) HCORE)
    as (HocG & Hcapn & Hocapn & Hnon & Henn & Hecapn & Hkan).
  assert (SZtl : tr_sizes_ok tl).
  { apply (gs_dsfut_sizes cx (dnext (dlive cx) (dxmx cx) s1) a (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q)
      (GSno cx s1 p q) (GSoc cx s1 p q) (drlq s1 (S q)) jb o ha ks tl
      Hmx0 HocG Hcapn Hocapn Hnon Henn Hecapn Hkan). unfold GSfut in HFUT. exact HFUT. }
  unfold GSfut, dsfut in HFUT. cbv zeta in HFUT.
  rewrite (proj1 (proj2 (gs_seen_begin_new (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q) x jb ha ks Hges Hidx))) in HFUT.
  cbn [fst snd] in HFUT. destruct HFUT as (tl2 & HLF & Htl).
  pose proof HBUD as ((Hmle & Hsp0b & Hcost & Hbb & Hmx) & HRMb & HCNTb).
  rewrite Htl in SZtl.
  unfold tr_sizes_ok in SZtl. pose proof (Forall_inv_tail (Forall_inv_tail SZtl)) as SZtl2.
  assert (HnH : (Z.of_nat (length (dlH cx s1 p)) + 1) * 8 = 8 * re_nheld e1 + 8) by (rewrite Hlen_eq; ring).
  assert (Hcost2 : 0 <= tr_cost MT tl2) by (apply gs_tr_cost_nonneg; [exact MTL | exact SZtl2]).
  assert (Hmf : 0 <= mo_free MT) by (apply (mo_free_nonneg MT MTL)).
  assert (Hmm : 0 <= mo_malloc MT (Z.of_nat (length x) + 1)) by (apply (mo_malloc_nonneg MT MTL); lia).
  assert (Hmm2 : 0 <= mo_malloc MT (8 * re_nheld e1 + 8)) by (apply (mo_malloc_nonneg MT MTL); lia).
  assert (CTm : forall n (t : dtrace), tr_cost MT (RelayRunT.RMalloc n :: t) = (mo_malloc MT n + mo_free MT) + tr_cost MT t)
    by reflexivity.
  assert (CTr : forall k n aa (t : dtrace),
    tr_cost MT (RelayRunT.RRealloc k n aa :: t) = (mo_malloc MT n + mo_free MT) + tr_cost MT t) by reflexivity.
  assert (MTm : forall n (t : dtrace), tr_max (RelayRunT.RMalloc n :: t) = Z.max n (tr_max t)) by reflexivity.
  assert (MTr : forall k n aa (t : dtrace), tr_max (RelayRunT.RRealloc k n aa :: t) = Z.max n (tr_max t)) by reflexivity.
  assert (Etra : (8 * re_nheld e1 + 8) - drain_b_c.ent_ka e1 +
    tr_peak (RelayRunT.RMalloc (Z.of_nat (length x) + 1) :: tl2) <= tr_peak tl).
  { pose proof Dka as Dka'. cbn [drain_b_c.ds_ka dvirt] in Dka'. rewrite Dka', Htl, <- HnH. cbn [app].
    pose proof (W_tr_peak.tr_peak_nonneg (RelayRunT.RMalloc (Z.of_nat (length x) + 1) :: tl2)) as P0.
    destruct (Z.eqb_spec (dlka cx s1 p) 0) as [Ek|Ek];
      [rewrite (W_tr_peak.tr_peak_malloc ((Z.of_nat (length (dlH cx s1 p)) + 1) * 8))
      |rewrite (W_tr_peak.tr_peak_realloc (dlka cx s1 p))]; lia. }
  assert (Etrc : tr_cost MT tl =
    (mo_malloc MT (8 * re_nheld e1 + 8) + mo_free MT)
    + ((mo_malloc MT (Z.of_nat (length x) + 1) + mo_free MT) + tr_cost MT tl2)).
  { rewrite Htl. destruct (dlka cx s1 p =? 0);
      repeat first [rewrite CTm | rewrite CTr]; rewrite HnH; reflexivity. }
  assert (HnMMAX : 8 * re_nheld e1 + 8 < MMAX).
  { eapply Z.le_lt_trans; [|exact Hmx]. rewrite Htl.
    destruct (dlka cx s1 p =? 0);
      repeat first [rewrite MTm | rewrite MTr]; rewrite HnH; apply Z.le_max_l. }
  assert (HbbN : blocks_bytes S1 + (8 * re_nheld e1 + 8) <= LIVE_MAX).
  { assert (Pk1 : 8 * re_nheld e1 + 8 <= tr_peak tl).
    { rewrite Htl, <- HnH. cbn [app].
      pose proof (W_tr_peak.tr_peak_nonneg (RelayRunT.RMalloc (Z.of_nat (length x) + 1) :: tl2)) as P0.
      destruct (dlka cx s1 p =? 0);
        [rewrite (W_tr_peak.tr_peak_malloc ((Z.of_nat (length (dlH cx s1 p)) + 1) * 8))
        |rewrite (W_tr_peak.tr_peak_realloc (dlka cx s1 p))]; lia. }
    lia. }
  assert (DBmook : mo_ok MT (dxS cx) (dcost MT cx)) by exact HMOK.
  assert (HmokN : mo_ok MT S1 (mo_malloc MT (8 * re_nheld e1 + 8) + mo_free MT)).
  { apply (mok_station MT (dxS cx) S1 (dcost MT cx) spent
      (mo_malloc MT (8 * re_nheld e1 + 8) + mo_free MT)).
    - exact MTL.
    - exact DBmook.
    - exact Hmle.
    - lia.
    - rewrite Etrc in Hcost. lia. }
  assert (HoldFP : re_hp e1 <> 0 -> In (re_hp e1, re_kh e1) (ablocks B (dxly cx) (dxS cx)) ->
          forall i, 0 <= i < req_size (re_kh e1) -> inFP (dFP cx) (re_hp e1 + i)).
  { intros Hnz Hin0 i Hi.
    destruct KHP as [(Hz & _)|(_ & _ & _ & Hk2 & _)]; [contradiction|].
    assert (HHae : In (re_hp e1, re_kh e1) (aentry_blks e1)).
    { unfold aentry_blks. apply in_or_app; right. apply in_or_app; left.
      rewrite (proj2 (Z.eqb_neq (re_hp e1) 0) Hnz). apply in_eq. }
    exact (ga_fp_x cx ly1 S1 Hp1 W1 m1 md1 e1 h1 _ out1 _ _ HAR1 HPERM HPERM0 HHae ltac:(lia) Hin0 i Hi). }
  destruct HJ as (_ & _ & (memS2 & HJi2 & HAG2) & _). rewrite !Z.add_0_r in HJi2.
  (* the room round at realloc #2: the engine's stack room, the room of seen_tr's first request (MT_rk charges it
     2) on top of the budget of the requests after it, and the live counts *)
  pose proof (aj_stack_room_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (- DRAIN_FRAME) (ms_regs ms1) HJi2
    ltac:(rewrite Usp1; lia) ltac:(rewrite Has, WS, WF; lia)) as HROOM.
  match type of Htl with _ = [?ev0; ?m0] ++ ?t0 =>
    assert (HRM1 : rp_RM RP S1 (Nat.add 2 (Nat.add (Z.to_nat (tr_cost MT_rk (m0 :: t0))) kr)))
      by (refine (gs_rm_take RP S1 [ev0] (m0 :: t0) kr 2 _ _);
          [destruct (dlka cx s1 p =? 0); exact (le_n 2%nat) | rewrite Htl in HRMb; exact HRMb]) end.
  pose proof (gs_cnt_call RP tl (ablocks B ly1 S1) HCNTb) as HCNT1.
  eapply (SRrG_bind SEGS R R_trans).
  { eapply (AREALLOCR W1 (ms_regs ms1) (ms_mem ms1) DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp (dxW cx)
      memS2 (dxmd cx) [] ly1 S1 Hp1 _ k1 (re_hp e1) (re_kh e1) (8 * re_nheld e1 + 8) (- DRAIN_FRAME) _ []
      (Nat.add (Z.to_nat (tr_cost MT_rk (RelayRunT.RMalloc (Z.of_nat (length x) + 1) :: tl2))) kr) HJi2).
    - destruct KHP as [(Hz & _)|(_ & Hin & _)]; [left; exact Hz | right; exact Hin].
    - exact P10v.
    - exact P11v.
    - lia.
    - exact HbbN.
    - exact HCNT1.
    - rewrite Usp1. unfold DRAIN_FRAME. ring.
    - vm_compute; reflexivity.
    - unfold DRAIN_FRAME; lia.
    - rewrite Has, WS, WF. lia.
    - exact HROOM.
    - exact P3v.
    - exact P4v.
    - exact P1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - pose proof HGSB as (HG1 & HG2 & _).
      assert (HD8 : 0 <= (rg_s RG + 4) / 8 <= rg_s RG + 4)
        by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
      apply (achain_chain_pre ly1 _ (dsp0 cx - DRAIN_FRAME) ((rg_s RG + 4) / 8) [] (ms_regs ms1)).
      + apply achain_low. unfold ASRC in *. lia.
      + rewrite Usp1, WF. lia.
      + unfold s0Z. rewrite P8, (eq_trans (EA 8%nat ltac:(lia)) R8). unfold w64.
        apply unsigned_lit_small. unfold ASRC in *. lia.
      + unfold raZ. rewrite P1. rewrite unsigned_lit_small by lia. lia.
    - exact (RO_ARx _ _ _ _ _ _ (proj1 HJi2)).
    - apply HA_call. exact HmokN.
    - (* the caller-context fact: the chain is cut, so the trace is the return address alone (HCTX_re2) *)
      unfold raZ. cbn [spine map]. rewrite P1. rewrite unsigned_lit_small by lia.
      match goal with |- In [?y] _ =>
        replace y with (BASE + AF_fr_drain + 0x7e8) by (try unfold A_dr_add; try unfold AF_fr_drain; ring) end.
      exact HCTX_re2.
    - exact HRM1.
    - exact HoldFP.
    - exact HmokN. }
  cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & res & -> & HJ2i & HPR2 & Hres10 & Hfr2 &
    Hres4096 & HpermZ & HpermN & Hcopy & Hkept2 & Hmle2 & HRM2 & Herr2 & Hpres2).
  pose proof (proj1 HJ2i) as HAR2.
  assert (Hres0 : res <> 0) by lia.
  assert (RQ2 : req_size (8 * re_nheld e1 + 8) = 8 * re_nheld e1 + 8)
    by (unfold req_size; destruct (Z.eqb_spec (8 * re_nheld e1 + 8) 0); lia).
  (* the live blocks after realloc #2: the entry's held array is the new block *)
  match type of HPERM with Permutation _ (_ :: aentry_blks _ ++ ?r) => pose (Rbl := r) end.
  pose (BUF := if re_cap e1 =? 0 then [] else [(re_buf e1, re_cap e1)]).
  pose (KEYS := map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e1)).
  pose (NEW := (res, 8 * re_nheld e1 + 8)).
  pose (TBL := (dxG cx, ATABLE)).
  assert (EA2 : aentry_blks (ga_entry e1 res (8 * re_nheld e1 + 8)) = BUF ++ NEW :: KEYS).
  { unfold ga_entry, aentry_blks, BUF, KEYS, NEW. cbn [re_cap re_buf re_hp re_kh re_keys].
    rewrite (proj2 (Z.eqb_neq res 0) Hres0). reflexivity. }
  assert (BASEP : Permutation (ablocks B ly2 S2) (NEW :: TBL :: (BUF ++ KEYS ++ Rbl))).
  { destruct (Z.eqb_spec (re_hp e1) 0) as [Hz | Hnz].
    - assert (EA1 : aentry_blks e1 = BUF ++ KEYS)
        by (unfold aentry_blks, BUF, KEYS; rewrite Hz; reflexivity).
      eapply Permutation_trans; [exact (HpermZ Hz)|]. apply perm_skip.
      eapply Permutation_trans; [exact HPERM|]. apply perm_skip.
      rewrite EA1, <- app_assoc. apply Permutation_refl.
    - assert (EA1 : aentry_blks e1 = BUF ++ (re_hp e1, re_kh e1) :: KEYS)
        by (unfold aentry_blks, BUF, KEYS; rewrite (proj2 (Z.eqb_neq (re_hp e1) 0) Hnz); reflexivity).
      destruct (HpermN Hnz) as (l1 & l2 & Ebl1 & Ebl2).
      eapply Permutation_trans; [exact Ebl2|]. apply perm_skip.
      apply (Permutation_cons_inv (a := (re_hp e1, re_kh e1))).
      eapply Permutation_trans; [apply Permutation_middle|].
      rewrite <- Ebl1.
      eapply Permutation_trans; [exact HPERM|].
      rewrite EA1, <- app_assoc.
      eapply Permutation_trans; [apply perm_skip; apply Permutation_sym, Permutation_middle|].
      apply perm_swap. }
  assert (PERM2 : Permutation (ablocks B ly2 S2)
    (TBL :: aentry_blks (ga_entry e1 res (8 * re_nheld e1 + 8)) ++ Rbl)).
  { eapply Permutation_trans; [exact BASEP|].
    eapply Permutation_trans; [apply perm_swap|]. apply perm_skip.
    rewrite EA2, <- app_assoc. change ((NEW :: KEYS) ++ Rbl) with (NEW :: (KEYS ++ Rbl)).
    apply Permutation_middle. }
  assert (HGin2 : In TBL (ablocks B ly2 S2))
    by (apply (Permutation_in _ (Permutation_sym BASEP)); right; left; reflexivity).
  assert (HNin2 : In NEW (ablocks B ly2 S2))
    by (apply (Permutation_in _ (Permutation_sym BASEP)); left; reflexivity).
  (* the table block is apart from the new block and from the old held array *)
  assert (DTN : zdisjoint (block_rng NEW) (block_rng TBL))
    by exact (ga_sep_head_x ly2 S2 Hp2 W2 mem2 md2 NEW (TBL :: BUF ++ KEYS ++ Rbl) TBL HAR2 BASEP (or_introl eq_refl)).
  assert (DTH : re_hp e1 <> 0 -> zdisjoint (block_rng TBL) (block_rng (re_hp e1, re_kh e1))).
  { intros Hnz. apply (ga_sep_head_x ly1 S1 Hp1 W1 m1 md1 TBL (aentry_blks e1 ++ Rbl) _ HAR1 HPERM).
    apply in_or_app; left. unfold aentry_blks. apply in_or_app; right. apply in_or_app; left.
    rewrite (proj2 (Z.eqb_neq (re_hp e1) 0) Hnz). apply in_eq. }
  assert (NOEXC : forall aa, dxG cx <= aa < dxG cx + req_size ATABLE ->
    ~ ((res <= aa < res + req_size (8 * re_nheld e1 + 8)) \/
       (re_hp e1 <> 0 /\ re_hp e1 <= aa < re_hp e1 + req_size (re_kh e1)))).
  { intros aa Haa [Hx | (Hnz & Hx)].
    - unfold zdisjoint, block_rng in DTN. unfold NEW, TBL in DTN. cbn [fst snd] in DTN.
      rewrite RQ2 in Hx. rewrite RQT in Haa. lia.
    - pose proof (DTH Hnz) as DD. unfold zdisjoint, block_rng, TBL in DD. cbn [fst snd] in DD.
      rewrite RQT in Haa, DD. lia. }
  assert (B2 : bv_unsigned (ew E 2) = dsp0 cx - DRAIN_FRAME)
    by (rewrite E2; apply unsigned_lit_small; rewrite WF; lia).
  jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W2) mem2) HPR2 [0; 1]%nat HS2.
  match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
    - eapply region_kept_stack_aj_xR; [exact Hkept2 | exact HJ2i | exact B2 | ..]; rewrite ?WS, ?WF, ?Has; lia.
    - apply (ga_kept_blk_x E ly1 S1 W1 (ms_mem ms1) W2 mem2 _ _ _ ly2 S2 Hp2 md2 22 0 56 40 52 _ (dxG cx) ATABLE
        (dxSA cx) Hkept2 HAR2 HGin2 U22 HGin1); rewrite ?RQT;
      [ unfold AENT, ATABLE in *; lia | unfold AENT, ATABLE in *; lia | lia | lia
      | cbv beta; intros aa Haa; apply NOEXC; rewrite RQT; exact Haa ]. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc E 48 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
  assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLDa : forall mm, (mm < 48)%nat -> ew Ea mm = ew E mm)
    by (intros mm Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
  assert (Ea52 : ew Ea 52 = w64 res).
  { rewrite HEa. replace 52%nat with (48 + 4)%nat by lia.
    rewrite (ew_havoc_new E 48 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0)) by (cbv; lia).
    unfold CLOB. cbn [map nth]. exact Hres10. }
  clear HEa.
  assert (B22a : bv_unsigned (ew Ea 22) = dxSA cx) by (rewrite OLDa by lia; exact U22).
  assert (UBxa : U Ea gaBx = SHADOW_OFF)
    by (unfold gaBx, U; cbn [sv_denot]; rewrite OLDa by lia; rewrite E21, Z.add_0_r;
        unfold w64; rewrite Z_to_bv_bv_unsigned; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (HJ2 : @ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
    (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly2 S2 Hp2 W2 mem2 md2 (k1 + 3)).
  { apply (ajournal_gx_pack_xR SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx) (dxly cx) (dxS cx) Hp
      (dxW cx) (dxmem cx) (dxmd cx) [] ly2 S2 Hp2 W2 mem2 md2 (k1 + 3) memS2);
      [lia | lia | rewrite !Z.add_0_r; exact HJ2i | exact HAG2 | intros aa Haa; lia]. }
  assert (SHOK2 : sh_ok SEGS gaBx ga_SH Ea (mrestrict (w_H W2) mem2)).
  { unfold sh_ok, ga_SH. constructor; [|constructor].
    apply (ga_shent_x Ea ly2 S2 Hp2 W2 mem2 md2 (dxG cx) ATABLE 22 (dxSA cx) 0 56 HAR2 HGin2 UBxa
      ltac:(unfold U; cbn [sv_denot]; rewrite OLDa by lia; rewrite E22, Z.add_0_r; unfold w64;
            rewrite Z_to_bv_bv_unsigned; apply unsigned_lit_small; unfold GA_HI in *; lia));
      rewrite ?RQT; unfold AENT, ATABLE in *; lia. }
  destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 HNin2)
    as (Hres16 & _ & Hresceil & Hresapp & Hrespres & _).
  rewrite RQ2 in Hresceil, Hresapp, Hrespres.
  assert (Hres64 : 0 <= res < 2 ^ 64) by lia.
  (* 0x838c4 beqz a0: realloc returned a block, not NULL *)
  psrr_branch_tok RUNR BRR HS SHOK2 gaBspan;
    rename Hc into BZ2;
    rewrite (ga_beqz_pos RG Ea 52 res Ea52 Hres64 Hres4096) in BZ2.
  { discriminate. }
  (* 0x838c8 .. 0x838d4: the shadow byte of &s->held is 0, then s->held = res *)
  paj_run_to_tok_xR RUNTOR HS HJ2 SHOK2 gaBspan A_dr_addb.
  { lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
      let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_x_cons; [intros aa Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros aa Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite B22a in Ha.
    left. split; [|lia]. right; left. split.
    - unfold dFP, dr_fp. exists (dxSA cx, dxSA cx + AENT). split; [left; reflexivity|].
      cbn [fst snd]. unfold AENT. lia.
    - exists (dxG cx), ATABLE. split; [exact HGin2|]. rewrite RQT. unfold AENT, ATABLE in *. lia. }
  rename HFr into HFr2, HG0 into HGr2. clear HF.
  lazymatch goal with |- SRrG _ R _ (mkCfg ?mm ?mo) _ => rename mm into msf; set (matf := mo) in * end.
  pmkst HS.
  prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4.
  prreg HS (8%bv : bv 5) F8. prreg HS (9%bv : bv 5) F9. prreg HS (18%bv : bv 5) F18.
  prreg HS (21%bv : bv 5) F21. prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23.
  prreg HS (24%bv : bv 5) F24. prreg HS (25%bv : bv 5) F25. prreg HS (27%bv : bv 5) F27.
  (* s3 keeps the shadow address of &s->held it entered with *)
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H Ev ss ms 19%bv HS) as F19;
    let e := eval vm_compute in (sr_get (ss_regs ss) 19%bv) in change (sr_get (ss_regs ss) 19%bv) with e in F19;
    set (Ef := Ev) in HS, F19 end.
  cbn [ms_regs restrict mkst] in F19.
  assert (UF : forall mm, (mm < 512)%nat -> ew Ef mm = ew Ea mm)
    by (intros mm Hm; subst Ef; rewrite ?ew_ewset_other by lia; reflexivity).
  assert (EF : forall mm, (mm < 48)%nat -> ew Ef mm = ew E mm)
    by (intros mm Hm; rewrite UF by lia; exact (OLDa mm Hm)).
  assert (Ef21 : ew Ef 21 = w64 SHADOW_OFF) by (rewrite EF by lia; exact E21).
  assert (Ef22 : ew Ef 22 = w64 (dxSA cx)) by (rewrite EF by lia; exact E22).
  assert (U21f : U Ef (SOff 21 0) = SHADOW_OFF)
    by (apply (U_atom Ef 21 _ Ef21); unfold SHADOW_OFF; lia).
  assert (HD40f : 0 <= (dxSA cx + 40) / 8 <= dxSA cx + 40)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (US40f : U Ef (SAlu ALU_SRL (SOff 22 40) (SLit 3)) = (dxSA cx + 40) / 8)
    by (apply (ga_den_srl3 Ef 22 (dxSA cx) 40 Ef22); unfold GA_HI in *; lia).
  (* every byte outside the two cells this arm writes keeps its view, across both runs and the call *)
  assert (KR1 : forall aa, 0 <= aa < 2 ^ 64 -> ~ (dxSA cx + 40 <= aa < dxSA cx + 52) ->
    aview SEGS (w_H W1) (ms_mem ms1) aa = aview SEGS (w_H W1) m1 aa).
  { intros aa Ha Hno. apply (aview_kept_out E _ (w_H W1) m1 (ms_mem ms1) HFr1 aa Ha). apply ga_not_wrange.
    lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end.
    repeat constructor; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?U22; lia. }
  assert (KR2 : forall aa, 0 <= aa < 2 ^ 64 -> ~ (dxSA cx + 40 <= aa < dxSA cx + 52) ->
    aview SEGS (w_H W2) (ms_mem msf) aa = aview SEGS (w_H W2) mem2 aa).
  { intros aa Ha Hno. apply (aview_kept_out Ea _ (w_H W2) mem2 (ms_mem msf) HFr2 aa Ha). apply ga_not_wrange.
    lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end.
    repeat constructor; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?B22a; lia. }
  pose proof Hkept2 as (KC1 & KC2 & KC3 & KC4 & KC5 & KC6).
  assert (FK : forall aa, dsp0 cx - DRAIN_FRAME <= aa < dsp0 cx -> abyte_kept W1 m1 W2 (ms_mem msf) aa).
  { intros aa Haa.
    assert (Hr : 0 <= aa < 2 ^ 64) by (rewrite WF in *; lia).
    assert (Hno : ~ (dxSA cx + 40 <= aa < dxSA cx + 52))
      by (unfold GA_HI in *; rewrite WF in *; lia).
    split.
    - rewrite (KR2 aa Hr Hno), (KC1 aa ltac:(rewrite WF in *; lia) ltac:(rewrite WF, Has in *; lia)).
      exact (KR1 aa Hr Hno).
    - intros Hw. apply (ga_writable_kept (w_H W1) (w_H W2) m1 (ms_mem msf) aa); [|exact Hw].
      intros Hpx. apply (ga_apresent_grows _ _ _ _ HGr2).
      apply (KC5 aa ltac:(rewrite WF in *; lia) ltac:(rewrite WF, Has in *; lia)).
      exact (ga_apresent_grows _ _ _ _ HGr1 Hpx). }
  (* rom_view at the cut: GAR_x carries it on its own and inside GARB_x's DMEM_x *)
  assert (ROM2 : rom_view SEGS W2 (ms_mem msf)).
  { pose proof (ajournal_gx_AR_xR SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
      (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly2 S2 Hp2 W2 (ms_mem msf) matf (k1 + 3) HJ2) as HAR2f.
    assert (HKI : forall xx, in_img SEGS xx -> ~ Exists (in_zr xx) (as_owned_static B) ->
      ~ (as_errno B <= xx < as_errno B + 4) ->
      aview SEGS (w_H W2) (ms_mem msf) xx = aview SEGS (w_H W1) m1 xx).
    { intros xx Hi Hno Hne.
      assert (Hr : 0 <= xx < 2 ^ 64) by (pose proof (pa_segs_low xx Hi); unfold kLowMemEnd in *; lia).
      assert (Hno2 : ~ (dxSA cx + 40 <= xx < dxSA cx + 52)).
      { intros Hx. exact (blk_img_x _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 _ _ xx HAR1 HGin1
          ltac:(rewrite RQT; unfold AENT, ATABLE in *; lia) Hi). }
      rewrite (KR2 xx Hr Hno2), (KC3 xx Hi Hno Hne). exact (KR1 xx Hr Hno2). }
    intros xx Hx. destruct (HROMO xx Hx) as (_ & Hpin & Hne & _).
    destruct (Exists_dec (in_zr xx) (as_owned_static B) (ga_in_zr_dec RG xx)) as [Hown | Hno].
    - exact (rom_pinned_view_x SEGS B ARx LAWS ly2 S2 Hp2 W2 (ms_mem msf) matf xx HAR2f (Hpin Hown)).
    - assert (Hi : in_img SEGS xx)
        by (destruct Hx as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
      rewrite (HKI xx Hi Hno Hne). exact (HROM xx Hx). }
  (* the GAR_x cut *)
  apply (ADDB cx Hp kr s1 D p q W2 _ HB); [|exact HN].
  unfold GAR_xR.
  exists (ms_regs msf), ly2, S2, Hp2, (ms_mem msf), matf, (k1 + 3),
    (ga_entry e1 res (8 * re_nheld e1 + 8)), h1, out1, ev1, LB1,
    (spent + (mo_malloc MT (8 * re_nheld e1 + 8) + mo_free MT)), a,
    (RelayRunT.RMalloc (Z.of_nat (length x) + 1) :: tl2), jj.
  split; [reflexivity|].
  split.
  { apply (ga_dregs_kept RG HGSB cx regs1 (ms_regs msf) W1 m1 W2 (ms_mem msf) HRL);
    [ rewrite F2, EF by lia; exact (EA 2%nat ltac:(lia))
    | rewrite F3, EF by lia; exact (EA 3%nat ltac:(lia))
    | rewrite F4, EF by lia; exact (EA 4%nat ltac:(lia))
    | rewrite F22, EF by lia; exact (EA 22%nat ltac:(lia))
    | rewrite F27, EF by lia; exact (EA 27%nat ltac:(lia))
    | rewrite F18, EF by lia; exact (EA 18%nat ltac:(lia))
    | rewrite F9, EF by lia; exact (EA 9%nat ltac:(lia))
    | rewrite F8, EF by lia; exact (EA 8%nat ltac:(lia))
    | rewrite F21, EF by lia; exact (EA 21%nat ltac:(lia))
    | exact FK ]. }
  split; [cbn [ga_entry re_buf]; rewrite F23, EF by lia; exact (eq_trans (EA 23%nat ltac:(lia)) R23)|].
  split; [cbn [ga_entry re_buf]; rewrite F24, EF by lia; exact (eq_trans (EA 24%nat ltac:(lia)) R24)|].
  split; [cbn [ga_entry re_buf]; rewrite F25, EF by lia; exact (eq_trans (EA 25%nat ltac:(lia)) R25)|].
  split.
  { rewrite F19. apply ga_den_of_U.
    rewrite (ga_U_add RG) by (rewrite US40f, U21f; unfold SHADOW_OFF; unfold GA_HI in *; lia).
    rewrite US40f, U21f. reflexivity. }
  split; [apply (akept_vm W1 m1); [intros y Hy; apply FK; cbn in Hy; rewrite WF in *; lia | exact V72]|].
  split; [cbn [ga_entry re_hp]; exact Hres0|].
  split; [cbn [ga_entry re_kh]; reflexivity|].
  split.
  { cbn [ga_entry re_hp re_kh]. intros blc lyq ownq i Hin Hi.
    apply (ga_awr_blk_x cx ly2 S2 Hp2 W2 mem2 md2 (ga_entry e1 res (8 * re_nheld e1 + 8)) h1 _ out1
             res (8 * re_nheld e1 + 8) blc lyq ownq (res + i) HAR2 PERM2 HPERM0);
      [ rewrite EA2; apply in_or_app; right; apply in_eq | lia | exact Hin | rewrite RQ2 in Hi |- *; lia ]. }
  split; [exact ROM2|].
  split; [exact Hges|]. split; [exact Hjj|]. split; [exact Hidx|]. split; [exact HGSF|].
  (* GARB_x: gb_garb_x, with the entry's two cells read off the final regions and the room round's room and
     counts after the call *)
  split.
  { pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as REF. cbn [ms_mem restrict] in REF.
    assert (B22f : bv_unsigned (ew Ef 22) = dxSA cx) by (rewrite (UF 22%nat ltac:(lia)); exact B22a).
    assert (VF40 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (dxSA cx + 40) (N.to_nat 8) res).
    { eapply (field_of_region Ef _ 22 (dxSA cx)); [exact REF | exact B22f | ga_in_x | | |].
      - cbn [sv_denot]. rewrite (UF 52%nat ltac:(lia)), Ea52, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
        reflexivity.
      - change (8 * Z.of_N 8) with 64. clear - Hres64. lia.
      - apply (proj1 (Z.leb_le _ _)). reflexivity. }
    assert (VF48 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (dxSA cx + 48) (N.to_nat 4) (re_nheld e1)).
    { eapply (field_of_region Ef _ 22 (dxSA cx)); [exact REF | exact B22f | ga_in_x | | |].
      - cbn [sv_denot]. rewrite (EF 10%nat ltac:(lia)), E10, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
        reflexivity.
      - change (8 * Z.of_N 4) with 32. clear - Hnh26. lia.
      - apply (proj1 (Z.leb_le _ _)). reflexivity. }
    change (N.to_nat 8) with 8%nat in VF40. change (N.to_nat 4) with 4%nat in VF48.
    assert (HmxT : tr_max (RelayRunT.RMalloc (Z.of_nat (length x) + 1) :: tl2) <= tr_max tl).
    { rewrite Htl. destruct (dlka cx s1 p =? 0); repeat first [rewrite MTm | rewrite MTr]; apply Z.le_max_r. }
    (* the counts after realloc #2: a malloc when s->held is NULL, else the realloc of the old array *)
    assert (HCNT2 : cnt_ok_pk RP
      (fun P => (Z.to_nat (tr_peakP P (RelayRunT.RMalloc (Z.of_nat (length x) + 1) :: tl2)) + 2)%nat)
      (ablocks B ly2 S2)).
    { pose proof Dka as Dka2. cbn [drain_b_c.ds_ka dvirt] in Dka2.
      rewrite Htl in HCNTb. cbn [app] in HCNTb.
      destruct (Z.eqb_spec (re_hp e1) 0) as [Hz | Hnz].
      - assert (Ek : dlka cx s1 p = 0)
          by (rewrite <- Dka2; unfold drain_b_c.ent_ka; rewrite (proj2 (Z.eqb_eq _ _) Hz); reflexivity).
        rewrite Ek in HCNTb.
        refine (gs_cnt_malloc RP ((Z.of_nat (length (dlH cx s1 p)) + 1) * 8) _ (ablocks B ly1 S1) _ res _ HCNTb).
        rewrite HnH. exact (HpermZ Hz).
      - assert (Hk8 : 8 <= re_kh e1)
          by (destruct KHP as [(Hz & _)|(_ & _ & _ & Hk8 & _)]; [contradiction | exact Hk8]).
        assert (Ek : dlka cx s1 p = re_kh e1)
          by (rewrite <- Dka2; unfold drain_b_c.ent_ka; rewrite (proj2 (Z.eqb_neq _ _) Hnz); reflexivity).
        assert (Ek0 : (re_kh e1 =? 0) = false) by (apply Z.eqb_neq; lia).
        rewrite Ek, Ek0 in HCNTb.
        destruct (HpermN Hnz) as (l1 & l2 & Ebl1 & Ebl2).
        rewrite Ebl1 in HCNTb.
        refine (gs_cnt_realloc RP (re_kh e1) ((Z.of_nat (length (dlH cx s1 p)) + 1) * 8) ha _ l1 l2 _ (re_hp e1) res
          _ HCNTb).
        rewrite HnH. exact Ebl2. }
    exact (gb_garb_xR cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl (ms_mem ms1) ly2 S2 Hp2
      W2 mem2 (ms_mem msf) matf res x tl2 HB HCORE Hges Hidx Etra Etrc HmxT HJ2 Hfr2 Hres4096 BASEP Hcopy Hkept2
      Herr2 Hpres2 HGr1 HGr2 KR1 KR2 Hmle2 VF40 VF48 ROM2 FK HRM2 HCNT2). }
  unfold GARfut. exists tl2. do 4 eexists. split; [exact HLF | reflexivity].
Qed.
End wR.


Lemma region_kept_stack_aj_x : forall E lyc Sc (W : world SEGS) memc (W2 : world SEGS) mem2 slo shi (Er : Z -> Prop)
    n lo hi wlo whi cs sp0 sp STK FP ly S Hp W0 mem md own ly2 S2 Hp2 md2 k,
  acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi Er ->
  ajournal_x SEGS B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k ->
  bv_unsigned (ew E n) = sp -> shi <= sp + lo -> sp0 - STK <= sp + lo -> sp + hi <= sp0 -> lo <= wlo -> whi <= hi ->
  region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof. eapply (region_kept_stack_aj_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.


(* ---- W_drain_tr.v:408 gs_cut_facts, :444 gs_cut_dnext_signs, :516 gs_dgs_dnext_signs over LCORE_x ---- *)
Lemma gs_cut_facts_x : forall cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl,
  LCORE_x B PST ARx MT RP MMAX RG cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1
    spent tl ->
  nozero (drain_b_c.ds_u s1) /\ 0 <= drain_b_c.ds_cap s1 /\ 0 <= dxmx cx /\ 0 <= no /\ 0 <= oc /\ 0 <= ka /\
  0 <= drain_b_c.ds_en (dnext (dlive cx) (dxmx cx) s1) /\ 0 <= drain_b_c.ds_ecap (dnext (dlive cx) (dxmx cx) s1).
Proof. eapply (gs_cut_facts_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.


Lemma gs_cut_dnext_signs_x : forall cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1
  spent tl p,
  0 <= dxmx cx -> dbound s1 p -> no = dlno s1 p -> oc = dloc cx s1 p -> (0 <= ka -> 0 <= dlka cx s1 p) ->
  LCORE_x B PST ARx MT RP MMAX RG cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1
    spent tl ->
  0 <= oc /\
  0 <= drain_b_c.ds_cap (dnext (dlive cx) (dxmx cx) s1) /\ 0 <= drain_b_c.ds_ocap (dnext (dlive cx) (dxmx cx) s1) /\
  0 <= drain_b_c.ds_no (dnext (dlive cx) (dxmx cx) s1) /\ 0 <= drain_b_c.ds_en (dnext (dlive cx) (dxmx cx) s1) /\
  0 <= drain_b_c.ds_ecap (dnext (dlive cx) (dxmx cx) s1) /\ 0 <= drain_b_c.ds_ka (dnext (dlive cx) (dxmx cx) s1).
Proof. eapply (gs_cut_dnext_signs_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.


Lemma gs_dgs_dnext_signs_x : forall cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1
  spent tl p q,
  dbound s1 p -> (p <= q < length (dW s1))%nat -> nth_error (dW s1) q = Some 0 ->
  (forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) -> dskp s1 p = false -> (q - p <= LINE_LIMIT)%nat ->
  no = dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1 ->
  oc = send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
         (Z.of_nat (length (dline s1 p q)) + 1) ->
  (0 <= ka -> 0 <= dlka cx s1 p) ->
  LCORE_x B PST ARx MT RP MMAX RG cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1
    spent tl ->
  0 <= oc /\
  0 <= drain_b_c.ds_cap (dnext (dlive cx) (dxmx cx) s1) /\ 0 <= drain_b_c.ds_ocap (dnext (dlive cx) (dxmx cx) s1) /\
  0 <= drain_b_c.ds_no (dnext (dlive cx) (dxmx cx) s1) /\ 0 <= drain_b_c.ds_en (dnext (dlive cx) (dxmx cx) s1) /\
  0 <= drain_b_c.ds_ecap (dnext (dlive cx) (dxmx cx) s1) /\ 0 <= drain_b_c.ds_ka (dnext (dlive cx) (dxmx cx) s1).
Proof. eapply (gs_dgs_dnext_signs_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.


(* ---- (2) the line loop's core across an END whose key is not held (ga_lcore_end) ---- *)
Lemma ga_lcore_end_x : forall cx Hp kr s1 D sent kl kl' l x H ka no oc nk nk' sk
  ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl,
LCORE_x B PST ARx MT RP MMAX RG cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1
  spent tl ->
gesture l = Some (GEnd, x) -> index_of x H = None -> nk' <= nk -> kl' = kl ++ [l] ->
LCORE_x B PST ARx MT RP MMAX RG cx Hp kr s1 D sent kl' H ka no oc nk' sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1
  spent tl.
Proof. eapply (ga_lcore_end_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.


(* ---- the line loop's core across a memory that keeps every byte's view (ga_lcore_mem) ---- *)
Lemma ga_lcore_mem_x : forall cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 (W1 : world SEGS) m1 md1 k1
  e1 h1 out1 ev1 LB1 spent tl m' md',
LCORE_x B PST ARx MT RP MMAX RG cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1
  spent tl ->
ARx ly1 S1 Hp1 W1 m1 md1 ->
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m' md' k1 ->
(forall x, 0 <= x < 2 ^ 64 -> aview SEGS (w_H W1) m' x = aview SEGS (w_H W1) m1 x) ->
(forall x, apresent (w_H W1) m1 x -> apresent (w_H W1) m' x) ->
alloc_ceiling + 8 <= dsp0 cx - DRAIN_FRAME -> dsp0 cx <= 2 ^ 47 ->
4096 <= dxSA cx -> dxSA cx + AENT <= alloc_ceiling ->
rg_s RG <= dHA RG cx -> dHA RG cx + ASRC <= rg_s RG + 4 * ASRC ->
LCORE_x B PST ARx MT RP MMAX RG cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m' md' k1 e1 h1 out1 ev1 LB1
  spent tl.
Proof. eapply (ga_lcore_mem_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.


(* ---- (5) GARB_x, the cut's core from the post of realloc #2 and the store s->held = res (gb_garb), with
   dbud_x's room and counts after the call as two more premises ---- *)
Lemma gb_garb_x : forall cx Hp kr s1 D p q ly1 S1 Hp1 (W1 : world SEGS) m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl
  mR1 ly2 S2 Hp2 (W2 : world SEGS) mem2 m2 md2 res xx tl2,
DBASE_x B ARx MT RP MMAX RG cx Hp kr ->
GSB_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl ->
gesture (dline s1 p q) = Some (GBegin, xx) -> index_of xx (dlH cx s1 p) = None ->
(8 * re_nheld e1 + 8) - drain_b_c.ent_ka e1 + tr_peak (RelayRunT.RMalloc (Z.of_nat (length xx) + 1) :: tl2) <=
  tr_peak tl ->
tr_cost MT tl = mo_malloc MT (8 * re_nheld e1 + 8) + mo_free MT +
  (mo_malloc MT (Z.of_nat (length xx) + 1) + mo_free MT + tr_cost MT tl2) ->
tr_max (RelayRunT.RMalloc (Z.of_nat (length xx) + 1) :: tl2) <= tr_max tl ->
@ajournal_gx_x _ SK SEGS B PST ARx (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly2 S2 Hp2 W2 m2 md2 (k1 + 3) ->
frames S2 = frames S1 -> 4096 <= res ->
Permutation (ablocks B ly2 S2)
  ((res, 8 * re_nheld e1 + 8) :: (dxG cx, ATABLE) ::
   (if re_cap e1 =? 0 then [] else [(re_buf e1, re_cap e1)]) ++
   map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e1) ++
   asrc_blks h1 ++ aout_blks (GSoc cx s1 p q) out1 ++ dxrest cx) ->
(re_hp e1 <> 0 -> forall i, 0 <= i < Z.min (re_kh e1) (8 * re_nheld e1 + 8) ->
  aview SEGS (w_H W2) mem2 (res + i) = aview SEGS (w_H W1) mR1 (re_hp e1 + i)) ->
acall_kept SEGS B ly1 S1 W1 mR1 W2 mem2 (dsp0 cx + - DRAIN_FRAME - ASTACK) (dsp0 cx + - DRAIN_FRAME)
  (fun a => res <= a < res + req_size (8 * re_nheld e1 + 8) \/
            re_hp e1 <> 0 /\ re_hp e1 <= a < re_hp e1 + req_size (re_kh e1)) ->
(forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W1) mR1 (as_errno B + i)) ->
(forall a, in_img SEGS a -> ~ aowned B ly1 S1 a -> ~ aowned B ly2 S2 a -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (res <= a < res + req_size (8 * re_nheld e1 + 8) \/
     re_hp e1 <> 0 /\ re_hp e1 <= a < re_hp e1 + req_size (re_kh e1)) ->
  apresent (w_H W1) mR1 a -> apresent (w_H W2) mem2 a) ->
mem_grows (mrestrict (w_H W1) m1) (mrestrict (w_H W1) mR1) ->
mem_grows (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) m2) ->
(forall aa, 0 <= aa < 2 ^ 64 -> ~ (dxSA cx + 40 <= aa < dxSA cx + 52) ->
  aview SEGS (w_H W1) mR1 aa = aview SEGS (w_H W1) m1 aa) ->
(forall aa, 0 <= aa < 2 ^ 64 -> ~ (dxSA cx + 40 <= aa < dxSA cx + 52) ->
  aview SEGS (w_H W2) m2 aa = aview SEGS (w_H W2) mem2 aa) ->
mo_le MT S1 S2 (mo_malloc MT (8 * re_nheld e1 + 8) + mo_free MT) ->
val_mem SEGS (arm W2 m2) (dxSA cx + 40) 8 res ->
val_mem SEGS (arm W2 m2) (dxSA cx + 48) 4 (re_nheld e1) ->
rom_view SEGS W2 m2 ->
(forall aa, dsp0 cx - DRAIN_FRAME <= aa < dsp0 cx -> abyte_kept W1 m1 W2 m2 aa) ->
rp_RM RP S2 (Z.to_nat (tr_cost MT_rk (RelayRunT.RMalloc (Z.of_nat (length xx) + 1) :: tl2)) + kr) ->
cnt_ok_pk RP (fun P => (Z.to_nat (tr_peakP P (RelayRunT.RMalloc (Z.of_nat (length xx) + 1) :: tl2)) + 2)%nat)
  (ablocks B ly2 S2) ->
GARB_x B PST ARx MT RP MMAX RG cx Hp kr s1 D p q ly2 S2 Hp2 W2 m2 md2 (k1 + 3) (ga_entry e1 res (8 * re_nheld e1 + 8))
  h1 out1 ev1 LB1 (spent + (mo_malloc MT (8 * re_nheld e1 + 8) + mo_free MT))
  (RelayRunT.RMalloc (Z.of_nat (length xx) + 1) :: tl2).
Proof. eapply (gb_garb_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | assumption]. Qed.


(* ---- (6) GA (0x8389c) -> DLN (S q) over ARx, through GAR (0x838d8) ---- *)
Theorem gs_adda_x : gs_addb_stmt_x B PST ARx MT RP MMAX RG -> gs_add_stmt_x B PST ARx MT RP MMAX RG.
Proof. eapply (gs_adda_xR (@wle SEGS)); first [exact (wle_refl SEGS) | exact (wle_trans SEGS) | exact (fun W W' (h : @wle SEGS W W') => h) | (apply afree_cf_rule_c_xR_of_x; assumption) | (apply arealloc_cf_rule_c_xR_of_x; assumption) | (intros; exact I) | assumption]. Qed.

End cx.
End bx.
End ax.
