(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the two seeds of record's ASan+UBSan walk (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan), after A's spa_seedA / spa_meet_seed (lib/A/Prog/sup_pin_accept_s4.v, a working branch
   3cc8391594b) and spa_shok (sup_pin_accept_s1.v), at B's frame (32 bytes: ra, s0, s1, s2) and registers (s1 = the
   slot, s2 = the shadow base): the entry state (the frame the prologue writes, the shadow-base GOT word and cell,
   g_rec.ncalls) and the state where record()'s two arms meet (0x8a7ac). The GOT word's and the cell's values are
   AR's constant cells (AR_const_law) at the record's addresses (a Theorem Labs lane's CmdRecCells.v cmd_cf_got / cmd_cf_cell, from
   CmdBSyms and cmd_val_objs); g_rec's and the slot's write windows are writable by prog_rw (CmdRecCells.v
   PROG_WRITABLE); the slot's shadow entry is CmdRecCells.v cmd_cf_grec / CmdRecBase.v cmd_addressable_chk. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_aux.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdChk CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecBase CmdRecCells CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import rec_calls_free_c record_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the environments of the two seeds: the registers at the point, then the extra atoms *)
Definition rcb_EA (regs : bvmap 5 word) (n : Z) : env := Eimg (Ereg regs (rcb_extraA n)).
Definition rcb_EM (regsc regs : bvmap 5 word) (c : Z) : env := Eimg (Ereg regsc (rcb_extra regs c)).
Section e.
Variable B : asyms.
#[local] Notation LAWS := (AR_laws_ok SEGS B).
Hypothesis HB : CmdBSyms B.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis PRW : prog_rw SEGS B.

Lemma rcb_grec_val : VAL (A_OBJ 44) = A_G_REC.
Proof. rewrite (VOBJS 44%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

Lemma rcb_spill_val : VAL (A_OBJ 53) = A_REC_SPILL.
Proof. rewrite (VOBJS 53%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

(* the slot's 56 bytes are addressable: inside g_rec (CmdRecCells.v cmd_cf_grec) or record.spill (the record's
   checks, by computation) *)
Lemma rcb_slot_addressable : forall ly S (W : world SEGS) mem md c, AR SEGS B ly S W mem md -> rcb_slot_ok c ->
range_addressable (rdW W mem) SHADOW_OFF c CALL_SIZE.
Proof.
intros ly S W mem md c HAR Hc. destruct Hc as [(H1 & H2 & _) | ->].
- intros x Hx. apply (cmd_cf_grec SEGS B LAWS HB ly S W mem md HAR).
  unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE in *. lia.
- exact (cmd_addressable_chk SEGS B LAWS HB ly S W mem md A_REC_SPILL CALL_SIZE HAR ltac:(vm_compute; reflexivity)).
Qed.

(* the shadow entry of the slot, at any AR state of an environment whose atoms 32 and 33 are SB and the slot *)
Lemma rcb_shok : forall ly S (W : world SEGS) mem md E c, AR SEGS B ly S W mem md -> rcb_slot_ok c ->
ew E SA_SB = Z_to_bv 64 SB -> ew E SA_C = Z_to_bv 64 c -> sh_ok SEGS rcb_Bx rcb_SH E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E c HAR Hc ESB EC.
destruct (rcb_slot_bounds c Hc) as (Hcb & _ & Hce).
assert (Hcr : 0x5e32d0 <= c /\ c + 56 <= 0x5e3798)
  by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL, CALL_SIZE, SC_SIZE in Hcb, Hce; lia).
unfold sh_ok, rcb_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E rcb_Bx SA_C c CALL_SIZE c 0 CALL_SIZE).
- exact (rcb_slot_addressable ly S W mem md c HAR Hc).
- unfold rcb_Bx. rewrite (U_atom E SA_SB SB ESB) by (unfold SB; lia). reflexivity.
- apply (U_atom E SA_C c EC). lia.
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold CALL_SIZE, SHADOW_OFF in *. lia.
Qed.

(* the seed of the entry segment: the frame the prologue will write, the GOT word of the shadow cell, that cell,
   and g_rec.ncalls *)
Lemma rcb_seedA : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md n,
AR SEGS B ly S W mem md ->
astk_ok RECORD_STK ly (spZ regs) ->
(forall a, spZ regs - RECORD_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
0 <= n <= 16 ->
aval_mem (rdW W mem) (A_G_REC + OFF_NCALLS) 4 n ->
st_ok_pi SEGS VAL (rcb_EA regs n) ss_rcbA
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + RCB_E)) mem (seg_rom SEGS)))
/\ sh_ok SEGS rcb_BxA [] (rcb_EA regs n) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md n HAR Hstk Hpres Hn HNC.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : RECORD_STK = 16560) by (vm_compute; reflexivity).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (cmd_cf_got B HB VOBJS), (cmd_cf_cell B HB VOBJS) in Kgot. rewrite (cmd_cf_cell B HB VOBJS) in Kcell.
pose proof (pa_obj_img 0%nat ltac:(lia)) as Hgot_r. pose proof (pa_obj_img 12%nat ltac:(lia)) as Hcell_r.
set (E := rcb_EA regs n).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : bv_unsigned (ew E 2) = spZ regs).
{ subst E. unfold rcb_EA. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (E32 : ew E 32 = Z_to_bv 64 SB).
{ subst E. unfold rcb_EA. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
assert (E33 : ew E 33 = Z_to_bv 64 n).
{ subst E. unfold rcb_EA. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). }
assert (EG : ew E (A_OBJ 44) = Z_to_bv 64 A_G_REC).
{ rewrite (img_env_atomP E (A_OBJ 44) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), rcb_grec_val. reflexivity. }
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (exact (img_env_atomP E (A_OBJ 0) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (exact (img_env_atomP E (A_OBJ 12) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
split; [|unfold sh_ok; apply Forall_nil].
unfold ss_rcbA. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. unfold rcb_EA. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold rcb_rsA, stack_region, got_regionP, bcell_regionP, rcb_ncalls.
  repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite E2. unfold RCB_FRAME. split; [lia|]. split; [lia|]. split.
    { intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia. }
    constructor.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); pose proof (pa_val_range (A_OBJ 12)); lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold SB; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
  + rewrite (VB (A_OBJ 44) A_G_REC EG) by (unfold A_G_REC; lia).
    split; [unfold A_G_REC, OFF_NCALLS; lia|]. split; [unfold A_G_REC, OFF_NCALLS; lia|].
    split.
    { intros o Ho. apply (CmdRecCells.PROG_WRITABLE SEGS B LAWS HB PRW). apply rcb_PG_grec.
      unfold A_G_REC, REC_SIZE, OFF_NCALLS in *. lia. }
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ A_G_REC OFF_NCALLS 4 (SOff 33 0) n);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia |].
    exact (val_mem_view SEGS (w_H W) mem (A_G_REC + OFF_NCALLS) 4%nat n HNC).
- apply pairwise_disjoint_of_extents.
  unfold rcb_rsA, stack_region, got_regionP, bcell_regionP, rcb_ncalls, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
  rewrite (VB (A_OBJ 44) A_G_REC EG) by (unfold A_G_REC; lia).
  cbn [base_val]. rewrite E2.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  rewrite (VOBJS 0%nat ltac:(vm_compute; lia)), (VOBJS 12%nat ltac:(vm_compute; lia)).
  cbn [nth cmd_objs]. unfold RCB_FRAME, A_G_REC, OFF_NCALLS in *.
  rewrite WS in Hslo. repeat split; lia.
- split; [|split; exact I].
  cbn [rcb_factsA f_atoms atoms_ok]. unfold afact_ok, SA_SB, SA_N. cbn [af_lo af_hi af_al2].
  rewrite E2, E32, E33, EG, !unsigned_lit_small by (unfold SB, A_G_REC; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, A_G_REC.
  rewrite WS in Hslo.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
Qed.

(* the state where record()'s two arms meet (0x8a7ac): the slot c is chosen, the frame holds the entry's ra, s0, s1,
   s2, and nothing of the slot has been written yet *)
Lemma rcb_meet_seed : forall ly S (W : world SEGS) mem md (regs regs1 : bvmap 5 word) c sp0,
AR SEGS B ly S W mem md ->
2 ^ 46 <= sp0 - RCB_FRAME -> sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 -> rcb_slot_ok c ->
spZ regs1 = sp0 - RCB_FRAME ->
getr regs1 9 = w64 c -> getr regs1 18 = w64 SB ->
(forall j r, nth_error rcb_saved j = Some r ->
  val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))) ->
st_ok_pi SEGS VAL (rcb_EM regs1 regs c) ss_meet
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + RCB_MEET)) mem (seg_rom SEGS)))
/\ sh_ok SEGS rcb_Bx rcb_SH (rcb_EM regs1 regs c) (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md regs regs1 c sp0 HAR Hsp Hsp47 Hsp16 Hc Hsp1 R9 R18 HFR.
destruct (rcb_slot_bounds c Hc) as (Hcb & Hc8 & Hce).
assert (Hcr : 0x5e32d0 <= c <= 0x5e3760 /\ c + 56 <= 0x5e3798)
  by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL, CALL_SIZE, SC_SIZE in Hcb, Hce; lia).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := rcb_EM regs1 regs c).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs1 r).
{ intros nn r Hnn. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5.
  change (bv_modulus 5) with 32 in Hr5. unfold rcb_EM.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hnn. }
assert (EX : forall j, (j < 6)%nat -> ew E (32 + j) = nth j (rcb_extra regs c) (Z_to_bv 64 0)).
{ intros j Hj. subst E. unfold rcb_EM. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (ESB : ew E 32 = Z_to_bv 64 SB) by (exact (EX 0%nat ltac:(lia))).
assert (EC : ew E 33 = Z_to_bv 64 c) by (exact (EX 1%nat ltac:(lia))).
assert (Usp : bv_unsigned (ew E 2) = sp0 - RCB_FRAME) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp1).
assert (UC : bv_unsigned (ew E 33) = c) by (rewrite EC; apply unsigned_lit_small; lia).
assert (USB : bv_unsigned (ew E 32) = SB) by (rewrite ESB; apply unsigned_lit_small; unfold SB; lia).
split; [|exact (rcb_shok ly S W mem md E c HAR Hc ESB EC)].
rewrite restrict_mkst_fx. unfold ss_meet. apply pa_entry_st_ok_full.
- apply regs_ok_by_cases. intros r Hr. cbv [YP01.all_regs In] in Hr.
  clear HFR.
  repeat (destruct Hr as [<- | Hr];
    [ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) =>
        let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
      cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
      first [ apply getr_zero
            | symmetry; apply EE; reflexivity
            | rewrite ESB; exact R18
            | rewrite EC; exact R9 ]
    | ]); try (destruct Hr; fail).
- vm_compute. reflexivity.
- unfold rcb_mrs, rcb_mframe, rcb_mslot.
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite Usp. unfold RCB_FRAME in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil;
    lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?nn 0))) =>
      let j := eval compute in (nn - 34)%nat in let r := eval compute in (nth j rcb_saved 0) in
      let m := eval compute in (nn - 32)%nat in
      apply (chunk_ok_val SEGS E _ (sp0 - 32) off 8 (SOff nn 0) (bv_unsigned (getr regs (Z_to_bv 5 r))));
      [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
        change (ew E nn) with (ew E (32 + m)%nat); rewrite (EX m ltac:(cbv; lia));
        cbn [rcb_extra nth map app rcb_saved]; symmetry; apply Z_to_bv_bv_unsigned
      | let HR := fresh in pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HR;
        change (bv_modulus 64) with (2 ^ 64) in HR; exact HR
      | cbn; lia
      | replace (sp0 - 32 + off) with (sp0 - 8 - 8 * Z.of_nat j) by (cbn; lia); exact (HFR j r eq_refl) ] end.
  + unfold SA_C. rewrite UC. split; [lia|]. split; [unfold CALL_SIZE; lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (CmdRecCells.PROG_WRITABLE SEGS B LAWS HB PRW).
    apply (rcb_PG_slot c); [exact Hc | unfold CALL_SIZE; lia].
- apply pairwise_disjoint_of_extents. unfold rcb_mrs, rcb_mframe, rcb_mslot, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. unfold SA_C. rewrite Usp, UC.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold RCB_FRAME, CALL_SIZE in *. repeat split; lia.
- split; [|split; exact I].
  cbn [rcb_facts f_atoms atoms_ok]. unfold afact_ok, SA_C, SA_SB. cbn [af_lo af_hi af_al2].
  rewrite Usp, UC, USB. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r.
  unfold RCB_FRAME in *. split; [split; [lia | split; [|lia]]|].
  { replace (sp0 - 32) with (sp0 + (-2) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16. }
  split; [unfold SB; lia | split; [|exact I]].
  split; [unfold A_G_REC, OFF_CALLS, A_REC_SPILL; lia | split; [exact Hc8 | lia]].
Qed.

(* the seed of a segment that starts right after a call, with no region: the registers only *)
Lemma rcb_seed0 : forall (W : world SEGS) (regs : bvmap 5 word) mem pc,
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)))
/\ sh_ok SEGS rcb_BxA [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
intros W regs mem pc. split; [|apply Forall_nil].
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full; [apply regs_ok_Eimg_Ereg | reflexivity | constructor | exact I |].
split; [exact I | split; exact I].
Qed.
End e.
End f.
End d.
