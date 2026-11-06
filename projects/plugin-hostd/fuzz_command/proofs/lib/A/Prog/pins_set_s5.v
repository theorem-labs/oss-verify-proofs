(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the symbolic states of pins_set's ASan walk where it starts again after a
   call (and at record()'s join), after proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (cl_seed: a segment's symbolic
   state from the concrete facts) over fuzz_command's recorder slot. *)

(* The registers the rest of the body reads are pinned to expressions over the atoms: s0 = the slot c (atom 34),
   s2 = c + 4, s5 = c + 8 (from the second call on), s6 = g_rec, s7 = the shadow base (atom 32), s8 = the shadow
   byte address of c + 4. Every region names exactly the bytes the run may write (the frame of the symbolic
   executor then keeps every other byte): the slot's nargs word and the argument word the run stores, at the
   join the slot's fn and nargs words; read-only regions carry the frame's saved registers (atoms 38 .. 47),
   g_rec.refuse / g_rec.code (atoms 35, 36) and g_rec.state (atom 37). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas pins_set_s2 pins_set_s1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition ps_shx : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff PS_C 4) (SLit 3)) (SOff PS_SB 0).
(* the registers after a call of xstrdup: before the second call s5 still holds the first argument *)
Definition ps_sregs0_def : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 8 (SOff PS_C 0)) 18 (SOff PS_C 4)) 22 (SOff PS_GREC 0))
  23 (SOff PS_SB 0)) 24 ps_shx.
Definition ps_sregs1_def : list sv := sr_set ps_sregs0_def 21 (SOff PS_C 8).
Definition ps_sregs0 : list sv := Eval vm_compute in ps_sregs0_def.
Definition ps_sregs1 : list sv := Eval vm_compute in ps_sregs1_def.
Lemma ps_sregs0_eq : ps_sregs0 = ps_sregs0_def. Proof. vm_compute. reflexivity. Qed.
Lemma ps_sregs1_eq : ps_sregs1 = ps_sregs1_def. Proof. vm_compute. reflexivity. Qed.
Definition ps_sregs (j : nat) : list sv := if (1 <? j)%nat then ps_sregs1 else ps_sregs0.
(* the registers at record()'s join *)
Definition ps_jregs_def : list sv := sr_set (sr_set (sr_set sr_atoms 8 (SOff PS_C 0)) 22 (SOff PS_GREC 0)) 23 (SOff PS_SB 0).
Definition ps_jregs : list sv := Eval vm_compute in ps_jregs_def.
Lemma ps_jregs_eq : ps_jregs = ps_jregs_def. Proof. vm_compute. reflexivity. Qed.
(* the registers after mix_call *)
Definition ps_mregs_def : list sv := sr_set sr_atoms 22 (SOff PS_GREC 0).
Definition ps_mregs : list sv := Eval vm_compute in ps_mregs_def.
Lemma ps_mregs_eq : ps_mregs = ps_mregs_def. Proof. vm_compute. reflexivity. Qed.

Definition ps_mfacts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46 - 80) (2 ^ 47) 4); (PS_SB, mkAF SB SB 0);
         (PS_C, mkAF (A_G_REC + OFF_CALLS) A_REC_SPILL 3);
         (PS_GREC, mkAF A_G_REC A_G_REC 3); (PS_SPILL, mkAF A_REC_SPILL A_REC_SPILL 3)] [] [].

(* the regions *)
Definition ps_fnargs_r : YP09.region := YP09.mkRegion (Some PS_C) 0 8 0 8 [].
Definition ps_nargs_r (m : Z) : YP09.region := YP09.mkRegion (Some PS_C) 4 8 4 8 [YP09.mkChunk 4 (CVal 4 (SLit m))].
Definition ps_arg_r (i : Z) : YP09.region := YP09.mkRegion (Some PS_C) (8 + 8 * i) (16 + 8 * i) (8 + 8 * i) (16 + 8 * i) [].
Definition ps_frame_chunks : list YP09.chunk := Eval vm_compute in
map (fun i => YP09.mkChunk (72 - 8 * Z.of_nat i) (CVal 8 (SOff (38 + i) 0))) (seq 0 10).
Definition ps_frame_r : YP09.region := YP09.mkRegion (Some 2%nat) 0 80 0 0 ps_frame_chunks.
Definition ps_state_ro : YP09.region :=
YP09.mkRegion (Some PS_GREC) OFF_STATE (OFF_STATE + 8) OFF_STATE OFF_STATE [YP09.mkChunk OFF_STATE (CVal 8 (SOff 37 0))].
Definition ps_state_w : YP09.region := YP09.mkRegion (Some PS_GREC) OFF_STATE (OFF_STATE + 8) OFF_STATE (OFF_STATE + 8) [].
Definition ps_aft_rs (j : nat) : YP09.smem :=
[ps_nargs_r (Z.of_nat (j - 1)); ps_arg_r (Z.of_nat (j - 1)); ps_frame_r; ps_rc; ps_state_ro].
Definition ps_mix_rs : YP09.smem := [ps_frame_r; ps_state_w].

Lemma ps_regs_ok_set : forall E sr (regs : bvmap 5 word) (r : bv 5) e,
regs_ok E sr regs -> bv_eqb r 0 = false -> getr regs r = sv_denot E e -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e H Hr He r'. destruct (decide (r' = r)) as [-> | Hne].
- rewrite sr_get_set_same by exact Hr. exact He.
- rewrite sr_get_set_other by exact Hne. apply H.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
#[local] Notation LAWS := (AR_laws_ok SEGS B).
Hypothesis HB : CmdBSyms B.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.

Lemma ps_slot_PG : forall c a, ps_slot_ok c -> c <= a < c + CALL_SIZE -> Exists (in_zr a) recb_PG.
Proof.
intros c a [(H1 & H2 & _) | ->] Ha; [apply recb_grec_in | apply recb_spill_in];
  unfold A_G_REC, OFF_CALLS, OFF_ANSWER, CALL_SIZE, REC_SIZE, A_REC_SPILL, SC_SIZE in *; lia.
Qed.

(* the environment of a re-seeded state: the registers, then the walk's atoms 32 .. 47 *)
Definition ps_Ec (regsc regs : bvmap 5 word) (c rf cd st : Z) : env := Eimg (Ereg regsc (ps_extra regs 0 c rf cd st)).

Lemma ps_Ec_facts : forall regsc regs c rf cd st,
img_env VAL A_LIM (ps_Ec regsc regs c rf cd st) /\
ew (ps_Ec regsc regs c rf cd st) PS_SB = Z_to_bv 64 SB /\ ew (ps_Ec regsc regs c rf cd st) PS_C = Z_to_bv 64 c /\
ew (ps_Ec regsc regs c rf cd st) 35%nat = Z_to_bv 64 rf /\ ew (ps_Ec regsc regs c rf cd st) 36%nat = Z_to_bv 64 cd /\
ew (ps_Ec regsc regs c rf cd st) 37%nat = Z_to_bv 64 st /\
ew (ps_Ec regsc regs c rf cd st) PS_GREC = Z_to_bv 64 A_G_REC /\
ew (ps_Ec regsc regs c rf cd st) PS_SPILL = Z_to_bv 64 A_REC_SPILL /\
(forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (ps_Ec regsc regs c rf cd st) k = getr regsc r) /\
(forall i r, nth_error ps_saved i = Some r -> ew (ps_Ec regsc regs c rf cd st) (38 + i) = getr regs (Z_to_bv 5 r)).
Proof.
intros regsc regs c rf cd st.
assert (HEI : img_env VAL A_LIM (ps_Ec regsc regs c rf cd st)) by (unfold ps_Ec; apply Eimg_env).
assert (LOW : forall k, (k < A_TEXT)%nat -> ew (ps_Ec regsc regs c rf cd st) k = ew (Ereg regsc (ps_extra regs 0 c rf cd st)) k)
  by (intros k Hk; unfold ps_Ec; apply Eimg_low; exact Hk).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (ps_Ec regsc regs c rf cd st) k = getr regsc r).
{ intros k r Hk. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
  rewrite LOW by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. }
assert (ESV : forall i r, nth_error ps_saved i = Some r -> ew (ps_Ec regsc regs c rf cd st) (38 + i) = getr regs (Z_to_bv 5 r)).
{ intros i r Hir. assert (Hi : (i < 10)%nat) by (change 10%nat with (length ps_saved); apply nth_error_Some; rewrite Hir; discriminate).
  rewrite LOW by (unfold A_TEXT; lia). replace (38 + i)%nat with (32 + (6 + i))%nat by lia. rewrite ew_Ereg_extra.
  do 10 (destruct i as [|i]; [cbn in Hir; injection Hir as <-; reflexivity|]). lia. }
split; [exact HEI|].
split; [rewrite LOW by (unfold PS_SB, A_TEXT; lia); change PS_SB with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity|].
split; [rewrite LOW by (unfold PS_C, A_TEXT; lia); change PS_C with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity|].
split; [rewrite LOW by (unfold A_TEXT; lia); change 35%nat with (32 + 3)%nat; rewrite ew_Ereg_extra; reflexivity|].
split; [rewrite LOW by (unfold A_TEXT; lia); change 36%nat with (32 + 4)%nat; rewrite ew_Ereg_extra; reflexivity|].
split; [rewrite LOW by (unfold A_TEXT; lia); change 37%nat with (32 + 5)%nat; rewrite ew_Ereg_extra; reflexivity|].
split; [rewrite (img_env_atomP _ PS_GREC HEI ltac:(unfold PS_GREC, A_OBJ, A_TEXT, A_LIM; lia)), (ps_grec_val VOBJS); reflexivity|].
split; [rewrite (img_env_atomP _ PS_SPILL HEI ltac:(unfold PS_SPILL, A_OBJ, A_TEXT, A_LIM; lia)), (ps_spill_val VOBJS); reflexivity|].
split; [exact EE | exact ESV].
Qed.

Lemma ps_frame_ok : forall E (W : world SEGS) mem (regs : bvmap 5 word) sp,
(forall i r, nth_error ps_saved i = Some r -> ew E (38 + i) = getr regs (Z_to_bv 5 r)) ->
(forall i r, nth_error ps_saved i = Some r ->
  aval_mem (rdW W mem) (sp + 72 - 8 * Z.of_nat i) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))) ->
Forall (YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) sp) ps_frame_chunks.
Proof.
intros E W mem regs sp HE HM.
assert (ONE : forall i r, nth_error ps_saved i = Some r ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) sp (YP09.mkChunk (72 - 8 * Z.of_nat i) (CVal 8 (SOff (38 + i) 0)))).
{ intros i r Hir. apply (chunk_ok_val SEGS E _ sp _ 8 _ (bv_unsigned (getr regs (Z_to_bv 5 r)))).
  - cbn [sv_denot]. rewrite (HE i r Hir), Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity.
  - rewrite ps_pow8. apply bv_unsigned_in_range.
  - lia.
  - replace (sp + (72 - 8 * Z.of_nat i)) with (sp + 72 - 8 * Z.of_nat i) by lia.
    exact (val_mem_view SEGS (w_H W) mem _ 8%nat _ (HM i r Hir)). }
unfold ps_frame_chunks.
apply Forall_cons; [exact (ONE 0%nat _ eq_refl)|]. apply Forall_cons; [exact (ONE 1%nat _ eq_refl)|].
apply Forall_cons; [exact (ONE 2%nat _ eq_refl)|]. apply Forall_cons; [exact (ONE 3%nat _ eq_refl)|].
apply Forall_cons; [exact (ONE 4%nat _ eq_refl)|]. apply Forall_cons; [exact (ONE 5%nat _ eq_refl)|].
apply Forall_cons; [exact (ONE 6%nat _ eq_refl)|]. apply Forall_cons; [exact (ONE 7%nat _ eq_refl)|].
apply Forall_cons; [exact (ONE 8%nat _ eq_refl)|]. apply Forall_cons; [exact (ONE 9%nat _ eq_refl)|].
apply Forall_nil.
Qed.

(* the symbolic state at the return of the j-th xstrdup *)
Lemma ps_aft_seed : forall ly S (W : world SEGS) mem md (regs regsc : bvmap 5 word) (j : nat) pc c rf cd st,
AR SEGS B ly S W mem md ->
ps_slot_ok c -> (1 <= j <= 4)%nat ->
2 ^ 46 - 80 <= spZ regsc <= 2 ^ 47 -> spZ regsc mod 16 = 0 ->
getr regsc 8 = w64 c -> getr regsc 18 = w64 (c + 4) -> getr regsc 22 = w64 A_G_REC -> getr regsc 23 = w64 SB ->
getr regsc 24 = w64 (SB + (c + 4) / 8) -> ((1 < j)%nat -> getr regsc 21 = w64 (c + 8)) ->
aval_mem (rdW W mem) (c + 4) 4 (Z.of_nat (j - 1)) ->
(forall i r, nth_error ps_saved i = Some r ->
  aval_mem (rdW W mem) (spZ regsc + 72 - 8 * Z.of_nat i) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))) ->
aval_mem (rdW W mem) A_G_REC 4 rf -> aval_mem (rdW W mem) (A_G_REC + 4) 4 cd ->
aval_mem (rdW W mem) (A_G_REC + OFF_STATE) 8 st ->
0 <= rf < 2 ^ 32 -> 0 <= cd < 2 ^ 32 -> 0 <= st < 2 ^ 64 ->
st_ok_pi SEGS VAL (ps_Ec regsc regs c rf cd st) (mkSS pc (ps_sregs j) (ps_aft_rs j) None ps_mfacts)
  (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)))
/\ sh_ok SEGS ps_Bx ps_SH (ps_Ec regsc regs c rf cd st) (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md regs regsc j pc c rf cd st HAR Hc Hj Hsp Hsp16 R8 R18 R22 R23 R24 R21 HNA HFR HRF HCD HST Hrf Hcd Hst.
set (E := ps_Ec regsc regs c rf cd st).
destruct (ps_Ec_facts regsc regs c rf cd st) as (HEI & ESB & EC & E35 & E36 & E37 & EG & ES & EE & ESV).
fold E in HEI, ESB, EC, E35, E36, E37, EG, ES, EE, ESV.
destruct (ps_slot_bounds c Hc) as [Hcb Hc8].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regsc))
  by (rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (Hc64 : 0 <= c < 2 ^ 64) by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
assert (UC : forall k, 0 <= k <= 8 -> sv_denot E (SOff PS_C k) = w64 (c + k)).
{ intros k Hk. cbn [sv_denot]. rewrite EC, unsigned_lit_small by exact Hc64. reflexivity. }
split; [| exact (ps_sh_ok B HB ly S W mem md E c HAR ESB EC Hc)].
rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full.
- assert (R0 : regs_ok E sr_atoms regsc) by (unfold E, ps_Ec; apply regs_ok_Eimg_Ereg).
  assert (H0 : regs_ok E ps_sregs0_def regsc).
  { unfold ps_sregs0_def.
    apply ps_regs_ok_set; [|reflexivity|].
    2: { rewrite R24. unfold ps_shx. symmetry.
         rewrite (denot_shx E PS_C PS_SB 4 c SB EC ESB); [reflexivity | lia | lia | | cbv [SB]; lia].
         unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *. lia. }
    apply ps_regs_ok_set; [|reflexivity|].
    2: { rewrite R23. cbn [sv_denot]. rewrite ESB, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
    apply ps_regs_ok_set; [|reflexivity|].
    2: { rewrite R22. cbn [sv_denot]. rewrite EG, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
    apply ps_regs_ok_set; [|reflexivity|].
    2: { rewrite R18, (UC 4 ltac:(lia)). reflexivity. }
    apply ps_regs_ok_set; [exact R0 | reflexivity |].
    rewrite R8, (UC 0 ltac:(lia)), Z.add_0_r. reflexivity. }
  unfold ps_sregs. destruct (1 <? j)%nat eqn:Ej.
  + rewrite ps_sregs1_eq. unfold ps_sregs1_def. apply ps_regs_ok_set; [exact H0 | reflexivity |].
    rewrite (R21 ltac:(apply Nat.ltb_lt; exact Ej)), (UC 8 ltac:(lia)). reflexivity.
  + rewrite ps_sregs0_eq. exact H0.
- destruct j as [|[|[|[|[|j]]]]]; try lia; vm_compute; reflexivity.
- unfold ps_aft_rs, ps_nargs_r, ps_arg_r, ps_frame_r, ps_rc, ps_state_ro.
  repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (VB PS_C c EC Hc64).
    split; [lia|]. split; [unfold A_REC_SPILL in *; lia|]. split.
    { intros o Ho. apply (cmd_prog_writable ly S W mem md); [exact HAR|]. apply (ps_slot_PG c); [exact Hc | unfold CALL_SIZE; lia]. }
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ c 4 4 (SLit (Z.of_nat (j - 1))) (Z.of_nat (j - 1)));
    [reflexivity | rewrite ps_pow4; lia | cbn; lia |].
    exact (val_mem_view SEGS (w_H W) mem (c + 4) 4%nat _ HNA).
  + rewrite (VB PS_C c EC Hc64).
    split; [lia|]. split; [unfold A_REC_SPILL in *; lia|]. split; [|constructor].
    intros o Ho. apply (cmd_prog_writable ly S W mem md); [exact HAR|]. apply (ps_slot_PG c); [exact Hc | unfold CALL_SIZE; lia].
  + rewrite (VB 2%nat (spZ regsc) E2) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    exact (ps_frame_ok E W mem regs (spZ regsc) ESV HFR).
  + rewrite (VB PS_GREC A_G_REC EG) by (unfold A_G_REC; lia).
    split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS E _ A_G_REC 0 4 (SOff 35 0) rf);
      [cbn [sv_denot]; rewrite E35, unsigned_lit_small, Z.add_0_r by lia; reflexivity | rewrite ps_pow4; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_view SEGS (w_H W) mem A_G_REC 4%nat _ HRF).
    * apply (chunk_ok_val SEGS E _ A_G_REC 4 4 (SOff 36 0) cd);
      [cbn [sv_denot]; rewrite E36, unsigned_lit_small, Z.add_0_r by lia; reflexivity | rewrite ps_pow4; lia | cbn; lia |].
      exact (val_mem_view SEGS (w_H W) mem (A_G_REC + 4) 4%nat _ HCD).
  + rewrite (VB PS_GREC A_G_REC EG) by (unfold A_G_REC; lia).
    split; [unfold A_G_REC, OFF_STATE; lia|]. split; [unfold A_G_REC, OFF_STATE; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ A_G_REC OFF_STATE 8 (SOff 37 0) st);
    [cbn [sv_denot]; rewrite E37, unsigned_lit_small, Z.add_0_r by lia; reflexivity | rewrite ps_pow8; lia | cbn; lia |].
    exact (val_mem_view SEGS (w_H W) mem (A_G_REC + OFF_STATE) 8%nat _ HST).
- apply pairwise_disjoint_of_extents.
  unfold ps_aft_rs, ps_nargs_r, ps_arg_r, ps_frame_r, ps_rc, ps_state_ro, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB PS_C c EC Hc64), (VB 2%nat (spZ regsc) E2) by lia.
  rewrite (VB PS_GREC A_G_REC EG) by (unfold A_G_REC; lia).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  destruct Hc as [(H1 & H2 & _) | Hsp'];
    unfold A_G_REC, OFF_CALLS, OFF_ANSWER, CALL_SIZE, A_REC_SPILL, OFF_STATE in *; repeat split; lia.
- unfold facts_ok, ps_mfacts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; [exact I | exact I]].
  split; [|split; [|split; [|split; [|split; [|exact I]]]]].
  + apply (ps_afact E 2%nat (spZ regsc)); [exact E2 | lia | lia | change (2 ^ 4) with 16; exact Hsp16 | lia].
  + apply (ps_afact E PS_SB SB); [exact ESB | unfold SB; lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
  + apply (ps_afact E PS_C c); [exact EC | exact Hc64 | exact Hcb | change (2 ^ 3) with 8; exact Hc8 | lia].
  + apply (ps_afact E PS_GREC A_G_REC); [exact EG | unfold A_G_REC; lia | lia | reflexivity | lia].
  + apply (ps_afact E PS_SPILL A_REC_SPILL); [exact ES | unfold A_REC_SPILL; lia | lia | reflexivity | lia].
Qed.

(* the symbolic state at record()'s join (pc = PS_JOIN on the table arm, PS_RET_RCF after rec_calls_free) *)
Lemma ps_join_seed : forall ly S (W : world SEGS) mem md (regs regsc : bvmap 5 word) pc c,
AR SEGS B ly S W mem md ->
ps_slot_ok c ->
2 ^ 46 - 80 <= spZ regsc <= 2 ^ 47 -> spZ regsc mod 16 = 0 ->
getr regsc 8 = w64 c -> getr regsc 22 = w64 A_G_REC -> getr regsc 23 = w64 SB ->
st_ok_pi SEGS VAL (ps_Ec regsc regs c 0 0 0) (mkSS pc ps_jregs [ps_fnargs_r] None ps_mfacts)
  (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)))
/\ sh_ok SEGS ps_Bx ps_SH (ps_Ec regsc regs c 0 0 0) (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md regs regsc pc c HAR Hc Hsp Hsp16 R8 R22 R23.
set (E := ps_Ec regsc regs c 0 0 0).
destruct (ps_Ec_facts regsc regs c 0 0 0) as (HEI & ESB & EC & E35 & E36 & E37 & EG & ES & EE & ESV).
fold E in HEI, ESB, EC, E35, E36, E37, EG, ES, EE, ESV.
destruct (ps_slot_bounds c Hc) as [Hcb Hc8].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regsc))
  by (rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (Hc64 : 0 <= c < 2 ^ 64) by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
split; [| exact (ps_sh_ok B HB ly S W mem md E c HAR ESB EC Hc)].
rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full.
- assert (R0 : regs_ok E sr_atoms regsc) by (unfold E, ps_Ec; apply regs_ok_Eimg_Ereg).
  rewrite ps_jregs_eq. unfold ps_jregs_def.
  apply ps_regs_ok_set; [|reflexivity|].
  2: { rewrite R23. cbn [sv_denot]. rewrite ESB, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  apply ps_regs_ok_set; [|reflexivity|].
  2: { rewrite R22. cbn [sv_denot]. rewrite EG, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
  apply ps_regs_ok_set; [exact R0 | reflexivity |].
  rewrite R8. cbn [sv_denot]. rewrite EC, unsigned_lit_small, Z.add_0_r by exact Hc64. reflexivity.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold ps_fnargs_r, YP09.region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (VB PS_C c EC Hc64).
  split; [lia|]. split; [unfold A_REC_SPILL in *; lia|]. split; [|constructor].
  intros o Ho. apply (cmd_prog_writable ly S W mem md); [exact HAR|]. apply (ps_slot_PG c); [exact Hc | unfold CALL_SIZE; lia].
- cbn. exact (conj I I).
- unfold facts_ok, ps_mfacts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; [exact I | exact I]].
  split; [|split; [|split; [|split; [|split; [|exact I]]]]].
  + apply (ps_afact E 2%nat (spZ regsc)); [exact E2 | lia | lia | change (2 ^ 4) with 16; exact Hsp16 | lia].
  + apply (ps_afact E PS_SB SB); [exact ESB | unfold SB; lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
  + apply (ps_afact E PS_C c); [exact EC | exact Hc64 | exact Hcb | change (2 ^ 3) with 8; exact Hc8 | lia].
  + apply (ps_afact E PS_GREC A_G_REC); [exact EG | unfold A_G_REC; lia | lia | reflexivity | lia].
  + apply (ps_afact E PS_SPILL A_REC_SPILL); [exact ES | unfold A_REC_SPILL; lia | lia | reflexivity | lia].
Qed.

(* the symbolic state at the return of mix_call *)
Lemma ps_mix_seed : forall ly S (W : world SEGS) mem md (regs regsc : bvmap 5 word) pc c,
AR SEGS B ly S W mem md ->
ps_slot_ok c ->
2 ^ 46 - 80 <= spZ regsc <= 2 ^ 47 -> spZ regsc mod 16 = 0 ->
getr regsc 22 = w64 A_G_REC ->
(forall i r, nth_error ps_saved i = Some r ->
  aval_mem (rdW W mem) (spZ regsc + 72 - 8 * Z.of_nat i) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))) ->
st_ok_pi SEGS VAL (ps_Ec regsc regs c 0 0 0) (mkSS pc ps_mregs ps_mix_rs None ps_mfacts)
  (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)))
/\ sh_ok SEGS ps_Bx ps_SH (ps_Ec regsc regs c 0 0 0) (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md regs regsc pc c HAR Hc Hsp Hsp16 R22 HFR.
set (E := ps_Ec regsc regs c 0 0 0).
destruct (ps_Ec_facts regsc regs c 0 0 0) as (HEI & ESB & EC & E35 & E36 & E37 & EG & ES & EE & ESV).
fold E in HEI, ESB, EC, E35, E36, E37, EG, ES, EE, ESV.
destruct (ps_slot_bounds c Hc) as [Hcb Hc8].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regsc))
  by (rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (Hc64 : 0 <= c < 2 ^ 64) by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
split; [| exact (ps_sh_ok B HB ly S W mem md E c HAR ESB EC Hc)].
rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full.
- assert (R0 : regs_ok E sr_atoms regsc) by (unfold E, ps_Ec; apply regs_ok_Eimg_Ereg).
  rewrite ps_mregs_eq. unfold ps_mregs_def.
  apply ps_regs_ok_set; [exact R0 | reflexivity |].
  rewrite R22. cbn [sv_denot]. rewrite EG, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- vm_compute. reflexivity.
- unfold ps_mix_rs, ps_frame_r, ps_state_w.
  repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (VB 2%nat (spZ regsc) E2) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    exact (ps_frame_ok E W mem regs (spZ regsc) ESV HFR).
  + rewrite (VB PS_GREC A_G_REC EG) by (unfold A_G_REC; lia).
    split; [unfold A_G_REC, OFF_STATE; lia|]. split; [unfold A_G_REC, OFF_STATE; lia|]. split; [|constructor].
    intros o Ho. apply (cmd_prog_writable ly S W mem md); [exact HAR|]. apply recb_grec_in.
    unfold OFF_STATE, REC_SIZE in *. lia.
- apply pairwise_disjoint_of_extents.
  unfold ps_mix_rs, ps_frame_r, ps_state_w, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB 2%nat (spZ regsc) E2) by lia.
  rewrite (VB PS_GREC A_G_REC EG) by (unfold A_G_REC; lia).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold A_G_REC, OFF_STATE in *. repeat split; lia.
- unfold facts_ok, ps_mfacts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; [exact I | exact I]].
  split; [|split; [|split; [|split; [|split; [|exact I]]]]].
  + apply (ps_afact E 2%nat (spZ regsc)); [exact E2 | lia | lia | change (2 ^ 4) with 16; exact Hsp16 | lia].
  + apply (ps_afact E PS_SB SB); [exact ESB | unfold SB; lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
  + apply (ps_afact E PS_C c); [exact EC | exact Hc64 | exact Hcb | change (2 ^ 3) with 8; exact Hc8 | lia].
  + apply (ps_afact E PS_GREC A_G_REC); [exact EG | unfold A_G_REC; lia | lia | reflexivity | lia].
  + apply (ps_afact E PS_SPILL A_REC_SPILL); [exact ES | unfold A_REC_SPILL; lia | lia | reflexivity | lia].
Qed.

End e.
End f.
End d.
