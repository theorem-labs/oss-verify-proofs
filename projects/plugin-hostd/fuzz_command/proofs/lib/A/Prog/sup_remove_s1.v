(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of sup_pool_config (plugin-hostd/fuzz_command, image
   fuzz_command.asan-ubsan, entry BASE + AF_sup_pool_config = 0x8bed0, 127 instructions): it proves a Theorem Labs lane's
   `tsup_pool_config_spec` (lib/B/Prog/sup_pool_config_c.v, a working branch 707acd856cb; the same text as at
   f490061c104) in the form of
   cgif_file_fuzzer's per-function walks: afn_pre at the entry, the symbolic executor over the position-abstract
   listing up to each call, the runtime's rules at the runtime calls (__asan_stack_malloc_0, the snprintf wrapper,
   the frame's release by its flag byte), the callee contracts record_c, arg_s_c, rec_shape_of_c and answer_c at the
   program calls (through cl_callS_wide / cl_callS_na), the return through paj_ret_at, and apost_base at the end.

   It is the B re-walk of the A walk lib/A/Prog/sup_pool_config.v (a working branch c4f188792bb),
   whose B code differs: B calls record() and arg_s() where A inlined record() and called xstrdup, and B inlines
   arg_i, so this function owns arg_i's class-0 side-stack frame (64 bytes, b = frame + 32) and its snprintf. The
   frame code (prologue, realignment `andi sp,sp,-32`, __asan_stack_malloc_0, header and shadow f1 f1 f1 f1 | f8 f8 |
   f3 f3, b unpoisoned around the snprintf and the second arg_s, the release through the flag byte) is arg_i's ASan
   walk's (lib/A/Prog/arg_i.v, a working branch 12dc52bfe84) and answer_code's ASan walk's
   (lib/A/Prog/answer_code.v, a working branch 2ba4488ce71); the B kit usage is socket_send's B walk
   (lib/B/Prog/socket_send.v, a working branch a470f91dbfb).

   Report and trap edges: none. The function has no `jal __asan_report_*`, no `unimp`, no UBSan handler call
   (capstone over the pin's .symtab, gen/traps.B.summary row `sup_pool_config 0`). Its branches: 0x8bf30 `beqz a2`
   on the use-after-return flag, read through the GOT word 0xa5fa8 at the record's const cell 0xb0c40 (= 1, lib/B/YF0m.v
   z4 (ANum 0xb0c40) 0x1, AR's const-cell law al_const; the executor decides it not taken); 0x8bf4c `bnez s2` and
   0x8c040 `beqz s2` on the side-stack frame (nonzero, __asan_stack_malloc_0's post; decided by the frame atom's
   fact), so the real-stack fallback 0x8bf50-0x8bf68 with its page probe and the real-stack release 0x8c074-0x8c090
   are not reached. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/sup_pool_config.v, with its module paths, module names and numbers changed; 332 of its 404 lines of code are new or changed and 1992 lines of the source are left out. *)
(* sup_remove's walk on the ASan build of plugin-hostd/fuzz_command, part 1: the footprint, the symbolic entry and
   join states with their seeds, the step rule for a store into the program's statics, and the statements of the
   two walk pieces the arms compose (sr_jl_stmt, sr_tail_stmt). sup_remove.v proves tsup_remove_spec
   (lib/A/Prog/sup_remove_c.v) as stated.

   The entry state follows cgif's flushFrame seed (cgif lib/A/ACj0.v:40-53, A/AChz.v:57-196) and arg_i's
   (lib/A/Prog/arg_i_s1.v): the 32-byte frame below the entry sp, the shadow GOT word (the listing's A_OBJ 0,
   0xa63f0) and the shadow cell (A_OBJ 12, 0xb10b8), and g_rec.ncalls (A_OBJ 44 = g_rec 0x5e3740, + 8), which the
   function reads before it writes, holding the extra atom kN = length (r_calls R). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaLibG PaDenot PaLibF PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaSB PaCallRun PaCall PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c arg_i_c answer_c sup_remove_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the footprint the statement names (sup_remove_c.v:86-87) *)
Definition sr_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8) ::
(A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

(* ---- the symbolic entry state ---- *)
Definition sr_Bx : sv := SOff 32 0.
Definition sr_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* atom 32: the shadow base; atom 33: g_rec.ncalls *)
Definition sr_kN : nat := 33%nat.
Definition sr_nc_region : YP09.region :=
YP09.mkRegion (Some (A_OBJ 44)) 8 12 8 12 [YP09.mkChunk 8 (CVal 4 (SOff sr_kN 0))].
Definition sr_regions0 : smem := [ stack_region 32; got_regionP; bcell_regionP 32; sr_nc_region ].
Definition sr_atoms0 : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0); (sr_kN, mkAF 0 16 0); (A_OBJ 44, mkAF A_G_REC A_G_REC 6) ].
Definition ss_sr0 : sstate := mkSS AF_sup_remove sr_atoms sr_regions0 None (mkFacts sr_atoms0 [] []).
Definition sr_extra (n : Z) : list word := map (Z_to_bv 64) [SB; n].

(* ---- the symbolic state at the join 0x8abbc (BASE + AF_sup_remove + 0x6c), where both arms have s1 = c, the
   call's slot (g_rec's table slot ncalls, or record.spill), s0 = id and s2 = the shadow base, and the frame holds
   the entry ra, s0, s1, s2. Atoms 32..35 are those four entry values; atom 9 (s1) is c. ---- *)
Definition SR_J : Z := 0x6c.
Definition sr_Bxj : sv := SOff 18 0.
Definition sr_SHj : list shent := [mkSHE 9 0 56].
Definition sr_jstack : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 32 0 32
[YP09.mkChunk 0 (CVal 8 (SOff 35 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0));
 YP09.mkChunk 16 (CVal 8 (SOff 33 0)); YP09.mkChunk 24 (CVal 8 (SOff 32 0))].
Definition sr_jslot : YP09.region := YP09.mkRegion (Some 9%nat) 0 8 0 8 [].
Definition sr_jregions : smem := [ sr_jstack; sr_jslot ].
Definition sr_jatoms : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (9%nat, mkAF (A_G_REC + OFF_CALLS) A_REC_SPILL 3); (18%nat, mkAF SB SB 0) ].
Definition ss_srj : sstate := mkSS (AF_sup_remove + SR_J) sr_atoms sr_jregions None (mkFacts sr_jatoms [] []).
(* the entry ra, s0, s1, s2 *)
Definition sr_jextra (regs : bvmap 5 word) : list word := [getr regs 1; getr regs 8; getr regs 9; getr regs 18].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

(* the per-binary walk facts (cgif's names, and this walk's interim names) *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis VOBJS : cmd_val_objs.
(* CmdRecBase.v's field cif_prog_img of cmd_img_facts (sup_remove.v gives it from IMG) and the core's prog_rw
   (the walk hypothesis PRW) *)
Hypothesis cif_prog_img : forall a, inFP cmd_PG a -> in_img SEGS a.
Hypothesis PRW : prog_rw SEGS B.

(* g_rec, record.spill and g_quitting are the program's statics (CmdBSyms' ts_prog) *)
Lemma HPROG : forall a, inFP cmd_PG a -> Exists (in_zr a) (as_prog_static B).
Proof.
intros a (r & Hr & Ha). rewrite (ts_prog B HB). unfold cmd_PG, TFIB_PROG_STATIC, A_G_REC, A_REC_SPILL, A_G_QUITTING in *.
cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha;
[apply Exists_cons_hd | apply Exists_cons_tl, Exists_cons_hd | apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd];
unfold in_zr; cbn [fst snd]; lia.
Qed.
Lemma sr_prog_sep : forall a, inFP cmd_PG a ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4) /\
~ Exists (in_zr a) (asyms_areas B).
Proof.
intros a Ha. split; [exact (cif_prog_img a Ha)|].
exact (prog_static_sep B a (ts_ok B HB) (HPROG a Ha)).
Qed.
Lemma sr_inPG : forall a, (A_G_REC <= a < A_G_REC + 960 \/ A_REC_SPILL <= a < A_REC_SPILL + 56) -> inFP cmd_PG a.
Proof.
intros a [Ha | Ha]; unfold cmd_PG.
- exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn; lia].
- exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity | cbn; lia].
Qed.
Lemma sr_val_obj : forall i, (i < length cmd_objs)%nat -> VAL (A_OBJ i) = nth i cmd_objs 0.
Proof. exact VOBJS. Qed.
Lemma sr_val_mem : forall H mem a n v, aval_mem (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn [option_map] in Hv; [|discriminate Hv].
injection Hv as Hv. apply (f_equal (Z_to_bv 8)) in Hv. rewrite Z_to_bv_bv_unsigned in Hv.
rewrite Hv. reflexivity.
Qed.

(* a store into the program's statics is a footprint write the journal admits (awr_byte's static case) *)
Lemma awr_ok_cons_prog : forall E r rs STK sp0 FP bl0 blc fr0 ly own n b,
YP09.r_base r = Some n -> bv_unsigned (ew E n) = b ->
(forall a, b + YP09.r_wlo r <= a < b + YP09.r_whi r -> inFP FP a /\ inFP cmd_PG a) ->
awr_ok SEGS B E rs STK sp0 FP bl0 blc fr0 ly own -> awr_ok SEGS B E (r :: rs) STK sp0 FP bl0 blc fr0 ly own.
Proof.
intros E r rs STK sp0 FP bl0 blc fr0 ly own n b Hb Hn Hfp H a (r' & [<-|Hin'] & Ha).
- rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hn in Ha. destruct (Hfp a ltac:(lia)) as [Hf Hpg].
  right. right. right. right. left. split; [exact Hf|]. split; [exact (HPROG a Hpg) | exact (cif_prog_img a Hpg)].
- apply H. exists r'. auto.
Qed.

(* the entry state *)
Lemma sr_entry : forall W ly S regs mem md ch n,
afn_pre SEGS B SUP_REMOVE_STK ly S W regs mem md ch ->
aval_mem (rdW W mem) (A_G_REC + OFF_NCALLS) 4 n -> 0 <= n <= 16 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (sr_extra n))) ss_sr0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_remove)) mem (seg_rom SEGS))).
Proof.
intros W ly S regs mem md ch n HPRE Hn Hn16.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : SUP_REMOVE_STK >= 32) by (vm_compute; discriminate).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (sr_extra n))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E sr_kN = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold sr_kN, A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (V0 : VAL (A_OBJ 0) = 0xa63f0) by (rewrite (VOBJS 0%nat ltac:(vm_compute; lia)); reflexivity).
assert (V12 : VAL (A_OBJ 12) = 0xb10b8) by (rewrite (VOBJS 12%nat ltac:(vm_compute; lia)); reflexivity).
assert (V44 : VAL (A_OBJ 44) = A_G_REC) by (rewrite (VOBJS 44%nat ltac:(vm_compute; lia)); reflexivity).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 0xa63f0) by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V0; reflexivity).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 0xb10b8) by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V12; reflexivity).
assert (E285 : ew E (A_OBJ 44) = Z_to_bv 64 A_G_REC) by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V44; reflexivity).
rewrite V0, V12 in Kgot. rewrite V12 in Kcell.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
{ intros k v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
unfold ss_sr0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold sr_regions0, stack_region, got_regionP, bcell_regionP, sr_nc_region.
  repeat apply Forall_cons; try apply Forall_nil.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
    split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (VB (A_OBJ 0) 0xa63f0 E241) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ 0xa63f0 0 8 (SOff (A_OBJ 12) 0) 0xb10b8);
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (VB (A_OBJ 12) 0xb10b8 E253) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ 0xb10b8 0 8 (SOff 32 0) SB);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (VB (A_OBJ 44) A_G_REC E285) by (unfold A_G_REC; lia). split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|].
    split.
    * intros o Ho. apply PRW. apply HPROG. apply sr_inPG. unfold A_G_REC in *. lia.
    * constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ A_G_REC 8 4 (SOff sr_kN 0) n);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      exact (sr_val_mem (w_H W) mem _ _ _ Hn).
- apply pairwise_disjoint_of_extents.
  unfold sr_regions0, stack_region, got_regionP, bcell_regionP, sr_nc_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) 0xa63f0 E241), (VB (A_OBJ 12) 0xb10b8 E253), (VB (A_OBJ 44) A_G_REC E285) by (unfold A_G_REC; lia).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj, A_G_REC. cbn [fst snd].
  unfold ASAN_CEIL in *. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok sr_atoms0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32, E33, E285. rewrite !unsigned_lit_small by (unfold SB, A_G_REC; lia).
  change (2 ^ 4) with 16. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; unfold SB, A_G_REC; first [lia | reflexivity].
Qed.

(* the call's slot: a slot of g_rec's call table or record.spill (arg_i_c.v:82's form) *)
Definition sr_slot (c : Z) : Prop :=
(exists i, 0 <= i < REC_CALLS_MAX /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ c = A_REC_SPILL.
Lemma sr_slot_range : forall c, sr_slot c ->
c mod 8 = 0 /\ A_G_REC + OFF_CALLS <= c <= A_REC_SPILL /\
((A_G_REC + OFF_CALLS <= c /\ c + CALL_SIZE <= A_G_REC + OFF_ANSWER) \/ c = A_REC_SPILL).
Proof.
intros c [(i & Hi & ->) | ->]; unfold OFF_CALLS, OFF_ANSWER, CALL_SIZE, REC_CALLS_MAX, A_G_REC, A_REC_SPILL in *.
- split; [|lia]. replace (6174528 + 16 + 56 * i) with ((771818 + 7 * i) * 8) by lia. apply Z_mod_mult.
- split; [reflexivity | lia].
Qed.
Lemma sr_slot_PG : forall c a, sr_slot c -> c <= a < c + CALL_SIZE -> inFP cmd_PG a.
Proof.
intros c a Hc Ha. apply sr_inPG. destruct (sr_slot_range c Hc) as (_ & _ & [H | ->]); unfold CALL_SIZE, OFF_CALLS, OFF_ANSWER, A_G_REC, A_REC_SPILL in *; lia.
Qed.
Lemma sr_in_pairs : forall (l : list (Z * Z)) r, existsb (fun q => (fst q =? fst r) && (snd q =? snd r)) l = true -> In r l.
Proof.
induction l as [|q l IH]; intros r H; [discriminate H|]. cbn [existsb] in H. apply orb_true_iff in H as [H|H].
- left. apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1, H2. destruct q, r; cbn in *; subst; reflexivity.
- right. exact (IH r H).
Qed.
Lemma sr_slot_zsh : forall ly S (W : world SEGS) mem md c, AR SEGS B ly S W mem md -> sr_slot c ->
range_addressable (rdW W mem) SHADOW_OFF c 56.
Proof.
intros ly S W mem md c HAR Hc. destruct (sr_slot_range c Hc) as (Hc8 & _ & [H | ->]).
- (* g_rec's table lies in the record's zero-shadow range [0xada00, 0x5e3b00) *)
  apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0xada00, 0x536100) c 56 HAR);
  [apply sr_in_pairs; vm_compute; reflexivity | reflexivity | reflexivity
  | cbn [fst snd]; unfold CALL_SIZE, OFF_CALLS, OFF_ANSWER, A_G_REC in *; lia
  | cbn [fst snd]; unfold CALL_SIZE, OFF_CALLS, OFF_ANSWER, A_G_REC in *; lia].
- (* record.spill's body is the record's zero-shadow range [0x5e3be0, 0x5e3c18) *)
  apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0x5e3be0, 0x38) A_REC_SPILL 56 HAR);
  [apply sr_in_pairs; vm_compute; reflexivity | reflexivity | reflexivity | cbn [fst snd]; unfold A_REC_SPILL; lia
  | cbn [fst snd]; unfold A_REC_SPILL; lia].
Qed.
(* a chunk of a region of the symbolic state holds its value *)
Lemma sr_st_chunk : forall E ss ms r c, st_ok SEGS E ss ms -> In r (ss_mem ss) -> In c (YP09.r_chunks r) ->
YP09.chunk_ok SEGS E (ms_mem ms) (base_val E (YP09.r_base r)) c.
Proof.
intros E ss ms r c (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hr Hc.
apply region_ok_chunk; [|exact Hc]. rewrite Forall_forall in Hok. exact (Hok r Hr).
Qed.
(* the state at the join *)
Lemma sr_join_seed : forall W ly S (regs regsj : bvmap 5 word) memj mdj sp0 c,
AR SEGS B ly S W memj mdj ->
spZ regsj = sp0 - 32 -> sp0 mod 16 = 0 -> 2 ^ 46 + 32 <= sp0 <= 2 ^ 47 ->
(forall a, sp0 - 32 <= a < sp0 -> apresent (w_H W) memj a) ->
val_mem SEGS (mrestrict (w_H W) memj) (sp0 - 32) 8 (bv_unsigned (getr regs 18)) ->
val_mem SEGS (mrestrict (w_H W) memj) (sp0 - 24) 8 (bv_unsigned (getr regs 9)) ->
val_mem SEGS (mrestrict (w_H W) memj) (sp0 - 16) 8 (bv_unsigned (getr regs 8)) ->
val_mem SEGS (mrestrict (w_H W) memj) (sp0 - 8) 8 (bv_unsigned (getr regs 1)) ->
getr regsj 9 = w64 c -> sr_slot c -> getr regsj 18 = w64 SB ->
st_ok_pi SEGS VAL (Eimg (Ereg regsj (sr_jextra regs))) ss_srj
  (restrict (w_H W) (mkst regsj (Z_to_bv 64 (BASE + (AF_sup_remove + SR_J))) memj (seg_rom SEGS))) /\
sh_ok SEGS sr_Bxj sr_SHj (Eimg (Ereg regsj (sr_jextra regs))) (mrestrict (w_H W) memj).
Proof.
intros W ly S regs regsj memj mdj sp0 c HAR Hsp Hal Hsp47 Hpres V18 V9 V8 V1 H9 Hc H18.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (sr_slot_range c Hc) as (Hc8 & Hclo & Hc2).
set (E := Eimg (Ereg regsj (sr_jextra regs))).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regsj r).
{ intros k r Hk. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. }
assert (E2 : ew E 2 = getr regsj 2) by (apply EE; reflexivity).
assert (E9 : ew E 9 = Z_to_bv 64 c) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
assert (E18 : ew E 18 = Z_to_bv 64 SB) by (rewrite (EE 18%nat 18%bv eq_refl); exact H18).
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) = nth j (sr_jextra regs) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E32 : ew E 32 = getr regs 1) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = getr regs 8) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = getr regs 9) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = getr regs 18) by exact (EX 3%nat ltac:(lia)).
clear EE EX. assert (Usp : bv_unsigned (ew E 2) = sp0 - 32) by (rewrite E2; exact Hsp).
assert (Uc : bv_unsigned (ew E 9) = c) by (rewrite E9; apply unsigned_lit_small; unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
assert (USB : bv_unsigned (ew E 18) = SB) by (rewrite E18; apply unsigned_lit_small; unfold SB; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_srj. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold sr_jregions, sr_jstack, sr_jslot. repeat apply Forall_cons; try apply Forall_nil.
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
      split; [lia|]. split; [lia|]. split.
      { intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
      repeat apply Forall_cons; try apply Forall_nil;
      [ apply (chunk_ok_val SEGS E _ (sp0 - 32) 0 8 (SOff 35 0) (bv_unsigned (getr regs 18)))
      | apply (chunk_ok_val SEGS E _ (sp0 - 32) 8 8 (SOff 34 0) (bv_unsigned (getr regs 9)))
      | apply (chunk_ok_val SEGS E _ (sp0 - 32) 16 8 (SOff 33 0) (bv_unsigned (getr regs 8)))
      | apply (chunk_ok_val SEGS E _ (sp0 - 32) 24 8 (SOff 32 0) (bv_unsigned (getr regs 1))) ];
      first [ cbn [sv_denot]; rewrite ?E32, ?E33, ?E34, ?E35, Z.add_0_r; reflexivity
            | apply bv_unsigned_in_range | cbn; lia
            | replace (sp0 - 32 + 0) with (sp0 - 32) by lia; exact V18
            | replace (sp0 - 32 + 8) with (sp0 - 24) by lia; exact V9
            | replace (sp0 - 32 + 16) with (sp0 - 16) by lia; exact V8
            | replace (sp0 - 32 + 24) with (sp0 - 8) by lia; exact V1 ].
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Uc.
      refine (conj _ (conj _ (conj _ (Forall_nil _)))); [unfold A_G_REC, OFF_CALLS in Hclo; lia | unfold A_REC_SPILL in Hclo; lia|].
      intros o Ho. apply PRW. apply HPROG.
      apply (sr_slot_PG c); [exact Hc | unfold CALL_SIZE; lia].
  + apply pairwise_disjoint_of_extents.
    unfold sr_jregions, sr_jstack, sr_jslot, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Uc.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold A_REC_SPILL in *. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok sr_jatoms]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, Uc, USB. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hs16 : (sp0 - 32) mod 16 = 0) by (rewrite Zminus_mod, Hal; reflexivity).
    unfold A_G_REC, A_REC_SPILL, OFF_CALLS, SB in *.
    repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, sr_SHj. apply Forall_cons; [|apply Forall_nil].
  eapply (shent_ok_of_range SEGS (w_H W) memj E sr_Bxj 9 c 56 c 0 56 (sr_slot_zsh ly S W memj mdj c HAR Hc)).
  + unfold U, sr_Bxj. cbn [sv_denot]. rewrite E18, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. unfold SHADOW_OFF; lia.
  + unfold U. cbn [sv_denot]. rewrite E9, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. unfold A_G_REC, OFF_CALLS, A_REC_SPILL in *; lia.
  + lia.
  + lia.
  + intros x Hx. unfold SHADOW_OFF. cbn [Z.min Z.max] in Hx. unfold A_REC_SPILL in *. lia.
Qed.

(* ---- the read-only bytes across the walk ---- *)
(* RLO / RHI are CmdGlob's CMD_RLO / CMD_RHI; RPG and RRO are the common walk hypotheses (cmd_img_facts'
   cif_prog_not_ro and cif_relro_img) *)
Hypothesis RPG : forall a, inFP cmd_PG a -> ~ in_roP SEGS CMD_RLO CMD_RHI a.
Hypothesis RRO : forall a, CMD_RLO <= a < CMD_RHI -> in_img SEGS a.
Lemma sr_FP_pos : forall ly S W mem md O, AR SEGS B ly S W mem md -> Forall (fun pn => In pn (ablocks B ly S)) O ->
Forall (fun r => 0 < fst r) (sr_FP O).
Proof.
intros ly S W mem md O HAR HO. unfold sr_FP.
do 4 (apply Forall_cons; [cbn [fst]; unfold A_G_REC, A_REC_SPILL, OFF_NCALLS, OFF_CALLS, OFF_STATE; lia|]).
unfold ablocks_fp. apply Forall_map. eapply Forall_impl; [|exact HO]. intros [p n] Hin. cbn [fst].
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & H4096 & _). lia.
Qed.
Lemma sr_FP_cases : forall O a, inFP (sr_FP O) a -> inFP cmd_PG a \/ inFP (ablocks_fp O) a.
Proof.
intros O a (r & Hr & Ha). unfold sr_FP in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; cbn [fst snd] in Ha;
[left; apply sr_inPG; unfold OFF_NCALLS, A_G_REC in *; lia | left; apply sr_inPG; unfold OFF_CALLS, OFF_ANSWER, A_G_REC in *; lia
| left; apply sr_inPG; unfold OFF_STATE, A_G_REC in *; lia | left; apply sr_inPG; unfold SC_SIZE, A_REC_SPILL in *; lia |].
right. exists r. auto.
Qed.
Lemma sr_FP_noro : forall ly S W mem md O, AR SEGS B ly S W mem md -> Forall (fun pn => In pn (ablocks B ly S)) O ->
forall a, in_roP SEGS RLO RHI a -> ~ inFP (sr_FP O) a.
Proof.
intros ly S W mem md O HAR HO a Hro Hf.
destruct (sr_FP_cases O a Hf) as [Hpg | Hb]; [exact (RPG a Hpg Hro)|].
destruct (inFP_ablocks_fp_inv O a Hb) as (p & n & Hin & Hr).
apply (blk_img SEGS B LAWS ly S W mem md p n a HAR); [exact (proj1 (Forall_forall _ _) HO _ Hin) | exact Hr |].
destruct Hro as [(s & Hs & _ & Hr') | Hrel]; [exists s; split; [exact Hs | exact Hr'] | exact (RRO a Hrel)].
Qed.
(* arodata_okP carries over a journal of the call: a read-only byte is an image byte outside the footprint *)
Lemma sr_aro_journal : forall STK sp0 O ly S W mem md own ly' S' W' mem' md' k,
AR SEGS B ly S W mem md -> Forall (fun pn => In pn (ablocks B ly S)) O ->
ajournal SEGS B STK sp0 (sr_FP O) ly S W mem md own ly' S' W' mem' md' k ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W' mem').
Proof.
intros STK sp0 O ly S W mem md own ly' S' W' mem' md' k HAR HO HJ HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He |].
- pose proof Hro as Hro'.
  destruct Hro' as [(s & Hs & _ & Hr) | Hrel]; [exists s; split; [exact Hs | exact Hr] | exact (RRO a Hrel)].
- apply fp_spares_closed; [exact (sink_closed_pos _ (sr_FP_pos ly S W mem md O HAR HO)) | exact (sr_FP_noro ly S W mem md O HAR HO a Hro)].
Qed.

(* ---- the two walk pieces the arms compose ---- *)
(* Statement passes 4 and 5 (sup_remove_c.v): both pieces take the rounding-mode-0 premise
   after afn_pre and end in apost_baseF; neither has the astack_pres premise. *)
(* the join piece (sup_remove_j.v): from 0x8abbc to the tail jump into answer; the two checks of c and c + 4, the
   stores c->fn := REC_REMOVE and c->nargs := 0, the call arg_i(c, id), the frame's restore. TAILK is what the
   arm does at the tail jump; arg_i reaches the snprintf wrapper, so the tail jump runs at the FP state fx1 that
   arg_i returned (fxrel fx fx1, lib/A/Prog/PaFx.v). *)
Definition sr_jl_stmt : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (id : Z) (O : list (Z * Z)) kj lyj Sj Wj (regsj : bvmap 5 word) memj mdj
  (c : Z) (EV : Z) (Q : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
afn_pre SEGS B SUP_REMOVE_STK ly S W regs mem md ch ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
Z.of_nat (length (frames S)) <= 8 ->
getr regs 10 = w64 id -> -2 ^ 31 <= id < 2 ^ 31 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
Forall (fun pn => In pn (ablocks B ly S)) O ->
ajournal SEGS B SUP_REMOVE_STK (spZ regs) (sr_FP O) ly S W mem md [] lyj Sj Wj memj mdj kj ->
sr_slot c ->
spZ regsj = spZ regs - 32 -> getr regsj 8 = getr regs 10 -> getr regsj 9 = w64 c -> getr regsj 18 = w64 SB ->
getr regsj 3 = getr regs 3 -> getr regsj 4 = getr regs 4 ->
(forall r, 19 <= r <= 27 -> getr regsj (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
val_mem SEGS (mrestrict (w_H Wj) memj) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
val_mem SEGS (mrestrict (w_H Wj) memj) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
val_mem SEGS (mrestrict (w_H Wj) memj) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
val_mem SEGS (mrestrict (w_H Wj) memj) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
st_nev Sj + EV_ARG_I <= EV_MAX -> blocks_bytes Sj + LIVE_ARG_I id <= LIVE_MAX -> mo_ok MT Sj (XM_ARG_I MT id) ->
(forall (fx1 : YK11.FPState), fxrel fx fx1 -> forall lyt St Wt (regst : bvmap 5 word) memt mdt (p : Z),
  ajournal SEGS B SUP_REMOVE_STK (spZ regs) (sr_FP O) ly S W mem md [] lyt St Wt memt mdt (kj + EV_ARG_I) ->
  spZ regst = spZ regs -> getr regst 1 = getr regs 1 -> aregs_preserved regs regst ->
  getr regst 10 = w64 c -> getr regst 11 = w64 0x21ce0 -> getr regst 12 = w64 1 ->
  aval_mem (rdW Wt memt) (c + CALL_OFF_FN) 4 REC_REMOVE ->
  aval_mem (rdW Wt memt) (c + CALL_OFF_NARGS) 4 1 ->
  aval_mem (rdW Wt memt) (c + CALL_OFF_ARGS) 8 p ->
  astr_atR (rdW Wt memt) p (dec id) -> 4096 <= p ->
  Permutation (ablocks B lyt St) ((p, Z.of_nat (length (dec id)) + 1) :: ablocks B lyj Sj) ->
  Forall (fun qk => iv_apart p (Z.of_nat (length (dec id)) + 1) (fst qk) (snd qk)) (ablocks B lyj Sj) ->
  (forall a, inFP cmd_PG a -> ~ (c <= a < c + 16) -> rdW Wt memt a = rdW Wj memj a) ->
  (forall b m i, In (b, m) (ablocks B lyj Sj) -> 0 <= i < req_size m -> rdW Wt memt (b + i) = rdW Wj memj (b + i)) ->
  blocks_bytes St <= blocks_bytes Sj + LIVE_ARG_I id ->
  mo_le MT Sj St (XM_ARG_I MT id) ->
  SRr SEGS Wt (mkCfg (@mkst fx1 regst (Z_to_bv 64 (SIGMA CS_answer)) memt (seg_rom SEGS)) mdt)
    (apost_baseF (fx := fx) SEGS B SUP_REMOVE_STK (sr_FP O) regs ly S W mem md EV Q)) ->
SRr SEGS Wj (mkCfg (mkst regsj (Z_to_bv 64 (BASE + (AF_sup_remove + SR_J))) memj (seg_rom SEGS)) mdj)
  (apost_baseF SEGS B SUP_REMOVE_STK (sr_FP O) regs ly S W mem md EV Q).
(* the tail piece (sup_remove_t.v): answer's statement at the tail jump, composed into sup_remove's journal *)
Definition sr_tail_stmt : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (id : Z) (R : rstate) (O : list (Z * Z))
  lyt St Wt (regst : bvmap 5 word) memt mdt (kt : Z) (Ot : list (Z * Z)) (c old acc : Z),
let t := snd (sup_remove_m R id) in
let R1 := rec_record R REC_REMOVE [dec id] in
afn_pre SEGS B SUP_REMOVE_STK ly S W regs mem md ch ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
Z.of_nat (length (frames S)) <= 8 ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
Forall (fun pn => In pn (ablocks B ly S)) O ->
ajournal SEGS B SUP_REMOVE_STK (spZ regs) (sr_FP O) ly S W mem md [] lyt St Wt memt mdt kt ->
spZ regst = spZ regs -> getr regst 1 = getr regs 1 -> aregs_preserved regs regst ->
getr regst 10 = w64 c -> getr regst 11 = w64 0x21ce0 -> getr regst 12 = w64 1 ->
rec_repA B lyt St (rdW Wt memt) R1 Ot ->
aval_mem (rdW Wt memt) (A_G_REC + OFF_ANSWER) 8 old -> 0 <= old < 2 ^ 64 ->
(forall pn, In pn Ot -> fst pn = old -> In pn O) ->
((exists k, nth_error (r_calls R1) k = Some (REC_REMOVE, [dec id]) /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat k) \/
 (c = A_REC_SPILL /\ (REC_REMOVE, [dec id]) = r_spill R1)) ->
0 <= kt -> kt + EV_ANSWER <= EV_SUP_REMOVE R ->
st_nev S + EV_SUP_REMOVE R <= EV_MAX ->
blocks_bytes St + LIVE_ANSWER t <= LIVE_MAX ->
mo_ok MT S (XM_SUP_REMOVE MT R id t) -> mo_le MT S St acc -> acc + XM_ANSWER MT t <= XM_SUP_REMOVE MT R id t ->
SRr SEGS Wt (mkCfg (mkst regst (Z_to_bv 64 (SIGMA CS_answer)) memt (seg_rom SEGS)) mdt)
 (apost_baseF SEGS B SUP_REMOVE_STK (sr_FP O) regs ly S W mem md (EV_SUP_REMOVE R)
  (fun ly' S' W' regs' mem' md' => exists p1 p2 O',
    let n := Z.of_nat (length t) + 1 in
    getr regs' 10 = w64 p2 /\ 4096 <= p2 < 2 ^ 64 /\ p1 <> p2 /\
    (forall pn, In pn (ablocks B lyt St) -> fst pn <> old -> pn <> (p1, n) /\ pn <> (p2, n)) /\
    (forall pn, In pn (ablocks B ly' S') <-> (In pn (ablocks B lyt St) /\ fst pn <> old) \/ pn = (p1, n) \/ pn = (p2, n)) /\
    rec_repA B ly' S' (rdW W' mem') (fst (sup_remove_m R id)) O' /\
    (forall pn, In pn O' <-> (In pn Ot /\ fst pn <> old) \/ pn = (p1, n)) /\
    astr_atR (rdW W' mem') p2 t /\
    blocks_bytes S' <= blocks_bytes St + LIVE_ANSWER t /\
    mo_le MT S S' (XM_SUP_REMOVE MT R id t))).
End c.
End b.
End a.
