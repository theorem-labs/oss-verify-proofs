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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/sup_pool_config.v, with its module paths, module names and numbers changed; 189 of its 252 lines of code are new or changed and 2001 lines of the source are left out. *)
(* sup_remove_all's walk on the ASan build of plugin-hostd/fuzz_command, the symbolic entry state and the small
   steps the walk takes beside the executor.

   The entry state (0x8ac44): every register is its own atom; atom 32 is the shadow base (0x7fff8000, the value
   of the cell 0xb10b8 that the GOT word 0xa63f0 points at); atom 33 is g_rec.ncalls (n, 0 .. 16), read by `lw
   a1, 8(a0)`; atom 34 is the call slot record() fills: g_rec + 16 + 56 n while n < 16, record.spill when the
   table is full. The regions: the 32-byte frame, the GOT word and the shadow-base cell (read-only), g_rec's
   ncalls cell (written on the append arm) and the slot's first 8 bytes (fn and nargs, written on both arms).
   The executor's state at 0x8aca8 computes the slot as g_rec + (n * 56 + 16); the walk pins s0 to atom 34 there
   (sra_pin_append) so that the two inline checks see the slot as one shadow entry, mkSHE 34 0 16. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaLibF.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdAddr CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c answer_c sup_remove_all_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecBase CmdRecCells.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition sra_SB : Z := 0x7fff8000.
Definition sra_Bx : sv := SOff 32 0.
Definition sra_Bspan : Z * Z := (sra_SB, sra_SB + 2 ^ 44 - 1).
(* g_rec.ncalls: 4 bytes at g_rec + 8, the atom n *)
Definition sra_ncalls_region : YP09.region :=
YP09.mkRegion (Some (A_OBJ 44)) 8 12 8 12 [YP09.mkChunk 8 (CVal 4 (SOff 33 0))].
(* the slot's fn and nargs: 8 bytes at atom 34, written; added once s0 is the slot (sra_add_slot), so that the
   runs before it keep every byte of the slot *)
Definition sra_slot_region : YP09.region := YP09.mkRegion (Some 34%nat) 0 8 0 8 [].
Definition sra_regions : smem := [ stack_region 32; got_regionP; bcell_regionP 32; sra_ncalls_region ].
Definition sra_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF sra_SB sra_SB 0); (33%nat, mkAF 0 16 0);
  (34%nat, mkAF 0x10000 0x606000 3); (A_OBJ 44, mkAF 0x10000 0x606000 3) ] [] [].
Definition ss_sra : sstate := mkSS AF_sup_remove_all sr_atoms sra_regions None sra_facts.
Definition sra_SH0 : list shent := [].
Definition sra_SH : list shent := [mkSHE 34 0 16].
Definition sra_slot (n : Z) : Z := if n <? 16 then A_G_REC + OFF_CALLS + CALL_SIZE * n else A_REC_SPILL.
Definition sra_extra (n : Z) : list word := map (Z_to_bv 64) [sra_SB; n; sra_slot n].
(* the s0 the executor computes at 0x8aca8 on the append arm *)
Definition sra_s0_append : sv := SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 33 0) (SLit 56)) (SLit 16)) (SOff (A_OBJ 44) 0).

Lemma sra_slot_range : forall n, 0 <= n <= 16 ->
  sra_slot n mod 8 = 0 /\ inFP cmd_PG (sra_slot n) /\
  (forall i, 0 <= i < 16 -> inFP cmd_PG (sra_slot n + i)) /\
  0x10000 <= sra_slot n /\ sra_slot n + 16 <= 0x606000 /\
  ((n < 16 /\ sra_slot n = A_G_REC + OFF_CALLS + CALL_SIZE * n) \/ (n = 16 /\ sra_slot n = A_REC_SPILL)).
Proof.
intros n Hn. unfold sra_slot. destruct (Z.ltb_spec n 16) as [Hl|Hl].
- unfold A_G_REC, OFF_CALLS, CALL_SIZE, cmd_PG, inFP.
  split; [replace (6174528 + 16 + 56 * n) with ((771818 + 7 * n) * 8) by lia; apply Z_mod_mult|].
  split; [exists (6174528, 6174528 + 960); split; [left; reflexivity | cbn [fst snd]; lia]|].
  split; [intros i Hi; exists (6174528, 6174528 + 960); split; [left; reflexivity | cbn [fst snd]; lia]|].
  split; [lia|]. split; [lia|]. left. split; [lia | reflexivity].
- unfold A_REC_SPILL, cmd_PG, inFP.
  split; [reflexivity|].
  split; [exists (0x5e3be0, 0x5e3be0 + 56); split; [right; left; reflexivity | cbn [fst snd]; lia]|].
  split; [intros i Hi; exists (0x5e3be0, 0x5e3be0 + 56); split; [right; left; reflexivity | cbn [fst snd]; lia]|].
  split; [lia|]. split; [lia|]. right. split; [lia | reflexivity].
Qed.

Lemma aval_mem_of_val_mem : forall segs H mem a n v,
  val_mem segs (mrestrict H mem) a n v -> aval_mem (aview segs H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small.
unfold le_byte. apply Z.mod_pos_bound. lia.
Qed.

(* the denotation of the executor's s0 at 0x8aca8 on the append arm *)
Lemma sra_pin_append : forall E n, ew E 33 = Z_to_bv 64 n -> 0 <= n < 16 ->
  ew E (A_OBJ 44) = Z_to_bv 64 A_G_REC ->
  sv_denot E sra_s0_append = Z_to_bv 64 (A_G_REC + OFF_CALLS + CALL_SIZE * n).
Proof.
intros E n H33 Hn H44. rewrite denot_lit_U. f_equal. unfold sra_s0_append.
rewrite U_SAlu, U_SAlu, U_SMd.
rewrite (U_atom E 33 n H33) by lia. rewrite (U_atom E (A_OBJ 44) A_G_REC H44) by (unfold A_G_REC; lia).
rewrite !U_SLit. rewrite (zcanon_id 56) by (unfold M64; lia). rewrite (zcanon_id 16) by (unfold M64; lia).
cbn [zalu_raw zmd_raw]. cbv zeta.
rewrite (zcanon_id (n * 56)) by (unfold M64; lia). rewrite (zcanon_id (n * 56 + 16)) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64, A_G_REC; lia). unfold A_G_REC, OFF_CALLS, CALL_SIZE. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition sra_E (regs : bvmap 5 word) (n : Z) : env := Eimg (Ereg regs (sra_extra n)).

(* a register's symbolic value replaced by another of the same denotation *)
Lemma st_ok_pi_set_reg : forall E ss ms (r : bv 5) e,
st_ok_pi SEGS VAL E ss ms -> sv_denot E e = sv_denot E (sr_get (ss_regs ss) r) -> bv_eqb r 0 = false ->
st_ok_pi SEGS VAL E (mkSST (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e HS He Hr0. unfold st_ok_pi, abs_ss, setpc in *. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
apply (st_ok_regs SEGS E (mkSST (VAL A_TEXT + ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms
(sr_set (ss_regs ss) r e) HS).
intros rr. cbn [ss_regs]. destruct (decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. rewrite He. reflexivity.
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.

Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HB : CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis VOBJS : cmd_val_objs.
(* the statics are writable (the core's prog_rw, YCbq.v; the walk hypothesis PRW; CmdRecCells' PROG_WRITABLE
   gives writable_at for every byte of cmd_PG) and the image facts (IMG, CmdRecBase's cmd_img_facts) *)
Hypothesis PRW : prog_rw SEGS B.
Hypothesis IMG : CmdRecBase.cmd_img_facts SEGS B.

(* the program's statics are as_prog_static B (CmdBSyms' ts_prog) *)
Lemma HPROG : forall a, inFP cmd_PG a -> Exists (in_zr a) (as_prog_static B).
Proof.
intros a (r & Hr & Ha). rewrite (ts_prog B HB). unfold TFIB_PROG_STATIC. unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hr.
cbn [In] in Hr. apply Exists_exists.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha;
[exists (0x5e3740, 960) | exists (0x5e3be0, 56) | exists (0x5e3c60, 4)];
(split; [cbn [In]; tauto | unfold in_zr; cbn [fst snd]; lia]).
Qed.

Lemma awr_ok_cons_prog : forall E r rs STK sp0 FP bl0 blc fr0 ly own n b,
YP09.r_base r = Some n -> bv_unsigned (ew E n) = b ->
(forall a, b + YP09.r_wlo r <= a < b + YP09.r_whi r -> inFP FP a /\ inFP cmd_PG a) ->
awr_ok SEGS B E rs STK sp0 FP bl0 blc fr0 ly own -> awr_ok SEGS B E (r :: rs) STK sp0 FP bl0 blc fr0 ly own.
Proof.
intros E r rs STK sp0 FP bl0 blc fr0 ly own n b Hb Hn Hw H a (r' & [<-|Hin] & Ha).
- rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hn in Ha. destruct (Hw a Ha) as [Hf Hp].
  right; right; right; right. left. split; [exact Hf|]. split; [exact (HPROG a Hp) | exact (CmdRecBase.cif_prog_img _ _ IMG a Hp)].
- apply H. exists r'. auto.
Qed.

Lemma sra_inzsh : forall lo n, existsb (fun r => (fst r =? lo) && (snd r =? n)) Tfib_zero_shadow = true ->
  In (lo, n) Tfib_zero_shadow.
Proof.
intros lo n H. apply existsb_exists in H as ([l k] & Hin & E). apply andb_true_iff in E as [E1 E2].
apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. cbn [fst snd] in E1, E2. subst. exact Hin.
Qed.

(* the slot's 16 bytes are addressable at every state of the record *)
Lemma sra_slot_addressable : forall ly S (W : world SEGS) mem md n, AR SEGS B ly S W mem md -> 0 <= n <= 16 ->
  range_addressable (rdW W mem) SHADOW_OFF (sra_slot n) 16.
Proof.
intros ly S W mem md n HAR Hn. unfold sra_slot. destruct (Z.ltb_spec n 16) as [Hl|Hl].
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0xada00, 0x536100)); cbn [fst snd];
  [exact HAR | apply sra_inzsh; vm_compute; reflexivity | reflexivity | reflexivity | unfold A_G_REC, OFF_CALLS, CALL_SIZE; lia
  | unfold A_G_REC, OFF_CALLS, CALL_SIZE; lia].
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0x5e3be0, 0x38)); cbn [fst snd];
  [exact HAR | apply sra_inzsh; vm_compute; reflexivity | reflexivity | reflexivity | unfold A_REC_SPILL; lia
  | unfold A_REC_SPILL; lia].
Qed.

(* the shadow entry of the slot, at any state where atom 34 is the slot and atom 32 the shadow base *)
Lemma sra_shok : forall ly S (W : world SEGS) mem md E n, AR SEGS B ly S W mem md -> 0 <= n <= 16 ->
  ew E 32 = Z_to_bv 64 sra_SB -> ew E 34 = Z_to_bv 64 (sra_slot n) ->
  sh_ok SEGS sra_Bx sra_SH E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E n HAR Hn E32 E34. pose proof (sra_slot_range n Hn) as (_ & _ & _ & Hs0 & Hs1 & _).
unfold sh_ok, sra_SH. apply Forall_cons; [|apply Forall_nil].
apply (shent_ok_of_range SEGS (w_H W) mem E sra_Bx 34 (sra_slot n) 16 (sra_slot n) 0 16).
- exact (sra_slot_addressable ly S W mem md n HAR Hn).
- unfold sra_Bx. rewrite (U_atom E 32 sra_SB E32) by (unfold sra_SB; lia). reflexivity.
- apply (U_atom E 34 (sra_slot n) E34). lia.
- lia. - lia.
- intros x Hx. unfold SHADOW_OFF. lia.
Qed.

(* the symbolic entry state *)
Lemma sra_entry : forall W ly S regs mem md ch n,
afn_pre SEGS B SUP_REMOVE_ALL_STK ly S W regs mem md ch ->
0 <= n <= 16 ->
aval_mem (rdW W mem) (A_G_REC + OFF_NCALLS) 4 n ->
st_ok_pi SEGS VAL (sra_E regs n) ss_sra
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_remove_all)) mem (seg_rom SEGS))) /\
sh_ok SEGS sra_Bx sra_SH0 (sra_E regs n) (mrestrict (w_H W) mem).
Proof.
intros W ly S regs mem md ch n HPRE Hn Hnc.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : SUP_REMOVE_ALL_STK = ltac:(let v := eval vm_compute in SUP_REMOVE_ALL_STK in exact v)) by reflexivity.
pose proof (sra_slot_range n Hn) as (Hc8 & HcPG & HcPG16 & Hc0 & Hc1 & _).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
assert (V0 : VAL (A_OBJ 0) = 0xa63f0) by (rewrite (VOBJS 0%nat ltac:(vm_compute; lia)); reflexivity).
assert (V12 : VAL (A_OBJ 12) = 0xb10b8) by (rewrite (VOBJS 12%nat ltac:(vm_compute; lia)); reflexivity).
assert (V44 : VAL (A_OBJ 44) = A_G_REC) by (rewrite (VOBJS 44%nat ltac:(vm_compute; lia)); reflexivity).
rewrite V0, V12 in Kgot. rewrite V12 in Kcell.
split; [|unfold sh_ok, sra_SH0; apply Forall_nil].
rewrite restrict_mkst_fx.
set (E := sra_E regs n).
assert (E2 : ew E 2 = getr regs 2) by (subst E; unfold sra_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 sra_SB) by (subst E; unfold sra_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 n) by (subst E; unfold sra_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (sra_slot n)) by (subst E; unfold sra_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 0xa63f0) by (subst E; unfold sra_E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V0; reflexivity).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 0xb10b8) by (subst E; unfold sra_E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V12; reflexivity).
assert (E285 : ew E (A_OBJ 44) = Z_to_bv 64 A_G_REC) by (subst E; unfold sra_E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V44; reflexivity).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
{ intros k v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
unfold ss_sra. apply pa_entry_st_ok_full.
- subst E. unfold sra_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold sra_regions, stack_region, got_regionP, bcell_regionP, sra_ncalls_region.
  repeat apply Forall_cons; try apply Forall_nil.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
    split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (VB (A_OBJ 0) 0xa63f0 E241) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ 0xa63f0 0 8 (SOff (A_OBJ 12) 0) 0xb10b8);
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (VB (A_OBJ 12) 0xb10b8 E253) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ 0xb10b8 0 8 (SOff 32 0) sra_SB);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold sra_SB; lia | lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (VB (A_OBJ 44) A_G_REC E285) by (unfold A_G_REC; lia). split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|].
    split.
    * intros o Ho. apply (CmdRecCells.PROG_WRITABLE SEGS B LAWS HB PRW).
      exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold A_G_REC; lia].
    * constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ A_G_REC 8 4 (SOff 33 0) n);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
      exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Hnc).
- apply pairwise_disjoint_of_extents.
  unfold sra_regions, stack_region, got_regionP, bcell_regionP, sra_ncalls_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) 0xa63f0 E241) by lia. rewrite (VB (A_OBJ 12) 0xb10b8 E253) by lia.
  rewrite (VB (A_OBJ 44) A_G_REC E285) by (unfold A_G_REC; lia).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold A_G_REC, OFF_NCALLS in *.
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok sra_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32, E33, E34, E285.
  rewrite !unsigned_lit_small by (unfold sra_SB, A_G_REC in *; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; unfold sra_SB, A_G_REC; first [exact I | lia | reflexivity].
Qed.
(* the slot's region, added at a state where atom 34 is the slot *)
Lemma sra_add_slot : forall (W : world SEGS) E ss ms ly S md n,
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
  AR SEGS B ly S W (ms_mem ms) md -> 0 <= n <= 16 -> ew E 34 = Z_to_bv 64 (sra_slot n) ->
  all_disjoint E sra_slot_region (ss_mem ss) ->
  st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) (sra_slot_region :: ss_mem ss) (ss_resv ss) (ss_facts ss))
    (restrict (w_H W) ms).
Proof.
intros W E ss ms ly S md n HS HAR Hn E34 Hd.
pose proof (sra_slot_range n Hn) as (_ & _ & HcPG16 & Hc0 & Hc1 & _).
apply st_ok_pi_add_region; [exact HS | reflexivity | | exact Hd].
unfold region_ok, sra_slot_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E34, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. cbn [ms_mem restrict]. apply (CmdRecCells.PROG_WRITABLE SEGS B LAWS HB PRW).
apply HcPG16. lia.
Qed.
End e.
End f.
End d.
