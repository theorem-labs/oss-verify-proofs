(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: the entry segment of the image-A walk of reac-repacer/fuzz_uci's LLVMFuzzerTestOneInput, in the form of proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v (en_entry, the run of the prologue by the Pa engine, reg_at / saved_tac) and LLVMFuzzerTestOneInput_seg_early.v (the input byte checked by the token rule, the branch on the size test): fuzz_uci.asan's prologue, its two shadow-checked loads and its first cut point. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of reac-repacer/fuzz_wire's LLVMFuzzerTestOneInput (u_entry_stmt of lib/A/Prog/LLVMFuzzerTestOneInput_segs.v), at this unit's modules and image A's Pa kit (lib/A/Prog/WirePPa.v, WirePPaLib.v, WirePPaImg.v, LLVMFuzzerTestOneInput_seg_lib.v): fuzz_wire.asan's prologue, its size refusal, data[0]'s shadow-checked load, the malloc of f by the statement's amalloc04_rule and __asan_memcpy (f, data + 1, fn) by its aintrin_realizes, the two calls in the form of libreac/fuzz_decode's released lib/A/Prog/LLVMFuzzerTestOneInput_seg_early.v (e_call) and LLVMFuzzerTestOneInput_seg_copy.v (cp_call_memcpy). *)
(* LLVMFuzzerTestOneInput_seg_entry: u_entry_ok : u_entry_stmt (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v), the entry
   segment of the image-B walk of fuzz_wire.asan-ubsan's LLVMFuzzerTestOneInput, in the form of the image-A walk's
   lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v at image B's listing, offsets and modules (every value re-measured on
   the asan-ubsan pin).

   The run, offsets from the entry 0x7fbf8 of fuzz_wire.asan-ubsan (listing lib/B/Prog/WirePList.v):
   - +0x000 .. +0x030 by the Pa engine from the slot pre: the frame (addi sp, sp, -0x40), the eight saves,
     a3 = size - 2 ^ 26, a2 = 1 - 2 ^ 26 (mod 2 ^ 64) and `bltu a3, a2`; under the slot pre (size < 2 ^ 26) it is
     taken exactly when size = 0 (en_size_test), and then +0x160 is reached with no event (en_close_ret);
   - size > 0, +0x034 .. +0x06c: s4 = data, the UBSan check data = NULL (decided by the pointer fact of atom 10),
     the shadow base out of its GOT word (object 0 -> object 12 -> atom 32), data[0]'s shadow check (the token rule;
     the obligation is discharged by the input block, lib/B/YCbq.v obl_of_block), the UBSan wrap check of data + 1
     (decided by the same fact), s6 = s1 = size - 1, a0 = 1600 and `bltu s6, a0` (en_clamp_test);
   - either arm up to the malloc of f (+0x084): s1 = fn, s2 = data[0] (the input byte's region, atom 33), s3 = a0 = fsz;
   - from the call on, en_after: malloc (fsz) by the statement's amalloc04_rule (lib/B/YC5d.v; s0 is the caller's,
     whose chain the slot gives as empty, so the trace is [pc0; +0x088] of wire_llvmf_ufix; st_depot <> [] by
     lib/B/Prog/WireCg.v wire_depot_of_block);
   - +0x088 .. +0x09c by the Pa engine from a fresh state (en_e88): `beqz a0` (refuted: 4096 <= f), s0 = f,
     s5 = data[0] & 1, s2 = (data[0] >> 1) - 2, `beqz s6`: size = 1 reaches +0x0b0 at once (fn = 0); otherwise
     __asan_memcpy (f, data + 1, fn) by the statement's aintrin_realizes (lib/B/YCbq.v aj_intrin_at) returns to +0x0b0;
   - +0x0b0, the head of turn_a, by en_close_oh. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0s.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YCbq YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YM05 YE00 YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YE01 YImgTop.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI16.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YB1v YCfn.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require YE2k AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import PaJournal
  WirePSyms WirePList WirePAddr WirePPa WirePPaLib WirePImg WireCg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import LLVMFuzzerTestOneInput_cg
  LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_seg_lib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable.YK11.
Module WCells := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.AsanCells.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ------------------------------------------------------------------ *)
(* 1. The symbolic states                                               *)
(* ------------------------------------------------------------------ *)

(* At +0x000. Atoms: registers 0 .. 31 (Ereg), 32 the shadow base, 33 data[0] (0 when n = 0). Regions: the 0x40 bytes
   below the entry sp (atom 2), written; the GOT word of the shadow base (object 0) and the shadow-base cell
   (object 12). *)
Definition en_regions : smem := [stack_region U_FRAME; got_regionP; bcell_regionP 32].
Definition en_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SBv SBv 0); (10%nat, PTR 0);
           (11%nat, mkAF 0 (2 ^ 26 - 1) 0); (33%nat, mkAF 0 255 0)] [] [].
Definition ss_en : sstate := mkSS AF_LLVMFuzzerTestOneInput sr_atoms en_regions None en_facts.
Definition en_extra (d0 : Z) : list word := [Z_to_bv 64 SBv; Z_to_bv 64 d0].
(* At +0x088, the return of the malloc of f: every register its own atom, 32 the shadow base, no region. *)
Definition ss_88 : sstate := mkSS 0x88 sr_atoms [] None (mkFacts [(32%nat, mkAF SBv SBv 0)] [] []).
(* The stack region as the prologue leaves it: the eight saved words, each the entry value of its register. *)
Definition en_saved : list YP09.chunk :=
  [YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
   YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
   YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
   YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].

(* Values of symbolic expressions. *)
Lemma en_bv_small : forall v, 0 <= v < 2 ^ 64 -> bv_unsigned (w64 v) = v.
Proof. intros v Hv. unfold w64. rewrite unsigned_lit_small by exact Hv. reflexivity. Qed.
Lemma en_reg_val : forall E e v, U E e mod 2 ^ 64 = v mod 2 ^ 64 -> sv_denot E e = w64 v.
Proof.
intros E e v H. rewrite denot_lit_U. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). exact H.
Qed.
Lemma en_v_reg : forall E n (w : word), ew E n = w -> sv_denot E (SOff n 0) = w.
Proof. intros E n w H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma en_v_off : forall E n c v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n c) = w64 (v + c).
Proof.
intros E n c v Hn Hv. apply en_reg_val. rewrite U_SOff, Hn, unsigned_lit_small by exact Hv.
unfold zcanon, M64. apply Z.mod_mod. lia.
Qed.
Lemma en_v_lit : forall E z, sv_denot E (SLit z) = w64 z.
Proof. reflexivity. Qed.
Lemma en_sp_val : forall E (regs : bvmap 5 word) c, ew E 2 = getr regs 2 -> 0 <= spZ regs + c < 2 ^ 64 ->
  bv_unsigned (sv_denot E (SOff 2 c)) = spZ regs + c.
Proof. intros E regs c H Hr. cbn [sv_denot]. rewrite H. unfold spZ in *. rewrite unsigned_lit_small by exact Hr. reflexivity. Qed.
(* `bltu a3, a2` at +0x030: a3 = n - 2 ^ 26 and a2 = 1 - 2 ^ 26, both mod 2 ^ 64. *)
Lemma en_size_test : forall E n, ew E 11 = Z_to_bv 64 n -> 0 <= n < 2 ^ 26 ->
  branch_taken BC_LTU (sv_denot E (SOff 11 (-67108864))) (sv_denot E (SLit 18446744073642442753)) = (n =? 0).
Proof.
intros E n Hn Hr. rewrite branch_ltu_U, U_SOff, U_SLit, Hn, unsigned_lit_small by lia. unfold zcanon, M64.
destruct (Z.eqb_spec n 0) as [->|Hne]; [vm_compute; reflexivity|].
apply Z.ltb_ge. rewrite (Z.mod_small 18446744073642442753) by lia.
rewrite <- (Z.mod_add (n + -67108864) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
(* `bltu s6, a0` at +0x06c: s6 = n - 1, a0 = 1600. *)
Lemma en_clamp_test : forall E n, ew E 11 = Z_to_bv 64 n -> 1 <= n < 2 ^ 26 ->
  branch_taken BC_LTU (sv_denot E (SOff 11 (-1))) (sv_denot E (SLit 1600)) = (n - 1 <? 1600).
Proof.
intros E n Hn Hr. rewrite branch_ltu_U, U_SOff, U_SLit, Hn, unsigned_lit_small by lia.
rewrite !zcanon_id by (unfold M64; lia). reflexivity.
Qed.
(* s3 = fn + (fn == 0) (+0x078, +0x07c), when fn = n - 1; and a0 = s3 + 0 (+0x080). *)
Lemma en_v_fsz : forall E n, ew E 11 = Z_to_bv 64 n -> 1 <= n <= 1601 ->
  sv_denot E (SAlu ALU_ADD (SOff 11 (-1)) (SAlu ALU_SLTU (SOff 11 (-1)) (SLit 1))) = w64 (Z.max (Z.min (n - 1) 1600) 1).
Proof.
intros E n Hn Hr. apply en_reg_val. rewrite !U_SAlu, !U_SOff, U_SLit, Hn, unsigned_lit_small by lia. cbn [zalu_raw].
unfold zcanon, M64. rewrite (Z.mod_small (n + -1)), (Z.mod_small 1) by lia.
destruct (Z.ltb_spec (n + -1) 1); rewrite ?(Z.mod_small 0), ?(Z.mod_small 1) by lia;
  rewrite Z.mod_mod by lia; f_equal; lia.
Qed.
Lemma en_v_fsz0 : forall E n, ew E 11 = Z_to_bv 64 n -> 1 <= n <= 1601 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 11 (-1)) (SAlu ALU_SLTU (SOff 11 (-1)) (SLit 1))) (SLit 0)) =
  w64 (Z.max (Z.min (n - 1) 1600) 1).
Proof.
intros E n Hn Hr. rewrite <- (en_v_fsz E n Hn Hr). rewrite !denot_lit_U. f_equal.
rewrite U_SAlu, U_SLit. cbn [zalu_raw]. change (zcanon 0) with 0. rewrite Z.add_0_r. apply zcanon_id. apply U_range.
Qed.
(* s2 = (data[0] >> 1) - 2 (+0x090, +0x098) and s5 = data[0] & 1 (+0x094). *)
Lemma en_v_slot : forall E d, ew E 18 = Z_to_bv 64 d -> 0 <= d < 256 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 1)) (SLit (-2))) = w64 (Z.shiftr d 1 - 2).
Proof.
intros E d Hd Hr. apply en_reg_val. rewrite !U_SAlu, U_SOff, !U_SLit, Hd, unsigned_lit_small by lia.
cbn [zalu_raw]. change (Z.land (zcanon 1) 63) with 1. rewrite Z.add_0_r, (zcanon_id d) by (unfold M64; lia).
unfold zcanon, M64. rewrite Z.mod_mod by lia. rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r. f_equal; lia.
Qed.
Lemma en_v_bc : forall E d, ew E 18 = Z_to_bv 64 d -> 0 <= d < 256 ->
  sv_denot E (SAlu ALU_AND (SOff 18 0) (SLit 1)) = w64 (Z.land d 1).
Proof.
intros E d Hd Hr. apply en_reg_val. rewrite U_and_lit by lia. rewrite (U_atom E 18 d Hd) by lia. reflexivity.
Qed.

(* Lists: f's bytes are data[1 .. fn]. *)
Lemma en_map_firstn : forall (A C : Type) (f : A -> C) k l, map f (firstn k l) = firstn k (map f l).
Proof. intros A C f k. induction k as [|k IH]; intros l; destruct l; cbn; [reflexivity..| f_equal; apply IH]. Qed.
Lemma en_nth_firstn : forall (l : list Z) k j, (j < k)%nat -> nth j (firstn k l) 0 = nth j l 0.
Proof.
intros l. induction l as [|x l IH]; intros k j Hj; [rewrite firstn_nil; destruct j; reflexivity|].
destruct k as [|k]; [lia|]. destruct j as [|j]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
Lemma en_fb_nth : forall cx j, (Z.of_nat j < u_fn cx) ->
  nth j (map (fun b : byte => bv_unsigned b) (u_fb cx)) 0 = nth (S j) (map (fun b : byte => bv_unsigned b) (u_pl cx)) 0.
Proof.
intros cx j Hj. unfold u_fb. rewrite en_map_firstn, en_nth_firstn by lia.
destruct (u_pl cx) as [|b l]; [destruct j; reflexivity|]. reflexivity.
Qed.

(* The allocator's trace at a call with an empty frame-pointer chain is WireCg.v's wire_utrace of the return
   address (lib/B/YCbq.v call_trace0). *)
Lemma en_trace0 : forall pc0 regs, call_trace0 pc0 regs [] = wire_utrace pc0 [raZ regs].
Proof.
intros pc0 regs. rewrite call_trace_nil. unfold wire_utrace. cbn [flat_map].
destruct (raZ regs =? pc0); reflexivity.
Qed.

Section en. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation SEGS := (@pa_segs _ wire_listing PI_wire).
Local Abbreviation VAL := (@pa_val _ wire_listing PI_wire).
Local Abbreviation BASE := (@pa_val _ wire_listing PI_wire A_TEXT).
Definition EEN (regs : bvmap 5 word) (d0 : Z) : env := Eimg (PI := PI_wire) (Ereg regs (en_extra d0)).
Definition E88 (regs : bvmap 5 word) : env := Eimg (PI := PI_wire) (Ereg regs [Z_to_bv 64 SBv]).
Lemma en_vals : VAL (A_OBJ 0) = WCells.GOT_CELL_K /\ VAL (A_OBJ 12) = WCells.CELL_K.
Proof. vm_compute. split; reflexivity. Qed.

Lemma en_entry : forall (B : asyms) ly S (W : world SEGS) (regs : bvmap 5 word) mem md (p n d0 : Z),
  AR SEGS B ly S W mem md -> wire_cells B ->
  (forall a, spZ regs - U_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  getr regs 10 = w64 p -> getr regs 11 = w64 n -> 4096 <= p <= 140737479966720 -> 0 <= n < 2 ^ 26 -> 0 <= d0 < 256 ->
  st_ok_pi SEGS VAL (EEN regs d0) ss_en
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_LLVMFuzzerTestOneInput)) mem (seg_rom SEGS))).
Proof.
intros B ly S W regs mem md p n d0 HAR HCELLS Hpres Hsp Hsp16 R10 R11 Hp Hn Hd0.
destruct (HCELLS ly) as (I1 & I2 & _).
assert (CH : forall c, In c (as_const B ly) -> cell_holds B ly (aview SEGS (w_H W) mem) c).
{ intros c Hc. destruct HAR as (Mx & _). exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) c Hc). }
assert (Kcell : rdword (aview SEGS (w_H W) mem) WCells.CELL_K = Some WCells.ASAN_K)
  by (apply (rdword_cell B ly); [unfold WCells.ASAN_K; lia | exact (CH _ I1)]).
assert (Kgot : rdword (aview SEGS (w_H W) mem) WCells.GOT_CELL_K = Some WCells.CELL_K)
  by (apply (rdword_cell B ly); [unfold WCells.CELL_K; lia | exact (CH _ I2)]).
destruct en_vals as (V0 & V12).
rewrite restrict_mkst_fx. unfold ss_en.
set (E := EEN regs d0).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (en_extra d0)) n)
  by (intros nn Hnn; unfold E, EEN; apply Eimg_low; exact Hnn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E11 : ew E 11 = getr regs 11) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SBv) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 d0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (EO : forall i, (i < 14)%nat -> ew E (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)))
  by (intros i Hi; unfold E, EEN; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (EO 0%nat ltac:(lia)) as EO0. pose proof (EO 12%nat ltac:(lia)) as EO12.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
  by (intros nn v0 Hnn Hv0; cbn [base_val]; rewrite Hnn; apply unsigned_lit_small; exact Hv0).
assert (R0 : 0 <= VAL (A_OBJ 0) < 2 ^ 47) by (rewrite V0; unfold WCells.GOT_CELL_K; lia).
assert (R12 : 0 <= VAL (A_OBJ 12) < 2 ^ 47) by (rewrite V12; unfold WCells.CELL_K; lia).
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold en_regions, stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. unfold U_FRAME in *. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold U_FRAME in *. lia.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite EO12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r, V0, V12. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO12) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SBv);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SBv; zside | zside |].
    rewrite Z.add_0_r, V12. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
- apply pairwise_disjoint_of_extents.
  unfold en_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0), (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO12) by lia.
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  rewrite V0, V12. unfold WCells.GOT_CELL_K, WCells.CELL_K, U_FRAME.
  repeat split; first [exact I | lia].
- split; [|split; [exact I | exact I]].
  cbn [en_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32, E33, E10, E11, R10, R11.
  rewrite !unsigned_lit_small by (unfold SBv; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SBv in *; first [lia | reflexivity].
Qed.

(* The state at +0x088: every register its entry value, no region. *)
Lemma en_e88 : forall (regs : bvmap 5 word) mem H,
  st_ok_pi SEGS VAL (E88 regs) ss_88 (restrict H (mkst regs (Z_to_bv 64 (BASE + 0x88)) mem (seg_rom SEGS))).
Proof.
intros regs mem H. rewrite restrict_mkst_fx. unfold ss_88.
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  assert (E32 : ew (E88 regs) 32 = Z_to_bv 64 SBv)
    by (unfold E88; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  rewrite E32, unsigned_lit_small by (unfold SBv; lia). rewrite Z.pow_0_r, Z.mod_1_r. unfold SBv. lia.
Qed.
End en.

(* ------------------------------------------------------------------ *)
(* 2. Tactics                                                           *)
(* ------------------------------------------------------------------ *)

(* The write rights of a run: the stack region (atom 2 = the entry sp) in the entry's stack window, every other
   region read only. *)
Ltac en_awr Usp Hstkv :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0);
    [reflexivity | rewrite ?ew_ewset_other by lia; rewrite Usp; lia | cbn; rewrite Hstkv; lia | cbn; lia |] ].
(* ... of a run from a state with no region. *)
Ltac en_awr0 :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_nil.
(* The model after a run, named and opaque. *)
Ltac en_md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
    let md2 := fresh "md" in set (md2 := mdx) in *; clearbody md2 end.
Ltac en_norm HS :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?ms => let v := eval vm_compute in ss in change ss with v in HS end.
(* The symbolic value of register r in the machine state of HS. *)
Ltac en_r HS r H :=
  lazymatch type of HS with
  | st_ok ?sg ?Ex ?ss (restrict ?Hh ?msx) =>
    pose proof (st_ok_restrict_reg sg Hh Ex ss msx r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H
  | st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?msx) =>
    pose proof (st_ok_pi_restrict_reg Hh Ex ss msx r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H
  end.
(* Rewrite the register of the goal `getr R r = _` by its symbolic value in HS. *)
Ltac en_rg HS :=
  lazymatch goal with |- YK11.getr _ ?r = _ => let H := fresh "Hrv" in en_r HS r H; rewrite H; clear H end.
(* The kept bytes after a run from a state with no region: every byte. *)
Ltac en_kupd0 KR :=
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict ?H ?m0) (mrestrict ?H ?m1) |- _ =>
  lazymatch type of KR with forall a, _ -> aview ?sg ?H ?m0 a = aview ?sg ?H ?mb a =>
    let KR2 := fresh "KR" in
    assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> aview sg H m1 a = aview sg H mb a)
      by (let aq := fresh "aq" in let Haq := fresh "Haq" in let Hwq := fresh "Hwq" in
          intros aq Haq; rewrite (kept_of_frame Ex rs H m0 m1 (fun _ => False) HFr
            ltac:(intros ? ? ? ? Hwq _; vm_compute in Hwq; destruct Hwq) aq Haq (fun xq => xq));
          exact (KR aq Haq));
    clear KR HFr; rename KR2 into KR end end;
  repeat match goal with
  | H : frame_of _ _ _ _ |- _ => clear H
  | H : mem_grows _ _ |- _ => clear H
  end.

(* ------------------------------------------------------------------ *)
(* 3. The segment                                                       *)
(* ------------------------------------------------------------------ *)

Section sg. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.

(* The registers every cut point keeps: sp = sp1, gp / tp, s7 .. s11. *)
Definition en_cregs (cx : ucx) (regs' : bvmap 5 word) : Prop :=
  spZ regs' = u_sp1 cx /\ YK11.getr regs' 3 = w64 (as_gp B) /\ YK11.getr regs' 4 = w64 (as_tp B) /\
  YK11.getr regs' 23 = YK11.getr (u_regs cx) 23 /\ YK11.getr regs' 24 = YK11.getr (u_regs cx) 24 /\
  YK11.getr regs' 25 = YK11.getr (u_regs cx) 25 /\ YK11.getr regs' 26 = YK11.getr (u_regs cx) 26 /\
  YK11.getr regs' 27 = YK11.getr (u_regs cx) 27.
Lemma en_cregs_kept : forall cx regs regs', en_cregs cx regs -> aregs_preserved regs regs' -> en_cregs cx regs'.
Proof.
intros cx regs regs' (H2 & H3 & H4 & H23 & H24 & H25 & H26 & H27) P.
assert (Q : forall r, acallee_saved r -> YK11.getr regs' (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) by exact P.
split; [rewrite <- H2; unfold spZ; f_equal; exact (Q 2 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- H3; exact (Q 3 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- H4; exact (Q 4 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- H23; exact (Q 23 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- H24; exact (Q 24 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- H25; exact (Q 25 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- H26; exact (Q 26 ltac:(unfold acallee_saved; lia))|].
rewrite <- H27; exact (Q 27 ltac:(unfold acallee_saved; lia)).
Qed.
Lemma en_fregs_kept : forall cx regs regs' f, u_fregs cx regs f -> aregs_preserved regs regs' -> u_fregs cx regs' f.
Proof.
intros cx regs regs' f (H8 & H9 & H18 & H19 & H21 & H22) P.
assert (Q : forall r, acallee_saved r -> YK11.getr regs' (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) by exact P.
split; [rewrite <- H8; exact (Q 8 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- H9; exact (Q 9 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- H18; exact (Q 18 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- H19; exact (Q 19 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- H21; exact (Q 21 ltac:(unfold acallee_saved; lia))|].
rewrite <- H22; exact (Q 22 ltac:(unfold acallee_saved; lia)).
Qed.
(* The saved words are read at [sp0 - 64, sp0) only. *)
Lemma en_saved_kept : forall cx (r r' : reader),
  (forall a, u_sp0 cx - 64 <= a < u_sp0 cx -> r' a = r a) -> u_saved cx r -> u_saved cx r'.
Proof.
intros cx r r' Hk Hs. unfold u_saved in *. rewrite Forall_forall in Hs |- *. intros o Ho. rewrite <- (Hs o Ho).
apply rdword_kept. intros i Hi. apply Hk. unfold wire_saved_at in Ho. cbn [In] in Ho.
repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho.
Qed.
(* ... and the stack region of a state after the prologue holds them. *)
Lemma en_saved_of : forall cx E H mem,
  region_ok segs E (mrestrict H mem) (YP09.mkRegion (Some 2%nat) (-64) 0 (-64) 0 en_saved) ->
  bv_unsigned (ew E 2) = u_sp0 cx ->
  (forall k (r : bv 5), (k < 32)%nat -> Z.of_nat k = bv_unsigned r -> ew E k = YK11.getr (u_regs cx) r) ->
  u_saved cx (aview segs H mem).
Proof.
intros cx E H mem HR0 Usp EE.
unfold u_saved, wire_saved_at.
repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
lazymatch goal with |- rdword _ (u_sp0 cx - ?off) = Some (bv_unsigned (YK11.getr (u_regs cx) (Z_to_bv 5 ?r))) =>
  let rn := eval vm_compute in (Z.to_nat r) in
  rewrite <- (EE rn (Z_to_bv 5 r)) by (vm_compute; first [reflexivity | lia]);
  apply rdword_of_val_mem;
  [ replace (u_sp0 cx - off) with (u_sp0 cx + (- off)) by lia;
    eapply (saved_slot _ _ _ _ _ _ _ _ _ (- off) rn (u_sp0 cx) HR0 Usp);
    unfold en_saved; cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right])
  | let w := fresh "w" in pose proof (bv_unsigned_in_range 64 (ew E rn)) as w;
    change (bv_modulus 64) with (2 ^ 64) in w; exact w ]
end.
Qed.

(* The region at index i of a state (either form). *)
Ltac en_region HS i HR :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?msx) =>
    let r := eval vm_compute in (nth i (ss_mem ss) (stack_region 0)) in
    assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r)
      by (apply (st_ok_pi_region_nth Ex ss (restrict Hh msx) i r HS); vm_compute; reflexivity);
    cbn [ms_mem restrict] in HR
  | st_ok ?sg ?Ex ?ss (restrict ?Hh ?msx) =>
    let r := eval vm_compute in (nth i (ss_mem ss) (stack_region 0)) in
    assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r)
      by (apply (st_ok_region_nth Ex ss (restrict Hh msx) i r HS); vm_compute; reflexivity);
    cbn [ms_mem restrict] in HR
  end.
(* en_cregs at a state of the prologue's run: sp = sp0 - 0x40, gp / tp and s7 .. s11 the entry's. *)
Ltac en_cregs1 HS regs E2 EE0 Hgp Htp :=
  let H := fresh "Hrv" in
  split;
  [ en_r HS (2%bv : bv 5) H; unfold spZ at 1; rewrite H; clear H;
    rewrite (en_sp_val _ regs (-64)); [unfold u_sp1, u_sp0; cbn [u_regs]; unfold U_FRAME; lia
                                      | rewrite ?ew_ewset_other by lia; exact E2 | lia]
  | split; [en_rg HS; apply en_v_reg; rewrite ?ew_ewset_other by lia; rewrite (EE0 3%nat 3%bv eq_refl); exact Hgp|];
    split; [en_rg HS; apply en_v_reg; rewrite ?ew_ewset_other by lia; rewrite (EE0 4%nat 4%bv eq_refl); exact Htp|];
    repeat match goal with |- _ /\ _ => split end;
    en_rg HS; apply en_v_reg; rewrite ?ew_ewset_other by lia; apply EE0; reflexivity ].
(* u_saved at a state of the prologue's run, from its stack region (index i). *)
Ltac en_saved1 HS i EE0 Usp :=
  let HR := fresh "HR" in en_region HS i HR;
  apply (en_saved_of _ _ _ _ HR);
  [ rewrite ?ew_ewset_other by lia; exact Usp
  | let kq := fresh "kq" in let rq := fresh "rq" in let Hkq := fresh "Hkq" in let Hrq := fresh "Hrq" in
    intros kq rq Hkq Hrq; rewrite ?ew_ewset_other by lia; apply EE0; exact Hrq ].

(* +0x160 on the refusal (n = 0): the frame and the saves only; no event, and the meter has spent nothing. *)
Lemma en_close_ret : forall (MTL : ameter_laws MT) (cx : ucx) regs' mem' md',
  u_base B MT XL RLO RHI cx -> u_n cx = 0 ->
  @ajournal rc YE2k.tfib_sink_head segs B LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx)
    [] (u_ly cx) (u_S cx) (u_W cx) mem' md' 0 ->
  en_cregs cx regs' -> u_saved cx (aview segs (w_H (u_W cx)) mem') ->
  u_st_ret B MT XL cx (u_W cx) (u_cfg cx U_RET regs' mem' md').
Proof.
intros MTL cx regs' mem' md' HB Hn0 HJ (R2 & R3 & R4 & R23 & R24 & R25 & R26 & R27) HSV.
pose proof HB as HB'. unfold u_base, tfib_lib_pre_x in HB'.
destruct HB' as (_ & _ & _ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hmo).
exists (u_ly cx), (u_S cx), regs', mem', md'. split; [reflexivity|]. split.
- split; [eapply ajournal_mono_k; [exact HJ | apply Z.leb_le; vm_compute; reflexivity]|].
  split; [exact Hfrs|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
  split; [exact R23|]. split; [exact R24|]. split; [exact R25|]. split; [exact R26|]. split; [exact R27|].
  split; [exact HSV|]. rewrite app_nil_r. apply Permutation_refl.
- pose proof (mo_malloc_nonneg MT MTL WIRE_RECV_MAX ltac:(unfold WIRE_RECV_MAX; lia)) as Mm.
  pose proof (mo_malloc_nonneg MT MTL (Z.max WIRE_RECV_MAX 1) ltac:(unfold WIRE_RECV_MAX; lia)) as Mc.
  pose proof (mo_free_nonneg MT MTL) as Mf.
  assert (Hc0 : 0 <= wire_llvmf_cost MT (u_n cx))
    by (unfold wire_llvmf_cost, wire_ccpy_cost_max, PCPY.wire_check_copy_cost; lia).
  split; [apply (mo_le_mono MT MTL _ _ 0); [apply (mo_le_refl MT MTL) | exact Hc0]|].
  apply (mo_ok_le MT MTL _ _ (XL (u_n cx)) Hmo). lia.
Qed.

(* +0x0b0, the head of turn_a. *)
Lemma en_close_oh : forall (MTL : ameter_laws MT) (cx : ucx) ly2 S2 (W2 : world segs) regs' mem' md' f,
  u_base B MT XL RLO RHI cx -> 0 < u_n cx ->
  @ajournal rc YE2k.tfib_sink_head segs B LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx)
    [] ly2 S2 W2 mem' md' 1 ->
  frames S2 = frames (u_S cx) ->
  ablocks B ly2 S2 = ablocks B (u_ly cx) (u_S cx) ++ [(f, u_fsz cx)] ->
  mo_le MT (u_S cx) S2 (mo_malloc MT (u_fsz cx)) ->
  en_cregs cx regs' -> u_saved cx (aview segs (w_H W2) mem') -> u_fregs cx regs' f ->
  garr8 segs (mrestrict (w_H W2) mem') f (map (fun b : byte => bv_unsigned b) (u_fb cx)) ->
  u_st_oh B MT XL cx W2 (u_cfg cx U_OH regs' mem' md').
Proof.
intros MTL cx ly2 S2 W2 regs' mem' md' f HB Hn HJ Hfr Hbl MLE (R2 & R3 & R4 & R23 & R24 & R25 & R26 & R27) HSV HF HG.
pose proof HB as HB'. unfold u_base, tfib_lib_pre_x in HB'.
destruct HB' as (_ & _ & _ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hmo).
exists ly2, S2, regs', mem', md', f. split; [reflexivity|]. split; [exact Hn|]. split.
- split; [exact HJ|]. split; [rewrite Hfr; exact Hfrs|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
  split; [exact R23|]. split; [exact R24|]. split; [exact R25|]. split; [exact R26|]. split; [exact R27|].
  split; [exact HSV|]. rewrite Hbl. apply Permutation_refl.
- pose proof (u_fn_range cx Hn) as (Hfn & Hfsz).
  pose proof (mo_malloc_mono MT MTL (u_fsz cx) WIRE_RECV_MAX ltac:(unfold WIRE_RECV_MAX in *; lia)) as Mmono.
  unfold u_meter, U_C_F. split; [split; [exact (mo_le_mono MT MTL _ _ _ _ MLE Mmono)|]|].
  { apply (mo_ok_step MT MTL (u_S cx) S2 (mo_malloc MT (u_fsz cx))); [|exact MLE].
    apply (mo_ok_le MT MTL _ _ (XL (u_n cx)) Hmo). lia. }
  split; [exact HF | exact HG].
Qed.

(* From the malloc of f (+0x084) to +0x0b0. *)
Lemma en_after : forall (HP : u_prem B MT XL RLO RHI) (cx : ucx) regsT memT mdT,
  u_base B MT XL RLO RHI cx -> 0 < u_n cx ->
  @ajournal rc YE2k.tfib_sink_head segs B LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx)
    [] (u_ly cx) (u_S cx) (u_W cx) memT mdT 0 ->
  YK11.getr regsT 1 = w64 (WIRE_A_LLVMF + 0x88) ->
  en_cregs cx regsT ->
  YK11.getr regsT 8 = YK11.getr (u_regs cx) 8 ->
  YK11.getr regsT 9 = w64 (u_fn cx) -> YK11.getr regsT 10 = w64 (u_fsz cx) ->
  YK11.getr regsT 18 = w64 (u_flag cx) -> YK11.getr regsT 19 = w64 (u_fsz cx) ->
  YK11.getr regsT 20 = w64 (u_p cx) -> YK11.getr regsT 22 = w64 (u_n cx - 1) ->
  u_saved cx (aview segs (w_H (u_W cx)) memT) ->
  SRr segs (u_W cx)
    (mkCfg (@YK11.mkst (u_fx cx) regsT (Z_to_bv 64 (pc_wrap_malloc (as_code B))) memT (YK11.seg_rom segs)) mdT)
    (fun W' c' => u_st_oh B MT XL cx W' c' \/ u_st_ret B MT XL cx W' c').
Proof.
intros HP cx regsT memT mdT HB Hn0 HJ R1 HCR R8 R9 R10 R18 R19 R20 R22 HSV.
pose proof (up_laws _ _ _ _ _ HP) as LAWS. pose proof (up_meter_laws _ _ _ _ _ HP) as MTL.
pose proof HB as HB'. unfold u_base, tfib_lib_pre_x in HB'.
destruct HB' as (HAFN & Hra & H10 & H11 & Hpn & Hlen & Hgarr & Hfrs & Hnev & Hbb & Haro & Hsink & Hfd & Hfs & Hmeta & Hmo).
pose proof HAFN as (HAR & Hret & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
destruct Hpn as [(Hz & _) | (Hn & Hin)]; [lia|].
pose proof (u_fn_range cx Hn0) as (Hfn & Hfsz).
pose proof alloc_ceiling_val as Hac. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HCR as (Rsp & R3 & R4 & R23 & R24 & R25 & R26 & R27).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hp4 & Hpc & _ & _ & _ & _).
pose proof (req_size_pos (u_n cx) ltac:(lia)) as Hrq.
assert (Hstkv : LLVMF_STK = 32768) by reflexivity.
assert (Hsp0 : alloc_ceiling + 32768 <= u_sp0 cx /\ u_sp0 cx <= 2 ^ 47) by (unfold u_sp0; rewrite Hstkv in Hslo; lia).
assert (Hfd0 : 0 <= u_flag cx < 256) by exact (u_flag_range cx).
assert (Hraz : raZ regsT = WIRE_A_LLVMF + 0x88)
  by (unfold raZ; rewrite R1; apply en_bv_small; unfold WIRE_A_LLVMF, wire_text, AF_LLVMFuzzerTestOneInput; lia).
assert (Hs0 : s0Z regsT = s0Z (u_regs cx)) by (unfold s0Z; rewrite R8; reflexivity).
(* the chain at the call: s0 is the caller's, whose chain is empty (the slot's afn_pre ... []) *)
assert (HCH : chain_pre (u_ly cx) (aview segs (w_H (u_W cx)) memT) regsT []).
{ unfold chain_pre. split; [rewrite Hraz; unfold WIRE_A_LLVMF, wire_text, AF_LLVMFuzzerTestOneInput; lia|].
  destruct (frame0_ok (u_ly cx) regsT); [|reflexivity].
  rewrite Rsp, Hs0. unfold u_sp1, u_sp0, U_FRAME in *.
  destruct Hch as [(Hbad & _) | (Hv1 & Hv2 & Hv3 & Hfp & _)].
  - replace (bad_next (spZ (u_regs cx) - 64) (ly_top (u_ly cx)) (s0Z (u_regs cx))) with true; [reflexivity|].
    symmetry. unfold bad_next. destruct Hbad as [Hb | [Hb | Hb]].
    + apply orb_true_intro. left. apply orb_true_intro. left. apply Z.leb_le. rewrite Hstkv in Hslo. lia.
    + apply orb_true_intro. left. apply orb_true_intro. right. apply Z.leb_le. lia.
    + apply orb_true_intro. right. apply negb_true_iff. apply Z.eqb_neq. exact Hb.
  - replace (bad_next (spZ (u_regs cx) - 64) (ly_top (u_ly cx)) (s0Z (u_regs cx))) with false.
    2: { symmetry. unfold bad_next. apply orb_false_intro; [apply orb_false_intro|].
         - apply Z.leb_gt. lia. - apply Z.leb_gt. lia. - apply negb_false_iff. apply Z.eqb_eq. exact Hv3. }
    split; [lia|]. cbn [fpchain] in Hfp |- *. destruct Hfp as (r & Hr & Hr4). exists r. split; [|exact Hr4].
    rewrite <- Hr. apply rdword_kept. intros i Hi.
    pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). apply F1; rewrite ?Hstkv; lia. }
(* the trace [pc0; +0x088] *)
assert (HTR : In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT []) (as_universe B)).
{ rewrite en_trace0, Hraz. exact (proj1 (up_ufix _ _ _ _ _ HP)). }
(* the meter: the malloc of f is the first charge of wire_llvmf_cost *)
pose proof (up_cost _ _ _ _ _ HP (u_n cx) ltac:(lia)) as Hcost.
unfold wire_llvmf_cost, wire_ccpy_cost_max, PCPY.wire_check_copy_cost in Hcost.
pose proof (mo_malloc_nonneg MT MTL (u_fsz cx) ltac:(lia)) as Mm.
pose proof (mo_malloc_mono MT MTL (u_fsz cx) WIRE_RECV_MAX ltac:(unfold WIRE_RECV_MAX in *; lia)) as Mmono.
pose proof (mo_malloc_nonneg MT MTL WIRE_RECV_MAX ltac:(unfold WIRE_RECV_MAX; lia)) as Mm1.
pose proof (mo_malloc_nonneg MT MTL (Z.max WIRE_RECV_MAX 1) ltac:(unfold WIRE_RECV_MAX; lia)) as Mc.
pose proof (mo_free_nonneg MT MTL) as Mf.
assert (HMOK : mo_ok MT (u_S cx) (mo_malloc MT (u_fsz cx))) by (apply (mo_ok_le MT MTL _ _ _ Hmo); lia).
assert (HDEP : st_depot (u_S cx) <> []) by exact (wire_depot_of_block B _ _ _ _ _ _ _ (proj1 HJ) Hin).
(* malloc (fsz) *)
pose proof (up_malloc _ _ _ _ _ HP (u_fx cx)) as AM.
assert (A1 : 0 <= u_fsz cx < MALLOC_MAX) by (clear - Hfsz; unfold WIRE_RECV_MAX, MALLOC_MAX in *; lia).
assert (A2 : blocks_bytes (u_S cx) + u_fsz cx <= LIVE_MAX)
  by (clear - Hfsz Hbb; unfold WIRE_RECV_MAX, LIVE_LIB, LIVE_MAX in *; lia).
assert (A3 : spZ regsT = u_sp0 cx + -64) by (rewrite Rsp; unfold u_sp1, U_FRAME; lia).
assert (A6 : ASTACK - -64 <= LLVMF_STK) by (unfold ASTACK; rewrite Hstkv; lia).
assert (A7 : YK0s.ret_ok (YK11.getr regsT 1))
  by (rewrite R1; exact (ret_ok_codeptr_v (PI := PI_wire) 0x88 ltac:(lia) eq_refl)).
assert (A8 : st_nev (u_S cx) < EV_MAX) by (clear - Hnev; unfold EV_LIB in Hnev; lia).
eapply SRr_bind.
{ exact (AM (u_W cx) regsT memT LLVMF_STK (u_sp0 cx) [] (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) []
    (u_ly cx) (u_S cx) mdT 0 (u_fsz cx) (-64) (YK11.getr regsT 1) [] HJ R10 A1 A2 A3 eq_refl ltac:(lia) A6 R3 R4 eq_refl
    A7 A8 HCH HTR HMOK HDEP). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Hres & Hfr2 & Hr4 & Hbl2 & HK & MLE).
assert (HRS : forall r, acallee_saved r -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regsT (Z_to_bv 5 r)) by exact HP2.
pose proof (en_cregs_kept cx regsT regs2 HCR HP2) as HCR2.
assert (G9 : YK11.getr regs2 9 = w64 (u_fn cx)) by (rewrite <- R9; exact (HRS 9 ltac:(unfold acallee_saved; lia))).
assert (G18 : YK11.getr regs2 18 = w64 (u_flag cx)) by (rewrite <- R18; exact (HRS 18 ltac:(unfold acallee_saved; lia))).
assert (G19 : YK11.getr regs2 19 = w64 (u_fsz cx)) by (rewrite <- R19; exact (HRS 19 ltac:(unfold acallee_saved; lia))).
assert (G20 : YK11.getr regs2 20 = w64 (u_p cx)) by (rewrite <- R20; exact (HRS 20 ltac:(unfold acallee_saved; lia))).
assert (G22 : YK11.getr regs2 22 = w64 (u_n cx - 1)) by (rewrite <- R22; exact (HRS 22 ltac:(unfold acallee_saved; lia))).
assert (Hresin : In (res, u_fsz cx) (ablocks B ly2 S2)) by (rewrite Hbl2; apply in_or_app; right; left; reflexivity).
assert (Hpin2 : In (u_p cx, u_n cx) (ablocks B ly2 S2)) by (rewrite Hbl2; apply in_or_app; left; exact Hin).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ2) Hresin) as (_ & Hres4 & Hresc & _ & _ & _ & _).
pose proof (req_size_pos (u_fsz cx) ltac:(lia)) as Hrqf.
pose proof HK as (HK1 & _).
assert (HSV2 : u_saved cx (aview segs (w_H W2) mem2)).
{ apply (en_saved_kept cx (aview segs (w_H (u_W cx)) memT)); [|exact HSV].
  intros a Ha. apply HK1; [lia | unfold ASTACK; lia]. }
(* +0x088 .. by the Pa engine *)
rewrite R1.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr (@pa_segs _ wire_listing PI_wire) Wx
    (mkCfg (@YK11.mkst (u_fx cx) regs2 (Z_to_bv 64 (@pa_val _ wire_listing PI_wire A_TEXT + 0x88)) mem2
      (seg_rom (@pa_segs _ wire_listing PI_wire))) md2) Q) end.
pose proof (en_e88 (fx := u_fx cx) regs2 mem2 (w_H W2)) as HS.
assert (SHOK : sh_ok segs (SOff 32 0) [] (E88 regs2) (mrestrict (w_H W2) mem2)) by constructor.
assert (HEI : img_env (@pa_val _ wire_listing PI_wire) A_LIM (E88 regs2)) by apply Eimg_env.
assert (X : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (E88 regs2) k = YK11.getr regs2 r)
  by (intros k r Hk; unfold E88; apply ew_Eimg_Ereg_nat; exact Hk).
assert (KR : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W2) mem2 a) by reflexivity.
assert (RR : 0 <= res < 2 ^ 64) by lia.
pose proof (paj_run (fx := u_fx cx) (SK := YE2k.tfib_sink_head) (PI := PI_wire) B LAWS) as RUN.
pose proof (paj_run_to (fx := u_fx cx) (SK := YE2k.tfib_sink_head) (PI := PI_wire) B LAWS) as RUNTO.
pose proof (@paj_branch (u_fx cx) _ wire_listing PI_wire) as BR.
(* `beqz a0`: f is not NULL *)
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_eq_U, (U_atom _ 10 res), U_lit in Hc
    by (first [lia | rewrite (X 10%nat 10%bv eq_refl); exact Hres]).
  apply Z.eqb_eq in Hc. lia. }
clear Hc.
(* s0 = f, s5 = data[0] & 1, s2 = (data[0] >> 1) - 2, up to `beqz s6` *)
paj_run_tok RUN HS HJ2 SHOK Bspan; [en_awr0|]. en_kupd0 KR. en_md.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* n = 1: fn = 0, +0x0b0 at once *)
  assert (Hn1 : u_n cx = 1).
  { rewrite branch_eq_U, (U_atom _ 22 (u_n cx - 1)), U_lit in Hc
      by (first [lia | rewrite ?ew_ewset_other by lia; rewrite (X 22%nat 22%bv eq_refl); exact G22]).
    apply Z.eqb_eq in Hc. lia. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ2 SHOK Bspan 176; [en_awr0|]. en_kupd0 KR. en_md.
  pmkst HS.
  apply SRr_ret. left.
  lazymatch goal with |- _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) =>
    refine (en_close_oh MTL cx ly2 S2 W2 rg mm mdx res HB Hn0 HJ2 Hfr2 Hbl2 MLE _ _ _ _) end.
  + destruct HCR2 as (Q2 & Q3 & Q4 & Q23 & Q24 & Q25 & Q26 & Q27).
    split; [unfold spZ; rewrite <- Q2; unfold spZ; f_equal; en_rg HS; apply en_v_reg; rewrite ?ew_ewset_other by lia;
            apply X; reflexivity|].
    split; [rewrite <- Q3; en_rg HS; apply en_v_reg; rewrite ?ew_ewset_other by lia; apply X; reflexivity|].
    split; [rewrite <- Q4; en_rg HS; apply en_v_reg; rewrite ?ew_ewset_other by lia; apply X; reflexivity|].
    split; [rewrite <- Q23; en_rg HS; apply en_v_reg; rewrite ?ew_ewset_other by lia; apply X; reflexivity|].
    split; [rewrite <- Q24; en_rg HS; apply en_v_reg; rewrite ?ew_ewset_other by lia; apply X; reflexivity|].
    split; [rewrite <- Q25; en_rg HS; apply en_v_reg; rewrite ?ew_ewset_other by lia; apply X; reflexivity|].
    split; [rewrite <- Q26; en_rg HS; apply en_v_reg; rewrite ?ew_ewset_other by lia; apply X; reflexivity|].
    rewrite <- Q27; en_rg HS; apply en_v_reg; rewrite ?ew_ewset_other by lia; apply X; reflexivity.
  + apply (en_saved_kept cx (aview segs (w_H W2) mem2)); [|exact HSV2]. intros a Ha. apply KR. lia.
  + split; [en_rg HS; apply en_v_reg; rewrite ?ew_ewset_other by lia; rewrite (X 10%nat 10%bv eq_refl); exact Hres|].
    split; [en_rg HS; apply en_v_reg; rewrite ?ew_ewset_other by lia; rewrite (X 9%nat 9%bv eq_refl); exact G9|].
    split; [en_rg HS; unfold u_slot; apply en_v_slot; [rewrite ?ew_ewset_other by lia; rewrite (X 18%nat 18%bv eq_refl); exact G18 | exact Hfd0]|].
    split; [en_rg HS; apply en_v_reg; rewrite ?ew_ewset_other by lia; rewrite (X 19%nat 19%bv eq_refl); exact G19|].
    split; [en_rg HS; unfold u_bc; apply en_v_bc; [rewrite ?ew_ewset_other by lia; rewrite (X 18%nat 18%bv eq_refl); exact G18 | exact Hfd0]|].
    en_rg HS; apply en_v_reg; rewrite ?ew_ewset_other by lia; rewrite (X 22%nat 22%bv eq_refl); exact G22.
  + replace (u_fb cx) with (@nil byte) by (unfold u_fb, u_fn; rewrite Hn1; reflexivity). apply garr8_nil.
- (* n >= 2: __asan_memcpy (f, data + 1, fn) *)
  assert (Hn2 : u_n cx <> 1).
  { rewrite branch_eq_U, (U_atom _ 22 (u_n cx - 1)), U_lit in Hc
      by (first [lia | rewrite ?ew_ewset_other by lia; rewrite (X 22%nat 22%bv eq_refl); exact G22]).
    apply Z.eqb_neq in Hc. lia. }
  clear Hc.
  paj_run_tok RUN HS HJ2 SHOK Bspan; [en_awr0|]. en_kupd0 KR. en_md.
  pmkst HS.
  change (pa_sigma WS___asan_memcpy) with (wire_sigma WS___asan_memcpy).
  assert (Hfn2 : u_fn cx = u_fsz cx /\ 1 <= u_fn cx <= u_n cx - 1) by (unfold u_fsz, u_fn, WIRE_RECV_MAX in *; lia).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
    assert (M10 : YK11.getr rg 10 = w64 res)
      by (en_rg HS; apply en_v_reg; rewrite ?ew_ewset_other by lia; rewrite (X 10%nat 10%bv eq_refl); exact Hres);
    assert (M11 : YK11.getr rg 11 = w64 (u_p cx + 1))
      by (en_rg HS; apply en_v_off; [rewrite ?ew_ewset_other by lia; rewrite (X 20%nat 20%bv eq_refl); exact G20 | lia]);
    assert (M12 : YK11.getr rg 12 = w64 (u_fn cx))
      by (en_rg HS; apply en_v_reg; rewrite ?ew_ewset_other by lia; rewrite (X 9%nat 9%bv eq_refl); exact G9);
    assert (M1 : YK11.getr rg 1 = Z_to_bv 64 (@pa_val _ wire_listing PI_wire A_TEXT + 176))
      by (en_rg HS; lazymatch goal with |- sv_denot ?Ex _ = _ =>
            lazymatch goal with HEIy : img_env _ _ Ex |- _ => exact (codeptr_val Ex 176 HEIy) end end);
    assert (MCR : en_cregs cx rg);
    [ destruct HCR2 as (Q2 & Q3 & Q4 & Q23 & Q24 & Q25 & Q26 & Q27);
      split; [unfold spZ; rewrite <- Q2; unfold spZ; f_equal; en_rg HS; apply en_v_reg; rewrite ?ew_ewset_other by lia;
              apply X; reflexivity|];
      split; [rewrite <- Q3; en_rg HS; apply en_v_reg; rewrite ?ew_ewset_other by lia; apply X; reflexivity|];
      split; [rewrite <- Q4; en_rg HS; apply en_v_reg; rewrite ?ew_ewset_other by lia; apply X; reflexivity|];
      split; [rewrite <- Q23; en_rg HS; apply en_v_reg; rewrite ?ew_ewset_other by lia; apply X; reflexivity|];
      split; [rewrite <- Q24; en_rg HS; apply en_v_reg; rewrite ?ew_ewset_other by lia; apply X; reflexivity|];
      split; [rewrite <- Q25; en_rg HS; apply en_v_reg; rewrite ?ew_ewset_other by lia; apply X; reflexivity|];
      split; [rewrite <- Q26; en_rg HS; apply en_v_reg; rewrite ?ew_ewset_other by lia; apply X; reflexivity|];
      rewrite <- Q27; en_rg HS; apply en_v_reg; rewrite ?ew_ewset_other by lia; apply X; reflexivity
    | ];
    assert (MFR : u_fregs cx rg res);
    [ split; [en_rg HS; apply en_v_reg; rewrite ?ew_ewset_other by lia; rewrite (X 10%nat 10%bv eq_refl); exact Hres|];
      split; [en_rg HS; apply en_v_reg; rewrite ?ew_ewset_other by lia; rewrite (X 9%nat 9%bv eq_refl); exact G9|];
      split; [en_rg HS; unfold u_slot; apply en_v_slot;
              [rewrite ?ew_ewset_other by lia; rewrite (X 18%nat 18%bv eq_refl); exact G18 | exact Hfd0]|];
      split; [en_rg HS; apply en_v_reg; rewrite ?ew_ewset_other by lia; rewrite (X 19%nat 19%bv eq_refl); exact G19|];
      split; [en_rg HS; unfold u_bc; apply en_v_bc;
              [rewrite ?ew_ewset_other by lia; rewrite (X 18%nat 18%bv eq_refl); exact G18 | exact Hfd0]|];
      en_rg HS; apply en_v_reg; rewrite ?ew_ewset_other by lia; rewrite (X 22%nat 22%bv eq_refl); exact G22
    | ]
  end.
  pose proof MCR as (Msp & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ2) Hpin2) as (_ & _ & _ & _ & Hppres & _ & _).
  assert (Hne : (res, u_fsz cx) <> (u_p cx, u_n cx)) by (intros Heq; injection Heq as _ Hq; lia).
  pose proof (sep_blocks segs B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ2) Hresin Hpin2 Hne) as Hdj.
  unfold zdisjoint in Hdj. cbn [fst snd] in Hdj.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
    assert (Hsrc : 0 <= u_p cx + 1 /\ u_p cx + 1 + u_fn cx <= 2 ^ 63 /\
      src_ok segs W2 rg mm (u_p cx + 1) (u_fn cx) /\
      (res + u_fn cx <= u_p cx + 1 \/ u_p cx + 1 + u_fn cx <= res) /\
      amem_range (u_p cx + 1) (u_fn cx) /\
      range_addressable (aview segs (w_H W2) mm) SHADOW_OFF (u_p cx + 1) (u_fn cx) /\
      (0 < u_fn cx -> shadow_hull_vis (aview segs (w_H W2) mm) (u_p cx + 1) (u_fn cx)))
  end.
  { split; [lia|]. split; [lia|].
    split.
    { intros a Ha. split; [apply (aview_some_of_apresent segs); exact (proj1 (Hppres a ltac:(lia)))|].
      rewrite Msp. unfold u_sp1, U_FRAME, ESTACK. lia. }
    split; [lia|].
    split; [eapply (amem_range_of_block segs B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ2) Hpin2); lia|].
    split; [eapply (range_addressable_of_block segs B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ2) Hpin2); lia|].
    intros Hk0. eapply (shadow_hull_vis_of_block segs B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ2) Hpin2); lia. }
  eapply SRr_mono.
  { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
    refine (aj_intrin_at (fx := u_fx cx) (SK := YE2k.tfib_sink_head) segs B LAWS wire_segs_low OCpy
      (wire_sigma WS___asan_memcpy) (up_memcpy _ _ _ _ _ HP (u_fx cx)) W2 rg mm LLVMF_STK (u_sp0 cx) []
      (u_ly cx) (u_S cx) (u_W cx) (u_mem cx) (u_md cx) [] ly2 S2 mdx 1 res (u_p cx + 1) (u_fn cx) (-64)
      (YK11.getr rg 1) HJ2 M10 M11 M12 _ _ _ _ _ _ _ (proj1 (proj2 MCR)) (proj1 (proj2 (proj2 MCR))) eq_refl
      _ _ _ _ _ Hsrc) end.
    - lia.
    - lia.
    - lia.
    - rewrite Msp. unfold u_sp1, U_FRAME. lia.
    - reflexivity.
    - lia.
    - unfold ESTACK. rewrite Hstkv. lia.
    - rewrite M1. exact (ret_ok_codeptr_v (PI := PI_wire) 176 ltac:(lia) eq_refl).
    - intros a Ha. split.
      + replace a with (res + (a - res)) by lia.
        eapply (awr_new_block segs B LAWS); [exact HJ | exact (proj1 HJ2) | exact Hbl2 | lia | exact Hresin | lia].
      + unfold ESTACK. lia.
    - eapply (amem_range_of_block segs B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ2) Hresin); lia.
    - eapply (range_addressable_of_block segs B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ2) Hresin); lia.
    - intros Hk0. eapply (shadow_hull_vis_of_block segs B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ2) Hresin); lia. }
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & _ & Hcopy & Hkeep & _).
  cbv iota in Hcopy.
  rewrite M1. left.
  refine (en_close_oh MTL cx ly2 S2 W2 regs3 mem3 md3 res HB Hn0 HJ3 Hfr2 Hbl2 MLE
    (en_cregs_kept cx _ regs3 MCR HP3) _ (en_fregs_kept cx _ regs3 res MFR HP3) _).
  + apply (en_saved_kept cx (aview segs (w_H W2) mem2)); [|exact HSV2]. intros a Ha.
    rewrite Hkeep; [apply KR; lia | lia | lia | unfold ESTACK, u_sp1, U_FRAME; lia].
  + intros j Hj. rewrite length_map in Hj.
    pose proof (u_fb_length cx Hn0 Hlen) as Hfbl.
    rewrite (en_fb_nth cx j) by lia.
    assert (HjS : (S j < length (map (fun b : byte => bv_unsigned b) (u_pl cx)))%nat) by (rewrite length_map; lia).
    destruct (Hgarr (S j) HjS) as [Hv Hr]. split; [|exact Hr].
    apply (val_mem_moved segs (w_H (u_W cx)) (w_H W2) (u_mem cx) mem3 (u_p cx + Z.of_nat (S j)) (res + Z.of_nat j) 1);
      [|exact Hv].
    intros k Hk. replace (res + Z.of_nat j + k) with (res + (Z.of_nat j + k)) by lia.
    rewrite (Hcopy (Z.of_nat j + k)) by lia.
    pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
    replace (u_p cx + 1 + (Z.of_nat j + k)) with (u_p cx + (Z.of_nat (S j) + k)) by lia.
    replace (u_p cx + Z.of_nat (S j) + k) with (u_p cx + (Z.of_nat (S j) + k)) by lia.
    apply (F2 (u_p cx) (u_n cx) (Z.of_nat (S j) + k) Hin Hpin2); [lia | intros (rg & [] & _)].
Qed.

Theorem u_entry_ok : u_entry_stmt B MT XL RLO RHI.
Proof.
intros HP cx HB.
pose proof (up_cells _ _ _ _ _ HP) as HCELLS. pose proof (up_laws _ _ _ _ _ HP) as LAWS.
pose proof (up_meter_laws _ _ _ _ _ HP) as MTL.
pose proof HB as HB0.
destruct cx as [fx ly S W regs mem md p n pl M].
unfold u_base, tfib_lib_pre_x in HB. cbn [u_fx u_ly u_S u_W u_regs u_mem u_md u_p u_n u_pl u_M] in *.
destruct HB as (HAFN & Hra & H10 & H11 & Hpn & Hlen & Hgarr & Hfrs & Hnev & Hbb & Haro & Hsink & Hfd & Hfs & Hmeta & Hmo).
pose proof HAFN as (HAR & Hret & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as Hac.
assert (Hstkv : LLVMF_STK = 32768) by reflexivity.
assert (Hn26 : 0 <= n < 2 ^ 26) by (destruct Hpn as [(-> & _) | (Hn & _)]; lia).
assert (Hp : 4096 <= p <= 140737479966720).
{ destruct Hpn as [(_ & ->) | (Hn & Hin)]; [unfold A_EMPTY; lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & Hb1 & Hb3 & _).
  pose proof (req_size_pos n ltac:(lia)) as Hrq. lia. }
set (d0 := match pl with [] => 0 | b :: _ => bv_unsigned b end).
assert (Hd0 : 0 <= d0 < 256).
{ unfold d0. destruct pl as [|b pl']; [lia|]. pose proof (bv_unsigned_in_range 8 b) as Hb. exact Hb. }
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by (rewrite Hstkv in Hslo; lia).
pose proof (en_entry (fx := fx) B ly S W regs mem md p n d0 HAR HCELLS
  ltac:(intros a Ha; apply Hpres; unfold U_FRAME in Ha; lia) Hsp Hsp16 H10 H11 Hp Hn26 Hd0) as HS.
pose proof (ajournal_init (SK := YE2k.tfib_sink_head) segs B LLVMF_STK [] ly S W regs mem md [] HAFN) as HJ.
assert (SHOK : sh_ok segs (SOff 32 0) [] (EEN regs d0) (mrestrict (w_H W) mem)) by constructor.
assert (HEI : img_env (@pa_val _ wire_listing PI_wire) A_LIM (EEN regs d0)) by apply Eimg_env.
assert (EE0 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (EEN regs d0) n = getr regs r)
  by (intros nn r Hnn; unfold EEN; apply ew_Eimg_Ereg_nat; exact Hnn).
assert (E2 : ew (EEN regs d0) 2 = getr regs 2) by exact (EE0 2%nat 2%bv eq_refl).
assert (Usp : bv_unsigned (ew (EEN regs d0) 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E10 : ew (EEN regs d0) 10 = w64 p) by (rewrite (EE0 10%nat 10%bv eq_refl); exact H10).
assert (E11 : ew (EEN regs d0) 11 = w64 n) by (rewrite (EE0 11%nat 11%bv eq_refl); exact H11).
assert (E32 : ew (EEN regs d0) 32 = Z_to_bv 64 SBv)
  by (unfold EEN; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew (EEN regs d0) 33 = Z_to_bv 64 d0)
  by (unfold EEN; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
set (E0 := EEN regs d0) in *.
pose proof (paj_run (fx := fx) (SK := YE2k.tfib_sink_head) (PI := PI_wire) B LAWS) as RUN.
pose proof (paj_run_to (fx := fx) (SK := YE2k.tfib_sink_head) (PI := PI_wire) B LAWS) as RUNTO.
pose proof (@paj_branch fx _ wire_listing PI_wire) as BR.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr (@pa_segs _ wire_listing PI_wire) Wx
    (mkCfg (mkst regs (Z_to_bv 64 (@pa_val _ wire_listing PI_wire A_TEXT + AF_LLVMFuzzerTestOneInput)) mem
      (seg_rom (@pa_segs _ wire_listing PI_wire))) md) Q) end.
(* +0x000 .. +0x030: the frame, the saves, the size test *)
paj_run_tok RUN HS HJ SHOK Bspan; [en_awr Usp Hstkv|]. en_md.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ (* n = 0: +0x160 *)
  assert (Hn0 : n = 0).
  { lazymatch type of Hc with context [sv_denot ?Ex (SOff 11 _)] =>
      rewrite (en_size_test Ex n ltac:(rewrite ?ew_ewset_other by lia; exact E11) Hn26) in Hc end.
    apply Z.eqb_eq in Hc. exact Hc. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 352; [en_awr Usp Hstkv|]. en_md.
  pmkst HS.
  apply SRr_ret. right.
  lazymatch goal with |- _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) =>
    refine (en_close_ret MTL (mkUCx fx ly S W regs mem md p n pl M) rg mm mdx HB0 Hn0 HJ _ _) end.
  - en_cregs1 HS regs E2 EE0 Hgp Htp.
  - en_saved1 HS 0%nat EE0 Usp. }
(* n > 0 *)
assert (Hn0 : n <> 0).
{ lazymatch type of Hc with context [sv_denot ?Ex (SOff 11 _)] =>
    rewrite (en_size_test Ex n ltac:(rewrite ?ew_ewset_other by lia; exact E11) Hn26) in Hc end.
  apply Z.eqb_neq in Hc. exact Hc. }
clear Hc.
destruct Hpn as [(Hz & _) | (Hnpos & Hin)]; [lia|].
destruct pl as [|b0 pl']; [cbn in Hlen; lia|].
(* data[0]'s region: the entry's byte at p, kept by the journal's block clause *)
assert (Hb0 : val_mem segs (mrestrict (w_H W) mem) p 1 d0).
{ assert (Hil : (0 < length (map (fun b : byte => bv_unsigned b) (b0 :: pl')))%nat) by (cbn; lia).
  destruct (Hgarr 0%nat Hil) as [Hv _]. rewrite Z.add_0_r in Hv. exact Hv. }
lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?msx) =>
  assert (Hb0' : val_mem segs (mrestrict (w_H W) (ms_mem msx)) p 1 d0);
  [ apply (val_mem_moved segs (w_H W) (w_H W) mem (ms_mem msx) p p 1 d0); [|exact Hb0];
    intros kk Hkk; pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _);
    pose proof (req_size_pos n ltac:(lia)) as Hrq;
    apply (F2 p n kk Hin Hin); [lia | intros (rg & [] & _)]
  | ];
  let HS2 := fresh "HS" in
  pose proof (st_ok_pi_add_region Ex ss (restrict Hh msx)
    (YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))]) HS eq_refl) as HS2;
  lazymatch type of HS2 with ?A -> ?B -> _ =>
    let Hrok := fresh "Hrok" in let Hdj := fresh "Hdj" in
    assert (Hrok : A); [| assert (Hdj : B); [| specialize (HS2 Hrok Hdj); clear HS Hrok Hdj; rename HS2 into HS]] end
end.
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
  rewrite ?ew_ewset_other by lia. rewrite E10, en_bv_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val segs _ _ p 0 1 (SOff 33 0) d0);
    [cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (8 * Z.of_N 1) with 8; lia | zside | rewrite Z.add_0_r; exact Hb0']. }
{ pose proof (blk_off_imgP (PI := PI_wire) B ly S W mem md p n HAR Hin) as Hoff. unfold off_img in Hoff.
  pose proof (req_size_pos n ltac:(lia)) as Hrq.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & Hb1 & Hb3 & _).
  lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
    let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
  cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite ?ew_ewset_other by lia.
  rewrite E10, Usp, en_bv_small by lia.
  unfold E0, EEN. rewrite !(Eimg_img (PI := PI_wire)) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  change (pa_val 241) with WCells.GOT_CELL_K. change (pa_val 253) with WCells.CELL_K.
  rewrite !unsigned_lit_small by (unfold WCells.GOT_CELL_K, WCells.CELL_K; lia).
  unfold WCells.GOT_CELL_K, WCells.CELL_K. rewrite Hstkv in Hslo. repeat split; lia. }
en_norm HS.
(* +0x034 .. +0x06c: s4 = p, the UBSan checks of data, data[0]'s shadow check (the token rule), s6 = s1 = n - 1,
   a0 = 1600, `bltu s6, a0` *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ eapply (obl_of_block segs B LAWS ly S W _ _ _ (SOff 32 0) _ 1 p n (proj1 HJ) Hin).
  - rewrite (U_atom _ 32 SBv) by (rewrite ?ew_ewset_other by lia; first [exact E32 | unfold SBv; lia]). reflexivity.
  - rewrite (U_atom _ 10 p) by (rewrite ?ew_ewset_other by lia; first [exact E10 | lia]). lia.
  - rewrite (U_atom _ 10 p) by (rewrite ?ew_ewset_other by lia; first [exact E10 | lia]).
    pose proof (req_size_pos n ltac:(lia)) as Hrq. lia. }
{ en_awr Usp Hstkv. }
en_md.
assert (Hcl : forall Ex, ew Ex 11 = ew E0 11 ->
  branch_taken BC_LTU (sv_denot Ex (SOff 11 (-1))) (sv_denot Ex (SLit 1600)) = (n - 1 <? 1600))
  by (intros Ex HEx; apply en_clamp_test; [rewrite HEx; exact E11 | lia]).
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* n - 1 < 1600: s1 = n - 1 *)
  assert (Hlt : n - 1 < 1600).
  { lazymatch type of Hc with context [sv_denot ?Ex (SOff 11 _)] =>
      rewrite (Hcl Ex ltac:(rewrite ?ew_ewset_other by lia; reflexivity)) in Hc end.
    apply Z.ltb_lt in Hc. exact Hc. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [en_awr Usp Hstkv|]. en_md.
  pmkst HS.
  change (pa_sigma WS___interceptor_trampoline_malloc) with (wire_sigma WS___interceptor_trampoline_malloc).
  rewrite <- (up_wrap_malloc _ _ _ _ _ HP).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
    refine (en_after HP (mkUCx fx ly S W regs mem md p n (b0 :: pl') M) rg mm mdx HB0 ltac:(cbn; lia) HJ
      _ _ _ _ _ _ _ _ _ _) end.
  + en_rg HS. lazymatch goal with |- sv_denot ?Ex _ = _ =>
      lazymatch goal with HEIy : img_env _ _ Ex |- _ => exact (codeptr_val Ex 136 HEIy) end end.
  + en_cregs1 HS regs E2 EE0 Hgp Htp.
  + en_rg HS. apply en_v_reg. rewrite ?ew_ewset_other by lia. apply EE0. reflexivity.
  + en_rg HS. rewrite (en_v_off _ 11 (-1) n) by (first [rewrite ?ew_ewset_other by lia; exact E11 | lia]).
    unfold w64. f_equal. unfold u_fn, WIRE_RECV_MAX. cbn [u_n]. lia.
  + en_rg HS. exact (en_v_fsz0 _ n ltac:(rewrite ?ew_ewset_other by lia; exact E11) ltac:(lia)).
  + en_rg HS. apply en_v_reg. rewrite ?ew_ewset_other by lia. exact E33.
  + en_rg HS. exact (en_v_fsz _ n ltac:(rewrite ?ew_ewset_other by lia; exact E11) ltac:(lia)).
  + en_rg HS. apply en_v_reg. rewrite ?ew_ewset_other by lia. exact E10.
  + en_rg HS. rewrite (en_v_off _ 11 (-1) n) by (first [rewrite ?ew_ewset_other by lia; exact E11 | lia]).
    reflexivity.
  + en_saved1 HS 1%nat EE0 Usp.
- (* n - 1 >= 1600: s1 = 1600 *)
  assert (Hge : 1600 <= n - 1).
  { lazymatch type of Hc with context [sv_denot ?Ex (SOff 11 _)] =>
      rewrite (Hcl Ex ltac:(rewrite ?ew_ewset_other by lia; reflexivity)) in Hc end.
    apply Z.ltb_ge in Hc. exact Hc. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [en_awr Usp Hstkv|]. en_md.
  pmkst HS.
  change (pa_sigma WS___interceptor_trampoline_malloc) with (wire_sigma WS___interceptor_trampoline_malloc).
  rewrite <- (up_wrap_malloc _ _ _ _ _ HP).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
    refine (en_after HP (mkUCx fx ly S W regs mem md p n (b0 :: pl') M) rg mm mdx HB0 ltac:(cbn; lia) HJ
      _ _ _ _ _ _ _ _ _ _) end.
  + en_rg HS. lazymatch goal with |- sv_denot ?Ex _ = _ =>
      lazymatch goal with HEIy : img_env _ _ Ex |- _ => exact (codeptr_val Ex 136 HEIy) end end.
  + en_cregs1 HS regs E2 EE0 Hgp Htp.
  + en_rg HS. apply en_v_reg. rewrite ?ew_ewset_other by lia. apply EE0. reflexivity.
  + en_rg HS. rewrite en_v_lit. unfold w64. f_equal. unfold u_fn, WIRE_RECV_MAX. cbn [u_n]. lia.
  + en_rg HS. rewrite en_v_lit. unfold w64. f_equal. unfold u_fsz, u_fn, WIRE_RECV_MAX. cbn [u_n]. lia.
  + en_rg HS. apply en_v_reg. rewrite ?ew_ewset_other by lia. exact E33.
  + en_rg HS. rewrite en_v_lit. unfold w64. f_equal. unfold u_fsz, u_fn, WIRE_RECV_MAX. cbn [u_n]. lia.
  + en_rg HS. apply en_v_reg. rewrite ?ew_ewset_other by lia. exact E10.
  + en_rg HS. rewrite (en_v_off _ 11 (-1) n) by (first [rewrite ?ew_ewset_other by lia; exact E11 | lia]).
    reflexivity.
  + en_saved1 HS 1%nat EE0 Usp.
Qed.
End sg.
