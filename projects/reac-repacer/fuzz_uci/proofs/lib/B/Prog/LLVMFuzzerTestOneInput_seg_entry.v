(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: the entry segment of the image-A walk of reac-repacer/fuzz_uci's LLVMFuzzerTestOneInput, in the form of proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v (en_entry, the run of the prologue by the Pa engine, reg_at / saved_tac) and LLVMFuzzerTestOneInput_seg_early.v (the input byte checked by the token rule, the branch on the size test): fuzz_uci.asan's prologue, its two shadow-checked loads and its first cut point. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, with its module paths, module names and numbers changed; 54 of its 483 lines of code are new or changed and 27 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_entry: u_entry_ok : u_entry_stmt (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v), the entry
   segment of the image-B walk of fuzz_uci.asan-ubsan's LLVMFuzzerTestOneInput, in the form of the image-A walk's
   lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v (the same symbolic entry state, region of MARGIN_MAX and closing
   lemma, at image B's registers and offsets).

   The run, by the Pa engine from the slot pre at +0x000 (uci_listing slots 0 .. 46):
   - +0x000 .. +0x03c: the frame (addi sp, sp, -0x90), the twelve saves, s0 = n, a1 = n >> 26 and `bnez a1` (to the
     early return at +0x220): the taken arm is refuted by the slot pre (n < 2 ^ 26);
   - +0x040 .. +0x050: s1 = p, the shadow base out of its GOT word (object 0 -> object 8 -> atom 32) into s5,
     `beqz s0`;
   - n = 0 (+0x08c .. +0x090): a0 = MARGIN_MAX (object 1), then +0x094;
     n > 0 (+0x054 .. +0x074): the UBSan check `beqz s1` (to `unimp` at +0x25c) is decided by the engine from the
     pointer fact of atom 10 (p >= 4096: A_EMPTY, or p's block in ablocks); data[0]'s shadow check (the token rule
     against the obligation that the input block discharges, YCbq.v obl_of_block); lbu; a0 = MARGIN_MAX; a1 = data[0]
     & 1. The run is cut at +0x078 and a1 is set to the literal bit (two cases); then a1 = 4 bit, a2 = ~MARGIN_MAX and
     the UBSan check `bltu a2, a1` (to `unimp` at +0x25c) is refuted (~0x20ca0 is far above 4: en_bltu_mm), so that
     a0 = MARGIN_MAX + 4 bit is a literal offset of object 1, and `j` to +0x094;
   - +0x094 .. +0x0b8: a0's shadow check (covered: the shadow entry of object 1, whose granule has shadow 0 by
     uci_cells' last row, so the slow path +0x260 and its report never run), s6 = 0, s7 = (n != 0), `lw s2` from the
     MARGIN_MAX region (1984 / 16320, the image's bytes through arodata_okS), s8 = (p != 0) = 1 (decided by the same
     pointer fact), s9 = sp + 0x1c, s10 = 5; the run is cut at +0xbc, the head of turn 0 (en_close). *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YCbq YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YM05 YE00 YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YE01 YImgTop.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YI16.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import YB1v YCfn.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require YE2k AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import PaRun PaShadow.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require Import PaJournal UciPSyms UciPList UciPAddr UciPPa
  UciPPaLib UciPImg UciCg.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require Import LLVMFuzzerTestOneInput_cg
  LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_seg_lib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YK11.
Module UCells := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.AsanCells.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ------------------------------------------------------------------ *)
(* 1. The symbolic state at +0x000                                      *)
(* ------------------------------------------------------------------ *)

(* Atoms: registers 0 .. 31 (Ereg), 32 the shadow base, 33 data[0] (0 when n = 0). Regions: the 0x90 bytes below the
   entry sp (atom 2), written; the GOT word of the shadow base (object 0) and the shadow-base cell (object 8); MARGIN_MAX
   (object 1, 8 bytes, read only). *)
Definition en_marg : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 1)) 0 8 0 0 [YP09.mkChunk 0 (CVal 4 (SLit U_MM0)); YP09.mkChunk 4 (CVal 4 (SLit U_MM1))].
Definition en_regions : smem := [stack_region U_FRAME; got_regionP; bcell_regionP 32; en_marg].
Definition en_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SBv SBv 0); (10%nat, PTR 0);
           (11%nat, mkAF 0 (2 ^ 26 - 1) 0); (A_OBJ 1, mkAF UCI_MARGIN_MAX UCI_MARGIN_MAX 3); (33%nat, mkAF 0 255 0)]
          [] [].
Definition ss_en : sstate := mkSS AF_LLVMFuzzerTestOneInput sr_atoms en_regions None en_facts.
Definition en_SH : list shent := [mkSHE (A_OBJ 1) 0 8].
Definition en_extra (d0 : Z) : list word := [Z_to_bv 64 SBv; Z_to_bv 64 d0].

(* The image's bytes of MARGIN_MAX (0x20ca0 .. 0x20ca7): 1984 and 16320 as little-endian int32. *)
Definition en_mm_rom (a : Z) : option Z := option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom tfibsegs (Z_to_bv 64 a)).
Lemma en_mm_bytes : forall k, (k < 4)%nat ->
  en_mm_rom (UCI_MARGIN_MAX + Z.of_nat k) = Some (le_byte U_MM0 4 k) /\
  en_mm_rom (UCI_MARGIN_MAX + 4 + Z.of_nat k) = Some (le_byte U_MM1 4 k).
Proof.
intros k Hk. do 4 (destruct k as [|k]; [split; vm_compute; reflexivity|]). lia.
Qed.

Section en. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation SEGS := (@pa_segs _ uci_listing PI_uci).
Local Abbreviation VAL := (@pa_val _ uci_listing PI_uci).
Local Abbreviation BASE := (@pa_val _ uci_listing PI_uci A_TEXT).
Definition EEN (regs : bvmap 5 word) (d0 : Z) : env := Eimg (PI := PI_uci) (Ereg regs (en_extra d0)).
Lemma en_vals : VAL (A_OBJ 0) = UCells.GOT_CELL_K /\ VAL (A_OBJ 8) = UCells.CELL_K /\ VAL (A_OBJ 1) = UCI_MARGIN_MAX.
Proof. vm_compute. repeat split. Qed.
Lemma en_srl26 : forall E v, ew E 11 = Z_to_bv 64 v -> 0 <= v < 2 ^ 26 ->
  U E (SAlu ALU_SRL (SOff 11 0) (SLit 26)) = 0.
Proof.
intros E v Hv Hr. rewrite U_SAlu, U_SLit, U_SOff, Hv, unsigned_lit_small by lia. cbn [zalu_raw].
change (Z.land (zcanon 26) 63) with 26. rewrite Z.add_0_r, (zcanon_id v) by (unfold M64; lia).
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.
Lemma en_denot_off : forall E n c v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n c) = Z_to_bv 64 (bv_unsigned (Z_to_bv 64 v) + c).
Proof. intros E n c v Hv. cbn [sv_denot]. rewrite Hv. reflexivity. Qed.
Lemma en_w64_off : forall v c, 0 <= v < 2 ^ 64 -> Z_to_bv 64 (bv_unsigned (Z_to_bv 64 v) + c) = w64 (v + c).
Proof. intros v c Hv. rewrite unsigned_lit_small by exact Hv. reflexivity. Qed.
Lemma en_bv_small : forall v, 0 <= v < 2 ^ 64 -> bv_unsigned (w64 v) = v.
Proof. intros v Hv. unfold w64. rewrite unsigned_lit_small by exact Hv. reflexivity. Qed.
Lemma en_sltu0 : forall E v, ew E 11 = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_SLTU (SLit 0) (SOff 11 0)) = w64 (if 0 <? v then 1 else 0).
Proof.
intros E v Hv Hr. rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu, U_SLit, U_SOff, Hv, unsigned_lit_small by lia. cbn [zalu_raw]. rewrite Z.add_0_r.
rewrite (zcanon_id v) by (unfold M64; lia). change (zcanon 0) with 0.
destruct (0 <? v); reflexivity.
Qed.
Lemma en_and1 : forall E d, ew E 33 = Z_to_bv 64 d -> 0 <= d < 256 ->
  sv_denot E (SAlu ALU_AND (SOff 33 0) (SLit 1)) = Z_to_bv 64 (Z.land d 1).
Proof.
intros E d Hd Hr. rewrite denot_lit_U. f_equal. rewrite U_and_lit by lia. rewrite (U_atom E 33 d Hd) by lia. reflexivity.
Qed.
Lemma en_land1 : forall d, 0 <= d -> Z.land d 1 = 0 \/ Z.land d 1 = 1.
Proof.
intros d Hd. assert (E : Z.land d 1 = d mod 2) by exact (Z.land_ones d 1 ltac:(lia)).
rewrite E. pose proof (Z.mod_pos_bound d 2 ltac:(lia)). lia.
Qed.

(* The view of MARGIN_MAX's bytes is the image's (arodata_okS at the two read-only facts of B). *)
Lemma en_mm_view : forall (B : asyms) RLO RHI (W : world SEGS) mem,
  uci_ro_rd_unowned B -> uci_rom_no_errno B ->
  arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) mem) ->
  forall a, UCI_MARGIN_MAX <= a < UCI_MARGIN_MAX + 8 -> aview SEGS (w_H W) mem a = en_mm_rom a.
Proof.
intros B RLO RHI W mem HOU HNE HRO a Ha.
assert (Hin : uci_in_ro_rd a) by (unfold uci_in_ro_rd, UCI_RO_RD; left; unfold in_zr; cbn [fst snd]; unfold UCI_MARGIN_MAX in *; lia).
destruct (uci_ro_rd_scoped B HOU HNE a Hin) as [Ho He].
destruct (uci_ro_rd_rom_clean a Hin) as [Hrom _].
apply HRO; [left; exact Hrom | exact Ho | exact He].
Qed.

Lemma en_entry : forall (B : asyms) RLO RHI ly S (W : world SEGS) (regs : bvmap 5 word) mem md (p n d0 : Z),
  AR SEGS B ly S W mem md -> uci_cells B -> uci_ro_rd_unowned B -> uci_rom_no_errno B ->
  arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) mem) ->
  (forall a, spZ regs - U_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  getr regs 10 = w64 p -> getr regs 11 = w64 n -> 4096 <= p <= 140737479966720 -> 0 <= n < 2 ^ 26 -> 0 <= d0 < 256 ->
  st_ok_pi SEGS VAL (EEN regs d0) ss_en
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_LLVMFuzzerTestOneInput)) mem (seg_rom SEGS))).
Proof.
intros B RLO RHI ly S W regs mem md p n d0 HAR HCELLS HOU HNE HRO Hpres Hsp Hsp16 R10 R11 Hp Hn Hd0.
destruct (HCELLS ly) as (I1 & I2 & _).
assert (CH : forall c, In c (as_const B ly) -> cell_holds B ly (aview SEGS (w_H W) mem) c).
{ intros c Hc. destruct HAR as (Mx & _). exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) c Hc). }
assert (Kcell : rdword (aview SEGS (w_H W) mem) UCells.CELL_K = Some UCells.ASAN_K)
  by (apply (rdword_cell B ly); [unfold UCells.ASAN_K; lia | exact (CH _ I1)]).
assert (Kgot : rdword (aview SEGS (w_H W) mem) UCells.GOT_CELL_K = Some UCells.CELL_K)
  by (apply (rdword_cell B ly); [unfold UCells.CELL_K; lia | exact (CH _ I2)]).
destruct en_vals as (V0 & V8 & V1).
rewrite restrict_mkst_fx. unfold ss_en.
set (E := EEN regs d0).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (en_extra d0)) n)
  by (intros nn Hnn; unfold E, EEN; apply Eimg_low; exact Hnn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E11 : ew E 11 = getr regs 11) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SBv) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 d0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (EO : forall i, (i < 10)%nat -> ew E (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)))
  by (intros i Hi; unfold E, EEN; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (EO 0%nat ltac:(lia)) as EO0. pose proof (EO 1%nat ltac:(lia)) as EO1. pose proof (EO 8%nat ltac:(lia)) as EO8.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
  by (intros nn v0 Hnn Hv0; cbn [base_val]; rewrite Hnn; apply unsigned_lit_small; exact Hv0).
assert (R0 : 0 <= VAL (A_OBJ 0) < 2 ^ 47) by (rewrite V0; unfold UCells.GOT_CELL_K; lia).
assert (R8 : 0 <= VAL (A_OBJ 8) < 2 ^ 47) by (rewrite V8; unfold UCells.CELL_K; lia).
assert (R1 : 0 <= VAL (A_OBJ 1) < 2 ^ 47) by (rewrite V1; unfold UCI_MARGIN_MAX; lia).
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold en_regions, stack_region, got_regionP, bcell_regionP, en_marg.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. unfold U_FRAME in *. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold U_FRAME in *. lia.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 8) 0) (VAL (A_OBJ 8)));
    [cbn [sv_denot]; rewrite EO8, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r, V0, V8. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + rewrite (VB (A_OBJ 8) (VAL (A_OBJ 8)) EO8) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 8)) 0 8 (SOff 32 0) SBv);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SBv; zside | zside |].
    rewrite Z.add_0_r, V8. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    rewrite V1.
    assert (MV : forall k, (k < 4)%nat ->
      aview SEGS (w_H W) mem (UCI_MARGIN_MAX + Z.of_nat k) = Some (le_byte U_MM0 4 k) /\
      aview SEGS (w_H W) mem (UCI_MARGIN_MAX + 4 + Z.of_nat k) = Some (le_byte U_MM1 4 k)).
    { intros k Hk. rewrite !(en_mm_view B RLO RHI W mem HOU HNE HRO) by (unfold UCI_MARGIN_MAX; lia).
      exact (en_mm_bytes k Hk). }
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS E _ UCI_MARGIN_MAX 0 4 (SLit U_MM0) U_MM0); [reflexivity | vm_compute; split; congruence | zside |].
      rewrite Z.add_0_r. apply val_mem_of_rd32. intros k Hk. exact (proj1 (MV k Hk)).
    * apply (chunk_ok_val SEGS E _ UCI_MARGIN_MAX 4 4 (SLit U_MM1) U_MM1); [reflexivity | vm_compute; split; congruence | zside |].
      apply val_mem_of_rd32. intros k Hk. exact (proj2 (MV k Hk)).
- apply pairwise_disjoint_of_extents.
  unfold en_regions, stack_region, got_regionP, bcell_regionP, en_marg, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0), (VB (A_OBJ 8) (VAL (A_OBJ 8)) EO8), (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1) by lia.
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  rewrite V0, V8, V1. unfold UCells.GOT_CELL_K, UCells.CELL_K, UCI_MARGIN_MAX, U_FRAME.
  repeat split; first [exact I | lia].
- split; [|split; [exact I | exact I]].
  cbn [en_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32, E33, E10, E11, R10, R11, EO1, V1.
  rewrite !unsigned_lit_small by (unfold SBv, UCI_MARGIN_MAX; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SBv, UCI_MARGIN_MAX in *; first [lia | reflexivity].
Qed.

(* The shadow entry of object 1: MARGIN_MAX's granule has shadow 0 (uci_cells' last row, read by uci_tab_zshadow_rd). *)
Lemma en_shok : forall (B : asyms) ly S (W : world SEGS) (regs : bvmap 5 word) mem md (d0 : Z),
  AR SEGS B ly S W mem md -> uci_cells B ->
  sh_ok SEGS (SOff 32 0) en_SH (EEN regs d0) (mrestrict (w_H W) mem).
Proof.
intros B ly S W regs mem md d0 HAR HCELLS.
destruct (HCELLS ly) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HZ).
pose proof (uci_tab_zshadow_rd B ly S W mem md UCI_MARGIN_MAX HAR ltac:(reflexivity) HZ) as Hz.
destruct en_vals as (_ & _ & V1).
assert (U32 : U (EEN regs d0) (SOff 32 0) = SHADOW_OFF).
{ assert (E32 : ew (Ereg regs (en_extra d0)) 32 = Z_to_bv 64 SBv) by exact (ew_Ereg_extra regs _ 0).
  rewrite U_SOff. unfold EEN. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite E32.
  rewrite Z.add_0_r, unsigned_lit_small by (unfold SBv; lia). reflexivity. }
assert (U242 : U (EEN regs d0) (SOff (A_OBJ 1) 0) = UCI_MARGIN_MAX).
{ rewrite U_SOff. unfold EEN. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite V1.
  rewrite Z.add_0_r, unsigned_lit_small by (unfold UCI_MARGIN_MAX; lia). reflexivity. }
constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem (EEN regs d0) (SOff 32 0) (A_OBJ 1) UCI_MARGIN_MAX 8 UCI_MARGIN_MAX 0 8);
  [| exact U32 | exact U242 | lia | lia | intros x Hx; unfold UCI_MARGIN_MAX, SHADOW_OFF in *; lia].
intros x Hx. exists 0. split; [|left; reflexivity].
replace (shadow_of_addr SHADOW_OFF x) with (UCells.shadow_addr UCI_MARGIN_MAX); [exact Hz|].
unfold shadow_of_addr, UCells.shadow_addr, UCells.ASAN_K, SHADOW_OFF, UCI_MARGIN_MAX in *. lia.
Qed.

(* The stack region as the prologue leaves it: the twelve saved words, each the entry value of its register. *)
Definition en_saved : list YP09.chunk :=
  [YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0));
   YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0));
   YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
   YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
   YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
   YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].


(* The UBSan wrap check of MARGIN_MAX + 4 bit (+0x80 `bltu a2, a1`, a2 = ~MARGIN_MAX, a1 = 4 bit <= 4) never branches. *)
Lemma en_bltu_mm : forall E k, img_env VAL A_LIM E -> k <= 4 ->
  U E (SAlu ALU_XOR (SOff (A_OBJ 1) 0) (SLit (-1))) < k -> False.
Proof.
intros E k HE Hk Hc.
assert (V : U E (SAlu ALU_XOR (SOff (A_OBJ 1) 0) (SLit (-1))) = 2 ^ 64 - 1 - UCI_MARGIN_MAX).
{ rewrite U_SAlu, U_SLit, (U_img_atom _ HE (A_OBJ 1)) by (unfold A_OBJ, A_TEXT, A_LIM; lia). vm_compute. reflexivity. }
rewrite V in Hc. unfold UCI_MARGIN_MAX in Hc. lia.
Qed.

(* The closing of a path at +0xbc: a symbolic state with the registers and the stack region the three paths of the
   prologue end with is the head of turn 0 (s0 = n, s1 = p, s2 = MARGIN_MAX[bit], s5 = the shadow base, s6 = 0,
   s7 = (n != 0), s8 = 1, s9 = sp1 + 0x1c, s10 = 5). *)
Lemma en_close : forall (B : asyms) (MT : ameter_ops) (XL : Z -> Z) ly S (W : world SEGS) (regs : bvmap 5 word) mem md
    p n pl M d0 Ex ss ms md' mmv,
  ameter_laws MT -> frames S = [] -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> mo_ok MT S (XL n) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> getr regs 10 = w64 p -> getr regs 11 = w64 n -> 0 <= n < 2 ^ 26 ->
  @ajournal rc YE2k.tfib_sink_head SEGS B LLVMF_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem ms) md' 0 ->
  st_ok_pi SEGS VAL Ex ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = U_OH ->
  (forall k, (k < 512)%nat -> ew Ex k = ew (EEN regs d0) k) ->
  In (YP09.mkRegion (Some 2%nat) (-144) 0 (-144) 0 en_saved) (ss_mem ss) ->
  sr_get (ss_regs ss) 2 = SOff 2 (-144) -> sr_get (ss_regs ss) 3 = SOff 3 0 -> sr_get (ss_regs ss) 4 = SOff 4 0 ->
  sr_get (ss_regs ss) 8 = SOff 11 0 -> sr_get (ss_regs ss) 9 = SOff 10 0 -> sr_get (ss_regs ss) 18 = SLit mmv ->
  (mmv = U_MM0 \/ mmv = U_MM1) ->
  sr_get (ss_regs ss) 21 = SOff 32 0 -> sr_get (ss_regs ss) 22 = SLit 0 ->
  sr_get (ss_regs ss) 23 = SAlu ALU_SLTU (SLit 0) (SOff 11 0) -> sr_get (ss_regs ss) 24 = SLit 1 ->
  sr_get (ss_regs ss) 25 = SOff 2 (-116) -> sr_get (ss_regs ss) 26 = SLit 5 -> sr_get (ss_regs ss) 27 = SOff 27 0 ->
  u_st_oh B MT XL (mkUCx fx ly S W regs mem md p n pl M) 0 W (mkCfg ms md').
Proof.
intros B MT XL ly S W regs mem md p n pl M d0 Ex ss ms md' mmv MTL Hfrs Hgp Htp Hmo Hsp R10 R11 Hn HJ HS Hrv Hpc EA
  Hin S2 S3 S4 S8 S9 S18 Hmm S21 S22 S23 S24 S25 S26 S27.
assert (EE : forall k (r : bv 5), (k < 32)%nat -> Z.of_nat k = bv_unsigned r -> ew Ex k = getr regs r).
{ intros k r Hk Hkr. rewrite (EA k) by lia. unfold EEN. apply ew_Eimg_Ereg_nat. exact Hkr. }
assert (E32 : ew Ex 32 = Z_to_bv 64 SBv).
{ rewrite (EA 32%nat) by lia. unfold EEN. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
assert (RG : forall (r : bv 5) e, sr_get (ss_regs ss) r = e -> getr (ms_regs ms) r = sv_denot Ex e).
{ intros r e He. rewrite <- He. exact (st_ok_pi_restrict_reg (w_H W) Ex ss ms r HS). }
assert (Usp : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite (EE 2%nat 2%bv) by (lia || reflexivity); reflexivity).
pose proof (st_ok_pi_restrict_mkst (w_H W) Ex ss ms HS Hrv) as Hms.
assert (HR0 : region_ok SEGS Ex (mrestrict (w_H W) (ms_mem ms)) (YP09.mkRegion (Some 2%nat) (-144) 0 (-144) 0 en_saved)).
{ destruct (st_ok_mem_ok SEGS Ex (abs_ss VAL ss) (restrict (w_H W) ms) HS) as (_ & Hrs & _).
  exact (proj1 (Forall_forall _ _) Hrs _ ltac:(destruct ss; exact Hin)). }
rewrite Hms, Hpc.
exists ly, S, (ms_regs ms), (ms_mem ms), md', (if 0 <? n then 1 else 0), mmv, (@nil Z).
cbn [u_ly u_S u_W u_regs u_mem u_md u_p u_n u_pl u_M u_fx].
split; [reflexivity|].
split.
{ split; [rewrite Z.mul_0_l; exact HJ|].
  split; [exact Hfrs|].
  split; [unfold spZ at 1; rewrite (RG 2%bv _ S2); cbn [sv_denot]; rewrite Usp; unfold u_sp1, u_sp0, U_FRAME;
          cbn [u_regs]; rewrite unsigned_lit_small by lia; lia|].
  split; [rewrite (RG 3%bv _ S3); cbn [sv_denot]; rewrite (EE 3%nat 3%bv) by (lia || reflexivity);
          rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp|].
  split; [rewrite (RG 4%bv _ S4); cbn [sv_denot]; rewrite (EE 4%nat 4%bv) by (lia || reflexivity);
          rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp|].
  split; [rewrite (RG 27%bv _ S27); cbn [sv_denot]; rewrite (EE 27%nat 27%bv) by (lia || reflexivity);
          rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
  split; [|apply Permutation_refl].
  unfold u_saved, uci_saved_at, u_sp0; cbn [u_regs].
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  lazymatch goal with |- rdword _ (spZ regs - ?off) = Some (bv_unsigned (getr regs (Z_to_bv 5 ?r))) =>
    let rn := eval vm_compute in (Z.to_nat r) in
    rewrite <- (EE rn (Z_to_bv 5 r)) by (vm_compute; first [reflexivity | lia]);
    apply rdword_of_val_mem;
    [ replace (spZ regs - off) with (spZ regs + (- off)) by lia;
      eapply (saved_slot _ _ _ _ _ _ _ _ _ (- off) rn (spZ regs) HR0 Usp);
      unfold en_saved; cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right])
    | let w := fresh "w" in pose proof (bv_unsigned_in_range 64 (ew Ex rn)) as w;
      change (bv_modulus 64) with (2 ^ 64) in w; exact w ]
  end. }
split; [split; [rewrite Z.mul_0_l; apply (mo_le_refl MT MTL) | rewrite Z.mul_0_l, Z.sub_0_r; exact Hmo]|].
split.
{ unfold u_lregs; cbn [u_n u_p u_regs].
  split; [rewrite (RG 8%bv _ S8); cbn [sv_denot]; rewrite (EE 11%nat 11%bv) by (lia || reflexivity); rewrite R11, Z.add_0_r;
          unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
  split; [rewrite (RG 9%bv _ S9); cbn [sv_denot]; rewrite (EE 10%nat 10%bv) by (lia || reflexivity); rewrite R10, Z.add_0_r;
          unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
  split; [rewrite (RG 18%bv _ S18); reflexivity|].
  split; [exact Hmm|].
  split; [rewrite (RG 21%bv _ S21); cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
  split; [rewrite (RG 22%bv _ S22); reflexivity|].
  split; [rewrite (RG 23%bv _ S23); apply (en_sltu0 Ex n); [rewrite (EE 11%nat 11%bv) by (lia || reflexivity); exact R11 | lia]|].
  split; [rewrite (RG 24%bv _ S24); reflexivity|].
  split; [rewrite (RG 25%bv _ S25); cbn [sv_denot]; rewrite Usp; unfold u_sp1, u_sp0, U_FRAME; cbn [u_regs];
          unfold w64; f_equal; lia|].
  rewrite (RG 26%bv _ S26); reflexivity. }
split; [destruct (Z.ltb_spec 0 n); lia|].
split; [reflexivity|]. split; [constructor|]. intros jj Hjj. lia.
Qed.
End en.

(* ------------------------------------------------------------------ *)
(* 2. The segment                                                       *)
(* ------------------------------------------------------------------ *)

Ltac awr_ro_rec := first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]; awr_ro_rec ].
(* The write rights of a run of this segment: the stack region (atom 2 = the entry sp) in the entry's stack window,
   every other region read only. *)
Ltac en_awr Usp Hstkv :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0);
    [reflexivity | rewrite ?ew_ewset_other by lia; rewrite Usp; lia | cbn; rewrite Hstkv; lia | cbn; lia |] ].
(* The symbolic value of register r in the machine state of HS. *)
Ltac ureg HS r H :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?msx) =>
    pose proof (st_ok_pi_restrict_reg Hh Ex ss msx r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H
  end.
(* The model after a run, named and opaque. *)
Ltac en_md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
    let md2 := fresh "md" in set (md2 := mdx) in *; clearbody md2 end.
Ltac en_norm HS :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?ms => let v := eval vm_compute in ss in change ss with v in HS end.


Section sg. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
(* The closing of a path at +0xbc by en_close. *)
Local Ltac en_fin mmv d0 MTL Hfrs Hgp Htp Hmo Hsp H10 H11 Hn26 HJ HS :=
  apply SRr_ret;
  eapply (en_close _ _ _ _ _ _ _ _ _ _ _ _ _ d0);
  [ exact MTL | exact Hfrs | exact Hgp | exact Htp | exact Hmo | exact Hsp | exact H10 | exact H11 | exact Hn26
  | exact HJ | exact HS | reflexivity | reflexivity
  | intros kk Hkk; rewrite ?ew_ewset_other by lia; reflexivity
  | cbn [ss_mem In]; repeat (first [left; reflexivity | right])
  | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
  | unfold U_MM0, U_MM1; lia
  | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity ].
(* The UBSan check at +0x80 by en_bltu_mm, at the image environment of the run that reached it. *)
Local Ltac en_bltu Hc :=
  exfalso; rewrite branch_ltu_U, U_lit in Hc by lia; apply Z.ltb_lt in Hc;
  lazymatch type of Hc with U ?Ex _ < ?k =>
    lazymatch goal with HE : img_env _ _ Ex |- _ => exact (en_bltu_mm Ex k HE ltac:(lia) Hc) end end.

Theorem u_entry_ok : u_entry_stmt B MT XL RLO RHI.
Proof.
intros HP cx HB.
pose proof (up_cells _ _ _ _ _ HP) as HCELLS. pose proof (up_ro_unowned _ _ _ _ _ HP) as HOU.
pose proof (up_rom_no_errno _ _ _ _ _ HP) as HNE. pose proof (up_laws _ _ _ _ _ HP) as LAWS.
pose proof (up_meter_laws _ _ _ _ _ HP) as MTL.
destruct cx as [fx ly S W regs mem md p n pl M].
unfold u_base, tfib_lib_pre_x in HB. cbn [u_fx u_ly u_S u_W u_regs u_mem u_md u_p u_n u_pl u_M] in *.
destruct HB as (HAFN & Hra & H10 & H11 & Hpn & Hlen & Hgarr & Hfrs & Hnev & Hbb & Haro & Hsink & Hfd & Hfs & Hmeta & Hmo).
pose proof HAFN as (HAR & Hret & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hstkv : LLVMF_STK = 32768) by reflexivity.
assert (Hn26 : 0 <= n < 2 ^ 26) by (destruct Hpn as [(-> & _) | (Hn & _)]; lia).
assert (Hp : 4096 <= p <= 140737479966720).
{ destruct Hpn as [(_ & ->) | (Hn & Hin)]; [unfold A_EMPTY; lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & Hb1 & Hb3 & _).
  pose proof (req_size_pos n ltac:(lia)) as Hrq. lia. }
set (d0 := match pl with [] => 0 | b :: _ => bv_unsigned b end).
assert (Hd0 : 0 <= d0 < 256).
{ unfold d0. destruct pl as [|b pl']; [lia|]. pose proof (bv_unsigned_in_range 8 b) as Hb. exact Hb. }
pose proof (en_entry B RLO RHI ly S W regs mem md p n d0 HAR HCELLS HOU HNE Haro
  ltac:(intros a Ha; apply Hpres; unfold U_FRAME in Ha; lia) ltac:(lia) Hsp16 H10 H11 Hp Hn26 Hd0) as HS.
pose proof (ajournal_init (SK := YE2k.tfib_sink_head) segs B LLVMF_STK [] ly S W regs mem md [] HAFN) as HJ.
pose proof (en_shok B ly S W regs mem md d0 HAR HCELLS) as SHOK.
assert (HEI : img_env (@pa_val _ uci_listing PI_uci) A_LIM (EEN regs d0)) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (EEN regs d0) n = getr regs r)
  by (intros nn r Hnn; unfold EEN; apply ew_Eimg_Ereg_nat; exact Hnn).
assert (E2 : ew (EEN regs d0) 2 = getr regs 2) by exact (EE 2%nat 2%bv eq_refl).
assert (Usp : bv_unsigned (ew (EEN regs d0) 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E10 : ew (EEN regs d0) 10 = w64 p) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (E11 : ew (EEN regs d0) 11 = w64 n) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11).
assert (E32 : ew (EEN regs d0) 32 = Z_to_bv 64 SBv)
  by (unfold EEN; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew (EEN regs d0) 33 = Z_to_bv 64 d0)
  by (unfold EEN; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
set (E0 := EEN regs d0) in *.
pose proof (paj_run (fx := fx) (SK := YE2k.tfib_sink_head) (PI := PI_uci) B LAWS) as RUN.
pose proof (paj_run_to (fx := fx) (SK := YE2k.tfib_sink_head) (PI := PI_uci) B LAWS) as RUNTO.
pose proof (@paj_branch fx rc uci_listing PI_uci) as BR.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr (@pa_segs _ uci_listing PI_uci) Wx
    (mkCfg (mkst regs (Z_to_bv 64 (@pa_val _ uci_listing PI_uci A_TEXT + AF_LLVMFuzzerTestOneInput)) mem
      (seg_rom (@pa_segs _ uci_listing PI_uci))) md) Q) end.
(* +0x000 .. +0x03c: the frame, the saves, s0 = n, a1 = n >> 26. *)
paj_run_tok RUN HS HJ SHOK Bspan; [en_awr Usp Hstkv|]. en_md.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ (* n >> 26 <> 0 (the early return at +0x220): refuted by the slot pre *)
  exfalso. rewrite branch_ne_U, (en_srl26 _ n ltac:(rewrite ?ew_ewset_other by lia; exact E11) Hn26), U_lit in Hc by lia.
  discriminate Hc. }
clear Hc.
(* +0x040 .. +0x050: s1 = p, the shadow base into s5, `beqz s0`. *)
paj_run_tok RUN HS HJ SHOK Bspan; [en_awr Usp Hstkv|]. en_md.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ (* n = 0 (+0x08c): a0 = MARGIN_MAX, MARGIN_MAX[0], up to the head of turn 0. *)
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 188; [en_awr Usp Hstkv|]. en_md.
  en_fin U_MM0 d0 MTL Hfrs Hgp Htp Hmo Hsp H10 H11 Hn26 HJ HS. }
(* n <> 0 *)
assert (Hn0 : n <> 0).
{ rewrite branch_eq_U, (U_atom _ 11 n ltac:(rewrite ?ew_ewset_other by lia; exact E11)), U_lit in Hc by lia.
  intros Hz. rewrite Hz in Hc. discriminate Hc. }
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
    | change (8 * Z.of_N 1) with 8; lia | zside | rewrite Z.add_0_r; exact Hb0'].
}
{ pose proof (blk_off_imgP (PI := PI_uci) B ly S W mem md p n HAR Hin) as Hoff. unfold off_img in Hoff.
  pose proof (req_size_pos n ltac:(lia)) as Hrq.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & Hb1 & Hb3 & _).
  pose proof (pa_obj_img (L := uci_listing) 0%nat ltac:(lia)) as O0.
  pose proof (pa_obj_img (L := uci_listing) 1%nat ltac:(lia)) as O1.
  pose proof (pa_obj_img (L := uci_listing) 8%nat ltac:(lia)) as O8.
  lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
    let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
  cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite ?ew_ewset_other by lia.
  rewrite E10, Usp, en_bv_small by lia.
  unfold E0, EEN. rewrite !(Eimg_img (PI := PI_uci)) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  change (pa_val 241) with UCells.GOT_CELL_K. change (pa_val 242) with UCI_MARGIN_MAX. change (pa_val 249) with UCells.CELL_K.
  rewrite !unsigned_lit_small by (unfold UCells.GOT_CELL_K, UCells.CELL_K, UCI_MARGIN_MAX; lia).
  unfold UCells.GOT_CELL_K, UCells.CELL_K, UCI_MARGIN_MAX. repeat split; lia. }
en_norm HS.
(* +0x054 .. +0x074: `beqz s1` (decided: p >= 4096 by the fact of atom 10), data[0]'s shadow check (the token rule),
   lbu, a0 = MARGIN_MAX, a1 = data[0] & 1, up to +0x078. *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan 120.
{ eapply (obl_of_block segs B LAWS ly S W _ _ _ (SOff 32 0) _ 1 p n (proj1 HJ) Hin).
  - rewrite (U_atom _ 32 SBv) by (rewrite ?ew_ewset_other by lia; first [exact E32 | unfold SBv; lia]). reflexivity.
  - rewrite (U_atom _ 10 p) by (rewrite ?ew_ewset_other by lia; first [exact E10 | lia]). lia.
  - rewrite (U_atom _ 10 p) by (rewrite ?ew_ewset_other by lia; first [exact E10 | lia]).
    pose proof (req_size_pos n ltac:(lia)) as Hrq. lia. }
{ en_awr Usp Hstkv. }
en_md.
(* a1 = bit as a literal, two cases *)
pose proof (en_land1 d0 ltac:(lia)) as Hbit.
lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?msx) =>
  assert (Ra1 : getr (ms_regs (restrict Hh msx)) 11 = Z_to_bv 64 (Z.land d0 1));
  [ cbn [ms_regs restrict]; rewrite (st_ok_pi_restrict_reg Hh Ex ss msx 11 HS);
    let e := eval vm_compute in (sr_get (ss_regs ss) 11) in change (sr_get (ss_regs ss) 11) with e;
    apply en_and1; [rewrite ?ew_ewset_other by lia; exact E33 | lia]
  | ]
end.
destruct Hbit as [Hbit | Hbit]; rewrite Hbit in Ra1.
- lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?msx =>
    let HS2 := fresh "HS" in
    pose proof (st_ok_pi_set_reg Ex ss msx 11 (SLit 0) HS
      ltac:(intros Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate Hq) Ra1) as HS2;
    clear HS; rename HS2 into HS end.
  en_norm HS.
  (* +0x078 .. +0x080: a1 = 0, a2 = ~MARGIN_MAX, the UBSan check `bltu a2, a1` *)
  paj_run_tok RUN HS HJ SHOK Bspan; [en_awr Usp Hstkv|]. en_md.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  { en_bltu Hc. }
  clear Hc.
  (* +0x084 .. +0x0b8: a0 = MARGIN_MAX, MARGIN_MAX[0], up to the head of turn 0 *)
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 188; [en_awr Usp Hstkv|]. en_md.
  en_fin U_MM0 d0 MTL Hfrs Hgp Htp Hmo Hsp H10 H11 Hn26 HJ HS.
- lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?msx =>
    let HS2 := fresh "HS" in
    pose proof (st_ok_pi_set_reg Ex ss msx 11 (SLit 1) HS
      ltac:(intros Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate Hq) Ra1) as HS2;
    clear HS; rename HS2 into HS end.
  en_norm HS.
  (* +0x078 .. +0x080: a1 = 4, a2 = ~MARGIN_MAX, the UBSan check `bltu a2, a1` *)
  paj_run_tok RUN HS HJ SHOK Bspan; [en_awr Usp Hstkv|]. en_md.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  { en_bltu Hc. }
  clear Hc.
  (* +0x084 .. +0x0b8: a0 = MARGIN_MAX + 4, MARGIN_MAX[1], up to the head of turn 0 *)
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 188; [en_awr Usp Hstkv|]. en_md.
  en_fin U_MM1 d0 MTL Hfrs Hgp Htp Hmo Hsp H10 H11 Hn26 HJ HS.
Qed.
End sg.
