(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk kit of rec_shape_of on fuzz_command.asan (0x891ec), in the form of
   proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (cgif_close's offsets, symbolic register files, regions and seeds):
   the loop head, the two return sites of the wrapper calls, the frame of eleven saved registers, the row of the
   read-only table g_shapes that iteration i reads, and the shadow entries the inline checks are discharged
   against. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib PaSB CmdAddr CmdObj CmdChk CmdRo PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdBase CmdRep rec_shape_of_c.
From Stdlib Require Import Permutation.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* program points, as listing offsets (M: the listing of 0x891ec, 69 slots) *)
Definition RS_HEAD : Z := AF_rec_shape_of + 0x68.
Definition RS_R1 : Z := AF_rec_shape_of + 0x7c.
Definition RS_R2 : Z := AF_rec_shape_of + 0x90.
Definition RS_LATCH : Z := AF_rec_shape_of + 0x94.
(* the registers the prologue saves, in the order of the frame from its top: ra at sp+88 down to s9 at sp+8 *)
Definition rso_saved : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25].
(* g_shapes' 28 rows as the pinned image holds them (M: RO_g_shapes of lib/A/Prog/CmdRo.v): name, reply *)
Definition RSO_ROWS : list (Z * Z) :=
[(0x21fc0, 0x21fe0); (0x21d80, 0x22000); (0x21da0, 0x22060); (0x21dc0, 0x21ce0); (0x21e00, 0x21ce0);
 (0x21e40, 0x21ce0); (0x21e80, 0x21ce0); (0x21ec0, 0x21ce0); (0x220c0, 0x21ce0); (0x220e0, 0x21ce0);
 (0x21ea0, 0x21ce0); (0x21e60, 0x21ce0); (0x22100, 0x22120); (0x22160, 0x21ce0); (0x21f20, 0x21ce0);
 (0x21f40, 0x21ce0); (0x21f60, 0x22180); (0x21f80, 0x22180); (0x221a0, 0x21ce0); (0x221c0, 0x221e0);
 (0x22200, 0x22220); (0x222a0, 0x222c0); (0x22340, 0x221e0); (0x22360, 0x22380); (0x223c0, 0x223e0);
 (0x22420, 0x21ce0); (0x22440, 0x21ce0); (0x22460, 0x21ce0)].
Definition rso_nm (i : Z) : Z := fst (nth (Z.to_nat i) RSO_ROWS (0, 0)).
Definition rso_rp (i : Z) : Z := snd (nth (Z.to_nat i) RSO_ROWS (0, 0)).
(* the row's strings in the model, lib/Prog/RecFacts.v:280-309 *)
Definition rso_name (i : Z) : list byte := fst (nth (Z.to_nat i) shape_table ([], [])).
Definition rso_reply (i : Z) : list byte := snd (nth (Z.to_nat i) shape_table ([], [])).
(* atoms: 0..31 registers, 32 the shadow base, 33..43 the values the prologue saves (rso_saved order) *)
Definition RBx : sv := SOff 32 0.
Definition RBspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rshx (n : nat) (c : Z) : sv := SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff n c) (SLit 3)).
Definition rso_frame_region : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 96 0 0
(map (fun j => YP09.mkChunk (88 - 8 * Z.of_nat j) (CVal 8 (SOff (33 + j) 0))) (seq 0 11)).
Definition rso_row_region (i : Z) : YP09.region :=
YP09.mkRegion (Some (A_OBJ 41)) (16 * i) (16 * i + 16) 0 0
[YP09.mkChunk (16 * i) (CVal 8 (SLit (rso_nm i))); YP09.mkChunk (16 * i + 8) (CVal 8 (SLit (rso_rp i)))].
Definition rso_regions (i : Z) : smem := [rso_frame_region; rso_row_region i].
Definition rso_atom_facts : list (nat * afact) :=
[(2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0);
 (A_OBJ 41, mkAF 0xa5ec0 0xa5ec0 3); (A_OBJ 43, mkAF 0xa5ec8 0xa5ec8 3)].
Definition rso_SH : list shent := [mkSHE (A_OBJ 41) 0 448; mkSHE (A_OBJ 43) 0 440].
(* the registers at the loop head of iteration i (0x89254) *)
Definition rso_regs_head (i : Z) : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
18 (SOff (A_OBJ 41) (16 * i))) 19 (SOff (A_OBJ 42) 0)) 21 (SLit (zcanon (- (2 * i)))))
22 (SOff (A_OBJ 41) (16 * i + 8))) 23 (SOff 32 0)) 24 (rshx (A_OBJ 41) (16 * i))) 25 (SLit (zcanon (-56))).
(* the found-branch check (0x892ac) addresses the shadow of g_shapes + 8 + 16 i as (s7 + ((g_shapes + 8) >> 3)) - s5;
   the alias names that value in the form the token executor recognises (MEASURED: the executor's own s_alu2 form) *)
Definition rso_key (i : Z) : sv := SAlu ALU_SUB (rshx (A_OBJ 43) 0) (SLit (zcanon (- (2 * i)))).
Definition rso_facts (i : Z) : facts := mkFacts rso_atom_facts [] [(rso_key i, rshx (A_OBJ 43) (16 * i))].
Definition ss_rso (pc : Z) (sregs : list sv) (i : Z) : sstate := mkSS pc sregs (rso_regions i) None (rso_facts i).
Definition rso_extra (regs : bvmap 5 word) : list word :=
Z_to_bv 64 SB :: map (fun r => getr regs (Z_to_bv 5 r)) rso_saved.
Lemma RSO_ROWS_range : Forall (fun r => 0 <= fst r < 2 ^ 32 /\ 0 <= snd r < 2 ^ 32) RSO_ROWS.
Proof. unfold RSO_ROWS. repeat constructor; cbn; lia. Qed.
Lemma rso_nm_range : forall i, 0 <= rso_nm i < 2 ^ 32.
Proof.
intros i. unfold rso_nm. destruct (nth_in_or_default (Z.to_nat i) RSO_ROWS (0, 0)) as [Hin | ->]; [|cbn; lia].
exact (proj1 (proj1 (Forall_forall _ _) RSO_ROWS_range _ Hin)).
Qed.
Lemma rso_rp_range : forall i, 0 <= rso_rp i < 2 ^ 32.
Proof.
intros i. unfold rso_rp. destruct (nth_in_or_default (Z.to_nat i) RSO_ROWS (0, 0)) as [Hin | ->]; [|cbn; lia].
exact (proj2 (proj1 (Forall_forall _ _) RSO_ROWS_range _ Hin)).
Qed.
Lemma U_rshx : forall E n c v, ew E 32 = Z_to_bv 64 SB -> ew E n = Z_to_bv 64 v -> 0 <= v -> 0 <= c -> v + c < 2 ^ 63 ->
U E (rshx n c) = SB + (v + c) / 8.
Proof.
intros E n c v H32 Hn Hv Hc0 Hc. unfold rshx.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, H32, Hn.
rewrite !unsigned_lit_small by (unfold SB; lia). rewrite Z.add_0_r.
change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos (v + c) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (v + c) 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (YP0m.zcanon_small (v + c)) by lia. rewrite (YP0m.zcanon_small ((v + c) / 8)) by lia. rewrite (YP0m.zcanon_small SB) by (unfold SB; lia).
rewrite YP0m.zcanon_small by (unfold SB; lia). reflexivity.
Qed.
Lemma rso_div8 : forall b i, b mod 8 = 0 -> (b + 16 * i) / 8 = b / 8 + 2 * i.
Proof.
intros b i Hb. rewrite (Z.div_mod b 8) at 1 by lia. rewrite Hb, Z.add_0_r.
replace (8 * (b / 8) + 16 * i) with ((b / 8 + 2 * i) * 8) by lia. apply Z.div_mul. lia.
Qed.
Lemma rso_key_arith : forall i, 0 <= i < 28 -> YP0m.zcanon (SB + 84953 - YP0m.zcanon (YP0m.zcanon (- (2 * i)))) = SB + (84953 + 2 * i).
Proof.
intros i Hi. unfold YP0m.zcanon, YP0m.M64. rewrite (Z.mod_mod (- (2 * i))) by lia. rewrite Zminus_mod_idemp_r.
rewrite Z.mod_small; [lia | unfold SB; lia].
Qed.
Lemma U_rso_key : forall E i, ew E 32 = Z_to_bv 64 SB -> ew E (A_OBJ 43) = Z_to_bv 64 0xa5ec8 -> 0 <= i < 28 ->
U E (rso_key i) = SB + (0xa5ec8 + 16 * i) / 8.
Proof.
intros E i H32 H43 Hi. unfold rso_key. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_rshx E (A_OBJ 43) 0 0xa5ec8 H32 H43) by lia. rewrite U_SLit.
rewrite rso_div8 by reflexivity. rewrite Z.add_0_r.
change (679624 / 8) with 84953. exact (rso_key_arith i Hi).
Qed.
Lemma In_Z_of_existsb : forall x l, existsb (Z.eqb x) l = true -> In x l.
Proof. intros x l H. apply existsb_exists in H as (y & Hy & E). apply Z.eqb_eq in E. subst y. exact Hy. Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the frame the prologue writes: register rso_saved[j] at sp0 - 8 - 8 j *)
Definition rso_frame (m : word -> option byte) (sp0 : Z) (regs : bvmap 5 word) : Prop :=
forall j r, nth_error rso_saved j = Some r -> val_mem SEGS m (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
Lemma rso_val_objs : cmd_val_objs -> VAL (A_OBJ 41) = 0xa5ec0 /\ VAL (A_OBJ 42) = 0x21ce0 /\ VAL (A_OBJ 43) = 0xa5ec8.
Proof.
intros H. split; [|split].
- rewrite (H 41%nat ltac:(vm_compute; lia)). reflexivity.
- rewrite (H 42%nat ltac:(vm_compute; lia)). reflexivity.
- rewrite (H 43%nat ltac:(vm_compute; lia)). reflexivity.
Qed.
Lemma rso_seed : forall pc sregs i (W1 : world SEGS) (regs regs1 : bvmap 5 word) mem1 sp0,
cmd_val_objs -> 0 <= i < 28 -> regions_wf (rso_regions i) = true ->
alloc_ceiling <= sp0 - 96 -> sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 ->
bv_unsigned (getr regs1 2) = sp0 - 96 ->
regs_ok (Eimg (Ereg regs1 (rso_extra regs))) sregs regs1 ->
rso_frame (mrestrict (w_H W1) mem1) sp0 regs ->
rdword (rdW W1 mem1) (0xa5ec0 + 16 * i) = Some (rso_nm i) ->
rdword (rdW W1 mem1) (0xa5ec8 + 16 * i) = Some (rso_rp i) ->
range_addressable (rdW W1 mem1) SHADOW_OFF 0xa5ec0 448 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (rso_extra regs))) (ss_rso pc sregs i)
(restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + pc)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS RBx rso_SH (Eimg (Ereg regs1 (rso_extra regs))) (mrestrict (w_H W1) mem1).
Proof.
intros pc sregs i W1 regs regs1 mem1 sp0 HVO Hi Hwf Hceil H47 Hal Hsp HREG HFR Hnm Hrp HZ.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (rso_val_objs HVO) as (V41 & V42 & V43).
pose proof (rso_nm_range i) as Rnm. pose proof (rso_rp_range i) as Rrp.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs1 (rso_extra regs))).
assert (E2 : bv_unsigned (ew E 2) = sp0 - 96) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl); exact Hsp).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (ES : forall j r, nth_error rso_saved j = Some r -> ew E (33 + j) = getr regs (Z_to_bv 5 r)).
{ intros j r Hj. subst E. assert (Hj11 : (j < 11)%nat) by (apply (proj1 (nth_error_Some rso_saved j)); rewrite Hj; discriminate).
rewrite Eimg_low by (unfold A_TEXT; lia). replace (33 + j)%nat with (32 + S j)%nat by lia. rewrite ew_Ereg_extra.
do 11 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; reflexivity|]). lia. }
assert (E41 : ew E (A_OBJ 41) = Z_to_bv 64 0xa5ec0) by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V41; reflexivity).
assert (E43 : ew E (A_OBJ 43) = Z_to_bv 64 0xa5ec8) by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V43; reflexivity).
assert (B41 : base_val E (Some (A_OBJ 41)) = 0xa5ec0) by (cbn [base_val]; rewrite E41; apply unsigned_lit_small; lia).
split.
- unfold ss_rso, rso_regions. apply pa_entry_st_ok_full.
  + exact HREG.
  + exact Hwf.
  + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok.
    * unfold rso_frame_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      lazymatch goal with |- Forall ?P ?l => let l2 := eval vm_compute in l in change (Forall P l2) end.
      repeat apply Forall_cons; try apply Forall_nil;
      lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
      let j := eval compute in (n - 33)%nat in let r := eval compute in (nth j rso_saved 0) in
      apply (chunk_ok_val SEGS E _ (sp0 - 96) off 8 (SOff n 0) (bv_unsigned (ew E n)));
      [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | let HR := fresh in pose proof (bv_unsigned_in_range 64 (ew E n)) as HR; clear - HR; change (bv_modulus 64) with (2 ^ 64) in HR; exact HR
      | cbn; lia
      | replace (sp0 - 96 + off) with (sp0 - 8 - 8 * Z.of_nat j) by (cbn; lia);
        let Ej := fresh "Ej" in pose proof (ES j r eq_refl) as Ej; change (33 + j)%nat with n in Ej;
        rewrite Ej; exact (HFR j r eq_refl) ] end.
    * unfold rso_row_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite B41. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ 0xa5ec0 (16 * i) 8 (SLit (rso_nm i)) (rso_nm i)); [reflexivity | zside | zside |].
         exact (val_mem_of_rdword SEGS (w_H W1) mem1 _ _ Hnm).
      -- apply (chunk_ok_val SEGS E _ 0xa5ec0 (16 * i + 8) 8 (SLit (rso_rp i)) (rso_rp i)); [reflexivity | zside | zside |].
         replace (0xa5ec0 + (16 * i + 8)) with (0xa5ec8 + 16 * i) by lia.
         exact (val_mem_of_rdword SEGS (w_H W1) mem1 _ _ Hrp).
  + apply pairwise_disjoint_of_extents. unfold rso_frame_region, rso_row_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B41. cbn [base_val]. rewrite E2.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; [exact I|]].
    * cbn [rso_facts rso_atom_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E2, E32, E41, E43, !unsigned_lit_small by (unfold SB; lia).
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold SB. repeat split; try lia.
    * cbn [rso_facts f_alias alias_ok]. split; [|exact I].
      apply U_inj. rewrite (U_rso_key E i E32 E43 Hi). rewrite (U_rshx E (A_OBJ 43) (16 * i) 0xa5ec8 E32 E43) by lia. reflexivity.
- unfold sh_ok, rso_SH. constructor; [|constructor; [|constructor]].
  + split.
    * unfold rd_of. change (fun a => option_map (fun b : byte => bv_unsigned b) (mbyte SEGS (mrestrict (w_H W1) mem1) a)) with (rdW W1 mem1).
      replace (U E RBx) with SHADOW_OFF by (unfold RBx; rewrite (U_atom E 32 SB E32) by (unfold SB; lia); reflexivity).
      cbn [she_m she_lo she_hi]. rewrite (U_atom E (A_OBJ 41) 0xa5ec0 E41) by lia. exact HZ.
    * intros a Ha. cbn [she_m she_lo she_hi Z.min Z.max] in Ha. rewrite (U_atom E (A_OBJ 41) 0xa5ec0 E41) in Ha by lia.
      unfold RBx. rewrite (U_atom E 32 SB E32) by (unfold SB; lia). unfold SB. lia.
  + split.
    * unfold rd_of. change (fun a => option_map (fun b : byte => bv_unsigned b) (mbyte SEGS (mrestrict (w_H W1) mem1) a)) with (rdW W1 mem1).
      replace (U E RBx) with SHADOW_OFF by (unfold RBx; rewrite (U_atom E 32 SB E32) by (unfold SB; lia); reflexivity).
      cbn [she_m she_lo she_hi]. rewrite (U_atom E (A_OBJ 43) 0xa5ec8 E43) by lia.
      apply (range_addressable_sub _ _ _ _ _ _ HZ); lia.
    * intros a Ha. cbn [she_m she_lo she_hi Z.min Z.max] in Ha. rewrite (U_atom E (A_OBJ 43) 0xa5ec8 E43) in Ha by lia.
      unfold RBx. rewrite (U_atom E 32 SB E32) by (unfold SB; lia). unfold SB. lia.
Qed.
(* two memories that agree below alloc_ceiling (the image, its shadow, the heap): every fact the walk keeps about
   the image's literals, g_shapes and their shadow carries over *)
Definition rso_low (W : world SEGS) (m m' : word -> option byte) : Prop :=
forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Lemma rso_low_refl : forall W m, rso_low W m m.
Proof. intros W m a _. reflexivity. Qed.
Lemma rso_low_trans : forall W m1 m2 m3, rso_low W m1 m2 -> rso_low W m2 m3 -> rso_low W m1 m3.
Proof. intros W m1 m2 m3 H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.
Lemma rso_low_of_kept : forall W m m' lo hi, alloc_ceiling <= lo ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) -> rso_low W m m'.
Proof. intros W m m' lo hi Hlo H a Ha. pose proof asan_consts as (C1 & _). apply H; lia. Qed.
Lemma low_rdword : forall W m m' a v, rso_low W m m' -> 0 <= a -> a + 8 <= alloc_ceiling ->
rdword (rdW W m) a = Some v -> rdword (rdW W m') a = Some v.
Proof. intros W m m' a v HL H0 H1 Hv. rewrite (YCbq.rdword_ext (rdW W m) (rdW W m') a); [exact Hv|]. intros k Hk. apply HL. lia. Qed.
Lemma low_abytes : forall W m m' a l, rso_low W m m' -> 0 <= a -> a + Z.of_nat (length l) <= alloc_ceiling ->
abytes_atR (rdW W m) a l -> abytes_atR (rdW W m') a l.
Proof. intros W m m' a l HL H0 H1 Hb k Hk. rewrite HL by lia. exact (Hb k Hk). Qed.
Lemma low_astr : forall W m m' a s, rso_low W m m' -> 0 <= a -> a + Z.of_nat (length s) + 1 <= alloc_ceiling ->
astr_atR (rdW W m) a s -> astr_atR (rdW W m') a s.
Proof.
intros W m m' a s HL H0 H1 [Hb Hn]. split; [|exact Hn]. apply (low_abytes W m m' a _ HL H0); [|exact Hb].
rewrite length_app. cbn [length]. lia.
Qed.
Lemma low_range_addr : forall W m m' a n, rso_low W m m' -> 0 <= a -> a + n <= 2 ^ 40 ->
range_addressable (rdW W m) SHADOW_OFF a n -> range_addressable (rdW W m') SHADOW_OFF a n.
Proof.
intros W m m' a n HL H0 H1 HR. pose proof asan_consts as (C1 & _).
apply (range_addressable_agree (rdW W m) (rdW W m') SHADOW_OFF a n); [|exact HR].
intros x Hx. apply HL. unfold shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound x 8 (2 ^ 37) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma low_hull : forall W m m' a n, rso_low W m m' -> 0 <= a -> a + n <= 2 ^ 40 ->
shadow_hull_vis (rdW W m) a n -> shadow_hull_vis (rdW W m') a n.
Proof.
intros W m m' a n HL H0 H1 HH s Hs. pose proof asan_consts as (C1 & _).
rewrite HL; [exact (HH s Hs)|]. unfold shadow_addr, SHADOW_OFF in Hs.
pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)).
assert (Hq : (a + n - 1) / 8 <= 2 ^ 37) by (apply Z.div_le_upper_bound; lia).
assert (Hr : forall u, 0 <= u -> u / 8 * 8 <= u) by (intros u Hu; pose proof (Z.mul_div_le u 8 ltac:(lia)); lia).
pose proof (Hr (2147450880 + a / 8) ltac:(lia)). pose proof (Hr (2147450880 + (a + n - 1) / 8) ltac:(lia)).
lia.
Qed.
Lemma low_tail : forall W m m' e, rso_low W m m' -> 0 <= e -> e + 8 <= alloc_ceiling ->
atail_vis SEGS W m e -> atail_vis SEGS W m' e.
Proof.
intros W m m' e HL H0 H1 HT a Ha. pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
rewrite HL by lia. exact (HT a Ha).
Qed.
Lemma in_rom_low : forall a, in_rom SEGS a -> 0 <= a < alloc_ceiling.
Proof.
intros a (sg & Hin & _ & Ha). pose proof (pa_img_range a (ex_intro _ sg (conj Hin Ha))).
pose proof alloc_ceiling_value as [[HC _] _]. lia.
Qed.
Lemma low_rt_rom : forall {B} W m m', rso_low W m m' -> rt_rom_view SEGS B W m -> rt_rom_view SEGS B W m'.
Proof.
intros B W m m' HL HV a Hr Ho He. rewrite (HL a (in_rom_low a Hr)). exact (HV a Hr Ho He).
Qed.
Section g.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
(* the strlen wrapper's call through the journal, in the form of aj_bcmp_at (lib/Reusable/YCbq.v:2169), for
   astrlen_realizes (lib/A/Rt/RtString.v:74) *)
Lemma aj_strlen_at : forall pc, astrlen_realizes SEGS B pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x s (o : Z) raw,
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> 0 < x ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
astr_at SEGS W memT x s -> aread_ok SEGS ESTACK W regsT memT x (astr_len s + 1) ->
atail_vis SEGS W memT (x + astr_len s) -> rt_rom_view SEGS B W memT ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (astr_len s) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a)).
Proof.
intros pc AS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x s o raw
HJ Ha0 Hx Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw HSTR HRD HTV HRV.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity.
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply ecall_pre_at; [exact HJ | exact Hsp' | exact Hal | exact Hneg | exact Hbud | rewrite Hra; exact Hraw | exact Hgp | exact Htp]. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HPS : ecall_pre_stk SEGS B ESTACK lyc Sc W regsT memT mdc).
{ split; [exact HPRE|]. split; [rewrite Eslo, Hsp'; zlia|]. intros a Ha. apply Hpres. unfold ascratch_stk in Ha. rewrite Hsp' in Ha. zlia. }
eapply SRr_mono.
{ exact (AS lyc Sc W regsT memT mdc x s HPS Ha0 Hx HSTR HRD HTV HRV). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & HQ & Hfr & Hpres2 & Hscr).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
(fun a => sp0 + o - ESTACK <= a < sp0 + o) Sc own HJ).
- intros a Ha Hna. apply (Hfr a Ha); [unfold ascratch_stk; rewrite Hsp'; exact Hna | intros []].
- exact Hpres2.
- exact Hsame.
- intros a Ha; left; left; zlia.
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact HQ|].
intros a Ha Hna. apply (Hfr a Ha); [unfold ascratch_stk; rewrite Hsp'; exact Hna | intros []].
Qed.
End g.
Lemma pres_reg : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). exact (HP _ Hr). Qed.
Lemma abytes_some : forall rd a l b, abytes_atR rd a l -> a <= b < a + Z.of_nat (length l) -> rd b <> None.
Proof.
intros rd a l b H Hb. replace b with (a + Z.of_nat (Z.to_nat (b - a))) by lia.
rewrite (H (Z.to_nat (b - a)) ltac:(lia)). discriminate.
Qed.
(* RtDefs.v's aread_ok for an image literal below the stack *)
Lemma aread_ok_lit : forall stk (W : world SEGS) regsT m x s,
astr_atR (rdW W m) x s -> range_addressable (rdW W m) SHADOW_OFF x (astr_len s + 1) ->
shadow_hull_vis (rdW W m) x (astr_len s + 1) ->
0 <= x -> x + astr_len s + 1 <= kLowMemEnd - 1 -> kLowMemEnd <= spZ regsT - stk ->
aread_ok SEGS stk W regsT m x (astr_len s + 1).
Proof.
intros stk W regsT m x s [Hb _] HR HH H0 H1 H2. unfold astr_len in *.
split; [lia|]. split; [unfold kLowMemEnd in H1; lia|]. split; [unfold kLowMemEnd in H1; lia|].
split; [|split; [unfold amem_range; left; lia | split; [exact HR | intros _; exact HH]]].
intros a Ha. split.
- apply (abytes_some _ x (s ++ [Z_to_bv 8 0])); [exact Hb|]. rewrite length_app. cbn [length]. lia.
- unfold ascratch_stk. lia.
Qed.
(* the eleven saved words lie in [sp0 - 88, sp0) *)
Lemma rso_frame_kept : forall H H' m m' sp0 regs,
rso_frame (mrestrict H m) sp0 regs -> (forall a, sp0 - 88 <= a < sp0 -> aview SEGS H' m' a = aview SEGS H m a) ->
rso_frame (mrestrict H' m') sp0 regs.
Proof.
intros H H' m m' sp0 regs HF Hk j r Hj. pose proof (HF j r Hj) as V.
assert (Hj11 : (j < 11)%nat) by (apply (proj1 (nth_error_Some rso_saved j)); rewrite Hj; discriminate).
intros kk Hkk. rewrite <- (V kk Hkk). apply (mbyte_of_aview SEGS). apply Hk. lia.
Qed.
(* a source range of a runtime entry below its stack window *)
Lemma src_ok_low : forall (W : world SEGS) regsT m x l,
abytes_atR (rdW W m) x l -> 0 <= x -> x + Z.of_nat (length l) <= spZ regsT - ESTACK ->
src_ok SEGS W regsT m x (Z.of_nat (length l)).
Proof. intros W regsT m x l Hb H0 H1 a Ha. split; [exact (abytes_some _ x l a Hb Ha) | lia]. Qed.
Lemma rso_E_saved : forall (regs regs1 : bvmap 5 word) j r, nth_error rso_saved j = Some r ->
ew (Eimg (Ereg regs1 (rso_extra regs))) (33 + j) = getr regs (Z_to_bv 5 r).
Proof.
intros regs regs1 j r Hj. assert (Hj11 : (j < 11)%nat) by (apply (proj1 (nth_error_Some rso_saved j)); rewrite Hj; discriminate).
rewrite Eimg_low by (unfold A_TEXT; lia). replace (33 + j)%nat with (32 + S j)%nat by lia. rewrite ew_Ereg_extra.
do 11 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; reflexivity|]). lia.
Qed.
Lemma hull_sub : forall (rd : reader) x n m, 0 < n -> n <= m -> 0 <= x ->
shadow_hull_vis rd x m -> shadow_hull_vis rd x n.
Proof.
intros rd x n m Hn Hm Hx HH s Hs. apply HH. split; [lia|].
assert (shadow_addr (x + n - 1) <= shadow_addr (x + m - 1)) by (unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
assert (shadow_addr (x + n - 1) / 8 * 8 <= shadow_addr (x + m - 1) / 8 * 8) by (apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
lia.
Qed.
Lemma abytes_prefix : forall rd a l1 l2, abytes_atR rd a (l1 ++ l2) -> abytes_atR rd a l1.
Proof. intros rd a l1 l2 H k Hk. rewrite (H k ltac:(rewrite length_app; lia)). rewrite app_nth1 by lia. reflexivity. Qed.
Lemma bytes_eq_iff : forall (rd : reader) x y (l1 l2 : list byte), length l1 = length l2 ->
abytes_atR rd x l1 -> abytes_atR rd y l2 ->
((forall k, 0 <= k < Z.of_nat (length l1) -> rd (x + k) = rd (y + k)) <-> map bv_unsigned l1 = map bv_unsigned l2).
Proof.
intros rd x y l1 l2 HL H1 H2. split.
- intros H. apply nth_ext with (d := 0) (d' := 0); [rewrite !length_map; exact HL|].
  intros k Hk. rewrite length_map in Hk.
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
  rewrite (nth_indep (map bv_unsigned l2) 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
  rewrite !map_nth. pose proof (H (Z.of_nat k) ltac:(lia)) as E.
  rewrite (H1 k Hk), (H2 k ltac:(lia)) in E. injection E as E. exact E.
- intros H k Hk. replace k with (Z.of_nat (Z.to_nat k)) by lia.
  rewrite (H1 (Z.to_nat k) ltac:(lia)), (H2 (Z.to_nat k) ltac:(lia)). f_equal.
  rewrite <- !(map_nth bv_unsigned). rewrite H. reflexivity.
Qed.
(* the shadow facts of the image ranges the walk reads (g_shapes, the 28 names): what CmdRecBase.v's
   cmd_aread_ok_chk gives for these concrete ranges (addressable, and aread_ok's shadow hull) *)
Definition rso_zsh (rd : reader) : Prop :=
range_addressable rd SHADOW_OFF 0xa5ec0 448 /\
(forall i, 0 <= i < 28 ->
 range_addressable rd SHADOW_OFF (rso_nm i) (astr_len (rso_name i) + 1) /\
 shadow_hull_vis rd (rso_nm i) (astr_len (rso_name i) + 1)).
Section e.
Variable B : asyms.
Variables RLO RHI : Z.
(* the image's read-only bytes the walk reads at the entry state: g_shapes' rows, the 28 names and the replies
   (cmd_ro_ok's RO_g_shapes and RO_lit_* conjuncts, lib/A/Prog/CmdRo.v) and the word tail after each name *)
Definition rso_ro (rd : reader) : Prop :=
(forall i, 0 <= i < 28 ->
 rdword rd (0xa5ec0 + 16 * i) = Some (rso_nm i) /\ rdword rd (0xa5ec8 + 16 * i) = Some (rso_rp i) /\
 astr_atR rd (rso_nm i) (rso_name i) /\ astr_atR rd (rso_rp i) (rso_reply i)) /\
astr_atR rd 0x21ce0 REC_MOD_HOST_SHAPE.
(* a byte of astr_argA's read-only arm: read-only, owned by no runtime entry, not the errno cell *)
Definition rso_rob (a : Z) : Prop :=
in_roP SEGS RLO RHI a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Definition rso_ro_in : Prop :=
(forall i k, 0 <= i < 28 -> 0 <= k < astr_len (rso_reply i) + 1 -> rso_rob (rso_rp i + k)) /\
(forall k, 0 <= k < 7 -> rso_rob (0x21ce0 + k)).
Definition rso_tails (W : world SEGS) mem : Prop :=
forall i, 0 <= i < 28 -> atail_vis SEGS W mem (rso_nm i + astr_len (rso_name i)).
(* the verb, as rec_shape_of_c.v:86-89 states it *)
Definition rso_verb ly S (W : world SEGS) mem (p : Z) (v : list byte) : Prop :=
Z.of_nat (length v) <= 16 ->
abytes_atR (rdW W mem) p v /\
(in_blockA (ablocks B ly S) p (Z.of_nat (length v)) \/
 astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) [] p (Some v)).
(* the relro range [RLO, RHI) in the image (cmd_img_facts' field cif_relro_img, the walk hypothesis RRO),
   and the statement's bound on len (rec_shape_of_c.v:75), which the bcmp call's length needs *)
Definition rso_gaps (v : list byte) : Prop :=
(forall a, RLO <= a < RHI -> in_img SEGS a) /\ Z.of_nat (length v) < 2 ^ 64.
Definition rso_cx ly S (W : world SEGS) (regs : bvmap 5 word) mem md (p : Z) (v : list byte) : Prop :=
afn_pre_na SEGS B REC_SHAPE_OF_STK ly S W regs mem md /\
getr regs 10 = w64 p /\ getr regs 11 = w64 (Z.of_nat (length v)) /\
cmd_val_objs /\ rso_ro (rdW W mem) /\ rso_ro_in /\ rso_tails W mem /\ rso_verb ly S W mem p v /\ rso_gaps v.
(* the post of rec_shape_of_c.v:93-105, word for word *)
Definition rso_Q ly S (v : list byte) : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' =>
(exists q, getr regs' 10 = w64 q /\ 0 <= q < 2 ^ 64 /\
 forall O, astr_argA B ly' S' (rdW W' mem') (in_roP SEGS RLO RHI) O q (Some (shape_of v))) /\
Permutation (ablocks B ly' S') (ablocks B ly S) /\
ly' = ly /\ S' = S.
Definition rso_post ly S (W : world SEGS) (regs : bvmap 5 word) mem md (v : list byte) : world SEGS -> config -> Prop :=
apost_base SEGS B REC_SHAPE_OF_STK [] regs ly S W mem md EV_REC_SHAPE_OF (rso_Q ly S v).
(* the state between the entry and the current pc: the journal (no event, no block, footprint empty), every byte
   outside this call's stack window unchanged, and the eleven saved registers in the frame *)
Definition rso_mid ly S (W : world SEGS) (regs : bvmap 5 word) mem md memc mdc : Prop :=
ajournal SEGS B REC_SHAPE_OF_STK (spZ regs) [] ly S W mem md [] ly S W memc mdc 0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REC_SHAPE_OF_STK <= a < spZ regs) ->
 aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) /\
rso_frame (mrestrict (w_H W) memc) (spZ regs) regs.
(* the registers at the loop head of iteration i, and at the two return sites of that iteration *)
Definition rso_regs_at (regs regs1 : bvmap 5 word) (i : Z) : Prop :=
getr regs1 2 = w64 (spZ regs - 96) /\ getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4 /\
getr regs1 8 = getr regs 11 /\ getr regs1 9 = getr regs 10 /\
getr regs1 18 = w64 (0xa5ec0 + 16 * i) /\ getr regs1 19 = w64 0x21ce0 /\ getr regs1 21 = w64 (- (2 * i)) /\
getr regs1 22 = w64 (0xa5ec8 + 16 * i) /\ getr regs1 23 = w64 SB /\ getr regs1 24 = w64 (SB + (0xa5ec0 + 16 * i) / 8) /\
getr regs1 25 = w64 (-56) /\ getr regs1 26 = getr regs 26 /\ getr regs1 27 = getr regs 27.
Definition rso_unseen (i : Z) (v : list byte) : Prop :=
forall j, 0 <= j < i -> map bv_unsigned (rso_name j) <> map bv_unsigned v.
(* the model's lookup past rows that do not match, at the row that does, and past all 28 (RecFacts.v:313-319) *)
Lemma lookup_unseen : forall rows v n, (n <= length rows)%nat ->
(forall j, (j < n)%nat -> map bv_unsigned (fst (nth j rows ([], []))) <> map bv_unsigned v) ->
shape_lookup rows v = shape_lookup (skipn n rows) v.
Proof.
induction rows as [|[nm rp] rows IH]; intros v n Hn H; [destruct n; reflexivity|].
destruct n as [|n]; [reflexivity|]. cbn [shape_lookup skipn].
assert (Hb : bl_eqb nm v = false).
{ unfold bl_eqb. destruct (list_eq_dec Z.eq_dec (map bv_unsigned nm) (map bv_unsigned v)) as [e|]; [|reflexivity].
  exfalso. exact (H 0%nat ltac:(lia) e). }
rewrite Hb. apply IH; [cbn in Hn; lia|]. intros j Hj. exact (H (S j) ltac:(lia)).
Qed.
Lemma skipn_cons_nth : forall {A} (l : list A) n d, (n < length l)%nat -> skipn n l = nth n l d :: skipn (S n) l.
Proof. intros A l. induction l as [|a l IH]; intros n d Hn; cbn in Hn; [lia|]. destruct n; [reflexivity|]. cbn [skipn nth]. apply IH. lia. Qed.
Lemma rso_lookup_skip : forall i v, 0 <= i <= 28 -> rso_unseen i v ->
shape_of v = shape_lookup (skipn (Z.to_nat i) shape_table) v.
Proof.
intros i v Hi HU. unfold shape_of. apply lookup_unseen; [rewrite shape_table_length; lia|].
intros j Hj. pose proof (HU (Z.of_nat j) ltac:(lia)) as H. unfold rso_name in H. rewrite Nat2Z.id in H. exact H.
Qed.
Lemma rso_shape_found : forall i v, 0 <= i < 28 -> rso_unseen i v ->
map bv_unsigned (rso_name i) = map bv_unsigned v -> shape_of v = rso_reply i.
Proof.
intros i v Hi HU HE. rewrite (rso_lookup_skip i v ltac:(lia) HU).
rewrite (skipn_cons_nth shape_table (Z.to_nat i) ([], [])) by (rewrite shape_table_length; lia).
unfold rso_name, rso_reply in *. destruct (nth (Z.to_nat i) shape_table ([], [])) as [nm rp]. cbn [fst snd shape_lookup] in *.
unfold bl_eqb. destruct (list_eq_dec Z.eq_dec (map bv_unsigned nm) (map bv_unsigned v)) as [e|n]; [reflexivity | contradiction].
Qed.
Lemma rso_shape_default : forall v, rso_unseen 28 v -> shape_of v = REC_MOD_HOST_SHAPE.
Proof.
intros v HU. rewrite (rso_lookup_skip 28 v ltac:(lia) HU). rewrite skipn_all2 by (rewrite shape_table_length; lia). reflexivity.
Qed.
Lemma rso_unseen_next : forall i v, 0 <= i -> rso_unseen i v -> map bv_unsigned (rso_name i) <> map bv_unsigned v ->
rso_unseen (i + 1) v.
Proof.
intros i v Hi HU Hn j Hj. destruct (Z.eq_dec j i) as [->|Hne]; [exact Hn|]. apply HU. lia.
Qed.
Definition HEAD_stmt (i : Z) : Prop :=
forall ly S W regs mem md p v regs1 memc mdc,
rso_cx ly S W regs mem md p v -> rso_mid ly S W regs mem md memc mdc -> rso_regs_at regs regs1 i ->
rso_unseen i v -> rt_rom_view SEGS B W memc ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + RS_HEAD)) memc (seg_rom SEGS)) mdc) (rso_post ly S W regs mem md v).
Definition R1_stmt (i : Z) : Prop :=
forall ly S W regs mem md p v regs1 memc mdc,
rso_cx ly S W regs mem md p v -> rso_mid ly S W regs mem md memc mdc -> rso_regs_at regs regs1 i ->
getr regs1 10 = w64 (astr_len (rso_name i)) -> getr regs1 20 = w64 (rso_nm i) ->
rso_unseen i v -> rt_rom_view SEGS B W memc ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + RS_R1)) memc (seg_rom SEGS)) mdc) (rso_post ly S W regs mem md v).
Definition R2_stmt (i : Z) : Prop :=
forall ly S W regs mem md p v regs1 memc mdc,
rso_cx ly S W regs mem md p v -> rso_mid ly S W regs mem md memc mdc -> rso_regs_at regs regs1 i ->
getr regs1 20 = w64 (rso_nm i) -> Z.of_nat (length v) = astr_len (rso_name i) ->
(getr regs1 10 = w64 0 <-> map bv_unsigned (rso_name i) = map bv_unsigned v) ->
rso_unseen i v -> rt_rom_view SEGS B W memc ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + RS_R2)) memc (seg_rom SEGS)) mdc) (rso_post ly S W regs mem md v).
(* the latch (0x89280), reached from the length compare and from the bcmp result's test when row i does not match *)
Definition LATCH_stmt (i : Z) : Prop :=
forall ly S W regs mem md p v regs1 memc mdc,
rso_cx ly S W regs mem md p v -> rso_mid ly S W regs mem md memc mdc -> rso_regs_at regs regs1 i ->
rso_unseen (i + 1) v -> rt_rom_view SEGS B W memc ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + RS_LATCH)) memc (seg_rom SEGS)) mdc) (rso_post ly S W regs mem md v).
(* the callee-saved registers at the return, one equation each *)
Lemma rso_pres_ret : forall (regs r' : bvmap 5 word),
getr r' 2 = getr regs 2 -> getr r' 3 = getr regs 3 -> getr r' 4 = getr regs 4 -> getr r' 8 = getr regs 8 ->
getr r' 9 = getr regs 9 -> getr r' 18 = getr regs 18 -> getr r' 19 = getr regs 19 -> getr r' 20 = getr regs 20 ->
getr r' 21 = getr regs 21 -> getr r' 22 = getr regs 22 -> getr r' 23 = getr regs 23 -> getr r' 24 = getr regs 24 ->
getr r' 25 = getr regs 25 -> getr r' 26 = getr regs 26 -> getr r' 27 = getr regs 27 ->
aregs_preserved regs r'.
Proof.
intros regs r' H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 r Hr.
assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
  r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia).
repeat (destruct Hc as [-> | Hc]); try subst r;
match goal with H : getr r' ?k = getr regs ?k |- getr r' (Z_to_bv 5 ?n) = _ =>
  replace (Z_to_bv 5 n) with k by (apply bv_eq; reflexivity); exact H end.
Qed.
Lemma rso_regs_ok : forall i (regs regs1 : bvmap 5 word), cmd_val_objs -> 0 <= i < 28 -> rso_regs_at regs regs1 i ->
regs_ok (Eimg (Ereg regs1 (rso_extra regs))) (rso_regs_head i) regs1.
Proof.
intros i regs regs1 HVO Hi (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
destruct (rso_val_objs HVO) as (V41 & V42 & V43).
set (E := Eimg (Ereg regs1 (rso_extra regs))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E41 : ew E (A_OBJ 41) = Z_to_bv 64 0xa5ec0) by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V41; reflexivity).
assert (E42 : ew E (A_OBJ 42) = Z_to_bv 64 0x21ce0) by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V42; reflexivity).
change (A_OBJ 41) with 282%nat in E41. change (A_OBJ 42) with 283%nat in E42.
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr];
[ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) => let w := eval cbv -[Z.mul Z.add Z.sub Z.opp zcanon] in (sr_get a rr2) in change (sr_get a rr2) with w end;
  first
  [ cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; symmetry; apply EE; reflexivity
  | rewrite getr_zero; reflexivity
  | cbn [sv_denot]; rewrite E41, unsigned_lit_small by lia; first [exact R18 | exact R22]
  | cbn [sv_denot]; rewrite E42, unsigned_lit_small by lia; rewrite Z.add_0_r; exact R19
  | cbn [sv_denot]; rewrite Z.add_0_r, E32; exact R23
  | cbn [sv_denot]; rewrite Z_to_bv64_canon; first [exact R21 | exact R25]
  | cbn [sv_denot]; rewrite E41, unsigned_lit_small by lia; rewrite R22; unfold w64; f_equal; lia
  | change (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 282 (16 * i)) (SLit 3))) with (rshx 282 (16 * i));
    rewrite denot_lit_U, (U_rshx E 282%nat (16 * i) 0xa5ec0 E32 E41) by lia; exact R24 ]
| ]); try (destruct Hr; fail).
Qed.
(* the head registers after a wrapper call that preserves the callee-saved registers of a state whose callee-saved
   registers are those of regs1 *)
Lemma rso_regs_at_pres : forall regs regs1 rgT regs2 i,
rso_regs_at regs regs1 i -> aregs_preserved rgT regs2 ->
getr rgT 2 = getr regs1 2 -> getr rgT 3 = getr regs1 3 -> getr rgT 4 = getr regs1 4 ->
getr rgT 8 = getr regs1 8 -> getr rgT 9 = getr regs1 9 -> getr rgT 18 = getr regs1 18 ->
getr rgT 19 = getr regs1 19 -> getr rgT 21 = getr regs1 21 -> getr rgT 22 = getr regs1 22 ->
getr rgT 23 = getr regs1 23 -> getr rgT 24 = getr regs1 24 -> getr rgT 25 = getr regs1 25 ->
getr rgT 26 = getr regs1 26 -> getr rgT 27 = getr regs1 27 ->
rso_regs_at regs regs2 i.
Proof.
intros regs regs1 rgT regs2 i (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R21 & R22 & R23 & R24 & R25 & R26 & R27) HP
S2 S3 S4 S8 S9 S18 S19 S21 S22 S23 S24 S25 S26 S27.
assert (P : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr rgT r) by (intros r Hr; exact (pres_reg _ _ r HP Hr)).
repeat split; (rewrite P;
  [ first [ rewrite S2; exact R2 | rewrite S3; exact R3 | rewrite S4; exact R4 | rewrite S8; exact R8 | rewrite S9; exact R9
          | rewrite S18; exact R18 | rewrite S19; exact R19 | rewrite S21; exact R21 | rewrite S22; exact R22
          | rewrite S23; exact R23 | rewrite S24; exact R24 | rewrite S25; exact R25 | rewrite S26; exact R26
          | rewrite S27; exact R27 ]
  | unfold acallee_saved;
    lazymatch goal with |- context [bv_unsigned ?x] => let z := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with z end;
    lia ]).
Qed.
(* the state facts after a run that wrote nothing and a wrapper call that wrote only below this frame *)
Lemma rso_mid_call : forall ly S (W : world SEGS) regs mem md memc mdc mm mem2 md2 lo,
rso_mid ly S W regs mem md memc mdc ->
(forall a, 0 <= a < 2 ^ 64 -> rdW W mm a = rdW W memc a) ->
ajournal SEGS B REC_SHAPE_OF_STK (spZ regs) [] ly S W mem md [] ly S W mem2 md2 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < spZ regs - 96) -> rdW W mem2 a = rdW W mm a) ->
spZ regs - REC_SHAPE_OF_STK <= lo ->
rso_mid ly S W regs mem md mem2 md2.
Proof.
intros ly S W regs mem md memc mdc mm mem2 md2 lo (HJ & HK & HFR) U1 HJ2 HK2 Hlo.
split; [exact HJ2|]. split.
- intros a Ha Hna. rewrite (HK2 a Ha) by lia. rewrite (U1 a Ha). exact (HK a Ha Hna).
- apply (rso_frame_kept (w_H W) (w_H W) memc mem2 (spZ regs) regs HFR). intros a Ha.
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as R. unfold spZ in *. change (bv_modulus 64) with (2 ^ 64) in R.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & _) & _).
  pose proof asan_consts as (C1 & _). unfold REC_SHAPE_OF_STK, ESTACK in *.
  rewrite (HK2 a) by lia. apply U1. lia.
Qed.
Section h.
Hypothesis LAWS : AR_laws SEGS B.
(* the per-binary record, for CmdRecBase.v's cmd_aread_ok_chk *)
Hypothesis HB : CmdBSyms B.
(* the verb at a call of the bcmp wrapper: its bytes, its range and its shadow at the call's memory *)
Lemma rso_verb_call : forall ly S (W : world SEGS) mem memT mdT p v,
AR SEGS B ly S W memT mdT -> rso_low W mem memT -> rso_verb ly S W mem p v -> rso_gaps v ->
Z.of_nat (length v) <= 16 -> 0 < Z.of_nat (length v) ->
abytes_atR (rdW W memT) p v /\ 0 <= p /\ p + Z.of_nat (length v) <= alloc_ceiling /\ amem_range p (Z.of_nat (length v)) /\
range_addressable (rdW W memT) SHADOW_OFF p (Z.of_nat (length v)) /\ shadow_hull_vis (rdW W memT) p (Z.of_nat (length v)).
Proof.
intros ly S W mem memT mdT p v HAR HL HV (HRI & _) H16 H0. pose proof asan_consts as (C1 & _).
(* a live block holding the verb's bytes (and maybe more) *)
assert (BLK : forall n, Z.of_nat (length v) <= n -> in_blockA (ablocks B ly S) p n -> abytes_atR (rdW W mem) p v ->
  abytes_atR (rdW W memT) p v /\ 0 <= p /\ p + Z.of_nat (length v) <= alloc_ceiling /\ amem_range p (Z.of_nat (length v)) /\
  range_addressable (rdW W memT) SHADOW_OFF p (Z.of_nat (length v)) /\ shadow_hull_vis (rdW W memT) p (Z.of_nat (length v))).
{ intros n Hn (p0 & k & Hin & Hp0 & Hpk) Hb.
  destruct (al_blocks _ _ LAWS ly S W memT mdT p0 k HAR Hin) as (Hal & H4096 & Hceil & _ & _ & _ & Hk).
  pose proof (req_size_pos0 k ltac:(lia)) as [_ Hrk].
  assert (Hp : 0 <= p) by lia. assert (Hpc : p + Z.of_nat (length v) <= alloc_ceiling) by lia.
  split; [exact (low_abytes W mem memT p v HL Hp Hpc Hb)|]. split; [exact Hp|]. split; [exact Hpc|].
  split; [apply (amem_range_of_block SEGS B LAWS ly S W memT mdT p0 k p (Z.of_nat (length v)) HAR Hin); lia|].
  split; [apply (range_addressable_of_block SEGS B LAWS ly S W memT mdT p0 k p (Z.of_nat (length v)) HAR Hin); lia|].
  apply (shadow_hull_vis_of_block SEGS B LAWS ly S W memT mdT p0 k p (Z.of_nat (length v)) HAR Hin); lia. }
destruct (HV H16) as (Hb & [Hblk | Harg]); [exact (BLK _ (Z.le_refl _) Hblk Hb)|].
cbv beta iota zeta delta [astr_argA] in Harg.
destruct Harg as (_ & _ & _ & [(Hblk & _) | (Hro & Ha & Hh & _)]);
[exact (BLK (Z.of_nat (length v) + 1) ltac:(lia) Hblk Hb)|].
(* astr_argA's read-only arm: image bytes, whose shadow the record's checks give at the call's state *)
assert (HI : forall i, 0 <= i < Z.of_nat (length v) -> 0x10000 <= p + i < 0x606000).
{ intros i Hi. apply pa_img_range. destruct (proj1 (Hro i ltac:(lia))) as [(s & Hs & _ & Hr) | Hr].
  - exists s. split; [exact Hs | lia].
  - exact (HRI _ Hr). }
pose proof (HI 0 ltac:(lia)) as I0. pose proof (HI (Z.of_nat (length v) - 1) ltac:(lia)) as I1.
assert (Hp : 0 <= p) by lia. assert (Hpc : p + Z.of_nat (length v) <= alloc_ceiling) by lia.
destruct (cmd_aread_ok_chk SEGS B LAWS HB ly S W memT mdT p _ HAR Ha Hh) as [Hra Hhv].
split; [exact (low_abytes W mem memT p v HL Hp Hpc Hb)|]. split; [exact Hp|]. split; [exact Hpc|].
split; [unfold amem_range, kLowMemEnd; left; lia|].
split; [exact (range_addressable_sub _ _ p (Z.of_nat (length v) + 1) p (Z.of_nat (length v)) Hra ltac:(lia) ltac:(lia))|].
exact (hull_sub _ p (Z.of_nat (length v)) (Z.of_nat (length v) + 1) H0 ltac:(lia) Hp Hhv).
Qed.
End h.
End e.
End f.
End d.
