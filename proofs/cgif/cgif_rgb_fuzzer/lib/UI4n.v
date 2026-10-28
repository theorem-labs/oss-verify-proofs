(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p YK1j.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ0a YQ05 YQ0e YQ02 YQ00 YQ07 YQ08.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03 YI07
UI1e UI1i UI57 YI0x YP14 YI08 YI0c YI0g YI0f YI0d
UI3h UI4v UIZm UI4w.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YM06.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition PC_GP1 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0xfc8).
Definition PC_FR1 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0xfd0).
Definition PC_MA1 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0xfe8).
Definition PC_L4 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x101c).
Definition PC_L4X : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x1058).
Lemma U_mulw_shl : forall E na nb a b,
ew E na = Z_to_bv 64 a -> ew E nb = Z_to_bv 64 b -> 0 <= a < 2 ^ 16 -> 0 <= b < 2 ^ 15 ->
U E (SMdw M_MUL (SOff na 0) (SOff nb 0)) = a * b /\
U E (SAlu ALU_SRL (SAlu ALU_SLL (SMdw M_MUL (SOff na 0) (SOff nb 0)) (SLit 32)) (SLit 30)) = 4 * (a * b) /\
U E (SAlu ALU_SLL (SMdw M_MUL (SOff na 0) (SOff nb 0)) (SLit 32)) = a * b * 2 ^ 32.
Proof.
intros E na nb a b Ha Hb Ra Rb.
assert (HM : U E (SMdw M_MUL (SOff na 0) (SOff nb 0)) = a * b).
{ rewrite U_SMdw. cbn [zmd_raw]. rewrite (U_atom E na a Ha), (U_atom E nb b Hb) by lia.
rewrite (Z.mod_small a), (Z.mod_small b) by lia. rewrite swrap32_id by nia.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. nia. }
assert (HS : U E (SAlu ALU_SLL (SMdw M_MUL (SOff na 0) (SOff nb 0)) (SLit 32)) = a * b * 2 ^ 32).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite HM, U_SLit. change (Z.land (zcanon 32) 63) with 32.
rewrite Z.shiftl_mul_pow2 by lia. apply zcanon_id. unfold M64. nia. }
split; [exact HM|]. split; [|exact HS].
rewrite U_SAlu. cbn [zalu_raw]. rewrite HS, U_SLit. change (Z.land (zcanon 30) 63) with 30.
rewrite Z.shiftr_div_pow2 by lia. replace (a * b * 2 ^ 32) with (4 * (a * b) * 2 ^ 30) by lia.
rewrite Z.div_mul by lia. apply zcanon_id. unfold M64. nia.
Qed.
Lemma U_fill_len : forall E n9 M,
ew E n9 = Z_to_bv 64 (M * 2 ^ 32) -> 0 <= M < 2 ^ 20 ->
U E (SAlu ALU_SRL (SOff n9 0) (SLit 32)) = M /\
U E (SAlu ALU_SLL (SAlu ALU_SRL (SOff n9 0) (SLit 32)) (SLit 2)) = 4 * M.
Proof.
intros E n9 M H9 HM.
assert (HS : U E (SAlu ALU_SRL (SOff n9 0) (SLit 32)) = M).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n9 (M * 2 ^ 32) H9) by nia. rewrite U_SLit. change (Z.land (zcanon 32) 63) with 32.
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. apply zcanon_id. unfold M64. lia. }
split; [exact HS|].
rewrite U_SAlu. cbn [zalu_raw]. rewrite HS, U_SLit. change (Z.land (zcanon 2) 63) with 2.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma in_subq_qt : forall (l L : list reg), forallb (fun r => existsb (bv_eqb r) L) l = true -> forall r, In r l -> In r L.
Proof.
intros l L Hs r Hr. pose proof (proj1 (forallb_forall _ _) Hs r Hr) as Hx. cbn beta in Hx.
apply existsb_exists in Hx as (r' & Hin & Heq). apply bv_eqb_eq in Heq. subst r'. exact Hin.
Qed.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Hypothesis GETPAL : forall fx', getpal_spec (fx:=fx') API.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Local Notation BASEv := (BASE r g N img fmt rest s bef beffmt).
Local Notation FPv := (FPfoot r g bef beffmt s N).
Local Notation spv := (sp regs0).
Local Notation sp0v := (sp0 regs0).
Local Notation qfk := (qfacts_kept regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay rest).
Section e.
Context {fxi : YK11.FPState}.
Definition ss_L4x : sstate :=
mkSS PC_L4 (sr_set (sr_set sr_atoms 12%bv (SLit 0)) 14%bv (SLit 1))
[ YQ0b.mkRegion (Some 15%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 32 0))];
YQ0b.mkRegion (Some 33%nat) 0 4 0 4 [] ]
None
(mkFacts [ (15%nat, mkAF 4096 CEIL_MAX 0); (16%nat, mkAF 4096 CEIL_MAX 0); (5%nat, mkAF 4096 CEIL_MAX 0);
(11%nat, mkAF (2^63) (2^64-4097) 0); (10%nat, mkAF 0 CEIL_MAX 2); (33%nat, mkAF 4096 CEIL_MAX 2); (32%nat, mkAF 0 255 0) ]
[mkAC BC_GEU (SOff 16 0) (SOff 5 0)]
[(SAlu ALU_ADD (SOff 24 0) (SOff 10 0), SOff 33 0)]).
Definition ss_L4 : sstate := mkSST PC_L4 (ss_regs ss_L4x) (sfr_atoms 64) (ss_mem ss_L4x) None (ss_facts ss_L4x).
Definition L4_KEEP : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Section L4.
Variables (Lq : layout) (Aq : astate) (mdq : Model) (flt M : Z) (imgl : list Z).
Hypothesis HM : 0 < M.
Hypothesis Himgl : zlen imgl = M.
Hypothesis Himg0 : 4096 <= img. Hypothesis Himg1 : img + M <= alloc_ceiling.
Hypothesis Hflt0 : 4096 <= flt. Hypothesis Hflt1 : flt + 4 * M <= alloc_ceiling. Hypothesis Hflt4 : flt mod 4 = 0.
Hypothesis Hdisj : img + M <= flt \/ flt + 4 * M <= img.
Hypothesis Hfin : In (flt, 4 * M) (blocks Lq Aq).
Hypothesis Hwb : forall i, 0 <= i < 4 * M -> wr_byte RGBA_STK sp0v FPv (blocks L A) (blocks Lq Aq) (flt + i).
Definition L4_post (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (pc : Z) (j lo : Z) : config -> Prop :=
fun c' => exists (fy' : FPState) regs' mem',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 pc) mem' (seg_rom ubs2segs)) mdq /\
journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem' mdq /\ frm_zero (@fp_csr fy') /\
getr regs' 10 = Z_to_bv 64 (4 * j) /\ getr regs' 15 = Z_to_bv 64 (img + j) /\ getr regs' 16 = Z_to_bv 64 (img + j) /\
getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 14 = Z_to_bv 64 1 /\
(forall rr : reg, In rr L4_KEEP -> getr regs' rr = getr regs rr) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (flt + 4 * lo <= a < flt + 4 * j) -> mbyte ubs2segs mem' a = mbyte ubs2segs mem a).
Lemma L4_step : forall (fy : FPState) (regs : bvmap 5 word) mem (j : Z),
0 <= j < M ->
journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq -> frm_zero (@fp_csr fy) ->
getr regs 13 = Z_to_bv 64 (4 * M) -> getr regs 10 = Z_to_bv 64 (4 * j) -> getr regs 15 = Z_to_bv 64 (img + j) ->
getr regs 16 = Z_to_bv 64 (img + j) -> getr regs 5 = Z_to_bv 64 img -> getr regs 24 = Z_to_bv 64 flt ->
getr regs 11 = Z_to_bv 64 (2 ^ 64 - 1 - flt) -> getr regs 12 = Z_to_bv 64 0 -> getr regs 14 = Z_to_bv 64 1 ->
arr8 ubs2segs mem img imgl ->
SR ubs2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_L4) mem (seg_rom ubs2segs)) mdq)
(L4_post fy regs mem (if j + 1 <? M then PC_L4 else PC_L4X) (j + 1) j).
Proof.
intros fy regs mem j Hj HJ Hfrm Hre Hrc Hri Hri6 Hr5 Hr24 Hr11 Hr12 Hr14 Himg.
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (arr8_getz ubs2segs mem img imgl j Himg ltac:(lia)) as [Hbyte Hbr].
set (E0 := Ereg regs (map (Z_to_bv 64) [getz imgl j; flt + 4 * j] ++ [])).
set (E := ew_fregs E0 64 (@fp_regs fy)).
assert (HE0 : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E0 k = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HEE : forall k, (k < 64)%nat -> ew E k = ew E0 k) by (intros k Hk; subst E; apply ew_fregs_low; exact Hk).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr).
{ intros k rr Hk. pose proof (u5_range rr). rewrite HEE by lia. apply HE0. exact Hk. }
assert (HUe : bv_unsigned (ew E0 13) = 4 * M) by (rewrite (HE0 13%nat 13%bv eq_refl), Hre; apply unsigned_lit_small; lia).
assert (HUc : bv_unsigned (ew E0 10) = 4 * j) by (rewrite (HE0 10%nat 10%bv eq_refl), Hrc; apply unsigned_lit_small; lia).
assert (HUi : bv_unsigned (ew E0 15) = img + j) by (rewrite (HE0 15%nat 15%bv eq_refl), Hri; apply unsigned_lit_small; lia).
assert (HUi6 : bv_unsigned (ew E0 16) = img + j) by (rewrite (HE0 16%nat 16%bv eq_refl), Hri6; apply unsigned_lit_small; lia).
assert (HU5 : bv_unsigned (ew E0 5) = img) by (rewrite (HE0 5%nat 5%bv eq_refl), Hr5; apply unsigned_lit_small; lia).
assert (HU11 : bv_unsigned (ew E0 11) = 2 ^ 64 - 1 - flt) by (rewrite (HE0 11%nat 11%bv eq_refl), Hr11; apply unsigned_lit_small; lia).
assert (A32 : ew E0 32 = Z_to_bv 64 (getz imgl j)) by (subst E0; apply (Ereg_vals regs [getz imgl j; flt + 4 * j] [] 0%nat); reflexivity).
assert (HU32 : bv_unsigned (ew E0 32) = getz imgl j) by (rewrite A32; apply unsigned_lit_small; lia).
assert (A33 : ew E0 33 = Z_to_bv 64 (flt + 4 * j)) by (subst E0; apply (Ereg_vals regs [getz imgl j; flt + 4 * j] [] 1%nat); reflexivity).
assert (HU33 : bv_unsigned (ew E0 33) = flt + 4 * j) by (rewrite A33; apply unsigned_lit_small; lia).
assert (Hpres : forall i, 0 <= i < 4 -> writable_at ubs2segs mem (flt + 4 * j + i)).
{ intros i Hi. replace (flt + 4 * j + i) with (flt + (4 * j + i)) by lia. apply (present_writable ubs2_msyms).
apply (proj1 (heap_blocks _ _ LAWS Lq Aq mem mdq flt (4 * M) (4 * j + i) (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) Hfin ltac:(lia))). }
assert (HS0 : @st_ok ubs2segs fy E0 ss_L4x (@mkst fy regs (Z_to_bv 64 PC_L4) mem (seg_rom ubs2segs))).
{ unfold ss_L4x. subst E0. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | cbn [sv_denot]; exact Hr12] | intros X; discriminate X | cbn [sv_denot]; exact Hr14].
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HUi.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, HU32; reflexivity | cbn; lia | cbn; lia |].
apply val_mem_byte; [rewrite Z.add_0_r; exact Hbyte | lia].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU33.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hpres; lia | constructor].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU33, HUi. repeat split; lia.
- split; [|split].
+ cbn [f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite HUi, HUi6, HU5, HU11, HUc, HU33, HU32.
change (2 ^ 2) with 4. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
assert ((flt + 4 * j) mod 4 = 0) by (replace (flt + 4 * j) with (flt + j * 4) by lia; rewrite Z.mod_add by lia; exact Hflt4).
assert ((4 * j) mod 4 = 0) by (replace (4 * j) with (j * 4) by lia; apply Z.mod_mul; lia).
repeat split; lia.
+ cbn [f_conds conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U.
rewrite (U_atom _ 16 (img + j) ltac:(rewrite (HE0 16%nat 16%bv eq_refl); exact Hri6)), (U_atom _ 5 img ltac:(rewrite (HE0 5%nat 5%bv eq_refl); exact Hr5)) by lia.
split; [apply negb_true_iff, Z.ltb_ge; lia | exact I].
+ cbn [f_alias alias_ok]. split; [|exact I]. apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom _ 24 flt ltac:(rewrite (HE0 24%nat 24%bv eq_refl); exact Hr24)), (U_atom _ 10 (4 * j) ltac:(rewrite (HE0 10%nat 10%bv eq_refl); exact Hrc)),
(U_atom _ 33 (flt + 4 * j) A33) by lia. apply zcanon_small. lia. }
pose proof (st_ok_enterF ubs2segs fy 64 E0 ss_L4x _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS.
change (ew_fregs E0 64 (@fp_regs fy)) with E in HS.
change (mkSST (ss_pc ss_L4x) (ss_regs ss_L4x) (sfr_atoms 64) (ss_mem ss_L4x) (ss_resv ss_L4x) (ss_facts ss_L4x)) with ss_L4 in HS.
rewrite <- !HEE in HUe, HUc, HUi, HUi6, HU33 by lia.
change mem with (ms_mem (@mkst fy regs (Z_to_bv 64 PC_L4) mem (seg_rom ubs2segs))) in HJ.
assert (Hwr : forall cs1 cs2, wr_ok E [YQ0b.mkRegion (Some 15%nat) 0 1 0 0 cs1; YQ0b.mkRegion (Some 33%nat) 0 4 0 4 cs2] RGBA_STK sp0v FPv (blocks L A) (blocks Lq Aq)).
{ intros cs1 cs2. apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_gen; [reflexivity | exact HU33 | cbn [r_wlo r_whi]; intros a Ha; replace a with (flt + (a - flt)) by lia; apply Hwb; lia | apply wr_ok_nil]. }
jrunF_to LAWS ubs2tbl_ok HS HJ PC_L4X. { wr_ok_eval. apply Hwr. }
cbn [ms_mem mkst] in HF, HJ.
assert (POST : forall ss1 ms1 pc, st_okF ubs2segs E ss1 ms1 -> ss_regs ss1 = ss_regs (fst (sym_run_toFN ubs2segs ubs2tbl FUEL PC_L4X ss_L4)) ->
ss_resv ss1 = None -> ss_pc ss1 = pc ->
journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq (ms_mem ms1) mdq ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (flt + 4 * j <= a < flt + 4 * (j + 1)) -> mbyte ubs2segs (ms_mem ms1) a = mbyte ubs2segs mem a) ->
L4_post fy regs mem pc (j + 1) j (mkCfg ms1 mdq)).
{ intros ss1 ms1 pc HS1 Hr1 Hrv1 Hpc1 HJ1 Hmb.
match type of Hr1 with _ = ss_regs (fst ?x) => let v := eval vm_compute in (ss_regs (fst x)) in change (ss_regs (fst x)) with v in Hr1 end.
exists (fp_of ms1), (ms_regs ms1), (ms_mem ms1).
split; [rewrite (st_okF_mkst ubs2segs E ss1 ms1 HS1 Hrv1), Hpc1; reflexivity|].
split; [exact HJ1|]. split; [exact (st_okF_frm ubs2segs E _ _ HS1)|].
split; [rewrite (st_okF_reg ubs2segs E ss1 ms1 10%bv HS1), Hr1; eval_sr_get; cbn [sv_denot]; rewrite HUc; f_equal; lia|].
split; [rewrite (st_okF_reg ubs2segs E ss1 ms1 15%bv HS1), Hr1; eval_sr_get; cbn [sv_denot]; rewrite HUi; f_equal; lia|].
split; [rewrite (st_okF_reg ubs2segs E ss1 ms1 16%bv HS1), Hr1; eval_sr_get; cbn [sv_denot]; rewrite HUi6; f_equal; lia|].
split; [rewrite (st_okF_reg ubs2segs E ss1 ms1 12%bv HS1), Hr1; eval_sr_get; reflexivity|].
split; [rewrite (st_okF_reg ubs2segs E ss1 ms1 14%bv HS1), Hr1; eval_sr_get; reflexivity|].
split; [exact (st_okF_regs_kept ubs2segs E ss1 ms1 _ L4_KEEP HS1 ltac:(intros rr _; apply HE; pose proof (u5_range rr); unfold ridx; lia) ltac:(rewrite Hr1; vm_compute; reflexivity))|].
exact Hmb. }
jbranchF ubs2tbl HS.
- rewrite branch_ne_U, !U_SOff, HUe, HUc, !zcanon_id in Hc by (unfold M64; lia).
destruct (Z_lt_ge_dec (j + 1) M) as [Hlt|Hge]; [| exfalso; destruct (Z.eqb_spec (4 * M + 0) (4 * j + 4)); [discriminate Hc | lia]].
jrunF_to LAWS ubs2tbl_ok HS HJ PC_L4. { wr_ok_eval. apply Hwr. }
cbn [ms_mem mkst] in HF0, HJ. replace (j + 1 <? M) with true by (symmetry; apply Z.ltb_lt; lia).
apply SR_ret. eapply (POST _ _ PC_L4 HS); [reflexivity | reflexivity | reflexivity | exact HJ |].
intros a Ha Hna. mb_frames ltac:(exact Ha) ltac:(rewrite ?HU33, ?HUi; lia). reflexivity.
- rewrite branch_ne_U, !U_SOff, HUe, HUc, !zcanon_id in Hc by (unfold M64; lia).
destruct (Z_lt_ge_dec (j + 1) M) as [Hlt|Hge]; [exfalso; destruct (Z.eqb_spec (4 * M + 0) (4 * j + 4)); [lia | discriminate Hc] |].
jrunF_to LAWS ubs2tbl_ok HS HJ PC_L4X. { wr_ok_eval. apply Hwr. }
cbn [ms_mem mkst] in HF0, HJ. replace (j + 1 <? M) with false by (symmetry; apply Z.ltb_ge; lia).
apply SR_ret. eapply (POST _ _ PC_L4X HS); [reflexivity | reflexivity | reflexivity | exact HJ |].
intros a Ha Hna. mb_frames ltac:(exact Ha) ltac:(rewrite ?HU33, ?HUi; lia). reflexivity.
Qed.
Lemma L4_loop : forall (k : nat) (fy : FPState) (regs : bvmap 5 word) mem (j : Z),
0 <= j < M -> Z.of_nat k = M - 1 - j ->
journal ubs2_msyms MR RGBA_STK sp0v FPv L A mem0 md0 Lq Aq mem mdq -> frm_zero (@fp_csr fy) ->
getr regs 13 = Z_to_bv 64 (4 * M) -> getr regs 10 = Z_to_bv 64 (4 * j) -> getr regs 15 = Z_to_bv 64 (img + j) ->
getr regs 16 = Z_to_bv 64 (img + j) -> getr regs 5 = Z_to_bv 64 img -> getr regs 24 = Z_to_bv 64 flt ->
getr regs 11 = Z_to_bv 64 (2 ^ 64 - 1 - flt) -> getr regs 12 = Z_to_bv 64 0 -> getr regs 14 = Z_to_bv 64 1 ->
arr8 ubs2segs mem img imgl ->
SR ubs2segs (mkCfg (@mkst fy regs (Z_to_bv 64 PC_L4) mem (seg_rom ubs2segs)) mdq) (L4_post fy regs mem PC_L4X M j).
Proof.
induction k as [|k IH]; intros fy regs mem j Hj Hk HJ Hfrm Hre Hrc Hri Hri6 Hr5 Hr24 Hr11 Hr12 Hr14 Himg; pose proof (proj1 alloc_ceiling_val) as Hac.
- assert (Hlast : j + 1 = M) by lia.
eapply SR_mono; [exact (L4_step fy regs mem j Hj HJ Hfrm Hre Hrc Hri Hri6 Hr5 Hr24 Hr11 Hr12 Hr14 Himg)|].
cbv beta. intros c' (fy' & regs' & mem' & -> & HJ' & Hfrm' & Gc & Gi & Gi6 & G12 & G14 & Gk & Hm').
replace (j + 1 <? M) with false by (symmetry; apply Z.ltb_ge; lia). rewrite Hlast in Gc, Gi, Gi6.
exists fy', regs', mem'. repeat (split; [first [reflexivity | assumption]|]).
intros a Ha Hna. apply Hm'; [exact Ha | lia].
- eapply SR_bind; [exact (L4_step fy regs mem j Hj HJ Hfrm Hre Hrc Hri Hri6 Hr5 Hr24 Hr11 Hr12 Hr14 Himg)|].
cbv beta. intros c' (fy' & regs' & mem' & -> & HJ' & Hfrm' & Gc & Gi & Gi6 & G12 & G14 & Gk & Hm').
replace (j + 1 <? M) with true by (symmetry; apply Z.ltb_lt; lia).
assert (Himg' : arr8 ubs2segs mem' img imgl).
{ eapply arr8_frame; [exact Himg|]. intros a Ha. apply Hm'; lia. }
eapply SR_mono; [exact (IH fy' regs' mem' (j + 1) ltac:(lia) ltac:(lia) HJ' Hfrm' ltac:(rewrite (Gk 13%bv ltac:(cbv; tauto)); exact Hre) Gc Gi Gi6
ltac:(rewrite (Gk 5%bv ltac:(cbv; tauto)); exact Hr5) ltac:(rewrite (Gk 24%bv ltac:(cbv; tauto)); exact Hr24) ltac:(rewrite (Gk 11%bv ltac:(cbv; tauto)); exact Hr11)
G12 G14 Himg')|].
cbv beta. intros c'' (fy'' & regs'' & mem'' & -> & HJ'' & Hfrm'' & Gc' & Gi' & Gi6' & G12' & G14' & Gk' & Hm'').
exists fy'', regs'', mem''. split; [reflexivity|]. split; [exact HJ''|]. split; [exact Hfrm''|]. split; [exact Gc'|]. split; [exact Gi'|]. split; [exact Gi6'|].
split; [exact G12'|]. split; [exact G14'|].
split; [intros rr Hrr; rewrite (Gk' rr Hrr); apply Gk; exact Hrr|].
intros a Ha Hna. rewrite (Hm'' a Ha) by lia. apply Hm'; [exact Ha | lia].
Qed.
End L4.
Definition ss_QT0 : sstate :=
mkSS PC_QT sr_atoms [ YQ0b.mkRegion (Some 2%nat) 0 RGBA_FRAME 0 0 [mkChunk SL_80 (CVal 8 (SOff 32 0))] ] None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4) ] [] []).
Definition ss_GP1 : sstate := mkSS PC_GP1 sr_atoms [] None (mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4) ] [] []).
Definition ss_FR1 : sstate :=
mkSS PC_FR1 sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 0 RGBA_FRAME 0 0 [mkChunk SL_N (CVal 8 (SOff 32 0)); mkChunk SL_120 (CVal 8 (SOff 33 0))] ] None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (32%nat, mkAF 1 RGB_NMAX 0); (33%nat, mkAF 3 4 0) ] [] []).
Definition ss_MA1 : sstate :=
mkSS PC_MA1 sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 0 RGBA_FRAME 0 0 [mkChunk SL_112 (CVal 8 (SOff 32 0)); mkChunk SL_120 (CVal 8 (SOff 33 0))] ] None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (10%nat, mkAF 4096 CEIL_MAX 4); (18%nat, mkAF 3 (4 * RGB_NMAX) 0);
(32%nat, mkAF 4096 CEIL_MAX 0) ] [] []).
Definition ss_MA0 : sstate :=
mkSS PC_MA1 (sr_set sr_atoms 10%bv (SLit 0)) [] None (mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4) ] [] []).
Definition ss_L4X : sstate :=
mkSS PC_L4X sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 0 RGBA_FRAME 0 0
[mkChunk SL_32 (CVal 8 (SOff 32 0)); mkChunk SL_40 (CVal 8 (SOff 33 0)); mkChunk SL_64 (CVal 8 (SOff 34 0))] ] None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4) ] [] []).
Definition QT_KS1 : list reg := [2; 3; 4; 8; 9; 18; 20; 21; 22; 24; 25; 26; 27]%bv.
Lemma QT_at : forall regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt fdp pal t,
K_DI (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest ->
K_ND (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest ->
K_XT2 (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest ->
frm_zero (@fp_csr fxi) ->
at_QT (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest
regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt fdp pal t ->
SR ubs2segs (mkCfg (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_QT) memc (seg_rom ubs2segs)) mdc)
(rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Proof.
intros regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt fdp pal t KDI KND KXT2 HFRM HAT.
destruct HAT as (HINV & HREGS & Hfmt & HN1 & Hha & Hcnt & G24 & G20 & G8 & G21 &
Hsl & Hsq & S80q & Hfc & Hobj & Hcg & Himg & Hchq & Htok & Hpnew & Hfimg & Hfdp & HB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbef & HBent).
destruct HREGS as (G2 & G3 & G4).
pose proof Htok as (Htree & Hfull & Hth & Hwft & Hmeans & Hnodes).
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (Hroc : ubs2_rgb_rodata_ok memc).
{ pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & Hik). exact (ubs2_rgb_rodata_kept mem0 memc Hik Hro). }
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity.
assert (HSZ : RGB_SIZE = 64) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity. assert (HCSv : CHT_SIZE = 48) by reflexivity.
assert (HGPv : GETPAL_STK = 16464) by reflexivity. assert (HNMv : RGB_NMAX = 10000) by reflexivity.
assert (Hsp16 : spv mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (Rtr : 0 <= troot t < 2 ^ 64).
{ destruct t as [|n0|n0 l0 r0]; cbn [troot]; [lia| |];
pose proof (Hnodes n0 ltac:(cbn; left; reflexivity)) as X; unfold NODE_SIZE in X; lia. }
set (keep := (BASEv ++ [(pnew, fmt * N); (fimg, N)]) ++ cht_blks C ++ tree_blocks t).
assert (HB' : Permutation (blocks Lc Ac) (keep ++ [(fdp, 4 * cnt)])).
{ eapply Permutation_trans; [exact HB|]. subst keep. rewrite <- !app_assoc. repeat (apply Permutation_app_head).
apply Permutation_app_comm. }
assert (HBf : Permutation (blocks Lc Ac) ((fdp, 4 * cnt) :: keep)).
{ eapply Permutation_trans; [exact HB'|]. apply Permutation_sym. apply Permutation_cons_append. }
assert (Hsub : forall x0, In x0 BASEv -> In x0 keep) by (intros x0 Hx0; subst keep; apply in_app_iff; left; apply in_app_iff; left; exact Hx0).
assert (Hkeep_rng : forall b m, In (b, m) keep -> 0 < m -> 4096 <= b /\ b + m <= alloc_ceiling).
{ intros b m Hbm Hm. destruct (heap_blocks_range _ _ LAWS _ _ _ _ b m HHc ltac:(eapply blocks_perm_in; [exact HBf | right; exact Hbm]) Hm) as (X1 & X2 & _). lia. }
assert (Htb : forall b, In b (tree_blocks t) -> In b (blocks Lc Ac)).
{ intros b Hb. eapply blocks_perm_in; [exact HBf|]. right. subst keep. apply in_app_iff. right. apply in_app_iff. right. exact Hb. }
assert (HfN : 0 < fmt * N) by (destruct Hfmt as [Hf|Hf]; rewrite Hf; lia).
assert (Rfimg : 0 <= fimg < 2 ^ 64).
{ pose proof (Hkeep_rng fimg N ltac:(subst keep; apply in_app_iff; left; apply in_app_iff; right; right; left; reflexivity) ltac:(lia)). lia. }
assert (Rpnew : 0 <= pnew < 2 ^ 64).
{ pose proof (Hkeep_rng pnew (fmt * N) ltac:(subst keep; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity) HfN). lia. }
assert (Rfattr : 0 <= fattr < 2 ^ 32).
{ pose proof Hcfp as X. cbn [obj_at LAY_RgbFrameConfig] in X. destruct X as (_ & _ & [_ Rf] & _). cbn in Rf. lia. }
assert (RW : 0 <= W < 2 ^ 16).
{ pose proof Hobj as X. unfold rgb_obj in X. cbn [obj_at LAY_Rgb] in X. destruct X as (_ & _ & _ & _ & _ & _ & _ & [_ Rf] & _). cbn in Rf. lia. }
assert (Rnha : 0 <= nha ha <= 1) by (unfold nha; destruct (ha =? 0); lia).
set (E := Ereg regs1 (map (Z_to_bv 64) [troot t] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (D32 : ew E 32 = Z_to_bv 64 (troot t)) by (subst E; apply (Ereg_vals regs1 [troot t] [] 0%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = spv) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (HS : st_ok (fx:=fxi) ubs2segs E ss_QT0 (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_QT) memc (seg_rom ubs2segs))).
{ unfold ss_QT0. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [unfold sp, sp0, RGBA_FRAME in *; lia|]. split; [unfold sp, sp0, RGBA_FRAME in *; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, D32, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact S80q].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2.
change (2 ^ 4) with 16. unfold sp, sp0, RGBA_FRAME in *. repeat split; lia. }
change memc with (ms_mem (mkst (fx:=fxi) regs1 (Z_to_bv 64 PC_QT) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_get_palette_from_decision_tree. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (Hmm : ms_mem ms = memc).
{ apply functional_extensionality. intros x0. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => exact (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF x0) end. }
jreg HS (10%bv:reg) as Hr10. rewrite D32 in Hr10.
jreg HS (19%bv:reg) as Hr19. rewrite D32 in Hr19.
jreg HS (11%bv:reg) as Hr11. rewrite HU2 in Hr11.
jreg HS (2%bv:reg) as Hr2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hr2.
jreg HS (1%bv:reg) as Hr1.
assert (HG1 : getr (ms_regs ms) 1 = Z_to_bv 64 PC_GP1) by (rewrite Hr1; reflexivity).
assert (Hspms : spZ (ms_regs ms) = spv) by (unfold spZ; rewrite Hr2; apply unsigned_lit_small; unfold sp, sp0, RGBA_FRAME in *; lia).
pose proof (regs_kept_of_st_ok _ _ _ _ regs1 _ QT_KS1 HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as Hk1. cbn [ms_regs mkst] in Hk1.
rewrite (st_ok_mkst ubs2segs E _ _ HS eq_refl). cbn [ss_pc ms_regs ms_mem mkst]. rewrite Hmm. rewrite Hmm in HJ.
eapply SR_bind.
{ eapply (GETPAL fxi RGBA_STK sp0v FPv L A mem0 md0 Lc Ac memc mdc (ms_regs ms) t (spv + OFF_apal) HJ);
[ rewrite HG1; apply ret_ok_even; vm_compute; reflexivity
| rewrite Hspms; exact Hsp16
| rewrite Hspms; unfold sp, sp0, RGBA_FRAME in *; lia
| rewrite Hspms; unfold sp, sp0, RGBA_FRAME in *; lia
| exact HFRM | exact Hr10 | rewrite Hr11; unfold OFF_apal; reflexivity
| exact Htree | exact Hfull | exact Hth | exact Hwft | exact Hmeans | exact Htb
| rewrite Hspms; unfold OFF_apal; lia | unfold OFF_apal, sp, sp0, RGBA_FRAME in *; lia | exact Hroc ]. }
cbv beta. intros c1 (fx2 & regs2 & mem2 & -> & Hfrm2 & Hfp2 & HJ2 & HP2 & Hm2). clear HJ.
rewrite HG1, Hspms in *.
pose proof (fun (rr : reg) (Hc : In rr QT_KS1) => eq_trans (regs_preserved_in _ _ rr HP2 (in_subq_qt QT_KS1 CALLEE_SAVED ltac:(vm_compute; reflexivity) rr Hc)) (Hk1 rr Hc)) as Hk2.
assert (V19 : getr regs2 19 = Z_to_bv 64 (troot t)) by (rewrite (regs_preserved_in _ _ 19%bv HP2 ltac:(cbv; tauto)); exact Hr19).
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> (a < spv - GETPAL_STK \/ spv <= a) -> ~ (spv + OFF_apal <= a < spv + OFF_apal + 768) ->
mbyte ubs2segs mem2 a = mbyte ubs2segs memc a).
{ intros a Ha H1 H2. apply Hm2; [exact Ha | lia | exact H2]. }
assert (K2b : forall b m i, In (b, m) ((fdp, 4 * cnt) :: keep) -> 0 <= i < m -> mbyte ubs2segs mem2 (b + i) = mbyte ubs2segs memc (b + i)).
{ intros b m i Hbm Hi.
destruct (heap_blocks_range _ _ LAWS _ _ _ _ b m HHc ltac:(eapply blocks_perm_in; [exact HBf | destruct Hbm as [<-|Hbm]; [left; reflexivity | right; exact Hbm]]) ltac:(lia)) as (X1 & X2 & _).
apply K2; [lia | left; unfold sp, sp0, RGBA_FRAME in *; lia | unfold OFF_apal, sp, sp0, RGBA_FRAME in *; lia]. }
clear HS HF Hmm. set (E2 := Ereg regs2 []).
assert (HE2 : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E2 n = getr regs2 rr) by (intros; subst E2; apply ew_Ereg_nat; assumption).
assert (HU2b : bv_unsigned (ew E2 2) = spv) by (rewrite (HE2 2%nat 2%bv eq_refl), (Hk2 2%bv ltac:(cbv; tauto)), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (HS : st_ok (fx:=fx2) ubs2segs E2 ss_GP1 (mkst (fx:=fx2) regs2 (Z_to_bv 64 PC_GP1) mem2 (seg_rom ubs2segs))).
{ unfold ss_GP1. subst E2. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor.
- cbn [pairwise_disjoint all_disjoint]. exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2b.
change (2 ^ 4) with 16. unfold sp, sp0, RGBA_FRAME in *. repeat split; lia. }
change mem2 with (ms_mem (mkst (fx:=fx2) regs2 (Z_to_bv 64 PC_GP1) mem2 (seg_rom ubs2segs))) in HJ2.
jrun_to LAWS ubs2tbl_ok HS HJ2 ubs2_A_free. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (Hmm2 : ms_mem ms0 = mem2) by (apply functional_extensionality; intros x0; apply (frame_of_nil _ _ _ _ HF)).
jreg HS (10%bv:reg) as Fr10. rewrite (HE2 24%nat 24%bv eq_refl), (Hk2 24%bv ltac:(cbv; tauto)), G24 in Fr10.
jreg HS (2%bv:reg) as Fr2. rewrite (HE2 2%nat 2%bv eq_refl), (Hk2 2%bv ltac:(cbv; tauto)), G2 in Fr2.
jreg HS (4%bv:reg) as Fr4. rewrite (HE2 4%nat 4%bv eq_refl), (Hk2 4%bv ltac:(cbv; tauto)), G4, Htp0 in Fr4.
jreg HS (1%bv:reg) as Fr1.
assert (FG1 : getr (ms_regs ms0) 1 = Z_to_bv 64 PC_FR1) by (rewrite Fr1; reflexivity).
pose proof (regs_kept_of_st_ok _ _ _ _ regs2 _ CALLEE_SAVED HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as Hk3. cbn [ms_regs mkst] in Hk3.
eapply SR_bind.
{ eapply (jfree_at _ _ LAWS ubs2_errno_low IMG (aa_free API)) with (a := fdp) (n := 4 * cnt) (spc := spv);
[ exact HS | reflexivity | reflexivity | exact HJ2
| eapply blocks_perm_in; [exact HBf | left; reflexivity]
| exact Fr10 | exact Fr2 | unfold sp, sp0, RGBA_FRAME in *; lia | exact Hsp16
| unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp, sp0, RGBA_FRAME in *; lia
| exact Fr4 | exact FG1 | apply ret_ok_even; vm_compute; reflexivity | ].
intros Hin0. exfalso.
exact (proj2 (tmp_of_station API L A r g bef beffmt s N img fmt rest Lc Ac memc mdc keep [(fdp, 4 * cnt)] fdp (4 * cnt) HHc HB' HBent Hsub ltac:(left; reflexivity) ltac:(lia)) Hin0). }
cbv beta. intros c2 (L3 & A3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hrm3 & Hkeep3 & Hhi3 & Hinit3). clear HJ2.
rewrite Hmm2 in *. cbn [ms_regs ms_mem mkst] in HP3, Hkeep3, Hhi3, HJ3.
change (ms_segs ubs2_msyms) with ubs2segs in Hkeep3, Hhi3.
pose proof (perm_after_rm1 _ _ _ _ HBf Hrm3) as HB3.
pose proof (fun (rr : reg) (Hc : In rr CALLEE_SAVED) => eq_trans (regs_preserved_in _ _ rr HP3 Hc) (Hk3 rr Hc)) as Hk4.
assert (K3 : forall a, alloc_ceiling <= a < 2 ^ 64 -> spv <= a -> mbyte ubs2segs mem3 a = mbyte ubs2segs mem2 a).
{ intros a Ha Hs. apply (proj1 (Hhi3 a Ha ltac:(lia))). }
assert (K3b : forall b m i, In (b, m) keep -> 0 <= i < m -> mbyte ubs2segs mem3 (b + i) = mbyte ubs2segs mem2 (b + i)).
{ intros b m i Hbm Hi. apply (Hkeep3 b m i); [| exact Hi]. eapply Permutation_in; [apply Permutation_sym; exact HB3 | exact Hbm]. }
assert (KH3 : forall x, alloc_ceiling <= x < 2 ^ 64 -> spv <= x -> ~ (spv + OFF_apal <= x < spv + OFF_apal + 768) -> mbyte ubs2segs mem3 x = mbyte ubs2segs memc x).
{ intros x Hx Hs Hna. rewrite (K3 x Hx Hs). apply K2; [lia | right; exact Hs | exact Hna]. }
assert (KB3 : forall b m i, In (b, m) (BASEv ++ cht_blks C ++ tree_blocks t) -> 0 <= i < m -> mbyte ubs2segs mem3 (b + i) = mbyte ubs2segs memc (b + i)).
{ intros b m i Hbm Hi.
assert (Hk : In (b, m) keep) by (subst keep; apply in_app_iff in Hbm as [Hbm|Hbm]; [apply in_app_iff; left; apply in_app_iff; left; exact Hbm | apply in_app_iff; right; exact Hbm]).
rewrite (K3b b m i Hk Hi). apply (K2b b m i); [right; exact Hk | exact Hi]. }
clear HS HF.
destruct (qfk memc mem3 ha pnew fimg imgl C cnt pal t Hceil H63 Hfmt KH3 KB3) as (_ & TS3 & TQ3 & _).
pose proof (TS3 Hsl) as (S8 & _). pose proof (TQ3 Hsq) as ((_ & _ & _ & _ & S120) & _).
set (E3 := Ereg regs3 (map (Z_to_bv 64) [N; fmt] ++ [])).
assert (HE3 : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E3 n = getr regs3 rr) by (intros; subst E3; apply ew_Ereg_nat; assumption).
assert (A32 : ew E3 32 = Z_to_bv 64 N) by (subst E3; apply (Ereg_vals regs3 [N; fmt] [] 0%nat); reflexivity).
assert (A33 : ew E3 33 = Z_to_bv 64 fmt) by (subst E3; apply (Ereg_vals regs3 [N; fmt] [] 1%nat); reflexivity).
assert (HU2c : bv_unsigned (ew E3 2) = spv) by (rewrite (HE3 2%nat 2%bv eq_refl), (Hk4 2%bv ltac:(cbv; tauto)), (Hk2 2%bv ltac:(cbv; tauto)), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (HS : st_ok (fx:=fx2) ubs2segs E3 ss_FR1 (mkst (fx:=fx2) regs3 (Z_to_bv 64 PC_FR1) mem3 (seg_rom ubs2segs))).
{ unfold ss_FR1. subst E3. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2c.
split; [unfold sp, sp0, RGBA_FRAME in *; lia|]. split; [unfold sp, sp0, RGBA_FRAME in *; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A32, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact S8].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, A33, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact S120].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2c, A32, A33, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold sp, sp0, RGBA_FRAME in *. repeat split; lia. }
change mem3 with (ms_mem (mkst (fx:=fx2) regs3 (Z_to_bv 64 PC_FR1) mem3 (seg_rom ubs2segs))) in HJ3.
jrun_to LAWS ubs2tbl_ok HS HJ3 ubs2_A_malloc. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
lazymatch goal with |- SR _ (mkCfg ?msx _) _ => rename msx into msM end.
cbn [ms_mem mkst] in HF.
assert (Hmm3 : ms_mem msM = mem3).
{ apply functional_extensionality. intros x0. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => exact (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF x0) end. }
destruct (U_mulw_shl E3 33 32 fmt N A33 A32 ltac:(lia) ltac:(lia)) as (HUm & HUa & HUs).
jreg HS (2%bv:reg) as Mr2. jreg HS (4%bv:reg) as Mr4. jreg HS (1%bv:reg) as Mr1.
rewrite (HE3 2%nat 2%bv eq_refl), (Hk4 2%bv ltac:(cbv; tauto)), (Hk2 2%bv ltac:(cbv; tauto)), G2 in Mr2.
rewrite (HE3 4%nat 4%bv eq_refl), (Hk4 4%bv ltac:(cbv; tauto)), (Hk2 4%bv ltac:(cbv; tauto)), G4, Htp0 in Mr4.
assert (MG1 : getr (ms_regs msM) 1 = Z_to_bv 64 PC_MA1) by (rewrite Mr1; reflexivity).
pose proof (st_ok_reg ubs2segs E3 _ _ 18%bv HS) as Mr18. eval_sr_get_in Mr18. cbn [ms_regs mkst] in Mr18. rewrite denot_lit_U, HUm in Mr18.
pose proof (st_ok_reg ubs2segs E3 _ _ 9%bv HS) as Mr9. eval_sr_get_in Mr9. cbn [ms_regs mkst] in Mr9. rewrite denot_lit_U, HUs in Mr9.
pose proof (st_ok_reg ubs2segs E3 _ _ 10%bv HS) as Mr10'. eval_sr_get_in Mr10'. cbn [ms_regs mkst] in Mr10'. rewrite denot_lit_U, HUa in Mr10'.
jreg HS (25%bv:reg) as Mr25. rewrite A32 in Mr25.
pose proof (regs_kept_of_st_ok _ _ _ _ regs3 _ [2; 3; 4; 8; 19; 20; 21]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as Hk5. cbn [ms_regs mkst] in Hk5.
eapply SR_bind.
{ eapply (jmalloc_at _ _ LAWS ubs2_errno_low IMG (aa_malloc API)) with (n := 4 * (fmt * N)) (spc := spv);
[ exact HS | reflexivity | reflexivity | exact HJ3 | exact Hinit3 | exact Mr10' | lia
| exact Mr2 | unfold sp, sp0, RGBA_FRAME in *; lia | exact Hsp16 | unfold sp, sp0, RGBA_FRAME in *; lia | unfold sp, sp0, RGBA_FRAME in *; lia
| exact Mr4 | exact MG1 | apply ret_ok_even; vm_compute; reflexivity ]. }
cbv beta. intros c3 (L4 & A4 & regs4 & mem4 & md4 & flt & -> & HJ4 & Hinit4 & HP4 & Hf10 & Hres & Hkeep4 & Hhi4). clear HJ3.
rewrite Hmm3 in *. cbn [ms_regs ms_mem mkst] in HP4, Hkeep4, Hhi4, HJ4.
change (ms_segs ubs2_msyms) with ubs2segs in Hkeep4, Hhi4.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HH4.
pose proof (fun (rr : reg) (Hc : In rr CALLEE_SAVED) => regs_preserved_in _ _ rr HP4 Hc) as HP4k. cbn [ms_regs mkst] in HP4k.
assert (W2 : getr regs4 2 = Z_to_bv 64 spv) by (rewrite (HP4k 2%bv ltac:(cbv; tauto)); exact Mr2).
assert (W3 : getr regs4 3 = getr regs0 3) by (rewrite (HP4k 3%bv ltac:(cbv; tauto)), (Hk5 3%bv ltac:(cbv; tauto)), (Hk4 3%bv ltac:(cbv; tauto)), (Hk2 3%bv ltac:(cbv; tauto)); exact G3).
assert (W4 : getr regs4 4 = getr regs0 4) by (rewrite (HP4k 4%bv ltac:(cbv; tauto)), (Hk5 4%bv ltac:(cbv; tauto)), (Hk4 4%bv ltac:(cbv; tauto)), (Hk2 4%bv ltac:(cbv; tauto)); exact G4).
assert (W8 : getr regs4 8 = Z_to_bv 64 r) by (rewrite (HP4k 8%bv ltac:(cbv; tauto)), (Hk5 8%bv ltac:(cbv; tauto)), (Hk4 8%bv ltac:(cbv; tauto)), (Hk2 8%bv ltac:(cbv; tauto)); exact G8).
assert (W9 : getr regs4 9 = Z_to_bv 64 (fmt * N * 2 ^ 32)) by (rewrite (HP4k 9%bv ltac:(cbv; tauto)); exact Mr9).
assert (W18 : getr regs4 18 = Z_to_bv 64 (fmt * N)) by (rewrite (HP4k 18%bv ltac:(cbv; tauto)); exact Mr18).
assert (W19 : getr regs4 19 = Z_to_bv 64 (troot t)) by (rewrite (HP4k 19%bv ltac:(cbv; tauto)), (Hk5 19%bv ltac:(cbv; tauto)), (Hk4 19%bv ltac:(cbv; tauto)); exact V19).
assert (W20 : getr regs4 20 = Z_to_bv 64 (ch_c C)) by (rewrite (HP4k 20%bv ltac:(cbv; tauto)), (Hk5 20%bv ltac:(cbv; tauto)), (Hk4 20%bv ltac:(cbv; tauto)), (Hk2 20%bv ltac:(cbv; tauto)); exact G20).
assert (W21 : getr regs4 21 = Z_to_bv 64 2) by (rewrite (HP4k 21%bv ltac:(cbv; tauto)), (Hk5 21%bv ltac:(cbv; tauto)), (Hk4 21%bv ltac:(cbv; tauto)), (Hk2 21%bv ltac:(cbv; tauto)); exact G21).
assert (W25 : getr regs4 25 = Z_to_bv 64 N) by (rewrite (HP4k 25%bv ltac:(cbv; tauto)); exact Mr25).
assert (KH4 : forall x, alloc_ceiling <= x < 2 ^ 64 -> spv <= x -> ~ (spv + OFF_apal <= x < spv + OFF_apal + 768) -> mbyte ubs2segs mem4 x = mbyte ubs2segs memc x).
{ intros x Hx Hs Hna. rewrite (proj1 (Hhi4 x Hx ltac:(lia))). apply KH3; assumption. }
assert (KB4k : forall b m i, In (b, m) keep -> 0 <= i < m -> mbyte ubs2segs mem4 (b + i) = mbyte ubs2segs mem3 (b + i)).
{ intros b m i Hbm Hi. apply (Hkeep4 b m i); [| exact Hi]. eapply Permutation_in; [apply Permutation_sym; exact HB3 | exact Hbm]. }
assert (KB4 : forall b m i, In (b, m) (BASEv ++ cht_blks C ++ tree_blocks t) -> 0 <= i < m -> mbyte ubs2segs mem4 (b + i) = mbyte ubs2segs memc (b + i)).
{ intros b m i Hbm Hi.
assert (Hk : In (b, m) keep) by (subst keep; apply in_app_iff in Hbm as [Hbm|Hbm]; [apply in_app_iff; left; apply in_app_iff; left; exact Hbm | apply in_app_iff; right; exact Hbm]).
rewrite (KB4k b m i Hk Hi). apply (KB3 b m i); assumption. }
destruct (qfk memc mem4 ha pnew fimg imgl C cnt pal t Hceil H63 Hfmt KH4 KB4) as (TR4 & TS4 & TQ4 & TF4 & TO4 & TC4 & TI4 & TH4 & TT4).
pose proof (TS4 Hsl) as Hsl4. pose proof Hsl4 as (_ & _ & S24 & S48).
pose proof (TQ4 Hsq) as Hsq4. pose proof Hsq4 as ((_ & _ & _ & S112 & S120b) & _).
clear HS HF.
destruct Hres as [[-> Hbl4] | (Hfnz & Hf16 & (b1 & b2 & Hbl4 & Hblc4) & Hwb4)].
-
set (E4 := Ereg regs4 []).
assert (HE4 : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E4 n = getr regs4 rr) by (intros; subst E4; apply ew_Ereg_nat; assumption).
assert (HU2d : bv_unsigned (ew E4 2) = spv) by (rewrite (HE4 2%nat 2%bv eq_refl), W2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (HS : st_ok (fx:=fx2) ubs2segs E4 ss_MA0 (mkst (fx:=fx2) regs4 (Z_to_bv 64 PC_MA1) mem4 (seg_rom ubs2segs))).
{ unfold ss_MA0. subst E4. apply entry_st_ok_gen.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros HH0; discriminate HH0 | cbn [sv_denot]; exact Hf10].
- vm_compute. reflexivity.
- constructor.
- cbn [pairwise_disjoint all_disjoint]. exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2d. change (2 ^ 4) with 16. unfold sp, sp0, RGBA_FRAME in *. repeat split; lia. }
change mem4 with (ms_mem (mkst (fx:=fx2) regs4 (Z_to_bv 64 PC_MA1) mem4 (seg_rom ubs2segs))) in HJ4.
jrun_to LAWS ubs2tbl_ok HS HJ4 PC_XT2. { apply wr_ok_nil. }
lazymatch goal with |- SR _ (mkCfg ?msx _) _ => rename msx into msA end.
cbn [ms_mem mkst] in HF, HJ4.
assert (Hmm4 : ms_mem msA = mem4) by (apply functional_extensionality; intros x0; apply (frame_of_nil _ _ _ _ HF)).
rewrite (st_ok_mkst ubs2segs E4 _ _ HS eq_refl). cbn [ss_pc]. rewrite Hmm4. rewrite Hmm4 in HJ4.
pose proof (regs_kept_of_st_ok _ _ _ _ regs4 _ [2; 3; 4; 8; 19; 20; 21]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as Hk6. cbn [ms_regs mkst] in Hk6.
apply (KXT2 fx2 (ms_regs msA) L4 A4 mem4 md4 ha pnew fimg C cnt pal t Hfrm2).
split.
{ split; [exact HJ4|]. split; [exact Hinit4|]. split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
split; [exact (TR4 HRA)|]. split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |].
intros i Hi. unfold RGBFC_SIZE in *. apply KH4; unfold sp, sp0, RGBA_FRAME, OFF_apal in *; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HH|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
split. { split; [rewrite (Hk6 2%bv ltac:(cbv; tauto)); exact W2|]. split; [rewrite (Hk6 3%bv ltac:(cbv; tauto)); exact W3|]. rewrite (Hk6 4%bv ltac:(cbv; tauto)); exact W4. }
split; [exact Hfmt|].
split; [rewrite (Hk6 19%bv ltac:(cbv; tauto)); exact W19|]. split; [rewrite (Hk6 20%bv ltac:(cbv; tauto)); exact W20|]. split; [rewrite (Hk6 21%bv ltac:(cbv; tauto)); exact W21|].
split; [rewrite (Hk6 8%bv ltac:(cbv; tauto)); exact W8|].
split; [exact S24|]. split; [exact S48|]. split; [exact (TO4 Hobj)|]. split; [exact (TC4 Hcg)|]. split; [exact (TH4 Hchq)|].
split; [exact (proj1 (TT4 Htok))|]. split; [exact Hth|]. split; [exact Hpnew|]. split; [exact Hfimg|].
rewrite Hbl4. eapply Permutation_trans; [exact HB3|]. subst keep. rewrite <- !app_assoc. apply Permutation_refl.
-
assert (Hfin : In (flt, 4 * (fmt * N)) (blocks L4 A4)) by (rewrite Hbl4; apply in_app_iff; right; left; reflexivity).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ flt _ HH4 Hfin ltac:(lia)) as (Hf0 & Hf1 & Hfal).
assert (HB4 : Permutation (blocks L4 A4) ((flt, 4 * (fmt * N)) :: keep)).
{ rewrite Hbl4. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. apply perm_skip. rewrite <- Hblc4. exact HB3. }
assert (Hsep4 : forall b m, In (b, m) keep -> flt + 4 * (fmt * N) <= b \/ b + m <= flt).
{ intros b m Hbm. pose proof (heap_sep _ _ LAWS L4 A4 mem4 md4 b1 (flt, 4 * (fmt * N)) b2 (b, m) HH4 Hbl4
ltac:(rewrite <- Hblc4; eapply Permutation_in; [apply Permutation_sym; exact HB3 | exact Hbm])) as X. cbn [fst snd] in X. lia. }
assert (Himgk : In (img, fmt * N) keep).
{ apply Hsub. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
unfold img_block. replace (fmt_okb fmt) with true; [left; reflexivity|]. unfold fmt_okb. destruct Hfmt as [-> | ->]; reflexivity. }
destruct (Hkeep_rng img (fmt * N) Himgk ltac:(lia)) as [Himg0 Himg1].
pose proof (TI4 Himg) as [Harr4 Hzl].
assert (Hwbf : forall i, 0 <= i < 4 * (fmt * N) -> wr_byte RGBA_STK sp0v FPv (blocks L A) (blocks L4 A4) (flt + i)) by (intros i Hi; apply (Hwb4 _ i Hfin Hi)).
assert (Hf4 : flt mod 4 = 0).
{ pose proof (Z.div_mod flt 16 ltac:(lia)) as Hd. rewrite Hfal, Z.add_0_r in Hd. rewrite Hd. replace (16 * (flt / 16)) with ((4 * (flt / 16)) * 4) by lia. apply Z_mod_mult. }
set (E5 := Ereg regs4 (map (Z_to_bv 64) [img; fmt] ++ [])).
assert (HE5 : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E5 n = getr regs4 rr) by (intros; subst E5; apply ew_Ereg_nat; assumption).
assert (B32 : ew E5 32 = Z_to_bv 64 img) by (subst E5; apply (Ereg_vals regs4 [img; fmt] [] 0%nat); reflexivity).
assert (B33 : ew E5 33 = Z_to_bv 64 fmt) by (subst E5; apply (Ereg_vals regs4 [img; fmt] [] 1%nat); reflexivity).
assert (HU2e : bv_unsigned (ew E5 2) = spv) by (rewrite (HE5 2%nat 2%bv eq_refl), W2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (HU10e : bv_unsigned (ew E5 10) = flt) by (rewrite (HE5 10%nat 10%bv eq_refl), Hf10; apply unsigned_lit_small; lia).
assert (HfN4 : fmt * N <= 4 * RGB_NMAX) by (destruct Hfmt as [Hf|Hf]; rewrite Hf; lia).
assert (HU18e : bv_unsigned (ew E5 18) = fmt * N) by (rewrite (HE5 18%nat 18%bv eq_refl), W18; apply unsigned_lit_small; lia).
assert (HU32e : bv_unsigned (ew E5 32) = img) by (rewrite B32; apply unsigned_lit_small; lia).
assert (HS : st_ok (fx:=fx2) ubs2segs E5 ss_MA1 (mkst (fx:=fx2) regs4 (Z_to_bv 64 PC_MA1) mem4 (seg_rom ubs2segs))).
{ unfold ss_MA1. subst E5. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2e.
split; [unfold sp, sp0, RGBA_FRAME in *; lia|]. split; [unfold sp, sp0, RGBA_FRAME in *; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, B32, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact S112].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, B33, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact S120b].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2e, HU10e, HU18e, HU32e.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold sp, sp0, RGBA_FRAME in *. repeat split; lia. }
change mem4 with (ms_mem (mkst (fx:=fx2) regs4 (Z_to_bv 64 PC_MA1) mem4 (seg_rom ubs2segs))) in HJ4.
jrun_to LAWS ubs2tbl_ok HS HJ4 PC_L4. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
lazymatch goal with |- SR _ (mkCfg ?msx _) _ => rename msx into msB end.
cbn [ms_mem mkst] in HF, HJ4.
assert (Hmm4 : ms_mem msB = mem4).
{ apply functional_extensionality. intros x0. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => exact (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF x0) end. }
destruct (U_fill_len E5 9 (fmt * N) ltac:(rewrite (HE5 9%nat 9%bv eq_refl); exact W9) ltac:(lia)) as [_ HUl].
jreg HS (5%bv:reg) as Q5. rewrite B32 in Q5. jreg HS (7%bv:reg) as Q7. rewrite B33 in Q7.
jreg HS (10%bv:reg) as Q10. jreg HS (12%bv:reg) as Q12. jreg HS (14%bv:reg) as Q14.
jreg HS (15%bv:reg) as Q15. rewrite B32 in Q15. jreg HS (16%bv:reg) as Q16. rewrite B32 in Q16.
jreg HS (24%bv:reg) as Q24. rewrite (HE5 10%nat 10%bv eq_refl), Hf10 in Q24.
pose proof (st_ok_reg ubs2segs E5 _ _ 13%bv HS) as Q13. eval_sr_get_in Q13. cbn [ms_regs mkst] in Q13. rewrite denot_lit_U, HUl in Q13.
pose proof (st_ok_reg ubs2segs E5 _ _ 11%bv HS) as Q11. eval_sr_get_in Q11. cbn [ms_regs mkst] in Q11.
rewrite denot_lit_U, (YI01.U_not E5 10 flt ltac:(rewrite (HE5 10%nat 10%bv eq_refl); exact Hf10)) in Q11 by lia.
pose proof (regs_kept_of_st_ok _ _ _ _ regs4 _ [2; 3; 4; 8; 19; 20; 21; 25]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as Hk7. cbn [ms_regs mkst] in Hk7.
rewrite (st_ok_mkst ubs2segs E5 _ _ HS eq_refl). cbn [ss_pc]. rewrite Hmm4. rewrite Hmm4 in HJ4. clear HS HF.
eapply SR_bind.
{ eapply (L4_loop L4 A4 md4 flt (fmt * N) imgl ltac:(lia) Hzl Himg0 Himg1 Hf0 Hf1 Hf4
ltac:(destruct (Hsep4 img (fmt * N) Himgk); lia) Hfin Hwbf (Z.to_nat (fmt * N - 1)) fx2 (ms_regs msB) mem4 0 ltac:(lia) ltac:(lia) HJ4 Hfrm2 Q13);
[ rewrite Q10; f_equal; lia | rewrite Q15; f_equal; lia | rewrite Q16; f_equal; lia | exact Q5 | exact Q24 | exact Q11 | exact Q12 | exact Q14 | exact Harr4 ]. }
cbv beta. intros c4 (fy5 & regs5 & mem5 & -> & HJ5 & Hfrm5 & V10 & V15 & V16 & V12 & V14 & Hk8 & Hm5). clear HJ4.
assert (KH5 : forall x, alloc_ceiling <= x < 2 ^ 64 -> spv <= x -> ~ (spv + OFF_apal <= x < spv + OFF_apal + 768) -> mbyte ubs2segs mem5 x = mbyte ubs2segs memc x).
{ intros x Hx Hs Hna. rewrite (Hm5 x) by lia. apply KH4; assumption. }
assert (KB5 : forall b m i, In (b, m) (BASEv ++ cht_blks C ++ tree_blocks t) -> 0 <= i < m -> mbyte ubs2segs mem5 (b + i) = mbyte ubs2segs memc (b + i)).
{ intros b m i Hbm Hi.
assert (Hk : In (b, m) keep) by (subst keep; apply in_app_iff in Hbm as [Hbm|Hbm]; [apply in_app_iff; left; apply in_app_iff; left; exact Hbm | apply in_app_iff; right; exact Hbm]).
pose proof (Hkeep_rng b m Hk ltac:(lia)) as [R1 R2]. pose proof (Hsep4 b m Hk) as Hs.
rewrite (Hm5 (b + i)) by lia. apply (KB4 b m i); assumption. }
destruct (qfk memc mem5 ha pnew fimg imgl C cnt pal t Hceil H63 Hfmt KH5 KB5) as (TR5 & TS5 & TQ5 & TF5 & TO5 & TC5 & TI5 & TH5 & TT5).
pose proof (TS5 Hsl) as Hsl5. pose proof (TQ5 Hsq) as Hsq5.
pose proof Hsl5 as (_ & _ & _ & _). pose proof Hsq5 as ((S64 & _) & S32 & S40).
assert (S80_5 : slot regs0 mem5 SL_80 (troot t)).
{ unfold slot, word_mem in S80q |- *. intros k Hk. rewrite KH5; [exact (S80q k Hk) | | |]; unfold SL_80, OFF_apal, sp, sp0, RGBA_FRAME in *; lia. }
set (E6 := Ereg regs5 (map (Z_to_bv 64) [fattr; W; nha ha] ++ [])).
assert (HE6 : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E6 n = getr regs5 rr) by (intros; subst E6; apply ew_Ereg_nat; assumption).
assert (C32 : ew E6 32 = Z_to_bv 64 fattr) by (subst E6; apply (Ereg_vals regs5 [fattr; W; nha ha] [] 0%nat); reflexivity).
assert (C33 : ew E6 33 = Z_to_bv 64 W) by (subst E6; apply (Ereg_vals regs5 [fattr; W; nha ha] [] 1%nat); reflexivity).
assert (C34 : ew E6 34 = Z_to_bv 64 (nha ha)) by (subst E6; apply (Ereg_vals regs5 [fattr; W; nha ha] [] 2%nat); reflexivity).
assert (HU2f : bv_unsigned (ew E6 2) = spv) by (rewrite (HE6 2%nat 2%bv eq_refl), (Hk8 2%bv ltac:(cbv; tauto)), (Hk7 2%bv ltac:(cbv; tauto)), W2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (HS : st_ok (fx:=fy5) ubs2segs E6 ss_L4X (mkst (fx:=fy5) regs5 (Z_to_bv 64 PC_L4X) mem5 (seg_rom ubs2segs))).
{ unfold ss_L4X. subst E6. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2f.
split; [unfold sp, sp0, RGBA_FRAME in *; lia|]. split; [unfold sp, sp0, RGBA_FRAME in *; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, C32, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact S32].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, C33, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact S40].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite Z.add_0_r, C34, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact S64].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2f.
change (2 ^ 4) with 16. unfold sp, sp0, RGBA_FRAME in *. repeat split; lia. }
change mem5 with (ms_mem (mkst (fx:=fy5) regs5 (Z_to_bv 64 PC_L4X) mem5 (seg_rom ubs2segs))) in HJ5.
jrun_to LAWS ubs2tbl_ok HS HJ5 PC_DI. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
lazymatch goal with |- SR _ (mkCfg ?msx _) _ => rename msx into msC end.
cbn [ms_mem mkst] in HF, HJ5.
assert (Hmm5 : ms_mem msC = mem5).
{ apply functional_extensionality. intros x0. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => exact (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF x0) end. }
clear HF.
assert (HBq : Permutation (blocks L4 A4) (BASEv ++ [(pnew, fmt * N); (fimg, N)] ++ cht_blks C ++ tree_blocks t ++ [(flt, 4 * (fmt * N))])).
{ eapply Permutation_trans; [exact HB4|]. eapply Permutation_trans; [apply Permutation_cons_append|]. subst keep. rewrite <- !app_assoc. apply Permutation_refl. }
assert (HINV5 : rgba_inv (fx:=fx) API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest L4 A4 mem5 md4).
{ split; [rewrite <- Hmm5; exact HJ5|]. split; [exact Hinit4|]. split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
split; [exact (TR5 HRA)|]. split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |].
intros i Hi. unfold RGBFC_SIZE in *. apply KH5; unfold sp, sp0, RGBA_FRAME, OFF_apal in *; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HH|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
assert (QR : forall regsF, (forall rr : reg, In rr [2; 3; 4; 7; 8; 20; 21; 24; 25]%bv -> getr regsF rr = getr regs5 rr) ->
(getr regsF 2 = Z_to_bv 64 spv /\ getr regsF 3 = getr regs0 3 /\ getr regsF 4 = getr regs0 4) /\
(getr regsF 24 = Z_to_bv 64 flt /\ getr regsF 25 = Z_to_bv 64 N /\ getr regsF 7 = Z_to_bv 64 fmt /\
getr regsF 20 = Z_to_bv 64 (ch_c C) /\ getr regsF 8 = Z_to_bv 64 r /\ getr regsF 21 = Z_to_bv 64 2)).
{ intros regsF HK.
assert (KK : forall rr : reg, In rr [2; 3; 4; 7; 8; 20; 21; 24; 25]%bv -> getr regsF rr = getr (ms_regs msB) rr).
{ intros rr Hrr. rewrite (HK rr Hrr). apply Hk8. cbv [In] in Hrr. repeat (destruct Hrr as [<-|Hrr]; [cbv; tauto|]). destruct Hrr. }
assert (KK4 : forall rr : reg, In rr [2; 3; 4; 8; 20; 21; 25]%bv -> getr regsF rr = getr regs4 rr).
{ intros rr Hrr. rewrite (KK rr ltac:(cbv [In] in Hrr |- *; tauto)). apply Hk7. cbv [In] in Hrr |- *. tauto. }
split.
{ split; [rewrite (KK4 2%bv ltac:(cbv; tauto)); exact W2|]. split; [rewrite (KK4 3%bv ltac:(cbv; tauto)); exact W3|]. rewrite (KK4 4%bv ltac:(cbv; tauto)); exact W4. }
split; [rewrite (KK 24%bv ltac:(cbv; tauto)); exact Q24|]. split; [rewrite (KK4 25%bv ltac:(cbv; tauto)); exact W25|].
split; [rewrite (KK 7%bv ltac:(cbv; tauto)); exact Q7|].
split; [rewrite (KK4 20%bv ltac:(cbv; tauto)); exact W20|]. split; [rewrite (KK4 8%bv ltac:(cbv; tauto)); exact W8|].
rewrite (KK4 21%bv ltac:(cbv; tauto)); exact W21. }
jbranch ubs2tbl HS.
+
rewrite branch_ne_U, (U_and_lit E6 (SOff 32 0) 2), (U_atom E6 32 fattr C32), U_lit in Hc by lia.
assert (Hnd : Z.land fattr 2 <> 0) by (destruct (Z.eqb_spec (Z.land fattr 2) 0); [discriminate Hc | assumption]).
jrun_to LAWS ubs2tbl_ok HS HJ5 PC_ND. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
lazymatch goal with |- SR _ (mkCfg ?msx _) _ => rename msx into msD end.
cbn [ms_mem mkst] in HF, HJ5.
assert (Hmm6 : ms_mem msD = mem5).
{ rewrite <- Hmm5. apply functional_extensionality. intros x0. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => exact (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF x0) end. }
rewrite (st_ok_mkst ubs2segs E6 _ _ HS eq_refl). cbn [ss_pc]. rewrite Hmm6.
pose proof (regs_kept_of_st_ok _ _ _ _ regs5 _ [2; 3; 4; 7; 8; 20; 21; 24; 25]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as Hk9. cbn [ms_regs mkst] in Hk9.
jreg HS (18%bv:reg) as F18. rewrite C34 in F18. cbn [ms_regs mkst] in F18.
destruct (QR (ms_regs msD) Hk9) as [QR1 QR2].
apply (KND fy5 (ms_regs msD) L4 A4 mem5 md4 ha pnew fimg imgl C cnt pal t flt Hfrm5).
split; [exact HINV5|]. split; [exact QR1|]. split; [exact Hfmt|]. split; [exact HN1|]. split; [exact Hha|]. split; [exact Hnd|]. split; [exact QR2|].
split; [exact F18|]. split; [exact Hsl5|]. split; [exact Hsq5|]. split; [exact S80_5|]. split; [exact (TF5 Hfc)|]. split; [exact (TO5 Hobj)|]. split; [exact (TC5 Hcg)|].
split; [exact (TI5 Himg)|]. split; [exact (TH5 Hchq)|]. split; [exact (TT5 Htok)|].
split; [exact Hpnew|]. split; [exact Hfimg|]. split; [exact Hfnz|]. exact HBq.
+
rewrite branch_ne_U, (U_and_lit E6 (SOff 32 0) 2), (U_atom E6 32 fattr C32), U_lit in Hc by lia.
assert (Hdi : Z.land fattr 2 = 0) by (destruct (Z.eqb_spec (Z.land fattr 2) 0); [assumption | discriminate Hc]).
jrun_to LAWS ubs2tbl_ok HS HJ5 PC_DI. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
lazymatch goal with |- SR _ (mkCfg ?msx _) _ => rename msx into msD end.
cbn [ms_mem mkst] in HF, HJ5.
assert (Hmm6 : ms_mem msD = mem5).
{ rewrite <- Hmm5. apply functional_extensionality. intros x0. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => exact (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF x0) end. }
rewrite (st_ok_mkst ubs2segs E6 _ _ HS eq_refl). cbn [ss_pc]. rewrite Hmm6.
pose proof (regs_kept_of_st_ok _ _ _ _ regs5 _ [2; 3; 4; 7; 8; 20; 21; 24; 25]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as Hk9. cbn [ms_regs mkst] in Hk9.
jreg HS (18%bv:reg) as F18. rewrite C33 in F18. cbn [ms_regs mkst] in F18.
destruct (QR (ms_regs msD) Hk9) as [QR1 QR2].
apply (KDI fy5 (ms_regs msD) L4 A4 mem5 md4 ha pnew fimg imgl C cnt pal t flt Hfrm5).
split; [exact HINV5|]. split; [exact QR1|]. split; [exact Hfmt|]. split; [exact HN1|]. split; [exact Hha|]. split; [exact Hdi|]. split; [exact QR2|].
split; [exact F18|]. split; [exact Hsl5|]. split; [exact Hsq5|]. split; [exact S80_5|]. split; [exact (TF5 Hfc)|]. split; [exact (TO5 Hobj)|]. split; [exact (TC5 Hcg)|].
split; [exact (TI5 Himg)|]. split; [exact (TH5 Hchq)|]. split; [exact (TT5 Htok)|].
split; [exact Hpnew|]. split; [exact Hfimg|]. split; [exact Hfnz|]. exact HBq.
Qed.
End e.
Lemma ubs2_rgbadd_QT : seg_QT (fx:=fx) API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest.
Proof. intros KDI KND KXT2 fx1 regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt fdp pal t HFRM HAT. exact (QT_at regs1 Lc Ac memc mdc ha pnew fimg imgl C cnt fdp pal t KDI KND KXT2 HFRM HAT). Qed.
End d.
End c.
