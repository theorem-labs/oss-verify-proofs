(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3a YI06 UI5b YI09 YI08 YI0r
UI1w UI1v UI4l UI21 UI5o UI5l YI6b UI5n
UI20 UI1d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Ltac name_ms HS nm := lazymatch type of HS with st_ok _ _ _ ?m => rename m into nm end.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition AF_CMPRET : Z := Eval vm_compute in (ubs0_A_cgif_addframe + 0x1f4).
Definition AF_LBU : Z := Eval vm_compute in (ubs0_A_cgif_addframe + 0x1e0).
Lemma rdn_ext : forall segs (m1 m2 : word -> option byte) n a,
(forall x, m1 x = m2 x) -> rdn segs m1 a n = rdn segs m2 a n.
Proof using.
intros segs m1 m2 n. induction n as [|n IH]; intros a Heq; [reflexivity|].
cbn [rdn]. rewrite (Heq a), (IH (a + 1)%bv Heq). reflexivity.
Qed.
Lemma mem_grows_of_eq : forall (m1 m2 : word -> option byte), (forall x, m2 x = m1 x) -> mem_grows m1 m2.
Proof using. intros m1 m2 Heq x Hx. rewrite Heq. exact Hx. Qed.
Lemma mbyte_of_eq : forall segs (m1 m2 : word -> option byte) a, (forall x, m2 x = m1 x) -> mbyte segs m2 a = mbyte segs m1 a.
Proof using. intros segs m1 m2 a Heq. unfold mbyte. rewrite Heq. reflexivity. Qed.
Lemma fld_val : forall (m0 m : word -> option byte) a lay vals j off w v, (forall x, m x = m0 x) ->
obj_at ubs0segs m0 a lay vals -> nth_error lay j = Some (off, w) -> nth_error vals j = Some v ->
val_mem ubs0segs m (a + off) (N.to_nat w) v /\ 0 <= v < 2 ^ (8 * Z.of_N w).
Proof using.
intros m0 m a lay vals j off w v Heq Hobj Hl Hv. destruct (obj_at_fields ubs0segs m0 a lay vals Hobj j (off, w) v Hl Hv) as [Hm Hr].
cbn [fst snd] in Hm, Hr. split; [|exact Hr]. intros i Hi. rewrite (mbyte_of_eq _ _ _ _ Heq). apply Hm. exact Hi.
Qed.
Lemma byte_at_eq : forall (m1 m2 : word -> option byte) a, (forall x, m2 x = m1 x) -> byte_at m2 a = byte_at m1 a.
Proof using. intros m1 m2 a Heq. unfold byte_at. rewrite (mbyte_of_eq _ _ _ _ Heq). reflexivity. Qed.
Definition CMP_CLOB : list reg := [5; 6; 10; 11; 12; 13; 14; 15; 16; 17]%bv.
Lemma cmp_clob_out : forall r : reg, reg_in r CMP_CLOB = false ->
r <> 5%bv /\ r <> 6%bv /\ r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv /\ r <> 15%bv /\ r <> 16%bv /\ r <> 17%bv.
Proof using. intros r Hr. repeat split; intros ->; vm_compute in Hr; discriminate. Qed.
Fixpoint cmp_run (CMP : Z -> Z -> Z) (mem0 : word -> option byte) (img fimg : Z) (k : Z) (n : nat) : bool :=
match n with
| O => true
| S n' => (CMP (byte_at mem0 (img + k)) (byte_at mem0 (fimg + k)) =? 0) && cmp_run CMP mem0 img fimg (k + 1) n'
end.
Definition LP_RF : YP09.region := YP09.mkRegion (Some 33%nat) 0 8 0 0 [mkChunk 0 (CVal 8 (SOff 32 0))].
Definition LP_Rc : YP09.region := YP09.mkRegion (Some 9%nat) 8 16 0 0 [mkChunk 8 (CVal 8 (SOff 38 0))].
Definition LP_Rb : YP09.region := YP09.mkRegion (Some 32%nat) 8 16 0 0 [mkChunk 8 (CVal 8 (SOff 39 0))].
Definition LP_Ri : YP09.region := YP09.mkRegion (Some 34%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 36 0))].
Definition LP_Rf : YP09.region := YP09.mkRegion (Some 35%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 37 0))].
Definition LP_Rg : YP09.region :=
YP09.mkRegion (Some 8%nat) 48 96 0 0 [mkChunk 48 (CVal 2 (SOff 40 0)); mkChunk 50 (CVal 2 (SOff 41 0)); mkChunk 92 (CVal 4 (SOff 20 0))].
Definition LP_facts : facts := mkFacts
[ (20%nat, mkAF 1 2 0); (22%nat, mkAF 2 2 0); (32%nat, mkAF 4096 (2 ^ 63) 3); (33%nat, mkAF 4096 (2 ^ 63) 0);
(34%nat, mkAF 4096 (2 ^ 63) 0); (35%nat, mkAF 4096 (2 ^ 63) 0); (36%nat, mkAF 0 255 0); (37%nat, mkAF 0 255 0);
(38%nat, mkAF 4096 (2 ^ 63) 0); (39%nat, mkAF 4096 (2 ^ 63) 0); (40%nat, mkAF 0 65535 0); (41%nat, mkAF 0 65535 0) ]
[ mkAC BC_GEU (SOff 33 0) (SOff 8 0); mkAC BC_GEU (SOff 34 0) (SOff 38 0); mkAC BC_GEU (SOff 35 0) (SOff 39 0) ]
[ (SAlu ALU_ADD (SAlu ALU_SLL (SOff 20 0) (SLit 3)) (SOff 8 0), SOff 33 0); (SAlu ALU_ADD (SOff 38 0) (SOff 18 0), SOff 34 0);
(SAlu ALU_ADD (SOff 39 0) (SOff 18 0), SOff 35 0) ].
Definition ss_loop : sstate := mkSS AF_LOOP sr_atoms [LP_RF; LP_Rc; LP_Rb] None LP_facts.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Section c.
Variables (mem0 : word -> option byte) (g cfp fhp img fimg Wd Ht N ih : Z) (gvals cvals bvals : list Z)
(cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal : Z) (ctcur ctbef : list byte).
Hypothesis Og : obj_at ubs0segs mem0 g LAY_CGIF gvals.
Hypothesis Ongp : nth_error gvals CG_ngp = Some ngp.
Hypothesis Ogpal : nth_error gvals CG_pal = Some gpal.
Hypothesis Oc : obj_at ubs0segs mem0 cfp LAY_FrameConfig cvals.
Hypothesis Ocattr : nth_error cvals FR_attr = Some cattr.
Hypothesis Octidx : nth_error cvals FR_ctidx = Some ctidx.
Hypothesis Ocnlp : nth_error cvals FR_nlp = Some cnlp.
Hypothesis Oclpal : nth_error cvals FR_lpal = Some clpal.
Hypothesis Ob : obj_at ubs0segs mem0 fhp LAY_FrameConfig bvals.
Hypothesis Obattr : nth_error bvals FR_attr = Some battr.
Hypothesis Obtidx : nth_error bvals FR_ctidx = Some btidx.
Hypothesis Obnlp : nth_error bvals FR_nlp = Some bnlp.
Hypothesis Oblpal : nth_error bvals FR_lpal = Some blpal.
Hypothesis G0 : 4096 <= g. Hypothesis G1 : g + CGIF_SIZE <= alloc_ceiling. Hypothesis G16 : g mod 16 = 0.
Hypothesis C0 : 4096 <= cfp. Hypothesis C1 : cfp + 32 <= 2 ^ 63. Hypothesis C8 : cfp mod 8 = 0.
Hypothesis B0 : 4096 <= fhp. Hypothesis B1 : fhp + 32 <= 2 ^ 63. Hypothesis B8 : fhp mod 8 = 0.
Hypothesis Dgc : g + CGIF_SIZE <= cfp \/ cfp + 29 <= g.
Hypothesis Dgb : g + CGIF_SIZE <= fhp \/ fhp + 29 <= g.
Hypothesis Dcb : cfp + 29 <= fhp \/ fhp + 29 <= cfp.
Hypothesis Rct : rdn ubs0segs mem0 (Z_to_bv 64 (ct_sel cattr clpal gpal)) (Z.to_nat (3 * ct_sel cattr cnlp ngp)) = Some ctcur.
Hypothesis Rbt : rdn ubs0segs mem0 (Z_to_bv 64 (ct_sel battr blpal gpal)) (Z.to_nat (3 * ct_sel battr bnlp ngp)) = Some ctbef.
Hypothesis Sc0 : 4096 <= ct_sel cattr clpal gpal. Hypothesis Sc1 : ct_sel cattr clpal gpal + 3 * ct_sel cattr cnlp ngp <= alloc_ceiling.
Hypothesis Sb0 : 4096 <= ct_sel battr blpal gpal. Hypothesis Sb1 : ct_sel battr blpal gpal + 3 * ct_sel battr bnlp ngp <= alloc_ceiling.
Hypothesis Pimg : forall i, 0 <= i < N -> present mem0 (img + i).
Hypothesis Pfimg : forall i, 0 <= i < N -> present mem0 (fimg + i).
Hypothesis Himg0 : 4096 <= img. Hypothesis Himg1 : img + N <= alloc_ceiling.
Hypothesis Hfimg0 : 4096 <= fimg. Hypothesis Hfimg1 : fimg + N <= alloc_ceiling.
Hypothesis HN : N < 2 ^ 32.
Hypothesis Dif : img + N <= fimg \/ fimg + N <= img.
Hypothesis Ofr : nth_error gvals (Z.to_nat ih) = Some fhp.
Hypothesis OW : nth_error gvals CG_w = Some Wd.
Hypothesis OH : nth_error gvals CG_h = Some Ht.
Hypothesis Oih : nth_error gvals CG_ihead = Some ih.
Hypothesis Ocimg : nth_error cvals FR_img = Some img.
Hypothesis Obimg : nth_error bvals FR_img = Some fimg.
Hypothesis HWH : N = Wd * Ht.
Hypothesis Hih : ih = 1 \/ ih = 2.
Definition LOOP_KEPT : list reg := [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition loop_post STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) (k : Z) (n : nat) (c' : config) : Prop :=
exists regs' mem' pc',
c' = mkCfg (mkst regs' (Z_to_bv 64 pc') mem' (seg_rom ubs0segs)) mdc /\ (pc' = AF_C \/ pc' = AF_SAME) /\
pc' = (if cmp_run (cmpPixel_fn cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef) mem0 img fimg k n then AF_SAME else AF_C) /\
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac mem' mdc /\ (forall x, mem' x = mem0 x) /\
(forall r : reg, In r LOOP_KEPT -> getr regs' r = getr regs r).
Lemma af_loop : forall (n : nat) (k : Z) STK sp0 FP L A mem md Lc Ac mdc (regs : bvmap 5 word) memc,
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
(forall x, memc x = mem0 x) ->
0 <= k -> k + Z.of_nat n = N -> (1 <= n)%nat ->
getr regs 8 = Z_to_bv 64 g -> getr regs 9 = Z_to_bv 64 cfp -> getr regs 18 = Z_to_bv 64 k ->
getr regs 20 = Z_to_bv 64 ih -> getr regs 22 = Z_to_bv 64 2 ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 AF_LOOP) memc (seg_rom ubs0segs)) mdc) (loop_post STK sp0 FP L A mem md Lc Ac mdc regs k n).
Proof using B0 B1 B8 C0 C1 C8 Dcb Dgb Dgc Dif G0 G1 G16 HN HWH Hfimg0 Hfimg1 Hih Himg0 Himg1 IMG OH OW Ob Obattr Obimg Oblpal Obnlp Obtidx Oc Ocattr Ocimg Oclpal Ocnlp Octidx Ofr Og Ogpal Oih Ongp Pfimg Pimg Rbt Rct Sb0 Sb1 Sc0 Sc1.
intros n. induction n as [|n IH]; intros k STK sp0 FP L A mem md Lc Ac mdc regs memc HJ Hmem Hk HkN Hn G8 G9 G18 G20 G22; [lia|].
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof alloc_ceiling_lt as Hac47. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
assert (Lih : nth_error LAY_CGIF (Z.to_nat ih) = Some (8 * ih, 8%N)) by (destruct Hih as [-> | ->]; reflexivity).
destruct (fld_val mem0 memc g LAY_CGIF gvals (Z.to_nat ih) (8 * ih) 8%N fhp Hmem Og Lih Ofr) as [VF _].
destruct (fld_val mem0 memc cfp LAY_FrameConfig cvals FR_img 8 8%N img Hmem Oc eq_refl Ocimg) as [VC _].
destruct (fld_val mem0 memc fhp LAY_FrameConfig bvals FR_img 8 8%N fimg Hmem Ob eq_refl Obimg) as [VB _].
destruct (fld_val mem0 mem0 g LAY_CGIF gvals CG_w 48 2%N Wd (fun x => eq_refl) Og eq_refl OW) as [_ RW].
destruct (fld_val mem0 mem0 g LAY_CGIF gvals CG_h 50 2%N Ht (fun x => eq_refl) Og eq_refl OH) as [_ RH].
change (2 ^ (8 * Z.of_N 2)) with 65536 in RW, RH.
set (bc := byte_at mem0 (img + k)). set (bb := byte_at mem0 (fimg + k)).
pose proof (byte_at_range mem0 (img + k)) as Rbc. pose proof (byte_at_range mem0 (fimg + k)) as Rbb. fold bc in Rbc. fold bb in Rbb.
set (E := Ereg regs (map (Z_to_bv 64) [fhp; g + 8 * ih; img + k; fimg + k; bc; bb; img; fimg; Wd; Ht] ++ [])).
assert (HE : forall m (rr : reg), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error [fhp; g + 8 * ih; img + k; fimg + k; bc; bb; img; fimg; Wd; Ht] j = Some v -> ew E (32 + j) = Z_to_bv 64 v)
by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HE8 : ew E 8 = Z_to_bv 64 g) by (rewrite (HE 8%nat 8%bv eq_refl); exact G8).
assert (HE9 : ew E 9 = Z_to_bv 64 cfp) by (rewrite (HE 9%nat 9%bv eq_refl); exact G9).
assert (HE18 : ew E 18 = Z_to_bv 64 k) by (rewrite (HE 18%nat 18%bv eq_refl); exact G18).
assert (HE20 : ew E 20 = Z_to_bv 64 ih) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (HE22 : ew E 22 = Z_to_bv 64 2) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22).
assert (HE32 : ew E 32 = Z_to_bv 64 fhp) by exact (HX 0%nat _ eq_refl).
assert (HE33 : ew E 33 = Z_to_bv 64 (g + 8 * ih)) by exact (HX 1%nat _ eq_refl).
assert (HE34 : ew E 34 = Z_to_bv 64 (img + k)) by exact (HX 2%nat _ eq_refl).
assert (HE35 : ew E 35 = Z_to_bv 64 (fimg + k)) by exact (HX 3%nat _ eq_refl).
assert (HE36 : ew E 36 = Z_to_bv 64 bc) by exact (HX 4%nat _ eq_refl).
assert (HE37 : ew E 37 = Z_to_bv 64 bb) by exact (HX 5%nat _ eq_refl).
assert (HE38 : ew E 38 = Z_to_bv 64 img) by exact (HX 6%nat _ eq_refl).
assert (HE39 : ew E 39 = Z_to_bv 64 fimg) by exact (HX 7%nat _ eq_refl).
assert (HE40 : ew E 40 = Z_to_bv 64 Wd) by exact (HX 8%nat _ eq_refl).
assert (HE41 : ew E 41 = Z_to_bv 64 Ht) by exact (HX 9%nat _ eq_refl).
assert (HU8 : bv_unsigned (ew E 8) = g) by (rewrite HE8; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E 9) = cfp) by (rewrite HE9; apply unsigned_lit_small; lia).
assert (HU20 : bv_unsigned (ew E 20) = ih) by (rewrite HE20; apply unsigned_lit_small; lia).
assert (HU22 : bv_unsigned (ew E 22) = 2) by (rewrite HE22; apply unsigned_lit_small; lia).
assert (HU32 : bv_unsigned (ew E 32) = fhp) by (rewrite HE32; apply unsigned_lit_small; lia).
assert (HU33 : bv_unsigned (ew E 33) = g + 8 * ih) by (rewrite HE33; apply unsigned_lit_small; lia).
assert (HU34 : bv_unsigned (ew E 34) = img + k) by (rewrite HE34; apply unsigned_lit_small; lia).
assert (HU35 : bv_unsigned (ew E 35) = fimg + k) by (rewrite HE35; apply unsigned_lit_small; lia).
assert (HU36 : bv_unsigned (ew E 36) = bc) by (rewrite HE36; apply unsigned_lit_small; lia).
assert (HU37 : bv_unsigned (ew E 37) = bb) by (rewrite HE37; apply unsigned_lit_small; lia).
assert (HU38 : bv_unsigned (ew E 38) = img) by (rewrite HE38; apply unsigned_lit_small; lia).
assert (HU39 : bv_unsigned (ew E 39) = fimg) by (rewrite HE39; apply unsigned_lit_small; lia).
assert (HU40 : bv_unsigned (ew E 40) = Wd) by (rewrite HE40; apply unsigned_lit_small; lia).
assert (HU41 : bv_unsigned (ew E 41) = Ht) by (rewrite HE41; apply unsigned_lit_small; lia).
assert (HS : st_ok ubs0segs E ss_loop (mkst regs (Z_to_bv 64 AF_LOOP) memc (seg_rom ubs0segs))).
{ unfold ss_loop. subst E. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | | | ].
- constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok, LP_RF. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU33.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ fhp); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
rewrite Z.add_0_r. exact VF.
+ unfold region_ok, LP_Rc. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU9.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ img); [cbn [sv_denot]; rewrite Z.add_0_r, HE38, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
exact VC.
+ unfold region_ok, LP_Rb. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU32.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ fimg); [cbn [sv_denot]; rewrite Z.add_0_r, HE39, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
exact VB.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, LP_RF, LP_Rc, LP_Rb. cbn [r_base r_lo r_hi base_val]. rewrite HU33, HU9, HU32.
repeat split; try exact I; clear - Dgc Dgb Dcb Hih HGSv; lia.
- unfold LP_facts. split; [|split].
+ cbn [atoms_ok f_atoms]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU20, HU22, HU32, HU33, HU34, HU35, HU36, HU37, HU38, HU39, HU40, HU41.
change (2 ^ 0) with 1. change (2 ^ 3) with 8. rewrite !Z.mod_1_r. repeat split; lia.
+ cbn [conds_ok f_conds]. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite !branch_geu_U.
rewrite (U_atom _ 33 _ HE33), (U_atom _ 8 _ HE8), (U_atom _ 34 _ HE34), (U_atom _ 38 _ HE38), (U_atom _ 35 _ HE35), (U_atom _ 39 _ HE39) by lia.
repeat split; try exact I; apply Bool.negb_true_iff, Z.ltb_ge; lia.
+ cbn [alias_ok f_alias]. split; [|split; [|split; [|exact I]]]; apply U_inj.
* rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SLit, (U_atom _ 20 _ HE20), (U_atom _ 8 _ HE8), (U_atom _ 33 _ HE33) by lia.
change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
unfold zcanon, M64. rewrite (Z.mod_small (ih * 8)) by lia. rewrite Z.mod_small by lia. lia.
* rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom _ 38 _ HE38), (U_atom _ 18 _ HE18), (U_atom _ 34 _ HE34) by lia.
unfold zcanon, M64. rewrite Z.mod_small by lia. reflexivity.
* rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom _ 39 _ HE39), (U_atom _ 18 _ HE18), (U_atom _ 35 _ HE35) by lia.
unfold zcanon, M64. rewrite Z.mod_small by lia. reflexivity. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 AF_LOOP) memc (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ AF_LBU. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
name_ms HS msA. cbn [ms_mem mkst] in HF.
assert (KA : forall x, ms_mem msA x = mem0 x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply Hmem. }
clear HF.
pose proof (st_ok_submem ubs0segs _ _ _ [] HS ltac:(submem_tac) eq_refl) as HS0. clear HS.
lazymatch type of HS0 with st_ok _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS0 end. rename HS0 into HS.
af_add_region HS LP_Ri.
2:{ unfold region_ok, LP_Ri. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU34.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bc); [cbn [sv_denot]; rewrite Z.add_0_r, HE36, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
rewrite Z.add_0_r. replace bc with (byte_at (ms_mem msA) (img + k)) by (subst bc; apply byte_at_eq; exact KA).
apply byte_at_val. unfold present. rewrite KA. apply (Pimg k). lia. }
2:{ exact I. }
af_add_region HS LP_Rf.
2:{ unfold region_ok, LP_Rf. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU35.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply (chunk_ok_val _ _ _ _ _ _ _ bb); [cbn [sv_denot]; rewrite Z.add_0_r, HE37, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
rewrite Z.add_0_r. replace bb with (byte_at (ms_mem msA) (fimg + k)) by (subst bb; apply byte_at_eq; exact KA).
apply byte_at_val. unfold present. rewrite KA. apply (Pfimg k). lia. }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint, LP_Rf. cbn [r_base r_lo r_hi base_val]. rewrite HU34, HU35.
split; [|exact I]. clear - Dif Hk HkN. lia. }
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_cmpPixel. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
name_ms HS msB. cbn [ms_mem mkst] in HF.
assert (K1 : forall x, ms_mem msB x = mem0 x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply KA. }
clear HF KA.
jreg HS (10%bv:reg) as Ha0. rewrite HE8 in Ha0.
jreg HS (11%bv:reg) as Ha1. rewrite HE9 in Ha1.
jreg HS (12%bv:reg) as Ha2. rewrite HE32 in Ha2.
jreg HS (13%bv:reg) as Ha3. rewrite HE36 in Ha3. jreg HS (14%bv:reg) as Ha4. rewrite HE37 in Ha4.
jreg HS (1%bv:reg) as Hra.
destruct (ubs0_cmpPixel (ms_regs msB) (ms_mem msB) g gvals cfp cvals fhp bvals bc bb ctcur ctbef cattr ctidx cnlp clpal battr btidx bnlp blpal ngp gpal
Ha0 Ha1 Ha2 Ha3 Ha4 Rbc Rbb) as (regs2 & mem2 & Hms & Hmem2 & Hres & Hfr2);
[ eapply obj_at_transport_range; [exact Og | exact (proj1 LAY_CGIF_ok) | intros i Hi; apply mbyte_of_eq; exact K1]
| exact Ongp | exact Ogpal
| eapply obj_at_transport_range; [exact Oc | exact lay_inside_FrameConfig | intros i Hi; apply mbyte_of_eq; exact K1]
| exact Ocattr | exact Octidx | exact Ocnlp | exact Oclpal
| eapply obj_at_transport_range; [exact Ob | exact lay_inside_FrameConfig | intros i Hi; apply mbyte_of_eq; exact K1]
| exact Obattr | exact Obtidx | exact Obnlp | exact Oblpal
| exact G0 | exact G1 | exact G16 | exact C0 | exact C1 | exact C8 | exact B0 | exact B1 | exact B8 | exact Dgc | exact Dgb | exact Dcb
| rewrite (rdn_ext ubs0segs (ms_mem msB) mem0) by exact K1; exact Rct
| rewrite (rdn_ext ubs0segs (ms_mem msB) mem0) by exact K1; exact Rbt
| exact Sc0 | exact Sc1 | exact Sb0 | exact Sb1 | ].
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_msteps; [exact Hh | exact Hl | exact Hms |].
replace (v_jalr (getr (ms_regs msB) 1) 0) with (Z_to_bv 64 AF_CMPRET).
2:{ rewrite Hra. symmetry. apply ret_ok_even. vm_compute. reflexivity. }
assert (HJ2 : journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac mem2 mdc).
{ eapply (journal_exec _ _ LAWS IMG) with (W := fun _ => False); [exact HJ | intros x _; apply Hmem2 | apply mem_grows_of_eq; exact Hmem2 | intros a []]. }
clear HJ.
jafter_stretch_keep HS 42%nat regs2 mem2 CMP_CLOB AF_CMPRET (@nil nat) HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. destruct (cmp_clob_out rr Hrr) as (?&?&?&?&?&?&?&?&?&?). apply Hfr2; assumption. }
{ constructor. }
clear HS. rename HS2 into HS.
assert (K2 : forall x, mem2 x = mem0 x) by (intros x; rewrite Hmem2; apply K1).
af_add_region HS LP_Rg.
2:{ unfold region_ok, LP_Rg. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val ms_mem mkst]. ew_havocA. rewrite HU8.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
destruct (fld_val mem0 mem2 g LAY_CGIF gvals CG_w 48 2%N Wd K2 Og eq_refl OW) as [VW _].
destruct (fld_val mem0 mem2 g LAY_CGIF gvals CG_h 50 2%N Ht K2 Og eq_refl OH) as [VH _].
destruct (fld_val mem0 mem2 g LAY_CGIF gvals CG_ihead 92 4%N ih K2 Og eq_refl Oih) as [VI RI].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
- eapply (chunk_ok_val _ _ _ _ _ _ _ Wd); [cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HE40, unsigned_lit_small by lia; reflexivity | exact RW | cbn; lia | exact VW].
- eapply (chunk_ok_val _ _ _ _ _ _ _ Ht); [cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HE41, unsigned_lit_small by lia; reflexivity | exact RH | cbn; lia | exact VH].
- eapply (chunk_ok_val _ _ _ _ _ _ _ ih); [cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HE20, unsigned_lit_small by lia; reflexivity | exact RI | cbn; lia | exact VI]. }
2:{ exact I. }
jreg HS (10%bv:reg) as Hq44. cbn [ms_regs mkst] in Hq44. rewrite Hres in Hq44. symmetry in Hq44.
assert (RUN : cmp_run (cmpPixel_fn cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef) mem0 img fimg k (Datatypes.S n) = ((cmpPixel_fn cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef) bc bb =? 0) && cmp_run (cmpPixel_fn cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef) mem0 img fimg (k + 1) n)
by reflexivity.
assert (U18 : forall ws, U (havoc E 42 ws) (SOff 18 1) = k + 1) by (intros ws; apply U_atom_off; [ew_havocA; exact HE18 | lia | lia]).
assert (UM : forall ws, U (havoc E 42 ws) (SMd M_MUL (SOff 41 0) (SOff 40 0)) = N).
{ intros ws. unfold U. rewrite (denot_mul_atoms _ 41 40 Ht Wd); [rewrite unsigned_lit_small by nia; nia | ew_havocA; exact HE41 | ew_havocA; exact HE40 | lia | lia | nia]. }
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 AF_CMPRET) mem2 (seg_rom ubs0segs))) in HJ2.
assert (EA : forall k' ws E', env_agree 32 E E' -> (32 <= k')%nat -> env_agree 32 E (havoc E' k' ws)).
{ intros k' ws E' HA Hk'. apply env_agree_havoc_ge; [exact Hk' | exact HA]. }
pose proof (EA 42%nat (map (getr regs2) CMP_CLOB) E (env_agree_refl _ _) ltac:(lia)) as EA1.
assert (EXIT : forall E' ss ms' pc', st_ok ubs0segs E' ss ms' -> env_agree 32 E E' -> ss_pc ss = pc' -> ss_resv ss = None ->
forallb (fun r : reg => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) LOOP_KEPT = true ->
(pc' = AF_C \/ pc' = AF_SAME) ->
pc' = (if cmp_run (cmpPixel_fn cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef) mem0 img fimg k (Datatypes.S n) then AF_SAME else AF_C) ->
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac (ms_mem ms') mdc -> (forall x, ms_mem ms' x = mem0 x) ->
loop_post STK sp0 FP L A mem md Lc Ac mdc regs k (Datatypes.S n) (mkCfg ms' mdc)).
{ intros E' ss ms' pc' HS' HA Hpc Hrv Hkl Hpc' Hpx HJ' K. exists (ms_regs ms'), (ms_mem ms'), pc'.
split; [rewrite (st_ok_mkst ubs0segs _ _ _ HS' Hrv), Hpc; reflexivity|]. split; [exact Hpc'|]. split; [exact Hpx|]. split; [exact HJ'|]. split; [exact K|].
intros rr Hrr. subst E. exact (regs_kept_of_st_ok ubs0segs E' ss ms' regs _ LOOP_KEPT HS' HA Hkl rr Hrr). }
jbranch ubs0tbl HS.
-
assert (NZ : ((cmpPixel_fn cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef) bc bb =? 0) = false).
{ destruct (Z.eqb_spec ((cmpPixel_fn cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef) bc bb) 0) as [E0|NE0]; [exfalso | reflexivity]. revert Hc. cbn [sv_denot]. ew_havocA. rewrite ?Z.add_0_r, Hq44, E0, (unsigned_lit_small 0) by lia.
cbn. rewrite bv_eqb_refl. cbn. intros HH. first [discriminate HH | exact (HH eq_refl)]. }
clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ2 AF_C. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply SR_ret. apply (EXIT _ _ _ AF_C HS EA1 eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(left; reflexivity) ltac:(rewrite RUN, NZ; reflexivity) HJ2).
intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K2.
-
assert (EQ0 : ((cmpPixel_fn cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef) bc bb =? 0) = true).
{ apply Z.eqb_eq. pose proof (memcmp_spec_range (firstn 3 (skipn (Z.to_nat (3 * bb)) ctbef)) (firstn 3 (skipn (Z.to_nat (3 * bc)) ctcur))) as MR0.
assert (Rv : -256 < (cmpPixel_fn cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef) bc bb < 256) by (unfold cmpPixel_fn; destruct (negb (Z.land cattr 4 =? 0) && (bc =? ctidx)); [split; reflexivity|]; destruct (negb (Z.land battr 4 =? 0) && (bb =? btidx)); [split; reflexivity|]; destruct ((ct_sel battr bnlp ngp <=? bb) || (ct_sel cattr cnlp ngp <=? bc)); [split; reflexivity | exact MR0]).
revert Hc. cbn [sv_denot]. ew_havocA. rewrite ?Z.add_0_r, Hq44, Z_to_bv_unsigned. cbn [branch_taken].
destruct (bv_eqb (Z_to_bv 64 (bv_wrap 64 ((cmpPixel_fn cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef) bc bb))) (Z_to_bv 64 0)) eqn:Eb; cbn; intros HH;
[ apply (proj1 (Fs.bv_eqb_eq _ _)) in Eb; apply (f_equal bv_unsigned) in Eb; rewrite !Z_to_bv_unsigned, bv_wrap_idemp, (bv_wrap_small 64 0) in Eb by (split; [apply Z.le_refl | vm_compute; reflexivity]);
unfold bv_wrap in Eb; change (bv_modulus 64) with (2 ^ 64) in Eb;
destruct (Z_lt_le_dec ((cmpPixel_fn cattr ctidx cnlp battr btidx bnlp ngp ctcur ctbef) bc bb) 0) as [l|l]; [| rewrite Z.mod_small in Eb by (clear - Rv l; lia); exact Eb];
exfalso; rewrite <- (Z.mod_add _ 1 (2 ^ 64)), Z.mod_small in Eb by (clear - Rv l; lia); clear - Eb Rv l; lia
| exfalso; first [discriminate HH | exact (HH eq_refl)] ]. }
clear Hc.
jrun LAWS ubs0tbl_ok HS HJ2. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
name_ms HS msC. cbn [ms_mem mkst] in HF.
assert (K3 : forall x, ms_mem msC x = mem0 x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K2. }
clear HF.
jbranch ubs0tbl HS.
+
rewrite branch_ltu_U, U18, UM in Hc.
assert (Hn1 : (1 <= n)%nat) by (apply Z.ltb_lt in Hc; lia). clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ2 AF_LOOP. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
name_ms HS msD. cbn [ms_mem mkst] in HF.
assert (K4 : forall x, ms_mem msD x = mem0 x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K3. }
clear HF.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs0segs Ef ssf msf regs _ LOOP_KEPT HS ltac:(subst E; exact EA1) ltac:(vm_compute; reflexivity)) as HKR end.
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_mono.
{ eapply (IH (k + 1) STK sp0 FP L A mem md Lc Ac mdc _ _ HJ2 K4 ltac:(lia) ltac:(lia) Hn1).
- rewrite (HKR 8%bv ltac:(cbv; auto 20)). exact G8.
- rewrite (HKR 9%bv ltac:(cbv; auto 20)). exact G9.
- reg_nowF HS ltac:(rewrite HE18, unsigned_lit_small by lia; reflexivity).
- rewrite (HKR 20%bv ltac:(cbv; auto 20)). exact G20.
- rewrite (HKR 22%bv ltac:(cbv; auto 20)). exact G22. }
cbv beta. intros c' (regs' & mem' & pc' & -> & Hpc' & Hpx' & HJ' & K' & HK'). exists regs', mem', pc'.
split; [reflexivity|]. split; [exact Hpc'|]. split; [rewrite Hpx', RUN, EQ0; reflexivity|]. split; [exact HJ'|]. split; [exact K'|].
intros rr Hrr. rewrite (HK' rr Hrr). apply (HKR rr Hrr).
+
rewrite branch_ltu_U, U18, UM in Hc.
assert (Hn0 : n = 0%nat) by (apply Z.ltb_ge in Hc; lia). subst n. clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ2 AF_SAME. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
apply SR_ret. apply (EXIT _ _ _ AF_SAME HS EA1 eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(right; reflexivity) ltac:(rewrite RUN, EQ0; reflexivity) HJ2).
intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K3.
Qed.
End c.
End S.
End b.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
