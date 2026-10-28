(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3l YI00 YI02 YI01 YI03
UI1e UI1i YI07 YP14 YI08 YI0c YI0g.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition pixel_val (c : colour) (op : bool) : Z :=
cR c + cG c * 2 ^ 8 + cB c * 2 ^ 16 + (if op then 255 else 0) * 2 ^ 24.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma U_pix_or : forall E eA n32 n33 n34 (c : colour) A,
ew E n32 = Z_to_bv 64 (cR c) -> ew E n33 = Z_to_bv 64 (cG c) -> ew E n34 = Z_to_bv 64 (cB c) -> colour_ok c ->
U E eA = A * 2 ^ 24 -> 0 <= A < 256 ->
U E (SAlu ALU_OR (SAlu ALU_OR eA (SAlu ALU_SLL (SOff n34 0) (SLit 16))) (SAlu ALU_OR (SAlu ALU_SLL (SOff n33 0) (SLit 8)) (SOff n32 0)))
= A * 2 ^ 24 + cB c * 2 ^ 16 + cG c * 2 ^ 8 + cR c.
Proof.
intros E eA n32 n33 n34 c A H32 H33 H34 (Rr & Rg & Rb) HA RA.
rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit, HA.
rewrite (U_atom E n32 (cR c) H32), (U_atom E n33 (cG c) H33), (U_atom E n34 (cB c) H34) by lia.
change (Z.land (zcanon 16) 63) with 16. change (Z.land (zcanon 8) 63) with 8.
rewrite !Z.shiftl_mul_pow2 by lia.
rewrite (zcanon_id (cB c * 2 ^ 16)), (zcanon_id (cG c * 2 ^ 8)) by (unfold M64; lia).
assert (L1 : Z.lor (A * 2 ^ 24) (cB c * 2 ^ 16) = A * 2 ^ 24 + cB c * 2 ^ 16).
{ apply (lor_disjoint_gen _ _ 24); [lia | lia | lia | apply Z.mod_mul; lia]. }
assert (L2 : Z.lor (cG c * 2 ^ 8) (cR c) = cG c * 2 ^ 8 + cR c).
{ apply (lor_disjoint_gen _ _ 8); [lia | lia | lia | apply Z.mod_mul; lia]. }
rewrite L1, L2.
rewrite (zcanon_id (A * 2 ^ 24 + cB c * 2 ^ 16)), (zcanon_id (cG c * 2 ^ 8 + cR c)) by (unfold M64; lia).
assert (L3 : Z.lor (A * 2 ^ 24 + cB c * 2 ^ 16) (cG c * 2 ^ 8 + cR c) = A * 2 ^ 24 + cB c * 2 ^ 16 + (cG c * 2 ^ 8 + cR c)).
{ apply (lor_disjoint_gen _ _ 16); [lia | lia | lia |].
replace (A * 2 ^ 24 + cB c * 2 ^ 16) with ((A * 2 ^ 8 + cB c) * 2 ^ 16) by lia. apply Z.mod_mul; lia. }
rewrite L3. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma U_pix3 : forall E n32 n33 n34 (c : colour),
ew E n32 = Z_to_bv 64 (cR c) -> ew E n33 = Z_to_bv 64 (cG c) -> ew E n34 = Z_to_bv 64 (cB c) -> colour_ok c ->
U E (sv_pix3 n32 n33 n34) = pixel_val c true.
Proof.
intros E n32 n33 n34 c H32 H33 H34 Cok. unfold sv_pix3, pixel_val.
rewrite (U_pix_or E (SLit 4278190080) n32 n33 n34 c 255 H32 H33 H34 Cok); [lia | | lia].
rewrite U_SLit. reflexivity.
Qed.
Lemma U_pix4 : forall E n32 n33 n34 n35 (c : colour) a,
ew E n32 = Z_to_bv 64 (cR c) -> ew E n33 = Z_to_bv 64 (cG c) -> ew E n34 = Z_to_bv 64 (cB c) -> colour_ok c ->
ew E n35 = Z_to_bv 64 a -> 0 <= a < 256 ->
U E (sv_pix4 n32 n33 n34 n35) = pixel_val c (128 <=? a).
Proof.
intros E n32 n33 n34 n35 c a H32 H33 H34 Cok H35 Ra. unfold sv_pix4, pixel_val.
rewrite (U_pix_or E _ n32 n33 n34 c (alpha8 a) H32 H33 H34 Cok (U_alpha_sext8 E n35 a H35 Ra)).
- unfold alpha8. destruct (128 <=? a); lia.
- unfold alpha8. destruct (128 <=? a); lia.
Qed.
Lemma region_kept_ext : forall E (m m' : word -> option byte) r,
(forall x, m' x = m x) -> region_kept ubs2segs E m m' r.
Proof.
intros E m m' r H. split; intros a _.
- unfold mbyte. rewrite H. reflexivity.
- unfold writable_at, wview. rewrite H. exact (fun X => X).
Qed.
Lemma pixel_at_frame : forall (m m' : word -> option byte) rgb fmt c op,
pixel_at ubs2segs m rgb fmt c op -> (forall a, rgb <= a < rgb + fmt -> mbyte ubs2segs m' a = mbyte ubs2segs m a) ->
pixel_at ubs2segs m' rgb fmt c op.
Proof.
intros m m' rgb fmt c op [(C0 & C1 & C2 & Cok) Hf] H.
assert (F3 : 3 <= fmt) by (destruct Hf as [[-> _] | (-> & _)]; lia).
split; [split; [|split; [|split]]|].
- rewrite H by lia. exact C0.
- rewrite H by lia. exact C1.
- rewrite H by lia. exact C2.
- exact Cok.
- destruct Hf as [Hf | (Hf & a & Ca & Ra & Hop)]; [left; exact Hf | right; split; [exact Hf|]].
exists a. split; [rewrite H by lia; exact Ca | split; [exact Ra | exact Hop]].
Qed.
Definition gp_chunks (fmt : Z) : list chunk :=
[mkChunk 0 (CVal 1 (SOff 32%nat 0)); mkChunk 1 (CVal 1 (SOff 33%nat 0)); mkChunk 2 (CVal 1 (SOff 34%nat 0))]
++ (if fmt =? 4 then [mkChunk 3 (CVal 1 (SOff 35%nat 0))] else []).
Definition ss_gp (fmt : Z) : sstate :=
mkSS ubs2_A_getPixelVal (sr_set sr_atoms 11%bv (SLit fmt))
[ YQ0b.mkRegion (Some 10%nat) 0 fmt 0 0 (gp_chunks fmt) ]
None
(mkFacts [ (10%nat, mkAF 4096 (CEIL_MAX - fmt) 0);
(32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0) ] [] []).
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Definition getpix_spec : Prop :=
forall STK sp0 FP L A mem md Lc Ac memc mdc (regs : bvmap 5 word) (rgb fmt : Z) (c : colour) (op : bool),
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> YK0s.ret_ok (getr regs 1) ->
getr regs 10 = Z_to_bv 64 rgb -> getr regs 11 = Z_to_bv 64 fmt ->
pixel_at ubs2segs memc rgb fmt c op -> 4096 <= rgb -> rgb + fmt <= alloc_ceiling ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 ubs2_A_getPixelVal) memc (seg_rom ubs2segs)) mdc)
(fun c' => exists regs2 mem2,
c' = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom ubs2segs)) mdc /\
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem2 mdc /\
regs_preserved regs regs2 /\
getr regs2 10 = Z_to_bv 64 (pixel_val c op) /\
(forall x, mem2 x = memc x)).
Theorem ubs2_getPixelVal : getpix_spec.
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs rgb fmt c op HJ Hra G10 G11 Hpix R0 R1.
pose proof (proj1 alloc_ceiling_val) as Hac.
destruct Hpix as [Hcol Hfmt]. pose proof Hcol as (C0 & C1 & C2 & Cok). pose proof Cok as (Rr & Rg & Rb).
assert (Hfa : exists a, ((fmt = 3 /\ a = 0) \/ (fmt = 4 /\ mbyte ubs2segs memc (rgb + 3) = Some (Z_to_bv 8 a) /\ 0 <= a < 256))
/\ (fmt = 3 -> op = true) /\ (fmt = 4 -> op = (128 <=? a))).
{ destruct Hfmt as [[-> ->] | (-> & a & Hb & Ra & ->)].
- exists 0. split; [left; split; reflexivity|]. split; [reflexivity | intros X; discriminate X].
- exists a. split; [right; split; [reflexivity | split; assumption]|]. split; [intros X; discriminate X | reflexivity]. }
destruct Hfa as (a & Hfa & Hop3 & Hop4).
assert (Ra : 0 <= a < 256) by (destruct Hfa as [[_ ->] | (_ & _ & Ra)]; lia).
assert (Rf : fmt = 3 \/ fmt = 4) by (destruct Hfa as [[-> _] | (-> & _)]; [left | right]; reflexivity).
set (E := Ereg regs (map (Z_to_bv 64) [cR c; cG c; cB c; a] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall jj v, nth_error [cR c; cG c; cB c; a] jj = Some v -> ew E (32 + jj) = Z_to_bv 64 v) by (intros jj v Hjj; subst E; apply Ereg_vals; exact Hjj).
assert (HE32 : ew E 32 = Z_to_bv 64 (cR c)) by exact (HV 0%nat _ eq_refl).
assert (HE33 : ew E 33 = Z_to_bv 64 (cG c)) by exact (HV 1%nat _ eq_refl).
assert (HE34 : ew E 34 = Z_to_bv 64 (cB c)) by exact (HV 2%nat _ eq_refl).
assert (HE35 : ew E 35 = Z_to_bv 64 a) by exact (HV 3%nat _ eq_refl).
assert (HU10 : bv_unsigned (ew E 10) = rgb) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HS : st_ok ubs2segs E (ss_gp fmt) (mkst regs (Z_to_bv 64 ubs2_A_getPixelVal) memc (seg_rom ubs2segs))).
{ unfold ss_gp. subst E. apply entry_st_ok_gen.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | rewrite G11; reflexivity].
- destruct Rf as [-> | ->]; vm_compute; reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU10.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
assert (BY : forall q v n, mbyte ubs2segs memc (rgb + q) = Some (Z_to_bv 8 v) -> 0 <= v < 256 -> 0 <= q < fmt ->
ew (Ereg regs (map (Z_to_bv 64) [cR c; cG c; cB c; a] ++ [])) n = Z_to_bv 64 v ->
chunk_ok ubs2segs (Ereg regs (map (Z_to_bv 64) [cR c; cG c; cB c; a] ++ [])) memc rgb (mkChunk q (CVal 1 (SOff n 0)))).
{ intros q v n Hb Rv Hq Hn.
eapply (chunk_ok_val _ _ _ _ _ _ _ v); [cbn [sv_denot]; rewrite Z.add_0_r, Hn, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op]. apply val_mem_byte; [exact Hb | lia]. }
unfold gp_chunks. apply Forall_app. split.
+ repeat apply Forall_cons; try apply Forall_nil.
* apply (BY 0 (cR c)); [rewrite Z.add_0_r; exact C0 | exact Rr | lia | exact HE32].
* apply (BY 1 (cG c)); [exact C1 | exact Rg | lia | exact HE33].
* apply (BY 2 (cB c)); [exact C2 | exact Rb | lia | exact HE34].
+ destruct Hfa as [[-> _] | (-> & Hb3 & _)]; cbn [Z.eqb Pos.eqb]; [apply Forall_nil|].
apply Forall_cons; [|apply Forall_nil]. apply (BY 3 a); [exact Hb3 | exact Ra | lia | exact HE35].
- cbn [pairwise_disjoint all_disjoint]. repeat split; try exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU10, HE32, HE33, HE34, HE35, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; lia. }
change memc with (ms_mem (mkst regs (Z_to_bv 64 ubs2_A_getPixelVal) memc (seg_rom ubs2segs))) in HJ.
assert (EA0 : env_agree 32 (Ereg regs []) E).
{ subst E. split; [intros n Hn; rewrite !ew_Ereg_lt by exact Hn; reflexivity | reflexivity]. }
clearbody E.
destruct Rf as [-> | ->].
- jrun LAWS ubs2tbl_ok HS HJ. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
eapply (SR_ret_at ubs2segs ubs2tbl); [exact ubs2tbl_ok | exact Hh | exact Hl | exact HS | reflexivity | vm_compute; reflexivity |].
assert (R1' : getr (ms_regs ms) 1 = getr regs 1).
{ jreg HS (1%bv:reg) as X. rewrite X. exact (HE 1%nat 1%bv eq_refl). }
exists (ms_regs ms), (ms_mem ms). split; [rewrite R1', Hra; reflexivity|]. split; [exact HJ|]. split; [|split].
+ apply (regs_preserved_of_st_ok ubs2segs E _ ms regs [] HS EA0). vm_compute. reflexivity.
+ eapply (getr_of_U ubs2segs); [exact HS|]. eval_sr_get.
rewrite (Hop3 eq_refl). apply (U_pix3 E 32 33 34 c HE32 HE33 HE34 Cok).
+ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity.
- jrun LAWS ubs2tbl_ok HS HJ. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hl & _).
eapply (SR_ret_at ubs2segs ubs2tbl); [exact ubs2tbl_ok | exact Hh | exact Hl | exact HS | reflexivity | vm_compute; reflexivity |].
assert (R1' : getr (ms_regs ms) 1 = getr regs 1).
{ jreg HS (1%bv:reg) as X. rewrite X. exact (HE 1%nat 1%bv eq_refl). }
exists (ms_regs ms), (ms_mem ms). split; [rewrite R1', Hra; reflexivity|]. split; [exact HJ|]. split; [|split].
+ apply (regs_preserved_of_st_ok ubs2segs E _ ms regs [] HS EA0). vm_compute. reflexivity.
+ eapply (getr_of_U ubs2segs); [exact HS|]. eval_sr_get.
rewrite (Hop4 eq_refl). apply (U_pix4 E 32 33 34 35 c a HE32 HE33 HE34 Cok HE35 Ra).
+ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity.
Qed.
End S.
End b.
