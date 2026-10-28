(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03
UI1e UI1i UI57 YI07 YP14 YP15 YP13 YI08 YI0c YI0g UI3h UI3d
UI4v UI46.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UIZ5.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Ltac kw_hl HF HU KWo KWn spv memc :=
lazymatch type of HF with frame_of _ _ _ ?m' =>
assert (KWn : forall x, 0 <= x < 2 ^ 64 -> ~ (spv + 72 <= x < spv + 80) -> mbyte ubs2segs m' x = mbyte ubs2segs memc x)
by (intros x Hx Hnx; mb_frame_g HF; [apply KWo; assumption | rewrite HU; lia | lia | lia]) end; clear HF KWo.
Ltac wr_hl HU :=
eapply wr_ok_cons_win; [reflexivity | exact HU | cbn [r_wlo r_whi]; intros _; unfold sp, sp0 in *; lia |];
apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_nil.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition pixe (fmtv : Z) : sv := SAlu ALU_ADD (SMd M_MUL (SOff 9%nat 0) (SLit fmtv)) (SOff 33%nat 0).
Definition hsx_p (p : sv) (nT : nat) : sv :=
SMdw M_REMU (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SRL (SAlu ALU_SLL p (SLit 56)) (SLit 40)) (SAlu ALU_AND p (SLit 65280)))
(SAlu ALU_AND (SAluw ALU_SRL p (SLit 16)) (SLit 255))) (SOff nT 0).
Definition sv_hsx (na nT : nat) : sv := hsx_p (SOff na 0) nT.
Lemma U_pixe : forall E fmtv i img, ew E 9 = Z_to_bv 64 i -> ew E 33 = Z_to_bv 64 img -> 0 <= i -> 1 <= fmtv <= 4 -> 0 <= img ->
img + fmtv * i < 2 ^ 64 -> U E (pixe fmtv) = img + fmtv * i.
Proof.
intros E fmtv i img Hi Himg Ri Rf R0 R1. unfold pixe. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E 9 i Hi), (U_atom E 33 img Himg), U_SLit by nia.
rewrite (zcanon_id fmtv) by (unfold M64; lia). rewrite (zcanon_id (i * fmtv)) by (unfold M64; nia).
rewrite zcanon_id by (unfold M64; nia). lia.
Qed.
Lemma U_add2 : forall E a b x y, U E a = x -> U E b = y -> 0 <= x -> 0 <= y -> x + y < 2 ^ 64 -> U E (SAlu ALU_ADD a b) = x + y.
Proof. intros E a b x y Ha Hb Rx Ry Rxy. rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, Hb. apply zcanon_id. unfold M64; lia. Qed.
Lemma U_hsx_p : forall E p nT A (c : colour) T,
colour_ok c -> 0 <= A < 256 -> U E p = cR c + cG c * 2 ^ 8 + cB c * 2 ^ 16 + A * 2 ^ 24 ->
ew E nT = Z_to_bv 64 T -> 0 < T < 2 ^ 30 ->
U E (hsx_p p nT) = hash0 T c.
Proof.
intros E p nT A c T (Rr & Rg & Rb) RA Hp HT RT. unfold hsx_p, hash0.
apply U_remuw_small; [| apply (U_atom E nT T HT); lia | lia | lia].
rewrite !U_SAlu. cbn [zalu_raw]. rewrite U_SAluw. cbn [zalu_raw]. rewrite !U_SLit, Hp.
change (Z.land (zcanon 56) 63) with 56. change (Z.land (zcanon 40) 63) with 40. rewrite (zcanon_id 65280), (zcanon_id 255) by (unfold M64; lia).
set (P := cR c + cG c * 2 ^ 8 + cB c * 2 ^ 16 + A * 2 ^ 24).
assert (HP : 0 <= P < 2 ^ 32) by (subst P; lia).
assert (E1 : Z.shiftr (zcanon (Z.shiftl P 56)) 40 = cR c * 2 ^ 16).
{ unfold zcanon, M64. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
replace (P * 2 ^ 56) with (cR c * 2 ^ 56 + (A * 2 ^ 16 + cB c * 2 ^ 8 + cG c) * 2 ^ 64) by (subst P; lia).
rewrite Z.mod_add, Z.mod_small by lia.
symmetry. apply Z.div_unique with (r := 0); lia. }
assert (E2 : Z.land P 65280 = cG c * 2 ^ 8).
{ change 65280 with (255 * 2 ^ 8). rewrite land_byte_mask by lia. f_equal.
replace (P / 2 ^ 8) with (A * 2 ^ 16 + cB c * 2 ^ 8 + cG c) by (apply Z.div_unique with (r := cR c); subst P; lia).
replace (A * 2 ^ 16 + cB c * 2 ^ 8 + cG c) with (cG c + (A * 2 ^ 8 + cB c) * 256) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
assert (E3 : Z.land (bv_wrap 64 (bv_swrap 32 (Z.shiftr (P mod 2 ^ 32) (Z.land (zcanon 16 mod 2 ^ 32) 31)))) 255 = cB c).
{ rewrite (Z.mod_small P) by lia. change (Z.land (zcanon 16 mod 2 ^ 32) 31) with 16. rewrite Z.shiftr_div_pow2 by lia.
assert (Hq : P / 2 ^ 16 = A * 2 ^ 8 + cB c) by (symmetry; apply Z.div_unique with (r := cG c * 2 ^ 8 + cR c); subst P; lia).
rewrite Hq. rewrite swrap32_id by lia. rewrite wrap64_id by (unfold M64; lia).
change 255 with (255 * 2 ^ 0). rewrite land_byte_mask by lia. rewrite Z.pow_0_r, Z.div_1_r, Z.mul_1_r.
replace (A * 2 ^ 8 + cB c) with (cB c + A * 256) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
rewrite E1, E2. rewrite (zcanon_id (cR c * 2 ^ 16)), (zcanon_id (cG c * 2 ^ 8)) by (unfold M64; lia).
assert (L1 : Z.lor (cR c * 2 ^ 16) (cG c * 2 ^ 8) = cR c * 2 ^ 16 + cG c * 2 ^ 8).
{ apply (lor_disjoint_gen _ _ 16); try lia. rewrite Z.mod_mul. reflexivity. lia. }
rewrite L1. rewrite (zcanon_id (cR c * 2 ^ 16 + cG c * 2 ^ 8)) by (unfold M64; lia).
rewrite E3. rewrite (zcanon_id (cB c)) by (unfold M64; lia).
assert (L2 : Z.lor (cR c * 2 ^ 16 + cG c * 2 ^ 8) (cB c) = cR c * 2 ^ 16 + cG c * 2 ^ 8 + cB c).
{ apply (lor_disjoint_gen _ _ 8); try lia. replace (cR c * 2 ^ 16 + cG c * 2 ^ 8) with ((cR c * 2 ^ 8 + cG c) * 2 ^ 8) by lia.
rewrite Z.mod_mul; lia. }
rewrite L2. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma U_hsx : forall E na nT (c : colour) op T,
ew E na = Z_to_bv 64 (pixel_val c op) -> colour_ok c -> ew E nT = Z_to_bv 64 T -> 0 < T < 2 ^ 30 ->
U E (sv_hsx na nT) = hash0 T c /\ U E (SAlu ALU_SRL (SOff na 0) (SLit 24)) = (if op then 255 else 0).
Proof.
intros E na nT c op T Hn Hc HT RT. pose proof Hc as (Rr & Rg & Rb).
assert (RA : 0 <= (if op then 255 else 0) < 256) by (destruct op; lia).
assert (Hp : U E (SOff na 0) = cR c + cG c * 2 ^ 8 + cB c * 2 ^ 16 + (if op then 255 else 0) * 2 ^ 24).
{ rewrite (U_atom E na (pixel_val c op) Hn) by (unfold pixel_val; destruct op; lia). reflexivity. }
split.
- exact (U_hsx_p E (SOff na 0) nT _ c T Hc RA Hp HT RT).
- apply (U_pix_alpha E (SOff na 0) _ c Hc RA). rewrite Hp. lia.
Qed.
Lemma find_off_home_free : forall H ent c, ht_inv H ent -> usedz H (hash0 (ht_T H) c) = 0 -> find_off H c = Some 0.
Proof.
intros H ent c INV Hz. destruct (find_off_exists H ent INV c) as (js & Ejs).
destruct (find_off_spec H ent INV c js Ejs) as (Hjs & _ & Hbefore).
destruct (Z.eq_dec js 0) as [->|Hne]; [exact Ejs|].
exfalso. specialize (Hbefore 0 ltac:(lia)). rewrite cyc_0 in Hbefore by (apply hash0_range; exact (inv_T_pos H ent INV)).
unfold slot_stop in Hbefore. rewrite Hz in Hbefore. discriminate Hbefore.
Qed.
Lemma cht_ok_kept : forall (memc memX : word -> option byte) C,
cht_ok memc C -> (forall a, in_cht C a -> mbyte ubs2segs memX a = mbyte ubs2segs memc a) -> cht_ok memX C.
Proof.
intros memc memX C (Hobj & (Af & Ah & Au & Ap & Ax) & Hinv & HT & Hch & Rh & Ru & Rt) KEEP.
pose proof Hinv as ((L1 & L2 & L3 & L4 & L5) & _). rewrite HT in L1, L2, L3, L4, L5.
assert (IC : forall k a, match nth_error (cht_blks C) k with Some b => fst b <= a < fst b + snd b | None => False end -> in_cht C a).
{ intros k a Ha. destruct (nth_error (cht_blks C) k) as [b|] eqn:Eb; [|destruct Ha]. exists b. split; [eapply nth_error_In; exact Eb | exact Ha]. }
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ CHT_SIZE); [exact Hobj | reflexivity |].
intros k Hk. apply KEEP. apply (IC 0%nat); cbn -[Z.add Z.mul Z.lt Z.le]; unfold CHT_SIZE in *; lia. }
split. { unfold cht_arrays. split; [|split; [|split; [|split]]].
- eapply arr32_frame; [exact Af|]. intros a Ha. apply KEEP. apply (IC 1%nat); cbn; lia.
- eapply arr8_frame; [exact Ah|]. intros a Ha. apply KEEP. apply (IC 2%nat); cbn; lia.
- eapply arr8_frame; [exact Au|]. intros a Ha. apply KEEP. apply (IC 3%nat); cbn; lia.
- eapply arr8_frame; [exact Ap|]. intros a Ha. apply KEEP. apply (IC 4%nat); cbn; lia.
- eapply arr32_frame; [exact Ax|]. intros a Ha. apply KEEP. apply (IC 5%nat); cbn; lia. }
split; [exact Hinv|]. split; [exact HT|]. split; [exact Hch|]. split; [exact Rh|]. split; [exact Ru | exact Rt].
Qed.
Definition hl_mem (fmtv : Z) : smem :=
[ YQ0b.mkRegion (Some 2%nat) 0 128 72 80
[ mkChunk 32 (CVal 8 (SLit 65280)); mkChunk 64 (CVal 8 (SLit 1)); mkChunk 112 (CVal 8 (SLit fmtv)); mkChunk 120 (CVal 8 (SOff 33%nat 0)) ] ;
YQ0b.mkRegion (Some 20%nat) 0 48 0 0 [mkChunk 8 (CVal 8 (SOff 36%nat 0)); mkChunk 16 (CVal 8 (SOff 37%nat 0)); mkChunk 44 (CVal 4 (SOff 38%nat 0))] ;
YQ0b.mkRegion (Some 34%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 35%nat 0))] ].
Definition hl_atoms : list (nat * afact) :=
[ (2%nat, mkAF CEIL_MIN (2^63) 4); (9%nat, mkAF 0 RGB_NMAX 0); (20%nat, mkAF 4096 (CEIL_MAX - 48) 0);
(32%nat, mkAF 4096 CEIL_MAX 0); (33%nat, mkAF 4096 CEIL_MAX 0); (34%nat, mkAF 4096 CEIL_MAX 0); (35%nat, mkAF 0 1 0);
(36%nat, mkAF 4096 CEIL_MAX 0); (37%nat, mkAF 4096 CEIL_MAX 0); (38%nat, mkAF 521 (2^24) 0) ].
Definition ss_HL (fmtv : Z) : sstate :=
mkSS PC_HL (sr_set sr_atoms 18%bv (SLit fmtv)) (hl_mem fmtv) None
(mkFacts hl_atoms [mkAC BC_GEU (SOff 32%nat 0) (SOff 33%nat 0); mkAC BC_GEU (SOff 34%nat 0) (SOff 37%nat 0)] [(pixe fmtv, SOff 32%nat 0)]).
Section c.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Local Notation RINV := (rgba_inv API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest).
Local Notation HM := (hist_mem regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay rest).
Local Notation POST := (rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Local Notation SP := (sp regs0).
Local Notation BASE0 := (BASE r g N img fmt rest s bef beffmt).
Local Notation AT_HL := (at_HL API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation AT_L := (at_L API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation AT_PX := (at_PX API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation AT_INC := (at_INC API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation HM_UPD := (hist_mem_update API regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay rest).
Local Notation RINV_MEM := (rgba_inv_mem API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest).
Section d.
Variables (i : Z) (Lc : layout) (Ac : astate) (mdc : Model) (pnew fimg : Z) (imgl : list Z) (C : cht).
Hypothesis KINC : forall regs1 memc ha' C', AT_INC regs1 Lc Ac memc mdc i ha' pnew fimg imgl C' ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_INC) memc (seg_rom ubs2segs)) mdc) POST.
Hypothesis KPX : forall regs1 memc ha, AT_PX regs1 Lc Ac memc mdc i ha pnew fimg imgl C 0 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_PX) memc (seg_rom ubs2segs)) mdc) POST.
Hypothesis KL0 : forall regs1 memc ha, AT_L regs1 Lc Ac memc mdc i ha pnew fimg imgl C 0 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_L) memc (seg_rom ubs2segs)) mdc) POST.
Theorem HL_stretch : forall regs1 memc ha, AT_HL regs1 Lc Ac memc mdc i ha pnew fimg imgl C ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_HL) memc (seg_rom ubs2segs)) mdc) POST.
Proof.
intros regs1 memc ha HAT.
destruct HAT as (HINV & HREGS & Hfmt & Hi & Hha & HR & HMEM).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbf & HB0).
destruct HREGS as (G2 & G3 & G4).
destruct HR as (G9 & G18 & G19 & G20 & G8 & G21).
pose proof HMEM as (Hslots & S32 & S40 & S56 & S64 & S80 & S112 & S120 & Hfc & Hobj & Hcg & [Himg Hlen] & Hcht & EhS & EuS & ETS & Hz & Hpn & Hfi & HB).
pose proof Hcht as (Hobjc & (Af & Ah & Au & Ap & Ax) & Hinv & HT & Hch & RhS & RuS & RTS).
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity.
pose proof (ts_chain_ok _ Hch) as (RT1 & RT2 & RT3). unfold MAX_TABLE_SIZE in RT1.
pose proof Hinv as ((L1 & L2 & L3 & L4 & L5) & (C1 & C2 & C3) & (B1 & B2 & B3) & _). rewrite HT in L1, L2, L3, L4, L5, C1.
set (T := ch_T C) in *. set (col := pxc fmt imgl i). set (h0 := hash0 T col).
assert (Rh0 : 0 <= h0 < T) by (subst h0; apply hash0_range; lia).
unfold RGB_NMAX in HNmax.
assert (Himgb : In (img, fmt * N) (blocks Lc Ac)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. left. unfold BASE. right.
apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. unfold img_block, fmt_okb.
destruct Hfmt as [-> | ->]; left; reflexivity. }
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc img (fmt * N) HHc Himgb ltac:(lia)) as (Ri0 & Ri1 & _).
set (pix := img + fmt * i).
assert (PX1 : 0 <= fmt * i) by nia. assert (PX2 : fmt * i + fmt <= fmt * N) by nia. assert (PX3 : fmt * N <= 4 * N) by nia.
assert (PB : forall k, 0 <= k < fmt -> mbyte ubs2segs memc (pix + k) = Some (Z_to_bv 8 (getz imgl (fmt * i + k))) /\ 0 <= getz imgl (fmt * i + k) < 256).
{ intros k Hk. subst pix. rewrite <- Z.add_assoc. apply (arr8_getz ubs2segs memc img imgl); [exact Himg | lia]. }
assert (Hub : In (ch_u C, T) (blocks Lc Ac)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. right. apply in_app_iff. right. unfold cht_blks, cht_blocks. subst T. cbn. auto 10. }
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc (ch_u C) T HHc Hub ltac:(lia)) as (Ru0 & Ru1 & _).
destruct (arr8_getz ubs2segs memc (ch_u C) (ht_used (ch_H C)) h0 Au ltac:(lia)) as [Bu0 Ru0'].
set (used0 := getz (ht_used (ch_H C)) h0) in *.
assert (U01 : used0 = 0 \/ used0 = 1) by (subst used0; exact (B1 h0 ltac:(rewrite HT; lia))).
assert (Hcb : In (ch_c C, CHT_SIZE) (blocks Lc Ac)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. right. apply in_app_iff. right. left. reflexivity. }
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc (ch_c C) CHT_SIZE HHc Hcb ltac:(unfold CHT_SIZE; lia)) as (Rc0 & Rc1 & _).
unfold CHT_SIZE in Rc1.
assert (SEPuc : ch_c C + 48 <= ch_u C \/ ch_u C + T <= ch_c C).
{ pose proof (cht_apart_of_perm API Lc Ac memc mdc (BASE0 ++ [(pnew, fmt * N); (fimg, N)]) C HHc ltac:(rewrite <- app_assoc; exact HB)) as CA.
pose proof (cht_apart_blocks C 0%nat 3%nat (ch_c C, CHT_SIZE) (ch_u C, T) CA ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold CHT_SIZE in X. lia. }
pose proof Hobjc as Hobjc'. cbn [obj_at LAY_Cht] in Hobjc'. unfold field_ok in Hobjc'. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Hobjc'.
destruct Hobjc' as (_ & [Vh _] & [Vu _] & _ & _ & _ & [VT _] & _).
rewrite EhS in Vh. rewrite EuS in Vu. rewrite ETS in VT. fold T in VT.
assert (Hhb : In (ch_h C, 3 * T) (blocks Lc Ac)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. right. apply in_app_iff. right. unfold cht_blks, cht_blocks. subst T. cbn. auto 10. }
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc (ch_h C) (3 * T) HHc Hhb ltac:(lia)) as (Rhh0 & Rhh1 & _).
pose proof (PB 0 ltac:(lia)) as [P0 R0']. rewrite !Z.add_0_r in P0, R0'. pose proof (PB 1 ltac:(lia)) as [P1 R1']. pose proof (PB 2 ltac:(lia)) as [P2 R2'].
assert (Hcol : colour_ok col) by (subst col; unfold pxc, colour_ok, cR, cG, cB, mkcol; cbn [fst snd]; lia).
remember (if fmt =? 4 then 128 <=? getz imgl (fmt * i + 3) else true) as op eqn:Eop.
assert (OPQ : op = true -> opaque_px fmt imgl i).
{ intros Ho H4. unfold pxa. rewrite Ho, H4 in Eop. rewrite H4. cbn [Z.eqb Pos.eqb] in Eop. symmetry in Eop. apply Z.leb_le in Eop. exact Eop. }
assert (OPF : op = false -> fmt = 4).
{ intros Ho. destruct Hfmt as [H3 | H4]; [|exact H4]. exfalso. rewrite Ho, H3 in Eop. cbn [Z.eqb Pos.eqb] in Eop. discriminate Eop. }
assert (Hpix : pixel_at ubs2segs memc pix fmt col op).
{ split. { unfold col3. subst col. unfold pxc, cR, cG, cB, mkcol; cbn [fst snd]. split; [rewrite <- (Z.add_0_r (fmt * i)); exact P0|]. split; [exact P1|]. split; [exact P2|].
unfold colour_ok, cR, cG, cB; cbn [fst snd]; lia. }
destruct Hfmt as [H3 | H4]; [left; split; [exact H3 | rewrite Eop, H3; reflexivity] | right; split; [exact H4 |]].
exists (getz imgl (fmt * i + 3)). destruct (PB 3 ltac:(lia)) as [P3 R3]. split; [exact P3|]. split; [exact R3|]. rewrite Eop, H4. reflexivity. }
set (vals := [pix; img; ch_u C + h0; used0; ch_h C; ch_u C; T]).
set (E := Ereg regs1 (map (Z_to_bv 64) vals ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall jj v, nth_error vals jj = Some v -> ew E (32 + jj) = Z_to_bv 64 v)
by (intros jj v Hjj; subst E; apply Ereg_vals; exact Hjj).
assert (HE32 : ew E 32 = Z_to_bv 64 pix) by exact (HV 0%nat _ eq_refl).
assert (HE33 : ew E 33 = Z_to_bv 64 img) by exact (HV 1%nat _ eq_refl).
assert (HE34 : ew E 34 = Z_to_bv 64 (ch_u C + h0)) by exact (HV 2%nat _ eq_refl).
assert (HE35 : ew E 35 = Z_to_bv 64 used0) by exact (HV 3%nat _ eq_refl).
assert (HE36 : ew E 36 = Z_to_bv 64 (ch_h C)) by exact (HV 4%nat _ eq_refl).
assert (HE37 : ew E 37 = Z_to_bv 64 (ch_u C)) by exact (HV 5%nat _ eq_refl).
assert (HE38 : ew E 38 = Z_to_bv 64 T) by exact (HV 6%nat _ eq_refl).
assert (HU2 : bv_unsigned (ew E 2) = SP) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (HE9 : ew E 9 = Z_to_bv 64 i) by (rewrite (HE 9%nat 9%bv eq_refl); exact G9).
assert (HE19 : ew E 19 = Z_to_bv 64 ha) by (rewrite (HE 19%nat 19%bv eq_refl); exact G19).
assert (HU20 : bv_unsigned (ew E 20) = ch_c C) by (rewrite (HE 20%nat 20%bv eq_refl), G20; apply unsigned_lit_small; lia).
assert (HS : st_ok ubs2segs E (ss_HL fmt) (mkst regs1 (Z_to_bv 64 PC_HL) memc (seg_rom ubs2segs))).
{ unfold ss_HL. subst E. apply entry_st_ok_full.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | rewrite G18; reflexivity].
- unfold hl_mem. vm_compute. reflexivity.
- unfold hl_mem. constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [unfold sp, sp0 in *; lia|]. split; [unfold sp, sp0 in *; lia|].
split; [intros o Ho; apply Hstw; unfold sp, sp0 in *; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
* eapply (chunk_ok_val _ _ _ _ _ _ _ 65280); [reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. apply val_mem_word_mem. exact S32.
* eapply (chunk_ok_val _ _ _ _ _ _ _ 1); [reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. apply val_mem_word_mem. exact S64.
* eapply (chunk_ok_val _ _ _ _ _ _ _ fmt); [reflexivity | cbn; destruct Hfmt as [-> | ->]; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. apply val_mem_word_mem. exact S112.
* eapply (chunk_ok_val _ _ _ _ _ _ _ img); [cbn [sv_denot]; rewrite Z.add_0_r, HE33, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. apply val_mem_word_mem. exact S120.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU20.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
* eapply (chunk_ok_val _ _ _ _ _ _ _ (ch_h C)); [cbn [sv_denot]; rewrite Z.add_0_r, HE36, unsigned_lit_small by lia; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact Vh].
* eapply (chunk_ok_val _ _ _ _ _ _ _ (ch_u C)); [cbn [sv_denot]; rewrite Z.add_0_r, HE37, unsigned_lit_small by lia; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact Vu].
* eapply (chunk_ok_val _ _ _ _ _ _ _ T); [cbn [sv_denot]; rewrite Z.add_0_r, HE38, unsigned_lit_small by lia; reflexivity | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia | exact VT].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE34, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ used0); [cbn [sv_denot]; rewrite Z.add_0_r, HE35, unsigned_lit_small by lia; reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op]. rewrite Z.add_0_r. apply val_mem_byte; [exact Bu0 | lia].
- unfold hl_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU20, HE34, !unsigned_lit_small by lia.
repeat match goal with |- _ /\ _ => split | |- True => exact I end.
+ right. unfold sp, sp0 in *. lia.
+ right. unfold sp, sp0 in *. lia.
+ clear - SEPuc Rh0; destruct SEPuc; [left; lia | right; lia].
- unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [| split].
+ cbn [atoms_ok hl_atoms]. unfold afact_ok. cbn [af_lo af_hi af_al2]. unfold RGB_NMAX.
rewrite HU2, HU20, (ew_Ereg_nat regs1 _ 9 9%bv eq_refl), G9, HE32, HE33, HE34, HE35, HE36, HE37, HE38.
unfold sp, sp0 in *. subst pix.
rewrite !unsigned_lit_small by lia.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
assert (Hsp16 : (spZ regs0 - RGBA_FRAME) mod 16 = 0).
{ unfold RGBA_FRAME. replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
repeat match goal with |- _ /\ _ => split | |- True => exact I end; lia.
+ cbn [conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite !branch_geu_U.
rewrite (U_atom _ 32 pix HE32), (U_atom _ 33 img HE33), (U_atom _ 34 (ch_u C + h0) HE34), (U_atom _ 37 (ch_u C) HE37) by (subst pix; lia).
split; [apply Bool.negb_true_iff, Z.ltb_ge; subst pix; lia|]. split; [apply Bool.negb_true_iff, Z.ltb_ge; lia | exact I].
+ cbn [alias_ok]. split; [|exact I]. apply U_inj.
rewrite (U_pixe _ fmt i img HE9 HE33), (U_atom _ 32 pix HE32) by (subst pix; destruct Hfmt as [-> | ->]; lia). reflexivity. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_HL) memc (seg_rom ubs2segs))) in HJ.
assert (EA0 : env_agree 32 (Ereg regs1 []) E).
{ subst E. split; [intros n Hn; rewrite !ew_Ereg_lt by exact Hn; reflexivity | reflexivity]. }
clearbody E. clear HV.
assert (POSTF : forall E', env_agree 40 E E' -> ew E' 44 = Z_to_bv 64 (pixel_val col op) ->
U E' (sv_hsx 44 38) = h0 /\ U E' (SAlu ALU_SRL (SOff 44 0) (SLit 24)) = (if op then 255 else 0) /\
sv_denot E' (SAlu ALU_ADD (sv_hsx 44 38) (SOff 37 0)) = sv_denot E' (SOff 34 0) /\
sv_denot E' (SAlu ALU_ADD (SOff 37 0) (sv_hsx 44 38)) = sv_denot E' (SOff 34 0) /\
ew E' 35 = Z_to_bv 64 used0 /\ bv_unsigned (ew E' 2) = SP).
{ intros E' EA H44.
assert (E38 : ew E' 38 = Z_to_bv 64 T) by (rewrite (proj1 EA) by lia; exact HE38).
destruct (U_hsx E' 44 38 col op T H44 Hcol E38 ltac:(lia)) as [UH UA]. fold h0 in UH.
assert (U37 : U E' (SOff 37 0) = ch_u C) by (apply U_atom; [rewrite (proj1 EA) by lia; exact HE37 | lia]).
assert (U34 : U E' (SOff 34 0) = ch_u C + h0) by (apply U_atom; [rewrite (proj1 EA) by lia; exact HE34 | lia]).
split; [exact UH|]. split; [exact UA|].
split; [apply U_inj; rewrite (U_add2 E' _ _ _ _ UH U37) by lia; rewrite U34; lia|].
split; [apply U_inj; rewrite (U_add2 E' _ _ _ _ U37 UH) by lia; rewrite U34; lia|].
split; [rewrite (proj1 EA) by lia; exact HE35|].
rewrite (proj1 EA) by lia. exact HU2. }
assert (EXC : forall E' ss ms' rg, env_agree 40 E E' -> env_agree 32 (Ereg regs1 []) E' -> st_ok ubs2segs E' ss ms' ->
journal ubs2_msyms MR RGBA_STK (sp0 regs0) (FPfoot r g bef beffmt s N) L A mem0 md0 Lc Ac (ms_mem ms') mdc ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (SP + 72 <= x < SP + 80) -> mbyte ubs2segs (ms_mem ms') x = mbyte ubs2segs memc x) ->
nth_error (ss_mem ss) 0 = Some rg -> r_base rg = Some 2%nat -> In (mkChunk 72 (CVal 8 (SOff 19 0))) (r_chunks rg) ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ss) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) [2; 3; 4; 20; 9; 8; 21]%bv = true ->
RINV Lc Ac (ms_mem ms') mdc /\ rgba_regs regs0 (ms_regs ms') /\ body_regs r (ms_regs ms') C i /\
slot regs0 (ms_mem ms') SL_72 ha /\ (forall i', zsum (map snd (ch_ent C)) <= i' -> HM Lc Ac (ms_mem ms') pnew fimg imgl C i')).
{ intros E' ss ms' rg EA EAr HS' HJ' KW' Hrg Hb Hin QK.
pose proof (regs_kept_of_st_ok ubs2segs E' ss ms' regs1 [] [2; 3; 4; 20; 9; 8; 21]%bv HS' EAr QK) as GK.
assert (HU2e : bv_unsigned (ew E' 2) = SP) by (rewrite (proj1 EA) by lia; exact HU2).
split. { apply (RINV_MEM Lc Ac memc _ mdc HINV HJ'). intros a Ha Hna. apply KW'; [lia | unfold sp, sp0 in *; lia]. }
split. { split; [rewrite (GK 2%bv ltac:(cbv; auto 20)); exact G2|]. split; [rewrite (GK 3%bv ltac:(cbv; auto 20)); exact G3 | rewrite (GK 4%bv ltac:(cbv; auto 20)); exact G4]. }
split. { unfold body_regs. rewrite (GK 20%bv ltac:(cbv; auto 20)), (GK 9%bv ltac:(cbv; auto 20)), (GK 8%bv ltac:(cbv; auto 20)), (GK 21%bv ltac:(cbv; auto 20)).
repeat split; assumption. }
split. { unfold slot. apply val_mem_word_mem.
refine (st_chunk_val_g E' ss ms' 0%nat rg 2%nat 72 8%N (SOff 19 0) SP ha HS' Hrg Hb Hin HU2e _ _ _).
- rewrite denot_lit_U. f_equal. apply (U_atom E' 19 ha); [rewrite (proj1 EA) by lia; exact HE19 | destruct Hha as [-> | [-> _]]; lia].
- cbn. destruct Hha as [-> | [-> _]]; lia.
- cbn. lia. }
intros i' Hi'. apply (HM_UPD Lc Ac memc mdc (ms_mem ms') pnew fimg imgl C C i i' HHc); [unfold sp, sp0 in *; lia | unfold sp, sp0 in *; lia | exact Hfmt | exact HMEM | | | reflexivity | reflexivity | exact EhS | exact EuS | exact ETS | exact Hi'].
+ intros a Ha _ Hns. apply KW'; [exact Ha|]. intros Hw. apply Hns. unfold hm_scratch. left. exact Hw.
+ apply (cht_ok_kept memc (ms_mem ms') C Hcht). intros a Hca.
pose proof (cht_low API r g bef beffmt s N img fmt rest Lc Ac memc mdc pnew fimg C a HHc HB Hca) as X.
apply KW'; [lia | unfold sp, sp0 in *; lia]. }
assert (TOINC : forall E' ss ms' rg, env_agree 40 E E' -> env_agree 32 (Ereg regs1 []) E' -> st_ok ubs2segs E' ss ms' ->
ss_resv ss = None -> ss_pc ss = PC_INC ->
journal ubs2_msyms MR RGBA_STK (sp0 regs0) (FPfoot r g bef beffmt s N) L A mem0 md0 Lc Ac (ms_mem ms') mdc ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (SP + 72 <= x < SP + 80) -> mbyte ubs2segs (ms_mem ms') x = mbyte ubs2segs memc x) ->
nth_error (ss_mem ss) 0 = Some rg -> r_base rg = Some 2%nat -> In (mkChunk 72 (CVal 8 (SOff 19 0))) (r_chunks rg) ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ss) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) [2; 3; 4; 20; 9; 8; 21]%bv = true ->
sr_get (ss_regs ss) 18 = SLit 4 -> sr_get (ss_regs ss) 19 = SLit 1 -> fmt = 4 ->
SR ubs2segs (mkCfg ms' mdc) POST).
{ intros E' ss ms' rg EA EAr HS' Hrv Hpc HJ' KW' Hrg Hb Hin QK Q18 Q19 Hf4.
destruct (EXC E' ss ms' rg EA EAr HS' HJ' KW' Hrg Hb Hin QK) as (RI & RR & BR & _ & HMi).
rewrite (st_ok_mkst ubs2segs _ _ _ HS' Hrv), Hpc.
apply (KINC (ms_regs ms') (ms_mem ms') 1 C). unfold at_INC.
split; [exact RI|]. split; [exact RR|]. split; [exact Hfmt|]. split; [exact Hi|]. split; [right; split; [reflexivity | exact Hf4]|].
destruct BR as (B20 & B9 & B8 & B21).
split. { unfold hist_regs.
split; [exact B9|].
split; [eapply (getr_of_U ubs2segs); [exact HS'|]; rewrite Q18, Hf4; apply U_lit; lia|].
split; [eapply (getr_of_U ubs2segs); [exact HS'|]; rewrite Q19; apply U_lit; lia|].
split; [exact B20|]. split; [exact B8 | exact B21]. }
apply HMi. lia. }
assert (TOPX : forall E' ss ms' rg, env_agree 40 E E' -> env_agree 32 (Ereg regs1 []) E' -> st_ok ubs2segs E' ss ms' ->
ss_resv ss = None -> ss_pc ss = PC_PX ->
journal ubs2_msyms MR RGBA_STK (sp0 regs0) (FPfoot r g bef beffmt s N) L A mem0 md0 Lc Ac (ms_mem ms') mdc ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (SP + 72 <= x < SP + 80) -> mbyte ubs2segs (ms_mem ms') x = mbyte ubs2segs memc x) ->
nth_error (ss_mem ss) 0 = Some rg -> r_base rg = Some 2%nat -> In (mkChunk 72 (CVal 8 (SOff 19 0))) (r_chunks rg) ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ss) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) [2; 3; 4; 20; 9; 8; 21]%bv = true ->
sr_get (ss_regs ss) 27 = SAlu ALU_ADD (sv_hsx 44 38) (SLit 0) -> sr_get (ss_regs ss) 23 = SOff 32 0 ->
U E' (sv_hsx 44 38) = h0 -> opaque_px fmt imgl i -> used0 = 0 ->
SR ubs2segs (mkCfg ms' mdc) POST).
{ intros E' ss ms' rg EA EAr HS' Hrv Hpc HJ' KW' Hrg Hb Hin QK Q27 Q23 UH Hop Hu0.
destruct (EXC E' ss ms' rg EA EAr HS' HJ' KW' Hrg Hb Hin QK) as (RI & RR & BR & S72' & HMi).
rewrite (st_ok_mkst ubs2segs _ _ _ HS' Hrv), Hpc.
apply (KPX (ms_regs ms') (ms_mem ms') ha). unfold at_PX.
split; [exact RI|]. split; [exact RR|]. split; [exact Hfmt|]. split; [exact Hi|]. split; [exact Hha|]. split; [exact Hop|].
split. { apply (find_off_home_free (ch_H C) (ch_ent C)); [exact Hinv|]. rewrite HT. exact Hu0. }
change (cyc (ch_T C) (hash0 (ch_T C) (pxc fmt imgl i)) 0) with (cyc T h0 0). rewrite cyc_0 by exact Rh0.
split; [eapply (getr_of_U ubs2segs); [exact HS'|]; rewrite Q27; rewrite (U_add2 E' _ _ h0 0 UH (U_lit E' 0 ltac:(lia))) by lia; lia|].
split; [eapply (getr_of_U ubs2segs); [exact HS'|]; rewrite Q23; apply (U_atom E' 32 pix); [rewrite (proj1 EA) by lia; exact HE32 | subst pix; lia]|].
split; [exact BR|]. split; [exact S72'|]. apply HMi. exact Hz. }
assert (TOL : forall E' ss ms' rg, env_agree 40 E E' -> env_agree 32 (Ereg regs1 []) E' -> st_ok ubs2segs E' ss ms' ->
ss_resv ss = None -> ss_pc ss = PC_L ->
journal ubs2_msyms MR RGBA_STK (sp0 regs0) (FPfoot r g bef beffmt s N) L A mem0 md0 Lc Ac (ms_mem ms') mdc ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (SP + 72 <= x < SP + 80) -> mbyte ubs2segs (ms_mem ms') x = mbyte ubs2segs memc x) ->
nth_error (ss_mem ss) 0 = Some rg -> r_base rg = Some 2%nat -> In (mkChunk 72 (CVal 8 (SOff 19 0))) (r_chunks rg) ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ss) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) [2; 3; 4; 20; 9; 8; 21]%bv = true ->
sr_get (ss_regs ss) 27 = SAlu ALU_ADD (sv_hsx 44 38) (SLit 0) -> sr_get (ss_regs ss) 22 = SLit 0 ->
sr_get (ss_regs ss) 18 = SAlu ALU_XOR (SOff 37 0) (SLit (-1)) -> sr_get (ss_regs ss) 23 = SOff 32 0 ->
sr_get (ss_regs ss) 24 = SOff 36 0 -> sr_get (ss_regs ss) 25 = SOff 37 0 -> sr_get (ss_regs ss) 26 = SOff 38 0 ->
U E' (sv_hsx 44 38) = h0 -> opaque_px fmt imgl i -> used0 <> 0 ->
SR ubs2segs (mkCfg ms' mdc) POST).
{ intros E' ss ms' rg EA EAr HS' Hrv Hpc HJ' KW' Hrg Hb Hin QK Q27 Q22 Q18 Q23 Q24 Q25 Q26 UH Hop Hu0.
destruct (EXC E' ss ms' rg EA EAr HS' HJ' KW' Hrg Hb Hin QK) as (RI & RR & BR & S72' & HMi).
rewrite (st_ok_mkst ubs2segs _ _ _ HS' Hrv), Hpc.
apply (KL0 (ms_regs ms') (ms_mem ms') ha). unfold at_L.
split; [exact RI|]. split; [exact RR|]. split; [exact Hfmt|]. split; [exact Hi|]. split; [exact Hha|]. split; [exact Hop|].
split. { destruct (find_off_exists (ch_H C) (ch_ent C) Hinv col) as [js Ejs]. exists js. split; [exact Ejs|].
pose proof (find_off_ge0 (ch_H C) (ch_ent C) col js Hinv Ejs). lia. }
change (cyc (ch_T C) (hash0 (ch_T C) (pxc fmt imgl i)) 0) with (cyc T h0 0). rewrite cyc_0 by exact Rh0.
split; [exact Hu0|].
split; [eapply (getr_of_U ubs2segs); [exact HS'|]; rewrite Q27; rewrite (U_add2 E' _ _ h0 0 UH (U_lit E' 0 ltac:(lia))) by lia; lia|].
split; [eapply (getr_of_U ubs2segs); [exact HS'|]; rewrite Q22; apply U_lit; lia|].
split; [eapply (getr_of_U ubs2segs); [exact HS'|]; rewrite Q18; apply (U_not E' 37 (ch_u C)); [rewrite (proj1 EA) by lia; exact HE37 | lia]|].
split. { unfold probe_regs.
split; [eapply (getr_of_U ubs2segs); [exact HS'|]; rewrite Q23; apply (U_atom E' 32 pix); [rewrite (proj1 EA) by lia; exact HE32 | subst pix; lia]|].
split; [eapply (getr_of_U ubs2segs); [exact HS'|]; rewrite Q24; apply (U_atom E' 36 (ch_h C)); [rewrite (proj1 EA) by lia; exact HE36 | lia]|].
split; [eapply (getr_of_U ubs2segs); [exact HS'|]; rewrite Q25; apply (U_atom E' 37 (ch_u C)); [rewrite (proj1 EA) by lia; exact HE37 | lia]|].
eapply (getr_of_U ubs2segs); [exact HS'|]; rewrite Q26; apply (U_atom E' 38 T); [rewrite (proj1 EA) by lia; exact HE38 | lia]. }
split; [exact BR|]. split; [exact S72'|]. apply HMi. exact Hz. }
assert (KWm : forall x, 0 <= x < 2 ^ 64 -> ~ (SP + 72 <= x < SP + 80) -> mbyte ubs2segs memc x = mbyte ubs2segs memc x) by (intros; reflexivity).
destruct Hfmt as [Hf | Hf]; rewrite Hf in HS.
-
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_getPixelVal. { wr_hl HU2. }
cbn [ms_mem mkst] in HF.
kw_hl HF HU2 KWm KW0 (sp regs0) memc. clear HG.
jreg HS (1%bv:reg) as Cra. jreg HS (10%bv:reg) as Ca0. jreg HS (11%bv:reg) as Ca1.
rewrite HE32 in Ca0.
assert (Ca1' : getr (ms_regs ms) 11 = Z_to_bv 64 fmt) by (rewrite Ca1, Hf; reflexivity).
assert (HpixC : pixel_at ubs2segs (ms_mem ms) pix fmt col op).
{ apply (pixel_at_frame memc); [exact Hpix | intros a Ha; apply KW0; [lia | unfold sp, sp0 in *; lia]]. }
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst _ (Z_to_bv 64 ?p) _ _) _) _ => change p with ubs2_A_getPixelVal end.
eapply SR_bind.
{ eapply (ubs2_getPixelVal API IMG RGBA_STK (sp0 regs0) (FPfoot r g bef beffmt s N) L A mem0 md0 Lc Ac (ms_mem ms) mdc (ms_regs ms) pix fmt col op HJ);
[ rewrite Cra; apply ret_ok_even; vm_compute; reflexivity | exact Ca0 | exact Ca1' | exact HpixC | lia | lia ]. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & HP2 & Ha02 & Hm2). clear HJ.
rewrite Cra.
jafter_call_keep HS 40%nat regs2 mem2 HP2 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ apply Forall_cons; [apply region_kept_ext; exact Hm2|]. apply Forall_cons; [apply region_kept_ext; exact Hm2|].
apply Forall_cons; [apply region_kept_ext; exact Hm2 | apply Forall_nil]. }
clear HS. rename HS2 into HS. rename HJ2 into HJ.
lazymatch type of HS with st_ok _ _ _ ?mX => change mem2 with (ms_mem mX) in HJ end.
set (E2 := havoc E 40 (map (getr regs2) CLOB)) in *.
assert (HE44 : ew E2 44 = Z_to_bv 64 (pixel_val col op)).
{ rewrite <- Ha02. subst E2. etransitivity; [apply (ew_havoc_new E 40 _ 4%nat (Z_to_bv 64 0)); cbn; lia | reflexivity]. }
assert (EA2 : env_agree 40 E E2) by (subst E2; apply env_agree_havoc_ge; [lia | apply env_agree_refl]).
assert (EAr : env_agree 32 (Ereg regs1 []) E2) by (subst E2; apply env_agree_havoc_ge; [lia | exact EA0]).
clearbody E2.
assert (KW1 : forall x, 0 <= x < 2 ^ 64 -> ~ (SP + 72 <= x < SP + 80) -> mbyte ubs2segs mem2 x = mbyte ubs2segs memc x).
{ intros x Hx Hnx. unfold mbyte. rewrite Hm2. fold (mbyte ubs2segs (ms_mem ms) x). apply KW0; assumption. }
clear KW0.
destruct (POSTF E2 EA2 HE44) as (UH & UA & AL1 & AL2 & E2_35 & HU2').
pose proof (st_ok_add_alias ubs2segs E2 _ _ _ _ (st_ok_add_alias ubs2segs E2 _ _ _ _ HS AL1) AL2) as HS3. clear HS. rename HS3 into HS.
jrun LAWS ubs2tbl_ok HS HJ. { wr_hl HU2'. }
cbn [ms_mem mkst] in HF.
kw_hl HF HU2' KW1 KW2 (sp regs0) memc. clear HG.
jbranch ubs2tbl HS.
+ rewrite branch_eq_U, UA, U_SLit in Hc.
assert (Hopf : op = false) by (destruct op; [vm_compute in Hc; discriminate Hc | reflexivity]).
exfalso. pose proof (OPF Hopf) as X. lia.
+ rewrite branch_eq_U, UA, U_SLit in Hc.
assert (Hopt : op = true) by (destruct op; [reflexivity | vm_compute in Hc; discriminate Hc]).
pose proof (OPQ Hopt) as Hop. clear Hc.
jrun LAWS ubs2tbl_ok HS HJ. { wr_hl HU2'. }
cbn [ms_mem mkst] in HF.
kw_hl HF HU2' KW2 KW3 (sp regs0) memc. clear HG.
jbranch ubs2tbl HS.
* rewrite branch_eq_U, (U_atom E2 35 used0 E2_35), U_lit in Hc by lia. apply Z.eqb_eq in Hc.
jrun_to LAWS ubs2tbl_ok HS HJ PC_PX. { wr_hl HU2'. }
cbn [ms_mem mkst] in HF.
kw_hl HF HU2' KW3 KW4 (sp regs0) memc. clear HG.
eapply (TOPX E2 _ _ _ EA2 EAr HS eq_refl eq_refl HJ KW4);
[reflexivity | reflexivity | left; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact UH | exact Hop | exact Hc].
* rewrite branch_eq_U, (U_atom E2 35 used0 E2_35), U_lit in Hc by lia. apply Z.eqb_neq in Hc.
jrun_to LAWS ubs2tbl_ok HS HJ PC_L. { wr_hl HU2'. }
cbn [ms_mem mkst] in HF.
kw_hl HF HU2' KW3 KW4 (sp regs0) memc. clear HG.
eapply (TOL E2 _ _ _ EA2 EAr HS eq_refl eq_refl HJ KW4);
[reflexivity | reflexivity | left; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact UH | exact Hop | exact Hc].
-
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_getPixelVal. { wr_hl HU2. }
cbn [ms_mem mkst] in HF.
kw_hl HF HU2 KWm KW0 (sp regs0) memc. clear HG.
jreg HS (1%bv:reg) as Cra. jreg HS (10%bv:reg) as Ca0. jreg HS (11%bv:reg) as Ca1.
rewrite HE32 in Ca0.
assert (Ca1' : getr (ms_regs ms) 11 = Z_to_bv 64 fmt) by (rewrite Ca1, Hf; reflexivity).
assert (HpixC : pixel_at ubs2segs (ms_mem ms) pix fmt col op).
{ apply (pixel_at_frame memc); [exact Hpix | intros a Ha; apply KW0; [lia | unfold sp, sp0 in *; lia]]. }
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst _ (Z_to_bv 64 ?p) _ _) _) _ => change p with ubs2_A_getPixelVal end.
eapply SR_bind.
{ eapply (ubs2_getPixelVal API IMG RGBA_STK (sp0 regs0) (FPfoot r g bef beffmt s N) L A mem0 md0 Lc Ac (ms_mem ms) mdc (ms_regs ms) pix fmt col op HJ);
[ rewrite Cra; apply ret_ok_even; vm_compute; reflexivity | exact Ca0 | exact Ca1' | exact HpixC | lia | lia ]. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & HP2 & Ha02 & Hm2). clear HJ.
rewrite Cra.
jafter_call_keep HS 40%nat regs2 mem2 HP2 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ apply Forall_cons; [apply region_kept_ext; exact Hm2|]. apply Forall_cons; [apply region_kept_ext; exact Hm2|].
apply Forall_cons; [apply region_kept_ext; exact Hm2 | apply Forall_nil]. }
clear HS. rename HS2 into HS. rename HJ2 into HJ.
lazymatch type of HS with st_ok _ _ _ ?mX => change mem2 with (ms_mem mX) in HJ end.
set (E2 := havoc E 40 (map (getr regs2) CLOB)) in *.
assert (HE44 : ew E2 44 = Z_to_bv 64 (pixel_val col op)).
{ rewrite <- Ha02. subst E2. etransitivity; [apply (ew_havoc_new E 40 _ 4%nat (Z_to_bv 64 0)); cbn; lia | reflexivity]. }
assert (EA2 : env_agree 40 E E2) by (subst E2; apply env_agree_havoc_ge; [lia | apply env_agree_refl]).
assert (EAr : env_agree 32 (Ereg regs1 []) E2) by (subst E2; apply env_agree_havoc_ge; [lia | exact EA0]).
clearbody E2.
assert (KW1 : forall x, 0 <= x < 2 ^ 64 -> ~ (SP + 72 <= x < SP + 80) -> mbyte ubs2segs mem2 x = mbyte ubs2segs memc x).
{ intros x Hx Hnx. unfold mbyte. rewrite Hm2. fold (mbyte ubs2segs (ms_mem ms) x). apply KW0; assumption. }
clear KW0.
destruct (POSTF E2 EA2 HE44) as (UH & UA & AL1 & AL2 & E2_35 & HU2').
pose proof (st_ok_add_alias ubs2segs E2 _ _ _ _ (st_ok_add_alias ubs2segs E2 _ _ _ _ HS AL1) AL2) as HS3. clear HS. rename HS3 into HS.
jrun LAWS ubs2tbl_ok HS HJ. { wr_hl HU2'. }
cbn [ms_mem mkst] in HF.
kw_hl HF HU2' KW1 KW2 (sp regs0) memc. clear HG.
jbranch ubs2tbl HS.
+ rewrite branch_eq_U, UA, U_SLit in Hc.
assert (Hopf : op = false) by (destruct op; [vm_compute in Hc; discriminate Hc | reflexivity]).
jrun_to LAWS ubs2tbl_ok HS HJ PC_INC. { wr_hl HU2'. }
cbn [ms_mem mkst] in HF.
kw_hl HF HU2' KW2 KW3 (sp regs0) memc. clear HG.
eapply (TOINC E2 _ _ _ EA2 EAr HS eq_refl eq_refl HJ KW3);
[reflexivity | reflexivity | left; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact Hf].
+ rewrite branch_eq_U, UA, U_SLit in Hc.
assert (Hopt : op = true) by (destruct op; [reflexivity | vm_compute in Hc; discriminate Hc]).
pose proof (OPQ Hopt) as Hop. clear Hc.
jrun LAWS ubs2tbl_ok HS HJ. { wr_hl HU2'. }
cbn [ms_mem mkst] in HF.
kw_hl HF HU2' KW2 KW3 (sp regs0) memc. clear HG.
jbranch ubs2tbl HS.
* rewrite branch_eq_U, (U_atom E2 35 used0 E2_35), U_lit in Hc by lia. apply Z.eqb_eq in Hc.
jrun_to LAWS ubs2tbl_ok HS HJ PC_PX. { wr_hl HU2'. }
cbn [ms_mem mkst] in HF.
kw_hl HF HU2' KW3 KW4 (sp regs0) memc. clear HG.
eapply (TOPX E2 _ _ _ EA2 EAr HS eq_refl eq_refl HJ KW4);
[reflexivity | reflexivity | left; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact UH | exact Hop | exact Hc].
* rewrite branch_eq_U, (U_atom E2 35 used0 E2_35), U_lit in Hc by lia. apply Z.eqb_neq in Hc.
jrun_to LAWS ubs2tbl_ok HS HJ PC_L. { wr_hl HU2'. }
cbn [ms_mem mkst] in HF.
kw_hl HF HU2' KW3 KW4 (sp regs0) memc. clear HG.
eapply (TOL E2 _ _ _ EA2 EAr HS eq_refl eq_refl HJ KW4);
[reflexivity | reflexivity | left; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
| vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact UH | exact Hop | exact Hc].
Qed.
End d.
End c.
End b.
