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
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3m YI00 YI02 YI01 YI03 YI04
UI1e UI39 UI1i UI57 UI1h YI0x UI16 UO0e
YI07 YP14 YI08 YI0c YI0g UI3h UI3d UI4v UIZm
UI3x UI3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition E1_MAL1 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0xd4).
Definition E1_CPY : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0xf8).
Definition E1_MAL2 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x110).
Definition E1_BADFMT : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x13c).
Definition E1_NOMEM1 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x144).
Definition E1_NOMEM2 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x14c).
Lemma U_sext32_small : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 -> U E (SExt true 32 (SOff n 0)) = v.
Proof.
intros E n v Hn Hv. rewrite U_SExt, (U_atom E n v Hn) by lia. change (2 ^ Z.of_N 32) with (2 ^ 32).
rewrite Z.mod_small by lia. rewrite swrap32_id by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma fmt_test_false : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
(U E (SLit 1) <? U E (SAluw ALU_ADD (SExt true 32 (SOff n 0)) (SLit (-3)))) = false -> v = 3 \/ v = 4.
Proof.
intros E n v Hn Hv Hc. apply Z.ltb_ge in Hc. rewrite U_lit in Hc by lia.
rewrite U_SAluw in Hc. cbn [zalu_raw] in Hc. rewrite (U_sext32_low E n v Hn Hv), U_SLit in Hc.
change (zcanon (-3) mod 2 ^ 32) with 4294967293 in Hc.
unfold bv_swrap, bv_wrap in Hc.
change (bv_modulus 32) with 4294967296 in Hc. change (bv_half_modulus 32) with 2147483648 in Hc. change (bv_modulus 64) with 18446744073709551616 in Hc.
pose proof (Z.div_mod (v + 4294967293 + 2147483648) 4294967296 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (v + 4294967293 + 2147483648) 4294967296 ltac:(lia)) as B1.
set (r1 := (v + 4294967293 + 2147483648) mod 4294967296) in *.
set (q1 := (v + 4294967293 + 2147483648) / 4294967296) in *.
pose proof (Z.div_mod (r1 - 2147483648) 18446744073709551616 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (r1 - 2147483648) 18446744073709551616 ltac:(lia)) as B2.
set (r2 := (r1 - 2147483648) mod 18446744073709551616) in *.
set (q2 := (r1 - 2147483648) / 18446744073709551616) in *.
clearbody r1 q1 r2 q2. clear Hn. lia.
Qed.
Lemma U_HW : forall E nh nw H W, ew E nh = Z_to_bv 64 H -> ew E nw = Z_to_bv 64 W -> 0 <= H < 2 ^ 16 -> 0 <= W < 2 ^ 16 -> 0 <= H * W < 2 ^ 31 ->
U E (SMdw M_MUL (SOff nh 0) (SOff nw 0)) = H * W.
Proof.
intros E nh nw H W Hh Hw RH RW RHW. apply U_mulw_small; [apply (U_atom E nh H Hh); lia | apply (U_atom E nw W Hw); lia | lia | lia | lia].
Qed.
Lemma U_fN : forall E nf nh nw fmt H W,
ew E nf = Z_to_bv 64 fmt -> ew E nh = Z_to_bv 64 H -> ew E nw = Z_to_bv 64 W ->
0 <= fmt < 2 ^ 31 -> 0 <= H < 2 ^ 16 -> 0 <= W < 2 ^ 16 -> 0 <= H * W < 2 ^ 31 -> fmt * (H * W) < 2 ^ 32 ->
U E (SAlu ALU_SRL (SAlu ALU_SLL (SMd M_MUL (SExt true 32 (SOff nf 0)) (SMdw M_MUL (SOff nh 0) (SOff nw 0))) (SLit 32)) (SLit 32)) = fmt * (H * W).
Proof.
intros E nf nh nw fmt H W Hf Hh Hw Rf RH RW RHW RfN. apply U_zext32_shifts; [| lia].
rewrite U_SMd. cbn [zmd_raw]. rewrite (U_sext32_small E nf fmt Hf Rf), (U_HW E nh nw H W Hh Hw RH RW RHW). apply zcanon_id. unfold M64. lia.
Qed.
Lemma U_fN2 : forall E nf nn fmt N, ew E nf = Z_to_bv 64 fmt -> ew E nn = Z_to_bv 64 N -> 0 <= fmt < 2 ^ 31 -> 0 <= N < 2 ^ 31 -> fmt * N < 2 ^ 32 ->
U E (SAlu ALU_SRL (SAlu ALU_SLL (SMd M_MUL (SOff nf 0) (SOff nn 0)) (SLit 32)) (SLit 32)) = fmt * N.
Proof.
intros E nf nn fmt N Hf Hn Rf RN RfN. apply U_zext32_shifts; [| lia].
rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E nf fmt Hf), (U_atom E nn N Hn) by lia. apply zcanon_id. unfold M64. nia.
Qed.
Lemma U_HW64 : forall E nh nw H W, ew E nh = Z_to_bv 64 H -> ew E nw = Z_to_bv 64 W -> 0 <= H < 2 ^ 16 -> 0 <= W < 2 ^ 16 ->
U E (SMd M_MUL (SOff nh 0) (SOff nw 0)) = H * W.
Proof.
intros E nh nw H W Hh Hw RH RW. rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E nh H Hh), (U_atom E nw W Hw) by lia. apply zcanon_id. unfold M64. nia.
Qed.
Lemma arr8_of_present : forall segs (m : word -> option byte) base n,
(forall i, 0 <= i < Z.of_nat n -> exists b, mbyte segs m (base + i) = Some b) ->
exists l, arr8 segs m base l /\ length l = n.
Proof.
intros segs m base n. induction n as [|n IH]; intros Hp.
- exists []. split; [intros j Hj; cbn in Hj; lia | reflexivity].
- destruct (IH ltac:(intros i Hi; apply Hp; lia)) as (l & Hl & Hlen).
destruct (Hp (Z.of_nat n) ltac:(lia)) as [b Hb].
exists (l ++ [bv_unsigned b]). split; [| rewrite length_app; cbn; lia].
intros j Hj. rewrite length_app in Hj. cbn in Hj.
destruct (Nat.lt_ge_cases j (length l)) as [Hlt|Hge].
+ rewrite app_nth1 by lia. apply Hl. exact Hlt.
+ assert (j = n) by lia. subst j. rewrite app_nth2 by lia. rewrite Hlen, Nat.sub_diag. cbn [nth].
pose proof (bv_unsigned_in_range 8 b) as Hb8. change (bv_modulus 8) with 256 in Hb8.
split; [rewrite Hb, Z_to_bv_bv_unsigned; reflexivity | lia].
Qed.
Ltac set_reg HS r e Hval :=
lazymatch type of HS with st_ok ?segs ?E1 ?ss1 ?ms1 =>
let H2 := fresh "HSq" in
pose proof (st_ok_set_reg segs E1 ss1 ms1 r e HS ltac:(let X := fresh in intros X; discriminate X) Hval) as H2;
let v := eval vm_compute in (mkSS (ss_pc ss1) (sr_set (ss_regs ss1) r e) (ss_mem ss1) (ss_resv ss1) (ss_facts ss1)) in
change (mkSS (ss_pc ss1) (sr_set (ss_regs ss1) r e) (ss_mem ss1) (ss_resv ss1) (ss_facts ss1)) with v in H2;
clear HS; rename H2 into HS
end.
Section f. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition fcfg0_chunks : list YQ0b.chunk :=
[ mkChunk 144 (CVal 4 (SLit 0)); mkChunk 148 (CVal 4 (SLit 0)); mkChunk 152 (CVal 2 (SLit 0));
mkChunk 154 (CVal 2 (SLit 0)); mkChunk 156 (CVal 1 (SLit 0)) ].
Definition ss_E1c : sstate :=
mkSS PC_M1 sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 0 166 0 166 fcfg0_chunks ;
YQ0b.mkRegion (Some 8%nat) 0 RGB_SIZE 0 0 (obj_chunks_from LAY_Rgb 32) ;
YQ0b.mkRegion (Some 26%nat) 0 RGBFC_SIZE 0 0 (obj_chunks_from LAY_RgbFrameConfig 44) ]
None
(mkFacts [ (2%nat, mkAF CEIL_MIN (2^63) 4); (8%nat, mkAF 4096 (CEIL_MAX - RGB_SIZE) 4);
(26%nat, mkAF CEIL_MIN (2^63 - RGBFC_SIZE) 3);
(10%nat, mkAF 1 65535 0); (11%nat, mkAF 1 65535 0); (39%nat, mkAF 1 65535 0); (40%nat, mkAF 1 65535 0);
(45%nat, mkAF 0 (2^32 - 1) 0); (46%nat, mkAF 0 (2^32 - 1) 0); (48%nat, mkAF 0 65535 0);
(49%nat, mkAF 1 RGB_NMAX 0) ] [] []).
Section h.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Lemma ubs2_rgbadd_E1c :
K_A1 API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest ->
K_XS API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt s N img fmt fattr fgen delay rest ->
K_XF API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt s N img fmt fattr fgen delay rest ->
K_M1 API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest.
Proof.
intros KA1 KXS KXF regs1 Lc Ac memc mdc HAT. unfold K_A1, cfg_at in KA1. unfold K_XS, cfg_atF in KXS. unfold K_XF, cfg_atF in KXF.
destruct HAT as (HINV & HREGS & G26 & G8 & G10 & G11 & S144 & S152 & Hobj & Hcg & HB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HHt & HNmax & Hbef & HBent).
destruct HREGS as (G2 & G3 & G4).
pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity.
assert (HSZ : RGB_SIZE = 64) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HRFCv : RGBFC_SIZE = 24) by reflexivity. assert (HNMv : RGB_NMAX = 10000) by reflexivity.
assert (HWH : 1 <= W /\ 1 <= H /\ N = W * H).
{ destruct Hwf as (_ & HW1 & HH1 & HNdef & _). rewrite <- HW, <- HHt. split; [exact HW1 | split; [exact HH1 | exact HNdef]]. }
destruct HWH as (HW1 & HH1 & HNWH).
assert (HN1 : 1 <= N) by (rewrite HNWH; clear - HW1 HH1; nia).
assert (Hrin : In (r, RGB_SIZE) (blocks Lc Ac)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc r RGB_SIZE HHc Hrin ltac:(lia)) as (Rr0 & Rr1 & Rr16).
pose proof (obj_at_range _ _ _ _ _ Hobj) as Rrgb.
pose proof (Rrgb 7%nat W eq_refl) as RW. pose proof (Rrgb 8%nat H eq_refl) as RH. cbn in RW, RH.
pose proof (obj_at_range _ _ _ _ _ Hcfp) as Rcfg.
pose proof (Rcfg 0%nat img eq_refl) as Rimg. pose proof (Rcfg 1%nat fmt eq_refl) as Rfmt. pose proof (Rcfg 2%nat fattr eq_refl) as Rfattr.
pose proof (Rcfg 3%nat fgen eq_refl) as Rfgen. pose proof (Rcfg 4%nat delay eq_refl) as Rdelay. cbn in Rimg, Rfmt, Rfattr, Rfgen, Rdelay.
assert (HfN : 0 <= fmt * N < 2 ^ 32 * RGB_NMAX) by (clear - Rfmt HN1 HNmax HNMv; nia).
set (rgbv := [g; wfn; ctx; path; attr; gen; loops; W; H; bef; beffmt; cur]) in *.
set (cfgv := [img; fmt; fattr; fgen; delay]) in *.
set (E := Ereg regs1 (map (Z_to_bv 64) (rgbv ++ cfgv ++ [N; fmt * N]) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error (rgbv ++ cfgv ++ [N; fmt * N]) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HE39 : ew E 39 = Z_to_bv 64 W) by (apply (HV 7%nat); reflexivity).
assert (HE40 : ew E 40 = Z_to_bv 64 H) by (apply (HV 8%nat); reflexivity).
assert (HE44 : ew E 44 = Z_to_bv 64 img) by (apply (HV 12%nat); reflexivity).
assert (HE45 : ew E 45 = Z_to_bv 64 fmt) by (apply (HV 13%nat); reflexivity).
assert (HE46 : ew E 46 = Z_to_bv 64 fattr) by (apply (HV 14%nat); reflexivity).
assert (HE48 : ew E 48 = Z_to_bv 64 delay) by (apply (HV 16%nat); reflexivity).
assert (HE49 : ew E 49 = Z_to_bv 64 N) by (apply (HV 17%nat); reflexivity).
assert (HE50 : ew E 50 = Z_to_bv 64 (fmt * N)) by (apply (HV 18%nat); reflexivity).
assert (HE10 : ew E 10 = Z_to_bv 64 W) by (rewrite (HE 10%nat 10%bv eq_refl); exact G10).
assert (HE11 : ew E 11 = Z_to_bv 64 H) by (rewrite (HE 11%nat 11%bv eq_refl); exact G11).
pose proof Hal0 as Hal16. unfold UI4v.sp0 in Hal16, Hclo, Hceil, H63, Hstw, HJ.
set (sp0 := spZ regs0) in *. assert (Hsp0 : sp0 = spZ regs0) by reflexivity.
assert (Hspv : sp regs0 = sp0 - 5168) by (unfold sp, UI4v.sp0, RGBA_FRAME; lia).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 5168) by (rewrite (HE 2%nat 2%bv eq_refl), G2, Hspv; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = r) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HU26 : bv_unsigned (ew E 26) = cfp) by (rewrite (HE 26%nat 26%bv eq_refl), G26; apply unsigned_lit_small; lia).
assert (Hsp16 : (sp0 - 5168) mod 16 = 0).
{ replace (sp0 - 5168) with (sp0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal16 | lia]. }
assert (Hz16 : forall i, 0 <= i < 16 -> mbyte ubs2segs memc (sp0 - 5168 + 144 + i) = Some (Z_to_bv 8 0)).
{ intros i Hi. destruct (Z_lt_le_dec i 8) as [H8|H8].
- replace (sp0 - 5168 + 144 + i) with (sp regs0 + 144 + Z.of_nat (Z.to_nat i)) by lia. rewrite (S144 (Z.to_nat i)) by lia.
rewrite le_byte_small by (cbn; lia). rewrite Z.shiftr_0_l. reflexivity.
- replace (sp0 - 5168 + 144 + i) with (sp regs0 + 152 + Z.of_nat (Z.to_nat (i - 8))) by lia. rewrite (S152 (Z.to_nat (i - 8))) by lia.
rewrite le_byte_small by (cbn; lia). rewrite Z.shiftr_0_l. reflexivity. }
assert (HS : st_ok ubs2segs E ss_E1c (mkst regs1 (Z_to_bv 64 PC_M1) memc (seg_rom ubs2segs))).
{ unfold ss_E1c. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hstw; lia|].
unfold fcfg0_chunks.
repeat (apply Forall_cons; [apply chunk_ok_val with (v := 0); [reflexivity | cbn; lia | cbn; lia | intros k Hk; rewrite le_byte_small by (cbn; lia); rewrite Z.shiftr_0_l;
match goal with |- mbyte _ _ (?b + ?o + Z.of_nat k) = _ => replace (b + o + Z.of_nat k) with (sp0 - 5168 + 144 + (o - 144 + Z.of_nat k)) by lia end; apply Hz16; cbn in Hk; lia] |]).
apply Forall_nil.
+ eapply (region_ok_obj ubs2segs _ memc 8 r); [exact HU8 | lia | lia | exact Hobj | reflexivity | | intros i Hi; lia].
intros j v Hj. apply (Ereg_vals regs1 _ [] j v). rewrite nth_error_app1; [exact Hj | apply nth_error_Some; subst rgbv; congruence].
+ eapply (region_ok_obj ubs2segs _ memc 26 cfp); [exact HU26 | lia | lia | exact Hcfp | reflexivity | | intros i Hi; lia].
intros j v Hj. replace (44 + j)%nat with (32 + (length rgbv + j))%nat by (subst rgbv; cbn; lia).
apply (Ereg_vals regs1 _ [] (length rgbv + j)%nat v). rewrite nth_error_app2 by lia. replace (length rgbv + j - length rgbv)%nat with j by lia.
rewrite nth_error_app1; [exact Hj | apply nth_error_Some; subst cfgv; congruence].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU8, HU26. repeat split; lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU8, HU26, HE10, HE11, HE39, HE40, HE45, HE46, HE48, HE49, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_M1) memc (seg_rom ubs2segs))) in HJ.
jrun LAWS ubs2tbl_ok HS HJ.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HG.
assert (KH1 : forall x, alloc_ceiling <= x < 2 ^ 64 -> sp0 - 5168 + 166 <= x -> mbyte ubs2segs (ms_mem ms) x = mbyte ubs2segs memc x).
{ intros x Hx Hlx. mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU8; lia | rewrite HU26; lia]. }
assert (KB1 : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs2segs (ms_mem ms) (b + i) = mbyte ubs2segs memc (b + i)).
{ intros b m i Hbm Hi. destruct (blocks_range _ _ LAWS Lc Ac memc mdc b m HHc Hbm) as [Hb0 Hb1].
mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU8; lia | rewrite HU26; lia]. }
clear HF HG.
assert (TOXS : forall (res : Z) (regsx : bvmap 5 word) (memx : word -> option byte) Lx Ax mdx,
journal ubs2_msyms MR RGBA_STK sp0 (FPfoot r g bef beffmt s N) L A mem0 md0 Lx Ax memx mdx -> st_init_done Ax = true ->
(forall x, alloc_ceiling <= x < 2 ^ 64 -> sp0 - 5168 + 166 <= x -> mbyte ubs2segs memx x = mbyte ubs2segs memc x) ->
(forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs2segs memx (b + i) = mbyte ubs2segs memc (b + i)) ->
Permutation (blocks Lx Ax) (BASE r g N img fmt rest s bef beffmt) ->
getr regsx 2 = Z_to_bv 64 (sp regs0) -> getr regsx 3 = getr regs0 3 -> getr regsx 4 = getr regs0 4 ->
0 <= res < 2 ^ 64 -> getr regsx 21 = Z_to_bv 64 res -> getr regsx 8 = Z_to_bv 64 r ->
SR ubs2segs (mkCfg (mkst regsx (Z_to_bv 64 PC_XS) memx (seg_rom ubs2segs)) mdx)
(rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest)).
{ intros res regsx memx Lx Ax mdx HJx Hinitx KHx KBx HBx X2 X3 X4 Rres X21 X8.
apply (KXS fx regsx Lx Ax memx mdx res s bef beffmt cur Hfrm0). split.
{ split; [exact HJx|]. split; [exact Hinitx|]. split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
split. { eapply (ra_saved_kept regs0 memc memx (sp0 - 104)); [exact HRA | unfold UI4v.sp0; lia | unfold UI4v.sp0; lia | unfold UI4v.sp0; lia | intros x Hx Hlx; apply KHx; lia]. }
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |]. intros i Hi. apply KHx; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HHt|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
split; [split; [exact X2 | split; [exact X3 | exact X4]]|].
split; [exact Rres|]. split; [exact X21|]. split; [exact X8|].
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |]. intros i Hi. apply (KBx r RGB_SIZE i Hrin Hi). }
split. { eapply (cgif_at_kept _ _ g s N (blocks Lc Ac)); [| exact Hcg | exact KBx]. eapply Permutation_trans; [exact HB|]. unfold BASE. apply Permutation_middle. }
split; [exact Hwf|]. split; [exact HW|]. split; [exact HHt|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hbef|]. exact HBx. }
jbranch ubs2tbl HS.
{
jrun_to LAWS ubs2tbl_ok HS HJ PC_XS.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HG |- *.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc]. lazymatch goal with |- SR _ (mkCfg (mkst _ ?pcv _ _) _) _ => change pcv with (Z_to_bv 64 PC_XS) end.
apply (TOXS (2 ^ 64 - 1) _ _ Lc Ac mdc HJ Hinit).
- intros x Hx Hlx. rewrite <- (KH1 x Hx Hlx). mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU8; lia | rewrite HU26; lia].
- intros b m i Hbm Hi. rewrite <- (KB1 b m i Hbm Hi). destruct (blocks_range _ _ LAWS Lc Ac memc mdc b m HHc Hbm) as [Hb0 Hb1].
mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU8; lia | rewrite HU26; lia].
- exact HB.
- jreg HS (2%bv:reg) as Hq. rewrite Hq, (HE 2%nat 2%bv eq_refl). exact G2.
- jreg HS (3%bv:reg) as Hq. rewrite Hq, (HE 3%nat 3%bv eq_refl). exact G3.
- jreg HS (4%bv:reg) as Hq. rewrite Hq, (HE 4%nat 4%bv eq_refl). exact G4.
- lia.
- jreg HS (21%bv:reg) as Hq. rewrite Hq. apply bv_eq. vm_compute. reflexivity.
- jreg HS (8%bv:reg) as Hq. rewrite Hq, (HE 8%nat 8%bv eq_refl). exact G8. }
rewrite branch_ltu_U in Hc. pose proof (fmt_test_false E 45 fmt HE45 Rfmt Hc) as Hfmt. clear Hc.
assert (HfN2 : 3 <= fmt * N <= 4 * RGB_NMAX) by (clear - Hfmt HN1 HNmax HNMv; nia).
assert (Hib : img_block img fmt N = [(img, fmt * N)]) by (unfold img_block, fmt_okb; destruct Hfmt as [-> | ->]; reflexivity).
assert (Himg : In (img, fmt * N) (blocks Lc Ac)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB|]. unfold BASE. rewrite Hib. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity. }
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc img (fmt * N) HHc Himg ltac:(lia)) as (Ri0 & Ri1 & _).
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_malloc.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HG.
assert (KH2 : forall x, alloc_ceiling <= x < 2 ^ 64 -> sp0 - 5168 + 166 <= x -> mbyte ubs2segs (ms_mem ms0) x = mbyte ubs2segs memc x).
{ intros x Hx Hlx. rewrite <- (KH1 x Hx Hlx). mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU8; lia | rewrite HU26; lia]. }
assert (KB2 : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs2segs (ms_mem ms0) (b + i) = mbyte ubs2segs memc (b + i)).
{ intros b m i Hbm Hi. rewrite <- (KB1 b m i Hbm Hi). destruct (blocks_range _ _ LAWS Lc Ac memc mdc b m HHc Hbm) as [Hb0 Hb1].
mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU8; lia | rewrite HU26; lia]. }
clear HF HG KH1 KB1.
assert (Ma0 : getr (ms_regs ms0) 10 = Z_to_bv 64 (fmt * N)).
{ eapply (getr_of_U ubs2segs); [exact HS|]. eval_sr_get. rewrite HNWH, (Z.mul_comm W H).
apply (U_fN E 45 11 10 fmt H W HE45 HE11 HE10); clear - Hfmt RH RW HNWH HN1 HNmax HNMv; nia. }
jreg HS (2%bv:reg) as Mq2. rewrite (HE 2%nat 2%bv eq_refl), G2, Hspv in Mq2.
jreg HS (4%bv:reg) as Mq4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Mq4.
jreg HS (1%bv:reg) as Mq1.
eapply SR_bind.
{ eapply (jmalloc_at _ _ LAWS ubs2_errno_low IMG (aa_malloc API)) with (n := fmt * N) (spc := sp0 - 5168);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hinit | exact Ma0 | lia
| exact Mq2 | lia | exact Hsp16 | lia | lia | exact Mq4 | exact Mq1 | apply ret_ok_even; vm_compute; reflexivity ]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & pnew & -> & HJ2 & Hinit2 & HP2 & Hr10 & Hres & Hkeep2 & Hhi2). clear HJ.
cbn [ms_regs ms_mem mkst] in HP2, Hr10, Hkeep2, Hhi2, HJ2.
pose proof (proj1 HJ2) as HH2.
assert (KH3 : forall x, alloc_ceiling <= x < 2 ^ 64 -> sp0 - 5168 + 166 <= x -> mbyte ubs2segs mem2 x = mbyte ubs2segs memc x).
{ intros x Hx Hlx. rewrite <- (KH2 x Hx Hlx). apply (proj1 (Hhi2 x Hx ltac:(lia))). }
assert (KB3 : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs2segs mem2 (b + i) = mbyte ubs2segs memc (b + i)).
{ intros b m i Hbm Hi. rewrite <- (KB2 b m i Hbm Hi). apply (Hkeep2 b m i Hbm Hi). }
jafter_call_keep HS 51%nat regs2 mem2 HP2 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [exact HU2 | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_block_ro ubs2segs _ _ _ 8); [exact HU8 | exact Hrin | exact Hkeep2 | cbn; lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs2segs _ _ _ 26); [exact HU26 | exact Hhi2 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS KH2 KB2 Mq2 Mq4 Mq1 Ma0. rename HS2 into HS.
(jreg HS (10%bv:reg) as Hatom); cbn [ms_regs mkst] in Hatom; rewrite Hr10 in Hatom; symmetry in Hatom.
destruct Hres as [[-> HBeq] | (Hpnz & Hp16 & (pb1 & pb2 & HBp & HBc) & Wp)].
{
pin_reg' HS (10%bv:reg) 0 Hr10.
jrun_to LAWS ubs2tbl_ok HS HJ2 PC_XS.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HG |- *.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc]. lazymatch goal with |- SR _ (mkCfg (mkst _ ?pcv _ _) _) _ => change pcv with (Z_to_bv 64 PC_XS) end.
apply (TOXS 2 _ _ L2 A2 md2 HJ2 Hinit2).
- intros x Hx Hlx. rewrite <- (KH3 x Hx Hlx). mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU8; lia | rewrite HU26; lia].
- intros b m i Hbm Hi. rewrite <- (KB3 b m i Hbm Hi). destruct (blocks_range _ _ LAWS Lc Ac memc mdc b m HHc Hbm) as [Hb0 Hb1].
mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU8; lia | rewrite HU26; lia].
- rewrite HBeq. exact HB.
- jreg HS (2%bv:reg) as Hq. rewrite Hq, (HE 2%nat 2%bv eq_refl). exact G2.
- jreg HS (3%bv:reg) as Hq. rewrite Hq, (HE 3%nat 3%bv eq_refl). exact G3.
- jreg HS (4%bv:reg) as Hq. rewrite Hq, (HE 4%nat 4%bv eq_refl). exact G4.
- lia.
- jreg HS (21%bv:reg) as Hq. exact Hq.
- jreg HS (8%bv:reg) as Hq. rewrite Hq, (HE 8%nat 8%bv eq_refl). exact G8. }
assert (HBp2 : In (pnew, fmt * N) (blocks L2 A2)) by (rewrite HBp; apply in_app_iff; right; left; reflexivity).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ pnew (fmt * N) HH2 HBp2 ltac:(lia)) as (Rp0 & Rp1 & _).
assert (HB2 : Permutation (blocks L2 A2) ((pnew, fmt * N) :: BASE r g N img fmt rest s bef beffmt)).
{ rewrite HBp. eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|]. apply perm_skip. rewrite <- HBc. exact HB. }
assert (Hsub2 : forall x, In x (blocks Lc Ac) -> In x (blocks L2 A2)) by (intros x Hx; rewrite HBp; rewrite HBc in Hx; apply in_app_iff in Hx; apply in_app_iff; destruct Hx as [Hx|Hx]; [left; exact Hx | right; right; exact Hx]).
add_fact' HS 55%nat (mkAF 4096 (CEIL_MAX - 1) 4); [| rewrite Hatom, unsigned_lit_small by lia; change (2 ^ 4) with 16; lia].
assert (Q27 : getr (ms_regs (mkst regs2 (Z_to_bv 64 E1_MAL1) mem2 (seg_rom ubs2segs))) 27 = Z_to_bv 64 N).
{ eapply (getr_of_U ubs2segs); [exact HS|]. eval_sr_get. rewrite HNWH, (Z.mul_comm W H).
apply (U_HW _ 11 10 H W); [ew_havoc; exact HE11 | ew_havoc; exact HE10 | clear - RH; lia | clear - RW; lia | clear - HNWH HN1 HNmax HNMv; nia]. }
lazymatch type of HS with st_ok _ ?E1 _ _ =>
assert (D49 : sv_denot E1 (SOff 49 0) = Z_to_bv 64 N) by (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; ew_havoc; exact HE49)
end.
set_reg HS (27%bv:reg) (SOff 49 0) (eq_trans Q27 (eq_sym D49)).
clear Q27 D49.
add_fact' HS 45%nat (mkAF 3 4 0); [| ew_havoc; rewrite HE45, unsigned_lit_small by lia; change (2 ^ 0) with 1; rewrite Z.mod_1_r; clear - Hfmt; lia].
jrun_to LAWS ubs2tbl_ok HS HJ2 ubs2_A_memcpy.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HG.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (KH4 : forall x, alloc_ceiling <= x < 2 ^ 64 -> sp0 - 5168 + 166 <= x -> mbyte ubs2segs (ms_mem msx) x = mbyte ubs2segs memc x)
by (intros x Hx Hlx; rewrite <- (KH3 x Hx Hlx); mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU8; lia | rewrite HU26; lia]);
assert (KB4 : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs2segs (ms_mem msx) (b + i) = mbyte ubs2segs memc (b + i))
by (intros b m i Hbm Hi; rewrite <- (KB3 b m i Hbm Hi); destruct (blocks_range _ _ LAWS Lc Ac memc mdc b m HHc Hbm) as [Hb0 Hb1];
mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU8; lia | rewrite HU26; lia])
end.
jreg HS (10%bv:reg) as Ca0. rewrite Hatom in Ca0.
jreg HS (11%bv:reg) as Ca1. rewrite HE44 in Ca1.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Ca2 : getr (ms_regs msx) 12 = Z_to_bv 64 (fmt * N))
by (eapply (getr_of_U ubs2segs); [exact HS|]; eval_sr_get;
apply (U_fN2 _ 45 49 fmt N); [ew_havoc; exact HE45 | ew_havoc; exact HE49 | clear - Hfmt; lia | clear - HN1 HNmax HNMv; lia | clear - Hfmt HN1 HNmax HNMv; nia]) end.
jreg HS (1%bv:reg) as Cra.
eapply SR_bind.
{ eapply (jmemcpy_rd API IMG _ ubs2_memcpy) with (d := pnew) (src := img) (n := fmt * N);
[ exact HS | reflexivity | reflexivity | exact HJ2 | exact Ca0 | exact Ca1 | exact Ca2 | exact Cra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | lia | | | | ].
- intros i Hi. eapply (present_grows _ _ _ HG). apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ pnew (fmt * N) i HH2 HBp2 Hi)).
- intros i Hi. rewrite (KB4 img (fmt * N) i Himg Hi). apply (present_mbyte ubs2_msyms). apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ img (fmt * N) i HHc Himg Hi)).
- pose proof (heap_sep_perm _ _ LAWS L2 A2 mem2 md2 (pnew, fmt * N) _ (img, fmt * N) HH2 HB2
ltac:(unfold BASE; rewrite Hib; right; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; left; reflexivity)) as Hsep.
cbn [fst snd] in Hsep. lia.
- intros a Ha. replace a with (pnew + (a - pnew)) by lia. apply (Wp (blocks L2 A2) (a - pnew) HBp2). lia. }
cbv beta. intros c' (regs3 & mem3 & -> & HJ3 & Hd10 & Hfr3 & Hout3 & Hgr3 & Hcpy3). clear HJ2.
cbn [ms_regs ms_mem mkst] in Hfr3, Hout3, Hgr3, Hcpy3, HJ3.
jafter_stretch_keep HS 67%nat regs3 mem3 MEMCPY_CLOB E1_CPY [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr3. exact Hrr. }
{ pose proof (heap_sep_perm _ _ LAWS L2 A2 mem2 md2 (pnew, fmt * N) _ (r, RGB_SIZE) HH2 HB2 ltac:(left; reflexivity)) as Hsepr. cbn [fst snd] in Hsepr.
constructor; [|constructor; [|constructor; [|constructor]]].
- eapply region_kept_out; [exact Hout3 | exact Hgr3 | cbn [r_base r_lo base_val]; ew_havoc; rewrite HU2; lia | cbn [r_base r_hi base_val]; ew_havoc; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; ew_havoc; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout3 | exact Hgr3 | cbn [r_base r_lo base_val]; ew_havoc; rewrite HU8; lia | cbn [r_base r_hi base_val]; ew_havoc; rewrite HU8; lia | cbn [r_base r_lo r_hi base_val]; ew_havoc; rewrite HU8; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout3 | exact Hgr3 | cbn [r_base r_lo base_val]; ew_havoc; rewrite HU26; lia | cbn [r_base r_hi base_val]; ew_havoc; rewrite HU26; lia | cbn [r_base r_lo r_hi base_val]; ew_havoc; rewrite HU26; intros a Ha; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
assert (KH5 : forall x, alloc_ceiling <= x < 2 ^ 64 -> sp0 - 5168 + 166 <= x -> mbyte ubs2segs mem3 x = mbyte ubs2segs memc x).
{ intros x Hx Hlx. rewrite <- (KH4 x Hx Hlx). unfold mbyte. rewrite (Hout3 (Z_to_bv 64 x)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
assert (KB5 : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs2segs mem3 (b + i) = mbyte ubs2segs memc (b + i)).
{ intros b m i Hbm Hi. rewrite <- (KB4 b m i Hbm Hi).
pose proof (heap_sep_perm _ _ LAWS L2 A2 mem2 md2 (pnew, fmt * N) _ (b, m) HH2 HB2 ltac:(eapply Permutation_in; [exact HB | exact Hbm])) as Hsep. cbn [fst snd] in Hsep.
destruct (blocks_range _ _ LAWS Lc Ac memc mdc b m HHc Hbm) as [Hb0 Hb1].
unfold mbyte. rewrite (Hout3 (Z_to_bv 64 (b + i))) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
clear HF HG KH3 KB3 KH4 KB4 Ca0 Ca1 Ca2 Cra.
jrun_to LAWS ubs2tbl_ok HS HJ3 ubs2_A_malloc.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HG.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (KH6 : forall x, alloc_ceiling <= x < 2 ^ 64 -> sp0 - 5168 + 166 <= x -> mbyte ubs2segs (ms_mem msx) x = mbyte ubs2segs memc x)
by (intros x Hx Hlx; rewrite <- (KH5 x Hx Hlx); mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU8; lia | rewrite HU26; lia]);
assert (KB6 : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs2segs (ms_mem msx) (b + i) = mbyte ubs2segs memc (b + i))
by (intros b m i Hbm Hi; rewrite <- (KB5 b m i Hbm Hi); destruct (blocks_range _ _ LAWS Lc Ac memc mdc b m HHc Hbm) as [Hb0 Hb1];
mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU8; lia | rewrite HU26; lia])
end.
clear HF HG KH5 KB5.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Na0 : getr (ms_regs msx) 10 = Z_to_bv 64 N)
by (eapply (getr_of_U ubs2segs); [exact HS|]; eval_sr_get; rewrite HNWH, (Z.mul_comm W H);
apply (U_HW64 _ 40 39 H W); [ew_havoc; exact HE40 | ew_havoc; exact HE39 | clear - RH; lia | clear - RW; lia]) end.
jreg HS (2%bv:reg) as Nq2. rewrite (HE 2%nat 2%bv eq_refl), G2, Hspv in Nq2.
jreg HS (4%bv:reg) as Nq4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Nq4.
jreg HS (1%bv:reg) as Nq1.
eapply SR_bind.
{ eapply (jmalloc_at _ _ LAWS ubs2_errno_low IMG (aa_malloc API)) with (n := N) (spc := sp0 - 5168);
[ exact HS | reflexivity | reflexivity | exact HJ3 | exact Hinit2 | exact Na0 | lia
| exact Nq2 | lia | exact Hsp16 | lia | lia | exact Nq4 | exact Nq1 | apply ret_ok_even; vm_compute; reflexivity ]. }
cbv beta. intros c' (L3 & A3 & regs4 & mem4 & md4 & fimg & -> & HJ4 & Hinit4 & HP4 & Hf10 & Hres2 & Hkeep4 & Hhi4). clear HJ3.
cbn [ms_regs ms_mem mkst] in HP4, Hf10, Hkeep4, Hhi4, HJ4.
pose proof (proj1 HJ4) as HH4.
assert (KH7 : forall x, alloc_ceiling <= x < 2 ^ 64 -> sp0 - 5168 + 166 <= x -> mbyte ubs2segs mem4 x = mbyte ubs2segs memc x).
{ intros x Hx Hlx. rewrite <- (KH6 x Hx Hlx). apply (proj1 (Hhi4 x Hx ltac:(lia))). }
assert (KB7 : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs2segs mem4 (b + i) = mbyte ubs2segs memc (b + i)).
{ intros b m i Hbm Hi. rewrite <- (KB6 b m i Hbm Hi). apply (Hkeep4 b m i (Hsub2 _ Hbm) Hi). }
jafter_call_keep HS 78%nat regs4 mem4 HP4 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havoc; exact HU2 | exact Hhi4 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_block_ro ubs2segs _ _ _ 8); [ew_havoc; exact HU8 | apply Hsub2; exact Hrin | exact Hkeep4 | cbn; lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs2segs _ _ _ 26); [ew_havoc; exact HU26 | exact Hhi4 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS KH6 KB6 Nq2 Nq4 Nq1 Na0. rename HS2 into HS.
(jreg HS (10%bv:reg) as Hatom2); cbn [ms_regs mkst] in Hatom2; rewrite Hf10 in Hatom2; symmetry in Hatom2.
destruct Hres2 as [[-> HBeq2] | (Hfnz & Hf16 & (fb1 & fb2 & HBf & HBfc) & Wf)].
{
pin_reg' HS (10%bv:reg) 0 Hf10.
jrun_to LAWS ubs2tbl_ok HS HJ4 PC_XF.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HG |- *.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (KH8 : forall x, alloc_ceiling <= x < 2 ^ 64 -> sp0 - 5168 + 166 <= x -> mbyte ubs2segs (ms_mem msx) x = mbyte ubs2segs memc x)
by (intros x Hx Hlx; rewrite <- (KH7 x Hx Hlx); mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU8; lia | rewrite HU26; lia]);
assert (KB8 : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs2segs (ms_mem msx) (b + i) = mbyte ubs2segs memc (b + i))
by (intros b m i Hbm Hi; rewrite <- (KB7 b m i Hbm Hi); destruct (blocks_range _ _ LAWS Lc Ac memc mdc b m HHc Hbm) as [Hb0 Hb1];
mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU8; lia | rewrite HU26; lia])
end.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc]. lazymatch goal with |- SR _ (mkCfg (mkst _ ?pcv _ _) _) _ => change pcv with (Z_to_bv 64 PC_XF) end.
lazymatch goal with |- SR _ (mkCfg (mkst _ _ ?memx _) _) _ =>
apply (KXF fx _ L3 A3 memx md4 2 pnew (fmt * N) s bef beffmt cur Hfrm0) end.
split.
{ split; [exact HJ4|]. split; [exact Hinit4|]. split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
split. { eapply (ra_saved_kept regs0 memc _ (sp0 - 104)); [exact HRA | unfold UI4v.sp0; lia | unfold UI4v.sp0; lia | unfold UI4v.sp0; lia | intros x Hx Hlx; apply KH8; lia]. }
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |]. intros i Hi. apply KH8; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HHt|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
split. { split; [jreg HS (2%bv:reg) as Hq; rewrite Hq, (HE 2%nat 2%bv eq_refl); exact G2|].
split; [jreg HS (3%bv:reg) as Hq; rewrite Hq, (HE 3%nat 3%bv eq_refl); exact G3|].
jreg HS (4%bv:reg) as Hq; rewrite Hq, (HE 4%nat 4%bv eq_refl); exact G4. }
split; [lia|].
split; [jreg HS (9%bv:reg) as Hq; rewrite Hq; exact Hatom|].
split; [jreg HS (21%bv:reg) as Hq; exact Hq|].
split; [jreg HS (8%bv:reg) as Hq; rewrite Hq, (HE 8%nat 8%bv eq_refl); exact G8|].
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |]. intros i Hi. apply (KB8 r RGB_SIZE i Hrin Hi). }
split. { eapply (cgif_at_kept _ _ g s N (blocks Lc Ac)); [| exact Hcg | exact KB8]. eapply Permutation_trans; [exact HB|]. unfold BASE. apply Permutation_middle. }
split; [exact Hwf|]. split; [exact HW|]. split; [exact HHt|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hbef|].
split; [exact Hpnz|].
split. { refine (proj2 (tmp_of_station API L A r g bef beffmt s N img fmt rest L3 A3 mem4 md4 (BASE r g N img fmt rest s bef beffmt) [(pnew, fmt * N)] pnew (fmt * N)
HH4 _ HBent ltac:(intros x1 Hx1; exact Hx1) ltac:(left; reflexivity) ltac:(lia))).
rewrite HBeq2. eapply Permutation_trans; [exact HB2 | apply Permutation_cons_append]. }
rewrite HBeq2. eapply Permutation_trans; [exact HB2 | apply Permutation_cons_append]. }
assert (HBf3 : In (fimg, N) (blocks L3 A3)) by (rewrite HBf; apply in_app_iff; right; left; reflexivity).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ fimg N HH4 HBf3 ltac:(lia)) as (Rf0 & Rf1 & _).
assert (HB3 : Permutation (blocks L3 A3) (BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N); (fimg, N)])).
{ rewrite HBf. eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|].
replace (BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N); (fimg, N)]) with ((BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N)]) ++ [(fimg, N)]) by (rewrite <- app_assoc; reflexivity).
eapply Permutation_trans; [| apply Permutation_cons_append]. apply perm_skip. rewrite <- HBfc.
eapply Permutation_trans; [exact HB2 | apply Permutation_cons_append]. }
add_fact' HS 82%nat (mkAF 4096 (CEIL_MAX - 1) 4); [| rewrite Hatom2, unsigned_lit_small by lia; change (2 ^ 4) with 16; lia].
assert (TOA1 : forall (av : Z) (Ex : env) (cs : list YQ0b.chunk) (regsx : bvmap 5 word) (memx : word -> option byte),
fattr1 fattr = av ->
bv_unsigned (ew Ex 2) = sp0 - 5168 -> ew Ex 44 = Z_to_bv 64 img -> ew Ex 45 = Z_to_bv 64 fmt ->
ew Ex 48 = Z_to_bv 64 delay -> ew Ex 82 = Z_to_bv 64 fimg ->
Forall (chunk_ok ubs2segs Ex memx (sp0 - 5168)) cs ->
In (mkChunk 112 (CVal 8 (SOff 45 0))) cs -> In (mkChunk 120 (CVal 8 (SOff 44 0))) cs ->
In (mkChunk 128 (CVal 8 (SOff 2 166))) cs -> In (mkChunk 136 (CVal 8 (SOff 82 0))) cs ->
In (mkChunk 144 (CVal 4 (SLit av))) cs -> In (mkChunk 148 (CVal 4 (SLit 0))) cs ->
In (mkChunk 152 (CVal 2 (SExt true 16 (SOff 48 0)))) cs -> In (mkChunk 154 (CVal 2 (SLit 0))) cs -> In (mkChunk 156 (CVal 1 (SLit 0))) cs ->
journal ubs2_msyms MR RGBA_STK sp0 (FPfoot r g bef beffmt s N) L A mem0 md0 L3 A3 memx md4 ->
(forall x, alloc_ceiling <= x < 2 ^ 64 -> sp0 - 5168 + 166 <= x -> mbyte ubs2segs memx x = mbyte ubs2segs memc x) ->
(forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs2segs memx (b + i) = mbyte ubs2segs memc (b + i)) ->
getr regsx 2 = Z_to_bv 64 (sp regs0) -> getr regsx 3 = getr regs0 3 -> getr regsx 4 = getr regs0 4 ->
getr regsx 8 = Z_to_bv 64 r -> getr regsx 26 = Z_to_bv 64 cfp -> getr regsx 18 = Z_to_bv 64 pnew -> getr regsx 9 = Z_to_bv 64 fimg ->
getr regsx 21 = Z_to_bv 64 2 -> getr regsx 27 = Z_to_bv 64 N ->
SR ubs2segs (mkCfg (mkst regsx (Z_to_bv 64 PC_A1) memx (seg_rom ubs2segs)) md4)
(rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest)).
{ intros av Ex cs regsx memx Hav X2 X44 X45 X48 X82 HC I112 I120 I128 I136 I144 I148 I152 I154 I156 HJx KHx KBx R2 R3 R4 R8 R26 R18 R9 R21 R27.
assert (Hav' : av = 1 \/ av = 9) by (unfold fattr1 in Hav; destruct (Z.land fattr 1 =? 0); lia).
assert (PRES : forall i, 0 <= i < Z.of_nat (Z.to_nat (fmt * N)) -> exists b, mbyte ubs2segs memx (img + i) = Some b).
{ intros i Hi. rewrite (KBx img (fmt * N) i Himg ltac:(lia)). apply (present_mbyte ubs2_msyms). apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ img (fmt * N) i HHc Himg ltac:(lia))). }
destruct (arr8_of_present ubs2segs memx img (Z.to_nat (fmt * N)) PRES) as (imgl & Himgl & Hlen).
pose proof (fun c Hc => proj1 (Forall_forall _ _) HC c Hc) as CH.
apply (KA1 regsx L3 A3 memx md4 pnew fimg imgl). split.
{ split; [exact HJx|]. split; [exact Hinit4|]. split; [exact Hfrm0|]. split; [exact Hra0|]. split; [exact Hal0|]. split; [exact Htp0|].
split. { eapply (ra_saved_kept regs0 memc memx (sp0 - 104)); [exact HRA | unfold UI4v.sp0; lia | unfold UI4v.sp0; lia | unfold UI4v.sp0; lia | intros x Hx Hlx; apply KHx; lia]. }
split; [exact Hc8|]. split; [exact Hclo|]. split; [exact Hchi|].
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGBFC_SIZE); [exact Hcfp | reflexivity |]. intros i Hi. apply KHx; lia. }
split; [exact Hro|]. split; [exact Hwf|]. split; [exact HW|]. split; [exact HHt|]. split; [exact HNmax|]. split; [exact Hbef | exact HBent]. }
split; [split; [exact R2 | split; [exact R3 | exact R4]]|].
split; [exact Hfmt|]. split; [exact HN1|].
split; [exact R8|]. split; [exact R26|]. split; [exact R18|]. split; [exact R9|]. split; [exact R21|]. split; [exact R27|].
split. { unfold slot, SL_112. rewrite Hspv.
apply (chunk_word_mem ubs2segs Ex memx (sp0 - 5168) 112 (SOff 45 0) fmt (CH _ I112)); [cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact X45 | lia]. }
split. { unfold slot, SL_120. rewrite Hspv.
apply (chunk_word_mem ubs2segs Ex memx (sp0 - 5168) 120 (SOff 44 0) img (CH _ I120)); [cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact X44 | lia]. }
split. { unfold fcfg_at, OFF_fcfg, OFF_apal. rewrite Hav, Hspv. cbn [obj_at LAY_FrameConfig]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N].
split; [split; [| lia]|]. { replace (sp0 - 5168 + 128 + 0) with (sp0 - 5168 + 128) by lia.
eapply (val_of_chunk_ok ubs2segs Ex memx (sp0 - 5168) 128 8%N (SOff 2 166) (sp0 - 5168 + 166)); [exact (CH _ I128) | cbn [sv_denot]; rewrite X2; reflexivity | cbn; lia | cbn; lia]. }
split; [split; [| lia]|]. { replace (sp0 - 5168 + 128 + 8) with (sp0 - 5168 + 136) by lia.
eapply (val_of_chunk_ok ubs2segs Ex memx (sp0 - 5168) 136 8%N (SOff 82 0) fimg); [exact (CH _ I136) | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact X82 | cbn; lia | cbn; lia]. }
split; [split; [| lia]|]. { replace (sp0 - 5168 + 128 + 16) with (sp0 - 5168 + 144) by lia.
eapply (val_of_chunk_ok ubs2segs Ex memx (sp0 - 5168) 144 4%N (SLit av) av); [exact (CH _ I144) | cbn [sv_denot]; reflexivity | cbn; lia | cbn; lia]. }
split; [split; [| lia]|]. { replace (sp0 - 5168 + 128 + 20) with (sp0 - 5168 + 148) by lia.
eapply (val_of_chunk_ok ubs2segs Ex memx (sp0 - 5168) 148 4%N (SLit 0) 0); [exact (CH _ I148) | reflexivity | cbn; lia | cbn; lia]. }
split; [split; [| lia]|]. { replace (sp0 - 5168 + 128 + 24) with (sp0 - 5168 + 152) by lia.
pose proof (val_mem_low_of_chunk ubs2segs Ex memx (sp0 - 5168) 152 2%N (SExt true 16 (SOff 48 0)) (CH _ I152) ltac:(cbn; lia)) as V.
change (bv_unsigned (sv_denot Ex (SExt true 16 (SOff 48 0)))) with (U Ex (SExt true 16 (SOff 48 0))) in V.
change (2 ^ (8 * Z.of_N 2)) with (2 ^ 16) in V. rewrite (U_sext16_low Ex 48 delay X48) in V by lia. exact V. }
split; [split; [| lia]|]. { replace (sp0 - 5168 + 128 + 26) with (sp0 - 5168 + 154) by lia.
eapply (val_of_chunk_ok ubs2segs Ex memx (sp0 - 5168) 154 2%N (SLit 0) 0); [exact (CH _ I154) | reflexivity | cbn; lia | cbn; lia]. }
split; [split; [| lia]|]. { replace (sp0 - 5168 + 128 + 28) with (sp0 - 5168 + 156) by lia.
eapply (val_of_chunk_ok ubs2segs Ex memx (sp0 - 5168) 156 1%N (SLit 0) 0); [exact (CH _ I156) | reflexivity | cbn; lia | cbn; lia]. }
exact I. }
split. { eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |]. intros i Hi. apply (KBx r RGB_SIZE i Hrin Hi). }
split. { eapply (cgif_at_kept _ _ g s N (blocks Lc Ac)); [| exact Hcg | exact KBx]. eapply Permutation_trans; [exact HB|]. unfold BASE. apply Permutation_middle. }
split. { split; [exact Himgl|]. unfold zlen. rewrite Hlen. lia. }
split; [exact Hpnz|]. split; [exact Hfnz|]. exact HB3. }
jrun LAWS ubs2tbl_ok HS HJ4.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF, HG.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (KH8 : forall x, alloc_ceiling <= x < 2 ^ 64 -> sp0 - 5168 + 166 <= x -> mbyte ubs2segs (ms_mem msx) x = mbyte ubs2segs memc x)
by (intros x Hx Hlx; rewrite <- (KH7 x Hx Hlx); mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU8; lia | rewrite HU26; lia]);
assert (KB8 : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs2segs (ms_mem msx) (b + i) = mbyte ubs2segs memc (b + i))
by (intros b m i Hbm Hi; rewrite <- (KB7 b m i Hbm Hi); destruct (blocks_range _ _ LAWS Lc Ac memc mdc b m HHc Hbm) as [Hb0 Hb1];
mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU8; lia | rewrite HU26; lia])
end.
clear HF HG KH7 KB7.
Ltac go_A1 TOA1 HS HJ4 KH8 KB8 HE HU2 HU8 HU26 HE44 HE45 HE48 Hatom Hatom2 G2 G3 G4 G8 G26 HE10 HE11 HE49 HE50 LAWS Lc Ac memc mdc HHc av Hav :=
cbn [ms_mem mkst] in *;
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
let HF := match goal with HFx : frame_of _ _ _ (ms_mem msx) |- _ => HFx end in
let KH9 := fresh "KH9" in let KB9 := fresh "KB9" in
assert (KH9 : forall x, alloc_ceiling <= x < 2 ^ 64 -> _ <= x -> mbyte ubs2segs (ms_mem msx) x = mbyte ubs2segs memc x)
by (intros x Hx Hlx; rewrite <- (KH8 x Hx Hlx); mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU8; lia | rewrite HU26; lia]);
assert (KB9 : forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m -> mbyte ubs2segs (ms_mem msx) (b + i) = mbyte ubs2segs memc (b + i))
by (intros b m i Hbm Hi; rewrite <- (KB8 b m i Hbm Hi); destruct (blocks_range _ _ LAWS Lc Ac memc mdc b m HHc Hbm) as [Hb0 Hb1];
mb_frame_g HF; [reflexivity | rewrite HU2; lia | rewrite HU8; lia | rewrite HU26; lia]);
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl); cbn [ss_pc];
lazymatch goal with |- SR _ (mkCfg (mkst _ ?pcv _ _) _) _ => change pcv with (Z_to_bv 64 PC_A1) end;
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
eapply (TOA1 av Ex (r_chunks (nth 0 (ss_mem ssx) (YQ0b.mkRegion None 0 0 0 0 []))));
[ exact Hav | ew_havoc; exact HU2 | ew_havoc; exact HE44 | ew_havoc; exact HE45 | ew_havoc; exact HE48 | ew_havoc; exact Hatom2
| exact (st_region_chunks ubs2segs _ _ _ 0%nat _ 2%nat _ HS eq_refl eq_refl ltac:(ew_havoc; exact HU2))
| cbv; tauto | cbv; tauto | cbv; tauto | cbv; tauto | cbv; tauto | cbv; tauto | cbv; tauto | cbv; tauto | cbv; tauto
| exact HJ4 | exact KH9 | exact KB9
| let Q := fresh "Q" in jreg HS (2%bv:reg) as Q; rewrite Q, (HE 2%nat 2%bv eq_refl); exact G2
| let Q := fresh "Q" in jreg HS (3%bv:reg) as Q; rewrite Q, (HE 3%nat 3%bv eq_refl); exact G3
| let Q := fresh "Q" in jreg HS (4%bv:reg) as Q; rewrite Q, (HE 4%nat 4%bv eq_refl); exact G4
| let Q := fresh "Q" in jreg HS (8%bv:reg) as Q; rewrite Q, (HE 8%nat 8%bv eq_refl); exact G8
| let Q := fresh "Q" in jreg HS (26%bv:reg) as Q; rewrite Q, (HE 26%nat 26%bv eq_refl); exact G26
| let Q := fresh "Q" in jreg HS (18%bv:reg) as Q; rewrite Q; exact Hatom
| let Q := fresh "Q" in jreg HS (9%bv:reg) as Q; rewrite Q; exact Hatom2
| let Q := fresh "Q" in jreg HS (21%bv:reg) as Q; exact Q
| let Q := fresh "Q" in jreg HS (27%bv:reg) as Q; rewrite Q; exact HE49 ]
end
end.
jbranch ubs2tbl HS.
{
rewrite branch_eq_U, U_and_lit, U_lit, (U_atom _ 46 fattr) in Hc by first [lia | ew_havoc; exact HE46].
assert (Hav : fattr1 fattr = 1) by (unfold fattr1; rewrite Hc; reflexivity).
jrun_to LAWS ubs2tbl_ok HS HJ4 PC_A1.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
go_A1 TOA1 HS HJ4 KH8 KB8 HE HU2 HU8 HU26 HE44 HE45 HE48 Hatom Hatom2 G2 G3 G4 G8 G26 HE10 HE11 HE49 HE50 LAWS Lc Ac memc mdc HHc 1 Hav. }
rewrite branch_eq_U, U_and_lit, U_lit, (U_atom _ 46 fattr) in Hc by first [lia | ew_havoc; exact HE46].
assert (Hav : fattr1 fattr = 9) by (unfold fattr1; rewrite Hc; reflexivity).
jrun_to LAWS ubs2tbl_ok HS HJ4 PC_A1.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
go_A1 TOA1 HS HJ4 KH8 KB8 HE HU2 HU8 HU26 HE44 HE45 HE48 Hatom Hatom2 G2 G3 G4 G8 G26 HE10 HE11 HE49 HE50 LAWS Lc Ac memc mdc HHc 9 Hav.
Qed.
Theorem ubs2_rgbadd_E1 : seg_E1 API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest.
Proof.
intros KA1 KXS KXF PRE.
exact (ubs2_rgbadd_E1a API IMG L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest
(ubs2_rgbadd_E1c KA1 KXS KXF) PRE).
Qed.
End h.
End f.
