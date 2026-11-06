(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YI00 YI02 YI01 YI03
YI1e YI1i YI57 YI07 YP14 YP15 YP13 YI08 YI0c YI0g YI3h YI3d
YI4v YI46.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition sv_poff (fmtv : Z) : sv := if fmtv =? 4 then SAlu ALU_SLL (SOff 9%nat 0) (SLit 2) else SMd M_MUL (SOff 9%nat 0) (SLit 3).
Definition sv_pix (fmtv : Z) : sv := SAlu ALU_ADD (sv_poff fmtv) (SOff 26%nat 0).
Lemma U_poff : forall E fmtv i, ew E 9 = Z_to_bv 64 i -> 0 <= i <= 10000 -> (fmtv = 3 \/ fmtv = 4) -> U E (sv_poff fmtv) = fmtv * i.
Proof.
intros E fmtv i Hi Ri [-> | ->]; unfold sv_poff; cbn [Z.eqb Pos.eqb].
- rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E 9 i Hi), U_SLit by lia. rewrite (zcanon_id 3) by (unfold M64; lia). rewrite Z.mul_comm. apply zcanon_id. unfold M64; lia.
- rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 9 i Hi), U_SLit by lia. change (Z.land (zcanon 2) 63) with 2.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite Z.mul_comm. apply zcanon_id. unfold M64; lia.
Qed.
Lemma U_pix : forall E fmtv i img, ew E 9 = Z_to_bv 64 i -> ew E 26 = Z_to_bv 64 img -> 0 <= i <= 10000 -> (fmtv = 3 \/ fmtv = 4) ->
0 <= img -> img + fmtv * i < 2 ^ 64 -> U E (sv_pix fmtv) = img + fmtv * i.
Proof.
intros E fmtv i img Hi Himg Ri Hf R0 R1. unfold sv_pix. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_poff E fmtv i Hi Ri Hf), (U_atom E 26 img Himg) by lia. rewrite Z.add_comm. apply zcanon_id. unfold M64. destruct Hf as [-> | ->]; lia.
Qed.
Lemma branch_ge_sext8 : forall E n a,
ew E n = Z_to_bv 64 a -> 0 <= a < 256 ->
branch_taken BC_GE (sv_denot E (SExt true 8 (SOff n 0))) (sv_denot E (SLit 0)) = negb (128 <=? a).
Proof. intros E n a Hn Ha. change BC_GE with (neg_bc BC_LT). rewrite branch_taken_neg, (branch_lt_sext8 E n a Hn Ha). reflexivity. Qed.
Definition hl_sr (fmtv : Z) : list sv := sr_set (sr_set (sr_set sr_atoms 15%bv (SLit fmtv)) 27%bv (SLit fmtv)) 16%bv (SLit 3).
Definition hl_pix3 : list YQ0b.chunk := [mkChunk 0 (CVal 1 (SOff 33%nat 0)); mkChunk 1 (CVal 1 (SOff 34%nat 0)); mkChunk 2 (CVal 1 (SOff 35%nat 0))].
Definition hl_cht : list YQ0b.chunk := [mkChunk 8 (CVal 8 (SOff 39%nat 0)); mkChunk 16 (CVal 8 (SOff 40%nat 0)); mkChunk 44 (CVal 4 (SOff 41%nat 0))].
Definition hl_mem (fmtv : Z) : smem :=
[ YQ0b.mkRegion (Some 32%nat) 0 fmtv 0 0 (if fmtv =? 4 then hl_pix3 ++ [mkChunk 3 (CVal 1 (SOff 36%nat 0))] else hl_pix3) ;
YQ0b.mkRegion (Some 37%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 38%nat 0))] ;
YQ0b.mkRegion (Some 20%nat) 0 48 0 0 hl_cht ].
Definition hl_atoms : list (nat * afact) :=
[ (2%nat, mkAF CEIL_MIN (2^63) 4); (9%nat, mkAF 0 10000 0); (41%nat, mkAF 521 (2^24) 0);
(40%nat, mkAF 4096 CEIL_MAX 0); (32%nat, mkAF 4096 CEIL_MAX 0); (20%nat, mkAF 4096 (CEIL_MAX - 48) 0);
(33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0); (36%nat, mkAF 0 255 0);
(37%nat, mkAF 4096 CEIL_MAX 0); (38%nat, mkAF 0 1 0) ].
Definition hl_alias (fmtv : Z) : list (sv * sv) :=
[ (sv_pix fmtv, SOff 32%nat 0);
(SAlu ALU_ADD (SOff 40%nat 0) (sv_zx (sv_hsh 33 34 35 41)), SOff 37%nat 0) ].
Definition ss_HL (fmtv : Z) : sstate := mkSS PC_HL (hl_sr fmtv) (hl_mem fmtv) None (mkFacts hl_atoms [] (hl_alias fmtv)).
Section c.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
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
Local Notation AT_INS := (at_INS API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation AT_INC := (at_INC API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation SEP_BC := (sep_base_cht API r g bef beffmt s N img fmt rest).
Local Notation HM_UPD := (hist_mem_update API regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay rest).
Section d.
Variables (i : Z) (Lc : layout) (Ac : astate) (mdc : Model) (pnew fimg : Z) (imgl : list Z) (C : cht).
Hypothesis KINC : forall regs1 memc ha' C', AT_INC regs1 Lc Ac memc mdc i ha' pnew fimg imgl C' ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_INC) memc (seg_rom src2segs)) mdc) POST.
Hypothesis KINS : forall regs1 memc ha h, AT_INS regs1 Lc Ac memc mdc i ha pnew fimg imgl C h ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_INS) memc (seg_rom src2segs)) mdc) POST.
Hypothesis KL0 : forall regs1 memc ha, AT_L regs1 Lc Ac memc mdc i ha pnew fimg imgl C 0 ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_L) memc (seg_rom src2segs)) mdc) POST.
Theorem HL_stretch : forall regs1 memc ha, AT_HL regs1 Lc Ac memc mdc i ha pnew fimg imgl C ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_HL) memc (seg_rom src2segs)) mdc) POST.
Proof.
intros regs1 memc ha HAT.
destruct HAT as (HINV & HREGS & Hfmt & Hi & Hha & HR & HMEM).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbf & HB0).
destruct HREGS as (G2 & G3 & G4).
destruct HR as (G9 & G10 & G15 & G16 & G17 & G26 & G27 & G20 & G8 & G21).
pose proof HMEM as (Hslots & S16 & S104 & S64 & S80 & S88 & S96 & Hfc & Hobj & Hcg & [Himg Hlen] & Hcht & EhS & EuS & ETS & Hz & Hpn & Hfi & HB).
pose proof Hcht as (Hobjc & (Af & Ah & Au & Ap & Ax) & Hinv & HT & Hch & RhS & RuS & RTS).
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5136) by reflexivity.
pose proof (ts_chain_ok _ Hch) as (RT1 & RT2 & RT3). unfold MAX_TABLE_SIZE in RT1.
pose proof Hinv as ((L1 & L2 & L3 & L4 & L5) & (C1 & C2 & C3) & (B1 & B2 & B3) & _). rewrite HT in L1, L2, L3, L4, L5, C1.
set (T := ch_T C) in *. set (col := pxc fmt imgl i). set (h0 := hash0 T col).
assert (Rh0 : 0 <= h0 < T) by (subst h0; apply hash0_range; lia).
unfold RGB_NMAX in HNmax.
assert (Himgb : In (img, fmt * N) (blocks Lc Ac)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. left. unfold BASE. right.
apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. unfold img_block, fmt_okb.
destruct Hfmt as [-> | ->]; left; reflexivity. }
destruct (heap_blocks_range src2_msyms MR LAWS Lc Ac memc mdc img (fmt * N) HHc Himgb ltac:(lia)) as (Ri0 & Ri1 & _).
set (pix := img + fmt * i).
assert (PX1 : 0 <= fmt * i) by nia. assert (PX2 : fmt * i + fmt <= fmt * N) by nia. assert (PX3 : fmt * N <= 4 * N) by nia.
assert (PB : forall k, 0 <= k < fmt -> mbyte src2segs memc (pix + k) = Some (Z_to_bv 8 (getz imgl (fmt * i + k))) /\ 0 <= getz imgl (fmt * i + k) < 256).
{ intros k Hk. subst pix. rewrite <- Z.add_assoc. apply (arr8_getz src2segs memc img imgl); [exact Himg | lia]. }
assert (Hub : In (ch_u C, T) (blocks Lc Ac)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. right. apply in_app_iff. right. unfold cht_blks, cht_blocks. subst T. cbn. auto 10. }
destruct (heap_blocks_range src2_msyms MR LAWS Lc Ac memc mdc (ch_u C) T HHc Hub ltac:(lia)) as (Ru0 & Ru1 & _).
destruct (arr8_getz src2segs memc (ch_u C) (ht_used (ch_H C)) h0 Au ltac:(lia)) as [Bu0 Ru0'].
set (used0 := getz (ht_used (ch_H C)) h0) in *.
assert (U01 : used0 = 0 \/ used0 = 1) by (subst used0; exact (B1 h0 ltac:(rewrite HT; lia))).
assert (Hcb : In (ch_c C, CHT_SIZE) (blocks Lc Ac)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. right. apply in_app_iff. right. left. reflexivity. }
destruct (heap_blocks_range src2_msyms MR LAWS Lc Ac memc mdc (ch_c C) CHT_SIZE HHc Hcb ltac:(unfold CHT_SIZE; lia)) as (Rc0 & Rc1 & _).
unfold CHT_SIZE in Rc1.
assert (Hy : In (img, fmt * N) (BASE0 ++ [(pnew, fmt * N); (fimg, N)])).
{ apply in_app_iff. left. unfold BASE. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
unfold img_block, fmt_okb. destruct Hfmt as [-> | ->]; left; reflexivity. }
assert (SEP : img + fmt * N <= ch_u C \/ ch_u C + T <= img).
{ pose proof (sep_base_cht_blk API r g bef beffmt s N img fmt rest Lc Ac memc mdc pnew fimg C (img, fmt * N) (ch_u C, T) HHc HB Hy
ltac:(unfold cht_blks, cht_blocks; subst T; cbn; auto 10)) as X. cbn [fst snd] in X. lia. }
assert (SEPc : img + fmt * N <= ch_c C \/ ch_c C + 48 <= img).
{ pose proof (sep_base_cht_blk API r g bef beffmt s N img fmt rest Lc Ac memc mdc pnew fimg C (img, fmt * N) (ch_c C, CHT_SIZE) HHc HB Hy
ltac:(left; reflexivity)) as X. cbn [fst snd] in X. unfold CHT_SIZE in X. lia. }
assert (SEPuc : ch_c C + 48 <= ch_u C \/ ch_u C + T <= ch_c C).
{ pose proof (cht_apart_of_perm API Lc Ac memc mdc (BASE0 ++ [(pnew, fmt * N); (fimg, N)]) C HHc ltac:(rewrite <- app_assoc; exact HB)) as CA.
pose proof (cht_apart_blocks C 0%nat 3%nat (ch_c C, CHT_SIZE) (ch_u C, T) CA ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold CHT_SIZE in X. lia. }
pose proof Hobjc as Hobjc'. cbn [obj_at LAY_Cht] in Hobjc'. unfold field_ok in Hobjc'. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Hobjc'.
destruct Hobjc' as (_ & [Vh _] & [Vu _] & _ & _ & _ & [VT _] & _).
rewrite EhS in Vh. rewrite EuS in Vu. rewrite ETS in VT. fold T in VT.
assert (Hhb : In (ch_h C, 3 * T) (blocks Lc Ac)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. right. apply in_app_iff. right. unfold cht_blks, cht_blocks. subst T. cbn. auto 10. }
destruct (heap_blocks_range src2_msyms MR LAWS Lc Ac memc mdc (ch_h C) (3 * T) HHc Hhb ltac:(lia)) as (Rhh0 & Rhh1 & _).
set (vals := [pix; getz imgl (fmt * i); getz imgl (fmt * i + 1); getz imgl (fmt * i + 2); getz imgl (fmt * i + 3); ch_u C + h0; used0; ch_h C; ch_u C; T]).
set (E := Ereg regs1 (map (Z_to_bv 64) vals ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall jj v, nth_error vals jj = Some v -> ew E (32 + jj) = Z_to_bv 64 v)
by (intros jj v Hjj; subst E; apply Ereg_vals; exact Hjj).
assert (HE32 : ew E 32 = Z_to_bv 64 pix) by exact (HV 0%nat _ eq_refl).
assert (HE33 : ew E 33 = Z_to_bv 64 (getz imgl (fmt * i))) by exact (HV 1%nat _ eq_refl).
assert (HE34 : ew E 34 = Z_to_bv 64 (getz imgl (fmt * i + 1))) by exact (HV 2%nat _ eq_refl).
assert (HE35 : ew E 35 = Z_to_bv 64 (getz imgl (fmt * i + 2))) by exact (HV 3%nat _ eq_refl).
assert (HE36 : ew E 36 = Z_to_bv 64 (getz imgl (fmt * i + 3))) by exact (HV 4%nat _ eq_refl).
assert (HE37 : ew E 37 = Z_to_bv 64 (ch_u C + h0)) by exact (HV 5%nat _ eq_refl).
assert (HE38 : ew E 38 = Z_to_bv 64 used0) by exact (HV 6%nat _ eq_refl).
assert (HE39 : ew E 39 = Z_to_bv 64 (ch_h C)) by exact (HV 7%nat _ eq_refl).
assert (HE40 : ew E 40 = Z_to_bv 64 (ch_u C)) by exact (HV 8%nat _ eq_refl).
assert (HE41 : ew E 41 = Z_to_bv 64 T) by exact (HV 9%nat _ eq_refl).
assert (HU2 : bv_unsigned (ew E 2) = SP) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (HE9 : ew E 9 = Z_to_bv 64 i) by (rewrite (HE 9%nat 9%bv eq_refl); exact G9).
assert (HE26 : ew E 26 = Z_to_bv 64 img) by (rewrite (HE 26%nat 26%bv eq_refl); exact G26).
assert (HU20 : bv_unsigned (ew E 20) = ch_c C) by (rewrite (HE 20%nat 20%bv eq_refl), G20; apply unsigned_lit_small; lia).
pose proof (PB 0 ltac:(lia)) as [P0 R0']. rewrite Z.add_0_r in P0, R0'. pose proof (PB 1 ltac:(lia)) as [P1 R1']. pose proof (PB 2 ltac:(lia)) as [P2 R2'].
assert (Hcol : colour_ok col) by (subst col; unfold pxc, colour_ok, cR, cG, cB, mkcol; cbn [fst snd]; lia).
assert (UH : U E (sv_hsh 33 34 35 41) = h0).
{ subst h0. apply (U_hsh E 33 34 35 41 col T); [ | | | exact Hcol | exact HE41 | lia]; subst col; unfold pxc, cR, cG, cB, mkcol; cbn [fst snd]; assumption. }
assert (HS : st_ok src2segs E (ss_HL fmt) (mkst regs1 (Z_to_bv 64 PC_HL) memc (seg_rom src2segs))).
{ unfold ss_HL. subst E. apply entry_st_ok_full.
- unfold hl_sr. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | rewrite G15; reflexivity] | intros X; discriminate X | rewrite G27; reflexivity] | intros X; discriminate X | rewrite G16; reflexivity].
- unfold hl_mem. destruct Hfmt as [-> | ->]; vm_compute; reflexivity.
- unfold hl_mem. constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE32, unsigned_lit_small by (subst pix; lia).
split; [subst pix; lia|]. split; [subst pix; lia|]. split; [intros o Ho; lia|].
assert (CK : forall k n, 0 <= k < fmt -> ew (Ereg regs1 (map (Z_to_bv 64) vals ++ [])) n = Z_to_bv 64 (getz imgl (fmt * i + k)) ->
chunk_ok src2segs (Ereg regs1 (map (Z_to_bv 64) vals ++ [])) memc pix (mkChunk k (CVal 1 (SOff n 0)))).
{ intros k n Hk Hn. destruct (PB k Hk) as [Pk Rk]. eapply (chunk_ok_val _ _ _ _ _ _ _ (getz imgl (fmt * i + k))); [cbn [sv_denot]; rewrite Z.add_0_r, Hn, unsigned_lit_small by lia; reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; exact Rk | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op]. apply val_mem_byte; [exact Pk | exact Rk]. }
destruct Hfmt as [-> | ->]; cbn [Z.eqb hl_pix3 app]; repeat apply Forall_cons; try apply Forall_nil.
* apply (CK 0 33%nat); [lia | replace (3 * i + 0) with (3 * i) by lia; exact HE33].
* apply (CK 1 34%nat); [lia | exact HE34].
* apply (CK 2 35%nat); [lia | exact HE35].
* apply (CK 0 33%nat); [lia | replace (4 * i + 0) with (4 * i) by lia; exact HE33].
* apply (CK 1 34%nat); [lia | exact HE34].
* apply (CK 2 35%nat); [lia | exact HE35].
* apply (CK 3 36%nat); [lia | exact HE36].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HE37, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ used0); [cbn [sv_denot]; rewrite Z.add_0_r, HE38, unsigned_lit_small by lia; reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op]. rewrite Z.add_0_r. apply val_mem_byte; [exact Bu0 | lia].
+ unfold region_ok, hl_cht. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU20.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
* eapply (chunk_ok_val _ _ _ _ _ _ _ (ch_h C)); [cbn [sv_denot]; rewrite Z.add_0_r, HE39, unsigned_lit_small by lia; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact Vh].
* eapply (chunk_ok_val _ _ _ _ _ _ _ (ch_u C)); [cbn [sv_denot]; rewrite Z.add_0_r, HE40, unsigned_lit_small by lia; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact Vu].
* eapply (chunk_ok_val _ _ _ _ _ _ _ T); [cbn [sv_denot]; rewrite Z.add_0_r, HE41, unsigned_lit_small by lia; reflexivity | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia | exact VT].
- unfold hl_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU20, HE32, HE37, !unsigned_lit_small by (subst pix; lia).
repeat match goal with |- _ /\ _ => split | |- True => exact I end.
+ subst pix; clear - SEP Hi Rh0 PX1 PX2; destruct SEP; [left; lia | right; lia].
+ subst pix; clear - SEPc Hi PX1 PX2; destruct SEPc; [left; lia | right; lia].
+ clear - SEPuc Rh0; destruct SEPuc; [right; lia | left; lia].
- unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [| split; [exact I|]].
+ cbn [atoms_ok hl_atoms]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU20, (ew_Ereg_nat regs1 _ 9 9%bv eq_refl), G9, HE32, HE33, HE34, HE35, HE36, HE37, HE38, HE40, HE41.
assert (R3' : 0 <= getz imgl (fmt * i + 3) < 256).
{ destruct Hfmt as [-> | ->]; [| exact (proj2 (PB 3 ltac:(lia)))].
destruct (Z_lt_le_dec (3 * i + 3) (zlen imgl)) as [Hl|Hl]; [exact (proj2 (arr8_getz src2segs memc img imgl (3 * i + 3) Himg ltac:(lia))) | rewrite getz_oob by lia; lia]. }
unfold sp, sp0 in *. subst pix.
rewrite !unsigned_lit_small by lia.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
assert (Hsp16 : (spZ regs0 - RGBA_FRAME) mod 16 = 0).
{ unfold RGBA_FRAME. replace (spZ regs0 - 5136) with (spZ regs0 + (-321) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
repeat match goal with |- _ /\ _ => split | |- True => exact I end; lia.
+ cbn [alias_ok hl_alias]. split; [|split; [|exact I]].
* apply U_inj. rewrite (U_atom _ 32 pix HE32) by (subst pix; lia). subst pix.
apply (U_pix _ fmt i img HE9 HE26); [lia | exact Hfmt | lia | lia].
* apply U_inj. rewrite (U_atom _ 37 (ch_u C + h0) HE37) by lia.
apply (U_add_atom _ 40 (ch_u C) _ h0); [exact HE40 | lia | | lia | lia].
apply (U_zx _ _ h0); [exact UH | lia]. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_HL) memc (seg_rom src2segs))) in HJ.
assert (EA0 : env_agree 32 (Ereg regs1 []) E).
{ subst E. split; [intros n Hn; rewrite !ew_Ereg_lt by exact Hn; reflexivity | reflexivity]. }
clearbody E. clear HV.
assert (ARR : forall ss ms', st_ok src2segs E ss ms' -> ms_mem ms' = memc ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ss) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) [2; 3; 4; 20; 9; 8; 21; 17]%bv = true ->
RINV Lc Ac (ms_mem ms') mdc /\ rgba_regs regs0 (ms_regs ms') /\ body_regs r (ms_regs ms') C i /\ getr (ms_regs ms') 17 = Z_to_bv 64 N /\
(forall i', zsum (map snd (ch_ent C)) <= i' -> HM Lc Ac (ms_mem ms') pnew fimg imgl C i')).
{ intros ss ms' HS' Hmm QK.
assert (GK : forall rr, In rr [2; 3; 4; 20; 9; 8; 21; 17]%bv -> getr (ms_regs ms') rr = getr regs1 rr).
{ intros rr Hrr. apply (regs_kept_of_st_ok src2segs E ss ms' regs1 _ _ HS' EA0 QK rr Hrr). }
rewrite Hmm.
split; [exact HINV|].
split. { split; [rewrite (GK 2%bv ltac:(cbv; auto 10)); exact G2|]. split; [rewrite (GK 3%bv ltac:(cbv; auto 10)); exact G3 | rewrite (GK 4%bv ltac:(cbv; auto 10)); exact G4]. }
split. { unfold body_regs. rewrite (GK 20%bv ltac:(cbv; auto 10)), (GK 9%bv ltac:(cbv; auto 10)), (GK 8%bv ltac:(cbv; auto 10)), (GK 21%bv ltac:(cbv; auto 10)).
repeat split; assumption. }
split; [rewrite (GK 17%bv ltac:(cbv; auto 10)); exact G17|].
intros i' Hi'. apply (HM_UPD Lc Ac memc mdc memc pnew fimg imgl C C i i' HHc); [unfold sp, sp0 in *; lia | unfold sp, sp0 in *; lia | exact Hfmt | exact HMEM | intros; reflexivity | exact Hcht | reflexivity | reflexivity | exact EhS | exact EuS | exact ETS | exact Hi']. }
Ltac ro3 := apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_nil.
assert (TOINS : forall ss ms', st_ok src2segs E ss ms' -> ms_mem ms' = memc -> ss_resv ss = None -> ss_pc ss = PC_INS ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ss) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) [2; 3; 4; 20; 9; 8; 21; 17]%bv = true ->
sr_get (ss_regs ss) 19 = sv_hsh 33 34 35 41 -> sr_get (ss_regs ss) 11 = sv_zx (sv_hsh 33 34 35 41) ->
sr_get (ss_regs ss) 10 = SOff 38 0 -> sr_get (ss_regs ss) 5 = SOff 10 0 -> sr_get (ss_regs ss) 22 = SOff 32 0 -> sr_get (ss_regs ss) 23 = SOff 39 0 ->
sr_get (ss_regs ss) 15 = SLit fmt -> sr_get (ss_regs ss) 16 = SLit 3 -> sr_get (ss_regs ss) 26 = SOff 26 0 -> sr_get (ss_regs ss) 27 = SLit fmt ->
opaque_px fmt imgl i -> used0 = 0 ->
SR src2segs (mkCfg ms' mdc) POST).
{ intros ss ms' HS' Hmm Hrv Hpc QK Q19 Q11 Q10 Q5 Q22 Q23 Q15 Q16 Q26 Q27 Hop Hu0.
destruct (ARR _ _ HS' Hmm QK) as (RI & RR & BR & R17 & HMi).
rewrite (st_ok_mkst src2segs _ _ _ HS' Hrv), Hpc.
apply (KINS (ms_regs ms') (ms_mem ms') ha h0). unfold at_INS.
split; [exact RI|]. split; [exact RR|]. split; [exact Hfmt|]. split; [exact Hi|]. split; [exact Hha|]. split; [exact Hop|].
split. { subst h0 col T. rewrite <- HT. apply (find_slot_home_free (ch_H C) (ch_ent C)); [exact Hinv|]. rewrite HT. exact Hu0. }
split; [exact Hu0|].
split; [eapply (getr_of_U src2segs); [exact HS'|]; rewrite Q19; exact UH|].
split; [eapply (getr_of_U src2segs); [exact HS'|]; rewrite Q11; apply (U_zx _ _ h0); [exact UH | lia]|].
split. { exists 0. split; [left; reflexivity|]. eapply (getr_of_U src2segs); [exact HS'|]. rewrite Q10, (U_atom E 38 used0 HE38) by lia. exact Hu0. }
split; [eapply (getr_of_U src2segs); [exact HS'|]; rewrite Q5; apply (U_atom E 10 ha); [rewrite (HE 10%nat 10%bv eq_refl); exact G10 | destruct Hha as [-> | [-> _]]; lia]|].
split; [eapply (getr_of_U src2segs); [exact HS'|]; rewrite Q22; apply (U_atom E 32 pix HE32); subst pix; lia|].
split; [eapply (getr_of_U src2segs); [exact HS'|]; rewrite Q23; apply (U_atom E 39 (ch_h C) HE39); lia|].
split. { unfold head_regs.
split; [eapply (getr_of_U src2segs); [exact HS'|]; rewrite Q15; apply U_lit; lia|].
split; [eapply (getr_of_U src2segs); [exact HS'|]; rewrite Q16; apply U_lit; lia|].
split; [exact R17|].
split; [eapply (getr_of_U src2segs); [exact HS'|]; rewrite Q26; apply (U_atom E 26 img HE26); lia|].
eapply (getr_of_U src2segs); [exact HS'|]; rewrite Q27; apply U_lit; lia. }
split; [exact BR|]. apply HMi. exact Hz. }
assert (TOL : forall ss ms', st_ok src2segs E ss ms' -> ms_mem ms' = memc -> ss_resv ss = None -> ss_pc ss = PC_L ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ss) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) [2; 3; 4; 20; 9; 8; 21; 17]%bv = true ->
sr_get (ss_regs ss) 19 = sv_hsh 33 34 35 41 -> sr_get (ss_regs ss) 25 = SLit 0 ->
sr_get (ss_regs ss) 22 = SOff 32 0 -> sr_get (ss_regs ss) 23 = SOff 39 0 -> sr_get (ss_regs ss) 18 = SOff 40 0 -> sr_get (ss_regs ss) 24 = SOff 41 0 ->
sr_get (ss_regs ss) 27 = SOff 26 0 -> sr_get (ss_regs ss) 26 = SOff 10 0 ->
opaque_px fmt imgl i -> used0 <> 0 ->
SR src2segs (mkCfg ms' mdc) POST).
{ intros ss ms' HS' Hmm Hrv Hpc QK Q19 Q25 Q22 Q23 Q18 Q24 Q27 Q26 Hop Hu0.
destruct (ARR _ _ HS' Hmm QK) as (RI & RR & BR & R17 & HMi).
rewrite (st_ok_mkst src2segs _ _ _ HS' Hrv), Hpc.
apply (KL0 (ms_regs ms') (ms_mem ms') ha). unfold at_L.
split; [exact RI|]. split; [exact RR|]. split; [exact Hfmt|]. split; [exact Hi|]. split; [exact Hha|]. split; [exact Hop|].
split. { destruct (find_off_exists (ch_H C) (ch_ent C) Hinv col) as [js Ejs]. exists js. split; [exact Ejs|].
pose proof (find_off_ge0 (ch_H C) (ch_ent C) col js Hinv Ejs). lia. }
change (cyc (ch_T C) (hash0 (ch_T C) (pxc fmt imgl i)) 0) with (cyc T h0 0). rewrite cyc_0 by exact Rh0.
split; [exact Hu0|].
split; [eapply (getr_of_U src2segs); [exact HS'|]; rewrite Q19; exact UH|].
split; [eapply (getr_of_U src2segs); [exact HS'|]; rewrite Q25; apply U_lit; lia|].
split. { unfold probe_regs.
split; [eapply (getr_of_U src2segs); [exact HS'|]; rewrite Q22; apply (U_atom E 32 pix HE32); subst pix; lia|].
split; [eapply (getr_of_U src2segs); [exact HS'|]; rewrite Q23; apply (U_atom E 39 (ch_h C) HE39); lia|].
split; [eapply (getr_of_U src2segs); [exact HS'|]; rewrite Q18; apply (U_atom E 40 (ch_u C) HE40); lia|].
split; [eapply (getr_of_U src2segs); [exact HS'|]; rewrite Q24; apply (U_atom E 41 T HE41); lia|].
split; [eapply (getr_of_U src2segs); [exact HS'|]; rewrite Q27; apply (U_atom E 26 img HE26); lia|].
eapply (getr_of_U src2segs); [exact HS'|]; rewrite Q26; apply (U_atom E 10 ha); [rewrite (HE 10%nat 10%bv eq_refl); exact G10 | destruct Hha as [-> | [-> _]]; lia]. }
split; [exact BR|]. apply HMi. exact Hz. }
destruct Hfmt as [Hf | Hf]; rewrite Hf in HS.
-
jrun LAWS src2tbl_ok HS HJ. { ro3. }
cbn [ms_mem mkst] in HF.
assert (Hm0 : ms_mem ms = memc) by (apply functional_extensionality; intros x0; refine (frame_of_ro _ _ _ _ _ HF x0); reflexivity).
jbranch src2tbl HS.
+
rewrite branch_eq_U, (U_atom E 38 used0 HE38), U_lit in Hc by lia. apply Z.eqb_eq in Hc.
jrun_to LAWS src2tbl_ok HS HJ PC_INS. { ro3. }
cbn [ms_mem mkst] in HF0.
assert (Hm1 : ms_mem ms0 = memc) by (rewrite <- Hm0; apply functional_extensionality; intros x0; refine (frame_of_ro _ _ _ _ _ HF0 x0); reflexivity).
apply (TOINS _ _ HS Hm1 eq_refl eq_refl); try (rewrite Hf); try (vm_compute; reflexivity); [intros H4; exfalso; lia | exact Hc].
+
rewrite branch_eq_U, (U_atom E 38 used0 HE38), U_lit in Hc by lia. apply Z.eqb_neq in Hc.
jrun_to LAWS src2tbl_ok HS HJ PC_L. { ro3. }
cbn [ms_mem mkst] in HF0.
assert (Hm1 : ms_mem ms0 = memc) by (rewrite <- Hm0; apply functional_extensionality; intros x0; refine (frame_of_ro _ _ _ _ _ HF0 x0); reflexivity).
apply (TOL _ _ HS Hm1 eq_refl eq_refl); try (vm_compute; reflexivity); [intros H4; exfalso; lia | exact Hc].
-
assert (Ra : 0 <= getz imgl (4 * i + 3) < 256) by (rewrite <- Hf; exact (proj2 (PB 3 ltac:(lia)))).
jrun LAWS src2tbl_ok HS HJ. { ro3. }
cbn [ms_mem mkst] in HF.
assert (Hm0 : ms_mem ms = memc) by (apply functional_extensionality; intros x0; refine (frame_of_ro _ _ _ _ _ HF x0); reflexivity).
jbranch src2tbl HS.
+
rewrite Hf in HE36. rewrite (branch_ge_sext8 _ 36 _ HE36 Ra) in Hc. apply Bool.negb_true_iff, Z.leb_gt in Hc.
jrun_to LAWS src2tbl_ok HS HJ PC_INC. { ro3. }
cbn [ms_mem mkst] in HF0.
assert (Hm1 : ms_mem ms0 = memc) by (rewrite <- Hm0; apply functional_extensionality; intros x0; refine (frame_of_ro _ _ _ _ _ HF0 x0); reflexivity).
destruct (ARR _ _ HS Hm1 ltac:(vm_compute; reflexivity)) as (RI & RR & BR & R17 & HMi).
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc]. change (Z_to_bv 64 80572) with (Z_to_bv 64 PC_INC).
apply (KINC (ms_regs ms0) (ms_mem ms0) 1 C). unfold at_INC.
split; [exact RI|]. split; [exact RR|]. split; [right; exact Hf|]. split; [exact Hi|]. split; [right; split; [reflexivity | exact Hf]|].
destruct BR as (B20 & B9 & B8 & B21).
split. { unfold hist_regs.
split; [exact B9|].
split; [jreg HS (10%bv:reg) as Hq; exact Hq|].
split; [jreg HS (15%bv:reg) as Hq; rewrite Hq, Hf; reflexivity|].
split; [jreg HS (16%bv:reg) as Hq; exact Hq|].
split; [exact R17|].
split; [jreg HS (26%bv:reg) as Hq; rewrite Hq, (HE 26%nat 26%bv eq_refl); exact G26|].
split; [jreg HS (27%bv:reg) as Hq; rewrite Hq, Hf; reflexivity|].
split; [exact B20|]. split; [exact B8 | exact B21]. }
apply HMi. lia.
+
rewrite Hf in HE36. rewrite (branch_ge_sext8 _ 36 _ HE36 Ra) in Hc. apply Bool.negb_false_iff, Z.leb_le in Hc.
jrun LAWS src2tbl_ok HS HJ. { ro3. }
cbn [ms_mem mkst] in HF0.
assert (Hm1 : ms_mem ms0 = memc) by (rewrite <- Hm0; apply functional_extensionality; intros x0; refine (frame_of_ro _ _ _ _ _ HF0 x0); reflexivity).
jbranch src2tbl HS.
*
rewrite branch_eq_U, (U_atom E 38 used0 HE38), U_lit in Hc0 by lia. apply Z.eqb_eq in Hc0.
jrun_to LAWS src2tbl_ok HS HJ PC_INS. { ro3. }
cbn [ms_mem mkst] in HF1.
assert (Hm2 : ms_mem ms1 = memc) by (rewrite <- Hm1; apply functional_extensionality; intros x0; refine (frame_of_ro _ _ _ _ _ HF1 x0); reflexivity).
apply (TOINS _ _ HS Hm2 eq_refl eq_refl); try (rewrite Hf); try (vm_compute; reflexivity); [intros _; unfold pxa; exact Hc | exact Hc0].
*
rewrite branch_eq_U, (U_atom E 38 used0 HE38), U_lit in Hc0 by lia. apply Z.eqb_neq in Hc0.
jrun_to LAWS src2tbl_ok HS HJ PC_L. { ro3. }
cbn [ms_mem mkst] in HF1.
assert (Hm2 : ms_mem ms1 = memc) by (rewrite <- Hm1; apply functional_extensionality; intros x0; refine (frame_of_ro _ _ _ _ _ HF1 x0); reflexivity).
apply (TOL _ _ HS Hm2 eq_refl eq_refl); try (vm_compute; reflexivity); [intros _; unfold pxa; rewrite Hf; exact Hc | exact Hc0].
Qed.
End d.
End c.
End b.
