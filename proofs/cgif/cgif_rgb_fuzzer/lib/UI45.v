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
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma U_mul3_add' : forall E n m i b,
ew E n = Z_to_bv 64 i -> 0 <= i -> ew E m = Z_to_bv 64 b -> 0 <= b -> b + 3 * i < 2 ^ 64 ->
U E (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit 3)) (SOff m 0)) = b + 3 * i.
Proof.
intros E n m i b Hn Hi Hm Hb Hnw. rewrite <- (U_add_mul3' E n m i b Hn Hi Hm Hb Hnw).
rewrite !U_SAlu. cbn [zalu_raw]. rewrite Z.add_comm. reflexivity.
Qed.
Lemma U_add_sll2' : forall E n m i b,
ew E n = Z_to_bv 64 i -> 0 <= i < 2 ^ 60 -> ew E m = Z_to_bv 64 b -> 0 <= b -> b + 4 * i < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff m 0) (SAlu ALU_SLL (SOff n 0) (SLit 2))) = b + 4 * i.
Proof.
intros E n m i b Hn Hi Hm Hb Hnw. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
rewrite (U_atom E n i Hn), (U_atom E m b Hm) by lia. change (Z.land (zcanon 2) 63) with 2.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite (zcanon_id (i * 4)) by (unfold M64; lia).
rewrite zcanon_id; unfold M64; lia.
Qed.
Lemma mbyte_of_val_mem1 : forall (m : word -> option byte) a v,
val_mem ubs2segs m a 1 v -> 0 <= v < 256 -> mbyte ubs2segs m a = Some (Z_to_bv 8 v).
Proof.
intros m a v H Hv. specialize (H 0%nat ltac:(lia)). cbn [Z.of_nat] in H. rewrite Z.add_0_r in H. rewrite H.
rewrite le_byte_small; [| change (2 ^ (8 * Z.of_nat 1)) with 256; exact Hv | lia].
change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
Qed.

Lemma U_srl24 : forall E n T, ew E n = Z_to_bv 64 T -> 0 <= T < 2 ^ 31 ->
U E (SAlu ALU_SRL (SOff n 0) (SLit 24)) = Z.shiftr T 24.
Proof.
intros E n T Hn HT. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom E n T Hn) by lia.
change (Z.land (zcanon 24) 63) with 24.
assert (HR : 0 <= Z.shiftr T 24 < 2 ^ 7) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
apply zcanon_id. unfold M64. lia.
Qed.
Lemma U_flag31 : forall E n j, ew E n = Z_to_bv 64 j -> 0 <= j < 2 ^ 32 ->
U E (SAlu ALU_XOR (SAlu ALU_SLTU (SOff n 0) (SLit 31)) (SLit 1)) = if j <? 31 then 0 else 1.
Proof.
intros E n j Hn Hj. rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit, (U_atom E n j Hn) by lia.
rewrite (zcanon_id 31), (zcanon_id 1) by (unfold M64; lia).
destruct (j <? 31); [rewrite (zcanon_id 1) by (unfold M64; lia) | rewrite (zcanon_id 0) by (unfold M64; lia)]; reflexivity.
Qed.
Lemma mod4_add16 : forall b i, b mod 16 = 0 -> (b + 4 * i) mod 2 ^ 2 = 0.
Proof.
intros b i Hb. change (2 ^ 2) with 4. apply (proj1 (Z.mod_divide b 16 ltac:(lia))) in Hb. destruct Hb as [k ->].
replace (k * 16 + 4 * i) with ((4 * k + i) * 4) by ring. apply Z.mod_mul. lia.
Qed.
Definition px_stack : YQ0b.region :=
YQ0b.mkRegion (Some 2%nat) 0 5168 0 0 [mkChunk 40 (CVal 8 (SOff 32%nat 0))].
Definition px0_smem : smem := [ px_stack ;
YQ0b.mkRegion (Some 35%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SLit 0))] ;
YQ0b.mkRegion (Some 20%nat) 0 48 0 0 [mkChunk 16 (CVal 8 (SOff 33%nat 0))] ].
Definition px1_smem : smem :=
[ px_stack ;
YQ0b.mkRegion (Some 35%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SLit 1))] ;
YQ0b.mkRegion (Some 36%nat) 0 4 0 4 [mkChunk 0 (CVal 4 (SOff 37%nat 0))] ;
YQ0b.mkRegion (Some 20%nat) 0 48 0 0 [mkChunk 0 (CVal 8 (SOff 38%nat 0)); mkChunk 16 (CVal 8 (SOff 33%nat 0)); mkChunk 40 (CVal 4 (SOff 39%nat 0))] ].
Definition px0_atoms : list (nat * afact) := [ (2%nat, mkAF CEIL_MIN (2^63) 4); (27%nat, mkAF 0 (2^24 - 1) 0);
(33%nat, mkAF 4096 CEIL_MAX 4); (35%nat, mkAF 4096 (CEIL_MAX + 2^24) 0) ].
Definition px1_atoms : list (nat * afact) := px0_atoms ++ [ (38%nat, mkAF 4096 CEIL_MAX 4); (36%nat, mkAF 4096 (CEIL_MAX + 2^26) 2);
(37%nat, mkAF 1 10000 0); (39%nat, mkAF 0 10000 0) ].
Definition px_cond_u : acond := mkAC BC_GEU (SOff 35%nat 0) (SOff 33%nat 0).
Definition px_cond_f : acond := mkAC BC_GEU (SOff 36%nat 0) (SOff 38%nat 0).
Definition px_alias_u : sv * sv := (SAlu ALU_ADD (SOff 33%nat 0) (SOff 27%nat 0), SOff 35%nat 0).
Definition px_alias_f : sv * sv := (SAlu ALU_ADD (SOff 38%nat 0) (SAlu ALU_SLL (SOff 27%nat 0) (SLit 2)), SOff 36%nat 0).
Definition ss_PX0 : sstate := mkSS PC_PX sr_atoms px0_smem None (mkFacts px0_atoms [px_cond_u] [px_alias_u]).
Definition ss_PX1 : sstate := mkSS PC_PX sr_atoms px1_smem None (mkFacts px1_atoms [px_cond_u; px_cond_f] [px_alias_u; px_alias_f]).
Definition ins_smem : smem :=
[ YQ0b.mkRegion (Some 23%nat) 0 3 0 0 [mkChunk 0 (CVal 1 (SOff 37%nat 0)); mkChunk 1 (CVal 1 (SOff 38%nat 0)); mkChunk 2 (CVal 1 (SOff 39%nat 0))] ;
YQ0b.mkRegion (Some 20%nat) 0 48 40 44 [mkChunk 0 (CVal 8 (SOff 32%nat 0)); mkChunk 8 (CVal 8 (SOff 45%nat 0)); mkChunk 16 (CVal 8 (SOff 33%nat 0));
mkChunk 24 (CVal 8 (SOff 34%nat 0)); mkChunk 32 (CVal 8 (SOff 35%nat 0)); mkChunk 40 (CVal 4 (SOff 36%nat 0))] ;
YQ0b.mkRegion (Some 40%nat) 0 3 0 3 [] ;
YQ0b.mkRegion (Some 41%nat) 0 3 0 3 [] ;
YQ0b.mkRegion (Some 42%nat) 0 1 0 1 [] ;
YQ0b.mkRegion (Some 43%nat) 0 4 0 4 [] ;
YQ0b.mkRegion (Some 44%nat) 0 4 0 4 [] ].
Definition ins_atoms : list (nat * afact) :=
[ (27%nat, mkAF 0 (2^24 - 1) 0); (10%nat, mkAF 0 (2^24 - 1) 0); (36%nat, mkAF 0 10000 0);
(37%nat, mkAF 0 255 0); (38%nat, mkAF 0 255 0); (39%nat, mkAF 0 255 0);
(32%nat, mkAF 4096 CEIL_MAX 4); (33%nat, mkAF 4096 CEIL_MAX 4); (34%nat, mkAF 4096 CEIL_MAX 4);
(35%nat, mkAF 4096 CEIL_MAX 4); (45%nat, mkAF 4096 CEIL_MAX 4);
(40%nat, mkAF 4096 (CEIL_MAX + 2^26) 0); (41%nat, mkAF 4096 (CEIL_MAX + 2^26) 0); (42%nat, mkAF 4096 (CEIL_MAX + 2^24) 0);
(43%nat, mkAF 4096 (CEIL_MAX + 2^26) 2); (44%nat, mkAF 4096 (CEIL_MAX + 2^26) 2) ].
Definition ins_cond : list acond :=
[ mkAC BC_GEU (SOff 40%nat 0) (SOff 45%nat 0); mkAC BC_GEU (SOff 41%nat 0) (SOff 34%nat 0); mkAC BC_GEU (SOff 42%nat 0) (SOff 33%nat 0);
mkAC BC_GEU (SOff 43%nat 0) (SOff 35%nat 0); mkAC BC_GEU (SOff 44%nat 0) (SOff 32%nat 0) ].
Definition ins_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SMd M_MUL (SOff 27%nat 0) (SLit 3)) (SOff 45%nat 0), SOff 40%nat 0);
(SAlu ALU_ADD (SMd M_MUL (SOff 36%nat 0) (SLit 3)) (SOff 34%nat 0), SOff 41%nat 0);
(SAlu ALU_ADD (SOff 33%nat 0) (SOff 10%nat 0), SOff 42%nat 0);
(SAlu ALU_ADD (SOff 35%nat 0) (SAlu ALU_SLL (SOff 10%nat 0) (SLit 2)), SOff 43%nat 0);
(SAlu ALU_ADD (SOff 32%nat 0) (SAlu ALU_SLL (SOff 10%nat 0) (SLit 2)), SOff 44%nat 0) ].
Definition ss_INS : sstate := mkSS PC_INS sr_atoms ins_smem None (mkFacts ins_atoms ins_cond ins_alias).
Section d.
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
Local Notation AT_RS := (at_RS API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation AT_HD := (at_HD API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation AT_PX := (at_PX API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation AT_INS := (at_INS API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation AT_RT := (at_RT API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation AT_INC := (at_INC API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation SEP_BLK := (sep_base_cht_blk API r g bef beffmt s N img fmt rest).
Local Notation WR_CHT := (wr_byte_cht API L A regs0 r g bef beffmt s N img fmt rest).
Local Notation HM_UPD := (hist_mem_update API regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay rest).
Local Notation RINV_MEM := (rgba_inv_mem API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest).
Section Px.
Variables (i ha : Z) (Lc : layout) (Ac : astate) (mdc : Model) (pnew fimg : Z) (imgl : list Z) (C : cht).
Hypothesis KRT : forall regs1 memc C', AT_RT regs1 Lc Ac memc mdc i ha pnew fimg imgl C' ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_RT) memc (seg_rom ubs2segs)) mdc) POST.
Hypothesis KINS : forall regs1 memc h, AT_INS regs1 Lc Ac memc mdc i ha pnew fimg imgl C h ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_INS) memc (seg_rom ubs2segs)) mdc) POST.
Theorem PX_stretch : forall js regs1 memc, AT_PX regs1 Lc Ac memc mdc i ha pnew fimg imgl C js ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_PX) memc (seg_rom ubs2segs)) mdc) POST.
Proof.
intros js regs1 memc HAT.
destruct HAT as (HINV & HREGS & Hfmt & Hi & Hha & Hop & Ejs & G27 & G23 & BR & S72 & HMEM).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbf & HB0).
destruct HREGS as (G2 & G3 & G4).
pose proof BR as (G20 & G9 & G8 & G21).
pose proof HMEM as (Hslots & S32 & S40 & S56 & S64 & S80 & S112 & S120 & Hfc & Hobj & Hcg & [Himg Hlen] & Hcht & EhS & EuS & ETS & Hz & Hpn & Hfi & HB).
pose proof Hcht as (Hobjc & (Af & Ah & Au & Ap & Ax) & Hinv & HT & Hch & _).
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity.
pose proof (ts_chain_ok _ Hch) as (RT1 & RT2 & RT3). unfold MAX_TABLE_SIZE in RT1.
pose proof Hinv as ((L1 & L2 & L3 & L4 & L5) & (C1 & C2 & C3) & (B1 & B2 & B3) & I4 & _). rewrite HT in L1, L2, L3, L4, L5, C1, B1.
set (T := ch_T C) in *. set (col := pxc fmt imgl i) in *. set (h0 := hash0 T col) in *.
set (h := cyc T h0 js) in *.
destruct (probe_end (ch_H C) (ch_ent C) Hinv col js Ejs) as (Hfs & Rh & Hcase). rewrite HT in Hfs, Rh, Hcase. fold h0 in Hfs, Rh, Hcase. fold h in Hfs, Rh, Hcase.
assert (Hjs0 : 0 <= js) by exact (find_off_ge0 (ch_H C) (ch_ent C) col js Hinv Ejs).
assert (Hjs_cnt : js <= ht_cnt (ch_H C)) by exact (find_off_le_cnt (ch_H C) (ch_ent C) Hinv col js Ejs).
assert (Hcnt_i : ht_cnt (ch_H C) <= i).
{ pose proof (zsum_ge_length (ch_ent C) (ent_freq_pos (ch_H C) (ch_ent C) Hinv)). lia. }
unfold RGB_NMAX in HNmax.
set (cnt := ht_cnt (ch_H C)) in *.
destruct (arr8_getz ubs2segs memc (ch_u C) (ht_used (ch_H C)) h Au ltac:(lia)) as [Bu _].
change (getz (ht_used (ch_H C)) h) with (usedz (ch_H C) h) in Bu.
destruct (arr32_getz ubs2segs memc (ch_f C) (ht_frequ (ch_H C)) h Af ltac:(lia)) as [Bf Rfq].
change (getz (ht_frequ (ch_H C)) h) with (freq (ch_H C) h) in Bf, Rfq.
set (fq := freq (ch_H C) h) in *.
pose proof (obj_at_nth ubs2segs memc (ch_c C) LAY_Cht _ 0 _ _ Hobjc eq_refl eq_refl) as [Bc0 _]. cbn [fst snd] in Bc0.
pose proof (obj_at_nth ubs2segs memc (ch_c C) LAY_Cht _ 2 _ _ Hobjc eq_refl eq_refl) as [Bc2 _]. cbn [fst snd] in Bc2. rewrite EuS in Bc2.
pose proof (obj_at_nth ubs2segs memc (ch_c C) LAY_Cht _ 5 _ _ Hobjc eq_refl eq_refl) as [Bc5 Rc5]. cbn [fst snd] in Bc5, Rc5.
change (N.to_nat 8) with 8%nat in Bc0, Bc2. change (N.to_nat 4) with 4%nat in Bc5. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Rc5.
rewrite Z.add_0_r in Bc0. change (ht_cnt (ch_H C)) with cnt in Bc5, Rc5.
assert (INB : forall b, In b (cht_blks C) -> In b (blocks Lc Ac)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. right. apply in_app_iff. right. exact Hb. }
assert (E0 : nth_error (cht_blks C) 0 = Some (ch_c C, CHT_SIZE)) by reflexivity.
assert (E1 : nth_error (cht_blks C) 1 = Some (ch_f C, 4 * T)) by reflexivity.
assert (E3 : nth_error (cht_blks C) 3 = Some (ch_u C, T)) by reflexivity.
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc (ch_c C) CHT_SIZE HHc (INB _ (nth_error_In _ _ E0)) ltac:(unfold CHT_SIZE; lia)) as (Rc0 & Rc1 & _).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc (ch_f C) (4 * T) HHc (INB _ (nth_error_In _ _ E1)) ltac:(lia)) as (Rf0 & Rf1 & Rf2).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc (ch_u C) T HHc (INB _ (nth_error_In _ _ E3)) ltac:(lia)) as (Ru0 & Ru1 & Ru2).
pose proof (mod4_add16 (ch_f C) h Rf2) as M36.
unfold CHT_SIZE in Rc1.
assert (HB' : Permutation (blocks Lc Ac) ((BASE0 ++ [(pnew, fmt * N); (fimg, N)]) ++ cht_blks C)) by (rewrite <- app_assoc; exact HB).
pose proof (cht_apart_of_perm API Lc Ac memc mdc _ C HHc HB') as CA.
set (vals := [fmt; ch_u C; 0; ch_u C + h; ch_f C + 4 * h; fq; ch_f C; cnt]).
set (E := Ereg regs1 (map (Z_to_bv 64) vals ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall jj v, nth_error vals jj = Some v -> ew E (32 + jj) = Z_to_bv 64 v)
by (intros jj v Hjv; subst E; apply Ereg_vals; exact Hjv).
assert (HE32 : ew E 32 = Z_to_bv 64 fmt) by exact (HV 0%nat _ eq_refl).
assert (HE33 : ew E 33 = Z_to_bv 64 (ch_u C)) by exact (HV 1%nat _ eq_refl).
assert (HE35 : ew E 35 = Z_to_bv 64 (ch_u C + h)) by exact (HV 3%nat _ eq_refl).
assert (HE36 : ew E 36 = Z_to_bv 64 (ch_f C + 4 * h)) by exact (HV 4%nat _ eq_refl).
assert (HE37 : ew E 37 = Z_to_bv 64 fq) by exact (HV 5%nat _ eq_refl).
assert (HE38 : ew E 38 = Z_to_bv 64 (ch_f C)) by exact (HV 6%nat _ eq_refl).
assert (HE39 : ew E 39 = Z_to_bv 64 cnt) by exact (HV 7%nat _ eq_refl).
assert (HU2 : bv_unsigned (ew E 2) = SP) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (HU35 : bv_unsigned (ew E 35) = ch_u C + h) by (rewrite HE35; apply unsigned_lit_small; lia).
assert (HU36 : bv_unsigned (ew E 36) = ch_f C + 4 * h) by (rewrite HE36; apply unsigned_lit_small; lia).
assert (HE20 : ew E 20 = Z_to_bv 64 (ch_c C)) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (HU20 : bv_unsigned (ew E 20) = ch_c C) by (rewrite HE20; apply unsigned_lit_small; lia).
assert (HE27 : ew E 27 = Z_to_bv 64 h) by (rewrite (HE 27%nat 27%bv eq_refl); exact G27).
assert (Rimg : 0 <= img < 2 ^ 64).
{ pose proof (obj_at_nth ubs2segs memc cfp LAY_RgbFrameConfig _ 0 _ _ Hcfp eq_refl eq_refl) as [_ X]. cbn [fst snd] in X. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in X. exact X. }
assert (Rha : 0 <= ha < 2 ^ 64) by (destruct Hha as [-> | [-> _]]; lia).
assert (Rfmt : 0 <= fmt < 2 ^ 64) by (destruct Hfmt as [-> | ->]; lia).
assert (RSTK : forall E', bv_unsigned (ew E' 2) = SP -> ew E' 32 = Z_to_bv 64 fmt -> region_ok ubs2segs E' memc px_stack).
{ intros E' H2 H32. unfold region_ok, px_stack; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite H2.
split; [unfold sp, sp0 in *; lia|]. split; [unfold sp, sp0 in *; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ fmt); [cbn [sv_denot]; rewrite Z.add_0_r, H32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. apply val_mem_word_mem. exact S40. }
assert (Hsp16 : SP mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (EA0 : env_agree 32 (Ereg regs1 []) E).
{ subst E. split; [intros n Hn; rewrite !ew_Ereg_lt by exact Hn; reflexivity | reflexivity]. }
destruct Hcase as [Hfree | (Hu1 & Hkey & _)].
-
rewrite Hfree in Bu.
assert (HS : st_ok ubs2segs E ss_PX0 (mkst regs1 (Z_to_bv 64 PC_PX) memc (seg_rom ubs2segs))).
{ unfold ss_PX0. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold px0_smem. constructor; [|constructor; [|constructor; [|constructor]]].
+ apply RSTK; assumption.
+ unfold region_ok; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU35. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ 0); [cbn [sv_denot]; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op]. rewrite Z.add_0_r. apply val_mem_byte; [exact Bu | lia].
+ unfold region_ok; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ (ch_u C)); [cbn [sv_denot]; rewrite Z.add_0_r, HE33, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact Bc2.
- unfold px0_smem, px_stack. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU35, HU20.
pose proof (cht_apart_blocks C 0 3 _ _ CA ltac:(lia) E0 E3) as A03. cbn [fst snd] in A03. unfold CHT_SIZE in A03.
unfold sp, sp0 in *. clear - HFv HRv Hceil Rh A03 Ru1 Rc1 Ru0 Rc0.
repeat match goal with |- _ /\ _ => split | |- True => exact I end; lia.
- unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [| split].
+ cbn [atoms_ok px0_atoms]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HE27, HE33, HE35.
unfold sp, sp0 in *. rewrite !unsigned_lit_small by lia.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
repeat match goal with |- _ /\ _ => split | |- True => exact I end; lia.
+ cbn [conds_ok]. unfold acond_ok, px_cond_u. cbn [ac_c ac_a ac_b]. rewrite !branch_geu_U.
rewrite (U_atom _ 35 _ HE35), (U_atom _ 33 _ HE33) by lia.
split; [apply Bool.negb_true_iff, Z.ltb_ge; lia | exact I].
+ cbn [alias_ok px_alias_u]. split; [|exact I].
apply U_inj. rewrite (U_atom _ 35 (ch_u C + h) HE35) by lia.
apply (U_add_atom _ 33 (ch_u C) _ h); [exact HE33 | lia | apply (U_atom _ 27 h HE27); lia | lia | lia]. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_PX) memc (seg_rom ubs2segs))) in HJ.
clearbody E. clear HV.
jrun_to LAWS ubs2tbl_ok HS HJ PC_INS. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (Hm0 : ms_mem ms = memc) by (apply functional_extensionality; intros x0; refine (frame_of_ro _ _ _ _ _ HF x0); reflexivity).
pose proof (regs_kept_of_st_ok ubs2segs E _ _ regs1 [] [2; 3; 4; 27; 23; 20; 9; 8; 21]%bv HS EA0 ltac:(vm_compute; reflexivity)) as GK.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc]. change (Z_to_bv 64 80124) with (Z_to_bv 64 PC_INS).
apply (KINS (ms_regs ms) (ms_mem ms) h). unfold at_INS. rewrite Hm0.
split; [exact HINV|].
split. { split; [rewrite (GK 2%bv ltac:(cbv; auto 20)); exact G2|]. split; [rewrite (GK 3%bv ltac:(cbv; auto 20)); exact G3 | rewrite (GK 4%bv ltac:(cbv; auto 20)); exact G4]. }
split; [exact Hfmt|]. split; [exact Hi|]. split; [exact Hha|]. split; [exact Hop|].
split; [exact Hfs|]. split; [exact Hfree|].
split; [eapply (getr_of_U ubs2segs); [exact HS|]; eval_sr_get; first [apply (U_atom E 27 h HE27); lia | apply U_zx; [apply (U_atom E 27 h HE27); lia | lia]]|].
split; [rewrite (GK 27%bv ltac:(cbv; auto 20)); exact G27|].
split; [eapply (getr_of_U ubs2segs); [exact HS|]; eval_sr_get; apply (U_atom E 32 fmt HE32); lia|].
split; [rewrite (GK 23%bv ltac:(cbv; auto 20)); exact G23|].
split. { unfold body_regs. rewrite (GK 20%bv ltac:(cbv; auto 20)), (GK 9%bv ltac:(cbv; auto 20)), (GK 8%bv ltac:(cbv; auto 20)), (GK 21%bv ltac:(cbv; auto 20)). exact BR. }
split; [exact S72|].
exact HMEM.
-
rewrite Hu1 in Bu.
assert (Hsl : in_slot (ch_H C) h) by (split; [rewrite HT; exact Rh | rewrite Hu1; discriminate]).
destruct (I4 h Hsl) as (Rci & Hnth & Fq1).
pose proof (zsum_pos_le (ch_ent C) _ _ _ (ent_freq_pos (ch_H C) (ch_ent C) Hinv) Hnth) as Fq2.
change (freq (ch_H C) h) with fq in Fq1, Fq2, Hnth.
assert (HS : st_ok ubs2segs E ss_PX1 (mkst regs1 (Z_to_bv 64 PC_PX) memc (seg_rom ubs2segs))).
{ unfold ss_PX1. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold px1_smem. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
+ apply RSTK; assumption.
+ unfold region_ok; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU35. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ 1); [cbn [sv_denot]; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op]. rewrite Z.add_0_r. apply val_mem_byte; [exact Bu | lia].
+ unfold region_ok; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU36. split; [lia|]. split; [lia|].
split; [intros o Ho; apply (present_writable ubs2_msyms); replace (ch_f C + 4 * h + o) with (ch_f C + (4 * h + o)) by lia; apply (proj1 (heap_blocks ubs2_msyms MR LAWS Lc Ac memc mdc (ch_f C) (4 * T) (4 * h + o) HHc (INB _ (nth_error_In _ _ E1)) ltac:(lia))) |].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ fq); [cbn [sv_denot]; rewrite Z.add_0_r, HE37, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite Z.add_0_r. exact Bf.
+ unfold region_ok; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
* eapply (chunk_ok_val _ _ _ _ _ _ _ (ch_f C)); [cbn [sv_denot]; rewrite Z.add_0_r, HE38, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite Z.add_0_r. exact Bc0.
* eapply (chunk_ok_val _ _ _ _ _ _ _ (ch_u C)); [cbn [sv_denot]; rewrite Z.add_0_r, HE33, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact Bc2.
* eapply (chunk_ok_val _ _ _ _ _ _ _ cnt); [cbn [sv_denot]; rewrite Z.add_0_r, HE39, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact Bc5.
- unfold px1_smem, px_stack. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU35, HU36, HU20.
pose proof (cht_apart_blocks C 0 1 _ _ CA ltac:(lia) E0 E1) as A01. pose proof (cht_apart_blocks C 0 3 _ _ CA ltac:(lia) E0 E3) as A03.
pose proof (cht_apart_blocks C 1 3 _ _ CA ltac:(lia) E1 E3) as A13. cbn [fst snd] in A01, A03, A13. unfold CHT_SIZE in A01, A03.
unfold sp, sp0 in *. clear - HFv HRv Hceil Rh A01 A03 A13 Ru1 Rf1 Rc1 Ru0 Rf0 Rc0.
repeat match goal with |- _ /\ _ => split | |- True => exact I end; lia.
- unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [| split].
+ cbn [atoms_ok px1_atoms px0_atoms app]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HE27, HE33, HE35, HE38, HE36, HE37, HE39.
unfold sp, sp0 in *. rewrite !unsigned_lit_small by lia.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
repeat match goal with |- _ /\ _ => split | |- True => exact I end; lia.
+ cbn [conds_ok]. unfold acond_ok, px_cond_u, px_cond_f. cbn [ac_c ac_a ac_b]. rewrite !branch_geu_U.
rewrite (U_atom _ 35 _ HE35), (U_atom _ 33 _ HE33), (U_atom _ 36 _ HE36), (U_atom _ 38 _ HE38) by lia.
repeat match goal with |- _ /\ _ => split | |- True => exact I end; apply Bool.negb_true_iff, Z.ltb_ge; lia.
+ cbn [alias_ok px_alias_u px_alias_f]. split; [|split; [|exact I]].
* apply U_inj. rewrite (U_atom _ 35 (ch_u C + h) HE35) by lia.
apply (U_add_atom _ 33 (ch_u C) _ h); [exact HE33 | lia | apply (U_atom _ 27 h HE27); lia | lia | lia].
* apply U_inj. rewrite (U_atom _ 36 (ch_f C + 4 * h) HE36) by lia.
apply (U_add_sll2' _ 27 38 h (ch_f C)); [exact HE27 | lia | exact HE38 | lia | lia]. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_PX) memc (seg_rom ubs2segs))) in HJ.
clearbody E. clear HV.
assert (WRC : forall a, ch_f C + 4 * h <= a < ch_f C + 4 * h + 4 -> wr_byte RGBA_STK (sp0 regs0) (FPfoot r g bef beffmt s N) (blocks L A) (blocks Lc Ac) a).
{ intros a Ha. apply (WR_CHT Lc Ac memc mdc pnew fimg C a HHc HB HB0 Hch). exists (ch_f C, 4 * T). split; [exact (nth_error_In _ _ E1) | cbn; lia]. }
jrun_to LAWS ubs2tbl_ok HS HJ PC_RT.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_gen; [reflexivity | exact HU36 | cbn [r_wlo r_whi]; intros a Ha; apply WRC; lia |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (ch_f C + 4 * h <= a < ch_f C + 4 * h + 4) -> mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs memc a).
{ intros a Ha Hna. mb_frame_g HF; [reflexivity | lia | lia | rewrite HU36; lia | lia]. }
assert (NEWF : val_mem ubs2segs (ms_mem ms) (ch_f C + 4 * h) 4 (fq + 1)).
{ replace (ch_f C + 4 * h) with (ch_f C + 4 * h + 0) by lia.
apply (st_chunk_val_g _ _ _ 2%nat _ 36%nat 0 4%N (SOff 37 1) _ _ HS eq_refl eq_refl ltac:(left; reflexivity)); [exact HU36 | | cbn; lia | cbn; lia].
cbn [sv_denot]. rewrite HE37, unsigned_lit_small by lia. reflexivity. }
pose proof (regs_kept_of_st_ok ubs2segs E _ _ regs1 [] [2; 3; 4; 20; 9; 8; 21]%bv HS EA0 ltac:(vm_compute; reflexivity)) as GK.
assert (KEEPc : forall a, in_cht C a -> ~ (ch_f C + 4 * h <= a < ch_f C + 4 * h + 4) -> mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs memc a).
{ intros a Hca Hna. pose proof (cht_low API r g bef beffmt s N img fmt rest Lc Ac memc mdc pnew fimg C a HHc HB Hca). apply KEEP2; [lia | exact Hna]. }
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc]. change (Z_to_bv 64 80476) with (Z_to_bv 64 PC_RT).
apply (KRT (ms_regs ms) (ms_mem ms) (C_hit C h)). unfold at_RT.
split. { apply (RINV_MEM Lc Ac memc _ mdc HINV HJ). intros a Ha Hna. apply KEEP2; [lia | unfold sp, sp0 in *; lia]. }
split. { split; [rewrite (GK 2%bv ltac:(cbv; auto 20)); exact G2|]. split; [rewrite (GK 3%bv ltac:(cbv; auto 20)); exact G3 | rewrite (GK 4%bv ltac:(cbv; auto 20)); exact G4]. }
split; [exact Hfmt|]. split; [exact Hi|]. split; [exact Hha|].
split; [eapply (getr_of_U ubs2segs); [exact HS|]; eval_sr_get; apply (U_atom E 32 fmt HE32); lia|].
split. { unfold body_regs. cbn [ch_c C_hit]. rewrite (GK 20%bv ltac:(cbv; auto 20)), (GK 9%bv ltac:(cbv; auto 20)), (GK 8%bv ltac:(cbv; auto 20)), (GK 21%bv ltac:(cbv; auto 20)). exact BR. }
split. { unfold slot in *. apply (val_mem_kept8 memc); [exact S72|]. intros k Hk. apply KEEP2; unfold sp, sp0, SL_72 in *; lia. }
apply (HM_UPD Lc Ac memc mdc (ms_mem ms) pnew fimg imgl C (C_hit C h) i (i + 1) HHc); [unfold sp, sp0 in *; lia | unfold sp, sp0 in *; lia | exact Hfmt | exact HMEM | | | reflexivity | reflexivity | exact EhS | exact EuS | exact ETS |].
+ intros a Ha Hnc _. apply KEEP2; [exact Ha|]. intros Hin. apply Hnc. exists (ch_f C, 4 * T). split; [exact (nth_error_In _ _ E1) | cbn; lia].
+ apply (cht_ok_hit memc (ms_mem ms) C h Hcht CA Hsl); [subst fq; lia | exact NEWF | exact KEEPc].
+ cbn [ch_ent C_hit]. rewrite (zsum_lset_snd (ch_ent C) _ _ _ (freq (ch_H C) h + 1) Hnth). subst fq. lia.
Qed.
End Px.
Section e.
Variables (i ha : Z) (Lc : layout) (Ac : astate) (mdc : Model) (pnew fimg : Z) (imgl : list Z) (C : cht).
Hypothesis KRT : forall regs1 memc C', AT_RT regs1 Lc Ac memc mdc i ha pnew fimg imgl C' ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_RT) memc (seg_rom ubs2segs)) mdc) POST.
Theorem INS_stretch : forall regs1 memc h, AT_INS regs1 Lc Ac memc mdc i ha pnew fimg imgl C h ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_INS) memc (seg_rom ubs2segs)) mdc) POST.
Proof.
intros regs1 memc h HAT.
destruct HAT as (HINV & HREGS & Hfmt & Hi & Hha & Hop & Hfs & Hz0 & G10 & G27 & G18 & G23 & BR & S72 & HMEM).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbf & HB0).
destruct HREGS as (G2 & G3 & G4).
pose proof BR as (G20 & G9 & G8 & G21).
pose proof HMEM as (Hslots & S32 & S40 & S56 & S64 & S80 & S112 & S120 & Hfc & Hobj & Hcg & [Himg Hlen] & Hcht & EhS & EuS & ETS & Hz & Hpn & Hfi & HB).
pose proof Hcht as (Hobjc & (Af & Ah & Au & Ap & Ax) & Hinv & HT & Hch & _).
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity.
pose proof (ts_chain_ok _ Hch) as (RT1 & RT2 & RT3). unfold MAX_TABLE_SIZE in RT1.
pose proof Hinv as ((L1 & L2 & L3 & L4 & L5) & (C1 & C2 & C3) & (B1 & B2 & B3) & I4 & _). rewrite HT in L1, L2, L3, L4, L5, C1, B1.
set (T := ch_T C) in *. set (col := pxc fmt imgl i) in *. set (cnt := ht_cnt (ch_H C)) in *.
pose proof (find_slot_range (ch_H C) (ch_ent C) Hinv col h Hfs) as Rh. rewrite HT in Rh.
assert (Hcnt_i : cnt <= i).
{ pose proof (zsum_ge_length (ch_ent C) (ent_freq_pos (ch_H C) (ch_ent C) Hinv)). subst cnt. lia. }
unfold RGB_NMAX in HNmax.
assert (Hroom : cnt + 1 < T) by lia.
assert (Hyimg : In (img, fmt * N) (BASE0 ++ [(pnew, fmt * N); (fimg, N)])).
{ apply in_app_iff. left. unfold BASE. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
unfold img_block, fmt_okb. destruct Hfmt as [-> | ->]; left; reflexivity. }
assert (Himgb : In (img, fmt * N) (blocks Lc Ac)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB|]. rewrite app_assoc. apply in_app_iff. left. exact Hyimg. }
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc img (fmt * N) HHc Himgb ltac:(lia)) as (Ri0 & Ri1 & _).
set (pix := img + fmt * i) in *.
assert (PX1 : 0 <= fmt * i) by nia. assert (PX2 : fmt * i + fmt <= fmt * N) by nia.
assert (PB : forall k, 0 <= k < 3 -> mbyte ubs2segs memc (pix + k) = Some (Z_to_bv 8 (getz imgl (fmt * i + k))) /\ 0 <= getz imgl (fmt * i + k) < 256).
{ intros k Hk. subst pix. rewrite <- Z.add_assoc. apply (arr8_getz ubs2segs memc img imgl); [exact Himg | clear - Hk PX1 PX2 Hfmt Hlen; nia]. }
pose proof (PB 0 ltac:(lia)) as [P0 R0]. pose proof (PB 1 ltac:(lia)) as [P1 R1]. pose proof (PB 2 ltac:(lia)) as [P2 R2]. rewrite !Z.add_0_r in P0. rewrite !Z.add_0_r in R0.
assert (Hcol : colour_ok col) by (subst col; unfold pxc, colour_ok, cR, cG, cB, mkcol; cbn [fst snd]; lia).
pose proof (obj_at_nth ubs2segs memc (ch_c C) LAY_Cht _ 0 _ _ Hobjc eq_refl eq_refl) as [Bc0 _]. cbn [fst snd] in Bc0.
pose proof (obj_at_nth ubs2segs memc (ch_c C) LAY_Cht _ 1 _ _ Hobjc eq_refl eq_refl) as [Bc1 _]. cbn [fst snd] in Bc1. rewrite EhS in Bc1.
pose proof (obj_at_nth ubs2segs memc (ch_c C) LAY_Cht _ 2 _ _ Hobjc eq_refl eq_refl) as [Bc2 _]. cbn [fst snd] in Bc2. rewrite EuS in Bc2.
pose proof (obj_at_nth ubs2segs memc (ch_c C) LAY_Cht _ 3 _ _ Hobjc eq_refl eq_refl) as [Bc3 _]. cbn [fst snd] in Bc3.
pose proof (obj_at_nth ubs2segs memc (ch_c C) LAY_Cht _ 4 _ _ Hobjc eq_refl eq_refl) as [Bc4 _]. cbn [fst snd] in Bc4.
pose proof (obj_at_nth ubs2segs memc (ch_c C) LAY_Cht _ 5 _ _ Hobjc eq_refl eq_refl) as [Bc5 Rc5]. cbn [fst snd] in Bc5, Rc5.
change (N.to_nat 8) with 8%nat in Bc0, Bc1, Bc2, Bc3, Bc4. change (N.to_nat 4) with 4%nat in Bc5. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Rc5.
rewrite Z.add_0_r in Bc0. change (ht_cnt (ch_H C)) with cnt in Bc5, Rc5.
assert (INB : forall b, In b (cht_blks C) -> In b (blocks Lc Ac)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. right. apply in_app_iff. right. exact Hb. }
assert (E0 : nth_error (cht_blks C) 0 = Some (ch_c C, CHT_SIZE)) by reflexivity.
assert (E1 : nth_error (cht_blks C) 1 = Some (ch_f C, 4 * T)) by reflexivity.
assert (E2 : nth_error (cht_blks C) 2 = Some (ch_h C, 3 * T)) by reflexivity.
assert (E3 : nth_error (cht_blks C) 3 = Some (ch_u C, T)) by reflexivity.
assert (E4 : nth_error (cht_blks C) 4 = Some (ch_p C, 3 * T)) by reflexivity.
assert (E5 : nth_error (cht_blks C) 5 = Some (ch_x C, 4 * T)) by reflexivity.
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc (ch_c C) CHT_SIZE HHc (INB _ (nth_error_In _ _ E0)) ltac:(unfold CHT_SIZE; lia)) as (Rc0 & Rc1 & _).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc (ch_f C) (4 * T) HHc (INB _ (nth_error_In _ _ E1)) ltac:(lia)) as (Rf0 & Rf1 & Rf2).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc (ch_h C) (3 * T) HHc (INB _ (nth_error_In _ _ E2)) ltac:(lia)) as (Rk0 & Rk1 & Rk2).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc (ch_u C) T HHc (INB _ (nth_error_In _ _ E3)) ltac:(lia)) as (Ru0 & Ru1 & Ru2).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc (ch_p C) (3 * T) HHc (INB _ (nth_error_In _ _ E4)) ltac:(lia)) as (Rp0 & Rp1 & Rp2).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc (ch_x C) (4 * T) HHc (INB _ (nth_error_In _ _ E5)) ltac:(lia)) as (Rx0 & Rx1 & Rx2).
unfold CHT_SIZE in Rc1.
pose proof (mod4_add16 (ch_x C) h Rx2) as M43. pose proof (mod4_add16 (ch_f C) h Rf2) as M44.
assert (HB' : Permutation (blocks Lc Ac) ((BASE0 ++ [(pnew, fmt * N); (fimg, N)]) ++ cht_blks C)) by (rewrite <- app_assoc; exact HB).
pose proof (cht_apart_of_perm API Lc Ac memc mdc _ C HHc HB') as CA.
assert (WRC : forall a, ins_w C h a -> in_cht C a).
{ intros a Ha. unfold ins_w in Ha. change (ht_cnt (ch_H C)) with cnt in Ha.
destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]].
- exists (ch_h C, 3 * T). split; [exact (nth_error_In _ _ E2) | cbn; lia].
- exists (ch_p C, 3 * T). split; [exact (nth_error_In _ _ E4) | cbn; lia].
- exists (ch_u C, T). split; [exact (nth_error_In _ _ E3) | cbn; lia].
- exists (ch_x C, 4 * T). split; [exact (nth_error_In _ _ E5) | cbn; lia].
- exists (ch_f C, 4 * T). split; [exact (nth_error_In _ _ E1) | cbn; lia].
- exists (ch_c C, CHT_SIZE). split; [exact (nth_error_In _ _ E0) | cbn; unfold CHT_SIZE; lia]. }
set (cR_ := getz imgl (fmt * i)) in *. set (cG_ := getz imgl (fmt * i + 1)) in *. set (cB_ := getz imgl (fmt * i + 2)) in *.
set (E := Ereg regs1 (map (Z_to_bv 64) [ch_f C; ch_u C; ch_p C; ch_x C; cnt; cR_; cG_; cB_; ch_h C + 3 * h; ch_p C + 3 * cnt; ch_u C + h; ch_x C + 4 * h; ch_f C + 4 * h; ch_h C] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall jj v, nth_error [ch_f C; ch_u C; ch_p C; ch_x C; cnt; cR_; cG_; cB_; ch_h C + 3 * h; ch_p C + 3 * cnt; ch_u C + h; ch_x C + 4 * h; ch_f C + 4 * h; ch_h C] jj = Some v -> ew E (32 + jj) = Z_to_bv 64 v)
by (intros jj v Hjv; subst E; apply Ereg_vals; exact Hjv).
assert (HE32 : ew E 32 = Z_to_bv 64 (ch_f C)) by exact (HV 0%nat _ eq_refl).
assert (HE33 : ew E 33 = Z_to_bv 64 (ch_u C)) by exact (HV 1%nat _ eq_refl).
assert (HE34 : ew E 34 = Z_to_bv 64 (ch_p C)) by exact (HV 2%nat _ eq_refl).
assert (HE35 : ew E 35 = Z_to_bv 64 (ch_x C)) by exact (HV 3%nat _ eq_refl).
assert (HE36 : ew E 36 = Z_to_bv 64 cnt) by exact (HV 4%nat _ eq_refl).
assert (HE37 : ew E 37 = Z_to_bv 64 cR_) by exact (HV 5%nat _ eq_refl).
assert (HE38 : ew E 38 = Z_to_bv 64 cG_) by exact (HV 6%nat _ eq_refl).
assert (HE39 : ew E 39 = Z_to_bv 64 cB_) by exact (HV 7%nat _ eq_refl).
assert (HE40 : ew E 40 = Z_to_bv 64 (ch_h C + 3 * h)) by exact (HV 8%nat _ eq_refl).
assert (HE41 : ew E 41 = Z_to_bv 64 (ch_p C + 3 * cnt)) by exact (HV 9%nat _ eq_refl).
assert (HE42 : ew E 42 = Z_to_bv 64 (ch_u C + h)) by exact (HV 10%nat _ eq_refl).
assert (HE43 : ew E 43 = Z_to_bv 64 (ch_x C + 4 * h)) by exact (HV 11%nat _ eq_refl).
assert (HE44 : ew E 44 = Z_to_bv 64 (ch_f C + 4 * h)) by exact (HV 12%nat _ eq_refl).
assert (HE45 : ew E 45 = Z_to_bv 64 (ch_h C)) by exact (HV 13%nat _ eq_refl).
assert (HE27 : ew E 27 = Z_to_bv 64 h) by (rewrite (HE 27%nat 27%bv eq_refl); exact G27).
assert (HE10 : ew E 10 = Z_to_bv 64 h) by (rewrite (HE 10%nat 10%bv eq_refl); exact G10).
assert (HE23 : ew E 23 = Z_to_bv 64 pix) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (HE20 : ew E 20 = Z_to_bv 64 (ch_c C)) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (HU23 : bv_unsigned (ew E 23) = pix) by (rewrite HE23; apply unsigned_lit_small; subst pix; lia).
assert (HU20 : bv_unsigned (ew E 20) = ch_c C) by (rewrite HE20; apply unsigned_lit_small; lia).
assert (HU40 : bv_unsigned (ew E 40) = ch_h C + 3 * h) by (rewrite HE40; apply unsigned_lit_small; lia).
assert (HU41 : bv_unsigned (ew E 41) = ch_p C + 3 * cnt) by (rewrite HE41; apply unsigned_lit_small; lia).
assert (HU42 : bv_unsigned (ew E 42) = ch_u C + h) by (rewrite HE42; apply unsigned_lit_small; lia).
assert (HU43 : bv_unsigned (ew E 43) = ch_x C + 4 * h) by (rewrite HE43; apply unsigned_lit_small; lia).
assert (HU44 : bv_unsigned (ew E 44) = ch_f C + 4 * h) by (rewrite HE44; apply unsigned_lit_small; lia).
assert (WRT : forall a, in_cht C a -> writable_at ubs2segs memc a).
{ intros a ([b n] & Hb & Ha). cbn [fst snd] in Ha. apply (present_writable ubs2_msyms). replace a with (b + (a - b)) by lia.
apply (proj1 (heap_blocks ubs2_msyms MR LAWS Lc Ac memc mdc b n (a - b) HHc (INB _ Hb) ltac:(lia))). }
assert (HS : st_ok ubs2segs E ss_INS (mkst regs1 (Z_to_bv 64 PC_INS) memc (seg_rom ubs2segs))).
{ unfold ss_INS. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold ins_smem. constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]]];
unfold region_ok; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
+ rewrite HU23. split; [subst pix; lia|]. split; [subst pix; lia|]. split; [intros o Ho; lia|].
assert (CK : forall k n v, 0 <= k < 3 -> ew (Ereg regs1 (map (Z_to_bv 64) [ch_f C; ch_u C; ch_p C; ch_x C; cnt; cR_; cG_; cB_; ch_h C + 3 * h; ch_p C + 3 * cnt; ch_u C + h; ch_x C + 4 * h; ch_f C + 4 * h; ch_h C] ++ [])) n = Z_to_bv 64 v ->
mbyte ubs2segs memc (pix + k) = Some (Z_to_bv 8 v) -> 0 <= v < 256 ->
chunk_ok ubs2segs (Ereg regs1 (map (Z_to_bv 64) [ch_f C; ch_u C; ch_p C; ch_x C; cnt; cR_; cG_; cB_; ch_h C + 3 * h; ch_p C + 3 * cnt; ch_u C + h; ch_x C + 4 * h; ch_f C + 4 * h; ch_h C] ++ [])) memc pix (mkChunk k (CVal 1 (SOff n 0)))).
{ intros k n v Hk Hn Hb Hv. eapply (chunk_ok_val _ _ _ _ _ _ _ v); [cbn [sv_denot]; rewrite Z.add_0_r, Hn, unsigned_lit_small by lia; reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; exact Hv | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op]. apply val_mem_byte; [exact Hb | exact Hv]. }
apply Forall_cons; [apply (CK 0 37%nat cR_); [lia | exact HE37 | rewrite Z.add_0_r; exact P0 | exact R0]|].
apply Forall_cons; [apply (CK 1 38%nat cG_); [lia | exact HE38 | exact P1 | exact R1]|].
apply Forall_cons; [apply (CK 2 39%nat cB_); [lia | exact HE39 | exact P2 | exact R2]|]. apply Forall_nil.
+ rewrite HU20. split; [lia|]. split; [lia|].
split; [intros o Ho; apply WRT; exists (ch_c C, CHT_SIZE); split; [exact (nth_error_In _ _ E0) | cbn; unfold CHT_SIZE; lia]|].
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (ch_f C)); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite Z.add_0_r. exact Bc0. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (ch_h C)); [cbn [sv_denot]; rewrite Z.add_0_r, HE45, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact Bc1. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (ch_u C)); [cbn [sv_denot]; rewrite Z.add_0_r, HE33, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact Bc2. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (ch_p C)); [cbn [sv_denot]; rewrite Z.add_0_r, HE34, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact Bc3. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (ch_x C)); [cbn [sv_denot]; rewrite Z.add_0_r, HE35, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact Bc4. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ cnt); [cbn [sv_denot]; rewrite Z.add_0_r, HE36, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact Bc5. }
apply Forall_nil.
+ rewrite HU40. split; [lia|]. split; [lia|]. split; [| apply Forall_nil].
intros o Ho. apply WRT. exists (ch_h C, 3 * T). split; [exact (nth_error_In _ _ E2) | cbn; lia].
+ rewrite HU41. split; [lia|]. split; [lia|]. split; [| apply Forall_nil].
intros o Ho. apply WRT. exists (ch_p C, 3 * T). split; [exact (nth_error_In _ _ E4) | cbn; lia].
+ rewrite HU42. split; [lia|]. split; [lia|]. split; [| apply Forall_nil].
intros o Ho. apply WRT. exists (ch_u C, T). split; [exact (nth_error_In _ _ E3) | cbn; lia].
+ rewrite HU43. split; [lia|]. split; [lia|]. split; [| apply Forall_nil].
intros o Ho. apply WRT. exists (ch_x C, 4 * T). split; [exact (nth_error_In _ _ E5) | cbn; lia].
+ rewrite HU44. split; [lia|]. split; [lia|]. split; [| apply Forall_nil].
intros o Ho. apply WRT. exists (ch_f C, 4 * T). split; [exact (nth_error_In _ _ E1) | cbn; lia].
- unfold ins_smem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU23, HU20, HU40, HU41, HU42, HU43, HU44.
repeat match goal with |- _ /\ _ => split | |- True => exact I end.
{ pose proof (SEP_BLK Lc Ac memc mdc pnew fimg C (img, fmt * N) (ch_c C, CHT_SIZE) HHc HB Hyimg (nth_error_In _ _ E0)) as F; cbn [fst snd] in F; unfold CHT_SIZE in F.
subst pix. clear - F PX1 PX2 Hfmt Rh Hroom C1. lia. }
{ pose proof (SEP_BLK Lc Ac memc mdc pnew fimg C (img, fmt * N) (ch_h C, 3 * T) HHc HB Hyimg (nth_error_In _ _ E2)) as F; cbn [fst snd] in F; unfold CHT_SIZE in F.
subst pix. clear - F PX1 PX2 Hfmt Rh Hroom C1. lia. }
{ pose proof (SEP_BLK Lc Ac memc mdc pnew fimg C (img, fmt * N) (ch_p C, 3 * T) HHc HB Hyimg (nth_error_In _ _ E4)) as F; cbn [fst snd] in F; unfold CHT_SIZE in F.
subst pix. clear - F PX1 PX2 Hfmt Rh Hroom C1. lia. }
{ pose proof (SEP_BLK Lc Ac memc mdc pnew fimg C (img, fmt * N) (ch_u C, T) HHc HB Hyimg (nth_error_In _ _ E3)) as F; cbn [fst snd] in F; unfold CHT_SIZE in F.
subst pix. clear - F PX1 PX2 Hfmt Rh Hroom C1. lia. }
{ pose proof (SEP_BLK Lc Ac memc mdc pnew fimg C (img, fmt * N) (ch_x C, 4 * T) HHc HB Hyimg (nth_error_In _ _ E5)) as F; cbn [fst snd] in F; unfold CHT_SIZE in F.
subst pix. clear - F PX1 PX2 Hfmt Rh Hroom C1. lia. }
{ pose proof (SEP_BLK Lc Ac memc mdc pnew fimg C (img, fmt * N) (ch_f C, 4 * T) HHc HB Hyimg (nth_error_In _ _ E1)) as F; cbn [fst snd] in F; unfold CHT_SIZE in F.
subst pix. clear - F PX1 PX2 Hfmt Rh Hroom C1. lia. }
{ pose proof (cht_apart_blocks C 0 2 _ _ CA ltac:(lia) E0 E2) as F; cbn [fst snd] in F; unfold CHT_SIZE in F.
clear - F Rh Hroom C1. lia. }
{ pose proof (cht_apart_blocks C 0 4 _ _ CA ltac:(lia) E0 E4) as F; cbn [fst snd] in F; unfold CHT_SIZE in F.
clear - F Rh Hroom C1. lia. }
{ pose proof (cht_apart_blocks C 0 3 _ _ CA ltac:(lia) E0 E3) as F; cbn [fst snd] in F; unfold CHT_SIZE in F.
clear - F Rh Hroom C1. lia. }
{ pose proof (cht_apart_blocks C 0 5 _ _ CA ltac:(lia) E0 E5) as F; cbn [fst snd] in F; unfold CHT_SIZE in F.
clear - F Rh Hroom C1. lia. }
{ pose proof (cht_apart_blocks C 0 1 _ _ CA ltac:(lia) E0 E1) as F; cbn [fst snd] in F; unfold CHT_SIZE in F.
clear - F Rh Hroom C1. lia. }
{ pose proof (cht_apart_blocks C 2 4 _ _ CA ltac:(lia) E2 E4) as F; cbn [fst snd] in F; unfold CHT_SIZE in F.
clear - F Rh Hroom C1. lia. }
{ pose proof (cht_apart_blocks C 2 3 _ _ CA ltac:(lia) E2 E3) as F; cbn [fst snd] in F; unfold CHT_SIZE in F.
clear - F Rh Hroom C1. lia. }
{ pose proof (cht_apart_blocks C 2 5 _ _ CA ltac:(lia) E2 E5) as F; cbn [fst snd] in F; unfold CHT_SIZE in F.
clear - F Rh Hroom C1. lia. }
{ pose proof (cht_apart_blocks C 1 2 _ _ CA ltac:(lia) E1 E2) as F; cbn [fst snd] in F; unfold CHT_SIZE in F.
clear - F Rh Hroom C1. lia. }
{ pose proof (cht_apart_blocks C 3 4 _ _ CA ltac:(lia) E3 E4) as F; cbn [fst snd] in F; unfold CHT_SIZE in F.
clear - F Rh Hroom C1. lia. }
{ pose proof (cht_apart_blocks C 4 5 _ _ CA ltac:(lia) E4 E5) as F; cbn [fst snd] in F; unfold CHT_SIZE in F.
clear - F Rh Hroom C1. lia. }
{ pose proof (cht_apart_blocks C 1 4 _ _ CA ltac:(lia) E1 E4) as F; cbn [fst snd] in F; unfold CHT_SIZE in F.
clear - F Rh Hroom C1. lia. }
{ pose proof (cht_apart_blocks C 3 5 _ _ CA ltac:(lia) E3 E5) as F; cbn [fst snd] in F; unfold CHT_SIZE in F.
clear - F Rh Hroom C1. lia. }
{ pose proof (cht_apart_blocks C 1 3 _ _ CA ltac:(lia) E1 E3) as F; cbn [fst snd] in F; unfold CHT_SIZE in F.
clear - F Rh Hroom C1. lia. }
{ pose proof (cht_apart_blocks C 1 5 _ _ CA ltac:(lia) E1 E5) as F; cbn [fst snd] in F; unfold CHT_SIZE in F.
clear - F Rh Hroom C1. lia. }
- unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [| split].
+ cbn [atoms_ok ins_atoms]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (ew_Ereg_nat regs1 _ 27 27%bv eq_refl), G27, (ew_Ereg_nat regs1 _ 10 10%bv eq_refl), G10, HE36, HE37, HE38, HE39,
HE32, HE33, HE34, HE35, HE45, HE40, HE41, HE42, HE43, HE44.
rewrite !unsigned_lit_small by lia.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
try pose proof (proj1 alloc_ceiling_val) as HacR; clear - HacR Rh RT1 Hcnt_i Hi HNmax R0 R1 R2 C1 Hroom Rf0 Rf1 Rf2 Rk0 Rk1 Rk2 Ru0 Ru1 Ru2 Rp0 Rp1 Rp2 Rx0 Rx1 Rx2 M43 M44.
repeat match goal with |- _ /\ _ => split | |- True => exact I end; lia.
+ cbn [conds_ok ins_cond]. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite !branch_geu_U.
rewrite (U_atom _ 40 _ HE40), (U_atom _ 45 _ HE45), (U_atom _ 41 _ HE41), (U_atom _ 34 _ HE34), (U_atom _ 42 _ HE42),
(U_atom _ 33 _ HE33), (U_atom _ 43 _ HE43), (U_atom _ 35 _ HE35), (U_atom _ 44 _ HE44), (U_atom _ 32 _ HE32) by lia.
repeat match goal with |- _ /\ _ => split | |- True => exact I end; apply Bool.negb_true_iff, Z.ltb_ge; lia.
+ cbn [alias_ok ins_alias]. split; [|split; [|split; [|split; [|split; [|exact I]]]]].
* apply U_inj. rewrite (U_atom _ 40 (ch_h C + 3 * h) HE40) by lia. apply (U_mul3_add' _ 27 45 h (ch_h C)); [exact HE27 | lia | exact HE45 | lia | lia].
* apply U_inj. rewrite (U_atom _ 41 (ch_p C + 3 * cnt) HE41) by lia. apply (U_mul3_add' _ 36 34 cnt (ch_p C)); [exact HE36 | lia | exact HE34 | lia | lia].
* apply U_inj. rewrite (U_atom _ 42 (ch_u C + h) HE42) by lia. apply (U_add_atom _ 33 (ch_u C) _ h); [exact HE33 | lia | apply (U_atom _ 10 h HE10); lia | lia | lia].
* apply U_inj. rewrite (U_atom _ 43 (ch_x C + 4 * h) HE43) by lia. apply (U_add_sll2' _ 10 35 h (ch_x C)); [exact HE10 | lia | exact HE35 | lia | lia].
* apply U_inj. rewrite (U_atom _ 44 (ch_f C + 4 * h) HE44) by lia. apply (U_add_sll2' _ 10 32 h (ch_f C)); [exact HE10 | lia | exact HE32 | lia | lia]. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_INS) memc (seg_rom ubs2segs))) in HJ.
assert (EA0 : env_agree 32 (Ereg regs1 []) E).
{ subst E. split; [intros n Hn; rewrite !ew_Ereg_lt by exact Hn; reflexivity | reflexivity]. }
clearbody E. clear HV.
assert (WRI : forall a, ins_w C h a -> wr_byte RGBA_STK (sp0 regs0) (FPfoot r g bef beffmt s N) (blocks L A) (blocks Lc Ac) a)
by (intros a Ha; exact (WR_CHT Lc Ac memc mdc pnew fimg C a HHc HB HB0 Hch (WRC a Ha))).
jrun_to LAWS ubs2tbl_ok HS HJ PC_RT.
{ apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_gen; [reflexivity | exact HU20 | cbn [r_wlo r_whi]; intros a Ha; apply WRI; unfold ins_w; change (ht_cnt (ch_H C)) with cnt; clear - Ha; lia |].
eapply wr_ok_cons_gen; [reflexivity | exact HU40 | cbn [r_wlo r_whi]; intros a Ha; apply WRI; unfold ins_w; change (ht_cnt (ch_H C)) with cnt; clear - Ha; lia |].
eapply wr_ok_cons_gen; [reflexivity | exact HU41 | cbn [r_wlo r_whi]; intros a Ha; apply WRI; unfold ins_w; change (ht_cnt (ch_H C)) with cnt; clear - Ha; lia |].
eapply wr_ok_cons_gen; [reflexivity | exact HU42 | cbn [r_wlo r_whi]; intros a Ha; apply WRI; unfold ins_w; change (ht_cnt (ch_H C)) with cnt; clear - Ha; lia |].
eapply wr_ok_cons_gen; [reflexivity | exact HU43 | cbn [r_wlo r_whi]; intros a Ha; apply WRI; unfold ins_w; change (ht_cnt (ch_H C)) with cnt; clear - Ha; lia |].
eapply wr_ok_cons_gen; [reflexivity | exact HU44 | cbn [r_wlo r_whi]; intros a Ha; apply WRI; unfold ins_w; change (ht_cnt (ch_H C)) with cnt; clear - Ha; lia |].
apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ ins_w C h a -> mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs memc a).
{ intros a Ha Hna. unfold ins_w in Hna. change (ht_cnt (ch_H C)) with cnt in Hna.
mb_frame_g HF; [reflexivity | lia | rewrite HU20; clear - Hna; lia | rewrite HU40; clear - Hna; lia | rewrite HU41; clear - Hna; lia
| rewrite HU42; clear - Hna; lia | rewrite HU43; clear - Hna; lia | rewrite HU44; clear - Hna; lia]. }
assert (KEEPc : forall a, in_cht C a -> ~ ins_w C h a -> mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs memc a).
{ intros a Hca Hna. pose proof (cht_low API r g bef beffmt s N img fmt rest Lc Ac memc mdc pnew fimg C a HHc HB Hca). apply KEEP; [lia | exact Hna]. }
assert (LOWw : forall a, ins_w C h a -> a < alloc_ceiling).
{ intros a Ha. exact (proj2 (cht_low API r g bef beffmt s N img fmt rest Lc Ac memc mdc pnew fimg C a HHc HB (WRC a Ha))). }
assert (S4 : val_mem ubs2segs (ms_mem ms) (ch_c C + 40) 4 (cnt + 1)).
{ apply (st_chunk_val_g _ _ _ 1%nat _ 20%nat 40 4%N (SOff 36 1) _ _ HS eq_refl eq_refl ltac:(cbn; auto)); [exact HU20 | | cbn; lia | cbn; lia].
cbn [sv_denot]. rewrite HE36, unsigned_lit_small by lia. reflexivity. }
assert (K0 : mbyte ubs2segs (ms_mem ms) (ch_h C + 3 * h) = Some (Z_to_bv 8 cR_)).
{ apply mbyte_of_val_mem1; [|exact R0]. replace (ch_h C + 3 * h) with (ch_h C + 3 * h + 0) by lia.
apply (st_chunk_val_g _ _ _ 2%nat _ 40%nat 0 1%N (SOff 37 0) _ _ HS eq_refl eq_refl ltac:(cbn; auto)); [exact HU40 | | cbn; lia | cbn; lia].
cbn [sv_denot]. rewrite Z.add_0_r, HE37, Z_to_bv_bv_unsigned. reflexivity. }
assert (K1 : mbyte ubs2segs (ms_mem ms) (ch_h C + 3 * h + 1) = Some (Z_to_bv 8 cG_)).
{ apply mbyte_of_val_mem1; [|exact R1].
apply (st_chunk_val_g _ _ _ 2%nat _ 40%nat 1 1%N (SOff 38 0) _ _ HS eq_refl eq_refl ltac:(cbn; auto)); [exact HU40 | | cbn; lia | cbn; lia].
cbn [sv_denot]. rewrite Z.add_0_r, HE38, Z_to_bv_bv_unsigned. reflexivity. }
assert (K2 : mbyte ubs2segs (ms_mem ms) (ch_h C + 3 * h + 2) = Some (Z_to_bv 8 cB_)).
{ apply mbyte_of_val_mem1; [|exact R2].
apply (st_chunk_val_g _ _ _ 2%nat _ 40%nat 2 1%N (SOff 39 0) _ _ HS eq_refl eq_refl ltac:(cbn; auto)); [exact HU40 | | cbn; lia | cbn; lia].
cbn [sv_denot]. rewrite Z.add_0_r, HE39, Z_to_bv_bv_unsigned. reflexivity. }
assert (Q0 : mbyte ubs2segs (ms_mem ms) (ch_p C + 3 * cnt) = Some (Z_to_bv 8 cR_)).
{ apply mbyte_of_val_mem1; [|exact R0]. replace (ch_p C + 3 * cnt) with (ch_p C + 3 * cnt + 0) by lia.
apply (st_chunk_val_g _ _ _ 3%nat _ 41%nat 0 1%N (SOff 37 0) _ _ HS eq_refl eq_refl ltac:(cbn; auto)); [exact HU41 | | cbn; lia | cbn; lia].
cbn [sv_denot]. rewrite Z.add_0_r, HE37, Z_to_bv_bv_unsigned. reflexivity. }
assert (Q1 : mbyte ubs2segs (ms_mem ms) (ch_p C + 3 * cnt + 1) = Some (Z_to_bv 8 cG_)).
{ apply mbyte_of_val_mem1; [|exact R1].
apply (st_chunk_val_g _ _ _ 3%nat _ 41%nat 1 1%N (SOff 38 0) _ _ HS eq_refl eq_refl ltac:(cbn; auto)); [exact HU41 | | cbn; lia | cbn; lia].
cbn [sv_denot]. rewrite Z.add_0_r, HE38, Z_to_bv_bv_unsigned. reflexivity. }
assert (Q2 : mbyte ubs2segs (ms_mem ms) (ch_p C + 3 * cnt + 2) = Some (Z_to_bv 8 cB_)).
{ apply mbyte_of_val_mem1; [|exact R2].
apply (st_chunk_val_g _ _ _ 3%nat _ 41%nat 2 1%N (SOff 39 0) _ _ HS eq_refl eq_refl ltac:(cbn; auto)); [exact HU41 | | cbn; lia | cbn; lia].
cbn [sv_denot]. rewrite Z.add_0_r, HE39, Z_to_bv_bv_unsigned. reflexivity. }
assert (U1 : mbyte ubs2segs (ms_mem ms) (ch_u C + h) = Some (Z_to_bv 8 1)).
{ apply mbyte_of_val_mem1; [|lia]. replace (ch_u C + h) with (ch_u C + h + 0) by lia.
apply (st_chunk_val_g _ _ _ 4%nat _ 42%nat 0 1%N (SLit 1) _ _ HS eq_refl eq_refl ltac:(cbn; auto)); [exact HU42 | reflexivity | cbn; lia | cbn; lia]. }
assert (X4 : val_mem ubs2segs (ms_mem ms) (ch_x C + 4 * h) 4 cnt).
{ replace (ch_x C + 4 * h) with (ch_x C + 4 * h + 0) by lia.
apply (st_chunk_val_g _ _ _ 5%nat _ 43%nat 0 4%N (SOff 36 0) _ _ HS eq_refl eq_refl ltac:(cbn; auto)); [exact HU43 | | cbn; lia | cbn; lia].
cbn [sv_denot]. rewrite Z.add_0_r, HE36, Z_to_bv_bv_unsigned. reflexivity. }
assert (F4 : val_mem ubs2segs (ms_mem ms) (ch_f C + 4 * h) 4 1).
{ replace (ch_f C + 4 * h) with (ch_f C + 4 * h + 0) by lia.
apply (st_chunk_val_g _ _ _ 6%nat _ 44%nat 0 4%N (SLit 1) _ _ HS eq_refl eq_refl ltac:(cbn; auto)); [exact HU44 | reflexivity | cbn; lia | cbn; lia]. }
pose proof (regs_kept_of_st_ok ubs2segs E _ _ regs1 [] [2; 3; 4; 18; 20; 9; 8; 21]%bv HS EA0 ltac:(vm_compute; reflexivity)) as GK.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc]. change (Z_to_bv 64 80476) with (Z_to_bv 64 PC_RT).
apply (KRT (ms_regs ms) (ms_mem ms) (C_ins C h col)). unfold at_RT.
split. { apply (RINV_MEM Lc Ac memc _ mdc HINV HJ). intros a Ha Hna. apply KEEP; [lia|]. intros Hw. pose proof (LOWw a Hw). lia. }
split. { split; [rewrite (GK 2%bv ltac:(cbv; auto 20)); exact G2|]. split; [rewrite (GK 3%bv ltac:(cbv; auto 20)); exact G3 | rewrite (GK 4%bv ltac:(cbv; auto 20)); exact G4]. }
split; [exact Hfmt|]. split; [exact Hi|]. split; [exact Hha|].
split; [rewrite (GK 18%bv ltac:(cbv; auto 20)); exact G18|].
split. { unfold body_regs. cbn [ch_c C_ins]. rewrite (GK 20%bv ltac:(cbv; auto 20)), (GK 9%bv ltac:(cbv; auto 20)), (GK 8%bv ltac:(cbv; auto 20)), (GK 21%bv ltac:(cbv; auto 20)). exact BR. }
split. { unfold slot in *. apply (val_mem_kept8 memc); [exact S72|]. intros k Hk. apply KEEP; [unfold sp, sp0, SL_72 in *; lia|].
intros Hw. pose proof (LOWw _ Hw). unfold sp, sp0, SL_72 in *; lia. }
apply (HM_UPD Lc Ac memc mdc (ms_mem ms) pnew fimg imgl C (C_ins C h col) i (i + 1) HHc); [unfold sp, sp0 in *; lia | unfold sp, sp0 in *; lia | exact Hfmt | exact HMEM | | | reflexivity | reflexivity | exact EhS | exact EuS | exact ETS |].
- intros a Ha Hnc _. apply KEEP; [exact Ha|]. intros Hw. exact (Hnc (WRC a Hw)).
- apply (cht_ok_ins memc (ms_mem ms) C h col Hcht CA Hfs Hz0 Hcol); [exact Hroom | exact K0 | exact K1 | exact K2 | exact Q0 | exact Q1 | exact Q2 | exact U1 | exact X4 | exact F4 | exact S4 | exact KEEPc].
- cbn [ch_ent C_ins]. rewrite map_app, zsum_app. cbn [map snd zsum]. lia.
Qed.
End e.
Section Rt.
Variables (i ha : Z) (Lc : layout) (Ac : astate) (mdc : Model) (pnew fimg : Z) (imgl : list Z).
Hypothesis KRS : forall regs1 memc C', AT_RS regs1 Lc Ac memc mdc i ha pnew fimg imgl C' ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_RS) memc (seg_rom ubs2segs)) mdc) POST.
Hypothesis KINC : forall regs1 memc ha' C', AT_INC regs1 Lc Ac memc mdc i ha' pnew fimg imgl C' ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_INC) memc (seg_rom ubs2segs)) mdc) POST.
Theorem RT_stretch : forall regs1 memc C', AT_RT regs1 Lc Ac memc mdc i ha pnew fimg imgl C' ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_RT) memc (seg_rom ubs2segs)) mdc) POST.
Proof.
intros regs1 memc C' HAT. pose proof HAT as (HINV & HREGS & Hfmt & Hi & Hha & G18 & BR & S72 & HMEM).
pose proof HINV as (HJ & _ & _ & _ & Hal0 & _). pose proof (proj1 HJ) as HHc. pose proof (proj1 alloc_ceiling_val) as Hac.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity.
pose proof HMEM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcht & _ & _ & ETS & _ & _ & _ & HB). pose proof Hcht as (Hobjc & _ & _ & HT & Hch & _).
pose proof (ts_chain_ok _ Hch) as (RT1 & RT2 & RT3). unfold MAX_TABLE_SIZE in RT1.
pose proof BR as (G20 & G9 & G8 & G21).
destruct HREGS as (G2 & G3 & G4).
pose proof (obj_at_nth ubs2segs memc (ch_c C') LAY_Cht _ 6 _ _ Hobjc eq_refl eq_refl) as [Bc6 _]. cbn [fst snd] in Bc6. rewrite ETS in Bc6.
change (N.to_nat 4) with 4%nat in Bc6.
assert (Hcb : In (ch_c C', CHT_SIZE) (blocks Lc Ac)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. right. apply in_app_iff. right. left. reflexivity. }
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc (ch_c C') CHT_SIZE HHc Hcb ltac:(unfold CHT_SIZE; lia)) as (Rc0 & Rc1 & _).
unfold CHT_SIZE in Rc1.
assert (Hsp16 : SP mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (Rha : 0 <= ha <= 1) by (destruct Hha as [-> | [-> _]]; lia).
set (E := Ereg regs1 (map (Z_to_bv 64) [ch_T C'; ha] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 (ch_T C')) by (subst E; apply (Ereg_vals regs1 _ [] 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 ha) by (subst E; apply (Ereg_vals regs1 _ [] 1%nat); reflexivity).
assert (HU20 : bv_unsigned (ew E 20) = ch_c C') by (rewrite (HE 20%nat 20%bv eq_refl), G20; apply unsigned_lit_small; lia).
assert (HU2 : bv_unsigned (ew E 2) = SP) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (HS : st_ok ubs2segs E (mkSS PC_RT sr_atoms [YQ0b.mkRegion (Some 20%nat) 0 48 0 0 [mkChunk 44 (CVal 4 (SOff 32%nat 0))];
YQ0b.mkRegion (Some 2%nat) 0 5168 0 0 [mkChunk 72 (CVal 8 (SOff 33%nat 0))]] None
(mkFacts [(32%nat, mkAF 521 (2^24) 0); (33%nat, mkAF 0 1 0); (2%nat, mkAF CEIL_MIN (2^63) 4)] [] []))
(mkst regs1 (Z_to_bv 64 PC_RT) memc (seg_rom ubs2segs))).
{ subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ unfold region_ok; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU20.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ (ch_T C')); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia | exact Bc6].
+ unfold region_ok; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [unfold sp, sp0 in *; lia|]. split; [unfold sp, sp0 in *; lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ ha); [cbn [sv_denot]; rewrite Z.add_0_r, HE33, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. apply val_mem_word_mem. exact S72.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU20, HU2.
unfold sp, sp0 in *. repeat match goal with |- _ /\ _ => split | |- True => exact I end; lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE32, HE33, HU2, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r. unfold sp, sp0 in *. repeat split; lia. }
assert (EA0 : env_agree 32 (Ereg regs1 []) E).
{ subst E. split; [intros n Hn; rewrite !ew_Ereg_lt by exact Hn; reflexivity | reflexivity]. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_RT) memc (seg_rom ubs2segs))) in HJ. clearbody E.
assert (ARR_INC : forall ss ms', st_ok ubs2segs E ss ms' -> ss_resv ss = None -> ss_pc ss = PC_INC -> ms_mem ms' = memc ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ss) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) [2; 3; 4; 9; 18; 20; 8; 21]%bv = true ->
sr_get (ss_regs ss) 19 = SOff 33 0 ->
SR ubs2segs (mkCfg ms' mdc) POST).
{ intros ss ms' HS' Hrv Hpc Hm QK Q19.
pose proof (regs_kept_of_st_ok ubs2segs E ss ms' regs1 [] _ HS' EA0 QK) as GK.
rewrite (st_ok_mkst ubs2segs _ _ _ HS' Hrv), Hpc, Hm. apply (KINC (ms_regs ms') memc ha C'). unfold at_INC.
split; [exact HINV|].
split. { split; [rewrite (GK 2%bv ltac:(cbv; auto 20)); exact G2|]. split; [rewrite (GK 3%bv ltac:(cbv; auto 20)); exact G3 | rewrite (GK 4%bv ltac:(cbv; auto 20)); exact G4]. }
split; [exact Hfmt|]. split; [exact Hi|]. split; [exact Hha|]. split; [|exact HMEM].
unfold hist_regs.
rewrite (GK 9%bv ltac:(cbv; auto 20)), (GK 18%bv ltac:(cbv; auto 20)), (GK 20%bv ltac:(cbv; auto 20)), (GK 8%bv ltac:(cbv; auto 20)), (GK 21%bv ltac:(cbv; auto 20)).
split; [exact G9|]. split; [exact G18|].
split. { eapply (getr_of_U ubs2segs); [exact HS'|]. rewrite Q19. apply (U_atom E 33 ha HE33). lia. }
split; [exact G20|]. split; [exact G8 | exact G21]. }
assert (ARR_RS : forall ss ms', st_ok ubs2segs E ss ms' -> ss_resv ss = None -> ss_pc ss = PC_RS -> ms_mem ms' = memc -> ch_T C' < MAX_TABLE_SIZE ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ss) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) [2; 3; 4; 9; 20; 8; 21]%bv = true ->
sr_get (ss_regs ss) 10 = SOff 32 0 ->
SR ubs2segs (mkCfg ms' mdc) POST).
{ intros ss ms' HS' Hrv Hpc Hm HTlt QK Q10.
pose proof (regs_kept_of_st_ok ubs2segs E ss ms' regs1 [] _ HS' EA0 QK) as GK.
rewrite (st_ok_mkst ubs2segs _ _ _ HS' Hrv), Hpc, Hm. apply (KRS (ms_regs ms') memc C'). unfold at_RS.
split; [exact HINV|].
split. { split; [rewrite (GK 2%bv ltac:(cbv; auto 20)); exact G2|]. split; [rewrite (GK 3%bv ltac:(cbv; auto 20)); exact G3 | rewrite (GK 4%bv ltac:(cbv; auto 20)); exact G4]. }
split; [exact Hfmt|]. split; [exact Hi|]. split; [exact Hha|].
split. { eapply (getr_of_U ubs2segs); [exact HS'|]. rewrite Q10. apply (U_atom E 32 (ch_T C') HE32). lia. }
rewrite (GK 9%bv ltac:(cbv; auto 20)), (GK 20%bv ltac:(cbv; auto 20)), (GK 8%bv ltac:(cbv; auto 20)), (GK 21%bv ltac:(cbv; auto 20)).
split; [exact G9|]. split; [exact G20|]. split; [exact G8|]. split; [exact G21|]. split; [exact HTlt|]. split; [exact S72 | exact HMEM]. }
Ltac ro2 := apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_nil.
jrun LAWS ubs2tbl_ok HS HJ. { ro2. }
assert (Em : ms_mem ms = memc) by (apply functional_extensionality; intros x; refine (frame_of_ro _ _ _ _ _ HF x); reflexivity). cbn [ms_mem mkst] in Em.
jbranch ubs2tbl HS.
-
jrun_to LAWS ubs2tbl_ok HS HJ PC_INC. { ro2. }
assert (Em0 : ms_mem ms0 = memc) by (rewrite <- Em; apply functional_extensionality; intros x; refine (frame_of_ro _ _ _ _ _ HF0 x); reflexivity).
apply (ARR_INC _ _ HS eq_refl eq_refl Em0); vm_compute; reflexivity.
-
rewrite branch_ne_U, U_lit, (U_srl24 E 32 (ch_T C') HE32) in Hc by lia. apply negb_false_iff in Hc. apply Z.eqb_eq in Hc.
assert (HTlt : ch_T C' < MAX_TABLE_SIZE).
{ unfold MAX_TABLE_SIZE. destruct (Z_lt_le_dec (ch_T C') 16777216) as [|Hge]; [assumption|]. exfalso.
rewrite Z.shiftr_div_pow2 in Hc by lia. assert (1 <= ch_T C' / 2 ^ 24) by (apply Z.div_le_lower_bound; lia). lia. }
jrun LAWS ubs2tbl_ok HS HJ. { ro2. }
assert (Em0 : ms_mem ms0 = memc) by (rewrite <- Em; apply functional_extensionality; intros x; refine (frame_of_ro _ _ _ _ _ HF0 x); reflexivity).
jbranch ubs2tbl HS.
+
jrun_to LAWS ubs2tbl_ok HS HJ PC_INC. { ro2. }
assert (Em1 : ms_mem ms1 = memc) by (rewrite <- Em0; apply functional_extensionality; intros x; refine (frame_of_ro _ _ _ _ _ HF1 x); reflexivity).
apply (ARR_INC _ _ HS eq_refl eq_refl Em1); vm_compute; reflexivity.
+
jrun_to LAWS ubs2tbl_ok HS HJ PC_RS. { ro2. }
assert (Em1 : ms_mem ms1 = memc) by (rewrite <- Em0; apply functional_extensionality; intros x; refine (frame_of_ro _ _ _ _ _ HF1 x); reflexivity).
apply (ARR_RS _ _ HS eq_refl eq_refl Em1 HTlt); vm_compute; reflexivity.
Qed.
End Rt.
Section f.
Variables (i : Z) (Lc : layout) (Ac : astate) (mdc : Model) (pnew fimg : Z) (imgl : list Z).
Hypothesis KHL : forall regs1 memc ha C', AT_HL regs1 Lc Ac memc mdc (i + 1) ha pnew fimg imgl C' ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_HL) memc (seg_rom ubs2segs)) mdc) POST.
Hypothesis KHD : forall regs1 memc ha C', AT_HD regs1 Lc Ac memc mdc ha pnew fimg imgl C' ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_HD) memc (seg_rom ubs2segs)) mdc) POST.
Theorem INC_stretch : forall regs1 memc ha C', AT_INC regs1 Lc Ac memc mdc i ha pnew fimg imgl C' ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_INC) memc (seg_rom ubs2segs)) mdc) POST.
Proof.
intros regs1 memc ha C' HAT. pose proof HAT as (HINV & HREGS & Hfmt & Hi & Hha & HR & HMEM).
pose proof (proj1 HINV) as HJ. pose proof HINV as (_ & _ & _ & _ & Hal0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNmax & _). unfold RGB_NMAX in HNmax.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw). pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity.
destruct HREGS as (G2 & G3 & G4). pose proof HR as (G9 & G18 & G19 & G20 & G8 & G21).
pose proof HMEM as (_ & _ & _ & S56 & _).
assert (Hsp16 : SP mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
set (E := Ereg regs1 (map (Z_to_bv 64) [N] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE9 : ew E 9 = Z_to_bv 64 i) by (rewrite (HE 9%nat 9%bv eq_refl); exact G9).
assert (HE32 : ew E 32 = Z_to_bv 64 N) by (subst E; apply (Ereg_vals regs1 _ [] 0%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = SP) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (HS : st_ok ubs2segs E (mkSS PC_INC sr_atoms [YQ0b.mkRegion (Some 2%nat) 0 5168 0 0 [mkChunk 56 (CVal 8 (SOff 32%nat 0))]] None
(mkFacts [(9%nat, mkAF 0 10000 0); (32%nat, mkAF 0 10000 0); (2%nat, mkAF CEIL_MIN (2^63) 4)] [] [])) (mkst regs1 (Z_to_bv 64 PC_INC) memc (seg_rom ubs2segs))).
{ subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [unfold sp, sp0 in *; lia|]. split; [unfold sp, sp0 in *; lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ N); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. apply val_mem_word_mem. exact S56.
- cbn [pairwise_disjoint all_disjoint]. repeat split; exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE9, HE32, HU2, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r. unfold sp, sp0 in *. repeat split; lia. }
assert (EA0 : env_agree 32 (Ereg regs1 []) E).
{ subst E. split; [intros n Hn; rewrite !ew_Ereg_lt by exact Hn; reflexivity | reflexivity]. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_INC) memc (seg_rom ubs2segs))) in HJ. clearbody E.
jrun LAWS ubs2tbl_ok HS HJ. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
assert (Em : ms_mem ms = memc) by (apply functional_extensionality; intros x; refine (frame_of_ro _ _ _ _ _ HF x); reflexivity). cbn [ms_mem mkst] in Em.
jbranch ubs2tbl HS.
-
rewrite branch_ne_U, (U_atom_off E 9 i 1 HE9), (U_atom E 32 N HE32) in Hc by lia. apply negb_true_iff in Hc. apply Z.eqb_neq in Hc.
jrun_to LAWS ubs2tbl_ok HS HJ PC_HL. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
assert (Em0 : ms_mem ms0 = memc) by (rewrite <- Em; apply functional_extensionality; intros x; refine (frame_of_ro _ _ _ _ _ HF0 x); reflexivity).
pose proof (regs_kept_of_st_ok ubs2segs E _ _ regs1 [] [2; 3; 4; 18; 19; 20; 8; 21]%bv HS EA0 ltac:(vm_compute; reflexivity)) as GK.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl), Em0. cbn [ss_pc]. change (Z_to_bv 64 79672) with (Z_to_bv 64 PC_HL).
apply (KHL (ms_regs ms0) memc ha C'). unfold at_HL.
split; [exact HINV|].
split. { split; [rewrite (GK 2%bv ltac:(cbv; auto 20)); exact G2|]. split; [rewrite (GK 3%bv ltac:(cbv; auto 20)); exact G3 | rewrite (GK 4%bv ltac:(cbv; auto 20)); exact G4]. }
split; [exact Hfmt|]. split; [lia|]. split; [exact Hha|]. split; [|exact HMEM].
unfold hist_regs.
rewrite (GK 18%bv ltac:(cbv; auto 20)), (GK 19%bv ltac:(cbv; auto 20)), (GK 20%bv ltac:(cbv; auto 20)), (GK 8%bv ltac:(cbv; auto 20)), (GK 21%bv ltac:(cbv; auto 20)).
split; [eapply (getr_of_U ubs2segs); [exact HS|]; eval_sr_get; apply (U_atom_off E 9 i 1 HE9); lia|].
repeat (split; [assumption|]). exact G21.
-
rewrite branch_ne_U, (U_atom_off E 9 i 1 HE9), (U_atom E 32 N HE32) in Hc by lia. apply negb_false_iff in Hc. apply Z.eqb_eq in Hc.
jrun_to LAWS ubs2tbl_ok HS HJ PC_HD. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
assert (Em0 : ms_mem ms0 = memc) by (rewrite <- Em; apply functional_extensionality; intros x; refine (frame_of_ro _ _ _ _ _ HF0 x); reflexivity).
pose proof (regs_kept_of_st_ok ubs2segs E _ _ regs1 [] [2; 3; 4; 19; 20; 8; 21]%bv HS EA0 ltac:(vm_compute; reflexivity)) as GK.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl), Em0. cbn [ss_pc]. change (Z_to_bv 64 81528) with (Z_to_bv 64 PC_HD).
apply (KHD (ms_regs ms0) memc ha C'). unfold at_HD.
split; [exact HINV|].
split. { split; [rewrite (GK 2%bv ltac:(cbv; auto 20)); exact G2|]. split; [rewrite (GK 3%bv ltac:(cbv; auto 20)); exact G3 | rewrite (GK 4%bv ltac:(cbv; auto 20)); exact G4]. }
split; [exact Hfmt|]. split; [lia|]. split; [exact Hha|].
rewrite (GK 19%bv ltac:(cbv; auto 20)), (GK 20%bv ltac:(cbv; auto 20)), (GK 8%bv ltac:(cbv; auto 20)), (GK 21%bv ltac:(cbv; auto 20)).
repeat (split; [assumption|]). rewrite Hc in HMEM. exact HMEM.
Qed.
End f.
End d.
End c.
