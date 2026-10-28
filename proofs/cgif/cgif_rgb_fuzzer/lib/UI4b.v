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
UI4v UI46 UI4g.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.

Definition PC_F1 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x1380).
Definition PC_F2 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x1388).
Definition PC_F3 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x1390).
Definition ssF (p1z x1z : bool) : sstate := mkSS PC_FAIL
(let sr := if p1z then sr_set sr_atoms 27%bv (SLit 0) else sr_atoms in if x1z then sr_set sr 22%bv (SLit 0) else sr)
[ YQ0b.mkRegion (Some 20%nat) 0 48 24 40 [mkChunk 0 (CVal 8 (SOff 32%nat 0)); mkChunk 8 (CVal 8 (SOff 33%nat 0)); mkChunk 16 (CVal 8 (SOff 34%nat 0));
mkChunk 24 (CVal 8 (SOff 35%nat 0)); mkChunk 32 (CVal 8 (SOff 36%nat 0)); mkChunk 40 (CVal 4 (SOff 37%nat 0)); mkChunk 44 (CVal 4 (SOff 38%nat 0))] ;
YQ0b.mkRegion (Some 2%nat) 0 5168 0 0 [mkChunk 48 (CVal 8 (SOff 39%nat 0))] ] None
(mkFacts ([(2%nat, mkAF CEIL_MIN (2^63) 4); (37%nat, mkAF 0 (2^32 - 1) 0); (38%nat, mkAF 0 (2^32 - 1) 0)]
++ (if p1z then [] else [(27%nat, mkAF 1 (2^64-1) 0)]) ++ (if x1z then [] else [(22%nat, mkAF 1 (2^64-1) 0)])) [] []).
Ltac in_chunks := cbn [r_chunks]; repeat (first [left; reflexivity | right]).
Section d.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Hypothesis FCHT : forall fx', free_cht_spec (fx:=fx') API.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Local Notation RINV := (rgba_inv API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest).
Local Notation POST := (rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Local Notation SP := (sp regs0).
Local Notation BASE0 := (BASE r g N img fmt rest s bef beffmt).
Local Notation AT_FAIL := (at_FAIL API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation AT_XB := (at_XB API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation KEEPB := (keepb r g bef beffmt s N img fmt rest).
Local Notation RZ_MEM := (rz_mem regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay).
Local Notation RZ_BLOCKS := (rz_blocks r g bef beffmt s N img fmt rest).
Local Notation RZ_FACTS := (rz_facts N fmt).
Local Notation RZ_MEM_ZSUM := (rz_mem_zsum regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay).
Local Notation RZ_MEM_HT := (rz_mem_ht regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay).
Local Notation RZ_MEM_LIVE := (rz_mem_live regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay).
Local Notation RZ_MEM_KEPT := (rz_mem_kept API regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay rest).
Local Notation RINV_CALL := (rgba_inv_call API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest).
Definition structF (memc : word -> option byte) (C : cht) (T' p1 x1 : Z) : Prop :=
obj_at ubs2segs memc (ch_c C) LAY_Cht [ch_f C; ch_h C; ch_u C; fst (rbk (ch_p C, 3 * ch_T C) p1 (3 * T')); fst (rbk (ch_x C, 4 * ch_T C) x1 (4 * T')); ht_cnt (ch_H C); ch_T C].
Definition f_regs (regs1 : bvmap 5 word) (C : cht) : Prop :=
rgba_regs regs0 regs1 /\ getr regs1 20 = Z_to_bv 64 (ch_c C) /\ getr regs1 8 = Z_to_bv 64 r /\ getr regs1 21 = Z_to_bv 64 2.
Definition at_FS (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(i ha pnew fimg : Z) (imgl : list Z) (C : cht) (T' p1 x1 h1 u1 f1 : Z) : Prop :=
RINV Lc Ac memc mdc /\ RZ_FACTS i ha T' C /\ f_regs regs1 C /\ getr regs1 1 = Z_to_bv 64 PC_F1 /\ getr regs1 10 = Z_to_bv 64 h1 /\
getr regs1 25 = Z_to_bv 64 u1 /\ getr regs1 26 = Z_to_bv 64 f1 /\ getr regs1 9 = Z_to_bv 64 fimg /\
RZ_MEM memc i ha pnew fimg imgl C /\ structF memc C T' p1 x1 /\
RZ_BLOCKS Lc Ac pnew fimg C ([rbk (ch_p C, 3 * ch_T C) p1 (3 * T'); rbk (ch_x C, 4 * ch_T C) x1 (4 * T')] ++ optb h1 (3 * T') ++ optb u1 T' ++ optb f1 (4 * T')).
Definition at_F1 (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(i ha pnew fimg : Z) (imgl : list Z) (C : cht) (T' p1 x1 u1 f1 : Z) : Prop :=
RINV Lc Ac memc mdc /\ RZ_FACTS i ha T' C /\ f_regs regs1 C /\ getr regs1 25 = Z_to_bv 64 u1 /\ getr regs1 26 = Z_to_bv 64 f1 /\
getr regs1 9 = Z_to_bv 64 fimg /\
RZ_MEM memc i ha pnew fimg imgl C /\ structF memc C T' p1 x1 /\
RZ_BLOCKS Lc Ac pnew fimg C ([rbk (ch_p C, 3 * ch_T C) p1 (3 * T'); rbk (ch_x C, 4 * ch_T C) x1 (4 * T')] ++ optb u1 T' ++ optb f1 (4 * T')).
Definition at_F2 (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(i ha pnew fimg : Z) (imgl : list Z) (C : cht) (T' p1 x1 f1 : Z) : Prop :=
RINV Lc Ac memc mdc /\ RZ_FACTS i ha T' C /\ f_regs regs1 C /\ getr regs1 26 = Z_to_bv 64 f1 /\ getr regs1 9 = Z_to_bv 64 fimg /\
RZ_MEM memc i ha pnew fimg imgl C /\ structF memc C T' p1 x1 /\
RZ_BLOCKS Lc Ac pnew fimg C ([rbk (ch_p C, 3 * ch_T C) p1 (3 * T'); rbk (ch_x C, 4 * ch_T C) x1 (4 * T')] ++ optb f1 (4 * T')).
Definition at_F3 (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(i ha pnew fimg : Z) (imgl : list Z) (C : cht) (T' p1 x1 : Z) : Prop :=
RINV Lc Ac memc mdc /\ RZ_FACTS i ha T' C /\ f_regs regs1 C /\ getr regs1 9 = Z_to_bv 64 fimg /\
RZ_MEM memc i ha pnew fimg imgl C /\ structF memc C T' p1 x1 /\
RZ_BLOCKS Lc Ac pnew fimg C [rbk (ch_p C, 3 * ch_T C) p1 (3 * T'); rbk (ch_x C, 4 * ch_T C) x1 (4 * T')].
Section h.
Variables (i ha : Z) (pnew fimg : Z) (imgl : list Z) (C : cht) (T' : Z).
Hypothesis KFS : forall regs1 Lc Ac memc mdc p1 x1 h1 u1 f1, at_FS regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 ubs2_A_free) memc (seg_rom ubs2segs)) mdc) POST.
Theorem FAIL_stretch : forall regs1 Lc Ac memc mdc p1 x1 h1 u1 f1, AT_FAIL regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_FAIL) memc (seg_rom ubs2segs)) mdc) POST.
Proof.
intros regs1 Lc Ac memc mdc p1 x1 h1 u1 f1 HAT.
destruct HAT as (HINV & HRZF & (HREGS & G9 & G20 & G8 & G21) & (G27 & G22 & G24 & G25 & G26 & G19) & Hsome & RZM & S72 & RZS & RZB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbf & HB0).
destruct HREGS as (G2 & G3 & G4).
pose proof (RZ_MEM_HT _ _ _ _ _ _ _ RZM) as (Hinv & HT & Hch & HTlt). pose proof (RZ_MEM_ZSUM _ _ _ _ _ _ _ RZM) as Hz.
pose proof (RZ_MEM_LIVE _ _ _ _ _ _ _ RZM) as (EhS & EuS & ETS).
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity.
pose proof (ts_chain_ok _ Hch) as (RT1 & RT2 & RT3). unfold MAX_TABLE_SIZE in RT1, HTlt.
pose proof HRZF as (Hfmt & Hi & Hha & ET').
pose proof (resize_next (ch_T C) Hch HTlt) as (Hch' & _ & (RT1' & _)). rewrite <- ET' in Hch', RT1'. unfold MAX_TABLE_SIZE in RT1'.
pose proof Hinv as (_ & (C1 & _) & _). rewrite HT in C1.
set (T := ch_T C) in *.
pose proof RZS as Hobjc. unfold rz_struct in Hobjc.
assert (FLD : forall j v, nth_error [ch_f C; ch_hS C; ch_uS C; ch_p C; ch_x C; ht_cnt (ch_H C); ch_TS C] j = Some v ->
forall f, nth_error LAY_Cht j = Some f -> field_ok ubs2segs memc (ch_c C) f v).
{ intros j v Hv f Hf. exact (obj_at_nth ubs2segs memc (ch_c C) LAY_Cht _ j f v Hobjc Hf Hv). }
pose proof (FLD 0%nat _ eq_refl _ eq_refl) as [B0 R0]. pose proof (FLD 1%nat _ eq_refl _ eq_refl) as [B1 R1]. pose proof (FLD 2%nat _ eq_refl _ eq_refl) as [B2 R2].
pose proof (FLD 3%nat _ eq_refl _ eq_refl) as [B3 R3]. pose proof (FLD 4%nat _ eq_refl _ eq_refl) as [B4 R4]. pose proof (FLD 5%nat _ eq_refl _ eq_refl) as [B5 R5].
pose proof (FLD 6%nat _ eq_refl _ eq_refl) as [B6 R6]. clear FLD.
cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in B0, B1, B2, B3, B4, B5, B6, R0, R1, R2, R3, R4, R5, R6.
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in R0, R1, R2, R3, R4. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in R5, R6. rewrite Z.add_0_r in B0.
assert (INB : forall b, In b (KEEPB pnew fimg C ++ [rbk (ch_p C, 3 * T) p1 (3 * T'); rbk (ch_x C, 4 * T) x1 (4 * T')] ++ optb h1 (3 * T') ++ optb u1 T' ++ optb f1 (4 * T')) -> In b (blocks Lc Ac)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact RZB | exact Hb]. }
assert (RNG : forall q n, In (q, n) (blocks Lc Ac) -> 0 < n -> 4096 <= q /\ q + n <= alloc_ceiling).
{ intros q n Hq Hn. destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc q n HHc Hq Hn) as (Q0 & Q1 & _). lia. }
destruct (RNG (ch_c C) CHT_SIZE ltac:(apply INB; apply in_app_iff; left; unfold keepb; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity) ltac:(unfold CHT_SIZE; lia)) as [Rc0 Rc1]. unfold CHT_SIZE in Rc1.
assert (Rp1 : p1 <> 0 -> 4096 <= p1 /\ p1 + 3 * T' <= alloc_ceiling).
{ intros Hnz. apply (RNG p1 (3 * T')); [| lia]. apply INB. apply in_app_iff. right. apply in_app_iff. left. left. unfold rbk. destruct (Z.eqb_spec p1 0); [lia | reflexivity]. }
assert (Rx1 : x1 <> 0 -> 4096 <= x1 /\ x1 + 4 * T' <= alloc_ceiling).
{ intros Hnz. apply (RNG x1 (4 * T')); [| lia]. apply INB. apply in_app_iff. right. apply in_app_iff. left. right. left. unfold rbk. destruct (Z.eqb_spec x1 0); [lia | reflexivity]. }
set (E := Ereg regs1 (map (Z_to_bv 64) [ch_f C; ch_hS C; ch_uS C; ch_p C; ch_x C; ht_cnt (ch_H C); ch_TS C; fimg] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall jj v, nth_error [ch_f C; ch_hS C; ch_uS C; ch_p C; ch_x C; ht_cnt (ch_H C); ch_TS C; fimg] jj = Some v -> ew E (32 + jj) = Z_to_bv 64 v)
by (intros jj v Hjv; subst E; apply Ereg_vals; exact Hjv).
assert (HE32 : ew E 32 = Z_to_bv 64 (ch_f C)) by exact (HV 0%nat _ eq_refl).
assert (HE33 : ew E 33 = Z_to_bv 64 (ch_hS C)) by exact (HV 1%nat _ eq_refl).
assert (HE34 : ew E 34 = Z_to_bv 64 (ch_uS C)) by exact (HV 2%nat _ eq_refl).
assert (HE35 : ew E 35 = Z_to_bv 64 (ch_p C)) by exact (HV 3%nat _ eq_refl).
assert (HE36 : ew E 36 = Z_to_bv 64 (ch_x C)) by exact (HV 4%nat _ eq_refl).
assert (HE37 : ew E 37 = Z_to_bv 64 (ht_cnt (ch_H C))) by exact (HV 5%nat _ eq_refl).
assert (HE38 : ew E 38 = Z_to_bv 64 (ch_TS C)) by exact (HV 6%nat _ eq_refl).
assert (HE39 : ew E 39 = Z_to_bv 64 fimg) by exact (HV 7%nat _ eq_refl).
assert (HE20 : ew E 20 = Z_to_bv 64 (ch_c C)) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (HU20 : bv_unsigned (ew E 20) = ch_c C) by (rewrite HE20; apply unsigned_lit_small; lia).
assert (HU2 : bv_unsigned (ew E 2) = SP) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (HE27 : ew E 27 = Z_to_bv 64 p1) by (rewrite (HE 27%nat 27%bv eq_refl); exact G27).
assert (HE22 : ew E 22 = Z_to_bv 64 x1) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22).
assert (HE24 : ew E 24 = Z_to_bv 64 h1) by (rewrite (HE 24%nat 24%bv eq_refl); exact G24).
assert (Rfm : 0 <= fimg < 2 ^ 64).
{ destruct (RNG fimg N) as [Q0 Q1]; [| lia | lia].
apply INB. apply in_app_iff. left. unfold keepb. apply in_app_iff. right. apply in_app_iff. left. right. left. reflexivity. }
assert (SFIM : slot regs0 memc SL_fimg fimg) by (pose proof RZM as (Hslots & _); exact (proj2 (proj2 (proj2 Hslots)))).
assert (Hsp16 : SP mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (ROK : Forall (region_ok ubs2segs E memc) (ss_mem (ssF true true))).
{ cbn [ss_mem ssF]. subst E. constructor; [|constructor; [|constructor]]; unfold region_ok; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite HU20. split; [lia|]. split; [lia|].
split. { intros o Ho. apply (present_writable ubs2_msyms).
apply (proj1 (heap_blocks ubs2_msyms MR LAWS Lc Ac memc mdc (ch_c C) CHT_SIZE o HHc ltac:(apply INB; apply in_app_iff; left; unfold keepb; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity) ltac:(unfold CHT_SIZE; lia))). }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]]]].
+ eapply (chunk_ok_val _ _ _ _ _ _ _ (ch_f C)); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite Z.add_0_r. exact B0.
+ eapply (chunk_ok_val _ _ _ _ _ _ _ (ch_hS C)); [cbn [sv_denot]; rewrite Z.add_0_r, HE33, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact B1.
+ eapply (chunk_ok_val _ _ _ _ _ _ _ (ch_uS C)); [cbn [sv_denot]; rewrite Z.add_0_r, HE34, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact B2.
+ eapply (chunk_ok_val _ _ _ _ _ _ _ (ch_p C)); [cbn [sv_denot]; rewrite Z.add_0_r, HE35, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact B3.
+ eapply (chunk_ok_val _ _ _ _ _ _ _ (ch_x C)); [cbn [sv_denot]; rewrite Z.add_0_r, HE36, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact B4.
+ eapply (chunk_ok_val _ _ _ _ _ _ _ (ht_cnt (ch_H C))); [cbn [sv_denot]; rewrite Z.add_0_r, HE37, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact B5.
+ eapply (chunk_ok_val _ _ _ _ _ _ _ (ch_TS C)); [cbn [sv_denot]; rewrite Z.add_0_r, HE38, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact B6.
+ rewrite HU2. split; [unfold sp, sp0 in *; lia|]. split; [unfold sp, sp0 in *; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ fimg); [cbn [sv_denot]; rewrite Z.add_0_r, HE39, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. apply val_mem_word_mem. exact SFIM. }
assert (PD : pairwise_disjoint E (ss_mem (ssF true true))).
{ cbn [ss_mem ssF pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU20, HU2.
unfold sp, sp0 in *. repeat match goal with |- _ /\ _ => split | |- True => exact I end; lia. }
assert (AOK : forall p1z x1z, (p1z = false -> p1 <> 0) -> (x1z = false -> x1 <> 0) -> atoms_ok E (f_atoms (ss_facts (ssF p1z x1z)))).
{ intros p1z x1z Hp Hx. cbn [ss_facts ssF f_atoms].
assert (A2 : afact_ok E 2 (mkAF CEIL_MIN (2^63) 4)) by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite HU2; change (2 ^ 4) with 16; unfold sp, sp0 in *; repeat split; lia).
assert (A37 : afact_ok E 37 (mkAF 0 (2^32 - 1) 0)) by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite HE37, unsigned_lit_small by lia; change (2 ^ 0) with 1; rewrite Z.mod_1_r; repeat split; lia).
assert (A38 : afact_ok E 38 (mkAF 0 (2^32 - 1) 0)) by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite HE38, unsigned_lit_small by lia; change (2 ^ 0) with 1; rewrite Z.mod_1_r; repeat split; lia).
assert (A27 : p1 <> 0 -> afact_ok E 27 (mkAF 1 (2^64-1) 0)).
{ intros Hnz. specialize (Rp1 Hnz). unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite HE27, unsigned_lit_small by lia; change (2 ^ 0) with 1; rewrite Z.mod_1_r; repeat split; lia. }
assert (A22 : x1 <> 0 -> afact_ok E 22 (mkAF 1 (2^64-1) 0)).
{ intros Hnz. specialize (Rx1 Hnz). unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite HE22, unsigned_lit_small by lia; change (2 ^ 0) with 1; rewrite Z.mod_1_r; repeat split; lia. }
destruct p1z, x1z; cbn [app atoms_ok].
- exact (conj A2 (conj A37 (conj A38 I))).
- exact (conj A2 (conj A37 (conj A38 (conj (A22 (Hx eq_refl)) I)))).
- exact (conj A2 (conj A37 (conj A38 (conj (A27 (Hp eq_refl)) I)))).
- exact (conj A2 (conj A37 (conj A38 (conj (A27 (Hp eq_refl)) (conj (A22 (Hx eq_refl)) I))))). }
assert (RGOK : forall p1z x1z, (p1z = true -> p1 = 0) -> (x1z = true -> x1 = 0) -> regs_ok E (ss_regs (ssF p1z x1z)) regs1).
{ intros p1z x1z Hp Hx. cbn [ss_regs ssF]. subst E.
destruct x1z; [apply regs_ok_pin; [| intros X; discriminate X | rewrite G22, (Hx eq_refl); reflexivity]|]; (destruct p1z; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | rewrite G27, (Hp eq_refl); reflexivity] | apply regs_ok_Ereg]). }
assert (MKS : forall p1z x1z, (p1z = true <-> p1 = 0) -> (x1z = true <-> x1 = 0) -> st_ok ubs2segs E (ssF p1z x1z) (mkst regs1 (Z_to_bv 64 PC_FAIL) memc (seg_rom ubs2segs))).
{ intros p1z x1z Hp Hx. unfold ssF.
lazymatch goal with |- st_ok _ _ (mkSS _ ?sr ?rs _ (mkFacts ?fa _ _)) _ =>
change sr with (ss_regs (ssF p1z x1z)); change rs with (ss_mem (ssF true true)); change fa with (f_atoms (ss_facts (ssF p1z x1z))) end.
subst E. apply entry_st_ok_gen; [apply RGOK; [apply Hp | apply Hx] | destruct p1z, x1z; vm_compute; reflexivity | exact ROK | exact PD | apply AOK; [intros Ez; destruct Hp as [_ Hp']; intros E0; specialize (Hp' E0); congruence | intros Ez; destruct Hx as [_ Hx']; intros E0; specialize (Hx' E0); congruence]]. }
assert (EA0 : env_agree 32 (Ereg regs1 []) E).
{ subst E. split; [intros n Hn; rewrite !ew_Ereg_lt by exact Hn; reflexivity | reflexivity]. }
clearbody E. clear HV ROK PD AOK RGOK.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_FAIL) memc (seg_rom ubs2segs))) in HJ.
assert (SEPc : forall y, In y (BASE0 ++ [(ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T)]) -> ch_c C + CHT_SIZE <= fst y \/ fst y + snd y <= ch_c C).
{ intros y Hy. pose proof (perm_sep API Lc Ac memc mdc (ch_c C, CHT_SIZE) y (BASE0 ++ [(pnew, fmt * N); (fimg, N)])
([(ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T)] ++ [rbk (ch_p C, 3 * T) p1 (3 * T'); rbk (ch_x C, 4 * T) x1 (4 * T')] ++ optb h1 (3 * T') ++ optb u1 T' ++ optb f1 (4 * T')) HHc) as X.
cbn [fst snd] in X. apply X.
- unfold rz_blocks, keepb in RZB. rewrite <- !app_assoc in RZB. rewrite <- !app_assoc. exact RZB.
- apply in_app_iff in Hy. apply in_app_iff. destruct Hy as [Hy|Hy]; [left; apply in_app_iff; left; exact Hy | right; apply in_app_iff; left; exact Hy]. }
unfold CHT_SIZE in SEPc.
assert (ARR : forall ss ms' rg, st_ok ubs2segs E ss ms' -> ss_resv ss = None -> ss_pc ss = ubs2_A_free ->
journal ubs2_msyms MR RGBA_STK (sp0 regs0) (FPfoot r g bef beffmt s N) L A mem0 md0 Lc Ac (ms_mem ms') mdc ->
frame_of E (ss_mem (ssF true true)) memc (ms_mem ms') ->
nth_error (ss_mem ss) 0 = Some rg -> r_base rg = Some 20%nat ->
In (mkChunk 0 (CVal 8 (SOff 32 0))) (r_chunks rg) -> In (mkChunk 8 (CVal 8 (SOff 33 0))) (r_chunks rg) -> In (mkChunk 16 (CVal 8 (SOff 34 0))) (r_chunks rg) ->
In (mkChunk 24 (CVal 8 (if p1 =? 0 then SOff 35 0 else SOff 27 0))) (r_chunks rg) -> In (mkChunk 32 (CVal 8 (if x1 =? 0 then SOff 36 0 else SOff 22 0))) (r_chunks rg) ->
In (mkChunk 40 (CVal 4 (SOff 37 0))) (r_chunks rg) -> In (mkChunk 44 (CVal 4 (SOff 38 0))) (r_chunks rg) ->
sr_get (ss_regs ss) 10 = SOff 24 0 -> sr_get (ss_regs ss) 1 = SLit 83948 -> sr_get (ss_regs ss) 9 = SOff 39 0 ->
forallb (fun rr : reg => sv_eqb (sr_get (ss_regs ss) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) [2; 3; 4; 8; 20; 21; 25; 26]%bv = true ->
SR ubs2segs (mkCfg ms' mdc) POST).
{ intros ss ms' rg HS' Hrv Hpc HJ' HF' Hrg Hb C0 C8 C16 C24 C32 C40 C44 Q10 Q1 Q9 QK.
pose proof (regs_kept_of_st_ok ubs2segs E ss ms' regs1 [] _ HS' EA0 QK) as GK.
assert (RG : forall (rr : reg) e, sr_get (ss_regs ss) rr = e -> getr (ms_regs ms') rr = sv_denot E e) by (intros rr e He; rewrite <- He; apply (st_ok_reg _ _ _ _ rr HS')).
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (ch_c C + 24 <= a < ch_c C + 40) -> mbyte ubs2segs (ms_mem ms') a = mbyte ubs2segs memc a).
{ intros a Ha Hna. cbn [ss_mem ssF] in HF'. mb_frame_g HF'; [reflexivity | rewrite HU20; exact Hna | rewrite HU2; lia]. }
assert (VAL : forall off (n : BinNums.N) e v, In (mkChunk off (CVal n e)) (r_chunks rg) -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem ubs2segs (ms_mem ms') (ch_c C + off) (N.to_nat n) v).
{ intros off n e v Hin He Hv Hn. exact (st_chunk_val_g E ss ms' 0%nat rg 20%nat off n e (ch_c C) v HS' Hrg Hb Hin HU20 He Hv Hn). }
rewrite (st_ok_mkst ubs2segs _ _ _ HS' Hrv), Hpc. apply (KFS (ms_regs ms') Lc Ac (ms_mem ms') mdc p1 x1 h1 u1 f1). unfold at_FS.
split. { apply (rgba_inv_mem API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest Lc Ac memc _ mdc HINV HJ'). intros a Ha Hna. apply KEEP; lia. }
split; [exact HRZF|].
split. { unfold f_regs, rgba_regs. rewrite (GK 2%bv ltac:(cbv; auto 20)), (GK 3%bv ltac:(cbv; auto 20)), (GK 4%bv ltac:(cbv; auto 20)),
(GK 20%bv ltac:(cbv; auto 20)), (GK 8%bv ltac:(cbv; auto 20)), (GK 21%bv ltac:(cbv; auto 20)).
split; [split; [exact G2 | split; [exact G3 | exact G4]]|]. split; [exact G20|]. split; [exact G8 | exact G21]. }
split; [rewrite (RG _ _ Q1); reflexivity|].
split; [rewrite (RG _ _ Q10); cbn [sv_denot]; rewrite Z.add_0_r, HE24, Z_to_bv_bv_unsigned; reflexivity|].
split; [rewrite (GK 25%bv ltac:(cbv; auto 20)); exact G25|].
split; [rewrite (GK 26%bv ltac:(cbv; auto 20)); exact G26|].
split; [rewrite (RG _ _ Q9); cbn [sv_denot]; rewrite Z.add_0_r, HE39, Z_to_bv_bv_unsigned; reflexivity|].
split. { apply (RZ_MEM_KEPT Lc Ac memc (ms_mem ms') mdc i ha pnew fimg imgl C _ i HHc ltac:(unfold sp, sp0 in *; lia) ltac:(unfold sp, sp0 in *; lia) Hfmt RZB RZM); [| | exact Hz].
- intros a Ha Hs _ _. apply KEEP; unfold sp, sp0 in *; lia.
- intros b n k Hbk Hk. pose proof (SEPc (b, n) Hbk) as Hs. cbn [fst snd] in Hs.
assert (Hbn : In (b, n) (blocks Lc Ac)) by (apply INB; apply in_app_iff; left; apply (keepb_sub r g bef beffmt s N img fmt rest); exact Hbk).
destruct (RNG b n Hbn ltac:(lia)) as [Rb0 Rb1]. apply KEEP; lia. }
split. { unfold structF. rewrite <- EhS, <- EuS. replace (ch_T C) with (ch_TS C) by exact ETS. cbn [obj_at LAY_Cht]. unfold field_ok. cbn [fst snd].
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32).
split. { split; [| exact R0]. rewrite Z.add_0_r. replace (ch_c C) with (ch_c C + 0) by lia. apply (VAL 0 8%N (SOff 32 0)); [exact C0 | cbn [sv_denot]; rewrite Z.add_0_r, HE32, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia]. }
split. { split; [| exact R1]. apply (VAL 8 8%N (SOff 33 0)); [exact C8 | cbn [sv_denot]; rewrite Z.add_0_r, HE33, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia]. }
split. { split; [| exact R2]. apply (VAL 16 8%N (SOff 34 0)); [exact C16 | cbn [sv_denot]; rewrite Z.add_0_r, HE34, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia]. }
split. { unfold rbk in *. destruct (Z.eqb_spec p1 0) as [Ep|Ep]; cbn [fst].
- split; [| exact R3]. apply (VAL 24 8%N (SOff 35 0)); [exact C24 | cbn [sv_denot]; rewrite Z.add_0_r, HE35, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia].
- specialize (Rp1 Ep). split; [| lia]. apply (VAL 24 8%N (SOff 27 0)); [exact C24 | cbn [sv_denot]; rewrite Z.add_0_r, HE27, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia]. }
split. { unfold rbk in *. destruct (Z.eqb_spec x1 0) as [Ex|Ex]; cbn [fst].
- split; [| exact R4]. apply (VAL 32 8%N (SOff 36 0)); [exact C32 | cbn [sv_denot]; rewrite Z.add_0_r, HE36, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia].
- specialize (Rx1 Ex). split; [| lia]. apply (VAL 32 8%N (SOff 22 0)); [exact C32 | cbn [sv_denot]; rewrite Z.add_0_r, HE22, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia]. }
split. { split; [| exact R5]. apply (VAL 40 4%N (SOff 37 0)); [exact C40 | cbn [sv_denot]; rewrite Z.add_0_r, HE37, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia]. }
split. { split; [| exact R6]. apply (VAL 44 4%N (SOff 38 0)); [exact C44 | cbn [sv_denot]; rewrite Z.add_0_r, HE38, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia]. }
exact I. }
exact RZB. }
assert (WRS : forall a, ch_c C + 24 <= a < ch_c C + 40 -> wr_byte RGBA_STK (sp0 regs0) (FPfoot r g bef beffmt s N) (blocks L A) (blocks Lc Ac) a).
{ intros a Ha. apply (wr_byte_tmp API L A regs0 r g bef beffmt s N img fmt rest Lc Ac memc mdc
([(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE); (ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T)] ++ [rbk (ch_p C, 3 * T) p1 (3 * T'); rbk (ch_x C, 4 * T) x1 (4 * T')] ++ optb h1 (3 * T') ++ optb u1 T' ++ optb f1 (4 * T'))
(ch_c C) CHT_SIZE a HHc); [| exact HB0 | apply in_app_iff; right; apply in_app_iff; left; left; reflexivity | unfold CHT_SIZE; lia | unfold CHT_SIZE; lia].
unfold rz_blocks, keepb in RZB. rewrite <- !app_assoc in RZB. rewrite <- ?app_assoc. exact RZB. }
assert (WROK : wr_ok E (ss_mem (ssF true true)) RGBA_STK (sp0 regs0) (FPfoot r g bef beffmt s N) (blocks L A) (blocks Lc Ac)).
{ cbn [ss_mem ssF]. eapply wr_ok_cons_gen; [reflexivity | exact HU20 | cbn [r_wlo r_whi]; intros a Ha; apply WRS; exact Ha |]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
destruct (Z.eqb_spec p1 0) as [Zp|Zp]; destruct (Z.eqb_spec x1 0) as [Zx|Zx].
all: [> pose proof (MKS true true ltac:(split; auto) ltac:(split; auto)) as HS
| pose proof (MKS true false ltac:(split; auto) ltac:(split; [intros X; discriminate X | intros X; exfalso; exact (Zx X)])) as HS
| pose proof (MKS false true ltac:(split; [intros X; discriminate X | intros X; exfalso; exact (Zp X)]) ltac:(split; auto)) as HS
| pose proof (MKS false false ltac:(split; [intros X; discriminate X | intros X; exfalso; exact (Zp X)]) ltac:(split; [intros X; discriminate X | intros X; exfalso; exact (Zx X)])) as HS ].
all: jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_free; [exact WROK|]; cbn [ms_mem mkst] in HF.
all: try rewrite (proj2 (Z.eqb_eq p1 0) Zp) in ARR; try rewrite (proj2 (Z.eqb_neq p1 0) Zp) in ARR; try rewrite (proj2 (Z.eqb_eq x1 0) Zx) in ARR; try rewrite (proj2 (Z.eqb_neq x1 0) Zx) in ARR; cbv iota in ARR.
all: apply (ARR _ _ _ HS eq_refl eq_refl HJ HF eq_refl eq_refl); [in_chunks | in_chunks | in_chunks | in_chunks | in_chunks | in_chunks | in_chunks | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity].
Qed.
End h.
Section l.
Variables (i ha : Z) (pnew fimg : Z) (imgl : list Z) (C : cht) (T' : Z).
Hypothesis KNEXT : forall regs1 Lc Ac memc mdc p1 x1 u1 f1, at_F1 regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 u1 f1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_F1) memc (seg_rom ubs2segs)) mdc) POST.
Theorem FS_stretch : forall regs1 Lc Ac memc mdc p1 x1 h1 u1 f1, at_FS regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 ubs2_A_free) memc (seg_rom ubs2segs)) mdc) POST.
Proof.
intros regs1 Lc Ac memc mdc p1 x1 h1 u1 f1 HAT.
destruct HAT as (HINV & HRZF & ((G2 & G3 & G4) & G20 & G8 & G21) & G1 & G10 & G25 & G26 & G9 & RZM & RZS & RZB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbf & HB0).
pose proof (RZ_MEM_HT _ _ _ _ _ _ _ RZM) as (Hinv & HT & Hch & HTlt). pose proof (RZ_MEM_ZSUM _ _ _ _ _ _ _ RZM) as Hz.
pose proof HRZF as (Hfmt & Hi & Hha & ET').
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
pose proof (ts_chain_ok _ Hch) as (RT1 & RT2 & RT3).
pose proof (resize_next (ch_T C) Hch HTlt) as (Hch' & HTT' & (RT1' & RT2' & RT3')). rewrite <- ET' in Hch', HTT', RT1', RT2', RT3'.
set (T := ch_T C) in *.
assert (RZB' : Permutation (blocks Lc Ac) ((KEEPB pnew fimg C ++ [rbk (ch_p C, 3 * ch_T C) p1 (3 * T'); rbk (ch_x C, 4 * ch_T C) x1 (4 * T')] ++ optb u1 T' ++ optb f1 (4 * T')) ++ optb h1 (3 * T'))).
{ eapply Permutation_trans; [exact RZB|]. unfold keepb. rewrite <- !app_assoc. repeat apply Permutation_app_head. eapply Permutation_trans; [apply Permutation_app_comm|]. rewrite <- app_assoc. apply Permutation_refl. }
assert (HBq : Permutation (blocks Lc Ac) (optb h1 (3 * T') ++ (KEEPB pnew fimg C ++ [rbk (ch_p C, 3 * ch_T C) p1 (3 * T'); rbk (ch_x C, 4 * ch_T C) x1 (4 * T')] ++ optb u1 T' ++ optb f1 (4 * T')))).
{ eapply Permutation_trans; [exact RZB' | apply Permutation_app_comm]. }
assert (HFPq : h1 <> 0 -> In (h1, 3 * T') (blocks L A) -> forall i0, 0 <= i0 < 3 * T' -> inFP (FPfoot r g bef beffmt s N) (h1 + i0)).
{ intros Hnz Hin0 i0 Hi0. exfalso.
apply (tmp_not_entry API L A Lc Ac memc mdc (h1, 3 * T') BASE0 (([(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE); (ch_f C, 4 * ch_T C); (ch_h C, 3 * ch_T C); (ch_u C, ch_T C)] ++ [rbk (ch_p C, 3 * ch_T C) p1 (3 * T'); rbk (ch_x C, 4 * ch_T C) x1 (4 * T')] ++ optb u1 T' ++ optb f1 (4 * T')) ++ optb h1 (3 * T')) HHc); [| exact HB0 | | cbn; lia | exact Hin0].
- unfold keepb in RZB'. rewrite <- !app_assoc in RZB'. rewrite <- !app_assoc. exact RZB'.
- apply in_app_iff. right. unfold optb. destruct (Z.eqb_spec h1 0); [lia|]. left. reflexivity. }
set (E := Ereg regs1 []).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (Hsp16 : SP mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok ubs2segs E (mkSS ubs2_A_free sr_atoms [] None (mkFacts [] [] [])) (mkst regs1 (Z_to_bv 64 ubs2_A_free) memc (seg_rom ubs2segs))).
{ subst E. apply entry_st_ok; [vm_compute; reflexivity | constructor | exact I | exact I]. }
assert (EA0 : env_agree 32 (Ereg regs1 []) E) by (subst E; apply env_agree_refl).
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 ubs2_A_free) memc (seg_rom ubs2segs))) in HJ. clearbody E.
pose proof G10 as Ma0. pose proof G2 as Mq2. pose proof G4 as Mq4. rewrite Htp0 in Mq4. pose proof G1 as Mq1.
assert (Em : ms_mem (mkst regs1 (Z_to_bv 64 ubs2_A_free) memc (seg_rom ubs2segs)) = memc) by reflexivity.
assert (GK : forall rr : reg, In rr [2; 3; 4; 8; 20; 21; 25; 26; 9]%bv -> getr (ms_regs (mkst regs1 (Z_to_bv 64 ubs2_A_free) memc (seg_rom ubs2segs))) rr = getr regs1 rr) by (intros; reflexivity).
change (mkst regs1 (Z_to_bv 64 ubs2_A_free) memc (seg_rom ubs2segs)) with (mkst regs1 (Z_to_bv 64 ubs2_A_free) memc (seg_rom ubs2segs)).
eapply SR_bind.
{ eapply (jfree_opt _ _ LAWS ubs2_errno_low IMG (aa_free API) (aa_free_null API)) with (p := h1) (n := 3 * T') (spc := SP);
[ exact HS | reflexivity | reflexivity | exact HJ | exact HBq | exact Ma0
| exact Mq2 | unfold sp, sp0 in *; lia | exact Hsp16 | unfold sp, sp0 in *; lia | unfold sp, sp0 in *; lia | exact Mq4 | exact Mq1 | apply ret_ok_even; vm_compute; reflexivity | exact HFPq ]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HB2 & Hkeep2 & Hhi2). clear HJ.
cbn [ms_regs ms_mem mkst] in HP2, HB2, Hkeep2, Hhi2, HJ2.
change (ms_segs ubs2_msyms) with ubs2segs in Hkeep2, Hhi2.
pose proof (proj1 HJ2) as HH2.
assert (KH2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> SP <= a -> mbyte ubs2segs mem2 a = mbyte ubs2segs memc a).
{ intros a Ha Hs. apply (proj1 (Hhi2 a Ha ltac:(lia))). }
assert (KB2 : forall b m k, In (b, m) (KEEPB pnew fimg C) -> 0 <= k < m -> mbyte ubs2segs mem2 (b + k) = mbyte ubs2segs memc (b + k)).
{ intros b m k Hb Hk. apply (Hkeep2 b m k); [| exact Hk]. eapply Permutation_in; [apply Permutation_sym; exact HB2|]. apply in_app_iff. left. exact Hb. }
change (Z_to_bv 64 83948) with (Z_to_bv 64 PC_F1). change (ms_segs ubs2_msyms) with ubs2segs.
apply (KNEXT regs2 L2 A2 mem2 md2 p1 x1 u1 f1). unfold at_F1.
assert (RP : forall rr : reg, reg_in rr CLOB = false -> getr regs2 rr = getr (ms_regs (mkst regs1 (Z_to_bv 64 ubs2_A_free) memc (seg_rom ubs2segs))) rr) by (intros rr Hrr; exact (regs_preserved_frame _ _ HP2 rr Hrr)).
cbn [ms_regs mkst] in RP.
split. { pose proof HB2 as HB2'. unfold keepb in HB2'. rewrite <- !app_assoc in HB2'. apply (RINV_CALL Lc Ac memc mem2 mdc L2 A2 md2 _ HINV HJ2 HB2'). intros a Ha Hs. apply KH2; [exact Ha | lia]. }
split; [exact HRZF|].
split. { unfold f_regs, rgba_regs. rewrite !RP by (vm_compute; reflexivity).
split; [split; [exact G2 | split; [exact G3 | exact G4]]|]. repeat (split; [assumption|]). exact G21. }
split; [rewrite RP by (vm_compute; reflexivity); exact G25|].
split; [rewrite RP by (vm_compute; reflexivity); exact G26|].
split; [rewrite RP by (vm_compute; reflexivity); exact G9|].
split. { apply (RZ_MEM_KEPT Lc Ac memc mem2 mdc i ha pnew fimg imgl C _ i HHc ltac:(unfold sp, sp0 in *; lia) ltac:(unfold sp, sp0 in *; lia) Hfmt RZB RZM); [| intros b m k Hb Hk; exact (KB2 b m k (keepb_sub r g bef beffmt s N img fmt rest _ _ _ _ Hb) Hk) | exact Hz].
intros a Ha Hs _ _. apply KH2; [exact Ha | exact Hs]. }
split. { unfold structF in RZS |- *. eapply (obj_at_transport_range ubs2segs _ _ _ _ _ CHT_SIZE); [exact RZS | reflexivity |]. intros k Hk.
apply (KB2 (ch_c C) CHT_SIZE k); [| exact Hk]. unfold keepb. apply in_app_iff. right. apply in_app_iff. right. left. reflexivity. }
unfold rz_blocks. eapply Permutation_trans; [exact HB2|]. rewrite <- ?app_assoc. apply Permutation_refl.
Qed.
End l.
Section t.
Variables (i ha : Z) (pnew fimg : Z) (imgl : list Z) (C : cht) (T' : Z).
Hypothesis KNEXT : forall regs1 Lc Ac memc mdc p1 x1 f1, at_F2 regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 f1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_F2) memc (seg_rom ubs2segs)) mdc) POST.
Theorem F1_stretch : forall regs1 Lc Ac memc mdc p1 x1 u1 f1, at_F1 regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 u1 f1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_F1) memc (seg_rom ubs2segs)) mdc) POST.
Proof.
intros regs1 Lc Ac memc mdc p1 x1 u1 f1 HAT.
destruct HAT as (HINV & HRZF & ((G2 & G3 & G4) & G20 & G8 & G21) & G25 & G26 & G9 & RZM & RZS & RZB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbf & HB0).
pose proof (RZ_MEM_HT _ _ _ _ _ _ _ RZM) as (Hinv & HT & Hch & HTlt). pose proof (RZ_MEM_ZSUM _ _ _ _ _ _ _ RZM) as Hz.
pose proof HRZF as (Hfmt & Hi & Hha & ET').
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
pose proof (ts_chain_ok _ Hch) as (RT1 & RT2 & RT3).
pose proof (resize_next (ch_T C) Hch HTlt) as (Hch' & HTT' & (RT1' & RT2' & RT3')). rewrite <- ET' in Hch', HTT', RT1', RT2', RT3'.
set (T := ch_T C) in *.
assert (RZB' : Permutation (blocks Lc Ac) ((KEEPB pnew fimg C ++ [rbk (ch_p C, 3 * ch_T C) p1 (3 * T'); rbk (ch_x C, 4 * ch_T C) x1 (4 * T')] ++ optb f1 (4 * T')) ++ optb u1 (T'))).
{ eapply Permutation_trans; [exact RZB|]. unfold keepb. rewrite <- !app_assoc. repeat apply Permutation_app_head. apply Permutation_app_comm. }
assert (HBq : Permutation (blocks Lc Ac) (optb u1 (T') ++ (KEEPB pnew fimg C ++ [rbk (ch_p C, 3 * ch_T C) p1 (3 * T'); rbk (ch_x C, 4 * ch_T C) x1 (4 * T')] ++ optb f1 (4 * T')))).
{ eapply Permutation_trans; [exact RZB' | apply Permutation_app_comm]. }
assert (HFPq : u1 <> 0 -> In (u1, T') (blocks L A) -> forall i0, 0 <= i0 < T' -> inFP (FPfoot r g bef beffmt s N) (u1 + i0)).
{ intros Hnz Hin0 i0 Hi0. exfalso.
apply (tmp_not_entry API L A Lc Ac memc mdc (u1, T') BASE0 (([(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE); (ch_f C, 4 * ch_T C); (ch_h C, 3 * ch_T C); (ch_u C, ch_T C)] ++ [rbk (ch_p C, 3 * ch_T C) p1 (3 * T'); rbk (ch_x C, 4 * ch_T C) x1 (4 * T')] ++ optb f1 (4 * T')) ++ optb u1 (T')) HHc); [| exact HB0 | | cbn; lia | exact Hin0].
- unfold keepb in RZB'. rewrite <- !app_assoc in RZB'. rewrite <- !app_assoc. exact RZB'.
- apply in_app_iff. right. unfold optb. destruct (Z.eqb_spec u1 0); [lia|]. left. reflexivity. }
set (E := Ereg regs1 []).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (Hsp16 : SP mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok ubs2segs E (mkSS PC_F1 sr_atoms [] None (mkFacts [] [] [])) (mkst regs1 (Z_to_bv 64 PC_F1) memc (seg_rom ubs2segs))).
{ subst E. apply entry_st_ok; [vm_compute; reflexivity | constructor | exact I | exact I]. }
assert (EA0 : env_agree 32 (Ereg regs1 []) E) by (subst E; apply env_agree_refl).
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_F1) memc (seg_rom ubs2segs))) in HJ. clearbody E.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_free. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (Em : ms_mem ms = memc) by (apply functional_extensionality; intros x; exact (frame_of_nil _ _ _ x HF)).
jreg HS (10%bv:reg) as Ma0. rewrite (HE 25%nat 25%bv eq_refl), G25 in Ma0.
jreg HS (2%bv:reg) as Mq2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Mq2.
jreg HS (4%bv:reg) as Mq4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Mq4.
jreg HS (1%bv:reg) as Mq1.
lazymatch type of HS with st_ok _ _ ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs2segs E ssf msf regs1 [] [2; 3; 4; 8; 20; 21; 26; 9]%bv HS EA0 ltac:(vm_compute; reflexivity)) as GK end.
eapply SR_bind.
{ eapply (jfree_opt _ _ LAWS ubs2_errno_low IMG (aa_free API) (aa_free_null API)) with (p := u1) (n := T') (spc := SP);
[ exact HS | reflexivity | reflexivity | exact HJ | exact HBq | exact Ma0
| exact Mq2 | unfold sp, sp0 in *; lia | exact Hsp16 | unfold sp, sp0 in *; lia | unfold sp, sp0 in *; lia | exact Mq4 | exact Mq1 | apply ret_ok_even; vm_compute; reflexivity | exact HFPq ]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HB2 & Hkeep2 & Hhi2). clear HJ.
cbn [ms_regs ms_mem mkst] in HP2, HB2, Hkeep2, Hhi2, HJ2.
change (ms_segs ubs2_msyms) with ubs2segs in Hkeep2, Hhi2. rewrite Em in Hkeep2, Hhi2.
pose proof (proj1 HJ2) as HH2.
assert (KH2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> SP <= a -> mbyte ubs2segs mem2 a = mbyte ubs2segs memc a).
{ intros a Ha Hs. apply (proj1 (Hhi2 a Ha ltac:(lia))). }
assert (KB2 : forall b m k, In (b, m) (KEEPB pnew fimg C) -> 0 <= k < m -> mbyte ubs2segs mem2 (b + k) = mbyte ubs2segs memc (b + k)).
{ intros b m k Hb Hk. apply (Hkeep2 b m k); [| exact Hk]. eapply Permutation_in; [apply Permutation_sym; exact HB2|]. apply in_app_iff. left. exact Hb. }
change (Z_to_bv 64 83956) with (Z_to_bv 64 PC_F2). change (ms_segs ubs2_msyms) with ubs2segs.
apply (KNEXT regs2 L2 A2 mem2 md2 p1 x1 f1). unfold at_F2.
assert (RP : forall rr : reg, reg_in rr CLOB = false -> getr regs2 rr = getr (ms_regs ms) rr) by (intros rr Hrr; exact (regs_preserved_frame _ _ HP2 rr Hrr)).
cbn [ms_regs mkst] in RP.
split. { pose proof HB2 as HB2'. unfold keepb in HB2'. rewrite <- !app_assoc in HB2'. apply (RINV_CALL Lc Ac memc mem2 mdc L2 A2 md2 _ HINV HJ2 HB2'). intros a Ha Hs. apply KH2; [exact Ha | lia]. }
split; [exact HRZF|].
split. { unfold f_regs, rgba_regs. rewrite !RP by (vm_compute; reflexivity).
rewrite (GK 2%bv ltac:(cbv; auto 20)), (GK 3%bv ltac:(cbv; auto 20)), (GK 4%bv ltac:(cbv; auto 20)), (GK 8%bv ltac:(cbv; auto 20)), (GK 20%bv ltac:(cbv; auto 20)),
(GK 21%bv ltac:(cbv; auto 20)).
split; [split; [exact G2 | split; [exact G3 | exact G4]]|]. repeat (split; [assumption|]). exact G21. }
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 26%bv ltac:(cbv; auto 20)); exact G26|].
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 9%bv ltac:(cbv; auto 20)); exact G9|].
split. { apply (RZ_MEM_KEPT Lc Ac memc mem2 mdc i ha pnew fimg imgl C _ i HHc ltac:(unfold sp, sp0 in *; lia) ltac:(unfold sp, sp0 in *; lia) Hfmt RZB RZM); [| intros b m k Hb Hk; exact (KB2 b m k (keepb_sub r g bef beffmt s N img fmt rest _ _ _ _ Hb) Hk) | exact Hz].
intros a Ha Hs _ _. apply KH2; [exact Ha | exact Hs]. }
split. { unfold structF in RZS |- *. eapply (obj_at_transport_range ubs2segs _ _ _ _ _ CHT_SIZE); [exact RZS | reflexivity |]. intros k Hk.
apply (KB2 (ch_c C) CHT_SIZE k); [| exact Hk]. unfold keepb. apply in_app_iff. right. apply in_app_iff. right. left. reflexivity. }
unfold rz_blocks. eapply Permutation_trans; [exact HB2|]. rewrite <- ?app_assoc. apply Permutation_refl.
Qed.
End t.
Section u.
Variables (i ha : Z) (pnew fimg : Z) (imgl : list Z) (C : cht) (T' : Z).
Hypothesis KNEXT : forall regs1 Lc Ac memc mdc p1 x1, at_F3 regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_F3) memc (seg_rom ubs2segs)) mdc) POST.
Theorem F2_stretch : forall regs1 Lc Ac memc mdc p1 x1 f1, at_F2 regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 f1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_F2) memc (seg_rom ubs2segs)) mdc) POST.
Proof.
intros regs1 Lc Ac memc mdc p1 x1 f1 HAT.
destruct HAT as (HINV & HRZF & ((G2 & G3 & G4) & G20 & G8 & G21) & G26 & G9 & RZM & RZS & RZB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbf & HB0).
pose proof (RZ_MEM_HT _ _ _ _ _ _ _ RZM) as (Hinv & HT & Hch & HTlt). pose proof (RZ_MEM_ZSUM _ _ _ _ _ _ _ RZM) as Hz.
pose proof HRZF as (Hfmt & Hi & Hha & ET').
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
pose proof (ts_chain_ok _ Hch) as (RT1 & RT2 & RT3).
pose proof (resize_next (ch_T C) Hch HTlt) as (Hch' & HTT' & (RT1' & RT2' & RT3')). rewrite <- ET' in Hch', HTT', RT1', RT2', RT3'.
set (T := ch_T C) in *.
assert (RZB' : Permutation (blocks Lc Ac) ((KEEPB pnew fimg C ++ [rbk (ch_p C, 3 * ch_T C) p1 (3 * T'); rbk (ch_x C, 4 * ch_T C) x1 (4 * T')]) ++ optb f1 (4 * T'))).
{ eapply Permutation_trans; [exact RZB|]. unfold keepb. rewrite <- !app_assoc. repeat apply Permutation_app_head. apply Permutation_refl. }
assert (HBq : Permutation (blocks Lc Ac) (optb f1 (4 * T') ++ (KEEPB pnew fimg C ++ [rbk (ch_p C, 3 * ch_T C) p1 (3 * T'); rbk (ch_x C, 4 * ch_T C) x1 (4 * T')]))).
{ eapply Permutation_trans; [exact RZB' | apply Permutation_app_comm]. }
assert (HFPq : f1 <> 0 -> In (f1, 4 * T') (blocks L A) -> forall i0, 0 <= i0 < 4 * T' -> inFP (FPfoot r g bef beffmt s N) (f1 + i0)).
{ intros Hnz Hin0 i0 Hi0. exfalso.
apply (tmp_not_entry API L A Lc Ac memc mdc (f1, 4 * T') BASE0 (([(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE); (ch_f C, 4 * ch_T C); (ch_h C, 3 * ch_T C); (ch_u C, ch_T C)] ++ [rbk (ch_p C, 3 * ch_T C) p1 (3 * T'); rbk (ch_x C, 4 * ch_T C) x1 (4 * T')]) ++ optb f1 (4 * T')) HHc); [| exact HB0 | | cbn; lia | exact Hin0].
- unfold keepb in RZB'. rewrite <- !app_assoc in RZB'. rewrite <- !app_assoc. exact RZB'.
- apply in_app_iff. right. unfold optb. destruct (Z.eqb_spec f1 0); [lia|]. left. reflexivity. }
assert (Rf1 : 0 <= f1 < 2 ^ 64).
{ destruct (Z.eqb_spec f1 0) as [->|Hnz]; [lia|].
assert (Hin : In (f1, 4 * T') (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HBq|]; apply in_app_iff; left; unfold optb; destruct (Z.eqb_spec f1 0); [lia | left; reflexivity]).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc f1 (4 * T') HHc Hin ltac:(lia)) as (Q0 & Q1 & _). lia. }
set (E := Ereg regs1 (map (Z_to_bv 64) [f1] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 f1) by (subst E; apply (Ereg_vals regs1 _ [] 0%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = SP) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (Hsp16 : SP mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok ubs2segs E (mkSS PC_F2 sr_atoms [] None (mkFacts [] [] [])) (mkst regs1 (Z_to_bv 64 PC_F2) memc (seg_rom ubs2segs))).
{ subst E. apply entry_st_ok; [vm_compute; reflexivity | constructor | exact I | exact I]. }
assert (EA0 : env_agree 32 (Ereg regs1 []) E).
{ subst E. split; [intros n Hn; rewrite !ew_Ereg_lt by exact Hn; reflexivity | reflexivity]. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_F2) memc (seg_rom ubs2segs))) in HJ. clearbody E.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_free. { apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (Em : ms_mem ms = memc) by (apply functional_extensionality; intros x; exact (frame_of_nil _ _ _ x HF)).
jreg HS (10%bv:reg) as Ma0. rewrite (HE 26%nat 26%bv eq_refl), G26 in Ma0.
jreg HS (2%bv:reg) as Mq2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Mq2.
jreg HS (4%bv:reg) as Mq4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Mq4.
jreg HS (1%bv:reg) as Mq1.
lazymatch type of HS with st_ok _ _ ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs2segs E ssf msf regs1 [] [2; 3; 4; 8; 20; 21; 9]%bv HS EA0 ltac:(vm_compute; reflexivity)) as GK end.
eapply SR_bind.
{ eapply (jfree_opt _ _ LAWS ubs2_errno_low IMG (aa_free API) (aa_free_null API)) with (p := f1) (n := 4 * T') (spc := SP);
[ exact HS | reflexivity | reflexivity | exact HJ | exact HBq | exact Ma0
| exact Mq2 | unfold sp, sp0 in *; lia | exact Hsp16 | unfold sp, sp0 in *; lia | unfold sp, sp0 in *; lia | exact Mq4 | exact Mq1 | apply ret_ok_even; vm_compute; reflexivity | exact HFPq ]. }
cbv beta. intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HB2 & Hkeep2 & Hhi2). clear HJ.
cbn [ms_regs ms_mem mkst] in HP2, HB2, Hkeep2, Hhi2, HJ2.
change (ms_segs ubs2_msyms) with ubs2segs in Hkeep2, Hhi2. rewrite Em in Hkeep2, Hhi2.
pose proof (proj1 HJ2) as HH2.
assert (KH2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> SP <= a -> mbyte ubs2segs mem2 a = mbyte ubs2segs memc a).
{ intros a Ha Hs. apply (proj1 (Hhi2 a Ha ltac:(lia))). }
assert (KB2 : forall b m k, In (b, m) (KEEPB pnew fimg C) -> 0 <= k < m -> mbyte ubs2segs mem2 (b + k) = mbyte ubs2segs memc (b + k)).
{ intros b m k Hb Hk. apply (Hkeep2 b m k); [| exact Hk]. eapply Permutation_in; [apply Permutation_sym; exact HB2|]. apply in_app_iff. left. exact Hb. }
change (Z_to_bv 64 83964) with (Z_to_bv 64 PC_F3). change (ms_segs ubs2_msyms) with ubs2segs.
apply (KNEXT regs2 L2 A2 mem2 md2 p1 x1). unfold at_F3.
assert (RP : forall rr : reg, reg_in rr CLOB = false -> getr regs2 rr = getr (ms_regs ms) rr) by (intros rr Hrr; exact (regs_preserved_frame _ _ HP2 rr Hrr)).
cbn [ms_regs mkst] in RP.
split. { pose proof HB2 as HB2'. unfold keepb in HB2'. rewrite <- !app_assoc in HB2'. apply (RINV_CALL Lc Ac memc mem2 mdc L2 A2 md2 _ HINV HJ2 HB2'). intros a Ha Hs. apply KH2; [exact Ha | lia]. }
split; [exact HRZF|].
split. { unfold f_regs, rgba_regs. rewrite !RP by (vm_compute; reflexivity).
rewrite (GK 2%bv ltac:(cbv; auto 20)), (GK 3%bv ltac:(cbv; auto 20)), (GK 4%bv ltac:(cbv; auto 20)), (GK 8%bv ltac:(cbv; auto 20)), (GK 20%bv ltac:(cbv; auto 20)),
(GK 21%bv ltac:(cbv; auto 20)).
split; [split; [exact G2 | split; [exact G3 | exact G4]]|]. repeat (split; [assumption|]). exact G21. }
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 9%bv ltac:(cbv; auto 20)); exact G9|].
split. { apply (RZ_MEM_KEPT Lc Ac memc mem2 mdc i ha pnew fimg imgl C _ i HHc ltac:(unfold sp, sp0 in *; lia) ltac:(unfold sp, sp0 in *; lia) Hfmt RZB RZM); [| intros b m k Hb Hk; exact (KB2 b m k (keepb_sub r g bef beffmt s N img fmt rest _ _ _ _ Hb) Hk) | exact Hz].
intros a Ha Hs _ _. apply KH2; [exact Ha | exact Hs]. }
split. { unfold structF in RZS |- *. eapply (obj_at_transport_range ubs2segs _ _ _ _ _ CHT_SIZE); [exact RZS | reflexivity |]. intros k Hk.
apply (KB2 (ch_c C) CHT_SIZE k); [| exact Hk]. unfold keepb. apply in_app_iff. right. apply in_app_iff. right. left. reflexivity. }
unfold rz_blocks. eapply Permutation_trans; [exact HB2|]. rewrite <- ?app_assoc. apply Permutation_refl.
Qed.
End u.
Section w.
Variables (i ha : Z) (pnew fimg : Z) (imgl : list Z) (C : cht) (T' : Z).
Hypothesis KXB : forall regs1 Lc Ac memc mdc, AT_XB regs1 Lc Ac memc mdc pnew fimg ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_XB) memc (seg_rom ubs2segs)) mdc) POST.
Lemma optfp_nz' : forall p n, p <> 0 -> optfp p n = [(p, p + n)].
Proof. intros p n Hp. unfold optfp. destruct (Z.eqb_spec p 0); [lia | reflexivity]. Qed.
Lemma optb_nz' : forall p n, p <> 0 -> optb p n = [(p, n)].
Proof. intros p n Hp. unfold optb. destruct (Z.eqb_spec p 0); [lia | reflexivity]. Qed.
Theorem F3_stretch : forall regs1 Lc Ac memc mdc p1 x1, at_F3 regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_F3) memc (seg_rom ubs2segs)) mdc) POST.
Proof.
intros regs1 Lc Ac memc mdc p1 x1 HAT.
destruct HAT as (HINV & HRZF & ((G2 & G3 & G4) & G20 & G8 & G21) & G9 & RZM & RZS & RZB).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbf & HB0).
pose proof RZM as (Hslots & _ & _ & _ & _ & _ & _ & _ & Hfc & Hobj & Hcg & _ & Hpn & Hfi & _).
destruct Hslots as (M8 & M16 & M24 & M48).
pose proof (RZ_MEM_HT _ _ _ _ _ _ _ RZM) as (Hinv & HT & Hch & HTlt). pose proof (RZ_MEM_ZSUM _ _ _ _ _ _ _ RZM) as Hz.
pose proof HRZF as (Hfmt & Hi & Hha & ET').
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity. assert (HFSv : FREECHT_STK = 8208) by reflexivity.
pose proof (ts_chain_ok _ Hch) as (RT1 & RT2 & RT3).
pose proof (resize_next (ch_T C) Hch HTlt) as (Hch' & HTT' & (RT1' & RT2' & RT3')). rewrite <- ET' in Hch', HTT', RT1', RT2', RT3'.
set (T := ch_T C) in *.
set (pc := fst (rbk (ch_p C, 3 * T) p1 (3 * T'))) in *. set (npc := snd (rbk (ch_p C, 3 * T) p1 (3 * T'))).
set (xc := fst (rbk (ch_x C, 4 * T) x1 (4 * T'))) in *. set (nxc := snd (rbk (ch_x C, 4 * T) x1 (4 * T'))).
assert (Epc : rbk (ch_p C, 3 * T) p1 (3 * T') = (pc, npc)) by (subst pc npc; apply surjective_pairing).
assert (Exc : rbk (ch_x C, 4 * T) x1 (4 * T') = (xc, nxc)) by (subst xc nxc; apply surjective_pairing).
rewrite Epc, Exc in RZB.
set (tmp := (ch_c C, CHT_SIZE) :: [(ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T); (pc, npc); (xc, nxc)]).
set (keep2 := BASE0 ++ [(pnew, fmt * N); (fimg, N)]).
assert (HB' : Permutation (blocks Lc Ac) (keep2 ++ tmp)).
{ eapply Permutation_trans; [exact RZB|]. unfold keepb. subst keep2 tmp. rewrite <- !app_assoc. apply Permutation_refl. }
assert (INB : forall b, In b (keep2 ++ tmp) -> In b (blocks Lc Ac)) by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact HB' | exact Hb]).
assert (TMP : forall b, In b tmp -> 0 < snd b /\ In b (blocks Lc Ac) /\ ~ In b (blocks L A)).
{ intros [b n] Hb.
assert (Hn : 0 < n).
{ subst tmp. cbn [In] in Hb. unfold CHT_SIZE in Hb. subst npc nxc. unfold rbk in Hb.
destruct (p1 =? 0); destruct (x1 =? 0); cbn [snd] in Hb; decompose [or] Hb; try match goal with H : _ = (b, n) |- _ => injection H; intros; subst end; try lia; try contradiction. }
split; [exact Hn|]. split; [apply INB; apply in_app_iff; right; exact Hb|].
exact (tmp_not_entry API L A Lc Ac memc mdc (b, n) BASE0 ([(pnew, fmt * N); (fimg, N)] ++ tmp) HHc ltac:(subst keep2; rewrite <- app_assoc in HB'; exact HB') HB0 ltac:(apply in_app_iff; right; exact Hb) Hn). }
assert (NZ : forall b, In b tmp -> fst b <> 0).
{ intros [b n] Hb. destruct (TMP _ Hb) as (Hn & Hin & _). destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc b n HHc Hin Hn) as (R0 & _). cbn. lia. }
assert (Zc : ch_c C <> 0) by exact (NZ (ch_c C, CHT_SIZE) ltac:(subst tmp; cbn; auto)).
assert (Zf : ch_f C <> 0) by exact (NZ (ch_f C, 4 * T) ltac:(subst tmp; cbn; auto)).
assert (Zh : ch_h C <> 0) by exact (NZ (ch_h C, 3 * T) ltac:(subst tmp; cbn; auto)).
assert (Zu : ch_u C <> 0) by exact (NZ (ch_u C, T) ltac:(subst tmp; cbn; auto 10)).
assert (Zpc : pc <> 0) by exact (NZ (pc, npc) ltac:(subst tmp; cbn; auto 10)).
assert (Zxc : xc <> 0) by exact (NZ (xc, nxc) ltac:(subst tmp; cbn; auto 10)).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc (ch_c C) CHT_SIZE HHc ltac:(apply INB; apply in_app_iff; right; subst tmp; left; reflexivity) ltac:(unfold CHT_SIZE; lia)) as (Rc0 & Rc1 & _). unfold CHT_SIZE in Rc1.
assert (HfN : 0 < fmt * N) by (clear - Hfmt Hi; nia).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc pnew (fmt * N) HHc ltac:(apply INB; apply in_app_iff; left; subst keep2; apply in_app_iff; right; left; reflexivity) HfN) as (Rn0 & Rn1 & _).
destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc fimg N HHc ltac:(apply INB; apply in_app_iff; left; subst keep2; apply in_app_iff; right; right; left; reflexivity) ltac:(lia)) as (Rfi0 & Rfi1 & _).
set (E := Ereg regs1 (map (Z_to_bv 64) [pnew; fimg] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 pnew) by (subst E; apply (Ereg_vals regs1 _ [] 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 fimg) by (subst E; apply (Ereg_vals regs1 _ [] 1%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = SP) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (Hsp16 : SP mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok ubs2segs E (mkSS PC_F3 sr_atoms [YQ0b.mkRegion (Some 2%nat) 0 5168 0 0 [mkChunk 24 (CVal 8 (SOff 32%nat 0))]] None (mkFacts [(2%nat, mkAF CEIL_MIN (2^63) 4)] [] []))
(mkst regs1 (Z_to_bv 64 PC_F3) memc (seg_rom ubs2segs))).
{ subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [unfold sp, sp0 in *; lia|]. split; [unfold sp, sp0 in *; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ pnew); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. apply val_mem_word_mem. exact M24.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2. change (2 ^ 4) with 16. unfold sp, sp0 in *. repeat split; lia. }
assert (EA0 : env_agree 32 (Ereg regs1 []) E).
{ subst E. split; [intros n Hn; rewrite !ew_Ereg_lt by exact Hn; reflexivity | reflexivity]. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_F3) memc (seg_rom ubs2segs))) in HJ. clearbody E.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_free_col_hash_table. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (Em : ms_mem ms = memc) by (apply functional_extensionality; intros x; lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => exact (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF x) end).
jreg HS (10%bv:reg) as Hr10. rewrite (HE 20%nat 20%bv eq_refl), G20 in Hr10.
jreg HS (9%bv:reg) as Hr9. rewrite (HE 9%nat 9%bv eq_refl), G9 in Hr9.
jreg HS (18%bv:reg) as Hr18. rewrite HE32 in Hr18.
jreg HS (2%bv:reg) as Hr2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hr2.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hr4.
jreg HS (1%bv:reg) as Hr1.
lazymatch type of HS with st_ok _ _ ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs2segs E ssf msf regs1 [] [2; 3; 4; 8; 21]%bv HS EA0 ltac:(vm_compute; reflexivity)) as GK end.
assert (Hspms : spZ (ms_regs ms) = SP) by (unfold spZ; rewrite Hr2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (HBc : Permutation (blocks Lc Ac) ((ch_c C, CHT_SIZE) :: optb (ch_f C) (4 * T) ++ optb (ch_h C) (3 * T) ++ optb (ch_u C) T ++ optb pc npc ++ optb xc nxc ++ keep2)).
{ rewrite !optb_nz' by assumption. eapply Permutation_trans; [exact HB'|]. eapply Permutation_trans; [apply Permutation_app_comm|]. subst tmp. cbn [app]. apply Permutation_refl. }
eapply SR_bind.
{ eapply (jcall_tmp _ _ LAWS) with (STK1 := FREECHT_STK)
(FP1 := (ch_c C, ch_c C + CHT_SIZE) :: optfp (ch_f C) (4 * T) ++ optfp (ch_h C) (3 * T) ++ optfp (ch_u C) T ++ optfp pc npc ++ optfp xc nxc)
(K := fun L5 A5 (regs5 : bvmap 5 word) (mem5 : word -> option byte) (md5 : Model) => Permutation (blocks L5 A5) keep2);
[ exact HS | reflexivity | exact HJ | exact Hr1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hspms; exact Hsp16 | lia
| rewrite Hspms; unfold sp, sp0 in *; lia
| rewrite Hspms; unfold sp, sp0 in *; lia | exact Hr4 | ].
- intros HPRE1. rewrite Em in HPRE1 |- *. eapply SR_mono.
{ unfold rz_struct, structF in RZS. eapply (FCHT fx Lc Ac (ms_regs ms) memc mdc (ch_c C) (ch_f C) (ch_h C) (ch_u C) pc xc (ht_cnt (ch_H C)) T (4 * T) (3 * T) T npc nxc keep2 HPRE1 Hr10 RZS HBc). }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJc5 & HP5 & HB5).
exists L5, A5, regs5, mem5, md5. split; [rewrite Hr1; reflexivity|]. split; [exact HJc5|]. split; [exact HP5 | exact HB5].
- intros a Ha. right. rewrite !optfp_nz' in Ha by assumption.
destruct Ha as (rg & Hin & Hr). cbn [In app] in Hin.
assert (Hx : exists b, In b tmp /\ fst b <= a < fst b + snd b).
{ subst tmp. decompose [or] Hin; try contradiction; subst rg; cbn [fst snd] in Hr;
lazymatch type of Hr with ?b <= a < _ + ?n => exists (b, n) end; (split; [cbn [In]; repeat (first [left; reflexivity | right]) | cbn [fst snd]; exact Hr]). }
destruct Hx as ([b n] & Hb & Hab). destruct (TMP _ Hb) as (_ & H1 & H2). exists b, n. cbn [fst snd] in Hab. auto. }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJ5 & HJc5 & HP5 & HB5). clear HJ.
cbn [ms_regs ms_mem mkst] in HJc5, HP5, HJ5.
rewrite Em, Hspms in HJc5. pose proof (proj1 HJ5) as HH5.
assert (HI : forall x0, alloc_ceiling <= x0 < 2 ^ 64 -> SP <= x0 -> mbyte ubs2segs mem5 x0 = mbyte ubs2segs memc x0).
{ intros x0 Hx Hsx. apply (journal_high _ _ _ _ _ _ _ _ _ _ _ _ _ HJc5 x0 Hx). lia. }
assert (Hkeep' : forall b m k, In (b, m) keep2 -> 0 <= k < m -> mbyte ubs2segs mem5 (b + k) = mbyte ubs2segs memc (b + k)).
{ intros b m k Hbm Hk. apply (journal_kept_live _ _ LAWS _ _ _ _ _ _ _ _ _ _ _ HJc5 HHc) with (m := m); [| apply INB; apply in_app_iff; left; exact Hbm | eapply Permutation_in; [apply Permutation_sym; exact HB5 | exact Hbm] | exact Hk].
intros lo hi Hin. rewrite !optfp_nz' in Hin by assumption. cbn [In app] in Hin.
assert (Hx : exists n, hi = lo + n /\ In (lo, n) tmp).
{ subst tmp. decompose [or] Hin; try contradiction;
match goal with H : _ = (lo, hi) |- _ => injection H as <- <- end; (eexists; split; [reflexivity | cbn [In]; repeat (first [left; reflexivity | right])]). }
destruct Hx as (n & -> & Hbn). exists n. split; [lia|]. destruct (TMP _ Hbn) as (Hn0 & H1 & H2). split; [exact H1|].
intros H5. assert (Hk2 : In (lo, n) keep2) by (eapply Permutation_in; [exact HB5 | exact H5]).
destruct (in_split _ _ Hbn) as (t1 & t2 & Et).
apply (perm_block_once API Lc Ac memc mdc (lo, n) (keep2 ++ t1) t2 HHc); [| exact Hn0 | apply in_app_iff; left; apply in_app_iff; left; exact Hk2].
rewrite <- app_assoc. rewrite <- Et. exact HB'. }
assert (RP : forall rr : reg, reg_in rr CLOB = false -> getr regs5 rr = getr (ms_regs ms) rr) by (intros rr Hrr; exact (regs_preserved_frame _ _ HP5 rr Hrr)).
change (Z_to_bv 64 82592) with (Z_to_bv 64 PC_XB). change (ms_segs ubs2_msyms) with ubs2segs.
apply (KXB regs5 L5 A5 mem5 md5). unfold at_XB.
split. { pose proof HB5 as HB5'. subst keep2. apply (RINV_CALL Lc Ac memc mem5 mdc L5 A5 md5 _ HINV HJ5 HB5'). intros a Ha Hs. apply HI; [exact Ha | lia]. }
split. { unfold rgba_regs. rewrite !RP by (vm_compute; reflexivity).
rewrite (GK 2%bv ltac:(cbv; auto 20)), (GK 3%bv ltac:(cbv; auto 20)), (GK 4%bv ltac:(cbv; auto 20)). split; [exact G2 | split; [exact G3 | exact G4]]. }
split; [exact Hfmt|].
split; [rewrite RP by (vm_compute; reflexivity); exact Hr18|].
split; [rewrite RP by (vm_compute; reflexivity); exact Hr9|].
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 21%bv ltac:(cbv; auto 20)); exact G21|].
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 8%bv ltac:(cbv; auto 20)); exact G8|].
split. { unfold rgb_obj in Hobj |- *. eapply (obj_at_transport_range ubs2segs _ _ _ _ _ RGB_SIZE); [exact Hobj | reflexivity |].
intros k Hk. apply (Hkeep' r RGB_SIZE k); [subst keep2; apply in_app_iff; left; left; reflexivity | exact Hk]. }
split. { eapply (cgif_at_kept _ _ g s N keep2); [| exact Hcg | exact Hkeep']. subst keep2. unfold BASE. cbn [app]. rewrite <- !app_assoc. apply Permutation_middle. }
split; [exact Hpn|]. split; [exact Hfi|]. subst keep2. exact HB5.
Qed.
End w.
End d.
End c.
