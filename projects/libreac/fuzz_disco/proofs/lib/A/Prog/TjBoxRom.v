(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of check_groupa on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACa2.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACb8.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChf.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CheckGroupaWalk.v, with its module paths and module names changed; 906 of its 982 lines of code are new or changed and 1111 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/TjBox.v, with its module paths and module names changed; 63 of its 163 lines of code are new or changed and 882 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YCkd.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaRun PaShadow PaStep DiscoSyms DiscoList DiscoAddr DiscoPa.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaJournal DiscoPaLib YC1g YC1h YC81 YC4b DiscoFrame YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoBase YC1i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import TjSpec TjBase DiscoRo TjCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SetShadowDef ConstsViewDef StrlenDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import SbDec ReacBoxName.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
Definition tj_rbn_str (q sz : Z) (s : list Z) : Prop :=
rbn_ro q sz /\ Z.of_nat (length s) + 1 <= sz /\
IMG_LO + 64 <= q /\ q + sz + 64 <= IMG_TOP /\
Forall (fun c => 0 < c < 256) s /\ tj_rom_bytes q (s ++ [0]) /\
(forall x, q + Z.of_nat (length s) < x < q + Z.of_nat (length s) - (q + Z.of_nat (length s)) mod 8 + 8 ->
seg_rom SEGS (Z_to_bv 64 x) <> None).
Definition tj_rbn_word (a v : Z) : Prop :=
forall k, (k < 8)%nat -> seg_rom SEGS (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 (YO0f.le_byte v 8 k)).
Definition tj_rbn_rom : Prop :=
exists t1 t2 t3 : Z,
VAL (A_OBJ 26) mod 8 = 0 /\ In (VAL (A_OBJ 26), 24) disco_globs /\
IMG_LO + 64 <= VAL (A_OBJ 26) /\ VAL (A_OBJ 26) + 24 + 64 <= IMG_TOP /\
tj_rbn_word (VAL (A_OBJ 26)) t1 /\ tj_rbn_word (VAL (A_OBJ 26) + 8) t2 /\ tj_rbn_word (VAL (A_OBJ 26) + 16) t3 /\
tj_rbn_str t1 7 (bn_STEM 1) /\ tj_rbn_str t2 7 (bn_STEM 2) /\ tj_rbn_str t3 8 (bn_STEM 3) /\
tj_rbn_str (VAL (A_OBJ 27)) 5 (bn_STEM 0) /\
tj_rbn_str (VAL (A_OBJ 28)) 3 [32; 40] /\
tj_rbn_str (VAL (A_OBJ 29)) 7 [32; 105; 110; 32; 47; 32] /\
tj_rbn_str (VAL (A_OBJ 30)) 6 [32; 111; 117; 116; 41].
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis DRO : disco_ro_unowned B.
Hypothesis GM : globs_marked SEGS B disco_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Lemma tj_mc_consts : forall (W : world SEGS) mem,
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
consts_view SEGS MC_CONSTS_LO MC_CONSTS_HI W mem.
Proof.
intros W mem HRO a Ha. unfold MC_CONSTS_LO, MC_CONSTS_HI in Ha.
assert (Hin : In (0x10368, 32) disco_ro_ranges)
by (unfold disco_ro_ranges; apply in_or_app; right; cbn [disco_ro_extra In]; repeat (first [left; reflexivity | right])).
assert (Hall : In (0x10368, 32) disco_ro_all) by (unfold disco_ro_all; apply in_or_app; left; exact Hin).
exact (ro_bytes SEGS pa_relro_lo pa_relro_hi B _ 0x10368 32 a HRO (disco_ro_in_ro 0x10368 32 a Hall ltac:(lia))
(disco_ro_unowned_at B 0x10368 32 DRO Hin) ltac:(lia)).
Qed.
Hypothesis RBR : tj_rbn_rom.
Lemma tj_ro_ranges_glob : forall q sz, In (q, sz) disco_globs -> In (q, sz) disco_ro_ranges.
Proof. intros q sz Hin. unfold disco_ro_ranges. apply in_or_app. left. exact Hin. Qed.
Lemma tj_ro_all_glob : forall q sz, In (q, sz) disco_globs -> In (q, sz) disco_ro_all.
Proof. intros q sz Hin. unfold disco_ro_all. apply in_or_app. left. exact (tj_ro_ranges_glob q sz Hin). Qed.
Lemma tj_ro_aview : forall (W : world SEGS) mem q sz x,
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
In (q, sz) disco_globs -> q <= x < q + sz ->
aview SEGS (w_H W) mem x = option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 x)).
Proof.
intros W mem q sz x HRO Hin Hx. pose proof (tj_ro_ranges_glob q sz Hin) as Hr.
exact (ro_bytes SEGS pa_relro_lo pa_relro_hi B _ q sz x HRO (disco_ro_in_ro q sz x (tj_ro_all_glob q sz Hin) Hx)
(disco_ro_unowned_at B q sz DRO Hr) Hx).
Qed.
Lemma tj_ro_img : forall q sz x, In (q, sz) disco_globs -> q <= x < q + sz -> in_img SEGS x.
Proof.
intros q sz x Hin Hx.
destruct (pa_ro_ok q sz x (tj_ro_all_glob q sz Hin) Hx) as [(sg & Hs & _ & Hb) | Hrel].
- exists sg. split; [exact Hs | exact Hb].
- exact (pa_relro_img x Hrel).
Qed.
Lemma tj_mbyte_of_aview : forall (H : word -> bool) (mem : word -> option byte) x (b : byte),
aview SEGS H mem x = Some (bv_unsigned b) -> mbyte SEGS (mrestrict H mem) x = Some b.
Proof.
intros H mem x b Hv. unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H mem) x) as [b'|] eqn:E; cbn in Hv; [|discriminate].
injection Hv as Hv. f_equal. apply bv_eq. exact Hv.
Qed.
Lemma tj_word_ok : forall (W : world SEGS) mem q sz a v,
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
In (q, sz) disco_globs -> q <= a -> a + 8 <= q + sz ->
tj_rbn_word a v -> val_mem SEGS (mrestrict (w_H W) mem) a 8 v.
Proof.
intros W mem q sz a v HRO Hin H1 H2 Hw k Hk. apply tj_mbyte_of_aview.
rewrite (tj_ro_aview W mem q sz (a + Z.of_nat k) HRO Hin ltac:(lia)), (Hw k Hk). reflexivity.
Qed.
Lemma tj_rbn_stem_ok : forall ly S (W : world SEGS) mem md q sz s,
AR SEGS B ly S W mem md ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
tj_rbn_str q sz s -> rbn_stem W mem q s.
Proof.
intros ly S W mem md q sz s HAR HRO ((Hin & _) & Hlen & Hlo & Hhi & Hch & Hrom & Htl).
assert (Hq : 0 < q /\ q + sz + 64 <= 0x5fe000) by (unfold IMG_LO, IMG_TOP in *; lia).
destruct (ro_read_ok_glob _ _ disco_globs ly S W mem md q sz q (Z.of_nat (length s) + 1) GM Hin HV HAR
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold IMG_TOP in *; lia)) as [Hra Hhv].
assert (HG : garr8 SEGS (mrestrict (w_H W) mem) q (s ++ [0])).
{ intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
  assert (Hv : aview SEGS (w_H W) mem (q + Z.of_nat j) = Some (nth j (s ++ [0]) 0)).
  { rewrite (tj_ro_aview W mem q sz (q + Z.of_nat j) HRO Hin ltac:(lia)). apply Hrom.
    rewrite length_app. cbn [length]. lia. }
  exact (val_mem1_of_aview SEGS (w_H W) mem _ _ Hv). }
split; [|intros x Hx; exact (tj_ro_img q sz x Hin ltac:(lia))].
refine (conj Hch (conj HG (conj _ (conj _ (conj _ (conj _ (conj Hra (conj Hhv _)))))))).
- lia.
- lia.
- lia.
- left. unfold kLowMemEnd. lia.
- intros x Hx. unfold aview, mbyte.
  destruct (mrestrict (w_H W) mem (Z_to_bv 64 x)) as [b|]; [cbn [option_map]; discriminate|].
  pose proof (Htl x Hx) as Hn. destruct (seg_rom SEGS (Z_to_bv 64 x)) as [b|]; [cbn [option_map]; discriminate | contradiction].
Qed.
Lemma tj_rbn_lit_ok : forall (W : world SEGS) mem q s, rbn_stem W mem q s -> rbn_lit W mem q s.
Proof. intros W mem q s ((_ & HG & _ & _ & _ & _ & Hra & _) & Himg). exact (conj HG (conj Hra Himg)). Qed.
Lemma tj_rbn_img : forall ly S (W : world SEGS) mem md,
AR SEGS B ly S W mem md ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
rbn_img W mem.
Proof.
intros ly S W mem md HAR HRO.
destruct RBR as (t1 & t2 & t3 & H8 & Hin & Hlo & Hhi & Hw1 & Hw2 & Hw3 & Hs1 & Hs2 & Hs3 & Hs0 & Hl28 & Hl29 & Hl30).
pose proof (tj_rbn_stem_ok ly S W mem md _ _ _ HAR HRO Hs1) as St1.
pose proof (tj_rbn_stem_ok ly S W mem md _ _ _ HAR HRO Hs2) as St2.
pose proof (tj_rbn_stem_ok ly S W mem md _ _ _ HAR HRO Hs3) as St3.
pose proof (tj_rbn_stem_ok ly S W mem md _ _ _ HAR HRO Hs0) as St0.
pose proof (tj_rbn_lit_ok W mem _ _ (tj_rbn_stem_ok ly S W mem md _ _ _ HAR HRO Hl28)) as Lt28.
pose proof (tj_rbn_lit_ok W mem _ _ (tj_rbn_stem_ok ly S W mem md _ _ _ HAR HRO Hl29)) as Lt29.
pose proof (tj_rbn_lit_ok W mem _ _ (tj_rbn_stem_ok ly S W mem md _ _ _ HAR HRO Hl30)) as Lt30.
assert (R26 : rbn_ro (VAL (A_OBJ 26)) 24) by (split; [exact Hin | left; reflexivity]).
exists t1, t2, t3.
refine (conj H8 (conj _ (conj _ (conj _ (conj _ (conj _ (conj St1 (conj St2 (conj St3 (conj St0
(conj Lt28 (conj Lt29 (conj Lt30 (conj R26 (conj (proj1 Hs1) (conj (proj1 Hs2) (conj (proj1 Hs3)
(conj (proj1 Hs0) (conj (proj1 Hl28) (conj (proj1 Hl29) (proj1 Hl30))))))))))))))))))))).
- intros x Hx. exact (tj_ro_img _ _ x Hin Hx).
- exact (ro_usable_glob _ _ disco_globs ly S W mem md (VAL (A_OBJ 26)) 24 (VAL (A_OBJ 26)) 24 GM Hin HAR
(Z.le_refl _) (Z.le_refl _)).
- exact (tj_word_ok W mem (VAL (A_OBJ 26)) 24 (VAL (A_OBJ 26)) t1 HRO Hin ltac:(lia) ltac:(lia) Hw1).
- exact (tj_word_ok W mem (VAL (A_OBJ 26)) 24 (VAL (A_OBJ 26) + 8) t2 HRO Hin ltac:(lia) ltac:(lia) Hw2).
- exact (tj_word_ok W mem (VAL (A_OBJ 26)) 24 (VAL (A_OBJ 26) + 16) t3 HRO Hin ltac:(lia) ltac:(lia) Hw3).
Qed.
End h.
End f.
End d.
