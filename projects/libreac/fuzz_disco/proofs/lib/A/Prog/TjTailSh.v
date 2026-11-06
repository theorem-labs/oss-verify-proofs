(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of ctrl_lay_block on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8k.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChz.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACa2.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACb8.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlLayBlock.v, with its module paths, module names and numbers changed; 1110 of its 1173 lines of code are new or changed and 881 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import TjSpec TjBase DiscoRo TjCuts TjEntry TjLoopCuts TjSnSh.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnShared PfFacts SnprintfDef SnprintfDefR.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_json_text.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require tj_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_json_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import AmemBlock8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
Context {RO : ro_below_ofl (@pa_segs _ disco_listing PI) (@pa_relro_lo _ disco_listing PI) (@pa_relro_hi _ disco_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Section h.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TLF : PALibF B.
Variables SNPC GC GV IMGLO IMGHI : Z.
Variable CR : list (Z * Z).
Hypothesis HSNPC : pa_sigma DS___interceptor_trampoline_snprintf = SNPC.
Hypothesis ASNP : forall fq : YK11.FPState,
SnprintfDefR.asnprintf_realizesR (fx := fq) SEGS B pa_relro_lo pa_relro_hi GC GV IMGLO IMGHI disco_fmt_lo disco_fmt_hi CR SNPC.
Hypothesis tj_snp_consts : forall (W : world SEGS) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> consts_view SEGS W mem CR.
Hypothesis tj_snp_cr : Forall (fun r => IMG_LO <= fst r /\ 0 <= snd r /\ fst r + snd r <= IMG_TOP) CR.
Hypothesis tj_snp_canary : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
exists cval, rdword (aview SEGS (w_H W) mem) GC = Some GV /\ rdword (aview SEGS (w_H W) mem) GV = Some cval.
Hypothesis tj_snp_gcgv : IMG_LO <= GC /\ GC + 8 <= IMG_TOP /\ IMG_LO <= GV /\ GV + 8 <= IMG_TOP.
Hypothesis tj_snp_img : IMG_LO <= IMGLO /\ IMGHI <= IMG_TOP.
Hypothesis DRO : disco_ro_unowned B.
Hypothesis GM : globs_marked SEGS B disco_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis TJS : tj_strs.
Hypothesis tj_pad : forall k s, tj_ro_at k s ->
forall x, VAL (A_OBJ k) + Z.of_nat (length s) < x < str_end (VAL (A_OBJ k)) s -> seg_rom SEGS (Z_to_bv 64 x) <> None.
Variables STK EV EVB : Z.
Variable IMG : world SEGS -> (word -> option byte) -> Prop.
Hypothesis HSTK : TJ_FRAME + SNPRINTF_STK <= STK.
Hypothesis HEVB : 0 <= EVB.
Hypothesis HEV : 8 * EVB <= EV.
Lemma tjt_s32 : forall T k v, 0 <= v < 2 ^ 31 -> disco_table_c.s32_at T k = v ->
length (disco_table_c.sub T k 4) = 4%nat -> disco_table_c.u_at T k 4 = v.
Proof.
intros T k v Hv Hs Hl. unfold disco_table_c.s32_at, disco_table_c.u_at in *.
pose proof (bytes_le_to_Z_bound (disco_table_c.sub T k 4)) as Hb. rewrite Hl in Hb.
pose proof (bytes_le_to_Z_nonneg (disco_table_c.sub T k 4)) as Hn.
set (x := bytes_le_to_Z (disco_table_c.sub T k 4)) in *.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Hb.
change (bv_swrap 32 x) with ((x + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31) in Hs.
pose proof (Z.div_mod (x + 2 ^ 31) (2 ^ 32) ltac:(lia)) as D. pose proof (Z.mod_pos_bound (x + 2 ^ 31) (2 ^ 32) ltac:(lia)) as M.
lia.
Qed.
Lemma tjt_cons : forall (b : byte) bs, bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
intros b bs. cbn [bytes_le_to_Z].
pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
pose proof (bytes_le_to_Z_nonneg bs) as Hr.
assert (HL : Z.land (bv_unsigned b) (bytes_le_to_Z bs * 256) = 0).
{ apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases j 8) as [Hj8 | Hj8].
- change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
- rewrite <- (Z.mod_small (bv_unsigned b) (2 ^ 8)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite <- (Z.lxor_lor _ _ HL). rewrite (Z.add_nocarry_lxor _ _ HL). reflexivity.
Qed.
Lemma tjt_nle : forall bs k (b : byte),
nth_error bs k = Some b -> bv_unsigned b = (bytes_le_to_Z bs / 2 ^ (8 * Z.of_nat k)) mod 256.
Proof.
induction bs as [|b0 bs IHbs]; intros k b H; [destruct k; discriminate H|].
rewrite tjt_cons. pose proof (bv_unsigned_in_range 8 b0) as Hb0. change (bv_modulus 8) with 256 in Hb0.
pose proof (bytes_le_to_Z_nonneg bs) as Hr.
destruct k as [|k].
- cbn in H. injection H as <-. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r.
rewrite Z_mod_plus_full. symmetry. apply Z.mod_small. lia.
- cbn [nth_error] in H. rewrite (IHbs k b H).
replace (8 * Z.of_nat (Datatypes.S k)) with (8 + 8 * Z.of_nat k) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
rewrite <- Z.div_div by lia. rewrite Z_div_plus_full by lia. rewrite (Z.div_small (bv_unsigned b0) 256) by lia.
reflexivity.
Qed.
Lemma tjt_vm : forall m t T k n, garr8 SEGS m t (map bv_unsigned T) -> 0 <= k ->
(Z.to_nat k + n <= length T)%nat -> val_mem SEGS m (t + k) n (disco_table_c.u_at T k n).
Proof.
intros m t T k n HG Hk Hl j Hj.
pose proof (garr8_mbyte SEGS m t (map bv_unsigned T) (Z.to_nat k + j) HG ltac:(rewrite length_map; lia)) as Hb.
replace (t + Z.of_nat (Z.to_nat k + j)) with (t + k + Z.of_nat j) in Hb by lia. rewrite Hb. f_equal.
destruct (nth_error T (Z.to_nat k + j)) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
assert (Hn : nth (Z.to_nat k + j) (map bv_unsigned T) 0 = bv_unsigned b)
by (apply nth_error_nth; rewrite nth_error_map, Eb; reflexivity).
rewrite Hn.
assert (Hs : nth_error (disco_table_c.sub T k n) j = Some b).
{ unfold disco_table_c.sub. rewrite nth_error_firstn. replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
rewrite nth_error_skipn. exact Eb. }
rewrite (tjt_nle _ _ _ Hs).
assert (HL : length (disco_table_c.sub T k n) = n) by (unfold disco_table_c.sub; rewrite length_firstn, length_skipn; lia).
pose proof (bytes_le_to_Z_bound (disco_table_c.sub T k n)) as Hbd. rewrite HL in Hbd.
pose proof (bytes_le_to_Z_nonneg (disco_table_c.sub T k n)) as Hnn.
unfold disco_table_c.u_at, YO0f.le_byte. rewrite (Z.mod_small (bytes_le_to_Z _)) by lia.
rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Ltac zlia := first [ lia
| match goal with H : boxed _ |- _ => let H' := fresh "Hub" in pose proof H as H'; unfold boxed in H'; lia end
| match goal with H : boxed _, H2 : boxed _ |- _ => let H' := fresh "Hub" in let H2' := fresh "Hub" in
pose proof H as H'; pose proof H2 as H2'; unfold boxed in H', H2'; lia end ].
Ltac ulia1 H := let H' := fresh "Hub" in pose proof H as H'; unfold boxed in H'; lia.
Ltac tjt_zn n Hbapp Hbsep Hbsep2 Hbimg := lazymatch n with
| 740%nat => ulia1 Hbsep2 | 10%nat => ulia1 Hbsep2 | 529%nat => ulia1 Hbapp | 516%nat => ulia1 Hbsep
| 2%nat => lia | 60%nat => lia | _ => ulia1 Hbimg end.
Ltac tjt_notw AG Hbapp Hbsep Hbsep2 Hbimg :=
let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [lazymatch type of Hrg with context [YP09.mkRegion (Some ?n) _ _ _ _ _] =>
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg; tjt_zn n Hbapp Hbsep Hbsep2 Hbimg end|]);
destruct Hin.
Ltac uval := rewrite ?U_SAlu, ?U_SMd, ?U_SLit; cbn [zalu_raw zmd_raw];
repeat match goal with |- context [U ?E (SOff ?n ?c)] =>
let H := lazymatch goal with H : ew E n = Z_to_bv 64 _ |- _ => H end in
first [rewrite (U_atom E n _ H) by (try unfold SB in *; lia) | rewrite (U_atom_off E n _ c H) by (try unfold SB in *; lia)] end;
repeat match goal with |- context [zcanon ?x] => lazymatch x with context [zcanon _] => fail | _ => rewrite (zcanon_id x) by (unfold M64; lia) end end.
Ltac tjt_fa2 tac := apply Forall_cons; [tac | apply Forall_cons; [tac | apply Forall_nil]].
Ltac tjt_kept AG Hfr Hpres2 Hbapp Hbsep Hbsep2 Hbimg :=
lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some ?n) _ _ _ _ _) =>
eapply region_kept_aview; [evalE AG | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply Hfr; tjt_zn n Hbapp Hbsep Hbsep2 Hbimg | exact Hpres2] end.
Ltac tjt_keepq cx := lazymatch goal with |- tj_keep ?B0 _ ?W0 ?m0 => change (tj_keep B0 cx W0 m0) end;
eapply tj_keep_journal; eassumption.
Lemma tjt_sub : forall c l z, zcanon z = 2 ^ 64 - 1 -> 0 <= l <= c -> c < 2 ^ 63 -> zcanon (c + zcanon (l * zcanon z)) = c - l.
Proof.
intros c l z Hz Hl Hc. rewrite Hz. unfold zcanon, M64. rewrite Z.add_mod_idemp_r by lia.
replace (c + l * (2 ^ 64 - 1)) with ((c - l) + l * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma tjt_rd_rom : forall H (mem : word -> option byte) x, seg_rom SEGS (Z_to_bv 64 x) <> None -> aview SEGS H mem x <> None.
Proof.
intros H mem x Hr. unfold aview, mbyte, mrestrict. cbv beta.
destruct (H (Z_to_bv 64 x)); [| destruct (mem (Z_to_bv 64 x)); [discriminate|]];
destruct (seg_rom SEGS (Z_to_bv 64 x)); [discriminate | exfalso; exact (Hr eq_refl) | discriminate | exfalso; exact (Hr eq_refl)].
Qed.
Lemma tjt_ro_rd : forall k s rd, tj_ro_at k s -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rd ->
forall j, 0 <= j <= Z.of_nat (length s) -> rd (VAL (A_OBJ k) + j) = Some (nth (Z.to_nat j) (s ++ [0]) 0).
Proof.
intros k s rd (Hg & Hro & Hlo & Hhi & Hc & Hb) HA j Hj.
rewrite (ro_bytes SEGS pa_relro_lo pa_relro_hi B rd (VAL (A_OBJ k)) (Z.of_nat (length s) + 1) (VAL (A_OBJ k) + j) HA
(Hro (VAL (A_OBJ k) + j) ltac:(lia)) (disco_ro_unowned_at B _ _ DRO ltac:(unfold disco_ro_ranges; apply in_or_app; left; exact Hg)) ltac:(lia)).
replace (VAL (A_OBJ k) + j) with (VAL (A_OBJ k) + Z.of_nat (Z.to_nat j)) by lia.
apply Hb. rewrite length_app. cbn [length]. lia.
Qed.
Lemma tjt_fmt : forall k s ly S (W : world SEGS) mem md rs, tj_ro_at k s -> AR SEGS B ly S W mem md ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
Forall (zdisjoint (VAL (A_OBJ k), Z.of_nat (length s) + 1)) rs ->
fmt_at (aview SEGS (w_H W) mem) rs (VAL (A_OBJ k)) s.
Proof.
intros k s ly S W mem md rs Hk HAR HA Hrs. pose proof Hk as (Hg & Hro & Hlo & Hhi & Hc & Hb).
pose proof (asan_consts) as (_ & _ & _ & _ & C5).
destruct (ro_read_ok_glob SEGS B disco_globs ly S W mem md (VAL (A_OBJ k)) (Z.of_nat (length s) + 1) (VAL (A_OBJ k))
(Z.of_nat (length s) + 1) GM Hg HV HAR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Hra Hhu].
unfold IMG_LO, IMG_TOP in Hlo, Hhi.
unfold fmt_at. split; [lia|]. split; [exact (tjt_ro_rd k s _ Hk HA)|]. split; [exact Hrs|].
split; [unfold amem_range; left; rewrite C5; lia|]. split; assumption.
Qed.
Lemma tjt_strarg : forall k s ly S (W : world SEGS) mem md rs, tj_ro_at k s -> AR SEGS B ly S W mem md ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
Forall (zdisjoint (VAL (A_OBJ k), Z.of_nat (length s) + 8)) rs ->
pf_arg_asan (aview SEGS (w_H W) mem) rs (VAL (A_OBJ k)) (APtr s).
Proof.
intros k s ly S W mem md rs Hk HAR HA Hrs. pose proof Hk as (Hg & Hro & Hlo & Hhi & Hc & Hb).
pose proof (asan_consts) as (_ & _ & _ & _ & C5).
destruct (ro_read_ok_glob SEGS B disco_globs ly S W mem md (VAL (A_OBJ k)) (Z.of_nat (length s) + 1) (VAL (A_OBJ k))
(Z.of_nat (length s) + 1) GM Hg HV HAR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Hra Hhu].
unfold IMG_LO, IMG_TOP in Hlo, Hhi.
unfold pf_arg_asan. split; [exact Hc|]. split; [lia|]. split; [lia|].
split; [exact (tjt_ro_rd k s _ Hk HA)|].
split; [intros x Hx; apply tjt_rd_rom; exact (tj_pad k s Hk x Hx)|].
split.
{ eapply Forall_impl; [|exact Hrs]. intros r Hr. unfold zdisjoint in *. cbn [fst snd] in *. unfold str_end.
pose proof (Z.mod_pos_bound (VAL (A_OBJ k) + Z.of_nat (length s)) 8 ltac:(lia)). lia. }
split; [unfold amem_range; left; rewrite C5; lia|]. split; assumption.
Qed.
Lemma tjt_garr8_snp : forall H (m m2 : word -> option byte) b acc T n o d,
Z.of_nat (length acc) = o -> d = b + o ->
garr8 SEGS (mrestrict H m) b (acc ++ [0]) -> Z.of_nat (length T) < n ->
(forall j, 0 <= j < Z.min (Z.of_nat (length T)) (n - 1) -> aview SEGS H m2 (d + j) = Some (nth (Z.to_nat j) T 0)) ->
aview SEGS H m2 (d + Z.min (Z.of_nat (length T)) (n - 1)) = Some 0 ->
(forall a, b <= a < b + o -> aview SEGS H m2 a = aview SEGS H m a) ->
garr8 SEGS (mrestrict H m2) b (acc ++ T ++ [0]).
Proof.
intros H m m2 b acc T n o d Ho Hd HG Hn Hw Hz Hk. subst d. subst o. rewrite Z.min_l in Hw, Hz by lia.
apply (proj2 (garr8_app SEGS _ _ _ _)). split.
- apply (garr8_aview_kept SEGS H H m m2 b acc); [exact Hk|]. exact (proj1 (proj1 (garr8_app SEGS _ _ _ _) HG)).
- intros j Hj. rewrite length_app in Hj. cbn [length] in Hj. apply val_mem1_of_aview.
destruct (Nat.lt_ge_cases j (length T)) as [Hjl | Hjl].
+ rewrite app_nth1 by lia. rewrite (Hw (Z.of_nat j) ltac:(lia)). rewrite Nat2Z.id. reflexivity.
+ assert (Ej : j = length T) by lia. subst j. rewrite app_nth2 by lia. rewrite Nat.sub_diag. exact Hz.
Qed.
Definition tjt_T5 (s : list Z) : list Z := [44; 34; 111; 119; 110; 101; 100; 34; 58] ++ s.
Definition tjt_T6 (u : Z) : list Z := [44; 34; 97; 103; 101; 95; 109; 115; 34; 58] ++ pf_udec u ++ [125].
Lemma tjt_dec_aux_pf : forall f x acc, 1 <= x < 10 ^ Z.of_nat f -> dec_aux (S f) x acc = pf_digits f x acc.
Proof.
induction f as [|f IH]; intros x acc Hx; [cbn in Hx; lia|].
change (dec_aux (S (S f)) x acc) with (if x =? 0 then acc else dec_aux (S f) (x / 10) ((48 + x mod 10) :: acc)).
change (pf_digits (S f) x acc) with (if x <? 10 then (48 + x) :: acc else pf_digits f (x / 10) ((48 + x mod 10) :: acc)).
replace (x =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
destruct (Z.ltb_spec x 10) as [Lt|Lt].
- rewrite Z.div_small by lia. rewrite Z.mod_small by lia. reflexivity.
- cbv beta iota. apply IH. rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hx by lia. split.
+ apply Z.div_le_lower_bound; lia.
+ apply Z.div_lt_upper_bound; lia.
Qed.
Lemma tjt_pf_digits_fuel : forall f x acc, 0 <= x < 10 ^ Z.of_nat (S f) -> pf_digits (S f) x acc = pf_digits (S (S f)) x acc.
Proof.
induction f as [|f IH]; intros x acc Hx.
- cbn in Hx. cbn [pf_digits]. replace (x <? 10) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
- change (pf_digits (S (S f)) x acc) with (if x <? 10 then (48 + x) :: acc else pf_digits (S f) (x / 10) ((48 + x mod 10) :: acc)).
change (pf_digits (S (S (S f))) x acc) with (if x <? 10 then (48 + x) :: acc else pf_digits (S (S f)) (x / 10) ((48 + x mod 10) :: acc)).
destruct (Z.ltb_spec x 10) as [Lt|Lt]; [reflexivity|].
cbv beta iota. apply IH. rewrite (Nat2Z.inj_succ (S f)), Z.pow_succ_r in Hx by lia. split.
+ apply Z.div_pos; lia.
+ apply Z.div_lt_upper_bound; lia.
Qed.
Lemma tjt_dec_udec : forall u, 0 <= u < 10 ^ 19 -> dec u = pf_udec u.
Proof.
intros u Hu. unfold dec, pf_udec. destruct (Z.eqb_spec u 0) as [->|N]; [reflexivity|].
change 20%nat with (S 19). rewrite tjt_dec_aux_pf by (cbn; lia).
apply (tjt_pf_digits_fuel 18). cbn. lia.
Qed.
Lemma tjt_age_rng : forall now ls, 0 <= now < 2 ^ 64 -> 0 <= ls -> 0 <= age_of now ls < 2 ^ 45.
Proof.
intros now ls Hn Hl. unfold age_of. destruct (Z.ltb_spec ls now).
- split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
- lia.
Qed.
Lemma tjt_blt0 : forall E a v, U E a = v -> 0 <= v < 2 ^ 63 ->
branch_taken BC_LT (sv_denot E a) (sv_denot E (SLit 0)) = false.
Proof.
intros E a v Hu Hv. rewrite (denot_lit_U E a), (denot_lit_U E (SLit 0)), Hu, U_SLit.
change (zcanon 0) with 0. cbn [branch_taken]. unfold bv_lts. rewrite !Z_to_bv_signed.
rewrite (bv_swrap_small 64 v), (bv_swrap_small 64 0) by (change (bv_half_modulus 64) with (2 ^ 63); lia).
apply Z.ltb_ge. lia.
Qed.
Lemma tjt_blt : forall E a b x y, U E a = x -> U E b = y -> 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (x <? y).
Proof.
intros E a b x y Ha Hb Hx Hy. rewrite (denot_lit_U E a), (denot_lit_U E b), Ha, Hb.
cbn [branch_taken]. unfold bv_lts. rewrite !Z_to_bv_signed.
rewrite (bv_swrap_small 64 x), (bv_swrap_small 64 y) by (change (bv_half_modulus 64) with (2 ^ 63); lia).
reflexivity.
Qed.
Definition ss_tjA : sstate :=
(mkSS 24620
[SLit 0; SOff 860 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 861 0; SOff 862 0; SOff 863 0; SOff 2 0; SOff 60 0; SOff 864 0; SOff 865 0; SOff 866 0; SOff 867 0; SOff 868 0; SOff 869 0; SOff 870 0; SOff 871 0; SOff 516 0; SOff 12 0; SOff 13 0; SAlu ALU_ADD (SOff 844 0) (SOff 852 0); SOff 529 0; SAlu ALU_ADD (SAlu ALU_ADD (SOff 13 0) (SMd M_MUL (SOff 844 0) (SLit (-1)))) (SMd M_MUL (SOff 852 0) (SLit (-1))); SOff 853 0; SOff 32 0; SOff 854 0; SOff 855 0; SOff 872 0; SOff 873 0; SOff 874 0; SOff 875 0]
[YP09.mkRegion (Some 529%nat) 0 32 0 0 [];
YP09.mkRegion (Some 516%nat) 0 256 0 256 [YP09.mkChunk 248 (CVal 8 (SOff 528 0))];
YP09.mkRegion (Some 60%nat) 0 184 0 184 [YP09.mkChunk 32 (CVal 8 (SOff 281 0)); YP09.mkChunk 40 (CVal 8 (SLit 4835703278458516699)); YP09.mkChunk 48 (CVal 8 (SOff 516 160)); YP09.mkChunk 56 (CVal 8 (SOff 516 32)); YP09.mkChunk 64 (CVal 8 (SOff 10 0)); YP09.mkChunk 72 (CVal 8 (SOff 11 0)); YP09.mkChunk 80 (CVal 8 (SOff 10 384)); YP09.mkChunk 88 (CVal 8 (SOff 516 0)); YP09.mkChunk 96 (CVal 8 (SOff 516 96)); YP09.mkChunk 104 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 384) (SLit 3)) (SOff 32 0))); YP09.mkChunk 112 (CVal 8 (SOff 282 0)); YP09.mkChunk 120 (CVal 8 (SOff 741 0)); YP09.mkChunk 128 (CVal 8 (SOff 734 0)); YP09.mkChunk 136 (CVal 8 (SOff 723 0)); YP09.mkChunk 144 (CVal 8 (SOff 722 0)); YP09.mkChunk 152 (CVal 8 (SOff 721 0))];
YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))];
YP09.mkRegion (Some 242%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 307 0))];
YP09.mkRegion (Some 307%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 241%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 308 0))];
YP09.mkRegion (Some 308%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))]]
None
(mkFacts
[(740%nat, mkAF 4096 140737479966720 3); (529%nat, mkAF 2147451392 17594333495296 2); (528%nat, mkAF 4096 140737479966720 0); (516%nat, mkAF 4096 140737479966720 5); (60%nat, mkAF 70368744177152 140737488355328 5); (2%nat, mkAF 70368744177664 140737488355328 4); (32%nat, mkAF 2147450880 2147450880 0); (13%nat, mkAF 0 2147483647 0); (12%nat, mkAF 4096 140737479966720 4); (10%nat, mkAF 4096 140737479966720 3)]
[]
[(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0), SOff 529 0)])).
Definition INV_tjA (i : Z) : tjcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 =>
k <= EVB * (i + 1) /\ tj_lbody B i cx E ly3 S3 W3 ms3 /\
exists (acc s : list Z), tj_split E 852 844 acc /\ (s = s_false \/ s = s_true) /\
ew E 864 = w64 (Z.of_nat (length (tjt_T5 s))) /\ Z.of_nat (length acc) < c_cap cx /\
reac_disco_table_json_c.tj_text (c_T cx) (c_now cx) =
acc ++ tjt_T5 s ++ P6 (c_now cx) (tj_e cx i) ++ tj_lemmas.tj_rest (c_T cx) (c_now cx) (i + 1) /\
(Z.of_nat (length (tjt_T5 s)) < c_cap cx - Z.of_nat (length acc) ->
garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) (c_buf cx) (acc ++ tjt_T5 s ++ [0])).
Definition tj_fromA (i : Z) : Prop := tj_from0 B STK EV IMG ss_tjA (INV_tjA i).
Lemma tjt_seg_A : forall i, tj_fromX B STK EV IMG -> tj_fromC B STK EV EVB IMG -> tj_fromL B STK EV EVB IMG (i + 1) -> tj_fromA i.
Proof.
intros i FX FC FL. unfold tj_fromA, tj_from0.
intros cx E k ly3 S3 W3 ms3 md3 HBASE HEX HJ HFR HINV HS.
destruct cx as [fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0].
pose proof HBASE as HB0. pose proof HEX as HX0. unfold tj_baseX in HB0. unfold tj_EX, tj_F, tj_FL in HX0.
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0 tj_F tj_FL]
in HB0, HX0, HINV, HJ, HFR, HS.
pose proof HB0 as (HPRE & Hfrm0 & Hroom & HROD & HIM & H10 & H11 & H12 & H13 & Hnow & Hcap & Hobj & Harr & HlenT & Hok
& Hbuf & Hev & Hsp1b & HE0 & HE032 & HE02).
pose proof HX0 as (AG & E60 & E516 & E528 & E529 & HEI).
unfold INV_tjA, tj_lbody, tj_split in HINV. cbn [c_cap c_T c_now c_buf c_t c_ly c_S] in HINV.
destruct HINV as (Hk0 & (Hperm & HKEEP & Hcap3 & Hi & E721 & E722 & E723 & E734 & E740 & E741) & acc & s5 &
(o1 & o2 & E852 & E844 & Ho1 & Ho2 & Ho12) & Hs5 & E864 & Hacc & Htxt & Hgarr).
unfold w64 in E721, E722, E723, E734, E740, E741, E852, E844, E864.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity. assert (HSNP : SNPRINTF_STK = 11776) by reflexivity.
assert (HSK : 11776 + 640 <= STK) by (unfold TJ_FRAME in HSTK; lia).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBOK. pose proof pa_base_lo as HBLO.
destruct (sp1_facts (spZ regs + -288) ltac:(clear - Hceil Hslo Hstk0 HSK C1; lia)
ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
rewrite <- Hsp1b in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 304 <= sp1 <= spZ regs - 288) by (clear - Hsp1r; lia). clear Hsp1r.
pose (RUN := paj_run (fx := fq) B LAWS). pose (RUNTO := paj_run_to (fx := fq) B LAWS).
pose (BR := paj_branch (fx := fq) (PI := PI)).
pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & Hnev3 & Hk3 & _ & _ & _ & _ & _ & Hpres3 & _ & _ & HQT3).
destruct (al_layout _ _ LAWS ly S W mem md ly3 HAR Hly3) as (Eab3 & EFA & Eown3).
assert (EFA0 : forall c p, frame_addr ly3 c p = frame_addr ly c p) by exact EFA.
set (F := frame_addr ly 2 fpos) in *. set (FLg := flag_addr ly 2 fpos) in *.
assert (Hfin : In (2, fpos) (frames S3)) by (rewrite HFR; left; reflexivity).
assert (E1 : ew E 1 = getr regs 1) by (rewrite (AG 1%nat ltac:(lia)); exact (HE0 1%nat 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite (AG 2%nat ltac:(lia)); exact (HE0 2%nat 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite (AG 3%nat ltac:(lia)); exact (HE0 3%nat 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite (AG 4%nat ltac:(lia)); exact (HE0 4%nat 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite (AG 10%nat ltac:(lia)); rewrite (HE0 10%nat 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 now) by (rewrite (AG 11%nat ltac:(lia)); rewrite (HE0 11%nat 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 buf) by (rewrite (AG 12%nat ltac:(lia)); rewrite (HE0 12%nat 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat ltac:(lia)); rewrite (HE0 13%nat 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat ltac:(lia)); exact HE032).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat ltac:(lia)); exact HE02).
assert (F12 : ew E0 12 = Z_to_bv 64 buf) by (rewrite (HE0 12%nat 12%bv eq_refl); exact H12).
assert (F13 : ew E0 13 = Z_to_bv 64 cap) by (rewrite (HE0 13%nat 13%bv eq_refl); exact H13).
assert (F10 : ew E0 10 = Z_to_bv 64 t) by (rewrite (HE0 10%nat 10%bv eq_refl); exact H10).
assert (F11 : ew E0 11 = Z_to_bv 64 now) by (rewrite (HE0 11%nat 11%bv eq_refl); exact H11).
img_factsF E.
pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as Hob242. pose proof (pa_obj_img 0 ltac:(unfold disco_nobj; lia)) as Hob241.
pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as Hob307. pose proof (pa_obj_img 67 ltac:(unfold disco_nobj; lia)) as Hob308.
cbv [A_OBJ Nat.add] in Hob241, Hob242, Hob307, Hob308.
pose proof (palf_uar_img B TL) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
unfold IMG_LO, IMG_TOP in Hob241, Hob242, Hob307, Hob308, Huar.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR3 Hfin) as (HFal & [HFhi _] & HFpres & HFSpres).
rewrite EFA in HFal, HFhi, HFpres, HFSpres. fold F in HFal, HFhi, HFpres, HFSpres.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 2 fpos HAR3 Hfin) as (HF4096 & HFceil & HFhigh).
rewrite EFA in HF4096, HFceil, HFhigh. fold F in HF4096, HFceil, HFhigh.
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hfin) as HFhigh_img. rewrite EFA in HFhigh_img. fold F in HFhigh_img.
change (fs_frame_bytes 2) with 256 in *.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
pose proof Hobj as ((cidt & post & Hint & Hcidt & Hfa8 & Htlo & Hthi) & Ht8 & Htra0).
assert (Hint3 : In (cidt, post) (frames S3)) by (rewrite HFR; right; exact Hint).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cidt post HAR Hint) as (HT4096 & HTceil & HTapp).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hint3) as HTimg. rewrite EFA in HTimg.
assert (HTF : zdisjoint (frame_rng ly3 (2, fpos)) (frame_rng ly3 (cidt, post))).
{ destruct (in_split _ _ Hint) as (l2 & l3 & El). apply (sep_frames_pos SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ [] l2 l3 HAR3).
rewrite HFR, El. reflexivity. }
unfold zdisjoint, frame_rng in HTF. cbn [fst snd] in HTF. rewrite !EFA in HTF. fold F in HTF.
change (fs_frame_bytes 2) with 256 in HTF.
pose proof (fs_frame_bytes_nonneg cidt) as HTb0.
set (TB := fs_frame_bytes cidt) in *. set (FT := frame_addr ly cidt post) in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HTapp. unfold off_img, IMG_LO, IMG_TOP in HTimg.
destruct Hok as (HT1 & HT2 & HT3 & HT4).
unfold tj_keep, afobj in HKEEP. cbn [c_t c_ly c_S c_T] in HKEEP. destruct HKEEP as (HROD3 & HG3 & (_ & _ & HRA3)). unfold disco_table_c.tbl_T1 in HT1.
destruct (HT4 i Hi) as (_ & _ & Hown).
assert (Ht400 : t + 400 <= FT + TB) by lia.
assert (Hinb0 : In (buf, Nb) (ablocks B ly S)) by exact (proj1 (Hbuf Hcap3)).
assert (Hcapb : cap <= req_size Nb) by exact (proj2 (Hbuf Hcap3)).
assert (Hinb : In (buf, Nb) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hinb0]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ buf Nb HAR3 Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & _ & _ & HNb).
pose proof (blk_off_imgP _ _ _ _ _ _ buf Nb HAR3 Hinb) as Hbimg.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ buf Nb 2 fpos HAR3 Hinb Hfin) as Hbsep.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ buf Nb cidt post HAR3 Hinb Hint3) as Hbsep2.
rewrite EFA0 in Hbsep, Hbsep2. fold F FT in Hbsep, Hbsep2. change (fs_frame_bytes 2) with 256 in Hbsep. fold TB in Hbsep2.
unfold zdisjoint in Hbsep, Hbsep2. cbn [fst snd] in Hbsep, Hbsep2.
unfold in_app, kLowShadowBeg, kHighMemBeg in Hbapp. unfold off_img, IMG_LO, IMG_TOP in Hbimg.
box HTapp. box HTimg. box HTF. box Hbapp. box Hbimg. box Hbsep. box Hbsep2.
pose proof tj_snp_gcgv as (Hgc1 & Hgc2 & Hgv1 & Hgv2). unfold IMG_LO, IMG_TOP in Hgc1, Hgc2, Hgv1, Hgv2.
pose proof TJS as (_ & _ & _ & _ & _ & _ & _ & _ & Hs53 & Hs54 & _ & _ & _ & _ & _ & Hs51 & Hs52 & _).
set (L := Z.of_nat (length acc)) in *. assert (HLd : L = Z.of_nat (length acc)) by reflexivity.
set (l5 := Z.of_nat (length (tjt_T5 s5))) in *. assert (Hl5d : l5 = Z.of_nat (length (tjt_T5 s5))) by reflexivity.
assert (Hl5r : 13 <= l5 <= 14) by (rewrite Hl5d; destruct Hs5 as [-> | ->]; cbn; lia).
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq) B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fq) B LAWS).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (eq_trans (AG 13%nat ltac:(lia)) F13) as E13v;
assert (U4 : U Ev (SAlu ALU_ADD (SAlu ALU_ADD (SOff 13 0) (SMd M_MUL (SOff 844 0) (SLit (-1)))) (SMd M_MUL (SOff 852 0) (SLit (-1)))) = cap - L)
by (rewrite !U_SAlu; cbn [zalu_raw]; rewrite !U_SMd; cbn [zmd_raw]; rewrite (U_atom Ev 13 cap E13v), (U_atom Ev 844 o2 E844), (U_atom Ev 852 o1 E852), !U_SLit by lia;
rewrite (tjt_sub cap o2) by (first [reflexivity | lia]); rewrite tjt_sub by (first [reflexivity | lia]); lia);
assert (U0 : U Ev (SOff 864 0) = l5) by (apply U_atom; [exact E864 | lia])
end.
psrr_branch_pi RUNP BR HS.
{ exfalso. lazymatch type of Hc with branch_taken _ (sv_denot ?Ev ?a) (sv_denot _ _) = _ =>
rewrite (tjt_blt0 Ev a l5 U0 ltac:(lia)) in Hc; discriminate Hc end. }
clear Hc.
paj_run_shc RUNP RUNC HS HJ. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HK2 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | tjt_notw AG Hbapp Hbsep Hbsep2 Hbimg]) end.
clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
- rewrite branch_geu_U, U0, U4 in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
pose proof (proj1 HJ) as HARx. destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HARx Hfin) as (_ & _ & _ & HFSx).
rewrite EFA0 in HFSx. fold F in HFSx. change (fs_frame_bytes 2 / 8) with 32 in HFSx.
fs_rwF HS E529 HFSx.
paj_run_to_shc RUNTOP HS HJ 0x621c. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
clear HF HFr HG.
prreg HS (21%bv : bv 5) R21.
ra_join HS ss_tjX 640%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 21; 23; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 640%nat 13%nat R21 E653.
hei_havoc HS. rebaseE HS AG HEv. clear HEv.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (FX (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) Ev k ly3 S3 Wg msF mdF) end end.
+ exact HBASE.
+ unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [exact AG|]. split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529 | assumption].
+ cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ.
+ cbn [c_S c_fpos]. exact HFR.
+ unfold INV_tjX. cbn [c_cap c_T c_now c_buf c_ly c_S].
assert (Htl : cap <= tj_len T now).
{ unfold tj_len. rewrite Htxt, !length_app. lia. }
assert (HkE : EVB * (i + 1) <= EVB * 8) by (apply Z.mul_le_mono_nonneg_l; lia).
split; [lia|]. split; [exact Hperm|]. exists (-1). split.
{ rewrite E653. apply bv_eq. unfold w64. rewrite !Z_to_bv_unsigned. vm_compute. reflexivity. }
split; [intros; lia|]. split; [intros _ Hlt; exfalso; lia | intros _ _; reflexivity].
+ exact HS.
- rewrite branch_geu_U, U0, U4 in Hc. apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hn1.
paj_run_shc RUNP RUNC HS HJ. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HK3 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | tjt_notw AG Hbapp Hbsep Hbsep2 Hbimg]) end.
clear HF HFr HG.
set (ag := tj_age (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) i) in *.
assert (Hag : 0 <= ag < 2 ^ 45).
{ unfold ag, tj_age. cbn [c_now c_T]. apply tjt_age_rng; [lia|]. unfold disco_table_c.last_of, disco_table_c.u_at. apply bytes_le_to_Z_nonneg. }
assert (HP6 : P6 now (tj_e (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) i) = tjt_T6 ag).
{ unfold P6, key, k_age_ms, tjt_T6, tj_e. cbn [c_T]. unfold reac_disco_table_json_c.tj_entry. cbn [e_last_seen].
rewrite tjt_dec_udec; [reflexivity|]. change (age_of now (disco_table_c.last_of T i)) with ag. lia. }
assert (Hud : (length (pf_udec ag) <= 20)%nat) by (rewrite <- tjt_dec_udec by lia; apply tj_lemmas.dec_len).
cbn [c_now c_T] in Htxt. rewrite HP6 in Htxt.
assert (Hg1 : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) buf (acc ++ tjt_T5 s5 ++ [0])) by (apply Hgarr; lia).
lazymatch type of HK3 with forall a, _ -> aview _ _ ?m1 a = aview _ _ ?m0 a =>
lazymatch type of HK2 with forall a, _ -> aview _ _ ?n1 a = aview _ _ ?n0 a =>
assert (Hg2 : garr8 SEGS (mrestrict (w_H W3) m1) buf (acc ++ tjt_T5 s5 ++ [0]))
by (apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms3) m1 buf); [|exact Hg1];
intros a Ha; rewrite !length_app in Ha; cbn [length] in Ha;
rewrite HK3 by lia; apply HK2; lia) end end.
clear Hg1.
lazymatch type of HS with st_ok _ ?Ev _ (restrict _ ?msx) =>
pose proof (eq_trans (AG 12%nat ltac:(lia)) F12) as E12v;
let HEv := rnHEI Ev in pose proof (img_env_atomP Ev 295 HEv ltac:(unfold A_TEXT, A_LIM; lia)) as E295;
rregU HS (10%bv : bv 5) (buf + L + l5) ltac:(rewrite !U_SAlu; cbn [zalu_raw];
rewrite (U_atom Ev 12 buf E12v), (U_atom Ev 844 o2 E844), (U_atom Ev 852 o1 E852), (U_atom Ev 864 l5 E864) by lia;
rewrite (zcanon_id (buf + o2)) by (unfold M64; lia); rewrite (zcanon_id (buf + o2 + o1)) by (unfold M64; lia);
rewrite zcanon_id by (unfold M64; lia); lia) Rb0;
rregU HS (11%bv : bv 5) (cap - L - l5) ltac:(rewrite !U_SAlu; cbn [zalu_raw]; rewrite !U_SMd; cbn [zmd_raw];
rewrite (U_atom Ev 13 cap E13v), (U_atom Ev 844 o2 E844), (U_atom Ev 852 o1 E852), (U_atom Ev 864 l5 E864), !U_SLit by lia;
rewrite (tjt_sub cap o2) by (first [reflexivity | lia]); rewrite (tjt_sub (cap - o2) o1) by (first [reflexivity | lia]);
rewrite tjt_sub by (first [reflexivity | lia]); lia) Rb1 end.
prreg HS (2%bv : bv 5) Qsp2. prreg HS (3%bv : bv 5) Qgp2. prreg HS (4%bv : bv 5) Qtp2. prreg HS (1%bv : bv 5) Qra2.
prreg HS (12%bv : bv 5) Qb2. prreg HS (13%bv : bv 5) Qb3.
pose proof (proj1 HJ) as HARd.
pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD) as HRODd.
destruct (tj_snp_canary _ _ _ _ _ HARd) as (cval2 & HC3 & HC4).
pose proof Hs54 as (_ & _ & H54lo & H54hi & _). unfold IMG_LO, IMG_TOP in H54lo, H54hi. cbv [A_OBJ Nat.add] in H54lo, H54hi.
change (Z.of_nat (length tj_f_age)) with 15 in H54lo, H54hi.
pmkst HS. rewrite HSNPC.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msx) _ (ms_mem ?msx) _) _) _ =>
eapply (aj_sh_snprintf_at B LAWS pa_segs_low STK fq GC GV IMGLO IMGHI CR SNPC (ASNP fq) W3 (ms_regs msx) (ms_mem msx) (spZ regs) (tj_fp buf cap)
ly S W mem md [(2, fpos)] ly3 S3 _ k (buf + L + l5) (cap - L - l5) (VAL 295) tj_f_age
ltac:(let v := eval vm_compute in (pf_parse tj_f_age) in lazymatch v with Some ?p => exact p end)
[] (map (argZ (ms_regs msx)) [3; 4; 5; 6; 7] ++ []) [AU64 ag] (tjt_T6 ag) cval2 (sp1 - spZ regs)
(Z_to_bv 64 (BASE + 24660)) _ HJ HRODd) end.
{ unfold spZ at 1. rewrite Qsp2, E60, unsigned_lit_small by lia. lia. }
{ rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity. }
{ lia. }
{ lia. }
{ rewrite Qgp2, (AG 3%nat) by lia. rewrite (HE0 3%nat 3%bv eq_refl). exact Hgp. }
{ rewrite Qtp2, (AG 4%nat) by lia. rewrite (HE0 4%nat 4%bv eq_refl). exact Htp. }
{ exact Qra2. }
{ apply ret_ok_codeptr_v; [lia | reflexivity]. }
{ exact Rb0. }
{ exact Rb1. }
{ rewrite Qb2, E295. reflexivity. }
{ exact (tj_snp_consts _ _ HRODd). }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r Hr. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr. zlia. }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r Hr. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr. unfold snp_out.
tjt_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; zlia). }
{ exact HC3. }
{ exact HC4. }
{ lia. }
{ lia. }
{ lia. }
{ lia. }
{ unfold snp_out. tjt_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; zlia). }
{ unfold snp_out. tjt_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; zlia). }
{ apply (tjt_fmt 54 tj_f_age _ _ _ _ _ _ Hs54 HARd HRODd).
change (Z.of_nat (length tj_f_age)) with 15. cbv [A_OBJ Nat.add]. unfold snp_out. tjt_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; zlia). }
{ exact (tj_ro_fmt_rng 54 tj_f_age Hs54 ltac:(cbn; lia)). }
{ unfold tj_f_age; discriminate. }
{ reflexivity. }
{ repeat (apply Forall_cons; [exact I|]); apply Forall_nil. }
{ split; [reflexivity | intros j Hj; cbn in Hj; lia]. }
{ cbn [length Z.of_nat]. lia. }
{ unfold snp_out. tjt_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; zlia). }
{ cbn [pf_args_asan map app]. split; [|exact I]. cbn [pf_arg_asan].
unfold argZ. replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Qb3, E741.
apply unsigned_lit_small. lia. }
{ cbn [map app SnFF.pf_args_amem]. exact I. }
{ reflexivity. }
{ zlia. }
{ unfold tjt_T6. rewrite !length_app. cbn [length]. lia. }
{ zlia. }
{ zlia. }
{ unfold snp_out. cbn [pairwise].
split; [apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; zlia | apply Forall_nil] | split; [apply Forall_nil | exact I]]. }
{ intros a Ha. split; [|zlia]. right. left. split.
+ exists (buf, buf + cap). split; [unfold tj_fp; rewrite (proj2 (Z.ltb_ge cap 3) Hcap3); left; reflexivity | cbn [fst snd]; lia].
+ exists buf, Nb. split; [exact Hinb | lia]. }
{ apply (amem_range_of_block8 SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARd Hinb); zlia. }
{ apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARd Hinb); zlia. }
{ apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARd Hinb); zlia. }
{ eapply tj_dest_off_globals; [exact (proj1 tj_snp_img) | exact (proj2 tj_snp_img) | exact HARd | exact Hinb | lia | lia]. }
{ exact Hfrm0. }
intros fx' regs4 mem4 md4 Hf1 Hf2 HJ4 HP4 Ha0b Hwr2 Hnul2 Hfr2 Hpres4 Hsame2.
replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hfr2 by lia. rewrite HSNP in Hfr2.
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat AG ltac:(idtac; tjt_kept AG Hfr2 Hpres4 Hbapp Hbsep Hbsep2 Hbimg).
apply (st_ok_pi_restrict_fx fq fx') in HS.
clear RUN RUNP RUNTOP RUNC BR.
pose (RUN := paj_run (fx := fx') B LAWS).
pose (BR := paj_branch (fx := fx') (PI := PI)).
pose (RUNP := SRr_run_pi_AJ (fx := fx') B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ (fx := fx') B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fx') B LAWS).
prreg HS (10%bv : bv 5) Qr1. cbn [ms_regs] in Qr1. rewrite Ha0b in Qr1. symmetry in Qr1. unfold w64 in Qr1.
set (L2 := Z.of_nat (length (tjt_T6 ag))) in *. assert (HL2d : L2 = Z.of_nat (length (tjt_T6 ag))) by reflexivity.
assert (HL2 : 11 <= L2 <= 31) by (unfold L2, tjt_T6; rewrite !length_app; cbn [length]; lia).
lazymatch type of Qr1 with ew ?Ev ?K2 = _ =>
assert (U0b : U Ev (SOff K2 0) = L2) by (apply U_atom; [exact Qr1 | lia]);
pose proof (eq_trans (AG 13%nat ltac:(lia)) F13) as E13w;
assert (U5 : U Ev (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SOff 13 0) (SMd M_MUL (SOff 844 0) (SLit (-1))))
(SMd M_MUL (SOff 852 0) (SLit (-1)))) (SMd M_MUL (SOff 864 0) (SLit (-1)))) = cap - L - l5)
by (rewrite !U_SAlu; cbn [zalu_raw]; rewrite !U_SMd; cbn [zmd_raw];
rewrite (U_atom Ev 13 cap E13w), (U_atom Ev 844 o2 E844), (U_atom Ev 852 o1 E852), (U_atom Ev 864 l5 E864), !U_SLit by lia;
rewrite (tjt_sub cap o2) by (first [reflexivity | lia]); rewrite (tjt_sub (cap - o2) o1) by (first [reflexivity | lia]);
rewrite tjt_sub by (first [reflexivity | lia]); lia) end.
psrr_branch_pi RUNP BR HS.
{ exfalso. lazymatch type of Hc with branch_taken _ (sv_denot ?Ev ?a) (sv_denot _ _) = _ =>
rewrite (tjt_blt0 Ev a L2 U0b ltac:(lia)) in Hc; discriminate Hc end. }
clear Hc.
pose proof (proj1 HJ4) as HARy. destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HARy Hfin) as (_ & _ & _ & HFSy).
rewrite EFA0 in HFSy. fold F in HFSy. change (fs_frame_bytes 2 / 8) with 32 in HFSy.
fs_rwF HS E529 HFSy.
paj_run_shc RUNP RUNC HS HJ4. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HK4 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | tjt_notw AG Hbapp Hbsep Hbsep2 Hbimg]) end.
clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
* rewrite branch_geu_U, U0b, U5 in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
paj_run_to_shc RUNTOP HS HJ4 0x621c. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
clear HF HFr HG.
prreg HS (21%bv : bv 5) R21.
ra_join HS ss_tjX 640%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 21; 23; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 640%nat 13%nat R21 E653.
hei_havoc HS. rebaseE HS AG HEv. clear HEv.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B STK EV IMG _ _ FX (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx' Ev k ly3 S3 Wg msF mdF Hf1 Hf2) end end.
+ exact HBASE.
+ unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [exact AG|]. split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529 | assumption].
+ cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ4.
+ cbn [c_S c_fpos]. exact HFR.
+ unfold INV_tjX. cbn [c_cap c_T c_now c_buf c_ly c_S].
assert (Htl : cap <= tj_len T now).
{ unfold tj_len. rewrite Htxt, !length_app. lia. }
assert (HkE : EVB * (i + 1) <= EVB * 8) by (apply Z.mul_le_mono_nonneg_l; lia).
split; [lia|]. split; [exact Hperm|]. exists (-1). split.
{ rewrite E653. apply bv_eq. unfold w64. rewrite !Z_to_bv_unsigned. vm_compute. reflexivity. }
split; [intros; lia|]. split; [intros _ Hlt; exfalso; lia | intros _ _; reflexivity].
+ exact HS.
* rewrite branch_geu_U, U0b, U5 in Hc. apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hn2.
lazymatch type of HK3 with forall a, _ -> aview _ _ ?m1 a = aview _ _ ?m0 a =>
assert (Hg3 : garr8 SEGS (mrestrict (w_H W3) mem4) buf ((acc ++ tjt_T5 s5) ++ tjt_T6 ag ++ [0]))
by (apply (tjt_garr8_snp (w_H W3) m1 mem4 buf (acc ++ tjt_T5 s5) (tjt_T6 ag) (cap - L - l5) (L + l5) (buf + L + l5));
[ rewrite length_app; lia
| lia
| rewrite <- app_assoc; exact Hg2
| fold L2; lia
| exact Hwr2
| exact Hnul2
| intros a Ha; apply Hfr2; zlia ]) end.
clear Hg2.
lazymatch type of HK4 with forall a, _ -> aview _ _ ?m1 a = aview _ _ ?m0 a =>
assert (Hg4 : garr8 SEGS (mrestrict (w_H W3) m1) buf ((acc ++ tjt_T5 s5) ++ tjt_T6 ag ++ [0]))
by (apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) mem4 m1 buf); [|exact Hg3];
intros a Ha; rewrite !length_app in Ha; cbn [length] in Ha;
apply HK4; lia) end.
clear Hg3.
fs_roF HS.
lazymatch type of HJ4 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mx _ _ =>
assert (HKP : tj_keep B (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) W3 mx)
by (eapply tj_keep_journal; eassumption) end.
unfold tj_keep, afobj in HKP. cbn [c_t c_ly c_S c_T] in HKP. destruct HKP as (_ & HGk & (_ & _ & HRAk)).
assert (Hun : disco_table_c.u_at T 384 4 = disco_table_c.n_of T).
{ apply tjt_s32; [lia | reflexivity |]. unfold disco_table_c.sub. rewrite length_firstn, length_skipn. lia. }
pose proof (tjt_vm _ t T 384 4 HGk ltac:(lia) ltac:(rewrite HlenT; lia)) as Hvn. rewrite Hun in Hvn.
add_atom HS 900%nat (Z_to_bv 64 (disco_table_c.n_of T)) E900.
rebaseE HS AG HEv. clear HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_fact Ev ssv msv 900 (mkAF 0 8 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E900, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 10%nat) 384 388 0 0 [YP09.mkChunk 384 (CVal 4 (SOff 900 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite (AG 10%nat) by lia; rewrite F10, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS Ev _ t 384 4 (SOff 900 0) (disco_table_c.n_of T));
[cbn [sv_denot]; rewrite E900, unsigned_lit_small, Z.add_0_r by lia; reflexivity | zside | zside |];
exact Hvn)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; unfold SB;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C3 HF4096 HFceil HF8lo HF8hi HFq HF8 Hob241 Hob242 Hob307 Hob308 Huar
HT4096 HTceil HTapp HTimg HTF Htlo Ht400 Hi HT1 HTb0;
unfold boxed in *; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ (restrict _ ?msx) =>
(shok_auto SHOK2 (SOff 32 0) Ev (mrestrict (w_H W3) (ms_mem msx))) end.
(paj_run_tok RUN HS HJ4 SHOK2 Bspan).
{ lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ _) _ =>
rewrite (U_atom Ex 32 SB ltac:(rewrite (AG 32%nat) by lia; exact HE032)) by (unfold SB; lia);
rewrite (U_atom_off Ex 10 t 384 ltac:(rewrite (AG 10%nat) by lia; exact F10)) by lia end.
rewrite SB_SHADOW_OFF. apply (range_addressable_sub _ SHADOW_OFF t 400); [exact HRAk | lia | lia]. }
{ awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HK5 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | tjt_notw AG Hbapp Hbsep Hbsep2 Hbimg]) end.
clear HF HFr HG.
lazymatch type of HK5 with forall a, _ -> aview _ _ ?m1 a = aview _ _ ?m0 a =>
assert (Hg5 : garr8 SEGS (mrestrict (w_H W3) m1) buf ((acc ++ tjt_T5 s5) ++ tjt_T6 ag ++ [0]))
by (apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) m0 m1 buf); [|exact Hg4];
intros a Ha; rewrite !length_app in Ha; cbn [length] in Ha;
apply HK5; lia) end.
clear Hg4.
lazymatch type of HS with st_ok_pi _ _ ?Enew _ _ =>
assert (HEIn2 : img_env VAL A_LIM Enew) by (repeat apply img_env_ewset_hi; first [assumption | unfold A_LIM; lia]) end.
rebaseE HS AG HEv. clear HEv.
assert (Ht8b : 0 <= t / 8 <= 2 ^ 47) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (Ht40b : 0 <= (t + 40) / 8 <= 2 ^ 47) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (eq_trans (AG 10%nat ltac:(lia)) F10) as E10y; pose proof (eq_trans (AG 12%nat ltac:(lia)) F12) as E12y;
pose proof (eq_trans (AG 13%nat ltac:(lia)) F13) as E13y; pose proof (eq_trans (AG 11%nat ltac:(lia)) F11) as E11y end.
psrr_branch_pi RUNP BR HS.
{ lazymatch type of Hc with branch_taken BC_LT (sv_denot ?Ev ?a) (sv_denot _ ?b) = _ =>
assert (Ua : U Ev a = i + 1) by (uval; lia);
assert (Ub : U Ev b = disco_table_c.n_of T) by (uval; lia);
rewrite (tjt_blt Ev a b (i + 1) (disco_table_c.n_of T) Ua Ub ltac:(lia) ltac:(lia)) in Hc end.
apply Z.ltb_lt in Hc. rename Hc into Hlp.
paj_run_to_shc RUNTOP HS HJ4 0x5cec. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HK6 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | tjt_notw AG Hbapp Hbsep Hbsep2 Hbimg]) end.
clear HF HFr HG.
lazymatch type of HK6 with forall a, _ -> aview _ _ ?m1 a = aview _ _ ?m0 a =>
assert (Hg6 : garr8 SEGS (mrestrict (w_H W3) m1) buf ((acc ++ tjt_T5 s5) ++ tjt_T6 ag ++ [0]))
by (apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) m0 m1 buf); [|exact Hg5];
intros a Ha; rewrite !length_app in Ha; cbn [length] in Ha;
apply HK6; lia) end.
clear Hg5.
pose proof (proj1 HJ4) as HARz. destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HARz Hfin) as (_ & _ & _ & HFSz).
rewrite EFA0 in HFSz. fold F in HFSz. change (fs_frame_bytes 2 / 8) with 32 in HFSz.
fs_rwF HS E529 HFSz.
rregU HS (5%bv : bv 5) (48 * (i + 1)) ltac:(uval; lia) R5.
rregU HS (6%bv : bv 5) (i + 1) ltac:(uval; lia) R6.
rregU HS (7%bv : bv 5) (SB + t / 8 + 6 * (i + 1)) ltac:(uval; unfold SB; lia) R7.
rregU HS (28%bv : bv 5) (SB + (t + 40) / 8 + 6 * (i + 1)) ltac:(uval; unfold SB; lia) R28.
rregU HS (26%bv : bv 5) (L + l5 + L2) ltac:(uval; lia) R26.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
let fa := eval vm_compute in (f_atoms (ss_facts ssv)) in let al := eval vm_compute in (f_alias (ss_facts ssv)) in
pose proof (st_ok_pi_facts_incl Ev ssv msv fa al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3 end.
clear HS. rename HS3 into HS. norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let dl := eval cbv in ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 26; 28; 29; 30; 31]%bv : list (bv 5)) in
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dl) in
let vals' := eval cbn [map ms_regs restrict] in vals in
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_havoc_hi 950 Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS; hei_havoc HS; set_regs_rec HS 950%nat vals' 0%nat dl end.
norm_ss HS.
ra_join HS ss_tjL 720%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 26; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 720%nat 1%nat R5 E721n. ra_join_val HS 720%nat 2%nat R6 E722n. ra_join_val HS 720%nat 3%nat R7 E723n.
ra_join_val HS 720%nat 13%nat R26 E733n. ra_join_val HS 720%nat 14%nat R28 E734n.
hei_havoc HS. rebaseE HS AG HEv. clear HEv.
assert (HLe : Z.of_nat (length (acc ++ tjt_T5 s5 ++ tjt_T6 ag)) = L + l5 + L2)
by (rewrite !length_app; lia).
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B STK EV IMG _ _ FL (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx' Ev k ly3 S3 Wg msF mdF Hf1 Hf2) end end.
+ exact HBASE.
+ unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [exact AG|]. split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529 | assumption].
+ cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ4.
+ cbn [c_S c_fpos]. exact HFR.
+ unfold INV_tjL. cbn [c_cap c_T c_now c_buf c_t c_ly c_S].
split; [exact Hk0|]. split; [exact Hperm|]. split; [tjt_keepq (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0)|]. split; [lia|]. split; [lia|].
split; [exact E721n|]. split; [exact E722n|]. split; [exact E723n|]. split; [exact E734n|].
exists (acc ++ tjt_T5 s5 ++ tjt_T6 ag).
split; [rewrite E733n, HLe; reflexivity|]. split; [rewrite HLe; lia|].
split; [rewrite Htxt; rewrite <- !app_assoc; reflexivity|].
rewrite <- !app_assoc in Hg6. rewrite <- !app_assoc. exact Hg6.
+ exact HS. }
{ lazymatch type of Hc with branch_taken BC_LT (sv_denot ?Ev ?a) (sv_denot _ ?b) = _ =>
assert (Ua : U Ev a = i + 1) by (uval; lia);
assert (Ub : U Ev b = disco_table_c.n_of T) by (uval; lia);
rewrite (tjt_blt Ev a b (i + 1) (disco_table_c.n_of T) Ua Ub ltac:(lia) ltac:(lia)) in Hc end.
apply Z.ltb_ge in Hc. rename Hc into Hlp.
paj_run_to_shc RUNTOP HS HJ4 0x61b0. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HK7 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | tjt_notw AG Hbapp Hbsep Hbsep2 Hbimg]) end.
clear HF HFr HG.
lazymatch type of HK7 with forall a, _ -> aview _ _ ?m1 a = aview _ _ ?m0 a =>
assert (Hg7 : garr8 SEGS (mrestrict (w_H W3) m1) buf ((acc ++ tjt_T5 s5) ++ tjt_T6 ag ++ [0]))
by (apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) m0 m1 buf); [|exact Hg5];
intros a Ha; rewrite !length_app in Ha; cbn [length] in Ha;
apply HK7; lia) end.
clear Hg5.
pose proof (proj1 HJ4) as HARz. destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HARz Hfin) as (_ & _ & _ & HFSz).
rewrite EFA0 in HFSz. fold F in HFSz. change (fs_frame_bytes 2 / 8) with 32 in HFSz.
fs_rwF HS E529 HFSz.
rregU HS (26%bv : bv 5) (L + l5 + L2) ltac:(uval; lia) R26.
ra_join HS ss_tjC 680%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 21; 23; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 680%nat 15%nat R26 E695.
hei_havoc HS. rebaseE HS AG HEv. clear HEv.
assert (HLe : Z.of_nat (length (acc ++ tjt_T5 s5 ++ tjt_T6 ag)) = L + l5 + L2)
by (rewrite !length_app; lia).
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B STK EV IMG _ _ FC (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx' Ev k ly3 S3 Wg msF mdF Hf1 Hf2) end end.
+ exact HBASE.
+ unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [exact AG|]. split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529 | assumption].
+ cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ4.
+ cbn [c_S c_fpos]. exact HFR.
+ unfold INV_tjC. cbn [c_cap c_T c_now c_buf c_t c_ly c_S].
assert (HkE : EVB * (i + 1) <= EVB * 8) by (apply Z.mul_le_mono_nonneg_l; lia).
split; [lia|]. split; [exact Hperm|]. split; [tjt_keepq (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0)|]. split; [lia|].
exists (acc ++ tjt_T5 s5 ++ tjt_T6 ag).
split; [rewrite E695, HLe; reflexivity|]. split; [rewrite HLe; lia|].
split.
{ rewrite Htxt. replace (i + 1) with (disco_table_c.n_of T) by lia. rewrite tj_lemmas.tj_rest_end by lia.
rewrite <- !app_assoc. reflexivity. }
rewrite <- !app_assoc in Hg7. rewrite <- !app_assoc. exact Hg7.
+ exact HS. }
Qed.
Theorem pb_tj_tail_sh : tj_seg_tail B STK EV EVB IMG.
Proof.
unfold tj_seg_tail, tj_fromT, tj_from0.
intros i FX FC FL cx E k ly3 S3 W3 ms3 md3 HBASE HEX HJ HFR HINV HS.
destruct cx as [fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0].
pose proof HBASE as HB0. pose proof HEX as HX0. unfold tj_baseX in HB0. unfold tj_EX, tj_F, tj_FL in HX0.
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0 tj_F tj_FL]
in HB0, HX0, HINV, HJ, HFR, HS.
pose proof HB0 as (HPRE & Hfrm0 & Hroom & HROD & HIM & H10 & H11 & H12 & H13 & Hnow & Hcap & Hobj & Harr & HlenT & Hok
& Hbuf & Hev & Hsp1b & HE0 & HE032 & HE02).
pose proof HX0 as (AG & E60 & E516 & E528 & E529 & HEI).
unfold INV_tjT, tj_lbody, tj_wrote, tj_split in HINV. cbn [c_cap c_T c_now c_buf c_t c_ly c_S] in HINV.
destruct HINV as (Hk0 & (Hperm & HKEEP & Hcap3 & Hi & E721 & E722 & E723 & E734 & E740 & E741) & acc &
(o1 & o2 & E852 & E844 & Ho1 & Ho2 & Ho12) & Hacc & Htxt & Hgarr).
unfold w64 in E721, E722, E723, E734, E740, E741, E852, E844.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity. assert (HSNP : SNPRINTF_STK = 11776) by reflexivity.
assert (HSK : 11776 + 640 <= STK) by (unfold TJ_FRAME in HSTK; lia).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBOK. pose proof pa_base_lo as HBLO.
destruct (sp1_facts (spZ regs + -288) ltac:(clear - Hceil Hslo Hstk0 HSK C1; lia)
ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
rewrite <- Hsp1b in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 304 <= sp1 <= spZ regs - 288) by (clear - Hsp1r; lia). clear Hsp1r.
pose (RUN := paj_run (fx := fq) B LAWS). pose (RUNTO := paj_run_to (fx := fq) B LAWS).
pose (BR := paj_branch (fx := fq) (PI := PI)).
pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & Hnev3 & Hk3 & _ & _ & _ & _ & _ & Hpres3 & _ & _ & HQT3).
destruct (al_layout _ _ LAWS ly S W mem md ly3 HAR Hly3) as (Eab3 & EFA & Eown3).
assert (EFA0 : forall c p, frame_addr ly3 c p = frame_addr ly c p) by exact EFA.
set (F := frame_addr ly 2 fpos) in *. set (FLg := flag_addr ly 2 fpos) in *.
assert (Hfin : In (2, fpos) (frames S3)) by (rewrite HFR; left; reflexivity).
assert (E1 : ew E 1 = getr regs 1) by (rewrite (AG 1%nat ltac:(lia)); exact (HE0 1%nat 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite (AG 2%nat ltac:(lia)); exact (HE0 2%nat 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite (AG 3%nat ltac:(lia)); exact (HE0 3%nat 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite (AG 4%nat ltac:(lia)); exact (HE0 4%nat 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite (AG 10%nat ltac:(lia)); rewrite (HE0 10%nat 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 now) by (rewrite (AG 11%nat ltac:(lia)); rewrite (HE0 11%nat 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 buf) by (rewrite (AG 12%nat ltac:(lia)); rewrite (HE0 12%nat 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat ltac:(lia)); rewrite (HE0 13%nat 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat ltac:(lia)); exact HE032).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat ltac:(lia)); exact HE02).
assert (F12 : ew E0 12 = Z_to_bv 64 buf) by (rewrite (HE0 12%nat 12%bv eq_refl); exact H12).
assert (F13 : ew E0 13 = Z_to_bv 64 cap) by (rewrite (HE0 13%nat 13%bv eq_refl); exact H13).
assert (F10 : ew E0 10 = Z_to_bv 64 t) by (rewrite (HE0 10%nat 10%bv eq_refl); exact H10).
assert (F11 : ew E0 11 = Z_to_bv 64 now) by (rewrite (HE0 11%nat 11%bv eq_refl); exact H11).
img_factsF E.
pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as Hob242. pose proof (pa_obj_img 0 ltac:(unfold disco_nobj; lia)) as Hob241.
pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as Hob307. pose proof (pa_obj_img 67 ltac:(unfold disco_nobj; lia)) as Hob308.
cbv [A_OBJ Nat.add] in Hob241, Hob242, Hob307, Hob308.
pose proof (palf_uar_img B TL) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
unfold IMG_LO, IMG_TOP in Hob241, Hob242, Hob307, Hob308, Huar.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR3 Hfin) as (HFal & [HFhi _] & HFpres & HFSpres).
rewrite EFA in HFal, HFhi, HFpres, HFSpres. fold F in HFal, HFhi, HFpres, HFSpres.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 2 fpos HAR3 Hfin) as (HF4096 & HFceil & HFhigh).
rewrite EFA in HF4096, HFceil, HFhigh. fold F in HF4096, HFceil, HFhigh.
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hfin) as HFhigh_img. rewrite EFA in HFhigh_img. fold F in HFhigh_img.
change (fs_frame_bytes 2) with 256 in *.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
pose proof Hobj as ((cidt & post & Hint & Hcidt & Hfa8 & Htlo & Hthi) & Ht8 & Htra0).
assert (Hint3 : In (cidt, post) (frames S3)) by (rewrite HFR; right; exact Hint).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cidt post HAR Hint) as (HT4096 & HTceil & HTapp).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hint3) as HTimg. rewrite EFA in HTimg.
assert (HTF : zdisjoint (frame_rng ly3 (2, fpos)) (frame_rng ly3 (cidt, post))).
{ destruct (in_split _ _ Hint) as (l2 & l3 & El). apply (sep_frames_pos SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ [] l2 l3 HAR3).
rewrite HFR, El. reflexivity. }
unfold zdisjoint, frame_rng in HTF. cbn [fst snd] in HTF. rewrite !EFA in HTF. fold F in HTF.
change (fs_frame_bytes 2) with 256 in HTF.
pose proof (fs_frame_bytes_nonneg cidt) as HTb0.
set (TB := fs_frame_bytes cidt) in *. set (FT := frame_addr ly cidt post) in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HTapp. unfold off_img, IMG_LO, IMG_TOP in HTimg.
destruct Hok as (HT1 & HT2 & HT3 & HT4).
unfold tj_keep, afobj in HKEEP. cbn [c_t c_ly c_S c_T] in HKEEP. destruct HKEEP as (HROD3 & HG3 & (_ & _ & HRA3)). unfold disco_table_c.tbl_T1 in HT1.
destruct (HT4 i Hi) as (_ & _ & Hown).
assert (Ht400 : t + 400 <= FT + TB) by lia.
assert (Hinb0 : In (buf, Nb) (ablocks B ly S)) by exact (proj1 (Hbuf Hcap3)).
assert (Hcapb : cap <= req_size Nb) by exact (proj2 (Hbuf Hcap3)).
assert (Hinb : In (buf, Nb) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hinb0]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ buf Nb HAR3 Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & _ & _ & HNb).
pose proof (blk_off_imgP _ _ _ _ _ _ buf Nb HAR3 Hinb) as Hbimg.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ buf Nb 2 fpos HAR3 Hinb Hfin) as Hbsep.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ buf Nb cidt post HAR3 Hinb Hint3) as Hbsep2.
rewrite EFA0 in Hbsep, Hbsep2. fold F FT in Hbsep, Hbsep2. change (fs_frame_bytes 2) with 256 in Hbsep. fold TB in Hbsep2.
unfold zdisjoint in Hbsep, Hbsep2. cbn [fst snd] in Hbsep, Hbsep2.
unfold in_app, kLowShadowBeg, kHighMemBeg in Hbapp. unfold off_img, IMG_LO, IMG_TOP in Hbimg.
box HTapp. box HTimg. box HTF. box Hbapp. box Hbimg. box Hbsep. box Hbsep2.
fs_roF HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_fact Ev ssv msv 740 (PTR 3) HS
ltac:(unfold afact_ok, PTR; cbn [af_lo af_hi af_al2]; rewrite E740; rewrite unsigned_lit_small by lia;
change (2 ^ 3) with 8; split; [lia|]; split; [|lia]; rewrite Z.add_mod by lia; rewrite Ht8;
replace (48 * i) with (8 * (6 * i)) by lia; rewrite Z.mul_comm, Z_mod_mult; reflexivity)) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS.
destruct Hown as [Hown | Hown].
{ assert (Hu : disco_table_c.u_at T (48 * i + 24) 4 = 0).
{ apply tjt_s32; [lia | exact Hown |]. unfold disco_table_c.sub. rewrite length_firstn, length_skipn. lia. }
pose proof (tjt_vm _ t T (48 * i + 24) 4 HG3 ltac:(lia) ltac:(rewrite HlenT; lia)) as Hvm.
rewrite Hu in Hvm.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 740%nat) 24 28 0 0 [YP09.mkChunk 24 (CVal 4 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E740; rewrite unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS Ev _ (t + 48 * i) 24 4 (SLit 0) 0); [reflexivity | zside | zside |];
replace (t + 48 * i + 24) with (t + (48 * i + 24)) by lia; exact Hvm)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; unfold SB;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C3 HF4096 HFceil HF8lo HF8hi HFq HF8 Hob241 Hob242 Hob307 Hob308 Huar
HT4096 HTceil HTapp HTimg HTF Htlo Ht400 Hi HT1 HTb0;
unfold boxed in *; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS.
(shok_auto SHOK (SOff 32 0) E (mrestrict (w_H W3) (ms_mem ms3))).
(paj_run_tok RUN HS HJ SHOK Bspan).
{ change (rd_of SEGS (mrestrict (w_H W3) (ms_mem ms3))) with (aview SEGS (w_H W3) (ms_mem ms3)).
rewrite (U_atom E 32 SB E32) by (unfold SB; lia). rewrite (U_atom_off E 740 (t + 48 * i) 24 E740) by lia.
rewrite SB_SHADOW_OFF. apply (range_addressable_sub _ SHADOW_OFF t 400); [exact HRA3 | lia | lia]. }
{ awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
assert (HK1 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. eapply aview_kept_out; [exact HFr | lia | tjt_notw AG Hbapp Hbsep Hbsep2 Hbimg]. }
clear HF HFr HG.
lazymatch type of HS with st_ok _ ?Enew _ _ =>
assert (HEIn : img_env VAL A_LIM Enew) by (repeat apply img_env_ewset_hi; first [exact HEI | unfold A_LIM; lia]) end.
(rebaseE HS AG HEv). clear HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (eq_trans (AG 12%nat ltac:(lia)) F12) as E12c; pose proof (eq_trans (AG 13%nat ltac:(lia)) F13) as E13c;
let HEv := rnHEI Ev in
pose proof (img_env_atomP Ev 293 HEv ltac:(unfold A_TEXT, A_LIM; lia)) as E293;
pose proof (img_env_atomP Ev 294 HEv ltac:(unfold A_TEXT, A_LIM; lia)) as E294 end.
pose proof (proj1 HJ) as HARc.
pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD) as HRODc.
destruct (tj_snp_canary _ _ _ _ _ HARc) as (cval & HG1 & HG2).
pose proof tj_snp_gcgv as (Hgc1 & Hgc2 & Hgv1 & Hgv2). unfold IMG_LO, IMG_TOP in Hgc1, Hgc2, Hgv1, Hgv2.
pose proof TJS as (_ & _ & _ & _ & _ & _ & _ & _ & Hs53 & Hs54 & _ & _ & _ & _ & _ & Hs51 & Hs52 & _).
set (L := Z.of_nat (length acc)) in *.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rregU HS (10%bv : bv 5) (buf + L) ltac:(rewrite !U_SAlu; cbn [zalu_raw]; rewrite (U_atom Ev 12 buf E12c), (U_atom Ev 844 o2 E844), (U_atom Ev 852 o1 E852) by lia;
rewrite (zcanon_id (buf + o2)) by (unfold M64; lia); rewrite zcanon_id by (unfold M64; lia); lia) Ra0;
rregU HS (11%bv : bv 5) (cap - L) ltac:(rewrite !U_SAlu; cbn [zalu_raw]; rewrite !U_SMd; cbn [zmd_raw]; rewrite (U_atom Ev 13 cap E13c), (U_atom Ev 844 o2 E844), (U_atom Ev 852 o1 E852), !U_SLit by lia;
rewrite (tjt_sub cap o2) by (first [reflexivity | lia]); rewrite tjt_sub by (first [reflexivity | lia]); lia) Ra1 end.
prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp. prreg HS (1%bv : bv 5) Qra. prreg HS (12%bv : bv 5) Qa2. prreg HS (13%bv : bv 5) Qa3.
pose proof Hs53 as (_ & _ & H53lo & H53hi & _). pose proof Hs52 as (_ & _ & H52lo & H52hi & _).
unfold IMG_LO, IMG_TOP in H53lo, H53hi, H52lo, H52hi. cbv [A_OBJ Nat.add] in H53lo, H53hi, H52lo, H52hi.
change (Z.of_nat (length tj_f_owned)) with 11 in H53lo, H53hi. change (Z.of_nat (length s_false)) with 5 in H52lo, H52hi.
pmkst HS. rewrite HSNPC.
eapply (aj_sh_snprintf_at B LAWS pa_segs_low STK fq GC GV IMGLO IMGHI CR SNPC (ASNP fq) W3 (ms_regs ms) (ms_mem ms) (spZ regs) (tj_fp buf cap)
ly S W mem md [(2, fpos)] ly3 S3 _ k (buf + L) (cap - L) (VAL 294) tj_f_owned
ltac:(let v := eval vm_compute in (pf_parse tj_f_owned) in lazymatch v with Some ?p => exact p end)
[] (map (argZ (ms_regs ms)) [3; 4; 5; 6; 7] ++ []) [APtr s_false] (tjt_T5 s_false) cval (sp1 - spZ regs)
(Z_to_bv 64 (BASE + 24620)) _ HJ HRODc).
{ unfold spZ at 1. rewrite Qsp, E60, unsigned_lit_small by lia. lia. }
{ rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity. }
{ lia. }
{ lia. }
{ rewrite Qgp, (AG 3%nat) by lia. rewrite (HE0 3%nat 3%bv eq_refl). exact Hgp. }
{ rewrite Qtp, (AG 4%nat) by lia. rewrite (HE0 4%nat 4%bv eq_refl). exact Htp. }
{ exact Qra. }
{ apply ret_ok_codeptr_v; [lia | reflexivity]. }
{ exact Ra0. }
{ exact Ra1. }
{ rewrite Qa2, E294. reflexivity. }
{ exact (tj_snp_consts _ _ HRODc). }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r Hr. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr. zlia. }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r Hr. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr. unfold snp_out.
tjt_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; zlia). }
{ exact HG1. }
{ exact HG2. }
{ lia. }
{ lia. }
{ lia. }
{ lia. }
{ unfold snp_out. tjt_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; zlia). }
{ unfold snp_out. tjt_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; zlia). }
{ apply (tjt_fmt 53 tj_f_owned _ _ _ _ _ _ Hs53 HARc HRODc).
change (Z.of_nat (length tj_f_owned)) with 11. cbv [A_OBJ Nat.add]. unfold snp_out. tjt_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; zlia). }
{ exact (tj_ro_fmt_rng 53 tj_f_owned Hs53 ltac:(cbn; lia)). }
{ unfold tj_f_owned; discriminate. }
{ reflexivity. }
{ repeat (apply Forall_cons; [exact I|]); apply Forall_nil. }
{ split; [reflexivity | intros j Hj; cbn in Hj; zlia]. }
{ cbn [length Z.of_nat]. lia. }
{ unfold snp_out. tjt_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; zlia). }
{ cbn [pf_args_asan map app]. split; [|exact I].
assert (A3 : argZ (ms_regs ms) 3 = VAL 293).
{ unfold argZ. replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Qa3, E293. apply unsigned_lit_small. lia. }
rewrite A3. apply (tjt_strarg 52 s_false _ _ _ _ _ _ Hs52 HARc HRODc).
change (Z.of_nat (length s_false)) with 5. cbv [A_OBJ Nat.add]. unfold snp_out. tjt_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; zlia). }
{ cbn [map app SnFF.pf_args_amem].
assert (A3 : argZ (ms_regs ms) 3 = VAL 293).
{ unfold argZ. replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Qa3, E293. apply unsigned_lit_small. lia. }
rewrite A3. split; [exact (tj_ro_amem8 52 s_false Hs52) | exact I]. }
{ reflexivity. }
{ zlia. }
{ cbn. zlia. }
{ zlia. }
{ zlia. }
{ unfold snp_out. cbn [pairwise].
split; [apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil] | split; [apply Forall_nil | exact I]]. }
{ intros a Ha. split; [|zlia]. right. left. split.
+ exists (buf, buf + cap). split; [unfold tj_fp; rewrite (proj2 (Z.ltb_ge cap 3) Hcap3); left; reflexivity | cbn [fst snd]; lia].
+ exists buf, Nb. split; [exact Hinb | lia]. }
{ apply (amem_range_of_block8 SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); zlia. }
{ apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); zlia. }
{ apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); zlia. }
{ eapply tj_dest_off_globals; [exact (proj1 tj_snp_img) | exact (proj2 tj_snp_img) | exact HARc | exact Hinb | lia | lia]. }
{ exact Hfrm0. }
intros fx' regs2 mem2 md2 Hf1 Hf2 HJ2 HP2 Ha0' Hwr Hnul Hfr Hpres2 Hsame.
replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hfr by lia. rewrite HSNP in Hfr.
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat AG ltac:(idtac; tjt_kept AG Hfr Hpres2 Hbapp Hbsep Hbsep2 Hbimg).
apply (st_ok_pi_restrict_fx fq fx') in HS.
assert (HP5 : P5 (tj_e (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) i) = tjt_T5 s_false).
{ unfold tj_e, P5, owned_text, key, k_owned, tjt_T5. cbn [c_T]. unfold reac_disco_table_json_c.tj_entry. cbn [e_owned].
rewrite Hown. reflexivity. }
unfold tj_after4 in Htxt. rewrite HP5 in Htxt. cbn [c_now c_T] in Htxt.
prreg HS (10%bv : bv 5) Qr0. cbn [ms_regs] in Qr0. rewrite Ha0' in Qr0. symmetry in Qr0. unfold w64 in Qr0.
ra_join HS ss_tjA 950%nat (@nil (bv 5)) idtac.
hei_havoc HS. rebaseE HS AG HEv. clear HEv.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B STK EV IMG _ _ (tjt_seg_A i FX FC FL) (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx' Ev k ly3 S3 Wg msF mdF Hf1 Hf2) end end.
+ exact HBASE.
+ unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [exact AG|]. split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529 | assumption].
+ cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ2.
+ cbn [c_S c_fpos]. exact HFR.
+ unfold INV_tjA, tj_lbody, tj_split. cbn [c_cap c_T c_now c_buf c_t c_ly c_S ms_mem mkst].
split; [exact Hk0|]. split.
{ split; [exact Hperm|]. split; [tjt_keepq (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0)|]. split; [lia|]. split; [lia|].
repeat split; assumption. }
exists acc, s_false. split; [exists o1, o2; repeat split; assumption|]. split; [left; reflexivity|].
split; [exact Qr0|]. split; [lia|]. split; [exact Htxt|].
intros Hlt.
apply (tjt_garr8_snp (w_H W3) (ms_mem ms) mem2 buf acc (tjt_T5 s_false) (cap - L) L (buf + L)).
- reflexivity.
- reflexivity.
- apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms3) (ms_mem ms) buf).
* intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. apply HK1. lia.
* exact Hgarr.
- lia.
- exact Hwr.
- exact Hnul.
- intros a Ha. apply Hfr; zlia.
+ exact HS.
}
{ assert (Hu : disco_table_c.u_at T (48 * i + 24) 4 = 1).
{ apply tjt_s32; [lia | exact Hown |]. unfold disco_table_c.sub. rewrite length_firstn, length_skipn. lia. }
pose proof (tjt_vm _ t T (48 * i + 24) 4 HG3 ltac:(lia) ltac:(rewrite HlenT; lia)) as Hvm.
rewrite Hu in Hvm.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 740%nat) 24 28 0 0 [YP09.mkChunk 24 (CVal 4 (SLit 1))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E740; rewrite unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS Ev _ (t + 48 * i) 24 4 (SLit 1) 1); [reflexivity | zside | zside |];
replace (t + 48 * i + 24) with (t + (48 * i + 24)) by lia; exact Hvm)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; unfold SB;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 HSK C1 C3 HF4096 HFceil HF8lo HF8hi HFq HF8 Hob241 Hob242 Hob307 Hob308 Huar
HT4096 HTceil HTapp HTimg HTF Htlo Ht400 Hi HT1 HTb0;
unfold boxed in *; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS.
(shok_auto SHOK (SOff 32 0) E (mrestrict (w_H W3) (ms_mem ms3))).
(paj_run_tok RUN HS HJ SHOK Bspan).
{ change (rd_of SEGS (mrestrict (w_H W3) (ms_mem ms3))) with (aview SEGS (w_H W3) (ms_mem ms3)).
rewrite (U_atom E 32 SB E32) by (unfold SB; lia). rewrite (U_atom_off E 740 (t + 48 * i) 24 E740) by lia.
rewrite SB_SHADOW_OFF. apply (range_addressable_sub _ SHADOW_OFF t 400); [exact HRA3 | lia | lia]. }
{ awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
assert (HK1 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. eapply aview_kept_out; [exact HFr | lia | tjt_notw AG Hbapp Hbsep Hbsep2 Hbimg]. }
clear HF HFr HG.
lazymatch type of HS with st_ok _ ?Enew _ _ =>
assert (HEIn : img_env VAL A_LIM Enew) by (repeat apply img_env_ewset_hi; first [exact HEI | unfold A_LIM; lia]) end.
(rebaseE HS AG HEv). clear HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (eq_trans (AG 12%nat ltac:(lia)) F12) as E12c; pose proof (eq_trans (AG 13%nat ltac:(lia)) F13) as E13c;
let HEv := rnHEI Ev in
pose proof (img_env_atomP Ev 292 HEv ltac:(unfold A_TEXT, A_LIM; lia)) as E292;
pose proof (img_env_atomP Ev 294 HEv ltac:(unfold A_TEXT, A_LIM; lia)) as E294 end.
pose proof (proj1 HJ) as HARc.
pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD) as HRODc.
destruct (tj_snp_canary _ _ _ _ _ HARc) as (cval & HG1 & HG2).
pose proof tj_snp_gcgv as (Hgc1 & Hgc2 & Hgv1 & Hgv2). unfold IMG_LO, IMG_TOP in Hgc1, Hgc2, Hgv1, Hgv2.
pose proof TJS as (_ & _ & _ & _ & _ & _ & _ & _ & Hs53 & Hs54 & _ & _ & _ & _ & _ & Hs51 & Hs52 & _).
set (L := Z.of_nat (length acc)) in *.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rregU HS (10%bv : bv 5) (buf + L) ltac:(rewrite !U_SAlu; cbn [zalu_raw]; rewrite (U_atom Ev 12 buf E12c), (U_atom Ev 844 o2 E844), (U_atom Ev 852 o1 E852) by lia;
rewrite (zcanon_id (buf + o2)) by (unfold M64; lia); rewrite zcanon_id by (unfold M64; lia); lia) Ra0;
rregU HS (11%bv : bv 5) (cap - L) ltac:(rewrite !U_SAlu; cbn [zalu_raw]; rewrite !U_SMd; cbn [zmd_raw]; rewrite (U_atom Ev 13 cap E13c), (U_atom Ev 844 o2 E844), (U_atom Ev 852 o1 E852), !U_SLit by lia;
rewrite (tjt_sub cap o2) by (first [reflexivity | lia]); rewrite tjt_sub by (first [reflexivity | lia]); lia) Ra1 end.
prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp. prreg HS (1%bv : bv 5) Qra. prreg HS (12%bv : bv 5) Qa2. prreg HS (13%bv : bv 5) Qa3.
pose proof Hs53 as (_ & _ & H53lo & H53hi & _). pose proof Hs51 as (_ & _ & H51lo & H51hi & _).
unfold IMG_LO, IMG_TOP in H53lo, H53hi, H51lo, H51hi. cbv [A_OBJ Nat.add] in H53lo, H53hi, H51lo, H51hi.
change (Z.of_nat (length tj_f_owned)) with 11 in H53lo, H53hi. change (Z.of_nat (length s_true)) with 4 in H51lo, H51hi.
pmkst HS. rewrite HSNPC.
eapply (aj_sh_snprintf_at B LAWS pa_segs_low STK fq GC GV IMGLO IMGHI CR SNPC (ASNP fq) W3 (ms_regs ms) (ms_mem ms) (spZ regs) (tj_fp buf cap)
ly S W mem md [(2, fpos)] ly3 S3 _ k (buf + L) (cap - L) (VAL 294) tj_f_owned
ltac:(let v := eval vm_compute in (pf_parse tj_f_owned) in lazymatch v with Some ?p => exact p end)
[] (map (argZ (ms_regs ms)) [3; 4; 5; 6; 7] ++ []) [APtr s_true] (tjt_T5 s_true) cval (sp1 - spZ regs)
(Z_to_bv 64 (BASE + 24620)) _ HJ HRODc).
{ unfold spZ at 1. rewrite Qsp, E60, unsigned_lit_small by lia. lia. }
{ rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity. }
{ lia. }
{ lia. }
{ rewrite Qgp, (AG 3%nat) by lia. rewrite (HE0 3%nat 3%bv eq_refl). exact Hgp. }
{ rewrite Qtp, (AG 4%nat) by lia. rewrite (HE0 4%nat 4%bv eq_refl). exact Htp. }
{ exact Qra. }
{ apply ret_ok_codeptr_v; [lia | reflexivity]. }
{ exact Ra0. }
{ exact Ra1. }
{ rewrite Qa2, E294. reflexivity. }
{ exact (tj_snp_consts _ _ HRODc). }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r Hr. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr. zlia. }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r Hr. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr. unfold snp_out.
tjt_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; zlia). }
{ exact HG1. }
{ exact HG2. }
{ lia. }
{ lia. }
{ lia. }
{ lia. }
{ unfold snp_out. tjt_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; zlia). }
{ unfold snp_out. tjt_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; zlia). }
{ apply (tjt_fmt 53 tj_f_owned _ _ _ _ _ _ Hs53 HARc HRODc).
change (Z.of_nat (length tj_f_owned)) with 11. cbv [A_OBJ Nat.add]. unfold snp_out. tjt_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; zlia). }
{ exact (tj_ro_fmt_rng 53 tj_f_owned Hs53 ltac:(cbn; lia)). }
{ unfold tj_f_owned; discriminate. }
{ reflexivity. }
{ repeat (apply Forall_cons; [exact I|]); apply Forall_nil. }
{ split; [reflexivity | intros j Hj; cbn in Hj; zlia]. }
{ cbn [length Z.of_nat]. lia. }
{ unfold snp_out. tjt_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; zlia). }
{ cbn [pf_args_asan map app]. split; [|exact I].
assert (A3 : argZ (ms_regs ms) 3 = VAL 292).
{ unfold argZ. replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Qa3, E292. apply unsigned_lit_small. lia. }
rewrite A3. apply (tjt_strarg 51 s_true _ _ _ _ _ _ Hs51 HARc HRODc).
change (Z.of_nat (length s_true)) with 4. cbv [A_OBJ Nat.add]. unfold snp_out. tjt_fa2 ltac:(unfold zdisjoint; cbn [fst snd]; zlia). }
{ cbn [map app SnFF.pf_args_amem].
assert (A3 : argZ (ms_regs ms) 3 = VAL 292).
{ unfold argZ. replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Qa3, E292. apply unsigned_lit_small. lia. }
rewrite A3. split; [exact (tj_ro_amem8 51 s_true Hs51) | exact I]. }
{ reflexivity. }
{ zlia. }
{ cbn. zlia. }
{ zlia. }
{ zlia. }
{ unfold snp_out. cbn [pairwise].
split; [apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil] | split; [apply Forall_nil | exact I]]. }
{ intros a Ha. split; [|zlia]. right. left. split.
+ exists (buf, buf + cap). split; [unfold tj_fp; rewrite (proj2 (Z.ltb_ge cap 3) Hcap3); left; reflexivity | cbn [fst snd]; lia].
+ exists buf, Nb. split; [exact Hinb | lia]. }
{ apply (amem_range_of_block8 SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); zlia. }
{ apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); zlia. }
{ apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); zlia. }
{ eapply tj_dest_off_globals; [exact (proj1 tj_snp_img) | exact (proj2 tj_snp_img) | exact HARc | exact Hinb | lia | lia]. }
{ exact Hfrm0. }
intros fx' regs2 mem2 md2 Hf1 Hf2 HJ2 HP2 Ha0' Hwr Hnul Hfr Hpres2 Hsame.
replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hfr by lia. rewrite HSNP in Hfr.
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat AG ltac:(idtac; tjt_kept AG Hfr Hpres2 Hbapp Hbsep Hbsep2 Hbimg).
apply (st_ok_pi_restrict_fx fq fx') in HS.
assert (HP5 : P5 (tj_e (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) i) = tjt_T5 s_true).
{ unfold tj_e, P5, owned_text, key, k_owned, tjt_T5. cbn [c_T]. unfold reac_disco_table_json_c.tj_entry. cbn [e_owned].
rewrite Hown. reflexivity. }
unfold tj_after4 in Htxt. rewrite HP5 in Htxt. cbn [c_now c_T] in Htxt.
prreg HS (10%bv : bv 5) Qr0. cbn [ms_regs] in Qr0. rewrite Ha0' in Qr0. symmetry in Qr0. unfold w64 in Qr0.
ra_join HS ss_tjA 950%nat (@nil (bv 5)) idtac.
hei_havoc HS. rebaseE HS AG HEv. clear HEv.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B STK EV IMG _ _ (tjt_seg_A i FX FC FL) (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx' Ev k ly3 S3 Wg msF mdF Hf1 Hf2) end end.
+ exact HBASE.
+ unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [exact AG|]. split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529 | assumption].
+ cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ2.
+ cbn [c_S c_fpos]. exact HFR.
+ unfold INV_tjA, tj_lbody, tj_split. cbn [c_cap c_T c_now c_buf c_t c_ly c_S ms_mem mkst].
split; [exact Hk0|]. split.
{ split; [exact Hperm|]. split; [tjt_keepq (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0)|]. split; [lia|]. split; [lia|].
repeat split; assumption. }
exists acc, s_true. split; [exists o1, o2; repeat split; assumption|]. split; [right; reflexivity|].
split; [exact Qr0|]. split; [lia|]. split; [exact Htxt|].
intros Hlt.
apply (tjt_garr8_snp (w_H W3) (ms_mem ms) mem2 buf acc (tjt_T5 s_true) (cap - L) L (buf + L)).
- reflexivity.
- reflexivity.
- apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms3) (ms_mem ms) buf).
* intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. apply HK1. lia.
* exact Hgarr.
- lia.
- exact Hwr.
- exact Hnul.
- intros a Ha. apply Hfr; zlia.
+ exact HS.
}
Qed.
End h.
End f.
End d.
