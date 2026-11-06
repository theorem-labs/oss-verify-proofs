(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 380 of its 409 lines of code are new or changed and 40 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YN3u.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YA0o YA0q YCbm YK06 YI0m YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoFrame DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC1i YC45 YC4b YC7k YC81 YC85 YC88 YCbw YCkd ACbf ACj1 DiscoACja DiscoACjr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
ClassifyCore ReacDiscoClassifyOnSegment ReacDiscoTableObserve DiscoRo ReacFrameCleanLen ReacHuntObserve ReacHuntObserveSeg
ReacHuntObserveSF.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_classify_c disco_table_c hunt_c reac_disco_table_observe_c reac_frame_clean_len_c reac_hunt_observe_c
HuntObsFacts HuntObsLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis DRO : disco_ro_unowned B.

Lemma hoH_nth_sub : forall (L : list byte) k n i, 0 <= k -> (i < n)%nat ->
  nth_error (disco_table_c.sub L k n) i = nth_error L (Z.to_nat k + i).
Proof.
intros L k n i Hk Hi. unfold disco_table_c.sub. rewrite nth_error_firstn.
destruct (Nat.ltb_spec i n) as [_|]; [|lia]. rewrite nth_error_skipn. reflexivity.
Qed.

Definition hoH_env (regs : bvmap 5 word) (out : Z) (D : list byte) : env :=
  Eimg (mkEnv (ew (Ereg regs [Z_to_bv 64 out])) (fun d => match d with 0%nat => D | _ => [] end)).
Definition hoH_rs : smem :=
  [YP09.mkRegion (Some 9%nat) 0 32 0 0 [YP09.mkChunk 24 (CVal 8 (SOff 32 0))];
   YP09.mkRegion (Some 21%nat) 0 48 0 0 [YP09.mkChunk 0 (CData 0 0 48)];
   YP09.mkRegion (Some 32%nat) 8 17 8 17 [];
   YP09.mkRegion (Some 32%nat) 20 24 20 24 []].
Definition hoH_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (21%nat, mkAF 4096 140737479966720 3);
           (27%nat, mkAF SB SB 0); (32%nat, mkAF 4096 140737479966720 3)] [] [].
Definition hoH_SH : list shent := [mkSHE 21 0 48; mkSHE 32 0 24].

Lemma hoH_ent_nth : forall (T G : list byte) i (j : nat), length T = 400%nat -> length G = 24%nat -> 0 <= i < 8 ->
  ((j < 8)%nat -> nth_error (reac_hunt_observe_c.ho_entry T G i) j = nth_error G j) /\
  ((8 <= j < 17)%nat -> nth_error (reac_hunt_observe_c.ho_entry T G i) j = nth_error T (Z.to_nat (48 * i) + j)) /\
  ((17 <= j < 20)%nat -> nth_error (reac_hunt_observe_c.ho_entry T G i) j = nth_error G j) /\
  ((20 <= j < 24)%nat -> nth_error (reac_hunt_observe_c.ho_entry T G i) j = nth_error T (Z.to_nat (48 * i) + j)).
Proof.
intros T G i j LT LG Hi. unfold reac_hunt_observe_c.ho_entry.
assert (L1 : length (disco_table_c.sub G 0 8) = 8%nat) by (apply HuntObsLib.len_sub; lia).
assert (L2 : length (disco_table_c.sub T (48 * i + 8) 9) = 9%nat) by (apply HuntObsLib.len_sub; lia).
assert (L3 : length (disco_table_c.sub G 17 3) = 3%nat) by (apply HuntObsLib.len_sub; lia).
split; [|split; [|split]]; intros Hj.
- rewrite nth_error_app1 by lia. rewrite hoH_nth_sub by lia. f_equal.
- rewrite nth_error_app2 by lia. rewrite L1. rewrite nth_error_app1 by lia. rewrite hoH_nth_sub by lia. f_equal. lia.
- rewrite nth_error_app2 by lia. rewrite L1. rewrite nth_error_app2 by lia. rewrite L2.
  rewrite nth_error_app1 by lia. rewrite hoH_nth_sub by lia. f_equal. lia.
- rewrite nth_error_app2 by lia. rewrite L1. rewrite nth_error_app2 by lia. rewrite L2.
  rewrite nth_error_app2 by lia. rewrite L3. rewrite hoH_nth_sub by lia. f_equal. lia.
Qed.

Lemma hoH_D_nth : forall (H2 T' : list byte) ii (j : nat), H2 = T' ++ skipn 400 H2 -> length T' = 400%nat -> 0 <= ii < 8 ->
  (j < 48)%nat -> nth_error (disco_table_c.sub H2 (48 * ii) 48) j = nth_error T' (Z.to_nat (48 * ii) + j).
Proof.
intros H2 T' ii j HH LT Hii Hj. rewrite hoH_nth_sub by lia. rewrite HH. apply nth_error_app1. lia.
Qed.

Lemma hoH_garr8_mbyte : forall m p (L : list byte) j, garr8 SEGS m p (map (fun b : byte => bv_unsigned b) L) ->
  (j < length L)%nat -> mbyte SEGS m (p + Z.of_nat j) = Some (nth j L (Z_to_bv 8 0)).
Proof.
intros m p L j HG Hj. destruct (HG j ltac:(rewrite length_map; exact Hj)) as [Hv Hr].
pose proof (Hv 0%nat ltac:(lia)) as H0. cbn [Z.of_nat] in H0. rewrite Z.add_0_r in H0. rewrite H0.
rewrite (nth_indep _ _ (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
rewrite map_nth. rewrite le_byte_1_0 by (pose proof (bv_unsigned_in_range 8 (nth j L (Z_to_bv 8 0))) as R; exact R).
rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma hoH_cdata : forall E m p (L : list byte) d k len base off,
  garr8 SEGS m p (map (fun b : byte => bv_unsigned b) L) -> ed E d = disco_table_c.sub L k (Z.to_nat len) ->
  0 <= k -> 0 <= len -> k + len <= Z.of_nat (length L) -> base + off = p + k ->
  YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CData d 0 len)).
Proof.
intros E m p L d k len base off HG Hd Hk Hl Hkl Hb. apply chunk_ok_cdata_intro; [lia|].
intros i Hi. exists (nth (Z.to_nat (k + i)) L (Z_to_bv 8 0)). rewrite Hd. split.
- rewrite hoH_nth_sub by lia. replace (Z.to_nat k + Z.to_nat (0 + i))%nat with (Z.to_nat (k + i)) by lia.
  apply nth_error_nth'. lia.
- replace (base + off + i) with (p + Z.of_nat (Z.to_nat (k + i))) by lia. apply hoH_garr8_mbyte; [exact HG | lia].
Qed.

Lemma hoH_out_rng : forall c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F,
  ho_base B c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F -> c_out c <> 0 ->
  4096 <= c_out c /\ c_out c + 24 <= YM05.alloc_ceiling /\
  (forall a, c_out c <= a < c_out c + 24 -> apresent (w_H W2) mem a).
Proof.
intros c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F HB Hn.
destruct HB as (HP & HM & _).
pose proof HP as ((mdc & HJc) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hout & _ & _ & _).
pose proof HJc as (HARc & _).
destruct HM as (HJ2 & Hfrs & EFA & Hperm & _). pose proof HJ2 as (HAR2 & _).
destruct (Hout Hn) as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hloc) & _ & _).
destruct Hloc as [(cid & pos & Hfi & Hf1 & Hf2) | (b & m & Hbi & Hb1 & Hb2)].
- assert (Hfi' : In (cid, pos) (frames S2)) by (rewrite Hfrs; right; exact Hfi).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR2 Hfi') as (Hf4 & Hfc & _).
  destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR2 Hfi') as (_ & _ & Hfp & _).
  rewrite EFA in Hf4, Hfc, Hfp.
  split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (Hfp a ltac:(lia))).
- assert (Hb' : In (b, m) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hbi).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hb') as (_ & Hb4 & Hbc & _ & Hbp & _).
  split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (Hbp a ltac:(lia))).
Qed.

Lemma hoH_enter : forall fq c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F ii,
  ho_base B c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F ->
  getr regs 21 = w64 (c_h c + 48 * ii) -> 0 <= ii < 8 -> c_out c <> 0 ->
  rdword (aview SEGS (w_H W2) mem) (sp1 + 24) = Some (c_out c) ->
  st_ok_pi (fx := fq) SEGS VAL (hoH_env regs (c_out c) (disco_table_c.sub H2 (48 * ii) 48)) (mkSS 0x732c sr_atoms hoH_rs None hoH_facts)
    (restrict (w_H W2) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + 0x732c)) mem (seg_rom SEGS))) /\
  sh_ok SEGS (SOff 27 0) hoH_SH (hoH_env regs (c_out c) (disco_table_c.sub H2 (48 * ii) 48)) (mrestrict (w_H W2) mem).
Proof.
intros fq c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F ii HB R21 Hii Hon Hrd.
destruct (ho_Fb B LAWS c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F HB) as (Hf4 & Hfc & Hf32 & Happ & Hfin & HF2 & Hstk & Hsp47 & Hsp1r & Hsp1al & HSTK).
destruct (ho_out_loc B LAWS c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F HB Hon) as (HoF & HoImg & HoSp & HoH & HoAm & HoM8 & Ho63).
destruct (ho_out_ok B LAWS c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F HB Hon) as (HoRa & HoHv & HoAwr).
destruct (hoH_out_rng c fpos ly2 S2 W2 mem md k2 H2 regs sp1 F HB Hon) as (Ho4 & Hoc & HoP).
destruct HB as (HP & HM & HS1 & HFe & HR & HSV).
pose proof HP as ((mdc & HJc) & _ & _ & _ & _ & _ & _ & Hwin & Hsp & _ & _ & _ & Rout & Hh0 & Hh8 & Hin & Hhb & Hhe & _ & HOK & _ & _ & _ & _ & _ & _ & _).
destruct HM as (HJ2 & Hfrs & EFA & Hperm & HK & HG2 & HFL & HL2 & Hk2).
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R22 & R26 & R27).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin2 : In (c_hb c, c_hn c) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hin).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hin2) as (_ & Hb4 & Hbc & Hbapp & _).
assert (HLH : length H2 = 480%nat) by (rewrite HL2; destruct HOK as (X & _); exact X).
set (E := hoH_env regs (c_out c) (disco_table_c.sub H2 (48 * ii) 48)).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn. pose proof (u5_range r) as Hr. unfold E, hoH_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  cbn [ew]. exact (ew_Ereg_nat regs _ n r Hn). }
assert (E32 : ew E 32 = Z_to_bv 64 (c_out c))
  by (unfold E, hoH_env; rewrite Eimg_low by (unfold A_TEXT; lia); cbn [ew]; exact (ew_Ereg_extra regs _ 0)).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E21 : ew E 21 = Z_to_bv 64 (c_h c + 48 * ii)) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (E27 : ew E 27 = Z_to_bv 64 SB) by (rewrite (EE 27%nat 27%bv eq_refl); exact R27).
assert (Ed0 : ed E 0 = disco_table_c.sub H2 (48 * ii) 48) by reflexivity.
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (Hhr : c_h c + 480 <= YM05.alloc_ceiling) by lia.
split.
- rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + apply regs_ok_by_cases. intros z Hz. cbv [all_regs In] in Hz.
    repeat (destruct Hz as [<-|Hz];
      [ lazymatch goal with |- _ = sv_denot ?E (sr_get ?sr ?q) =>
          let v := eval vm_compute in (sr_get sr q) in change (sr_get sr q) with v end;
        first
        [ reflexivity
        | lazymatch goal with |- getr _ ?q = sv_denot _ (SOff ?n 0) =>
            cbn [sv_denot]; rewrite (EE n q eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity end ]
      | ]).
    destruct Hz.
  + vm_compute. reflexivity.
  + unfold hoH_rs. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite (VB 9%nat sp1 E9) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ sp1 24 8 (SOff 32 0) (c_out c));
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      exact (val_mem_of_rdword SEGS (w_H W2) mem _ _ Hrd).
    * rewrite (VB 21%nat (c_h c + 48 * ii) E21) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (hoH_cdata E _ (c_h c) H2 0 (48 * ii) 48 (c_h c + 48 * ii) 0 HG2 Ed0); lia.
    * rewrite (VB 32%nat (c_out c) E32) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply HoP. lia.
    * rewrite (VB 32%nat (c_out c) E32) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply HoP. lia.
  + apply pairwise_disjoint_of_extents. unfold hoH_rs, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 9%nat sp1 E9) by lia. rewrite (VB 21%nat (c_h c + 48 * ii) E21) by lia. rewrite (VB 32%nat (c_out c) E32) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + unfold hoH_facts. split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E9, E21, E27, E32, !unsigned_lit_small by (unfold SB; lia).
    repeat split; try lia.
- unfold sh_ok, hoH_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + apply (shent_ok_of_range SEGS (w_H W2) mem E (SOff 27 0) 21 (c_h c) 480 (c_h c + 48 * ii) 0 48).
    * exact (range_addressable_of_block SEGS B LAWS ly2 S2 W2 mem md (c_hb c) (c_hn c) (c_h c) 480 HAR2 Hin2 Hhb Hhe).
    * rewrite (U_atom E 27 SB E27) by (unfold SB; lia). symmetry. exact SB_SHADOW_OFF.
    * apply (U_atom E 21 _ E21). lia.
    * lia.
    * lia.
    * intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
      unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
  + apply (shent_ok_of_range SEGS (w_H W2) mem E (SOff 27 0) 32 (c_out c) 24 (c_out c) 0 24 HoRa).
    * rewrite (U_atom E 27 SB E27) by (unfold SB; lia). symmetry. exact SB_SHADOW_OFF.
    * apply (U_atom E 32 _ E32). lia.
    * lia.
    * lia.
    * intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
      unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
Qed.

Lemma hoH_garr8_of : forall m p (L : list byte),
  (forall i, (i < length L)%nat -> mbyte SEGS m (p + Z.of_nat i) = Some (nth i L (Z_to_bv 8 0))) ->
  garr8 SEGS m p (map (fun b : byte => bv_unsigned b) L).
Proof.
intros m p L H j Hj. rewrite length_map in Hj.
rewrite (nth_indep _ _ (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj). rewrite map_nth.
pose proof (bv_unsigned_in_range 8 (nth j L (Z_to_bv 8 0))) as R. change (bv_modulus 8) with 256 in R.
split; [|exact R].
intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r, (H j Hj).
rewrite le_byte_1_0 by exact R. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma hoH_garr8_exit : forall m m' p (L L' : list byte) (inW : Z -> bool),
  garr8 SEGS m p (map (fun b : byte => bv_unsigned b) L) -> length L' = length L ->
  (forall i, 0 <= i < Z.of_nat (length L) -> inW i = false -> mbyte SEGS m' (p + i) = mbyte SEGS m (p + i)) ->
  (forall i, 0 <= i < Z.of_nat (length L) -> inW i = false -> nth_error L' (Z.to_nat i) = nth_error L (Z.to_nat i)) ->
  (forall i, 0 <= i < Z.of_nat (length L) -> inW i = true -> mbyte SEGS m' (p + i) = nth_error L' (Z.to_nat i)) ->
  garr8 SEGS m' p (map (fun b : byte => bv_unsigned b) L').
Proof.
intros m m' p L L' inW HG HL Hout HLo Hin. apply hoH_garr8_of. intros i Hi.
assert (Hn : nth_error L' i = Some (nth i L' (Z_to_bv 8 0))) by (apply nth_error_nth'; exact Hi).
destruct (inW (Z.of_nat i)) eqn:Hw.
- rewrite (Hin (Z.of_nat i) ltac:(lia) Hw). rewrite Nat2Z.id. exact Hn.
- rewrite (Hout (Z.of_nat i) ltac:(lia) Hw). rewrite (hoH_garr8_mbyte _ _ _ i HG ltac:(lia)).
  pose proof (HLo (Z.of_nat i) ltac:(lia) Hw) as E. rewrite Nat2Z.id in E. rewrite Hn in E.
  assert (Hn2 : nth_error L i = Some (nth i L (Z_to_bv 8 0))) by (apply nth_error_nth'; lia).
  rewrite Hn2 in E. injection E as E. rewrite E. reflexivity.
Qed.

Lemma hoH_cb1 : forall E a d s X, ed E d = X -> 0 <= s -> (Z.to_nat s + 1 <= length X)%nat ->
  YP09.cbyte SEGS E a (CVal 1 (SData d s 1)) 0 = nth_error X (Z.to_nat s).
Proof.
intros E a d s X Hd Hs Hl. cbn [YP09.cbyte sv_denot]. rewrite <- Hd in Hl |- *.
pose proof (byte_of_data_word E d s 1 0 Hs Hl ltac:(cbn; lia) ltac:(cbn; lia)) as X'.
cbn [Z.of_nat] in X'. rewrite Nat.add_0_r in X'. exact X'.
Qed.

Lemma hoH_cb4 : forall E a d s i X, ed E d = X -> 0 <= s -> (Z.to_nat s + 4 <= length X)%nat -> 0 <= i < 4 ->
  YP09.cbyte SEGS E a (CVal 4 (SExt true 32 (SData d s 4))) i = nth_error X (Z.to_nat (s + i)).
Proof.
intros E a d s i X Hd Hs Hl Hi. cbn [YP09.cbyte].
transitivity (Some (byte_of_word (Z_to_bv 64 (data_word E d s 4)) i)).
- f_equal. exact (byte_of_word_low32 true (Z_to_bv 64 (data_word E d s 4)) i Hi).
- rewrite <- (Z2Nat.id i) at 1 by lia. rewrite <- Hd in Hl |- *.
  rewrite (byte_of_data_word E d s 4 (Z.to_nat i) Hs Hl ltac:(cbn; lia) ltac:(cbn; lia)). f_equal. lia.
Qed.

Definition hoH_cov (cs : list YP09.chunk) (lo hi : Z) : bool :=
  forallb (fun k => existsb (fun ch => (YP09.c_off ch <=? lo + Z.of_nat k) && (lo + Z.of_nat k <? YP09.c_off ch + YP09.c_len ch)) cs)
    (seq 0 (Z.to_nat (hi - lo))).

Lemma hoH_cov_ok : forall cs lo hi, hoH_cov cs lo hi = true ->
  forall i, lo <= i < hi -> exists ch, In ch cs /\ YP09.c_off ch <= i < YP09.c_off ch + YP09.c_len ch.
Proof.
intros cs lo hi H i Hi. unfold hoH_cov in H. rewrite forallb_forall in H.
specialize (H (Z.to_nat (i - lo)) ltac:(apply in_seq; lia)). apply existsb_exists in H as (ch & Hin & Hc).
exists ch. split; [exact Hin|]. apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma hoH_rbytes : forall E m n lo hi wlo whi cs b (L : list byte),
  YP09.region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> base_val E (Some n) = b ->
  hoH_cov cs lo hi = true ->
  (forall ch, In ch cs -> forall k, 0 <= k < YP09.c_len ch ->
     YP09.cbyte SEGS E (b + YP09.c_off ch) (YP09.c_val ch) k = nth_error L (Z.to_nat (YP09.c_off ch + k - lo))) ->
  forall i, lo <= i < hi -> mbyte SEGS m (b + i) = nth_error L (Z.to_nat (i - lo)).
Proof.
intros E m n lo hi wlo whi cs b L (_ & _ & _ & Hcs) Hb Hcov Hag i Hi.
cbn [YP09.r_base YP09.r_chunks] in Hcs. rewrite Hb in Hcs.
destruct (hoH_cov_ok cs lo hi Hcov i Hi) as (ch & Hin & Hr).
rewrite Forall_forall in Hcs.
destruct (Hcs ch Hin (i - YP09.c_off ch) ltac:(lia)) as (bt & Hb1 & Hb2).
replace (b + i) with (b + YP09.c_off ch + (i - YP09.c_off ch)) by lia. rewrite Hb2, <- Hb1.
rewrite (Hag ch Hin (i - YP09.c_off ch) ltac:(lia)). f_equal. f_equal. lia.
Qed.

Ltac hget HS r X :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as X;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in X;
    cbn [ms_regs restrict] in X
  end.

Lemma ho_seg_H : ho_seg_T_stmt B -> ho_seg_H_stmt B.
Proof.
intros ST c fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F H2 T' G r ii HB R20 Hr R21 R23 R25 Hfsh HOK2 HH2 LT' Hii Hmac Hnot HGg LG Hon Hrd HGout HTM.
pose proof (paj_run_to (fx := c_fq c) B LAWS) as RUNTO.
pose proof HB as (HP & HM & HS1 & HFe & HR & HSV).
pose proof HM as (HJ & Hfrs & EFA & Hperm & HK & HG2 & HFL & HL2 & Hk2).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R22 & R26 & R27).
pose proof HP as ((mdc & HJc) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rout & _).
destruct (ho_count (mrestrict (w_H W2) mem2) (c_h c) H2 HOK2 HG2) as [Hnr _].
rewrite (ho_sub0 H2 T' HH2 LT') in Hnr.
assert (Hii8 : 0 <= ii < 8) by lia.
destruct (ho_out_loc B LAWS c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F HB Hon) as (HoF & HoImg & HoSp & HoH & HoAm & HoM8 & Ho63).
destruct (hoH_enter (c_fq c) c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F ii HB R21 Hii8 Hon Hrd) as [HS SHOK].
set (D := disco_table_c.sub H2 (48 * ii) 48) in HS, SHOK.
set (E := hoH_env regs2 (c_out c) D) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs2 rr).
{ intros n rr Hn. pose proof (u5_range rr) as Hr5. unfold E, hoH_env. rewrite Eimg_low by (unfold A_TEXT; lia).
  cbn [ew]. exact (ew_Ereg_nat regs2 _ n rr Hn). }
assert (U32 : base_val E (Some 32%nat) = c_out c).
{ cbn [base_val]. unfold E, hoH_env. rewrite Eimg_low by (unfold A_TEXT; lia). cbn [ew].
  rewrite (ew_Ereg_extra regs2 _ 0). apply unsigned_lit_small. lia. }
assert (LD : length D = 48%nat).
{ unfold D. apply HuntObsLib.len_sub; [lia|]. rewrite HL2. destruct HOK2 as (X & _). rewrite <- HL2, X. lia. }
destruct (ho_out_ok B LAWS c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F HB Hon) as (HoRa & HoHv & HoAwr).
unfold ho_cfg.
paj_run_to_tok RUNTO HS HJ SHOK HOspan 0x71a0.
{ apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (n := 32%nat) (b := c_out c);
  [reflexivity | exact U32 | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply HoAwr; lia |].
  eapply awr_ok_cons_gen with (n := 32%nat) (b := c_out c);
  [reflexivity | exact U32 | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply HoAwr; lia |].
  apply awr_ok_nil. }
rename HFr into FRH, HG into FGH. clear HF.
pmkst HS.
hget HS (20%bv : bv 5) X20. rewrite ho_denot_reg, !ew_ewset_other in X20 by lia. rewrite (EE 20%nat 20%bv eq_refl), R20 in X20.
hget HS (25%bv : bv 5) X25. rewrite ho_denot_reg, !ew_ewset_other in X25 by lia. rewrite (EE 25%nat 25%bv eq_refl), R25 in X25.
hget HS (2%bv : bv 5) X2. rewrite ho_denot_reg, !ew_ewset_other in X2 by lia. rewrite (EE 2%nat 2%bv eq_refl), R2 in X2.
hget HS (3%bv : bv 5) X3. rewrite ho_denot_reg, !ew_ewset_other in X3 by lia. rewrite (EE 3%nat 3%bv eq_refl), R3 in X3.
hget HS (4%bv : bv 5) X4. rewrite ho_denot_reg, !ew_ewset_other in X4 by lia. rewrite (EE 4%nat 4%bv eq_refl), R4 in X4.
hget HS (8%bv : bv 5) X8. rewrite ho_denot_reg, !ew_ewset_other in X8 by lia. rewrite (EE 8%nat 8%bv eq_refl), R8 in X8.
hget HS (9%bv : bv 5) X9. rewrite ho_denot_reg, !ew_ewset_other in X9 by lia. rewrite (EE 9%nat 9%bv eq_refl), R9 in X9.
hget HS (18%bv : bv 5) X18. rewrite ho_denot_reg, !ew_ewset_other in X18 by lia. rewrite (EE 18%nat 18%bv eq_refl), R18 in X18.
hget HS (22%bv : bv 5) X22. rewrite ho_denot_reg, !ew_ewset_other in X22 by lia. rewrite (EE 22%nat 22%bv eq_refl), R22 in X22.
hget HS (26%bv : bv 5) X26. rewrite ho_denot_reg, !ew_ewset_other in X26 by lia. rewrite (EE 26%nat 26%bv eq_refl), R26 in X26.
hget HS (27%bv : bv 5) X27. rewrite ho_denot_reg, !ew_ewset_other in X27 by lia. rewrite (EE 27%nat 27%bv eq_refl), R27 in X27.
assert (HEf : forall a, 0 <= a < 2 ^ 64 -> ~ hoW c a -> aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hn. apply (ho_aview_frame E _ W2 mem2 (ms_mem ms) a FRH Ha).
  intros (rg & Hrg & Hrr). cbn in Hrg. destruct Hrg as [<- | [<- | [<- | [<- | []]]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hrr; try lia; rewrite U32 in Hrr; apply Hn; left; (split; [exact Hon | lia]). }
assert (HAf : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (ho_apr_grows _ _ _ a FGH Ha)).
assert (HRf : ho_regs_mid B c (ms_regs ms) sp1 F).
{ split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X8|]. split; [exact X9|].
  split; [exact X18|]. split; [exact X22|]. split; [exact X26 | exact X27]. }
assert (AD : forall j : nat, (8 <= j < 17 \/ 20 <= j < 24)%nat ->
  nth_error (reac_hunt_observe_c.ho_entry T' G ii) j = nth_error D j).
{ intros j Hj. destruct (hoH_ent_nth T' G ii j LT' LG Hii8) as (_ & N2 & _ & N4).
  unfold D. rewrite (hoH_D_nth H2 T' ii j HH2 LT' Hii8) by lia.
  destruct Hj; [apply N2 | apply N4]; lia. }
assert (LA : length (reac_hunt_observe_c.ho_entry T' G ii) = 24%nat).
{ unfold reac_hunt_observe_c.ho_entry. rewrite !length_app, !HuntObsLib.len_sub by lia. reflexivity. }
pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RgA. cbn [ms_mem restrict] in RgA.
pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RgB. cbn [ms_mem restrict] in RgB.
match type of RgA with YP09.region_ok _ ?E' _ _ =>
  assert (U32' : base_val E' (Some 32%nat) = c_out c) by (cbn [base_val]; rewrite !ew_ewset_other by lia; exact U32);
  assert (Ed' : ed E' 0 = D) by reflexivity end.
assert (HGA : garr8 SEGS (mrestrict (w_H W2) (ms_mem ms)) (c_out c)
  (map (fun b : byte => bv_unsigned b) (reac_hunt_observe_c.ho_entry T' G ii))).
{ apply (hoH_garr8_exit (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) (ms_mem ms)) (c_out c) G
    (reac_hunt_observe_c.ho_entry T' G ii) (fun i => ((8 <=? i) && (i <? 17)) || ((20 <=? i) && (i <? 24))) HGout).
  - rewrite LA, LG. reflexivity.
  - intros i Hi Hw. rewrite LG in Hi.
    assert (Hw' : ~ (8 <= i < 17) /\ ~ (20 <= i < 24))
      by (destruct (Z.leb_spec 8 i), (Z.ltb_spec i 17), (Z.leb_spec 20 i), (Z.ltb_spec i 24); cbn in Hw; try discriminate; lia).
    apply (mbyte_of_frame_x SEGS E _ _ _ (c_out c + i) FRH ltac:(lia)).
    intros rg Hrg. cbn in Hrg. destruct Hrg as [<- | [<- | [<- | [<- | []]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi]; try lia; rewrite U32; lia.
  - intros i Hi Hw. rewrite LG in Hi.
    assert (Hw' : ~ (8 <= i < 17) /\ ~ (20 <= i < 24))
      by (destruct (Z.leb_spec 8 i), (Z.ltb_spec i 17), (Z.leb_spec 20 i), (Z.ltb_spec i 24); cbn in Hw; try discriminate; lia).
    destruct (hoH_ent_nth T' G ii (Z.to_nat i) LT' LG Hii8) as (N1 & _ & N3 & _).
    destruct (Z_lt_le_dec i 8); [apply N1; lia | apply N3; lia].
  - intros i Hi Hw. rewrite LG in Hi.
    assert (Hw' : (8 <= i < 17) \/ (20 <= i < 24))
      by (destruct (Z.leb_spec 8 i), (Z.ltb_spec i 17), (Z.leb_spec 20 i), (Z.ltb_spec i 24); cbn in Hw; try discriminate; lia).
    destruct Hw' as [Hw' | Hw'].
    + rewrite (hoH_rbytes _ _ 32 8 17 8 17 _ (c_out c) (skipn 8 (reac_hunt_observe_c.ho_entry T' G ii)) RgA U32' ltac:(vm_compute; reflexivity)) by
        (first [ lia
               | intros ch Hch; cbn in Hch;
                 repeat (destruct Hch as [<- | Hch];
                   [ cbn [YP09.c_len YP09.c_off YP09.c_val YP09.cv_len Z.of_N]; intros k Hk;
                     rewrite nth_error_skipn;
                     first
                     [ assert (k = 0) by lia; subst k;
                       rewrite (hoH_cb1 _ _ 0 _ D Ed'); [rewrite AD by lia; f_equal; lia | lia | rewrite LD; lia]
                     | rewrite (hoH_cb4 _ _ 0 _ k D Ed'); [rewrite AD by lia; f_equal; lia | lia | rewrite LD; lia | exact Hk] ]
                   | ]); destruct Hch ]).
      rewrite nth_error_skipn. f_equal. lia.
    + rewrite (hoH_rbytes _ _ 32 20 24 20 24 _ (c_out c) (skipn 20 (reac_hunt_observe_c.ho_entry T' G ii)) RgB U32' ltac:(vm_compute; reflexivity)) by
        (first [ lia
               | intros ch Hch; cbn in Hch;
                 repeat (destruct Hch as [<- | Hch];
                   [ cbn [YP09.c_len YP09.c_off YP09.c_val YP09.cv_len Z.of_N]; intros k Hk;
                     rewrite nth_error_skipn;
                     rewrite (hoH_cb4 _ _ 0 _ k D Ed'); [rewrite AD by lia; f_equal; lia | lia | rewrite LD; lia | exact Hk]
                   | ]); destruct Hch ]).
      rewrite nth_error_skipn. f_equal. lia. }
eapply (ST c fpos ly2 S2 W2 (ms_mem ms) _ k2 (ms_regs ms) sp1 F H2 r).
- exact (ho_step B LAWS c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F _ _ _ HB HJ HEf HAf HRf).
- exact X20.
- lia.
- exact X25.
- exact (ho_fsh_step B LAWS c fpos ly2 S2 W2 mem2 md2 k2 H2 regs2 sp1 F _ _ HB HEf Hfsh).
- exact HOK2.
- exact (HoFM2.hof_mono _ _ _ _ _ _ _ _ _ _ (HTM _ eq_refl) HGA).
Qed.

End h.
End f.
End d.
