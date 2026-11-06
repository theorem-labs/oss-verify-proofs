(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YChd.v, with its module paths and module names changed; 759 of its 797 lines of code are new or changed and 507 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC81 YC1g YC1h YC4b.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import StackFreeDef StackFreeJournal.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntExitPostPf.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition x_sv (r : nat) : sv :=
  match r with
  | 0%nat => SLit 0 | 2%nat => SOff AT_A 0 | 8%nat => SOff AT_STK 0 | 9%nat => SOff AT_A 0
  | 27%nat => SOff AT_SH 0 | _ => SOff (AT_X + r) 0
  end.
Definition x_sr : list sv := map x_sv (seq 0 32).
Definition xslot_chunks : list YP09.chunk :=
  [YP09.mkChunk 32 (CVal 8 (SOff AT_F 0)); YP09.mkChunk 40 (CVal 8 (SOff AT_F 0))].
Definition xflag_chunk : YP09.chunk := YP09.mkChunk 4088 (CVal 8 (SOff AT_FL 0)).
Definition x_kregions (acs : list YP09.chunk) : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 0 0 (xslot_chunks ++ acs);
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 0 [xflag_chunk];
   fshadow_region AT_SH DFRAME_CLASS 0 0 [];
   got_regionP; bcell_regionP 32].
Definition ss_x (pc : Z) (acs : list YP09.chunk) (G : facts) : sstate :=
  mkSS pc x_sr (x_kregions acs) None G.
Ltac xx_nlt := apply Nat.ltb_lt; reflexivity.
Ltac xx_nle := apply Nat.leb_le; reflexivity.
Lemma xx_ra_rng : 0 <= RA_LLVMF < 2 ^ 64.
Proof. unfold RA_LLVMF. lia. Qed.


Lemma xx_ed_sym : forall E r r', extent_disjoint E r r' -> extent_disjoint E r' r.
Proof. unfold extent_disjoint. intros E r r' H. lia. Qed.
Lemma xx_adF : forall E r rs, all_disjoint E r rs <-> Forall (extent_disjoint E r) rs.
Proof.
  intros E r rs. induction rs as [|x rs IH]; cbn [all_disjoint].
  - split; intros _; [constructor | exact I].
  - split.
    + intros [H1 H2]. constructor; [exact H1 | apply IH; exact H2].
    + intros H. inversion H as [|? ? H1 H2]. split; [exact H1 | apply IH; exact H2].
Qed.
Lemma xx_pwd_app : forall E l1 l2, pairwise_disjoint E l1 -> pairwise_disjoint E l2 ->
  Forall (fun r => all_disjoint E r l1) l2 -> pairwise_disjoint E (l1 ++ l2).
Proof.
  intros E l1. induction l1 as [|x l1 IH]; intros l2 H1 H2 H3; cbn [app]; [exact H2|].
  cbn [pairwise_disjoint] in H1 |- *. destruct H1 as [Hx H1]. split.
  - apply xx_adF. apply Forall_app. split; [apply xx_adF; exact Hx|].
    apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) H3 r Hr) as Hd.
    cbn [all_disjoint] in Hd. apply xx_ed_sym. exact (proj1 Hd).
  - apply IH; [exact H1 | exact H2 |]. apply Forall_forall. intros r Hr.
    pose proof (proj1 (Forall_forall _ _) H3 r Hr) as Hd. cbn [all_disjoint] in Hd. exact (proj2 Hd).
Qed.
Lemma xx_rdword_range : forall segs H m a v, rdword (aview segs H m) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
  intros segs H m a v Hv. unfold rdword in Hv.
  destruct (aview segs H m a) as [b0|] eqn:E0; [|discriminate Hv].
  destruct (aview segs H m (a + 1)) as [b1|] eqn:E1; [|discriminate Hv].
  destruct (aview segs H m (a + 2)) as [b2|] eqn:E2; [|discriminate Hv].
  destruct (aview segs H m (a + 3)) as [b3|] eqn:E3; [|discriminate Hv].
  destruct (aview segs H m (a + 4)) as [b4|] eqn:E4; [|discriminate Hv].
  destruct (aview segs H m (a + 5)) as [b5|] eqn:E5; [|discriminate Hv].
  destruct (aview segs H m (a + 6)) as [b6|] eqn:E6; [|discriminate Hv].
  destruct (aview segs H m (a + 7)) as [b7|] eqn:E7; [|discriminate Hv].
  injection Hv as <-.
  assert (HB : forall x b, aview segs H m x = Some b -> 0 <= b < 256).
  { intros x b Hb. unfold aview in Hb. destruct (mbyte segs (mrestrict H m) x) as [y|]; [|discriminate Hb].
    cbn [option_map] in Hb. injection Hb as <-. pose proof (bv_unsigned_in_range _ y) as Hr.
    change (bv_modulus 8) with 256 in Hr. exact Hr. }
  apply HB in E0, E1, E2, E3, E4, E5, E6, E7. lia.
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Lemma xx_env_old : forall cx E vals n, (n < AT_FL)%nat -> ew (d_env cx E vals) n = ew E n.
Proof. intros cx E vals n Hn. unfold d_env. apply ew_havoc_old. exact Hn. Qed.
Lemma xx_env_fl : forall cx E vals,
  ew (d_env cx E vals) AT_FL = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)).
Proof.
  intros cx E vals. unfold d_env. replace AT_FL with (AT_FL + 0)%nat at 2 by lia.
  rewrite (ew_havoc_new _ AT_FL _ 0 (Z_to_bv 64 0)) by (cbn [length]; lia). reflexivity.
Qed.
Lemma xx_env_x : forall cx E vals j, (j < length vals)%nat ->
  ew (d_env cx E vals) (AT_X + j) = nth j vals (Z_to_bv 64 0).
Proof.
  intros cx E vals j Hj. unfold d_env. replace (AT_X + j)%nat with (AT_FL + S j)%nat by (unfold AT_X, AT_FL; lia).
  rewrite (ew_havoc_new _ AT_FL _ (S j) (Z_to_bv 64 0)) by (cbn [length]; lia). reflexivity.
Qed.
Lemma xx_env_agree : forall cx E vals, env_agree AT_FL E (d_env cx E vals).
Proof. intros cx E vals. split; [intros n Hn; apply xx_env_old; exact Hn | reflexivity]. Qed.
Lemma xx_E_env : forall cx E vals, d_E cx E -> d_E cx (d_env cx E vals).
Proof.
  intros cx E vals (EE & E32 & HEI & E60 & EF & ESH). unfold d_E.
  rewrite !xx_env_old by (unfold AT_FL, AT_A, AT_F, AT_SH; lia).
  split; [|split; [exact E32 | split; [|split; [exact E60 | split; [exact EF | exact ESH]]]]].
  - intros n r Hn. rewrite xx_env_old; [exact (EE n r Hn)|].
    pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32 in Hr. unfold AT_FL. lia.
  - unfold d_env. apply img_env_havoc_hi; [exact HEI | unfold A_LIM, AT_FL; lia].
Qed.
Lemma xx_den0 : forall E (k : nat) v, ew E k = Z_to_bv 64 v -> sv_denot E (SOff k 0) = Z_to_bv 64 v.
Proof. intros E k v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma xx_slot : forall E m (nn : nat) b lo hi wlo whi cs off e v,
  region_ok SEGS E m (YP09.mkRegion (Some nn) lo hi wlo whi cs) -> bv_unsigned (ew E nn) = b ->
  In (YP09.mkChunk off (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS m (b + off) 8 v.
Proof.
  intros E m nn b lo hi wlo whi cs off e v HR Hb Hin He Hv. change 8%nat with (N.to_nat 8).
  exact (field_of_region E m nn b cs lo hi wlo whi off 8%N e v HR Hb Hin He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
Lemma xx_pres_grows : forall (H : word -> bool) m m' a,
  mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
  intros H m m' a HG (Hh & b & Hb). split; [exact Hh|]. specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG.
  rewrite Hh, Hb in HG. destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity|].
  exfalso. exact (HG ltac:(discriminate) eq_refl).
Qed.
Lemma xx_dE_havoc : forall cx E kk ws, d_E cx E -> (530 <= kk)%nat -> d_E cx (havoc E kk ws).
Proof.
  intros cx E kk ws (EE & E32 & HEI & E60 & EF & ESH) Hk. unfold d_E.
  rewrite !ew_havoc_old by (unfold AT_A, AT_F, AT_SH; lia).
  split; [|split; [exact E32 | split; [|split; [exact E60 | split; [exact EF | exact ESH]]]]].
  - intros nn r Hn. rewrite ew_havoc_old; [exact (EE nn r Hn)|]. pose proof (bv_unsigned_in_range _ r) as Hr.
    change (bv_modulus 5) with 32 in Hr. lia.
  - apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia].
Qed.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MT_TRIV : MT = ameter_triv.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Variable SF6_ENTRY : Z.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis AFREE : forall fq : YK11.FPState, afree_realizes (fx := fq) SEGS B.
Hypothesis ASFW6 : forall fq : YK11.FPState, astack_free_realizes (fx := fq) SEGS B SF6_ENTRY 6.
Hypothesis HSF6 : SIGMA AS___asan_stack_free_6 = SF6_ENTRY.
Hypothesis DUNIV : duniv_ok B.
Hypothesis AIL : asink_img_laws SEGS B tfib_K.

Lemma xx_geom : forall cx ly3 S3 (W3 : world SEGS) mem3 md3 k,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 mem3 md3 k ->
  d_S cx mod 16 = 0 /\ alloc_ceiling + LLVMF_STK <= d_S cx /\ d_S cx <= 2 ^ 47 /\
  4096 <= d_FB cx /\ d_FB cx + 4096 <= alloc_ceiling /\ in_app (d_FB cx) 4096 /\
  off_img (d_FB cx) 4096 /\ d_FB cx mod 32 = 0 /\
  (forall a, d_FB cx <= a < d_FB cx + 4096 -> apresent (w_H W3) mem3 a) /\
  (forall i, 0 <= i < 512 -> apresent (w_H W3) mem3 (shadow_addr (d_FB cx) + i)) /\
  (forall a, d_S cx - LLVMF_STK <= a < d_S cx -> apresent (w_H W3) mem3 a) /\
  AR SEGS B ly3 S3 W3 mem3 md3 /\ In (DFRAME_CLASS, c_fpos cx) (frames S3) /\
  frame_addr ly3 DFRAME_CLASS (c_fpos cx) = d_FB cx /\
  flag_addr ly3 DFRAME_CLASS (c_fpos cx) = flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx).
Proof.
  intros cx ly3 S3 W3 mem3 md3 k (HB & HJ & HFR).
  destruct HB as ((HPRE & _) & _).
  pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
  assert (Hfin : In (DFRAME_CLASS, c_fpos cx) (frames S3)) by (rewrite HFR; left; reflexivity).
  destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 Hly3) as (_ & Efa & _).
  assert (Efl : flag_addr ly3 DFRAME_CLASS (c_fpos cx) = flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)).
  { pose proof (Efa 0 0) as E00. unfold frame_addr in E00. unfold flag_addr. lia. }
  destruct (frames_bounds _ _ LAWS _ _ _ _ _ DFRAME_CLASS (c_fpos cx) HAR3 Hfin) as (HF0 & HFc & HFia).
  pose proof (frm_off_imgP B ly3 S3 W3 mem3 md3 DFRAME_CLASS (c_fpos cx) HAR3 Hfin) as HFo.
  destruct (al_frames _ _ LAWS _ _ _ _ _ DFRAME_CLASS (c_fpos cx) HAR3 Hfin) as (Hal & _ & HFpres & HSpres).
  rewrite Efa in HF0, HFc, HFia, HFo, Hal, HFpres, HSpres.
  change (frame_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) with (d_FB cx) in *.
  change (fs_frame_bytes DFRAME_CLASS) with 4096 in *. change (4096 / 8) with 512 in HSpres.
  change (spZ (c_regs cx)) with (d_S cx) in *.
  split; [exact Hal16|]. split; [unfold LLVMF_STK in *; lia|]. split; [lia|].
  split; [exact HF0|]. split; [exact HFc|]. split; [exact HFia|]. split; [exact HFo|]. split; [exact Hal|].
  split; [intros a Ha; exact (proj1 (HFpres a Ha))|].
  split; [intros i Hi; exact (proj1 (HSpres i Hi))|].
  split; [intros a Ha; apply HJpres; exact Ha|].
  split; [exact HAR3|]. split; [exact Hfin|]. split; [rewrite Efa; reflexivity|]. exact Efl.
Qed.
Lemma xx_A_range : forall cx, 0 <= d_S cx - MFRAME ->
  d_S cx - MFRAME - 31 <= d_A cx <= d_S cx - MFRAME /\ d_A cx mod 32 = 0.
Proof.
  intros cx Hs. unfold d_A. pose proof (Z.div_mod (d_S cx - MFRAME) 32 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (d_S cx - MFRAME) 32 ltac:(lia)) as Hmp.
  split; [lia|]. rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

Definition x_vals (regs : bvmap 5 word) (h : Z) : list word :=
  map (fun r => getr regs (Z_to_bv 5 (Z.of_nat r))) (seq 0 32) ++ [Z_to_bv 64 h].

Lemma xx_regs_ok : forall cx E regs h, d_E cx E -> d_rX B cx h regs -> 0 <= d_A cx < 2 ^ 64 ->
  regs_ok (d_env cx E (x_vals regs h)) x_sr regs.
Proof.
  intros cx E regs h HE HL HA.
  destruct HE as (HER & H32 & _ & HA60 & _ & HASH).
  destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H27).
  apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  assert (H2 : getr regs 2 = Z_to_bv 64 (d_A cx)) by (rewrite <- Hsp; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (HS2 : ew E 2 = Z_to_bv 64 (d_S cx)).
  { rewrite (HER 2%nat 2%bv eq_refl). unfold d_S, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  change AT_A with 60%nat in HA60. change AT_SH with 529%nat in HASH.
  repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
  all: try (match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
    let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
    cbn [sv_denot];
    first
    [ rewrite getr_zero; reflexivity
    | rewrite Z.add_0_r; unfold d_env; rewrite ew_havoc_old by (cbv; lia);
      first [ rewrite HA60, Z_to_bv_bv_unsigned; first [exact H2 | exact H9]
            | rewrite HS2, Z_to_bv_bv_unsigned; exact H8
            | rewrite HASH; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H27 ]
    | rewrite Z.add_0_r; unfold d_env, havoc; cbn [ew Nat.ltb Nat.leb Nat.sub nth x_vals map seq app Nat.add AT_X AT_FL];
      match goal with |- getr ?rg _ = Z_to_bv 64 (bv_unsigned (getr ?rg ?x)) =>
        let y := eval vm_compute in x in change x with y end;
      rewrite Z_to_bv_bv_unsigned; reflexivity ]).
Qed.

Lemma xx_seat : forall (fq : YK11.FPState) (cx : dcx) ly3 S3 (W3 : world SEGS) (regs : bvmap 5 word) mem3 md3 k
  (E : env) (pc : Z) (vals : list word) (acs : list YP09.chunk) (G : facts),
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 mem3 md3 k ->
  d_E cx E -> Forall (region_ok SEGS E (rd W3 mem3)) (d_regions_x cx) ->
  rdword (aview SEGS (w_H W3) mem3) (d_FB cx + fs_frame_bytes DFRAME_CLASS - 8) =
    Some (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) ->
  regs_ok (d_env cx E vals) x_sr regs ->
  facts_ok (d_env cx E vals) G ->
  Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W3 mem3) (d_A cx)) acs ->
  regions_wf (x_kregions acs) = true ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E vals) (ss_x pc acs G)
    (restrict (w_H W3) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + pc)) mem3 (YK11.seg_rom SEGS))).
Proof.
  intros fq cx ly3 S3 W3 regs mem3 md3 k E pc vals acs G HC HE HRG HFL Hregs HG Hacs HWF.
  destruct (xx_geom cx ly3 S3 W3 mem3 md3 k HC)
    as (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR3 & Hfin & Efa & Efl).
  pose proof asan_consts as (Hac & _).
  pose proof (xx_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
  pose proof (xx_rdword_range _ _ _ _ _ HFL) as HFLr.
  destruct (al_const _ _ LAWS _ _ _ _ _ HAR3) as (Kcell & _ & Kgot & _).
  rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
  pose proof (pal_got_cell B TL) as Hgc.
  pose proof (pa_obj_img 0 ltac:(vm_compute; lia)) as HO1. pose proof (pa_obj_img 12 ltac:(vm_compute; lia)) as HO12.
  pose proof (pa_val_range (A_OBJ 0)) as HV1. pose proof (pa_val_range (A_OBJ 12)) as HV12.
  unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HO1, HO12. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HFo.
  set (E' := d_env cx E vals) in *.
  pose proof (xx_env_agree cx E vals) as HAG. fold E' in HAG.
  pose proof (xx_env_fl cx E vals) as EFL. fold E' in EFL.
  destruct (xx_E_env cx E vals HE) as (EE & E32 & HEI & E60 & EF & ESH). fold E' in EE, E32, HEI, E60, EF, ESH.
  assert (Hd0 : 0 <= d_FB cx / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : d_FB cx / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
  assert (U2 : base_val E' (Some AT_STK) = d_S cx).
  { cbn [base_val]. unfold AT_STK. rewrite (EE 2%nat 2%bv eq_refl). reflexivity. }
  assert (U60 : base_val E' (Some AT_A) = d_A cx).
  { cbn [base_val]. rewrite E60. apply unsigned_lit_small. unfold MFRAME, LLVMF_STK in *. lia. }
  assert (U516 : base_val E' (Some AT_F) = d_FB cx).
  { cbn [base_val]. rewrite EF. apply unsigned_lit_small. lia. }
  assert (U529 : base_val E' (Some AT_SH) = shadow_addr (d_FB cx)).
  { cbn [base_val]. rewrite ESH. apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF. lia. }
  assert (EA : forall n, (A_TEXT <= n < A_LIM)%nat -> base_val E' (Some n) = VAL n).
  { intros n Hn. cbn [base_val]. rewrite (img_env_atomP E' n HEI Hn). apply unsigned_lit_small. apply pa_val_range. }
  assert (UG1 : base_val E' (Some (A_OBJ 0)) = VAL (A_OBJ 0)) by (apply EA; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (UG12 : base_val E' (Some (A_OBJ 12)) = VAL (A_OBJ 12)) by (apply EA; unfold A_OBJ, A_TEXT, A_LIM; lia).
  unfold d_regions_x in HRG.
  pose proof (Forall_inv HRG) as R1. apply Forall_inv_tail in HRG.
  pose proof (Forall_inv HRG) as R2. apply Forall_inv_tail in HRG.
  pose proof (Forall_inv HRG) as R3. apply Forall_inv_tail in HRG.
  pose proof (Forall_inv HRG) as R4. clear HRG.
  lazymatch type of R1 with region_ok _ _ ?m ?r =>
    assert (R1x : region_ok SEGS E' m r) by (apply (region_ok_agree SEGS AT_FL E E' m r HAG); [vm_compute; reflexivity | exact R1]) end.
  clear R1. rename R1x into R1.
  lazymatch type of R2 with region_ok _ _ ?m ?r =>
    assert (R2x : region_ok SEGS E' m r) by (apply (region_ok_agree SEGS AT_FL E E' m r HAG); [vm_compute; reflexivity | exact R2]) end.
  clear R2. rename R2x into R2.
  lazymatch type of R3 with region_ok _ _ ?m ?r =>
    assert (R3x : region_ok SEGS E' m r) by (apply (region_ok_agree SEGS AT_FL E E' m r HAG); [vm_compute; reflexivity | exact R3]) end.
  clear R3. rename R3x into R3.
  lazymatch type of R4 with region_ok _ _ ?m ?r =>
    assert (R4x : region_ok SEGS E' m r) by (apply (region_ok_agree SEGS AT_FL E E' m r HAG); [vm_compute; reflexivity | exact R4]) end.
  clear R4. rename R4x into R4.
  unfold ss_x. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - exact Hregs.
  - exact HWF.
  - unfold x_kregions. repeat apply Forall_cons; try apply Forall_nil.
    + exact R1.
    + destruct R2 as (B1 & B2 & W2 & C2). unfold region_ok. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in B1, B2, W2, C2 |- *.
      split; [exact B1|]. split; [exact B2|]. split; [intros o Ho; lia|]. apply Forall_app. split; [exact C2|].
      rewrite U60. exact Hacs.
    + destruct R3 as (B1 & B2 & W2 & C2). unfold region_ok. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in B1, B2, W2, C2 |- *.
      split; [exact B1|]. split; [exact B2|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
      unfold xflag_chunk. rewrite U516.
      apply (chunk_ok_val SEGS E' _ (d_FB cx) 4088 8%N (SOff AT_FL 0) (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx))).
      * cbn [sv_denot]. rewrite EFL, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      * cbn [Z.of_N]. change (8 * 8) with 64. exact HFLr.
      * cbn [Z.of_N]. lia.
      * cbn [N.to_nat]. change (fs_frame_bytes DFRAME_CLASS) with 4096 in HFL.
        replace (d_FB cx + 4088) with (d_FB cx + 4096 - 8) by lia.
        exact (val_mem_of_rdword SEGS (w_H W3) mem3 _ _ HFL).
    + unfold fshadow_region in R4 |- *. destruct R4 as (B1 & B2 & W2 & C2). unfold region_ok. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in B1, B2, W2, C2 |- *.
      split; [exact B1|]. split; [exact B2|]. split; [intros o Ho; lia | apply Forall_nil].
    + unfold got_regionP, region_ok. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite UG1. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E' _ (VAL (A_OBJ 0)) 0 8%N (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12))).
      * cbn [sv_denot]. rewrite (img_env_atomP E' (A_OBJ 12) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
        rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
      * cbn [Z.of_N]. change (8 * 8) with 64. lia.
      * cbn [Z.of_N]. lia.
      * cbn [N.to_nat]. rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W3) mem3 _ _ Kgot).
    + unfold bcell_regionP, region_ok. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite UG12. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E' _ (VAL (A_OBJ 12)) 0 8%N (SOff 32 0) SHADOW_OFF).
      * cbn [sv_denot]. rewrite E32. unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
        rewrite Z.add_0_r. reflexivity.
      * cbn [Z.of_N]. change (8 * 8) with 64. unfold SHADOW_OFF. lia.
      * cbn [Z.of_N]. lia.
      * cbn [N.to_nat]. rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W3) mem3 _ _ Kcell).
  - apply pairwise_disjoint_of_extents.
    unfold x_kregions, fshadow_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite U2, U60, U516, U529, UG1, UG12.
    change (fs_frame_bytes DFRAME_CLASS) with 4096. change (4096 / 8) with 512.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold shadow_addr, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF, MFRAME, LLVMF_STK in *.
    repeat split; lia.
  - exact HG.
Qed.

Lemma xx_call_chain : forall (pc0 off : Z) (cx : dcx) ly3 S3 (W3 : world SEGS) mem3 md3 k
  (regs : bvmap 5 word) (V0 : Z),
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 mem3 md3 k ->
  pc0 < BASE -> 0 <= off -> 4096 <= BASE + off ->
  In [pc0; BASE + off] (as_universe B) -> In [pc0; BASE + off; RA_LLVMF] (as_universe B) ->
  spZ regs = d_A cx -> s0Z regs = d_S cx -> d_A cx + 16 <= d_S cx -> raZ regs = BASE + off ->
  rdword (aview SEGS (w_H W3) mem3) (d_S cx - 8) = Some RA_LLVMF ->
  rdword (aview SEGS (w_H W3) mem3) (d_S cx - 16) = Some V0 ->
  (bad_next (d_S cx) (ly_top ly3) V0 = true \/ fpchain (rdword (aview SEGS (w_H W3) mem3)) V0 (ly_top ly3) []) ->
  exists ch, chain_pre ly3 (aview SEGS (w_H W3) mem3) regs ch /\
    In (call_trace0 pc0 regs ch) (as_universe B).
Proof.
intros pc0 off cx ly3 S3 W3 mem3 md3 k regs V0 Hctx Hpc0 Hoff Hra4 HU2 HU3 Hsp Hs0 HAS Hra Hsave HV0 HCH.
assert (Hrane : (BASE + off =? pc0) = false) by (apply Z.eqb_neq; lia).
assert (Htr0 : forall l, (length l <= 1)%nat -> In (pc0 :: [BASE + off] ++ l) (as_universe B) ->
          In (firstn kUnwindMax (pc0 :: (if BASE + off =? pc0 then [] else [BASE + off]) ++ l)) (as_universe B)).
{ intros l Hlen Hl. rewrite Hrane. cbn [app] in *.
  destruct l as [|x [|y l']]; cbn [length] in Hlen; try lia;
  change kUnwindMax with 30%nat; cbn [firstn]; exact Hl. }
assert (Htr1 : In (firstn kUnwindMax (pc0 :: (if BASE + off =? pc0 then [] else [BASE + off]) ++
          (if RA_LLVMF =? pc0 then [] else [RA_LLVMF]) ++ [])) (as_universe B)).
{ destruct (Z.eqb_spec RA_LLVMF pc0) as [He|Hne].
  - apply Htr0; [cbn [length app]; lia|]. cbn [app]. exact HU2.
  - apply Htr0; [cbn [length app]; lia|]. cbn [app]. exact HU3. }
unfold chain_pre, frame0_ok, call_trace0, unwind_of_chain.
rewrite Hra.
destruct (spZ regs + 16 <? ly_top ly3) eqn:Hf0.
- destruct (bad_next (spZ regs) (ly_top ly3) (s0Z regs)) eqn:Hbn.
  + exists []. split; [split; [lia | reflexivity]|].
    cbn [flat_map app]. apply Htr0; [cbn [length]; lia|]. cbn [app]. exact HU2.
  + exists [(s0Z regs, RA_LLVMF, V0)]. split.
    { unfold bad_next in Hbn.
      apply Bool.orb_false_elim in Hbn as [Hbn1 Hbn3].
      apply Bool.orb_false_elim in Hbn1 as [Hbn1 Hbn2].
      apply Z.leb_gt in Hbn1. apply Z.leb_gt in Hbn2.
      apply Bool.negb_false_iff, Z.eqb_eq in Hbn3.
      split; [lia|]. split; [lia|].
      cbn [fpchain]. split; [reflexivity|]. split; [exact Hbn3|].
      rewrite <- Hs0 in Hsave, HV0. split; [exact Hsave|]. split; [exact HV0|].
      split; [unfold RA_LLVMF; lia|].
      rewrite Hs0. destruct HCH as [Hb|Hf].
      - rewrite Hb. reflexivity.
      - destruct (bad_next (d_S cx) (ly_top ly3) V0); [reflexivity | exact Hf]. }
    { cbn [flat_map app]. exact Htr1. }
- exists []. split; [split; [lia | reflexivity]|].
  cbn [flat_map app]. apply Htr0; [cbn [length]; lia|]. cbn [app]. exact HU2.
Qed.

Lemma xx_chain_disj : forall cx ly3 S3 (W3 : world SEGS) m3 md3 k,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 m3 md3 k ->
  bad_next (d_S cx) (ly_top ly3) (s0Z (c_regs cx)) = true \/
  fpchain (rdword (aview SEGS (w_H W3) m3)) (s0Z (c_regs cx)) (ly_top ly3) [].
Proof.
intros cx ly3 S3 W3 m3 md3 k (HB & HJ & _).
destruct HB as ((HPRE & _) & _).
destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
rewrite Etop. change (spZ (c_regs cx)) with (d_S cx) in *.
destruct Hch as [(Hb & _) | (H1 & H2 & H3 & Hf & _)].
- left. unfold bad_next. destruct Hb as [Hb|[Hb|Hb]].
  + rewrite (proj2 (Z.leb_le (s0Z (c_regs cx)) (d_S cx)) ltac:(lia)). reflexivity.
  + rewrite (proj2 (Z.leb_le (ly_top (c_ly cx) - 16) (s0Z (c_regs cx))) Hb), Bool.orb_true_r. reflexivity.
  + rewrite (proj2 (Z.eqb_neq _ _) Hb), Bool.orb_true_r. reflexivity.
- right. cbn [fpchain] in Hf |- *. destruct Hf as (r & Hr & Hr2). exists r. split; [|exact Hr2].
  rewrite <- Hr. apply rdword_ext. intros k0 Hk0. apply F1; lia.
Qed.
Ltac xx_in := cbn [In]; repeat (first [left; reflexivity | right]).

Theorem pb_exit : exit_spec B MT XM_LIB XN_LIB RLO RHI tfib_K.
Proof.
unfold exit_spec. intros cx h W c Hpre.
destruct Hpre as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm0 & HB & HJ & HFR & Hk & Hev & Hmo & Hacc &
  HX & Hfrx & Hblk & Himg & H184).
destruct Hfrx as (E & HE & HRG & HFL).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact HB | split; [exact HJ | exact HFR]]).
destruct (xx_geom cx ly3 S3 W mem3 md3 k HC) as
  (Hal16 & Hlo & Hhi & HF0 & HFc & HFia & HFo & HFal & HFpres & HSpres & HWpres & HAR3 & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (xx_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2). unfold MFRAME in HA1.
assert (RA : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
pose proof HB as (HPRE0 & _ & _).
pose proof HPRE0 as (HAPRE & Hra0 & _ & _ & _ & _ & _ & _ & HNEV & _).
pose proof HAPRE as (HAR0 & Hret0 & Hra4 & Hgp0 & Htp0 & _ & _ & _ & _).
pose proof HE as (EE & E32 & HEIb & E60v & E516v & E529v).
unfold AT_A, AT_F, AT_SH in E60v, E516v, E529v.
pose proof HX as (Hsp & Hgp & Htp & H8 & H9 & H19 & H27).
assert (Hhin : In (h, HUNT_SIZE) (ablocks B ly3 S3)).
{ destruct Hblk as (HP & _). eapply Permutation_in; [apply Permutation_sym; exact HP|]. cbn [app]. left. reflexivity. }
assert (Hnent : ~ In (h, HUNT_SIZE) (ablocks B (c_ly cx) (c_S cx))).
{ destruct Hblk as (_ & HFb & _). inversion HFb as [|? ? Hx _]. exact Hx. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ h HUNT_SIZE HAR3 Hhin) as (_ & Hh4096 & Hhce & Hhapp & _).
set (vals := x_vals regs h).
assert (EX : forall j, (j < 33)%nat -> ew (d_env cx E vals) (AT_X + j) = nth j vals (Z_to_bv 64 0)).
{ intros j Hj. apply xx_env_x. subst vals. unfold x_vals. rewrite length_app, length_map, length_seq. cbn. lia. }
assert (E563 : ew (d_env cx E vals) 563 = Z_to_bv 64 h) by (exact (EX 32%nat ltac:(lia))).
assert (Hrq : 480 <= req_size HUNT_SIZE) by (vm_compute; intros Hq; discriminate Hq).
assert (HAC : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_A cx))
  [YP09.mkChunk 184 (CVal 8 (SOff 563 0))]).
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ _ _ 8%N _ h);
    [apply xx_den0; exact E563 | cbn; unfold HUNT_SIZE in *; lia | cbn; lia | exact H184]. }
pose proof (xx_seat fq cx ly3 S3 W regs mem3 md3 k E EXIT_OFF vals
  [YP09.mkChunk 184 (CVal 8 (SOff 563 0))] (d_facts [] []) HC HE HRG HFL
  (xx_regs_ok cx E regs h HE HX RA)
  (FACTS LAWS cx ly3 S3 W mem3 md3 k E vals [] [] HC HE I I) HAC ltac:(vm_compute; reflexivity)) as HS.
pose proof (xx_E_env cx E vals HE) as HdEd.
pose proof HdEd as (_ & _ & HEI & _).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E vals) (rd W mem3)) by constructor.
pose (RUN := paj_run (fx := fq) B LAWS).
assert (E60 : bv_unsigned (ew (d_env cx E vals) 60%nat) = d_S cx + (d_A cx - d_S cx)).
{ rewrite xx_env_old by (unfold AT_FL; lia). rewrite E60v. unfold w64. rewrite unsigned_lit_small by exact RA. lia. }
assert (E60A : bv_unsigned (ew (d_env cx E vals) 60%nat) = d_A cx) by lia.
assert (E516A : bv_unsigned (ew (d_env cx E vals) 516%nat) = d_FB cx).
{ rewrite xx_env_old by (unfold AT_FL; lia). rewrite E516v. unfold w64. apply unsigned_lit_small. lia. }
assert (E529A : bv_unsigned (ew (d_env cx E vals) 529%nat) = shadow_addr (d_FB cx)).
{ rewrite xx_env_old by (unfold AT_FL; lia). rewrite E529v. unfold w64. apply unsigned_lit_small.
  unfold shadow_addr, SHADOW_OFF. lia. }
assert (USP2 : bv_unsigned (ew (d_env cx E vals) 2) = d_S cx)
  by (rewrite xx_env_old by (unfold AT_FL; lia); rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
unfold cfg_at. change (w64 (BASE + EXIT_OFF)) with (Z_to_bv 64 (BASE + EXIT_OFF)).
paj_run_tok RUN HS HJ SHOK Bspan.
{ cbn [ss_x ss_mem x_kregions].
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
assert (Hctx4 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md4 k)
  by (split; [exact HB | split; [exact HJ | exact HFR]]).
pose proof (proj1 HJ) as HAR4.
assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 19; 27]%bv -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms r HS).
  rewrite (xx_regs_ok cx E regs h HE HX RA r).
  cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [reflexivity|]). destruct Hr. }
assert (R10 : getr (ms_regs ms) 10 = w64 h).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 10%bv HS).
  match goal with |- context [sv_denot _ ?a] => let a' := eval vm_compute in a in change a with a' end.
  unfold w64. apply xx_den0. exact E563. }
assert (R1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + 9384)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 1%bv HS).
  match goal with |- context [sv_denot _ ?a] => let a' := eval vm_compute in a in change a with a' end.
  exact (codeptr_val _ 9384 HEI). }
assert (Hsp' : spZ (ms_regs ms) = d_S cx + (d_A cx - d_S cx)).
{ unfold spZ. rewrite (RG 2%bv ltac:(cbv; tauto)). unfold spZ in Hsp. lia. }
assert (Hs0' : s0Z (ms_regs ms) = d_S cx).
{ unfold s0Z. rewrite (RG 8%bv ltac:(cbv; tauto)). rewrite H8. unfold w64.
  apply unsigned_lit_small. unfold LLVMF_STK in *; lia. }
assert (R3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite (RG 3%bv ltac:(cbv; tauto)); exact Hgp).
assert (R4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite (RG 4%bv ltac:(cbv; tauto)); exact Htp).
pose proof pa_base_lo as HBLO. unfold YImgTop.IMG_LO in HBLO.
pose proof pa_B_ok as (HB0 & HB40 & _).
assert (Hraw : YK0s.ret_ok (Z_to_bv 64 (BASE + 9384))) by (apply ret_ok_codeptr_v; lia).
assert (Hraz : raZ (ms_regs ms) = BASE + 9384) by (unfold raZ; rewrite R1; apply unsigned_lit_small; lia).
assert (Hevx : st_nev S3 < EV_MAX) by (unfold EV_HEAD, EV_PRO, EV_ITER, EV_LIB, MAX_OPS in *; lia).
pose proof (st_ok_region_nth (d_env cx E vals) _ (restrict (w_H W) ms) 0 _ HS eq_refl) as HRS0.
cbn [ms_mem restrict] in HRS0.
assert (HRD8 : rdword (aview SEGS (w_H W) (ms_mem ms)) (d_S cx - 8) = Some RA_LLVMF).
{ apply rdword_of_val_mem; [|unfold RA_LLVMF; lia].
  replace (d_S cx - 8) with (d_S cx + (-8)) by lia.
  eapply (xx_slot _ _ 2%nat _ _ _ _ _ _ (-8) (SOff 1 0)); [exact HRS0 | exact USP2 | xx_in | | unfold RA_LLVMF; lia].
  apply xx_den0. rewrite xx_env_old by (unfold AT_FL; lia). rewrite (EE 1%nat 1%bv eq_refl). unfold raZ in Hra0.
  rewrite <- Hra0. symmetry. apply Z_to_bv_bv_unsigned. }
assert (HRD16 : rdword (aview SEGS (w_H W) (ms_mem ms)) (d_S cx - 16) = Some (s0Z (c_regs cx))).
{ pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr8. change (bv_modulus 64) with (2 ^ 64) in Hr8.
  apply rdword_of_val_mem; [|unfold s0Z; lia].
  replace (d_S cx - 16) with (d_S cx + (-16)) by lia.
  eapply (xx_slot _ _ 2%nat _ _ _ _ _ _ (-16) (SOff 8 0)); [exact HRS0 | exact USP2 | xx_in | | unfold s0Z; lia].
  apply xx_den0. rewrite xx_env_old by (unfold AT_FL; lia). rewrite (EE 8%nat 8%bv eq_refl). unfold s0Z.
  symmetry. apply Z_to_bv_bv_unsigned. }
assert (HU2 : In [pc_free_ra0 (as_code B); BASE + 9384] (as_universe B)) by (apply DUNIV; unfold d_sites; xx_in).
assert (HU3 : In [pc_free_ra0 (as_code B); BASE + 9384; RA_LLVMF] (as_universe B))
  by (apply DUNIV; unfold d_sites; xx_in).
destruct (xx_call_chain (pc_free_ra0 (as_code B)) 9384 cx ly3 S3 W (ms_mem ms) md4 k (ms_regs ms)
  (s0Z (c_regs cx)) Hctx4 (proj1 (pal_rt_below B TL)) ltac:(lia) ltac:(lia) HU2 HU3 ltac:(lia) Hs0'
  ltac:(unfold MFRAME in HA1; lia) Hraz
  HRD8 HRD16 (xx_chain_disj cx ly3 S3 W (ms_mem ms) md4 k Hctx4)) as (ch & Hch & Htr).
rewrite (pal_free B TL) in HS.
pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ ms HS eq_refl) as Hms. cbn [ss_pc setpc] in Hms.
rewrite Hms.
eapply SRr_bind; [exact (YCbq.aj_free_at (fx := fq) SEGS B LAWS pa_segs_low (pal_env B TL) ML (AFREE fq) W (ms_regs ms)
  (ms_mem ms) LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)]
  ly3 S3 md4 k h HUNT_SIZE (d_A cx - d_S cx) (Z_to_bv 64 (BASE + 9384)) ch HJ Hhin R10 Hsp'
  ltac:(clear - Hal16 HA2; lia) ltac:(clear - HA1; unfold MFRAME in HA1; lia)
  ltac:(clear - HA1; unfold LLVMF_STK, ASTACK, MFRAME in *; lia) R3 R4 R1 Hraw Hevx Hch Htr (fun Hc => False_ind _ (Hnent Hc)))|].
intros W2 c2 Hw2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & Hs1 & Hs2) & Hfr2 & HK).
assert (Hfrs2 : frames S2 = [(DFRAME_CLASS, c_fpos cx)]) by (rewrite Hfr2; exact HFR).
assert (Hctx2 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly2 S2 W2 mem2 md2 (k + 1))
  by (split; [exact HB | split; [exact HJ2 | exact Hfrs2]]).
destruct (xx_geom cx ly2 S2 W2 mem2 md2 (k + 1) Hctx2) as
  (_ & _ & _ & _ & _ & _ & _ & _ & HFpres2 & HSpres2 & HWpres2 & HAR2 & Hfin2 & Efa2 & Efl2).
assert (HnEF : forall a, d_FB cx <= a < d_FB cx + 4096 -> ~ (h <= a < h + req_size HUNT_SIZE)).
{ intros a Ha Hx.
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W (ms_mem ms) md4 h HUNT_SIZE DFRAME_CLASS (c_fpos cx) HAR4 Hhin Hfin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Efa in Hd.
  change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hd. lia. }
assert (HnES : forall a, shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512 -> ~ (h <= a < h + req_size HUNT_SIZE)).
{ intros a Ha Hx. unfold shadow_addr, SHADOW_OFF in Ha.
  exact (fshadow_not_app (d_FB cx) 512 h (req_size HUNT_SIZE) a HF0 ltac:(lia) Hhapp ltac:(lia) Hx). }
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (firstn 4 (ss_mem ssx)) in
  pose proof (st_ok_pi_after_call_hi (fx := fq) 600 Ex ssx msx regs2 (mrestrict (w_H W2) mem2) rs 9384 HEI ltac:(lia) HS eq_refl
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(submem_tac) eq_refl HP2) as HS2
end.
lazymatch type of HS2 with Forall ?P ?rs -> _ => assert (HKEPT : Forall P rs) end.
{ apply Forall_cons.
  { eapply region_kept_stack_aj; [exact HK | exact HJ2 | exact USP2 | lia | unfold LLVMF_STK; lia | lia | lia | lia]. }
  apply Forall_cons.
  { eapply region_kept_stack_aj; [exact HK | exact HJ2 | exact E60A | lia | unfold LLVMF_STK; lia | lia | lia | lia]. }
  apply Forall_cons.
  { eapply region_kept_ownframe_aj; [exact HK | exact E516A | exact Hfin
    | left; rewrite Efa; change (fs_frame_bytes DFRAME_CLASS) with 4096; lia
    | intros a Ha; apply HnEF; lia
    | intros a Ha; lia]. }
  apply Forall_cons.
  { eapply region_kept_ownframe_aj; [exact HK | exact E529A | exact Hfin
    | right; rewrite Efa; change (fs_frame_bytes DFRAME_CLASS / 8) with 512; lia
    | intros a Ha; apply HnES; lia
    | intros a Ha; lia]. }
  apply Forall_nil. }
specialize (HS2 HKEPT).
change (mkst regs2 (Z_to_bv 64 (BASE + 9384)) (rd W2 mem2) (seg_rom SEGS))
  with (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 9384)) mem2 (seg_rom SEGS))) in HS2.
norm_ss HS2.
set (E2 := havoc (d_env cx E vals) 600 (map (getr regs2) CLOB)) in HS2.
assert (HEI2 : img_env VAL A_LIM E2) by (apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]).
assert (EH : forall j : nat, (j < 600)%nat -> ew E2 j = ew (d_env cx E vals) j)
  by (intros j Hj; unfold E2; apply ew_havoc_old; exact Hj).
assert (E516B : bv_unsigned (ew E2 516%nat) = d_FB cx) by (rewrite EH by lia; exact E516A).
assert (E529B : bv_unsigned (ew E2 529%nat) = shadow_addr (d_FB cx)) by (rewrite EH by lia; exact E529A).
assert (E60B : bv_unsigned (ew E2 60%nat) = d_S cx + (d_A cx - d_S cx)) by (rewrite EH by lia; exact E60).
assert (USP2B : bv_unsigned (ew E2 2%nat) = d_S cx) by (rewrite EH by lia; exact USP2).
assert (EFLB : ew E2 AT_FL = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)))
  by (rewrite EH by (unfold AT_FL; lia); apply xx_env_fl).
pose proof (SRr_run_to_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNTO.
assert (HWRF : forall o, 0 <= o < 3072 -> writable_at SEGS (rd W2 mem2) (d_FB cx + o))
  by (intros o Ho; apply (apresent_writable SEGS); apply HFpres2; lia).
assert (HWRS : forall o, 0 <= o < 384 -> writable_at SEGS (rd W2 mem2) (shadow_addr (d_FB cx) + o))
  by (intros o Ho; apply (apresent_writable SEGS); apply HSpres2; lia).
lazymatch type of HS2 with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let r := eval vm_compute in (nth 2 (ss_mem ssx) got_regionP) in
  pose proof (ast_ok_pi_set_region Ex ssx msx 2 r (set_window r 0 3072) HS2 ltac:(vm_compute; reflexivity) eq_refl
    ltac:(vm_compute; reflexivity)
    (region_ok_rewindow _ Ex _ r 0 3072 (st_ok_pi_region_nth Ex ssx msx 2 r HS2 ltac:(vm_compute; reflexivity))
      ltac:(intros o Ho; cbn [YP09.r_base base_val ms_mem restrict mkst]; rewrite E516B; exact (HWRF o Ho)))) as HSa
end.
clear HS2. norm_ss HSa.
lazymatch type of HSa with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
  pose proof (ast_ok_pi_set_region Ex ssx msx 3 r (set_window r 0 384) HSa ltac:(vm_compute; reflexivity) eq_refl
    ltac:(vm_compute; reflexivity)
    (region_ok_rewindow _ Ex _ r 0 384 (st_ok_pi_region_nth Ex ssx msx 3 r HSa ltac:(vm_compute; reflexivity))
      ltac:(intros o Ho; cbn [YP09.r_base base_val ms_mem restrict mkst]; rewrite E529B; exact (HWRS o Ho)))) as HSb
end.
clear HSa. norm_ss HSb.
paj_run_to_sh RUNTO HSb HJ2 9768.
{ cbn [ss_mem].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 516%nat (d_FB cx)); [reflexivity | exact E516B | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right; right; right. exists DFRAME_CLASS, (c_fpos cx).
    split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite Efa2.
    change (fs_frame_bytes DFRAME_CLASS) with 4096. lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 529%nat (shadow_addr (d_FB cx))); [reflexivity | exact E529B | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right; right; right. exists DFRAME_CLASS, (c_fpos cx).
    split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite Efa2.
    change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia. }
  apply awr_ok_nil. }
set (md5 := with_vm_backing (m_vm_lazy md2) mat0 md2) in *.
lazymatch type of HSb with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let r := eval vm_compute in (nth 2 (ss_mem ssx) got_regionP) in
  pose proof (ast_ok_pi_set_region Ex ssx msx 2 r (set_window r 0 0) HSb ltac:(vm_compute; reflexivity) eq_refl
    ltac:(vm_compute; reflexivity)
    (region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx 2 r HSb ltac:(vm_compute; reflexivity))
      ltac:(intros o Ho; lia))) as HSc
end.
clear HSb. norm_ss HSc.
lazymatch type of HSc with st_ok_pi _ _ ?Ex ?ssx ?msx =>
  let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
  pose proof (ast_ok_pi_set_region Ex ssx msx 3 r (set_window r 0 0) HSc ltac:(vm_compute; reflexivity) eq_refl
    ltac:(vm_compute; reflexivity)
    (region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx 3 r HSc ltac:(vm_compute; reflexivity))
      ltac:(intros o Ho; lia))) as HS2
end.
clear HSc. norm_ss HS2.
assert (SHOK2 : sh_ok SEGS (SOff 32 0) [] E2 (rd W2 (ms_mem ms0))) by constructor.
paj_run_tok RUN HS2 HJ2 SHOK2 Bspan.
{ cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
set (md6 := with_vm_backing (m_vm_lazy md5) mat1 md5) in *.
assert (Hctx5 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly2 S2 W2 (ms_mem ms1) md6 (k + 1))
  by (split; [exact HB | split; [exact HJ2 | exact Hfrs2]]).
pose proof (st_ok_region_nth E2 _ (restrict (w_H W2) ms1) 2 _ HS2 eq_refl) as HRF.
cbn [ms_mem restrict] in HRF.
assert (HFLB : rdword (aview SEGS (w_H W2) (ms_mem ms1)) (d_FB cx + fs_frame_bytes DFRAME_CLASS - 8) =
  Some (flag_addr ly2 DFRAME_CLASS (c_fpos cx))).
{ rewrite Efl2. change (fs_frame_bytes DFRAME_CLASS) with 4096.
  apply rdword_of_val_mem; [|exact (xx_rdword_range _ _ _ _ _ HFL)].
  replace (d_FB cx + 4096 - 8) with (d_FB cx + 4088) by lia.
  eapply (xx_slot _ _ 516%nat _ _ _ _ _ _ 4088 (SOff AT_FL 0)); [exact HRF | exact E516B | xx_in | |
    exact (xx_rdword_range _ _ _ _ _ HFL)].
  apply xx_den0. exact EFLB. }
assert (R2B : getr (ms_regs ms1) 2 = getr regs 2).
{ rewrite (st_ok_restrict_reg SEGS (w_H W2) _ _ ms1 2%bv HS2).
  match goal with |- context [sv_denot _ ?a] => let a' := eval vm_compute in a in change a with a' end.
  cbn [sv_denot]. rewrite EH by lia. rewrite xx_env_old by (unfold AT_FL; lia). rewrite Z.add_0_r.
  rewrite E60v. unfold w64. rewrite Z_to_bv_bv_unsigned. unfold spZ in Hsp. rewrite <- Hsp.
  rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (R3B : getr (ms_regs ms1) 3 = w64 (as_gp B)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W2) _ _ ms1 3%bv HS2).
  match goal with |- context [sv_denot _ ?a] => let a' := eval vm_compute in a in change a with a' end.
  cbn [sv_denot]. rewrite EH by lia.
  replace 534%nat with (AT_X + 3)%nat by (unfold AT_X; lia).
  rewrite (EX 3%nat ltac:(lia)). subst vals. unfold x_vals. cbn [nth map seq app].
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hgp. }
assert (R4B : getr (ms_regs ms1) 4 = w64 (as_tp B)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W2) _ _ ms1 4%bv HS2).
  match goal with |- context [sv_denot _ ?a] => let a' := eval vm_compute in a in change a with a' end.
  cbn [sv_denot]. rewrite EH by lia.
  replace 535%nat with (AT_X + 4)%nat by (unfold AT_X; lia).
  rewrite (EX 4%nat ltac:(lia)). subst vals. unfold x_vals. cbn [nth map seq app].
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Htp. }
assert (R10B : getr (ms_regs ms1) 10 = w64 (frame_addr ly2 DFRAME_CLASS (c_fpos cx))).
{ rewrite (st_ok_restrict_reg SEGS (w_H W2) _ _ ms1 10%bv HS2).
  match goal with |- context [sv_denot _ ?a] => let a' := eval vm_compute in a in change a with a' end.
  rewrite Efa2. unfold w64. apply xx_den0. rewrite EH by lia.
  rewrite xx_env_old by (unfold AT_FL; lia). rewrite E516v. unfold w64. reflexivity. }
assert (R11B : getr (ms_regs ms1) 11 = w64 3072).
{ rewrite (st_ok_restrict_reg SEGS (w_H W2) _ _ ms1 11%bv HS2).
  match goal with |- context [sv_denot _ ?a] => let a' := eval vm_compute in a in change a with a' end.
  reflexivity. }
assert (R1B : getr (ms_regs ms1) 1 = Z_to_bv 64 (BASE + 9772)).
{ rewrite (st_ok_restrict_reg SEGS (w_H W2) _ _ ms1 1%bv HS2).
  match goal with |- context [sv_denot _ ?a] => let a' := eval vm_compute in a in change a with a' end.
  exact (codeptr_val _ 9772 HEI2). }
assert (HrawB : YK0s.ret_ok (Z_to_bv 64 (BASE + 9772))) by (apply ret_ok_codeptr_v; lia).
assert (HspB : spZ (ms_regs ms1) = d_S cx + (d_A cx - d_S cx)).
{ unfold spZ. rewrite R2B. unfold spZ in Hsp. lia. }
rewrite HSF6 in HS2.
pose proof (st_ok_restrict_mkst SEGS (w_H W2) _ _ ms1 HS2 eq_refl) as Hms0. cbn [ss_pc setpc] in Hms0.
rewrite Hms0.
eapply SRr_bind; [exact (aj_stack_free_at (fx := fq) SEGS B LAWS pa_segs_low ML SF6_ENTRY DFRAME_CLASS (ASFW6 fq)
  ltac:(unfold DFRAME_CLASS; lia) W2 (ms_regs ms1) (ms_mem ms1) LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
  [] ly2 S2 md6 (k + 1) (c_fpos cx) 3072 (d_A cx - d_S cx) (Z_to_bv 64 (BASE + 9772))
  HJ2 R10B R11B
  ltac:(change (fs_frame_bytes DFRAME_CLASS) with 4096; lia) ltac:(reflexivity)
  ltac:(rewrite Efa2; exact HFLB) HspB
  ltac:(clear - Hal16 HA2; lia) ltac:(clear - HA1; unfold MFRAME in HA1; lia)
  ltac:(clear - HA1; unfold LLVMF_STK, ESTACK, MFRAME in *; lia) R3B R4B R1B HrawB)|].
intros W3 c3 Hw3 (-> & regs3 & mem3b & md3b & -> & HJ3 & HP3 & Heff5 & Heff & Hpres3).
assert (HKEPT2 : Forall (region_kept SEGS E2 (ms_mem (restrict (w_H W2) ms1)) (mrestrict (w_H W2) mem3b))
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks]).
{ apply Forall_cons; [|apply Forall_nil]. split;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; unfold AT_STK;
  rewrite USP2B; intros a Ha; [|lia].
  cbn [ms_mem restrict]. apply (mbyte_of_aview SEGS). apply Heff.
  - clear - Ha Hlo Hhi HA1 C1; unfold LLVMF_STK in *; lia.
  - rewrite Efa2. change (sf_span DFRAME_CLASS 3072) with 512.
    clear - Ha Hlo HA1 HFc HF0 C1; unfold shadow_addr, SHADOW_OFF, LLVMF_STK in *; lia.
  - intros ->.
    destruct (al_flag _ _ LAWS ly2 S2 W2 (ms_mem ms1) md6 DFRAME_CLASS (c_fpos cx)
      (proj1 (proj1 (proj2 Hctx5))) Hfin2) as (_ & _ & _ & Hfl4).
    clear - Ha Hfl4 Hlo HA1; unfold LLVMF_STK in *; lia.
  - clear - Ha HA1; unfold ESTACK, MFRAME in *; lia. }
lazymatch type of HS2 with st_ok _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (firstn 1 (ss_mem ssx)) in
  pose proof (st_ok_pi_after_call_hi (fx := fq) 640 Ex ssx msx regs3 (mrestrict (w_H W2) mem3b) rs 9772 HEI2 ltac:(clear - C1; lia) HS2 eq_refl
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(submem_tac) eq_refl HP3 HKEPT2) as HS3
end.
change (mkst regs3 (Z_to_bv 64 (BASE + 9772)) (rd W2 mem3b) (seg_rom SEGS))
  with (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 (BASE + 9772)) mem3b (seg_rom SEGS))) in HS3.
norm_ss HS3.
set (E3 := havoc E2 640 (map (getr regs3) CLOB)) in HS3.
assert (HEI3 : img_env VAL A_LIM E3) by (apply img_env_havoc_hi; [exact HEI2 | unfold A_LIM; xx_nle]).
assert (EH3 : forall j : nat, (j < 640)%nat -> ew E3 j = ew E2 j)
  by (intros j Hj; unfold E3; apply ew_havoc_old; exact Hj).
paj_run_to_sh RUNTO HS3 HJ3 9852.
{ cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; apply Z.le_refl|]. apply awr_ok_nil. }
eapply (paj_ret_at (fx := fq) (PL := PL_both3_0) (PI := PI) W2 E3 _ ms2 _ _ HS3 eq_refl); [vm_compute; reflexivity|].
intros mat9.
assert (RF : forall r : bv 5, In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms2) r = getr (c_regs cx) r).
{ intros r Hr. rewrite (st_ok_pi_restrict_reg (w_H W2) _ _ ms2 r HS3).
  cbv [In] in Hr.
  repeat (destruct Hr as [<-|Hr];
    [ match goal with |- context [sv_denot _ ?a] => let a' := eval vm_compute in a in change a with a' end;
      cbn [sv_denot]; rewrite EH3 by xx_nlt; rewrite EH by xx_nlt; rewrite xx_env_old by (unfold AT_FL; xx_nlt);
      rewrite Z.add_0_r;
      first [ rewrite (EE 2%nat 2%bv eq_refl) | rewrite (EE 8%nat 8%bv eq_refl) | rewrite (EE 9%nat 9%bv eq_refl)
            | rewrite (EE 18%nat 18%bv eq_refl) | rewrite (EE 19%nat 19%bv eq_refl) | rewrite (EE 20%nat 20%bv eq_refl)
            | rewrite (EE 21%nat 21%bv eq_refl) | rewrite (EE 22%nat 22%bv eq_refl) | rewrite (EE 23%nat 23%bv eq_refl)
            | rewrite (EE 24%nat 24%bv eq_refl) | rewrite (EE 25%nat 25%bv eq_refl) | rewrite (EE 26%nat 26%bv eq_refl)
            | rewrite (EE 27%nat 27%bv eq_refl) ];
      rewrite Z_to_bv_bv_unsigned; reflexivity |]).
  destruct Hr. }
assert (R1F : getr (ms_regs ms2) 1 = getr (c_regs cx) 1).
{ rewrite (st_ok_pi_restrict_reg (w_H W2) _ _ ms2 1%bv HS3).
  match goal with |- context [sv_denot _ ?a] => let a' := eval vm_compute in a in change a with a' end.
  cbn [sv_denot]. rewrite EH3 by xx_nlt. rewrite EH by xx_nlt. rewrite xx_env_old by (unfold AT_FL; xx_nlt).
  rewrite Z.add_0_r. rewrite (EE 1%nat 1%bv eq_refl). rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (R10F : getr (ms_regs ms2) 10 = w64 0).
{ rewrite (st_ok_pi_restrict_reg (w_H W2) _ _ ms2 10%bv HS3).
  match goal with |- context [sv_denot _ ?a] => let a' := eval vm_compute in a in change a with a' end.
  reflexivity. }
assert (R34F : getr (ms_regs ms2) 3 = getr (c_regs cx) 3 /\ getr (ms_regs ms2) 4 = getr (c_regs cx) 4).
{ split.
  - rewrite (st_ok_pi_restrict_reg (w_H W2) _ _ ms2 3%bv HS3).
    match goal with |- context [sv_denot _ ?a] => let a' := eval vm_compute in a in change a with a' end.
    cbn [sv_denot]. rewrite EH3 by xx_nlt. rewrite EH by xx_nlt.
    replace 534%nat with (AT_X + 3)%nat by reflexivity.
    rewrite (EX 3%nat ltac:(xx_nlt)). subst vals. unfold x_vals. cbn [nth map seq app].
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. transitivity (w64 (as_gp B)); [exact Hgp | symmetry; exact Hgp0].
  - rewrite (st_ok_pi_restrict_reg (w_H W2) _ _ ms2 4%bv HS3).
    match goal with |- context [sv_denot _ ?a] => let a' := eval vm_compute in a in change a with a' end.
    cbn [sv_denot]. rewrite EH3 by xx_nlt. rewrite EH by xx_nlt.
    replace 535%nat with (AT_X + 4)%nat by reflexivity.
    rewrite (EX 4%nat ltac:(xx_nlt)). subst vals. unfold x_vals. cbn [nth map seq app].
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. transitivity (w64 (as_tp B)); [exact Htp | symmetry; exact Htp0]. }
assert (HPRES : aregs_preserved (c_regs cx) (ms_regs ms2)).
{ intros r Hr. unfold acallee_saved in Hr.
  destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
  - exact (RF 2%bv ltac:(cbv; tauto)).
  - exact (proj1 R34F).
  - exact (proj2 R34F).
  - exact (RF 8%bv ltac:(cbv; tauto)).
  - exact (RF 9%bv ltac:(cbv; tauto)).
  - assert (Hcase : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
      by (clear - Hr; lia).
    destruct Hcase as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
    [ exact (RF 18%bv ltac:(cbv; tauto)) | exact (RF 19%bv ltac:(cbv; tauto)) | exact (RF 20%bv ltac:(cbv; tauto))
    | exact (RF 21%bv ltac:(cbv; tauto)) | exact (RF 22%bv ltac:(cbv; tauto)) | exact (RF 23%bv ltac:(cbv; tauto))
    | exact (RF 24%bv ltac:(cbv; tauto)) | exact (RF 25%bv ltac:(cbv; tauto)) | exact (RF 26%bv ltac:(cbv; tauto))
    | exact (RF 27%bv ltac:(cbv; tauto)) ]. }
assert (HPERM : Permutation (ablocks B ly2 S2) (ablocks B (c_ly cx) (c_S cx))).
{ destruct Hblk as (HP & _). cbn [app] in HP.
  apply (Permutation_cons_inv (l := ablocks B ly2 S2) (l' := ablocks B (c_ly cx) (c_S cx)) (a := (h, HUNT_SIZE))).
  rewrite Hs2. eapply Permutation_trans; [apply Permutation_middle | rewrite <- Hs1; exact HP]. }
assert (HPC : v_jalr (getr (ms_regs ms2) 1) 0 = getr (c_regs cx) 1).
{ rewrite R1F. unfold raZ in Hra0.
  assert (E1 : getr (c_regs cx) 1 = Z_to_bv 64 RA_LLVMF) by (rewrite <- Hra0; symmetry; apply Z_to_bv_bv_unsigned).
  rewrite E1. exact (v_jalr_lit_even RA_LLVMF xx_ra_rng eq_refl). }
rewrite HPC.
eapply (exit_post_closed B MT MT_TRIV XM_LIB XN_LIB RLO RHI tfib_K AIL [] inFP_nil
  fq cx ly2 (stack_free_state DFRAME_CLASS (c_fpos cx) S2) W2 (ms_regs ms2) (ms_mem ms2) _ (k + 1) Hfrm0 HB).
- eapply (ajournal_materialize SEGS B); first [exact HJ3 | exact LAWS | exact pa_segs_low].
- clear - Hk; unfold EV_HEAD, EV_PRO, EV_ITER, EV_LIB, MAX_OPS in *; lia.
- unfold ablocks; rewrite blocks_stack_free_state; exact HPERM.
- exact HPRES.
- exact R10F.
Qed.
End h.
End f.
End d.
