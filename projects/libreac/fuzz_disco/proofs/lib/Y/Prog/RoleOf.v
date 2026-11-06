(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YC1i.v, with its module paths, module names and numbers changed; 643 of its 708 lines of code are new or changed and 637 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/FindEntry.v, with its module paths and module names changed; 250 of its 410 lines of code are new or changed and 548 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0s YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC8i YC1f YC1h YC88 YK0w YC85.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YL05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import FindEntry.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma ro_le_byte_bytes : forall (bs : list byte) j, (j < length bs)%nat ->
  YO0f.le_byte (bytes_le_to_Z bs) (length bs) j = bv_unsigned (nth j bs (Z_to_bv 8 0)).
Proof.
intros bs j Hj. unfold YO0f.le_byte.
pose proof (YK11.bytes_le_to_Z_bound bs) as Hb. pose proof (YK11.bytes_le_to_Z_nonneg bs) as Hn.
rewrite (Z.mod_small (bytes_le_to_Z bs) (2 ^ (8 * Z.of_nat (length bs)))) by (split; [exact Hn | exact Hb]).
rewrite Z.shiftr_div_pow2 by lia.
rewrite <- (zb_of_bytes bs j Hj). reflexivity.
Qed.
Lemma ro_u_at_range : forall T k, 0 <= u_at T k 4 < 2 ^ 32.
Proof.
intros T k. unfold u_at. pose proof (bytes_le_to_Z_bound (sub T k 4)) as Hb. pose proof (bytes_le_to_Z_nonneg (sub T k 4)) as Hn.
assert (Hl : (length (sub T k 4) <= 4)%nat) by (unfold sub; rewrite length_firstn; lia).
assert (2 ^ (8 * Z.of_nat (length (sub T k 4))) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia). lia.
Qed.
Lemma ro_role_u : forall T k o, o = 48 * k + 8 -> 0 <= k < n_of T -> tbl_T2 T ->
  u_at T o 4 = role_of_e T k /\ (role_of_e T k = 0 \/ role_of_e T k = 1 \/ role_of_e T k = 2).
Proof.
intros T k o -> Hk T2. pose proof (T2 k Hk) as Hr. split; [|exact Hr].
pose proof (ro_u_at_range T (48 * k + 8)) as R. unfold role_of_e, s32_at in *.
set (u := u_at T (48 * k + 8) 4) in *. unfold bv_swrap, bv_wrap in *.
change (bv_half_modulus 32) with (2 ^ 31) in *. change (bv_modulus 32) with (2 ^ 32) in *.
destruct (Z_lt_ge_dec u (2 ^ 31)).
- rewrite (Z.mod_small (u + 2 ^ 31)) in * by lia. lia.
- replace (u + 2 ^ 31) with ((u - 2 ^ 31) + 1 * 2 ^ 32) in Hr by lia.
  rewrite Z.mod_add, Z.mod_small in Hr by lia. lia.
Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Lemma ro_val_mem4_garr8 : forall (m : word -> option byte) b (L : list byte) k,
  garr8 SEGS m b (map bv_unsigned L) -> 0 <= k -> k + 4 <= Z.of_nat (length L) ->
  val_mem SEGS m (b + k) 4 (u_at L k 4).
Proof.
intros m b L k HG Hk Hkl j Hj. unfold u_at, sub.
set (bs := firstn 4 (skipn (Z.to_nat k) L)).
assert (Hlen : length bs = 4%nat) by (subst bs; rewrite length_firstn, length_skipn; lia).
replace (YO0f.le_byte (bytes_le_to_Z bs) 4 j) with (YO0f.le_byte (bytes_le_to_Z bs) (length bs) j) by (rewrite Hlen; reflexivity).
rewrite ro_le_byte_bytes by lia.
assert (Hn : nth j bs (Z_to_bv 8 0) = nth (Z.to_nat k + j) L (Z_to_bv 8 0)).
{ subst bs. rewrite nth_firstn. replace (j <? 4)%nat with true by (symmetry; apply Nat.ltb_lt; lia). rewrite nth_skipn. reflexivity. }
rewrite Hn.
assert (Hj2 : (Z.to_nat k + j < length (map bv_unsigned L))%nat) by (rewrite length_map; lia).
destruct (HG _ Hj2) as [Hv Hr]. specialize (Hv 0%nat ltac:(lia)).
replace (b + k + Z.of_nat j) with (b + Z.of_nat (Z.to_nat k + j) + Z.of_nat 0) by lia.
rewrite Hv. do 2 f_equal.
rewrite (nth_indep (map bv_unsigned L) 0 (bv_unsigned (Z_to_bv 8 0)) Hj2). rewrite map_nth.
apply le_byte_1_0. pose proof (bv_unsigned_in_range _ (nth (Z.to_nat k + j) L (Z_to_bv 8 0))) as R. change (bv_modulus 8) with 256 in R. lia.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TFIND : tfind_entry_spec B.
Definition TROLE_OF_STK : Z := 32 + TFIND_ENTRY_STK.
Definition trole_of_post (fq : YK11.FPState) (regs : bvmap 5 word) ly S (W : world SEGS) mem md (T P : list byte)
  : world SEGS -> config -> Prop :=
  apost_base (fx := fq) SEGS B TROLE_OF_STK [] regs ly S W mem md 0
    (fun ly' S' _ regs' _ _ => Permutation (ablocks B ly' S') (ablocks B ly S) /\ exists r v,
       find_res T P r /\ v = (if r <? 0 then -1 else role_of_e T r) /\
       getr regs' 10 = Z_to_bv 64 v /\ (v = -1 \/ v = 0 \/ v = 1 \/ v = 2)).
Definition trole_of_spec : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (t p : Z) (T P : list byte),
  afn_pre SEGS B TROLE_OF_STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  getr regs 10 = w64 t -> getr regs 11 = w64 p ->
  0 < t -> t mod 8 = 0 -> t + 400 <= 2 ^ 63 -> 0 < p -> p + 6 <= 2 ^ 63 ->
  length T = 400%nat -> garr8 SEGS (mrestrict (w_H W) mem) t (map bv_unsigned T) ->
  length P = 6%nat -> garr8 SEGS (mrestrict (w_H W) mem) p (map bv_unsigned P) ->
  amem_range t 400 -> amem_range p 6 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF t 400 ->
  shadow_hull_vis (aview SEGS (w_H W) mem) t 400 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p 6 ->
  shadow_hull_vis (aview SEGS (w_H W) mem) p 6 ->
  (t + 400 <= spZ regs - TROLE_OF_STK \/ spZ regs <= t) ->
  (p + 6 <= spZ regs - TROLE_OF_STK \/ spZ regs <= p) ->
  off_img t 400 ->
  tbl_T1 T -> tbl_T2 T ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_role_of) regs mem md) (trole_of_post fq regs ly S W mem md T P).
Section w. Context {fx : YK11.FPState}.
Definition RSB : Z := 0x7fff8000.
Definition RBx : sv := SOff 32 0.
Definition Rspan : Z * Z := (RSB, RSB + 2 ^ 44 - 1).
Definition ro_chunks : list YP09.chunk :=
  [ YP09.mkChunk 8 (CVal 4 (SOff 33 0)); YP09.mkChunk 56 (CVal 4 (SOff 34 0)); YP09.mkChunk 104 (CVal 4 (SOff 35 0));
    YP09.mkChunk 152 (CVal 4 (SOff 36 0)); YP09.mkChunk 200 (CVal 4 (SOff 37 0)); YP09.mkChunk 248 (CVal 4 (SOff 38 0));
    YP09.mkChunk 296 (CVal 4 (SOff 39 0)); YP09.mkChunk 344 (CVal 4 (SOff 40 0)) ].
Definition ro_regions : smem :=
  [ stack_region 32; got_regionP; bcell_regionP 32; YP09.mkRegion (Some 10%nat) 0 400 0 0 ro_chunks ].
Definition ro_facts : facts :=
  mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 1 (2^47 - 401) 3); (32%nat, mkAF RSB RSB 0);
    (33%nat, mkAF 0 (2^32 - 1) 0); (34%nat, mkAF 0 (2^32 - 1) 0); (35%nat, mkAF 0 (2^32 - 1) 0); (36%nat, mkAF 0 (2^32 - 1) 0);
    (37%nat, mkAF 0 (2^32 - 1) 0); (38%nat, mkAF 0 (2^32 - 1) 0); (39%nat, mkAF 0 (2^32 - 1) 0); (40%nat, mkAF 0 (2^32 - 1) 0) ] [] [].
Definition ss_ro : sstate := mkSS AF_both3_role_of sr_atoms ro_regions None ro_facts.
Definition ro_SH : list shent := [ mkSHE 10 0 400 ].
Definition ro_extra (T : list byte) : list word :=
  map (Z_to_bv 64) [RSB; u_at T 8 4; u_at T 56 4; u_at T 104 4; u_at T 152 4; u_at T 200 4; u_at T 248 4; u_at T 296 4; u_at T 344 4].
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN (fq : YK11.FPState) := paj_run (fx := fq) B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR (fq : YK11.FPState) := paj_branch (fx := fq) (PI := PI).
Let RET (fq : YK11.FPState) := paj_ret_at (fx := fq) (PL := PL_both3_0) (PI := PI).
Ltac ro_env E regs T EL :=
  assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl));
  assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl));
  assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl));
  assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl));
  assert (E8 : ew E 8 = getr regs 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl));
  assert (E32 : ew E 32 = Z_to_bv 64 RSB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0));
  assert (E33 : ew E 33 = Z_to_bv 64 (u_at T 8 4)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1));
  assert (E34 : ew E 34 = Z_to_bv 64 (u_at T 56 4)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2));
  assert (E35 : ew E 35 = Z_to_bv 64 (u_at T 104 4)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3));
  assert (E36 : ew E 36 = Z_to_bv 64 (u_at T 152 4)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4));
  assert (E37 : ew E 37 = Z_to_bv 64 (u_at T 200 4)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5));
  assert (E38 : ew E 38 = Z_to_bv 64 (u_at T 248 4)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6));
  assert (E39 : ew E 39 = Z_to_bv 64 (u_at T 296 4)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 7));
  assert (E40 : ew E 40 = Z_to_bv 64 (u_at T 344 4)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 8)).
Lemma ro_entry : forall ly S W (regs : bvmap 5 word) mem md ch (t : Z) (T : list byte),
  afn_pre SEGS B TROLE_OF_STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
  getr regs 10 = w64 t ->
  0 < t -> t mod 8 = 0 -> t + 400 <= 2 ^ 63 ->
  length T = 400%nat -> garr8 SEGS (mrestrict (w_H W) mem) t (map bv_unsigned T) ->
  amem_range t 400 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF t 400 ->
  (t + 400 <= spZ regs - TROLE_OF_STK \/ spZ regs <= t) ->
  off_img t 400 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (ro_extra T))) ss_ro
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_both3_role_of)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS RBx ro_SH (Eimg (Ereg regs (ro_extra T))) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch t T HPRE H10 Ht0 Ht8 Ht63 LT GT MRt RAt OWt OIt.
assert (Esp : spZ (regupd regs 8 (Z_to_bv 64 0)) = spZ regs) by (unfold spZ; rewrite getr_other by reg_neq_tac; reflexivity).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
rewrite Esp in Hstk, Hpres.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : TROLE_OF_STK = 8304) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HcellR, HgotR. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in OIt.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (ro_extra T))).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (ro_extra T)) k)
by (intros k Hk; subst E; apply Eimg_low; exact Hk).
ro_env E regs T EL.
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
{ intros k v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
pose proof (ro_u_at_range T 8) as R33. pose proof (ro_u_at_range T 56) as R34. pose proof (ro_u_at_range T 104) as R35.
pose proof (ro_u_at_range T 152) as R36. pose proof (ro_u_at_range T 200) as R37. pose proof (ro_u_at_range T 248) as R38.
pose proof (ro_u_at_range T 296) as R39. pose proof (ro_u_at_range T 344) as R40.
split.
- unfold ss_ro. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold ro_regions, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 RBx RSB);
      [cbn [sv_denot RBx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold RSB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB 10%nat t E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      unfold ro_chunks. repeat apply Forall_cons; try apply Forall_nil;
      (eapply (chunk_ok_val SEGS E _ t _ 4);
       [cbn [sv_denot]; first [rewrite E33 | rewrite E34 | rewrite E35 | rewrite E36 | rewrite E37 | rewrite E38 | rewrite E39 | rewrite E40];
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
       | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | lia
       | change (N.to_nat 4) with 4%nat; apply ro_val_mem4_garr8; [exact GT | lia | rewrite LT; lia]]).
  + apply pairwise_disjoint_of_extents. unfold ro_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat t E10) by lia.
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1 WS Hstk0 HcellR HgcD HgotR OWt OIt Ht0 Ht63. clear. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP. intros.
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [ro_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E32, E33, E34, E35, E36, E37, E38, E39, E40, !unsigned_lit_small by (unfold RSB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil C1 WS Hstk0 Hal16 Ht0 Ht8 Ht63 MRt R33 R34 R35 R36 R37 R38 R39 R40. clear. unfold RSB, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. intros.
    repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, ro_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E RBx 10 t 400 t 0 400 RAt).
  + unfold U, RBx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold RSB; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + revert MRt. clear. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF. intros. lia.
Qed.
Theorem ro_walk : forall ly S W (regs : bvmap 5 word) mem md ch (t p : Z) (T P : list byte),
  afn_pre SEGS B TROLE_OF_STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  getr regs 10 = w64 t -> getr regs 11 = w64 p ->
  0 < t -> t mod 8 = 0 -> t + 400 <= 2 ^ 63 -> 0 < p -> p + 6 <= 2 ^ 63 ->
  length T = 400%nat -> garr8 SEGS (mrestrict (w_H W) mem) t (map bv_unsigned T) ->
  length P = 6%nat -> garr8 SEGS (mrestrict (w_H W) mem) p (map bv_unsigned P) ->
  amem_range t 400 -> amem_range p 6 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF t 400 ->
  shadow_hull_vis (aview SEGS (w_H W) mem) t 400 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p 6 ->
  shadow_hull_vis (aview SEGS (w_H W) mem) p 6 ->
  (t + 400 <= spZ regs - TROLE_OF_STK \/ spZ regs <= t) ->
  (p + 6 <= spZ regs - TROLE_OF_STK \/ spZ regs <= p) ->
  off_img t 400 ->
  tbl_T1 T -> tbl_T2 T ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_both3_role_of) regs mem md) (trole_of_post fx regs ly S W mem md T P).
Proof.
intros ly S W regs mem md ch t p T P HPRE HRO H10 H11 Ht0 Ht8 Ht63 Hp0 Hp63 LT GT LP GP MRt MRp RAt SHt RAp SHp OWt OWp OIt T1 T2.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (ro_entry ly S W regs mem md ch t T HPRE H10 Ht0 Ht8 Ht63 LT GT MRt RAt OWt OIt) as [HS SHOK].
assert (Esp : spZ (regupd regs 8 (Z_to_bv 64 0)) = spZ regs) by (unfold spZ; rewrite getr_other by reg_neq_tac; reflexivity).
pose proof (ajournal_init SEGS B TROLE_OF_STK [] ly S W _ mem md ch HPRE) as HJ. rewrite Esp in HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
unfold raZ in Hra4. rewrite getr_other in Hra, Hra4, Hgp, Htp by reg_neq_tac. fold (raZ regs) in Hra4.
rewrite Esp in Hstk, Hpres.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : TROLE_OF_STK = 8304) by reflexivity. assert (WF : TFIND_ENTRY_STK = 8272) by reflexivity.
remember (Eimg (Ereg regs (ro_extra T))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (ro_extra T)) k)
by (intros k Hk; subst E; apply Eimg_low; exact Hk).
ro_env E regs T EL.
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (ro_extra T)) E) by (split; [intros k Hk; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear HE EL.
unfold cfg_at. change (w64 (BASE + AF_both3_role_of)) with (Z_to_bv 64 (BASE + AF_both3_role_of)).
paj_run_tok (RUN fx) HS HJ SHOK Rspan.
{ awr_ok_tac; exact Usp. }
pose proof (proj1 HJ) as HAR1.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
assert (Ra : spZ (ms_regs ms) = spZ regs - 32) by (unfold spZ at 1; rewrite R2, Usp, unsigned_lit_small by lia; lia).
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hn. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia.
  intros (rg & Hin & Hr). unfold ss_ro, ro_regions in Hin. cbn [ss_mem In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi stack_region got_regionP bcell_regionP base_val] in Hr;
  [rewrite Usp in Hr; lia | lia | lia | lia]. }
assert (Hk47 : kHighShadowEnd <= spZ regs - TROLE_OF_STK) by lia.
pose proof MRt as MRt'. pose proof MRp as MRp'. unfold amem_range in MRt', MRp'. rewrite C4, C5, C3 in MRt', MRp'.
pmkst HS. rewrite pa_sigma_find_entry.
pose proof (afn_pre_at SEGS B TROLE_OF_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem ms) _ 0
  (regupd (ms_regs ms) 8 (Z_to_bv 64 0)) TFIND_ENTRY_STK (-32) [] HJ) as HPRE1.
assert (EspC : spZ (regupd (ms_regs ms) 8 (Z_to_bv 64 0)) = spZ (ms_regs ms)) by (unfold spZ; rewrite getr_other by reg_neq_tac; reflexivity).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. unfold YImgTop.IMG_LO in HBLO.
specialize (HPRE1 ltac:(rewrite EspC, Ra; lia) ltac:(reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)).
specialize (HPRE1 ltac:(rewrite getr_other by reg_neq_tac; rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity])).
specialize (HPRE1 ltac:(unfold raZ; rewrite getr_other by reg_neq_tac; rewrite R1, unsigned_lit_small by lia; lia)).
specialize (HPRE1 ltac:(rewrite getr_other by reg_neq_tac; rewrite R3, E3; exact Hgp)).
specialize (HPRE1 ltac:(rewrite getr_other by reg_neq_tac; rewrite R4, E4; exact Htp)).
specialize (HPRE1 ltac:(apply achain_low; unfold s0Z; rewrite getr_same by reg_neq_tac; rewrite unsigned_lit_small by lia; lia)).
eapply SRr_bind.
{ pose proof (TFIND fx ly S W (ms_regs ms) (ms_mem ms) _ [] t p T P HPRE1) as CALL. unfold cfg_at in CALL. apply CALL; clear CALL.
  - exact (arodata_ok_journalP _ _ _ pa_relro_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HRO).
  - rewrite R10, E10. reflexivity.
  - rewrite R11, E11. reflexivity.
  - lia. - exact Ht8. - lia. - lia. - lia. - exact LT.
  - apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem (ms_mem ms) t). 2: exact GT.
    rewrite length_map, LT. intros a Ha. apply KEEP1; lia.
  - exact LP.
  - apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem (ms_mem ms) p). 2: exact GP.
    rewrite length_map, LP. intros a Ha. apply KEEP1; lia.
  - exact MRt. - exact MRp.
  - apply (range_addressable_kept_win _ _ (spZ regs - 32) (spZ regs) t 400 KEEP1); [lia | lia | lia | exact RAt].
  - apply (shadow_hull_vis_kept_win _ _ (spZ regs - 32) (spZ regs) t 400 KEEP1); [lia | lia | lia | lia | exact SHt].
  - apply (range_addressable_kept_win _ _ (spZ regs - 32) (spZ regs) p 6 KEEP1); [lia | lia | lia | exact RAp].
  - apply (shadow_hull_vis_kept_win _ _ (spZ regs - 32) (spZ regs) p 6 KEEP1); [lia | lia | lia | lia | exact SHp].
  - rewrite Ra. lia.
  - exact OIt.
  - rewrite Ra. lia.
  - exact T1. }
cbv beta. intros W2 c2 Hwle2 (fq2 & ly2 & S2 & regs2 & mem2 & md2 & -> & Hfr2 & Hcsr2 & HJ2 & HP2 & HPerm2 & (r & Hr10 & Hfr) & HK2).
rewrite Ra in HK2. rewrite R1.
pose proof (ajournal_sub SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HJ2) as HJc.
rewrite Ra in HJc. specialize (HJc ltac:(lia) ltac:(lia) ltac:(intros a (rg & [] & _))). cbn [app] in HJc. rewrite Z.add_0_r in HJc.
pose proof (proj1 HJ2) as HAR2.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR1) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcell2 & _ & Kgot2 & _). rewrite HBgot, HBcell in Kgot2. rewrite HBcell in Kcell2.
jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2; 3]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | apply Forall_nil].
  - eapply (region_kept_stack_sub SEGS B); [exact HJ2 | exact HJc | exact Usp | rewrite Ra; lia | lia | lia | cbn; lia | cbn; lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
    [exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot2) | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
    [exact (HEI (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell2) | lia].
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite E10, unsigned_lit_small by lia; intros a Ha; [|lia].
    apply (mbyte_of_aview SEGS). apply HK2; lia. }
clear HS.
lazymatch type of HS2 with st_ok_pi _ _ ?E2 ?ss2 (mkst ?rg ?pc ?mm ?rom) =>
  pose proof (YL05.st_ok_xfx fx fq2 _ _ _ _ _ _ HS2 : st_ok_pi (fx := fq2) SEGS VAL E2 ss2 (mkst (fx := fq2) rg pc mm rom)) as HS end.
clear HS2. rewrite <- restrict_mkst_fx in HS.
remember (havoc E 48 (map (getr regs2) CLOB)) as Eh eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM Eh) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall n, (n < 48)%nat -> ew Eh n = ew E n) by (intros n Hn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE2 : env_agree 32 (Ereg regs (ro_extra T)) Eh) by (rewrite HE2; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HE2.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TROLE_OF_STK <= a < spZ regs) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hn. rewrite HK2 by lia. apply KEEP1; lia. }
clear SHOK HF HFr HG.
assert (SHOK : sh_ok SEGS RBx ro_SH Eh (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, ro_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W2) mem2 Eh RBx 10 t 400 t 0 400).
  + apply (range_addressable_kept_win _ _ (spZ regs - TROLE_OF_STK) (spZ regs) t 400 KEEP); [lia | lia | lia | exact RAt].
  + unfold U, RBx. cbn [sv_denot]. rewrite OLD2 by lia. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold RSB; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite OLD2 by lia. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + unfold SHADOW_OFF. intros. lia. }
assert (Rr : r = -1 \/ r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7).
{ unfold tbl_T1 in T1. destruct Hfr as [[-> _]|(? & _)]; lia. }
pose proof HJc as HJ3.
assert (F10 : ew Eh 10 = Z_to_bv 64 t) by (rewrite OLD2 by lia; exact E10).
let pin z := lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msr) =>
  pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) z HS ltac:(cbn [ms_regs mkst restrict]; exact Hr10) eq_refl) as HS0 end;
  clear HS; rename HS0 into HS;
  lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end in
destruct Rr as [->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]; [pin (-1) | pin 0 | pin 1 | pin 2 | pin 3 | pin 4 | pin 5 | pin 6 | pin 7].
all: paj_run_tok (RUN fq2) HS HJ3 SHOK Rspan; [awr_ok_tac; rewrite ?OLD2 by lia; try exact Usp |].
all: clear HF HFr HG.
all: lazymatch goal with HS : st_ok_pi _ _ _ ?ss _ |- _ => let pc := eval vm_compute in (ss_pc ss) in
  lazymatch pc with 10704 => psrr_branch_tok (RUN fq2) (BR fq2) HS SHOK Rspan | _ => idtac end end.
all: lazymatch goal with Hc : branch_taken BC_LTU _ _ = true |- _ =>
  exfalso; rewrite branch_ltu_U, (U_not Eh 10 t F10), U_lit in Hc by lia; apply Z.ltb_lt in Hc; lia | _ => idtac end.
all: lazymatch goal with HS : st_ok_pi _ _ _ ?ss _ |- _ => let pc := eval vm_compute in (ss_pc ss) in
  lazymatch pc with 10772 => idtac | _ => paj_run_tok (RUN fq2) HS HJ3 SHOK Rspan; [awr_ok_tac; rewrite ?OLD2 by lia; try exact Usp |] end end.
all: try clear HF HFr HG.
all: lazymatch goal with HS : st_ok_pi _ _ _ ?ss (restrict _ ?msx) |- _ =>
  let Q1 := fresh "Q1" in let Q10 := fresh "Q10" in let mat' := fresh "mat" in
  prreg HS (1%bv : bv 5) Q1; prreg HS (10%bv : bv 5) Q10;
  eapply (RET fq2 W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  intros mat'; unfold trole_of_post;
  lazymatch goal with |- apost_base _ _ _ _ _ _ _ _ _ _ _ _ _ (mkCfg (mkst ?r _ ?m _) ?d) => exists fq2, ly2, S2, r, m, d end;
  split; [cbn [ms_regs]; rewrite Q1, (OLD2 1%nat) by lia; rewrite E1, Hra; reflexivity|];
  split; [exact Hfr2|]; split; [exact Hcsr2|];
  split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ3|];
  split; [eapply (aregs_preserved_of_st_ok SEGS _ Eh _ _ regs (ro_extra T) HS); [exact HAE2 | vm_compute; reflexivity]|];
  split; [exact HPerm2|];
  lazymatch type of Q10 with
  | _ = Z_to_bv 64 18446744073709551615 =>
    exists (-1), (-1); split; [exact Hfr|]; split; [reflexivity|]; split;
    [cbn [ms_regs]; rewrite Q10; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity | left; reflexivity]
  | _ = sext 64 (bv_extract 0 32 (ew _ ?n)) =>
    lazymatch type of Hfr with find_res _ _ ?rr =>
    let o := eval vm_compute in (48 * rr + 8) in
    let Hkn := fresh "Hkn" in let Hu := fresh "Hu" in let Hrng := fresh "Hrng" in
    assert (Hkn : 0 <= rr < n_of T) by (destruct Hfr as [[? _]|(? & _)]; lia);
    destruct (ro_role_u T rr o eq_refl Hkn T2) as [Hu Hrng];
    exists rr, (role_of_e T rr); split; [exact Hfr|]; split; [reflexivity|]; split;
    [ cbn [ms_regs]; rewrite Q10, (OLD2 n) by lia;
      first [rewrite E33 | rewrite E34 | rewrite E35 | rewrite E36 | rewrite E37 | rewrite E38 | rewrite E39 | rewrite E40];
      rewrite Hu; apply sext32_small; lia
    | right; exact Hrng ]
    end
  end end.
Qed.
End w.
Theorem pb_role_of : trole_of_spec.
Proof. unfold trole_of_spec. intros fq. exact (@ro_walk fq). Qed.
End h.
End f.
End d.
