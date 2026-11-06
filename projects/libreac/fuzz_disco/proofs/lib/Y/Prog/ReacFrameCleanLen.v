(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_headamp_tx_set_resweep on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/HeadampTxSetResweep.v, with its module paths, module names and numbers changed; 174 of its 247 lines of code are new or changed and 209 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/ReacHuntHeardAnything.v, with its module paths and module names changed; 158 of its 201 lines of code are new or changed and 204 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0s YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_frame_clean_len_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_frame_clean_len.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Lemma fcl_sep : forall segs m a b, val_mem segs m a 8 KM -> val_mem segs m b 8 KT -> a + 8 <= b \/ b + 8 <= a.
Proof.
intros segs m a b HM HT.
destruct (Z_le_gt_dec (a + 8) b) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec (b + 8) a) as [H2|H2]; [right; exact H2|].
exfalso. destruct (Z_le_gt_dec a b) as [H3|H3].
- destruct (Z.to_nat (b - a)) as [|k] eqn:Hk.
  + pose proof (HM 0%nat ltac:(lia)) as E1. pose proof (HT 0%nat ltac:(lia)) as E2.
    replace (b + Z.of_nat 0) with (a + Z.of_nat 0) in E2 by lia. rewrite E2 in E1. vm_compute in E1. discriminate E1.
  + pose proof (HM (S k) ltac:(lia)) as E1. pose proof (HT 0%nat ltac:(lia)) as E2.
    replace (b + Z.of_nat 0) with (a + Z.of_nat (S k)) in E2 by lia. rewrite E2 in E1.
    do 7 (destruct k as [|k]; [vm_compute in E1; discriminate E1|]). lia.
- destruct (Z.to_nat (a - b)) as [|k] eqn:Hk; [lia|].
  pose proof (HT (S k) ltac:(lia)) as E1. pose proof (HM 0%nat ltac:(lia)) as E2.
  replace (a + Z.of_nat 0) with (b + Z.of_nat (S k)) in E2 by lia. rewrite E2 in E1.
  do 7 (destruct k as [|k]; [vm_compute in E1; discriminate E1|]). lia.
Qed.
Lemma fcl_arith : forall n, 54 <= n < 2 ^ 64 ->
  zcanon (n + zcanon (Z.land (zcanon (zcanon 0 - zcanon (if zcanon (Z.lor
    (zcanon (Z.shiftr (zcanon (zcanon (n * zcanon 10248191152060862009) + zcanon (-6))) (Z.land (zcanon 2) 63)))
    (zcanon (zcanon (n * zcanon 47261439850130342148203327256459739136) + zcanon (-27670116110564327424))))
    <? zcanon 512409557603043101 then 1 else 0))) (zcanon (-2))))
  = reac_frame_clean_len_model n.
Proof.
intros n Hn. unfold zcanon, M64.
change 10248191152060862009 with KM. change 512409557603043101 with KT.
assert (Hy : (n * (KM mod 2 ^ 64) mod 2 ^ 64 + -6 mod 2 ^ 64) mod 2 ^ 64 = (n * KM + -6) mod 2 ^ 64).
{ rewrite Z.mul_mod_idemp_r by lia. rewrite <- Z.add_mod by lia. reflexivity. }
assert (Hz : (n * (47261439850130342148203327256459739136 mod 2 ^ 64) mod 2 ^ 64 + -27670116110564327424 mod 2 ^ 64) mod 2 ^ 64
  = (Z.shiftl ((n * KM + -6) mod 2 ^ 64) 62) mod 2 ^ 64).
{ rewrite Z.mul_mod_idemp_r by lia. rewrite <- Z.add_mod by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.mul_mod_idemp_l by lia. f_equal. unfold KM. ring. }
rewrite Hy, Hz. change (Z.land (2 mod 2 ^ 64) 63) with 2.
rewrite reac_frame_clean_len.rot_wrap. rewrite (Z.mod_small KT) by (unfold KT; lia).
destruct (reac_frame_clean_len.c2 n Hn) as [C1 C2].
unfold reac_frame_clean_len_model. rewrite (proj2 (Z.leb_le 54 n)) by lia. cbn [andb].
destruct (Z.ltb_spec (((n * KM + -6) mod 2 ^ 64) mod 4 * 2 ^ 62 + ((n * KM + -6) mod 2 ^ 64) / 4) KT) as [L | L].
- rewrite (proj2 (Z.eqb_eq _ 2) (C1 L)).
  change ((Z.land ((0 mod 2 ^ 64 - 1 mod 2 ^ 64) mod 2 ^ 64) (-2 mod 2 ^ 64)) mod 2 ^ 64) with 18446744073709551614.
  replace (n + 18446744073709551614) with ((n - 2) + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
- assert (N : (n - 52) mod 36 <> 2) by (intro X; specialize (C2 X); lia).
  rewrite (proj2 (Z.eqb_neq _ 2) N).
  change ((Z.land ((0 mod 2 ^ 64 - 0 mod 2 ^ 64) mod 2 ^ 64) (-2 mod 2 ^ 64)) mod 2 ^ 64) with 0.
  rewrite Z.add_0_r. apply Z.mod_small. lia.
Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PO : PAObjImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Definition REAC_FRAME_CLEAN_LEN_STK : Z := ESTACK.
Definition treac_frame_clean_len_post (fq : YK11.FPState) (regs : bvmap 5 word) ly S (W : world SEGS) mem md (n : Z)
  : world SEGS -> config -> Prop :=
  fun W' c' =>
    apost_base (fx := fq) SEGS B REAC_FRAME_CLEAN_LEN_STK [] regs ly S W mem md 0
      (fun ly' S' W' regs' mem' md' =>
         getr regs' 10 = w64 (reac_frame_clean_len_model n) /\
         Permutation (ablocks B ly' S') (ablocks B ly S)) W' c'.
Definition treac_frame_clean_len_spec : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (n : Z),
  afn_pre SEGS B REAC_FRAME_CLEAN_LEN_STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  getr regs 10 = w64 n -> 0 <= n < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 63)) 8 KM ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 64)) 8 KT ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_frame_clean_len) regs mem md)
    (treac_frame_clean_len_post fq regs ly S W mem md n).
Definition fcl_regions : smem :=
[ YP09.mkRegion (Some (A_OBJ 63)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit KM))];
  YP09.mkRegion (Some (A_OBJ 64)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit KT))] ].
Definition ss_fcl : sstate := mkSS AF_both3_reac_frame_clean_len sr_atoms fcl_regions None (mkFacts [] [] []).
Definition FCLBx : sv := SLit SHADOW_OFF.
Definition FCLspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Theorem pb_reac_frame_clean_len : treac_frame_clean_len_spec.
Proof.
unfold treac_frame_clean_len_spec.
intros fq ly S W regs mem md ch n HPRE HRO H10 Rn HKM HKT.
pose proof (pa_segs_low) as Hsegs.
pose proof (ajournal_init SEGS B REAC_FRAME_CLEAN_LEN_STK [] ly S W _ mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
assert (G1 : getr (regupd regs 8 (Z_to_bv 64 0)) 1 = getr regs 1) by (unfold getr; cbn; rewrite regupd_other; [reflexivity | intros X; apply (f_equal bv_unsigned) in X; vm_compute in X; discriminate X]).
assert (G2 : getr (regupd regs 8 (Z_to_bv 64 0)) 2 = getr regs 2) by (unfold getr; cbn; rewrite regupd_other; [reflexivity | intros X; apply (f_equal bv_unsigned) in X; vm_compute in X; discriminate X]).
unfold spZ in HJ. rewrite G2 in HJ. fold (spZ regs) in HJ.
rewrite G1 in Hra.
pose proof (pa_obj_img_all 63 ltac:(vm_compute; lia)) as HO63. pose proof (pa_obj_img_all 64 ltac:(vm_compute; lia)) as HO64.
pose proof (fcl_sep _ _ _ _ HKM HKT) as Hsep.
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs []) k) by (intros k Hk; subst E; apply Eimg_low; exact Hk).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 n) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E63 : ew E (A_OBJ 63) = Z_to_bv 64 (VAL (A_OBJ 63))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E64 : ew E (A_OBJ 64) = Z_to_bv 64 (VAL (A_OBJ 64))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (HAE : env_agree 32 (Ereg regs []) E) by (split; [intros k Hk; rewrite EL by (unfold A_TEXT; lia); reflexivity | subst E; reflexivity]).
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v).
{ intros k v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. }
assert (HS : st_ok_pi SEGS VAL E ss_fcl (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_both3_reac_frame_clean_len)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_fcl. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - pose proof (pa_val_range (A_OBJ 63)) as HV63. pose proof (pa_val_range (A_OBJ 64)) as HV64.
    unfold IMG_LO, IMG_TOP in HO63, HO64.
    unfold fcl_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok; cbv zeta;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite (VB (A_OBJ 63) (VAL (A_OBJ 63)) E63) by (pose proof (pa_val_range (A_OBJ 63)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 63)) 0 8 (SLit KM) KM); [reflexivity | unfold KM; lia | lia |].
      rewrite Z.add_0_r. exact HKM.
    + rewrite (VB (A_OBJ 64) (VAL (A_OBJ 64)) E64) by (pose proof (pa_val_range (A_OBJ 64)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 64)) 0 8 (SLit KT) KT); [reflexivity | unfold KT; lia | lia |].
      rewrite Z.add_0_r. exact HKT.
  - apply pairwise_disjoint_of_extents. unfold fcl_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 63) (VAL (A_OBJ 63)) E63) by (pose proof (pa_val_range (A_OBJ 63)); lia).
    rewrite (VB (A_OBJ 64) (VAL (A_OBJ 64)) E64) by (pose proof (pa_val_range (A_OBJ 64)); lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  - split; [|split; [exact I | exact I]]. cbn. exact I. }
assert (SHOK : sh_ok SEGS FCLBx [] E (mrestrict (w_H W) (ms_mem (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_both3_reac_frame_clean_len)) mem (seg_rom SEGS))))) by constructor.
unfold cfg_at. change (w64 (BASE + AF_both3_reac_frame_clean_len)) with (Z_to_bv 64 (BASE + AF_both3_reac_frame_clean_len)).
pose (RUN := paj_run (fx := fq) B LAWS).
pose (BR := paj_branch (fx := fq) (PI := PI)).
pose (RET := paj_ret_at (fx := fq) (PL := PL_both3_0) (PI := PI)).
clear HE EL.
let leaf_ret := idtac;
  lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  let R10 := fresh "R10" in let R1 := fresh "R1" in
  pose proof (st_ok_pi_restrict_reg _ E _ _ (10%bv : bv 5) HS) as R10;
  let e := eval vm_compute in (sr_get (ss_regs ssx) 10%bv) in change (sr_get (ss_regs ssx) 10%bv) with e in R10;
  cbn [ms_regs restrict mkst] in R10;
  rewrite denot_lit_U in R10; rewrite ?U_SAlu, ?U_SMd, ?U_SOff, ?U_SLit in R10; cbn [zalu_raw zmd_raw] in R10;
  rewrite E10 in R10; rewrite unsigned_lit_small in R10 by lia; rewrite ?Z.add_0_r in R10; rewrite ?(zcanon_id n) in R10 by (unfold M64; lia);
  prreg HS (1%bv : bv 5) R1;
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  let mat' := fresh "mat" in intros mat';
  unfold treac_frame_clean_len_post;
  apply apost_base_same_fx; eexists ly, S, _, _, _;
  split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|];
  split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
  split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs [] HS); [exact HAE | vm_compute; reflexivity]|];
  split; [|apply Permutation_refl];
  cbn [ms_regs]; rewrite R10; unfold w64;
  repeat match goal with H : branch_taken _ _ _ = _ |- _ =>
    rewrite branch_ltu_U, (U_atom E 10 n E10 Rn), U_lit in H by lia;
    first [apply Z.ltb_lt in H | apply Z.ltb_ge in H] end;
  f_equal; first [ unfold reac_frame_clean_len_model; rewrite (proj2 (Z.leb_gt 54 n)) by lia; reflexivity
                 | apply fcl_arith; lia ] end in
let rec go := idtac;
  lazymatch goal with HS : st_ok_pi _ _ _ ?ss0 _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_tok RUN HS HJ SHOK FCLspan; [awr_ok_tac |];
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  lazymatch goal with
  | HS' : st_ok_pi _ _ _ ?ss _, SHOK' : sh_ok _ _ _ _ _ |- _ =>
    let K := eval vm_compute in (run_K A_LIM FCLBx [] ss) in
    let why := lazymatch paj_tables RUN with (?tpi, ?tw) => psym_why_tok tpi tw K FCLBx FCLspan (@nil shent) (start K FCLBx FCLspan [] ss) end in
    lazymatch why with
    | SR_jalr _ => leaf_ret
    | SR_branch _ _ _ => psrr_branch_tok RUN BR HS' SHOK' FCLspan; [go | go]
    | _ => fail
    end
  end end in
go.
Qed.
End h.
End f.
End d.
