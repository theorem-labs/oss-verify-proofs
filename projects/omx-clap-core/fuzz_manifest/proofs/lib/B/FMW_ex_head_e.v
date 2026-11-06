(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v, with its module names changed; 259 of its 330 lines of code are new or changed and 1302 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_strkit.v, with its module paths and module names changed; 240 of its 267 lines of code are new or changed and 303 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_ex_head.v, with its module paths and module names changed; 299 of its 342 lines of code are new or changed and 224 lines of the source are left out. *)
(* G4.ExHead.HeadEntry, IMAGE B: the head walk's entry states (st_ok of ss_L, ss_W k s, ss_T, ss_N from ex_at_L) and the
   two region swaps (the word byte for the text byte at 0x8144c, text[i - 1] after the i <> 0 test at 0x81484), and the
   walk tactics the head files share (after FMW_plain.v fw_reg / pl_av / pl_mk / pl_g).
   Shape after image A's lib/A/FMW_ex_head_e.v (06d82004dc3); B's frame is 240 bytes, s5 (register 21) = text + i,
   s7 (register 23) = i, a6 (register 16) = text. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YCeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib FMTrapB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_ex_base FMW_ex_head_d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ---- walk tactics shared by the head files (after FMW_plain.v fw_reg, pl_av, pl_mk, pl_g) ---- *)
Ltac hd_reg HS r :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    rewrite (st_ok_restrict_reg segs H E ss ms r HS); change (sr_get (ss_regs ss) r) with e end.
Ltac hd_av W mem1 :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- _ =>
    let AVn := fresh "AVn" in
    pose proof (fw_nowin tfibsegs _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as AVn;
    lazymatch goal with AV : forall a, _ -> aview _ _ m0 a = aview _ _ mem1 a |- _ =>
      let AV2 := fresh "AV" in
      assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) m1 a = aview tfibsegs (w_H W) mem1 a)
        by (intros a Ha; rewrite (AVn a Ha); exact (AV a Ha));
      clear AV AVn; rename AV2 into AV end end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  repeat match goal with H : context [with_vm_backing (m_vm_lazy (with_vm_backing _ _ _)) _ _] |- _ =>
    rewrite wvb_collapse in H end.
Ltac hd_mk HS := rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl);
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
    let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end.
Ltac hd_g HS :=
  lazymatch goal with |- getr _ ?r = _ => hd_reg HS r end;
  cbn [sv_denot ew ewset Nat.eqb]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.

(* the letters of "prefix" are bytes *)
Lemma hd_e_prefix_byte : forall n, 0 <= nth n ManifestModel.prefix_lc 0 < 256.
Proof. intros n. do 6 (destruct n as [|n]; [cbn; lia|]). destruct n; cbn; lia. Qed.

(* the scalar facts of ex_at_L every entry lemma uses: the frame F = sp - 240 above alloc_ceiling (afn_pre's astk_ok),
   the text below alloc_ceiling and in one app band (cstr_ok), the registers and the frame slots *)
Ltac hd_e_unpack HAT cx :=
  let HB := fresh "HB" in let HC := fresh "HC" in let HSL := fresh "HSL" in let HSR := fresh "HSR" in
  let HCR := fresh "HCR" in let HSC := fresh "HSC" in let HPRE := fresh "HPRE" in let Hstk := fresh "Hstk" in
  let HCt := fresh "HCt" in
  destruct HAT as (HB & HC & HSL & HSR & HCR & HSC & R23 & R21);
  destruct HB as ((HPRE & _) & _ & _ & _ & _ & _ & _ & _ & _ & Htb);
  destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _);
  destruct Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _);
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
  destruct HC as (_ & _ & _ & Rsp & _ & _ & R25 & _ & _ & HCt & _);
  destruct HSL as (_ & _ & _ & _ & _ & _ & S68 & S70 & S78 & S80);
  destruct HSR as (R19 & R27 & R8);
  destruct HCR as (R16 & R17 & R5 & R6);
  destruct HSC as (Hi & _);
  destruct HCt as ((HGa & _) & H4096 & Hcl & _ & Ham & HRA & _);
  assert (HF1 : alloc_ceiling + 8224 <= cx_F cx)
    by (unfold cx_F, cx_sp; change STK_expected with (240 + 8224) in Hslo; lia);
  assert (HF2 : cx_F cx + 240 <= 2 ^ 47) by (unfold cx_F, cx_sp; lia);
  assert (HF3 : cx_F cx mod 16 = 0)
    by (unfold cx_F, cx_sp; replace (spZ (cx_regs cx) - 240) with (spZ (cx_regs cx) + (-15) * 16) by lia;
        rewrite Z_mod_plus_full; exact Hal16).

(* the pinned literal registers of every head state *)
Ltac hd_e_pins :=
  repeat (apply regs_ok_pin; [| intros X; discriminate X |]); [apply regs_ok_Ereg|..];
  cbn [sv_denot]; match goal with H : getr _ _ = _ |- _ => exact H end.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

Lemma hd_L_entry : forall cx i d f ly3 S3 W3 regs3 mem3 md3,
  ex_at_L B cx i d f ly3 S3 W3 regs3 mem3 md3 ->
  st_ok tfibsegs (Ereg regs3 (hd_extraL (nth i (cx_tb cx ++ [0]) 0))) ss_L
    (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 EX_L) mem3 (seg_rom tfibsegs))) /\
  sh_ok tfibsegs HD_Bx SH_L (Ereg regs3 (hd_extraL (nth i (cx_tb cx ++ [0]) 0))) (mrestrict (w_H W3) mem3).
Proof.
  intros cx i d f ly3 S3 W3 regs3 mem3 md3 HAT.
  hd_e_unpack HAT cx.
  set (t := cx_t cx) in *. set (tb := cx_tb cx) in *.
  destruct (HGa i ltac:(rewrite length_app; cbn [length]; lia)) as [Vc Rc].
  set (c := nth i (tb ++ [0]) 0) in *.
  rewrite restrict_mkst_fx.
  set (E := Ereg regs3 (hd_extraL c)).
  assert (U2 : bv_unsigned (ew E 2) = cx_F cx)
    by (subst E; rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl), Rsp; apply unsigned_lit_small; lia).
  assert (E25 : ew E 25 = Z_to_bv 64 SHADOW_OFF)
    by (subst E; rewrite (ew_Ereg_nat regs3 _ 25 25%bv eq_refl); exact R25).
  assert (U25 : bv_unsigned (ew E 25) = SHADOW_OFF)
    by (rewrite E25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (E21 : ew E 21 = Z_to_bv 64 (t + Z.of_nat i))
    by (subst E; rewrite (ew_Ereg_nat regs3 _ 21 21%bv eq_refl); exact R21).
  assert (U21 : bv_unsigned (ew E 21) = t + Z.of_nat i) by (rewrite E21; apply unsigned_lit_small; lia).
  assert (U23 : bv_unsigned (ew E 23) = Z.of_nat i)
    by (subst E; rewrite (ew_Ereg_nat regs3 _ 23 23%bv eq_refl), R23; apply unsigned_lit_small; lia).
  assert (U16 : bv_unsigned (ew E 16) = t)
    by (subst E; rewrite (ew_Ereg_nat regs3 _ 16 16%bv eq_refl), R16; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 c) by (subst E; exact (ew_Ereg_extra regs3 _ 0)).
  assert (U32 : bv_unsigned (ew E 32) = c) by (rewrite E32; apply unsigned_lit_small; lia).
  split.
  - unfold ss_L. apply (entry_st_ok_full tfibsegs); change (Ereg regs3 (hd_extraL c)) with E.
    + unfold hd_pins. hd_e_pins.
    + vm_compute. reflexivity.
    + unfold hd_frameL, hd_byteL. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      * rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
        -- apply (chunk_ok_val tfibsegs E _ (cx_F cx) 0x68 8 (SLit EX_PREFIX) EX_PREFIX);
             [reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold EX_PREFIX; lia | cbn; lia | exact S68].
        -- apply (chunk_ok_val tfibsegs E _ (cx_F cx) 0x70 8 (SLit EX_MASK1) EX_MASK1);
             [reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold EX_MASK1; lia | cbn; lia | exact S70].
        -- apply (chunk_ok_val tfibsegs E _ (cx_F cx) 0x78 8 (SOff 16 0) t);
             [cbn [sv_denot]; rewrite U16, Z.add_0_r; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
             | cbn; lia | exact S78].
      * rewrite U21. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val tfibsegs E _ (t + Z.of_nat i) 0 1 (SOff 32 0) c);
          [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia
          | cbn; lia |].
        rewrite Z.add_0_r. exact Vc.
    + apply pairwise_disjoint_of_extents. unfold hd_frameL, hd_byteL, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U21.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; lia.
    + split; [|split; [exact I | exact I]].
      unfold HD_AF2, HD_AF25, HD_AF21, HD_AF23, HD_AF16, HD_AFC. cbn [f_atoms atoms_ok]. unfold afact_ok.
      cbn [af_lo af_hi af_al2].
      rewrite U2, U25, U21, U23, U16, U32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold FW_SB, SHADOW_OFF. repeat split; first [exact HF3 | lia].
  - unfold sh_ok, SH_L. constructor; [|constructor].
    apply (shent_ok_of_range tfibsegs (w_H W3) mem3 E HD_Bx 21 t (Z.of_nat (length tb) + 1) (t + Z.of_nat i) 0 1).
    + exact HRA.
    + unfold HD_Bx. apply (U_atom E 25 SHADOW_OFF E25). unfold SHADOW_OFF. lia.
    + apply (U_atom E 21 _ E21). lia.
    + lia.
    + lia.
    + intros x Hx. cbn [Z.min Z.max] in Hx. unfold amem_range in Ham. unfold SHADOW_OFF. lia.
Qed.

Lemma hd_W_entry : forall cx i d f k s ly3 S3 W3 regs1 mem1 md1,
  ex_at_L B cx i d f ly3 S3 W3 regs1 mem1 md1 ->
  getr regs1 12 = w64 (Z.of_nat k) -> getr regs1 13 = w64 (2 ^ 64 - 1 - (cx_t cx + Z.of_nat i)) ->
  (k < 6)%nat -> (i + k <= length (cx_tb cx))%nat ->
  val_mem tfibsegs (mrestrict (w_H W3) mem1) (SHADOW_OFF + HD_WSH) 1 s -> 0 <= s < 256 ->
  st_ok tfibsegs (Ereg regs1 [Z_to_bv 64 (nth (i + k) (cx_tb cx ++ [0]) 0)]) (ss_W (Z.of_nat k) s)
    (restrict (w_H W3) (mkst regs1 (Z_to_bv 64 EX_W) mem1 (seg_rom tfibsegs))) /\
  sh_ok tfibsegs HD_Bx (SH_W (Z.of_nat k)) (Ereg regs1 [Z_to_bv 64 (nth (i + k) (cx_tb cx ++ [0]) 0)])
    (mrestrict (w_H W3) mem1).
Proof.
  intros cx i d f k s ly3 S3 W3 regs1 mem1 md1 HAT R12 R13 Hk Hik Vs Hs.
  hd_e_unpack HAT cx.
  set (t := cx_t cx) in *. set (tb := cx_tb cx) in *.
  destruct (HGa (i + k)%nat ltac:(rewrite length_app; cbn [length]; lia)) as [Vc Rc].
  set (c := nth (i + k) (tb ++ [0]) 0) in *.
  rewrite restrict_mkst_fx.
  set (E := Ereg regs1 [Z_to_bv 64 c]).
  assert (U2 : bv_unsigned (ew E 2) = cx_F cx)
    by (subst E; rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl), Rsp; apply unsigned_lit_small; lia).
  assert (E25 : ew E 25 = Z_to_bv 64 SHADOW_OFF)
    by (subst E; rewrite (ew_Ereg_nat regs1 _ 25 25%bv eq_refl); exact R25).
  assert (U25 : bv_unsigned (ew E 25) = SHADOW_OFF)
    by (rewrite E25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (E21 : ew E 21 = Z_to_bv 64 (t + Z.of_nat i))
    by (subst E; rewrite (ew_Ereg_nat regs1 _ 21 21%bv eq_refl); exact R21).
  assert (U21 : bv_unsigned (ew E 21) = t + Z.of_nat i) by (rewrite E21; apply unsigned_lit_small; lia).
  assert (U23 : bv_unsigned (ew E 23) = Z.of_nat i)
    by (subst E; rewrite (ew_Ereg_nat regs1 _ 23 23%bv eq_refl), R23; apply unsigned_lit_small; lia).
  assert (U16 : bv_unsigned (ew E 16) = t)
    by (subst E; rewrite (ew_Ereg_nat regs1 _ 16 16%bv eq_refl), R16; apply unsigned_lit_small; lia).
  assert (U13 : bv_unsigned (ew E 13) = 2 ^ 64 - 1 - (t + Z.of_nat i))
    by (subst E; rewrite (ew_Ereg_nat regs1 _ 13 13%bv eq_refl), R13; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 c) by (subst E; exact (ew_Ereg_extra regs1 _ 0)).
  assert (U32 : bv_unsigned (ew E 32) = c) by (rewrite E32; apply unsigned_lit_small; lia).
  split.
  - unfold ss_W. apply (entry_st_ok_full tfibsegs); change (Ereg regs1 [Z_to_bv 64 c]) with E.
    + unfold hd_pins. hd_e_pins.
    + unfold regions_wf, region_wf, hd_byteW, hd_wsh, chunk_inside.
      cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks forallb YP09.c_off YP09.c_len YP09.c_val YP09.cv_len].
      rewrite !(proj2 (Z.leb_le _ _)) by lia. reflexivity.
    + unfold hd_byteW, hd_wsh. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      * rewrite U21. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val tfibsegs E _ (t + Z.of_nat i) (Z.of_nat k) 1 (SOff 32 0) c);
          [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia
          | cbn; lia |].
        replace (t + Z.of_nat i + Z.of_nat k) with (t + Z.of_nat (i + k)) by lia. exact Vc.
      * rewrite U25. unfold HD_WSH, SHADOW_OFF. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val tfibsegs E _ 0x7fff8000 0x41a4 1 (SLit s) s);
          [reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia | exact Vs].
    + apply pairwise_disjoint_of_extents. unfold hd_byteW, hd_wsh, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U21, U25.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold amem_range in Ham. unfold HD_WSH, SHADOW_OFF.
      repeat split; lia.
    + split; [|split; [exact I | exact I]].
      unfold HD_AF2, HD_AF25, HD_AF21, HD_AF23, HD_AF16, HD_AF13, HD_AFC. cbn [f_atoms atoms_ok]. unfold afact_ok.
      cbn [af_lo af_hi af_al2].
      rewrite U2, U25, U21, U23, U16, U13, U32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold FW_SB, SHADOW_OFF. repeat split; first [exact HF3 | lia].
  - unfold sh_ok, SH_W. constructor; [|constructor].
    apply (shent_ok_of_range tfibsegs (w_H W3) mem1 E HD_Bx 21 t (Z.of_nat (length tb) + 1) (t + Z.of_nat i)
      (Z.of_nat k) (Z.of_nat k + 1)).
    + exact HRA.
    + unfold HD_Bx. apply (U_atom E 25 SHADOW_OFF E25). unfold SHADOW_OFF. lia.
    + apply (U_atom E 21 _ E21). lia.
    + lia.
    + lia.
    + intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. unfold amem_range in Ham. unfold SHADOW_OFF. lia.
Qed.

Lemma hd_W_swap : forall E ss ms k s,
  st_ok tfibsegs E ss ms -> ss_mem ss = [hd_byteW k; hd_wsh s] -> ss_fregs ss = [] ->
  ew E 25 = Z_to_bv 64 SHADOW_OFF -> 0 <= k < 6 ->
  val_mem tfibsegs (ms_mem ms) (EX_WORD + k) 1 (nth (Z.to_nat k) ManifestModel.prefix_lc 0) ->
  st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) [hd_wbyte k; hd_wsh s] (ss_resv ss) (ss_facts ss)) ms.
Proof.
  intros E ss ms k s HS Hm _ E25 Hk Vw.
  assert (HS1 : st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) [hd_wsh s] (ss_resv ss) (ss_facts ss)) ms).
  { apply (st_ok_submem tfibsegs); [exact HS | rewrite Hm | vm_compute; reflexivity].
    apply submem_drop, submem_keep; [|apply submem_nil].
    unfold subregion, hd_wsh. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia | intros x Hx; exact Hx]. }
  pose proof (ast_ok_add_region tfibsegs E _ ms (hd_wbyte k) HS1) as HS2.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
  pose proof (hd_e_prefix_byte (Z.to_nat k)) as Hw.
  apply HS2.
  - assert (Hk' : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5) by lia.
    repeat (destruct Hk' as [->|Hk']); try subst k; vm_compute; reflexivity.
  - unfold region_ok, hd_wbyte.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    unfold EX_WORD. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val tfibsegs E _ 0 (0x20d20 + k) 1 (SLit (nth (Z.to_nat k) ManifestModel.prefix_lc 0))
      (nth (Z.to_nat k) ManifestModel.prefix_lc 0));
      [reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
    rewrite Z.add_0_l. exact Vw.
  - cbn [all_disjoint]. split; [|exact I]. unfold extent_disjoint, hd_wbyte, hd_wsh.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E25, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    left. unfold EX_WORD, HD_WSH, SHADOW_OFF. lia.
Qed.

Lemma hd_T_entry : forall cx i d f ly3 S3 W3 regs1 mem1 md1,
  ex_at_L B cx i d f ly3 S3 W3 regs1 mem1 md1 -> (i + 6 <= length (cx_tb cx))%nat ->
  st_ok tfibsegs (Ereg regs1 [Z_to_bv 64 (nth (pred i) (cx_tb cx) 0)]) ss_T
    (restrict (w_H W3) (mkst regs1 (Z_to_bv 64 EX_TL) mem1 (seg_rom tfibsegs))).
Proof.
  intros cx i d f ly3 S3 W3 regs1 mem1 md1 HAT Hi6.
  hd_e_unpack HAT cx.
  set (t := cx_t cx) in *. set (tb := cx_tb cx) in *.
  pose proof (Nat.le_pred_l i) as Hpi.
  destruct (HGa (pred i) ltac:(rewrite length_app; cbn [length]; lia)) as [_ Rc].
  rewrite app_nth1 in Rc by lia.
  set (c := nth (pred i) tb 0) in *.
  rewrite restrict_mkst_fx.
  set (E := Ereg regs1 [Z_to_bv 64 c]).
  assert (U2 : bv_unsigned (ew E 2) = cx_F cx)
    by (subst E; rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl), Rsp; apply unsigned_lit_small; lia).
  assert (U25 : bv_unsigned (ew E 25) = SHADOW_OFF)
    by (subst E; rewrite (ew_Ereg_nat regs1 _ 25 25%bv eq_refl), R25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U21 : bv_unsigned (ew E 21) = t + Z.of_nat i)
    by (subst E; rewrite (ew_Ereg_nat regs1 _ 21 21%bv eq_refl), R21; apply unsigned_lit_small; lia).
  assert (U23 : bv_unsigned (ew E 23) = Z.of_nat i)
    by (subst E; rewrite (ew_Ereg_nat regs1 _ 23 23%bv eq_refl), R23; apply unsigned_lit_small; lia).
  assert (U16 : bv_unsigned (ew E 16) = t)
    by (subst E; rewrite (ew_Ereg_nat regs1 _ 16 16%bv eq_refl), R16; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = c)
    by (subst E; rewrite (ew_Ereg_extra regs1 _ 0); apply unsigned_lit_small; lia).
  unfold ss_T. apply (entry_st_ok_full tfibsegs); change (Ereg regs1 [Z_to_bv 64 c]) with E.
  - unfold hd_pins. hd_e_pins.
  - reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [|split; [exact I | exact I]].
    unfold HD_AF2, HD_AF25, HD_AF21, HD_AF23, HD_AF16, HD_AFC. cbn [f_atoms atoms_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2].
    rewrite U2, U25, U21, U23, U16, U32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold FW_SB, SHADOW_OFF. repeat split; first [exact HF3 | lia].
Qed.

Lemma hd_T_byte : forall E ss ms p c,
  st_ok tfibsegs E ss ms -> ss_mem ss = [] -> ss_fregs ss = [] ->
  ew E 21 = Z_to_bv 64 p -> ew E 32 = Z_to_bv 64 c -> 4096 < p < 2 ^ 47 -> 0 <= c < 256 ->
  val_mem tfibsegs (ms_mem ms) (p - 1) 1 c ->
  st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) [hd_byteT] (ss_resv ss) (ss_facts ss)) ms.
Proof.
  intros E ss ms p c HS Hm _ E21 E32 Hp Hc Vc.
  replace [hd_byteT] with (hd_byteT :: ss_mem ss) by (rewrite Hm; reflexivity).
  apply (ast_ok_add_region tfibsegs); [exact HS | vm_compute; reflexivity | | rewrite Hm; exact I].
  unfold region_ok, hd_byteT.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E21, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val tfibsegs E _ p (-1) 1 (SOff 32 0) c);
    [cbn [sv_denot]; rewrite E32, unsigned_lit_small, Z.add_0_r by lia; reflexivity
    | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
  replace (p + -1) with (p - 1) by lia. exact Vc.
Qed.

Lemma hd_N_entry : forall cx i d f ly3 S3 W3 regs1 mem1 md1,
  ex_at_L B cx i d f ly3 S3 W3 regs1 mem1 md1 ->
  st_ok tfibsegs (Ereg regs1 [Z_to_bv 64 (2 ^ 64 - 1 - cx_t cx)]) ss_N
    (restrict (w_H W3) (mkst regs1 (Z_to_bv 64 EX_NEXT) mem1 (seg_rom tfibsegs))).
Proof.
  intros cx i d f ly3 S3 W3 regs1 mem1 md1 HAT.
  hd_e_unpack HAT cx.
  set (t := cx_t cx) in *. set (tb := cx_tb cx) in *.
  rewrite restrict_mkst_fx.
  set (E := Ereg regs1 [Z_to_bv 64 (2 ^ 64 - 1 - t)]).
  assert (U2 : bv_unsigned (ew E 2) = cx_F cx)
    by (subst E; rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl), Rsp; apply unsigned_lit_small; lia).
  assert (U25 : bv_unsigned (ew E 25) = SHADOW_OFF)
    by (subst E; rewrite (ew_Ereg_nat regs1 _ 25 25%bv eq_refl), R25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U21 : bv_unsigned (ew E 21) = t + Z.of_nat i)
    by (subst E; rewrite (ew_Ereg_nat regs1 _ 21 21%bv eq_refl), R21; apply unsigned_lit_small; lia).
  assert (U23 : bv_unsigned (ew E 23) = Z.of_nat i)
    by (subst E; rewrite (ew_Ereg_nat regs1 _ 23 23%bv eq_refl), R23; apply unsigned_lit_small; lia).
  assert (U16 : bv_unsigned (ew E 16) = t)
    by (subst E; rewrite (ew_Ereg_nat regs1 _ 16 16%bv eq_refl), R16; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = 2 ^ 64 - 1 - t)
    by (subst E; rewrite (ew_Ereg_extra regs1 _ 0); apply unsigned_lit_small; lia).
  unfold ss_N. apply (entry_st_ok_full tfibsegs); change (Ereg regs1 [Z_to_bv 64 (2 ^ 64 - 1 - t)]) with E.
  - unfold hd_pins. hd_e_pins.
  - vm_compute. reflexivity.
  - unfold hd_frameN. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val tfibsegs E _ (cx_F cx) 0x80 8 (SOff 32 0) (2 ^ 64 - 1 - t));
      [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
      | cbn; lia | exact S80].
  - first [ exact I | split; exact I | (cbn [pairwise_disjoint all_disjoint]; tauto)
          | (apply pairwise_disjoint_of_extents; cbn [map zpairwise_disjoint zall_disjoint]; tauto) ].
  - split; [|split; [exact I | exact I]].
    unfold HD_AF2, HD_AF25, HD_AF21, HD_AF23, HD_AF16, HD_AFT. cbn [f_atoms atoms_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2].
    rewrite U2, U25, U21, U23, U16, U32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold FW_SB, SHADOW_OFF. repeat split; first [exact HF3 | lia].
Qed.
End s.

Print Assumptions hd_L_entry.
Print Assumptions hd_W_entry.
Print Assumptions hd_W_swap.
Print Assumptions hd_T_entry.
Print Assumptions hd_T_byte.
Print Assumptions hd_N_entry.
