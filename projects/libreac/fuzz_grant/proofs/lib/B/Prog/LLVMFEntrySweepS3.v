(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySweepS3), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntrySweepS3.v. *)
(* Segment 3 of the sweep phase of fuzz_grant's entry function on IMAGE B:
   0x815d0 .. 0x81618 (fuzz_grant.c:321-322) — the two bcmp against HEAD_ACK (object 4,
   the call at 0x815e0) and HEAD_MARK (object 5, the call at 0x81604), and the three
   registers the first group-A loop starts from. Three branches are refuted here: the two
   `bnez a0` into the abort block 0x81d98 (0x815e4 and 0x81608), because both compared
   ranges hold the same 34 bytes, and the UBSan pointer-overflow guard `bltu a0,s11` into
   the trap 0x81f48 (0x815ec, a0 = -137), because the sweep buffer lies below the
   allocator's ceiling. The ground this walk stands on is LLVMFEntrySweepS3c.v.

   Adapted from lib/A/Prog/GrantEntrySweepS3.v (a working branch afd75724b5b, blob
   d462a5d0c, 332 lines), which carries no licence header of its own.
   Image B holds the sweep buffer in s11 (image A: s5),
   adds the overflow guard at 0x815ec between the two calls, sets s2 = 34 before the
   second call (so that call is not made with every callee-saved register as the cut
   left it), and starts the group-A loop with s10 = 0, s9 = s + 34 and s4 = 3 (image A:
   s10 = 0, s11 = s + 34, s5 = 3); the two tables' bytes, globals entries and bounds come
   from `GSW_IMG` where image A's segment takes seven Hypotheses (lib/A/Prog/GrantEntrySweepS3.v:55-65). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaRun PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC88.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantPa GrantPaLib GrantRo GrantBContracts
LLVMFEntryDefs LLVMFEntrySweepDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC1g YC1h YC1i YC85 GrantFrame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import LLVMFEntrySeat LLVMFEntrySweepS3c.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel GrantModel GrantSweepModel BuildSweepModel SweepRowCheck GrantSlotPlan.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require SlotNeeds_c.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* Image A's text was written with this flag false; `Local` keeps the setting here. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* Listing offsets of the two bcmp returns. *)
Definition GPS_hd1 : Z := 0xba8.    (* 0x815e4, after bcmp(sweep, HEAD_ACK, 34)        *)
Definition GPS_hd2 : Z := 0xbcc.    (* 0x81608, after bcmp(sweep + 136, HEAD_MARK, 34) *)

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
Context {RO : ro_below_ofl (@pa_segs _ grant_listing PI) (@pa_relro_lo _ grant_listing PI) (@pa_relro_hi _ grant_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation GF := (fun GI => ge_from B MT (ge_post B MT) GI).

(* ---- the runtime and the image facts this segment uses (conjuncts of GSW_RT, GSW_IMG) ---- *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA GS___interceptor_trampoline_bcmp).
Hypothesis HVIS : img_shadow_vis SEGS B.
Hypothesis HGL : globs_marked SEGS B GRANT_GLOBS_B.
Hypothesis HIMG : GSW_IMG B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* One call of the bcmp wrapper on 34 equal bytes: a0 comes back 0, the journal
   grows, the callee-saved registers are kept, and so is every byte the cuts name. *)
Lemma gsw_bcmp : forall cx fp k ly3 S3 W3 (regsT : bvmap 5 word) memT mdT t s x y (L : list Z) raw,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 memT mdT k ->
  YG01.frames S3 = [(GE_CID, fp)] ->
  In (t, 460) (ablocks B ly3 S3) -> In (s, sw_mbytes (c_pl cx)) (ablocks B ly3 S3) ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 34 ->
  getr regsT 2 = w64 (c_sp1 cx) -> getr regsT 3 = getr (c_regs cx) 3 -> getr regsT 4 = getr (c_regs cx) 4 ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  s <= x -> x + 34 <= s + sw_mbytes (c_pl cx) ->
  In (y, 34) GRANT_GLOBS_B -> IMG_LO + 64 <= y -> y + 34 + 64 <= IMG_HI ->
  length L = 34%nat ->
  garr8 SEGS (mrestrict (w_H W3) memT) x L -> garr8 SEGS (mrestrict (w_H W3) memT) y L ->
  SRr SEGS W3 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA GS___interceptor_trampoline_bcmp)) memT (seg_rom SEGS)) mdT)
    (fun W2 c2 => W2 = W3 /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
       ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
         [(GE_CID, fp)] ly3 S3 W3 mem2 md2 k /\
       aregs_preserved regsT regs2 /\ getr regs2 10 = Z_to_bv 64 0 /\
       vkeep (gsw_out cx fp t s) W3 memT W3 mem2).
Proof.
  intros cx fp k ly3 S3 W3 regsT memT mdT t s x y L raw HB HJ Hfr Ht Hs R10 R11 R12 R2 R3 R4 R1 Hraw
    Hx1 Hx2 Hy Hy1 Hy2 HL Gx Gy.
  (* IMG_LO / IMG_HI are image B's opaque IMG_LO_B / IMG_TOP_B: give lia their values *)
  pose proof Hy1 as Hy1v. pose proof Hy2 as Hy2v. unfold IMG_LO in Hy1v. unfold IMG_HI in Hy2v.
  rewrite IMG_LO_B_val in Hy1v. rewrite IMG_TOP_B_val in Hy2v.
  destruct (gsw_bounds B MT cx fp k ly3 S3 W3 memT mdT t s HB HJ Hfr Ht Hs LAWS)
    as (Hal & Hsp0 & H47 & Hsp1 & Hsp32 & HF0 & HFc & HF32 & Ht0 & Htc & Hs0 & Hsc & HPB).
  unfold GE_STK, STK_LLVMFuzzerTestOneInput in Hsp0.
  destruct (gsw_base_facts B MT cx HB) as (HPRE & _ & _ & _).
  pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
  pose proof (proj1 HJ) as HAR.
  pose proof (@alloc_ceiling_value rc) as HAC.
  pose proof (sw_mbytes_ge (c_pl cx)) as Hsm.
  assert (Hrq : req_size (sw_mbytes (c_pl cx)) = sw_mbytes (c_pl cx)).
  { unfold req_size. replace (sw_mbytes (c_pl cx) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  assert (USP : spZ regsT = c_sp1 cx) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
  assert (Ho : (c_sp1 cx - spZ (c_regs cx)) mod 16 = 0).
  { pose proof (Z.div_mod (c_sp1 cx) 32 ltac:(lia)) as D1. pose proof (Z.div_mod (spZ (c_regs cx)) 16 ltac:(lia)) as D2.
    rewrite Hsp32 in D1. rewrite Hal in D2.
    replace (c_sp1 cx - spZ (c_regs cx)) with ((2 * (c_sp1 cx / 32) - spZ (c_regs cx) / 16) * 16) by lia.
    apply Z_mod_mult. }
  assert (Gxv : forall i, 0 <= i < 34 -> aview SEGS (w_H W3) memT (x + i) = Some (nth (Z.to_nat i) L 0)).
  { intros i Hi. destruct (garr8_nthZ SEGS _ x L i Gx ltac:(lia) ltac:(rewrite HL; lia)) as [Hv Hr].
    exact (aview_of_val_mem1 SEGS _ _ _ _ Hv Hr). }
  assert (Gyv : forall i, 0 <= i < 34 -> aview SEGS (w_H W3) memT (y + i) = Some (nth (Z.to_nat i) L 0)).
  { intros i Hi. destruct (garr8_nthZ SEGS _ y L i Gy ltac:(lia) ltac:(rewrite HL; lia)) as [Hv Hr].
    exact (aview_of_val_mem1 SEGS _ _ _ _ Hv Hr). }
  pose proof (ro_read_ok_glob SEGS B GRANT_GLOBS_B ly3 S3 W3 memT mdT y 34 y 34 HGL Hy HVIS HAR
    ltac:(lia) ltac:(lia) ltac:(lia) Hy1 Hy2) as [Hyra Hyhull].
  eapply SRr_mono.
  { eapply (aj_bcmp_at SEGS B LAWS pa_segs_low (SIGMA GS___interceptor_trampoline_bcmp) ABCMP W3 regsT memT
      GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GE_CID, fp)] ly3 S3 mdT k
      x y 34 (c_sp1 cx - spZ (c_regs cx)) raw HJ R10 R11 R12).
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - rewrite USP. lia.
    - exact Ho.
    - lia.
    - unfold ESTACK, GE_STK, STK_LLVMFuzzerTestOneInput. lia.
    - rewrite R3. exact Hgp.
    - rewrite R4. exact Htp.
    - exact R1.
    - exact Hraw.
    - intros a Ha. split.
      + replace a with (x + (a - x)) by lia. rewrite Gxv by lia. discriminate.
      + rewrite USP. unfold ESTACK. lia.
    - intros a Ha. split.
      + replace a with (y + (a - y)) by lia. rewrite Gyv by lia. discriminate.
      + rewrite USP. unfold ESTACK. lia.
    - intros a Ha. unfold ESTACK. lia.
    - intros a Ha. unfold ESTACK. lia.
    - apply (amem_range_of_block SEGS B LAWS ly3 S3 W3 memT mdT s _ x 34 HAR Hs); rewrite ?Hrq; lia.
    - unfold amem_range, kLowMemEnd. left. lia.
    - apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 memT mdT s _ x 34 HAR Hs); rewrite ?Hrq; lia.
    - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 memT mdT s _ x 34 HAR Hs); rewrite ?Hrq; lia.
    - exact Hyra.
    - intros _. exact Hyhull. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr2 & Hpres2).
  split; [reflexivity|]. exists regs2, mem2, md2.
  split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
  split.
  { rewrite Hv. change (Z_to_bv 64 0) with (w64 0). apply (proj2 Hcmp). intros i Hi.
    rewrite (Gxv i Hi), (Gyv i Hi). reflexivity. }
  intros a Ha. destruct (gsw_out_cases cx fp t s a HF0 HFc Ht0 Htc Hs0 Hsc HPB Ha) as [Hm | Hm];
    (apply Hfr2; [lia | unfold ESTACK; lia]).
Qed.

(* ---- 0x815d0 -> 0x81618: the two bcmp ---- *)
Lemma heads_main : GF (GIS_ga0 B MT) -> GF (GIS_rowex B MT).
Proof.
  intros HGA0 cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrm Hmo HI.
  destruct HI as (t & s & HBD & Hk & Hacc & HBLK & HROWS & H88 & H27 & H19).
  pose proof HBD as (Hpc & Hrv & Hsv & Hrom & Hfr & Hfc & (G2 & G8 & G9 & G3 & G4) & _).
  pose proof HBLK as (Hab & Hins & (Hint & _) & _ & _ & _ & _ & _ & _ & _ & _ & Hok & _).
  pose proof HROWS as (Hwant & HSW).
  destruct HIMG as (HTBL & HACKg & HMARKg & _ & _ & HACK1 & HACK2 & HMARK1 & HMARK2 & _).
  destruct (gsw_bounds B MT cx fp k ly3 S3 W3 (ms_mem ms3) md3 t s HB HJ Hfrm Hint Hins LAWS)
    as (Hal & Hsp0 & H47 & Hsp1 & Hsp32 & HF0 & HFc & HF32 & Ht0 & Htc & Hs0 & Hsc & HPB).
  unfold GE_STK, STK_LLVMFuzzerTestOneInput in Hsp0.
  pose proof (@alloc_ceiling_lt rc) as HACL.
  destruct (gsw_base_facts B MT cx HB) as (HPRE & HROD & _ & _).
  pose proof (sw_bytes_len cx t Hok Hwant) as Hswl.
  pose proof (length_sweep_ge (sw_base (c_pl cx)) (Z.to_nat (sw_in (c_pl cx))) (sw_vals (c_pl cx) t)) as Hsw170.
  fold (sw_bytes (c_pl cx) t) in Hsw170.
  rewrite (ms_shape ms3 (BASE + GPS_rowex) Hpc Hrv Hsv Hrom Hfr Hfc).
  (* run 1: 0x815d0 -> the call of the bcmp wrapper at 0x815e0 *)
  pose proof (plain_entry W3 (ms_regs ms3) (ms_mem ms3) GPS_rowex) as HS.
  pose proof (env_agree_Eimg (ms_regs ms3) []) as HAE.
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r)
    by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
  clear HE.
  assert (SHOK : sh_ok SEGS Bx3 [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  paj_run_tok RUN HS HJ SHOK Bsp3; [apply awr_ok_nil|].
  lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into ms1 end.
  pose proof (frame_of_nil_eq _ _ _ HF) as HM1. cbn [ms_mem mkst] in HM1.
  clear HF HFr HG.
  pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ (ms_regs ms3) [] HS HAE ltac:(vm_compute; reflexivity)) as P1.
  prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Ra.
  pmkst HS.
  pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD) as HROD1.
  eapply SRr_bind.
  { apply (gsw_bcmp cx fp k ly3 S3 W3 (ms_regs ms1) (ms_mem ms1) _ t s s (VAL (A_OBJ 4)) HEAD_ACK34z
      (Z_to_bv 64 (BASE + GPS_hd1)) HB HJ Hfrm Hint Hins).
    - (* `mv a0,s11` at 0x815dc *)
      rewrite Ra0, (ER 27%nat 27%bv eq_refl). exact H27.
    - (* the auipc/addi pair at 0x815d0/0x815d4 *)
      rewrite Ra1, (img_env_atomP E _ HEI) by (unfold A_TEXT, A_LIM; lia). reflexivity.
    - rewrite Ra2. reflexivity.
    - apg P1 (2%bv : bv 5) 2. exact G2.
    - apg P1 (3%bv : bv 5) 3. exact G3.
    - apg P1 (4%bv : bv 5) 4. exact G4.
    - rewrite Ra. reflexivity.
    - apply ret_ok_codeptr_v; [unfold GPS_hd1; lia | reflexivity].
    - lia.
    - lia.
    - exact HACKg.
    - exact HACK1.
    - exact HACK2.
    - reflexivity.
    - replace s with (s + Z.of_nat 0) at 1 by lia.
      apply (garr8_slice _ s (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)) HEAD_ACK34z 0); [| rewrite length_map; change (length HEAD_ACK34z) with 34%nat; lia |].
      + apply (garr8_vkeep (fun _ => True) W3 (ms_mem ms3) W3 (ms_mem ms1) s _ (vkeep_mem _ _ _ _ HM1)); [intros; exact I | exact HSW].
      + (* explicit arguments: unifying `sw_bytes` against `SWEEP` here exhausts memory *)
        intros j Hj. change (length HEAD_ACK34z) with 34%nat in Hj.
        exact (sweep_head_ack (sw_base (c_pl cx)) (Z.to_nat (sw_in (c_pl cx))) (sw_vals (c_pl cx) t) j Hj).
    - exact (proj1 (HTBL _ _ HROD1)). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hz2 & HK2).
  clear HS SHOK HROD1 Ra0 Ra1 Ra2 Ra.
  (* run 2: 0x815e4 -> the UBSan guard 0x815ec; `bnez a0` at 0x815e4 is not taken, as a0 is 0 *)
  pose proof (pin10_entry W3 regs2 mem2 GPS_hd1 Hz2) as HS.
  pose proof (env_agree_Eimg regs2 []) as HAE2.
  remember (Eimg (Ereg regs2 [])) as E2 eqn:HE.
  assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
  assert (ER2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs2 r)
    by (intros n r Hn; subst E2; apply ew_Eimg_Ereg_nat; exact Hn).
  clear HE.
  assert (P12 : aregs_preserved (ms_regs ms3) regs2) by (eapply aregs_preserved_trans; [exact P1 | exact HP2]).
  assert (E27 : ew E2 27 = Z_to_bv 64 s).
  { rewrite (ER2 27%nat 27%bv eq_refl). apg P12 (27%bv : bv 5) 27. exact H27. }
  assert (SHOK : sh_ok SEGS Bx3 [] E2 (mrestrict (w_H W3) mem2)) by constructor.
  paj_run_tok RUN HS HJ2 SHOK Bsp3; [apply awr_ok_nil|].
  lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msG end.
  pose proof (frame_of_nil_eq _ _ _ HF) as HMG. cbn [ms_mem mkst] in HMG.
  clear HF HFr HG.
  (* 0x815ec: `bltu a0,s11` with a0 = -137 goes to the trap 0x81f48 only if s + 136
     overflows; the sweep buffer is below the allocator's ceiling *)
  psrr_branch_tok RUN BR HS SHOK Bsp3.
  { exfalso. rewrite branch_ltu_U, (U_atom E2 27 s E27) in Hc by lia. rewrite U_SLit in Hc.
    lazymatch type of Hc with context [zcanon ?z] =>
      let v := eval vm_compute in (zcanon z) in change (zcanon z) with v in Hc end.
    apply Z.ltb_lt in Hc. lia. }
  clear Hc.
  (* run 2, continued: 0x815f0 -> the call of the bcmp wrapper at 0x81604 *)
  paj_run_tok RUN HS HJ2 SHOK Bsp3; [apply awr_ok_nil|].
  lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into ms2 end.
  pose proof (frame_of_nil_eq _ _ _ HF) as HM2. cbn [ms_mem mkst] in HM2.
  clear HF HFr HG.
  (* `li s2,34` at 0x81600 writes a callee-saved register: the others are kept. At a
     call the engine's state is a plain `st_ok` one, so the plain lemma reads it. *)
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regs2 [] [2; 3; 4; 8; 9; 19; 27]%bv HS HAE2
    ltac:(vm_compute; reflexivity)) as KF2. cbn [ms_regs restrict] in KF2.
  prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Ra.
  prreg HS (18%bv : bv 5) Rs2.
  pmkst HS.
  pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HROD) as HROD2.
  assert (KR2 : forall r : bv 5, In r [2; 3; 4; 8; 9; 19; 27]%bv -> getr (ms_regs ms2) r = getr (ms_regs ms3) r).
  { intros r Hr. rewrite (KF2 r Hr).
    destruct Hr as [<-|Hr]; [apg P12 (2%bv : bv 5) 2; reflexivity|].
    destruct Hr as [<-|Hr]; [apg P12 (3%bv : bv 5) 3; reflexivity|].
    destruct Hr as [<-|Hr]; [apg P12 (4%bv : bv 5) 4; reflexivity|].
    destruct Hr as [<-|Hr]; [apg P12 (8%bv : bv 5) 8; reflexivity|].
    destruct Hr as [<-|Hr]; [apg P12 (9%bv : bv 5) 9; reflexivity|].
    destruct Hr as [<-|Hr]; [apg P12 (19%bv : bv 5) 19; reflexivity|].
    destruct Hr as [<-|[]]. apg P12 (27%bv : bv 5) 27. reflexivity. }
  assert (VK2 : vkeep (gsw_out cx fp t s) W3 (ms_mem ms3) W3 (ms_mem ms2)).
  { eapply vkeep_trans; [apply vkeep_mem; exact HM1|]. eapply vkeep_trans; [exact HK2|].
    eapply vkeep_trans; apply vkeep_mem; [exact HMG | exact HM2]. }
  eapply SRr_bind.
  { apply (gsw_bcmp cx fp k ly3 S3 W3 (ms_regs ms2) (ms_mem ms2) _ t s (s + 136) (VAL (A_OBJ 5)) HEAD_MARK34z
      (Z_to_bv 64 (BASE + GPS_hd2)) HB HJ2 Hfrm Hint Hins).
    - (* `addi a0,s11,136` at 0x815f0 *)
      rewrite Ra0, E27. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    - (* the auipc/addi pair at 0x815f4/0x815f8 *)
      rewrite Ra1, (img_env_atomP E2 _ HEI2) by (unfold A_TEXT, A_LIM; lia). reflexivity.
    - rewrite Ra2. reflexivity.
    - rewrite (KR2 2%bv) by in_tac. exact G2.
    - rewrite (KR2 3%bv) by in_tac. exact G3.
    - rewrite (KR2 4%bv) by in_tac. exact G4.
    - rewrite Ra. reflexivity.
    - apply ret_ok_codeptr_v; [unfold GPS_hd2; lia | reflexivity].
    - lia.
    - lia.
    - exact HMARKg.
    - exact HMARK1.
    - exact HMARK2.
    - reflexivity.
    - change (s + 136) with (s + Z.of_nat 136).
      apply (garr8_slice _ s (map (fun b : byte => bv_unsigned b) (sw_bytes (c_pl cx) t)) HEAD_MARK34z 136); [| rewrite length_map; change (length HEAD_MARK34z) with 34%nat; lia |].
      + eapply garr8_vkeep; [exact VK2 | | exact HSW]. intros a Ha. right; right. rewrite length_map in Ha. lia.
      + intros j Hj. change (length HEAD_MARK34z) with 34%nat in Hj.
        exact (sweep_head_mark (sw_base (c_pl cx)) (Z.to_nat (sw_in (c_pl cx))) (sw_vals (c_pl cx) t) j Hj).
    - exact (proj1 (proj2 (HTBL _ _ HROD2))). }
  cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hz4 & HK4).
  clear HS SHOK HROD2 Ra0 Ra1 Ra2 Ra.
  (* run 3: 0x81608 -> 0x81618, the head of the first group-A loop; `bnez a0` at
     0x81608 is not taken, as a0 is 0 *)
  pose proof (pin10_entry W3 regs4 mem4 GPS_hd2 Hz4) as HS.
  pose proof (env_agree_Eimg regs4 []) as HAE4.
  remember (Eimg (Ereg regs4 [])) as E4 eqn:HE.
  assert (HEI4 : img_env VAL A_LIM E4) by (subst E4; apply Eimg_env).
  assert (ER4 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E4 n = getr regs4 r)
    by (intros n r Hn; subst E4; apply ew_Eimg_Ereg_nat; exact Hn).
  clear HE.
  assert (SHOK : sh_ok SEGS Bx3 [] E4 (mrestrict (w_H W3) mem4)) by constructor.
  paj_run_to_tok RUNTO HS HJ4 SHOK Bsp3 GPS_ga0; [apply awr_ok_nil|].
  lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into ms5 end.
  pose proof (frame_of_nil_eq _ _ _ HF) as HM5. cbn [ms_mem mkst] in HM5.
  clear HF HFr HG.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs4 [] [2; 3; 4; 8; 9; 18; 19; 27]%bv HS HAE4
    ltac:(vm_compute; reflexivity)) as KF. cbn [ms_regs restrict] in KF.
  prreg HS (26%bv : bv 5) R26. prreg HS (25%bv : bv 5) R25. prreg HS (20%bv : bv 5) R20.
  pmkst HS.
  assert (KR : forall r : bv 5, In r [2; 3; 4; 8; 9; 19; 27]%bv -> getr (ms_regs ms5) r = getr (ms_regs ms3) r).
  { intros r Hr.
    assert (Hr8 : In r [2; 3; 4; 8; 9; 18; 19; 27]%bv)
      by (clear - Hr; repeat (destruct Hr as [<-|Hr]; [in_tac|]); destruct Hr).
    rewrite (KF r Hr8). clear Hr8.
    rewrite <- (KR2 r Hr).
    destruct Hr as [<-|Hr]; [apg HP4 (2%bv : bv 5) 2; reflexivity|].
    destruct Hr as [<-|Hr]; [apg HP4 (3%bv : bv 5) 3; reflexivity|].
    destruct Hr as [<-|Hr]; [apg HP4 (4%bv : bv 5) 4; reflexivity|].
    destruct Hr as [<-|Hr]; [apg HP4 (8%bv : bv 5) 8; reflexivity|].
    destruct Hr as [<-|Hr]; [apg HP4 (9%bv : bv 5) 9; reflexivity|].
    destruct Hr as [<-|Hr]; [apg HP4 (19%bv : bv 5) 19; reflexivity|].
    destruct Hr as [<-|[]]. apg HP4 (27%bv : bv 5) 27. reflexivity. }
  assert (VK5 : vkeep (gsw_out cx fp t s) W3 (ms_mem ms3) W3 (ms_mem ms5)).
  { eapply vkeep_trans; [exact VK2|]. eapply vkeep_trans; [exact HK4|]. apply vkeep_mem. exact HM5. }
  apply (HGA0 cx fp k acc ly3 S3 W3 (mkst (ms_regs ms5) (Z_to_bv 64 (BASE + GPS_ga0)) (ms_mem ms5) (seg_rom SEGS)) _ HB HJ4 Hfrm Hmo).
  exists t, s, 0%nat.
  split.
  { apply (ge_body_move cx fp GPS_rowex GPS_ga0 W3 W3 ms3 (ms_regs ms5) (ms_mem ms5) GSH_a HBD).
    - eapply vkeep_sub; [| exact VK5]. intros a Ha. left. exact Ha.
    - lia.
    - apply KR; in_tac.
    - apply KR; in_tac.
    - apply KR; in_tac.
    - apply KR; in_tac.
    - apply KR; in_tac. }
  split; [exact Hk|]. split; [exact Hacc|].
  split.
  { eapply gsw_blk_move; [exact HBLK | reflexivity | exact VK5 | lia]. }
  split; [eapply gsw_rows_move; [exact Hok | exact HROWS | exact VK5]|].
  split.
  { unfold gslot in *. eapply rdword_vkeep; [exact VK5 | | exact H88].
    intros kk Hkk. left; left. lia. }
  split; [lia|].
  cbn [ms_regs mkst].
  split; [rewrite R26; reflexivity|].
  split.
  { rewrite R25, (ER4 27%nat 27%bv eq_refl). apg HP4 (27%bv : bv 5) 27.
    rewrite (KR2 27%bv) by in_tac. rewrite H27.
    unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia. }
  split.
  { rewrite (KF 18%bv) by in_tac. apg HP4 (18%bv : bv 5) 18. rewrite Rs2. reflexivity. }
  split; [rewrite R20; reflexivity|].
  split; [rewrite (KR 27%bv) by in_tac; exact H27|].
  rewrite (KR 19%bv) by in_tac. exact H19.
Qed.

End c.
End b.
End a.

Section z. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section zb.
Context {PI : PAImg grant_listing}.

Lemma gsw_seg_heads : forall (B : asyms) (MT : ameter_ops), @SEG_heads fx rc SK PI B MT.
Proof.
intros B MT RT HIMG NEXT.
destruct RT as (LAWS & TL & TLF & ML & MTL & MTF & AMALLOC4 & AFREE4 & ABCMP & HVIS & HGL & RO).
exact (heads_main (RO := RO) B MT LAWS ABCMP HVIS HGL HIMG NEXT).
Qed.

End zb.
End z.
