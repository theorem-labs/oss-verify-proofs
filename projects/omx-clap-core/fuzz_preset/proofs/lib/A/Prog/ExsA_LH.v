(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image A' (#102 pin asan 1be0f53d96cb), ex_string's LOOP HEAD cut (ExsA_Stmt.v
   LH_AT):
     A 0x84110 p's shadow (report 0x844c4 via the slow block 0x84390); lbu a0,0(s4) (the byte c at p);
     beq c,34 -> 0x84434 (CUT_QUOTE); bltu c,32 -> 0x8442c (CUT_FAIL, a control byte); addi s5,s4,1;
     bne c,92 -> 0x8424c: o's shadow (report 0x844d0 via 0x8439c), addi a1,s3,1, sb c,0(s3), j 0x84374,
       mv s3,a1 (CUT_CONT at p + 1, acc ++ [c]);
     c = 92: bgeu p + 1, s6 -> 0x8442c (CUT_FAIL: a backslash at the end), else 0x84138 (CUT_ESC at p).
   One engine run per segment from a fresh state: p's byte in a read-only region (atom 45), the output byte o (atom 19)
   writable, s9 .. s11 and a3 .. a6 pinned to their literals (ESB, ESK), the shadow entries of p and o from the live
   blocks' shadow (ExsA_Lib.v es_cut_mem). The report calls are not reachable inside the runs.
   PORTED from lib/B/Prog/ExsB_LH.v (a Theorem Labs lane's B' walk): the same runs, the same branch tree, the same leaf proofs.
   CHANGED for A': the pcs; no UBSan edge (B' tested o + 1 < 2 before each store); p / o / the next p / in->end / the
   shadow base are s4 / s3 / s5 / s6 / s7 (atoms 20 / 19 / 21 / 22 / 23; B': s3 / s2 / s4 / a1 / s6); the pinned
   constants are s9 .. s11 = 34, 32, 92 and a3 .. a6 = 101, 91, 113, 114 (B': s8 .. s11 with s11 = 2, a4 .. a7, t0); the
   plain-byte leaf ends at CONT with s3 = o + 1 (B': a0).
   Numerals: 0xdc, 0x104, 0x344, 0x3f8, 0x400 (DERIVED: cut offsets); 34, 32, 92, 101, 91, 113, 114 (WORD: the
   literals ESB / ESK name); atom 45 (DERIVED: the byte c); 255 (LENGTH: byte range). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Img Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgA ExsA_Stmt ExsA_Lib ExsA_Sym ExsA_Exit ExsA_Cont.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExsB_Model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
#[local] Notation VAL := (@pa_val _ A_prog_listing PI_prog_A).
#[local] Notation BASE := (@pa_val _ A_prog_listing PI_prog_A A_TEXT).

Definition ES_RT1 : YP09.region := YP09.mkRegion (Some 20%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 45 0))].
Definition es_pins : list (bv 5 * Z) :=
  [(25%bv, 34); (26%bv, 32); (27%bv, 92); (13%bv, 101); (14%bv, 91); (15%bv, 113); (16%bv, 114)].
Definition ss_lh : sstate :=
  mkSS (ES_PC + 0xdc) (es_pin_sr es_pins sr_atoms) [ES_RT1; ES_RO] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (19%nat, mkAF 4096 ES_CEIL 0); (20%nat, mkAF 4096 ES_CEIL 0);
              (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (45%nat, mkAF 0 255 0)] [] []).
Definition es_SHl : list shent := [mkSHE 20 0 1; mkSHE 19 0 1].
(* the registers kept as atoms by every LH segment *)
Definition ES_KEPT_L : list (bv 5) := [2; 3; 4; 8; 18; 19; 20; 22; 23; 24]%bv.
(* the leaves that store a byte also move o + 1 into s3 *)
Definition ES_KEPT_S : list (bv 5) := [2; 3; 4; 8; 18; 20; 22; 23; 24]%bv.

(* one LH / ESC segment run to a stuck branch (es_lh_tok) or to a stop pc (es_lh_run): the write premise (only the
   output byte o = U19's value, in the scratch block b m), the kept bytes chained into MK (outside o, from the cut's
   memc), the token atoms' agreement EWf at the new environment *)
Ltac es_lh_awr :=
  es_awr ltac:(fun a Ha =>
    match goal with U19 : bv_unsigned (ew _ 19) = _ |- _ => rewrite ?U19 in Ha end;
    match goal with Hbm' : In (?b, ?m) _, Hbs : ?b <= e_scr _, Hsm : e_scr _ + es_len _ + 1 <= ?b + ?m |- _ =>
      apply (es_awr_scr _ _ _ _ _ b m a Hbm' Hbs Hsm); lia end).
Ltac es_lh_after HS Ex memc o U18 MK EWf :=
  lazymatch goal with HFr : frame_of _ _ _ _ |- _ =>
    es_kept_of HFr (fun a => a = o) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U18 in h); clear HFr end;
  lazymatch goal with KEPT : forall a, _ -> _ -> aview ?sg ?H ?m' a = aview _ _ ?m a |- _ =>
    let MK2 := fresh "MK" in
    assert (MK2 : forall a, 0 <= a < 2 ^ 64 -> a <> o -> aview sg H m' a = aview sg H memc a)
      by (intros a Ha Hn; rewrite (KEPT a Ha Hn); exact (MK a Ha Hn));
    clear KEPT MK; rename MK2 into MK end;
  clear EWf; es_envkeep HS Ex EWf.
Ltac es_lh_tok RUN HS HJ SHOK HPM Ex memc o U18 MK EWf :=
  paj_run_tok_x_inv RUN HS HJ SHOK HPM ES_SPAN; [es_lh_awr | es_lh_after HS Ex memc o U18 MK EWf].
Ltac es_lh_run RUNTO HS HJ SHOK HPM stop Ex memc o U18 MK EWf :=
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM ES_SPAN stop; [es_lh_awr | es_lh_after HS Ex memc o U18 MK EWf].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis LAWS : AR_laws_x rsegs B ARx cf_head.
Hypothesis HHEAD : 8 <= cf_head.

Lemma es_cut_lh : forall E p, CUT_CONT B ARx SK E (p + 1) -> CUT_ESC B ARx SK E p -> LH_AT B ARx SK E p.
Proof.
intros E p HCT HESC. unfold LH_AT. intros lyc Sc Hpc regs memc mdc k acc HP HB HK HEG Hpe GA R19 R20.
pose proof (es_geom B ARx LAWS E HP) as G. unfold ES_GEOM in G. cbv zeta in G.
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
pose proof HB as (HJ & HWIN & HQP & HHp & HAB & HRK & HLED & HSAV & HC0 & HC8 & HC16 & HC24 & R2 & R8 & R18 & R22 &
  R23 & R24 & R25 & R26 & R27 & R3 & R4 & HSc & HMN).
pose proof HK as (K13 & K14 & K15 & K16).
pose proof (es_cur_ar B ARx SK E lyc Sc Hpc regs memc mdc k HB) as HAR.
pose proof HEG as (HG1 & HG2 & HG3).
destruct (es_cut_mem B ARx SK LAWS E lyc Sc Hpc regs memc mdc k HHEAD HP HB) as
  (HRAx & HRAs & HTX & (bx & mx & Hbxm & Hbxs & Hxm & Hxhd) & (b & m & Hbm' & Hbs & Hsm & Hhd)).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hbm') as (B1 & B2 & B3 & Bapp & Bpres & _).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hbxm) as (Bx1 & Bx2 & Bx3 & Bxapp & Bxpres & _).
assert (Hreq : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
assert (Hreqx : mx <= req_size mx) by (unfold req_size; destruct (Z.eqb_spec mx 0); lia).
unfold es_SP in *.
set (o := e_scr E + Z.of_nat (length acc)) in *.
assert (Ho : e_scr E <= o < e_scr E + es_len E + 1) by (unfold o; lia).
set (c := es_byte E p) in *.
destruct (HTX p ltac:(lia)) as [Vc Rc].
remember (es_xE regs (e_regs E) [w64 c]) as Ex eqn:HEx.
assert (HEI : img_env VAL A_LIM Ex) by (rewrite HEx; apply es_xE_env).
assert (E2 : ew Ex 2 = Z_to_bv 64 (es_sp E - 144)) by (rewrite HEx, (es_xE_reg _ _ _ 2%bv 2) by reflexivity; exact R2).
assert (E19 : ew Ex 19 = Z_to_bv 64 o) by (rewrite HEx, (es_xE_reg _ _ _ 19%bv 19) by reflexivity; exact R19).
assert (E20 : ew Ex 20 = Z_to_bv 64 p) by (rewrite HEx, (es_xE_reg _ _ _ 20%bv 20) by reflexivity; exact R20).
assert (E22 : ew Ex 22 = Z_to_bv 64 (e_x0 E + es_len E)) by (rewrite HEx, (es_xE_reg _ _ _ 22%bv 22) by reflexivity; exact R22).
assert (E23 : ew Ex 23 = Z_to_bv 64 SHADOW_OFF) by (rewrite HEx, (es_xE_reg _ _ _ 23%bv 23) by reflexivity; exact R23).
assert (E45 : ew Ex 45 = Z_to_bv 64 c) by (rewrite HEx, (es_xE_extra _ _ _ 0) by lia; reflexivity).
assert (U2 : bv_unsigned (ew Ex 2) = es_sp E - 144) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew Ex 19) = o) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew Ex 20) = p) by (rewrite E20; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew Ex 23) = SHADOW_OFF) by (rewrite E23; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U45 : bv_unsigned (ew Ex 45) = c) by (rewrite E45; apply unsigned_lit_small; lia).
assert (HBx : U Ex (SOff 23 0) = SHADOW_OFF) by (rewrite (U_atom Ex 23 SHADOW_OFF E23) by (unfold SHADOW_OFF; lia); reflexivity).
assert (HPN : Forall (fun rz => getr regs (fst rz) = Z_to_bv 64 (snd rz)) es_pins)
  by (repeat constructor; cbn [fst snd]; assumption).
assert (HS : st_ok_pi rsegs VAL Ex ss_lh
  (restrict (w_H (e_W E)) (YK11.mkst regs (Z_to_bv 64 (BASE + (ES_PC + 0xdc))) memc (YK11.seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_lh. apply (pa_entry_st_ok_full (fx := fx) (L := A_prog_listing) (PI := PI_prog_A)).
  - apply es_regs_ok_pins; [rewrite HEx; apply regs_ok_Eimg_Ereg|].
    unfold es_pins; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      (split; [intros X; apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X | assumption]).
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold region_ok, ES_RT1. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U20. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs Ex _ p 0 1 (SOff 45 0) c);
        [cbn [sv_denot]; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Vc.
    + unfold region_ok, ES_RO. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U19. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros oo Hoo. apply (apresent_writable rsegs). apply (Bpres (o + oo)). lia.
  - apply pairwise_disjoint_of_extents. unfold extent_of_region, ES_RT1, ES_RO.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U19, U20.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; unfold es_len in *; lia.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U19, U20, U23, U45. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF, ES_CEIL. repeat split; lia. }
assert (SHOK : sh_ok rsegs (SOff 23 0) es_SHl Ex (rdW (e_W E) memc)).
{ unfold es_SHl. constructor; [|constructor; [|constructor]].
  - apply (shent_ok_of_range rsegs (w_H (e_W E)) memc Ex (SOff 23 0) 20 (e_x0 E) (es_len E) p 0 1 HRAx HBx);
      [rewrite (U_atom Ex 20 p E20) by lia; reflexivity | lia | lia |].
    intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Bxapp. unfold SHADOW_OFF. lia.
  - apply (shent_ok_of_range rsegs (w_H (e_W E)) memc Ex (SOff 23 0) 19 (e_scr E) (es_len E + 1) o 0 1 HRAs HBx);
      [rewrite (U_atom Ex 19 o E19) by lia; reflexivity | lia | lia |].
    intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Bapp. unfold SHADOW_OFF. lia. }
pose (RUN := paj_run_x_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS _ (es_plaw E)).
pose (RUNTO := paj_run_to_x_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS _ (es_plaw E)).
pose (BR := paj_branch (PI := PI_prog_A)).
assert (HPM : es_P E memc) by exact HMN.
unfold cfg_at, w64. rewrite es_pc_eq.
paj_run_tok_x_inv RUN HS HJ SHOK HPM ES_SPAN.
{ es_lh_awr. }
es_kept_of HFr (fun a => a = o) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U19 in h).
clear HF HG HFr. rename KEPT into MK.
es_envkeep HS Ex EWf.
psrr_branch_tok RUN BR HS SHOK ES_SPAN.
- (* c = 34: the closing quote *)
  es_Uhc Hc EWf. apply Z.eqb_eq in Hc.
  es_lh_run RUNTO HS HJ SHOK HPM (ES_PC + 0x400) Ex memc o U19 MK EWf.
  es_leaf_regs HS HEx regs ES_KEPT_L es_pins HPN HR.
  pmkst HS. es_pc_to 0x400.
  apply (es_cut_quote B ARx SK LAWS HHEAD E lyc Sc Hpc _ _ _ k p acc HP).
  + apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ (fun a => a = o) HHEAD HP HB HJ);
      [intros a ->; left; unfold es_len in *; lia | exact MK | exact HR | exact HPM].
  + exact HEG.
  + apply (es_garr8_kept (w_H (e_W E)) memc); [|exact GA]. intros a Ha. apply MK; [lia|]. unfold o. lia.
  + exact Hpe.
  + exact Hc.
  + rewrite (HKR 19%bv ltac:(cbn; tauto)). exact R19.
  + rewrite (HKR 20%bv ltac:(cbn; tauto)). exact R20.
- es_Uhc Hc EWf. apply Z.eqb_neq in Hc. rename Hc into Hc34.
  es_lh_tok RUN HS HJ SHOK HPM Ex memc o U19 MK EWf.
  psrr_branch_tok RUN BR HS SHOK ES_SPAN.
  + (* c < 32: a control byte *)
    es_Uhc Hc EWf. apply Z.ltb_lt in Hc.
    es_lh_run RUNTO HS HJ SHOK HPM (ES_PC + 0x3f8) Ex memc o U19 MK EWf.
    es_leaf_regs HS HEx regs ES_KEPT_L es_pins HPN HR.
    pmkst HS. es_pc_to 0x3f8.
    apply (es_cut_fail B ARx SK LAWS E lyc Sc Hpc _ _ _ k HP).
    * apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ (fun a => a = o) HHEAD HP HB HJ);
        [intros a ->; left; unfold es_len in *; lia | exact MK | exact HR | exact HPM].
    * apply (es_fail_of E p acc HEG). rewrite (es_rest_cons E p) by lia. apply exs_dec_ctl. exact Hc.
  + es_Uhc Hc EWf. apply Z.ltb_ge in Hc. rename Hc into Hc32.
    es_lh_tok RUN HS HJ SHOK HPM Ex memc o U19 MK EWf.
    psrr_branch_tok RUN BR HS SHOK ES_SPAN.
    * (* c <> 92: a plain byte, stored *)
      es_Uhc Hc EWf. apply negb_true_iff, Z.eqb_neq in Hc.
      es_lh_run RUNTO HS HJ SHOK HPM (ES_PC + 0x344) Ex memc o U19 MK EWf.
      es_leaf_regs HS HEx regs ES_KEPT_S es_pins HPN HR.
      pose proof (es_region_nth _ _ _ 1 _ HS eq_refl) as RO. cbn [ms_mem restrict] in RO.
      pose proof (es_field _ _ 19 o _ _ _ _ _ 0 1 (SOff 45 0) c RO ltac:(rewrite EWf by lia; exact U19)
        ltac:(left; reflexivity) ltac:(rewrite es_den0, EWf by lia; exact E45) ltac:(cbn; lia) ltac:(cbn; lia)) as VO.
      rewrite Z.add_0_r in VO. clear RO.
      es_reg0 HS (19%bv : bv 5) R19'. es_reg0 HS (21%bv : bv 5) R21'.
      pmkst HS. es_pc_to 0x344.
      destruct (es_store_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ acc c HHEAD HP HB HJ MK HR HPM
        ltac:(unfold es_len in *; lia) GA VO Rc) as [HB' GA'].
      apply (HCT lyc Sc Hpc _ _ _ k (acc ++ [c]) HP HB').
      -- unfold ESK. rewrite (HPK 13%bv), (HPK 14%bv), (HPK 15%bv), (HPK 16%bv) by (cbn; tauto). exact HK.
      -- apply (es_esg_step E p acc 1 [c] HEG ltac:(lia) ltac:(cbn; lia)).
         rewrite (es_rest_cons E p) by lia. fold c. apply exs_dec_plain; [exact Hc32 | exact Hc34 | exact Hc].
      -- exact GA'.
      -- rewrite R19', (es_den_off _ 19 1 o ltac:(rewrite EWf by lia; exact E19)) by lia.
         rewrite length_app. cbn [length]. unfold w64, o. f_equal. lia.
      -- rewrite R21', (es_den_off _ 20 1 p ltac:(rewrite EWf by lia; exact E20)) by lia. reflexivity.
    * (* c = 92: a backslash *)
      es_Uhc Hc EWf. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hc92.
      es_lh_tok RUN HS HJ SHOK HPM Ex memc o U19 MK EWf.
      psrr_branch_tok RUN BR HS SHOK ES_SPAN.
      -- (* p + 1 >= in->end: the text ends after the backslash *)
         es_Uhc Hc EWf. apply negb_true_iff, Z.ltb_ge in Hc.
         es_lh_run RUNTO HS HJ SHOK HPM (ES_PC + 0x3f8) Ex memc o U19 MK EWf.
         es_leaf_regs HS HEx regs ES_KEPT_L es_pins HPN HR.
         pmkst HS. es_pc_to 0x3f8.
         apply (es_cut_fail B ARx SK LAWS E lyc Sc Hpc _ _ _ k HP).
         ++ apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ (fun a => a = o) HHEAD HP HB HJ);
              [intros a ->; left; unfold es_len in *; lia | exact MK | exact HR | exact HPM].
         ++ apply (es_fail_of E p acc HEG). rewrite (es_rest_cons E p) by lia. rewrite (es_rest_end E (p + 1)) by lia.
            fold c. rewrite Hc92. exact exs_dec_bs_end.
      -- es_Uhc Hc EWf. apply negb_false_iff, Z.ltb_lt in Hc.
         es_lh_run RUNTO HS HJ SHOK HPM (ES_PC + 0x104) Ex memc o U19 MK EWf.
         es_leaf_regs HS HEx regs ES_KEPT_L es_pins HPN HR.
         es_reg0 HS (21%bv : bv 5) R21'.
         pmkst HS. es_pc_to 0x104.
         apply (HESC lyc Sc Hpc _ _ _ k acc HP).
         ++ apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ (fun a => a = o) HHEAD HP HB HJ);
              [intros a ->; left; unfold es_len in *; lia | exact MK | exact HR | exact HPM].
         ++ unfold ESK. rewrite (HPK 13%bv), (HPK 14%bv), (HPK 15%bv), (HPK 16%bv) by (cbn; tauto). exact HK.
         ++ exact HEG.
         ++ apply (es_garr8_kept (w_H (e_W E)) memc); [|exact GA]. intros a Ha. apply MK; [lia|]. unfold o. lia.
         ++ exact Hc.
         ++ exact Hc92.
         ++ rewrite (HKR 19%bv ltac:(cbn; tauto)). exact R19.
         ++ rewrite (HKR 20%bv ltac:(cbn; tauto)). exact R20.
         ++ rewrite R21', (es_den_off _ 20 1 p ltac:(rewrite EWf by lia; exact E20)) by lia. reflexivity.
Qed.
End c.
