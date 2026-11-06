(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* RELOCATED B -> B' (h-pre-b3's #102 row, 2026-10-29): the walk of origin/cold/h-pre-b3-exstring-b 5f62ea0b5c45 (OLD
   pin f8f98a95, unstripped twin 3b5e1a09) moved to the #102 pin B' (asan-ubsan d663f82d7f48, unstripped twin
   c90d4fa54d43, facts 8f3e7e1a07f1) by alreloc c4338d099cfb8025 (cold/c-asan-tools d99acc3edd9), on int102 with the kit
   decff67d721f. ex_string, ex_hex4 and ex_utf8 have equal instruction words on B and B' up to pc-relative fields,
   and every pc-relative target names the same symbol + offset. Every address in this file, in a comment or in a term, is the B' image's; a mention of the record image
   f8f98a95 below names the donor's image. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (record f8f98a95), ex_string's ESCAPE cut (ExsB_Stmt.v CUT_ESC):
     B 0x84464 beq s4,-1 (UBSan, NOT taken: p + 1 < 2 ^ 47); p + 1's shadow (report 0x84880 via 0x8473c);
     lbu a0,0(s4) (the escape byte e); s4 = p + 2; the dispatch B 0x84480-0x84498 / 0x845dc-0x84644:
     backslash-backslash, -b, -quote, -slash, -f, -n, -r, -t store 92 8 34 47 12 10 13 9 at o (UBSan s2 + 1 < 2 NOT taken, o's shadow,
     reports 0x84888 .. 0x848c0 via 0x84748 .. 0x8479c not reached) and go to B 0x84708 (CUT_CONT at p + 2);
     `\u` goes to B 0x8449c (CUT_HEX1 at p); any other e to B 0x847c0 (CUT_FAIL: the grammar's escape table refuses).
   One engine run per segment from a fresh state: p's byte in a read-only region (atom 45), the output byte o (atom 18)
   writable, s8 .. s11 and a4 .. a7, t0 pinned to their literals (ESB, ESK), the shadow entries of p and o from the
   live blocks' shadow (ExsB_Lib.v es_cut_mem). The report calls and the UBSan trap are not reachable inside the runs.
   Numerals: 0x114, 0x14c, 0x3b8, 0x470 (DERIVED: cut offsets); 34, 32, 92, 2, 101, 91, 113, 114, -1 (WORD: the
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB ExsB_Stmt ExsB_Model ExsB_Lib ExsB_Sym ExsB_Exit ExsB_Cont ExsB_LH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PI_prog_B).
#[local] Notation VAL := (@pa_val _ B_prog_listing PI_prog_B).
#[local] Notation BASE := (@pa_val _ B_prog_listing PI_prog_B A_TEXT).

Definition ES_RE1 : YP09.region := YP09.mkRegion (Some 20%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 45 0))].
Definition ss_esc : sstate :=
  mkSS (ES_PC + 0x114) (es_pin_sr es_pins sr_atoms) [ES_RE1; ES_RO] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (18%nat, mkAF 4096 ES_CEIL 0); (19%nat, mkAF 4096 ES_CEIL 0);
              (20%nat, mkAF 4096 ES_CEIL 0); (22%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (45%nat, mkAF 0 255 0)] [] []).
Definition es_SHe : list shent := [mkSHE 20 0 1; mkSHE 18 0 1].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis LAWS : AR_laws_x rsegs B ARx cf_head.
Hypothesis HHEAD : 8 <= cf_head.

Lemma es_cut_esc : forall E p, CUT_CONT B ARx SK E (p + 2) -> CUT_HEX1 B ARx SK E p -> CUT_ESC B ARx SK E p.
Proof.
intros E p HCT HHX. unfold CUT_ESC. intros lyc Sc Hpc regs memc mdc k acc HP HB HK HEG GA Hp1 Hc92 R18 R19 R20 R11.
pose proof (es_geom B ARx LAWS E HP) as G. unfold ES_GEOM in G. cbv zeta in G.
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
pose proof HB as (HJ & HWIN & HQP & HHp & HAB & HRK & HLED & HSAV & HC8 & HC16 & HC24 & R2 & R8 & R9 & R21 & R22 &
  R23 & R24 & R25 & R26 & R27 & R3 & R4 & HSc & HMN).
pose proof HK as (K14 & K15 & K16 & K17 & K5).
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
set (c := es_byte E (p + 1)) in *.
destruct (HTX (p + 1) ltac:(lia)) as [Vc Rc].
remember (es_xE regs (e_regs E) [w64 c]) as Ex eqn:HEx.
assert (HEI : img_env VAL A_LIM Ex) by (rewrite HEx; apply es_xE_env).
assert (E2 : ew Ex 2 = Z_to_bv 64 (es_sp E - 144)) by (rewrite HEx, (es_xE_reg _ _ _ 2%bv 2) by reflexivity; exact R2).
assert (E11 : ew Ex 11 = Z_to_bv 64 (e_x0 E + es_len E)) by (rewrite HEx, (es_xE_reg _ _ _ 11%bv 11) by reflexivity; exact R11).
assert (E18 : ew Ex 18 = Z_to_bv 64 o) by (rewrite HEx, (es_xE_reg _ _ _ 18%bv 18) by reflexivity; exact R18).
assert (E19 : ew Ex 19 = Z_to_bv 64 p) by (rewrite HEx, (es_xE_reg _ _ _ 19%bv 19) by reflexivity; exact R19).
assert (E20 : ew Ex 20 = Z_to_bv 64 (p + 1)) by (rewrite HEx, (es_xE_reg _ _ _ 20%bv 20) by reflexivity; exact R20).
assert (E22 : ew Ex 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite HEx, (es_xE_reg _ _ _ 22%bv 22) by reflexivity; exact R22).
assert (E45 : ew Ex 45 = Z_to_bv 64 c) by (rewrite HEx, (es_xE_extra _ _ _ 0) by lia; reflexivity).
assert (U2 : bv_unsigned (ew Ex 2) = es_sp E - 144) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew Ex 18) = o) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew Ex 19) = p) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew Ex 20) = p + 1) by (rewrite E20; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew Ex 22) = SHADOW_OFF) by (rewrite E22; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U45 : bv_unsigned (ew Ex 45) = c) by (rewrite E45; apply unsigned_lit_small; lia).
assert (HBx : U Ex (SOff 22 0) = SHADOW_OFF) by (rewrite (U_atom Ex 22 SHADOW_OFF E22) by (unfold SHADOW_OFF; lia); reflexivity).
assert (HPN : Forall (fun rz => getr regs (fst rz) = Z_to_bv 64 (snd rz)) es_pins)
  by (repeat constructor; cbn [fst snd]; assumption).
assert (HS : st_ok_pi rsegs VAL Ex ss_esc
  (restrict (w_H (e_W E)) (YK11.mkst regs (Z_to_bv 64 (BASE + (ES_PC + 0x114))) memc (YK11.seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_esc. apply (pa_entry_st_ok_full (fx := fx) (L := B_prog_listing) (PI := PI_prog_B)).
  - apply es_regs_ok_pins; [rewrite HEx; apply regs_ok_Eimg_Ereg|].
    unfold es_pins; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      (split; [intros X; apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X | assumption]).
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold region_ok, ES_RE1. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U20. split; [lia|]. split; [lia|]. split; [intros oo Hoo; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs Ex _ (p + 1) 0 1 (SOff 45 0) c);
        [cbn [sv_denot]; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Vc.
    + unfold region_ok, ES_RO. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U18. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros oo Hoo. apply (apresent_writable rsegs). apply (Bpres (o + oo)). lia.
  - apply pairwise_disjoint_of_extents. unfold extent_of_region, ES_RE1, ES_RO.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U18, U20.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; unfold es_len in *; lia.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U18, U19, U20, U22, U45. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF, ES_CEIL. repeat split; lia. }
assert (SHOK : sh_ok rsegs (SOff 22 0) es_SHe Ex (rdW (e_W E) memc)).
{ unfold es_SHe. constructor; [|constructor; [|constructor]].
  - apply (shent_ok_of_range rsegs (w_H (e_W E)) memc Ex (SOff 22 0) 20 (e_x0 E) (es_len E) (p + 1) 0 1 HRAx HBx);
      [rewrite (U_atom Ex 20 (p + 1) E20) by lia; reflexivity | lia | lia |].
    intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Bxapp. unfold SHADOW_OFF. lia.
  - apply (shent_ok_of_range rsegs (w_H (e_W E)) memc Ex (SOff 22 0) 18 (e_scr E) (es_len E + 1) o 0 1 HRAs HBx);
      [rewrite (U_atom Ex 18 o E18) by lia; reflexivity | lia | lia |].
    intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Bapp. unfold SHADOW_OFF. lia. }
pose (RUN := paj_run_x_inv (SK := SK) (PL := PL_prog_B) (PI := PI_prog_B) B prh_pst ARx LAWS _ (es_plaw E)).
pose (RUNTO := paj_run_to_x_inv (SK := SK) (PL := PL_prog_B) (PI := PI_prog_B) B prh_pst ARx LAWS _ (es_plaw E)).
pose (BR := paj_branch (PI := PI_prog_B)).
assert (HPM : es_P E memc) by exact HMN.
unfold cfg_at, w64. rewrite es_pc_eq.

paj_run_tok_x_inv RUN HS HJ SHOK HPM ES_SPAN.
{ es_lh_awr. }
es_kept_of HFr (fun a => a = o) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U18 in h).
clear HF HG HFr. rename KEPT into MK.
es_envkeep HS Ex EWf.
(* B 0x84480 bge a5,a0: e <= 101 *)
psrr_branch_tok RUN BR HS SHOK ES_SPAN.
- rewrite (es_branch_ge_vals _ _ _ 101 c (es_U_lit _ 101 ltac:(lia)) ltac:(rewrite (es_U_off _ _ 45 0 c EWf ltac:(lia) E45 ltac:(lia) ltac:(lia)); lia)) in Hc by lia. apply negb_true_iff, Z.ltb_ge in Hc. rename Hc into Hle101.
  es_lh_tok RUN HS HJ SHOK HPM Ex memc o U18 MK EWf.
  (* B 0x845dc blt a6,a0: 91 < e *)
  psrr_branch_tok RUN BR HS SHOK ES_SPAN.
  + rewrite (es_branch_lt_vals _ _ _ 91 c (es_U_lit _ 91 ltac:(lia)) ltac:(rewrite (es_U_off _ _ 45 0 c EWf ltac:(lia) E45 ltac:(lia) ltac:(lia)); lia)) in Hc by lia. apply Z.ltb_lt in Hc. rename Hc into Hgt91.
    es_lh_tok RUN HS HJ SHOK HPM Ex memc o U18 MK EWf.
    (* B 0x8460c beq a0,s10: e = 92 *)
    psrr_branch_tok RUN BR HS SHOK ES_SPAN.
    * es_Uhc Hc EWf. apply Z.eqb_eq in Hc.      (* `\\` *)
      es_lh_run RUNTO HS HJ SHOK HPM (ES_PC + 0x3b8) Ex memc o U18 MK EWf.
      es_leaf_regs HS HEx regs ES_KEPT_S es_pins HPN HR.
      pose proof (es_region_nth _ _ _ 1 _ HS eq_refl) as RO. cbn [ms_mem restrict] in RO.
      pose proof (es_field _ _ 18 o _ _ _ _ _ 0 1 (SLit 92) 92 RO ltac:(rewrite EWf by lia; exact U18)
        ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VO.
      rewrite Z.add_0_r in VO. clear RO.
      es_reg0 HS (10%bv : bv 5) R10'. es_reg0 HS (20%bv : bv 5) R20'.
      pmkst HS. es_pc_to 0x3b8.
      destruct (es_store_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ acc 92 HHEAD HP HB HJ MK HR HPM
        ltac:(unfold es_len in *; lia) GA VO ltac:(lia)) as [HB' GA'].
      apply (HCT lyc Sc Hpc _ _ _ k (acc ++ [92]) HP HB').
      -- unfold ESK. rewrite (HPK 14%bv), (HPK 15%bv), (HPK 16%bv), (HPK 17%bv), (HPK 5%bv) by (cbn; tauto). exact HK.
      -- apply (es_esg_step E p acc 2 [92] HEG ltac:(lia) ltac:(cbn; lia)).
         rewrite (es_rest_esc E p) by lia. rewrite Hc92. fold c. rewrite exs_dec_esc by lia.
         replace c with 92 by lia. reflexivity.
      -- exact GA'.
      -- rewrite R10', (es_den_off _ 18 1 o ltac:(rewrite EWf by lia; exact E18)) by lia.
         rewrite length_app. cbn [length]. unfold w64, o. f_equal. lia.
      -- rewrite R20', (es_den_off _ 19 2 p ltac:(rewrite EWf by lia; exact E19)) by lia. reflexivity.
    * es_Uhc Hc EWf. apply Z.eqb_neq in Hc. rename Hc into Hn92.
      es_lh_tok RUN HS HJ SHOK HPM Ex memc o U18 MK EWf.
      (* B 0x84614 bne a0,a1 (98) *)
      psrr_branch_tok RUN BR HS SHOK ES_SPAN.
      -- es_Uhc Hc EWf. apply negb_true_iff, Z.eqb_neq in Hc.      (* a bad escape in 92 .. 101 *)
         es_lh_run RUNTO HS HJ SHOK HPM (ES_PC + 0x470) Ex memc o U18 MK EWf.
         es_leaf_regs HS HEx regs ES_KEPT_S es_pins HPN HR.
         pmkst HS. es_pc_to 0x470.
         apply (es_cut_fail B ARx SK LAWS E lyc Sc Hpc _ _ _ k HP).
         ++ apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ (fun a => a = o) HHEAD HP HB HJ);
              [intros a ->; left; unfold es_len in *; lia | exact MK | exact HR | exact HPM].
         ++ apply (es_fail_of E p acc HEG). rewrite (es_rest_esc E p) by lia. rewrite Hc92. fold c.
            rewrite exs_dec_esc by lia. rewrite exs_escape_none by lia. reflexivity.
      -- es_Uhc Hc EWf. apply negb_false_iff, Z.eqb_eq in Hc.      (* `\b` *)
         es_lh_run RUNTO HS HJ SHOK HPM (ES_PC + 0x3b8) Ex memc o U18 MK EWf.
         es_leaf_regs HS HEx regs ES_KEPT_S es_pins HPN HR.
         pose proof (es_region_nth _ _ _ 1 _ HS eq_refl) as RO. cbn [ms_mem restrict] in RO.
         pose proof (es_field _ _ 18 o _ _ _ _ _ 0 1 (SLit 8) 8 RO ltac:(rewrite EWf by lia; exact U18)
           ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VO.
         rewrite Z.add_0_r in VO. clear RO.
         es_reg0 HS (10%bv : bv 5) R10'. es_reg0 HS (20%bv : bv 5) R20'.
         pmkst HS. es_pc_to 0x3b8.
         destruct (es_store_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ acc 8 HHEAD HP HB HJ MK HR HPM
           ltac:(unfold es_len in *; lia) GA VO ltac:(lia)) as [HB' GA'].
         apply (HCT lyc Sc Hpc _ _ _ k (acc ++ [8]) HP HB').
         ++ unfold ESK. rewrite (HPK 14%bv), (HPK 15%bv), (HPK 16%bv), (HPK 17%bv), (HPK 5%bv) by (cbn; tauto). exact HK.
         ++ apply (es_esg_step E p acc 2 [8] HEG ltac:(lia) ltac:(cbn; lia)).
            rewrite (es_rest_esc E p) by lia. rewrite Hc92. fold c. rewrite exs_dec_esc by lia.
            replace c with 98 by lia. reflexivity.
         ++ exact GA'.
         ++ rewrite R10', (es_den_off _ 18 1 o ltac:(rewrite EWf by lia; exact E18)) by lia.
            rewrite length_app. cbn [length]. unfold w64, o. f_equal. lia.
         ++ rewrite R20', (es_den_off _ 19 2 p ltac:(rewrite EWf by lia; exact E19)) by lia. reflexivity.
  + rewrite (es_branch_lt_vals _ _ _ 91 c (es_U_lit _ 91 ltac:(lia)) ltac:(rewrite (es_U_off _ _ 45 0 c EWf ltac:(lia) E45 ltac:(lia) ltac:(lia)); lia)) in Hc by lia. apply Z.ltb_ge in Hc. rename Hc into Hle91.
    es_lh_tok RUN HS HJ SHOK HPM Ex memc o U18 MK EWf.
    (* B 0x845e0 beq a0,s8: e = 34 *)
    psrr_branch_tok RUN BR HS SHOK ES_SPAN.
    * es_Uhc Hc EWf. apply Z.eqb_eq in Hc.      (* backslash-quote *)
      es_lh_run RUNTO HS HJ SHOK HPM (ES_PC + 0x3b8) Ex memc o U18 MK EWf.
      es_leaf_regs HS HEx regs ES_KEPT_S es_pins HPN HR.
      pose proof (es_region_nth _ _ _ 1 _ HS eq_refl) as RO. cbn [ms_mem restrict] in RO.
      pose proof (es_field _ _ 18 o _ _ _ _ _ 0 1 (SLit 34) 34 RO ltac:(rewrite EWf by lia; exact U18)
        ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VO.
      rewrite Z.add_0_r in VO. clear RO.
      es_reg0 HS (10%bv : bv 5) R10'. es_reg0 HS (20%bv : bv 5) R20'.
      pmkst HS. es_pc_to 0x3b8.
      destruct (es_store_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ acc 34 HHEAD HP HB HJ MK HR HPM
        ltac:(unfold es_len in *; lia) GA VO ltac:(lia)) as [HB' GA'].
      apply (HCT lyc Sc Hpc _ _ _ k (acc ++ [34]) HP HB').
      -- unfold ESK. rewrite (HPK 14%bv), (HPK 15%bv), (HPK 16%bv), (HPK 17%bv), (HPK 5%bv) by (cbn; tauto). exact HK.
      -- apply (es_esg_step E p acc 2 [34] HEG ltac:(lia) ltac:(cbn; lia)).
         rewrite (es_rest_esc E p) by lia. rewrite Hc92. fold c. rewrite exs_dec_esc by lia.
         replace c with 34 by lia. reflexivity.
      -- exact GA'.
      -- rewrite R10', (es_den_off _ 18 1 o ltac:(rewrite EWf by lia; exact E18)) by lia.
         rewrite length_app. cbn [length]. unfold w64, o. f_equal. lia.
      -- rewrite R20', (es_den_off _ 19 2 p ltac:(rewrite EWf by lia; exact E19)) by lia. reflexivity.
    * es_Uhc Hc EWf. apply Z.eqb_neq in Hc. rename Hc into Hn34.
      es_lh_tok RUN HS HJ SHOK HPM Ex memc o U18 MK EWf.
      (* B 0x845e8 bne a0,a1 (47) *)
      psrr_branch_tok RUN BR HS SHOK ES_SPAN.
      -- es_Uhc Hc EWf. apply negb_true_iff, Z.eqb_neq in Hc.      (* a bad escape below 92 *)
         es_lh_run RUNTO HS HJ SHOK HPM (ES_PC + 0x470) Ex memc o U18 MK EWf.
         es_leaf_regs HS HEx regs ES_KEPT_S es_pins HPN HR.
         pmkst HS. es_pc_to 0x470.
         apply (es_cut_fail B ARx SK LAWS E lyc Sc Hpc _ _ _ k HP).
         ++ apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ (fun a => a = o) HHEAD HP HB HJ);
              [intros a ->; left; unfold es_len in *; lia | exact MK | exact HR | exact HPM].
         ++ apply (es_fail_of E p acc HEG). rewrite (es_rest_esc E p) by lia. rewrite Hc92. fold c.
            rewrite exs_dec_esc by lia. rewrite exs_escape_none by lia. reflexivity.
      -- es_Uhc Hc EWf. apply negb_false_iff, Z.eqb_eq in Hc.      (* `\/` *)
         es_lh_run RUNTO HS HJ SHOK HPM (ES_PC + 0x3b8) Ex memc o U18 MK EWf.
         es_leaf_regs HS HEx regs ES_KEPT_S es_pins HPN HR.
         pose proof (es_region_nth _ _ _ 1 _ HS eq_refl) as RO. cbn [ms_mem restrict] in RO.
         pose proof (es_field _ _ 18 o _ _ _ _ _ 0 1 (SLit 47) 47 RO ltac:(rewrite EWf by lia; exact U18)
           ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VO.
         rewrite Z.add_0_r in VO. clear RO.
         es_reg0 HS (10%bv : bv 5) R10'. es_reg0 HS (20%bv : bv 5) R20'.
         pmkst HS. es_pc_to 0x3b8.
         destruct (es_store_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ acc 47 HHEAD HP HB HJ MK HR HPM
           ltac:(unfold es_len in *; lia) GA VO ltac:(lia)) as [HB' GA'].
         apply (HCT lyc Sc Hpc _ _ _ k (acc ++ [47]) HP HB').
         ++ unfold ESK. rewrite (HPK 14%bv), (HPK 15%bv), (HPK 16%bv), (HPK 17%bv), (HPK 5%bv) by (cbn; tauto). exact HK.
         ++ apply (es_esg_step E p acc 2 [47] HEG ltac:(lia) ltac:(cbn; lia)).
            rewrite (es_rest_esc E p) by lia. rewrite Hc92. fold c. rewrite exs_dec_esc by lia.
            replace c with 47 by lia. reflexivity.
         ++ exact GA'.
         ++ rewrite R10', (es_den_off _ 18 1 o ltac:(rewrite EWf by lia; exact E18)) by lia.
            rewrite length_app. cbn [length]. unfold w64, o. f_equal. lia.
         ++ rewrite R20', (es_den_off _ 19 2 p ltac:(rewrite EWf by lia; exact E19)) by lia. reflexivity.
- rewrite (es_branch_ge_vals _ _ _ 101 c (es_U_lit _ 101 ltac:(lia)) ltac:(rewrite (es_U_off _ _ 45 0 c EWf ltac:(lia) E45 ltac:(lia) ltac:(lia)); lia)) in Hc by lia. apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hgt101.
  es_lh_tok RUN HS HJ SHOK HPM Ex memc o U18 MK EWf.
  (* B 0x84484 bge a7,a0: e <= 113 *)
  psrr_branch_tok RUN BR HS SHOK ES_SPAN.
  + rewrite (es_branch_ge_vals _ _ _ 113 c (es_U_lit _ 113 ltac:(lia)) ltac:(rewrite (es_U_off _ _ 45 0 c EWf ltac:(lia) E45 ltac:(lia) ltac:(lia)); lia)) in Hc by lia. apply negb_true_iff, Z.ltb_ge in Hc. rename Hc into Hle113.
    es_lh_tok RUN HS HJ SHOK HPM Ex memc o U18 MK EWf.
    (* B 0x8463c beq a0,a1 (102) *)
    psrr_branch_tok RUN BR HS SHOK ES_SPAN.
    * es_Uhc Hc EWf. apply Z.eqb_eq in Hc.      (* `\f` *)
      es_lh_run RUNTO HS HJ SHOK HPM (ES_PC + 0x3b8) Ex memc o U18 MK EWf.
      es_leaf_regs HS HEx regs ES_KEPT_S es_pins HPN HR.
      pose proof (es_region_nth _ _ _ 1 _ HS eq_refl) as RO. cbn [ms_mem restrict] in RO.
      pose proof (es_field _ _ 18 o _ _ _ _ _ 0 1 (SLit 12) 12 RO ltac:(rewrite EWf by lia; exact U18)
        ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VO.
      rewrite Z.add_0_r in VO. clear RO.
      es_reg0 HS (10%bv : bv 5) R10'. es_reg0 HS (20%bv : bv 5) R20'.
      pmkst HS. es_pc_to 0x3b8.
      destruct (es_store_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ acc 12 HHEAD HP HB HJ MK HR HPM
        ltac:(unfold es_len in *; lia) GA VO ltac:(lia)) as [HB' GA'].
      apply (HCT lyc Sc Hpc _ _ _ k (acc ++ [12]) HP HB').
      -- unfold ESK. rewrite (HPK 14%bv), (HPK 15%bv), (HPK 16%bv), (HPK 17%bv), (HPK 5%bv) by (cbn; tauto). exact HK.
      -- apply (es_esg_step E p acc 2 [12] HEG ltac:(lia) ltac:(cbn; lia)).
         rewrite (es_rest_esc E p) by lia. rewrite Hc92. fold c. rewrite exs_dec_esc by lia.
         replace c with 102 by lia. reflexivity.
      -- exact GA'.
      -- rewrite R10', (es_den_off _ 18 1 o ltac:(rewrite EWf by lia; exact E18)) by lia.
         rewrite length_app. cbn [length]. unfold w64, o. f_equal. lia.
      -- rewrite R20', (es_den_off _ 19 2 p ltac:(rewrite EWf by lia; exact E19)) by lia. reflexivity.
    * es_Uhc Hc EWf. apply Z.eqb_neq in Hc. rename Hc into Hn102.
      es_lh_tok RUN HS HJ SHOK HPM Ex memc o U18 MK EWf.
      (* B 0x84644 bne a0,a1 (110) *)
      psrr_branch_tok RUN BR HS SHOK ES_SPAN.
      -- es_Uhc Hc EWf. apply negb_true_iff, Z.eqb_neq in Hc.      (* a bad escape in 102 .. 113 *)
         es_lh_run RUNTO HS HJ SHOK HPM (ES_PC + 0x470) Ex memc o U18 MK EWf.
         es_leaf_regs HS HEx regs ES_KEPT_S es_pins HPN HR.
         pmkst HS. es_pc_to 0x470.
         apply (es_cut_fail B ARx SK LAWS E lyc Sc Hpc _ _ _ k HP).
         ++ apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ (fun a => a = o) HHEAD HP HB HJ);
              [intros a ->; left; unfold es_len in *; lia | exact MK | exact HR | exact HPM].
         ++ apply (es_fail_of E p acc HEG). rewrite (es_rest_esc E p) by lia. rewrite Hc92. fold c.
            rewrite exs_dec_esc by lia. rewrite exs_escape_none by lia. reflexivity.
      -- es_Uhc Hc EWf. apply negb_false_iff, Z.eqb_eq in Hc.      (* `\n` *)
         es_lh_run RUNTO HS HJ SHOK HPM (ES_PC + 0x3b8) Ex memc o U18 MK EWf.
         es_leaf_regs HS HEx regs ES_KEPT_S es_pins HPN HR.
         pose proof (es_region_nth _ _ _ 1 _ HS eq_refl) as RO. cbn [ms_mem restrict] in RO.
         pose proof (es_field _ _ 18 o _ _ _ _ _ 0 1 (SLit 10) 10 RO ltac:(rewrite EWf by lia; exact U18)
           ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VO.
         rewrite Z.add_0_r in VO. clear RO.
         es_reg0 HS (10%bv : bv 5) R10'. es_reg0 HS (20%bv : bv 5) R20'.
         pmkst HS. es_pc_to 0x3b8.
         destruct (es_store_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ acc 10 HHEAD HP HB HJ MK HR HPM
           ltac:(unfold es_len in *; lia) GA VO ltac:(lia)) as [HB' GA'].
         apply (HCT lyc Sc Hpc _ _ _ k (acc ++ [10]) HP HB').
         ++ unfold ESK. rewrite (HPK 14%bv), (HPK 15%bv), (HPK 16%bv), (HPK 17%bv), (HPK 5%bv) by (cbn; tauto). exact HK.
         ++ apply (es_esg_step E p acc 2 [10] HEG ltac:(lia) ltac:(cbn; lia)).
            rewrite (es_rest_esc E p) by lia. rewrite Hc92. fold c. rewrite exs_dec_esc by lia.
            replace c with 110 by lia. reflexivity.
         ++ exact GA'.
         ++ rewrite R10', (es_den_off _ 18 1 o ltac:(rewrite EWf by lia; exact E18)) by lia.
            rewrite length_app. cbn [length]. unfold w64, o. f_equal. lia.
         ++ rewrite R20', (es_den_off _ 19 2 p ltac:(rewrite EWf by lia; exact E19)) by lia. reflexivity.
  + rewrite (es_branch_ge_vals _ _ _ 113 c (es_U_lit _ 113 ltac:(lia)) ltac:(rewrite (es_U_off _ _ 45 0 c EWf ltac:(lia) E45 ltac:(lia) ltac:(lia)); lia)) in Hc by lia. apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hgt113.
    es_lh_tok RUN HS HJ SHOK HPM Ex memc o U18 MK EWf.
    (* B 0x84488 beq a0,t0 (114) *)
    psrr_branch_tok RUN BR HS SHOK ES_SPAN.
    * es_Uhc Hc EWf. apply Z.eqb_eq in Hc.      (* `\r` *)
      es_lh_run RUNTO HS HJ SHOK HPM (ES_PC + 0x3b8) Ex memc o U18 MK EWf.
      es_leaf_regs HS HEx regs ES_KEPT_S es_pins HPN HR.
      pose proof (es_region_nth _ _ _ 1 _ HS eq_refl) as RO. cbn [ms_mem restrict] in RO.
      pose proof (es_field _ _ 18 o _ _ _ _ _ 0 1 (SLit 13) 13 RO ltac:(rewrite EWf by lia; exact U18)
        ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VO.
      rewrite Z.add_0_r in VO. clear RO.
      es_reg0 HS (10%bv : bv 5) R10'. es_reg0 HS (20%bv : bv 5) R20'.
      pmkst HS. es_pc_to 0x3b8.
      destruct (es_store_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ acc 13 HHEAD HP HB HJ MK HR HPM
        ltac:(unfold es_len in *; lia) GA VO ltac:(lia)) as [HB' GA'].
      apply (HCT lyc Sc Hpc _ _ _ k (acc ++ [13]) HP HB').
      -- unfold ESK. rewrite (HPK 14%bv), (HPK 15%bv), (HPK 16%bv), (HPK 17%bv), (HPK 5%bv) by (cbn; tauto). exact HK.
      -- apply (es_esg_step E p acc 2 [13] HEG ltac:(lia) ltac:(cbn; lia)).
         rewrite (es_rest_esc E p) by lia. rewrite Hc92. fold c. rewrite exs_dec_esc by lia.
         replace c with 114 by lia. reflexivity.
      -- exact GA'.
      -- rewrite R10', (es_den_off _ 18 1 o ltac:(rewrite EWf by lia; exact E18)) by lia.
         rewrite length_app. cbn [length]. unfold w64, o. f_equal. lia.
      -- rewrite R20', (es_den_off _ 19 2 p ltac:(rewrite EWf by lia; exact E19)) by lia. reflexivity.
    * es_Uhc Hc EWf. apply Z.eqb_neq in Hc. rename Hc into Hn114.
      es_lh_tok RUN HS HJ SHOK HPM Ex memc o U18 MK EWf.
      (* B 0x84490 beq a0,a2 (116) *)
      psrr_branch_tok RUN BR HS SHOK ES_SPAN.
      -- es_Uhc Hc EWf. apply Z.eqb_eq in Hc.      (* `\t` *)
         es_lh_run RUNTO HS HJ SHOK HPM (ES_PC + 0x3b8) Ex memc o U18 MK EWf.
         es_leaf_regs HS HEx regs ES_KEPT_S es_pins HPN HR.
         pose proof (es_region_nth _ _ _ 1 _ HS eq_refl) as RO. cbn [ms_mem restrict] in RO.
         pose proof (es_field _ _ 18 o _ _ _ _ _ 0 1 (SLit 9) 9 RO ltac:(rewrite EWf by lia; exact U18)
           ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VO.
         rewrite Z.add_0_r in VO. clear RO.
         es_reg0 HS (10%bv : bv 5) R10'. es_reg0 HS (20%bv : bv 5) R20'.
         pmkst HS. es_pc_to 0x3b8.
         destruct (es_store_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ acc 9 HHEAD HP HB HJ MK HR HPM
           ltac:(unfold es_len in *; lia) GA VO ltac:(lia)) as [HB' GA'].
         apply (HCT lyc Sc Hpc _ _ _ k (acc ++ [9]) HP HB').
         ++ unfold ESK. rewrite (HPK 14%bv), (HPK 15%bv), (HPK 16%bv), (HPK 17%bv), (HPK 5%bv) by (cbn; tauto). exact HK.
         ++ apply (es_esg_step E p acc 2 [9] HEG ltac:(lia) ltac:(cbn; lia)).
            rewrite (es_rest_esc E p) by lia. rewrite Hc92. fold c. rewrite exs_dec_esc by lia.
            replace c with 116 by lia. reflexivity.
         ++ exact GA'.
         ++ rewrite R10', (es_den_off _ 18 1 o ltac:(rewrite EWf by lia; exact E18)) by lia.
            rewrite length_app. cbn [length]. unfold w64, o. f_equal. lia.
         ++ rewrite R20', (es_den_off _ 19 2 p ltac:(rewrite EWf by lia; exact E19)) by lia. reflexivity.
      -- es_Uhc Hc EWf. apply Z.eqb_neq in Hc. rename Hc into Hn116.
         es_lh_tok RUN HS HJ SHOK HPM Ex memc o U18 MK EWf.
         (* B 0x84498 bne a0,a2 (117) *)
         psrr_branch_tok RUN BR HS SHOK ES_SPAN.
         ++ es_Uhc Hc EWf. apply negb_true_iff, Z.eqb_neq in Hc.      (* a bad escape above 113 *)
            es_lh_run RUNTO HS HJ SHOK HPM (ES_PC + 0x470) Ex memc o U18 MK EWf.
            es_leaf_regs HS HEx regs ES_KEPT_S es_pins HPN HR.
            pmkst HS. es_pc_to 0x470.
            apply (es_cut_fail B ARx SK LAWS E lyc Sc Hpc _ _ _ k HP).
            ** apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ (fun a => a = o) HHEAD HP HB HJ);
                 [intros a ->; left; unfold es_len in *; lia | exact MK | exact HR | exact HPM].
            ** apply (es_fail_of E p acc HEG). rewrite (es_rest_esc E p) by lia. rewrite Hc92. fold c.
               rewrite exs_dec_esc by lia. rewrite exs_escape_none by lia. reflexivity.
         ++ es_Uhc Hc EWf. apply negb_false_iff, Z.eqb_eq in Hc. (* `\u`: HEX1 *)
            es_lh_run RUNTO HS HJ SHOK HPM (ES_PC + 0x14c) Ex memc o U18 MK EWf.
            es_leaf_regs HS HEx regs ES_KEPT_L es_pins HPN HR.
            es_reg0 HS (20%bv : bv 5) R20'.
            pmkst HS. es_pc_to 0x14c.
            apply (HHX lyc Sc Hpc _ _ _ k acc HP).
            ** apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ (fun a => a = o) HHEAD HP HB HJ);
                 [intros a ->; left; unfold es_len in *; lia | exact MK | exact HR | exact HPM].
            ** exact HEG.
            ** apply (es_garr8_kept (w_H (e_W E)) memc); [|exact GA]. intros a Ha. apply MK; [lia|]. unfold o. lia.
            ** exact Hp1.
            ** exact Hc92.
            ** exact Hc.
            ** rewrite (HKR 18%bv ltac:(cbn; tauto)). exact R18.
            ** rewrite (HKR 19%bv ltac:(cbn; tauto)). exact R19.
            ** rewrite R20', (es_den_off _ 19 2 p ltac:(rewrite EWf by lia; exact E19)) by lia. reflexivity.
            ** rewrite (HKR 11%bv ltac:(cbn; tauto)). exact R11.
Qed.
End c.
