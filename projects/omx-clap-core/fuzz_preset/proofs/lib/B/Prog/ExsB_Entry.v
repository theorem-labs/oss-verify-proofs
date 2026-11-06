(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* RELOCATED B -> B' (h-pre-b3's #102 row, 2026-10-29): the walk of origin/cold/h-pre-b3-exstring-b 5f62ea0b5c45 (OLD
   pin f8f98a95, unstripped twin 3b5e1a09) moved to the #102 pin B' (asan-ubsan d663f82d7f48, unstripped twin
   c90d4fa54d43, facts 8f3e7e1a07f1) by alreloc c4338d099cfb8025 (cold/c-asan-tools d99acc3edd9), on int102 with the kit
   decff67d721f. ex_string, ex_hex4 and ex_utf8 have equal instruction words on B and B' up to pc-relative fields,
   and every pc-relative target names the same symbol + offset. Every address in this file, in a comment or in a term, is the B' image's; a mention of the record image
   f8f98a95 below names the donor's image. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (record f8f98a95), ex_string's ENTRY segment (B 0x84350 to the loop head
   B 0x8443c, or to B 0x847c0):
     addi sp,-144; sd ra, s0 .. s11 at 136 .. 40(sp); s0 = q; UBSan q & 7 (NOT taken: q mod 8 = 0); the shadow base
     through the GOT (A_OBJ 0 -> A_OBJ 12, PALib); q's shadow (report 0x84854 via 0x84850); s3 = in->p + 1 (p);
     UBSan 1 >= p (NOT taken); s1 = q + 8, s7 = its shadow address, q + 8's shadow (report 0x8485c via 0x84858);
     a1 = in->end; bgeu p,a1 -> 0x847c0 (CUT_FAIL: the text ends after the opening quote); q + 24's shadow (report
     0x84868 via 0x84868); s2 = scr; the constants of ESB / ESK, and 8(sp), 16(sp), 24(sp) (ES_C8, 0xd800, 0xdc00);
     then the loop head LH_AT at p = x0 + i0 + 1 with acc = [].
   Numerals: 0xec, 0x470 (DERIVED: cut offsets); 144 (LENGTH: frame); 32 (LENGTH: struct ex); atoms 45 .. 48 (DERIVED:
   the shadow base, in->p, in->end, the scratch pointer). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGcallW.
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

Definition ES_QR : YP09.region := YP09.mkRegion (Some 10%nat) 0 32 0 0
  [YP09.mkChunk 0 (CVal 8 (SOff 46 0)); YP09.mkChunk 8 (CVal 8 (SOff 47 0)); YP09.mkChunk 24 (CVal 8 (SOff 48 0))].
Definition ss_ent : sstate :=
  mkSS ES_PC sr_atoms [stack_region 144; got_regionP; bcell_regionP 45; ES_QR] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF (2 ^ 46) (2 ^ 47 - 32) 3);
              (45%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (46%nat, mkAF 4096 ES_CEIL 0); (47%nat, mkAF 4096 ES_CEIL 0);
              (48%nat, mkAF 4096 ES_CEIL 0)] [] []).
Definition es_SHent : list shent := [mkSHE 10 0 32].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis LAWS : AR_laws_x rsegs B ARx cf_head.
Hypothesis HHEAD : 8 <= cf_head.
Hypothesis PAL : PALib (L := B_prog_listing) (PI := PI_prog_B) B.

Lemma es_cut_entry : forall E, ES_PRE B ARx E -> LH_AT B ARx SK E (e_x0 E + e_i0 E + 1) ->
  SRr rsegs (e_W E) (cfg_at rsegs (es_pc 0) (e_regs E) (e_mem E) (e_md E)) (ES_POST B ARx SK E).
Proof.
intros E HP HLH.
pose proof (es_geom B ARx LAWS E HP) as G. unfold ES_GEOM in G. cbv zeta in G.
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
pose proof HP as HP0. unfold ES_PRE in HP0. cbv zeta in HP0.
destruct HP0 as ((HFN & HROD & HTOP & HRAC) & H10 & Vp & Ve & Vs & Hq8 & Hspq & Hqd & HWIN & HSRC & HINBx & Hlen3 & Hi0 &
  HWD & HINBs & Hdx & Hdq & HLED).
pose proof HFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow (PI := PI_prog_B) B PAL), (pal_cell (PI := PI_prog_B) B PAL) in Kgot.
rewrite (pal_cell (PI := PI_prog_B) B PAL) in Kcell.
assert (Eo0v : VAL (A_OBJ 0) = 0xa2850) by (vm_compute; reflexivity).
assert (Eo12v : VAL (A_OBJ 12) = 0xab6f8) by (vm_compute; reflexivity).
set (len := es_len E) in *.
remember (es_xE (e_regs E) (e_regs E) [w64 SHADOW_OFF; w64 (e_x0 E + e_i0 E); w64 (e_x0 E + len); w64 (e_scr E)])
  as Ex eqn:HEx.
assert (HEI : img_env VAL A_LIM Ex) by (rewrite HEx; apply es_xE_env).
assert (E2 : ew Ex 2 = Z_to_bv 64 (es_sp E)).
{ rewrite HEx, (es_xE_reg _ _ _ 2%bv 2) by reflexivity. unfold es_sp, spZ. symmetry. apply Z_to_bv_bv_unsigned. }
assert (E10 : ew Ex 10 = Z_to_bv 64 (e_q E)) by (rewrite HEx, (es_xE_reg _ _ _ 10%bv 10) by reflexivity; exact H10).
assert (E45 : ew Ex 45 = Z_to_bv 64 SHADOW_OFF) by (rewrite HEx, (es_xE_extra _ _ _ 0) by lia; reflexivity).
assert (E46 : ew Ex 46 = Z_to_bv 64 (e_x0 E + e_i0 E)) by (rewrite HEx, (es_xE_extra _ _ _ 1) by lia; reflexivity).
assert (E47 : ew Ex 47 = Z_to_bv 64 (e_x0 E + len)) by (rewrite HEx, (es_xE_extra _ _ _ 2) by lia; reflexivity).
assert (E48 : ew Ex 48 = Z_to_bv 64 (e_scr E)) by (rewrite HEx, (es_xE_extra _ _ _ 3) by lia; reflexivity).
assert (Eo0 : ew Ex (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (rewrite HEx; unfold es_xE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo12 : ew Ex (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (rewrite HEx; unfold es_xE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VB : forall n z, ew Ex n = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> base_val Ex (Some n) = z).
{ intros n z Hn Hz. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hz. }
assert (UA : forall n z, ew Ex n = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> bv_unsigned (ew Ex n) = z).
{ intros n z Hn Hz. rewrite Hn. apply unsigned_lit_small. exact Hz. }
assert (HRAq : range_addressable (aview rsegs (w_H (e_W E)) (e_mem E)) SHADOW_OFF (e_q E) 32).
{ apply (es_stk_ra B ARx LAWS _ _ _ (e_W E) (e_mem E) (e_md E) (e_q E) 32 HAR); lia. }
assert (HS : st_ok_pi rsegs VAL Ex ss_ent
  (restrict (w_H (e_W E)) (YK11.mkst (e_regs E) (Z_to_bv 64 (BASE + ES_PC)) (e_mem E) (YK11.seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_ent. apply (pa_entry_st_ok_full (fx := fx) (L := B_prog_listing) (PI := PI_prog_B)).
  - rewrite HEx. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold stack_region, got_regionP, bcell_regionP, ES_QR.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite (VB 2%nat (es_sp E) E2) by lia. split; [lia|]. split; [lia|]. split; [|constructor].
      intros a Ha. apply (apresent_writable rsegs). apply Hpres. rewrite es_stk_val. unfold es_sp in *. lia.
    + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eo0) by lia. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs Ex _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite Eo12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (8 * Z.of_N 8) with 64; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword rsegs (w_H (e_W E)) (e_mem E) _ _ Kgot).
    + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12) by lia. split; [lia|]. split; [lia|]. split; [intros a Ha; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs Ex _ (VAL (A_OBJ 12)) 0 8 (SOff 45 0) SHADOW_OFF);
        [cbn [sv_denot]; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword rsegs (w_H (e_W E)) (e_mem E) _ _ Kcell).
    + rewrite (VB 10%nat (e_q E) E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor]]].
      * apply (chunk_ok_val rsegs Ex _ (e_q E) 0 8 (SOff 46 0) (e_x0 E + e_i0 E));
          [cbn [sv_denot]; rewrite E46, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. exact Vp.
      * apply (chunk_ok_val rsegs Ex _ (e_q E) 8 8 (SOff 47 0) (e_x0 E + len));
          [cbn [sv_denot]; rewrite E47, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Ve].
      * apply (chunk_ok_val rsegs Ex _ (e_q E) 24 8 (SOff 48 0) (e_scr E));
          [cbn [sv_denot]; rewrite E48, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact Vs].
  - apply pairwise_disjoint_of_extents. unfold stack_region, got_regionP, bcell_regionP, ES_QR, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 10%nat (e_q E) E10) by lia. rewrite (VB 2%nat (es_sp E) E2) by lia.
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) Eo0) by lia. rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Eo12) by lia.
    rewrite Eo0v, Eo12v.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (UA 2%nat _ E2), (UA 10%nat _ E10), (UA 45%nat _ E45), (UA 46%nat _ E46), (UA 47%nat _ E47), (UA 48%nat _ E48)
      by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF, ES_CEIL. unfold es_sp in *. repeat split; lia. }
assert (HBx : U Ex (SOff 45 0) = SHADOW_OFF) by (rewrite (U_atom Ex 45 SHADOW_OFF E45) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok rsegs (SOff 45 0) es_SHent Ex (rdW (e_W E) (e_mem E))).
{ unfold es_SHent. constructor; [|constructor].
  apply (shent_ok_of_range rsegs (w_H (e_W E)) (e_mem E) Ex (SOff 45 0) 10 (e_q E) 32 (e_q E) 0 32 HRAq HBx);
    [rewrite (U_atom Ex 10 (e_q E) E10) by lia; reflexivity | lia | lia |].
  intros x Hx. unfold SHADOW_OFF. lia. }
pose proof (YCbqGcallW.ajournal_x_init_W (SK := SK) rsegs B (@prh_pst prh_img_B) ARx STK_ex_string (e_d E) (es_FP E)
  (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_regs E) (e_mem E) (e_md E) (e_ch E) HFN HWIN) as HJ.
pose (RUN := paj_run_x_inv (SK := SK) (PL := PL_prog_B) (PI := PI_prog_B) B prh_pst ARx LAWS _ (es_plaw E)).
pose (RUNTO := paj_run_to_x_inv (SK := SK) (PL := PL_prog_B) (PI := PI_prog_B) B prh_pst ARx LAWS _ (es_plaw E)).
pose (BR := paj_branch (PI := PI_prog_B)).
assert (HPM : es_P E (e_mem E)) by (intros H0; exact H0).
unfold cfg_at, w64. rewrite es_pc_eq, Z.add_0_r.
change (spZ (e_regs E)) with (es_sp E) in HJ.
paj_run_tok_x_inv RUN HS HJ SHOK HPM ES_SPAN.
{ es_awr ltac:(fun a Ha => rewrite (UA 2%nat (es_sp E) E2) in Ha by lia; apply es_awr_stk; unfold es_sp in *; lia). }
es_kept_of HFr (fun a => es_sp E - 144 <= a < es_sp E) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?(UA 2%nat (es_sp E) E2) in h by lia).
clear HFr. rename KEPT into MK.
es_envkeep HS Ex EWf.
assert (HPN : Forall (fun rz => getr (e_regs E) (fst rz) = Z_to_bv 64 (snd rz)) ([] : list (bv 5 * Z))) by constructor.
psrr_branch_tok RUN BR HS SHOK ES_SPAN.
- (* the text ends after the opening quote: return -1 *)
  es_Uhc Hc EWf. apply negb_true_iff, Z.ltb_ge in Hc.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM ES_SPAN.
  { es_awr ltac:(fun a Ha => rewrite (UA 2%nat (es_sp E) E2) in Ha by lia; apply es_awr_stk; unfold es_sp in *; lia). }
  es_kept_of HFr (fun a => es_sp E - 144 <= a < es_sp E) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?(UA 2%nat (es_sp E) E2) in h by lia).
  clear HFr.
  lazymatch goal with KEPT : forall a, _ -> _ -> aview ?sg ?H ?m' a = aview _ _ ?m a,
                      MK0 : forall a, _ -> _ -> aview _ _ ?m a = aview _ _ (e_mem E) a |- _ =>
    assert (MK3 : forall a, 0 <= a < 2 ^ 64 -> ~ (es_sp E - 144 <= a < es_sp E) ->
      aview sg H m' a = aview sg H (e_mem E) a) by (intros a Ha Hn; rewrite (KEPT a Ha Hn); exact (MK0 a Ha Hn)) end.
  pose proof (regs_kept_of_st_ok_pi (L := B_prog_listing) (PI := PI_prog_B) _ _ _ (e_regs E) _ ES_CS HS
    ltac:(es_agree_tac HEx) ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
  pose proof (regs_kept_of_st_ok_pi (L := B_prog_listing) (PI := PI_prog_B) _ _ _ (e_regs E) _ [1%bv] HS
    ltac:(es_agree_tac HEx) ltac:(vm_compute; reflexivity) 1%bv ltac:(left; reflexivity)) as HKR'.
  cbn [ms_regs restrict] in HKR'.
  es_reg0 HS (10%bv : bv 5) Ra0.
  eapply (paj_ret_at (PL := PL_prog_B) (PI := PI_prog_B) (e_W E) _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  assert (XRA : v_jalr (getr (ms_regs ms0) 1) 0 = getr (e_regs E) 1).
  { rewrite HKR'. unfold YK0s.ret_ok in Hra. exact Hra. }
  rewrite XRA.
  apply (es_finish B ARx SK E (e_ly E) (e_S E) (e_Hp E) (ms_regs ms0) (ms_mem ms0) _ 0 (-1)).
  + apply (ajournal_x_materialize (SK := SK) rsegs B (@prh_pst prh_img_B) ARx LAWS B_prog_segs_low). exact HJ.
  + intros a Ha Hn. apply MK3; [lia | unfold es_sp in *; lia].
  + apply es_aregs_of_kept. exact HKR.
  + reflexivity.
  + reflexivity.
  + tauto.
  + reflexivity.
  + exact HPM.
  + apply (es_ledger_same B ARx LAWS (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) (ms_mem ms0) _ _ _ _ _ _ _ HAR);
      [|exact HLED]. intros a Ha. apply MK3; [lia | unfold es_sp in *; lia].
  + rewrite Ra0. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
  + unfold ES_RES. rewrite exs_jr_decode.
    assert (Hxs : es_xs E = []).
    { unfold es_xs; apply skipn_all2. clear - Hc Hi0. unfold len, es_len in *.
      apply Nat2Z.inj_le. rewrite Nat2Z.inj_succ, Z2Nat.id by (exact (proj1 Hi0)). lia. }
    rewrite Hxs. split; [reflexivity|]. intros z Hz. apply MK3; [lia | unfold es_sp in *; lia].
- es_Uhc Hc EWf. apply negb_false_iff, Z.ltb_lt in Hc.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM ES_SPAN (ES_PC + 0xec).
  { es_awr ltac:(fun a Ha => rewrite (UA 2%nat (es_sp E) E2) in Ha by lia; apply es_awr_stk; unfold es_sp in *; lia). }
  es_kept_of HFr (fun a => es_sp E - 144 <= a < es_sp E) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?(UA 2%nat (es_sp E) E2) in h by lia).
  clear HFr.
  lazymatch goal with KEPT : forall a, _ -> _ -> aview ?sg ?H ?m' a = aview _ _ ?m a,
                      MK0 : forall a, _ -> _ -> aview _ _ ?m a = aview _ _ (e_mem E) a |- _ =>
    assert (MK3 : forall a, 0 <= a < 2 ^ 64 -> ~ (es_sp E - 144 <= a < es_sp E) ->
      aview sg H m' a = aview sg H (e_mem E) a) by (intros a Ha Hn; rewrite (KEPT a Ha Hn); exact (MK0 a Ha Hn)) end.
  clear EWf. es_envkeep HS Ex EWf.
  lazymatch type of HS with st_ok_pi _ _ ?Ef _ (restrict _ ?m) => rename m into msF end.
  pose proof (es_region_nth _ _ _ 0 _ HS eq_refl) as RF. cbn [ms_mem restrict] in RF.
  lazymatch type of HS with st_ok_pi _ _ ?Ef _ _ =>
    assert (U2f : bv_unsigned (ew Ef 2) = es_sp E) by (try (rewrite EWf by lia); exact (UA 2%nat _ E2 ltac:(unfold es_sp in *; lia))) end.
  pose proof (regs_kept_of_st_ok_pi (L := B_prog_listing) (PI := PI_prog_B) _ _ _ (e_regs E) _ [3; 4]%bv HS
    ltac:(es_agree_tac HEx) ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
  es_reg0 HS (2%bv : bv 5) R2'. es_reg0 HS (8%bv : bv 5) R8'. es_reg0 HS (9%bv : bv 5) R9'.
  es_reg0 HS (21%bv : bv 5) R21'. es_reg0 HS (22%bv : bv 5) R22'. es_reg0 HS (23%bv : bv 5) R23'.
  es_reg0 HS (24%bv : bv 5) R24'. es_reg0 HS (25%bv : bv 5) R25'. es_reg0 HS (26%bv : bv 5) R26'.
  es_reg0 HS (27%bv : bv 5) R27'. es_reg0 HS (14%bv : bv 5) R14'. es_reg0 HS (15%bv : bv 5) R15'.
  es_reg0 HS (16%bv : bv 5) R16'. es_reg0 HS (17%bv : bv 5) R17'. es_reg0 HS (5%bv : bv 5) R5'.
  es_reg0 HS (18%bv : bv 5) R18'. es_reg0 HS (19%bv : bv 5) R19'. es_reg0 HS (11%bv : bv 5) R11'.
  pmkst HS. es_pc_to 0xec.
  apply (HLH (e_ly E) (e_S E) (e_Hp E) (ms_regs msF) (ms_mem msF) _ 0 [] HP).
  + unfold ESB. cbv zeta. unfold es_SP.
    refine (conj HJ _). split.
    { intros a Ha Hn. apply MK3; [lia | unfold es_sp in *; lia]. }
    split; [intros a Ha; apply MK3; [lia | unfold es_sp in *; lia]|].
    split; [reflexivity|]. split; [reflexivity|]. split; [tauto|].
    split.
    { apply (es_ledger_same B ARx LAWS (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) (ms_mem msF) _ _ _ _ _ _ _ HAR);
        [|exact HLED]. intros a Ha. apply MK3; [lia | unfold es_sp in *; lia]. }
    split.
    { intros o r Hin. cbn [es_saved In] in Hin.
      repeat (destruct Hin as [Hq | Hin];
        [injection Hq as <- <-;
         lazymatch goal with |- val_mem _ _ (es_sp E - 144 + ?o) 8 (bv_unsigned (getr _ (Z_to_bv 5 ?r))) =>
           let n := eval vm_compute in (Z.to_nat r) in
           replace (es_sp E - 144 + o) with (es_sp E + (o - 144)) by lia;
           apply (es_field _ _ 2 (es_sp E) _ _ _ _ _ (o - 144) 8 (SOff n 0) _ RF U2f
             ltac:(cbn [In]; repeat (first [left; reflexivity | right])));
           [ rewrite es_den0; try (rewrite EWf by lia); rewrite HEx, (es_xE_reg _ _ _ (Z_to_bv 5 r) n) by reflexivity;
             symmetry; apply Z_to_bv_bv_unsigned
           | apply u64_range
           | cbn; lia ] end |]).
      destruct Hin. }
    split.
    { replace (es_sp E - 144 + 8) with (es_sp E + -136) by lia.
      apply (es_field _ _ 2 (es_sp E) _ _ _ _ _ (-136) 8 (SLit ES_C8) ES_C8 RF U2f
        ltac:(cbn [In]; repeat (first [left; reflexivity | right])) eq_refl ltac:(unfold ES_C8; cbn; lia) ltac:(cbn; lia)). }
    split.
    { replace (es_sp E - 144 + 16) with (es_sp E + -128) by lia.
      apply (es_field _ _ 2 (es_sp E) _ _ _ _ _ (-128) 8 (SLit 55296) 55296 RF U2f
        ltac:(cbn [In]; repeat (first [left; reflexivity | right])) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
    split.
    { replace (es_sp E - 144 + 24) with (es_sp E + -120) by lia.
      apply (es_field _ _ 2 (es_sp E) _ _ _ _ _ (-120) 8 (SLit 56320) 56320 RF U2f
        ltac:(cbn [In]; repeat (first [left; reflexivity | right])) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
    split; [rewrite R2', (es_den_off _ 2 (-144) (es_sp E) ltac:(first [exact E2 | rewrite EWf by lia; exact E2])) by (unfold es_sp in *; lia);
      reflexivity|].
    split; [rewrite R8', es_den0; try (rewrite EWf by lia); exact E10|].
    split; [rewrite R9', (es_den_off _ 10 8 (e_q E) ltac:(first [exact E10 | rewrite EWf by lia; exact E10])) by lia; reflexivity|].
    split; [rewrite R21', (es_denot_shx _ 10 45 (e_q E) SHADOW_OFF ltac:(first [exact E10 | rewrite EWf by lia; exact E10])
      ltac:(first [exact E45 | rewrite EWf by lia; exact E45])) by (unfold SHADOW_OFF; lia); reflexivity|].
    split; [rewrite R22', es_den0; try (rewrite EWf by lia); exact E45|].
    split; [rewrite R23', (es_denot_shx_off _ 10 45 8 (e_q E) SHADOW_OFF ltac:(first [exact E10 | rewrite EWf by lia; exact E10])
      ltac:(first [exact E45 | rewrite EWf by lia; exact E45])) by (unfold SHADOW_OFF; lia); reflexivity|].
    split; [rewrite R24'; reflexivity|]. split; [rewrite R25'; reflexivity|].
    split; [rewrite R26'; reflexivity|]. split; [rewrite R27'; reflexivity|].
    split; [exact (HKR 3%bv ltac:(cbn; tauto))|]. split; [exact (HKR 4%bv ltac:(cbn; tauto))|].
    split; [reflexivity | exact HPM].
  + unfold ESK. rewrite R14', R15', R16', R17', R5'. cbn [sv_denot].
    split; [unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity|]. repeat split; reflexivity.
  + unfold ESG. cbn [length app]. split; [unfold len in *; lia|]. split; [lia|].
    unfold es_xs, es_rest. replace (e_x0 E + e_i0 E + 1 - e_x0 E) with (Z.succ (e_i0 E)) by lia.
    rewrite Z2Nat.inj_succ by (exact (proj1 Hi0)).
    rewrite exs_emit_nil. reflexivity.
  + exact Hc.
  + apply garr8_nil.
  + rewrite R18', es_den0. try (rewrite EWf by lia). rewrite E48. cbn [length Z.of_nat]. rewrite Z.add_0_r. reflexivity.
  + rewrite R19', (es_den_off _ 46 1 (e_x0 E + e_i0 E) ltac:(first [exact E46 | rewrite EWf by lia; exact E46])) by lia. reflexivity.
  + rewrite R11', es_den0. try (rewrite EWf by lia). exact E47.
Qed.
End c.
