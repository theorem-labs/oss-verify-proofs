(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image A' (#102 pin asan 1be0f53d96cb), ex_string after its second ex_hex4 call
   (ExsA_Stmt.v CUT_HEX2R, A 0x841f8):
     bnez a0 -> 0x8442c (CUT_FAIL: not four hex digits); lw a0,32(sp) (lo); lui a1,0xffff2; addw a1,a0,a1;
     li a2,-1024; bltu a1,a2 -> 0x8442c (CUT_FAIL: lo not a low surrogate, ExsA_Lib.v es_lo_check); addi s5,s4,12;
     slli s1,s1,10 (hi << 10); ld a1,0(sp) (ES_C8 = 2 ^ 64 - 0x35fdc00, ESB); add a0,a0,a1; add a0,s1,a0;
     sw a0,36(sp); then 0x84228 (CUT_UTF8 at p + 12 with cp = PjGrammar.pair_cp hi lo).
   PORTED from lib/B/Prog/ExsB_Hex2R.v (a Theorem Labs lane's B' walk): the same two states, the same runs, the same branch and
   leaf proofs. CHANGED for A': the pcs; no UBSan edge (B' tested `bltu -7,s4`); hi is s1 (atom 9; B' re-read it from
   36(sp) as an atom of the frame region), so the frame region holds ES_C8 at 0(sp) (B': 8(sp)) and lo at 32(sp) only,
   with 36(sp) writable; the pair's sv is the engine's form of A's operand order, ((hi << 10) + (ES_C8 - 2 ^ 64)) + lo,
   stated here as es_U_pairA (the donor's es_U_pair, ExsB_Sym.v, has B's form); p / the next p / o are s4 / s5 / s3
   (atoms 20 / 21 / 19; B': s3 / s4 / s2); the shadow base is s7 (atom 23).
   Numerals: 0x1c4, 0x1f4, 0x3f8 (DERIVED: cut offsets); 0, 32, 36, 40 (LENGTH: frame slots); 12 (LENGTH: the pair's
   bytes); 65535, 55296, 56319 (LENGTH / WORD: the digit and surrogate ranges); 10, 1024 (LENGTH: the surrogate
   shift); -56613888 = ES_C8 - 2 ^ 64, -57344 (WORD: the code's constants as the engine reads them). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgA ExsA_Stmt ExsA_Lib ExsA_Sym ExsA_Exit ExsA_Cont ExsA_LH.
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

(* the pair's code point as A 0x84214-0x84220 computes it, in the form the engine writes it at 36(sp):
   ((hi << 10) + (ES_C8 - 2 ^ 64)) + lo *)
Lemma es_U_pairA : forall E lo hi, ew E 45 = Z_to_bv 64 lo -> ew E 9 = Z_to_bv 64 hi ->
  55296 <= hi < 56320 -> 56320 <= lo <= 57343 ->
  U E (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SOff 9 0) (SLit 10)) (SLit (-56613888))) (SOff 45 0)) =
  PjGrammar.pair_cp hi lo.
Proof.
intros E lo hi H45 H9 Hh Hl.
assert (K : forall a b c, (((a mod 2 ^ 64 + b mod 2 ^ 64) mod 2 ^ 64) + c mod 2 ^ 64) mod 2 ^ 64 = (a + b + c) mod 2 ^ 64).
{ intros a b c. rewrite (Z.add_mod (a + b) c) by lia. rewrite (Z.add_mod a b) by lia. reflexivity. }
rewrite !U_SAlu, !U_SOff, H45, H9, !U_SLit, !unsigned_lit_small by lia.
cbn [zalu_raw]. unfold zcanon, M64.
change (Z.land (10 mod 2 ^ 64) 63) with 10. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 10) with 1024.
rewrite (Z.mod_small (hi + 0) (2 ^ 64)) by lia. rewrite !Z.add_0_r.
rewrite K. unfold PjGrammar.pair_cp. rewrite Z.mod_small by lia. lia.
Qed.

(* the frame slots the segment reads and writes: ES_C8 at 0(sp), lo at 32(sp), the pair written at 36(sp) *)
Definition ES_RF2 : YP09.region := YP09.mkRegion (Some 2%nat) 0 40 36 40
  [YP09.mkChunk 0 (CVal 8 (SLit ES_C8)); YP09.mkChunk 32 (CVal 4 (SOff 45 0))].
Definition ss_h2r_some : sstate :=
  mkSS (ES_PC + 0x1c4) (sr_set sr_atoms 10%bv (SLit 0)) [ES_RF2] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF 55296 56319 0); (20%nat, mkAF 4096 ES_CEIL 0);
              (21%nat, mkAF 4096 ES_CEIL 0); (45%nat, mkAF 0 65535 0)] [] []).
Definition ss_h2r_none : sstate :=
  mkSS (ES_PC + 0x1c4) (sr_set sr_atoms 10%bv (SLit (-1))) [] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (20%nat, mkAF 4096 ES_CEIL 0); (21%nat, mkAF 4096 ES_CEIL 0)] [] []).
(* the registers kept as atoms: up to the low-surrogate test (a0 .. a2 written), and to UTF8 (s1, s5 written too) *)
Definition ES_KEPT_H2F : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition ES_KEPT_H2U : list (bv 5) := [2; 3; 4; 8; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis LAWS : AR_laws_x rsegs B ARx cf_head.
Hypothesis HHEAD : 8 <= cf_head.

Lemma es_cut_hex2r : forall E p, CUT_UTF8 B ARx SK E (p + 12) -> CUT_HEX2R B ARx SK E p.
Proof.
intros E p HU8. unfold CUT_HEX2R.
intros lyc Sc Hpc regs memc mdc k acc hi HP HB HEG GA Hp12 Hc92 Hc117 Hhi Hhr R9 Hb6 Hb7 HRES R19 R20 R21.
pose proof (es_geom B ARx LAWS E HP) as G. unfold ES_GEOM in G. cbv zeta in G.
destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19).
pose proof HB as (HJ & HWIN & HQP & HHp & HAB & HRK & HLED & HSAV & HC0 & HC8 & HC16 & HC24 & R2 & R8 & R18 & R22 &
  R23 & R24 & R25 & R26 & R27 & R3 & R4 & HSc & HMN).
pose proof HEG as (HG1 & HG2 & HG3).
unfold es_SP in *.
assert (HPN : Forall (fun rz => getr regs (fst rz) = Z_to_bv 64 (snd rz)) ([] : list (bv 5 * Z))) by constructor.
assert (HPAIR := es_rest_pair E p ltac:(lia) ltac:(lia)).
assert (HX8 := es_hex4_at E (p + 8) ltac:(lia) ltac:(lia)).
replace (p + 8 + 1) with (p + 9) in HX8 by ring. replace (p + 8 + 2) with (p + 10) in HX8 by ring.
replace (p + 8 + 3) with (p + 11) in HX8 by ring.
assert (HDP : PjGrammar.decode (es_rest E p) =
  match PjGrammar.hex4 (es_rest E (p + 8)) with
  | Some lo => if (56320 <=? lo) && (lo <=? 57343)
      then PjGrammar.emit (PjGrammar.utf8 (PjGrammar.pair_cp hi lo)) (PjGrammar.decode (es_rest E (p + 12))) else None
  | None => None
  end).
{ rewrite (es_rest_esc E p) by lia. rewrite Hc92, Hc117. rewrite (exs_dec_hi_pair _ hi _ _ _ _ _ _ _ Hhi Hhr HPAIR).
  rewrite Hb6, Hb7. cbn [Z.eqb Pos.eqb andb]. rewrite HX8. reflexivity. }
pose (RUN := paj_run_x_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS _ (es_plaw E)).
pose (RUNTO := paj_run_to_x_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS _ (es_plaw E)).
pose (BR := paj_branch (PI := PI_prog_A)).
assert (HPM : es_P E memc) by exact HMN.
unfold cfg_at, w64. rewrite es_pc_eq.
destruct (PjGrammar.hex4 (es_rest E (p + 8))) as [lo|] eqn:Hlo.
2: { (* not four hex digits *)
  remember (es_xE regs (e_regs E) []) as Ex eqn:HEx.
  assert (HEI : img_env VAL A_LIM Ex) by (rewrite HEx; apply es_xE_env).
  assert (E2 : ew Ex 2 = Z_to_bv 64 (es_sp E - 144)) by (rewrite HEx, (es_xE_reg _ _ _ 2%bv 2) by reflexivity; exact R2).
  assert (E20 : ew Ex 20 = Z_to_bv 64 p) by (rewrite HEx, (es_xE_reg _ _ _ 20%bv 20) by reflexivity; exact R20).
  assert (E21 : ew Ex 21 = Z_to_bv 64 (p + 6)) by (rewrite HEx, (es_xE_reg _ _ _ 21%bv 21) by reflexivity; exact R21).
  assert (HS : st_ok_pi rsegs VAL Ex ss_h2r_none
    (restrict (w_H (e_W E)) (YK11.mkst regs (Z_to_bv 64 (BASE + (ES_PC + 0x1c4))) memc (YK11.seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. unfold ss_h2r_none.
    apply (pa_entry_st_ok_full (fx := fx) (L := A_prog_listing) (PI := PI_prog_A)).
    - apply regs_ok_pin; [rewrite HEx; apply regs_ok_Eimg_Ereg | intros X; discriminate X | exact HRES].
    - vm_compute. reflexivity.
    - apply Forall_nil.
    - apply pairwise_disjoint_of_extents. cbn. exact I.
    - split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E2, E20, E21, !unsigned_lit_small by lia. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold ES_CEIL. repeat split; lia. }
  assert (SHOK : sh_ok rsegs (SOff 23 0) [] Ex (rdW (e_W E) memc)) by apply Forall_nil.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM ES_SPAN (ES_PC + 0x3f8).
  { apply awr_ok_nil. }
  es_kept_of HFr (fun _ : Z => False) ltac:(fun h => idtac). clear HFr.
  es_leaf_regs HS HEx regs ES_REGS ([] : list (bv 5 * Z)) HPN HR.
  pmkst HS. es_pc_to 0x3f8.
  apply (es_cut_fail B ARx SK LAWS E lyc Sc Hpc _ _ _ k HP).
  + apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _ (fun _ : Z => False) HHEAD HP HB HJ);
      [intros a [] | exact KEPT | exact HR | exact HPM].
  + apply (es_fail_of E p acc HEG). rewrite HDP. reflexivity. }
destruct HRES as [R10 V32].
pose proof (exs_hex4_range _ _ Hlo) as Hlor.
remember (es_xE regs (e_regs E) [w64 lo]) as Ex eqn:HEx.
assert (HEI : img_env VAL A_LIM Ex) by (rewrite HEx; apply es_xE_env).
assert (E2 : ew Ex 2 = Z_to_bv 64 (es_sp E - 144)) by (rewrite HEx, (es_xE_reg _ _ _ 2%bv 2) by reflexivity; exact R2).
assert (E9 : ew Ex 9 = Z_to_bv 64 hi) by (rewrite HEx, (es_xE_reg _ _ _ 9%bv 9) by reflexivity; exact R9).
assert (E20 : ew Ex 20 = Z_to_bv 64 p) by (rewrite HEx, (es_xE_reg _ _ _ 20%bv 20) by reflexivity; exact R20).
assert (E21 : ew Ex 21 = Z_to_bv 64 (p + 6)) by (rewrite HEx, (es_xE_reg _ _ _ 21%bv 21) by reflexivity; exact R21).
assert (E45 : ew Ex 45 = Z_to_bv 64 lo) by (rewrite HEx, (es_xE_extra _ _ _ 0) by lia; reflexivity).
assert (U2 : bv_unsigned (ew Ex 2) = es_sp E - 144) by (rewrite E2; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi rsegs VAL Ex ss_h2r_some
  (restrict (w_H (e_W E)) (YK11.mkst regs (Z_to_bv 64 (BASE + (ES_PC + 0x1c4))) memc (YK11.seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_h2r_some.
  apply (pa_entry_st_ok_full (fx := fx) (L := A_prog_listing) (PI := PI_prog_A)).
  - apply regs_ok_pin; [rewrite HEx; apply regs_ok_Eimg_Ereg | intros X; discriminate X | exact R10].
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold region_ok, ES_RF2. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U2. split; [lia|]. split; [lia|]. split.
    + pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
      intros oo Hoo. apply (apresent_writable rsegs). apply HJpres. rewrite es_stk_val. lia.
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val rsegs Ex _ (es_sp E - 144) 0 8 (SLit ES_C8) ES_C8);
          [reflexivity | unfold ES_C8; cbn; lia | cbn; lia | rewrite Z.add_0_r; exact HC0].
      * apply (chunk_ok_val rsegs Ex _ (es_sp E - 144) 32 4 (SOff 45 0) lo);
          [cbn [sv_denot]; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact V32].
  - apply pairwise_disjoint_of_extents. cbn. repeat split.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E9, E20, E21, E45, !unsigned_lit_small by lia. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold ES_CEIL. repeat split; lia. }
assert (SHOK : sh_ok rsegs (SOff 23 0) [] Ex (rdW (e_W E) memc)) by apply Forall_nil.
paj_run_tok_x_inv RUN HS HJ SHOK HPM ES_SPAN.
{ es_awr ltac:(fun a Ha => rewrite ?U2 in Ha; apply es_awr_stk; lia). }
es_kept_of HFr (fun a => es_sp E - 144 + 36 <= a < es_sp E - 144 + 40) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U2 in h).
clear HFr. rename KEPT into MK.
es_envkeep HS Ex EWf.
assert (UL : forall Ef, (forall n, (n < 512)%nat -> ew Ef n = ew Ex n) -> U Ef (SOff 45 (-57344)) = (lo - 57344) mod 2 ^ 64).
{ intros Ef HW. rewrite U_SOff, (HW 45%nat ltac:(lia)), E45, unsigned_lit_small by lia. reflexivity. }
psrr_branch_tok RUN BR HS SHOK ES_SPAN.
- (* lo is not a low surrogate *)
  rewrite branch_ltu_U, (UL _ EWf), es_U_lit, es_lo_check in Hc by lia.
  apply negb_true_iff in Hc.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM ES_SPAN (ES_PC + 0x3f8).
  { es_awr ltac:(fun a Ha => rewrite ?U2 in Ha; apply es_awr_stk; lia). }
  es_kept_of HFr (fun a => es_sp E - 144 + 36 <= a < es_sp E - 144 + 40) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U2 in h).
  clear HFr.
  lazymatch goal with KEPT : forall a, _ -> _ -> aview ?sg ?H ?m' a = aview _ _ ?m a,
                      MK0 : forall a, _ -> _ -> aview _ _ ?m a = aview _ _ memc a |- _ =>
    assert (MK3 : forall a, 0 <= a < 2 ^ 64 -> ~ (es_sp E - 144 + 36 <= a < es_sp E - 144 + 40) ->
      aview sg H m' a = aview sg H memc a) by (intros a Ha Hn; rewrite (KEPT a Ha Hn); exact (MK0 a Ha Hn)) end.
  es_leaf_regs HS HEx regs ES_KEPT_H2F ([] : list (bv 5 * Z)) HPN HR.
  pmkst HS. es_pc_to 0x3f8.
  apply (es_cut_fail B ARx SK LAWS E lyc Sc Hpc _ _ _ k HP).
  + apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _
      (fun a => es_sp E - 144 + 36 <= a < es_sp E - 144 + 40) HHEAD HP HB HJ);
      [intros a Ha; right; right; unfold es_SP; lia | exact MK3 | exact HR | exact HPM].
  + apply (es_fail_of E p acc HEG). rewrite HDP, Hc. reflexivity.
- rewrite branch_ltu_U, (UL _ EWf), es_U_lit, es_lo_check in Hc by lia.
  apply negb_false_iff in Hc.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM ES_SPAN (ES_PC + 0x1f4).
  { es_awr ltac:(fun a Ha => rewrite ?U2 in Ha; apply es_awr_stk; lia). }
  es_kept_of HFr (fun a => es_sp E - 144 + 36 <= a < es_sp E - 144 + 40) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U2 in h).
  clear HFr.
  lazymatch goal with KEPT : forall a, _ -> _ -> aview ?sg ?H ?m' a = aview _ _ ?m a,
                      MK0 : forall a, _ -> _ -> aview _ _ ?m a = aview _ _ memc a |- _ =>
    assert (MK3 : forall a, 0 <= a < 2 ^ 64 -> ~ (es_sp E - 144 + 36 <= a < es_sp E - 144 + 40) ->
      aview sg H m' a = aview sg H memc a) by (intros a Ha Hn; rewrite (KEPT a Ha Hn); exact (MK0 a Ha Hn)) end.
  es_leaf_regs HS HEx regs ES_KEPT_H2U ([] : list (bv 5 * Z)) HPN HR.
  clear EWf. es_envkeep HS Ex EWf.
  lazymatch type of HS with st_ok_pi _ _ ?Ef _ _ =>
    pose proof (es_U_pairA Ef lo hi ltac:(first [exact E45 | rewrite EWf by lia; exact E45])
      ltac:(first [exact E9 | rewrite EWf by lia; exact E9])
      Hhr ltac:(rewrite !Bool.andb_true_iff, !Z.leb_le in Hc; lia)) as UP end.
  pose proof (es_region_nth _ _ _ 0 _ HS eq_refl) as RF. cbn [ms_mem restrict] in RF.
  pose proof (exs_pair_range hi lo Hhr ltac:(rewrite !Bool.andb_true_iff, !Z.leb_le in Hc; lia)) as HPR.
  pose proof (es_field _ _ 2 (es_sp E - 144) _ _ _ _ _ 36 4
    (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SOff 9 0) (SLit 10)) (SLit (-56613888))) (SOff 45 0))
    (PjGrammar.pair_cp hi lo) RF
    ltac:(first [exact U2 | rewrite EWf by lia; exact U2]) ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
    ltac:(unfold U in UP; rewrite <- UP; symmetry; apply Z_to_bv_bv_unsigned) ltac:(cbn; lia) ltac:(cbn; lia)) as V36'.
  clear RF.
  es_reg0 HS (21%bv : bv 5) R21'.
  pmkst HS. es_pc_to 0x1f4.
  apply (HU8 lyc Sc Hpc _ _ _ k acc (PjGrammar.pair_cp hi lo) HP).
  + apply (es_esb_step B ARx SK LAWS E lyc Sc Hpc regs memc mdc k _ _ _
      (fun a => es_sp E - 144 + 36 <= a < es_sp E - 144 + 40) HHEAD HP HB HJ);
      [intros a Ha; right; right; unfold es_SP; lia | exact MK3 | exact HR | exact HPM].
  + apply (es_esg_step E p acc 12 (PjGrammar.utf8 (PjGrammar.pair_cp hi lo)) HEG ltac:(lia)).
    * rewrite exs_utf8_len_pair by lia. lia.
    * rewrite HDP, Hc. reflexivity.
  + lia.
  + apply (es_garr8_kept (w_H (e_W E)) memc); [|exact GA]. intros a Ha. apply MK3; [lia | lia].
  + unfold es_SP. exact V36'.
  + rewrite (HKR 19%bv ltac:(cbn; tauto)). exact R19.
  + rewrite R21', (es_den_off _ 20 12 p ltac:(first [exact E20 | rewrite EWf by lia; exact E20])) by lia. reflexivity.
Qed.
End c.
