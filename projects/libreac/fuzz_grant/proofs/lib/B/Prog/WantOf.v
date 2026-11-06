(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: image-B walk of want_of; proof steps adapted from lib/A/Prog/HeadampTxEffective.v and CtrlChecksumVerify.v (cgif_file_fuzzer lib/A/AC8a.v, AChd.v, AC8h.v) and lib/Reusable/YI08.v, YI04.v (cgif lib/YI08.v, YI04.v). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaRun PaShadow PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantSyms GrantList GrantAddr GrantTop GrantPa.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantPaLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require HeadampDefault GrantBContracts.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module BC := OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog.GrantBContracts.
Module HD := OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog.HeadampDefault.

Lemma wo_tb_range : forall (T : list byte) i, 0 <= tb T i < 256.
Proof.
intros T i. unfold tb.
pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) T (Z_to_bv 8 0))) as R.
change (bv_modulus 8) with 256 in R. exact R.
Qed.

Lemma wo_U_3c : forall E c, ew E 12 = Z_to_bv 64 c -> 0 <= c < 48 ->
  U E (SMd M_MUL (SOff 12 0) (SLit 3)) = 3 * c.
Proof.
intros E c H12 Hc. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E 12 c H12) by lia. rewrite U_SLit, (zcanon_id 3) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma wo_U_base3c : forall E n b c, ew E n = Z_to_bv 64 b -> ew E 12 = Z_to_bv 64 c ->
  0 <= b < 2 ^ 47 -> 0 <= c < 48 ->
  U E (SAlu ALU_ADD (SOff n 0) (SMd M_MUL (SOff 12 0) (SLit 3))) = b + 3 * c.
Proof.
intros E n b c Hn H12 Hb Hc. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E n b Hn) by lia. rewrite (wo_U_3c E c H12 Hc).
apply zcanon_id. unfold M64. lia.
Qed.

Lemma wo_U_x : forall E n b c p, ew E n = Z_to_bv 64 b -> ew E 12 = Z_to_bv 64 c ->
  ew E 13 = Z_to_bv 64 p -> 0 <= b < 2 ^ 47 -> 0 <= c < 48 -> 0 <= p < 3 ->
  U E (SAlu ALU_ADD (SAlu ALU_ADD (SOff n 0) (SMd M_MUL (SOff 12 0) (SLit 3))) (SOff 13 0))
  = b + (3 * c + p).
Proof.
intros E n b c p Hn H12 H13 Hb Hc Hp. rewrite U_SAlu. cbn [zalu_raw].
rewrite (wo_U_base3c E n b c Hn H12 Hb Hc). rewrite (U_atom E 13 p H13) by lia.
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma wo_U_xor : forall E a, U E (SAlu ALU_XOR a (SLit (-1))) = 2 ^ 64 - 1 - U E a.
Proof.
intros E a. pose proof (U_range E a) as Hr. unfold M64 in Hr.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
change (zcanon (-1)) with (2 ^ 64 - 1). rewrite lxor_allones by lia.
apply zcanon_id. unfold M64. lia.
Qed.

Section D. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section F.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

(* The shadow base of this runtime, the symbolic atoms of the entry state, and the two
   one-byte cells the call reads: w + (3c + p) is atom 33, v + (3c + p) is atom 34. *)
Definition WSB : Z := 0x7fff8000.
Definition WBx : sv := SOff 32 0.
Definition WBspan : Z * Z := (WSB, WSB + 2 ^ 44 - 1).
Definition X3C : sv := SMd M_MUL (SOff 12 0) (SLit 3).
Definition XW : sv := SAlu ALU_ADD (SAlu ALU_ADD (SOff 10 0) X3C) (SOff 13 0).
Definition XV : sv := SAlu ALU_ADD (SAlu ALU_ADD (SOff 11 0) X3C) (SOff 13 0).
Definition wo_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 0 (2 ^ 47 - 145) 0);
            (11%nat, mkAF 0 (2 ^ 47 - 145) 0); (12%nat, mkAF 0 47 0); (13%nat, mkAF 0 2 0);
            (32%nat, mkAF WSB WSB 0); (33%nat, mkAF 0 (2 ^ 47 - 2) 0); (34%nat, mkAF 0 (2 ^ 47 - 2) 0);
            (35%nat, mkAF 0 255 0); (36%nat, mkAF 0 255 0) ]
          [] [ (XW, SOff 33 0); (XV, SOff 34 0) ].
Definition RXW : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 35 0))].
Definition RXV : YP09.region := YP09.mkRegion (Some 34%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 36 0))].
Definition wo_regions : smem := [ stack_region 16; got_regionP; bcell_regionP 32; RXW; RXV ].
Definition ss_wo : sstate := mkSS AF_want_of sr_atoms wo_regions None wo_facts.
Definition wo_SH : list shent := [ mkSHE 33 0 1; mkSHE 34 0 1 ].
Definition wo_extra (w v c p : Z) (WS VS : list byte) : list word :=
  map (Z_to_bv 64) [WSB; w + (3 * c + p); v + (3 * c + p); tb WS (3 * c + p); tb VS (3 * c + p)].
Definition EW (regs : bvmap 5 word) (w v c p : Z) (WS VS : list byte) : env :=
  Eimg (Ereg regs (wo_extra w v c p WS VS)).

Section H.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).

(* One byte of a caller table, as the entry state needs it. *)
Lemma wo_byte : forall (m : word -> option byte) (base : Z) (L : list byte) (i : Z),
  garr8 SEGS m base (map bv_unsigned L) -> 0 <= i < Z.of_nat (length L) ->
  val_mem SEGS m (base + i) 1 (tb L i).
Proof.
intros m base L i HG Hi.
destruct (HG (Z.to_nat i) ltac:(rewrite length_map; lia)) as [HV _].
rewrite Z2Nat.id in HV by lia.
replace (nth (Z.to_nat i) (map bv_unsigned L) 0)
  with (tb L i) in HV; [exact HV|].
unfold tb. rewrite <- (map_nth bv_unsigned L (Z_to_bv 8 0) (Z.to_nat i)).
f_equal; try (cbn; lia).
Qed.

Lemma wo_entry : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch (w v c p : Z) (WS VS : list byte),
  afn_pre SEGS B BC.STK_want_of ly S W regs mem md ch ->
  getr regs 10 = w64 w -> getr regs 11 = w64 v -> getr regs 12 = w64 c -> getr regs 13 = w64 p ->
  0 <= c < 48 -> 0 <= p < 3 ->
  length WS = 144%nat -> garr8 SEGS (mrestrict (w_H W) mem) w (map bv_unsigned WS) ->
  length VS = 144%nat -> garr8 SEGS (mrestrict (w_H W) mem) v (map bv_unsigned VS) ->
  0 <= w -> amem_range w 144 -> (w + 144 <= IMG_LO_B \/ IMG_TOP_B <= w) ->
  0 <= v -> amem_range v 144 -> (v + 144 <= IMG_LO_B \/ IMG_TOP_B <= v) ->
  (w + 144 <= v \/ v + 144 <= w) ->
  (spZ regs <= w \/ w + 144 <= spZ regs - BC.STK_want_of) ->
  (spZ regs <= v \/ v + 144 <= spZ regs - BC.STK_want_of) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (w + (3 * c + p)) 1 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (v + (3 * c + p)) 1 ->
  st_ok_pi SEGS VAL (EW regs w v c p WS VS) ss_wo
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_want_of)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS WBx wo_SH (EW regs w v c p WS VS) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch w v c p WS VS HPRE H10 H11 H12 H13 Hc Hp
  HLW HGW HLV HGV Hw0 Hwm Hwi Hv0 Hvm Hvi Hwv Hws Hvs HRW HRV.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchn & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS0 : BC.STK_want_of = 4096) by reflexivity.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR. pose proof (pa_obj_img 35 ltac:(lia)) as HcellR.
rewrite IMG_LO_B_val, IMG_TOP_B_val in HgotR, HcellR, Hwi, Hvi.
pose proof (pal_got_cell B TL) as HgcD.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
assert (HwU : 0 <= w <= 2 ^ 47 - 145) by (unfold amem_range in Hwm; lia).
assert (HvU : 0 <= v <= 2 ^ 47 - 145) by (unfold amem_range in Hvm; lia).
assert (Hsp47 : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
rewrite restrict_mkst_fx.
set (E := EW regs w v c p WS VS).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (wo_extra w v c p WS VS)) n)
  by (intros n Hn; subst E; unfold EW; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 w) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 v) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 c) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 WSB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (w + (3 * c + p))) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (v + (3 * c + p))) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (tb WS (3 * c + p))) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (tb VS (3 * c + p))) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold EW; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ecell : ew E (A_OBJ 35) = Z_to_bv 64 (VAL (A_OBJ 35))) by (subst E; unfold EW; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
pose proof (wo_tb_range WS (3 * c + p)) as RW. pose proof (wo_tb_range VS (3 * c + p)) as RV.
assert (VB : forall n z, ew E n = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> base_val E (Some n) = z).
{ intros n z Hn Hz. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hz. }
assert (HUB : U E WBx = SHADOW_OFF)
  by (unfold WBx; rewrite (U_atom E 32 WSB E32) by (unfold WSB; lia); reflexivity).
split.
- unfold ss_wo. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold wo_regions, stack_region, got_regionP, bcell_regionP, RXW, RXV.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 35) 0) (VAL (A_OBJ 35)));
      [cbn [sv_denot]; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 35)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 35) (VAL (A_OBJ 35)) Ecell) by (pose proof (pa_val_range (A_OBJ 35)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 35)) 0 8 WBx SHADOW_OFF);
      [cbn [sv_denot WBx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB 33%nat (w + (3 * c + p)) E33) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (w + (3 * c + p)) 0 1 (SOff 35 0) (tb WS (3 * c + p)));
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. apply (wo_byte (mrestrict (w_H W) mem) w WS (3 * c + p) HGW). lia.
    * rewrite (VB 34%nat (v + (3 * c + p)) E34) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (v + (3 * c + p)) 0 1 (SOff 36 0) (tb VS (3 * c + p)));
      [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. apply (wo_byte (mrestrict (w_H W) mem) v VS (3 * c + p) HGV). lia.
  + apply pairwise_disjoint_of_extents.
    unfold wo_regions, stack_region, got_regionP, bcell_regionP, RXW, RXV, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    rewrite (VB (A_OBJ 35) (VAL (A_OBJ 35)) Ecell) by (pose proof (pa_val_range (A_OBJ 35)); lia).
    rewrite (VB 33%nat (w + (3 * c + p)) E33) by lia.
    rewrite (VB 34%nat (v + (3 * c + p)) E34) by lia.
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1 C3 WS0 Hstk0 HcellR HgcD HgotR Hwi Hvi Hwv Hws Hvs HwU HvU Hc Hp.
    clear. intros. repeat split; lia.
  + split; [|split; [exact I | ]].
    * cbn [wo_facts f_atoms atoms_ok].
      split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Usp; change (2 ^ 4) with 16;
              revert Hslo Hshi H47 Hceil C1 WS0 Hstk0 Hal16 Hsp47; clear; intros; repeat split; lia|].
      split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E10, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia|].
      split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E11, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia|].
      split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E12, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia|].
      split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E13, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia|].
      split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E32, unsigned_lit_small by (unfold WSB; lia);
              rewrite Z.pow_0_r, Z.mod_1_r; lia|].
      split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E33, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia|].
      split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E34, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia|].
      split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E35, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia|].
      split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E36, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia | exact I].
    * cbn [wo_facts f_alias alias_ok].
      split; [|split; [|exact I]].
      -- unfold XW, X3C. rewrite denot_lit_U, (wo_U_x E 10 w c p E10 E12 E13 ltac:(lia) Hc Hp).
         cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      -- unfold XV, X3C. rewrite denot_lit_U, (wo_U_x E 11 v c p E11 E12 E13 ltac:(lia) Hc Hp).
         cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- unfold sh_ok, wo_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + apply (shent_ok_of_range SEGS (w_H W) mem E WBx 33 (w + (3 * c + p)) 1 (w + (3 * c + p)) 0 1 HRW HUB).
    * rewrite U_SOff, E33, Z.add_0_r, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
    * lia.
    * lia.
    * intros x Hx. unfold amem_range in Hwm.
      revert Hwm Hx Hc Hp C5 C3. unfold SHADOW_OFF, kHighMemBeg, kLowMemEnd. clear. intros. lia.
  + apply (shent_ok_of_range SEGS (w_H W) mem E WBx 34 (v + (3 * c + p)) 1 (v + (3 * c + p)) 0 1 HRV HUB).
    * rewrite U_SOff, E34, Z.add_0_r, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
    * lia.
    * lia.
    * intros x Hx. unfold amem_range in Hvm.
      revert Hvm Hx Hc Hp C5 C3. unfold SHADOW_OFF, kHighMemBeg, kLowMemEnd. clear. intros. lia.
Qed.

Ltac wo_reg HS r H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?vl ?Ex ?ss (restrict ?Hh ?ms) =>
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in
      assert (H : getr (ms_regs ms) r = sv_denot Ex e)
        by exact (st_ok_pi_restrict_reg Hh Ex ss ms r HS)
  | st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in
      assert (H : getr (ms_regs ms) r = sv_denot Ex e)
        by exact (st_ok_restrict_reg segs Hh Ex ss ms r HS)
  end.

Theorem wo_holds : HD.treac_headamp_default_spec B -> BC.tb_want_of_spec B.
Proof.
intros HDFLT.
unfold BC.tb_want_of_spec.
intros ly S W regs mem md ch w v c p WS VS HPRE H10 H11 H12 H13 Hc Hp
  HLW HGW HLV HGV Hw0 Hwm Hwi Hv0 Hvm Hvi Hwv Hws Hvs HRW HRV.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (wo_entry ly S W regs mem md ch w v c p WS VS HPRE H10 H11 H12 H13 Hc Hp
  HLW HGW HLV HGV Hw0 Hwm Hwi Hv0 Hvm Hvi Hwv Hws Hvs HRW HRV) as [HS SHOK].
pose proof (ajournal_init SEGS B BC.STK_want_of [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchn & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS0 : BC.STK_want_of = 4096) by reflexivity.
assert (HwU : 0 <= w <= 2 ^ 47 - 145) by (unfold amem_range in Hwm; lia).
assert (HvU : 0 <= v <= 2 ^ 47 - 145) by (unfold amem_range in Hvm; lia).
assert (Hspc : alloc_ceiling <= spZ regs) by lia.
pose proof (wo_tb_range WS (3 * c + p)) as RW. pose proof (wo_tb_range VS (3 * c + p)) as RV.
remember (EW regs w v c p WS VS) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EW; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (wo_extra w v c p WS VS)) n)
  by (intros n Hn; subst E; unfold EW; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 w) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 v) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 c) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 WSB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E35 : ew E 35 = Z_to_bv 64 (tb WS (3 * c + p))) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (tb VS (3 * c + p))) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (HAE : env_agree 32 (Ereg regs (wo_extra w v c p WS VS)) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HEdef EL.
unfold cfg_at. change (w64 (BASE + AF_want_of)) with (Z_to_bv 64 (BASE + AF_want_of)).
(* the prologue, the index and the first trap guard 0x82448 *)
paj_run_tok RUN HS HJ SHOK WBspan;
  [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
psrr_branch_tok RUN BR HS SHOK WBspan.
- (* 0x82448 taken: w + 3c would carry past 2^64 *)
  exfalso. rewrite branch_ltu_U, wo_U_xor in Hc0.
  rewrite (U_atom _ 10 w) in Hc0 by (first [rewrite ?ew_ewset_other by lia; exact E10 | lia]).
  rewrite (wo_U_3c _ c) in Hc0 by (first [rewrite ?ew_ewset_other by lia; exact E12 | lia]).
  apply Z.ltb_lt in Hc0. lia.
- paj_run_tok RUN HS HJ SHOK WBspan;
    [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
  psrr_branch_tok RUN BR HS SHOK WBspan.
  + (* 0x8245c taken: (w + 3c) + p would carry past 2^64 *)
    exfalso. rewrite branch_ltu_U, wo_U_xor in Hc1.
    rewrite (wo_U_base3c _ 10 w c) in Hc1
      by (first [rewrite ?ew_ewset_other by lia; exact E10 | rewrite ?ew_ewset_other by lia; exact E12 | lia]).
    rewrite (U_atom _ 13 p) in Hc1 by (first [rewrite ?ew_ewset_other by lia; exact E13 | lia]).
    apply Z.ltb_lt in Hc1. lia.
  + (* the shadow check of w[3c + p] and the read *)
    paj_run_tok RUN HS HJ SHOK WBspan;
      [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
    psrr_branch_tok RUN BR HS SHOK WBspan.
    * (* 0x82484 taken: w[3c + p] = 0, the tail jump to reac_headamp_default *)
      rewrite branch_eq_U in Hc2.
      rewrite (U_atom _ 35 (tb WS (3 * c + p))) in Hc2
        by (first [rewrite ?ew_ewset_other by lia; exact E35 | lia]).
      rewrite U_lit in Hc2 by lia. apply Z.eqb_eq in Hc2.
      paj_run_tok RUN HS HJ SHOK WBspan;
        [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
      lazymatch goal with
      | HS : st_ok _ ?Ex ?ssx (restrict _ ?msx) |- _ =>
        let R1 := fresh "R1" in let R2 := fresh "R2" in let R3 := fresh "R3" in
        let R4 := fresh "R4" in let R8 := fresh "R8" in let R10 := fresh "R10" in
        wo_reg HS (1%bv : bv 5) R1; wo_reg HS (2%bv : bv 5) R2; wo_reg HS (3%bv : bv 5) R3;
        wo_reg HS (4%bv : bv 5) R4; wo_reg HS (8%bv : bv 5) R8; wo_reg HS (10%bv : bv 5) R10;
        cbn [sv_denot] in R1, R3, R4, R8, R10;
        rewrite ?ew_ewset_other in R1, R3, R4, R8, R10 by lia;
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E1 in R1;
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E3 in R3;
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E4 in R4;
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E8 in R8;
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E13 in R10;
        eapply SRr_mono;
        [ eapply (aj_call SEGS B LAWS Hsegs W Ex ssx msx
                    BC.STK_want_of (spZ regs) [] ly S W mem md [] ly S _ 0
                    HD.REAC_HEADAMP_DEFAULT_STK [] 0 0 (getr regs 2) (getr (ms_regs msx) 1) ch _
                    HS ltac:(vm_compute; reflexivity) HJ)
        | ]
      end.
      -- (* sp at the jump is the entry sp *)
         exact R2.
      -- rewrite ?ew_ewset_other by lia. exact E2.
      -- reflexivity.
      -- reflexivity.
      -- lia.
      -- unfold HD.REAC_HEADAMP_DEFAULT_STK, ESTACK. lia.
      -- unfold HD.REAC_HEADAMP_DEFAULT_STK, BC.STK_want_of, ESTACK. lia.
      -- rewrite R3. exact Hgp.
      -- rewrite R4. exact Htp.
      -- reflexivity.
      -- rewrite R1. exact Hra.
      -- rewrite R1. exact Hra4.
      -- (* the caller's frame chain survives: nothing at or above sp changed *)
         rewrite Z.add_0_r. unfold s0Z. rewrite R8.
         eapply (achain_kept ly _ _ (spZ regs) _ ch (spZ regs) Hchn ltac:(lia) ltac:(lia)).
         intros a Ha.
         pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
         apply F1; lia.
      -- (* the callee *)
         intros HPREc.
         lazymatch goal with |- SRr _ _ (mkCfg (mkst _ ?pcx _ _) ?mdx) _ =>
           replace pcx with (w64 HD.A_reac_headamp_defaultP)
         end.
         ++ eapply SRr_mono.
            ** refine (HDFLT ly S W _ _ _ ch p HPREc _ ltac:(lia)).
               rewrite R10. reflexivity.
            ** cbv beta. intros W2 c2 _ HQ. exact HQ.
         ++ cbn [ss_pc setpc]. unfold HD.A_reac_headamp_defaultP.
            rewrite pa_sigma_reac_headamp_default. reflexivity.
      -- intros a Ha. destruct (inFP_nil a Ha).
      -- (* the post *)
         cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & _ & HPr & HK).
         destruct HK as (HV & -> & -> & -> & _ & _).
         unfold BC.tb_want_of_post, apost_base.
         exists ly, S, regs2, mem2, md2.
         split; [rewrite R1; reflexivity|].
         split; [exact HJ2|].
         split.
         ** eapply aregs_preserved_trans; [|exact HPr].
            lazymatch type of HS with
            | st_ok _ ?Ex _ _ =>
              eapply (aregs_preserved_of_st_ok SEGS _ Ex _ _ regs (wo_extra w v c p WS VS) HS);
              [eapply env_agree_trans;
               [exact HAE | split; [intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]]
              | vm_compute; reflexivity]
            end.
         ** split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
            rewrite HV. rewrite (proj2 (Z.eqb_eq (tb WS (3 * c + p)) 0) Hc2). reflexivity.
    * (* 0x82484 not taken: w[3c + p] <> 0, the second table *)
      rewrite branch_eq_U in Hc2.
      rewrite (U_atom _ 35 (tb WS (3 * c + p))) in Hc2
        by (first [rewrite ?ew_ewset_other by lia; exact E35 | lia]).
      rewrite U_lit in Hc2 by lia.
      apply Z.eqb_neq in Hc2.
      paj_run_tok RUN HS HJ SHOK WBspan;
        [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
      psrr_branch_tok RUN BR HS SHOK WBspan.
      -- (* 0x8248c taken: v + 3c would carry past 2^64 *)
         exfalso. rewrite branch_ltu_U, wo_U_xor in Hc3.
         rewrite (U_atom _ 11 v) in Hc3 by (first [rewrite ?ew_ewset_other by lia; exact E11 | lia]).
         rewrite (wo_U_3c _ c) in Hc3 by (first [rewrite ?ew_ewset_other by lia; exact E12 | lia]).
         apply Z.ltb_lt in Hc3. lia.
      -- paj_run_tok RUN HS HJ SHOK WBspan;
           [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
         psrr_branch_tok RUN BR HS SHOK WBspan.
         ++ (* 0x82498 taken: (v + 3c) + p would carry past 2^64 *)
            exfalso. rewrite branch_ltu_U, wo_U_xor in Hc4.
            rewrite (wo_U_base3c _ 11 v c) in Hc4
              by (first [rewrite ?ew_ewset_other by lia; exact E11 | rewrite ?ew_ewset_other by lia; exact E12 | lia]).
            rewrite (U_atom _ 13 p) in Hc4 by (first [rewrite ?ew_ewset_other by lia; exact E13 | lia]).
            apply Z.ltb_lt in Hc4. lia.
         ++ (* the shadow check of v[3c + p], the read and the return *)
            paj_run_tok RUN HS HJ SHOK WBspan;
              [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp |].
            lazymatch goal with
            | HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msx) |- _ =>
              let R1 := fresh "R1" in let R10 := fresh "R10" in
              wo_reg HS (1%bv : bv 5) R1; wo_reg HS (10%bv : bv 5) R10;
              cbn [sv_denot] in R1, R10;
              rewrite ?ew_ewset_other in R1, R10 by lia;
              rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E1 in R1;
              rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E36 in R10;
              eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
              let mt := fresh "mt" in intros mt; cbn [ms_regs ms_mem]; rewrite R1, Hra
            end.
            unfold BC.tb_want_of_post, apost_base.
            lazymatch goal with
            | HS : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ =>
              exists ly, S, (ms_regs msx), (ms_mem msx); eexists
            end.
            split; [reflexivity|].
            split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
            split.
            ** lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
                 eapply (aregs_preserved_of_st_ok SEGS _ Ex _ _ regs (wo_extra w v c p WS VS) HS);
                 [eapply env_agree_trans;
                  [exact HAE | split; [intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]]
                 | vm_compute; reflexivity]
               end.
            ** split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
               rewrite R10. rewrite (proj2 (Z.eqb_neq (tb WS (3 * c + p)) 0) Hc2). reflexivity.
Qed.

End H.

Theorem pb_want_of : forall B : asyms, BC.walk_want_of B.
Proof.
intros B HY HDFLT. destruct HY as [HL HP]. exact (wo_holds B HL HP HDFLT).
Qed.

End F.
End D.
