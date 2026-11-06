(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySetGa0), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySetGa0.v, with its module paths and module names changed; 671 of its 703 lines of code are new or changed and 147 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/BoxLxCase0Strn.v, with its module paths and module names changed; 150 of its 210 lines of code are new or changed and 643 lines of the source are left out. *)
(* The end of the checks of LLVMFuzzerTestOneInput's case 0 (fuzz_boxreg.c:280-283) on the ASan build, a placed row
   only: from the cut S (0x80a4c, BoxLxCase0Defs.v), strncmp returned 0 in a0. `ld a1, 0x48(s1)` (n), `ld a3,
   0x30(s1)` (want), `bnez a0` (a0 = 0: not taken), `sraiw a0, a3, 31; or a0, a0, a1` (want >= 0: a0 = n), `ld s9,
   0x50(s1)` (the fabric), `bne s7, a0` -> 0x80f60 (s7 = n: refuted with Pau's c0_link_placed, want = b >= 0,
   c0s_sra_or), then the shadow-checked `lw` of the new row's base at s3 + 8 = r + 56 n + 8 (the engine's shadow token
   from the SH entry of the row, so the slow path 0x80da0 and its report at 0x80fd4 are not taken) and `bne a0, a3`
   -> 0x80f60 (the base is b = want: decided by the engine, both are atom 32), `j 0x80aa4`: the cut F with
   bs' = c0_placed bs b nch p s (Pau's reac_boxreg_declare_keeps_inv_holds, c0_decl_fabric, c0_kept_placed). *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YI16 YC5d YM05 YG0s YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal BoxSyms BoxList BoxPa BoxPaLib BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC4b YC1g YC1h YC85 BoxFrame BoxCJ BoxRo.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import ReacBoxregInit BoxLxDefs ReadName.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg BoxregUpd LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require LLVMFuzzerTestOneInput_case0 LLVMFuzzerTestOneInput_rn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require read_name_c reac_boxreg_declare_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxLxCase0Defs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require reac_boxreg_declare_inv BoxregRd.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The symbolic state at S: the spill slots 0x30 (want = b, atom 32), 0x48 (n, s7's atom 23), 0x50 (the fabric,
   atom 33) over s1 (atom 9); the new row's base field (b, atom 32) over s3 = r + 56 n (atom 19). Atom 18 is s2 =
   SHADOW_OFF, the shadow base of the engine's tokens. *)
Definition C0S_SB : Z := 0x7fff8000.
Definition C0S_RS : YP09.region := YP09.mkRegion (Some 9%nat) 0x30 0x58 0 0
  [YP09.mkChunk 0x30 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x48 (CVal 8 (SOff 23 0)); YP09.mkChunk 0x50 (CVal 8 (SOff 33 0))].
Definition C0S_RR : YP09.region := YP09.mkRegion (Some 19%nat) 0 56 0 0 [YP09.mkChunk 8 (CVal 4 (SOff 32 0))].
Definition C0S_facts : facts :=
  mkFacts [(18%nat, mkAF C0S_SB C0S_SB 0); (19%nat, mkAF 4096 140737479966720 3); (32%nat, mkAF 0 127 0)] [] [].
Definition C0S_SH : list shent := [mkSHE 19 0 56].

(* `sraiw a0, a3, 31; or a0, a0, a1` with a3 = w, 0 <= w < 2^31, leaves a1. *)
Lemma c0s_sra_or : forall E w (m : nat), ew E 32 = Z_to_bv 64 w -> 0 <= w < 2 ^ 31 ->
  sv_denot E (SAlu ALU_OR (SAluw ALU_SRA (SOff 32 0) (SLit 31)) (SOff m 0)) = sv_denot E (SOff m 0).
Proof.
intros E w m H Hw. cbn [sv_denot]. rewrite w_sraw. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned.
unfold v_sraw. rewrite unsigned_lit_small by lia.
change (bv_unsigned (Z_to_bv 64 31) mod 32) with 31.
rewrite (LLVMFuzzerTestOneInput_case0.c0_swrap_small w) by lia.
rewrite Z.shiftr_div_pow2, Z.div_small by lia.
apply bv_eq. unfold alu64, alu. rewrite bv_or_unsigned. change (bv_unsigned (Z_to_bv 64 (bv_swrap 32 0))) with 0.
rewrite Z.lor_0_l. reflexivity.
Qed.
Lemma c0c_bsub_nth : forall (l : list byte) (k n : Z) (j : nat), 0 <= k -> 0 <= n -> k + n <= Z.of_nat (length l) ->
  (j < Z.to_nat n)%nat -> nth j (Boxreg.bsub l k n) (Z_to_bv 8 0) = nth (Z.to_nat k + j) l (Z_to_bv 8 0).
Proof.
intros l k n j Hk Hn Hkn Hj. unfold Boxreg.bsub. rewrite nth_firstn.
replace (j <? Z.to_nat n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hj).
apply nth_skipn.
Qed.
Lemma c0c_le4_byte : forall v (kk : nat), 0 <= v < 2 ^ 32 -> (kk < 4)%nat ->
  bv_unsigned (nth kk (Mem.le4 (Z_to_bv 64 v)) (Z_to_bv 8 0)) = YG0f.le_byte v 4 kk.
Proof.
intros v kk Hv Hk. unfold Mem.le4. rewrite unsigned_lit_small by lia. unfold YG0f.le_byte.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite (Z.mod_small v) by lia.
destruct kk as [|[|[|[|kk]]]]; [| | | | lia]; cbn [nth Z_to_le_bytes]; rewrite Z_to_bv_unsigned; unfold bv_wrap;
  change (bv_modulus 8) with 256; rewrite ?Z.shiftr_shiftr by lia; reflexivity.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).

(* Four bytes of a 288-byte table at r + o that are le4 v, as the engine's 4-byte chunk of value v. *)
Lemma c0c_vm4 : forall (H : word -> bool) mem r (l : list byte) o v,
  (forall i, 0 <= i < REG_SIZE -> aview SEGS H mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) l (Z_to_bv 8 0)))) ->
  length l = 288%nat -> 0 <= o -> o + 4 <= 288 ->
  Boxreg.bsub l o 4 = Mem.le4 (Z_to_bv 64 v) -> 0 <= v < 2 ^ 32 -> val_mem SEGS (mrestrict H mem) (r + o) 4 v.
Proof.
intros H mem r l o v HR HL Ho Ho4 Hb Hv. apply val_mem_of_rd32. intros kk Hk.
replace (r + o + Z.of_nat kk) with (r + (o + Z.of_nat kk)) by lia.
rewrite HR by (unfold REG_SIZE; lia). f_equal.
rewrite <- (c0c_le4_byte v kk Hv Hk), <- Hb.
rewrite (c0c_bsub_nth l o 4 kk) by (rewrite ?HL; lia).
do 2 f_equal. lia.
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.


Theorem c0_fin : forall i POST, gb_from B MT POST (C0_F B MT i) -> gb_from B MT POST (C0_S B MT i).
Proof.
intros i POST HNX cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
destruct HI as (r & bs & pos & op & nm & want & b & p & HMS & HTURN & HWANT & Hwr & S30 & S58 & HPL & HREG & R10 & R19 & R23 & R25 & R27).
destruct HTURN as (HMF & Hi & Hk & Hacc & HBL & HINV & Hpos & HCUR & Hnm & HNAME & Hop & Hop3 & R20).
pose proof HMS as (_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G3 & G4 & G18 & G24)).
pose proof HMF as (HSV & HSH & HFL & HSFR & HINP & HPREV & (S10 & S20 & S38 & S40 & S50 & S60) & S68 & S48).
pose proof (LLVMFuzzerTestOneInput_case0.c0_link_placed _ _ _ _ _ _ HWANT HPL) as Ewb. subst want.
pose proof HPL as (Hbw & Hn5 & Hpl).
pose proof HINV as ((HL & HB1 & HB2 & _) & _). unfold Boxreg.boxreg_B1 in HB1. unfold Boxreg.boxreg_B2 in HB2.

assert (Hb0 : 0 <= b) by (destruct Hpl as [(H1 & H2 & _) | (_ & _ & H3 & _)]; lia).
set (n := Boxreg.bx_n bs) in *.
set (fab := Boxreg.bx_fabric bs) in *.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBok.
pose proof (pa_base_lo (PL := PL_box) (PI := PI)) as HBLO.
pose proof (c0_sp cx HB) as (Hsp & Hsp1 & Hsp32 & Hsp16). unfold GB_STK in Hsp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR3 & _).
assert (Hrin3 : In (r, REG_SIZE) (ablocks B ly3 S3)) by (rewrite HBL; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR3 Hrin3) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
change (req_size REG_SIZE) with 288 in *.

set (E := Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 b; Z_to_bv 64 fab])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E q = getr (ms_regs ms3) r)
  by (intros q r0 Hq; subst E; apply ew_Eimg_Ereg_nat; exact Hq).
assert (F32 : ew E 32 = Z_to_bv 64 b) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (F33 : ew E 33 = Z_to_bv 64 fab) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite (EE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = r + 56 * n) by (rewrite (EE 19%nat 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (Hn4 : 0 <= n <= 4) by lia.
assert (HS : st_ok_pi SEGS VAL E (mkSS GC_S sr_atoms [C0S_RS; C0S_RR] None C0S_facts) (restrict (w_H W3) ms3)).
{ rewrite (c0_mkst cx fp GC_S ms3 (w_H W3) HMS). apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold C0S_RS, C0S_RR. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS _ _ _ 0x30 8%N (SOff 32 0) b); [rewrite c0_denot_off0; exact F32 | cbn; lia | cbn; lia |].
        apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). rewrite Z.mod_small in S30 by lia. exact S30.
      * apply (chunk_ok_val SEGS _ _ _ 0x48 8%N (SOff 23 0) n); [rewrite c0_denot_off0, (EE 23%nat 23%bv eq_refl), R23; reflexivity | cbn; lia | cbn; lia |].
        apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact S48.
      * apply (chunk_ok_val SEGS _ _ _ 0x50 8%N (SOff 33 0) fab); [rewrite c0_denot_off0; exact F33 | cbn; lia | cbn; lia |].
        apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact S50.
    + rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS _ _ _ 8 4%N (SOff 32 0) b); [rewrite c0_denot_off0; exact F32 | cbn; lia | cbn; lia |].
      replace (r + 56 * n + 8) with (r + (56 * n + 8)) by lia.
      destruct HREG as (_ & HRL & HRB).
      apply (c0c_vm4 (w_H W3) (ms_mem ms3) r _ (56 * n + 8) b HRB HRL); [lia | lia | | lia].
      unfold c0_placed. change (BoxregUpd.new_row_bytes bs (reac_boxreg_declare_c.decl_row b (c0_nch cx pos) p (c0_gs cx pos op)))
        with (reac_boxreg_declare_c.decl_bytes bs b (c0_nch cx pos) p (c0_gs cx pos op)).
      subst n. rewrite (LLVMFuzzerTestOneInput_case0.c0_row_bsub bs b _ p _ 8 4 HL Hn4) by lia.
      apply reac_boxreg_declare_inv.decl_row_base.
  - apply pairwise_disjoint_of_extents. unfold C0S_RS, C0S_RR, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U19.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split; [exact I | exact I]]. unfold C0S_facts. cbn [f_atoms atoms_ok].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U18, Z.pow_0_r, Z.mod_1_r; unfold SHADOW_OFF, C0S_SB; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U19; change (2 ^ 3) with 8|].
    { split; [lia|]. split; [|lia]. apply Z.mod_divide in Hr16; [|lia]. destruct Hr16 as [q Hq].
      replace (r + 56 * n) with ((2 * q + 7 * n) * 8) by lia. apply Z_mod_mult. }
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite F32, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia|].
    exact I. }
assert (SHOK : sh_ok SEGS (SOff 18 0) C0S_SH E (mrestrict (w_H W3) (ms_mem ms3))).
{ unfold sh_ok, C0S_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E (SOff 18 0) 19 r 288 (r + 56 * n) 0 56).
  - apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 r REG_SIZE r 288 HAR3 Hrin3);
      change (req_size REG_SIZE) with 288; lia.
  - rewrite U_SOff, U18, Z.add_0_r. apply c0_zcanon_in. unfold SHADOW_OFF; lia.
  - rewrite U_SOff, U19, Z.add_0_r. apply c0_zcanon_in. lia.
  - lia.
  - lia.
  - intros x Hx Hxs. rewrite Z.min_l, Z.max_r in Hx by lia. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. clear - Hria Hx Hxs Hn4. lia. }
apply (st_ok_pi_pin_reg' E _ _ 10%bv 0) in HS; [| cbn [restrict ms_regs]; exact R10 | reflexivity].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.

paj_run_tok (paj_run B LAWS) HS HJ SHOK (C0S_SB, C0S_SB + 2 ^ 44 - 1); [awr_ok_tac|].
assert (M1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. apply (c0_keep_outside E _ _ _ (w_H W3) a HF Ha). cbn. intros (rr & [<- | [<- | []]] & Hb); cbn in Hb; lia. }
clear HF HFr HG.

psrr_branch_tok (paj_run B LAWS) (paj_branch (PI := PI)) HS SHOK (C0S_SB, C0S_SB + 2 ^ 44 - 1).

{ exfalso. rewrite (c0s_sra_or E b 23 F32) in Hc by lia. rewrite branch_ne_U, Z.eqb_refl in Hc. discriminate Hc. }
clear Hc.
paj_run_to_tok (paj_run_to B LAWS) HS HJ SHOK (C0S_SB, C0S_SB + 2 ^ 44 - 1) GC_F; [awr_ok_tac|].
assert (M2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem ms0) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. rewrite <- (M1 a Ha). apply (c0_keep_outside E _ _ _ (w_H W3) a HF Ha). cbn. intros (rr & [<- | [<- | []]] & Hb); cbn in Hb; lia. }
clear HF HFr HG M1.

prreg HS (2%bv : bv 5) T2. prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (3%bv : bv 5) T3.
prreg HS (4%bv : bv 5) T4. prreg HS (18%bv : bv 5) T18. prreg HS (24%bv : bv 5) T24. prreg HS (20%bv : bv 5) T20.
prreg HS (25%bv : bv 5) T25.
pmkst HS.

assert (Hnk : 0 <= c0_nk cx pos <= 47) by (unfold c0_nk; pose proof (LLVMFuzzerTestOneInput_rn.rn_k_range (c0_pl2 cx pos)); lia).
assert (ZR : forall a, c0_zone cx fp a -> 0 <= a < 2 ^ 64).
{ pose proof (c0_geo LAWS cx fp k ly3 S3 W3 _ _ HB HJ HFR) as (Hinp & EgF & HF0 & HF1 & HF64 & HSH0).
  intros a; apply c0_zone_range; first [exact Hinp | lia | exact HSH0]. }
repeat rewrite wvb_collapse in HJ.
eapply (HNX cx fp k acc ly3 S3 W3 (mkst (ms_regs ms0) (Z_to_bv 64 (BASE + 2904)) (ms_mem ms0) (seg_rom SEGS)) _ HB HJ HFR HMO).
unfold C0_F. exists r, bs, (c0_placed bs b (c0_nch cx pos) p (c0_gs cx pos op)), (c0_pos2 cx pos), nm, (c0_nk cx pos + 1).
split.
{ unfold c0_ms. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs mkst].
  do 6 (split; [reflexivity|]). unfold gregs. cbn [ms_regs mkst].
  rewrite T2, T8, T9, T3, T4, T18, T24, (EE 2%nat 2%bv eq_refl), (EE 8%nat 8%bv eq_refl), (EE 9%nat 9%bv eq_refl),
    (EE 3%nat 3%bv eq_refl), (EE 4%nat 4%bv eq_refl), (EE 18%nat 18%bv eq_refl), (EE 24%nat 24%bv eq_refl).
  exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HMS)))))). }
split; [apply (c0_mf_keep i cx fp W3 ms3 _ r bs HB); [intros a Ha; cbn [ms_mem mkst]; apply M2; exact (ZR a Ha) | exact HMF]|].
split; [exact Hi|]. split; [exact Hk|]. split; [lia|]. split; [exact Hacc|]. split; [exact HBL|]. split; [exact Hnm|].
split.
{ destruct HREG as (HR1 & HR2 & HR3). split; [exact HR1|]. split; [exact HR2|].
  intros j Hj. cbn [ms_mem mkst]. rewrite M2 by (unfold REG_SIZE in Hj; lia). exact (HR3 j Hj). }
split; [exact HINV|].
split; [exact (reac_boxreg_declare_inv.reac_boxreg_declare_keeps_inv_holds bs (c0_gs cx pos op) _ _ _ _ HINV HPL)|].
split; [exact (LLVMFuzzerTestOneInput_case0.c0_decl_fabric bs b _ p _ HL Hn4)|].
split; [exact (LLVMFuzzerTestOneInput_case0.c0_kept_placed bs b _ p _ HINV Hn5)|].
assert (KS : forall off v, 0 <= off < 0x98 -> gslot cx W3 ms3 off v ->
  gslot cx W3 (mkst (ms_regs ms0) (Z_to_bv 64 (BASE + 2904)) (ms_mem ms0) (seg_rom SEGS)) off v).
{ intros off v Hoff Hv. unfold gslot in *. cbn [ms_mem mkst]. rewrite <- Hv. apply rdword_ext.
  intros j Hj. apply M2. lia. }
split; [destruct HCUR as (C1' & C88 & C90); split; [exact C1'|]; split; apply KS; first [lia | assumption]|].
split; [apply KS; [lia | exact S58]|].
split; [cbn [ms_regs mkst]; rewrite T20, (EE 20%nat 20%bv eq_refl); exact R20|].
cbn [ms_regs mkst]; rewrite T25, F33. reflexivity.
Qed.

End c.
End b.
End a.
