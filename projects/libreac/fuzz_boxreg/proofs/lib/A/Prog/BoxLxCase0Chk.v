(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (the leaf walk: the seed at
   the entry, the run, the return) and lib/A/AC8b.v (loops by fuel induction) at c8557374ad2e: the walk of
   syntax_reply_matches on fuzz_command.asan. This file: the prologue (0x8857c to the item loop at 0x885e8), the entry
   facts the statement's premises give, and the theorem. The segments are in syntax_reply_matches_s1.v .. _s7.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/syntax_reply_matches.v, with its module paths and module names changed; 645 of its 702 lines of code are new or changed and 209 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/ReacBoxregFind.v, with its module paths and module names changed; 1143 of its 1180 lines of code are new or changed and 665 lines of the source are left out. *)
(* The checks of LLVMFuzzerTestOneInput's case 0 after reac_boxreg_declare returned (fuzz_boxreg.c:228-279) on the
   ASan build: from the cut D (0x80960, BoxLxCase0Defs.v) `mv s7, a0` takes the index the call returned and the code
   checks it against the table.

   Refused (idx = -1, the table unchanged; Pau's c0_link_refused makes want = -1 too):
     0x80968 `beq s7, -1` -> 0x80974 (taken), 0x80974 `ld a0, 0x60(s1); lb a0, 0(a0)` reads the shadow byte of
     r + 280, which is 0 (the AR block-shadow law of r, al_shadow: r is 16-aligned, so r + 280 is the 36th whole
     granule of the 288-byte block), so `bnez a0` -> 0x80d44 is not taken; 0x80980 `ld a0, 0x40(s1); lw a0, 0(a0)`
     reads r->n = n; `bltz s7` -> 0x80a88 (taken, s7 = -1); 0x80a88 `ld a1, 0x48(s1)` (n), `bne a0, a1` -> 0x80f60
     is decided by the engine (both are atom 33); `ld a0, 0x30(s1)` (want = -1), `sraiw a0, a0, 31; or a0, a0, a1`
     leaves -1 (c0d_or_ones), `ld s9, 0x50(s1)` (the fabric) and `bne s7, a0` -> 0x80f60 is refuted (both -1);
     0x80aa4 = the cut F with bs' = bs (llvm_kept by Pau's c0_kept_refl).

   Placed (idx = n, the new row at r + 56 n):
     0x80968 not taken, 0x80970 `bne s7, 0x48(s1)` -> 0x80f60 not taken (both the pinned literal n), the shadow byte
     of r + 280 is 0 as above, 0x80984 reads r->n = n + 1 (Pau's c0_decl_n), `bltz s7` not taken, 0x80990
     `addiw a1, a1, 1` and `bne a0, a1` -> 0x80f60 not taken (both the literal n + 1), 0x80998 `slli/slli/sub/add`
     makes s6 = r + 56 n, 0x809a8 the checked `lw` of the row's nch field at s6 + 12 (the engine's shadow token from
     the SH entry of the r block, so the slow path 0x80d74 and its report at 0x80fc4 are not taken; the field is nch
     by c0_row_bsub and decl_row_nch) and `bne a0, s3` -> 0x80f60 is decided by the engine (both are atom 19), then
     `auipc/addi` put ZERO (A_OBJ 6) in a1, a2 = 6, a0 = s6, and 0x809d4 `jal bcmp` is the call YCbq.v aj_bcmp_at
     composes with ABCMP; its post gives a0 = 0 because the row's six mac bytes are zero (decl_row_mac) and ZERO's
     six bytes are zero (HZERO read through arodata_okP with pa's lib/A/Rt/StrncmpView.v fm_rom_viewN_of_arodata). The return slot
     0x809d8 is the cut B.
   The row's address r + 56 n folds to a literal offset only for a literal n, so the placed walk is done once for
   each n of Pau's boxreg_B1 range (0 .. 4, bx_n bs < 5 from declare_placed): the five blocks below are the same
   text with the index pinned (st_ok_pi_pin_reg') to 0, 1, 2, 3, 4. *)
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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxLxCase0Fin.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import SnprintfDef StrncmpDef StrncmpView.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Definition C0D_SB : Z := 0x7fff8000.
(* refused: slots 0x30 (want = -1), 0x40 (r + 280 = s4's atom 20 + 280), 0x48 (n, atom 33), 0x50 (fabric, atom 32),
   0x60 (the shadow byte's address of r + 280, atom 34); that shadow byte (0); r->n at r + 280 (n, atom 33). *)
Definition C0D_RSr : YP09.region := YP09.mkRegion (Some 9%nat) 0x30 0x68 0 0
  [YP09.mkChunk 0x30 (CVal 8 (SLit 18446744073709551615)); YP09.mkChunk 0x40 (CVal 8 (SOff 20 280));
   YP09.mkChunk 0x48 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x50 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x60 (CVal 8 (SOff 34 0))].
Definition C0D_RH : YP09.region := YP09.mkRegion (Some 34%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition C0D_RNr : YP09.region := YP09.mkRegion (Some 20%nat) 280 284 0 0 [YP09.mkChunk 280 (CVal 4 (SOff 33 0))].
Definition C0D_factsr : facts :=
  mkFacts [(18%nat, mkAF C0D_SB C0D_SB 0); (20%nat, mkAF 4096 140737479966720 4); (33%nat, mkAF 0 5 0)] [] [].

Definition C0D_RSp (nn : Z) : YP09.region := YP09.mkRegion (Some 9%nat) 0x40 0x68 0 0
  [YP09.mkChunk 0x40 (CVal 8 (SOff 20 280)); YP09.mkChunk 0x48 (CVal 8 (SLit nn)); YP09.mkChunk 0x60 (CVal 8 (SOff 34 0))].
Definition C0D_RNp (nn : Z) : YP09.region := YP09.mkRegion (Some 20%nat) 280 284 0 0 [YP09.mkChunk 280 (CVal 4 (SLit (nn + 1)))].
Definition C0D_RRp (nn : Z) : YP09.region := YP09.mkRegion (Some 20%nat) (56 * nn) (56 * nn + 56) 0 0
  [YP09.mkChunk (56 * nn + 12) (CVal 4 (SOff 19 0))].
Definition C0D_factsp : facts :=
  mkFacts [(18%nat, mkAF C0D_SB C0D_SB 0); (19%nat, mkAF 0 255 0); (20%nat, mkAF 4096 140737479966720 4)] [] [].
Definition C0D_SHp : list shent := [mkSHE 20 0 288].

Lemma c0d_or_ones : forall E x, sv_denot E (SAlu ALU_OR (SLit 18446744073709551615) x) = sv_denot E (SLit 18446744073709551615).
Proof.
intros E x. cbn [sv_denot]. apply bv_eq. unfold alu64, alu. rewrite bv_or_unsigned.
change (bv_unsigned (Z_to_bv 64 18446744073709551615)) with 18446744073709551615.
rewrite LLVMFuzzerTestOneInput_case0.c0_lor1. reflexivity.
Qed.

Lemma c0d_placed_n : forall bs b k p s, length bs = 288%nat -> 0 <= Boxreg.bx_n bs <= 4 ->
  Boxreg.bx_n (c0_placed bs b k p s) = Boxreg.bx_n bs + 1.
Proof.
intros bs b k p s HL Hn. unfold c0_placed.
change (BoxregUpd.new_row_bytes bs (reac_boxreg_declare_c.decl_row b k p s))
  with (reac_boxreg_declare_c.decl_bytes bs b k p s).
apply LLVMFuzzerTestOneInput_case0.c0_decl_n; [exact HL | exact Hn].
Qed.

Lemma c0d_zero6_nth : forall j, 0 <= j < 6 -> nth (Z.to_nat j) (map (fun b : byte => bv_unsigned b) Boxreg.zero6) 0 = 0.
Proof.
intros j Hj. assert (H6 : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5) by lia.
destruct H6 as [H|[H|[H|[H|[H|H]]]]]; rewrite H; reflexivity.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg box_listing}.
Context {RO : ro_below_ofl (@pa_segs _ box_listing PI) pa_relro_lo pa_relro_hi}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).

(* One byte of memory as the engine's 1-byte chunk. *)
Lemma c0c_vm1 : forall (H : word -> bool) (mem : word -> option byte) a v,
  aview SEGS H mem a = Some v -> val_mem SEGS (mrestrict H mem) a 1 v.
Proof.
intros H mem a v Ha. destruct (aview_byte SEGS H mem a v Ha) as (b & Hb & -> & _).
intros k Hk. assert (k = 0%nat) as -> by lia. rewrite Z.add_0_r, Hb. f_equal.
pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
assert (HL : forall x, 0 <= x < 256 -> YO0f.le_byte x 1 0 = x).
{ intros x Hx. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. rewrite (Z.mod_small x (2 ^ 8)) by (change (2 ^ 8) with 256; lia). apply Z.mod_small. lia. }
apply bv_eq. rewrite Z_to_bv_unsigned. rewrite HL by lia. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.mod_small by lia. reflexivity.
Qed.
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HISV : img_shadow_vis SEGS B.
Hypothesis HGLOB : globs_marked SEGS B BX_G.
Hypothesis HMRG : Forall (fun g => IMG_LO + 64 <= fst g /\ fst g + snd g + 64 <= IMG_HI) BX_G.
Hypothesis HZERO : asn_rom_bytes SEGS B (VAL (A_OBJ 6)) (map (fun b : byte => bv_unsigned b) Boxreg.zero6).
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA BS___interceptor_trampoline_bcmp).


Theorem c0_chk : forall i POST, gb_from B MT POST (C0_F B MT i) -> gb_from B MT POST (C0_B B MT i) ->
  gb_from B MT POST (C0_D B MT i).
Proof.
intros i POST HNF HNB cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
destruct HI as (r & bs & pos & op & nm & want & HMS & HTURN & HWANT & Hwr & S30 & S58 & R19 & R22 & R25 & R26 & R27 & HDEC).
destruct HTURN as (HMF & Hi & Hk & Hacc & HBL & HINV & Hpos & HCUR & Hnm & HNAME & Hop & Hop3 & R20).
pose proof HMS as (_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G3 & G4 & G18 & G24)).
pose proof HMF as (HSV & HSH & HFL & HSFR & HINP & HPREV & (S10 & S20 & S38 & S40 & S50 & S60) & S68 & S48).
pose proof HINV as ((HL & HB1 & HB2 & _) & _). unfold Boxreg.boxreg_B1 in HB1. unfold Boxreg.boxreg_B2 in HB2.
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
set (sh := shadow_of_addr SHADOW_OFF (r + 280)) in *.
assert (Hsh0 : aview SEGS (w_H W3) (ms_mem ms3) sh = Some 0).
{ destruct (al_shadow _ _ LAWS _ _ _ _ _ r REG_SIZE HAR3 Hrin3) as ((_ & _ & Hbs) & _).
  change (req_size REG_SIZE) with 288 in Hbs. pose proof (Hbs 35 ltac:(split; [lia | reflexivity])) as X. cbn in X.
  replace (shadow_of_addr SHADOW_OFF r + 35) with sh in X; [exact X|].
  subst sh. unfold shadow_of_addr. pose proof (Z.div_mod r 8 ltac:(lia)). pose proof (Z.mod_pos_bound r 8 ltac:(lia)).
  pose proof (Z.div_mod (r + 280) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (r + 280) 8 ltac:(lia)).
  apply Z.mod_divide in Hr16; [|lia]. destruct Hr16 as [q Hq]. lia. }
assert (Hshr : SHADOW_OFF <= sh < SHADOW_OFF + 2 ^ 44).
{ subst sh. unfold shadow_of_addr. pose proof (Z.div_pos (r + 280) 8 ltac:(lia) ltac:(lia)).
  assert ((r + 280) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }

assert (ZR : forall a, c0_zone cx fp a -> 0 <= a < 2 ^ 64).
{ pose proof (c0_geo LAWS cx fp k ly3 S3 W3 _ _ HB HJ HFR) as (Hinp & EgF & HF0 & HF1 & HF64 & HSH0).
  intros a; apply c0_zone_range; first [exact Hinp | lia | exact HSH0]. }
assert (Hnk : 0 <= c0_nk cx pos <= 47) by (unfold c0_nk; pose proof (LLVMFuzzerTestOneInput_rn.rn_k_range (c0_pl2 cx pos)); lia).
assert (Hnmin : In (nm, c0_nk cx pos + 1) (ablocks B ly3 S3)) by (rewrite HBL; apply in_or_app; right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ nm (c0_nk cx pos + 1) HAR3 Hnmin) as (_ & _ & Hnceil & _).
pose proof (req_size_pos (c0_nk cx pos + 1) ltac:(lia)) as (_ & Hrq).
destruct HDEC as [(HREF & HREG & R10) | (b & p & HPL & HREG & R10)].
- (* refused: idx = -1, bs' = bs *)
  pose proof (LLVMFuzzerTestOneInput_case0.c0_link_refused _ _ _ _ HWANT HREF) as Ew. subst want.
  set (E := Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 fab; Z_to_bv 64 n; Z_to_bv 64 sh])).
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E q = getr (ms_regs ms3) r)
    by (intros q r0 Hq; subst E; apply ew_Eimg_Ereg_nat; exact Hq).
  assert (F32 : ew E 32 = Z_to_bv 64 fab) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
  assert (F33 : ew E 33 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
  assert (F34 : ew E 34 = Z_to_bv 64 sh) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 2)).
  assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite (EE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
  assert (U20 : bv_unsigned (ew E 20) = r) by (rewrite (EE 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; lia).
  assert (U18 : bv_unsigned (ew E 18) = SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U34 : bv_unsigned (ew E 34) = sh) by (rewrite F34; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
  assert (HS : st_ok_pi SEGS VAL E (mkSS GC_D sr_atoms [C0D_RSr; C0D_RH; C0D_RNr] None C0D_factsr) (restrict (w_H W3) ms3)).
  { rewrite (c0_mkst cx fp GC_D ms3 (w_H W3) HMS). apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold C0D_RSr, C0D_RH, C0D_RNr. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        repeat apply Forall_cons; try apply Forall_nil.
        * apply (chunk_ok_val SEGS _ _ _ 0x30 8%N (SLit 18446744073709551615) 18446744073709551615); [reflexivity | cbn; lia | cbn; lia |].
          apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact S30.
        * apply (chunk_ok_val SEGS _ _ _ 0x40 8%N (SOff 20 280) (r + 280)); [cbn [sv_denot]; rewrite U20; reflexivity | cbn; lia | cbn; lia |].
          apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact S40.
        * apply (chunk_ok_val SEGS _ _ _ 0x48 8%N (SOff 33 0) n); [rewrite c0_denot_off0; exact F33 | cbn; lia | cbn; lia |].
          apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact S48.
        * apply (chunk_ok_val SEGS _ _ _ 0x50 8%N (SOff 32 0) fab); [rewrite c0_denot_off0; exact F32 | cbn; lia | cbn; lia |].
          apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact S50.
        * apply (chunk_ok_val SEGS _ _ _ 0x60 8%N (SOff 34 0) sh); [rewrite c0_denot_off0; exact F34 | cbn; unfold SHADOW_OFF in *; lia | cbn; lia |].
          apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact S60.
      + rewrite U34. split; [unfold SHADOW_OFF in *; lia|]. split; [unfold SHADOW_OFF in *; lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS _ _ _ 0 1%N (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. apply c0c_vm1. exact Hsh0.
      + rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS _ _ _ 280 4%N (SOff 33 0) n); [rewrite c0_denot_off0; exact F33 | cbn; lia | cbn; lia |].
        destruct HREG as (_ & HRL & HRB).
        apply (c0c_vm4 (w_H W3) (ms_mem ms3) r bs 280 n HRB HRL); [lia | lia | | lia].
        symmetry. apply BoxregRd.le4_rd4. rewrite Boxreg.bsub_length by (rewrite ?HRL; lia). reflexivity.
    - apply pairwise_disjoint_of_extents. unfold C0D_RSr, C0D_RH, C0D_RNr, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U20, U34.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. repeat split; lia.
    - split; [|split; [exact I | exact I]]. unfold C0D_factsr. cbn [f_atoms atoms_ok].
      split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U18, Z.pow_0_r, Z.mod_1_r; unfold SHADOW_OFF, C0D_SB; lia|].
      split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U20; change (2 ^ 4) with 16; lia|].
      split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite F33, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia|].
      exact I. }
  assert (SHOK : sh_ok SEGS (SOff 18 0) [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  apply (st_ok_pi_pin_reg' E _ _ 10%bv (-1)) in HS; [| cbn [restrict ms_regs]; exact R10 | reflexivity].
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.

  paj_run_tok (paj_run B LAWS) HS HJ SHOK (C0D_SB, C0D_SB + 2 ^ 44 - 1); [awr_ok_tac|].
  assert (M1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha. apply (c0_keep_outside E _ _ _ (w_H W3) a HF Ha). cbn. intros (rr & [<- | [<- | [<- | []]]] & Hb); cbn in Hb; lia. }
  clear HF HFr HG.
  psrr_branch_tok (paj_run B LAWS) (paj_branch (PI := PI)) HS SHOK (C0D_SB, C0D_SB + 2 ^ 44 - 1).
  { exfalso. rewrite c0d_or_ones in Hc. rewrite branch_ne_U, Z.eqb_refl in Hc. discriminate Hc. }
  clear Hc.
  paj_run_to_tok (paj_run_to B LAWS) HS HJ SHOK (C0D_SB, C0D_SB + 2 ^ 44 - 1) GC_F; [awr_ok_tac|].
  assert (M2 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem ms0) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha. rewrite <- (M1 a Ha). apply (c0_keep_outside E _ _ _ (w_H W3) a HF Ha). cbn. intros (rr & [<- | [<- | [<- | []]]] & Hb); cbn in Hb; lia. }
  clear HF HFr HG M1.

  prreg HS (2%bv : bv 5) T2. prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (3%bv : bv 5) T3.
  prreg HS (4%bv : bv 5) T4. prreg HS (18%bv : bv 5) T18. prreg HS (24%bv : bv 5) T24. prreg HS (20%bv : bv 5) T20.
  prreg HS (25%bv : bv 5) T25.
  pmkst HS.
  repeat rewrite wvb_collapse in HJ.
  eapply (HNF cx fp k acc ly3 S3 W3 (mkst (ms_regs ms0) (Z_to_bv 64 (BASE + 2904)) (ms_mem ms0) (seg_rom SEGS)) _ HB HJ HFR HMO).
  unfold C0_F. exists r, bs, bs, (c0_pos2 cx pos), nm, (c0_nk cx pos + 1).
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
  split; [exact HINV|]. split; [exact HINV|]. split; [reflexivity|].
  split; [exact (LLVMFuzzerTestOneInput_case0.c0_kept_refl bs)|].
  assert (KS : forall off v, 0 <= off < 0x98 -> gslot cx W3 ms3 off v ->
    gslot cx W3 (mkst (ms_regs ms0) (Z_to_bv 64 (BASE + 2904)) (ms_mem ms0) (seg_rom SEGS)) off v).
  { intros off v Hoff Hv. unfold gslot in *. cbn [ms_mem mkst]. rewrite <- Hv. apply rdword_ext.
    intros j Hj. apply M2. lia. }
  split; [destruct HCUR as (C1' & C88 & C90); split; [exact C1'|]; split; apply KS; first [lia | assumption]|].
  split; [apply KS; [lia | exact S58]|].
  split; [cbn [ms_regs mkst]; rewrite T20, (EE 20%nat 20%bv eq_refl); exact R20|].
  cbn [ms_regs mkst]; rewrite T25, F32. reflexivity.

- (* placed *)
  pose proof (LLVMFuzzerTestOneInput_case0.c0_link_placed _ _ _ _ _ _ HWANT HPL) as Ewb. subst want.
  pose proof HPL as (Hbw & Hn5 & Hpl).
  assert (Hb0 : 0 <= b) by (destruct Hpl as [(X1 & X2 & _) | (_ & _ & X3 & _)]; lia).
  assert (Hnchr : 0 <= c0_nch cx pos < 256) by (unfold c0_nch; apply LLVMFuzzerTestOneInput_case0.c0_nch_range).
  assert (H5 : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4) by lia.
  set (E := Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 fab; Z_to_bv 64 n; Z_to_bv 64 sh])).
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E q = getr (ms_regs ms3) r)
    by (intros q r0 Hq; subst E; apply ew_Eimg_Ereg_nat; exact Hq).
  assert (F34 : ew E 34 = Z_to_bv 64 sh) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 2)).
  assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite (EE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
  assert (U20 : bv_unsigned (ew E 20) = r) by (rewrite (EE 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; lia).
  assert (U19 : bv_unsigned (ew E 19) = c0_nch cx pos) by (rewrite (EE 19%nat 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
  assert (U18 : bv_unsigned (ew E 18) = SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U34 : bv_unsigned (ew E 34) = sh) by (rewrite F34; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
  assert (E20w : ew E 20 = w64 r) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
  assert (F247 : ew E 247 = Z_to_bv 64 (VAL (A_OBJ 6))) by (subst E; apply (Eimg_img _ (A_OBJ 6)); unfold A_OBJ, A_TEXT, A_LIM; lia).
  destruct HREG as (HRin & HRLp & HRB). assert (Hnp : Boxreg.bx_n bs = n) by reflexivity.
  assert (Hdb : forall o w, 0 <= o -> 0 <= w -> o + w <= 56 ->
    Boxreg.bsub (c0_placed bs b (c0_nch cx pos) p (c0_gs cx pos op)) (56 * n + o) w =
    Boxreg.bsub (reac_boxreg_declare_c.decl_row b (c0_nch cx pos) p (c0_gs cx pos op)) o w).
  { intros o w Ho Hw How. unfold c0_placed.
    change (BoxregUpd.new_row_bytes bs (reac_boxreg_declare_c.decl_row b (c0_nch cx pos) p (c0_gs cx pos op)))
      with (reac_boxreg_declare_c.decl_bytes bs b (c0_nch cx pos) p (c0_gs cx pos op)).
    subst n. apply (LLVMFuzzerTestOneInput_case0.c0_row_bsub bs b _ p _ o w HL); lia. }
  destruct H5 as [Hn|[Hn|[Hn|[Hn|Hn]]]].

  + rewrite Hn in R10.
    assert (HS : st_ok_pi SEGS VAL E (mkSS GC_D sr_atoms [C0D_RSp 0; C0D_RH; C0D_RNp 0; C0D_RRp 0] None C0D_factsp) (restrict (w_H W3) ms3)).
    { rewrite (c0_mkst cx fp GC_D ms3 (w_H W3) HMS). apply pa_entry_st_ok_full.
      - apply regs_ok_Eimg_Ereg.
      - vm_compute. reflexivity.
      - unfold C0D_RSp, C0D_RH, C0D_RNp, C0D_RRp. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
          repeat apply Forall_cons; try apply Forall_nil.
          * apply (chunk_ok_val SEGS _ _ _ 0x40 8%N (SOff 20 280) (r + 280)); [cbn [sv_denot]; rewrite U20; reflexivity | cbn; lia | cbn; lia |].
            apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact S40.
          * apply (chunk_ok_val SEGS _ _ _ 0x48 8%N (SLit 0) n); [rewrite Hn; reflexivity | cbn; lia | cbn; lia |].
            apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact S48.
          * apply (chunk_ok_val SEGS _ _ _ 0x60 8%N (SOff 34 0) sh); [rewrite c0_denot_off0; exact F34 | cbn; unfold SHADOW_OFF in *; lia | cbn; lia |].
            apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact S60.
        + rewrite U34. split; [unfold SHADOW_OFF in *; lia|]. split; [unfold SHADOW_OFF in *; lia|]. split; [intros o Ho; lia|].
          apply Forall_cons; [|apply Forall_nil].
          apply (chunk_ok_val SEGS _ _ _ 0 1%N (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
          rewrite Z.add_0_r. apply c0c_vm1. exact Hsh0.
        + rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
          apply Forall_cons; [|apply Forall_nil].
          apply (chunk_ok_val SEGS _ _ _ 280 4%N (SLit (0 + 1)) (n + 1)); [rewrite Hn; reflexivity | cbn; lia | cbn; lia |].
          apply (c0c_vm4 (w_H W3) (ms_mem ms3) r _ 280 (n + 1) HRB HRLp); [lia | lia | | lia].
          symmetry. rewrite <- (BoxregRd.le4_rd4 _ 280) by (rewrite Boxreg.bsub_length; [reflexivity | lia | lia | rewrite HRLp; lia]).
          do 2 f_equal. change (Boxreg.rd4 (c0_placed bs b (c0_nch cx pos) p (c0_gs cx pos op)) 280)
            with (Boxreg.bx_n (c0_placed bs b (c0_nch cx pos) p (c0_gs cx pos op))).
          symmetry. apply c0d_placed_n; [exact HL | lia].
        + rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
          apply Forall_cons; [|apply Forall_nil].
          apply (chunk_ok_val SEGS _ _ _ (56 * 0 + 12) 4%N (SOff 19 0) (c0_nch cx pos));
            [rewrite c0_denot_off0, (EE 19%nat 19%bv eq_refl), R19; reflexivity | cbn; lia | cbn; lia |].
          apply (c0c_vm4 (w_H W3) (ms_mem ms3) r _ (56 * 0 + 12) (c0_nch cx pos) HRB HRLp); [lia | lia | | lia].
          replace (56 * 0 + 12) with (56 * n + 12) by lia.
          rewrite (Hdb 12 4) by lia. apply reac_boxreg_declare_inv.decl_row_nch.
      - apply pairwise_disjoint_of_extents. unfold C0D_RSp, C0D_RH, C0D_RNp, C0D_RRp, extent_of_region.
        cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U20, U34.
        cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
        unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. repeat split; lia.
      - split; [|split; [exact I | exact I]]. unfold C0D_factsp. cbn [f_atoms atoms_ok].
        split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U18, Z.pow_0_r, Z.mod_1_r; unfold SHADOW_OFF, C0D_SB; lia|].
        split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U19, Z.pow_0_r, Z.mod_1_r; lia|].
        split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U20; change (2 ^ 4) with 16; lia|].
        exact I. }
    assert (SHOK : sh_ok SEGS (SOff 18 0) C0D_SHp E (mrestrict (w_H W3) (ms_mem ms3))).
    { unfold sh_ok, C0D_SHp. apply Forall_cons; [|apply Forall_nil].
      apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E (SOff 18 0) 20 r 288 r 0 288).
      - apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 r REG_SIZE r 288 HAR3 Hrin3);
          change (req_size REG_SIZE) with 288; lia.
      - rewrite U_SOff, U18, Z.add_0_r. apply c0_zcanon_in. unfold SHADOW_OFF; lia.
      - rewrite U_SOff, U20, Z.add_0_r. apply c0_zcanon_in. lia.
      - lia.
      - lia.
      - intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
        unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. clear - Hria Hx. lia. }
    apply (st_ok_pi_pin_reg' E _ _ 10%bv 0) in HS; [| cbn [restrict ms_regs]; exact R10 | reflexivity].
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.

    paj_run_tok (paj_run B LAWS) HS HJ SHOK (C0D_SB, C0D_SB + 2 ^ 44 - 1); [awr_ok_tac|].

    assert (M1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha. apply (c0_keep_outside E _ _ _ (w_H W3) a HF Ha). cbn.
      intros (rr & [<- | [<- | [<- | [<- | []]]]] & Hb); cbn in Hb; lia. }
    clear HF HFr HG.
    pose proof HJ as (HARj & _).
    assert (HZlo6 : IMG_LO + 64 <= VAL (A_OBJ 6) /\ VAL (A_OBJ 6) + 6 + 64 <= IMG_HI).
    { rewrite Forall_forall in HMRG. pose proof (HMRG (VAL (A_OBJ 6), 6) ltac:(unfold BX_G; cbn [In]; tauto)) as Hm.
      cbn [fst snd] in Hm. exact Hm. }
    destruct HZlo6 as (HZlo6 & HZhi6).
    pmkst HS.
    prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
    prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
    prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
    prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
    prreg HS (9%bv : bv 5) Q9. prreg HS (8%bv : bv 5) Q8. prreg HS (18%bv : bv 5) Q18. prreg HS (24%bv : bv 5) Q24.
    pose proof HB as (HPRE0 & _ & _ & _ & _ & _ & _ & _ & HARO & _).
    pose proof HPRE0 as (_ & _ & _ & Hgp & Htp & _).
    assert (Usp : spZ (ms_regs ms) = c_sp1 cx) by (unfold spZ; rewrite Q2, (EE 2%nat 2%bv eq_refl), G2; unfold w64; apply unsigned_lit_small; lia).
    pose proof (pa_obj_img 6 ltac:(lia)) as Hzimg.
    assert (HARO1 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) (ms_mem ms)))
      by exact (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HARO).
    assert (HZB : forall j, 0 <= j < 6 -> aview SEGS (w_H W3) (ms_mem ms) (VAL (A_OBJ 6) + j) = Some 0).
    { intros j Hj.
      destruct (HZERO j ltac:(rewrite length_map; cbn [length Boxreg.zero6 repeat]; lia)) as (Hro & Ho & He & Hv).
      rewrite (fm_rom_viewN_of_arodata SEGS B pa_relro_lo pa_relro_hi W3 (ms_mem ms) HARO1 _ Hro Ho He), Hv.
      f_equal. apply c0d_zero6_nth. exact Hj. }
    assert (HRB1 : forall j, 0 <= j < REG_SIZE ->
      aview SEGS (w_H W3) (ms_mem ms) (r + j) = Some (bv_unsigned (nth (Z.to_nat j) (c0_placed bs b (c0_nch cx pos) p (c0_gs cx pos op)) (Z_to_bv 8 0))))
      by (intros j Hj; rewrite M1 by (unfold REG_SIZE in Hj; lia); exact (HRB j Hj)).
    eapply SRr_bind.
    { eapply (aj_bcmp_at SEGS B LAWS Hsegs (SIGMA BS___interceptor_trampoline_bcmp) ABCMP W3 (ms_regs ms) (ms_mem ms)
        GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 _ k
        (r + 56 * 0) (VAL (A_OBJ 6)) 6 (c_sp1 cx - spZ (c_regs cx)) (Z_to_bv 64 (BASE + 2700)) HJ).
      - rewrite Q10, E20w. unfold w64. rewrite ?unsigned_lit_small by lia. f_equal; lia.
      - rewrite Q11, F247. reflexivity.
      - rewrite Q12. reflexivity.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - rewrite Usp. lia.
      - apply c0_sub_mod16; [exact Hsp32 | exact Hsp16].
      - lia.
      - change ESTACK with 4096. unfold GB_STK. lia.
      - rewrite Q3, (EE 3%nat 3%bv eq_refl), G3. exact Hgp.
      - rewrite Q4, (EE 4%nat 4%bv eq_refl), G4. exact Htp.
      - exact Q1.
      - apply ret_ok_codeptr_v; [lia | reflexivity].
      - intros a Ha. split.
        + replace a with (r + (a - r)) by lia. rewrite HRB1 by (unfold REG_SIZE; lia). discriminate.
        + rewrite Usp. change ESTACK with 4096. lia.
      - intros a Ha. split.
        + replace a with (VAL (A_OBJ 6) + (a - VAL (A_OBJ 6))) by lia. rewrite HZB by lia. discriminate.
        + rewrite Usp. change ESTACK with 4096. lia.
      - intros a Ha. change ESTACK with 4096. lia.
      - intros a Ha. change ESTACK with 4096. lia.
      - apply (amem_range_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 r REG_SIZE _ _ HAR3 Hrin3);
          change (req_size REG_SIZE) with 288; lia.
      - unfold amem_range, kLowMemEnd. lia.
      - apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms) _ r REG_SIZE _ _ HARj Hrin3);
          change (req_size REG_SIZE) with 288; lia.
      - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms) _ r REG_SIZE _ _ HARj Hrin3);
          change (req_size REG_SIZE) with 288; lia.
      - apply (proj1 (ro_read_ok_glob SEGS B BX_G ly3 S3 W3 (ms_mem ms) _ (VAL (A_OBJ 6)) 6 (VAL (A_OBJ 6)) 6
          HGLOB ltac:(unfold BX_G; cbn [In]; tauto) HISV HARj ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
      - intros _. apply (proj2 (ro_read_ok_glob SEGS B BX_G ly3 S3 W3 (ms_mem ms) _ (VAL (A_OBJ 6)) 6 (VAL (A_OBJ 6)) 6
          HGLOB ltac:(unfold BX_G; cbn [In]; tauto) HISV HARj ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))). }

    cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr & Hpr2).
    assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx - 8192 <= a < c_sp1 cx) ->
      aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha Hna. rewrite Hfr by (change ESTACK with 4096; lia). apply M1. exact Ha. }
    assert (KZ : forall a, c0_zone cx fp a -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha. pose proof (ZR a Ha) as Ha64. apply KM; [exact Ha64|].
      pose proof (c0_geo LAWS cx fp k ly3 S3 W3 _ _ HB HJ HFR) as (Hinp & _ & HFa & HFb & _ & HSHe).
      destruct Ha as [Ha|[Ha|[Ha|Ha]]]; [lia | destruct Hinp; lia | lia |].
      rewrite HSHe in Ha. unfold SHADOW_OFF in *.
      pose proof (Z.div_le_upper_bound (gF cx fp) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
    assert (KP2 : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> getr regs2 r0 = getr (ms_regs ms) r0)
      by (intros r0 Hr; pose proof (HP2 (bv_unsigned r0) Hr) as X; rewrite Z_to_bv_bv_unsigned in X; exact X).
    assert (HMAC : forall j, 0 <= j < 6 ->
      nth (Z.to_nat (56 * n + j)) (c0_placed bs b (c0_nch cx pos) p (c0_gs cx pos op)) (Z_to_bv 8 0) = Z_to_bv 8 0).
    { intros jj Hjj. replace (Z.to_nat (56 * n + jj)) with (Z.to_nat (56 * n + 0) + Z.to_nat jj)%nat by lia.
      rewrite <- (c0c_bsub_nth _ (56 * n + 0) 6 (Z.to_nat jj)) by (rewrite ?HRLp; lia).
      rewrite (Hdb 0 6) by lia. rewrite reac_boxreg_declare_inv.decl_row_mac.
      unfold Boxreg.zero6. rewrite nth_repeat. reflexivity. }
    assert (Hv0 : v = w64 0).
    { apply Hcmp. intros jj Hjj. replace (r + 56 * 0 + jj) with (r + (56 * n + jj)) by lia.
      rewrite HRB1 by (unfold REG_SIZE; lia). rewrite HZB by lia. rewrite HMAC by lia. reflexivity. }
    repeat rewrite wvb_collapse in HJ2.
    eapply (HNB cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + 2700)) mem2 (seg_rom SEGS)) _ HB HJ2 HFR HMO).
    unfold C0_B. exists r, bs, pos, op, nm, b, b, p.
    split.
    { unfold c0_ms. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs mkst].
      do 6 (split; [reflexivity|]). unfold gregs. cbn [ms_regs mkst].
      rewrite (KP2 2%bv ltac:(c0_cs)), (KP2 8%bv ltac:(c0_cs)), (KP2 9%bv ltac:(c0_cs)),
              (KP2 3%bv ltac:(c0_cs)), (KP2 4%bv ltac:(c0_cs)), (KP2 18%bv ltac:(c0_cs)), (KP2 24%bv ltac:(c0_cs)).
      rewrite Q2, Q8, Q9, Q3, Q4, Q18, Q24.
      rewrite (EE 2%nat 2%bv eq_refl), (EE 8%nat 8%bv eq_refl), (EE 9%nat 9%bv eq_refl),
              (EE 3%nat 3%bv eq_refl), (EE 4%nat 4%bv eq_refl), (EE 18%nat 18%bv eq_refl), (EE 24%nat 24%bv eq_refl).
      exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HMS)))))). }
    assert (KS : forall off w, 0 <= off < 0x98 -> gslot cx W3 ms3 off w ->
      gslot cx W3 (mkst regs2 (Z_to_bv 64 (BASE + 2700)) mem2 (seg_rom SEGS)) off w).
    { intros off w Hoff Hw. unfold gslot in *. cbn [ms_mem mkst]. rewrite <- Hw. apply rdword_ext.
      intros jj Hjj. apply KM; lia. }
    split.
    { split; [apply (c0_mf_keep i cx fp W3 ms3 _ r bs HB); [intros a Ha; cbn [ms_mem mkst]; apply KZ; exact Ha | exact HMF]|].
      split; [exact Hi|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBL|].
      split; [exact HINV|]. split; [exact Hpos|].
      split; [destruct HCUR as (CC1 & C88 & C90); split; [exact CC1|]; split; apply KS; first [lia | assumption]|].
      split; [exact Hnm|].
      split; [intros jj Hjj; cbn [ms_mem mkst]; rewrite KM by lia; exact (HNAME jj Hjj)|].
      split; [exact Hop|]. split; [exact Hop3|].
      cbn [ms_regs mkst]. rewrite (KP2 20%bv ltac:(c0_cs)), Q20, E20w. reflexivity. }
    split; [exact HWANT|]. split; [lia|].
    split; [apply KS; [lia | exact S30]|]. split; [apply KS; [lia | exact S58]|].
    split; [exact HPL|].
    split.
    { split; [exact HRin|]. split; [exact HRLp|].
      intros jj Hjj. cbn [ms_mem mkst]. rewrite KM by (unfold REG_SIZE in Hjj; lia). exact (HRB jj Hjj). }
    split; [cbn [ms_regs mkst]; rewrite Hv; exact Hv0|].
    split; [cbn [ms_regs mkst]; rewrite (KP2 19%bv ltac:(c0_cs)), Q19, (EE 19%nat 19%bv eq_refl); exact R19|].
    split; [cbn [ms_regs mkst]; rewrite (KP2 22%bv ltac:(c0_cs)), Q22, E20w; unfold w64;
            rewrite ?unsigned_lit_small by lia; f_equal; lia|].
    split; [cbn [ms_regs mkst]; rewrite (KP2 23%bv ltac:(c0_cs)), Q23; unfold w64; f_equal; lia|].
    split; [cbn [ms_regs mkst]; rewrite (KP2 25%bv ltac:(c0_cs)), Q25, (EE 25%nat 25%bv eq_refl); exact R25|].
    split; [cbn [ms_regs mkst]; rewrite (KP2 26%bv ltac:(c0_cs)), Q26, (EE 26%nat 26%bv eq_refl); exact R26|].
    cbn [ms_regs mkst]; rewrite (KP2 27%bv ltac:(c0_cs)), Q27, (EE 27%nat 27%bv eq_refl); exact R27.

  + rewrite Hn in R10.
    assert (HS : st_ok_pi SEGS VAL E (mkSS GC_D sr_atoms [C0D_RSp 1; C0D_RH; C0D_RNp 1; C0D_RRp 1] None C0D_factsp) (restrict (w_H W3) ms3)).
    { rewrite (c0_mkst cx fp GC_D ms3 (w_H W3) HMS). apply pa_entry_st_ok_full.
      - apply regs_ok_Eimg_Ereg.
      - vm_compute. reflexivity.
      - unfold C0D_RSp, C0D_RH, C0D_RNp, C0D_RRp. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
          repeat apply Forall_cons; try apply Forall_nil.
          * apply (chunk_ok_val SEGS _ _ _ 0x40 8%N (SOff 20 280) (r + 280)); [cbn [sv_denot]; rewrite U20; reflexivity | cbn; lia | cbn; lia |].
            apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact S40.
          * apply (chunk_ok_val SEGS _ _ _ 0x48 8%N (SLit 1) n); [rewrite Hn; reflexivity | cbn; lia | cbn; lia |].
            apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact S48.
          * apply (chunk_ok_val SEGS _ _ _ 0x60 8%N (SOff 34 0) sh); [rewrite c0_denot_off0; exact F34 | cbn; unfold SHADOW_OFF in *; lia | cbn; lia |].
            apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact S60.
        + rewrite U34. split; [unfold SHADOW_OFF in *; lia|]. split; [unfold SHADOW_OFF in *; lia|]. split; [intros o Ho; lia|].
          apply Forall_cons; [|apply Forall_nil].
          apply (chunk_ok_val SEGS _ _ _ 0 1%N (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
          rewrite Z.add_0_r. apply c0c_vm1. exact Hsh0.
        + rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
          apply Forall_cons; [|apply Forall_nil].
          apply (chunk_ok_val SEGS _ _ _ 280 4%N (SLit (1 + 1)) (n + 1)); [rewrite Hn; reflexivity | cbn; lia | cbn; lia |].
          apply (c0c_vm4 (w_H W3) (ms_mem ms3) r _ 280 (n + 1) HRB HRLp); [lia | lia | | lia].
          symmetry. rewrite <- (BoxregRd.le4_rd4 _ 280) by (rewrite Boxreg.bsub_length; [reflexivity | lia | lia | rewrite HRLp; lia]).
          do 2 f_equal. change (Boxreg.rd4 (c0_placed bs b (c0_nch cx pos) p (c0_gs cx pos op)) 280)
            with (Boxreg.bx_n (c0_placed bs b (c0_nch cx pos) p (c0_gs cx pos op))).
          symmetry. apply c0d_placed_n; [exact HL | lia].
        + rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
          apply Forall_cons; [|apply Forall_nil].
          apply (chunk_ok_val SEGS _ _ _ (56 * 1 + 12) 4%N (SOff 19 0) (c0_nch cx pos));
            [rewrite c0_denot_off0, (EE 19%nat 19%bv eq_refl), R19; reflexivity | cbn; lia | cbn; lia |].
          apply (c0c_vm4 (w_H W3) (ms_mem ms3) r _ (56 * 1 + 12) (c0_nch cx pos) HRB HRLp); [lia | lia | | lia].
          replace (56 * 1 + 12) with (56 * n + 12) by lia.
          rewrite (Hdb 12 4) by lia. apply reac_boxreg_declare_inv.decl_row_nch.
      - apply pairwise_disjoint_of_extents. unfold C0D_RSp, C0D_RH, C0D_RNp, C0D_RRp, extent_of_region.
        cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U20, U34.
        cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
        unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. repeat split; lia.
      - split; [|split; [exact I | exact I]]. unfold C0D_factsp. cbn [f_atoms atoms_ok].
        split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U18, Z.pow_0_r, Z.mod_1_r; unfold SHADOW_OFF, C0D_SB; lia|].
        split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U19, Z.pow_0_r, Z.mod_1_r; lia|].
        split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U20; change (2 ^ 4) with 16; lia|].
        exact I. }
    assert (SHOK : sh_ok SEGS (SOff 18 0) C0D_SHp E (mrestrict (w_H W3) (ms_mem ms3))).
    { unfold sh_ok, C0D_SHp. apply Forall_cons; [|apply Forall_nil].
      apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E (SOff 18 0) 20 r 288 r 0 288).
      - apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 r REG_SIZE r 288 HAR3 Hrin3);
          change (req_size REG_SIZE) with 288; lia.
      - rewrite U_SOff, U18, Z.add_0_r. apply c0_zcanon_in. unfold SHADOW_OFF; lia.
      - rewrite U_SOff, U20, Z.add_0_r. apply c0_zcanon_in. lia.
      - lia.
      - lia.
      - intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
        unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. clear - Hria Hx. lia. }
    apply (st_ok_pi_pin_reg' E _ _ 10%bv 1) in HS; [| cbn [restrict ms_regs]; exact R10 | reflexivity].
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.

    paj_run_tok (paj_run B LAWS) HS HJ SHOK (C0D_SB, C0D_SB + 2 ^ 44 - 1); [awr_ok_tac|].

    assert (M1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha. apply (c0_keep_outside E _ _ _ (w_H W3) a HF Ha). cbn.
      intros (rr & [<- | [<- | [<- | [<- | []]]]] & Hb); cbn in Hb; lia. }
    clear HF HFr HG.
    pose proof HJ as (HARj & _).
    assert (HZlo6 : IMG_LO + 64 <= VAL (A_OBJ 6) /\ VAL (A_OBJ 6) + 6 + 64 <= IMG_HI).
    { rewrite Forall_forall in HMRG. pose proof (HMRG (VAL (A_OBJ 6), 6) ltac:(unfold BX_G; cbn [In]; tauto)) as Hm.
      cbn [fst snd] in Hm. exact Hm. }
    destruct HZlo6 as (HZlo6 & HZhi6).
    pmkst HS.
    prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
    prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
    prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
    prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
    prreg HS (9%bv : bv 5) Q9. prreg HS (8%bv : bv 5) Q8. prreg HS (18%bv : bv 5) Q18. prreg HS (24%bv : bv 5) Q24.
    pose proof HB as (HPRE0 & _ & _ & _ & _ & _ & _ & _ & HARO & _).
    pose proof HPRE0 as (_ & _ & _ & Hgp & Htp & _).
    assert (Usp : spZ (ms_regs ms) = c_sp1 cx) by (unfold spZ; rewrite Q2, (EE 2%nat 2%bv eq_refl), G2; unfold w64; apply unsigned_lit_small; lia).
    pose proof (pa_obj_img 6 ltac:(lia)) as Hzimg.
    assert (HARO1 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) (ms_mem ms)))
      by exact (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HARO).
    assert (HZB : forall j, 0 <= j < 6 -> aview SEGS (w_H W3) (ms_mem ms) (VAL (A_OBJ 6) + j) = Some 0).
    { intros j Hj.
      destruct (HZERO j ltac:(rewrite length_map; cbn [length Boxreg.zero6 repeat]; lia)) as (Hro & Ho & He & Hv).
      rewrite (fm_rom_viewN_of_arodata SEGS B pa_relro_lo pa_relro_hi W3 (ms_mem ms) HARO1 _ Hro Ho He), Hv.
      f_equal. apply c0d_zero6_nth. exact Hj. }
    assert (HRB1 : forall j, 0 <= j < REG_SIZE ->
      aview SEGS (w_H W3) (ms_mem ms) (r + j) = Some (bv_unsigned (nth (Z.to_nat j) (c0_placed bs b (c0_nch cx pos) p (c0_gs cx pos op)) (Z_to_bv 8 0))))
      by (intros j Hj; rewrite M1 by (unfold REG_SIZE in Hj; lia); exact (HRB j Hj)).
    eapply SRr_bind.
    { eapply (aj_bcmp_at SEGS B LAWS Hsegs (SIGMA BS___interceptor_trampoline_bcmp) ABCMP W3 (ms_regs ms) (ms_mem ms)
        GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 _ k
        (r + 56 * 1) (VAL (A_OBJ 6)) 6 (c_sp1 cx - spZ (c_regs cx)) (Z_to_bv 64 (BASE + 2700)) HJ).
      - rewrite Q10, E20w. unfold w64. rewrite ?unsigned_lit_small by lia. f_equal; lia.
      - rewrite Q11, F247. reflexivity.
      - rewrite Q12. reflexivity.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - rewrite Usp. lia.
      - apply c0_sub_mod16; [exact Hsp32 | exact Hsp16].
      - lia.
      - change ESTACK with 4096. unfold GB_STK. lia.
      - rewrite Q3, (EE 3%nat 3%bv eq_refl), G3. exact Hgp.
      - rewrite Q4, (EE 4%nat 4%bv eq_refl), G4. exact Htp.
      - exact Q1.
      - apply ret_ok_codeptr_v; [lia | reflexivity].
      - intros a Ha. split.
        + replace a with (r + (a - r)) by lia. rewrite HRB1 by (unfold REG_SIZE; lia). discriminate.
        + rewrite Usp. change ESTACK with 4096. lia.
      - intros a Ha. split.
        + replace a with (VAL (A_OBJ 6) + (a - VAL (A_OBJ 6))) by lia. rewrite HZB by lia. discriminate.
        + rewrite Usp. change ESTACK with 4096. lia.
      - intros a Ha. change ESTACK with 4096. lia.
      - intros a Ha. change ESTACK with 4096. lia.
      - apply (amem_range_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 r REG_SIZE _ _ HAR3 Hrin3);
          change (req_size REG_SIZE) with 288; lia.
      - unfold amem_range, kLowMemEnd. lia.
      - apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms) _ r REG_SIZE _ _ HARj Hrin3);
          change (req_size REG_SIZE) with 288; lia.
      - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms) _ r REG_SIZE _ _ HARj Hrin3);
          change (req_size REG_SIZE) with 288; lia.
      - apply (proj1 (ro_read_ok_glob SEGS B BX_G ly3 S3 W3 (ms_mem ms) _ (VAL (A_OBJ 6)) 6 (VAL (A_OBJ 6)) 6
          HGLOB ltac:(unfold BX_G; cbn [In]; tauto) HISV HARj ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
      - intros _. apply (proj2 (ro_read_ok_glob SEGS B BX_G ly3 S3 W3 (ms_mem ms) _ (VAL (A_OBJ 6)) 6 (VAL (A_OBJ 6)) 6
          HGLOB ltac:(unfold BX_G; cbn [In]; tauto) HISV HARj ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))). }

    cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr & Hpr2).
    assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx - 8192 <= a < c_sp1 cx) ->
      aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha Hna. rewrite Hfr by (change ESTACK with 4096; lia). apply M1. exact Ha. }
    assert (KZ : forall a, c0_zone cx fp a -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha. pose proof (ZR a Ha) as Ha64. apply KM; [exact Ha64|].
      pose proof (c0_geo LAWS cx fp k ly3 S3 W3 _ _ HB HJ HFR) as (Hinp & _ & HFa & HFb & _ & HSHe).
      destruct Ha as [Ha|[Ha|[Ha|Ha]]]; [lia | destruct Hinp; lia | lia |].
      rewrite HSHe in Ha. unfold SHADOW_OFF in *.
      pose proof (Z.div_le_upper_bound (gF cx fp) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
    assert (KP2 : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> getr regs2 r0 = getr (ms_regs ms) r0)
      by (intros r0 Hr; pose proof (HP2 (bv_unsigned r0) Hr) as X; rewrite Z_to_bv_bv_unsigned in X; exact X).
    assert (HMAC : forall j, 0 <= j < 6 ->
      nth (Z.to_nat (56 * n + j)) (c0_placed bs b (c0_nch cx pos) p (c0_gs cx pos op)) (Z_to_bv 8 0) = Z_to_bv 8 0).
    { intros jj Hjj. replace (Z.to_nat (56 * n + jj)) with (Z.to_nat (56 * n + 0) + Z.to_nat jj)%nat by lia.
      rewrite <- (c0c_bsub_nth _ (56 * n + 0) 6 (Z.to_nat jj)) by (rewrite ?HRLp; lia).
      rewrite (Hdb 0 6) by lia. rewrite reac_boxreg_declare_inv.decl_row_mac.
      unfold Boxreg.zero6. rewrite nth_repeat. reflexivity. }
    assert (Hv0 : v = w64 0).
    { apply Hcmp. intros jj Hjj. replace (r + 56 * 1 + jj) with (r + (56 * n + jj)) by lia.
      rewrite HRB1 by (unfold REG_SIZE; lia). rewrite HZB by lia. rewrite HMAC by lia. reflexivity. }
    repeat rewrite wvb_collapse in HJ2.
    eapply (HNB cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + 2700)) mem2 (seg_rom SEGS)) _ HB HJ2 HFR HMO).
    unfold C0_B. exists r, bs, pos, op, nm, b, b, p.
    split.
    { unfold c0_ms. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs mkst].
      do 6 (split; [reflexivity|]). unfold gregs. cbn [ms_regs mkst].
      rewrite (KP2 2%bv ltac:(c0_cs)), (KP2 8%bv ltac:(c0_cs)), (KP2 9%bv ltac:(c0_cs)),
              (KP2 3%bv ltac:(c0_cs)), (KP2 4%bv ltac:(c0_cs)), (KP2 18%bv ltac:(c0_cs)), (KP2 24%bv ltac:(c0_cs)).
      rewrite Q2, Q8, Q9, Q3, Q4, Q18, Q24.
      rewrite (EE 2%nat 2%bv eq_refl), (EE 8%nat 8%bv eq_refl), (EE 9%nat 9%bv eq_refl),
              (EE 3%nat 3%bv eq_refl), (EE 4%nat 4%bv eq_refl), (EE 18%nat 18%bv eq_refl), (EE 24%nat 24%bv eq_refl).
      exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HMS)))))). }
    assert (KS : forall off w, 0 <= off < 0x98 -> gslot cx W3 ms3 off w ->
      gslot cx W3 (mkst regs2 (Z_to_bv 64 (BASE + 2700)) mem2 (seg_rom SEGS)) off w).
    { intros off w Hoff Hw. unfold gslot in *. cbn [ms_mem mkst]. rewrite <- Hw. apply rdword_ext.
      intros jj Hjj. apply KM; lia. }
    split.
    { split; [apply (c0_mf_keep i cx fp W3 ms3 _ r bs HB); [intros a Ha; cbn [ms_mem mkst]; apply KZ; exact Ha | exact HMF]|].
      split; [exact Hi|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBL|].
      split; [exact HINV|]. split; [exact Hpos|].
      split; [destruct HCUR as (CC1 & C88 & C90); split; [exact CC1|]; split; apply KS; first [lia | assumption]|].
      split; [exact Hnm|].
      split; [intros jj Hjj; cbn [ms_mem mkst]; rewrite KM by lia; exact (HNAME jj Hjj)|].
      split; [exact Hop|]. split; [exact Hop3|].
      cbn [ms_regs mkst]. rewrite (KP2 20%bv ltac:(c0_cs)), Q20, E20w. reflexivity. }
    split; [exact HWANT|]. split; [lia|].
    split; [apply KS; [lia | exact S30]|]. split; [apply KS; [lia | exact S58]|].
    split; [exact HPL|].
    split.
    { split; [exact HRin|]. split; [exact HRLp|].
      intros jj Hjj. cbn [ms_mem mkst]. rewrite KM by (unfold REG_SIZE in Hjj; lia). exact (HRB jj Hjj). }
    split; [cbn [ms_regs mkst]; rewrite Hv; exact Hv0|].
    split; [cbn [ms_regs mkst]; rewrite (KP2 19%bv ltac:(c0_cs)), Q19, (EE 19%nat 19%bv eq_refl); exact R19|].
    split; [cbn [ms_regs mkst]; rewrite (KP2 22%bv ltac:(c0_cs)), Q22, E20w; unfold w64;
            rewrite ?unsigned_lit_small by lia; f_equal; lia|].
    split; [cbn [ms_regs mkst]; rewrite (KP2 23%bv ltac:(c0_cs)), Q23; unfold w64; f_equal; lia|].
    split; [cbn [ms_regs mkst]; rewrite (KP2 25%bv ltac:(c0_cs)), Q25, (EE 25%nat 25%bv eq_refl); exact R25|].
    split; [cbn [ms_regs mkst]; rewrite (KP2 26%bv ltac:(c0_cs)), Q26, (EE 26%nat 26%bv eq_refl); exact R26|].
    cbn [ms_regs mkst]; rewrite (KP2 27%bv ltac:(c0_cs)), Q27, (EE 27%nat 27%bv eq_refl); exact R27.

  + rewrite Hn in R10.
    assert (HS : st_ok_pi SEGS VAL E (mkSS GC_D sr_atoms [C0D_RSp 2; C0D_RH; C0D_RNp 2; C0D_RRp 2] None C0D_factsp) (restrict (w_H W3) ms3)).
    { rewrite (c0_mkst cx fp GC_D ms3 (w_H W3) HMS). apply pa_entry_st_ok_full.
      - apply regs_ok_Eimg_Ereg.
      - vm_compute. reflexivity.
      - unfold C0D_RSp, C0D_RH, C0D_RNp, C0D_RRp. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
          repeat apply Forall_cons; try apply Forall_nil.
          * apply (chunk_ok_val SEGS _ _ _ 0x40 8%N (SOff 20 280) (r + 280)); [cbn [sv_denot]; rewrite U20; reflexivity | cbn; lia | cbn; lia |].
            apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact S40.
          * apply (chunk_ok_val SEGS _ _ _ 0x48 8%N (SLit 2) n); [rewrite Hn; reflexivity | cbn; lia | cbn; lia |].
            apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact S48.
          * apply (chunk_ok_val SEGS _ _ _ 0x60 8%N (SOff 34 0) sh); [rewrite c0_denot_off0; exact F34 | cbn; unfold SHADOW_OFF in *; lia | cbn; lia |].
            apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact S60.
        + rewrite U34. split; [unfold SHADOW_OFF in *; lia|]. split; [unfold SHADOW_OFF in *; lia|]. split; [intros o Ho; lia|].
          apply Forall_cons; [|apply Forall_nil].
          apply (chunk_ok_val SEGS _ _ _ 0 1%N (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
          rewrite Z.add_0_r. apply c0c_vm1. exact Hsh0.
        + rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
          apply Forall_cons; [|apply Forall_nil].
          apply (chunk_ok_val SEGS _ _ _ 280 4%N (SLit (2 + 1)) (n + 1)); [rewrite Hn; reflexivity | cbn; lia | cbn; lia |].
          apply (c0c_vm4 (w_H W3) (ms_mem ms3) r _ 280 (n + 1) HRB HRLp); [lia | lia | | lia].
          symmetry. rewrite <- (BoxregRd.le4_rd4 _ 280) by (rewrite Boxreg.bsub_length; [reflexivity | lia | lia | rewrite HRLp; lia]).
          do 2 f_equal. change (Boxreg.rd4 (c0_placed bs b (c0_nch cx pos) p (c0_gs cx pos op)) 280)
            with (Boxreg.bx_n (c0_placed bs b (c0_nch cx pos) p (c0_gs cx pos op))).
          symmetry. apply c0d_placed_n; [exact HL | lia].
        + rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
          apply Forall_cons; [|apply Forall_nil].
          apply (chunk_ok_val SEGS _ _ _ (56 * 2 + 12) 4%N (SOff 19 0) (c0_nch cx pos));
            [rewrite c0_denot_off0, (EE 19%nat 19%bv eq_refl), R19; reflexivity | cbn; lia | cbn; lia |].
          apply (c0c_vm4 (w_H W3) (ms_mem ms3) r _ (56 * 2 + 12) (c0_nch cx pos) HRB HRLp); [lia | lia | | lia].
          replace (56 * 2 + 12) with (56 * n + 12) by lia.
          rewrite (Hdb 12 4) by lia. apply reac_boxreg_declare_inv.decl_row_nch.
      - apply pairwise_disjoint_of_extents. unfold C0D_RSp, C0D_RH, C0D_RNp, C0D_RRp, extent_of_region.
        cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U20, U34.
        cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
        unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. repeat split; lia.
      - split; [|split; [exact I | exact I]]. unfold C0D_factsp. cbn [f_atoms atoms_ok].
        split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U18, Z.pow_0_r, Z.mod_1_r; unfold SHADOW_OFF, C0D_SB; lia|].
        split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U19, Z.pow_0_r, Z.mod_1_r; lia|].
        split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U20; change (2 ^ 4) with 16; lia|].
        exact I. }
    assert (SHOK : sh_ok SEGS (SOff 18 0) C0D_SHp E (mrestrict (w_H W3) (ms_mem ms3))).
    { unfold sh_ok, C0D_SHp. apply Forall_cons; [|apply Forall_nil].
      apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E (SOff 18 0) 20 r 288 r 0 288).
      - apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 r REG_SIZE r 288 HAR3 Hrin3);
          change (req_size REG_SIZE) with 288; lia.
      - rewrite U_SOff, U18, Z.add_0_r. apply c0_zcanon_in. unfold SHADOW_OFF; lia.
      - rewrite U_SOff, U20, Z.add_0_r. apply c0_zcanon_in. lia.
      - lia.
      - lia.
      - intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
        unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. clear - Hria Hx. lia. }
    apply (st_ok_pi_pin_reg' E _ _ 10%bv 2) in HS; [| cbn [restrict ms_regs]; exact R10 | reflexivity].
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.

    paj_run_tok (paj_run B LAWS) HS HJ SHOK (C0D_SB, C0D_SB + 2 ^ 44 - 1); [awr_ok_tac|].

    assert (M1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha. apply (c0_keep_outside E _ _ _ (w_H W3) a HF Ha). cbn.
      intros (rr & [<- | [<- | [<- | [<- | []]]]] & Hb); cbn in Hb; lia. }
    clear HF HFr HG.
    pose proof HJ as (HARj & _).
    assert (HZlo6 : IMG_LO + 64 <= VAL (A_OBJ 6) /\ VAL (A_OBJ 6) + 6 + 64 <= IMG_HI).
    { rewrite Forall_forall in HMRG. pose proof (HMRG (VAL (A_OBJ 6), 6) ltac:(unfold BX_G; cbn [In]; tauto)) as Hm.
      cbn [fst snd] in Hm. exact Hm. }
    destruct HZlo6 as (HZlo6 & HZhi6).
    pmkst HS.
    prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
    prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
    prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
    prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
    prreg HS (9%bv : bv 5) Q9. prreg HS (8%bv : bv 5) Q8. prreg HS (18%bv : bv 5) Q18. prreg HS (24%bv : bv 5) Q24.
    pose proof HB as (HPRE0 & _ & _ & _ & _ & _ & _ & _ & HARO & _).
    pose proof HPRE0 as (_ & _ & _ & Hgp & Htp & _).
    assert (Usp : spZ (ms_regs ms) = c_sp1 cx) by (unfold spZ; rewrite Q2, (EE 2%nat 2%bv eq_refl), G2; unfold w64; apply unsigned_lit_small; lia).
    pose proof (pa_obj_img 6 ltac:(lia)) as Hzimg.
    assert (HARO1 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) (ms_mem ms)))
      by exact (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HARO).
    assert (HZB : forall j, 0 <= j < 6 -> aview SEGS (w_H W3) (ms_mem ms) (VAL (A_OBJ 6) + j) = Some 0).
    { intros j Hj.
      destruct (HZERO j ltac:(rewrite length_map; cbn [length Boxreg.zero6 repeat]; lia)) as (Hro & Ho & He & Hv).
      rewrite (fm_rom_viewN_of_arodata SEGS B pa_relro_lo pa_relro_hi W3 (ms_mem ms) HARO1 _ Hro Ho He), Hv.
      f_equal. apply c0d_zero6_nth. exact Hj. }
    assert (HRB1 : forall j, 0 <= j < REG_SIZE ->
      aview SEGS (w_H W3) (ms_mem ms) (r + j) = Some (bv_unsigned (nth (Z.to_nat j) (c0_placed bs b (c0_nch cx pos) p (c0_gs cx pos op)) (Z_to_bv 8 0))))
      by (intros j Hj; rewrite M1 by (unfold REG_SIZE in Hj; lia); exact (HRB j Hj)).
    eapply SRr_bind.
    { eapply (aj_bcmp_at SEGS B LAWS Hsegs (SIGMA BS___interceptor_trampoline_bcmp) ABCMP W3 (ms_regs ms) (ms_mem ms)
        GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 _ k
        (r + 56 * 2) (VAL (A_OBJ 6)) 6 (c_sp1 cx - spZ (c_regs cx)) (Z_to_bv 64 (BASE + 2700)) HJ).
      - rewrite Q10, E20w. unfold w64. rewrite ?unsigned_lit_small by lia. f_equal; lia.
      - rewrite Q11, F247. reflexivity.
      - rewrite Q12. reflexivity.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - rewrite Usp. lia.
      - apply c0_sub_mod16; [exact Hsp32 | exact Hsp16].
      - lia.
      - change ESTACK with 4096. unfold GB_STK. lia.
      - rewrite Q3, (EE 3%nat 3%bv eq_refl), G3. exact Hgp.
      - rewrite Q4, (EE 4%nat 4%bv eq_refl), G4. exact Htp.
      - exact Q1.
      - apply ret_ok_codeptr_v; [lia | reflexivity].
      - intros a Ha. split.
        + replace a with (r + (a - r)) by lia. rewrite HRB1 by (unfold REG_SIZE; lia). discriminate.
        + rewrite Usp. change ESTACK with 4096. lia.
      - intros a Ha. split.
        + replace a with (VAL (A_OBJ 6) + (a - VAL (A_OBJ 6))) by lia. rewrite HZB by lia. discriminate.
        + rewrite Usp. change ESTACK with 4096. lia.
      - intros a Ha. change ESTACK with 4096. lia.
      - intros a Ha. change ESTACK with 4096. lia.
      - apply (amem_range_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 r REG_SIZE _ _ HAR3 Hrin3);
          change (req_size REG_SIZE) with 288; lia.
      - unfold amem_range, kLowMemEnd. lia.
      - apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms) _ r REG_SIZE _ _ HARj Hrin3);
          change (req_size REG_SIZE) with 288; lia.
      - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms) _ r REG_SIZE _ _ HARj Hrin3);
          change (req_size REG_SIZE) with 288; lia.
      - apply (proj1 (ro_read_ok_glob SEGS B BX_G ly3 S3 W3 (ms_mem ms) _ (VAL (A_OBJ 6)) 6 (VAL (A_OBJ 6)) 6
          HGLOB ltac:(unfold BX_G; cbn [In]; tauto) HISV HARj ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
      - intros _. apply (proj2 (ro_read_ok_glob SEGS B BX_G ly3 S3 W3 (ms_mem ms) _ (VAL (A_OBJ 6)) 6 (VAL (A_OBJ 6)) 6
          HGLOB ltac:(unfold BX_G; cbn [In]; tauto) HISV HARj ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))). }

    cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr & Hpr2).
    assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx - 8192 <= a < c_sp1 cx) ->
      aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha Hna. rewrite Hfr by (change ESTACK with 4096; lia). apply M1. exact Ha. }
    assert (KZ : forall a, c0_zone cx fp a -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha. pose proof (ZR a Ha) as Ha64. apply KM; [exact Ha64|].
      pose proof (c0_geo LAWS cx fp k ly3 S3 W3 _ _ HB HJ HFR) as (Hinp & _ & HFa & HFb & _ & HSHe).
      destruct Ha as [Ha|[Ha|[Ha|Ha]]]; [lia | destruct Hinp; lia | lia |].
      rewrite HSHe in Ha. unfold SHADOW_OFF in *.
      pose proof (Z.div_le_upper_bound (gF cx fp) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
    assert (KP2 : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> getr regs2 r0 = getr (ms_regs ms) r0)
      by (intros r0 Hr; pose proof (HP2 (bv_unsigned r0) Hr) as X; rewrite Z_to_bv_bv_unsigned in X; exact X).
    assert (HMAC : forall j, 0 <= j < 6 ->
      nth (Z.to_nat (56 * n + j)) (c0_placed bs b (c0_nch cx pos) p (c0_gs cx pos op)) (Z_to_bv 8 0) = Z_to_bv 8 0).
    { intros jj Hjj. replace (Z.to_nat (56 * n + jj)) with (Z.to_nat (56 * n + 0) + Z.to_nat jj)%nat by lia.
      rewrite <- (c0c_bsub_nth _ (56 * n + 0) 6 (Z.to_nat jj)) by (rewrite ?HRLp; lia).
      rewrite (Hdb 0 6) by lia. rewrite reac_boxreg_declare_inv.decl_row_mac.
      unfold Boxreg.zero6. rewrite nth_repeat. reflexivity. }
    assert (Hv0 : v = w64 0).
    { apply Hcmp. intros jj Hjj. replace (r + 56 * 2 + jj) with (r + (56 * n + jj)) by lia.
      rewrite HRB1 by (unfold REG_SIZE; lia). rewrite HZB by lia. rewrite HMAC by lia. reflexivity. }
    repeat rewrite wvb_collapse in HJ2.
    eapply (HNB cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + 2700)) mem2 (seg_rom SEGS)) _ HB HJ2 HFR HMO).
    unfold C0_B. exists r, bs, pos, op, nm, b, b, p.
    split.
    { unfold c0_ms. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs mkst].
      do 6 (split; [reflexivity|]). unfold gregs. cbn [ms_regs mkst].
      rewrite (KP2 2%bv ltac:(c0_cs)), (KP2 8%bv ltac:(c0_cs)), (KP2 9%bv ltac:(c0_cs)),
              (KP2 3%bv ltac:(c0_cs)), (KP2 4%bv ltac:(c0_cs)), (KP2 18%bv ltac:(c0_cs)), (KP2 24%bv ltac:(c0_cs)).
      rewrite Q2, Q8, Q9, Q3, Q4, Q18, Q24.
      rewrite (EE 2%nat 2%bv eq_refl), (EE 8%nat 8%bv eq_refl), (EE 9%nat 9%bv eq_refl),
              (EE 3%nat 3%bv eq_refl), (EE 4%nat 4%bv eq_refl), (EE 18%nat 18%bv eq_refl), (EE 24%nat 24%bv eq_refl).
      exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HMS)))))). }
    assert (KS : forall off w, 0 <= off < 0x98 -> gslot cx W3 ms3 off w ->
      gslot cx W3 (mkst regs2 (Z_to_bv 64 (BASE + 2700)) mem2 (seg_rom SEGS)) off w).
    { intros off w Hoff Hw. unfold gslot in *. cbn [ms_mem mkst]. rewrite <- Hw. apply rdword_ext.
      intros jj Hjj. apply KM; lia. }
    split.
    { split; [apply (c0_mf_keep i cx fp W3 ms3 _ r bs HB); [intros a Ha; cbn [ms_mem mkst]; apply KZ; exact Ha | exact HMF]|].
      split; [exact Hi|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBL|].
      split; [exact HINV|]. split; [exact Hpos|].
      split; [destruct HCUR as (CC1 & C88 & C90); split; [exact CC1|]; split; apply KS; first [lia | assumption]|].
      split; [exact Hnm|].
      split; [intros jj Hjj; cbn [ms_mem mkst]; rewrite KM by lia; exact (HNAME jj Hjj)|].
      split; [exact Hop|]. split; [exact Hop3|].
      cbn [ms_regs mkst]. rewrite (KP2 20%bv ltac:(c0_cs)), Q20, E20w. reflexivity. }
    split; [exact HWANT|]. split; [lia|].
    split; [apply KS; [lia | exact S30]|]. split; [apply KS; [lia | exact S58]|].
    split; [exact HPL|].
    split.
    { split; [exact HRin|]. split; [exact HRLp|].
      intros jj Hjj. cbn [ms_mem mkst]. rewrite KM by (unfold REG_SIZE in Hjj; lia). exact (HRB jj Hjj). }
    split; [cbn [ms_regs mkst]; rewrite Hv; exact Hv0|].
    split; [cbn [ms_regs mkst]; rewrite (KP2 19%bv ltac:(c0_cs)), Q19, (EE 19%nat 19%bv eq_refl); exact R19|].
    split; [cbn [ms_regs mkst]; rewrite (KP2 22%bv ltac:(c0_cs)), Q22, E20w; unfold w64;
            rewrite ?unsigned_lit_small by lia; f_equal; lia|].
    split; [cbn [ms_regs mkst]; rewrite (KP2 23%bv ltac:(c0_cs)), Q23; unfold w64; f_equal; lia|].
    split; [cbn [ms_regs mkst]; rewrite (KP2 25%bv ltac:(c0_cs)), Q25, (EE 25%nat 25%bv eq_refl); exact R25|].
    split; [cbn [ms_regs mkst]; rewrite (KP2 26%bv ltac:(c0_cs)), Q26, (EE 26%nat 26%bv eq_refl); exact R26|].
    cbn [ms_regs mkst]; rewrite (KP2 27%bv ltac:(c0_cs)), Q27, (EE 27%nat 27%bv eq_refl); exact R27.

  + rewrite Hn in R10.
    assert (HS : st_ok_pi SEGS VAL E (mkSS GC_D sr_atoms [C0D_RSp 3; C0D_RH; C0D_RNp 3; C0D_RRp 3] None C0D_factsp) (restrict (w_H W3) ms3)).
    { rewrite (c0_mkst cx fp GC_D ms3 (w_H W3) HMS). apply pa_entry_st_ok_full.
      - apply regs_ok_Eimg_Ereg.
      - vm_compute. reflexivity.
      - unfold C0D_RSp, C0D_RH, C0D_RNp, C0D_RRp. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
          repeat apply Forall_cons; try apply Forall_nil.
          * apply (chunk_ok_val SEGS _ _ _ 0x40 8%N (SOff 20 280) (r + 280)); [cbn [sv_denot]; rewrite U20; reflexivity | cbn; lia | cbn; lia |].
            apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact S40.
          * apply (chunk_ok_val SEGS _ _ _ 0x48 8%N (SLit 3) n); [rewrite Hn; reflexivity | cbn; lia | cbn; lia |].
            apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact S48.
          * apply (chunk_ok_val SEGS _ _ _ 0x60 8%N (SOff 34 0) sh); [rewrite c0_denot_off0; exact F34 | cbn; unfold SHADOW_OFF in *; lia | cbn; lia |].
            apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact S60.
        + rewrite U34. split; [unfold SHADOW_OFF in *; lia|]. split; [unfold SHADOW_OFF in *; lia|]. split; [intros o Ho; lia|].
          apply Forall_cons; [|apply Forall_nil].
          apply (chunk_ok_val SEGS _ _ _ 0 1%N (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
          rewrite Z.add_0_r. apply c0c_vm1. exact Hsh0.
        + rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
          apply Forall_cons; [|apply Forall_nil].
          apply (chunk_ok_val SEGS _ _ _ 280 4%N (SLit (3 + 1)) (n + 1)); [rewrite Hn; reflexivity | cbn; lia | cbn; lia |].
          apply (c0c_vm4 (w_H W3) (ms_mem ms3) r _ 280 (n + 1) HRB HRLp); [lia | lia | | lia].
          symmetry. rewrite <- (BoxregRd.le4_rd4 _ 280) by (rewrite Boxreg.bsub_length; [reflexivity | lia | lia | rewrite HRLp; lia]).
          do 2 f_equal. change (Boxreg.rd4 (c0_placed bs b (c0_nch cx pos) p (c0_gs cx pos op)) 280)
            with (Boxreg.bx_n (c0_placed bs b (c0_nch cx pos) p (c0_gs cx pos op))).
          symmetry. apply c0d_placed_n; [exact HL | lia].
        + rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
          apply Forall_cons; [|apply Forall_nil].
          apply (chunk_ok_val SEGS _ _ _ (56 * 3 + 12) 4%N (SOff 19 0) (c0_nch cx pos));
            [rewrite c0_denot_off0, (EE 19%nat 19%bv eq_refl), R19; reflexivity | cbn; lia | cbn; lia |].
          apply (c0c_vm4 (w_H W3) (ms_mem ms3) r _ (56 * 3 + 12) (c0_nch cx pos) HRB HRLp); [lia | lia | | lia].
          replace (56 * 3 + 12) with (56 * n + 12) by lia.
          rewrite (Hdb 12 4) by lia. apply reac_boxreg_declare_inv.decl_row_nch.
      - apply pairwise_disjoint_of_extents. unfold C0D_RSp, C0D_RH, C0D_RNp, C0D_RRp, extent_of_region.
        cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U20, U34.
        cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
        unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. repeat split; lia.
      - split; [|split; [exact I | exact I]]. unfold C0D_factsp. cbn [f_atoms atoms_ok].
        split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U18, Z.pow_0_r, Z.mod_1_r; unfold SHADOW_OFF, C0D_SB; lia|].
        split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U19, Z.pow_0_r, Z.mod_1_r; lia|].
        split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U20; change (2 ^ 4) with 16; lia|].
        exact I. }
    assert (SHOK : sh_ok SEGS (SOff 18 0) C0D_SHp E (mrestrict (w_H W3) (ms_mem ms3))).
    { unfold sh_ok, C0D_SHp. apply Forall_cons; [|apply Forall_nil].
      apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E (SOff 18 0) 20 r 288 r 0 288).
      - apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 r REG_SIZE r 288 HAR3 Hrin3);
          change (req_size REG_SIZE) with 288; lia.
      - rewrite U_SOff, U18, Z.add_0_r. apply c0_zcanon_in. unfold SHADOW_OFF; lia.
      - rewrite U_SOff, U20, Z.add_0_r. apply c0_zcanon_in. lia.
      - lia.
      - lia.
      - intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
        unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. clear - Hria Hx. lia. }
    apply (st_ok_pi_pin_reg' E _ _ 10%bv 3) in HS; [| cbn [restrict ms_regs]; exact R10 | reflexivity].
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.

    paj_run_tok (paj_run B LAWS) HS HJ SHOK (C0D_SB, C0D_SB + 2 ^ 44 - 1); [awr_ok_tac|].

    assert (M1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha. apply (c0_keep_outside E _ _ _ (w_H W3) a HF Ha). cbn.
      intros (rr & [<- | [<- | [<- | [<- | []]]]] & Hb); cbn in Hb; lia. }
    clear HF HFr HG.
    pose proof HJ as (HARj & _).
    assert (HZlo6 : IMG_LO + 64 <= VAL (A_OBJ 6) /\ VAL (A_OBJ 6) + 6 + 64 <= IMG_HI).
    { rewrite Forall_forall in HMRG. pose proof (HMRG (VAL (A_OBJ 6), 6) ltac:(unfold BX_G; cbn [In]; tauto)) as Hm.
      cbn [fst snd] in Hm. exact Hm. }
    destruct HZlo6 as (HZlo6 & HZhi6).
    pmkst HS.
    prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
    prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
    prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
    prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
    prreg HS (9%bv : bv 5) Q9. prreg HS (8%bv : bv 5) Q8. prreg HS (18%bv : bv 5) Q18. prreg HS (24%bv : bv 5) Q24.
    pose proof HB as (HPRE0 & _ & _ & _ & _ & _ & _ & _ & HARO & _).
    pose proof HPRE0 as (_ & _ & _ & Hgp & Htp & _).
    assert (Usp : spZ (ms_regs ms) = c_sp1 cx) by (unfold spZ; rewrite Q2, (EE 2%nat 2%bv eq_refl), G2; unfold w64; apply unsigned_lit_small; lia).
    pose proof (pa_obj_img 6 ltac:(lia)) as Hzimg.
    assert (HARO1 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) (ms_mem ms)))
      by exact (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HARO).
    assert (HZB : forall j, 0 <= j < 6 -> aview SEGS (w_H W3) (ms_mem ms) (VAL (A_OBJ 6) + j) = Some 0).
    { intros j Hj.
      destruct (HZERO j ltac:(rewrite length_map; cbn [length Boxreg.zero6 repeat]; lia)) as (Hro & Ho & He & Hv).
      rewrite (fm_rom_viewN_of_arodata SEGS B pa_relro_lo pa_relro_hi W3 (ms_mem ms) HARO1 _ Hro Ho He), Hv.
      f_equal. apply c0d_zero6_nth. exact Hj. }
    assert (HRB1 : forall j, 0 <= j < REG_SIZE ->
      aview SEGS (w_H W3) (ms_mem ms) (r + j) = Some (bv_unsigned (nth (Z.to_nat j) (c0_placed bs b (c0_nch cx pos) p (c0_gs cx pos op)) (Z_to_bv 8 0))))
      by (intros j Hj; rewrite M1 by (unfold REG_SIZE in Hj; lia); exact (HRB j Hj)).
    eapply SRr_bind.
    { eapply (aj_bcmp_at SEGS B LAWS Hsegs (SIGMA BS___interceptor_trampoline_bcmp) ABCMP W3 (ms_regs ms) (ms_mem ms)
        GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 _ k
        (r + 56 * 3) (VAL (A_OBJ 6)) 6 (c_sp1 cx - spZ (c_regs cx)) (Z_to_bv 64 (BASE + 2700)) HJ).
      - rewrite Q10, E20w. unfold w64. rewrite ?unsigned_lit_small by lia. f_equal; lia.
      - rewrite Q11, F247. reflexivity.
      - rewrite Q12. reflexivity.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - rewrite Usp. lia.
      - apply c0_sub_mod16; [exact Hsp32 | exact Hsp16].
      - lia.
      - change ESTACK with 4096. unfold GB_STK. lia.
      - rewrite Q3, (EE 3%nat 3%bv eq_refl), G3. exact Hgp.
      - rewrite Q4, (EE 4%nat 4%bv eq_refl), G4. exact Htp.
      - exact Q1.
      - apply ret_ok_codeptr_v; [lia | reflexivity].
      - intros a Ha. split.
        + replace a with (r + (a - r)) by lia. rewrite HRB1 by (unfold REG_SIZE; lia). discriminate.
        + rewrite Usp. change ESTACK with 4096. lia.
      - intros a Ha. split.
        + replace a with (VAL (A_OBJ 6) + (a - VAL (A_OBJ 6))) by lia. rewrite HZB by lia. discriminate.
        + rewrite Usp. change ESTACK with 4096. lia.
      - intros a Ha. change ESTACK with 4096. lia.
      - intros a Ha. change ESTACK with 4096. lia.
      - apply (amem_range_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 r REG_SIZE _ _ HAR3 Hrin3);
          change (req_size REG_SIZE) with 288; lia.
      - unfold amem_range, kLowMemEnd. lia.
      - apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms) _ r REG_SIZE _ _ HARj Hrin3);
          change (req_size REG_SIZE) with 288; lia.
      - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms) _ r REG_SIZE _ _ HARj Hrin3);
          change (req_size REG_SIZE) with 288; lia.
      - apply (proj1 (ro_read_ok_glob SEGS B BX_G ly3 S3 W3 (ms_mem ms) _ (VAL (A_OBJ 6)) 6 (VAL (A_OBJ 6)) 6
          HGLOB ltac:(unfold BX_G; cbn [In]; tauto) HISV HARj ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
      - intros _. apply (proj2 (ro_read_ok_glob SEGS B BX_G ly3 S3 W3 (ms_mem ms) _ (VAL (A_OBJ 6)) 6 (VAL (A_OBJ 6)) 6
          HGLOB ltac:(unfold BX_G; cbn [In]; tauto) HISV HARj ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))). }

    cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr & Hpr2).
    assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx - 8192 <= a < c_sp1 cx) ->
      aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha Hna. rewrite Hfr by (change ESTACK with 4096; lia). apply M1. exact Ha. }
    assert (KZ : forall a, c0_zone cx fp a -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha. pose proof (ZR a Ha) as Ha64. apply KM; [exact Ha64|].
      pose proof (c0_geo LAWS cx fp k ly3 S3 W3 _ _ HB HJ HFR) as (Hinp & _ & HFa & HFb & _ & HSHe).
      destruct Ha as [Ha|[Ha|[Ha|Ha]]]; [lia | destruct Hinp; lia | lia |].
      rewrite HSHe in Ha. unfold SHADOW_OFF in *.
      pose proof (Z.div_le_upper_bound (gF cx fp) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
    assert (KP2 : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> getr regs2 r0 = getr (ms_regs ms) r0)
      by (intros r0 Hr; pose proof (HP2 (bv_unsigned r0) Hr) as X; rewrite Z_to_bv_bv_unsigned in X; exact X).
    assert (HMAC : forall j, 0 <= j < 6 ->
      nth (Z.to_nat (56 * n + j)) (c0_placed bs b (c0_nch cx pos) p (c0_gs cx pos op)) (Z_to_bv 8 0) = Z_to_bv 8 0).
    { intros jj Hjj. replace (Z.to_nat (56 * n + jj)) with (Z.to_nat (56 * n + 0) + Z.to_nat jj)%nat by lia.
      rewrite <- (c0c_bsub_nth _ (56 * n + 0) 6 (Z.to_nat jj)) by (rewrite ?HRLp; lia).
      rewrite (Hdb 0 6) by lia. rewrite reac_boxreg_declare_inv.decl_row_mac.
      unfold Boxreg.zero6. rewrite nth_repeat. reflexivity. }
    assert (Hv0 : v = w64 0).
    { apply Hcmp. intros jj Hjj. replace (r + 56 * 3 + jj) with (r + (56 * n + jj)) by lia.
      rewrite HRB1 by (unfold REG_SIZE; lia). rewrite HZB by lia. rewrite HMAC by lia. reflexivity. }
    repeat rewrite wvb_collapse in HJ2.
    eapply (HNB cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + 2700)) mem2 (seg_rom SEGS)) _ HB HJ2 HFR HMO).
    unfold C0_B. exists r, bs, pos, op, nm, b, b, p.
    split.
    { unfold c0_ms. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs mkst].
      do 6 (split; [reflexivity|]). unfold gregs. cbn [ms_regs mkst].
      rewrite (KP2 2%bv ltac:(c0_cs)), (KP2 8%bv ltac:(c0_cs)), (KP2 9%bv ltac:(c0_cs)),
              (KP2 3%bv ltac:(c0_cs)), (KP2 4%bv ltac:(c0_cs)), (KP2 18%bv ltac:(c0_cs)), (KP2 24%bv ltac:(c0_cs)).
      rewrite Q2, Q8, Q9, Q3, Q4, Q18, Q24.
      rewrite (EE 2%nat 2%bv eq_refl), (EE 8%nat 8%bv eq_refl), (EE 9%nat 9%bv eq_refl),
              (EE 3%nat 3%bv eq_refl), (EE 4%nat 4%bv eq_refl), (EE 18%nat 18%bv eq_refl), (EE 24%nat 24%bv eq_refl).
      exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HMS)))))). }
    assert (KS : forall off w, 0 <= off < 0x98 -> gslot cx W3 ms3 off w ->
      gslot cx W3 (mkst regs2 (Z_to_bv 64 (BASE + 2700)) mem2 (seg_rom SEGS)) off w).
    { intros off w Hoff Hw. unfold gslot in *. cbn [ms_mem mkst]. rewrite <- Hw. apply rdword_ext.
      intros jj Hjj. apply KM; lia. }
    split.
    { split; [apply (c0_mf_keep i cx fp W3 ms3 _ r bs HB); [intros a Ha; cbn [ms_mem mkst]; apply KZ; exact Ha | exact HMF]|].
      split; [exact Hi|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBL|].
      split; [exact HINV|]. split; [exact Hpos|].
      split; [destruct HCUR as (CC1 & C88 & C90); split; [exact CC1|]; split; apply KS; first [lia | assumption]|].
      split; [exact Hnm|].
      split; [intros jj Hjj; cbn [ms_mem mkst]; rewrite KM by lia; exact (HNAME jj Hjj)|].
      split; [exact Hop|]. split; [exact Hop3|].
      cbn [ms_regs mkst]. rewrite (KP2 20%bv ltac:(c0_cs)), Q20, E20w. reflexivity. }
    split; [exact HWANT|]. split; [lia|].
    split; [apply KS; [lia | exact S30]|]. split; [apply KS; [lia | exact S58]|].
    split; [exact HPL|].
    split.
    { split; [exact HRin|]. split; [exact HRLp|].
      intros jj Hjj. cbn [ms_mem mkst]. rewrite KM by (unfold REG_SIZE in Hjj; lia). exact (HRB jj Hjj). }
    split; [cbn [ms_regs mkst]; rewrite Hv; exact Hv0|].
    split; [cbn [ms_regs mkst]; rewrite (KP2 19%bv ltac:(c0_cs)), Q19, (EE 19%nat 19%bv eq_refl); exact R19|].
    split; [cbn [ms_regs mkst]; rewrite (KP2 22%bv ltac:(c0_cs)), Q22, E20w; unfold w64;
            rewrite ?unsigned_lit_small by lia; f_equal; lia|].
    split; [cbn [ms_regs mkst]; rewrite (KP2 23%bv ltac:(c0_cs)), Q23; unfold w64; f_equal; lia|].
    split; [cbn [ms_regs mkst]; rewrite (KP2 25%bv ltac:(c0_cs)), Q25, (EE 25%nat 25%bv eq_refl); exact R25|].
    split; [cbn [ms_regs mkst]; rewrite (KP2 26%bv ltac:(c0_cs)), Q26, (EE 26%nat 26%bv eq_refl); exact R26|].
    cbn [ms_regs mkst]; rewrite (KP2 27%bv ltac:(c0_cs)), Q27, (EE 27%nat 27%bv eq_refl); exact R27.

  + rewrite Hn in R10.
    assert (HS : st_ok_pi SEGS VAL E (mkSS GC_D sr_atoms [C0D_RSp 4; C0D_RH; C0D_RNp 4; C0D_RRp 4] None C0D_factsp) (restrict (w_H W3) ms3)).
    { rewrite (c0_mkst cx fp GC_D ms3 (w_H W3) HMS). apply pa_entry_st_ok_full.
      - apply regs_ok_Eimg_Ereg.
      - vm_compute. reflexivity.
      - unfold C0D_RSp, C0D_RH, C0D_RNp, C0D_RRp. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
          repeat apply Forall_cons; try apply Forall_nil.
          * apply (chunk_ok_val SEGS _ _ _ 0x40 8%N (SOff 20 280) (r + 280)); [cbn [sv_denot]; rewrite U20; reflexivity | cbn; lia | cbn; lia |].
            apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact S40.
          * apply (chunk_ok_val SEGS _ _ _ 0x48 8%N (SLit 4) n); [rewrite Hn; reflexivity | cbn; lia | cbn; lia |].
            apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact S48.
          * apply (chunk_ok_val SEGS _ _ _ 0x60 8%N (SOff 34 0) sh); [rewrite c0_denot_off0; exact F34 | cbn; unfold SHADOW_OFF in *; lia | cbn; lia |].
            apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact S60.
        + rewrite U34. split; [unfold SHADOW_OFF in *; lia|]. split; [unfold SHADOW_OFF in *; lia|]. split; [intros o Ho; lia|].
          apply Forall_cons; [|apply Forall_nil].
          apply (chunk_ok_val SEGS _ _ _ 0 1%N (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
          rewrite Z.add_0_r. apply c0c_vm1. exact Hsh0.
        + rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
          apply Forall_cons; [|apply Forall_nil].
          apply (chunk_ok_val SEGS _ _ _ 280 4%N (SLit (4 + 1)) (n + 1)); [rewrite Hn; reflexivity | cbn; lia | cbn; lia |].
          apply (c0c_vm4 (w_H W3) (ms_mem ms3) r _ 280 (n + 1) HRB HRLp); [lia | lia | | lia].
          symmetry. rewrite <- (BoxregRd.le4_rd4 _ 280) by (rewrite Boxreg.bsub_length; [reflexivity | lia | lia | rewrite HRLp; lia]).
          do 2 f_equal. change (Boxreg.rd4 (c0_placed bs b (c0_nch cx pos) p (c0_gs cx pos op)) 280)
            with (Boxreg.bx_n (c0_placed bs b (c0_nch cx pos) p (c0_gs cx pos op))).
          symmetry. apply c0d_placed_n; [exact HL | lia].
        + rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
          apply Forall_cons; [|apply Forall_nil].
          apply (chunk_ok_val SEGS _ _ _ (56 * 4 + 12) 4%N (SOff 19 0) (c0_nch cx pos));
            [rewrite c0_denot_off0, (EE 19%nat 19%bv eq_refl), R19; reflexivity | cbn; lia | cbn; lia |].
          apply (c0c_vm4 (w_H W3) (ms_mem ms3) r _ (56 * 4 + 12) (c0_nch cx pos) HRB HRLp); [lia | lia | | lia].
          replace (56 * 4 + 12) with (56 * n + 12) by lia.
          rewrite (Hdb 12 4) by lia. apply reac_boxreg_declare_inv.decl_row_nch.
      - apply pairwise_disjoint_of_extents. unfold C0D_RSp, C0D_RH, C0D_RNp, C0D_RRp, extent_of_region.
        cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U20, U34.
        cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
        unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. repeat split; lia.
      - split; [|split; [exact I | exact I]]. unfold C0D_factsp. cbn [f_atoms atoms_ok].
        split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U18, Z.pow_0_r, Z.mod_1_r; unfold SHADOW_OFF, C0D_SB; lia|].
        split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U19, Z.pow_0_r, Z.mod_1_r; lia|].
        split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U20; change (2 ^ 4) with 16; lia|].
        exact I. }
    assert (SHOK : sh_ok SEGS (SOff 18 0) C0D_SHp E (mrestrict (w_H W3) (ms_mem ms3))).
    { unfold sh_ok, C0D_SHp. apply Forall_cons; [|apply Forall_nil].
      apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E (SOff 18 0) 20 r 288 r 0 288).
      - apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 r REG_SIZE r 288 HAR3 Hrin3);
          change (req_size REG_SIZE) with 288; lia.
      - rewrite U_SOff, U18, Z.add_0_r. apply c0_zcanon_in. unfold SHADOW_OFF; lia.
      - rewrite U_SOff, U20, Z.add_0_r. apply c0_zcanon_in. lia.
      - lia.
      - lia.
      - intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
        unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. clear - Hria Hx. lia. }
    apply (st_ok_pi_pin_reg' E _ _ 10%bv 4) in HS; [| cbn [restrict ms_regs]; exact R10 | reflexivity].
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.

    paj_run_tok (paj_run B LAWS) HS HJ SHOK (C0D_SB, C0D_SB + 2 ^ 44 - 1); [awr_ok_tac|].

    assert (M1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha. apply (c0_keep_outside E _ _ _ (w_H W3) a HF Ha). cbn.
      intros (rr & [<- | [<- | [<- | [<- | []]]]] & Hb); cbn in Hb; lia. }
    clear HF HFr HG.
    pose proof HJ as (HARj & _).
    assert (HZlo6 : IMG_LO + 64 <= VAL (A_OBJ 6) /\ VAL (A_OBJ 6) + 6 + 64 <= IMG_HI).
    { rewrite Forall_forall in HMRG. pose proof (HMRG (VAL (A_OBJ 6), 6) ltac:(unfold BX_G; cbn [In]; tauto)) as Hm.
      cbn [fst snd] in Hm. exact Hm. }
    destruct HZlo6 as (HZlo6 & HZhi6).
    pmkst HS.
    prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
    prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
    prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (22%bv : bv 5) Q22.
    prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
    prreg HS (9%bv : bv 5) Q9. prreg HS (8%bv : bv 5) Q8. prreg HS (18%bv : bv 5) Q18. prreg HS (24%bv : bv 5) Q24.
    pose proof HB as (HPRE0 & _ & _ & _ & _ & _ & _ & _ & HARO & _).
    pose proof HPRE0 as (_ & _ & _ & Hgp & Htp & _).
    assert (Usp : spZ (ms_regs ms) = c_sp1 cx) by (unfold spZ; rewrite Q2, (EE 2%nat 2%bv eq_refl), G2; unfold w64; apply unsigned_lit_small; lia).
    pose proof (pa_obj_img 6 ltac:(lia)) as Hzimg.
    assert (HARO1 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) (ms_mem ms)))
      by exact (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HARO).
    assert (HZB : forall j, 0 <= j < 6 -> aview SEGS (w_H W3) (ms_mem ms) (VAL (A_OBJ 6) + j) = Some 0).
    { intros j Hj.
      destruct (HZERO j ltac:(rewrite length_map; cbn [length Boxreg.zero6 repeat]; lia)) as (Hro & Ho & He & Hv).
      rewrite (fm_rom_viewN_of_arodata SEGS B pa_relro_lo pa_relro_hi W3 (ms_mem ms) HARO1 _ Hro Ho He), Hv.
      f_equal. apply c0d_zero6_nth. exact Hj. }
    assert (HRB1 : forall j, 0 <= j < REG_SIZE ->
      aview SEGS (w_H W3) (ms_mem ms) (r + j) = Some (bv_unsigned (nth (Z.to_nat j) (c0_placed bs b (c0_nch cx pos) p (c0_gs cx pos op)) (Z_to_bv 8 0))))
      by (intros j Hj; rewrite M1 by (unfold REG_SIZE in Hj; lia); exact (HRB j Hj)).
    eapply SRr_bind.
    { eapply (aj_bcmp_at SEGS B LAWS Hsegs (SIGMA BS___interceptor_trampoline_bcmp) ABCMP W3 (ms_regs ms) (ms_mem ms)
        GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 _ k
        (r + 56 * 4) (VAL (A_OBJ 6)) 6 (c_sp1 cx - spZ (c_regs cx)) (Z_to_bv 64 (BASE + 2700)) HJ).
      - rewrite Q10, E20w. unfold w64. rewrite ?unsigned_lit_small by lia. f_equal; lia.
      - rewrite Q11, F247. reflexivity.
      - rewrite Q12. reflexivity.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - rewrite Usp. lia.
      - apply c0_sub_mod16; [exact Hsp32 | exact Hsp16].
      - lia.
      - change ESTACK with 4096. unfold GB_STK. lia.
      - rewrite Q3, (EE 3%nat 3%bv eq_refl), G3. exact Hgp.
      - rewrite Q4, (EE 4%nat 4%bv eq_refl), G4. exact Htp.
      - exact Q1.
      - apply ret_ok_codeptr_v; [lia | reflexivity].
      - intros a Ha. split.
        + replace a with (r + (a - r)) by lia. rewrite HRB1 by (unfold REG_SIZE; lia). discriminate.
        + rewrite Usp. change ESTACK with 4096. lia.
      - intros a Ha. split.
        + replace a with (VAL (A_OBJ 6) + (a - VAL (A_OBJ 6))) by lia. rewrite HZB by lia. discriminate.
        + rewrite Usp. change ESTACK with 4096. lia.
      - intros a Ha. change ESTACK with 4096. lia.
      - intros a Ha. change ESTACK with 4096. lia.
      - apply (amem_range_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 r REG_SIZE _ _ HAR3 Hrin3);
          change (req_size REG_SIZE) with 288; lia.
      - unfold amem_range, kLowMemEnd. lia.
      - apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms) _ r REG_SIZE _ _ HARj Hrin3);
          change (req_size REG_SIZE) with 288; lia.
      - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms) _ r REG_SIZE _ _ HARj Hrin3);
          change (req_size REG_SIZE) with 288; lia.
      - apply (proj1 (ro_read_ok_glob SEGS B BX_G ly3 S3 W3 (ms_mem ms) _ (VAL (A_OBJ 6)) 6 (VAL (A_OBJ 6)) 6
          HGLOB ltac:(unfold BX_G; cbn [In]; tauto) HISV HARj ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
      - intros _. apply (proj2 (ro_read_ok_glob SEGS B BX_G ly3 S3 W3 (ms_mem ms) _ (VAL (A_OBJ 6)) 6 (VAL (A_OBJ 6)) 6
          HGLOB ltac:(unfold BX_G; cbn [In]; tauto) HISV HARj ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))). }

    cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr & Hpr2).
    assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx - 8192 <= a < c_sp1 cx) ->
      aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha Hna. rewrite Hfr by (change ESTACK with 4096; lia). apply M1. exact Ha. }
    assert (KZ : forall a, c0_zone cx fp a -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { intros a Ha. pose proof (ZR a Ha) as Ha64. apply KM; [exact Ha64|].
      pose proof (c0_geo LAWS cx fp k ly3 S3 W3 _ _ HB HJ HFR) as (Hinp & _ & HFa & HFb & _ & HSHe).
      destruct Ha as [Ha|[Ha|[Ha|Ha]]]; [lia | destruct Hinp; lia | lia |].
      rewrite HSHe in Ha. unfold SHADOW_OFF in *.
      pose proof (Z.div_le_upper_bound (gF cx fp) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
    assert (KP2 : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> getr regs2 r0 = getr (ms_regs ms) r0)
      by (intros r0 Hr; pose proof (HP2 (bv_unsigned r0) Hr) as X; rewrite Z_to_bv_bv_unsigned in X; exact X).
    assert (HMAC : forall j, 0 <= j < 6 ->
      nth (Z.to_nat (56 * n + j)) (c0_placed bs b (c0_nch cx pos) p (c0_gs cx pos op)) (Z_to_bv 8 0) = Z_to_bv 8 0).
    { intros jj Hjj. replace (Z.to_nat (56 * n + jj)) with (Z.to_nat (56 * n + 0) + Z.to_nat jj)%nat by lia.
      rewrite <- (c0c_bsub_nth _ (56 * n + 0) 6 (Z.to_nat jj)) by (rewrite ?HRLp; lia).
      rewrite (Hdb 0 6) by lia. rewrite reac_boxreg_declare_inv.decl_row_mac.
      unfold Boxreg.zero6. rewrite nth_repeat. reflexivity. }
    assert (Hv0 : v = w64 0).
    { apply Hcmp. intros jj Hjj. replace (r + 56 * 4 + jj) with (r + (56 * n + jj)) by lia.
      rewrite HRB1 by (unfold REG_SIZE; lia). rewrite HZB by lia. rewrite HMAC by lia. reflexivity. }
    repeat rewrite wvb_collapse in HJ2.
    eapply (HNB cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + 2700)) mem2 (seg_rom SEGS)) _ HB HJ2 HFR HMO).
    unfold C0_B. exists r, bs, pos, op, nm, b, b, p.
    split.
    { unfold c0_ms. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs mkst].
      do 6 (split; [reflexivity|]). unfold gregs. cbn [ms_regs mkst].
      rewrite (KP2 2%bv ltac:(c0_cs)), (KP2 8%bv ltac:(c0_cs)), (KP2 9%bv ltac:(c0_cs)),
              (KP2 3%bv ltac:(c0_cs)), (KP2 4%bv ltac:(c0_cs)), (KP2 18%bv ltac:(c0_cs)), (KP2 24%bv ltac:(c0_cs)).
      rewrite Q2, Q8, Q9, Q3, Q4, Q18, Q24.
      rewrite (EE 2%nat 2%bv eq_refl), (EE 8%nat 8%bv eq_refl), (EE 9%nat 9%bv eq_refl),
              (EE 3%nat 3%bv eq_refl), (EE 4%nat 4%bv eq_refl), (EE 18%nat 18%bv eq_refl), (EE 24%nat 24%bv eq_refl).
      exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HMS)))))). }
    assert (KS : forall off w, 0 <= off < 0x98 -> gslot cx W3 ms3 off w ->
      gslot cx W3 (mkst regs2 (Z_to_bv 64 (BASE + 2700)) mem2 (seg_rom SEGS)) off w).
    { intros off w Hoff Hw. unfold gslot in *. cbn [ms_mem mkst]. rewrite <- Hw. apply rdword_ext.
      intros jj Hjj. apply KM; lia. }
    split.
    { split; [apply (c0_mf_keep i cx fp W3 ms3 _ r bs HB); [intros a Ha; cbn [ms_mem mkst]; apply KZ; exact Ha | exact HMF]|].
      split; [exact Hi|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBL|].
      split; [exact HINV|]. split; [exact Hpos|].
      split; [destruct HCUR as (CC1 & C88 & C90); split; [exact CC1|]; split; apply KS; first [lia | assumption]|].
      split; [exact Hnm|].
      split; [intros jj Hjj; cbn [ms_mem mkst]; rewrite KM by lia; exact (HNAME jj Hjj)|].
      split; [exact Hop|]. split; [exact Hop3|].
      cbn [ms_regs mkst]. rewrite (KP2 20%bv ltac:(c0_cs)), Q20, E20w. reflexivity. }
    split; [exact HWANT|]. split; [lia|].
    split; [apply KS; [lia | exact S30]|]. split; [apply KS; [lia | exact S58]|].
    split; [exact HPL|].
    split.
    { split; [exact HRin|]. split; [exact HRLp|].
      intros jj Hjj. cbn [ms_mem mkst]. rewrite KM by (unfold REG_SIZE in Hjj; lia). exact (HRB jj Hjj). }
    split; [cbn [ms_regs mkst]; rewrite Hv; exact Hv0|].
    split; [cbn [ms_regs mkst]; rewrite (KP2 19%bv ltac:(c0_cs)), Q19, (EE 19%nat 19%bv eq_refl); exact R19|].
    split; [cbn [ms_regs mkst]; rewrite (KP2 22%bv ltac:(c0_cs)), Q22, E20w; unfold w64;
            rewrite ?unsigned_lit_small by lia; f_equal; lia|].
    split; [cbn [ms_regs mkst]; rewrite (KP2 23%bv ltac:(c0_cs)), Q23; unfold w64; f_equal; lia|].
    split; [cbn [ms_regs mkst]; rewrite (KP2 25%bv ltac:(c0_cs)), Q25, (EE 25%nat 25%bv eq_refl); exact R25|].
    split; [cbn [ms_regs mkst]; rewrite (KP2 26%bv ltac:(c0_cs)), Q26, (EE 26%nat 26%bv eq_refl); exact R26|].
    cbn [ms_regs mkst]; rewrite (KP2 27%bv ltac:(c0_cs)), Q27, (EE 27%nat 27%bv eq_refl); exact R27.
Qed.

End c.
End b.
End a.
