(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryAdmit), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACjo.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntryAdmit.v, with its module paths and module names changed; 873 of its 913 lines of code are new or changed and 619 lines of the source are left out. *)
(* The definitions and helper lemmas of case 1's add piece (0x807e8 .. 0x80ab4), split off BoxLxC1Add.v at
   a working branch 0ed2a7658c0 so that each segment of the piece can live in its own file:
   the engine's state at a cut (ca_ss, ca_E, ca_seat), the cuts CA_R1 / CA_R2 / CA_P, the call lemmas ca_find_at /
   ca_add_at / ca_bcmp_at, the branch-condition lemmas and the landing ca_land. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal BoxSyms BoxList BoxPa BoxPaLib BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC1g YC1h YC81 YC85 BoxFrame BoxCJ BoxRo.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import ReacBoxregInit.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require ReacBoxregFind ReacBoxregAdd LowestFree.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxLxDefs BoxLxSeat BoxLxC1Defs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require
Boxreg LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_case1
reac_boxreg_add_c reac_boxreg_find_c lowest_free_c reac_boxreg_add_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HISV : img_shadow_vis SEGS B.
Hypothesis HGLOB : globs_marked SEGS B BX_G.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA BS___asan_memcpy).
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA BS___interceptor_trampoline_bcmp).
Hypothesis TFIND : ReacBoxregFind.treac_boxreg_find_spec B.
Hypothesis TADD : ReacBoxregAdd.treac_boxreg_add_spec B.
Hypothesis TLOWFREE : LowestFree.tlowest_free_spec B.
Hypothesis HZERO : SnprintfDef.asn_rom_bytes SEGS B (VAL (A_OBJ 6))
  (map (fun b : byte => bv_unsigned b) Boxreg.zero6).
Hypothesis HRMB : SnprintfDef.asn_rom_bytes SEGS B (VAL (A_OBJ 4)) [0; 64; 171; 0; 0].
Hypothesis HMRG : Forall (fun g => IMG_LO + 64 <= fst g /\ fst g + snd g + 64 <= IMG_HI) BX_G.
Variable POST : bcx -> world SEGS -> config -> Prop.

(* ---- the engine's symbolic state at a cut of this piece ---- *)
(* The shadow base as the token engine wants it: register s2's own atom. *)
Definition ca_SB : Z := 0x7fff8000.
Definition ca_Bx : sv := SOff 18%nat 0.
Definition ca_Bspan : Z * Z := (ca_SB, ca_SB + 2 ^ 44 - 1).
(* The registry block r (s4, atom 20): its 288 bytes are addressable. *)
Definition ca_SH : list shent := [mkSHE 20%nat 0 288].
(* The atoms past the registers: 32 the address of mac, 33 nch, 34 the word in slot 0x30, 35 the shadow byte's
   address of r->n. *)
Definition ca_ext (cx : bcx) (fp r nch lfw : Z) : list word :=
  [w64 (gF cx fp + GO_MAC); w64 nch; w64 lfw; w64 (shadow_of_addr SHADOW_OFF (r + 280))].
Definition ca_E (regs : bvmap 5 word) (cx : bcx) (fp r nch lfw : Z) : env :=
  Eimg (Ereg regs (ca_ext cx fp r nch lfw)).
(* The spill slots this piece reads, read-only: no instruction of 0x807e8 .. 0x80924 stores. *)
Definition ca_chunks : list YP09.chunk :=
  [ YP09.mkChunk 0x70 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x58 (CVal 8 (SOff 33 0));
    YP09.mkChunk 0x30 (CVal 8 (SOff 34 0)); YP09.mkChunk 0x60 (CVal 8 (SOff 35 0));
    YP09.mkChunk 0x40 (CVal 8 (SOff 20 280)) ].
Definition ca_spill : YP09.region := YP09.mkRegion (Some 9%nat) 0 0x98 0 0 ca_chunks.
Definition ca_facts : facts :=
  mkFacts [(9%nat, mkAF 0x7fff7f000000 (2 ^ 47) 5); (18%nat, mkAF ca_SB ca_SB 0);
           (20%nat, mkAF 4096 0x7fffff800000 4)] [] [].
Definition ca_ss (pc : Z) : sstate := mkSS pc sr_atoms [ca_spill] None ca_facts.

Lemma ca_ewR : forall regs extra n (r : bv 5),
  Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs extra)) n = getr regs r.
Proof.
  intros regs extra n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.

Lemma ca_ewX : forall regs extra j,
  (32 + j < A_TEXT)%nat -> ew (Eimg (Ereg regs extra)) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof. intros regs extra j Hj. rewrite Eimg_low by exact Hj. apply ew_Ereg_extra. Qed.

Lemma ca_slot_chunk : forall cx W3 ms E off e v,
  gslot cx W3 ms off v -> 0 <= v < 2 ^ 64 -> sv_denot E e = Z_to_bv 64 v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) (c_sp1 cx) (YP09.mkChunk off (CVal 8 e)).
Proof.
  intros cx W3 ms E off e v Hv Hr He.
  apply (chunk_ok_val SEGS E _ (c_sp1 cx) off 8%N e v He).
  - cbn [Z.of_N]. change (8 * 8) with 64. exact Hr.
  - cbn [Z.of_N]. lia.
  - cbn [N.to_nat]. apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms)). exact Hv.
Qed.

Lemma ca_rdword_range : forall (H : word -> bool) (m : word -> option byte) a v,
  rdword (aview SEGS H m) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
  intros H m a v Hv. unfold rdword in Hv.
  repeat match type of Hv with
  | context [aview SEGS H m ?x] =>
      let b := fresh "b" in let Hb := fresh "Hb" in
      destruct (aview SEGS H m x) as [b|] eqn:Hb; [|discriminate Hv];
      apply (aview_byte SEGS) in Hb as (? & _ & -> & ?)
  end.
  injection Hv as <-. lia.
Qed.

(* The seat: a cut's machine state as the engine's symbolic state at its pc. *)
Lemma ca_seat : forall cx fp k ly3 S3 W3 ms md pc r fab nch lfw,
  gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 (ms_mem ms) md k ->
  frames S3 = [(GB_CID, fp)] ->
  c1_core cx fp pc ms ->
  getr (ms_regs ms) 20 = w64 r -> In (r, REG_SIZE) (ablocks B ly3 S3) ->
  gslots_fr cx fp W3 ms -> gslots_r cx fp W3 ms r fab ->
  gslot cx W3 ms 0x58 nch -> gslot cx W3 ms 0x30 lfw ->
  st_ok_pi SEGS VAL (ca_E (ms_regs ms) cx fp r nch lfw) (ca_ss pc) (restrict (w_H W3) ms) /\
  img_env VAL A_LIM (ca_E (ms_regs ms) cx fp r nch lfw) /\
  sh_ok SEGS ca_Bx ca_SH (ca_E (ms_regs ms) cx fp r nch lfw) (mrestrict (w_H W3) (ms_mem ms)).
Proof.
  intros cx fp k ly3 S3 W3 ms md pc r fab nch lfw HB HJ HFR HCO R20 Hrin HFRS HSR S58 S30.
  pose proof HCO as (Hpc & Hrv & Hsv & Hro & Hfr & Hfc & (G2 & G8 & G9 & G3 & G4 & G18 & G24)).
  pose proof HFRS as (F18 & F28 & F70 & F78 & F80).
  pose proof HSR as (S10 & S20 & S38 & S40 & S50 & S60).
  pose proof (gb_sp_facts B MT cx HB) as (Hal16 & Hlo & Hhi & Hsp1).
  pose proof (gb_sp1_al B MT cx HB) as Hsp1al.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HJ as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR3 Hrin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
  change (req_size REG_SIZE) with 288 in Hrceil, Hria.
  pose proof (gb_F_facts B MT LAWS cx fp W3 ms ly3 S3 md k HB HJ HFR) as (HF0 & HFc & HFia & _ & HSHeq).
  pose proof (ca_rdword_range _ _ _ _ S58) as Hnch. pose proof (ca_rdword_range _ _ _ _ S30) as Hlfw.
  pose proof (ca_rdword_range _ _ _ _ S60) as Hsh.
  set (E := ca_E (ms_regs ms) cx fp r nch lfw).
  assert (HEI : img_env VAL A_LIM E) by (subst E; unfold ca_E; apply Eimg_env).
  assert (E9 : ew E 9 = w64 (c_sp1 cx))
    by (subst E; unfold ca_E; rewrite (ca_ewR _ _ 9 9%bv eq_refl); exact G9).
  assert (E18 : ew E 18 = w64 SHADOW_OFF)
    by (subst E; unfold ca_E; rewrite (ca_ewR _ _ 18 18%bv eq_refl); exact G18).
  assert (E20 : ew E 20 = w64 r) by (subst E; unfold ca_E; rewrite (ca_ewR _ _ 20 20%bv eq_refl); exact R20).
  assert (E32 : ew E 32 = w64 (gF cx fp + GO_MAC))
    by (subst E; unfold ca_E; exact (ca_ewX _ _ 0 ltac:(unfold A_TEXT; lia))).
  assert (E33 : ew E 33 = w64 nch) by (subst E; unfold ca_E; exact (ca_ewX _ _ 1 ltac:(unfold A_TEXT; lia))).
  assert (E34 : ew E 34 = w64 lfw) by (subst E; unfold ca_E; exact (ca_ewX _ _ 2 ltac:(unfold A_TEXT; lia))).
  assert (E35 : ew E 35 = w64 (shadow_of_addr SHADOW_OFF (r + 280)))
    by (subst E; unfold ca_E; exact (ca_ewX _ _ 3 ltac:(unfold A_TEXT; lia))).
  assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (U18 : bv_unsigned (ew E 18) = SHADOW_OFF)
    by (rewrite E18; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U20 : bv_unsigned (ew E 20) = r) by (rewrite E20; apply unsigned_lit_small; lia).
  split; [|split; [exact HEI|]].
  - rewrite (c1_core_mkst cx fp pc ms HCO) at 1. rewrite restrict_mkst_fx.
    unfold ca_ss. apply pa_entry_st_ok_full.
    + subst E. unfold ca_E. apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_nil].
      unfold ca_spill, YP09.region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      unfold ca_chunks.
      apply Forall_cons;
        [apply (ca_slot_chunk cx W3 ms E 0x70 _ (gF cx fp + GO_MAC) F70); [unfold GO_MAC; lia |
         cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity] |].
      apply Forall_cons;
        [apply (ca_slot_chunk cx W3 ms E 0x58 _ nch S58 Hnch);
         cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity |].
      apply Forall_cons;
        [apply (ca_slot_chunk cx W3 ms E 0x30 _ lfw S30 Hlfw);
         cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity |].
      apply Forall_cons;
        [apply (ca_slot_chunk cx W3 ms E 0x60 _ _ S60 Hsh);
         cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity |].
      apply Forall_cons; [|apply Forall_nil].
      apply (ca_slot_chunk cx W3 ms E 0x40 _ (r + 280) S40); [lia|].
      cbn [sv_denot]. rewrite E20. unfold w64. apply Boxreg.addi_lit.
    + cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; exact I.
    + split; [|split; exact I]. cbn [ca_facts f_atoms atoms_ok].
      split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U9; change (2 ^ 5) with 32;
              split; [lia|]; split; [exact Hsp1al | lia]|].
      split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U18; unfold ca_SB, SHADOW_OFF;
              rewrite Z.pow_0_r, Z.mod_1_r; split; [lia|]; split; [reflexivity | lia]|].
      split; [|exact I].
      unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U20; change (2 ^ 4) with 16.
      split; [lia|]. split; [exact Hr16 | lia].
  - unfold sh_ok, ca_SH. apply Forall_cons; [|apply Forall_nil].
    unfold shent_ok, app_apart, ca_Bx. cbn [she_m she_lo she_hi].
    rewrite (U_atom E 18 SHADOW_OFF E18 ltac:(unfold SHADOW_OFF; lia)).
    rewrite (U_atom E 20 r E20 ltac:(lia)).
    rewrite <- (aview_rd_of SEGS). split.
    + eapply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms) md r REG_SIZE (r + 0) (288 - 0)
                HAR3 Hrin); change (req_size REG_SIZE) with 288; lia.
    + intros a Ha. rewrite Z.min_l in Ha by lia. rewrite Z.max_r in Ha by lia.
      revert Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
      revert Hria Hr4096 Hrceil C1 C3 C5. clear. intros. lia.
Qed.

Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).


Lemma ca_sub_mod16 : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
  intros a b Ha Hb. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hb; [|lia]. apply Z.mod_divide; [lia|].
  destruct Ha as [x Hx]. destruct Hb as [y Hy]. exists (2 * x - y). lia.
Qed.

Lemma ca_ro_same : forall E rs (m m' : word -> option byte),
  Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs -> frame_of E rs m m' -> forall x, m' x = m x.
Proof.
  intros E rs m m' Hro HF x. apply HF. intros (rg & Hin & Hb).
  rewrite Forall_forall in Hro. pose proof (Hro rg Hin). lia.
Qed.

(* The callee chain at the realigned machine stack pointer, through the layout of the phase. *)
Lemma ca_achain : forall cx ly3 S3 W3 mem md own k sp',
  gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    own ly3 S3 W3 mem md k ->
  rdword (aview SEGS (w_H W3) mem) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
  rdword (aview SEGS (w_H W3) mem) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
  sp' + 16 <= spZ (c_regs cx) ->
  achain ly3 (aview SEGS (w_H W3) mem) sp' (spZ (c_regs cx)) (gch cx).
Proof.
  intros cx ly3 S3 W3 mem md own k sp' HB HJ H8 H16 Hsp.
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & _).
  pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
  pose proof asan_consts as (C1 & _).
  apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ Etop).
  apply (gb_achain B MT cx HB); [ | exact H8 | exact H16 | exact Hsp].
  intros a Ha. apply F1; unfold GB_STK in *; lia.
Qed.

Lemma ca_gsaved_s0 : forall cx W3 ms, gsaved cx W3 ms ->
  rdword (aview SEGS (w_H W3) (ms_mem ms)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)).
Proof.
  intros cx W3 ms [_ H]. specialize (H 0 ltac:(lia)). rewrite Z.mul_0_r, Z.sub_0_r in H. rewrite H.
  unfold s0Z. do 3 f_equal; apply bv_eq; reflexivity.
Qed.

(* mac, the frame object at F + 32, as the callees' premise names it. *)
Lemma ca_afobj : forall cx fp k ly3 S3 W3 ms md,
  gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 (ms_mem ms) md k ->
  frames S3 = [(GB_CID, fp)] -> gshadow cx fp W3 ms GSH_it ->
  afobj SEGS B ly3 S3 W3 (ms_mem ms) (gF cx fp + GO_MAC) 6.
Proof.
  intros cx fp k ly3 S3 W3 ms md HB HJ HFR HSH.
  pose proof (gb_F_al B MT LAWS cx fp W3 ms ly3 S3 md k HB HJ HFR) as Hal.
  pose proof (gb_frame_addr_eq B MT LAWS cx fp W3 ms ly3 S3 md k HB HJ) as Efa.
  split; [|split].
  - exists GB_CID, fp. rewrite HFR, Efa. change (fs_frame_bytes GB_CID) with 512. unfold GO_MAC, GB_CID.
    split; [left; reflexivity|]. split; [lia|].
    split; [apply Z.mod_divide; [lia|]; apply Z.mod_divide in Hal; [|lia]; destruct Hal as [q Hq]; exists (8 * q); lia|].
    lia.
  - unfold GO_MAC. apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal; [|lia]. destruct Hal as [q Hq].
    exists (8 * q + 4). lia.
  - replace (gF cx fp + GO_MAC) with (gF cx fp + GO_MAC + 0) by lia.
    exact (gb_mac_ra B MT LAWS cx fp W3 ms ly3 S3 md k HB HJ HFR 0 6 HSH ltac:(lia) ltac:(lia)).
Qed.

Lemma ca_ewR' : forall regs cx fp r nch lfw n (q : bv 5),
  Z.of_nat n = bv_unsigned q -> ew (ca_E regs cx fp r nch lfw) n = getr regs q.
Proof. intros regs cx fp r nch lfw n q Hn. unfold ca_E. apply ca_ewR. exact Hn. Qed.

(* ---- the cuts inside this piece, at the return slot of each call ---- *)
Definition CA_PR1 : Z := 0x8ac.   (* 0x807f8, after reac_boxreg_find (r, mac)            *)
Definition CA_PR2 : Z := 0x8c0.   (* 0x8080c, after reac_boxreg_add (r, mac, nch)        *)
Definition CA_PR3 : Z := 0x920.   (* 0x8086c, after bcmp (r->box[idx].mac, mac, 6)       *)
Definition CA_PR4 : Z := 0x930.   (* 0x8087c, after reac_boxreg_find (r, mac) again      *)
Definition CA_PR5 : Z := 0x944.   (* 0x80890, after reac_boxreg_add (r, mac, nch) again  *)

(* What every cut of this piece holds: C1_call's facts but the registry's bytes and the registers the calls
   change. *)
Definition ca_com (i : Z) (cx : bcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms : machine_state) (r : Z) (bs : list byte) (pos : Z) (M : list byte) (nch lf want : Z) : Prop :=
  c1_base B MT cx fp k acc i ly3 S3 W3 ms r bs pos /\ c1mac cx fp W3 ms M /\
  0 <= nch < 256 /\ gslot cx W3 ms 0x58 nch /\ gslot cx W3 ms 0x30 (lf mod 2 ^ 64) /\ -1 <= lf <= 38 /\
  LLVMFuzzerTestOneInput_case1.c1_wantP bs M nch lf want /\ -1 <= want <= 4 /\
  getr (ms_regs ms) 22 = w64 want /\ getr (ms_regs ms) 26 = w64 (Boxreg.bx_n bs) /\
  getr (ms_regs ms) 25 = w64 (Boxreg.bx_fabric bs).

(* 0x807f8: find returned `known` in a0; s3 names mac. *)
Definition CA_R1 (i : Z) (cx : bcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms : machine_state) (md : Model) : Prop :=
  exists r bs pos M nch lf want v w5 known,
  c1_core cx fp CA_PR1 ms /\ ca_com i cx fp k acc ly3 S3 W3 ms r bs pos M nch lf want /\
  greg B ly3 S3 W3 ms r bs /\
  (v = 0 <-> M = Boxreg.zero6) /\ 0 <= v < 2 ^ 64 /\ getr (ms_regs ms) 27 = w64 v /\
  0 <= w5 < 2 ^ 64 /\ getr (ms_regs ms) 21 = w64 w5 /\
  (Z.land w5 1 = 0 <-> reac_boxreg_add_c.add_width_ok nch (Boxreg.bx_fabric bs)) /\
  reac_boxreg_find_c.find_result bs M known /\
  getr (ms_regs ms) 10 = w64 known /\ getr (ms_regs ms) 19 = w64 (gF cx fp + GO_MAC).

(* 0x8080c: add returned idx = z in a0 and left bs' in the registry; s7 holds known. *)
Definition CA_R2 (i : Z) (cx : bcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms : machine_state) (md : Model) : Prop :=
  exists r bs bs' pos M nch lf want v w5 known z,
  c1_core cx fp CA_PR2 ms /\ ca_com i cx fp k acc ly3 S3 W3 ms r bs pos M nch lf want /\
  greg B ly3 S3 W3 ms r bs' /\
  (v = 0 <-> M = Boxreg.zero6) /\ 0 <= v < 2 ^ 64 /\ getr (ms_regs ms) 27 = w64 v /\
  0 <= w5 < 2 ^ 64 /\ getr (ms_regs ms) 21 = w64 w5 /\
  (Z.land w5 1 = 0 <-> reac_boxreg_add_c.add_width_ok nch (Boxreg.bx_fabric bs)) /\
  reac_boxreg_find_c.find_result bs M known /\ reac_boxreg_add_c.add_out bs M nch z bs' /\
  getr (ms_regs ms) 10 = w64 z /\ getr (ms_regs ms) 23 = w64 known.

(* 0x8086c / 0x8087c / 0x80890: idx = z >= 0 in s3, mac in s5, known in s7; a0 is 0 (zr) or z. *)
Definition CA_P (pc : Z) (zr : bool) (i : Z) (cx : bcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate)
  (W3 : world SEGS) (ms : machine_state) (md : Model) : Prop :=
  exists r bs bs' pos M nch lf want known z,
  c1_core cx fp pc ms /\ ca_com i cx fp k acc ly3 S3 W3 ms r bs pos M nch lf want /\
  greg B ly3 S3 W3 ms r bs' /\
  reac_boxreg_find_c.find_result bs M known /\ reac_boxreg_add_c.add_out bs M nch z bs' /\ 0 <= z /\
  getr (ms_regs ms) 10 = w64 (if zr then 0 else z) /\ getr (ms_regs ms) 19 = w64 z /\
  getr (ms_regs ms) 21 = w64 (gF cx fp + GO_MAC) /\ getr (ms_regs ms) 23 = w64 known.

Lemma ca_pres : forall (regsc regs2 : bvmap 5 word) n (q : bv 5) v,
  aregs_preserved regsc regs2 -> acallee_saved n -> q = Z_to_bv 5 n -> getr regsc q = v -> getr regs2 q = v.
Proof. intros regsc regs2 n q v HP Hn -> Hv. rewrite (HP n Hn). exact Hv. Qed.

(* The facts of ca_com, across a step that keeps the case's own memory. *)
Lemma ca_com_keep : forall i cx fp k acc ly3 S3 W3 rs ms ms' r bs pos M nch lf want,
  gb_base B MT cx -> gb_keep cx fp W3 rs (ms_mem ms) (ms_mem ms') ->
  getr (ms_regs ms') 20 = w64 r -> getr (ms_regs ms') 22 = w64 want ->
  getr (ms_regs ms') 26 = w64 (Boxreg.bx_n bs) -> getr (ms_regs ms') 25 = w64 (Boxreg.bx_fabric bs) ->
  ca_com i cx fp k acc ly3 S3 W3 ms r bs pos M nch lf want ->
  ca_com i cx fp k acc ly3 S3 W3 ms' r bs pos M nch lf want.
Proof.
  intros i cx fp k acc ly3 S3 W3 rs ms ms' r bs pos M nch lf want HB HK R20 R22 R26 R25
    ((Hi & Hk & Hacc & HBL & HIb & (HSV & HSH & HFL & HIN & HFRS & HPV) & HSR & HCU & H68 & H48 & _) &
     HMAC & Hnch & S58 & S30 & Hlf & HW & Hwant & _ & _ & _).
  split; [|split; [exact (c1mac_keep cx fp W3 rs ms ms' M HK HMAC)|]].
  - split; [exact Hi|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBL|]. split; [exact HIb|].
    split; [|split; [exact (gb_gslots_r_keep B MT cx fp W3 HB rs ms ms' r _ HK HSR)|]].
    + split; [exact (gb_gsaved_keep B MT cx fp W3 HB rs ms ms' HK HSV)|].
      split; [exact (gb_gshadow_keep cx fp W3 rs ms ms' GSH_it HK ltac:(vm_compute; discriminate) HSH)|].
      split; [exact (gb_flag_keep cx fp W3 rs ms ms' HK HFL)|].
      split; [exact (gb_input_keep cx fp W3 rs ms ms' HK HIN)|].
      split; [exact (gb_gslots_fr_keep B MT cx fp W3 HB rs ms ms' HK HFRS)|].
      exact (gb_gprev_keep cx fp W3 rs ms ms' bs HK HPV).
    + split; [exact (gb_gcursor_keep B MT cx fp W3 HB rs ms ms' pos HK HCU)|].
      split; [exact (gb_gslot_keep B MT cx fp W3 HB rs ms ms' 0x68 i HK ltac:(lia) ltac:(lia) H68)|].
      split; [exact (gb_gslot_keep B MT cx fp W3 HB rs ms ms' 0x48 _ HK ltac:(lia) ltac:(lia) H48) | exact R20].
  - split; [exact Hnch|].
    split; [exact (gb_gslot_keep B MT cx fp W3 HB rs ms ms' 0x58 nch HK ltac:(lia) ltac:(lia) S58)|].
    split; [exact (gb_gslot_keep B MT cx fp W3 HB rs ms ms' 0x30 _ HK ltac:(lia) ltac:(lia) S30)|].
    split; [exact Hlf|]. split; [exact HW|]. split; [exact Hwant|].
    split; [exact R22|]. split; [exact R26 | exact R25].
Qed.

(* r is the call's own block: the caller's blocks do not hold it (ablocks has no duplicate). *)
Lemma ca_r_fresh : forall cx ly3 S3 W3 mem md r,
  AR SEGS B ly3 S3 W3 mem md -> gblk1 B cx ly3 S3 r -> ~ In (r, REG_SIZE) (ablocks B (c_ly cx) (c_S cx)).
Proof.
  intros cx ly3 S3 W3 mem md r HAR HBL Hin.
  apply in_split in Hin as (l1 & l2 & E0).
  unfold gblk1 in HBL. rewrite E0, <- app_assoc in HBL. cbn [app] in HBL.
  pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 mem md (r, REG_SIZE) (r, REG_SIZE) l1 l2 [] HAR HBL) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. change (req_size REG_SIZE) with 288 in Hd. lia.
Qed.

(* reac_boxreg_add writes only its own stack window and the registry block r: every byte of the case's own
   memory but r's is kept. *)
Lemma ca_keep_add : forall cx fp k ly3 S3 W3 ms md r STK1 memc mdc mem2 md2 k1,
  gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 (ms_mem ms) md k ->
  frames S3 = [(GB_CID, fp)] -> gblk1 B cx ly3 S3 r ->
  ajournal SEGS B STK1 (c_sp1 cx) [(r, r + REG_SIZE)] ly3 S3 W3 memc mdc [] ly3 S3 W3 mem2 md2 k1 ->
  gb_keep cx fp W3 [] memc mem2.
Proof.
  intros cx fp k ly3 S3 W3 ms md r STK1 memc mdc mem2 md2 k1 HB HJ HFR HBL HJ1 a Ha.
  pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & _ & F4 & _).
  pose proof HJ as (HAR & _).
  pose proof (gb_sp_facts B MT cx HB) as (Hal16 & Hlo & Hhi & Hsp1).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gb_F_facts B MT LAWS cx fp W3 ms ly3 S3 md k HB HJ HFR) as (HF0 & HFc & HFia & _ & HSHeq).
  pose proof (gb_frame_addr_eq B MT LAWS cx fp W3 ms ly3 S3 md k HB HJ) as Efa.
  assert (Hrin : In (r, REG_SIZE) (ablocks B ly3 S3))
    by (unfold gblk1 in HBL; rewrite HBL; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR Hrin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
  change (req_size REG_SIZE) with 288 in Hrceil, Hria.
  assert (Hfin : In (GB_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms) md r REG_SIZE GB_CID fp HAR Hrin Hfin) as Hdf.
  unfold zdisjoint in Hdf. cbn [fst snd] in Hdf. change (req_size REG_SIZE) with 288 in Hdf.
  rewrite Efa in Hdf. change (fs_frame_bytes GB_CID) with 512 in Hdf.
  assert (NFP : forall a, ~ (r <= a < r + 288) -> ~ inFP [(r, r + REG_SIZE)] a).
  { intros x Hx Hin. apply inFP_cons in Hin as [Hin | Hin]; [unfold REG_SIZE in Hin; lia | exact (inFP_nil x Hin)]. }
  assert (Hsa : shadow_addr (gF cx fp) = gSH cx fp) by (unfold shadow_addr; rewrite HSHeq; reflexivity).
  destruct HB as (_ & _ & _ & Hpn & _).
  destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
  - apply F1; lia.
  - destruct Hpn as [[Hn0 _] | [Hn Hin]]; [lia|].
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hq].
    assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
      by (unfold gblk1 in HBL; rewrite HBL; apply in_or_app; left; exact Hin).
    assert (Hne : (c_p cx, c_n cx) <> (r, REG_SIZE)).
    { intros E0. apply (ca_r_fresh cx ly3 S3 W3 (ms_mem ms) md r HAR HBL). rewrite <- E0. exact Hin. }
    pose proof (sep_blocks SEGS B LAWS ly3 S3 W3 (ms_mem ms) md _ _ _ _ HAR Hin3 Hrin Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size REG_SIZE) with 288 in Hd.
    replace a with (c_p cx + (a - c_p cx)) by lia.
    apply (F2 (c_p cx) (c_n cx) (a - c_p cx) Hin3 Hin3); [lia|]. apply NFP. lia.
  - change (fs_frame_bytes GB_CID) with 512 in Ha. apply (F4 GB_CID fp a Hfin).
    + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa. change (fs_frame_bytes GB_CID) with 512. lia.
    + apply NFP. lia.
  - apply (F4 GB_CID fp a Hfin).
    + right. unfold in_zr. cbn [fst snd]. rewrite Efa, Hsa. exact Ha.
    + apply NFP. change (fs_frame_bytes GB_CID / 8) with 64 in Ha. rewrite HSHeq in Ha.
      assert (Hd0 : 0 <= gF cx fp / 8) by (apply Z.div_pos; lia).
      assert (Hd1 : gF cx fp / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
      revert Ha Hria Hr4096 Hrceil Hd0 Hd1 C1 C3 C5. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL.
      clear. intros. lia.
  - apply Exists_exists in Ha as (x & [] & _).
Qed.

(* ---- the four program calls and the bcmp of this piece, at the machine level ---- *)
Lemma ca_call_regs : forall cx (regs : bvmap 5 word) ret,
  gb_base B MT cx ->
  getr regs 2 = w64 (c_sp1 cx) -> getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
  getr regs 1 = Z_to_bv 64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  spZ regs = spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx)) /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  YK0s.ret_ok (getr regs 1) /\ 4096 <= bv_unsigned (getr regs 1) /\
  (c_sp1 cx - spZ (c_regs cx)) mod 16 = 0 /\ c_sp1 cx - spZ (c_regs cx) <= 0 /\
  alloc_ceiling + 32768 - 288 <= c_sp1 cx.
Proof.
  intros cx regs ret HB R2 R3 R4 R1 Hret Hret2.
  pose proof (gb_sp_facts B MT cx HB) as (Hal16 & Hlo & Hhi & Hsp1).
  pose proof (gb_sp1_al B MT cx HB) as Hsp1al.
  pose proof asan_consts as (C1 & _).
  pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBok.
  pose proof HB as ((_ & _ & _ & Hgp0 & Htp0 & _) & _).
  split; [unfold spZ; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; lia|].
  split; [rewrite R3; exact Hgp0|]. split; [rewrite R4; exact Htp0|].
  split; [rewrite R1; apply ret_ok_codeptr_v; [lia | exact Hret2]|].
  split; [rewrite R1, unsigned_lit_small by lia; lia|].
  split; [apply ca_sub_mod16; [exact Hsp1al | exact Hal16]|].
  lia.
Qed.

Lemma ca_find_at : forall cx fp k ly3 S3 W3 ms0 mdc r bs M ret Q,
  gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 (ms_mem ms0) mdc k ->
  frames S3 = [(GB_CID, fp)] -> gblk1 B cx ly3 S3 r ->
  getr (ms_regs ms0) 2 = w64 (c_sp1 cx) -> getr (ms_regs ms0) 3 = getr (c_regs cx) 3 ->
  getr (ms_regs ms0) 4 = getr (c_regs cx) 4 -> getr (ms_regs ms0) 8 = w64 (spZ (c_regs cx)) ->
  getr (ms_regs ms0) 1 = Z_to_bv 64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  getr (ms_regs ms0) 10 = w64 r -> getr (ms_regs ms0) 11 = w64 (gF cx fp + GO_MAC) ->
  greg B ly3 S3 W3 ms0 r bs -> Boxreg.boxreg_B1 bs ->
  gsaved cx W3 ms0 -> gshadow cx fp W3 ms0 GSH_it -> c1mac cx fp W3 ms0 M ->
  (forall regs2 mem2 md2 known,
     ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
       [(GB_CID, fp)] ly3 S3 W3 mem2 md2 k ->
     aregs_preserved (ms_regs ms0) regs2 -> gb_keep cx fp W3 [(r, REG_SIZE)] (ms_mem ms0) mem2 ->
     getr regs2 10 = w64 known -> reac_boxreg_find_c.find_result bs M known ->
     SRr SEGS W3 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + ret)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W3 (mkCfg (mkst (ms_regs ms0) (Z_to_bv 64 (SIGMA BS_reac_boxreg_find)) (ms_mem ms0) (seg_rom SEGS)) mdc) Q.
Proof.
  intros cx fp k ly3 S3 W3 ms0 mdc r bs M ret Q HB HJ HFR HBL R2 R3 R4 R8 R1 Hret Hret2 R10 R11 HREG HB1
    HSV HSH HMAC HK.
  destruct (ca_call_regs cx (ms_regs ms0) ret HB R2 R3 R4 R1 Hret Hret2)
    as (Qsp & Qgp & Qtp & Qra & Qra4 & Ho16 & Ho & Hceil).
  pose proof (gb_sp_facts B MT cx HB) as (Hal16 & Hlo & Hhi & Hsp1).
  pose proof asan_consts as (C1 & _).
  pose proof HJ as (HAR3 & _).
  assert (Hrin : In (r, REG_SIZE) (ablocks B ly3 S3))
    by (unfold gblk1 in HBL; rewrite HBL; apply in_or_app; right; left; reflexivity).
  rewrite pa_sigma_reac_boxreg_find.
  eapply SRr_bind.
  { eapply (cl_callS B LAWS W3 (ms_regs ms0) (ms_mem ms0) _ GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx)
      (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 mdc k ReacBoxregFind.REAC_BOXREG_FIND_STK [] 0
      (c_sp1 cx - spZ (c_regs cx)) (getr (ms_regs ms0) 1) (gch cx)
      (fun ly' S' W' regs' mem' md' => ly' = ly3 /\ S' = S3 /\ W' = W3 /\ Permutation (ablocks B ly' S') (ablocks B ly3 S3) /\
        (forall i, 0 <= i < REG_SIZE ->
          aview SEGS (w_H W') mem' (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) /\
        (forall i, 0 <= i < 6 ->
          aview SEGS (w_H W') mem' (gF cx fp + GO_MAC + i) = Some (bv_unsigned (nth (Z.to_nat i) M (Z_to_bv 8 0)))) /\
        exists z, getr regs' 10 = w64 z /\ reac_boxreg_find_c.find_result bs M z) HJ Qsp);
    [ exact Ho16 | exact Ho | unfold ReacBoxregFind.REAC_BOXREG_FIND_STK, ESTACK; lia
    | unfold ReacBoxregFind.REAC_BOXREG_FIND_STK, ESTACK, GB_STK; lia | exact Qgp | exact Qtp | reflexivity
    | exact Qra | exact Qra4 | | | intros a Ha; exfalso; exact (inFP_nil a Ha) ].
    - replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) by lia.
      unfold s0Z. rewrite R8. unfold w64. rewrite unsigned_lit_small by lia.
      exact (ca_achain cx ly3 S3 W3 (ms_mem ms0) _ _ _ (c_sp1 cx) HB HJ (proj1 HSV) (ca_gsaved_s0 cx W3 ms0 HSV) ltac:(lia)).
    - intros HPRE1.
      pose proof HREG as (_ & Hlen & Hbytes).
      pose proof HMAC as (HLM & HMb).
      exact (TFIND ly3 S3 W3 _ _ _ (gch cx) r (gF cx fp + GO_MAC) bs M HPRE1 R10 R11 Hrin Hlen Hbytes HB1
        (ca_afobj cx fp k ly3 S3 W3 ms0 _ HB HJ HFR HSH) HLM HMb). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & (-> & -> & -> & _ & _ & _ & (known & Ha0 & Hfnd))).
  rewrite Z.add_0_r in HJ2.
  replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) in HJc by lia.
  rewrite R1. apply (HK regs2 mem2 md2 known HJ2 HP2); [|exact Ha0 | exact Hfnd].
  eapply (gb_keep_call B MT LAWS cx fp W3 ms0 ly3 S3 mdc k HB HJ HFR [(r, REG_SIZE)]); [lia | | | exact HJc].
  - intros p n Hpn. unfold gblk1 in HBL. rewrite HBL. apply in_or_app. left. exact Hpn.
  - constructor; [|constructor]. exists REG_SIZE. cbn [fst snd]. split; [exact Hrin | change (req_size REG_SIZE) with 288; unfold REG_SIZE; lia].
Qed.

Lemma ca_add_at : forall cx fp k ly3 S3 W3 ms0 mdc r bs M nch ret Q,
  gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 (ms_mem ms0) mdc k ->
  frames S3 = [(GB_CID, fp)] -> gblk1 B cx ly3 S3 r ->
  getr (ms_regs ms0) 2 = w64 (c_sp1 cx) -> getr (ms_regs ms0) 3 = getr (c_regs cx) 3 ->
  getr (ms_regs ms0) 4 = getr (c_regs cx) 4 -> getr (ms_regs ms0) 8 = w64 (spZ (c_regs cx)) ->
  getr (ms_regs ms0) 1 = Z_to_bv 64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  getr (ms_regs ms0) 10 = w64 r -> getr (ms_regs ms0) 11 = w64 (gF cx fp + GO_MAC) ->
  getr (ms_regs ms0) 12 = w64 nch -> 0 <= nch < 256 ->
  greg B ly3 S3 W3 ms0 r bs -> Boxreg.boxreg_inv bs ->
  gsaved cx W3 ms0 -> gshadow cx fp W3 ms0 GSH_it -> c1mac cx fp W3 ms0 M ->
  (forall regs2 mem2 md2 z bs',
     ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
       [(GB_CID, fp)] ly3 S3 W3 mem2 md2 k ->
     aregs_preserved (ms_regs ms0) regs2 -> gb_keep cx fp W3 [] (ms_mem ms0) mem2 ->
     getr regs2 10 = w64 z -> reac_boxreg_add_c.add_out bs M nch z bs' ->
     greg B ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + ret)) mem2 (seg_rom SEGS)) r bs' ->
     SRr SEGS W3 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + ret)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W3 (mkCfg (mkst (ms_regs ms0) (Z_to_bv 64 (SIGMA BS_reac_boxreg_add)) (ms_mem ms0) (seg_rom SEGS)) mdc) Q.
Proof.
  intros cx fp k ly3 S3 W3 ms0 mdc r bs M nch ret Q HB HJ HFR HBL R2 R3 R4 R8 R1 Hret Hret2 R10 R11 R12 Hnch
    HREG HIb HSV HSH HMAC HK.
  destruct (ca_call_regs cx (ms_regs ms0) ret HB R2 R3 R4 R1 Hret Hret2)
    as (Qsp & Qgp & Qtp & Qra & Qra4 & Ho16 & Ho & Hceil).
  pose proof (gb_sp_facts B MT cx HB) as (Hal16 & Hlo & Hhi & Hsp1).
  pose proof asan_consts as (C1 & _).
  pose proof HJ as (HAR3 & _).
  assert (Hrin : In (r, REG_SIZE) (ablocks B ly3 S3))
    by (unfold gblk1 in HBL; rewrite HBL; apply in_or_app; right; left; reflexivity).
  assert (Hstk : ReacBoxregAdd.REAC_BOXREG_ADD_STK = 8320) by (vm_compute; reflexivity).
  rewrite pa_sigma_reac_boxreg_add.
  eapply SRr_bind.
  { eapply (cl_callS B LAWS W3 (ms_regs ms0) (ms_mem ms0) _ GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx)
      (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 mdc k ReacBoxregAdd.REAC_BOXREG_ADD_STK [(r, r + REG_SIZE)] 0
      (c_sp1 cx - spZ (c_regs cx)) (getr (ms_regs ms0) 1) (gch cx)
      (fun ly' S' W' regs' mem' md' => ly' = ly3 /\ S' = S3 /\ W' = W3 /\ Permutation (ablocks B ly' S') (ablocks B ly3 S3) /\
        exists z bs', getr regs' 10 = w64 z /\ reac_boxreg_add_c.add_out bs M nch z bs' /\
        (forall i, 0 <= i < REG_SIZE ->
          aview SEGS (w_H W') mem' (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs' (Z_to_bv 8 0))))) HJ Qsp);
    [ exact Ho16 | exact Ho | rewrite Hstk; lia | rewrite Hstk; unfold GB_STK; lia | exact Qgp | exact Qtp | reflexivity
    | exact Qra | exact Qra4 | | | ].
    - replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) by lia.
      unfold s0Z. rewrite R8. unfold w64. rewrite unsigned_lit_small by lia.
      exact (ca_achain cx ly3 S3 W3 (ms_mem ms0) _ _ _ (c_sp1 cx) HB HJ (proj1 HSV) (ca_gsaved_s0 cx W3 ms0 HSV) ltac:(lia)).
    - intros HPRE1.
      pose proof HREG as (_ & Hlen & Hbytes).
      pose proof HMAC as (HLM & HMb).
      exact (TADD ly3 S3 W3 _ _ _ (gch cx) r (gF cx fp + GO_MAC) nch bs M HPRE1 R10 R11 R12 ltac:(lia) Hrin Hbytes HIb
        (ca_afobj cx fp k ly3 S3 W3 ms0 _ HB HJ HFR HSH) HLM HMb).
    - intros a Ha. right. apply inFP_cons in Ha as [Ha | Ha]; [|exfalso; exact (inFP_nil a Ha)].
      exists r, REG_SIZE. split; [exact Hrin|]. split; [exact (ca_r_fresh cx ly3 S3 W3 _ _ r HAR3 HBL)|].
      change (req_size REG_SIZE) with 288. unfold REG_SIZE in Ha. lia. }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & (-> & -> & -> & _ & (z & bs' & Ha0 & Hadd & Hbytes'))).
  rewrite Z.add_0_r in HJ2.
  replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) in HJc by lia.
  pose proof HREG as (_ & _ & _).
  rewrite R1. apply (HK regs2 mem2 md2 z bs' HJ2 HP2); [| exact Ha0 | exact Hadd |].
  - exact (ca_keep_add cx fp k ly3 S3 W3 ms0 mdc r _ _ _ _ _ _ HB HJ HFR HBL HJc).
  - split; [exact Hrin|]. split; [|exact Hbytes'].
    pose proof (c1_after_add bs M nch z bs' HIb (proj1 HMAC) Hadd) as (HIb' & _).
    exact (LLVMFuzzerTestOneInput_case1.c1_inv_len bs' HIb').
Qed.

(* box z's MAC bytes, as bytes of the registry. *)
Lemma ca_mac_nth : forall bs z j, length bs = 288%nat -> 0 <= z <= 4 -> 0 <= j < 6 ->
  nth (Z.to_nat j) (Boxreg.bx_mac bs z) (Z_to_bv 8 0) = nth (Z.to_nat (56 * z + j)) bs (Z_to_bv 8 0).
Proof.
  intros bs z j HL Hz Hj. unfold Boxreg.bx_mac, Boxreg.bsub. rewrite nth_firstn.
  destruct (Nat.ltb_spec (Z.to_nat j) (Z.to_nat 6)); [|lia]. rewrite nth_skipn. f_equal. lia.
Qed.

Lemma ca_bcmp_at : forall cx fp k ly3 S3 W3 ms0 mdc r bs' M z ret Q,
  gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 (ms_mem ms0) mdc k ->
  frames S3 = [(GB_CID, fp)] -> gblk1 B cx ly3 S3 r ->
  getr (ms_regs ms0) 2 = w64 (c_sp1 cx) -> getr (ms_regs ms0) 3 = getr (c_regs cx) 3 ->
  getr (ms_regs ms0) 4 = getr (c_regs cx) 4 ->
  getr (ms_regs ms0) 1 = Z_to_bv 64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  getr (ms_regs ms0) 10 = w64 (r + 56 * z) -> getr (ms_regs ms0) 11 = w64 (gF cx fp + GO_MAC) ->
  getr (ms_regs ms0) 12 = w64 6 -> 0 <= z <= 4 ->
  greg B ly3 S3 W3 ms0 r bs' -> Boxreg.bx_mac bs' z = M ->
  gshadow cx fp W3 ms0 GSH_it -> c1mac cx fp W3 ms0 M ->
  (forall regs2 mem2 md2,
     ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
       [(GB_CID, fp)] ly3 S3 W3 mem2 md2 k ->
     aregs_preserved (ms_regs ms0) regs2 -> gb_keep cx fp W3 [(r, REG_SIZE)] (ms_mem ms0) mem2 ->
     getr regs2 10 = w64 0 ->
     SRr SEGS W3 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + ret)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W3 (mkCfg (mkst (ms_regs ms0) (Z_to_bv 64 (SIGMA BS___interceptor_trampoline_bcmp)) (ms_mem ms0)
    (seg_rom SEGS)) mdc) Q.
Proof.
  intros cx fp k ly3 S3 W3 ms0 mdc r bs' M z ret Q HB HJ HFR HBL R2 R3 R4 R1 Hret Hret2 R10 R11 R12 Hz
    HREG HMz HSH HMAC HK.
  destruct (ca_call_regs cx (ms_regs ms0) ret HB R2 R3 R4 R1 Hret Hret2)
    as (Qsp & Qgp & Qtp & Qra & Qra4 & Ho16 & Ho & Hceil).
  pose proof (gb_sp_facts B MT cx HB) as (Hal16 & Hlo & Hhi & Hsp1).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HJ as (HAR3 & _).
  pose proof (gb_F_facts B MT LAWS cx fp W3 ms0 ly3 S3 mdc k HB HJ HFR) as (HF0 & HFc & HFia & _ & HSHeq).
  pose proof (gb_frame_addr_eq B MT LAWS cx fp W3 ms0 ly3 S3 mdc k HB HJ) as Efa.
  assert (Hfin : In (GB_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  assert (Hrin : In (r, REG_SIZE) (ablocks B ly3 S3))
    by (unfold gblk1 in HBL; rewrite HBL; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR3 Hrin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
  change (req_size REG_SIZE) with 288 in Hrceil, Hria.
  pose proof HREG as (_ & HL & Hbytes). pose proof HMAC as (HLM & HMb).
  assert (Hes : ESTACK = 4096) by reflexivity.
  assert (HX : forall j, 0 <= j < 6 -> aview SEGS (w_H W3) (ms_mem ms0) (r + 56 * z + j) =
             Some (bv_unsigned (nth (Z.to_nat (56 * z + j)) bs' (Z_to_bv 8 0)))).
  { intros j Hj. replace (r + 56 * z + j) with (r + (56 * z + j)) by lia. apply Hbytes. unfold REG_SIZE. lia. }
  eapply SRr_bind.
  { eapply (aj_bcmp_at SEGS B LAWS pa_segs_low _ ABCMP W3 (ms_regs ms0) (ms_mem ms0) GB_STK (spZ (c_regs cx)) []
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 mdc k
      (r + 56 * z) (gF cx fp + GO_MAC) 6 (c_sp1 cx - spZ (c_regs cx)) (getr (ms_regs ms0) 1) HJ);
    first [ exact R10 | exact R11 | exact R12 | exact Qsp | exact Ho16 | exact Ho | exact Qgp | exact Qtp
          | exact Qra | reflexivity | idtac ].
    - lia.
    - lia.
    - lia.
    - unfold GO_MAC. lia.
    - unfold GO_MAC. lia.
    - rewrite Hes. unfold GB_STK. lia.
    - intros a Ha. split; [replace a with (r + 56 * z + (a - (r + 56 * z))) by lia; rewrite HX by lia; discriminate|].
      rewrite Qsp, Hes. lia.
    - intros a Ha. split; [replace a with (gF cx fp + GO_MAC + (a - (gF cx fp + GO_MAC))) by lia; rewrite HMb by lia; discriminate|].
      rewrite Qsp, Hes. unfold GO_MAC in Ha. lia.
    - intros a Ha. rewrite Hes. lia.
    - intros a Ha. rewrite Hes. unfold GO_MAC in Ha. lia.
    - eapply (amem_range_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms0) mdc r REG_SIZE); [exact HAR3 | exact Hrin | lia |
        change (req_size REG_SIZE) with 288; lia].
    - exact (amem_range_sub_app _ _ (gF cx fp + GO_MAC) 6 HFia HFc ltac:(unfold GO_MAC; lia) ltac:(unfold GO_MAC; lia) ltac:(lia)).
    - eapply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms0) mdc r REG_SIZE); [exact HAR3 | exact Hrin | lia |
        change (req_size REG_SIZE) with 288; lia].
    - intros _. eapply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms0) mdc r REG_SIZE);
        [exact HAR3 | exact Hrin | lia | change (req_size REG_SIZE) with 288; lia | lia].
    - replace (gF cx fp + GO_MAC) with (gF cx fp + GO_MAC + 0) by lia.
      exact (gb_mac_ra B MT LAWS cx fp W3 ms0 ly3 S3 mdc k HB HJ HFR 0 6 HSH ltac:(lia) ltac:(lia)).
    - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms0) mdc GB_CID fp); [exact HAR3 | exact Hfin | | | lia];
        rewrite Efa; change (fs_frame_bytes GB_CID) with 512; unfold GO_MAC; lia. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP & Hv & Hcmp & Hfr & _).
  rewrite R1. apply (HK regs2 mem2 md2 HJ2 HP).
  - intros a Ha. apply Hfr.
    + destruct HB as (_ & _ & _ & Hpn & _).
      destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]]; [lia | | change (fs_frame_bytes GB_CID) with 512 in Ha; lia | | ].
      * destruct Hpn as [[Hn0 _] | [Hn Hin]]; [lia|].
        assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
          by (unfold gblk1 in HBL; rewrite HBL; apply in_or_app; left; exact Hin).
        destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (_ & Hp4096 & Hpceil & _).
        pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hq]. lia.
      * change (fs_frame_bytes GB_CID / 8) with 64 in Ha. rewrite HSHeq in Ha.
        assert (Hd0 : 0 <= gF cx fp / 8) by (apply Z.div_pos; lia).
        assert (Hd1 : gF cx fp / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
        unfold SHADOW_OFF in Ha. lia.
      * apply Exists_exists in Ha as (x & [Hx | []] & Hb). subst x. cbn [fst snd] in Hb. unfold REG_SIZE in Hb. lia.
    + destruct HB as (_ & _ & _ & Hpn & _).
      destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]]; [lia | | change (fs_frame_bytes GB_CID) with 512 in Ha; lia | | ].
      * destruct Hpn as [[Hn0 _] | [Hn Hin]]; [lia|].
        assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
          by (unfold gblk1 in HBL; rewrite HBL; apply in_or_app; left; exact Hin).
        destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (_ & Hp4096 & Hpceil & _).
        pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hq]. lia.
      * change (fs_frame_bytes GB_CID / 8) with 64 in Ha. rewrite HSHeq in Ha.
        assert (Hd1 : gF cx fp / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
        unfold SHADOW_OFF in Ha. lia.
      * apply Exists_exists in Ha as (x & [Hx | []] & Hb). subst x. cbn [fst snd] in Hb. unfold REG_SIZE in Hb. lia.
  - rewrite Hv. apply Hcmp. intros j Hj. rewrite HX, HMb by lia. f_equal. f_equal.
    rewrite <- HMz. rewrite ca_mac_nth by (try exact HL; lia). reflexivity.
Qed.


(* ---- branch conditions as facts on Z ---- *)
Lemma ca_zcanon_in : forall z, 0 <= z < 2 ^ 64 -> zcanon z = z.
Proof. intros z Hz. unfold zcanon, M64. apply Z.mod_small. exact Hz. Qed.
Lemma ca_zcanon_neg : forall z, - 2 ^ 64 <= z < 0 -> zcanon z = z + 2 ^ 64.
Proof.
  intros z Hz. unfold zcanon, M64.
  replace (z mod 2 ^ 64) with ((z + 1 * 2 ^ 64) mod 2 ^ 64) by (apply Z.mod_add; lia).
  apply Z.mod_small. lia.
Qed.
Lemma ca_U_off : forall E n v x, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + x < 2 ^ 64 ->
  U E (SOff n x) = v + x.
Proof. intros E n v x F Hv Hx. rewrite U_SOff, F, unsigned_lit_small by exact Hv. apply ca_zcanon_in. exact Hx. Qed.
Lemma ca_U_off_neg : forall E n v x, ew E n = Z_to_bv 64 (- v) -> 0 < v < 2 ^ 63 -> x = 0 ->
  U E (SOff n x) = 2 ^ 64 - v.
Proof.
  intros E n v x F Hv ->. rewrite U_SOff, F. rewrite Z.add_0_r. unfold zcanon, M64.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia.
  replace (- v mod 2 ^ 64) with ((- v + 1 * 2 ^ 64) mod 2 ^ 64) by (apply Z.mod_add; lia).
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma ca_U_lit : forall E z, 0 <= z < 2 ^ 64 -> U E (SLit z) = z.
Proof. intros E z Hz. rewrite U_SLit. apply ca_zcanon_in. exact Hz. Qed.
Lemma ca_U_lit_neg : forall E z, - 2 ^ 64 <= z < 0 -> U E (SLit z) = z + 2 ^ 64.
Proof. intros E z Hz. rewrite U_SLit. apply ca_zcanon_neg. exact Hz. Qed.
Lemma ca_br_lt : forall E a b, branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (Sg E a <? Sg E b).
Proof. reflexivity. Qed.
Lemma ca_br_ge : forall E a b, branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (Sg E a <? Sg E b).
Proof. reflexivity. Qed.
Lemma ca_S_off : forall E n v, ew E n = Z_to_bv 64 v -> - 2 ^ 63 <= v < 2 ^ 63 -> Sg E (SOff n 0) = v.
Proof.
  intros E n v F Hv. unfold Sg. rewrite (LowestFreeBase.lfb_den_atom E n v F). apply Boxreg.signed_lit. lia.
Qed.
Lemma ca_S_lit : forall E z, - 2 ^ 63 <= z < 2 ^ 63 -> Sg E (SLit z) = z.
Proof.
  intros E z Hz. rewrite S_SLit. unfold bv_swrap, bv_wrap, bv_half_modulus. change (bv_modulus 64) with (2 ^ 64).
  change (2 ^ 64 / 2) with (2 ^ 63). Z.div_mod_to_equations. lia.
Qed.


(* The low bit of `s5 | (s7 < 0)` (0x8081c .. 0x80824). *)
Lemma ca_cond_or : forall E w5 known, ew E 21 = Z_to_bv 64 w5 -> 0 <= w5 < 2 ^ 64 ->
  ew E 23 = Z_to_bv 64 known -> - 2 ^ 63 <= known < 2 ^ 63 ->
  branch_taken BC_NE (sv_denot E (SAlu ALU_AND (SAlu ALU_OR (SOff 21 0) (SAlu ALU_SLT (SOff 23 0) (SLit 0))) (SLit 1)))
    (sv_denot E (SLit 0)) = negb ((Z.land w5 1 =? 0) && (0 <=? known)).
Proof.
  intros E w5 known F21 Hw F23 Hk. rewrite branch_ne_U, (ca_U_lit E 0) by lia.
  rewrite !U_SAlu. cbn [zalu_raw]. rewrite (ca_U_off E 21 w5 0 F21 Hw) by lia. rewrite Z.add_0_r.
  rewrite (ca_U_lit E 0) by lia. rewrite (ca_U_lit E 1) by lia.
  assert (Hs : bv_swrap 64 (U E (SOff 23 0)) = known).
  { rewrite <- (ca_S_off E 23 known F23 Hk). unfold Sg, U. reflexivity. }
  rewrite Hs. change (bv_swrap 64 0) with 0.

  assert (Hlor : forall b, 0 <= b <= 1 -> 0 <= Z.lor w5 b < 2 ^ 64).
  { intros b Hb. split; [apply Z.lor_nonneg; lia|].
    destruct (Z.eq_dec b 0) as [->|Hb1]; [rewrite Z.lor_0_r; lia|].
    replace b with 1 by lia.
    rewrite <- (Z.mod_small w5 (2 ^ 64)) by lia.
    assert (Hm : Z.lor (w5 mod 2 ^ 64) 1 = (Z.lor w5 1) mod 2 ^ 64).
    { apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec.
      destruct (Z.lt_ge_cases n 64).
      - rewrite !Z.mod_pow2_bits_low by lia. rewrite Z.lor_spec. reflexivity.
      - rewrite !Z.mod_pow2_bits_high by lia. rewrite Z.bits_above_log2 with (a := 1); [reflexivity | lia | cbn; lia]. }
    rewrite Hm. apply Z.mod_pos_bound. lia. }
  assert (Hb : 0 <= Z.land w5 1 <= 1).
  { assert (E1 : Z.land w5 1 = w5 mod 2) by (change 1 with (Z.ones 1); rewrite Z.land_ones by lia; reflexivity).
    rewrite E1. pose proof (Z.mod_pos_bound w5 2 ltac:(lia)). lia. }
  destruct (Z.ltb_spec known 0) as [Hk0 | Hk0].
  - rewrite (ca_zcanon_in 1) by lia. rewrite (ca_zcanon_in (Z.lor w5 1)) by (apply Hlor; lia).
    rewrite Z.land_lor_distr_l, Z.land_diag.
    assert (Hor1 : forall x, 0 <= x <= 1 -> Z.lor x 1 = 1)
      by (intros x Hx; destruct (Z.eq_dec x 0) as [->|]; [reflexivity | replace x with 1 by lia; reflexivity]).
    rewrite (Hor1 _ Hb). rewrite (ca_zcanon_in 1) by lia.
    destruct (Z.leb_spec 0 known); [lia|]. rewrite andb_false_r. reflexivity.
  - rewrite (ca_zcanon_in 0) by lia. rewrite Z.lor_0_r. rewrite (ca_zcanon_in w5) by lia.
    rewrite (ca_zcanon_in (Z.land w5 1)) by lia.
    destruct (Z.leb_spec 0 known); [|lia]. rewrite andb_true_r. reflexivity.
Qed.


Lemma ca_U_atomz : forall E n v, ew E n = Z_to_bv 64 v -> U E (SOff n 0) = zcanon v.
Proof.
  intros E n v F. rewrite U_SOff, F, Z.add_0_r, Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
Lemma ca_zc_eq : forall a b, - 2 ^ 63 <= a < 2 ^ 63 -> - 2 ^ 63 <= b < 2 ^ 63 -> (zcanon a =? zcanon b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold zcanon, M64.
  destruct (Z.eqb_spec a b) as [-> | Hne]; [apply Z.eqb_refl|]. apply Z.eqb_neq. intros Hm.
  apply Hne. Z.div_mod_to_equations. nia.
Qed.
Lemma ca_Fr : forall regs cx fp r nch lfw n (q : bv 5) v,
  Z.of_nat n = bv_unsigned q -> getr regs q = w64 v -> ew (ca_E regs cx fp r nch lfw) n = Z_to_bv 64 v.
Proof. intros regs cx fp r nch lfw n q v Hn Hq. rewrite (ca_ewR' regs cx fp r nch lfw n q Hn). exact Hq. Qed.
Lemma ca_Fx : forall regs cx fp r nch lfw j,
  (32 + j < A_TEXT)%nat -> ew (ca_E regs cx fp r nch lfw) (32 + j) = nth j (ca_ext cx fp r nch lfw) (Z_to_bv 64 0).
Proof. intros regs cx fp r nch lfw j Hj. unfold ca_E. apply ca_ewX. exact Hj. Qed.

Ltac ca_zbool :=
  repeat match goal with
  | H : negb _ = true |- _ => apply (proj1 (Bool.negb_true_iff _)) in H
  | H : negb _ = false |- _ => apply (proj1 (Bool.negb_false_iff _)) in H
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
  | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
  | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
  end.
(* A branch over atoms whose values are known and literals, as a fact on Z. *)
Ltac ca_bfact H :=
  first [rewrite branch_ne_U in H | rewrite branch_eq_U in H];
  repeat match type of H with
  | context [U ?Ex (SOff ?n 0)] =>
      match goal with F : ew Ex n = Z_to_bv 64 _ |- _ => rewrite (ca_U_atomz Ex n _ F) in H end
  | context [U ?Ex (SLit ?z)] => rewrite (U_SLit Ex z) in H
  end;
  first [ rewrite ca_zc_eq in H by lia
        | repeat match type of H with context [zcanon ?x] => rewrite (ca_zcanon_in x) in H by lia end ];
  ca_zbool.


(* ---- the landing at 0x80ab4 (GP_K) ---- *)
Lemma ca_land : forall i cx fp k acc ly3 S3 W3 ms md r bs bs' pos M nch lf z,
  c1_core cx fp GP_K ms -> ca_com i cx fp k acc ly3 S3 W3 ms r bs pos M nch lf z ->
  greg B ly3 S3 W3 ms r bs' -> getr (ms_regs ms) 21 = w64 (2 ^ 32 - 1) ->
  reac_boxreg_add_c.add_out bs M nch z bs' ->
  GI_K B MT i cx fp k acc ly3 S3 W3 ms md.
Proof.
  intros i cx fp k acc ly3 S3 W3 ms md r bs bs' pos M nch lf z HCO HCOM HREG R21 Hadd.
  pose proof HCOM as (HBASE & HMAC & _ & _ & _ & _ & _ & _ & _ & _ & R25).
  pose proof HBASE as (Hi & Hk & Hacc & HBL & HIb & HMEM & HSR & HCU & H68 & H48 & R20).
  pose proof HMEM as (HSV & HSH & HFL & HIN & HFRS & HPV).
  pose proof HCO as (Hpc & Hrv & Hsv & Hro & Hfr & Hfc & HGR).
  destruct (c1_after_add bs M nch z bs' HIb (proj1 HMAC) Hadd) as (HIb' & Hfab & Hkept & _).
  apply (c1_fin_K B MT i cx fp k acc ly3 S3 W3 ms md r bs bs' pos); try assumption.
  - repeat (split; [assumption|]). split; [exact gb_GSH_it_len|]. repeat (split; [assumption|]). assumption.
  - lia.
  - exact (c1_acc_step MT MTL i acc ltac:(lia) Hacc).
Qed.

Lemma ca_agree : forall regs ext, env_agree 32 (Ereg regs ext) (Eimg (Ereg regs ext)).
Proof. intros regs ext. split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

Lemma ca_kept_pi : forall regs0 cx fp r nch lfw ss H ms' (l : list (bv 5)),
  st_ok_pi SEGS VAL (ca_E regs0 cx fp r nch lfw) ss (restrict H ms') ->
  forallb (fun q : bv 5 => sv_eqb (sr_get (ss_regs ss) q) (SOff (Z.to_nat (bv_unsigned q)) 0)) l = true ->
  forall q, In q l -> getr (ms_regs ms') q = getr regs0 q.
Proof.
  intros regs0 cx fp r nch lfw ss H ms' l HS Hl q Hq.
  exact (regs_kept_of_st_ok_pi _ ss (restrict H ms') regs0 (ca_ext cx fp r nch lfw) l HS (ca_agree _ _) Hl q Hq).
Qed.

Lemma ca_kept_st : forall regs0 cx fp r nch lfw ss H ms' (l : list (bv 5)),
  st_ok SEGS (ca_E regs0 cx fp r nch lfw) ss (restrict H ms') ->
  forallb (fun q : bv 5 => sv_eqb (sr_get (ss_regs ss) q) (SOff (Z.to_nat (bv_unsigned q)) 0)) l = true ->
  forall q, In q l -> getr (ms_regs ms') q = getr regs0 q.
Proof.
  intros regs0 cx fp r nch lfw ss H ms' l HS Hl q Hq.
  exact (regs_kept_of_st_ok SEGS _ ss (restrict H ms') regs0 (ca_ext cx fp r nch lfw) l HS (ca_agree _ _) Hl q Hq).
Qed.

(* The machine part at a new pc, from the registers the walk and the calls keep. *)
Lemma ca_core_at : forall cx fp pc0 pc ms (regs : bvmap 5 word) mem,
  c1_core cx fp pc0 ms ->
  (forall q : bv 5, In q [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 24%bv] -> getr regs q = getr (ms_regs ms) q) ->
  c1_core cx fp pc (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)).
Proof.
  intros cx fp pc0 pc ms regs mem (_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G3 & G4 & G18 & G24)) HK.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. unfold gregs. cbn [ms_regs mkst].
  split; [rewrite (HK 2%bv ltac:(cbn; tauto)); exact G2|].
  split; [rewrite (HK 8%bv ltac:(cbn; tauto)); exact G8|].
  split; [rewrite (HK 9%bv ltac:(cbn; tauto)); exact G9|].
  split; [rewrite (HK 3%bv ltac:(cbn; tauto)); exact G3|].
  split; [rewrite (HK 4%bv ltac:(cbn; tauto)); exact G4|].
  split; [rewrite (HK 18%bv ltac:(cbn; tauto)); exact G18|].
  rewrite (HK 24%bv ltac:(cbn; tauto)); exact G24.
Qed.


(* After a run over read-only regions: the memory is the seat's, pointwise. *)
Ltac ca_upd HM :=
  repeat match goal with H : frame_of _ _ (mrestrict _ _) _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  lazymatch goal with HF : frame_of ?Ex ?rs (ms_mem ?prev) (ms_mem ?new) |- _ =>
    lazymatch type of HM with forall x, ms_mem prev x = ms_mem ?m0 x =>
      let H2 := fresh "HMn" in
      assert (H2 : forall x, ms_mem new x = ms_mem m0 x)
        by (intros x; rewrite (ca_ro_same Ex rs _ _
              ltac:(let rs' := eval vm_compute in rs in change rs with rs';
                    repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil) HF x); apply HM);
      clear HF HM; rename H2 into HM end end.
Ltac ca_awr := cbn [ss_mem add_cond]; repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.


(* ---- the registry's fields and r->n's shadow byte as regions of the engine's state ---- *)
Lemma ca_rfield_ok : forall E (H : word -> bool) mem r bs off e,
  ew E 20 = Z_to_bv 64 r -> 0 <= r -> r + 288 <= 2 ^ 64 -> length bs = 288%nat ->
  (forall i, 0 <= i < REG_SIZE -> aview SEGS H mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
  0 <= off -> off + 4 <= 288 -> 0 <= Boxreg.rd4 bs off ->
  sv_denot E e = Z_to_bv 64 (Boxreg.rd4 bs off) ->
  YP09.region_ok SEGS E (mrestrict H mem) (YP09.mkRegion (Some 20%nat) off (off + 4) 0 0 [YP09.mkChunk off (CVal 4 e)]).
Proof.
  intros E H mem r bs off e F20 Hr0 Hr1 HL Hb Ho0 Ho1 Hv He.
  pose proof (Boxreg.rd4_range bs off) as Hrg.
  assert (Ub : YP09.base_val E (Some 20%nat) = r) by (cbn [YP09.base_val]; rewrite F20; apply unsigned_lit_small; lia).
  unfold YP09.region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. cbv zeta. rewrite Ub.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ r off 4%N e (Boxreg.rd4 bs off) He); [cbn [Z.of_N]; lia | cbn [Z.of_N]; lia |].
  cbn [N.to_nat]. exact (LowestFreeBase.lfb_val_mem4 H mem r bs off Hb HL Ho0 Ho1).
Qed.

Lemma ca_shbyte_ok : forall E (H : word -> bool) mem a,
  ew E 35 = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 - 1 -> aview SEGS H mem a = Some 0 ->
  YP09.region_ok SEGS E (mrestrict H mem) (YP09.mkRegion (Some 35%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))]).
Proof.
  intros E H mem a F35 Ha Hv.
  assert (Ub : YP09.base_val E (Some 35%nat) = a) by (cbn [YP09.base_val]; rewrite F35; apply unsigned_lit_small; lia).
  unfold YP09.region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. cbv zeta. rewrite Ub.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ a 0 1%N (SLit 0) 0 eq_refl); [cbn [Z.of_N]; lia | cbn [Z.of_N]; lia |].
  cbn [N.to_nat]. rewrite Z.add_0_r. exact (proj1 (val_mem1_of_aview SEGS H mem a 0 Hv)).
Qed.

(* r->n's shadow byte (r + 280 is 8-aligned: its granule lies in the block) is 0. *)
Lemma ca_sh280 : forall ly3 S3 W3 mem md r,
  AR SEGS B ly3 S3 W3 mem md -> In (r, REG_SIZE) (ablocks B ly3 S3) ->
  aview SEGS (w_H W3) mem (shadow_of_addr SHADOW_OFF (r + 280)) = Some 0.
Proof.
  intros ly3 S3 W3 mem md r HAR Hin.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR Hin) as (Hr16 & Hr4096 & _).
  pose proof (range_addressable_of_block SEGS B LAWS ly3 S3 W3 mem md r REG_SIZE (r + 280) 8 HAR Hin
    ltac:(lia) ltac:(change (req_size REG_SIZE) with 288; lia) (r + 287) ltac:(lia)) as (s & Hs & Hok).
  assert (E8 : shadow_of_addr SHADOW_OFF (r + 287) = shadow_of_addr SHADOW_OFF (r + 280)).
  { unfold shadow_of_addr. f_equal. Z.div_mod_to_equations. lia. }
  rewrite E8 in Hs. rewrite Hs. f_equal.
  destruct Hok as [-> | Hok]; [reflexivity|]. exfalso. Z.div_mod_to_equations. lia.
Qed.


Lemma ca_presq : forall (regsc regs2 : bvmap 5 word) (q : bv 5) v,
  aregs_preserved regsc regs2 -> acallee_saved (bv_unsigned q) -> getr regsc q = v -> getr regs2 q = v.
Proof.
  intros regsc regs2 q v HP Hq Hv. pose proof (HP (bv_unsigned q) Hq) as E0.
  rewrite Z_to_bv_bv_unsigned in E0. rewrite E0. exact Hv.
Qed.
Ltac ca_cs := unfold acallee_saved; cbn [bv_unsigned]; lia.

#[local] Ltac ca_cs ::= match goal with |- acallee_saved (bv_unsigned ?q) => let v := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with v end; unfold acallee_saved; lia.


Ltac ca_dj := cbn [ss_mem ca_ss YP09.all_disjoint]; unfold extent_disjoint, ca_spill;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val];
  repeat match goal with |- context [bv_unsigned (ew ?Ex ?n)] =>
    match goal with F : ew Ex n = Z_to_bv 64 _ |- _ => rewrite F end end;
  rewrite ?unsigned_lit_small by lia; repeat split; try exact I; lia.

Ltac ca_bf := match goal with H : branch_taken _ _ _ = _ |- _ => ca_bfact H end.


Lemma ca_br_sext_self : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 ->
  branch_taken BC_NE (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SOff n 0)) = false.
Proof.
  intros E n v F Hv. rewrite branch_ne_U, U_SExt, (ca_U_atomz E n v F), (ca_zcanon_in v) by lia.
  change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small v) by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus. change (bv_modulus 32) with (2 ^ 32). change (2 ^ 32 / 2) with (2 ^ 31).
  rewrite (Z.mod_small (v + 2 ^ 31)) by lia. replace (v + 2 ^ 31 - 2 ^ 31) with v by lia.
  rewrite (ca_zcanon_in v) by lia. rewrite Z.eqb_refl. reflexivity.
Qed.

End c.
End b.
End a.

(* The section's tactics, again outside it: a tactic defined inside a section ends with the section, and the
   segment files of the add piece use these. *)
Ltac ca_zbool :=
  repeat match goal with
  | H : negb _ = true |- _ => apply (proj1 (Bool.negb_true_iff _)) in H
  | H : negb _ = false |- _ => apply (proj1 (Bool.negb_false_iff _)) in H
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
  | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
  | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
  end.

Ltac ca_bfact H :=
  first [rewrite branch_ne_U in H | rewrite branch_eq_U in H];
  repeat match type of H with
  | context [U ?Ex (SOff ?n 0)] =>
      match goal with F : ew Ex n = Z_to_bv 64 _ |- _ => rewrite (ca_U_atomz Ex n _ F) in H end
  | context [U ?Ex (SLit ?z)] => rewrite (U_SLit Ex z) in H
  end;
  first [ rewrite ca_zc_eq in H by lia
        | repeat match type of H with context [zcanon ?x] => rewrite (ca_zcanon_in x) in H by lia end ];
  ca_zbool.

Ltac ca_upd HM :=
  repeat match goal with H : frame_of _ _ (mrestrict _ _) _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  lazymatch goal with HF : frame_of ?Ex ?rs (ms_mem ?prev) (ms_mem ?new) |- _ =>
    lazymatch type of HM with forall x, ms_mem prev x = ms_mem ?m0 x =>
      let H2 := fresh "HMn" in
      assert (H2 : forall x, ms_mem new x = ms_mem m0 x)
        by (intros x; rewrite (ca_ro_same Ex rs _ _
              ltac:(let rs' := eval vm_compute in rs in change rs with rs';
                    repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil) HF x); apply HM);
      clear HF HM; rename H2 into HM end end.
Ltac ca_awr := cbn [ss_mem add_cond]; repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

Ltac ca_cs := match goal with |- acallee_saved (bv_unsigned ?q) => let v := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with v end; unfold acallee_saved; lia.

Ltac ca_dj := cbn [ss_mem ca_ss YP09.all_disjoint]; unfold extent_disjoint, ca_spill;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val];
  repeat match goal with |- context [bv_unsigned (ew ?Ex ?n)] =>
    match goal with F : ew Ex n = Z_to_bv 64 _ |- _ => rewrite F end end;
  rewrite ?unsigned_lit_small by lia; repeat split; try exact I; lia.

Ltac ca_bf := match goal with H : branch_taken _ _ _ = _ |- _ => ca_bfact H end.
