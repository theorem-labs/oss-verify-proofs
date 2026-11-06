(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v, with its module paths and module names changed; 264 of its 309 lines of code are new or changed and 2644 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/fuzz_recv_cp.v, with its module names changed; 270 of its 315 lines of code are new or changed and 264 lines of the source are left out. *)
(* check_requests on image A: the definitions and the symbolic states of its walk (check_requests.v).
   The loop head +0xb0, after i turns of n = n_sent: s0 = m + 12 + 512 i (req[i]), s1 = s6 = m + 8208 + 8 i
   (req_len[i]), s2 = g + 262692 + 512 i (sent[i]), s3 = s7 = g + 270888 + 8 i (sent_len[i]), s4 = the shadow base,
   s5 = n - i, s8 = the shadow byte address of s7 (rq_inv); the frame holds the entry's ra and s0..s8 (rq_saved).
   Its symbolic state rq_lss names these as atoms 33..37 and the length sent_len[i] = req_len[i] as atom 38
   (rq_extra), with the two 8-byte cells as regions and shadow entries; rq_seat builds it.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC81 YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNoWrite LinkWalkNlk LinkWalkBcmp check_requests_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition RQ_SL : Z := LA_G_NL + NK_SENT_LEN.
Definition RQ_SD : Z := LA_G_NL + NK_SENT.
Lemma RQ_SL_val : RQ_SL = 6417640. Proof. reflexivity. Qed.
Lemma RQ_SD_val : RQ_SD = 6409444. Proof. reflexivity. Qed.

Ltac zrng := try change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); try change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32);
  try change (2 ^ (8 * Z.of_N 1)) with (2 ^ 8);
  try change (Z.of_N 8) with 8; try change (Z.of_N 4) with 4; try change (Z.of_N 1) with 1; lia.

Lemma rq_soff0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. apply bv_eq. change (U E (SOff n 0) = bv_unsigned (ew E n)). apply lf_U_reg. Qed.

Lemma rq_soffc : forall E n c v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E n c v H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by lia. reflexivity. Qed.

Definition rq_shx : sv := SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 34 0) (SLit 3)).

Lemma rq_denot_shx : forall E v sb, ew E 34 = Z_to_bv 64 v -> ew E 32 = Z_to_bv 64 sb ->
  0 <= v < 2 ^ 63 -> 0 <= sb < 2 ^ 32 ->
  sv_denot E (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 34 0) (SLit 3))) = Z_to_bv 64 (sb + v / 8).
Proof.
intros E v sb Hv Hs Hv0 Hs0. apply bv_eq.
change (U E (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 34 0) (SLit 3))) = bv_unsigned (Z_to_bv 64 (sb + v / 8))).
rewrite !U_SAlu, !lf_U_reg, U_SLit, Hv, Hs. rewrite !unsigned_lit_small by lia.
cbn [zalu_raw]. change (zcanon 3) with 3. change (Z.land 3 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold zcanon, M64.
pose proof (Z.div_pos v 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound v 8 v ltac:(lia) ltac:(lia)).
rewrite (Z.mod_small (v / 8)) by lia. apply Z.mod_small. lia.
Qed.

(* the entry state: the frame, the shadow base, n_sent (g_nl) and n_req (the model block at atom 10), both the atom 33 *)
Definition rq_ns : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 2)) NK_N_SENT (NK_N_SENT + 4) (NK_N_SENT + 4) (NK_N_SENT + 4)
    [YP09.mkChunk NK_N_SENT (CVal 4 (SOff 33 0))].
Definition rq_nr : YP09.region :=
  YP09.mkRegion (Some 10%nat) MD_N_REQ (MD_N_REQ + 4) (MD_N_REQ + 4) (MD_N_REQ + 4)
    [YP09.mkChunk MD_N_REQ (CVal 4 (SOff 33 0))].
Definition rq_regions : smem := [stack_region 80; got_regionP; bcell_regionP 32; rq_ns; rq_nr].
Definition rq_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0); (A_OBJ 2, mkAF LA_G_NL LA_G_NL 0);
           (10%nat, mkAF 0 (2 ^ 47 - MD_SIZE - 1) 0); (33%nat, mkAF 0 16 0)] [] [].
Definition rq_ss : sstate := mkSS AF_check_requests sr_atoms rq_regions None rq_facts.
Definition rq_SH : list shent := [mkSHE 10 MD_N_REQ (MD_N_REQ + 4)].
Definition rq_eextra (n : Z) : list word := map (Z_to_bv 64) [SB; n].

(* the loop head +0xb0 *)
Definition rq_sr : list sv :=
  [SLit 0; SOff 39 0; SOff 2 (-80); SOff 3 0; SOff 4 0; SOff 40 0; SOff 41 0; SOff 42 0;
   SOff 37 0; SOff 35 0;
   SOff 43 0; SOff 44 0; SOff 45 0; SOff 46 0; SOff 47 0; SOff 48 0; SOff 49 0; SOff 50 0;
   SOff 36 0; SOff 34 0; SOff 32 0; SOff 33 0; SOff 35 0; SOff 34 0; rq_shx;
   SOff 25 0; SOff 26 0; SOff 27 0; SOff 51 0; SOff 52 0; SOff 53 0; SOff 54 0].
Definition rq_frame : YP09.region :=
  YP09.mkRegion (Some 2%nat) (-80) 0 0 0
    [YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0));
     YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
     YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
     YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
     YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Definition rq_slr : YP09.region := YP09.mkRegion (Some 34%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 38 0))].
Definition rq_rlr : YP09.region := YP09.mkRegion (Some 35%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 38 0))].
Definition rq_lfacts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0);
           (33%nat, mkAF 1 16 0); (34%nat, mkAF RQ_SL (RQ_SL + 120) 3);
           (35%nat, mkAF 0 (2 ^ 47 - 8) 0); (36%nat, mkAF RQ_SD (RQ_SD + 7680) 0);
           (37%nat, mkAF 0 (2 ^ 47 - 512) 0); (38%nat, mkAF 0 512 0)] [] [].
Definition rq_lss (AF : Z) : sstate := mkSS (AF + 0xb0) rq_sr [rq_frame; rq_slr; rq_rlr] None rq_lfacts.
Definition rq_LSH : list shent := [mkSHE 34 0 8; mkSHE 35 0 8].

Definition rq_extra (regs : bvmap 5 word) (n i mp L : Z) : list word :=
  [Z_to_bv 64 SB; Z_to_bv 64 (n - i); Z_to_bv 64 (RQ_SL + 8 * i); Z_to_bv 64 (mp + MD_REQ_LEN + 8 * i);
   Z_to_bv 64 (RQ_SD + 512 * i); Z_to_bv 64 (mp + MD_REQ + 512 * i); Z_to_bv 64 L;
   getr regs 1; getr regs 5; getr regs 6; getr regs 7;
   getr regs 10; getr regs 11; getr regs 12; getr regs 13;
   getr regs 14; getr regs 15; getr regs 16; getr regs 17;
   getr regs 28; getr regs 29; getr regs 30; getr regs 31].

(* the registers at the loop head, for the turn with index i *)
Definition rq_inv (regs_e regs : bvmap 5 word) (n i mp : Z) : Prop :=
  getr regs 2 = Z_to_bv 64 (spZ regs_e - 80) /\
  getr regs 3 = getr regs_e 3 /\ getr regs 4 = getr regs_e 4 /\
  getr regs 8 = Z_to_bv 64 (mp + MD_REQ + 512 * i) /\
  getr regs 9 = Z_to_bv 64 (mp + MD_REQ_LEN + 8 * i) /\
  getr regs 18 = Z_to_bv 64 (RQ_SD + 512 * i) /\
  getr regs 19 = Z_to_bv 64 (RQ_SL + 8 * i) /\
  getr regs 20 = Z_to_bv 64 SB /\
  getr regs 21 = Z_to_bv 64 (n - i) /\
  getr regs 22 = Z_to_bv 64 (mp + MD_REQ_LEN + 8 * i) /\
  getr regs 23 = Z_to_bv 64 (RQ_SL + 8 * i) /\
  getr regs 24 = Z_to_bv 64 (SB + (RQ_SL + 8 * i) / 8) /\
  getr regs 25 = getr regs_e 25 /\ getr regs 26 = getr regs_e 26 /\ getr regs 27 = getr regs_e 27.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis LV : LinkVals.

Definition rq_E (regs_e regs : bvmap 5 word) (n i mp L : Z) : env := Eimg (Ereg regs_e (rq_extra regs n i mp L)).

(* the frame's ten saved words: the entry's ra and s0..s8 *)
Definition rq_saved (W : world SEGS) (mem : word -> option byte) (regs_e : bvmap 5 word) : Prop :=
  val_mem SEGS (rdW W mem) (spZ regs_e - 80) 8 (bv_unsigned (getr regs_e 24)) /\
  val_mem SEGS (rdW W mem) (spZ regs_e - 72) 8 (bv_unsigned (getr regs_e 23)) /\
  val_mem SEGS (rdW W mem) (spZ regs_e - 64) 8 (bv_unsigned (getr regs_e 22)) /\
  val_mem SEGS (rdW W mem) (spZ regs_e - 56) 8 (bv_unsigned (getr regs_e 21)) /\
  val_mem SEGS (rdW W mem) (spZ regs_e - 48) 8 (bv_unsigned (getr regs_e 20)) /\
  val_mem SEGS (rdW W mem) (spZ regs_e - 40) 8 (bv_unsigned (getr regs_e 19)) /\
  val_mem SEGS (rdW W mem) (spZ regs_e - 32) 8 (bv_unsigned (getr regs_e 18)) /\
  val_mem SEGS (rdW W mem) (spZ regs_e - 24) 8 (bv_unsigned (getr regs_e 9)) /\
  val_mem SEGS (rdW W mem) (spZ regs_e - 16) 8 (bv_unsigned (getr regs_e 8)) /\
  val_mem SEGS (rdW W mem) (spZ regs_e - 8) 8 (bv_unsigned (getr regs_e 1)).

Lemma rq_E_reg : forall regs_e regs n i mp L m (r : bv 5), Z.of_nat m = bv_unsigned r -> (m < 32)%nat ->
  ew (rq_E regs_e regs n i mp L) m = getr regs_e r.
Proof.
  intros regs_e regs n i mp L m r Hm Hlt. unfold rq_E.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm.
Qed.

Lemma rq_E_ext : forall regs_e regs n i mp L j, (j < 23)%nat ->
  ew (rq_E regs_e regs n i mp L) (32 + j) = nth j (rq_extra regs n i mp L) (Z_to_bv 64 0).
Proof.
  intros regs_e regs n i mp L j Hj. unfold rq_E.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra.
Qed.

Lemma rq_E_img : forall regs_e regs n i mp L, img_env VAL A_LIM (rq_E regs_e regs n i mp L).
Proof. intros. apply Eimg_env. Qed.

(* the loop head's state from the registers, the saved words and the two lengths *)
Lemma rq_seat : forall AF G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k
    (regs_e regs : bvmap 5 word) n i mp L,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
  spZ regs_e mod 16 = 0 -> sp0 - STK <= spZ regs_e - CHECK_REQUESTS_AK -> spZ regs_e <= sp0 ->
  rq_inv regs_e regs n i mp -> rq_saved W mem regs_e ->
  0 <= i -> i + 1 <= n -> n <= 16 -> 0 <= mp -> mp + MD_SIZE <= 2 ^ 47 - 1 -> 0 <= L <= 512 ->
  val_mem SEGS (rdW W mem) (RQ_SL + 8 * i) 8 L ->
  val_mem SEGS (rdW W mem) (mp + MD_REQ_LEN + 8 * i) 8 L ->
  (RQ_SL + 8 * i + 8 <= mp \/ mp + MD_SIZE <= RQ_SL + 8 * i) ->
  mp + MD_SIZE <= spZ regs_e - CHECK_REQUESTS_AK \/ spZ regs_e <= mp ->
  amem_range mp MD_SIZE ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (RQ_SL + 8 * i) 8 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (mp + MD_REQ_LEN + 8 * i) 8 ->
  st_ok_pi SEGS VAL (rq_E regs_e regs n i mp L) (rq_lss AF)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF + 0xb0))) mem (seg_rom SEGS))) /\
  sh_ok SEGS (SOff 32 0) rq_LSH (rq_E regs_e regs n i mp L) (rdW W mem).
Proof.
intros AF G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k regs_e regs n i mp L
  HJ H16 Hwlo Hwhi HINV HSV Hi0 Hin Hn16 Hmp1 Hmp2 HL VL1 VL2 Hsep Hapf Hamr RA1 RA2.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _).
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (HK : CHECK_REQUESTS_AK = 8272) by reflexivity.
assert (Hsp46 : 2 ^ 46 <= spZ regs_e <= 2 ^ 47) by lia.
destruct HINV as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
destruct HSV as (S8 & S7 & S6 & S5 & S4 & S3 & S2 & S1 & S0 & SRA).
set (E := rq_E regs_e regs n i mp L).
assert (HSL : RQ_SL = 6417640) by reflexivity.
assert (HSD : RQ_SD = 6409444) by reflexivity.
assert (HSBb : SB = 2147450880) by reflexivity.
assert (HMD : MD_SIZE = 8856 /\ MD_REQ_LEN = 8208 /\ MD_REQ = 12) by (repeat split; reflexivity).
destruct HMD as (HMD1 & HMD2 & HMD3).
assert (E1 : ew E 1 = getr regs_e 1) by (apply (rq_E_reg _ _ _ _ _ _ 1%nat 1%bv); [reflexivity | lia]).
assert (E2 : ew E 2 = getr regs_e 2) by (apply (rq_E_reg _ _ _ _ _ _ 2%nat 2%bv); [reflexivity | lia]).
assert (E3 : ew E 3 = getr regs_e 3) by (apply (rq_E_reg _ _ _ _ _ _ 3%nat 3%bv); [reflexivity | lia]).
assert (E4 : ew E 4 = getr regs_e 4) by (apply (rq_E_reg _ _ _ _ _ _ 4%nat 4%bv); [reflexivity | lia]).
assert (E8 : ew E 8 = getr regs_e 8) by (apply (rq_E_reg _ _ _ _ _ _ 8%nat 8%bv); [reflexivity | lia]).
assert (E9 : ew E 9 = getr regs_e 9) by (apply (rq_E_reg _ _ _ _ _ _ 9%nat 9%bv); [reflexivity | lia]).
assert (E18 : ew E 18 = getr regs_e 18) by (apply (rq_E_reg _ _ _ _ _ _ 18%nat 18%bv); [reflexivity | lia]).
assert (E19 : ew E 19 = getr regs_e 19) by (apply (rq_E_reg _ _ _ _ _ _ 19%nat 19%bv); [reflexivity | lia]).
assert (E20 : ew E 20 = getr regs_e 20) by (apply (rq_E_reg _ _ _ _ _ _ 20%nat 20%bv); [reflexivity | lia]).
assert (E21 : ew E 21 = getr regs_e 21) by (apply (rq_E_reg _ _ _ _ _ _ 21%nat 21%bv); [reflexivity | lia]).
assert (E22 : ew E 22 = getr regs_e 22) by (apply (rq_E_reg _ _ _ _ _ _ 22%nat 22%bv); [reflexivity | lia]).
assert (E23 : ew E 23 = getr regs_e 23) by (apply (rq_E_reg _ _ _ _ _ _ 23%nat 23%bv); [reflexivity | lia]).
assert (E24 : ew E 24 = getr regs_e 24) by (apply (rq_E_reg _ _ _ _ _ _ 24%nat 24%bv); [reflexivity | lia]).
assert (E25 : ew E 25 = getr regs_e 25) by (apply (rq_E_reg _ _ _ _ _ _ 25%nat 25%bv); [reflexivity | lia]).
assert (E26 : ew E 26 = getr regs_e 26) by (apply (rq_E_reg _ _ _ _ _ _ 26%nat 26%bv); [reflexivity | lia]).
assert (E27 : ew E 27 = getr regs_e 27) by (apply (rq_E_reg _ _ _ _ _ _ 27%nat 27%bv); [reflexivity | lia]).
assert (X32 : ew E 32 = Z_to_bv 64 SB) by exact (rq_E_ext _ _ _ _ _ _ 0%nat ltac:(lia)).
assert (X33 : ew E 33 = Z_to_bv 64 (n - i)) by exact (rq_E_ext _ _ _ _ _ _ 1%nat ltac:(lia)).
assert (X34 : ew E 34 = Z_to_bv 64 (RQ_SL + 8 * i)) by exact (rq_E_ext _ _ _ _ _ _ 2%nat ltac:(lia)).
assert (X35 : ew E 35 = Z_to_bv 64 (mp + MD_REQ_LEN + 8 * i)) by exact (rq_E_ext _ _ _ _ _ _ 3%nat ltac:(lia)).
assert (X36 : ew E 36 = Z_to_bv 64 (RQ_SD + 512 * i)) by exact (rq_E_ext _ _ _ _ _ _ 4%nat ltac:(lia)).
assert (X37 : ew E 37 = Z_to_bv 64 (mp + MD_REQ + 512 * i)) by exact (rq_E_ext _ _ _ _ _ _ 5%nat ltac:(lia)).
assert (X38 : ew E 38 = Z_to_bv 64 L) by exact (rq_E_ext _ _ _ _ _ _ 6%nat ltac:(lia)).
assert (X39 : ew E 39 = getr regs 1) by exact (rq_E_ext _ _ _ _ _ _ 7%nat ltac:(lia)).
assert (X40 : ew E 40 = getr regs 5) by exact (rq_E_ext _ _ _ _ _ _ 8%nat ltac:(lia)).
assert (X41 : ew E 41 = getr regs 6) by exact (rq_E_ext _ _ _ _ _ _ 9%nat ltac:(lia)).
assert (X42 : ew E 42 = getr regs 7) by exact (rq_E_ext _ _ _ _ _ _ 10%nat ltac:(lia)).
assert (X43 : ew E 43 = getr regs 10) by exact (rq_E_ext _ _ _ _ _ _ 11%nat ltac:(lia)).
assert (X44 : ew E 44 = getr regs 11) by exact (rq_E_ext _ _ _ _ _ _ 12%nat ltac:(lia)).
assert (X45 : ew E 45 = getr regs 12) by exact (rq_E_ext _ _ _ _ _ _ 13%nat ltac:(lia)).
assert (X46 : ew E 46 = getr regs 13) by exact (rq_E_ext _ _ _ _ _ _ 14%nat ltac:(lia)).
assert (X47 : ew E 47 = getr regs 14) by exact (rq_E_ext _ _ _ _ _ _ 15%nat ltac:(lia)).
assert (X48 : ew E 48 = getr regs 15) by exact (rq_E_ext _ _ _ _ _ _ 16%nat ltac:(lia)).
assert (X49 : ew E 49 = getr regs 16) by exact (rq_E_ext _ _ _ _ _ _ 17%nat ltac:(lia)).
assert (X50 : ew E 50 = getr regs 17) by exact (rq_E_ext _ _ _ _ _ _ 18%nat ltac:(lia)).
assert (X51 : ew E 51 = getr regs 28) by exact (rq_E_ext _ _ _ _ _ _ 19%nat ltac:(lia)).
assert (X52 : ew E 52 = getr regs 29) by exact (rq_E_ext _ _ _ _ _ _ 20%nat ltac:(lia)).
assert (X53 : ew E 53 = getr regs 30) by exact (rq_E_ext _ _ _ _ _ _ 21%nat ltac:(lia)).
assert (X54 : ew E 54 = getr regs 31) by exact (rq_E_ext _ _ _ _ _ _ 22%nat ltac:(lia)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs_e) by (rewrite E2; reflexivity).
assert (U34 : bv_unsigned (ew E 34) = RQ_SL + 8 * i) by (rewrite X34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = mp + MD_REQ_LEN + 8 * i) by (rewrite X35; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold rq_lss. apply pa_entry_st_ok_full.
  + apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
    repeat (destruct Hr as [<- | Hr]); [..|destruct Hr];
      [ lazymatch goal with |- _ = sv_denot ?EE (sr_get ?LL ?RR) =>
          let v := eval vm_compute in (sr_get LL RR) in change (sr_get LL RR) with v end .. ];
      [ rewrite getr_zero; reflexivity
      | rewrite rq_soff0, X39; reflexivity
      | rewrite (rq_soffc E 2 (-80) (spZ regs_e)); [exact R2 | rewrite E2; symmetry; apply Z_to_bv_bv_unsigned | lia]
      | rewrite rq_soff0, E3; exact R3
      | rewrite rq_soff0, E4; exact R4
      | rewrite rq_soff0, X40; reflexivity
      | rewrite rq_soff0, X41; reflexivity
      | rewrite rq_soff0, X42; reflexivity
      | rewrite rq_soff0, X37; exact R8
      | rewrite rq_soff0, X35; exact R9
      | rewrite rq_soff0, X43; reflexivity
      | rewrite rq_soff0, X44; reflexivity
      | rewrite rq_soff0, X45; reflexivity
      | rewrite rq_soff0, X46; reflexivity
      | rewrite rq_soff0, X47; reflexivity
      | rewrite rq_soff0, X48; reflexivity
      | rewrite rq_soff0, X49; reflexivity
      | rewrite rq_soff0, X50; reflexivity
      | rewrite rq_soff0, X36; exact R18
      | rewrite rq_soff0, X34; exact R19
      | rewrite rq_soff0, X32; exact R20
      | rewrite rq_soff0, X33; exact R21
      | rewrite rq_soff0, X35; exact R22
      | rewrite rq_soff0, X34; exact R23
      | rewrite (rq_denot_shx E (RQ_SL + 8 * i) SB X34 X32 ltac:(lia) ltac:(lia)); exact R24
      | rewrite rq_soff0, E25; exact R25
      | rewrite rq_soff0, E26; exact R26
      | rewrite rq_soff0, E27; exact R27
      | rewrite rq_soff0, X51; reflexivity
      | rewrite rq_soff0, X52; reflexivity
      | rewrite rq_soff0, X53; reflexivity
      | rewrite rq_soff0, X54; reflexivity ].
  + vm_compute. reflexivity.
  + unfold rq_frame, rq_slr, rq_rlr.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil; cbn [ms_mem restrict mkst];
        [ apply (chunk_ok_val SEGS E _ (spZ regs_e) (-80) 8 (SOff 24 0) (bv_unsigned (getr regs_e 24)))
        | apply (chunk_ok_val SEGS E _ (spZ regs_e) (-72) 8 (SOff 23 0) (bv_unsigned (getr regs_e 23)))
        | apply (chunk_ok_val SEGS E _ (spZ regs_e) (-64) 8 (SOff 22 0) (bv_unsigned (getr regs_e 22)))
        | apply (chunk_ok_val SEGS E _ (spZ regs_e) (-56) 8 (SOff 21 0) (bv_unsigned (getr regs_e 21)))
        | apply (chunk_ok_val SEGS E _ (spZ regs_e) (-48) 8 (SOff 20 0) (bv_unsigned (getr regs_e 20)))
        | apply (chunk_ok_val SEGS E _ (spZ regs_e) (-40) 8 (SOff 19 0) (bv_unsigned (getr regs_e 19)))
        | apply (chunk_ok_val SEGS E _ (spZ regs_e) (-32) 8 (SOff 18 0) (bv_unsigned (getr regs_e 18)))
        | apply (chunk_ok_val SEGS E _ (spZ regs_e) (-24) 8 (SOff 9 0) (bv_unsigned (getr regs_e 9)))
        | apply (chunk_ok_val SEGS E _ (spZ regs_e) (-16) 8 (SOff 8 0) (bv_unsigned (getr regs_e 8)))
        | apply (chunk_ok_val SEGS E _ (spZ regs_e) (-8) 8 (SOff 1 0) (bv_unsigned (getr regs_e 1))) ];
        try (rewrite rq_soff0; first [rewrite E24 | rewrite E23 | rewrite E22 | rewrite E21 | rewrite E20
                                     | rewrite E19 | rewrite E18 | rewrite E9 | rewrite E8 | rewrite E1];
             symmetry; apply Z_to_bv_bv_unsigned);
        try (change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply bv_unsigned_in_range);
        try (cbn; lia);
        first [exact S8 | exact S7 | exact S6 | exact S5 | exact S4 | exact S3 | exact S2 | exact S1 | exact S0
              | exact SRA].
    * cbn [base_val]. fold E. rewrite U34. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (RQ_SL + 8 * i) 0 8 (SOff 38 0) L);
        [rewrite rq_soff0, X38; reflexivity | zrng | zrng |].
      rewrite Z.add_0_r. cbn [ms_mem restrict mkst]. exact VL1.
    * cbn [base_val]. fold E. rewrite U35. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (mp + MD_REQ_LEN + 8 * i) 0 8 (SOff 38 0) L);
        [rewrite rq_soff0, X38; reflexivity | zrng | zrng |].
      rewrite Z.add_0_r. cbn [ms_mem restrict mkst]. exact VL2.
  + apply pairwise_disjoint_of_extents.
    unfold rq_frame, rq_slr, rq_rlr, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. fold E.
    cbn [base_val]. rewrite Usp, U34, U35.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [rq_lfacts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    fold E. rewrite Usp, X32, X33, X34, X35, X36, X37, X38.
    rewrite !unsigned_lit_small by lia.
    rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
- unfold rq_LSH. repeat apply Forall_cons; try apply Forall_nil;
    unfold shent_ok, app_apart; cbn [she_m she_lo she_hi];
    rewrite (U_atom E 32 SB X32) by lia; rewrite ?Z.add_0_r, ?Z.sub_0_r, ?Z.min_l, ?Z.max_r by lia.
  + rewrite (U_atom E 34 (RQ_SL + 8 * i) X34) by lia. split; [rewrite <- (aview_rd_of SEGS); exact RA1|].
    intros a Ha. lia.
  + rewrite (U_atom E 35 (mp + MD_REQ_LEN + 8 * i) X35) by lia. split; [rewrite <- (aview_rd_of SEGS); exact RA2|].
    intros a Ha. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr. lia.
Qed.
End w.
