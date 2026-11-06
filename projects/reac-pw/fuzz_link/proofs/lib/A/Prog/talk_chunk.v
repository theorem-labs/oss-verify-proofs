(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v, with its module paths and module names changed; 848 of its 933 lines of code are new or changed and 2604 lines of the source are left out. *)
(* talk on image A: the chunk loop of its walk, the pieces TK_CL0, TK_CHUNK and TK_NXT of
   lib/A/Prog/talk_defs.v (listing (internal path) (internal record, sha256 5526460cb5be)).
   - tk_cl0_ok (+0x16c): the set-up reads next and n_chunks; next >= n_chunks leaves at +0xb4 with a1 = -end_errno,
     else the loop head +0x1ac is reached with a2 = next.
   - tk_chunk_ok (+0x1ac, a2 = c): the store of c + 1 at m + 8 and the load of chunk_len[c]; a chunk shorter than a
     message header goes to +0x1e0, else the message loop +0x204 takes over at (b, 0, chunk_len[c]).
   - tk_nxt_ok (+0x1e0): next < n_chunks goes back to the loop head, else to +0xb4 with a1 = -end_errno.
   The three are proved together by induction on the chunks left, Z.to_nat (n_chunks - c).
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk talk_c talk_defs talk_kit talk_spec talk_ret.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Ltac ck_zrng := try change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); try change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32);
  try change (Z.of_N 8) with 8; try change (Z.of_N 4) with 4; lia.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation cfg_of regs pc mem md := (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom SEGS)) md).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis LV : LinkVals.
Variable c : tkc.
Hypothesis HC : tk_call SK B c.
#[local] Notation W := (tc_W c).
#[local] Notation memc := (tc_memc c).
#[local] Notation regs0 := (tc_regs0 c).
#[local] Notation mbs := (tc_mbs c).
#[local] Notation kbs := (tc_kbs c).
#[local] Notation req := (tc_req c).
Ltac ck_HC := pose proof HC as (HA & HMD & HMW & HNK & HNW & HRQ & HRL & HLEN & HBK & HBA & HRAm & HHm & HAMm &
  HRAq & HHq & HAMr & HRAr & HHr & HAPrm & HKD & HAD & HKA & HGm & HFm & HFr & HFk & HFa).

(* ---- words, denotations and branches ---------------------------------------------------------------------- *)
Lemma ck_uw : forall v, 0 <= v < 2 ^ 64 -> bv_unsigned (w64 v) = v.
Proof. intros v Hv. unfold w64. apply unsigned_lit_small. exact Hv. Qed.

Lemma ck_den0 : forall E n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = w64 v.
Proof. intros E n v H Hv. cbn [sv_denot]. rewrite H, ck_uw by exact Hv. rewrite Z.add_0_r. reflexivity. Qed.

Lemma ck_denoff : forall E n v k, ew E n = w64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n k) = w64 (v + k).
Proof. intros E n v k H Hv. cbn [sv_denot]. rewrite H, ck_uw by exact Hv. reflexivity. Qed.

Lemma ck_U0 : forall E n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> U E (SOff n 0) = v.
Proof. intros E n v H Hv. rewrite U_SOff, H, ck_uw by exact Hv. rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia. Qed.

Lemma ck_Uoff : forall E n v k, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + k < 2 ^ 64 ->
  U E (SOff n k) = v + k.
Proof. intros E n v k H Hv Hk. rewrite U_SOff, H, ck_uw by exact Hv. apply zcanon_id. unfold M64. lia. Qed.

(* `negw` of a 32-bit errno, as the runner leaves it *)
Lemma ck_sub0 : forall E v x, U E v = x -> 0 <= x < 2 ^ 64 ->
  sv_denot E (SAlu ALU_SUB (SLit 0) v) = w64 (- x).
Proof.
  intros E v x Hv Hx. rewrite denot_lit_U, U_SAlu. cbn [zalu_raw]. rewrite Hv, (U_SLit E 0).
  unfold zcanon, M64, w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Zmod_mod, Zmod_0_l. f_equal; lia.
Qed.

Lemma ck_ge : forall E a b x y, sv_denot E a = w64 x -> sv_denot E b = w64 y ->
  0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 -> branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (x <? y).
Proof.
  intros E a b x y Ha Hb Hx Hy. rewrite Ha, Hb. cbn [branch_taken]. rewrite bv_lts_signed.
  rewrite !signed_of_small by (rewrite ck_uw by lia; unfold half64; lia).
  rewrite !ck_uw by lia. reflexivity.
Qed.

Lemma ck_lt : forall E a b x y, sv_denot E a = w64 x -> sv_denot E b = w64 y ->
  0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 -> branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (x <? y).
Proof.
  intros E a b x y Ha Hb Hx Hy. rewrite Ha, Hb. cbn [branch_taken]. rewrite bv_lts_signed.
  rewrite !signed_of_small by (rewrite ck_uw by lia; unfold half64; lia).
  rewrite !ck_uw by lia. reflexivity.
Qed.

(* the address of chunk_len[x] (+0x1c0..+0x1c4) *)
Lemma ck_den_cl : forall E x, ew E 12 = w64 x -> bv_unsigned (ew E 243%nat) = LA_G_NL -> 0 <= x <= 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SOff 12 0) (SLit 3)) (SLit 262144)) (SOff 243 0)) =
  w64 (LA_G_NL + NK_CHUNK_LEN + 8 * x).
Proof.
  intros E x H12 Hg Hx. rewrite denot_lit_U. unfold w64. f_equal.
  rewrite !U_SAlu. cbn [zalu_raw]. rewrite (ck_U0 E 12 x H12) by lia. rewrite !U_lit by lia.
  rewrite U_SOff, Hg, Z.add_0_r. change (Z.land 3 63) with 3. rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 3) with 8. unfold zcanon, M64, LA_G_NL, NK_CHUNK_LEN. rewrite !(Z.mod_small _ (2 ^ 64)); lia.
Qed.

(* the base of chunk x (+0x1fc..+0x200) *)
Lemma ck_den_b : forall E x, ew E 12 = w64 x -> bv_unsigned (ew E 243%nat) = LA_G_NL -> 0 <= x <= 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SLL (SOff 12 0) (SLit 12)) (SOff 243 0)) =
  w64 (LA_G_NL + NL_CHUNK_MAX * x).
Proof.
  intros E x H12 Hg Hx. rewrite denot_lit_U. unfold w64. f_equal.
  rewrite !U_SAlu. cbn [zalu_raw]. rewrite (ck_U0 E 12 x H12) by lia. rewrite !U_lit by lia.
  rewrite U_SOff, Hg, Z.add_0_r. change (Z.land 12 63) with 12. rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 12) with 4096. unfold zcanon, M64, LA_G_NL, NL_CHUNK_MAX. rewrite !(Z.mod_small _ (2 ^ 64)); lia.
Qed.

(* ---- what the call gives ------------------------------------------------------------------------------------ *)
Lemma ck_wf : nlk_wf kbs /\ model_wf mbs /\ Z.of_nat (length mbs) = MD_SIZE /\
  Z.of_nat (length kbs) = NK_SIZE /\ Z.of_nat (length req) <= NL_SENT_LEN.
Proof.
  ck_HC. destruct HMD as (_ & HL). destruct HNK as (_ & KL).
  split; [exact HNW|]. split; [exact HMW|]. split; [exact HL|]. split; [exact KL|]. lia.
Qed.

Lemma ck_nch : 0 <= tk_nch c <= 64 /\ 0 <= nk_end_errno kbs < 2 ^ 31 /\
  (forall i, 0 <= i < tk_nch c -> 0 <= fld_u64 kbs (NK_CHUNK_LEN + 8 * i) <= NL_CHUNK_MAX).
Proof.
  pose proof ck_wf as (HNW & _).
  destruct HNW as (W1 & _ & _ & _ & _ & _ & _ & _ & W9 & _ & _ & W12 & _).
  unfold tk_nch, NL_CHUNKS in *. split; [lia|]. split; [lia | exact W12].
Qed.

Lemma ck_HJ0 : ajournal_gx SEGS B (tc_G c) (tc_XO c) (tc_OUT c) (tc_STK c) (tc_sp0 c) (tc_FP c) (tc_ly c) (tc_S c)
  (tc_W0 c) (tc_mem0 c) (tc_md0 c) (tc_own c) (tc_lyc c) (tc_Sc c) W memc (tc_mdc c) (tc_k c).
Proof. exact (proj1 (proj1 HC)). Qed.

Lemma ck_HGX : gx_ok SEGS B (tc_G c).
Proof. exact (proj1 (proj2 (proj1 HC))). Qed.

(* every byte of the model block is a byte the caller lets talk write *)
Lemma ck_ajw_m : forall a, tk_m c <= a < tk_m c + MD_SIZE ->
  ajw B (tc_G c) (tc_XO c) (tc_OUT c) (tc_STK c) (tc_sp0 c) (tc_FP c) (tc_ly c) (tc_S c) (tc_lyc c) (tc_Sc c)
    (tc_own c) a.
Proof.
  intros a Ha. ck_HC.
  destruct HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hajw & _).
  apply Hajw. exists (aarg regs0 0, aarg regs0 0 + MD_SIZE).
  split; [unfold talk_awr; cbn [In]; left; reflexivity|]. cbn [fst snd]. unfold tk_m in Ha. lia.
Qed.

(* a 4-byte field of g_nl at the current memory *)
Lemma ck_gfield : forall regs mem md off, tk_inv SK B c regs mem md ->
  0 <= off -> off + 4 <= NK_SIZE -> val_mem SEGS (rdW W mem) (LA_G_NL + off) 4 (fld_u32 kbs off).
Proof.
  intros regs mem md off HI Ho Hn. pose proof ck_wf as (_ & _ & _ & KL & _).
  pose proof (tk_gnl_val SK B c HC regs mem md off 4%nat HI Ho ltac:(unfold NK_SIZE in *; lia)) as HV.
  change (Z.of_nat 4) with 4 in HV. exact HV.
Qed.

(* an 8-byte field of g_nl at the current memory *)
Lemma ck_gfield8 : forall regs mem md off, tk_inv SK B c regs mem md ->
  0 <= off -> off + 8 <= NK_SIZE -> val_mem SEGS (rdW W mem) (LA_G_NL + off) 8 (fld_u64 kbs off).
Proof.
  intros regs mem md off HI Ho Hn. pose proof ck_wf as (_ & _ & _ & KL & _).
  pose proof (tk_gnl_val SK B c HC regs mem md off 8%nat HI Ho ltac:(unfold NK_SIZE in *; lia)) as HV.
  change (Z.of_nat 8) with 8 in HV. exact HV.
Qed.

(* a field of the model block at the current memory *)
Lemma ck_mfield : forall mem mb off (n : nat), amodel_at SEGS (rdW W mem) (tk_m c) mb ->
  0 <= off -> off + Z.of_nat n <= MD_SIZE -> val_mem SEGS (rdW W mem) (tk_m c + off) n (rdn mb off (Z.of_nat n)).
Proof.
  intros mem mb off n ((Hab & _) & HL) Ho Hn.
  apply (val_mem_of_abytes SEGS (rdW W mem) (tk_m c) mb off n Hab Ho). lia.
Qed.

Lemma ck_mnext : forall mem mb, amodel_at SEGS (rdW W mem) (tk_m c) mb ->
  val_mem SEGS (rdW W mem) (tk_m c + MD_NEXT) 4 (md_next mb).
Proof.
  intros mem mb HM.
  pose proof (ck_mfield mem mb MD_NEXT 4%nat HM ltac:(unfold MD_NEXT; lia)
    ltac:(unfold MD_NEXT, MD_SIZE; cbn; lia)) as HV.
  change (Z.of_nat 4) with 4 in HV. exact HV.
Qed.

(* every byte of the model block is writable at the current memory *)
Lemma ck_mwr : forall mem mb, amodel_at SEGS (rdW W mem) (tk_m c) mb ->
  forall i, 0 <= i < MD_SIZE -> writable_at SEGS (rdW W mem) (tk_m c + i).
Proof. intros mem mb ((_ & Hwr) & HL) i Hi. apply Hwr. lia. Qed.

(* ---- the buffers across a write that stays inside the model block ------------------------------------------- *)
Lemma ck_bufs_keep : forall mem mem' acc,
  tk_bufs c mem acc ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (tk_m c <= a < tk_m c + MD_SIZE) ->
     ~ (tk_sp c - TALK_AK <= a < tk_sp c) ->
     aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem' a) ->
  tk_bufs c mem' acc.
Proof.
  intros mem mem' acc (B1 & B2 & B3 & B4 & B5 & B6) UN PR.
  assert (Kk : forall i, tk_kd c <> 0 -> 1 <= tk_kn c -> 0 <= i < tk_kn c ->
    aview SEGS (w_H W) mem' (tk_kd c + i) = aview SEGS (w_H W) mem (tk_kd c + i)).
  { intros i H0 H1 Hi. destruct (tk_kd_facts SK B c HC H0 H1) as (K0 & K1 & K2 & K3 & K4 & K5 & _).
    pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
    apply UN; [lia | unfold apart in K4; lia | unfold apart_frame in K5; unfold tk_sp; lia]. }
  assert (Ka : forall i, tk_ad c <> 0 -> 1 <= tk_an c -> 0 <= i < tk_an c ->
    aview SEGS (w_H W) mem' (tk_ad c + i) = aview SEGS (w_H W) mem (tk_ad c + i)).
  { intros i H0 H1 Hi. destruct (tk_ad_facts SK B c HC H0 H1) as (K0 & K1 & K2 & K3 & K4 & K5 & _).
    pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
    apply UN; [lia | unfold apart in K4; lia | unfold apart_frame in K5; unfold tk_sp; lia]. }
  split; [|split; [|split; [|split; [|split]]]].
  - intros H0 H1.
    destruct (tk_kd_facts SK B c HC H0 H1) as (_ & _ & _ & _ & _ & _ & _ & _ & (junk & Hjl & (_ & Hwr))).
    apply (abuf_after SEGS (rdW W mem) (rdW W mem') (tk_kd c) (tk_kn c) (B1 H0 H1)).
    + intros i Hi. left. apply (mbyte_of_aview SEGS (w_H W) (w_H W) mem mem'). exact (Kk i H0 H1 Hi).
    + intros i Hi. apply (writable_kept (w_H W) memc mem' (tk_kd c + i) (PR (tk_kd c + i))).
      apply Hwr. lia.
  - intros H0 H1.
    destruct (tk_ad_facts SK B c HC H0 H1) as (_ & _ & _ & _ & _ & _ & _ & _ & (junk & Hjl & (_ & Hwr))).
    apply (abuf_after SEGS (rdW W mem) (rdW W mem') (tk_ad c) (tk_an c) (B2 H0 H1)).
    + intros i Hi. left. apply (mbyte_of_aview SEGS (w_H W) (w_H W) mem mem'). exact (Ka i H0 H1 Hi).
    + intros i Hi. apply (writable_kept (w_H W) memc mem' (tk_ad c + i) (PR (tk_ad c + i))).
      apply Hwr. lia.
  - intros pay Hp H0 H1. destruct (B3 pay Hp H0 H1) as (Hab & Hni). split; [|exact Hni].
    apply (abytes_kept SEGS (rdW W mem) (rdW W mem') (tk_kd c) _ Hab).
    intros i Hi. apply (mbyte_of_aview SEGS (w_H W) (w_H W) mem mem'). apply (Kk i H0 H1).
    rewrite length_app in Hi. cbn [length] in Hi.
    pose proof (tt_cut_len pay (tk_kn c) H1) as HL. lia.
  - intros pay Hp H0 H1. destruct (B4 pay Hp H0 H1) as (Hab & Hni). split; [|exact Hni].
    apply (abytes_kept SEGS (rdW W mem) (rdW W mem') (tk_ad c) _ Hab).
    intros i Hi. apply (mbyte_of_aview SEGS (w_H W) (w_H W) mem mem'). apply (Ka i H0 H1).
    rewrite length_app in Hi. cbn [length] in Hi.
    pose proof (tt_cut_len pay (tk_an c) H1) as HL. lia.
  - intros Hn H0 H1 i Hi. rewrite (Kk i H0 H1 Hi). exact (B5 Hn H0 H1 i Hi).
  - intros Hn H0 H1 i Hi. rewrite (Ka i H0 H1 Hi). exact (B6 Hn H0 H1 i Hi).
Qed.

(* ---- the fresh states of the three pieces -------------------------------------------------------------------- *)
(* the piece's own values: the field the state reads, g_nl's n_chunks and end_errno *)
Definition ck_xs (x : Z) : list word := [w64 x; w64 (tk_nch c); w64 (nk_end_errno kbs)].

Lemma ck_xs_atoms : forall regs x,
  ew (tk_E c regs (ck_xs x)) 49 = w64 x /\
  ew (tk_E c regs (ck_xs x)) 50 = w64 (tk_nch c) /\
  ew (tk_E c regs (ck_xs x)) 51 = w64 (nk_end_errno kbs).
Proof.
  intros regs x. split; [|split].
  - exact (tk_E_xs c regs (ck_xs x) 0%nat ltac:(lia)).
  - exact (tk_E_xs c regs (ck_xs x) 1%nat ltac:(lia)).
  - exact (tk_E_xs c regs (ck_xs x) 2%nat ltac:(lia)).
Qed.

Lemma ck_Rg_ok : forall regs mem md x, tk_inv SK B c regs mem md ->
  region_ok SEGS (tk_E c regs (ck_xs x)) (rdW W mem) tk_Rg.
Proof.
  intros regs mem md x HI.
  destruct (ck_xs_atoms regs x) as (_ & E50 & E51).
  pose proof ck_nch as (Hn & He & _).
  pose proof (tk_E_gnl LV c regs (ck_xs x)) as Hg.
  unfold tk_Rg, tk_ch, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Hg. split; [unfold LA_G_NL; lia|]. split; [unfold LA_G_NL; lia|].
  split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (chunk_ok_val SEGS _ _ LA_G_NL 262656 4 (SOff 50 0) (tk_nch c));
      [ apply ck_den0; [exact E50 | lia] | ck_zrng | ck_zrng |].
    exact (ck_gfield regs mem md NK_N_CHUNKS HI ltac:(unfold NK_N_CHUNKS; lia)
      ltac:(unfold NK_N_CHUNKS, NK_SIZE; lia)).
  - apply (chunk_ok_val SEGS _ _ LA_G_NL 262664 4 (SOff 51 0) (nk_end_errno kbs));
      [ apply ck_den0; [exact E51 | lia] | ck_zrng | ck_zrng |].
    exact (ck_gfield regs mem md NK_END_ERRNO HI ltac:(unfold NK_END_ERRNO; lia)
      ltac:(unfold NK_END_ERRNO, NK_SIZE; lia)).
Qed.

Lemma ck_gfacts_ok : forall regs x, atoms_ok (tk_E c regs (ck_xs x)) tk_gfacts.
Proof.
  intros regs x. destruct (ck_xs_atoms regs x) as (_ & E50 & E51).
  pose proof ck_nch as (Hn & He & _).
  unfold tk_gfacts. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E50, E51, !ck_uw by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* the SH entry of the model block *)
Lemma ck_sh_m : forall regs mem md xs, tk_inv SK B c regs mem md ->
  getr regs 23 = w64 SHADOW_OFF -> getr regs 20 = w64 (tk_m c) ->
  sh_ok SEGS tk_Bx tk_SH_cl0 (tk_E c regs xs) (rdW W mem).
Proof.
  intros regs mem md xs HI H23 H20.
  destruct (tk_m_facts SK B c HC) as (Hm0 & Hm1 & Hm2 & _ & _ & Hra & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  unfold tk_SH_cl0. apply Forall_cons; [|apply Forall_nil].
  apply (tk_shent_ok (tk_E c regs xs) (rdW W mem) 20%nat 0 MD_SIZE (tk_m c)).
  - unfold tk_Bx. apply (tk_U_reg c regs xs 23 23%bv); [lia | reflexivity | exact H23 | unfold SHADOW_OFF; lia].
  - apply (tk_U_reg c regs xs 20 20%bv); [lia | reflexivity | exact H20 | unfold MD_SIZE in *; lia].
  - unfold MD_SIZE; lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg in *. destruct Hm2 as [Hq|Hq]; [left | right]; lia.
  - rewrite <- (aview_rd_of SEGS (w_H W) mem).
    apply (range_addressable_sub _ _ (tk_m c) MD_SIZE); [|lia|lia].
    apply (tk_ra_kept SK B c HC regs mem md (tk_m c) MD_SIZE HI Hm0 ltac:(lia) Hra).
Qed.

(* one SH entry over a window at atom n *)
Lemma ck_shent : forall regs mem md xs (n : nat) (r : bv 5) x hi, tk_inv SK B c regs mem md ->
  (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  getr regs 23 = w64 SHADOW_OFF -> getr regs r = w64 x ->
  0 <= x -> 0 <= hi -> x + hi <= kHighMemEnd - 1 ->
  (x + hi <= kLowMemEnd \/ kHighMemBeg <= x) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF x hi ->
  shent_ok SEGS tk_Bx (tk_E c regs xs) (rdW W mem) (mkSHE n 0 hi).
Proof.
  intros regs mem md xs n r x hi HI Hn Hr H23 Hx H0 Hh Hk Hz HR.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  apply (tk_shent_ok (tk_E c regs xs) (rdW W mem) n 0 hi x).
  - unfold tk_Bx. apply (tk_U_reg c regs xs 23 23%bv); [lia | reflexivity | exact H23 | unfold SHADOW_OFF; lia].
  - apply (tk_U_reg c regs xs n r); [exact Hn | exact Hr | exact Hx | lia].
  - lia.
  - lia.
  - rewrite <- (aview_rd_of SEGS (w_H W) mem).
    apply (range_addressable_sub _ _ x hi); [|lia|lia].
    apply (tk_ra_kept SK B c HC regs mem md x hi HI H0 ltac:(lia) HR).
Qed.

(* g_nl's image atom as a word *)
Lemma ck_Eg : forall regs xs, ew (tk_E c regs xs) 243%nat = w64 LA_G_NL.
Proof.
  intros regs xs. pose proof (tk_E_gnl LV c regs xs) as Hg. change (A_OBJ 2) with 243%nat in Hg.
  rewrite <- Hg. unfold w64. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* a byte of the model block is a byte of the write set *)
Lemma ck_ewr_m : forall a, tk_m c <= a < tk_m c + MD_SIZE -> tk_ewr c a.
Proof.
  intros a Ha. unfold tk_ewr, inFP. exists (aarg regs0 0, aarg regs0 0 + MD_SIZE).
  split; [unfold talk_awr; cbn [In]; left; reflexivity|]. cbn [fst snd]. unfold tk_m in Ha. lia.
Qed.

Ltac ck_in := repeat (first [left; reflexivity | right]).
Ltac ck_keep RK r K := pose proof (RK r ltac:(ck_in)) as K; cbn [ms_regs restrict] in K.
Ltac ck_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
  end.
Ltac ck_awr0 :=
  lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat (apply awr_ok_x_cons;
    [ intros ?a ?Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; exfalso; clear - Ha; lia | ]);
  apply awr_ok_x_nil.

(* ---- the invariant and the register facts across a run that writes nothing ----------------------------------- *)
Lemma ck_agree : forall regs xs, env_agree 32 (Ereg regs (tk_ext c ++ xs)) (tk_E c regs xs).
Proof.
  intros regs xs. split; [intros n Hn; unfold tk_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
Qed.

Lemma ck_inv_same : forall regs mem md regs' md',
  tk_inv SK B c regs mem md ->
  ajournal_gx SEGS B (tc_G c) (tc_XO c) (tc_OUT c) (tc_STK c) (tc_sp0 c) (tc_FP c) (tc_ly c) (tc_S c) (tc_W0 c)
    (tc_mem0 c) (tc_md0 c) (tc_own c) (tc_lyc c) (tc_Sc c) W mem md' (tc_k c) ->
  m_fds md' = m_fds md -> m_fs md' = m_fs md ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  tk_inv SK B c regs' mem md'.
Proof.
  intros regs mem md regs' md' HI HJ Hfd Hfs R2 R3 R4.
  apply (tk_inv_step SK B c HC regs mem md regs' mem md' (fun _ => False) HI HJ Hfd Hfs);
    [ intros a _ _; reflexivity | intros a [] | intros a Hp; exact Hp | exact R2 | exact R3 | exact R4 ].
Qed.

(* ---- the exit at +0xb4 with a1 = - end_errno ----------------------------------------------------------------- *)
Lemma ck_exit : forall j regs mem md,
  TK_RET SK B c ->
  tk_inv SK B c regs mem md -> getr regs 23 = w64 SHADOW_OFF ->
  getr regs 11 = w64 (- nk_end_errno kbs) ->
  (exists mb, amodel_at SEGS (rdW W mem) (tk_m c) mb /\ tk_mo c mb /\ md_next mb = j) ->
  tk_bufs c mem no_attrs -> tk_main c -> tk_clr c j -> tk_nch c <= j ->
  tk_goal SK B c (cfg_of regs (BASE + TP_RT) mem md).
Proof.
  intros j regs mem md HRET HI H23 H11 (mb & HM & HMO & HN) HB (HS1 & HS2) HCL Hj.
  pose proof ck_wf as (HNW & HMW & HML & HKL & HRQ).
  pose proof ck_nch as (Hn & He & _).
  pose proof (cls_end mbs kbs j HCL Hj) as HCE.
  destruct (mres_main mbs kbs req mb NlNone (Z.to_nat j) HS1 HS2 HCE HMO
    ltac:(rewrite HN; destruct HMO as (HW & _); lia)) as (HRES & HRC & HAT).
  cbn [tw_rc tw_at] in HRC, HAT.
  rewrite (tw_norm_neg (nk_end_errno kbs) ltac:(lia)) in HRC.
  apply (HRET regs mem md HI H23).
  intros regs2 H10.
  apply (tk_post_of SK B c HC mem (- nk_end_errno kbs) no_attrs mb HM HRES
    ltac:(symmetry; exact HRC) ltac:(symmetry; exact HAT) HB regs2).
  rewrite H10. exact H11.
Qed.

(* ---- the three pieces ---------------------------------------------------------------------------------------- *)
Definition ck_CH (ci : Z) : Prop := forall regs mem md,
  tk_inv SK B c regs mem md -> tk_rs0 c regs -> tk_rsn c regs -> tk_rch c regs -> getr regs 12 = w64 ci ->
  tk_cmem c mem ci -> tk_bufs c mem no_attrs -> tk_main c -> tk_clr c ci -> 0 <= ci < tk_nch c ->
  tk_goal SK B c (cfg_of regs (BASE + TP_CH) mem md).

(* +0x1e0: next < n_chunks goes back to the loop head, else the exit *)
Lemma ck_nx_step : TK_RET SK B c -> forall j, (j < tk_nch c -> ck_CH j) -> TK_NXT SK B c j.
Proof.
intros HRET j HCH regs mem md HI HR0 HRN HRCH HCM HB HMAIN HCL Hj.
pose proof ck_wf as (HNW & HMW & HML & HKL & HRQ).
pose proof ck_nch as (Hn & He & Hclen).
destruct (tk_m_facts SK B c HC) as (Hm0 & Hmhi & Hm2 & Hmg & Hmf & Hmra & Hmh & Hmbs).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof HI as (HJ & _).
pose proof HR0 as (R8 & R9 & R23).
pose proof HRCH as (P10 & P13 & P14 & P15 & P16 & P17 & P6).
pose proof HCM as (mb & HM & HMO & HN).
pose proof (ck_xs_atoms regs j) as (E49 & E50 & E51).
assert (E10 : ew (tk_E c regs (ck_xs j)) 10 = w64 (tk_m c + MD_NEXT))
  by (rewrite (tk_E_reg c regs (ck_xs j) 10 10%bv) by (lia || reflexivity); exact P10).
assert (U10 : bv_unsigned (ew (tk_E c regs (ck_xs j)) 10) = tk_m c + MD_NEXT)
  by (rewrite E10; apply ck_uw; unfold MD_NEXT, MD_SIZE in *; lia).
assert (Ug : bv_unsigned (ew (tk_E c regs (ck_xs j)) (A_OBJ 2)) = LA_G_NL)
  by exact (tk_E_gnl LV c regs (ck_xs j)).
pose proof (ck_Eg regs (ck_xs j)) as Eg.
pose proof (tk_E_env c regs (ck_xs j)) as HEI.
assert (HS : st_ok_pi SEGS VAL (tk_E c regs (ck_xs j)) tk_ss_nx
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + TP_NX)) mem (seg_rom SEGS)))).
{ unfold tk_ss_nx. apply (tk_st_ok SK B LV c HC regs mem md (ck_xs j) TP_NX).
  - exact HI.
  - exact R23.
  - exact (tk_ov_ch_ok SK B LV c HC regs (ck_xs j) HRCH R23).
  - vm_compute; reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [exact (ck_Rg_ok regs mem md j HI) | apply Forall_nil]].
    unfold tk_ch, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U10. split; [unfold MD_NEXT; lia|]. split; [unfold MD_NEXT, MD_SIZE in *; lia|].
    split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ (tk_m c + MD_NEXT) 0 4 (SOff 49 0) j);
      [ apply ck_den0; [exact E49 | lia] | ck_zrng | ck_zrng |].
    rewrite Z.add_0_r, <- HN. exact (ck_mnext mem mb HM).
  - apply pairwise_disjoint_of_extents. unfold tk_Rg, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U10, Ug.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold apart_gnl, LA_G_NL, NK_SIZE, MD_SIZE, MD_NEXT in *. repeat split; lia.
  - refine (conj _ (conj _ (ck_gfacts_ok regs j))); unfold afact_ok; cbn [af_lo af_hi af_al2].
    + rewrite U10, Z.pow_0_r, Z.mod_1_r. unfold MD_NEXT, MD_SIZE in *. lia.
    + rewrite E49, (ck_uw j) by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
assert (SHOK : sh_ok SEGS tk_Bx tk_SH_nx (tk_E c regs (ck_xs j)) (rdW W mem)).
{ unfold tk_SH_nx. apply Forall_cons; [|apply Forall_nil].
  apply (ck_shent regs mem md (ck_xs j) 10%nat 10%bv (tk_m c + MD_NEXT) 8 HI
    ltac:(lia) ltac:(reflexivity) R23 P10);
    [ unfold MD_NEXT; lia | lia | unfold MD_NEXT, MD_SIZE in *; lia
    | unfold amem_range, kLowMemEnd, kHighMemBeg, MD_NEXT, MD_SIZE in *;
      destruct Hm2 as [Hq|Hq]; [left|right]; lia
    | apply (range_addressable_sub _ _ (tk_m c) MD_SIZE); [exact Hmra | unfold MD_NEXT; lia
      | unfold MD_NEXT, MD_SIZE; lia] ]. }
pose proof (paj_run_x SK B LAWS (tc_G c) ck_HGX (tc_XO c) (tc_OUT c)) as RUN.
pose proof (paj_run_to_x SK B LAWS (tc_G c) ck_HGX (tc_XO c) (tc_OUT c)) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
paj_run_tok RUN HS HJ SHOK tk_span; [ck_awr0|].
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
assert (Em1 : ms_mem ms1 = mem) by (eapply frame_of_read_only; [|exact HF]; vm_compute; reflexivity).
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK tk_span;
  rewrite (ck_lt _ (SOff 49 0) (SOff 50 0) j (tk_nch c)) in Hc
    by (first [apply ck_den0; [assumption | lia] | lia]).
- (* j < n_chunks: back to the loop head *)
  apply Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_CH; [ck_awr0|].
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms2 end.
  assert (Em2 : ms_mem ms2 = mem)
    by (rewrite <- Em1; eapply frame_of_read_only; [|exact HF]; vm_compute; reflexivity).
  rewrite Em2 in HJ. pmkst HS. rewrite Em2.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs (tk_ext c ++ ck_xs j)
    [2%bv;3%bv;4%bv;8%bv;9%bv;10%bv;18%bv;19%bv;23%bv] HS (ck_agree regs (ck_xs j))
    ltac:(vm_compute; reflexivity)) as RK.
  ck_keep RK (2%bv : bv 5) K2. ck_keep RK (3%bv : bv 5) K3. ck_keep RK (4%bv : bv 5) K4.
  ck_keep RK (8%bv : bv 5) K8. ck_keep RK (9%bv : bv 5) K9. ck_keep RK (10%bv : bv 5) K10.
  ck_keep RK (18%bv : bv 5) K18. ck_keep RK (19%bv : bv 5) K19. ck_keep RK (23%bv : bv 5) K23.
  ck_reg HS (6%bv : bv 5) Q6. ck_reg HS (12%bv : bv 5) Q12. ck_reg HS (13%bv : bv 5) Q13.
  ck_reg HS (14%bv : bv 5) Q14. ck_reg HS (15%bv : bv 5) Q15. ck_reg HS (16%bv : bv 5) Q16.
  ck_reg HS (17%bv : bv 5) Q17.
  apply (HCH Hc).
  + apply (ck_inv_same regs mem md _ _ HI HJ);
      [ repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
      | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
      | exact K2 | exact K3 | exact K4 ].
  + split; [rewrite K8; exact R8|]. split; [rewrite K9; exact R9 | rewrite K23; exact R23].
  + pose proof HRN as (N18 & N19). split; [rewrite K18; exact N18 | rewrite K19; exact N19].
  + split; [rewrite K10; exact P10|]. split.
    { rewrite Q13. apply (tk_den_shx _ (SOff 10 0) (tk_m c + MD_NEXT));
        [ apply (ck_U0 _ 10 _ E10); unfold MD_NEXT, MD_SIZE in *; lia
        | unfold tk_Bx; apply (tk_U_reg c regs (ck_xs j) 23 23%bv);
          [lia | reflexivity | exact R23 | unfold SHADOW_OFF; lia]
        | unfold MD_NEXT, MD_SIZE in *; lia ]. }
    split; [rewrite Q14; reflexivity|]. split.
    { rewrite Q15. apply (ck_denoff _ 243%nat LA_G_NL 262144); [exact Eg | unfold LA_G_NL; lia]. }
    split.
    { rewrite Q16. apply (ck_den0 _ 243%nat LA_G_NL); [exact Eg | unfold LA_G_NL; lia]. }
    split; [rewrite Q17; reflexivity | rewrite Q6; reflexivity].
  + rewrite Q12. apply ck_den0; [exact E49 | lia].
  + exact HCM.
  + exact HB.
  + exact HMAIN.
  + exact HCL.
  + lia.
- (* n_chunks <= next: the exit *)
  apply Z.ltb_ge in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_RT; [ck_awr0|].
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms2 end.
  assert (Em2 : ms_mem ms2 = mem)
    by (rewrite <- Em1; eapply frame_of_read_only; [|exact HF]; vm_compute; reflexivity).
  rewrite Em2 in HJ. pmkst HS. rewrite Em2.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs (tk_ext c ++ ck_xs j)
    [2%bv;3%bv;4%bv;23%bv] HS (ck_agree regs (ck_xs j)) ltac:(vm_compute; reflexivity)) as RK.
  ck_keep RK (2%bv : bv 5) K2. ck_keep RK (3%bv : bv 5) K3. ck_keep RK (4%bv : bv 5) K4.
  ck_keep RK (23%bv : bv 5) K23.
  ck_reg HS (11%bv : bv 5) Q11.
  apply (ck_exit j _ mem _ HRET).
  + apply (ck_inv_same regs mem md _ _ HI HJ);
      [ repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
      | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
      | exact K2 | exact K3 | exact K4 ].
  + rewrite K23; exact R23.
  + rewrite Q11. apply (ck_sub0 _ (SOff 51 0) (nk_end_errno kbs));
      [ apply (ck_U0 _ 51 _ E51); lia | lia ].
  + exists mb. split; [exact HM|]. split; [exact HMO | exact HN].
  + exact HB.
  + exact HMAIN.
  + exact HCL.
  + lia.
Qed.

(* the chunk-stage registers after a run that keeps them *)
Lemma ck_rch_keep : forall regs xs regs',
  tk_rch c regs -> getr regs 23 = w64 SHADOW_OFF ->
  getr regs' 10 = getr regs 10 ->
  getr regs' 13 = sv_denot (tk_E c regs xs) (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 23 0)) ->
  getr regs' 14 = sv_denot (tk_E c regs xs) (SLit 262144) ->
  getr regs' 15 = sv_denot (tk_E c regs xs) (SOff 243 262144) ->
  getr regs' 16 = sv_denot (tk_E c regs xs) (SOff 243 0) ->
  getr regs' 17 = sv_denot (tk_E c regs xs) (SLit 16) ->
  getr regs' 6 = sv_denot (tk_E c regs xs) (SLit 2) ->
  tk_rch c regs'.
Proof.
  intros regs xs regs' HRCH R23 H10 H13 H14 H15 H16 H17 H6.
  pose proof HRCH as (P10 & P13 & P14 & P15 & P16 & P17 & P6).
  destruct (tk_m_facts SK B c HC) as (Hm0 & Hmhi & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (E10 : ew (tk_E c regs xs) 10 = w64 (tk_m c + MD_NEXT))
    by (rewrite (tk_E_reg c regs xs 10 10%bv) by (lia || reflexivity); exact P10).
  pose proof (ck_Eg regs xs) as Eg.
  split; [rewrite H10; exact P10|]. split.
  { rewrite H13. apply (tk_den_shx _ (SOff 10 0) (tk_m c + MD_NEXT));
      [ apply (ck_U0 _ 10 _ E10); unfold MD_NEXT, MD_SIZE in *; lia
      | unfold tk_Bx; apply (tk_U_reg c regs xs 23 23%bv);
        [lia | reflexivity | exact R23 | unfold SHADOW_OFF; lia]
      | unfold MD_NEXT, MD_SIZE in *; lia ]. }
  split; [rewrite H14; reflexivity|]. split.
  { rewrite H15. apply (ck_denoff _ 243%nat LA_G_NL 262144); [exact Eg | unfold LA_G_NL; lia]. }
  split.
  { rewrite H16. apply (ck_den0 _ 243%nat LA_G_NL); [exact Eg | unfold LA_G_NL; lia]. }
  split; [rewrite H17; reflexivity | rewrite H6; reflexivity].
Qed.

Ltac ck_awr_m U10 :=
  lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end;
  apply awr_ok_x_cons;
  [ intros ?a ?Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U10 in Ha;
    apply ck_ajw_m; unfold MD_NEXT, MD_SIZE in Ha |- *; lia
  | apply awr_ok_x_nil ].

(* +0x1ac: the cursor store, the load of chunk_len[c], then the message loop or the next chunk *)
Lemma ck_ch_step : TK_RET SK B c -> TK_MSG SK B c -> forall ci, TK_NXT SK B c (ci + 1) -> ck_CH ci.
Proof.
intros HRET HMSG ci HNXT regs mem md HI HR0 HRN HRCH R12 HCM HB HMAIN HCL Hci.
pose proof ck_wf as (HNW & HMW & HML & HKL & HRQ).
pose proof ck_nch as (Hn & He & Hclen).
pose proof (Hclen ci Hci) as HLc. unfold NL_CHUNK_MAX in HLc.
destruct (tk_m_facts SK B c HC) as (Hm0 & Hmhi & Hm2 & Hmg & Hmf & Hmra & Hmh & Hmbs).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof HI as (HJ & _).
pose proof HR0 as (R8 & R9 & R23).
pose proof HRN as (N18 & N19).
pose proof HRCH as (P10 & P13 & P14 & P15 & P16 & P17 & P6).
pose proof HCM as (mb & HM & HMO & HN).
pose proof HM as (_ & HMBL).
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRAq & _).
change (ard SEGS (rdW W memc)) with (aview SEGS (w_H W) memc) in HRAq.
assert (E10 : ew (tk_E c regs []) 10 = w64 (tk_m c + MD_NEXT))
  by (rewrite (tk_E_reg c regs [] 10 10%bv) by (lia || reflexivity); exact P10).
assert (U10 : bv_unsigned (ew (tk_E c regs []) 10) = tk_m c + MD_NEXT)
  by (rewrite E10; apply ck_uw; unfold MD_NEXT, MD_SIZE in *; lia).
assert (E12 : ew (tk_E c regs []) 12 = w64 ci)
  by (rewrite (tk_E_reg c regs [] 12 12%bv) by (lia || reflexivity); exact R12).
pose proof (tk_E_env c regs []) as HEI.
assert (HS : st_ok_pi SEGS VAL (tk_E c regs []) tk_ss_ch
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + TP_CH)) mem (seg_rom SEGS)))).
{ unfold tk_ss_ch. apply (tk_st_ok SK B LV c HC regs mem md [] TP_CH).
  - exact HI.
  - exact R23.
  - exact (tk_ov_ch_ok SK B LV c HC regs [] HRCH R23).
  - vm_compute; reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold tk_ch, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U10. split; [unfold MD_NEXT; lia|]. split; [unfold MD_NEXT, MD_SIZE in *; lia|].
    split.
    { intros o Ho. replace (tk_m c + MD_NEXT + o) with (tk_m c + (MD_NEXT + o)) by lia.
      apply (ck_mwr mem mb HM). unfold MD_NEXT, MD_SIZE. lia. }
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ (tk_m c + MD_NEXT) 0 4 (SOff 12 0) ci);
      [ apply ck_den0; [exact E12 | lia] | ck_zrng | ck_zrng |].
    rewrite Z.add_0_r, <- HN. exact (ck_mnext mem mb HM).
  - cbn [pairwise_disjoint all_disjoint]. repeat first [exact I | split].
  - refine (conj _ (conj _ I)); unfold afact_ok; cbn [af_lo af_hi af_al2].
    + rewrite U10, Z.pow_0_r, Z.mod_1_r. unfold MD_NEXT, MD_SIZE in *. lia.
    + rewrite E12, (ck_uw ci) by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
assert (SHOK : sh_ok SEGS tk_Bx tk_SH_ch (tk_E c regs []) (rdW W mem)).
{ unfold tk_SH_ch. apply Forall_cons; [|apply Forall_nil].
  apply (ck_shent regs mem md [] 10%nat 10%bv (tk_m c + MD_NEXT) 8 HI
    ltac:(lia) ltac:(reflexivity) R23 P10);
    [ unfold MD_NEXT; lia | lia | unfold MD_NEXT, MD_SIZE in *; lia
    | unfold amem_range, kLowMemEnd, kHighMemBeg, MD_NEXT, MD_SIZE in *;
      destruct Hm2 as [Hq|Hq]; [left|right]; lia
    | apply (range_addressable_sub _ _ (tk_m c) MD_SIZE); [exact Hmra | unfold MD_NEXT; lia
      | unfold MD_NEXT, MD_SIZE; lia] ]. }
pose proof (paj_run_x SK B LAWS (tc_G c) ck_HGX (tc_XO c) (tc_OUT c)) as RUN.
pose proof (paj_run_to_x SK B LAWS (tc_G c) ck_HGX (tc_XO c) (tc_OUT c)) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
(* +0x1ac .. +0x1c4: the store of c + 1 and the address of chunk_len[c] *)
paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_CL; [ck_awr_m U10|].
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _
  (fun a => tk_m c + MD_NEXT <= a < tk_m c + MD_NEXT + 4) HFr
  ltac:(intros bb wlo whi aa Hin Hrr; vm_compute in Hin;
        destruct Hin as [Hq | []]; injection Hq as <- <- <-;
        cbn [base_val] in Hrr; rewrite U10 in Hrr; cbv beta; clear - Hrr; lia)) as UNk.
pose proof (st_ok_region_nth (segs := SEGS) _ _ _ 0 _ HS eq_refl) as HRnx.
assert (Vnew : val_mem SEGS (rdW W (ms_mem ms1)) (tk_m c + MD_NEXT + 0) 4 (ci + 1)).
{ eapply (field_of_region (segs := SEGS) _ _ _ _ _ _ _ _ _ _ 4%N);
    [ exact HRnx | exact U10 | ck_in | apply ck_denoff; [exact E12 | lia] | ck_zrng | ck_zrng ]. }
assert (Vnew0 : val_mem SEGS (rdW W (ms_mem ms1)) (tk_m c + MD_NEXT) 4 (ci + 1))
  by (replace (tk_m c + MD_NEXT) with (tk_m c + MD_NEXT + 0) by lia; exact Vnew).
assert (HMnew : amodel_at SEGS (rdW W (ms_mem ms1)) (tk_m c) (md_set_next mb (ci + 1))).
{ unfold md_set_next.
  apply (amodel_store SEGS (rdW W mem) (rdW W (ms_mem ms1)) (tk_m c) mb MD_NEXT 4%nat (ci + 1) HM);
    [ unfold MD_NEXT; lia | unfold MD_NEXT, MD_SIZE; cbn; lia | | exact Vnew0 | ].
  - intros i Hi Hni. apply (mbyte_of_aview SEGS (w_H W) (w_H W) mem (ms_mem ms1)).
    apply UNk; [unfold MD_SIZE in *; lia | cbv beta; unfold MD_NEXT in *; lia].
  - intros i Hi. apply (writable_kept (w_H W) mem (ms_mem ms1) (tk_m c + i)
      (fun Hp => apresent_grows _ _ _ _ HG Hp)). exact (ck_mwr mem mb HM i Hi). }
destruct (mo_set_next mbs req mb (ci + 1) HMBL ltac:(lia) HMO) as (HL2 & HN2 & HMO2).
assert (HB1 : tk_bufs c (ms_mem ms1) no_attrs).
{ apply (ck_bufs_keep mem (ms_mem ms1) no_attrs HB).
  - intros a Ha Hout Hwin. apply UNk; [exact Ha | cbv beta; unfold MD_NEXT, MD_SIZE in *; lia].
  - intros a Hp. pose proof HI as (_ & _ & _ & _ & _ & _ & _ & _ & PRm).
    exact (apresent_grows _ _ _ _ HG (PRm a Hp)). }
pose proof (regs_kept_of_st_ok_pi _ _ _ regs (tk_ext c ++ [])
  [2%bv;3%bv;4%bv;8%bv;9%bv;10%bv;12%bv;18%bv;19%bv;20%bv;23%bv] HS (ck_agree regs [])
  ltac:(vm_compute; reflexivity)) as RK.
ck_keep RK (2%bv : bv 5) K2. ck_keep RK (3%bv : bv 5) K3. ck_keep RK (4%bv : bv 5) K4.
ck_keep RK (8%bv : bv 5) K8. ck_keep RK (9%bv : bv 5) K9. ck_keep RK (10%bv : bv 5) K10.
ck_keep RK (12%bv : bv 5) K12. ck_keep RK (18%bv : bv 5) K18. ck_keep RK (19%bv : bv 5) K19.
ck_keep RK (20%bv : bv 5) K20. ck_keep RK (23%bv : bv 5) K23.
ck_reg HS (6%bv : bv 5) Q6. ck_reg HS (11%bv : bv 5) Q11. ck_reg HS (13%bv : bv 5) Q13.
ck_reg HS (14%bv : bv 5) Q14. ck_reg HS (15%bv : bv 5) Q15. ck_reg HS (16%bv : bv 5) Q16.
ck_reg HS (17%bv : bv 5) Q17.
pmkst HS.
assert (HRCH1 : tk_rch c (ms_regs ms1))
  by (apply (ck_rch_keep regs [] (ms_regs ms1) HRCH R23 K10 Q13 Q14 Q15 Q16 Q17 Q6)).
assert (R231 : getr (ms_regs ms1) 23 = w64 SHADOW_OFF) by (rewrite K23; exact R23).
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (MD1 := mdq) end.
assert (Hfd1 : m_fds MD1 = m_fds md) by (unfold MD1; repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity).
assert (Hfs1 : m_fs MD1 = m_fs md) by (unfold MD1; repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity).
assert (HI1 : tk_inv SK B c (ms_regs ms1) (ms_mem ms1) MD1).
{ apply (tk_inv_step SK B c HC regs mem md (ms_regs ms1) (ms_mem ms1) MD1
    (fun a => tk_m c + MD_NEXT <= a < tk_m c + MD_NEXT + 4) HI HJ Hfd1 Hfs1 UNk).
  - intros a Ha. right. apply ck_ewr_m. cbv beta in Ha. unfold MD_NEXT, MD_SIZE in *. lia.
  - intros a Hp. exact (apresent_grows _ _ _ _ HG Hp).
  - exact K2.
  - exact K3.
  - exact K4. }
clear HF HFr HG UNk HRnx.
(* the fresh state at +0x1c8 *)
assert (E10' : ew (tk_E c (ms_regs ms1) (ck_xs (fld_u64 kbs (NK_CHUNK_LEN + 8 * ci)))) 10
                 = w64 (tk_m c + MD_NEXT))
  by (rewrite (tk_E_reg c (ms_regs ms1) _ 10 10%bv) by (lia || reflexivity);
      rewrite K10; exact P10).
assert (U10' : bv_unsigned (ew (tk_E c (ms_regs ms1) (ck_xs (fld_u64 kbs (NK_CHUNK_LEN + 8 * ci)))) 10)
                 = tk_m c + MD_NEXT)
  by (rewrite E10'; apply ck_uw; unfold MD_NEXT, MD_SIZE in *; lia).
assert (E12' : ew (tk_E c (ms_regs ms1) (ck_xs (fld_u64 kbs (NK_CHUNK_LEN + 8 * ci)))) 12 = w64 ci)
  by (rewrite (tk_E_reg c (ms_regs ms1) _ 12 12%bv) by (lia || reflexivity); rewrite K12; exact R12).
assert (R11 : getr (ms_regs ms1) 11 = w64 (LA_G_NL + NK_CHUNK_LEN + 8 * ci)).
{ rewrite Q11. apply (ck_den_cl _ ci); [exact E12 | exact (tk_E_gnl LV c regs []) | lia]. }
assert (E11' : ew (tk_E c (ms_regs ms1) (ck_xs (fld_u64 kbs (NK_CHUNK_LEN + 8 * ci)))) 11
                 = w64 (LA_G_NL + NK_CHUNK_LEN + 8 * ci))
  by (rewrite (tk_E_reg c (ms_regs ms1) _ 11 11%bv) by (lia || reflexivity); exact R11).
assert (U11' : bv_unsigned (ew (tk_E c (ms_regs ms1) (ck_xs (fld_u64 kbs (NK_CHUNK_LEN + 8 * ci)))) 11)
                 = LA_G_NL + NK_CHUNK_LEN + 8 * ci)
  by (rewrite E11'; apply ck_uw; unfold LA_G_NL, NK_CHUNK_LEN; lia).
assert (Ug' : bv_unsigned (ew (tk_E c (ms_regs ms1) (ck_xs (fld_u64 kbs (NK_CHUNK_LEN + 8 * ci))))
                 (A_OBJ 2)) = LA_G_NL)
  by exact (tk_E_gnl LV c (ms_regs ms1) _).
pose proof (ck_Eg (ms_regs ms1) (ck_xs (fld_u64 kbs (NK_CHUNK_LEN + 8 * ci)))) as Eg'.
pose proof (ck_xs_atoms (ms_regs ms1) (fld_u64 kbs (NK_CHUNK_LEN + 8 * ci))) as (F49 & F50 & F51).
clear HEI. pose proof (tk_E_env c (ms_regs ms1) (ck_xs (fld_u64 kbs (NK_CHUNK_LEN + 8 * ci)))) as HEI.
clear HS SHOK.
assert (HS : st_ok_pi SEGS VAL (tk_E c (ms_regs ms1) (ck_xs (fld_u64 kbs (NK_CHUNK_LEN + 8 * ci)))) tk_ss_cl
    (restrict (w_H W) (mkst (ms_regs ms1) (Z_to_bv 64 (BASE + TP_CL)) (ms_mem ms1) (seg_rom SEGS)))).
{ unfold tk_ss_cl.
  apply (tk_st_ok SK B LV c HC (ms_regs ms1) (ms_mem ms1) MD1 _ TP_CL).
  - exact HI1.
  - exact R231.
  - exact (tk_ov_ch_ok SK B LV c HC (ms_regs ms1) _ HRCH1 R231).
  - vm_compute; reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons;
      [exact (ck_Rg_ok (ms_regs ms1) (ms_mem ms1) MD1 _ HI1) | apply Forall_nil]]].
    + unfold tk_ch, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U10'. split; [unfold MD_NEXT; lia|]. split; [unfold MD_NEXT, MD_SIZE in *; lia|].
      split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS _ _ (tk_m c + MD_NEXT) 0 4 (SOff 12 1) (ci + 1));
        [ apply ck_denoff; [exact E12' | lia] | ck_zrng | ck_zrng | exact Vnew ].
    + unfold tk_ch, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U11'. split; [unfold LA_G_NL, NK_CHUNK_LEN; lia|].
      split; [unfold LA_G_NL, NK_CHUNK_LEN; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS _ _ (LA_G_NL + NK_CHUNK_LEN + 8 * ci) 0 8 (SOff 49 0)
        (fld_u64 kbs (NK_CHUNK_LEN + 8 * ci)));
        [ apply ck_den0; [exact F49 | unfold NL_CHUNK_MAX in *; lia] | ck_zrng | ck_zrng |].
      replace (LA_G_NL + NK_CHUNK_LEN + 8 * ci + 0) with (LA_G_NL + (NK_CHUNK_LEN + 8 * ci)) by lia.
      apply (ck_gfield8 (ms_regs ms1) (ms_mem ms1) MD1 (NK_CHUNK_LEN + 8 * ci) HI1);
        [unfold NK_CHUNK_LEN; lia | unfold NK_CHUNK_LEN, NK_SIZE; lia].
  - apply pairwise_disjoint_of_extents. unfold tk_Rg, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U10', U11', Ug'.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold apart_gnl, LA_G_NL, NK_SIZE, NK_CHUNK_LEN, MD_SIZE, MD_NEXT in *. repeat split; lia.
  - refine (conj _ (conj _ (conj _ (conj _ (ck_gfacts_ok (ms_regs ms1) _)))));
      unfold afact_ok; cbn [af_lo af_hi af_al2].
    + rewrite U10', Z.pow_0_r, Z.mod_1_r. unfold MD_NEXT, MD_SIZE in *. lia.
    + rewrite U11'. split; [unfold NK_CHUNK_LEN; lia|]. split; [|lia].
      change (2 ^ 3) with 8. unfold LA_G_NL, NK_CHUNK_LEN.
      replace (6146752 + 262144 + 8 * ci) with ((801112 + ci) * 8) by lia.
      apply Z.mod_mul. lia.
    + rewrite E12', (ck_uw ci) by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
    + rewrite F49, (ck_uw (fld_u64 kbs (NK_CHUNK_LEN + 8 * ci))) by (unfold NL_CHUNK_MAX in *; lia).
      rewrite Z.pow_0_r, Z.mod_1_r. unfold NL_CHUNK_MAX in *. lia. }
assert (SHOK : sh_ok SEGS tk_Bx tk_SH_cl
    (tk_E c (ms_regs ms1) (ck_xs (fld_u64 kbs (NK_CHUNK_LEN + 8 * ci)))) (rdW W (ms_mem ms1))).
{ unfold tk_SH_cl. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (ck_shent (ms_regs ms1) (ms_mem ms1) MD1 _ 10%nat 10%bv (tk_m c + MD_NEXT) 8 HI1
      ltac:(lia) ltac:(reflexivity) R231 ltac:(rewrite K10; exact P10));
      [ unfold MD_NEXT; lia | lia | unfold MD_NEXT, MD_SIZE in *; lia
      | unfold amem_range, kLowMemEnd, kHighMemBeg, MD_NEXT, MD_SIZE in *;
        destruct Hm2 as [Hq|Hq]; [left|right]; lia
      | apply (range_addressable_sub _ _ (tk_m c) MD_SIZE); [exact Hmra | unfold MD_NEXT; lia
        | unfold MD_NEXT, MD_SIZE; lia] ].
  - apply (ck_shent (ms_regs ms1) (ms_mem ms1) MD1 _ 11%nat 11%bv
      (LA_G_NL + NK_CHUNK_LEN + 8 * ci) 8 HI1 ltac:(lia) ltac:(reflexivity) R231 R11);
      [ unfold LA_G_NL, NK_CHUNK_LEN; lia | lia | unfold LA_G_NL, NK_CHUNK_LEN, kHighMemEnd; lia
      | left; unfold LA_G_NL, NK_CHUNK_LEN, kLowMemEnd; lia
      | apply (range_addressable_sub _ _ (LA_G_NL + NK_CHUNK) NK_N_CHUNKS);
        [ exact HRAq | unfold NK_CHUNK, NK_CHUNK_LEN; lia
        | unfold NK_CHUNK, NK_CHUNK_LEN, NK_N_CHUNKS; lia ] ]. }
(* +0x1c8 .. +0x1dc: the check and the load of chunk_len[c], then `bge left, 16` *)
paj_run_tok RUN HS HJ SHOK tk_span; [ck_awr0|].
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msb end.
assert (Emb : ms_mem msb = ms_mem ms1)
  by (eapply frame_of_read_only; [|exact HF]; vm_compute; reflexivity).
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK tk_span;
  rewrite (ck_ge _ (SOff 49 0) (SLit 16) (fld_u64 kbs (NK_CHUNK_LEN + 8 * ci)) 16) in Hc
    by (first [apply ck_den0; [exact F49 | unfold NL_CHUNK_MAX in *; lia] | reflexivity
              | unfold NL_CHUNK_MAX in *; lia]).
- (* 16 <= chunk_len: the message loop *)
  apply negb_true_iff, Z.ltb_ge in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_MS; [ck_awr0|].
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms2 end.
  assert (Em2 : ms_mem ms2 = ms_mem ms1)
    by (rewrite <- Emb; eapply frame_of_read_only; [|exact HF]; vm_compute; reflexivity).
  rewrite Em2 in HJ. pmkst HS. rewrite Em2.
  pose proof (regs_kept_of_st_ok_pi _ _ _ (ms_regs ms1)
    (tk_ext c ++ ck_xs (fld_u64 kbs (NK_CHUNK_LEN + 8 * ci)))
    [2%bv;3%bv;4%bv;8%bv;9%bv;10%bv;18%bv;19%bv;23%bv] HS
    (ck_agree (ms_regs ms1) (ck_xs (fld_u64 kbs (NK_CHUNK_LEN + 8 * ci))))
    ltac:(vm_compute; reflexivity)) as RK2.
  ck_keep RK2 (2%bv : bv 5) L2. ck_keep RK2 (3%bv : bv 5) L3. ck_keep RK2 (4%bv : bv 5) L4.
  ck_keep RK2 (8%bv : bv 5) L8. ck_keep RK2 (9%bv : bv 5) L9. ck_keep RK2 (10%bv : bv 5) L10.
  ck_keep RK2 (18%bv : bv 5) L18. ck_keep RK2 (19%bv : bv 5) L19. ck_keep RK2 (23%bv : bv 5) L23.
  ck_reg HS (6%bv : bv 5) M6. ck_reg HS (7%bv : bv 5) M7. ck_reg HS (13%bv : bv 5) M13.
  ck_reg HS (14%bv : bv 5) M14. ck_reg HS (15%bv : bv 5) M15. ck_reg HS (16%bv : bv 5) M16.
  ck_reg HS (17%bv : bv 5) M17. ck_reg HS (20%bv : bv 5) M20. ck_reg HS (28%bv : bv 5) M28.
  destruct (nk_chunk_len kbs ci HNW HKL Hci) as (HCKL & _ & _).
  change (nk_chunk kbs ci) with (tk_ck c ci) in HCKL.
  apply (HMSG ci 0 (Z.of_nat (length (tk_ck c ci))) (S (length (tk_ck c ci))) HNXT).
  + apply (ck_inv_same (ms_regs ms1) (ms_mem ms1) MD1 _ _ HI1 HJ);
      [ repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
      | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
      | exact L2 | exact L3 | exact L4 ].
  + split; [rewrite L8, K8; exact R8|]. split; [rewrite L9, K9; exact R9 | rewrite L23; exact R231].
  + split; [rewrite L18, K18; exact N18 | rewrite L19, K19; exact N19].
  + apply (ck_rch_keep (ms_regs ms1) _ _ HRCH1 R231 L10 M13 M14 M15 M16 M17 M6).
  + rewrite M20. unfold tk_b. apply (ck_den_b _ ci); [exact E12' | exact Ug' | lia].
  + rewrite M7. reflexivity.
  + rewrite M28. rewrite HCKL. apply ck_den0; [exact F49 | unfold NL_CHUNK_MAX in *; lia].
  + exists (md_set_next mb (ci + 1)). split; [exact HMnew|]. split; [exact HMO2 | exact HN2].
  + exact HB1.
  + exact HMAIN.
  + exact HCL.
  + exact Hci.
  + apply chunk_walk_eq.
  + lia.
  + lia.
  + split; [lia | lia].
- (* chunk_len < 16: the next chunk *)
  apply negb_false_iff, Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_NX; [ck_awr0|].
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms2 end.
  assert (Em2 : ms_mem ms2 = ms_mem ms1)
    by (rewrite <- Emb; eapply frame_of_read_only; [|exact HF]; vm_compute; reflexivity).
  rewrite Em2 in HJ. pmkst HS. rewrite Em2.
  pose proof (regs_kept_of_st_ok_pi _ _ _ (ms_regs ms1)
    (tk_ext c ++ ck_xs (fld_u64 kbs (NK_CHUNK_LEN + 8 * ci)))
    [2%bv;3%bv;4%bv;8%bv;9%bv;10%bv;18%bv;19%bv;23%bv] HS
    (ck_agree (ms_regs ms1) (ck_xs (fld_u64 kbs (NK_CHUNK_LEN + 8 * ci))))
    ltac:(vm_compute; reflexivity)) as RK2.
  ck_keep RK2 (2%bv : bv 5) L2. ck_keep RK2 (3%bv : bv 5) L3. ck_keep RK2 (4%bv : bv 5) L4.
  ck_keep RK2 (8%bv : bv 5) L8. ck_keep RK2 (9%bv : bv 5) L9. ck_keep RK2 (10%bv : bv 5) L10.
  ck_keep RK2 (18%bv : bv 5) L18. ck_keep RK2 (19%bv : bv 5) L19. ck_keep RK2 (23%bv : bv 5) L23.
  ck_reg HS (6%bv : bv 5) M6. ck_reg HS (13%bv : bv 5) M13.
  ck_reg HS (14%bv : bv 5) M14. ck_reg HS (15%bv : bv 5) M15. ck_reg HS (16%bv : bv 5) M16.
  ck_reg HS (17%bv : bv 5) M17.
  destruct (nk_chunk_len kbs ci HNW HKL Hci) as (HCKL & _ & _).
  apply HNXT.
  + apply (ck_inv_same (ms_regs ms1) (ms_mem ms1) MD1 _ _ HI1 HJ);
      [ repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
      | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
      | exact L2 | exact L3 | exact L4 ].
  + split; [rewrite L8, K8; exact R8|]. split; [rewrite L9, K9; exact R9 | rewrite L23; exact R231].
  + split; [rewrite L18, K18; exact N18 | rewrite L19, K19; exact N19].
  + apply (ck_rch_keep (ms_regs ms1) _ _ HRCH1 R231 L10 M13 M14 M15 M16 M17 M6).
  + exists (md_set_next mb (ci + 1)). split; [exact HMnew|]. split; [exact HMO2 | exact HN2].
  + exact HB1.
  + exact HMAIN.
  + apply (cls_miss mbs kbs ci HCL Hci). unfold chunk_walk. apply ms_short. lia.
  + lia.
Qed.

Lemma ck_nxt_all : TK_RET SK B c -> TK_MSG SK B c ->
  forall k j, (Z.to_nat (tk_nch c - j) <= k)%nat -> TK_NXT SK B c j.
Proof.
  intros HRET HMSG k. induction k as [|k IH]; intros j Hk.
  - apply (ck_nx_step HRET j). intros Hlt. exfalso. lia.
  - apply (ck_nx_step HRET j). intros Hlt. apply (ck_ch_step HRET HMSG j).
    apply (IH (j + 1)). lia.
Qed.

Lemma tk_nxt_ok : TK_RET SK B c -> TK_MSG SK B c -> forall j, TK_NXT SK B c j.
Proof. intros HRET HMSG j. exact (ck_nxt_all HRET HMSG (Z.to_nat (tk_nch c - j)) j ltac:(lia)). Qed.

Lemma tk_chunk_ok : TK_RET SK B c -> TK_MSG SK B c -> TK_CHUNK SK B c.
Proof. intros HRET HMSG ci. exact (ck_ch_step HRET HMSG ci (tk_nxt_ok HRET HMSG (ci + 1))). Qed.

(* +0x16c: next and n_chunks; the loop head or the exit *)
Lemma tk_cl0_ok : TK_RET SK B c -> TK_MSG SK B c -> TK_CL0 SK B c.
Proof.
intros HRET HMSG regs mem md HI HR0 HRN R20 HCM HB HMAIN.
pose proof (tk_chunk_ok HRET HMSG) as HCH.
pose proof ck_wf as (HNW & HMW & HML & HKL & HRQ).
pose proof ck_nch as (Hn & He & Hclen).
destruct (tk_m_facts SK B c HC) as (Hm0 & Hmhi & Hm2 & Hmg & Hmf & Hmra & Hmh & Hmbs).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof HI as (HJ & _).
pose proof HR0 as (R8 & R9 & R23).
pose proof HRN as (N18 & N19).
pose proof HCM as (mb & HM & HMO & HN).
pose proof HMW as (_ & HNXR & _).
pose proof (ck_xs_atoms regs (md_next mbs)) as (E49 & E50 & E51).
assert (E20 : ew (tk_E c regs (ck_xs (md_next mbs))) 20 = w64 (tk_m c))
  by (rewrite (tk_E_reg c regs (ck_xs (md_next mbs)) 20 20%bv) by (lia || reflexivity); exact R20).
assert (U20 : bv_unsigned (ew (tk_E c regs (ck_xs (md_next mbs))) 20) = tk_m c)
  by (rewrite E20; apply ck_uw; unfold MD_SIZE in *; lia).
assert (Ug : bv_unsigned (ew (tk_E c regs (ck_xs (md_next mbs))) (A_OBJ 2)) = LA_G_NL)
  by exact (tk_E_gnl LV c regs (ck_xs (md_next mbs))).
pose proof (ck_Eg regs (ck_xs (md_next mbs))) as Eg.
pose proof (tk_E_env c regs (ck_xs (md_next mbs))) as HEI.
assert (HS : st_ok_pi SEGS VAL (tk_E c regs (ck_xs (md_next mbs))) tk_ss_cl0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + TP_CL0)) mem (seg_rom SEGS)))).
{ unfold tk_ss_cl0. apply (tk_st_ok SK B LV c HC regs mem md (ck_xs (md_next mbs)) TP_CL0).
  - exact HI.
  - exact R23.
  - apply Forall_nil.
  - vm_compute; reflexivity.
  - apply Forall_cons;
      [|apply Forall_cons; [exact (ck_Rg_ok regs mem md (md_next mbs) HI) | apply Forall_nil]].
    unfold tk_ch, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U20. split; [lia|]. split; [unfold MD_SIZE in *; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ (tk_m c) 8 4 (SOff 49 0) (md_next mbs));
      [ apply ck_den0; [exact E49 | lia] | ck_zrng | ck_zrng |].
    rewrite <- HN. exact (ck_mnext mem mb HM).
  - apply pairwise_disjoint_of_extents. unfold tk_Rg, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U20, Ug.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold apart_gnl, LA_G_NL, NK_SIZE, MD_SIZE in *. repeat split; lia.
  - refine (conj _ (conj _ (ck_gfacts_ok regs (md_next mbs)))); unfold afact_ok;
      cbn [af_lo af_hi af_al2].
    + rewrite U20, Z.pow_0_r, Z.mod_1_r. unfold MD_SIZE in *. lia.
    + rewrite E49, (ck_uw (md_next mbs)) by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
assert (SHOK : sh_ok SEGS tk_Bx tk_SH_cl0 (tk_E c regs (ck_xs (md_next mbs))) (rdW W mem))
  by exact (ck_sh_m regs mem md (ck_xs (md_next mbs)) HI R23 R20).
pose proof (paj_run_x SK B LAWS (tc_G c) ck_HGX (tc_XO c) (tc_OUT c)) as RUN.
pose proof (paj_run_to_x SK B LAWS (tc_G c) ck_HGX (tc_XO c) (tc_OUT c)) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
paj_run_tok RUN HS HJ SHOK tk_span; [ck_awr0|].
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
assert (Em1 : ms_mem ms1 = mem) by (eapply frame_of_read_only; [|exact HF]; vm_compute; reflexivity).
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK tk_span;
  rewrite (ck_ge _ (SOff 49 0) (SOff 50 0) (md_next mbs) (tk_nch c)) in Hc
    by (first [apply ck_den0; [assumption | lia] | lia]).
- (* n_chunks <= next: the exit *)
  apply negb_true_iff, Z.ltb_ge in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_RT; [ck_awr0|].
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms2 end.
  assert (Em2 : ms_mem ms2 = mem)
    by (rewrite <- Em1; eapply frame_of_read_only; [|exact HF]; vm_compute; reflexivity).
  rewrite Em2 in HJ. pmkst HS. rewrite Em2.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs (tk_ext c ++ ck_xs (md_next mbs))
    [2%bv;3%bv;4%bv;23%bv] HS (ck_agree regs (ck_xs (md_next mbs)))
    ltac:(vm_compute; reflexivity)) as RK.
  ck_keep RK (2%bv : bv 5) K2. ck_keep RK (3%bv : bv 5) K3. ck_keep RK (4%bv : bv 5) K4.
  ck_keep RK (23%bv : bv 5) K23.
  ck_reg HS (11%bv : bv 5) Q11.
  apply (ck_exit (md_next mbs) _ mem _ HRET).
  + apply (ck_inv_same regs mem md _ _ HI HJ);
      [ repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
      | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
      | exact K2 | exact K3 | exact K4 ].
  + rewrite K23; exact R23.
  + rewrite Q11. apply (ck_sub0 _ (SOff 51 0) (nk_end_errno kbs));
      [ apply (ck_U0 _ 51 _ E51); lia | lia ].
  + exists mb. split; [exact HM|]. split; [exact HMO | exact HN].
  + exact HB.
  + exact HMAIN.
  + apply cls_start.
  + exact Hc.
- (* next < n_chunks: the loop head *)
  apply negb_false_iff, Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_CH; [ck_awr0|].
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms2 end.
  assert (Em2 : ms_mem ms2 = mem)
    by (rewrite <- Em1; eapply frame_of_read_only; [|exact HF]; vm_compute; reflexivity).
  rewrite Em2 in HJ. pmkst HS. rewrite Em2.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs (tk_ext c ++ ck_xs (md_next mbs))
    [2%bv;3%bv;4%bv;8%bv;9%bv;18%bv;19%bv;20%bv;23%bv] HS (ck_agree regs (ck_xs (md_next mbs)))
    ltac:(vm_compute; reflexivity)) as RK.
  ck_keep RK (2%bv : bv 5) K2. ck_keep RK (3%bv : bv 5) K3. ck_keep RK (4%bv : bv 5) K4.
  ck_keep RK (8%bv : bv 5) K8. ck_keep RK (9%bv : bv 5) K9. ck_keep RK (18%bv : bv 5) K18.
  ck_keep RK (19%bv : bv 5) K19. ck_keep RK (23%bv : bv 5) K23.
  ck_reg HS (6%bv : bv 5) Q6. ck_reg HS (10%bv : bv 5) Q10. ck_reg HS (12%bv : bv 5) Q12.
  ck_reg HS (13%bv : bv 5) Q13. ck_reg HS (14%bv : bv 5) Q14. ck_reg HS (15%bv : bv 5) Q15.
  ck_reg HS (16%bv : bv 5) Q16. ck_reg HS (17%bv : bv 5) Q17.
  apply (HCH (md_next mbs)).
  + apply (ck_inv_same regs mem md _ _ HI HJ);
      [ repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
      | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
      | exact K2 | exact K3 | exact K4 ].
  + split; [rewrite K8; exact R8|]. split; [rewrite K9; exact R9 | rewrite K23; exact R23].
  + split; [rewrite K18; exact N18 | rewrite K19; exact N19].
  + split.
    { rewrite Q10. apply (ck_denoff _ 20 (tk_m c) 8); [exact E20 | unfold MD_SIZE in *; lia]. }
    split.
    { rewrite Q13. apply (tk_den_shx _ (SOff 20 8) (tk_m c + MD_NEXT));
        [ apply (ck_Uoff _ 20 (tk_m c) 8); [exact E20 | unfold MD_SIZE in *; lia
          | unfold MD_NEXT, MD_SIZE in *; lia]
        | unfold tk_Bx; apply (tk_U_reg c regs (ck_xs (md_next mbs)) 23 23%bv);
          [lia | reflexivity | exact R23 | unfold SHADOW_OFF; lia]
        | unfold MD_NEXT, MD_SIZE in *; lia ]. }
    split; [rewrite Q14; reflexivity|]. split.
    { rewrite Q15. apply (ck_denoff _ 243%nat LA_G_NL 262144); [exact Eg | unfold LA_G_NL; lia]. }
    split.
    { rewrite Q16. apply (ck_den0 _ 243%nat LA_G_NL); [exact Eg | unfold LA_G_NL; lia]. }
    split; [rewrite Q17; reflexivity | rewrite Q6; reflexivity].
  + rewrite Q12. apply ck_den0; [exact E49 | lia].
  + exact HCM.
  + exact HB.
  + exact HMAIN.
  + apply cls_start.
  + lia.
Qed.

End w.

