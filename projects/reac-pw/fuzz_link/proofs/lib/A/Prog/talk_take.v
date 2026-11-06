(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v, with its module paths and module names changed; 1428 of its 1523 lines of code are new or changed and 2594 lines of the source are left out. *)
(* talk on image A: the two inlined copies of take_text (fuzz_link.c:318-328) in its walk, the pieces TK_TAKE_AL
   (+0x3a0 .. +0x594, into the alias buffer) and TK_TAKE_KD (+0x47c .. +0x500, into the kind buffer) of
   lib/A/Prog/talk_defs.v (listing (internal path) (internal record, sha256 5526460cb5be)).
   Each copy, with pay the attribute's payload of n = l - 4 bytes at d = b + 4 + a (b + 4 the spilled word):
   - +0x3a0 / +0x47c: n := l - 4, d := b + 4 + a, s2 := 0; n = 0 goes to the clamp;
   - +0x3b8 / +0x494, the NUL scan, one fresh state per byte d[k] at the atom a3 = d + k (its instrumented check
     covered by the chunk queue's addressable range): d[k] = 0 or k + 1 = n goes to the clamp, else the next byte;
     at the clamp s2 = nul_at pay (by induction on n - k, the bytes before k hold no NUL);
   - +0x55c / +0x4c8: s2 := min (s2, cap - 1) from the spilled cap - 1, then checked_memcpy (buffer, d, s2)
     (talk_kit.v tk_intrin, a destination in a live buffer, a source in the chunk queue);
   - +0x574 / +0x4e0 and +0x578 / +0x4e4: the NUL store at buffer + s2, a5 := 4, a6 := 1, a7 := 3, and the next
     step +0x598 / +0x504 (TK_A598 / TK_K504);
   - the buffer then holds acstr_at of cut_text pay cap (talk_spec.v acstr_take); the model block, the other
     buffer and the spilled words keep their bytes (tt_amem_alias / tt_amem_kind).
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
link_aaddr link_amem link_ajkit LinkWalk fuzz_recv_kit talk_c talk_defs talk_kit talk_spec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ---- generic: values of symbolic terms ------------------------------------------------------------------------ *)
Lemma tt_U_lit : forall E z, 0 <= z < 2 ^ 64 -> U E (SLit z) = z.
Proof. intros E z Hz. rewrite U_SLit. unfold zcanon, M64. apply Z.mod_small. lia. Qed.

Lemma tt_U_add : forall E x k y v1 v2, ew E x = w64 v1 -> ew E y = w64 v2 ->
  0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> 0 <= v1 + k < 2 ^ 64 -> 0 <= v1 + k + v2 < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SOff x k) (SOff y 0)) = v1 + k + v2.
Proof.
  intros E x k y v1 v2 H1 H2 R1 R2 R3 R4. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom_off E x v1 k H1 R1 R3), (U_atom E y v2 H2 R2). unfold zcanon, M64. apply Z.mod_small. lia.
Qed.

(* the kept registers of a segment: sp, gp, tp and the callee-saved registers but s2 *)
Definition tt_KL : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv].
Definition tt_same (r1 r2 : bvmap 5 word) : Prop := forall r, In r tt_KL -> getr r2 r = getr r1 r.

Ltac tt_in := unfold tt_KL; cbn [In]; repeat (first [left; reflexivity | right]).

Lemma tt_same_trans : forall r1 r2 r3, tt_same r1 r2 -> tt_same r2 r3 -> tt_same r1 r3.
Proof. intros r1 r2 r3 H12 H23 r Hr. rewrite (H23 r Hr). exact (H12 r Hr). Qed.

Lemma tt_pres : forall r1 r2, aregs_preserved r1 r2 -> forall (r : bv 5), acallee_saved (bv_unsigned r) ->
  getr r2 r = getr r1 r.
Proof. intros r1 r2 HP r Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). exact (HP _ Hr). Qed.

Ltac tt_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?x] =>
    let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia.

Lemma tt_same_pres : forall r1 r2, aregs_preserved r1 r2 -> tt_same r1 r2.
Proof.
  intros r1 r2 HP r Hr. apply (tt_pres r1 r2 HP). unfold tt_KL in Hr.
  repeat (destruct Hr as [<-|Hr]; [tt_cs|]). destruct Hr.
Qed.

(* a register of a symbolic state at a stop, unnormalised *)
Ltac tt_reg HS r Hr :=
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

(* the write permission of a run whose regions have no write window *)
Ltac tt_awr0 :=
  intros ?a (?r & ?Hin & ?Hr); vm_compute in Hin;
  repeat (destruct Hin as [?Hq | Hin]; [subst r; cbn [YP09.r_wlo YP09.r_whi] in Hr; lia |]); destruct Hin.

(* a run over regions with no write window keeps the memory *)
Ltac tt_ro HF Em :=
  lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
    assert (Em : m' = m) by exact (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) end.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ link_listing PI).
#[local] Abbreviation VAL := (@pa_val _ link_listing PI).
#[local] Abbreviation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Abbreviation cfg_of regs pc mem md := (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom SEGS)) md).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis LV : LinkVals.
Hypothesis MEMCPY : aintrin_realizes SEGS B OCpy (pa_sigma LS___asan_memcpy).
Variable c : tkc.
Hypothesis HC : tk_call SK B c.
#[local] Abbreviation W := (tc_W c).
#[local] Abbreviation memc := (tc_memc c).
#[local] Abbreviation regs0 := (tc_regs0 c).
#[local] Abbreviation kbs := (tc_kbs c).

(* ---- small facts ------------------------------------------------------------------------------------------------ *)
Lemma tt_region : forall E ss ms i r, st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r ->
  region_ok SEGS E (ms_mem ms) r.
Proof. intros E ss ms i r HS Hi. exact (st_ok_region_nth (segs := SEGS) E (abs_ss VAL ss) ms i r HS ltac:(destruct ss; exact Hi)). Qed.

Lemma tt_den : forall regs xs n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  sv_denot (tk_E c regs xs) (SOff n 0) = getr regs r.
Proof.
  intros regs xs n r Hn Hr. cbn [sv_denot]. rewrite (tk_E_reg c regs xs n r Hn Hr), Z.add_0_r.
  apply Z_to_bv_bv_unsigned.
Qed.

Lemma tt_val1 : forall m a (bb : byte), mbyte SEGS m a = Some bb -> val_mem SEGS m a 1 (bz bb).
Proof.
  intros m a bb H j Hj. assert (j = 0%nat) by lia. subst j. cbn [Z.of_nat]. rewrite Z.add_0_r, H. f_equal.
  pose proof (tw_byte_range bb) as R.
  replace (YO0f.le_byte (bz bb) 1 0) with (bz bb).
  - symmetry. apply Z_to_bv_bv_unsigned.
  - unfold YO0f.le_byte. change (bz bb = Z.shiftr (bz bb mod 2 ^ 8) 0 mod 256).
    rewrite Z.shiftr_0_r. rewrite (Z.mod_small (bz bb) (2 ^ 8)) by (change (2 ^ 8) with 256; lia).
    rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma tt_an_pos : tk_an c <> 0 -> 1 <= tk_an c.
Proof.
  intros H. pose proof (bv_unsigned_in_range 64 (getr (tc_regs0 c) (Z_to_bv 5 (10 + 6)))) as R.
  unfold tk_an, aarg, argZ in *. lia.
Qed.

Lemma tt_kn_pos : tk_kn c <> 0 -> 1 <= tk_kn c.
Proof.
  intros H. pose proof (bv_unsigned_in_range 64 (getr (tc_regs0 c) (Z_to_bv 5 (10 + 4)))) as R.
  unfold tk_kn, aarg, argZ in *. lia.
Qed.

Lemma tt_rs0_same : forall r1 r2, tt_same r1 r2 -> tk_rs0 c r1 -> tk_rs0 c r2.
Proof.
  intros r1 r2 Hs (H8 & H9 & H23). unfold tk_rs0.
  rewrite (Hs 8%bv ltac:(tt_in)), (Hs 9%bv ltac:(tt_in)), (Hs 23%bv ltac:(tt_in)). auto.
Qed.

Lemma tt_rat_same : forall r1 r2 b a al, tt_same r1 r2 -> tk_rat r1 b a al ->
  getr r2 15 = w64 4 -> getr r2 16 = w64 1 -> getr r2 17 = w64 3 -> tk_rat r2 b a al.
Proof.
  intros r1 r2 b a al Hs (H20 & H27 & H22 & H19 & _) H15 H16 H17. unfold tk_rat.
  rewrite (Hs 20%bv ltac:(tt_in)), (Hs 27%bv ltac:(tt_in)), (Hs 22%bv ltac:(tt_in)), (Hs 19%bv ltac:(tt_in)).
  auto 10.
Qed.

(* the chunk queue's addressable range, at the current memory *)
Lemma tt_ra_gnl : forall regs mem md, tk_inv SK B c regs mem md -> forall x n,
  LA_G_NL <= x -> x + n <= LA_G_NL + NK_N_CHUNKS -> range_addressable (rd_of SEGS (rdW W mem)) SHADOW_OFF x n.
Proof.
  intros regs mem md HI x n H1 H2.
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRAq & _).
  rewrite <- (aview_rd_of SEGS).
  change (ard SEGS (rdW W memc)) with (aview SEGS (w_H W) memc) in HRAq.
  apply (range_addressable_sub _ _ (LA_G_NL + NK_CHUNK) NK_N_CHUNKS); [| unfold NK_CHUNK; lia | unfold NK_CHUNK; lia].
  apply (tk_ra_kept SK B c HC regs mem md _ _ HI);
    [unfold LA_G_NL, NK_CHUNK; lia | unfold LA_G_NL, NK_CHUNK, NK_N_CHUNKS, kHighMemEnd; lia | exact HRAq].
Qed.

(* a chunk of the queue: its length and the bound on its index *)
Lemma tt_chunk : forall ci, 0 <= ci < tk_nch c ->
  Z.of_nat (length (tk_ck c ci)) = fld_u64 kbs (NK_CHUNK_LEN + 8 * ci) /\
  0 <= fld_u64 kbs (NK_CHUNK_LEN + 8 * ci) <= NL_CHUNK_MAX /\ tk_nch c <= NL_CHUNKS.
Proof.
  intros ci Hci. pose proof HC as (_ & _ & _ & (_ & HNL) & HNW & _).
  unfold tk_nch, tk_ck in *. destruct (nk_chunk_len kbs ci HNW HNL Hci) as (H1 & H2 & H3). lia.
Qed.

(* the payload bytes of the attribute at o (length L) of chunk ci, at the current memory *)
Lemma tt_pay_mem : forall regs mem md ci o L, tk_inv SK B c regs mem md -> 0 <= ci < tk_nch c -> 0 <= o -> 4 <= L ->
  o + L <= Z.of_nat (length (tk_ck c ci)) ->
  forall i, 0 <= i < L - 4 ->
  mbyte SEGS (rdW W mem) (tk_b ci + 4 + o + i) = nth_error (slice (tk_ck c ci) (o + RTA_HDR) (L - RTA_HDR)) (Z.to_nat i).
Proof.
  intros regs mem md ci o L HI Hci Ho HL Hol i Hi.
  destruct (tt_chunk ci Hci) as (Hcl & Hcl2 & Hnc).
  pose proof HC as (_ & _ & _ & (_ & HNL) & _).
  unfold tk_nch, tk_ck, tk_b in *.
  rewrite (tt_pay_kbs kbs ci o L i) by lia.
  destruct (tk_nlk_kept SK B c HC regs mem md HI) as (((_ & _ & Hb) & _) & _).
  replace (LA_G_NL + NL_CHUNK_MAX * ci + 4 + o + i) with (LA_G_NL + Z.of_nat (Z.to_nat (4096 * ci + o + 4 + i)))
    by (unfold NL_CHUNK_MAX; lia).
  apply Hb. unfold NL_CHUNK_MAX, NL_CHUNKS, NK_SIZE in *. lia.
Qed.

(* ---- the memory after a take ----------------------------------------------------------------------------------- *)
(* the bytes kept: all but [x, x + n) and checked_memcpy's window below the frame *)
Definition tt_kept (x n : Z) (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (x <= a < x + n) -> ~ (tk_sp c - 144 - ESTACK <= a < tk_sp c - 144) ->
  aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.

(* the model block and the spilled words are apart from a live buffer and the callee's window *)
Lemma tt_model_kept : forall regs' mem mem' md' x n, tk_inv SK B c regs' mem' md' ->
  apart x n (tk_m c) MD_SIZE -> tt_kept x n mem mem' ->
  (exists mb, amodel_at SEGS (rdW W mem) (tk_m c) mb /\ tk_mres c mb) ->
  (exists mb, amodel_at SEGS (rdW W mem') (tk_m c) mb /\ tk_mres c mb).
Proof.
  intros regs' mem mem' md' x n HI' Hap UN (mb & Hm & Hres). exists mb. split; [|exact Hres].
  pose proof HI' as (_ & _ & _ & _ & _ & _ & _ & _ & PR).
  destruct (tk_m_facts SK B c HC) as (M0 & M1 & M2 & M3 & M4 & M5 & M6 & ((_ & Mwr) & ML)).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  apply (amodel_kept SEGS (rdW W mem) (rdW W mem') (tk_m c) mb Hm).
  - intros i Hi. apply (mbyte_of_aview SEGS (w_H W) (w_H W) mem mem'). apply UN.
    + unfold MD_SIZE in *. lia.
    + unfold apart, MD_SIZE in *. lia.
    + unfold apart_frame, tk_sp, TALK_AK, TALK_AFRAME, ESTACK, MD_SIZE in *. lia.
  - intros i Hi. apply (writable_kept (w_H W) memc mem' _ (PR _)). apply Mwr. lia.
Qed.

Lemma tt_spilled_kept : forall mem mem' b x n,
  (x + n <= tk_sp c - TALK_AK \/ tk_sp c <= x) -> tt_kept x n mem mem' -> tk_spilled c mem b -> tk_spilled c mem' b.
Proof.
  intros mem mem' b x n Hx UN HSP. destruct (tk_sp_rng SK B c HC) as (S0 & S1 & S2 & S3).
  unfold tk_spilled in *. rewrite Forall_forall in *. intros [o w] Hin.
  pose proof (HSP (o, w) Hin) as HV. cbn [fst snd] in HV |- *.
  assert (Ho : 0 <= o <= 32).
  { unfold tk_spill_vals in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hq|Hin]; [injection Hq as <- _; lia|]). destruct Hin. }
  apply (val_mem_kept (w_H W) mem mem'); [|exact HV]. intros q Hq. cbn in Hq.
  apply UN; unfold TALK_AK, TALK_AFRAME, ESTACK in *; lia.
Qed.

(* the kind buffer after a take into the alias buffer (and the alias buffer after one into the kind buffer) *)
Lemma tt_abuf_kept : forall regs' mem mem' md' p n, tk_inv SK B c regs' mem' md' ->
  abuf SEGS (rdW W memc) p n -> abuf SEGS (rdW W mem) p n ->
  (forall i, 0 <= i < n -> aview SEGS (w_H W) mem' (p + i) = aview SEGS (w_H W) mem (p + i)) ->
  abuf SEGS (rdW W mem') p n.
Proof.
  intros regs' mem mem' md' p n HI' Hc Hm K. pose proof HI' as (_ & _ & _ & _ & _ & _ & _ & _ & PR).
  apply (abuf_after SEGS (rdW W mem) (rdW W mem') _ _ Hm).
  - intros i Hi. left. apply (mbyte_of_aview SEGS (w_H W) (w_H W) mem mem'). exact (K i Hi).
  - intros i Hi. destruct Hc as (junk & Hjl & _ & Hwr). apply (writable_kept (w_H W) memc mem' _ (PR _)).
    apply Hwr. lia.
Qed.

Lemma tt_acstr_kept : forall mem mem' p s,
  acstr_at SEGS (rdW W mem) p s ->
  (forall i, 0 <= i <= Z.of_nat (length s) -> aview SEGS (w_H W) mem' (p + i) = aview SEGS (w_H W) mem (p + i)) ->
  acstr_at SEGS (rdW W mem') p s.
Proof.
  intros mem mem' p s ((Q0 & Q1 & Qb) & Qn) K. split; [|exact Qn]. split; [exact Q0|]. split; [exact Q1|].
  intros i Hi. rewrite <- (Qb i Hi). apply (mbyte_of_aview SEGS (w_H W) (w_H W) mem mem').
  rewrite length_app in Hi. cbn [length] in Hi. apply K. lia.
Qed.

(* the buffer a take wrote: present bytes up to its NUL, the kept ones after it *)
Lemma tt_abuf_written : forall regs' mem mem' md' p n s, tk_inv SK B c regs' mem' md' ->
  abuf SEGS (rdW W memc) p n -> abuf SEGS (rdW W mem) p n -> Z.of_nat (length s) + 1 <= n ->
  acstr_at SEGS (rdW W mem') p s ->
  (forall i, Z.of_nat (length s) + 1 <= i < n -> aview SEGS (w_H W) mem' (p + i) = aview SEGS (w_H W) mem (p + i)) ->
  abuf SEGS (rdW W mem') p n.
Proof.
  intros regs' mem mem' md' p n s HI' Hc Hm Hl ((_ & _ & Hby) & _) K.
  pose proof HI' as (_ & _ & _ & _ & _ & _ & _ & _ & PR).
  apply (abuf_after SEGS (rdW W mem) (rdW W mem') _ _ Hm).
  - intros i Hi. destruct (Z_lt_le_dec i (Z.of_nat (length s) + 1)) as [Hlt|Hge].
    + right. assert (Hi' : (Z.to_nat i < length (s ++ [zb 0]))%nat) by (rewrite length_app; cbn [length]; lia).
      pose proof (Hby _ Hi') as Hb. rewrite Z2Nat.id in Hb by lia. rewrite Hb.
      destruct (nth_error (s ++ [zb 0]) (Z.to_nat i)) as [x|] eqn:En; [exists x; reflexivity|].
      apply nth_error_None in En. lia.
    + left. apply (mbyte_of_aview SEGS (w_H W) (w_H W) mem mem'). apply K. lia.
  - intros i Hi. destruct Hc as (junk & Hjl & _ & Hwr). apply (writable_kept (w_H W) memc mem' _ (PR _)).
    apply Hwr. lia.
Qed.

Lemma tt_amem_alias : forall regs' mem mem' md' b acc pay kk,
  tk_inv SK B c regs' mem' md' -> tk_amem c mem b acc -> tk_ad c <> 0 -> 1 <= tk_an c ->
  Z.of_nat (length (cut_text pay (tk_an c))) = kk -> tt_kept (tk_ad c) (kk + 1) mem mem' ->
  acstr_at SEGS (rdW W mem') (tk_ad c) (cut_text pay (tk_an c)) ->
  tk_amem c mem' b (Attrs (a_kind acc) (Some pay)).
Proof.
  intros regs' mem mem' md' b acc pay kk HI' (HM & (B1 & B2 & B3 & B4 & B5 & B6) & HSP) Had Han Hkk UN Hcs.
  destruct (tk_ad_facts SK B c HC Had Han) as (A0 & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  destruct (tk_sp_rng SK B c HC) as (S0 & S1 & S2 & S3).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof (tt_cut_len pay (tk_an c) Han) as HL.
  assert (Hk : 0 <= kk <= tk_an c - 1) by lia.
  unfold apart_frame in A5. fold (tk_sp c) in A5.
  split; [|split].
  - apply (tt_model_kept regs' mem mem' md' (tk_ad c) (kk + 1) HI'); [unfold apart in *; lia | exact UN | exact HM].
  - refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
    + intros H0 H1. destruct (tk_kd_facts SK B c HC H0 H1) as (K0 & K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8).
      pose proof (tk_kd_ad_apart SK B c HC H0 H1 Had Han) as KA.
      unfold apart_frame in K5. fold (tk_sp c) in K5.
      apply (tt_abuf_kept regs' mem mem' md' _ _ HI' K8 (B1 H0 H1)). intros i Hi.
      apply UN; unfold apart, TALK_AK, TALK_AFRAME, ESTACK in *; lia.
    + intros _ _. apply (tt_abuf_written regs' mem mem' md' _ _ (cut_text pay (tk_an c)) HI' A8 (B2 Had Han));
        [lia | exact Hcs |].
      intros i Hi. apply UN; unfold TALK_AK, TALK_AFRAME, ESTACK in *; lia.
    + intros p Hp H0 H1. destruct (tk_kd_facts SK B c HC H0 H1) as (K0 & K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8).
      pose proof (tk_kd_ad_apart SK B c HC H0 H1 Had Han) as KA.
      unfold apart_frame in K5. fold (tk_sp c) in K5.
      pose proof (tt_cut_len p (tk_kn c) H1) as HLk.
      apply (tt_acstr_kept mem mem' _ _ (B3 p Hp H0 H1)). intros i Hi.
      apply UN; unfold apart, TALK_AK, TALK_AFRAME, ESTACK in *; lia.
    + intros p Hp _ _. cbn [a_alias] in Hp. injection Hp as <-. exact Hcs.
    + intros Hn H0 H1 i Hi. destruct (tk_kd_facts SK B c HC H0 H1) as (K0 & K1 & K2 & K3 & K4 & K5 & _).
      pose proof (tk_kd_ad_apart SK B c HC H0 H1 Had Han) as KA.
      unfold apart_frame in K5. fold (tk_sp c) in K5.
      rewrite <- (B5 Hn H0 H1 i Hi). apply UN; unfold apart, TALK_AK, TALK_AFRAME, ESTACK in *; lia.
    + intros Hn. cbn [a_alias] in Hn. discriminate Hn.
  - apply (tt_spilled_kept mem mem' b (tk_ad c) (kk + 1)); [lia | exact UN | exact HSP].
Qed.

Lemma tt_amem_kind : forall regs' mem mem' md' b acc pay kk,
  tk_inv SK B c regs' mem' md' -> tk_amem c mem b acc -> tk_kd c <> 0 -> 1 <= tk_kn c ->
  Z.of_nat (length (cut_text pay (tk_kn c))) = kk -> tt_kept (tk_kd c) (kk + 1) mem mem' ->
  acstr_at SEGS (rdW W mem') (tk_kd c) (cut_text pay (tk_kn c)) ->
  tk_amem c mem' b (Attrs (Some pay) (a_alias acc)).
Proof.
  intros regs' mem mem' md' b acc pay kk HI' (HM & (B1 & B2 & B3 & B4 & B5 & B6) & HSP) Hkd Hkn Hkk UN Hcs.
  destruct (tk_kd_facts SK B c HC Hkd Hkn) as (K0 & K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8).
  destruct (tk_sp_rng SK B c HC) as (S0 & S1 & S2 & S3).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof (tt_cut_len pay (tk_kn c) Hkn) as HL.
  assert (Hk : 0 <= kk <= tk_kn c - 1) by lia.
  unfold apart_frame in K5. fold (tk_sp c) in K5.
  split; [|split].
  - apply (tt_model_kept regs' mem mem' md' (tk_kd c) (kk + 1) HI'); [unfold apart in *; lia | exact UN | exact HM].
  - refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
    + intros _ _. apply (tt_abuf_written regs' mem mem' md' _ _ (cut_text pay (tk_kn c)) HI' K8 (B1 Hkd Hkn));
        [lia | exact Hcs |].
      intros i Hi. apply UN; unfold TALK_AK, TALK_AFRAME, ESTACK in *; lia.
    + intros H0 H1. destruct (tk_ad_facts SK B c HC H0 H1) as (A0 & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
      pose proof (tk_kd_ad_apart SK B c HC Hkd Hkn H0 H1) as KA.
      unfold apart_frame in A5. fold (tk_sp c) in A5.
      apply (tt_abuf_kept regs' mem mem' md' _ _ HI' A8 (B2 H0 H1)). intros i Hi.
      apply UN; unfold apart, TALK_AK, TALK_AFRAME, ESTACK in *; lia.
    + intros p Hp _ _. cbn [a_kind] in Hp. injection Hp as <-. exact Hcs.
    + intros p Hp H0 H1. destruct (tk_ad_facts SK B c HC H0 H1) as (A0 & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
      pose proof (tk_kd_ad_apart SK B c HC Hkd Hkn H0 H1) as KA.
      unfold apart_frame in A5. fold (tk_sp c) in A5.
      pose proof (tt_cut_len p (tk_an c) H1) as HLa.
      apply (tt_acstr_kept mem mem' _ _ (B4 p Hp H0 H1)). intros i Hi.
      apply UN; unfold apart, TALK_AK, TALK_AFRAME, ESTACK in *; lia.
    + intros Hn. cbn [a_kind] in Hn. discriminate Hn.
    + intros Hn H0 H1 i Hi. destruct (tk_ad_facts SK B c HC H0 H1) as (A0 & A1 & A2 & A3 & A4 & A5 & _).
      pose proof (tk_kd_ad_apart SK B c HC Hkd Hkn H0 H1) as KA.
      unfold apart_frame in A5. fold (tk_sp c) in A5.
      rewrite <- (B6 Hn H0 H1 i Hi). apply UN; unfold apart, TALK_AK, TALK_AFRAME, ESTACK in *; lia.
  - apply (tt_spilled_kept mem mem' b (tk_kd c) (kk + 1)); [lia | exact UN | exact HSP].
Qed.

(* ---- THE ALIAS COPY ------------------------------------------------------------------------------------------------ *)
(* +0x578: a0 = alias + k; the instrumented check, `sb zero`, a5 := 4, a6 := 1, a7 := 3; to +0x598 *)
Lemma al_an : forall k regs mem md,
  tk_inv SK B c regs mem md -> getr regs 23 = w64 SHADOW_OFF ->
  getr regs 10 = w64 (tk_ad c + k) -> tk_ad c <> 0 -> 1 <= tk_an c -> 0 <= k < tk_an c ->
  (forall regs' mem' md', tk_inv SK B c regs' mem' md' -> tt_same regs regs' ->
     getr regs' 15 = w64 4 -> getr regs' 16 = w64 1 -> getr regs' 17 = w64 3 ->
     (forall x, 0 <= x < 2 ^ 64 -> x <> tk_ad c + k -> aview SEGS (w_H W) mem' x = aview SEGS (w_H W) mem x) ->
     mbyte SEGS (rdW W mem') (tk_ad c + k) = Some (zb 0) ->
     tk_goal SK B c (cfg_of regs' (BASE + TP_AS) mem' md')) ->
  tk_goal SK B c (cfg_of regs (BASE + TP_AN) mem md).
Proof.
  intros k regs mem md HI H23 H10 Had Han Hk K. unfold tk_goal in *.
  destruct (tk_ad_facts SK B c HC Had Han) as (A0 & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  pose proof HC as ((_ & HGX & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hajw & _) & _).
  pose proof HI as (HJ & _ & _ & _ & _ & _ & _ & _ & PR).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (Hd : tk_dst c (tk_ad c + k) 1) by (right; right; repeat split; lia).
  destruct (tk_dst_facts SK B c HC _ _ Hd ltac:(lia)) as (D0 & D1 & D2 & D3 & D4 & D5 & D6).
  set (xs := @nil word).
  assert (U10 : bv_unsigned (ew (tk_E c regs xs) 10) = tk_ad c + k).
  { rewrite (tk_E_reg c regs xs 10 10%bv) by (lia || reflexivity). rewrite H10. apply unsigned_lit_small. lia. }
  assert (Hw : writable_at SEGS (rdW W mem) (tk_ad c + k)).
  { apply (writable_kept (w_H W) memc mem _ (PR _)). apply (D6 (tk_ad c + k)). lia. }
  assert (HR : region_ok SEGS (tk_E c regs xs) (rdW W mem) tk_Rnul).
  { unfold region_ok, tk_Rnul. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U10. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. replace (tk_ad c + k + o) with (tk_ad c + k) by lia. exact Hw. }
  pose proof (tk_st_ok SK B LV c HC regs mem md xs TP_AN [] [tk_Rnul] [(10%nat, mkAF 0 (kHighMemEnd - 2) 0)]
    HI H23 (Forall_nil _) ltac:(vm_compute; reflexivity) ltac:(apply Forall_cons; [exact HR | apply Forall_nil]) (conj I I)
    ltac:(cbn [atoms_ok]; split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U10, Z.pow_0_r, Z.mod_1_r; lia
                                 | exact I])) as HS.
  assert (SHOK : sh_ok SEGS tk_Bx tk_SH_an (tk_E c regs xs) (rdW W mem)).
  { apply Forall_cons; [|apply Forall_nil].
    apply (tk_shent_ok _ _ 10 0 1 (tk_ad c + k)).
    - unfold tk_Bx. apply (tk_U_reg c regs xs 23 23%bv); [lia | reflexivity | exact H23 | unfold SHADOW_OFF; lia].
    - apply (tk_U_reg c regs xs 10 10%bv); [lia | reflexivity | exact H10 | lia].
    - lia.
    - unfold amem_range in D2. destruct D2 as [Q|Q]; [left | right]; lia.
    - rewrite <- (aview_rd_of SEGS). replace (tk_ad c + k + 0) with (tk_ad c + k) by lia. replace (1 - 0) with 1 by lia.
      exact (tk_ra_kept SK B c HC regs mem md (tk_ad c + k) 1 HI ltac:(lia) ltac:(lia) D4). }
  pose proof (tk_E_env c regs xs) as HEI.
  pose proof (paj_run_to_x SK B LAWS (tc_G c) HGX (tc_XO c) (tc_OUT c)) as RUNTO.
  paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_AS.
  { (* the write window: the NUL byte, a byte of the write set *)
    intros a (r & Hin & Ha). vm_compute in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U10 in Ha.
    apply Hajw. apply (D6 a). lia. }
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md1 := m) in * end.
  (* the bytes kept: all but the NUL byte *)
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun x => x = tk_ad c + k) HFr
    ltac:(intros ?bq ?wlo ?whi ?x ?Hin ?Hr; vm_compute in Hin; destruct Hin as [?Hq | []];
          injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite U10 in Hr; lia)) as UN1.
  (* the NUL *)
  pose proof (tt_region _ _ _ 0 _ HS eq_refl) as HRn. cbn [ms_mem restrict mkst] in HRn.
  lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ =>
    assert (U10' : bv_unsigned (ew E1 10) = tk_ad c + k) by (rewrite ?ew_ewset_other by lia; exact U10) end.
  assert (HN : mbyte SEGS (rdW W (ms_mem ms1)) (tk_ad c + k) = Some (zb 0)).
  { pose proof (field_of_region_any (segs := SEGS) _ _ 10%nat (tk_ad c + k) _ _ _ _ _ 0 1%N (SLit 0) HRn U10'
      (or_introl eq_refl) ltac:(lia)) as V.
    rewrite Z.add_0_r in V. exact (val_mem_nul SEGS _ _ V). }
  (* the registers *)
  lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?msr =>
    pose proof (regs_kept_of_st_ok_pi E1 ss1 msr regs (tk_ext c ++ xs) tt_KL HS
      ltac:(split; [intros ?n ?Hn; rewrite ?ew_ewset_other by lia; unfold tk_E; apply Eimg_low; unfold A_TEXT; lia
                   | reflexivity])
      ltac:(vm_compute; reflexivity)) as RK end.
  cbn [ms_regs restrict] in RK.
  tt_reg HS (15%bv : bv 5) R15. tt_reg HS (16%bv : bv 5) R16. tt_reg HS (17%bv : bv 5) R17.
  assert (HI1 : tk_inv SK B c (ms_regs ms1) (ms_mem ms1) md1).
  { apply (tk_inv_step SK B c HC regs mem md (ms_regs ms1) (ms_mem ms1) md1 (fun x => x = tk_ad c + k) HI HJ).
    - unfold md1. repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
    - unfold md1. repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
    - intros x Hx Hz. exact (UN1 x Hx Hz).
    - intros x ->. right. exact (proj1 (D6 (tk_ad c + k) ltac:(lia))).
    - intros x Hp. exact (apresent_grows _ _ _ _ HG Hp).
    - exact (RK 2%bv ltac:(tt_in)).
    - exact (RK 3%bv ltac:(tt_in)).
    - exact (RK 4%bv ltac:(tt_in)). }
  apply (K (ms_regs ms1) (ms_mem ms1) md1 HI1).
  - intros r Hr. exact (RK r Hr).
  - rewrite R15. reflexivity.
  - rewrite R16. reflexivity.
  - rewrite R17. reflexivity.
  - intros x Hx Hne. exact (UN1 x Hx Hne).
  - exact HN.
Qed.

(* +0x574 (after checked_memcpy): `add a0, s0, s2`; to +0x578 *)
Lemma al_ar : forall k regs mem md,
  tk_inv SK B c regs mem md -> getr regs 23 = w64 SHADOW_OFF ->
  getr regs 8 = w64 (tk_ad c) -> getr regs 18 = w64 k -> tk_ad c <> 0 -> 1 <= tk_an c -> 0 <= k < tk_an c ->
  (forall regs' mem' md', tk_inv SK B c regs' mem' md' -> tt_same regs regs' ->
     getr regs' 15 = w64 4 -> getr regs' 16 = w64 1 -> getr regs' 17 = w64 3 ->
     (forall x, 0 <= x < 2 ^ 64 -> x <> tk_ad c + k -> aview SEGS (w_H W) mem' x = aview SEGS (w_H W) mem x) ->
     mbyte SEGS (rdW W mem') (tk_ad c + k) = Some (zb 0) ->
     tk_goal SK B c (cfg_of regs' (BASE + TP_AS) mem' md')) ->
  tk_goal SK B c (cfg_of regs (BASE + TP_AR) mem md).
Proof.
  intros k regs mem md HI H23 H8 H18 Had Han Hk K. unfold tk_goal in *.
  destruct (tk_ad_facts SK B c HC Had Han) as (A0 & A1 & _).
  pose proof HC as ((_ & HGX & _) & _).
  pose proof HI as (HJ & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  set (xs := @nil word).
  pose proof (tk_st_ok SK B LV c HC regs mem md xs TP_AR [] [] [] HI H23 (Forall_nil _) eq_refl (Forall_nil _) I I)
    as HS.
  assert (SHOK : sh_ok SEGS tk_Bx [] (tk_E c regs xs) (rdW W mem)) by constructor.
  pose proof (tk_E_env c regs xs) as HEI.
  pose proof (paj_run_to_x SK B LAWS (tc_G c) HGX (tc_XO c) (tc_OUT c)) as RUNTO.
  assert (E8 : ew (tk_E c regs xs) 8 = w64 (tk_ad c)) by (rewrite (tk_E_reg c regs xs 8 8%bv) by (lia || reflexivity); exact H8).
  assert (E18 : ew (tk_E c regs xs) 18 = w64 k) by (rewrite (tk_E_reg c regs xs 18 18%bv) by (lia || reflexivity); exact H18).
  paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_AN; [tt_awr0 |].
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
  tt_ro HF Em1. pmkst HS. rewrite Em1 in HJ |- *.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md1 := m) in * end.
  lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?msr =>
    pose proof (regs_kept_of_st_ok_pi E1 ss1 msr regs (tk_ext c ++ xs) tt_KL HS
      ltac:(split; [intros ?n ?Hn; rewrite ?ew_ewset_other by lia; unfold tk_E; apply Eimg_low; unfold A_TEXT; lia
                   | reflexivity])
      ltac:(vm_compute; reflexivity)) as RK end.
  cbn [ms_regs restrict] in RK.
  tt_reg HS (10%bv : bv 5) R10.
  rewrite denot_lit_U, (tt_U_add _ 8 0 18 (tk_ad c) k E8 E18) in R10 by lia.
  assert (R10' : getr (ms_regs ms1) 10 = w64 (tk_ad c + k)) by (rewrite R10; unfold w64; f_equal; lia).
  assert (HI1 : tk_inv SK B c (ms_regs ms1) mem md1).
  { apply (tk_inv_step SK B c HC regs mem md (ms_regs ms1) mem md1 (fun _ => False) HI HJ).
    - unfold md1. repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
    - unfold md1. repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
    - intros x _ _. reflexivity.
    - intros x [].
    - intros x Hp. exact Hp.
    - exact (RK 2%bv ltac:(tt_in)).
    - exact (RK 3%bv ltac:(tt_in)).
    - exact (RK 4%bv ltac:(tt_in)). }
  apply (al_an k (ms_regs ms1) mem md1 HI1 ltac:(rewrite (RK 23%bv ltac:(tt_in)); exact H23) R10' Had Han Hk).
  intros regs' mem' md' HI' Hs' H15 H16 H17 UN' HN'.
  exact (K regs' mem' md' HI' (tt_same_trans _ _ _ RK Hs') H15 H16 H17 UN' HN').
Qed.

(* the call of checked_memcpy at +0x570: a0 = alias, a1 = d, a2 = s2 = kk, ra = +0x574 *)
Lemma al_call : forall kk src regs mem md,
  tk_inv SK B c regs mem md -> getr regs 23 = w64 SHADOW_OFF -> getr regs 8 = w64 (tk_ad c) ->
  getr regs 10 = w64 (tk_ad c) -> getr regs 11 = w64 src -> getr regs 12 = w64 kk -> getr regs 18 = w64 kk ->
  getr regs 1 = Z_to_bv 64 (BASE + TP_AR) -> 0 <= kk <= tk_an c - 1 -> kk < 2 ^ 32 ->
  LA_G_NL <= src -> src + kk <= LA_G_NL + NK_CHUNK_LEN -> tk_ad c <> 0 -> 1 <= tk_an c ->
  (forall regs' mem' md', tk_inv SK B c regs' mem' md' -> tt_same regs regs' ->
     getr regs' 15 = w64 4 -> getr regs' 16 = w64 1 -> getr regs' 17 = w64 3 ->
     (forall i, 0 <= i < kk -> aview SEGS (w_H W) mem' (tk_ad c + i) = aview SEGS (w_H W) mem (src + i)) ->
     tt_kept (tk_ad c) (kk + 1) mem mem' ->
     mbyte SEGS (rdW W mem') (tk_ad c + kk) = Some (zb 0) ->
     tk_goal SK B c (cfg_of regs' (BASE + TP_AS) mem' md')) ->
  tk_goal SK B c (cfg_of regs (pa_sigma LS___asan_memcpy) mem md).
Proof.
  intros kk src regs mem md HI H23 H8 H10 H11 H12 H18 H1 Hkk Hkk2 Hs0 Hs1 Had Han K. unfold tk_goal in *.
  destruct (tk_ad_facts SK B c HC Had Han) as (A0 & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HI as (_ & _ & _ & Hsp & _).
  assert (Hd : tk_dst c (tk_ad c) kk) by (right; right; repeat split; lia).
  destruct (tk_src_gnl SK B c HC regs mem md src kk HI Hsp Hs0 Hs1 ltac:(lia)) as (X0 & X1 & X2 & X3 & X4 & X5).
  eapply SRr_bind.
  { refine (tk_intrin SK B LAWS c HC OCpy _ MEMCPY regs mem md (tk_ad c) src kk (Z_to_bv 64 (BASE + TP_AR)) HI
      H10 H11 H12 ltac:(lia) Hd H1 (ret_ok_codeptr_v TP_AR ltac:(unfold TP_AR, AF_talk; lia) eq_refl) _).
    refine (conj X0 (conj X1 (conj X2 (conj _ (conj X3 (conj X4 X5)))))).
    unfold apart_gnl, LA_G_NL, NK_SIZE, NK_CHUNK_LEN in *. lia. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HI2 & HP2 & Hcp & Hout).
  cbv iota beta in Hcp.
  pose proof (tt_same_pres _ _ HP2) as Hs2.
  apply (al_ar kk regs2 mem2 md2 HI2 ltac:(rewrite (Hs2 23%bv ltac:(tt_in)); exact H23)
    ltac:(rewrite (Hs2 8%bv ltac:(tt_in)); exact H8)
    ltac:(rewrite (tt_pres _ _ HP2 18%bv ltac:(tt_cs)); exact H18) Had Han ltac:(lia)).
  intros regs' mem' md' HI' Hs' H15 H16 H17 UN' HN'.
  apply (K regs' mem' md' HI' (tt_same_trans _ _ _ Hs2 Hs') H15 H16 H17).
  - intros i Hi. rewrite (UN' (tk_ad c + i)) by lia. exact (Hcp i Hi).
  - intros x Hx Hn Hw. rewrite (UN' x Hx) by lia. apply Hout; [exact Hx | lia | exact Hw].
  - exact HN'.
Qed.

(* +0x55c: s2 := min_u (s2, alias_n - 1) (the spilled alias_n - 1), the call checked_memcpy *)
Lemma al_ca : forall k0 src b regs mem md,
  tk_inv SK B c regs mem md -> tk_rs0 c regs -> getr regs 20 = w64 b -> tk_spilled c mem b ->
  0 <= b -> b + 4 < 2 ^ 64 ->
  getr regs 11 = w64 src -> getr regs 18 = w64 k0 -> 0 <= k0 < 2 ^ 32 ->
  LA_G_NL <= src -> src + k0 <= LA_G_NL + NK_CHUNK_LEN -> tk_ad c <> 0 -> 1 <= tk_an c ->
  (forall regs' mem' md', tk_inv SK B c regs' mem' md' -> tt_same regs regs' ->
     getr regs' 15 = w64 4 -> getr regs' 16 = w64 1 -> getr regs' 17 = w64 3 ->
     (forall i, 0 <= i < Z.min k0 (tk_an c - 1) ->
        aview SEGS (w_H W) mem' (tk_ad c + i) = aview SEGS (w_H W) mem (src + i)) ->
     tt_kept (tk_ad c) (Z.min k0 (tk_an c - 1) + 1) mem mem' ->
     mbyte SEGS (rdW W mem') (tk_ad c + Z.min k0 (tk_an c - 1)) = Some (zb 0) ->
     tk_goal SK B c (cfg_of regs' (BASE + TP_AS) mem' md')) ->
  tk_goal SK B c (cfg_of regs (BASE + TP_CA) mem md).
Proof.
  intros k0 src b regs mem md HI (H8 & H9 & H23) H20 HSP Hb0 Hb1 H11 H18 Hk0 Hs0 Hs1 Had Han K.
  destruct (tk_ad_facts SK B c HC Had Han) as (A0 & A1 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HC as ((_ & HGX & _) & _).
  pose proof HI as (HJ & _).
  set (xs := @nil word).
  pose proof (tk_st_ok SK B LV c HC regs mem md xs TP_CA [] [tk_frs] [] HI H23 (Forall_nil _)
    ltac:(vm_compute; reflexivity)
    ltac:(apply Forall_cons; [exact (tk_frs_ok SK B c HC regs mem md xs b HI HSP H20 Hb0 Hb1) | apply Forall_nil]) (conj I I) I) as HS.
  assert (SHOK : sh_ok SEGS tk_Bx [] (tk_E c regs xs) (rdW W mem)) by constructor.
  pose proof (tk_E_env c regs xs) as HEI.
  pose proof (paj_run_x SK B LAWS (tc_G c) HGX (tc_XO c) (tc_OUT c)) as RUN.
  pose proof (paj_branch (PI := PI)) as BR.
  assert (E18 : ew (tk_E c regs xs) 18 = w64 k0)
    by (rewrite (tk_E_reg c regs xs 18 18%bv) by (lia || reflexivity); exact H18).
  assert (E45 : ew (tk_E c regs xs) 45 = w64 (tk_an c - 1)) by exact (tk_E_ext c regs xs 13 ltac:(lia)).
  unfold tk_goal in *.
  (* +0x55c..+0x560: a0 := alias_n - 1; `bltu s2, a0` *)
  paj_run_tok RUN HS HJ SHOK tk_span; [tt_awr0 |].
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
  tt_ro HF Em1. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK tk_span;
    rewrite branch_ltu_U, (U_atom _ 18 k0 E18 ltac:(lia)), (U_atom _ 45 (tk_an c - 1) E45 ltac:(lia)) in Hc.
  - (* k0 < alias_n - 1: s2 = k0 *)
    apply Z.ltb_lt in Hc.
    paj_run_tok RUN HS HJ SHOK tk_span; [tt_awr0 |].
    lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => rename m into ms2 end.
    tt_ro HF Em2. pmkst HS. rewrite Em2, Em1 in HJ |- *.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md2 := m) in * end.
    lazymatch type of HS with st_ok _ ?E1 ?ss1 ?msr =>
      pose proof (regs_kept_of_st_ok SEGS E1 ss1 msr regs (tk_ext c ++ xs) tt_KL HS
        ltac:(split; [intros ?n ?Hn; rewrite ?ew_ewset_other by lia; unfold tk_E; apply Eimg_low; unfold A_TEXT; lia
                     | reflexivity])
        ltac:(vm_compute; reflexivity)) as RK end.
    cbn [ms_regs restrict] in RK.
    tt_reg HS (1%bv : bv 5) R1. tt_reg HS (10%bv : bv 5) R10. tt_reg HS (11%bv : bv 5) R11.
    tt_reg HS (12%bv : bv 5) R12. tt_reg HS (18%bv : bv 5) R18.
    rewrite (tt_den regs xs 8 8%bv) in R10 by (lia || reflexivity).
    rewrite (tt_den regs xs 11 11%bv) in R11 by (lia || reflexivity).
    rewrite (tt_den regs xs 18 18%bv) in R12 by (lia || reflexivity).
    rewrite (tt_den regs xs 18 18%bv) in R18 by (lia || reflexivity).
    assert (HI2 : tk_inv SK B c (ms_regs ms2) mem md2).
    { apply (tk_inv_step SK B c HC regs mem md (ms_regs ms2) mem md2 (fun _ => False) HI HJ).
      - unfold md2. repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
      - unfold md2. repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
      - intros x _ _. reflexivity.
      - intros x [].
      - intros x Hp. exact Hp.
      - exact (RK 2%bv ltac:(tt_in)).
      - exact (RK 3%bv ltac:(tt_in)).
      - exact (RK 4%bv ltac:(tt_in)). }
    replace (Z.min k0 (tk_an c - 1)) with k0 in K by lia.
    apply (al_call k0 src (ms_regs ms2) mem md2 HI2 ltac:(rewrite (RK 23%bv ltac:(tt_in)); exact H23)
      ltac:(rewrite (RK 8%bv ltac:(tt_in)); exact H8) ltac:(rewrite R10; exact H8) ltac:(rewrite R11; exact H11)
      ltac:(rewrite R12; exact H18) ltac:(rewrite R18; exact H18)
      ltac:(rewrite R1; exact (codeptr_val _ 23012 HEI)) ltac:(lia) ltac:(lia) Hs0 Hs1 Had Han).
    intros regs' mem' md' HI' Hs' H15 H16 H17 Hcp UN HN.
    exact (K regs' mem' md' HI' (tt_same_trans _ _ _ RK Hs') H15 H16 H17 Hcp UN HN).
  - (* k0 >= alias_n - 1: s2 := alias_n - 1 *)
    apply Z.ltb_ge in Hc.
    paj_run_tok RUN HS HJ SHOK tk_span; [tt_awr0 |].
    lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => rename m into ms2 end.
    tt_ro HF Em2. pmkst HS. rewrite Em2, Em1 in HJ |- *.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md2 := m) in * end.
    lazymatch type of HS with st_ok _ ?E1 ?ss1 ?msr =>
      pose proof (regs_kept_of_st_ok SEGS E1 ss1 msr regs (tk_ext c ++ xs) tt_KL HS
        ltac:(split; [intros ?n ?Hn; rewrite ?ew_ewset_other by lia; unfold tk_E; apply Eimg_low; unfold A_TEXT; lia
                     | reflexivity])
        ltac:(vm_compute; reflexivity)) as RK end.
    cbn [ms_regs restrict] in RK.
    tt_reg HS (1%bv : bv 5) R1. tt_reg HS (10%bv : bv 5) R10. tt_reg HS (11%bv : bv 5) R11.
    tt_reg HS (12%bv : bv 5) R12. tt_reg HS (18%bv : bv 5) R18.
    rewrite (tt_den regs xs 8 8%bv) in R10 by (lia || reflexivity).
    rewrite (tt_den regs xs 11 11%bv) in R11 by (lia || reflexivity).
    assert (V45 : sv_denot (tk_E c regs xs) (SOff 45 0) = w64 (tk_an c - 1)).
    { rewrite denot_lit_U, (U_atom _ 45 (tk_an c - 1) E45 ltac:(lia)). reflexivity. }
    rewrite V45 in R12, R18.
    assert (HI2 : tk_inv SK B c (ms_regs ms2) mem md2).
    { apply (tk_inv_step SK B c HC regs mem md (ms_regs ms2) mem md2 (fun _ => False) HI HJ).
      - unfold md2. repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
      - unfold md2. repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
      - intros x _ _. reflexivity.
      - intros x [].
      - intros x Hp. exact Hp.
      - exact (RK 2%bv ltac:(tt_in)).
      - exact (RK 3%bv ltac:(tt_in)).
      - exact (RK 4%bv ltac:(tt_in)). }
    replace (Z.min k0 (tk_an c - 1)) with (tk_an c - 1) in K by lia.
    apply (al_call (tk_an c - 1) src (ms_regs ms2) mem md2 HI2 ltac:(rewrite (RK 23%bv ltac:(tt_in)); exact H23)
      ltac:(rewrite (RK 8%bv ltac:(tt_in)); exact H8) ltac:(rewrite R10; exact H8) ltac:(rewrite R11; exact H11)
      R12 R18 ltac:(rewrite R1; exact (codeptr_val _ 23012 HEI)) ltac:(lia) ltac:(lia) Hs0 ltac:(lia) Had Han).
    intros regs' mem' md' HI' Hs' H15 H16 H17 Hcp UN HN.
    exact (K regs' mem' md' HI' (tt_same_trans _ _ _ RK Hs') H15 H16 H17 Hcp UN HN).
Qed.

(* +0x3b8: one byte of the NUL scan; a1 = d, a2 = n, s2 = k, a3 = d + k *)
Lemma al_sa_step : forall pay src n mem,
  Z.of_nat (length pay) = n ->
  (forall i, 0 <= i < n -> mbyte SEGS (rdW W mem) (src + i) = nth_error pay (Z.to_nat i)) ->
  LA_G_NL <= src -> src + n <= LA_G_NL + NK_CHUNK_LEN ->
  forall k regs md, 0 <= k < n -> (Z.to_nat k <= nul_at pay)%nat ->
  tk_inv SK B c regs mem md -> getr regs 23 = w64 SHADOW_OFF ->
  getr regs 11 = w64 src -> getr regs 12 = w64 n -> getr regs 18 = w64 k -> getr regs 13 = w64 (src + k) ->
  (k + 1 < n -> (Z.to_nat (k + 1) <= nul_at pay)%nat -> forall regs1 md1, tk_inv SK B c regs1 mem md1 ->
     tt_same regs regs1 -> getr regs1 11 = w64 src -> getr regs1 12 = w64 n -> getr regs1 18 = w64 (k + 1) ->
     getr regs1 13 = w64 (src + (k + 1)) -> tk_goal SK B c (cfg_of regs1 (BASE + TP_SA) mem md1)) ->
  (forall regs' md', tk_inv SK B c regs' mem md' -> tt_same regs regs' -> getr regs' 11 = w64 src ->
     getr regs' 18 = w64 (Z.of_nat (nul_at pay)) -> tk_goal SK B c (cfg_of regs' (BASE + TP_CA) mem md')) ->
  tk_goal SK B c (cfg_of regs (BASE + TP_SA) mem md).
Proof.
  intros pay src n mem Hlen Hby Hsr0 Hsr1 k regs md Hk Hnul HI H23 H11 H12 H18 H13 KS KC.
  unfold tk_goal in *. unfold LA_G_NL, NK_CHUNK_LEN in Hsr0, Hsr1.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HC as ((_ & HGX & _) & _).
  pose proof HI as (HJ & _).
  destruct (nth_error pay (Z.to_nat k)) as [bb|] eqn:Eb; [|apply nth_error_None in Eb; lia].
  pose proof (Hby k ltac:(lia)) as Hm. rewrite Eb in Hm.
  pose proof (tw_byte_range bb) as Rb.
  set (xs := [w64 (bz bb)]).
  assert (U13 : bv_unsigned (ew (tk_E c regs xs) 13) = src + k).
  { rewrite (tk_E_reg c regs xs 13 13%bv) by (lia || reflexivity). rewrite H13. apply unsigned_lit_small.
    unfold LA_G_NL, NK_CHUNK_LEN in *. lia. }
  assert (E49 : ew (tk_E c regs xs) 49 = w64 (bz bb)) by exact (tk_E_xs c regs xs 0 ltac:(lia)).
  assert (U49 : bv_unsigned (ew (tk_E c regs xs) 49) = bz bb) by (rewrite E49; apply unsigned_lit_small; lia).
  assert (HR : region_ok SEGS (tk_E c regs xs) (rdW W mem)
                 (YP09.mkRegion (Some 13%nat) 0 1 0 0 [tk_ch 0 1 (SOff 49 0)])).
  { unfold region_ok, tk_ch. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U13. split; [lia|]. split; [unfold LA_G_NL, NK_CHUNK_LEN in *; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ (src + k) 0 1 (SOff 49 0) (bz bb)).
    - cbn [sv_denot]. rewrite U49, Z.add_0_r. reflexivity.
    - change (2 ^ (8 * Z.of_N 1)) with 256. lia.
    - lia.
    - rewrite Z.add_0_r. exact (tt_val1 _ _ _ Hm). }
  pose proof (tk_st_ok SK B LV c HC regs mem md xs TP_SA [] [YP09.mkRegion (Some 13%nat) 0 1 0 0 [tk_ch 0 1 (SOff 49 0)]]
    [(13%nat, mkAF LA_G_NL (LA_G_NL + NK_CHUNK_LEN - 1) 0); (49%nat, mkAF 0 255 0)] HI H23 (Forall_nil _)
    ltac:(vm_compute; reflexivity) ltac:(apply Forall_cons; [exact HR | apply Forall_nil]) (conj I I)
    ltac:(cbn [atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U13, U49, !Z.pow_0_r, !Z.mod_1_r;
          unfold LA_G_NL, NK_CHUNK_LEN in *; repeat split; lia)) as HS.
  assert (SHOK : sh_ok SEGS tk_Bx tk_SH_sa (tk_E c regs xs) (rdW W mem)).
  { apply Forall_cons; [|apply Forall_nil].
    apply (tk_shent_ok _ _ 13 0 8 (src + k)).
    - unfold tk_Bx. apply (tk_U_reg c regs xs 23 23%bv); [lia | reflexivity | exact H23 | unfold SHADOW_OFF; lia].
    - apply (tk_U_reg c regs xs 13 13%bv); [lia | reflexivity | exact H13 | unfold LA_G_NL, NK_CHUNK_LEN in *; lia].
    - lia.
    - left. unfold LA_G_NL, NK_CHUNK_LEN in *. lia.
    - apply (tt_ra_gnl regs mem md HI); unfold LA_G_NL, NK_CHUNK_LEN, NK_N_CHUNKS in *; lia. }
  pose proof (tk_E_env c regs xs) as HEI.
  pose proof (paj_run_x SK B LAWS (tc_G c) HGX (tc_XO c) (tc_OUT c)) as RUN.
  pose proof (paj_run_to_x SK B LAWS (tc_G c) HGX (tc_XO c) (tc_OUT c)) as RUNTO.
  pose proof (paj_branch (PI := PI)) as BR.
  assert (E11 : ew (tk_E c regs xs) 11 = w64 src)
    by (rewrite (tk_E_reg c regs xs 11 11%bv) by (lia || reflexivity); exact H11).
  assert (E12 : ew (tk_E c regs xs) 12 = w64 n)
    by (rewrite (tk_E_reg c regs xs 12 12%bv) by (lia || reflexivity); exact H12).
  assert (E18 : ew (tk_E c regs xs) 18 = w64 k)
    by (rewrite (tk_E_reg c regs xs 18 18%bv) by (lia || reflexivity); exact H18).
  (* the instrumented check of d[k], `lbu`, `beqz` *)
  paj_run_tok RUN HS HJ SHOK tk_span; [tt_awr0 |].
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
  tt_ro HF Em1. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK tk_span;
    rewrite branch_eq_U, (U_atom _ 49 (bz bb) E49 ltac:(lia)), (tt_U_lit _ 0 ltac:(lia)) in Hc.
  - (* d[k] = 0: the clamp with s2 = k *)
    apply Z.eqb_eq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_CA; [tt_awr0 |].
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms2 end.
    tt_ro HF Em2. pmkst HS. rewrite Em2, Em1 in HJ |- *.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md2 := m) in * end.
    lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?msr =>
      pose proof (regs_kept_of_st_ok_pi E1 ss1 msr regs (tk_ext c ++ xs) tt_KL HS
        ltac:(split; [intros ?n ?Hn; rewrite ?ew_ewset_other by lia; unfold tk_E; apply Eimg_low; unfold A_TEXT; lia
                     | reflexivity])
        ltac:(vm_compute; reflexivity)) as RK end.
    cbn [ms_regs restrict] in RK.
    tt_reg HS (11%bv : bv 5) R11. tt_reg HS (18%bv : bv 5) R18.
    rewrite (tt_den regs xs 11 11%bv) in R11 by (lia || reflexivity).
    rewrite (tt_den regs xs 18 18%bv) in R18 by (lia || reflexivity).
    assert (HI2 : tk_inv SK B c (ms_regs ms2) mem md2).
    { apply (tk_inv_step SK B c HC regs mem md (ms_regs ms2) mem md2 (fun _ => False) HI HJ).
      - unfold md2. repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
      - unfold md2. repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
      - intros x _ _. reflexivity.
      - intros x [].
      - intros x Hp. exact Hp.
      - exact (RK 2%bv ltac:(tt_in)).
      - exact (RK 3%bv ltac:(tt_in)).
      - exact (RK 4%bv ltac:(tt_in)). }
    apply (KC (ms_regs ms2) md2 HI2 RK); [rewrite R11; exact H11 |].
    rewrite R18, H18, (tt_scan_hit pay k bb ltac:(lia) Hnul Eb Hc). reflexivity.
  - (* d[k] <> 0: s2 := k + 1, `bne a2, s2` *)
    apply Z.eqb_neq in Hc.
    pose proof (tt_scan_go pay k bb ltac:(lia) Hnul Eb Hc) as Hnul1. rename Hc into Hbz.
    paj_run_tok RUN HS HJ SHOK tk_span; [tt_awr0 |].
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms2 end.
    tt_ro HF Em2. clear HF HFr HG.
    psrr_branch_tok RUN BR HS SHOK tk_span;
      rewrite branch_ne_U, (U_atom _ 12 n E12 ltac:(lia)), (U_atom_off _ 18 k 1 E18 ltac:(lia) ltac:(lia)) in Hc.
    + (* k + 1 <> n: the next byte *)
      apply negb_true_iff, Z.eqb_neq in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_SA; [tt_awr0 |].
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms3 end.
      tt_ro HF Em3. pmkst HS. rewrite Em3, Em2, Em1 in HJ |- *.
      lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md3 := m) in * end.
      lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?msr =>
        pose proof (regs_kept_of_st_ok_pi E1 ss1 msr regs (tk_ext c ++ xs) tt_KL HS
          ltac:(split; [intros ?n ?Hn; rewrite ?ew_ewset_other by lia; unfold tk_E; apply Eimg_low; unfold A_TEXT; lia
                       | reflexivity])
          ltac:(vm_compute; reflexivity)) as RK end.
      cbn [ms_regs restrict] in RK.
      tt_reg HS (11%bv : bv 5) R11. tt_reg HS (12%bv : bv 5) R12. tt_reg HS (18%bv : bv 5) R18.
      tt_reg HS (13%bv : bv 5) R13.
      rewrite (tt_den regs xs 11 11%bv) in R11 by (lia || reflexivity).
      rewrite (tt_den regs xs 12 12%bv) in R12 by (lia || reflexivity).
      rewrite denot_lit_U, (U_atom_off _ 18 k 1 E18 ltac:(lia) ltac:(lia)) in R18.
      rewrite denot_lit_U, (tt_U_add _ 11 1 18 src k E11 E18) in R13 by (unfold LA_G_NL, NK_CHUNK_LEN in *; lia).
      assert (HI3 : tk_inv SK B c (ms_regs ms3) mem md3).
      { apply (tk_inv_step SK B c HC regs mem md (ms_regs ms3) mem md3 (fun _ => False) HI HJ).
        - unfold md3. repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
        - unfold md3. repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
        - intros x _ _. reflexivity.
        - intros x [].
        - intros x Hp. exact Hp.
        - exact (RK 2%bv ltac:(tt_in)).
        - exact (RK 3%bv ltac:(tt_in)).
        - exact (RK 4%bv ltac:(tt_in)). }
      apply (KS ltac:(lia) Hnul1 (ms_regs ms3) md3 HI3 RK).
      * rewrite R11. exact H11.
      * rewrite R12. exact H12.
      * rewrite R18. reflexivity.
      * rewrite R13. unfold w64. f_equal. lia.
    + (* k + 1 = n: the clamp with s2 = n *)
      apply negb_false_iff, Z.eqb_eq in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_CA; [tt_awr0 |].
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms3 end.
      tt_ro HF Em3. pmkst HS. rewrite Em3, Em2, Em1 in HJ |- *.
      lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md3 := m) in * end.
      lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?msr =>
        pose proof (regs_kept_of_st_ok_pi E1 ss1 msr regs (tk_ext c ++ xs) tt_KL HS
          ltac:(split; [intros ?n ?Hn; rewrite ?ew_ewset_other by lia; unfold tk_E; apply Eimg_low; unfold A_TEXT; lia
                       | reflexivity])
          ltac:(vm_compute; reflexivity)) as RK end.
      cbn [ms_regs restrict] in RK.
      tt_reg HS (11%bv : bv 5) R11. tt_reg HS (18%bv : bv 5) R18.
      rewrite (tt_den regs xs 11 11%bv) in R11 by (lia || reflexivity).
      rewrite (tt_den regs xs 12 12%bv) in R18 by (lia || reflexivity).
      assert (HI3 : tk_inv SK B c (ms_regs ms3) mem md3).
      { apply (tk_inv_step SK B c HC regs mem md (ms_regs ms3) mem md3 (fun _ => False) HI HJ).
        - unfold md3. repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
        - unfold md3. repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
        - intros x _ _. reflexivity.
        - intros x [].
        - intros x Hp. exact Hp.
        - exact (RK 2%bv ltac:(tt_in)).
        - exact (RK 3%bv ltac:(tt_in)).
        - exact (RK 4%bv ltac:(tt_in)). }
      apply (KC (ms_regs ms3) md3 HI3 RK); [rewrite R11; exact H11 |].
      rewrite R18, H12, (tt_scan_end pay n Hlen ltac:(lia)). reflexivity.
Qed.

(* the NUL scan from byte k, by induction on n - k *)
Lemma al_sa : forall pay src n mem,
  Z.of_nat (length pay) = n ->
  (forall i, 0 <= i < n -> mbyte SEGS (rdW W mem) (src + i) = nth_error pay (Z.to_nat i)) ->
  LA_G_NL <= src -> src + n <= LA_G_NL + NK_CHUNK_LEN ->
  forall (f : nat) k regs md, (Z.to_nat (n - k) <= f)%nat -> 0 <= k < n -> (Z.to_nat k <= nul_at pay)%nat ->
  tk_inv SK B c regs mem md -> getr regs 23 = w64 SHADOW_OFF ->
  getr regs 11 = w64 src -> getr regs 12 = w64 n -> getr regs 18 = w64 k -> getr regs 13 = w64 (src + k) ->
  (forall regs' md', tk_inv SK B c regs' mem md' -> tt_same regs regs' -> getr regs' 11 = w64 src ->
     getr regs' 18 = w64 (Z.of_nat (nul_at pay)) -> tk_goal SK B c (cfg_of regs' (BASE + TP_CA) mem md')) ->
  tk_goal SK B c (cfg_of regs (BASE + TP_SA) mem md).
Proof.
  intros pay src n mem Hlen Hby Hsr0 Hsr1 f. induction f as [|f IH];
    intros k regs md Hf Hk Hnul HI H23 H11 H12 H18 H13 KC; [lia|].
  apply (al_sa_step pay src n mem Hlen Hby Hsr0 Hsr1 k regs md Hk Hnul HI H23 H11 H12 H18 H13); [|exact KC].
  intros Hk1 Hnul1 regs1 md1 HI1 Hs1 H11' H12' H18' H13'.
  apply (IH (k + 1) regs1 md1 ltac:(lia) ltac:(lia) Hnul1 HI1
    ltac:(rewrite (Hs1 23%bv ltac:(tt_in)); exact H23) H11' H12' H18' H13').
  intros regs' md' HI' Hs' H11'' H18''. exact (KC regs' md' HI' (tt_same_trans _ _ _ Hs1 Hs') H11'' H18'').
Qed.

(* from the clamp's continuation to the attribute step: the alias buffer holds the cut text *)
Lemma al_fin : forall ci a al l acc regs mem md regs' mem' md',
  TK_A598 SK B c ci a al l (Attrs (a_kind acc) (Some (slice (tk_ck c ci) (a + RTA_HDR) (l - RTA_HDR)))) ->
  tk_inv SK B c regs mem md -> tk_rs0 c regs -> tk_rat regs (tk_b ci) a al -> getr regs 21 = w64 l ->
  tk_amem c mem (tk_b ci) acc -> tk_ad c <> 0 -> 1 <= tk_an c ->
  0 <= ci < tk_nch c -> 0 <= a -> 4 <= l <= al -> a + al <= Z.of_nat (length (tk_ck c ci)) ->
  tk_inv SK B c regs' mem' md' -> tt_same regs regs' ->
  getr regs' 15 = w64 4 -> getr regs' 16 = w64 1 -> getr regs' 17 = w64 3 ->
  (forall i, 0 <= i < Z.min (Z.of_nat (nul_at (slice (tk_ck c ci) (a + RTA_HDR) (l - RTA_HDR)))) (tk_an c - 1) ->
     aview SEGS (w_H W) mem' (tk_ad c + i) = aview SEGS (w_H W) mem (tk_b ci + 4 + a + i)) ->
  tt_kept (tk_ad c) (Z.min (Z.of_nat (nul_at (slice (tk_ck c ci) (a + RTA_HDR) (l - RTA_HDR)))) (tk_an c - 1) + 1)
    mem mem' ->
  mbyte SEGS (rdW W mem')
    (tk_ad c + Z.min (Z.of_nat (nul_at (slice (tk_ck c ci) (a + RTA_HDR) (l - RTA_HDR)))) (tk_an c - 1)) =
    Some (zb 0) ->
  tk_goal SK B c (cfg_of regs' (BASE + TP_AS) mem' md').
Proof.
  intros ci a al l acc regs mem md regs' mem' md' K598 HI Hrs0 Hrat H21 Ham Had Han Hci Ha Hl Hal
    HI' Hs H15 H16 H17 Hcp UN HN.
  destruct (tt_chunk ci Hci) as (Hcl & Hcl2 & Hnc).
  destruct (tk_ad_facts SK B c HC Had Han) as (A0 & A1 & _). unfold kHighMemEnd in A1.
  pose proof HC as (_ & _ & _ & _ & HNW & _).
  apply (K598 regs' mem' md' HI').
  - exact (tt_rs0_same _ _ Hs Hrs0).
  - exact (tt_rat_same _ _ _ _ _ Hs Hrat H15 H16 H17).
  - rewrite (Hs 21%bv ltac:(tt_in)). exact H21.
  - apply (tt_amem_alias regs' mem mem' md' _ acc _ _ HI' Ham Had Han (tt_cut_len _ _ Han) UN).
    unfold tk_nch, tk_ck in *.
    apply (acstr_take SEGS (w_H W) mem mem' LA_G_NL kbs ci a l (tk_ad c) (tk_an c)
      (tk_nlk_kept SK B c HC regs mem md HI) HNW Hci Ha ltac:(lia) ltac:(lia) Han ltac:(lia) ltac:(lia)).
    + intros i Hi. rewrite (Hcp i Hi). unfold tk_b, NL_CHUNK_MAX. f_equal. lia.
    + exact HN.
Qed.

(* THE PIECE: take_text into the alias buffer, +0x3a0 .. +0x594 *)
Lemma tk_take_al_ok : TK_TAKE_AL SK B c.
Proof.
  intros ci a al l acc K598 regs mem md HI Hrs0 Hrat H21 Ham Had Han0 Hci Ha Hl Hal.
  pose proof (tt_an_pos Han0) as Han.
  destruct (tt_chunk ci Hci) as (Hcl & Hcl2 & Hnc). unfold NL_CHUNK_MAX, NL_CHUNKS in Hcl2, Hnc.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HC as ((_ & HGX & _) & _).
  pose proof HI as (HJ & _).
  pose proof Hrs0 as (H8 & H9 & H23). pose proof Hrat as (H20 & H27 & H22 & H19 & H15 & H16 & H17).
  pose proof Ham as (_ & _ & HSP).
  assert (Hb : tk_b ci = LA_G_NL + 4096 * ci) by (unfold tk_b, NL_CHUNK_MAX; ring).
  assert (HbR : 0x5dcac0 <= tk_b ci /\ tk_b ci + 4096 <= 0x5dcac0 + 262144)
    by (rewrite Hb; unfold LA_G_NL, NL_CHUNKS in *; lia).
  assert (Hlen : Z.of_nat (length (slice (tk_ck c ci) (a + RTA_HDR) (l - RTA_HDR))) = l - 4)
    by (rewrite (tt_pay_len (tk_ck c ci) a l Ha ltac:(lia) ltac:(lia)); lia).
  pose proof (nul_at_le (slice (tk_ck c ci) (a + RTA_HDR) (l - RTA_HDR))) as Hnl.
  set (xs := @nil word).
  pose proof (tk_st_ok SK B LV c HC regs mem md xs TP_TA [] [tk_frs] [] HI H23 (Forall_nil _)
    ltac:(vm_compute; reflexivity)
    ltac:(apply Forall_cons; [exact (tk_frs_ok SK B c HC regs mem md xs (tk_b ci) HI HSP H20 ltac:(lia) ltac:(lia)) | apply Forall_nil])
    (conj I I) I) as HS.
  assert (SHOK : sh_ok SEGS tk_Bx [] (tk_E c regs xs) (rdW W mem)) by constructor.
  pose proof (tk_E_env c regs xs) as HEI.
  pose proof (paj_run_x SK B LAWS (tc_G c) HGX (tc_XO c) (tc_OUT c)) as RUN.
  pose proof (paj_run_to_x SK B LAWS (tc_G c) HGX (tc_XO c) (tc_OUT c)) as RUNTO.
  pose proof (paj_branch (PI := PI)) as BR.
  assert (E20 : ew (tk_E c regs xs) 20 = w64 (tk_b ci))
    by (rewrite (tk_E_reg c regs xs 20 20%bv) by (lia || reflexivity); exact H20).
  assert (E21 : ew (tk_E c regs xs) 21 = w64 l)
    by (rewrite (tk_E_reg c regs xs 21 21%bv) by (lia || reflexivity); exact H21).
  assert (E27 : ew (tk_E c regs xs) 27 = w64 a)
    by (rewrite (tk_E_reg c regs xs 27 27%bv) by (lia || reflexivity); exact H27).
  assert (Usrc : U (tk_E c regs xs) (SAlu ALU_ADD (SOff 20 4) (SOff 27 0)) = tk_b ci + 4 + a).
  { apply (tt_U_add _ 20 4 27 (tk_b ci) a E20 E27); unfold NL_CHUNK_MAX, NL_CHUNKS, LA_G_NL in *; lia. }
  unfold tk_goal in *.
  (* +0x3a0..+0x3b0: a2 := l - 4, a1 := b + 4 + a, s2 := 0, `beqz a2` *)
  paj_run_tok RUN HS HJ SHOK tk_span; [tt_awr0 |].
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
  tt_ro HF Em1. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK tk_span;
    rewrite branch_eq_U, (U_atom_off _ 21 l (-4) E21 ltac:(lia) ltac:(lia)), (tt_U_lit _ 0 ltac:(lia)) in Hc.
  - (* n = 0: the clamp with s2 = 0 *)
    apply Z.eqb_eq in Hc.
    assert (Hn0 : Z.of_nat (nul_at (slice (tk_ck c ci) (a + RTA_HDR) (l - RTA_HDR))) = 0) by lia.
    paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_CA; [tt_awr0 |].
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms2 end.
    tt_ro HF Em2. pmkst HS. rewrite Em2, Em1 in HJ |- *.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md2 := m) in * end.
    lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?msr =>
      pose proof (regs_kept_of_st_ok_pi E1 ss1 msr regs (tk_ext c ++ xs) tt_KL HS
        ltac:(split; [intros ?n ?Hn; rewrite ?ew_ewset_other by lia; unfold tk_E; apply Eimg_low; unfold A_TEXT; lia
                     | reflexivity])
        ltac:(vm_compute; reflexivity)) as RK end.
    cbn [ms_regs restrict] in RK.
    tt_reg HS (11%bv : bv 5) R11. tt_reg HS (18%bv : bv 5) R18.
    rewrite denot_lit_U, Usrc in R11.
    assert (HI2 : tk_inv SK B c (ms_regs ms2) mem md2).
    { apply (tk_inv_step SK B c HC regs mem md (ms_regs ms2) mem md2 (fun _ => False) HI HJ).
      - unfold md2. repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
      - unfold md2. repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
      - intros x _ _. reflexivity.
      - intros x [].
      - intros x Hp. exact Hp.
      - exact (RK 2%bv ltac:(tt_in)).
      - exact (RK 3%bv ltac:(tt_in)).
      - exact (RK 4%bv ltac:(tt_in)). }
    apply (al_ca (Z.of_nat (nul_at (slice (tk_ck c ci) (a + RTA_HDR) (l - RTA_HDR)))) (tk_b ci + 4 + a) (tk_b ci)
      (ms_regs ms2) mem md2 HI2 (tt_rs0_same _ _ RK Hrs0) ltac:(rewrite (RK 20%bv ltac:(tt_in)); exact H20) HSP
      ltac:(lia) ltac:(unfold NL_CHUNK_MAX, NL_CHUNKS, LA_G_NL in *; lia) R11
      ltac:(rewrite R18, Hn0; reflexivity) ltac:(lia) ltac:(unfold LA_G_NL in *; lia)
      ltac:(unfold NL_CHUNK_MAX, NL_CHUNKS, NK_CHUNK_LEN, LA_G_NL in *; lia) Had Han).
    intros regs' mem' md' HI' Hs' H15' H16' H17' Hcp UN HN.
    exact (al_fin ci a al l acc regs mem md regs' mem' md' K598 HI Hrs0 Hrat H21 Ham Had Han Hci Ha Hl Hal HI'
      (tt_same_trans _ _ _ RK Hs') H15' H16' H17' Hcp UN HN).
  - (* n > 0: the NUL scan from k = 0 *)
    apply Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_SA; [tt_awr0 |].
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms2 end.
    tt_ro HF Em2. pmkst HS. rewrite Em2, Em1 in HJ |- *.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md2 := m) in * end.
    lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?msr =>
      pose proof (regs_kept_of_st_ok_pi E1 ss1 msr regs (tk_ext c ++ xs) tt_KL HS
        ltac:(split; [intros ?n ?Hn; rewrite ?ew_ewset_other by lia; unfold tk_E; apply Eimg_low; unfold A_TEXT; lia
                     | reflexivity])
        ltac:(vm_compute; reflexivity)) as RK end.
    cbn [ms_regs restrict] in RK.
    tt_reg HS (11%bv : bv 5) R11. tt_reg HS (12%bv : bv 5) R12. tt_reg HS (18%bv : bv 5) R18.
    tt_reg HS (13%bv : bv 5) R13.
    rewrite denot_lit_U, Usrc in R11, R13.
    rewrite denot_lit_U, (U_atom_off _ 21 l (-4) E21 ltac:(lia) ltac:(lia)) in R12.
    assert (HI2 : tk_inv SK B c (ms_regs ms2) mem md2).
    { apply (tk_inv_step SK B c HC regs mem md (ms_regs ms2) mem md2 (fun _ => False) HI HJ).
      - unfold md2. repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
      - unfold md2. repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
      - intros x _ _. reflexivity.
      - intros x [].
      - intros x Hp. exact Hp.
      - exact (RK 2%bv ltac:(tt_in)).
      - exact (RK 3%bv ltac:(tt_in)).
      - exact (RK 4%bv ltac:(tt_in)). }
    apply (al_sa (slice (tk_ck c ci) (a + RTA_HDR) (l - RTA_HDR)) (tk_b ci + 4 + a) (l - 4) mem Hlen
      (tt_pay_mem regs mem md ci a l HI Hci Ha ltac:(lia) ltac:(lia)) ltac:(unfold LA_G_NL in *; lia)
      ltac:(unfold NL_CHUNK_MAX, NL_CHUNKS, NK_CHUNK_LEN, LA_G_NL in *; lia)
      (Z.to_nat (l - 4)) 0 (ms_regs ms2) md2 ltac:(lia) ltac:(lia) ltac:(lia) HI2
      ltac:(rewrite (RK 23%bv ltac:(tt_in)); exact H23) R11 R12 R18 ltac:(rewrite R13; unfold w64; f_equal; lia)).
    intros regs3 md3 HI3 Hs3 H11' H18'.
    pose proof (tt_same_trans _ _ _ RK Hs3) as Hs03.
    apply (al_ca (Z.of_nat (nul_at (slice (tk_ck c ci) (a + RTA_HDR) (l - RTA_HDR)))) (tk_b ci + 4 + a) (tk_b ci)
      regs3 mem md3 HI3 (tt_rs0_same _ _ Hs03 Hrs0) ltac:(rewrite (Hs03 20%bv ltac:(tt_in)); exact H20) HSP
      ltac:(lia) ltac:(unfold NL_CHUNK_MAX, NL_CHUNKS, LA_G_NL in *; lia) H11' H18' ltac:(lia)
      ltac:(unfold LA_G_NL in *; lia) ltac:(unfold NL_CHUNK_MAX, NL_CHUNKS, NK_CHUNK_LEN, LA_G_NL in *; lia) Had Han).
    intros regs' mem' md' HI' Hs' H15' H16' H17' Hcp UN HN.
    exact (al_fin ci a al l acc regs mem md regs' mem' md' K598 HI Hrs0 Hrat H21 Ham Had Han Hci Ha Hl Hal HI'
      (tt_same_trans _ _ _ Hs03 Hs') H15' H16' H17' Hcp UN HN).
Qed.

(* ---- THE KIND COPY (the same code at +0x47c .. +0x500, into the kind buffer s1, cap - 1 at sp + 0x18) ------- *)
(* +0x4e4: a0 = kind + k; the instrumented check, `sb zero`, a5 := 4, a6 := 1, a7 := 3; to +0x504 *)
Lemma kd_an : forall k regs mem md,
  tk_inv SK B c regs mem md -> getr regs 23 = w64 SHADOW_OFF ->
  getr regs 10 = w64 (tk_kd c + k) -> tk_kd c <> 0 -> 1 <= tk_kn c -> 0 <= k < tk_kn c ->
  (forall regs' mem' md', tk_inv SK B c regs' mem' md' -> tt_same regs regs' ->
     getr regs' 15 = w64 4 -> getr regs' 16 = w64 1 -> getr regs' 17 = w64 3 ->
     (forall x, 0 <= x < 2 ^ 64 -> x <> tk_kd c + k -> aview SEGS (w_H W) mem' x = aview SEGS (w_H W) mem x) ->
     mbyte SEGS (rdW W mem') (tk_kd c + k) = Some (zb 0) ->
     tk_goal SK B c (cfg_of regs' (BASE + TP_KS) mem' md')) ->
  tk_goal SK B c (cfg_of regs (BASE + TP_KN) mem md).
Proof.
  intros k regs mem md HI H23 H10 Hkd Hkn Hk K. unfold tk_goal in *.
  destruct (tk_kd_facts SK B c HC Hkd Hkn) as (A0 & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  pose proof HC as ((_ & HGX & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hajw & _) & _).
  pose proof HI as (HJ & _ & _ & _ & _ & _ & _ & _ & PR).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (Hd : tk_dst c (tk_kd c + k) 1) by (right; left; repeat split; lia).
  destruct (tk_dst_facts SK B c HC _ _ Hd ltac:(lia)) as (D0 & D1 & D2 & D3 & D4 & D5 & D6).
  set (xs := @nil word).
  assert (U10 : bv_unsigned (ew (tk_E c regs xs) 10) = tk_kd c + k).
  { rewrite (tk_E_reg c regs xs 10 10%bv) by (lia || reflexivity). rewrite H10. apply unsigned_lit_small. lia. }
  assert (Hw : writable_at SEGS (rdW W mem) (tk_kd c + k)).
  { apply (writable_kept (w_H W) memc mem _ (PR _)). apply (D6 (tk_kd c + k)). lia. }
  assert (HR : region_ok SEGS (tk_E c regs xs) (rdW W mem) tk_Rnul).
  { unfold region_ok, tk_Rnul. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U10. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. replace (tk_kd c + k + o) with (tk_kd c + k) by lia. exact Hw. }
  pose proof (tk_st_ok SK B LV c HC regs mem md xs TP_KN [] [tk_Rnul] [(10%nat, mkAF 0 (kHighMemEnd - 2) 0)]
    HI H23 (Forall_nil _) ltac:(vm_compute; reflexivity) ltac:(apply Forall_cons; [exact HR | apply Forall_nil]) (conj I I)
    ltac:(cbn [atoms_ok]; split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U10, Z.pow_0_r, Z.mod_1_r; lia
                                 | exact I])) as HS.
  assert (SHOK : sh_ok SEGS tk_Bx tk_SH_kn (tk_E c regs xs) (rdW W mem)).
  { apply Forall_cons; [|apply Forall_nil].
    apply (tk_shent_ok _ _ 10 0 1 (tk_kd c + k)).
    - unfold tk_Bx. apply (tk_U_reg c regs xs 23 23%bv); [lia | reflexivity | exact H23 | unfold SHADOW_OFF; lia].
    - apply (tk_U_reg c regs xs 10 10%bv); [lia | reflexivity | exact H10 | lia].
    - lia.
    - unfold amem_range in D2. destruct D2 as [Q|Q]; [left | right]; lia.
    - rewrite <- (aview_rd_of SEGS). replace (tk_kd c + k + 0) with (tk_kd c + k) by lia. replace (1 - 0) with 1 by lia.
      exact (tk_ra_kept SK B c HC regs mem md (tk_kd c + k) 1 HI ltac:(lia) ltac:(lia) D4). }
  pose proof (tk_E_env c regs xs) as HEI.
  pose proof (paj_run_to_x SK B LAWS (tc_G c) HGX (tc_XO c) (tc_OUT c)) as RUNTO.
  paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_KS.
  { (* the write window: the NUL byte, a byte of the write set *)
    intros a (r & Hin & Ha). vm_compute in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U10 in Ha.
    apply Hajw. apply (D6 a). lia. }
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md1 := m) in * end.
  (* the bytes kept: all but the NUL byte *)
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun x => x = tk_kd c + k) HFr
    ltac:(intros ?bq ?wlo ?whi ?x ?Hin ?Hr; vm_compute in Hin; destruct Hin as [?Hq | []];
          injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite U10 in Hr; lia)) as UN1.
  (* the NUL *)
  pose proof (tt_region _ _ _ 0 _ HS eq_refl) as HRn. cbn [ms_mem restrict mkst] in HRn.
  lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ =>
    assert (U10' : bv_unsigned (ew E1 10) = tk_kd c + k) by (rewrite ?ew_ewset_other by lia; exact U10) end.
  assert (HN : mbyte SEGS (rdW W (ms_mem ms1)) (tk_kd c + k) = Some (zb 0)).
  { pose proof (field_of_region_any (segs := SEGS) _ _ 10%nat (tk_kd c + k) _ _ _ _ _ 0 1%N (SLit 0) HRn U10'
      (or_introl eq_refl) ltac:(lia)) as V.
    rewrite Z.add_0_r in V. exact (val_mem_nul SEGS _ _ V). }
  (* the registers *)
  lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?msr =>
    pose proof (regs_kept_of_st_ok_pi E1 ss1 msr regs (tk_ext c ++ xs) tt_KL HS
      ltac:(split; [intros ?n ?Hn; rewrite ?ew_ewset_other by lia; unfold tk_E; apply Eimg_low; unfold A_TEXT; lia
                   | reflexivity])
      ltac:(vm_compute; reflexivity)) as RK end.
  cbn [ms_regs restrict] in RK.
  tt_reg HS (15%bv : bv 5) R15. tt_reg HS (16%bv : bv 5) R16. tt_reg HS (17%bv : bv 5) R17.
  assert (HI1 : tk_inv SK B c (ms_regs ms1) (ms_mem ms1) md1).
  { apply (tk_inv_step SK B c HC regs mem md (ms_regs ms1) (ms_mem ms1) md1 (fun x => x = tk_kd c + k) HI HJ).
    - unfold md1. repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
    - unfold md1. repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
    - intros x Hx Hz. exact (UN1 x Hx Hz).
    - intros x ->. right. exact (proj1 (D6 (tk_kd c + k) ltac:(lia))).
    - intros x Hp. exact (apresent_grows _ _ _ _ HG Hp).
    - exact (RK 2%bv ltac:(tt_in)).
    - exact (RK 3%bv ltac:(tt_in)).
    - exact (RK 4%bv ltac:(tt_in)). }
  apply (K (ms_regs ms1) (ms_mem ms1) md1 HI1).
  - intros r Hr. exact (RK r Hr).
  - rewrite R15. reflexivity.
  - rewrite R16. reflexivity.
  - rewrite R17. reflexivity.
  - intros x Hx Hne. exact (UN1 x Hx Hne).
  - exact HN.
Qed.

(* +0x4e0 (after checked_memcpy): `add a0, s0, s2`; to +0x4e4 *)
Lemma kd_ar : forall k regs mem md,
  tk_inv SK B c regs mem md -> getr regs 23 = w64 SHADOW_OFF ->
  getr regs 9 = w64 (tk_kd c) -> getr regs 18 = w64 k -> tk_kd c <> 0 -> 1 <= tk_kn c -> 0 <= k < tk_kn c ->
  (forall regs' mem' md', tk_inv SK B c regs' mem' md' -> tt_same regs regs' ->
     getr regs' 15 = w64 4 -> getr regs' 16 = w64 1 -> getr regs' 17 = w64 3 ->
     (forall x, 0 <= x < 2 ^ 64 -> x <> tk_kd c + k -> aview SEGS (w_H W) mem' x = aview SEGS (w_H W) mem x) ->
     mbyte SEGS (rdW W mem') (tk_kd c + k) = Some (zb 0) ->
     tk_goal SK B c (cfg_of regs' (BASE + TP_KS) mem' md')) ->
  tk_goal SK B c (cfg_of regs (BASE + TP_KR) mem md).
Proof.
  intros k regs mem md HI H23 H9 H18 Hkd Hkn Hk K. unfold tk_goal in *.
  destruct (tk_kd_facts SK B c HC Hkd Hkn) as (A0 & A1 & _).
  pose proof HC as ((_ & HGX & _) & _).
  pose proof HI as (HJ & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  set (xs := @nil word).
  pose proof (tk_st_ok SK B LV c HC regs mem md xs TP_KR [] [] [] HI H23 (Forall_nil _) eq_refl (Forall_nil _) I I)
    as HS.
  assert (SHOK : sh_ok SEGS tk_Bx [] (tk_E c regs xs) (rdW W mem)) by constructor.
  pose proof (tk_E_env c regs xs) as HEI.
  pose proof (paj_run_to_x SK B LAWS (tc_G c) HGX (tc_XO c) (tc_OUT c)) as RUNTO.
  assert (E9 : ew (tk_E c regs xs) 9 = w64 (tk_kd c)) by (rewrite (tk_E_reg c regs xs 9 9%bv) by (lia || reflexivity); exact H9).
  assert (E18 : ew (tk_E c regs xs) 18 = w64 k) by (rewrite (tk_E_reg c regs xs 18 18%bv) by (lia || reflexivity); exact H18).
  paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_KN; [tt_awr0 |].
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
  tt_ro HF Em1. pmkst HS. rewrite Em1 in HJ |- *.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md1 := m) in * end.
  lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?msr =>
    pose proof (regs_kept_of_st_ok_pi E1 ss1 msr regs (tk_ext c ++ xs) tt_KL HS
      ltac:(split; [intros ?n ?Hn; rewrite ?ew_ewset_other by lia; unfold tk_E; apply Eimg_low; unfold A_TEXT; lia
                   | reflexivity])
      ltac:(vm_compute; reflexivity)) as RK end.
  cbn [ms_regs restrict] in RK.
  tt_reg HS (10%bv : bv 5) R10.
  rewrite denot_lit_U, (tt_U_add _ 9 0 18 (tk_kd c) k E9 E18) in R10 by lia.
  assert (R10' : getr (ms_regs ms1) 10 = w64 (tk_kd c + k)) by (rewrite R10; unfold w64; f_equal; lia).
  assert (HI1 : tk_inv SK B c (ms_regs ms1) mem md1).
  { apply (tk_inv_step SK B c HC regs mem md (ms_regs ms1) mem md1 (fun _ => False) HI HJ).
    - unfold md1. repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
    - unfold md1. repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
    - intros x _ _. reflexivity.
    - intros x [].
    - intros x Hp. exact Hp.
    - exact (RK 2%bv ltac:(tt_in)).
    - exact (RK 3%bv ltac:(tt_in)).
    - exact (RK 4%bv ltac:(tt_in)). }
  apply (kd_an k (ms_regs ms1) mem md1 HI1 ltac:(rewrite (RK 23%bv ltac:(tt_in)); exact H23) R10' Hkd Hkn Hk).
  intros regs' mem' md' HI' Hs' H15 H16 H17 UN' HN'.
  exact (K regs' mem' md' HI' (tt_same_trans _ _ _ RK Hs') H15 H16 H17 UN' HN').
Qed.

(* the call of checked_memcpy at +0x4dc: a0 = kind, a1 = d, a2 = s2 = kk, ra = +0x4e0 *)
Lemma kd_call : forall kk src regs mem md,
  tk_inv SK B c regs mem md -> getr regs 23 = w64 SHADOW_OFF -> getr regs 9 = w64 (tk_kd c) ->
  getr regs 10 = w64 (tk_kd c) -> getr regs 11 = w64 src -> getr regs 12 = w64 kk -> getr regs 18 = w64 kk ->
  getr regs 1 = Z_to_bv 64 (BASE + TP_KR) -> 0 <= kk <= tk_kn c - 1 -> kk < 2 ^ 32 ->
  LA_G_NL <= src -> src + kk <= LA_G_NL + NK_CHUNK_LEN -> tk_kd c <> 0 -> 1 <= tk_kn c ->
  (forall regs' mem' md', tk_inv SK B c regs' mem' md' -> tt_same regs regs' ->
     getr regs' 15 = w64 4 -> getr regs' 16 = w64 1 -> getr regs' 17 = w64 3 ->
     (forall i, 0 <= i < kk -> aview SEGS (w_H W) mem' (tk_kd c + i) = aview SEGS (w_H W) mem (src + i)) ->
     tt_kept (tk_kd c) (kk + 1) mem mem' ->
     mbyte SEGS (rdW W mem') (tk_kd c + kk) = Some (zb 0) ->
     tk_goal SK B c (cfg_of regs' (BASE + TP_KS) mem' md')) ->
  tk_goal SK B c (cfg_of regs (pa_sigma LS___asan_memcpy) mem md).
Proof.
  intros kk src regs mem md HI H23 H9 H10 H11 H12 H18 H1 Hkk Hkk2 Hs0 Hs1 Hkd Hkn K. unfold tk_goal in *.
  destruct (tk_kd_facts SK B c HC Hkd Hkn) as (A0 & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HI as (_ & _ & _ & Hsp & _).
  assert (Hd : tk_dst c (tk_kd c) kk) by (right; left; repeat split; lia).
  destruct (tk_src_gnl SK B c HC regs mem md src kk HI Hsp Hs0 Hs1 ltac:(lia)) as (X0 & X1 & X2 & X3 & X4 & X5).
  eapply SRr_bind.
  { refine (tk_intrin SK B LAWS c HC OCpy _ MEMCPY regs mem md (tk_kd c) src kk (Z_to_bv 64 (BASE + TP_KR)) HI
      H10 H11 H12 ltac:(lia) Hd H1 (ret_ok_codeptr_v TP_KR ltac:(unfold TP_KR, AF_talk; lia) eq_refl) _).
    refine (conj X0 (conj X1 (conj X2 (conj _ (conj X3 (conj X4 X5)))))).
    unfold apart_gnl, LA_G_NL, NK_SIZE, NK_CHUNK_LEN in *. lia. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HI2 & HP2 & Hcp & Hout).
  cbv iota beta in Hcp.
  pose proof (tt_same_pres _ _ HP2) as Hs2.
  apply (kd_ar kk regs2 mem2 md2 HI2 ltac:(rewrite (Hs2 23%bv ltac:(tt_in)); exact H23)
    ltac:(rewrite (Hs2 9%bv ltac:(tt_in)); exact H9)
    ltac:(rewrite (tt_pres _ _ HP2 18%bv ltac:(tt_cs)); exact H18) Hkd Hkn ltac:(lia)).
  intros regs' mem' md' HI' Hs' H15 H16 H17 UN' HN'.
  apply (K regs' mem' md' HI' (tt_same_trans _ _ _ Hs2 Hs') H15 H16 H17).
  - intros i Hi. rewrite (UN' (tk_kd c + i)) by lia. exact (Hcp i Hi).
  - intros x Hx Hn Hw. rewrite (UN' x Hx) by lia. apply Hout; [exact Hx | lia | exact Hw].
  - exact HN'.
Qed.

(* +0x4c8: s2 := min_u (s2, kind_n - 1) (the spilled kind_n - 1), the call checked_memcpy *)
Lemma kd_ca : forall k0 src b regs mem md,
  tk_inv SK B c regs mem md -> tk_rs0 c regs -> getr regs 20 = w64 b -> tk_spilled c mem b ->
  0 <= b -> b + 4 < 2 ^ 64 ->
  getr regs 11 = w64 src -> getr regs 18 = w64 k0 -> 0 <= k0 < 2 ^ 32 ->
  LA_G_NL <= src -> src + k0 <= LA_G_NL + NK_CHUNK_LEN -> tk_kd c <> 0 -> 1 <= tk_kn c ->
  (forall regs' mem' md', tk_inv SK B c regs' mem' md' -> tt_same regs regs' ->
     getr regs' 15 = w64 4 -> getr regs' 16 = w64 1 -> getr regs' 17 = w64 3 ->
     (forall i, 0 <= i < Z.min k0 (tk_kn c - 1) ->
        aview SEGS (w_H W) mem' (tk_kd c + i) = aview SEGS (w_H W) mem (src + i)) ->
     tt_kept (tk_kd c) (Z.min k0 (tk_kn c - 1) + 1) mem mem' ->
     mbyte SEGS (rdW W mem') (tk_kd c + Z.min k0 (tk_kn c - 1)) = Some (zb 0) ->
     tk_goal SK B c (cfg_of regs' (BASE + TP_KS) mem' md')) ->
  tk_goal SK B c (cfg_of regs (BASE + TP_CK) mem md).
Proof.
  intros k0 src b regs mem md HI (H8 & H9 & H23) H20 HSP Hb0 Hb1 H11 H18 Hk0 Hs0 Hs1 Hkd Hkn K.
  destruct (tk_kd_facts SK B c HC Hkd Hkn) as (A0 & A1 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HC as ((_ & HGX & _) & _).
  pose proof HI as (HJ & _).
  set (xs := @nil word).
  pose proof (tk_st_ok SK B LV c HC regs mem md xs TP_CK [] [tk_frs] [] HI H23 (Forall_nil _)
    ltac:(vm_compute; reflexivity)
    ltac:(apply Forall_cons; [exact (tk_frs_ok SK B c HC regs mem md xs b HI HSP H20 Hb0 Hb1) | apply Forall_nil]) (conj I I) I) as HS.
  assert (SHOK : sh_ok SEGS tk_Bx [] (tk_E c regs xs) (rdW W mem)) by constructor.
  pose proof (tk_E_env c regs xs) as HEI.
  pose proof (paj_run_x SK B LAWS (tc_G c) HGX (tc_XO c) (tc_OUT c)) as RUN.
  pose proof (paj_branch (PI := PI)) as BR.
  assert (E18 : ew (tk_E c regs xs) 18 = w64 k0)
    by (rewrite (tk_E_reg c regs xs 18 18%bv) by (lia || reflexivity); exact H18).
  assert (E47 : ew (tk_E c regs xs) 47 = w64 (tk_kn c - 1)) by exact (tk_E_ext c regs xs 15 ltac:(lia)).
  unfold tk_goal in *.
  (* +0x4c8..+0x4cc: a0 := kind_n - 1; `bltu s2, a0` *)
  paj_run_tok RUN HS HJ SHOK tk_span; [tt_awr0 |].
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
  tt_ro HF Em1. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK tk_span;
    rewrite branch_ltu_U, (U_atom _ 18 k0 E18 ltac:(lia)), (U_atom _ 47 (tk_kn c - 1) E47 ltac:(lia)) in Hc.
  - (* k0 < kind_n - 1: s2 = k0 *)
    apply Z.ltb_lt in Hc.
    paj_run_tok RUN HS HJ SHOK tk_span; [tt_awr0 |].
    lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => rename m into ms2 end.
    tt_ro HF Em2. pmkst HS. rewrite Em2, Em1 in HJ |- *.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md2 := m) in * end.
    lazymatch type of HS with st_ok _ ?E1 ?ss1 ?msr =>
      pose proof (regs_kept_of_st_ok SEGS E1 ss1 msr regs (tk_ext c ++ xs) tt_KL HS
        ltac:(split; [intros ?n ?Hn; rewrite ?ew_ewset_other by lia; unfold tk_E; apply Eimg_low; unfold A_TEXT; lia
                     | reflexivity])
        ltac:(vm_compute; reflexivity)) as RK end.
    cbn [ms_regs restrict] in RK.
    tt_reg HS (1%bv : bv 5) R1. tt_reg HS (10%bv : bv 5) R10. tt_reg HS (11%bv : bv 5) R11.
    tt_reg HS (12%bv : bv 5) R12. tt_reg HS (18%bv : bv 5) R18.
    rewrite (tt_den regs xs 9 9%bv) in R10 by (lia || reflexivity).
    rewrite (tt_den regs xs 11 11%bv) in R11 by (lia || reflexivity).
    rewrite (tt_den regs xs 18 18%bv) in R12 by (lia || reflexivity).
    rewrite (tt_den regs xs 18 18%bv) in R18 by (lia || reflexivity).
    assert (HI2 : tk_inv SK B c (ms_regs ms2) mem md2).
    { apply (tk_inv_step SK B c HC regs mem md (ms_regs ms2) mem md2 (fun _ => False) HI HJ).
      - unfold md2. repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
      - unfold md2. repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
      - intros x _ _. reflexivity.
      - intros x [].
      - intros x Hp. exact Hp.
      - exact (RK 2%bv ltac:(tt_in)).
      - exact (RK 3%bv ltac:(tt_in)).
      - exact (RK 4%bv ltac:(tt_in)). }
    replace (Z.min k0 (tk_kn c - 1)) with k0 in K by lia.
    apply (kd_call k0 src (ms_regs ms2) mem md2 HI2 ltac:(rewrite (RK 23%bv ltac:(tt_in)); exact H23)
      ltac:(rewrite (RK 9%bv ltac:(tt_in)); exact H9) ltac:(rewrite R10; exact H9) ltac:(rewrite R11; exact H11)
      ltac:(rewrite R12; exact H18) ltac:(rewrite R18; exact H18)
      ltac:(rewrite R1; exact (codeptr_val _ 22864 HEI)) ltac:(lia) ltac:(lia) Hs0 Hs1 Hkd Hkn).
    intros regs' mem' md' HI' Hs' H15 H16 H17 Hcp UN HN.
    exact (K regs' mem' md' HI' (tt_same_trans _ _ _ RK Hs') H15 H16 H17 Hcp UN HN).
  - (* k0 >= kind_n - 1: s2 := kind_n - 1 *)
    apply Z.ltb_ge in Hc.
    paj_run_tok RUN HS HJ SHOK tk_span; [tt_awr0 |].
    lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => rename m into ms2 end.
    tt_ro HF Em2. pmkst HS. rewrite Em2, Em1 in HJ |- *.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md2 := m) in * end.
    lazymatch type of HS with st_ok _ ?E1 ?ss1 ?msr =>
      pose proof (regs_kept_of_st_ok SEGS E1 ss1 msr regs (tk_ext c ++ xs) tt_KL HS
        ltac:(split; [intros ?n ?Hn; rewrite ?ew_ewset_other by lia; unfold tk_E; apply Eimg_low; unfold A_TEXT; lia
                     | reflexivity])
        ltac:(vm_compute; reflexivity)) as RK end.
    cbn [ms_regs restrict] in RK.
    tt_reg HS (1%bv : bv 5) R1. tt_reg HS (10%bv : bv 5) R10. tt_reg HS (11%bv : bv 5) R11.
    tt_reg HS (12%bv : bv 5) R12. tt_reg HS (18%bv : bv 5) R18.
    rewrite (tt_den regs xs 9 9%bv) in R10 by (lia || reflexivity).
    rewrite (tt_den regs xs 11 11%bv) in R11 by (lia || reflexivity).
    assert (V47 : sv_denot (tk_E c regs xs) (SOff 47 0) = w64 (tk_kn c - 1)).
    { rewrite denot_lit_U, (U_atom _ 47 (tk_kn c - 1) E47 ltac:(lia)). reflexivity. }
    rewrite V47 in R12, R18.
    assert (HI2 : tk_inv SK B c (ms_regs ms2) mem md2).
    { apply (tk_inv_step SK B c HC regs mem md (ms_regs ms2) mem md2 (fun _ => False) HI HJ).
      - unfold md2. repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
      - unfold md2. repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
      - intros x _ _. reflexivity.
      - intros x [].
      - intros x Hp. exact Hp.
      - exact (RK 2%bv ltac:(tt_in)).
      - exact (RK 3%bv ltac:(tt_in)).
      - exact (RK 4%bv ltac:(tt_in)). }
    replace (Z.min k0 (tk_kn c - 1)) with (tk_kn c - 1) in K by lia.
    apply (kd_call (tk_kn c - 1) src (ms_regs ms2) mem md2 HI2 ltac:(rewrite (RK 23%bv ltac:(tt_in)); exact H23)
      ltac:(rewrite (RK 9%bv ltac:(tt_in)); exact H9) ltac:(rewrite R10; exact H9) ltac:(rewrite R11; exact H11)
      R12 R18 ltac:(rewrite R1; exact (codeptr_val _ 22864 HEI)) ltac:(lia) ltac:(lia) Hs0 ltac:(lia) Hkd Hkn).
    intros regs' mem' md' HI' Hs' H15 H16 H17 Hcp UN HN.
    exact (K regs' mem' md' HI' (tt_same_trans _ _ _ RK Hs') H15 H16 H17 Hcp UN HN).
Qed.

(* +0x494: one byte of the NUL scan; a1 = d, a2 = n, s2 = k, a3 = d + k *)
Lemma kd_sk_step : forall pay src n mem,
  Z.of_nat (length pay) = n ->
  (forall i, 0 <= i < n -> mbyte SEGS (rdW W mem) (src + i) = nth_error pay (Z.to_nat i)) ->
  LA_G_NL <= src -> src + n <= LA_G_NL + NK_CHUNK_LEN ->
  forall k regs md, 0 <= k < n -> (Z.to_nat k <= nul_at pay)%nat ->
  tk_inv SK B c regs mem md -> getr regs 23 = w64 SHADOW_OFF ->
  getr regs 11 = w64 src -> getr regs 12 = w64 n -> getr regs 18 = w64 k -> getr regs 13 = w64 (src + k) ->
  (k + 1 < n -> (Z.to_nat (k + 1) <= nul_at pay)%nat -> forall regs1 md1, tk_inv SK B c regs1 mem md1 ->
     tt_same regs regs1 -> getr regs1 11 = w64 src -> getr regs1 12 = w64 n -> getr regs1 18 = w64 (k + 1) ->
     getr regs1 13 = w64 (src + (k + 1)) -> tk_goal SK B c (cfg_of regs1 (BASE + TP_SK) mem md1)) ->
  (forall regs' md', tk_inv SK B c regs' mem md' -> tt_same regs regs' -> getr regs' 11 = w64 src ->
     getr regs' 18 = w64 (Z.of_nat (nul_at pay)) -> tk_goal SK B c (cfg_of regs' (BASE + TP_CK) mem md')) ->
  tk_goal SK B c (cfg_of regs (BASE + TP_SK) mem md).
Proof.
  intros pay src n mem Hlen Hby Hsr0 Hsr1 k regs md Hk Hnul HI H23 H11 H12 H18 H13 KS KC.
  unfold tk_goal in *. unfold LA_G_NL, NK_CHUNK_LEN in Hsr0, Hsr1.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HC as ((_ & HGX & _) & _).
  pose proof HI as (HJ & _).
  destruct (nth_error pay (Z.to_nat k)) as [bb|] eqn:Eb; [|apply nth_error_None in Eb; lia].
  pose proof (Hby k ltac:(lia)) as Hm. rewrite Eb in Hm.
  pose proof (tw_byte_range bb) as Rb.
  set (xs := [w64 (bz bb)]).
  assert (U13 : bv_unsigned (ew (tk_E c regs xs) 13) = src + k).
  { rewrite (tk_E_reg c regs xs 13 13%bv) by (lia || reflexivity). rewrite H13. apply unsigned_lit_small.
    unfold LA_G_NL, NK_CHUNK_LEN in *. lia. }
  assert (E49 : ew (tk_E c regs xs) 49 = w64 (bz bb)) by exact (tk_E_xs c regs xs 0 ltac:(lia)).
  assert (U49 : bv_unsigned (ew (tk_E c regs xs) 49) = bz bb) by (rewrite E49; apply unsigned_lit_small; lia).
  assert (HR : region_ok SEGS (tk_E c regs xs) (rdW W mem)
                 (YP09.mkRegion (Some 13%nat) 0 1 0 0 [tk_ch 0 1 (SOff 49 0)])).
  { unfold region_ok, tk_ch. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U13. split; [lia|]. split; [unfold LA_G_NL, NK_CHUNK_LEN in *; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ (src + k) 0 1 (SOff 49 0) (bz bb)).
    - cbn [sv_denot]. rewrite U49, Z.add_0_r. reflexivity.
    - change (2 ^ (8 * Z.of_N 1)) with 256. lia.
    - lia.
    - rewrite Z.add_0_r. exact (tt_val1 _ _ _ Hm). }
  pose proof (tk_st_ok SK B LV c HC regs mem md xs TP_SK [] [YP09.mkRegion (Some 13%nat) 0 1 0 0 [tk_ch 0 1 (SOff 49 0)]]
    [(13%nat, mkAF LA_G_NL (LA_G_NL + NK_CHUNK_LEN - 1) 0); (49%nat, mkAF 0 255 0)] HI H23 (Forall_nil _)
    ltac:(vm_compute; reflexivity) ltac:(apply Forall_cons; [exact HR | apply Forall_nil]) (conj I I)
    ltac:(cbn [atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U13, U49, !Z.pow_0_r, !Z.mod_1_r;
          unfold LA_G_NL, NK_CHUNK_LEN in *; repeat split; lia)) as HS.
  assert (SHOK : sh_ok SEGS tk_Bx tk_SH_sk (tk_E c regs xs) (rdW W mem)).
  { apply Forall_cons; [|apply Forall_nil].
    apply (tk_shent_ok _ _ 13 0 8 (src + k)).
    - unfold tk_Bx. apply (tk_U_reg c regs xs 23 23%bv); [lia | reflexivity | exact H23 | unfold SHADOW_OFF; lia].
    - apply (tk_U_reg c regs xs 13 13%bv); [lia | reflexivity | exact H13 | unfold LA_G_NL, NK_CHUNK_LEN in *; lia].
    - lia.
    - left. unfold LA_G_NL, NK_CHUNK_LEN in *. lia.
    - apply (tt_ra_gnl regs mem md HI); unfold LA_G_NL, NK_CHUNK_LEN, NK_N_CHUNKS in *; lia. }
  pose proof (tk_E_env c regs xs) as HEI.
  pose proof (paj_run_x SK B LAWS (tc_G c) HGX (tc_XO c) (tc_OUT c)) as RUN.
  pose proof (paj_run_to_x SK B LAWS (tc_G c) HGX (tc_XO c) (tc_OUT c)) as RUNTO.
  pose proof (paj_branch (PI := PI)) as BR.
  assert (E11 : ew (tk_E c regs xs) 11 = w64 src)
    by (rewrite (tk_E_reg c regs xs 11 11%bv) by (lia || reflexivity); exact H11).
  assert (E12 : ew (tk_E c regs xs) 12 = w64 n)
    by (rewrite (tk_E_reg c regs xs 12 12%bv) by (lia || reflexivity); exact H12).
  assert (E18 : ew (tk_E c regs xs) 18 = w64 k)
    by (rewrite (tk_E_reg c regs xs 18 18%bv) by (lia || reflexivity); exact H18).
  (* the instrumented check of d[k], `lbu`, `beqz` *)
  paj_run_tok RUN HS HJ SHOK tk_span; [tt_awr0 |].
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
  tt_ro HF Em1. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK tk_span;
    rewrite branch_eq_U, (U_atom _ 49 (bz bb) E49 ltac:(lia)), (tt_U_lit _ 0 ltac:(lia)) in Hc.
  - (* d[k] = 0: the clamp with s2 = k *)
    apply Z.eqb_eq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_CK; [tt_awr0 |].
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms2 end.
    tt_ro HF Em2. pmkst HS. rewrite Em2, Em1 in HJ |- *.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md2 := m) in * end.
    lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?msr =>
      pose proof (regs_kept_of_st_ok_pi E1 ss1 msr regs (tk_ext c ++ xs) tt_KL HS
        ltac:(split; [intros ?n ?Hn; rewrite ?ew_ewset_other by lia; unfold tk_E; apply Eimg_low; unfold A_TEXT; lia
                     | reflexivity])
        ltac:(vm_compute; reflexivity)) as RK end.
    cbn [ms_regs restrict] in RK.
    tt_reg HS (11%bv : bv 5) R11. tt_reg HS (18%bv : bv 5) R18.
    rewrite (tt_den regs xs 11 11%bv) in R11 by (lia || reflexivity).
    rewrite (tt_den regs xs 18 18%bv) in R18 by (lia || reflexivity).
    assert (HI2 : tk_inv SK B c (ms_regs ms2) mem md2).
    { apply (tk_inv_step SK B c HC regs mem md (ms_regs ms2) mem md2 (fun _ => False) HI HJ).
      - unfold md2. repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
      - unfold md2. repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
      - intros x _ _. reflexivity.
      - intros x [].
      - intros x Hp. exact Hp.
      - exact (RK 2%bv ltac:(tt_in)).
      - exact (RK 3%bv ltac:(tt_in)).
      - exact (RK 4%bv ltac:(tt_in)). }
    apply (KC (ms_regs ms2) md2 HI2 RK); [rewrite R11; exact H11 |].
    rewrite R18, H18, (tt_scan_hit pay k bb ltac:(lia) Hnul Eb Hc). reflexivity.
  - (* d[k] <> 0: s2 := k + 1, `bne a2, s2` *)
    apply Z.eqb_neq in Hc.
    pose proof (tt_scan_go pay k bb ltac:(lia) Hnul Eb Hc) as Hnul1. rename Hc into Hbz.
    paj_run_tok RUN HS HJ SHOK tk_span; [tt_awr0 |].
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms2 end.
    tt_ro HF Em2. clear HF HFr HG.
    psrr_branch_tok RUN BR HS SHOK tk_span;
      rewrite branch_ne_U, (U_atom _ 12 n E12 ltac:(lia)), (U_atom_off _ 18 k 1 E18 ltac:(lia) ltac:(lia)) in Hc.
    + (* k + 1 <> n: the next byte *)
      apply negb_true_iff, Z.eqb_neq in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_SK; [tt_awr0 |].
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms3 end.
      tt_ro HF Em3. pmkst HS. rewrite Em3, Em2, Em1 in HJ |- *.
      lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md3 := m) in * end.
      lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?msr =>
        pose proof (regs_kept_of_st_ok_pi E1 ss1 msr regs (tk_ext c ++ xs) tt_KL HS
          ltac:(split; [intros ?n ?Hn; rewrite ?ew_ewset_other by lia; unfold tk_E; apply Eimg_low; unfold A_TEXT; lia
                       | reflexivity])
          ltac:(vm_compute; reflexivity)) as RK end.
      cbn [ms_regs restrict] in RK.
      tt_reg HS (11%bv : bv 5) R11. tt_reg HS (12%bv : bv 5) R12. tt_reg HS (18%bv : bv 5) R18.
      tt_reg HS (13%bv : bv 5) R13.
      rewrite (tt_den regs xs 11 11%bv) in R11 by (lia || reflexivity).
      rewrite (tt_den regs xs 12 12%bv) in R12 by (lia || reflexivity).
      rewrite denot_lit_U, (U_atom_off _ 18 k 1 E18 ltac:(lia) ltac:(lia)) in R18.
      rewrite denot_lit_U, (tt_U_add _ 11 1 18 src k E11 E18) in R13 by (unfold LA_G_NL, NK_CHUNK_LEN in *; lia).
      assert (HI3 : tk_inv SK B c (ms_regs ms3) mem md3).
      { apply (tk_inv_step SK B c HC regs mem md (ms_regs ms3) mem md3 (fun _ => False) HI HJ).
        - unfold md3. repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
        - unfold md3. repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
        - intros x _ _. reflexivity.
        - intros x [].
        - intros x Hp. exact Hp.
        - exact (RK 2%bv ltac:(tt_in)).
        - exact (RK 3%bv ltac:(tt_in)).
        - exact (RK 4%bv ltac:(tt_in)). }
      apply (KS ltac:(lia) Hnul1 (ms_regs ms3) md3 HI3 RK).
      * rewrite R11. exact H11.
      * rewrite R12. exact H12.
      * rewrite R18. reflexivity.
      * rewrite R13. unfold w64. f_equal. lia.
    + (* k + 1 = n: the clamp with s2 = n *)
      apply negb_false_iff, Z.eqb_eq in Hc.
      paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_CK; [tt_awr0 |].
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms3 end.
      tt_ro HF Em3. pmkst HS. rewrite Em3, Em2, Em1 in HJ |- *.
      lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md3 := m) in * end.
      lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?msr =>
        pose proof (regs_kept_of_st_ok_pi E1 ss1 msr regs (tk_ext c ++ xs) tt_KL HS
          ltac:(split; [intros ?n ?Hn; rewrite ?ew_ewset_other by lia; unfold tk_E; apply Eimg_low; unfold A_TEXT; lia
                       | reflexivity])
          ltac:(vm_compute; reflexivity)) as RK end.
      cbn [ms_regs restrict] in RK.
      tt_reg HS (11%bv : bv 5) R11. tt_reg HS (18%bv : bv 5) R18.
      rewrite (tt_den regs xs 11 11%bv) in R11 by (lia || reflexivity).
      rewrite (tt_den regs xs 12 12%bv) in R18 by (lia || reflexivity).
      assert (HI3 : tk_inv SK B c (ms_regs ms3) mem md3).
      { apply (tk_inv_step SK B c HC regs mem md (ms_regs ms3) mem md3 (fun _ => False) HI HJ).
        - unfold md3. repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
        - unfold md3. repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
        - intros x _ _. reflexivity.
        - intros x [].
        - intros x Hp. exact Hp.
        - exact (RK 2%bv ltac:(tt_in)).
        - exact (RK 3%bv ltac:(tt_in)).
        - exact (RK 4%bv ltac:(tt_in)). }
      apply (KC (ms_regs ms3) md3 HI3 RK); [rewrite R11; exact H11 |].
      rewrite R18, H12, (tt_scan_end pay n Hlen ltac:(lia)). reflexivity.
Qed.

(* the NUL scan from byte k, by induction on n - k *)
Lemma kd_sk : forall pay src n mem,
  Z.of_nat (length pay) = n ->
  (forall i, 0 <= i < n -> mbyte SEGS (rdW W mem) (src + i) = nth_error pay (Z.to_nat i)) ->
  LA_G_NL <= src -> src + n <= LA_G_NL + NK_CHUNK_LEN ->
  forall (f : nat) k regs md, (Z.to_nat (n - k) <= f)%nat -> 0 <= k < n -> (Z.to_nat k <= nul_at pay)%nat ->
  tk_inv SK B c regs mem md -> getr regs 23 = w64 SHADOW_OFF ->
  getr regs 11 = w64 src -> getr regs 12 = w64 n -> getr regs 18 = w64 k -> getr regs 13 = w64 (src + k) ->
  (forall regs' md', tk_inv SK B c regs' mem md' -> tt_same regs regs' -> getr regs' 11 = w64 src ->
     getr regs' 18 = w64 (Z.of_nat (nul_at pay)) -> tk_goal SK B c (cfg_of regs' (BASE + TP_CK) mem md')) ->
  tk_goal SK B c (cfg_of regs (BASE + TP_SK) mem md).
Proof.
  intros pay src n mem Hlen Hby Hsr0 Hsr1 f. induction f as [|f IH];
    intros k regs md Hf Hk Hnul HI H23 H11 H12 H18 H13 KC; [lia|].
  apply (kd_sk_step pay src n mem Hlen Hby Hsr0 Hsr1 k regs md Hk Hnul HI H23 H11 H12 H18 H13); [|exact KC].
  intros Hk1 Hnul1 regs1 md1 HI1 Hs1 H11' H12' H18' H13'.
  apply (IH (k + 1) regs1 md1 ltac:(lia) ltac:(lia) Hnul1 HI1
    ltac:(rewrite (Hs1 23%bv ltac:(tt_in)); exact H23) H11' H12' H18' H13').
  intros regs' md' HI' Hs' H11'' H18''. exact (KC regs' md' HI' (tt_same_trans _ _ _ Hs1 Hs') H11'' H18'').
Qed.

(* from the clamp's continuation to the inner step: the kind buffer holds the cut text *)
Lemma kd_fin : forall ci a al l aa i il l' k regs mem md regs' mem' md',
  TK_K504 SK B c ci a al l aa i il l' (Some (slice (tk_ck c ci) (i + RTA_HDR) (l' - RTA_HDR))) ->
  tk_inv SK B c regs mem md -> tk_rs0 c regs -> tk_rat regs (tk_b ci) a al -> getr regs 21 = w64 l ->
  getr regs 24 = w64 i -> getr regs 25 = w64 il -> getr regs 26 = w64 l' ->
  tk_amem c mem (tk_b ci) (Attrs k aa) -> tk_kd c <> 0 -> 1 <= tk_kn c ->
  0 <= ci < tk_nch c -> 0 <= i -> 4 <= l' <= il -> i + il <= Z.of_nat (length (tk_ck c ci)) ->
  tk_inv SK B c regs' mem' md' -> tt_same regs regs' ->
  getr regs' 15 = w64 4 -> getr regs' 16 = w64 1 -> getr regs' 17 = w64 3 ->
  (forall j, 0 <= j < Z.min (Z.of_nat (nul_at (slice (tk_ck c ci) (i + RTA_HDR) (l' - RTA_HDR)))) (tk_kn c - 1) ->
     aview SEGS (w_H W) mem' (tk_kd c + j) = aview SEGS (w_H W) mem (tk_b ci + 4 + i + j)) ->
  tt_kept (tk_kd c) (Z.min (Z.of_nat (nul_at (slice (tk_ck c ci) (i + RTA_HDR) (l' - RTA_HDR)))) (tk_kn c - 1) + 1)
    mem mem' ->
  mbyte SEGS (rdW W mem')
    (tk_kd c + Z.min (Z.of_nat (nul_at (slice (tk_ck c ci) (i + RTA_HDR) (l' - RTA_HDR)))) (tk_kn c - 1)) =
    Some (zb 0) ->
  tk_goal SK B c (cfg_of regs' (BASE + TP_KS) mem' md').
Proof.
  intros ci a al l aa i il l' k regs mem md regs' mem' md' K504 HI Hrs0 Hrat H21 H24 H25 H26 Ham Hkd Hkn Hci Hi
    Hl Hil HI' Hs H15 H16 H17 Hcp UN HN.
  destruct (tt_chunk ci Hci) as (Hcl & Hcl2 & Hnc).
  destruct (tk_kd_facts SK B c HC Hkd Hkn) as (K0 & K1 & _). unfold kHighMemEnd in K1.
  pose proof HC as (_ & _ & _ & _ & HNW & _).
  apply (K504 regs' mem' md' HI').
  - exact (tt_rs0_same _ _ Hs Hrs0).
  - exact (tt_rat_same _ _ _ _ _ Hs Hrat H15 H16 H17).
  - rewrite (Hs 21%bv ltac:(tt_in)). exact H21.
  - rewrite (Hs 24%bv ltac:(tt_in)). exact H24.
  - rewrite (Hs 25%bv ltac:(tt_in)). exact H25.
  - rewrite (Hs 26%bv ltac:(tt_in)). exact H26.
  - apply (tt_amem_kind regs' mem mem' md' _ (Attrs k aa) _ _ HI' Ham Hkd Hkn (tt_cut_len _ _ Hkn) UN).
    unfold tk_nch, tk_ck in *.
    apply (acstr_take SEGS (w_H W) mem mem' LA_G_NL kbs ci i l' (tk_kd c) (tk_kn c)
      (tk_nlk_kept SK B c HC regs mem md HI) HNW Hci Hi ltac:(lia) ltac:(lia) Hkn ltac:(lia) ltac:(lia)).
    + intros j Hj. rewrite (Hcp j Hj). unfold tk_b, NL_CHUNK_MAX. f_equal. lia.
    + exact HN.
Qed.

(* THE PIECE: take_text into the kind buffer, +0x47c .. +0x500 *)
Lemma tk_take_kd_ok : TK_TAKE_KD SK B c.
Proof.
  intros ci a al l aa i il l' k K504 regs mem md HI Hrs0 Hrat H21 H24 H25 H26 Ham Hkd Hkn0 Hci Hi Hl Hil.
  pose proof (tt_kn_pos Hkn0) as Hkn.
  destruct (tt_chunk ci Hci) as (Hcl & Hcl2 & Hnc). unfold NL_CHUNK_MAX, NL_CHUNKS in Hcl2, Hnc.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HC as ((_ & HGX & _) & _).
  pose proof HI as (HJ & _).
  pose proof Hrs0 as (H8 & H9 & H23). pose proof Hrat as (H20 & H27 & H22 & H19 & H15 & H16 & H17).
  pose proof Ham as (_ & _ & HSP).
  assert (Hb : tk_b ci = LA_G_NL + 4096 * ci) by (unfold tk_b, NL_CHUNK_MAX; ring).
  assert (HbR : 0x5dcac0 <= tk_b ci /\ tk_b ci + 4096 <= 0x5dcac0 + 262144)
    by (rewrite Hb; unfold LA_G_NL, NL_CHUNKS in *; lia).
  assert (Hlen : Z.of_nat (length (slice (tk_ck c ci) (i + RTA_HDR) (l' - RTA_HDR))) = l' - 4)
    by (rewrite (tt_pay_len (tk_ck c ci) i l' Hi ltac:(lia) ltac:(lia)); lia).
  pose proof (nul_at_le (slice (tk_ck c ci) (i + RTA_HDR) (l' - RTA_HDR))) as Hnl.
  set (xs := @nil word).
  pose proof (tk_st_ok SK B LV c HC regs mem md xs TP_TK [] [tk_frs] [] HI H23 (Forall_nil _)
    ltac:(vm_compute; reflexivity)
    ltac:(apply Forall_cons; [exact (tk_frs_ok SK B c HC regs mem md xs (tk_b ci) HI HSP H20 ltac:(lia) ltac:(lia)) | apply Forall_nil])
    (conj I I) I) as HS.
  assert (SHOK : sh_ok SEGS tk_Bx [] (tk_E c regs xs) (rdW W mem)) by constructor.
  pose proof (tk_E_env c regs xs) as HEI.
  pose proof (paj_run_x SK B LAWS (tc_G c) HGX (tc_XO c) (tc_OUT c)) as RUN.
  pose proof (paj_run_to_x SK B LAWS (tc_G c) HGX (tc_XO c) (tc_OUT c)) as RUNTO.
  pose proof (paj_branch (PI := PI)) as BR.
  assert (E20 : ew (tk_E c regs xs) 20 = w64 (tk_b ci))
    by (rewrite (tk_E_reg c regs xs 20 20%bv) by (lia || reflexivity); exact H20).
  assert (E26 : ew (tk_E c regs xs) 26 = w64 l')
    by (rewrite (tk_E_reg c regs xs 26 26%bv) by (lia || reflexivity); exact H26).
  assert (E24 : ew (tk_E c regs xs) 24 = w64 i)
    by (rewrite (tk_E_reg c regs xs 24 24%bv) by (lia || reflexivity); exact H24).
  assert (Usrc : U (tk_E c regs xs) (SAlu ALU_ADD (SOff 20 4) (SOff 24 0)) = tk_b ci + 4 + i).
  { apply (tt_U_add _ 20 4 24 (tk_b ci) i E20 E24); unfold NL_CHUNK_MAX, NL_CHUNKS, LA_G_NL in *; lia. }
  unfold tk_goal in *.
  (* +0x47c..+0x48c: a2 := l' - 4, a1 := b + 4 + i, s2 := 0, `beqz a2` *)
  paj_run_tok RUN HS HJ SHOK tk_span; [tt_awr0 |].
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms1 end.
  tt_ro HF Em1. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK tk_span;
    rewrite branch_eq_U, (U_atom_off _ 26 l' (-4) E26 ltac:(lia) ltac:(lia)), (tt_U_lit _ 0 ltac:(lia)) in Hc.
  - (* n = 0: the clamp with s2 = 0 *)
    apply Z.eqb_eq in Hc.
    assert (Hn0 : Z.of_nat (nul_at (slice (tk_ck c ci) (i + RTA_HDR) (l' - RTA_HDR))) = 0) by lia.
    paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_CK; [tt_awr0 |].
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms2 end.
    tt_ro HF Em2. pmkst HS. rewrite Em2, Em1 in HJ |- *.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md2 := m) in * end.
    lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?msr =>
      pose proof (regs_kept_of_st_ok_pi E1 ss1 msr regs (tk_ext c ++ xs) tt_KL HS
        ltac:(split; [intros ?n ?Hn; rewrite ?ew_ewset_other by lia; unfold tk_E; apply Eimg_low; unfold A_TEXT; lia
                     | reflexivity])
        ltac:(vm_compute; reflexivity)) as RK end.
    cbn [ms_regs restrict] in RK.
    tt_reg HS (11%bv : bv 5) R11. tt_reg HS (18%bv : bv 5) R18.
    rewrite denot_lit_U, Usrc in R11.
    assert (HI2 : tk_inv SK B c (ms_regs ms2) mem md2).
    { apply (tk_inv_step SK B c HC regs mem md (ms_regs ms2) mem md2 (fun _ => False) HI HJ).
      - unfold md2. repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
      - unfold md2. repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
      - intros x _ _. reflexivity.
      - intros x [].
      - intros x Hp. exact Hp.
      - exact (RK 2%bv ltac:(tt_in)).
      - exact (RK 3%bv ltac:(tt_in)).
      - exact (RK 4%bv ltac:(tt_in)). }
    apply (kd_ca (Z.of_nat (nul_at (slice (tk_ck c ci) (i + RTA_HDR) (l' - RTA_HDR)))) (tk_b ci + 4 + i) (tk_b ci)
      (ms_regs ms2) mem md2 HI2 (tt_rs0_same _ _ RK Hrs0) ltac:(rewrite (RK 20%bv ltac:(tt_in)); exact H20) HSP
      ltac:(lia) ltac:(unfold NL_CHUNK_MAX, NL_CHUNKS, LA_G_NL in *; lia) R11
      ltac:(rewrite R18, Hn0; reflexivity) ltac:(lia) ltac:(unfold LA_G_NL in *; lia)
      ltac:(unfold NL_CHUNK_MAX, NL_CHUNKS, NK_CHUNK_LEN, LA_G_NL in *; lia) Hkd Hkn).
    intros regs' mem' md' HI' Hs' H15' H16' H17' Hcp UN HN.
    exact (kd_fin ci a al l aa i il l' k regs mem md regs' mem' md' K504 HI Hrs0 Hrat H21 H24 H25 H26 Ham Hkd Hkn Hci Hi
      Hl Hil HI'
      (tt_same_trans _ _ _ RK Hs') H15' H16' H17' Hcp UN HN).
  - (* n > 0: the NUL scan from k = 0 *)
    apply Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK tk_span TP_SK; [tt_awr0 |].
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms2 end.
    tt_ro HF Em2. pmkst HS. rewrite Em2, Em1 in HJ |- *.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md2 := m) in * end.
    lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?msr =>
      pose proof (regs_kept_of_st_ok_pi E1 ss1 msr regs (tk_ext c ++ xs) tt_KL HS
        ltac:(split; [intros ?n ?Hn; rewrite ?ew_ewset_other by lia; unfold tk_E; apply Eimg_low; unfold A_TEXT; lia
                     | reflexivity])
        ltac:(vm_compute; reflexivity)) as RK end.
    cbn [ms_regs restrict] in RK.
    tt_reg HS (11%bv : bv 5) R11. tt_reg HS (12%bv : bv 5) R12. tt_reg HS (18%bv : bv 5) R18.
    tt_reg HS (13%bv : bv 5) R13.
    rewrite denot_lit_U, Usrc in R11, R13.
    rewrite denot_lit_U, (U_atom_off _ 26 l' (-4) E26 ltac:(lia) ltac:(lia)) in R12.
    assert (HI2 : tk_inv SK B c (ms_regs ms2) mem md2).
    { apply (tk_inv_step SK B c HC regs mem md (ms_regs ms2) mem md2 (fun _ => False) HI HJ).
      - unfold md2. repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
      - unfold md2. repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
      - intros x _ _. reflexivity.
      - intros x [].
      - intros x Hp. exact Hp.
      - exact (RK 2%bv ltac:(tt_in)).
      - exact (RK 3%bv ltac:(tt_in)).
      - exact (RK 4%bv ltac:(tt_in)). }
    apply (kd_sk (slice (tk_ck c ci) (i + RTA_HDR) (l' - RTA_HDR)) (tk_b ci + 4 + i) (l' - 4) mem Hlen
      (tt_pay_mem regs mem md ci i l' HI Hci Hi ltac:(lia) ltac:(lia)) ltac:(unfold LA_G_NL in *; lia)
      ltac:(unfold NL_CHUNK_MAX, NL_CHUNKS, NK_CHUNK_LEN, LA_G_NL in *; lia)
      (Z.to_nat (l' - 4)) 0 (ms_regs ms2) md2 ltac:(lia) ltac:(lia) ltac:(lia) HI2
      ltac:(rewrite (RK 23%bv ltac:(tt_in)); exact H23) R11 R12 R18 ltac:(rewrite R13; unfold w64; f_equal; lia)).
    intros regs3 md3 HI3 Hs3 H11' H18'.
    pose proof (tt_same_trans _ _ _ RK Hs3) as Hs03.
    apply (kd_ca (Z.of_nat (nul_at (slice (tk_ck c ci) (i + RTA_HDR) (l' - RTA_HDR)))) (tk_b ci + 4 + i) (tk_b ci)
      regs3 mem md3 HI3 (tt_rs0_same _ _ Hs03 Hrs0) ltac:(rewrite (Hs03 20%bv ltac:(tt_in)); exact H20) HSP
      ltac:(lia) ltac:(unfold NL_CHUNK_MAX, NL_CHUNKS, LA_G_NL in *; lia) H11' H18' ltac:(lia)
      ltac:(unfold LA_G_NL in *; lia) ltac:(unfold NL_CHUNK_MAX, NL_CHUNKS, NK_CHUNK_LEN, LA_G_NL in *; lia) Hkd Hkn).
    intros regs' mem' md' HI' Hs' H15' H16' H17' Hcp UN HN.
    exact (kd_fin ci a al l aa i il l' k regs mem md regs' mem' md' K504 HI Hrs0 Hrat H21 H24 H25 H26 Ham Hkd Hkn Hci Hi
      Hl Hil HI'
      (tt_same_trans _ _ _ Hs03 Hs') H15' H16' H17' Hcp UN HN).
Qed.
End w.
