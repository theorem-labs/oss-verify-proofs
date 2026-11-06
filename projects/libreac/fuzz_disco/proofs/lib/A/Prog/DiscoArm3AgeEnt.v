(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 959 of its 988 lines of code are new or changed and 40 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntObs.v; 413 of its 459 lines of code are new or changed and 942 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop YE00 YC5d YCbp.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame YC81.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC45 YC1i ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoArm3 DiscoArm3AgeSt DiscoArm3AgeKit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require ReacDiscoTableAge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv disco_table_c reac_disco_table_age_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require PropExec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition e_fcs : list YP09.chunk :=
  [YP09.mkChunk 2544 (CVal 4 (SOff 563 0)); YP09.mkChunk 2552 (CVal 4 (SOff 564 0));
   YP09.mkChunk 2200 (CVal 8 (SOff 565 0)); YP09.mkChunk 2248 (CVal 8 (SOff 566 0));
   YP09.mkChunk 2296 (CVal 8 (SOff 567 0)); YP09.mkChunk 2344 (CVal 8 (SOff 568 0));
   YP09.mkChunk 2392 (CVal 8 (SOff 569 0)); YP09.mkChunk 2440 (CVal 8 (SOff 570 0));
   YP09.mkChunk 2488 (CVal 8 (SOff 571 0)); YP09.mkChunk 2536 (CVal 8 (SOff 572 0))].
Definition e_acs : list YP09.chunk := [YP09.mkChunk 232 (CVal 8 (SOff 573 0))].
Definition e_ex (T : list byte) (i : Z) : list word :=
  [Z_to_bv 64 (u_at T 384 4); Z_to_bv 64 (u_at T 392 4);
   Z_to_bv 64 (last_of T 0); Z_to_bv 64 (last_of T 1); Z_to_bv 64 (last_of T 2); Z_to_bv 64 (last_of T 3);
   Z_to_bv 64 (last_of T 4); Z_to_bv 64 (last_of T 5); Z_to_bv 64 (last_of T 6); Z_to_bv 64 (last_of T 7);
   Z_to_bv 64 i].
Definition e_win (r : YP09.region) : YP09.region :=
  match YP09.r_base r with
  | Some 60%nat => set_window r 224 256
  | Some 516%nat => set_window r 0 0
  | Some 529%nat => set_window r 0 0
  | _ => r
  end.
Definition e_rs : smem := map e_win (d_kregions dsh_loop e_acs e_fcs ++ []).
Definition e_ss0 : sstate := mkSS ARM3_OFF (sr_set a3_sr 14%bv (SOff 516 2160)) e_rs None (d_facts [] []).
Definition e_conds (k : nat) : list acond :=
  match k with
  | O => []
  | S k' => map (fun j : nat => mkAC BC_NE (SOff 563 (- Z.of_nat (S j))) (SLit 0)) (seq 0 k') ++
      [mkAC BC_EQ (SOff 563 (- Z.of_nat k)) (SLit 0)]
  end.
Definition st_bit (a : nat) : sv :=
  SAlu ALU_AND (SAlu ALU_SLTU (SOff a 0) (SOff 542 0))
    (SAlu ALU_SLTU (SLit 5000000000) (SAlu ALU_ADD (SOff 542 0) (SMd M_MUL (SOff a 0) (SLit (-1))))).
Fixpoint st_chain (k : nat) : sv :=
  match k with O => SLit 0 | S k' => SAlu ALU_ADD (st_chain k') (st_bit (565 + k')) end.
Definition fin_regs (k : nat) : list (bv 5 * sv) :=
  [(1%bv, SOff 240 2488); (2%bv, SOff 60 0); (3%bv, SOff 534 0); (4%bv, SOff 535 0); (8%bv, SOff 2 0);
   (9%bv, SOff 60 0); (10%bv, SOff 516 2160); (11%bv, SOff 542 0); (18%bv, SOff 32 0); (20%bv, SLit WS_MASK);
   (21%bv, SExt true 32 (SOff 564 0)); (22%bv, st_chain k); (23%bv, SOff 563 0); (24%bv, SOff 516 2160);
   (25%bv, SLit 32); (26%bv, SLit 5000000000); (27%bv, SOff 558 0)].
Definition fin_chunks : list YP09.chunk :=
  [YP09.mkChunk 224 (CVal 8 (SOff 538 0)); YP09.mkChunk 248 (CVal 8 (SOff 547 0)); YP09.mkChunk 232 (CVal 8 (SOff 573 0))].
Definition fin_ok (k : nat) (ss : sstate) : bool :=
  (match ss_resv ss with None => true | Some _ => false end) && d_land_chk dsh_loop (ss_mem ss) &&
  forallb (fun p => sv_eqb (sr_get (ss_regs ss) (fst p)) (snd p)) (fin_regs k) &&
  forallb (fun c => existsb (fun r => obase_eqb (YP09.r_base r) (Some 60%nat) && existsb (chunk_eqb c) (YP09.r_chunks r))
    (ss_mem ss)) fin_chunks.
Definition win_ok (rs : smem) : bool :=
  forallb (fun r => (YP09.r_whi r <=? YP09.r_wlo r) ||
    (obase_eqb (YP09.r_base r) (Some 60%nat) && (224 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 256))) rs.

Lemma val8_mod : forall segs m a v, val_mem segs m a 8 (v mod 2 ^ 64) -> val_mem segs m a 8 v.
Proof.
intros segs m a v H kk Hk. rewrite (H kk Hk). do 2 f_equal.
unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma bv64_mod : forall v, Z_to_bv 64 (v mod 2 ^ 64) = Z_to_bv 64 v.
Proof.
intros v. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_mod. lia.
Qed.

Lemma u_rng : forall (T : list byte) k n, 0 <= k -> (Z.to_nat k + n <= length T)%nat ->
  0 <= u_at T k n < 2 ^ (8 * Z.of_nat n).
Proof.
intros T k n Hk Hn. unfold u_at.
assert (LS : length (sub T k n) = n) by (unfold sub; rewrite length_firstn, length_skipn; lia).
pose proof (PropExec.bytes_le_to_Z_bound (sub T k n)) as Hb. rewrite LS in Hb.
pose proof (PropExec.bytes_le_to_Z_nonneg (sub T k n)) as Hb0. lia.
Qed.

Lemma u_rng4 : forall (T : list byte) k, 0 <= k -> (Z.to_nat k + 4 <= length T)%nat -> 0 <= u_at T k 4 < 2 ^ 32.
Proof. intros T k Hk Hn. exact (u_rng T k 4 Hk Hn). Qed.

Lemma u_rng8 : forall (T : list byte) k, 0 <= k -> (Z.to_nat k + 8 <= length T)%nat -> 0 <= u_at T k 8 < 2 ^ 64.
Proof. intros T k Hk Hn. exact (u_rng T k 8 Hk Hn). Qed.

Lemma st_bit_U : forall E a L now, ew E a = Z_to_bv 64 L -> ew E 542 = Z_to_bv 64 now ->
  0 <= L < 2 ^ 64 -> 0 <= now < 2 ^ 64 ->
  U E (st_bit a) = if (L <? now) && (5000000000 <? now - L) then 1 else 0.
Proof.
intros E a L now HL HN RL RN. unfold st_bit.
rewrite !U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
rewrite (U_atom E a L HL RL), (U_atom E 542 now HN RN), !U_SLit.
change (zcanon (-1)) with (2 ^ 64 - 1). change (zcanon 5000000000) with 5000000000.
assert (Hm : zcanon (now + zcanon (L * (2 ^ 64 - 1))) = (now - L) mod 2 ^ 64).
{ unfold zcanon, M64. rewrite Z.add_mod_idemp_r by lia.
  replace (now + L * (2 ^ 64 - 1)) with (now - L + L * 2 ^ 64) by ring. apply Z_mod_plus_full. }
rewrite Hm.
destruct (L <? now) eqn:Q1.
- apply Z.ltb_lt in Q1. rewrite (Z.mod_small (now - L)) by lia.
  destruct (5000000000 <? now - L); cbn [andb]; vm_compute; reflexivity.
- cbn [andb]. rewrite (zcanon_id 0) by (unfold M64; lia). rewrite Z.land_0_l. vm_compute. reflexivity.
Qed.

Lemma st_chain_U : forall E (T : list byte) now (k : nat),
  (forall j, (j < k)%nat ->
     ew E (565 + j) = Z_to_bv 64 (last_of T (Z.of_nat j)) /\ 0 <= last_of T (Z.of_nat j) < 2 ^ 64) ->
  ew E 542 = Z_to_bv 64 now -> 0 <= now < 2 ^ 64 -> (k <= 8)%nat ->
  U E (st_chain k) = age_count (fun j => disco_stale T j now) k.
Proof.
intros E T now k HL HN RN Hk. revert HL Hk. induction k as [|k IH]; intros HL Hk.
- cbn [st_chain age_count]. rewrite U_SLit. reflexivity.
- cbn [st_chain age_count]. rewrite U_SAlu. cbn [zalu_raw].
  rewrite IH by (first [intros j Hj; apply HL; lia | lia]).
  destruct (HL k ltac:(lia)) as [HLk RLk].
  rewrite (st_bit_U E (565 + k) (last_of T (Z.of_nat k)) now HLk HN RLk RN).
  unfold disco_stale, REAC_DISCO_STALE_NS.
  assert (B0 : 0 <= age_count (fun j => (last_of T j <? now) && (5000000000 <? now - last_of T j)) k <= Z.of_nat k).
  { clear. induction k as [|k IH]; cbn [age_count]; [lia|]. destruct (_ && _); lia. }
  apply zcanon_id. unfold M64. destruct (_ && _); lia.
Qed.

Lemma in_wrange_win : forall E rs a, win_ok rs = true -> in_wrange E rs a ->
  bv_unsigned (ew E 60) + 224 <= a < bv_unsigned (ew E 60) + 256.
Proof.
intros E rs a H (r & Hin & Ha). unfold win_ok in H. rewrite forallb_forall in H. specialize (H r Hin).
apply orb_prop in H as [H|H]; [apply Z.leb_le in H; lia|].
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply YP09.obase_eqb_eq in H1. rewrite H1 in Ha. cbn [base_val] in Ha. apply Z.leb_le in H2, H3. lia.
Qed.

Lemma fin_get : forall (l : list (bv 5 * sv)) ss j r e,
  forallb (fun p => sv_eqb (sr_get (ss_regs ss) (fst p)) (snd p)) l = true -> nth_error l j = Some (r, e) ->
  sr_get (ss_regs ss) r = e.
Proof.
intros l ss j r e H Hj. apply nth_error_In in Hj. rewrite forallb_forall in H. specialize (H _ Hj).
cbn [fst snd] in H. apply sv_eqb_eq. exact H.
Qed.

Lemma chunk_in_val : forall segs E m rs od e v,
  Forall (region_ok segs E m) rs ->
  existsb (fun r => obase_eqb (YP09.r_base r) (Some 60%nat) &&
    existsb (chunk_eqb (YP09.mkChunk od (CVal 8 e))) (YP09.r_chunks r)) rs = true ->
  sv_denot E e = Z_to_bv 64 v ->
  val_mem segs m (bv_unsigned (ew E 60) + od) 8 v.
Proof.
intros segs E m rs od e v HF H He. apply existsb_exists in H as (r & Hin & Hr).
apply andb_prop in Hr as [Hb Hc]. apply YP09.obase_eqb_eq in Hb. apply existsb_exists in Hc as (c & Hcin & Hce).
apply chunk_eqb_eq in Hce. subst c.
pose proof (proj1 (Forall_forall _ _) HF r Hin) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hcin) as Hck. rewrite Hb in Hck. cbn [base_val] in Hck.
apply val8_mod. change 8%nat with (N.to_nat 8).
apply (val_of_chunk_ok segs E m _ od 8%N e (v mod 2 ^ 64) Hck).
- rewrite He. symmetry. apply bv64_mod.
- pose proof (Z.mod_pos_bound v (2 ^ 64) ltac:(lia)). cbn. lia.
- cbn. lia.
Qed.

Lemma fin_chunk : forall rs c, forallb (fun c => existsb (fun r => obase_eqb (YP09.r_base r) (Some 60%nat) &&
    existsb (chunk_eqb c) (YP09.r_chunks r)) rs) fin_chunks = true -> In c fin_chunks ->
  existsb (fun r => obase_eqb (YP09.r_base r) (Some 60%nat) && existsb (chunk_eqb c) (YP09.r_chunks r)) rs = true.
Proof. intros rs c H Hc. rewrite forallb_forall in H. exact (H c Hc). Qed.

Lemma e_last : forall (T : list byte) i j, (j < 8)%nat ->
  nth (2 + j) (e_ex T i) (Z_to_bv 64 0) = Z_to_bv 64 (last_of T (Z.of_nat j)).
Proof. intros T i j Hj. do 8 (destruct j as [|j]; [reflexivity|]). lia. Qed.

Lemma zbv_zcanon : forall x, Z_to_bv 64 (zcanon x) = Z_to_bv 64 x.
Proof. intros x. unfold zcanon, M64. apply bv64_mod. Qed.

Ltac kfeed H :=
  repeat lazymatch type of H with
  | AR_laws _ _ -> _ => let X := lazymatch goal with X : AR_laws _ _ |- _ => X end in specialize (H X)
  | PALib _ -> _ => let X := lazymatch goal with X : PALib _ |- _ => X end in specialize (H X)
  | frame_flag_lawP _ _ -> _ => let X := lazymatch goal with X : frame_flag_lawP _ _ |- _ => X end in specialize (H X)
  | d_seat_stmt _ _ _ _ _ _ -> _ => let X := lazymatch goal with X : d_seat_stmt _ _ _ _ _ _ |- _ => X end in specialize (H X)
  | d_facts_stmt _ _ _ _ _ _ -> _ => let X := lazymatch goal with X : d_facts_stmt _ _ _ _ _ _ |- _ => X end in specialize (H X)
  | d_land_stmt _ _ _ _ _ _ -> _ => let X := lazymatch goal with X : d_land_stmt _ _ _ _ _ _ |- _ => X end in specialize (H X)
  | d_body_keep_stmt _ -> _ => let X := lazymatch goal with X : d_body_keep_stmt _ |- _ => X end in specialize (H X)
  end.

Ltac win HS n lo hi :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let RO := fresh "RO" in
pose proof (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) as RO;
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r lo hi) HS ltac:(vm_compute; reflexivity) eq_refl
  ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r lo hi RO ltac:(let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho;
     first [ exfalso; lia | apply (proj1 (proj2 (proj2 RO))); cbn [YP09.r_wlo YP09.r_whi]; lia ]))) as HS3;
clear HS RO; rename HS3 into HS; norm_ss HS end.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma e_atom : forall cx E regs ex j a, a = (563 + j)%nat -> (j < length ex)%nat ->
  ew (d_env cx E (a3_vals regs ex)) a = nth j ex (Z_to_bv 64 0).
Proof.
intros cx E regs ex j a -> Hj.
replace (563 + j)%nat with (AT_X + (32 + j))%nat by (unfold AT_X; lia).
rewrite d_env_x by (unfold a3_vals; rewrite length_app, length_map, length_seq; lia).
unfold a3_vals. rewrite app_nth2 by (rewrite length_map, length_seq; lia).
rewrite length_map, length_seq. replace (32 + j - 32)%nat with j by lia. reflexivity.
Qed.

Lemma pi_add_conds : forall (fq : YK11.FPState) E ss ms l,
  st_ok_pi (fx := fq) SEGS VAL E ss ms -> Forall (acond_ok E) l ->
  st_ok_pi (fx := fq) SEGS VAL E (fold_left add_cond l ss) ms.
Proof.
intros fq E ss ms l. revert ss. induction l as [|c l IH]; intros ss HS Hl; cbn [fold_left]; [exact HS|].
inversion Hl as [|c' l' Hc Hl']; subst. apply IH; [|exact Hl'].
destruct c as [c a b]. destruct ss. exact (st_ok_add_cond SEGS E _ ms c a b HS Hc).
Qed.

Lemma pcall_pi : forall (fq : YK11.FPState) E ss ms (s : dsym),
  st_ok (fx := fq) SEGS E ss ms -> ss_pc ss = SIGMA s ->
  st_ok_pi (fx := fq) SEGS VAL E (setpc ss (SIGMA s - BASE)) ms.
Proof.
intros fq E ss ms s HS Hpc. destruct ss as [p0 r0 f0 m0 v0 g0]. simpl in Hpc. subst p0.
apply (a3_pcall_pi fq E _ ms s). exact HS.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DBKEEP : d_body_keep_stmt B.

Lemma t_chunk : forall E (m : word -> option byte) (T : list byte) FB a (w : N) k,
  garr8 SEGS m (FB + 2160) (map (fun b : byte => bv_unsigned b) T) -> length T = 400%nat ->
  ew E a = Z_to_bv 64 (u_at T k (N.to_nat w)) -> 0 <= k -> (Z.to_nat k + N.to_nat w <= 400)%nat -> Z.of_N w <= 8 ->
  YP09.chunk_ok SEGS E m FB (YP09.mkChunk (2160 + k) (CVal w (SOff a 0))).
Proof.
intros E m T FB a w k HG HL Ha Hk Hkw Hw.
apply (chunk_ok_val SEGS E m FB (2160 + k) w (SOff a 0) (u_at T k (N.to_nat w))).
- rewrite sv_denot_SOff0. exact Ha.
- pose proof (u_rng T k (N.to_nat w) Hk ltac:(lia)) as R. rewrite N_nat_Z in R. exact R.
- exact Hw.
- replace (FB + (2160 + k)) with (FB + 2160 + k) by lia.
  apply (ReacDiscoTableAge.age_val m T (FB + 2160) k (N.to_nat w) HG Hk). lia.
Qed.

Theorem a3_e_ent : e_ent_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W c HIN. pose proof HIN as HIN0.
destruct HIN as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm0 & HB & HJ & HFR & Hk & Hnev & Hmo & Hacc &
  Hi & Hn & Hnow & Hop & Hop3 & HR & HSP0 & HBODY).
pose proof HBODY as (T0 & G0 & Lk0 & H0 & _ & _ & HOBJ & _).
destruct HOBJ as (HTl & HTg & HTok & _).
pose proof HR as (HrL & R7 & R11 & R14 & R16 & R27).
destruct HSP0 as (Hs232 & Hs344).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact HB | split; [exact HJ | exact HFR]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HC)
  as (G16 & GSlo & GShi & GF4 & GFc & _ & _ & GF32 & _).
pose proof alloc_ceiling_val as Hac.
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA & GA32). unfold MFRAME in GA.
unfold LLVMF_STK in GSlo.
pose proof (proj1 HTok) as HN8. unfold tbl_T1 in HN8.
assert (U563 : u_at T0 384 4 = n_of T0) by (apply ReacDiscoTableAge.u_of_n; [exact HTl | lia]).
assert (HTg' : garr8 SEGS (rd W mem3) (d_FB cx + 2160) (map (fun b : byte => bv_unsigned b) T0)) by exact HTg.
match goal with |- SRr _ _ _ ?Q => set (QQ := Q) end.
pose proof (a3_seat B MT XM_LIB RLO RHI tfib_K) as SEAT. kfeed SEAT.
destruct (SEAT fq cx ARM3_OFF h n [] dsh_loop ly3 S3 W regs mem3 md3 k (e_ex T0 i) e_acs e_fcs [] [] [] HC HrL HBODY)
  as (E & HdE & HS).
{ intros E HE. split; [exact I|]. split; [exact I|]. split; [|split; [|split; [constructor|split; [exact I|constructor]]]].
  - apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ (d_A cx) 232 8 (SOff 573 0) i).
    + rewrite sv_denot_SOff0, (e_atom cx E regs (e_ex T0 i) 10 573 eq_refl ltac:(cbn; lia)). reflexivity.
    + unfold MAX_OPS in Hi. cbn. lia.
    + cbn. lia.
    + exact Hs232.
  - unfold e_fcs. repeat apply Forall_cons; try apply Forall_nil.
    + apply (t_chunk _ _ T0 _ 563 4 384 HTg' HTl); [|lia | lia | lia].
      rewrite (e_atom cx E regs (e_ex T0 i) 0 563 eq_refl ltac:(cbn; lia)). reflexivity.
    + apply (t_chunk _ _ T0 _ 564 4 392 HTg' HTl); [|lia | lia | lia].
      rewrite (e_atom cx E regs (e_ex T0 i) 1 564 eq_refl ltac:(cbn; lia)). reflexivity.
    + apply (t_chunk _ _ T0 _ 565 8 40 HTg' HTl); [|lia | lia | lia].
      rewrite (e_atom cx E regs (e_ex T0 i) 2 565 eq_refl ltac:(cbn; lia)). reflexivity.
    + apply (t_chunk _ _ T0 _ 566 8 88 HTg' HTl); [|lia | lia | lia].
      rewrite (e_atom cx E regs (e_ex T0 i) 3 566 eq_refl ltac:(cbn; lia)). reflexivity.
    + apply (t_chunk _ _ T0 _ 567 8 136 HTg' HTl); [|lia | lia | lia].
      rewrite (e_atom cx E regs (e_ex T0 i) 4 567 eq_refl ltac:(cbn; lia)). reflexivity.
    + apply (t_chunk _ _ T0 _ 568 8 184 HTg' HTl); [|lia | lia | lia].
      rewrite (e_atom cx E regs (e_ex T0 i) 5 568 eq_refl ltac:(cbn; lia)). reflexivity.
    + apply (t_chunk _ _ T0 _ 569 8 232 HTg' HTl); [|lia | lia | lia].
      rewrite (e_atom cx E regs (e_ex T0 i) 6 569 eq_refl ltac:(cbn; lia)). reflexivity.
    + apply (t_chunk _ _ T0 _ 570 8 280 HTg' HTl); [|lia | lia | lia].
      rewrite (e_atom cx E regs (e_ex T0 i) 7 570 eq_refl ltac:(cbn; lia)). reflexivity.
    + apply (t_chunk _ _ T0 _ 571 8 328 HTg' HTl); [|lia | lia | lia].
      rewrite (e_atom cx E regs (e_ex T0 i) 8 571 eq_refl ltac:(cbn; lia)). reflexivity.
    + apply (t_chunk _ _ T0 _ 572 8 376 HTg' HTl); [|lia | lia | lia].
      rewrite (e_atom cx E regs (e_ex T0 i) 9 572 eq_refl ltac:(cbn; lia)). reflexivity. }
{ vm_compute. reflexivity. }
pose proof (d_E_env cx E (a3_vals regs (e_ex T0 i)) HdE) as HdEx.
pose proof (a3_env_img cx E (a3_vals regs (e_ex T0 i)) HdE) as HEI.
set (Ex := d_env cx E (a3_vals regs (e_ex T0 i))) in HS, HdEx, HEI.
pose proof HdEx as (EER & E32 & _ & E60 & EF & _).
change AT_A with 60%nat in E60. change AT_F with 516%nat in EF.
assert (EA60u : bv_unsigned (ew Ex 60) = d_A cx) by (rewrite E60; unfold w64; apply unsigned_lit_small; lia).
assert (EFu : bv_unsigned (ew Ex 516) = d_FB cx) by (rewrite EF; unfold w64; apply unsigned_lit_small; lia).
assert (D14 : sv_denot Ex (SOff 516 2160) = getr regs 14%bv).
{ cbn [sv_denot]. rewrite EFu, R14. unfold w64, d_obj, dobj_off. reflexivity. }
pose proof (ast_ok_pi_set_reg_fp Ex _ _ (14%bv : bv 5) (SOff 516 2160) HS ltac:(vm_compute; reflexivity)
  ltac:(exact D14)) as HS1.
clear HS. rename HS1 into HS. norm_ss HS.
win HS 516%nat 0 0. win HS 529%nat 0 0. win HS 60%nat 224 256.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
  assert (Heq : ssx = e_ss0) by (vm_compute; reflexivity); rewrite Heq in HS; clear Heq end.
assert (AWR : awr_ok Ex e_rs LLVMF_STK (d_S cx) [] (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3
  [(DFRAME_CLASS, c_fpos cx)]).
{ intros a Ha. pose proof (in_wrange_win Ex e_rs a ltac:(vm_compute; reflexivity) Ha) as Hb.
  rewrite EA60u in Hb. left. unfold LLVMF_STK. lia. }
assert (E542 : ew Ex 542 = Z_to_bv 64 now)
  by exact (eq_trans (a3_env_reg cx E regs (e_ex T0 i) 11%bv 542 eq_refl) R11).
assert (LAST : forall j, (j < 8)%nat ->
  ew Ex (565 + j) = Z_to_bv 64 (last_of T0 (Z.of_nat j)) /\ 0 <= last_of T0 (Z.of_nat j) < 2 ^ 64).
{ intros j Hj. split.
  - exact (eq_trans (e_atom cx E regs (e_ex T0 i) (2 + j) (565 + j) ltac:(lia) ltac:(cbn; lia)) (e_last T0 i j Hj)).
  - unfold last_of. exact (u_rng8 T0 (48 * Z.of_nat j + 40) ltac:(lia) ltac:(lia)). }
assert (E563 : ew Ex 563 = Z_to_bv 64 (u_at T0 384 4))
  by exact (e_atom cx E regs (e_ex T0 i) 0 563 eq_refl ltac:(cbn; lia)).
assert (E564 : ew Ex 564 = Z_to_bv 64 (u_at T0 392 4))
  by exact (e_atom cx E regs (e_ex T0 i) 1 564 eq_refl ltac:(cbn; lia)).
assert (LAND : forall (kk : nat) (ssc : sstate) (ms' : machine_state) mat,
  n_of T0 = Z.of_nat kk -> fin_ok kk ssc = true ->
  st_ok (fx := fq) SEGS Ex ssc (restrict (w_H W) ms') -> ss_pc ssc = SIGMA DS_reac_disco_table_age ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms') (with_vm_backing (m_vm_lazy md3) mat md3) k ->
  frame_of Ex e_rs (rd W mem3) (rd W (ms_mem ms')) ->
  mem_grows (rd W mem3) (rd W (ms_mem ms')) ->
  SRr SEGS W (mkCfg ms' (with_vm_backing (m_vm_lazy md3) mat md3)) QQ).
{ intros kk ssc ms' mat HkN Hfin HSc Hpc HJc HFc HGc.
  apply SRr_ret. unfold QQ. exists T0. unfold p_age. split.
  { unfold a3_from. split; [exact HIN0|]. split; [apply wle_refl|]. split; [exact HTl|].
    exists fq, regs, mem3, md3. split; [reflexivity | exact HTg]. }
  unfold fin_ok in Hfin. apply andb_prop in Hfin as [Hfin Hch]. apply andb_prop in Hfin as [Hfin Hrg].
  apply andb_prop in Hfin as [Hrv Hland].
  destruct (ss_resv ssc) eqn:Hresv; [discriminate Hrv|]. clear Hrv.
  pose proof (pcall_pi fq Ex ssc (restrict (w_H W) ms') DS_reac_disco_table_age HSc Hpc) as HSpi.
  rewrite (pa_sigma_reac_disco_table_age (PI := PI)) in HSpi.
  replace (BASE + AF_reac_disco_table_age - BASE) with AF_reac_disco_table_age in HSpi by lia.
  assert (GR : forall j r e, nth_error (fin_regs kk) j = Some (r, e) -> getr (ms_regs ms') r = sv_denot Ex e).
  { intros j r e Hj. rewrite (st_ok_restrict_reg SEGS (w_H W) Ex ssc ms' r HSc).
    rewrite (fin_get _ ssc j r e Hrg Hj). reflexivity. }
  pose proof (st_ok_mem_ok SEGS Ex _ _ HSc) as (_ & HRG & _).
  change (ms_mem (restrict (w_H W) ms')) with (rd W (ms_mem ms')) in HRG.
  assert (HKEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 224 <= a < d_A cx + 256) ->
    aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) mem3 a).
  { apply (a3_kept_frame Ex e_rs (w_H W) mem3 (ms_mem ms') (d_A cx + 224) (d_A cx + 256) HFc).
    intros a Ha. pose proof (in_wrange_win Ex e_rs a ltac:(vm_compute; reflexivity) Ha) as Hb.
    rewrite EA60u in Hb. exact Hb. }
  assert (V232 : val_mem SEGS (rd W (ms_mem ms')) (d_A cx + 232) 8 i).
  { rewrite <- EA60u. apply (chunk_in_val SEGS Ex _ (ss_mem ssc) 232 (SOff 573 0) i HRG).
    - apply (fin_chunk _ _ Hch). cbn [fin_chunks In]. right. right. left. reflexivity.
    - rewrite sv_denot_SOff0. exact (e_atom cx E regs (e_ex T0 i) 10 573 eq_refl ltac:(cbn; lia)). }
  assert (V224 : val_mem SEGS (rd W (ms_mem ms')) (d_A cx + 224) 8 n).
  { rewrite <- EA60u. apply (chunk_in_val SEGS Ex _ (ss_mem ssc) 224 (SOff 538 0) n HRG).
    - apply (fin_chunk _ _ Hch). cbn [fin_chunks In]. left. reflexivity.
    - rewrite sv_denot_SOff0. exact (eq_trans (a3_env_reg cx E regs (e_ex T0 i) 7%bv 538 eq_refl) R7). }
  assert (V248 : val_mem SEGS (rd W (ms_mem ms')) (d_A cx + 248) 8 (d_cur cx n)).
  { rewrite <- EA60u. apply (chunk_in_val SEGS Ex _ (ss_mem ssc) 248 (SOff 547 0) (d_cur cx n) HRG).
    - apply (fin_chunk _ _ Hch). cbn [fin_chunks In]. right. left. reflexivity.
    - rewrite sv_denot_SOff0. exact (eq_trans (a3_env_reg cx E regs (e_ex T0 i) 16%bv 547 eq_refl) R16). }
  assert (V344 : val_mem SEGS (rd W (ms_mem ms')) (d_A cx + 344) 8 now).
  { apply (a3_val_mem_keep W mem3 (ms_mem ms') (d_A cx + 224) (d_A cx + 256) (d_A cx + 344) 8 now HKEEP);
      [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
      | intros x Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; lia | exact Hs344]. }
  assert (VT : garr8 SEGS (rd W (ms_mem ms')) (d_obj cx OT) (map (fun b : byte => bv_unsigned b) T0)).
  { apply (a3_garr8_keep W mem3 (ms_mem ms') (d_A cx + 224) (d_A cx + 256) (d_obj cx OT) _ HKEEP);
      [unfold d_obj, dobj_off; lia | rewrite length_map, HTl; unfold d_obj, dobj_off; cbn; lia
      | intros x Hx; rewrite length_map, HTl in Hx; unfold d_obj, dobj_off in Hx; cbn in Hx; lia | exact HTg]. }
  assert (Hacc' : acc <= ACC_HEAD MT i + mo_malloc MT REC_MAX).
  { clear - Hacc MT_TRIV. rewrite MT_TRIV in *. cbn [mo_malloc ameter_triv]. lia. }
  pose proof (a3_land_keep B MT XM_LIB RLO RHI tfib_K) as LK. kfeed LK.
  eapply (LK fq cx AF_reac_disco_table_age (EV_HEAD i) h i n n now _ _ W ly3 S3 mem3 _ k acc Ex
    (setpc ssc AF_reac_disco_table_age) ms' (d_A cx + 224) (d_A cx + 256) Hfrm0 HB HJc HFR Hk Hnev Hmo Hacc' Hi
    ltac:(lia) Hnow HBODY HSpi ltac:(cbn [setpc ss_resv]; exact Hresv) eq_refl HdEx (d_env_fl cx E _)
    Hland ltac:(unfold LLVMF_STK; lia) ltac:(lia) HKEEP (fun a _ => a3_present_grows (w_H W) mem3 (ms_mem ms') HGc a)
    ltac:(intros a Ha; lia)); cbv beta.
  - pose proof (GR 1%nat 2%bv _ eq_refl) as Q2. pose proof (GR 2%nat 3%bv _ eq_refl) as Q3.
    pose proof (GR 3%nat 4%bv _ eq_refl) as Q4. pose proof (GR 4%nat 8%bv _ eq_refl) as Q8.
    pose proof (GR 5%nat 9%bv _ eq_refl) as Q9. pose proof (GR 8%nat 18%bv _ eq_refl) as Q18.
    pose proof (GR 9%nat 20%bv _ eq_refl) as Q20. pose proof (GR 14%nat 25%bv _ eq_refl) as Q25.
    destruct HrL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25).
    unfold d_rL.
    split; [unfold spZ; rewrite Q2, sv_denot_SOff0, E60; unfold w64; apply unsigned_lit_small; lia|].
    split; [rewrite Q3, sv_denot_SOff0; exact (eq_trans (a3_env_reg cx E regs (e_ex T0 i) 3%bv 534 eq_refl) Hgp)|].
    split; [rewrite Q4, sv_denot_SOff0; exact (eq_trans (a3_env_reg cx E regs (e_ex T0 i) 4%bv 535 eq_refl) Htp)|].
    split; [rewrite Q8, sv_denot_SOff0, (EER 2%nat 2%bv eq_refl); unfold w64, d_S, spZ;
      rewrite Z_to_bv_bv_unsigned; reflexivity|].
    split; [rewrite Q9, sv_denot_SOff0; exact E60|].
    split; [rewrite Q18, sv_denot_SOff0; exact E32|].
    split; [rewrite Q20; reflexivity|].
    rewrite Q25; reflexivity.
  - pose proof (GR 0%nat 1%bv _ eq_refl) as Q1. pose proof (GR 6%nat 10%bv _ eq_refl) as Q10.
    pose proof (GR 7%nat 11%bv _ eq_refl) as Q11. pose proof (GR 10%nat 21%bv _ eq_refl) as Q21.
    pose proof (GR 11%nat 22%bv _ eq_refl) as Q22. pose proof (GR 12%nat 23%bv _ eq_refl) as Q23.
    pose proof (GR 13%nat 24%bv _ eq_refl) as Q24. pose proof (GR 15%nat 26%bv _ eq_refl) as Q26.
    pose proof (GR 16%nat 27%bv _ eq_refl) as Q27.
    split; [rewrite Q1; exact (codeptr_val Ex 2488 HEI)|].
    split; [rewrite Q10; exact (eq_trans D14 R14)|].
    split; [rewrite Q11, sv_denot_SOff0; exact E542|].
    split.
    { rewrite Q22, denot_lit_U. unfold a3_stale, w64. f_equal.
      rewrite HkN, Nat2Z.id. apply (st_chain_U Ex T0 now kk); [intros j Hj; apply LAST; lia | exact E542 | exact Hnow | lia]. }
    unfold a3_age_regs.
    pose proof (u_rng4 T0 392 ltac:(lia) ltac:(lia)) as R392.
    split.
    { rewrite Q21, denot_lit_U, U_SExt. rewrite (U_atom Ex 564 (u_at T0 392 4) E564) by lia.
      rewrite Z.mod_small by (change (2 ^ Z.of_N 32) with (2 ^ 32); exact R392).
      unfold w64, s32_at. apply zbv_zcanon. }
    split; [rewrite Q23, sv_denot_SOff0, E563, U563; reflexivity|].
    split; [rewrite Q24; exact (eq_trans D14 R14)|].
    split; [rewrite Q26; reflexivity|].
    rewrite Q27, sv_denot_SOff0. exact (eq_trans (a3_env_reg cx E regs (e_ex T0 i) 27%bv 558 eq_refl) R27).
  - unfold d_sp1, d_sp0, a3_t0.
    split; [split; [split; [exact V232 | exact V344] | split; [exact V224 | exact V248]]|].
    split; [exact HTl|]. split; [exact HTok | exact VT].
  - unfold d_sp0. split; [exact V232 | exact V344]. }
assert (HK : exists kk : nat, (kk <= 8)%nat /\ n_of T0 = Z.of_nat kk) by (exists (Z.to_nat (n_of T0)); split; lia).
destruct HK as (kk & Hkk8 & HkkN).
assert (E563k : ew Ex 563 = Z_to_bv 64 (Z.of_nat kk)) by (rewrite E563, U563, HkkN; reflexivity).
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fq) B LAWS).
unfold cfg_at. change (w64 (BASE + ARM3_OFF)) with (Z_to_bv 64 (BASE + ARM3_OFF)).
do 9 (destruct kk as [|kk]; [
  lazymatch type of HkkN with _ = Z.of_nat ?KK =>
  lazymatch type of HS with st_ok_pi _ _ _ ?ss0 ?ms0 =>
  pose proof (st_ok_pi_add_fact Ex ss0 ms0 563 (mkAF (Z.of_nat KK) (Z.of_nat KK) 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E563k; rewrite unsigned_lit_small by (cbn; lia);
          rewrite Z.pow_0_r, Z.mod_1_r; cbn; lia)) as HS2;
  pose proof (pi_add_conds fq Ex _ ms0 (e_conds KK) HS2
    ltac:(cbn [e_conds seq map app];
          repeat (apply Forall_cons; [unfold acond_ok; cbn [ac_c ac_a ac_b sv_denot]; rewrite E563k;
            vm_compute; reflexivity|]); apply Forall_nil)) as HS3;
  clear HS2;
  paj_run_shc RUNP RUNC HS3 HJ;
  [ exact AWR
  | apply (fun Hf => LAND KK _ _ _ HkkN Hf HS3 eq_refl HJ HFr HG); vm_compute; reflexivity ]
  end end | ]).
exfalso. lia.
Qed.

End h.
End f.
End d.
