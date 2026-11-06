(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg RtCells AProto ABase ABytes AModelFacts F_memset F_apoison F_m2s F_annot.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import AKit AKit2 FsKit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::=
  first [ OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.LiaTuning.zify_prune_relevant; OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib.LiaTuning.zify_noeuclid_nosat; Z.euclidean_division_equations_cleanup; xlia zchecker
        | Zify.zify; xlia zchecker ].
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.
(* [comment removed for export] *)
Definition bxs (P : Prop) : Prop := P.
(* [comment removed for export] *)
Definition POISON : Prop := True.       (* [comment removed for export] *)
Definition BYTEST : Prop := True.       (* [comment removed for export] *)
Definition NOPOISON : Prop := True.
Local Ltac box H := lazymatch type of H with ?P => change P with (bxs P) in H end.
Local Tactic Notation "blia" "-" ne_hyp_list(hs) := clear - hs; unfold bxs in *; lia.
Local Tactic Notation "bdlia" "-" ne_hyp_list(hs) := clear - hs; unfold bxs in *; Z.div_mod_to_equations; lia.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sg_mid (full : list byte) (new old : Z) : list byte :=
  firstn (Z.to_nat (shlen (rup8 new))) full
  ++ repeat (Z_to_bv 8 252) (Z.to_nat (shlen (rup8 old) - shlen (rup8 new)))
  ++ skipn (Z.to_nat (shlen (rup8 old))) full.
Definition sg_out (full : list byte) (new old : Z) : list byte :=
  if new mod 8 =? 0 then sg_mid full new old
  else firstn (Z.to_nat (new / 8)) (sg_mid full new old) ++ [Z_to_bv 8 (new mod 8)] ++ skipn (Z.to_nat (new / 8) + 1) (sg_mid full new old).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma CB_len : forall m A n bs, rw_cells bsegs m A [CB n bs] -> length bs = n.
Proof. intros m A n bs [[[WF _] _] _]. cbn in WF. lia. Qed.

Lemma CB_split3 : forall m A n1 n2 n3 full,
  rw_cells bsegs m A [CB (n1 + n2 + n3) full] ->
  rw_cells bsegs m A [CB n1 (firstn n1 full)]
  /\ rw_cells bsegs m (A + Z.of_nat n1) [CB n2 (firstn n2 (skipn n1 full))]
  /\ rw_cells bsegs m (A + Z.of_nat n1 + Z.of_nat n2) [CB n3 (skipn n2 (skipn n1 full))].
Proof.
  intros m A n1 n2 n3 full H.
  pose proof (rw_cells_split_CB bsegs m A [] _ full [] [n1; n2; n3] H ltac:(cbn; lia)) as H3. cbn [app mk_CB_cells] in H3.
  apply (proj1 (rw_cells_app bsegs m A [_] [_; _])) in H3. destruct H3 as [H1 H23].
  cbn [cells_size csize Nat.add] in H23. rewrite Nat.add_0_r in H23.
  apply (proj1 (rw_cells_app bsegs m _ [_] [_])) in H23. destruct H23 as [H2 H3].
  cbn [cells_size csize Nat.add] in H3. rewrite Nat.add_0_r in H3.
  pose proof (CB_len _ _ _ _ H) as L. rewrite firstn_all2 in H3 by (rewrite !length_skipn; lia).
  split; [exact H1|]. split; [exact H2| exact H3].
Qed.

Lemma CB_join3 : forall m A n1 n2 n3 f1 f2 f3,
  rw_cells bsegs m A [CB n1 f1] ->
  rw_cells bsegs m (A + Z.of_nat n1) [CB n2 f2] ->
  rw_cells bsegs m (A + Z.of_nat n1 + Z.of_nat n2) [CB n3 f3] ->
  rw_cells bsegs m A [CB (n1 + n2 + n3) (f1 ++ f2 ++ f3)].
Proof.
  intros m A n1 n2 n3 f1 f2 f3 H1 H2 H3.
  pose proof (CB_len _ _ _ _ H1) as L1. pose proof (CB_len _ _ _ _ H2) as L2. pose proof (CB_len _ _ _ _ H3) as L3.
  assert (H : rw_cells bsegs m A ([CB n1 f1] ++ [CB n2 f2] ++ [CB n3 f3])).
  { apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r.
    apply rw_cells_app. split; [exact H2|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact H3. }
  pose proof (rw_cells_merge bsegs m A [] ([CB n1 f1] ++ [CB n2 f2] ++ [CB n3 f3]) []) as M.
  rewrite !app_nil_r in M. cbn [app] in M, H. specialize (M H). cbn [cells_size cells_bytes csize cbytes Nat.add app] in M.
  rewrite !app_nil_r, Nat.add_0_r in M. rewrite <- ?app_assoc in M. replace (n1 + (n2 + n3))%nat with (n1 + n2 + n3)%nat in M by lia. exact M.
Qed.

Lemma firstn1_skipn_nth : forall (l : list byte) k d, (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l d].
Proof. intros l k. revert l. induction k as [|k IH]; intros [|x l] d H; cbn in *; try lia; [reflexivity| apply IH; lia]. Qed.

Lemma CB_byte : forall m A n full k,
  rw_cells bsegs m A [CB n full] -> (k < n)%nat ->
  rw_cells bsegs m A [CB k (firstn k full)]
  /\ rw_cells bsegs m (A + Z.of_nat k) [C1 (nth k full (Z_to_bv 8 0))]
  /\ rw_cells bsegs m (A + Z.of_nat k + 1) [CB (n - k - 1) (skipn (k + 1) full)].
Proof.
  intros m A n full k H Hk. pose proof (CB_len _ _ _ _ H) as L.
  replace n with (k + 1 + (n - k - 1))%nat in H by lia.
  destruct (CB_split3 m A k 1 (n - k - 1) full H) as (H1 & H2 & H3).
  split; [exact H1|]. split.
  - eapply rw_cells_recast; [exact H2| cbn; tauto| | reflexivity].
    cbn [cells_bytes cbytes app]. rewrite (firstn1_skipn_nth full k (Z_to_bv 8 0)) by lia. reflexivity.
  - replace (A + Z.of_nat k + Z.of_nat 1) with (A + Z.of_nat k + 1) in H3 by lia. rewrite skipn_skipn in H3.
    replace (1 + k)%nat with (k + 1)%nat in H3 by lia. exact H3.
Qed.

Lemma CB_byte_join : forall m A n k f1 b f3,
  rw_cells bsegs m A [CB k f1] -> rw_cells bsegs m (A + Z.of_nat k) [C1 b] -> rw_cells bsegs m (A + Z.of_nat k + 1) [CB (n - k - 1) f3] ->
  (k < n)%nat -> rw_cells bsegs m A [CB n (f1 ++ [b] ++ f3)].
Proof.
  intros m A n k f1 b f3 H1 H2 H3 Hk.
  replace n with (k + 1 + (n - k - 1))%nat by lia. apply CB_join3; [exact H1| | ].
  - eapply rw_cells_recast; [exact H2| cbn; split; [reflexivity| exact I]| cbn; reflexivity| reflexivity].
  - replace (A + Z.of_nat k + Z.of_nat 1) with (A + Z.of_nat k + 1) by lia. exact H3.
Qed.

(* [comment removed for export] *)
Lemma full_byte_read : forall m beg cap full sb,
  beg mod 8 = 0 -> 0 < cap ->
  rw_cells bsegs m (shad beg) [CB (Z.to_nat (shlen (rup8 cap))) full] ->
  nth_error full (Z.to_nat (cap / 8)) = Some sb ->
  ov_read_bytes bsegs m (wa (2147450880 + Z.shiftr (beg + cap) 3)) 1 = Some [sb].
Proof.
  intros m beg cap full sb AL CAP H NTH. pose proof (CB_len _ _ _ _ H) as L.
  destruct H as [[WF BA] _]. cbn [cells_bytes cbytes app] in BA. rewrite app_nil_r in BA.
  replace (2147450880 + Z.shiftr (beg + cap) 3) with (shad beg + cap / 8)
    by (unfold shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  assert (LT : (Z.to_nat (cap / 8) < length full)%nat).
  { destruct (Nat.lt_ge_cases (Z.to_nat (cap / 8)) (length full)) as [LT|GE]; [exact LT|].
    rewrite (proj2 (nth_error_None full (Z.to_nat (cap / 8))) GE) in NTH. discriminate NTH. }
  rewrite (bytes_at_read bsegs m (shad beg) full (cap / 8) 1 BA) by (try lia; Z.div_mod_to_equations; lia).
  f_equal. rewrite <- (firstn_skipn (Z.to_nat (cap / 8)) full) in NTH.
  rewrite nth_error_app2 in NTH by (rewrite length_firstn; lia). rewrite length_firstn, Nat.min_l, Nat.sub_diag in NTH by lia.
  destruct (skipn (Z.to_nat (cap / 8)) full) as [|b r]; [discriminate|]. cbn in NTH. injection NTH as ->. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition annot_sg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (beg cap old new lo : Z) (full : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - ANNOT_STACK, bv_unsigned sp); (shad beg + new / 8, shad beg + shlen (rup8 old))] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (shad beg) [CB (Z.to_nat (shlen (rup8 cap))) (sg_out full new old)].

Lemma annot_sg_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (beg cap old new lo : Z) (full : list byte),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - ANNOT_STACK ->
  poison_cells m -> annot_cells m ->
  a0 = Z_to_bv 64 beg -> a1 = Z_to_bv 64 (beg + cap) -> a2 = Z_to_bv 64 (beg + old) -> a3 = Z_to_bv 64 (beg + new) ->
  beg mod 8 = 0 -> 0 < cap <= 2^40 -> 0 <= new -> new < old -> old <= cap ->
  ablk beg (beg + rup8 cap) -> beg + rup8 cap <= 2^47 ->
  rw_cells bsegs m (shad beg) [CB (Z.to_nat (shlen (rup8 cap))) full] ->
  (cap mod 8 <> 0 -> rdn8 cap < old -> exists sb, nth_error full (Z.to_nat (cap / 8)) = Some sb /\ end_byte_ok cap sb) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad beg) (shlen (rup8 cap)) ->
  evtF bsegs RNG (annot_sg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc beg cap old new lo full m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AANNOT) fc None m (seg_rom bsegs)).
Proof.
  intros until full. intros MI ST CEIL LO PC AC -> -> -> -> AL CAP N0 NO OC KH HE FULL HSB RIMG RSTK RSH.
  unfold ANNOT_STACK, AANNOT in *. pose proof KH as KH0. unfold ablk, AIMG_HI, KLS in KH. pose proof atop_range as ATR.
  pose proof PC as PC'. destruct PC' as (GOT & GOTMS & REAL & SHB & LAY & CANP & THR). destruct AC as (DCO & GVB & VERB).
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  (* [comment removed for export] *)
  assert (AR : exists G qn qo gn nm cm gc,
    shlen (rup8 cap) = G /\ shlen (rup8 new) = qn /\ shlen (rup8 old) = qo /\ new / 8 = gn /\ new mod 8 = nm /\ cap mod 8 = cm /\ cap / 8 = gc
    /\ rup8 cap = 8 * G /\ rup8 new = 8 * qn /\ rup8 old = 8 * qo /\ rdn8 new = 8 * gn /\ rdn8 cap = 8 * gc
    /\ new = 8 * gn + nm /\ cap = 8 * gc + cm /\ 0 <= nm < 8 /\ 0 <= cm < 8
    /\ (nm = 0 -> qn = gn) /\ (nm <> 0 -> qn = gn + 1) /\ (cm = 0 -> G = gc) /\ (cm <> 0 -> G = gc + 1)
    /\ 0 <= gn /\ qn <= qo /\ qo <= G /\ old <= 8 * qo /\ 8 * qo < old + 8
    /\ shlen (rup8 old - rup8 new) = qo - qn).
  { exists (shlen (rup8 cap)), (shlen (rup8 new)), (shlen (rup8 old)), (new / 8), (new mod 8), (cap mod 8), (cap / 8).
    unfold shlen, rup8, rdn8. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    repeat split; clear - CAP N0 NO OC; Z.div_mod_to_equations; lia. }
  destruct AR as (G & qn & qo & gn & nm & cm & gc & EG & EQN & EQO & EGN & ENM & ECM & EGC & R8 & RN & RO & DN & DC & NEW & CAPE & NM8 & CM8
                  & QN0 & QN1 & GC0 & GC1 & GN0 & LE1 & LE2 & OLO & OHI & SHLD).
  rewrite EG in FULL, RSH. rewrite R8 in KH, KH0, HE.
  assert (SHF : shad beg = 2147450880 + beg / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (BEG8 : exists bg, beg = 8 * bg) by (exists (beg / 8); clear - AL; Z.div_mod_to_equations; lia).
  destruct BEG8 as [bg EBG].
  assert (SHQN : shad (beg + 8 * qn) = shad beg + qn) by (unfold shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; rewrite EBG; clear; Z.div_mod_to_equations; lia).
  assert (SHGN : shad (beg + 8 * gn) = shad beg + gn) by (unfold shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; rewrite EBG; clear; Z.div_mod_to_equations; lia).
  assert (SHCAP : 2147450880 + Z.shiftr (beg + cap) 3 = shad beg + gc) by (unfold shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; rewrite EBG, CAPE; clear - CM8; Z.div_mod_to_equations; lia).
  assert (BG8 : beg / 8 = bg) by (rewrite EBG; clear; Z.div_mod_to_equations; lia). rewrite BG8 in SHF.
  pose proof (CB_len _ _ _ _ FULL) as LF.
  assert (M8E : (beg + cap) mod 8 = cm) by (rewrite EBG, CAPE; clear - CM8; Z.div_mod_to_equations; lia).
  assert (N8E : (beg + new) mod 8 = nm) by (rewrite EBG, NEW; clear - NM8; Z.div_mod_to_equations; lia).
  assert (N7E : (beg + new + 7) mod 8 = 8 * gn + nm + 7 - 8 * qn).
  { rewrite EBG, NEW. destruct (Z.eq_dec nm 0) as [Z0|NZ]; [rewrite (QN0 Z0); clear - NM8 Z0 | rewrite (QN1 NZ); clear - NM8 NZ]; Z.div_mod_to_equations; lia. }
  assert (O7E : (beg + old + 7) mod 8 = old + 7 - 8 * qo) by (rewrite EBG; clear - OLO OHI; Z.div_mod_to_equations; lia).
  clear BG8.
  assert (SHLD2 : shlen (8 * qo - 8 * qn) = qo - qn) by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  unfold annot_sg_post, sg_out, sg_mid. rewrite ?EG, ?EQN, ?EQO, ?EGN, ?ENM.
  box EG; box EQN; box EQO; box EGN; box ENM; box ECM; box EGC.
  assert (BE1 : beg + cap <= beg + 8 * G) by (clear - CAPE GC0 GC1 CM8; lia).
  assert (BE2 : 8 * G < cap + 8) by (clear - CAPE GC0 GC1 CM8; lia).
  assert (GCB : 0 <= 8 * gc <= cap) by (clear - CAPE CM8 CAP; lia).
  assert (SHR : 0x6d4000 <= shad beg /\ shad beg + G <= 0x10007fff8000) by (rewrite SHF; clear - EBG KH BE2 CAP ATR; lia).
  assert (GNB : 0 <= 8 * gn <= new) by (clear - NEW NM8 GN0; lia).
  assert (QNB : new <= 8 * qn <= new + 7) by (clear - NEW NM8 GN0 QN0 QN1; lia).
  assert (QOB : old <= 8 * qo <= old + 7) by (clear - OLO OHI; lia).
  box R8; box RN; box RO; box DN; box DC; box NEW; box CAPE; box QN0; box QN1; box GC0; box GC1; box LE1; box LE2; box OLO; box OHI; box SHLD;
  box SHF; box EBG; box SHCAP; box M8E; box N8E; box N7E; box O7E; box LF.
  pose proof (munch_refl [(bv_unsigned sp - 2720, bv_unsigned sp); (shad beg + gn, shad beg + qo)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 2720, bv_unsigned sp)]%Z m) as MUF.
  carve_frame 56%nat ST;
       (destruct (stk_split bsegs _ lo (bv_unsigned sp + -2128) (bv_unsigned sp + -56) ST ltac:(lia)) as [ST' STP]; clear ST; rename ST' into ST).
  do 9 zstep.                 (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  zstep; zstep.               (* [comment removed for export] *)
  zstep; rewrite zxb_lit by lia.   (* [comment removed for export] *)
  zstep; let K := fresh "Ka" in if_cases K; zify_cond K; [exfalso; clear - K; lia|].   (* [comment removed for export] *)
  do 3 zstep.                 (* [comment removed for export] *)
  zstep; zstep; zstep; lits.  (* [comment removed for export] *)
  zstep; zstep; let K := fresh "Kb" in if_cases K; zify_cond K; [exfalso; clear - K; lia|].   (* [comment removed for export] *)
  zstep; let K := fresh "Kc" in if_cases K; zify_cond K; [| exfalso; clear - K CAP NO N0 OC; lia].   (* [comment removed for export] *)
  zstep; let K := fresh "Kd" in if_cases K; zify_cond K; [exfalso; clear - K CAP NO N0 OC; lia|].   (* [comment removed for export] *)
  zstep; let K := fresh "Ke" in if_cases K; zify_cond K; [exfalso; clear - K CAP NO N0 OC; lia|].   (* [comment removed for export] *)
  zstep; let K := fresh "Kf" in if_cases K; zify_cond K; [exfalso; clear - K CAP NO N0 OC; lia|].   (* [comment removed for export] *)
  do 4 zstep.                 (* [comment removed for export] *)
  zstep; let K := fresh "Kg" in if_cases K; zify_cond K; [exfalso; clear - K CAP; lia|].   (* [comment removed for export] *)
  zstep; let K := fresh "Kh" in if_cases K; zify_cond K; [exfalso; clear - K CAP NO N0 OC; lia|].   (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  replace (Z.land (beg + cap) 7) with cm by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; unfold bxs in M8E; symmetry; exact M8E).
  zstep; if_cases Kal; zify_cond Kal.   (* [comment removed for export] *)
  all: swap 1 2.                       (* [comment removed for export] *)
  1: assert (ALI : cm = 0) by (clear - Kal CM8; lia).
  2: assert (NAL : cm <> 0) by (clear - Kal CM8; lia).
  all: clear Kal.
  (* [comment removed for export] *)
  2: zstep; rewrite land_align8 by lia; unfold bxs in M8E; rewrite M8E; box M8E; replace (beg + cap - cm) with (beg + 8 * gc) by (blia - CAPE).     (* [comment removed for export] *)
  2: zstep; zstep; (let Ki := fresh "Ki" in if_cases Ki; zify_cond Ki; [| exfalso; clear - Ki CAP NO N0 OC; lia]).   (* [comment removed for export] *)
  2: zstep; (let Kj := fresh "Kj" in if_cases Kj; zify_cond Kj).        (* [comment removed for export] *)
  (* [comment removed for export] *)
  3: (assert (RDO : rdn8 cap < old) by (blia - Kj DC);
      assert (NAL' : cap mod 8 <> 0) by (blia - NAL CAPE CM8);
      destruct (HSB NAL' RDO) as (sb & NTH & SB1 & SB2); clear NAL';
      pose proof FULL as FULLc;
      do 5 zstep;                                 (* [comment removed for export] *)
      lazymatch goal with |- evtF _ ?RNG' _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (full_byte_read mm beg cap full sb AL ltac:(lia) ltac:(replace (shlen (rup8 cap)) with G by (unfold bxs in R8; rewrite R8; unfold shlen; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear; Z.div_mod_to_equations; lia); exact FULLc) NTH) as HR;
        unfold bxs in SHCAP; rewrite SHCAP in HR;
        assert (ACC : rng RNG' (shad beg + gc) 1) by (eapply rng_sub'; [exact RSH|]; blia - GC1 NAL GCB)
      end;
      rewrite SHCAP; box SHCAP;
      zstep; clear HR ACC FULLc; rewrite sxb_sval;       (* [comment removed for export] *)
      pose proof (sval_range sb) as SBR;
      zstep; (let Kk := fresh "Kk" in if_cases Kk; zify_cond Kk; [ exfalso; clear - Kk SB1 SBR; rewrite ?unsigned_sval in Kk; apply SB1; apply sval_zero_iff; lia |]);
      zstep; unfold bv_lts; rewrite !signed_lit_small64 by lia;   (* [comment removed for export] *)
      unfold end_byte_ok in SB2;
      replace (cm <? sval sb) with false by (symmetry; apply Z.ltb_ge; bdlia - SB2 M8E CAPE CM8); cbn [negb];
      clear Ki Kj Kk SB1 SB2 SBR NTH RDO).
  2: clear Ki Kj.
  all: clear HSB MUF.
  (* [comment removed for export] *)
  all: do 3 zstep.                 (* [comment removed for export] *)
  all: zstep.                      (* [comment removed for export] *)
  all: replace (Z.land beg 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; clear - AL; lia).
  all: zstep; if_lit.              (* [comment removed for export] *)
  all: zstep; zstep.               (* [comment removed for export] *)
  all: zstep; (let K := fresh "Kt" in if_cases K; zify_cond K; [exfalso; clear - K NO; lia| clear K]).   (* [comment removed for export] *)
  all: zstep; rewrite land_align8 by lia; unfold bxs in N8E; rewrite N8E; box N8E.        (* [comment removed for export] *)
  all: replace (beg + new - nm) with (beg + 8 * gn) by (blia - NEW).
  all: zstep; (let K := fresh "Kt" in if_cases K; zify_cond K; [exfalso; clear - K NO; lia| clear K]).   (* [comment removed for export] *)
  all: zstep; rewrite land_align8 by lia; unfold bxs in N8E; rewrite N8E; box N8E.        (* [comment removed for export] *)
  all: replace (beg + new - nm) with (beg + 8 * gn) by (blia - NEW).
  all: zstep; zstep; rewrite land_align8 by lia; unfold bxs in N7E; rewrite N7E; box N7E.      (* [comment removed for export] *)
  all: replace (beg + new + 7 - (8 * gn + nm + 7 - 8 * qn)) with (beg + 8 * qn) by (blia - NEW).
  all: zstep; (let K := fresh "Kt" in if_cases K; zify_cond K; [clear K| exfalso; clear - K; lia]).   (* [comment removed for export] *)
  all: zstep; zstep; rewrite land_align8 by lia; unfold bxs in O7E; rewrite O7E; box O7E.      (* [comment removed for export] *)
  all: replace (beg + old + 7 - (old + 7 - 8 * qo)) with (beg + 8 * qo) by (clear; lia).
  all: zstep; (let K := fresh "Kp" in if_cases K; zify_cond K).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: match goal with
       | Kp : _ <= _ |- _ => assert (NOP : qo = qn) by (blia - Kp LE1); clear Kp; assert (NPB : NOPOISON) by exact I
       | Kp : _ < _ |- _ => assert (POI : qn < qo) by (clear - Kp; lia); clear Kp; assert (POB : POISON) by exact I
       end.
  all: lazymatch goal with
       | POB : POISON |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
           let FU := fresh "FU" in
           lazymatch goal with H : rw_cells bsegs mm (shad _) [CB _ _] |- _ => rename H into FU end;
           replace (Z.to_nat G) with (Z.to_nat qn + Z.to_nat (qo - qn) + Z.to_nat (G - qo))%nat in FU by (blia - POI LE2 GNB QNB N0);
           destruct (CB_split3 mm (shad beg) _ _ _ full FU) as (FA & FB & FC); clear FU;
           rewrite (Z2Nat.id qn) in FB by (blia - GNB QNB N0);
           replace (shad beg + qn) with (shad (beg + 8 * qn)) in FB by (first [exact SHQN | symmetry; exact SHQN]);
           rewrite <- SHLD2 in FB;
           zstep; zstep; zstep;                                  (* [comment removed for export] *)
           replace (beg + 8 * qo - (beg + 8 * qn)) with (8 * qo - 8 * qn) by (clear; lia);
           zstep;                                                (* [comment removed for export] *)
           call_sp (poison_shadow_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (beg + 8 * qn) (8 * qo - 8 * qn) 252);
           first [ exact CEIL | reflexivity | (rewrite Hsp; exact ST) | exact FB | eassumption
                 | (unfold poison_cells; repeat lazymatch goal with |- _ /\ _ => split end; assumption)
                 | (lazymatch goal with |- (_ + 8 * _) mod 8 = 0 => bdlia - AL end)
                 | (lazymatch goal with |- (8 * _ - 8 * _) mod 8 = 0 => bdlia - POI end)
                 | (lazymatch goal with |- ablk _ _ => eapply ablk_sub; [exact KH0 | blia - GNB QNB N0 | blia - LE2] end)
                 | (intros X; exfalso; clear - X; lia)
                 | (lazymatch goal with |- rng _ (shad (_ + 8 * _)) _ => rewrite SHQN, SHLD2; eapply rng_sub'; [exact RSH| blia - POI LE2 GNB QNB N0] end)
                 | lia | (rewrite Hsp; solve_rng) | solve_rng | idtac ]
       | _ => idtac
       end.
  (* [comment removed for export] *)
  all: lazymatch goal with
       | POB : POISON |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
           let FBP := fresh "FBP" in
           lazymatch goal with H : rw_cells bsegs mm (shad (_ + 8 * _)) [CB _ (repeat _ _)] |- _ => rename H into FBP end;
           rewrite SHLD2, SHQN in FBP; rewrite <- (Z2Nat.id qn) in FBP at 1 by (blia - GNB QNB N0);
           lazymatch goal with FA : rw_cells bsegs mm (shad _) [CB _ (firstn _ _)], FC : rw_cells bsegs mm (shad _ + Z.of_nat _ + Z.of_nat _) [CB _ _] |- _ =>
             pose proof (CB_join3 mm (shad beg) _ _ _ _ _ _ FA FBP FC) as MID; clear FA FBP FC;
             rewrite skipn_skipn in MID;
             replace (Z.to_nat (qo - qn) + Z.to_nat qn)%nat with (Z.to_nat qo) in MID by (blia - POI GNB QNB N0);
             replace (Z.to_nat qn + Z.to_nat (qo - qn) + Z.to_nat (G - qo))%nat with (Z.to_nat G) in MID by (blia - POI LE2 GNB QNB N0)
           end
       | NPB : NOPOISON |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
           let FU := fresh "FU" in
           lazymatch goal with H : rw_cells bsegs mm (shad _) [CB _ _] |- _ => rename H into FU end;
           assert (MID : rw_cells bsegs mm (shad beg) [CB (Z.to_nat G) (firstn (Z.to_nat qn) full ++ repeat (Z_to_bv 8 252) (Z.to_nat (qo - qn)) ++ skipn (Z.to_nat qo) full)])
             by (rewrite NOP; replace (qn - qn) with 0 by (clear; lia); cbn [Z.to_nat repeat app]; rewrite firstn_skipn; exact FU);
           clear FU
       end.
  all: lazymatch goal with P : stk bsegs ?mm ?a _, H : stk bsegs ?mm _ ?a |- _ => rename H into ST9 | _ => idtac end.
  (* [comment removed for export] *)
  all: zstep; (let K := fresh "Kb" in if_cases K; zify_cond K).     (* [comment removed for export] *)
  all: match goal with
       | Kb : _ = _ |- _ => assert (NALN : nm = 0) by (blia - Kb QN1 NM8); clear Kb
       | Kb : _ <> _ |- _ => assert (UALN : nm <> 0) by (blia - Kb QN0); clear Kb; assert (BYB : BYTEST) by exact I;
           assert (GNQ : gn + 1 = qn) by (blia - UALN QN1)
       end.
  all: lazymatch goal with
       | BYB : BYTEST |- evtF _ ?RNG' _ (MS _ _ _ _ _ ?mm _) =>
           zstep; replace (beg + 8 * qn - (beg + 8 * gn)) with 8 by (blia - UALN QN1);   (* [comment removed for export] *)
           zstep; zstep; if_lit;                          (* [comment removed for export] *)
           zstep; replace (Z.land (beg + new) 7) with nm by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; unfold bxs in N8E; first [exact N8E | symmetry; exact N8E]);   (* [comment removed for export] *)
           zstep; zstep;                                  (* [comment removed for export] *)
           call m2s_spec; first [ eassumption | (rewrite ?unsigned_lit by (clear - KH GNB N0 NO OC BE1 HE ATR; lia); unfold KLOW, KHIGH, KEND; clear - KH GNB N0 NO OC BE1 HE ATR; lia) | idtac ];
           rewrite ?unsigned_lit by (clear - KH GNB N0 NO OC BE1 HE ATR; lia);
           rewrite SHGN;
           (* [comment removed for export] *)
           destruct (CB_byte mm (shad beg) (Z.to_nat G) _ (Z.to_nat gn) MID ltac:(blia - UALN QN1 LE1 LE2 GNB)) as (FA2 & FBY & FC2); clear MID;
           rewrite (Z2Nat.id gn) in FBY by (blia - GNB);
           assert (ACC2 : rng RNG' (shad beg + gn) 1) by (eapply rng_sub'; [exact RSH| blia - UALN QN1 LE1 LE2 GNB]);
           set (SBA := shad beg + gn) in *; zstep; rewrite le1_sym; mem_after_store; subst SBA
       | _ => idtac
       end.
  (* [comment removed for export] *)
  all: lazymatch goal with
       | BYB : BYTEST |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
           lazymatch goal with FA2 : rw_cells bsegs mm (shad _) [CB _ (firstn _ _)], FBY : rw_cells bsegs mm (shad _ + _) [C1 _], FC2 : rw_cells bsegs mm _ [CB _ (skipn _ _)] |- _ =>
             rewrite <- (Z2Nat.id gn) in FBY at 1 by (blia - GNB);
             pose proof (CB_byte_join mm (shad beg) (Z.to_nat G) (Z.to_nat gn) _ _ _ FA2 FBY FC2 ltac:(blia - GNQ LE1 LE2 GNB)) as FIN; clear FA2 FBY FC2
           end
       | _ => idtac
       end.
  (* [comment removed for export] *)
  all: do 10 zstep.
  all: match goal with P : stk bsegs ?mm ?a _, H : stk bsegs ?mm _ ?a |- _ => (pose proof (stk_merge bsegs _ _ _ _ H P ltac:(lia)) as ST9'; clear H P); release_frame FR ST9' (bv_unsigned sp) end.
  all: finish.
  (* [comment removed for export] *)
  all: try (replace (nm =? 0) with true by (symmetry; apply Z.eqb_eq; assumption); assumption).
  all: try (replace (nm =? 0) with false by (symmetry; apply Z.eqb_neq; assumption); assumption).
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition annot_nopg_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - ANNOT_STACK, bv_unsigned sp)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma annot_nopg_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (beg cap k lo : Z),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - ANNOT_STACK ->
  poison_cells m -> annot_cells m ->
  a0 = Z_to_bv 64 beg -> a1 = Z_to_bv 64 (beg + cap) -> a2 = Z_to_bv 64 (beg + k) -> a3 = Z_to_bv 64 (beg + k) ->
  0 <= beg -> 0 <= cap <= 2^40 -> 0 <= k <= cap -> beg + cap + 8 <= 2^47 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (annot_nopg_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AANNOT) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros MI ST CEIL LO PC AC -> -> -> -> B0 CAP KK HE RIMG RSTK.
  unfold ANNOT_STACK, AANNOT in *. pose proof atop_range as ATR.
  pose proof PC as PC'. destruct PC' as (GOT & GOTMS & REAL & SHB & LAY & CANP & THR). destruct AC as (DCO & GVB & VERB).
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 2720, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 56%nat ST;
       (destruct (stk_split bsegs _ lo (bv_unsigned sp + -2128) (bv_unsigned sp + -56) ST ltac:(lia)) as [ST' STP]; clear ST; rename ST' into ST).
  do 9 zstep.                 (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  zstep.                      (* [comment removed for export] *)
  zstep; zstep.               (* [comment removed for export] *)
  zstep; rewrite zxb_lit by lia.   (* [comment removed for export] *)
  zstep; let K := fresh "Ka" in if_cases K; zify_cond K; [exfalso; clear - K; lia|].   (* [comment removed for export] *)
  do 3 zstep.                 (* [comment removed for export] *)
  zstep; zstep; zstep; lits.  (* [comment removed for export] *)
  zstep; zstep; let K := fresh "Kb" in if_cases K; zify_cond K; [exfalso; clear - K; lia|].   (* [comment removed for export] *)
  zstep; let K := fresh "Kc" in if_cases K; zify_cond K; [| exfalso; clear - K CAP KK; lia].   (* [comment removed for export] *)
  zstep; let K := fresh "Kd" in if_cases K; zify_cond K; [exfalso; clear - K CAP KK; lia|].   (* [comment removed for export] *)
  zstep; let K := fresh "Ke" in if_cases K; zify_cond K; [exfalso; clear - K CAP KK; lia|].   (* [comment removed for export] *)
  zstep; let K := fresh "Kf" in if_cases K; zify_cond K; [exfalso; clear - K CAP KK; lia|].   (* [comment removed for export] *)
  do 4 zstep.                 (* [comment removed for export] *)
  zstep; let K := fresh "Kg" in if_cases K; zify_cond K; [exfalso; clear - K CAP; lia|].   (* [comment removed for export] *)
  zstep; let K := fresh "Kh" in if_cases K; zify_cond K; [| exfalso; clear - K; lia].   (* [comment removed for export] *)
  (* [comment removed for export] *)
  do 10 zstep.
  match goal with P : stk bsegs ?mm ?a _, H : stk bsegs ?mm _ ?a |- _ => (pose proof (stk_merge bsegs _ _ _ _ H P ltac:(lia)) as ST9'; clear H P); release_frame FR ST9' (bv_unsigned sp) end.
  finish.
Qed.
End CANSEC1.
