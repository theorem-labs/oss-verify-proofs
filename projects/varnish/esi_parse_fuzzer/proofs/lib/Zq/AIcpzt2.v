(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require ImgA.

Module RA_s5ib.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import RA_sp5c RA_m08t.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Definition strchrnul_entry := 0xa20c4%Z.
Definition strchr_entry := 0xa2088%Z.

(* [comment removed for export] *)
Definition strchrnul_off (c : Z) (str : list byte) : Z :=
  if (c =? 0)%Z then Z.of_nat (length str) else Z.of_nat (strchrnul_idx c str).
(* [comment removed for export] *)
Definition strchr_val (A c : Z) (str : list byte) : Z :=
  if (c =? 0)%Z then (A + Z.of_nat (length str))%Z else strchr_res A c str.

Definition strchrnul_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (bv_unsigned a0 + strchrnul_off (bv_unsigned a1 mod 256) str))
                 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).

Section Strchrnul.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (str slack : list byte) (lo : Z).
  (* [comment removed for export] *)
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis STR : bytes_at rsegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Hypothesis FR : rw_cells rsegs m (bv_unsigned sp + -16) [C8 s0; C8 ra].
  Hypothesis STK : stk rsegs m lo (bv_unsigned sp + -16).
  Hypothesis MU : munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m0 m.
  Hypothesis WM : wmono rsegs m0 m.
  Hypothesis LO : (0 <= lo <= bv_unsigned sp - 16)%Z.
  Hypothesis CR : (0 < bv_unsigned a1 mod 256)%Z.

  Notation A := (bv_unsigned a0).
  Notation c := ((bv_unsigned a1) mod 256)%Z.
  Notation len := (Z.of_nat (length str)).
  Notation full := (str ++ Z_to_bv 8 0 :: slack).
  Notation r := (Z.of_nat (strchrnul_idx ((bv_unsigned a1) mod 256)%Z str)).
  Notation POST := (strchrnul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m0).
  (* [comment removed for export] *)
  Notation ST pc x10 x12 x13 x14 x15 x16 x17 :=
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 x10 (Z_to_bv 64 c) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
  Notation CMAGIC := 72340172838076672%Z.      (* [comment removed for export] *)
  Notation HIGHS := 9259542123273814144%Z.     (* [comment removed for export] *)
  Notation ONES := 72340172838076673%Z.       (* [comment removed for export] *)

  #[using="a1 a0"] Lemma full_length : length full = (length str + S (length slack))%nat.
  Proof. rewrite length_app. cbn. lia. Qed.

  #[using="CR STR m"] Lemma A_bound : (0 <= A /\ A + len + 1 + Z.of_nat (length slack) <= 2^64 /\ 0 < c < 256)%Z.
  Proof.
    pose proof (bytes_at_bound _ _ _ _ STR) as B. rewrite full_length in B.
    pose proof (Z.mod_pos_bound (bv_unsigned a1) 256). lia.
  Qed.

  #[using="STK FR lo slack str m a1 a0 s0 ra"] Lemma sp_bound : (16 <= bv_unsigned sp /\ bv_unsigned sp < 2^64)%Z.
  Proof.
    pose proof (rw_cells_bound _ _ _ _ FR) as B. cbn in B. destruct STK as [? _].
    pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R. lia.
  Qed.

  #[using="slack a0"] Lemma r_le : (0 <= r <= len)%Z.
  Proof. pose proof (strchrnul_idx_le c str). lia. Qed.

  #[using="NONUL a1 a0"] Lemma full_nth_lt : forall i, (0 <= i < len)%Z ->
    exists b, nth_error full (Z.to_nat i) = Some b /\ bv_unsigned b <> 0%Z /\ nth_error str (Z.to_nat i) = Some b.
  Proof.
    intros i Hi. destruct (nth_error str (Z.to_nat i)) as [b|] eqn:E.
    - exists b. split. { rewrite nth_error_app1 by lia. exact E. }
      split; [|reflexivity]. intros Hb. apply NONUL. replace (Z_to_bv 8 0) with b. { eapply nth_error_In; eauto. }
      apply bv_eq. rewrite Hb. reflexivity.
    - apply nth_error_None in E. lia.
  Qed.

  #[using="a1 a0"] Lemma full_nth_len : nth_error full (Z.to_nat len) = Some (Z_to_bv 8 0).
  Proof. rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="CR NONUL STR m a0"] Lemma byte_at : forall i, (0 <= i <= r)%Z ->
    exists b, nth_error full (Z.to_nat i) = Some b /\
      (bv_unsigned b = 0%Z <-> i = len) /\
      (i < r -> bv_unsigned b <> c)%Z /\
      (i = r -> r < len -> bv_unsigned b = c)%Z.
  Proof.
    intros i Hi. pose proof r_le as RL. pose proof A_bound as AB.
    destruct (Z.eq_dec i len) as [->|NE].
    - exists (Z_to_bv 8 0). split; [exact full_nth_len|]. split; [split; auto|]. split; [lia|]. intros; lia.
    - (first [ pose proof ((full_nth_lt i ltac:(lia))) as dR_1; dex1 dR_1 as b; dand3 dR_1 as Hn Hb Hs | pose proof ((full_nth_lt i ltac:(lia))) as dR_1; dand4 dR_1 as b Hn Hb Hs | destruct (full_nth_lt i ltac:(lia)) as (b & Hn & Hb & Hs) ]). exists b. split; [exact Hn|].
      split. { split; intros; exfalso; [exact (Hb H)| lia]. }
      split. { intros Hir. eapply (strchrnul_idx_before c str (Z.to_nat i)); [lia| exact Hs]. }
      intros -> Hr. (first [ pose proof ((strchrnul_idx_at c str ltac:(lia))) as dR_2; dex1 dR_2 as b'; destruct dR_2 as [Hn' Hc'] | pose proof ((strchrnul_idx_at c str ltac:(lia))) as dR_2; dand3 dR_2 as b' Hn' Hc' | destruct (strchrnul_idx_at c str ltac:(lia)) as (b' & Hn' & Hc') ]).
      rewrite Nat2Z.id in Hs. rewrite Hs in Hn'. injection Hn' as <-. exact Hc'.
  Qed.

  (* [comment removed for export] *)
  #[using="CR LO WM MU STK FR STR MI"] Lemma strchrnul_exit : forall x12 x13 x14 x15 x16 x17,
    evt rsegs POST (ST 0xa2194 (Z_to_bv 64 (A + r)) x12 x13 x14 x15 x16 x17).
  Proof.
    intros. pose proof sp_bound as SB. pose proof A_bound as AB.
    zstep. zstep. zstep. zstep.
    pose proof (stk_release rsegs _ _ _ _ STK FR ltac:(lia)) as ST'. cbn [cells_size csize Nat.add] in ST'.
    replace (bv_unsigned sp + -16 + Z.of_nat 16)%Z with (bv_unsigned sp) in ST' by lia.
    apply evt_done. unfold strchrnul_post, strchrnul_off.
    replace (c =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    repeat (lazymatch goal with |- ex _ => eexists end); split; [reflexivity|].
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="CR LO WM MU STK FR NONUL STR MI"] Lemma strchrnul_tail : forall (k : nat) (j : Z) x12 x13 x14 x15 x16 x17,
    Z.to_nat (r - j) = k -> (0 <= j <= r)%Z ->
    evt rsegs POST (ST 0xa2184 (Z_to_bv 64 (A + j - 1)) x12 x13 x14 x15 x16 x17).
  Proof.
    induction k as [|k IH]; intros j x12 x13 x14 x15 x16 x17 Hk Hj; pose proof A_bound as AB; pose proof r_le as RL;
      (first [ pose proof ((byte_at j ltac:(lia))) as dR_3; dex1 dR_3 as b; dand4 dR_3 as Hn Hz Hlt Heq | pose proof ((byte_at j ltac:(lia))) as dR_3; dand5 dR_3 as b Hn Hz Hlt Heq | destruct (byte_at j ltac:(lia)) as (b & Hn & Hz & Hlt & Heq) ]); pose proof (byte_range b);
      pose proof (u8ro_read rsegs m A full j b (Z_to_bv 64 (A + j - 1 + 1)) STR Hn ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    - (* [comment removed for export] *) assert (Ej : j = r) by lia.
      zstep. zstep. zstep. replace (A + j - 1 + 1)%Z with (A + r)%Z by lia.
      if_cases Kz; zify_cond Kz. { apply strchrnul_exit. }
      zstep. if_cases Kc; zify_cond Kc. { exfalso. apply Kc. apply Heq; [exact Ej|]. destruct (Z.eq_dec r len); [|lia]. exfalso. apply Kz, Hz. lia. }
      apply strchrnul_exit.
    - zstep. zstep. zstep. if_cases Kz; zify_cond Kz. { exfalso. apply Hz in Kz. lia. }
      zstep. if_cases Kc; zify_cond Kc.
      + replace (A + j - 1 + 1)%Z with (A + (j + 1) - 1)%Z by lia. apply (IH (j + 1)%Z); [lia|].
        destruct (Z.eq_dec j r) as [E|]; [|lia]. exfalso. apply Kc, Heq; [exact E|].
        destruct (Z.eq_dec r len); [|lia]. exfalso. assert (bv_unsigned b = 0%Z) by (apply Hz; lia). lia.
      + destruct (Z.eq_dec j r) as [E|NE]. { rewrite E. replace (A + r - 1 + 1)%Z with (A + r)%Z by lia. apply strchrnul_exit. }
        exfalso. exact (Hlt ltac:(lia) Kc).
  Qed.

  (* [comment removed for export] *)
  #[using="CR LO WM MU STK FR NONUL STR MI"] Lemma strchrnul_tail_entry : forall (i : Z) x10 x12 x13 x14 x15 x17, (0 <= i <= r)%Z ->
    evt rsegs POST (ST 0xa2180 x10 x12 x13 x14 x15 (Z_to_bv 64 (A + i)) x17).
  Proof.
    intros i x10 x12 x13 x14 x15 x17 Hi. pose proof A_bound as AB.
    zstep. replace (A + i + -1)%Z with (A + i - 1)%Z by lia.
    apply (strchrnul_tail (Z.to_nat (r - i)) i); lia.
  Qed.

  (* [comment removed for export] *)
  #[using="CR PAD STR m"] Lemma word_ok : forall i, (0 <= i <= r)%Z -> ((A + i) mod 8 = 0)%Z -> (Z.to_nat i + 8 <= length full)%nat.
  Proof. intros i Hi Hal. pose proof r_le. pose proof A_bound. rewrite full_length. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  #[using="CR NONUL STR m a0"] Lemma clean_word : forall i, (0 <= i <= r)%Z ->
    ~ In 0%Z (map bv_unsigned (firstn 8 (skipn (Z.to_nat i) full))) ->
    ~ In c (map bv_unsigned (firstn 8 (skipn (Z.to_nat i) full))) ->
    (Z.to_nat i + 8 <= length full)%nat ->
    (i + 8 <= r)%Z.
  Proof.
    intros i Hi NZ NC HW. pose proof r_le as RL.
    assert (IN : forall j b, (Z.to_nat i <= j < Z.to_nat i + 8)%nat -> nth_error full j = Some b ->
                 In (bv_unsigned b) (map bv_unsigned (firstn 8 (skipn (Z.to_nat i) full)))).
    { intros j b Hj Hn. apply in_map. apply nth_error_In with (n := (j - Z.to_nat i)%nat).
      rewrite nth_error_firstn. replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia).
      rewrite nth_error_skipn, <- Hn. f_equal. lia. }
    destruct (Z.lt_ge_cases r (i + 8)) as [Hlt|]; [|assumption]. exfalso.
    (first [ pose proof ((byte_at r ltac:(lia))) as dR_4; dex1 dR_4 as b; dand4 dR_4 as Hn Hz _ Heq | pose proof ((byte_at r ltac:(lia))) as dR_4; dand5 dR_4 as b Hn Hz _ Heq | destruct (byte_at r ltac:(lia)) as (b & Hn & Hz & _ & Heq) ]).
    pose proof (IN (Z.to_nat r) b ltac:(lia) Hn) as HIN.
    destruct (Z.eq_dec r len) as [E|NE].
    - apply NZ. rewrite <- (proj2 Hz E) at 1. exact HIN.
    - apply NC. rewrite <- (Heq eq_refl ltac:(lia)). exact HIN.
  Qed.

  (* [comment removed for export] *)
  #[using="CR LO WM MU STK FR PAD NONUL STR MI"] Lemma strchrnul_words : forall (k : nat) (i : Z) (chunk : list byte) (w14 x15' x16 x17 : word),
    Z.to_nat (r - i) = k -> (0 <= i <= r)%Z -> ((A + i) mod 8 = 0)%Z ->
    chunk = firstn 8 (skipn (Z.to_nat i) full) -> length chunk = 8%nat ->
    ~ In 0%Z (map bv_unsigned chunk) ->
    bv_unsigned w14 = le_val (map bv_unsigned chunk) ->
    x15' = Z_to_bv 64 (c * ONES) ->
    evt rsegs POST (ST 0xa212c (Z_to_bv 64 (A + i)) (Z_to_bv 64 CMAGIC) (Z_to_bv 64 HIGHS) w14 x15' x16 x17).
  Proof.
    induction k as [k IH] using lt_wf_ind; intros i chunk w14 x15' x16 x17 Hk Hi Hal Hch CL NZ Hw ->;
      pose proof A_bound as AB; pose proof r_le as RL.
    pose proof (le_val_range _ (bytes_ok_map chunk)) as WR. rewrite length_map, CL in WR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR.
    pose proof (le_val_range _ (bytes_ok_xor _ c (bytes_ok_map chunk) ltac:(lia))) as XR. rewrite !length_map, CL in XR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in XR.
    zstep. rewrite Hw.
    replace (Z.lxor (le_val (map bv_unsigned chunk)) (c * ONES)) with (le_val (map (fun b => Z.lxor b c) (map bv_unsigned chunk))).
    2:{ change ONES with ONES64b. rewrite <- ones_8, <- CL, <- (length_map bv_unsigned). symmetry. apply le_val_xor_bcast; [apply bytes_ok_map| lia]. }
    zstep. zstep. zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      zstep. apply (strchrnul_tail_entry i); lia.
    - apply (haszero64_clang _ (bytes_ok_xor _ c (bytes_ok_map chunk) ltac:(lia)) ltac:(rewrite !length_map; exact CL)) in K.
      rewrite In0_xor in K.
      pose proof (word_ok i ltac:(lia) Hal) as HW0.
      pose proof (clean_word i ltac:(lia) ltac:(rewrite <- Hch; exact NZ) ltac:(rewrite <- Hch; exact K) HW0) as H8.
      (* [comment removed for export] *)
      assert (Hal8 : ((A + (i + 8)) mod 8 = 0)%Z) by (Z.div_mod_to_equations; lia).
      pose proof (word_ok (i + 8) ltac:(lia) Hal8) as HW.
      pose proof (bytes_at_read rsegs m A full (i + 8) 8 STR ltac:(lia) HW) as RD.
      set (chunk2 := firstn 8 (skipn (Z.to_nat (i + 8)) full)) in RD.
      assert (CL2 : length chunk2 = 8%nat). { subst chunk2. rewrite firstn_length, skipn_length. lia. }
      pose proof (le_val_range _ (bytes_ok_map chunk2)) as WR2. rewrite length_map, CL2 in WR2.
      change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR2.
      zstep. do 5 zstep. replace (A + i + 8)%Z with (A + (i + 8))%Z by lia. rewrite (load8_le_val chunk2 CL2).
      zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        apply (haszero64_clang _ (bytes_ok_map chunk2) ltac:(rewrite length_map; exact CL2)) in K2.
        apply (IH (Z.to_nat (r - (i + 8)))) with (chunk := chunk2); try lia; try reflexivity; try exact CL2; try exact K2.
        apply load8_le_val. exact CL2.
      + zstep. apply (strchrnul_tail_entry (i + 8)); lia.
  Qed.

  (* [comment removed for export] *)
  #[using="CR LO WM MU STK FR PAD NONUL STR MI"] Lemma strchrnul_wentry : forall (i : Z) x12 x13 x14 x15 x16 x17,
    (0 <= i <= r)%Z -> ((A + i) mod 8 = 0)%Z ->
    evt rsegs POST (ST 0xa2100 (Z_to_bv 64 (A + i)) x12 x13 x14 x15 x16 x17).
  Proof.
    intros i x12 x13 x14 x15 x16 x17 Hi Hal. pose proof A_bound as AB. pose proof r_le as RL.
    pose proof (word_ok i Hi Hal) as HW.
    pose proof (bytes_at_read rsegs m A full i 8 STR ltac:(lia) HW) as RD.
    set (chunk := firstn 8 (skipn (Z.to_nat i) full)) in RD.
    assert (CL : length chunk = 8%nat). { subst chunk. rewrite firstn_length, skipn_length. lia. }
    pose proof (le_val_range _ (bytes_ok_map chunk)) as WR. rewrite length_map, CL in WR.
    change (256 ^ Z.of_nat 8)%Z with (2^64)%Z in WR.
    do 8 zstep. rewrite (load8_le_val chunk CL).
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *) zstep. apply (strchrnul_tail_entry i); lia.
    - apply (haszero64_clang _ (bytes_ok_map chunk) ltac:(rewrite length_map; exact CL)) in K.
      zstep. zstep.
      apply (strchrnul_words (Z.to_nat (r - i)) i chunk); try lia; try reflexivity; try exact CL; try exact K.
      apply load8_le_val. exact CL.
  Qed.

  (* [comment removed for export] *)
  #[using="CR LO WM MU STK FR PAD NONUL STR MI"] Lemma strchrnul_head : forall (k : nat) (i : Z) x13 x14 x15 x16 x17,
    Z.to_nat (r - i) = k -> (0 <= i <= r)%Z ->
    evt rsegs POST (ST 0xa20e4 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (A + i + 1)) x13 x14 x15 x16 x17).
  Proof.
    induction k as [|k IH]; intros i x13 x14 x15 x16 x17 Hk Hi; pose proof A_bound as AB; pose proof r_le as RL;
      (first [ pose proof ((byte_at i ltac:(lia))) as dR_5; dex1 dR_5 as b; dand4 dR_5 as Hn Hz Hlt Heq | pose proof ((byte_at i ltac:(lia))) as dR_5; dand5 dR_5 as b Hn Hz Hlt Heq | destruct (byte_at i ltac:(lia)) as (b & Hn & Hz & Hlt & Heq) ]); pose proof (byte_range b);
      pose proof (u8ro_read rsegs m A full i b _ STR Hn ltac:(lia) eq_refl) as RD.
    - assert (Ei : i = r) by lia.
      zstep. zstep. if_cases Kz; zify_cond Kz. { rewrite Ei. apply strchrnul_exit. }
      zstep. if_cases Kc; zify_cond Kc. { rewrite Ei. apply strchrnul_exit. }
      exfalso. apply Kc, Heq; [exact Ei|]. destruct (Z.eq_dec r len); [|lia]. exfalso. apply Kz, Hz. lia.
    - zstep. zstep. if_cases Kz; zify_cond Kz. { exfalso. apply Hz in Kz. lia. }
      zstep. if_cases Kc; zify_cond Kc.
      { destruct (Z.eq_dec i r) as [E|NE]. { rewrite E. apply strchrnul_exit. } exfalso. exact (Hlt ltac:(lia) Kc). }
      assert (Hir : (i < r)%Z).
      { destruct (Z.eq_dec i r) as [E|]; [|lia]. exfalso. apply Kc, Heq; [exact E|].
        destruct (Z.eq_dec r len); [|lia]. exfalso. assert (bv_unsigned b = 0%Z) by (apply Hz; lia). lia. }
      zstep. zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
      + replace (A + i + 2)%Z with (A + (i + 1) + 1)%Z by lia. replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
        apply (IH (i + 1)%Z); lia.
      + replace (A + i + 1)%Z with (A + (i + 1))%Z by lia.
        apply (strchrnul_wentry (i + 1)); [lia|]. revert Kal. zb_masks. intros Kal. Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="CR LO WM MU STK FR PAD NONUL STR MI"] Lemma strchrnul_body : forall x12 x13 x14 x15 x16 x17,
    evt rsegs POST (ST 0xa20d8 a0 x12 x13 x14 x15 x16 x17).
  Proof.
    intros. pose proof A_bound as AB. pose proof r_le as RL.
    zstep. zstep. if_cases Kal; zify_cond Kal.
    - eapply evt_eq. 2:{ apply (strchrnul_wentry 0); [lia|]. revert Kal. zb_masks. intros Kal. rewrite Z.add_0_r. exact Kal. }
      unfold mkR. rewrite Z_to_bv_plus0. reflexivity.
    - zstep. eapply evt_eq. 2:{ apply (strchrnul_head (Z.to_nat r) 0); lia. }
      unfold mkR. rewrite ?Z.add_0_r, ?Z_to_bv_plus0, ?Z_to_bv_bv_unsigned. reflexivity.
  Qed.
End Strchrnul.

Lemma strchrnul_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) ->
  bytes_at rsegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  mem_inv rsegs m ->
  (lo <= bv_unsigned sp - 16)%Z ->
  (bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  ((bv_unsigned a1) mod 256 <> 0)%Z ->
  evt rsegs (strchrnul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xa20c4) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST STR NONUL PAD MI LO SEP CNZ.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (zr_word a1) as R1. unfold inr64 in R1.
  carve_frame 16%nat ST.
  zstep. zstep. zstep. zstep.
  replace (Z.land (bv_unsigned a1) 255) with ((bv_unsigned a1) mod 256)%Z.
  2:{ change 255%Z with (2^8 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. }
  pose proof (Z.mod_pos_bound (bv_unsigned a1) 256 ltac:(lia)) as CB.
  zstep. if_cases Kc; zify_cond Kc.
  - (* [comment removed for export] *)
    exfalso. lia.
  - eapply strchrnul_body; try eassumption; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma select_mask : forall x y v, (0 <= x < 256)%Z -> (0 <= y < 256)%Z -> (0 <= v < 2^64)%Z ->
  Z.land ((Z.b2z (0 <? Z.lxor x y)%Z + -1) mod 18446744073709551616) v = (if (x =? y)%Z then v else 0%Z).
Proof.
  intros x y v Hx Hy Hv. destruct (Z.eqb_spec x y) as [->|NE].
  - rewrite Z.lxor_nilpotent. cbn -[Z.land]. change ((0 + -1) mod 18446744073709551616)%Z with (Z.ones 64).
    rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
  - pose proof (lxor_lt_256 x y Hx Hy) as R.
    assert (NZ : Z.lxor x y <> 0%Z). { intros E. apply NE. apply Z.lxor_eq. exact E. }
    replace (0 <? Z.lxor x y)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma strchr_byte : forall (A c : Z) (str slack : list byte),
  (0 <= c < 256)%Z -> ~ In (Z_to_bv 8 0) str ->
  exists b : byte, nth_error (str ++ Z_to_bv 8 0 :: slack) (Z.to_nat (strchrnul_off c str)) = Some b /\
    (bv_unsigned b = c -> strchr_val A c str = (A + strchrnul_off c str)%Z) /\
    (bv_unsigned b <> c -> strchr_val A c str = 0%Z).
Proof.
  intros A c str slack Hc NONUL. unfold strchrnul_off, strchr_val, strchr_res, strchrnul_idx.
  destruct (Z.eqb_spec c 0) as [->|NE].
  - exists (Z_to_bv 8 0). rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia. cbn [nth_error].
    split; [reflexivity|]. split; [intros; reflexivity|]. intros H. exfalso. apply H. reflexivity.
  - destruct (find_byte c str) as [i|] eqn:FB.
    + (first [ pose proof ((find_byte_Some _ _ _ FB)) as dR_6; dand3 dR_6 as Hi (b & Hn & Hb) _ | destruct (find_byte_Some _ _ _ FB) as (Hi & (b & Hn & Hb) & _) ]).
      exists b. rewrite Nat2Z.id, nth_error_app1 by lia. split; [exact Hn|]. split; [intros; reflexivity|].
      intros H. exfalso. exact (H Hb).
    + exists (Z_to_bv 8 0). rewrite Nat2Z.id, nth_error_app2, Nat.sub_diag by lia. cbn [nth_error].
      split; [reflexivity|]. split; [|intros; reflexivity].
      intros H. exfalso. apply NE. rewrite <- H. reflexivity.
Qed.

Definition strchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (strchr_val (bv_unsigned a0) (bv_unsigned a1 mod 256) str))
                 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).

Lemma strchr_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) ->
  bytes_at rsegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  mem_inv rsegs m ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  ((bv_unsigned a1) mod 256 <> 0)%Z ->
  evt rsegs (strchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xa2088) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST STR NONUL PAD MI LO SEP CNZ.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB. cbn [length] in AB.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (zr_word a1) as R1. unfold inr64 in R1.
  pose proof (Z.mod_pos_bound (bv_unsigned a1) 256 ltac:(lia)) as CB.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  carve_frame 16%nat ST.
  zstep. zstep. zstep. zstep. zstep.
  call_lit strchrnul_spec by (rewrite ?unsigned_lit by lia; first [exact ST | exact STR | exact NONUL | exact PAD | exact CNZ | assumption | lia]).
  rename PC into ST. clear POST.
  set (off := strchrnul_off (bv_unsigned a1 mod 256) str).
  assert (Hoff : (0 <= off <= Z.of_nat (length str))%Z).
  { subst off. unfold strchrnul_off. pose proof (strchrnul_idx_le (bv_unsigned a1 mod 256) str). destruct (_ =? 0)%Z; lia. }
  (first [ pose proof ((strchr_byte (bv_unsigned a0) (bv_unsigned a1 mod 256) str slack ltac:(lia) NONUL)) as dR_7; dex1 dR_7 as b; dand3 dR_7 as Hn Heq Hne | pose proof ((strchr_byte (bv_unsigned a0) (bv_unsigned a1 mod 256) str slack ltac:(lia) NONUL)) as dR_7; dand4 dR_7 as b Hn Heq Hne | destruct (strchr_byte (bv_unsigned a0) (bv_unsigned a1 mod 256) str slack ltac:(lia) NONUL) as (b & Hn & Heq & Hne) ]).
  fold off in Hn, Heq. pose proof (byte_range b) as BR.
  pose proof (u8ro_read rsegs _ (bv_unsigned a0) _ off b _ STR Hn ltac:(lia) eq_refl) as RD.
  zstep. zstep.
  replace (Z.land (bv_unsigned a1) 255) with ((bv_unsigned a1) mod 256)%Z.
  2:{ change 255%Z with (2^8 - 1)%Z. rewrite zb_land_mask by lia. reflexivity. }
  zstep. zstep. zstep. zstep.
  rewrite select_mask by lia.
  zstep. zstep. zstep. zstep.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold strchr_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split.
  { unfold mkR. destruct (Z.eqb_spec (bv_unsigned b) (bv_unsigned a1 mod 256)) as [E|NE].
    - rewrite (Heq E). reflexivity.
    - rewrite (Hne NE). reflexivity. }
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; assumption.
Qed.
End RA_s5ib.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.ImgA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpzt2.RA_s5ib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require CallLit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw.CallLit.AIcpmc7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp7wm AIcppc0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpjcb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcppc0.

Module AIcpzur.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require CallLit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw.CallLit.AIcpmc7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp7wm.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpjcb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@AFB; @AFA; @Hj; @I31; @Hc; @ESL; @SB; @K2; @A1R; @ESF; @CEIL; @LOLE'; @CV; @HS2; @SFB; @SPR; @LBR; @C1R; @C2R; @LOLE; @K; @K3; @LB; @HS1; @LBB; @l; @l0; @K0; @K1; @H; @K4; @SHhi; @K8])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)

Definition strcmp_icpt_entry : Z := 0x478e4.
Definition STRCMP_ICPT_STACK : Z := 2272.

(* [comment removed for export] *)
Definition strcmp_icpt_cells (m : word -> option byte) : Prop :=
     asan_inited_cell m                                          (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xa8b60 [C8 (Z_to_bv 64 0x1466e8)]      (* [comment removed for export] *)
  /\ ro_cells rsegs m 0x1467dd [C1 (Z_to_bv 8 0)]              (* [comment removed for export] *)
  /\ ro_cells rsegs m 0x1467e2 [C1 (Z_to_bv 8 1)]              (* [comment removed for export] *)
  /\ map_cells m.

Ltac solve_strcmp_cells := unfold strcmp_icpt_cells, asan_inited_cell, map_cells; repeat (split; [assumption|]); assumption.
Ltac open_strcmp_cells H :=
  let I := fresh "CI" in let G := fresh "Gcf" in let C1 := fresh "Cssc" in let C2 := fresh "Cisc" in let MC := fresh "MC" in
  destruct H as (I & G & C1 & C2 & MC); pose proof MC as MC'; open_map_cells MC'; unfold asan_inited_cell in I.

(* [comment removed for export] *)
Fixpoint strcmp_stop (l r : list byte) : option (nat * Z * Z) :=
  match l, r with
  | a :: l', b :: r' =>
      if ((bv_unsigned a =? 0) || negb (bv_unsigned a =? bv_unsigned b))%Z%bool
      then Some (0%nat, bv_unsigned a, bv_unsigned b)
      else match strcmp_stop l' r' with
           | Some (i, x, y) => Some (S i, x, y)
           | None => None
           end
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition char_cmp (c1 c2 : Z) : Z := (if c1 <? c2 then -1 else if c2 <? c1 then 1 else 0)%Z.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma strcmp_stop_nth : forall l r i c1 c2, strcmp_stop l r = Some (i, c1, c2) ->
  (exists a b, nth_error l i = Some a /\ nth_error r i = Some b /\ bv_unsigned a = c1 /\ bv_unsigned b = c2
               /\ (c1 = 0%Z \/ c1 <> c2))
  /\ (forall j, (j < i)%nat -> exists a b, nth_error l j = Some a /\ nth_error r j = Some b
                                  /\ bv_unsigned a = bv_unsigned b /\ bv_unsigned a <> 0%Z).
Proof.
  induction l as [|a l IH]; intros r i c1 c2 H; [discriminate|].
  destruct r as [|b r]; [discriminate|]. cbn -[Z.eqb] in H.
  destruct (Z.eqb_spec (bv_unsigned a) 0) as [A0|A0]; cbn in H.
  - inversion H; subst. split; [exists a, b; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto|]. intros j Hj; lia.
  - destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|NE]; cbn in H.
    + destruct (strcmp_stop l r) as [[[i' x] y]|] eqn:Hs; [|discriminate].
      injection H as Ei Ex Ey. subst i c1 c2.
      destruct (IH r i' x y Hs) as [(a' & b' & Ha & Hb & Hx & Hy & Hc) Hpre].
      split; [exists a', b'; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto|].
      intros j Hj. destruct j as [|j]; [exists a, b; cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto|].
      apply Hpre. lia.
    + inversion H; subst. split; [exists a, b; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto|]. intros j Hj; lia.
Qed.

Definition strcmp_icpt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (ls rs : list byte) (v lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - STRCMP_ICPT_STACK, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' (bv_unsigned a0) ls /\ bytes_at rsegs m' (bv_unsigned a1) rs.

Lemma char_cmp_val : forall c1 c2, (0 <= c1 < 256)%Z -> (0 <= c2 < 256)%Z ->
  Z_to_bv 64 (Z.b2z (c2 <? c1) - Z.b2z (c1 <? c2)) = Z_to_bv 64 (char_cmp c1 c2).
Proof.
  intros c1 c2 H1 H2. unfold char_cmp.
  destruct (Z.ltb_spec0 c1 c2); destruct (Z.ltb_spec0 c2 c1); cbn; try reflexivity; lia.
Qed.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ls rs : list byte) (lo : Z)
            (i : nat) (c1 c2 : Z).
  Notation A := (bv_unsigned a0).
  Notation B := (bv_unsigned a1).
  Notation I := (Z.of_nat i).
  Notation POST := (strcmp_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs (char_cmp c1 c2) lo m).
  Notation FRAME m1 := (rw_cells rsegs m1 (bv_unsigned sp + -104)
                          [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation FRAMEB m1 fjunk := (rw_cells rsegs m1 (bv_unsigned sp + -2192) [CB 2088 fjunk]).
  Hypothesis LOLE : (lo + STRCMP_ICPT_STACK <= bv_unsigned sp)%Z.
  Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
  Hypothesis C1R : (0 <= c1 < 256)%Z.
  Hypothesis C2R : (0 <= c2 < 256)%Z.
  Hypothesis I31 : (I + 1 <= 2^31)%Z.
  Notation SEPAt := ((A + Z.of_nat (length ls) <= lo \/ bv_unsigned sp <= A)%Z) (only parsing).
  Notation SEPBt := ((B + Z.of_nat (length rs) <= lo \/ bv_unsigned sp <= B)%Z) (only parsing).

  (* [comment removed for export] *)
  #[using="C2R C1R LOLE Clg"] Lemma sc_tail : forall m1 fjunk x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x28 x29 x30 x31,
    SEPAt -> SEPBt ->
    mem_inv rsegs m1 ->
    munch [(bv_unsigned sp - STRCMP_ICPT_STACK, bv_unsigned sp)]%Z m m1 -> wmono rsegs m m1 ->
    stk rsegs m1 lo (bv_unsigned sp + -2192) -> FRAME m1 -> FRAMEB m1 fjunk ->
    bytes_at rsegs m1 A ls -> bytes_at rsegs m1 B rs ->
    evt rsegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp x5 x6 x7 sp a1
               x10 x11 x12 x13 x14 x15 x16 x17 a0 ra (Z_to_bv 64 (I + 1)) x21 (Z_to_bv 64 (I + 1)) s7
               (Z_to_bv 64 0x1466e8) (Z_to_bv 64 c1) (Z_to_bv 64 c2) (Z_to_bv 64 (bv_unsigned sp + -2176)) x28 x29 x30 x31)
        F (Z_to_bv 64 0x47fd4) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until x31. intros SEPA SEPB MI1 MU1 WM1 ST1 FR1 FRB1 LS1 RS1. unfold STRCMP_ICPT_STACK in *.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (zr_word ra) as RAR; unfold inr64 in RAR.
    pose proof alloc_ceiling_val as CV.
    zstep. zstep. zstep. rewrite char_cmp_val by assumption.
    do 4 zstep. zstep. (* [comment removed for export] *) zstep. (* [comment removed for export] *)
    zstep. zstep.
    do 13 zstep. zstep. zstep.
    release_frame FRB1 ST1 (bv_unsigned sp + -104)%Z. release_frame FR1 ST1 (bv_unsigned sp). finish.
  Qed.

  Section Facts.
    Variables (ngA ngB : nat) (lastbA lastbB : Z) (w1A w2A w1B w2B : word).
    Notation LBAt := ((lastbA = 0 \/ ((I + A) mod 8 < lastbA <= 7))%Z) (only parsing).
    Notation LBBt := ((lastbB = 0 \/ ((I + B) mod 8 < lastbB <= 7))%Z) (only parsing).
    Hypothesis AFA : (0 <= A /\ A + I + 1 + 8 <= 0x800000000000)%Z.
    Hypothesis AFB : (0 <= B /\ B + I + 1 + 8 <= 0x800000000000)%Z.
    Hypothesis IRA : inmem_range A (I + 1).
    Hypothesis IRB : inmem_range B (I + 1).
    Hypothesis NGA : ((I + A) / 8 - A / 8 = Z.of_nat ngA)%Z.
    Hypothesis NGB : ((I + B) / 8 - B / 8 = Z.of_nat ngB)%Z.
    Hypothesis LSI : (I + 1 <= Z.of_nat (length ls))%Z.
    Hypothesis RSI : (I + 1 <= Z.of_nat (length rs))%Z.

    Section Phase2.
      Variables (m1 : word -> option byte) (fjunk : list byte).
      Hypothesis MI1 : mem_inv rsegs m1.
      Hypothesis MU1 : munch [(bv_unsigned sp - STRCMP_ICPT_STACK, bv_unsigned sp)]%Z m m1.
      Hypothesis WM1 : wmono rsegs m m1.
      Hypothesis ST1 : stk rsegs m1 lo (bv_unsigned sp + -2192).
      Hypothesis FR1 : FRAME m1.
      Hypothesis FRB1 : FRAMEB m1 fjunk.
      Hypothesis LS1 : bytes_at rsegs m1 A ls.
      Hypothesis RS1 : bytes_at rsegs m1 B rs.
      Hypothesis CI : ro_cells rsegs m1 0xb5898 [C1 (Z_to_bv 8 1)].
      Hypothesis Gcf : ro_cells rsegs m1 0xa8b60 [C8 (Z_to_bv 64 0x1466e8)].
      Hypothesis Cssc : ro_cells rsegs m1 0x1467dd [C1 (Z_to_bv 8 0)].
      Hypothesis Cisc : ro_cells rsegs m1 0x1467e2 [C1 (Z_to_bv 8 1)].
      Hypothesis Gsh : ro_cells rsegs m1 0xa8b70 [C8 (Z_to_bv 64 0xb4bb8)].
      Hypothesis Csh : ro_cells rsegs m1 0xb4bb8 [C8 (Z_to_bv 64 0x7fff8000)].
      Hypothesis Gmb : ro_cells rsegs m1 0xa8b78 [C8 (Z_to_bv 64 0xb58a8)].
      Hypothesis Cmb : ro_cells rsegs m1 0xb58a8 [C8 (Z_to_bv 64 0)].
      Hypothesis Gme : ro_cells rsegs m1 0xa8b80 [C8 (Z_to_bv 64 0xb58b0)].
      Hypothesis Cme : ro_cells rsegs m1 0xb58b0 [C8 (Z_to_bv 64 0)].
      Hypothesis Ghe : ro_cells rsegs m1 0xa8b88 [C8 (Z_to_bv 64 0xb58a0)].
      Hypothesis Che : ro_cells rsegs m1 0xb58a0 [C8 (Z_to_bv 64 0x7fffffffffff)].
      Hypothesis SHB1 : bytes_at rsegs m1 (B / 8 + shadow_off) (zeros ngB ++ [Z_to_bv 8 lastbB]).
      Hypothesis QBB1 : bytes_at rsegs m1 (sha B - sha B mod 8) (le8 w1B).
      Hypothesis QBB2 : bytes_at rsegs m1 (sha (I + B) - sha (I + B) mod 8) (le8 w2B).

      Section SlowB.
        Variables (sf sl : Z) (x1 x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 : word).
        Hypothesis SEPA : SEPAt. Hypothesis SEPB : SEPBt.
        Hypothesis ESF : (sf = B / 8 + shadow_off)%Z.
        Hypothesis ESL : (sl = sf + Z.of_nat ngB)%Z.
        Notation AT pc x10 x12 x13 :=
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp x5 x6 x7 sp a1
                   x10 (Z_to_bv 64 sl) x12 x13 x14 x15 x16 x17 a0 ra (Z_to_bv 64 (I + 1)) (Z_to_bv 64 (I + B)) (Z_to_bv 64 (I + 1)) s7
                   (Z_to_bv 64 0x1466e8) (Z_to_bv 64 c1) (Z_to_bv 64 c2) (Z_to_bv 64 (bv_unsigned sp + -2176)) x28 x29 x30 x31)
              F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)) (only parsing).

        (* [comment removed for export] *)
        #[using="SEPB SEPA RS1 LS1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk C2R C1R LOLE Clg"] Lemma sc_slowB_end : forall x10 x13, evt rsegs POST (AT 0x482b0 x10 (Z_to_bv 64 0) x13).
        Proof.
          intros. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
          zstep. zstep. if_cases K; zify_cond K. 2:{ exfalso. try (generalize alloc_ceiling_val); clear -K; try pose proof alloc_ceiling_val. cbv in K. lia. }
          eapply sc_tail; try eassumption.
        Qed.

        (* [comment removed for export] *)
        #[using="ESL ESF SEPB SEPA SHB1 RS1 LS1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk AFB AFA lastbB ngA C2R C1R LOLE Clg"] Lemma sc_slowB_loop : forall (c : nat) (j : Z) x10 x13,
          Z.to_nat (Z.of_nat ngB - j) = c -> (0 <= j < Z.of_nat ngB)%Z -> x10 = Z_to_bv 64 (sf + j) ->
          evt rsegs POST (AT 0x482a0 x10 (Z_to_bv 64 0) x13).
        Proof.
          induction c as [|c IH]; intros j x10 x13 Hc Hj ->; [lia|].
          pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (bytes_at_bound _ _ _ _ SHB1) as SB.
          rewrite length_app, zeros_length in SB. cbn [length] in SB.
          pose proof (u8ro_read rsegs m1 (B / 8 + shadow_off) _ j (Z_to_bv 8 0) (Z_to_bv 64 (sf + j)) SHB1) as RD.
          specialize (RD ltac:(rewrite (shadow_nth ngB lastbB (Z.to_nat j)) by lia;
                                 replace (Z.to_nat j <? ngB)%nat with true by (symmetry; apply Nat.ltb_lt; lia); reflexivity)
                         ltac:(lia) ltac:(unfold wa; f_equal; lia)).
          zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
          zstep. zstep.
          zstep. if_cases K; zify_cond K.
          - apply (IH (j + 1)%Z); [lia|lia|f_equal; lia].
          - apply sc_slowB_end.
        Qed.
      End SlowB.

      (* [comment removed for export] *)
      #[using="QBB2 QBB1 SHB1 Che Ghe Cme Gme Cmb Gmb Csh Gsh Cisc Cssc Gcf CI RS1 LS1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk RSI NGB IRB AFB AFA w2B w1B ngB ngA I31 C2R C1R CEIL LOLE Clg"] Lemma sc_p2 : forall x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
        SEPAt -> SEPBt -> LBBt ->
        evt rsegs POST
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp x5 x6 x7 sp a1
                   x10 x11 x12 x13 x14 x15 x16 x17 a0 ra (Z_to_bv 64 (I + 1)) (Z_to_bv 64 I) (Z_to_bv 64 (I + 1)) s7
                   (Z_to_bv 64 0x1466e8) (Z_to_bv 64 c1) (Z_to_bv 64 c2) (Z_to_bv 64 (bv_unsigned sp + -2176)) x28 x29 x30 x31)
            F (Z_to_bv 64 0x47f84) fc None m1 (seg_rom rsegs)).
      Proof.
        intros until x31. intros SEPA SEPB LBB. pose proof LOLE as LOLE'. unfold STRCMP_ICPT_STACK in LOLE'.
        unfold STRCMP_ICPT_STACK in MU1.
        pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
        pose proof (zr_word a0) as A0R; unfold inr64 in A0R. pose proof (zr_word a1) as A1R; unfold inr64 in A1R.
        pose proof (zr_word ra) as RAR; unfold inr64 in RAR.
        pose proof (bytes_at_bound _ _ _ _ LS1) as LB. pose proof (bytes_at_bound _ _ _ _ RS1) as RB.
        assert (QH1 : (sha B - sha B mod 8 + Z.of_nat (length (le8 w1B)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        assert (QH2 : (sha (I + B) - sha (I + B) mod 8 + Z.of_nat (length (le8 w2B)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        pose proof SHB1 as SH. remember (zeros ngB ++ [Z_to_bv 8 lastbB]) as sbs eqn:Esbs.
        assert (SHhi : (B / 8 + shadow_off + Z.of_nat (length sbs) <= 0x100080000000)%Z).
        { subst sbs. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
        pose proof QBB1 as QB1. pose proof QBB2 as QB2.
        zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
        zstep. if_cases K0; zify_cond K0. { exfalso. try (generalize alloc_ceiling_val); clear -K0; try pose proof alloc_ceiling_val. cbv in K0. lia. }
        zstep. rewrite zb_lxor_ones by lia.
        zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
        zstep.
        zstep. if_cases K2; zify_cond K2.
        - (* [comment removed for export] *)
          zstep. if_cases K3; zify_cond K3. 2:{ exfalso. lia. }
          zstep. zstep.
          zstep. call_lit region_is_poisoned_spec by (idtac;
            lazymatch goal with
            | |- map_cells _ => repeat (split; [assumption|]); assumption
            | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST1
            | |- mem_inv _ _ => eassumption
            | |- inmem_range _ _ => rewrite ?unsigned_lit by lia; exact IRB
            | |- shadow_ok _ _ _ => rewrite ?unsigned_lit by lia; exists ngB, lastbB; subst sbs; split;
                 [replace (B + (I + 1) - 1)%Z with (I + B)%Z by lia; exact NGB| split; [exact SH| replace (B + (I + 1) - 1)%Z with (I + B)%Z by lia; exact LBB]]
            | |- _ => rewrite ?unsigned_lit by lia; first [lia | mlia]
            end).
          zstep. if_cases K4; zify_cond K4. 2:{ exfalso. try (generalize alloc_ceiling_val); clear -K4; try pose proof alloc_ceiling_val. cbv in K4. lia. }
          subst sbs. eapply sc_tail; try eassumption.
        - (* [comment removed for export] *)
          assert (HS1 : (0 <= Z.shiftr B 3 <= B)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
          assert (HS2 : (0 <= Z.shiftr (I + B) 3 <= I + B)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
          do 10 zstep.
          pose proof (qc_read _ _ _ QB1 ltac:(lia)) as RD1.
          pose proof (qc_read _ _ _ QB2 ltac:(lia)) as RD2.
          zstep. zstep. zstep.
          zstep. if_cases K7; zify_cond K7.
          + (* [comment removed for export] *)
            subst sbs.
            assert (LBR : (0 <= lastbB < 128)%Z) by lia.
            pose proof (u8ro_read rsegs _ (B / 8 + shadow_off) _ (Z.of_nat ngB) (Z_to_bv 8 lastbB)
                          (Z_to_bv 64 (2147450880 + Z.shiftr (I + B) 3)) SH) as RD.
            specialize (RD ltac:(rewrite Nat2Z.id, (shadow_nth ngB lastbB ngB), Nat.ltb_irrefl by lia; reflexivity) ltac:(lia)
                           ltac:(unfold wa, shadow_off; f_equal; rewrite Z.shiftr_div_pow2 by lia; mlia)).
            zstep. rewrite sxb_small by lia.
            zstep. zstep. zstep. zstep. zstep.
            rewrite (poisoned_last_zero (I + B) lastbB) by (first [lia | exact LBB]).
            rewrite !Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
            set (sf := (2147450880 + B / 8)%Z). set (sl := (2147450880 + (I + B) / 8)%Z).
            assert (ESF : (sf = B / 8 + shadow_off)%Z) by (unfold sf, shadow_off; lia).
            assert (ESL : (sl = sf + Z.of_nat ngB)%Z) by (unfold sf, sl; mlia).
            assert (SFB : (0 <= sf /\ sl + 1 <= 0x100080000000)%Z).
            { rewrite length_app, zeros_length in SHhi. cbn [length] in SHhi. unfold shadow_off in *. lia. }
            clearbody sf sl.
            zstep. if_cases K8; zify_cond K8.
            * eapply sc_slowB_end; eassumption.
            * eapply sc_slowB_loop with (j := 0%Z); try eassumption; try reflexivity; try lia. f_equal; lia.
          + subst sbs. eapply sc_tail; try eassumption.
      Qed.
    End Phase2.
  End Facts.
End S.

End AIcpzur.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@AF; @Hj; @I31; @Hc; @ESL; @SB; @K2; @A0R; @ESF; @CEIL; @LOLE'; @CV; @HS2; @SFB; @SPR; @LBR; @LOLE; @K; @K3; @SEP'; @LB; @K1; @H; @K4; @HS1; @SI; @SEP; @SHhi; @K8])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
Local Ltac deadK K := exfalso; first [lia | (try (generalize alloc_ceiling_val); clear -K; try pose proof alloc_ceiling_val; cbv in K; first [lia | discriminate | congruence | exact (K eq_refl)])].

Definition strchr_icpt_entry : Z := 0x478e8.
Definition STRCHR_ICPT_STACK : Z := 2224.

Definition strchr_icpt_cells (m : word -> option byte) : Prop :=
     asan_inited_cell m
  /\ ro_cells rsegs m 0xaa8b8 [C8 (Z_to_bv 64 0xa2088)]      (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xa8b60 [C8 (Z_to_bv 64 0x1466e8)]      (* [comment removed for export] *)
  /\ ro_cells rsegs m 0x1467dd [C1 (Z_to_bv 8 0)]              (* [comment removed for export] *)
  /\ ro_cells rsegs m 0x1467e5 [C1 (Z_to_bv 8 1)]              (* [comment removed for export] *)
  /\ map_cells m.

Definition strchr_icpt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (c : Z) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (strchr_res (bv_unsigned a0) c str)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - STRCHR_ICPT_STACK, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str slack : list byte) (lo c v : Z).
  Notation A := (bv_unsigned a0).
  Notation I := (Z.of_nat (strchrnul_idx c str)).
  Notation full := (str ++ Z_to_bv 8 0 :: slack).
  Hypothesis HV : v = strchr_res A c str.
  Notation POST := (strchr_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 c str slack lo m).
  Notation FRAME m1 := (rw_cells rsegs m1 (bv_unsigned sp + -72)
                          [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation FRAMEB m1 fjunk := (rw_cells rsegs m1 (bv_unsigned sp + -2144) [CB 2072 fjunk]).
  Hypothesis LOLE : (lo + STRCHR_ICPT_STACK <= bv_unsigned sp)%Z.
  Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
  Hypothesis I31 : (I + 1 <= 2^31)%Z.
  Hypothesis VR : (0 <= v < 2^64)%Z.
  Notation SEPt := ((A + Z.of_nat (length full) <= lo \/ bv_unsigned sp <= A)%Z) (only parsing).

  (* [comment removed for export] *)
  #[using="LOLE HV"] Lemma sr_exit : forall m1 fjunk x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    mem_inv rsegs m1 -> munch [(bv_unsigned sp - STRCHR_ICPT_STACK, bv_unsigned sp)]%Z m m1 -> wmono rsegs m m1 ->
    stk rsegs m1 lo (bv_unsigned sp + -2144) -> FRAME m1 -> FRAMEB m1 fjunk ->
    bytes_at rsegs m1 A full ->
    evt rsegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9
               (Z_to_bv 64 v) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x484f0) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until x31. intros MI1 MU1 WM1 ST1 FR1 FRB1 STR1. unfold STRCHR_ICPT_STACK in *.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    do 12 zstep.
    release_frame FRB1 ST1 (bv_unsigned sp + -72)%Z. release_frame FR1 ST1 (bv_unsigned sp). rewrite HV. finish.
  Qed.

  Section Facts.
    Variables (ng : nat) (lastb : Z) (w1 w2 : word).
    Notation LBt := ((lastb = 0 \/ ((I + A) mod 8 < lastb <= 7))%Z) (only parsing).
    Hypothesis AF : (0 <= A /\ A + I + 1 + 8 <= 0x800000000000)%Z.
    Hypothesis IR : inmem_range A (I + 1).
    Hypothesis NG : ((I + A) / 8 - A / 8 = Z.of_nat ng)%Z.
    Hypothesis SI : (I + 1 <= Z.of_nat (length full))%Z.

    Section Phase.
      Variables (m1 : word -> option byte) (fjunk : list byte).
      Hypothesis MI1 : mem_inv rsegs m1.
      Hypothesis MU1 : munch [(bv_unsigned sp - STRCHR_ICPT_STACK, bv_unsigned sp)]%Z m m1.
      Hypothesis WM1 : wmono rsegs m m1.
      Hypothesis ST1 : stk rsegs m1 lo (bv_unsigned sp + -2144).
      Hypothesis FR1 : FRAME m1.
      Hypothesis FRB1 : FRAMEB m1 fjunk.
      Hypothesis STR1 : bytes_at rsegs m1 A full.
      Hypothesis Gsh : ro_cells rsegs m1 0xa8b70 [C8 (Z_to_bv 64 0xb4bb8)].
      Hypothesis Csh : ro_cells rsegs m1 0xb4bb8 [C8 (Z_to_bv 64 0x7fff8000)].
      Hypothesis Gmb : ro_cells rsegs m1 0xa8b78 [C8 (Z_to_bv 64 0xb58a8)].
      Hypothesis Cmb : ro_cells rsegs m1 0xb58a8 [C8 (Z_to_bv 64 0)].
      Hypothesis Gme : ro_cells rsegs m1 0xa8b80 [C8 (Z_to_bv 64 0xb58b0)].
      Hypothesis Cme : ro_cells rsegs m1 0xb58b0 [C8 (Z_to_bv 64 0)].
      Hypothesis Ghe : ro_cells rsegs m1 0xa8b88 [C8 (Z_to_bv 64 0xb58a0)].
      Hypothesis Che : ro_cells rsegs m1 0xb58a0 [C8 (Z_to_bv 64 0x7fffffffffff)].
      Hypothesis SH1 : bytes_at rsegs m1 (A / 8 + shadow_off) (zeros ng ++ [Z_to_bv 8 lastb]).
      Hypothesis QB1 : bytes_at rsegs m1 (sha A - sha A mod 8) (le8 w1).
      Hypothesis QB2 : bytes_at rsegs m1 (sha (I + A) - sha (I + A) mod 8) (le8 w2).

      Section Slow.
        Variables (sf sl : Z) (x1 x5 x6 x7 x9 x15 x16 x17 x20 x21 x22 x23 x28 x29 x30 x31 : word).
        Hypothesis SEP : SEPt.
        Hypothesis ESF : (sf = A / 8 + shadow_off)%Z.
        Hypothesis ESL : (sl = sf + Z.of_nat ng)%Z.
        Notation AT pc x11 x13 x14 :=
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9
                   (Z_to_bv 64 v) x11 (Z_to_bv 64 sl) x13 x14 x15 x16 x17 a0 (Z_to_bv 64 (I + A)) x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)) (only parsing).

        #[using="STR1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk ng LOLE HV"] Lemma sr_slow_end : forall x11 x14, evt rsegs POST (AT 0x485c0 x11 (Z_to_bv 64 0) x14).
        Proof.
          intros. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
          zstep. zstep. if_cases K; zify_cond K. all: try (deadK K).
          eapply sr_exit; try eassumption.
        Qed.

        #[using="ESL ESF SH1 STR1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk AF lastb LOLE HV"] Lemma sr_slow_loop : forall (cc : nat) (j : Z) x11 x14,
          Z.to_nat (Z.of_nat ng - j) = cc -> (0 <= j < Z.of_nat ng)%Z -> x11 = Z_to_bv 64 (sf + j) ->
          evt rsegs POST (AT 0x485b0 x11 (Z_to_bv 64 0) x14).
        Proof.
          induction cc as [|cc IH]; intros j x11 x14 Hc Hj ->; [lia|].
          pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (bytes_at_bound _ _ _ _ SH1) as SB.
          rewrite length_app, zeros_length in SB. cbn [length] in SB.
          pose proof (u8ro_read rsegs m1 (A / 8 + shadow_off) _ j (Z_to_bv 8 0) (Z_to_bv 64 (sf + j)) SH1) as RD.
          specialize (RD ltac:(rewrite (shadow_nth ng lastb (Z.to_nat j)) by lia;
                                 replace (Z.to_nat j <? ng)%nat with true by (symmetry; apply Nat.ltb_lt; lia); reflexivity)
                         ltac:(lia) ltac:(unfold wa; f_equal; lia)).
          zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
          zstep. zstep.
          zstep. if_cases K; zify_cond K.
          - apply (IH (j + 1)%Z); [lia|lia|f_equal; lia].
          - apply sr_slow_end.
        Qed.
      End Slow.

      (* [comment removed for export] *)
      #[using="QB2 QB1 SH1 Che Ghe Cme Gme Cmb Gmb Csh Gsh STR1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk SI NG IR AF w2 w1 ng I31 CEIL LOLE HV Clg"] Lemma sr_phase : forall x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x28 x29 x30 x31,
        SEPt -> LBt ->
        evt rsegs POST
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9
                   (Z_to_bv 64 v) x11 x12 x13 x14 x15 x16 x17 a0 (Z_to_bv 64 I) (Z_to_bv 64 0x1466e8) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x4849c) fc None m1 (seg_rom rsegs)).
      Proof.
        intros until x31. intros SEP LB. pose proof LOLE as LOLE'. unfold STRCHR_ICPT_STACK in LOLE'.
        unfold STRCHR_ICPT_STACK in MU1.
        pose proof SEP as SEP'. rewrite length_app in SEP'. cbn [length] in SEP'.
        pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
        pose proof (zr_word a0) as A0R; unfold inr64 in A0R.
        pose proof (bytes_at_bound _ _ _ _ STR1) as LBd.
        assert (QH1 : (sha A - sha A mod 8 + Z.of_nat (length (le8 w1)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        assert (QH2 : (sha (I + A) - sha (I + A) mod 8 + Z.of_nat (length (le8 w2)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        pose proof SH1 as SH. remember (zeros ng ++ [Z_to_bv 8 lastb]) as sbs eqn:Esbs.
        assert (SHhi : (A / 8 + shadow_off + Z.of_nat (length sbs) <= 0x100080000000)%Z).
        { subst sbs. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
        pose proof QB1 as QB1'. pose proof QB2 as QB2'.
        zstep. zstep. rewrite zb_lxor_ones by lia.
        zstep. zstep.
        zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
        zstep.
        zstep. if_cases K2; zify_cond K2.
        - (* [comment removed for export] *)
          zstep. if_cases K3; zify_cond K3. 2:{ exfalso. lia. }
          zstep. zstep. zstep.
          zstep. call_lit region_is_poisoned_spec by (idtac;
            lazymatch goal with
            | |- map_cells _ => repeat (split; [assumption|]); assumption
            | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST1
            | |- mem_inv _ _ => eassumption
            | |- inmem_range _ _ => rewrite ?unsigned_lit by lia; exact IR
            | |- shadow_ok _ _ _ => rewrite ?unsigned_lit by lia; exists ng, lastb; subst sbs; split;
                 [replace (A + (I + 1) - 1)%Z with (I + A)%Z by lia; exact NG| split; [exact SH| replace (A + (I + 1) - 1)%Z with (I + A)%Z by lia; exact LB]]
            | |- _ => rewrite ?unsigned_lit by lia; first [lia | mlia]
            end).
          zstep. zstep.
          zstep. if_cases K4; zify_cond K4. all: try (deadK K4).
          subst sbs. eapply sr_exit; try eassumption.
        - (* [comment removed for export] *)
          assert (HS1 : (0 <= Z.shiftr A 3 <= A)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
          assert (HS2 : (0 <= Z.shiftr (I + A) 3 <= I + A)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
          do 10 zstep.
          pose proof (qc_read _ _ _ QB1' ltac:(lia)) as RD1.
          pose proof (qc_read _ _ _ QB2' ltac:(lia)) as RD2.
          zstep. zstep. zstep.
          zstep. if_cases K7; zify_cond K7.
          + (* [comment removed for export] *)
            subst sbs.
            assert (LBR : (0 <= lastb < 128)%Z) by lia.
            pose proof (u8ro_read rsegs _ (A / 8 + shadow_off) _ (Z.of_nat ng) (Z_to_bv 8 lastb)
                          (Z_to_bv 64 (2147450880 + Z.shiftr (I + A) 3)) SH) as RD.
            specialize (RD ltac:(rewrite Nat2Z.id, (shadow_nth ng lastb ng), Nat.ltb_irrefl by lia; reflexivity) ltac:(lia)
                           ltac:(unfold wa, shadow_off; f_equal; rewrite Z.shiftr_div_pow2 by lia; mlia)).
            zstep. rewrite sxb_small by lia.
            zstep. zstep. zstep. zstep. zstep.
            rewrite (poisoned_last_zero (I + A) lastb) by (first [lia | exact LB]).
            rewrite !Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
            set (sf := (2147450880 + A / 8)%Z). set (sl := (2147450880 + (I + A) / 8)%Z).
            assert (ESF : (sf = A / 8 + shadow_off)%Z) by (unfold sf, shadow_off; lia).
            assert (ESL : (sl = sf + Z.of_nat ng)%Z) by (unfold sf, sl; mlia).
            assert (SFB : (0 <= sf /\ sl + 1 <= 0x100080000000)%Z).
            { rewrite length_app, zeros_length in SHhi. cbn [length] in SHhi. unfold shadow_off in *. lia. }
            clearbody sf sl.
            zstep. if_cases K8; zify_cond K8.
            * eapply sr_slow_end; eassumption.
            * eapply sr_slow_loop with (j := 0%Z); try eassumption; try reflexivity; try lia. f_equal; lia.
          + subst sbs. eapply sr_exit; try eassumption.
      Qed.
    End Phase.
  End Facts.
End S.
