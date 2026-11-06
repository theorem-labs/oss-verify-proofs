(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIcpm9j.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
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
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition imemset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (c : Z) (n : nat) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + Z.of_nat n)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' (bv_unsigned a0) [CB n (repeat (Z_to_bv 8 c) n)].

Lemma upd_repeat_skipn : forall (cb : byte) (junk : list byte) (j : nat),
  (j < length junk)%nat ->
  upd (repeat cb j ++ skipn j junk) j cb = repeat cb (S j) ++ skipn (S j) junk.
Proof.
  intros cb junk j Hj.
  rewrite upd_firstn_skipn by (rewrite length_app, repeat_length, length_skipn; lia).
  rewrite firstn_app, repeat_length, Nat.sub_diag, firstn_O, app_nil_r.
  rewrite firstn_all2 by (rewrite repeat_length; lia).
  rewrite skipn_app, repeat_length. replace (S j - j)%nat with 1%nat by lia.
  rewrite skipn_all2 by (rewrite repeat_length; lia). cbn [app].
  rewrite skipn_skipn. replace (1 + j)%nat with (S j) by lia.
  replace (repeat cb (S j)) with (repeat cb j ++ [cb]) by (rewrite <- repeat_cons, repeat_app || (replace (S j) with (j + 1)%nat by lia; rewrite repeat_app; reflexivity)).
  rewrite <- app_assoc. reflexivity.
Qed.

Section IMS.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : Z) (n : nat) (junk : list byte).
  Notation A := (bv_unsigned a0).
  Hypothesis Hc : c = (bv_unsigned a1 mod 256)%Z.
  Hypothesis LJ : length junk = n.
  Hypothesis AB : (0 <= A /\ A + Z.of_nat n < 2^64)%Z.
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + Z.of_nat n)]%Z.
  Notation POST := (imemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 c n m).

  #[using="AB LJ Hc"] Lemma ims_loop : forall (k : nat) (i : Z) (m1 : word -> option byte) (x13 : word),
    (n - Z.to_nat i = k)%nat -> (0 <= i < Z.of_nat n)%Z -> x13 = Z_to_bv 64 (A + i) ->
    u8arr rsegs m1 A (repeat (Z_to_bv 8 c) (Z.to_nat i) ++ skipn (Z.to_nat i) junk) ->
    mem_inv rsegs m1 -> munch W m m1 -> wmono rsegs m m1 ->
    evt rsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (A + Z.of_nat n)) x13 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x6a2a8) fc None m1 (seg_rom rsegs)).
  Proof.
    induction k as [|k IH]; intros i m1 x13 Hk Hi -> ARR MI MU WM; [lia|].
    pose proof (zr_word a1) as R1; unfold inr64 in R1.
    assert (Rc : (0 <= c < 256)%Z) by (subst c; apply Z.mod_pos_bound; lia).
    assert (LA : length (repeat (Z_to_bv 8 c) (Z.to_nat i) ++ skipn (Z.to_nat i) junk) = n).
    { rewrite length_app, repeat_length, length_skipn. lia. }
    pose proof (u8arr_store_ok rsegs _ _ _ i (Z_to_bv 64 (A + i)) ARR ltac:(rewrite LA; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zstep. rewrite le1_byte. rewrite <- Hc.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mq ?a _) _) =>
      replace (write_to_mem mq a [Z_to_bv 8 c]) with (write_to_mem mq (wa (A + i)) [Z_to_bv 8 c]) by (unfold wa; f_equal; f_equal; lia) end.
    pose proof (u8arr_write rsegs _ _ _ i (Z_to_bv 8 c) ARR ltac:(rewrite LA; lia)) as ARR2. clear ARR.
    store_done.
    rewrite upd_repeat_skipn in ARR2 by lia.
    assert (ARR3 : u8arr rsegs m0 A (repeat (Z_to_bv 8 c) (Z.to_nat (i + 1)) ++ skipn (Z.to_nat (i + 1)) junk)).
    { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. exact ARR2. }
    clear ARR2.
    zstep. zstep. if_cases K; zify_cond K; rewrite ?Z.mod_small in K by lia.
    - apply (IH (i + 1)%Z); try assumption; try lia. f_equal; lia.
    - (* [comment removed for export] *)
      assert (E : (i + 1 = Z.of_nat n)%Z) by lia.
      zstep. zstep.
      rewrite E, Nat2Z.id, <- LJ, skipn_all, app_nil_r in ARR3.
      apply rw_cells_of_u8arr in ARR3. rewrite repeat_length, LJ in ARR3.
      finish.
  Qed.
End IMS.

Lemma imemset_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (n : nat) (junk : list byte),
  rw_cells rsegs m (bv_unsigned a0) [CB n junk] -> (bv_unsigned a0 + Z.of_nat n < 2^64)%Z ->
  bv_unsigned a2 = Z.of_nat n -> (1 <= n)%nat ->
  (Z.land (Z.of_nat n) 15 <> 0)%Z ->          (* [comment removed for export] *)
  mem_inv rsegs m ->
  evt rsegs (imemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 (bv_unsigned a1 mod 256) n m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6a290) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros DST A64 N EN1 NB MI.
  pose proof (munch_refl [(bv_unsigned a0, bv_unsigned a0 + Z.of_nat n)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (rw_CB_length _ _ _ _ _ DST) as LJ.
  pose proof (zr_word a0) as R0; unfold inr64 in R0. pose proof (zr_word a2) as R2; unfold inr64 in R2.
  zstep. zstep.
  rewrite Z.land_lor_distr_l.
  zstep. if_cases K0; zify_cond K0.
  { exfalso. rewrite N in K0. apply Z.lor_eq_0_iff in K0. lia. }
  zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
  zstep. zstep. rewrite N.
  eapply (ims_loop ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m _ n junk eq_refl LJ ltac:(lia) (n - 0)%nat 0%Z);
    try eassumption; try lia.
  - rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned.
  - cbn [Z.to_nat repeat skipn app]. exact (u8arr_of_rw_cells _ _ _ _ _ DST).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint strchr_scan (c : Z) (bs : list byte) (i : nat) : option (nat + unit) :=
  match bs with
  | [] => None
  | b :: bs' => if (bv_unsigned b =? c)%Z then Some (inl i)
                else if (bv_unsigned b =? 0)%Z then Some (inr tt)
                else strchr_scan c bs' (S i)
  end.
Definition strchr_scan_val (A : Z) (r : nat + unit) : Z :=
  match r with inl j => (A + Z.of_nat j)%Z | inr _ => 0%Z end.

Lemma skipn_cons_of_nth : forall (bs : list byte) i b, nth_error bs i = Some b -> skipn i bs = b :: skipn (S i) bs.
Proof.
  induction bs as [|x bs IH]; intros [|i] b H; cbn in H |- *; try discriminate.
  - inversion H. reflexivity.
  - exact (IH i b H).
Qed.

Definition istrchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (v : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom rsegs)
    /\ munch [] m m /\ wmono rsegs m m /\ mem_inv rsegs m.

Section ISC.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A c : Z) (bs : list byte) (r : nat + unit).
  Hypothesis STR : bytes_at rsegs m A bs.
  Hypothesis Rc : (0 <= c < 256)%Z.
  Hypothesis SC : strchr_scan c bs 0 = Some r.
  Hypothesis MI : mem_inv rsegs m.
  Notation POST := (istrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (strchr_scan_val A r) m).

  (* [comment removed for export] *)
  #[using="MI SC Rc STR"] Lemma isc_loop : forall (k i : nat) (x10 x11 : word) (b : byte),
    (length bs - i = k)%nat -> nth_error bs i = Some b -> (bv_unsigned b <> c)%Z ->
    strchr_scan c (skipn i bs) i = Some r ->
    x10 = Z_to_bv 64 (A + Z.of_nat i) ->
    evt rsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 (Z_to_bv 64 c) (Z_to_bv 64 (bv_unsigned b)) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x6a354) fc None m (seg_rom rsegs)).
  Proof.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    induction k as [|k IH]; intros i x10 x11 b Hk Hb NB SCi ->.
    { exfalso. assert (IL : (i < length bs)%nat); [|lia].
      destruct (Nat.lt_ge_cases i (length bs)) as [L|G]; [exact L|]. rewrite (proj2 (nth_error_None bs i) G) in Hb. discriminate. }
    pose proof (bytes_at_bound _ _ _ _ STR) as AB. pose proof (bv_unsigned_in_range _ b) as BR.
    assert (IL : (i < length bs)%nat).
    { destruct (Nat.lt_ge_cases i (length bs)) as [L|G]; [exact L|]. rewrite (proj2 (nth_error_None bs i) G) in Hb. discriminate. }
    rewrite (skipn_cons_of_nth _ _ _ Hb) in SCi. cbn [strchr_scan] in SCi.
    replace (bv_unsigned b =? c)%Z with false in SCi by (symmetry; apply Z.eqb_neq; exact NB).
    zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      replace (bv_unsigned b =? 0)%Z with true in SCi by (symmetry; apply Z.eqb_eq; lia). inversion SCi; subst.
      zstep. zstep. cbn [strchr_scan_val]. finish.
    - replace (bv_unsigned b =? 0)%Z with false in SCi by (symmetry; apply Z.eqb_neq; lia).
      destruct (nth_error bs (S i)) as [b2|] eqn:Hb2.
      2:{ exfalso. rewrite skipn_all2 in SCi by (apply nth_error_None in Hb2; lia). cbn in SCi. discriminate. }
      pose proof (bv_unsigned_in_range _ b2) as BR2.
      pose proof (u8ro_read rsegs m A _ (Z.of_nat (S i)) b2 (Z_to_bv 64 (A + Z.of_nat i + 1)) STR
                    ltac:(rewrite Nat2Z.id; exact Hb2) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      zstep. cbv beta. zstep. zstep.
      zstep. if_cases K1; zify_cond K1.
      + (* [comment removed for export] *)
        apply (IH (S i) _ _ b2); try reflexivity; try lia; [exact Hb2 | exact SCi | f_equal; lia].
      + (* [comment removed for export] *)
        rewrite (skipn_cons_of_nth _ _ _ Hb2) in SCi. cbn [strchr_scan] in SCi.
        replace (bv_unsigned b2 =? c)%Z with true in SCi by (symmetry; apply Z.eqb_eq; lia). inversion SCi; subst.
        zstep. zstep. cbn [strchr_scan_val].
        replace (A + Z.of_nat i + 1)%Z with (A + Z.of_nat (S i))%Z by lia. finish.
  Qed.

  #[using="MI SC Rc STR bs"] Lemma istrchr_body : forall x11 x12 x13,
    bv_unsigned x11 mod 256 = c ->
    evt rsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) x11 x12 x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x6a344) fc None m (seg_rom rsegs)).
  Proof.
    intros x11 x12 x13 Hc.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bytes_at_bound _ _ _ _ STR) as AB. pose proof (zr_word x11) as R11; unfold inr64 in R11.
    destruct bs as [|b0 bs'] eqn:Ebs; [cbn in SC; discriminate|]. rewrite <- Ebs in *.
    assert (Hb0 : nth_error bs 0 = Some b0) by (rewrite Ebs; reflexivity).
    pose proof (bv_unsigned_in_range _ b0) as BR0.
    pose proof (u8ro_read rsegs m A _ 0 b0 (Z_to_bv 64 A) STR ltac:(exact Hb0) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. cbv beta. zstep.
    (* [comment removed for export] *)
    replace (Z.land (bv_unsigned x11) 255) with c by (change 255%Z with (Z.ones 8); rewrite Z.land_ones by lia; symmetry; exact Hc).
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      apply (isc_loop (length bs - 0)%nat 0%nat _ _ b0); try reflexivity; try lia; [exact Hb0| | rewrite Z.add_0_r; reflexivity].
      cbn [skipn]. exact SC.
    - (* [comment removed for export] *)
      rewrite Ebs in SC. cbn [strchr_scan] in SC. replace (bv_unsigned b0 =? c)%Z with true in SC by (symmetry; apply Z.eqb_eq; lia).
      inversion SC; subst. zstep. cbn [strchr_scan_val]. rewrite Z.add_0_r. finish.
  Qed.
End ISC.

(* [comment removed for export] *)
Lemma istrchr_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (A c : Z) (bs : list byte) (r : nat + unit),
  bytes_at rsegs m A bs -> mem_inv rsegs m ->
  bv_unsigned a1 mod 256 = c ->
  strchr_scan c bs 0 = Some r ->
  evt rsegs (istrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (strchr_scan_val A r) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x6a344) fc None m (seg_rom rsegs)).
Proof.
  intros until r. intros STR MI Hc SC.
  pose proof (Z.mod_pos_bound (bv_unsigned a1) 256 ltac:(lia)) as CB. rewrite Hc in CB.
  eapply istrchr_body; try eassumption; lia.
Qed.
