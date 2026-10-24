(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(** Functional multiplication loop adapted from the pinned Varnish proof to
    the actual zlib checksum_fuzzer instruction layout and register allocation. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import Tac Bytes.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import Img0 CrcLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require TacDiet2.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.transport_chunks segs m a bs ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Tac.footprint_after_store segs m a bs ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.mem_after_store ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Tac.transport_after_call segs m m' MU WM ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.addr_eq_tac ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.ZBridge.word_eq_tac ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.ZBridge.mlia ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require StepFast.
#[local] Ltac2 Set OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.step_core segs R F pc fc rv m ro ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.zstep ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Destzna.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Tac.destruct_exs PO ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Destzna.dk_exs PO.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Tac.destruct_ands PO ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require WeqGuard TacDiet2.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.WeqGuard.weq_guard; OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Stor0fe.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.mem_after_store ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Dieta54.
Local Ltac lia ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Dieta54.dlia.
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import CrcGenInner CrcGenModel.
Lemma zext32_SX : forall b, 0 <= b < 2^32 ->
  Z.shiftr (Z.shiftl (SX b) 32 mod 2^64) 32 = b.
Proof.
  intros b Hb. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  unfold SX, HI32. destruct (Z.ltb_spec b (2^31)); Z.div_mod_to_equations; lia.
Qed.

Lemma x2n_loop_zero : forall fuel k p, x2n_loop fuel 0 k p = p.
Proof. intros []; reflexivity. Qed.

Lemma x2n_tab_at : forall m, mem_inv rsegs m -> bytes_at rsegs m X2N_TAB x2n_bytes.
Proof. intros m MI. apply (ro_table_at rsegs m); [exact MI | vm_compute; reflexivity | unfold X2N_TAB; lia | rewrite x2n_bytes_length; unfold X2N_TAB; lia]. Qed.

Section Outer.
  Variables (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Hypothesis TABLE : bytes_at rsegs m X2N_TAB x2n_bytes.
  Variable Q : machine_state -> Prop.
  Notation AT pc x5 x10 x11 x12 x15 x16 x17 :=
    (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 x10 x11 x12 (Z_to_bv 64 0x11954) (Z_to_bv 64 18446744073402876704) x15 x16 x17
            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  Lemma x2n_outer : forall (fuel : nat) (n k p : Z) x5 x15 x16 x17,
    (fuel <= 60)%nat -> (0 < n < 2 ^ Z.of_nat fuel)%Z ->
    (0 <= k /\ k + Z.of_nat fuel < 2^63)%Z -> (0 < p < 2^32)%Z ->
    (forall x5' x11' x15' x16' x17',
       evt rsegs Q (AT 0x14d54 x5' (Z_to_bv 64 0) x11'
          (Z_to_bv 64 (SX (x2n_loop fuel n k p))) x15' x16' x17')) ->
    evt rsegs Q (AT 0x14cf8 x5 (Z_to_bv 64 n) (Z_to_bv 64 k)
      (Z_to_bv 64 (SX p)) x15 x16 x17).
  Proof.
    induction fuel as [|fuel IH]; intros n k p x5 x15 x16 x17 HF Hn Hk Hp END.
    { cbn in Hn. lia. }
    pose proof (SX_range p ltac:(lia)) as Rp.
    assert (Hn63 : (n < 2^63)%Z).
    { eapply Z.lt_le_trans; [exact (proj2 Hn)|]. apply Z.pow_le_mono_r; lia. }
    set (nn := Z.shiftr n 1).
    set (qq := if Z.land n 1 =? 0 then p else mm (tabz (Z.to_nat (Z.land k 31))) p).
    assert (Hnn : (0 <= nn < 2 ^ Z.of_nat fuel)%Z).
    { unfold nn. apply shiftr1_bound; [|lia].
      rewrite Nat2Z.inj_succ in Hn. replace (Z.succ (Z.of_nat fuel)) with (Z.of_nat fuel + 1)%Z in Hn by lia. lia. }
    assert (Hqq : (0 < qq < 2^32)%Z).
    { unfold qq. destruct (Z.land n 1 =? 0); [exact Hp|]. apply mm_tab_pos; [apply table_index_range|exact Hp]. }
    assert (MODEL : x2n_loop (S fuel) n k p = x2n_loop fuel nn (k+1) qq).
    { cbn [x2n_loop]. rewrite (proj2 (Z.eqb_neq n 0) ltac:(lia)). reflexivity. }
    rewrite MODEL in END.
    assert (CONT : forall p' x5' x15' x16' x17', p' = qq ->
      evt rsegs Q (AT 0x14cec x5' (Z_to_bv 64 n) (Z_to_bv 64 k)
        (Z_to_bv 64 (SX p')) x15' x16' x17')).
    { intros p' x5' x15' x16' x17' ->. pose proof (SX_range qq ltac:(lia)) as Rq.
      zstep. rewrite (signed_small n) by lia.
      change (Z.shiftr n 1) with nn.
      try rewrite (Z.mod_small nn 18446744073709551616) by (split; [exact (proj1 Hnn)|]; eapply Z.lt_le_trans; [exact (proj2 Hnn)|]; apply Z.pow_le_mono_r; lia).
      do 2 zstep. if_cases K; zify_cond K.
      - assert (E : (nn = 0)%Z) by lia. rewrite E, x2n_loop_zero in END. rewrite E. apply END.
      - apply (IH nn (k+1)%Z qq); try lia. exact END. }
    do 2 zstep. if_cases K; zify_cond K.
    - apply CONT. unfold qq. rewrite (proj2 (Z.eqb_eq _ _) K). reflexivity.
    - pose proof (rd_x2n rsegs m k _ TABLE eq_refl) as RD. cbv delta [X2N_TAB] in RD.
      set (i := Z.to_nat (Z.land k 31)) in RD.
      assert (Hi32 : (i < 32)%nat) by (unfold i; apply table_index_range).
      pose proof (tabz_range i Hi32) as Ht.
      do 4 zstep.
      rewrite (sx32_SX (Z_to_bv 64 (tabz i)) (tabz i) (tabz_word i Hi32) ltac:(lia)).
      do 4 zstep.
      replace (Z_to_bv 64 (-2147483648)) with (Z_to_bv 64 (SX (2 ^ Z.of_nat 31))) by (apply bv_eq; reflexivity).
      change (Z_to_bv 64 0) with (Z_to_bv 64 (SX 0)).
      eapply x2n_inner with (k:=31%nat) (a:=tabz i) (b:=p) (p:=0%Z);
        [lia|lia|lia|lia|apply lowbits_nz_init; lia|].
      intros x5' x15' x17'. apply CONT. unfold qq. rewrite (proj2 (Z.eqb_neq _ _) K). reflexivity.
  Qed.
End Outer.

(* Keep recursive arithmetic symbolic during instruction matching.
   Its defining equations and all machine certificates remain checked. *)
Opaque x2n_loop.

Definition combine_gen_post (answer : Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 answer) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom rsegs)
    /\ munch [] m m /\ wmono rsegs m m /\ mem_inv rsegs m.

Theorem crc32_combine_gen_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv rsegs m ->
  (bv_unsigned a0 <= 1048576)%Z ->
  evt rsegs (combine_gen_post (combine_gen_model (bv_unsigned a0))
     ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14ccc) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros MI Hn.
  pose proof (bv_unsigned_in_range _ a0) as Rn.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  remember (combine_gen_model (bv_unsigned a0)) as answer eqn:Eanswer.
  zstep. if_cases K; zify_cond K.
  - assert (MODEL : (combine_gen_model (bv_unsigned a0) = 2^31)%Z).
    { unfold combine_gen_model. rewrite K, x2n_loop_zero. reflexivity. }
    rewrite <- Eanswer in MODEL. rewrite MODEL. do 3 zstep. finish.
  - do 7 zstep.
    rewrite <- (Z_to_bv_bv_unsigned a0).
    replace (Z_to_bv 64 (-2147483648)) with (Z_to_bv 64 (SX (2^31))) by (apply bv_eq; reflexivity).
    replace (Z_to_bv 64 (-306674912)) with (Z_to_bv 64 18446744073402876704) by (apply bv_eq; reflexivity).
    eapply x2n_outer with (fuel:=21%nat) (n:=bv_unsigned a0) (k:=3%Z) (p:=(2^31)%Z);
      [exact (x2n_tab_at m MI)|lia|lia|lia|lia|].
    intros x5' x11' x15' x16' x17'.
    pose proof (combine_gen_model_positive (bv_unsigned a0)) as Hp.
    change (x2n_loop 21 (bv_unsigned a0) 3 (2^31)) with (combine_gen_model (bv_unsigned a0)).
    pose proof (SX_range (combine_gen_model (bv_unsigned a0)) ltac:(lia)) as Rp.
    do 3 zstep.
    pose proof (SX_mod32 (combine_gen_model (bv_unsigned a0)) ltac:(lia)) as NARROW.
    change (SX (combine_gen_model (bv_unsigned a0)) mod 4294967296 = combine_gen_model (bv_unsigned a0))%Z in NARROW.
    rewrite NARROW.
    rewrite <- Eanswer. finish.
Qed.

(** Variant matched to the driver: the bytes read must be the fixed table.
    The overlay memory itself is arbitrary and is preserved exactly. *)
Definition crc_return_post (answer : Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 answer) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom rsegs)
    /\ munch [] m m /\ wmono rsegs m m.

Theorem crc32_combine_gen_table_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  bytes_at rsegs m X2N_TAB x2n_bytes ->
  (bv_unsigned a0 <= 1048576)%Z ->
  evt rsegs (crc_return_post (combine_gen_model (bv_unsigned a0))
     ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14ccc) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros TABLE Hn.
  pose proof (bv_unsigned_in_range _ a0) as Rn.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  remember (combine_gen_model (bv_unsigned a0)) as answer eqn:Eanswer.
  zstep. if_cases K; zify_cond K.
  - assert (MODEL : (combine_gen_model (bv_unsigned a0) = 2^31)%Z).
    { unfold combine_gen_model. rewrite K, x2n_loop_zero. reflexivity. }
    rewrite <- Eanswer in MODEL. rewrite MODEL. do 3 zstep. finish.
  - do 7 zstep.
    rewrite <- (Z_to_bv_bv_unsigned a0).
    replace (Z_to_bv 64 (-2147483648)) with (Z_to_bv 64 (SX (2^31))) by (apply bv_eq; reflexivity).
    replace (Z_to_bv 64 (-306674912)) with (Z_to_bv 64 18446744073402876704) by (apply bv_eq; reflexivity).
    eapply x2n_outer with (fuel:=21%nat) (n:=bv_unsigned a0) (k:=3%Z) (p:=(2^31)%Z);
      [exact TABLE|lia|lia|lia|lia|].
    intros x5' x11' x15' x16' x17'.
    pose proof (combine_gen_model_positive (bv_unsigned a0)) as Hp.
    change (x2n_loop 21 (bv_unsigned a0) 3 (2^31)) with (combine_gen_model (bv_unsigned a0)).
    pose proof (SX_range (combine_gen_model (bv_unsigned a0)) ltac:(lia)) as Rp.
    do 3 zstep.
    pose proof (SX_mod32 (combine_gen_model (bv_unsigned a0)) ltac:(lia)) as NARROW.
    change (SX (combine_gen_model (bv_unsigned a0)) mod 4294967296 = combine_gen_model (bv_unsigned a0))%Z in NARROW.
    rewrite NARROW.
    rewrite <- Eanswer. finish.
Qed.
