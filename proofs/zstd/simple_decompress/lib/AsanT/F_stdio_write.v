(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Decode SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad Stdio.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import Stdio_pure.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg F_syscalls StdioFiles Stdio_kit MonadF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

Ltac showregsM :=
  lazymatch goal with
  | |- context [MS ?R _ _ _ _ _ _] =>
      let pr n := (let p := eval vm_compute in (bv_key (Z_to_bv 5 n)) in
                   let v := eval cbv beta iota delta [tget mkR] in (tget p R) in idtac n ":=" v) in
      pr 1%Z; pr 2%Z; pr 8%Z; pr 9%Z; pr 10%Z; pr 11%Z; pr 12%Z; pr 13%Z; pr 14%Z; pr 15%Z; pr 18%Z; pr 19%Z; pr 20%Z; pr 21%Z; pr 22%Z
  end.

Section CANSEC1. Context {rc : runConstT}.
Definition STDIO_WRITE : Z := 0xbc334.
Definition STDIO_WRITE_DEPTH : Z := 112.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition iovs_of (buf s : list Z) : list (list Z) :=
  match buf with [] => [s] | _ => [buf; s] end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zlength_to_bytes : forall l, zlength (to_bytes l) = zlength l.
Proof. intros l. unfold zlength, to_bytes. rewrite length_map. reflexivity. Qed.
Lemma length_to_bytes : forall l, length (to_bytes l) = length l.
Proof. intros l. unfold to_bytes. apply length_map. Qed.
Lemma zlength_skipn : forall {A} n (l : list A), zlength (skipn n l) = zlength l - Z.of_nat (Nat.min n (length l)).
Proof. intros A n l. unfold zlength. rewrite length_skipn. lia. Qed.
Lemma to_bytes_skipn : forall n l, to_bytes (skipn n l) = skipn n (to_bytes l).
Proof. intros n l. unfold to_bytes. rewrite skipn_map. reflexivity. Qed.
Lemma iov_total_1 : forall b, iov_total [b] = zlength b.
Proof. intros b. unfold iov_total, zlength. cbn. rewrite app_nil_r. reflexivity. Qed.
Lemma iov_total_2 : forall a b, iov_total [a; b] = zlength a + zlength b.
Proof. intros a b. unfold iov_total, zlength. cbn. rewrite app_nil_r, length_app. lia. Qed.

Section StdioWrite.
  Context {St : Type}.

  Definition stdio_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (Fp : Z) (flags : word) (B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
      (l : Z) (lo : Z) (canary : word) (m : mem) (st : St) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - STDIO_WRITE_DEPTH, bv_unsigned sp); (Fp + 32, Fp + 64)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ rw_cells bsegs m' Fp (file_cells flags (B + bufsize) B B wfn B bufsize fd mode lbf tail)
      /\ ssp_cells m' canary
      /\ st' = st.

  Section Body.
    Variables (RNG : footprint) (ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
    Variables (m : mem) (st : St) (Fp : Z) (flags : word) (wend B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
              (buf s : list Z) (S lo : Z) (canary : word).
    Local Notation q := (bv_unsigned sp + -112).
    Let POST := stdio_write_post ra sp gp tp s0i s1i s2i s3i s4i s5i s6i s7 s8 s9 s10 s11 F fc Fp flags B bufsize wfn fd mode lbf tail
                                 (zlength s) lo canary m st.
    Hypothesis FD : fd = 1 \/ fd = 2.
    Hypothesis LO : lo <= bv_unsigned sp - STDIO_WRITE_DEPTH.
    Hypothesis GLO : GLOBALS_TOP <= lo.
    Hypothesis Fp0 : 0 <= Fp. Hypothesis FPLO : Fp + 232 <= lo.
    Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
    Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
    Hypothesis B0 : 0 <= B. Hypothesis BS0 : 0 <= bufsize. Hypothesis BUFLE : zlength buf <= bufsize. Hypothesis BShi : B + bufsize < 2^64.
    Hypothesis S0 : 0 <= S < 2^64. Hypothesis Shi : S + zlength s <= 2^64.
    (* [comment removed for export] *)
    Hypothesis SP47 : bv_unsigned sp < 2^47. Hypothesis B47 : B + bufsize <= 2^47. Hypothesis S47 : S + zlength s <= 2^47.
    Hypothesis SEPS : s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp + 32 \/ Fp + 64 <= S)).
    Hypothesis SEPB : buf = [] \/ ((B + zlength buf <= lo \/ bv_unsigned sp <= B) /\ (B + zlength buf <= Fp + 32 \/ Fp + 64 <= B)).
    Hypothesis FC0 : rw_cells bsegs m Fp (file_cells flags wend (B + zlength buf) B wfn B bufsize fd mode lbf tail).
    Hypothesis ST0 : stk bsegs m lo (bv_unsigned sp).
    Hypothesis SSP0 : ssp_cells m canary.
    Hypothesis MI0 : mem_inv bsegs m.
    Hypothesis BUFB : bytes_at bsegs m B (to_bytes buf).
    Hypothesis SRC : bytes_at bsegs m S (to_bytes s).
    (* [comment removed for export] *)
    Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
    Hypothesis RFP : rng RNG Fp 232.
    Hypothesis RB : rng RNG B (zlength buf).
    Hypothesis RS : rng RNG S (zlength s).
    Hypothesis RIMG : rng_aimg RNG.

    (* [comment removed for export] *)
    Definition frame (j0 : list byte) (w1 w2 w3 w4 : word) : list cell :=
      [CB 8 j0; C8 w1; C8 w2; C8 w3; C8 w4; C8 canary; C8 s6i; C8 s5i; C8 s4i; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 ra].

    (* [comment removed for export] *)
    Definition data_ok (p : Z) (l : list Z) : Prop :=
      bytes_at bsegs m p (to_bytes l)
      /\ p + zlength l <= 2^47
      /\ (l = [] \/ ((p + zlength l <= lo \/ bv_unsigned sp <= p) /\ (p + zlength l <= Fp + 32 \/ Fp + 64 <= p)))
      /\ rng RNG p (zlength l).

    Lemma data_ok_rng : forall p l, data_ok p l -> rng RNG p (Z.of_nat (length (to_bytes l))).
    Proof. intros p l (_ & _ & _ & R). rewrite length_to_bytes. exact R. Qed.

    Lemma data_ok_task : forall p l, data_ok p l -> p + Z.of_nat (length (to_bytes l)) <= 0x800000000000.
    Proof. intros p l (_ & H & _). rewrite length_to_bytes. unfold zlength in H. exact H. Qed.

    (* [comment removed for export] *)
    Definition iov_rel (iov : list (list Z)) (iovp iovcnt : Z) (w1 w2 w3 w4 : word) : Prop :=
      match iov with
      | [b] => iovp = q + 24 /\ iovcnt = 1 /\ w4 = Z_to_bv 64 (zlength b) /\ data_ok (bv_unsigned w3) b
      | [a; b] => iovp = q + 8 /\ iovcnt = 2 /\ w2 = Z_to_bv 64 (zlength a) /\ w4 = Z_to_bv 64 (zlength b)
               /\ data_ok (bv_unsigned w1) a /\ data_ok (bv_unsigned w3) b
               /\ bv_unsigned w1 + zlength a < 2^64   (* [comment removed for export] *)
      | _ => False
      end.

    Lemma data_ok_now : forall m1 p l,
      data_ok p l -> munch [(bv_unsigned sp - 112, bv_unsigned sp); (Fp + 32, Fp + 64)] m m1 ->
      bytes_at bsegs m1 p (to_bytes l).
    Proof.
      intros m1 p l (BA & _ & SEP & _) MU. pose proof (bytes_at_bound _ _ _ _ BA) as BB. rewrite length_to_bytes in BB.
      destruct SEP as [-> | [S1 S2]].
      - apply bytes_at_nil. cbn in BB. lia.
      - apply (bytes_at_transport _ _ _ m1 _ _ BA MU). cbn [disjoint_from]. rewrite length_to_bytes.
        unfold zlength, STDIO_WRITE_DEPTH in *. lia.
    Qed.

    Lemma data_ok_skipn : forall p l k, data_ok p l -> 0 <= k <= zlength l -> data_ok (p + k) (skipn (Z.to_nat k) l).
    Proof.
      intros p l k (BA & T47 & SEP & RR) Hk. pose proof (bytes_at_bound _ _ _ _ BA) as BB. rewrite length_to_bytes in BB.
      split; [| split; [rewrite zlength_skipn; unfold zlength in *; lia| split]].
      - rewrite to_bytes_skipn. replace (p + k) with (p + Z.of_nat (Z.to_nat k)) by lia.
        rewrite <- (firstn_skipn (Z.to_nat k) (to_bytes l)) in BA. apply bytes_at_app in BA as [_ BA].
        rewrite length_firstn, length_to_bytes in BA.
        replace (Nat.min (Z.to_nat k) (length l)) with (Z.to_nat k) in BA by (unfold zlength in Hk; lia).
        exact BA.
      - destruct (Z.eq_dec k (zlength l)) as [->|NE].
        + left. apply skipn_all2. unfold zlength. lia.
        + destruct SEP as [-> | [S1 S2]]. { exfalso. unfold zlength in *. cbn in *. lia. }
          right. rewrite zlength_skipn. unfold zlength in *. split; lia.
      - rewrite zlength_skipn. eapply rng_sub; [exact RR| lia| unfold zlength in *; lia].
    Qed.

    (* [comment removed for export] *)
    Lemma data_ok_skipn_w : forall p l k, data_ok p l -> 0 <= k <= zlength l -> p + k < 2^64 ->
      data_ok (bv_unsigned (Z_to_bv 64 (p + k))) (skipn (Z.to_nat k) l).
    Proof.
      intros p l k D Hk LT. pose proof (bytes_at_bound _ _ _ _ (proj1 D)) as BB.
      rewrite unsigned_lit by lia. apply data_ok_skipn; assumption.
    Qed.

    (* [comment removed for export] *)
    Lemma frame_iov2 : forall m1 j0 w1 w2 w3 w4, rw_cells bsegs m1 q (frame j0 w1 w2 w3 w4) ->
      bytes_at bsegs m1 (bv_unsigned sp + -104) (iovec_bytes [(w1, w2); (w3, w4)]).
    Proof.
      intros m1 j0 w1 w2 w3 w4 FR.
      change (frame j0 w1 w2 w3 w4) with ([CB 8 j0] ++ [C8 w1; C8 w2; C8 w3; C8 w4] ++ [C8 canary; C8 s6i; C8 s5i; C8 s4i; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 ra]) in FR.
      apply rw_cells_app in FR as [_ FR]. apply rw_cells_app in FR as [FR _].
      cbn [cells_size csize Nat.add] in FR. replace (q + Z.of_nat 8) with (bv_unsigned sp + -104) in FR by lia.
      eapply bytes_at_ext; [exact (rw_cells_bytes_at _ _ _ _ FR)|]. cbn [cells_bytes cbytes iovec_bytes flat_map fst snd].
      rewrite !app_nil_r, <- ?app_assoc. reflexivity.
    Qed.
    Lemma frame_iov1 : forall m1 j0 w1 w2 w3 w4, rw_cells bsegs m1 q (frame j0 w1 w2 w3 w4) ->
      bytes_at bsegs m1 (bv_unsigned sp + -88) (iovec_bytes [(w3, w4)]).
    Proof.
      intros m1 j0 w1 w2 w3 w4 FR.
      change (frame j0 w1 w2 w3 w4) with ([CB 8 j0; C8 w1; C8 w2] ++ [C8 w3; C8 w4] ++ [C8 canary; C8 s6i; C8 s5i; C8 s4i; C8 s3i; C8 s2i; C8 s1i; C8 s0i; C8 ra]) in FR.
      apply rw_cells_app in FR as [_ FR]. apply rw_cells_app in FR as [FR _].
      cbn [cells_size csize Nat.add] in FR. replace (q + Z.of_nat 24) with (bv_unsigned sp + -88) in FR by lia.
      eapply bytes_at_ext; [exact (rw_cells_bytes_at _ _ _ _ FR)|]. cbn [cells_bytes cbytes iovec_bytes flat_map fst snd].
      rewrite !app_nil_r, <- ?app_assoc. reflexivity.
    Qed.

    (* [comment removed for export] *)
    Lemma ok_path : forall (m1 : mem) (j0 : list byte) (w1 w2 w3 w4 : word)
        (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x28 x29 x30 x31 : word),
      rw_cells bsegs m1 q (frame j0 w1 w2 w3 w4) ->
      rw_cells bsegs m1 Fp (file_cells flags wend (B + zlength buf) B wfn B bufsize fd mode lbf tail) ->
      rw_cells bsegs m1 got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells bsegs m1 ssp_guard [C8 canary] ->
      mem_inv bsegs m1 ->
      munch [(bv_unsigned sp - 112, bv_unsigned sp); (Fp + 32, Fp + 64)] m m1 -> wmono bsegs m m1 ->
      stk bsegs m1 lo q ->
      evtF bsegs RNG (POST tt st)
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
                   x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 ssp_guard) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0xbc3c8) fc None m1 (seg_rom bsegs)).
    Proof.
      intros until x31. intros FR FC GOT GUARD MI MU WM ST.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      unfold got_ssp, ssp_guard, STDIO_WRITE_DEPTH, GLOBALS_TOP, frame, file_cells in *.
      do 7 step.
      do 3 step. if_false. do 10 step.
      release_frame FR ST (bv_unsigned sp).
      subst POST. unfold stdio_write_post, STDIO_WRITE_DEPTH, file_cells, ssp_cells, got_ssp, ssp_guard. sys_finish.
      reflexivity.
    Qed.

    (* [comment removed for export] *)
    Ltac sysret_fast ret :=
      zstep; zstep; zstep; zstep;
      let Hr := fresh "Hr" in (if_cases Hr; zify_cond Hr); [ | exfalso; lia ];
      zstep; replace (ret_pc (Z_to_bv 64 ret)) with (Z_to_bv 64 ret : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    (* [comment removed for export] *)
    Lemma loop_L2 : forall (fuel : nat) (iov : list (list Z)) (c : Z) (m1 : mem) (j0 : list byte) (w1 w2 w3 w4 : word) (iovp iovcnt : Z)
        (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word),
      iov_rel iov iovp iovcnt w1 w2 w3 w4 ->
      rw_cells bsegs m1 q (frame j0 w1 w2 w3 w4) ->
      rw_cells bsegs m1 Fp (file_cells flags wend (B + zlength buf) B wfn B bufsize fd mode lbf tail) ->
      rw_cells bsegs m1 got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells bsegs m1 ssp_guard [C8 canary] ->
      mem_inv bsegs m1 ->
      munch [(bv_unsigned sp - 112, bv_unsigned sp); (Fp + 32, Fp + 64)] m m1 -> wmono bsegs m m1 ->
      stk bsegs m1 lo q ->
      0 <= c < iov_total iov -> iov_total iov <= 67108864 ->
      implAM RNG (stdio_write_loop fuel fd (iov_advance iov c)) st POST
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 (Z_to_bv 64 (zlength s)) (Z_to_bv 64 Fp)
                   (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 iovcnt) (Z_to_bv 64 iovp) x20 (Z_to_bv 64 ssp_guard)
                   (Z_to_bv 64 (iov_total iov)) s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0xbc454) fc None m1 (seg_rom bsegs)).
    Proof.
      induction fuel as [|fuel IH]; intros until x31; intros IR FR FC GOT GUARD MI MU WM ST Hc TOT.
      { cbn [stdio_write_loop]. apply implAM_unr. }
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      unfold got_ssp, ssp_guard, STDIO_WRITE_DEPTH, GLOBALS_TOP, frame, file_cells in *.
      (* [comment removed for export] *)
      Ltac cont IH total iov' FR FC GOT GUARD MI MU WM ST DATA :=
        let rsp := fresh "rsp" in let ans := fresh "ans" in let Hdec := fresh "Hdec" in let ci := fresh "ci" in
        let Hans := fresh "Hans" in let Hcase := fresh "Hcase" in let Keq := fresh "Keq" in
        intros rsp ans Hdec; apply dec_writev_Some in Hdec as (ci & -> & Hans & Hcase);
        replace (iov_total iov') with total in Hcase by (rewrite ?iov_total_1, ?iov_total_2, ?zlength_skipn; unfold zlength in *; lia);
        apply implAM_from_evt; sys_nret;
        sysret_fast 0xbc44c%Z;
        zstep; zstep; (if_cases Keq; zify_cond Keq);
        [ apply evtF_done; replace (ans =? iov_total iov') with true by (symmetry; apply Z.eqb_eq; rewrite ?iov_total_1, ?iov_total_2, ?zlength_skipn; unfold zlength in *; lia);
          apply implAM_ret;
          eapply ok_path; first [exact FR | exact FC | exact GOT | exact GUARD | exact MI | exact MU | exact WM | exact ST]
        | apply evtF_done; replace (ans =? iov_total iov') with false by (symmetry; apply Z.eqb_neq; rewrite ?iov_total_1, ?iov_total_2, ?zlength_skipn; unfold zlength in *; lia);
          replace (Z_to_bv 64 total : word) with (Z_to_bv 64 (iov_total iov') : word)
            by (f_equal; rewrite ?iov_total_1, ?iov_total_2, ?zlength_skipn; unfold zlength in *; lia);
          lazymatch type of FR with rw_cells _ ?mf _ (CB 8 ?j0 :: C8 ?v1 :: C8 ?v2 :: C8 ?v3 :: C8 ?v4 :: _) =>
            eapply (IH iov' _ mf j0 v1 v2 v3 v4) end;
          first [exact FR | exact FC | exact GOT | exact GUARD | exact MI | exact MU | exact WM | exact ST
                | rewrite ?iov_total_1, ?iov_total_2, ?zlength_skipn; unfold zlength in *; lia
                | cbn [iov_rel]; DATA ] ].
      destruct iov as [|a [|b [|? ?]]]; try contradiction.
      - (* [comment removed for export] *)
        rename a into b. destruct IR as (-> & -> & -> & DB).
        pose proof (bytes_at_bound _ _ _ _ (proj1 DB)) as BB. rewrite length_to_bytes in BB.
        change (Z.of_nat (length b)) with (zlength b) in BB.
        rewrite iov_total_1 in *.
        assert (Zb : 0 <= zlength b) by (unfold zlength; lia).
        cbn [stdio_write_loop]. (apply implAM_sysk; [exact I|]).
        zstep. if_cases Kneg; zify_cond Kneg. { exfalso. lia. }
        zstep. zstep.
        replace (zlength b <? c) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
        change (iov_advance [b] c) with [skipn (Z.to_nat c) b].
        do 5 zstep. rewrite Z.land_0_l. zstep. rewrite Z.sub_0_r. zstep. zstep. zstep.
        if_cases Kd; zify_cond Kd. 2:{ exfalso. lia. }
        zstep. zstep. zstep. do 8 zstep.
        replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd : word) by (symmetry; apply sx32_small; lia).
        step_ecall.
        split.
        { at_nodeA_red; split_spine; try reflexivity; try lia; try solve_rng;
            try (cbn [map concat length]; rewrite ?app_nil_r, ?length_app, ?length_to_bytes, ?length_skipn; unfold zlength in *; lia);
              try (rewrite unsigned_lit by lia; cbn [map length]; lia).
          1:{ rewrite unsigned_lit by lia. cbn [map length]. eapply rng_sub; [exact RSTK| lia| lia]. }
          eexists [(_, _)]. split.
          + rewrite unsigned_lit by lia. eapply frame_iov1. exact FR.
          + constructor; [|constructor]. split; [| split; [| split]].
            * cbn [snd]. rewrite length_to_bytes, length_skipn. f_equal. unfold zlength in *. lia.
            * cbn [fst]. apply (data_ok_task _ _ (data_ok_skipn_w _ _ c DB ltac:(lia) ltac:(lia))).
            * cbn [fst]. apply (data_ok_now _ _ _ (data_ok_skipn_w _ _ c DB ltac:(lia) ltac:(lia)) MU).
            * cbn [fst]. exact (data_ok_rng _ _ (data_ok_skipn_w _ _ c DB ltac:(lia) ltac:(lia))). }
        cont IH (zlength b - c) [skipn (Z.to_nat c) b] FR FC GOT GUARD MI MU WM ST
             ltac:(idtac; split; [lia|]; split; [reflexivity|]; split; [f_equal; rewrite zlength_skipn; unfold zlength in *; lia|];
                   apply (data_ok_skipn_w _ _ c DB ltac:(lia) ltac:(lia))).
      - (* [comment removed for export] *)
        destruct IR as (-> & -> & -> & -> & DA & DB & LTA).
        pose proof (bytes_at_bound _ _ _ _ (proj1 DA)) as BA. pose proof (bytes_at_bound _ _ _ _ (proj1 DB)) as BB.
        rewrite length_to_bytes in BA, BB.
        change (Z.of_nat (length a)) with (zlength a) in BA. change (Z.of_nat (length b)) with (zlength b) in BB.
        rewrite iov_total_2 in *.
        assert (Za : 0 <= zlength a) by (unfold zlength; lia). assert (Zb : 0 <= zlength b) by (unfold zlength; lia).
        cbn [stdio_write_loop]. (apply implAM_sysk; [exact I|]).
        zstep. if_cases Kneg; zify_cond Kneg. { exfalso. lia. }
        zstep. zstep.
        destruct (Z.ltb_spec0 (zlength a) c) as [DROP|NODROP].
        + (* [comment removed for export] *)
          replace (zlength a <? c) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
          replace (iov_advance [a; b] c) with [skipn (Z.to_nat (c - zlength a)) b]
            by (cbn [iov_advance]; destruct (Z.ltb_spec0 (zlength a) c); [reflexivity|lia]).
          do 5 zstep.
          replace (Z.land 18446744073709551615 (zlength a)) with (zlength a)
            by (change 18446744073709551615 with (2^64-1); rewrite zb_land_mask_l by lia; rewrite Z.mod_small by lia; reflexivity).
          zstep. zstep. zstep. zstep. if_cases Kd; zify_cond Kd. { exfalso. lia. }
          zstep. zstep.
          do 8 zstep.
          replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd : word) by (symmetry; apply sx32_small; lia).
          zstep. zstep. step_ecall.
          split.
          { at_nodeA_red; split_spine; try reflexivity; try lia; try solve_rng;
              try (cbn [map concat length]; rewrite ?app_nil_r, ?length_app, ?length_to_bytes, ?length_skipn; unfold zlength in *; lia);
              try (rewrite unsigned_lit by lia; cbn [map length]; lia).
            1:{ rewrite unsigned_lit by lia. cbn [map length]. eapply rng_sub; [exact RSTK| lia| lia]. }
            eexists [(_, _)]. split.
            + rewrite unsigned_lit by lia. eapply frame_iov1. exact FR.
            + constructor; [|constructor]. split; [| split; [| split]].
              * cbn [snd]. rewrite length_to_bytes, length_skipn. f_equal. unfold zlength in *. lia.
              * cbn [fst]. apply (data_ok_task _ _ (data_ok_skipn_w _ _ (c - zlength a) DB ltac:(lia) ltac:(lia))).
              * cbn [fst]. apply (data_ok_now _ _ _ (data_ok_skipn_w _ _ (c - zlength a) DB ltac:(lia) ltac:(lia)) MU).
              * cbn [fst]. exact (data_ok_rng _ _ (data_ok_skipn_w _ _ (c - zlength a) DB ltac:(lia) ltac:(lia))). }
          cont IH (zlength a + zlength b - c) [skipn (Z.to_nat (c - zlength a)) b] FR FC GOT GUARD MI MU WM ST
               ltac:(idtac; split; [lia|]; split; [reflexivity|]; split; [f_equal; rewrite zlength_skipn; unfold zlength in *; lia|];
                     apply (data_ok_skipn_w _ _ (c - zlength a) DB ltac:(lia) ltac:(lia))).
        + (* [comment removed for export] *)
          replace (zlength a <? c) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
          replace (iov_advance [a; b] c) with [skipn (Z.to_nat c) a; b]
            by (cbn [iov_advance]; destruct (Z.ltb_spec0 (zlength a) c); [lia|reflexivity]).
          do 5 zstep. rewrite Z.land_0_l. zstep. rewrite Z.sub_0_r. zstep. zstep. zstep.
          if_cases Kd; zify_cond Kd. 2:{ exfalso. lia. }
          zstep. zstep. zstep. do 8 zstep.
          replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd : word) by (symmetry; apply sx32_small; lia).
          step_ecall.
          split.
          { at_nodeA_red; split_spine; try reflexivity; try lia; try solve_rng;
              try (cbn [map concat length]; rewrite ?app_nil_r, ?length_app, ?length_to_bytes, ?length_skipn; unfold zlength in *; lia);
              try (rewrite unsigned_lit by lia; cbn [map length]; lia).
            1:{ rewrite unsigned_lit by lia. cbn [map length]. eapply rng_sub; [exact RSTK| lia| lia]. }
            eexists [(_, _); (_, _)]. split.
            + rewrite unsigned_lit by lia. eapply frame_iov2. exact FR.
            + constructor; [|constructor; [|constructor]]; (split; [| split; [| split]]).
              * cbn [snd]. rewrite length_to_bytes, length_skipn. f_equal. unfold zlength in *. lia.
              * cbn [fst]. apply (data_ok_task _ _ (data_ok_skipn_w _ _ c DA ltac:(lia) ltac:(lia))).
              * cbn [fst]. apply (data_ok_now _ _ _ (data_ok_skipn_w _ _ c DA ltac:(lia) ltac:(lia)) MU).
              * cbn [fst]. exact (data_ok_rng _ _ (data_ok_skipn_w _ _ c DA ltac:(lia) ltac:(lia))).
              * cbn [snd]. rewrite length_to_bytes. reflexivity.
              * cbn [fst]. apply (data_ok_task _ _ DB).
              * cbn [fst]. apply (data_ok_now _ _ _ DB MU).
              * cbn [fst]. exact (data_ok_rng _ _ DB). }
          cont IH (zlength a + zlength b - c) [skipn (Z.to_nat c) a; b] FR FC GOT GUARD MI MU WM ST
               ltac:(idtac; split; [lia|]; split; [reflexivity|]; split; [f_equal; rewrite zlength_skipn; unfold zlength in *; lia|];
                     split; [reflexivity|]; split; [apply (data_ok_skipn_w _ _ c DA ltac:(lia) ltac:(lia)) | split; [exact DB| rewrite unsigned_lit by lia; rewrite zlength_skipn; unfold zlength in *; lia]]).
    Qed.

    (* [comment removed for export] *)
    Lemma stdio_write_body : forall (x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      implAM RNG (stdio_write (St:=St) fd buf s) st POST
            (MS (mkR ra sp gp tp x5 x6 x7 s0i s1i (Z_to_bv 64 Fp) (Z_to_bv 64 S) (Z_to_bv 64 (zlength s)) x13 x14 x15 x16 x17
                     s2i s3i s4i s5i s6i s7 s8 s9 s10 s11 x28 x29 x30 x31)
                F (Z_to_bv 64 0xbc334) fc None m (seg_rom bsegs)).
    Proof.
      intros.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof SSP0 as SSP. destruct SSP as [GOT GUARD]. pose proof FC0 as FC. pose proof ST0 as ST. pose proof MI0 as MI.
      unfold got_ssp, ssp_guard, STDIO_WRITE_DEPTH, GLOBALS_TOP, file_cells in *.
      pose proof (bytes_at_bound _ _ _ _ BUFB) as BB. pose proof (bytes_at_bound _ _ _ _ SRC) as BS.
      rewrite length_to_bytes in BB, BS. change (Z.of_nat (length buf)) with (zlength buf) in BB. change (Z.of_nat (length s)) with (zlength s) in BS.
      assert (Zb : 0 <= zlength buf) by (unfold zlength; lia). assert (Zs : 0 <= zlength s) by (unfold zlength; lia).
      assert (DBUF : data_ok B buf) by (split; [exact BUFB | split; [lia | split; [exact SEPB| exact RB]]]).
      assert (DS : data_ok S s) by (split; [exact SRC | split; [lia | split; [exact SEPS| exact RS]]]).
      change (bytes_at bsegs m S (to_bytes s)) with (boxed (bytes_at bsegs m S (to_bytes s))) in SRC.
      change (bytes_at bsegs m B (to_bytes buf)) with (boxed (bytes_at bsegs m B (to_bytes buf))) in BUFB.
      pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (Fp + 32, Fp + 64)] m) as MU.
      pose proof (wmono_refl bsegs m) as WM.
      unfold stdio_write, WRITE_MAX.
      destruct (Z.ltb_spec0 67108864 (zlength buf + zlength s)) as [BIG|LENS]. { apply implAM_unr. }
      apply Z.nlt_ge in LENS.
      cbn [stdio_write_loop]. (apply implAM_sysk; [exact I|]).
      carve_frame 112%nat ST.
      do 12 zstep. do 13 zstep.
      replace (B + zlength buf - B) with (zlength buf) in * by lia.
      lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j :: _) => set (j0 := j) in FR end.
      (* [comment removed for export] *)
      Ltac cont0 total iov0 iovp iovcnt FR FC GOT GUARD MI MU WM ST DATA :=
        let rsp := fresh "rsp" in let ans := fresh "ans" in let Hdec := fresh "Hdec" in let ci := fresh "ci" in
        let Hans := fresh "Hans" in let Hcase := fresh "Hcase" in let Keq := fresh "Keq" in
        intros rsp ans Hdec; apply dec_writev_Some in Hdec as (ci & -> & Hans & Hcase);
        replace (iov_total iov0) with total in Hcase by (rewrite ?iov_total_1, ?iov_total_2; unfold zlength in *; lia);
        apply implAM_from_evt; sys_nret;
        sysret_fast 0xbc3c4%Z;
        zstep; (if_cases Keq; zify_cond Keq);
        [ apply evtF_done; replace (ans =? iov_total iov0) with false by (symmetry; apply Z.eqb_neq; rewrite ?iov_total_1, ?iov_total_2; unfold zlength in *; lia);
          let L := fresh "L" in
          lazymatch type of FR with rw_cells _ ?mf _ (CB 8 ?j0 :: C8 ?v1 :: C8 ?v2 :: C8 ?v3 :: C8 ?v4 :: _) =>
            pose proof (fun fuel x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 =>
                          loop_L2 fuel iov0 ans mf j0 v1 v2 v3 v4 iovp iovcnt x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31) as L end;
          cbv beta in L; rewrite ?iov_total_1, ?iov_total_2 in L; unfold ssp_guard in L;
          eapply L; clear L;
          first [exact FR | exact FC | exact GOT | exact GUARD | exact MI | exact MU | exact WM | exact ST
                | unfold zlength in *; lia
                | cbn [iov_rel]; DATA ]
        | apply evtF_done; replace (ans =? iov_total iov0) with true by (symmetry; apply Z.eqb_eq; rewrite ?iov_total_1, ?iov_total_2; unfold zlength in *; lia);
          apply implAM_ret;
          eapply ok_path; first [exact FR | exact FC | exact GOT | exact GUARD | exact MI | exact MU | exact WM | exact ST] ].
      destruct buf as [|b0 buf'] eqn:Ebuf; rewrite <- ?Ebuf in *.
      - (* [comment removed for export] *)
        replace (zlength buf) with 0 in FR |- * by (rewrite Ebuf; reflexivity).
        rewrite !Z.add_0_r, !Z.add_0_l. rewrite Z.lxor_nilpotent. change (Z.b2z (0 <? 0)) with 0.
        zstep. if_cases Kb; zify_cond Kb. 2:{ exfalso. lia. }
        zstep. zstep.
        replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd : word) by (symmetry; apply sx32_small; lia).
        zstep. change (0 + 1) with 1. zstep. zstep. zstep. step_ecall.
        split.
        { at_nodeA_red; split_spine; try reflexivity; try lia; try solve_rng;
            try (cbn [map concat length]; rewrite ?app_nil_r, ?length_app, ?length_to_bytes; unfold zlength in *; lia);
            try (rewrite unsigned_lit by lia; cbn [map length]; lia).
          1:{ rewrite unsigned_lit by lia. cbn [map length]. eapply rng_sub; [exact RSTK| lia| lia]. }
          eexists [(_, _)]. split.
          + rewrite unsigned_lit by lia. eapply frame_iov1. exact FR.
          + constructor; [|constructor]. split; [| split; [| split]].
            * cbn [snd]. rewrite length_to_bytes. reflexivity.
            * cbn [fst]. rewrite unsigned_lit by lia. apply (data_ok_task _ _ DS).
            * cbn [fst]. rewrite unsigned_lit by lia. apply (data_ok_now _ _ _ DS MU).
            * cbn [fst]. rewrite unsigned_lit by lia. exact (data_ok_rng _ _ DS). }
        cont0 (zlength s) [s] (bv_unsigned sp + -88) 1 FR FC GOT GUARD MI MU WM ST
              ltac:(idtac; split; [lia|]; split; [reflexivity|]; split; [reflexivity|]; rewrite unsigned_lit by lia; exact DS).
      - (* [comment removed for export] *)
        assert (NB1 : 1 <= zlength buf) by (rewrite Ebuf; unfold zlength; cbn [length]; lia).
        replace (match buf with [] => [s] | _ :: _ => [buf; s] end) with [buf; s] by (rewrite Ebuf; reflexivity).
        assert (XNZ : Z.lxor (B + zlength buf) B <> 0).
        { intros E. rewrite <- (Z.add_0_r B) in E at 2. apply Z.lxor_eq in E. lia. }
        pose proof (Z_lxor_range (B + zlength buf) B ltac:(lia) ltac:(lia)) as XR.
        replace (0 <? Z.lxor (B + zlength buf) B) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
        zstep. if_cases Kb; zify_cond Kb. 1:{ exfalso. lia. }
        zstep. zstep. zstep.
        replace (sx32 (Z_to_bv 64 fd)) with (Z_to_bv 64 fd : word) by (symmetry; apply sx32_small; lia).
        zstep. change (1 + 1) with 2. zstep. zstep. zstep. step_ecall.
        split.
        { at_nodeA_red; split_spine; try reflexivity; try lia; try solve_rng;
            try (cbn [map concat length]; rewrite ?app_nil_r, ?length_app, ?length_to_bytes; unfold zlength in *; lia);
            try (rewrite unsigned_lit by lia; cbn [map length]; lia).
          1:{ rewrite unsigned_lit by lia. cbn [map length]. eapply rng_sub; [exact RSTK| lia| lia]. }
          eexists [(_, _); (_, _)]. split.
          + rewrite unsigned_lit by lia. eapply frame_iov2. exact FR.
          + constructor; [|constructor; [|constructor]]; (split; [| split; [| split]]).
            * cbn [snd]. rewrite length_to_bytes. reflexivity.
            * cbn [fst]. rewrite unsigned_lit by lia. apply (data_ok_task _ _ DBUF).
            * cbn [fst]. rewrite unsigned_lit by lia. apply (data_ok_now _ _ _ DBUF MU).
            * cbn [fst]. rewrite unsigned_lit by lia. exact (data_ok_rng _ _ DBUF).
            * cbn [snd]. rewrite length_to_bytes. reflexivity.
            * cbn [fst]. rewrite unsigned_lit by lia. apply (data_ok_task _ _ DS).
            * cbn [fst]. rewrite unsigned_lit by lia. apply (data_ok_now _ _ _ DS MU).
            * cbn [fst]. rewrite unsigned_lit by lia. exact (data_ok_rng _ _ DS). }
        cont0 (zlength buf + zlength s) [buf; s] (bv_unsigned sp + -104) 2 FR FC GOT GUARD MI MU WM ST
              ltac:(idtac; split; [lia|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
                    rewrite !unsigned_lit by lia; split; [exact DBUF | split; [exact DS| unfold zlength in *; lia]]).
    Qed.
  End Body.

  (* [comment removed for export] *)
  Lemma stdio_write_spec :
    forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (Fp : Z) (flags : word) (wend B bufsize wfn fd : Z) (mode : word) (lbf : Z) (tail : list byte)
           (buf s : list Z) (S lo : Z) (canary : word),
      rw_cells bsegs m Fp (file_cells flags wend (B + zlength buf) B wfn B bufsize fd mode lbf tail) ->
      bytes_at bsegs m B (to_bytes buf) ->
      bytes_at bsegs m S (to_bytes s) ->
      a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
      (fd = 1 \/ fd = 2) ->
      stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - STDIO_WRITE_DEPTH) -> (GLOBALS_TOP <= lo) ->
      ssp_cells m canary -> mem_inv bsegs m ->
      (0 <= Fp) -> (Fp + 232 <= lo) ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      (0 <= B) -> (0 <= bufsize) -> (zlength buf <= bufsize) -> (B + bufsize < 2^64) ->
      (0 <= S < 2^64) -> (S + zlength s <= 2^64) ->
      (s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp + 32 \/ Fp + 64 <= S))) ->
      (buf = [] \/ ((B + zlength buf <= lo \/ bv_unsigned sp <= B) /\ (B + zlength buf <= Fp + 32 \/ Fp + 64 <= B))) ->
      (* [comment removed for export] *)
      rng RNG lo (bv_unsigned sp - lo) -> rng RNG Fp 232 -> rng RNG B (zlength buf) -> rng RNG S (zlength s) -> rng_aimg RNG ->
      (bv_unsigned sp < 2^47) -> (B + bufsize <= 2^47) -> (S + zlength s <= 2^47) ->     (* [comment removed for export] *)
      implAM RNG (stdio_write (St:=St) fd buf s) st
            (stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp flags B bufsize wfn fd mode lbf tail
                              (zlength s) lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0xbc334) fc None m (seg_rom bsegs)).
  Proof.
    intros until canary. intros FC BUFB SRC -> -> -> FD ST LO GLO SSP MI Fp0 FPLO FSEP1 FSEP2 B0 BS0 BUFLE BShi S0 Shi SEPS SEPB RSTK RFP RB RS RIMG SP47 B47 S47.
    eapply stdio_write_body; eassumption.
  Qed.
End StdioWrite.
End CANSEC1.
