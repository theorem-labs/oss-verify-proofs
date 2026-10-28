(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjNumber.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma shz_read : forall (m : mem) a n E adr, shz m a n -> a <= E < a + n -> adr = wa (E / 8 + 2147450880) ->
  ov_read_bytes bsegs m adr 1 = Some [Z_to_bv 8 0].
Proof. intros m a n E adr H HE ->. exact (H E HE). Qed.

Lemma div8_add : forall B j, B mod 8 = 0 -> (B + 8 * j) / 8 = B / 8 + j.
Proof. intros B j HB. rewrite Z.mul_comm, Z.div_add by lia. reflexivity. Qed.

Lemma shz_run : forall (m : mem) B j k, B mod 8 = 0 -> 0 <= B -> 0 <= j ->
  bytes_at bsegs m (B / 8 + 2147450880 + j) (repeat (Z_to_bv 8 0) k) -> shz m (B + 8 * j) (8 * Z.of_nat k).
Proof.
  intros m B j k B8 B0 J0 HB. apply (shz_of_zero_run m (B + 8 * j) k).
  - replace (B + 8 * j) with (B + j * 8) by lia. rewrite Z.mod_add by lia. exact B8.
  - lia.
  - unfold shad, SHB. rewrite div8_add by exact B8. replace (B / 8 + j + 2147450880) with (B / 8 + 2147450880 + j) by lia. exact HB.
Qed.

Lemma shz_run0 : forall (m : mem) B k, B mod 8 = 0 -> 0 <= B ->
  bytes_at bsegs m (B / 8 + 2147450880) (repeat (Z_to_bv 8 0) k) -> shz m B (8 * Z.of_nat k).
Proof.
  intros m B k B8 B0 HB. replace B with (B + 8 * 0) at 1 by lia. apply shz_run; [exact B8| exact B0| lia|].
  rewrite Z.add_0_r. exact HB.
Qed.

Lemma zr_read1 : forall (m : mem) S k a j, bytes_at bsegs m S (repeat (Z_to_bv 8 0) k) -> 0 <= j < Z.of_nat k -> a = wa (S + j) ->
  ov_read_bytes bsegs m a 1 = Some [Z_to_bv 8 0].
Proof.
  intros m S k a j HB Hj ->. rewrite (bytes_read1_at bsegs m S _ j (wa (S + j)) HB ltac:(rewrite repeat_length; lia) eq_refl).
  rewrite nth_repeat. reflexivity.
Qed.

Lemma bvu_z8 : bv_unsigned (Z_to_bv 8 0) = 0.
Proof. reflexivity. Qed.

Lemma land7_mod8 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Section AMem.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.

Definition fp_ok (Σ : rts RT) (lo : Z) (W : list (Z * Z)) : Prop :=
  Forall (fun r => (lo <= fst r /\ snd r <= USTACK_TOP)
                   \/ (exists p k, In (p, k) (rt_live RT Σ) /\ p <= fst r /\ snd r <= p + k)
                   \/ (exists f c, In (f, c) (rt_frames RT Σ) /\ f <= fst r /\ snd r <= f + fs_size c - 8)
                   \/ (exists f c, In (f, c) (rt_frames RT Σ) /\ shad f <= fst r /\ snd r <= shad (f + fs_size c))) W.

Lemma art_of_munch : forall Σ (m m' : mem) lo W, ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= lo -> fp_ok Σ lo W ->
  munch W m m' -> wmono bsegs m m' -> ART RT Σ m'.
Proof using AF.
  intros Σ m m' lo W HA LO FP MU WM. apply (art_client_write RT AF Σ m m' lo HA LO); [| exact WM].
  intros a Ha. apply MU. clear MU. induction W as [|[wl wh] W IH]; [exact I|]. inversion FP as [|? ? H1 H2]; subst.
  cbn [outside]. split; [| exact (IH H2)]. intros Hin. apply Ha. cbn [fst snd] in H1.
  destruct H1 as [H1|[(p & k & Hp & P1 & P2)|[(f & c & Hf & P1 & P2)|(f & c & Hf & P1 & P2)]]].
  - left. lia.
  - right; right; left. exists p, k. split; [exact Hp| lia].
  - right; right; right; left. exists f, c. split; [exact Hf| lia].
  - right; right; right; right. exists f, c. split; [exact Hf| lia].
Qed.

Lemma shzp_live : forall Σ (m0 : mem) lo W p n, ART RT Σ m0 -> rt_sp0 RT Σ - STACK_WIN <= lo -> fp_ok Σ lo W ->
  In (p, n) (rt_live RT Σ) -> p mod 8 = 0 ->
  forall m', munch W m0 m' -> wmono bsegs m0 m' -> shz m' p (8 * (n / 8)).
Proof using AF.
  intros Σ m0 lo W p n HA LO FP Hin P8 m' MU WM.
  exact (shz_live RT AF Σ m' p n (art_of_munch Σ m0 m' lo W HA LO FP MU WM) Hin P8).
Qed.

Lemma shz_stack : forall Σ (m : mem) a n, ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= a -> a + n <= USTACK_TOP -> a mod 8 = 0 ->
  shz m a (8 * (n / 8)).
Proof using AF.
  intros Σ m a n HA A1 A2 A8. pose proof (af_sp0_range RT AF Σ m HA) as SPR.
  apply shz_of_acc; [exact (af_acc_stack RT AF Σ m a n HA A1 A2)| exact A8| ul].
Qed.

Lemma shzp_stack : forall Σ (m0 : mem) lo W a n, ART RT Σ m0 -> rt_sp0 RT Σ - STACK_WIN <= lo -> fp_ok Σ lo W ->
  rt_sp0 RT Σ - STACK_WIN <= a -> a + n <= USTACK_TOP -> a mod 8 = 0 ->
  forall m', munch W m0 m' -> wmono bsegs m0 m' -> shz m' a (8 * (n / 8)).
Proof using AF.
  intros Σ m0 lo W a n HA LO FP A1 A2 A8 m' MU WM.
  exact (shz_stack Σ m' a n (art_of_munch Σ m0 m' lo W HA LO FP MU WM) A1 A2 A8).
Qed.

Lemma shzp_lits : forall Σ (m0 : mem) lo W a n, num_lits_acc RT -> ART RT Σ m0 -> rt_sp0 RT Σ - STACK_WIN <= lo -> fp_ok Σ lo W ->
  In (a, n) NUM_LITS ->
  forall m', munch W m0 m' -> wmono bsegs m0 m' -> shz m' a (8 * (n / 8)).
Proof using AF.
  intros Σ m0 lo W a n NL HA LO FP Hin m' MU WM.
  pose proof (NL Σ m' (art_of_munch Σ m0 m' lo W HA LO FP MU WM)) as F. rewrite Forall_forall in F. specialize (F (a, n) Hin). cbn [fst snd] in F.
  apply shz_of_acc; [exact F| |]; unfold NUM_LITS in Hin; cbn [In] in Hin;
    destruct Hin as [E|[E|[]]]; inversion E; subst; [reflexivity | reflexivity | lia | lia].
Qed.

Lemma agree_pres : forall live frames sp (m m' : mem) (P : Z -> Prop),
  rt_pres live frames sp m m' -> (forall x, P x -> aclient live frames sp x) -> agree_on P m m'.
Proof. intros. eapply agree_of_pres; eassumption. Qed.

Lemma u8arr_agree : forall (m m' : mem) A bs, u8arr bsegs m A bs ->
  agree_on (fun x => A <= x < A + Z.of_nat (length bs)) m m' -> wmono bsegs m m' -> u8arr bsegs m' A bs.
Proof.
  intros m m' A bs [HB HW] AG WM. split; [exact (bytes_at_agree bsegs m m' A bs HB AG)| exact (wr_at_transport bsegs m m' A _ HW WM)].
Qed.

Lemma pres_ex_of_munch : forall live frames sp d n W (m m' : mem),
  munch W m m' -> (forall a, aclient live frames sp a -> ~ (d <= a < d + n) -> outside W a) -> rt_pres_ex live frames sp d n m m'.
Proof. intros live frames sp d n W m m' MU H a Ha Hd. apply MU. exact (H _ Ha Hd). Qed.

Lemma pres_ex_of_pres : forall live frames sp sp' d n (m m' : mem), rt_pres live frames sp' m m' -> sp' <= sp -> rt_pres_ex live frames sp d n m m'.
Proof.
  intros live frames sp sp' d n m m' H Hsp a Ha _. apply H.
  eapply aclient_mono; [exact Ha| auto| auto| exact Hsp].
Qed.

Lemma pres_ex_of_pres_ex : forall live frames sp sp' d n (m m' : mem), rt_pres_ex live frames sp' d n m m' -> sp' <= sp -> rt_pres_ex live frames sp d n m m'.
Proof.
  intros live frames sp sp' d n m m' H Hsp a Ha Hd. apply H; [| exact Hd].
  eapply aclient_mono; [exact Ha| auto| auto| exact Hsp].
Qed.

Lemma pres_ex_trans : forall live frames sp d n (m1 m2 m3 : mem),
  rt_pres_ex live frames sp d n m1 m2 -> rt_pres_ex live frames sp d n m2 m3 -> rt_pres_ex live frames sp d n m1 m3.
Proof. intros live frames sp d n m1 m2 m3 H1 H2 a Ha Hd. rewrite (H2 a Ha Hd). exact (H1 a Ha Hd). Qed.

Lemma pres_fp_of_munch : forall live frames sp FP W (m m' : mem),
  munch W m m' -> (forall a, aclient live frames sp a -> outside FP a -> outside W a) -> rt_pres_fp live frames sp FP m m'.
Proof. intros live frames sp FP W m m' MU H a Ha Hd. apply MU. exact (H _ Ha Hd). Qed.

Lemma pres_fp_sp : forall live frames sp sp' FP (m m' : mem), rt_pres_fp live frames sp' FP m m' -> sp' <= sp -> rt_pres_fp live frames sp FP m m'.
Proof.
  intros live frames sp sp' FP m m' H Hsp a Ha Hd. apply H; [| exact Hd].
  eapply aclient_mono; [exact Ha| auto| auto| exact Hsp].
Qed.

Lemma pres_fp_trans : forall live frames sp FP (m1 m2 m3 : mem),
  rt_pres_fp live frames sp FP m1 m2 -> rt_pres_fp live frames sp FP m2 m3 -> rt_pres_fp live frames sp FP m1 m3.
Proof. intros live frames sp FP m1 m2 m3 H1 H2 a Ha Hd. rewrite (H2 a Ha Hd). exact (H1 a Ha Hd). Qed.

Lemma pres_fp_refl : forall live frames sp FP (m : mem), rt_pres_fp live frames sp FP m m.
Proof. intros live frames sp FP m a _ _. reflexivity. Qed.

Lemma agree_pres_fp : forall live frames sp FP (m m' : mem) (P : Z -> Prop),
  rt_pres_fp live frames sp FP m m' -> (forall x, P x -> aclient live frames sp x /\ outside FP x) -> agree_on P m m'.
Proof. intros. eapply agree_of_pres_fp; eassumption. Qed.

Lemma pres_ex_refl : forall live frames sp d n (m : mem), rt_pres_ex live frames sp d n m m.
Proof. intros live frames sp d n m a _ _. reflexivity. Qed.

End AMem.

Ltac aclient_tac :=
  first [ left; unfold USTACK_TOP in *; lia
        | right; right; left; match goal with H : In (?p, ?n) _ |- _ => exists p, n; split; [exact H| lia] end
        | right; right; right; left; match goal with H : In (?f, ?k) _ |- _ => exists f, k; split; [exact H| first [lia | unfold fs_size; cbn; lia]] end
        | right; right; right; right; match goal with H : In (?f, ?k) _ |- _ =>
            exists f, k; split; [exact H| first [ unfold shad, SHB; Z.div_mod_to_equations; lia | unfold shad, SHB, fs_size; cbn; Z.div_mod_to_equations; lia ]] end ].

Ltac rt_transport_with m m' AG WM side :=
  repeat match goal with
  | H : bytes_at bsegs m ?A ?bs |- _ =>
      first [ let Q := fresh "AGQ" in
              assert (Q : agree_on (fun x => A <= x < A + Z.of_nat (length bs)) m m') by (eapply agree_sub; [exact AG| side]);
              apply (fun X => bytes_at_agree bsegs m m' A bs X Q) in H; clear Q
            | idtac "note: dropping (not a client fact across the call):" H; clear H ]
  | H : rw_cells bsegs m ?A ?cs |- _ =>
      first [ let Q := fresh "AGQ" in
              assert (Q : agree_on (fun x => A <= x < A + Z.of_nat (cells_size cs)) m m') by (eapply agree_sub; [exact AG| side]);
              apply (fun X => rw_cells_agree bsegs m m' A cs X Q WM) in H; clear Q
            | idtac "note: dropping (not a client fact across the call):" H; clear H ]
  | H : ro_cells bsegs m ?A ?cs |- _ =>
      first [ let Q := fresh "AGQ" in
              assert (Q : agree_on (fun x => A <= x < A + Z.of_nat (cells_size cs)) m m') by (eapply agree_sub; [exact AG| side]);
              apply (fun X => ro_cells_agree bsegs m m' A cs X Q) in H; clear Q
            | clear H ]
  | H : u8arr bsegs m ?A ?bs |- _ =>
      first [ let Q := fresh "AGQ" in
              assert (Q : agree_on (fun x => A <= x < A + Z.of_nat (length bs)) m m') by (eapply agree_sub; [exact AG| side]);
              apply (fun X => u8arr_agree m m' A bs X Q WM) in H; clear Q
            | idtac "note: dropping (not a client fact across the call):" H; clear H ]
  | H : wr_at bsegs m ?A ?n |- _ => apply (wr_at_transport bsegs m m' A n) in H; [| exact WM]
  end.

Ltac asan_load_hook :=
  match goal with
  | |- context [ov_read_bytes bsegs ?m ?a 1] =>
      let Ea := addr_expr a in
      lazymatch Ea with
      | (?E / 8 + 2147450880)%Z =>
          first
          [ match goal with
            | SHP : (forall m', munch ?W ?m0 m' -> wmono bsegs ?m0 m' -> shz m' ?a0 ?n0), MU : munch ?W ?m0 m, WM : wmono bsegs ?m0 m |- _ =>
                rewrite (shz_read m a0 n0 E a (SHP m MU WM) ltac:(lia) ltac:(reflexivity))
            end
          | match goal with
            | SZ : shz m ?a0 ?n0 |- _ => rewrite (shz_read m a0 n0 E a SZ ltac:(lia) ltac:(reflexivity))
            end
          | match goal with
            | ZR : bytes_at bsegs m (?B / 8 + 2147450880)%Z (repeat (Z_to_bv 8 0) ?k) |- _ =>
                rewrite (shz_read m B (8 * Z.of_nat k)%Z E a (shz_run0 m B k ltac:(assumption) ltac:(lia) ZR)
                           ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) ltac:(reflexivity))
            end
          | match goal with
            | ZR : bytes_at bsegs m (?B / 8 + 2147450880 + ?j)%Z (repeat (Z_to_bv 8 0) ?k) |- _ =>
                rewrite (shz_read m (B + 8 * j)%Z (8 * Z.of_nat k)%Z E a (shz_run m B j k ltac:(assumption) ltac:(lia) ltac:(lia) ZR)
                           ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) ltac:(reflexivity))
            end ]
      end
  end;
  load_post.

Ltac asan_zr_hook :=
  match goal with
  | |- context [ov_read_bytes bsegs ?m ?a 1] =>
      let Ea := addr_expr a in
      match goal with
      | ZR : bytes_at bsegs m ?S (repeat (Z_to_bv 8 0) ?k) |- _ =>
          rewrite (zr_read1 m S k a (Ea - S)%Z ZR ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) ltac:(unfold wa; f_equal; lia))
      end
  end;
  load_post.

Ltac anorm :=
  repeat match goal with
  | |- context [Z.shiftr ?x 3] => rewrite (shr3_div x)
  end;
  rewrite ?sxb_z8, ?zxb_z8; cbv beta; rewrite ?bvu_z8.
Ltac astep := nstep; anorm.

Ltac zastep := zstep; anorm.

Ltac awalk_fuel n K :=
  lazymatch n with
  | O => lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail 100 "awalk: out of fuel at" pc end
  | S ?n' =>
      lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => first [ K pc | (astep; awalk_fuel n' K) ]
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
          let H := fresh "KB" in
          if_cases H; zify_cond H; num_signed_lits_in H;
          tryif num_is_data H then (clear H; awalk_fuel n' K) else first [ solve [exfalso; lia] | awalk_fuel n' K ]
      end
  end.
Ltac awalk K := awalk_fuel 400%nat K.
Ltac awalkd_fuel n K :=
  lazymatch n with
  | O => idtac "awalkd: out of fuel"
  | S ?n' =>
      lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => first [ K pc | (astep; awalkd_fuel n' K) | idtac "STUCK at" pc ]
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
          let H := fresh "KB" in
          if_cases H; zify_cond H; num_signed_lits_in H;
          tryif num_is_data H then (clear H; awalkd_fuel n' K) else first [ solve [exfalso; lia] | awalkd_fuel n' K ]
      end
  end.
Ltac awalkd K := awalkd_fuel 400%nat K.
