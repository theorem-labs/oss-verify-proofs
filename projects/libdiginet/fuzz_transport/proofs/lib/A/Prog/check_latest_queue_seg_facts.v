(* check_latest_queue_seg_facts: the model steps of TCb.v queue_loop and the small memory / arithmetic facts the
   image-A walk of check_latest_queue (lib/A/Prog/check_latest_queue_cgW.v) uses at every step.

   The model. check_latest_queue_m Bw = Some (Bw', tt) says: Bw' = Bw, S_queued Bw = g_nq Bw (the first test of the
   code), and queue_loop ran to Some true from i = 0. queue_loop carries the running `same` INTO the next turn, so a
   turn whose test fails makes every later turn return Some false (clq_false); hence a run that ends Some true has
   every turn's test true, which is what the code's two traps need (clq_step), and it ends only by i reaching g_nq
   (clq_exit).

   The memory. clq_rd reads c bytes at b + k inside ONE payload of TMAP_A as sub Bw (o + k) c, in the form the kit's
   load step takes (the leaf form's view csw_view, lib/A/Prog/check_state_wake_c.v). clq_zsh is "every byte of
   [lo, lo + n) has shadow byte 0 in raw memory": the instrumented check of a load inside such a range reads 0 and
   falls through, so no __asan_report_* entry is reached. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorldLemmas TSess0.
Import ListNotations.
Open Scope Z_scope.

Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.

(* ============================================================================
   The model
   ============================================================================ *)

(* Once `same` is false the loop answers Some false, whatever is left of the fuel. *)
Lemma clq_false : forall fuel Bw i r, TC.queue_loop fuel Bw i false = Some r -> r = false.
Proof.
  intros [|fuel] Bw i r H; [discriminate H|].
  cbn [TC.queue_loop andb] in H. injection H as H. congruence.
Qed.

(* The loop ends at i >= g_nq with the `same` it was called with. *)
Lemma clq_exit : forall fuel Bw i r, TC.queue_loop fuel Bw i true = Some r -> TW.g_nq Bw <= i -> r = true.
Proof.
  intros [|fuel] Bw i r H Hi; [discriminate H|].
  cbn [TC.queue_loop] in H. rewrite (proj2 (Z.ltb_ge _ _) Hi) in H. cbn [andb] in H.
  injection H as H. congruence.
Qed.

(* One turn: the three index bounds the instrumented loads need, the length test and the byte test of the code,
   and the loop at i + 1. *)
Lemma clq_step : forall fuel Bw i, TC.queue_loop (S fuel) Bw i true = Some true -> i < TW.g_nq Bw ->
  i < TC.CMDS_MAX /\ TW.Q_at Bw i < TC.CMDS_MAX /\ i < TC.QUEUE_MAX /\
  TW.S_queue_len Bw i = TW.Cmd_len Bw (TW.Q_at Bw i) /\
  TW.zs (TW.sub Bw (TW.A_S_queue_bytes i) (Z.to_nat (TW.Cmd_len Bw (TW.Q_at Bw i))))
  = TW.zs (TW.sub Bw (TW.A_Cmd_bytes (TW.Q_at Bw i)) (Z.to_nat (TW.Cmd_len Bw (TW.Q_at Bw i)))) /\
  TC.queue_loop fuel Bw (i + 1) true = Some true.
Proof.
  intros fuel Bw i H Hi. cbn [TC.queue_loop] in H.
  rewrite (proj2 (Z.ltb_lt _ _) Hi) in H. cbn [andb] in H.
  destruct (TC.CMDS_MAX <=? i) eqn:C1; [discriminate H|].
  destruct (TC.CMDS_MAX <=? TW.Q_at Bw i) eqn:C2; [discriminate H|].
  destruct (TC.QUEUE_MAX <=? i) eqn:C3; [discriminate H|].
  apply Z.leb_gt in C1. apply Z.leb_gt in C2. apply Z.leb_gt in C3.
  destruct ((TW.S_queue_len Bw i =? TW.Cmd_len Bw (TW.Q_at Bw i)) &&
            TC.beq_bytes (TW.sub Bw (TW.A_S_queue_bytes i) (Z.to_nat (TW.Cmd_len Bw (TW.Q_at Bw i))))
                         (TW.sub Bw (TW.A_Cmd_bytes (TW.Q_at Bw i))
                                 (Z.to_nat (TW.Cmd_len Bw (TW.Q_at Bw i)))))%bool eqn:Eb.
  2: { exfalso. pose proof (clq_false _ _ _ _ H) as Hr. discriminate Hr. }
  apply andb_true_iff in Eb as [E1 E2]. apply Z.eqb_eq in E1.
  unfold TC.beq_bytes in E2.
  destruct (list_eq_dec Z.eq_dec
              (TW.zs (TW.sub Bw (TW.A_S_queue_bytes i) (Z.to_nat (TW.Cmd_len Bw (TW.Q_at Bw i)))))
              (TW.zs (TW.sub Bw (TW.A_Cmd_bytes (TW.Q_at Bw i))
                              (Z.to_nat (TW.Cmd_len Bw (TW.Q_at Bw i)))))) as [Ez|Ez]; [|discriminate E2].
  split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact E1|]. split; [exact Ez|].
  exact H.
Qed.

(* What the statement's model premise gives the walk. *)
Lemma clq_model : forall Bw Bw', TC.check_latest_queue_m Bw = Some (Bw', tt) ->
  Bw' = Bw /\ TW.S_queued Bw = TW.g_nq Bw /\
  TC.queue_loop (S (Z.to_nat TC.QUEUE_MAX)) Bw 0 true = Some true.
Proof.
  intros Bw Bw' H. unfold TC.check_latest_queue_m in H. cbv zeta in H.
  destruct (TC.queue_loop (S (Z.to_nat TC.QUEUE_MAX)) Bw 0 (TW.S_queued Bw =? TW.g_nq Bw)) as [same|] eqn:E;
    [|discriminate H].
  destruct same; cbn [negb] in H; [|discriminate H].
  assert (HQ : (TW.S_queued Bw =? TW.g_nq Bw) = true).
  { destruct (TW.S_queued Bw =? TW.g_nq Bw) eqn:Eb; [reflexivity|].
    exfalso. pose proof (clq_false _ _ _ _ E) as Hr. discriminate Hr. }
  rewrite HQ in E.
  pose proof (f_equal (fun o : option (list byte * unit) => match o with Some (b, _) => b | None => Bw end) H)
    as HB. cbv beta iota in HB.
  split; [symmetry; exact HB|]. split; [apply Z.eqb_eq; exact HQ | exact E].
Qed.

(* ============================================================================
   The world at the machine's view
   ============================================================================ *)

(* A load of c bytes at b + k inside ONE payload, in the form the kit's load step reads. *)
Lemma clq_rd : forall (m : word -> option byte) Bw o b n k (c : nat),
  tw_at TMAP_A (csw_view m) Bw -> In (o, b, n) TMAP_A -> 0 <= k -> k + Z.of_nat c <= n ->
  ov_read_bytes rsegs m (wa (b + k)) c = Some (TW.sub Bw (o + k) c).
Proof.
  intros m Bw o b n k c HW Hin Hk Hkc.
  pose proof (tw_row TMAP_A o b n TMAP_A_ok Hin) as (Ho & Hn & HoW & Hb & Hb64).
  pose proof (tw_bytes_at rsegs m TMAP_A Bw o b n k c TMAP_A_ok HW Hin Hk Hkc) as BF.
  assert (LB : Z.of_nat (length Bw) = TW.W_LEN).
  { rewrite (tw_len TMAP_A _ Bw HW). apply Z2Nat.id. unfold TW.W_LEN. lia. }
  assert (L : length (TW.sub Bw (o + k) c) = c) by (apply TWL.length_sub; lia).
  replace (wa (b + k)) with (wa (b + k + 0)) by (unfold wa; f_equal; lia).
  rewrite (bytes_at_read rsegs m (b + k) _ 0 c BF ltac:(lia)) by (rewrite L; lia).
  cbn [Z.to_nat skipn]. f_equal. apply firstn_all2. rewrite L. lia.
Qed.

(* A run that writes only [lo, hi), outside the hull of the 18 payloads, keeps the world. *)
Lemma clq_kept : forall (m m' : word -> option byte) lo hi Bw,
  tw_at TMAP_A (csw_view m) Bw -> munch [(lo, hi)] m m' ->
  (hi <= TG.G_HARNESS_LO \/ TG.G_HARNESS_HI <= lo) -> tw_at TMAP_A (csw_view m') Bw.
Proof.
  intros m m' lo hi Bw H MU D. unfold csw_view in *. exact (TMAP_A_kept m m' lo hi Bw H MU D).
Qed.

(* ============================================================================
   The zero shadow of a payload, at the machine's view
   ============================================================================ *)

(* Every byte of [lo, lo + n) has shadow byte 0 in m. *)
Definition clq_zsh (m : word -> option byte) (lo n : Z) : Prop :=
  forall a, lo <= a < lo + n -> mrd rsegs m (wa (shadow_addr a)) = Some (Z_to_bv 8 0).

Lemma clq_zsh_sub : forall m lo n lo' n', clq_zsh m lo n -> lo <= lo' -> lo' + n' <= lo + n ->
  clq_zsh m lo' n'.
Proof. intros m lo n lo' n' H H1 H2 a Ha. apply H. lia. Qed.

(* The shadow byte read of the check of a load at a, in the form the kit's load step takes. *)
Lemma clq_zsh_rd : forall m lo n a, clq_zsh m lo n -> lo <= a < lo + n ->
  ov_read_bytes rsegs m (wa (a / 8 + ASAN_K)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m lo n a H Ha. apply rd1. exact (H a Ha).
Qed.

(* The shadow byte 0 is signed 0, so the check's `bne` is not taken. *)
Lemma clq_sxb0 : bv_signed (Z_to_bv 8 0) = 0.
Proof. reflexivity. Qed.

(* The shadow bytes survive a store outside shadow memory (the frame store of the prologue). *)
Lemma clq_zsh_tp : forall (m m' : word -> option byte) (sp lo n : Z),
  clq_zsh m lo n -> munch [(sp - 80, sp)] m m' -> app_mem (sp - 80) -> app_mem (sp - 1) ->
  0 <= lo -> lo + n <= LOWMEM_END -> clq_zsh m' lo n.
Proof.
  intros m m' sp lo n H MU A1 A2 H0 Hn a Ha.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A1, A2, Hn.
  unfold shadow_addr, ASAN_K in *.
  eapply mrd_tp; [exact MU | | | exact (H a Ha)].
  - Z.div_mod_to_equations; lia.
  - destruct A1 as [A1|A1]; destruct A2 as [A2|A2]; Z.div_mod_to_equations; lia.
Qed.

(* ============================================================================
   The machine words of the comparisons
   ============================================================================ *)

Lemma clq_shr3 : forall z, Z.shiftr z 3 = z / 8.
Proof. intros z. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma clq_eqb_lit : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec x y) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E.
  assert (E2 : (x - y) mod 2^64 = 0) by (rewrite Zminus_mod, E, Z.sub_diag; reflexivity).
  apply Z.mod_divide in E2; [|lia]. destruct E2 as [c Ec]. nia.
Qed.

Lemma clq_eqb0 : forall v, -2^63 <= v < 2^63 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof. intros v Hv. apply clq_eqb_lit; lia. Qed.

(* `blt` / `bge` of a literal with a sign-extended shadow byte. *)
Lemma clq_lts_lit : forall (x : Z) (k : byte), -2^63 <= x < 2^63 ->
  bv_lts (Z_to_bv 64 x) (sxb k) = (x <? bv_signed k).
Proof.
  intros x k Hx. unfold bv_lts, sxb. pose proof (byte_signed_range k).
  rewrite !signed_lit by lia. reflexivity.
Qed.

Lemma clq_wrap64_7 : bv_wrap 64 7 = 7.
Proof. reflexivity. Qed.

(* The ranges of the world values the loop loads. *)
Lemma clq_rng4 : forall Bw k, 0 <= TW.u_at Bw k 4 < 2 ^ 32.
Proof. intros Bw k. exact (TWL.u_at_range Bw k 4). Qed.
Lemma clq_rng1 : forall Bw k, 0 <= TW.u_at Bw k 1 < 2 ^ 8.
Proof. intros Bw k. exact (TWL.u_at_range Bw k 1). Qed.
Lemma clq_rngs4 : forall Bw k, -2 ^ 31 <= TW.s32_at Bw k < 2 ^ 31.
Proof. intros Bw k. exact (TWL.s32_range Bw k). Qed.

(* Two u32 values are equal exactly when their sign extensions are: the first test of the code against the
   model's S_queued = g_nq. *)
Lemma clq_s32_eq : forall Bw k1 k2, (TW.s32_at Bw k1 =? TW.s32_at Bw k2) = (TW.u_at Bw k1 4 =? TW.u_at Bw k2 4).
Proof.
  intros Bw k1 k2. unfold TW.s32_at.
  pose proof (clq_rng4 Bw k1) as R1. pose proof (clq_rng4 Bw k2) as R2.
  destruct (Z.eqb_spec (TW.u_at Bw k1 4) (TW.u_at Bw k2 4)) as [E|E].
  - rewrite E. apply Z.eqb_refl.
  - apply Z.eqb_neq. intros HH. apply E.
    unfold bv_swrap, bv_wrap in HH. change (bv_modulus 32) with (2 ^ 32) in HH.
    change (bv_half_modulus 32) with (2 ^ 31) in HH.
    rewrite !(Z.mod_small _ (2 ^ 32)) in HH by lia. lia.
Qed.

(* `slli x, 32` then `srli x, 32`: the zero extension of the low 32 bits, which the code uses to turn the
   sign-extended g_s.queued into the unsigned loop counter. *)
Lemma clq_slsr : forall v u, 0 <= u < 2 ^ 32 -> v mod 2 ^ 32 = u ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 v)) 32))) 32 = u.
Proof.
  intros v u Hu Hv.
  assert (HM : forall z, (z mod (2 ^ 32 * 2 ^ 32)) mod 2 ^ 32 = z mod 2 ^ 32).
  { intros z. pose proof (Z.div_mod z (2 ^ 32 * 2 ^ 32) ltac:(lia)) as D.
    replace (z mod (2 ^ 32 * 2 ^ 32)) with (z - 2 ^ 32 * (2 ^ 32 * (z / (2 ^ 32 * 2 ^ 32)))) by lia.
    replace (2 ^ 32 * (2 ^ 32 * (z / (2 ^ 32 * 2 ^ 32))))
      with ((2 ^ 32 * (z / (2 ^ 32 * 2 ^ 32))) * 2 ^ 32) by ring.
    rewrite Zminus_mod, Z_mod_mult, Z.sub_0_r, Zmod_mod. reflexivity. }
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite Z.shiftl_mul_pow2 by lia.
  replace (2 ^ 64) with (2 ^ 32 * 2 ^ 32) by reflexivity.
  rewrite Z.mul_mod_distr_r by lia.
  rewrite Z.div_mul by lia.
  rewrite HM. exact Hv.
Qed.

(* A signed and an unsigned 32-bit reading of the world agree modulo 2 ^ 32. *)
Lemma clq_s32_mod : forall Bw k, TW.s32_at Bw k mod 2 ^ 32 = TW.u_at Bw k 4.
Proof.
  intros Bw k. pose proof (clq_rng4 Bw k) as R.
  unfold TW.s32_at, bv_swrap, bv_wrap, bv_half_modulus.
  unfold bv_modulus.
  change (2 ^ Z.of_N 32) with (2 ^ 32).
  rewrite Zminus_mod_idemp_l.
  replace (TW.u_at Bw k 4 + 2 ^ 32 / 2 - 2 ^ 32 / 2) with (TW.u_at Bw k 4) by lia.
  apply Z.mod_small. lia.
Qed.
