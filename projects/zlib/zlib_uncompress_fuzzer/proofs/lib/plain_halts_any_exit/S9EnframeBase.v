(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_zlib_uncompress_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import
  ListFacts PropExec CatExec CatSim SeqExec StreamExec StreamSim MmapSim StepTac Hoare WalkTac StoreOk
  Frame RefMemcpyLib AgentLib MallocDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import LiaFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import RefEnframeArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Src_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments.


Definition SCT : Z := 0x1245c.




Definition sc_tbl_clear (m : word -> option byte) : Prop :=
  forall j, (0 <= j < 96)%Z -> m (Z_to_bv 64 (SCT + j)) = None.



Ltac solve_kcs :=
  repeat (apply keeps_cs_upd; [| not_kept]); first [apply keeps_cs_refl | assumption].


Record efH {RCa1 : RunCtx}  (mem : word -> option byte) (c : word)
       (g M W idx n h3 o16 stride start off : Z) : Prop := EFH {
  Estride : stride = slot_stride (w_maplen W) (w_lastidx W) (w_sizeclass W);
  Estart  : start = slot_start M stride idx;
  Eoff    : off = enframe_off (slack_of stride n)
                    ((if h3 =? 0 then bv_unsigned c else o16 + 1) mod 256);
  Hg      : 0 <= g /\ g + 40 <= 2 ^ 64;
  HM      : 0 <= M;
  HW      : 0 <= W < 2 ^ 64;
  Hidx    : 0 <= idx < 32;
  Hn      : 0 <= n /\ n + 4 <= stride;
  Hsc     : (w_maplen W = 0 \/ w_lastidx W <> 0) -> w_sizeclass W < 48;
  Hst31   : stride < 2 ^ 31;
  Hq      : stride * idx + 4096 <= 16 * 65536;
  Hnw     : start + stride < 2 ^ 64;
  Hdisj   : g + 24 <= start - 3 \/ start + stride - 4 <= g + 16;
  Hh3     : 0 <= h3 < 256;
  Ho16    : 0 <= o16 < 65536;
  RM      : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (g + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 M));
  RW      : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (g + 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 W));
  R4      : mem (Z_to_bv 64 (start - 4)) = Some (Z_to_bv 8 0);
  R3      : mem (Z_to_bv 64 (start - 3)) = Some (Z_to_bv 8 h3);
  R2      : h3 <> 0 ->
            rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (start - 2)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 o16));
  OK      : store_ok (run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (start - 3)) (Z.to_nat (stride - 1)) = true;
  TBL     : sc_tbl_clear mem }.
Arguments EFH {RCa1}.

Record enframe_post {RCa1 : RunCtx}  (mem' : word -> option byte) (idx n stride start off : Z) : Prop := EPOST {
  P_p := start + 16 * off;
  P_e := start + stride - 4;
  P_r := stride - 4 - n - 16 * off;
  P_q := stride * idx / 16 + off;
  Pm4   : mem' (Z_to_bv 64 (P_p - 4)) = Some (Z_to_bv 8 0);
  Pm3   : mem' (Z_to_bv 64 (P_p - 3)) = Some (Z_to_bv 8 (idx + 32 * res_code P_r));
  Pm2   : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem' (Z_to_bv 64 (P_p - 2)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 P_q));
  Pzr   : 0 < P_r -> mem' (Z_to_bv 64 (P_p + n)) = Some (Z_to_bv 8 0);
  Pe5   : 5 <= P_r -> mem' (Z_to_bv 64 (P_e - 5)) = Some (Z_to_bv 8 0);
  Pe4   : 5 <= P_r -> rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem' (Z_to_bv 64 (P_e - 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 P_r));
  Ps3   : off <> 0 -> mem' (Z_to_bv 64 (start - 3)) = Some (Z_to_bv 8 224);
  Ps2   : off <> 0 -> rdn (run_segments RSEGS rc_inp rc_sp rc_mb) mem' (Z_to_bv 64 (start - 2)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 off));
  Pr    : 0 <= P_r /\ 0 <= off <= 255 /\ 0 <= P_q < 65536 }.
Arguments EPOST {RCa1}.


Section Facts.
Context {RCa1 : RunCtx}.
  Variables (mem0 : word -> option byte) (c : word) (g M W idx n h3 o16 stride start off : Z).
  Hypothesis H : efH mem0 c g M W idx n h3 o16 stride start off.

  Lemma stride_facts : 16 <= stride /\ stride mod 16 = 0 /\ stride < 2 ^ 31.
  Proof.
    destruct H. clear RM0 RW0 R5 R6 R7 OK0 TBL0.
    assert (Hml : 0 <= w_maplen W) by (unfold w_maplen; apply Z.div_pos; lia).
    rewrite Estride0 in *. unfold slot_stride, UNIT in *.
    destruct (negb (w_maplen W =? 0) && (w_lastidx W =? 0))%bool eqn:E.
    - apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E2.
      destruct (w_maplen W =? 0) eqn:E3; [discriminate|]. apply Z.eqb_neq in E3.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      repeat split; lia.
    - assert (Hs : w_sizeclass W < 48).
      { apply Hsc0. destruct (w_maplen W =? 0) eqn:E3.
        + left. apply Z.eqb_eq, E3.
        + right. cbn in E. apply Z.eqb_neq. exact E. }
      assert (0 <= w_sizeclass W) by (unfold w_sizeclass; apply Z.mod_pos_bound; lia).
      pose proof (size_class_pos (w_sizeclass W) ltac:(lia)).
      repeat split; lia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Lemma off_facts : 0 <= off <= slack_of stride n /\ off <= 255
                    /\ 16 * off <= stride - 4 - n /\ 0 <= slack_of stride n.
  Proof.
    destruct H. clear RM0 RW0 R5 R6 R7 OK0 TBL0.
    pose proof (u64_range c).
    assert (Hsl : 0 <= slack_of stride n /\ 16 * slack_of stride n <= stride - 4 - n).
    { unfold slack_of, IB, UNIT.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      split; [apply Z.div_pos; lia|]. lia. }
    assert (Ho0 : 0 <= (if h3 =? 0 then bv_unsigned c else o16 + 1) mod 256 < 256)
      by (apply Z.mod_pos_bound; lia).
    pose proof (enframe_off_le (slack_of stride n) _ (proj1 Hsl) Ho0) as B.
    rewrite <- Eoff0 in B.
    pose proof (enframe_off_255 (slack_of stride n) _ (proj1 Hsl) Ho0) as B2.
    rewrite <- Eoff0 in B2.
    repeat split; lia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Lemma start_facts : 16 <= start /\ start = M + 16 + stride * idx /\ start + stride < 2 ^ 64
                      /\ 0 <= stride * idx /\ stride * idx + 4096 <= 16 * 65536.
  Proof.
    destruct H. clear RM0 RW0 R5 R6 R7 OK0 TBL0. pose proof stride_facts as (S1 & S2 & S3).
    rewrite Estart0 in *. unfold slot_start, UNIT in *. repeat split; try nia.
  Qed.
End Facts.


Ltac greg :=
  repeat match goal with
         | Hr : getr ?rs ?k = ?v |- context [getr ?rs ?k] => rewrite Hr
         end.

Ltac stb F D aa bb vtac oktac :=
  chain_step;
  [ reflexivity
  | eapply MmapSim.step_sb_at with (a := aa) (b := bb);
    [ exact F | reflexivity | exact D
    | gres; greg; imm_norm; rewrite ?v_addi_0; rewrite ?v_addi_lit by lia; first [ reflexivity | f_equal; lia ]
    | gres; greg; reflexivity | vtac | oktac ]
  | step_simpl ].

Ltac sth F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | eapply step_sh_at with (a := aa) (v := vv);
    [ exact F | reflexivity | exact D
    | gres; greg; imm_norm; rewrite ?v_addi_0; rewrite ?v_addi_lit by lia; first [ reflexivity | f_equal; lia ]
    | gres; greg; first [ reflexivity | assumption ] | oktac ]
  | step_simpl ].

Ltac stw F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | eapply step_sw_at with (a := aa) (v := vv);
    [ exact F | reflexivity | exact D
    | gres; greg; imm_norm; rewrite ?v_addi_0; rewrite ?v_addi_lit by lia; first [ reflexivity | f_equal; lia ]
    | gres; greg; first [ reflexivity | assumption ] | oktac ]
  | step_simpl ].

Ltac ldbu F D rtac :=
  chain_step;
  [ reflexivity
  | eapply step_lbu; [exact F | reflexivity | exact D
    | gres; greg; imm_norm; rewrite ?v_addi_0; rewrite ?v_addi_lit by lia; rtac ]
  | step_simpl; vnorm ].

Ltac ldhu F D vv rtac btac :=
  chain_step;
  [ reflexivity
  | eapply step_lhu with (v := vv); [exact F | reflexivity | exact D
    | gres; greg; imm_norm; rewrite ?v_addi_0; rewrite ?v_addi_lit by lia; rtac | btac ]
  | step_simpl; vnorm ].

Ltac ldd F D vv rtac :=
  chain_step;
  [ reflexivity
  | eapply step_ld with (v := vv); [exact F | reflexivity | exact D
    | gres; greg; imm_norm; rewrite ?v_addi_0; rewrite ?v_addi_lit by lia; rtac
    | apply bytes_le_to_Z_8 ]
  | step_simpl; vnorm ].


Lemma rdn1_of_mem : forall segs m (a : word) b, m a = Some b -> rdn segs m a 1 = Some [b].
Proof. intros segs m a b Hm. cbn [rdn]. rewrite Hm. reflexivity. Qed.



Lemma wbytes_miss : forall bs m (a x : word),
  (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned x)%Z ->
  wbytes m a bs x = m x.
Proof.
  intros bs m a x Hnw [Hl|Hh].
  - apply wbytes_below; assumption.
  - apply wbytes_above; assumption.
Qed.

Lemma length_wle2 : forall v : word, length (word_to_le_bytes 2 v) = 2%nat.
Proof. intros. apply length_N_to_le_bytes. Qed.
Lemma length_wle4 : forall v : word, length (word_to_le_bytes 4 v) = 4%nat.
Proof. intros. apply length_N_to_le_bytes. Qed.






Definition memT := word -> option byte.

Definition mD (start off : Z) (m : memT) : memT :=
  if off =? 0 then m else
  wbytes (wbytes (wbytes m (Z_to_bv 64 (start - 3)) [Z_to_bv 8 224])
                 (Z_to_bv 64 (start - 2)) (word_to_le_bytes 2 (Z_to_bv 64 off)))
         (Z_to_bv 64 (start + 16 * off - 4)) [Z_to_bv 8 0].

Definition mE1 (idx stride start off : Z) (m : memT) : memT :=
  wbytes (wbytes m (Z_to_bv 64 (start + 16 * off - 3)) [Z_to_bv 8 idx])
         (Z_to_bv 64 (start + 16 * off - 2))
         (word_to_le_bytes 2 (Z_to_bv 64 (stride * idx / 16 + off))).

Definition mE (idx n stride start off : Z) (m : memT) : memT :=
  let r := stride - 4 - n - 16 * off in
  let m1 := mE1 idx stride start off m in
  if r =? 0 then m1 else
  let m2 := wbytes m1 (Z_to_bv 64 (start + 16 * off + n)) [Z_to_bv 8 0] in
  if r <? 5 then m2 else
  wbytes (wbytes m2 (Z_to_bv 64 (start + stride - 4 - 5)) [Z_to_bv 8 0])
         (Z_to_bv 64 (start + stride - 4 - 4)) (word_to_le_bytes 4 (Z_to_bv 64 r)).

Definition mF (idx n stride start off : Z) (m : memT) : memT :=
  wbytes m (Z_to_bv 64 (start + 16 * off - 3))
         [Z_to_bv 8 (idx + 32 * res_code (stride - 4 - n - 16 * off))].

Lemma grows_mD : forall start off m, mem_grows m (mD start off m).
Proof.
  intros. cbv delta [mD] beta zeta. destruct (off =? 0); [apply mem_grows_refl|].
  repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
Qed.

Lemma grows_mE1 : forall idx stride start off m, mem_grows m (mE1 idx stride start off m).
Proof.
  intros. cbv delta [mE1] beta zeta.
  repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
Qed.

Lemma grows_mE : forall idx n stride start off m, mem_grows m (mE idx n stride start off m).
Proof.
  intros. cbv delta [mE] beta zeta.
  set (m1 := mE1 idx stride start off m).
  assert (G1 : mem_grows m m1) by apply grows_mE1. clearbody m1.
  destruct (_ =? 0); [exact G1|].
  destruct (_ <? 5).
  - eapply mem_grows_trans; [exact G1 | apply wbytes_grows].
  - eapply mem_grows_trans; [exact G1|].
    repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
Qed.

Lemma grows_mF : forall idx n stride start off m, mem_grows m (mF idx n stride start off m).
Proof. intros. apply wbytes_grows. Qed.
