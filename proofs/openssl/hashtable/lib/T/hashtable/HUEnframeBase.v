(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  ListFacts PropExec CatExec CatSim SeqExec StreamExec StreamSim MmapSim StepTac Hoare WalkTac StoreOk
  Frame RefMemcpyLib AgentLib MallocDefs.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import RefEnframeArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition SCT : Z := 0x72234.

(* [comment removed for export] *)
Definition sc_entry (sc : Z) : list byte :=
  match rdn RSEGS (fun _ => None) (Z_to_bv 64 (SCT + 2 * sc)) 2 with Some bs => bs | None => [] end.

Lemma sc_table_check :
  zall (N.to_nat 48%N)
    (fun sc => match rdn RSEGS (fun _ => None) (Z_to_bv 64 (SCT + 2 * sc)) 2 with
               | Some bs => (bytes_le_to_Z bs =? size_class sc)%Z
               | None => false end) 0 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sc_entry_rom : forall sc, (0 <= sc < 48)%Z ->
  rdn RSEGS (fun _ => None) (Z_to_bv 64 (SCT + 2 * sc)) 2 = Some (sc_entry sc)
  /\ bytes_le_to_Z (sc_entry sc) = size_class sc.
Proof.
  intros sc Hsc. pose proof (zallN_spec _ _ sc_table_check sc ltac:(cbn; lia)) as E.
  cbv beta in E. unfold sc_entry.
  destruct (rdn RSEGS (fun _ => None) (Z_to_bv 64 (SCT + 2 * sc)) 2) as [bs|]; [|discriminate].
  split; [reflexivity | apply Z.eqb_eq; exact E].
Qed.

(* [comment removed for export] *)
Definition sc_tbl_clear (m : word -> option byte) : Prop :=
  forall j, (0 <= j < 96)%Z -> m (Z_to_bv 64 (SCT + j)) = None.

Lemma sc_tbl_read : forall m sc, sc_tbl_clear m -> (0 <= sc < 48)%Z ->
  rdn RSEGS m (Z_to_bv 64 (SCT + 2 * sc)) 2 = Some (sc_entry sc).
Proof.
  intros m sc Hc Hsc. destruct (sc_entry_rom sc Hsc) as [R _].
  rewrite (rdn_ext RSEGS 2 m (fun _ => None)); [exact R | unfold SCT; rewrite u64_lit by lia; cbn; lia |].
  intros x Hx. unfold SCT in *. rewrite u64_lit in Hx by lia. cbn in Hx.
  replace x with (Z_to_bv 64 (467508 + (bv_unsigned x - 467508))) by (apply bv_eq; rewrite u64_lit by lia; lia).
  apply Hc. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac solve_kcs :=
  repeat (apply keeps_cs_upd; [| not_kept]); first [apply keeps_cs_refl | assumption].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record efH (mem : word -> option byte) (c : word)
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
  RM      : rdn RSEGS mem (Z_to_bv 64 (g + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 M));
  RW      : rdn RSEGS mem (Z_to_bv 64 (g + 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 W));
  R4      : mem (Z_to_bv 64 (start - 4)) = Some (Z_to_bv 8 0);
  R3      : mem (Z_to_bv 64 (start - 3)) = Some (Z_to_bv 8 h3);
  R2      : h3 <> 0 ->
            rdn RSEGS mem (Z_to_bv 64 (start - 2)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 o16));
  OK      : store_ok RSEGS mem (Z_to_bv 64 (start - 3)) (Z.to_nat (stride - 1)) = true;
  TBL     : sc_tbl_clear mem }.

(* [comment removed for export] *)
Record enframe_post (mem' : word -> option byte) (idx n stride start off : Z) : Prop := EPOST {
  P_p := start + 16 * off;
  P_e := start + stride - 4;
  P_r := stride - 4 - n - 16 * off;
  P_q := stride * idx / 16 + off;
  Pm4   : mem' (Z_to_bv 64 (P_p - 4)) = Some (Z_to_bv 8 0);
  Pm3   : mem' (Z_to_bv 64 (P_p - 3)) = Some (Z_to_bv 8 (idx + 32 * res_code P_r));
  Pm2   : rdn RSEGS mem' (Z_to_bv 64 (P_p - 2)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 P_q));
  Pzr   : 0 < P_r -> mem' (Z_to_bv 64 (P_p + n)) = Some (Z_to_bv 8 0);
  Pe5   : 5 <= P_r -> mem' (Z_to_bv 64 (P_e - 5)) = Some (Z_to_bv 8 0);
  Pe4   : 5 <= P_r -> rdn RSEGS mem' (Z_to_bv 64 (P_e - 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 P_r));
  Ps3   : off <> 0 -> mem' (Z_to_bv 64 (start - 3)) = Some (Z_to_bv 8 224);
  Ps2   : off <> 0 -> rdn RSEGS mem' (Z_to_bv 64 (start - 2)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 off));
  Pr    : 0 <= P_r /\ 0 <= off <= 255 /\ 0 <= P_q < 65536 }.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Facts.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac greg :=
  repeat match goal with
         | Hr : getr ?rs ?k = ?v |- context [getr ?rs ?k] => rewrite Hr
         end.

(* [comment removed for export] *)
Ltac stb F D aa bb vtac oktac :=
  chain_step;
  [ reflexivity
  | eapply MmapSim.step_sb_at with (a := aa) (b := bb);
    [ exact F | reflexivity | exact D
    | gres; greg; imm_norm; rewrite ?v_addi_0; rewrite ?v_addi_lit by lia; first [ reflexivity | f_equal; lia ]
    | gres; greg; reflexivity | vtac | oktac ]
  | step_simpl ].

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Ltac ldbu F D rtac :=
  chain_step;
  [ reflexivity
  | eapply step_lbu; [exact F | reflexivity | exact D
    | gres; greg; imm_norm; rewrite ?v_addi_0; rewrite ?v_addi_lit by lia; rtac ]
  | step_simpl; vnorm ].

(* [comment removed for export] *)
Ltac ldhu F D vv rtac btac :=
  chain_step;
  [ reflexivity
  | eapply step_lhu with (v := vv); [exact F | reflexivity | exact D
    | gres; greg; imm_norm; rewrite ?v_addi_0; rewrite ?v_addi_lit by lia; rtac | btac ]
  | step_simpl; vnorm ].

(* [comment removed for export] *)
Ltac ldd F D vv rtac :=
  chain_step;
  [ reflexivity
  | eapply step_ld with (v := vv); [exact F | reflexivity | exact D
    | gres; greg; imm_norm; rewrite ?v_addi_0; rewrite ?v_addi_lit by lia; rtac
    | apply bytes_le_to_Z_8 ]
  | step_simpl; vnorm ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn1_of_mem : forall segs m (a : word) b, m a = Some b -> rdn segs m a 1 = Some [b].
Proof. intros segs m a b Hm. cbn [rdn]. rewrite Hm. reflexivity. Qed.

Lemma wbytes_hit1 : forall m (a : word) b, wbytes m a [b] a = Some b.
Proof. intros m a b. cbn [wbytes]. rewrite bv_eqb_refl. reflexivity. Qed.

(* [comment removed for export] *)
Lemma wbytes_miss1 : forall m (a x : word) b, x <> a -> wbytes m a [b] x = m x.
Proof.
  intros m a x b Hx. cbn [wbytes].
  destruct (bv_eqb x a) eqn:E; [|reflexivity].
  exfalso. apply Hx. apply bv_eqb_eq in E. exact E.
Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma bytes_le_wle2 : forall z, (0 <= z < 65536)%Z ->
  bytes_le_to_Z (word_to_le_bytes 2 (Z_to_bv 64 z)) = bv_unsigned (Z_to_bv 64 z).
Proof.
  intros z Hz. rewrite bytes_le_N. rewrite u64_lit by lia.
  change (2 ^ (8 * Z.of_nat 2))%Z with 65536%Z. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma sb_byte : forall z, (0 <= z < 2 ^ 64)%Z ->
  Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z)) = Z_to_bv 8 (z mod 256).
Proof.
  intros z Hz. rewrite u64_lit by lia. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8)%Z with 256%Z. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma sb_byte_small : forall z, (0 <= z < 256)%Z ->
  Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z)) = Z_to_bv 8 z.
Proof. intros z Hz. rewrite sb_byte by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma wle2_eq : forall (v : word) z, bv_unsigned v = z ->
  word_to_le_bytes 2 v = word_to_le_bytes 2 (Z_to_bv 64 z).
Proof. intros v z <-. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition memT := word -> option byte.

(* [comment removed for export] *)
Definition mD (start off : Z) (m : memT) : memT :=
  if off =? 0 then m else
  wbytes (wbytes (wbytes m (Z_to_bv 64 (start - 3)) [Z_to_bv 8 224])
                 (Z_to_bv 64 (start - 2)) (word_to_le_bytes 2 (Z_to_bv 64 off)))
         (Z_to_bv 64 (start + 16 * off - 4)) [Z_to_bv 8 0].

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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
