(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep Image SFW1_lemmas.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlLex YajlFactsLex YajlFactsDecode.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AYajlRep AYajl_iface AY_rz AY_lex_rdck.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition AY_CHARTAB : Z := 0x215e0.
Definition AY_JT_LEX : Z := 0x213d0.
Definition A_RUE : Z := 0x21560.
Definition A_ALSE : Z := 0x21580.
Definition A_ULL : Z := 0x215a0.
Definition J_EOF : Z := 0x857fc.
Definition J_TOK : Z := 0x85418.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lxcells (e LB AF : Z) : list cell :=
  [C4 (wz 0); C4 (wz 0); C4 (wz e); C4 (wz 0); C8 (wz LB); C4 (wz 0); C4 (wz 0); C4 (wz 1); C4 (wz 1); C8 (wz AF)].

Lemma lxcells_of_lexer : forall lx LB AF,
  lex_inv lx -> lexer_cells lx LB AF = lxcells (lex_error_code (lx_error lx)) LB AF.
Proof. aceil.
  intros lx LB AF (IU & IO & IL & ICH & IA & IV & IB). unfold lexer_cells, lxcells.
  rewrite IU, IO, IL, ICH, IA, IV. reflexivity.
Qed.

Lemma lex_error_code_range : forall e, 0 <= lex_error_code e <= 11.
Proof. aceil. intros []; cbn; lia. Qed.
Lemma tok_code_range : forall t, 0 <= tok_code t <= 14.
Proof. aceil. intros []; cbn; lia. Qed.

Definition err_upd (e : Z) (r : option lex_error) : Z :=
  match r with Some e' => lex_error_code e' | None => e end.
Lemma err_upd_set_error_opt : forall lx r,
  lex_error_code (lx_error (lx_set_error_opt lx r)) = err_upd (lex_error_code (lx_error lx)) r.
Proof. aceil. intros lx [e|]; reflexivity. Qed.

(* [comment removed for export] *)
End RC__1.
Notation ASB := 2147450880%Z (only parsing).
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition alex_frame (k0 : list byte) (k8 k16 k24 k64 : word) (OBP OLP T L : Z) (start : Z)
           (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [CB 8 k0; C8 k8; C8 k16; C8 k24; C8 (wz (OLP / 8 + ASB)); C8 (wz (OBP / 8 + ASB)); C8 (wz OBP); C8 (wz OLP);
   C8 k64; C8 (wz L); C8 (wz start); C8 (wz T); C8 (wz ((L + 28) / 8 + ASB));
   C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition lexW (SP lo H L LB : Z) : list (Z * Z) :=
  [(lo, SP); (H + 32, H + 36); (L, L + 48); (LB + 8, LB + 12)].

(* [comment removed for export] *)
Record lexenvA (SP lo T len H L LB OT OTn : Z) : Prop := mkLE {
  le_ceil : alloc_ceiling <= lo;   (* [comment removed for export] *)
  le_lo : lo <= SP - 8528;   (* [comment removed for export] *)
  le_sp : SP <= 2^47;
  le_H : 17594333495296 <= H /\ H + 104 <= alloc_ceiling /\ H mod 16 = 0;
  le_L : 17594333495296 <= L /\ L + 48 <= alloc_ceiling /\ L mod 16 = 0;
  le_LB : 17594333495296 <= LB /\ LB + 32 <= alloc_ceiling /\ LB mod 16 = 0;
  le_HL : H + 104 <= L \/ L + 48 <= H;
  le_HLB : H + 104 <= LB \/ LB + 32 <= H;
  le_LLB : L + 48 <= LB \/ LB + 32 <= L;
  le_len : 0 <= len < 2^26;
  le_T : 0 < T /\ T + len < 2^62;
  le_Tsep : 0 < len -> (6303744 <= T /\ (T + len <= 2147446784 \/ 17594333495296 <= T)) /\ T + len <= alloc_ceiling /\ (H + 104 <= T \/ T + len <= H)
                       /\ (L + 48 <= T \/ T + len <= L) /\ (LB + 32 <= T \/ T + len <= LB);
  le_OT : 0 < len -> OT mod 8 = 0 /\ OT <= T /\ T + len <= OT + OTn /\ (6303744 <= OT /\ (OT + OTn <= 2147446784 \/ 17594333495296 <= OT)) /\ OT + OTn <= alloc_ceiling
}.
(* [comment removed for export] *)
Record lexenvT (lo T len H L LB OBP OLP : Z) : Prop := mkLT {
  le_OB : (6303744 <= OBP /\ (OBP + 40 <= 2147446784 \/ 17594333495296 <= OBP)) /\ OBP + 40 <= alloc_ceiling /\ OBP mod 32 = 0 /\ OLP = OBP + 32;
  le_OBsep : (H + 104 <= OBP \/ OBP + 40 <= H) /\ (L + 48 <= OBP \/ OBP + 40 <= L) /\ (LB + 32 <= OBP \/ OBP + 40 <= LB)
             /\ (0 < len -> T + len <= OBP \/ OBP + 40 <= T)
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma znth_nth_error : forall l i, 0 <= i < zlength l -> nth_error l (Z.to_nat i) = Some (znth l i).
Proof. aceil.
  intros l i Hi. unfold znth. destruct (Z.ltb_spec0 i 0); [lia|].
  destruct (nth_error l (Z.to_nat i)) as [c|] eqn:E.
  - rewrite (nth_error_nth _ _ _ E). reflexivity.
  - apply nth_error_None in E. unfold zlength in Hi. lia.
Qed.
Lemma text_byte_range : forall txt i, Forall (fun c => 0 <= c < 256) txt -> 0 <= znth txt i < 256.
Proof. aceil.
  intros txt i HF. unfold znth. destruct (Z.ltb_spec0 i 0); [lia|].
  destruct (Nat.lt_ge_cases (Z.to_nat i) (length txt)).
  - apply (proj1 (Forall_forall _ _) HF). apply nth_In. assumption.
  - rewrite nth_overflow by lia. lia.
Qed.
Lemma text_at_transport : forall W m m' T txt,
  text_at asegs m T txt -> munch W m m' ->
  (0 < zlength txt -> disjoint_from W T (zlength txt)) ->
  text_at asegs m' T txt.
Proof. aceil.
  intros W m m' T txt (TB & TF & T0 & TL) MU HD. split; [| auto].
  destruct (Z.eq_dec (zlength txt) 0) as [Z0|NZ].
  - destruct txt; [| unfold zlength in Z0; cbn in Z0; lia]. destruct TB as (B0 & B1 & _).
    split; [exact B0|]. split; [exact B1|]. intros i Hi. cbn in Hi. lia.
  - eapply bytes_at_transport; [exact TB| exact MU|]. rewrite zbytes_length.
    unfold zlength in *. apply HD. lia.
Qed.
Lemma text_read : forall W m m' T txt i,
  text_at asegs m T txt -> munch W m m' ->
  (0 < zlength txt -> disjoint_from W T (zlength txt)) ->
  0 <= i < zlength txt ->
  ov_read_bytes asegs m' (wa (T + i)) 1 = Some [Z_to_bv 8 (znth txt i)].
Proof. aceil.
  intros W m m' T txt i TX MU HD Hi.
  destruct (text_at_transport W m m' T txt TX MU HD) as (TB & _).
  eapply (u8ro_read asegs m' T (zbytes txt) i); [exact TB| | lia| reflexivity].
  unfold zbytes. rewrite nth_error_map, (znth_nth_error _ _ Hi). reflexivity.
Qed.
Lemma lexW_text : forall SP lo T len H L LB OT OTn, lexenvA SP lo T len H L LB OT OTn ->
  0 < len -> disjoint_from (lexW SP lo H L LB) T len.
Proof. aceil. intros until OTn. intros E Hl. destruct E. cbn. specialize (le_Tsep0 Hl). lia. Qed.

(* [comment removed for export] *)
Lemma chartab_bytes : forall m, mem_inv asegs m -> bytes_at asegs m AY_CHARTAB (zbytes char_lookup_table).
Proof. aceil.
  intros m MI. apply ro_bytes_at. { exact MI. } { unfold AY_CHARTAB. lia. }
  { rewrite zbytes_length. cbn [length char_lookup_table]. unfold AY_CHARTAB. lia. }
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
Lemma chartab_read : forall m c, mem_inv asegs m -> 0 <= c < 256 ->
  ov_read_bytes asegs m (wa (AY_CHARTAB + c)) 1 = Some [Z_to_bv 8 (clt c)].
Proof. aceil.
  intros m c MI Hc. unfold clt.
  eapply (u8ro_read asegs m AY_CHARTAB (zbytes char_lookup_table) c); [apply chartab_bytes; exact MI| | lia| reflexivity].
  unfold zbytes. rewrite nth_error_map, znth_nth_error; [reflexivity|]. unfold zlength. cbn [length char_lookup_table]. lia.
Qed.
Lemma clt_range8 : forall c, 0 <= clt c < 8.
Proof. aceil.
  intros c. destruct (Z.lt_ge_cases c 0) as [Hn|Hnn].
  { unfold clt, znth. destruct (Z.ltb_spec0 c 0); [lia| lia]. }
  destruct (Z.lt_ge_cases c 256) as [Hl|Hge].
  - pose proof (byte_forall (fun c => (0 <=? clt c) && (clt c <? 8)) ltac:(vm_compute; reflexivity) c ltac:(lia)) as H.
    cbn beta in H. apply andb_true_iff in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
  - unfold clt, znth. destruct (Z.ltb_spec0 c 0); [lia|]. rewrite nth_overflow; [lia|].
    cbn [length char_lookup_table]. lia.
Qed.

(* [comment removed for export] *)
Definition JT_LEX : list Z :=
  [40; 30; 6; 0; 40; 30; 6; 0; 40; 30; 6; 0; 40; 30; 6; 0; 40; 30; 6; 0; 252; 57; 6; 0; 252; 57; 6; 0; 252; 57; 6; 0;
   252; 57; 6; 0; 252; 57; 6; 0; 252; 57; 6; 0; 252; 57; 6; 0; 252; 57; 6; 0; 252; 57; 6; 0; 252; 57; 6; 0; 252; 57; 6; 0;
   252; 57; 6; 0; 252; 57; 6; 0; 252; 57; 6; 0; 252; 57; 6; 0; 252; 57; 6; 0; 252; 57; 6; 0; 252; 57; 6; 0; 40; 30; 6; 0;
   252; 57; 6; 0; 52; 44; 6; 0; 252; 57; 6; 0; 252; 57; 6; 0; 252; 57; 6; 0; 252; 57; 6; 0; 252; 57; 6; 0; 252; 57; 6; 0;
   252; 57; 6; 0; 252; 57; 6; 0; 252; 57; 6; 0; 44; 44; 6; 0; 96; 36; 6; 0; 252; 57; 6; 0; 72; 30; 6; 0; 96; 36; 6; 0;
   96; 36; 6; 0; 96; 36; 6; 0; 96; 36; 6; 0; 96; 36; 6; 0; 96; 36; 6; 0; 96; 36; 6; 0; 96; 36; 6; 0; 96; 36; 6; 0;
   96; 36; 6; 0; 104; 56; 6; 0].
Lemma jt_lex_bytes : forall m, mem_inv asegs m -> bytes_at asegs m AY_JT_LEX (zbytes JT_LEX).
Proof. aceil.
  intros m MI. apply ro_bytes_at. { exact MI. } { unfold AY_JT_LEX. lia. }
  { rewrite zbytes_length. cbn [length JT_LEX]. unfold AY_JT_LEX. lia. }
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
Lemma jt_lex_read_lit : forall m (c : Z) bs, mem_inv asegs m -> 9 <= c <= 58 ->
  firstn 4 (skipn (Z.to_nat (4 * (c - 9))) (zbytes JT_LEX)) = bs ->
  ov_read_bytes asegs m (wa (AY_JT_LEX + 4 * (c - 9))) 4 = Some bs.
Proof. aceil.
  intros m c bs MI Hc <-.
  pose proof (bytes_at_ov_read asegs m AY_JT_LEX (zbytes JT_LEX) (Z.to_nat (4 * (c - 9))) 4 (jt_lex_bytes m MI)) as R.
  rewrite Z2Nat.id in R by lia. apply R.
  rewrite zbytes_length. cbn [length JT_LEX]. lia.
Qed.
(* [comment removed for export] *)
Definition jt_ws_b : list byte := [Z_to_bv 8 40; Z_to_bv 8 30; Z_to_bv 8 6; Z_to_bv 8 0].
Definition jt_def_b : list byte := [Z_to_bv 8 252; Z_to_bv 8 57; Z_to_bv 8 6; Z_to_bv 8 0].
Definition jt_str_b : list byte := [Z_to_bv 8 52; Z_to_bv 8 44; Z_to_bv 8 6; Z_to_bv 8 0].
Definition jt_comma_b : list byte := [Z_to_bv 8 44; Z_to_bv 8 44; Z_to_bv 8 6; Z_to_bv 8 0].
Definition jt_num_b : list byte := [Z_to_bv 8 96; Z_to_bv 8 36; Z_to_bv 8 6; Z_to_bv 8 0].
Definition jt_cmt_b : list byte := [Z_to_bv 8 72; Z_to_bv 8 30; Z_to_bv 8 6; Z_to_bv 8 0].
Definition jt_colon_b : list byte := [Z_to_bv 8 104; Z_to_bv 8 56; Z_to_bv 8 6; Z_to_bv 8 0].
Lemma range_forall : forall (f : Z -> bool) lo n,
  forallb f (zseq lo n) = true -> forall c, lo <= c < lo + Z.of_nat n -> f c = true.
Proof. aceil. intros f lo n. exact (zseq_forallb f n lo). Qed.
Definition jt_class (c : Z) : list byte :=
  if is_lex_ws c then jt_ws_b
  else if c =? c_quote then jt_str_b
  else if c =? c_comma then jt_comma_b
  else if (c =? c_minus) || is_digit c then jt_num_b
  else if c =? c_slash then jt_cmt_b
  else if c =? c_colon then jt_colon_b
  else jt_def_b.
Lemma jt_class_table : forall c, 9 <= c <= 58 ->
  firstn 4 (skipn (Z.to_nat (4 * (c - 9))) (zbytes JT_LEX)) = jt_class c.
Proof. aceil.
  intros c Hc.
  pose proof (range_forall (fun c => if list_eq_dec (bv_eq_dec 8) (firstn 4 (skipn (Z.to_nat (4 * (c - 9))) (zbytes JT_LEX))) (jt_class c) then true else false)
                9 50 ltac:(vm_compute; reflexivity) c ltac:(lia)) as H.
  cbn beta in H. destruct (list_eq_dec _ _ _) as [E|NE]; [exact E| discriminate H].
Qed.
Lemma jt_lex_read : forall m c, mem_inv asegs m -> 9 <= c <= 58 ->
  ov_read_bytes asegs m (wa (AY_JT_LEX + 4 * (c - 9))) 4 = Some (jt_class c).
Proof. aceil. intros m c MI Hc. apply jt_lex_read_lit; [exact MI| exact Hc| apply jt_class_table; exact Hc]. Qed.

Lemma is_lex_ws_cases : forall c, is_lex_ws c = true -> (9 <= c <= 13) \/ c = 32.
Proof. aceil.
  intros c H. unfold is_lex_ws, c_tab, c_lf, c_vt, c_ff, c_cr, c_sp in H.
  repeat (apply orb_true_iff in H; destruct H as [H|H]); apply Z.eqb_eq in H; lia.
Qed.
Lemma minus_digit_cases : forall c, (c =? c_minus) || is_digit c = true -> c = 45 \/ 48 <= c <= 57.
Proof. aceil.
  intros c H. apply orb_true_iff in H. destruct H as [H|H].
  - apply Z.eqb_eq in H. unfold c_minus in H. lia.
  - unfold is_digit, c_0, c_9 in H. apply andb_true_iff in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Lemma jt_read_ws : forall m c, mem_inv asegs m -> is_lex_ws c = true ->
  ov_read_bytes asegs m (wa (AY_JT_LEX + 4 * (c - 9))) 4 = Some jt_ws_b.
Proof. aceil.
  intros m c MI H. pose proof (is_lex_ws_cases c H). rewrite jt_lex_read by (auto; lia). unfold jt_class. rewrite H. reflexivity.
Qed.
Lemma jt_read_lit : forall m c bs, mem_inv asegs m -> 9 <= c <= 58 -> jt_class c = bs ->
  ov_read_bytes asegs m (wa (AY_JT_LEX + 4 * (c - 9))) 4 = Some bs.
Proof. aceil. intros m c bs MI Hc <-. apply jt_lex_read; assumption. Qed.
Lemma jt_read_num : forall m c, mem_inv asegs m -> is_lex_ws c = false -> c <> 34 -> c <> 44 ->
  (c =? c_minus) || is_digit c = true ->
  ov_read_bytes asegs m (wa (AY_JT_LEX + 4 * (c - 9))) 4 = Some jt_num_b.
Proof. aceil.
  intros m c MI W Q CM H. pose proof (minus_digit_cases c H).
  rewrite jt_lex_read by (auto; lia). unfold jt_class. rewrite W, H.
  replace (c =? c_quote) with false by (symmetry; apply Z.eqb_neq; unfold c_quote; lia).
  replace (c =? c_comma) with false by (symmetry; apply Z.eqb_neq; unfold c_comma; lia). reflexivity.
Qed.
Lemma jt_read_def : forall m c, mem_inv asegs m -> 9 <= c <= 58 -> is_lex_ws c = false -> c <> 34 -> c <> 44 ->
  (c =? c_minus) || is_digit c = false -> c <> 47 -> c <> 58 ->
  ov_read_bytes asegs m (wa (AY_JT_LEX + 4 * (c - 9))) 4 = Some jt_def_b.
Proof. aceil.
  intros m c MI Hc W Q CM H SL CO.
  rewrite jt_lex_read by (auto; lia). unfold jt_class. rewrite W, H.
  replace (c =? c_quote) with false by (symmetry; apply Z.eqb_neq; unfold c_quote; lia).
  replace (c =? c_comma) with false by (symmetry; apply Z.eqb_neq; unfold c_comma; lia).
  replace (c =? c_slash) with false by (symmetry; apply Z.eqb_neq; unfold c_slash; lia).
  replace (c =? c_colon) with false by (symmetry; apply Z.eqb_neq; unfold c_colon; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rue_bytes : forall m, mem_inv asegs m -> bytes_at asegs m A_RUE (zbytes want_rue).
Proof. aceil.
  intros m MI. apply ro_bytes_at; [exact MI| unfold A_RUE; lia| rewrite zbytes_length; cbn; unfold A_RUE; lia|].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
Lemma alse_bytes : forall m, mem_inv asegs m -> bytes_at asegs m A_ALSE (zbytes want_alse).
Proof. aceil.
  intros m MI. apply ro_bytes_at; [exact MI| unfold A_ALSE; lia| rewrite zbytes_length; cbn; unfold A_ALSE; lia|].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
Lemma ull_bytes : forall m, mem_inv asegs m -> bytes_at asegs m A_ULL (zbytes want_ull).
Proof. aceil.
  intros m MI. apply ro_bytes_at; [exact MI| unfold A_ULL; lia| rewrite zbytes_length; cbn; unfold A_ULL; lia|].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma want_bytes_range : Forall (fun c => 0 <= c < 256) want_rue /\ Forall (fun c => 0 <= c < 256) want_alse
                         /\ Forall (fun c => 0 <= c < 256) want_ull.
Proof. aceil.
  unfold want_rue, want_alse, want_ull, c_r, c_u, c_e, c_a.
  repeat split; repeat (apply Forall_cons; [lia|]); apply Forall_nil.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma signed_small : forall c, 0 <= c < 2^63 -> bv_signed (Z_to_bv 64 c) = c.
Proof. aceil. intros c Hc. rewrite zb_signed. rewrite unsigned_lit by lia. destruct (Z.ltb_spec0 c (2^63)); lia. Qed.
Lemma u8_val : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. aceil. intros c Hc. apply (Z_to_bv_small 8). unfold bv_modulus. lia. Qed.
Lemma swrap32_small : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. aceil. intros z Hz. rewrite ybv_swrap32_eq. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma rw_cells_C8_CB : forall m A v cs, rw_cells asegs m A (C8 v :: cs) -> rw_cells asegs m A (CB 8 (le8 v) :: cs).
Proof. aceil.
  intros m A v cs [[WF BA] WR]. split; [split|].
  - cbn. split; [apply (length_le8 v)| exact (proj2 WF)].
  - exact BA.
  - exact WR.
Qed.

(* [comment removed for export] *)
Lemma sext8_lo : forall c, 0 <= c <= 127 -> Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl c 56))) 56 = c.
Proof. aceil.
  intros c Hc.
  pose proof (byte_forall (fun c => implb (c <=? 127) (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl c 56))) 56 =? c))
                ltac:(vm_compute; reflexivity) c ltac:(lia)) as X.
  cbn beta in X. replace (c <=? 127) with true in X by (symmetry; apply Z.leb_le; lia). cbn [implb] in X.
  apply Z.eqb_eq in X. exact X.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record alexK : Type := mkALK {
  k_P : acc -> Prop;
  k_sp : word; k_gp : word; k_tp : word; k_F : bvmap 5 word; k_fc : bv 32;
  k_lo : Z; k_T : Z; k_txt : list Z; k_H : Z; k_L : Z; k_LB : Z; k_OBP : Z; k_OLP : Z; k_OT : Z; k_OTn : Z;
  k_k16 : word; k_k24 : word;
  k_ra : word; k_s0 : word; k_s1 : word; k_s2 : word; k_s3 : word; k_s4 : word; k_s5 : word;
  k_s6 : word; k_s7 : word; k_s8 : word; k_s9 : word; k_s10 : word; k_s11 : word }.

Definition kSQ (K : alexK) : Z := bv_unsigned (k_sp K) - 208.
Definition kAF (K : alexK) : Z := k_H K + 72.
Definition kframe (K : alexK) (k0 : list byte) (k8 k64 : word) (start : Z) : list cell :=
  alex_frame k0 k8 (k_k16 K) (k_k24 K) k64 (k_OBP K) (k_OLP K) (k_T K) (k_L K) start
             (k_ra K) (k_s0 K) (k_s1 K) (k_s2 K) (k_s3 K) (k_s4 K) (k_s5 K) (k_s6 K) (k_s7 K) (k_s8 K) (k_s9 K) (k_s10 K) (k_s11 K).
Definition kW (K : alexK) : list (Z * Z) := lexW (bv_unsigned (k_sp K)) (k_lo K) (k_H K) (k_L K) (k_LB K).
Definition kenvA (K : alexK) : Prop :=
  lexenvA (bv_unsigned (k_sp K)) (k_lo K) (k_T K) (zlength (k_txt K)) (k_H K) (k_L K) (k_LB K) (k_OT K) (k_OTn K).
Definition kenvT (K : alexK) : Prop :=
  lexenvT (k_lo K) (k_T K) (zlength (k_txt K)) (k_H K) (k_L K) (k_LB K) (k_OBP K) (k_OLP K).

(* [comment removed for export] *)
Record kpolA (K : alexK) : Prop := mkKP {
  kp_stk : pol (k_P K) (k_lo K) (bv_unsigned (k_sp K));
  kp_img : pol (k_P K) AY_IMG_LO AY_IMG_HI;
  kp_imgsh : pol (k_P K) 0x7fffa000 0x800b8600;   (* [comment removed for export] *)
  kp_H : pol (k_P K) (k_H K) (k_H K + 104);
  kp_Hs : pol (k_P K) (ASB + k_H K / 8) (ASB + k_H K / 8 + 13);
  kp_L : pol (k_P K) (k_L K) (k_L K + 48);
  kp_Ls : pol (k_P K) (ASB + k_L K / 8) (ASB + k_L K / 8 + 6);
  kp_LB : pol (k_P K) (k_LB K) (k_LB K + 32);
  kp_LBs : pol (k_P K) (ASB + k_LB K / 8) (ASB + k_LB K / 8 + 4);
  kp_T : 0 < zlength (k_txt K) -> pol (k_P K) (k_T K) (k_T K + zlength (k_txt K));
  kp_Ts : 0 < zlength (k_txt K) -> pol (k_P K) (ASB + k_OT K / 8) (ASB + k_OT K / 8 + (k_OTn K + 7) / 8);
  kp_OB : pol (k_P K) (k_OBP K) (k_OBP K + 8);
  kp_OBs : pol (k_P K) (ASB + k_OBP K / 8) (ASB + k_OBP K / 8 + 1);
  kp_OL : pol (k_P K) (k_OLP K) (k_OLP K + 4);
  kp_OLs : pol (k_P K) (ASB + k_OLP K / 8) (ASB + k_OLP K / 8 + 1) }.

(* [comment removed for export] *)
Record alexsh (K : alexK) (m0 : mem) : Prop := mkSH {
  sh_H : u8arr asegs m0 (ASB + k_H K / 8) (blk_shadow 104);
  sh_L : u8arr asegs m0 (ASB + k_L K / 8) (blk_shadow 48);
  sh_LB : u8arr asegs m0 (ASB + k_LB K / 8) (blk_shadow 32);
  sh_T : 0 < zlength (k_txt K) -> u8arr asegs m0 (ASB + k_OT K / 8) (blk_shadow (k_OTn K));
  sh_C : u8arr asegs m0 (ASB + AY_CHARTAB / 8) (blk_shadow 256);
  sh_rue : u8arr asegs m0 (ASB + A_RUE / 8) (blk_shadow 4);
  sh_alse : u8arr asegs m0 (ASB + A_ALSE / 8) (blk_shadow 5);
  sh_ull : u8arr asegs m0 (ASB + A_ULL / 8) (blk_shadow 4);
  sh_OB : u8arr asegs m0 (ASB + k_OBP K / 8) (blk_shadow 8);
  sh_OL : u8arr asegs m0 (ASB + k_OLP K / 8) (blk_shadow 4);
  sh_stat : ay_statics m0;
  sh_txt : text_at asegs m0 (k_T K) (k_txt K) }.

(* [comment removed for export] *)
Definition alexmem (K : alexK) (m0 m : mem) (e off start : Z) (k0 : list byte) (k8 k64 : word) : Prop :=
  munch (kW K) m0 m /\ wmono asegs m0 m /\ mem_inv asegs m
  /\ stk asegs m (k_lo K) (kSQ K)
  /\ rw_cells asegs m (kSQ K) (kframe K k0 k8 k64 start)
  /\ rw_cells asegs m (k_H K + 32) [C4 (wz off)]
  /\ rw_cells asegs m (k_L K) (lxcells e (k_LB K) (kAF K))
  /\ rw_cells asegs m (k_LB K) (buf_cells ybuf_zero 0 (kAF K)).

(* [comment removed for export] *)
Definition J_HD : Z := 0x83100.
Definition alex_at (K : alexK) (m0 : mem) (pc : Z) (s7v : word) (e off start : Z) : machine_state -> Prop :=
  fun ms' => exists (rav s2v s3v s6v s10v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (k0 : list byte) (k8 k64 : word) (m' : mem),
    ms' = MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz (k_L K + 16)) a0 a1 a2 a3 a4 a5 a6 a7
                  s2v s3v (wz (k_L K + 24)) (wz (k_L K + 28)) s6v s7v (wz (zlength (k_txt K))) (wz ASB) s10v
                  (wz ((k_H K + 32) / 8 + ASB)) t3 t4 t5 t6)
             (k_F K) (wz pc) (k_fc K) None m' (seg_rom asegs)
    /\ alexmem K m0 m' e off start k0 k8 k64.
Definition J_CMT : Z := 0x83720.
Definition alex_hd (K : alexK) (m0 : mem) (pc : Z) (a0v : word) (e off start : Z) : machine_state -> Prop :=
  fun ms' => exists (rav s2v s3v s10v t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (k0 : list byte) (k8 : word) (m' : mem),
    ms' = MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz (k_L K + 16)) a0v a1 a2 a3 a4 a5 a6 a7
                  s2v s3v (wz (k_L K + 24)) (wz (k_L K + 28)) (wz (k_L K + 32)) (wz AY_JT_LEX) (wz (zlength (k_txt K))) (wz ASB) s10v
                  (wz ((k_H K + 32) / 8 + ASB)) t3 t4 t5 t6)
             (k_F K) (wz pc) (k_fc K) None m' (seg_rom asegs)
    /\ alexmem K m0 m' e off start k0 k8 (wz ((k_L K + 32) / 8 + ASB)).

(* [comment removed for export] *)
Definition sub_post (K : alexK) (m0 : mem) (e start : Z) (r : ytok * Z * option lex_error) : machine_state -> Prop :=
  let '(tok, o, err) := r in
  match tok with
  | TK_eof => fun ms' => exists s7v, alex_at K m0 J_EOF s7v (err_upd e err) o start ms'
  | _ => alex_at K m0 J_TOK (wz (tok_code tok)) (err_upd e err) o start
  end.
Definition tok_post (K : alexK) (m0 : mem) (tok : ytok) (e1 off1 start1 : Z) : machine_state -> Prop :=
  match tok with
  | TK_eof => fun ms' => exists s7v, alex_at K m0 J_EOF s7v e1 off1 start1 ms'
  | _ => alex_at K m0 J_TOK (wz (tok_code tok)) e1 off1 start1
  end.
Lemma sub_post_tok : forall K m0 e start tok o err ms,
  sub_post K m0 e start (tok, o, err) ms -> tok_post K m0 tok (err_upd e err) o start ms.
Proof. aceil. intros K m0 e start tok o err ms H. destruct tok; exact H. Qed.

(* [comment removed for export] *)
Record rdckF (K : alexK) (off : Z) : Prop := mkRF {
  rf1 : k_OT K mod 8 = 0; rf2 : 0 <= k_OT K; rf3 : k_OT K <= k_T K + off; rf4 : k_T K + off + 1 <= k_OT K + k_OTn K;
  rf5 : 0 <= 2147450880; rf6 : 2147450880 + (k_OT K + k_OTn K) / 8 + 1 < 2^64; rf7 : k_T K + off < 2^64 }.
Lemma rdck_facts : forall K off, kenvA K -> 0 <= off < zlength (k_txt K) -> rdckF K off.
Proof. aceil.
  intros K off ENV Hoff. destruct ENV. specialize (le_OT0 ltac:(lia)). specialize (le_Tsep0 ltac:(lia)).
  clear le_HL0 le_HLB0 le_LLB0. split; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Definition cmt_post (K : alexK) (m0 : mem) (e start : Z) (r : ytok * Z * option lex_error) : machine_state -> Prop :=
  let '(tok, o, err) := r in
  match tok with
  | TK_comment => fun ms' => exists a0v, alex_hd K m0 J_CMT a0v (err_upd e err) o start ms'
  | _ => sub_post K m0 e start r
  end.

(* [comment removed for export] *)
Definition lex_number_stmt (K : alexK) (m0 : mem) : Prop :=
  forall (rav s2v s3v s6v s7v s10v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k8 k64 : word) (k0 : list byte) (m : mem) (e off0 start : Z),
  alexmem K m0 m e (off0 + 1) start k0 k8 k64 -> 0 <= start <= off0 -> off0 < zlength (k_txt K) -> 0 <= e <= 11 ->
  evtA asegs (k_P K) (sub_post K m0 e start (ylex_number (k_txt K) (zlength (k_txt K)) off0))
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz (k_L K + 16)) a0 a1 a2 a3 a4 a5 a6 a7
          s2v s3v (wz (k_L K + 24)) (wz (k_L K + 28)) s6v s7v (wz (zlength (k_txt K))) (wz ASB) s10v
          (wz ((k_H K + 32) / 8 + ASB)) t3 t4 t5 t6)
        (k_F K) (wz 0x83830) (k_fc K) None m (seg_rom asegs)).
Definition lex_string_stmt (K : alexK) (m0 : mem) : Prop :=
  forall (rav s2v s3v s6v s7v s10v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k8 k64 : word) (k0 : list byte) (m : mem) (e off start : Z),
  alexmem K m0 m e off start k0 k8 k64 -> 0 <= start <= off -> off <= zlength (k_txt K) -> 0 <= e <= 11 ->
  evtA asegs (k_P K) (sub_post K m0 e start (ylex_string 1 (k_txt K) (zlength (k_txt K)) off))
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz (k_L K + 16)) a0 a1 a2 a3 a4 a5 a6 a7
          s2v s3v (wz (k_L K + 24)) (wz (k_L K + 28)) s6v s7v (wz (zlength (k_txt K))) (wz ASB) s10v
          (wz ((k_H K + 32) / 8 + ASB)) t3 t4 t5 t6)
        (k_F K) (wz 0x84004) (k_fc K) None m (seg_rom asegs)).
Definition lex_comment_stmt (K : alexK) (m0 : mem) : Prop :=
  forall (rav s2v s3v s10v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 k8 : word) (k0 : list byte) (m : mem) (e off start : Z),
  alexmem K m0 m e off start k0 k8 (wz ((k_L K + 32) / 8 + ASB)) -> 0 <= start <= off -> off <= zlength (k_txt K) -> 0 <= e <= 11 ->
  evtA asegs (k_P K) (cmt_post K m0 e start (ylex_comment (k_txt K) (zlength (k_txt K)) off))
    (MS (mkR rav (wz (kSQ K)) (k_gp K) (k_tp K) t0 t1 t2 (wz (k_H K + 32)) (wz (k_L K + 16)) a0 a1 a2 a3 a4 a5 a6 a7
          s2v s3v (wz (k_L K + 24)) (wz (k_L K + 28)) (wz (k_L K + 32)) (wz AY_JT_LEX) (wz (zlength (k_txt K))) (wz ASB) s10v
          (wz ((k_H K + 32) / 8 + ASB)) t3 t4 t5 t6)
        (k_F K) (wz 0x83218) (k_fc K) None m (seg_rom asegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Now.
Variable K : alexK.
Variables m0 m : mem.
Hypothesis ENV : kenvA K.
Hypothesis SH : alexsh K m0.
Hypothesis MU : munch (kW K) m0 m.
Hypothesis WM : wmono asegs m0 m.

Lemma kW_low : forall a n, 0 <= a -> a + n <= 17594333495296 -> disjoint_from (kW K) a n.
Proof. aceil. intros a n Ha Hn. destruct ENV. unfold kW, lexW. cbn. lia. Qed.

Lemma blk_shadow_len_nat : forall n, 0 <= n -> Z.of_nat (length (blk_shadow n)) = (n + 7) / 8.
Proof. aceil. intros; apply blk_shadow_length; assumption. Qed.

Lemma sh_disj : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 -> disjoint_from (kW K) (ASB + X / 8) ((n + 7) / 8).
Proof. aceil. intros X n H0 Hn HX. apply kW_low; Z.div_mod_to_equations; lia. Qed.

Ltac now_arr F n :=
  eapply (u8arr_transport asegs (kW K) m0 m); [exact F| exact MU| exact WM|];
  rewrite (blk_shadow_len_nat n) by lia; apply sh_disj; [destruct ENV; lia| lia| destruct ENV; lia].

Lemma shH_now : u8arr asegs m (ASB + k_H K / 8) (blk_shadow 104).
Proof. aceil. now_arr (sh_H K m0 SH) 104. Qed.
Lemma shL_now : u8arr asegs m (ASB + k_L K / 8) (blk_shadow 48).
Proof. aceil. now_arr (sh_L K m0 SH) 48. Qed.
Lemma shLB_now : u8arr asegs m (ASB + k_LB K / 8) (blk_shadow 32).
Proof. aceil. now_arr (sh_LB K m0 SH) 32. Qed.
Lemma shT_now : 0 < zlength (k_txt K) -> u8arr asegs m (ASB + k_OT K / 8) (blk_shadow (k_OTn K)).
Proof. aceil.
  intros Hl. eapply (u8arr_transport asegs (kW K) m0 m); [exact (sh_T K m0 SH Hl)| exact MU| exact WM|].
  destruct ENV. specialize (le_OT0 Hl). specialize (le_Tsep0 Hl). rewrite (blk_shadow_len_nat (k_OTn K)) by lia.
  apply sh_disj; lia.
Qed.
Lemma shC_now : u8arr asegs m (ASB + AY_CHARTAB / 8) (blk_shadow 256).
Proof. aceil. unfold AY_CHARTAB. now_arr (sh_C K m0 SH) 256. Qed.
Lemma shrue_now : u8arr asegs m (ASB + A_RUE / 8) (blk_shadow 4).
Proof. aceil. unfold A_RUE. now_arr (sh_rue K m0 SH) 4. Qed.
Lemma shalse_now : u8arr asegs m (ASB + A_ALSE / 8) (blk_shadow 5).
Proof. aceil. unfold A_ALSE. now_arr (sh_alse K m0 SH) 5. Qed.
Lemma shull_now : u8arr asegs m (ASB + A_ULL / 8) (blk_shadow 4).
Proof. aceil. unfold A_ULL. now_arr (sh_ull K m0 SH) 4. Qed.
Lemma shOB_now : kenvT K -> u8arr asegs m (ASB + k_OBP K / 8) (blk_shadow 8).
Proof. aceil.
  intros ET. eapply (u8arr_transport asegs (kW K) m0 m); [exact (sh_OB K m0 SH)| exact MU| exact WM|].
  rewrite (blk_shadow_len_nat 8) by lia; apply sh_disj; [destruct ET; lia| lia| destruct ENV; destruct ET; lia].
Qed.
Lemma shOL_now : kenvT K -> u8arr asegs m (ASB + k_OLP K / 8) (blk_shadow 4).
Proof. aceil.
  intros ET. eapply (u8arr_transport asegs (kW K) m0 m); [exact (sh_OL K m0 SH)| exact MU| exact WM|].
  rewrite (blk_shadow_len_nat 4) by lia; apply sh_disj; [destruct ET; lia| lia| destruct ENV; destruct ET; lia].
Qed.
Lemma stat_now : ay_statics m.
Proof. aceil.
  destruct (sh_stat K m0 SH) as (G1 & G2 & G3 & G4).
  unfold ay_statics, AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR in *.
  repeat split; (eapply (rw_cells_transport asegs (kW K) m0 m); [eassumption| exact MU| exact WM| apply kW_low; cbn; lia]).
Qed.
Lemma txt_now : text_at asegs m (k_T K) (k_txt K).
Proof. aceil.
  eapply text_at_transport; [exact (sh_txt K m0 SH)| exact MU|]. intros Hl. unfold kW. apply (lexW_text _ _ _ _ _ _ _ _ _ ENV Hl).
Qed.

(* [comment removed for export] *)
Lemma rd0_gen : forall A n a, u8arr asegs m (ASB + A / 8) (blk_shadow n) -> A mod 8 = 0 -> 0 <= A ->
  A <= a -> a < A + 8 * (n / 8) ->
  ov_read_bytes asegs m (Z_to_bv 64 (a / 8 + ASB)) 1 = Some [Z_to_bv 8 0].
Proof. aceil.
  intros A n a HU HA H0 H1 H2.
  replace (a / 8 + ASB) with (ASB + a / 8) by lia.
  apply (block_shadow_read0_u asegs m ASB A n a 1); [exact HA| Z.div_mod_to_equations; lia| exact HU| exact H1| lia| lia| Z.div_mod_to_equations; lia].
Qed.
Lemma rdk_gen : forall A n i bs, u8arr asegs m (ASB + A / 8) bs -> A mod 8 = 0 -> 0 <= A -> 0 <= i < 8 ->
  nth_error bs (Z.to_nat n) = Some (Z_to_bv 8 (znth (map bv_unsigned bs) n)) ->
  0 <= n ->
  ov_read_bytes asegs m (Z_to_bv 64 ((A + 8 * n + i) / 8 + ASB)) 1 = Some [Z_to_bv 8 (znth (map bv_unsigned bs) n)].
Proof. aceil.
  intros A n i bs HU HA H0 Hi Hn Hn0.
  eapply (u8arr_read asegs m (ASB + A / 8) bs n); [exact HU| exact Hn| exact Hn0|].
  unfold wa. f_equal. Z.div_mod_to_equations. lia.
Qed.
Lemma kH_facts : 17594333495296 <= k_H K /\ k_H K + 104 <= 2^47 /\ k_H K mod 8 = 0.
Proof. aceil. destruct ENV. split; [lia|]. split; [lia|]. Z.div_mod_to_equations. lia. Qed.
Lemma kL_facts : 17594333495296 <= k_L K /\ k_L K + 48 <= 2^47 /\ k_L K mod 8 = 0.
Proof. aceil. destruct ENV. split; [lia|]. split; [lia|]. Z.div_mod_to_equations. lia. Qed.
Lemma kLB_facts : 17594333495296 <= k_LB K /\ k_LB K + 32 <= 2^47 /\ k_LB K mod 8 = 0.
Proof. aceil. destruct ENV. split; [lia|]. split; [lia|]. Z.div_mod_to_equations. lia. Qed.
Lemma kOB_facts : kenvT K -> (6303744 <= k_OBP K /\ (k_OBP K + 40 <= 2147446784 \/ 17594333495296 <= k_OBP K)) /\ k_OBP K + 40 <= 2^47 /\ k_OBP K mod 32 = 0 /\ k_OLP K = k_OBP K + 32.
Proof. aceil. intros ET. destruct ENV. destruct ET. lia. Qed.

Lemma rd_shH : forall k, 0 <= k < 104 ->
  ov_read_bytes asegs m (Z_to_bv 64 ((k_H K + k) / 8 + ASB)) 1 = Some [Z_to_bv 8 0].
Proof. aceil. intros k Hk. pose proof kH_facts. apply (rd0_gen (k_H K) 104); [exact shH_now| lia| lia| lia| lia]. Qed.
Lemma rd_shL : forall k, 0 <= k < 48 ->
  ov_read_bytes asegs m (Z_to_bv 64 ((k_L K + k) / 8 + ASB)) 1 = Some [Z_to_bv 8 0].
Proof. aceil. intros k Hk. pose proof kL_facts. apply (rd0_gen (k_L K) 48); [exact shL_now| lia| lia| lia| lia]. Qed.
Lemma rd_shLB : forall k, 0 <= k < 32 ->
  ov_read_bytes asegs m (Z_to_bv 64 ((k_LB K + k) / 8 + ASB)) 1 = Some [Z_to_bv 8 0].
Proof. aceil. intros k Hk. pose proof kLB_facts. apply (rd0_gen (k_LB K) 32); [exact shLB_now| lia| lia| lia| lia]. Qed.
Lemma rd_shOB : kenvT K -> ov_read_bytes asegs m (Z_to_bv 64 (k_OBP K / 8 + ASB)) 1 = Some [Z_to_bv 8 0].
Proof. aceil. intros ET. pose proof (kOB_facts ET). apply (rd0_gen (k_OBP K) 8); [exact (shOB_now ET)| Z.div_mod_to_equations; lia| lia| lia| lia]. Qed.
Lemma rd_shOL : kenvT K -> ov_read_bytes asegs m (Z_to_bv 64 (k_OLP K / 8 + ASB)) 1 = Some [Z_to_bv 8 4].
Proof. aceil.
  intros ET. pose proof (kOB_facts ET). replace (k_OLP K / 8 + ASB) with ((k_OLP K + 8 * 0 + 0) / 8 + ASB) by (f_equal; f_equal; lia).
  apply (rdk_gen (k_OLP K) 0 0 (blk_shadow 4)); [exact (shOL_now ET)| Z.div_mod_to_equations; lia| lia| lia| reflexivity| lia].
Qed.
Lemma rd_shC : forall c, 0 <= c < 256 ->
  ov_read_bytes asegs m (Z_to_bv 64 ((AY_CHARTAB + c) / 8 + ASB)) 1 = Some [Z_to_bv 8 0].
Proof. aceil. intros c Hc. apply (rd0_gen AY_CHARTAB 256); [exact shC_now| reflexivity| unfold AY_CHARTAB; lia| lia| unfold AY_CHARTAB in *; lia]. Qed.
(* [comment removed for export] *)
Lemma rd_shrue : forall i, 0 <= i < 4 ->
  ov_read_bytes asegs m (Z_to_bv 64 ((A_RUE + i) / 8 + ASB)) 1 = Some [Z_to_bv 8 4].
Proof. aceil.
  intros i Hi. replace (A_RUE + i) with (A_RUE + 8 * 0 + i) by lia.
  apply (rdk_gen A_RUE 0 i (blk_shadow 4)); [exact shrue_now| reflexivity| unfold A_RUE; lia| lia| reflexivity| lia].
Qed.
Lemma rd_shalse : forall i, 0 <= i < 5 ->
  ov_read_bytes asegs m (Z_to_bv 64 ((A_ALSE + i) / 8 + ASB)) 1 = Some [Z_to_bv 8 5].
Proof. aceil.
  intros i Hi. replace (A_ALSE + i) with (A_ALSE + 8 * 0 + i) by lia.
  apply (rdk_gen A_ALSE 0 i (blk_shadow 5)); [exact shalse_now| reflexivity| unfold A_ALSE; lia| lia| reflexivity| lia].
Qed.
Lemma rd_shull : forall i, 0 <= i < 4 ->
  ov_read_bytes asegs m (Z_to_bv 64 ((A_ULL + i) / 8 + ASB)) 1 = Some [Z_to_bv 8 4].
Proof. aceil.
  intros i Hi. replace (A_ULL + i) with (A_ULL + 8 * 0 + i) by lia.
  apply (rdk_gen A_ULL 0 i (blk_shadow 4)); [exact shull_now| reflexivity| unfold A_ULL; lia| lia| reflexivity| lia].
Qed.
(* [comment removed for export] *)
Lemma rd_txt : forall i, 0 <= i < zlength (k_txt K) ->
  ov_read_bytes asegs m (wa (k_T K + i)) 1 = Some [Z_to_bv 8 (znth (k_txt K) i)].
Proof. aceil.
  intros i Hi. eapply (text_read (kW K) m0 m); [exact (sh_txt K m0 SH)| exact MU| | exact Hi].
  intros Hl. unfold kW. apply (lexW_text _ _ _ _ _ _ _ _ _ ENV Hl).
Qed.
Lemma txt_range : forall i, 0 <= znth (k_txt K) i < 256.
Proof. aceil. intros i. apply text_byte_range. exact (proj1 (proj2 (sh_txt K m0 SH))). Qed.
End Now.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End RC__2.
Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia; rewrite ?signed_small by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.

(* [comment removed for export] *)
Ltac clear_seps :=
  try match goal with H1 : (k_H _ + 104 <= k_L _ \/ _) |- _ => clear H1 end;
  try match goal with H2 : (k_H _ + 104 <= k_LB _ \/ _) |- _ => clear H2 end;
  try match goal with H3 : (k_L _ + 48 <= k_LB _ \/ _) |- _ => clear H3 end.
Ltac lex_prep ENV BC :=
  let E := fresh "ENV0" in pose proof ENV as E; destruct E;
  clear_seps;
  (* [comment removed for export] *)
  repeat match goal with H : 0 < zlength _ -> _ |- _ => clear H end;
  unfold kSQ, kAF, kW, lexW, kframe, alex_frame, lxcells, buf_cells in *; unfold wz in *;
  cbn [buf_state_code yb_state yb_len yb_used ybuf_zero] in BC.
Ltac seps ENV :=
  pose proof (le_HL _ _ _ _ _ _ _ _ _ ENV) as SEP1; pose proof (le_HLB _ _ _ _ _ _ _ _ _ ENV) as SEP2;
  pose proof (le_LLB _ _ _ _ _ _ _ _ _ ENV) as SEP3.
Ltac zstoreA ENV := seps ENV; zstepA; clear_seps.

(* [comment removed for export] *)
Tactic Notation "polu" constr(KP) constr(f) ident(H) := pose proof (f _ KP) as H; unfold pol, AY_IMG_LO, AY_IMG_HI in H.

(* [comment removed for export] *)
Ltac polby pat :=
  match goal with
  | H : forall a k, pat <= a -> _ |- _ => eapply H; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; solve [lia | zsimp; lia]
  end.
Ltac lexpolicy K :=
  lazymatch goal with
  | |- _ (Z_to_bv 64 ?E, _) =>
      match E with
      | context [bv_unsigned _] => polby (k_lo K)
      | context [2147450880] =>
          match E with
          | context [k_H K] => polby (2147450880 + k_H K / 8)
          | context [k_L K] => polby (2147450880 + k_L K / 8)
          | context [k_LB K] => polby (2147450880 + k_LB K / 8)
          | context [k_OT K] => polby (2147450880 + k_OT K / 8)
          | context [k_OBP K] => polby (2147450880 + k_OBP K / 8)
          | context [k_OLP K] => polby (2147450880 + k_OLP K / 8)
          | _ => polby 0x7fffa000
          end
      | context [k_H K] => polby (k_H K)
      | context [k_L K] => polby (k_L K)
      | context [k_LB K] => polby (k_LB K)
      | context [k_T K] => polby (k_T K)
      | context [k_OBP K] => polby (k_OBP K)
      | context [k_OLP K] => polby (k_OLP K)
      | _ => polby 65536
      end
  end.
Ltac policy1 ::=
  lazymatch goal with
  | |- ?P (?a, ?n) =>
      (lazymatch a with
       | Z_to_bv 64 _ => idtac
       | wa _ => apply policy_wa
       | wz ?X => change (wz X) with (Z_to_bv 64 X)
       | _ => apply policy_var
       end);
      first [ assumption
            | match goal with K : alexK |- _ => lexpolicy K end
            | LiaA.policy_pick   (* [comment removed for export] *)
            | match goal with
              | H : _ |- _ =>
                  lazymatch type of H with
                  | context [P (_, _)] => eapply H; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; solve [ eauto | lia | zsimp; lia ]
                  end
              end ]
  end.

(* [comment removed for export] *)
Ltac fin_lexmem :=
  unfold alexmem, kSQ, kAF, kW, lexW, kframe, alex_frame, lxcells, buf_cells;
  cbn [buf_state_code yb_state yb_len yb_used ybuf_zero];
  repeat match goal with |- _ /\ _ => split end; first [assumption| eassumption| apply rw_cells_C8_CB; eassumption].
Ltac fin_at :=
  lazymatch goal with |- evtA _ _ _ _ => apply evtA_done | _ => idtac end; cbv beta;
  lazymatch goal with |- ex _ => eexists | _ => idtac end;
  unfold alex_at; eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _;
  split; [reflexivity| fin_lexmem].
Ltac fin_hd :=
  lazymatch goal with |- evtA _ _ _ _ => apply evtA_done | _ => idtac end; cbv beta;
  unfold alex_hd; eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _;
  split; [reflexivity| fin_lexmem].

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac if_litc := let c := goal_cond in let v := eval vm_compute in c in
  lazymatch v with true => change c with true | false => change c with false end; cbv iota.
Ltac iflit := first [if_litc | if_false | if_true | idtac].

(* [comment removed for export] *)
Ltac shld RD := let H := fresh "RD" in pose proof RD as H; zstepA; clear H; rewrite ?zxb_small, ?sxb_small by lia.

(* [comment removed for export] *)
Ltac rdincA K m0 ENV SH MU WM off :=
  shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia));              (* [comment removed for export] *)
  zstepA; iflit;                                                 (* [comment removed for export] *)
  zstepA; rewrite ?ysx32_small by lia;                           (* [comment removed for export] *)
  zstepA; zstoreA ENV;                                           (* [comment removed for export] *)
  zstepA;                                                        (* [comment removed for export] *)
  zstepA; zstepA; rewrite (land_M32_small off) by lia;           (* [comment removed for export] *)
  zstepA.                                                        (* [comment removed for export] *)
Ltac rdckA K m0 ENV KPOL SH MU WM RDCK off :=
  let RF := fresh "RF" in
  pose proof (rdck_facts K off ENV ltac:(lia)) as RF;
  (eapply evtA_cut;
   [ eapply (RDCK (k_P K)); [ apply (shT_now K m0 _ ENV SH MU WM); lia | reflexivity
                            | exact (rf1 _ _ RF) | exact (rf2 _ _ RF) | exact (rf3 _ _ RF) | exact (rf4 _ _ RF)
                            | exact (rf5 _ _ RF) | exact (rf6 _ _ RF) | exact (rf7 _ _ RF)
                            | let X := fresh in pose proof KPOL as X; apply (kp_Ts _ X); lia ]
   | ]); clear RF;
  (let ms := fresh "ms" in let PO := fresh "PO" in let x := fresh "x" in let y := fresh "y" in
   intros ms PO; destruct PO as (x & y & PO); subst ms).
Ltac txtld K m0 ENV SH MU WM off :=
  (let RD := fresh "RD" in
   pose proof (rd_txt K m0 _ ENV SH MU off ltac:(lia)) as RD; zstepA; cbn beta; clear RD);
  rewrite (u8_val (znth _ off)) by (apply (txt_range K m0 SH));
  try (lazymatch goal with H : 0 <= znth _ off < 256 |- _ => idtac
       | |- _ => pose proof (txt_range K m0 SH off) end).
Ltac rdcharA0 K m0 ENV KPOL SH MU WM RDCK off :=
  zstepA;                                                       (* [comment removed for export] *)
  shld (rd_shL K m0 _ ENV SH MU WM 28 ltac:(lia));              (* [comment removed for export] *)
  zstepA; iflit;                                                 (* [comment removed for export] *)
  zstepA; rewrite ?ysx32_small by lia;                           (* [comment removed for export] *)
  zstepA; iflit;                                                 (* [comment removed for export] *)
  rdincA K m0 ENV SH MU WM off;
  rdckA K m0 ENV KPOL SH MU WM RDCK off.
Ltac rdcharA K m0 ENV KPOL SH MU WM RDCK off :=
  rdcharA0 K m0 ENV KPOL SH MU WM RDCK off; txtld K m0 ENV SH MU WM off.

(* [comment removed for export] *)
Ltac eofchkA K m0 ENV SH MU WM KK :=
  shld (rd_shH K m0 _ ENV SH MU WM 32 ltac:(lia)); zstepA; iflit;
  zstepA; rewrite ?ysx32_small by lia; zstepA; if_cases KK; zify_cond KK.
