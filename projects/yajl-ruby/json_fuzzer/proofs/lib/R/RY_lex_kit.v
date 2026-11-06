(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel SFW1_lemmas InitMem Arr Frame.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMalloc_iface RYajlRep RYajl_iface RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlLex YajlFactsLex YajlFactsDecode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition lxcells (e LB AF : Z) : list cell :=
  [C4 (wz 0); C4 (wz 0); C4 (wz e); C4 (wz 0); C8 (wz LB); C4 (wz 0); C4 (wz 0); C4 (wz 1); C4 (wz 1); C8 (wz AF)].

Lemma lxcells_of_lexer : forall lx LB AF,
  lex_inv lx -> lexer_cells lx LB AF = lxcells (lex_error_code (lx_error lx)) LB AF.
Proof.
  intros lx LB AF (IU & IO & IL & ICH & IA & IV & IB). unfold lexer_cells, lxcells.
  rewrite IU, IO, IL, ICH, IA, IV. reflexivity.
Qed.

Lemma lex_error_code_range : forall e, 0 <= lex_error_code e <= 11.
Proof. intros []; cbn; lia. Qed.

Lemma tok_code_range : forall t, 0 <= tok_code t <= 14.
Proof. intros []; cbn; lia. Qed.

(* [comment removed for export] *)
Definition err_upd (e : Z) (r : option lex_error) : Z :=
  match r with Some e' => lex_error_code e' | None => e end.

Lemma err_upd_set_error_opt : forall lx r,
  lex_error_code (lx_error (lx_set_error_opt lx r)) = err_upd (lex_error_code (lx_error lx)) r.
Proof. intros lx [e|]; reflexivity. Qed.

(* [comment removed for export] *)
Definition lex_frame (OBP OLP : Z) (junk : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [CB 8 junk; C8 (wz OBP); C8 (wz OLP); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition lexW (SP lo H L LB : Z) : list (Z * Z) :=
  [(lo, SP); (H + 32, H + 36); (L, L + 48); (LB + 8, LB + 12)].

(* [comment removed for export] *)
Record lexenv (SP lo T len H L LB : Z) : Prop := mkLE {
  le_ceil : alloc_ceiling <= lo;
  le_lo : lo <= SP - 8432;
  le_sp : SP < 2^64;
  le_H : 0 < H /\ H + 104 <= alloc_ceiling;
  le_L : 0 < L /\ L + 48 <= alloc_ceiling;
  le_LB : 0 < LB /\ LB + 32 <= alloc_ceiling;
  le_HL : H + 104 <= L \/ L + 48 <= H;
  le_HLB : H + 104 <= LB \/ LB + 32 <= H;
  le_LLB : L + 48 <= LB \/ LB + 32 <= L;
  le_len : 0 <= len < 2^26;
  le_T : 0 < T /\ T + len < 2^62;
  le_Tsep : 0 < len -> T + len <= alloc_ceiling /\ (H + 104 <= T \/ T + len <= H)
                       /\ (L + 48 <= T \/ T + len <= L) /\ (LB + 32 <= T \/ T + len <= LB)
}.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma znth_nth_error : forall l i, 0 <= i < zlength l -> nth_error l (Z.to_nat i) = Some (znth l i).
Proof.
  intros l i Hi. unfold znth. destruct (Z.ltb_spec0 i 0); [lia|].
  destruct (nth_error l (Z.to_nat i)) as [c|] eqn:E.
  - rewrite (nth_error_nth _ _ _ E). reflexivity.
  - apply nth_error_None in E. unfold zlength in Hi. lia.
Qed.

Lemma text_byte_range : forall txt i, Forall (fun c => 0 <= c < 256) txt -> 0 <= znth txt i < 256.
Proof.
  intros txt i HF. unfold znth. destruct (Z.ltb_spec0 i 0); [lia|].
  destruct (Nat.lt_ge_cases (Z.to_nat i) (length txt)).
  - apply (proj1 (Forall_forall _ _) HF). apply nth_In. assumption.
  - rewrite nth_overflow by lia. lia.
Qed.

Lemma text_at_transport : forall W m m' T txt,
  text_at rsegs m T txt -> munch W m m' ->
  (0 < zlength txt -> disjoint_from W T (zlength txt)) ->
  text_at rsegs m' T txt.
Proof.
  intros W m m' T txt (TB & TF & T0 & TL) MU HD. split; [| auto].
  destruct (Z.eq_dec (zlength txt) 0) as [Z0|NZ].
  - destruct txt; [| unfold zlength in Z0; cbn in Z0; lia]. destruct TB as (B0 & B1 & _).
    split; [exact B0|]. split; [exact B1|]. intros i Hi. cbn in Hi. lia.
  - eapply bytes_at_transport; [exact TB| exact MU|]. rewrite zbytes_length.
    unfold zlength in *. apply HD. lia.
Qed.

Lemma text_read : forall W m m' T txt i,
  text_at rsegs m T txt -> munch W m m' ->
  (0 < zlength txt -> disjoint_from W T (zlength txt)) ->
  0 <= i < zlength txt ->
  ov_read_bytes rsegs m' (wa (T + i)) 1 = Some [Z_to_bv 8 (znth txt i)].
Proof.
  intros W m m' T txt i TX MU HD Hi.
  destruct (text_at_transport W m m' T txt TX MU HD) as (TB & _).
  eapply (u8ro_read rsegs m' T (zbytes txt) i); [exact TB| | lia| reflexivity].
  unfold zbytes. rewrite nth_error_map, (znth_nth_error _ _ Hi). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lexW_text : forall SP lo T len H L LB, lexenv SP lo T len H L LB ->
  0 < len -> disjoint_from (lexW SP lo H L LB) T len.
Proof.
  intros SP lo T len H L LB E Hl. destruct E. cbn. specialize (le_Tsep0 Hl). lia.
Qed.

(* [comment removed for export] *)
Lemma chartab_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m RY_CHARTAB (zbytes char_lookup_table).
Proof.
  intros m MI. apply ro_bytes_at. { exact MI. } { unfold RY_CHARTAB. lia. }
  { rewrite zbytes_length. cbn [length char_lookup_table]. unfold RY_CHARTAB. lia. }
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma chartab_read : forall m c, mem_inv rsegs m -> 0 <= c < 256 ->
  ov_read_bytes rsegs m (wa (RY_CHARTAB + c)) 1 = Some [Z_to_bv 8 (clt c)].
Proof.
  intros m c MI Hc. unfold clt.
  eapply (u8ro_read rsegs m RY_CHARTAB (zbytes char_lookup_table) c); [apply chartab_bytes; exact MI| | lia| reflexivity].
  unfold zbytes. rewrite nth_error_map, znth_nth_error; [reflexivity|]. unfold zlength. cbn [length char_lookup_table]. lia.
Qed.

Lemma clt_range8 : forall c, 0 <= clt c < 8.
Proof.
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
  [160; 54; 0; 0; 160; 54; 0; 0; 160; 54; 0; 0; 160; 54; 0; 0; 160; 54; 0; 0; 216; 58; 0; 0; 216; 58; 0; 0; 216; 58; 0; 0;
   216; 58; 0; 0; 216; 58; 0; 0; 216; 58; 0; 0; 216; 58; 0; 0; 216; 58; 0; 0; 216; 58; 0; 0; 216; 58; 0; 0; 216; 58; 0; 0;
   216; 58; 0; 0; 216; 58; 0; 0; 216; 58; 0; 0; 216; 58; 0; 0; 216; 58; 0; 0; 216; 58; 0; 0; 216; 58; 0; 0; 160; 54; 0; 0;
   216; 58; 0; 0; 232; 59; 0; 0; 216; 58; 0; 0; 216; 58; 0; 0; 216; 58; 0; 0; 216; 58; 0; 0; 216; 58; 0; 0; 216; 58; 0; 0;
   216; 58; 0; 0; 216; 58; 0; 0; 216; 58; 0; 0; 224; 59; 0; 0; 160; 56; 0; 0; 216; 58; 0; 0; 176; 54; 0; 0; 160; 56; 0; 0;
   160; 56; 0; 0; 160; 56; 0; 0; 160; 56; 0; 0; 160; 56; 0; 0; 160; 56; 0; 0; 160; 56; 0; 0; 160; 56; 0; 0; 160; 56; 0; 0;
   160; 56; 0; 0; 96; 64; 0; 0].

Lemma jt_lex_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m RY_JT_LEX (zbytes JT_LEX).
Proof.
  intros m MI. apply ro_bytes_at. { exact MI. } { unfold RY_JT_LEX. lia. }
  { rewrite zbytes_length. cbn [length JT_LEX]. unfold RY_JT_LEX. lia. }
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma jt_lex_read_lit : forall m (c : Z) bs, mem_inv rsegs m -> 9 <= c <= 58 ->
  firstn 4 (skipn (Z.to_nat (4 * (c - 9))) (zbytes JT_LEX)) = bs ->
  ov_read_bytes rsegs m (wa (RY_JT_LEX + 4 * (c - 9))) 4 = Some bs.
Proof.
  intros m c bs MI Hc <-.
  pose proof (bytes_at_ov_read rsegs m RY_JT_LEX (zbytes JT_LEX) (Z.to_nat (4 * (c - 9))) 4 (jt_lex_bytes m MI)) as R.
  rewrite Z2Nat.id in R by lia. apply R.
  rewrite zbytes_length. cbn [length JT_LEX]. lia.
Qed.

(* [comment removed for export] *)
Definition jt_ws_b : list byte := [Z_to_bv 8 160; Z_to_bv 8 54; Z_to_bv 8 0; Z_to_bv 8 0].      (* [comment removed for export] *)
Definition jt_def_b : list byte := [Z_to_bv 8 216; Z_to_bv 8 58; Z_to_bv 8 0; Z_to_bv 8 0].     (* [comment removed for export] *)
Definition jt_str_b : list byte := [Z_to_bv 8 232; Z_to_bv 8 59; Z_to_bv 8 0; Z_to_bv 8 0].     (* [comment removed for export] *)
Definition jt_comma_b : list byte := [Z_to_bv 8 224; Z_to_bv 8 59; Z_to_bv 8 0; Z_to_bv 8 0].   (* [comment removed for export] *)
Definition jt_num_b : list byte := [Z_to_bv 8 160; Z_to_bv 8 56; Z_to_bv 8 0; Z_to_bv 8 0].     (* [comment removed for export] *)
Definition jt_cmt_b : list byte := [Z_to_bv 8 176; Z_to_bv 8 54; Z_to_bv 8 0; Z_to_bv 8 0].     (* [comment removed for export] *)
Definition jt_colon_b : list byte := [Z_to_bv 8 96; Z_to_bv 8 64; Z_to_bv 8 0; Z_to_bv 8 0].   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma range_forall : forall (f : Z -> bool) lo n,
  forallb f (zseq lo n) = true -> forall c, lo <= c < lo + Z.of_nat n -> f c = true.
Proof. intros f lo n. exact (zseq_forallb f n lo). Qed.

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
Proof.
  intros c Hc.
  pose proof (range_forall (fun c => if list_eq_dec (bv_eq_dec 8) (firstn 4 (skipn (Z.to_nat (4 * (c - 9))) (zbytes JT_LEX))) (jt_class c) then true else false)
                9 50 ltac:(vm_compute; reflexivity) c ltac:(lia)) as H.
  cbn beta in H. destruct (list_eq_dec _ _ _) as [E|NE]; [exact E| discriminate H].
Qed.

Lemma jt_lex_read : forall m c, mem_inv rsegs m -> 9 <= c <= 58 ->
  ov_read_bytes rsegs m (wa (RY_JT_LEX + 4 * (c - 9))) 4 = Some (jt_class c).
Proof. intros m c MI Hc. apply jt_lex_read_lit; [exact MI| exact Hc| apply jt_class_table; exact Hc]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma signed_small : forall c, 0 <= c < 2^63 -> bv_signed (Z_to_bv 64 c) = c.
Proof.
  intros c Hc. rewrite zb_signed. rewrite unsigned_lit by lia.
  destruct (Z.ltb_spec0 c (2^63)); lia.
Qed.

Lemma u8_val : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. intros c Hc. apply (Z_to_bv_small 8). unfold bv_modulus. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Record lexK : Type := mkLK {
  k_sp : word; k_gp : word; k_tp : word; k_F : bvmap 5 word; k_fc : bv 32;
  k_lo : Z; k_T : Z; k_txt : list Z; k_H : Z; k_L : Z; k_LB : Z; k_OBP : Z; k_OLP : Z;
  k_junk : list byte;
  k_ra : word; k_s0 : word; k_s1 : word; k_s2 : word; k_s3 : word; k_s4 : word; k_s5 : word;
  k_s6 : word; k_s7 : word; k_s8 : word; k_s9 : word; k_s10 : word; k_s11 : word }.

Definition kframe (K : lexK) : list cell :=
  lex_frame (k_OBP K) (k_OLP K) (k_junk K) (k_ra K) (k_s0 K) (k_s1 K) (k_s2 K) (k_s3 K) (k_s4 K) (k_s5 K)
            (k_s6 K) (k_s7 K) (k_s8 K) (k_s9 K) (k_s10 K) (k_s11 K).
Definition kW (K : lexK) : list (Z * Z) := lexW (bv_unsigned (k_sp K)) (k_lo K) (k_H K) (k_L K) (k_LB K).
Definition kenv (K : lexK) : Prop :=
  lexenv (bv_unsigned (k_sp K)) (k_lo K) (k_T K) (zlength (k_txt K)) (k_H K) (k_L K) (k_LB K).
Definition kSP (K : lexK) : Z := bv_unsigned (k_sp K) - 128.
Definition kAF (K : lexK) : Z := k_H K + 72.

(* [comment removed for export] *)
Definition lexmem (K : lexK) (m0 m : mem) (e off : Z) : Prop :=
  munch (kW K) m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m
  /\ stk rsegs m (k_lo K) (kSP K)
  /\ rw_cells rsegs m (kSP K) (kframe K)
  /\ rw_cells rsegs m (k_H K + 32) [C4 (wz off)]
  /\ rw_cells rsegs m (k_L K) (lxcells e (k_LB K) (kAF K))
  /\ rw_cells rsegs m (k_LB K) (buf_cells ybuf_zero 0 (kAF K)).

(* [comment removed for export] *)
Definition J_EOF : Z := 0x14dc0.
Definition J_TOK : Z := 0x14b5c.

Definition lex_at (K : lexK) (m0 : mem) (pc : Z) (s0v : word) (e off start : Z) : machine_state -> Prop :=
  fun ms' => exists (rav s1v s7v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7
                  (wz (k_L K)) (wz (k_T K)) (wz (k_H K + 32)) (wz (zlength (k_txt K))) (wz start) s7v s8v s9v s10v s11v t3 t4 t5 t6)
             (k_F K) (wz pc) (k_fc K) None m' (seg_rom rsegs)
    /\ lexmem K m0 m' e off.

(* [comment removed for export] *)
Definition sub_post (K : lexK) (m0 : mem) (e start : Z) (r : ytok * Z * option lex_error) : machine_state -> Prop :=
  let '(tok, o, err) := r in
  match tok with
  | TK_eof => fun ms' => exists s0v, lex_at K m0 J_EOF s0v (err_upd e err) o start ms'
  | _ => lex_at K m0 J_TOK (wz (tok_code tok)) (err_upd e err) o start
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End RC__1.
Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.

(* [comment removed for export] *)
Ltac lex_prep ENV BC :=
  destruct ENV;
  unfold kSP, kAF, kW, lexW, kframe, lex_frame, lxcells, buf_cells in *; unfold wz; unfold alloc_ceiling in *;
  cbn [buf_state_code yb_state yb_len yb_used ybuf_zero] in BC.

(* [comment removed for export] *)
Ltac fin_lexmem :=
  unfold lexmem, kSP, kAF, kW, lexW, kframe, lex_frame, lxcells, buf_cells;
  cbn [buf_state_code yb_state yb_len yb_used ybuf_zero];
  repeat match goal with |- _ /\ _ => split end; first [assumption| eassumption].
Ltac fin_at :=
  lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end; cbv beta;
  lazymatch goal with |- ex _ => eexists | _ => idtac end;
  unfold lex_at; eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _;
  split; [reflexivity| fin_lexmem].

(* [comment removed for export] *)
Ltac rdchar MU TX0 off :=
  zstep; rewrite ?ysx32_small by lia;
  zstep; (let K := fresh "KB" in if_cases K; zify_cond K; [ clear K | kill K ]);
  zstep; rewrite ?ysx32_small by lia;
  zstep; zstep; zstep; zstep; zstep;
  rewrite (land_M32_small off) by lia;
  zstep;
  (let RD := fresh "RD" in
   pose proof (text_read _ _ _ _ _ off TX0 MU ltac:(intros; cbn; lia) ltac:(lia)) as RD;
   zstep; cbn beta; clear RD);
  rewrite (u8_val (znth _ off)) by (apply text_byte_range; exact (proj1 (proj2 TX0)));
  try (lazymatch goal with H : 0 <= znth _ off < 256 |- _ => idtac
       | |- _ => pose proof (text_byte_range _ off (proj1 (proj2 TX0))) end).

(* [comment removed for export] *)
Ltac eofchk K := zstep; rewrite ?ysx32_small by lia; zstep; if_cases K; zify_cond K.

(* [comment removed for export] *)
Ltac unread :=
  zstep; rewrite ?ysx32_small by lia;
  zstep; (let K := fresh "KU" in if_cases K; zify_cond K; [ kill K | clear K ]);
  zstep; try rewrite ybv_swrap32_eq; zstep.

(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition A_RUE : Z := 0x105cd.
Definition A_ALSE : Z := 0x105f6.
Definition A_ULL : Z := 0x10679.
Lemma rue_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m A_RUE (zbytes want_rue).
Proof.
  intros m MI. apply ro_bytes_at. { exact MI. } { unfold A_RUE. lia. } { cbn. unfold A_RUE. lia. }
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
Lemma alse_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m A_ALSE (zbytes want_alse).
Proof.
  intros m MI. apply ro_bytes_at. { exact MI. } { unfold A_ALSE. lia. } { cbn. unfold A_ALSE. lia. }
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
Lemma ull_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m A_ULL (zbytes want_ull).
Proof.
  intros m MI. apply ro_bytes_at. { exact MI. } { unfold A_ULL. lia. } { cbn. unfold A_ULL. lia. }
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
Lemma want_bytes_range : Forall (fun c => 0 <= c < 256) want_rue /\ Forall (fun c => 0 <= c < 256) want_alse
                         /\ Forall (fun c => 0 <= c < 256) want_ull.
Proof.
  unfold want_rue, want_alse, want_ull, c_r, c_u, c_e, c_a.
  repeat split; repeat (apply Forall_cons; [lia|]); apply Forall_nil.
Qed.

(* [comment removed for export] *)
Definition lex_hd (K : lexK) (m0 : mem) (pc : Z) (e off start : Z) : machine_state -> Prop :=
  fun ms' => exists (rav s1v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR rav (wz (kSP K)) (k_gp K) (k_tp K) t0 t1 t2 (wz 10) s1v a0 a1 a2 a3 a4 a5 a6 a7
                  (wz (k_L K)) (wz (k_T K)) (wz (k_H K + 32)) (wz (zlength (k_txt K))) (wz start)
                  (wz 90) (wz 49) (wz 42) (wz 47) (wz RY_JT_LEX) t3 t4 t5 t6)
             (k_F K) (wz pc) (k_fc K) None m' (seg_rom rsegs)
    /\ lexmem K m0 m' e off.
Definition J_CMT : Z := 0x140bc.

End RC__2.
Ltac fin_hd :=
  lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end; cbv beta;
  unfold lex_hd; eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _;
  split; [reflexivity| fin_lexmem].

Section RC__3.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma swrap32_small : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z Hz. rewrite ybv_swrap32_eq. rewrite Z.mod_small; lia. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma buf_clear_null_walk : forall (B AF lo : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells rsegs m B (buf_cells ybuf_zero 0 AF) ->
  B <> 0 -> 0 < B ->
  stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> 0 <= lo -> B + 32 <= lo ->
  mem_inv rsegs m -> a0 = wz B ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(lo, bv_unsigned sp); (B + 8, B + 12)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp) /\ rw_cells rsegs m' B (buf_cells ybuf_zero 0 AF))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz RY_BUF_CLEAR) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros BC BNZ BP STK LO LO0 BL MI A0. subst a0.
  unfold buf_cells, RY_BUF_CLEAR, wz in *. cbn [buf_state_code yb_state yb_len yb_used ybuf_zero] in BC.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (munch_refl [(lo, bv_unsigned sp); (B + 8, B + 12)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. carve_frame 16%nat STK.
  zstep.
  zstep. if_cases K0; zify_cond K0. 1:{ kill K0. }
  zstep. rewrite ?ysx32_small by lia.
  zstep. if_cases K1; zify_cond K1. 1:{ kill K1. }
  zstep. zstep.
  zstep. if_cases K2; zify_cond K2. 2:{ kill K2. }
  zstep. zstep. zstep.
  release_frame FR STK (bv_unsigned sp).
  apply evt_done. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
  split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end; try assumption.
Qed.
End RC__3.
