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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlLex YajlDecode YajlParser YajlLeaf YajlFactsBuf YajlFactsLex YajlFactsParse YajlFactsLoop.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AYajlRep AYajl_iface AY_rz AY_hand.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition AY_JT_PSTATE : Z := 0x219f4.     (* [comment removed for export] *)
Definition AY_JT_PMAP : Z := 0x21a24.       (* [comment removed for export] *)
Definition AY_JT_PTOK : Z := 0x21a50.       (* [comment removed for export] *)
Definition AY_PHEAD : Z := 0x87540.        (* [comment removed for export] *)
Definition AY_PEXIT : Z := 0x89848.        (* [comment removed for export] *)
Definition AY_PABORT : Z := 0x89934.       (* [comment removed for export] *)
End RC__1.
Notation ASB := 2147450880%Z (only parsing).

(* [comment removed for export] *)
Ltac lk_nil := repeat match goal with H : _ = @nil _ |- _ => try rewrite H; clear H end; rewrite ?app_nil_r; reflexivity.
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma state_code_range : forall s, 0 <= state_code s < 12.
Proof. aceil. intros []; cbn; lia. Qed.
Lemma tok_code_range : forall t, 0 <= tok_code t < 15.
Proof. aceil. intros []; cbn; lia. Qed.

Definition state_targetA (s : ystate) : Z :=
  match s with
  | ST_start | ST_map_need_val | ST_array_start | ST_array_need_val => 0x8759c
  | ST_parse_complete => 0x89848
  | ST_parse_error | ST_lexical_error => 0x890a8
  | ST_map_start | ST_map_need_key => 0x87684
  | ST_map_sep => 0x878e8
  | ST_map_got_val => 0x87758
  | ST_array_got_val => 0x87820
  end.
Definition lex_state (s : ystate) : bool :=
  match s with ST_parse_complete | ST_parse_error | ST_lexical_error => false | _ => true end.

(* [comment removed for export] *)
Lemma stack_top_byte : forall s rest junk,
  nth_error (zbytes (stack_bytes (s :: rest)) ++ junk) (Z.to_nat (zlength rest)) = Some (Z_to_bv 8 (state_code s)).
Proof. aceil.
  intros s rest junk. rewrite stack_bytes_cons, zbytes_app. cbn [zbytes map].
  rewrite <- app_assoc. cbn [app]. rewrite nth_error_app2 by (rewrite zbytes_length, stack_bytes_length; unfold zlength; lia).
  rewrite zbytes_length, stack_bytes_length. unfold zlength. rewrite Nat2Z.id, Nat.sub_diag. reflexivity.
Qed.

Lemma u8_val : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. aceil. intros c Hc. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

(* [comment removed for export] *)
Definition JT_PSTATE : list Z :=
  [168; 91; 6; 0; 84; 126; 6; 0; 180; 118; 6; 0; 180; 118; 6; 0; 144; 92; 6; 0; 244; 94; 6; 0; 168; 91; 6; 0; 100; 93; 6; 0;
   144; 92; 6; 0; 168; 91; 6; 0; 44; 94; 6; 0; 168; 91; 6; 0].
Definition JT_PMAP : list Z :=
  [36; 126; 6; 0; 192; 92; 6; 0; 120; 96; 6; 0; 120; 96; 6; 0; 120; 96; 6; 0; 120; 96; 6; 0; 164; 95; 6; 0; 120; 96; 6; 0;
   120; 96; 6; 0; 228; 97; 6; 0; 8; 97; 6; 0].
Definition JT_PTOK : list Z :=
  [60; 102; 6; 0; 164; 91; 6; 0; 164; 91; 6; 0; 248; 125; 6; 0; 92; 105; 6; 0; 216; 101; 6; 0; 200; 102; 6; 0; 120; 101; 6; 0;
   136; 104; 6; 0; 164; 91; 6; 0; 4; 101; 6; 0; 144; 100; 6; 0; 200; 105; 6; 0; 60; 103; 6; 0].

Lemma jt_pstate_bytes : forall m, mem_inv asegs m -> bytes_at asegs m AY_JT_PSTATE (zbytes JT_PSTATE).
Proof. aceil.
  intros m MI. apply ro_bytes_at. { exact MI. } { unfold AY_JT_PSTATE. lia. }
  { rewrite zbytes_length. cbn [length JT_PSTATE]. unfold AY_JT_PSTATE. lia. }
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
Lemma jt_pmap_bytes : forall m, mem_inv asegs m -> bytes_at asegs m AY_JT_PMAP (zbytes JT_PMAP).
Proof. aceil.
  intros m MI. apply ro_bytes_at. { exact MI. } { unfold AY_JT_PMAP. lia. }
  { rewrite zbytes_length. cbn [length JT_PMAP]. unfold AY_JT_PMAP. lia. }
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
Lemma jt_ptok_bytes : forall m, mem_inv asegs m -> bytes_at asegs m AY_JT_PTOK (zbytes JT_PTOK).
Proof. aceil.
  intros m MI. apply ro_bytes_at. { exact MI. } { unfold AY_JT_PTOK. lia. }
  { rewrite zbytes_length. cbn [length JT_PTOK]. unfold AY_JT_PTOK. lia. }
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma jt_pstate_read : forall m i bs, mem_inv asegs m -> 0 <= i < 12 ->
  firstn 4 (skipn (Z.to_nat (4 * i)) (zbytes JT_PSTATE)) = bs ->
  ov_read_bytes asegs m (wa (AY_JT_PSTATE + 4 * i)) 4 = Some bs.
Proof. aceil.
  intros m i bs MI Hi <-.
  pose proof (bytes_at_ov_read asegs m AY_JT_PSTATE (zbytes JT_PSTATE) (Z.to_nat (4 * i)) 4 (jt_pstate_bytes m MI)) as R.
  rewrite Z2Nat.id in R by lia. apply R. rewrite zbytes_length. cbn [length JT_PSTATE]. lia.
Qed.
Lemma jt_pmap_read : forall m i bs, mem_inv asegs m -> 0 <= i < 11 ->
  firstn 4 (skipn (Z.to_nat (4 * i)) (zbytes JT_PMAP)) = bs ->
  ov_read_bytes asegs m (wa (AY_JT_PMAP + 4 * i)) 4 = Some bs.
Proof. aceil.
  intros m i bs MI Hi <-.
  pose proof (bytes_at_ov_read asegs m AY_JT_PMAP (zbytes JT_PMAP) (Z.to_nat (4 * i)) 4 (jt_pmap_bytes m MI)) as R.
  rewrite Z2Nat.id in R by lia. apply R. rewrite zbytes_length. cbn [length JT_PMAP]. lia.
Qed.
Lemma jt_ptok_read : forall m i bs, mem_inv asegs m -> 0 <= i < 14 ->
  firstn 4 (skipn (Z.to_nat (4 * i)) (zbytes JT_PTOK)) = bs ->
  ov_read_bytes asegs m (wa (AY_JT_PTOK + 4 * i)) 4 = Some bs.
Proof. aceil.
  intros m i bs MI Hi <-.
  pose proof (bytes_at_ov_read asegs m AY_JT_PTOK (zbytes JT_PTOK) (Z.to_nat (4 * i)) 4 (jt_ptok_bytes m MI)) as R.
  rewrite Z2Nat.id in R by lia. apply R. rewrite zbytes_length. cbn [length JT_PTOK]. lia.
Qed.
(* [comment removed for export] *)
Definition jtb (off : Z) : list byte :=
  [Z_to_bv 8 (off mod 256); Z_to_bv 8 ((off / 256) mod 256); Z_to_bv 8 ((off / 65536) mod 256); Z_to_bv 8 0].
Lemma byte_list_dec : forall l1 l2 : list byte,
  (if list_eq_dec (bv_eq_dec 8) l1 l2 then true else false) = true -> l1 = l2.
Proof. aceil. intros l1 l2 H. destruct (list_eq_dec _ l1 l2); [assumption| discriminate H]. Qed.
(* [comment removed for export] *)
Definition jt_pstate_off (s : ystate) : Z := state_targetA s - AY_JT_PSTATE.
Lemma jt_pstate_entry : forall s,
  firstn 4 (skipn (Z.to_nat (4 * state_code s)) (zbytes JT_PSTATE)) = jtb (jt_pstate_off s).
Proof. aceil. intros []; apply byte_list_dec; vm_compute; reflexivity. Qed.
Lemma jt_pstate_read_state : forall m s, mem_inv asegs m ->
  ov_read_bytes asegs m (wa (AY_JT_PSTATE + 4 * state_code s)) 4 = Some (jtb (jt_pstate_off s)).
Proof. aceil. intros m s MI. apply jt_pstate_read; [exact MI| apply state_code_range| apply jt_pstate_entry]. Qed.

(* [comment removed for export] *)
Definition jt_pstate_bs (s : ystate) : list byte :=
  match s with
  | ST_start => [Z_to_bv 8 168; Z_to_bv 8 91; Z_to_bv 8 6; Z_to_bv 8 0]
  | ST_parse_complete => [Z_to_bv 8 84; Z_to_bv 8 126; Z_to_bv 8 6; Z_to_bv 8 0]
  | ST_parse_error => [Z_to_bv 8 180; Z_to_bv 8 118; Z_to_bv 8 6; Z_to_bv 8 0]
  | ST_lexical_error => [Z_to_bv 8 180; Z_to_bv 8 118; Z_to_bv 8 6; Z_to_bv 8 0]
  | ST_map_start => [Z_to_bv 8 144; Z_to_bv 8 92; Z_to_bv 8 6; Z_to_bv 8 0]
  | ST_map_sep => [Z_to_bv 8 244; Z_to_bv 8 94; Z_to_bv 8 6; Z_to_bv 8 0]
  | ST_map_need_val => [Z_to_bv 8 168; Z_to_bv 8 91; Z_to_bv 8 6; Z_to_bv 8 0]
  | ST_map_got_val => [Z_to_bv 8 100; Z_to_bv 8 93; Z_to_bv 8 6; Z_to_bv 8 0]
  | ST_map_need_key => [Z_to_bv 8 144; Z_to_bv 8 92; Z_to_bv 8 6; Z_to_bv 8 0]
  | ST_array_start => [Z_to_bv 8 168; Z_to_bv 8 91; Z_to_bv 8 6; Z_to_bv 8 0]
  | ST_array_got_val => [Z_to_bv 8 44; Z_to_bv 8 94; Z_to_bv 8 6; Z_to_bv 8 0]
  | ST_array_need_val => [Z_to_bv 8 168; Z_to_bv 8 91; Z_to_bv 8 6; Z_to_bv 8 0]
  end.
Lemma jt_pstate_entry_bs : forall s,
  firstn 4 (skipn (Z.to_nat (4 * state_code s)) (zbytes JT_PSTATE)) = jt_pstate_bs s.
Proof. aceil. intros []; apply byte_list_dec; vm_compute; reflexivity. Qed.
Lemma jt_pstate_read_bs : forall m s, mem_inv asegs m ->
  ov_read_bytes asegs m (wa (AY_JT_PSTATE + 4 * state_code s)) 4 = Some (jt_pstate_bs s).
Proof. aceil. intros m s MI. apply jt_pstate_read; [exact MI| apply state_code_range| apply jt_pstate_entry_bs]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithY.
Variable Y : ay_params.
Record apE := mkPE {
  p_sp : word; p_gp : word; p_tp : word;                           (* [comment removed for export] *)
  p_ra : word; p_s0 : word; p_s1 : word; p_s2 : word; p_s3 : word; p_s4 : word; p_s5 : word;
  p_s6 : word; p_s7 : word; p_s8 : word; p_s9 : word; p_s10 : word; p_s11 : word; p_fs0 : word;   (* [comment removed for export] *)
  p_SQ : Z;                                                         (* [comment removed for export] *)
  p_ff : Z; p_fj1 : list byte; p_fj2 : list byte; p_fj3 : list byte; p_ffp : word;   (* [comment removed for export] *)
  p_lo : Z; p_T : Z; p_txt : list Z; p_OT : Z; p_OTn : Z; p_K : TSet;
  p_LF : list fblock;                                               (* [comment removed for export] *)
  p_REST : list ablock; p_mh : mhand; p_RR : Z;
  p_m0 : mem;                                                       (* [comment removed for export] *)
  p_st0 : y_APS Y; p_mo0 : Model                                    (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Notation pSP E := (bv_unsigned (p_sp E)) (only parsing).
Notation pH E := (mh_addr (p_mh E)) (only parsing).
Notation pCX E := (mh_ctx (p_mh E)) (only parsing).
Notation pLEN E := (zlength (p_txt E)) (only parsing).
Notation pAF E := (mh_addr (p_mh E) + 72) (only parsing).
Definition pLF (E : apE) : list fblock := (1, p_ff E) :: p_LF E.

(* [comment removed for export] *)
Record penvA (E : apE) : Prop := mkPA {
  pa_ceil : alloc_ceiling <= p_lo E;                  (* [comment removed for export] *)
  pa_lo : p_lo E <= pSP E - 8960;                       (* [comment removed for export] *)
  pa_sp : pSP E < 2^47 /\ pSP E mod 16 = 0;
  pa_SQ : p_SQ E mod 32 = 0 /\ pSP E - 368 <= p_SQ E <= pSP E - 352;
  pa_H : 17594333495296 <= pH E /\ pH E + 104 <= alloc_ceiling /\ pH E mod 16 = 0;
  pa_CX : 6303776 <= pCX E /\ pCX E + 8 <= alloc_ceiling /\ pCX E mod 32 = 0;
  pa_ff : 6303744 <= p_ff E /\ p_ff E + 128 <= alloc_ceiling /\ p_ff E mod 128 = 0;
  pa_ffCX : pCX E + 8 <= p_ff E \/ p_ff E + 128 <= pCX E - 32;
  pa_ffH : pH E + 104 <= p_ff E \/ p_ff E + 128 <= pH E;
  pa_CXH : pH E + 104 <= pCX E \/ pCX E + 8 <= pH E;
  pa_len : 0 <= pLEN E < 2^26;
  pa_T : 0 < p_T E /\ p_T E + pLEN E < 2^62 /\ p_T E + pLEN E <= 2^47;
  pa_OT : 0 < pLEN E -> p_OT E mod 8 = 0 /\ p_OT E <= p_T E /\ p_T E + pLEN E <= p_OT E + p_OTn E
                        /\ 6303744 <= p_OT E /\ p_OT E + p_OTn E <= alloc_ceiling;
  pa_Tsep : 0 < pLEN E -> (pH E + 104 <= p_T E \/ p_T E + pLEN E <= pH E) /\ (p_ff E + 128 <= p_T E \/ p_T E + pLEN E <= p_ff E)
                          /\ (pCX E + 8 <= p_T E \/ p_T E + pLEN E <= pCX E);
  pa_j : length (p_fj1 E) = 8%nat /\ length (p_fj2 E) = 24%nat /\ length (p_fj3 E) = 52%nat;
  (* [comment removed for export] *)
  pa_strhi : 17594333495296 <= mh_lexer (p_mh E) /\ 17594333495296 <= mb_addr (mh_lexbuf (p_mh E)) /\ 17594333495296 <= mb_addr (mh_decbuf (p_mh E));
  (* [comment removed for export] *)
  pa_CXP : pCX E - 32 + 128 <= 2147446784 \/ 17594333495296 <= pCX E - 32;
  pa_ffP : p_ff E + 128 <= 2147446784 \/ 17594333495296 <= p_ff E;
  pa_OTP : 0 < pLEN E -> p_OT E + p_OTn E <= 2147446784 \/ 17594333495296 <= p_OT E
}.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pframe (E : apE) (k0 : list byte) (k224 : list byte) : list cell :=
  [CB 24 k0; C8 (wz 3); C8 (wz 7); C8 (wz 9223372036854775809); C8 (wz (p_ff E)); C8 (wz ((pH E + 32) / 8 + 2147450880));
   C8 (wz 0x21d00); C8 (wz (p_ff E)); C8 (wz (pH E + 40)); C8 (wz ((pH E + 8) / 8 + 2147450880)); C8 (wz (pH E + 8));
   C8 (wz ((pH E + 24) / 8 + 2147450880)); C8 (wz (pH E + 24)); C8 (wz AY_JT_PTOK); C8 (wz (pH E / 8 + 2147450880)); C8 (wz (pH E));
   C8 (wz ((pH E + 56) / 8 + 2147450880)); C8 (wz (pH E + 56)); C8 (wz ((pH E + 16) / 8 + 2147450880)); C8 (wz (pH E + 16));
   C8 (wz (p_T E)); C8 (wz (pLEN E)); C8 (wz (pH E + 32)); C8 (wz (p_ff E + 32)); C8 (wz (p_ff E + 64));
   C8 (wz (pH E + 48)); CB 8 k224; C8 (wz (p_ff E))].
(* [comment removed for export] *)
Definition psaved (E : apE) : list cell :=
  [C8 (p_fs0 E); C8 (p_s11 E); C8 (p_s10 E); C8 (p_s9 E); C8 (p_s8 E); C8 (p_s7 E); C8 (p_s6 E); C8 (p_s5 E);
   C8 (p_s4 E); C8 (p_s3 E); C8 (p_s2 E); C8 (p_s1 E); C8 (p_s0 E); C8 (p_ra E)].
(* [comment removed for export] *)
Definition AFF_MAGIC : Z := 0x41b58ab3.
Definition AFF_DESCR : Z := 0x12404.
Definition pffA (E : apE) : list cell := [C8 (wz AFF_MAGIC); C8 (wz AFF_DESCR); C8 (wz AY_DO_PARSE); CB 8 (p_fj1 E)].
Definition pffZ (E : apE) : list cell := [CB 52 (p_fj3 E); C8 (p_ffp E)].
(* [comment removed for export] *)
Definition pffsh : list cell :=
  [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 0);
   C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 4);
   C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); CB 4 (repeat (Z_to_bv 8 0) 4)].
(* [comment removed for export] *)
Definition pff (E : apE) (m : mem) (obw olw : word) : Prop :=
  rw_cells asegs m (p_ff E) (pffA E) /\ rw_cells asegs m (p_ff E + 32) [C8 obw] /\ rw_cells asegs m (p_ff E + 40) [CB 24 (p_fj2 E)]
  /\ rw_cells asegs m (p_ff E + 64) [C4 olw] /\ rw_cells asegs m (p_ff E + 68) (pffZ E)
  /\ rw_cells asegs m (p_ff E / 8 + 2147450880) pffsh.

(* [comment removed for export] *)
Definition pstate (E : apE) (pc : Z) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v s4v s5v t3 t4 t5 t6 : word) : machine_state :=
  MS (mkR rav (wz (p_SQ E)) (p_gp E) (p_tp E) t0 t1 t2 (p_sp E) (wz (p_SQ E)) a0 a1 a2 a3 a4 a5 a6 a7
          s2v (wz 11) s4v s5v (wz (pH E + 60)) (wz ((pH E + 60) / 8 + 2147450880)) (wz 2147450880) (wz ((pH E + 48) / 8 + 2147450880))
          (wz AY_JT_PSTATE) (wz (p_ff E / 8 + 2147450880)) t3 t4 t5 t6)
     F (wz pc) fc None m (seg_rom asegs).

(* [comment removed for export] *)
Definition pok (E : apE) (h : yhandle) (cx : yctx) : Prop :=
  p_K E [] /\ loop_pre (pLEN E) h cx /\ 0 < h_used h /\ (h_stack_blk h <> None /\ h_stack_size h mod 8 = 0)
  /\ ((exists bt, In bt (p_REST E) /\ ab_addr bt <= p_T E /\ p_T E + pLEN E <= ab_addr bt + ab_size bt) \/ pLEN E = 0)
  /\ (pLEN E = 0 \/ (exists bt, In bt (p_REST E) /\ ab_addr bt <= p_OT E /\ p_OT E + p_OTn E <= ab_addr bt + ab_size bt))
  /\ (exists f, In f (p_LF E) /\ snd f + 32 = pCX E /\ fst f = 1)
  /\ (ff_live_class (p_LF E) 0 < 2)%nat
  /\ nbig (p_REST E) <= AY_NBIG_REST /\ 0 <= p_RR E /\ p_tp E = wz (c_tp ACONSTS)
  /\ p_ffp E = wz (y_aflag Y 1 (p_ff E)) /\ (forall f, In f (p_LF E) -> snd f + ff_bytes (fst f) <= p_ff E \/ p_ff E + 128 <= snd f).

#[local, warnings="-notation-for-abbreviation"] Notation AYSTY := (AYST Y).

(* [comment removed for export] *)
Definition pmem (E : apE) (m : mem) (mo : Model) (s : y_APS Y) (LK : list ablock) (h : yhandle) (mh : mhand) (cx : yctx)
    (obw olw : word) (cr : Z) : Prop :=
  AYSTY s (abl (yblocks mh h) ++ LK ++ p_REST E) (pLF E) m mo
  /\ ahand_rep m h mh /\ mh_same (p_mh E) mh /\ actx_rep m (pCX E) cx /\ atext_at m (p_T E) (p_txt E)
  /\ (exists k0 k224, rw_cells asegs m (p_SQ E) (pframe E k0 k224))
  /\ rw_cells asegs m (pSP E - 112) (psaved E)
  /\ pff E m obw olw
  /\ oshadow m (pCX E) 8
  /\ stk asegs m (p_lo E) (p_SQ E) /\ stk asegs m (p_SQ E + 240) (pSP E - 112) /\ mem_inv asegs m
  /\ ay_pres (p_REST E) (p_LF E) (pSP E) [(pCX E, pCX E + 8)] (p_m0 E) m
  /\ y_uanchor Y m (pSP E) (p_ra E) (p_s0 E)
  /\ (cr + p_RR E <= y_acredit Y s /\ 0 <= cr)
  /\ (y_SO Y s = y_SO Y (p_st0 E) /\ y_ayR Y (p_st0 E) (p_mo0 E) s mo)
  /\ h_stack_blk h <> None
  /\ LK = [].               (* [comment removed for export] *)

(* [comment removed for export] *)
Definition phead (E : apE) (F : bvmap 5 word) (fc : bv 32) (m : mem) (used : Z)
    (rav t0 t1 a1 a2 a3 a4 a5 a6 a7 s4v s5v t3 t4 t5 t6 : word) : machine_state :=
  pstate E AY_PHEAD F fc m rav t0 t1 (wz (pH E + 48)) (wz used) a1 a2 a3 a4 a5 a6 a7 (wz (pH E + 64)) s4v s5v t3 t4 t5 t6.

(* [comment removed for export] *)
Definition plk_ok (LK : list ablock) (h : yhandle) : Prop :=
  LK = [] \/ (length LK = 1%nat /\ exists st rest, h_stack h = st :: rest /\ lex_state st = false).
Lemma plk_ok_nil : forall h, plk_ok [] h.
Proof. aceil. intros h. left. reflexivity. Qed.
Lemma plk_ok_lex : forall LK h st rest, plk_ok LK h -> h_stack h = st :: rest -> lex_state st = true -> LK = [].
Proof. aceil. intros LK h st rest [E0|(_ & st' & rest' & HS & LS)] HST LT; [exact E0|]. rewrite HST in HS. injection HS as <- <-. congruence. Qed.
Lemma plk_ok_len : forall LK h, plk_ok LK h -> (length LK <= 1)%nat.
Proof. aceil. intros LK h [->|(L1 & _)]; [cbn; lia| lia]. Qed.

(* [comment removed for export] *)
Definition pcr (E : apE) (h : yhandle) (cr : Z) : Prop :=
  y_phi_hand Y h 0 <= cr /\ (forall st rest, h_stack h = st :: rest -> lex_state st = true -> y_phi_hand Y h (pLEN E) <= cr).

Lemma pcr_full : yacct_hand_mono_stmt Y -> forall E h cr, penvA E -> y_phi_hand Y h (pLEN E) <= cr -> pcr E h cr.
Proof. aceil.
  intros YHM E h cr PA HCR. split; [| intros; exact HCR].
  pose proof (YHM h (pLEN E) 0 ltac:(destruct PA; lia)) as M0. lia.
Qed.

(* [comment removed for export] *)
Definition phead_inv (E : apE) (fc : bv 32) (m : mem) (mo : Model) (s : y_APS Y) (LK : list ablock) (h : yhandle) (mh : mhand) (cx : yctx) : Prop :=
  (exists obw olw cr, pmem E m mo s LK h mh cx obw olw cr /\ pcr E h cr) /\ pok E h cx /\ frm0 fc /\ plk_ok LK h.

(* [comment removed for export] *)
Definition ppot (phr : Z -> Z -> Z -> Z -> Z) (E : apE) (h0 h : yhandle) (cr : Z) : Prop :=
  y_phi_buf Y (lx_buf (h_lexer h)) + y_phi_buf Y (h_decbuf h) + phr (h_bytesConsumed h0) (h_used h0) (h_stack_size h0) (pLEN E) <= cr.

(* [comment removed for export] *)
Definition pexit_cont (E : apE) (R : ystatus * yhandle * yctx -> Prop) : Prop :=
  forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32)
         (m' : mem) (mo' : Model) (s' : y_APS Y) (st : ystatus) (h' : yhandle) (cx' : yctx) (mh' : mhand) (LK : list ablock),
    R (st, h', cx') ->
    y_SO Y s' = y_SO Y (p_st0 E) -> y_ayR Y (p_st0 E) (p_mo0 E) s' mo' -> y_phi_hand Y h' 0 + p_RR E <= y_acredit Y s' ->
    a0' = wz (status_code st) ->
    mem_inv asegs m' -> stk asegs m' (p_lo E) (pSP E) -> frm0 fc' ->
    ay_pres (p_REST E) (p_LF E) (pSP E) [(pCX E, pCX E + 8)] (p_m0 E) m' ->
    ahand_rep m' h' mh' -> mh_same (p_mh E) mh' -> actx_rep m' (pCX E) cx' -> atext_at m' (p_T E) (p_txt E) ->
    (yb_data (lx_buf (h_lexer h')) <> None -> oshadow m' (mb_data (mh_lexbuf mh')) (yb_len (lx_buf (h_lexer h'))) /\ amem (mb_data (mh_lexbuf mh')) (yb_len (lx_buf (h_lexer h')))) ->
    (yb_data (h_decbuf h') <> None -> oshadow m' (mb_data (mh_decbuf mh')) (yb_len (h_decbuf h')) /\ amem (mb_data (mh_decbuf mh')) (yb_len (h_decbuf h'))) ->
    (h_stack_blk h' <> None -> oshadow m' (mh_stack mh') (h_stack_size h') /\ amem (mh_stack mh') (h_stack_size h')) ->
    AYSTY s' (abl (yblocks mh' h') ++ LK ++ p_REST E) (p_LF E) m' mo' -> (length LK <= 1)%nat -> LK = [] ->
    realizes_cfg acfg asegs (mkCfg (MS (mkR (p_ra E) (p_sp E) (p_gp E) (p_tp E) t0' t1' t2' (p_s0 E) (p_s1 E) a0' a1' a2' a3' a4' a5' a6' a7'
                                    (p_s2 E) (p_s3 E) (p_s4 E) (p_s5 E) (p_s6 E) (p_s7 E) (p_s8 E) (p_s9 E) (p_s10 E) (p_s11 E) t3' t4' t5' t6')
                            F' (ret_pc (p_ra E)) fc' None m' (seg_rom asegs)) mo') (p_K E).

(* [comment removed for export] *)
Definition ploop_at (E : apE) (fuel : nat) : Prop :=
  forall (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : y_APS Y) (LK : list ablock) (h : yhandle) (mh : mhand) (cx : yctx)
         (rav t0 t1 a1 a2 a3 a4 a5 a6 a7 s4v s5v t3 t4 t5 t6 : word),
    phead_inv E fc m mo s LK h mh cx -> (passes_left (pLEN E) h <= Z.of_nat fuel)%Z ->
    pexit_cont E (yleaf (yparse_loop jf_callbacks (p_txt E) (pLEN E) fuel h cx)) ->
    realizes_cfg acfg asegs (mkCfg (phead E F fc m (h_used h) rav t0 t1 a1 a2 a3 a4 a5 a6 a7 s4v s5v t3 t4 t5 t6) mo) (p_K E).
Definition ppass_stmt (E : apE) : Prop :=
  forall (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : y_APS Y) (LK : list ablock) (h : yhandle) (mh : mhand) (cx : yctx)
         (rav t0 t1 a1 a2 a3 a4 a5 a6 a7 s4v s5v t3 t4 t5 t6 : word),
    phead_inv E fc m mo s LK h mh cx ->
    pexit_cont E (fun r => let '(st, h', cx') := r in yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h cx) (SR_done st h' cx')) ->
    (forall (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : y_APS Y) (LK' : list ablock) (h' : yhandle) (mh' : mhand) (cx' : yctx)
            (rav' t0' t1' a1' a2' a3' a4' a5' a6' a7' s4v' s5v' t3' t4' t5' t6' : word),
       yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h cx) (SR_again h' cx') ->
       phead_inv E fc' m' mo' s' (LK' ++ LK) h' mh' cx' ->
       realizes_cfg acfg asegs (mkCfg (phead E F' fc' m' (h_used h') rav' t0' t1' a1' a2' a3' a4' a5' a6' a7' s4v' s5v' t3' t4' t5' t6') mo') (p_K E)) ->
    realizes_cfg acfg asegs (mkCfg (phead E F fc m (h_used h) rav t0 t1 a1 a2 a3 a4 a5 a6 a7 s4v s5v t3 t4 t5 t6) mo) (p_K E).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record pblk (E : apE) (mh : mhand) (h : yhandle) : Prop := mkPB {
  pb_H : mh_addr mh = pH E /\ mh_ctx mh = pCX E;
  pb_L : 17594333495296 <= mh_lexer mh /\ mh_lexer mh + 48 <= alloc_ceiling /\ mh_lexer mh mod 16 = 0;
  pb_LB : 17594333495296 <= mb_addr (mh_lexbuf mh) /\ mb_addr (mh_lexbuf mh) + 32 <= alloc_ceiling /\ mb_addr (mh_lexbuf mh) mod 16 = 0;
  pb_DB : 17594333495296 <= mb_addr (mh_decbuf mh) /\ mb_addr (mh_decbuf mh) + 32 <= alloc_ceiling /\ mb_addr (mh_decbuf mh) mod 16 = 0;
  pb_SB : 6303744 <= mh_stack mh /\ mh_stack mh + h_stack_size h <= alloc_ceiling /\ mh_stack mh mod 16 = 0;
  pb_LD : forall d, yb_data (lx_buf (h_lexer h)) = Some d -> 0 < mb_data (mh_lexbuf mh) /\ mb_data (mh_lexbuf mh) + yb_len (lx_buf (h_lexer h)) <= alloc_ceiling;
  pb_DD : forall d, yb_data (h_decbuf h) = Some d -> 0 < mb_data (mh_decbuf mh) /\ mb_data (mh_decbuf mh) + yb_len (h_decbuf h) <= alloc_ceiling;
  (* [comment removed for export] *)
  pb_HL : pH E + 104 <= mh_lexer mh \/ mh_lexer mh + 48 <= pH E;
  pb_HLB : pH E + 104 <= mb_addr (mh_lexbuf mh) \/ mb_addr (mh_lexbuf mh) + 32 <= pH E;
  pb_HLD : forall d, yb_data (lx_buf (h_lexer h)) = Some d -> pH E + 104 <= mb_data (mh_lexbuf mh) \/ mb_data (mh_lexbuf mh) + yb_len (lx_buf (h_lexer h)) <= pH E;
  pb_HDB : pH E + 104 <= mb_addr (mh_decbuf mh) \/ mb_addr (mh_decbuf mh) + 32 <= pH E;
  pb_HDD : forall d, yb_data (h_decbuf h) = Some d -> pH E + 104 <= mb_data (mh_decbuf mh) \/ mb_data (mh_decbuf mh) + yb_len (h_decbuf h) <= pH E;
  pb_HSB : pH E + 104 <= mh_stack mh \/ mh_stack mh + h_stack_size h <= pH E;
  (* [comment removed for export] *)
  pb_LSB : mh_lexer mh + 48 <= mh_stack mh \/ mh_stack mh + h_stack_size h <= mh_lexer mh;
  pb_LBSB : mb_addr (mh_lexbuf mh) + 32 <= mh_stack mh \/ mh_stack mh + h_stack_size h <= mb_addr (mh_lexbuf mh);
  pb_LDSB : forall d, yb_data (lx_buf (h_lexer h)) = Some d -> mb_data (mh_lexbuf mh) + yb_len (lx_buf (h_lexer h)) <= mh_stack mh \/ mh_stack mh + h_stack_size h <= mb_data (mh_lexbuf mh);
  pb_DBSB : mb_addr (mh_decbuf mh) + 32 <= mh_stack mh \/ mh_stack mh + h_stack_size h <= mb_addr (mh_decbuf mh);
  pb_DDSB : forall d, yb_data (h_decbuf h) = Some d -> mb_data (mh_decbuf mh) + yb_len (h_decbuf h) <= mh_stack mh \/ mh_stack mh + h_stack_size h <= mb_data (mh_decbuf mh);
  (* [comment removed for export] *)
  pb_LCX : mh_lexer mh + 48 <= pCX E \/ pCX E + 8 <= mh_lexer mh;
  pb_LBCX : mb_addr (mh_lexbuf mh) + 32 <= pCX E \/ pCX E + 8 <= mb_addr (mh_lexbuf mh);
  pb_LDCX : forall d, yb_data (lx_buf (h_lexer h)) = Some d -> mb_data (mh_lexbuf mh) + yb_len (lx_buf (h_lexer h)) <= pCX E \/ pCX E + 8 <= mb_data (mh_lexbuf mh);
  pb_DBCX : mb_addr (mh_decbuf mh) + 32 <= pCX E \/ pCX E + 8 <= mb_addr (mh_decbuf mh);
  pb_DDCX : forall d, yb_data (h_decbuf h) = Some d -> mb_data (mh_decbuf mh) + yb_len (h_decbuf h) <= pCX E \/ pCX E + 8 <= mb_data (mh_decbuf mh);
  pb_SBCX : mh_stack mh + h_stack_size h <= pCX E \/ pCX E + 8 <= mh_stack mh;
  pb_SBff : mh_stack mh + h_stack_size h <= p_ff E \/ p_ff E + 128 <= mh_stack mh;
  pb_DBff : mb_addr (mh_decbuf mh) + 32 <= p_ff E \/ p_ff E + 128 <= mb_addr (mh_decbuf mh);
  pb_Lff : mh_lexer mh + 48 <= p_ff E \/ p_ff E + 128 <= mh_lexer mh;
  pb_LBff : mb_addr (mh_lexbuf mh) + 32 <= p_ff E \/ p_ff E + 128 <= mb_addr (mh_lexbuf mh);
  pb_LDff : forall d, yb_data (lx_buf (h_lexer h)) = Some d -> mb_data (mh_lexbuf mh) + yb_len (lx_buf (h_lexer h)) <= p_ff E \/ p_ff E + 128 <= mb_data (mh_lexbuf mh);
  pb_DDff : forall d, yb_data (h_decbuf h) = Some d -> mb_data (mh_decbuf mh) + yb_len (h_decbuf h) <= p_ff E \/ p_ff E + 128 <= mb_data (mh_decbuf mh);
  pb_SBT : 0 < pLEN E -> mh_stack mh + h_stack_size h <= p_T E \/ p_T E + pLEN E <= mh_stack mh;
  (* [comment removed for export] *)
  pb_SBP : mh_stack mh + h_stack_size h <= 2147446784 \/ 17594333495296 <= mh_stack mh
}.

(* [comment removed for export] *)
Lemma pa_ffA : forall E, penvA E -> (6303744 <= p_ff E /\ (p_ff E + 128 <= 2147446784 \/ 17594333495296 <= p_ff E)).
Proof. aceil. intros E PA. pose proof (pa_ff E PA). pose proof (pa_ffP E PA). lia. Qed.
Lemma pa_CXA : forall E, penvA E -> (6303744 <= pCX E - 32 /\ (pCX E - 32 + 128 <= 2147446784 \/ 17594333495296 <= pCX E - 32)).
Proof. aceil. intros E PA. pose proof (pa_CX E PA). pose proof (pa_CXP E PA). lia. Qed.
Lemma pa_CXA8 : forall E, penvA E -> (6303744 <= pCX E /\ (pCX E + 8 <= 2147446784 \/ 17594333495296 <= pCX E)).
Proof. aceil. intros E PA. pose proof (pa_CX E PA). pose proof (pa_CXP E PA). lia. Qed.
Lemma pa_OTA : forall E, penvA E -> 0 < pLEN E -> (6303744 <= p_OT E /\ (p_OT E + p_OTn E <= 2147446784 \/ 17594333495296 <= p_OT E)).
Proof. aceil. intros E PA Hl. pose proof (pa_OT E PA Hl). pose proof (pa_OTP E PA Hl). lia. Qed.
Lemma pb_SBA : forall E mh h, pblk E mh h -> (6303744 <= mh_stack mh /\ (mh_stack mh + h_stack_size h <= 2147446784 \/ 17594333495296 <= mh_stack mh)).
Proof. aceil. intros E mh h PB. pose proof (pb_SB E mh h PB). pose proof (pb_SBP E mh h PB). lia. Qed.

(* [comment removed for export] *)
Record ppolA (P : acc -> Prop) (E : apE) (mh : mhand) (h : yhandle) : Prop := mkPP {
  pp_stk : pol P (p_lo E) (pSP E);
  pp_img : pol P AY_IMG_LO AY_IMG_HI;
  pp_imgsh : pol P 0x7fffa000 0x800b8600;   (* [comment removed for export] *)
  pp_H : pol P (pH E) (pH E + 104);
  pp_Hs : pol P (ASB + pH E / 8) (ASB + pH E / 8 + 13);
  pp_L : pol P (mh_lexer mh) (mh_lexer mh + 48);
  pp_Ls : pol P (ASB + mh_lexer mh / 8) (ASB + mh_lexer mh / 8 + 6);
  pp_DB : pol P (mb_addr (mh_decbuf mh)) (mb_addr (mh_decbuf mh) + 32);
  pp_DBs : pol P (ASB + mb_addr (mh_decbuf mh) / 8) (ASB + mb_addr (mh_decbuf mh) / 8 + 4);
  pp_SB : pol P (mh_stack mh) (mh_stack mh + h_stack_size h);
  pp_SBs : pol P (ASB + mh_stack mh / 8) (ASB + mh_stack mh / 8 + (h_stack_size h + 7) / 8);
  pp_CX : pol P (pCX E) (pCX E + 8);
  pp_CXs : pol P (ASB + pCX E / 8) (ASB + pCX E / 8 + 1);
  pp_ff : pol P (p_ff E) (p_ff E + 128);
  pp_ffs : pol P (ASB + p_ff E / 8) (ASB + p_ff E / 8 + 16);
  pp_T : 0 < pLEN E -> pol P (p_T E) (p_T E + pLEN E);
  pp_Ts : 0 < pLEN E -> pol P (ASB + p_OT E / 8) (ASB + p_OT E / 8 + (p_OTn E + 7) / 8) }.

Hypothesis BLKY : AHK_y_blocks_stmt Y.
Hypothesis LAYY : AHK_y_layout_stmt Y.
Hypothesis BSHY : AHK_y_block_shadow_stmt Y.

(* [comment removed for export] *)
Ltac dconj H :=
  lazymatch type of H with
  | _ /\ _ => let A := fresh "SP" in let B := fresh "SP" in destruct H as [A B]; dconj A; dconj B
  | _ => idtac
  end.
Lemma mk_pblk : forall E s LK h mh h0 cx0 m mo,
  penvA E -> pok E h0 cx0 -> y_AHK Y s (abl (yblocks mh h) ++ LK ++ p_REST E) (pLF E) m mo ->
  mh_same (p_mh E) mh -> h_stack_blk h <> None -> 0 < h_stack_size h -> pblk E mh h.
Proof. aceil.
  intros E s LK h mh h0 cx0 m mo PA OK AHK SAME HSB SZ.
  destruct (BLKY _ _ _ _ _ AHK) as (RNG & _ & _).
  destruct (LAYY _ _ _ _ _ AHK) as (LAYF & LAYFB & _).
  destruct SAME as (EH & EL & ELB & EDB & ECX).
  destruct OK as (_ & _ & _ & _ & TB & _ & (f & FIN & FCX & FCL) & _).
  destruct PA.
  assert (IN : forall b, In b (abl (yblocks mh h)) -> In b (abl (yblocks mh h) ++ LK ++ p_REST E)) by (intros b Hb; apply in_or_app; left; exact Hb).
  assert (R : forall A n, In (mkABlock A n) (abl (yblocks mh h)) ->
            (0 < A /\ A + n <= alloc_ceiling /\ A mod 16 = 0)
            /\ (A + n <= mh_ctx (p_mh E) \/ mh_ctx (p_mh E) + 8 <= A) /\ (A + n <= p_ff E \/ p_ff E + 128 <= A)).
  { intros A n Hb. pose proof (RNG _ (IN _ Hb)) as X. unfold ablock_range, ACONSTS in X. cbn [ab_addr ab_size c_img_hi] in X.
    aceil.
    pose proof (proj1 (LAYFB f (mkABlock A n) (or_intror FIN) (IN _ Hb))) as Z1. cbn [ab_addr ab_size snd fst] in Z1.
    pose proof (proj1 (LAYFB (1, p_ff E) (mkABlock A n) (or_introl eq_refl) (IN _ Hb))) as Z2. cbn [ab_addr ab_size snd fst] in Z2.
    rewrite FCL in Z1. unfold ff_bytes in Z1, Z2. change (Z.shiftl 64 1) with 128 in Z1, Z2.
    split; [clear -CEILB X; lia|]. split; [clear -CEILB Z1 FCX; lia| clear -CEILB Z2; lia]. }
  assert (BSH : forall A n, In (mkABlock A n) (abl (yblocks mh h)) -> 0 < n -> (6303744 <= A /\ (A + n <= 2147446784 \/ 17594333495296 <= A))).
  { intros A n Hb Hn. pose proof (BSHY _ _ _ _ _ _ AHK (IN _ Hb) Hn) as [_ Y1]. cbn [ab_addr ab_size] in Y1. unfold oshw_hi, A_SB, amem in Y1. clear -CEILB Y1. lia. }
  pose proof (R _ _ (yb_in_lexer mh h)) as (RL & RL2 & RL3). pose proof (R _ _ (yb_in_lexbuf mh h)) as (RLB & RLB2 & RLB3). pose proof (R _ _ (yb_in_decbuf mh h)) as (RDB & RDB2 & RDB3).
  pose proof pa_strhi0 as (RL1 & RLB1 & RDB1). rewrite <- EL in RL1. rewrite <- ELB in RLB1. rewrite <- EDB in RDB1.
  pose proof (R _ _ (yb_in_stack mh h HSB)) as (RSB & RSB2 & RSB3). pose proof (BSH _ _ (yb_in_stack mh h HSB) SZ) as RSB1.
  unfold SIZEOF_LEXER, SIZEOF_BUF in RL, RLB, RDB.
  assert (RLD : forall d, yb_data (lx_buf (h_lexer h)) = Some d ->
            (0 < mb_data (mh_lexbuf mh) /\ mb_data (mh_lexbuf mh) + yb_len (lx_buf (h_lexer h)) <= alloc_ceiling)
            /\ (mb_data (mh_lexbuf mh) + yb_len (lx_buf (h_lexer h)) <= mh_ctx (p_mh E) \/ mh_ctx (p_mh E) + 8 <= mb_data (mh_lexbuf mh))
            /\ (mb_data (mh_lexbuf mh) + yb_len (lx_buf (h_lexer h)) <= p_ff E \/ p_ff E + 128 <= mb_data (mh_lexbuf mh))).
  { intros d Hd. destruct (R _ _ (yb_in_lexdata mh h ltac:(rewrite Hd; discriminate))) as (X1 & X2 & X3). split; [clear -CEILB X1; lia| split; [exact X2| exact X3]]. }
  assert (RDD : forall d, yb_data (h_decbuf h) = Some d ->
            (0 < mb_data (mh_decbuf mh) /\ mb_data (mh_decbuf mh) + yb_len (h_decbuf h) <= alloc_ceiling)
            /\ (mb_data (mh_decbuf mh) + yb_len (h_decbuf h) <= mh_ctx (p_mh E) \/ mh_ctx (p_mh E) + 8 <= mb_data (mh_decbuf mh))
            /\ (mb_data (mh_decbuf mh) + yb_len (h_decbuf h) <= p_ff E \/ p_ff E + 128 <= mb_data (mh_decbuf mh))).
  { intros d Hd. destruct (R _ _ (yb_in_decdata mh h ltac:(rewrite Hd; discriminate))) as (X1 & X2 & X3). split; [clear -CEILB X1; lia| split; [exact X2| exact X3]]. }
  clear R BSH.
  assert (SEPT : forall A n, asep_from (mkABlock A n) (LK ++ p_REST E) -> 0 < zlength (p_txt E) -> A + n <= p_T E \/ p_T E + zlength (p_txt E) <= A).
  { intros A n HS Hl. destruct TB as [(bt & Hbt & B1 & B2)| Z0]; [| exfalso; clear -CEILB Hl Z0; lia].
    pose proof (asep_from_In _ _ _ HS ltac:(apply in_or_app; right; exact Hbt)) as X. unfold absep in X. cbn [ab_addr ab_size] in X. clear -CEILB X B1 B2. lia. }
  (* [comment removed for export] *)
  pose proof (ay_all_sep Y BLKY _ _ _ _ _ AHK) as ASEP.
  unfold yblocks, lexer_blocks, buf_blocks, bs_blocks, abl in ASEP. rewrite !map_cons, !map_app, !map_cons in ASEP.
  destruct (h_stack_blk h) as [sid|]; [| exfalso; apply HSB; reflexivity].
  destruct (yb_data (lx_buf (h_lexer h))) as [dl|] eqn:HDL; destruct (yb_data (h_decbuf h)) as [dd|] eqn:HDD0;
    cbn [map app aall_sep asep_from MallocBlocks.blk_addr MallocBlocks.blk_size fst snd] in ASEP;
    unfold absep in ASEP; cbn [ab_addr ab_size] in ASEP; unfold SIZEOF_HANDLE, SIZEOF_LEXER, SIZEOF_BUF in ASEP;
    rewrite ?EH in ASEP; dconj ASEP; split; rewrite ?HDL, ?HDD0;
    first [ split; [exact EH| exact ECX]
          | assumption
          | exact RL2 | exact RLB2 | exact RDB2 | exact RSB2 | exact RSB3 | exact RDB3
          | clear -CEILB RL RL1; lia | clear -CEILB RLB RLB1; lia | clear -CEILB RDB RDB1; lia | clear -CEILB RSB RSB1; lia
          | exact RL3 | exact RLB3
          | intros d Hd; first [exact (proj1 (RLD d Hd)) | exact (proj1 (RDD d Hd)) | exact (proj1 (proj2 (RLD d Hd))) | exact (proj1 (proj2 (RDD d Hd)))
                              | exact (proj2 (proj2 (RLD d Hd))) | exact (proj2 (proj2 (RDD d Hd))) | discriminate Hd | assumption]
          | intros Hl; apply SEPT; [assumption| exact Hl] ].
Qed.

(* [comment removed for export] *)
Lemma mk_ppol : forall E s LK h mh h0 cx0 m mo (Lz : list (word * word)) (Sz : word -> Prop),
  penvA E -> pok E h0 cx0 -> y_AHK Y s (abl (yblocks mh h) ++ LK ++ p_REST E) (pLF E) m mo ->
  mh_same (p_mh E) mh -> h_stack_blk h <> None -> 0 < h_stack_size h ->
  (forall x, ay_acc Y (abl (yblocks mh h) ++ LK ++ p_REST E) (pLF E) x -> acc_ok Lz Sz x) ->
  ppolA (acc_ok Lz Sz) E mh h.
Proof. aceil.
  intros E s LK h mh h0 cx0 m mo Lz Sz PA OK AHK SAME HSB SZ LINK.
  pose proof (mk_pblk E s LK h mh h0 cx0 m mo PA OK AHK SAME HSB SZ) as PB.
  destruct (BLKY _ _ _ _ _ AHK) as (RNG & _ & _).
  pose proof OK as (_ & _ & _ & _ & TB & OTB & (f & FIN & FCX & FCL) & _).
  destruct PA. destruct PB.
  set (LB := abl (yblocks mh h) ++ LK ++ p_REST E) in *.
  assert (IN : forall b, In b (abl (yblocks mh h)) -> In b LB) by (intros b Hb; unfold LB; apply in_or_app; left; exact Hb).
  assert (INR : forall b, In b (p_REST E) -> In b LB) by (intros b Hb; unfold LB; apply in_or_app; right; apply in_or_app; right; exact Hb).
  assert (FIN' : In f (pLF E)) by (right; exact FIN).
  assert (FFIN : In (1, p_ff E) (pLF E)) by (left; reflexivity).
  assert (OP : forall A n, In (mkABlock A n) (abl (yblocks mh h)) -> (6303744 <= A /\ (A + n <= 2147446784 \/ 17594333495296 <= A)) -> A + n <= alloc_ceiling ->
            pol (acc_ok Lz Sz) A (A + n) /\ pol (acc_ok Lz Sz) (ASB + A / 8) (ASB + A / 8 + (n + 7) / 8)).
  { intros A n Hb H1 H2.
    destruct (aypol_opol_block Y _ _ _ _ LINK (mkABlock A n) (IN _ Hb) ltac:(cbn; clear -CEILB H1; lia) ltac:(cbn; unfold oshw_lo, A_SB; clear -CEILB H1; lia)
                ltac:(cbn; unfold oshw_hi, A_SB, amem; clear -CEILB H1 H2; lia) ltac:(cbn; clear -CEILB H1 H2; lia)) as [P1 P2].
    cbn [ab_addr ab_size] in P1, P2. unfold oshw_lo, oshw_hi, A_SB, amem in P2. split; [exact P1| exact P2]. }
  destruct (OP _ _ (yb_in_hand mh h) ltac:(unfold SIZEOF_HANDLE; lia) ltac:(unfold SIZEOF_HANDLE; lia)) as [PH PHs].
  destruct (OP _ _ (yb_in_lexer mh h) ltac:(unfold SIZEOF_LEXER; lia) ltac:(unfold SIZEOF_LEXER; lia)) as [PL PLs].
  destruct (OP _ _ (yb_in_decbuf mh h) ltac:(unfold SIZEOF_BUF; lia) ltac:(unfold SIZEOF_BUF; lia)) as [PDB PDBs].
  destruct (OP _ _ (yb_in_stack mh h HSB) ltac:(lia) ltac:(lia)) as [PSB PSBs].
  unfold SIZEOF_HANDLE, SIZEOF_LEXER, SIZEOF_BUF in PH, PHs, PL, PLs, PDB, PDBs.
  change ((104 + 7) / 8) with 13 in PHs. change ((48 + 7) / 8) with 6 in PLs. change ((32 + 7) / 8) with 4 in PDBs.
  split.
  - apply (aypol_stack Y _ _ _ _ LINK); [aceil; lia| lia].
  - apply (aypol_img Y _ _ _ _ LINK).
  - intros a k Ha Hk. apply (aypol_imgshadow Y _ _ _ _ LINK a (a + Z.of_nat k)); [| | lia| lia]; unfold oshw_lo, oshw_hi, A_SB, amem, AY_IMG_LO, AY_IMG_HI; clear -CEILB Ha Hk; lia.
  - rewrite <- (proj1 pb_H0). exact PH.
  - rewrite <- (proj1 pb_H0). exact PHs.
  - exact PL.
  - exact PLs.
  - exact PDB.
  - exact PDBs.
  - exact PSB.
  - exact PSBs.
  - rewrite <- FCX. apply (aypol_fframe Y _ _ _ _ LINK f); [exact FIN'| lia| rewrite FCL; unfold ff_bytes; change (Z.shiftl 64 1) with 128; lia| clear -CEILB FCX pa_CX0; lia| rewrite FCL; unfold ff_bytes; change (Z.shiftl 64 1) with 128; clear -CEILB FCX pa_CX0; lia].
  - rewrite <- FCX. apply (aypol_ffshadow Y _ _ _ _ LINK f); [exact FIN'| | | |];
      rewrite ?FCL; unfold oshw_lo, A_SB; try change (Z.shiftl 8 1) with 16; clear -CEILB FCX pa_CX0; Z.div_mod_to_equations; lia.
  - apply (aypol_fframe Y _ _ _ _ LINK (1, p_ff E)); [exact FFIN| cbn; lia| cbn [fst snd]; unfold ff_bytes; change (Z.shiftl 64 1) with 128; lia| clear -CEILB pa_ff0; lia| cbn [fst snd]; unfold ff_bytes; change (Z.shiftl 64 1) with 128; clear -CEILB pa_ff0; lia].
  - apply (aypol_ffshadow Y _ _ _ _ LINK (1, p_ff E)); [exact FFIN| | | |];
      cbn [fst snd]; unfold oshw_lo, A_SB; try change (Z.shiftl 8 1) with 16; clear -CEILB pa_ff0; Z.div_mod_to_equations; lia.
  - intros Hl. destruct TB as [(bt & HBT & B1 & B2)| Z0]; [| exfalso; clear -CEILB Hl Z0; lia].
    apply (aypol_block Y _ _ _ _ LINK bt); [apply INR; exact HBT| exact B1| exact B2| clear -CEILB pa_T0; lia| ].
    pose proof (RNG bt (INR _ HBT)) as RT. unfold ablock_range in RT. clear -CEILB RT. aceil. lia.
  - intros Hl. destruct OTB as [Z0| (bt & HBT & Q1 & Q2)]; [exfalso; clear -CEILB Hl Z0; lia|]. destruct (pa_OT0 Hl) as (O8 & O1 & O2 & O3 & O4).
    pose proof (RNG bt (INR _ HBT)) as RT. unfold ablock_range, ACONSTS in RT. cbn [c_img_hi] in RT. aceil.
    apply (aypol_bshadow Y _ _ _ _ LINK bt); [apply INR; exact HBT| unfold oshw_lo, A_SB; clear -CEILB Q1 O8; Z.div_mod_to_equations; lia| | clear -CEILB O3; lia|];
      unfold oshw_lo, oshw_hi, A_SB, amem; clear -CEILB Q1 Q2 O8 RT O3 O4; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ownA (E : apE) (mh : mhand) (h : yhandle) (iv : Z * Z) : Prop :=
  (mh_addr mh <= fst iv /\ snd iv <= mh_addr mh + 72)
  \/ (mh_stack mh <= fst iv /\ snd iv <= mh_stack mh + h_stack_size h)
  \/ (pCX E <= fst iv /\ snd iv <= pCX E + 8)
  \/ (p_lo E <= fst iv /\ snd iv <= p_SQ E + 240).
Lemma ownA_outside : forall E mh h W a,
  Forall (ownA E mh h) W ->
  (a < mh_addr mh \/ mh_addr mh + 72 <= a) -> (a < mh_stack mh \/ mh_stack mh + h_stack_size h <= a) ->
  (a < pCX E \/ pCX E + 8 <= a) -> (a < p_lo E \/ p_SQ E + 240 <= a) -> outside W a.
Proof. aceil.
  intros E mh h W a HF H1 H2 H3 H4. induction HF as [| [lo hi] W HO HF IH]; [exact I|].
  cbn. split; [| exact IH]. unfold ownA in *. cbn [fst snd] in HO. lia.
Qed.
Lemma ownA_disjoint_hi : forall E mh h W a n, Forall (ownA E mh h) W ->
  mh_addr mh + 72 <= a -> mh_stack mh + h_stack_size h <= a -> pCX E + 8 <= a -> p_SQ E + 240 <= a -> disjoint_from W a n.
Proof. aceil.
  intros E mh h W a n HF H1 H2 H3 H4. induction HF as [| [lo hi] W HO HF IH]; [exact I|].
  cbn. split; [| exact IH]. unfold ownA in HO. cbn [fst snd] in HO. lia.
Qed.
Lemma munch_agree : forall W m m', munch W m m' -> wmono asegs m m' -> agree_on asegs (outside W) m m'.
Proof. aceil. intros W m m' MU WM a Ha Ho. split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha. exact Ho. Qed.
Lemma ownA_write_ok : forall E s LK h mh h0 cx0 m mo W,
  penvA E -> pok E h0 cx0 -> y_AHK Y s (abl (yblocks mh h) ++ LK ++ p_REST E) (pLF E) m mo -> mh_same (p_mh E) mh -> h_stack_blk h <> None ->
  Forall (ownA E mh h) W -> Forall (ay_write_ok (abl (yblocks mh h) ++ LK ++ p_REST E) (pLF E)) W.
Proof. aceil.
  intros E s LK h mh h0 cx0 m mo W PA OK AHK SAME HSB HF.
  pose proof OK as (_ & _ & _ & _ & _ & _ & (f & FIN & FCX & FCL) & _). destruct PA. destruct SAME as (EH & _ & _ & _ & ECX).
  induction HF as [| [lo hi] W HO HF IH]; constructor; [| exact IH].
  unfold ownA in HO. unfold ay_write_ok. cbn [fst snd] in *. destruct HO as [HO|[HO|[HO|HO]]].
  - right; left. exists (mkABlock (mh_addr mh) SIZEOF_HANDLE). split; [apply in_or_app; left; apply yb_in_hand| cbn; unfold SIZEOF_HANDLE; lia].
  - right; left. exists (mkABlock (mh_stack mh) (h_stack_size h)). split; [apply in_or_app; left; apply yb_in_stack; exact HSB| cbn; lia].
  - right; right; left. exists f. split; [right; exact FIN|]. rewrite FCL. unfold ff_bytes. change (Z.shiftl 64 1) with 128. lia.
  - left. aceil. lia.
Qed.

Hypothesis FRAMEY : AHK_y_frame_stmt Y.
Hypothesis UFRAME : forall m m' SP ra s0, (forall a, SP <= a < 2^47 -> m' (wa a) = m (wa a)) -> y_uanchor Y m SP ra s0 -> y_uanchor Y m' SP ra s0.
Lemma rw_cells_agree_out : forall W m m' A cs, munch W m m' -> wmono asegs m m' -> rw_cells asegs m A cs ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) -> outside W a) -> rw_cells asegs m' A cs.
Proof. aceil. intros W m m' A cs MU WM HC HO. eapply rw_cells_agree; [apply munch_agree; [exact MU| exact WM]| exact HC| exact HO]. Qed.

Lemma pmem_updA : forall E m m' mo s LK h mh cx obw olw cr h' cx' h0 cx0 W,
  penvA E -> pok E h0 cx0 -> pmem E m mo s LK h mh cx obw olw cr -> 0 < h_stack_size h ->
  munch W m m' -> wmono asegs m m' -> mem_inv asegs m' ->
  Forall (ownA E mh h) W ->
  h_lexer h' = h_lexer h -> h_decbuf h' = h_decbuf h -> h_stack_blk h' = h_stack_blk h -> h_stack_size h' = h_stack_size h ->
  True ->
  ahand_struct m' h' mh -> abs_rep m' (mh_stack mh) h' -> actx_rep m' (pCX E) cx' ->
  (exists k0 k224, rw_cells asegs m' (p_SQ E) (pframe E k0 k224)) ->
  rw_cells asegs m' (pSP E - 112) (psaved E) ->
  stk asegs m' (p_lo E) (p_SQ E) ->
  pmem E m' mo s LK h' mh cx' obw olw cr.
Proof. aceil.
  intros until W. intros PA OK PM SZ MU WM MI' OWN EL ED EB ES PHI HS' BS' CX' FR' SV' STK'.
  pose proof PM as (AY & HR & SAME & CXR & TXT & FR & SV & FFC & OCX & STK & GAP & MI & PRES & UA & CRED & SOR & SB1 & LKZ).
  apply AYST_split in AY. destruct AY as [AHK YS].
  destruct HR as (HS & LXR & DBR & BSR). pose proof HS as (_ & _ & _ & HU & _).
  pose proof (mk_pblk E s LK h mh h0 cx0 m mo PA OK AHK SAME SB1 SZ) as PB.
  pose proof (ownA_write_ok E s LK h mh h0 cx0 m mo W PA OK AHK SAME SB1 OWN) as WOK.
  destruct (BLKY _ _ _ _ _ AHK) as (RNG & SEP & ND).
  destruct (LAYY _ _ _ _ _ AHK) as (LAYF & LAYFB & LAYFF).
  pose proof OK as (_ & _ & _ & _ & TB & _ & (f & FIN & FCX & FCL) & _).
  pose proof (munch_agree _ _ _ MU WM) as AG.
  assert (YB : yblocks mh h' = yblocks mh h) by (unfold yblocks, lexer_blocks, bs_blocks; rewrite EL, ED, EB, ES; reflexivity).
  destruct PA. destruct PB. pose proof SAME as (EH & ELx & ELB & EDB & ECX).
  assert (IN : forall b, In b (abl (yblocks mh h)) -> In b (abl (yblocks mh h) ++ LK ++ p_REST E)) by (intros b Hb; apply in_or_app; left; exact Hb).
  assert (INR : forall b, In b (p_REST E) -> In b (abl (yblocks mh h) ++ LK ++ p_REST E)) by (intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb).
  (* [comment removed for export] *)
  assert (OUTsep : forall A n a, (A + n <= mh_addr mh \/ mh_addr mh + 104 <= A) -> (A + n <= mh_stack mh \/ mh_stack mh + h_stack_size h <= A) ->
            (A + n <= mh_ctx (p_mh E) \/ mh_ctx (p_mh E) + 8 <= A) -> A + n <= alloc_ceiling -> A <= a < A + n -> outside W a).
  { intros A n a D1 D2 D3 Rb Ha. eapply ownA_outside; [exact OWN| clear -CEILB Ha D1; lia| clear -CEILB Ha D2; lia| clear -CEILB Ha D3; lia| clear -CEILB Ha Rb pa_ceil0 pa_lo0; lia]. }
  assert (OUTlow : forall a, (a < 6303744 \/ 2147446784 <= a < 17594333495296) -> outside W a).   (* [comment removed for export] *)
  { intros a Ha. eapply ownA_outside; [exact OWN| clear -CEILB Ha pa_H0 EH; lia| clear -CEILB Ha pb_SB0 pb_SBP0; lia| clear -CEILB Ha pa_CX0 pa_CXP0; lia| clear -CEILB Ha pa_ceil0; lia]. }
  assert (OUThi : forall a, p_SQ E + 240 <= a -> outside W a).
  { intros a Ha. eapply ownA_outside; [exact OWN| clear -CEILB Ha pa_H0 EH pa_lo0 pa_ceil0 pa_SQ0; lia| clear -CEILB Ha pb_SB0 pa_lo0 pa_ceil0 pa_SQ0; lia| clear -CEILB Ha pa_CX0 pa_lo0 pa_ceil0 pa_SQ0; lia| clear -CEILB Ha; lia]. }
  (* [comment removed for export] *)
  assert (OUTR : forall b a, In b (p_REST E) -> ab_addr b <= a < ab_addr b + ab_size b -> outside W a).
  { intros b a Hb Ha.
    assert (NDa : forall A n, In (mkABlock A n) (abl (yblocks mh h)) -> ab_addr b <> A).
    { intros A n HA E0. rewrite map_app in ND. eapply (nodup_app_disj _ _ A ND).
      - apply in_map_iff. exists (mkABlock A n). split; [reflexivity| exact HA].
      - rewrite map_app. apply in_or_app. right. apply in_map_iff. exists b. split; [exact E0| exact Hb]. }
    pose proof (SEP _ _ (INR _ Hb) (IN _ (yb_in_hand mh h)) (NDa _ _ (yb_in_hand mh h))) as D1. cbn [ab_addr ab_size] in D1. unfold SIZEOF_HANDLE in D1.
    pose proof (SEP _ _ (INR _ Hb) (IN _ (yb_in_stack mh h SB1)) (NDa _ _ (yb_in_stack mh h SB1))) as D2. cbn [ab_addr ab_size] in D2.
    pose proof (proj1 (LAYFB f _ (or_intror FIN) (INR _ Hb))) as D3. rewrite FCL in D3. unfold ff_bytes in D3. change (Z.shiftl 64 1) with 128 in D3.
    pose proof (RNG _ (INR _ Hb)) as Rb. unfold ablock_range in Rb. aceil.
    eapply (OUTsep (ab_addr b) (ab_size b)); [exact D1| exact D2| clear -CEILB D3 FCX; lia| clear -CEILB Rb; lia| exact Ha]. }
  split.
  { rewrite YB. apply AYST_split. split; [eapply FRAMEY; [exact AHK| exact MU| exact WM| exact WOK]|].
    eapply aystatics_munch; [exact YS| exact MU| exact WM|].
    clear -CEILB OWN pa_H0 EH pb_SB0 pa_CX0 pa_ceil0. induction OWN as [| [lo hi] W HO HF IH]; constructor; [| exact IH].
    unfold ownA in HO. cbn [fst snd] in *. right. lia. }
  split.
  { split; [exact HS'|]. split; [| split; [| exact BS']].
    - rewrite EL. eapply lexer_rep_agree; [exact AG| exact LXR| | |].
      + intros a Ha. unfold SIZEOF_LEXER in Ha. eapply (OUTsep (mh_lexer mh) 48); [clear -CEILB pb_HL0 EH; lia| clear -CEILB pb_LSB0; lia| exact pb_LCX0| clear -CEILB pb_L0; lia| exact Ha].
      + intros a Ha. unfold SIZEOF_BUF in Ha. eapply (OUTsep (mb_addr (mh_lexbuf mh)) 32); [clear -CEILB pb_HLB0 EH; lia| clear -CEILB pb_LBSB0; lia| exact pb_LBCX0| clear -CEILB pb_LB0; lia| exact Ha].
      + intros HD a Ha. destruct (yb_data (lx_buf (h_lexer h))) as [d|] eqn:Hd; [| exfalso; apply HD; reflexivity].
        eapply (OUTsep (mb_data (mh_lexbuf mh)) (yb_len (lx_buf (h_lexer h))));
          [pose proof (pb_HLD0 d eq_refl); clear -CEILB H EH; lia| pose proof (pb_LDSB0 d eq_refl); clear -CEILB H; lia| exact (pb_LDCX0 d eq_refl)| pose proof (pb_LD0 d eq_refl); clear -CEILB H; lia| exact Ha].
    - rewrite ED. eapply buf_rep_agree; [exact AG| exact DBR| |].
      + intros a Ha. unfold SIZEOF_BUF in Ha. eapply (OUTsep (mb_addr (mh_decbuf mh)) 32); [clear -CEILB pb_HDB0 EH; lia| clear -CEILB pb_DBSB0; lia| exact pb_DBCX0| clear -CEILB pb_DB0; lia| exact Ha].
      + intros HD a Ha. destruct (yb_data (h_decbuf h)) as [d|] eqn:Hd; [| exfalso; apply HD; reflexivity].
        eapply (OUTsep (mb_data (mh_decbuf mh)) (yb_len (h_decbuf h)));
          [pose proof (pb_HDD0 d eq_refl); clear -CEILB H EH; lia| pose proof (pb_DDSB0 d eq_refl); clear -CEILB H; lia| exact (pb_DDCX0 d eq_refl)| pose proof (pb_DD0 d eq_refl); clear -CEILB H; lia| exact Ha]. }
  split; [exact SAME|]. split; [exact CX'|].
  split.
  { eapply text_at_agree; [exact AG| exact TXT|]. intros a Ha.
    destruct (Z.eq_dec (zlength (p_txt E)) 0) as [Z0|NZ]; [exfalso; clear -CEILB Ha Z0; lia|].
    assert (Hl : 0 < zlength (p_txt E)) by (clear -CEILB NZ pa_len0; lia).
    destruct (pa_Tsep0 Hl) as (T1 & T2 & T3). pose proof (pb_SBT0 Hl) as T4. pose proof (pa_OT0 Hl) as (_ & _ & T5 & _ & T6).
    eapply (OUTsep (p_T E) (zlength (p_txt E))); [clear -CEILB T1 EH; lia| clear -CEILB T4; lia| clear -CEILB T3; lia| clear -CEILB T5 T6; lia| exact Ha]. }
  split; [exact FR'|]. split; [exact SV'|].
  split.
  { assert (OF : forall A cs, rw_cells asegs m A cs -> p_ff E <= A -> A + Z.of_nat (cells_size cs) <= p_ff E + 128 -> rw_cells asegs m' A cs).
    { intros A cs HC H1 H2. eapply rw_cells_agree_out; [exact MU| exact WM| exact HC|]. intros a Ha.
      eapply (OUTsep (p_ff E) 128); [clear -CEILB pa_ffH0 EH; lia| clear -CEILB pb_SBff0; lia| clear -CEILB pa_ffCX0; lia| clear -CEILB pa_ff0; lia| clear -CEILB Ha H1 H2; lia]. }
    destruct FFC as (F1 & F2 & F3 & F4 & F5 & F6). destruct pa_j0 as (J1 & J2 & J3).
    split; [apply (OF _ _ F1); [lia| unfold pffA; cbn [cells_size csize Nat.add]; lia]|].
    split; [apply (OF _ _ F2); [lia| cbn [cells_size csize Nat.add]; lia]|].
    split; [apply (OF _ _ F3); [lia| cbn [cells_size csize Nat.add]; lia]|].
    split; [apply (OF _ _ F4); [lia| cbn [cells_size csize Nat.add]; lia]|].
    split; [apply (OF _ _ F5); [lia| unfold pffZ; cbn [cells_size csize Nat.add]; lia]|].
    eapply rw_cells_agree_out; [exact MU| exact WM| exact F6|]. intros a Ha. apply OUTlow. revert Ha. unfold pffsh. cbn [cells_size csize Nat.add]. clear -CEILB pa_ff0. intros Ha. lia. }
  split.
  { eapply oshadow_agree; [exact AG| exact OCX|]. intros a Ha. apply OUTlow. revert Ha. unfold oshw_lo, oshw_hi, A_SB, amem. clear -CEILB pa_CX0. intros Ha. lia. }
  split; [exact STK'|]. split; [eapply stk_transport_disjoint; [exact GAP| exact MU| exact WM|]; eapply ownA_disjoint_hi; [exact OWN| | | |]; clear -CEILB pa_H0 EH pb_SB0 pa_CX0 pa_ceil0 pa_lo0 pa_SQ0; lia|].
  split; [exact MI'|].
  split.
  { eapply ay_pres_trans; [exact PRES|]. eapply ay_pres_of_munch; [exact MU| exact WM|].
    intros a Ha Hc Hx. destruct Hc as [Hc|[Hc|[Hc|Hc]]].
    - apply OUThi. clear -CEILB Hc pa_SQ0. lia.
    - destruct Hc as (b & Hb & Hr). eapply OUTR; [exact Hb| exact Hr].
    - destruct Hc as (f' & Hf' & Hr).
      pose proof (LAYF f' (or_intror Hf')) as (F1' & F2' & _ & F4' & _). aceil.
      destruct Hr as [Hr|Hr].
      + (* [comment removed for export] *)
        pose proof (proj1 (LAYFB f' _ (or_intror Hf') (IN _ (yb_in_hand mh h)))) as D1. cbn [ab_addr ab_size] in D1. unfold SIZEOF_HANDLE in D1.
        pose proof (proj1 (LAYFB f' _ (or_intror Hf') (IN _ (yb_in_stack mh h SB1)))) as D2. cbn [ab_addr ab_size] in D2.
        eapply ownA_outside; [exact OWN| clear -CEILB Hr D1; lia| clear -CEILB Hr D2; lia| | clear -CEILB Hr F2' pa_ceil0; lia].
        destruct (Z.eq_dec (snd f') (snd f)) as [EQ|NE].
        * (* [comment removed for export] *) cbn [yin_ivs fst snd] in Hx. clear -CEILB Hx. lia.
        * pose proof (LAYFF f' f (or_intror Hf') (or_intror FIN) NE) as D3. rewrite FCL in D3. change (ff_bytes 1) with 128 in D3.
          clear -CEILB Hr D3 FCX. lia.
      + apply OUTlow. revert Hr F1' F2' F4' CEILB. clear. unfold oshw_lo, oshw_hi, A_SB, amem. intros Hr F1' F2' F4' CEILB.
        assert (E0 : fst f' = 0 \/ fst f' = 1) by lia.
        destruct E0 as [E0|E0]; rewrite E0 in Hr, F1', F2';
          [change (ff_bytes 0) with 64 in F1', F2'; change (Z.shiftl 8 0) with 8 in Hr| change (ff_bytes 1) with 128 in F1', F2'; change (Z.shiftl 8 1) with 16 in Hr]; lia.
    - apply OUTlow. unfold ay_static in Hc. clear -CEILB Hc. lia. }
  pose proof (bv_unsigned_in_range 64 (p_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  split; [eapply UFRAME; [| exact UA]; intros a Ha; apply MU; rewrite wa_unsigned by (clear -CEILB Ha SPR; lia); apply OUThi; clear -CEILB Ha pa_SQ0; lia|].
  split; [exact CRED|].
  split; [exact SOR|].
  rewrite EB. split; [exact SB1| lk_nil].   (* [comment removed for export] *)
Qed.

(* [comment removed for export] *)
Lemma pmem_remodel : forall E m mo mo1 s LK h mh cx obw olw cr,
  pmem E m mo s LK h mh cx obw olw cr -> y_AHK Y s (abl (yblocks mh h) ++ LK ++ p_REST E) (pLF E) m mo1 ->
  y_ayR Y (p_st0 E) (p_mo0 E) s mo1 -> pmem E m mo1 s LK h mh cx obw olw cr.
Proof. aceil.
  intros until cr. intros PM AHK1 R1.
  destruct PM as (AY & HR & SAME & CXR & TXT & FR & SV & FFC & OCX & STK & GAP & MI & PRES & UA & [CRED CR0] & [SO1 _] & SB1 & LKZ).
  apply AYST_split in AY. destruct AY as [_ YS].
  unfold pmem. repeat match goal with |- _ /\ _ => split end; try assumption.
  apply AYST_split. split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ploop_of_pass : forall E, penvA E -> ppass_stmt E -> forall fuel, ploop_at E fuel.
Proof. aceil.
  intros E PA PASS. induction fuel as [|fuel IH]; unfold ploop_at; intros until t6; intros HI FUEL EXIT.
  { exfalso. destruct HI as (_ & (_ & LP & _) & _). pose proof (loop_pre_passes_left_pos _ _ _ LP). clear -CEILB H FUEL. cbn in FUEL. lia. }
  eapply PASS; [exact HI| |].
  - (* [comment removed for export] *)
    unfold pexit_cont in EXIT |- *. intros until LK0. intros R'. eapply EXIT. eapply yparse_loop_leaf_done. exact R'.
  - (* [comment removed for export] *)
    intros until t6'. intros YLS HI'.
    destruct HI as (_ & (_ & LP & _) & _). destruct PA.
    destruct (yparse_step_again_facts (p_txt E) (zlength (p_txt E)) h cx h' cx' eq_refl ltac:(clear -CEILB pa_len0; lia) LP YLS) as (LP' & U1 & PL').
    eapply IH; [exact HI'| clear -CEILB PL' FUEL; lia|].
    unfold pexit_cont in EXIT |- *. intros until LK0. intros R'.
    intros SO' R2' CR' A0' MI' STK' FRM' PRES' HR' SAME' CXR' TXT' SH1 SH2 SH3 AY'.
    eapply EXIT; try eassumption.
    eapply yparse_loop_leaf_again; [exact YLS| exact R'].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sub_chunk : forall m A cs1 cs2 cs3,
  rw_cells asegs m A (cs1 ++ cs2 ++ cs3) -> rw_cells asegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof. aceil.
  intros m A cs1 cs2 cs3 H. apply (proj1 (ycells_app asegs _ _ cs1 (cs2 ++ cs3))) in H. destruct H as [_ H].
  apply (proj1 (ycells_app asegs _ _ cs2 cs3)) in H. destruct H as [H _]. exact H.
Qed.
Lemma pff_oshadow_OB : forall E m obw olw, penvA E -> pff E m obw olw -> oshadow m (p_ff E + 32) 8.
Proof. aceil.
  intros E m obw olw PA (_ & _ & _ & _ & _ & FSH). destruct PA. destruct pa_ff0 as (F1 & F2 & F3).
  unfold oshadow, block_shadow. split; [clear -CEILB F3; Z.div_mod_to_equations; lia|]. split; [lia|].
  unfold pffsh in FSH.
  pose proof (sub_chunk m _ [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241)] [C1 (Z_to_bv 8 0)]
               [C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); CB 4 (repeat (Z_to_bv 8 0) 4)] FSH) as X.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in X.
  replace (A_SB + (p_ff E + 32) / 8) with (p_ff E / 8 + 2147450880 + 4) by (unfold A_SB; clear -CEILB F3; Z.div_mod_to_equations; lia).
  change (blk_shadow 8) with [Z_to_bv 8 0]. replace (p_ff E / 8 + 2147450880 + 4) with (p_ff E / 8 + 2147450880 + Z.of_nat 4) by lia.
  apply (u8arr_of_rw_cells asegs _ _ 1). eapply rw_cells_reshape; [exact X| cbn; lia| reflexivity| reflexivity].
Qed.
Lemma pff_oshadow_OL : forall E m obw olw, penvA E -> pff E m obw olw -> oshadow m (p_ff E + 64) 4.
Proof. aceil.
  intros E m obw olw PA (_ & _ & _ & _ & _ & FSH). destruct PA. destruct pa_ff0 as (F1 & F2 & F3).
  unfold oshadow, block_shadow. split; [clear -CEILB F3; Z.div_mod_to_equations; lia|]. split; [lia|].
  unfold pffsh in FSH.
  pose proof (sub_chunk m _ [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242)]
               [C1 (Z_to_bv 8 4)] [C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); CB 4 (repeat (Z_to_bv 8 0) 4)] FSH) as X.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in X.
  replace (A_SB + (p_ff E + 64) / 8) with (p_ff E / 8 + 2147450880 + 8) by (unfold A_SB; clear -CEILB F3; Z.div_mod_to_equations; lia).
  change (blk_shadow 4) with [Z_to_bv 8 4]. replace (p_ff E / 8 + 2147450880 + 8) with (p_ff E / 8 + 2147450880 + Z.of_nat 8) by lia.
  apply (u8arr_of_rw_cells asegs _ _ 1). eapply rw_cells_reshape; [exact X| cbn; lia| reflexivity| reflexivity].
Qed.
End WithY.

End RC__2.
Arguments mkPE {Y}.
Arguments pmem_remodel {RC__} {Y}.
Arguments penvA {RC__} {Y}.
Arguments pa_ceil {RC__} {Y}.
Arguments pa_lo {RC__} {Y}.
Arguments pa_sp {RC__} {Y}.
Arguments pa_SQ {RC__} {Y}.
Arguments pa_H {RC__} {Y}.
Arguments pa_CX {RC__} {Y}.
Arguments pa_ff {RC__} {Y}.
Arguments pa_ffCX {RC__} {Y}.
Arguments pa_ffH {RC__} {Y}.
Arguments pa_CXH {RC__} {Y}.
Arguments pa_len {RC__} {Y}.
Arguments pa_T {RC__} {Y}.
Arguments pa_OT {RC__} {Y}.
Arguments pa_Tsep {RC__} {Y}.
Arguments pa_j {RC__} {Y}.
Arguments pa_strhi {RC__} {Y}.
Arguments pblk {RC__} {Y}.
Arguments pb_H {RC__} {Y}.
Arguments pb_L {RC__} {Y}.
Arguments pb_LB {RC__} {Y}.
Arguments pb_DB {RC__} {Y}.
Arguments pb_SB {RC__} {Y}.
Arguments pb_LD {RC__} {Y}.
Arguments pb_DD {RC__} {Y}.
Arguments pb_HL {RC__} {Y}.
Arguments pb_HLB {RC__} {Y}.
Arguments pb_HLD {RC__} {Y}.
Arguments pb_HDB {RC__} {Y}.
Arguments pb_HDD {RC__} {Y}.
Arguments pb_HSB {RC__} {Y}.
Arguments pb_LSB {RC__} {Y}.
Arguments pb_LBSB {RC__} {Y}.
Arguments pb_LDSB {RC__} {Y}.
Arguments pb_DBSB {RC__} {Y}.
Arguments pb_DDSB {RC__} {Y}.
Arguments pb_LCX {RC__} {Y}.
Arguments pb_LBCX {RC__} {Y}.
Arguments pb_LDCX {RC__} {Y}.
Arguments pb_DBCX {RC__} {Y}.
Arguments pb_DDCX {RC__} {Y}.
Arguments pb_SBCX {RC__} {Y}.
Arguments pb_SBff {RC__} {Y}.
Arguments pb_DBff {RC__} {Y}.
Arguments pb_Lff {RC__} {Y}.
Arguments pb_LBff {RC__} {Y}.
Arguments pb_LDff {RC__} {Y}.
Arguments pb_DDff {RC__} {Y}.
Arguments pb_SBT {RC__} {Y}.
Arguments ppolA {Y}.
Arguments pp_stk {Y}.
Arguments pp_img {Y}.
Arguments pp_imgsh {Y}.
Arguments pp_H {Y}.
Arguments pp_Hs {Y}.
Arguments pp_L {Y}.
Arguments pp_Ls {Y}.
Arguments pp_DB {Y}.
Arguments pp_DBs {Y}.
Arguments pp_SB {Y}.
Arguments pp_SBs {Y}.
Arguments pp_CX {Y}.
Arguments pp_CXs {Y}.
Arguments pp_ff {Y}.
Arguments pp_ffs {Y}.
Arguments pp_T {Y}.
Arguments pp_Ts {Y}.
Arguments mkPA {RC__} {Y}.
Arguments mkPB {RC__} {Y}.
Arguments pa_ffA {RC__} {Y} [E].
Arguments pa_CXA {RC__} {Y} [E].
Arguments pa_CXA8 {RC__} {Y} [E].
Arguments pa_OTA {RC__} {Y} [E].
Arguments pb_SBA {RC__} {Y} [E] [mh] [h].
Arguments pb_SBP {RC__} {Y}.
Arguments pa_CXP {RC__} {Y}.
Arguments pa_ffP {RC__} {Y}.
Arguments pa_OTP {RC__} {Y}.
Arguments mkPP {Y}.
Arguments p_sp {Y} _.
Arguments p_gp {Y} _.
Arguments p_tp {Y} _.
Arguments p_ra {Y} _.
Arguments p_s0 {Y} _.
Arguments p_s1 {Y} _.
Arguments p_s2 {Y} _.
Arguments p_s3 {Y} _.
Arguments p_s4 {Y} _.
Arguments p_s5 {Y} _.
Arguments p_s6 {Y} _.
Arguments p_s7 {Y} _.
Arguments p_s8 {Y} _.
Arguments p_s9 {Y} _.
Arguments p_s10 {Y} _.
Arguments p_s11 {Y} _.
Arguments p_fs0 {Y} _.
Arguments p_SQ {Y} _.
Arguments p_ff {Y} _.
Arguments p_fj1 {Y} _.
Arguments p_fj2 {Y} _.
Arguments p_fj3 {Y} _.
Arguments p_ffp {Y} _.
Arguments p_lo {Y} _.
Arguments p_T {Y} _.
Arguments p_txt {Y} _.
Arguments p_OT {Y} _.
Arguments p_OTn {Y} _.
Arguments p_K {Y} _.
Arguments p_LF {Y} _.
Arguments p_REST {Y} _.
Arguments p_mh {Y} _.
Arguments p_RR {Y} _.
Arguments p_m0 {Y} _.
Arguments p_st0 {Y} _.
Arguments p_mo0 {Y} _.
Arguments pLF {Y}.
Arguments pframe {Y}.
Arguments psaved {Y}.
Arguments pffA {Y}.
Arguments pffZ {Y}.
Arguments pff {Y}.
Arguments pstate {Y}.
Arguments pok {Y}.
Arguments pmem {Y}.
Arguments ppot {Y}.
Arguments pcr {Y}.
Arguments pcr_full {RC__} {Y}.
Arguments phead {Y}.
Arguments phead_inv {Y}.
Arguments pexit_cont {Y}.
Arguments ploop_at {Y}.
Arguments ppass_stmt {Y}.
Arguments pblk {RC__} {Y}.
Arguments ppolA {Y}.
Arguments ownA {Y}.
Arguments mk_pblk {RC__} {Y}.
Arguments mk_ppol {RC__} {Y}.
Arguments pmem_updA {RC__} {Y}.
Arguments ploop_of_pass {RC__} {Y}.
Arguments pff_oshadow_OB {RC__} {Y}.
Arguments pff_oshadow_OL {RC__} {Y}.
Arguments ownA_outside {RC__} {Y}.
Arguments ownA_write_ok {RC__} {Y}.
Notation pSP E := (bv_unsigned (p_sp E)) (only parsing).
Notation pH E := (mh_addr (p_mh E)) (only parsing).
Notation pCX E := (mh_ctx (p_mh E)) (only parsing).
Notation pLEN E := (zlength (p_txt E)) (only parsing).
Notation pAF E := (mh_addr (p_mh E) + 72) (only parsing).

(* [comment removed for export] *)
Ltac openPA PA := let X := fresh in pose proof PA as X; destruct X as [pa_ceil0 pa_lo0 pa_sp0 pa_SQ0 pa_H0 pa_CX0 pa_ff0 pa_ffCX0 pa_ffH0 pa_CXH0 pa_len0 pa_T0 pa_OT0 pa_Tsep0 pa_j0 pa_strhi0 pa_CXP0 pa_ffP0 pa_OTP0]; yhide pa_CXP0; yhide pa_ffP0; yhide pa_OTP0.
Ltac openPB PB := let X := fresh in pose proof PB as X; destruct X as [pb_H0 pb_L0 pb_LB0 pb_DB0 pb_SB0 pb_LD0 pb_DD0 pb_HL0 pb_HLB0 pb_HLD0 pb_HDB0 pb_HDD0 pb_HSB0 pb_LSB0 pb_LBSB0 pb_LDSB0 pb_DBSB0 pb_DDSB0 pb_LCX0 pb_LBCX0 pb_LDCX0 pb_DBCX0 pb_DDCX0 pb_SBCX0 pb_SBff0 pb_DBff0 pb_Lff0 pb_LBff0 pb_LDff0 pb_DDff0 pb_SBT0 pb_SBP0]; yhide pb_SBP0.
Ltac openPP PP := let X := fresh in pose proof PP as X; destruct X as [pp_stk0 pp_img0 pp_imgsh0 pp_H0 pp_Hs0 pp_L0 pp_Ls0 pp_DB0 pp_DBs0 pp_SB0 pp_SBs0 pp_CX0 pp_CXs0 pp_ff0 pp_ffs0 pp_T0 pp_Ts0].
(* [comment removed for export] *)
Ltac popen OK PM :=
  pose proof PM as (AY & HR & SAME & CXR & TXT & (k0 & k224 & FR) & SV & FF & OCX & STK & GAP & MI & PRES & UA & (CRED & CR0) & (SO1 & R1) & SB1 & LKZ);
  pose proof OK as (K0 & LP & U0 & (SB0 & SZM) & TB & OTB & (f & FIN & FCX & FCL) & LC0 & NBIG & RR0 & TP & FFP & FFR0);
  apply AYST_split in AY; destruct AY as [AHK YS];
  pose proof HR as (HS & LXR & DBR & BSR); pose proof HS as ((pew & pad & HC & PW) & BC1 & BC2 & BC3 & BC4);
  unfold pframe in FR.
(* [comment removed for export] *)
Section RC__3.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma loop_pre_exit_facts : forall len h cx, loop_pre len h cx ->
  (yb_data (lx_buf (h_lexer h)) <> None -> 0 < yb_len (lx_buf (h_lexer h))) /\
  (yb_data (h_decbuf h) <> None -> 0 < yb_len (h_decbuf h)) /\ 0 < h_stack_size h.
Proof. aceil.
  intros len h cx LP.
  assert (W : weak_inv len h) by (destruct LP as [HI|[W _]]; [apply (hinv_weak _ _ _ HI)| exact W]).
  destruct W as (NE & US & _ & DBI & LBI & _). split; [| split].
  - intros HD. destruct LBI as (U0 & _ & _ & _ & DL & _). specialize (DL HD). lia.
  - intros HD. destruct DBI as (U0 & _ & _ & _ & DL & _). specialize (DL HD). lia.
  - unfold h_used in US. destruct (h_stack h); [exfalso; apply NE; reflexivity|]. unfold zlength in US. cbn [length] in US. lia.
Qed.
End RC__3.
