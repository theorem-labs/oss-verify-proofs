(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs CJ_iface AShadow ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_memcpy F_memset F_memchr ICPT_mem3 ICPT_mem4 ICPT_str3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope. Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition app_iv (iv : Z * Z) : Prop := snd iv <= 0x7fff8000 \/ KHIGHMEM_BEG <= fst iv.

(* [comment removed for export] *)
Definition A_PFX_TBL : Z := 0x10b84.    (* [comment removed for export] *)
Definition A_FPFX_STR : Z := 0x1380a.   (* [comment removed for export] *)
Definition A_DOT_STR : Z := 0x142a3.    (* [comment removed for export] *)
Definition musl_lit_shadow (m : word -> option byte) : Prop :=
  shadow_ok m A_PFX_TBL 9 /\ shadow_ok m A_FPFX_STR 19 /\ shadow_ok m A_DOT_STR 2.

(* [comment removed for export] *)
Definition icpt_cells2 (m : word -> option byte) : Prop :=
  ro_cells asegs m 0xa3cb8 [C8 (Z_to_bv 64 0x906c4)]       (* [comment removed for export] *)
  /\ ro_cells asegs m 0xa3db0 [C8 (Z_to_bv 64 0x9badc)].   (* [comment removed for export] *)
Definition icpt2_ivs : list (Z * Z) := [(0xa3cb8, 0xa3cc0); (0xa3db0, 0xa3db8)].

Definition MRT (m : word -> option byte) : Prop :=
  icpt_cells m /\ stack_shadow_zero m /\ musl_lit_shadow m /\ icpt_cells2 m.

(* [comment removed for export] *)
Definition mrt_iv_ok (iv : Z * Z) : Prop :=
  Forall (fun c => snd iv <= fst c \/ snd c <= fst iv) (icpt_cell_ivs ++ icpt2_ivs) /\ app_iv iv.

Lemma disjoint_from_of_ivs : forall W a n,
  Forall (fun iv => snd iv <= a \/ a + n <= fst iv) W -> disjoint_from W a n.
Proof.
  induction W as [|[u v] W IH]; cbn; intros a n H; [exact I|].
  apply Forall_cons_iff in H as [H1 H2]. cbn [fst snd] in H1. split; [lia| apply IH; exact H2].
Qed.

Lemma disjoint_from_app_ivs : forall W a k,
  Forall app_iv W -> 0x7fff8000 <= a -> a + k <= KHIGHMEM_BEG -> disjoint_from W a k.
Proof.
  induction W as [|[u v] W IH]; cbn; intros a k HW H1 H2; [exact I|].
  apply Forall_cons_iff in HW as [Hh HW]. unfold app_iv in Hh. cbn [fst snd] in Hh.
  split; [lia| apply IH; assumption].
Qed.

Lemma shadow_ok_munch_app : forall W m m' A n,
  shadow_ok m A n -> munch W m m' -> 0 < n -> app_range A n -> Forall app_iv W -> shadow_ok m' A n.
Proof.
  intros W m m' A n SO MU Hn AR HW.
  pose proof (app_range_lt47 A n AR) as R.
  pose proof (SH_bounds A ltac:(lia)) as B1. pose proof (SH_bounds (A + n - 1) ltac:(lia)) as B2.
  eapply shadow_ok_munch; [exact SO| exact MU| exact Hn| lia| unfold KHIGHMEM_BEG, AIMG_HI in *; lia|].
  apply disjoint_from_app_ivs; [exact HW| Z.div_mod_to_equations; lia|].
  unfold KHIGHMEM_BEG, AIMG_HI in *. Z.div_mod_to_equations. lia.
Qed.

Lemma MRT_munch : forall W m m',
  MRT m -> munch W m m' -> Forall mrt_iv_ok W -> MRT m'.
Proof.
  intros W m m' (IC & SZ & (L1 & L2 & L3) & (R1 & R2)) MU HW.
  assert (HA : Forall app_iv W).
  { apply Forall_forall. intros iv Hiv. exact (proj2 (proj1 (Forall_forall _ _) HW iv Hiv)). }
  assert (DJ : forall c, In c (icpt_cell_ivs ++ icpt2_ivs) -> disjoint_from W (fst c) (snd c - fst c)).
  { intros c Hc. apply disjoint_from_of_ivs.
    apply Forall_forall. intros iv Hiv. pose proof (proj1 (Forall_forall _ _) HW iv Hiv) as [H1 _].
    pose proof (proj1 (Forall_forall _ _) H1 c Hc) as H. cbn in H. lia. }
  split; [| split; [| split; [split; [| split]| split]]].
  - eapply icpt_cells_munch; [exact IC| exact MU|].
    apply Forall_forall. intros c Hc. apply DJ. apply in_app_iff. left; exact Hc.
  - eapply stack_shadow_zero_munch; [exact SZ| exact MU|].
    apply Forall_forall. intros [u v] Hiv. pose proof (proj1 (Forall_forall _ _) HA (u, v) Hiv) as H.
    unfold app_iv in H. cbn [fst snd] in H |- *. unfold SSZ_LO, SSZ_HI, KHIGHMEM_BEG in *. lia.
  - eapply shadow_ok_munch_app; [exact L1| exact MU| lia| left; unfold lowmem_range, A_PFX_TBL, KLOWSHADOW_BEG; lia| exact HA].
  - eapply shadow_ok_munch_app; [exact L2| exact MU| lia| left; unfold lowmem_range, A_FPFX_STR, KLOWSHADOW_BEG; lia| exact HA].
  - eapply shadow_ok_munch_app; [exact L3| exact MU| lia| left; unfold lowmem_range, A_DOT_STR, KLOWSHADOW_BEG; lia| exact HA].
  - eapply ro_cells_transport; [exact R1| exact MU|]. apply (DJ (0xa3cb8, 0xa3cc0)). apply in_app_iff; right; cbn; tauto.
  - eapply ro_cells_transport; [exact R2| exact MU|]. apply (DJ (0xa3db0, 0xa3db8)). apply in_app_iff; right; cbn; tauto.
Qed.

(* [comment removed for export] *)
Definition lit_or_stack (S L : Z) : Prop :=
  (alloc_ceiling + 64 <= S /\ S + L + 64 <= 2^47)
  \/ (A_PFX_TBL <= S /\ S + L <= A_PFX_TBL + 9)
  \/ (A_FPFX_STR <= S /\ S + L <= A_FPFX_STR + 19)
  \/ (A_DOT_STR <= S /\ S + L <= A_DOT_STR + 2).

Lemma lit_or_stack_ok : forall m S L,
  MRT m -> lit_or_stack S L -> 0 < L -> shadow_ok m S L /\ app_range S L.
Proof.
  intros m S L MR LS HL. destruct MR as (IC & SZ & (L1 & L2 & L3) & _).
  destruct LS as [H|[H|[H|H]]].
  - split. { apply stack_shadow_zero_shadow_ok; try exact SZ; lia. }
    right. unfold highmem_range, KHIGHMEM_BEG, KHIGHMEM_END, alloc_ceiling, sp_window_lo, stack_max_size in *. lia.
  - split. { eapply (shadow_ok_sub m A_PFX_TBL 9); [exact L1| lia| lia| lia]. } left. unfold lowmem_range, A_PFX_TBL, KLOWSHADOW_BEG in *. lia.
  - split. { eapply (shadow_ok_sub m A_FPFX_STR 19); [exact L2| lia| lia| lia]. } left. unfold lowmem_range, A_FPFX_STR, KLOWSHADOW_BEG in *. lia.
  - split. { eapply (shadow_ok_sub m A_DOT_STR 2); [exact L3| lia| lia| lia]. } left. unfold lowmem_range, A_DOT_STR, KLOWSHADOW_BEG in *. lia.
Qed.
Lemma lit_or_stack_app : forall S L, lit_or_stack S L -> 0 <= L -> app_range S L.
Proof.
  intros S L [H|[H|[H|H]]] HL.
  - right. unfold highmem_range, KHIGHMEM_BEG, KHIGHMEM_END, alloc_ceiling, sp_window_lo, stack_max_size in *. lia.
  - left. unfold lowmem_range, A_PFX_TBL, KLOWSHADOW_BEG in *. lia.
  - left. unfold lowmem_range, A_FPFX_STR, KLOWSHADOW_BEG in *. lia.
  - left. unfold lowmem_range, A_DOT_STR, KLOWSHADOW_BEG in *. lia.
Qed.

(* [comment removed for export] *)
Lemma mrt_iv_ok_high : forall u v, KHIGHMEM_BEG <= u -> mrt_iv_ok (u, v).
Proof.
  intros u v H. unfold mrt_iv_ok, icpt_cell_ivs, icpt2_ivs, app_iv, KHIGHMEM_BEG in *. cbn [fst snd].
  split; [| right; lia]. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
Qed.
Lemma mrt_iv_ok_stack : forall u v, alloc_ceiling <= u -> mrt_iv_ok (u, v).
Proof. intros u v H. apply mrt_iv_ok_high. unfold KHIGHMEM_BEG, alloc_ceiling, sp_window_lo, stack_max_size in *. lia. Qed.
(* [comment removed for export] *)
Lemma mrt_iv_ok_mid : forall u v, 0x1e4000 <= u -> v <= 0x7fff8000 -> mrt_iv_ok (u, v).
Proof.
  intros u v H1 H2. unfold mrt_iv_ok, icpt_cell_ivs, icpt2_ivs, app_iv in *. cbn [fst snd app].
  split; [| left; exact H2]. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
Qed.
Lemma mrt_iv_ok_low : forall u v, v <= 0xa1f70 -> mrt_iv_ok (u, v).
Proof.
  intros u v H. unfold mrt_iv_ok, icpt_cell_ivs, icpt2_ivs, app_iv in *. cbn [fst snd app].
  split; [| left; lia]. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
Qed.
(* [comment removed for export] *)
Lemma mrt_iv_ok_libcdata : forall u v, 0xa3e10 <= u -> v <= 0xaa278 -> mrt_iv_ok (u, v).
Proof.
  intros u v H1 H2. unfold mrt_iv_ok, icpt_cell_ivs, icpt2_ivs, app_iv in *. cbn [fst snd app].
  split; [| left; lia]. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
Qed.
Lemma mrt_iv_ok_app : forall iv, mrt_iv_ok iv -> app_iv iv.
Proof. intros iv [_ H]; exact H. Qed.
Lemma mrt_ivs_app : forall W, Forall mrt_iv_ok W -> Forall app_iv W.
Proof. intros W H. eapply Forall_impl; [| exact H]. intros iv; apply mrt_iv_ok_app. Qed.

(* [comment removed for export] *)
Lemma AINTRIN_STACK_val : AINTRIN_STACK = 2304. Proof. reflexivity. Qed.
Lemma ASTRFN_STACK_val : ASTRFN_STACK = 2400. Proof. reflexivity. Qed.

Lemma MRT_icpt : forall m, MRT m -> icpt_cells m. Proof. intros m (H & _ & _ & _); exact H. Qed.
Lemma MRT_ssz : forall m, MRT m -> stack_shadow_zero m. Proof. intros m (_ & H & _ & _); exact H. Qed.
Lemma MRT_lit : forall m, MRT m -> musl_lit_shadow m. Proof. intros m (_ & _ & H & _); exact H. Qed.
Lemma MRT_icpt2 : forall m, MRT m -> icpt_cells2 m. Proof. intros m (_ & _ & _ & H); exact H. Qed.

Lemma MRT_shadow_ok_stack : forall m a n,
  MRT m -> alloc_ceiling + 64 <= a -> a + n + 64 <= 2^47 -> 0 < n -> shadow_ok m a n.
Proof. intros m a n H. apply stack_shadow_zero_shadow_ok. exact (MRT_ssz m H). Qed.

Lemma app_iv_high : forall u v, KHIGHMEM_BEG <= u -> app_iv (u, v).
Proof. intros; right; assumption. Qed.
Lemma app_iv_stack : forall u v, alloc_ceiling <= u -> app_iv (u, v).
Proof. intros u v H. right. cbn. unfold KHIGHMEM_BEG, alloc_ceiling, sp_window_lo, stack_max_size in *. lia. Qed.
Lemma app_iv_img : forall u v, v <= AIMG_HI -> app_iv (u, v).
Proof. intros u v H. left. cbn. unfold AIMG_HI in H. lia. Qed.
Lemma app_iv_of_range : forall a n, app_range a n -> app_iv (a, a + n).
Proof.
  intros a n [H|H]; [left|right]; cbn; unfold lowmem_range, highmem_range, KLOWSHADOW_BEG in H; lia.
Qed.

(* [comment removed for export] *)
Lemma app_range_stack : forall a n, alloc_ceiling <= a -> 0 <= n -> a + n + 8 <= KHIGHMEM_END -> app_range a n.
Proof.
  intros a n H1 H2 H3. right. unfold highmem_range, KHIGHMEM_BEG, alloc_ceiling, sp_window_lo, stack_max_size in *. lia.
Qed.
Lemma wr_range_ok_stack : forall d n, alloc_ceiling <= d -> wr_range_ok d n.
Proof. intros d n H. apply wr_range_ok_high. unfold alloc_ceiling, sp_window_lo, stack_max_size in H. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma stk_lo_nonneg'' : forall segs m lo hi, stk segs m lo hi -> (0 <= lo)%Z.
Proof. intros segs m lo hi (H & _). exact H. Qed.

(* [comment removed for export] *)
Ltac name_sp' sp k :=
  let sp1 := fresh "sp" in let E := fresh "Esp" in let H := fresh "Hsp" in
  remember (Z_to_bv 64 (bv_unsigned sp + k)) as sp1 eqn:E;
  assert (H : bv_unsigned sp1 = (bv_unsigned sp + k)%Z)
    by (rewrite E; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *;
        try match goal with ST : stk _ _ _ _ |- _ => pose proof (stk_lo_nonneg'' _ _ _ _ ST) end;
        apply unsigned_lit; lia).
Ltac unname_sp' :=
  match goal with
  | H : bv_unsigned ?sp1 = (bv_unsigned ?sp + ?k)%Z, E : ?sp1' = Z_to_bv 64 (bv_unsigned ?sp + ?k) |- _ =>
      constr_eq sp1 sp1'; rewrite ?H in *; clear H; subst sp1
  end.
Tactic Notation "callsp" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt _ _ (MS (TNode _ None (TNode _ (Some (Z_to_bv 64 (bv_unsigned ?sp + ?k))) _)) _ _ _ _ _ _) =>
      name_sp' sp k; call SPEC; unname_sp'
  | |- evt _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?sp + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      name_sp' sp k; call SPEC; unname_sp'
  | _ => call SPEC
  end.

Lemma zb_u : forall w : word, Z_to_bv 64 (bv_unsigned w) = w.
Proof. intros w. apply Z_to_bv_bv_unsigned. Qed.

(* [comment removed for export] *)
Ltac name_spq e :=
  let sp1 := fresh "sp" in let E := fresh "Esp" in let H := fresh "Hsp" in
  remember (Z_to_bv 64 e) as sp1 eqn:E;
  assert (H : bv_unsigned sp1 = e)
    by (rewrite E; try match goal with ST : stk _ _ _ _ |- _ => pose proof (stk_lo_nonneg'' _ _ _ _ ST) end;
        apply unsigned_lit; lia).
Ltac unname_spq :=
  match goal with
  | H : bv_unsigned ?sp1 = ?e, E : ?sp1' = Z_to_bv 64 ?e' |- _ =>
      constr_eq sp1 sp1'; rewrite ?H in *; clear H; subst sp1
  end.
Tactic Notation "callq" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt _ _ (MS (TNode _ None (TNode _ (Some (Z_to_bv 64 ?e)) _)) _ _ _ _ _ _) =>
      name_spq e; call SPEC; unname_spq
  | |- evt _ _ (MS (mkR _ (Z_to_bv 64 ?e) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      name_spq e; call SPEC; unname_spq
  | _ => call SPEC
  end.

(* [comment removed for export] *)
Lemma memcpy_icpt_callZ : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D : Z) (src junk : list byte) (lo : Z),
  bytes_at asegs m (bv_unsigned a1) src ->
  length src = Z.to_nat (bv_unsigned a2) ->
  rw_cells asegs m D [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  (0 <= D < 2^64)%Z ->
  (bv_unsigned a1 + bv_unsigned a2 <= D \/ D + bv_unsigned a2 <= bv_unsigned a1)%Z ->
  mem_inv asegs m ->
  (* [comment removed for export] *)
  icpt_cells m -> stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + AINTRIN_STACK <= bv_unsigned sp ->
  bv_unsigned a2 < 2^40 -> app_range (bv_unsigned a1) (bv_unsigned a2) -> app_range D (bv_unsigned a2) -> wr_range_ok D (bv_unsigned a2) ->
  (0 < bv_unsigned a2 -> shadow_ok m (bv_unsigned a1) (bv_unsigned a2)) -> (0 < bv_unsigned a2 -> shadow_ok m D (bv_unsigned a2)) ->
  (bv_unsigned a1 + bv_unsigned a2 <= lo \/ bv_unsigned sp <= bv_unsigned a1) -> (D + bv_unsigned a2 <= lo \/ bv_unsigned sp <= D) ->
  evt asegs (memcpy_like_post AINTRIN_STACK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D (bv_unsigned a1) (bv_unsigned a2) src lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AMEMCPY_T) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros SRC LEN DST HD SEP MI IC ST CEIL SPB N40 ARs ARd WR SOs SOd SEPs SEPd.
  pose proof (bv_unsigned_in_range 64 a2) as R2.
  assert (LEN' : Z.of_nat (length src) = bv_unsigned a2) by (rewrite LEN; lia).
  rewrite <- (zb_u a1), <- (zb_u a2).
  eapply memcpy_icpt_ok; rewrite ?zb_u; eauto; try reflexivity; try lia.
Qed.

(* [comment removed for export] *)
Lemma memcpy_icpt_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D S N : Z) (src junk : list byte) (lo : Z),
  bytes_at asegs m S src -> Z.of_nat (length src) = N ->
  rw_cells asegs m D [CB (Z.to_nat N) junk] ->
  (S + N <= D \/ D + N <= S) ->
  (0 <= D)%Z -> (D + N < 2^64)%Z -> (0 <= S)%Z -> (S + N < 2^64)%Z ->
  mem_inv asegs m ->
  icpt_cells m -> stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + AINTRIN_STACK <= bv_unsigned sp ->
  N < 2^40 -> app_range S N -> app_range D N -> wr_range_ok D N ->
  (0 < N -> shadow_ok m S N) -> (0 < N -> shadow_ok m D N) ->
  (S + N <= lo \/ bv_unsigned sp <= S) -> (D + N <= lo \/ bv_unsigned sp <= D) ->
  evt asegs (memcpy_like_post AINTRIN_STACK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D S N src lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AMEMCPY_T) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros SRC LEN DST SEP HD1 HD2 HS1 HS2 MI IC ST CEIL SPB N40 ARs ARd WR SOs SOd SEPs SEPd.
  eapply memcpy_icpt_ok; eauto; lia.
Qed.

(* [comment removed for export] *)
Definition memset_like_postq (STK : Z) (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (d c n : Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(d, d + n); (q - STK, q)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' d [CB (Z.to_nat n) (repeat (Z_to_bv 8 (c mod 256)) (Z.to_nat n))]
    /\ stk asegs m' lo q.

Lemma memset_icpt_callZ : forall ra gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (q D N : Z) (junk : list byte) (lo : Z),
  rw_cells asegs m D [CB (Z.to_nat N) junk] ->
  mem_inv asegs m ->
  (0 <= D)%Z -> (0 <= N)%Z -> (D + N < 2^64)%Z -> (0 <= q < 2^64)%Z ->
  icpt_cells m -> stk asegs m lo q -> alloc_ceiling <= lo -> lo + AINTRIN_STACK <= q ->
  N < 2^40 -> app_range D N -> wr_range_ok D N -> (0 < N -> shadow_ok m D N) ->
  (D + N <= lo \/ q <= D) ->
  evt asegs (memset_like_postq AINTRIN_STACK ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D (bv_unsigned a1) N lo m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AMEMSET_T) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros DST MI HD HN HDN Hq IC ST CEIL SPB N40 AR WR SO SEP.
  assert (Eq : bv_unsigned (Z_to_bv 64 q : word) = q) by (apply unsigned_lit; lia).
  pose proof (bv_unsigned_in_range 64 a1) as R1. unfold bv_modulus in R1.
  pose proof (memset_icpt_ok ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 (Z_to_bv 64 N) a3 a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D (bv_unsigned a1) N junk lo) as H.
  rewrite !Eq, zb_u in H.
  eapply evt_mono.
  { eapply H; eauto; try reflexivity; try lia. }
  intros ms' P. unfold memset_like_post, memset_like_postq in *. rewrite !Eq in P. exact P.
Qed.

(* [comment removed for export] *)
Lemma memchr_icpt_callw : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (buf : list byte) (lo : Z),
  bytes_at asegs m (bv_unsigned a0) buf ->
  memchr_ok (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf ->
  mem_inv asegs m ->
  icpt_cells m -> stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + AINTRIN_STACK <= bv_unsigned sp ->
  bv_unsigned a2 < 2^40 -> app_range (bv_unsigned a0) (Z.of_nat (length buf)) ->
  (let len := memchr_chk_len (bv_unsigned a0) (bv_unsigned a1 mod 256) (bv_unsigned a2) buf in
   0 < len -> app_range (bv_unsigned a0) len /\ shadow_ok m (bv_unsigned a0) len) ->
  (bv_unsigned a0 + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
  evt asegs (memchr_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) buf lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AMEMCHR_T) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros BUF OK MI IC ST CEIL SPB N40 AR CHK SEP.
  pose proof (bv_unsigned_in_range 64 a1) as R1. unfold bv_modulus in R1.
  pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2.
  rewrite <- (zb_u a0), <- (zb_u a1), <- (zb_u a2).
  eapply memchr_icpt_ok; rewrite ?zb_u; eauto; try reflexivity; try lia.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac name_sp' sp k :=
  let sp1 := fresh "sp" in let E := fresh "Esp" in let H := fresh "Hsp" in
  remember (Z_to_bv 64 (bv_unsigned sp + k)) as sp1 eqn:E;
  assert (H : bv_unsigned sp1 = (bv_unsigned sp + k)%Z)
    by (rewrite E; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *;
        try match goal with ST : stk _ _ _ _ |- _ => pose proof (stk_lo_nonneg'' _ _ _ _ ST) end;
        apply unsigned_lit; lia).
Ltac unname_sp' :=
  match goal with
  | H : bv_unsigned ?sp1 = (bv_unsigned ?sp + ?k)%Z, E : ?sp1' = Z_to_bv 64 (bv_unsigned ?sp + ?k) |- _ =>
      constr_eq sp1 sp1'; rewrite ?H in *; clear H; subst sp1
  end.
Tactic Notation "callsp" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt _ _ (MS (TNode _ None (TNode _ (Some (Z_to_bv 64 (bv_unsigned ?sp + ?k))) _)) _ _ _ _ _ _) =>
      name_sp' sp k; call SPEC; unname_sp'
  | |- evt _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?sp + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      name_sp' sp k; call SPEC; unname_sp'
  | _ => call SPEC
  end.
Ltac name_spq e :=
  let sp1 := fresh "sp" in let E := fresh "Esp" in let H := fresh "Hsp" in
  remember (Z_to_bv 64 e) as sp1 eqn:E;
  assert (H : bv_unsigned sp1 = e)
    by (rewrite E; try match goal with ST : stk _ _ _ _ |- _ => pose proof (stk_lo_nonneg'' _ _ _ _ ST) end;
        apply unsigned_lit; lia).
Ltac unname_spq :=
  match goal with
  | H : bv_unsigned ?sp1 = ?e, E : ?sp1' = Z_to_bv 64 ?e' |- _ =>
      constr_eq sp1 sp1'; rewrite ?H in *; clear H; subst sp1
  end.
Tactic Notation "callq" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt _ _ (MS (TNode _ None (TNode _ (Some (Z_to_bv 64 ?e)) _)) _ _ _ _ _ _) =>
      name_spq e; call SPEC; unname_spq
  | |- evt _ _ (MS (mkR _ (Z_to_bv 64 ?e) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      name_spq e; call SPEC; unname_spq
  | _ => call SPEC
  end.
