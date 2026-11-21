(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateParams.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateSafe RefDeflateRel RefDeflSafeL1 RefDeflSafeI1 RefDeflSafeI4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition params_legal (level strategy : Z) : Prop := 0 <= level <= 9 /\ 0 <= strategy <= Z_FIXED.

(* [comment removed for export] *)
Definition PQ (s : deflate_state) : Prop :=
  (ds_match_available s = 0 /\ ds_sym_next s = 0) \/ 1 <= ds_strstart s - ds_block_start s.

(* [comment removed for export] *)
Definition PRI (s : deflate_state) : Prop :=
  ds_lookahead s = 0 /\ ds_strstart s = 0 /\ ds_block_start s = 0 /\ ds_sym_next s = 0 /\ ds_match_available s = 0 /\ ds_match_length s = 2.

(* [comment removed for export] *)
Definition ZLS (s : deflate_state) : Prop :=
  (dmode s = 0 ->
     ds_match_length s = 2
     /\ (ds_matches s = 0 -> CHAIN s (ds_strstart s - 1) (ds_strstart s - 1))
     /\ (ds_matches s = 1 -> CHAIN s (ds_strstart s + ds_w_size s - 1) (ds_strstart s + ds_w_size s - 1)))
  /\ (dmode s = 4 -> PQ s)
  /\ (ds_last_flush s = -2 -> PRI s).

(* [comment removed for export] *)
Definition lv (s : deflate_state) : Z * Z * Z := (ds_level s, ds_strategy s, ds_last_flush s).

Lemma dmode_lv : forall a b, lv b = lv a -> dmode b = dmode a.
Proof. intros a b E. unfold lv in E. injection E as E1 E2 E3. unfold dmode. rewrite E1, E2. reflexivity. Qed.

(* [comment removed for export] *)
Definition zl_modes (s : deflate_state) : Prop := (dmode s = 0 \/ dmode s = 4) /\ (ds_strategy s = 0 \/ ds_strategy s = 1).
Definition zl_side (s : deflate_state) (level : Z) : Prop := zl_modes s /\ (cfunc_id level = 0 \/ cfunc_id level = 2).

(* [comment removed for export] *)
Definition dparams_DD_stmt : Prop :=
  forall s zc level strategy,
    DD s -> ZLS s -> dcall_wf zc -> params_legal level strategy -> (strategy = 0 \/ strategy = 1) -> zl_side s level ->
    DD (fst (deflateParams_m s zc level strategy)) /\ ZLS (fst (deflateParams_m s zc level strategy)).

(* [comment removed for export] *)
Definition deflate_ZLS_stmt : Prop :=
  forall s zc flush, DD s -> ZLS s -> dcall_wf zc -> (flush = Z_NO_FLUSH \/ flush = Z_FINISH \/ flush = Z_BLOCK) -> zl_modes s ->
    ZLS (fst (deflate_m s zc flush)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma ZLS_load : forall s c, ZLS s -> ZLS (set_strm s c).
Proof. intros s c H. exact H. Qed.

Lemma zl_modes_lv : forall a b, lv b = lv a -> zl_modes a -> zl_modes b.
Proof. intros a b E H. unfold zl_modes in *. rewrite (dmode_lv a b E). unfold lv in E. injection E as E1 E2 E3. rewrite E2. exact H. Qed.

Lemma PQ_of_fields : forall s s',
  ds_match_available s' = ds_match_available s -> ds_sym_next s' = ds_sym_next s ->
  ds_strstart s' - ds_block_start s' = ds_strstart s - ds_block_start s -> PQ s -> PQ s'.
Proof. intros s s' E1 E2 E3 H. unfold PQ in *. rewrite E1, E2, E3. exact H. Qed.
