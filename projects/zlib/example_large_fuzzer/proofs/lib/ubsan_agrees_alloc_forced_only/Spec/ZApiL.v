(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prelim ZApi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition Z_BEST_COMPRESSION : Z := 9.
Definition Z_NO_COMPRESSION : Z := 0.
Definition Z_DEFAULT_STRATEGY : Z := 0.
Definition Z_FILTERED : Z := 1.

(* [comment removed for export] *)
Definition ZL_MAX : Z := 524288.
(* [comment removed for export] *)
Definition NofL (size : Z) : Z := 100 + 3 * size.

Record zapiL : Type := mkZapiL {
  DSL : Type;                                  (* [comment removed for export] *)
  ISL : Type;                                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  zl_dstate : Z; zl_dwin : Z; zl_dprev : Z; zl_dhead : Z; zl_dpend : Z; zl_isize : Z; zl_wsize : Z;
  (* [comment removed for export] *)
  dl_init9 : DSL;                              (* [comment removed for export] *)
  dl_total_out : DSL -> Z;
  dl_deflate : list Z -> DSL -> Z -> Z -> DSL * Z * list Z * Z;
                                               (* [comment removed for export] *)
  dl_params : list Z -> DSL -> Z -> Z -> Z -> DSL * Z * list Z * Z;
                                               (* [comment removed for export] *)
  dl_end : DSL -> Z;                           (* [comment removed for export] *)
  (* [comment removed for export] *)
  il_init : ISL;                               (* [comment removed for export] *)
  il_total_in : ISL -> Z;
  il_total_out : ISL -> Z;
  il_wants_window : list Z -> ISL -> Z -> bool;  (* [comment removed for export] *)
  il_inflate : list Z -> ISL -> Z -> bool -> ISL * Z * list Z * Z;
                                               (* [comment removed for export] *)
  il_end : ISL -> Z                            (* [comment removed for export] *)
}.
