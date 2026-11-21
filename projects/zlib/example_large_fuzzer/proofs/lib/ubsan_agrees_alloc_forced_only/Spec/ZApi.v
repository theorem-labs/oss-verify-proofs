(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition Z_OK : Z := 0.
Definition Z_STREAM_END : Z := 1.
Definition Z_MEM_ERROR : Z := -4.
(* [comment removed for export] *)
Definition Z_NO_FLUSH : Z := 0.
Definition Z_FINISH : Z := 4.

(* [comment removed for export] *)
Definition ZH_MAX : Z := 1048576.

Record zapi : Type := mkZapi {
  DS : Type;                                   (* [comment removed for export] *)
  IS : Type;                                   (* [comment removed for export] *)
  z_bound : Z -> Z;                            (* [comment removed for export] *)
  (* [comment removed for export] *)
  z_dstate : Z;                                (* [comment removed for export] *)
  z_dwin : Z;                                  (* [comment removed for export] *)
  z_dprev : Z;                                 (* [comment removed for export] *)
  z_dhead : Z;                                 (* [comment removed for export] *)
  z_dpend : Z;                                 (* [comment removed for export] *)
  z_isize : Z;                                 (* [comment removed for export] *)
  z_wsize : Z;                                 (* [comment removed for export] *)
  (* [comment removed for export] *)
  d_init : DS;                                 (* [comment removed for export] *)
  d_total_in : DS -> Z;
  d_total_out : DS -> Z;
  d_deflate : list Z -> DS -> Z -> Z -> Z -> DS * Z * Z * list Z * Z;
                                               (* [comment removed for export] *)
  d_end : DS -> Z;                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  i_init : IS;                                 (* [comment removed for export] *)
  i_total_in : IS -> Z;
  i_total_out : IS -> Z;
  i_wants_window : list Z -> IS -> bool;       (* [comment removed for export] *)
  i_inflate : list Z -> IS -> Z -> Z -> bool -> IS * Z * Z * list Z * Z;
                                               (* [comment removed for export] *)
  i_end : IS -> Z                              (* [comment removed for export] *)
}.
