(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import InitMem Z_kit Z_dview Z_drep Z_dkit Z_defl_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState DeflateLz DeflateBlk Deflate DeflateParams.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition ZL_CFG_TABLE : Z := 0x29238.
Definition ZL_DEFLATE_STORED : Z := 0x1802c.
Definition ZL_DEFLATE_FAST : Z := 0x191d4.
Definition ZL_DEFLATE_SLOW : Z := 0x1985c.

Definition cfunc_addr (l : Z) : Z :=
  if l =? 0 then ZL_DEFLATE_STORED else if l <=? 3 then ZL_DEFLATE_FAST else ZL_DEFLATE_SLOW.

Lemma cfunc_addr_eqb : forall a b, (cfunc_addr a =? cfunc_addr b) = (cfunc_id a =? cfunc_id b).
Proof.
  intros a b. unfold cfunc_addr, cfunc_id, ZL_DEFLATE_STORED, ZL_DEFLATE_FAST, ZL_DEFLATE_SLOW.
  destruct (a =? 0); [| destruct (a <=? 3)]; (destruct (b =? 0); [| destruct (b <=? 3)]); reflexivity.
Qed.

Lemma cfunc_addr_cases : forall l, cfunc_addr l = ZL_DEFLATE_STORED \/ cfunc_addr l = ZL_DEFLATE_FAST \/ cfunc_addr l = ZL_DEFLATE_SLOW.
Proof. intros l. unfold cfunc_addr. destruct (l =? 0); [tauto|]. destruct (l <=? 3); tauto. Qed.

(* [comment removed for export] *)
Local Ltac relro_cell8 RC b v :=
  let cs := constr:([C8 (wz v)]) in
  apply (InitMem.rw_cells_recast psegs _ b [CB 8 (cells_bytes cs)] cs);
  [ apply (InitMem.rw_cells_image0 psegs _ b (cells_bytes cs));
    [ intros x Hx; apply RC; change (Z.of_nat (length (cells_bytes cs))) with 8 in Hx; lia
    | vm_compute; reflexivity | lia | change (Z.of_nat (length (cells_bytes cs))) with 8; lia ]
  | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ].

Lemma cfgL_func : forall m l, relro_clean m -> 0 <= l <= 9 -> rw_cells psegs m (ZL_CFG_TABLE + 16 * l + 8) [C8 (wz (cfunc_addr l))].
Proof.
  intros m l RC Hl. unfold relro_clean, RELRO_LO, RELRO_HI in RC. unfold ZL_CFG_TABLE, cfunc_addr, ZL_DEFLATE_STORED, ZL_DEFLATE_FAST, ZL_DEFLATE_SLOW.
  assert (C : l = 0 \/ l = 1 \/ l = 2 \/ l = 3 \/ l = 4 \/ l = 5 \/ l = 6 \/ l = 7 \/ l = 8 \/ l = 9) by lia.
  destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]; cbn [Z.mul Z.add Z.eqb Z.leb Pos.mul Pos.add Pos.eqb Pos.leb Pos.compare Pos.compare_cont];
  lazymatch goal with |- rw_cells _ _ ?b [C8 (wz ?v)] => relro_cell8 RC b v end.
Qed.

(* [comment removed for export] *)
Definition cfg_row_cells (l : Z) : list cell :=
  let '(good, lazy, nice, chain) := configuration_table l in [C2 (wz good); C2 (wz lazy); C2 (wz nice); C2 (wz chain)].

Local Ltac relro_cell_row RC b cs :=
  apply (InitMem.rw_cells_recast psegs _ b [CB 8 (cells_bytes cs)] cs);
  [ apply (InitMem.rw_cells_image0 psegs _ b (cells_bytes cs));
    [ intros x Hx; apply RC; change (Z.of_nat (length (cells_bytes cs))) with 8 in Hx; lia
    | vm_compute; reflexivity | lia | change (Z.of_nat (length (cells_bytes cs))) with 8; lia ]
  | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ].

Lemma cfgL_row : forall m l, relro_clean m -> 0 <= l <= 9 -> rw_cells psegs m (ZL_CFG_TABLE + 16 * l) (cfg_row_cells l).
Proof.
  intros m l RC Hl. unfold relro_clean, RELRO_LO, RELRO_HI in RC. unfold ZL_CFG_TABLE, cfg_row_cells.
  assert (C : l = 0 \/ l = 1 \/ l = 2 \/ l = 3 \/ l = 4 \/ l = 5 \/ l = 6 \/ l = 7 \/ l = 8 \/ l = 9) by lia.
  destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]; cbn [configuration_table Z.mul Z.add Pos.mul Pos.add];
  lazymatch goal with |- rw_cells _ _ ?b ?cs => relro_cell_row RC b cs end.
Qed.

(* [comment removed for export] *)
Lemma strm_slide_hash : forall s, ds_strm (slide_hash s) = ds_strm s. Proof. reflexivity. Qed.
Lemma strm_clear_hash : forall s, ds_strm (clear_hash s) = ds_strm s. Proof. reflexivity. Qed.

Lemma dparams_strm : forall s level strategy, ds_strm (set_strategy (dparams_set_level s level) strategy) = ds_strm s.
Proof.
  intros s level strategy. unfold dparams_set_level.
  destruct (configuration_table level) as [[[good lazy] nice] chain].
  destruct ((ds_level s =? 0) && negb (ds_matches s =? 0)); [destruct (ds_matches s =? 1)|]; reflexivity.
Qed.
