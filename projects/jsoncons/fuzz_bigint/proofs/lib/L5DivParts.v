(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreSpecs L5DivSpecs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module L5DIVP.
Import L5CS. Import L5DS.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Definition LTEST : Z := 0x221d4.
Definition LEXIT : Z := 0x2223c.
Definition DT0 : Z := 0x22290.
Definition RET : Z := 0x22348.

Definition apart (x lx y ly : Z) : Prop := x + lx <= y \/ y + ly <= x.
Definition inr (lo n a : Z) : Prop := lo <= a < lo + n.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition loop_kept : list nat := [3; 4; 9; 18; 20; 21; 22; 23; 27]%nat.

Definition divloop_run_stmt : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp this remd quotd denomd d : Z) (l n : nat),
    getr R (reg 2) = Z_to_bv 64 (sp - 304) -> getr R (reg 10) = Z_to_bv 64 remd -> getr R (reg 18) = Z_to_bv 64 this ->
    getr R (reg 20) = Z_to_bv 64 denomd -> getr R (reg 21) = Z_to_bv 64 (Z.of_nat l + 1) -> getr R (reg 22) = Z_to_bv 64 (Z.of_nat l) ->
    getr R (reg 23) = Z_to_bv 64 d -> getr R (reg 24) = Z_to_bv 64 quotd -> getr R (reg 26) = Z_to_bv 64 (Z.of_nat n) ->
    2 ^ 63 <= d < 2 ^ 64 -> (l <= n <= 299)%nat -> 0 <= this < 2 ^ 64 ->
    sp mod 16 = 0 -> 1048880 + 16 <= sp <= 2 ^ 47 ->
    (* [comment removed for export] *)
    remd mod 8 = 0 -> 4096 <= remd -> remd + 8 * (Z.of_nat n + 1) <= 2 ^ 47 ->
    L5.defined M remd (8 * (Z.of_nat n + 1)) -> L5.writable RSEGS M remd (8 * (Z.of_nat n + 1)) ->
    (* [comment removed for export] *)
    quotd mod 8 = 0 -> 4096 <= quotd -> quotd + 8 * (Z.of_nat n - Z.of_nat l) <= 2 ^ 47 ->
    L5.writable RSEGS M quotd (8 * (Z.of_nat n - Z.of_nat l)) ->
    (* [comment removed for export] *)
    denomd mod 8 = 0 -> 4096 <= denomd -> denomd + 8 * (Z.of_nat l + 1) <= 2 ^ 47 -> L5.defined M denomd (8 * (Z.of_nat l + 1)) ->
    (* [comment removed for export] *)
    L5.writable RSEGS M (sp - 320) 320 -> L5.defined M (sp - 248) 8 ->
    (* [comment removed for export] *)
    apart remd (8 * (Z.of_nat n + 1)) (sp - 320) 320 -> apart quotd (8 * (Z.of_nat n - Z.of_nat l)) (sp - 320) 320 ->
    apart remd (8 * (Z.of_nat n + 1)) quotd (8 * (Z.of_nat n - Z.of_nat l)) ->
    apart remd (8 * (Z.of_nat n + 1)) denomd (8 * (Z.of_nat l + 1)) ->
    apart quotd (8 * (Z.of_nat n - Z.of_nat l)) denomd (8 * (Z.of_nat l + 1)) ->
    apart denomd (8 * (Z.of_nat l + 1)) (sp - 248) 8 -> apart denomd (8 * (Z.of_nat l + 1)) (sp - 320) 16 ->
    exists (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte),
      msteps RSEGS (st fx R LTEST M) (st fx' R' LEXIT M')
      /\ getr R' (reg 2) = Z_to_bv 64 (sp - 304)
      /\ (forall i, In i loop_kept -> getr R' (reg i) = getr R (reg i))
      /\ (forall a : word, ~ inr remd (8 * (Z.of_nat n + 1)) (bv_unsigned a) -> ~ inr quotd (8 * (Z.of_nat n - Z.of_nat l)) (bv_unsigned a) ->
                           ~ inr (sp - 248) 8 (bv_unsigned a) -> ~ inr (sp - 320) 16 (bv_unsigned a) -> M' a = M a)
      /\ mem_grows M M'.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition local_obj (M : word -> option byte) (o : Z) (f c p : Z) : Prop :=
  L5.u8_at RSEGS M o f /\ 0 <= f < 256 /\
  (Z.testbit f 0 = true -> L5.u64_at RSEGS M (o + 16) c /\ 1 <= c <= 4096 /\ L5.u64_at RSEGS M (o + 24) p /\ 4096 <= p /\ p + 8 * c <= 2 ^ 47).
(* [comment removed for export] *)
Definition lb_free (f p : Z) (LB : list (Z * Z)) : list (Z * Z) := if Z.testbit f 0 then lb_remove p LB else LB.

Definition divtail_stmt (L : heap_layout) (HI : heap_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBc : list (Z * Z)) (crc : credit) (sp : Z) (Rs : bvmap 5 word)
         (f0 c0 p0 f1 c1 p1 f2 c2 p2 f3 c3 p3 : Z),
    hi_heap HI LBc crc M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R (reg 2) = Z_to_bv 64 (sp - 304) -> getr R (reg 4) = Z_to_bv 64 TP ->
    L5C.stk (hl_sptop L) M (sp - 304) OPDEL_SCR -> sp <= hl_sptop L -> L5.defined M (sp - 304) 304 ->
    div_saves M sp Rs -> L5.ra_ok (U Rs 1) ->
    local_obj M (sp - 232) f0 c0 p0 -> local_obj M (sp - 200) f1 c1 p1 -> local_obj M (sp - 168) f2 c2 p2 -> local_obj M (sp - 136) f3 c3 p3 ->
    let LB1 := lb_free f0 p0 LBc in let LB2 := lb_free f1 p1 LB1 in let LB3 := lb_free f2 p2 LB2 in let LB4 := lb_free f3 p3 LB3 in
    (Z.testbit f0 0 = true -> In (p0, 8 * c0) LBc) -> (Z.testbit f1 0 = true -> In (p1, 8 * c1) LB1) ->
    (Z.testbit f2 0 = true -> In (p2, 8 * c2) LB2) -> (Z.testbit f3 0 = true -> In (p3, 8 * c3) LB3) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        getr R' (reg 2) = Z_to_bv 64 sp -> getr R' (reg 3) = getr R (reg 3) -> getr R' (reg 4) = getr R (reg 4) ->
        (forall i, In i [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (reg i) = getr Rs (reg i)) ->
        L5C.hpres L LB4 (sp - 304) OPDEL_SCR [] M M' ->
        model_but_vm model model' -> hi_heap HI LB4 crc M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' (U Rs 1) M' model') K) ->
    srealizes RSEGS SCFG (cfg R DT0 M model) K.

End SCFG_1.
End L5DIVP.
