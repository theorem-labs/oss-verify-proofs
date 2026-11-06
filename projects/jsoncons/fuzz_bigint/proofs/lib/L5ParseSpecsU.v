(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface
     BigModel BigFactsRun BigFactsDigits L5Defs L5Core L5CoreSpecsU.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5PSU.
Import L5CSU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Definition GP : Z := 67584.              (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition digits_ok (ds : list Z) : Prop := Forall (fun c => 48 <= c <= 57) ds.
(* [comment removed for export] *)
Definition split_sign (s : list Z) : bool * list Z :=
  match s with c :: t => if Z.eqb c 45 then (true, t) else (false, s) | [] => (false, []) end.
(* [comment removed for export] *)
Definition parses (s : list Z) : Prop := (1 <= length (snd (split_sign s)))%nat /\ digits_ok (snd (split_sign s)).
Definition no_parse (s : list Z) : Prop := length (snd (split_sign s)) = 0%nat \/ ~ digits_ok (snd (split_sign s)).

(* [comment removed for export] *)
Definition vblk (m : nat) : Z := if (m <? 39)%nat then 64 else 8 * Z.of_nat (BigModel.round_up (num_words_est m)).
Definition parse_credit (L : heap_layout) (cr : credit) (m : nat) : Prop :=
  credit_ok L cr (vblk m) /\ credit_ok L (debit L cr (vblk m)) (vblk m).
(* [comment removed for export] *)
Definition parse_debit (L : heap_layout) (cr : credit) (m : nat) : credit := debit L (debit L cr (vblk m)) (vblk m).

(* [comment removed for export] *)
Definition res_fb (fb : Z) (n : nat) (neg : bool) : Z :=
  fb + (if (3 <=? n)%nat then 1 else 0) + (if (neg && (1 <=? n)%nat)%bool then 2 else 0).

(* [comment removed for export] *)
Definition digits_at (L : heap_layout) (LB : list (Z * Z)) (sp p : Z) (m : nat) : Prop :=
  m = 0%nat
  \/ (exists A k, In (A, k) LB /\ A <= p /\ p + Z.of_nat m <= A + k)
  \/ (sp <= p /\ p + Z.of_nat m <= hl_sptop L)
  \/ (0x10000 <= p /\ p + Z.of_nat m <= 0x20000).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition DETAIL : Z := 0x20ea4.
Definition DETAIL_SCR : Z := 112 + ADDD_SCR.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition parse_post (L : heap_layout) (LB : list (Z * Z)) (cr : credit) (M M' : word -> option byte)
           (o sp fb : Z) (neg : bool) (ds : list Z) (SCR : Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  let V := dec ds in let n := nwords V in
  exists st',
    L5.big_at RSEGS M' o (L5.BO (res_fb fb n neg) n st') /\ L5C.obj_limbs RSEGS M' (L5.BO (res_fb fb n neg) n st') (wlist V n)
    /\ match st' with
       | L5.BInl _ _ => (n <= 2)%nat /\ LB' = LB
       | L5.BDyn cap A => (3 <= n)%nat /\ cap = Z.of_nat (BigModel.round_up n) /\ LB' = (A, 8 * cap) :: LB /\ L5C.fresh_block L LB M' A (8 * cap)
       end
    /\ credit_le (parse_debit L cr (length ds)) cr'
    /\ L5C.hpres L LB sp SCR [(o, 32)] M M'.

(* [comment removed for export] *)
Definition noparse_post (L : heap_layout) (LB : list (Z * Z)) (cr : credit) (M M' : word -> option byte)
           (o sp fb : Z) (m : nat) (SCR : Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  LB' = LB /\ L5.big_at RSEGS M' o (L5.BO fb 0 (L5.BInl 0 0))
  /\ credit_le (parse_debit L cr m) cr'
  /\ L5C.hpres L LB sp SCR [] M M'.

Definition detail_post (L : heap_layout) (LB : list (Z * Z)) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (o sp fb : Z) (neg : bool) (ds : list Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R' /\
  ( ((1 <= length ds)%nat /\ digits_ok ds /\ getr R' 11%bv = Z_to_bv 64 0 /\ parse_post L LB cr M M' o sp fb neg ds DETAIL_SCR LB' cr')
  \/ ((length ds = 0%nat \/ ~ digits_ok ds) /\ getr R' 11%bv = Z_to_bv 64 22 /\ noparse_post L LB cr M M' o sp fb (length ds) DETAIL_SCR LB' cr') ).

Definition detail_spec (L : heap_layout) (HI : heap_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (p o sp r fb : Z) (neg : bool) (ds : list Z),
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 (Z.of_nat (length ds)) ->
    getr R 12%bv = Z_to_bv 64 (if neg then 1 else 0) -> getr R 13%bv = Z_to_bv 64 o ->
    (length ds <= 4999)%nat -> parse_credit L cr (length ds) ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 3%bv = Z_to_bv 64 GP -> getr R 4%bv = Z_to_bv 64 TP ->
    L5C.stk (hl_sptop L) M sp DETAIL_SCR ->
    (* [comment removed for export] *)
    L5.big_at RSEGS M o (L5.BO fb 0 (L5.BInl 0 0)) -> Z.land fb 3 = 0 ->
    o mod 8 = 0 -> sp <= o -> o + 32 <= hl_sptop L -> L5.writable RSEGS M o 32 ->
    (* [comment removed for export] *)
    L5.bytes_at RSEGS M p ds -> Forall (fun c => 0 <= c < 256) ds -> 4096 <= p -> p + Z.of_nat (length ds) <= 2 ^ 47 ->
    digits_at L LB sp p (length ds) -> (p + Z.of_nat (length ds) <= o \/ o + 32 <= p) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
        detail_post L LB cr M M' R R' o sp fb neg ds LB' cr' ->
        model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R DETAIL M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition TOBIG3 : Z := 0x22268.
Definition TOBIG4 : Z := 0x20e40.
Definition TOBIG_SCR : Z := 16 + DETAIL_SCR.

Definition tobig_post (L : heap_layout) (LB : list (Z * Z)) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (o sp fb : Z) (s : list Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  let neg := fst (split_sign s) in let ds := snd (split_sign s) in
  regs_preserved R R' /\
  ( (parses s /\ getr R' 11%bv = Z_to_bv 64 0 /\ parse_post L LB cr M M' o sp fb neg ds TOBIG_SCR LB' cr')
  \/ (no_parse s /\ getr R' 11%bv = Z_to_bv 64 22 /\ noparse_post L LB cr M M' o sp fb (length ds) TOBIG_SCR LB' cr') ).

Definition tobig_spec_at (pc : Z) (oreg : bv 5) (L : heap_layout) (HI : heap_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (p o sp r fb : Z) (s : list Z),
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 (Z.of_nat (length s)) -> getr R oreg = Z_to_bv 64 o ->
    (length s <= 4999)%nat -> parse_credit L cr (length (snd (split_sign s))) ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 3%bv = Z_to_bv 64 GP -> getr R 4%bv = Z_to_bv 64 TP ->
    L5C.stk (hl_sptop L) M sp TOBIG_SCR ->
    L5.big_at RSEGS M o (L5.BO fb 0 (L5.BInl 0 0)) -> Z.land fb 3 = 0 ->
    o mod 8 = 0 -> sp <= o -> o + 32 <= hl_sptop L -> L5.writable RSEGS M o 32 ->
    L5.bytes_at RSEGS M p s -> Forall (fun c => 0 <= c < 256) s -> 4096 <= p -> p + Z.of_nat (length s) <= 2 ^ 47 ->
    digits_at L LB sp p (length s) -> (p + Z.of_nat (length s) <= o \/ o + 32 <= p) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
        tobig_post L LB cr M M' R R' o sp fb s LB' cr' ->
        model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R pc M model) K.
Definition tobig3_spec := tobig_spec_at TOBIG3 12%bv.     (* [comment removed for export] *)
Definition tobig4_spec := tobig_spec_at TOBIG4 12%bv.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CSTR : Z := 0x20b4c.
Definition CSTR_SCR : Z := 32 + TOBIG_SCR.
Definition ALIT : Z := 0x127ab.
Definition A0 : Z := 0x16af9c0daf145395.
Definition A1 : Z := 0x2a9f3636273caaf2.
Definition alit_digits : list Z := [53;54;54;53;52;50;53;48;53;54;52;48;53;54;49;51;53;52;49;53;54;51;49;53;53;52;53;51;49;53;53;52;53;49;51;56;49;51].

Definition cstr_post (L : heap_layout) (LB : list (Z * Z)) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (o sp fbo : Z) (cr' : credit) : Prop :=
  regs_preserved R R' /\
  L5.big_at RSEGS M' o (L5.BO (Z.land fbo 252) 2 (L5.BInl A0 A1)) /\
  credit_le (parse_debit L cr 38) cr' /\
  L5C.hpres L LB sp CSTR_SCR [(o, 32)] M M'.

Definition cstr_spec (L : heap_layout) (HI : heap_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (o sp r fbo : Z),
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 ALIT -> parse_credit L cr 38 ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 3%bv = Z_to_bv 64 GP -> getr R 4%bv = Z_to_bv 64 TP ->
    L5C.stk (hl_sptop L) M sp CSTR_SCR -> L5.img_clear M 0x10000 0x20000 ->
    (* [comment removed for export] *)
    L5.u8_at RSEGS M o fbo -> 0 <= fbo < 256 ->
    o mod 8 = 0 -> sp <= o -> o + 32 <= hl_sptop L -> L5.writable RSEGS M o 32 ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) cr',
        cstr_post L LB cr M M' R R' o sp fbo cr' ->
        model_but_vm model model' -> hi_heap HI LB cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R CSTR M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STRCTOR : Z := 0x20c1c.
Definition STRCTOR_RET : Z := 0x20838.
Definition E1_LANDING : Z := 0x20a0c.
Definition STRCTOR_SCR : Z := 32 + TOBIG_SCR.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition EH_CAUGHT : Z := 0x703f8.      (* [comment removed for export] *)
Definition EH_UNCAUGHT : Z := 0x70400.    (* [comment removed for export] *)
Definition SYSCAT_GUARD : Z := 0x70620.   (* [comment removed for export] *)
Definition UW_FLAGS : Z := 0x70e61.       (* [comment removed for export] *)
Definition TD_LOCALE : Z := 0x70f08.      (* [comment removed for export] *)
Definition GLOBAL_LOCALE : Z := 0x91200.
Definition LOCALE_MSGCAT : Z := 0x91228. (* [comment removed for export] *)
Definition ERRNO : Z := 0x70e94.
Definition CANARY : Z := 0x911a8.         (* [comment removed for export] *)
Definition AUXVP : Z := 0x911d0.          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition auxv20 (uid rnd hw : Z) : list Z := [3; 0x10040; 4; 56; 5; 10; 16; hw; 6; 4096; 11; uid; 12; uid; 23; 0; 25; rnd; 0; 0].

(* [comment removed for export] *)
Definition e1_statics (M : word -> option byte) (gd fl : bool) (av uid rnd canary hw : Z) : Prop :=
     L5.u64_at RSEGS M EH_CAUGHT 0 /\ L5.u32_at RSEGS M EH_UNCAUGHT 0
  /\ L5.u8_at RSEGS M SYSCAT_GUARD (if gd then 1 else 0) /\ L5.u8_at RSEGS M (SYSCAT_GUARD + 1) (if gd then 1 else 0)
  /\ (if fl then L5.u8_at RSEGS M UW_FLAGS 1 /\ L5.u8_at RSEGS M (UW_FLAGS + 1) 0 /\ L5.u8_at RSEGS M (UW_FLAGS + 2) 1
             /\ L5.u8_at RSEGS M (UW_FLAGS + 3) 0 /\ L5.u8_at RSEGS M (UW_FLAGS + 4) 1 /\ L5.u8_at RSEGS M (UW_FLAGS + 5) 0
      else L5.u8_at RSEGS M UW_FLAGS 0 /\ L5.u8_at RSEGS M (UW_FLAGS + 2) 0 /\ L5.u8_at RSEGS M (UW_FLAGS + 4) 0)
  /\ L5.u64_at RSEGS M TD_LOCALE GLOBAL_LOCALE /\ L5.u64_at RSEGS M LOCALE_MSGCAT 0
  /\ L5.u64_at RSEGS M CANARY canary /\ L5.u64_at RSEGS M AUXVP av /\ av mod 8 = 0 /\ 2 ^ 40 <= av /\ av + 160 <= 2 ^ 47
  /\ (forall j, (j < 20)%nat -> L5.u64_at RSEGS M (av + 8 * Z.of_nat j) (nth j (auxv20 uid rnd hw) 0))
  /\ 0 <= uid < 2 ^ 64 /\ 0 <= rnd < 2 ^ 64 /\ 0 <= canary < 2 ^ 64 /\ 0 <= hw < 2 ^ 64
  (* [comment removed for export] *)
  /\ L5.img_clear M 0x10000 0x60100 /\ L5.img_clear M 0x60128 0x60148 /\ L5.img_clear M 0x60158 0x60160.

(* [comment removed for export] *)
Definition e1_statics_landed (M : word -> option byte) (av uid rnd canary hw : Z) : Prop :=
     L5.u64_at RSEGS M EH_CAUGHT 0 /\ L5.u32_at RSEGS M EH_UNCAUGHT 1
  /\ L5.u8_at RSEGS M SYSCAT_GUARD 1 /\ L5.u8_at RSEGS M (SYSCAT_GUARD + 1) 1
  /\ L5.u8_at RSEGS M UW_FLAGS 1 /\ L5.u8_at RSEGS M (UW_FLAGS + 1) 0 /\ L5.u8_at RSEGS M (UW_FLAGS + 2) 1
  /\ L5.u8_at RSEGS M (UW_FLAGS + 3) 0 /\ L5.u8_at RSEGS M (UW_FLAGS + 4) 1 /\ L5.u8_at RSEGS M (UW_FLAGS + 5) 0
  /\ L5.u64_at RSEGS M TD_LOCALE GLOBAL_LOCALE /\ L5.u64_at RSEGS M LOCALE_MSGCAT 0
  /\ L5.u64_at RSEGS M CANARY canary /\ L5.u64_at RSEGS M AUXVP av
  /\ (forall j, (j < 20)%nat -> L5.u64_at RSEGS M (av + 8 * Z.of_nat j) (nth j (auxv20 uid rnd hw) 0))
  /\ L5.img_clear M 0x10000 0x60100 /\ L5.img_clear M 0x60128 0x60148 /\ L5.img_clear M 0x60158 0x60160.

(* [comment removed for export] *)
Definition TI_SYSTEM_ERROR : Z := 0x5ee28.     (* [comment removed for export] *)
Definition DTOR_SYSTEM_ERROR : Z := 0x41e44.   (* [comment removed for export] *)
Definition VT_SYSTEM_ERROR : Z := 0x5ee10.     (* [comment removed for export] *)
Definition SYSCAT_OBJ : Z := 0x60158.          (* [comment removed for export] *)
Definition UNEXPECTED_H : Z := 0x23974.
Definition TERMINATE_H : Z := 0x23868.
Definition E1_ACTION : Z := 0x1675b.           (* [comment removed for export] *)
Definition E1_LSDA : Z := 0x166d0.
Definition UE_CLEANUP : Z := 0x3f954.          (* [comment removed for export] *)
Definition EXC_CLASS : Z := 0x434c4e47432b2b00.  (* [comment removed for export] *)

Definition e1_exception_at (M : word -> option byte) (obj ref spL : Z) : Prop :=
  (* [comment removed for export] *)
     (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M (obj - 128 + i) 0)            (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M (obj - 120) 1                                         (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M (obj - 112) TI_SYSTEM_ERROR /\ L5.u64_at RSEGS M (obj - 104) DTOR_SYSTEM_ERROR
  /\ L5.u64_at RSEGS M (obj - 96) UNEXPECTED_H /\ L5.u64_at RSEGS M (obj - 88) TERMINATE_H
  /\ (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M (obj - 80 + i) 0)            (* [comment removed for export] *)
  /\ L5.u32_at RSEGS M (obj - 68) 1                                          (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M (obj - 64) E1_ACTION /\ L5.u64_at RSEGS M (obj - 56) E1_LSDA /\ L5.u64_at RSEGS M (obj - 48) E1_LANDING
  /\ L5.u64_at RSEGS M (obj - 40) obj                                        (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M (obj - 32) EXC_CLASS /\ L5.u64_at RSEGS M (obj - 24) UE_CLEANUP /\ L5.u64_at RSEGS M (obj - 16) 0
  /\ L5.u64_at RSEGS M (obj - 8) spL                                         (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M obj VT_SYSTEM_ERROR /\ L5.u64_at RSEGS M (obj + 8) (ref + 24)
  /\ L5.u32_at RSEGS M (obj + 16) 22 /\ L5.u64_at RSEGS M (obj + 24) SYSCAT_OBJ
  (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M ref 16 /\ L5.u64_at RSEGS M (ref + 8) 16 /\ L5.u32_at RSEGS M (ref + 16) 0
  /\ L5.bytes_at RSEGS M (ref + 24) [73;110;118;97;108;105;100;32;97;114;103;117;109;101;110;116;0].

(* [comment removed for export] *)
Definition e1_landing (L : heap_layout) (LB : list (Z * Z)) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (o sp fbo : Z) (m : nat) (av uid rnd canary hw : Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  exists obj ref,
     regs_preserved R R'                                                      (* [comment removed for export] *)
  /\ getr R' 10%bv = Z_to_bv 64 (obj - 32) /\ getr R' 11%bv = Z_to_bv 64 1   (* [comment removed for export] *)
  /\ LB' = (ref, 41) :: (obj - 128, 160) :: LB /\ credit_le (debit L (debit L (parse_debit L cr m) 160) 41) cr'   (* [comment removed for export] *)
  /\ L5C.fresh_block L LB M' (obj - 128) 160 /\ L5C.fresh_block L ((obj - 128, 160) :: LB) M' ref 41
  /\ e1_exception_at M' obj ref sp
  /\ e1_statics_landed M' av uid rnd canary hw
  /\ L5.big_at RSEGS M' o (L5.BO (Z.land fbo 252) 0 (L5.BInl 0 0))           (* [comment removed for export] *)
  /\ L5C.hpres L LB sp STRCTOR_SCR [(o, 32); (EH_UNCAUGHT, 4); (SYSCAT_GUARD, 2); (UW_FLAGS, 6)] M M'.

Definition strctor_post (L : heap_layout) (LB : list (Z * Z)) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (o sp fbo : Z) (s : list Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  let neg := fst (split_sign s) in let ds := snd (split_sign s) in
  regs_preserved R R' /\ parses s /\ parse_post L LB cr M M' o sp (Z.land fbo 252) neg ds STRCTOR_SCR LB' cr'.

Definition strctor_spec (L : heap_layout) (HI : heap_iface) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (o so sp fbo : Z) (s : list Z) (gd fl : bool) (av uid rnd canary hw : Z),
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 so ->
    (length s <= 4999)%nat -> Forall (fun c => 0 <= c < 256) s ->
    parse_credit L cr (length (snd (split_sign s))) ->
    credit_ok L (parse_debit L cr (length (snd (split_sign s)))) 160 -> credit_ok L (debit L (parse_debit L cr (length (snd (split_sign s)))) 160) 41 ->
    getr R 1%bv = Z_to_bv 64 STRCTOR_RET ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 3%bv = Z_to_bv 64 GP -> getr R 4%bv = Z_to_bv 64 TP ->
    L5C.stk (hl_sptop L) M sp STRCTOR_SCR ->
    (* [comment removed for export] *)
    L5.u8_at RSEGS M o fbo -> 0 <= fbo < 256 ->
    o mod 8 = 0 -> sp <= o -> o + 32 <= hl_sptop L -> L5.writable RSEGS M o 32 ->
    (* [comment removed for export] *)
    so mod 8 = 0 -> sp <= so -> so + 24 <= hl_sptop L -> (o + 32 <= so \/ so + 24 <= o) ->
    ( L5.lstr_short RSEGS M so s
      \/ (exists w0 pd, L5.lstr_long RSEGS M so s w0 pd /\ In (pd, w0 - 1) LB /\ Z.of_nat (length s) + 1 <= w0 - 1 /\ 0 <= w0 < 2 ^ 64) ) ->
    (* [comment removed for export] *)
    e1_statics M gd fl av uid rnd canary hw -> hl_sptop L <= av ->     (* [comment removed for export] *)
    (* [comment removed for export] *)
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
        strctor_post L LB cr M M' R R' o sp fbo s LB' cr' ->
        e1_statics M' gd fl av uid rnd canary hw ->
        model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' STRCTOR_RET M' model') K) ->
    (* [comment removed for export] *)
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
        no_parse s ->
        e1_landing L LB cr M M' R R' o sp fbo (length (snd (split_sign s))) av uid rnd canary hw LB' cr' ->
        model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' E1_LANDING M' model') K) ->
    srealizes RSEGS SCFG (cfg R STRCTOR M model) K.
End SCFG_1.


End L5PSU.
