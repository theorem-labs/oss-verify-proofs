(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface
  L5Defs L5Core L5CoreSpecs L5DivSpecs L5ParseSpecs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto.

Module L5US.
Import L5CS.
Abbreviation RSEGS := Plain.M.loaded_segments.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition GP : Z := 67584.
Definition TOP_PAD : Z := 0x20798.        (* [comment removed for export] *)
Definition E1_LANDING : Z := 0x2073c.     (* [comment removed for export] *)
Definition CATCH : Z := 0x20810.          (* [comment removed for export] *)
Definition CATCH_E : Z := 0x20814.        (* [comment removed for export] *)
Definition CATCH_RET : Z := 0x20818.      (* [comment removed for export] *)
Definition ZERO_THROW : Z := 0x22350.     (* [comment removed for export] *)
Definition ASSERT_THROW : Z := 0x21470.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition UNEXPECTED_H : Z := 0x22e78.   (* [comment removed for export] *)
Definition TERMINATE_H : Z := 0x22d6c.    (* [comment removed for export] *)
Definition EXC_ACTION : Z := 0x16633.     (* [comment removed for export] *)
Definition EXC_LSDA : Z := 0x165a8.       (* [comment removed for export] *)
Definition UE_CLEANUP : Z := 0x3ee58.     (* [comment removed for export] *)
Definition EXC_CLASS : Z := 0x434c4e47432b2b00.  (* [comment removed for export] *)
(* [comment removed for export] *)
Definition TI_RUNTIME_ERROR : Z := 0x5e168.    (* [comment removed for export] *)
Definition DTOR_RUNTIME_ERROR : Z := 0x3df78.  (* [comment removed for export] *)
Definition VT_RUNTIME_ERROR : Z := 0x5e078.    (* [comment removed for export] *)
Definition TI_ASSERTION_ERROR : Z := 0x5b1f0.  (* [comment removed for export] *)
Definition VT_ASSERTION_ERROR : Z := 0x5b218.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition zero_divide_msg : list Z := [90;101;114;111;32;100;105;118;105;100;101;46].        (* [comment removed for export] *)
Definition assert_msg : list Z :=                                                             (* [comment removed for export] *)
  [97;115;115;101;114;116;105;111;110;32;39;110;32;60;32;109;97;120;95;115;105;122;101;39;32;102;97;105;108;101;100;32;97;116;32;32;60;62;32;58;48].
Definition REF1_SZ : Z := 41.   (* [comment removed for export] *)
Definition REF2_SZ : Z := 37.   (* [comment removed for export] *)
Definition REF3_SZ : Z := 66.   (* [comment removed for export] *)
Definition EXC1_SZ : Z := 160.  (* [comment removed for export] *)
Definition EXC23_SZ : Z := 144. (* [comment removed for export] *)

(* [comment removed for export] *)
Definition CATCH_SCR : Z := 112 + HEAP_STACK.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record XS : Type := mkXS { xs_gd : bool; xs_fl : bool; xs_av : Z; xs_uid : Z; xs_rnd : Z; xs_canary : Z; xs_hw : Z }.
Definition xs_of (gd fl : bool) (av uid rnd canary hw : Z) : XS := mkXS gd fl av uid rnd canary hw.

Definition lib_statics_at (M : word -> option byte) (gd fl : bool) (av uid rnd canary hw : Z) : Prop :=
  L5PS.e1_statics M gd fl av uid rnd canary hw.
Definition xs_pre (st : XS) (M : word -> option byte) : Prop :=
  lib_statics_at M (xs_gd st) (xs_fl st) (xs_av st) (xs_uid st) (xs_rnd st) (xs_canary st) (xs_hw st).

(* [comment removed for export] *)
Definition xs_foot : list L5.range := [(L5PS.EH_UNCAUGHT, 4); (L5PS.UW_FLAGS, 6)].

Lemma xs_foot_incl : Forall (fun r => (0x6f8f8 <= fst r /\ fst r + snd r <= 0x6f908) \/ (0x6fb20 <= fst r /\ fst r + snd r <= 0x6fb22)
                                     \/ (0x70361 <= fst r /\ fst r + snd r <= 0x70367)) xs_foot.
Proof. unfold xs_foot, L5PS.EH_UNCAUGHT, L5PS.UW_FLAGS. repeat constructor; cbn; lia. Qed.

(* [comment removed for export] *)
Definition statics_landed (M : word -> option byte) (gd : bool) (av uid rnd canary hw : Z) : Prop :=
     L5.u64_at RSEGS M L5PS.EH_CAUGHT 0 /\ L5.u32_at RSEGS M L5PS.EH_UNCAUGHT 1
  /\ L5.u8_at RSEGS M L5PS.SYSCAT_GUARD (if gd then 1 else 0) /\ L5.u8_at RSEGS M (L5PS.SYSCAT_GUARD + 1) (if gd then 1 else 0)
  /\ L5.u8_at RSEGS M L5PS.UW_FLAGS 1 /\ L5.u8_at RSEGS M (L5PS.UW_FLAGS + 1) 0 /\ L5.u8_at RSEGS M (L5PS.UW_FLAGS + 2) 1
  /\ L5.u8_at RSEGS M (L5PS.UW_FLAGS + 3) 0 /\ L5.u8_at RSEGS M (L5PS.UW_FLAGS + 4) 1 /\ L5.u8_at RSEGS M (L5PS.UW_FLAGS + 5) 0
  /\ L5.u64_at RSEGS M L5PS.TD_LOCALE L5PS.GLOBAL_LOCALE /\ L5.u64_at RSEGS M L5PS.LOCALE_MSGCAT 0
  /\ L5.u64_at RSEGS M L5PS.CANARY canary /\ L5.u64_at RSEGS M L5PS.AUXVP av /\ av mod 8 = 0 /\ 2 ^ 40 <= av /\ av + 160 <= 2 ^ 47
  /\ (forall j, (j < 20)%nat -> L5.u64_at RSEGS M (av + 8 * Z.of_nat j) (nth j (L5PS.auxv20 uid rnd hw) 0))
  /\ 0 <= uid < 2 ^ 64 /\ 0 <= rnd < 2 ^ 64 /\ 0 <= canary < 2 ^ 64 /\ 0 <= hw < 2 ^ 64
  /\ L5.img_clear M 0x10000 0x5f608 /\ L5.img_clear M 0x5f630 0x5f650 /\ L5.img_clear M 0x5f660 0x5f668.

(* [comment removed for export] *)
Lemma statics_landed_of_e1 : forall M0 M gd fl av uid rnd canary hw,
  L5PS.e1_statics M0 gd fl av uid rnd canary hw -> L5PS.e1_statics_landed M av uid rnd canary hw ->
  statics_landed M true av uid rnd canary hw.
Proof.
  intros M0 M gd fl av uid rnd canary hw PRE LD.
  unfold L5PS.e1_statics in PRE. unfold L5PS.e1_statics_landed in LD. unfold statics_landed. cbn [negb].
  decompose [and] PRE; decompose [and] LD; repeat split; try assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition exc_hdr (M : word -> option byte) (obj ti dtor pad cfa : Z) : Prop :=
     (forall i, 0 <= i < 8 -> L5.u8_at RSEGS M (obj - 128 + i) 0)            (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M (obj - 120) 1                                         (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M (obj - 112) ti /\ L5.u64_at RSEGS M (obj - 104) dtor
  /\ L5.u64_at RSEGS M (obj - 96) UNEXPECTED_H /\ L5.u64_at RSEGS M (obj - 88) TERMINATE_H
  /\ (forall i, 0 <= i < 12 -> L5.u8_at RSEGS M (obj - 80 + i) 0)            (* [comment removed for export] *)
  /\ L5.u32_at RSEGS M (obj - 68) 1                                          (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M (obj - 64) EXC_ACTION /\ L5.u64_at RSEGS M (obj - 56) EXC_LSDA /\ L5.u64_at RSEGS M (obj - 48) pad
  /\ L5.u64_at RSEGS M (obj - 40) obj                                        (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M (obj - 32) EXC_CLASS /\ L5.u64_at RSEGS M (obj - 24) UE_CLEANUP /\ L5.u64_at RSEGS M (obj - 16) 0
  /\ L5.u64_at RSEGS M (obj - 8) cfa.

(* [comment removed for export] *)
Definition refstring_at (M : word -> option byte) (ref : Z) (txt : list Z) : Prop :=
     L5.u64_at RSEGS M ref (Z.of_nat (length txt)) /\ L5.u64_at RSEGS M (ref + 8) (Z.of_nat (length txt))
  /\ L5.u32_at RSEGS M (ref + 16) 0
  /\ L5.bytes_at RSEGS M (ref + 24) (txt ++ [0]).

(* [comment removed for export] *)
Definition exc_blocks_ok (obj ref objsz refsz : Z) : Prop :=
     (obj - 128) mod 16 = 0 /\ 4096 <= obj - 128 /\ obj + (objsz - 128) <= 2 ^ 47 /\ L5.hull_apart RSEGS (obj - 128) objsz
  /\ ref mod 16 = 0 /\ 4096 <= ref /\ ref + refsz <= 2 ^ 47 /\ L5.hull_apart RSEGS ref refsz
  /\ (obj - 128 + objsz <= ref \/ ref + refsz <= obj - 128).

(* [comment removed for export] *)
Definition exc1 (M : word -> option byte) (obj : Z) (LBX : list (Z * Z)) : Prop :=
  exists ref spL, LBX = [(ref, REF1_SZ); (obj - 128, EXC1_SZ)] /\ exc_blocks_ok obj ref EXC1_SZ REF1_SZ /\ L5PS.e1_exception_at M obj ref spL.

(* [comment removed for export] *)
Definition exc2_at (M : word -> option byte) (obj ref cfa : Z) : Prop :=
     exc_hdr M obj TI_RUNTIME_ERROR DTOR_RUNTIME_ERROR TOP_PAD cfa
  /\ L5.u64_at RSEGS M obj VT_RUNTIME_ERROR /\ L5.u64_at RSEGS M (obj + 8) (ref + 24)
  /\ refstring_at M ref zero_divide_msg.
Definition exc2 (M : word -> option byte) (obj : Z) (LBX : list (Z * Z)) : Prop :=
  exists ref cfa, LBX = [(ref, REF2_SZ); (obj - 128, EXC23_SZ)] /\ exc_blocks_ok obj ref EXC23_SZ REF2_SZ /\ exc2_at M obj ref cfa.

(* [comment removed for export] *)
Definition exc3_at (M : word -> option byte) (obj ref cfa : Z) : Prop :=
     exc_hdr M obj TI_ASSERTION_ERROR DTOR_RUNTIME_ERROR TOP_PAD cfa
  /\ L5.u64_at RSEGS M obj VT_ASSERTION_ERROR /\ L5.u64_at RSEGS M (obj + 8) (ref + 24)
  /\ refstring_at M ref assert_msg.
Definition exc3 (M : word -> option byte) (obj : Z) (LBX : list (Z * Z)) : Prop :=
  exists ref cfa, LBX = [(ref, REF3_SZ); (obj - 128, EXC23_SZ)] /\ exc_blocks_ok obj ref EXC23_SZ REF3_SZ /\ exc3_at M obj ref cfa.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithLayout.
Variable L : heap_layout.

Definition e2_landed (st : XS) (LB1 : list (Z * Z)) (cr1 : credit) (S : Z) (M' : word -> option byte) (R' : bvmap 5 word)
           (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  exists obj ref,
     getr R' 10%bv = Z_to_bv 64 (obj - 32) /\ getr R' 11%bv = Z_to_bv 64 1 /\ getr R' 2%bv = Z_to_bv 64 S
  /\ LB' = (ref, REF2_SZ) :: (obj - 128, EXC23_SZ) :: LB1
  /\ L5C.fresh_block L LB1 M' (obj - 128) EXC23_SZ /\ L5C.fresh_block L ((obj - 128, EXC23_SZ) :: LB1) M' ref REF2_SZ
  /\ exc_blocks_ok obj ref EXC23_SZ REF2_SZ
  /\ exc2_at M' obj ref S
  /\ statics_landed M' (xs_gd st) (xs_av st) (xs_uid st) (xs_rnd st) (xs_canary st) (xs_hw st)
  /\ credit_le (debit L (debit L cr1 EXC23_SZ) REF2_SZ) cr'.

Definition e3_landed (st : XS) (LB1 : list (Z * Z)) (cr1 : credit) (S : Z) (M' : word -> option byte) (R' : bvmap 5 word)
           (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  exists obj ref,
     getr R' 10%bv = Z_to_bv 64 (obj - 32) /\ getr R' 11%bv = Z_to_bv 64 1 /\ getr R' 2%bv = Z_to_bv 64 S
  /\ LB' = (ref, REF3_SZ) :: (obj - 128, EXC23_SZ) :: LB1
  /\ L5C.fresh_block L LB1 M' (obj - 128) EXC23_SZ /\ L5C.fresh_block L ((obj - 128, EXC23_SZ) :: LB1) M' ref REF3_SZ
  /\ exc_blocks_ok obj ref EXC23_SZ REF3_SZ
  /\ exc3_at M' obj ref S
  /\ statics_landed M' (xs_gd st) (xs_av st) (xs_uid st) (xs_rnd st) (xs_canary st) (xs_hw st)
  /\ credit_le (debit L (debit L (debit L cr1 48) EXC23_SZ) REF3_SZ) cr'.    (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma e2_landed_elim : forall gd fl av uid rnd canary hw LB1 cr1 S M' R' LB' cr',
  e2_landed (xs_of gd fl av uid rnd canary hw) LB1 cr1 S M' R' LB' cr' ->
  exists obj LBX, getr R' 10%bv = Z_to_bv 64 (obj - 32) /\ getr R' 11%bv = Z_to_bv 64 1 /\ LB' = LBX ++ LB1
    /\ exc2 M' obj LBX /\ statics_landed M' gd av uid rnd canary hw
    /\ fst cr1 - 2 * hl_k_per_malloc L <= fst cr' /\ snd cr1 - (REF2_SZ + EXC23_SZ + 2 * hl_b_overhead L) <= snd cr'.
Proof.
  intros gd fl av uid rnd canary hw LB1 cr1 S M' R' LB' cr' (obj & ref & A0 & A1 & _ & ELB & _ & _ & BOK & EXC & STL & CR).
  exists obj, [(ref, REF2_SZ); (obj - 128, EXC23_SZ)]. cbn [xs_gd xs_av xs_uid xs_rnd xs_canary xs_hw xs_of] in STL.
  split; [exact A0|]. split; [exact A1|]. split; [exact ELB|]. split; [exists ref, S; split; [reflexivity|]; split; [exact BOK | exact EXC]|].
  split; [exact STL|]. unfold credit_le, debit in CR. cbn [fst snd] in CR. lia.
Qed.

Lemma e3_landed_elim : forall gd fl av uid rnd canary hw LB1 cr1 S M' R' LB' cr',
  e3_landed (xs_of gd fl av uid rnd canary hw) LB1 cr1 S M' R' LB' cr' ->
  exists obj LBX, getr R' 10%bv = Z_to_bv 64 (obj - 32) /\ getr R' 11%bv = Z_to_bv 64 1 /\ LB' = LBX ++ LB1
    /\ exc3 M' obj LBX /\ statics_landed M' gd av uid rnd canary hw
    /\ fst cr1 - 3 * hl_k_per_malloc L <= fst cr' /\ snd cr1 - (48 + REF3_SZ + EXC23_SZ + 3 * hl_b_overhead L) <= snd cr'.
Proof.
  intros gd fl av uid rnd canary hw LB1 cr1 S M' R' LB' cr' (obj & ref & A0 & A1 & _ & ELB & _ & _ & BOK & EXC & STL & CR).
  exists obj, [(ref, REF3_SZ); (obj - 128, EXC23_SZ)]. cbn [xs_gd xs_av xs_uid xs_rnd xs_canary xs_hw xs_of] in STL.
  split; [exact A0|]. split; [exact A1|]. split; [exact ELB|]. split; [exists ref, S; split; [reflexivity|]; split; [exact BOK | exact EXC]|].
  split; [exact STL|]. unfold credit_le, debit in CR. cbn [fst snd] in CR. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition e2_chain_spec (HI : heap_iface) : Prop :=
  forall (fx : FPState) (R0 : bvmap 5 word) (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte)
         (model : Model) (K : TSet) (LB : list (Z * Z)) (cr : credit) (S : Z) (st : XS),
    L5DS.zero_throw_at L LB R0 M0 R M S ->
    getr R0 1%bv = Z_to_bv 64 L5DS.OPMOD1_RET -> getr R0 2%bv = Z_to_bv 64 S -> getr R0 3%bv = Z_to_bv 64 GP -> getr R0 4%bv = Z_to_bv 64 TP ->
    xs_pre st M -> hl_sptop L <= xs_av st ->
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    L5C.stk (hl_sptop L) M S L5DS.SCR_OPMOD -> S + 240 <= hl_sptop L ->
    credit_ok L cr EXC23_SZ -> credit_ok L (debit L cr EXC23_SZ) REF2_SZ ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit),
        regs_preserved R0 R' ->
        e2_landed st LB cr S M' R' LB' cr' ->
        L5C.hpres L LB S L5DS.SCR_OPMOD xs_foot M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' TOP_PAD M' model') K) ->
    srealizes RSEGS SCFG (cfg R ZERO_THROW M model) K.

(* [comment removed for export] *)
Definition e3_chain_spec_of (assert_throw_req : list (Z * Z) -> list (Z * Z) -> bvmap 5 word -> (word -> option byte) -> bvmap 5 word -> (word -> option byte) -> Z -> Prop)
           (HI : heap_iface) : Prop :=
  forall (fx : FPState) (R0 : bvmap 5 word) (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte)
         (model : Model) (K : TSet) (LBT LB1 : list (Z * Z)) (cr : credit) (S : Z) (st : XS),
    (* [comment removed for export] *)
    assert_throw_req LBT LB1 R0 M0 R M S ->
    getr R0 1%bv = Z_to_bv 64 L5DS.OPMOD1_RET -> getr R0 2%bv = Z_to_bv 64 S -> getr R0 3%bv = Z_to_bv 64 GP -> getr R0 4%bv = Z_to_bv 64 TP ->
    xs_pre st M -> hl_sptop L <= xs_av st ->
    hi_heap HI (LBT ++ LB1) cr M (m_vmmaps model) -> model_ok model -> K [] ->
    L5C.stk (hl_sptop L) M S L5DS.SCR_OPMOD -> S + 240 <= hl_sptop L ->
    credit_ok L cr EXC23_SZ -> credit_ok L (debit L cr EXC23_SZ) 48 -> credit_ok L (debit L (debit L cr EXC23_SZ) 48) REF3_SZ ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LB' : list (Z * Z)) (cr' : credit),
        regs_preserved R0 R' ->
        e3_landed st LB1 cr S M' R' LB' cr' ->
        L5C.hpres L LB1 S L5DS.SCR_OPMOD xs_foot M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' TOP_PAD M' model') K) ->
    srealizes RSEGS SCFG (cfg R ASSERT_THROW M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition catch_spec (HI : heap_iface) (exc_at : (word -> option byte) -> Z -> list (Z * Z) -> Prop) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB LBX : list (Z * Z)) (cr : credit) (obj S : Z),
    hi_heap HI (LBX ++ LB) cr M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 (obj - 32) ->
    getr R 2%bv = Z_to_bv 64 S -> getr R 3%bv = Z_to_bv 64 GP -> getr R 4%bv = Z_to_bv 64 TP ->
    L5C.stk (hl_sptop L) M S CATCH_SCR ->
    exc_at M obj LBX ->
    L5.u64_at RSEGS M L5PS.EH_CAUGHT 0 -> L5.u32_at RSEGS M L5PS.EH_UNCAUGHT 1 ->
    L5.img_clear M 0x10000 0x5f608 -> L5.img_clear M 0x5f630 0x5f650 -> L5.img_clear M 0x5f660 0x5f668 ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        regs_preserved R R' ->
        L5.u64_at RSEGS M' L5PS.EH_CAUGHT 0 -> L5.u32_at RSEGS M' L5PS.EH_UNCAUGHT 0 ->
        L5C.hpres L LB S CATCH_SCR [(L5PS.EH_CAUGHT, 8); (L5PS.EH_UNCAUGHT, 4)] M M' ->
        model_but_vm model model' -> hi_heap HI LB cr M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' CATCH_RET M' model') K) ->
    srealizes RSEGS SCFG (cfg R CATCH M model) K.

Definition catch1_spec (HI : heap_iface) : Prop := catch_spec HI exc1.
Definition catch2_spec (HI : heap_iface) : Prop := catch_spec HI exc2.
Definition catch3_spec (HI : heap_iface) : Prop := catch_spec HI exc3.

End WithLayout.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma xs_pre_e1 : forall gd fl av uid rnd canary hw M,
  xs_pre (xs_of gd fl av uid rnd canary hw) M <-> L5PS.e1_statics M gd fl av uid rnd canary hw.
Proof. intros. unfold xs_pre, lib_statics_at. cbn. tauto. Qed.

(* [comment removed for export] *)
Lemma exc1_of_e1_landing : forall L LB M obj ref spL,
  L5PS.e1_exception_at M obj ref spL ->
  L5C.fresh_block L LB M (obj - 128) EXC1_SZ -> L5C.fresh_block L ((obj - 128, EXC1_SZ) :: LB) M ref REF1_SZ ->
  hl_img_lo L = L5.hull_lo RSEGS -> hl_img_hi L = L5.hull_hi RSEGS -> hl_sptop L <= 2 ^ 47 ->
  exc1 M obj [(ref, REF1_SZ); (obj - 128, EXC1_SZ)].
Proof.
  intros L LB M obj ref spL EXC FB1 FB2 Hlo Hhi Htop.
  pose proof (L5C.fresh_block_bounds _ _ _ _ _ FB1) as (A1 & B1 & C1 & D1 & E1).
  pose proof (L5C.fresh_block_bounds _ _ _ _ _ FB2) as (A2 & B2 & C2 & D2 & E2).
  pose proof (L5C.fresh_block_hull RSEGS _ _ _ _ _ FB1 Hlo Hhi) as H1.
  pose proof (L5C.fresh_block_hull RSEGS _ _ _ _ _ FB2 Hlo Hhi) as H2.
  destruct FB2 as (_ & AP2 & _). specialize (AP2 (obj - 128, EXC1_SZ) (or_introl eq_refl)). cbn [fst snd] in AP2.
  exists ref, spL. split; [reflexivity|]. split; [| exact EXC].
  unfold exc_blocks_ok, EXC1_SZ, REF1_SZ in *. repeat split; try assumption; try lia.
Qed.

(* [comment removed for export] *)
Lemma u32_at_agree : forall M M' a v, L5C.agree_on M M' a 4 -> 0 <= a -> a + 4 <= 2 ^ 64 -> L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v.
Proof. intros M M' a v AG Ha Hn H. unfold L5.u32_at in *. rewrite (L5C.rdn_agree RSEGS M M' 4 a Ha ltac:(cbn; lia) AG). exact H. Qed.

Lemma exc_hdr_agree : forall M M' obj ti dtor pad cfa,
  L5C.agree_on M M' (obj - 128) EXC23_SZ -> 4096 <= obj - 128 -> obj + 16 <= 2 ^ 47 ->
  exc_hdr M obj ti dtor pad cfa -> exc_hdr M' obj ti dtor pad cfa.
Proof.
  intros M M' obj ti dtor pad cfa AG LO HI H. unfold exc_hdr, EXC23_SZ in *.
  decompose [and] H.
  repeat match goal with |- _ /\ _ => split end;
  first [ intros i Hi; eapply L5C.u8_at_agree; [eapply L5C.agree_on_sub; [exact AG | lia | lia] | lia | lia | eauto]
        | eapply L5C.u64_at_agree; [eapply L5C.agree_on_sub; [exact AG | lia | lia] | lia | lia | assumption]
        | eapply u32_at_agree; [eapply L5C.agree_on_sub; [exact AG | lia | lia] | lia | lia | assumption] ].
Qed.

Lemma refstring_at_agree : forall M M' ref txt,
  L5C.agree_on M M' ref (25 + Z.of_nat (length txt)) -> 4096 <= ref -> ref + 25 + Z.of_nat (length txt) <= 2 ^ 47 ->
  refstring_at M ref txt -> refstring_at M' ref txt.
Proof.
  intros M M' ref txt AG LO HI (A & B & C & D). unfold refstring_at.
  split; [| split; [| split]].
  - eapply L5C.u64_at_agree; [eapply L5C.agree_on_sub; [exact AG | lia | lia] | lia | lia | exact A].
  - eapply L5C.u64_at_agree; [eapply L5C.agree_on_sub; [exact AG | lia | lia] | lia | lia | exact B].
  - eapply u32_at_agree; [eapply L5C.agree_on_sub; [exact AG | lia | lia] | lia | lia | exact C].
  - eapply L5C.bytes_at_agree; [| lia | | exact D]; rewrite length_app; cbn [length];
      [eapply L5C.agree_on_sub; [exact AG | lia | lia] | lia].
Qed.

Lemma exc2_agree : forall M M' obj LBX,
  (forall b, In b LBX -> L5C.agree_on M M' (fst b) (snd b)) -> exc2 M obj LBX -> exc2 M' obj LBX.
Proof.
  intros M M' obj LBX AG (ref & cfa & -> & BOK & (HDR & VT & IMP & RS)).
  pose proof (AG (ref, REF2_SZ) (or_introl eq_refl)) as AGR. pose proof (AG (obj - 128, EXC23_SZ) (or_intror (or_introl eq_refl))) as AGO.
  cbn [fst snd] in AGR, AGO. destruct BOK as (O16 & OLO & OHI & OHA & R16 & RLO & RHI & RHA & APART).
  unfold EXC23_SZ, REF2_SZ in *.
  exists ref, cfa. split; [reflexivity|]. split; [repeat split; assumption|]. split; [| split; [| split]].
  - eapply exc_hdr_agree; [exact AGO | lia | lia | exact HDR].
  - eapply L5C.u64_at_agree; [eapply L5C.agree_on_sub; [exact AGO | lia | lia] | lia | lia | exact VT].
  - eapply L5C.u64_at_agree; [eapply L5C.agree_on_sub; [exact AGO | lia | lia] | lia | lia | exact IMP].
  - eapply refstring_at_agree; [| lia | | exact RS]; unfold zero_divide_msg; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; [| lia].
    eapply L5C.agree_on_sub; [exact AGR | lia | lia].
Qed.

Lemma exc3_agree : forall M M' obj LBX,
  (forall b, In b LBX -> L5C.agree_on M M' (fst b) (snd b)) -> exc3 M obj LBX -> exc3 M' obj LBX.
Proof.
  intros M M' obj LBX AG (ref & cfa & -> & BOK & (HDR & VT & IMP & RS)).
  pose proof (AG (ref, REF3_SZ) (or_introl eq_refl)) as AGR. pose proof (AG (obj - 128, EXC23_SZ) (or_intror (or_introl eq_refl))) as AGO.
  cbn [fst snd] in AGR, AGO. destruct BOK as (O16 & OLO & OHI & OHA & R16 & RLO & RHI & RHA & APART).
  unfold EXC23_SZ, REF3_SZ in *.
  exists ref, cfa. split; [reflexivity|]. split; [repeat split; assumption|]. split; [| split; [| split]].
  - eapply exc_hdr_agree; [exact AGO | lia | lia | exact HDR].
  - eapply L5C.u64_at_agree; [eapply L5C.agree_on_sub; [exact AGO | lia | lia] | lia | lia | exact VT].
  - eapply L5C.u64_at_agree; [eapply L5C.agree_on_sub; [exact AGO | lia | lia] | lia | lia | exact IMP].
  - eapply refstring_at_agree; [| lia | | exact RS]; unfold assert_msg; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; [| lia].
    eapply L5C.agree_on_sub; [exact AGR | lia | lia].
Qed.

(* [comment removed for export] *)

End SCFG_1.
End L5US.
