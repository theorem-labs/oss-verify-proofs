(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode.
Module HeapIface.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Record heap_layout : Type := HL {
  hl_segs      : list Segment;        (* [comment removed for export] *)
  hl_malloc    : Z;                   (* [comment removed for export] *)
  hl_free      : Z;                   (* [comment removed for export] *)
  hl_aligned_alloc : Z;               (* [comment removed for export] *)
  hl_tp        : Z;                   (* [comment removed for export] *)
  hl_errno     : Z;                   (* [comment removed for export] *)
  hl_img_lo    : Z;                   (* [comment removed for export] *)
  hl_img_hi    : Z;
  hl_alloc_static : Z -> Prop;        (* [comment removed for export] *)
  hl_alloc_ro  : Z -> Prop;           (* [comment removed for export] *)
  hl_stack     : Z;                   (* [comment removed for export] *)
  hl_sptop     : Z;                   (* [comment removed for export] *)
  hl_k_per_malloc : Z;                (* [comment removed for export] *)
  hl_b_overhead : Z;                  (* [comment removed for export] *)
  hl_K0 : Z; hl_B0 : Z                (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Abbreviation hl_ceil L := (hl_sptop L - 8388608).
(* [comment removed for export] *)

Lemma hl_ceil_eq : forall L, hl_ceil L = hl_sptop L - 2 ^ 23.
Proof. intros L. reflexivity. Qed.

Definition credit : Type := (Z * Z)%type.   (* [comment removed for export] *)
Definition credit_ok (L : heap_layout) (cr : credit) (n : Z) : Prop :=
  hl_k_per_malloc L <= fst cr /\ n + hl_b_overhead L <= snd cr.
Definition debit (L : heap_layout) (cr : credit) (n : Z) : credit :=
  (fst cr - hl_k_per_malloc L, snd cr - (n + hl_b_overhead L)).

(* [comment removed for export] *)
Definition in_block (LB : list (Z * Z)) (a : Z) : Prop :=
  exists b, In b LB /\ fst b <= a < fst b + snd b.

(* [comment removed for export] *)
Definition client_addr (L : heap_layout) (LB : list (Z * Z)) (sp scratch : Z) (a : Z) : Prop :=
  in_block LB a
  \/ (hl_ceil L <= a < 2 ^ 64 /\ ~ (sp - scratch <= a < sp))
  \/ (hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a).

(* [comment removed for export] *)
Definition in_errno (L : heap_layout) (a : Z) : Prop := hl_errno L <= a < hl_errno L + 4.

(* [comment removed for export] *)
Definition heap_pres_core (L : heap_layout) (LB : list (Z * Z)) (sp : Z) (M M' : word -> option byte) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> client_addr L LB sp (hl_stack L) a -> ~ in_errno L a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
  /\ (forall a, sp - hl_stack L <= a < sp -> M' (Z_to_bv 64 a) <> None).   (* [comment removed for export] *)
  (* [comment removed for export] *)

Definition heap_pres (L : heap_layout) (LB : list (Z * Z)) (sp : Z) (M M' : word -> option byte) : Prop :=
  heap_pres_core L LB sp M M'
  /\ rdn (hl_segs L) M' (Z_to_bv 64 (hl_errno L)) 4 = rdn (hl_segs L) M (Z_to_bv 64 (hl_errno L)) 4.   (* [comment removed for export] *)

Definition defined (M : word -> option byte) (a n : Z) : Prop :=
  forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) <> None.

Definition blocks_apart (A n : Z) (LB : list (Z * Z)) : Prop :=
  forall b, In b LB -> A + n <= fst b \/ fst b + snd b <= A.

(* [comment removed for export] *)
Definition block_range (L : heap_layout) (A n : Z) : Prop :=
  4096 <= A /\ (A + n <= hl_img_lo L \/ hl_img_hi L <= A) /\ A mod 16 = 0 /\ 0 < n /\ A + n <= hl_ceil L.

Fixpoint lb_remove (A : Z) (LB : list (Z * Z)) : list (Z * Z) :=
  match LB with
  | [] => []
  | b :: LB' => if Z.eqb (fst b) A then LB' else b :: lb_remove A LB'
  end.

(* [comment removed for export] *)
Definition callee_saved_idx : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition regs_preserved (R R' : bvmap 5 word) : Prop :=
  forall r : bv 5, In (bv_unsigned r) callee_saved_idx -> getr R' r = getr R r.

(* [comment removed for export] *)
Definition model_but_vm (m m' : Model) : Prop :=
  m' = with_vmmaps (m_vmmaps m') m.

(* [comment removed for export] *)
Section Iface.
Variable L : heap_layout.
Variable scfg : SpuriousCfg. Context {bmK : BMode}.   (* [comment removed for export] *)      (* [comment removed for export] *)

Record heap_iface : Type := HI {
  (* [comment removed for export] *)
  hi_heap : list (Z * Z) -> credit -> (word -> option byte) -> VmMaps -> Prop
}.

Variable HI : heap_iface.

(* [comment removed for export] *)
Definition stack_ok (M : word -> option byte) (sp : Z) : Prop :=
  sp mod 16 = 0 /\ hl_ceil L + hl_stack L <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 /\
  (forall d (m : nat), 0 <= d -> d + Z.of_nat m <= hl_stack L ->
      store_ok (hl_segs L) M (Z_to_bv 64 (sp - hl_stack L + d)) m = true).

(* [comment removed for export] *)
Lemma stack_ok_floor : forall M sp, stack_ok M sp -> 0x7fff7f800000 + hl_stack L <= sp.
Proof. intros M sp (_ & H & _ & (Hlo & _) & _). lia. Qed.

(* [comment removed for export] *)
Definition malloc_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (cr : credit) (n : Z) (K : ShapeAlg.TSet),
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    getr R 10%bv = Z_to_bv 64 n -> 0 < n <= 2 ^ 27 ->
    credit_ok L cr n ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    Hoare.ret_ok (getr R 1%bv) ->                      (* [comment removed for export] *)
    stack_ok M (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A : Z),
        getr R' 10%bv = Z_to_bv 64 A ->
        regs_preserved R R' ->
        block_range L A n -> blocks_apart A n LB ->
        defined M' A n ->
        heap_pres_core L LB (bv_unsigned (getr R 2%bv)) M M' ->
        model_but_vm model model' ->
        hi_heap HI ((A, n) :: LB) (debit L cr n) M' (m_vmmaps model') ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_malloc L)) M (seg_rom (hl_segs L))) model) K.


(* [comment removed for export] *)
Definition aligned_alloc16_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (cr : credit) (n : Z) (K : ShapeAlg.TSet),
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    getr R 10%bv = Z_to_bv 64 16 -> getr R 11%bv = Z_to_bv 64 n -> 0 < n <= 2 ^ 27 ->
    credit_ok L cr n ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    Hoare.ret_ok (getr R 1%bv) ->                      (* [comment removed for export] *)
    stack_ok M (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A : Z),
        getr R' 10%bv = Z_to_bv 64 A ->
        regs_preserved R R' ->
        block_range L A n -> blocks_apart A n LB ->
        defined M' A n ->
        heap_pres_core L LB (bv_unsigned (getr R 2%bv)) M M' ->
        model_but_vm model model' ->
        hi_heap HI ((A, n) :: LB) (debit L cr n) M' (m_vmmaps model') ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_aligned_alloc L)) M (seg_rom (hl_segs L))) model) K.

(* [comment removed for export] *)
Definition free_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (cr : credit) (A n : Z) (K : ShapeAlg.TSet),
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    In (A, n) LB ->
    getr R 10%bv = Z_to_bv 64 A ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    Hoare.ret_ok (getr R 1%bv) ->                      (* [comment removed for export] *)
    stack_ok M (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        regs_preserved R R' ->
        heap_pres L (lb_remove A LB) (bv_unsigned (getr R 2%bv)) M M' ->
        model_but_vm model model' ->
        hi_heap HI (lb_remove A LB) cr M' (m_vmmaps model') ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_free L)) M (seg_rom (hl_segs L))) model) K.

(* [comment removed for export] *)
Definition free_null_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : ShapeAlg.TSet),
    m_halted model = None -> m_vm_lazy model = [] ->
    getr R 10%bv = Z_to_bv 64 0 ->
    Hoare.ret_ok (getr R 1%bv) ->
    K [] ->
    (forall R', regs_preserved R R' ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M (seg_rom (hl_segs L))) model) K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_free L)) M (seg_rom (hl_segs L))) model) K.

(* [comment removed for export] *)
Definition alloc_private (LB : list (Z * Z)) (a : Z) : Prop :=
  (a < hl_ceil L /\ ~ in_block LB a /\ ~ (hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a))
  \/ hl_alloc_ro L a.

Definition heap_frame : Prop :=
  forall LB cr M M' VM,
    hi_heap HI LB cr M VM ->
    (forall a, 0 <= a < 2 ^ 64 -> alloc_private LB a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    (forall a : word, M a <> None -> M' a <> None) ->
    hi_heap HI LB cr M' VM.

(* [comment removed for export] *)
Definition heap_blocks_wf : Prop :=
  forall LB cr M VM, hi_heap HI LB cr M VM ->
    (forall b, In b LB -> block_range L (fst b) (snd b) /\ defined M (fst b) (snd b)
                       /\ blocks_apart (fst b) (snd b) (lb_remove (fst b) LB))
    /\ NoDup (map fst LB) /\ 0 <= fst cr /\ 0 <= snd cr.

(* [comment removed for export] *)
Definition heap_perm : Prop :=
  forall LB LB' cr M VM, hi_heap HI LB cr M VM -> (forall b, In b LB <-> In b LB') -> NoDup (map fst LB') ->
    hi_heap HI LB' cr M VM.

Record heap_iface_ok : Prop := HIOK {
  hio_malloc : malloc_spec;
  hio_aligned : aligned_alloc16_spec;
  hio_free : free_spec;
  hio_free_null : free_null_spec;
  hio_frame : heap_frame;
  hio_wf : heap_blocks_wf;
  hio_perm : heap_perm
}.
End Iface.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section InitVm.
Context {bmK : BMode}.
Definition init_vm (L : heap_layout) (lim : Z) (VM : VmMaps) : Prop :=
  exists brk0 mbase isp,
    VM = mkVmMapsFull (segments_reserved (hl_segs L)) [] [] brk0 brk0 lim mbase isp /\
    valid_brk (hl_segs L) brk0 /\ valid_mmap_base mbase /\ valid_sp isp /\ bv_unsigned isp = hl_sptop L /\ (bm_on = true \/ 2 ^ 34 <= lim).
End InitVm.
(* [comment removed for export] *)

Lemma init_vm_alloc_top : forall L lim VM, init_vm L lim VM -> alloc_top VM = hl_ceil L.
Proof.
  intros L lim VM (brk0 & mbase & isp & -> & _ & _ & _ & Hsp & _).
  unfold alloc_top. cbn [vm_init_sp]. rewrite Hsp. rewrite stack_max_size_val. reflexivity.
Qed.

End HeapIface.
From Stdlib Require ZArith List Lia Bool. From stdpp.bitvector Require definitions. From LinuxProcessSemantics.Riscv Require Prelude Instr. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module L5Defs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_L5Defs () := "C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3fstC35stdpp4base6ElemOfI35stdpp4base<list_elem_of00I35stdpp4base5NoDup00C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundc69OSSVerify5KrLib7Mh_00846L5Defs2L5:hull_apartC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01c69OSSVerify5KrLib7Mh_00846L5Defs2L57hull_loC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_00846L5Defs2L57hull_hiC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01c69OSSVerify5KrLib7Mh_00846L5Defs2L55rangeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List4inclK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions;bv_unsignedc69OSSVerify5KrLib7Mh_00846L5Defs2L57outsideC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_00846L5Defs2L59frame_butC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2Inc69OSSVerify5KrLib7Mh_00846L5Defs2L56in_rngC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notI47Corelib4Init5Logic3and00C46Stdlib5Lists4List:in_app_iffK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K47Corelib4Init5Logic3and01C47Corelib4Init5Logic3iffc69OSSVerify5KrLib7Mh_00846L5Defs2L5;outside_appC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rc69OSSVerify5KrLib7Mh_00846L5Defs2L5>frame_but_monoC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z9mod_smallC45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions@Z_to_bv_unsignedC56Stdlib6ZArith6BinInt1Z6of_natC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions6bv_addC45stdpp9bitvector;definitions5bv_eqC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC47Corelib4Init5Logic6eq_indC45stdpp9bitvector;definitions?bv_add_unsignedC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revc69OSSVerify5KrLib7Mh_00846L5Defs2L5<unsigned_litC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula05I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succK46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init5Logic4True01I47Corelib7Numbers7BinNums1N00C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00c69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesc69OSSVerify5KrLib7Mh_00846L5Defs2L59rdn_frameC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith6BinInt1Z3mulc69OSSVerify5KrLib7Mh_00846L5Defs2L58limbs_atC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC47Corelib5Lists7ListDef3nthK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05c69OSSVerify5KrLib7Mh_00846L5Defs2L5<u64_at_frameC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk=store_ok_monoC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00849HeapIface>regs_preservedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00849HeapIface@callee_saved_idxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4succC56Stdlib6ZArith6BinInt1Z7testbitC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z9div2_bitsC56Stdlib6ZArith6BinInt1Z3oddC46Stdlib6ZArith4Zdiv8Zmod_oddK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib6ZArith4Zdiv;Zmod_uniqueC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega5Tauto8GFormula02C56Stdlib6ZArith6BinInt1Z8bit0_oddK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula0:K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic5False00K46Stdlib9micromega5Tauto4kind02C56Stdlib6ZArith6BinInt1Z4landC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decC46Stdlib4Bool4Bool;andb_true_rC56Stdlib6ZArith6BinInt1Z=testbit_falseC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z;lt_le_transC56Stdlib6ZArith6BinInt1Z9div_smallC56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z:land_assocC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00846L5Defs4SCFGC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg:srz_mstepsC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00c69OSSVerify5KrLib7Mh_00846L5Defs2L5=cps_of_mstepsC1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.

(* [comment removed for export] *)
Class ScfgP : Type := MkScfgP { SCFG : SpuriousCfg }.

Module L5.
Section WithSegs.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition u8_at (M : word -> option byte) (a : Z) (b : Z) : Prop :=
  rdn segs M (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 b].
Definition u64_at (M : word -> option byte) (a : Z) (v : Z) : Prop :=
  rdn segs M (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v)).
Definition u32_at (M : word -> option byte) (a : Z) (v : Z) : Prop :=
  rdn segs M (Z_to_bv 64 a) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 v)).
Definition bytes_at (M : word -> option byte) (p : Z) (bs : list Z) : Prop :=
  forall i, (i < length bs)%nat -> u8_at M (p + Z.of_nat i) (nth i bs 0).
Definition limbs_at (M : word -> option byte) (q : Z) (ws : list Z) : Prop :=
  forall i, (i < length ws)%nat -> u64_at M (q + 8 * Z.of_nat i) (nth i ws 0).
(* [comment removed for export] *)
Definition defined (M : word -> option byte) (a n : Z) : Prop :=
  forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) <> None.
(* [comment removed for export] *)
Definition writable (M : word -> option byte) (a n : Z) : Prop :=
  forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok segs M (Z_to_bv 64 (a + d)) k = true.
(* [comment removed for export] *)
Definition img_clear (M : word -> option byte) (lo hi : Z) : Prop :=
  forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None.
(* [comment removed for export] *)
Definition hull_lo : Z := fold_right Z.min (2 ^ 64) (map (fun s => Z.of_N (seg_base s)) segs).
Definition hull_hi : Z := fold_right Z.max 0 (map (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s)) segs).
Definition hull_apart (a n : Z) : Prop := a + n <= hull_lo \/ hull_hi <= a.
Lemma hull_apart_sub a n a' n' : hull_apart a n -> a <= a' -> a' + n' <= a + n -> hull_apart a' n'.
Proof.
ltac2:(KReplay.run1 (kr_t_L5Defs ()) ["WithSegs"] "h04__x1h14__x2h24__x3h34__x4h44__x5h54__x6h61ah72a'h81nh92n'h:7__arithh;4__ffh<8__varmaph=5__witp;2p;1p;3p;4p;7p;8p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000cR1p4p710p8P0P1p4p7210p8P0p1001@R1p4p710R2p8P0P1p4p7210R1p8P0p1001Tp4p710R0p8p10020p4p710R3P2p8P3P1p8P3P0p8g002Ej24Tg002bj20Tg003>j29Tg003Xj16Tg0047j25Tg004`j37Tg005Ij2@Tg0065j1NTg006Uj3>Tg0075j1GTg007Uj2;Tg0083j4:Tg008Qj1CTg008oj1RTg009Mj1QTg00:8j21Tg00:[j1<Tg00;@j3BTg00;cj1ATg00<Hj1PTg00<jj2MTg00=Lj2LTg00=fj2KTg00>Rj3JTg00>lj3HTg00?Kj4ITg00@=j2=Tg00A>j4FTg00Aij7ETg00BMj7OTg00C1j8DTg00CUR0f1R3g00D3f0R1CFp=2P3g00DZR2g00E9R4P4g00EYR5P1g00F9FEp=3f2R6P2P4P4P5P3P1FOp=?f3R7P2P4P4P5P6P3P1GDp=81476R2g00FYR8'0g00GWR9/07'9f4R:/06R;f5R</4:,02R2g00HUR=g00IAR>#6R?#6R@#6RA,50150@R@150>570570g00I`R>'@%6A,50150?970@570/@>%N=5>=3>%G=P0P01;0:P6f6R=,;0C:P3P01;0<P7%C0C:C:%R0%Q0R>g00JLR@,10R?%<@RA,105B0RB%AA,10RC%A@R@#<,105B0RD'2,3>%P4R4P>12C?,3>P4P>110@R@,2D,3>%<A,10RA/2C,3>5?>P412B@,3>12A?,3>5?>C8C8C81M>5P1P6g00K1R>g00KQR5'L1K16=J>5dg00L1=H03CIb;b<b=X00X10X20X30X40X50141314:<'010<3f7R5,4=/0:10<='9147:/0<10=7'9[[[^00^10^20^30^40^50P1P=P5P9P8P:P<P3P6P7O9b:UUU1=761=:7\2\;[eX90X70X80X60P7P6P3P1O4X90X70X80X60o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition range : Type := (Z * Z)%type.
Definition in_rng (r : range) (a : Z) : Prop := fst r <= a < fst r + snd r.
Definition outside (F : list range) (a : Z) : Prop := forall r, In r F -> ~ in_rng r a.
Definition frame_but (F : list range) (M M' : word -> option byte) : Prop :=
  forall x : word, outside F (bv_unsigned x) -> M' x = M x.

Lemma frame_but_refl F M : frame_but F M M.
Proof.
ltac2:(KReplay.run1 (kr_t_L5Defs ()) ["WithSegs"] "h01Fh11Mh22_Hh31xp;1p;2p;3p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000cR2p4p710p8P0P2p4p7210p8P0p1001@R2p4p710R3p8P0P2p4p7210R2p8P0p1001Tp4p710R0p8g00LOR4p606000R5P1p8P5p100MKp4p710p8P5p100Mhp4p710p8P5p100NEp4p710p8p10020p4p710R5P3p8P5P2p8P5P0p8g0075j18Tg00:[j10Tg00N^j12Tg00O<j11Tg00O_j17Tg00PAj26Tg00Pkj24Tg00=Lj23Tg00Qij35T%84R4g00JL#0#0#0R0#0#0#0#2R5#1R2%20#1#7R0[R3f2R1f0R6,65'4P1f1R1O1,30W2X32A5166eX13X04P1P6O2W1W0o"). Qed.
Lemma outside_app F G a : outside (F ++ G) a <-> outside F a /\ outside G a.
Proof.
ltac2:(KReplay.run1 (kr_t_L5Defs ()) ["WithSegs"] "h01rh11ah21Hh31Ah42Hrh51lh62l'h71Fh81Gh92H0h:2H1h;2H2p;1p;3p;2p;4p-1R0g00RiR1p4p710R2p8P0p1000GR3p4p710p8P0P3p4p7210p8P0p1000cR3p4p710p8P0P3p4p7210p8P0p1001@R3p4p710R4p8P0P3p4p7210R3p8P0p1001Tp4p710R0p8g00LOR5p606000R6P2p8P6g00MKp4p710R2p8P6g00MhR7p4p710p8P6p100NEp4p710p8p10020p4p710R6P4p8P6P3p8P6P0p8g0075j18TP7j32Tg00S@j23Tg00T=j14Tg00TVR7j27TP1j31Tg003>R1j25Tg00U1j4<Tg00UPj3;Tg00Ujj3:Tg00VDj49Tg00Pkj26Tg00V_j2=Tf1R0f0R6515p=0%85R3g00CUR4f3R8f2R9525,061309#4R:[^05R;f4R<,06R=1308#4R>[^05R?1068R@P>[^05RA'7[P:\@^051069P:[^05'7R:A25<8,06P>[^05[P?PAP9P0%86R>%80RBP7A28909186A1<08A1<09'5RC[RDA1869A1860'5A2<8991<0RE[RFf5RGA2G<8719\CP8P9P0P6C<RCP6n2001000000120000000X19W6W5X32RHPF^19^6B^5>^32RIP6P5f6RJPGP9109JRK109GRL;;0O5b9O2X4=X05P9P0PHPIP6P5PJPGP9A:KL0O5b9O2X4@X05C9X2;P7P?PAA25G<,06130<#4[^05P6106JRA130G#4[^05130J#4\A^05f8f7RA525,06P7PDPFA1G9<A1G98'5\EPCP0n2001000000120000000X19X6BX5>X32PD^19^6B^5>^32P6P5f:R2f9R>P9P0O51092109>'5P1f;R1,08108213<2#4P6f<,0<PAPGP6O2W2P6O110<1PJPGP6O2W2P6O1n200100000021000010000b4b2W4X05W;W:P0P6O2n2001000000120000000X2:C9A2590/6616961606'7'=eX14X83X73P9P0P6O3W1X83W7o"). Qed.
Lemma frame_but_mono F G M M' : (forall a, outside G a -> outside F a) -> frame_but F M M' -> frame_but G M M'.
Proof.
ltac2:(KReplay.run1 (kr_t_L5Defs ()) ["WithSegs"] "h01Fh11Gh21Mh32M'h42HFh53HFGh62Hxh71ah81xp;1p;2p;3p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000cR2p4p710p8P0P2p4p7210p8P0p1001@R2p4p710R3p8P0P2p4p7210R2p8P0p1001Tp4p710R0p8g00LOR4p606000R5P1p8P5p100MKp4p710p8P5p100Mhp4p710p8P5p100NEp4p710p8p10020p4p710R5P3p8P5P2p8P5P0p8g0075j17Tg00:[j10Tg00N^j13Tg00O<j12Tg00O_j16Tg00Pkj21Tg00Qij35Tg00PAj24T%74R4g00JL#0#0#0R0#0#0#0#3R5#2R2%30#2#6[R0g00CUf3R3f0R1'1f5R6f1R7'1[]7f4R8f2R9;571451,16P9P7P31457P1O2O2W6X82A5839eW4W5X30X20X14X04P3P9P7P1O4X30W2X14W0o"). Qed.
Lemma frame_but_trans F G M M' M'' : frame_but F M M' -> frame_but G M' M'' -> frame_but (F ++ G) M M''.
Proof.
ltac2:(KReplay.run1 (kr_t_L5Defs ()) ["WithSegs"] "h01Fh11Gh22Hxh31Mh42M'h53M''h61ah71Hh82H1h92H2h:3HxFh;3HxGh<1oh=1xp;1p;3p;2p;6p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000cR2p4p710p8P0P2p4p7210p8P0p1001@R2p4p710R3p8P0P2p4p7210R2p8P0p1001Tp4p710R0p8g00LOR4p606000R5P1p8P5p100MKp4p710p8P5g00MhR1p4p710p8P5p100NEp4p710p8p10020p4p710R5P3p8P5P2p8P5P0p8g0075j1<Tg00:[j11Tg00N^j16Tg00O<j15Tg00O_j1;Tg00Qij38TP1j33Tg00PAj22Tg00Pkj20Tg00TVR1j24Tg00W8j39Tg00>Rj37Tg00X:j6:T%<4R0g00JL#1#1#1R5#1#1#1#6R2#5R3%65#5#;R5[R6f4R7f2R8f1R938R:f7R;f6R<534f0R=,22'0g00CUR>P1A3489/0=f3R?/091089'4[R@108=109='4A34?8/09RA[107810?8'4\AA989=P9n2001000000120000000W6X10X00P@^6>^10^00P=f9R>f8R@1228RAP9O410>A10@A'4P1f:R1122?RA'010>AP;P7O1P>P7O1575P=f<RAf5RB,22'0122<,0AP5f;P;O1f=P@O1975=X<5P>P;P9O2P1P;O1P@P;P=O2E:W;W:P9P=O2n2001000000120000000b2b7W2X=3A34<B?878eX9:W8X56X46X36X10X00P7P?P8P9P=O5X56X46W3X10W0o"). Qed.
Lemma frame_but_weaken F G M M' : incl F G -> frame_but F M M' -> frame_but G M M'.
Proof.
ltac2:(KReplay.run1 (kr_t_L5Defs ()) ["WithSegs"] "h01Fh11Gh21Mh32M'h42HGh52Hih62Hrh71ah81rp;1p;3p;2p;5p-1R0g00RiR1p4p710R2p8P0p1000GR3p4p710p8P0P3p4p7210p8P0p1000cR3p4p710p8P0P3p4p7210p8P0p1001@R3p4p710R4p8P0P3p4p7210R3p8P0p1001Tp4p710R0p8g00LOR5p606000R6P2p8P6p100MKp4p710p8P6p100Mhp4p710p8P6g00NER6p4p710p8p10020p4p710R2P4p8P2P3p8P2P0p8g0075j18Tg00:[j10Tg00N^j13Tg00O<j11Tg00O_j17TP6j36Tg00Pkj22TP1j34Tg00XXj55T%85R1g00JL#0#0#0R6#0#0#0#3#1%36#1#7[R6f3R0f2R2565f4R3P0P2f1R4g00CUf0R7,23f79457P2P4P3P4P7O2O2W6X85f6/24eW4W7D5W5X36X26X11X01P0P2P4P7O4X36W2X11W0o"). Qed.

Lemma unsigned_lit a : 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof.
ltac2:(KReplay.run1 (kr_t_L5Defs ()) ["WithSegs"] "h01ah11Hh21zp;2p;1p;3p;6p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000cR2p4p710p8P0P2p4p7210p8P0p1001@R2p4p710R3p8P0P2p4p7210R2p8P0p1001Tp4p710R0p8p100LOp606000R4P1p8P4p100MKp4p710p8P4p100Mhp4p710p8P4p100NEp4p710p8p10020p4p710R4P3p8P4P2p8P4P0p8g002bj2>Tg00:[j10Tg00Y]j11Tg00Z;j23Tg00ZXj2=Tg00TVj2:Tg00N^j15Tg00[4j24Tg00>Rj32Tg00[Zj16Tg00\Cj37Tg00\fj28Tg00PAj29Tg00]Lj2<Tg00X:j6;Tg00CUR0g00L1f0R4'>g00JL#0R2#1%02#0#0#0#0R2#1'3,=4':P0%52R2f1R3'4R1f29204X20%62=734A2013e1823,921<23E;W1X00P4O1W0o"). Qed.

(* [comment removed for export] *)
Lemma rdn_frame (M M' : word -> option byte) F : frame_but F M M' ->
  forall n a, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (forall i, a <= i < a + Z.of_nat n -> outside F i) ->
  rdn segs M' (Z_to_bv 64 a) n = rdn segs M (Z_to_bv 64 a) n.
Proof.
ltac2:(KReplay.run1 (kr_t_L5Defs ()) ["WithSegs"] "p'0h04__x1h14__x2h21nh33Hn0h47__arithh54__ffh66__sat0h76__sat1h88__varmaph95__with:4cstrh;1xi001xh<1zh=2Hah>1ih?1ah@1FhA1HhB2HnhC4HouthD1MhE2M'hF4__x3hG2b1hH2b2hI1ohJ1yhK2HFhL2HihM2IHhN1bi011bhO1mi024restp&0p;1p;3p;2p;4p;6p;<p;Bp;7p;8p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000cR2p4p710p8P0P2p4p7210p8P0p1001@R2p4p710R3p8P0P2p4p7210R2p8P0p1001Tp4p710R0p8g00LOR4p606000R5P1p8P5p100MKp4p710p8P5p100Mhp4p710p8P5p100NEp4p710p8p10020p4p710R5P3p8P5P2p8P5P0p8g00:[j1CTg00N^j1iTg00O<j1=Tg00O_R0j1]Tg0075j1WTg00Qij3~Tg00^;R5j12Tg002ER2j20Tg00Y]j1PTg00Z;j2mTg002bR3j21Tg00Pkj2MTg00\fj2<Tg00^[j43Tg00>Rj37Tg00=Lj2KTg003XR1j1@Tg00_Lj2eTg00_nj2cTg00`cj3uTg00aFj3RTg006Uj3aTg00<Hj1`Tg00PAj25Tg00akj3oTg00[4j2>Tg00[Zj1nTg00bOj2FTg00boj3lTg00cVj6[Tg00]Lj2ZTg00X:j6BTg00d2j3kTg00d`j1JTg00e>j4jTg00eaj4VTg00fHj1OTg00fmk205Tg00ZXR6j2;Tg00gUk304Tg0065k103Tg007Uj2UTg008oj1}Tg009Mj1|Tg00h9j2TTg00:8j2STg00<jj2{Tg00=fj2zTg00>lj3yTg00?Kj4xTg008Qj1wTg0083j4\Tg00h\j3vTg00TVR7j2DTg00i?j6^Tg00;cj1tTg00ihj4dTg0047j2QTg004`j3YTg005Ij2sTg00jSj2rTg00kVj4qTg00l7l<fTg00l\lBpTg00mBl<_Tg00A>j4gTg00Aij7hTg00;@k300Tg00C1k801Tg00mgk702Tg00L1R8f0R9'1p=6f2R:f1R;/;9'Dp=:g00CUR<?7;9p=81K<9p=4g00nKR=P=P<P<P1P5P5f3R1g00njP:P;P9M<fp=NP=P<P<P<P5P5f5R5f4R>P1P:P;P9M<fp=GP<P<P<P<P<P<P2P9P;P:P2P1P>P5f6R2f7R?f8R@f9RAMBpp=EP<P<P3P?P3P2P5P>P1P:P;P9M<_p=XP:g00DZR3g00E9RBPBg00EYRCP<P;g00D3P9Cgg00F9RDFhp=9B00<;9p=?P1P3PBPBPCP:P;P9L01p=AP<P<P6P?P6P2P5P>P1P:P;P9M<_p=bP<P;g00oNP9Cgp=IP;P3PBPBPCP9PDFhp=HP:P3PBPBPCP;P9K02p=Lg00JLR3#CRD#C#CR6#C#C#CRE#iRF#=RG%i6#=R6#]RH[RI%W4R4A~9:;%69RJ%2:,0;%PDRK%PERE'mRL'11119RM%2>,017:91M@;[^><%W6RN#]ROp,4segsRPP@1<F1RQP>C3PPPAPQP>C337[[[^?<RRX2=g00IARS#2RT,0;/1L101T9:M91M?;[^><PPP@PQPSC3,KOWCWBX=JX?<%@1#2,0;/1L%@5RT#2RU,01RV9:M91MA;[^><PHf:RMPQO1P0P6POP0P6PHP91e69RW1<F>RX,cPRYn10110000021010100P0PNPOPPf;RZ1<F5R[%P3R\g01055uFR]5RFR^P?C3Aa6;9,eNR_%`NR`n10110000021010200P`n10110000021010100P0P6POP0P6PHPZPXO1PWPYn10110000021010100RYP0PNPOPPf<RaP^P?C3P_P`n10110000021010200P`n1011000002101010057OXIHg010QR^%=9Rb%=;RcP7%=:?7;9151:151;'8R7[15:;15:9'8%=1?7:;[Rd%=>?71:\7Ao:;9P9n2001000000120000000WHWGW2Pd^Hc^Gb^2^P9PF10>\R^,<FRbARFX]RcP<15FXRd15F]R7'0,>F105\Re,<FRf,5F/89X<<P<1>F^Rg15F[/07,>F,89X<<P<1>F>Rh1>Fe1097,>F'8X<<P<%nFRi,F>/0\/FiRj1F5i/0\/Fi,89X<<%4j1F^iAl>\iE[10h7,>F,8gePd1ZF>EB15Fb1ZF^EB15FcAkFX]EBO4bA101\RX,<FARFQ]57GPGPbP0P6POP0P6PHPaP[O1PW1cP[n10110000021010100R[P0PNPOPPPaP;P@C3P_P`n10110000021010200P`n10110000021010100P0P6POP[P0PNPOPPf=RWP;P@C3P_P`n10110000021010200P`n1011000002101010057OXNGPOPPPZPbP2C3P0P6POP[P0PNPOP;P_P`n10110000021010200P`n10110000021010100P0P6POP[P0PNPOPPPW102\,<FP@C3P_P`n10110000021010200P`n1011000002101010057OXIOP0P6POPYP0PNPOPPPaPfP?C3P_P`n10110000021010200P`n10110000021010100,KOPPPMPbP2C3P5P^%@2R^#2Rb,0>R`/1L%22R_/0\,0>/1LRfP9X;<Ra11;9#JXJ<X;<RNP`Pa109\R`X;<R0P_O1RYO1R6,0>PaPaPaP<P<g010o10;9Cj#4XO<X2<R[P>P>%4>PbP6PaPa%29#4X;=R6P^PYP0P2P_%4_CNEGM:EPLPL%4L18LLeRYGXP:CVR^Pf%O?Rb%2?RG#6RH205KER]1;8K%6E1;8L[[Rd%6KRgg011SRhB04KE;UW=RE%6L\h^=gRgg00HURh$03R7%WhRi1U<;%}<Rj%|<Rk1T<8Rl1S<3Rm59kRn%`BRB1T<\Ro,?mRp99klCA1{kCRCP9P:g00K1Rqg00KQRr'K1z9:=7qrdAy<8;CxR8b5b8b9X0<10;\Rr#6\J^0<P9PAP@O2b4b6b7b:b3P^PfPbPHP]PdPEPgP7PiP<1U<:RHP;%w<C\RbPjPk1S<DRD/?o,?mRf1T<K=v<FRK59kR^PB1?pD=9kKCAPCP8b5b8b9X0<X1<109r/1L10r:/1L[^0<^1<P9%2ZPAP>O3b4b6b7b:b311e910eG7:9P1P;112;RG%@@Re#2Rr,02Rq,;;Rs'D%2@Rt/0\Ru,02Rv,;;Rw,DGPGPsPGPw%JGPa1;;9#JXJ<X;<RGP;P;%4;PqPvPaPaPaP[P2P2%42RwPrPuPaPaP6PePuP0P@Pt%4tCNRuEGM:EGbE^11qL11vLRvPaPNPqPaP0PtO1RtO1Rq,02PaPaPaP[P2P2PwPrPqPaPaP6PePtPuEGM:EPLPLPYGXP>CVPv%OA%2A#6P]PdPEPgP7PiP<PHP;1U<1C\PjPkA9kpD%t3,S<R3,?p,ID,Hk5LkPBA9kmD1?3o,?m,ID,Hk5LkCAPCP8b5b8b9X0<X1<XF<11`;10`:7:;11;:10;X7::[^0<^1<^F<P9%2WP2PZP5O4b4b6b7b:b3CdO2WLX><O4EBPcP9E[bAPAPQO1P?PQP<P11MA9X<<P9P11111Rc1;1VRZ'D%25RW/0\RX,01R`,;1R3,DcPcPZPcP3%JcPaPGP1P1%41RGPVP`PaPaPaP[P1P1PGPUPXPaPaP6PTPXP0P5PW%4WCNR5EGM:EGbE^11VL11`LR`PaPNPVPaP0PWO1RWO1R0,01PaPaPaP[P1P1PGPUP0PaPaP6PTPWP5EGM:EPLPLPYGXP;CVRYP`%O2R2%6_R_P]PdPEPgP7PiPbPjPkA9klDRDPBA9kmm1Imf,Hk5LkCAPCP8b5b8b9X0<X1<%6;Rf11;;10:\,0;R\7:;[^0<^1<P9%2MRlP@P1O3b4b6b7b:b3CdO215FQPYP`P2P_P]PdPEPg%@S#@Rg#@,Q<1Q<g1Q<S5Y<5Y<g00I`'s=ah7PiPbPjPkPDPBPkP^PBPkPnPB1ImK,Hk9LknCACACAPCP8b5b8b9X0<X1<11\L%6:%61?:1L[[\f^0<^1<P9PlP@P1P>P?O5b4b6b7b:b3,r1EBO2EBPPPAPQPTC3PPPMPQPTC357OeWCWBX=JX?<XMRX2=P9CqX2=WKX@4XEIXDIP:P;P9O3W@XEIWDo"). Qed.
Lemma u64_at_frame M M' F a v : frame_but F M M' -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall i, a <= i < a + 8 -> outside F i) -> u64_at M a v -> u64_at M' a v.
Proof.
ltac2:(KReplay.run1 (kr_t_L5Defs ()) ["WithSegs"] "h04__x1h11xh22Hah31Fh41Mh52M'h67__arithh74__ffh87__sat10h96__sat9h:8__varmaph;5__with<4__x2h=1ah>1ih?1vh@1yhA2H8hB2HFhC2HihD3Hi0hE2HohF2HuhG1mhH1nhI1op;1p;3p;2p;4p;<p;6p;7p;9p;Bp;8p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000cR2p4p710p8P0P2p4p7210p8P0p1001@R2p4p710R3p8P0P2p4p7210R2p8P0p1001Tp4p710R0p8g00LOR4p606000R5P1p8P5p100MKp4p710p8P5p100Mhp4p710p8P5p100NEp4p710p8p10020p4p710R5P3p8P5P2p8P5P0p8g00:[j16Tg00N^j1HTg00O<j1ATg00O_j1@Tg0075j1;Tg00Qij3ZTg002bR0j20Tg00Y]j17Tg002ER5j21Tg00Z;j2RTg00ZXR2j22Tg00TVj25Tg00Pkj2KTg011oj3ITg00\fj2hTg003Xj13Tg00^[j4ETg012lj2XTg00_Lj2WTg00>Rj3CTg00^;R3j1BTg00d`j18Tg00e>j4VTg00mBl<GTg00fmj2STg00gUj3QTg0065j1OTg007Uj2=Tg008oj1NTg009Mj1MTg00:8j2<Tg00h9j2>Tg00;@j3LTg00h\j3PTg00A>j4:Tg00<Hj1TTg00<jj2iTg00=Lj2DTg00>lj3gTg00?Kj4FTg00ihj4fTg00i?j6]Tg00eaj4\Tg008Qj1[Tg0083j4YTg00mgj7^Tg00=fj2_Tg0144l9`Tg00X:j6aTg00l7l<bTg00l\lBcTg00Aij7dTg00C1j8eTg00CUR1f0R6'Dp=4g00nKR7P1P1P1P3P3f5R3f4R8f3R9f2R:f1R;P6M<bp=UP1P1P1P1P1P1P5P6P;P:P5P9P8P3f6R5f7R<f8R=f9R>MBcp=?P;g00DZR?g00E9R@P@g00EYRAP6g00F9Fdp=9P9P?P@P@PAP:P;P6Gep=Jg00JLRB#6RC#6#6RD#6#6#6RE#HRF#A%HD#ARG#@[RH%;4R4AZ:89g00L1RI/0:%7DRD,19%7CRJ%7ERE'RRK'01036113D,26'51K<;[^>1AI=38%;GRG#@RLp,4segsRMP>1hF5RNg00IA#3#3#3#3#3#3#3#3ROCE1XON,WG9CL6XILP6PMP=PNPOCEP>P=P<P8POP5P9%BORN,15RM/0K115DRL/0KP1P1P0P6X11RGP010;6#8X@1X11PMPLPGPGPGP1P1g010o11;6CV#4XG1XH1RLP5P5%45PNPDPGPG%B6#4X17POPD%4DEUROM:?PKPK%4KM<G1SJER712IJ10IE12IK[[RM10IJR0g011SRPAQJE;UW2RE10IK\P^20R0g00HURP#ORQ%;PRP1=1;%N1RR%M1RSP11<1BRB1>1D5L1RTg00D3RU1>1J=P1FC:,9SRF%T@RJPFCJ1iSARFP6P:g00K1RVg00KQRW'DRXAg1I;RICFb7b:b;X01116DRY/0K11;DRZ/0K[^01P6P>P3O2b6b9b8Cf10<611<N,26'5P9P;10=;R<11=NR>,2;RK'511=D,2;,5<R[P<PKP<PGPDO1RD,1=RK,2;%8<P1P1P2PGP212;6#8X@1X11P;P;%4;P>PKPGPGPGPLP=P=%4=PNPDPOM:?M<GE]P6C\P[P7PMPEP0PQPPP11=1:P;%[1CYPRPSPSP?P@P@PAP1PBPU1<1CRCC:,9SP1PCg00oNPTC:,9SF^RSPJPSCJPFP6P:PX1_6:=CVWdPICFb7b:b;X01X<1106;12;Y'510;:12:Z'5[^01^<1P6P3f<P9O3b6b9b8bDO2WCX>1M9`EaAI=53eWFWEWAW2WBX?1X=1X34X5HX4HP8P9P:P;P6O5X?1X=1W3X5HW4o"). Qed.
Lemma u8_at_frame M M' F a b : frame_but F M M' -> 0 <= a -> a + 1 <= 2 ^ 64 ->
  outside F a -> u8_at M a b -> u8_at M' a b.
Proof.
ltac2:(KReplay.run1 (kr_t_L5Defs ()) ["WithSegs"] "h04__x1h11xh22Hah31Fh41Mh52M'h67__arithh74__ffh86__sat2h96__sat3h:8__varmaph;5__with<4__x2h=1ah>1bh?1ih@1yhA1HhB2H1hC2HFhD2HihE3Hi0hF2HohG2HuhH1mhI1nhJ1op;1p;3p;2p;4p;<p;6p;7p;9p;Bp;8p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000cR2p4p710p8P0P2p4p7210p8P0p1001@R2p4p710R3p8P0P2p4p7210R2p8P0p1001Tp4p710R0p8g00LOR4p606000R5P1p8P5p100MKp4p710p8P5p100Mhp4p710p8P5p100NEp4p710p8p10020p4p710R5P3p8P5P2p8P5P0p8g00:[j14Tg00N^j1KTg00O<j1BTg00O_j1>Tg0075j19Tg00Qij3[Tg002bR0j20Tg00Y]j1;Tg002ER5j21Tg00Z;j2STg00Pkj2<Tg0154j3ITg00\fj2FTg003Xj1jTg00^[j4DTg0065j1GTg006Uj3ZTg00_Lj2YTg00>Rj36Tg00^;R2j1CTg00d`j1:Tg00e>j4VTg00mBl<@Tg00fmj2TTg00ZXR3j22Tg00gUj3RTg007Uj2?Tg008oj1QTg009Mj1OTg00:8j2=Tg00h9j2ETg00;@j3NTg00h\j3PTg00A>j45Tg00<Hj1MTg00<jj2iTg00=Lj2LTg00>lj3hTg00?Kj4HTg00ihj4gTg00TVj28Tg00i?j6fTg00eaj4eTg008Qj1bTg0083j4\Tg00mgj7]Tg00=fj2^Tg00cVj6_Tg0144l9`Tg00X:j6aTg00l7l<XTg00l\lBcTg00Aij7dTg00C1j8WTg00CUR1f0R6'Lp=3g00nKR7P1P1P1P2P2f5R2f4R8f3R9f2R:f1R;P6M<Xp=UP1P1P1P1P1P1P5P6P;P:P5P9P8P2f6R5f7R<f8R=f9R>MBcp=AP;g00DZR?g00E9R@P@g00EYRAP6g00F9Fdp=7P9P?P@P@PAP:P;P6GWp=Jg00JLRB#4RC#4#4RD#4#4#4RE#KRF#B%KDRD#BRG#>[RH%94R4A[:89g00L1RI/0:%;BRJ,19%;CRK%;ERE'SRL'01<28AI=28%9GRM#>RNp,4segsROP>1FF5RPg00IA#jRQCD1FD5%GG5ZG,YM96N6XJNP6POP=PPPQCDP>P=P<P8PQP5P9%CQRP,15RO/0L115JRN/0LP1P1P0P6X11RMP010;6#:X@1X11POPNPMPMPMP1P1g010o11;6CV#3XH1XI1RNP5P5%35PPPJPMPM%C6#3X17PQPJ%3JEURQM:APLPL%3LM<@1TKER712IK10IE12IL[[RO10IKR0g011SRGARKE;UW2RE10IL\G^20R0g00HURG#GRD%9GRG1?1;%Q1RR%O1RSP11=1BRB1E1J5N1RTg00D3RU1E1K=P1FC5,7SRF%M@RKPFCJ1iSARFP6P:g00K1RVg00KQRW'LRXAh1I;RICHb7b:b;X01116JRY/0L11;J/0L[^01P6P>P2O2b6b8b9Cg10<611<P,26'810=;R<11=PRL,2;RZ'811=J,2;,8<R[P<PZP<PMPJO1RJ,1=RZ,2;%:<P1P1P3PMP312;6#:X@1X11P;P;%3;PLPZPMPMPMPNP=P=%3=PPPJPQM:AM<@EfP6CeP[P7POPEP0PDPGP11?1:P;%b1C\PRPSPSP?P@P@PAP1PBPU1=1CRCC5,7SP1PCg00oNPTC5,7SF]PKP1PBg0160PCC5,7SCJPFP6P:PX1^6:=6VWdPICHb7b:b;X01X<1106;12;Y'8A61;:[^01^<1P6P2f<P9O3b6b8b9bEA61=;P1P>f;/<6X?1P8P:P6E_bAWDX?1M9`EaAI=52eWGWFWBW2WCX>1X=1X34X5HX4HP8P9P:P;P6O5X>1X=1W3X5HW4o"). Qed.
Lemma limbs_at_frame M M' F q ws : frame_but F M M' -> 0 <= q -> q + 8 * Z.of_nat (length ws) <= 2 ^ 64 ->
  (forall i, q <= i < q + 8 * Z.of_nat (length ws) -> outside F i) -> limbs_at M q ws -> limbs_at M' q ws.
Proof.
ltac2:(KReplay.run1 (kr_t_L5Defs ()) ["WithSegs"] "h04__x1h14__x2h24__x3h33Hi0h47__arithh54__ffh66__sat1h76__sat2h88__varmaph95__with:4cstrh;5cstr0h<1Fh=2Hah>1Mh?2M'h@4__x4hA1ihB1qhC2wshD2HFhE2HLhF2HhhG2HihH2HjhI2HohJ2HqhK1jp;1p;3p;2p;4p;:p;<p;7p;8p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000cR2p4p710p8P0P2p4p7210p8P0p1001@R2p4p710R3p8P0P2p4p7210R2p8P0p1001Tp4p710R0p8g00LOR4p606000R5P1p8P5p100MKp4p710p8P5p100Mhp4p710p8P5p100NEp4p710p8p10020p4p710R5P3p8P5P2p8P5P0p8g00:[j18Tg00N^j1UTg00O<j1OTg00O_j1[Tg0075j1MTg00Qij3kTg00Y]j1JTg00^;R0j10Tg016Wj29Tg002Ej21Tg00Z;j2WTg002bj26Tg00ZXR5j23Tg00TVj2CTg00Pkj2jTg0174j3PTg0183R2j2LTg018Kj4bTg00=Lj2<Tg00eaj4NTg00fHj1BTg00fmj2^Tg00gUj3]Tg003Xj1@Tg0047j2;Tg005Ij2?Tg018gj2\Tg0065j1ZTg006Uj3>Tg007Uj2ITg008Qj1YTg0083j4FTg008oj1XTg009Mj1VTg00h9j2GTg00:8j2ATg00<Hj1pTg019Sj3HTg00;@j3=Tg00<jj2oTg00=fj2nTg00>Rj3mTg00>lj3lTg00?Kj4iTg01:6j2hTg01:_j3KTg00;cj1dTg00h\j3cTg01;Hl:eTg01<Kj2aTg00mBl<fTg004`j3gTg00A>j4RTg00Aij7TTg00C1j8`Tg00mgj7_Tg00L1R3f0R1'6p=2g00CUR6/a1p=4g00nKR7P6P2P0P5g01<kf5R5f4R0f3R2f2R8f1R9P1M<fp=SAg691p=:P8g00DZR:g00E9R;P;g00EYR<P6P9g00D3P1CRg00F9R=FTp=5P2P:P;P;P<P8P9P1G`p=7P6P9g00oNP1CRp=DP9P:P;P;P<P1P=FTp=EP8P:P;P;P<P9P1F_p=Qg00JLR:#8R=#8R>#8R?#8#8#8R@#URA#O%U?#O#[[RB%M4R4%M6RCAk802%28%J?R?%48#0'9,12%J=RD%J@R@'WRE'61651%40#0,9?,15,31'Cf7RF/j9[^A6f8RG?P50f6RH#4,L1f;RIf:RJf9RK%09RL,9?,1GP6P9PFP3CbPH%4FRM,L9%0MRN,3LROP9PL1<6LPMPN1<6NESP1CNRNPO%B8RM%08RL#2RP%4KRQ#BRR%0QRS#2RT1^D@RU133D%2@133E[[RV%2DRWg011SRXA]D@9UW=R@%2E\X^=WRWg00HURXg00IARY#@RZ,;61;6YRY':R[%@ZRZ#@R\,;6R],:Yg00I`R^'?'\%ZXR_3>%MXR`P61I68RaP9%Y6RbCF%X6Rc%V6Rd1G63Re1A6=R=55d%p;R;Pd1A6:Rf95deP;1G6?Rg=H6=9=6fRh95deC7C71od<R<P1P8g00K1Rig00KQRj'<1n18=mijdAl639CiR3b5b8b9X06X16%29Rj19?2Ri,18Rk#2\j[^06^16P1%0FRjf>RlP0PIO4b4b6b7b;b:b3PNPOPMPPPRPTPUPVP@PW1h6?RT1;6ZRZ5K6/:[/?^=>X_P`P6PaP91I62RaCFPcPd%d:,A6R:,D=,EdP;PdAH6g:9=6fRR1G6D=c6ARA55dP;A=6hg=5dAC7C7P<P3b5b8b9X06X16X261398119i/6E11k?/6E[[^06^16^26P1f=#4#0PjPlP5PJO5b4b6b7b;b:b319?L,1KRL/6111L?,31'CP5P91L2Q%02RL/3SRJP2PL1<6LPQPS1<6SESP8CNPJ%B0%00#2%4IRI#B%0I#2PUPVP@PWAK6T]/:[/?^%@\,;69K6T1:ZY':/?^=>X_5>XP`P6P61I60P8PbCFP9PaCFPcPd1A6>R>95deP;Pd1D>:,EdP;PdAH6g>9=6fR>=5d=A=6>g,D=,Ed5QdP;A5df=1D=R,Ed5QdC7C7C7P<P3b5b8b9X06X16X26X@6%22130219?5R3,18R</6211<?,32'C16201123,30'C[[[^06^16^26^@6P1%0Kf?#4#0PFf@P0P5PHO7b4b6b7b;b:b3O2WHXK6P8P9P1O2M:eWGXA7APGH5eWEWIWFWJWDXCCXB6X<4X?BX>BP0P2P8P9P1O5WCXB6W<X?BW>o"). Qed.
Lemma defined_grows M M' a n : mem_grows M M' -> defined M a n -> defined M' a n.
Proof.
ltac2:(KReplay.run1 (kr_t_L5Defs ()) ["WithSegs"] "h01Mh12M'h21ah31nh41Dh51Gh62Hih71ip;1p;2p;3p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000cR2p4p710p8P0P2p4p7210p8P0p1001@R2p4p710R3p8P0P2p4p7210R2p8P0p1001Tp4p710R0p8p100LOp606000R4P1p8P4p100MKp4p710p8P4p100Mhp4p710p8P4p100NEp4p710p8p10020p4p710R4P3p8P4P2p8P4P0p8g00:[j10Tg00N^j13Tg00O<j12Tg00O_j14Tg01=Mj2:Tg01>Kj31Tg002bj29Tg00ZXj25Tg00TVj26Tg002Ej27Tg00\fj28Tg00JL#0#0#0R0#0#0#0#3R4#2%30#2#4[R0g00CUR2f3R3f2R1':f4R5f1R6711g00L1f0R7'91573'6P3f5/76,84P1P6P7O2O2W6X72A1531eW4W5X32X22X10X00P3P1P6P7O4X32W2X10W0o"). Qed.
Lemma writable_grows M M' a n : mem_grows M M' -> writable M a n -> writable M' a n.
Proof.
ltac2:(KReplay.run1 (kr_t_L5Defs ()) ["WithSegs"] "h01Mh12M'h21ah31nh41Gh52Hdh62Hkh71Wh81dh91kp;1p;2p;3p;7p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000cR2p4p710p8P0P2p4p7210p8P0p1001@R2p4p710R3p8P0P2p4p7210R2p8P0p1001Tp4p710R0p8p100LOp606000R4P1p8P4p100MKp4p710p8P4p100Mhp4p710p8P4p100NEp4p710p8p10020p4p710R4P3p8P4P2p8P4P0p8g00:[j10Tg00N^j15Tg00O<j12Tg00O_j16Tg01=Mj2:Tg01?Ij34Tg002bj23Tg00^;j19Tg002Ej21Tg00\fj28Tg01@Hj77Tg00JL#0#0#0R0#0#0#0#5R4#2%50#2#6[R0g00CUR2f3R3f2R1':f4R5f1R6741g00nKg00L1/36%96,11f5R7'3p,4segsP1f9f8f7/13,84P7P5P3P1P6f0R7O4F7W6W5W9X82A4531eW7W4X32X22X10X00P3P1P6P7O4X32W2X10W0o"). Qed.
Lemma writable_sub M a n a' n' : writable M a n -> a <= a' -> a' + n' <= a + n -> writable M a' n'.
Proof.
ltac2:(KReplay.run1 (kr_t_L5Defs ()) ["WithSegs"] "h04__x1h14__x2h24__x3h37__arithh44__ffh58__varmaph65__with74cstrh81Mh94__x4h:4__x5h;4__x6h<1ah=2a'h>1nh?2n'h@1HhA2H1hB2H2hC2HdhD2HkhE1WhF1dhG1khH1zp;1p;3p;2p;4p;6p;7p;8p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000cR2p4p710p8P0P2p4p7210p8P0p1001@R2p4p710R3p8P0P2p4p7210R2p8P0p1001Tp4p710R0p8p100LOp606000R4P1p8P4p100MKp4p710p8P4p100Mhp4p710p8P4p100NEp4p710p8p10020p4p710R4P3p8P4P2p8P4P0p8g00:[j14Tg00N^j1ETg00O<j1ATg00O_j1JTg01?Ij3FTg002bj21Tg002Ej20Tg00^;j1;Tg00fHj1@Tg0065j1MTg0075j1ITg007Uj27Tg0083j4<Tg008oj1[Tg009Mj1VTg00:8j25Tg01AJj3DTg00;cj1CTg00A>j4BTg00<jj2UTg00=Lj2STg00=fj2RTg00>Rj39Tg00>lj3QTg00?Kj4PTg01Amj28Tg00\fj2LTg01BJj4KTg003Xj1?Tg0047j2=Tg004`j3>Tg005Ij2NTg006Uj3HTg00h9j2OTg00<Hj1GTg008Qj1TTg00cVj6ZTg00;@j3YTg00Aij7XTg00C1j8WTg00CUR0f1R4f0R23Yp=2P4g00DZR3g00E9R1P1g00EYR5P2g00F9FXp=3P0P4g00D3P2CBp=6f3R6P3P1P1P5f2R3P4P2GWp=:g00JLR7#4R8#4R9#4R:#4#4#4#ER;#A%E:#A#J[R:f4R<?F6311<31063f5R=/0<'1g00nKg00L1R>/14%;4,03f6R?'1%@3%;3,1>g00HUR@#MRA%I@RBP01703P41706C<RC%[0RD%V0REP01507RF1508RG=D0F%C7R7,50RH'2'2g016012GHCB'31UE5R5P2P3g00K1RIg00KQRJ'S1R23=9IJdAQ0>4CPRKb4b5b6X00X10X201842/03,021043590^00^10^20P2P=f:RLf<RMO3b3b7f8RN/8L/06,0L10N6590P0f;ROf9RP/8O/0<RQ'0p,4segsf=RR1L;2P<CK=9IJXH0f7RJPQP6%@6RQ%;6,1>RIg00IAR;#?RS#?,=01=0S1=0;5>05>0g00I`'N=H@ARAPBPCPDPE1O0>RC/6H,3E%G1R1PE16GF,3EP1AD0FG/2HR@,6C,3EC:C:P5PKb4b5b6X00X10X2011>311341836/0<RC,1>[[^00^10^20P2P?PRPOP<PNO5b3b7PQPIPAPBP0P0170<P3170?C<P4P0170=P6%T0C<C<PDPE1509R9,2H%47,50R7'6,3EP1PE12F7%C8,50R8,2G'6,3EP112@9/68,3EC:C:P5PKb4b5b6X00X10X20X90X:0X;01036/1=104?103='110C=/1?[[^00^10^20^90^:0^;0P2PLPM%;=P?PRPOP6PJO8b3b7O410P<P2EZb@WDWCWGXF0AFJ<6eWBWAWEX?0X=0X>0X<0X8:P<P6P3P4P2O5X?0X=0X>0X<0W8o"). Qed.
Lemma defined_sub M a n a' n' : defined M a n -> a <= a' -> a' + n' <= a + n -> defined M a' n'.
Proof.
ltac2:(KReplay.run1 (kr_t_L5Defs ()) ["WithSegs"] "h04__x1h14__x2h24__x3h31Mh47__arithh54__ffh68__varmaph75__with84__x4h94__x5h:1ah;2a'h<1nh=2n'h>1Dh?1Hh@2H1hA2H2hB2HihC1ihD1zp;1p;3p;2p;4p;6p;7p;8p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000cR2p4p710p8P0P2p4p7210p8P0p1001@R2p4p710R3p8P0P2p4p7210R2p8P0p1001Tp4p710R0p8p100LOp606000R4P1p8P4p100MKp4p710p8P4p100Mhp4p710p8P4p100NEp4p710p8p10020p4p710R4P3p8P4P2p8P4P0p8g00:[j14Tg00N^j1ITg00O<j1ETg00O_j1NTg01>Kj3JTg002bj21Tg002Ej20Tg00ZXj2@Tg00TVj2?Tg0065j1QTg0075j1MTg007Uj2;Tg0083j4>Tg008oj1]Tg009Mj1ZTg00:8j26Tg01AJj3GTg00;cj1FTg00A>j4:Tg00<jj2VTg00=Lj2UTg00=fj2TTg00>Rj38Tg00>lj3STg00?Kj4RTg01Amj2<Tg00\fj2PTg00<Hj1BTg00T=j1OTg003Xj17Tg0047j25Tg004`j39Tg005Ij2CTg006Uj3DTg008Qj1LTg00h9j2KTg00cVj6\Tg00;@j3[Tg00Aij7YTg00mgj7WTg00C1j8XTg00CUR0f1R4f0R23[p=3P4g00DZR3g00E9R1P1g00EYR5P2g00F9FYp=2P0P4g00D3P2C:p==f2R6P3P1P1P5P4P2FWp=Hf3R7P3P1P1P5P6P4P2GXp=Ag00JLR3#4R8#4R9#4R:#4#4#4#IR;#E%I:#ER:#NR<[R=f4R>?J7611>61076f5R?/0>'1g00L1R@/121@2>'?g00HURA#QRB%MARCP01;06P41;07C>%]0RD%Z0REP01603RF1608RG=G0F%F3,60R3'3'3g016013G3C:'21VE5R5P2P6g00K1RHg00KQRI'U1T26=8HIdAS0@4CRRIb5b6b7X00X10X201<42/06,021046580^00^10^20P2P6f7RHf9RJO3b4f8RKf6RL/<K/04'010L4580P01<HJ/06RM,0Jf;1P;2O1%B:58<#OXD0P?PMg00IARM#7R<#7R:#7R;,50150:150MRM590590g00I`R:'C%7;,50150<=90M590/C:=DAB5DAPCP0P01;0>P6%L0RCC>P4P01;0?P7PCC>C>PDPE1K0@RD/=3,2EP0P3g00oNRC%F8,60R8C:,2E5HE%B1R1PE13F81609R9,3G'=,2EP1PE1=GF,2EP1AG0FG/33R3,=D,2EP0P3PCP9C:,2E5HECACACAP5PIb5b6b7X00X10X20X80X9011@61@6>'?104?106>'111761<7>/0?RI,1@1@IL'?[[[^00^10^20^80^90P2PHPJP7f:PKP6P>P?O8b4O210H6P2E\b?WBXC0AJH>7eWAW@W>X=0X;0X<0X:0X3=P>P7P6P4P2O5X=0X;0X<0X:0W3o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma regs_preserved_refl R : regs_preserved R R.
Proof.
ltac2:(KReplay.run1 (kr_t_L5Defs ()) ["WithSegs"] "h01Rh12_Hh21rp;1p;2p;3p-1R0g00RiR1p4p710R2p8P0p1000GR3p4p710p8P0P3p4p7210p8P0p1000cR3p4p710p8P0P3p4p7210p8P0p1001@R3p4p710R4p8P0P3p4p7210R3p8P0p1001Tp4p710R0p8p100LOp606000R5P2p8P5p100MKp4p710p8P5p100Mhp4p710p8P5p100NEp4p710p8p10020p4p710R5P4p8P5P3p8P5P0p8g00:[j10Tg00;cj19Tg00N^j12Tg00O<j11Tg01CJj28Tg00PAj27TP1j34Tg01D6j23Tg00=Lj25Tg01Dhj26Tg00JL#0R1#9#2R0%01#0#0#0#0#2#1R1'8R5%10g00CUf0R3,70g01Em34f2f1'3,51W1W21633eX05P3O1W0o"). Qed.
Lemma regs_preserved_trans R R' R'' : regs_preserved R R' -> regs_preserved R' R'' -> regs_preserved R R''.
Proof.
ltac2:(KReplay.run1 (kr_t_L5Defs ()) ["WithSegs"] "h01Rh12R'h23R''h31Ah41Bh52Hrh61bh71rp;1p;2p;3p;6p-1R0g00RiR1p4p710R2p8P0p1000GR3p4p710p8P0P3p4p7210p8P0p1000cR3p4p710p8P0P3p4p7210p8P0p1001@R3p4p710R4p8P0P3p4p7210R3p8P0p1001Tp4p710R0p8p100LOp606000R5P2p8P5p100MKp4p710p8P5p100Mhp4p710p8P5p100NEp4p710p8p10020p4p710R5P4p8P5P3p8P5P0p8g00:[j10Tg00;cj1:Tg00N^j13Tg00O<j12Tg01CJj29Tg01Dhj24Tg00PAj28TP1j36Tg01D6j21Tg00>Rj37Tg00X:j65Tg00JL#0R1#:#3R0%01#0#0#0#0#3#2R1'9R5f2R3f1R4'4R2%20g00CUf0R6,80g01Em36P1f5/14f7/139716X61f3P4P6O2f4R1/14P3P4P6O2E5W5W71413eX42W3X25X15X05P3P4P6O3X25X15W0o"). Qed.
(* [comment removed for export] *)
Definition ra_ok (r : Z) : Prop := 0 <= r < 2 ^ 47 /\ r mod 2 = 0.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive bstore : Type := BInl (v0 v1 : Z) | BDyn (cap : Z) (q : Z).
Record bigobj : Type := BO { bo_fb : Z; bo_len : nat; bo_st : bstore }.
Definition bo_dyn (b : bigobj) : bool := Z.testbit (bo_fb b) 0.
Definition bo_neg (b : bigobj) : bool := Z.testbit (bo_fb b) 1.
Definition bo_cap (b : bigobj) : Z := match bo_st b with BInl _ _ => 2 | BDyn c _ => c end.
(* [comment removed for export] *)
Definition bo_data (o : Z) (b : bigobj) : Z := match bo_st b with BInl _ _ => o + 16 | BDyn _ q => q end.

Definition big_at (M : word -> option byte) (o : Z) (b : bigobj) : Prop :=
  u8_at M o (bo_fb b) /\ 0 <= bo_fb b < 256 /\
  u64_at M (o + 8) (Z.of_nat (bo_len b)) /\
  match bo_st b with
  | BInl v0 v1 => Z.testbit (bo_fb b) 0 = false /\ u64_at M (o + 16) v0 /\ u64_at M (o + 24) v1 /\ (bo_len b <= 2)%nat
                  /\ 0 <= v0 < 2 ^ 64 /\ 0 <= v1 < 2 ^ 64
  | BDyn cap q => Z.testbit (bo_fb b) 0 = true /\ u64_at M (o + 16) cap /\ u64_at M (o + 24) q
                  /\ Z.of_nat (bo_len b) <= cap /\ 1 <= cap <= 2 ^ 27 /\ q mod 8 = 0 /\ 4096 <= q /\ q + 8 * cap <= 2 ^ 47
                  /\ hull_apart q (8 * cap)   (* [comment removed for export] *)
  end.
(* [comment removed for export] *)
Definition bo_with_len (b : bigobj) (n : nat) : bigobj := BO (bo_fb b) n (bo_st b).
Definition bo_with_fb (b : bigobj) (fb : Z) : bigobj := BO fb (bo_len b) (bo_st b).

(* [comment removed for export] *)
Lemma fb_dyn_nonneg fb : 0 <= fb < 256 -> fb mod 4 = 1 <-> (Z.testbit fb 0 = true /\ Z.testbit fb 1 = false).
Proof.
ltac2:(KReplay.run1 (kr_t_L5Defs ()) ["WithSegs"] "p'0h04__p1h17__arithh24__ffh38__varmaph45__with54__p2h66__sat5h74__x1h84__x2h94__x3h:4__x4h;6__sat8h<6__sat9h=1Hh>6__sat6h?2M2h@6__sat7hA1bi001bhB2M1hC4__x5hD2H0hE2H1hF3H10hG3H11hH3H12hI3H13hJ3H14hK3H15hL3H16hM3H17hN3H18hO3H19hP2H2hQ3H20hR2H3hS2H4hT2H5hU2H6hV2H7hW2H8hX2H9hY1qhZ2q0h[2q1h\1rh]2r0h^2r1h_4__p3h`6__sat3ha6__sat4hb2fbhc2B1hd2B2he2D1hf2D2hg2E4hh3Hfbhi1zp%0p&0p;1p;2p;3p;4p;6p;5p;7p;8p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000cR2p4p710p8P0P2p4p7210p8P0p1001@R2p4p710R3p8P0P2p4p7210R2p8P0p1001Tp4p710R0p8p100LOp606000R4P1p8P4p100MKp4p710p8P4p100Mhp4p710p8P4p100NEp4p710p8p10020p4p710R4P3p8P4P2p8P4P0p8g00:[j1?Tg00Y]j1VTg01G4k10@Tg01GRj2ATg00>Rj38Tg00=Lj2mTg01H3j22Tg0065j1}Tg0075j1yTg008Qj1uTg008oj1tTg009Mk10?Tg00h9j2]Tg00<jk20=Tg00=fk20<Tg00>lk30:Tg00?Kk408Tg002bj2QTg01HPk305Tg00X:j6ZTg00bOj21Tg00TVR0j23Tg00V_j2CTg01I3j1:Tg01IPj1pTg01Inj6vTg01JRj3jj2_Tg00ZXj24Tg01K3j3ij2eTg01KZj2TTg01LKj2^Tg003Xj1BTg01:6k20>Tg01:_j3fTg0047j2sTg01M<j1rTg01MZj2qTg01N;j3RTg018gk20;Tg007Uj2dTg00;cj1nTg00:8j2JTg00<Hk109Tg019Sj3OTg016Wj2[Tg002Ej2STg01Ndk603Tg01OEk402Tg00T=j1kTg01Oaj2bTg01PHj2aTg01Pnj2`Tg01QTk501Tg01R8k500Tg00VDj4XTg01R\j1lTg00cVj6~Tg00A>j4cTg00Aij7gTg004`j3|Tg005Ij2{Tg006Uk306Tg0083k407Tg00C1j8\Tg01S>j6zTg00mgj7oTg00;@j3xTg01Sbj6wTg00L1R4f0R2'Qp=0f2R3f1R1/42'3p=;P3g00DZR5g00E9R6P6g00EYR7g00CUR8P1g00D3P2Ccg00F9R9Fgp=>g00K1R:g00KQR;782p=KA8812p=7g01TFR<98:2p=NP3P5P6P6P7P8P1g0160P2CcP9Fgp=9A8824p=<f3R=1[31/S2588p=@P8P1g00oNP2Ccp=WP1P5P6P6P7P2P9Fgp=U1[31/S2p=h1s82p=LA|812p=6g00I`,{2p=Fg00HUR9@0612p=GP8P3P1P2H07p=Mf6R>P5P6P6P7f5R?f4R@P=P5P6P6P7P3P1P2G\G\p=5P1P5P6P6P7P2Ezp=IP3P5P6P6P7P1P2Fop=HAx812p=DP?P5P6P6P7P@P5P6P6P7P=P3FoP1P2G\p=P1S129883p>041[=3/S1=882p==P=P5P6P6P7P3P1P2G\p=EP3P5P6P6P1P2Ewp=Y%02RAg00JLRB#?RC#?RD#?#?#?#?#?#?#VRE7;2P:&0@4,A1%VBRF,A3S0098:2XA:1A1FRG,m:%VCRH,21/A4RI%}9RJ%y9R9%u8RK%t8RL&0?8RM1]84RN;>N20=M7ROP2P31m:;20<23#KdB0:841H08RPb2b3b41Q44P2b1:0514EZA8:IGP:123HRI/A4S01%VDRG,1=/7FRQ1A=4#K%N2RR'3'CXA:P:%:3RS%K212=HRT/A4#N'3,CQXA:P:%:I%:=#K/3R,CQXA:%p3113HS02P:P8PSPFP4n0100000020000'7%pT11THP:P8%:TPFP4n0100000020000'7PJP9PKPLPMP5P6P6P71]8HR7=9MNEvPOPPb2b3b4%<HRTg01Tf[P2b1RS9j@HP@PH12@H11@HRQC@12?HRR?jHSPRPH12RH11RHC@PJP9PKPL1WN7,UMPOPPb2b3b4144HRSP2b1RU9i>H11>HRV#0?;VHf7RW/2HRX?iHU11XHRX#0?;XHP8f8RX/2HRU/1H11XH5hHRY11XGRZPXPG12UHPY1TXHS03%0XRU%0HR[f:R\/1HR]#0[[S04f9R^/^HS05%0^R_f;R`/2HRa#0Rb\[[S0612\HRc/THS07%0cf<Rd/2HRe/1HRf#0\[[S081^aHS09f=Rg/2HRh/2HRi#0\[\bS0:p-0Rbg00IARj#BS0;#BRk#BRl#BRm#BRn#L20>8HRo%LkRk5f8S0<1s8jRj'6'6%Bn#B#B#L%rB,q8Rn%LlRl5R8S0='6,6j#F+0;%Lm9f8o16lj'6#F/GJ'GP91d8@Rm9MK31d8?9MK=Rp7M1PLPMPM%nBRq#?,J8Rr9>MNRs&096RtPMA>MN7RuPt1J8BRB9>MNRvF5PtPMPM1J8qRw9>MNRxPtPMPuPtPsF5PtPMPMPxPtPMPuPt1J8CRs9>MNF5PtPM1IMWRy1WB7,UM5HMPtPMPM1IMX1Ws7,UMPtPM%nq,J8Rq9O87Rz/DB99MrPtPM1IM^9HMxPtAO87B/DsRr9>MN1]8GR{,Wr,UM5HMF5EPF5F5POPPb2b3b4X78X88X98X:8XC8X0bX5bW_%0=R|%03S0>\[[%0>\[S0?\|%0@S0@%0?S0A\[S0B[A;X=HA;\?HPXPHP^P?C@13UgAhHWXRU#0?;UG[[[[[[[^78^88^98^:8^C8^0b^5b^_bP214gERU11gHR}#011hHR~#0PiPhPgP}P~P3P=P@P?P>PWPdO?b1b`bab6b>Q03Q04Q05Q06Q07Q08Q09Q0:Af8ol16kj'6#F%rC,q8S0:=R8lAR8nk/6j'6#F/GJ'GS09P9AMm3KS08?M1pPLPMPMPvPtPMPuPtA>MNqF5PtPMAO87s/Dw99MqPtPM1J8DRD,Dz99MBPtPMAHMvyPtAO8{sAO87wR7/DD'D99MBF5F5POPPb2b3b4X78X88X98X:8XC8X0bQ0?\AP?PHP3P=C@1[H>R{>043?13|XP@PGP?1S{WC@[[[[^78^88^98^:8^C8^0bP2PUPhP}P~PiPgP=PWPXPdO:b1b`bab6b>J03H0217ZYP812^H/1H11^H5hH172F%:\#K%:c#N'3'CXi8%:^P:P:11`HP:P8P2PFP4n0100000020000R`'7PHPf11dHPFC=%K1%:e#N'3'C]BP217]F%:aS0?P:P:17~`S07PHf>R`/2H/1H11`HPFC=RaA8:;;Re%N1S06'3'C]?P217fFS05PHP~P}PFC=R}A8:;<R~,3eRc[Pa\c1T`HRZ%0`f@R`/1H#0\[[RYf?Ri/^HRh%0ifA/2HRU#0R{\[[R|12`HRz/THRq%0zfBRz/2H/1H#0\[[Rp1^UHRUfCRm/2H/2H#0\[\{R{1TzGRj%0zS04%0GS03fDRC/1G#0[[RoQ0:=R8kQ0;#LS0;9R8n'6,6l#F/GJS0:P9Q081d8=7M1S08PLPMPMPvPtPMPuPtA>MNDCES0CCES0DPtPM1D7s1]8FR759MS0EPtPMA9Mw7S0FPtPMA9Ms7S0GPtPMPMPv1IM>S0HPtPyEPS0IF5F5POPPb2b3b4X78X88X98X:8X0bX5bQ0B\ARAPHP=P3PFC=Ry17@FRvQ0@/3XP\[S0@\v[[[^78^88^98^:8^0b^5bP2Pc14CES0J12CHRD11DHS0K11CHRuPCP@P>PWP^PmO;b1b6b>b@b;b<X=}PZPYPhP|PqPpPUP{PjPo1_mHS0L%kTS0MPCPHPDPuC@[S0N1eCHS0OfERl/1HRn#0?;nH\SS0P1blHS0Q14H4S0RfFRn/1HRk,4H1Qk4'3[S0S1anHS0TfGRn/2H#<\TS0U1`nHS0VfHRk/1H/7k\TS0W12kHS0XP8fI/1HS0YP81_1HS0ZQ0MP3PHPIQ02C@[S0M1e3HS0211=HRk#0?;kH\SS0[1b=HS0\Q0R14HQ1QQ4'3[S0R1a@HS0]%<R\TS0^1`?HS0_17V>\TS0`12>HS0aP811WHS0bP8fQRT/_GS0c%<GRV#kfRRRPG12RG11RGC@[S0d1eRGS0e144GfSRR/1GRQ#0?;QG[S0f1bRGS0g14G4fTRR/1GRQ,4G1QQ4'3[S0h1aRGS0ifURR/2G#<\VS0j1`RGS0kfVRQ/1G/7Q\VS0l12QGS0mP8fWRQ/1GS0nP8P0%0WS0o14WHS0pPHPXPiPFC=S0qfPS0r14\HR\P0Q0414zHS0sPHPdPmPFC=S0tPR%0CRd14lHRlP0f`Rz#0S0u14zES0vPHP`PnPFC=R`f_Rzfb#0Rifc/4EREPTP1O1RTQ03%0g[RgPRP3O1RVfM#0\[R[PQP=O1RQP[PJP9PKPLPMPM1IM3RSPMP5P6P6g01UCS03I01RkPMP5P6P6Q03I00R65YMS03Pt1IM=S0wEPPOPPb2b3b4X0bX5b132~P3[^0b^5bP2PHPnfNPFC=RnPefZR5O3b1b<b;b6WQWOP1P2O2n2001000000120000000WNWMP1P2O2n2001000000120000000WLXK_P1P2O2n2001000000121000000b^b[bJbIbHbGbFb]bZbXbWbVbUbTb\bYbSbRbPbEbDb6b>b@b;b<X=cCXW?%<fRfA8:<<Rc,3eRe\}Pa\ePJP9PKPLAYMkkAYM665HMPOPPb2b3b4PeP2b1X=}PZPYPhP|PqPpPUP{PjPoQ09P9Q08PLPMPMPxPtQ0CCEPtPMA9MBNPtPMQ0GPtPMQ0H9HMxPtA9Mr7F5F5POPPb2b3b4X78X88X98X:8X0bQ0>Q0B[%<117=FQ0A/3WPHP@P?PFC=[[[[^78^88^98^:8^0bP2Q0JPDPCPuQ0KP@PWP^PmO9b1b6b>b@b;b<X=eCXW?n0110000020101PXO1bAWB%<]Q0?P:P:Q07A8:<;R<Q06'3,Ca]?P2Q0513<~R~\}Pa\~PZPYPhP|PqPpPUP{PjPoQ0:P9Q08PLPMQ0DPtPMQ0EPtPMQ0FPtPMA9MsNPtQ0ICERsCEF5POPPb2b3b4X78X88X98X:8X0bX5b%<@R;Q0@[R:\v\y\A^78^88^98^:8^0b^5bP2P~Q0JPDQ0KPuPCP@P>PWP^PmO;b1b6b>b@b;b<X=}PZPYPhP|PqPpPUP{PjPoQ0LQ0NQ0OQ0PQ0QQ0SQ0TQ0UQ0VQ0WQ0XP8Q0YP8Q0ZQ0MQ02Q0[Q0\Q0RQ0]Q0^Q0_Q0`Q0aP8Q0bP8Q0cQ0dQ0eQ0fQ0gQ0hQ0iQ0jQ0kQ0lQ0mP8Q0nP8P0Q0oQ0pQ0qQ0rP0Q04Q0sQ0tPRP0Q0uQ0vP`PzPTPgPVP[PQP[PJP9PKPLPMPMAYM6kR6Q03PtPSEPPOPPb2b3b4X0bP1\~^0bP2PnP5O2b1b<b;b6XQEXOiP1P2O2n2001000000120000000XNlXMdP1P2O2n2001000000121000000XL\XK_P1P2O2n2001000000121000000b^b[bJbIbHbGbFb]bZbXbWbVbUbTb\bYbSbRbPbEbDb6b>b@b;b<X=~CXW?13<cR~\}Pa\~PZPYPhP|PqPpPUP{PjPoQ0=Q0<Q0;'6'6#F/GJP9Q08PLPMQ0DPtPMQ0EPtPMA9MwNPtPsCEF5POPPb2b3b4X78X88X98X:8X0bX5bP:\;\y\A^78^88^98^:8^0b^5bP2P~Q0JPDQ0KPuPCP@P>PWP^PmO;b1b6b>b@b;b<X=}PZPYPhP|PqPpPUP{PjPoQ0LQ0NQ0OQ0PQ0QQ0SQ0TQ0UQ0VQ0WQ0XP8Q0YP8Q0ZQ0MQ02Q0[Q0\Q0RQ0]Q0^Q0_Q0`Q0aP8Q0bP8Q0cQ0dQ0eQ0fQ0gQ0hQ0iQ0jQ0kQ0lQ0mP8Q0nP8P0Q0oQ0pQ0qQ0rP0Q04Q0sQ0tPRP0Q0uQ0vP`PzPTPgPVP[PQP[PJP9PKPLPMPMP6PSPtQ0wEPPOPPb2b3b4X0bX5b13<2P3[^0b^5bP2PnPcP5O3b1b<b;b6XQEXOiP1P2O2n2001000000120000000XNlXMdP1P2O2n2001000000120000000XL\XK_P1P2O2n2001000000121000000b^b[bJbIbHbGbFb]bZbXbWbVbUbTb\bYbSbRbPbEbDb6b>b@b;b<X=~CXX?fn0110000020101PXO1bAWBn0110000020101PWO1bA11^GP2EZbgbdbcbfbeb?bBQ01%lIEZ1A34%l3EZQ00P2E~b=WhXb8P2O1Xb8o"). Qed.

(* [comment removed for export] *)
Lemma land253_nonneg fb : 0 <= fb < 256 -> Z.testbit fb 1 = false -> Z.land fb 253 = fb.
Proof.
ltac2:(KReplay.run1 (kr_t_L5Defs ()) ["WithSegs"] "p'0h01Hh12Hih24__x1h33Hi1h43Hlth57__arithh64__ffh78__varmaph85__with94__p1h:1bh;1ih<2Hah=1ah>2fbh?1ni001nh@1si011shA2B1hB2HchC3HfbhD3HgehE6__sat0hF6__sat1hG1ei021ehH1zi031lp;1p;2p;6p;7p;4p;3p;9p;5p;8p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000cR2p4p710p8P0P2p4p7210p8P0p1001@R2p4p710R3p8P0P2p4p7210R2p8P0p1001Tp4p710R0p8p100LOp606000R4P1p8P4p100MKp4p710p8P4p100Mhp4p710p8P4p100NEp4p710p8p10020p4p710R4P3p8P4P2p8P4P0p8g00:[j17Tg00Y]j16Tg00ZXj22Tg00TVR0j2PTg01GRj20Tg00;cj1?Tg01Ucj2RTg01VAj2=Tg01V_j2[Tg00T=j18Tg01W?R4j2WTg00=Lj2JTg00X:j6Mj7ul9UTg01W_j2qTg002bj2<Tg0065j1eTg0075j1dTg007Uj2cTg008oj1`Tg009Mj1_Tg00:8j2^Tg00<Hj1]Tg01Inj6\Tg00h9j2QTg00A>j4ITg00<jj2ZTg00=fj2YTg00>Rj35Tg00>lj3XTg00?Kj4xTg01XFj1wTg00cVj6vTg00Z;j2LTg01H3j2NTg00bOj2OTg01Xej3tTg01S>j6pTg00fmj2oTg00gUj3gTg00N^j1fTg00h\j3hTg008Qj1iTg01YLj5jTg01Z3j5kTg00VDj4lTg01ZXj3mTg01[;j3nTg01[^j3bTg00Aij7TTg00BMj7aTg00C1j8rTg003>R2j2GTg00mgj7sTg00L1R3f0R1'<p=4g00K1R5g01TFR6751p=Hf1R7=551p=Ag00CUR8?571p=11Q81p=9P8P7g00oNP1CIp=KP7g00DZR9g00E9R:P:g00EYR;P1g00F9R<FTp=Ef2R=P9P:P:P;P8P7g0160P1CIP<FTp=:P=P9P:P:P;P7P1Fap=Cf3R<P9P:P:P;P=P7P1Grp=>A5813p=Bf4R>=58<A58=7/G1'Gp=31G71,G=p=VA58<=A5871'Gp=Dg00KQR?=551p=;1J51p=@P8f7R@f6RAf5RBP>P<P=P7P1M9Up=FP=P9P:P:P;P7P1Fsp=S%41RCg00JLRD#7RE#7RF#7RG#7#7#7#7#7#6RH,21RI'P%6DRJ,07#H%?DRK#?RL#?#?#?#7#?#6RM,R=P510>710M7RN'=10B=,A1X:51[7J117JRO%8ORP'WP411=JRQ%8Q10A<RQ10M<RR'=/AQP111<JRQP8PJf9RS/07RT/=N/AT^1CX;8%4JP5P610MJ,=1/A1X:51J56RTf8RN/0JPAEMW1P>P1P<FuWGP1O1%8Q%6GRQ,q>12>Q1<Q>'WP412BQ1<QB10SAR410MA'=/A4P112AQg00HUR4#eRU%d4R41c87RV%`8RW%_8RX1^8DRD%9QRY'K,EX%]:RZPXPXP9P:P:P;%9J9:XDE\PZPXP81Q83R[g00D3R\PDCI,EXR]PZA:XD[%6ER^#9R_9:XD%6KR`#99:XD%6FRF#99:XD%?E#6RE#99:XD%7K#6RK#99:XD%6LRL#99:XD5CX5CX5CX5CX5CX5CXC>C>C>1ZX;RaP1P=1J5?1Y1==55?dAX837CxRbb6b7b8X28121Qg01Tf\O%4=%B<11<^P<P`P<PFP<PEP<PK11<LD3D33V[[[^28P1PNP7P>P@O4b5%B@11@^P@P`P@PFP@PEP@PK11@LD3D33VP2%BNPNP^PNP`PNPFPNPEPNPKPNPLCDD3D310MSRO#;P1%BSP8P312=Q%;R]4^3P^1CX;8RP1<33A583J#8123Q10M3#@W4W3W1f:RRP1PSPAP<M9UW0P1O1PSP^PSP`PSPFPSPEPSPKPSPLCDD3D3P211R^PRP`PRPFPRPEPRPK11RLD3D3f;Rc,0M#;P111c^P^PP%4^Rd11^J#812^Q10M^#@W4W3W1f<ReP1PcPNPBGFW0P1O1PcP`PcPFPcPEPcPK11cLD3D3P211e`PePFPePEPePKPePLCDD3f=RB,0M#;P111B`P`PP%4`11`J#812`Q10M`#@W4W3W1f>R`P1PBPRP@GFW0P1O1PBPFPBPEPBPKPBPLCDD3P211`FP`PEP`PK11`LD3f?Rf,0M#;P111fFPFPP%4F11FJ#812FQ10MF#@W4W3W1f@RFP1PfPePSGFW0P1O1PfPEPfPK11fLD3P211FEPFPKPFPLCDfARf,0M#;P111fEPEPP%4E11EJ#812EQ10ME#@W4W3W1fBREP1PfP`PcGFW0P1O1PfPKPfPLCDP211EK11ELfCRE,0M#;P111EKPKPP%4K11KJ#812KQ10MK#@W4W3W1fDRKP1PEPFPBGFW0P1O111ELPLPP%4L11LJ#812LQ10ML#@W4W3W1PKP1PEPFPBGFW0P1O1n200100000021000010000W0P1O1n200100000021000011000W0P1O1n200100000021000011000W0P1O1n200100000021000011000W0P1O1n200100000021000011000W0P1O1n200100000021000011000bB10M@#;P5P?10eSR?/=1/A?X:510cNR?#w10MNP1Evb0W4P1O11<QAP010=7#H1L^=,N</O^#BR0[1L^7,N=/O^#B10<=#H[RA10><#H\0At=71P1n2001000000120000000VCX?8X=8PA\C^?8^=8P1PcPNPUP4PVPWPXP]PZP]C>PaPbb6b7b8X28%47RA\C^28P1PSPNO2b5P8P31O1^#BXH81J831L^NR0,Nc%4c12c0p-0RFPUP4PVPWPXPXP9P:P:P;P<EpR<9SX]PZP]C>PaPbb6b7b8X28W91PC7PA[^28^9FP112eHPePcO3b5Pc1L^QReP01o^Q123^RA%4Q123e[[g011SR3Ag^Q7UX<d%4e\3^<dPUP4PVPWPX%9H,KD,EX9SX<PZ%fG9h8_,KD,EXC>PaPbb6b7b8X28X9F1P7I127e[^28^9FP1%4`P`PBO3b5bEbFP^PQPNPUP4%i8PW1K[_,EXPaPbb6b7b8PAP1b5PUP4PVPWPXP8PYP\PDCI,EXRXPZPXC>PaPbb6b7b8X281<Q11<Q7[^28P1PSP=O2b5DjDkCl9mc0EMO4b010R@#HP5P61=1O/A1X:5PTP?P1EMb0WDP1O1n200110100021110311103b@W3P1O1n200110100021010211100b@1R>M/07An>M7EMX1CX;87b=WAWCX>8P1O1X>8o"). Qed.

Lemma land_byte_range a m : 0 <= m < 256 -> 0 <= Z.land a m < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_L5Defs ()) ["WithSegs"] "h07__arithh14__ffh28__varmaph35__with44__x1h51mh62Hah71ah81zh91Hh:2Hmh;6__sat0h<6__sat1p;1p;2p;3p;4p;8p;6p;7p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000cR2p4p710p8P0P2p4p7210p8P0p1001@R2p4p710R3p8P0P2p4p7210R2p8P0p1001Tp4p710R0p8p100LOp606000R4P1p8P4p100MKp4p710p8P4p100Mhp4p710p8P4p100NEp4p710p8p10020p4p710R4P3p8P4P2p8P4P0p8g00:[j10Tg00Y]j1:Tg00ZXj24Tg00TVj2;Tg00Z;j2VTg00bOj2=Tg00>Rj35Tg0065j1DTg0075j1CTg007Uj2BTg008oj1@Tg009Mj1?Tg00:8j2YTg00A>j48Tg00<jj2UTg00=Lj2TTg00=fj2OTg00>lj3MTg00?Kj4LTg00fmj2KTg00gUj3ETg00h9j27Tg00<Hj1FTg00N^j1GTg00h\j3HTg00C1j8ITg00\Cj3JTg00X:j66Tg01\Aj1ATg01Ucj22Tg008Qj1NTg01\_j3>Tg01K3j3PTg01]Bj3QTg00cVj6RTg002bj2STg00Aij7XTg00mgj7WTg00L1R0f0R4'Sp=3f1R2g00DZR3g00E9R1P1g00EYR5P4g00F9FXp=1g00CUR6P2g00oNP4C8p=9f2R7P3P1P1P5P2P4FWp=<%34g00JLR8#0R9#0#0R:#0#0#0#0#0#:R;,44';R<P6%:9R9%::R='VR>,=2R?A5647X86R@P6P2P@g00HUR@#DRA%C@R@1B62RB%@6RC%?6RDP61Y68R8g0160P8C8'11UD5REP4P7g00K1RFg00KQRG'T1O47=5FGdAM602CLRGb1b2b3X46A5644^46P4P7O1b0P?1K9=1409%3=R?140>[[%39RFg011SRHAE9=2UW6%3>\H^6FPAP@PBPCPDP3P1P1P5P61760R5g00D3R3P8C8,1DRB176;RF,98,1D5<D%F11769%G:5H6,98,1D9<DBGIPEPGb1b2b3X46%32142>';\<^46P4f4RBf3R8O2b0b;b<9J2>E6%A=R:,22R9PAP@%N6R1PCP6P5P3176=C8,1DPEPGb1b2b3P?P4b0R?9>2=E6A5692P6127:R912B4RB#314B;';X56P61287RB/2:R3P<X86R<P61=B>P<PAP@P1PC195F,1DPEPGb1b2b3140;P4b09PB;P3A>B=?E61289AQ87:E6P7P4ERb9W:X56X76P2P4O2X56X76o"). Qed.

(* [comment removed for export] *)
Fixpoint limbs_val (ws : list Z) : Z := match ws with [] => 0 | w :: r => w + 2 ^ 64 * limbs_val r end.

(* [comment removed for export] *)
Definition lstr_short (M : word -> option byte) (o : Z) (s : list Z) : Prop :=
  (length s <= 22)%nat /\ u8_at M o (2 * Z.of_nat (length s)) /\ bytes_at M (o + 1) s /\ u8_at M (o + 1 + Z.of_nat (length s)) 0.
Definition lstr_long (M : word -> option byte) (o : Z) (s : list Z) (w0 p : Z) : Prop :=
  Z.testbit w0 0 = true /\ u64_at M o w0 /\ u64_at M (o + 8) (Z.of_nat (length s)) /\ u64_at M (o + 16) p /\
  bytes_at M p s /\ u8_at M (p + Z.of_nat (length s)) 0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Context {SCFG_P : ScfgP}.
Lemma cps_of_msteps (fx fx' : FPState) R pc M R' pc' M' model K :
  m_halted model = None -> m_vm_lazy model = [] ->
  msteps segs (@mkst fx R pc M (seg_rom segs)) (@mkst fx' R' pc' M' (seg_rom segs)) ->
  srealizes segs SCFG (mkCfg (@mkst fx' R' pc' M' (seg_rom segs)) model) K ->
  srealizes segs SCFG (mkCfg (@mkst fx R pc M (seg_rom segs)) model) K.
Proof.
ltac2:(KReplay.run1 (kr_t_L5Defs ()) ["WithSegs"] "h01Kh11Mh22M'h31Rh42R'h52fxh63fx'h75modelh82pch93pc'h:2Hhh;2Hkh<2Hlh=3Hmsp;1p;2p;3p;5p;;p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000cR2p4p710p8P0P2p4p7210p8P0p1001@R2p4p710R3p8P0P2p4p7210R2p8P0p1001Tp4p710R0p8p100LOp606000R4P1p8P4p100MKp4p710p8P4p100Mhp4p710p8P4p100NEp4p710p8p10020p4p710R4P3p8P4P2p8P4P0p8g00:[j10Tg00;cj1CTg00N^j12Tg00O<j14Tg01CJj2BTg00O_j15Tg01]fj1;Tg00<Hj18Tg00>Rj33Tg01^]j27Tg0075j16Tg01_=j19Tg0065j1:Tg00_nj1ATg01`5j51Tg01`gj3@Tg01acj1<Tg01b[j2=Tg01cPj5>Tg01dNl;?Tg01eMR0g00JL#0R4#C#2%04#0R4#0#0#0#2#4R2'BR3%24#4#5\2R4g01fDR1g01g:R5%52f1R6#;%82331722R7#6f2R8#9%:733p,4segsR7f;R9f9R:f8R;f7R<%A7R=D1f:R>f6R?f5R@f4RAP=D13@p,3bmKRBP7p,6SCFG_P#<RCP9P<P?P@P=D1/=Af3RDD>PBP7PCf=P9P>P:P=D1f<P;P<P?P=D1P@PAPDP8P6f0R=M;?W;W=W<W:X05X71X24X92X43X14X82X33X60X50P:P;P<P?P@PAPDP8P6P=O:W0W7X24X92X43W1X82W3X60W5o"). Qed.

(* [comment removed for export] *)
Lemma run_cps (Q : FPState -> bvmap 5 word -> (word -> option byte) -> Prop) (fx : FPState) R pc M pc' model K :
  m_halted model = None -> m_vm_lazy model = [] ->
  (exists (fx' : FPState) R' M', msteps segs (@mkst fx R pc M (seg_rom segs)) (@mkst fx' R' pc' M' (seg_rom segs)) /\ Q fx' R' M') ->
  (forall (fx' : FPState) R' M', Q fx' R' M' -> srealizes segs SCFG (mkCfg (@mkst fx' R' pc' M' (seg_rom segs)) model) K) ->
  srealizes segs SCFG (mkCfg (@mkst fx R pc M (seg_rom segs)) model) K.
Proof.
ltac2:(KReplay.run1 (kr_t_L5Defs ()) ["WithSegs"] "p'0h02M'h12R'h23fx'h31Hh41Kh51Mh61Qh71Rh82fxh95modelh:2pch;3pc'h<2HKh=2HQh>2Hhh?2Hlh@3Hmsi001xp;1p;2p;3p;5p;>p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000cR2p4p710p8P0P2p4p7210p8P0p1001@R2p4p710R3p8P0P2p4p7210R2p8P0p1001Tp4p710R0p8p100LOp606000R4P1p8P4p100MKp4p710p8P4p100Mhp4p710p8P4p100NEp4p710p8p10020p4p710R4P3p8P4P2p8P4P0p8g00:[j15Tg00;cj1GTg00N^j16Tg00O<j17Tg01CJj2FTg00O_j19Tg01]fj1@Tg00<Hj1?Tg00>Rj38Tg01^]j2=Tg0075j1<Tg01_=j1;Tg0065j1:Tg00_nj1ETg01`5j50Tg00TVR0j24Tg01h4R4j21Tg01acj1CTg01hNl>ATg01`gj3BTg01b[j2>Tg01cPj5DTf6R2f5R3f4R1f3R5f2R6f1R7f0R8D03Bp=3P3P1P51>67P8DDp=2g01eMR9g00JL#5R:#G#6%5:#5R:#5#5#5#6#7R;'FR<%6:#7#9\;R:p-0[[[R=g01fDR>g01g:R?%9;%@7%?;381=;;R@#<%;6%:@38p,4segsR@f;RAf:RBf9RCf8RD%E@RED0RFP6P7f7RGP8PEF3f<RHP6P7P8O3'4X0:,1:X1<,1<X29,19P4P9P@PHPAPBPCPED0P6P7PDP8PEF3f=RIP6P7P8O3'4X0:,1:X1<,1<X29f>RJP6P7P8O3p,3bmKRKP@p,6SCFG_P#CRLP5P6PBP7PED0PCPDE2[^0:^1<^29PKP@PLPFP2P3E2[P8P@PJPIPHPAPED0P6P7PBP8PEF3f?RFP6P7P8O3'4X0:,1:X1<,1<P4P<P@PFPJPIPHPED0RMP5P7PAP8PEF3f@RNP5P7P8O3'4X0:,1:X1<fBROP6P7P8O3PKP@PLP5P6PJP7PED0PIPHE2[^0:^1<^29PKP@PLPMPBPCE2[P8P@fARMPNPFPJPED0P3P7PIP8PEF3POP3P7P8O3'4X0:,1:P4P:P@POPMPNPFPED0P2P6PJP8PEF3fCRFP2P6P8O3'4X0:fFR4P6P7P8O3PKP@PLP5P6POP7PED0PMPNE2[^0:^1<^29PKP@PLPFPOPMPNPED0PJPIE2[P8P@fDRIPFPOPMPED0PDP1PNP8PEF3fERNPDP1P8O3'4P0P@PNPIPFPOPED0PCP3PMP7PEF3P4PCP3P7O3fJRCP6P7P8O3PKP@PLP5P6P4P7PED0PNPIE2[^0:^1<^29PKP@PLfGR0P4PNPIPED0RPPOPME2[P8P@PPPAPGPFP5PEF3fIRAPHPDP1O3fMP6P7P8O3PKP@PLP5P6PAP7PED0fHREP0E2[^0:^1<^29PCPJPAPEP0PBP4P2PNPIPFPOP6P8PJPBP2P7O4M>AW<W=W@P7P8O2n2001000000120000000W3X0:P7P8O2n2001000000121100000W3X1<P7P8O2n2001000000121100000W3X29P7P8O2n2001000000121100000W3W?W>X4?X9>X;;X5:X:;X7<X89X6=PGP2P3P1P5P6P7P8O8W4W9X;;X5:X:;X7<X89W6o"). Qed.

End WithSegs.
End L5.

End L5Defs.
