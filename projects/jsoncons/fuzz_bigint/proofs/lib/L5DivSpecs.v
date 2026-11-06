(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreSpecs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module L5DS.
Import L5CS.
Abbreviation RSEGS := Plain.M.loaded_segments.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Definition GP : Z := 67584.

(* [comment removed for export] *)
Definition A0 : Z := 0x16af9c0daf145395.
Definition A1 : Z := 0x2a9f3636273caaf2.

(* [comment removed for export] *)
Definition OPMOD : Z := 0x21cf0.          (* [comment removed for export] *)
Definition OPMOD1_RET : Z := 0x20600.     (* [comment removed for export] *)
Definition OPMOD2_RET : Z := 0x20644.     (* [comment removed for export] *)
Definition TOP_PAD : Z := 0x20798.        (* [comment removed for export] *)
Definition ZERO_THROW : Z := 0x22350.     (* [comment removed for export] *)
Definition ASSERT_THROW : Z := 0x21470.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition SCR_OPMOD : Z := 10240.

(* [comment removed for export] *)
Definition credit_for (L : heap_layout) (cr : credit) (k bytes : Z) : Prop :=
  k * hl_k_per_malloc L <= fst cr /\ bytes + k * hl_b_overhead L <= snd cr.
Definition credit_after (L : heap_layout) (cr : credit) (k bytes : Z) (cr' : credit) : Prop :=
  fst cr - k * hl_k_per_malloc L <= fst cr' /\ snd cr - (bytes + k * hl_b_overhead L) <= snd cr'.
(* [comment removed for export] *)
Definition OPMOD1_K : Z := 16.
Definition opmod1_bytes (capb : Z) : Z := 8 * capb + 1536.
Definition OPMOD2_K : Z := 12.
Definition opmod2_bytes (capy : Z) : Z := 24 * capy + 1024.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition reduced (ws : list Z) : Prop := ws = [] \/ nth (length ws - 1) ws 0 <> 0.

Definition U (R : bvmap 5 word) (k : Z) : Z := bv_unsigned (getr R (Z_to_bv 5 k)).

(* [comment removed for export] *)
Definition DIVIDE : Z := 0x21d80.
Definition UNNORM : Z := 0x22790.
Definition OPDIV : Z := 0x22b08.          (* [comment removed for export] *)
Definition SHR : Z := 0x22b98.            (* [comment removed for export] *)
Definition RESIZE_RET1 : Z := 0x210e0.    (* [comment removed for export] *)
Definition DIVN_RESIZE_RET : Z := 0x22100. (* [comment removed for export] *)
Definition DIVN_RET : Z := 0x22b38.       (* [comment removed for export] *)
Definition DIVEQ_RET : Z := 0x227d0.      (* [comment removed for export] *)
Definition UNNORM_RET : Z := 0x22280.     (* [comment removed for export] *)
Definition MAX_SIZE : Z := 2 ^ 61 - 1.    (* [comment removed for export] *)
Definition MWORD : Z := 2 ^ 64 - 1.       (* [comment removed for export] *)
Definition DIV_SCR : Z := 304 + (64 + (48 + RESIZE_SCR)).   (* [comment removed for export] *)
Definition DIVEQ_SCR : Z := 48 + DIV_SCR.
Definition UNNORM_SCR : Z := 64 + DIVEQ_SCR.                 (* [comment removed for export] *)

(* [comment removed for export] *)
Definition div_saves (M : word -> option byte) (sp : Z) (R : bvmap 5 word) : Prop :=
     L5.u64_at RSEGS M (sp - 8) (U R 1) /\ L5.u64_at RSEGS M (sp - 16) (U R 8) /\ L5.u64_at RSEGS M (sp - 24) (U R 9)
  /\ L5.u64_at RSEGS M (sp - 32) (U R 18) /\ L5.u64_at RSEGS M (sp - 40) (U R 19) /\ L5.u64_at RSEGS M (sp - 48) (U R 20)
  /\ L5.u64_at RSEGS M (sp - 56) (U R 21) /\ L5.u64_at RSEGS M (sp - 64) (U R 22) /\ L5.u64_at RSEGS M (sp - 72) (U R 23)
  /\ L5.u64_at RSEGS M (sp - 80) (U R 24) /\ L5.u64_at RSEGS M (sp - 88) (U R 25) /\ L5.u64_at RSEGS M (sp - 96) (U R 26)
  /\ L5.u64_at RSEGS M (sp - 104) (U R 27).

(* [comment removed for export] *)
Definition mword_obj (M : word -> option byte) (dv fdv : Z) : Prop :=
  L5.big_at RSEGS M dv (L5.BO fdv 1 (L5.BInl MWORD 0)) /\ Z.testbit fdv 1 = false.
(* [comment removed for export] *)
Definition zero_obj (M : word -> option byte) (o : Z) : Prop := L5.big_at RSEGS M o (L5.BO 0 0 (L5.BInl 0 0)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition resize_huge_at (M M' : word -> option byte) (R R' : bvmap 5 word) (o sp n : Z) (b : L5.bigobj) : Prop :=
     getr R' 2%bv = Z_to_bv 64 (sp - 128) /\ getr R' 3%bv = getr R 3%bv /\ getr R' 4%bv = getr R 4%bv
  /\ getr R' 1%bv = Z_to_bv 64 RESIZE_RET1
  /\ getr R' 8%bv = Z_to_bv 64 o /\ getr R' 9%bv = Z_to_bv 64 n /\ getr R' 18%bv = Z_to_bv 64 (Z.of_nat (L5.bo_len b))
  /\ getr R' 19%bv = getr R 19%bv /\ getr R' 20%bv = getr R 20%bv /\ getr R' 21%bv = getr R 21%bv /\ getr R' 22%bv = getr R 22%bv
  /\ getr R' 23%bv = getr R 23%bv /\ getr R' 24%bv = getr R 24%bv /\ getr R' 25%bv = getr R 25%bv /\ getr R' 26%bv = getr R 26%bv
  /\ getr R' 27%bv = getr R 27%bv
  /\ getr R' 10%bv = Z_to_bv 64 16 /\ getr R' 11%bv = Z_to_bv 64 n /\ getr R' 12%bv = Z_to_bv 64 MAX_SIZE
  /\ L5.u64_at RSEGS M' (sp - 8) (U R 1) /\ L5.u64_at RSEGS M' (sp - 16) (U R 8)
  /\ L5.u64_at RSEGS M' (sp - 24) (U R 9) /\ L5.u64_at RSEGS M' (sp - 32) (U R 18)
  /\ L5.u64_at RSEGS M' (sp - 72) RESIZE_RET1 /\ L5.u64_at RSEGS M' (sp - 80) o /\ L5.u64_at RSEGS M' (sp - 88) n
  /\ L5.u64_at RSEGS M' (sp - 96) (Z.of_nat (L5.bo_len b))
  /\ L5.u64_at RSEGS M' (sp - 104) (U R 19) /\ L5.u64_at RSEGS M' (sp - 112) (U R 20) /\ L5.u64_at RSEGS M' (sp - 120) (U R 21)
  /\ L5.frame_but [(sp - 128, 128)] M M' /\ mem_grows M M'.

Definition resize_huge_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (o sp n : Z) (b : L5.bigobj),
    m_halted model = None -> m_vm_lazy model = [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 n -> MAX_SIZE <= n < 2 ^ 64 ->
    getr R 2%bv = Z_to_bv 64 sp -> 0x7fff7f800000 + 128 <= sp -> sp <= 2 ^ 47 -> L5.defined M (sp - 128) 128 ->
    L5.big_at RSEGS M o b -> L5.bo_dyn b = true -> 0 <= o -> o + 32 <= 2 ^ 47 -> (o + 32 <= sp - 128 \/ sp <= o) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte),
        resize_huge_at M M' R R' o sp n b -> srealizes RSEGS SCFG (cfg R' ASSERT_THROW M' model) K) ->
    srealizes RSEGS SCFG (cfg R RESIZE M model) K.

Section DivSpecs.
Variable L : heap_layout.
Variable HI : heap_iface.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition DIVN_K : Z := 3.
Definition DIVN_BYTES : Z := 192.

(* [comment removed for export] *)
Definition divN_post (LB : list (Z * Z)) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (X qX rr dv fdv sp : Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R'
  /\ (exists fbq nq wq, L5.big_at RSEGS M' X (L5.BO fbq nq (L5.BDyn 8 qX)) /\ L5C.obj_limbs RSEGS M' (L5.BO fbq nq (L5.BDyn 8 qX)) wq
                       /\ Z.testbit fbq 1 = false /\ (nq <= 6)%nat /\ L5.defined M' qX 64)
  /\ (exists fbr nr str wr, L5.big_at RSEGS M' rr (L5.BO fbr nr str) /\ L5C.obj_limbs RSEGS M' (L5.BO fbr nr str) wr /\
        match str with
        | L5.BInl _ _ => LB' = LB
        | L5.BDyn cap q => cap = 8 /\ LB' = (q, 64) :: LB /\ L5C.fresh_block L LB M' q 64
        end)
  /\ mword_obj M' dv fdv
  /\ credit_after L cr DIVN_K DIVN_BYTES cr'
  /\ L5C.hpres L LB sp DIV_SCR [(X, 32); (qX, 64); (rr, 32)] M M'.

(* [comment removed for export] *)
Definition divN_e3 (LB : list (Z * Z)) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (X qX : Z) (lenX : nat) (rr dv sp : Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  exists (B0 B1 n fd0 fn0 fn fden : Z),
  (* [comment removed for export] *)
     getr R' 2%bv = Z_to_bv 64 (sp - 432) /\ getr R' 3%bv = getr R 3%bv /\ getr R' 4%bv = getr R 4%bv
  /\ getr R' 1%bv = Z_to_bv 64 RESIZE_RET1 /\ getr R' 10%bv = Z_to_bv 64 16 /\ getr R' 11%bv = Z_to_bv 64 n /\ getr R' 12%bv = Z_to_bv 64 MAX_SIZE
  /\ n = 2 ^ 64 - 1
  /\ getr R' 8%bv = Z_to_bv 64 X /\ getr R' 9%bv = Z_to_bv 64 n /\ getr R' 18%bv = Z_to_bv 64 (Z.of_nat lenX)
  /\ getr R' 19%bv = Z_to_bv 64 0 /\ getr R' 20%bv = Z_to_bv 64 (sp - 120) /\ getr R' 21%bv = Z_to_bv 64 1
  /\ getr R' 22%bv = Z_to_bv 64 B1 /\ getr R' 23%bv = Z_to_bv 64 qX /\ getr R' 24%bv = Z_to_bv 64 (X + 16)
  /\ getr R' 25%bv = getr R 25%bv /\ getr R' 26%bv = Z_to_bv 64 0 /\ getr R' 27%bv = Z_to_bv 64 rr
  (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M' (sp - 312) DIVN_RESIZE_RET /\ L5.u64_at RSEGS M' (sp - 320) 0 /\ L5.u64_at RSEGS M' (sp - 328) X /\ L5.u64_at RSEGS M' (sp - 336) X
  /\ L5.u64_at RSEGS M' (sp - 376) RESIZE_RET1 /\ L5.u64_at RSEGS M' (sp - 384) X /\ L5.u64_at RSEGS M' (sp - 392) n
  /\ L5.u64_at RSEGS M' (sp - 400) (Z.of_nat lenX) /\ L5.u64_at RSEGS M' (sp - 408) 0 /\ L5.u64_at RSEGS M' (sp - 416) (sp - 120)
  /\ L5.u64_at RSEGS M' (sp - 424) 1
  (* [comment removed for export] *)
  /\ div_saves M' sp R
  /\ L5.u8_at RSEGS M' (sp - 232) fd0 /\ 0 <= fd0 < 256 /\ Z.testbit fd0 0 = false                         (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M' (sp - 224) 1 /\ L5.u64_at RSEGS M' (sp - 216) MWORD /\ L5.u64_at RSEGS M' (sp - 208) 0
  /\ L5.u8_at RSEGS M' (sp - 200) fn0 /\ 0 <= fn0 < 256 /\ Z.testbit fn0 0 = true                          (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M' (sp - 192) (Z.of_nat lenX) /\ L5.u64_at RSEGS M' (sp - 184) 8 /\ L5.u64_at RSEGS M' (sp - 176) B0
  /\ L5.u8_at RSEGS M' (sp - 168) fn /\ 0 <= fn < 256 /\ Z.testbit fn 0 = true /\ Z.testbit fn 1 = false   (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M' (sp - 160) 0 /\ L5.u64_at RSEGS M' (sp - 152) 8 /\ L5.u64_at RSEGS M' (sp - 144) B1
  /\ L5.u8_at RSEGS M' (sp - 136) fden /\ 0 <= fden < 256 /\ Z.testbit fden 0 = false /\ Z.testbit fden 1 = false  (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M' (sp - 128) 1 /\ L5.u64_at RSEGS M' (sp - 120) MWORD /\ L5.defined M' (sp - 112) 8   (* [comment removed for export] *)
  /\ L5.u32_at RSEGS M' (sp - 236) 0 /\ L5.u64_at RSEGS M' (sp - 256) 0 /\ L5.u64_at RSEGS M' (sp - 264) (X + 16) /\ L5.u64_at RSEGS M' (sp - 296) 0
  (* [comment removed for export] *)
  /\ LB' = (B0, 64) :: (B1, 64) :: LB /\ L5C.fresh_block L LB M' B1 64 /\ L5C.fresh_block L ((B1, 64) :: LB) M' B0 64
  /\ cr' = debit L (debit L cr 64) 64
  (* [comment removed for export] *)
  /\ L5C.hpres L LB sp DIV_SCR [] M M'.

Definition divN_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (X qX rr dv fdv sp r : Z) (bX : L5.bigobj) (wX : list Z),
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 X -> getr R 11%bv = Z_to_bv 64 dv -> getr R 12%bv = Z_to_bv 64 X -> getr R 13%bv = Z_to_bv 64 rr ->
    getr R 14%bv = Z_to_bv 64 0 ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 3%bv = Z_to_bv 64 GP -> getr R 4%bv = Z_to_bv 64 TP -> L5C.stk (hl_sptop L) M sp DIV_SCR ->
    L5.img_clear M 0x10000 0x20000 ->
    (* [comment removed for export] *)
    L5.big_at RSEGS M X bX -> L5C.obj_limbs RSEGS M bX wX -> L5.bo_st bX = L5.BDyn 8 qX -> (2 <= L5.bo_len bX <= 6)%nat ->
    Z.testbit (L5.bo_fb bX) 1 = false -> In (qX, 64) LB -> L5.defined M qX 64 ->
    X mod 8 = 0 -> sp <= X -> X + 32 <= hl_sptop L -> L5.defined M X 32 ->
    (* [comment removed for export] *)
    mword_obj M dv fdv -> dv mod 8 = 0 -> sp <= dv -> dv + 32 <= hl_sptop L ->
    zero_obj M rr -> rr mod 8 = 0 -> sp <= rr -> rr + 32 <= hl_sptop L -> L5.defined M rr 32 ->
    (X + 32 <= dv \/ dv + 32 <= X) -> (X + 32 <= rr \/ rr + 32 <= X) -> (dv + 32 <= rr \/ rr + 32 <= dv) ->
    credit_for L cr DIVN_K DIVN_BYTES ->
    (* [comment removed for export] *)
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
        divN_post LB cr M M' R R' X qX rr dv fdv sp LB' cr' ->
        model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    (* [comment removed for export] *)
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
        divN_e3 LB cr M M' R R' X qX (L5.bo_len bX) rr dv sp LB' cr' ->
        model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' ASSERT_THROW M' model') K) ->
    srealizes RSEGS SCFG (cfg R DIVIDE M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition diveq_post (LB : list (Z * Z)) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (X qX dv fdv sp : Z) (cr' : credit) : Prop :=
  regs_preserved R R' /\ getr R' 10%bv = Z_to_bv 64 X
  /\ (exists fbq nq wq, L5.big_at RSEGS M' X (L5.BO fbq nq (L5.BDyn 8 qX)) /\ L5C.obj_limbs RSEGS M' (L5.BO fbq nq (L5.BDyn 8 qX)) wq
                       /\ Z.testbit fbq 1 = false /\ (nq <= 6)%nat /\ L5.defined M' qX 64)
  /\ mword_obj M' dv fdv
  /\ credit_after L cr DIVN_K DIVN_BYTES cr'
  /\ L5C.hpres L LB sp DIVEQ_SCR [(X, 32); (qX, 64)] M M'.

(* [comment removed for export] *)
Definition diveq_e3 (LB : list (Z * Z)) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (X qX : Z) (lenX : nat) (dv sp : Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  exists (RN : bvmap 5 word) (MN : word -> option byte),      (* [comment removed for export] *)
     getr RN 1%bv = Z_to_bv 64 DIVN_RET /\ getr RN 2%bv = Z_to_bv 64 (sp - 48) /\ getr RN 8%bv = Z_to_bv 64 X
  /\ getr RN 3%bv = getr R 3%bv /\ getr RN 4%bv = getr R 4%bv /\ getr RN 9%bv = getr R 9%bv
  /\ (forall k, 18 <= k <= 27 -> getr RN (Z_to_bv 5 k) = getr R (Z_to_bv 5 k))
  /\ divN_e3 LB cr MN M' RN R' X qX lenX (sp - 48) dv (sp - 48) LB' cr'
  /\ L5.u64_at RSEGS M' (sp - 8) (U R 1) /\ L5.u64_at RSEGS M' (sp - 16) (U R 8)
  /\ zero_obj M' (sp - 48)
  /\ L5C.hpres L LB sp DIVEQ_SCR [] M M'.      (* [comment removed for export] *)

Definition diveq_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (X qX dv fdv sp r : Z) (bX : L5.bigobj) (wX : list Z),
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 X -> getr R 11%bv = Z_to_bv 64 dv ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 3%bv = Z_to_bv 64 GP -> getr R 4%bv = Z_to_bv 64 TP -> L5C.stk (hl_sptop L) M sp DIVEQ_SCR ->
    L5.img_clear M 0x10000 0x20000 ->
    L5.big_at RSEGS M X bX -> L5C.obj_limbs RSEGS M bX wX -> L5.bo_st bX = L5.BDyn 8 qX -> (2 <= L5.bo_len bX <= 6)%nat ->
    Z.testbit (L5.bo_fb bX) 1 = false -> In (qX, 64) LB -> L5.defined M qX 64 ->
    X mod 8 = 0 -> sp <= X -> X + 32 <= hl_sptop L -> L5.defined M X 32 ->
    mword_obj M dv fdv -> dv mod 8 = 0 -> sp <= dv -> dv + 32 <= hl_sptop L ->
    (X + 32 <= dv \/ dv + 32 <= X) ->
    credit_for L cr DIVN_K DIVN_BYTES ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) cr',
        diveq_post LB cr M M' R R' X qX dv fdv sp cr' ->
        model_but_vm model model' -> hi_heap HI LB cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
        diveq_e3 LB cr M M' R R' X qX (L5.bo_len bX) dv sp LB' cr' ->
        model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' ASSERT_THROW M' model') K) ->
    srealizes RSEGS SCFG (cfg R OPDIV M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition unnorm_post (LB : list (Z * Z)) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (X sp : Z) (bX : L5.bigobj) (cr' : credit) : Prop :=
  regs_preserved R R'
  /\ (exists fb' n' st' w', L5.big_at RSEGS M' X (L5.BO fb' n' st') /\ L5C.obj_limbs RSEGS M' (L5.BO fb' n' st') w'
        /\ Z.testbit fb' 1 = false
        /\ match L5.bo_st bX, st' with
           | L5.BDyn cap q, L5.BDyn cap' q' => cap' = cap /\ q' = q /\ L5.defined M' q (8 * cap)
           | L5.BInl _ _, L5.BInl _ _ => True
           | _, _ => False end)
  /\ credit_after L cr DIVN_K DIVN_BYTES cr'
  /\ L5C.hpres L LB sp UNNORM_SCR [(X, 32); (L5.bo_data X bX, 8 * L5.bo_cap bX)] M M'.

Definition unnorm_e3 (LB : list (Z * Z)) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (X qX : Z) (lenX : nat) (sp : Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  exists (RQ : bvmap 5 word) (MQ : word -> option byte),      (* [comment removed for export] *)
     getr RQ 1%bv = Z_to_bv 64 DIVEQ_RET /\ getr RQ 2%bv = Z_to_bv 64 (sp - 64) /\ getr RQ 8%bv = Z_to_bv 64 X /\ getr RQ 9%bv = getr R 12%bv
  /\ getr RQ 3%bv = getr R 3%bv /\ getr RQ 4%bv = getr R 4%bv
  /\ (forall k, 18 <= k <= 27 -> getr RQ (Z_to_bv 5 k) = getr R (Z_to_bv 5 k))
  /\ diveq_e3 LB cr MQ M' RQ R' X qX lenX (sp - 56) (sp - 64) LB' cr'
  /\ L5.u64_at RSEGS M' (sp - 8) (U R 1) /\ L5.u64_at RSEGS M' (sp - 16) (U R 8) /\ L5.u64_at RSEGS M' (sp - 24) (U R 9)
  /\ L5.u8_at RSEGS M' (sp - 56) 0 /\ L5.u64_at RSEGS M' (sp - 48) 1 /\ L5.u64_at RSEGS M' (sp - 40) MWORD /\ L5.u64_at RSEGS M' (sp - 32) 0
  /\ L5C.hpres L LB sp UNNORM_SCR [] M M'.     (* [comment removed for export] *)

Definition unnorm_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (X xs sd sp r : Z) (bX : L5.bigobj) (wX : list Z),
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R 11%bv = Z_to_bv 64 X -> getr R 12%bv = Z_to_bv 64 xs -> 0 <= xs <= 63 -> getr R 13%bv = Z_to_bv 64 sd -> (sd = 0 \/ sd = 1) ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 3%bv = Z_to_bv 64 GP -> getr R 4%bv = Z_to_bv 64 TP -> L5C.stk (hl_sptop L) M sp UNNORM_SCR ->
    L5.img_clear M 0x10000 0x20000 ->
    L5.big_at RSEGS M X bX -> L5C.obj_limbs RSEGS M bX wX -> (1 <= L5.bo_len bX <= 299)%nat -> Z.testbit (L5.bo_fb bX) 1 = false ->   (* [comment removed for export] *)
    X mod 8 = 0 -> sp <= X -> X + 32 <= hl_sptop L -> L5.defined M X 32 ->
    (forall cap q, L5.bo_st bX = L5.BDyn cap q -> In (q, 8 * cap) LB /\ L5.defined M q (8 * cap)) ->
    (sd = 1 -> exists qX, L5.bo_st bX = L5.BDyn 8 qX /\ (2 <= L5.bo_len bX <= 6)%nat) ->
    (sd = 1 -> credit_for L cr DIVN_K DIVN_BYTES) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) cr',
        unnorm_post LB cr M M' R R' X sp bX cr' ->
        model_but_vm model model' -> hi_heap HI LB cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) qX LB' cr',
        sd = 1 -> L5.bo_st bX = L5.BDyn 8 qX ->
        unnorm_e3 LB cr M M' R R' X qX (L5.bo_len bX) sp LB' cr' ->
        model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' ASSERT_THROW M' model') K) ->
    srealizes RSEGS SCFG (cfg R UNNORM M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SHRZ_SCR : Z := 48 + RESIZE_SCR.
Definition shrz_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (X k sp r fb : Z) (st : L5.bstore),
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 X -> getr R 11%bv = Z_to_bv 64 k -> 0 <= k <= 63 ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 TP -> L5C.stk (hl_sptop L) M sp SHRZ_SCR ->
    L5.big_at RSEGS M X (L5.BO fb 0 st) -> (exists cap q, st = L5.BDyn cap q /\ In (q, 8 * cap) LB) ->   (* [comment removed for export] *)
    X mod 8 = 0 -> sp <= X -> X + 32 <= hl_sptop L -> L5.writable RSEGS M X 32 ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        regs_preserved R R' -> getr R' 10%bv = Z_to_bv 64 X ->
        L5.big_at RSEGS M' X (L5.BO fb 0 st) ->
        L5C.hpres L LB sp SHRZ_SCR [(X, 32)] M M' ->
        model_but_vm model model' -> hi_heap HI LB cr M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R SHR M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)

End DivSpecs.

Section Specs.
Variable L : heap_layout.
Variable HI : heap_iface.
(* [comment removed for export] *)
Variable XS : Type.                                            (* [comment removed for export] *)
Variable xs_pre : XS -> (word -> option byte) -> Prop.          (* [comment removed for export] *)
Variable xs_foot : list L5.range.                              (* [comment removed for export] *)
(* [comment removed for export] *)
Variable e2_landed : XS -> list (Z * Z) -> credit -> Z -> (word -> option byte) -> bvmap 5 word -> list (Z * Z) -> credit -> Prop.
Variable e3_landed : XS -> list (Z * Z) -> credit -> Z -> (word -> option byte) -> bvmap 5 word -> list (Z * Z) -> credit -> Prop.

Definition cfg {fx : FPState} (R : bvmap 5 word) (pc : Z) (M : word -> option byte) (model : Model) : config :=
  mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) model.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zero_throw_at (LB : list (Z * Z)) (R0 : bvmap 5 word) (M0 : word -> option byte)
           (R : bvmap 5 word) (M : word -> option byte) (S : Z) : Prop :=
  exists fden v16 v24,
  (* [comment removed for export] *)
     getr R 2%bv = Z_to_bv 64 (S - 352) /\ getr R 3%bv = getr R0 3%bv /\ getr R 4%bv = getr R0 4%bv
  /\ getr R 8%bv = Z_to_bv 64 fden /\ getr R 9%bv = Z_to_bv 64 (S - 48) /\ getr R 10%bv = Z_to_bv 64 16
  /\ getr R 18%bv = Z_to_bv 64 (S + 64) /\ getr R 19%bv = Z_to_bv 64 0 /\ getr R 20%bv = Z_to_bv 64 (S - 168) /\ getr R 21%bv = Z_to_bv 64 (S - 168)
  /\ getr R 22%bv = getr R0 22%bv /\ getr R 23%bv = Z_to_bv 64 1 /\ getr R 24%bv = getr R0 24%bv /\ getr R 25%bv = getr R0 25%bv
  /\ getr R 26%bv = getr R0 26%bv /\ getr R 27%bv = Z_to_bv 64 (S + 64)
  (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M (S - 8) (U R0 1) /\ L5.u64_at RSEGS M (S - 16) (U R0 8)
  /\ L5.u8_at RSEGS M (S - 48) 0 /\ L5.u64_at RSEGS M (S - 40) 0 /\ L5.u64_at RSEGS M (S - 32) 0 /\ L5.u64_at RSEGS M (S - 24) 0
  (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M (S - 56) 0x21d20 /\ L5.u64_at RSEGS M (S - 64) (S + 64)
  /\ L5.u64_at RSEGS M (S - 72) (U R0 9) /\ L5.u64_at RSEGS M (S - 80) (U R0 18) /\ L5.u64_at RSEGS M (S - 88) (U R0 19)
  /\ L5.u64_at RSEGS M (S - 96) (U R0 20) /\ L5.u64_at RSEGS M (S - 104) (U R0 21) /\ L5.u64_at RSEGS M (S - 112) (U R0 22)
  /\ L5.u64_at RSEGS M (S - 120) (U R0 23) /\ L5.u64_at RSEGS M (S - 128) (U R0 24) /\ L5.u64_at RSEGS M (S - 136) (U R0 25)
  /\ L5.u64_at RSEGS M (S - 144) (U R0 26) /\ L5.u64_at RSEGS M (S - 152) (U R0 27)
  /\ L5.u8_at RSEGS M (S - 184) fden /\ 0 <= fden < 256 /\ Z.testbit fden 0 = false
  /\ L5.u64_at RSEGS M (S - 176) 0 /\ L5.u64_at RSEGS M (S - 168) v16 /\ L5.u64_at RSEGS M (S - 160) v24
  (* [comment removed for export] *)
  /\ L5C.hpres L LB S SCR_OPMOD [] M0 M.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition x_is_a (M : word -> option byte) (xo fbx : Z) : Prop :=
  L5.big_at RSEGS M xo (L5.BO fbx 2 (L5.BInl A0 A1)) /\ Z.testbit fbx 1 = false.

(* [comment removed for export] *)
Definition b_ok (LB : list (Z * Z)) (M : word -> option byte) (bo : Z) (bb : L5.bigobj) (wb : list Z) : Prop :=
  L5.big_at RSEGS M bo bb /\ L5C.obj_limbs RSEGS M bb wb /\ reduced wb /\
  match L5.bo_st bb with L5.BInl _ _ => True | L5.BDyn cap q => In (q, 8 * cap) LB /\ L5.defined M q (8 * cap) end.

(* [comment removed for export] *)
Definition x_after (L : heap_layout) (LB : list (Z * Z)) (M M' : word -> option byte) (xo : Z) (LB' : list (Z * Z)) : Prop :=
  exists bx wx, L5.big_at RSEGS M' xo bx /\ L5C.obj_limbs RSEGS M' bx wx /\ L5.bo_neg bx = false /\
    match L5.bo_st bx with
    | L5.BInl _ _ => LB' = LB
    | L5.BDyn cap q => cap = 8 /\ LB' = (q, 64) :: LB /\ L5C.fresh_block L LB M' q 64
    end.

Definition opmod1_post (LB : list (Z * Z)) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (S bo : Z) (bb : L5.bigobj) (wb : list Z) (capb : Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R' /\ getr R' 10%bv = Z_to_bv 64 (S + 64)
  /\ x_after L LB M M' (S + 64) LB'
  /\ L5.big_at RSEGS M' bo bb /\ L5C.obj_limbs RSEGS M' bb wb /\ (1 <= L5.bo_len bb)%nat      (* [comment removed for export] *)
  /\ credit_after L cr OPMOD1_K (opmod1_bytes capb) cr'
  /\ L5C.hpres L LB S SCR_OPMOD [(S + 64, 32)] M M'.

(* [comment removed for export] *)
Definition opmod1_e2 (st : XS) (LB : list (Z * Z)) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (S fbx bo : Z) (bb : L5.bigobj) (wb : list Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R'
  /\ e2_landed st LB cr S M' R' LB' cr'
  /\ x_is_a M' (S + 64) fbx
  /\ L5.big_at RSEGS M' bo bb /\ L5C.obj_limbs RSEGS M' bb wb
  /\ L5C.hpres L LB S SCR_OPMOD ((S + 64, 32) :: xs_foot) M M'.

(* [comment removed for export] *)
Definition opmod1_e3 (st : XS) (LB : list (Z * Z)) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (S bo : Z) (bb : L5.bigobj) (wb : list Z) (capb : Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R'
  /\ (exists fbx' nx qx cr1 LB1,
        L5.big_at RSEGS M' (S + 64) (L5.BO fbx' nx (L5.BDyn 8 qx)) /\ LB1 = (qx, 64) :: LB /\ L5C.fresh_block L LB M' qx 64
        /\ credit_after L cr OPMOD1_K (opmod1_bytes capb) cr1
        /\ e3_landed st LB1 cr1 S M' R' LB' cr')
  /\ L5.big_at RSEGS M' bo bb /\ L5C.obj_limbs RSEGS M' bb wb
  /\ L5C.hpres L LB S SCR_OPMOD ((S + 64, 32) :: xs_foot) M M'.

Definition opmod1_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (S fbx bo : Z) (bb : L5.bigobj) (wb : list Z) (st : XS),
    let capb := L5.bo_cap bb in
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 (S + 64) -> getr R 11%bv = Z_to_bv 64 bo -> bo = S + 128 ->
    getr R 1%bv = Z_to_bv 64 OPMOD1_RET ->
    getr R 2%bv = Z_to_bv 64 S -> getr R 3%bv = Z_to_bv 64 GP -> getr R 4%bv = Z_to_bv 64 TP ->
    L5C.stk (hl_sptop L) M S SCR_OPMOD -> S + 240 <= hl_sptop L -> L5.writable RSEGS M (S + 64) 32 ->
    L5.img_clear M 0x10000 0x20000 ->
    x_is_a M (S + 64) fbx ->
    b_ok LB M bo bb wb ->
    L5.bo_cap bb <= 268 -> (L5.bo_dyn bb = true -> (3 <= L5.bo_len bb)%nat) ->      (* [comment removed for export] *)
    credit_for L cr OPMOD1_K (opmod1_bytes capb) ->
    xs_pre st M ->
    (* [comment removed for export] *)
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
        opmod1_post LB cr M M' R R' S bo bb wb capb LB' cr' ->
        model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' OPMOD1_RET M' model') K) ->
    (* [comment removed for export] *)
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
        opmod1_e2 st LB cr M M' R R' S fbx bo bb wb LB' cr' ->
        model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' TOP_PAD M' model') K) ->
    (* [comment removed for export] *)
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
        opmod1_e3 st LB cr M M' R R' S bo bb wb capb LB' cr' ->
        model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' TOP_PAD M' model') K) ->
    srealizes RSEGS SCFG (cfg R OPMOD M model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition a_ok (M : word -> option byte) (ao fba : Z) : Prop :=
  L5.big_at RSEGS M ao (L5.BO fba 2 (L5.BInl A0 A1)) /\ Z.testbit fba 1 = false.

(* [comment removed for export] *)
Definition y_ok (LB : list (Z * Z)) (M : word -> option byte) (yo : Z) (by_ : L5.bigobj) (wy : list Z) : Prop :=
  L5.big_at RSEGS M yo by_ /\ L5C.obj_limbs RSEGS M by_ wy /\ reduced wy /\
  match L5.bo_st by_ with
  | L5.BInl _ _ => True
  | L5.BDyn cap q => In (q, 8 * cap) LB /\ L5.defined M q (8 * cap) /\ Z.of_nat (L5.bo_len by_) + 1 <= cap
  end.

(* [comment removed for export] *)
Definition y_after (L : heap_layout) (LB : list (Z * Z)) (M M' : word -> option byte) (yo : Z) (by_ : L5.bigobj) (LB' : list (Z * Z)) : Prop :=
  exists by' wy', L5.big_at RSEGS M' yo by' /\ L5C.obj_limbs RSEGS M' by' wy' /\
    match L5.bo_st by_, L5.bo_st by' with
    | L5.BDyn cap q, L5.BDyn cap' q' => cap' = cap /\ q' = q /\ LB' = LB /\ L5.defined M' q (8 * cap)
    | L5.BInl _ _, L5.BInl _ _ => LB' = LB
    | L5.BInl _ _, L5.BDyn cap' q' => cap' = 8 /\ LB' = (q', 64) :: LB /\ L5C.fresh_block L LB M' q' 64
    | L5.BDyn _ _, L5.BInl _ _ => False
    end.

Definition opmod2_post (LB : list (Z * Z)) (cr : credit) (M M' : word -> option byte) (R R' : bvmap 5 word)
           (S ao fba : Z) (by_ : L5.bigobj) (capy : Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  regs_preserved R R' /\ getr R' 10%bv = Z_to_bv 64 S
  /\ y_after L LB M M' S by_ LB'
  /\ a_ok M' ao fba
  /\ credit_after L cr OPMOD2_K (opmod2_bytes capy) cr'
  /\ L5C.hpres L LB S SCR_OPMOD [(S, 32); (L5.bo_data S by_, 8 * L5.bo_cap by_)] M M'.

Definition opmod2_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (S ao fba : Z) (by_ : L5.bigobj) (wy : list Z),
    let capy := L5.bo_cap by_ in
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 S -> getr R 11%bv = Z_to_bv 64 ao -> ao = S + 160 ->
    getr R 1%bv = Z_to_bv 64 OPMOD2_RET ->
    getr R 2%bv = Z_to_bv 64 S -> getr R 3%bv = Z_to_bv 64 GP -> getr R 4%bv = Z_to_bv 64 TP ->
    L5C.stk (hl_sptop L) M S SCR_OPMOD -> S + 240 <= hl_sptop L -> L5.writable RSEGS M S 32 ->
    (forall cap q, L5.bo_st by_ = L5.BDyn cap q -> L5.writable RSEGS M q (8 * cap)) ->
    L5.img_clear M 0x10000 0x20000 ->
    y_ok LB M S by_ wy -> (1 <= L5.bo_len by_)%nat -> L5.bo_cap by_ <= 268 ->                                     (* [comment removed for export] *)
    a_ok M ao fba ->
    credit_for L cr OPMOD2_K (opmod2_bytes capy) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
        opmod2_post LB cr M M' R R' S ao fba by_ capy LB' cr' ->
        model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' OPMOD2_RET M' model') K) ->
    srealizes RSEGS SCFG (cfg R OPMOD M model) K.

End Specs.
End SCFG_1.

End L5DS.
