(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SRealizes FPSteps RefMemcpyLib LibIface LibBudget.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibEff SumMemsetLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Record hconsts : Type := HC {
  hc_find_u32     : Z;
  hc_find_nt      : Z;
  hc_emplace_u32  : Z;
  hc_emplace_ext  : Z;
  hc_rehash_u32   : Z;
  hc_rehash_ext   : Z;
  hc_mva_u32      : Z;
  hc_mva_ext      : Z;
  hc_next_prime   : Z;
  hc_state_mva    : Z;
  hc_state_dtor   : Z;
  hc_memset       : Z;
  hc_delete_sized : Z;
  hc_nt_entry     : Z;
  hc_nt_exit      : Z
}.

Section Stmts.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.
Variable L : Layout.
Variable MI : MallocIface SEGS L.
Variable ST : StaticsIface SEGS L.
Variable hc : hconsts.

Variables NEW_STACK DEL_STACK : Z.

#[local] Abbreviation cfg fx R pc M model :=
  (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).

Definition free_ops {V : Type} (bl bc : Z) (ents : list (Z * (Z * V))) : list lop :=
  map (fun e => LDel (fst e)) ents ++ (if bc =? 0 then [] else [LDel bl]).

Definition b2z (b : bool) : Z := if b then 1 else 0.

Definition memset_stmt : Prop :=
  forall (fx : FPState) (mem0 : mem) (d cv ret : word) (n : Z) (regs : bvmap 5 word),
    0 <= n -> bv_unsigned d + n < 2 ^ 64 ->
    store_ok SEGS mem0 d (Z.to_nat n) = true -> ret_ok ret ->
    getr regs 10%bv = d -> getr regs 11%bv = cv -> getr regs 12%bv = Z_to_bv 64 n -> getr regs 1%bv = ret ->
    exists regs',
      msteps SEGS (@mkst fx regs (Z_to_bv 64 (hc_memset hc)) mem0 (seg_rom SEGS))
                  (@mkst fx regs' ret (wbytes mem0 d (repeat (cbyte cv) (Z.to_nat n))) (seg_rom SEGS))
      /\ getr regs' 10%bv = d /\ ms_agree regs regs'.

Definition BSEQ_LAST : Z := 26339969.

Definition next_prime_stmt : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : mem) (bc sp : Z) (ret : word),
    In bc BSEQ -> bc <> 0 -> bc <> BSEQ_LAST ->
    getr R 10%bv = Z_to_bv 64 (np_arg bc) ->
    getr R 1%bv = ret -> ret_ok ret -> getr R 2%bv = Z_to_bv 64 sp ->
    sp mod 16 = 0 -> 2 ^ 24 <= sp -> sp <= 2 ^ 47 ->
    stack_room SEGS M sp 16 -> ro_clear L M ->
    exists R',
      msteps SEGS (@mkst fx R (Z_to_bv 64 (hc_next_prime hc)) M (seg_rom SEGS))
                  (@mkst fx R' ret
                      (wbytes M (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 ret)) (seg_rom SEGS))
      /\ kept R R'
      /\ getr R' 10%bv = Z_to_bv 64 (bseq_next bc).

Definition find_stmt (F : Z) (NS : Z) (V : Type) (nval : mem -> Z -> V -> Prop) : Prop :=
  forall (fx : FPState) (A : AS MI) (R : bvmap 5 word) (M : mem)
         (obj bl bc keyp key : Z) (ents : list (Z * (Z * V))) (ret : word),
    umapx MI NS nval A M obj bl bc ents -> 24 <= NS ->
    cell4 SEGS M keyp key -> 0 < keyp -> keyp + 4 <= 2 ^ 47 ->
    getr R 10%bv = Z_to_bv 64 obj -> getr R 11%bv = Z_to_bv 64 keyp ->
    getr R 1%bv = ret -> ret_ok ret ->
    exists R' (p : Z),
      msteps SEGS (@mkst fx R (Z_to_bv 64 F) M (seg_rom SEGS)) (@mkst fx R' ret M (seg_rom SEGS))
      /\ kept R R'
      /\ getr R' 10%bv = Z_to_bv 64 p
      /\ (p = 0 \/ exists v, In (p, (key, v)) ents).

Definition EMPLACE_STACK : Z := 96 + Z.max NEW_STACK DEL_STACK.

Definition emplace24_stmt (F : Z) : Prop :=
  forall (fx : FPState) (A : AS MI) (s : SX ST) (R : bvmap 5 word) (M : mem) (model : Model)
         (sp ret obj bl bc keyp tupp keyp2 key : Z) (ents : list (Z * (Z * Z))) (K : TSet),
    callB MI ST A s R M model sp ret EMPLACE_STACK ->
    frm_zero (@fp_csr fx) ->
    getr R 10%bv = Z_to_bv 64 obj -> getr R 11%bv = Z_to_bv 64 keyp -> getr R 13%bv = Z_to_bv 64 tupp ->
    umapx MI 24 (nval24 SEGS) A M obj bl bc ents ->
    above_sp MI A sp obj 40 -> above_sp MI A sp keyp 4 -> above_sp MI A sp tupp 8 -> above_sp MI A sp keyp2 4 ->
    cell4 SEGS M keyp key -> cell8 SEGS M tupp keyp2 -> cell4 SEGS M keyp2 key -> ro_clear L M ->

    Zlength ents + 1 < 2 ^ 24 -> LIB_NMAX <= NMAX MI -> bc <> BSEQ_LAST ->

    roomL MI A (live MI A) 24 ->
    ((bc = 0 \/ Zlength ents = bc) -> roomL MI A ((0, 24) :: live MI A) (8 * bseq_next bc)) ->
    (forall (fx' : FPState) A' R' M' model' (p v bl' bc' : Z) (ents' : list (Z * (Z * Z)))
            (inserted rehashed : bool),
        retB MI ST A' s R R' M' model model' -> frm_zero (@fp_csr fx') ->
        getr R' 10%bv = Z_to_bv 64 p -> getr R' 11%bv = Z_to_bv 64 (b2z inserted) ->
        umapx MI 24 (nval24 SEGS) A' M' obj bl' bc' ents' ->
        In (p, (key, v)) ents' ->
        (inserted = false -> ents' = ents /\ rehashed = false) ->
        (inserted = true -> v = 0 /\ Permutation ents' ((p, (key, 0)) :: ents)) ->
        (rehashed = false -> bl' = bl /\ bc' = bc) ->
        (rehashed = true -> (bc = 0 \/ Zlength ents = bc) /\ bc' = bseq_next bc) ->
        lapply (live MI A)
               ((if inserted then [LAdd p 24] else [])
                ++ (if rehashed then LAdd bl' (8 * bc') :: (if bc =? 0 then [] else [LDel bl]) else []))
               (live MI A') ->
        eff MI A A' M M' (sp - EMPLACE_STACK, sp)
            (fun a => umap_foot 24 obj bl bc ents a \/ umap_foot 24 obj bl' bc' ents' a) ->
        srealizes SEGS (cfg fx' R' ret M' model') K) ->
    srealizes SEGS (cfg fx R F M model) K.

Definition REHASH_STACK : Z := 48 + Z.max NEW_STACK DEL_STACK.

Definition rehash24_stmt (F : Z) : Prop :=
  forall (fx : FPState) (A : AS MI) (s : SX ST) (R : bvmap 5 word) (M : mem) (model : Model)
         (sp ret obj bl bc : Z) (ents : list (Z * (Z * Z))) (K : TSet),
    callB MI ST A s R M model sp ret REHASH_STACK ->
    getr R 10%bv = Z_to_bv 64 obj -> getr R 11%bv = Z_to_bv 64 (bseq_next bc) ->
    umapx MI 24 (nval24 SEGS) A M obj bl bc ents -> bc <> BSEQ_LAST -> LIB_NMAX <= NMAX MI ->
    above_sp MI A sp obj 40 ->
    roomL MI A (live MI A) (8 * bseq_next bc) ->
    (forall A' R' M' model' (bl' : Z) (ents' : list (Z * (Z * Z))),
        retB MI ST A' s R R' M' model model' ->
        umapx MI 24 (nval24 SEGS) A' M' obj bl' (bseq_next bc) ents' ->
        Permutation ents' ents ->
        lapply (live MI A) (LAdd bl' (8 * bseq_next bc) :: (if bc =? 0 then [] else [LDel bl])) (live MI A') ->
        eff MI A A' M M' (sp - REHASH_STACK, sp)
            (fun a => umap_foot 24 obj bl bc ents a \/ umap_foot 24 obj bl' (bseq_next bc) ents' a) ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R F M model) K.

Definition MVA_STACK : Z := 32 + DEL_STACK.

Definition mva_stmt (F : Z) (NS : Z) (V : Type) (nval : mem -> Z -> V -> Prop) : Prop :=
  forall (fx : FPState) (A : AS MI) (s : SX ST) (R : bvmap 5 word) (M : mem) (model : Model)
         (sp ret obj1 bl1 bc1 obj2 bl2 bc2 : Z) (ents1 ents2 : list (Z * (Z * V))) (K : TSet),
    callB MI ST A s R M model sp ret MVA_STACK ->
    getr R 10%bv = Z_to_bv 64 obj1 -> getr R 11%bv = Z_to_bv 64 obj2 ->
    umapx MI NS nval A M obj1 bl1 bc1 ents1 -> umapx MI NS nval A M obj2 bl2 bc2 ents2 ->
    above_sp MI A sp obj1 40 -> above_sp MI A sp obj2 40 -> apart obj1 40 obj2 40 ->
    (forall b, In b (map fst (umap_blocks NS bl1 bc1 ents1)) -> ~ In b (map fst (umap_blocks NS bl2 bc2 ents2))) ->
    (forall (fx' : FPState) A' R' M' model',
        retB MI ST A' s R R' M' model model' -> @fp_csr fx' = @fp_csr fx ->
        umapx MI NS nval A' M' obj1 bl2 bc2 ents2 ->
        umapx MI NS nval A' M' obj2 0 0 [] ->
        lapply (live MI A) (free_ops bl1 bc1 ents1) (live MI A') ->
        eff MI A A' M M' (sp - MVA_STACK, sp)
            (fun a => umap_foot NS obj1 bl1 bc1 ents1 a \/ umap_foot NS obj2 bl2 bc2 ents2 a) ->
        srealizes SEGS (cfg fx' R' ret M' model') K) ->
    srealizes SEGS (cfg fx R F M model) K.

Record vraw (A : AS MI) (M : mem) (v : Z) (b e c : Z) : Prop := VRAW {
  vr_b : cell8 SEGS M v b;
  vr_e : cell8 SEGS M (v + 8) e;
  vr_c : cell8 SEGS M (v + 16) c;
  vr_blk : (b = 0 /\ e = 0 /\ c = 0) \/ (b <> 0 /\ In (b, c - b) (live MI A) /\ b <= e <= c)
}.

Record stateC : Type := STC {
  st_words : Z; st_nwords : Z; st_diag : Z; st_widx : Z; st_icount : Z;
  st_endian : Z;
  st_flags : Z;
  st_m1 : Z * Z * list (Z * (Z * Z));
  st_m2 : Z * Z * list (Z * (Z * (Z * Z * Z)));
  st_m3 : Z * Z * list (Z * (Z * Z));
  st_v1 : Z * Z * Z;
  st_v2 : Z * Z * Z;
  st_v3 : Z * Z * Z
}.

Definition t3a {A B C : Type} (t : A * B * C) : A := fst (fst t).
Definition t3b {A B C : Type} (t : A * B * C) : B := snd (fst t).
Definition t3c {A B C : Type} (t : A * B * C) : C := snd t.

Definition vec_blocks (v : Z * Z * Z) : list (Z * Z) :=
  if t3a v =? 0 then [] else [(t3a v, t3c v - t3a v)].
Definition state_blocks (c : stateC) : list (Z * Z) :=
  umap_blocks 24 (t3a (st_m1 c)) (t3b (st_m1 c)) (t3c (st_m1 c))
  ++ umap_blocks 32 (t3a (st_m2 c)) (t3b (st_m2 c)) (t3c (st_m2 c))
  ++ umap_blocks 24 (t3a (st_m3 c)) (t3b (st_m3 c)) (t3c (st_m3 c))
  ++ vec_blocks (st_v1 c) ++ vec_blocks (st_v2 c) ++ vec_blocks (st_v3 c).

Record state_rep (A : AS MI) (M : mem) (st : Z) (c : stateC) : Prop := STATE_REP {
  sr_w0 : cell8 SEGS M st (st_words c);
  sr_w1 : cell8 SEGS M (st + 8) (st_nwords c);
  sr_w2 : cell8 SEGS M (st + 16) (st_diag c);
  sr_w3 : cell8 SEGS M (st + 24) (st_widx c);
  sr_w4 : cell8 SEGS M (st + 32) (st_icount c);
  sr_w5 : cell4 SEGS M (st + 40) (st_endian c);
  sr_w6 : cellw SEGS M (st + 44) 2 (st_flags c);
  sr_m1 : umapx MI 24 (nval24 SEGS) A M (st + 48)  (t3a (st_m1 c)) (t3b (st_m1 c)) (t3c (st_m1 c));
  sr_m2 : umapx MI 32 (nval32 SEGS) A M (st + 88)  (t3a (st_m2 c)) (t3b (st_m2 c)) (t3c (st_m2 c));
  sr_m3 : umapx MI 24 (nval24 SEGS) A M (st + 128) (t3a (st_m3 c)) (t3b (st_m3 c)) (t3c (st_m3 c));
  sr_v1 : vraw A M (st + 168) (t3a (st_v1 c)) (t3b (st_v1 c)) (t3c (st_v1 c));
  sr_v2 : vraw A M (st + 192) (t3a (st_v2 c)) (t3b (st_v2 c)) (t3c (st_v2 c));
  sr_v3 : vraw A M (st + 216) (t3a (st_v3 c)) (t3b (st_v3 c)) (t3c (st_v3 c));
  sr_def : defined M st 240;
  sr_al  : st mod 8 = 0;
  sr_nodup : NoDup (map fst (state_blocks c))
}.

Definition state_foot (st : Z) (c : stateC) (a : Z) : Prop :=
  (st <= a < st + 240) \/ exists b, In b (state_blocks c) /\ fst b <= a < fst b + snd b.

Definition state_moved (cthis cother : stateC) : stateC :=
  {| st_words := st_words cother; st_nwords := st_nwords cother; st_diag := st_diag cother;
     st_widx := st_widx cother; st_icount := st_icount cother; st_endian := st_endian cother;
     st_flags := st_flags cother;
     st_m1 := st_m1 cother; st_m2 := st_m2 cother; st_m3 := st_m3 cother;
     st_v1 := st_v1 cother; st_v2 := st_v2 cother; st_v3 := st_v3 cother |}.

Definition state_emptied (cother : stateC) : stateC :=
  {| st_words := st_words cother; st_nwords := st_nwords cother; st_diag := st_diag cother;
     st_widx := st_widx cother; st_icount := st_icount cother; st_endian := st_endian cother;
     st_flags := st_flags cother;
     st_m1 := (0, 0, []); st_m2 := (0, 0, []); st_m3 := (0, 0, []);
     st_v1 := (0, 0, 0); st_v2 := (0, 0, 0); st_v3 := (0, 0, 0) |}.

Definition STATE_MVA_STACK : Z := 64 + DEL_STACK.

Definition state_mva_stmt : Prop :=
  forall (fx : FPState) (A : AS MI) (s : SX ST) (R : bvmap 5 word) (M : mem) (model : Model)
         (sp ret st1 st2 : Z) (c1 c2 : stateC) (K : TSet),
    callB MI ST A s R M model sp ret STATE_MVA_STACK ->
    getr R 10%bv = Z_to_bv 64 st1 -> getr R 11%bv = Z_to_bv 64 st2 ->
    state_rep A M st1 c1 -> state_rep A M st2 c2 ->
    above_sp MI A sp st1 240 -> above_sp MI A sp st2 240 -> apart st1 240 st2 240 ->
    (forall b, In b (map fst (state_blocks c1)) -> ~ In b (map fst (state_blocks c2))) ->
    (forall (fx' : FPState) A' R' M' model',
        retB MI ST A' s R R' M' model model' -> @fp_csr fx' = @fp_csr fx ->
        getr R' 10%bv = Z_to_bv 64 st1 ->
        state_rep A' M' st1 (state_moved c1 c2) ->
        state_rep A' M' st2 (state_emptied c2) ->
        lapply (live MI A) (map (fun b => LDel (fst b)) (state_blocks c1)) (live MI A') ->
        eff MI A A' M M' (sp - STATE_MVA_STACK, sp) (fun a => state_foot st1 c1 a \/ state_foot st2 c2 a) ->
        srealizes SEGS (cfg fx' R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (hc_state_mva hc) M model) K.

Definition STATE_DTOR_STACK : Z := 32 + DEL_STACK.

Definition state_dtor_stmt : Prop :=
  forall (fx : FPState) (A : AS MI) (s : SX ST) (R : bvmap 5 word) (M : mem) (model : Model)
         (sp ret st : Z) (c : stateC) (K : TSet),
    callB MI ST A s R M model sp ret STATE_DTOR_STACK ->
    getr R 10%bv = Z_to_bv 64 st ->
    state_rep A M st c -> above_sp MI A sp st 240 ->
    (forall A' R' M' model',
        retB MI ST A' s R R' M' model model' ->
        lapply (live MI A) (map (fun b => LDel (fst b)) (state_blocks c)) (live MI A') ->
        eff MI A A' M M' (sp - STATE_DTOR_STACK, sp) (state_foot st c) ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (hc_state_dtor hc) M model) K.

Definition NT_STACK : Z := Z.max (Z.max NEW_STACK DEL_STACK) 16.

Record nt_frame (R : bvmap 5 word) (M : mem) (sp parser key : Z) (val : Z * Z * Z) (v2 : Z) : Prop := NT_FRAME {
  nf_sp  : getr R 2%bv = Z_to_bv 64 sp;
  nf_s0  : getr R 8%bv = Z_to_bv 64 parser;
  nf_s8  : getr R 24%bv = Z_to_bv 64 1;
  nf_s5  : getr R 21%bv = Z_to_bv 64 (t3a val);
  nf_s2  : getr R 18%bv = Z_to_bv 64 v2;
  nf_s11 : getr R 27%bv = Z_to_bv 64 (t3c val);
  nf_gp  : getr R 3%bv = Z_to_bv 64 (ly_gp L);
  nf_tp  : getr R 4%bv = Z_to_bv 64 (ly_tp L);
  nf_key : cell4 SEGS M (sp + 244) key;
  nf_p1  : cell8 SEGS M (sp + 24) (parser + 152);
  nf_c40 : cell8 SEGS M (sp + 40) 0x01010101;
  nf_c48 : cell8 SEGS M (sp + 48) 0x0f0f0f0f;
  nf_c56 : cell8 SEGS M (sp + 56) 0x33333333;
  nf_c64 : cell8 SEGS M (sp + 64) 0x55555555
}.

Definition nt_kept (R R' : bvmap 5 word) : Prop :=
  forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 27]%bv -> getr R' r = getr R r.

Definition emplace_nt_block_stmt : Prop :=
  forall (fx : FPState) (A : AS MI) (s : SX ST) (R : bvmap 5 word) (M : mem) (model : Model)
         (sp parser key bl bc : Z) (val : Z * Z * Z) (v2 : Z) (ents : list (Z * (Z * (Z * Z * Z)))) (K : TSet),
    ainv MI A M model -> mstd model -> sx_inv ST s M -> sx_handler_set ST s ->
    sp mod 16 = 0 -> alloc_ceiling + NT_STACK <= sp -> stack_room SEGS M sp NT_STACK ->
    (forall a, zwin (sp - NT_STACK) sp a -> ~ owned MI A a /\ ~ sx_region ST a) ->
    (forall a, owned MI A a -> ~ sx_region ST a) -> (forall a, errno_win L a -> ~ sx_region ST a) ->
    frm_zero (@fp_csr fx) ->
    nt_frame R M sp parser key val v2 ->
    above_sp MI A sp (sp + 8) 8 -> above_sp MI A sp (sp + 24) 48 -> above_sp MI A sp (sp + 244) 4 ->
    store_ok SEGS M (Z_to_bv 64 (sp + 8)) 8 = true ->
    umapx MI 32 (nval32 SEGS) A M (parser + 136) bl bc ents -> above_sp MI A sp (parser + 136) 40 -> sp + 248 <= parser + 136 ->
    0 <= t3a val < 2 ^ 32 -> 0 <= t3b val < 2 ^ 32 -> 0 <= t3c val < 2 ^ 32 -> 0 <= v2 < 2 ^ 64 -> v2 mod 2 ^ 32 = t3b val -> ro_clear L M ->
    Zlength ents + 1 < 2 ^ 24 -> LIB_NMAX <= NMAX MI -> bc <> BSEQ_LAST ->
    roomL MI A (live MI A) 32 ->
    ((bc = 0 \/ Zlength ents = bc) -> roomL MI A ((0, 32) :: live MI A) (8 * bseq_next bc)) ->
    (forall (fx' : FPState) A' R' M' model' (p bl' bc' : Z) (ents' : list (Z * (Z * (Z * Z * Z))))
            (inserted rehashed : bool),
        ainv MI A' M' model' -> mstd model' -> m_fs model' = m_fs model -> m_fds model' = m_fds model ->
        sx_inv ST s M' -> frm_zero (@fp_csr fx') ->
        nt_kept R R' -> getr R' 25%bv = Z_to_bv 64 p ->
        umapx MI 32 (nval32 SEGS) A' M' (parser + 136) bl' bc' ents' ->
        In (p, (key, val)) ents' ->
        (inserted = false -> exists v0 l1 l2, ents = l1 ++ (p, (key, v0)) :: l2 /\ ents' = l1 ++ (p, (key, val)) :: l2
                             /\ rehashed = false) ->
        (inserted = true -> Permutation ents' ((p, (key, val)) :: ents)) ->
        (rehashed = false -> bl' = bl /\ bc' = bc) ->
        (rehashed = true -> (bc = 0 \/ Zlength ents = bc) /\ bc' = bseq_next bc) ->
        lapply (live MI A)
               ((if inserted then [LAdd p 32] else [])
                ++ (if rehashed then LAdd bl' (8 * bc') :: (if bc =? 0 then [] else [LDel bl]) else []))
               (live MI A') ->
        eff MI A A' M M' (sp - NT_STACK, sp)
            (fun a => umap_foot 32 (parser + 136) bl bc ents a \/ umap_foot 32 (parser + 136) bl' bc' ents' a
                      \/ (sp + 8 <= a < sp + 16)) ->
        defined M' (sp + 8) 8 ->
        srealizes SEGS (cfg fx' R' (hc_nt_exit hc) M' model') K) ->
    srealizes SEGS (cfg fx R (hc_nt_entry hc) M model) K.

Definition sx32 (x : Z) : Z := if x <? 2 ^ 31 then x else x + 2 ^ 64 - 2 ^ 32.

Definition nt_find_block_stmt (ENTRY MISS HIT : Z) : Prop :=
  forall (fx : FPState) (A : AS MI) (R : bvmap 5 word) (M : mem)
         (this bl bc tid : Z) (ents : list (Z * (Z * (Z * Z * Z)))),
    umapx MI 32 (nval32 SEGS) A M (this + 136) bl bc ents ->
    getr R 10%bv = Z_to_bv 64 this -> getr R 8%bv = Z_to_bv 64 (sx32 tid) -> 0 <= tid < 2 ^ 32 ->
    0 < this -> this + 288 <= 2 ^ 47 ->
    exists R' (pc' : Z),
      msteps SEGS (@mkst fx R (Z_to_bv 64 ENTRY) M (seg_rom SEGS)) (@mkst fx R' (Z_to_bv 64 pc') M (seg_rom SEGS))
      /\ (forall r, ~ In r [12; 13; 14; 15; 16; 17]%bv -> getr R' r = getr R r)
      /\ ( pc' = MISS
          \/ (pc' = HIT /\ exists p v, In (p, (tid, v)) ents /\ getr R' 14%bv = Z_to_bv 64 p)).

End Stmts.

Arguments vraw {AC SEGS L} MI.
Arguments state_rep {AC SEGS L} MI.
