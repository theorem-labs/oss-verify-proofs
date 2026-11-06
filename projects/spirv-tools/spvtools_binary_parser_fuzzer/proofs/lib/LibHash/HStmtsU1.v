(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SRealizes FPSteps RefMemcpyLib LibIface LibEff LibBudget.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HStmts HFpu.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section StmtsU1.
Context {AC : AllocCeiling}.
  Variable SEGS : list Segment.
  Variable L : Layout.
  Variable MI : MallocIface SEGS L.

  Definition nt_find_block_u1_stmt (ENTRY MISS HIT : Z) : Prop :=
    forall (fx : FPState) (A : AS MI) (R : bvmap 5 word) (M : mem)
           (this bl bc tid : Z) (ents : list (Z * (Z * (Z * Z * Z)))),
      umapx MI 32 (nval32 SEGS) A M (this + 136) bl bc ents ->
      getr R 10%bv = Z_to_bv 64 this -> getr R 8%bv = Z_to_bv 64 (sx32 tid) -> 0 <= tid < 2 ^ 32 ->
      0 < this -> this + 288 <= 2 ^ 47 ->
      exists R' (pc' : Z),
        msteps SEGS (@mkst fx R (Z_to_bv 64 ENTRY) M (seg_rom SEGS)) (@mkst fx R' (Z_to_bv 64 pc') M (seg_rom SEGS))
        /\ (forall r, ~ In r [5; 6; 10; 12; 13; 14; 15; 16; 17]%bv -> getr R' r = getr R r)
        /\ getr R' 13%bv = Z_to_bv 64 this
        /\ ( pc' = MISS
            \/ (pc' = HIT /\ exists p v, In (p, (tid, v)) ents /\ getr R' 15%bv = Z_to_bv 64 p)).

  Definition rw_arg (bc : Z) : Z := if bc =? 0 then 1 else np_arg bc.

  Variable ST : StaticsIface SEGS L.
  Variables NEW_STACK DEL_STACK : Z.
  Definition rehashw_stmt (F : Z) : Prop :=
    forall (fx : FPState) (A : AS MI) (s : SX ST) (R : bvmap 5 word) (M : mem) (model : Model)
           (sp ret obj bl bc : Z) (ents : list (Z * (Z * Z))) (K : TSet),
      callB MI ST A s R M model sp ret (REHASH_STACK NEW_STACK DEL_STACK) ->
      getr R 10%bv = Z_to_bv 64 obj -> getr R 11%bv = Z_to_bv 64 (rw_arg bc) ->
      umapx MI 24 (nval24 SEGS) A M obj bl bc ents -> bc <> BSEQ_LAST -> LIB_NMAX <= NMAX MI ->
      above_sp MI A sp obj 40 -> ro_clear L M ->
      roomL MI A (live MI A) (8 * bseq_next bc) ->
      (forall A' R' M' model' (bl' : Z) (ents' : list (Z * (Z * Z))),
          retB MI ST A' s R R' M' model model' ->
          umapx MI 24 (nval24 SEGS) A' M' obj bl' (bseq_next bc) ents' ->
          Permutation ents' ents ->
          lapply (live MI A) (LAdd bl' (8 * bseq_next bc) :: (if bc =? 0 then [] else [LDel bl])) (live MI A') ->
          eff MI A A' M M' (sp - REHASH_STACK NEW_STACK DEL_STACK, sp)
              (fun a => umap_foot 24 obj bl bc ents a \/ umap_foot 24 obj bl' (bseq_next bc) ents' a) ->
          srealizes SEGS (mkCfg (@mkst fx R' (Z_to_bv 64 ret) M' (seg_rom SEGS)) model') K) ->
      srealizes SEGS (mkCfg (@mkst fx R (Z_to_bv 64 F) M (seg_rom SEGS)) model) K.

  Definition fkept_u1 (fx fx' : FPState) : Prop :=
    forall r : bv 5, ~ In r [13; 14; 15]%bv -> reg_get (@fp_regs fx') r = reg_get (@fp_regs fx) r.

  Definition emplace24u_stmt (F : Z) : Prop :=
    forall (fx : FPState) (A : AS MI) (s : SX ST) (R : bvmap 5 word) (M : mem) (model : Model)
           (sp ret obj bl bc keyp tupp keyp2 key : Z) (ents : list (Z * (Z * Z))) (K : TSet),
      callB MI ST A s R M model sp ret (EMPLACE_STACK NEW_STACK DEL_STACK) ->
      frm_zero (@fp_csr fx) ->
      getr R 10%bv = Z_to_bv 64 obj -> getr R 11%bv = Z_to_bv 64 keyp -> getr R 13%bv = Z_to_bv 64 tupp ->
      umapx MI 24 (nval24 SEGS) A M obj bl bc ents ->
      above_sp MI A sp obj 40 -> above_sp MI A sp keyp 4 -> above_sp MI A sp tupp 8 -> above_sp MI A sp keyp2 4 ->
      cell4 SEGS M keyp key -> cell8 SEGS M tupp keyp2 -> cell4 SEGS M keyp2 key -> keyp2 mod 4 = 0 -> ro_clear L M ->

      Zlength ents + 1 < 2 ^ 24 -> LIB_NMAX <= NMAX MI -> bc <> BSEQ_LAST ->

      roomL MI A (live MI A) 24 ->
      ((bc = 0 \/ Zlength ents = bc) -> roomL MI A ((0, 24) :: live MI A) (8 * bseq_next bc)) ->
      (forall (fx' : FPState) A' R' M' model' (p v bl' bc' : Z) (ents' : list (Z * (Z * Z)))
              (inserted rehashed : bool),
          retB MI ST A' s R R' M' model model' -> frm_zero (@fp_csr fx') -> fkept_u1 fx fx' ->
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
          eff MI A A' M M' (sp - EMPLACE_STACK NEW_STACK DEL_STACK, sp)
              (fun a => umap_foot 24 obj bl bc ents a \/ umap_foot 24 obj bl' bc' ents' a) ->
          srealizes SEGS (mkCfg (@mkst fx' R' (Z_to_bv 64 ret) M' (seg_rom SEGS)) model') K) ->
      srealizes SEGS (mkCfg (@mkst fx R (Z_to_bv 64 F) M (seg_rom SEGS)) model) K.

  Definition INDEX_STACK : Z := 32 + EMPLACE_STACK NEW_STACK DEL_STACK.
  Definition index24_u1_stmt (F : Z) : Prop :=
    forall (fx : FPState) (A : AS MI) (s : SX ST) (R : bvmap 5 word) (M : mem) (model : Model)
           (sp ret obj bl bc keyp key : Z) (ents : list (Z * (Z * Z))) (K : TSet),
      callB MI ST A s R M model sp ret INDEX_STACK ->
      frm_zero (@fp_csr fx) ->
      getr R 10%bv = Z_to_bv 64 obj -> getr R 11%bv = Z_to_bv 64 keyp ->
      umapx MI 24 (nval24 SEGS) A M obj bl bc ents ->
      above_sp MI A sp obj 40 -> above_sp MI A sp keyp 4 -> cell4 SEGS M keyp key -> keyp mod 4 = 0 -> ro_clear L M ->
      Zlength ents + 1 < 2 ^ 24 -> LIB_NMAX <= NMAX MI -> bc <> BSEQ_LAST ->
      roomL MI A (live MI A) 24 ->
      ((bc = 0 \/ Zlength ents = bc) -> roomL MI A ((0, 24) :: live MI A) (8 * bseq_next bc)) ->
      (forall (fx' : FPState) A' R' M' model' (p v bl' bc' : Z) (ents' : list (Z * (Z * Z)))
              (inserted rehashed : bool),
          retB MI ST A' s R R' M' model model' -> frm_zero (@fp_csr fx') -> fkept_u1 fx fx' ->
          getr R' 10%bv = Z_to_bv 64 (p + 20) ->
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
          eff MI A A' M M' (sp - INDEX_STACK, sp)
              (fun a => umap_foot 24 obj bl bc ents a \/ umap_foot 24 obj bl' bc' ents' a) ->
          srealizes SEGS (mkCfg (@mkst fx' R' (Z_to_bv 64 ret) M' (seg_rom SEGS)) model') K) ->
      srealizes SEGS (mkCfg (@mkst fx R (Z_to_bv 64 F) M (seg_rom SEGS)) model) K.

  Definition vstep (esz b e : Z) : Prop := exists n, 0 <= n /\ e = b + esz * n.
  Definition state_vsteps (c : stateC) : Prop :=
    vstep 20 (t3a (st_v1 c)) (t3b (st_v1 c)) /\ vstep 4 (t3a (st_v2 c)) (t3b (st_v2 c)) /\ vstep 4 (t3a (st_v3 c)) (t3b (st_v3 c)).

  Definition state_dtor_u1_stmt (hc : hconsts) : Prop :=
    forall (fx : FPState) (A : AS MI) (s : SX ST) (R : bvmap 5 word) (M : mem) (model : Model)
           (sp ret st : Z) (c : stateC) (K : TSet),
      callB MI ST A s R M model sp ret (STATE_DTOR_STACK DEL_STACK) ->
      getr R 10%bv = Z_to_bv 64 st ->
      state_rep MI A M st c -> state_vsteps c -> above_sp MI A sp st 240 ->
      (forall A' R' M' model',
          retB MI ST A' s R R' M' model model' ->
          lapply (live MI A) (map (fun b => LDel (fst b)) (state_blocks c)) (live MI A') ->
          eff MI A A' M M' (sp - STATE_DTOR_STACK DEL_STACK, sp) (state_foot st c) ->
          srealizes SEGS (mkCfg (@mkst fx R' (Z_to_bv 64 ret) M' (seg_rom SEGS)) model') K) ->
      srealizes SEGS (mkCfg (@mkst fx R (Z_to_bv 64 (hc_state_dtor hc)) M (seg_rom SEGS)) model) K.

  Definition state_mva_u1_stmt (hc : hconsts) : Prop :=
    forall (fx : FPState) (A : AS MI) (s : SX ST) (R : bvmap 5 word) (M : mem) (model : Model)
           (sp ret st1 st2 : Z) (c1 c2 : stateC) (K : TSet),
      callB MI ST A s R M model sp ret (STATE_MVA_STACK DEL_STACK) ->
      getr R 10%bv = Z_to_bv 64 st1 -> getr R 11%bv = Z_to_bv 64 st2 ->
      state_rep MI A M st1 c1 -> state_rep MI A M st2 c2 -> state_vsteps c1 ->
      above_sp MI A sp st1 240 -> above_sp MI A sp st2 240 -> apart st1 240 st2 240 ->
      (forall b, In b (map fst (state_blocks c1)) -> ~ In b (map fst (state_blocks c2))) ->
      (forall (fx' : FPState) A' R' M' model',
          retB MI ST A' s R R' M' model model' -> @fp_csr fx' = @fp_csr fx ->
          getr R' 10%bv = Z_to_bv 64 st1 ->
          state_rep MI A' M' st1 (state_moved c1 c2) ->
          state_rep MI A' M' st2 (state_emptied c2) ->
          lapply (live MI A) (map (fun b => LDel (fst b)) (state_blocks c1)) (live MI A') ->
          eff MI A A' M M' (sp - STATE_MVA_STACK DEL_STACK, sp) (fun a => state_foot st1 c1 a \/ state_foot st2 c2 a) ->
          srealizes SEGS (mkCfg (@mkst fx' R' (Z_to_bv 64 ret) M' (seg_rom SEGS)) model') K) ->
      srealizes SEGS (mkCfg (@mkst fx R (Z_to_bv 64 (hc_state_mva hc)) M (seg_rom SEGS)) model) K.

  Record nt_frame_u1 (fx : FPState) (R : bvmap 5 word) (M : mem) (sp parser key w1 w2 w3 : Z) : Prop := NT_FRAME_U1 {
    nu_sp  : getr R 2%bv = Z_to_bv 64 sp;
    nu_s0  : getr R 8%bv = Z_to_bv 64 parser;
    nu_s2  : getr R 18%bv = Z_to_bv 64 1;
    nu_a5  : getr R 15%bv = Z_to_bv 64 w3;
    nu_gp  : getr R 3%bv = Z_to_bv 64 (ly_gp L);
    nu_tp  : getr R 4%bv = Z_to_bv 64 (ly_tp L);
    nu_key : cell4 SEGS M (sp + 260) key;
    nu_p1  : cell8 SEGS M (sp + 40) (parser + 152);
    nu_c56 : cell8 SEGS M (sp + 56) 0x01010101;
    nu_c64 : cell8 SEGS M (sp + 64) 0x0f0f0f0f;
    nu_c72 : cell8 SEGS M (sp + 72) 0x33333333;
    nu_c80 : cell8 SEGS M (sp + 80) 0x55555555;
    nu_v1  : cell8 SEGS M (sp + 16) w1;
    nu_v2  : cell8 SEGS M (sp + 8) w2;
    nu_fs0 : fholds fx 8%bv 0x4b000000;
    nu_fs1 : fholds fx 9%bv 0xbf800000;
    nu_fs2 : fholds fx 18%bv 0x5f800000
  }.

  Definition nt_kept_u1 (R R' : bvmap 5 word) : Prop :=
    forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 25]%bv -> getr R' r = getr R r.

  Definition emplace_nt_block_u1_stmt (hc : hconsts) : Prop :=
    forall (fx : FPState) (A : AS MI) (s : SX ST) (R : bvmap 5 word) (M : mem) (model : Model)
           (sp parser key bl bc w1 w2 w3 : Z) (val : Z * Z * Z) (ents : list (Z * (Z * (Z * Z * Z)))) (K : TSet),
      ainv MI A M model -> mstd model -> sx_inv ST s M -> sx_handler_set ST s ->
      sp mod 16 = 0 -> alloc_ceiling + NT_STACK NEW_STACK DEL_STACK <= sp ->
      stack_room SEGS M sp (NT_STACK NEW_STACK DEL_STACK) ->
      (forall a, zwin (sp - NT_STACK NEW_STACK DEL_STACK) sp a -> ~ owned MI A a /\ ~ sx_region ST a) ->
      (forall a, owned MI A a -> ~ sx_region ST a) -> (forall a, errno_win L a -> ~ sx_region ST a) ->
      frm_zero (@fp_csr fx) ->
      nt_frame_u1 fx R M sp parser key w1 w2 w3 ->
      above_sp MI A sp sp 24 -> above_sp MI A sp (sp + 40) 8 -> above_sp MI A sp (sp + 56) 32 -> above_sp MI A sp (sp + 260) 4 ->
      store_ok SEGS M (Z_to_bv 64 sp) 8 = true ->
      umapx MI 32 (nval32 SEGS) A M (parser + 136) bl bc ents -> above_sp MI A sp (parser + 136) 40 -> sp + 264 <= parser + 136 ->
      0 <= w1 < 2 ^ 64 -> 0 <= w2 < 2 ^ 64 -> 0 <= w3 < 2 ^ 64 -> val = (w1 mod 2 ^ 32, w2 mod 2 ^ 32, w3 mod 2 ^ 32) ->
      ro_clear L M ->
      Zlength ents + 1 < 2 ^ 24 -> LIB_NMAX <= NMAX MI -> bc <> BSEQ_LAST ->
      roomL MI A (live MI A) 32 ->
      ((bc = 0 \/ Zlength ents = bc) -> roomL MI A ((0, 32) :: live MI A) (8 * bseq_next bc)) ->
      (forall (fx' : FPState) A' R' M' model' (p bl' bc' : Z) (ents' : list (Z * (Z * (Z * Z * Z))))
              (inserted rehashed : bool),
          ainv MI A' M' model' -> mstd model' -> m_fs model' = m_fs model -> m_fds model' = m_fds model ->
          sx_inv ST s M' -> frm_zero (@fp_csr fx') -> fkept_u1 fx fx' ->
          nt_kept_u1 R R' -> getr R' 27%bv = Z_to_bv 64 p ->
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
          eff MI A A' M M' (sp - NT_STACK NEW_STACK DEL_STACK, sp)
              (fun a => umap_foot 32 (parser + 136) bl bc ents a \/ umap_foot 32 (parser + 136) bl' bc' ents' a
                        \/ (sp <= a < sp + 8)) ->
          defined M' sp 8 ->
          srealizes SEGS (mkCfg (@mkst fx' R' (Z_to_bv 64 (hc_nt_exit hc)) M' (seg_rom SEGS)) model') K) ->
      srealizes SEGS (mkCfg (@mkst fx R (Z_to_bv 64 (hc_nt_entry hc)) M (seg_rom SEGS)) model) K.
End StmtsU1.
