(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmEncSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Heap Require Import HeapIfaceU.
Import ListNotations.
Import PML.
Import PMES.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMES2.
(* [comment removed for export] *)
Definition enc_objx (M : mem) (V S2 dI dD : Z) : Prop :=
  u64 M V VT_VISITOR /\ u64 M (V + O_SINK) S2 /\ u64 M (V + O_OPT_VPTR) VT_ENC_OPTIONS /\
  (exists fl, u8 M (V + O_FLAGS) fl /\ Z.land fl 15 = 0) /\
  u8 M (V + O_BIGNUM_FMT) 0 /\
  u8 M (V + O_SPLITS) 0 /\ u8 M (V + O_SPLITS + 1) 0 /\ u8 M (V + O_SPLITS + 2) 0 /\ u8 M (V + O_SPLITS + 3) 0 /\ u8 M (V + O_SPLITS + 4) 0 /\
  u8 M (V + O_INDENT_SIZE) 4 /\ u64 M (V + O_LINE_LIMIT) 120 /\
  u64 M (V + O_NL_CHARS) 0xa02 /\ u64 M (V + O_NL_CHARS + 8) 0 /\ u64 M (V + O_NL_CHARS + 16) 0 /\ L5.defined M (V + O_NL_CHARS) 24 /\
  u64 M (V + O_COMMON_VPTR) VT_ENC_COMMON /\ (exists en, u8 M (V + O_ENABLE) en /\ Z.land en 63 = 0 /\ L5.defined M (V + O_ENABLE) 2) /\
  u32 M (V + O_MAX_DEPTH) MAX_DEPTH /\ u8 M (V + O_INDENT_CHAR) 32 /\
  u8 M (V + O_FP) 0 /\ u32 M (V + O_FP + 4) 0 /\ (exists dp, u8 M (V + O_FP + 8) dp) /\
  u32 M (V + O_INDENT) (4 * dI) /\ L5.defined M (V + O_COLUMN) 8 /\ u32 M (V + O_DEPTH) dD /\
  sv_at M (V + O_COLON) TXT_COLON 2 /\ sv_at M (V + O_COMMA) TXT_COMMA 2 /\ sv_at M (V + O_OBRACE) TXT_OBRACE 1 /\ sv_at M (V + O_CBRACE) TXT_CBRACE 1 /\
  sv_at M (V + O_OBRACKET) TXT_OBRACKET 1 /\ sv_at M (V + O_CBRACKET) TXT_CBRACKET 1.
Lemma enc_objx_eq : forall M V S2 d, enc_obj M V S2 d = enc_objx M V S2 d d.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Record bkind : Type := BK { bk_arr : bool; bk_tail : Z; bk_open : Z }.
Definition BK_OBJECT : bkind := BK false 0x3c610 O_OBRACE.
Definition BK_ARRAY : bkind := BK true 0x3cb78 O_OBRACKET.
(* [comment removed for export] *)
Definition PC_MID_OBJ_ROOT : Z := 0x3c508.   Definition PC_MID_OBJ_NESTED : Z := 0x3c58c.
Definition PC_MID_ARR_ROOT : Z := 0x3c998.   Definition PC_MID_ARR_INOBJ : Z := 0x3c9f0.    Definition PC_MID_ARR_INARR : Z := 0x3ca9c.

Definition FRAME : Z := 64.
Definition LOC (arr : bool) : Z := if arr then 24 else 32.
Definition KEPT (arr : bool) : list Z := if arr then [3; 20; 21; 22; 23; 24; 25; 26; 27] else [3; 19; 20; 21; 22; 23; 24; 25; 26; 27].

(* [comment removed for export] *)
Definition stack_mid (M : mem) (V : Z) (es : estate) (c0 : ectx) (b capb : Z) : Prop :=
  u64 M (V + O_STACK) b /\ u64 M (V + O_STACK + 16) (b + capb) /\
  32 * (depth es + 1) <= capb /\ (exists k, 0 <= k <= 10 /\ capb = 32 * 2 ^ k) /\
  (forall i, (i < length es)%nat -> ctx_at M (b + 32 * Z.of_nat i) (nth (length es - 1 - i) es ctx0)) /\
  ctx_at M (b + 32 * depth es) c0.
(* [comment removed for export] *)
Definition W_mid (K : bkind) (V sp : Z) : list L5.range := [(V + O_STACK, 24); (sp, LOC (bk_arr K))].

Section Specs.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.

(* [comment removed for export] *)
Definition cps_seg (pc r sp scr : Z) (LB : list (Z * Z)) (cr : credit)
           (Pre : bvmap 5 word -> mem -> Prop)
           (Post : bvmap 5 word -> mem -> bvmap 5 word -> mem -> list (Z * Z) -> credit -> list (Z * Z) -> list L5.range -> Prop) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (K : TSet),
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] -> fp_ok fx -> Pre R M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range),
        fp_ok fx' -> Post R M R' M' LB' cr' LBk W ->
        L5C.hpres L LBk sp scr W M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (@cfg fx' R' r M' model') K) ->
    srealizes RSEGS SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition regs_kept (arr : bool) (R R' : bvmap 5 word) : Prop := forall r : bv 5, In (bv_unsigned r) (KEPT arr) -> getr R' r = getr R r.

(* [comment removed for export] *)
Definition MID_SCR : Z := 144 + OPNEWX_SCR.

(* [comment removed for export] *)
Definition mid_spec (K : bkind) (pcm : Z) (GX : estate -> Prop) (RX : bvmap 5 word -> mem -> Z -> Z -> Z -> Prop) : Prop :=
  forall (LBo : list (Z * Z)) (cr : credit) (sp V S2 b capb dI dD : Z) (es : estate),
    cps_seg pcm (bk_tail K) sp MID_SCR (LBo ++ stack_blocks b capb) cr
      (fun R M => getr R 2%bv = Z_to_bv 64 sp /\ getr R 4%bv = Z_to_bv 64 TP /\ L5C.stk (hl_sptop L) M sp MID_SCR /\ sp mod 16 = 0 /\
                  getr R 8%bv = Z_to_bv 64 V /\ getr R 9%bv = Z_to_bv 64 (V + O_STACK) /\ GX es /\ RX R M sp b (b + 32 * depth es) /\
                  enc_objx M V S2 dI dD /\ stack_at M V es b capb /\ depth es < MAX_DEPTH /\
                  obj_on_stack L (sp + FRAME) V ENC_SIZE /\ L5.defined M sp FRAME /\
                  (32 * depth es = capb -> credit_ok L cr (stack_grow capb) /\ stack_grow capb <= NBU))
      (fun R M R' M' LB' cr' LBk W => exists (b' capb' : Z),
          getr R' 2%bv = Z_to_bv 64 sp /\ getr R' 4%bv = Z_to_bv 64 TP /\ getr R' 8%bv = Z_to_bv 64 V /\ getr R' 10%bv = Z_to_bv 64 (b' + 32 * (depth es + 1)) /\
          regs_kept (bk_arr K) R R' /\
          enc_objx M' V S2 dI dD /\ stack_mid M' V es (ECtx (bk_arr K) 0 false) b' capb' /\
          LB' = LBo ++ [(b', capb')] /\ LBk = LBo /\ W = W_mid K V sp /\
          ((32 * depth es < capb /\ b' = b /\ capb' = capb /\ cr' = cr) \/
           (32 * depth es = capb /\ capb' = stack_grow capb /\ cr' = debit L cr (stack_grow capb)))).

(* [comment removed for export] *)
Definition is_root (es : estate) : Prop := es = [].
Definition is_nested (es : estate) : Prop := es <> [].
Definition RX_OBJ_ROOT (R : bvmap 5 word) (M : mem) (sp b e : Z) : Prop := getr R 18%bv = Z_to_bv 64 e.
Definition RX_OBJ_NESTED (R : bvmap 5 word) (M : mem) (sp b e : Z) : Prop := u8 M (sp + 31) 0.
Definition RX_ARR_ROOT (R : bvmap 5 word) (M : mem) (sp b e : Z) : Prop := getr R 18%bv = Z_to_bv 64 e /\ getr R 19%bv = Z_to_bv 64 b.
Definition RX_ARR_INOBJ (R : bvmap 5 word) (M : mem) (sp b e : Z) : Prop := getr R 18%bv = Z_to_bv 64 e /\ getr R 19%bv = Z_to_bv 64 b.
Definition RX_ARR_INARR (R : bvmap 5 word) (M : mem) (sp b e : Z) : Prop := getr R 19%bv = Z_to_bv 64 1 /\ u8 M (sp + 23) 0.
Definition mid_obj_root_spec : Prop := mid_spec BK_OBJECT PC_MID_OBJ_ROOT is_root RX_OBJ_ROOT.
Definition mid_obj_nested_spec : Prop := mid_spec BK_OBJECT PC_MID_OBJ_NESTED is_nested RX_OBJ_NESTED.
Definition mid_arr_root_spec : Prop := mid_spec BK_ARRAY PC_MID_ARR_ROOT is_root RX_ARR_ROOT.
Definition mid_arr_inobj_spec : Prop := mid_spec BK_ARRAY PC_MID_ARR_INOBJ is_nested RX_ARR_INOBJ.
Definition mid_arr_inarr_spec : Prop := mid_spec BK_ARRAY PC_MID_ARR_INARR is_nested RX_ARR_INARR.
(* [comment removed for export] *)
Definition frame_at (arr : bool) (M : mem) (sp r s0v s1v s2v s3v : Z) : Prop :=
  u64 M (sp + 56) r /\ u64 M (sp + 48) s0v /\ u64 M (sp + 40) s1v /\ u64 M (sp + 32) s2v /\ (arr = true -> u64 M (sp + 24) s3v).

(* [comment removed for export] *)
Definition TAIL_SCR : Z := STRX_SCR.
Definition W_tail (V S2 : Z) : list L5.range := [(V + O_STACK, 40); (S2, 24)].
Definition tail_spec (K : bkind) : Prop :=
  forall (LBo : list (Z * Z)) (cr : credit) (sp V S2 b capb kx bx r s0v s1v s2v s3v : Z) (es : estate) (rep : srep),
    cps_seg (bk_tail K) r sp TAIL_SCR (LBo ++ srep_blocks rep ++ [(b, capb)]) cr
      (fun R M => getr R 2%bv = Z_to_bv 64 sp /\ getr R 4%bv = Z_to_bv 64 TP /\ L5C.stk (hl_sptop L) M sp TAIL_SCR /\ sp mod 16 = 0 /\
                  getr R 8%bv = Z_to_bv 64 V /\ getr R 10%bv = Z_to_bv 64 (b + 32 * (depth es + 1)) /\
                  frame_at (bk_arr K) M sp r s0v s1v s2v s3v /\ L5.ra_ok r /\ L5.defined M sp FRAME /\ L5.defined M (V + O_STACK + 8) 8 /\
                  enc_objx M V S2 (depth es) (depth es + 1) /\ stack_mid M V es (ECtx (bk_arr K) 0 false) b capb /\ depth es < MAX_DEPTH /\
                  sink_at M S2 rep /\ screditU L cr rep kx bx /\ len (srep_chars rep) + 1 <= CLU /\ img_ro M /\
                  obj_on_stack L (sp + FRAME) V ENC_SIZE /\ obj_on_stack L (sp + FRAME) S2 24 /\ apart V ENC_SIZE S2 24)
      (fun R M R' M' LB' cr' LBk W => exists (rep' : srep),
          getr R' 2%bv = Z_to_bv 64 (sp + FRAME) /\ getr R' 4%bv = Z_to_bv 64 TP /\ a0 R' 1 /\ regs_kept (bk_arr K) R R' /\
          getr R' 8%bv = Z_to_bv 64 s0v /\ getr R' 9%bv = Z_to_bv 64 s1v /\ getr R' 18%bv = Z_to_bv 64 s2v /\
          (bk_arr K = true -> getr R' 19%bv = Z_to_bv 64 s3v) /\
          enc_inv M' V S2 (EG (ECtx (bk_arr K) 0 false :: es) (len (srep_chars rep) + 1) rep' b capb) /\
          LB' = LBo ++ srep_blocks rep' ++ [(b, capb)] /\ LBk = LBo /\ W = W_tail V S2 /\ screditU L cr' rep' kx bx).
Definition tail_obj_spec : Prop := tail_spec BK_OBJECT.
Definition tail_arr_spec : Prop := tail_spec BK_ARRAY.

(* [comment removed for export] *)
Definition HEAD_SCR : Z := 96 + NEWLINE_SCR.
Definition W_head (V S2 : Z) : list L5.range := [(V + O_COLUMN, 8); (V + O_DEPTH, 4); (S2, 24)].
(* [comment removed for export] *)
Definition head_post (M : mem) (V S2 : Z) (es : estate) (len0 : Z) (rep' : srep) (b capb : Z) : Prop :=
  enc_objx M V S2 (depth es) (depth es + 1) /\
  stack_at M V (match es with [] => [] | c :: r => if ec_arr c then set_nla c :: r else es end) b capb /\
  sink_at M S2 rep' /\ len (srep_chars rep') = len0 + (match es with [] => 0 | c :: _ => if ec_arr c then comma c + nl es else 0 end).
Definition head_spec (arr : bool) (pc pcm : Z) (GX : estate -> Prop) (RX : bvmap 5 word -> mem -> Z -> Z -> Z -> Prop) : Prop :=
  forall (LBo : list (Z * Z)) (cr : credit) (sp r V S2 kx bx : Z) (g : eghost),
    cps_seg pc pcm sp HEAD_SCR (LBo ++ g_lbv g) cr
      (fun R M => entry L R M sp r (VIS_SCR WD_SCR_X) /\ a0 R V /\ GX (g_es g) /\ enc_inv M V S2 g /\ depth (g_es g) < MAX_DEPTH /\ img_ro M /\ lits_ok M /\
                  eroomU g (EvBegin arr) /\ ecreditU L cr g kx bx /\ objs_enc L sp V S2)
      (fun R M R' M' LB' cr' LBk W => exists (rep' : srep),
          getr R' 2%bv = Z_to_bv 64 (sp - FRAME) /\ getr R' 4%bv = Z_to_bv 64 TP /\ getr R' 8%bv = Z_to_bv 64 V /\ getr R' 9%bv = Z_to_bv 64 (V + O_STACK) /\
          RX R' M' (sp - FRAME) (g_sb g) (g_sb g + 32 * depth (g_es g)) /\ regs_kept arr R R' /\
          frame_at arr M' (sp - FRAME) r (bv_unsigned (getr R 8%bv)) (bv_unsigned (getr R 9%bv)) (bv_unsigned (getr R 18%bv)) (bv_unsigned (getr R 19%bv)) /\
          L5.defined M' (sp - FRAME) FRAME /\
          head_post M' V S2 (g_es g) (g_len g) rep' (g_sb g) (g_scap g) /\ lits_ok M' /\ img_ro M' /\
          LB' = LBo ++ srep_blocks rep' ++ stack_blocks (g_sb g) (g_scap g) /\ LBk = LBo /\ W = W_head V S2 /\
          screditU L cr' rep' (kx + kv_st (g_scap g) * hl_k_per_malloc L) (bx + bpot_st L (g_scap g))).
(* [comment removed for export] *)
Definition par_root (es : estate) : Prop := es = [].
Definition par_obj (es : estate) : Prop := match es with c :: _ => ec_arr c = false | [] => False end.
Definition par_arr (es : estate) : Prop := match es with c :: _ => ec_arr c = true | [] => False end.
Definition head_obj_root_spec : Prop := head_spec false PC_VISIT_BEGIN_OBJECT PC_MID_OBJ_ROOT par_root RX_OBJ_ROOT.
Definition head_obj_inobj_spec : Prop := head_spec false PC_VISIT_BEGIN_OBJECT PC_MID_OBJ_NESTED par_obj RX_OBJ_NESTED.
Definition head_obj_inarr_spec : Prop := head_spec false PC_VISIT_BEGIN_OBJECT PC_MID_OBJ_NESTED par_arr RX_OBJ_NESTED.
Definition head_arr_root_spec : Prop := head_spec true PC_VISIT_BEGIN_ARRAY PC_MID_ARR_ROOT par_root RX_ARR_ROOT.
Definition head_arr_inobj_spec : Prop := head_spec true PC_VISIT_BEGIN_ARRAY PC_MID_ARR_INOBJ par_obj RX_ARR_INOBJ.
Definition head_arr_inarr_spec : Prop := head_spec true PC_VISIT_BEGIN_ARRAY PC_MID_ARR_INARR par_arr RX_ARR_INARR.
End Specs.
End PMES2.
