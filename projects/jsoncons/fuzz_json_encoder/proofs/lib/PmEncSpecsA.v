(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA LibIface FPSteps L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeapA CutL5A.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMESA.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PC_NEW_LINE_xasan : Z := 0xba814.        Definition PC_NEW_LINE_LEN_xasan : Z := 0xcaf94.    Definition PC_BEGIN_SCALAR_xasan : Z := 0xbaeb0.
Definition PC_WRITE_STRING_xasan : Z := 0xbbf24.    Definition PC_WRITE_BIGNUM_xasan : Z := 0xbd2b0.    Definition PC_ESCAPE_STRING_xasan : Z := 0xbded8.
Definition PC_TO_CODEPOINT_xasan : Z := 0xc59ec.    Definition PC_FROM_INT_U64_xasan : Z := 0xbb0cc.    Definition PC_FROM_INT_I64_xasan : Z := 0xbb72c.
Definition PC_WRITE_DOUBLE_xasan : Z := 0xbc830.    Definition PC_NULL_LIT_xasan : Z := 0xbc1e0.        Definition PC_TRUE_LIT_xasan : Z := 0xcb56c.
Definition PC_FALSE_LIT_xasan : Z := 0xcb5e0.       Definition PC_VISIT_END_ARRAY_xasan : Z := 0xb40f0. Definition PC_VISIT_UINT64_xasan : Z := 0xb463c.
Definition PC_VISIT_INT64_xasan : Z := 0xb4864.     Definition PC_VISIT_DOUBLE_xasan : Z := 0xb4a8c.    Definition PC_VISIT_FLUSH_xasan : Z := 0xb5c8c.
Definition PC_VISIT_BEGIN_OBJECT_xasan : Z := 0xb5c90. Definition PC_VISIT_END_OBJECT_xasan : Z := 0xb636c. Definition PC_VISIT_BEGIN_ARRAY_xasan : Z := 0xb68b8.
Definition PC_VISIT_KEY_xasan : Z := 0xb6ff0.       Definition PC_VISIT_NULL_xasan : Z := 0xb76d4.      Definition PC_VISIT_BOOL_xasan : Z := 0xb7930.
Definition PC_VISIT_STRING_xasan : Z := 0xb7bc8.    Definition PC_ENC_CTOR_xasan : Z := 0xb13d0.        Definition PC_ENC_CTOR_MAIN_xasan : Z := 0xb34b0.
Definition PC_ENC_DTOR_xasan : Z := 0xb1e94.        Definition PC_STACK_DTOR_xasan : Z := 0xba3dc.      Definition PC_EMPLACE_ROOT_xasan : Z := 0xca1ac.
Definition PC_EMPLACE_NESTED_xasan : Z := 0xca6bc.  Definition PC_ANN_INCREASE_xasan : Z := 0xcabcc.    Definition PC_ANN_SHRINK_xasan : Z := 0xba5a0.
Definition PC_ANN_NEW_xasan : Z := 0xcaf08.         Definition PC_SWAP_OUT_xasan : Z := 0xcac74.       Definition PC_SPLIT_DTOR_xasan : Z := 0xcade0.
Definition PC_CTX_ALLOCATE_xasan : Z := 0xcaecc.
(* [comment removed for export] *)
Record econsts : Type := ECONSTS {
  VT_ENC_OPTIONS : Z; VT_ENC_COMMON : Z;
  TXT_COLON : Z; TXT_COMMA : Z; TXT_OBRACE : Z; TXT_CBRACE : Z; TXT_OBRACKET : Z; TXT_CBRACKET : Z }.
Definition EC_xasan : econsts := {|
  VT_ENC_OPTIONS := 0x15ab70; VT_ENC_COMMON := 0x15ab98;
  TXT_COLON := 0x24b14; TXT_COMMA := 0x24b1c; TXT_OBRACE := 0x24b28; TXT_CBRACE := 0x24b29; TXT_OBRACKET := 0x24b2e; TXT_CBRACKET := 0x24b2f |}.
(* [comment removed for export] *)
Definition PC_NEW_LINE_xboth : Z := 0xbc29c.        Definition PC_NEW_LINE_LEN_xboth : Z := 0xced48.    Definition PC_BEGIN_SCALAR_xboth : Z := 0xbc9b0.
Definition PC_WRITE_STRING_xboth : Z := 0xbdb88.    Definition PC_WRITE_BIGNUM_xboth : Z := 0xbf090.    Definition PC_ESCAPE_STRING_xboth : Z := 0xbfd34.
Definition PC_TO_CODEPOINT_xboth : Z := 0xc8b68.    Definition PC_FROM_INT_U64_xboth : Z := 0xbcca4.    Definition PC_FROM_INT_I64_xboth : Z := 0xbd328.
Definition PC_WRITE_DOUBLE_xboth : Z := 0xbe5b8.    Definition PC_NULL_LIT_xboth : Z := 0xbdf30.        Definition PC_TRUE_LIT_xboth : Z := 0xcf254.
Definition PC_FALSE_LIT_xboth : Z := 0xcf2c8.       Definition PC_VISIT_END_ARRAY_xboth : Z := 0xb4c40. Definition PC_VISIT_UINT64_xboth : Z := 0xb520c.
Definition PC_VISIT_INT64_xboth : Z := 0xb543c.     Definition PC_VISIT_DOUBLE_xboth : Z := 0xb566c.    Definition PC_VISIT_FLUSH_xboth : Z := 0xb6818.
Definition PC_VISIT_BEGIN_OBJECT_xboth : Z := 0xb681c. Definition PC_VISIT_END_OBJECT_xboth : Z := 0xb70d4. Definition PC_VISIT_BEGIN_ARRAY_xboth : Z := 0xb76a0.
Definition PC_VISIT_KEY_xboth : Z := 0xb820c.       Definition PC_VISIT_NULL_xboth : Z := 0xb8984.      Definition PC_VISIT_BOOL_xboth : Z := 0xb8bec.
Definition PC_VISIT_STRING_xboth : Z := 0xb8ea4.    Definition PC_ENC_CTOR_xboth : Z := 0xb1cb4.        Definition PC_ENC_CTOR_MAIN_xboth : Z := 0xb3fb8.
Definition PC_ENC_DTOR_xboth : Z := 0xb278c.
Definition EC_xboth : econsts := {|
  VT_ENC_OPTIONS := 0x15e590; VT_ENC_COMMON := 0x15e5b8;
  TXT_COLON := 0x24b74; TXT_COMMA := 0x24b7c; TXT_OBRACE := 0x24b88; TXT_CBRACE := 0x24b89; TXT_OBRACKET := 0x24b8e; TXT_CBRACKET := 0x24b8f |}.

(* [comment removed for export] *)
Abbreviation ectx := PMES.ectx.       Abbreviation estate := PMES.estate.   Abbreviation eev := PMES.eev.         Abbreviation eghost := PMES.eghost.
Abbreviation srep := PML.srep.         Abbreviation len := PMES.len.         Abbreviation depth := PMES.depth.
Abbreviation ENC_SIZE := PMES.ENC_SIZE.   Abbreviation MAX_DEPTH := PMES.MAX_DEPTH.
Abbreviation O_SINK := PMES.O_SINK.   Abbreviation O_OPT_VPTR := PMES.O_OPT_VPTR.   Abbreviation O_FLAGS := PMES.O_FLAGS.   Abbreviation O_BIGNUM_FMT := PMES.O_BIGNUM_FMT.
Abbreviation O_SPLITS := PMES.O_SPLITS.   Abbreviation O_INDENT_SIZE := PMES.O_INDENT_SIZE.   Abbreviation O_LINE_LIMIT := PMES.O_LINE_LIMIT.   Abbreviation O_NL_CHARS := PMES.O_NL_CHARS.
Abbreviation O_COMMON_VPTR := PMES.O_COMMON_VPTR.   Abbreviation O_ENABLE := PMES.O_ENABLE.   Abbreviation O_MAX_DEPTH := PMES.O_MAX_DEPTH.   Abbreviation O_INDENT_CHAR := PMES.O_INDENT_CHAR.
Abbreviation O_FP := PMES.O_FP.   Abbreviation O_STACK := PMES.O_STACK.   Abbreviation O_INDENT := PMES.O_INDENT.   Abbreviation O_COLUMN := PMES.O_COLUMN.
Abbreviation O_COLON := PMES.O_COLON.   Abbreviation O_COMMA := PMES.O_COMMA.   Abbreviation O_OBRACE := PMES.O_OBRACE.   Abbreviation O_CBRACE := PMES.O_CBRACE.
Abbreviation O_OBRACKET := PMES.O_OBRACKET.   Abbreviation O_CBRACKET := PMES.O_CBRACKET.   Abbreviation O_DEPTH := PMES.O_DEPTH.

(* [comment removed for export] *)
Definition pay_hi (ev : eev) : Z :=
  match ev with
  | PMES.EvBegin _ | PMES.EvEnd => 0 | PMES.EvKey bs => PMES.esc_len bs
  | PMES.EvStr tag bs => if (tag =? 1) || (tag =? 2) || (tag =? 3) then len bs else PMES.esc_len bs
  | PMES.EvNull => 4 | PMES.EvBool b => if b then 4 else 5 | PMES.EvU64 | PMES.EvI64 => 20 | PMES.EvDbl => 28
  end.
Lemma pay_ok_hi : forall ev pay, PMES.pay_ok ev pay -> PMES.pay_lo ev <= pay <= pay_hi ev.
Proof. intros ev pay H. destruct ev; cbn in *; lia. Qed.
(* [comment removed for export] *)
Definition kmax (es : estate) (ev : eev) : Z := PMES.ev_ind es ev + pay_hi ev.

Section SpecsA.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable IC : PMLA.consts.          (* [comment removed for export] *)
Variable EC : econsts.              (* [comment removed for export] *)
Variable WD_SCRA : Z.               (* [comment removed for export] *)
Variable CL : Z.                    (* [comment removed for export] *)
Variable onmax : Z.                 (* [comment removed for export] *)

Abbreviation cps_asan := (PMSA.cps_asan L ar HI).
Abbreviation mem := PMSA.mem.
Abbreviation a0 := PMSA.a0.   Abbreviation a1 := PMSA.a1.   Abbreviation a2 := PMSA.a2.   Abbreviation a3 := PMSA.a3.   Abbreviation a4 := PMSA.a4.
Abbreviation u8 := (PMSA.u8 L).   Abbreviation u32 := (PMSA.u32 L).   Abbreviation u64 := (PMSA.u64 L).
Abbreviation str_at := (PMSA.str_at L).   Abbreviation fobj := PMSA.fobj.   Abbreviation stksh := (PMSA.stksh ar).   Abbreviation acobj := (PMSA.acobj ar).
Abbreviation afresh := (PMSA.afresh L ar).   Abbreviation text_inA := PMSA.text_inA.   Abbreviation apart := PMLA.apart.
Definition img_ro (M : mem) : Prop := PMLA.img_ro IC M.
Definition lits_ok (M : mem) : Prop := PMLA.lits_ok (hl_segs L) IC M.
Definition b2z := PML.b2z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sink_atA (M : mem) (o : Z) (rep : srep) : Prop := str_at M o rep /\ L5.defined M o 24 /\ PMES.rep_ok rep /\ PMLA.srep_sh M rep.
(* [comment removed for export] *)
Definition ctx_at (M : mem) (a : Z) (c : ectx) : Prop :=
  u32 M a (b2z (PMES.ec_arr c)) /\ u8 M (a + 4) 0 /\ u8 M (a + 6) (b2z (PMES.ec_nla c)) /\ u64 M (a + 24) (PMES.ec_count c) /\ 0 <= PMES.ec_count c < 2 ^ 64 /\ L5.defined M a 32.
(* [comment removed for export] *)
Definition stack_at (M : mem) (V : Z) (es : estate) (b capb : Z) : Prop :=
  u64 M (V + O_STACK) b /\ u64 M (V + O_STACK + 8) (b + 32 * depth es) /\ u64 M (V + O_STACK + 16) (b + capb) /\
  32 * depth es <= capb /\ ((capb = 0 /\ b = 0) \/ (exists k, 0 <= k <= 10 /\ capb = 32 * 2 ^ k)) /\
  (forall i, (i < length es)%nat -> ctx_at M (b + 32 * Z.of_nat i) (nth (length es - 1 - i) es PMES.ctx0)).
(* [comment removed for export] *)
Definition stack_sh (M : mem) (es : estate) (b capb : Z) : Prop := capb = 0 \/ shadow_cont M b capb (32 * depth es).
Definition sv_at (M : mem) (a txt n : Z) : Prop := u64 M a txt /\ u64 M (a + 8) n.
(* [comment removed for export] *)
Definition enc_objA (M : mem) (V S2 d : Z) : Prop :=
  u64 M V (PMLA.VT_VISITOR IC) /\ u64 M (V + O_SINK) S2 /\ u64 M (V + O_OPT_VPTR) (VT_ENC_OPTIONS EC) /\
  (exists fl, u8 M (V + O_FLAGS) fl /\ Z.land fl 15 = 0) /\
  u8 M (V + O_BIGNUM_FMT) 0 /\
  u8 M (V + O_SPLITS) 0 /\ u8 M (V + O_SPLITS + 1) 0 /\ u8 M (V + O_SPLITS + 2) 0 /\ u8 M (V + O_SPLITS + 3) 0 /\ u8 M (V + O_SPLITS + 4) 0 /\
  u8 M (V + O_INDENT_SIZE) 4 /\ u64 M (V + O_LINE_LIMIT) 120 /\
  u64 M (V + O_NL_CHARS) 0xa02 /\ u64 M (V + O_NL_CHARS + 8) 0 /\ u64 M (V + O_NL_CHARS + 16) 0 /\ L5.defined M (V + O_NL_CHARS) 24 /\
  u64 M (V + O_COMMON_VPTR) (VT_ENC_COMMON EC) /\ (exists en, u8 M (V + O_ENABLE) en /\ Z.land en 63 = 0 /\ L5.defined M (V + O_ENABLE) 2) /\
  u32 M (V + O_MAX_DEPTH) MAX_DEPTH /\ u8 M (V + O_INDENT_CHAR) 32 /\
  u8 M (V + O_FP) 0 /\ u32 M (V + O_FP + 4) 0 /\ (exists dp, u8 M (V + O_FP + 8) dp) /\
  u32 M (V + O_INDENT) (4 * d) /\ L5.defined M (V + O_COLUMN) 8 /\ u32 M (V + O_DEPTH) d /\
  sv_at M (V + O_COLON) (TXT_COLON EC) 2 /\ sv_at M (V + O_COMMA) (TXT_COMMA EC) 2 /\ sv_at M (V + O_OBRACE) (TXT_OBRACE EC) 1 /\ sv_at M (V + O_CBRACE) (TXT_CBRACE EC) 1 /\
  sv_at M (V + O_OBRACKET) (TXT_OBRACKET EC) 1 /\ sv_at M (V + O_CBRACKET) (TXT_CBRACKET EC) 1 /\
  L5.defined M V ENC_SIZE.
(* [comment removed for export] *)
Definition opts_idle (M : mem) (V : Z) : Prop :=
  u64 M (V + 96) 0 /\ u64 M (V + 120) 0 /\ u64 M (V + 144) 0 /\ u64 M (V + 168) 0 /\ u64 M (V + 192) 0 /\ u64 M (V + 216) 0.
(* [comment removed for export] *)
Definition lbv_rng (V S2 : Z) (g : eghost) : Prop :=
  0 <= V /\ V + ENC_SIZE <= 2 ^ 47 /\ 0 <= S2 /\ S2 + 24 <= 2 ^ 47 /\
  (forall b, In b (PMES.g_lbv g) -> 0 <= fst b /\ fst b mod 16 = 0 /\ 0 < snd b /\ fst b + snd b <= 2 ^ 47).
(* [comment removed for export] *)
Definition enc_invA (M : mem) (V S2 : Z) (g : eghost) : Prop :=
  enc_objA M V S2 (depth (PMES.g_es g)) /\ stack_at M V (PMES.g_es g) (PMES.g_sb g) (PMES.g_scap g) /\ stack_sh M (PMES.g_es g) (PMES.g_sb g) (PMES.g_scap g) /\
  sink_atA M S2 (PMES.g_rep g) /\ len (PML.srep_chars (PMES.g_rep g)) = PMES.g_len g /\ depth (PMES.g_es g) <= MAX_DEPTH /\ lbv_rng V S2 g.
(* [comment removed for export] *)
Definition objs_encA (M : mem) (FF : list fframe) (V S2 : Z) : Prop := fobj M FF V ENC_SIZE /\ fobj M FF S2 24 /\ apart V ENC_SIZE S2 24.
(* [comment removed for export] *)
Definition W_encA (V S2 : Z) : list L5.range := [(V + PMES.O_STACK, 40); (V + PMES.O_DEPTH, 4); (S2, 24); (PMLA.LIT_LO IC, PMLA.LIT_HI IC - PMLA.LIT_LO IC)].
Definition efootA (V S2 : Z) (g : PMES.eghost) (a : Z) : Prop :=
  (V <= a < V + PMES.ENC_SIZE) \/ (S2 <= a < S2 + 24) \/ in_block (PMES.g_lbv g) a \/ (exists b, In b (PMES.g_lbv g) /\ in_shadow_of (fst b) (snd b) a) \/
  in_shadow_of V PMES.ENC_SIZE a \/ in_shadow_of S2 24 a.
Definition enc_agreeP : Prop :=
  forall (M M' : mem) V S2 g, enc_invA M V S2 g -> (forall a, efootA V S2 g a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> enc_invA M' V S2 g.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kenc (eg : PMES.eghost) : Z := (PMES.kv_s2 (PMES.g_rep eg) + PMES.kv_st (PMES.g_scap eg)) * hl_k_per_malloc L.
Definition bpot_s2 (rep : srep) : Z := hl_b_lin L * Z.max 0 (4 * CL + 16 - 2 * PMES.alloc_of rep) + hl_b_overhead L * PMES.kv_s2 rep.
Definition bpot_st (capb : Z) : Z := hl_b_lin L * Z.max 0 (65536 - 2 * capb) + hl_b_overhead L * PMES.kv_st capb.
Definition benc (eg : PMES.eghost) : Z := bpot_s2 (PMES.g_rep eg) + bpot_st (PMES.g_scap eg).
(* [comment removed for export] *)
Definition ecreditA (cr : credit) (g : PMES.eghost) (kx bx : Z) : Prop := 0 <= kx /\ kenc g <= fst cr - kx /\ 0 <= bx /\ benc g <= snd cr - bx.
(* [comment removed for export] *)
Definition screditA (cr : credit) (rep : srep) (kx bx : Z) : Prop :=
  0 <= kx /\ PMES.kv_s2 rep * hl_k_per_malloc L <= fst cr - kx /\ 0 <= bx /\ bpot_s2 rep <= snd cr - bx.
(* [comment removed for export] *)
Definition eroomA (g : eghost) (ev : eev) : Prop := PMES.g_len g + kmax (PMES.g_es g) ev <= CL.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition OPNEWX_SCRA : Z := PMSA.OPNEW_SCR.
Definition opnew_x_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (n sp r : Z),
    cps_asan pc r sp OPNEWX_SCRA LB FF LK cr A 0
      (fun R M => a0 R n /\ 0 < n <= onmax /\ acredit_ok L cr n)
      (fun R M R' M' LB' cr' LBk W => exists q, a0 R' q /\ afresh LB FF M' q n /\ LB' = (q, n) :: LB /\ cr' = adebit L cr n /\ LBk = LB /\ W = []).
(* [comment removed for export] *)
Definition amem_preX (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
           (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (dst n : Z) (K : ShapeAlg.TSet) : Prop :=
  ri_inv HI LB FF LK cr A M (vml_of model) /\ m_halted model = None /\ MInv A model /\
  getr R 10%bv = Z_to_bv 64 dst /\ getr R 12%bv = Z_to_bv 64 n /\ 0 <= n <= onmax /\
  getr R 4%bv = Z_to_bv 64 (hl_tp L) /\ Hoare.ret_ok (getr R 1%bv) /\
  astack_ok L ar M (hl_scr_mem L) (bv_unsigned (getr R 2%bv)) /\
  aacc M dst n /\ (forall i, 0 <= i < n -> aclientw L ar LB FF (bv_unsigned (getr R 2%bv)) (hl_scr_mem L) (dst + i)) /\
  (forall i (m : nat), 0 <= i -> i + Z.of_nat m <= n -> store_ok (hl_segs L) M (Z_to_bv 64 (dst + i)) m = true) /\
  K [] /\ app_rng ar dst n.
Definition amemcpy_x_spec_at (pc : Z) (may_overlap : bool) : Prop :=
  forall fx R M model LB FF LK cr A dst src n (bs : list byte) K,
    amem_preX fx R M model LB FF LK cr A dst n K -> getr R 11%bv = Z_to_bv 64 src ->
    aacc M src n -> 0 <= src /\ src + n <= 2 ^ 47 -> app_rng ar src n ->
    (forall i, 0 <= i < n -> hl_img_lo L <= src + i < hl_img_hi L \/ aclient L ar LB FF (bv_unsigned (getr R 2%bv)) (hl_scr_mem L) (src + i)) ->
    rdn (hl_segs L) M (Z_to_bv 64 src) (Z.to_nat n) = Some bs ->
    (may_overlap = false -> dst + n <= src \/ src + n <= dst) ->
    amem_post L ar SCFG HI fx R M model LB FF LK cr A dst n (fun i v => nth_error bs (Z.to_nat i) = Some (Z_to_bv 8 v) /\ 0 <= v < 256) K ->
    srealizes (hl_segs L) SCFG (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs L))) model) K.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STRX_SCRA : Z := PMSA.STR_SCR.
(* [comment removed for export] *)
Definition x_grownA (LB : list (Z * Z)) (FF : list fframe) (M' : mem) (o : Z) (rep : srep) (s' : list Z) (LB' : list (Z * Z)) (LBk : list (Z * Z)) (rep' : srep) : Prop :=
     (PMES.fits rep (len s') /\ rep' = PMES.same_rep rep s' /\ sink_atA M' o rep' /\ LB' = LB /\ LBk = PMES.lb_drop rep LB)
  \/ (~ PMES.fits rep (len s') /\ exists p', let cap' := PML.grow_cap (PMES.alloc_of rep) (len s') in
        rep' = PML.SLong cap' p' s' /\ sink_atA M' o rep' /\ afresh (PMES.lb_drop rep LB) FF M' p' cap' /\ LB' = (p', cap') :: PMES.lb_drop rep LB /\ LBk = PMES.lb_drop rep LB).

Definition str_push_back_x_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o c sp r kx bx : Z) (rep : srep),
    cps_asan pc r sp STRX_SCRA LB FF LK cr A 0
      (fun R M => a0 R o /\ a1 R c /\ 0 <= c < 256 /\ sink_atA M o rep /\ PMES.rep_live rep LB /\ fobj M FF o 24 /\ stksh M sp STRX_SCRA /\
                  screditA cr rep kx bx /\ len (PML.srep_chars rep) + 1 <= CL)
      (fun R M R' M' LB' cr' LBk W => exists rep', x_grownA LB FF M' o rep (PML.srep_chars rep ++ [c]) LB' LBk rep' /\ screditA cr' rep' kx bx /\ W = [(o, 24)]).

(* [comment removed for export] *)
Definition gran_zero (M : mem) (q k : Z) : Prop := shadow_zero M (q - q mod 8) ((q mod 8 + k + 7) / 8).
(* [comment removed for export] *)
Definition img_aacc (q k : Z) : Prop := forall LB FF LK cr A (M : mem) V, ri_inv HI LB FF LK cr A M V -> aacc M q k.
Definition src_okA (M : mem) (LB : list (Z * Z)) (FF : list fframe) (sp o : Z) (rep : srep) (q k : Z) : Prop :=
     k = 0
  \/ (PMLA.IMG_RO_LO IC <= q /\ q + k <= PMLA.IMG_RO_HI IC /\ img_ro M /\ img_aacc q k)
  \/ (sp <= q /\ q + k <= ar_sptop ar /\ apart q k o 24 /\ L5.defined M q k /\ gran_zero M q k)
  \/ (L5.defined M q k /\ text_inA M (PMES.lb_drop rep LB) q k)
  \/ (L5.defined M q k /\ CL5A.ainfr FF q k /\ apart q k o 24 /\ gran_zero M q k).

Definition str_append_x_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o q sp r kx bx : Z) (rep : srep) (src : list Z),
    cps_asan pc r sp STRX_SCRA LB FF LK cr A 0
      (fun R M => a0 R o /\ a1 R q /\ a2 R (len src) /\ sink_atA M o rep /\ PMES.rep_live rep LB /\ fobj M FF o 24 /\ stksh M sp STRX_SCRA /\
                  L5.bytes_at (hl_segs L) M q src /\ src_okA M LB FF sp o rep q (len src) /\
                  screditA cr rep kx bx /\ len (PML.srep_chars rep) + len src <= CL)
      (fun R M R' M' LB' cr' LBk W => exists rep' s', len s' = len (PML.srep_chars rep) + len src /\ x_grownA LB FF M' o rep s' LB' LBk rep' /\
                                      screditA cr' rep' kx bx /\ W = [(o, 24)]).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition stransA (pc scr d : Z) (Args : list (Z * Z) -> list fframe -> Z -> bvmap 5 word -> mem -> Z -> Prop) (Ret : bvmap 5 word -> Z -> Prop)
           (PayP : Z -> Prop) (paymax : Z) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r SK S2 kx bx : Z) (rep : srep),
    cps_asan pc r sp scr (LBo ++ PML.srep_blocks rep) FF LK cr A d
      (fun R M => Args LBo FF sp R M SK /\ u64 M SK S2 /\ L5.defined M SK 8 /\ acobj FF sp SK 8 /\ SK mod 8 = 0 /\ shadow_zero M SK 1 /\ apart SK 8 S2 24 /\
                  stksh M sp scr /\ sink_atA M S2 rep /\ fobj M FF S2 24 /\ img_ro M /\ screditA cr rep kx bx /\ len (PML.srep_chars rep) + paymax <= CL)
      (fun R M R' M' LB' cr' LBk W => exists (rep' : srep) (pay : Z),
          PayP pay /\ Ret R' pay /\ sink_atA M' S2 rep' /\ len (PML.srep_chars rep') = len (PML.srep_chars rep) + pay /\
          LB' = LBo ++ PML.srep_blocks rep' /\ LBk = LBo /\ W = [(S2, 24)] /\ screditA cr' rep' kx bx).
(* [comment removed for export] *)
Definition stransA_w (pc scr d : Z) (Wx : list L5.range) (Args : list (Z * Z) -> list fframe -> Z -> bvmap 5 word -> mem -> Z -> Prop) (Ret : bvmap 5 word -> Z -> Prop)
           (PayP : Z -> Prop) (paymax : Z) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r SK S2 kx bx : Z) (rep : srep),
    cps_asan pc r sp scr (LBo ++ PML.srep_blocks rep) FF LK cr A d
      (fun R M => Args LBo FF sp R M SK /\ u64 M SK S2 /\ L5.defined M SK 8 /\ acobj FF sp SK 8 /\ SK mod 8 = 0 /\ shadow_zero M SK 1 /\ apart SK 8 S2 24 /\
                  stksh M sp scr /\ sink_atA M S2 rep /\ fobj M FF S2 24 /\ img_ro M /\ screditA cr rep kx bx /\ len (PML.srep_chars rep) + paymax <= CL)
      (fun R M R' M' LB' cr' LBk W => exists (rep' : srep) (pay : Z),
          PayP pay /\ Ret R' pay /\ sink_atA M' S2 rep' /\ len (PML.srep_chars rep') = len (PML.srep_chars rep) + pay /\
          LB' = LBo ++ PML.srep_blocks rep' /\ LBk = LBo /\ W = (S2, 24) :: Wx /\ screditA cr' rep' kx bx).

(* [comment removed for export] *)
Definition FROMINT_SCRA : Z := 512 + STRX_SCRA.
Definition FROMINT_DA : Z := 2.
Definition from_integer_x_specA (pc : Z) : Prop :=
  forall (v : Z),
    stransA pc FROMINT_SCRA FROMINT_DA (fun _ _ sp R M SK => a0 R v /\ 0 <= v < 2 ^ 64 /\ a1 R SK /\ sp mod 32 = 16) (fun R' pay => a0 R' pay) (fun pay => 1 <= pay <= 20) 20.

(* [comment removed for export] *)
Definition ESC_SCRA : Z := 160 + STRX_SCRA.
Definition escape_string_specA (pc : Z) : Prop :=
  forall (q : Z) (bs : list Z),
    stransA pc ESC_SCRA 0
      (fun LBo _ _ R M SK => a0 R q /\ a1 R (len bs) /\ a2 R 0 /\ a3 R 0 /\ a4 R SK /\
                            L5.bytes_at (hl_segs L) M q bs /\ L5.defined M q (len bs) /\ text_inA M LBo q (len bs))
      (fun R' pay => a0 R' pay) (fun pay => pay = PMES.esc_len bs) (PMES.esc_len bs).

(* [comment removed for export] *)
Definition to_codepoint_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (it e cpc c sp r : Z),
    cps_asan pc r sp 16 LB FF LK cr A 0
      (fun R M => img_ro M /\ a0 R it /\ a1 R e /\ a2 R cpc /\ a3 R 0 /\ u8 M it c /\ 0 <= c <= 127 /\ it + 1 <= e < 2 ^ 47 /\
                  text_inA M LB it 1 /\ L5.defined M (cpc - cpc mod 8) 8 /\ acobj FF sp (cpc - cpc mod 8) 8 /\ cpc mod 8 <= 4 /\ shadow_zero M cpc 1)
      (fun R M R' M' LB' cr' LBk W => a0 R' (it + 1) /\ a1 R' 0 /\ u32 M' cpc c /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(cpc - cpc mod 8, 8)]).

(* [comment removed for export] *)
Definition WD_DA : Z := 6.
Definition wd_at (M : mem) (wd : Z) : Prop := u8 M wd 0 /\ u32 M (wd + 4) 0 /\ exists dp, u8 M (wd + 8) dp.
Definition write_double_x_specA (pc : Z) : Prop :=
  forall (wd : Z),
    stransA_w pc WD_SCRA WD_DA [(hl_tp L - 164, 4)]
      (fun _ FF sp R M SK => a0 R wd /\ a1 R SK /\ wd_at M wd /\ L5.defined M wd 12 /\ CL5A.ainfr FF wd 12 /\ wd mod 8 = 4 /\ shadow_zero M (wd - 4) 2 /\ sp mod 32 = 0)
      (fun R' _ => a0 R' 0) (fun pay => 1 <= pay <= 28) 28.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lit_done (M : mem) (S G txt n : Z) : Prop := u8 M G 1 /\ u8 M (G + 1) 1 /\ u64 M S txt /\ u64 M (S + 8) n.
Definition LIT_SCRA : Z := 16 + 64.
Definition literal_specA (pc S G txt n : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r : Z),
    cps_asan pc r sp LIT_SCRA LB FF LK cr A 0
      (fun R M => PMLA.lit_ok (hl_segs L) M S G txt n /\ L5.writable (hl_segs L) M S 18 /\ img_ro M /\ PMSA.cstatic L S 18 /\ 0 <= G < 2 ^ 62)
      (fun R M R' M' LB' cr' LBk W => a0 R' txt /\ a1 R' n /\ lit_done M' S G txt n /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(S, 18)]).
Definition null_literal_specA (pc : Z) : Prop := literal_specA pc (PMLA.LIT_NULL_S IC) (PMLA.LIT_NULL_G IC) (PMLA.LIT_NULL_TXT IC) 4.
Definition true_literal_specA (pc : Z) : Prop := literal_specA pc (PMLA.LIT_TRUE_S IC) (PMLA.LIT_TRUE_G IC) (PMLA.LIT_TRUE_TXT IC) 4.
Definition false_literal_specA (pc : Z) : Prop := literal_specA pc (PMLA.LIT_FALSE_S IC) (PMLA.LIT_FALSE_G IC) (PMLA.LIT_FALSE_TXT IC) 5.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition VIS_SCRA : Z := 1024 + Z.max STRX_SCRA WD_SCRA.
Definition VIS_D : Z := 8.
Definition vtransA (pc : Z) (ev : PMES.eev) (Args : list (Z * Z) -> list fframe -> Z -> Z -> Z -> bvmap 5 word -> PMSA.mem -> Prop) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r V S2 kx bx : Z) (g : PMES.eghost),
    cps_asan pc r sp VIS_SCRA (LBo ++ PMES.g_lbv g) FF LK cr A VIS_D
      (fun R M => PMSA.a0 R V /\ Args LBo FF sp V S2 R M /\ sp mod 32 = 0 /\ PMSA.stksh ar M sp VIS_SCRA /\ enc_invA M V S2 g /\ PMES.ev_guard (PMES.g_es g) ev /\ eroomA g ev /\
                  PMLA.img_ro IC M /\ lits_ok M /\ ecreditA cr g kx bx /\ PMSA.fobj M FF V PMES.ENC_SIZE /\ PMSA.fobj M FF S2 24 /\ PMLA.apart V PMES.ENC_SIZE S2 24)
      (fun R M R' M' LB' cr' LBk W => exists (g' : PMES.eghost) (pay : Z),
          PMSA.a0 R' 1 /\ enc_invA M' V S2 g' /\ PMES.g_es g' = PMES.estep (PMES.g_es g) ev /\ PMES.pay_ok ev pay /\
          PMES.g_len g' = PMES.g_len g + PMES.ev_ind (PMES.g_es g) ev + pay /\
          lits_ok M' /\ LB' = LBo ++ PMES.g_lbv g' /\ LBk = LBo /\ W = W_encA V S2 /\ ecreditA cr' g' kx bx).
(* [comment removed for export] *)
Definition sv_argA (LBo : list (Z * Z)) (FF : list fframe) (sp V S2 : Z) (M : mem) (sv : Z) (bs : list Z) : Prop :=
  exists q, u64 M sv q /\ u64 M (sv + 8) (PMES.len bs) /\ L5.bytes_at (hl_segs L) M q bs /\ L5.defined M q (PMES.len bs) /\ text_inA M LBo q (PMES.len bs) /\
            PMLA.apart sv 16 V PMES.ENC_SIZE /\ PMLA.apart sv 16 S2 24 /\ fobj M FF sv 16.
Definition argT : list (Z * Z) -> list fframe -> Z -> Z -> Z -> bvmap 5 word -> PMSA.mem -> Prop := fun _ _ _ _ _ _ _ => True.
Definition visit_begin_object_specA (pc : Z) : Prop := vtransA pc (PMES.EvBegin false) argT.
Definition visit_begin_array_specA (pc : Z) : Prop := vtransA pc (PMES.EvBegin true) argT.
Definition visit_end_object_specA (pc : Z) : Prop := vtransA pc PMES.EvEnd argT.
Definition visit_end_array_specA (pc : Z) : Prop := vtransA pc PMES.EvEnd argT.
Definition visit_null_specA (pc : Z) : Prop := vtransA pc PMES.EvNull argT.
Definition visit_bool_specA (pc : Z) : Prop := forall (b : bool), vtransA pc (PMES.EvBool b) (fun _ _ _ _ _ R _ => a1 R (PML.b2z b)).
Definition visit_uint64_specA (pc : Z) : Prop := forall (v : Z), vtransA pc PMES.EvU64 (fun _ _ _ _ _ R _ => a1 R v /\ 0 <= v < 2 ^ 64).
Definition visit_int64_specA (pc : Z) : Prop := forall (v : Z), vtransA pc PMES.EvI64 (fun _ _ _ _ _ R _ => a1 R v /\ 0 <= v < 2 ^ 64).
(* [comment removed for export] *)
Definition vtranseA (pc : Z) (ev : PMES.eev) (Args : list (Z * Z) -> list fframe -> Z -> Z -> Z -> bvmap 5 word -> PMSA.mem -> Prop) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r V S2 kx bx : Z) (g : PMES.eghost),
    cps_asan pc r sp VIS_SCRA (LBo ++ PMES.g_lbv g) FF LK cr A VIS_D
      (fun R M => PMSA.a0 R V /\ Args LBo FF sp V S2 R M /\ sp mod 32 = 0 /\ PMSA.stksh ar M sp VIS_SCRA /\ enc_invA M V S2 g /\ PMES.ev_guard (PMES.g_es g) ev /\ eroomA g ev /\
                  PMLA.img_ro IC M /\ lits_ok M /\ ecreditA cr g kx bx /\ PMSA.fobj M FF V PMES.ENC_SIZE /\ PMSA.fobj M FF S2 24 /\ PMLA.apart V PMES.ENC_SIZE S2 24)
      (fun R M R' M' LB' cr' LBk W => exists (g' : PMES.eghost) (pay : Z),
          PMSA.a0 R' 1 /\ enc_invA M' V S2 g' /\ PMES.g_es g' = PMES.estep (PMES.g_es g) ev /\ PMES.pay_ok ev pay /\
          PMES.g_len g' = PMES.g_len g + PMES.ev_ind (PMES.g_es g) ev + pay /\
          lits_ok M' /\ LB' = LBo ++ PMES.g_lbv g' /\ LBk = LBo /\ W = W_encA V S2 ++ [(hl_tp L - 164, 4)] /\ ecreditA cr' g' kx bx).
Definition visit_double_specA (pc : Z) : Prop := vtranseA pc PMES.EvDbl argT.      (* [comment removed for export] *)
Definition visit_key_specA (pc : Z) : Prop := forall (bs : list Z) (sv : Z), vtransA pc (PMES.EvKey bs) (fun LBo FF sp V S2 R M => a1 R sv /\ sv_argA LBo FF sp V S2 M sv bs).
Definition visit_string_specA (pc : Z) : Prop := forall (tag : Z) (bs : list Z) (sv : Z), 0 <= tag < 256 ->
  vtransA pc (PMES.EvStr tag bs) (fun LBo FF sp V S2 R M => a1 R sv /\ a2 R tag /\ sv_argA LBo FF sp V S2 M sv bs).

(* [comment removed for export] *)
Definition W_h (V S2 : Z) : list L5.range := [(V + O_COLUMN, 8); (S2, 24)].
Definition htransA (pc scr d : Z) (Args : list (Z * Z) -> list fframe -> Z -> bvmap 5 word -> mem -> Z -> Z -> Prop) (Guard : estate -> Prop)
           (Dmax : estate -> Z) (Delta : estate -> Z -> Prop) (Upd : estate -> estate) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r V S2 kx bx : Z) (g : eghost),
    cps_asan pc r sp scr (LBo ++ PMES.g_lbv g) FF LK cr A d
      (fun R M => a0 R V /\ Args LBo FF sp R M V S2 /\ stksh M sp scr /\ enc_invA M V S2 g /\ Guard (PMES.g_es g) /\ PMES.g_len g + Dmax (PMES.g_es g) <= CL /\
                  img_ro M /\ ecreditA cr g kx bx /\ objs_encA M FF V S2)
      (fun R M R' M' LB' cr' LBk W => exists (g' : eghost) (dl : Z),
          enc_invA M' V S2 g' /\ PMES.g_es g' = Upd (PMES.g_es g) /\ PMES.g_sb g' = PMES.g_sb g /\ PMES.g_scap g' = PMES.g_scap g /\ Delta (PMES.g_es g) dl /\
          PMES.g_len g' = PMES.g_len g + dl /\ LB' = LBo ++ PMES.g_lbv g' /\ LBk = LBo /\ W = W_h V S2 /\ ecreditA cr' g' kx bx).
(* [comment removed for export] *)
Definition NEWLINE_SCRA : Z := 192 + STRX_SCRA.
Definition NEWLINE_DA : Z := 2.
Definition argH : list (Z * Z) -> list fframe -> Z -> bvmap 5 word -> mem -> Z -> Z -> Prop := fun _ _ _ _ _ _ _ => True.
Definition new_line_specA (pc : Z) : Prop :=
  htransA pc NEWLINE_SCRA NEWLINE_DA argH (fun _ => True) PMES.nl (fun es dl => dl = PMES.nl es) (fun es => es).
(* [comment removed for export] *)
Definition nl_reads (M : mem) (V S2 dI : Z) : Prop :=
  u64 M (V + O_SINK) S2 /\ u64 M (V + O_NL_CHARS) 0xa02 /\ u64 M (V + O_NL_CHARS + 8) 0 /\ u64 M (V + O_NL_CHARS + 16) 0 /\ L5.defined M (V + O_NL_CHARS) 24 /\
  u8 M (V + O_INDENT_CHAR) 32 /\ u32 M (V + O_INDENT) (4 * dI) /\ 0 <= dI <= MAX_DEPTH /\ L5.defined M (V + O_COLUMN) 8.
Definition new_line2_specA (pc : Z) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r V S2 kx bx dI : Z) (rep : srep),
    cps_asan pc r sp NEWLINE_SCRA (LBo ++ PML.srep_blocks rep) FF LK cr A NEWLINE_DA
      (fun R M => a0 R V /\ nl_reads M V S2 dI /\ stksh M sp NEWLINE_SCRA /\ sink_atA M S2 rep /\ img_ro M /\ screditA cr rep kx bx /\
                  len (PML.srep_chars rep) + (1 + 4 * dI) <= CL /\ objs_encA M FF V S2)
      (fun R M R' M' LB' cr' LBk W => exists (rep' : srep),
          sink_atA M' S2 rep' /\ len (PML.srep_chars rep') = len (PML.srep_chars rep) + (1 + 4 * dI) /\ L5.defined M' (V + O_COLUMN) 8 /\
          LB' = LBo ++ PML.srep_blocks rep' /\ LBk = LBo /\ W = W_h V S2 /\ screditA cr' rep' kx bx).
(* [comment removed for export] *)
Definition BSCALAR_SCRA : Z := 64 + NEWLINE_SCRA.
Definition bs_delta (es : estate) : Z := match es with [] => 0 | c :: _ => PMES.comma c + PMES.nl es end.
Definition begin_scalar_specA (pc : Z) : Prop :=
  htransA pc BSCALAR_SCRA NEWLINE_DA argH (fun _ => True) bs_delta (fun es dl => dl = bs_delta es)
          (fun es => match es with [] => [] | c :: r => PMES.set_nla c :: r end).
(* [comment removed for export] *)
Definition WSTRING_SCRA : Z := 64 + ESC_SCRA.
Definition WSTRING_DA : Z := 2.          (* [comment removed for export] *)
Definition write_string_specA (pc : Z) : Prop :=
  forall (tag sv : Z) (bs : list Z), 0 <= tag < 256 ->
    htransA pc WSTRING_SCRA WSTRING_DA (fun LBo FF sp R M V S2 => a1 R sv /\ a2 R tag /\ sv_argA LBo FF sp V S2 M sv bs /\ sp mod 32 = 0) (fun _ => True)
            (fun _ => PMES.quotes (PMES.EvStr tag bs) + pay_hi (PMES.EvStr tag bs))
            (fun _ dl => exists pay, PMES.pay_ok (PMES.EvStr tag bs) pay /\ dl = PMES.quotes (PMES.EvStr tag bs) + pay) (fun es => es).
Definition WBIGNUM_SCRA : Z := 160 + STRX_SCRA.
Definition WBIGNUM_DA : Z := 2.
Definition write_bignum_specA (pc : Z) : Prop :=
  forall (sv : Z) (bs : list Z),
    htransA pc WBIGNUM_SCRA WBIGNUM_DA (fun LBo FF sp R M V S2 => a1 R sv /\ sv_argA LBo FF sp V S2 M sv bs /\ sp mod 32 = 0) (fun _ => True)
            (fun _ => len bs) (fun _ dl => dl = len bs) (fun es => es).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ENC_CTOR_SCRA : Z := 512 + STRX_SCRA.
Definition ENC_CTOR_DA : Z := 2.
Definition enc_ctor_specA (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r V S2 SKT : Z),
    cps_asan pc r sp ENC_CTOR_SCRA LB FF LK cr A ENC_CTOR_DA
      (fun R M => a0 R V /\ a1 R SKT /\ sp mod 32 = 0 /\ stksh M sp ENC_CTOR_SCRA /\ u64 M SKT S2 /\ L5.defined M SKT 8 /\ fobj M FF SKT 8 /\
                  sink_atA M S2 (PML.SShort []) /\ L5.defined M V ENC_SIZE /\ objs_encA M FF V S2 /\ apart SKT 8 V ENC_SIZE /\ apart SKT 8 S2 24 /\ img_ro M /\
                  PMLA.libc_quiet (hl_segs L) IC M)
      (fun R M R' M' LB' cr' LBk W => enc_invA M' V S2 PMES.g0 /\ opts_idle M' V /\ u64 M' SKT 0 /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(V, ENC_SIZE); (SKT, 8)]).
Definition ENC_DTOR_SCRA : Z := 96 + PMSA.ANEW_SCR.
Definition enc_dtor_specA (pc : Z) : Prop :=
  forall (LBo : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r V S2 : Z) (g : eghost),
    cps_asan pc r sp ENC_DTOR_SCRA (LBo ++ PMES.g_lbv g) FF LK cr A 0
      (fun R M => a0 R V /\ stksh M sp ENC_DTOR_SCRA /\ enc_invA M V S2 g /\ opts_idle M V /\ objs_encA M FF V S2 /\ img_ro M)
      (fun R M R' M' LB' cr' LBk W => sink_atA M' S2 (PMES.g_rep g) /\ LB' = LBo ++ PML.srep_blocks (PMES.g_rep g) /\ cr' = cr /\ LBk = LBo ++ PML.srep_blocks (PMES.g_rep g) /\
                                      W = [(V, ENC_SIZE)]).

End SpecsA.
End PMESA.
