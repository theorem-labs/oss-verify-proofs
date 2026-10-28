(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Heap Require Import HeapIfaceU.
Import ListNotations.
Import PML.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMES.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PC_NEW_LINE : Z := 0x3e81c.        Definition PC_BEGIN_SCALAR : Z := 0x3e9ec.    Definition PC_WRITE_STRING : Z := 0x3ee84.
Definition PC_WRITE_BIGNUM : Z := 0x3f684.    Definition PC_ESCAPE_STRING : Z := 0x3faf4.   Definition PC_TO_CODEPOINT : Z := 0x434ec.
Definition PC_FROM_INT_U64 : Z := 0x3eaf0.    Definition PC_FROM_INT_I64 : Z := 0x3ec48.    Definition PC_WRITE_DOUBLE : Z := 0x3f2ec.
Definition PC_NULL_LIT : Z := 0x3f028.        Definition PC_TRUE_LIT : Z := 0x460c4.        Definition PC_FALSE_LIT : Z := 0x46138.
Definition PC_VISIT_END_ARRAY : Z := 0x3bab8. Definition PC_VISIT_UINT64 : Z := 0x3bc48.    Definition PC_VISIT_INT64 : Z := 0x3bd34.
Definition PC_VISIT_DOUBLE : Z := 0x3be20.    Definition PC_VISIT_FLUSH : Z := 0x3c3ec.     Definition PC_VISIT_BEGIN_OBJECT : Z := 0x3c3f0.
Definition PC_VISIT_END_OBJECT : Z := 0x3c6d0. Definition PC_VISIT_BEGIN_ARRAY : Z := 0x3c860. Definition PC_VISIT_KEY : Z := 0x3cc0c.
Definition PC_VISIT_NULL : Z := 0x3ce38.      Definition PC_VISIT_BOOL : Z := 0x3cf40.      Definition PC_VISIT_STRING : Z := 0x3d080.
Definition PC_ENC_CTOR : Z := 0x3a9c0.        Definition PC_ENC_CTOR_MAIN : Z := 0x3b570.   Definition PC_ENC_DTOR : Z := 0x3abc4.
Definition PC_ENC_ALLOCATE : Z := 0x45d68.    Definition PC_SPLIT_DTOR : Z := 0x42f58.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ENC_SIZE : Z := 408.
Definition O_SINK : Z := 8.          Definition O_OPT_VPTR : Z := 16.    Definition O_FLAGS : Z := 24.        Definition O_BIGNUM_FMT : Z := 27.
Definition O_SPLITS : Z := 28.       Definition O_INDENT_SIZE : Z := 36. Definition O_LINE_LIMIT : Z := 40.   Definition O_NL_CHARS : Z := 48.
Definition O_COMMON_VPTR : Z := 80.  Definition O_ENABLE : Z := 88.      Definition O_MAX_DEPTH : Z := 240.   Definition O_INDENT_CHAR : Z := 248.
Definition O_FP : Z := 252.          Definition O_STACK : Z := 264.      Definition O_INDENT : Z := 288.      Definition O_COLUMN : Z := 296.
Definition O_COLON : Z := 304.       Definition O_COMMA : Z := 320.      Definition O_OBRACE : Z := 336.      Definition O_CBRACE : Z := 352.
Definition O_OBRACKET : Z := 368.    Definition O_CBRACKET : Z := 384.   Definition O_DEPTH : Z := 400.
Definition VT_ENC_OPTIONS : Z := 0xc4220.     Definition VT_ENC_COMMON : Z := 0xc4248.
Definition TXT_COLON : Z := 0x146d3.          Definition TXT_COMMA : Z := 0x146db.          Definition TXT_OBRACE : Z := 0x146e7.
Definition TXT_CBRACE : Z := 0x146e8.         Definition TXT_OBRACKET : Z := 0x146ed.       Definition TXT_CBRACKET : Z := 0x146ee.
Definition MAX_DEPTH : Z := 1024.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record ectx : Type := ECtx { ec_arr : bool; ec_count : Z; ec_nla : bool }.
(* [comment removed for export] *)
Definition estate : Type := list ectx.
Definition depth (es : estate) : Z := Z.of_nat (length es).
(* [comment removed for export] *)
Inductive eev : Type :=
  | EvBegin (arr : bool) | EvEnd | EvKey (bs : list Z) | EvStr (tag : Z) (bs : list Z) | EvNull | EvBool (b : bool) | EvU64 | EvI64 | EvDbl.

Definition len (bs : list Z) : Z := Z.of_nat (length bs).
(* [comment removed for export] *)
Definition nl (es : estate) : Z := 1 + 4 * depth es.
(* [comment removed for export] *)
Definition comma (c : ectx) : Z := if 0 <? ec_count c then 2 else 0.
Definition set_nla (c : ectx) : ectx := ECtx (ec_arr c) (ec_count c) true.
(* [comment removed for export] *)
Definition bump (es : estate) : estate := match es with [] => [] | c :: r => ECtx (ec_arr c) ((ec_count c + 1) mod 2 ^ 64) (ec_nla c) :: r end.
(* [comment removed for export] *)
Definition pre_scalar (es : estate) : Z * estate :=
  match es with
  | [] => (0, [])
  | c :: r => if ec_arr c then (comma c + nl es, set_nla c :: r) else (0, es)
  end.
(* [comment removed for export] *)
Definition quotes (ev : eev) : Z := match ev with EvStr tag _ => if (tag =? 2) || (tag =? 3) then 0 else 2 | _ => 0 end.

(* [comment removed for export] *)
Definition ev_ind (es : estate) (ev : eev) : Z :=
  match ev with
  | EvBegin _ => match es with [] => 1 | c :: _ => if ec_arr c then comma c + nl es + 1 else 1 end
  | EvEnd => match es with [] => 0 | c :: r => (if ec_nla c then 1 + 4 * depth r else 0) + 1 end
  | EvKey _ => match es with [] => 0 | c :: _ => comma c + nl es + 4 end
  | _ => fst (pre_scalar es) + quotes ev
  end.
Definition estep (es : estate) (ev : eev) : estate :=
  match ev with
  | EvBegin a => ECtx a 0 false :: match es with [] => [] | c :: r => if ec_arr c then set_nla c :: r else es end
  | EvEnd => match es with [] => [] | _ :: r => bump r end
  | EvKey _ => match es with [] => [] | c :: r => set_nla c :: r end
  | _ => bump (snd (pre_scalar es))
  end.
(* [comment removed for export] *)
Definition ev_guard (es : estate) (ev : eev) : Prop :=
  match ev with EvBegin _ => depth es < MAX_DEPTH | EvEnd => es <> [] | EvKey _ => es <> [] | _ => True end.

(* [comment removed for export] *)
Definition esc_cls (c0 : Z) : Z :=
  let c := c0 mod 256 in if existsb (Z.eqb c) [8; 9; 10; 12; 13; 34; 92] then 2 else if (c <? 32) || (c =? 127) then 6 else 1.
Definition esc_len (bs : list Z) : Z := fold_right (fun c a => esc_cls c + a) 0 bs.
(* [comment removed for export] *)
Definition pay_ok (ev : eev) (pay : Z) : Prop :=
  match ev with
  | EvBegin _ => pay = 0 | EvEnd => pay = 0
  | EvKey bs => pay = esc_len bs
  | EvStr tag bs => pay = if (tag =? 1) || (tag =? 2) || (tag =? 3) then len bs else esc_len bs
  | EvNull => pay = 4
  | EvBool b => pay = if b then 4 else 5
  | EvU64 => 1 <= pay <= 20 | EvI64 => 1 <= pay <= 20
  | EvDbl => 1 <= pay <= 28
  end.
Definition is_num (ev : eev) : bool := match ev with EvU64 | EvI64 | EvDbl => true | _ => false end.
(* [comment removed for export] *)
Definition pay_lo (ev : eev) : Z :=
  match ev with
  | EvBegin _ | EvEnd => 0 | EvKey bs => esc_len bs
  | EvStr tag bs => if (tag =? 1) || (tag =? 2) || (tag =? 3) then len bs else esc_len bs
  | EvNull => 4 | EvBool b => if b then 4 else 5 | EvU64 | EvI64 | EvDbl => 1
  end.
Lemma pay_interval : forall ev pay, pay_ok ev pay -> pay_lo ev <= pay <= pay_lo ev + (if is_num ev then 27 else 0).
Proof. intros ev pay H. destruct ev; cbn in *; lia. Qed.

Definition CLU : Z := 2 ^ 34 + 2 ^ 31 + 31.
Definition pay_hi (ev : eev) : Z :=
  match ev with
  | EvBegin _ | EvEnd => 0 | EvKey bs => esc_len bs
  | EvStr tag bs => if (tag =? 1) || (tag =? 2) || (tag =? 3) then len bs else esc_len bs
  | EvNull => 4 | EvBool b => if b then 4 else 5 | EvU64 | EvI64 => 20 | EvDbl => 28
  end.
Definition kmax (es : estate) (ev : eev) : Z := ev_ind es ev + pay_hi ev.
Lemma pay_ok_hi : forall ev pay, pay_ok ev pay -> pay <= pay_hi ev.
Proof. intros ev pay H. destruct ev; cbn in *; lia. Qed.
Definition bs_delta (es : estate) : Z := match es with [] => 0 | c :: _ => comma c + nl es end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rep_ok (rep : srep) : Prop := match rep with SShort _ => True | SLong cap _ _ => 48 <= cap end.
Definition sink_at (M : mem) (o : Z) (rep : srep) : Prop := str_at M o rep /\ L5.defined M o 24 /\ rep_ok rep.
(* [comment removed for export] *)
Definition ctx_at (M : mem) (a : Z) (c : ectx) : Prop :=
  u32 M a (b2z (ec_arr c)) /\ u8 M (a + 4) 0 /\ u8 M (a + 6) (b2z (ec_nla c)) /\ u64 M (a + 24) (ec_count c) /\ 0 <= ec_count c < 2 ^ 64 /\ L5.defined M a 32.
Definition ctx0 : ectx := ECtx false 0 false.
(* [comment removed for export] *)
Definition stack_at (M : mem) (V : Z) (es : estate) (b capb : Z) : Prop :=
  u64 M (V + O_STACK) b /\ u64 M (V + O_STACK + 8) (b + 32 * depth es) /\ u64 M (V + O_STACK + 16) (b + capb) /\
  32 * depth es <= capb /\ ((capb = 0 /\ b = 0) \/ (exists k, 0 <= k <= 10 /\ capb = 32 * 2 ^ k)) /\
  (forall i, (i < length es)%nat -> ctx_at M (b + 32 * Z.of_nat i) (nth (length es - 1 - i) es ctx0)).
(* [comment removed for export] *)
Definition sv_at (M : mem) (a txt n : Z) : Prop := u64 M a txt /\ u64 M (a + 8) n.
(* [comment removed for export] *)
Definition enc_obj (M : mem) (V S2 d : Z) : Prop :=
  u64 M V VT_VISITOR /\ u64 M (V + O_SINK) S2 /\ u64 M (V + O_OPT_VPTR) VT_ENC_OPTIONS /\
  (exists fl, u8 M (V + O_FLAGS) fl /\ Z.land fl 15 = 0) /\
  u8 M (V + O_BIGNUM_FMT) 0 /\
  u8 M (V + O_SPLITS) 0 /\ u8 M (V + O_SPLITS + 1) 0 /\ u8 M (V + O_SPLITS + 2) 0 /\ u8 M (V + O_SPLITS + 3) 0 /\ u8 M (V + O_SPLITS + 4) 0 /\
  u8 M (V + O_INDENT_SIZE) 4 /\ u64 M (V + O_LINE_LIMIT) 120 /\
  u64 M (V + O_NL_CHARS) 0xa02 /\ u64 M (V + O_NL_CHARS + 8) 0 /\ u64 M (V + O_NL_CHARS + 16) 0 /\ L5.defined M (V + O_NL_CHARS) 24 /\
  u64 M (V + O_COMMON_VPTR) VT_ENC_COMMON /\ (exists en, u8 M (V + O_ENABLE) en /\ Z.land en 63 = 0 /\ L5.defined M (V + O_ENABLE) 2) /\
  u32 M (V + O_MAX_DEPTH) MAX_DEPTH /\ u8 M (V + O_INDENT_CHAR) 32 /\
  u8 M (V + O_FP) 0 /\ u32 M (V + O_FP + 4) 0 /\ (exists dp, u8 M (V + O_FP + 8) dp) /\
  u32 M (V + O_INDENT) (4 * d) /\ L5.defined M (V + O_COLUMN) 8 /\ u32 M (V + O_DEPTH) d /\
  sv_at M (V + O_COLON) TXT_COLON 2 /\ sv_at M (V + O_COMMA) TXT_COMMA 2 /\ sv_at M (V + O_OBRACE) TXT_OBRACE 1 /\ sv_at M (V + O_CBRACE) TXT_CBRACE 1 /\
  sv_at M (V + O_OBRACKET) TXT_OBRACKET 1 /\ sv_at M (V + O_CBRACKET) TXT_CBRACKET 1.

(* [comment removed for export] *)
Definition opts_idle (M : mem) (V : Z) : Prop :=
  u64 M (V + 96) 0 /\ u64 M (V + 120) 0 /\ u64 M (V + 144) 0 /\ u64 M (V + 168) 0 /\ u64 M (V + 192) 0 /\ u64 M (V + 216) 0.

(* [comment removed for export] *)
Record eghost : Type := EG { g_es : estate; g_len : Z; g_rep : srep; g_sb : Z; g_scap : Z }.
Definition stack_blocks (b capb : Z) : list (Z * Z) := if capb =? 0 then [] else [(b, capb)].
(* [comment removed for export] *)
Definition g_lbv (g : eghost) : list (Z * Z) := srep_blocks (g_rep g) ++ stack_blocks (g_sb g) (g_scap g).
Definition enc_inv (M : mem) (V S2 : Z) (g : eghost) : Prop :=
  enc_obj M V S2 (depth (g_es g)) /\ stack_at M V (g_es g) (g_sb g) (g_scap g) /\ sink_at M S2 (g_rep g) /\
  len (srep_chars (g_rep g)) = g_len g /\ depth (g_es g) <= MAX_DEPTH.
(* [comment removed for export] *)
Definition g0 : eghost := EG [] 0 (SShort []) 0 0.
(* [comment removed for export] *)
Definition W_enc (V S2 : Z) : list L5.range := [(V + O_STACK, 40); (V + O_DEPTH, 4); (S2, 24); (LIT_LO, LIT_HI - LIT_LO)].

Section Specs.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable WD_SCR : Z.               (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kv_s2 (rep : srep) : Z := match rep with SShort _ => 43 | SLong cap _ _ => 1 + Z.log2 (2 ^ 47 / cap) end.
Definition kv_st (capb : Z) : Z := if capb =? 0 then 11 else Z.log2 (32768 / capb).
Definition debit_k (cr : credit) : credit := (fst cr - hl_k_per_malloc L, snd cr).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition OPNEWX_SCR : Z := PMS.OPNEW_SCR.
Definition opnew_x_spec : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (n sp r : Z),
    cps_heap L HI PC_OPNEW r sp OPNEWX_SCR LB cr
      (fun R M => entry L R M sp r OPNEWX_SCR /\ a0 R n /\ 0 < n < 2 ^ 48 /\ hl_k_per_malloc L <= fst cr)
      (fun R M R' M' LB' cr' LBk W => exists A, a0 R' A /\ L5C.fresh_block L LB M' A n /\ LB' = (A, n) :: LB /\ cr' = debit_k cr /\ LBk = LB /\ W = []).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STRX_SCR : Z := PMS.STR_SCR.
(* [comment removed for export] *)
Definition alloc_of (rep : srep) : Z := match rep with SShort _ => 23 | SLong cap _ _ => cap end.
Definition fits (rep : srep) (n : Z) : Prop := match rep with SShort _ => n <= 22 | SLong cap _ _ => n < cap end.
Definition same_rep (rep : srep) (s' : list Z) : srep := match rep with SShort _ => SShort s' | SLong cap p _ => SLong cap p s' end.
Definition lb_drop (rep : srep) (LB : list (Z * Z)) : list (Z * Z) := match rep with SShort _ => LB | SLong _ p _ => lb_remove p LB end.
(* [comment removed for export] *)
Definition x_grown (LB : list (Z * Z)) (cr : credit) (M' : mem) (o : Z) (rep : srep) (s' : list Z)
           (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (rep' : srep) : Prop :=
     (fits rep (len s') /\ rep' = same_rep rep s' /\ sink_at M' o rep' /\ LB' = LB /\ cr' = cr /\ LBk = lb_drop rep LB)
  \/ (~ fits rep (len s') /\ exists p', let cap' := grow_cap (alloc_of rep) (len s') in
        rep' = SLong cap' p' s' /\ sink_at M' o rep' /\ L5C.fresh_block L LB M' p' cap' /\
        LB' = (p', cap') :: lb_drop rep LB /\ cr' = debit_k cr /\ LBk = lb_drop rep LB).
(* [comment removed for export] *)
Definition rep_live (rep : srep) (LB : list (Z * Z)) : Prop := match rep with SShort _ => True | SLong cap p _ => In (p, cap) LB end.

Definition str_push_back_x_spec : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (o c sp r : Z) (rep : srep),
    cps_heap L HI PC_STR_PUSH_BACK r sp STRX_SCR LB cr
      (fun R M => entry L R M sp r STRX_SCR /\ a0 R o /\ a1 R c /\ 0 <= c < 256 /\ sink_at M o rep /\ rep_live rep LB /\ obj_on_stack L sp o 24 /\
                  (~ fits rep (len (srep_chars rep) + 1) -> hl_k_per_malloc L <= fst cr))
      (fun R M R' M' LB' cr' LBk W => exists rep', x_grown LB cr M' o rep (srep_chars rep ++ [c]) LB' cr' LBk rep' /\ W = [(o, 24)]).

(* [comment removed for export] *)
Definition src_ok (M : mem) (LB : list (Z * Z)) (sp o : Z) (rep : srep) (q k : Z) : Prop :=
     k = 0
  \/ (0x10000 <= q /\ q + k <= IMG_RO_HI /\ img_ro M)
  \/ (sp <= q /\ q + k <= hl_sptop L /\ apart q k o 24 /\ L5.defined M q k)
  \/ (exists b, In b LB /\ ~ In b (srep_blocks rep) /\ fst b <= q /\ q + k <= fst b + snd b /\ L5.defined M q k).

Definition str_append_x_spec : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (o q sp r : Z) (rep : srep) (src : list Z),
    cps_heap L HI PC_STR_APPEND r sp STRX_SCR LB cr
      (fun R M => entry L R M sp r STRX_SCR /\ a0 R o /\ a1 R q /\ a2 R (len src) /\ sink_at M o rep /\ rep_live rep LB /\ obj_on_stack L sp o 24 /\
                  L5.bytes_at RSEGS M q src /\ src_ok M LB sp o rep q (len src) /\ len (srep_chars rep) + len src < 2 ^ 47 /\
                  (~ fits rep (len (srep_chars rep) + len src) -> hl_k_per_malloc L <= fst cr))
      (fun R M R' M' LB' cr' LBk W => exists rep' s', len s' = len (srep_chars rep) + len src /\ x_grown LB cr M' o rep s' LB' cr' LBk rep' /\ W = [(o, 24)]).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition in_blocks (LB : list (Z * Z)) (q k : Z) : Prop := k = 0 \/ exists b, In b LB /\ fst b <= q /\ q + k <= fst b + snd b.

(* [comment removed for export] *)
Definition FROMINT_SCR : Z := 320 + STRX_SCR.

(* [comment removed for export] *)
Definition ESC_SCR : Z := 144 + STRX_SCR.

(* [comment removed for export] *)
Definition to_codepoint_spec : Prop :=
  forall (it e cpc c sp r : Z),
    cps_pure PC_TO_CODEPOINT r sp 0 [(cpc, 4)]
      (fun R M => entry L R M sp r 0 /\ a0 R it /\ a1 R e /\ a2 R cpc /\ a3 R 0 /\ it < e /\ u8 M it c /\ 0 <= c < 128 /\ img_ro M /\
                  L5.defined M cpc 4 /\ sp <= cpc /\ cpc + 4 <= hl_sptop L /\ 4096 <= it /\ e < 2 ^ 47 /\ it < sp)
      (fun R M R' M' => a0 R' (it + 1) /\ getr R' 11%bv = Z_to_bv 64 0 /\ u32 M' cpc c).

(* [comment removed for export] *)
Definition WD_SCR_X : Z := 9600.
Definition wd_at (M : mem) (wd : Z) : Prop := u8 M wd 0 /\ u32 M (wd + 4) 0 /\ exists dp, u8 M (wd + 8) dp.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lit_done (M : mem) (S G txt n : Z) : Prop := u8 M G 1 /\ u8 M (G + 1) 1 /\ u64 M S txt /\ u64 M (S + 8) n.
Definition LIT_SCR : Z := 64.
Definition literal_spec (pc S G txt n : Z) : Prop :=
  forall (sp r : Z),
    cps_pure pc r sp LIT_SCR [(S, 18)]
      (fun R M => entry L R M sp r LIT_SCR /\ lit_ok M S G txt n /\ L5.writable RSEGS M S 18 /\ img_ro M)
      (fun R M R' M' => a0 R' txt /\ a1 R' n /\ lit_done M' S G txt n).
Definition null_literal_spec : Prop := literal_spec PC_NULL_LIT LIT_NULL_S LIT_NULL_G LIT_NULL_TXT 4.
Definition true_literal_spec : Prop := literal_spec PC_TRUE_LIT LIT_TRUE_S LIT_TRUE_G LIT_TRUE_TXT 4.
Definition false_literal_spec : Prop := literal_spec PC_FALSE_LIT LIT_FALSE_S LIT_FALSE_G LIT_FALSE_TXT 5.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition VIS_SCR : Z := 1024 + Z.max STRX_SCR WD_SCR.
Definition objs_enc (sp V S2 : Z) : Prop := obj_on_stack L sp V ENC_SIZE /\ obj_on_stack L sp S2 24 /\ apart V ENC_SIZE S2 24.

(* [comment removed for export] *)
Definition sv_arg (LBo : list (Z * Z)) (M : mem) (sp V S2 sv : Z) (bs : list Z) : Prop :=
  exists q, u64 M sv q /\ u64 M (sv + 8) (len bs) /\ L5.bytes_at RSEGS M q bs /\ L5.defined M q (len bs) /\ in_blocks LBo q (len bs) /\
            apart sv 16 V ENC_SIZE /\ apart sv 16 S2 24 /\ obj_on_stack L sp sv 16.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_h (V S2 : Z) : list L5.range := [(V + O_COLUMN, 8); (S2, 24)].
Definition NEWLINE_SCR : Z := 80 + STRX_SCR.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nl_reads (M : mem) (V S2 dI : Z) : Prop :=
  u64 M (V + O_SINK) S2 /\ u64 M (V + O_NL_CHARS) 0xa02 /\ u64 M (V + O_NL_CHARS + 8) 0 /\ u64 M (V + O_NL_CHARS + 16) 0 /\ L5.defined M (V + O_NL_CHARS) 24 /\
  u8 M (V + O_INDENT_CHAR) 32 /\ u32 M (V + O_INDENT) (4 * dI) /\ 0 <= dI <= MAX_DEPTH /\ L5.defined M (V + O_COLUMN) 8.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ENC_CTOR_SCR : Z := 272 + 32 + 64 + STRX_SCR.
Definition enc_ctor_spec : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (sp r V S2 SKT : Z),
    cps_heap L HI PC_ENC_CTOR r sp ENC_CTOR_SCR LB cr
      (fun R M => entry L R M sp r ENC_CTOR_SCR /\ a0 R V /\ a1 R SKT /\ u64 M SKT S2 /\ L5.defined M SKT 8 /\ sink_at M S2 (SShort []) /\ L5.defined M V ENC_SIZE /\
                  objs_enc sp V S2 /\ obj_on_stack L sp SKT 8 /\ apart SKT 8 V ENC_SIZE /\ apart SKT 8 S2 24 /\ img_ro M /\ libc_quiet M)
      (fun R M R' M' LB' cr' LBk W => enc_inv M' V S2 g0 /\ opts_idle M' V /\ u64 M' SKT 0 /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [(V, ENC_SIZE); (SKT, 8)]).
(* [comment removed for export] *)
Definition ENC_DTOR_SCR : Z := 64 + PMS.OPDEL_SCR.
Definition enc_dtor_spec : Prop :=
  forall (LBo : list (Z * Z)) (cr : credit) (sp r V S2 : Z) (g : eghost),
    cps_heap L HI PC_ENC_DTOR r sp ENC_DTOR_SCR (LBo ++ g_lbv g) cr
      (fun R M => entry L R M sp r ENC_DTOR_SCR /\ a0 R V /\ enc_inv M V S2 g /\ opts_idle M V /\ L5.defined M V ENC_SIZE /\ objs_enc sp V S2 /\ img_ro M)
      (fun R M R' M' LB' cr' LBk W => sink_at M' S2 (g_rep g) /\ LB' = LBo ++ srep_blocks (g_rep g) /\ cr' = cr /\ LBk = LBo ++ srep_blocks (g_rep g) /\
                                      W = [(V, ENC_SIZE)]).

Definition kenc (g : eghost) : Z := (kv_s2 (g_rep g) + kv_st (g_scap g)) * hl_k_per_malloc L.
Definition bpot_s2 (rep : srep) : Z := Z.max 0 (4 * CLU + 16 - 2 * alloc_of rep) + hl_b_overhead L * kv_s2 rep.
Definition bpot_st (capb : Z) : Z := Z.max 0 (65536 - 2 * capb) + hl_b_overhead L * kv_st capb.
Definition benc (g : eghost) : Z := bpot_s2 (g_rep g) + bpot_st (g_scap g).
Definition screditU (cr : credit) (rep : srep) (kx bx : Z) : Prop :=
  0 <= kx /\ kv_s2 rep * hl_k_per_malloc L <= fst cr - kx /\ 0 <= bx /\ bpot_s2 rep <= snd cr - bx.
Definition ecreditU (cr : credit) (g : eghost) (kx bx : Z) : Prop :=
  0 <= kx /\ kenc g <= fst cr - kx /\ 0 <= bx /\ benc g <= snd cr - bx.
Definition eroomU (g : eghost) (ev : eev) : Prop := g_len g + kmax (g_es g) ev <= CLU.
Definition stack_grow (capb : Z) : Z := if capb =? 0 then 32 else 2 * capb.
Definition grow_req (rep : srep) (need : Z) : Z := grow_cap (alloc_of rep) need.

Definition opnew_x_specU : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (n sp r : Z),
    cps_heap L HI PC_OPNEW r sp OPNEWX_SCR LB cr
      (fun R M => entry L R M sp r OPNEWX_SCR /\ a0 R n /\ 0 < n <= NBU /\ credit_ok L cr n)
      (fun R M R' M' LB' cr' LBk W => exists A, a0 R' A /\ L5C.fresh_block L LB M' A n /\ LB' = (A, n) :: LB /\ cr' = debit L cr n /\ LBk = LB /\ W = []).
Definition x_grownU (LB : list (Z * Z)) (cr : credit) (M' : mem) (o : Z) (rep : srep) (s' : list Z)
           (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (rep' : srep) : Prop :=
     (fits rep (len s') /\ rep' = same_rep rep s' /\ sink_at M' o rep' /\ LB' = LB /\ cr' = cr /\ LBk = lb_drop rep LB)
  \/ (~ fits rep (len s') /\ exists p', let cap' := grow_cap (alloc_of rep) (len s') in
        rep' = SLong cap' p' s' /\ sink_at M' o rep' /\ L5C.fresh_block L LB M' p' cap' /\
        LB' = (p', cap') :: lb_drop rep LB /\ cr' = debit L cr cap' /\ LBk = lb_drop rep LB).
Definition str_push_back_x_specU : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (o c sp r : Z) (rep : srep),
    cps_heap L HI PC_STR_PUSH_BACK r sp STRX_SCR LB cr
      (fun R M => entry L R M sp r STRX_SCR /\ a0 R o /\ a1 R c /\ 0 <= c < 256 /\ sink_at M o rep /\ rep_live rep LB /\ obj_on_stack L sp o 24 /\
                  (~ fits rep (len (srep_chars rep) + 1) -> credit_ok L cr (grow_req rep (len (srep_chars rep) + 1)) /\ grow_req rep (len (srep_chars rep) + 1) <= NBU))
      (fun R M R' M' LB' cr' LBk W => exists rep', x_grownU LB cr M' o rep (srep_chars rep ++ [c]) LB' cr' LBk rep' /\ W = [(o, 24)]).
Definition str_append_x_specU : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (o q sp r : Z) (rep : srep) (src : list Z),
    cps_heap L HI PC_STR_APPEND r sp STRX_SCR LB cr
      (fun R M => entry L R M sp r STRX_SCR /\ a0 R o /\ a1 R q /\ a2 R (len src) /\ sink_at M o rep /\ rep_live rep LB /\ obj_on_stack L sp o 24 /\
                  L5.bytes_at RSEGS M q src /\ src_ok M LB sp o rep q (len src) /\ len (srep_chars rep) + len src < 2 ^ 47 /\
                  (~ fits rep (len (srep_chars rep) + len src) -> credit_ok L cr (grow_req rep (len (srep_chars rep) + len src)) /\ grow_req rep (len (srep_chars rep) + len src) <= NBU))
      (fun R M R' M' LB' cr' LBk W => exists rep' s', len s' = len (srep_chars rep) + len src /\ x_grownU LB cr M' o rep s' LB' cr' LBk rep' /\ W = [(o, 24)]).

Definition stransU (pc scr : Z) (Args : list (Z * Z) -> Z -> bvmap 5 word -> mem -> Z -> Prop) (Ret : bvmap 5 word -> Z -> Prop) (PayP : Z -> Prop)
           (paymax : Z) : Prop :=
  forall (LBo : list (Z * Z)) (cr : credit) (sp r SK S2 kx bx : Z) (rep : srep),
    cps_heap L HI pc r sp scr (LBo ++ srep_blocks rep) cr
      (fun R M => entry L R M sp r scr /\ Args LBo sp R M SK /\ u64 M SK S2 /\ sp <= SK /\ SK + 8 <= hl_sptop L /\ apart SK 8 S2 24 /\
                  sink_at M S2 rep /\ obj_on_stack L sp S2 24 /\ img_ro M /\ screditU cr rep kx bx /\ len (srep_chars rep) + paymax <= CLU)
      (fun R M R' M' LB' cr' LBk W => exists (rep' : srep) (pay : Z),
          PayP pay /\ Ret R' pay /\ sink_at M' S2 rep' /\ len (srep_chars rep') = len (srep_chars rep) + pay /\
          LB' = LBo ++ srep_blocks rep' /\ LBk = LBo /\ W = [(S2, 24)] /\ screditU cr' rep' kx bx).
Definition from_integer_x_specU (pc : Z) : Prop :=
  forall (v : Z),
    stransU pc FROMINT_SCR (fun _ _ R M SK => a0 R v /\ 0 <= v < 2 ^ 64 /\ a1 R SK) (fun R' pay => a0 R' pay) (fun pay => 1 <= pay <= 20) 20.
Definition from_integer_u64_x_specU : Prop := from_integer_x_specU PC_FROM_INT_U64.
Definition from_integer_i64_x_specU : Prop := from_integer_x_specU PC_FROM_INT_I64.
Definition escape_string_specU : Prop :=
  forall (q : Z) (bs : list Z),
    stransU PC_ESCAPE_STRING ESC_SCR
      (fun LBo _ R M SK => a0 R q /\ a1 R (len bs) /\ a2 R 0 /\ a3 R 0 /\ getr R 14%bv = Z_to_bv 64 SK /\
                         L5.bytes_at RSEGS M q bs /\ L5.defined M q (len bs) /\ in_blocks LBo q (len bs) /\ 4096 <= q < 2 ^ 47)
      (fun R' pay => a0 R' pay) (fun pay => pay = esc_len bs) (esc_len bs).
Definition write_double_x_specU : Prop :=
  forall (wd : Z),
    stransU PC_WRITE_DOUBLE WD_SCR
      (fun _ sp R M SK => a0 R wd /\ a1 R SK /\ wd_at M wd /\ sp <= wd /\ wd + 9 <= hl_sptop L)
      (fun R' _ => a0 R' 0) (fun pay => 1 <= pay <= 28) 28.

Definition vtrans_genU (pc scr : Z) (ev : eev) (Args : list (Z * Z) -> bvmap 5 word -> mem -> Prop) (Ret : bvmap 5 word -> Prop) : Prop :=
  forall (LBo : list (Z * Z)) (cr : credit) (sp r V S2 kx bx : Z) (g : eghost),
    cps_heap L HI pc r sp scr (LBo ++ g_lbv g) cr
      (fun R M => entry L R M sp r scr /\ a0 R V /\ Args LBo R M /\ enc_inv M V S2 g /\ ev_guard (g_es g) ev /\ eroomU g ev /\ img_ro M /\ lits_ok M /\
                  ecreditU cr g kx bx /\ objs_enc sp V S2)
      (fun R M R' M' LB' cr' LBk W => exists (g' : eghost) (pay : Z),
          Ret R' /\ enc_inv M' V S2 g' /\ g_es g' = estep (g_es g) ev /\ pay_ok ev pay /\ g_len g' = g_len g + ev_ind (g_es g) ev + pay /\
          lits_ok M' /\ LB' = LBo ++ g_lbv g' /\ LBk = LBo /\ W = W_enc V S2 /\ ecreditU cr' g' kx bx).
Definition vtransU (pc : Z) (ev : eev) (Args : list (Z * Z) -> bvmap 5 word -> mem -> Prop) : Prop :=
  vtrans_genU pc VIS_SCR ev Args (fun R' => a0 R' 1).
Definition visit_begin_object_specU : Prop := vtransU PC_VISIT_BEGIN_OBJECT (EvBegin false) (fun _ _ _ => True).
Definition visit_begin_array_specU : Prop := vtransU PC_VISIT_BEGIN_ARRAY (EvBegin true) (fun _ _ _ => True).
Definition visit_end_object_specU : Prop := vtransU PC_VISIT_END_OBJECT EvEnd (fun _ _ _ => True).
Definition visit_end_array_specU : Prop := vtransU PC_VISIT_END_ARRAY EvEnd (fun _ _ _ => True).
Definition visit_null_specU : Prop := vtransU PC_VISIT_NULL EvNull (fun _ _ _ => True).
Definition visit_bool_specU : Prop := forall (b : bool), vtransU PC_VISIT_BOOL (EvBool b) (fun _ R _ => a1 R (b2z b)).
Definition visit_uint64_specU : Prop := forall (v : Z), vtransU PC_VISIT_UINT64 EvU64 (fun _ R _ => a1 R v /\ 0 <= v < 2 ^ 64).
Definition visit_int64_specU : Prop := forall (v : Z), vtransU PC_VISIT_INT64 EvI64 (fun _ R _ => a1 R v /\ 0 <= v < 2 ^ 64).
Definition visit_double_specU : Prop := vtransU PC_VISIT_DOUBLE EvDbl (fun _ _ _ => True).
Definition sv_argU (LBo : list (Z * Z)) (M : mem) (sp V S2 sv : Z) (bs : list Z) : Prop :=
  exists q, u64 M sv q /\ 4096 <= q < 2 ^ 47 /\ u64 M (sv + 8) (len bs) /\ L5.bytes_at RSEGS M q bs /\ L5.defined M q (len bs) /\ in_blocks LBo q (len bs) /\
            apart sv 16 V ENC_SIZE /\ apart sv 16 S2 24 /\ obj_on_stack L sp sv 16.
Lemma sv_arg_of_U : forall LBo M sp V S2 sv bs, sv_argU LBo M sp V S2 sv bs -> sv_arg LBo M sp V S2 sv bs.
Proof. intros LBo M sp V S2 sv bs (q & H1 & _ & H2). exists q. exact (conj H1 H2). Qed.
Definition vtrans_svU (pc : Z) (ev : eev) (bs : list Z) (Extra : bvmap 5 word -> Prop) : Prop :=
  forall (LBo : list (Z * Z)) (cr : credit) (sp r V S2 kx bx sv : Z) (g : eghost),
    cps_heap L HI pc r sp VIS_SCR (LBo ++ g_lbv g) cr
      (fun R M => entry L R M sp r VIS_SCR /\ a0 R V /\ a1 R sv /\ Extra R /\ sv_argU LBo M sp V S2 sv bs /\ enc_inv M V S2 g /\ ev_guard (g_es g) ev /\ eroomU g ev /\
                  img_ro M /\ lits_ok M /\ ecreditU cr g kx bx /\ objs_enc sp V S2)
      (fun R M R' M' LB' cr' LBk W => exists (g' : eghost) (pay : Z),
          a0 R' 1 /\ enc_inv M' V S2 g' /\ g_es g' = estep (g_es g) ev /\ pay_ok ev pay /\ g_len g' = g_len g + ev_ind (g_es g) ev + pay /\
          lits_ok M' /\ LB' = LBo ++ g_lbv g' /\ LBk = LBo /\ W = W_enc V S2 /\ ecreditU cr' g' kx bx).
Definition visit_key_specU : Prop := forall (bs : list Z), vtrans_svU PC_VISIT_KEY (EvKey bs) bs (fun _ => True).
Definition visit_string_specU : Prop := forall (tag : Z) (bs : list Z), 0 <= tag < 256 -> vtrans_svU PC_VISIT_STRING (EvStr tag bs) bs (fun R => a2 R tag).

Definition htransU (pc scr : Z) (Args : list (Z * Z) -> Z -> bvmap 5 word -> mem -> Z -> Z -> Prop) (Guard : estate -> Prop)
           (Dmax : estate -> Z) (Delta : estate -> Z -> Prop) (Upd : estate -> estate) : Prop :=
  forall (LBo : list (Z * Z)) (cr : credit) (sp r V S2 kx bx : Z) (g : eghost),
    cps_heap L HI pc r sp scr (LBo ++ g_lbv g) cr
      (fun R M => entry L R M sp r scr /\ a0 R V /\ Args LBo sp R M V S2 /\ enc_inv M V S2 g /\ Guard (g_es g) /\ g_len g + Dmax (g_es g) <= CLU /\
                  img_ro M /\ ecreditU cr g kx bx /\ objs_enc sp V S2)
      (fun R M R' M' LB' cr' LBk W => exists (g' : eghost) (d : Z),
          enc_inv M' V S2 g' /\ g_es g' = Upd (g_es g) /\ g_sb g' = g_sb g /\ g_scap g' = g_scap g /\ Delta (g_es g) d /\ g_len g' = g_len g + d /\
          LB' = LBo ++ g_lbv g' /\ LBk = LBo /\ W = W_h V S2 /\ ecreditU cr' g' kx bx).
Definition new_line_specU : Prop := htransU PC_NEW_LINE NEWLINE_SCR (fun _ _ _ _ _ _ => True) (fun _ => True) nl (fun es d => d = nl es) (fun es => es).
Definition new_line2_specU : Prop :=
  forall (LBo : list (Z * Z)) (cr : credit) (sp r V S2 kx bx dI : Z) (rep : srep),
    cps_heap L HI PC_NEW_LINE r sp NEWLINE_SCR (LBo ++ srep_blocks rep) cr
      (fun R M => entry L R M sp r NEWLINE_SCR /\ a0 R V /\ nl_reads M V S2 dI /\ sink_at M S2 rep /\ screditU cr rep kx bx /\
                  len (srep_chars rep) + (1 + 4 * dI) <= CLU /\ objs_enc sp V S2)
      (fun R M R' M' LB' cr' LBk W => exists (rep' : srep),
          sink_at M' S2 rep' /\ len (srep_chars rep') = len (srep_chars rep) + (1 + 4 * dI) /\ L5.defined M' (V + O_COLUMN) 8 /\
          LB' = LBo ++ srep_blocks rep' /\ LBk = LBo /\ W = W_h V S2 /\ screditU cr' rep' kx bx).
Definition begin_scalar_specU : Prop :=
  htransU PC_BEGIN_SCALAR (16 + NEWLINE_SCR) (fun _ _ _ _ _ _ => True) (fun _ => True) bs_delta
          (fun es d => d = bs_delta es)
          (fun es => match es with [] => [] | c :: r => set_nla c :: r end).
Definition write_string_specU : Prop :=
  forall (tag sv : Z) (bs : list Z), 0 <= tag < 256 ->
    htransU PC_WRITE_STRING (32 + Z.max ESC_SCR (176 + STRX_SCR)) (fun LBo sp R M V S2 => a1 R sv /\ a2 R tag /\ sv_argU LBo M sp V S2 sv bs) (fun _ => True)
            (fun _ => quotes (EvStr tag bs) + pay_hi (EvStr tag bs))
            (fun _ d => exists pay, pay_ok (EvStr tag bs) pay /\ d = quotes (EvStr tag bs) + pay) (fun es => es).
Definition write_bignum_specU : Prop :=
  forall (sv : Z) (bs : list Z),
    htransU PC_WRITE_BIGNUM (176 + STRX_SCR) (fun LBo sp R M V S2 => a1 R sv /\ sv_argU LBo M sp V S2 sv bs) (fun _ => True) (fun _ => len bs)
            (fun _ d => d = len bs) (fun es => es).

End Specs.
End PMES.
