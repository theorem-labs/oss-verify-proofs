(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA FPSteps L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibDefs.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeapA CutL5A.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMLA.
Definition mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
Record consts : Type := CONSTS {
  VT_VISITOR : Z;            (* [comment removed for export] *)
  VT_PARSER : Z;             (* [comment removed for export] *)
  VT_FUNC : Z;               (* [comment removed for export] *)
  VT_ISS : Z; VT_ISS_IOS : Z; VT_STRINGBUF : Z;
  OBJ_JSON_CATEGORY : Z; OBJ_SYSTEM_CATEGORY : Z;
  ATEXIT_HANDLER : Z;        (* [comment removed for export] *)
  ATCXA_HANDLER : Z;         (* [comment removed for export] *)
  CLASSIC_IMP : Z;           (* [comment removed for export] *)
  IMG_RO_LO : Z; IMG_RO_HI : Z;   (* [comment removed for export] *)
  GLOC_PTR : Z; GLOC_GUARD : Z;   (* [comment removed for export] *)
  SYSCAT_GUARD : Z;          (* [comment removed for export] *)
  ERRCAT_GUARD : Z;          (* [comment removed for export] *)
  ATEXIT_TAB : Z;            (* [comment removed for export] *)
  NEED_LOCKS : Z;            (* [comment removed for export] *)
  LOCALE_LOCK : Z;           (* [comment removed for export] *)
  HS0 : list (Z * Z);        (* [comment removed for export] *)
  FOOT : list (Z * Z);       (* [comment removed for export] *)
  VT_DEFVIS : Z;             (* [comment removed for export] *)
  LIT_NULL_S : Z; LIT_NULL_G : Z; LIT_NULL_TXT : Z; LIT_TRUE_S : Z; LIT_TRUE_G : Z; LIT_TRUE_TXT : Z; LIT_FALSE_S : Z; LIT_FALSE_G : Z; LIT_FALSE_TXT : Z   (* [comment removed for export] *)
}.
Definition C_xasan : consts := {|
  VT_VISITOR := 0x15ac20; VT_PARSER := 0x15aa20; VT_FUNC := 0x15b000; VT_ISS := 0x15e888; VT_ISS_IOS := 0x15e8b0; VT_STRINGBUF := 0x15e798;
  OBJ_JSON_CATEGORY := 0x165378; OBJ_SYSTEM_CATEGORY := 0x1653b0; ATEXIT_HANDLER := 0xfd4f0; ATCXA_HANDLER := 0x76048; CLASSIC_IMP := 0x69ce10;
  IMG_RO_LO := 0x10000; IMG_RO_HI := 0x162000;
  GLOC_PTR := 0x69c9f8; GLOC_GUARD := 0x69ca00; SYSCAT_GUARD := 0x69c800; ERRCAT_GUARD := 0x69c580; ATEXIT_TAB := 0x6be020; NEED_LOCKS := 0x6be263; LOCALE_LOCK := 0x6be340;
  HS0 := [(0x1419c0, 0x9fb10); (0x1419c0, 0xb04d8)];      (* [comment removed for export] *)
  FOOT := [(0x69c580, 0x69c582); (0x69c800, 0x69c802); (0x69c810, 0x69ca08); (0x69cab8, 0x69cf38); (0x69d668, 0x69d6c8); (0x6be020, 0x6be240); (0x6be263, 0x6be264); (0x6be340, 0x6be344)];
  VT_DEFVIS := 0x15b128;
  LIT_NULL_S := 0x69c588; LIT_NULL_G := 0x69c598; LIT_NULL_TXT := 0x25aa0; LIT_TRUE_S := 0x69c5a0; LIT_TRUE_G := 0x69c5b0; LIT_TRUE_TXT := 0x284a0;
  LIT_FALSE_S := 0x69c5b8; LIT_FALSE_G := 0x69c5c8; LIT_FALSE_TXT := 0x284c0
|}.
(* [comment removed for export] *)
Definition C_xboth : consts := {|
  VT_VISITOR := 0x15e640; VT_PARSER := 0x15e440; VT_FUNC := 0x15ea20; VT_ISS := 0x162188; VT_ISS_IOS := 0x1621b0; VT_STRINGBUF := 0x162098;
  OBJ_JSON_CATEGORY := 0x168c78; OBJ_SYSTEM_CATEGORY := 0x168cb0; ATEXIT_HANDLER := 0x100e68; ATCXA_HANDLER := 0x76918; CLASSIC_IMP := 0x6a06d0;
  IMG_RO_LO := 0x10000; IMG_RO_HI := 0x166000;
  GLOC_PTR := 0x6a02b8; GLOC_GUARD := 0x6a02c0; SYSCAT_GUARD := 0x6a00c0; ERRCAT_GUARD := 0x69fe40; ATEXIT_TAB := 0x6c18e0; NEED_LOCKS := 0x6c1b23; LOCALE_LOCK := 0x6c1c00;
  HS0 := [(0x145338, 0xa03e0); (0x145338, 0xb0da8)];      (* [comment removed for export] *)
  FOOT := [(0x69fe40, 0x69fe42); (0x6a00c0, 0x6a00c2); (0x6a00d0, 0x6a02c8); (0x6a0378, 0x6a07f8); (0x6a0f28, 0x6a0f88); (0x6c18e0, 0x6c1b00); (0x6c1b23, 0x6c1b24); (0x6c1c00, 0x6c1c04)];
  VT_DEFVIS := 0x15eb48;
  LIT_NULL_S := 0x69fe48; LIT_NULL_G := 0x69fe58; LIT_NULL_TXT := 0x25c40; LIT_TRUE_S := 0x69fe60; LIT_TRUE_G := 0x69fe70; LIT_TRUE_TXT := 0x28640;
  LIT_FALSE_S := 0x69fe78; LIT_FALSE_G := 0x69fe88; LIT_FALSE_TXT := 0x28660
|}.
(* [comment removed for export] *)
Definition PC_LIB : Z := 0xb0500.          Definition PC_STRINIT : Z := 0xb0f8c.        Definition PC_ISS_CTOR : Z := 0xb10e4.      Definition PC_READER_CTOR : Z := 0xb1834.
Definition PC_READ : Z := 0xb1db0.         Definition PC_PARSER_DTOR : Z := 0xb2030.    Definition PC_VEC_DTOR : Z := 0xb242c.      Definition PC_ANNOT_DELETE : Z := 0xb254c.
Definition PC_ANNOT_SHRINK : Z := 0xb25ec. Definition PC_SOURCE_DTOR : Z := 0xb2690.    Definition PC_VEC_RESERVE : Z := 0xcd184.   Definition PC_ANNOT_NEW : Z := 0xcd590.
Definition PC_VEC_PUSH : Z := 0xcd618.     Definition PC_VEC_SLOW : Z := 0xcd71c.       Definition PC_ANNOT_INCREASE : Z := 0xcd8fc. Definition PC_READ_NEXT : Z := 0xcd9a0.
Definition PC_RCHECK_DONE : Z := 0xcded4.  Definition PC_SET_EC : Z := 0xca080.         Definition PC_RESET : Z := 0xce284.         Definition PC_READ_CHUNK : Z := 0xce3e8.
Definition PC_SKIP_WS : Z := 0xce580.      Definition PC_PARSE_SOME : Z := 0xceef0.     Definition PC_END_INT : Z := 0xd606c.       Definition PC_END_FRAC : Z := 0xd611c.
Definition PC_POP_STATE : Z := 0xd6750.    Definition PC_SKIP_SPACE : Z := 0xd6ad0.     Definition PC_BEGIN_OBJECT : Z := 0xd6d8c.  Definition PC_BEGIN_ARRAY : Z := 0xd7110.
Definition PC_PARSE_STRING : Z := 0xd74c0. Definition PC_PARSE_NUMBER : Z := 0xd8d1c.   Definition PC_PARSE_NULL : Z := 0xd9cdc.    Definition PC_PARSE_TRUE : Z := 0xda1f0.
Definition PC_PARSE_FALSE : Z := 0xda6c0.  Definition PC_END_OBJECT : Z := 0xdabd8.     Definition PC_END_ARRAY : Z := 0xdb1ac.     Definition PC_BEGIN_MEMBER : Z := 0xdb778.
Definition PC_PARENT : Z := 0xdba24.       Definition PC_END_NEG : Z := 0xdbd80.        Definition PC_END_POS : Z := 0xdc338.       Definition PC_DEC_I64 : Z := 0xdc8f0.
Definition PC_DECSTR_DOUBLE : Z := 0xc9508. Definition PC_AFTER_VALUE : Z := 0xdc9cc.   Definition PC_DEC_U64 : Z := 0xdcc78.       Definition PC_END_STRING : Z := 0xdce50.
Definition PC_APPEND_CP : Z := 0xddadc.    Definition PC_CONVERT : Z := 0xddd78.        Definition PC_VALIDATE : Z := 0xddf4c.      Definition PC_TRANSLATE_ERRC : Z := 0xde2f0.
Definition PC_APPEND_RANGE : Z := 0xde87c. Definition PC_PCHECK_DONE : Z := 0xdf028.    Definition PC_GUARD_ACQ : Z := 0xdf3fc.     Definition PC_GUARD_REL : Z := 0xdf44c.
Definition PC_OPDEL : Z := 0xfbd28.        Definition PC_STR_RESERVE : Z := 0xfded4.    Definition PC_STR_APPEND : Z := 0xfe0f4.    Definition PC_STR_GROW_BY : Z := 0xfe1f0.
Definition PC_STR_PUSH_BACK : Z := 0xfe33c. Definition PC_STR_COPY : Z := 0xfe770.      Definition PC_SYSTEM_CATEGORY : Z := 0x10262c. Definition PC_IOS_CLEAR : Z := 0x103404.
Definition PC_IOSB_INIT : Z := 0x1034dc.    Definition PC_IOSB_DTOR : Z := 0x1038a8.      Definition PC_ISTREAM_DTOR : Z := 0x103b94.  Definition PC_LOCALE_CTOR : Z := 0x127fb4.
Definition PC_LOCALE_DTOR : Z := 0x12808c. Definition PC_STRTOD : Z := 0x151d04.        Definition PC_OPNEW : Z := 0x159494.
Definition PC_SET_SHADOW_00 : Z := 0x83d60. Definition PC_SET_SHADOW_F5 : Z := 0x83e68. Definition PC_SET_SHADOW_F8 : Z := 0x83e80.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Mem.
Variable segs : list Segment.
Variable IC : consts.

Definition u8 (M : mem) := L5.u8_at segs M.   Definition u32 (M : mem) := L5.u32_at segs M.   Definition u64 (M : mem) := L5.u64_at segs M.
Definition b2z (b : bool) : Z := if b then 1 else 0.
Definition img_ro (M : mem) : Prop := L5.img_clear M (IMG_RO_LO IC) (IMG_RO_HI IC).

(* [comment removed for export] *)
Definition str_at (M : mem) (o : Z) (r : PML.srep) : Prop :=
  match r with
  | PML.SShort s => L5.lstr_short segs M o s
  | PML.SLong cap p s => L5.lstr_long segs M o s (cap + 1) p /\ cap mod 8 = 0 /\ Z.of_nat (length s) < cap
  end.
Definition str_at_w (M : mem) (o : Z) (r : PML.srep) : Prop :=
  match r with
  | PML.SShort s => L5.lstr_short segs M o s
  | PML.SLong cap p s => L5.lstr_long segs M o s (cap + 1) p /\ Z.of_nat (length s) < cap
  end.

(* [comment removed for export] *)
Definition parser_at (M : mem) (P : Z) (ps : PML.pstate) : Prop :=
  u64 M P (VT_PARSER IC) /\ u32 M (P + 8) 1024 /\
  u8 M (P + 12) 0 /\ u8 M (P + 13) 1 /\ u8 M (P + 14) 0 /\ u8 M (P + 15) 1 /\ u8 M (P + 16) 0 /\ u8 M (P + 17) 0 /\ u8 M (P + 18) 0 /\
  L5.lstr_short segs M (P + 24) [] /\ L5.lstr_short segs M (P + 48) [] /\ L5.lstr_short segs M (P + 72) [] /\
  u64 M (P + 96) (VT_FUNC IC) /\ u64 M (P + 128) (P + 96) /\
  u32 M (P + 144) (PML.ps_level ps) /\
  match PML.ps_win ps with None => u64 M (P + 192) 0 /\ u64 M (P + 200) 0 | Some (p, e) => u64 M (P + 200) p /\ u64 M (P + 192) e /\ p <= e end /\
  u8 M (P + 208) (PML.ps_st ps) /\ u8 M (P + 209) (PML.ps_sst ps) /\ u8 M (P + 210) (PML.ps_nst ps) /\
  u8 M (P + 211) (b2z (PML.ps_more ps)) /\ u8 M (P + 212) (b2z (PML.ps_done ps)) /\ u8 M (P + 213) 0 /\ u32 M (P + 216) 0 /\
  str_at M (P + 224) (PML.SLong (PML.ps_bcap ps) (PML.ps_bptr ps) (PML.ps_buf ps)) /\ 264 <= PML.ps_bcap ps /\
  u64 M (P + 248) (PML.ps_sb ps) /\ u64 M (P + 256) (PML.ps_sb ps + Z.of_nat (length (PML.ps_stack ps))) /\ u64 M (P + 264) (PML.ps_sb ps + PML.ps_scap ps) /\
  L5.bytes_at segs M (PML.ps_sb ps) (PML.ps_stack ps) /\ Z.of_nat (length (PML.ps_stack ps)) <= PML.ps_scap ps /\
  L5.defined M P 272.
(* [comment removed for export] *)
Definition parser_sh (M : mem) (ps : PML.pstate) : Prop :=
  shadow_blk M (PML.ps_bptr ps) (PML.ps_bcap ps) /\ shadow_cont M (PML.ps_sb ps) (PML.ps_scap ps) (Z.of_nat (length (PML.ps_stack ps))).

Definition vis_at (M : mem) (V : Z) : Prop := u64 M V (VT_VISITOR IC).
Definition ec_at (M : mem) (E : Z) (code : Z) : Prop :=
  u32 M E code /\ L5.defined M E 16 /\ (code = 0 \/ (1 <= code <= 31 /\ u64 M (E + 8) (OBJ_JSON_CATEGORY IC))).
Definition iosb_at (M : mem) (B : Z) (rdstate rdbuf : Z) : Prop :=
  u32 M (B + 32) rdstate /\ u32 M (B + 36) 0 /\ u64 M (B + 40) rdbuf /\ u64 M (B + 48) (CLASSIC_IMP IC) /\
  (forall k, 0 <= k < 10 -> u64 M (B + 56 + 8 * k) 0) /\ L5.defined M B 152.
Definition isrc_at (M : mem) (IS : Z) (rep : PML.srep) (g : Z) (rdstate : Z) : Prop :=
  let D := PML.srep_data (IS + 80) rep in let n := Z.of_nat (length (PML.srep_chars rep)) in
  u64 M IS (VT_ISS IC) /\ u64 M (IS + 16) (VT_STRINGBUF IC) /\ u64 M (IS + 24) (CLASSIC_IMP IC) /\
  u64 M (IS + 32) D /\ u64 M (IS + 40) g /\ u64 M (IS + 48) (D + n) /\ D <= g <= D + n /\
  u64 M (IS + 56) 0 /\ u64 M (IS + 64) 0 /\ u64 M (IS + 72) 0 /\
  str_at M (IS + 80) rep /\ u64 M (IS + 104) (D + n) /\ u32 M (IS + 112) 8 /\
  u64 M (IS + 120) (VT_ISS_IOS IC) /\ iosb_at M (IS + 120) rdstate (IS + 16) /\ (rdstate = 0 \/ rdstate = 2) /\
  L5.defined M IS 272.
Definition source_at (M : mem) (R ch : Z) : Prop :=
  u64 M (R + 264) ch /\ u64 M (R + 272) 16384 /\ (exists st0, iosb_at M (R + 88) st0 (R + 24)) /\ u64 M (R + 32) (CLASSIC_IMP IC) /\ L5.defined M R 320.
Definition reader_at (M : mem) (R IS V ch : Z) (bof : bool) (ps : PML.pstate) : Prop :=
  u64 M (R + 240) IS /\ u64 M (R + 248) (IS + 16) /\ u64 M (R + 264) ch /\ u64 M (R + 272) 16384 /\
  (exists de, u64 M (R + 280) de /\ ch <= de <= ch + 16384) /\ u64 M (R + 288) 0 /\ u8 M (R + 296) (b2z bof) /\
  u64 M (R + 304) (VT_DEFVIS IC) /\ u64 M (R + 312) V /\
  (exists st0, iosb_at M (R + 88) st0 (R + 24)) /\ u64 M (R + 32) (CLASSIC_IMP IC) /\
  parser_at M (R + 320) ps /\
  match PML.ps_win ps with None => True | Some (p, e) => ch <= p /\ e <= ch + 16384 /\ L5.defined M p (e - p) end /\
  L5.defined M R 592.
(* [comment removed for export] *)
Definition srep_sh (M : mem) (r : PML.srep) : Prop := match r with PML.SShort _ => True | PML.SLong cap p _ => shadow_blk M p cap end.

(* [comment removed for export] *)
Definition win_okA (M : mem) (LBo : list (Z * Z)) (ps : PML.pstate) : Prop :=
  match PML.ps_win ps with
  | None => True
  | Some (p, e) => exists ch, In (ch, 16384) LBo /\ ch <= p /\ e <= ch + 16384 /\ L5.defined M p (e - p) /\ shadow_blk M ch 16384
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition in_foot (a : Z) : Prop := exists iv, In iv (FOOT IC) /\ fst iv <= a < snd iv.
Definition in_tab (a : Z) : Prop := ATEXIT_TAB IC <= a < ATEXIT_TAB IC + ATEXIT_TAB_BYTES.
(* [comment removed for export] *)
Definition foot_pristine (M : mem) : Prop := forall a, in_foot a -> ~ in_tab a -> a <> NEED_LOCKS IC -> M (Z_to_bv 64 a) = None.
Definition loc_done (M : mem) : Prop := u8 M (GLOC_GUARD IC) 1 /\ u64 M (GLOC_PTR IC) (CLASSIC_IMP IC) /\ u8 M (SYSCAT_GUARD IC) 1.
Definition errcat_guard (M : mem) (b : Z) : Prop := u8 M (ERRCAT_GUARD IC) b /\ u8 M (ERRCAT_GUARD IC + 1) b.
(* [comment removed for export] *)
Definition ls_atexit (g : PML.ls_state) : list (Z * Z) :=
  match g with PML.LS2 => [(ATEXIT_HANDLER IC, OBJ_JSON_CATEGORY IC); (ATCXA_HANDLER IC, 0)] | _ => [] end.
(* [comment removed for export] *)
Definition libc_quiet (M : mem) : Prop := cell_is segs M (NEED_LOCKS IC) 1 0 /\ cell_is segs M (LOCALE_LOCK IC) 4 0.
Definition atexit_ok (M : mem) (g : PML.ls_state) : Prop :=
  atexit_state_at segs (ATEXIT_TAB IC) M (HS0 IC ++ ls_atexit g) /\ libc_quiet M.
Definition ls_ok (g : PML.ls_state) (M : mem) : Prop :=
  img_ro M /\ atexit_ok M g /\
  match g with
  | PML.LS0 => foot_pristine M
  | PML.LS1 => loc_done M /\ errcat_guard M 0
  | PML.LS2 => loc_done M /\ errcat_guard M 1
  end.
(* [comment removed for export] *)
Definition LIT_LO : Z := LIT_NULL_S IC.   Definition LIT_HI : Z := LIT_FALSE_G IC + 8.
Definition FOOTX : list (Z * Z) := FOOT IC ++ [(LIT_LO, LIT_HI)].
Definition in_footx (a : Z) : Prop := exists iv, In iv FOOTX /\ fst iv <= a < snd iv.
Definition lit_ok (M : mem) (S G txt len : Z) : Prop :=
     (u8 M G 0 /\ u8 M (G + 1) 0 /\ u64 M S 0 /\ u64 M (S + 8) 0)
  \/ (u8 M G 1 /\ u8 M (G + 1) 1 /\ u64 M S txt /\ u64 M (S + 8) len).
Definition lits_ok (M : mem) : Prop :=
  lit_ok M (LIT_NULL_S IC) (LIT_NULL_G IC) (LIT_NULL_TXT IC) 4 /\ lit_ok M (LIT_TRUE_S IC) (LIT_TRUE_G IC) (LIT_TRUE_TXT IC) 4 /\ lit_ok M (LIT_FALSE_S IC) (LIT_FALSE_G IC) (LIT_FALSE_TXT IC) 5.
(* [comment removed for export] *)
Definition lits_pristine (M : mem) : Prop := forall a, LIT_LO <= a < LIT_HI -> M (Z_to_bv 64 a) = None.
(* [comment removed for export] *)
Definition ls_okx (g : PML.ls_state) (M : mem) : Prop := ls_ok g M /\ match g with PML.LS0 => lits_pristine M | _ => lits_ok M end.
(* [comment removed for export] *)
Lemma ls_ok_exit : forall g M, ls_ok g M ->
  atexit_state_at segs (ATEXIT_TAB IC) M (HS0 IC ++ ls_atexit g) /\ cell_is segs M (NEED_LOCKS IC) 1 0.
Proof. intros g M (_ & (H1 & H2 & _) & _). exact (conj H1 H2). Qed.

(* [comment removed for export] *)
Definition W_parA (P E : Z) : list L5.range := [(P, 272); (E, 16); (ERRCAT_GUARD IC, 2); (ATEXIT_TAB IC, ATEXIT_TAB_BYTES)].
End Mem.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fobj (M : mem) (FF : list fframe) (o n : Z) : Prop := CL5A.ainfr FF o n /\ o mod 8 = 0 /\ shadow_zero M o (n / 8).
(* [comment removed for export] *)
Definition rstk (ar : asan_run) (sp a n : Z) : Prop := sp <= a /\ a + n <= ar_sptop ar.
(* [comment removed for export] *)
Definition stksh (ar : asan_run) (M : mem) (sp scr : Z) : Prop :=
  shadow_zero M (sp - scr) ((Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - scr)) / 8).
Definition apart (a n b m : Z) : Prop := a + n <= b \/ b + m <= a.
(* [comment removed for export] *)
Definition afresh (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF : list fframe) (M' : mem) (q n : Z) : Prop :=
  ablock_range L ar q n /\ blocks_apart q n LB /\ fframes_apart q n FF /\ L5.defined M' q n /\ shadow_blk M' q n.

(* [comment removed for export] *)
Definition pcreditA (L : asan_layout) (cr : credit) (ps : PML.pstate) : Prop :=
  PML.ps_bcap ps <= 2 ^ 27 /\ PML.kleft ps * hl_k_per_malloc L <= fst cr /\ hl_b_lin L * PML.bleft ps + PML.kleft ps * hl_b_overhead L <= snd cr.
(* [comment removed for export] *)
Definition pcredit_xA (L : asan_layout) (cr : credit) (ps : PML.pstate) (kx bx : Z) : Prop :=
  0 <= kx /\ 0 <= bx /\ pcreditA L (fst cr - kx, snd cr - bx) ps.
End PMLA.
