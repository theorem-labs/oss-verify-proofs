(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA FPSteps L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibDefs.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeapA CutL5A.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMLA.
Definition mem := (word -> option byte).

Record consts : Type := CONSTS {
  VT_VISITOR : Z;
  VT_PARSER : Z;
  VT_FUNC : Z;
  VT_ISS : Z; VT_ISS_IOS : Z; VT_STRINGBUF : Z;
  OBJ_JSON_CATEGORY : Z; OBJ_SYSTEM_CATEGORY : Z;
  ATEXIT_HANDLER : Z;
  ATCXA_HANDLER : Z;
  CLASSIC_IMP : Z;
  IMG_RO_LO : Z; IMG_RO_HI : Z;
  GLOC_PTR : Z; GLOC_GUARD : Z;
  SYSCAT_GUARD : Z;
  ERRCAT_GUARD : Z;
  OBJ_CONV_CATEGORY : Z;
  CONVCAT_GUARD : Z;
  ATEXIT_TAB : Z;
  NEED_LOCKS : Z;
  LOCALE_LOCK : Z;
  HS0 : list (Z * Z);
  FOOT : list (Z * Z)
}.
Definition C_casan : consts := {|
  VT_VISITOR := 0x14d4e0; VT_PARSER := 0x14d000; VT_FUNC := 0x14d3b8; VT_ISS := 0x150da8; VT_ISS_IOS := 0x150dd0; VT_STRINGBUF := 0x150cb8;
  OBJ_JSON_CATEGORY := 0x157890; OBJ_SYSTEM_CATEGORY := 0x1578c8; ATEXIT_HANDLER := 0xef920; ATCXA_HANDLER := 0x74c7c; CLASSIC_IMP := 0x68f890;
  IMG_RO_LO := 0x10000; IMG_RO_HI := 0x154000;
  GLOC_PTR := 0x68f478; GLOC_GUARD := 0x68f480; SYSCAT_GUARD := 0x68f280; ERRCAT_GUARD := 0x68f048; ATEXIT_TAB := 0x6b0aa0; NEED_LOCKS := 0x6b0ce3; LOCALE_LOCK := 0x6b0dc0;
  OBJ_CONV_CATEGORY := 0x157888; CONVCAT_GUARD := 0x68f040;
  HS0 := [(0x133e24, 0x9e744); (0x133e24, 0xaf10c)];
  FOOT := [(0x68f048, 0x68f04a); (0x68f280, 0x68f282); (0x68f290, 0x68f488); (0x68f538, 0x68f9b8); (0x6900e8, 0x690148); (0x6b0aa0, 0x6b0cc0); (0x6b0ce3, 0x6b0ce4); (0x6b0dc0, 0x6b0dc4); (0x68f040, 0x68f042)]
|}.

Definition C_cboth : consts := {|
  VT_VISITOR := 0x14eae8; VT_PARSER := 0x14e5c0; VT_FUNC := 0x14e978; VT_ISS := 0x152170; VT_ISS_IOS := 0x152198; VT_STRINGBUF := 0x152080;
  OBJ_JSON_CATEGORY := 0x158c58; OBJ_SYSTEM_CATEGORY := 0x158c90; ATEXIT_HANDLER := 0xf0e3c; ATCXA_HANDLER := 0x7503c; CLASSIC_IMP := 0x690bd0;
  IMG_RO_LO := 0x10000; IMG_RO_HI := 0x156000;
  GLOC_PTR := 0x6907b8; GLOC_GUARD := 0x6907c0; SYSCAT_GUARD := 0x6905c0; ERRCAT_GUARD := 0x690388; ATEXIT_TAB := 0x6b1de0; NEED_LOCKS := 0x6b2023; LOCALE_LOCK := 0x6b2100;
  OBJ_CONV_CATEGORY := 0x158c50; CONVCAT_GUARD := 0x690380;
  HS0 := [(0x135340, 0x9eb04); (0x135340, 0xaf4cc)];
  FOOT := [(0x690388, 0x69038a); (0x6905c0, 0x6905c2); (0x6905d0, 0x6907c8); (0x690878, 0x690cf8); (0x691428, 0x691488); (0x6b1de0, 0x6b2000); (0x6b2023, 0x6b2024); (0x6b2100, 0x6b2104); (0x690380, 0x690382)]
|}.

Definition PC_LIB : Z := 0xaf184.          Definition PC_STRINIT : Z := 0xaf8f0.        Definition PC_ISS_CTOR : Z := 0xafa48.      Definition PC_READER_CTOR : Z := 0xafce4.
Definition PC_READ : Z := 0.         Definition PC_PARSER_DTOR : Z := 0xb10cc.    Definition PC_VEC_DTOR : Z := 0xb14c8.      Definition PC_ANNOT_DELETE : Z := 0xb15e8.
Definition PC_ANNOT_SHRINK : Z := 0xb1688. Definition PC_SOURCE_DTOR : Z := 0xb172c.    Definition PC_VEC_RESERVE : Z := 0xc9ebc.   Definition PC_ANNOT_NEW : Z := 0xc562c.
Definition PC_VEC_PUSH : Z := 0xc5120.     Definition PC_VEC_SLOW : Z := 0xc5224.       Definition PC_ANNOT_INCREASE : Z := 0xc5404. Definition PC_READ_NEXT : Z := 0.
Definition PC_RCHECK_DONE : Z := 0.  Definition PC_SET_EC : Z := 0xb6600.         Definition PC_RESET : Z := 0.         Definition PC_READ_CHUNK : Z := 0xb6468.
Definition PC_SKIP_WS : Z := 0.      Definition PC_PARSE_SOME : Z := 0xb6dac.     Definition PC_END_INT : Z := 0xbdf28.       Definition PC_END_FRAC : Z := 0xbdfd8.
Definition PC_POP_STATE : Z := 0xbe60c.    Definition PC_SKIP_SPACE : Z := 0xbe98c.     Definition PC_BEGIN_OBJECT : Z := 0xbec48.  Definition PC_BEGIN_ARRAY : Z := 0xbefcc.
Definition PC_PARSE_STRING : Z := 0xbf37c. Definition PC_PARSE_NUMBER : Z := 0xc0bd8.   Definition PC_PARSE_NULL : Z := 0xc1b98.    Definition PC_PARSE_TRUE : Z := 0xc20ac.
Definition PC_PARSE_FALSE : Z := 0xc257c.  Definition PC_END_OBJECT : Z := 0xc2a94.     Definition PC_END_ARRAY : Z := 0xc3068.     Definition PC_BEGIN_MEMBER : Z := 0xc3634.
Definition PC_PARENT : Z := 0xc38e0.       Definition PC_END_NEG : Z := 0xc3ca8.        Definition PC_END_POS : Z := 0xc4260.       Definition PC_DEC_I64 : Z := 0xc4818.
Definition PC_DECSTR_DOUBLE : Z := 0xc48f4. Definition PC_AFTER_VALUE : Z := 0xc4c9c.   Definition PC_DEC_U64 : Z := 0xc4f48.       Definition PC_END_STRING : Z := 0xc56b4.
Definition PC_APPEND_CP : Z := 0xc6340.    Definition PC_CONVERT : Z := 0xc65dc.        Definition PC_VALIDATE : Z := 0xc67b0.      Definition PC_TRANSLATE_ERRC : Z := 0xc6b54.
Definition PC_APPEND_RANGE : Z := 0xc70e0. Definition PC_PCHECK_DONE : Z := 0.    Definition PC_GUARD_ACQ : Z := 0xd187c.     Definition PC_GUARD_REL : Z := 0xd18cc.
Definition PC_OPDEL : Z := 0xee1a8.        Definition PC_STR_RESERVE : Z := 0xf0354.    Definition PC_STR_APPEND : Z := 0xf0574.    Definition PC_STR_GROW_BY : Z := 0xf0670.
Definition PC_STR_PUSH_BACK : Z := 0xf07bc. Definition PC_STR_COPY : Z := 0xf0bf0.      Definition PC_SYSTEM_CATEGORY : Z := 0xf4ae0. Definition PC_IOS_CLEAR : Z := 0xf58b8.
Definition PC_IOSB_INIT : Z := 0xf5990.    Definition PC_IOSB_DTOR : Z := 0xf5d5c.      Definition PC_ISTREAM_DTOR : Z := 0xf6048.  Definition PC_LOCALE_CTOR : Z := 0x11a468.
Definition PC_LOCALE_DTOR : Z := 0x11a540. Definition PC_STRTOD : Z := 0x1441ac.        Definition PC_OPNEW : Z := 0x14b93c.
Definition PC_SET_SHADOW_00 : Z := 0x829e4. Definition PC_SET_SHADOW_F5 : Z := 0x82aec. Definition PC_SET_SHADOW_F8 : Z := 0x82b04.

Section Mem.
Variable segs : list Segment.
Variable IC : consts.

Definition u8 (M : mem) := L5.u8_at segs M.   Definition u32 (M : mem) := L5.u32_at segs M.   Definition u64 (M : mem) := L5.u64_at segs M.
Definition b2z (b : bool) : Z := if b then 1 else 0.
Definition img_ro (M : mem) : Prop := L5.img_clear M (IMG_RO_LO IC) (IMG_RO_HI IC).

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

Definition parser_at (M : mem) (P : Z) (ps : PML.pstate) : Prop :=
  u64 M P (VT_PARSER IC) /\ u32 M (P + 8) 1024 /\
  u8 M (P + 12) 0 /\ u8 M (P + 13) 1 /\ u8 M (P + 14) 0 /\ u8 M (P + 15) 1 /\ u8 M (P + 16) 0 /\ u8 M (P + 17) 0 /\ u8 M (P + 18) 0 /\
  L5.lstr_short segs M (P + 24) [] /\ L5.lstr_short segs M (P + 48) [] /\ L5.lstr_short segs M (P + 72) [] /\
  u64 M (P + 96) (VT_FUNC IC) /\ u64 M (P + 128) (P + 96) /\
  u32 M (P + 144) (PML.ps_level ps) /\
  match PML.ps_win ps with None => u64 M (P + 192) 0 /\ u64 M (P + 200) 0 | Some (p, e) => u64 M (P + 200) p /\ u64 M (P + 192) e /\ p <= e end /\
  u8 M (P + 208) (PML.ps_st ps) /\ u8 M (P + 209) (PML.ps_sst ps) /\ u8 M (P + 210) (PML.ps_nst ps) /\
  u8 M (P + 211) (b2z (PML.ps_more ps)) /\ u8 M (P + 212) (b2z (PML.ps_done ps)) /\ u8 M (P + 213) 1 /\ u32 M (P + 216) 0 /\
  str_at M (P + 224) (PML.SLong (PML.ps_bcap ps) (PML.ps_bptr ps) (PML.ps_buf ps)) /\ 264 <= PML.ps_bcap ps /\
  u64 M (P + 248) (PML.ps_sb ps) /\ u64 M (P + 256) (PML.ps_sb ps + Z.of_nat (length (PML.ps_stack ps))) /\ u64 M (P + 264) (PML.ps_sb ps + PML.ps_scap ps) /\
  L5.bytes_at segs M (PML.ps_sb ps) (PML.ps_stack ps) /\ Z.of_nat (length (PML.ps_stack ps)) <= PML.ps_scap ps /\
  L5.defined M P 272.

Definition parser_sh (M : mem) (ps : PML.pstate) : Prop :=
  shadow_blk M (PML.ps_bptr ps) (PML.ps_bcap ps) /\ shadow_cont M (PML.ps_sb ps) (PML.ps_scap ps) (Z.of_nat (length (PML.ps_stack ps))).

Definition vis_at (M : mem) (V : Z) : Prop := u64 M V (VT_VISITOR IC) /\ L5.defined M V 48.
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
  u64 M (R + 304) (VT_VISITOR IC) /\ u64 M (R + 312) V /\
  (exists st0, iosb_at M (R + 88) st0 (R + 24)) /\ u64 M (R + 32) (CLASSIC_IMP IC) /\
  parser_at M (R + 320) ps /\
  match PML.ps_win ps with None => True | Some (p, e) => ch <= p /\ e <= ch + 16384 /\ L5.defined M p (e - p) end /\
  L5.defined M R 592.

Definition srep_sh (M : mem) (r : PML.srep) : Prop := match r with PML.SShort _ => True | PML.SLong cap p _ => shadow_blk M p cap end.

Definition win_okA (M : mem) (LBo : list (Z * Z)) (ps : PML.pstate) : Prop :=
  match PML.ps_win ps with
  | None => True
  | Some (p, e) => exists ch, In (ch, 16384) LBo /\ ch <= p /\ e <= ch + 16384 /\ L5.defined M p (e - p) /\ shadow_blk M ch 16384
  end.

Definition in_foot (a : Z) : Prop := exists iv, In iv (FOOT IC) /\ fst iv <= a < snd iv.
Definition in_tab (a : Z) : Prop := ATEXIT_TAB IC <= a < ATEXIT_TAB IC + ATEXIT_TAB_BYTES.

Definition foot_pristine (M : mem) : Prop := forall a, in_foot a -> ~ in_tab a -> a <> NEED_LOCKS IC -> M (Z_to_bv 64 a) = None.
Definition loc_done (M : mem) : Prop := u8 M (GLOC_GUARD IC) 1 /\ u64 M (GLOC_PTR IC) (CLASSIC_IMP IC) /\ u8 M (SYSCAT_GUARD IC) 1.
Definition errcat_guard (M : mem) (b : Z) : Prop := u8 M (ERRCAT_GUARD IC) b /\ u8 M (ERRCAT_GUARD IC + 1) b.
Definition convcat_guard (M : mem) (b : Z) : Prop := u8 M (CONVCAT_GUARD IC) b /\ u8 M (CONVCAT_GUARD IC + 1) b.

Definition jregs : list (Z * Z) := [(ATEXIT_HANDLER IC, OBJ_JSON_CATEGORY IC); (ATCXA_HANDLER IC, 0)].
Definition cregs : list (Z * Z) := [(ATEXIT_HANDLER IC, OBJ_CONV_CATEGORY IC); (ATCXA_HANDLER IC, 0)].
Definition ls_atexit (g : PML.ls_state) : list (Z * Z) :=
  match g with PML.LS0 | PML.LS1 => [] | PML.J => jregs | PML.C => cregs | PML.JC => jregs ++ cregs | PML.CJ => cregs ++ jregs end.

Definition libc_quiet (M : mem) : Prop := cell_is segs M (NEED_LOCKS IC) 1 0 /\ cell_is segs M (LOCALE_LOCK IC) 4 0.
Definition atexit_ok (M : mem) (g : PML.ls_state) : Prop :=
  atexit_state_at segs (ATEXIT_TAB IC) M (HS0 IC ++ ls_atexit g) /\ libc_quiet M.
Definition ls_ok (g : PML.ls_state) (M : mem) : Prop :=
  img_ro M /\ atexit_ok M g /\
  match g with
  | PML.LS0 => foot_pristine M
  | _ => loc_done M /\ errcat_guard M (PML.jbit g) /\ convcat_guard M (PML.cbit g)
  end.

Lemma ls_ok_exit : forall g M, ls_ok g M ->
  atexit_state_at segs (ATEXIT_TAB IC) M (HS0 IC ++ ls_atexit g) /\ cell_is segs M (NEED_LOCKS IC) 1 0.
Proof. intros g M (_ & (H1 & H2 & _) & _). exact (conj H1 H2). Qed.

Definition W_parA (P E : Z) : list L5.range := [(P, 272); (E, 16); (ERRCAT_GUARD IC, 2); (ATEXIT_TAB IC, ATEXIT_TAB_BYTES)].
End Mem.

Definition fobj (M : mem) (FF : list fframe) (o n : Z) : Prop := CL5A.ainfr FF o n /\ o mod 8 = 0 /\ shadow_zero M o (n / 8).

Definition rstk (ar : asan_run) (sp a n : Z) : Prop := sp <= a /\ a + n <= ar_sptop ar.

Definition stksh (ar : asan_run) (M : mem) (sp scr : Z) : Prop :=
  shadow_zero M (sp - scr) ((Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - scr)) / 8).
Definition apart (a n b m : Z) : Prop := a + n <= b \/ b + m <= a.

Definition afresh (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF : list fframe) (M' : mem) (q n : Z) : Prop :=
  ablock_range L ar q n /\ blocks_apart q n LB /\ fframes_apart q n FF /\ L5.defined M' q n /\ shadow_blk M' q n.

Definition pcreditA (L : asan_layout) (cr : credit) (ps : PML.pstate) : Prop :=
  PML.ps_bcap ps <= 2 ^ 27 /\ PML.kleft ps * hl_k_per_malloc L <= fst cr /\ hl_b_lin L * PML.bleft ps + PML.kleft ps * hl_b_overhead L <= snd cr.

Definition pcredit_xA (L : asan_layout) (cr : credit) (ps : PML.pstate) (kx bx : Z) : Prop :=
  0 <= kx /\ 0 <= bx /\ pcreditA L (fst cr - kx, snd cr - bx) ps.
End PMLA.
