(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require FPSteps.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PML.
Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition TP : Z := 0xd9620.            (* [comment removed for export] *)
Definition HEAP_STACK : Z := 8224.       (* [comment removed for export] *)
(* [comment removed for export] *)
Definition STRTOD_SCR_V : Z := 8944.

(* [comment removed for export] *)
Definition PC_LIB : Z := 0x39d90.        Definition PC_STRINIT : Z := 0x39f68.     Definition PC_ISS_CTOR : Z := 0x3a020.
Definition PC_READER_CTOR : Z := 0x3a1c0. Definition PC_READ : Z := 0x3a2d8.       Definition PC_PARSER_DTOR : Z := 0x3a414.
Definition PC_SOURCE_DTOR : Z := 0x3a570. Definition PC_SBUF_CTOR : Z := 0x3a8c8.  Definition PC_INIT_BUF_PTRS : Z := 0x3a9b4.
Definition PC_READER_CTOR2 : Z := 0x43500. Definition PC_OPTS_BASE_DTOR : Z := 0x3aecc. Definition PC_PARSER_CTOR : Z := 0x43800.
Definition PC_SOURCE_CTOR : Z := 0x43af8. Definition PC_NULLIS_CTOR : Z := 0x43b8c. Definition PC_VEC_RESERVE : Z := 0x43d0c.
Definition PC_FUNC_COPY : Z := 0x43de0.  Definition PC_VEC_PUSH : Z := 0x43e60.    Definition PC_READ_NEXT : Z := 0x43f60.
Definition PC_RCHECK_DONE : Z := 0x44138. Definition PC_SET_EC : Z := 0x42ec0.     Definition PC_READ_CHUNK : Z := 0x44268.
Definition PC_SKIP_WS : Z := 0x44330.    Definition PC_SRC_READ_CHUNK : Z := 0x44420. Definition PC_DETECT_JSON : Z := 0x4447c.
Definition PC_FILL_BUFFER : Z := 0x44538. Definition PC_DETECT_BOM : Z := 0x4461c.  Definition PC_PARSE_SOME : Z := 0x4474c.
Definition PC_END_INT : Z := 0x456e8.    Definition PC_END_FRAC : Z := 0x45714.    Definition PC_POP_STATE : Z := 0x45898.
Definition PC_SKIP_SPACE : Z := 0x45950. Definition PC_BEGIN_OBJECT : Z := 0x45a54. Definition PC_BEGIN_ARRAY : Z := 0x45b24.
Definition PC_PARSE_STRING : Z := 0x45bfc. Definition PC_PARSE_NUMBER : Z := 0x46314. Definition PC_PARSE_NULL : Z := 0x4690c.
Definition PC_PARSE_TRUE : Z := 0x46a24. Definition PC_PARSE_FALSE : Z := 0x46b4c.  Definition PC_END_OBJECT : Z := 0x46c80.
Definition PC_END_ARRAY : Z := 0x46dc0.  Definition PC_BEGIN_MEMBER : Z := 0x46f00. Definition PC_PARENT : Z := 0x46f94.
Definition PC_END_NEG : Z := 0x47040.    Definition PC_END_POS : Z := 0x471cc.     Definition PC_DEC_I64 : Z := 0x47358.
Definition PC_DECSTR_DOUBLE : Z := 0x42ba8. Definition PC_AFTER_VALUE : Z := 0x473f8. Definition PC_DEC_U64 : Z := 0x4748c.
Definition PC_END_STRING : Z := 0x47588. Definition PC_APPEND_CP : Z := 0x47998.   Definition PC_CONVERT : Z := 0x47a50.
Definition PC_VALIDATE : Z := 0x47bd0.   Definition PC_TRANSLATE_ERRC : Z := 0x47ddc. Definition PC_APPEND_RANGE : Z := 0x47ea0.
Definition PC_PCHECK_DONE : Z := 0x48130. Definition PC_GUARD_ACQ : Z := 0x481fc.   Definition PC_GUARD_REL : Z := 0x4824c.
Definition PC_OPDEL : Z := 0x64b24.      Definition PC_OPDEL_SIZED : Z := 0x64b28.  Definition PC_STR_GROW_REPLACE : Z := 0x66640.
Definition PC_STR_RESERVE : Z := 0x66cd4. Definition PC_STR_APPEND : Z := 0x66ef4.  Definition PC_STR_GROW_BY : Z := 0x66ff0.
Definition PC_STR_PUSH_BACK : Z := 0x6713c. Definition PC_STR_COPY : Z := 0x67570.  Definition PC_SYSTEM_CATEGORY : Z := 0x6b42c.
Definition PC_IOSB_DTOR : Z := 0x6c6a8.  Definition PC_IOS_CLEAR : Z := 0x6c204.   Definition PC_IOSB_INIT : Z := 0x6c2dc.
Definition PC_XSGETN : Z := 0x6c74c.     Definition PC_ISTREAM_DTOR : Z := 0x6c994. Definition PC_LOCALE_CTOR : Z := 0x90db4.
Definition PC_LOCALE_DTOR : Z := 0x90e8c. Definition PC_CXA_ATEXIT : Z := 0xa9de8.  Definition PC_STRTOD : Z := 0xb9904.
Definition PC_OPNEW : Z := 0xbf594.      Definition PC_MALLOC : Z := 0xabfac.      Definition PC_FREE : Z := 0xabe6c.

(* [comment removed for export] *)
Definition VT_VISITOR : Z := 0xc08e0.    (* [comment removed for export] *)
Definition VT_DEFVIS : Z := 0xc0de8.    (* [comment removed for export] *)
Definition VT_PARSER : Z := 0xc06e0.     (* [comment removed for export] *)
Definition VT_FUNC : Z := 0xc0cc0.       (* [comment removed for export] *)
Definition VT_ISS : Z := 0xc43d8.        (* [comment removed for export] *)
Definition VT_ISS_IOS : Z := 0xc4400.
Definition VT_STRINGBUF : Z := 0xc42e8.  (* [comment removed for export] *)
Definition OBJ_JSON_CATEGORY : Z := 0xc7888.  Definition OBJ_SYSTEM_CATEGORY : Z := 0xc78c0.
Definition ATEXIT_HANDLER : Z := 0x662a0.     (* [comment removed for export] *)
Definition AX : Z := 0xf9668.                       (* [comment removed for export] *)
Definition ATEXIT_CALL : Z := 0xa9f74.              (* [comment removed for export] *)
Definition AEF_EXIT_GUARD : Z := 0x39d18.           (* [comment removed for export] *)
Definition CLASSIC_IMP : Z := 0xd8460.        (* [comment removed for export] *)
Definition IMG_RO_HI : Z := 0xc6860.          (* [comment removed for export] *)

Definition img_ro (M : mem) : Prop := L5.img_clear M 0x10000 IMG_RO_HI.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive srep : Type := SShort (s : list Z) | SLong (cap p : Z) (s : list Z).
Definition srep_chars (r : srep) : list Z := match r with SShort s => s | SLong _ _ s => s end.
Definition srep_data (o : Z) (r : srep) : Z := match r with SShort _ => o + 1 | SLong _ p _ => p end.
Definition str_at (M : mem) (o : Z) (r : srep) : Prop :=
  match r with
  | SShort s => L5.lstr_short RSEGS M o s
  | SLong cap p s => L5.lstr_long RSEGS M o s (cap + 1) p /\ cap mod 8 = 0 /\ Z.of_nat (length s) < cap
  end.
(* [comment removed for export] *)
Definition str_at_w (M : mem) (o : Z) (r : srep) : Prop :=
  match r with
  | SShort s => L5.lstr_short RSEGS M o s
  | SLong cap p s => L5.lstr_long RSEGS M o s (cap + 1) p /\ Z.of_nat (length s) < cap
  end.
(* [comment removed for export] *)
Definition srep_blocks (r : srep) : list (Z * Z) := match r with SShort _ => [] | SLong cap p _ => [(p, cap)] end.
Definition str_cap (n : Z) : Z := if Z.eqb (Z.lor n 7) 23 then 26 else Z.lor n 7 + 1.   (* [comment removed for export] *)
Definition copy_cap (n : Z) : Z := Z.lor (Z.max n 44) 7 + 1.                               (* [comment removed for export] *)
Definition grow_cap (cap need : Z) : Z := Z.lor (Z.max need (2 * (cap - 1))) 7 + 1.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ST_ROOT := 0.  Definition ST_START := 1.  Definition ST_ACCEPT := 2.  Definition ST_SLASH := 3.  Definition ST_SLASH_SLASH := 4.
Definition ST_SLASH_STAR := 5.  Definition ST_SLASH_STAR_STAR := 6.  Definition ST_EXPECT_COMMA_OR_END := 7.  Definition ST_OBJECT := 8.
Definition ST_EXPECT_MEMBER_NAME_OR_END := 9.  Definition ST_EXPECT_MEMBER_NAME := 10.  Definition ST_EXPECT_COLON := 11.
Definition ST_EXPECT_VALUE_OR_END := 12.  Definition ST_EXPECT_VALUE := 13.  Definition ST_ARRAY := 14.  Definition ST_STRING := 15.
Definition ST_MEMBER_NAME := 16.  Definition ST_NUMBER := 17.  Definition ST_CR := 28.  Definition ST_DONE := 29.

(* [comment removed for export] *)
Record pstate : Type := PS {
  ps_st : Z; ps_sst : Z; ps_nst : Z; ps_more : bool; ps_done : bool; ps_level : Z;
  ps_stack : list Z;                 (* [comment removed for export] *)
  ps_sb : Z; ps_scap : Z;            (* [comment removed for export] *)
  ps_bcap : Z; ps_bptr : Z; ps_buf : list Z;   (* [comment removed for export] *)
  ps_win : option (Z * Z)            (* [comment removed for export] *)
}.
Definition ps_blocks (ps : pstate) : list (Z * Z) := [(ps_bptr ps, ps_bcap ps); (ps_sb ps, ps_scap ps)].
(* [comment removed for export] *)
Definition ps_set_win (ps : pstate) (w : option (Z * Z)) : pstate :=
  PS (ps_st ps) (ps_sst ps) (ps_nst ps) (ps_more ps) (ps_done ps) (ps_level ps) (ps_stack ps) (ps_sb ps) (ps_scap ps) (ps_bcap ps) (ps_bptr ps) (ps_buf ps) w.

Definition is_container (x : Z) : Prop := x = ST_OBJECT \/ x = ST_ARRAY.
Definition is_expect (x : Z) : Prop := In x [1; 7; 9; 10; 11; 12; 13].
Definition handled (x : Z) : Prop := 1 <= x <= 7 \/ 9 <= x <= 13 \/ x = 15 \/ 17 <= x <= 28.
Definition comment_or_cr (x : Z) : Prop := 3 <= x <= 6 \/ x = ST_CR.
(* [comment removed for export] *)
Definition transient (st : Z) (T : list Z) : Prop :=
     (T = [] /\ ~ comment_or_cr st)
  \/ (T = [ST_MEMBER_NAME] /\ st = ST_STRING)
  \/ (exists S, is_expect S /\ T = [S] /\ comment_or_cr st)
  \/ (exists S, is_expect S /\ T = [S; ST_SLASH_STAR] /\ st = ST_CR).

(* [comment removed for export] *)
Definition is_dig (c : Z) : bool := (48 <=? c) && (c <=? 57).
Definition nl_step (k c : Z) : option Z :=
  if Z.eqb k (-1) then (if Z.eqb c 45 then Some 0 else if Z.eqb c 48 then Some 1 else if is_dig c then Some 2 else None)
  else if Z.eqb k 0 then (if Z.eqb c 48 then Some 1 else if is_dig c then Some 2 else None)
  else if Z.eqb k 1 then (if Z.eqb c 46 then Some 3 else if Z.eqb c 101 || Z.eqb c 69 then Some 5 else if is_dig c then Some 2 (* [comment removed for export] *) else None)
  else if Z.eqb k 2 then (if is_dig c then Some 2 else if Z.eqb c 46 then Some 3 else if Z.eqb c 101 || Z.eqb c 69 then Some 5 else None)
  else if Z.eqb k 3 then (if is_dig c then Some 4 else None)
  else if Z.eqb k 4 then (if is_dig c then Some 4 else if Z.eqb c 101 || Z.eqb c 69 then Some 5 else None)
  else if Z.eqb k 5 then (if Z.eqb c 45 || Z.eqb c 43 then Some 6 else if is_dig c then Some 7 else None)
  else if Z.eqb k 6 then (if is_dig c then Some 7 else None)
  else if Z.eqb k 7 then (if is_dig c then Some 7 else None)
  else None.
Fixpoint nl_run (k : Z) (s : list Z) : option Z :=
  match s with [] => Some k | c :: r => match nl_step k c with Some k' => nl_run k' r | None => None end end.
(* [comment removed for export] *)
Definition num_prefix (nst : Z) (s : list Z) : Prop := exists k, nl_run (-1) s = Some k /\ (nst = k \/ (nst = 2 /\ k = 1)).
(* [comment removed for export] *)
Definition num_final (s : list Z) : Prop := exists k, nl_run (-1) s = Some k /\ In k [1; 2; 4; 7].

(* [comment removed for export] *)
Definition wf_ps (ps : pstate) : Prop :=
  0 <= ps_sst ps <= 11 /\ 0 <= ps_nst ps <= 7 /\
  (length (ps_stack ps) <= 1027)%nat /\ In (ps_scap ps) [66; 132; 264; 528; 1056] /\
  exists C T, ps_stack ps = ST_ROOT :: C ++ T /\ Forall is_container C /\
    (ps_more ps = true ->
       Z.of_nat (length C) = ps_level ps /\ 0 <= ps_level ps <= 1024 /\ handled (ps_st ps) /\ transient (ps_st ps) T /\
       (* [comment removed for export] *)
       (ps_st ps = ST_EXPECT_COMMA_OR_END \/ In ST_EXPECT_COMMA_OR_END T -> 1 <= ps_level ps) /\
       (ps_st ps = ST_NUMBER -> num_prefix (ps_nst ps) (ps_buf ps))).

(* [comment removed for export] *)
Definition ws_ok (ps : pstate) : Prop :=
  ps_more ps = false ->
  exists C, Forall is_container C /\ (length C <= 1024)%nat /\
    ((ps_st ps = ST_DONE /\ ps_stack ps = ST_ROOT :: C) \/ (ps_st ps = ST_CR /\ ps_stack ps = ST_ROOT :: C ++ [ST_DONE])) /\
    (* [comment removed for export] *)
    0 <= ps_level ps <= 1024.

(* [comment removed for export] *)
Definition ps_set_nst (ps : pstate) (n : Z) : pstate :=
  PS (ps_st ps) (ps_sst ps) n (ps_more ps) (ps_done ps) (ps_level ps) (ps_stack ps) (ps_sb ps) (ps_scap ps) (ps_bcap ps) (ps_bptr ps) (ps_buf ps) (ps_win ps).
Definition wf_ps_stale (ps : pstate) : Prop := 0 <= ps_nst ps <= 7 /\ exists n', wf_ps (ps_set_nst ps n').
Lemma wf_ps_stale_of : forall ps, wf_ps ps -> wf_ps_stale ps.
Proof. intros ps H. split; [exact (proj1 (proj2 H))|]. exists (ps_nst ps). destruct ps; exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition b2z (b : bool) : Z := if b then 1 else 0.
Definition u8 (M : mem) := L5.u8_at RSEGS M.   Definition u32 (M : mem) := L5.u32_at RSEGS M.   Definition u64 (M : mem) := L5.u64_at RSEGS M.

(* [comment removed for export] *)
Definition parser_at (M : mem) (P : Z) (ps : pstate) : Prop :=
  u64 M P VT_PARSER /\ u32 M (P + 8) 1024 /\
  u8 M (P + 12) 0 /\ u8 M (P + 13) 1 /\ u8 M (P + 14) 0 /\ u8 M (P + 15) 1 /\ u8 M (P + 16) 0 /\ u8 M (P + 17) 0 /\ u8 M (P + 18) 0 /\
  L5.lstr_short RSEGS M (P + 24) [] /\ L5.lstr_short RSEGS M (P + 48) [] /\ L5.lstr_short RSEGS M (P + 72) [] /\
  u64 M (P + 96) VT_FUNC /\ u64 M (P + 128) (P + 96) /\
  u32 M (P + 144) (ps_level ps) /\
  match ps_win ps with None => u64 M (P + 192) 0 /\ u64 M (P + 200) 0 | Some (p, e) => u64 M (P + 200) p /\ u64 M (P + 192) e /\ p <= e end /\
  u8 M (P + 208) (ps_st ps) /\ u8 M (P + 209) (ps_sst ps) /\ u8 M (P + 210) (ps_nst ps) /\
  u8 M (P + 211) (b2z (ps_more ps)) /\ u8 M (P + 212) (b2z (ps_done ps)) /\ u8 M (P + 213) 0 /\ u32 M (P + 216) 0 /\
  str_at M (P + 224) (SLong (ps_bcap ps) (ps_bptr ps) (ps_buf ps)) /\ 264 <= ps_bcap ps /\
  u64 M (P + 248) (ps_sb ps) /\ u64 M (P + 256) (ps_sb ps + Z.of_nat (length (ps_stack ps))) /\ u64 M (P + 264) (ps_sb ps + ps_scap ps) /\
  L5.bytes_at RSEGS M (ps_sb ps) (ps_stack ps) /\ Z.of_nat (length (ps_stack ps)) <= ps_scap ps /\
  L5.defined M P 272.

(* [comment removed for export] *)
Definition vis_at (M : mem) (V : Z) : Prop := u64 M V VT_VISITOR.
Definition ec_at (M : mem) (E : Z) (code : Z) : Prop :=
  u32 M E code /\ L5.defined M E 16 /\ (code = 0 \/ (1 <= code <= 31 /\ u64 M (E + 8) OBJ_JSON_CATEGORY)).

(* [comment removed for export] *)
Definition iosb_at (M : mem) (B : Z) (rdstate rdbuf : Z) : Prop :=
  u32 M (B + 32) rdstate /\ u32 M (B + 36) 0 /\ u64 M (B + 40) rdbuf /\ u64 M (B + 48) CLASSIC_IMP /\
  (forall k, 0 <= k < 10 -> u64 M (B + 56 + 8 * k) 0) /\ L5.defined M B 152.

(* [comment removed for export] *)
Definition isrc_at (M : mem) (IS : Z) (rep : srep) (g : Z) (rdstate : Z) : Prop :=
  let D := srep_data (IS + 80) rep in let n := Z.of_nat (length (srep_chars rep)) in
  u64 M IS VT_ISS /\ u64 M (IS + 16) VT_STRINGBUF /\ u64 M (IS + 24) CLASSIC_IMP /\
  u64 M (IS + 32) D /\ u64 M (IS + 40) g /\ u64 M (IS + 48) (D + n) /\ D <= g <= D + n /\
  u64 M (IS + 56) 0 /\ u64 M (IS + 64) 0 /\ u64 M (IS + 72) 0 /\
  str_at M (IS + 80) rep /\ u64 M (IS + 104) (D + n) /\ u32 M (IS + 112) 8 /\
  u64 M (IS + 120) VT_ISS_IOS /\ iosb_at M (IS + 120) rdstate (IS + 16) /\ (rdstate = 0 \/ rdstate = 2) /\
  L5.defined M IS 272.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition source_at (M : mem) (R ch : Z) : Prop :=
  u64 M (R + 264) ch /\ u64 M (R + 272) 16384 /\ (exists st0, iosb_at M (R + 88) st0 (R + 24)) /\ u64 M (R + 32) CLASSIC_IMP /\ L5.defined M R 320.
Definition reader_at (M : mem) (R IS V ch : Z) (bof : bool) (ps : pstate) : Prop :=
  u64 M (R + 240) IS /\ u64 M (R + 248) (IS + 16) /\ u64 M (R + 264) ch /\ u64 M (R + 272) 16384 /\
  (exists de, u64 M (R + 280) de /\ ch <= de <= ch + 16384) /\ u64 M (R + 288) 0 /\ u8 M (R + 296) (b2z bof) /\
  u64 M (R + 304) VT_DEFVIS /\ u64 M (R + 312) V /\
  (exists st0, iosb_at M (R + 88) st0 (R + 24)) /\ u64 M (R + 32) CLASSIC_IMP /\
  parser_at M (R + 320) ps /\
  match ps_win ps with None => True | Some (p, e) => ch <= p /\ e <= ch + 16384 /\ L5.defined M p (e - p) end /\
  L5.defined M R 592.

(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive ls_state : Type := LS0 | LS1 | LS2.
(* [comment removed for export] *)
Definition ll_foot_xsrc : list (Z * Z) :=
  [(0xd7bd0, 0xd7bd2); (0xd7e50, 0xd7e52); (0xd7e60, 0xd8058); (0xd8108, 0xd8588); (0xd8cb8, 0xd8d18); (0xf9668, 0xf9888)].   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ll_prist_xsrc : list (Z * Z) :=
  [(0xd7bd0, 0xd7bd2); (0xd7e50, 0xd7e52); (0xd7e60, 0xd8058); (0xd8108, 0xd8588); (0xd8cb8, 0xd8d18)].
(* [comment removed for export] *)
Definition ll_footx_xsrc : list (Z * Z) := ll_foot_xsrc ++ [(0xd7bd8, 0xd7c20)].
Definition in_foot11 (a : Z) : Prop := exists iv, In iv ll_foot_xsrc /\ fst iv <= a < snd iv.
Definition in_prist11 (a : Z) : Prop := exists iv, In iv ll_prist_xsrc /\ fst iv <= a < snd iv.
Definition foot_pristine (M : mem) : Prop := forall a, in_prist11 a -> M (Z_to_bv 64 a) = None.
Lemma in_prist_foot11 : forall a, in_prist11 a -> in_foot11 a.
Proof. intros a (iv & Hiv & Hr). exists iv. split; [|exact Hr]. cbn in Hiv |- *. tauto. Qed.
Definition loc_done (M : mem) : Prop := u8 M 0xd8050 1 /\ u64 M 0xd8048 CLASSIC_IMP /\ u8 M 0xd7e50 1.
Definition atexit_cells (M : mem) (hs : list (Z * Z)) : Prop :=
  u8 M 0xf9668 0 /\ u32 M 0xf966c 0 /\ u32 M 0xf9670 (1 + Z.of_nat (length hs)) /\ u64 M 0xf9678 0xf9680 /\ u64 M 0xf9680 0 /\
  u64 M 0xf9688 ATEXIT_CALL /\ u64 M 0xf9788 AEF_EXIT_GUARD /\      (* [comment removed for export] *)
  match hs with
  | [] => True
  | [(f, a)] => u64 M 0xf9690 f /\ u64 M 0xf9790 a                  (* [comment removed for export] *)
  | _ => False
  end.
Definition ls_atexit (g : ls_state) : list (Z * Z) := match g with LS2 => [(ATEXIT_HANDLER, OBJ_JSON_CATEGORY)] | _ => [] end.
Definition errcat_guard (M : mem) (b : Z) : Prop := u8 M 0xd7bd0 b /\ u8 M 0xd7bd1 b.
(* [comment removed for export] *)
Definition NEED_LOCKS : Z := 0xf98b3.   Definition LOCALE_LOCK : Z := 0xf9988.
Definition libc_quiet (M : mem) : Prop := u8 M NEED_LOCKS 0 /\ u32 M LOCALE_LOCK 0.
Definition ls_ok (g : ls_state) (M : mem) : Prop :=
  img_ro M /\ libc_quiet M /\
  match g with
  | LS0 => foot_pristine M /\ atexit_cells M []
  | LS1 => loc_done M /\ errcat_guard M 0 /\ atexit_cells M []
  | LS2 => loc_done M /\ errcat_guard M 1 /\ atexit_cells M (ls_atexit LS2)
  end.
(* [comment removed for export] *)
Definition LIT_LO : Z := 0xd7bd8.   Definition LIT_HI : Z := 0xd7c20.
Definition LIT_NULL_S  : Z := 0xd7bd8.  Definition LIT_NULL_G  : Z := 0xd7be8.  Definition LIT_NULL_TXT  : Z := 0x10fea.
Definition LIT_TRUE_S  : Z := 0xd7bf0.  Definition LIT_TRUE_G  : Z := 0xd7c00.  Definition LIT_TRUE_TXT  : Z := 0x11a2d.
Definition LIT_FALSE_S : Z := 0xd7c08.  Definition LIT_FALSE_G : Z := 0xd7c18.  Definition LIT_FALSE_TXT : Z := 0x1030d.
(* [comment removed for export] *)
Definition lit_ok (M : mem) (S G txt len : Z) : Prop :=
     (u8 M G 0 /\ u8 M (G + 1) 0 /\ u64 M S 0 /\ u64 M (S + 8) 0)
  \/ (u8 M G 1 /\ u8 M (G + 1) 1 /\ u64 M S txt /\ u64 M (S + 8) len).
Definition lits_ok (M : mem) : Prop :=
  lit_ok M LIT_NULL_S LIT_NULL_G LIT_NULL_TXT 4 /\ lit_ok M LIT_TRUE_S LIT_TRUE_G LIT_TRUE_TXT 4 /\ lit_ok M LIT_FALSE_S LIT_FALSE_G LIT_FALSE_TXT 5.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lits_pristine (M : mem) : Prop := forall a, LIT_LO <= a < LIT_HI -> M (Z_to_bv 64 a) = None.
Definition ls_okx (g : ls_state) (M : mem) : Prop := ls_ok g M /\ match g with LS0 => lits_pristine M | _ => lits_ok M end.
(* [comment removed for export] *)
Lemma lits_ok_agree : forall (M M' : mem), (forall a, LIT_LO <= a < LIT_HI -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> lits_ok M -> lits_ok M'.
Proof.
  intros M M' HE H. unfold lits_ok, lit_ok, u8, u64, L5.u8_at, L5.u64_at in *.
  assert (R : forall a n, LIT_LO <= a -> a + Z.of_nat n <= LIT_HI -> rdn RSEGS M' (Z_to_bv 64 a) n = rdn RSEGS M (Z_to_bv 64 a) n).
  { intros a n H1 H2. apply (L5C.rdn_agree RSEGS M M' n a); [unfold LIT_LO in *; lia | unfold LIT_HI in *; lia | intros i Hi; apply HE; lia]. }
  rewrite !R by (unfold LIT_LO, LIT_HI, LIT_NULL_S, LIT_NULL_G, LIT_TRUE_S, LIT_TRUE_G, LIT_FALSE_S, LIT_FALSE_G; cbn; lia). exact H.
Qed.
(* [comment removed for export] *)
Definition ls_next (g g' : ls_state) : Prop := match g, g' with LS0, LS0 => False | LS2, LS1 => False | _, LS0 => False | _, _ => True end.
(* [comment removed for export] *)
Lemma atexit_cells_agree : forall (M M' : mem) hs,
  (forall a, AX <= a < AX + 544 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> atexit_cells M hs -> atexit_cells M' hs.
Proof.
  intros M M' hs HE H. unfold atexit_cells, u8, u32, u64, L5.u8_at, L5.u32_at, L5.u64_at in *.
  assert (R : forall a n, AX <= a -> a + Z.of_nat n <= AX + 544 -> rdn RSEGS M' (Z_to_bv 64 a) n = rdn RSEGS M (Z_to_bv 64 a) n).
  { intros a n H1 H2. apply (L5C.rdn_agree RSEGS M M' n a); [unfold AX in *; lia | unfold AX in *; lia | intros i Hi; apply HE; lia]. }
  rewrite !R by (unfold AX; cbn; lia).
  destruct hs as [|[f a] [|]]; [| | exact H]; rewrite ?R by (unfold AX; cbn; lia); exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kleft (ps : pstate) : Z := Z.log2 (2 ^ 27 / ps_bcap ps) + Z.log2 (1056 / ps_scap ps).
Definition bleft (ps : pstate) : Z := (2 ^ 28 - 2 * ps_bcap ps) + (2112 - 2 * ps_scap ps).
Definition pcredit (L : heap_layout) (cr : credit) (ps : pstate) : Prop :=
  ps_bcap ps <= 2 ^ 27 /\ kleft ps * hl_k_per_malloc L <= fst cr /\ bleft ps + kleft ps * hl_b_overhead L <= snd cr.
(* [comment removed for export] *)
Definition pcredit_x (L : heap_layout) (cr : credit) (ps : pstate) (kx bx : Z) : Prop :=
  0 <= kx /\ 0 <= bx /\ pcredit L (fst cr - kx, snd cr - bx) ps.
(* [comment removed for export] *)
Definition winlen (ps : pstate) : Z := match ps_win ps with None => 0 | Some (p, e) => e - p end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition esc_need (sst : Z) : Z := nth (Z.to_nat sst) [0; 0; 0; 1; 2; 3; 0; 0; 0; 1; 2; 3] 0.
Definition buf_need (ps : pstate) : Z := if (ps_more ps && Z.eqb (ps_st ps) ST_STRING)%bool then esc_need (ps_sst ps) else 0.
Definition buf_bound (ps : pstate) (B : Z) : Prop := Z.of_nat (length (ps_buf ps)) + winlen ps + buf_need ps <= B /\ B < 2 ^ 26.
(* [comment removed for export] *)
Definition win_ok (M : mem) (LBo : list (Z * Z)) (ps : pstate) : Prop :=
  match ps_win ps with None => True | Some (p, e) => exists ch, In (ch, 16384) LBo /\ ch <= p /\ e <= ch + 16384 /\ L5.defined M p (e - p) end.
(* [comment removed for export] *)
Definition obj_on_stack (L : heap_layout) (sp o n : Z) : Prop := sp <= o /\ o + n <= hl_sptop L /\ o mod 8 = 0.
Definition apart (a n b m : Z) : Prop := a + n <= b \/ b + m <= a.
(* [comment removed for export] *)
Definition W_par (P E : Z) : list L5.range := [(P, 272); (E, 16); (0xd7bd0, 2); (0xf9668, 544)].

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CPS.
Context {SCFG_P : ScfgP}.

Definition cfg {fx : FPState} (R : bvmap 5 word) (pc : Z) (M : mem) (model : Model) : config :=
  mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) model.
Definition model_ok (model : Model) : Prop := m_halted model = None /\ m_vm_lazy model = [] /\ m_vm_materialized model = [].
(* [comment removed for export] *)
Definition fp_ok (fx : FPState) : Prop := FPSteps.frm_zero (@fp_csr fx).

(* [comment removed for export] *)
Definition entry (L : heap_layout) (R : bvmap 5 word) (M : mem) (sp r scr : Z) : Prop :=
  getr R 1%bv = Z_to_bv 64 r /\ L5.ra_ok r /\ getr R 2%bv = Z_to_bv 64 sp /\ getr R 4%bv = Z_to_bv 64 TP /\ L5C.stk (hl_sptop L) M sp scr.
Definition a0 (R : bvmap 5 word) (v : Z) : Prop := getr R 10%bv = Z_to_bv 64 v.
Definition a1 (R : bvmap 5 word) (v : Z) : Prop := getr R 11%bv = Z_to_bv 64 v.
Definition a2 (R : bvmap 5 word) (v : Z) : Prop := getr R 12%bv = Z_to_bv 64 v.
Definition a3 (R : bvmap 5 word) (v : Z) : Prop := getr R 13%bv = Z_to_bv 64 v.

(* [comment removed for export] *)
Definition cps_pure (pc r sp scr : Z) (W : list L5.range)
           (Pre : bvmap 5 word -> mem -> Prop) (Post : bvmap 5 word -> mem -> bvmap 5 word -> mem -> Prop) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (K : TSet),
    m_halted model = None -> m_vm_lazy model = [] -> K [] -> fp_ok fx -> Pre R M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem),
        fp_ok fx' -> Post R M R' M' -> regs_preserved R R' -> L5.frame_but ((sp - scr, scr) :: W) M M' -> mem_grows M M' ->
        srealizes RSEGS SCFG (@cfg fx' R' r M' model) K) ->
    srealizes RSEGS SCFG (@cfg fx R pc M model) K.

(* [comment removed for export] *)
Definition cps_heap (L : heap_layout) (HI : heap_iface) (pc r sp scr : Z) (LB : list (Z * Z)) (cr : credit)
           (Pre : bvmap 5 word -> mem -> Prop)
           (Post : bvmap 5 word -> mem -> bvmap 5 word -> mem -> list (Z * Z) -> credit -> list (Z * Z) -> list L5.range -> Prop) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : mem) (model : Model) (K : TSet),
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] -> fp_ok fx -> Pre R M ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range),
        fp_ok fx' -> Post R M R' M' LB' cr' LBk W -> regs_preserved R R' ->
        L5C.hpres L LBk sp scr W M M' -> model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (@cfg fx' R' r M' model') K) ->
    srealizes RSEGS SCFG (@cfg fx R pc M model) K.
End CPS.
End PML.
