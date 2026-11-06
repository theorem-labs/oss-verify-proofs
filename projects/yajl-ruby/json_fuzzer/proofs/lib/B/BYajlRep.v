(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.   (* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Export RYajlRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlBuf YajlLex YajlDecode YajlParser.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages ExecA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_base.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition AY_TARGET_RUN : Z := 0x81b80.
Definition AY_FUZZ : Z := 0x81d50.          (* [comment removed for export] *)
Definition AY_CB_NULL : Z := 0x81f70.
Definition AY_CB_BOOLEAN : Z := 0x81f78.
Definition AY_CB_NUMBER : Z := 0x81f80.
Definition AY_CB_STRING : Z := 0x81fc4.
Definition AY_CB_START_MAP : Z := 0x81fcc.   (* [comment removed for export] *)
Definition AY_CB_MAP_KEY : Z := 0x82054.     (* [comment removed for export] *)
Definition AY_CB_END_MAP : Z := 0x820dc.     (* [comment removed for export] *)
Definition AY_CB_START_ARRAY : Z := 0x8218c.
Definition AY_CB_END_ARRAY : Z := 0x82214.
Definition AY_ALLOC : Z := 0x8232c.          (* [comment removed for export] *)
Definition AY_RESET : Z := 0x82914.          (* [comment removed for export] *)
Definition AY_FREE : Z := 0x829b0.           (* [comment removed for export] *)
Definition AY_PARSE : Z := 0x82b20.          (* [comment removed for export] *)
Definition AY_SET_DEFAULT : Z := 0x82b60.    (* [comment removed for export] *)
Definition AY_MALLOC_W : Z := 0x82c1c.       (* [comment removed for export] *)
Definition AY_FREE_W : Z := 0x82c28.         (* [comment removed for export] *)
Definition AY_REALLOC_W : Z := 0x82c30.      (* [comment removed for export] *)
Definition AY_LEX_ALLOC : Z := 0x82c44.
Definition AY_LEX_REALLOC : Z := 0x82da0.
Definition AY_LEX_FREE : Z := 0x82ecc.
Definition AY_LEX_LEX : Z := 0x82f9c.        (* [comment removed for export] *)
Definition AY_BUF_ERR : Z := 0x86f20.
Definition AY_BUF_ALLOC : Z := 0x86f94.
Definition AY_BUF_FREE : Z := 0x87068.
Definition AY_BUF_APPEND : Z := 0x871d0.     (* [comment removed for export] *)
Definition AY_BUF_CLEAR : Z := 0x87630.
Definition AY_BUF_DATA : Z := 0x87740.
Definition AY_BUF_LEN : Z := 0x87800.
Definition AY_NOOP_MALLOC : Z := 0x878cc.
Definition AY_NOOP_REALLOC : Z := 0x878e0.
Definition AY_NOOP_FREE : Z := 0x8793c.
Definition AY_DO_PARSE : Z := 0x87aa0.       (* [comment removed for export] *)
Definition AY_BS_SET : Z := 0x8b4c0.         (* [comment removed for export] *)
Definition AY_STRING_DECODE : Z := 0x8b5fc.  (* [comment removed for export] *)
Definition AY_HEXTODIGIT : Z := 0x8bc68.
(* [comment removed for export] *)
Definition AY_WRAP_MALLOC : Z := 0x53ea8.     (* [comment removed for export] *)
Definition AY_WRAP_FREE : Z := 0x53ea4.
Definition AY_WRAP_REALLOC : Z := 0x53eac.    (* [comment removed for export] *)
Definition AY_ASAN_MEMCPY : Z := 0x52b54.     (* [comment removed for export] *)
Definition AY_ASAN_MEMSET : Z := 0x52ff0.     (* [comment removed for export] *)
Definition AY_WRAP_STRLEN : Z := 0x43050.     (* [comment removed for export] *)
Definition AY_STACK_MALLOC_0 : Z := 0x3df9c.  (* [comment removed for export] *)
Definition AY_STACK_MALLOC_1 : Z := 0x3e110.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition AY_CALLBACKS : Z := 0xa9b40.      (* [comment removed for export] *)
Definition AY_NOOP_ALLOCS : Z := 0xa9bc0.    (* [comment removed for export] *)
Definition AY_BUF_ALLOC_ERROR : Z := 0xa9c00. (* [comment removed for export] *)
Definition AY_EMPTY : Z := 0x5e0c20.          (* [comment removed for export] *)
(* [comment removed for export] *)
Definition AY_GOT_SHADOW : Z := 0xa55a0.     (* [comment removed for export] *)
Definition AY_SHADOW_VAR : Z := 0xae5b8.     (* [comment removed for export] *)
Definition AY_GOT_UAR : Z := 0xa55f8.        (* [comment removed for export] *)
Definition AY_UAR_VAR : Z := 0xae5c0.        (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ay_perr (e : perr) : Z :=
  match e with
  | PE_client_cancelled => 0x21a00
  | PE_alloc_failed => 0x21a60
  | PE_unallowed_token => 0x21b40
  | PE_invalid_token_internal => 0x21ba0
  | PE_invalid_object_key => 0x21be0
  | PE_expect_colon => 0x21c40
  | PE_map_expect => 0x21ca0
  | PE_array_expect => 0x21d00
  end.

Definition ayc : yconsts :=
  mkYC AY_MALLOC_W AY_REALLOC_W AY_FREE_W AY_CALLBACKS
       AY_CB_NULL AY_CB_BOOLEAN AY_CB_NUMBER AY_CB_STRING AY_CB_START_MAP AY_CB_MAP_KEY AY_CB_END_MAP
       AY_CB_START_ARRAY AY_CB_END_ARRAY ay_perr AY_BUF_ALLOC_ERROR AY_NOOP_ALLOCS.

Definition anoop_allocs_cells : list cell :=
  [C8 (wz AY_NOOP_MALLOC); C8 (wz AY_NOOP_REALLOC); C8 (wz AY_NOOP_FREE); C8 (wz 0)].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition abl (l : list block) : list ablock := map (fun b => mkABlock (blk_addr b) (blk_size b)) l.

Lemma abl_app : forall l1 l2, abl (l1 ++ l2) = abl l1 ++ abl l2.
Proof. intros; apply map_app. Qed.
Lemma abl_cons : forall p A n l, abl ((p, A, n) :: l) = mkABlock A n :: abl l.
Proof. reflexivity. Qed.
Lemma in_abl : forall l b, In b l -> In (mkABlock (blk_addr b) (blk_size b)) (abl l).
Proof. intros l b H. unfold abl. apply (in_map (fun b0 => mkABlock (blk_addr b0) (blk_size b0))). exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition oshadow (m : mem) (A n : Z) : Prop := block_shadow bsegs m A_SB A n.

(* [comment removed for export] *)
Definition oshw_lo (A : Z) : Z := A_SB + A / 8.
Definition oshw_hi (A n : Z) : Z := A_SB + A / 8 + (n + 7) / 8.

Lemma oshadow_bound : forall m A n, oshadow m A n -> 0 <= oshw_lo A /\ oshw_hi A n <= 2^64 /\ A mod 8 = 0 /\ 0 < n.
Proof.
  intros m A n H. pose proof (block_shadow_bound bsegs m A_SB A n H) as [H1 H2].
  destruct H as (HA & Hn & _). unfold oshw_lo, oshw_hi. repeat split; lia.
Qed.

(* [comment removed for export] *)
Definition pol (P : acc -> Prop) (lo hi : Z) : Prop :=
  forall a k, lo <= a -> a + Z.of_nat k <= hi -> P (Z_to_bv 64 a, k).
Definition opol (P : acc -> Prop) (A n : Z) : Prop := pol P A (A + n) /\ pol P (oshw_lo A) (oshw_hi A n).

Lemma pol_sub : forall P lo hi lo' hi', pol P lo hi -> lo <= lo' -> hi' <= hi -> pol P lo' hi'.
Proof. intros P lo hi lo' hi' H H1 H2 a k Ha Hk. apply H; lia. Qed.

(* [comment removed for export] *)
Definition ay_statics (m : mem) : Prop :=
  rw_cells bsegs m AY_GOT_SHADOW [C8 (wz AY_SHADOW_VAR)]
  /\ rw_cells bsegs m AY_SHADOW_VAR [C8 (wz A_SB)]
  /\ rw_cells bsegs m AY_GOT_UAR [C8 (wz AY_UAR_VAR)]
  /\ rw_cells bsegs m AY_UAR_VAR [C4 (wz 1)].
(* [comment removed for export] *)
Definition AY_IMG_LO : Z := 0x10000.
Definition AY_IMG_HI : Z := 0x603000.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition FF_MAGIC_LIVE : Z := 0x41b58ab3.
Definition FF_MAGIC_RETIRED : Z := 0x45e0360e.
Definition fframe_head_cells (desc fn : Z) : list cell := [C8 (wz FF_MAGIC_LIVE); C8 (wz desc); C8 (wz fn)].
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SH_F1 : Z := 0xf1.  (* [comment removed for export] *)
Definition SH_F2 : Z := 0xf2.  (* [comment removed for export] *)
Definition SH_F3 : Z := 0xf3.  (* [comment removed for export] *)
Definition SH_F5 : Z := 0xf5.  (* [comment removed for export] *)
Definition SH_F8 : Z := 0xf8.  (* [comment removed for export] *)

End RC__1.
#[warnings="-notation-for-abbreviation"] Notation abuf_rep := (buf_rep bsegs).
#[warnings="-notation-for-abbreviation"] Notation abuf_struct := (buf_struct bsegs).
#[warnings="-notation-for-abbreviation"] Notation abuf_data := (buf_data bsegs).
#[warnings="-notation-for-abbreviation"] Notation alexer_rep := (lexer_rep bsegs).
#[warnings="-notation-for-abbreviation"] Notation alexer_struct := (lexer_struct bsegs).
#[warnings="-notation-for-abbreviation"] Notation ahand_rep := (hand_rep bsegs ayc).
#[warnings="-notation-for-abbreviation"] Notation ahand_struct := (hand_struct bsegs ayc).
#[warnings="-notation-for-abbreviation"] Notation abs_rep := (bs_rep bsegs).
#[warnings="-notation-for-abbreviation"] Notation actx_rep := (ctx_rep bsegs).
#[warnings="-notation-for-abbreviation"] Notation atext_at := (text_at bsegs).
#[warnings="-notation-for-abbreviation"] Notation ayalloc_cells := (alloc_cells ayc).
