(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface L5Defs L5Core PmLayout PmModel PgSrc PgV8.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNM.

Section Model.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable A : pm_addrs.
Variable acc : (word -> option byte) -> Z -> Z -> Prop.
Variable ann : (word -> option byte) -> Z -> Z -> Z -> Prop.
(* [comment removed for export] *)
Variable vp_parser : Z.      (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Record bstate : Type := BS { bs_mode : Z; bs_len : Z; bs_pos : Z; bs_type : Z; bs_idx : Z }.
Definition bs_root : bstate := BS 0 0 0 0 0.
Definition MAX_DEPTH : Z := 1024.
Definition BSZ : Z := 40.

Definition bstate_ok (s : bstate) : Prop :=
  0 <= bs_mode s <= 4 /\ 0 <= bs_len s < 2 ^ 64 /\ 0 <= bs_pos s < 2 ^ 64 /\ 0 <= bs_type s < 256 /\ 0 <= bs_idx s < 2 ^ 64.

Definition bstate_at (M : word -> option byte) (a : Z) (s : bstate) : Prop :=
  L5.u32_at segs M a (bs_mode s) /\ L5.u64_at segs M (a + 8) (bs_len s) /\ L5.u64_at segs M (a + 16) (bs_pos s)
  /\ L5.u8_at segs M (a + 24) (bs_type s) /\ L5.u64_at segs M (a + 32) (bs_idx s).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bvec_at (M : word -> option byte) (v b k : Z) (stk : list bstate) : Prop :=
  L5.u64_at segs M v b /\ L5.u64_at segs M (v + 8) (b + BSZ * Z.of_nat (length stk)) /\ L5.u64_at segs M (v + 16) (b + BSZ * 2 ^ k)
  /\ 0 <= k <= 11 /\ Z.of_nat (length stk) <= 2 ^ k /\ b mod 16 = 0
  /\ L5.defined M b (BSZ * 2 ^ k) /\ acc M b (BSZ * Z.of_nat (length stk)) /\ ann M b (BSZ * Z.of_nat (length stk)) (BSZ * 2 ^ k)
  /\ (forall i, (i < length stk)%nat -> bstate_at M (b + BSZ * Z.of_nat i) (nth i stk bs_root)).
Definition bvec_own (b k : Z) : list (Z * Z) := [(b, BSZ * 2 ^ k)].

(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation v8_at := (PGV8.v8_at segs acc ann).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition OFF_SRC : Z := 16.
Definition OFF_BB : Z := 320.
Definition OFF_NB : Z := 344.
Definition OFF_TB : Z := 368.
Definition OFF_STK : Z := 392.
Definition PSIZE : Z := 416.

Record bpst : Type := BPST {
  b_more : Z; b_done : Z;
  b_src : PM.srcst;
  b_bb : PGV8.v8;          (* [comment removed for export] *)
  b_nb : PM.vstr;          (* [comment removed for export] *)
  b_tb : PM.vstr;          (* [comment removed for export] *)
  b_ng : Z; b_tg : Z; b_bg : Z;   (* [comment removed for export] *)
  b_sb : Z; b_sk : Z; b_stk : list bstate   (* [comment removed for export] *)
}.

Definition bparser_at (M : word -> option byte) (op ois : Z) (s : bpst) : Prop :=
  L5.u64_at segs M op vp_parser /\ L5.defined M op PSIZE /\ acc M op 16
  /\ L5.u8_at segs M (op + 8) (b_more s) /\ L5.u8_at segs M (op + 9) (b_done s)
  /\ L5.u8_at segs M (op + 10) 0 /\ L5.u32_at segs M (op + 12) 0
  /\ PM.nullis_at segs A acc M (op + OFF_SRC + 8)
  /\ PM.src_fields_at segs acc M (op + OFF_SRC) ois (ois + 16) (b_src s)
  /\ L5.u32_at segs M (op + 312) MAX_DEPTH /\ acc M (op + 312) 8
  /\ v8_at M (op + OFF_BB) (b_bb s)
  /\ PM.vstr_at segs acc M (op + OFF_NB) (b_nb s)
  /\ PM.vstr_at segs acc M (op + OFF_TB) (b_tb s)
  /\ bvec_at M (op + OFF_STK) (b_sb s) (b_sk s) (b_stk s)
  /\ (b_more s = 0 \/ b_more s = 1) /\ (b_done s = 0 \/ b_done s = 1).

(* [comment removed for export] *)
Definition brest_own (s : bpst) : list (Z * Z) :=
  bvec_own (b_sb s) (b_sk s) ++ PGV8.v8_own (b_bb s) ++ PM.vs_own (b_nb s) ++ PM.vs_own (b_tb s).
Definition bparser_own (s : bpst) : list (Z * Z) := PM.src_own (b_src s) ++ brest_own s.

Definition with_srcB (s : bpst) (src' : PM.srcst) : bpst :=
  BPST (b_more s) (b_done s) src' (b_bb s) (b_nb s) (b_tb s) (b_ng s) (b_tg s) (b_bg s) (b_sb s) (b_sk s) (b_stk s).
(* [comment removed for export] *)
Definition bgrow_ok (s : bpst) : Prop :=
  PM.tb_ok (b_nb s) (b_ng s) /\ PM.tb_ok (b_tb s) (b_tg s) /\ PGV8.v8_ok (b_bb s) (b_bg s).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sso_win (o : Z) (x : PM.vstr) (p k : Z) : Prop := (exists n, x = PM.VShort n) /\ 0 <= k /\ o + 1 <= p /\ p + k <= o + 24.
Definition blk_win (l : list (Z * Z)) (p k : Z) : Prop := exists B m, In (B, m) l /\ 0 <= k /\ B <= p /\ p + k <= B + m.
Definition bwin (op : Z) (s : bpst) (p k : Z) : Prop :=
  sso_win (op + OFF_NB) (b_nb s) p k \/ sso_win (op + OFF_TB) (b_tb s) p k
  \/ blk_win (PGV8.v8_own (b_bb s) ++ PM.vs_own (b_nb s) ++ PM.vs_own (b_tb s)) p k.

Definition src_owner (op ois lo hi : Z) (s : bpst) : PGS.owner :=
  {| PGS.ow_at := fun M src OB => bparser_at M op ois (with_srcB s src) /\ OB = brest_own s;
     PGS.ow_os := op + OFF_SRC; PGS.ow_ois := ois; PGS.ow_lo := lo; PGS.ow_hi := hi;
     PGS.ow_win := fun M src OB p k => bwin op s p k |}.

(* [comment removed for export] *)
Definition with_src_tb (s : bpst) (src' : PM.srcst) (tb' : PM.vstr) (tg' : Z) : bpst :=
  BPST (b_more s) (b_done s) src' (b_bb s) (b_nb s) tb' (b_ng s) tg' (b_bg s) (b_sb s) (b_sk s) (b_stk s).
Definition txt_rest_own (s : bpst) : list (Z * Z) := bvec_own (b_sb s) (b_sk s) ++ PGV8.v8_own (b_bb s) ++ PM.vs_own (b_nb s).
Definition txt_owner (op ois lo hi : Z) (s : bpst) : PGS.towner :=
  {| PGS.tw_at := fun M src tb tg OB => bparser_at M op ois (with_src_tb s src tb tg) /\ PM.tb_ok tb tg /\ OB = txt_rest_own s;
     PGS.tw_os := op + OFF_SRC; PGS.tw_ois := ois; PGS.tw_otb := op + OFF_TB; PGS.tw_lo := lo; PGS.tw_hi := hi |}.

(* [comment removed for export] *)
Definition with_src_bb (s : bpst) (src' : PM.srcst) (bb' : PGV8.v8) (bg' : Z) : bpst :=
  BPST (b_more s) (b_done s) src' bb' (b_nb s) (b_tb s) (b_ng s) (b_tg s) bg' (b_sb s) (b_sk s) (b_stk s).
Definition vec_rest_own (s : bpst) : list (Z * Z) := bvec_own (b_sb s) (b_sk s) ++ PM.vs_own (b_nb s) ++ PM.vs_own (b_tb s).
Definition vec_owner (op ois lo hi : Z) (s : bpst) : PGV8.vowner :=
  {| PGV8.vw_at := fun M src x g OB => bparser_at M op ois (with_src_bb s src x g) /\ PGV8.v8_ok x g /\ OB = vec_rest_own s;
     PGV8.vw_os := op + OFF_SRC; PGV8.vw_ois := ois; PGV8.vw_ov := op + OFF_BB; PGV8.vw_lo := lo; PGV8.vw_hi := hi |}.

End Model.
End PNM.
