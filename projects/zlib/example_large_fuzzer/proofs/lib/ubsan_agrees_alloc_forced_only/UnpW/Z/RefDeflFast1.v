(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreeMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefBitsLib.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflBlkApi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma keeps_hash_size : keeps ds_hash_size true true.
Proof. constructor; intros; try match goal with tt : tree_id |- _ => destruct tt end; match goal with ss : deflate_state |- _ => destruct ss; reflexivity end. Qed.

Definition cs_io (c : cstrm) := (cs_input c, cs_next_in c, cs_avail_in c, cs_out_rev c, cs_avail_out c, cs_total_in c, cs_total_out c, cs_msg c, cs_adler c).
Definition ds_io (s : deflate_state) := cs_io (ds_strm s).

(* [comment removed for export] *)
Definition ds_sizes (s : deflate_state) := (ds_w_size s, ds_hash_size s, ds_lit_bufsize s).

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma tr_flush_bits_cases : forall s,
  tr_flush_bits s = s
  \/ tr_flush_bits s = set_bi_valid (set_bi_buf (put_byte s (ds_bi_buf s)) (Z.shiftr (ds_bi_buf s) 8)) (ds_bi_valid s - 8)
  \/ tr_flush_bits s = set_bi_valid (set_bi_buf (put_byte (put_byte s (Z.land (ds_bi_buf s) 255)) (Z.shiftr (wrap16 (ds_bi_buf s)) 8)) 0) 0.
Proof.
  intros s. unfold tr_flush_bits, bi_flush, put_short.
  destruct (ds_bi_valid s =? 16); [right; right; reflexivity|].
  destruct (8 <=? ds_bi_valid s); [right; left; reflexivity | left; reflexivity].
Qed.

Definition ds_nobits (s : deflate_state) :=
  (ds_window s, ds_prev s, ds_head s, ds_strm s, ds_sizes s, ds_pending_out s, arr_len (ds_pending_buf s)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record DWF (ds : deflate_state) : Prop := {
  wf_wlen : arr_len (ds_window ds) = 2 * ds_w_size ds;
  wf_plen : arr_len (ds_prev ds) = ds_w_size ds;
  wf_hlen : arr_len (ds_head ds) = ds_hash_size ds;
  wf_blen : arr_len (ds_pending_buf ds) = ds_lit_bufsize ds * 4;
  wf_lbs : 1 <= ds_lit_bufsize ds < 2 ^ 16;
  wf_wsz : 512 <= ds_w_size ds <= 32768;
  wf_hsz : 1 <= ds_hash_size ds <= 65536;
  wf_ao : 0 <= cs_avail_out (ds_strm ds) < 2 ^ 32 }.

Section Walk.
Variable S : Z.
Variable p : ds_ptrs.
Variable zp : zs_ptrs.
Variable ds : deflate_state.
Variable flush : Z.
Variable sp : Z.
Local Notation W := (p_window p).
Local Notation PV := (p_prev p).
Local Notation HD := (p_head p).
Local Notation PB := (p_pending_buf p).
Local Notation strm := (p_strm p).
Local Notation INP := (zp_in zp).
Local Notation OUTB := (zp_out zp).
Local Notation ws := (ds_w_size ds).
Local Notation hs := (ds_hash_size ds).
Local Notation lbs := (ds_lit_bufsize ds).
Local Notation PBL := (ds_lit_bufsize ds * 4).
Local Notation ILEN := (arr_len (cs_input (ds_strm ds))).
Local Notation OLEN0 := (Z.of_nat (length (cs_out_rev (ds_strm ds)))).
Local Notation AV0 := (cs_avail_out (ds_strm ds)).
Local Notation SP := (sp - 96).

(* [comment removed for export] *)
Definition CST (w pv hd : arr) (st : cstrm) : Prop :=
  arr_len w = 2 * ws /\ arr_len pv = ws /\ arr_len hd = hs /\ cs_input st = cs_input (ds_strm ds)
  /\ Z.of_nat (length (cs_out_rev st)) + cs_avail_out st = OLEN0 + AV0
  /\ 0 <= cs_avail_out st /\ OLEN0 <= Z.of_nat (length (cs_out_rev st)).

(* [comment removed for export] *)
Inductive skind :=
  | KInsH | KBlockStart | KMatchLength | KStrstart | KLookahead | KInsert | KSymNext | KPending
  | KPendingOut (off : Z)            (* [comment removed for export] *)
  | KPb (i c' : Z)                   (* [comment removed for export] *)
  | KFc (t : tree_id) (i v' : Z)     (* [comment removed for export] *)
  | KPrev (i v' : Z) | KHead (i v' : Z)
  | KFrame.

End Walk.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition dfF (w hd fc fdc : arr) (f : nat) (x : Z) : Z :=
  match f with 0%nat => wb w x | 1%nat => pb hd x | 2%nat => pb fc x | 3%nat => pb fdc x | _ => 0 end.

Definition dfFB : list (nat * Z) := [(0%nat, 256); (1%nat, 65536); (2%nat, 65536); (3%nat, 65536)].

(* [comment removed for export] *)
Definition dfVB : bounds := [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 6)].

(* [comment removed for export] *)
Lemma mm16_8 : forall x, (x mod 65536) mod 256 = x mod 256.
Proof. intros x. change 65536 with (2 ^ 16). change 256 with (2 ^ 8). apply mod_pow2_mod_pow2. lia. Qed.
Lemma mm32_16 : forall x, (x mod 4294967296) mod 65536 = x mod 65536.
Proof. intros x. change 4294967296 with (2 ^ 32). change 65536 with (2 ^ 16). apply mod_pow2_mod_pow2. lia. Qed.
Lemma mm32_8 : forall x, (x mod 4294967296) mod 256 = x mod 256.
Proof. intros x. change 4294967296 with (2 ^ 32). change 256 with (2 ^ 8). apply mod_pow2_mod_pow2. lia. Qed.
Lemma mm16_16 : forall x, (x mod 65536) mod 65536 = x mod 65536.
Proof. intros x. apply Z.mod_mod. lia. Qed.
Lemma mm8_8 : forall x, (x mod 256) mod 256 = x mod 256.
Proof. intros x. apply Z.mod_mod. lia. Qed.
Lemma addm16 : forall a b, (a mod 65536 + b) mod 65536 = (a + b) mod 65536.
Proof. intros. apply Zplus_mod_idemp_l. Qed.
Lemma addm8 : forall a b, (a mod 256 + b) mod 256 = (a + b) mod 256.
Proof. intros. apply Zplus_mod_idemp_l. Qed.

