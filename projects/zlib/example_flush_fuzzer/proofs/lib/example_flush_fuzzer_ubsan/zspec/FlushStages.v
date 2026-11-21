(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import
  Prog ZIface DeflateState Deflate InflateState Inflate InflateSync HarnessKit HarnessFacts HarnessSmallStages HarnessSmallFacts HarnessFlush HarnessFlushFacts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition KI : Z := 7.
Definition KW : Z := 8.
Definition O4 : horacle := ocanon [].

Definition fl_clen (n : Z) : Z := wrap64 (100 + 2 * compressBound_m n).
Definition fl_c0 (n : Z) : czs := mkCZS 0 3 0 (wrap32 (fl_clen n)) (zr_strm zr0).
Definition fl_zc1 (d : list Z) : ZCall := fst (cz_call (fl_c0 (zlength d)) (arr_of_list d)).
Definition fl_call1 (d : list Z) : deflate_state * ZRet := deflate_m ds0 (fl_zc1 d) Z_FULL_FLUSH.
Definition fl_s1 (d : list Z) : deflate_state := fst (fl_call1 d).
Definition fl_r1 (d : list Z) : ZRet := snd (fl_call1 d).
Definition fl_ret1 (d : list Z) : czs * arr * bool := cz_ret (fl_c0 (zlength d)) (fl_r1 d) (zero_buf (fl_clen (zlength d))).
Definition fl_c1 (d : list Z) : czs := fst (fst (fl_ret1 d)).
Definition fl_compr1 (d : list Z) : arr := snd (fst (fl_ret1 d)).
Definition fl_compr1' (d : list Z) : arr := arr_set (fl_compr1 d) 3 (wrap8 (arr_get (fl_compr1 d) 3 + 1)).
Definition fl_c1' (d : list Z) : czs := cz_set_avail_in (fl_c1 d) (wrap32 (wrap32 (zlength d) - 3)).
Definition fl_zc2 (d : list Z) : ZCall := fst (cz_call (fl_c1' d) (arr_of_list d)).
Definition fl_call2 (d : list Z) : deflate_state * ZRet := deflate_m (fl_s1 d) (fl_zc2 d) Z_FINISH.
Definition fl_s2 (d : list Z) : deflate_state := fst (fl_call2 d).
Definition fl_r2 (d : list Z) : ZRet := snd (fl_call2 d).
Definition fl_ret2 (d : list Z) : czs * arr * bool := cz_ret (fl_c1' d) (fl_r2 d) (fl_compr1' d).
Definition fl_c2 (d : list Z) : czs := fst (fst (fl_ret2 d)).
Definition fl_compr2 (d : list Z) : arr := snd (fst (fl_ret2 d)).
Definition fl_dend (d : list Z) : Z * list hevent := dend_p (fl_s2 d).
Definition fl_busy (d : list Z) : bool := negb (fst (fl_dend d) =? Z_OK).
Definition fl_tot (d : list Z) : Z := zs_total_out (cz_z (fl_c2 d)).
Definition fl_ds1 (d : list Z) : deflate_state := set_strm ds0 (cstrm_of_call (fl_zc1 d)).
Definition fl_ds2 (d : list Z) : deflate_state := set_strm (fl_s1 d) (cstrm_of_call (fl_zc2 d)).

Lemma fl_call1_core : forall d,
  fl_call1 d = (let '(s, rc) := deflate_core (fl_ds1 d) Z_FULL_FLUSH in (s, zret_of_cs (ds_strm s) rc)).
Proof. intros d. reflexivity. Qed.
Lemma fl_call2_core : forall d,
  fl_call2 d = (let '(s, rc) := deflate_core (fl_ds2 d) Z_FINISH in (s, zret_of_cs (ds_strm s) rc)).
Proof. intros d. reflexivity. Qed.


Definition fl_i0 : inflate_state := is0 KI.
Definition fl_iz0 : zstrm := iz0 KI.
Definition fl_ic0 (n : Z) : czs := mkCZS 0 2 0 (wrap32 n) fl_iz0.
Definition fl_izc1 (c : arr) (n : Z) : ZCall := fst (cz_call (fl_ic0 n) c).
Definition fl_icall1 (c : arr) (n : Z) : (inflate_state * ZRet) * option Z := inflate_p ivar_ref (hans O4 KW) fl_i0 (fl_izc1 c n) Z_NO_FLUSH.
Definition fl_is1 (c : arr) (n : Z) : inflate_state := fst (fst (fl_icall1 c n)).
Definition fl_ir1 (c : arr) (n : Z) : ZRet := snd (fst (fl_icall1 c n)).
Definition fl_iasked1 (c : arr) (n : Z) : option Z := snd (fl_icall1 c n).
Definition fl_iret1 (c : arr) (n : Z) : czs * arr * bool := cz_ret (fl_ic0 n) (fl_ir1 c n) (zero_buf n).
Definition fl_ic1 (c : arr) (n : Z) : czs := fst (fst (fl_iret1 c n)).
Definition fl_unc1 (c : arr) (n : Z) : arr := snd (fst (fl_iret1 c n)).
Definition fl_ic1' (c : arr) (clen n : Z) : czs := cz_set_avail_in (fl_ic1 c n) (wrap32 (wrap32 clen - 2)).
Definition fl_izc2 (c : arr) (clen n : Z) : ZCall := fst (cz_call (fl_ic1' c clen n) c).
Definition fl_sync (c : arr) (clen n : Z) : inflate_state * ZRet := inflateSync_m ivar_ref (fl_is1 c n) (fl_izc2 c clen n).
Definition fl_is2 (c : arr) (clen n : Z) : inflate_state := fst (fl_sync c clen n).
Definition fl_ir2 (c : arr) (clen n : Z) : ZRet := snd (fl_sync c clen n).
Definition fl_iret2 (c : arr) (clen n : Z) : czs * arr * bool := cz_ret (fl_ic1' c clen n) (fl_ir2 c clen n) (fl_unc1 c n).
Definition fl_ic2 (c : arr) (clen n : Z) : czs := fst (fst (fl_iret2 c clen n)).
Definition fl_izc3 (c : arr) (clen n : Z) : ZCall := fst (cz_call (fl_ic2 c clen n) c).
Definition fl_icall3 (c : arr) (clen n : Z) : (inflate_state * ZRet) * option Z :=
  inflate_p ivar_ref (hans O4 (hstep_n KW (fl_iasked1 c n))) (fl_is2 c clen n) (fl_izc3 c clen n) Z_FINISH.
Definition fl_is3 (c : arr) (clen n : Z) : inflate_state := fst (fst (fl_icall3 c clen n)).
Definition fl_ir3 (c : arr) (clen n : Z) : ZRet := snd (fst (fl_icall3 c clen n)).
Definition fl_iasked3 (c : arr) (clen n : Z) : option Z := snd (fl_icall3 c clen n).

