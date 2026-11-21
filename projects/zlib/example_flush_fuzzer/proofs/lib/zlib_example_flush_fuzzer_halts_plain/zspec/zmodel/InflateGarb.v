(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import InflateGarbBase InflateGarbFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section ArmsWP.
  Variable iv : ivariant.
  Variable flush : Z.







  Definition olen (w : iw) : Z := arr_len (ic_outbuf (w_c w)).
  Definition roomok (w : iw) : bool :=
    (0 <=? ir_put (w_r w)) && (0 <=? ir_left (w_r w)) && (ir_put (w_r w) + ir_left (w_r w) <=? olen w).

  Definition gLIT (w : iw) : bool :=
    (ir_left (w_r w) =? 0) || ((0 <=? ir_put (w_r w)) && (ir_put (w_r w) <? olen w)).


  Definition gCOPY (w : iw) : bool := roomok w && (0 <=? ir_have (w_r w)) && (0 <=? is_length (w_s w)).


  Definition mstep (win : arr) (st : arr * Z * fromptr * Z) : bool * (arr * Z * fromptr * Z) :=
    let '(ob, put, from, copy) := st in
    let v := match from with FWin i => arr_get win i | FOut i => arr_get ob i end in
    let ob := arr_set ob put v in
    let copy := wrap32 (copy - 1) in
    (negb (copy =? 0), (ob, put + 1, from_succ from, copy)).





  Definition gMATCH (w : iw) : bool :=
    let s := w_s w in let r := w_r w in
    (ir_left r =? 0)
    || (roomok w && ((wrap32 (ir_out r - ir_left r) <? is_offset s)
                     || ((1 <=? is_offset s) && (is_offset s <=? ir_put r)))).


  Definition gCHECK (w : iw) : bool :=
    let s := w_s w in let r := w_r w in
    (is_wrap s =? 0) || (wrap32 (ir_out r - ir_left r) <=? ir_put r).





  Ltac keeps_refl :=
    intros ?w0 ?a0 ?w1 ?C0 ?E0;
    first [ injection E0
          | unfold add_back, set_back, aux in E0; destruct (iv_aux iv); injection E0 ];
    intros <- _; exact C0.

  Definition gCOPY_ : iw -> bool := gCOPY.

  Definition gSTORED (w : iw) : bool := roomok w && (0 <=? ir_have (w_r w)).


  Definition cp0 (r : iregs) : Z := wrap32 (ir_out r - ir_left r).

  Definition dentry_ok (e : Z) : bool := negb (Z.land (code_op e) 64 =? 0) || (1 <=? code_val e).
  Definition dtable_ok (s : inflate_state) : bool :=
    (0 <=? is_distbits s) &&
    forallb (fun i => let e := code_at s (is_distcode s) i in
               if Z.land (code_op e) 240 =? 0
               then forallb (fun j => dentry_ok (code_at s (is_distcode s) (code_val e + j))) (zupto (2 ^ code_op e))
               else dentry_ok e)
            (zupto (2 ^ is_distbits s)).


  Definition gDISTEXT (w : iw) : bool :=
    (ir_left (w_r w) =? 0)
    || (roomok w && (cp0 (w_r w) <=? ir_put (w_r w)) && (1 <=? is_offset (w_s w)) && (is_offset (w_s w) <=? 65535)
        && (0 <=? is_extra (w_s w)) && (is_extra (w_s w) <=? 16)).


  Definition gDIST (w : iw) : bool :=
    (ir_left (w_r w) =? 0) || (roomok w && (cp0 (w_r w) <=? ir_put (w_r w)) && dtable_ok (w_s w)).





  Ltac keeps_prim :=
    intros ?w0 ?a0 ?w1 ?C0 ?E0;
    first [ injection E0
          | unfold add_back, set_back, aux in E0; destruct (iv_aux iv); injection E0 ];
    intros <- _; exact C0.
  Ltac keeps_step :=
    lazymatch goal with
    | |- keeps _ (abind _ _) => apply keeps_bind; [|intros]
    | |- keeps _ (if _ then _ else _) => apply keeps_if
    | |- keeps _ (NEEDBITS _) => apply keeps_NEEDBITS; unfold frame_chk; intros ?x ?x1 ?X1 ?X2 ?X3 ?X4 ?X5
    | |- keeps _ (DECODE1 _ _) => apply keeps_DECODE_k; unfold frame_chk; intros ?x ?x1 ?X1 ?X2 ?X3 ?X4 ?X5
    | |- keeps _ (DECODE2 _ _) => apply keeps_DECODE_k; unfold frame_chk; intros ?x ?x1 ?X1 ?X2 ?X3 ?X4 ?X5
    | |- keeps _ (DECODE_k _ _ _ _) => apply keeps_DECODE_k; unfold frame_chk; intros ?x ?x1 ?X1 ?X2 ?X3 ?X4 ?X5
    | |- keeps _ _ => keeps_prim
    end.


  Definition gLENEXT : iw -> bool := gDIST.

  (* zlib 1.4 (smodel14-r1's LEN row): the fast path also needs bits < 8 *)
  Definition fastcond (r : iregs) : bool := iv_fast iv && (6 <=? ir_have r) && (258 <=? ir_left r) && (ir_bits r <? 8).

  Definition gLEN (w : iw) : bool := if fastcond (w_r w) then gFAST w else gDIST w.


  Definition gLEN_ (w : iw) : bool := after (set_mode LEN) (fun _ => gLEN) w.



  Definition gCODELENS : iw -> bool :=
    after (codelens_while 321%nat) (fun _ =>
    after (gs (fun s => s)) (fun s =>
    if is_mode s =? BAD then ctrue
    else if arr_get (is_lens s) 256 =? 0 then ctrue
    else
      let '(ret, tbl, next, lenbits, work) :=
        inflate_table LENS (is_lens s) 0 (is_nlen s) (is_codes s) 0 9 (is_work s) in
      after (us (fun s => iset_work (iset_lenbits (iset_next (iset_lencode (iset_codes s tbl) (CDyn 0)) next) lenbits) work)) (fun _ =>
      after (ur (fun r => irset_ret r ret)) (fun _ =>
      if negb (ret =? 0) then ctrue
      else
        after (gs (fun s => s)) (fun s =>
        let '(ret, tbl, next, distbits, work) :=
          inflate_table DISTS (is_lens s) (is_nlen s) (is_ndist s) (is_codes s) (is_next s) 6 (is_work s) in
        after (us (fun s => iset_work (iset_distbits (iset_next (iset_distcode (iset_codes s tbl) (CDyn (is_next s))) next) distbits) work)) (fun _ =>
        after (ur (fun r => irset_ret r ret)) (fun _ =>
        if negb (ret =? 0) then ctrue
        else after (set_mode LEN_) (fun _ => if iv_flush_exits iv && (flush =? Z_TREES) then ctrue else gLEN_)))))))).

  Ltac syn_step :=
    lazymatch goal with
    | |- WP (after ?m _) (abind ?m _) => apply WP_bind0l; [wp0 | intros]
    | |- WP (fun w => after ?m _ w) (abind ?m _) => apply WP_bind0l; [wp0 | intros]
    | |- WP ctrue _ => apply WP0_WP; wp0
    | |- WP (fun _ => true) _ => apply WP0_WP; wp0
    | |- WP (if ?c then _ else _) (if ?c then _ else _) => destruct c
    | |- WP (fun w => (if ?c then _ else _) w) (if ?c then _ else _) => destruct c
    | |- WP (match ?x with _ => _ end) (match ?x with _ => _ end) => destruct x
    | |- WP _ (match ?x with _ => _ end) => destruct x
    end.


  Definition gLENLENS : iw -> bool :=
    after (lenlens_while1 19%nat) (fun _ =>
    after (lenlens_while2 19%nat) (fun _ =>
    after (gs (fun s => s)) (fun s =>
    let '(ret, tbl, next, lenbits, work) := inflate_table CODES (is_lens s) 0 19 (is_codes s) 0 7 (is_work s) in
    (* zlib 1.4 (smodel14-r1's LENLENS row): distcode := CDyn 0 with lencode *)
    after (us (fun s => iset_work (iset_lenbits (iset_next (iset_lencode (iset_distcode (iset_codes s tbl) (CDyn 0)) (CDyn 0)) next) lenbits) work)) (fun _ =>
    after (ur (fun r => irset_ret r ret)) (fun _ =>
    if negb (ret =? 0) then ctrue
    else after (us (fun s => iset_have s 0)) (fun _ => after (set_mode CODELENS) (fun _ => gCODELENS))))))).


  Definition gTABLE : iw -> bool :=
    after (NEEDBITS 14) (fun _ =>
    after (BITS 5) (fun v => after (us (fun s => iset_nlen s (v + 257))) (fun _ => after (DROPBITS 5) (fun _ =>
    after (BITS 5) (fun v => after (us (fun s => iset_ndist s (v + 1))) (fun _ => after (DROPBITS 5) (fun _ =>
    after (BITS 4) (fun v => after (us (fun s => iset_ncode s (v + 4))) (fun _ => after (DROPBITS 4) (fun _ =>
    after (gs (fun s => s)) (fun s =>
    if (286 <? is_nlen s) || (30 <? is_ndist s) then ctrue
    else after (us (fun s => iset_have s 0)) (fun _ => after (set_mode LENLENS) (fun _ => gLENLENS))))))))))))).





  Definition gsel (m : Z) : iw -> bool :=
    if m =? HEAD then ctrue
    else if m =? FLAGS then ctrue
    else if m =? TIME then ctrue
    else if m =? OS then ctrue
    else if m =? EXLEN then ctrue
    else if m =? EXTRA then ctrue
    else if m =? NAME then ctrue
    else if m =? COMMENT then ctrue
    else if m =? HCRC then ctrue
    else if m =? DICTID then ctrue
    else if m =? DICT then ctrue
    else if m =? TYPE then ctrue
    else if m =? TYPEDO then ctrue
    else if m =? STORED then gSTORED
    else if m =? COPY_ then gCOPY_
    else if m =? COPY then gCOPY
    else if m =? TABLE then gTABLE
    else if m =? LENLENS then gLENLENS
    else if m =? CODELENS then gCODELENS
    else if m =? LEN_ then gLEN_
    else if m =? LEN then gLEN
    else if m =? LENEXT then gLENEXT
    else if m =? DIST then gDIST
    else if m =? DISTEXT then gDISTEXT
    else if m =? MATCH then gMATCH
    else if m =? LIT then gLIT
    else if m =? CHECK then gCHECK
    else ctrue.
  Definition gok (w : iw) : bool := gsel (is_mode (w_s w)) w.




  Fixpoint garb_okN (n : nat) (w : iw) : bool :=
    match n with
    | O => true
    | S n' => gok w && match dispatch iv flush w with
                       | ARun _ w' => garb_okN n' w'
                       | _ => true
                       end
    end.
  Definition gfuel (w : iw) : Z := 64 * (ic_avail_in (w_c w) + ic_avail_out (w_c w) + 64).
  Definition gstep (w : iw) : iw + (istop * iw) :=
    match dispatch iv flush w with
    | ARun _ w' => inl w'
    | ALeave w' => inr (SLeave, w')
    | ARet rc w' => inr (SRet rc, w')
    end.

  Lemma inf_loop_iter : forall w,
    inf_loop iv flush w = match iterK_nat (Z.to_nat (gfuel w)) gstep w with inl w' => (SLeave, w') | inr b => b end.
  Proof. intros w. unfold inf_loop, gfuel, gstep. rewrite iterZ_nat. reflexivity. Qed.


  Lemma iterK_gstep_S : forall n w, iterK_nat (S n) gstep w =
    match dispatch iv flush w with
    | ARun _ w' => iterK_nat n gstep w'
    | ALeave w' => inr (SLeave, w')
    | ARet rc w' => inr (SRet rc, w')
    end.
  Proof. intros n w. cbn [iterK_nat]. unfold gstep at 1. destruct (dispatch iv flush w) as [? ?|?|? ?]; reflexivity. Qed.


End ArmsWP.

