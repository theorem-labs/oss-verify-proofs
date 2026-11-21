(** * Bridge.Infl.IInv — group I (inflate): the loop invariant and the per-trip obligation.

    the tracker plan item 2.2, part C, group I.  Owned by the inflate group.

    The lead's [IRelInfl.iw_rel] relates S5's loop state ([IS.iw]: state + call + registers)
    to RT's ([RI.InfSt]).  A trip of S5's [InflateArms.dispatch] and a trip of RT's
    [Inflate.inf_step] are compared under [inv] = [icore] + [imode]:

    - [icore]: [iw_rel], plus the facts every arm needs and that hold for the whole of the
      harness's one uncompress call (windowBits 15, fresh state, no dictionary, the window
      never allocated inside the call, the C's unsigned counters never wrap);
    - [imode]: what the next trip needs, by RT mode (the decoding tables for the block
      modes, ranges of [length]/[offset]).

    [step_ok] is the obligation of one trip.  Only the outcomes a successful call can take
    are compared: an [InfCont] into any mode but BAD, and an [InfLeave] that returns
    [Z_STREAM_END].  That is enough because RT's [zr_inflate] is [Some] only at
    [Z_STREAM_END]: a BAD state always leaves with [Z_DATA_ERROR], every other [InfLeave]
    carries [q_ret = Z_OK], and every [InfRet] code differs from [Z_STREAM_END].

    The decoding tables are compared through [tview]: on every index a decode can form, S5's
    packed table is RT's [code_enc], and the entries have the shape [inflate_table] builds
    (bits within the root, one level of sub-tables, length codes at most 258). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState InflateFast InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base ZBitsIn Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module IA := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.InflateArms.
Module RBa := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.Base.

(** The flush both models are called with in the harness's uncompress call. *)
Definition FL : Z := ZIface.Z_NO_FLUSH.

(* ------------------------------------------------------------------------- *)
(* 1.  Decoding tables                                                       *)
(* ------------------------------------------------------------------------- *)

(** An RT table entry with byte-sized [op]/[bits] and a short [val], so that S5's packed
    form [code_enc] decodes back to it. *)
Definition code_rng (e : RBa.Code) : Prop :=
  0 <= RBa.c_op e < 256 /\ 0 <= RBa.c_bits e < 256 /\ 0 <= RBa.c_val e < 65536.

Inductive tkind : Set := KCodes | KLens | KDists.

(** Does a root entry point at a sub-table?  LEN tests [op && (op & 0xf0) == 0]
    ([inflate.c:1041]); DIST tests [(op & 0xf0) == 0] ([:1090]); CODELENS never follows
    one (a code-length table has no sub-tables). *)
Definition tsub (k : tkind) (op : Z) : bool :=
  match k with
  | KDists => Z.land op 240 =? 0
  | _ => negb (op =? 0) && (Z.land op 240 =? 0)
  end.

(** Entry facts by table kind, all true of [inflate_table]'s output (ops 0, 16..29, 64, 96,
    the links 1..15, and two invalid length slots with bit 64 set):
    - a length code is at most 258 with at most 5 extra bits, a distance code at most 32768
      with at most 13, and no distance entry has [op = 0] (so [inflate_fast] never writes past
      the output buffer and never reads past the 6 input bytes [in < last] guarantees);
    - every entry [inffast.c] chains on ([op & 16 = 0], [op & 64 = 0], and [op <> 0] for
      lengths) is one the slow path also treats as a link ([op & 0xf0 = 0]). *)
Definition tent (k : tkind) (e : Z) : Prop :=
  let op := IS.code_op e in
  match k with
  | KCodes => True
  | KLens => (Z.land op 16 <> 0 -> Z.land op 15 <= 5 /\ IS.code_val e + 2 ^ Z.land op 15 <= 259)
             /\ (op <> 0 -> Z.land op 16 = 0 -> Z.land op 64 = 0 -> Z.land op 240 = 0)
  | KDists => op <> 0
              /\ (Z.land op 16 <> 0 ->
                    Z.land op 15 <= 13 /\ 1 <= IS.code_val e /\ IS.code_val e + 2 ^ Z.land op 15 <= 32769)
              /\ (Z.land op 16 = 0 -> Z.land op 64 = 0 -> Z.land op 240 = 0)
  end.

(** [f] is S5's table as a decode reads it ([IS.code_at s p], indices relative to the
    table's base), [g] RT's ([RI.tbl_of st r]).  [root] is [lenbits]/[distbits]. *)
Definition tview (f : Z -> Z) (g : Z -> RBa.Code) (root : Z) (k : tkind) : Prop :=
  1 <= root <= 15 /\
  forall x, 0 <= x < 2 ^ root ->
    f x = RBa.code_enc (g x) /\ code_rng (g x) /\
    IS.code_bits (f x) <= root /\ tent k (f x) /\
    (tsub k (IS.code_op (f x)) = true ->
       IS.code_bits (f x) = root /\ 1 <= IS.code_op (f x) /\ root + IS.code_op (f x) <= 15 /\
       forall y, 0 <= y < 2 ^ IS.code_op (f x) ->
         let z := IS.code_val (f x) + y in
         f z = RBa.code_enc (g z) /\ code_rng (g z) /\
         IS.code_bits (f z) <= 15 - root /\ tsub k (IS.code_op (f z)) = false /\ tent k (f z)).

(** The two tables of a Huffman block (LEN_ .. LIT). *)
Definition tviews_blk (w : IS.iw) (q : RI.InfSt) : Prop :=
  let s := IS.w_s w in let st := RI.q_st q in
  tview (IS.code_at s (IS.is_lencode s)) (RI.tbl_of st (RI.t_lencode (RI.s_tab st))) (IS.is_lenbits s) KLens
  /\ tview (IS.code_at s (IS.is_distcode s)) (RI.tbl_of st (RI.t_distcode (RI.s_tab st))) (IS.is_distbits s) KDists.

(* ------------------------------------------------------------------------- *)
(* 2.  The invariant                                                         *)
(* ------------------------------------------------------------------------- *)

Definition icore (w : IS.iw) (q : RI.InfSt) : Prop :=
  let s := IS.w_s w in let c := IS.w_c w in let r := IS.w_r w in
  let st := RI.q_st q in let b := RI.q_br q in let o := RI.q_ob q in
  iw_rel w q
  (* between trips nothing has set [ret]: only DONE and BAD do, and both leave *)
  /\ RI.q_ret q = RBa.Z_OK
  (* the accumulator holds exactly [bits] bits, at most 39 ([NEEDBITS(32)] from 31), all of
     them read from input already consumed *)
  /\ 0 <= IS.ir_bits r <= 39 /\ 0 <= IS.ir_hold r < 2 ^ IS.ir_bits r
  /\ IS.ir_bits r <= 8 * IS.ir_next r
  (* the input agrees at every nonnegative index (past its end both models read 0), and is bytes *)
  /\ (forall i, 0 <= i -> arr_get (IS.ic_input c) i = RB.br_in b i /\ 0 <= RB.br_in b i < 256)
  (* the output buffer agrees on its unwritten tail too (both start zeroed) *)
  /\ arr_rel (IS.ic_outbuf c) (RI.o_buf o) (IS.ir_put r) (IS.ir_put r + IS.ir_left r)
  (* the C's unsigned counters never wrap in the harness's call *)
  /\ IS.ir_put r + IS.ir_left r < 2 ^ 31 /\ IS.ir_next r + IS.ir_have r < 2 ^ 32
  (* [out] is the entry snapshot of [avail_out] until CHECK; nothing is counted out yet *)
  /\ IS.ir_out r = IS.ir_put r + IS.ir_left r
  /\ IS.ic_total_out c = 0 /\ IS.is_total s = 0
  (* windowBits 15, no dictionary, [sane], the window never allocated inside the call *)
  /\ IS.is_wrap s = 5 /\ IS.is_wbits s = 15 /\ IS.is_havedict s = 0 /\ IS.is_sane s = 1
  /\ IS.is_wsize s = 0 /\ IS.is_whave s = 0 /\ IS.is_wnext s = 0 /\ IS.is_window_blk s = None
  (* past the header: a zlib stream (no gzip flags) and the running Adler-32 still at its start *)
  /\ (IS.is_mode s <> IS.HEAD -> IS.is_flags s = 0 /\ IS.is_check s = 1)
  (* RT's table memory holds packed-[code]-ranged entries *)
  /\ (forall i, code_rng (RI.t_codes (RI.s_tab st) i))
  (* RT's window and output buffer hold bytes (both start zeroed and only bytes are written):
     the Adler-32 fold at CHECK needs them *)
  /\ (forall i, 0 <= RI.w_win (RI.s_win st) i < 256)
  /\ (forall i, 0 <= RI.o_buf o i < 256).

(** Bytes stay bytes under RT's output writes. *)
Definition zbytes (a : RBa.zarr) : Prop := forall i, 0 <= a i < 256.

Lemma zbytes_zset : forall a k v, zbytes a -> 0 <= v < 256 -> zbytes (RBa.zset a k v).
Proof.
  intros a k v Ha Hv i. unfold RBa.zset. destruct (Z.eqb i k); [exact Hv | apply Ha].
Qed.

Lemma zbytes_zcopy : forall n dst di src si, zbytes dst -> (forall i, si <= i -> 0 <= src i < 256) ->
  zbytes (RI.zcopy n dst di src si).
Proof.
  induction n as [|n IH]; intros dst di src si Hd Hs; cbn [RI.zcopy]; [exact Hd|].
  apply IH; [apply zbytes_zset; [exact Hd | apply Hs; lia] | intros i Hi; apply Hs; lia].
Qed.

Lemma zbytes_ob_copyn : forall n win o r, zbytes win -> zbytes (RI.o_buf o) ->
  zbytes (RI.o_buf (RI.ob_copyn n win o r)).
Proof.
  induction n as [|n IH]; intros win o r Hw Ho; cbn [RI.ob_copyn]; [exact Ho|].
  apply IH; [exact Hw|]. unfold RI.ob_write. cbn [RI.o_buf].
  apply zbytes_zset; [exact Ho|]. destruct r as [i|i]; cbn [RI.os_read]; [apply Hw | apply Ho].
Qed.

(** What the next trip needs, by RT mode.  These are the modes a trip of a successful call
    can end in (and the two entry-only modes TYPEDO and COPY_); any other mode is [False]. *)
Definition imode (w : IS.iw) (q : RI.InfSt) : Prop :=
  let s := IS.w_s w in
  match RI.q_mode q with
  | RI.M_HEAD | RI.M_DICTID | RI.M_TYPE | RI.M_TYPEDO | RI.M_STORED | RI.M_TABLE | RI.M_CHECK => True
  | RI.M_COPY_ | RI.M_COPY => 0 <= IS.is_length s < 65536
  | RI.M_LEN_ | RI.M_LEN | RI.M_LIT => tviews_blk w q
  | RI.M_MATCH => tviews_blk w q /\ 0 <= IS.is_length s <= 258 /\ 1 <= IS.is_offset s <= 32768
  | _ => False
  end.

Definition inv (w : IS.iw) (q : RI.InfSt) : Prop := icore w q /\ imode w q.

(** The state a successful call leaves the loop in (DONE, after CHECK): what [inf_leave]
    needs to return RT's bytes, [Z_STREAM_END] and the right [total_out]. *)
Definition ifin (w : IS.iw) (q : RI.InfSt) : Prop :=
  let c := IS.w_c w in let r := IS.w_r w in
  iw_rel w q
  /\ IS.ir_out r = IS.ir_left r
  /\ IS.ic_total_out c = IS.ir_put r
  /\ IS.is_wsize (IS.w_s w) = 0
  /\ IS.ir_put r + IS.ir_left r < 2 ^ 31.

(* ------------------------------------------------------------------------- *)
(* 3.  One trip                                                              *)
(* ------------------------------------------------------------------------- *)

(** The obligation of one trip (or of one arm, entered by fallthrough): S5's result [sr]
    against RT's [rr], on the outcomes a successful call can take; and a trip never
    returns [Z_STREAM_END] past the epilogue (the [InfRet] codes are NEED_DICT, MEM and
    STREAM_ERROR). *)
Definition step_ok (sr : IS.ares unit) (rr : RI.InfStep) : Prop :=
  match rr with
  | RI.InfCont q' => RI.q_mode q' <> RI.M_BAD -> exists w', sr = IS.ARun tt w' /\ inv w' q'
  | RI.InfLeave q' => RI.q_ret q' = RBa.Z_STREAM_END -> exists w', sr = IS.ALeave w' /\ ifin w' q'
  | RI.InfRet _ rc => rc <> RBa.Z_STREAM_END
  | RI.InfDead _ | RI.InfFuel => True
  end.
