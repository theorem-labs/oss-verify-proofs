(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import AdlerModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint allz (lo : Z) (n : nat) (f : Z -> bool) : bool :=
  match n with
  | O => true
  | S k => f lo && allz (lo + 1) k f
  end.

Lemma allz_spec : forall n lo f, allz lo n f = true -> forall i, lo <= i < lo + Z.of_nat n -> f i = true.
Proof.
  induction n as [|n IH]; intros lo f H i Hi; [cbn in Hi; lia|].
  cbn [allz] in H. apply andb_prop in H as [H0 H1].
  destruct (Z.eq_dec i lo) as [->|NE]; [exact H0|].
  apply (IH (lo + 1) f H1). rewrite Nat2Z.inj_succ in Hi. lia.
Qed.

Lemma allz_range : forall lo hi f, allz lo (Z.to_nat (hi - lo)) f = true ->
  forall i, lo <= i < hi -> f i = true.
Proof.
  intros lo hi f H i Hi. apply (allz_spec _ _ _ H). rewrite Z2Nat.id by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sym_shape_b (ty : codetype) (root x e s : Z) : bool :=
  (code_op e =? fst (sym_entry ty s)) && (code_val e =? snd (sym_entry ty s)) &&
  (((x <? 2 ^ root) && (1 <=? code_bits e) && (code_bits e <=? root) && (code_bits e <=? 15))
   || ((2 ^ root <=? x) && (1 <=? code_bits e) && (root + code_bits e <=? 15))).

Definition anyz (lo : Z) (n : nat) (f : Z -> bool) : bool := negb (allz lo n (fun s => negb (f s))).

Definition entry_shape_b (ty : codetype) (root used x e : Z) : bool :=
  anyz 0 (Z.to_nat (nsyms ty)) (sym_shape_b ty root x e)
  || ((x <? 2 ^ root) && (code_bits e =? root) && (1 <=? code_op e) && (code_op e <=? 15 - root)
      && (2 ^ root <=? code_val e) && (code_val e + 2 ^ code_op e <=? used))
  || ((code_op e =? 64) && (code_bits e =? 1) && (code_val e =? 0) && (root =? 1)).

Lemma sym_shape_b_sound : forall ty root used x e s,
  0 <= s < nsyms ty -> 0 <= root -> sym_shape_b ty root x e s = true -> entry_shape ty root used x e.
Proof.
  intros ty root used x e s Hs Hr H. unfold sym_shape_b in H.
  apply andb_prop in H as [H HB]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.eqb_eq in H2.
  left. apply Bool.orb_prop in HB. destruct HB as [HB|HB].
  - apply andb_prop in HB as [HB B4]. apply andb_prop in HB as [HB B3]. apply andb_prop in HB as [B1 B2].
    apply Z.ltb_lt in B1. apply Z.leb_le in B2. apply Z.leb_le in B3. apply Z.leb_le in B4.
    exists s, (code_bits e). split; [exact Hs|]. split; [lia|]. split; [exact H1|]. split; [exact H2|].
    left. split; [exact B1|]. split; [exact B3|reflexivity].
  - apply andb_prop in HB as [HB B3]. apply andb_prop in HB as [B1 B2].
    apply Z.leb_le in B1. apply Z.leb_le in B2. apply Z.leb_le in B3.
    exists s, (root + code_bits e). split; [exact Hs|]. split; [lia|]. split; [exact H1|]. split; [exact H2|].
    right. split; [exact B1|]. split; [lia|lia].
Qed.

Lemma allz_negb_false : forall n lo f, allz lo n (fun s => negb (f s)) = false ->
  exists s, lo <= s < lo + Z.of_nat n /\ f s = true.
Proof.
  induction n as [|n IH]; intros lo f H; [discriminate H|].
  cbn [allz] in H. apply Bool.andb_false_iff in H. destruct H as [H|H].
  - exists lo. split; [rewrite Nat2Z.inj_succ; lia|]. destruct (f lo); [reflexivity|discriminate H].
  - destruct (IH _ _ H) as [s [Hs Hf]]. exists s. split; [rewrite Nat2Z.inj_succ; lia|exact Hf].
Qed.

Lemma anyz_true : forall n lo f, anyz lo n f = true -> exists s, lo <= s < lo + Z.of_nat n /\ f s = true.
Proof. intros n lo f H. unfold anyz in H. apply Bool.negb_true_iff in H. exact (allz_negb_false n lo f H). Qed.

Lemma entry_shape_b_sound : forall ty root used x e,
  0 <= root -> entry_shape_b ty root used x e = true -> entry_shape ty root used x e.
Proof.
  intros ty root used x e Hr H. unfold entry_shape_b in H.
  assert (Hn : 0 <= nsyms ty) by (destruct ty; cbn; lia).
  apply Bool.orb_prop in H. destruct H as [H|H]; [apply Bool.orb_prop in H; destruct H as [H|H]|].
  - destruct (anyz_true _ _ _ H) as [s [Hs Hf]]. rewrite Z2Nat.id in Hs by exact Hn.
    exact (sym_shape_b_sound ty root used x e s ltac:(lia) Hr Hf).
  - apply andb_prop in H as [H C6]. apply andb_prop in H as [H C5]. apply andb_prop in H as [H C4].
    apply andb_prop in H as [H C3]. apply andb_prop in H as [C1 C2].
    apply Z.ltb_lt in C1. apply Z.eqb_eq in C2. apply Z.leb_le in C3. apply Z.leb_le in C4.
    apply Z.leb_le in C5. apply Z.leb_le in C6.
    right; left. repeat split; assumption.
  - apply andb_prop in H as [H C4]. apply andb_prop in H as [H C3]. apply andb_prop in H as [C1 C2].
    apply Z.eqb_eq in C1. apply Z.eqb_eq in C2. apply Z.eqb_eq in C3. apply Z.eqb_eq in C4.
    right; right. repeat split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cell_ok (ty : codetype) (root used x e : Z) : Prop :=
  entry_shape ty root used x e
  \/ (code_op e = 64 /\ ((x < 2 ^ root /\ 1 <= code_bits e <= root) \/ (2 ^ root <= x /\ 1 <= code_bits e <= 15 - root))).
Definition cell_ok_b (ty : codetype) (root used x e : Z) : bool :=
  entry_shape_b ty root used x e
  || ((code_op e =? 64) && (((x <? 2 ^ root) && (1 <=? code_bits e) && (code_bits e <=? root))
                            || ((2 ^ root <=? x) && (1 <=? code_bits e) && (code_bits e <=? 15 - root)))).
Lemma cell_ok_b_sound : forall ty root used x e, 0 <= root -> cell_ok_b ty root used x e = true -> cell_ok ty root used x e.
Proof.
  intros ty root used x e Hr H. unfold cell_ok_b in H. apply Bool.orb_prop in H. destruct H as [H|H].
  - left. exact (entry_shape_b_sound ty root used x e Hr H).
  - right. apply andb_prop in H as [A B]. apply Z.eqb_eq in A. split; [exact A|].
    apply Bool.orb_prop in B. destruct B as [B|B].
    + apply andb_prop in B as [B B3]. apply andb_prop in B as [B1 B2].
      apply Z.ltb_lt in B1. apply Z.leb_le in B2. apply Z.leb_le in B3. left. lia.
    + apply andb_prop in B as [B B3]. apply andb_prop in B as [B1 B2].
      apply Z.leb_le in B1. apply Z.leb_le in B2. apply Z.leb_le in B3. right. lia.
Qed.

Definition rep_root (get : Z -> Z) (root : Z) : Prop :=
  forall x x', 0 <= x < 2 ^ root -> 0 <= x' < 2 ^ root ->
    1 <= code_bits (get x) <= root -> x' mod 2 ^ code_bits (get x) = x mod 2 ^ code_bits (get x) ->
    get x' = get x.
Definition rep_sub (get : Z -> Z) (root : Z) : Prop :=
  forall x, 0 <= x < 2 ^ root -> 1 <= code_op (get x) <= 15 ->
    forall y y', 0 <= y < 2 ^ code_op (get x) -> 0 <= y' < 2 ^ code_op (get x) ->
      1 <= code_bits (get (code_val (get x) + y)) ->
      y' mod 2 ^ code_bits (get (code_val (get x) + y)) = y mod 2 ^ code_bits (get (code_val (get x) + y)) ->
      get (code_val (get x) + y') = get (code_val (get x) + y).
Definition TBLg (ty : codetype) (get : Z -> Z) (root used : Z) : Prop :=
  1 <= root <= 15 /\ 2 ^ root <= used
  /\ (forall x, 0 <= x < used -> cell_ok ty root used x (get x))
  /\ rep_root get root /\ rep_sub get root.

(* [comment removed for export] *)
Definition cpok (ty : codetype) (codes : arr) (p : codeptr) (root : Z) : Prop :=
  match p with
  | CDyn ofs => 0 <= ofs /\ exists used, ofs + used <= 1444 /\ TBLg ty (fun x => arr_get codes (ofs + x)) root used
  | CLenfix => ty = LENS /\ root = 9
  | CDistfix => ty = DISTS /\ root = 5
  end.

(* [comment removed for export] *)
Definition rep_root_b (get : Z -> Z) (root : Z) : bool :=
  allz 0 (Z.to_nat (2 ^ root)) (fun x =>
    let e := get x in let b := code_bits e in
    if (1 <=? b) && (b <=? root)
    then allz 0 (Z.to_nat (2 ^ (root - b))) (fun k => get (x mod 2 ^ b + k * 2 ^ b) =? e)
    else true).
Definition rep_sub_b (get : Z -> Z) (root : Z) : bool :=
  allz 0 (Z.to_nat (2 ^ root)) (fun x =>
    let L := get x in let o := code_op L in
    if (1 <=? o) && (o <=? 15)
    then allz 0 (Z.to_nat (2 ^ o)) (fun y =>
           let e := get (code_val L + y) in let b := code_bits e in
           if (1 <=? b) && (b <=? o)
           then allz 0 (Z.to_nat (2 ^ (o - b))) (fun k => get (code_val L + y mod 2 ^ b + k * 2 ^ b) =? e)
           else if 1 <=? b then true   (* [comment removed for export] *)
           else true)
    else true).
Definition tblb (ty : codetype) (get : Z -> Z) (root used : Z) : bool :=
  (1 <=? root) && (root <=? 15) && (2 ^ root <=? used)
  && allz 0 (Z.to_nat used) (fun x => cell_ok_b ty root used x (get x))
  && rep_root_b get root && rep_sub_b get root.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition HB (h b : Z) : Prop := 0 <= b <= 63 /\ 0 <= h < 2 ^ b.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition is_linkb (e : Z) : bool := (1 <=? code_op e) && (code_op e <=? 15).
Definition lneed (s : inflate_state) (p : codeptr) (root h : Z) : Z :=
  let e := code_at s p (h mod 2 ^ root) in
  if is_linkb e
  then code_bits e + code_bits (code_at s p (code_val e + h mod 2 ^ (code_bits e + code_op e) / 2 ^ code_bits e))
  else code_bits e.
(* [comment removed for export] *)
Definition cl_ext (v : Z) : Z := if v <? 16 then 0 else if v =? 16 then 2 else if v =? 17 then 3 else 7.
Definition cneed (s : inflate_state) (h : Z) : Z :=
  let e := code_at s (is_lencode s) (h mod 2 ^ is_lenbits s) in code_bits e + cl_ext (code_val e).

(* [comment removed for export] *)
Definition CORE (s : inflate_state) : Prop :=
  (is_window_blk s = None -> is_wsize s = 0)
  /\ (is_window_blk s <> None -> arr_len (is_window s) = shl32 1 (is_wbits s) /\ is_wbits s <> 0)
  /\ (is_wsize s <> 0 -> is_wsize s = shl32 1 (is_wbits s))
  /\ 0 <= is_whave s /\ 0 <= is_wnext s
  /\ (is_wsize s = 0 -> is_whave s = 0 /\ is_wnext s = 0)
  /\ (is_wsize s <> 0 -> is_wnext s < is_wsize s /\ is_whave s <= is_wsize s)
  /\ (is_wsize s <> 0 -> is_whave s < is_wsize s -> is_wnext s = is_whave s)
  /\ (is_wbits s = 0 -> is_window_blk s = None /\ is_wrap s <> 0)
  /\ arr_len (is_lens s) = 320 /\ arr_len (is_work s) = 288 /\ arr_len (is_codes s) = 1444
  /\ is_sane s = 1
  /\ 0 <= is_length s < 2 ^ 32.

(* [comment removed for export] *)
Definition common (s : inflate_state) : Prop :=
  is_wbits s <> 0 /\ (is_flags s = 0 -> adler_canon (is_check s)).

(* [comment removed for export] *)
Definition tables (s : inflate_state) : Prop :=
  cpok LENS (is_codes s) (is_lencode s) (is_lenbits s) /\ cpok DISTS (is_codes s) (is_distcode s) (is_distbits s).

(* [comment removed for export] *)
Definition MF (m : Z) (s : inflate_state) (h b : Z) : Prop :=
  if m =? HEAD then (is_wrap s = 0 -> b < 8) /\ (is_flags s = 0 -> adler_canon (is_check s))
  else if m =? FLAGS then is_wbits s <> 0 /\ adler_canon (is_check s)
  else if (m =? TIME) || (m =? OS) then common s       (* [comment removed for export] *)
  else if m =? EXLEN then common s /\ (Z.land (is_flags s) 1024 = 0 -> b < 8)
  else if (m =? EXTRA) || (m =? NAME) || (m =? COMMENT) then common s /\ b < 8   (* [comment removed for export] *)
  else if m =? HCRC then common s /\ (Z.land (is_flags s) 512 = 0 -> b < 8)
  else if m =? DICTID then common s
  else if m =? DICT then is_wbits s <> 0 /\ b < 8
  else if (m =? TYPE) || (m =? TYPEDO) then common s /\ b < 8
  else if m =? STORED then common s
  else if (m =? COPY_) || (m =? COPY) then common s /\ b < 8
  else if m =? TABLE then common s /\ b < 14
  else if m =? LENLENS then
    common s /\ b < 8
    /\ 4 <= is_ncode s <= 19 /\ 257 <= is_nlen s <= 286 /\ 1 <= is_ndist s <= 30 /\ 0 <= is_have s < is_ncode s
    /\ (forall k, 0 <= k < is_have s -> 0 <= arr_get (is_lens s) (arr_get order_a k) <= 7)
  else if m =? CODELENS then
    common s /\ (b < 8 \/ b < cneed s h)
    /\ 257 <= is_nlen s <= 286 /\ 1 <= is_ndist s <= 30 /\ 0 <= is_have s < is_nlen s + is_ndist s
    /\ (forall i, 0 <= i < is_have s -> 0 <= arr_get (is_lens s) i <= 15)
    /\ cpok CODES (is_codes s) (is_lencode s) (is_lenbits s)
  else if m =? LEN_ then common s /\ b < 8 /\ tables s
  else if m =? LEN then common s /\ (b < 8 \/ b < lneed s (is_lencode s) (is_lenbits s) h) /\ tables s
  else if m =? LENEXT then common s /\ (b < 8 \/ b < is_extra s) /\ tables s /\ 0 <= is_extra s <= 15 /\ 1 <= is_length s < 2 ^ 16
  else if m =? DIST then common s /\ (b < 8 \/ b < lneed s (is_distcode s) (is_distbits s) h) /\ tables s /\ 1 <= is_length s
  else if m =? DISTEXT then
    common s /\ (b < 8 \/ b < is_extra s) /\ tables s /\ 1 <= is_length s /\ 0 <= is_extra s <= 15 /\ 1 <= is_offset s < 2 ^ 16
  else if m =? MATCH then common s /\ b < 8 /\ tables s /\ 1 <= is_length s /\ 1 <= is_offset s < 2 ^ 32
  else if m =? LIT then common s /\ b < 8 /\ tables s
  else if (m =? CHECK) || (m =? LENGTH) || (m =? DONE) then common s
  else if m =? BAD then (is_flags s = 0 -> adler_canon (is_check s))
  else if m =? MEM then is_hold s = h /\ is_bits s = b          (* [comment removed for export] *)
  else False.                                            (* [comment removed for export] *)

(* [comment removed for export] *)
Definition INV (s : inflate_state) : Prop :=
  CORE s /\ HB (is_hold s) (is_bits s) /\ MF (is_mode s) s (is_hold s) (is_bits s).

(* [comment removed for export] *)
Definition REGS (c : icall) (r : iregs) : Prop :=
  0 <= ir_next r /\ 0 <= ir_have r /\ ir_next r + ir_have r = arr_len (ic_input c)
  /\ 0 <= ir_put r /\ 0 <= ir_left r /\ ir_put r + ir_left r = arr_len (ic_outbuf c)
  /\ HB (ir_hold r) (ir_bits r)
  /\ (forall i, 0 <= arr_get (ic_input c) i < 256)
  /\ arr_len (ic_input c) < 2 ^ 32 /\ arr_len (ic_outbuf c) < 2 ^ 32.

(* [comment removed for export] *)
Definition WF (m : Z) (c : icall) (r : iregs) : Prop :=
  if (m =? LENGTH) || (m =? DONE) || (m =? BAD) then True
  else if (m =? HEAD) || (m =? FLAGS) then ir_out r = arr_len (ic_outbuf c) /\ ir_put r = 0   (* [comment removed for export] *)
  else ir_out r = arr_len (ic_outbuf c).

(* [comment removed for export] *)
Definition WINV (w : iw) : Prop :=
  let s := w_s w in let c := w_c w in let r := w_r w in
  CORE s /\ REGS c r /\ MF (is_mode s) s (ir_hold r) (ir_bits r) /\ WF (is_mode s) c r
  (* [comment removed for export] *)
  /\ (is_wbits s = 0 -> ir_put r = 0).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rank (m : Z) : Z :=
  if (HEAD <=? m) && (m <=? HCRC) then 3
  else if m =? DICT then 3
  else if (m =? TYPE) || (m =? TYPEDO) then 2
  else if (m =? COPY_) || (m =? COPY) then 3
  else if (m =? STORED) || (m =? DISTEXT) || (m =? MATCH) || (m =? CHECK) || (m =? LENGTH) then 1
  else 0.

Lemma rank_range : forall m, 0 <= rank m <= 3.
Proof.
  intros m. unfold rank.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia.
Qed.

Definition PHI (w : iw) : Z :=
  let r := w_r w in 64 * ir_have r + 8 * ir_bits r + 8 * ir_left r + rank (is_mode (w_s w)).

(* [comment removed for export] *)
Definition POST (w0 : iw) {A} (res : ares A) : Prop :=
  match res with
  | ARun _ w' => WINV w' /\ PHI w' < PHI w0
  | ALeave w' => WINV w'
  | ARet _ w' => WINV w' /\ INV (w_s w')
  end.
