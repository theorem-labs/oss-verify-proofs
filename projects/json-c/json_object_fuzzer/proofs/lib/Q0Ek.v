(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbVh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
Import ListNotations.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).

Record fnaddrs := FN {
fn_obj_to_json_string : Z;
fn_arr_to_json_string : Z;
fn_bool_to_json_string : Z;
fn_dbl_to_json_string : Z;
fn_int_to_json_string : Z;
fn_str_to_json_string : Z;
fn_ud_to_json_string : Z;
fn_free_userdata : Z;
fn_lh_entry_free : Z;
fn_lh_char_hash : Z;
fn_lh_char_equal : Z;
fn_arr_entry_free : Z
}.

Definition JT_NULL : Z := 0.
Definition JT_BOOLEAN : Z := 1.
Definition JT_DOUBLE : Z := 2.
Definition JT_INT : Z := 3.
Definition JT_OBJECT : Z := 4.
Definition JT_ARRAY : Z := 5.
Definition JT_STRING : Z := 6.

Notation LH_EMPTY := 18446744073709551615 (only parsing).
Notation LH_FREED := 18446744073709551614 (only parsing).
Notation LH_ENTRY_SZ := 40 (only parsing).
Notation LH_TABLE_SZ := 56 (only parsing).
Notation AL_SZ := 32 (only parsing).
Notation PB_SZ := 16 (only parsing).

Inductive jshape : Type :=
| Sbool
| Sdouble (ud : bool)
| Sint
| Sstr (heap : bool)
| Sobj (kids : list (option jshape))
| Sarr (kids : list (option jshape)).

Fixpoint sdepth (s : jshape) : Z :=
match s with
| Sobj kids | Sarr kids =>
1 + (fix kmax (l : list (option jshape)) : Z :=
match l with
| [] => 0
| None :: l' => kmax l'
| Some s' :: l' => Z.max (sdepth s') (kmax l')
end) kids
| _ => 0
end.

Definition kdepth (kids : list (option jshape)) : Z :=
fold_right (fun k d => match k with None => d | Some s => Z.max (sdepth s) d end) 0 kids.

Lemma sdepth_obj : forall kids, sdepth (Sobj kids) = 1 + kdepth kids.
Proof. reflexivity. Qed.
Lemma sdepth_arr : forall kids, sdepth (Sarr kids) = 1 + kdepth kids.
Proof. reflexivity. Qed.
Lemma kdepth_cons : forall k l,
kdepth (k :: l) = match k with None => kdepth l | Some s => Z.max (sdepth s) (kdepth l) end.
Proof. reflexivity. Qed.
Lemma kdepth_nonneg : forall l, 0 <= kdepth l.
Proof. induction l as [|[s|] l IH]; [cbn; lia| |]; rewrite kdepth_cons; lia. Qed.
Lemma sdepth_nonneg : forall s, 0 <= sdepth s.
Proof.
intros s; destruct s as [| | | |kids|kids]; try (cbn; lia);
rewrite ?sdepth_obj, ?sdepth_arr; pose proof (kdepth_nonneg kids); lia.
Qed.

Definition LH_EMPTYv : Z := 18446744073709551615.
Definition LH_FREEDv : Z := 18446744073709551614.

Record slotv := SV { sv_k : Z; sv_kc : Z; sv_pad : Z; sv_v : Z; sv_nx : Z; sv_pv : Z }.
Definition slot_cells (s : slotv) : list cell :=
[C8 (Z_to_bv 64 (sv_k s)); C4 (Z_to_bv 64 (sv_kc s)); C4 (Z_to_bv 64 (sv_pad s));
C8 (Z_to_bv 64 (sv_v s)); C8 (Z_to_bv 64 (sv_nx s)); C8 (Z_to_bv 64 (sv_pv s))].

Record lent := LE { le_ix : nat; le_k : Z; le_kn : Z; le_ks : list byte; le_v : Z }.

Definition ent_addr (tbl : Z) (i : nat) : Z := tbl + 40 * Z.of_nat i.

Definition nx_of (tbl : Z) (es : list lent) (j : nat) : Z :=
match nth_error es (S j) with Some e => ent_addr tbl (le_ix e) | None => 0 end.
Definition pv_of (tbl : Z) (es : list lent) (j : nat) : Z :=
match j with O => 0 | S j' => match nth_error es j' with Some e => ent_addr tbl (le_ix e) | None => 0 end end.
Definition hd_of (tbl : Z) (es : list lent) : Z :=
match es with [] => 0 | e :: _ => ent_addr tbl (le_ix e) end.
Definition tl_of (tbl : Z) (es : list lent) : Z :=
match es with [] => 0 | _ => ent_addr tbl (le_ix (last es (LE 0 0 0 [] 0))) end.

Section WithSegs.
Variable segs : list Segment.
Variable fn : fnaddrs.

Notation rw_cells := (rw_cells segs).

Definition cstr (m : word -> option byte) (a n : Z) (s : list byte) : Prop :=
Z.of_nat (length s) + 1 <= n /\
Forall (fun b => bv_unsigned b <> 0) s /\
exists junk, rw_cells m a [CB (Z.to_nat n) (s ++ [Z_to_bv 8 0] ++ junk)].

Definition pbuf_core (m : word -> option byte) (pb buf bpos size : Z) (content : list byte) : Prop :=
0 <= bpos <= size /\ 0 < size < 2^31 /\
Z.of_nat (length content) = size /\
rw_cells m pb [C8 (wz buf); C4 (wz bpos); C4 (wz size)] /\
rw_cells m buf [CB (Z.to_nat size) content].

Definition pbufw (m : word -> option byte) (BS : list blk) (pb : Z) : Prop :=
exists buf bpos size content,
BS = [(pb, PB_SZ); (buf, size)] /\ pbuf_core m pb buf bpos size content.

Definition pbuf (m : word -> option byte) (BS : list blk) (pb : Z) : Prop :=
exists buf bpos size pre post,
BS = [(pb, PB_SZ); (buf, size)] /\
Z.of_nat (length pre) = bpos /\
pbuf_core m pb buf bpos size (pre ++ [Z_to_bv 8 0] ++ post).

#[using="Type"] Lemma pbuf_pbufw : forall m BS pb, pbuf m BS pb -> pbufw m BS pb.
Proof. intros m BS pb (buf & bpos & size & pre & post & E & L & C). exists buf, bpos, size, (pre ++ [Z_to_bv 8 0] ++ post). auto. Qed.

#[using="Type"] Lemma pbuf_lt : forall m pb buf bpos size pre post,
Z.of_nat (length pre) = bpos -> pbuf_core m pb buf bpos size (pre ++ [Z_to_bv 8 0] ++ post) -> bpos < size.
Proof. intros m pb buf bpos size pre post L (H1 & H2 & H3 & _). rewrite !length_app in H3. cbn in H3. lia. Qed.

Definition jhdr_cells (ty rc tojs pb udel ud : Z) : list cell :=
[C4 (wz ty); C4 (wz rc); C8 (wz tojs); C8 (wz pb); C8 (wz udel); C8 (wz ud)].

Definition opt_pbuf (m : word -> option byte) (BS : list blk) (pb : Z) : Prop :=
(pb = 0 /\ BS = []) \/ (pb <> 0 /\ pbufw m BS pb).

Definition alist (m : word -> option byte) (BS : list blk) (a : Z) (ps : list Z) : Prop :=
exists arr size junk,
BS = [(a, AL_SZ); (arr, 8 * size)] /\
Z.of_nat (length ps) <= size /\ (1 <= size /\ 8 * size < 2^64) /\
rw_cells m a [C8 (wz arr); C8 (wz (Z.of_nat (length ps))); C8 (wz size); C8 (wz (fn_arr_entry_free fn))] /\
rw_cells m arr (map (fun p => C8 (wz p)) ps ++ [CB (Z.to_nat (8 * (size - Z.of_nat (length ps)))) junk]).

Definition lh_hdrf (ffn : Z) (m : word -> option byte) (t size count hd tl tbl : Z) : Prop :=
rw_cells m t [C4 (Z_to_bv 64 size); C4 (Z_to_bv 64 count); C8 (Z_to_bv 64 hd); C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 tbl);
C8 (Z_to_bv 64 ffn); C8 (Z_to_bv 64 (fn_lh_char_hash fn)); C8 (Z_to_bv 64 (fn_lh_char_equal fn))].
Definition lh_hdr := lh_hdrf (fn_lh_entry_free fn).

Definition lh_slots (m : word -> option byte) (tbl : Z) (svs : list slotv) : Prop :=
forall i s, nth_error svs i = Some s -> rw_cells m (ent_addr tbl i) (slot_cells s).

Definition lh_link (tbl : Z) (es : list lent) (svs : list slotv) : Prop :=
(forall j e, nth_error es j = Some e ->
exists s, nth_error svs (le_ix e) = Some s /\ sv_k s = le_k e /\ sv_kc s = 0 /\ sv_v s = le_v e /\
sv_nx s = nx_of tbl es j /\ sv_pv s = pv_of tbl es j)
/\ (forall i s, nth_error svs i = Some s -> ~ In i (map le_ix es) -> sv_k s = LH_EMPTYv \/ sv_k s = LH_FREEDv)
/\ List.NoDup (map le_ix es)
/\ (forall e, In e es -> 0 < le_k e /\ le_k e + le_kn e < LH_FREEDv /\ le_kn e <= 2^31 /\ 0 <= le_v e < 2^64).

Definition lh_keys (m : word -> option byte) (es : list lent) : Prop :=
Forall (fun e => cstr m (le_k e) (le_kn e) (le_ks e)) es.

Definition lh_openf (ffn : Z) (m : word -> option byte) (t tbl size : Z) (es : list lent) (svs : list slotv) : Prop :=
lh_hdrf ffn m t size (Z.of_nat (length es)) (hd_of tbl es) (tl_of tbl es) tbl
/\ lh_slots m tbl svs /\ lh_link tbl es svs /\ lh_keys m es
/\ In size lf_sizes /\ Z.of_nat (length es) <= lf_thr size /\ Z.of_nat (length svs) = size.
Definition lh_open := lh_openf (fn_lh_entry_free fn).

Definition lh_blocks (t tbl size : Z) (es : list lent) : list blk :=
(t, 56) :: (tbl, 40 * size) :: map (fun e => (le_k e, le_kn e)) es.

Definition lhtab2 (m : word -> option byte) (BS : list blk) (t : Z) (kvs : list (Z * Z)) : Prop :=
exists tbl size es svs,
kvs = map (fun e => (le_k e, le_v e)) es /\ BS = lh_blocks t tbl size es /\ lh_open m t tbl size es svs.

Definition dbl_special (bits : word) : Prop := 0x7FF0000000000000 <= (bv_unsigned bits) mod 2^63.

Definition str_objsize (len : Z) : Z := 49 + Z.max len 8.

Fixpoint jval (s : jshape) (m : word -> option byte) (BS : list blk) (p : Z) (rc : Z) {struct s} : Prop :=
exists (pb : Z) (PBS : list blk) (REST : list blk),
BS = REST ++ PBS /\ opt_pbuf m PBS pb /\
match s with
| Sbool =>
exists (b : Z) junk,
REST = [(p, 48)] /\
rw_cells m p (jhdr_cells JT_BOOLEAN rc (fn_bool_to_json_string fn) pb 0 0 ++ [C4 (wz b); CB 4 junk])
| Sdouble false =>
exists (bits : word),
REST = [(p, 48)] /\ dbl_special bits /\
rw_cells m p (jhdr_cells JT_DOUBLE rc (fn_dbl_to_json_string fn) pb 0 0 ++ [C8 bits])
| Sdouble true =>
exists (bits : word) (ud udn : Z) (uds : list byte),
REST = [(p, 48); (ud, udn)] /\ udn <= 2^31 /\
rw_cells m p (jhdr_cells JT_DOUBLE rc (fn_ud_to_json_string fn) pb (fn_free_userdata fn) ud ++ [C8 bits]) /\
cstr m ud udn uds
| Sint =>
exists (cty : Z) (v : word) junk,
REST = [(p, 56)] /\ (cty = 0 \/ cty = 1) /\
rw_cells m p (jhdr_cells JT_INT rc (fn_int_to_json_string fn) pb 0 0 ++ [C4 (wz cty); CB 4 junk; C8 v])
| Sstr false =>
exists (len : Z) (str : list byte) junk,
REST = [(p, str_objsize len)] /\
0 <= len < 2^31 /\ Z.of_nat (length str) = len /\
rw_cells m p (jhdr_cells JT_STRING rc (fn_str_to_json_string fn) pb 0 0 ++
[C8 (wz len); CB (Z.to_nat (str_objsize len - 48)) (str ++ [Z_to_bv 8 0] ++ junk)])

| Sstr true =>
exists (len : Z) (pd pdn : Z) (str : list byte) junk2,
REST = [(p, 56); (pd, pdn)] /\
- 2^31 < len < 0 /\ Z.of_nat (length str) = - len /\ - len + 1 <= pdn /\
rw_cells m p (jhdr_cells JT_STRING rc (fn_str_to_json_string fn) pb 0 0 ++ [C8 (wz len); C8 (wz pd)]) /\
rw_cells m pd [CB (Z.to_nat pdn) (str ++ [Z_to_bv 8 0] ++ junk2)]

| Sobj kids =>
exists (t : Z) (TBS : list blk) (kvs : list (Z * Z)) (KBS : list (list blk)),
REST = (p, 48) :: TBS ++ concat KBS /\
rw_cells m p (jhdr_cells JT_OBJECT rc (fn_obj_to_json_string fn) pb 0 0 ++ [C8 (wz t)]) /\
lhtab2 m TBS t kvs /\
length kvs = length kids /\ length KBS = length kids /\
(fix kids_ok (ks : list (option jshape)) (vs : list (Z * Z)) (bss : list (list blk)) {struct ks} : Prop :=
match ks, vs, bss with
| [], [], [] => True
| k :: ks', (_, v) :: vs', bs :: bss' =>
match k with
| None => v = 0 /\ bs = []
| Some s' => v <> 0 /\ jval s' m bs v 1
end /\ kids_ok ks' vs' bss'
| _, _, _ => False
end) kids kvs KBS
| Sarr kids =>
exists (a : Z) (ABS : list blk) (ps : list Z) (KBS : list (list blk)),
REST = (p, 48) :: ABS ++ concat KBS /\
rw_cells m p (jhdr_cells JT_ARRAY rc (fn_arr_to_json_string fn) pb 0 0 ++ [C8 (wz a)]) /\
alist m ABS a ps /\
length ps = length kids /\ length KBS = length kids /\
(fix kids_ok (ks : list (option jshape)) (vs : list Z) (bss : list (list blk)) {struct ks} : Prop :=
match ks, vs, bss with
| [], [], [] => True
| k :: ks', v :: vs', bs :: bss' =>
match k with
| None => v = 0 /\ bs = []
| Some s' => v <> 0 /\ jval s' m bs v 1
end /\ kids_ok ks' vs' bss'
| _, _, _ => False
end) kids ps KBS
end.

Definition jopt (s : option jshape) (m : word -> option byte) (BS : list blk) (p : Z) : Prop :=
match s with
| None => p = 0 /\ BS = []
| Some s' => p <> 0 /\ jval s' m BS p 1
end.

End WithSegs.
