(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bt X1c1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qy X1nw.
Import ListNotations.
Import X1bt.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Definition INT_MAX : Z := 2147483647.
Definition LONG_MAX : Z := 9223372036854775807.
Definition OGGS_MAGIC : list Z := [79; 103; 103; 83].
Definition CHAR_O : Z := 79.
Definition GRANULE_UNSPEC : Z := 0.
Definition SIZEOF_INT : Z := 4.
Definition SIZEOF_INT64 : Z := 8.

Section Records.
Variable ptr : Type.

Record sync_st : Type := mkSync {
sy_data : option ptr;
sy_buf : list Z;
sy_storage : Z;
sy_fill : Z;
sy_returned : Z;
sy_unsynced : Z;
sy_headerbytes : Z;
sy_bodybytes : Z }.

Record stream_st : Type := mkStream {
os_body_data : option ptr;
os_body : list Z;
os_body_storage : Z;
os_body_fill : Z;
os_body_returned : Z;
os_lacing_vals : option ptr;
os_lacing : list Z;
os_granule_vals : option ptr;
os_granules : list Z;
os_lacing_storage : Z;
os_lacing_fill : Z;
os_lacing_packet : Z;
os_lacing_returned : Z;
os_header_fill : Z;
os_e_o_s : Z;
os_b_o_s : Z;
os_serialno : Z;
os_pageno : Z;
os_packetno : Z;
os_granulepos : Z }.
End Records.
Arguments mkSync {ptr}.
Arguments mkStream {ptr}.
Arguments sy_data {ptr}. Arguments sy_buf {ptr}. Arguments sy_storage {ptr}. Arguments sy_fill {ptr}.
Arguments sy_returned {ptr}. Arguments sy_unsynced {ptr}. Arguments sy_headerbytes {ptr}. Arguments sy_bodybytes {ptr}.
Arguments os_body_data {ptr}. Arguments os_body {ptr}. Arguments os_body_storage {ptr}. Arguments os_body_fill {ptr}.
Arguments os_body_returned {ptr}. Arguments os_lacing_vals {ptr}. Arguments os_lacing {ptr}. Arguments os_granule_vals {ptr}.
Arguments os_granules {ptr}. Arguments os_lacing_storage {ptr}. Arguments os_lacing_fill {ptr}. Arguments os_lacing_packet {ptr}.
Arguments os_lacing_returned {ptr}. Arguments os_header_fill {ptr}. Arguments os_e_o_s {ptr}. Arguments os_b_o_s {ptr}.
Arguments os_serialno {ptr}. Arguments os_pageno {ptr}. Arguments os_packetno {ptr}. Arguments os_granulepos {ptr}.

Record page : Type := mkPage { pg_hdr : Z; pg_header_len : Z; pg_body_len : Z }.
Record packet : Type := mkPacket {
pk_off : Z; pk_bytes : Z; pk_b_o_s : Z; pk_e_o_s : Z; pk_granulepos : Z; pk_packetno : Z }.

Definition page_header {ptr} (sy : sync_st ptr) (og : page) : list Z :=
zslice (pg_hdr og) (pg_header_len og) (sy_buf sy).
Definition page_body {ptr} (sy : sync_st ptr) (og : page) : list Z :=
zslice (pg_hdr og + pg_header_len og) (pg_body_len og) (sy_buf sy).

Definition packet_data {ptr} (os : stream_st ptr) (op : packet) : list Z :=
zslice (pk_off op) (pk_bytes op) (os_body os).

Definition ogg_page_version (hdr : list Z) : Z := znth hdr 4.

Definition ogg_page_continued (hdr : list Z) : Z := Z.land (znth hdr 5) 1.
Definition ogg_page_bos (hdr : list Z) : Z := Z.land (znth hdr 5) 2.
Definition ogg_page_eos (hdr : list Z) : Z := Z.land (znth hdr 5) 4.

Definition ogg_page_granulepos (hdr : list Z) : Z := s64 (le64_at hdr 6).

Definition ogg_page_serialno (hdr : list Z) : Z := s32 (le32_at hdr 14).

Definition ogg_page_pageno (hdr : list Z) : Z := le32_at hdr 18.

Fixpoint count_lt255 (l : list Z) : Z :=
match l with [] => 0 | v :: l' => (if v <? 255 then 1 else 0) + count_lt255 l' end.
Definition ogg_page_packets (hdr : list Z) : Z := count_lt255 (zslice 27 (znth hdr 26) hdr).

Definition lacing_of (hdr : list Z) : list Z := zslice 27 (znth hdr 26) hdr.

Definition ogg_page_checksum (hdr body : list Z) : list Z :=
let hdr0 := ztake 22 hdr ++ [0; 0; 0; 0] ++ zdrop 26 hdr in
let crc := os_update_crc (os_update_crc 0 hdr0) body in
[crc mod 256; (crc / 2^8) mod 256; (crc / 2^16) mod 256; (crc / 2^24) mod 256].

Fixpoint find_byte (c : Z) (l : list Z) (i : Z) : option Z :=
match l with
| [] => None
| b :: l' => if b =? c then Some i else find_byte c l' (i + 1)
end.

Section Ogg.
Context {St ptr : Type}.
Variable lib_malloc : Z -> M St (option ptr).
Variable lib_realloc : ptr -> Z -> M St (option ptr).
Variable lib_free : ptr -> M St unit.

Definition ogg_sync_init : sync_st ptr := mkSync None [] 0 0 0 0 0 0.

Definition ogg_sync_clear (sy : sync_st ptr) : M St (sync_st ptr) :=
match sy_data sy with
| Some p => lib_free p ;;; mret ogg_sync_init
| None => mret ogg_sync_init
end.

Definition ogg_sync_check (sy : sync_st ptr) : bool := sy_storage sy <? 0.

Definition ogg_sync_buffer (sy : sync_st ptr) (size : Z) : M St (option (ptr * Z) * sync_st ptr) :=
if ogg_sync_check sy then mret (None, sy) else
let sy := if negb (sy_returned sy =? 0) then
let fill := sy_fill sy - sy_returned sy in
mkSync (sy_data sy) (ztake fill (zdrop (sy_returned sy) (sy_buf sy)))
(sy_storage sy) fill 0 (sy_unsynced sy) (sy_headerbytes sy) (sy_bodybytes sy)
else sy in
if sy_storage sy - sy_fill sy <? size then
if INT_MAX - 4096 - sy_fill sy <? size then
sy' <- ogg_sync_clear sy ;; mret (None, sy')
else
let newsize := size + sy_fill sy + 4096 in
ret <- match sy_data sy with
| Some p => lib_realloc p newsize
| None => lib_malloc newsize
end ;;
match ret with
| None => sy' <- ogg_sync_clear sy ;; mret (None, sy')
| Some q =>
let sy := mkSync (Some q) (sy_buf sy) newsize (sy_fill sy) (sy_returned sy)
(sy_unsynced sy) (sy_headerbytes sy) (sy_bodybytes sy) in
mret (Some (q, sy_fill sy), sy)
end
else
mret (match sy_data sy with Some p => Some (p, sy_fill sy) | None => None end, sy).

Definition sync_write (sy : sync_st ptr) (off : Z) (bytes : list Z) : sync_st ptr :=
mkSync (sy_data sy) (ztake off (sy_buf sy) ++ bytes) (sy_storage sy) (sy_fill sy) (sy_returned sy)
(sy_unsynced sy) (sy_headerbytes sy) (sy_bodybytes sy).

Definition ogg_sync_wrote (sy : sync_st ptr) (bytes : Z) : Z * sync_st ptr :=
if ogg_sync_check sy then (-1, sy)
else if sy_storage sy <? sy_fill sy + bytes then (-1, sy)
else (0, mkSync (sy_data sy) (sy_buf sy) (sy_storage sy) (sy_fill sy + bytes) (sy_returned sy)
(sy_unsynced sy) (sy_headerbytes sy) (sy_bodybytes sy)).

Definition sync_fail (sy : sync_st ptr) (ret bytes : Z) : (Z * option page) * sync_st ptr :=

let next := match find_byte CHAR_O (zslice (ret + 1) (bytes - 1) (sy_buf sy)) (ret + 1) with
| Some i => i
| None => sy_fill sy
end in
((- (next - ret), None),
mkSync (sy_data sy) (sy_buf sy) (sy_storage sy) (sy_fill sy) next (sy_unsynced sy) 0 0).

Definition ogg_sync_pageseek (sy : sync_st ptr) : (Z * option page) * sync_st ptr :=
let ret := sy_returned sy in
let bytes := sy_fill sy - ret in
let buf := sy_buf sy in
if ogg_sync_check sy then ((0, None), sy) else

let hdr_phase : option (unit + sync_st ptr) :=
if sy_headerbytes sy =? 0 then
if bytes <? 27 then None
else if negb (list_eqb (zslice ret 4 buf) OGGS_MAGIC) then Some (inl tt)
else
let nseg := znth buf (ret + 26) in
let headerbytes := nseg + 27 in
if bytes <? headerbytes then None
else Some (inr (mkSync (sy_data sy) buf (sy_storage sy) (sy_fill sy) ret (sy_unsynced sy)
headerbytes (sy_bodybytes sy + zsum (zslice (ret + 27) nseg buf))))
else Some (inr sy) in
match hdr_phase with
| None => ((0, None), sy)
| Some (inl _) => sync_fail sy ret bytes
| Some (inr sy) =>
if bytes <? sy_bodybytes sy + sy_headerbytes sy then ((0, None), sy)
else
let hdr := zslice ret (sy_headerbytes sy) buf in
let body := zslice (ret + sy_headerbytes sy) (sy_bodybytes sy) buf in
let chksum := zslice (ret + 22) 4 buf in
if negb (list_eqb chksum (ogg_page_checksum hdr body)) then sync_fail sy ret bytes
else
let n := sy_headerbytes sy + sy_bodybytes sy in
((n, Some (mkPage ret (sy_headerbytes sy) (sy_bodybytes sy))),
mkSync (sy_data sy) buf (sy_storage sy) (sy_fill sy) (ret + n) 0 0 0)
end.

Fixpoint pageout_loop (fuel : nat) (sy : sync_st ptr) : option ((Z * option page) * sync_st ptr) :=
match fuel with
| O => None
| S fuel' =>
let '((ret, og), sy1) := ogg_sync_pageseek sy in
if 0 <? ret then Some ((1, og), sy1)
else if ret =? 0 then Some ((0, None), sy1)
else if sy_unsynced sy1 =? 0 then
Some ((-1, None), mkSync (sy_data sy1) (sy_buf sy1) (sy_storage sy1) (sy_fill sy1) (sy_returned sy1)
1 (sy_headerbytes sy1) (sy_bodybytes sy1))
else pageout_loop fuel' sy1
end.

Definition pageout_fuel (sy : sync_st ptr) : nat := S (Z.to_nat (sy_fill sy - sy_returned sy)).

Definition ogg_sync_pageout (sy : sync_st ptr) : option ((Z * option page) * sync_st ptr) :=
if ogg_sync_check sy then Some ((0, None), sy)
else pageout_loop (pageout_fuel sy) sy.

Definition stream_zero : stream_st ptr :=
mkStream None [] 0 0 0 None [] None [] 0 0 0 0 0 0 0 0 0 0 0.

Definition ogg_stream_check (os : stream_st ptr) : bool :=
match os_body_data os with None => true | Some _ => false end.

Definition mfree_opt (o : option ptr) : M St unit :=
match o with Some p => lib_free p | None => mret tt end.

Definition ogg_stream_clear (os : stream_st ptr) : M St (stream_st ptr) :=
mfree_opt (os_body_data os) ;;;
mfree_opt (os_lacing_vals os) ;;;
mfree_opt (os_granule_vals os) ;;;
mret stream_zero.

Definition ogg_stream_init (serialno : Z) : M St (Z * stream_st ptr) :=
b <- lib_malloc 16384 ;;
l <- lib_malloc 4096 ;;
g <- lib_malloc 8192 ;;
let os := mkStream b [] 16384 0 0 l [] g [] 1024 0 0 0 0 0 0 0 0 0 0 in
match b, l, g with
| Some _, Some _, Some _ =>
mret (0, mkStream b [] 16384 0 0 l [] g [] 1024 0 0 0 0 0 0 serialno 0 0 0)
| _, _, _ => os' <- ogg_stream_clear os ;; mret (-1, os')
end.

Definition set_body (os : stream_st ptr) (body : list Z) (storage fill returned : Z) : stream_st ptr :=
mkStream (os_body_data os) body storage fill returned
(os_lacing_vals os) (os_lacing os) (os_granule_vals os) (os_granules os)
(os_lacing_storage os) (os_lacing_fill os) (os_lacing_packet os) (os_lacing_returned os)
(os_header_fill os) (os_e_o_s os) (os_b_o_s os) (os_serialno os) (os_pageno os) (os_packetno os) (os_granulepos os).
Definition set_lacing (os : stream_st ptr) (lac gran : list Z) (storage fill packet returned : Z) : stream_st ptr :=
mkStream (os_body_data os) (os_body os) (os_body_storage os) (os_body_fill os) (os_body_returned os)
(os_lacing_vals os) lac (os_granule_vals os) gran storage fill packet returned
(os_header_fill os) (os_e_o_s os) (os_b_o_s os) (os_serialno os) (os_pageno os) (os_packetno os) (os_granulepos os).
Definition set_blocks (os : stream_st ptr) (b : option ptr) (bstorage : Z) (l g : option ptr) (lstorage : Z) : stream_st ptr :=
mkStream b (os_body os) bstorage (os_body_fill os) (os_body_returned os)
l (os_lacing os) g (os_granules os) lstorage (os_lacing_fill os) (os_lacing_packet os) (os_lacing_returned os)
(os_header_fill os) (os_e_o_s os) (os_b_o_s os) (os_serialno os) (os_pageno os) (os_packetno os) (os_granulepos os).
Definition set_tail (os : stream_st ptr) (e_o_s pageno packetno : Z) : stream_st ptr :=
mkStream (os_body_data os) (os_body os) (os_body_storage os) (os_body_fill os) (os_body_returned os)
(os_lacing_vals os) (os_lacing os) (os_granule_vals os) (os_granules os)
(os_lacing_storage os) (os_lacing_fill os) (os_lacing_packet os) (os_lacing_returned os)
(os_header_fill os) e_o_s (os_b_o_s os) (os_serialno os) pageno packetno (os_granulepos os).

Definition os_body_expand (os : stream_st ptr) (needed : Z) : M St (Z * stream_st ptr) :=
if os_body_fill os <? os_body_storage os - needed then mret (0, os)
else if LONG_MAX - needed <? os_body_storage os then os' <- ogg_stream_clear os ;; mret (-1, os')
else
let body_storage := os_body_storage os + needed in
let body_storage := if body_storage <? LONG_MAX - 1024 then body_storage + 1024 else body_storage in
match os_body_data os with
| None => munr
| Some p =>
ret <- lib_realloc p (body_storage * 1) ;;
match ret with
| None => os' <- ogg_stream_clear os ;; mret (-1, os')
| Some q => mret (0, set_blocks os (Some q) body_storage (os_lacing_vals os) (os_granule_vals os) (os_lacing_storage os))
end
end.

Definition os_lacing_expand (os : stream_st ptr) (needed : Z) : M St (Z * stream_st ptr) :=
if os_lacing_fill os <? os_lacing_storage os - needed then mret (0, os)
else if LONG_MAX - needed <? os_lacing_storage os then os' <- ogg_stream_clear os ;; mret (-1, os')
else
let lacing_storage := os_lacing_storage os + needed in
let lacing_storage := if lacing_storage <? LONG_MAX - 32 then lacing_storage + 32 else lacing_storage in
match os_lacing_vals os, os_granule_vals os with
| Some l, Some g =>
ret <- lib_realloc l (lacing_storage * SIZEOF_INT) ;;
match ret with
| None => os' <- ogg_stream_clear os ;; mret (-1, os')
| Some l' =>
let os := set_blocks os (os_body_data os) (os_body_storage os) (Some l') (os_granule_vals os) (os_lacing_storage os) in
ret2 <- lib_realloc g (lacing_storage * SIZEOF_INT64) ;;
match ret2 with
| None => os' <- ogg_stream_clear os ;; mret (-1, os')
| Some g' => mret (0, set_blocks os (os_body_data os) (os_body_storage os) (Some l') (Some g') lacing_storage)
end
end
| _, _ => munr
end.

Fixpoint sum_low (l : list Z) : Z :=
match l with [] => 0 | v :: l' => Z.land v 255 + sum_low l' end.

Fixpoint skip_continued (l : list Z) : Z * Z :=
match l with
| [] => (0, 0)
| v :: l' => if v <? 255 then (1, v)
else let '(n, s) := skip_continued l' in (n + 1, s + v)
end.

Fixpoint seg_loop (vals : list Z) (bos : bool) (fill packet saved : Z) : list Z * list Z * Z * Z * Z :=
match vals with
| [] => ([], [], fill, packet, saved)
| v :: vals' =>
let lv := if bos then Z.lor v 256 else v in
let saved' := if v <? 255 then fill else saved in
let fill' := fill + 1 in
let packet' := if v <? 255 then fill' else packet in
let '(lac, gran, f, p, s) := seg_loop vals' false fill' packet' saved' in
(lv :: lac, (-1) :: gran, f, p, s)
end.

Definition pagein_returned (os : stream_st ptr) : stream_st ptr :=
let br := os_body_returned os in
let os := if negb (br =? 0) then
let fill := os_body_fill os - br in
set_body os (ztake fill (zdrop br (os_body os))) (os_body_storage os) fill 0
else os in
let lr := os_lacing_returned os in
if negb (lr =? 0) then
set_lacing os (zdrop lr (os_lacing os)) (zdrop lr (os_granules os)) (os_lacing_storage os)
(os_lacing_fill os - lr) (os_lacing_packet os - lr) 0
else os.

Definition pagein_unroll (os : stream_st ptr) (pageno : Z) : stream_st ptr :=
if negb (pageno =? os_pageno os) then
let lp := os_lacing_packet os in
let lf := os_lacing_fill os in
let dropped := sum_low (zslice lp (lf - lp) (os_lacing os)) in
let bfill := os_body_fill os - dropped in
let os := set_body os (ztake bfill (os_body os)) (os_body_storage os) bfill (os_body_returned os) in
let os := set_lacing os (ztake lp (os_lacing os)) (ztake lp (os_granules os)) (os_lacing_storage os)
lp lp (os_lacing_returned os) in
if negb (os_pageno os =? -1) then
set_lacing os (os_lacing os ++ [1024]) (os_granules os ++ [GRANULE_UNSPEC]) (os_lacing_storage os)
(lp + 1) (lp + 1) (os_lacing_returned os)
else os
else os.

Definition pagein_skip (os : stream_st ptr) (hdr : list Z) : Z * Z * Z :=
let bos := ogg_page_bos hdr in
if negb (ogg_page_continued hdr =? 0) then
let lf := os_lacing_fill os in
let last := znth (os_lacing os) (lf - 1) in
if (lf <? 1) || (Z.land last 255 <? 255) || (last =? 1024)
then let '(n, s) := skip_continued (lacing_of hdr) in (0, n, s)
else (bos, 0, 0)
else (bos, 0, 0).

Definition pagein_body (os : stream_st ptr) (body : list Z) (skipped bodysize : Z) : stream_st ptr :=
set_body os (os_body os ++ zslice skipped bodysize body) (os_body_storage os)
(os_body_fill os + bodysize) (os_body_returned os).

Definition pagein_segments (os : stream_st ptr) (hdr : list Z) (bos segptr : Z) : stream_st ptr :=
let eos := ogg_page_eos hdr in
let '(lac, gran, fill', packet', saved) :=
seg_loop (zdrop segptr (lacing_of hdr)) (negb (bos =? 0)) (os_lacing_fill os) (os_lacing_packet os) (-1) in
let lacing := os_lacing os ++ lac in
let granules := os_granules os ++ gran in
let granules := if negb (saved =? -1) then zupd granules saved (ogg_page_granulepos hdr) else granules in
let lacing := if negb (eos =? 0) then
(if 0 <? fill' then zupd lacing (fill' - 1) (Z.lor (znth lacing (fill' - 1)) 512) else lacing)
else lacing in
let os := set_lacing os lacing granules (os_lacing_storage os) fill' packet' (os_lacing_returned os) in
set_tail os (if negb (eos =? 0) then 1 else os_e_o_s os) (ogg_page_pageno hdr + 1) (os_packetno os).

Definition ogg_stream_pagein (os : stream_st ptr) (hdr body : list Z) : M St (Z * stream_st ptr) :=
if ogg_stream_check os then mret (-1, os) else
let os := pagein_returned os in

if negb (ogg_page_serialno hdr =? os_serialno os) then mret (-1, os) else
if 0 <? ogg_page_version hdr then mret (-1, os) else
' (r, os) <- os_lacing_expand os (znth hdr 26 + 1) ;;
if negb (r =? 0) then mret (-1, os) else
let os := pagein_unroll os (ogg_page_pageno hdr) in
let '(bos, segptr, skipped) := pagein_skip os hdr in
let bodysize := zlength body - skipped in

' (r, os) <- (if negb (bodysize =? 0) then
' (r, os) <- os_body_expand os bodysize ;;
if negb (r =? 0) then mret (r, os)
else mret (0, pagein_body os body skipped bodysize)
else mret (0, os)) ;;
if negb (r =? 0) then mret (-1, os) else
mret (0, pagein_segments os hdr bos segptr).

Definition ogg_stream_reset (os : stream_st ptr) : stream_st ptr :=
mkStream (os_body_data os) [] (os_body_storage os) 0 0
(os_lacing_vals os) [] (os_granule_vals os) [] (os_lacing_storage os) 0 0 0
0 0 0 (os_serialno os) (-1) 0 0.

Definition ogg_stream_reset_serialno (os : stream_st ptr) (serialno : Z) : Z * stream_st ptr :=
if ogg_stream_check os then (-1, os)
else let os := ogg_stream_reset os in
(0, mkStream (os_body_data os) (os_body os) (os_body_storage os) (os_body_fill os) (os_body_returned os)
(os_lacing_vals os) (os_lacing os) (os_granule_vals os) (os_granules os)
(os_lacing_storage os) (os_lacing_fill os) (os_lacing_packet os) (os_lacing_returned os)
(os_header_fill os) (os_e_o_s os) (os_b_o_s os) serialno (os_pageno os) (os_packetno os) (os_granulepos os)).

Fixpoint gather255 (size : Z) (rest : list Z) (eos bytes n : Z) : option (Z * Z * Z) :=
if size =? 255 then
match rest with
| [] => None
| val :: rest' =>
let size := Z.land val 255 in
let eos := if negb (Z.land val 512 =? 0) then 512 else eos in
gather255 size rest' eos (bytes + size) (n + 1)
end
else Some (n, eos, bytes).

Definition packetout (os : stream_st ptr) : option ((Z * option packet) * stream_st ptr) :=
let ptr := os_lacing_returned os in
if os_lacing_packet os <=? ptr then Some ((0, None), os) else
let v := znth (os_lacing os) ptr in
if negb (Z.land v 1024 =? 0) then
Some ((-1, None),
set_tail (set_lacing os (os_lacing os) (os_granules os) (os_lacing_storage os) (os_lacing_fill os)
(os_lacing_packet os) (ptr + 1))
(os_e_o_s os) (os_pageno os) (os_packetno os + 1))
else
let size := Z.land v 255 in
match gather255 size (zdrop (ptr + 1) (os_lacing os)) (Z.land v 512) size 0 with
| None => None
| Some (n, eos, bytes) =>
let ptr' := ptr + n in
let op := mkPacket (os_body_returned os) bytes (Z.land v 256) eos (znth (os_granules os) ptr') (os_packetno os) in
Some ((1, Some op),
mkStream (os_body_data os) (os_body os) (os_body_storage os) (os_body_fill os) (os_body_returned os + bytes)
(os_lacing_vals os) (os_lacing os) (os_granule_vals os) (os_granules os)
(os_lacing_storage os) (os_lacing_fill os) (os_lacing_packet os) (ptr' + 1)
(os_header_fill os) (os_e_o_s os) (os_b_o_s os) (os_serialno os) (os_pageno os)
(os_packetno os + 1) (os_granulepos os))
end.

Definition ogg_stream_packetout (os : stream_st ptr) : option ((Z * option packet) * stream_st ptr) :=
if ogg_stream_check os then Some ((0, None), os) else packetout os.

End Ogg.

Lemma find_byte_range : forall c l i j, find_byte c l i = Some j -> i <= j < i + zlength l.
Proof.
intros c l. induction l as [|b l IH]; intros i j H; cbn in H; [discriminate|].
rewrite zlength_cons. destruct (b =? c).
- inversion H; subst. pose proof (zlength_nonneg l). lia.
- apply IH in H. lia.
Qed.
