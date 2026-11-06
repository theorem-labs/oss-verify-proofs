(* The shared pure model of reac-pw/fuzz_link: one spec for the harness's own reader and for the
   library's, so a walk of either side proves it computes THIS spec and the two agree by
   construction.

   Sources: projects/reac-pw/fuzz_link/source/{fuzz_link.c,fuzz.h,netlink.h} and the library under
   test src/{reac_link_alias.c,reac_served_mark.c} (upstream f86a30a3).

   Nothing here mentions a machine state, an image or an address: the file is pure, and the UBSan
   build's lib/U/Prog/link_spec.v re-exports it, so both builds speak of the same model. The byte
   OFFSETS of the three structures are here (they are the same in both builds); the BASE addresses
   are per build and live in lib/Prog/link_mem.v and lib/U/Prog/link_mem.v. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Import ListNotations.
Open Scope Z_scope.

(* ==========================================================================
   1. Constants of the grammar and of the policy (netlink.h, fuzz_link.c,
      reac_served_mark.h). Each is the value the two images hold.
   ========================================================================== *)

Definition NL_HDR : Z := 16.
Definition NL_ERR_BODY : Z := 20.
Definition RTA_HDR : Z := 4.
Definition IFI_LEN : Z := 16.
Definition NL_DONE : Z := 3.
Definition NL_ERROR : Z := 2.
Definition RTM_NEWLINK : Z := 16.
Definition RTM_GETLINK : Z := 18.
Definition IFLA_IFNAME : Z := 3.
Definition IFLA_LINKINFO : Z := 18.
Definition IFLA_IFALIAS : Z := 20.
Definition INFO_KIND : Z := 1.
Definition ALIAS_MAX : Z := 256.
Definition MARKS_MAX : Z := 32.
Definition MARK_LEN : Z := 16.
Definition NL_FD : Z := 7.
Definition NL_CHUNKS : Z := 64.
Definition NL_CHUNK_MAX : Z := 4096.
Definition NL_SENT_MAX : Z := 16.
Definition NL_SENT_LEN : Z := 512.
Definition OPS_MAX : Z := 48.
Definition RC_FAILS : Z := 1000000.
Definition GUARD_BYTE : Z := 0x5a.
Definition F_REQUEST : Z := 1.
Definition F_ACK : Z := 4.
Definition KIND_CAP : Z := 32.      (* char kind[32] in model_mark and reac_served_mark *)

(* errno numbers, as the images hold them *)
Definition E_PERM : Z := 1.
Definition E_INTR : Z := 4.
Definition E_IO : Z := 5.
Definition E_AGAIN : Z := 11.
Definition E_NODEV : Z := 19.
Definition E_INVAL : Z := 22.
Definition E_MFILE : Z := 24.
Definition E_NAMETOOLONG : Z := 36.
Definition E_OPNOTSUPP : Z := 95.
Definition E_NOBUFS : Z := 105.
Definition E_CONNREFUSED : Z := 111.
Definition E_NOTRECOVERABLE : Z := 131.

(* nl_errno.e, netlink.h:159: the 24 bytes of the .rodata object nl_errno.e, read from both pinned
   images (plain and ubsan hold 105, 4, 11, 1, 24, 111). *)
Definition nl_errno_tab : list Z := [E_NOBUFS; E_INTR; E_AGAIN; E_PERM; E_MFILE; E_CONNREFUSED].
Definition nl_errno (b : Z) : Z := nth (Z.to_nat (b mod 6)) nl_errno_tab 0.

(* enum reac_served_verdict, reac_served_mark.h:39-44 *)
Definition V_MARK : Z := 0.
Definition V_OURS : Z := 1.
Definition V_LEAVE_VLAN : Z := 2.
Definition V_LEAVE_HOST : Z := 3.

(* The two policy strings, as byte lists without their NUL. *)
Definition S_PREFIX : list byte := map (Z_to_bv 8) [114; 101; 97; 99; 45; 112; 119; 58].
Definition S_SERVED : list byte :=
  map (Z_to_bv 8) [114; 101; 97; 99; 45; 112; 119; 58; 115; 101; 114; 118; 101; 100].
Definition S_VLAN : list byte := map (Z_to_bv 8) [118; 108; 97; 110].

(* ==========================================================================
   2. Byte reading and the text cut
   ========================================================================== *)

Definition bz (b : byte) : Z := bv_unsigned b.
Definition zb (z : Z) : byte := Z_to_bv 8 z.

Definition byte_eqb (a b : byte) : bool := bz a =? bz b.
Fixpoint bl_eqb (l1 l2 : list byte) : bool :=
  match l1, l2 with
  | [], [] => true
  | a :: l1', b :: l2' => byte_eqb a b && bl_eqb l1' l2'
  | _, _ => false
  end.

(* `n` bytes of `c` from `off`, little-endian; the walks below only ever read inside the chunk. *)
Definition slice (c : list byte) (off n : Z) : list byte :=
  firstn (Z.to_nat n) (skipn (Z.to_nat off) c).
Definition rdn (c : list byte) (off n : Z) : Z := bytes_le_to_Z (slice c off n).
Definition rd16 (c : list byte) (off : Z) : Z := rdn c off 2.
Definition rd32 (c : list byte) (off : Z) : Z := rdn c off 4.
(* an int32 read, as `(int32_t)nl_rd32(...)` in talk and `err->error` in nl_talk *)
Definition rd32s (c : list byte) (off : Z) : Z :=
  let v := rd32 c off in if v <? 2 ^ 31 then v else v - 2 ^ 32.

(* NL_ALIGN(n) = ((n)+3u) & ~3u, and RTA_ALIGN / NLMSG_ALIGN, for the 0 <= n < 2^32-3 the walks use *)
Definition nl_align (n : Z) : Z := 4 * ((n + 3) / 4).

(* strnlen over a payload: the index of its first NUL, or its whole length. This is BOTH
   strnlen(s, RTA_PAYLOAD(a)) of copy_attr (reac_link_alias.c:31) and the `while (k < n && d[k]) k++`
   of take_text (fuzz_link.c:321-323). *)
Fixpoint nul_at (l : list byte) : nat :=
  match l with [] => 0%nat | b :: l' => if bz b =? 0 then 0%nat else S (nul_at l') end.

(* The C string a byte list holds: its bytes before the first NUL. *)
Definition cstr (l : list byte) : list byte := firstn (nul_at l) l.

(* The text an attribute payload puts in a buffer of `cap` bytes: cut at the NUL and at cap-1.
   copy_attr: k = strnlen(s,len); if (k >= n) k = n-1; memcpy(out,s,k); out[k] = 0.
   take_text: k = first NUL in n; if (k > cap-1) k = cap-1; memcpy(out,d,k); out[k] = 0.
   The two are the same function. The call is a no-op when out is NULL or cap is 0. *)
Definition cut_text (pay : list byte) (cap : Z) : list byte :=
  firstn (Z.to_nat (Z.min (Z.of_nat (nul_at pay)) (cap - 1))) pay.

(* The C string left in a buffer of cap bytes by a sequence of attribute writes: the LAST write
   decides it, and no write at all leaves what the caller put there (model_read and
   reac_link_alias_read both store a NUL at [0] first, so that is the empty string). *)
Definition text_of_attr (o : option (list byte)) (cap : Z) : list byte :=
  match o with None => [] | Some pay => cut_text pay cap end.

(* ==========================================================================
   3. The netlink walk: ONE spec for talk (fuzz_link.c:334-384) and for nl_talk
      (reac_link_alias.c:39-93).

      Both walk the SAME bytes with the SAME tests:
        message: left >= 16, 16 <= len <= left  (signed in both: nl_msg's cast to unsigned long is
                 after the signed `*left < NL_HDR` test, and NLMSG_OK's `len` is a signed ssize_t);
        attribute: left >= 4, 4 <= len <= left (signed in both);
        step: off += ALIGN(len), left -= ALIGN(len).
      The reader's buffer holds the chunk at [0, n) and nothing the walk reaches past it: the fake
      kernel's trailing NLMSG_ERROR messages (netlink.h:120-134) lie beyond `n`, which bounds both
      walks. They are what makes a reader that walks too far answer -ENOTRECOVERABLE.
   ========================================================================== *)

Record attrs : Type := Attrs { a_kind : option (list byte); a_alias : option (list byte) }.
Definition no_attrs : attrs := Attrs None None.

(* the attributes inside one IFLA_LINKINFO: the LAST IFLA_INFO_KIND wins *)
Fixpoint kind_scan (fuel : nat) (c : list byte) (off left : Z) (k : option (list byte))
  : option (list byte) :=
  match fuel with
  | O => k
  | S f =>
      if left <? RTA_HDR then k else
      let l := rd16 c off in
      if (l <? RTA_HDR) || (left <? l) then k else
      let t := rd16 c (off + 2) in
      let k' := if t =? INFO_KIND then Some (slice c (off + RTA_HDR) (l - RTA_HDR)) else k in
      kind_scan f c (off + nl_align l) (left - nl_align l) k'
  end.

(* the attributes of one RTM_NEWLINK: the LAST IFLA_IFALIAS and the LAST IFLA_INFO_KIND win *)
Fixpoint attr_scan (fuel : nat) (c : list byte) (off left : Z) (a : attrs) : attrs :=
  match fuel with
  | O => a
  | S f =>
      if left <? RTA_HDR then a else
      let l := rd16 c off in
      if (l <? RTA_HDR) || (left <? l) then a else
      let t := rd16 c (off + 2) in
      let a' :=
        if t =? IFLA_IFALIAS
        then Attrs (a_kind a) (Some (slice c (off + RTA_HDR) (l - RTA_HDR)))
        else if t =? IFLA_LINKINFO
             then Attrs (kind_scan f c (off + RTA_HDR) (l - RTA_HDR) (a_kind a)) (a_alias a)
             else a in
      attr_scan f c (off + nl_align l) (left - nl_align l) a'
  end.

(* what one chunk answers *)
Inductive nlv : Type :=
| NlNone                      (* the walk ended: take the next chunk *)
| NlShort                     (* an NLMSG_ERROR too short to hold its code: -EIO *)
| NlErr (code : Z)            (* an NLMSG_ERROR: its code (0 is the ACK) *)
| NlLink (a : attrs).         (* the first RTM_NEWLINK: its kind and alias *)

Fixpoint msg_scan (fuel : nat) (c : list byte) (off left : Z) : nlv :=
  match fuel with
  | O => NlNone
  | S f =>
      if left <? NL_HDR then NlNone else
      let ml := rd32 c off in
      if (ml <? NL_HDR) || (left <? ml) then NlNone else
      let ty := rd16 c (off + 4) in
      if ty =? NL_ERROR
      then (if ml <? NL_HDR + NL_ERR_BODY then NlShort else NlErr (rd32s c (off + NL_HDR)))
      else if ty =? RTM_NEWLINK
           then NlLink (attr_scan f c (off + NL_HDR + IFI_LEN) (ml - NL_HDR - IFI_LEN) no_attrs)
           else msg_scan f c (off + nl_align ml) (left - nl_align ml)
  end.

(* Every message takes at least NL_HDR = 16 bytes, so `length c` steps are more than enough. *)
Definition chunk_walk (c : list byte) : nlv :=
  msg_scan (S (length c)) c 0 (Z.of_nat (length c)).

(* the loop over chunks: recv hands out chunk `i`, then `i+1`, ... *)
Fixpoint chunk_loop (fuel : nat) (cs : list (list byte)) (i : nat) : nlv * nat :=
  match fuel with
  | O => (NlNone, i)
  | S f =>
      match nth_error cs i with
      | None => (NlNone, i)
      | Some c => match chunk_walk c with
                  | NlNone => chunk_loop f cs (S i)
                  | v => (v, S i)
                  end
      end
  end.

(* ==========================================================================
   4. One exchange. `talk` and `nl_talk` differ in exactly one place: the code of an
      NLMSG_ERROR. nl_talk answers it raw; talk answers RC_FAILS for a positive one, because the
      kernel cannot give a positive error and the harness then claims only that the reader failed
      (fuzz_link.c:76-78, same_rc at :472-475).
   ========================================================================== *)

(* The part of the fake kernel one exchange reads: the chunk queue, the cursor, and the three
   errnos. socket_errno and send_errno are each used once and cleared. *)
Record kstate : Type := Kst {
  k_chunks : list (list byte);
  k_next : nat;
  k_end : Z;
  k_sock : Z;
  k_send : Z
}.

(* the raw answer: what nl_talk returns, plus the attributes seen and the state after *)
Definition talk_core (K : kstate) : Z * attrs * kstate :=
  if negb (k_sock K =? 0)
  then (- k_sock K, no_attrs, Kst (k_chunks K) (k_next K) (k_end K) 0 (k_send K))
  else if negb (k_send K =? 0)
  then (- k_send K, no_attrs, Kst (k_chunks K) (k_next K) (k_end K) 0 0)
  else
    let '(v, j) := chunk_loop (S (length (k_chunks K))) (k_chunks K) (k_next K) in
    let K' := Kst (k_chunks K) j (k_end K) 0 0 in
    match v with
    | NlNone => (- k_end K, no_attrs, K')
    | NlShort => (- E_IO, no_attrs, K')
    | NlErr code => (code, no_attrs, K')
    | NlLink a => (0, a, K')
    end.

(* a request is owed only when neither failure came first (talk: `owe` runs after both tests;
   nl_talk: fuzz_send records only when it does not fail) *)
Definition talk_owes (K : kstate) : bool := (k_sock K =? 0) && (k_send K =? 0).

Definition norm_rc (rc : Z) : Z := if 0 <? rc then RC_FAILS else rc.
Definition same_rc (got want : Z) : bool :=
  if want =? RC_FAILS then negb (got =? 0) else got =? want.

(* the library's code, and the harness's *)
Definition talk_rc_lib (K : kstate) : Z := fst (fst (talk_core K)).
Definition talk_rc_model (K : kstate) : Z := norm_rc (talk_rc_lib K).
Definition talk_attrs (K : kstate) : attrs := snd (fst (talk_core K)).
Definition talk_after (K : kstate) : kstate := snd (talk_core K).

(* ==========================================================================
   5. The request bytes an operation owes
      req_head (fuzz_link.c:305-316) against the two `struct { nlmsghdr; ifinfomsg; ... } req`
      of reac_link_alias.c:105-117 and :131-147. Byte for byte the same:
        [0,4) len  [4,6) type  [6,8) flags  [8,12) seq=1  [12,16) pid=0
        [16] family=0 [17] pad=0 [18,20) type=0 [20,24) index [24,28) flags=0 [28,32) change=0
   ========================================================================== *)

Definition zeros (n : Z) : list byte := repeat (zb 0) (Z.to_nat n).

Definition req_head (len ty fl idx : Z) : list byte :=
  Z_to_le_bytes 4 len ++ Z_to_le_bytes 2 ty ++ Z_to_le_bytes 2 fl ++ Z_to_le_bytes 4 1
  ++ zeros 4 ++ zeros 4 ++ Z_to_le_bytes 4 idx ++ zeros (len - 24).

(* the RTM_GETLINK a read sends: 32 bytes *)
Definition req_read (idx : Z) : list byte := req_head 32 RTM_GETLINK F_REQUEST idx.

(* the RTM_NEWLINK a write sends: the header, then one IFLA_IFALIAS of `alias`, then the padding
   NL_ALIGN leaves (both sides memset the whole request to 0 before writing). *)
Definition req_write (idx : Z) (alias : list byte) : list byte :=
  let alen := Z.of_nat (length alias) in
  let len := 32 + nl_align (RTA_HDR + alen) in
  Z_to_le_bytes 4 len ++ Z_to_le_bytes 2 RTM_NEWLINK ++ Z_to_le_bytes 2 (F_REQUEST + F_ACK)
  ++ Z_to_le_bytes 4 1 ++ zeros 4 ++ zeros 4 ++ Z_to_le_bytes 4 idx ++ zeros 8
  ++ Z_to_le_bytes 2 (RTA_HDR + alen) ++ Z_to_le_bytes 2 IFLA_IFALIAS
  ++ alias ++ zeros (nl_align (RTA_HDR + alen) - RTA_HDR - alen).

(* the request list an operation owes; both `owe` (fuzz_link.c:296-303) and fuzz_send
   (netlink.h:98-103) stop at NL_SENT_MAX *)
Definition owe (reqs : list (list byte)) (r : list byte) : list (list byte) :=
  if Z.of_nat (length reqs) <? NL_SENT_MAX then reqs ++ [r] else reqs.

(* ==========================================================================
   6. The interface table and the index lookup
      index_of (fuzz_link.c:111-118) and fuzz_if_nametoindex (netlink.h:148-154) are the same code
      over the same table (the donor map's finding: byte-identical in both builds).
   ========================================================================== *)

Fixpoint index_of (tab : list (list byte * Z)) (nm : list byte) : Z :=
  match tab with
  | [] => 0
  | (n, i) :: tab' => if bl_eqb n nm then i else index_of tab' nm
  end.

(* ==========================================================================
   7. The reader's two doors
      model_read (fuzz_link.c:386-401) against reac_link_alias_read (reac_link_alias.c:95-119),
      model_write (:403-421) against reac_link_alias_write (:121-149).
      `nm = None` is a NULL name; `nm = Some s` is the C string s.
   ========================================================================== *)

Record rres : Type := Rres {
  r_rc : Z;                      (* the code the reader answers *)
  r_kind : list byte;            (* the C string left in `kind` *)
  r_alias : list byte;           (* the C string left in `alias` *)
  r_reqs : list (list byte);     (* the requests owed, appended *)
  r_state : kstate
}.

(* the part common to both sides; `norm` is applied by the model only *)
Definition read_core (tab : list (list byte * Z)) (nm : option (list byte))
                     (kc ac : Z) (reqs : list (list byte)) (K : kstate) : rres :=
  match nm with
  | None => Rres (- E_INVAL) [] [] reqs K
  | Some s =>
      if Nat.eqb (length s) 0 then Rres (- E_INVAL) [] [] reqs K
      else
        let idx := index_of tab s in
        if idx =? 0 then Rres (- E_NODEV) [] [] reqs K
        else
          let reqs' := if talk_owes K then owe reqs (req_read idx) else reqs in
          let a := talk_attrs K in
          Rres (talk_rc_lib K)
               (if kc <? 1 then [] else text_of_attr (a_kind a) kc)
               (if ac <? 1 then [] else text_of_attr (a_alias a) ac)
               reqs' (talk_after K)
  end.

Definition read_lib (tab : list (list byte * Z)) (nm : option (list byte)) (kc ac : Z)
                    (reqs : list (list byte)) (K : kstate) : rres := read_core tab nm kc ac reqs K.
Definition read_model (tab : list (list byte * Z)) (nm : option (list byte)) (kc ac : Z)
                      (reqs : list (list byte)) (K : kstate) : rres :=
  let r := read_core tab nm kc ac reqs K in
  Rres (norm_rc (r_rc r)) (r_kind r) (r_alias r) (r_reqs r) (r_state r).

Record wres : Type := Wres {
  w_rc : Z;
  w_reqs : list (list byte);
  w_state : kstate
}.

Definition write_core (tab : list (list byte * Z)) (nm al : option (list byte))
                      (reqs : list (list byte)) (K : kstate) : wres :=
  match nm, al with
  | None, _ => Wres (- E_INVAL) reqs K
  | _, None => Wres (- E_INVAL) reqs K
  | Some s, Some a =>
      if Nat.eqb (length s) 0 then Wres (- E_INVAL) reqs K
      else if ALIAS_MAX <=? Z.of_nat (length a) then Wres (- E_NAMETOOLONG) reqs K
      else
        let idx := index_of tab s in
        if idx =? 0 then Wres (- E_NODEV) reqs K
        else
          let reqs' := if talk_owes K then owe reqs (req_write idx a) else reqs in
          Wres (talk_rc_lib K) reqs' (talk_after K)
  end.

Definition write_lib (tab : list (list byte * Z)) (nm al : option (list byte))
                     (reqs : list (list byte)) (K : kstate) : wres := write_core tab nm al reqs K.
Definition write_model (tab : list (list byte * Z)) (nm al : option (list byte))
                       (reqs : list (list byte)) (K : kstate) : wres :=
  let r := write_core tab nm al reqs K in Wres (norm_rc (w_rc r)) (w_reqs r) (w_state r).

(* ==========================================================================
   8. The verdict
      model_decide (fuzz_link.c:423-431) and reac_served_decide (reac_served_mark.c:26-36) are the
      same code (the donor map's finding), so ONE spec. `None` is a NULL pointer.
   ========================================================================== *)

(* strncmp(alias, "reac-pw:", 8) == 0 *)
Definition has_prefix (s : list byte) : bool := bl_eqb (firstn 8 s) S_PREFIX.

Definition decide (kind alias : option (list byte)) : Z :=
  match alias with
  | Some a =>
      if negb (Nat.eqb (length a) 0)
      then (if has_prefix a then V_OURS else V_LEAVE_HOST)
      else match kind with
           | Some k => if bl_eqb k S_VLAN then V_LEAVE_VLAN else V_MARK
           | None => V_MARK
           end
  | None =>
      match kind with
      | Some k => if bl_eqb k S_VLAN then V_LEAVE_VLAN else V_MARK
      | None => V_MARK
      end
  end.

(* ==========================================================================
   9. The marks
      remember (reac_served_mark.c:38-47) and model_remember (fuzz_link.c:433-440) are the same:
      a linear search by strcmp over the names already kept, then snprintf into 16 bytes, which
      stores the first 15 bytes of the name and a NUL. At most 32 names are kept.
   ========================================================================== *)

Definition remember (l : list (list byte)) (nm : list byte) : list (list byte) :=
  if existsb (fun x => bl_eqb x nm) l then l
  else if Z.of_nat (length l) <? MARKS_MAX then l ++ [firstn 15 nm] else l.

(* model_mark (fuzz_link.c:442-460) against reac_served_mark (reac_served_mark.c:48-92).
   `m` is the mark list, `nm` the name. The two differ only in the normalisation of a code and in
   the lines reac_served_mark writes to its stream, which no check reads. *)
Record mres : Type := Mres {
  m_rc : Z;
  m_marks : list (list byte);
  m_reqs : list (list byte);
  m_state : kstate
}.

Definition mark_core (tab : list (list byte * Z)) (nm : option (list byte))
                     (marks : list (list byte)) (reqs : list (list byte)) (K : kstate) : mres :=
  match nm with
  | None => Mres (- E_INVAL) marks reqs K
  | Some s =>
      if Nat.eqb (length s) 0 then Mres (- E_INVAL) marks reqs K
      else
        let r := read_core tab nm KIND_CAP ALIAS_MAX reqs K in
        if negb (r_rc r =? 0) then Mres (r_rc r) marks (r_reqs r) (r_state r)
        else
          let v := decide (Some (r_kind r)) (Some (r_alias r)) in
          if v =? V_MARK
          then
            let w := write_core tab nm (Some S_SERVED) (r_reqs r) (r_state r) in
            if negb (w_rc w =? 0) then Mres (w_rc w) marks (w_reqs w) (w_state w)
            else Mres v (remember marks s) (w_reqs w) (w_state w)
          else if (v =? V_OURS) && bl_eqb (r_alias r) S_SERVED
          then Mres v (remember marks s) (r_reqs r) (r_state r)
          else Mres v marks (r_reqs r) (r_state r)
  end.

Definition mark_lib (tab : list (list byte * Z)) (nm : option (list byte))
                    (marks reqs : list (list byte)) (K : kstate) : mres :=
  mark_core tab nm marks reqs K.
Definition mark_model (tab : list (list byte * Z)) (nm : option (list byte))
                      (marks reqs : list (list byte)) (K : kstate) : mres :=
  let r := mark_core tab nm marks reqs K in
  Mres (norm_rc (m_rc r)) (m_marks r) (m_reqs r) (m_state r).

(* model_unmark (fuzz_link.c:462-473) against reac_served_unmark_all (reac_served_mark.c:94-107):
   read each mark, keep going unless the read answered 0 AND the alias is still `reac-pw:served`,
   and then write an empty alias. The list is cleared at the end. *)
Fixpoint unmark_walk (tab : list (list byte * Z)) (names : list (list byte))
                     (reqs : list (list byte)) (K : kstate) : list (list byte) * kstate :=
  match names with
  | [] => (reqs, K)
  | nm :: rest =>
      let r := read_core tab (Some nm) 0 ALIAS_MAX reqs K in
      if negb (r_rc r =? 0) then unmark_walk tab rest (r_reqs r) (r_state r)
      else if negb (bl_eqb (r_alias r) S_SERVED) then unmark_walk tab rest (r_reqs r) (r_state r)
      else
        let w := write_core tab (Some nm) (Some []) (r_reqs r) (r_state r) in
        unmark_walk tab rest (w_reqs w) (w_state w)
  end.

Definition unmark (tab : list (list byte * Z)) (names : list (list byte))
                  (reqs : list (list byte)) (K : kstate) : list (list byte) * kstate :=
  unmark_walk tab names reqs K.

(* ==========================================================================
   10. The pure facts the walks need
   ========================================================================== *)

Lemma bl_eqb_refl : forall l, bl_eqb l l = true.
Proof.
  induction l as [|b l IH]; cbn; [reflexivity|].
  unfold byte_eqb. rewrite Z.eqb_refl, IH. reflexivity.
Qed.

Lemma bl_eqb_eq : forall l1 l2, bl_eqb l1 l2 = true -> l1 = l2.
Proof.
  induction l1 as [|a l1 IH]; intros [|b l2] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [Hb Hl]. unfold byte_eqb in Hb. apply Z.eqb_eq in Hb.
  f_equal; [apply bv_eq; exact Hb | apply IH; exact Hl].
Qed.

Lemma bl_eqb_iff : forall l1 l2, bl_eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros l1 l2. split; [apply bl_eqb_eq|]. intros ->. apply bl_eqb_refl.
Qed.

(* THE AGREEMENT OF THE TWO SIDES. One spec serves both readers, so the texts and the request
   lists are equal by construction and the codes agree under the harness's own comparison. These
   are the facts the op walks of LLVMFuzzerTestOneInput use to show check_read, check_write and
   check_mark never abort. *)

Lemma same_rc_norm : forall rc, same_rc rc (norm_rc rc) = true.
Proof.
  intros rc. unfold same_rc, norm_rc.
  destruct (Z.ltb_spec 0 rc) as [Hp|Hn].
  - rewrite Z.eqb_refl. apply negb_true_iff, Z.eqb_neq. lia.
  - destruct (Z.eqb_spec rc RC_FAILS) as [->|_]; [unfold RC_FAILS in Hn; lia | apply Z.eqb_refl].
Qed.

Theorem read_agree : forall tab nm kc ac reqs K,
  let l := read_lib tab nm kc ac reqs K in
  let m := read_model tab nm kc ac reqs K in
  same_rc (r_rc l) (r_rc m) = true /\ r_kind l = r_kind m /\ r_alias l = r_alias m /\
  r_reqs l = r_reqs m /\ r_state l = r_state m.
Proof.
  intros tab nm kc ac reqs K. cbn. repeat split; try reflexivity. apply same_rc_norm.
Qed.

Theorem write_agree : forall tab nm al reqs K,
  let l := write_lib tab nm al reqs K in
  let m := write_model tab nm al reqs K in
  same_rc (w_rc l) (w_rc m) = true /\ w_reqs l = w_reqs m /\ w_state l = w_state m.
Proof.
  intros tab nm al reqs K. cbn. repeat split; try reflexivity. apply same_rc_norm.
Qed.

Theorem mark_agree : forall tab nm marks reqs K,
  let l := mark_lib tab nm marks reqs K in
  let m := mark_model tab nm marks reqs K in
  same_rc (m_rc l) (m_rc m) = true /\ m_marks l = m_marks m /\ m_reqs l = m_reqs m /\
  m_state l = m_state m.
Proof.
  intros tab nm marks reqs K. cbn. repeat split; try reflexivity. apply same_rc_norm.
Qed.

(* the two sides of a refused mark both answer -EINVAL, whichever of the three refusals it is *)
Lemma mark_refused_null : forall tab marks reqs K,
  m_rc (mark_model tab None marks reqs K) = - E_INVAL.
Proof. intros. cbn. reflexivity. Qed.

Lemma mark_refused_empty : forall tab marks reqs K,
  m_rc (mark_model tab (Some []) marks reqs K) = - E_INVAL.
Proof. intros. cbn. reflexivity. Qed.

(* THE TEXT CUT FITS THE BUFFER: this is what makes check_bounds (fuzz_link.c:556-566) never fire.
   The write touches out[0 .. k] with k <= cap-1, so the guard byte at out[cap] is untouched and
   a NUL sits inside the buffer. *)
Lemma nul_at_le : forall l, (nul_at l <= length l)%nat.
Proof.
  induction l as [|b l IH]; cbn; [lia|]. destruct (bz b =? 0); lia.
Qed.

Lemma cut_text_len : forall pay cap, 1 <= cap -> Z.of_nat (length (cut_text pay cap)) <= cap - 1.
Proof.
  intros pay cap Hc. unfold cut_text. rewrite length_firstn.
  pose proof (nul_at_le pay). lia.
Qed.

Lemma cut_text_prefix : forall pay cap, firstn (length (cut_text pay cap)) pay = cut_text pay cap.
Proof.
  intros pay cap. unfold cut_text. rewrite length_firstn.
  rewrite <- firstn_firstn, firstn_all. reflexivity.
Qed.

Lemma firstn_nul_free : forall l k b, (k <= nul_at l)%nat -> In b (firstn k l) -> bz b <> 0.
Proof.
  induction l as [|a l IH]; intros k b Hk Hin.
  - destruct k; cbn in Hin; contradiction.
  - destruct k as [|k]; cbn in Hin; [contradiction|].
    cbn in Hk. destruct (Z.eqb_spec (bz a) 0) as [E|NE]; [lia|].
    destruct Hin as [->|Hin]; [exact NE|]. apply (IH k b); [lia | exact Hin].
Qed.

Lemma cut_text_nonul : forall pay cap b, In b (cut_text pay cap) -> bz b <> 0.
Proof.
  intros pay cap b Hin. unfold cut_text in Hin.
  apply (firstn_nul_free pay (Z.to_nat (Z.min (Z.of_nat (nul_at pay)) (cap - 1))) b);
    [| exact Hin].
  pose proof (Z.le_min_l (Z.of_nat (nul_at pay)) (cap - 1)). lia.
Qed.

(* THE MARK LIST STAYS SHORT AND WITHOUT A DUPLICATE. `names_short` holds for link: every name an
   operation can name is a g_names entry ("nl0".."nl63", 4 bytes at most) or an `odd` entry
   ("enp131s0.33", 11 bytes at most), so no name reaches the 15-byte cut. *)
Definition names_short (l : list (list byte)) : Prop :=
  Forall (fun x => (length x <= 15)%nat) l.

Lemma remember_len : forall l nm,
  Z.of_nat (length l) <= MARKS_MAX -> Z.of_nat (length (remember l nm)) <= MARKS_MAX.
Proof.
  intros l nm Hl. unfold remember.
  destruct (existsb (fun x => bl_eqb x nm) l); [exact Hl|].
  destruct (Z.ltb_spec (Z.of_nat (length l)) MARKS_MAX) as [Hs|Hs]; [|exact Hl].
  rewrite length_app. cbn [length]. lia.
Qed.

Lemma remember_short : forall l nm, names_short l -> names_short (remember l nm).
Proof.
  intros l nm Hs. unfold remember.
  destruct (existsb (fun x => bl_eqb x nm) l); [exact Hs|].
  destruct (Z.ltb_spec (Z.of_nat (length l)) MARKS_MAX); [|exact Hs].
  apply Forall_app. split; [exact Hs|].
  constructor; [| constructor]. rewrite length_firstn. lia.
Qed.

(* "each name once". Stated here and not with NoDup: both List's and stdpp's NoDup are in scope
   under these Requires, and the two have different constructor names. *)
Fixpoint ml_nodup (l : list (list byte)) : Prop :=
  match l with [] => True | x :: l' => ~ In x l' /\ ml_nodup l' end.

Lemma ml_nodup_snoc : forall l x, ml_nodup l -> ~ In x l -> ml_nodup (l ++ [x]).
Proof.
  induction l as [|a l IH]; intros x Hd Hin; simpl.
  - split; [exact Hin | exact I].
  - destruct Hd as [Ha Hl]. split.
    + rewrite in_app_iff. intros [H|H]; [contradiction|].
      simpl in H. destruct H as [H|H]; [|contradiction].
      apply Hin. left. symmetry. exact H.
    + apply IH; [exact Hl | intros H; apply Hin; right; exact H].
Qed.

Lemma remember_nodup : forall l nm,
  ml_nodup l -> (length nm <= 15)%nat -> ml_nodup (remember l nm).
Proof.
  intros l nm Hd Hn. unfold remember.
  destruct (existsb (fun x => bl_eqb x nm) l) eqn:E; [exact Hd|].
  destruct (Z.ltb_spec (Z.of_nat (length l)) MARKS_MAX); [|exact Hd].
  rewrite firstn_all2 by exact Hn.
  apply ml_nodup_snoc; [exact Hd|].
  intros Hin.
  assert (Htrue : existsb (fun x => bl_eqb x nm) l = true).
  { apply existsb_exists. exists nm. split; [exact Hin | apply bl_eqb_refl]. }
  rewrite E in Htrue. discriminate.
Qed.

(* EVERY RESULT IS IN RANGE. The verdict is one of the four of the enum, and the codes the two
   readers answer are the ones the checks compare. *)
Lemma decide_range : forall k a, V_MARK <= decide k a <= V_LEAVE_HOST.
Proof.
  intros k a. unfold decide, V_MARK, V_OURS, V_LEAVE_VLAN, V_LEAVE_HOST.
  destruct a as [s|]; [destruct (negb (Nat.eqb (length s) 0))|].
  - destruct (has_prefix s); lia.
  - destruct k as [x|]; [destruct (bl_eqb x S_VLAN)|]; lia.
  - destruct k as [x|]; [destruct (bl_eqb x S_VLAN)|]; lia.
Qed.

Lemma decide_cases : forall k a,
  decide k a = V_MARK \/ decide k a = V_OURS \/ decide k a = V_LEAVE_VLAN \/
  decide k a = V_LEAVE_HOST.
Proof.
  intros k a. unfold decide.
  destruct a as [s|]; [destruct (negb (Nat.eqb (length s) 0))|].
  - destruct (has_prefix s); tauto.
  - destruct k as [x|]; [destruct (bl_eqb x S_VLAN)|]; tauto.
  - destruct k as [x|]; [destruct (bl_eqb x S_VLAN)|]; tauto.
Qed.

(* `owe` never grows past the kernel's own ring: check_requests compares the two lists entry by
   entry, so both must stop at the same bound. *)
Lemma owe_len : forall reqs r,
  Z.of_nat (length reqs) <= NL_SENT_MAX -> Z.of_nat (length (owe reqs r)) <= NL_SENT_MAX.
Proof.
  intros reqs r H. unfold owe.
  destruct (Z.ltb_spec (Z.of_nat (length reqs)) NL_SENT_MAX) as [Hs|Hs]; [|exact H].
  rewrite length_app. cbn [length]. lia.
Qed.

(* the request a read sends is 32 bytes, and the one a write sends is under the kernel's 512-byte
   record, so neither side's `memcpy` of min(len, 512) loses a byte *)
Lemma len_le_bytes : forall n z, length (Z_to_le_bytes n z) = n.
Proof. induction n as [|n IH]; intros z; cbn; [reflexivity | now rewrite IH]. Qed.

Lemma req_read_len : forall idx, length (req_read idx) = 32%nat.
Proof.
  intros idx. unfold req_read, req_head, zeros.
  rewrite !length_app, !len_le_bytes, !repeat_length. reflexivity.
Qed.

Lemma nl_align_le : forall n, 0 <= n -> n <= nl_align n <= n + 3.
Proof. intros n Hn. unfold nl_align. Z.div_mod_to_equations. lia. Qed.

Lemma req_write_len : forall idx alias,
  Z.of_nat (length alias) < ALIAS_MAX ->
  Z.of_nat (length (req_write idx alias)) = 32 + nl_align (RTA_HDR + Z.of_nat (length alias)).
Proof.
  intros idx alias Ha. unfold req_write, zeros.
  rewrite !length_app, !len_le_bytes, !repeat_length.
  pose proof (nl_align_le (RTA_HDR + Z.of_nat (length alias))) as Hal.
  unfold RTA_HDR in *. unfold ALIAS_MAX in Ha. lia.
Qed.

Lemma req_write_small : forall idx alias,
  Z.of_nat (length alias) < ALIAS_MAX ->
  Z.of_nat (length (req_write idx alias)) <= NL_SENT_LEN.
Proof.
  intros idx alias Ha. rewrite req_write_len by exact Ha.
  pose proof (nl_align_le (RTA_HDR + Z.of_nat (length alias))) as Hal.
  unfold RTA_HDR, ALIAS_MAX, NL_SENT_LEN in *. lia.
Qed.

(* ==========================================================================
   11. The byte offsets of the three structures.
       Read from the two images (the same in both; only the base of g_nl moves).
   ========================================================================== *)

(* struct nl_kernel (netlink.h:48-68), 271992 bytes *)
Definition NK_CHUNK : Z := 0.
Definition NK_CHUNK_LEN : Z := 262144.
Definition NK_N_CHUNKS : Z := 262656.
Definition NK_NEXT : Z := 262660.
Definition NK_END_ERRNO : Z := 262664.
Definition NK_SOCKET_ERRNO : Z := 262668.
Definition NK_SEND_ERRNO : Z := 262672.
Definition NK_OPEN : Z := 262676.
Definition NK_OPENED : Z := 262680.
Definition NK_CLOSED : Z := 262684.
Definition NK_MISUSE : Z := 262688.
Definition NK_SENT : Z := 262692.
Definition NK_SENT_LEN : Z := 270888.
Definition NK_N_SENT : Z := 271016.
Definition NK_IF_NAME : Z := 271024.
Definition NK_IF_INDEX : Z := 271664.
Definition NK_N_IF : Z := 271984.
Definition NK_SIZE : Z := 271992.

(* struct model (fuzz_link.c:287-298), 8856 bytes: the block calloc(1, 8856) hands out *)
Definition MD_SOCKET_ERRNO : Z := 0.
Definition MD_SEND_ERRNO : Z := 4.
Definition MD_NEXT : Z := 8.
Definition MD_REQ : Z := 12.
Definition MD_REQ_LEN : Z := 8208.
Definition MD_N_REQ : Z := 8336.
Definition MD_MARK : Z := 8340.
Definition MD_N_MARK : Z := 8852.
Definition MD_SIZE : Z := 8856.

(* struct reac_served_marks (reac_served_mark.h:49-52), 516 bytes: calloc(1, 516) *)
Definition MK_N : Z := 0.
Definition MK_NAME : Z := 4.
Definition MK_SIZE : Z := 516.

(* g_names (64 x 8 bytes) and the two pointer tables *)
Definition G_NAMES_SIZE : Z := 512.
Definition ODD_N : Z := 6.
Definition TEXTS_N : Z := 11.
Definition SAID_SIZE : Z := 4096.
Definition LONG_ALIAS_SIZE : Z := 301.

(* ==========================================================================
   12. Pure accessors over the raw bytes of the three structures.
       A contract gives ONE `u8arr` premise for a structure and then speaks of its fields through
       these, so every store a walk makes is an `upd_bytes` of the same byte list.
   ========================================================================== *)

Definition fld_u32 (bs : list byte) (off : Z) : Z := rdn bs off 4.
Definition fld_u64 (bs : list byte) (off : Z) : Z := rdn bs off 8.

(* struct nl_kernel *)
Definition nk_n_chunks (bs : list byte) : Z := fld_u32 bs NK_N_CHUNKS.
Definition nk_next (bs : list byte) : Z := fld_u32 bs NK_NEXT.
Definition nk_end_errno (bs : list byte) : Z := fld_u32 bs NK_END_ERRNO.
Definition nk_socket_errno (bs : list byte) : Z := fld_u32 bs NK_SOCKET_ERRNO.
Definition nk_send_errno (bs : list byte) : Z := fld_u32 bs NK_SEND_ERRNO.
Definition nk_open (bs : list byte) : Z := fld_u32 bs NK_OPEN.
Definition nk_opened (bs : list byte) : Z := fld_u32 bs NK_OPENED.
Definition nk_closed (bs : list byte) : Z := fld_u32 bs NK_CLOSED.
Definition nk_misuse (bs : list byte) : Z := fld_u32 bs NK_MISUSE.
Definition nk_n_sent (bs : list byte) : Z := fld_u32 bs NK_N_SENT.
Definition nk_n_if (bs : list byte) : Z := fld_u32 bs NK_N_IF.
Definition nk_chunk (bs : list byte) (i : Z) : list byte :=
  slice bs (NK_CHUNK + NL_CHUNK_MAX * i) (fld_u64 bs (NK_CHUNK_LEN + 8 * i)).
Definition nk_sent_one (bs : list byte) (i : Z) : list byte :=
  slice bs (NK_SENT + NL_SENT_LEN * i) (fld_u64 bs (NK_SENT_LEN + 8 * i)).
Definition nk_chunks (bs : list byte) : list (list byte) :=
  map (fun i => nk_chunk bs (Z.of_nat i)) (seq 0 (Z.to_nat (nk_n_chunks bs))).
Definition nk_sent (bs : list byte) : list (list byte) :=
  map (fun i => nk_sent_one bs (Z.of_nat i)) (seq 0 (Z.to_nat (nk_n_sent bs))).

(* the chunk queue as one exchange sees it *)
Definition nk_kstate (bs : list byte) : kstate :=
  Kst (nk_chunks bs) (Z.to_nat (nk_next bs)) (nk_end_errno bs)
      (nk_socket_errno bs) (nk_send_errno bs).

(* struct model *)
Definition md_socket_errno (bs : list byte) : Z := fld_u32 bs MD_SOCKET_ERRNO.
Definition md_send_errno (bs : list byte) : Z := fld_u32 bs MD_SEND_ERRNO.
Definition md_next (bs : list byte) : Z := fld_u32 bs MD_NEXT.
Definition md_n_req (bs : list byte) : Z := fld_u32 bs MD_N_REQ.
Definition md_n_mark (bs : list byte) : Z := fld_u32 bs MD_N_MARK.
Definition md_req_one (bs : list byte) (i : Z) : list byte :=
  slice bs (MD_REQ + NL_SENT_LEN * i) (fld_u64 bs (MD_REQ_LEN + 8 * i)).
Definition md_reqs (bs : list byte) : list (list byte) :=
  map (fun i => md_req_one bs (Z.of_nat i)) (seq 0 (Z.to_nat (md_n_req bs))).
Definition md_marks (bs : list byte) : list (list byte) :=
  map (fun i => cstr (slice bs (MD_MARK + MARK_LEN * Z.of_nat i) MARK_LEN))
      (seq 0 (Z.to_nat (md_n_mark bs))).

(* struct reac_served_marks *)
Definition mk_n (bs : list byte) : Z := fld_u32 bs MK_N.
Definition mk_names (bs : list byte) : list (list byte) :=
  map (fun i => cstr (slice bs (MK_NAME + MARK_LEN * Z.of_nat i) MARK_LEN))
      (seq 0 (Z.to_nat (mk_n bs))).

(* THE CHECKS' COMPARISONS, over the byte lists. plain_halts needs each to hold at the call site
   of its check_* function, so that the abort inside is not taken: (b) check_requests
   (requests_are, fuzz_link.c:628-639) and (h)/(i) check_marks (marks_are, :645-654). *)
Definition requests_are (kbs mbs : list byte) : Prop :=
  nk_n_sent kbs = md_n_req mbs /\
  forall i, 0 <= i < nk_n_sent kbs ->
    fld_u64 kbs (NK_SENT_LEN + 8 * i) = fld_u64 mbs (MD_REQ_LEN + 8 * i) /\
    nk_sent_one kbs i = md_req_one mbs i.

Definition marks_are (gbs mbs : list byte) : Prop :=
  mk_n gbs = md_n_mark mbs /\ mk_names gbs = md_marks mbs.

(* Every mark slot a strcmp reads holds a NUL inside its 16 bytes, so the comparison stops there.
   snprintf(name, 16, "%s", ...) always leaves one (reac_served_mark.c:45, fuzz_link.c:439), and
   calloc zeroed the whole block, so this holds of every slot of a block a run made. *)
Definition slots_terminated (bs : list byte) (base n : Z) : Prop :=
  forall i, 0 <= i < n -> (nul_at (slice bs (base + MARK_LEN * i) MARK_LEN) < Z.to_nat MARK_LEN)%nat.

Definition marks_wf (gbs : list byte) : Prop :=
  0 <= mk_n gbs <= MARKS_MAX /\ slots_terminated gbs MK_NAME (mk_n gbs).
Definition model_marks_wf (mbs : list byte) : Prop :=
  0 <= md_n_mark mbs <= MARKS_MAX /\ slots_terminated mbs MD_MARK (md_n_mark mbs).

(* struct nl_w (netlink.h:219-223): the reply the harness builds, 4112 bytes.
   uint8_t b[4096]; size_t n; int full. *)
Definition NW_B : Z := 0.
Definition NW_N : Z := 4096.
Definition NW_FULL : Z := 4104.
Definition NW_SIZE : Z := 4112.
Definition nw_n (bs : list byte) : Z := fld_u64 bs NW_N.
Definition nw_full (bs : list byte) : Z := fld_u32 bs NW_FULL.
Definition nw_bytes (bs : list byte) : list byte := slice bs NW_B (nw_n bs).

(* The fake kernel is well formed: every count is inside its array and every length inside its
   record. interfaces() and kernel() leave it so, and every own function keeps it so. *)
Definition nlk_wf (bs : list byte) : Prop :=
  0 <= nk_n_chunks bs <= NL_CHUNKS /\ 0 <= nk_next bs <= nk_n_chunks bs /\
  0 <= nk_n_sent bs <= NL_SENT_MAX /\ 0 <= nk_n_if bs <= 80 /\
  0 <= nk_open bs <= 1 /\ 0 <= nk_opened bs < 2 ^ 31 /\ 0 <= nk_closed bs < 2 ^ 31 /\
  0 <= nk_misuse bs <= 1 /\
  0 <= nk_end_errno bs < 2 ^ 31 /\ 0 <= nk_socket_errno bs < 2 ^ 31 /\
  0 <= nk_send_errno bs < 2 ^ 31 /\
  (forall i, 0 <= i < nk_n_chunks bs -> 0 <= fld_u64 bs (NK_CHUNK_LEN + 8 * i) <= NL_CHUNK_MAX) /\
  (forall i, 0 <= i < nk_n_sent bs -> 0 <= fld_u64 bs (NK_SENT_LEN + 8 * i) <= NL_SENT_LEN).

(* The model block is well formed in the same way. *)
Definition model_wf (bs : list byte) : Prop :=
  0 <= md_n_req bs <= NL_SENT_MAX /\ 0 <= md_next bs < 2 ^ 31 /\
  0 <= md_socket_errno bs < 2 ^ 31 /\ 0 <= md_send_errno bs < 2 ^ 31 /\
  (forall i, 0 <= i < md_n_req bs -> 0 <= fld_u64 bs (MD_REQ_LEN + 8 * i) <= NL_SENT_LEN) /\
  model_marks_wf bs.

(* The exchange `talk` makes: the model keeps its OWN copies of the two failures and its own
   cursor (model_begin, fuzz_link.c:668-675), and reads the chunk queue and the end errno from the
   fake kernel. `nl_talk` reads all five from the fake kernel itself, through fuzz_socket,
   fuzz_send and fuzz_recv. The two are the same state after model_begin: that is what the op
   walk shows. *)
Definition md_kstate (mbs kbs : list byte) : kstate :=
  Kst (nk_chunks kbs) (Z.to_nat (md_next mbs)) (nk_end_errno kbs)
      (md_socket_errno mbs) (md_send_errno mbs).

(* the reply writer stays a writer: its length never passes its buffer and its full flag is a flag *)
Definition nlw_wf (bs : list byte) : Prop :=
  0 <= nw_n bs <= NL_CHUNK_MAX /\ 0 <= nw_full bs <= 1.
