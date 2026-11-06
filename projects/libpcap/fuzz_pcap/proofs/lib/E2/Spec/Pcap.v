(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import String.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Fmt PcapPrelim PcapTypes PcapPure.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Record MonadOps (M : Type -> Type) := mkMonadOps {
  mo_ret : forall {A : Type}, A -> M A ;
  mo_bind : forall {A B : Type}, M A -> (A -> M B) -> M B ;
  (* [comment removed for export] *)
  mo_unr : forall {A : Type}, M A
}.
Arguments mo_ret {M} _ {A} _.
Arguments mo_bind {M} _ {A B} _ _.
Arguments mo_unr {M} _ {A}.

(* [comment removed for export] *)
Inductive stack_site :=
| SiteMagic             (* [comment removed for export] *)
| SitePcapHdrRest       (* [comment removed for export] *)
| SiteSfHdr             (* [comment removed for export] *)
| SiteDiscardBuf        (* [comment removed for export] *)
| SiteNgTotalLength     (* [comment removed for export] *)
| SiteNgByteOrderMagic  (* [comment removed for export] *)
| SiteBhdrCheckHeader   (* [comment removed for export] *)
| SiteBhdrNextPacket    (* [comment removed for export] *)
| SiteReadStage.        (* [comment removed for export] *)

(* [comment removed for export] *)
Inductive fframe :=
| FF_FOPEN_OFFLINE      (* [comment removed for export] *)
| FF_CHECK_HEADER       (* [comment removed for export] *)
| FF_NEXT_PACKET        (* [comment removed for export] *)
| FF_OFFLINE_READ       (* [comment removed for export] *)
| FF_NEXT_EX            (* [comment removed for export] *)
| FF_FMT_ERRMSG         (* [comment removed for export] *)
| FF_NG_CHECK_HEADER    (* [comment removed for export] *)
| FF_READ_BLOCK         (* [comment removed for export] *)
| FF_FUZZ_ONE_INPUT.    (* [comment removed for export] *)


(* [comment removed for export] *)
Inductive rdest (ptr : Type) : Type :=
| DHeap (q : ptr) (off : Z)
| DStack (site : stack_site) (off : Z).
Arguments DHeap {ptr} _ _.
Arguments DStack {ptr} _ _.

Record Prims (M : Type -> Type) (fh ptr : Type) := mkPrims {
  (* [comment removed for export] *)
  e_fopen_r : list Z -> M (option fh) ;
  (* [comment removed for export] *)
  e_fopen_w : list Z -> M (option fh) ;
  (* [comment removed for export] *)
  e_fclose : fh -> M unit ;
  (* [comment removed for export] *)
  e_fread : fh -> rdest ptr -> Z -> M (list Z) ;
  (* [comment removed for export] *)
  e_fwrite : fh -> list Z -> M Z ;
  (* [comment removed for export] *)
  e_ferror : fh -> M bool ;
  (* [comment removed for export] *)
  e_fileno : fh -> M Z ;
  (* [comment removed for export] *)
  e_last_errno : M Z ;
  (* [comment removed for export] *)
  e_fprintf : fh -> list (list Z) -> M unit ;
  (* [comment removed for export] *)
  e_printf : list (list Z) -> M unit ;
  e_malloc : Z -> M (option ptr) ;
  e_calloc : Z -> Z -> M (option ptr) ;
  (* [comment removed for export] *)
  e_realloc : ptr -> Z -> M (option ptr) ;
  (* [comment removed for export] *)
  e_free : ptr -> M unit ;
  (* [comment removed for export] *)
  e_mkstemp : list Z -> M (list Z * Z)%type ;
  (* [comment removed for export] *)
  e_close_fd : Z -> M Z ;
  (* [comment removed for export] *)
  e_remove : list Z -> M Z ;
  (* [comment removed for export] *)
  e_unlink : list Z -> M Z ;
  (* [comment removed for export] *)
  e_get_outfile : M (option fh) ;
  e_set_outfile : option fh -> M unit ;
  (* [comment removed for export] *)
  e_fenter : forall A : Type, fframe -> M A -> M A ;
  e_fret : forall A : Type, fframe -> A -> M A
}.
Arguments e_fopen_r {M fh ptr} _ _.      Arguments e_fopen_w {M fh ptr} _ _.
Arguments e_fclose {M fh ptr} _ _.       Arguments e_fread {M fh ptr} _ _ _ _.
Arguments e_fwrite {M fh ptr} _ _ _.     Arguments e_ferror {M fh ptr} _ _.
Arguments e_fileno {M fh ptr} _ _.       Arguments e_last_errno {M fh ptr} _.
Arguments e_fprintf {M fh ptr} _ _ _.    Arguments e_printf {M fh ptr} _ _.
Arguments e_malloc {M fh ptr} _ _.       Arguments e_calloc {M fh ptr} _ _ _.
Arguments e_realloc {M fh ptr} _ _ _.    Arguments e_free {M fh ptr} _ _.
Arguments e_mkstemp {M fh ptr} _ _.      Arguments e_close_fd {M fh ptr} _ _.
Arguments e_remove {M fh ptr} _ _.       Arguments e_unlink {M fh ptr} _ _.
Arguments e_fenter {M fh ptr} _ {A} _ _.   Arguments e_fret {M fh ptr} _ {A} _ _.
Arguments e_get_outfile {M fh ptr} _.    Arguments e_set_outfile {M fh ptr} _ _.

Declare Scope pcapm_scope.

Section PcapModel.
Context {M : Type -> Type} (MO : MonadOps M) {fh ptr : Type} (P : Prims M fh ptr).

Local Notation "x <- m ;; k" := (mo_bind MO m (fun x => k))
  (at level 100, m at next level, right associativity) : pcapm_scope.
Local Notation "' pat <- m ;; k" := (mo_bind MO m (fun x => let 'pat := x in k))
  (at level 100, pat pattern, m at next level, right associativity) : pcapm_scope.
Local Notation "m ;;; k" := (mo_bind MO m (fun _ => k))
  (at level 100, right associativity) : pcapm_scope.
Local Notation "'ret' x" := (mo_ret MO x) (at level 10) : pcapm_scope.
Local Notation "'fret' f x" := (e_fret P f x) (at level 10, f at level 0) : pcapm_scope.
Local Open Scope pcapm_scope.

#[local] Abbreviation pcap := (PcapTypes.pcap ptr fh) (only parsing).

Definition FUEL_OUT : Z := -99.

(* [comment removed for export] *)
Definition free_opt (q : option ptr) : M unit :=
  match q with None => ret tt | Some q' => e_free P q' end.

(* [comment removed for export] *)
Definition errmsg_for_errno (f : string) (args : list farg) : M (list Z) :=
  e <- e_last_errno P ;;
  e_fenter P FF_FMT_ERRMSG (
  fret FF_FMT_ERRMSG (fmt_errmsg f args e)).

(* [comment removed for export] *)
Definition read_fail_msg (fp : fh) (truncmsg : list Z) : M (list Z) :=
  e <- e_ferror P fp ;;
  if e then errmsg_for_errno "error reading dump file" [] else ret truncmsg.

(* [comment removed for export] *)
Definition PCAP_T_SIZE : Z := 648.
Definition PCAP_SF_TOTAL : Z := 664.
Definition PCAP_NG_SF_TOTAL : Z := 680.
Definition pcapint_open_offline_common (total_size : Z) : M ((list Z) + ptr) :=
  r <- e_calloc P total_size 1 ;;
  match r with
  | None => m <- errmsg_for_errno "malloc" [] ;; ret (inl m)
  | Some chunk => ret (inr chunk)
  end.

(* [comment removed for export] *)

Definition TCPDUMP_MAGIC : Z := 2712847316.            (* [comment removed for export] *)
Definition KUZNETZOV_TCPDUMP_MAGIC : Z := 2712849716.  (* [comment removed for export] *)
Definition NSEC_TCPDUMP_MAGIC : Z := 2712812621.       (* [comment removed for export] *)
Definition PCAP_TSTAMP_PRECISION_MICRO : Z := 0.
Definition PCAP_TSTAMP_PRECISION_NANO : Z := 1.

Definition is_pcap_magic (m : Z) : bool :=
  (m =? TCPDUMP_MAGIC) || (m =? KUZNETZOV_TCPDUMP_MAGIC) || (m =? NSEC_TCPDUMP_MAGIC).

(* [comment removed for export] *)
Inductive check_result :=
| CH_NotMe                 (* [comment removed for export] *)
| CH_Err (msg : list Z)    (* [comment removed for export] *)
| CH_Ok (p : pcap).

(* [comment removed for export] *)
Definition pcap_check_header (magic : list Z) (fp : fh) (precision : Z) : M check_result :=
  e_fenter P FF_CHECK_HEADER (
  let magic_int := le_of_bytes magic in
  let '(ok, magic_int, swapped) :=
    if is_pcap_magic magic_int then (true, magic_int, false)
    else let m' := bswap32 magic_int in
         if is_pcap_magic m' then (true, m', true) else (false, magic_int, false) in
  if negb ok then fret FF_CHECK_HEADER CH_NotMe else
  (* [comment removed for export] *)
  rest <- e_fread P fp (DStack SitePcapHdrRest 0) 20 ;;
  if negb (zlength rest =? 20) then
    m <- read_fail_msg fp (Msg.trunc_file_header 24 (zlength rest)) ;; fret FF_CHECK_HEADER (CH_Err m)
  else
  let version_major := if swapped then bswap16 (get_le16 rest 0) else get_le16 rest 0 in
  let version_minor := if swapped then bswap16 (get_le16 rest 2) else get_le16 rest 2 in
  (* [comment removed for export] *)
  let snaplen := if swapped then bswap32 (get_le32 rest 12) else get_le32 rest 12 in
  let linktype := if swapped then bswap32 (get_le32 rest 16) else get_le32 rest 16 in
  if negb (((version_major =? 2) && (version_minor <=? 4)) ||
           ((version_major =? 543) && (version_minor =? 0)))
  then fret FF_CHECK_HEADER (CH_Err (Msg.unsupported_pcap_version version_major version_minor))
  else if negb (Z.land linktype 67043328 (* [comment removed for export] *) =? 0)
  then fret FF_CHECK_HEADER (CH_Err (Msg.reserved_not_zero (Z.land linktype 67043328)))
  else
  r <- pcapint_open_offline_common PCAP_SF_TOTAL ;;
  match r with
  | inl m => fret FF_CHECK_HEADER (CH_Err m)
  | inr self =>
    let lt := linktype_to_dlt (Z.land linktype 65535) in            (* [comment removed for export] *)
    let lt_ext := s32 (Z.land linktype 4294901760) in               (* [comment removed for export] *)
    let snapshot := pcapint_adjust_snapshot lt snaplen in
    (* [comment removed for export] *)
    let scale := if precision =? PCAP_TSTAMP_PRECISION_MICRO then
                   Some (if magic_int =? NSEC_TCPDUMP_MAGIC then SF_SCALE_DOWN else SF_PASS_THROUGH)
                 else if precision =? PCAP_TSTAMP_PRECISION_NANO then
                   Some (if magic_int =? NSEC_TCPDUMP_MAGIC then SF_PASS_THROUGH else SF_SCALE_UP)
                 else None in
    match scale with
    | None => e_free P self ;;; fret FF_CHECK_HEADER (CH_Err (Msg.unknown_tstamp_resolution precision))
    | Some scale_type =>
      let lengths_swapped :=
        if version_major =? 2 then
          (if version_minor <? 3 then SWAPPED else if version_minor =? 3 then MAYBE_SWAPPED else NOT_SWAPPED)
        else if version_major =? 543 then SWAPPED else NOT_SWAPPED in
      let '(hdrsize, snapshot) :=
        if magic_int =? KUZNETZOV_TCPDUMP_MAGIC then
          (24, if lt =? DLT_EN10MB then (if snapshot <=? INT_MAX - 14 then snapshot + 14 else INT_MAX) else snapshot)
        else (16, snapshot) in
      let bufsize := if 2048 <? snapshot then 2048 else snapshot in
      b <- e_malloc P bufsize ;;
      match b with
      | None => e_free P self ;;; fret FF_CHECK_HEADER (CH_Err Msg.out_of_memory)
      | Some buf =>
        fret FF_CHECK_HEADER (CH_Ok (mkPcap self fp bufsize bufsize buf [] swapped version_major version_minor
                      snapshot lt lt_ext precision 0 [] hdr0
                      (PrivPcap (mkSf hdrsize lengths_swapped scale_type))))
      end
    end
  end).

(* [comment removed for export] *)
Definition grow_buffer (p : pcap) (bufsize : Z) : M (bool * pcap) :=
  r <- e_realloc P (pc_buffer p) bufsize ;;
  match r with
  | None => ret (false, set_errbuf Msg.out_of_memory p)
  | Some b => ret (true, set_buffer b bufsize bufsize (zfirstn bufsize (pc_bufdata p)) p)
  end.

(* [comment removed for export] *)
Fixpoint discard_loop (fuel : nat) (fp : fh) (caplen : Z) (bytes_to_discard bytes_read : Z)
  : M ((list Z) + unit) :=
  match fuel with
  | O => ret (inr tt)
  | S fuel' =>
    if bytes_to_discard =? 0 then ret (inr tt) else
    let bytes_to_read := if 4096 <? bytes_to_discard then 4096 else bytes_to_discard in
    got <- e_fread P fp (DStack SiteDiscardBuf 0) bytes_to_read ;;
    let amt_read := zlength got in
    let bytes_read := bytes_read + amt_read in
    if negb (amt_read =? bytes_to_read) then
      m <- read_fail_msg fp (Msg.trunc_captured_u caplen bytes_read) ;; ret (inl m)
    else discard_loop fuel' fp caplen (bytes_to_discard - amt_read) bytes_read
  end.

(* [comment removed for export] *)
Definition roundup_pow2_u32 (v : Z) : Z :=
  let n := u32 (v - 1) in
  let n := Z.lor n (Z.shiftr n 1) in
  let n := Z.lor n (Z.shiftr n 2) in
  let n := Z.lor n (Z.shiftr n 4) in
  let n := Z.lor n (Z.shiftr n 8) in
  let n := Z.lor n (Z.shiftr n 16) in
  u32 (n + 1).

Definition sf_of (p : pcap) : pcap_sf :=
  match pc_priv p with PrivPcap s => s | PrivNg _ _ => mkSf 16 NOT_SWAPPED SF_PASS_THROUGH end.

(* [comment removed for export] *)
Definition pcap_next_packet (p : pcap) : M (Z * pkthdr * pcap) :=
  e_fenter P FF_NEXT_PACKET (
  let ps := sf_of p in
  let fp := pc_rfile p in
  hb <- e_fread P fp (DStack SiteSfHdr 0) (sf_hdrsize ps) ;;
  let amt_read := zlength hb in
  if negb (amt_read =? sf_hdrsize ps) then
    e <- e_ferror P fp ;;
    if e then (m <- errmsg_for_errno "error reading dump file" [] ;; fret FF_NEXT_PACKET (-1, hdr0, set_errbuf m p))
    else if negb (amt_read =? 0) then
      fret FF_NEXT_PACKET (-1, hdr0, set_errbuf (Msg.trunc_header (sf_hdrsize ps) amt_read) p)
    else fret FF_NEXT_PACKET (0, hdr0, p)                                              (* [comment removed for export] *)
  else
  let sw (v : Z) := if pc_swapped p then bswap32 v else v in
  let caplen := sw (get_le32 hb 8) in
  let len := sw (get_le32 hb 12) in
  let sec := sw (get_le32 hb 0) in
  let usec := sw (get_le32 hb 4) in
  let usec := match sf_scale_type ps with
              | SF_PASS_THROUGH => usec
              | SF_SCALE_UP => usec * 1000
              | SF_SCALE_DOWN => usec / 1000
              end in
  let '(caplen, len) := match sf_lengths_swapped ps with
                       | NOT_SWAPPED => (caplen, len)
                       | MAYBE_SWAPPED => if caplen <=? len then (caplen, len) else (len, caplen)
                       | SWAPPED => (len, caplen)
                       end in
  let hdr := mkHdr sec usec caplen len in
  let snapshot := pc_snapshot p in       (* [comment removed for export] *)
  if max_snaplen_for_dlt (pc_linktype p) <? caplen then
    (if snapshot <? caplen
     then fret FF_NEXT_PACKET (-1, hdr, set_errbuf (Msg.invalid_caplen_snaplen caplen snapshot) p)
     else fret FF_NEXT_PACKET (-1, hdr, set_errbuf (Msg.invalid_caplen_maximum caplen
                                      (max_snaplen_for_dlt (pc_linktype p))) p))
  else if snapshot <? caplen then
    (* [comment removed for export] *)
    '(ok, p) <- (if pc_bufsize p <? caplen then grow_buffer p snapshot else ret (true, p)) ;;
    if negb ok then fret FF_NEXT_PACKET (-1, hdr, p) else
    got <- e_fread P fp (DHeap (pc_buffer p) 0) snapshot ;;
    let p := set_bufdata got p in
    if negb (zlength got =? snapshot) then
      m <- read_fail_msg fp (Msg.trunc_captured_d snapshot (zlength got)) ;;
      fret FF_NEXT_PACKET (-1, hdr, set_errbuf m p)
    else
    r <- discard_loop (Z.to_nat ((caplen - snapshot) / 4096 + 2)) fp caplen (caplen - snapshot) snapshot ;;
    match r with
    | inl m => fret FF_NEXT_PACKET (-1, hdr, set_errbuf m p)
    | inr _ =>
      let hdr := mkHdr sec usec snapshot len in
      let '(hdr, d) := pcapint_post_process (pc_linktype p) (pc_swapped p) hdr (pc_bufdata p) in
      fret FF_NEXT_PACKET (1, hdr, set_bufdata d p)
    end
  else
    '(ok, p) <- (if pc_bufsize p <? caplen then
                   let new_bufsize := roundup_pow2_u32 caplen in
                   let new_bufsize := if snapshot <? new_bufsize then snapshot else new_bufsize in
                   grow_buffer p new_bufsize
                 else ret (true, p)) ;;
    if negb ok then fret FF_NEXT_PACKET (-1, hdr, p) else
    got <- e_fread P fp (DHeap (pc_buffer p) 0) caplen ;;
    let p := set_bufdata got p in
    if negb (zlength got =? caplen) then
      m <- read_fail_msg fp (Msg.trunc_captured_u caplen (zlength got)) ;;
      fret FF_NEXT_PACKET (-1, hdr, set_errbuf m p)
    else
    let '(hdr, d) := pcapint_post_process (pc_linktype p) (pc_swapped p) hdr (pc_bufdata p) in
    fret FF_NEXT_PACKET (1, hdr, set_bufdata d p)).

(* [comment removed for export] *)

Definition BT_SHB : Z := 168627466.        (* [comment removed for export] *)
Definition BT_IDB : Z := 1.
Definition BT_PB : Z := 2.
Definition BT_SPB : Z := 3.
Definition BT_EPB : Z := 6.
Definition BYTE_ORDER_MAGIC : Z := 439041101.      (* [comment removed for export] *)
Definition BYTE_ORDER_MAGIC_SWAPPED : Z := 1295788826. (* [comment removed for export] *)
Definition BT_SHB_INSANE_MAX : Z := 1048576.
Definition INITIAL_MAX_BLOCKSIZE : Z := 16777216.
(* [comment removed for export] *)
Definition MAX_BLOCKSIZE_FOR_SNAPLEN (s : Z) : Z := s + 131104.
Definition PCAP_NG_IF_SIZE : Z := 40.     (* [comment removed for export] *)

(* [comment removed for export] *)
Inductive rb_status := RBS_Ok | RBS_Eof | RBS_Err (msg : list Z).
Definition read_bytes (fp : fh) (dest : rdest ptr) (n : Z) (fail_on_eof : bool) : M (rb_status * list Z) :=
  got <- e_fread P fp dest n ;;
  let amt_read := zlength got in
  if negb (amt_read =? n) then
    e <- e_ferror P fp ;;
    if e then (m <- errmsg_for_errno "error reading dump file" [] ;; ret (RBS_Err m, got))
    else if (amt_read =? 0) && negb fail_on_eof then ret (RBS_Eof, got)
    else ret (RBS_Err (Msg.trunc_pcapng n amt_read), got)
  else ret (RBS_Ok, got).

Inductive block_result :=
| RB_Eof (p : pcap)
| RB_Err (msg : list Z) (p : pcap)
| RB_Ok (c : cursor) (p : pcap).

(* [comment removed for export] *)
Definition read_block (a_bhdr : rdest ptr) (p : pcap) : M block_result :=
  e_fenter P FF_READ_BLOCK (
  let fp := pc_rfile p in
  '(st, bh) <- read_bytes fp a_bhdr 8 false ;;
  match st with
  | RBS_Eof => fret FF_READ_BLOCK (RB_Eof p)
  | RBS_Err m => fret FF_READ_BLOCK (RB_Err m p)
  | RBS_Ok =>
    let block_type := if pc_swapped p then bswap32 (get_le32 bh 0) else get_le32 bh 0 in
    let total_length := if pc_swapped p then bswap32 (get_le32 bh 4) else get_le32 bh 4 in
    if total_length <? 12 then fret FF_READ_BLOCK (RB_Err (Msg.block_length_lt total_length) p)
    else if negb (total_length mod 4 =? 0)
    then fret FF_READ_BLOCK (RB_Err (Msg.block_length_not_mult4 total_length) p)
    else
    (* [comment removed for export] *)
    '(gerr, p) <-
      (if pc_bufsize p <? total_length then
         if ng_max_blocksize (ng_of p) <? total_length
         then ret (Some (Msg.block_size_gt_max total_length (ng_max_blocksize (ng_of p))), p)
         else
           r <- e_realloc P (pc_buffer p) total_length ;;
           match r with
           | None => ret (Some Msg.out_of_memory, p)
           | Some b => ret (@None (list Z),
                            set_buffer b (pc_bufsize p) total_length
                                       (zfirstn total_length (pc_bufdata p)) p)
           end
       else ret (@None (list Z), p)) ;;
    match gerr with
    | Some m => fret FF_READ_BLOCK (RB_Err m p)
    | None =>
      (* [comment removed for export] *)
      let p := set_bufdata (le_bytes 4 block_type ++ le_bytes 4 total_length) p in
      (* [comment removed for export] *)
      '(st, data) <- read_bytes fp (DHeap (pc_buffer p) 8) (total_length - 8) true ;;
      let p := set_bufdata (pc_bufdata p ++ data) p in
      match st with
      | RBS_Err m => fret FF_READ_BLOCK (RB_Err m p)
      | RBS_Eof => fret FF_READ_BLOCK (RB_Err [] p)           (* [comment removed for export] *)
      | RBS_Ok =>
        (* [comment removed for export] *)
        let toff := total_length - 4 in
        let p := if pc_swapped p then set_bufdata (swap_field 4 toff (pc_bufdata p)) p else p in
        let trailer_length := get_le32 (pc_bufdata p) toff in
        if negb (total_length =? trailer_length)
        then fret FF_READ_BLOCK (RB_Err (Msg.header_trailer_mismatch total_length trailer_length) p)
        else fret FF_READ_BLOCK (RB_Ok (mkCursor 8 (total_length - 12) block_type) p)
      end
    end
  end).

(* [comment removed for export] *)
Definition ngif0 : ng_if := mkIf 0 1 NG_PASS_THROUGH 0 0.
Definition upd_head (f : ng_if -> ng_if) (l : list ng_if) : list ng_if :=
  match l with [] => [] | x :: t => f x :: t end.
(* [comment removed for export] *)
Definition nth_slot (l : list ng_if) (ifcount i : Z) : ng_if := nth (Z.to_nat (ifcount - 1 - i)) l ngif0.

(* [comment removed for export] *)
Definition add_interface (p : pcap) (idb_off : Z) (c : cursor)
  : M (bool * cursor * pcap * list Z) :=
  let ng := ng_of p in
  let iptr := ng_ifaces_ptr_of p in
  let ifcount := u32 (ng_ifcount ng + 1) in
  let ng1 := mkNg (ng_user_tsresol ng) (ng_max_blocksize ng) ifcount (ng_ifaces_size ng) (ng_ifaces ng) in
  let p := set_ng ng1 iptr p in
  (* [comment removed for export] *)
  '(r, p) <-
    (if ng_ifaces_size ng <? ifcount then
       if ng_ifaces_size ng =? 0 then
         q <- e_malloc P PCAP_NG_IF_SIZE ;;
         match q with
         | None => ret (Some (Msg.oom_interfaces ifcount), p)
         | Some q' => ret (@None (list Z),
                           set_ng (mkNg (ng_user_tsresol ng) (ng_max_blocksize ng) ifcount 1 (ng_ifaces ng))
                                  (Some q') p)
         end
       else if u32 (ng_ifaces_size ng * 2) <? ng_ifaces_size ng then
         ret (Some (Msg.too_many_interfaces 2147483648), p)
       else if negb (ng_ifcount ng <? 2 ^ 22) then
         mo_unr MO   (* [comment removed for export] *)
       else
         let new_size := ng_ifaces_size ng * 2 in
         (* [comment removed for export] *)
         match iptr with
         | None => ret (Some [], p)    (* [comment removed for export] *)
         | Some old =>
           q <- e_realloc P old (new_size * PCAP_NG_IF_SIZE) ;;
           match q with
           | None => ret (Some (Msg.oom_interfaces ifcount), p)
           | Some q' => ret (@None (list Z),
                             set_ng (mkNg (ng_user_tsresol ng) (ng_max_blocksize ng) ifcount new_size (ng_ifaces ng))
                                    (Some q') p)
           end
         end
     else ret (@None (list Z), p)) ;;
  match r with
  | Some m => ret (false, c, p, m)
  | None =>
    let ng := ng_of p in
    let iptr := ng_ifaces_ptr_of p in
    (* [comment removed for export] *)
    let snaplen := get_le32 (pc_bufdata p) (idb_off + 4) in
    let ifs := mkIf snaplen 0 NG_PASS_THROUGH 0 0 :: ng_ifaces ng in
    let p := set_ng (mkNg (ng_user_tsresol ng) (ng_max_blocksize ng) (ng_ifcount ng) (ng_ifaces_size ng) ifs) iptr p in
    let '(buf, r) := process_idb_options (pc_swapped p) c (pc_bufdata p) in
    let p := set_bufdata buf p in
    match r with
    | inl m => ret (false, c, p, m)
    | inr (opts, c) =>
      let tsresol := io_tsresol opts in
      let user := ng_user_tsresol ng in
      let '(scale_type, scale_factor) :=
        if tsresol =? user then (NG_PASS_THROUGH, None)
        else if user <? tsresol then
          (if io_is_binary opts then (SCALE_DOWN_BIN, None) else (SCALE_DOWN_DEC, Some (tsresol / user)))
        else
          (if io_is_binary opts then (SCALE_UP_BIN, None) else (SCALE_UP_DEC, Some (user / tsresol))) in
      let ifs := upd_head (fun s => mkIf (if_snaplen s) tsresol scale_type
                                      (match scale_factor with Some f => f | None => if_scale_factor s end)
                                      (io_tsoffset opts)) ifs in
      let p := set_ng (mkNg (ng_user_tsresol ng) (ng_max_blocksize ng) (ng_ifcount ng) (ng_ifaces_size ng) ifs) iptr p in
      ret (true, c, p, [])
    end
  end.

(* [comment removed for export] *)
Fixpoint ng_find_idb (fuel : nat) (p : pcap) : M (((list Z) + Z) * pcap) :=
  match fuel with
  | O => mo_unr MO                                       (* [comment removed for export] *)
  | S fuel' =>
    rb <- read_block (DStack SiteBhdrCheckHeader 0) p ;;
    match rb with
    | RB_Eof p => ret (inl Msg.no_idb, p)
    | RB_Err m p => ret (inl m, p)
    | RB_Ok c p =>
      let bt := cur_block_type c in
      if bt =? BT_IDB then
        match get_from_block_data c 8 with
        | inl m => ret (inl m, p)
        | inr (off, c) =>
          let p := if pc_swapped p
                   then set_bufdata (swap_field 4 (off + 4) (swap_field 2 off (pc_bufdata p))) p
                   else p in
          '(ok, c, p, m) <- add_interface p off c ;;
          if ok then ret (inr off, p) else ret (inl m, p)
        end
      else if (bt =? BT_EPB) || (bt =? BT_SPB) || (bt =? BT_PB) then
        ret (inl Msg.packet_before_idb, p)
      else ng_find_idb fuel' p
    end
  end.

(* [comment removed for export] *)
Definition pcap_ng_check_header (fuel : nat) (magic : list Z) (fp : fh) (precision : Z)
  : M check_result :=
  e_fenter P FF_NG_CHECK_HEADER (
  let magic_int := le_of_bytes magic in
  if negb (magic_int =? BT_SHB) then fret FF_NG_CHECK_HEADER CH_NotMe else
  tlb <- e_fread P fp (DStack SiteNgTotalLength 0) 4 ;;
  if zlength tlb <? 4 then
    (e <- e_ferror P fp ;;
     if e then (m <- errmsg_for_errno "error reading dump file" [] ;; fret FF_NG_CHECK_HEADER (CH_Err m)) else fret FF_NG_CHECK_HEADER CH_NotMe)
  else
  bomb <- e_fread P fp (DStack SiteNgByteOrderMagic 0) 4 ;;
  if zlength bomb <? 4 then
    (e <- e_ferror P fp ;;
     if e then (m <- errmsg_for_errno "error reading dump file" [] ;; fret FF_NG_CHECK_HEADER (CH_Err m)) else fret FF_NG_CHECK_HEADER CH_NotMe)
  else
  let total_length := get_le32 tlb 0 in
  let byte_order_magic := get_le32 bomb 0 in
  let '(ok, swapped, total_length) :=
    if byte_order_magic =? BYTE_ORDER_MAGIC then (true, false, total_length)
    else if bswap32 byte_order_magic =? BYTE_ORDER_MAGIC then (true, true, bswap32 total_length)
    else (false, false, total_length) in
  if negb ok then fret FF_NG_CHECK_HEADER CH_NotMe else
  if (total_length <? 28) || (BT_SHB_INSANE_MAX <? total_length)
  then fret FF_NG_CHECK_HEADER (CH_Err (Msg.shb_invalid_length total_length))
  else
  r <- pcapint_open_offline_common PCAP_NG_SF_TOTAL ;;
  match r with
  | inl m => fret FF_NG_CHECK_HEADER (CH_Err m)
  | inr self =>
    let user_tsresol := if precision =? PCAP_TSTAMP_PRECISION_MICRO then Some 1000000
                        else if precision =? PCAP_TSTAMP_PRECISION_NANO then Some 1000000000
                        else None in
    match user_tsresol with
    | None => e_free P self ;;; fret FF_NG_CHECK_HEADER (CH_Err (Msg.unknown_tstamp_resolution precision))
    | Some user_tsresol =>
      let bufsize := if 2048 <? total_length then total_length else 2048 in
      b <- e_malloc P bufsize ;;
      match b with
      | None => e_free P self ;;; fret FF_NG_CHECK_HEADER (CH_Err Msg.out_of_memory)
      | Some buf =>
        let ng := mkNg user_tsresol INITIAL_MAX_BLOCKSIZE 0 0 [] in
        (* [comment removed for export] *)
        let p0 := mkPcap self fp bufsize bufsize buf
                    (le_bytes 4 magic_int ++ le_bytes 4 total_length ++ le_bytes 4 BYTE_ORDER_MAGIC)
                    swapped 0 0 0 0 0 precision 0 [] hdr0 (PrivNg ng None) in
        let fail (m : list Z) (p : pcap) : M check_result :=
          free_opt (ng_ifaces_ptr_of p) ;;; e_free P (pc_buffer p) ;;; e_free P (pc_self p) ;;; fret FF_NG_CHECK_HEADER (CH_Err m) in
        '(st, data) <- read_bytes fp (DHeap buf 12) (total_length - 12) true ;;
        let p0 := set_bufdata (pc_bufdata p0 ++ data) p0 in
        match st with
        | RBS_Err m => fail m p0
        | RBS_Eof => fail [] p0                 (* [comment removed for export] *)
        | RBS_Ok =>
          let p0 := if swapped
                    then set_bufdata (swap_field 2 14 (swap_field 2 12 (pc_bufdata p0))) p0
                    else p0 in
          let major := get_le16 (pc_bufdata p0) 12 in
          let minor := get_le16 (pc_bufdata p0) 14 in
          if negb ((major =? 1) && ((minor =? 0) || (minor =? 2)))
          then fail (Msg.unsupported_pcapng_version major minor) p0
          else
          let p0 := mkPcap (pc_self p0) (pc_rfile p0) (pc_bufsize p0) (pc_bufalloc p0) (pc_buffer p0)
                      (pc_bufdata p0) (pc_swapped p0) major minor (pc_snapshot p0) (pc_linktype p0)
                      (pc_linktype_ext p0) precision 0 [] hdr0 (pc_priv p0) in
          r <- ng_find_idb fuel p0 ;;
          match r with
          | (inl m, p1) => fail m p1
          | (inr idb_off, p1) =>
            let lt := linktype_to_dlt (get_le16 (pc_bufdata p1) idb_off) in
            let snapshot := pcapint_adjust_snapshot lt (get_le32 (pc_bufdata p1) (idb_off + 4)) in
            let ng := ng_of p1 in
            let mb := MAX_BLOCKSIZE_FOR_SNAPLEN (max_snaplen_for_dlt lt) in
            let ng := if ng_max_blocksize ng <? mb
                      then mkNg (ng_user_tsresol ng) mb (ng_ifcount ng) (ng_ifaces_size ng) (ng_ifaces ng)
                      else ng in
            fret FF_NG_CHECK_HEADER (CH_Ok (mkPcap (pc_self p1) (pc_rfile p1) (pc_bufsize p1) (pc_bufalloc p1) (pc_buffer p1)
                          (pc_bufdata p1) (pc_swapped p1) (pc_version_major p1) (pc_version_minor p1)
                          snapshot lt 0 precision 0 [] hdr0 (PrivNg ng (ng_ifaces_ptr_of p1))))
          end
        end
      end
    end
  end).

(* [comment removed for export] *)
Record ng_found := mkFound { f_interface_id : Z ; f_t : Z ; f_caplen : Z ; f_len : Z ; f_cursor : cursor }.

(* [comment removed for export] *)
Fixpoint ng_scan_blocks (fuel : nat) (p : pcap) : M ((Z + ng_found) * pcap) :=
  match fuel with
  | O => mo_unr MO                                       (* [comment removed for export] *)
  | S fuel' =>
    rb <- read_block (DStack SiteBhdrNextPacket 0) p ;;
    match rb with
    | RB_Eof p => ret (inl 0, p)
    | RB_Err m p => ret (inl (-1), set_errbuf m p)
    | RB_Ok c p =>
      let bt := cur_block_type c in
      let buf := pc_bufdata p in
      let sw32 (v : Z) := if pc_swapped p then bswap32 v else v in
      let sw16 (v : Z) := if pc_swapped p then bswap16 v else v in
      if bt =? BT_EPB then
        match get_from_block_data c 20 with
        | inl m => ret (inl (-1), set_errbuf m p)
        | inr (off, c) =>
          ret (inr (mkFound (sw32 (get_le32 buf off))
                            (sw32 (get_le32 buf (off + 4)) * 2^32 + sw32 (get_le32 buf (off + 8)))
                            (sw32 (get_le32 buf (off + 12))) (sw32 (get_le32 buf (off + 16))) c), p)
        end
      else if bt =? BT_SPB then
        match get_from_block_data c 4 with
        | inl m => ret (inl (-1), set_errbuf m p)
        | inr (off, c) =>
          let len := sw32 (get_le32 buf off) in
          let caplen := if pc_snapshot p <? len then pc_snapshot p else len in
          ret (inr (mkFound 0 0 caplen len c), p)
        end
      else if bt =? BT_PB then
        match get_from_block_data c 20 with
        | inl m => ret (inl (-1), set_errbuf m p)
        | inr (off, c) =>
          ret (inr (mkFound (sw16 (get_le16 buf off))
                            (sw32 (get_le32 buf (off + 4)) * 2^32 + sw32 (get_le32 buf (off + 8)))
                            (sw32 (get_le32 buf (off + 12))) (sw32 (get_le32 buf (off + 16))) c), p)
        end
      else if bt =? BT_IDB then
        match get_from_block_data c 8 with
        | inl m => ret (inl (-1), set_errbuf m p)
        | inr (off, c) =>
          let p := if pc_swapped p
                   then set_bufdata (swap_field 4 (off + 4) (swap_field 2 off buf)) p
                   else p in
          let lt := get_le16 (pc_bufdata p) off in
          let sl := get_le32 (pc_bufdata p) (off + 4) in
          if negb (pc_linktype p =? lt)
          then ret (inl (-1), set_errbuf (Msg.iface_type_differs lt) p)
          else if negb (pc_snapshot p =? pcapint_adjust_snapshot (pc_linktype p) sl)
          then ret (inl (-1), set_errbuf (Msg.iface_snaplen_differs sl) p)
          else
            '(ok, c, p, m) <- add_interface p off c ;;
            if ok then ng_scan_blocks fuel' p else ret (inl (-1), set_errbuf m p)
        end
      else if bt =? BT_SHB then
        match get_from_block_data c 16 with
        | inl m => ret (inl (-1), set_errbuf m p)
        | inr (off, c) =>
          let p := if pc_swapped p
                   then set_bufdata (swap_field 2 (off + 4) (swap_field 4 off buf)) p
                   else p in
          let bom := get_le32 (pc_bufdata p) off in
          if bom =? BYTE_ORDER_MAGIC then
            let major := get_le16 (pc_bufdata p) (off + 4) in
            if negb (major =? 1)
            then ret (inl (-1), set_errbuf (Msg.unknown_major major) p)
            else
              (* [comment removed for export] *)
              let ng := ng_of p in
              let p := set_ng (mkNg (ng_user_tsresol ng) (ng_max_blocksize ng) 0 (ng_ifaces_size ng) [])
                              (ng_ifaces_ptr_of p) p in
              ng_scan_blocks fuel' p
          else if bom =? BYTE_ORDER_MAGIC_SWAPPED
          then ret (inl (-1), set_errbuf Msg.sections_byte_order p)
          else ret (inl (-1), set_errbuf Msg.bad_byte_order_magic p)
        end
      else ng_scan_blocks fuel' p
    end
  end.

(* [comment removed for export] *)
Definition pcap_ng_next_packet (fuel : nat) (p : pcap) : M (Z * pkthdr * pcap) :=
  '(r, p) <- ng_scan_blocks fuel p ;;
  match r with
  | inl status => ret (status, hdr0, p)
  | inr f =>
    let ng := ng_of p in
    let interface_id := f_interface_id f in
    if ng_ifcount ng <=? interface_id
    then ret (-1, hdr0, set_errbuf (Msg.no_idb_for_interface interface_id) p)
    else if pc_snapshot p <? f_caplen f
    then ret (-1, hdr0, set_errbuf (Msg.invalid_caplen_snaplen (f_caplen f) (pc_snapshot p)) p)
    else
    let ifc := nth_slot (ng_ifaces ng) (ng_ifcount ng) interface_id in
    let t := f_t f in
    (* [comment removed for export] *)
    let sec := u64 (t / if_tsresol ifc + if_tsoffset ifc) in
    let frac := t mod if_tsresol ifc in
    let frac := match if_scale_type ifc with
                | NG_PASS_THROUGH => frac
                | SCALE_UP_DEC => u64 (frac * if_scale_factor ifc)
                | SCALE_UP_BIN => u64 (frac * ng_user_tsresol ng) / if_tsresol ifc
                | SCALE_DOWN_DEC => frac / if_scale_factor ifc
                | SCALE_DOWN_BIN => u64 (frac * ng_user_tsresol ng) / if_tsresol ifc
                end in
    (* [comment removed for export] *)
    let hdr := mkHdr (s64 sec) (s32 frac) (f_caplen f) (f_len f) in
    match get_from_block_data (f_cursor f) (f_caplen f) with
    | inl m => ret (-1, hdr, set_errbuf m p)
    | inr (doff, _) =>
      let '(hdr, d) := pcapint_post_process (pc_linktype p) (pc_swapped p) hdr (zskipn doff (pc_bufdata p)) in
      ret (1, hdr, set_bufdata (zfirstn doff (pc_bufdata p) ++ d) p)
    end
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition next_packet_op (fuel : nat) (p : pcap) : M (Z * pkthdr * pcap) :=
  match pc_priv p with
  | PrivPcap _ => pcap_next_packet p
  | PrivNg _ _ => pcap_ng_next_packet fuel p
  end.

(* [comment removed for export] *)
Definition pcapint_offline_read_1 (fuel : nat) (p : pcap) : M (Z * pcap) :=
  e_fenter P FF_OFFLINE_READ (
  if negb (pc_break_loop p =? 0) then fret FF_OFFLINE_READ (-2, set_break_loop 0 p)   (* [comment removed for export] *)
  else
    '(status, h, p) <- next_packet_op fuel p ;;
    if status <? 0 then fret FF_OFFLINE_READ (status, p)
    else if status =? 0 then fret FF_OFFLINE_READ (0, p)
    else fret FF_OFFLINE_READ (1, set_header h p)).                                      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition pcap_next_ex (fuel : nat) (p : pcap) : M (Z * pcap) :=
  e_fenter P FF_NEXT_EX (
  '(status, p) <- pcapint_offline_read_1 fuel p ;;
  fret FF_NEXT_EX (if status =? 0 then -2 else status, p)).

(* [comment removed for export] *)
Definition pcap_stats (p : pcap) : M (Z * pcap) :=
  ret (-1, set_errbuf Msg.stats_not_avail p).

(* [comment removed for export] *)
Definition pcapint_sf_cleanup (p : pcap) : M unit :=
  e_fclose P (pc_rfile p) ;;;
  e_free P (pc_buffer p).

(* [comment removed for export] *)
Definition pcap_ng_cleanup (p : pcap) : M unit :=
  free_opt (ng_ifaces_ptr_of p) ;;;
  pcapint_sf_cleanup p.

(* [comment removed for export] *)
Definition pcap_close (p : pcap) : M unit :=
  match pc_priv p with
  | PrivPcap _ => pcapint_sf_cleanup p
  | PrivNg _ _ => pcap_ng_cleanup p
  end ;;;
  e_free P (pc_self p).

(* [comment removed for export] *)
Definition pcap_fopen_offline_with_tstamp_precision (fuel : nat) (fp : fh) (precision : Z)
  : M ((list Z) + pcap) :=
  e_fenter P FF_FOPEN_OFFLINE (
  magic <- e_fread P fp (DStack SiteMagic 0) 4 ;;
  if negb (zlength magic =? 4) then
    m <- read_fail_msg fp (Msg.trunc_file_header 4 (zlength magic)) ;; fret FF_FOPEN_OFFLINE (inl m)
  else
  r1 <- pcap_check_header magic fp precision ;;
  match r1 with
  | CH_Err m => fret FF_FOPEN_OFFLINE (inl m)
  | CH_Ok p => e_fileno P fp ;;; fret FF_FOPEN_OFFLINE (inr p)         (* [comment removed for export] *)
  | CH_NotMe =>
    r2 <- pcap_ng_check_header fuel magic fp precision ;;
    match r2 with
    | CH_Err m => fret FF_FOPEN_OFFLINE (inl m)
    | CH_Ok p => e_fileno P fp ;;; fret FF_FOPEN_OFFLINE (inr p)
    | CH_NotMe => fret FF_FOPEN_OFFLINE (inl Msg.unknown_file_format)
    end
  end).

(* [comment removed for export] *)
Definition pcap_open_offline_with_tstamp_precision (fuel : nat) (fname : list Z) (precision : Z)
  : M ((list Z) + pcap) :=
  fo <- e_fopen_r P fname ;;
  match fo with
  | None => m <- errmsg_for_errno "%s" [AStr (cstr fname)] ;; ret (inl m)
  | Some fp =>
    r <- pcap_fopen_offline_with_tstamp_precision fuel fp precision ;;
    match r with
    | inl m => e_fclose P fp ;;; ret (inl m)
    | inr p => ret (inr p)
    end
  end.

(* [comment removed for export] *)
Definition pcap_open_offline (fuel : nat) (fname : list Z) : M ((list Z) + pcap) :=
  pcap_open_offline_with_tstamp_precision fuel fname PCAP_TSTAMP_PRECISION_MICRO.

(* [comment removed for export] *)

Local Open Scope string_scope.
Definition DEVNULL : list Z := str "/dev/null".
Definition TEMPLATE : list Z := str "/tmp/libpcap_fuzz_pcap.XXXXXX".
(* [comment removed for export] *)
Definition TMPNAME : list Z := str "libpcap_fuzz_pcap.000000".
Local Close Scope string_scope.
Definition ENOENT : Z := 2.

(* [comment removed for export] *)
Definition bufferToFile (name : list Z) (data : list Z) : M Z :=
  r <- e_remove P name ;;
  k <- (if negb (r =? 0) then
          e <- e_last_errno P ;;                  (* [comment removed for export] *)
          if negb (e =? ENOENT) then (e_printf P (pieces_failed_remove e) ;;; ret false) else ret true
        else ret true) ;;
  if negb k then ret (-1) else
  fo <- e_fopen_w P name ;;
  match fo with
  | None => e <- e_last_errno P ;; e_printf P (pieces_failed_open e) ;;; ret (-2)
  | Some fd =>
    n <- e_fwrite P fd data ;;
    e_fclose P fd ;;;                             (* [comment removed for export] *)
    if negb (n =? zlength data) then ret (-3) else ret 0
  end.

(* [comment removed for export] *)
Definition with_outfile {A} (k : fh -> M A) : M A :=
  o <- e_get_outfile P ;;
  match o with
  | Some out => k out
  | None => mo_unr MO
  end.

(* [comment removed for export] *)
Fixpoint packet_loop (fuel : nat) (ngfuel : nat) (p : pcap) : M pcap :=
  match fuel with
  | O => mo_unr MO                               (* [comment removed for export] *)
  | S fuel' =>
    '(r, p) <- pcap_next_ex ngfuel p ;;
    if 0 <? r then
      with_outfile (fun out => e_fprintf P out (pieces_packet_length (h_caplen (pc_header p)) (h_len (pc_header p)))) ;;;
      packet_loop fuel' ngfuel p
    else ret p
  end.

(* [comment removed for export] *)
Definition LLVMFuzzerTestOneInput (data : list Z) : M unit :=
  e_fenter P FF_FUZZ_ONE_INPUT (
  let fuel := S (length data) in
  o0 <- e_get_outfile P ;;
  o <- match o0 with
       | Some f => ret (Some f)
       | None => fo <- e_fopen_w P DEVNULL ;; e_set_outfile P fo ;;; ret fo
       end ;;
  match o with
  | None => fret FF_FUZZ_ONE_INPUT tt                              (* [comment removed for export] *)
  | Some _ =>
    '(filename, fd) <- e_mkstemp P TEMPLATE ;;   (* [comment removed for export] *)
    if fd <? 0 then fret FF_FUZZ_ONE_INPUT tt                        (* [comment removed for export] *)
    else
      e_close_fd P fd ;;;
      r <- bufferToFile filename data ;;
      if r <? 0 then e_unlink P filename ;;; fret FF_FUZZ_ONE_INPUT tt
      else
      po <- pcap_open_offline fuel filename ;;
      match po with
      | inl errbuf =>
        with_outfile (fun out => e_fprintf P out (pieces_couldnt_open (cstr errbuf))) ;;;
        e_unlink P filename ;;;
        fret FF_FUZZ_ONE_INPUT tt
      | inr p =>
        p <- packet_loop fuel fuel p ;;
        '(sr, p) <- pcap_stats p ;;
        (if sr =? 0 then with_outfile (fun out => e_fprintf P out (pieces_number_of_packets 0)) else ret tt) ;;;  (* [comment removed for export] *)
        pcap_close p ;;;
        e_unlink P filename ;;;
        fret FF_FUZZ_ONE_INPUT tt
      end
  end).

(* [comment removed for export] *)
Fixpoint call_loop (n : nat) (data : list Z) : M unit :=
  match n with
  | O => ret tt
  | S n' =>
    LLVMFuzzerTestOneInput data ;;;
    e_printf P (pieces_emit_d 0) ;;;
    call_loop n' data
  end.
Definition target_run (config payload : list Z) : M Z :=
  let c := match config with [] => 0 | b :: _ => b end in
  let calls := Z.to_nat (1 + Z.land c 3) in
  owned <- (match payload with
            | [] => ret (Some None)
            | _ => q <- e_malloc P (zlength payload) ;;
                   match q with None => ret None | Some q' => ret (Some (Some q')) end
            end) ;;
  match owned with
  | None => ret 2
  | Some optr =>
    call_loop calls payload ;;;
    free_opt optr ;;;
    ret 0
  end.

End PcapModel.
