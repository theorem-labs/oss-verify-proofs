(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim PcapPrelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Record pkthdr := mkHdr { h_sec : Z ; h_usec : Z ; h_caplen : Z ; h_len : Z }.
Definition hdr0 : pkthdr := mkHdr 0 0 0 0.

(* [comment removed for export] *)
Inductive lenswap_t := NOT_SWAPPED | SWAPPED | MAYBE_SWAPPED.      (* [comment removed for export] *)
Inductive sf_scale_t := SF_PASS_THROUGH | SF_SCALE_UP | SF_SCALE_DOWN. (* [comment removed for export] *)
Record pcap_sf := mkSf {
  sf_hdrsize : Z ;                 (* [comment removed for export] *)
  sf_lengths_swapped : lenswap_t ;
  sf_scale_type : sf_scale_t
}.

(* [comment removed for export] *)
Inductive ng_scale_t := NG_PASS_THROUGH | SCALE_UP_DEC | SCALE_DOWN_DEC | SCALE_UP_BIN | SCALE_DOWN_BIN. (* [comment removed for export] *)
Record ng_if := mkIf {
  if_snaplen : Z ;        (* [comment removed for export] *)
  if_tsresol : Z ;        (* [comment removed for export] *)
  if_scale_type : ng_scale_t ;
  if_scale_factor : Z ;   (* [comment removed for export] *)
  if_tsoffset : Z         (* [comment removed for export] *)
}.
Record pcap_ng_sf := mkNg {
  ng_user_tsresol : Z ;   (* [comment removed for export] *)
  ng_max_blocksize : Z ;  (* [comment removed for export] *)
  ng_ifcount : Z ;        (* [comment removed for export] *)
  ng_ifaces_size : Z ;    (* [comment removed for export] *)
  ng_ifaces : list ng_if  (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Section Pcap.
Context {ptr fh : Type}.

Inductive sf_priv :=
| PrivPcap (s : pcap_sf)                        (* [comment removed for export] *)
| PrivNg (s : pcap_ng_sf) (ifaces : option ptr). (* [comment removed for export] *)

Record pcap := mkPcap {
  pc_self : ptr ;           (* [comment removed for export] *)
  pc_rfile : fh ;           (* [comment removed for export] *)
  pc_bufsize : Z ;          (* [comment removed for export] *)
  pc_bufalloc : Z ;         (* [comment removed for export] *)
  pc_buffer : ptr ;         (* [comment removed for export] *)
  pc_bufdata : list Z ;     (* [comment removed for export] *)
  pc_swapped : bool ;       (* [comment removed for export] *)
  pc_version_major : Z ;    (* [comment removed for export] *)
  pc_version_minor : Z ;
  pc_snapshot : Z ;         (* [comment removed for export] *)
  pc_linktype : Z ;         (* [comment removed for export] *)
  pc_linktype_ext : Z ;     (* [comment removed for export] *)
  pc_tstamp_precision : Z ; (* [comment removed for export] *)
  pc_break_loop : Z ;       (* [comment removed for export] *)
  pc_errbuf : list Z ;      (* [comment removed for export] *)
  pc_header : pkthdr ;      (* [comment removed for export] *)
  pc_priv : sf_priv
}.

(* [comment removed for export] *)
Definition set_bufdata (d : list Z) (p : pcap) : pcap :=
  mkPcap (pc_self p) (pc_rfile p) (pc_bufsize p) (pc_bufalloc p) (pc_buffer p) d (pc_swapped p)
    (pc_version_major p) (pc_version_minor p) (pc_snapshot p) (pc_linktype p) (pc_linktype_ext p)
    (pc_tstamp_precision p) (pc_break_loop p) (pc_errbuf p) (pc_header p) (pc_priv p).
(* [comment removed for export] *)
Definition set_buffer (b : ptr) (size alloc : Z) (d : list Z) (p : pcap) : pcap :=
  mkPcap (pc_self p) (pc_rfile p) size alloc b d (pc_swapped p)
    (pc_version_major p) (pc_version_minor p) (pc_snapshot p) (pc_linktype p) (pc_linktype_ext p)
    (pc_tstamp_precision p) (pc_break_loop p) (pc_errbuf p) (pc_header p) (pc_priv p).
Definition set_errbuf (e : list Z) (p : pcap) : pcap :=
  mkPcap (pc_self p) (pc_rfile p) (pc_bufsize p) (pc_bufalloc p) (pc_buffer p) (pc_bufdata p) (pc_swapped p)
    (pc_version_major p) (pc_version_minor p) (pc_snapshot p) (pc_linktype p) (pc_linktype_ext p)
    (pc_tstamp_precision p) (pc_break_loop p) e (pc_header p) (pc_priv p).
Definition set_header (h : pkthdr) (p : pcap) : pcap :=
  mkPcap (pc_self p) (pc_rfile p) (pc_bufsize p) (pc_bufalloc p) (pc_buffer p) (pc_bufdata p) (pc_swapped p)
    (pc_version_major p) (pc_version_minor p) (pc_snapshot p) (pc_linktype p) (pc_linktype_ext p)
    (pc_tstamp_precision p) (pc_break_loop p) (pc_errbuf p) h (pc_priv p).
Definition set_priv (v : sf_priv) (p : pcap) : pcap :=
  mkPcap (pc_self p) (pc_rfile p) (pc_bufsize p) (pc_bufalloc p) (pc_buffer p) (pc_bufdata p) (pc_swapped p)
    (pc_version_major p) (pc_version_minor p) (pc_snapshot p) (pc_linktype p) (pc_linktype_ext p)
    (pc_tstamp_precision p) (pc_break_loop p) (pc_errbuf p) (pc_header p) v.
Definition set_break_loop (v : Z) (p : pcap) : pcap :=
  mkPcap (pc_self p) (pc_rfile p) (pc_bufsize p) (pc_bufalloc p) (pc_buffer p) (pc_bufdata p) (pc_swapped p)
    (pc_version_major p) (pc_version_minor p) (pc_snapshot p) (pc_linktype p) (pc_linktype_ext p)
    (pc_tstamp_precision p) v (pc_errbuf p) (pc_header p) (pc_priv p).

(* [comment removed for export] *)
Definition ng_of (p : pcap) : pcap_ng_sf :=
  match pc_priv p with PrivNg s _ => s | PrivPcap _ => mkNg 0 0 0 0 [] end.
Definition ng_ifaces_ptr_of (p : pcap) : option ptr :=
  match pc_priv p with PrivNg _ i => i | PrivPcap _ => None end.
Definition set_ng (s : pcap_ng_sf) (i : option ptr) (p : pcap) : pcap := set_priv (PrivNg s i) p.

End Pcap.
Arguments pcap ptr fh : clear implicits.
Arguments sf_priv ptr : clear implicits.

(* [comment removed for export] *)
Record cursor := mkCursor { cur_off : Z ; cur_remaining : Z ; cur_block_type : Z }.
