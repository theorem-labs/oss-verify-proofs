(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
Import ListNotations.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section NgModel.
  Context {M : Type -> Type} (MO : MonadOps M) {fh ptr : Type} (P : Prims M fh ptr).
  Local Notation "x <- m ;; k" := (mo_bind MO m (fun x => k)) (at level 100, m at next level, right associativity).
  Local Notation "m ;;; k" := (mo_bind MO m (fun _ => k)) (at level 100, right associativity).
  Local Notation "' pat <- m ;; k" := (mo_bind MO m (fun x => let 'pat := x in k)) (at level 100, pat pattern, m at next level, right associativity).
  Local Notation "'ret' x" := (mo_ret MO x) (at level 10).
  Local Notation "'fret' f x" := (e_fret P f x) (at level 10, f at level 0).
  #[local] Notation pcapM := (PcapTypes.pcap ptr fh).
  #[local] Notation chkres := (@check_result fh ptr).

  (* [comment removed for export] *)
  Definition ngc_fail (m : list Z) (p : pcapM) : M chkres :=
    free_opt MO P (ng_ifaces_ptr_of p) ;;; e_free P (pc_buffer p) ;;; e_free P (pc_self p) ;;; fret FF_NG_CHECK_HEADER (CH_Err m).

  (* [comment removed for export] *)
  Definition ngc_done (precision idb_off : Z) (p1 : pcapM) : M chkres :=
    let lt := linktype_to_dlt (get_le16 (pc_bufdata p1) idb_off) in
    let snapshot := pcapint_adjust_snapshot lt (get_le32 (pc_bufdata p1) (idb_off + 4)) in
    let ng := ng_of p1 in
    let mb := MAX_BLOCKSIZE_FOR_SNAPLEN (max_snaplen_for_dlt lt) in
    let ng := if ng_max_blocksize ng <? mb
              then mkNg (ng_user_tsresol ng) mb (ng_ifcount ng) (ng_ifaces_size ng) (ng_ifaces ng)
              else ng in
    fret FF_NG_CHECK_HEADER (CH_Ok (mkPcap (pc_self p1) (pc_rfile p1) (pc_bufsize p1) (pc_bufalloc p1) (pc_buffer p1)
                  (pc_bufdata p1) (pc_swapped p1) (pc_version_major p1) (pc_version_minor p1)
                  snapshot lt 0 precision 0 [] hdr0 (PrivNg ng (ng_ifaces_ptr_of p1)))).

  Definition ngc_loop_tail (precision : Z) (r : ((list Z) + Z) * pcapM) : M chkres :=
    match r with
    | (inl m, p1) => ngc_fail m p1
    | (inr idb_off, p1) => ngc_done precision idb_off p1
    end.
  (* [comment removed for export] *)
  Definition ngc_find (fuel : nat) (precision : Z) (p0 : pcapM) : M chkres :=
    r <- ng_find_idb MO P fuel p0 ;; ngc_loop_tail precision r.

  (* [comment removed for export] *)
  Definition ngc_after_rb (fuel : nat) (precision : Z) (swapped : bool) (p0 : pcapM) (st : rb_status) (data : list Z) : M chkres :=
    let p0 := set_bufdata (pc_bufdata p0 ++ data) p0 in
    match st with
    | RBS_Err m => ngc_fail m p0
    | RBS_Eof => ngc_fail [] p0
    | RBS_Ok =>
      let p0 := if swapped then set_bufdata (swap_field 2 14 (swap_field 2 12 (pc_bufdata p0))) p0 else p0 in
      let major := get_le16 (pc_bufdata p0) 12 in
      let minor := get_le16 (pc_bufdata p0) 14 in
      if negb ((major =? 1) && ((minor =? 0) || (minor =? 2)))
      then ngc_fail (Msg.unsupported_pcapng_version major minor) p0
      else
      let p0 := mkPcap (pc_self p0) (pc_rfile p0) (pc_bufsize p0) (pc_bufalloc p0) (pc_buffer p0)
                  (pc_bufdata p0) (pc_swapped p0) major minor (pc_snapshot p0) (pc_linktype p0)
                  (pc_linktype_ext p0) precision 0 [] hdr0 (pc_priv p0) in
      ngc_find fuel precision p0
    end.

  (* [comment removed for export] *)
  Definition ngc_p0 (self : ptr) (fp : fh) (precision magic_int : Z) (swapped : bool) (TL : Z) (buf : ptr) (user_tsresol : Z) : pcapM :=
    let bufsize := if 2048 <? TL then TL else 2048 in
    mkPcap self fp bufsize bufsize buf (le_bytes 4 magic_int ++ le_bytes 4 TL ++ le_bytes 4 BYTE_ORDER_MAGIC)
           swapped 0 0 0 0 0 precision 0 [] hdr0 (PrivNg (mkNg user_tsresol INITIAL_MAX_BLOCKSIZE 0 0 []) None).

  (* [comment removed for export] *)
  Definition ngc_buf (fuel : nat) (fp : fh) (precision magic_int : Z) (swapped : bool) (TL : Z) (self : ptr) (user_tsresol : Z) : M chkres :=
    let bufsize := if 2048 <? TL then TL else 2048 in
    b <- e_malloc P bufsize ;;
    match b with
    | None => e_free P self ;;; fret FF_NG_CHECK_HEADER (CH_Err Msg.out_of_memory)
    | Some buf =>
      '(st, data) <- read_bytes MO P fp (DHeap buf 12) (TL - 12) true ;;
      ngc_after_rb fuel precision swapped (ngc_p0 self fp precision magic_int swapped TL buf user_tsresol) st data
    end.

  (* [comment removed for export] *)
  Definition ngc_open (fuel : nat) (fp : fh) (precision magic_int : Z) (swapped : bool) (TL : Z) : M chkres :=
    r <- pcapint_open_offline_common MO P PCAP_NG_SF_TOTAL ;;
    match r with
    | inl m => fret FF_NG_CHECK_HEADER (CH_Err m)
    | inr self =>
      let user_tsresol := if precision =? PCAP_TSTAMP_PRECISION_MICRO then Some 1000000
                          else if precision =? PCAP_TSTAMP_PRECISION_NANO then Some 1000000000
                          else None in
      match user_tsresol with
      | None => e_free P self ;;; fret FF_NG_CHECK_HEADER (CH_Err (Msg.unknown_tstamp_resolution precision))
      | Some user_tsresol => ngc_buf fuel fp precision magic_int swapped TL self user_tsresol
      end
    end.

  (* [comment removed for export] *)
  Definition ngc_head (fuel : nat) (magic : list Z) (fp : fh) (precision : Z) : M chkres :=
    let magic_int := le_of_bytes magic in
    if negb (magic_int =? BT_SHB) then fret FF_NG_CHECK_HEADER CH_NotMe else
    tlb <- e_fread P fp (DStack SiteNgTotalLength 0) 4 ;;
    if zlength tlb <? 4 then
      (e <- e_ferror P fp ;;
       if e then (m <- errmsg_for_errno MO P "error reading dump file" [] ;; fret FF_NG_CHECK_HEADER (CH_Err m)) else fret FF_NG_CHECK_HEADER CH_NotMe)
    else
    bomb <- e_fread P fp (DStack SiteNgByteOrderMagic 0) 4 ;;
    if zlength bomb <? 4 then
      (e <- e_ferror P fp ;;
       if e then (m <- errmsg_for_errno MO P "error reading dump file" [] ;; fret FF_NG_CHECK_HEADER (CH_Err m)) else fret FF_NG_CHECK_HEADER CH_NotMe)
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
    else ngc_open fuel fp precision magic_int swapped total_length.

  #[using="Type"] Lemma ngc_head_eq : forall fuel magic fp precision,
    pcap_ng_check_header MO P fuel magic fp precision = e_fenter P FF_NG_CHECK_HEADER (ngc_head fuel magic fp precision).
  Proof. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition ngc_K (fuel : nat) (rb : block_result) : M (((list Z) + Z) * pcapM) :=
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
          '(ok, c, p, m) <- add_interface MO P p off c ;;
          if ok then ret (inr off, p) else ret (inl m, p)
        end
      else if (bt =? BT_EPB) || (bt =? BT_SPB) || (bt =? BT_PB) then
        ret (inl Msg.packet_before_idb, p)
      else ng_find_idb MO P fuel p
    end.
  #[using="Type"] Lemma ng_find_idb_S : forall fuel p,
    ng_find_idb MO P (S fuel) p = (rb <- read_block MO P (DStack SiteBhdrCheckHeader 0) p ;; ngc_K fuel rb).
  Proof. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition ngc_round (fuel : nat) (precision : Z) (rb : block_result) : M chkres :=
    match rb with
    | RB_Eof p => ngc_fail Msg.no_idb p
    | RB_Err m p => ngc_fail m p
    | RB_Ok c p =>
      let bt := cur_block_type c in
      if bt =? BT_IDB then
        match get_from_block_data c 8 with
        | inl m => ngc_fail m p
        | inr (off, c) =>
          let p := if pc_swapped p
                   then set_bufdata (swap_field 4 (off + 4) (swap_field 2 off (pc_bufdata p))) p
                   else p in
          '(ok, c, p, m) <- add_interface MO P p off c ;;
          if ok then ngc_done precision off p else ngc_fail m p
        end
      else if (bt =? BT_EPB) || (bt =? BT_SPB) || (bt =? BT_PB) then ngc_fail Msg.packet_before_idb p
      else ngc_find fuel precision p
    end.
End NgModel.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import ListNotations.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section NgModel.
  Context {M : Type -> Type} (MO : MonadOps M) {fh ptr : Type} (P : Prims M fh ptr).
  Local Notation "x <- m ;; k" := (mo_bind MO m (fun x => k)) (at level 100, m at next level, right associativity).
  Local Notation "m ;;; k" := (mo_bind MO m (fun _ => k)) (at level 100, right associativity).
  Local Notation "' pat <- m ;; k" := (mo_bind MO m (fun x => let 'pat := x in k)) (at level 100, pat pattern, m at next level, right associativity).
  Local Notation "'ret' x" := (mo_ret MO x) (at level 10).
  Local Notation "'fret' f x" := (e_fret P f x) (at level 10, f at level 0).
  #[local] Notation pcapM := (PcapTypes.pcap ptr fh).
  #[local] Notation chkres := (@check_result fh ptr).

  (* [comment removed for export] *)
  Definition ngc_fail (m : list Z) (p : pcapM) : M chkres :=
    free_opt MO P (ng_ifaces_ptr_of p) ;;; e_free P (pc_buffer p) ;;; e_free P (pc_self p) ;;; fret FF_NG_CHECK_HEADER (CH_Err m).

  (* [comment removed for export] *)
  Definition ngc_done (precision idb_off : Z) (p1 : pcapM) : M chkres :=
    let lt := linktype_to_dlt (get_le16 (pc_bufdata p1) idb_off) in
    let snapshot := pcapint_adjust_snapshot lt (get_le32 (pc_bufdata p1) (idb_off + 4)) in
    let ng := ng_of p1 in
    let mb := MAX_BLOCKSIZE_FOR_SNAPLEN (max_snaplen_for_dlt lt) in
    let ng := if ng_max_blocksize ng <? mb
              then mkNg (ng_user_tsresol ng) mb (ng_ifcount ng) (ng_ifaces_size ng) (ng_ifaces ng)
              else ng in
    fret FF_NG_CHECK_HEADER (CH_Ok (mkPcap (pc_self p1) (pc_rfile p1) (pc_bufsize p1) (pc_bufalloc p1) (pc_buffer p1)
                  (pc_bufdata p1) (pc_swapped p1) (pc_version_major p1) (pc_version_minor p1)
                  snapshot lt 0 precision 0 [] hdr0 (PrivNg ng (ng_ifaces_ptr_of p1)))).

  Definition ngc_loop_tail (precision : Z) (r : ((list Z) + Z) * pcapM) : M chkres :=
    match r with
    | (inl m, p1) => ngc_fail m p1
    | (inr idb_off, p1) => ngc_done precision idb_off p1
    end.
  (* [comment removed for export] *)
  Definition ngc_find (fuel : nat) (precision : Z) (p0 : pcapM) : M chkres :=
    r <- ng_find_idb MO P fuel p0 ;; ngc_loop_tail precision r.

  (* [comment removed for export] *)
  Definition ngc_after_rb (fuel : nat) (precision : Z) (swapped : bool) (p0 : pcapM) (st : rb_status) (data : list Z) : M chkres :=
    let p0 := set_bufdata (pc_bufdata p0 ++ data) p0 in
    match st with
    | RBS_Err m => ngc_fail m p0
    | RBS_Eof => ngc_fail [] p0
    | RBS_Ok =>
      let p0 := if swapped then set_bufdata (swap_field 2 14 (swap_field 2 12 (pc_bufdata p0))) p0 else p0 in
      let major := get_le16 (pc_bufdata p0) 12 in
      let minor := get_le16 (pc_bufdata p0) 14 in
      if negb ((major =? 1) && ((minor =? 0) || (minor =? 2)))
      then ngc_fail (Msg.unsupported_pcapng_version major minor) p0
      else
      let p0 := mkPcap (pc_self p0) (pc_rfile p0) (pc_bufsize p0) (pc_bufalloc p0) (pc_buffer p0)
                  (pc_bufdata p0) (pc_swapped p0) major minor (pc_snapshot p0) (pc_linktype p0)
                  (pc_linktype_ext p0) precision 0 [] hdr0 (pc_priv p0) in
      ngc_find fuel precision p0
    end.

  (* [comment removed for export] *)
  Definition ngc_p0 (self : ptr) (fp : fh) (precision magic_int : Z) (swapped : bool) (TL : Z) (buf : ptr) (user_tsresol : Z) : pcapM :=
    let bufsize := if 2048 <? TL then TL else 2048 in
    mkPcap self fp bufsize bufsize buf (le_bytes 4 magic_int ++ le_bytes 4 TL ++ le_bytes 4 BYTE_ORDER_MAGIC)
           swapped 0 0 0 0 0 precision 0 [] hdr0 (PrivNg (mkNg user_tsresol INITIAL_MAX_BLOCKSIZE 0 0 []) None).

  (* [comment removed for export] *)
  Definition ngc_buf (fuel : nat) (fp : fh) (precision magic_int : Z) (swapped : bool) (TL : Z) (self : ptr) (user_tsresol : Z) : M chkres :=
    let bufsize := if 2048 <? TL then TL else 2048 in
    b <- e_malloc P bufsize ;;
    match b with
    | None => e_free P self ;;; fret FF_NG_CHECK_HEADER (CH_Err Msg.out_of_memory)
    | Some buf =>
      '(st, data) <- read_bytes MO P fp (DHeap buf 12) (TL - 12) true ;;
      ngc_after_rb fuel precision swapped (ngc_p0 self fp precision magic_int swapped TL buf user_tsresol) st data
    end.

  (* [comment removed for export] *)
  Definition ngc_open (fuel : nat) (fp : fh) (precision magic_int : Z) (swapped : bool) (TL : Z) : M chkres :=
    r <- pcapint_open_offline_common MO P PCAP_NG_SF_TOTAL ;;
    match r with
    | inl m => fret FF_NG_CHECK_HEADER (CH_Err m)
    | inr self =>
      let user_tsresol := if precision =? PCAP_TSTAMP_PRECISION_MICRO then Some 1000000
                          else if precision =? PCAP_TSTAMP_PRECISION_NANO then Some 1000000000
                          else None in
      match user_tsresol with
      | None => e_free P self ;;; fret FF_NG_CHECK_HEADER (CH_Err (Msg.unknown_tstamp_resolution precision))
      | Some user_tsresol => ngc_buf fuel fp precision magic_int swapped TL self user_tsresol
      end
    end.

  (* [comment removed for export] *)
  Definition ngc_head (fuel : nat) (magic : list Z) (fp : fh) (precision : Z) : M chkres :=
    let magic_int := le_of_bytes magic in
    if negb (magic_int =? BT_SHB) then fret FF_NG_CHECK_HEADER CH_NotMe else
    tlb <- e_fread P fp (DStack SiteNgTotalLength 0) 4 ;;
    if zlength tlb <? 4 then
      (e <- e_ferror P fp ;;
       if e then (m <- errmsg_for_errno MO P "error reading dump file" [] ;; fret FF_NG_CHECK_HEADER (CH_Err m)) else fret FF_NG_CHECK_HEADER CH_NotMe)
    else
    bomb <- e_fread P fp (DStack SiteNgByteOrderMagic 0) 4 ;;
    if zlength bomb <? 4 then
      (e <- e_ferror P fp ;;
       if e then (m <- errmsg_for_errno MO P "error reading dump file" [] ;; fret FF_NG_CHECK_HEADER (CH_Err m)) else fret FF_NG_CHECK_HEADER CH_NotMe)
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
    else ngc_open fuel fp precision magic_int swapped total_length.

  #[using="Type"] Lemma ngc_head_eq : forall fuel magic fp precision,
    pcap_ng_check_header MO P fuel magic fp precision = e_fenter P FF_NG_CHECK_HEADER (ngc_head fuel magic fp precision).
  Proof. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition ngc_K (fuel : nat) (rb : block_result) : M (((list Z) + Z) * pcapM) :=
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
          '(ok, c, p, m) <- add_interface MO P p off c ;;
          if ok then ret (inr off, p) else ret (inl m, p)
        end
      else if (bt =? BT_EPB) || (bt =? BT_SPB) || (bt =? BT_PB) then
        ret (inl Msg.packet_before_idb, p)
      else ng_find_idb MO P fuel p
    end.
  #[using="Type"] Lemma ng_find_idb_S : forall fuel p,
    ng_find_idb MO P (S fuel) p = (rb <- read_block MO P (DStack SiteBhdrCheckHeader 0) p ;; ngc_K fuel rb).
  Proof. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition ngc_round (fuel : nat) (precision : Z) (rb : block_result) : M chkres :=
    match rb with
    | RB_Eof p => ngc_fail Msg.no_idb p
    | RB_Err m p => ngc_fail m p
    | RB_Ok c p =>
      let bt := cur_block_type c in
      if bt =? BT_IDB then
        match get_from_block_data c 8 with
        | inl m => ngc_fail m p
        | inr (off, c) =>
          let p := if pc_swapped p
                   then set_bufdata (swap_field 4 (off + 4) (swap_field 2 off (pc_bufdata p))) p
                   else p in
          '(ok, c, p, m) <- add_interface MO P p off c ;;
          if ok then ngc_done precision off p else ngc_fail m p
        end
      else if (bt =? BT_EPB) || (bt =? BT_SPB) || (bt =? BT_PB) then ngc_fail Msg.packet_before_idb p
      else ngc_find fuel precision p
    end.
End NgModel.
End TwB.
