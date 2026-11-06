(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCStream.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition out_byte (s : dstrm) (b : Z) : dstrm :=
  DSTRM (s_in s) (b :: s_out s) (s_avail_out s - 1) (s_tin s) (s_tout s + 1).

Definition blk_cap (d : dst) : Z := 100000 * d_bs100k d.

(* [comment removed for export] *)
Definition get_sym (d : dst) : option (Z * dst) :=
  if blk_cap d <=? d_tPos d then None
  else
    let '(k, d1) :=
      if smallb d
      then (indexIntoF (d_tPos d) (d_cftab d), d_set_tPos d (get_ll d (d_tPos d)))
      else let w := zget (d_tt d) (d_tPos d) in (Z.land w 255, d_set_tPos d (Z.shiftr w 8)) in
    if d_rand d =? 0 then Some (k, d1)
    else let d2 := rand_upd d1 in Some (Z.lxor k (rand_mask d2), d2).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint flush_run (n : nat) (d : dst) (s : dstrm) : dst * dstrm * bool :=
  match n with
  | O => (d, s, false)
  | S n' =>
      if s_avail_out s =? 0 then (d, s, true)
      else if d_out_len d =? 0 then (d, s, false)
      else let ch := d_out_ch d in
           let d1 := d_set_out_len (d_set_cbcrc d (crc_update (d_cbcrc d) ch)) (d_out_len d - 1) in
           flush_run n' d1 (out_byte s ch)
  end.

(* [comment removed for export] *)
Fixpoint unrle_plain (fuel : nat) (d : dst) (s : dstrm) : Z * dst * dstrm :=
  match fuel with
  | O => (0, d, s)
  | S f =>
      let '(d1, s1, ret) := flush_run (S (Z.to_nat (d_out_len d))) d s in
      if ret then (0, d1, s1) else
      let PP := sv_nblock (d_sv d1) + 1 in
      if d_nused d1 =? PP then (0, d1, s1)
      else if PP <? d_nused d1 then (1, d1, s1)
      else
        let d2 := d_set_out_ch (d_set_out_len d1 1) (d_k0 d1) in
        match get_sym d2 with
        | None => (1, d2, s1)
        | Some (k1, d3) =>
            let d3 := d_set_nused d3 (d_nused d3 + 1) in
            if d_nused d3 =? PP then unrle_plain f d3 s1
            else if negb (k1 =? d_k0 d3) then unrle_plain f (d_set_k0 d3 k1) s1
            else
              let d4 := d_set_out_len d3 2 in
              match get_sym d4 with
              | None => (1, d4, s1)
              | Some (k2, d5) =>
                  let d5 := d_set_nused d5 (d_nused d5 + 1) in
                  if d_nused d5 =? PP then unrle_plain f d5 s1
                  else if negb (k2 =? d_k0 d5) then unrle_plain f (d_set_k0 d5 k2) s1
                  else
                    let d6 := d_set_out_len d5 3 in
                    match get_sym d6 with
                    | None => (1, d6, s1)
                    | Some (k3, d7) =>
                        let d7 := d_set_nused d7 (d_nused d7 + 1) in
                        if d_nused d7 =? PP then unrle_plain f d7 s1
                        else if negb (k3 =? d_k0 d7) then unrle_plain f (d_set_k0 d7 k3) s1
                        else
                          match get_sym d7 with
                          | None => (1, d7, s1)
                          | Some (k4, d8) =>
                              let d8 := d_set_out_len (d_set_nused d8 (d_nused d8 + 1)) (k4 + 4) in
                              match get_sym d8 with
                              | None => (1, d8, s1)
                              | Some (k5, d9) => unrle_plain f (d_set_nused (d_set_k0 d9 k5) (d_nused d9 + 1)) s1
                              end
                          end
                    end
              end
        end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record cloc := CLOC { c_crc : Z; c_ch : Z; c_len : Z; c_nused : Z; c_k0 : Z; c_tPos : Z;
                      c_out : list Z; c_avail : Z }.

Definition c_write (c : cloc) : cloc :=
  CLOC (crc_update (c_crc c) (c_ch c)) (c_ch c) (c_len c) (c_nused c) (c_k0 c) (c_tPos c) (c_ch c :: c_out c) (c_avail c - 1).
(* [comment removed for export] *)
Definition c_get (tt : zarr) (cap : Z) (c : cloc) : option (Z * cloc) :=
  if cap <=? c_tPos c then None
  else let w := zget tt (c_tPos c) in
       Some (Z.land w 255, CLOC (c_crc c) (c_ch c) (c_len c) (c_nused c) (c_k0 c) (Z.shiftr w 8) (c_out c) (c_avail c)).
Definition c_set_len (c : cloc) (v : Z) : cloc :=
  CLOC (c_crc c) (c_ch c) v (c_nused c) (c_k0 c) (c_tPos c) (c_out c) (c_avail c).
Definition c_set_k0 (c : cloc) (v : Z) : cloc :=
  CLOC (c_crc c) (c_ch c) (c_len c) (c_nused c) v (c_tPos c) (c_out c) (c_avail c).
Definition c_set_ch (c : cloc) (v : Z) : cloc :=
  CLOC (c_crc c) v (c_len c) (c_nused c) (c_k0 c) (c_tPos c) (c_out c) (c_avail c).
Definition c_inc (c : cloc) : cloc :=
  CLOC (c_crc c) (c_ch c) (c_len c) (c_nused c + 1) (c_k0 c) (c_tPos c) (c_out c) (c_avail c).

(* [comment removed for export] *)
Fixpoint c_flush (n : nat) (c : cloc) : cloc * bool :=
  match n with
  | O => (c, false)
  | S n' => if c_avail c =? 0 then (c, true)
            else if c_len c =? 1 then (c, false)
            else c_flush n' (c_set_len (c_write c) (c_len c - 1))
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint unrle_creg (fuel : nat) (eq1 : bool) (tt : zarr) (cap PP : Z) (c : cloc) : Z * cloc :=
  match fuel with
  | O => (0, c)
  | S f =>
      (* [comment removed for export] *)
      let '(c1, stop) :=
        if eq1 then
          (if c_avail c =? 0 then (c_set_len c 1, true) else (c_write c, false))
        else if 0 <? c_len c then
          let '(c', r) := c_flush (S (Z.to_nat (c_len c))) c in
          if r then (c', true)
          else if c_avail c' =? 0 then (c_set_len c' 1, true) else (c_write c', false)
        else (c, false) in
      if stop then (0, c1) else
      if PP <? c_nused c1 then (1, c1)
      else if c_nused c1 =? PP then (0, c_set_len c1 0)
      else
        let c2 := c_set_ch c1 (c_k0 c1) in
        match c_get tt cap c2 with
        | None => (1, c2)
        | Some (k1, c3) =>
            let c3 := c_inc c3 in
            if negb (k1 =? c_k0 c3) then unrle_creg f true tt cap PP (c_set_k0 c3 k1)
            else if c_nused c3 =? PP then unrle_creg f true tt cap PP c3
            else
              let c4 := c_set_len c3 2 in
              match c_get tt cap c4 with
              | None => (1, c4)
              | Some (k2, c5) =>
                  let c5 := c_inc c5 in
                  if c_nused c5 =? PP then unrle_creg f false tt cap PP c5
                  else if negb (k2 =? c_k0 c5) then unrle_creg f false tt cap PP (c_set_k0 c5 k2)
                  else
                    let c6 := c_set_len c5 3 in
                    match c_get tt cap c6 with
                    | None => (1, c6)
                    | Some (k3, c7) =>
                        let c7 := c_inc c7 in
                        if c_nused c7 =? PP then unrle_creg f false tt cap PP c7
                        else if negb (k3 =? c_k0 c7) then unrle_creg f false tt cap PP (c_set_k0 c7 k3)
                        else
                          match c_get tt cap c7 with
                          | None => (1, c7)
                          | Some (k4, c8) =>
                              let c8 := c_set_len (c_inc c8) (k4 + 4) in
                              match c_get tt cap c8 with
                              | None => (1, c8)
                              | Some (k5, c9) => unrle_creg f false tt cap PP (c_inc (c_set_k0 c9 k5))
                              end
                          end
                    end
              end
        end
  end.

(* [comment removed for export] *)
Definition unRLE (d : dst) (s : dstrm) : Z * dst * dstrm :=
  let PP := sv_nblock (d_sv d) + 1 in
  let fuel := Z.to_nat (PP + 3 - d_nused d) in
  if smallb d || negb (d_rand d =? 0) then unrle_plain fuel d s
  else
    let c0 := CLOC (d_cbcrc d) (d_out_ch d) (d_out_len d) (d_nused d) (d_k0 d) (d_tPos d) [] (s_avail_out s) in
    let '(r, c) := unrle_creg fuel false (d_tt d) (blk_cap d) PP c0 in
    if r =? 0 then
      (0, d_set_tPos (d_set_k0 (d_set_nused (d_set_out_len (d_set_out_ch (d_set_cbcrc d (c_crc c)) (c_ch c)) (c_len c))
            (c_nused c)) (c_k0 c)) (c_tPos c),
       DSTRM (s_in s) (c_out c ++ s_out s) (c_avail c) (s_tin s) (s_tout s + (s_avail_out s - c_avail c)))
    else (1, d, s).   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint bzd_loop (fuel : nat) (d : dst) (s : dstrm) : Z * dst * dstrm :=
  match fuel with
  | O => (BZ_OK, d, s)
  | S f =>
      if d_state d =? BZ_X_IDLE then (BZ_SEQUENCE_ERROR, d, s)
      else
        (* [comment removed for export] *)
        let '(ret, d1, s1) :=
          if d_state d =? BZ_X_OUTPUT then
            let '(corrupt, d', s') := unRLE d s in
            if corrupt =? 1 then (Some BZ_DATA_ERROR, d', s')
            else if (d_nused d' =? sv_nblock (d_sv d') + 1) && (d_out_len d' =? 0) then
              let crc := crc_final (d_cbcrc d') in
              let d'' := d_set_cbcrc d' crc in
              if negb (crc =? d_sbcrc d'') then (Some BZ_DATA_ERROR, d'', s')
              else
                let cc := Z.lxor (Z.lor (Z.shiftl (d_cccrc d'') 1) (Z.shiftr (d_cccrc d'') 31) mod 4294967296) crc in
                (None, d_set_state (d_set_cccrc d'' cc) BZ_X_BLKHDR_1, s')
            else (Some BZ_OK, d', s')
          else (None, d, s) in
        match ret with
        | Some r => (r, d1, s1)
        | None =>
            if BZ_X_MAGIC_1 <=? d_state d1 then
              let '(r, d2, s2) := decompress d1 s1 in
              if r =? BZ_STREAM_END then
                (if d_cccrc d2 =? d_sccrc d2 then (r, d2, s2) else (BZ_DATA_ERROR, d2, s2))
              else if negb (d_state d2 =? BZ_X_OUTPUT) then (r, d2, s2)
              else bzd_loop f d2 s2
            else bzd_loop f d1 s1
        end
  end.

Definition bzDecompress (d : dst) (s : dstrm) : Z * dst * dstrm :=
  bzd_loop (S (S (length (s_in s)))) d s.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition buffToBuffDecompress (junk : dst) (source : list Z) (destLen small : Z)
  : Z * Z * list Z * dst :=
  let d0 := dst_init junk 0 small in
  let s0 := dstrm_init source destLen in
  let '(ret, d1, s1) := bzDecompress d0 s0 in
  if ret =? BZ_OK then
    ((if 0 <? s_avail_out s1 then BZ_UNEXPECTED_EOF else BZ_OUTBUFF_FULL), destLen, s_output s1, d1)
  else if ret =? BZ_STREAM_END then (BZ_OK, destLen - s_avail_out s1, s_output s1, d1)
  else (ret, destLen, s_output s1, d1).

(* [comment removed for export] *)
Definition dst_zero : dst :=
  DST 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 znew 0 znew znew znew znew znew false false 0 0 0 0 0 znew znew znew
      znew znew znew znew znew znew znew znew znew dsv_zero.

Definition decompress_b2b (small : bool) (src : list Z) (destLen : Z) : Z * Z * list Z :=
  let '(r, n, out, _) := buffToBuffDecompress dst_zero src destLen (if small then 1 else 0) in (r, n, out).
