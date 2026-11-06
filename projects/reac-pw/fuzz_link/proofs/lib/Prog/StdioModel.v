(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths changed; 78 of its 91 lines of code are new or changed and 248 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition A_MREAD : Z := 0x19470.
Definition A_MWRITE : Z := 0x19544.
Definition A_MSEEK : Z := 0x19658.
Definition A_MCLOSE : Z := 0x196f4.
Definition A_LIBC : Z := 0x95898.
Definition A_OFL_LOCK : Z := 0x95cc0.
Definition A_OFL_HEAD : Z := 0x95cc8.
Definition A_GOT_GUARD : Z := 0x208d8.
Definition A_GUARD : Z := 0x95878.

Definition wz (z : Z) : word := Z_to_bv 64 z.

Definition stdio_ok (m : word -> option byte) : Prop :=
  bytes_at rsegs m (A_LIBC + 1) [Z_to_bv 8 0] /\
  bytes_at rsegs m (A_LIBC + 3) [Z_to_bv 8 0] /\
  bytes_at rsegs m A_OFL_LOCK (le4 (wz 0)).

Definition ofl_empty (m : word -> option byte) : Prop :=
  rw_cells rsegs m A_OFL_HEAD [C8 (wz 0)].

Definition ofl_one (m : word -> option byte) (h : Z) : Prop :=
  rw_cells rsegs m A_OFL_HEAD [C8 (wz h)].

Definition guard_ok (m : word -> option byte) : Prop :=
  bytes_at rsegs m A_GOT_GUARD (le8 (wz A_GUARD)) /\ exists g : word, bytes_at rsegs m A_GUARD (le8 g).

Definition A_STDERR : Z := 0x21918.
Definition A_STDIO_WRITE : Z := 0x19dbc.
Definition A_STDIO_SEEK : Z := 0x19f4c.
Definition A_STDIO_CLOSE : Z := 0x19d90.
Definition A_STDERR_BUF : Z := 0x95cd8.

Definition stderr_cells (fl md : Z) : list cell :=
  [ C4 (wz fl); C4 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz A_STDIO_CLOSE);
    C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0);
    C8 (wz 0); C8 (wz A_STDIO_WRITE); C8 (wz A_STDIO_SEEK); C8 (wz A_STDERR_BUF); C8 (wz 0);
    C8 (wz 0); C8 (wz 0);
    C4 (wz 2); C4 (wz 0); C8 (wz 0); C4 (wz md); C4 (wz 4294967295); C4 (wz 4294967295); C4 (wz 0);
    C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0) ].

Definition errf (m : word -> option byte) (fl md : Z) : Prop :=
  rw_cells rsegs m A_STDERR (stderr_cells fl md) /\ (fl = 5 \/ fl = 37) /\ (md = 0 \/ md = 4294967295).

Definition ascii (s : list Z) : list byte := map (Z_to_bv 8) s.

Fixpoint dec_aux (fuel : nat) (z : Z) (acc : list byte) : list byte :=
  match fuel with
  | O => acc
  | S f => if z <? 10 then Z_to_bv 8 (48 + z) :: acc
           else dec_aux f (z / 10) (Z_to_bv 8 (48 + z mod 10) :: acc)
  end.

Definition dec (z : Z) : list byte := dec_aux 20 z [].

Definition mfile_cells (h b n : Z) (flags pad0 rpos rend prev next mode pad1 pos pad2 : word)
    (ung buf : list byte) : list cell :=
  [ C4 flags; C4 pad0; C8 rpos; C8 rend; C8 (wz A_MCLOSE);
    C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0);
    C8 (wz A_MREAD); C8 (wz A_MWRITE); C8 (wz A_MSEEK); C8 (wz (h + 280)); C8 (wz 1024);
    C8 prev; C8 next;
    C4 (wz 4294967295); C4 (wz 0); C8 (wz 0); C4 mode; C4 (wz 4294967295); C4 (wz 4294967295); C4 pad1;
    C8 (wz (h + 232));
    C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0);
    C8 pos; C8 (wz n); C8 (wz n); C8 (wz b); C4 (wz 114); C4 pad2;
    CB 8 ung; CB 1024 buf ].

Definition rpos_of (h : Z) (rb : option (Z * Z)) : word :=
  match rb with None => wz 0 | Some (i, _) => wz (h + 280 + i) end.
Definition rend_of (h : Z) (rb : option (Z * Z)) : word :=
  match rb with None => wz 0 | Some (_, e) => wz (h + 280 + e) end.
Definition rlen (rb : option (Z * Z)) : Z :=
  match rb with None => 0 | Some (i, e) => e - i end.

Definition mfile_raw (m : word -> option byte) (h b n : Z) (fl rpos rend md : word) (q : Z)
    (prev next : word) (buf : list byte) : Prop :=
  exists (pad0 pad1 pad2 : word) (ung : list byte),
    rw_cells rsegs m h (mfile_cells h b n fl pad0 rpos rend prev next md pad1 (wz q) pad2 ung buf) /\
    length ung = 8%nat /\ length buf = 1024%nat /\ 0 < h /\ h mod 16 = 0.

Definition mfile (m : word -> option byte) (h b : Z) (Fc : list byte) (fl md : word) (q : Z)
    (rb : option (Z * Z)) (prev next : word) : Prop :=
  let n := Z.of_nat (length Fc) in
  exists buf : list byte,
    mfile_raw m h b n fl (rpos_of h rb) (rend_of h rb) md q prev next buf /\
    0 <= q <= n /\
    match rb with
    | None => True
    | Some (i, e) =>
        0 <= i <= e /\ e <= 1024 /\ e - i <= q /\
        firstn (Z.to_nat (e - i)) (skipn (Z.to_nat i) buf) = firstn (Z.to_nat (e - i)) (skipn (Z.to_nat (q - (e - i))) Fc)
    end /\
    bytes_at rsegs m b Fc /\ 0 < b /\
    (h + 1304 <= b \/ b + n <= h).

Definition mstl (m : word -> option byte) (h b : Z) (Fc : list byte) (p : Z) (prev next : word) : Prop :=
  exists (fl md : word) (q : Z) (rb : option (Z * Z)),
    mfile m h b Fc fl md q rb prev next /\
    (fl = wz 8 \/ fl = wz 24) /\ (md = wz 0 \/ md = wz 4294967295) /\
    p = q - rlen rb /\ (fl = wz 24 -> p = Z.of_nat (length Fc)).

Definition mst (m : word -> option byte) (h b : Z) (Fc : list byte) (p : Z) : Prop :=
  exists prev next, mstl m h b Fc p prev next.
