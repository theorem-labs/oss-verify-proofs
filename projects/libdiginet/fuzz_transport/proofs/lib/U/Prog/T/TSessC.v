(* The struct diginet_frame a session function receives from diginet_session_rx (rx's local f, filled by
   diginet_frame_parse) and the blocks besides the world and the stack window that a session function reads or
   writes (an argument buffer, an out-cell of its caller's frame). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TContract.
Import ListNotations.
Open Scope Z_scope.

(* A block [p, p + n) of the caller (an argument buffer or an out-cell): not NULL, below 2^64, outside the world
   [W_BASE_UBSAN, W_BASE_UBSAN + W_LEN) and outside the callee's stack window [sp - K, sp). *)
Definition arg_blk (sp : word) (K p n : Z) : Prop :=
  0 < p /\ p + n < 2^64 /\ off_world p n /\ off_window sp K p n.

(* Two blocks [p, p + n) and [q, q + k) that do not overlap. *)
Definition blk_sep (p n q k : Z) : Prop := p + n <= q \/ q + k <= p.

(* struct diginet_frame (include/diginet/diginet_frame.h; offsets in the ubsan image: dst 0, src 6, ethertype 12,
   h 16 (numbytes 16, sum 18, send_counter 20, ack_counter 24, retry 28, cmd 30, num_commands 31), body 32,
   body_len 40, pad_len 48, body_sum 56, sum_matches 58; 64 bytes) after diginet_frame_parse of the frame bytes b at
   address buf answered 0 (fr_code b = 0). fj are the 64 bytes the parse found there; it leaves bytes 14, 15 and
   59 .. 63 alone. This is, cell for cell, parse_cells of the diginet_frame_parse contract
   (fuzz_frame's lib/U/Prog/diginet_frame_parse_c.v), so rx's walk passes that contract's post unchanged. *)
Definition dframe_cells (buf : Z) (b fj : list byte) : list cell :=
  [ CB 6 (fr_dst b);                                          (*  0 dst *)
    CB 6 (fr_src b);                                          (*  6 src *)
    C2 (Z_to_bv 64 (fr_ethertype b));                         (* 12 ethertype *)
    CB 2 (firstn 2 (skipn 14 fj));                            (* 14 not written *)
    C2 (Z_to_bv 64 (fr_numbytes b));                          (* 16 h.numbytes *)
    C2 (Z_to_bv 64 (fr_sum b));                               (* 18 h.sum *)
    C4 (Z_to_bv 64 (fr_send b));                              (* 20 h.send_counter *)
    C4 (Z_to_bv 64 (fr_ack b));                               (* 24 h.ack_counter *)
    C2 (Z_to_bv 64 (fr_retry b));                             (* 28 h.retry *)
    C1 (b8 (fr_cmd b));                                       (* 30 h.cmd *)
    C1 (b8 (fr_ncmds b));                                     (* 31 h.num_commands *)
    C8 (Z_to_bv 64 (buf + 30));                               (* 32 body *)
    C8 (Z_to_bv 64 (fr_body_len b));                          (* 40 body_len *)
    C8 (Z_to_bv 64 (fr_pad_len b));                           (* 48 pad_len *)
    C2 (Z_to_bv 64 (fr_body_sum b));                          (* 56 body_sum *)
    C1 (b8 (if fr_sum b =? fr_body_sum b then 1 else 0));     (* 58 sum_matches *)
    CB 5 (skipn 59 fj) ].                                     (* 59 not written *)

(* The frame a session function receives (on_announce, on_ack, on_data): the frame bytes b at buf, parsed with
   code 0, and the struct at fp (8-aligned) as the parse left it; both blocks of the caller. *)
Definition dframe_at (m : word -> option byte) (sp : word) (K fp buf : Z) (b fj : list byte) : Prop :=
  fr_code b = 0 /\
  bytes_at rsegs m buf b /\ arg_blk sp K buf (Z.of_nat (length b)) /\
  rw_cells rsegs m fp (dframe_cells buf b fj) /\ arg_blk sp K fp 64 /\ fp mod 8 = 0.
