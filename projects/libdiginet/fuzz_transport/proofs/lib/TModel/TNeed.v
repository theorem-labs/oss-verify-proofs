(* Each definition below transcribes a C body that the shared model (lib/Spec/DgnSpec.v,
   DgnLib.v) did not hold when it was written. DgnLink.v now models all three; TNeedLink.v
   proves each one equal to DgnLink's definition (the notes below), so they stay. One section per model file. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld.
Import ListNotations.
Open Scope Z_scope.

(* ==== for TSess0.v, TSess.v ==== *)

(* x and y are the same list of numbers *)
Fixpoint z_list_eqb (x y : list Z) : bool :=
  match x, y with
  | [], [] => true
  | a :: x', b :: y' => (a =? b) && z_list_eqb x' y'
  | _, _ => false
  end.

(* Link: DgnLink.diginet_personality_from_name, equal by TNeedLink.personality_from_name_link.
   diginet_personality_from_name (src/diginet_codec.c:17-25).
   name = the bytes of the C string before its NUL. strcmp (name, personalities[i].announce_name) (:22) is 0
   exactly when the two strings are equal, and it reads no byte after the first NUL of either. The loop
   (:21-23) walks the two entries of personalities (DgnLib.personalities, diginet_codec.c:12-15) in order:
   Some i = &personalities[i] (:23), None = NULL (:24). The one caller (diginet_session.c:191) passes the
   array a.name, so the NULL test of :19-20 is not taken. *)
Fixpoint personality_name_find (t : list dgn_personality) (i : Z) (name : list Z) : option Z :=
  match t with
  | [] => None
  | p :: t' => if z_list_eqb name (dp_announce_name p) then Some i else personality_name_find t' (i + 1) name
  end.

Definition diginet_personality_from_name (name : list byte) : option Z :=
  personality_name_find personalities 0 (map bz name).

(* Link: the code of DgnLink.diginet_frame_build, equal by TNeedLink.frame_build_code_link.
   The sum-mode test of diginet_frame_build (src/diginet_frame.c:100-101), which DgnLib's
   lib_build_code (:102-111) starts after: -1 (DIGINET_E_ARG) for a mode other than DIGINET_SUM_BODY (0) and
   DIGINET_SUM_ZERO (1). The pointer test of :98-99 is not taken by the session's calls: buf, dst, src and h
   are the session's own objects or its caller's locals, and the one call without a body passes body_len 0
   (diginet_session.c:101). On a result >= 0 the bytes written are DgnLib.lib_frame. *)
Definition diginet_frame_build_code (body : list byte) (cap mode : Z) : Z :=
  if negb ((mode =? 0) || (mode =? 1)) then -1 else lib_build_code body cap.

(* ==== for TOps.v ==== *)

(* Link: DgnLink.spec_build_frame, equal by TNeedLink.spec_build_frame_link (tneed_spec_build_frame).
   spec_build_frame(out, dst, src, send, ack, retry, cmd, ncmds, body, len, zero_sum),
   fuzz/spec.h:228-247, transcribed statement by statement. dst / src: the 6 bytes at each pointer; body: the len
   bytes at body (len = length body). Result: the n bytes the function writes at out (out[0 .. n-1]) and its return
   value n. Every write is inside out[0 .. n-1]: the 30 header bytes, then the body at 30 (30 + len <= n). *)
Definition spec_build_frame (dst src : list byte) (send ack retry cmd ncmds : Z) (body : list byte)
    (zero_sum : Z) : list byte * Z :=
  let len := Z.of_nat (length body) in
  let n := if 30 + len <? 60 then 60 else 30 + len in                  (* :232 SPEC_BODY_AT, SPEC_MIN_FRAME *)
  let o0 := repeat (b8 0) (Z.to_nat n) in                              (* :233 memset(out, 0, n) *)
  let o1 := upd o0 0 (firstn 6 dst) in                                 (* :234 *)
  let o2 := upd o1 6 (firstn 6 src) in                                 (* :235 *)
  let o3 := upd o2 12 (put16 0x885f) in                                (* :236 SPEC_ETHERTYPE *)
  let o4 := upd o3 14 (put16 ((16 + len) mod 2^32)) in                 (* :237 (unsigned)(SPEC_HDR + len) *)
  let o5 := upd o4 16 (put16 (if zero_sum =? 0 then spec_sum body else 0)) in   (* :238 *)
  let o6 := upd o5 18 (put32 send) in                                  (* :239 *)
  let o7 := upd o6 22 (put32 ack) in                                   (* :240 *)
  let o8 := upd o7 26 (put16 retry) in                                 (* :241 *)
  let o9 := upd o8 28 [b8 cmd] in                                      (* :242 *)
  let o10 := upd o9 29 [b8 ncmds] in                                   (* :243 *)
  let o11 := if len =? 0 then o10 else upd o10 30 body in              (* :244-245 *)
  (o11, n).                                                            (* :246 *)
