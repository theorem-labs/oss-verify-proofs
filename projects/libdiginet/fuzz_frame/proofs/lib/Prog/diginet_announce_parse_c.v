(* Contract of diginet_announce_parse in fuzz_frame.plain.
   Source: src/diginet_frame.c:138-151 at 835f336c. The binary inlines copy_strz
   (src/diginet_frame.c:130-136) two times and tests (cmd & 0xfe) == 0xe0
   (DgnSpec.ann_cmd_land).
   Address 0x13ab0, size 212 bytes. No stack frame.
   Arguments: a0 is the address f of a struct diginet_frame, a1 the address ap of a struct
   diginet_announce (40 bytes). The caller is check_announce; it gives the frame that
   diginet_frame_parse filled and an announce in its stack frame.
   Preconditions:
   - f and ap are not 0;
   - these bytes are readable (bytes_at): f + 30, f->h.cmd: the byte cmd; f + 32, f->body: the
     8 bytes of the address body; f + 40, f->body_len: the 8 bytes of the length of bb; the
     bytes bb at body;
   - the 40 bytes aj at ap are writable (rw_cells);
   - the 40 bytes at ap do not overlap the bytes f + 30 .. f + 47 or the bytes at body;
   - mem_inv holds.
   Result: a0 is ann_code cmd (length bb): -9 (NOT_ANNOUNCE) for a command other than e0 and
   e1, else -4 (LENGTH) for a body under 33 bytes, else 0. On 0 the function writes ap as
   ann_cells gives it: version (bytes 0..9) is ann_version, name (bytes 10..19) is ann_name,
   unknown (byte 24) is body and unknown_len (byte 32) is 15. In each string field copy_strz
   writes the k = strz_len bytes of the string and a NUL after them; it does not write the
   bytes k+1..9 of the field. It does not write the bytes 20..23. On a code that is not 0 it
   writes no byte at ap.
   The function writes only the 40 bytes at ap. It writes a1..a6. It keeps all other
   registers.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

Definition DIGINET_ANNOUNCE_PARSE : Z := 0x13ab0.

(* The struct diginet_announce after a parse that answered 0, for the body bb at the address
   body; aj are the 40 bytes before the call. *)
Definition ann_cells (body : Z) (bb aj : list byte) : list cell :=
  [ CB 10 (ann_version bb (firstn 10 aj));            (*  0 version[10] *)
    CB 10 (ann_name bb (firstn 10 (skipn 10 aj)));    (* 10 name[10] *)
    CB 4 (firstn 4 (skipn 20 aj));                    (* 20 not written *)
    C8 (Z_to_bv 64 body);                             (* 24 unknown *)
    C8 (Z_to_bv 64 15) ].                             (* 32 unknown_len *)

Definition diginet_announce_parse_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (f ap cmd body : Z) (bb aj : list byte),
    f <> 0 -> ap <> 0 ->
    0 <= cmd < 2^8 -> 0 <= body < 2^64 ->
    bytes_at rsegs m (f + 30) [b8 cmd] ->
    bytes_at rsegs m (f + 32) (le8 (Z_to_bv 64 body) ++ le8 (Z_to_bv 64 (Z.of_nat (length bb)))) ->
    bytes_at rsegs m body bb ->
    rw_cells rsegs m ap [CB 40 aj] ->
    ap + 40 <= f + 30 \/ f + 48 <= ap ->
    ap + 40 <= body \/ body + Z.of_nat (length bb) <= ap ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (ann_code cmd (Z.of_nat (length bb))))
                       a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(ap, ap + 40)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         rw_cells rsegs m' ap
           (if ann_code cmd (Z.of_nat (length bb)) =? 0 then ann_cells body bb aj else [CB 40 aj]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 ap) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_ANNOUNCE_PARSE) fc None m (seg_rom rsegs)).
