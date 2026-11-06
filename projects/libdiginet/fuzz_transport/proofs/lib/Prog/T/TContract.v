(* What is NOT here, and why: the return state and the frame clause (munch / wmono / mem_inv / stk / wmem) stay
   literal in every <f>_c.v. The kit's post_call (Lib/Tac.v) and TModel/TWorldMem.v's wk_post_call destruct a callee's
   postcondition by its shape `exists .., ms' = MS .. /\ munch W m m' /\ wmono .. /\ mem_inv .. /\ ..`; a definition
   wrapping that shape would hide it from them. The stack premises stay literal for the same reason (carve_frame
   and the transport tactics match `stk segs m lo hi` hypotheses). The literal forms every contract uses:
     premises    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + K <= bv_unsigned sp ->
                 w_off_stack W_BASE_PLAIN sp K -> mem_inv rsegs m -> wmem rsegs m B -> f_m .. = Some (B', r) ->
     post        exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
                   ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' .. a7' s2 .. s11 t3' t4' t5' t6')
                            F (ret_pc ra) fc None m' (seg_rom rsegs) /\
                   munch [(bv_unsigned sp - K, bv_unsigned sp); (W_BASE_PLAIN, W_BASE_PLAIN + W_LEN)] m m' /\
                   wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ wmem rsegs m' B'
                 (a0' replaced by the return value; the world interval left out, and `B' = B /\ wmem rsegs m' B`
                 posted, for a function that does not write the world). The floating-point registers F and fcsr fc
                 are kept as they are: no harness function of the binary touches them (as in fuzz_frame's contracts). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require Import WMem.
Import ListNotations.
Open Scope Z_scope.

(* ---- spans ---- *)

(* the n bytes at a lie outside the callee's stack window [sp - k, sp) (disco Prog/disco_table_c.v:54) *)
Definition off_window (sp : word) (k a n : Z) : Prop := a + n <= bv_unsigned sp - k \/ bv_unsigned sp <= a.

(* the n bytes at a lie outside the world [W_BASE_PLAIN, W_BASE_PLAIN + W_LEN) *)
Definition off_world (a n : Z) : Prop := a + n <= W_BASE_PLAIN \/ W_BASE_PLAIN + W_LEN <= a.

(* ---- the current heap frame (TImg.v tframe) ---- *)

(* The block the model's F names holds its bytes, is not at NULL, and lies off the world and off the callee's
   window. None (no current frame) asks nothing: every model read through F is then None. *)
Definition tframe_at (m : word -> option byte) (sp : word) (K : Z) (F : option tframe) : Prop :=
  match F with
  | None => True
  | Some fr =>
      0 < tf_addr fr /\ bytes_at rsegs m (tf_addr fr) (tf_bytes fr) /\
      off_world (tf_addr fr) (Z.of_nat (length (tf_bytes fr))) /\
      off_window sp K (tf_addr fr) (Z.of_nat (length (tf_bytes fr)))
  end.

(* The heap frame ends below 2^64 (bytes_at alone allows its end to be 2^64): what spec_read_frame's no-wrap premise
   needs at m_rx's call; the slot has it from the allocator. *)
Definition tframe_ok (F : option tframe) : Prop :=
  match F with None => True | Some fr => tf_addr fr + Z.of_nat (length (tf_bytes fr)) < 2 ^ 64 end.

(* ---- struct spec_frame (fuzz/spec.h:188-197; the plain image's layout, the same in ubsan: 80 bytes, code 0 (4),
   dst 8, src 16 (8), ethertype 24, numbytes 26, sum 28, retry 30 (2), send 32, ack 36 (4), cmd 40, ncmds 41 (1),
   body 48, body_len 56, pad_len 64 (8), body_sum 72 (2)) ---- *)

(* the value of a pointer field for the parse f of the frame buffer at fa: fa plus the model's offset
   (DgnSpec.v spec_frame), NULL when the parse failed (the memset of spec.h:201) *)
Definition sf_ptr (fa : Z) (f : spec_frame) (off : Z) : Z := if sf_code f =? SPEC_OK then fa + off else 0.

(* the 80 bytes of the struct, padding zero (what spec_read_frame writes after its memset) *)
Definition sf_bytes (fa : Z) (f : spec_frame) : list byte :=
  put 4 (sf_code f) ++ repeat (b8 0) 4 ++
  put 8 (sf_ptr fa f (sf_dst f)) ++ put 8 (sf_ptr fa f (sf_src f)) ++
  put 2 (sf_ethertype f) ++ put 2 (sf_numbytes f) ++ put 2 (sf_sum f) ++ put 2 (sf_retry f) ++
  put 4 (sf_send f) ++ put 4 (sf_ack f) ++ put 1 (sf_cmd f) ++ put 1 (sf_ncmds f) ++ repeat (b8 0) 6 ++
  put 8 (sf_ptr fa f (sf_body f)) ++ put 8 (sf_body_len f) ++ put 8 (sf_pad_len f) ++ put 2 (sf_body_sum f) ++
  repeat (b8 0) 6.

(* A struct spec_frame at p holding the parse f of the frame buffer at fa, field by field (the padding is left
   free, so a caller whose inlined parse does not zero it can still give it; bytes_at rsegs m p (sf_bytes fa f)
   implies it when every field is in its C range). p is not NULL and 8-aligned (the ubsan build traps a misaligned
   member access). *)
Definition sframe_at (m : word -> option byte) (p fa : Z) (f : spec_frame) : Prop :=
  0 < p /\ p mod 8 = 0 /\
  exists SB : list byte, bytes_at rsegs m p SB /\ length SB = 80%nat /\
    s32_at SB 0 = sf_code f /\
    u_at SB 8 8 = sf_ptr fa f (sf_dst f) /\ u_at SB 16 8 = sf_ptr fa f (sf_src f) /\
    u_at SB 24 2 = sf_ethertype f /\ u_at SB 26 2 = sf_numbytes f /\
    u_at SB 28 2 = sf_sum f /\ u_at SB 30 2 = sf_retry f /\
    u_at SB 32 4 = sf_send f /\ u_at SB 36 4 = sf_ack f /\
    u_at SB 40 1 = sf_cmd f /\ u_at SB 41 1 = sf_ncmds f /\
    u_at SB 48 8 = sf_ptr fa f (sf_body f) /\ u_at SB 56 8 = sf_body_len f /\
    u_at SB 64 8 = sf_pad_len f /\ u_at SB 72 2 = sf_body_sum f.

(* ---- struct diginet_notice (include/diginet/transport/diginet_session.h; the plain image's layout: 72 bytes,
   kind 0, state 4, old_state 8, reason 12 (4), frame 16, announce 24, personality 32 (8), mac_offset 40 (4),
   body 48, body_len 56 (8), counter 64 (4), retry 68 (2); struct diginet_announce: version 0 (10), name 10 (10),
   40 bytes, 8-aligned) ---- *)

(* A struct diginet_notice at p as notice() and the checks it calls read it (TImg.v ntc): the scalar fields, the
   personality pointer's value, the announce pointer (NULL exactly when n_ann = None; else 8-aligned, with the
   version bytes at it and the name bytes 10 further), the body bytes at the body pointer (n_body = [] asks
   nothing). The struct, the announce and the body lie off the world (notice writes the world before the checks
   read them; the session builds them on its stack, the body is the received frame) and off the callee's window
   [sp - K, sp). *)
Definition ntc_at (m : word -> option byte) (p : Z) (n : ntc) (sp : word) (K : Z) : Prop :=
  0 < p /\ p mod 8 = 0 /\ off_world p 72 /\ off_window sp K p 72 /\
  exists NB : list byte, bytes_at rsegs m p NB /\ length NB = 72%nat /\
    s32_at NB 0 = n_kind n /\ s32_at NB 4 = n_state n /\ s32_at NB 8 = n_old n /\ s32_at NB 12 = n_reason n /\
    u_at NB 32 8 = n_pers n /\ s32_at NB 40 = n_mac_offset n /\ u_at NB 56 8 = n_body_len n /\
    u_at NB 64 4 = n_counter n /\ u_at NB 68 2 = n_retry n /\
    bytes_at rsegs m (u_at NB 48 8) (n_body n) /\
    off_world (u_at NB 48 8) (Z.of_nat (length (n_body n))) /\
    off_window sp K (u_at NB 48 8) (Z.of_nat (length (n_body n))) /\
    match n_ann n with
    | None => u_at NB 24 8 = 0
    | Some a =>
        0 < u_at NB 24 8 /\ u_at NB 24 8 mod 8 = 0 /\
        bytes_at rsegs m (u_at NB 24 8) (ta_version a) /\ bytes_at rsegs m (u_at NB 24 8 + 10) (ta_name a) /\
        off_world (u_at NB 24 8) 20 /\ off_window sp K (u_at NB 24 8) 20
    end.

(* ---- the read-only records the harness reads through pointers ---- *)

(* .data.rel.ro (readelf section 8 of the plain ELF: 0x213c8, 0x98 bytes): SPEC_C24, SPEC_PC, op_announce.NAME, personalities[], stderr, stdout. The
   memory image puts it in the writable LOAD segment [0x21000, 0x22000) (rw-; PT_GNU_RELRO is not applied), so mem_inv
   does not give its bytes. relro_img says the memory still holds the image's bytes there (the form of
   fuzz_codec Prog/codec_cells.v relro_img, so one premise serves check_state_desk, notice and
   diginet_personality_from_name). check_state_desk reads personalities[k].device / .strips (bytes 16, 17 of a
   24-byte element) and OW.desk_p->device / ->strips (bytes 8, 9 of struct spec_desk) through it
   (fuzz_transport.c:535-536); in both images they are 01 18 (personalities[0], SPEC_C24) and 00 08
   (personalities[1], SPEC_PC), the values DgnLib.v personality_at and DgnSpec.v c24 / pc have (checked against
   the ELF). *)
Definition RELRO_BASE : Z := 0x213c8.
Definition RELRO_LEN : Z := 0x98.
Definition relro_img (m : word -> option byte) : Prop :=
  forall i, 0 <= i < RELRO_LEN -> mrd rsegs m (wa (RELRO_BASE + i)) = seg_rom rsegs (wa (RELRO_BASE + i)).

(* relro_img is satisfiable: a memory that has written nothing reads the image everywhere. *)
Example relro_img_unwritten : relro_img (fun _ => None).
Proof. intros i _. reflexivity. Qed.
