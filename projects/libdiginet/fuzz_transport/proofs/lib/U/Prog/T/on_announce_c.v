(* on_announce (transport/src/diginet_session.c:184-221) at 0x17000, 652 bytes. The binary inlines find_mac (bcmp
   per offset) and session_lost; it calls diginet_announce_parse (:187), diginet_personality_from_name (:191),
   bcmp, memset (the notices), set_state (session_lost's), diginet_session_wake (:205), maybe_online (:213) and,
   through g_s.notify, notice (:198, :218). FRAME 1056 = its own 304 (addi sp,sp,-304 at 0x17000) + 752, the
   deepest callee window (diginet_session_wake; bcmp 0, diginet_announce_parse 32, diginet_personality_from_name
   48, maybe_online 384, memset 0, notice 272, set_state 384). Every callee window counted is that callee's full
   transitive stack depth, abort() paths included, so it bounds the window any callee contract asks for. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TSess0 TCb TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem TImgU TContract TSessC.
Import ListNotations.
Open Scope Z_scope.

Definition on_announce_ENTRY : Z := 0x17000.
Definition on_announce_FRAME : Z := 1056.

(* a0 = s = &g_s, a1 = f = rx's struct diginet_frame, parsed (code 0) from the frame bytes b at buf (dframe_at), a2
   = now (uint64_t). void. *)
Definition on_announce_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
         (fp buf now : Z) (b fj : list byte) (B B' : list byte) (TF : option tframe),
    a0 = Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s) ->
    a1 = Z_to_bv 64 fp ->
    a2 = Z_to_bv 64 now ->
    0 <= now < 2^64 ->
    dframe_at m sp on_announce_FRAME fp buf b fj ->
    wmem rsegs m B -> g_fail_next B <= 1 ->
    on_announce_m timg_ubsan TF B b now = Some (B', tt) ->
    tframe_at m sp on_announce_FRAME TF ->
    relro_img m ->
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + on_announce_FRAME <= bv_unsigned sp ->
    w_off_stack W_BASE_UBSAN sp on_announce_FRAME ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - on_announce_FRAME, bv_unsigned sp);
                (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         wmem rsegs m' B' /\ g_fail_next B' <= 1)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 on_announce_ENTRY) fc None m (seg_rom rsegs)).
