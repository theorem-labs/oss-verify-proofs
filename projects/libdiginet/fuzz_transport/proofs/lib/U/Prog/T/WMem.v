From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require YO0d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memcpy_c memset_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem.
Import ListNotations.
Open Scope Z_scope.

(* The world B : list byte (TModel/TWorld.v) is the memory at [W_BASE_UBSAN, W_BASE_UBSAN + W_LEN): one writable
   rw_cells cell of W_LEN bytes. An abbreviation of an rw_cells fact (TModel/TWorldMem.v wmem_at). *)
Abbreviation wmem segs m B := (wmem_at segs W_BASE_UBSAN m B).

Lemma wmem_end : W_BASE_UBSAN + W_LEN = 0x43350.
Proof. reflexivity. Qed.

(* ---- (d) the world is not heap and not stack ---- *)

(* The world lies in the image's last LOAD segment (base 0x23000, size 0x41000, rw-), so in_img holds of it. *)
Lemma wmem_in_img : forall (Bm : YO0d.malloc_syms) a, YO0d.ms_segs Bm = rsegs ->
  W_BASE_UBSAN <= a < W_BASE_UBSAN + W_LEN -> YO0d.in_img Bm a.
Proof.
  intros Bm a HS Ha. unfold YO0d.in_img. rewrite HS. split.
  - intros E. assert (L : length rsegs = 4%nat) by (vm_compute; reflexivity). rewrite E in L. discriminate L.
  - exists (nth 3 (segments_reserved rsegs) (Z_to_bv 64 0, Z_to_bv 64 0)). split.
    + apply nth_In. assert (L : length (segments_reserved rsegs) = 4%nat) by (vm_compute; reflexivity). lia.
    + replace (bv_unsigned (fst (nth 3 (segments_reserved rsegs) (Z_to_bv 64 0, Z_to_bv 64 0)))) with 0x23000
        by (vm_compute; reflexivity).
      replace (bv_unsigned (snd (nth 3 (segments_reserved rsegs) (Z_to_bv 64 0, Z_to_bv 64 0)))) with 0x41000
        by (vm_compute; reflexivity).
      unfold W_BASE_UBSAN, W_LEN in Ha. lia.
Qed.

(* Heap: every byte of every allocator block is outside the image (AllocExtra.ax_blocks_img, U/Reusable/YL01.v:25-26,
   and malloc's fresh_block, U/Contract.v:73-74), so a block [p, p + n) misses the world. *)
Lemma wmem_off_heap : forall (Bm : YO0d.malloc_syms) p n, YO0d.ms_segs Bm = rsegs -> 0 < n ->
  (forall i, 0 <= i < n -> ~ YO0d.in_img Bm (p + i)) ->
  p + n <= W_BASE_UBSAN \/ W_BASE_UBSAN + W_LEN <= p.
Proof.
  intros Bm p n HS Hn NI.
  destruct (Z_le_gt_dec (p + n) W_BASE_UBSAN) as [L|L]; [left; exact L|].
  destruct (Z_le_gt_dec (W_BASE_UBSAN + W_LEN) p) as [R|R]; [right; exact R|].
  exfalso. apply (NI (Z.max p W_BASE_UBSAN - p)); [lia|].
  replace (p + (Z.max p W_BASE_UBSAN - p)) with (Z.max p W_BASE_UBSAN) by lia.
  apply wmem_in_img; [exact HS | unfold W_LEN in *; lia].
Qed.

(* Stack: errno_addr = ms_tp + ms_errno_off = 0x43420 - 164 (U/FrameAPI.v:40-41, Reusable/YO0d.v:48 via
   U/Reusable/YO0d.v) and errno_addr + 4 <= alloc_ceiling (U/FrameAPI.v:37); lib_pre puts the slot's stack window
   above the ceiling (alloc_ceiling + stk <= spZ regs, U/Reusable/YL0g.v:37). So a callee window [sp - K, sp)
   inside the slot's window lies above the world. *)
Lemma wmem_below_ceiling : forall (Bm : YO0d.malloc_syms) ceil,
  YO0d.ms_tp Bm = 0x43420 -> YO0d.ms_errno_off Bm = -164 -> YO0d.errno_addr Bm + 4 <= ceil ->
  W_BASE_UBSAN + W_LEN <= ceil.
Proof. intros Bm ceil T E C. unfold YO0d.errno_addr in C. rewrite T, E in C. unfold W_BASE_UBSAN, W_LEN. lia. Qed.

Lemma wmem_below_stack : forall (Bm : YO0d.malloc_syms) ceil stk (sp : word) K,
  YO0d.ms_tp Bm = 0x43420 -> YO0d.ms_errno_off Bm = -164 -> YO0d.errno_addr Bm + 4 <= ceil ->
  ceil + stk <= bv_unsigned sp -> K <= stk ->
  w_off_stack W_BASE_UBSAN sp K.
Proof.
  intros Bm ceil stk sp K T E C S HK. pose proof (wmem_below_ceiling Bm ceil T E C). unfold w_off_stack. lia.
Qed.

(* ---- worked examples (no function of the binary): a made-up 9-instruction code image at 0x1000 ----
     0x1000 auipc a5, 0x42        a5 = 0x43000
     0x1004 ld    a0, 0xe8(a5)    a0 = the 8 bytes at 0x430e8 = W_BASE_UBSAN + OFF_g_now
     0x1008 auipc a5, 0x42        a5 = 0x43008
     0x100c sd    a1, 0xe0(a5)    the 8 bytes at 0x430e8 := a1
     0x1010 auipc a5, 0x41        a5 = 0x42010
     0x1014 addi  a5, a5, 0xb8    a5 = 0x420c8 = W_BASE_UBSAN + OFF_g_q
     0x1018 slli  a1, a1, 2
     0x101c add   a5, a5, a1      a5 = &g_q[a1]
     0x1020 lw    a0, 0(a5)       a0 = g_q[a1], sign-extended (U/Prog/T/WMemIdx.v) *)
Module DemoImg.
Import Stdlib.Strings.String Stdlib.Strings.PrimString.
Definition seg : Segment := {|
  seg_base := 0x1000%N; seg_size := 36%N; seg_perms := "r-x"%string;
  seg_bytes := ["9727040003b5870e9727040023b0b70e971704009387870b93952500b387b70003a50700"%pstring] |}.
End DemoImg.
Definition demo_segs : list Segment := [DemoImg.seg].

(* A world load: the hook rewrites the 8-byte read at 0x430e8 to sub B 65000 8, and ld's value to u_at B 65000 8,
   which is g_now B. *)
Lemma demo_load : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (B : list byte),
  wmem demo_segs m B ->
  evt demo_segs
    (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (g_now B)) a1 a2 a3 a4 (Z_to_bv 64 0x43000) a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x1008) fc None m (seg_rom demo_segs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1000) fc None m (seg_rom demo_segs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m B WM.
  step.                                   (* auipc a5, 0x42 *)
  step.                                   (* ld a0, 0xe8(a5): a0 = Z_to_bv 64 (u_at B 65000 8) *)
  change (u_at B 65000 8) with (g_now B).
  apply evt_done. hnf. reflexivity.
Qed.

(* A world store: the hooks prove the store target writable, then turn WM into the world upd B 65000 (put 8 v)
   = set_g_now B v about the new memory, and carry the footprint MU across the store. *)
Lemma demo_store : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (B : list byte) (v : Z),
  wmem demo_segs m B ->
  evt demo_segs
    (fun ms' => exists m', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 v) a2 a3 a4 (Z_to_bv 64 0x43008) a6 a7
                                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                     F (Z_to_bv 64 0x1010) fc None m' (seg_rom demo_segs) /\
                 wmem demo_segs m' (set_g_now B v) /\ munch [(W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 v) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1008) fc None m (seg_rom demo_segs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m B v WM.
  pose proof (munch_refl [(W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m) as MU.
  step.                                   (* auipc a5, 0x42 *)
  step.                                   (* sd a1, 0xe0(a5): the world is now upd B 65000 (put 8 v) *)
  apply evt_done. hnf. eexists. split; [reflexivity|]. split; eassumption.
Qed.

(* A memcpy of 6 bytes into M.desk (W_BASE_UBSAN + A_M_desk), with the kit's libc contract (U/Prog/memcpy_c.v:34-43)
   as the callee: wm_piece gives the destination cell, wk_post_call folds the copied bytes into the world. *)
Lemma demo_memcpy : memcpy_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (B S : list byte) (src : Z),
  wmem rsegs m B -> mem_inv rsegs m ->
  bytes_at rsegs m src S -> length S = 6%nat -> 0 <= src -> src + 6 <= W_BASE_UBSAN ->
  evt rsegs
    (fun ms' => exists R' pc' m', ms' = MS R' F pc' fc None m' (seg_rom rsegs) /\
                 wmem rsegs m' (set_M_desk B S) /\ mem_inv rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (W_BASE_UBSAN + A_M_desk)) (Z_to_bv 64 src) (Z_to_bv 64 6)
             a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 memcpy_entry) fc None m (seg_rom rsegs)).
Proof.
  intros MEMCPY ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m B S src
    WM MI SRC LS Hs Hd.
  wk_facts.
  assert (DST : rw_cells rsegs m (bv_unsigned (Z_to_bv 64 (W_BASE_UBSAN + A_M_desk)))
                  [CB (Z.to_nat (bv_unsigned (Z_to_bv 64 6))) (sub B 4 (Z.to_nat (bv_unsigned (Z_to_bv 64 6))))]).
  { apply (wm_piece rsegs W_BASE_UBSAN m B 4); [exact WM | vm_compute; reflexivity | lia | wk_side | wk_side]. }
  eapply evt_cut.
  { eapply (MEMCPY ra sp gp tp t0 t1 t2 s0 s1 _ _ _ a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S _).
    - rewrite unsigned_lit by lia. exact SRC.
    - rewrite unsigned_lit by lia. exact LS.
    - exact DST.
    - rewrite !unsigned_lit by (unfold A_M_desk, OFF_M; lia). unfold A_M_desk, OFF_M. lia.
    - exact MI. }
  wk_post_call rsegs m.
  apply evt_done. hnf. do 3 eexists. split; [reflexivity|]. split; eassumption.
Qed.

(* ---- a call whose footprint has two spans, its stack window and an out cell inside the world ----
   A made-up 12-byte code image at 0x1000 that calls a made-up callee at 0x2000 and then reads the world:
     0x1000 jal   ra, 0x2000      ra = 0x1004
     0x1004 auipc a5, 0x42        a5 = 0x43004
     0x1008 ld    a0, 0xe4(a5)    a0 = the 8 bytes at 0x430e8 = W_BASE_UBSAN + OFF_g_now *)
Module DemoCallImg.
Import Stdlib.Strings.String Stdlib.Strings.PrimString.
Definition seg : Segment := {|
  seg_base := 0x1000%N; seg_size := 12%N; seg_perms := "r-x"%string;
  seg_bytes := ["ef1000009727040003b5470e"%pstring] |}.
End DemoCallImg.
Definition demo_call_segs : list Segment := [DemoCallImg.seg].

(* The made-up callee has diginet_frame_build's frame clause (fuzz_frame/lib/U/Prog/diginet_frame_build_c.v): it
   writes its 240-byte stack window and the bytes oj at out (a0, length a1), which become g oj. *)
Definition demo_callee_contract (g : list byte -> list byte) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (out lo : Z) (oj : list byte),
    rw_cells demo_call_segs m out [CB (length oj) oj] ->
    stk demo_call_segs m lo (bv_unsigned sp) -> lo + 240 <= bv_unsigned sp ->
    out + Z.of_nat (length oj) <= bv_unsigned sp - 240 \/ bv_unsigned sp <= out ->
    mem_inv demo_call_segs m ->
    evt demo_call_segs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom demo_call_segs) /\
         munch [(bv_unsigned sp - 240, bv_unsigned sp); (out, out + Z.of_nat (length oj))] m m' /\
         wmono demo_call_segs m m' /\ mem_inv demo_call_segs m' /\ stk demo_call_segs m' lo (bv_unsigned sp) /\
         rw_cells demo_call_segs m' out [CB (length oj) (g oj)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 out) (Z_to_bv 64 (Z.of_nat (length oj))) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2000) fc None m (seg_rom demo_call_segs)).

(* The callee fills the 8 bytes of g_now: wm_cell gives its out cell, wk_post_call folds the two-span footprint into
   the world by wm_fill_out (the window misses the world by w_off_stack), and the load after the return reads the
   callee's bytes from the new world. *)
Lemma demo_call2 : forall g, demo_callee_contract g ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (B : list byte) (lo : Z),
  wmem demo_call_segs m B -> mem_inv demo_call_segs m ->
  stk demo_call_segs m lo (bv_unsigned sp) -> lo + 240 <= bv_unsigned sp -> w_off_stack W_BASE_UBSAN sp 240 ->
  evt demo_call_segs
    (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       ms' = MS (mkR (Z_to_bv 64 0x1004) sp gp tp t0' t1' t2' s0 s1
                     (Z_to_bv 64 (u_at (upd B 65000 (g (sub B 65000 8))) 65000 8)) a1' a2' a3' a4'
                     (Z_to_bv 64 0x43004) a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x100c) fc None m' (seg_rom demo_call_segs) /\
       wmem demo_call_segs m' (upd B 65000 (g (sub B 65000 8))) /\ stk demo_call_segs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (W_BASE_UBSAN + 65000)) (Z_to_bv 64 8) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1000) fc None m (seg_rom demo_call_segs)).
Proof.
  intros g CALLEE ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m B lo
    WM MI ST Hlo OFF.
  wk_facts.
  assert (DST : rw_cells demo_call_segs m (W_BASE_UBSAN + 65000) [CB (length (sub B 65000 8)) (sub B 65000 8)])
    by (apply (wm_cell demo_call_segs W_BASE_UBSAN m B 65000 8); [exact WM | reflexivity | lia | wk_side]).
  assert (LO : length (sub B 65000 8) = 8%nat)
    by (apply length_sub; [lia | rewrite (wm_len _ _ _ _ WM); wk_side]).
  step.                                   (* jal ra, 0x2000 *)
  replace (Z_to_bv 64 8) with (Z_to_bv 64 (Z.of_nat (length (sub B 65000 8)))) by (rewrite LO; reflexivity).
  eapply evt_cut.
  { eapply (CALLEE _ sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              (W_BASE_UBSAN + 65000) lo (sub B 65000 8)).
    - exact DST.
    - exact ST.
    - exact Hlo.
    - left. unfold w_off_stack in OFF. rewrite LO. unfold W_LEN in *. lia.
    - exact MI. }
  wk_post_call demo_call_segs m.          (* the world is now upd B 65000 (g (sub B 65000 8)) about the new memory *)
  step.                                   (* auipc a5, 0x42 *)
  step.                                   (* ld a0, 0xe4(a5): a0 = Z_to_bv 64 (u_at (upd B 65000 ..) 65000 8) *)
  apply evt_done. hnf. do 14 eexists. split; [reflexivity|]. split; eassumption.
Qed.

(* ---- a memset into the STACK: the world is carried across the call ----
   memset's post (U/Prog/memset_c.v) states its footprint and its destination at bv_unsigned a0 =
   bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)), still wrapped. wk_post_call shows that the footprint misses the
   world (wk_disj_side: unsigned_lit by lia from the register's range and w_off_stack) and carries the world to the
   memory after the call; no step computes on the open address. *)
Lemma demo_memset_stack : memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (B junk : list byte),
  wmem rsegs m B -> mem_inv rsegs m -> w_off_stack W_BASE_UBSAN sp 64 ->
  rw_cells rsegs m (bv_unsigned sp + -64) [CB 16 junk] ->
  evt rsegs
    (fun ms' => exists R' pc' m', ms' = MS R' F pc' fc None m' (seg_rom rsegs) /\
                 wmem rsegs m' B /\ mem_inv rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + -64)) (Z_to_bv 64 0) (Z_to_bv 64 16)
             a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 MEMSET) fc None m (seg_rom rsegs)).
Proof.
  intros MEMSETC ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m B junk
    WM MI OFF FR.
  wk_facts.
  pose proof (wk_word_range sp) as Rsp.
  eapply evt_cut.
  { eapply (MEMSETC ra sp gp tp t0 t1 t2 s0 s1 _ _ _ a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m junk).
    - rewrite !unsigned_lit by (unfold w_off_stack, W_LEN in *; lia). exact FR.
    - exact MI. }
  wk_post_call rsegs m.                   (* the world WM is now about the memory after memset *)
  apply evt_done. hnf. do 3 eexists. split; [reflexivity|]. split; eassumption.
Qed.

(* ---- a byte store of a REGISTER into the stack, then a world load ----
   A made-up 12-byte code image at 0x1000:
     0x1000 sb    a1, -8(sp)      the byte at sp - 8 := the low byte of a1
     0x1004 auipc a5, 0x42        a5 = 0x43004
     0x1008 ld    a0, 0xe4(a5)    a0 = the 8 bytes at 0x430e8 = W_BASE_UBSAN + OFF_g_now
   The store writes le1 a1. The kit's store aftermath (mem_after_store, Lib/Tac.v:98) turns it into the cell
   C1 (Z_to_bv 8 (bv_unsigned a1)) (cell_of_bytes, Lib/Step.v), carries the world across the store and names the
   new memory, so the world load after it reads g_now. *)
Module DemoSbImg.
Import Stdlib.Strings.String Stdlib.Strings.PrimString.
Definition seg : Segment := {|
  seg_base := 0x1000%N; seg_size := 12%N; seg_perms := "r-x"%string;
  seg_bytes := ["230cb1fe9727040003b5470e"%pstring] |}.
End DemoSbImg.
Definition sb_segs : list Segment := [DemoSbImg.seg].

Lemma demo_sb_stack : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (B junk : list byte),
  wmem sb_segs m B -> mem_inv sb_segs m ->
  rw_cells sb_segs m (bv_unsigned sp + -8) [CB 8 junk] -> W_BASE_UBSAN + W_LEN <= bv_unsigned sp - 8 ->
  evt sb_segs
    (fun ms' => exists a5' m', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (g_now B)) a1 a2 a3 a4 a5' a6 a7
                                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                          F (Z_to_bv 64 0x100c) fc None m' (seg_rom sb_segs) /\
                 wmem sb_segs m' B /\ mem_inv sb_segs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1000) fc None m (seg_rom sb_segs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m B junk
    WM MI FR OFF.
  step.                                   (* sb a1, -8(sp): the stack cell, the world and mem_inv move to the new memory *)
  step.                                   (* auipc a5, 0x42 *)
  step.                                   (* ld a0, 0xf4(a5): a0 = Z_to_bv 64 (u_at B 65000 8) *)
  change (u_at B 65000 8) with (g_now B).
  apply evt_done. hnf. do 2 eexists. split; [reflexivity|]. split; eassumption.
Qed.
