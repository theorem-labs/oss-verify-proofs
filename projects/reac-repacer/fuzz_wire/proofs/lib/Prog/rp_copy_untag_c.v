From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Arr.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(* size_t rp_copy_untag(uint8_t *f, size_t n)   repace_wire.c:88-99:
     if (n < 50) return 0;
     if (is_tagged_reac(f)) { memmove(f + 12, f + 16, n - 16); n -= 4; }
     if (!reac_frame_is_reac(f, n) || !is_audio(f)) return 0;
     return n;
   is_tagged_reac(f) = f[12] == 0x81 && f[13] == 0x00 && f[16] == 0x88 && f[17] == 0x19 (repace_wire.c:23-26),
   is_audio(f) = f[16] == 0x00 && f[17] == 0x00 (repace_wire.c:29-32), reac_frame_is_reac(f, n) = f != NULL && n >= 14
   && f[12] == 0x88 && f[13] == 0x19 (libreac reac.c); both are decided on the frame AFTER the memmove, cu_bytes.
   Past n >= 50, f >= 8 and n >= 50 make reac_frame_is_reac's own exits (f == NULL, n < 14) unreachable, so
   copy_untag_result states the bytes test only.
   Form: libreac/fuzz_decode's reac_decode_c.v for a function with a 32-byte stack frame (stk, munch over that frame and
   the bytes the function writes, wmono), with libreac/fuzz_pcap's memmove_c.v vocabulary (u8arr, mem_inv) for the
   frame it moves: the memmove call writes exactly f[12 .. n-4) (cu_footprint), with the bytes cu_bytes, and every
   other byte outside the stack frame keeps its value. *)
Definition RP_COPY_UNTAG : Z := 0x13690.

Definition cu_byte (bs : list byte) (i : nat) : Z := bv_unsigned (nth i bs (Z_to_bv 8 0)).

Definition cu_tagged (bs : list byte) : bool :=
  (cu_byte bs 12 =? 0x81) && (cu_byte bs 13 =? 0x00) && (cu_byte bs 16 =? 0x88) && (cu_byte bs 17 =? 0x19).

Definition cu_moves (n : Z) (bs : list byte) : bool := (50 <=? n) && cu_tagged bs.

(* the frame after the call: memmove(f + 12, f + 16, n - 16) when it moves *)
Definition cu_bytes (n : Z) (bs : list byte) : list byte :=
  if cu_moves n bs then upd_bytes bs 12 (firstn (Z.to_nat (n - 16)) (skipn 16 bs)) else bs.

Definition cu_len (n : Z) (bs : list byte) : Z := if cu_moves n bs then n - 4 else n.

Definition copy_untag_result (n : Z) (bs : list byte) : Z :=
  if n <? 50 then 0
  else if (cu_byte (cu_bytes n bs) 12 =? 0x88) && (cu_byte (cu_bytes n bs) 13 =? 0x19)
          && (cu_byte (cu_bytes n bs) 16 =? 0x00) && (cu_byte (cu_bytes n bs) 17 =? 0x00)
       then cu_len n bs else 0.

(* the frame bytes the call writes *)
Definition cu_footprint (f n : Z) (bs : list byte) : list ivl :=
  if cu_moves n bs then [(f + 12, f + n - 4)] else [].

Definition rp_copy_untag_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp ->
    mem_inv rsegs m ->
    (50 <= bv_unsigned a1 ->
       u8arr rsegs m (bv_unsigned a0) bs /\ bv_unsigned a1 <= Z.of_nat (length bs) /\ bv_unsigned a1 < 2^62 /\
       8 <= bv_unsigned a0 /\
       (bv_unsigned a0 + Z.of_nat (length bs) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (copy_untag_result (bv_unsigned a1) bs))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         munch ((bv_unsigned sp - 32, bv_unsigned sp) :: cu_footprint (bv_unsigned a0) (bv_unsigned a1) bs) m m' /\
         (50 <= bv_unsigned a1 -> u8arr rsegs m' (bv_unsigned a0) (cu_bytes (bv_unsigned a1) bs)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RP_COPY_UNTAG) fc None m (seg_rom rsegs)).

(* Satisfiability at check_copy's call (fuzz_wire.c:184-210, rp_copy_untag(c, n)): a0 = c, the copy fuzz_dup put at the
   heap address 0x50010 (above every loaded segment, which end at or below 0x50000), a1 = n = 344, its length; sp =
   rp_copy_untag's entry sp 0x7fffffffe690 = check_copy's entry sp 0x7fffffffe6c0 - check_copy's frame 0x30 (addi sp,
   sp, -0x30 at plain 0x13378 / U 0x13550), over a 4 KiB stack window [lo, sp), lo = 0x7fffffffd690, disjoint from the
   heap copy. The frame is a REAC audio frame of 8 channels behind one 802.1Q tag (52 + 8 * 36 + 4 bytes; 0x81 0x00 at
   bytes 12-13, EtherType 0x8819 at 16-17, type 00 00 at 20-21), so every guard holds, the call takes the memmove
   path and returns 340, the untagged length. The memory holds exactly the copy and the stack window (mem_inv: no byte
   in a read-only segment).
   sp convention of the fuzz_wire sat lemmas: 0x7fffffffe700 is LLVMFuzzerTestOneInput's entry sp; its frame is 0x40
   (addi sp, sp, -0x40 at plain 0x12d78 / U 0x12dc0), so every check_* is entered at sp 0x7fffffffe6c0. *)
Definition cu_sat_frame : list byte :=
  map (Z_to_bv 8) [0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0x00; 0x1d; 0xc1; 0x00; 0x00; 0x01; 0x81; 0x00; 0x00; 0x05;
                   0x88; 0x19; 0x34; 0x12; 0x00; 0x00] ++ repeat (Z_to_bv 8 0) 322.

Definition cu_sat_mem : word -> option byte :=
  write_to_mem (write_to_mem (fun _ => None) (wa 0x50010) cu_sat_frame) (wa 0x7fffffffd690)
    (repeat (Z_to_bv 8 0) 4096).

Lemma cu_noseg : forall x, 0x50000 <= x -> find_segment rsegs x 1 = None.
Proof.
  intros x Hx.
  assert (C : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x50000) rsegs = true)
    by (vm_compute; reflexivity).
  revert C. generalize rsegs. intros l. induction l as [|s l IH]; intros C; [reflexivity|].
  cbn [forallb] in C. apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1.
  cbn [find_segment].
  destruct (Z.leb (Z.of_N (seg_base s)) x && Z.leb (x + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s))) eqn:E.
  - apply andb_prop in E as [_ E2]. apply Z.leb_le in E2. lia.
  - apply IH. exact C2.
Qed.

Lemma cu_written : forall m (A : Z) bs (a : Z), 0 <= A -> A + Z.of_nat (length bs) <= 2^64 ->
  A <= a < A + Z.of_nat (length bs) -> exists b, write_to_mem m (wa A) bs (wa a) = Some b.
Proof.
  intros m A bs a H0 H1 Ha. rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
  destruct (Z.leb_spec0 A a); destruct (Z.ltb_spec0 a (A + Z.of_nat (length bs))); cbn [andb]; try (exfalso; lia).
  destruct (nth_error bs (Z.to_nat (a - A))) eqn:E; [eexists; reflexivity|].
  apply nth_error_None in E. lia.
Qed.

Lemma rp_copy_untag_premises_sat :
  let a0 := Z_to_bv 64 0x50010 in
  let a1 := Z_to_bv 64 344 in
  let sp := Z_to_bv 64 0x7fffffffe690 in
  let lo := 0x7fffffffd690 in
  Z.of_nat (length cu_sat_frame) = bv_unsigned a1 /\
  cu_moves (bv_unsigned a1) cu_sat_frame = true /\ copy_untag_result (bv_unsigned a1) cu_sat_frame = 340 /\
  stk rsegs cu_sat_mem lo (bv_unsigned sp) /\ lo + 32 <= bv_unsigned sp /\
  mem_inv rsegs cu_sat_mem /\
  (50 <= bv_unsigned a1 ->
     u8arr rsegs cu_sat_mem (bv_unsigned a0) cu_sat_frame /\ bv_unsigned a1 <= Z.of_nat (length cu_sat_frame) /\
     bv_unsigned a1 < 2^62 /\ 8 <= bv_unsigned a0 /\
     (bv_unsigned a0 + Z.of_nat (length cu_sat_frame) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)).
Proof.
  cbv zeta.
  assert (L : length cu_sat_frame = 344%nat)
    by (unfold cu_sat_frame; rewrite app_length, map_length, repeat_length; reflexivity).
  assert (LS : length (repeat (Z_to_bv 8 0) 4096) = 4096%nat) by apply repeat_length.
  rewrite !unsigned_lit by lia.
  split; [rewrite L; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  split; [|split; [lia|split]].
  - (* the stack window is written *)
    split; [lia|]. split; [lia|]. intros a Ha.
    destruct (cu_written (write_to_mem (fun _ => None) (wa 0x50010) cu_sat_frame) 0x7fffffffd690
                (repeat (Z_to_bv 8 0) 4096) a ltac:(lia) ltac:(rewrite LS; lia) ltac:(rewrite LS; lia)) as [b Hb].
    unfold cu_sat_mem, wview, mrd. rewrite Hb. split; [discriminate | eexists; reflexivity].
  - (* every byte of the memory is above the image *)
    intros x b Hx. unfold cu_sat_mem in Hx.
    apply write_to_mem_some in Hx as [Hx | (i & Hi & ->)].
    + apply write_to_mem_some in Hx as [Hx | (i & Hi & ->)]; [discriminate|].
      unfold ro_addr. rewrite (wa_unsigned 0x50010) by lia. rewrite wa_unsigned by (rewrite L in Hi; lia).
      rewrite cu_noseg; [reflexivity|]. lia.
    + unfold ro_addr. rewrite (wa_unsigned 0x7fffffffd690) by lia. rewrite wa_unsigned by (rewrite LS in Hi; lia).
      rewrite cu_noseg; [reflexivity|]. lia.
  - intros _. split; [|split; [rewrite L; lia|split; [lia|split; [lia|left; rewrite L; lia]]]].
    unfold cu_sat_mem. split.
    + apply bytes_at_write_other;
        [apply bytes_at_write_same; rewrite ?L; lia | lia | rewrite LS; lia | rewrite L, LS; lia].
    + apply wr_at_write. split; [lia|]. split; [rewrite L; lia|]. intros i Hi.
      destruct (cu_written (fun _ => None) 0x50010 cu_sat_frame (0x50010 + i) ltac:(lia) ltac:(rewrite L; lia)
                  ltac:(rewrite L in Hi; lia)) as [b Hb].
      unfold wview. rewrite Hb. discriminate.
Qed.
