(* diginet_frame_build_iface: what the pieces of the image-B walk of diginet_frame_build (fuzz_frame.asan-ubsan
   0x82670 = frameb_sigma FB_diginet_frame_build) share: the addresses and cut points, the 96-byte frame, the bytes the
   function writes at out, and the STATEMENT of each straight-line piece as a footprint run (lib/Lib/ExecF.v evtF,
   stepped by lib/Lib/StepF.v). Each statement is a Prop here and a Lemma in its own file
   (lib/B/Prog/diginet_frame_build_seg_*.v); lib/B/Prog/diginet_frame_build_walk.v carries them into SRr and cuts each
   call by its callee contract, a premise of the statement lib/B/Prog/diginet_frame_build_cg.v.

   Registers (from the neutral listing): s0 = out, s1 = body_len, s2 = body, s3 = hp, s4 = src (out + 14 from
   0x827bc), s5 = mode, s6 = dst (out + 16 from 0x82808), s7 = cap, s8 = -1 / the length / the result, s9 =
   30 + body_len, s10 = the shadow base.

   Control flow (offsets from the entry):
     +0x000 entry, `addi sp,sp,-96`, ra at 88(sp) and s0 .. s10 at 80(sp) .. 0(sp); s8 := -1; the four `beqz` (out,
            dst, src, hp), the `bnez` of body = 0 with body_len <> 0, `bltu 1,mode`, `bgeu 1484,body_len`
            (body_len > 1484: s8 := -4, to +0x444);
     +0x090 the shadow base through the GOT word (GOT_CELL_K -> CELL_K) into s10, a0 := body, a1 := body_len;
     +0x0a4 call diginet_body_check, returns +0x0a8; a0 <> 0 leaves -10;
     +0x0b4 s9 := 30 + body_len, s8 := max 60 s9; cap < s8 leaves -5;
     +0x0e0 call __asan_memcpy(out, dst, 6), returns +0x0e4;
     +0x0e4 the wrap guard of out + 6, call __asan_memcpy(out + 6, src, 6), returns +0x0fc;
     +0x0fc .. +0x19c the wrap guard of out + 13, the four header stores out+12 .. out+15, each after its shadow check
            and before its wrap guard; s6 := out + 16;
     +0x19c `beqz s5`: mode <> 0 takes a0 := 0, a1 := 0 and jumps to +0x1bc; mode = 0 calls diginet_sum16(body,
            body_len) at +0x1b4, returns +0x1b8, `srli a1,a0,0x8`;
     +0x1bc .. +0x2a4 the stores out+16 .. out+21 (the sum, the send counter: the 4-byte load at hp + 4, after the
            alignment guard of hp at +0x1f8 / +0x1fc);
     +0x2a4 .. +0x40c the stores out+22 .. out+29 (ack at hp + 8, retry at hp + 12, cmd at hp + 14, num_commands at
            hp + 15);
     +0x40c the body copy when body_len <> 0: the wrap guard of out + 30 and call __asan_memcpy(out + 30, body,
            body_len), returns +0x428;
     +0x428 the padding when 30 + body_len < len: the wrap guard of out + 30 + body_len and call
            __asan_memset(out + 30 + body_len, 0, len - 30 - body_len), returns +0x444;
     +0x444 a0 := sext.w s8, the epilogue, `ret`.
   The 23 error-path calls (errpath_store1 x18, errpath_load4 x2, errpath_load2 x1, errpath_load1 x2) are never
   reached: each check reads the shadow byte of its address, and fb_ck_of_addressable turns the addressability of
   the range into exactly the fact the check needs. The 22 branches to the `unimp` at +0x480 are never taken: 21 test
   a wrap of out + K or of s4 + K, false for out + the length of the bytes at out <= 2 ^ 63; the 22nd is the alignment
   test of hp, false for hp mod 4 = 0. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA AsanKAProof.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF.
Import ListNotations.
Open Scope Z_scope.

(** * Addresses *)

Definition FB_ENTRY : Z := transportb_sigma TB_diginet_frame_build.
Definition FB_AT (off : Z) : Z := FB_ENTRY + off.
Definition FB_BC : Z := transportb_sigma TB_diginet_body_check.
Definition FB_CPY : Z := transportb_sigma TB___asan_memcpy.
Definition FB_SET : Z := transportb_sigma TB___asan_memset.
Definition FB_S16 : Z := transportb_sigma TB_diginet_sum16.

(* The cut points, as offsets from the entry (0x82670). *)
Definition FB_RET_BC : Z := FB_AT 0xa8.    (* 0x82718, after `jal diginet_body_check` at 0x82714 *)
Definition FB_RET_C1 : Z := FB_AT 0xe4.    (* 0x82754, after `jal __asan_memcpy` at 0x82750 *)
Definition FB_RET_C2 : Z := FB_AT 0xfc.    (* 0x8276c, after `jal __asan_memcpy` at 0x82768 *)
Definition FB_SUM : Z := FB_AT 0x19c.      (* 0x8280c, `beqz s5` *)
Definition FB_RET_S : Z := FB_AT 0x1b8.    (* 0x82828, after `jal diginet_sum16` at 0x82824 *)
Definition FB_H2 : Z := FB_AT 0x1bc.       (* 0x8282c, the check of out + 16 *)
Definition FB_H2B : Z := FB_AT 0x2a4.      (* 0x82914, `addi a1,s3,8` *)
Definition FB_TAIL : Z := FB_AT 0x40c.     (* 0x82a7c, `beqz s1` *)
Definition FB_RET_C3 : Z := FB_AT 0x428.   (* 0x82a98, after `jal __asan_memcpy` at 0x82a94 *)
Definition FB_EPI : Z := FB_AT 0x444.      (* 0x82ab4, `sext.w a0,s8` *)

(* The function's own frame: 96 bytes. The caller's s10, s9, ..., s0, ra at 0(sp) .. 88(sp). *)
Definition FB_FRAME : Z := 96.
Definition fb_fr (c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word) : list cell :=
  [C8 c10; C8 c9; C8 c8; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra].

Lemma fb_fr_size : forall c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra,
  Z.of_nat (cells_size (fb_fr c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra)) = FB_FRAME.
Proof. intros. reflexivity. Qed.

(** * The values the function computes *)

(* The frame length, over a body length as a number (DgnSpec.frame_len over a nat). *)
Definition fb_len (blen : Z) : Z := Z.max 60 (30 + blen).

Lemma fb_len_frame_len : forall bb : list byte, fb_len (Z.of_nat (length bb)) = frame_len (length bb).
Proof. intros bb. unfold fb_len, frame_len. reflexivity. Qed.

(* The 16-bit sum the header carries: diginet_sum16's result in mode 0 (the call at 0x82824), zero in mode 1
   (`li a0,0` / `li a1,0` at 0x82810 / 0x82814). *)
Definition fb_sum (bb : list byte) (mode : Z) : Z := if mode =? 0 then lib_sum16 bb else 0.

Lemma fb_sum_range : forall bb mode, 0 <= fb_sum bb mode < 2 ^ 16.
Proof.
  intros bb mode. unfold fb_sum. destruct (mode =? 0); [|lia].
  rewrite lib_sum16_eq. apply sum16_range.
Qed.

(* The 12 bytes the function reads at hp + 4 (little endian), as the loads see them. *)
Definition fb_hdr_in (send ack retry cmd ncmds : Z) : list byte :=
  le4 (Z_to_bv 64 send) ++ le4 (Z_to_bv 64 ack) ++ le2 (Z_to_bv 64 retry) ++ [b8 cmd; b8 ncmds].

Lemma fb_hdr_in_length : forall send ack retry cmd ncmds,
  length (fb_hdr_in send ack retry cmd ncmds) = 12%nat.
Proof.
  intros. unfold fb_hdr_in, le4, le2. rewrite !length_app, !length_Z_to_le_bytes. reflexivity.
Qed.

(* The 18 bytes the stores leave at out + 12 (big endian), i.e. bytes 12 .. 29 of DgnSpec.build_frame. *)
Definition fb_hdr18 (send ack retry cmd ncmds sm blen : Z) : list byte :=
  put16 0x885f ++ put16 (16 + blen) ++ put16 sm ++ put32 send ++ put32 ack ++ put16 retry ++ [b8 cmd; b8 ncmds].

Lemma fb_hdr18_length : forall send ack retry cmd ncmds sm blen,
  length (fb_hdr18 send ack retry cmd ncmds sm blen) = 18%nat.
Proof. intros. reflexivity. Qed.

(** * Writing a window of a byte list *)

Definition fb_put (l : list byte) (k : nat) (w : list byte) : list byte :=
  firstn k l ++ w ++ skipn (k + length w)%nat l.

Lemma fb_put_length : forall l k w, (k + length w <= length l)%nat ->
  length (fb_put l k w) = length l.
Proof.
  intros l k w H. unfold fb_put. rewrite !length_app, length_firstn, length_skipn. lia.
Qed.

(* The composition of two adjacent windows, proved by rewriting both sides to the same split of l. *)
Lemma fb_put_app : forall (l : list byte) (k : nat) (w1 w2 : list byte),
  (k + length w1 + length w2 <= length l)%nat ->
  fb_put (fb_put l k w1) (k + length w1) w2 = fb_put l k (w1 ++ w2).
Proof.
  intros l k w1 w2 H. unfold fb_put.
  assert (Hk : (k <= length l)%nat) by lia.
  assert (E1 : firstn (k + length w1) (firstn k l ++ w1 ++ skipn (k + length w1) l) = firstn k l ++ w1).
  { rewrite app_assoc, firstn_app, length_app, length_firstn.
    replace (Nat.min k (length l)) with k by lia.
    rewrite firstn_all2 by (rewrite length_app, length_firstn; lia).
    replace (k + length w1 - (k + length w1))%nat with 0%nat by lia.
    cbn [firstn]. apply app_nil_r. }
  assert (E2 : skipn (k + length w1 + length w2) (firstn k l ++ w1 ++ skipn (k + length w1) l)
             = skipn (k + length w1 + length w2) l).
  { rewrite app_assoc, skipn_app, length_app, length_firstn.
    replace (Nat.min k (length l)) with k by lia.
    rewrite skipn_all2 by (rewrite length_app, length_firstn; lia).
    replace (k + length w1 + length w2 - (k + length w1))%nat with (length w2) by lia.
    rewrite skipn_skipn. cbn [app].
    f_equal. lia. }
  rewrite E1, E2, length_app.
  replace (k + (length w1 + length w2))%nat with (k + length w1 + length w2)%nat by lia.
  rewrite <- !app_assoc. reflexivity.
Qed.

(** * The shadow fact every instrumented check needs *)

(* The check before a w-byte access at x reads the ONE shadow byte of x's granule and, when it is not 0, needs
   x mod 8 + w - 1 < it. Addressability of any range that holds [x, x + w) gives exactly that: read it at the last
   address of the access that still lies in x's granule. *)
Lemma fb_ck_of_addressable : forall m q n x w,
  addressable m q n -> q <= x -> x + w <= q + n -> 1 <= w <= 8 ->
  exists b : byte, mrd rsegs m (wa (shadow_addr x)) = Some b /\
    (bv_signed b = 0 \/ (x mod 8 + w - 1 < bv_signed b /\ bv_signed b <= 7)).
Proof.
  intros m q n x w (Hq & Hn & He & HA) Hqx Hxn Hw.
  set (d := Z.min (x + w - 1) (x - x mod 8 + 7)).
  pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hm.
  assert (Hd1 : x <= d <= x + w - 1) by (unfold d; lia).
  assert (Hd2 : d < q + n) by lia.
  destruct (HA (d - q) ltac:(lia)) as (_ & b & Hb & Hok).
  replace (q + (d - q)) with d in Hb, Hok by lia.
  assert (Hsame : shadow_addr d = shadow_addr x).
  { unfold shadow_addr. f_equal. unfold d.
    pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.div_mod d 8 ltac:(lia)) as Dd.
    pose proof (Z.mod_pos_bound d 8 ltac:(lia)) as Hmd.
    assert (Hlo : 8 * (x / 8) <= d) by lia.
    assert (Hhi : d < 8 * (x / 8) + 8) by lia.
    symmetry. apply (Z.div_unique_pos d 8 (x / 8) (d - 8 * (x / 8))); lia. }
  rewrite Hsame in Hb. exists b. split; [exact Hb|].
  unfold shadow_ok in Hok.
  destruct Hok as [Hz | (Hlt & Hle)]; [left; exact Hz|].
  destruct (Z.le_gt_cases (x mod 8 + w) 8) as [Hin | Hout].
  - right. split; [|exact Hle].
    assert (Ed : d = x + w - 1) by (unfold d; lia).
    assert (Emd : d mod 8 = x mod 8 + w - 1).
    { rewrite Ed. pose proof (Z.div_mod x 8 ltac:(lia)) as Dx.
      symmetry. apply (Z.mod_unique_pos (x + w - 1) 8 (x / 8)); lia. }
    lia.
  - left. exfalso.
    assert (Ed : d = x - x mod 8 + 7) by (unfold d; lia).
    assert (Emd : d mod 8 = 7).
    { rewrite Ed. pose proof (Z.div_mod x 8 ltac:(lia)) as Dx.
      symmetry. apply (Z.mod_unique_pos (x - x mod 8 + 7) 8 (x / 8)); lia. }
    lia.
Qed.

(* A write inside application memory never changes a shadow byte, so addressability survives it. *)
Lemma fb_app_not_shadow : forall a a', app_mem a -> in_shadow a' -> a <> a'.
Proof.
  intros a a' Ha Ha' E. subst a'.
  unfold app_mem, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END in *. lia.
Qed.

Lemma fb_shadow_in_shadow : forall a, app_mem a -> in_shadow (shadow_addr a).
Proof.
  intros a Ha. unfold app_mem, in_shadow, shadow_addr, ASAN_K, LOWMEM_END, LOWSHADOW_END,
    HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END in *.
  destruct Ha as [Ha | Ha]; [left | right]; Z.div_mod_to_equations; lia.
Qed.

Lemma fb_addressable_tp : forall m m' q n lo hi,
  munch [(lo, hi)] m m' -> (forall a, lo <= a < hi -> app_mem a) ->
  addressable m q n -> addressable m' q n.
Proof.
  intros m m' q n lo hi MU HA (Hq & Hn & He & H).
  split; [exact Hq|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (H i Hi) as (Happ & b & Hb & Hok).
  split; [exact Happ|]. exists b. split; [|exact Hok].
  pose proof (fb_shadow_in_shadow (q + i) Happ) as Hs.
  assert (Hrange : 0 <= shadow_addr (q + i) < 2 ^ 64).
  { unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hs. lia. }
  assert (Hdisj : shadow_addr (q + i) < lo \/ hi <= shadow_addr (q + i)).
  { destruct (Z.lt_ge_cases (shadow_addr (q + i)) lo) as [Hlt | Hge]; [left; exact Hlt|].
    destruct (Z.lt_ge_cases (shadow_addr (q + i)) hi) as [Hlt2 | Hge2]; [|right; exact Hge2].
    exfalso. pose proof (HA (shadow_addr (q + i)) (conj Hge Hlt2)) as Happ2.
    unfold app_mem, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG,
      APPMEM_END in Happ2, Hs. lia. }
  exact (mrd_tp m m' lo hi (shadow_addr (q + i)) b MU Hrange Hdisj Hb).
Qed.

(** * The statements of the straight-line pieces *)

(* ---- fb_seg1: FB_ENTRY -> the call of diginet_body_check (mode 0 or 1, body_len <= 1484; body is not 0, or
   body_len is 0: send_control passes body = 0 with body_len = 0) ---- *)
Definition fb_seg1_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (out cap dst src hp body blen mode lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 96 <= bv_unsigned sp ->
    bytes_at rsegs m GOT_CELL_K (le8 (wa CELL_K)) -> bytes_at rsegs m CELL_K (le8 (wa ASAN_K)) ->
    CELL_K + 8 <= bv_unsigned sp - 96 ->
    0 < out < 2 ^ 64 -> 0 < dst < 2 ^ 64 -> 0 < src < 2 ^ 64 -> 0 < hp < 2 ^ 64 -> 0 <= body < 2 ^ 64 ->
    (0 < body \/ blen = 0) -> 0 <= cap < 2 ^ 64 -> 0 <= blen <= 1484 -> (mode = 0 \/ mode = 1) ->
    ExecF.rng RNG (bv_unsigned sp - 96) 96 -> ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m1,
         ms' = MS (mkR (Z_to_bv 64 FB_RET_BC) (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp t0 t1 t2
                     (Z_to_bv 64 out) (Z_to_bv 64 blen)
                     (Z_to_bv 64 body) (Z_to_bv 64 blen) (Z_to_bv 64 dst) (Z_to_bv 64 src) (Z_to_bv 64 hp)
                     (Z_to_bv 64 body) (Z_to_bv 64 blen) (Z_to_bv 64 mode)
                     (Z_to_bv 64 body) (Z_to_bv 64 hp) (Z_to_bv 64 src) (Z_to_bv 64 mode) (Z_to_bv 64 dst)
                     (Z_to_bv 64 cap) (Z_to_bv 64 (-1)) s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FB_BC) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
         rw_cells rsegs m1 (bv_unsigned sp - 96) (fb_fr s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 out) (Z_to_bv 64 cap) (Z_to_bv 64 dst) (Z_to_bv 64 src)
               (Z_to_bv 64 hp) (Z_to_bv 64 body) (Z_to_bv 64 blen) (Z_to_bv 64 mode)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FB_ENTRY) fc None m (seg_rom rsegs)).

(* ---- fb_seg1L: FB_ENTRY -> FB_EPI with s8 = -4 (body_len > 1484) ---- *)
Definition fb_seg1L_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (out cap dst src hp body blen mode lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 96 <= bv_unsigned sp ->
    0 < out < 2 ^ 64 -> 0 < dst < 2 ^ 64 -> 0 < src < 2 ^ 64 -> 0 < hp < 2 ^ 64 -> 0 < body < 2 ^ 64 ->
    0 <= cap < 2 ^ 64 -> 1484 < blen < 2 ^ 64 -> (mode = 0 \/ mode = 1) ->
    ExecF.rng RNG (bv_unsigned sp - 96) 96 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m1,
         ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp t0 t1 t2
                     (Z_to_bv 64 out) (Z_to_bv 64 blen)
                     (Z_to_bv 64 1484) (Z_to_bv 64 0) (Z_to_bv 64 dst) (Z_to_bv 64 src) (Z_to_bv 64 hp)
                     (Z_to_bv 64 body) (Z_to_bv 64 blen) (Z_to_bv 64 mode)
                     (Z_to_bv 64 body) (Z_to_bv 64 hp) (Z_to_bv 64 src) (Z_to_bv 64 mode) (Z_to_bv 64 dst)
                     (Z_to_bv 64 cap) (Z_to_bv 64 (-4)) s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FB_EPI) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
         rw_cells rsegs m1 (bv_unsigned sp - 96) (fb_fr s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 out) (Z_to_bv 64 cap) (Z_to_bv 64 dst) (Z_to_bv 64 src)
               (Z_to_bv 64 hp) (Z_to_bv 64 body) (Z_to_bv 64 blen) (Z_to_bv 64 mode)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FB_ENTRY) fc None m (seg_rom rsegs)).

(* ---- fb_seg1M: FB_ENTRY -> FB_EPI with s8 = -1 (mode not 0 or 1: `bltu 1,mode` taken, before the length test) ---- *)
Definition fb_seg1M_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (out cap dst src hp body blen mode lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 96 <= bv_unsigned sp ->
    0 < out < 2 ^ 64 -> 0 < dst < 2 ^ 64 -> 0 < src < 2 ^ 64 -> 0 < hp < 2 ^ 64 -> 0 <= body < 2 ^ 64 ->
    (0 < body \/ blen = 0) -> 0 <= cap < 2 ^ 64 -> 0 <= blen < 2 ^ 64 ->
    - 2 ^ 31 <= mode < 2 ^ 31 -> mode <> 0 -> mode <> 1 ->
    ExecF.rng RNG (bv_unsigned sp - 96) 96 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a1' : word) m1,
         ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp t0 t1 t2
                     (Z_to_bv 64 out) (Z_to_bv 64 blen)
                     (Z_to_bv 64 1) a1' (Z_to_bv 64 dst) (Z_to_bv 64 src) (Z_to_bv 64 hp)
                     (Z_to_bv 64 body) (Z_to_bv 64 blen) (Z_to_bv 64 mode)
                     (Z_to_bv 64 body) (Z_to_bv 64 hp) (Z_to_bv 64 src) (Z_to_bv 64 mode) (Z_to_bv 64 dst)
                     (Z_to_bv 64 cap) (Z_to_bv 64 (-1)) s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FB_EPI) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
         rw_cells rsegs m1 (bv_unsigned sp - 96) (fb_fr s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 out) (Z_to_bv 64 cap) (Z_to_bv 64 dst) (Z_to_bv 64 src)
               (Z_to_bv 64 hp) (Z_to_bv 64 body) (Z_to_bv 64 blen) (Z_to_bv 64 mode)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FB_ENTRY) fc None m (seg_rom rsegs)).

(* ---- fb_seg2R: FB_RET_BC with a0 <> 0 -> FB_EPI with s8 = -10 ---- *)
Definition fb_seg2R_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    bv_unsigned a0 <> 0 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 (Z_to_bv 64 (-10)) s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FB_EPI) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FB_RET_BC) fc None m (seg_rom rsegs)).

(* ---- fb_seg2S: FB_RET_BC with a0 = 0 and cap < fb_len -> FB_EPI with s8 = -5 ---- *)
Definition fb_seg2S_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11
          t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (blen cap : Z),
    bv_unsigned a0 = 0 -> 0 <= blen <= 1484 -> 0 <= cap < 2 ^ 64 -> cap < fb_len blen ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 blen) (Z_to_bv 64 30) a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 (Z_to_bv 64 cap) (Z_to_bv 64 (-5)) (Z_to_bv 64 (30 + blen)) s10 s11
                     t3 t4 t5 t6)
                   F (Z_to_bv 64 FB_EPI) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 blen) a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 (Z_to_bv 64 cap) s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FB_RET_BC) fc None m (seg_rom rsegs)).

(* ---- fb_seg2C: FB_RET_BC with a0 = 0 and fb_len <= cap -> the first __asan_memcpy ---- *)
Definition fb_seg2C_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s8 s9 s10 s11
          t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (out dst blen cap : Z),
    bv_unsigned a0 = 0 -> 0 <= blen <= 1484 -> 0 <= cap < 2 ^ 64 -> fb_len blen <= cap ->
    0 < out < 2 ^ 64 -> 0 < dst < 2 ^ 64 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR (Z_to_bv 64 FB_RET_C1) sp gp tp t0 t1 t2 (Z_to_bv 64 out) (Z_to_bv 64 blen)
                     (Z_to_bv 64 out) (Z_to_bv 64 dst) (Z_to_bv 64 6) a3 a4 a5 a6 a7
                     s2 s3 s4 s5 (Z_to_bv 64 dst) (Z_to_bv 64 cap) (Z_to_bv 64 (fb_len blen))
                     (Z_to_bv 64 (30 + blen)) s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FB_CPY) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 out) (Z_to_bv 64 blen) a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 (Z_to_bv 64 dst) (Z_to_bv 64 cap) s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FB_RET_BC) fc None m (seg_rom rsegs)).

(* ---- fb_seg3: FB_RET_C1 -> the second __asan_memcpy (the wrap guard of out + 6 at 0x82758 not taken) ---- *)
Definition fb_seg3_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11
          t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (out src : Z),
    0 < out -> out + 6 < 2 ^ 64 -> 0 < src < 2 ^ 64 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR (Z_to_bv 64 FB_RET_C2) sp gp tp t0 t1 t2 (Z_to_bv 64 out) s1
                     (Z_to_bv 64 (out + 6)) (Z_to_bv 64 src) (Z_to_bv 64 6) a3 a4 a5 a6 a7
                     s2 s3 (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FB_CPY) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 out) s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FB_RET_C1) fc None m (seg_rom rsegs)).

(* ---- fb_h1: FB_RET_C2 -> FB_SUM: the four stores out+12 .. out+15, s4 := out + 14, s6 := out + 16 ---- *)
Definition fb_h1_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11
          t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (out blen : Z) (l : list byte),
    0 < out -> out + Z.of_nat (length l) <= 2 ^ 63 -> (30 <= length l)%nat ->
    0 <= blen <= 1484 ->
    rw_cells rsegs m out [CB (length l) l] ->
    addressable m (out + 12) 4 ->
    ExecF.rng RNG (out + 12) 4 ->
    ExecF.rng RNG (shadow_addr (out + 12)) (shadow_addr (out + 15) - shadow_addr (out + 12) + 1) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a0' a1' a2' a3' : word) (m1 : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 out) (Z_to_bv 64 blen)
                     a0' a1' a2' a3' a4 a5 a6 a7
                     s2 s3 (Z_to_bv 64 (out + 14)) s5 (Z_to_bv 64 (out + 16)) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11
                     t3 t4 t5 t6)
                   F (Z_to_bv 64 FB_SUM) fc None m1 (seg_rom rsegs) /\
         munch [(out + 12, out + 16)] m m1 /\ wmono rsegs m m1 /\
         rw_cells rsegs m1 out [CB (length l) (fb_put l 12 (put16 0x885f ++ put16 (16 + blen)))])
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 out) (Z_to_bv 64 blen) a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FB_RET_C2) fc None m (seg_rom rsegs)).

(* ---- fb_sumZ: FB_SUM with s5 = mode <> 0 -> FB_H2 with a0 = a1 = 0 ---- *)
Definition fb_sumZ_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    bv_unsigned s5 <> 0 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FB_H2) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FB_SUM) fc None m (seg_rom rsegs)).

(* ---- fb_sumC: FB_SUM with s5 = mode = 0 -> the call of diginet_sum16 (a0 := s2, a1 := s1) ---- *)
Definition fb_sumC_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    bv_unsigned s5 = 0 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR (Z_to_bv 64 FB_RET_S) sp gp tp t0 t1 t2 s0 s1 s2 s1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FB_S16) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FB_SUM) fc None m (seg_rom rsegs)).

(* ---- fb_sumR: FB_RET_S -> FB_H2: `srli a1,a0,0x8` ---- *)
Definition fb_sumR_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sm : Z),
    0 <= sm < 2 ^ 64 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 sm) (Z_to_bv 64 (sm / 2 ^ 8)) a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FB_H2) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 sm) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FB_RET_S) fc None m (seg_rom rsegs)).

(* ---- fb_h2a: FB_H2 -> FB_H2B: the stores out+16 .. out+21 (the sum in a1 / a0, the alignment guard of hp, then
   the send counter loaded from hp + 4) ---- *)
Definition fb_h2a_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s9 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (out hp send ack retry cmd ncmds sm : Z) (l : list byte),
    0 < out -> out + Z.of_nat (length l) <= 2 ^ 63 -> (30 <= length l)%nat ->
    0 < hp -> hp + 16 <= 2 ^ 63 -> hp mod 4 = 0 ->
    0 <= send < 2 ^ 32 -> 0 <= ack < 2 ^ 32 -> 0 <= retry < 2 ^ 16 -> 0 <= cmd < 2 ^ 8 -> 0 <= ncmds < 2 ^ 8 ->
    0 <= sm < 2 ^ 16 ->
    (out + Z.of_nat (length l) <= hp + 4 \/ hp + 16 <= out) ->
    rw_cells rsegs m out [CB (length l) l] ->
    bytes_at rsegs m (hp + 4) (fb_hdr_in send ack retry cmd ncmds) ->
    addressable m (out + 12) 18 -> addressable m (hp + 4) 12 ->
    ExecF.rng RNG (out + 12) 18 -> ExecF.rng RNG (hp + 4) 12 ->
    ExecF.rng RNG (shadow_addr (out + 12)) (shadow_addr (out + 29) - shadow_addr (out + 12) + 1) ->
    ExecF.rng RNG (shadow_addr (hp + 4)) (shadow_addr (hp + 15) - shadow_addr (hp + 4) + 1) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a0' a1' a2' a3' a4' : word) (m1 : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 out) s1 a0' a1' a2' a3' a4' a5 a6 a7
                     s2 (Z_to_bv 64 hp) (Z_to_bv 64 (out + 14)) s5 (Z_to_bv 64 (out + 16)) s7 s8 s9
                     (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FB_H2B) fc None m1 (seg_rom rsegs) /\
         munch [(out + 16, out + 22)] m m1 /\ wmono rsegs m m1 /\
         rw_cells rsegs m1 out [CB (length l) (fb_put l 16 (put16 sm ++ put32 send))])
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 out) s1 (Z_to_bv 64 sm) (Z_to_bv 64 (sm / 2 ^ 8))
               a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 hp) (Z_to_bv 64 (out + 14)) s5 (Z_to_bv 64 (out + 16)) s7 s8 s9
               (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FB_H2) fc None m (seg_rom rsegs)).

(* ---- fb_h2b: FB_H2B -> FB_TAIL: the stores out+22 .. out+29 (ack, retry, cmd, num_commands) ---- *)
Definition fb_h2b_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (out hp send ack retry cmd ncmds : Z) (l : list byte),
    0 < out -> out + Z.of_nat (length l) <= 2 ^ 63 -> (30 <= length l)%nat ->
    0 < hp -> hp + 16 <= 2 ^ 63 -> hp mod 4 = 0 ->
    0 <= send < 2 ^ 32 -> 0 <= ack < 2 ^ 32 -> 0 <= retry < 2 ^ 16 -> 0 <= cmd < 2 ^ 8 -> 0 <= ncmds < 2 ^ 8 ->
    (out + Z.of_nat (length l) <= hp + 4 \/ hp + 16 <= out) ->
    rw_cells rsegs m out [CB (length l) l] ->
    bytes_at rsegs m (hp + 4) (fb_hdr_in send ack retry cmd ncmds) ->
    addressable m (out + 12) 18 -> addressable m (hp + 4) 12 ->
    ExecF.rng RNG (out + 12) 18 -> ExecF.rng RNG (hp + 4) 12 ->
    ExecF.rng RNG (shadow_addr (out + 12)) (shadow_addr (out + 29) - shadow_addr (out + 12) + 1) ->
    ExecF.rng RNG (shadow_addr (hp + 4)) (shadow_addr (hp + 15) - shadow_addr (hp + 4) + 1) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (a0' a1' a2' a3' a4' : word) (m1 : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 out) s1 a0' a1' a2' a3' a4' a5 a6 a7
                     s2 (Z_to_bv 64 hp) (Z_to_bv 64 (out + 14)) s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11
                     t3 t4 t5 t6)
                   F (Z_to_bv 64 FB_TAIL) fc None m1 (seg_rom rsegs) /\
         munch [(out + 22, out + 30)] m m1 /\ wmono rsegs m m1 /\
         rw_cells rsegs m1 out
           [CB (length l) (fb_put l 22 (put32 ack ++ put16 retry ++ [b8 cmd; b8 ncmds]))])
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 out) s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 (Z_to_bv 64 hp) (Z_to_bv 64 (out + 14)) s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FB_H2B) fc None m (seg_rom rsegs)).

(* ---- fb_seg4Z: FB_TAIL with s1 = 0 -> FB_RET_C3 ---- *)
Definition fb_seg4Z_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0) a0 a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FB_RET_C3) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0) a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FB_TAIL) fc None m (seg_rom rsegs)).

(* ---- fb_seg4: FB_TAIL with s1 = body_len <> 0 -> the third __asan_memcpy (the wrap guard of out + 30 at
   0x82a84 not taken) ---- *)
Definition fb_seg4_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11
          t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (out body blen : Z),
    0 < out -> out + 31 <= 2 ^ 64 -> 0 < body < 2 ^ 64 -> 0 < blen <= 1484 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR (Z_to_bv 64 FB_RET_C3) sp gp tp t0 t1 t2 (Z_to_bv 64 out) (Z_to_bv 64 blen)
                     (Z_to_bv 64 (out + 30)) (Z_to_bv 64 body) (Z_to_bv 64 blen) a3 a4 a5 a6 a7
                     (Z_to_bv 64 body) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FB_CPY) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 out) (Z_to_bv 64 blen) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 body) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FB_TAIL) fc None m (seg_rom rsegs)).

(* ---- fb_seg5Z: FB_RET_C3 with 30 + body_len >= len -> FB_EPI ---- *)
Definition fb_seg5Z_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11
          t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (blen : Z),
    30 <= blen <= 1484 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 (Z_to_bv 64 (fb_len blen)) (Z_to_bv 64 (30 + blen)) s10 s11
                     t3 t4 t5 t6)
                   F (Z_to_bv 64 FB_EPI) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 (Z_to_bv 64 (fb_len blen)) (Z_to_bv 64 (30 + blen)) s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FB_RET_C3) fc None m (seg_rom rsegs)).

(* ---- fb_seg5: FB_RET_C3 with 30 + body_len < len -> the __asan_memset (the wrap guard of out + 30 + body_len at
   0x82aa0 not taken) ---- *)
Definition fb_seg5_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s10 s11
          t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (out blen : Z),
    0 < out -> out + 60 < 2 ^ 64 -> 0 <= blen < 30 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR (Z_to_bv 64 FB_EPI) sp gp tp t0 t1 t2 (Z_to_bv 64 out) s1
                     (Z_to_bv 64 (out + 30 + blen)) (Z_to_bv 64 0) (Z_to_bv 64 (30 - blen)) a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 (Z_to_bv 64 60) (Z_to_bv 64 (30 + blen)) s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FB_SET) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 out) s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 (Z_to_bv 64 60) (Z_to_bv 64 (30 + blen)) s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FB_RET_C3) fc None m (seg_rom rsegs)).

(* ---- fb_epi: FB_EPI -> the return: a0 := sext.w s8, the frame reloaded, sp += 96, `ret` ---- *)
Definition fb_epi_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11
          t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (v : Z) (c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word),
    rw_cells rsegs m (bv_unsigned sp) (fb_fr c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) ->
    bv_unsigned sp + 96 < 2 ^ 64 ->
    ExecF.rng RNG (bv_unsigned sp) 96 ->
    - 2 ^ 31 <= v < 2 ^ 31 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR cra (Z_to_bv 64 (bv_unsigned sp + 96)) gp tp t0 t1 t2 c0 c1
                     (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7
                     c2 c3 c4 c5 c6 c7 c8 c9 c10 s11 t3 t4 t5 t6)
                   F (ret_pc cra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 (Z_to_bv 64 v) s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FB_EPI) fc None m (seg_rom rsegs)).
