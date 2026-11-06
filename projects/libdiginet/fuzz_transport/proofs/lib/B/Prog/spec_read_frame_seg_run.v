(* spec_read_frame_seg_run: the shared definitions of the footprint runs (lib/Lib/ExecF.v evtF) of spec_read_frame on
   fuzz_transport.asan-ubsan (entry 0x839c0 = transportb_sigma TB_spec_read_frame, listing
   lib/B/Prog/DgnTransportBList.v), for the caller-journal walk of lib/B/Prog/spec_read_frame_cg.v
   (lib/B/Prog/spec_read_frame_cgW.v), and run 1:
     srf_run1_F  0x839c0 .. the call of __asan_memset at 0x839fc: `addi sp,sp,-48`, the five saves (ra, s0 .. s3 at
                 sp + 40 .. sp + 8), s0 = fp, s1 = len, s3 = the shadow base (read through the GOT word of the runtime
                 cell), s2 = b, a0 = fp, a1 = 0, a2 = 80, `jal __asan_memset` (ra = 0x83a00).
   Run 2, from the memset's return to the `ret`, is lib/B/Prog/spec_read_frame_seg_head.v, _seg_mid.v and _seg_tail.v;
   it reads its memory facts from the bundle srf_cx below (the frame bytes, the shadow bytes the checks read, the
   frame's five saves, all at the memory m0 the memset returned, and the footprint), and keeps every memory it runs
   through related to m0 by `munch [(fp, fp + 80)] m0 m`: run 2 writes only the struct. The struct itself is carried as
   rw_cells over srf_cells, its 18 fields and padding runs (lib/Prog/T/TContract.v sf_bytes), so every store of run 2
   hits one whole cell. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA AsanKAProof.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require TContract.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module DS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module TCt := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.TContract.

Definition SRF_ENTRY : Z := 0x839c0.
Definition SRF_MEMSET : Z := 0x52888.     (* transportb_sigma TB___asan_memset *)
Definition SRF_RET1 : Z := 0x83a00.       (* the memset's return address *)

(* The frame the prologue writes: sp + 0 .. sp + 7 unused, then s3, s2, s1, s0, ra. *)
Definition srf_fr (junk : list byte) (c3 c2 c1 c0 cra : word) : list cell :=
  [CB 8 junk; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra].

(* ---- run 1: the entry to the call of __asan_memset ---- *)

Lemma srf_run1_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo b len fp : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp ->
    ro_cells rsegs m GOT_CELL_K [C8 (wa CELL_K)] -> ro_cells rsegs m CELL_K [C8 (wa ASAN_K)] ->
    GOT_CELL_K + 8 <= bv_unsigned sp - 48 -> CELL_K + 8 <= bv_unsigned sp - 48 ->
    ExecF.rng RNG (bv_unsigned sp - 48) 48 -> ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m1 junk,
         ms' = MS (mkR (Z_to_bv 64 SRF_RET1) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2
                    (Z_to_bv 64 fp) (Z_to_bv 64 len) (Z_to_bv 64 fp) (Z_to_bv 64 0) (Z_to_bv 64 80) a3 a4 a5 a6 a7
                    (Z_to_bv 64 b) (Z_to_bv 64 ASAN_K) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 SRF_MEMSET) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
         stk rsegs m1 lo (bv_unsigned sp + -48) /\
         rw_cells rsegs m1 (bv_unsigned sp + -48) (srf_fr junk s3 s2 s1 s0 ra) /\
         ro_cells rsegs m1 GOT_CELL_K [C8 (wa CELL_K)] /\ ro_cells rsegs m1 CELL_K [C8 (wa ASAN_K)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 b) (Z_to_bv 64 len) (Z_to_bv 64 fp) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SRF_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo b len fp
    ST LO RG RC DG DC RFR RGOT RCELL.
  unfold SRF_ENTRY, SRF_RET1, SRF_MEMSET.
  unfold GOT_CELL_K, CELL_K, ASAN_K in *.
  pose proof (u64_range sp) as Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  (* 0x839c0 .. 0x839d4: the frame and the five saves *)
  do 6 step.
  (* 0x839d8 .. 0x839fc: s0 = fp, s1 = len, the GOT word, s3 = the shadow base, s2 = b, a2 = 80, a0 = fp, a1 = 0,
     jal __asan_memset *)
  unfold wa in RG, RC.
  do 10 step.
  lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => apply evtF_done; exists mm end.
  lazymatch goal with H : rw_cells _ _ _ (CB 8 ?j :: _) |- _ => exists j end.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact ST|]. split; [exact FR|].
  split; assumption.
Qed.

(* ---- run 2: what it starts from ---- *)

(* Byte j of the frame. *)
Definition srf_fb (frame : list byte) (j : Z) : byte := nth (Z.to_nat j) frame (Z_to_bv 8 0).

(* The struct's 80 bytes as 18 cells: the fields of struct spec_frame (spec.h:188-197) and its three padding runs, in
   the order of TContract.sf_bytes. Every store of run 2 writes one whole cell. *)
Definition srf_cells (code dst src et nb sm rt sd ak : Z) (cm nc : byte) (bd bl pl bs : Z) : list cell :=
  [C4 (Z_to_bv 64 code); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 dst); C8 (Z_to_bv 64 src);
   C2 (Z_to_bv 64 et); C2 (Z_to_bv 64 nb); C2 (Z_to_bv 64 sm); C2 (Z_to_bv 64 rt);
   C4 (Z_to_bv 64 sd); C4 (Z_to_bv 64 ak); C1 cm; C1 nc; CB 6 (repeat (Z_to_bv 8 0) 6);
   C8 (Z_to_bv 64 bd); C8 (Z_to_bv 64 bl); C8 (Z_to_bv 64 pl); C2 (Z_to_bv 64 bs); CB 6 (repeat (Z_to_bv 8 0) 6)].

(* What run 2 reads, at the memory m0 the memset returned: the bounds, the separations its reads need (each frame
   byte, each shadow byte it reads and the five saves lie outside the struct, the only bytes it writes), the frame's
   bytes, the shadow bytes of the frame (0, or above the byte's offset in its granule) and of the struct (0), the five
   saves, and the footprint. *)
Definition srf_cx (RNG : ExecF.footprint) (m0 : word -> option byte) (sp : word) (b len fp : Z)
    (frame junk : list byte) (c3 c2 c1 c0 cra : word) : Prop :=
  (0 < b /\ 0 <= len /\ len <= Z.of_nat (length frame) /\ b + len <= 2 ^ 63 /\
   0 <= fp /\ fp mod 8 = 0 /\ fp + 80 <= 2 ^ 63 /\ 48 <= bv_unsigned sp) /\
  ((forall i, 0 <= i < len -> b + i < fp \/ fp + 80 <= b + i) /\
   (forall i, 0 <= i < len -> (b + i) / 8 + ASAN_K < fp \/ fp + 80 <= (b + i) / 8 + ASAN_K) /\
   (forall i, 0 <= i < 80 -> (fp + i) / 8 + ASAN_K < fp \/ fp + 80 <= (fp + i) / 8 + ASAN_K) /\
   (fp + 80 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= fp)) /\
  ((forall i, 0 <= i < len -> mrd rsegs m0 (wa (b + i)) = Some (srf_fb frame i)) /\
   (forall i, 0 <= i < len -> exists k : byte, mrd rsegs m0 (wa ((b + i) / 8 + ASAN_K)) = Some k /\
      (bv_signed k = 0 \/ (b + i) mod 8 < bv_signed k)) /\
   (forall i, 0 <= i < 80 -> mrd rsegs m0 (wa ((fp + i) / 8 + ASAN_K)) = Some (Z_to_bv 8 0)) /\
   rw_cells rsegs m0 (bv_unsigned sp + -48) (srf_fr junk c3 c2 c1 c0 cra)) /\
  (ExecF.rng RNG (bv_unsigned sp - 48) 48 /\ ExecF.rng RNG fp 80 /\ ExecF.rng RNG b len /\
   (forall i, 0 <= i < 80 -> ExecF.rng RNG ((fp + i) / 8 + ASAN_K) 1) /\
   (forall i, 0 <= i < len -> ExecF.rng RNG ((b + i) / 8 + ASAN_K) 1)).

(* What run 2 leaves at the `ret`: the caller's ra, sp, gp, tp and callee-saved registers, a0 = the code, the struct's
   80 bytes SB, every byte outside the struct as at m0. *)
Definition srf_q2 (sp gp tp cra c0 c1 c2 c3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (fp code : Z) (SB : list byte) : machine_state -> Prop :=
  fun ms' => exists (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 spx : word) (m' : word -> option byte),
    ms' = MS (mkR cra spx gp tp x5 x6 x7 c0 c1 (Z_to_bv 64 code) x11 x12 x13 x14 x15 x16 x17
                  c2 c3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (ret_pc cra) fc None m' (seg_rom rsegs) /\
    bv_unsigned spx = bv_unsigned sp /\
    munch [(fp, fp + 80)] m0 m' /\ wmono rsegs m0 m' /\ bytes_at rsegs m' fp SB.

(* ---- run 2: the memory and arithmetic facts its steps use ---- *)

(* A byte outside the struct, read at a memory that differs from m0 only in the struct. *)
Lemma srf_rd1 : forall m0 m fp a x, munch [(fp, fp + 80)] m0 m -> 0 <= a < 2 ^ 64 -> (a < fp \/ fp + 80 <= a) ->
  mrd rsegs m0 (wa a) = Some x -> ov_read_bytes rsegs m (wa a) 1 = Some [x].
Proof.
  intros m0 m fp a x MU Ha Hd H. apply rd1. unfold mrd in *. rewrite MU; [exact H|].
  rewrite wa_unsigned by lia. cbn [outside]. split; [lia | exact I].
Qed.

(* `srli rd,rs,3` of an address below 2^64. *)
Lemma srf_shr3 : forall x, 0 <= x < 2 ^ 64 -> Z.shiftr (bv_unsigned (Z_to_bv 64 x)) 3 = x / 8.
Proof. intros x Hx. rewrite (unsigned_lit x) by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

(* `andi rd,rs,7` of an address below 2^64. *)
Lemma srf_land7 : forall x, 0 <= x < 2 ^ 64 -> Z.land (bv_unsigned (Z_to_bv 64 x)) 7 = x mod 8.
Proof. intros x Hx. rewrite (unsigned_lit x) by lia. exact (land7 x). Qed.

Lemma srf_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. exact byte_range. Qed.

Lemma srf_zxb_u : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof. intros b0. exact (zxb_u b0). Qed.

(* `xori rd,rs,-1` of an address below 2^64: its bitwise not. *)
Lemma srf_xor1 : forall x, 0 <= x < 2 ^ 64 ->
  Z.lxor (bv_unsigned (Z_to_bv 64 x)) 18446744073709551615 = 18446744073709551615 - x.
Proof.
  intros x Hx. rewrite (unsigned_lit x) by lia.
  assert (E : Z.lxor x 18446744073709551615 = Z.land (Z.lnot x) (Z.ones 64)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
    change 18446744073709551615 with (Z.ones 64).
    destruct (Z.lt_ge_cases i 64) as [Hl|Hl].
    - rewrite Z.ones_spec_low by lia. destruct (Z.testbit x i); reflexivity.
    - rewrite Z.ones_spec_high by lia. rewrite (Z.bits_above_log2 x i); [reflexivity | lia |].
      destruct (Z.eq_dec x 0) as [->|Hn]; [cbn; lia|].
      apply Z.lt_le_trans with 64; [|lia]. apply Z.log2_lt_pow2; lia. }
  rewrite E, Z.land_ones by lia. pose proof (Z.add_lnot_diag x). Z.div_mod_to_equations. lia.
Qed.

(* Byte j of the model's frame (TWorld.zs frame) is the unsigned value of srf_fb frame j. *)
Lemma srf_byte_at : forall frame j, DS.byte_at (TW.zs frame) j = bv_unsigned (srf_fb frame j).
Proof.
  intros frame j. unfold DS.byte_at, TW.zs, srf_fb.
  rewrite <- (map_nth (@bv_unsigned 8) frame (Z_to_bv 8 0) (Z.to_nat j)). reflexivity.
Qed.

(* The body sum without the 16-bit wrap: the bytes b[p + i], ..., b[p + i + n - 1] added. *)
Fixpoint srf_rsum (bz : list Z) (p i : Z) (n : nat) : Z :=
  match n with O => 0 | S n' => DS.byte_at bz (p + i) + srf_rsum bz p (i + 1) n' end.

(* spec_sum's loop (spec.h:178, s = (s + p[i]) & 0xffff) is the plain sum, cut to 16 bits at the end. *)
Lemma srf_sum_loop : forall bz p n s i, 0 <= s < 65536 ->
  DS.spec_sum_loop bz p s i n = (s + srf_rsum bz p i n) mod 65536.
Proof.
  intros bz p n. induction n as [|n IH]; intros s i Hs; cbn [DS.spec_sum_loop srf_rsum].
  - rewrite Z.add_0_r. symmetry. apply Z.mod_small. exact Hs.
  - change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. change (2 ^ 16) with 65536.
    rewrite IH by (apply Z.mod_pos_bound; lia). rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

(* ---- the model's record ---- *)

(* The record the code fills: lib/Spec/DgnSpec.v spec_read_frame of the frame's bytes and len. *)
Definition srf_fm (frame : list byte) (len : Z) : DS.spec_frame := DS.spec_read_frame (TW.zs frame) len.

(* The model's record of an error code: the code, the ethertype and numbytes it read, every other field 0. *)
Definition srf_zero (code et nb : Z) : DS.spec_frame :=
  {| DS.sf_code := code; DS.sf_dst := 0; DS.sf_src := 0; DS.sf_ethertype := et; DS.sf_numbytes := nb;
     DS.sf_sum := 0; DS.sf_retry := 0; DS.sf_send := 0; DS.sf_ack := 0; DS.sf_cmd := 0; DS.sf_ncmds := 0;
     DS.sf_body := 0; DS.sf_body_len := 0; DS.sf_pad_len := 0; DS.sf_body_sum := 0 |}.

Lemma srf_fm_short : forall frame len, len < 30 -> srf_fm frame len = srf_zero (-2) 0 0.
Proof.
  intros frame len H. unfold srf_fm, DS.spec_read_frame, DS.SPEC_BODY_AT.
  rewrite (proj2 (Z.ltb_lt len 30) H). reflexivity.
Qed.

Lemma srf_fm_et : forall frame len, 30 <= len -> DS.spec_be16 (TW.zs frame) 12 <> 34911 ->
  srf_fm frame len = srf_zero (-3) (DS.spec_be16 (TW.zs frame) 12) 0.
Proof.
  intros frame len H E. unfold srf_fm, DS.spec_read_frame, DS.SPEC_BODY_AT, DS.SPEC_ETHERTYPE. cbv zeta.
  rewrite (proj2 (Z.ltb_ge len 30) H), (proj2 (Z.eqb_neq _ _) E). reflexivity.
Qed.

Lemma srf_fm_len : forall frame len, 30 <= len -> DS.spec_be16 (TW.zs frame) 12 = 34911 ->
  DS.spec_be16 (TW.zs frame) 14 < 16 \/ len - 14 < DS.spec_be16 (TW.zs frame) 14 ->
  srf_fm frame len = srf_zero (-4) (DS.spec_be16 (TW.zs frame) 12) (DS.spec_be16 (TW.zs frame) 14).
Proof.
  intros frame len H E HN. unfold srf_fm, DS.spec_read_frame, DS.SPEC_BODY_AT, DS.SPEC_ETHERTYPE,
    DS.SPEC_AT_NUMBYTES, DS.SPEC_HDR, DS.SPEC_ETH_HDR. cbv zeta.
  rewrite (proj2 (Z.ltb_ge len 30) H), E. cbn [Z.eqb Pos.eqb negb].
  replace ((DS.spec_be16 (TW.zs frame) 14 <? 16) || (len - 14 <? DS.spec_be16 (TW.zs frame) 14))%bool with true
    by (symmetry; apply orb_true_iff; destruct HN as [HN|HN]; [left | right]; apply Z.ltb_lt; exact HN).
  reflexivity.
Qed.

(* The SPEC_OK record. *)
Definition srf_okf (frame : list byte) (len : Z) : DS.spec_frame :=
  let zf := TW.zs frame in
  let nb := DS.spec_be16 zf 14 in
  {| DS.sf_code := 0; DS.sf_dst := 0; DS.sf_src := 6; DS.sf_ethertype := DS.spec_be16 zf 12;
     DS.sf_numbytes := nb; DS.sf_sum := DS.spec_be16 zf 16; DS.sf_retry := DS.spec_be16 zf 26;
     DS.sf_send := DS.spec_be32 zf 18; DS.sf_ack := DS.spec_be32 zf 22; DS.sf_cmd := DS.byte_at zf 28;
     DS.sf_ncmds := DS.byte_at zf 29; DS.sf_body := 30; DS.sf_body_len := nb - 16;
     DS.sf_pad_len := len - 30 - (nb - 16); DS.sf_body_sum := DS.spec_sum_at zf 30 (nb - 16) |}.

Lemma srf_fm_ok : forall frame len, 30 <= len -> DS.spec_be16 (TW.zs frame) 12 = 34911 ->
  16 <= DS.spec_be16 (TW.zs frame) 14 -> DS.spec_be16 (TW.zs frame) 14 <= len - 14 ->
  srf_fm frame len = srf_okf frame len.
Proof.
  intros frame len H E H1 H2. unfold srf_fm, srf_okf, DS.spec_read_frame, DS.SPEC_BODY_AT, DS.SPEC_ETHERTYPE,
    DS.SPEC_AT_NUMBYTES, DS.SPEC_HDR, DS.SPEC_ETH_HDR, DS.SPEC_OK, DS.SPEC_MAC, DS.SPEC_AT_SUM, DS.SPEC_AT_RETRY,
    DS.SPEC_AT_SEND, DS.SPEC_AT_ACK, DS.SPEC_AT_CMD, DS.SPEC_AT_NCMDS. cbv zeta.
  rewrite (proj2 (Z.ltb_ge len 30) H), E. cbn [Z.eqb Pos.eqb negb].
  replace ((DS.spec_be16 (TW.zs frame) 14 <? 16) || (len - 14 <? DS.spec_be16 (TW.zs frame) 14))%bool with false
    by (symmetry; apply orb_false_iff; split; apply Z.ltb_ge; lia).
  reflexivity.
Qed.

(* ---- the values the code computes ---- *)

(* A number shifted up by k, or-ed with one below 2^k, is their sum. *)
Lemma srf_lor_add : forall a c k, 0 <= a -> 0 <= k -> 0 <= c < 2 ^ k -> Z.lor (Z.shiftl a k) c = a * 2 ^ k + c.
Proof.
  intros a c k Ha Hk Hc.
  assert (D : Z.land (Z.shiftl a k) c = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i k) as [Hl|Hl].
    - rewrite Z.shiftl_spec_low by lia. reflexivity.
    - destruct (Z.eq_dec c 0) as [->|Hn]; [rewrite Z.bits_0; apply andb_false_r|].
      rewrite (Z.bits_above_log2 c i); [apply andb_false_r | lia |].
      apply Z.lt_le_trans with k; [apply Z.log2_lt_pow2; lia | lia]. }
  rewrite <- (Z.lxor_lor _ _ D), <- (Z.add_nocarry_lxor _ _ D).
  rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

(* An 8-aligned-up number a (a multiple of 2^k) or-ed with one below 2^k is their sum. *)
Lemma srf_lor_al : forall a c k, 0 <= a -> 0 <= k -> a mod 2 ^ k = 0 -> 0 <= c < 2 ^ k -> Z.lor a c = a + c.
Proof.
  intros a c k Ha Hk Hm Hc.
  assert (Pk : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (E : a = Z.shiftl (a / 2 ^ k) k)
    by (rewrite Z.shiftl_mul_pow2 by lia; pose proof (Z.div_mod a (2 ^ k) ltac:(lia)); lia).
  rewrite E, srf_lor_add; [ | apply Z.div_pos; lia | lia | lia].
  rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

(* spec.h:148-151 spec_be16: `b[j] << 8 | b[j + 1]`, as the code computes it from two `lbu`s. *)
Lemma srf_be16c : forall frame j j', j' = j + 1 ->
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb (srf_fb frame j))) 8)))
        (bv_unsigned (zxb (srf_fb frame j'))) = DS.spec_be16 (TW.zs frame) j.
Proof.
  intros frame j j' ->. unfold DS.spec_be16, DS.u16. rewrite !srf_zxb_u, !srf_byte_at.
  pose proof (srf_byte_range (srf_fb frame j)) as R1. pose proof (srf_byte_range (srf_fb frame (j + 1))) as R2.
  rewrite (unsigned_lit (Z.shiftl _ 8)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite srf_lor_add by lia. change (2 ^ 8) with 256. symmetry. apply Z.mod_small. lia.
Qed.

Lemma srf_be16_range : forall bz j, 0 <= DS.spec_be16 bz j < 65536.
Proof. intros bz j. unfold DS.spec_be16, DS.u16. apply Z.mod_pos_bound. lia. Qed.

(* The byte of a C1 cell `sb` stores from an `lbu` register (zxb unfolded). *)
Lemma srf_c1 : forall x : byte, Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned x))) = x.
Proof.
  intros x. rewrite (unsigned_lit (bv_unsigned x)) by (pose proof (srf_byte_range x); lia).
  apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* spec.h:153-156 spec_be32: `b[j] << 24 | b[j + 1] << 16 | b[j + 2] << 8 | b[j + 3]`, as the code computes it
   from four `lbu`s: (b[j + 1] << 16 | b[j] << 24) | (b[j + 2] << 8 | b[j + 3]). *)
Lemma srf_be32c : forall frame j j1 j2 j3, j1 = j + 1 -> j2 = j + 2 -> j3 = j + 3 ->
  Z.lor
    (bv_unsigned (Z_to_bv 64
       (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb (srf_fb frame j1))) 16)))
              (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb (srf_fb frame j))) 24))))))
    (bv_unsigned (Z_to_bv 64
       (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb (srf_fb frame j2))) 8)))
              (bv_unsigned (zxb (srf_fb frame j3))))))
  = DS.spec_be32 (TW.zs frame) j.
Proof.
  intros frame j j1 j2 j3 -> -> ->. unfold DS.spec_be32, DS.u32. rewrite !srf_zxb_u, !srf_byte_at.
  pose proof (srf_byte_range (srf_fb frame j)) as R0. pose proof (srf_byte_range (srf_fb frame (j + 1))) as R1.
  pose proof (srf_byte_range (srf_fb frame (j + 2))) as R2. pose proof (srf_byte_range (srf_fb frame (j + 3))) as R3.
  set (x0 := bv_unsigned (srf_fb frame j)) in *. set (x1 := bv_unsigned (srf_fb frame (j + 1))) in *.
  set (x2 := bv_unsigned (srf_fb frame (j + 2))) in *. set (x3 := bv_unsigned (srf_fb frame (j + 3))) in *.
  clearbody x0 x1 x2 x3.
  rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256 in *. change (2 ^ 16) with 65536 in *.
  change (2 ^ 24) with 16777216 in *. change (2 ^ 32) with 4294967296 in *.
  rewrite (unsigned_lit (x1 * 65536)), (unsigned_lit (x0 * 16777216)), (unsigned_lit (x2 * 256)) by lia.
  rewrite (Z.mod_small (x0 * 16777216)), (Z.mod_small (x1 * 65536)), (Z.mod_small (x2 * 256)) by lia.
  rewrite (Z.lor_comm (x1 * 65536) (x0 * 16777216)).
  rewrite (srf_lor_al (x0 * 16777216) (x1 * 65536) 24) by (change (2 ^ 24) with 16777216; Z.div_mod_to_equations; lia).
  rewrite (srf_lor_al (x2 * 256) x3 8) by (change (2 ^ 8) with 256; Z.div_mod_to_equations; lia).
  rewrite (unsigned_lit (x0 * 16777216 + x1 * 65536)), (unsigned_lit (x2 * 256 + x3)) by lia.
  rewrite (srf_lor_al (x0 * 16777216 + x1 * 65536) (x2 * 256 + x3) 16)
    by (change (2 ^ 16) with 65536; Z.div_mod_to_equations; lia).
  rewrite (srf_lor_al (x1 * 65536) (x2 * 256 + x3) 16) by (change (2 ^ 16) with 65536; Z.div_mod_to_equations; lia).
  rewrite (srf_lor_al (x0 * 16777216) (x1 * 65536 + (x2 * 256 + x3)) 24)
    by (change (2 ^ 24) with 16777216; Z.div_mod_to_equations; lia).
  lia.
Qed.
Lemma srf_put1 : forall x : byte, TW.put 1 (bv_unsigned x) = [x].
Proof.
  intros x. unfold TW.put. cbn [Z_to_le_bytes]. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* The 80 bytes of the cells of an error record against TContract.sf_bytes of that record. *)
Ltac srf_bytes :=
  unfold TCt.sf_bytes, TCt.sf_ptr, srf_zero;
  cbn [cells_bytes cbytes DS.sf_code DS.sf_dst DS.sf_src DS.sf_ethertype DS.sf_numbytes DS.sf_sum DS.sf_retry
       DS.sf_send DS.sf_ack DS.sf_cmd DS.sf_ncmds DS.sf_body DS.sf_body_len DS.sf_pad_len DS.sf_body_sum
       Z.eqb Pos.eqb];
  rewrite ?TWorldLemmas.le8_put, ?TWorldLemmas.le4_put, ?TWorldLemmas.le2_put;
  reflexivity.

(* The 80 bytes of the cells the SPEC_OK path leaves are TContract.sf_bytes of the SPEC_OK record. *)
Lemma srf_ok_bytes : forall frame b len,
  cells_bytes (srf_cells 0 b (b + 6) (DS.spec_be16 (TW.zs frame) 12) (DS.spec_be16 (TW.zs frame) 14)
                 (DS.spec_be16 (TW.zs frame) 16) (DS.spec_be16 (TW.zs frame) 26)
                 (DS.spec_be32 (TW.zs frame) 18) (DS.spec_be32 (TW.zs frame) 22) (srf_fb frame 28) (srf_fb frame 29)
                 (b + 30) (DS.spec_be16 (TW.zs frame) 14 - 16) (len - 30 - (DS.spec_be16 (TW.zs frame) 14 - 16))
                 (srf_rsum (TW.zs frame) 30 0 (Z.to_nat (DS.spec_be16 (TW.zs frame) 14 - 16))))
  = TCt.sf_bytes b (srf_okf frame len).
Proof.
  intros frame b len. unfold srf_cells, TCt.sf_bytes, TCt.sf_ptr, srf_okf. cbv zeta.
  cbn [cells_bytes cbytes DS.sf_code DS.sf_dst DS.sf_src DS.sf_ethertype DS.sf_numbytes DS.sf_sum DS.sf_retry
       DS.sf_send DS.sf_ack DS.sf_cmd DS.sf_ncmds DS.sf_body DS.sf_body_len DS.sf_pad_len DS.sf_body_sum
       Z.eqb Pos.eqb].
  rewrite ?TWorldLemmas.le8_put, ?TWorldLemmas.le4_put, ?TWorldLemmas.le2_put.
  rewrite !srf_byte_at, !srf_put1, Z.add_0_r.
  unfold DS.spec_sum_at, DS.u16. rewrite srf_sum_loop by lia. rewrite Z.add_0_l, Z.mod_mod by lia.
  set (SM := srf_rsum (TW.zs frame) 30 0 (Z.to_nat (DS.spec_be16 (TW.zs frame) 14 - 16))).
  replace (TW.put 2 (SM mod 65536)) with (TW.put 2 SM)
    by (unfold TW.put; change 65536 with (2 ^ 16); symmetry; apply Z_to_le_bytes_mod; lia).
  reflexivity.
Qed.

(* The compares of the branches, on any two words given as Z_to_bv 64 of a number. *)
Lemma srf_ltu_w : forall x y, bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x mod 2 ^ 64 <? y mod 2 ^ 64).
Proof. intros x y. unfold bv_ltu. rewrite !unsigned_lit_wrap. reflexivity. Qed.
Lemma srf_eqb_w : forall x y, bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x mod 2 ^ 64 =? y mod 2 ^ 64).
Proof. intros x y. unfold bv_eqb. rewrite !unsigned_lit_wrap. reflexivity. Qed.

(* A branch condition as a Z compare: the two compares above, then each `x mod 2 ^ 64` computed (a literal) or
   dropped (a number in range, by lia). *)
Ltac srf_cond :=
  rewrite ?srf_ltu_w, ?srf_eqb_w;
  repeat match goal with
  | |- context [?x mod 2 ^ 64] =>
      tryif is_Zlit x then (let v := eval vm_compute in (x mod 2 ^ 64) in change (x mod 2 ^ 64) with v)
      else rewrite (Z.mod_small x (2 ^ 64)) by (Z.div_mod_to_equations; lia)
  end.

(* A branch whose condition lia decides from the context. *)
Ltac srf_br v :=
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with v; [cbv iota | symmetry; srf_cond; solve_cond_rec]
  end.

(* Every `x >> 3` and `x & 7` of an address in the goal, as x / 8 and x mod 8. *)
Ltac srf_shr :=
  repeat match goal with
  | |- context [Z.shiftr (bv_unsigned (Z_to_bv 64 ?x)) 3] => rewrite (srf_shr3 x) by (Z.div_mod_to_equations; lia)
  | |- context [Z.land (bv_unsigned (Z_to_bv 64 ?x)) 7] => rewrite (srf_land7 x) by (Z.div_mod_to_equations; lia)
  end.

(* The bundle, opened under fixed names, with the shadow base as a numeral and the range of sp. *)
Ltac srf_open CX :=
  lazymatch type of CX with srf_cx _ _ ?sp _ _ _ _ _ _ _ _ _ _ =>
    let H := fresh in pose proof CX as H;
    destruct H as ((B0 & L0 & LF & BLEN & P0 & P8 & PL & S48) & (FOUT & FSOUT & PSOUT & SPOUT) &
                   (FR0 & SHF0 & SHP0 & FRM0) & (RFR & RFP & RFB & RSP & RSF));
    unfold ASAN_K in *;
    pose proof (u64_range sp) as Rsp
  end.

(* srf_rd1 with the read fact first, so the address is known when the side conditions are elaborated. *)
Lemma srf_rd1' : forall m0 m fp a x, munch [(fp, fp + 80)] m0 m -> mrd rsegs m0 (wa a) = Some x ->
  0 <= a < 2 ^ 64 -> (a < fp \/ fp + 80 <= a) -> ov_read_bytes rsegs m (wa a) 1 = Some [x].
Proof. intros m0 m fp a x MU H Ha Hd. exact (srf_rd1 m0 m fp a x MU Ha Hd H). Qed.

(* The shadow byte k of frame byte j, read at the current memory, with its footprint (SHF, FSOUT, RSF: the bundle's
   frame-shadow facts; MU: the current memory's munch from m0). *)
Ltac srf_shf j SHF FSOUT RSF MU k SK :=
  let MK := fresh "MK" in let R := fresh "RSH" in let RS := fresh "RGS" in
  destruct (SHF j ltac:(lia)) as (k & MK & SK);
  pose proof (srf_rd1' _ _ _ _ _ MU MK ltac:(Z.div_mod_to_equations; lia) (FSOUT j ltac:(lia))) as R;
  pose proof (RSF j ltac:(lia)) as RS; clear MK; rewrite ?Z.add_assoc in R, RS, SK.

(* Frame byte j, read at the current memory (FR, FOUT: the bundle's frame facts). *)
Ltac srf_ldf j FR FOUT MU :=
  let R := fresh "RFB" in
  pose proof (srf_rd1' _ _ _ _ _ MU (FR j ltac:(lia)) ltac:(lia) (FOUT j ltac:(lia))) as R;
  rewrite ?Z.add_assoc in R.

(* The shadow byte (0) of struct byte o, read at the current memory, with its footprint. *)
Ltac srf_shp o SHP PSOUT RSP MU :=
  let R := fresh "RSP" in let RS := fresh "RGP" in
  pose proof (srf_rd1' _ _ _ _ _ MU (SHP o ltac:(lia)) ltac:(Z.div_mod_to_equations; lia) (PSOUT o ltac:(lia))) as R;
  pose proof (RSP o ltac:(lia)) as RS; rewrite ?Z.add_0_r in R, RS.

(* The read facts of the step just taken, their footprint, and the slow-path fact of a frame check: that fact
   (`bv_signed k = 0 \/ ...`) is a disjunction, and a lia of the kit that falls back to its unpruned branch case-splits
   on every one left in the context. *)
Ltac srf_clear := repeat match goal with
  | H : ov_read_bytes _ _ _ _ = Some _ |- _ => clear H
  | H : ExecF.rng _ (_ / 8 + _) 1 |- _ => clear H
  | H : bv_signed _ = 0 \/ _ |- _ => clear H
  end.

(* A check of a frame byte joins its fast path (the shadow byte is 0) and its slow path (the byte's offset in its
   granule is below the shadow byte) at the instruction after the `bne`; the slow path writes one register r (its
   `andi r, x, 7`). srf_join r, at the `bne`, leaves two goals: the check, with the hypothesis K (the walk from the
   join, for any value of r), and that walk. *)
Ltac srf_join r K :=
  lazymatch goal with
  | |- ExecF.evtF ?sg ?RNG ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
      let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
      let P := eval vm_compute in (pc + 4) in
      enough (K : forall v : word, ExecF.evtF sg RNG Q (MS (tset p v R) F (Z_to_bv 64 P) fc rv m ro));
      [ cbv beta iota delta [tset] in K | intros ?; map_cbv_set ]
  end.

(* The check itself: the `bne` on sxb k; at k = 0 the join; else the slow path `andi; blt` back to the join, taken
   since the byte's offset is below k (SK). *)
Ltac srf_chk K k SK :=
  step; rewrite ?sxb_eq0;
  let Z0 := fresh "Z0" in
  destruct (Z.eqb_spec (bv_signed k) 0) as [Z0|Z0]; cbn [negb]; cbv iota;
  [ apply K
  | step; srf_shr; step;
    lazymatch goal with
    | |- ExecF.evtF _ _ _ (MS _ _ (if bv_lts (Z_to_bv 64 ?x) (sxb k) then _ else _) _ _ _ _) =>
        rewrite (lts_low x k) by (Z.div_mod_to_equations; lia);
        replace (x <? bv_signed k) with true by (symmetry; apply Z.ltb_lt; destruct SK as [SK|SK]; [contradiction | exact SK]);
        cbv iota; apply K
    end ].
