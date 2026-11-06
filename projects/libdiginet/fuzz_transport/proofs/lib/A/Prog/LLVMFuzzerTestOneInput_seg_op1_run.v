(* LLVMFuzzerTestOneInput_seg_op1_run: the machine run of segment OP1 of the image-A walk of fuzz_transport.asan's
   LLVMFuzzerTestOneInput (lib/A/Prog/LLVMFuzzerTestOneInput_segs.v lc_op1_stmt, +0x5e8 .. +0x1118: op 1, the inlined
   op_frame of fuzz_transport.c), as footprint runs of lib/Lib/ExecF.v (StepF's step) over the registers and memory
   facts the segment reads. No byte is written.

   The code reads op_frame's eight bytes after the op byte (sel; send lo, hi; ack lo, hi; r; w lo, hi) unrolled per
   cursor length, each by a checked 1-byte load (`srli`, `add` of the shadow base, `lb`, `bnez`, the handler's
   `andi 7` / `blt` back to the load when the granule is partial; op1_chk), then (op1_tail, op1_tables) w % 1485 by a
   multiply with 0x610f (checked over all 65536 values of w), the take's n = min (w % 1485, bytes left), the
   checked 8-byte loads of op_frame.DST[sel >> 5 & 3] and op_frame.SRC[sel >> 3 & 3] (zero-shadow granules) and
   the checked byte load of op_frame.CMD[(sel & 7) % 7] (its granule's shadow byte is 7: the handler's `blt`
   returns to the load). The lemmas, from the call back to the arm:
     op1_tables  +0x1084 .. +0x1118  the three table loads, a2 = send, s3 / s7 the cursor after the take;
     op1_tail    +0x1040 ..          w, its remainder by 1485, the min with the bytes left;
     op1_j8 .. op1_j6, op1_retry, op1_end0   w's high and low byte, the retry byte (+0x1034, +0xd14, +0xcc0, +0xcb0)
                 or none of them (+0xcf0);
     op1_c9c     +0xc9c              sel's sign extension, `bltz` on bit 7: ack = g_last_counter (`lw` at
                                     g_last_counter's address 0x5df140, its page from the spill slot at s1 + 48)
                                     or ack = hi << 8 | lo;
     op1_j5 .. op1_j1               ack's and send's bytes and sel (+0x1318, +0x1134, +0xc7c, +0x920, +0x5fc);
     op1_run     +0x5e8              `beqz s7` (no byte after the op byte: every value 0) or the check of sel.
   The values are the plain walk's (lib/Prog/T/LLVMFuzzerTestOneInput_op1.v op1_g: byte j after the op byte, 0 past
   the cursor's end); op1_post is the state at the call. The report stubs the slow paths could reach (0x8276c,
   0x82c08, 0x82c10, 0x82c9c, 0x82cbc, 0x82cd8, 0x82cec, 0x82d00, 0x82d04, 0x82d28, 0x82d38) are never stepped:
   each `bnez` / `blt` before one is decided by the shadow byte of the access it guards. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import AsanKA AsanKAProof TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require LLVMFuzzerTestOneInput_op1.
Import ListNotations.
Open Scope Z_scope.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module POP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.LLVMFuzzerTestOneInput_op1.
Module LS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.LLVMFuzzerTestOneInput_segs.

(* ---- the computations the code does on a byte or a 16-bit value, checked over every value ---- *)

Lemma op1_byte_all : forall (Pb : Z -> bool), forallb Pb (map Z.of_nat (seq 0 256)) = true ->
  forall x, 0 <= x < 256 -> Pb x = true.
Proof.
  intros Pb H x Hx. rewrite forallb_forall in H. apply H.
  apply in_map_iff. exists (Z.to_nat x). split; [lia|]. apply in_seq. lia.
Qed.

Lemma op1_w_all : forall (Pb : Z -> bool),
  forallb (fun h => forallb (fun l => Pb (h * 256 + l)) (map Z.of_nat (seq 0 256))) (map Z.of_nat (seq 0 256)) = true ->
  forall x, 0 <= x < 65536 -> Pb x = true.
Proof.
  intros Pb H x Hx.
  assert (Ex : x = x / 256 * 256 + x mod 256) by (rewrite (Z.div_mod x 256) at 1 by lia; ring).
  pose proof (op1_byte_all (fun h => forallb (fun l => Pb (h * 256 + l)) (map Z.of_nat (seq 0 256))) H (x / 256)
    ltac:(split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia)) as H1.
  cbv beta in H1. rewrite Ex. exact (op1_byte_all (fun l => Pb (x / 256 * 256 + l)) H1 (x mod 256)
    ltac:(apply Z.mod_pos_bound; lia)).
Qed.

(* hi << 8 | lo of two bytes, as the code builds it. *)
Lemma op1_w16 : forall h l, 0 <= h < 256 -> 0 <= l < 256 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 h)) 8))) (bv_unsigned (Z_to_bv 64 l)))
  = Z_to_bv 64 (h * 256 + l).
Proof.
  intros h l Hh Hl. rewrite (unsigned_lit h) by lia. rewrite (unsigned_lit l) by lia.
  rewrite (unsigned_lit (Z.shiftl h 8)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite Z.lor_comm, lor_shiftl8_add by lia. f_equal. lia.
Qed.

(* A closed boolean test over every byte value, as a fact about x. *)
Ltac op1_bytes x Hx :=
  lazymatch goal with |- ?l = ?r =>
    apply Z.eqb_eq;
    let bexp := constr:(Z.eqb l r) in
    let f := eval pattern x in bexp in
    lazymatch f with ?g x => exact (op1_byte_all g ltac:(vm_compute; reflexivity) x Hx) end
  end.

Ltac brF b := lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b by (vm_compute; reflexivity); cbv iota
  end.

Section Run.
Variables (RNG : ExecF.footprint) (ra sp gp tp s0 s1 s2 s4 s5 s6 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (P O N : Z).
Local Notation ST pc x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x24 :=
  (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 x19 s4 s5 s6 x23 x24
           (Z_to_bv 64 (P + O)) (Z_to_bv 64 2147450880) (Z_to_bv 64 N) t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Hypothesis M96 : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned s1 + 96)) 8 = Some (le8 (Z_to_bv 64 0x610f)).
Hypothesis M136 : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned s1 + 136)) 8 = Some (le8 (Z_to_bv 64 0xffff)).
Hypothesis R96 : rng RNG (bv_unsigned s1 + 96) 8.
Hypothesis R136 : rng RNG (bv_unsigned s1 + 136) 8.
Hypothesis MDST : forall i, 0 <= i < 4 -> ov_read_bytes rsegs m (Z_to_bv 64 (671264 + 8 * i)) 8 =
  Some (le8 (Z_to_bv 64 (nth (Z.to_nat i) [TRANS_HOST; TRANS_SPEC_BCAST; TRANS_OTHER; TRANS_HOST] 0))).
Hypothesis MSRC : forall i, 0 <= i < 4 -> ov_read_bytes rsegs m (Z_to_bv 64 (671200 + 8 * i)) 8 =
  Some (le8 (Z_to_bv 64 (nth (Z.to_nat i) [TRANS_DESK; TRANS_DESK2; TRANS_HOST; TRANS_NOTDD] 0))).
Hypothesis MCMD : forall i, 0 <= i < 7 -> ov_read_bytes rsegs m (Z_to_bv 64 (135424 + i)) 1 =
  Some [Z_to_bv 8 (nth (Z.to_nat i) TOP.op_frame_CMD 0)].
Hypothesis SDST : forall i, 0 <= i < 4 -> mrd rsegs m (wa ((671264 + 8 * i) / 8 + 2147450880)) = Some (Z_to_bv 8 0).
Hypothesis SSRC : forall i, 0 <= i < 4 -> mrd rsegs m (wa ((671200 + 8 * i) / 8 + 2147450880)) = Some (Z_to_bv 8 0).
Hypothesis SCMD : forall i, 0 <= i < 7 -> mrd rsegs m (wa ((135424 + i) / 8 + 2147450880)) = Some (Z_to_bv 8 7).
Hypothesis RDST : rng RNG 671264 32.
Hypothesis RSRC : rng RNG 671200 32.
Hypothesis RCMD : rng RNG 135424 7.
Hypothesis RSDST : forall i, 0 <= i < 4 -> rng RNG ((671264 + 8 * i) / 8 + 2147450880) 1.
Hypothesis RSSRC : forall i, 0 <= i < 4 -> rng RNG ((671200 + 8 * i) / 8 + 2147450880) 1.
Hypothesis RSCMD : forall i, 0 <= i < 7 -> rng RNG ((135424 + i) / 8 + 2147450880) 1.

(* +0x1084 .. the call at +0x1118: a0 = op_frame.DST[sel >> 5 & 3] (the checked 8-byte load), a1 =
   op_frame.SRC[sel >> 3 & 3] (the same), a5 = op_frame.CMD[(sel & 7) % 7] (the checked byte load: the granule's
   shadow byte is 7, the slow path's `blt` goes back to the load), a2 = t0 | a6, s3 = s8 + a7, s7 = t1 - a7,
   a6 = s8. *)
Lemma op1_tables : forall (Q : machine_state -> Prop) t0 t2 a0 a1 a2 a3 a4 a5 a6 s3 s7 (R S8 sel len : Z),
  0 <= R < 2 ^ 32 -> 0 <= len <= R -> 0 <= S8 -> S8 + R < 2 ^ 63 -> 0 <= sel < 256 ->
  Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned a1) 2))) 24 = 8 * Z.land (Z.shiftr sel 5) 3 ->
  Z.land (bv_unsigned a1) 255 = sel ->
  (forall t2' : word,
     Q (ST 0x8237c t0 (Z_to_bv 64 R) t2' (Z_to_bv 64 (LS.lc_fdst_a sel)) (Z_to_bv 64 (LS.lc_fsrc_a sel))
           (Z_to_bv 64 (Z.lor (bv_unsigned t0) (bv_unsigned a6))) a3 a4 (Z_to_bv 64 (LS.lc_fcmd sel))
           (Z_to_bv 64 S8) (Z_to_bv 64 len) (Z_to_bv 64 (S8 + len)) (Z_to_bv 64 (R - len)) (Z_to_bv 64 S8))) ->
  ExecF.evtF rsegs RNG Q
    (ST 0x822e8 t0 (Z_to_bv 64 R) t2 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 len) s3 s7 (Z_to_bv 64 S8)).
Proof.
  intros Q t0 t2 a0 a1 a2 a3 a4 a5 a6 s3 s7 R S8 sel len HR Hlen HS0 HS1 Hsel HA1 HA2 HK.
  set (di := Z.land (Z.shiftr sel 5) 3) in *.
  assert (Hdi : 0 <= di < 4) by (unfold di; change 3 with (Z.ones 2); rewrite Z.land_ones by lia;
                                 apply Z.mod_pos_bound; lia).
  (* 0x822e8 srli a0, a1, 2; auipc; andi a0, a0, 24; addi (DST); add a0, a2, a0 *)
  do 4 step. rewrite HA1. step.
  (* the check of the 8-byte load at DST + 8 di: the shadow byte is 0 *)
  pose proof (SDST di Hdi) as MS0. pose proof (RSDST di Hdi) as RS0.
  step. gen_shr (Z_to_bv 64 (671264 + 8 * di)) g G. rewrite (unsigned_lit (671264 + 8 * di)) in G by lia.
  step. gen_addi g h H.
  pose proof (rdw0 m h _ _ MS0 ltac:(rewrite H, G; reflexivity)) as RR. step. clear RR.
  step. brF false.
  (* 0x8230c zext.b a2, a1 *)
  step. rewrite HA2.
  (* 0x82310 auipc a1; andi a5, a2, 24; addi (SRC); add a1, a1, a5 *)
  do 4 step. rewrite (unsigned_lit sel) by lia.
  set (dj := Z.land (Z.shiftr sel 3) 3) in *.
  assert (Hdj : 0 <= dj < 4) by (unfold dj; change 3 with (Z.ones 2); rewrite Z.land_ones by lia;
                                 apply Z.mod_pos_bound; lia).
  replace (Z.land sel 24) with (8 * dj) by (unfold dj; op1_bytes sel Hsel).
  (* the check of the 8-byte load at SRC + 8 dj *)
  pose proof (SSRC dj Hdj) as MS1. pose proof (RSSRC dj Hdj) as RS1.
  step. gen_shr (Z_to_bv 64 (671200 + 8 * dj)) g1 G1. rewrite (unsigned_lit (671200 + 8 * dj)) in G1 by lia.
  step. gen_addi g1 h1 H1.
  pose proof (rdw0 m h1 _ _ MS1 ltac:(rewrite H1, G1; reflexivity)) as RR. step. clear RR.
  step. brF false.
  (* 0x82330 ld a0, 0(a0): DST[di] *)
  pose proof (MDST di Hdi) as RD. step. clear RD.
  do 7 step.
  set (dk := Z.land sel 7 mod 7).
  assert (Hdk : 0 <= dk < 7) by (unfold dk; apply Z.mod_pos_bound; lia).
  let w := getreg 12 in replace w with (Z_to_bv 64 dk) by (f_equal; unfold dk; op1_bytes sel Hsel).
  (* 0x82350 add a2, a5, a2 (CMD + dk); the check of the byte load there: the granule's shadow byte is 7 *)
  pose proof (SCMD dk Hdk) as MS2. pose proof (RSCMD dk Hdk) as RS2.
  step. step. gen_shr (Z_to_bv 64 (135424 + dk)) g2 G2. rewrite (unsigned_lit (135424 + dk)) in G2 by lia.
  step. gen_addi g2 h2 H2.
  pose proof (rdw0 m h2 _ _ MS2 ltac:(rewrite H2, G2; reflexivity)) as RR. step. clear RR.
  (* 0x82360 ld a1, 0(a1): SRC[dj] *)
  pose proof (MSRC dj Hdj) as RD. step. clear RD.
  (* 0x82364 bnez a5 (taken: 7); 0x8259c andi t2, a2, 7; 0x825a0 blt t2, a5 (taken: dk < 7) *)
  step. brF true.
  step. rewrite land7, (unsigned_lit (135424 + dk)) by lia.
  replace ((135424 + dk) mod 8) with dk
    by (replace (135424 + dk) with (dk + 16928 * 8) by lia; rewrite Z.mod_add by lia; symmetry; apply Z.mod_small; lia).
  step. rewrite (lts_low dk (Z_to_bv 8 7)) by lia.
  replace (dk <? bv_signed (Z_to_bv 8 7)) with true by (symmetry; apply Z.ltb_lt; change (bv_signed (Z_to_bv 8 7)) with 7; lia).
  cbv iota.
  (* 0x82368 lbu a5, 0(a2): CMD[dk]; or a2, t0, a6; add s3, s8, a7; sub s7, t1, a7; mv a6, s8 *)
  pose proof (MCMD dk Hdk) as RD. step. clear RD.
  do 4 step.
  apply evtF_done.
  rewrite (unsigned_lit R), (unsigned_lit len) by lia.
  assert (Hc : 0 <= nth (Z.to_nat dk) TOP.op_frame_CMD 0 < 256)
    by (assert (C : dk = 0 \/ dk = 1 \/ dk = 2 \/ dk = 3 \/ dk = 4 \/ dk = 5 \/ dk = 6) by lia;
        destruct C as [C|[C|[C|[C|[C|[C|C]]]]]]; rewrite C; unfold TOP.op_frame_CMD; simpl; lia).
  replace (zxb (Z_to_bv 8 (nth (Z.to_nat dk) TOP.op_frame_CMD 0))) with (Z_to_bv 64 (LS.lc_fcmd sel))
    by (unfold zxb; f_equal; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
        change (2 ^ Z.of_N 8) with 256; rewrite Z.mod_small by lia; reflexivity).
  exact (HK (Z_to_bv 64 dk)).
Qed.

(* +0x1040 .. the call at +0x1118: w = hi << 8 | lo, the take's n = min (w mod 1485, R), the checked loads of
   op_frame.DST / SRC and the checked byte load of op_frame.CMD, a2 = t0 | a6, s3 / s7 the cursor after the take. *)
Lemma op1_tail : forall (Q : machine_state -> Prop) t0 t2 a0 a1 a3 a4 a6 a7 s3 s7 (whi wlo R S8 sel : Z),
  0 <= whi < 256 -> 0 <= wlo < 256 -> 0 <= R < 2 ^ 32 -> 0 <= S8 -> S8 + R < 2 ^ 63 -> 0 <= sel < 256 ->
  Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned a1) 2))) 24 = 8 * Z.land (Z.shiftr sel 5) 3 ->
  Z.land (bv_unsigned a1) 255 = sel ->
  (forall t2' : word,
     Q (ST 0x8237c t0 (Z_to_bv 64 R) t2' (Z_to_bv 64 (LS.lc_fdst_a sel)) (Z_to_bv 64 (LS.lc_fsrc_a sel))
           (Z_to_bv 64 (Z.lor (bv_unsigned t0) (bv_unsigned a6))) a3 a4 (Z_to_bv 64 (LS.lc_fcmd sel))
           (Z_to_bv 64 S8) (Z_to_bv 64 (Z.min ((whi * 256 + wlo) mod 1485) R))
           (Z_to_bv 64 (S8 + Z.min ((whi * 256 + wlo) mod 1485) R))
           (Z_to_bv 64 (R - Z.min ((whi * 256 + wlo) mod 1485) R)) (Z_to_bv 64 S8))) ->
  ExecF.evtF rsegs RNG Q
    (ST 0x822a4 t0 (Z_to_bv 64 R) t2 a0 a1 (Z_to_bv 64 wlo) a3 a4 (Z_to_bv 64 whi) a6 a7 s3 s7 (Z_to_bv 64 S8)).
Proof.
  intros Q t0 t2 a0 a1 a3 a4 a6 a7 s3 s7 whi wlo R S8 sel Hhi Hlo HR HS0 HS1 Hsel HA1 HA2 HK.
  (* 0x822a4 slli a5, a5, 8; 0x822a8 or a2, a5, a2 (w) *)
  do 2 step.
  rewrite (op1_w16 whi wlo Hhi Hlo).
  assert (Hw : 0 <= whi * 256 + wlo < 65536) by lia.
  remember (whi * 256 + wlo) as w eqn:Ew.
  pose proof (Z.mod_pos_bound w 1485 ltac:(lia)) as Hwm.
  (* 0x822ac .. 0x822dc: w mod 1485 by the multiply with 0x610f, masked with 0xffff; 0x822e0 bltu a7, t1 *)
  do 14 step.
  lazymatch goal with |- context [bv_ltu (Z_to_bv 64 ?e) _] =>
    let f := eval pattern w in e in
    lazymatch f with ?g w =>
      assert (EW : e = w mod 1485)
        by (apply Z.eqb_eq; exact (op1_w_all (fun x => g x =? x mod 1485) ltac:(vm_compute; reflexivity) w Hw))
    end;
    rewrite EW
  end.
  if_cases K; zify_cond K.
  - (* w mod 1485 < R: a7 = w mod 1485 *)
    rewrite Z.min_l in HK by lia.
    apply (op1_tables Q t0 t2 _ a1 _ a3 a4 _ a6 s3 s7 R S8 sel (w mod 1485)); [lia | lia | lia | lia | lia | exact HA1
      | exact HA2 | exact HK].
  - (* R <= w mod 1485: 0x822e4 mv a7, t1 *)
    rewrite Z.min_r in HK by lia.
    step.
    apply (op1_tables Q t0 t2 _ a1 _ a3 a4 _ a6 s3 s7 R S8 sel R); [lia | lia | lia | lia | lia | exact HA1
      | exact HA2 | exact HK].
Qed.

Variables (D Bw : list byte).
Hypothesis HN : 1 <= N.
Hypothesis HN26 : N < 2 ^ 26.
Hypothesis HO : 0 <= O.
Hypothesis HP : 0 <= P.
Hypothesis HPN : P + O + N < 2 ^ 62.
Hypothesis HRB : forall k, 0 <= k < N ->
  ov_read_bytes rsegs m (Z_to_bv 64 (P + O + k)) 1 = Some [nth (Z.to_nat (O + k)) D (Z_to_bv 8 0)].
Hypothesis HSH : forall k, 0 <= k < N -> exists sk : byte,
  mrd rsegs m (wa ((P + O + k) / 8 + 2147450880)) = Some sk /\ (bv_signed sk = 0 \/ (P + O + k) mod 8 < bv_signed sk).
Hypothesis HRD : forall k, 0 <= k < N -> rng RNG (P + O + k) 1.
Hypothesis HRS : forall k, 0 <= k < N -> rng RNG ((P + O + k) / 8 + 2147450880) 1.
Hypothesis M48 : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned s1 + 48)) 8 = Some (le8 (Z_to_bv 64 0x5df568)).
Hypothesis R48 : rng RNG (bv_unsigned s1 + 48) 8.
Hypothesis MLC : ov_read_bytes rsegs m (Z_to_bv 64 0x5df140) 4 = Some (TW.sub Bw TW.OFF_g_last_counter 4).
Hypothesis RLC : rng RNG 0x5df140 4.

(* ---- op_frame's values, as the bytes after the op byte give them (the plain walk's op1_g: byte j after the op
   byte, 0 past the cursor's end) ---- *)
Definition og (j : Z) : Z := POP.op1_g D (TOP.FuzzIn (O + 1) (N - 1)) j.
Definition r_send : Z := Z.lor (og 1) (Z.shiftl (og 2) 8).
Definition r_ack : Z := if Z.land (og 0) 128 =? 0 then Z.lor (og 3) (Z.shiftl (og 4) 8) else TW.g_last_counter Bw.
Definition r_retry : Z := Z.land (og 5) 3.
Definition r_w : Z := Z.lor (og 6) (Z.shiftl (og 7) 8).
Definition r_nr : Z := N - 1 - Z.min 8 (N - 1).
Definition r_S5 : Z := P + O + 1 + Z.min 8 (N - 1).
Definition r_len : Z := Z.min (r_w mod 1485) r_nr.

(* The state at the call of build_and_receive (+0x1118). *)
Definition op1_post (ms : machine_state) : Prop :=
  exists (t0' t1' t2' a2' a3' s8' : word),
    ms = ST 0x8237c t0' t1' t2' (Z_to_bv 64 (LS.lc_fdst_a (og 0))) (Z_to_bv 64 (LS.lc_fsrc_a (og 0))) a2' a3'
            (Z_to_bv 64 r_retry) (Z_to_bv 64 (LS.lc_fcmd (og 0))) (Z_to_bv 64 r_S5) (Z_to_bv 64 r_len)
            (Z_to_bv 64 (r_S5 + r_len)) (Z_to_bv 64 (r_nr - r_len)) s8' /\
    bv_unsigned a2' = r_send /\ bv_unsigned a3' mod 2 ^ 32 = r_ack.

Lemma og_range : forall j, 0 <= og j < 256.
Proof. intros j. apply POP.op1_g_range. Qed.

Lemma og_zero : forall j, N <= j + 1 -> og j = 0.
Proof.
  intros j Hj. unfold og, POP.op1_g. cbn [TOP.fi_n TOP.fi_off].
  rewrite (proj2 (Z.ltb_ge j (N - 1))) by lia. reflexivity.
Qed.

Lemma og_byte : forall k j, 1 <= k < N -> j = k - 1 ->
  zxb (nth (Z.to_nat (O + k)) D (Z_to_bv 8 0)) = Z_to_bv 64 (og j).
Proof.
  intros k j Hk ->. unfold og, POP.op1_g. cbn [TOP.fi_n TOP.fi_off].
  rewrite (proj2 (Z.ltb_lt (k - 1) (N - 1))) by lia.
  unfold zxb. do 2 f_equal. f_equal. lia.
Qed.

Lemma r_send_range : 0 <= r_send < 65536.
Proof.
  unfold r_send. pose proof (og_range 1). pose proof (og_range 2).
  rewrite lor_shiftl8_add by lia. lia.
Qed.

(* the sign extension of sel (`slli a1, a1, 56; srai a1, a1, 56`) and what the tail reads off it *)
Lemma op1_sx_lts : forall sel, 0 <= sel < 256 ->
  bv_lts (Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 sel)) 56))) 56))
    (Z_to_bv 64 0) = negb (Z.land sel 128 =? 0).
Proof.
  intros sel Hsel. apply Bool.eqb_prop.
  let f := eval pattern sel in
    (Bool.eqb (bv_lts (Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 sel)) 56))) 56))
                (Z_to_bv 64 0)) (negb (Z.land sel 128 =? 0))) in
  lazymatch f with ?g sel => exact (op1_byte_all g ltac:(vm_compute; reflexivity) sel Hsel) end.
Qed.

Definition op1_sel_ok (a1 : word) (sel : Z) : Prop :=
  Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned a1) 2))) 24 = 8 * Z.land (Z.shiftr sel 5) 3 /\
  Z.land (bv_unsigned a1) 255 = sel.

Lemma op1_sx_ok : forall sel, 0 <= sel < 256 ->
  op1_sel_ok (Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 sel)) 56))) 56)) sel.
Proof.
  intros sel Hsel. split; op1_bytes sel Hsel.
Qed.

Lemma op1_sel0_ok : op1_sel_ok (Z_to_bv 64 0) 0.
Proof. split; reflexivity. Qed.

(* From the tail's call state to op1_post. *)
Lemma op1_tail_post : forall (Q : machine_state -> Prop) (t0 a3 a4 a6 : word) (whi wlo R S8 : Z),
  (forall ms, op1_post ms -> Q ms) ->
  Z.lor (bv_unsigned t0) (bv_unsigned a6) = r_send -> bv_unsigned a3 mod 2 ^ 32 = r_ack ->
  a4 = Z_to_bv 64 r_retry -> S8 = r_S5 -> R = r_nr -> whi * 256 + wlo = r_w ->
  forall t2' : word,
    Q (ST 0x8237c t0 (Z_to_bv 64 R) t2' (Z_to_bv 64 (LS.lc_fdst_a (og 0))) (Z_to_bv 64 (LS.lc_fsrc_a (og 0)))
          (Z_to_bv 64 (Z.lor (bv_unsigned t0) (bv_unsigned a6))) a3 a4 (Z_to_bv 64 (LS.lc_fcmd (og 0)))
          (Z_to_bv 64 S8) (Z_to_bv 64 (Z.min ((whi * 256 + wlo) mod 1485) R))
          (Z_to_bv 64 (S8 + Z.min ((whi * 256 + wlo) mod 1485) R))
          (Z_to_bv 64 (R - Z.min ((whi * 256 + wlo) mod 1485) R)) (Z_to_bv 64 S8)).
Proof.
  intros Q t0 a3 a4 a6 whi wlo R S8 HK Hs Ha -> -> -> Hw t2'. rewrite Hw. apply HK.
  exists t0, (Z_to_bv 64 r_nr), t2', (Z_to_bv 64 (Z.lor (bv_unsigned t0) (bv_unsigned a6))), a3, (Z_to_bv 64 r_S5).
  split; [reflexivity|]. split; [|exact Ha].
  pose proof r_send_range. rewrite Hs, unsigned_lit by lia. reflexivity.
Qed.

(* ---- the checked loads of the input bytes ---- *)

(* The instrumented check of a 1-byte load at X (the address register holds Z_to_bv 64 X): `srli`, `add` of the
   shadow base, `lb` of the shadow byte k (MK, its footprint RS), `bnez`; when k <> 0 the handler's `andi 7` and
   `blt` back to the load, taken because X mod 8 < k (SK). BODY continues at the load in both cases. *)
Ltac op1_chk X MK SK RS BODY :=
  step; let g := fresh "g" in let G := fresh "G" in
  gen_shr (Z_to_bv 64 X) g G; rewrite (unsigned_lit X) in G by lia;
  step; let h := fresh "h" in let H := fresh "H" in gen_addi g h H;
  let R := fresh "R" in pose proof (rdw0 _ h _ _ MK ltac:(lia)) as R; step; clear R;
  step; rewrite sxb_eq0;
  lazymatch type of MK with
  | mrd _ _ _ = Some ?k =>
      let C := fresh "C" in destruct SK as [C|C];
      [ rewrite (proj2 (Z.eqb_eq _ _) C); cbn [negb]; cbv iota; BODY
      | rewrite (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb]; cbv iota;
        step; rewrite land7, (unsigned_lit X) by lia;
        step; rewrite (lts_low (X mod 8) k ltac:(apply Z.mod_pos_bound; lia)), (proj2 (Z.ltb_lt _ _) C); cbv iota;
        BODY ]
  end.

(* A register's value, put in the form the next lemma states. *)
Ltac op1_reg r v := setreg r v ltac:(f_equal; rewrite ?unsigned_lit by lia; lia).

(* +0x1034: w's high byte (s8 = p + off + 8), t1 = n - 9, s8 = the cursor after w; on to the tail. *)
Lemma op1_j8 : forall (Q : machine_state -> Prop) (t0 t2 a1 a3 a5 a6 a7 s3 s7 : word),
  9 <= N -> (forall ms, op1_post ms -> Q ms) -> op1_sel_ok a1 (og 0) ->
  Z.lor (bv_unsigned t0) (bv_unsigned a6) = r_send -> bv_unsigned a3 mod 2 ^ 32 = r_ack ->
  ExecF.evtF rsegs RNG Q (ST 0x82298 t0 (Z_to_bv 64 (N - 6)) t2 (Z_to_bv 64 (P + O + 6)) a1 (Z_to_bv 64 (og 6)) a3
                           (Z_to_bv 64 r_retry) a5 a6 a7 s3 s7 (Z_to_bv 64 (P + O + 8))).
Proof.
  intros Q t0 t2 a1 a3 a5 a6 a7 s3 s7 HN9 HK (HA1 & HA2) Hs Ha.
  (* 0x82298 lbu a5, 0(s8); 0x8229c addi t1, t1, -3; 0x822a0 addi s8, a0, 3 *)
  pose proof (HRB 8 ltac:(lia)) as RB. pose proof (HRD 8 ltac:(lia)) as RD. step. clear RB RD. rewrite (og_byte 8 7 ltac:(lia) eq_refl).
  do 2 step. op1_reg 6 (Z_to_bv 64 (N - 9)). op1_reg 24 (Z_to_bv 64 (P + O + 9)).
  apply (op1_tail Q t0 t2 _ a1 a3 _ a6 _ s3 s7 (og 7) (og 6) (N - 9) (P + O + 9) (og 0));
    [apply og_range | apply og_range | lia | lia | lia | apply og_range | exact HA1 | exact HA2 |].
  pose proof (og_range 6). pose proof (og_range 7).
  apply op1_tail_post; [exact HK | exact Hs | exact Ha | reflexivity | unfold r_S5; lia | unfold r_nr; lia |].
  unfold r_w. rewrite lor_shiftl8_add by lia. lia.
Qed.

(* +0xd14: w's low byte (s8 = p + off + 7), s8 = p + off + 8, `bne t1, a5` (t1 = n - 6 against 2). *)
Lemma op1_j7 : forall (Q : machine_state -> Prop) (t0 t2 a1 a2 a3 a5 a6 a7 s3 s7 : word),
  8 <= N -> (forall ms, op1_post ms -> Q ms) -> op1_sel_ok a1 (og 0) ->
  Z.lor (bv_unsigned t0) (bv_unsigned a6) = r_send -> bv_unsigned a3 mod 2 ^ 32 = r_ack ->
  ExecF.evtF rsegs RNG Q (ST 0x81f78 t0 (Z_to_bv 64 (N - 6)) t2 (Z_to_bv 64 (P + O + 6)) a1 a2 a3
                           (Z_to_bv 64 r_retry) a5 a6 a7 s3 s7 (Z_to_bv 64 (P + O + 7))).
Proof.
  intros Q t0 t2 a1 a2 a3 a5 a6 a7 s3 s7 HN8 HK HSEL Hs Ha.
  pose proof HSEL as (HA1 & HA2).
  (* 0x81f78 lbu a2, 0(s8); addi s8, a0, 2; li a5, 2; bne t1, a5 *)
  pose proof (HRB 7 ltac:(lia)) as RB. pose proof (HRD 7 ltac:(lia)) as RD. step. clear RB RD. rewrite (og_byte 7 6 ltac:(lia) eq_refl).
  do 3 step. op1_reg 24 (Z_to_bv 64 (P + O + 8)).
  if_cases K; zify_cond K.
  - (* n > 8: the check of w's high byte at p + off + 8 *)
    destruct (HSH 8 ltac:(lia)) as (sk & MK & SK). pose proof (HRS 8 ltac:(lia)) as RS.
    op1_chk (P + O + 8) MK SK RS ltac:(eapply op1_j8; [lia | exact HK | exact HSEL | exact Hs | exact Ha]).
  - (* n = 8: 0x81f88 li t1, 0; j; 0x81f40 li a5, 0; j 0x822a4 *)
    assert (E8 : N = 8) by lia.
    do 4 step.
    apply (op1_tail Q t0 t2 _ a1 a3 _ a6 _ s3 s7 0 (og 6) 0 (P + O + 8) (og 0));
      [lia | apply og_range | lia | lia | lia | apply og_range | exact HA1 | exact HA2 |].
    pose proof (og_range 6).
    apply op1_tail_post; [exact HK | exact Hs | exact Ha | reflexivity | unfold r_S5; lia | unfold r_nr; lia |].
    unfold r_w. rewrite (og_zero 7) by lia. rewrite lor_shiftl8_add by lia. lia.
Qed.

(* +0xcc0: the retry byte (a0 = p + off + 6), s8 = p + off + 7, retry = r & 3, `bne t1, a2` (t1 = n - 6 against
   1). *)
Lemma op1_j6 : forall (Q : machine_state -> Prop) (t0 t2 a1 a2 a3 a4 a5 a6 a7 s3 s7 s8 : word),
  7 <= N -> (forall ms, op1_post ms -> Q ms) -> op1_sel_ok a1 (og 0) ->
  Z.lor (bv_unsigned t0) (bv_unsigned a6) = r_send -> bv_unsigned a3 mod 2 ^ 32 = r_ack ->
  ExecF.evtF rsegs RNG Q (ST 0x81f24 t0 (Z_to_bv 64 (N - 6)) t2 (Z_to_bv 64 (P + O + 6)) a1 a2 a3 a4 a5 a6 a7 s3 s7
                           s8).
Proof.
  intros Q t0 t2 a1 a2 a3 a4 a5 a6 a7 s3 s7 s8 HN7 HK HSEL Hs Ha.
  pose proof HSEL as (HA1 & HA2).
  (* 0x81f24 lbu a4, 0(a0); addi s8, a0, 1; andi a4, a4, 3; li a2, 1; bne t1, a2 *)
  pose proof (HRB 6 ltac:(lia)) as RB. pose proof (HRD 6 ltac:(lia)) as RD. step. clear RB RD. rewrite (og_byte 6 5 ltac:(lia) eq_refl).
  do 4 step. op1_reg 24 (Z_to_bv 64 (P + O + 7)).
  pose proof (og_range 5).
  setreg 14 (Z_to_bv 64 r_retry) ltac:(unfold r_retry; f_equal; rewrite unsigned_lit by lia; reflexivity).
  if_cases K; zify_cond K.
  - (* n > 7: the check of w's low byte at p + off + 7 *)
    destruct (HSH 7 ltac:(lia)) as (sk & MK & SK). pose proof (HRS 7 ltac:(lia)) as RS.
    op1_chk (P + O + 7) MK SK RS ltac:(eapply op1_j7; [lia | exact HK | exact HSEL | exact Hs | exact Ha]).
  - (* n = 7: 0x81f38 li t1, 0; li a2, 0; li a5, 0; j 0x822a4 *)
    do 4 step.
    apply (op1_tail Q t0 t2 _ a1 a3 _ a6 _ s3 s7 0 0 0 (P + O + 7) (og 0));
      [lia | lia | lia | lia | lia | apply og_range | exact HA1 | exact HA2 |].
    apply op1_tail_post; [exact HK | exact Hs | exact Ha | reflexivity | unfold r_S5; lia | unfold r_nr; lia |].
    unfold r_w. rewrite (og_zero 6), (og_zero 7) by lia. reflexivity.
Qed.


(* +0xcf0, no retry byte (n <= 6): retry = 0, w = 0, s8 = a0 = the cursor's end; on to the tail. *)
Lemma op1_end0 : forall (Q : machine_state -> Prop) (t0 t2 a1 a2 a3 a4 a5 a6 a7 s3 s7 s8 : word),
  2 <= N <= 6 -> (forall ms, op1_post ms -> Q ms) -> op1_sel_ok a1 (og 0) ->
  Z.lor (bv_unsigned t0) (bv_unsigned a6) = r_send -> bv_unsigned a3 mod 2 ^ 32 = r_ack ->
  ExecF.evtF rsegs RNG Q (ST 0x81f54 t0 (Z_to_bv 64 0) t2 (Z_to_bv 64 (P + O + N)) a1 a2 a3 a4 a5 a6 a7 s3 s7 s8).
Proof.
  intros Q t0 t2 a1 a2 a3 a4 a5 a6 a7 s3 s7 s8 HN6 HK (HA1 & HA2) Hs Ha.
  (* 0x81f54 li a4, 0; li a2, 0; li a5, 0; mv s8, a0; j 0x822a4 *)
  do 5 step.
  apply (op1_tail Q t0 t2 _ a1 a3 _ a6 _ s3 s7 0 0 0 (P + O + N) (og 0));
    [lia | lia | lia | lia | lia | apply og_range | exact HA1 | exact HA2 |].
  apply op1_tail_post; [exact HK | exact Hs | exact Ha | | unfold r_S5; lia | unfold r_nr; lia |].
  - unfold r_retry. rewrite (og_zero 5) by lia. reflexivity.
  - unfold r_w. rewrite (og_zero 6), (og_zero 7) by lia. reflexivity.
Qed.

(* +0xcb0 (n >= 7): the check of the retry byte at a0 = p + off + 6; on to its load. *)
Lemma op1_retry : forall (Q : machine_state -> Prop) (t0 t2 a1 a2 a3 a4 a5 a6 a7 s3 s7 s8 : word),
  7 <= N -> (forall ms, op1_post ms -> Q ms) -> op1_sel_ok a1 (og 0) ->
  Z.lor (bv_unsigned t0) (bv_unsigned a6) = r_send -> bv_unsigned a3 mod 2 ^ 32 = r_ack ->
  ExecF.evtF rsegs RNG Q (ST 0x81f14 t0 (Z_to_bv 64 (N - 6)) t2 (Z_to_bv 64 (P + O + 6)) a1 a2 a3 a4 a5 a6 a7 s3 s7
                           s8).
Proof.
  intros Q t0 t2 a1 a2 a3 a4 a5 a6 a7 s3 s7 s8 HN7 HK HSEL Hs Ha.
  destruct (HSH 6 ltac:(lia)) as (sk & MK & SK). pose proof (HRS 6 ltac:(lia)) as RS.
  op1_chk (P + O + 6) MK SK RS ltac:(eapply op1_j6; [lia | exact HK | exact HSEL | exact Hs | exact Ha]).
Qed.

(* +0xc9c: sel's sign extension, `bltz` on bit 7: ack = g_last_counter (`ld a2, 48(s1)`, `lw a3, -1064(a2)`) when
   it is set, else ack = hi << 8 | lo; then the retry byte when bytes are left (t1 <> 0). *)
Lemma op1_c9c : forall (Q : machine_state -> Prop) (t0 t2 a4 a5 a6 a7 s3 s7 s8 : word) (AH AL T1 A0 : Z),
  2 <= N -> T1 = N - Z.min N 6 -> A0 = P + O + Z.min N 6 -> (forall ms, op1_post ms -> Q ms) ->
  Z.lor (bv_unsigned t0) (bv_unsigned a6) = r_send ->
  0 <= AH < 2 ^ 32 -> 0 <= AL < 256 -> Z.lor AH AL = Z.lor (og 3) (Z.shiftl (og 4) 8) ->
  ExecF.evtF rsegs RNG Q (ST 0x81f00 t0 (Z_to_bv 64 T1) t2 (Z_to_bv 64 A0)
                           (Z_to_bv 64 (og 0)) (Z_to_bv 64 AL) (Z_to_bv 64 AH) a4 a5 a6 a7 s3 s7 s8).
Proof.
  intros Q t0 t2 a4 a5 a6 a7 s3 s7 s8 AH AL T1 A0 HN2 -> -> HK Hs HAH HAL Hack.
  pose proof (og_range 0) as R0. pose proof (og_range 3). pose proof (og_range 4).
  pose proof (op1_sx_ok (og 0) R0) as HSEL.
  (* 0x81f00 slli a1, a1, 56; srai a1, a1, 56; bltz a1 *)
  do 3 step.
  rewrite (op1_sx_lts (og 0) R0).
  destruct (Z.land (og 0) 128 =? 0) eqn:E80; cbn [negb]; cbv iota.
  - (* bit 7 clear: 0x81f0c or a3, a3, a2; 0x81f10 beqz t1 *)
    step.
    assert (Ha : bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 AH)) (bv_unsigned (Z_to_bv 64 AL)))) mod 2 ^ 32
                 = r_ack).
    { unfold r_ack. rewrite E80. rewrite (unsigned_lit AH), (unsigned_lit AL) by lia. rewrite Hack.
      rewrite lor_shiftl8_add by lia. rewrite unsigned_lit by lia. apply Z.mod_small. lia. }
    step.
    destruct (Z_le_gt_dec N 6) as [L6|G6].
    + rewrite (Z.min_l N 6) by lia. op1_reg 6 (Z_to_bv 64 0). brF true.
      eapply op1_end0; [lia | exact HK | exact HSEL | exact Hs | exact Ha].
    + rewrite (Z.min_r N 6) by lia.
      if_cases K; zify_cond K; [lia|].
      eapply op1_retry; [lia | exact HK | exact HSEL | exact Hs | exact Ha].
  - (* bit 7 set: 0x81f48 ld a2, 48(s1); lw a3, -1064(a2) (g_last_counter); 0x81f50 bnez t1 *)
    do 2 step. rewrite lw_world.
    assert (Ha : bv_unsigned (Z_to_bv 64 (TW.s32_at Bw TW.OFF_g_last_counter)) mod 2 ^ 32 = r_ack)
      by (unfold r_ack; rewrite E80; exact (POP.op1_lastc Bw)).
    step.
    destruct (Z_le_gt_dec N 6) as [L6|G6].
    + rewrite (Z.min_l N 6) by lia. op1_reg 6 (Z_to_bv 64 0). brF false.
      eapply op1_end0; [lia | exact HK | exact HSEL | exact Hs | exact Ha].
    + rewrite (Z.min_r N 6) by lia.
      if_cases K; zify_cond K; [|lia].
      eapply op1_retry; [lia | exact HK | exact HSEL | exact Hs | exact Ha].
Qed.

(* +0x1318 (n >= 6): ack's high byte (a0 = p + off + 5), t1 = n - 6, a0 = p + off + 6, a3 = hi << 8; to +0xc9c. *)
Lemma op1_j5 : forall (Q : machine_state -> Prop) (t0 t1 t2 a3 a4 a5 a6 a7 s3 s7 s8 : word),
  6 <= N -> (forall ms, op1_post ms -> Q ms) -> Z.lor (bv_unsigned t0) (bv_unsigned a6) = r_send ->
  ExecF.evtF rsegs RNG Q (ST 0x8257c t0 t1 t2 (Z_to_bv 64 (P + O + 5)) (Z_to_bv 64 (og 0)) (Z_to_bv 64 (og 3)) a3 a4
                           a5 a6 a7 s3 s7 s8).
Proof.
  intros Q t0 t1 t2 a3 a4 a5 a6 a7 s3 s7 s8 HN6 HK Hs.
  pose proof (og_range 3). pose proof (og_range 4).
  (* 0x8257c lbu a3, 0(a0); addi t1, s11, -6; addi a0, s9, 6; slliw a3, a3, 8; j 0x81f00 *)
  pose proof (HRB 5 ltac:(lia)) as RB. pose proof (HRD 5 ltac:(lia)) as RD. step. clear RB RD.
  rewrite (og_byte 5 4 ltac:(lia) eq_refl).
  do 4 step.
  op1_reg 6 (Z_to_bv 64 (N - 6)). op1_reg 10 (Z_to_bv 64 (P + O + 6)).
  setreg 13 (Z_to_bv 64 (Z.shiftl (og 4) 8))
    ltac:(f_equal; rewrite (unsigned_lit (og 4)) by lia; rewrite Z.shiftl_mul_pow2 by lia; symmetry;
          apply bv_swrap_small; change (bv_half_modulus 32) with (2 ^ 31); lia).
  apply (op1_c9c Q t0 t2 a4 a5 a6 a7 s3 s7 s8 (Z.shiftl (og 4) 8) (og 3) (N - 6) (P + O + 6));
    [lia | lia | lia | exact HK | exact Hs | rewrite Z.shiftl_mul_pow2 by lia; lia | lia | apply Z.lor_comm].
Qed.

(* +0x1134 (n >= 5): ack's low byte (a0 = p + off + 4), a0 = p + off + 5, `bne s11, a3` (n against 5). *)
Lemma op1_j4 : forall (Q : machine_state -> Prop) (t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s7 s8 : word),
  5 <= N -> (forall ms, op1_post ms -> Q ms) -> Z.lor (bv_unsigned t0) (bv_unsigned a6) = r_send ->
  ExecF.evtF rsegs RNG Q (ST 0x82398 t0 t1 t2 (Z_to_bv 64 (P + O + 4)) (Z_to_bv 64 (og 0)) a2 a3 a4 a5 a6 a7 s3 s7
                           s8).
Proof.
  intros Q t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s7 s8 HN5 HK Hs.
  pose proof (og_range 3). pose proof (og_range 4).
  (* 0x82398 lbu a2, 0(a0); addi a0, s9, 5; li a3, 5; bne s11, a3 *)
  pose proof (HRB 4 ltac:(lia)) as RB. pose proof (HRD 4 ltac:(lia)) as RD. step. clear RB RD.
  rewrite (og_byte 4 3 ltac:(lia) eq_refl).
  do 3 step. op1_reg 10 (Z_to_bv 64 (P + O + 5)).
  if_cases K; zify_cond K.
  - (* n > 5: the check of ack's high byte at p + off + 5 *)
    destruct (HSH 5 ltac:(lia)) as (sk & MK & SK). pose proof (HRS 5 ltac:(lia)) as RS.
    op1_chk (P + O + 5) MK SK RS ltac:(eapply op1_j5; [lia | exact HK | exact Hs]).
  - (* n = 5: 0x823a8 li t1, 0; j; 0x81efc li a3, 0 *)
    do 3 step.
    apply (op1_c9c Q t0 _ a4 a5 a6 a7 s3 s7 s8 0 (og 3) 0 (P + O + 5));
      [lia | lia | lia | exact HK | exact Hs | lia | lia |].
    rewrite (og_zero 4) by lia. rewrite Z.lor_comm. reflexivity.
Qed.

(* +0xc7c (n >= 4): send's high byte (a0 = p + off + 3), a0 = p + off + 4, t0 = hi << 8, `bne s11, a2` (n against
   4). *)
Lemma op1_j3 : forall (Q : machine_state -> Prop) (t0 t1 t2 a2 a3 a4 a5 a7 s3 s7 s8 : word),
  4 <= N -> (forall ms, op1_post ms -> Q ms) ->
  ExecF.evtF rsegs RNG Q (ST 0x81ee0 t0 t1 t2 (Z_to_bv 64 (P + O + 3)) (Z_to_bv 64 (og 0)) a2 a3 a4 a5
                           (Z_to_bv 64 (og 1)) a7 s3 s7 s8).
Proof.
  intros Q t0 t1 t2 a2 a3 a4 a5 a7 s3 s7 s8 HN4 HK.
  pose proof (og_range 1). pose proof (og_range 2).
  (* 0x81ee0 lbu t0, 0(a0); addi a0, s9, 4; slli t0, t0, 8; li a2, 4; bne s11, a2 *)
  pose proof (HRB 3 ltac:(lia)) as RB. pose proof (HRD 3 ltac:(lia)) as RD. step. clear RB RD.
  rewrite (og_byte 3 2 ltac:(lia) eq_refl).
  do 4 step. op1_reg 10 (Z_to_bv 64 (P + O + 4)).
  op1_reg 5 (Z_to_bv 64 (Z.shiftl (og 2) 8)).
  assert (Hs : Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (og 2) 8))) (bv_unsigned (Z_to_bv 64 (og 1))) = r_send)
    by (unfold r_send; rewrite !unsigned_lit by (rewrite ?Z.shiftl_mul_pow2 by lia; lia); apply Z.lor_comm).
  if_cases K; zify_cond K.
  - (* n > 4: the check of ack's low byte at p + off + 4 *)
    destruct (HSH 4 ltac:(lia)) as (sk & MK & SK). pose proof (HRS 4 ltac:(lia)) as RS.
    op1_chk (P + O + 4) MK SK RS ltac:(eapply op1_j4; [lia | exact HK | exact Hs]).
  - (* n = 4: 0x81ef4 li t1, 0; li a2, 0; li a3, 0 *)
    do 3 step.
    apply (op1_c9c Q _ _ a4 a5 _ a7 s3 s7 s8 0 0 0 (P + O + 4)); [lia | lia | lia | exact HK | exact Hs | lia | lia |].
    rewrite (og_zero 3), (og_zero 4) by lia. reflexivity.
Qed.

(* +0x920 (n >= 3): send's low byte (a0 = p + off + 2), a0 = p + off + 3, `bne s11, a2` (n against 3). *)
Lemma op1_j2 : forall (Q : machine_state -> Prop) (t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s7 s8 : word),
  3 <= N -> (forall ms, op1_post ms -> Q ms) ->
  ExecF.evtF rsegs RNG Q (ST 0x81b84 t0 t1 t2 (Z_to_bv 64 (P + O + 2)) (Z_to_bv 64 (og 0)) a2 a3 a4 a5 a6 a7 s3 s7
                           s8).
Proof.
  intros Q t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s7 s8 HN3 HK.
  pose proof (og_range 1). pose proof (og_range 2).
  (* 0x81b84 lbu a6, 0(a0); addi a0, s9, 3; li a2, 3; bne s11, a2 *)
  pose proof (HRB 2 ltac:(lia)) as RB. pose proof (HRD 2 ltac:(lia)) as RD. step. clear RB RD.
  rewrite (og_byte 2 1 ltac:(lia) eq_refl).
  do 3 step. op1_reg 10 (Z_to_bv 64 (P + O + 3)).
  if_cases K; zify_cond K.
  - (* n > 3: the check of send's high byte at p + off + 3 *)
    destruct (HSH 3 ltac:(lia)) as (sk & MK & SK). pose proof (HRS 3 ltac:(lia)) as RS.
    op1_chk (P + O + 3) MK SK RS ltac:(eapply op1_j3; [lia | exact HK]).
  - (* n = 3: 0x81b94 li t0, 0; j; 0x81ef4 li t1, 0; li a2, 0; li a3, 0 *)
    do 5 step.
    apply (op1_c9c Q _ _ a4 a5 _ a7 s3 s7 s8 0 0 0 (P + O + 3)); [lia | lia | lia | exact HK | | lia | lia |].
    + unfold r_send. rewrite (og_zero 2) by lia. rewrite !unsigned_lit by lia. rewrite Z.lor_0_l, Z.lor_comm.
      reflexivity.
    + rewrite (og_zero 3), (og_zero 4) by lia. reflexivity.
Qed.

(* +0x5fc (n >= 2): sel (s8 = p + off + 1), a0 = p + off + 2, `bne s11, a2` (n against 2). *)
Lemma op1_j1 : forall (Q : machine_state -> Prop) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s7 : word),
  2 <= N -> (forall ms, op1_post ms -> Q ms) ->
  ExecF.evtF rsegs RNG Q (ST 0x81860 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s7 (Z_to_bv 64 (P + O + 1))).
Proof.
  intros Q t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s7 HN2 HK.
  pose proof (og_range 0).
  (* 0x81860 lbu a1, 0(s8); addi a0, s9, 2; li a2, 2; bne s11, a2 *)
  pose proof (HRB 1 ltac:(lia)) as RB. pose proof (HRD 1 ltac:(lia)) as RD. step. clear RB RD.
  rewrite (og_byte 1 0 ltac:(lia) eq_refl).
  do 3 step. op1_reg 10 (Z_to_bv 64 (P + O + 2)).
  if_cases K; zify_cond K.
  - (* n > 2: the check of send's low byte at p + off + 2 *)
    destruct (HSH 2 ltac:(lia)) as (sk & MK & SK). pose proof (HRS 2 ltac:(lia)) as RS.
    op1_chk (P + O + 2) MK SK RS ltac:(eapply op1_j2; [lia | exact HK]).
  - (* n = 2: 0x8186c li t0, 0; li a6, 0; j; 0x81ef4 li t1, 0; li a2, 0; li a3, 0 *)
    do 6 step.
    apply (op1_c9c Q _ _ a4 a5 _ a7 s3 s7 _ 0 0 0 (P + O + 2)); [lia | lia | lia | exact HK | | lia | lia |].
    + unfold r_send. rewrite (og_zero 1), (og_zero 2) by lia. reflexivity.
    + rewrite (og_zero 3), (og_zero 4) by lia. reflexivity.
Qed.

(* ARM1, +0x5e8: `beqz s7` (no byte after the op byte: every value 0), else the check of sel at s8 = p + off + 1. *)
Lemma op1_run : forall (Q : machine_state -> Prop) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 : word),
  (forall ms, op1_post ms -> Q ms) ->
  ExecF.evtF rsegs RNG Q
    (ST 0x8184c t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 (Z_to_bv 64 (N - 1)) (Z_to_bv 64 (P + O + 1))).
Proof.
  intros Q t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 HK.
  step.
  if_cases K; zify_cond K.
  - (* n = 1: 0x81a60 .. 0x81a78 t1 = a3 = a1 = t0 = a6 = a4 = 0, j; 0x81f3c li a2, 0; li a5, 0; j 0x822a4 *)
    assert (E1 : N = 1) by lia.
    do 10 step.
    apply (op1_tail Q _ t2 _ _ _ _ _ a7 s3 _ 0 0 0 (P + O + 1) (og 0));
      [lia | lia | lia | lia | lia | apply og_range | | |].
    + rewrite (og_zero 0) by lia. reflexivity.
    + rewrite (og_zero 0) by lia. reflexivity.
    + apply op1_tail_post; [exact HK | | | | unfold r_S5; lia | unfold r_nr; lia |].
      * unfold r_send. rewrite (og_zero 1), (og_zero 2) by lia. reflexivity.
      * unfold r_ack. rewrite (og_zero 0), (og_zero 3), (og_zero 4) by lia. reflexivity.
      * unfold r_retry. rewrite (og_zero 5) by lia. reflexivity.
      * unfold r_w. rewrite (og_zero 6), (og_zero 7) by lia. reflexivity.
  - (* n >= 2: the check of sel at p + off + 1 *)
    destruct (HSH 1 ltac:(lia)) as (sk & MK & SK). pose proof (HRS 1 ltac:(lia)) as RS.
    op1_chk (P + O + 1) MK SK RS ltac:(eapply op1_j1; [lia | exact HK]).
Qed.


(* The run as one statement: from ARM1 to the call of build_and_receive, at op1_post. *)
Lemma op1_run_post : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 : word),
  ExecF.evtF rsegs RNG op1_post
    (ST 0x8184c t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 (Z_to_bv 64 (N - 1)) (Z_to_bv 64 (P + O + 1))).
Proof. intros. apply op1_run. intros ms H. exact H. Qed.

End Run.
