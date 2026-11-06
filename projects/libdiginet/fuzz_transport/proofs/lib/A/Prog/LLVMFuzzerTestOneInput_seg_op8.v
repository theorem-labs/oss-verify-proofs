(* LLVMFuzzerTestOneInput_seg_op8: proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk).
   Sub-row AW72h: lc_op8_stmt of lib/A/Prog/LLVMFuzzerTestOneInput_segs.v, the piece OP8 (+0x6e8 .. +0x904) of the
   image-A walk of fuzz_transport.asan's LLVMFuzzerTestOneInput: from the first instruction of arm 8 (0x8194c) to
   the call of receive at +0x908 (0x81b6c). Theorem lc_op8_ok.

   The code (the listing DgnTransportList.v, slot k at 0x81264 + 4k; offsets from 0x81264). At the arm, s9 / s11
   hold the cursor { p + o, nn } before the op byte and s8 / s7 the one after it (nn >= 1):
     +0x6e8          `beqz s7`: no byte after the op byte goes to +0x824 (a3 = 0: the poll flags; no record);
     +0x6ec .. +0x6f8 the check of the byte at s8 = p + o + 1 (its shadow byte k at (s8 >> 3) + s10; k <> 0 goes to
                     the slow path +0x1380, `andi a1, s8, 7`, `blt a1, a0` back to +0x6fc, else the report call
                     0x82cc4);
     +0x6fc .. +0x708 a3 = the poll flags byte; s8 = s9 + 2; `beq s11, 2` goes to +0x828 (no byte of the u16);
     +0x70c .. +0x718 the check of the byte at p + o + 2 (slow path +0x13c8, report 0x82ce0);
     +0x71c .. +0x728 a1 = the u16's low byte; s8 = s9 + 3; `bne s11, 3` goes to +0xd2c, else +0x72c s11 = 0 and
                     `j` +0x830 (no high byte);
     +0xd2c .. +0xd38 the check of the byte at p + o + 3 (slow path +0x1470, report 0x82d0c);
     +0xd3c .. +0xd4c a2 = the high byte << 8; s11 = nn - 4; s8 = s9 + 4; `j` +0x834;
     +0x824 .. +0x850 the take (fuzz_take): a1 = a2 | a1 = w; a1 = min (w, s11) (`bltu`, `mv`); s3 = s8 + a1;
                     s7 = s11 - a1; a2 = 1 (by_poll); a0 = s8; `j` +0x908.
   The model (lc_recv_vals' op-8 branch, o8_vals here): the poll flags byte, then fuzz_record (TOps.v :69-71) from
   the cursor after it; o8_v1 .. o8_v4 compute it on the four ways of the code (nn = 1, 2, 3, >= 4).

   The machine run (module O8Run) is a footprint run (lib/Lib/ExecF.v evtF, stepped by lib/Lib/StepF.v step), as
   diginet_frame_build_seg_loop.v's check fb_ck_F: each of the three checks reads a shadow byte that is 0 or above
   the byte's offset in its granule (o8_shadow1, from the addressability of the input block), so no report call is
   reached; the run writes no memory. The walk (lc_op8_ok) carries the run into SRr with DgnTransportCgRun.v
   decode_run: the input's read range is DgnTransportCg.v decode_rd_ok of the block (p, n) of ablocks
   (LLVMFuzzerTestOneInput_st.v lc_geom, trans_src_ok_rd), its bytes the garr8 of lc_input; the G journal follows the
   run's model materialization by W_journalG.v ajournal_gx_exec with no byte written (FP-generic); every register
   the cut RECV fixes and the run does not set is the cut ARM8's. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require PropExec MState Mem Exec Frame Cells Step Tac
  Bytes ZBridge ExecF StepF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require AsanKA AsanKAProof.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require LLVMFuzzerTestOneInput_segs.
Import ListNotations.
Open Scope Z_scope.

Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module DS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LCS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.LLVMFuzzerTestOneInput_segs.

(* ======== the model of op 8's reads ======== *)

(* lc_recv_vals' op-8 branch, from the cursor c1 after the op byte. *)
Definition o8_vals (D : list byte) (c1 : TOP.fuzz_in) : LCS.lrv :=
  let (c2, pf) := TOP.fuzz_u8_m D c1 in
  let '(c3, off, n) := TOP.fuzz_record_m D c2 in LCS.mkLrv 1 pf off n c3.

Lemma o8_recv_vals : forall D c, LCS.lc_opc D c = 8 -> LCS.lc_recv_vals D c = o8_vals D (LCS.lc_oc D c).
Proof.
  intros D c H. unfold LCS.lc_opc, LCS.lc_oc in *. unfold LCS.lc_recv_vals, o8_vals.
  destruct (TOP.fuzz_u8_m D c) as [c1 opb]. cbn [fst snd] in *. rewrite H. reflexivity.
Qed.

Lemma o8_u8_some : forall D c, TOP.fi_n c <> 0 ->
  TOP.fuzz_u8_m D c = (TOP.FuzzIn (TOP.fi_off c + 1) (TOP.fi_n c - 1), DS.at8 D (Z.to_nat (TOP.fi_off c))).
Proof. intros D c H. unfold TOP.fuzz_u8_m. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.

Lemma o8_u8_none : forall D c, TOP.fi_n c = 0 -> TOP.fuzz_u8_m D c = (c, 0).
Proof. intros D c H. unfold TOP.fuzz_u8_m. rewrite H. reflexivity. Qed.

Lemma o8_take : forall c w, TOP.fuzz_take_m c w =
  (TOP.FuzzIn (TOP.fi_off c + (if w <? TOP.fi_n c then w else TOP.fi_n c))
              (TOP.fi_n c - (if w <? TOP.fi_n c then w else TOP.fi_n c)),
   TOP.fi_off c, if w <? TOP.fi_n c then w else TOP.fi_n c).
Proof. reflexivity. Qed.

Lemma o8_at8_range : forall D k, 0 <= DS.at8 D k < 256.
Proof.
  intros D k. unfold DS.at8, DS.bz. pose proof (bv_unsigned_in_range 8 (nth k D (DS.b8 0))) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. exact R.
Qed.

(* The four ways of the code, as the model's values. *)
Lemma o8_v1 : forall D o, o8_vals D (TOP.FuzzIn (o + 1) (1 - 1)) = LCS.mkLrv 1 0 (o + 1) 0 (TOP.FuzzIn (o + 1) 0).
Proof.
  intros D o. unfold o8_vals.
  rewrite (o8_u8_none D (TOP.FuzzIn (o + 1) (1 - 1)) eq_refl).
  unfold TOP.fuzz_record_m, TOP.fuzz_u16_m.
  rewrite !(o8_u8_none D (TOP.FuzzIn (o + 1) (1 - 1)) eq_refl).
  rewrite o8_take. cbn [TOP.fi_off TOP.fi_n]. change (Z.lor 0 (Z.shiftl 0 8) mod 2 ^ 16) with 0.
  change (0 <? 1 - 1) with false. cbv iota. rewrite Z.add_0_r. reflexivity.
Qed.

Lemma o8_v2 : forall D o, o8_vals D (TOP.FuzzIn (o + 1) (2 - 1)) =
  LCS.mkLrv 1 (DS.at8 D (Z.to_nat (o + 1))) (o + 2) 0 (TOP.FuzzIn (o + 2) 0).
Proof.
  intros D o. unfold o8_vals.
  rewrite (o8_u8_some D (TOP.FuzzIn (o + 1) (2 - 1)) ltac:(cbn; lia)). cbn [TOP.fi_off TOP.fi_n].
  unfold TOP.fuzz_record_m, TOP.fuzz_u16_m.
  rewrite !(o8_u8_none D (TOP.FuzzIn (o + 1 + 1) (2 - 1 - 1)) eq_refl).
  rewrite o8_take. cbn [TOP.fi_off TOP.fi_n]. change (Z.lor 0 (Z.shiftl 0 8) mod 2 ^ 16) with 0.
  change (0 <? 2 - 1 - 1) with false. cbv iota.
  replace (o + 1 + 1 + (2 - 1 - 1)) with (o + 2) by lia. replace (o + 1 + 1) with (o + 2) by lia. reflexivity.
Qed.

Lemma o8_v3 : forall D o, o8_vals D (TOP.FuzzIn (o + 1) (3 - 1)) =
  LCS.mkLrv 1 (DS.at8 D (Z.to_nat (o + 1))) (o + 3) 0 (TOP.FuzzIn (o + 3) 0).
Proof.
  intros D o. unfold o8_vals.
  rewrite (o8_u8_some D (TOP.FuzzIn (o + 1) (3 - 1)) ltac:(cbn; lia)). cbn [TOP.fi_off TOP.fi_n].
  unfold TOP.fuzz_record_m, TOP.fuzz_u16_m.
  rewrite (o8_u8_some D (TOP.FuzzIn (o + 1 + 1) (3 - 1 - 1)) ltac:(cbn; lia)). cbn [TOP.fi_off TOP.fi_n].
  rewrite (o8_u8_none D (TOP.FuzzIn (o + 1 + 1 + 1) (3 - 1 - 1 - 1)) eq_refl).
  rewrite o8_take. cbn [TOP.fi_off TOP.fi_n].
  pose proof (o8_at8_range D (Z.to_nat (o + 1 + 1))) as R.
  set (w := Z.lor (DS.at8 D (Z.to_nat (o + 1 + 1))) (Z.shiftl 0 8) mod 2 ^ 16).
  assert (Hw : 0 <= w) by (unfold w; apply Z.mod_pos_bound; lia).
  replace (w <? 3 - 1 - 1 - 1) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
  replace (o + 1 + 1 + 1 + (3 - 1 - 1 - 1)) with (o + 3) by lia. replace (o + 1 + 1 + 1) with (o + 3) by lia.
  reflexivity.
Qed.

Lemma o8_v4 : forall D o nn, 4 <= nn ->
  let lo := DS.at8 D (Z.to_nat (o + 2)) in let hi := DS.at8 D (Z.to_nat (o + 3)) in
  let w := lo + 256 * hi in
  let n := if w <? nn - 4 then w else nn - 4 in
  o8_vals D (TOP.FuzzIn (o + 1) (nn - 1)) =
  LCS.mkLrv 1 (DS.at8 D (Z.to_nat (o + 1))) (o + 4) n (TOP.FuzzIn (o + 4 + n) (nn - 4 - n)).
Proof.
  intros D o nn H4 lo hi w n. unfold o8_vals.
  rewrite (o8_u8_some D (TOP.FuzzIn (o + 1) (nn - 1)) ltac:(cbn; lia)). cbn [TOP.fi_off TOP.fi_n].
  unfold TOP.fuzz_record_m, TOP.fuzz_u16_m.
  rewrite (o8_u8_some D (TOP.FuzzIn (o + 1 + 1) (nn - 1 - 1)) ltac:(cbn; lia)). cbn [TOP.fi_off TOP.fi_n].
  rewrite (o8_u8_some D (TOP.FuzzIn (o + 1 + 1 + 1) (nn - 1 - 1 - 1)) ltac:(cbn; lia)).
  cbn [TOP.fi_off TOP.fi_n].
  rewrite o8_take. cbn [TOP.fi_off TOP.fi_n].
  replace (o + 1 + 1) with (o + 2) by lia. replace (o + 2 + 1) with (o + 3) by lia.
  pose proof (o8_at8_range D (Z.to_nat (o + 2))) as Rl. pose proof (o8_at8_range D (Z.to_nat (o + 3))) as Rh.
  fold lo hi.
  assert (Ew : Z.lor lo (Z.shiftl hi 8) mod 2 ^ 16 = w).
  { unfold w. rewrite (OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Bytes.lor_shiftl8_add lo hi)
      by lia.
    apply Z.mod_small. lia. }
  rewrite Ew. replace (nn - 1 - 1 - 1 - 1) with (nn - 4) by lia. fold n.
  replace (o + 3 + 1) with (o + 4) by lia. reflexivity.
Qed.

(* ======== the machine run ======== *)

Module O8Run.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.PropExec.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.MState.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Exec.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Frame.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Cells.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Step.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Tac.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Bytes.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.ZBridge.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Img0.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.AsanKA.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.AsanKAProof.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.ExecF.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.StepF.
Local Open Scope Z_scope.

Lemma o8_eqb_lit : forall (w : word) c, 0 <= c < 2 ^ 64 -> bv_eqb w (Z_to_bv 64 c) = (bv_unsigned w =? c).
Proof. intros w c Hc. unfold bv_eqb. rewrite (unsigned_lit c) by lia. reflexivity. Qed.

Lemma o8_ltu : forall (x y : word), bv_ltu x y = (bv_unsigned x <? bv_unsigned y).
Proof. reflexivity. Qed.

(* the shadow byte the check of a 1-byte load at a reads, and the fact the check needs from it *)
Lemma o8_shadow1 : forall m a, addr_byte m a ->
  exists k : byte, mrd rsegs m (wa (a / 8 + 2147450880)) = Some k /\ (bv_signed k = 0 \/ a mod 8 < bv_signed k).
Proof.
  intros m a (AP & k & MK & OK). unfold shadow_addr, ASAN_K in MK. exists k.
  split; [exact MK|]. unfold shadow_ok in OK. lia.
Qed.

(* The post: at the call of receive (0x81b6c), the registers receive's call site reads, from the model's values. *)
Definition o8_post (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s4 s5 s6 s9 s10 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : Z) (R : LCS.lrv) (ms : machine_state) : Prop :=
  exists x10 x11 x12 x13 x19 x23 x24 x27 : word,
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 a4 a5 a6 a7 s2 x19 s4 s5 s6 x23 x24 s9 s10 x27
                 t3 t4 t5 t6) F (Z_to_bv 64 0x81b6c) fc None m (seg_rom rsegs) /\
    bv_unsigned x10 = p + LCS.rv_off R /\ bv_unsigned x11 = LCS.rv_n R /\ bv_unsigned x12 = LCS.rv_bp R /\
    bv_unsigned x13 = LCS.rv_pf R /\ bv_unsigned x19 = p + TOP.fi_off (LCS.rv_c R) /\
    bv_unsigned x23 = TOP.fi_n (LCS.rv_c R).

(* name the register value Z_to_bv 64 e (e mentions bv_unsigned x) by w, with U : bv_unsigned w = e
   (diginet_frame_build_seg_loop.v gen_reg) *)
Local Ltac o8_gen x w U :=
  match goal with
  | |- context [Some (Z_to_bv 64 ?e)] =>
      lazymatch e with
      | context [bv_unsigned x] =>
          let Ew := fresh "Ew" in
          assert (U : bv_unsigned (Z_to_bv 64 e) = e)
            by (apply unsigned_lit; first [lia | Z.div_mod_to_equations; lia]);
          remember (Z_to_bv 64 e) as w eqn:Ew; clear Ew
      end
  end.

(* rewrite each word of the goal by a fact bv_unsigned w = _ *)
Local Ltac o8_wsub :=
  repeat match goal with
  | H : bv_unsigned ?w = _ |- context [bv_unsigned ?w] => is_var w; rewrite H
  end.

(* a register fact bv_unsigned (Z_to_bv 64 e) = _ *)
Local Ltac o8_fact :=
  cbv delta [zxb]; o8_wsub; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia.

Lemma o8_lor : forall b2 b3 : byte,
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (bv_unsigned b3))) 8)))
        (bv_unsigned (Z_to_bv 64 (bv_unsigned b2))) = bv_unsigned b2 + 256 * bv_unsigned b3.
Proof.
  intros b2 b3. pose proof (byte_range b2). pose proof (byte_range b3).
  rewrite (unsigned_lit (bv_unsigned b3)) by lia. rewrite (unsigned_lit (bv_unsigned b2)) by lia.
  rewrite (unsigned_lit (Z.shiftl (bv_unsigned b3) 8)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite Z.lor_comm. apply lor_shiftl8_add; lia.
Qed.

Section Run.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s4 s5 s6 s9 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : Z) (D : list byte) (RNG : ExecF.footprint).
Hypothesis HP : 0 <= p.
Hypothesis HPN : p + Z.of_nat (length D) <= 2 ^ 63.
Hypothesis BA : bytes_at rsegs m p D.
Hypothesis AD : addressable m p (Z.of_nat (length D)).
Hypothesis RB : ExecF.rng RNG p (Z.of_nat (length D)).
Hypothesis RS : forall i, 0 <= i < Z.of_nat (length D) -> ExecF.rng RNG (shadow_addr (p + i)) 1.

(* the machine state of the piece: the registers it may change are a0 .. a3, s3, s7, s8, s11 *)
Local Abbreviation O8S pc x10 x11 x12 x13 x19 x23 x24 x27 :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 a4 a5 a6 a7 s2 x19 s4 s5 s6 x23 x24 s9
           (Z_to_bv 64 2147450880) x27 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Local Abbreviation O8Q R :=
  (o8_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s4 s5 s6 s9 (Z_to_bv 64 2147450880) t3 t4 t5 t6 F fc m p R).

(* +0x834 .. +0x850 (0x81a98): a1 = a2 | a1 = w, a1 = min (w, s11) (`bltu a1, s11` +0x838, `mv a1, s11` +0x83c),
   s3 = s8 + a1, s7 = s11 - a1, a2 = 1, a0 = s8, `j` to the call of receive. *)
Lemma o8_take_run : forall (R : LCS.lrv) (x10 x11 x12 x13 x19 x23 x24 x27 : word) (base left w : Z),
  bv_unsigned x24 = p + base -> bv_unsigned x27 = left -> 0 <= base -> 0 <= left -> p + base + left <= 2 ^ 63 ->
  Z.lor (bv_unsigned x12) (bv_unsigned x11) = w -> 0 <= w < 2 ^ 17 ->
  LCS.rv_off R = base -> LCS.rv_n R = (if w <? left then w else left) -> LCS.rv_bp R = 1 ->
  LCS.rv_pf R = bv_unsigned x13 -> TOP.fi_off (LCS.rv_c R) = base + LCS.rv_n R ->
  TOP.fi_n (LCS.rv_c R) = left - LCS.rv_n R ->
  ExecF.evtF rsegs RNG (O8Q R) (O8S 0x81a98 x10 x11 x12 x13 x19 x23 x24 x27).
Proof.
  intros R x10 x11 x12 x13 x19 x23 x24 x27 base left w E24 E27 B0 L0 BL EW RW Roff Rn Rbp Rpf Rco Rcn.
  (* +0x834 or a1,a2,a1 *)
  step.
  match goal with |- context [Z.lor (bv_unsigned x12) (bv_unsigned x11)] => rewrite EW end.
  (* +0x838 bltu a1,s11 *)
  step.
  rewrite o8_ltu, (unsigned_lit w) by lia. rewrite E27.
  destruct (Z.ltb_spec w left) as [L|L]; cbv iota.
  - (* +0x840 add s3,s8,a1; +0x844 sub s7,s11,a1; +0x848 li a2,1; +0x84c mv a0,s8; +0x850 j *)
    step. step. step. step. step.
    apply evtF_done. unfold o8_post. do 8 eexists. split; [reflexivity|].
    rewrite Rco, Rcn, Roff, Rbp, <- Rpf, Rn. try rewrite (proj2 (Z.ltb_lt w left) L). cbv iota.
    repeat split; o8_fact.
  - (* +0x83c mv a1,s11, then as above *)
    step. step. step. step. step. step.
    apply evtF_done. unfold o8_post. do 8 eexists. split; [reflexivity|].
    rewrite Rco, Rcn, Roff, Rbp, <- Rpf, Rn. try rewrite (proj2 (Z.ltb_ge w left) L). cbv iota.
    repeat split; o8_fact.
Qed.

(* The instrumented check of the byte at s8 (= A), three times: srli by 3, add s10, `lb` of the shadow byte k,
   `bnez`; when k <> 0 the slow path `andi _, s8, 7` and `blt` back (else the report call). *)
Lemma o8_ck1 : forall (x10 x11 x12 x13 x19 x23 x24 x27 : word) (Q : machine_state -> Prop) (kk : byte) (A : Z),
  bv_unsigned x24 = A -> A < 2 ^ 63 ->
  mrd rsegs m (wa (A / 8 + 2147450880)) = Some kk -> (bv_signed kk = 0 \/ A mod 8 < bv_signed kk) ->
  ExecF.rng RNG (A / 8 + 2147450880) 1 ->
  (forall y10 y11 : word, ExecF.evtF rsegs RNG Q (O8S 0x81960 y10 y11 x12 x13 x19 x23 x24 x27)) ->
  ExecF.evtF rsegs RNG Q (O8S 0x81950 x10 x11 x12 x13 x19 x23 x24 x27).
Proof.
  intros x10 x11 x12 x13 x19 x23 x24 x27 Q kk A EA RA M SK RK CONT.
  pose proof (u64_range x24) as R0.
  (* +0x6ec srli a0,s8,3 *)
  step. gen_shr x24 g G. rewrite EA in G.
  (* +0x6f0 add a0,a0,s10 *)
  step. gen_addi g h H.
  assert (RH : ExecF.rng RNG (bv_unsigned h) 1) by (rewrite H, G; exact RK).
  (* +0x6f4 lb a0,0(a0) *)
  pose proof (rdw0 m h _ _ M ltac:(lia)) as R. step. clear R.
  (* +0x6f8 bnez a0 *)
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed kk) 0) ltac:(lia)); cbn [negb].
    (* +0x1380 andi a1,s8,7; +0x1384 blt a1,a0 *)
    step. step.
    rewrite land7, EA, (lts_low (A mod 8) kk MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    apply CONT.
Qed.

Lemma o8_ck2 : forall (x10 x11 x12 x13 x19 x23 x24 x27 : word) (Q : machine_state -> Prop) (kk : byte) (A : Z),
  bv_unsigned x24 = A -> A < 2 ^ 63 ->
  mrd rsegs m (wa (A / 8 + 2147450880)) = Some kk -> (bv_signed kk = 0 \/ A mod 8 < bv_signed kk) ->
  ExecF.rng RNG (A / 8 + 2147450880) 1 ->
  (forall y11 y12 : word, ExecF.evtF rsegs RNG Q (O8S 0x81980 x10 y11 y12 x13 x19 x23 x24 x27)) ->
  ExecF.evtF rsegs RNG Q (O8S 0x81970 x10 x11 x12 x13 x19 x23 x24 x27).
Proof.
  intros x10 x11 x12 x13 x19 x23 x24 x27 Q kk A EA RA M SK RK CONT.
  pose proof (u64_range x24) as R0.
  (* +0x70c srli a1,s8,3 *)
  step. gen_shr x24 g G. rewrite EA in G.
  (* +0x710 add a1,a1,s10 *)
  step. gen_addi g h H.
  assert (RH : ExecF.rng RNG (bv_unsigned h) 1) by (rewrite H, G; exact RK).
  (* +0x714 lb a1,0(a1) *)
  pose proof (rdw0 m h _ _ M ltac:(lia)) as R. step. clear R.
  (* +0x718 bnez a1 *)
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed kk) 0) ltac:(lia)); cbn [negb].
    (* +0x13c8 andi a2,s8,7; +0x13cc blt a2,a1 *)
    step. step.
    rewrite land7, EA, (lts_low (A mod 8) kk MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    apply CONT.
Qed.

Lemma o8_ck3 : forall (x10 x11 x12 x13 x19 x23 x24 x27 : word) (Q : machine_state -> Prop) (kk : byte) (A : Z),
  bv_unsigned x24 = A -> A < 2 ^ 63 ->
  mrd rsegs m (wa (A / 8 + 2147450880)) = Some kk -> (bv_signed kk = 0 \/ A mod 8 < bv_signed kk) ->
  ExecF.rng RNG (A / 8 + 2147450880) 1 ->
  (forall y10 y12 : word, ExecF.evtF rsegs RNG Q (O8S 0x81fa0 y10 x11 y12 x13 x19 x23 x24 x27)) ->
  ExecF.evtF rsegs RNG Q (O8S 0x81f90 x10 x11 x12 x13 x19 x23 x24 x27).
Proof.
  intros x10 x11 x12 x13 x19 x23 x24 x27 Q kk A EA RA M SK RK CONT.
  pose proof (u64_range x24) as R0.
  (* +0xd2c srli a0,s8,3 *)
  step. gen_shr x24 g G. rewrite EA in G.
  (* +0xd30 add a0,a0,s10 *)
  step. gen_addi g h H.
  assert (RH : ExecF.rng RNG (bv_unsigned h) 1) by (rewrite H, G; exact RK).
  (* +0xd34 lb a0,0(a0) *)
  pose proof (rdw0 m h _ _ M ltac:(lia)) as R. step. clear R.
  (* +0xd38 bnez a0 *)
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed kk) 0) ltac:(lia)); cbn [negb].
    (* +0x1470 andi a2,s8,7; +0x1474 blt a2,a0 *)
    step. step.
    rewrite land7, EA, (lts_low (A mod 8) kk MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    apply CONT.
Qed.

(* The check facts for byte j of the input: its shadow byte and the footprint of that shadow byte. *)
Lemma o8_byte_ck : forall j, 0 <= j < Z.of_nat (length D) ->
  exists kk : byte, mrd rsegs m (wa ((p + j) / 8 + 2147450880)) = Some kk /\
    (bv_signed kk = 0 \/ (p + j) mod 8 < bv_signed kk) /\ ExecF.rng RNG ((p + j) / 8 + 2147450880) 1.
Proof.
  intros j Hj. pose proof AD as (_ & _ & _ & AB).
  destruct (o8_shadow1 m (p + j) (AB j Hj)) as (kk & M & SK). exists kk. split; [exact M|]. split; [exact SK|].
  pose proof (RS j Hj) as R. unfold shadow_addr, ASAN_K in R. exact R.
Qed.

(* byte j of the input, as the load reads it *)
Lemma o8_byte_rd : forall j (w : word), 0 <= j < Z.of_nat (length D) -> bv_unsigned w = p + j ->
  ov_read_bytes rsegs m w 1 = Some [nth (Z.to_nat j) D (Z_to_bv 8 0)].
Proof.
  intros j w Hj E. apply (rdw0 m w (p + j)); [|exact E].
  pose proof (bytes_nth m p D (Z.to_nat j) BA ltac:(lia)) as M. rewrite Z2Nat.id in M by lia. exact M.
Qed.

Lemma o8_byte_rng : forall j (w : word), 0 <= j < Z.of_nat (length D) -> bv_unsigned w = p + j ->
  ExecF.rng RNG (bv_unsigned w) 1.
Proof. intros j w Hj E. rewrite E. eapply rng_sub'; [exact RB | lia]. Qed.

Lemma o8_at8 : forall j, DS.at8 D j = bv_unsigned (nth j D (Z_to_bv 8 0)).
Proof. reflexivity. Qed.

(* The piece, from 0x8194c (+0x6e8) with the cursor { p + o, nn } before the op byte in s9 / s11 and the one after
   it in s8 / s7, to the call of receive. *)
Lemma o8_run : forall (o nn : Z) (x10 x11 x12 x13 x19 x23 x24 x27 : word),
  0 <= o -> 1 <= nn -> o + nn = Z.of_nat (length D) ->
  bv_unsigned s9 = p + o -> bv_unsigned x23 = nn - 1 -> bv_unsigned x24 = p + o + 1 -> bv_unsigned x27 = nn ->
  ExecF.evtF rsegs RNG (O8Q (o8_vals D (TOP.FuzzIn (o + 1) (nn - 1))))
    (O8S 0x8194c x10 x11 x12 x13 x19 x23 x24 x27).
Proof.
  intros o nn x10 x11 x12 x13 x19 x23 x24 x27 Ho Hn HL E9 E23 E24 E27.
  (* +0x6e8 beqz s7 *)
  step. rewrite (o8_eqb_lit x23 0) by lia. rewrite E23.
  destruct (Z.eqb_spec (nn - 1) 0) as [N1|N1]; cbv iota.
  { (* nn = 1: +0x824 li a3,0; +0x828 li s11,0; +0x82c li a1,0; +0x830 li a2,0 *)
    step. step. step. step.
    replace (nn - 1) with (1 - 1) by lia. rewrite o8_v1.
    apply (o8_take_run _ _ _ _ _ _ _ _ _ (o + 1) 0 0); cbn [LCS.rv_off LCS.rv_n LCS.rv_bp LCS.rv_pf LCS.rv_c
      TOP.fi_off TOP.fi_n]; first [reflexivity | lia | o8_fact]. }
  (* +0x6ec .. +0x6f8: the check of the poll flags byte at p + o + 1 *)
  destruct (o8_byte_ck (o + 1) ltac:(lia)) as (k1 & M1 & SK1 & RK1).
  apply (o8_ck1 _ _ _ _ _ _ _ _ _ k1 (p + o + 1) E24 ltac:(lia)); [rewrite <- Z.add_assoc; exact M1 |
    rewrite <- Z.add_assoc; exact SK1 | rewrite <- Z.add_assoc; exact RK1 |].
  intros y10 y11.
  (* +0x6fc lbu a3,0(s8) *)
  pose proof (o8_byte_rd (o + 1) x24 ltac:(lia) ltac:(lia)) as RD1.
  pose proof (o8_byte_rng (o + 1) x24 ltac:(lia) ltac:(lia)) as RG1.
  set (b1 := nth (Z.to_nat (o + 1)) D (Z_to_bv 8 0)) in RD1.
  pose proof (byte_range b1) as Rb1.
  step. clear RD1.
  (* +0x700 addi s8,s9,2 *)
  step. o8_gen s9 s8b U8b.
  (* +0x704 li a1,2; +0x708 beq s11,a1 *)
  step. step.
  rewrite (o8_eqb_lit x27 2) by lia. rewrite E27.
  destruct (Z.eqb_spec nn 2) as [N2|N2]; cbv iota.
  { (* nn = 2: +0x828 li s11,0; +0x82c li a1,0; +0x830 li a2,0 *)
    step. step. step.
    replace (nn - 1) with (2 - 1) by lia. rewrite o8_v2.
    apply (o8_take_run _ _ _ _ _ _ _ _ _ (o + 2) 0 0); cbn [LCS.rv_off LCS.rv_n LCS.rv_bp LCS.rv_pf LCS.rv_c
      TOP.fi_off TOP.fi_n]; first [reflexivity | lia | (rewrite o8_at8; exact (eq_sym (zxb_u b1))) | o8_fact]. }
  (* +0x70c .. +0x718: the check of the u16's low byte at p + o + 2 *)
  destruct (o8_byte_ck (o + 2) ltac:(lia)) as (k2 & M2 & SK2 & RK2).
  apply (o8_ck2 _ _ _ _ _ _ _ _ _ k2 (p + o + 2) ltac:(rewrite U8b, E9; lia) ltac:(lia));
    [rewrite <- Z.add_assoc; exact M2 | rewrite <- Z.add_assoc; exact SK2 | rewrite <- Z.add_assoc; exact RK2 |].
  intros z11 z12.
  (* +0x71c lbu a1,0(s8) *)
  pose proof (o8_byte_rd (o + 2) s8b ltac:(lia) ltac:(rewrite U8b, E9; lia)) as RD2.
  pose proof (o8_byte_rng (o + 2) s8b ltac:(lia) ltac:(rewrite U8b, E9; lia)) as RG2.
  set (b2 := nth (Z.to_nat (o + 2)) D (Z_to_bv 8 0)) in RD2.
  pose proof (byte_range b2) as Rb2.
  step. clear RD2.
  (* +0x720 addi s8,s9,3 *)
  step. o8_gen s9 s8c U8c.
  (* +0x724 li a0,3; +0x728 bne s11,a0 *)
  step. step.
  rewrite (o8_eqb_lit x27 3) by lia. rewrite E27.
  destruct (Z.eqb_spec nn 3) as [N3|N3]; cbn [negb]; cbv iota.
  { (* nn = 3: +0x72c li s11,0; +0x730 j +0x830; +0x830 li a2,0 *)
    step. step. step.
    replace (nn - 1) with (3 - 1) by lia. rewrite o8_v3.
    apply (o8_take_run _ _ _ _ _ _ _ _ _ (o + 3) 0 (bv_unsigned b2)); cbn [LCS.rv_off LCS.rv_n LCS.rv_bp LCS.rv_pf
      LCS.rv_c TOP.fi_off TOP.fi_n];
      first [reflexivity | lia | (rewrite o8_at8; exact (eq_sym (zxb_u b1))) |
             (rewrite (proj2 (Z.ltb_ge (bv_unsigned b2) 0) ltac:(lia)); reflexivity) |
             (cbv delta [zxb]; rewrite (unsigned_lit 0), zxb_u by lia; apply Z.lor_0_l) | o8_fact]. }
  (* +0xd2c .. +0xd38: the check of the u16's high byte at p + o + 3 *)
  destruct (o8_byte_ck (o + 3) ltac:(lia)) as (k3 & M3 & SK3 & RK3).
  apply (o8_ck3 _ _ _ _ _ _ _ _ _ k3 (p + o + 3) ltac:(rewrite U8c, E9; lia) ltac:(lia));
    [rewrite <- Z.add_assoc; exact M3 | rewrite <- Z.add_assoc; exact SK3 | rewrite <- Z.add_assoc; exact RK3 |].
  intros w10 w12.
  (* +0xd3c lbu a2,0(s8) *)
  pose proof (o8_byte_rd (o + 3) s8c ltac:(lia) ltac:(rewrite U8c, E9; lia)) as RD3.
  pose proof (o8_byte_rng (o + 3) s8c ltac:(lia) ltac:(rewrite U8c, E9; lia)) as RG3.
  set (b3 := nth (Z.to_nat (o + 3)) D (Z_to_bv 8 0)) in RD3.
  pose proof (byte_range b3) as Rb3.
  step. clear RD3.
  (* +0xd40 addi s11,s11,-4 *)
  step. o8_gen x27 s11d U11d.
  (* +0xd44 addi s8,s9,4 *)
  step. o8_gen s9 s8d U8d.
  (* +0xd48 slli a2,a2,8; +0xd4c j +0x834 *)
  step. step.
  pose proof (o8_v4 D o nn ltac:(lia)) as V4. cbv zeta in V4. rewrite V4. clear V4.
  rewrite !o8_at8. fold b1 b2 b3.
  apply (o8_take_run _ _ _ _ _ _ _ _ _ (o + 4) (nn - 4) (bv_unsigned b2 + 256 * bv_unsigned b3));
    cbn [LCS.rv_off LCS.rv_n LCS.rv_bp LCS.rv_pf LCS.rv_c TOP.fi_off TOP.fi_n];
    first [reflexivity | lia | exact (o8_lor b2 b3) | exact (eq_sym (zxb_u b1)) | o8_fact].
Qed.

End Run.

End O8Run.

(* ======== the model's bounds of op 8's values ======== *)

Lemma o8_bounds : forall D o nn, 0 <= o -> 1 <= nn ->
  let R := o8_vals D (TOP.FuzzIn (o + 1) (nn - 1)) in
  LCS.rv_bp R = 1 /\ 0 <= LCS.rv_pf R < 256 /\ o < LCS.rv_off R /\ 0 <= LCS.rv_n R /\
  LCS.rv_off R + LCS.rv_n R <= o + nn /\ TOP.fi_off (LCS.rv_c R) = LCS.rv_off R + LCS.rv_n R /\
  TOP.fi_n (LCS.rv_c R) = o + nn - TOP.fi_off (LCS.rv_c R).
Proof.
  intros D o nn Ho Hn R.
  assert (Hc : nn = 1 \/ nn = 2 \/ nn = 3 \/ 4 <= nn) by lia.
  destruct Hc as [E|[E|[E|E]]].
  - subst nn. unfold R. rewrite o8_v1. cbn. lia.
  - subst nn. unfold R. rewrite o8_v2. cbn. pose proof (o8_at8_range D (Z.to_nat (o + 1))). lia.
  - subst nn. unfold R. rewrite o8_v3. cbn. pose proof (o8_at8_range D (Z.to_nat (o + 1))). lia.
  - unfold R. pose proof (o8_v4 D o nn E) as V. cbv zeta in V. rewrite V. clear V. cbn.
    pose proof (o8_at8_range D (Z.to_nat (o + 1))). pose proof (o8_at8_range D (Z.to_nat (o + 2))).
    pose proof (o8_at8_range D (Z.to_nat (o + 3))).
    destruct (Z.ltb_spec (DS.at8 D (Z.to_nat (o + 2)) + 256 * DS.at8 D (Z.to_nat (o + 3))) (nn - 4)); lia.
Qed.

Lemma o8_oc : forall D c, TOP.fi_n c <> 0 -> LCS.lc_oc D c = TOP.FuzzIn (TOP.fi_off c + 1) (TOP.fi_n c - 1).
Proof. intros D c H. unfold LCS.lc_oc. rewrite (o8_u8_some D c H). reflexivity. Qed.

(* ======== the walk: the run carried into SRr at the cut states ======== *)

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
  YK11 YK0s YK0o YK15 YK18 YP09 YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
  YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YO09 YI16 YE00 YE01 YK1b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v AE2k ACfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require W_journalG TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg DgnTransportCgRun.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require LeafCgKit LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require QueueFacts.
Module LST := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.LLVMFuzzerTestOneInput_st.
Module LCK8 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.LeafCgKit.
Module ACells8 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module QF8 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.QueueFacts.

Section seg8. Context {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.

(* AsanCells' addressable (the run's form) from a read range (desk_named_cgW.v dn_addressable). *)
Lemma o8_addressable : forall (W : world segs) mem q n, decode_rd_ok W mem q n -> 0 <= n ->
  ACells8.addressable mem q n.
Proof.
  intros W mem q n (Hv & Hra & Hh & Hm & H0 & H63) Hn.
  unfold amem_range in Hm. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  split; [lia|]. split; [lia|]. split; [unfold ACells8.APPMEM_END; lia|].
  intros i Hi. split.
  - unfold ACells8.app_mem, ACells8.LOWMEM_END, ACells8.HIGHMEM_BEG, ACells8.APPMEM_END. lia.
  - destruct (Hra (q + i) ltac:(lia)) as (s & Hs & Hok).
    destruct (decode_aview_some W mem _ s Hs) as (_ & b & Hb & Eb).
    exists b. split.
    + replace (ACells8.shadow_addr (q + i)) with (shadow_of_addr SHADOW_OFF (q + i))
        by (unfold ACells8.shadow_addr, shadow_of_addr, ACells8.ASAN_K, SHADOW_OFF; lia).
      exact Hb.
    + pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
      unfold saddr_ok in Hok. unfold ACells8.shadow_ok.
      rewrite decode_byte_signed by lia. lia.
Qed.

(* The input's bytes as raw memory (desk_named_cgW.v dn_bytes): visible, so mrd reads what the view reads. *)
Lemma o8_bytes : forall (W : world segs) mem p (pl : list byte),
  decode_rd_ok W mem p (Z.of_nat (length pl)) ->
  garr8 segs (mrestrict (w_H W) mem) p (map (fun b : byte => bv_unsigned b) pl) ->
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.bytes_at
    OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Img0.rsegs mem p pl.
Proof.
  intros W mem p pl (Hv & _ & _ & _ & H0 & H63) G.
  split; [lia|]. split; [lia|].
  intros i Hi.
  assert (Hvis : w_H W (Z_to_bv 64 (p + Z.of_nat i)) = false).
  { destruct (aview segs (w_H W) mem (p + Z.of_nat i)) as [v|] eqn:Ev; [exact (decode_aview_vis W mem _ v Ev)|].
    exfalso. exact (Hv (p + Z.of_nat i) ltac:(lia) Ev). }
  pose proof (garr8_mbyte segs _ _ _ i G ltac:(rewrite length_map; exact Hi)) as MB.
  assert (AV : aview segs (w_H W) mem (p + Z.of_nat i) = Some (bv_unsigned (nth i pl (Z_to_bv 8 0)))).
  { unfold aview. cbv beta. rewrite MB. cbn [option_map]. f_equal.
    rewrite (nth_indep (map (fun b : byte => bv_unsigned b) pl) 0 (bv_unsigned (Z_to_bv 8 0)))
      by (rewrite length_map; exact Hi).
    rewrite (map_nth (fun b : byte => bv_unsigned b)). rewrite Z_to_bv_bv_unsigned. reflexivity. }
  rewrite (decode_aview_mrd W mem _ Hvis) in AV.
  rewrite (nth_error_nth' pl (Z_to_bv 8 0) Hi).
  lazymatch type of AV with option_map _ ?X = _ => destruct X as [b|] end;
    cbn [option_map] in AV; [|discriminate AV].
  injection AV as AV. f_equal. apply bv_eq. exact AV.
Qed.

Lemma o8_unw : forall v, 0 <= v < 2 ^ 64 -> bv_unsigned (w64 v) = v.
Proof.
  intros v R. unfold w64. exact (OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.MState.unsigned_lit v R).
Qed.

Lemma o8_w64 : forall (x : word) v, bv_unsigned x = v -> 0 <= v < 2 ^ 64 -> x = w64 v.
Proof. intros x v E R. apply bv_eq. rewrite (o8_unw v R). exact E. Qed.

Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.LLVMFuzzerTestOneInput_segs.

(* A register of the run's end state: one the run keeps is the cut's (H), one it sets has the value fact F. *)
Local Ltac o8_keep E H :=
  rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ E) by reflexivity; exact H.
Local Ltac o8_set E F :=
  rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ E) by reflexivity; cbv beta;
  apply o8_w64; [exact F | lia].

Theorem lc_op8_ok : @LCS.lc_op8_stmt rc B MT XL RLO RHI.
Proof.
  unfold LCS.lc_op8_stmt. intros HP cx op W' c' HB HA.
  destruct HA as (ly' & S' & regs' & mem' & md' & e & -> & Ho & HL & HTW & (C25 & C27) & (C24 & C23) & G20 & G22).
  pose proof HL as (HCORE & (G18 & G26) & HSP & HFSH & HOPOK & HE & HMET & G21).
  pose proof HOPOK as (HAG & HOPS & HFI & HN0 & HK).
  destruct (lo_c op) as [o nn] eqn:Ec.
  pose proof HFI as (Ho0 & Hn0 & HLD). cbn [TOP.fi_off TOP.fi_n] in Ho0, Hn0, HLD, HN0.
  rewrite (o8_oc (l_pl cx) (TOP.FuzzIn o nn) HN0) in C24, C23. cbn [TOP.fi_off TOP.fi_n] in C24, C23, C25, C27.
  pose proof (@LST.lc_geom rc B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HCORE) as GEO.
  destruct GEO as [HAR _ _ _ _ _ (Hnr & Hnl) HIN _].
  assert (HNP : 0 < l_n cx) by lia.
  assert (RDB : decode_rd_ok W' mem' (l_p cx) (l_n cx)).
  { apply (trans_src_ok_rd B (lp_laws B MT XL RLO RHI HP) ly' S' W' mem' md' (l_p cx) (l_n cx) HAR);
      [|exact HNP].
    left. exists (l_p cx), (l_n cx). split; [exact (HIN HNP)|]. lia. }
  pose proof RDB as (RBv & RBra & RBh & RBm & RB0 & RB63).
  pose proof HCORE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (GIN & _)).
  pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5).
  rewrite Hnl in RDB, RBv, RBra, RB63, HNP.
  change (LCS.lc_cfg cx (LCS.lo_arm 8) regs' mem' md') with (@cfg_at (l_fx cx) segs 0x8194c regs' mem' md').
  eapply decode_run.
  { unfold LCK8.ms_of_regs.
    replace (YK11.getr regs' (Z_to_bv 5 26)) with (Z_to_bv 64 2147450880) by (symmetry; exact G26).
    eapply O8Run.o8_run with (p := l_p cx) (D := l_pl cx) (o := o) (nn := nn).
    all: first
      [ exact (o8_bytes W' mem' (l_p cx) (l_pl cx) RDB GIN)
      | exact (o8_addressable W' mem' _ _ RDB ltac:(lia))
      | exact Ho0
      | (rewrite C25; rewrite o8_unw by lia; lia)
      | (rewrite C23; rewrite o8_unw by lia; lia)
      | (rewrite C24; rewrite o8_unw by lia; lia)
      | (rewrite C27; rewrite o8_unw by lia; lia)
      | (intros i Hi; destruct (RBra (l_p cx + i) ltac:(lia)) as (s & Hs & _);
         pose proof (decode_aview_vis W' mem' _ s Hs) as Hvs;
         assert (SB : kLowMemEnd <= shadow_of_addr SHADOW_OFF (l_p cx + i) < kHighShadowEnd)
           by (exact (shadow_addr_bounds (l_p cx + i) ltac:(unfold amem_range in RBm; lia)));
         assert (Es : ACells8.shadow_addr (l_p cx + i) = shadow_of_addr SHADOW_OFF (l_p cx + i))
           by (unfold ACells8.shadow_addr, shadow_of_addr, ACells8.ASAN_K, SHADOW_OFF; lia);
         rewrite Es; apply decode_rng; [lia | lia|]; intros b Hb;
         replace b with (shadow_of_addr SHADOW_OFF (l_p cx + i)) by lia; exact Hvs)
      | (apply decode_rng; [lia | lia|]; intros b Hb;
         destruct (aview segs (w_H W') mem' b) as [v|] eqn:Ev; [exact (decode_aview_vis W' mem' b v Ev)|];
         exfalso; exact (RBv b Hb Ev))
      | lia
      | lia ]. }
  intros ms' md2 (ms0 & POST & EQV) SBM.
  unfold O8Run.o8_post in POST.
  destruct POST as (x10 & x11 & x12 & x13 & x19 & x23 & x24 & x27 & -> & F10 & F11 & F12 & F13 & F19 & F23).
  rewrite (decode_ms_shape _ _ _ _ EQV).
  apply SRr_ret. unfold LCS.lc_st_recv.
  exists ly', S', (ms_regs ms'), mem', md2, e. cbv zeta.
  rewrite Ec. rewrite (o8_recv_vals _ _ (eq_sym Ho)), (o8_oc (l_pl cx) (TOP.FuzzIn o nn) HN0).
  cbn [TOP.fi_off TOP.fi_n].
  pose proof (o8_bounds (l_pl cx) o nn Ho0 ltac:(lia)) as BD. cbv zeta in BD.
  set (R := o8_vals (l_pl cx) (TOP.FuzzIn (o + 1) (nn - 1))) in *.
  destruct BD as (Bbp & Bpf & Boff & Bn & Bon & Bco & Bcn).
  (* the registers the run keeps are the cut's *)
  pose proof HCORE as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal &
    HFceil & HFpres & HFL & HINP).
  split; [reflexivity|].
  split; [right; symmetry; exact Ho|].
  split.
  { unfold lc_lcore. split.
    { unfold lc_core. split.
      { eapply (W_journalG.ajournal_gx_exec segs B (lp_laws B MT XL RLO RHI HP) decode_segs_low)
          with (memc' := mem') (mdc' := md2) (Wr := fun _ => False).
        - exact (G_HARNESS_gx_ok B (lp_g_unowned B MT XL RLO RHI HP)).
        - exact HJ.
        - intros x _. reflexivity.
        - apply mem_grows_refl.
        - intros x _. reflexivity.
        - exact SBM.
        - intros a Fa. destruct Fa. }
      split; [exact Hfrs|]. split; [exact HlyF|]. split; [exact HPERM|].
      split; [o8_keep EQV Rsp|]. split; [o8_keep EQV R8|]. split; [o8_keep EQV R9|].
      split; [o8_keep EQV Rgp|]. split; [o8_keep EQV Rtp|].
      split; [exact Hsp1|]. split; [exact Hsp1al|]. split; [exact HSAV|]. split; [exact HF4096|].
      split; [exact HFal|]. split; [exact HFceil|]. split; [exact HFpres|]. split; [exact HFL|]. exact HINP. }
    split; [split; [o8_keep EQV G18 |
      rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV) by reflexivity; reflexivity]|].
    split; [exact HSP|]. split; [exact HFSH|]. split; [exact HOPOK|]. split; [exact HE|]. split; [exact HMET|].
    o8_keep EQV G21. }
  split; [exact HTW|].
  split; [o8_set EQV F10|].
  split; [o8_set EQV F11|].
  split; [o8_set EQV F12|].
  split; [o8_set EQV F13|].
  split; [split; [o8_set EQV F19 | o8_set EQV F23]|].
  split; [o8_keep EQV G20 | o8_keep EQV G22].
Qed.

End seg8.
