(* rp_fwd_class of fuzz_wire.asan-ubsan (entry 0x80d9c, 0x144 bytes):
     0x80d9c `addi sp, sp, -0x10`, 0x80da0 `sd ra, 8(sp)`;
     0x80da4 `li a3, 18`, 0x80da8 `bltu a1, a3, 0x80e2c`: n < 18 goes to 0x80e2c `li a0, 0`;
     0x80dac `beqz a0, 0x80e94`, 0x80db0 `li a1, -12`, 0x80db4 `bgeu a0, a1, 0x80e94` (UBSan; `unimp` at 0x80e94):
       a0 <> 0 and f + 18 <= APPMEM_END make both fall through;
     0x80db8 `auipc a1, 0x18`, 0x80dbc `ld a1, -0x540(a1)` (the GOT word 0x98878), 0x80dc0 `ld a3, 0(a1)` (the shadow
       base in 0xa07f8);
     0x80dc4 .. 0x80dd4: the shadow byte of f + 12 into a4, `bnez a4, 0x80e98`; 0x80e98 `andi a5, a1, 7`, 0x80e9c
       `blt a5, a4, 0x80dd8` returns (ck_80dd4), so the report call at 0x80ea4 is never reached;
     0x80dd8 `lbu a1, 0(a1)` (f[12]), 0x80ddc `li a4, 0x88`, 0x80de0 `bne a1, a4, 0x80e2c`;
     0x80de4 `li a1, -14`, 0x80de8 `bltu a1, a0, 0x80e94` (UBSan): falls through as above;
     0x80dec .. 0x80dfc: the shadow byte of f + 13 into a4, `bnez a4, 0x80ea8`; its check 0x80ea8 / 0x80eac returns to
       0x80e00 (ck_80dfc); 0x80e00 `lbu a1, 0(a1)` (f[13]), 0x80e04 `li a4, 0x19`, 0x80e08 `bne a1, a4, 0x80e2c`;
     0x80e0c `beqz a2, 0x80e3c` (bcast_only = 0 skips f[0]);
     0x80e10 .. 0x80e1c: the shadow byte of f into a1, `bnez a1, 0x80eb8`; its check 0x80eb8 / 0x80ebc returns to
       0x80e20 (ck_80e1c); 0x80e20 `lbu a1, 0(a0)` (f[0]), 0x80e24 `li a2, 0xff`, 0x80e28 `beq a1, a2, 0x80e3c`,
       else 0x80e2c `li a0, 0`, 0x80e30 `ld ra, 8(sp)`, 0x80e34 `addi sp, sp, 0x10`, 0x80e38 `ret`;
     0x80e3c `li a1, -16`, 0x80e40 `bgeu a0, a1, 0x80e94` (UBSan): falls through;
     0x80e44 .. 0x80e54: the shadow byte of f + 16 into a2, `bnez a2, 0x80ec4`; its check 0x80ec4 / 0x80ec8 returns to
       0x80e58 (ck_80e54); 0x80e58 `lbu a1, 0(a1)` (f[16]), 0x80e5c `bnez a1, 0x80e84` (0x80e84 `li a0, 2`; `j 0x80e30`);
     0x80e60 `li a1, -18`, 0x80e64 `bltu a1, a0, 0x80e94` (UBSan): falls through;
     0x80e68 `addi a0, a0, 17`, 0x80e6c .. 0x80e78: the shadow byte of f + 17 into a1, `bnez a1, 0x80ed4`; its check
       0x80ed4 / 0x80ed8 returns to 0x80e7c (ck_80e78); 0x80e7c `lbu a0, 0(a0)` (f[17]), 0x80e80 `beqz a0, 0x80e8c`
       (0x80e8c `li a0, 1`; `j 0x80e30`), else 0x80e84 `li a0, 2`; `j 0x80e30`. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import AsanKA AsanKAProof rp_fwd_class_F_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_fwd_class_c.
Import ListNotations.
Open Scope Z_scope.
Module PFC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_fwd_class_c.

(* ---- helpers ---- *)

(* the one-byte window of the shadow range of [p, p + n) at the shadow byte of a (uci's rng_one_shadow) *)
Lemma rfc_shadow_one : forall RNG p n a,
  ExecF.rng RNG (shadow_addr p) (shadow_addr (p + n - 1) - shadow_addr p + 1) ->
  p <= a < p + n -> ExecF.rng RNG (shadow_addr a) 1.
Proof.
  intros RNG p n a H Ha. unfold shadow_addr in *.
  assert (L1 : p / 8 <= a / 8) by (apply Z.div_le_mono; lia).
  assert (L2 : a / 8 <= (p + n - 1) / 8) by (apply Z.div_le_mono; lia).
  eapply ExecF.rng_sub; [exact H | lia | lia].
Qed.

(* the shadow check of a one-byte access at X passes on shadow byte k *)
Definition shok1 (k : byte) (X : Z) : Prop := bv_signed k = 0 \/ X mod 8 < bv_signed k.

Lemma shok1_of : forall (k : byte) X, shadow_ok X (bv_signed k) -> shok1 k X.
Proof. intros k X [C|[C _]]; [left | right]; exact C. Qed.

(* ---- tactics ---- *)

Local Ltac zc H := zify_cond H; rewrite ?zxb_u in H.

(* lib/U/Prog/rp_fwd_class.v bfacts *)
Local Ltac bfacts :=
  repeat match goal with
  | H : ?x = ?c |- context [Z.eqb ?x ?c] => rewrite (proj2 (Z.eqb_eq x c) H)
  | H : ?x <> ?c |- context [Z.eqb ?x ?c] => rewrite (proj2 (Z.eqb_neq x c) H)
  | H : ?x < ?c |- context [Z.ltb ?x ?c] => rewrite (proj2 (Z.ltb_lt x c) H)
  | H : ?c <= ?x |- context [Z.ltb ?x ?c] => rewrite (proj2 (Z.ltb_ge x c) H)
  end.

(* the shadow check from its `bnez` back to the access: k = 0 falls through, else `andi`; `blt` returns *)
Local Ltac chk1 HX C K :=
  unfold shok1 in C;
  lazymatch type of C with bv_signed ?k = 0 \/ _ =>
  lazymatch type of HX with bv_unsigned _ = ?X =>
    let MB := fresh "MB" in
    pose proof (Z.mod_pos_bound X 8 ltac:(lia)) as MB;
    step; rewrite sxb_eq0; destruct C as [C|C];
    [ rewrite (proj2 (Z.eqb_eq _ _) C); cbn [negb]; apply K
    | rewrite (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb];
      step; step;
      rewrite land7, HX, (lts_low (X mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); apply K ]
  end end.

Section Checks.
Variables (RNG : footprint) (Q : machine_state -> Prop)
  (ra sp1 gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32).

(* the states of the walk: sp1 is the frame's sp; r0 .. r5 are a0 .. a5 *)
Local Abbreviation ST pc m r0 r1 r2 r3 r4 r5 :=
  (MS (mkR ra sp1 gp tp t0 t1 t2 s0 s1 r0 r1 r2 r3 r4 r5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

(* 0x80dd4: `bnez a4` on the shadow byte of f + 12 (in a1); its check (`andi a5, a1, 7`; `blt a5, a4`) returns to
   0x80dd8: the `jal __asan_report_load1` at 0x80ea4 is not reached. *)
Lemma ck_80dd4 : forall m (r0 r1 r2 r3 r5 : word) (k : byte) X,
  bv_unsigned r1 = X -> shok1 k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x80dd8 m r0 r1 r2 r3 (sxb k) v)) ->
  evtF rsegs RNG Q (ST 0x80dd4 m r0 r1 r2 r3 (sxb k) r5).
Proof. intros m r0 r1 r2 r3 r5 k X HX C K. chk1 HX C K. Qed.

(* 0x80dfc: `bnez a4` on the shadow byte of f + 13 (in a1); its check (`andi a5, a1, 7`; `blt a5, a4`) returns to
   0x80e00: the `jal __asan_report_load1` at 0x80eb4 is not reached. *)
Lemma ck_80dfc : forall m (r0 r1 r2 r3 r5 : word) (k : byte) X,
  bv_unsigned r1 = X -> shok1 k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x80e00 m r0 r1 r2 r3 (sxb k) v)) ->
  evtF rsegs RNG Q (ST 0x80dfc m r0 r1 r2 r3 (sxb k) r5).
Proof. intros m r0 r1 r2 r3 r5 k X HX C K. chk1 HX C K. Qed.

(* 0x80e1c: `bnez a1` on the shadow byte of f (in a0); its check (`andi a2, a0, 7`; `blt a2, a1`) returns to
   0x80e20: the `jal __asan_report_load1` at 0x80ec0 is not reached. *)
Lemma ck_80e1c : forall m (r0 r2 r3 r4 r5 : word) (k : byte) X,
  bv_unsigned r0 = X -> shok1 k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x80e20 m r0 (sxb k) v r3 r4 r5)) ->
  evtF rsegs RNG Q (ST 0x80e1c m r0 (sxb k) r2 r3 r4 r5).
Proof. intros m r0 r2 r3 r4 r5 k X HX C K. chk1 HX C K. Qed.

(* 0x80e54: `bnez a2` on the shadow byte of f + 16 (in a1); its check (`andi a4, a1, 7`; `blt a4, a2`) returns to
   0x80e58: the `jal __asan_report_load1` at 0x80ed0 is not reached. *)
Lemma ck_80e54 : forall m (r0 r1 r3 r4 r5 : word) (k : byte) X,
  bv_unsigned r1 = X -> shok1 k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x80e58 m r0 r1 (sxb k) r3 v r5)) ->
  evtF rsegs RNG Q (ST 0x80e54 m r0 r1 (sxb k) r3 r4 r5).
Proof. intros m r0 r1 r3 r4 r5 k X HX C K. chk1 HX C K. Qed.

(* 0x80e78: `bnez a1` on the shadow byte of f + 17 (in a0); its check (`andi a2, a0, 7`; `blt a2, a1`) returns to
   0x80e7c: the `jal __asan_report_load1` at 0x80edc is not reached. *)
Lemma ck_80e78 : forall m (r0 r2 r3 r4 r5 : word) (k : byte) X,
  bv_unsigned r0 = X -> shok1 k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x80e7c m r0 (sxb k) v r3 r4 r5)) ->
  evtF rsegs RNG Q (ST 0x80e78 m r0 (sxb k) r2 r3 r4 r5).
Proof. intros m r0 r2 r3 r4 r5 k X HX C K. chk1 HX C K. Qed.

End Checks.

(* ---- the contract ---- *)

(* an exit: the model evaluated on the branch facts of the path, the post's registers and the frame released *)
Local Ltac fin :=
  apply evtF_done; unfold PFC.fwd_class_result, PFC.fwd_byte;
  repeat match goal with Eb : ?b = nth ?i ?l ?d |- context [nth ?i ?l ?d] => rewrite <- Eb end;
  bfacts;
  do 6 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|];
  lazymatch goal with FR : rw_cells _ _ _ _, ST : stk _ _ _ _ |- stk _ _ _ (bv_unsigned ?s) =>
    release_frame FR ST (bv_unsigned s); exact ST end.

Theorem rp_fwd_class_holds_F : rp_fwd_class_contract_F.
Proof.
  unfold rp_fwd_class_contract_F, RP_FWD_CLASS, RP_FWD_CLASS_FRAME, RP_FWD_CLASS_SPAN.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs lo
    ST HLO HB RFR RGC RCK RBUF RSH.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0. change (2 ^ Z.of_N 64) with (2^64) in Ra0.
  carve_frame 16%nat ST.
  (* addi sp, sp, -16; sd ra, 8(sp); li a3, 18; bltu a1, a3 *)
  step. step. step. step. if_cases HL.
  { (* n < 18: li a0, 0; ld ra; addi sp; ret *)
    zc HL. do 4 step. fin. }
  zc HL.
  destruct (HB HL) as (NZ & LEN & BA & D0 & APS1 & APS2 & CELLS & DG & DS & ADR).
  specialize (RGC HL). specialize (RCK HL). specialize (RBUF HL). specialize (RSH HL).
  clear HB.
  destruct CELLS as (CK & GCK & _).
  destruct ADR as (P0 & N0 & PE & AB).
  (* the five bytes it reads, f + 0, 12, 13, 16, 17: each is application memory and its shadow byte passes *)
  destruct (AB 0 ltac:(lia)) as (APP0 & k0 & MK0 & SK0).
  destruct (AB 12 ltac:(lia)) as (APP12 & k12 & MK12 & SK12).
  destruct (AB 13 ltac:(lia)) as (APP13 & k13 & MK13 & SK13).
  destruct (AB 16 ltac:(lia)) as (APP16 & k16 & MK16 & SK16).
  destruct (AB 17 ltac:(lia)) as (APP17 & k17 & MK17 & SK17).
  clear AB.
  rewrite Z.add_0_r in APP0, MK0, SK0.
  apply shok1_of in SK0, SK12, SK13, SK16, SK17.
  pose proof (rfc_shadow_one RNG _ 18 (bv_unsigned a0) RSH ltac:(lia)) as RS0.
  pose proof (rfc_shadow_one RNG _ 18 (bv_unsigned a0 + 12) RSH ltac:(lia)) as RS12.
  pose proof (rfc_shadow_one RNG _ 18 (bv_unsigned a0 + 13) RSH ltac:(lia)) as RS13.
  pose proof (rfc_shadow_one RNG _ 18 (bv_unsigned a0 + 16) RSH ltac:(lia)) as RS16.
  pose proof (rfc_shadow_one RNG _ 18 (bv_unsigned a0 + 17) RSH ltac:(lia)) as RS17.
  clear RSH.
  unfold off_stk, GOT_CELL_K, CELL_K, shadow_addr, ASAN_K in *.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in APP0, APP12, APP13, APP16, APP17, APS1, APS2, PE.
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  (* the cells, the shadow bytes and the frame bytes, read in the memory after the store of ra *)
  pose proof (bytes_tp m m0 _ _ 624760 (le8 (wa 657400)) MU1 ltac:(rewrite length_le8; lia) GCK) as GOT0.
  pose proof (bytes_tp m m0 _ _ 657400 (le8 (wa 2147450880)) MU1 ltac:(rewrite length_le8; lia) CK) as SV0.
  assert (RDG : ov_read_bytes rsegs m0 (wa 624760) 8 = Some (le8 (wa 657400))).
  { replace (wa 624760) with (wa (624760 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 624760 _ 0 8 GOT0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  assert (RDS : ov_read_bytes rsegs m0 (wa 657400) 8 = Some (le8 (wa 2147450880))).
  { replace (wa 657400) with (wa (657400 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 657400 _ 0 8 SV0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 / 8 + 2147450880) _ MU1
    ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK0) as M0.
  pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 12) / 8 + 2147450880) _ MU1
    ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK12) as M12.
  pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 13) / 8 + 2147450880) _ MU1
    ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK13) as M13.
  pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 16) / 8 + 2147450880) _ MU1
    ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK16) as M16.
  pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 17) / 8 + 2147450880) _ MU1
    ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK17) as M17.
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 0) _ MU1 ltac:(lia) ltac:(lia)
    (bytes_nth m _ bs 0 BA ltac:(lia))) as F0.
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 12) _ MU1 ltac:(lia) ltac:(lia)
    (bytes_nth m _ bs 12 BA ltac:(lia))) as F12.
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 13) _ MU1 ltac:(lia) ltac:(lia)
    (bytes_nth m _ bs 13 BA ltac:(lia))) as F13.
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 16) _ MU1 ltac:(lia) ltac:(lia)
    (bytes_nth m _ bs 16 BA ltac:(lia))) as F16.
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 17) _ MU1 ltac:(lia) ltac:(lia)
    (bytes_nth m _ bs 17 BA ltac:(lia))) as F17.
  change (Z.of_nat 0) with 0 in F0. change (Z.of_nat 12) with 12 in F12. change (Z.of_nat 13) with 13 in F13.
  change (Z.of_nat 16) with 16 in F16. change (Z.of_nat 17) with 17 in F17.
  remember (nth 0 bs (Z_to_bv 8 0)) as b0 eqn:E0.
  remember (nth 12 bs (Z_to_bv 8 0)) as b12 eqn:E12.
  remember (nth 13 bs (Z_to_bv 8 0)) as b13 eqn:E13.
  remember (nth 16 bs (Z_to_bv 8 0)) as b16 eqn:E16.
  remember (nth 17 bs (Z_to_bv 8 0)) as b17 eqn:E17.
  assert (RW0 : ExecF.rng RNG (bv_unsigned a0) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RBUF); lia).
  (* the UBSan checks of f: `beqz a0` and `bgeu a0, a1` (a1 = -12) fall through *)
  step. if_false.
  step. step. if_false.
  (* the shadow base through its GOT word *)
  step. step. step.
  (* f + 12: its shadow byte and check *)
  step. gen_addi a0 w12 U12.
  assert (RW12 : ExecF.rng RNG (bv_unsigned w12) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RBUF); lia).
  step. gen_shr w12 g12 G12. rewrite U12 in G12.
  step. gen_addi g12 h12 H12.
  assert (RH12 : ExecF.rng RNG (bv_unsigned h12) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RS12); lia).
  pose proof (rdw0 m0 h12 _ _ M12 ltac:(lia)) as R. step. clear R.
  eapply ck_80dd4 with (X := bv_unsigned a0 + 12); [exact U12 | exact SK12 | intros v12].
  (* f[12]; li a4, 0x88; bne a1, a4 *)
  pose proof (rdw0 m0 w12 _ _ F12 ltac:(lia)) as R. step. clear R.
  step. step. if_cases HC12; zc HC12.
  { (* f[12] <> 0x88: li a0, 0; ld ra; addi sp; ret *)
    do 4 step. fin. }
  (* the UBSan check `bltu a1, a0` (a1 = -14) falls through *)
  step. step. if_false.
  (* f + 13: its shadow byte and check *)
  step. gen_addi a0 w13 U13.
  assert (RW13 : ExecF.rng RNG (bv_unsigned w13) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RBUF); lia).
  step. gen_shr w13 g13 G13. rewrite U13 in G13.
  step. gen_addi g13 h13 H13.
  assert (RH13 : ExecF.rng RNG (bv_unsigned h13) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RS13); lia).
  pose proof (rdw0 m0 h13 _ _ M13 ltac:(lia)) as R. step. clear R.
  eapply ck_80dfc with (X := bv_unsigned a0 + 13); [exact U13 | exact SK13 | intros v13].
  (* f[13]; li a4, 0x19; bne a1, a4 *)
  pose proof (rdw0 m0 w13 _ _ F13 ltac:(lia)) as R. step. clear R.
  step. step. if_cases HC13; zc HC13.
  { (* f[13] <> 0x19: li a0, 0; ld ra; addi sp; ret *)
    do 4 step. fin. }
  (* beqz a2: bcast_only = 0 skips f[0] *)
  step. if_cases HBC; zc HBC.
  (* bcast_only <> 0 (goal 2): f: its shadow byte and check *)
  2: step; gen_shr a0 g0 G0.
  2: step; gen_addi g0 h0 H0.
  2: assert (RH0 : ExecF.rng RNG (bv_unsigned h0) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RS0); lia).
  2: pose proof (rdw0 m0 h0 _ _ M0 ltac:(lia)) as R; step; clear R.
  2: eapply ck_80e1c with (X := bv_unsigned a0); [reflexivity | exact SK0 | intros v0].
  (* f[0]; li a2, 0xff; beq a1, a2 *)
  2: pose proof (rdw0 m0 a0 _ _ F0 ltac:(lia)) as R; step; clear R.
  2: step; step; if_cases HC0; zc HC0.
  (* f[0] <> 0xff (goal 3): li a0, 0; ld ra; addi sp; ret *)
  3: do 4 step; fin.
  (* 0x80e3c, from both paths: is_audio(f) *)
  all: step; step; if_false.
  (* f + 16: its shadow byte and check *)
  all: step; gen_addi a0 w16 U16.
  all: assert (RW16 : ExecF.rng RNG (bv_unsigned w16) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RBUF); lia).
  all: step; gen_shr w16 g16 G16; rewrite U16 in G16.
  all: step; gen_addi g16 h16 H16.
  all: assert (RH16 : ExecF.rng RNG (bv_unsigned h16) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RS16); lia).
  all: pose proof (rdw0 m0 h16 _ _ M16 ltac:(lia)) as R; step; clear R.
  all: eapply ck_80e54 with (X := bv_unsigned a0 + 16); [exact U16 | exact SK16 | intros v16].
  (* f[16]; bnez a1 *)
  all: pose proof (rdw0 m0 w16 _ _ F16 ltac:(lia)) as R; step; clear R.
  all: step; if_cases HC16; zc HC16.
  (* f[16] <> 0: li a0, 2; j; ld ra; addi sp; ret *)
  1, 3: do 5 step; fin.
  (* the UBSan check `bltu a1, a0` (a1 = -18) falls through *)
  all: step; step; if_false.
  (* f + 17: addi a0, a0, 17; its shadow byte and check *)
  all: step; gen_addi a0 w17 U17.
  all: assert (RW17 : ExecF.rng RNG (bv_unsigned w17) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RBUF); lia).
  all: step; gen_shr w17 g17 G17; rewrite U17 in G17.
  all: step; gen_addi g17 h17 H17.
  all: assert (RH17 : ExecF.rng RNG (bv_unsigned h17) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RS17); lia).
  all: pose proof (rdw0 m0 h17 _ _ M17 ltac:(lia)) as R; step; clear R.
  all: eapply ck_80e78 with (X := bv_unsigned a0 + 17); [exact U17 | exact SK17 | intros v17].
  (* f[17]; beqz a0: li a0, 1 or li a0, 2; j; ld ra; addi sp; ret *)
  all: pose proof (rdw0 m0 w17 _ _ F17 ltac:(lia)) as R; step; clear R.
  all: step; if_cases HC17; zc HC17.
  all: do 5 step; fin.
Qed.
