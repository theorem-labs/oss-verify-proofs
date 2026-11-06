(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/B/Prog/is_tagged_reac_F.v, with its module paths, module names and numbers changed; 167 of its 236 lines of code are new or changed and 123 lines of the source are left out. *)
(* rp_ds_accept_FW: the footprint walk of reac-repacer/fuzz_wire's rp_ds_accept in image A (fuzz_wire.asan),
   against the frozen lib/A/Prog/rp_ds_accept_F_c.v rp_ds_accept_contract_F (so it proves lib/A/Prog/rp_ds_accept_cg.v
   wire_rp_ds_accept_holds_stmt). The footprint idioms are libreac/fuzz_decode's released walk
   proofs/libreac/fuzz_decode/lib/A/Prog/reac_frame_is_reac_F.v (origin/ossv/recipes 88154566652a: StepF's step, one
   rng fact per access, the frame carved and released, the shadow base through its GOT word, the shadow loads read
   from the `addressable` premise); the branch order and the closing of each exit by evaluating ds_accept_result on
   the branch facts are this unit's released plain walk lib/Prog/rp_ds_accept.v; the one lemma per shadow check with
   its continuation and the Section's state abbreviation are reac-repacer/fuzz_uci's lib/A/Prog/rp_hot_clamp_FW.v
   (origin/ossv/recipes 0295462466b2). *)
(* rp_ds_accept of fuzz_wire.asan (entry 0x8106c, 0xfc bytes, 63 words):
     0x8106c `addi sp, sp, -0x10`, 0x81070 `sd ra, 8(sp)`;
     0x81074 `li a2, 18`, 0x81078 `bltu a1, a2, 0x810f4`: n < 18 goes to 0x810f4 `li a0, 0`;
     0x8107c `auipc a1, 0x17`, 0x81080 `ld a1, 0x76c(a1)` (the GOT word 0x987e8), 0x81084 `ld a2, 0(a1)` (the shadow
       base in 0xa0778);
     0x81088 .. 0x81094: the shadow byte of f + 12 into a3, 0x81098 `bnez a3, 0x8112c`; 0x8112c `andi a4, a1, 7`,
       0x81130 `blt a4, a3, 0x8109c` returns (rda_ck_81098), so the report call at 0x81138 is never reached;
     0x8109c `lbu a1, 0(a1)` (f[12]), 0x810a0 `li a3, 0x88`, 0x810a4 `beq a1, a3, 0x81104`
       (0x81104 `li a1, 13`, then the tail at 0x81108 reads f[13]);
     0x810a8 `li a3, 0x81`, 0x810ac `bne a1, a3, 0x810f4`;
     0x810b0 .. 0x810bc: the shadow byte of f + 13 into a3, 0x810c0 `bnez a3, 0x81148`; its check 0x81148 / 0x8114c
       returns to 0x810c4 (rda_ck_810c0); 0x810c4 `lbu a1, 0(a1)` (f[13]), 0x810c8 `bnez a1, 0x810f4`;
     0x810cc .. 0x810d8: the shadow byte of f + 16 into a3, 0x810dc `bnez a3, 0x81158`; its check 0x81158 / 0x8115c
       returns to 0x810e0 (rda_ck_810dc); 0x810e0 `lbu a1, 0(a1)` (f[16]), 0x810e4 `li a3, 0x88`,
       0x810e8 `bne a1, a3, 0x810f4`;
     0x810ec `li a1, 17`, 0x810f0 `j 0x81108` (the tail reads f[17]);
     0x810f4 `li a0, 0`, 0x810f8 `ld ra, 8(sp)`, 0x810fc `addi sp, sp, 0x10`, 0x81100 `ret`;
     the tail (rda_tail_81108), entered with a1 = 13 or 17: 0x81108 `add a0, a0, a1`; 0x8110c .. 0x81114: the shadow
       byte of f + a1 into a1, 0x81118 `bnez a1, 0x8113c`; its check 0x8113c `andi a2, a0, 7`, 0x81140
       `blt a2, a1, 0x8111c` returns to 0x8111c (rda_ck_81118), so the report call at 0x81144 is never reached;
       0x8111c `lbu a0, 0(a0)`, 0x81120 `addi a0, a0, -25`, 0x81124 `seqz a0, a0`, 0x81128 `j 0x810f8`.
   The report calls at 0x81138, 0x81144, 0x81154 and 0x81164 are refuted by `addressable m (f + 12) 6`: each shadow
   byte k it gives has k = 0 or (a mod 8 < k <= 7). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import AsanKA AsanKAProof rp_ds_accept_F_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_ds_accept_c.
Import ListNotations.
Open Scope Z_scope.
Module PDA := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_ds_accept_c.

(* ---- helpers ---- *)

(* the one-byte window of the shadow range of [p, p + n) at the shadow byte of a *)
Lemma rda_shadow_one : forall RNG p n a,
  ExecF.rng RNG (shadow_addr p) (shadow_addr (p + n - 1) - shadow_addr p + 1) ->
  p <= a < p + n -> ExecF.rng RNG (shadow_addr a) 1.
Proof.
  intros RNG p n a H Ha. unfold shadow_addr in *.
  assert (L1 : p / 8 <= a / 8) by (apply Z.div_le_mono; lia).
  assert (L2 : a / 8 <= (p + n - 1) / 8) by (apply Z.div_le_mono; lia).
  eapply ExecF.rng_sub; [exact H | lia | lia].
Qed.

(* the shadow check of a one-byte access at X passes on shadow byte k *)
Definition rda_shok1 (k : byte) (X : Z) : Prop := bv_signed k = 0 \/ X mod 8 < bv_signed k.

Lemma rda_shok1_of : forall (k : byte) X, shadow_ok X (bv_signed k) -> rda_shok1 k X.
Proof. intros k X [C|[C _]]; [left | right]; exact C. Qed.

(* the tail's `addi a0, a0, -25`; `seqz a0, a0` on the byte b (lib/Prog/rp_ds_accept.v seqz_byte) *)
Lemma rda_seqz_byte : forall b : byte,
  v_sltiu (Z_to_bv 64 (bv_unsigned (zxb b) + -25)) 1 = Z_to_bv 64 (if bv_unsigned b =? 25 then 1 else 0).
Proof.
  intros b. unfold v_sltiu, zxb. rewrite zxb_u. pose proof (byte_range b) as X.
  destruct (Z.eq_dec (bv_unsigned b) 25) as [E|E].
  - rewrite E. vm_compute. reflexivity.
  - rewrite (proj2 (Z.eqb_neq _ _) E).
    rewrite unsigned_lit_wrap. change (bv_wrap 64 1) with 1.
    replace ((bv_unsigned b + -25) mod 2 ^ 64 <? 1) with false; [reflexivity|].
    symmetry. apply Z.ltb_ge. Z.div_mod_to_equations. lia.
Qed.

(* ---- tactics ---- *)

Local Ltac zc H := zify_cond H; rewrite ?zxb_u in H.

(* lib/Prog/rp_ds_accept.v bfacts *)
Local Ltac bfacts :=
  repeat match goal with
  | H : ?x = ?c |- context [Z.eqb ?x ?c] => rewrite (proj2 (Z.eqb_eq x c) H)
  | H : ?x <> ?c |- context [Z.eqb ?x ?c] => rewrite (proj2 (Z.eqb_neq x c) H)
  | H : ?x < ?c |- context [Z.ltb ?x ?c] => rewrite (proj2 (Z.ltb_lt x c) H)
  | H : ?c <= ?x |- context [Z.ltb ?x ?c] => rewrite (proj2 (Z.ltb_ge x c) H)
  end.

(* the shadow check from its `bnez` back to the access: k = 0 falls through, else `andi`; `blt` returns *)
Local Ltac chk1 HX C K :=
  unfold rda_shok1 in C;
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

Section Walk.
Variables (RNG : footprint) (Q : machine_state -> Prop)
  (ra sp1 gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32).

(* the states of the walk: sp1 is the frame's sp; r0 .. r4 are a0 .. a4 *)
Local Abbreviation ST pc m r0 r1 r2 r3 r4 :=
  (MS (mkR ra sp1 gp tp t0 t1 t2 s0 s1 r0 r1 r2 r3 r4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

(* 0x81098: `bnez a3` on the shadow byte of f + 12 (in a1); its check (`andi a4, a1, 7`; `blt a4, a3`) returns to
   0x8109c: the `jal __asan_report_load1` at 0x81138 is not reached. *)
Lemma rda_ck_81098 : forall m (r0 r1 r2 r4 : word) (k : byte) X,
  bv_unsigned r1 = X -> rda_shok1 k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x8109c m r0 r1 r2 (sxb k) v)) ->
  evtF rsegs RNG Q (ST 0x81098 m r0 r1 r2 (sxb k) r4).
Proof. intros m r0 r1 r2 r4 k X HX C K. chk1 HX C K. Qed.

(* 0x810c0: `bnez a3` on the shadow byte of f + 13 (in a1); its check (`andi a4, a1, 7`; `blt a4, a3`) returns to
   0x810c4: the `jal __asan_report_load1` at 0x81154 is not reached. *)
Lemma rda_ck_810c0 : forall m (r0 r1 r2 r4 : word) (k : byte) X,
  bv_unsigned r1 = X -> rda_shok1 k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x810c4 m r0 r1 r2 (sxb k) v)) ->
  evtF rsegs RNG Q (ST 0x810c0 m r0 r1 r2 (sxb k) r4).
Proof. intros m r0 r1 r2 r4 k X HX C K. chk1 HX C K. Qed.

(* 0x810dc: `bnez a3` on the shadow byte of f + 16 (in a1); its check (`andi a4, a1, 7`; `blt a4, a3`) returns to
   0x810e0: the `jal __asan_report_load1` at 0x81164 is not reached. *)
Lemma rda_ck_810dc : forall m (r0 r1 r2 r4 : word) (k : byte) X,
  bv_unsigned r1 = X -> rda_shok1 k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x810e0 m r0 r1 r2 (sxb k) v)) ->
  evtF rsegs RNG Q (ST 0x810dc m r0 r1 r2 (sxb k) r4).
Proof. intros m r0 r1 r2 r4 k X HX C K. chk1 HX C K. Qed.

(* 0x81118: `bnez a1` on the shadow byte of f + a1 (the address in a0); its check (`andi a2, a0, 7`;
   `blt a2, a1`) returns to 0x8111c: the `jal __asan_report_load1` at 0x81144 is not reached. *)
Lemma rda_ck_81118 : forall m (r0 r2 r3 r4 : word) (k : byte) X,
  bv_unsigned r0 = X -> rda_shok1 k X ->
  (forall v : word, evtF rsegs RNG Q (ST 0x8111c m r0 (sxb k) v r3 r4)) ->
  evtF rsegs RNG Q (ST 0x81118 m r0 (sxb k) r2 r3 r4).
Proof. intros m r0 r2 r3 r4 k X HX C K. chk1 HX C K. Qed.

(* 0x81108, the shared tail, entered with a1 = off (13 from 0x81104, 17 from 0x810f0) and a2 = the shadow base:
   it reads the byte b at f + off after its shadow check and continues at 0x810f8 with a0 = (b = 0x19). *)
Lemma rda_tail_81108 : forall m (r0 r2 r3 r4 : word) (k b : byte) off,
  bv_unsigned r2 = 2147450880 ->
  0 <= bv_unsigned r0 + off < 2^60 ->
  ExecF.rng RNG (bv_unsigned r0 + off) 1 ->
  ExecF.rng RNG ((bv_unsigned r0 + off) / 8 + 2147450880) 1 ->
  mrd rsegs m (wa ((bv_unsigned r0 + off) / 8 + 2147450880)) = Some k ->
  rda_shok1 k (bv_unsigned r0 + off) ->
  mrd rsegs m (wa (bv_unsigned r0 + off)) = Some b ->
  (forall v : word, evtF rsegs RNG Q
     (ST 0x810f8 m (Z_to_bv 64 (if bv_unsigned b =? 25 then 1 else 0)) (sxb k) v r3 r4)) ->
  evtF rsegs RNG Q (ST 0x81108 m r0 (Z_to_bv 64 off) r2 r3 r4).
Proof.
  intros m r0 r2 r3 r4 k b off HR2 HX RW RS MK SK MB K.
  (* add a0, a0, a1 *)
  step. gen_addi r0 w U.
  assert (RW' : ExecF.rng RNG (bv_unsigned w) 1) by (rewrite U; exact RW).
  (* srli a1, a0, 3 *)
  step. gen_shr w g G. rewrite U in G.
  (* add a1, a1, a2 *)
  step. rewrite HR2. gen_addi g h H.
  assert (RH : ExecF.rng RNG (bv_unsigned h) 1) by (rewrite H, G; exact RS).
  (* lb a1, 0(a1) *)
  pose proof (rdw0 m h _ _ MK ltac:(lia)) as R. step. clear R.
  (* bnez a1 and its check *)
  eapply rda_ck_81118 with (X := bv_unsigned r0 + off); [exact U | exact SK | intros v].
  (* lbu a0, 0(a0) *)
  pose proof (rdw0 m w _ _ MB ltac:(lia)) as R. step. clear R.
  (* addi a0, a0, -25; seqz a0, a0; j 0x810f8 *)
  step. step. step.
  rewrite rda_seqz_byte. apply K.
Qed.

End Walk.

(* ---- the contract ---- *)

(* an exit with a0 = V: ds_accept_result evaluated to V on the branch facts of the path, the post's registers and the
   frame released *)
Local Ltac fin V :=
  apply evtF_done;
  lazymatch goal with |- context [PDA.ds_accept_result ?n ?l] =>
    let W := fresh "W" in
    assert (W : PDA.ds_accept_result n l = V)
      by (unfold PDA.ds_accept_result, PDA.ds_byte;
          repeat match goal with Eb : ?b = nth ?i ?ll ?d |- context [nth ?i ?ll ?d] => rewrite <- Eb end;
          bfacts;
          first [ reflexivity
                | repeat match goal with |- context [Z.eqb ?x ?c] =>
                    destruct (Z.eqb_spec x c); try (exfalso; congruence) end;
                  reflexivity ]);
    rewrite W
  end;
  do 5 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|];
  lazymatch goal with FR : rw_cells _ _ _ _, ST : stk _ _ _ _ |- stk _ _ _ (bv_unsigned ?s) =>
    release_frame FR ST (bv_unsigned s); exact ST end.

Theorem rp_ds_accept_holds_F : rp_ds_accept_contract_F.
Proof.
  unfold rp_ds_accept_contract_F, RP_DS_ACCEPT, RP_DS_ACCEPT_FRAME.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs
    lo ST HLO HB RFR RX.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0. change (2 ^ Z.of_N 64) with (2^64) in Ra0.
  carve_frame 16%nat ST.
  (* addi sp, sp, -16; sd ra, 8(sp); li a2, 18; bltu a1, a2 *)
  step. step. step. step. if_cases HL.
  { (* n < 18: li a0, 0; ld ra; addi sp; ret *)
    zc HL. do 4 step. fin constr:(0%Z). }
  zc HL.
  destruct (HB HL) as (LEN & BA & D0 & APS1 & APS2 & CELLS & DG & DS & ADR).
  destruct (RX HL) as (RGOT & RCELL & RBUF & RSH).
  clear HB RX.
  destruct CELLS as (CK & GCK & _).
  destruct ADR as (P0 & N0 & PE & AB).
  (* the four bytes it reads, f + 12, 13, 16, 17: each is application memory and its shadow byte passes *)
  destruct (AB 0 ltac:(lia)) as (APP12 & k12 & MK12 & SK12).
  destruct (AB 1 ltac:(lia)) as (APP13 & k13 & MK13 & SK13).
  destruct (AB 4 ltac:(lia)) as (APP16 & k16 & MK16 & SK16).
  destruct (AB 5 ltac:(lia)) as (APP17 & k17 & MK17 & SK17).
  clear AB.
  rewrite Z.add_0_r in APP12, MK12, SK12.
  replace (bv_unsigned a0 + 12 + 1) with (bv_unsigned a0 + 13) in APP13, MK13, SK13 by lia.
  replace (bv_unsigned a0 + 12 + 4) with (bv_unsigned a0 + 16) in APP16, MK16, SK16 by lia.
  replace (bv_unsigned a0 + 12 + 5) with (bv_unsigned a0 + 17) in APP17, MK17, SK17 by lia.
  apply rda_shok1_of in SK12, SK13, SK16, SK17.
  pose proof (rda_shadow_one RNG _ 6 (bv_unsigned a0 + 12) RSH ltac:(lia)) as RS12.
  pose proof (rda_shadow_one RNG _ 6 (bv_unsigned a0 + 13) RSH ltac:(lia)) as RS13.
  pose proof (rda_shadow_one RNG _ 6 (bv_unsigned a0 + 16) RSH ltac:(lia)) as RS16.
  pose proof (rda_shadow_one RNG _ 6 (bv_unsigned a0 + 17) RSH ltac:(lia)) as RS17.
  clear RSH.
  unfold off_stk, GOT_CELL_K, CELL_K, shadow_addr, ASAN_K in *.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in APP12, APP13, APP16, APP17, APS1, APS2, PE.
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  (* the cells, the shadow bytes and the frame bytes, read in the memory after the store of ra *)
  pose proof (bytes_tp m m0 _ _ 0x987e8 (le8 (wa 0xa0778)) MU1 ltac:(rewrite length_le8; lia) GCK) as GOT0.
  pose proof (bytes_tp m m0 _ _ 0xa0778 (le8 (wa 2147450880)) MU1 ltac:(rewrite length_le8; lia) CK) as SV0.
  assert (RDG : ov_read_bytes rsegs m0 (wa 0x987e8) 8 = Some (le8 (wa 0xa0778))).
  { replace (wa 0x987e8) with (wa (0x987e8 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 0x987e8 _ 0 8 GOT0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  assert (RDS : ov_read_bytes rsegs m0 (wa 0xa0778) 8 = Some (le8 (wa 2147450880))).
  { replace (wa 0xa0778) with (wa (0xa0778 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 0xa0778 _ 0 8 SV0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 12) / 8 + 2147450880) _ MU1
    ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK12) as M12.
  pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 13) / 8 + 2147450880) _ MU1
    ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK13) as M13.
  pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 16) / 8 + 2147450880) _ MU1
    ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK16) as M16.
  pose proof (mrd_tp m m0 _ _ ((bv_unsigned a0 + 17) / 8 + 2147450880) _ MU1
    ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) MK17) as M17.
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 12) _ MU1 ltac:(lia) ltac:(lia)
    (bytes_nth m _ bs 12 BA ltac:(lia))) as F12.
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 13) _ MU1 ltac:(lia) ltac:(lia)
    (bytes_nth m _ bs 13 BA ltac:(lia))) as F13.
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 16) _ MU1 ltac:(lia) ltac:(lia)
    (bytes_nth m _ bs 16 BA ltac:(lia))) as F16.
  pose proof (mrd_tp m m0 _ _ (bv_unsigned a0 + Z.of_nat 17) _ MU1 ltac:(lia) ltac:(lia)
    (bytes_nth m _ bs 17 BA ltac:(lia))) as F17.
  change (Z.of_nat 12) with 12 in F12. change (Z.of_nat 13) with 13 in F13.
  change (Z.of_nat 16) with 16 in F16. change (Z.of_nat 17) with 17 in F17.
  remember (nth 12 bs (Z_to_bv 8 0)) as b12 eqn:E12.
  remember (nth 13 bs (Z_to_bv 8 0)) as b13 eqn:E13.
  remember (nth 16 bs (Z_to_bv 8 0)) as b16 eqn:E16.
  remember (nth 17 bs (Z_to_bv 8 0)) as b17 eqn:E17.
  (* the shadow base through its GOT word *)
  step. step. step.
  (* f + 12: its shadow byte and check *)
  step. gen_addi a0 w12 U12.
  assert (RW12 : ExecF.rng RNG (bv_unsigned w12) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RBUF); lia).
  step. gen_shr w12 g12 G12. rewrite U12 in G12.
  step. gen_addi g12 h12 H12.
  assert (RH12 : ExecF.rng RNG (bv_unsigned h12) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RS12); lia).
  pose proof (rdw0 m0 h12 _ _ M12 ltac:(lia)) as R. step. clear R.
  eapply rda_ck_81098 with (X := bv_unsigned a0 + 12); [exact U12 | exact SK12 | intros v12].
  (* f[12]; li a3, 0x88; beq a1, a3 *)
  pose proof (rdw0 m0 w12 _ _ F12 ltac:(lia)) as R. step. clear R.
  step. step. if_cases H88; zc H88.
  { (* f[12] = 0x88 (is_reac): li a1, 13; the tail reads f[13] *)
    step.
    eapply rda_tail_81108 with (off := 13) (k := k13) (b := b13);
      [ vm_compute; reflexivity | lia | apply (ExecF.rng_sub RNG _ _ _ _ RBUF); lia
      | exact RS13 | exact M13 | exact SK13 | exact F13 | intros v ].
    (* ld ra; addi sp; ret *)
    do 3 step. fin constr:(if bv_unsigned b13 =? 25 then 1 else 0). }
  (* li a3, 0x81; bne a1, a3 *)
  step. step. if_cases H81; zc H81.
  { (* f[12] <> 0x81: li a0, 0; ld ra; addi sp; ret *)
    do 4 step. fin constr:(0%Z). }
  (* f + 13: its shadow byte and check *)
  step. gen_addi a0 w13 U13.
  assert (RW13 : ExecF.rng RNG (bv_unsigned w13) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RBUF); lia).
  step. gen_shr w13 g13 G13. rewrite U13 in G13.
  step. gen_addi g13 h13 H13.
  assert (RH13 : ExecF.rng RNG (bv_unsigned h13) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RS13); lia).
  pose proof (rdw0 m0 h13 _ _ M13 ltac:(lia)) as R. step. clear R.
  eapply rda_ck_810c0 with (X := bv_unsigned a0 + 13); [exact U13 | exact SK13 | intros v13].
  (* f[13]; bnez a1 *)
  pose proof (rdw0 m0 w13 _ _ F13 ltac:(lia)) as R. step. clear R.
  step. if_cases HZ13; zc HZ13.
  { (* f[13] <> 0: li a0, 0; ld ra; addi sp; ret *)
    do 4 step. fin constr:(0%Z). }
  (* f + 16: its shadow byte and check *)
  step. gen_addi a0 w16 U16.
  assert (RW16 : ExecF.rng RNG (bv_unsigned w16) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RBUF); lia).
  step. gen_shr w16 g16 G16. rewrite U16 in G16.
  step. gen_addi g16 h16 H16.
  assert (RH16 : ExecF.rng RNG (bv_unsigned h16) 1) by (apply (ExecF.rng_sub RNG _ _ _ _ RS16); lia).
  pose proof (rdw0 m0 h16 _ _ M16 ltac:(lia)) as R. step. clear R.
  eapply rda_ck_810dc with (X := bv_unsigned a0 + 16); [exact U16 | exact SK16 | intros v16].
  (* f[16]; li a3, 0x88; bne a1, a3 *)
  pose proof (rdw0 m0 w16 _ _ F16 ltac:(lia)) as R. step. clear R.
  step. step. if_cases H16'; zc H16'.
  { (* f[16] <> 0x88: li a0, 0; ld ra; addi sp; ret *)
    do 4 step. fin constr:(0%Z). }
  (* f[16] = 0x88 (is_tagged_reac): li a1, 17; j 0x81108; the tail reads f[17] *)
  step. step.
  eapply rda_tail_81108 with (off := 17) (k := k17) (b := b17);
    [ vm_compute; reflexivity | lia | apply (ExecF.rng_sub RNG _ _ _ _ RBUF); lia
    | exact RS17 | exact M17 | exact SK17 | exact F17 | intros v ].
  (* ld ra; addi sp; ret *)
  do 3 step. fin constr:(if bv_unsigned b17 =? 25 then 1 else 0).
Qed.
