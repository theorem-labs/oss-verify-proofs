(* Segment M02 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (plain, ELF 8dec0b814e6f): piece B of its inner walk,
   0x13b88 .. 0x13c00, as M02D.M02_B_stmt.
   The code: check_refusals(c = s8, m = s0) (0x13b90); a0 = m->n_kept (`lw 0x3ac(s10)`), s6 = cap (`ld 0x18(sp)`,
   M02K.m02_cap), `blez a0` to 0x13c00; else s1 = i = 0, s2 = &c->n_refusals (c + 0x34c8), s3 = c->refusal[0]
   (c + 0x2e88), s4 = m->kept[0] (m + 0x200c), s5 = &m->kept_knock[0] (m + 0x238c). Head 0x13bc8: `lw a0,0(s2)`
   (n_refusals = n_kept by check_refusals), `bge s1,a0` to 0x13c00 (not taken: i < n_kept); check_address(s3, s4)
   (0x13bd8; the strncmp premise is check_kept's first conjunct); `lw a1,0(s5)` (kept_knock[i] = b2z knock);
   check_knock_refused(s3, a1) (0x13be4; check_kept's second conjunct, the stack-protector cells M02K.m02_ssp);
   `lw a0,0x3ac(s10)`, s1 += 1, s5 += 4, s4 += 0x70, s3 += 0xc8, `blt s1,a0` to 0x13bc8. The loop is the assertion
   LOOP by induction on the turns left; each callee runs by Exec.evt_cut over its contract, its post steps
   M02_inv (M02K.m02_inv_call / m02_inv_nil), and the block facts at each new memory come from
   M02K's m02_rconf / m02_mconf and M02_bridge's mb_refusal / mb_kept / mb_mconf_nkept / mb_rconf_nref (the
   assertion AT). The exit at 0x13c00 is M02_mid with s6 = cap.
   M02BPure holds the build-independent lemmas this file adds (mbb_cstr_eq, mbb_cstrz_eq); the loads and the signed
   compares use M02K.m02_rd4 / m02_rd8 / m02_lts.
   Part of the proof of LLVMFuzzerTestOneInput: this file is piece B of segment M02 of its walk; no released proof
   of fuzz_segconf's LLVMFuzzerTestOneInput exists, written new in the style of Prog/check_segments.v. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac Bytes ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env
  check_refusals_c check_address_c check_knock_refused_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require check_segments.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import M02D M02K.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require M02_bridge.
Import check_segments.CsPure.
Import M02_bridge.M02Bridge.
Import ListNotations.
Open Scope Z_scope.

Module M02BPure.
Section Pure.
Variable segs : list Segment.

Lemma mbb_cstr_eq : forall m a a' s, cstr_at segs m a s -> a = a' -> cstr_at segs m a' s.
Proof. intros m a a' s H <-. exact H. Qed.

Lemma mbb_cstrz_eq : forall m a a' s, cstrz_at segs m a s -> a = a' -> cstrz_at segs m a' s.
Proof. intros m a a' s H <-. exact H. Qed.

End Pure.

End M02BPure.
Import M02BPure.

Ltac mbb_weq := first [ reflexivity | f_equal; lia
                      | apply Z_to_bv_eqm; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia ].

Theorem m02_B : check_refusals_c.check_refusals_contract -> check_address_c.check_address_contract ->
  check_knock_refused_c.check_knock_refused_contract -> M02D.M02_B_stmt.
Proof.
  intros CRC CAC CKC. unfold M02_B_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m
    S c mm cap rc mc ret Esp Es0 Es8 Es10 FRM HMOD HM HI.
  subst sp s0 s8 s10.
  destruct HMOD as (_ & _ & HCR & HKA & _ & _).
  destruct (mb_check_refusals_len rc mc HCR) as (Lrk & _).
  pose proof HM as BND. apply m02_bnds in BND.
  destruct BND as (H16 & HT & H47 & Hc0 & Hc16 & Hc & Hm0 & Hm16 & Hm).
  assert (NK8 : (length (mc_kept mc) <= 8)%nat).
  { assert (MC : mconf_at rsegs m mm mc) by (eapply m02_mconf; eassumption).
    exact (proj2 (mb_mconf_nkept rsegs m mm mc MC)). }
  unfold M02_FRAME, MC_N, SEG_C_SIZE, SEG_M_SIZE in *.
  assert (Hb : forall b, 0 <= b2z b < 2 ^ 31) by (intros []; cbn; lia).
  (* The facts of the two blocks and the stack at any M02_inv successor m' of m0. *)
  assert (AT : forall m', M02_inv S m0 m' ->
    mem_inv rsegs m' /\ ssp_ok m' /\
    ov_read_bytes rsegs m' (wa (mm + 9132)) 4 = Some (le4 (Z_to_bv 64 (Z.of_nat (length (mc_kept mc))))) /\
    ov_read_bytes rsegs m' (wa (c + 13512)) 4 = Some (le4 (Z_to_bv 64 (Z.of_nat (length (mc_kept mc))))) /\
    (forall i, (i < length (mc_kept mc))%nat ->
       cstr_at rsegs m' (c + 11912 + 200 * Z.of_nat i) (nth i (rc_refusal rc) []) /\
       cstrz_at rsegs m' (c + 11912 + 200 * Z.of_nat i) (nth i (rc_refusal rc) []) /\
       c + 11912 + 200 * Z.of_nat i + Z.of_nat (length (nth i (rc_refusal rc) [])) + 1 <= c + 16616 /\
       cstr_at rsegs m' (mm + 8204 + 112 * Z.of_nat i) (fst (nth i (mc_kept mc) ([], false))) /\
       mm + 8204 + 112 * Z.of_nat i + Z.of_nat (length (fst (nth i (mc_kept mc) ([], false)))) + 1 <= mm + 9236 /\
       ov_read_bytes rsegs m' (wa (mm + 9100 + 4 * Z.of_nat i)) 4 =
         Some (le4 (Z_to_bv 64 (b2z (snd (nth i (mc_kept mc) ([], false))))))) /\
    (forall depth, 0 <= depth <= 65536 - 208 -> stack_ok rsegs m' (S - 65536) (S - 208) depth) /\
    rconf_at rsegs m' c rc /\ mconf_at rsegs m' mm mc).
  { intros m' HI'.
    assert (RC : rconf_at rsegs m' c rc) by (eapply m02_rconf; eassumption).
    assert (MC : mconf_at rsegs m' mm mc) by (eapply m02_mconf; eassumption).
    split; [eapply m02_mem_inv; eassumption|].
    split; [eapply m02_ssp; eassumption|].
    split; [exact (proj1 (mb_mconf_nkept rsegs m' mm mc MC))|].
    split; [rewrite <- Lrk; exact (proj1 (mb_rconf_nref rsegs m' c rc RC))|].
    split.
    { intros i Hi.
      destruct (mb_refusal rsegs m' c rc i RC Hc16 ltac:(lia)) as (R1 & R2 & R3).
      destruct (mb_kept rsegs m' mm mc i MC Hm16 Hi) as (K1 & _ & K3 & K4 & _).
      split; [exact R1|]. split; [exact R2|]. split; [exact R3|].
      split; [exact K1|]. split; [exact K3|]. apply m02_rd4. exact K4. }
    split; [intros depth Hd; eapply m02_stack_ok; [eassumption | eassumption | unfold M02_FRAME; lia]|].
    split; [exact RC | exact MC]. }
  lazymatch goal with |- evt _ ?Q _ => set (Post := Q) end.
  (* EXIT 0x13c00: M02_mid with s6 = cap. *)
  assert (EXIT : forall (ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' t3' t4' t5' t6' : word)
                        (m' : word -> option byte),
    M02_inv S m0 m' ->
    evt rsegs Post (MS (mkR ra' (Z_to_bv 64 (S - 208)) gp tp t0' t1' t2' (Z_to_bv 64 mm) s1' a0' a1' a2' a3' a4'
                            a5' a6' a7' s2' s3' s4' s5' (Z_to_bv 64 cap) s7 (Z_to_bv 64 c) s9
                            (Z_to_bv 64 (mm + 8192)) s11 t3' t4' t5' t6')
                       F (Z_to_bv 64 0x13c00) fc None m' (seg_rom rsegs))).
  { intros ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' t3' t4' t5' t6' m' HI'.
    apply evt_done. unfold Post, M02_mid.
    exists ra', t0', t1', t2', s1', a0', a1', a2', a3', a4', a5', a6', a7', s2', s3', s4', s5', (Z_to_bv 64 cap),
      s7, s9, s11, t3', t4', t5', t6', F, fc, m'.
    split; [reflexivity|]. split; [exact FRM|]. split; [exact HI' | reflexivity]. }
  (* LOOP 0x13bc8 at turn i, k turns left: s1 = i, s2 = &c->n_refusals, s3 = c->refusal[i], s4 = m->kept[i],
     s5 = &m->kept_knock[i]. *)
  assert (LOOP : forall k i (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' w9 w18 w19 w20 w21 : word)
                        (m' : word -> option byte),
    (i + k = length (mc_kept mc))%nat -> (0 < k)%nat -> M02_inv S m0 m' ->
    w9 = Z_to_bv 64 (Z.of_nat i) -> w18 = Z_to_bv 64 (c + 13512) ->
    w19 = Z_to_bv 64 (c + 11912 + 200 * Z.of_nat i) -> w20 = Z_to_bv 64 (mm + 8204 + 112 * Z.of_nat i) ->
    w21 = Z_to_bv 64 (mm + 9100 + 4 * Z.of_nat i) ->
    evt rsegs Post (MS (mkR ra' (Z_to_bv 64 (S - 208)) gp tp t0' t1' t2' (Z_to_bv 64 mm) w9 a0' a1' a2' a3' a4'
                            a5' a6' a7' w18 w19 w20 w21 (Z_to_bv 64 cap) s7 (Z_to_bv 64 c) s9
                            (Z_to_bv 64 (mm + 8192)) s11 t3' t4' t5' t6')
                       F (Z_to_bv 64 0x13bc8) fc None m' (seg_rom rsegs))).
  { induction k as [|k IH];
      intros i ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' w9 w18 w19 w20 w21 m'
        Hik Hk HI' E9 E18 E19 E20 E21; [lia|].
    subst w9 w18 w19 w20 w21.
    assert (Hi : (i < length (mc_kept mc))%nat) by lia.
    destruct (AT m' HI') as (MI' & _ & _ & RN' & PER' & STK' & _ & _).
    destruct (PER' i Hi) as (_ & G2 & GE & W1 & WE & _).
    pose proof (mb_kept_all_nth _ _ i HKA ltac:(lia) Hi) as CK.
    unfold check_kept in CK. apply andb_true_iff in CK as [CK1 CK2]. apply Z.eqb_eq in CK1.
    pose proof (Hb (snd (nth i (mc_kept mc) ([], false)))) as Hbk.
    (* 0x13bc8 lw a0,0(s2); 0x13bcc bge s1,a0 (not taken: i < n_refusals) *)
    zstep. rewrite ?sx32_small by lia.
    zstep. rewrite ?m02_lts by lia. cs_ntk.
    (* 0x13bd0 mv a0,s3; 0x13bd4 mv a1,s4; 0x13bd8 jal check_address *)
    zstep. zstep. zstep.
    eapply evt_cut.
    { eapply CAC with (lo := S - 65536) (gs := nth i (rc_refusal rc) [])
                      (ws := fst (nth i (mc_kept mc) ([], false))).
      unfold check_address_pre. rewrite !unsigned_lit by lia. rewrite ?Z.add_0_r.
      split; [lia|]. split; [eapply mbb_cstrz_eq; [exact G2 | lia]|].
      split; [unfold apart; lia|]. split; [lia|]. split; [eapply mbb_cstr_eq; [exact W1 | lia]|].
      split; [unfold apart; lia|]. split; [exact CK1|].
      split; [apply STK'; unfold CHECK_ADDRESS_STACK; lia | exact MI']. }
    intros ms' (t0a & t1a & t2a & a0a & a1a & a2a & a3a & a4a & a5a & a6a & a7a & t3a & t4a & t5a & t6a & m2 & -> &
                MU2 & WM2 & MI2 & _ & _).
    rewrite ret_pc_even by (try lia; reflexivity).
    assert (HI2 : M02_inv S m0 m2).
    { eapply m02_inv_call; [exact MU2 | exact HI' | reflexivity | exact WM2 | exact MI2
                           | unfold CHECK_ADDRESS_STACK; lia | lia | lia]. }
    destruct (AT m2 HI2) as (_ & SSP2 & _ & _ & PER2 & STK2 & _ & _).
    destruct (PER2 i Hi) as (G1b & _ & GEb & _ & _ & KN2).
    (* 0x13bdc lw a1,0(s5); 0x13be0 mv a0,s3; 0x13be4 jal check_knock_refused *)
    zstep. rewrite ?sx32_small by lia.
    zstep. zstep.
    eapply evt_cut.
    { eapply CKC with (lo := S - 65536) (gs := nth i (rc_refusal rc) [])
                      (k := snd (nth i (mc_kept mc) ([], false))).
      unfold check_knock_refused_pre. rewrite !unsigned_lit by lia. rewrite ?Z.add_0_r.
      split; [lia|]. split; [eapply mbb_cstr_eq; [exact G1b | lia]|].
      split; [unfold apart; lia|]. split; [reflexivity|]. split; [exact CK2|].
      split; [exact (proj1 SSP2)|]. split; [exact (proj2 SSP2)|].
      split; [cbn [sa_guard SEG_PLAIN]; lia|]. split; [cbn [sa_got_guard SEG_PLAIN]; lia|].
      split; [apply STK2; unfold CHECK_KNOCK_REFUSED_STACK; lia | exact (proj1 (AT m2 HI2))]. }
    intros ms' (t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m3 & -> &
                MU3 & WM3 & MI3 & _ & _).
    rewrite ret_pc_even by (try lia; reflexivity).
    assert (HI3 : M02_inv S m0 m3).
    { eapply m02_inv_call; [exact MU3 | exact HI2 | reflexivity | exact WM3 | exact MI3
                           | unfold CHECK_KNOCK_REFUSED_STACK; lia | lia | lia]. }
    destruct (AT m3 HI3) as (_ & _ & RK3 & _ & _ & _ & _ & _).
    (* 0x13be8 lw a0,0x3ac(s10); s1 += 1; s5 += 4; s4 += 0x70; s3 += 0xc8; 0x13bfc blt s1,a0 *)
    zstep. rewrite ?sx32_small by lia.
    zstep. zstep. zstep. zstep.
    zstep. rewrite ?m02_lts by lia.
    destruct k as [|k].
    - cs_ntk. eapply EXIT. exact HI3.
    - cs_tkn. eapply (IH (Datatypes.S i)); [lia | lia | exact HI3 | | | | |]; mbb_weq. }
  (* 0x13b88 mv a0,s8; 0x13b8c mv a1,s0; 0x13b90 jal check_refusals *)
  zstep. zstep. zstep.
  eapply evt_cut.
  { eapply CRC with (lo := S - 65536) (rc := rc) (mc := mc).
    destruct (AT m HI) as (MI0 & _ & _ & _ & _ & STK0 & RC0 & MC0).
    unfold check_refusals_pre. rewrite !unsigned_lit by lia. rewrite ?Z.add_0_r.
    split; [lia|]. split; [exact Hc16|]. split; [exact RC0|]. split; [unfold apart, SEG_C_SIZE; lia|].
    split; [lia|]. split; [exact Hm16|]. split; [exact MC0|]. split; [unfold apart, SEG_M_SIZE; lia|].
    split; [exact HCR|]. split; [apply STK0; unfold CHECK_REFUSALS_STACK; lia | exact MI0]. }
  intros ms' (t0a & t1a & t2a & a0a & a1a & a2a & a3a & a4a & a5a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & -> &
              MU1 & WM1 & MI1 & _ & _).
  rewrite ret_pc_even by (try lia; reflexivity).
  pose proof (m02_inv_nil S m0 m m1 MU1 HI WM1 MI1) as HI1.
  destruct (AT m1 HI1) as (_ & _ & RK1 & _ & _ & _ & _ & _).
  assert (CAP1 : ov_read_bytes rsegs m1 (wa (S - 208 + 24)) 8 = Some (le8 (Z_to_bv 64 cap))).
  { apply m02_rd8. eapply m02_cap; eassumption. }
  (* 0x13b94 lw a0,0x3ac(s10); 0x13b98 ld s6,0x18(sp); 0x13b9c blez a0 *)
  zstep. rewrite ?sx32_small by lia.
  zstep.
  zstep. rewrite ?m02_lts by lia.
  destruct (Nat.eq_dec (length (mc_kept mc)) 0) as [N0|N0].
  - cs_tkn. eapply EXIT. exact HI1.
  - cs_ntk.
    (* 0x13ba0 .. 0x13bc4: s1 = 0, s2 = c + 0x34c8, s3 = c + 0x2e88, s4 = m + 0x200c, s5 = s10 + 0x38c *)
    do 10 (zstep; cs_swrap).
    eapply (LOOP (length (mc_kept mc)) 0%nat); [lia | lia | exact HI1 | | | | |]; mbb_weq.
Qed.
