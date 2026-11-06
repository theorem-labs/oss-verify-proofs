(* Segment M02 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (UBSan, ELF afc060e3cc9c), piece B (U/Prog/Seg/M02D.v):
   0x13d04 .. 0x13dd0.
   check_refusals(c = 0x48(sp), m = 0x50(sp)) (0x13d0c, premise M02_model's check_refusals: n_refusals = n_kept);
   K = m->n_kept (`lw 0x3ac(s11)`, `blez` skips the loop for K = 0); the loop's state: 0x40(sp) = c & 7 = 0 and
   0x38(sp) = &c->n_refusals (the two cells of M02_W this piece writes), s4 = i, s1 = 200 i, s0 = 4 i,
   s6 = 112 i - 0x380, s7 = c + 0x2e88, s8 = m + 0x238c, s9 = ~s7, s10 = ~(m + 0x200c), s5 = ~s8. Each turn (LOOP,
   by induction on the turns left): the traps c & 7 (`ld 0x40(sp)`, `bnez`), ~s7 < 200 i, ~(m + 0x200c) < 112 i
   (no wrap: the blocks lie below 2^47); `bge s4, n_refusals` (not taken: i < K = n_refusals);
   check_address(c->refusal[i], m->kept[i]) (M02Bridge.mb_refusal / mb_kept, the first conjunct of check_kept);
   the traps s6 = 0 (i = 8: i < K <= 8) and ~s8 < 4 i; check_knock_refused(c->refusal[i], `lw` kept_knock[i])
   (the second conjunct, the stack-protector cells of M02_mem); then `lw` K, i + 1 and `blt` back or out to
   0x13dd0.
   Part of the proof of LLVMFuzzerTestOneInput: this file is piece B of segment M02 of its walk; no released proof
   of fuzz_segconf's LLVMFuzzerTestOneInput exists, written new. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require check_segments.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require M02_bridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env check_refusals_c check_address_c
  check_knock_refused_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.Seg Require Import Tac_slot Tac_b1 M02D M02K.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg.M02_bridge.M02Bridge.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.check_segments.CsPure.
Import ListNotations.
Open Scope Z_scope.

Lemma m02b_check_kept : forall got want, check_kept got want = true ->
  strncmp got (fst want) (strlen (fst want)) = 0 /\ (negb (snd want) || strstr_found got TNP) = true.
Proof.
  intros got want H. unfold check_kept in H. apply andb_true_iff in H as [H1 H2].
  apply Z.eqb_eq in H1. split; assumption.
Qed.

Lemma m02b_b2z : forall b, 0 <= b2z b <= 1.
Proof. intros [|]; cbn; lia. Qed.

Lemma m02b_cstr_eq : forall m a a' s, cstr_at rsegs m a s -> a = a' -> cstr_at rsegs m a' s.
Proof. intros m a a' s H <-. exact H. Qed.

Lemma m02b_cstrz_eq : forall m a a' s, cstrz_at rsegs m a s -> a = a' -> cstrz_at rsegs m a' s.
Proof. intros m a a' s H <-. exact H. Qed.

Section Loop.
Hypothesis CA : check_address_contract.
Hypothesis CK : check_knock_refused_contract.
Variables (S c mm cap : Z) (rc : rconf) (mc : mconf) (ret : bool) (m0 : word -> option byte) (gp tp : word)
  (F : bvmap 5 word) (fc : bv 32).
Hypothesis HMod : M02_model rc mc ret.
Hypothesis HM : M02_mem S c mm cap rc mc m0.
Hypothesis FRM : frm0 fc.

Lemma m02b_loop : forall k i (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31
                              w8 w9 w20 w21 w22 w23 w24 w25 w26 w38 w40 : word) (M : word -> option byte),
  (i + k = length (mc_kept mc))%nat -> (0 < k)%nat -> M02_inv S m0 M ->
  bytes_at rsegs M (S - 240 + 64) (le8 w40) -> bytes_at rsegs M (S - 240 + 56) (le8 w38) ->
  w40 = Z_to_bv 64 0 -> w38 = Z_to_bv 64 (c + 13512) ->
  w8 = Z_to_bv 64 (4 * Z.of_nat i) -> w9 = Z_to_bv 64 (200 * Z.of_nat i) -> w20 = Z_to_bv 64 (Z.of_nat i) ->
  w22 = Z_to_bv 64 (112 * Z.of_nat i - 896) ->
  w21 = Z_to_bv 64 (18446744073709551615 - (mm + 9100)) -> w23 = Z_to_bv 64 (c + 11912) ->
  w24 = Z_to_bv 64 (mm + 9100) -> w25 = Z_to_bv 64 (18446744073709551615 - (c + 11912)) ->
  w26 = Z_to_bv 64 (18446744073709551615 - (mm + 8204)) ->
  evt rsegs (M02_mid 0x13dd0 S mm gp tp m0)
    (MS (mkR x1 (Z_to_bv 64 (S - 240)) gp tp x5 x6 x7 w8 w9 x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (18446744073709551615 - mm)) x19 w20 w21 w22 w23 w24 w25 w26
             (Z_to_bv 64 (mm + MC_N)) x28 x29 x30 x31)
        F (Z_to_bv 64 0x13d70) fc None M (seg_rom rsegs)).
Proof.
  pose proof (m02_bnds S c mm cap rc mc m0 HM) as (H16 & HT & H47 & Hc0 & Hc16 & Hc & Hm0 & Hm16 & Hm).
  unfold SEG_C_SIZE, SEG_M_SIZE in Hc, Hm.
  pose proof HMod as (_ & _ & HCR & HKA & _).
  destruct (mb_check_refusals_len rc mc HCR) as (EK & _).
  pose proof HM as (_ & HTM0 & _).
  induction k as [|k IH];
    intros i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31
      w8 w9 w20 w21 w22 w23 w24 w25 w26 w38 w40 M
      Hik Hk HI B40 B38 E40 E38 E8 E9 E20 E22 E21 E23 E24 E25 E26; [lia|].
  subst w8 w9 w20 w21 w22 w23 w24 w25 w26 w38 w40.
  assert (Hi : (i < length (mc_kept mc))%nat) by lia.
  pose proof (mb_kept rsegs M mm mc i (m02_mconf S c mm cap rc mc m0 M HM HI) Hm16 Hi)
    as (KS & KZ & KB & KN & Hi8).
  pose proof (mb_refusal rsegs M c rc i (m02_rconf S c mm cap rc mc m0 M HM HI) Hc16 ltac:(lia))
    as (RS & RZ & RB).
  pose proof (m02b_check_kept _ _ (mb_kept_all_nth _ _ i HKA ltac:(lia) Hi)) as (CK1 & CK2).
  unfold refusal_addr, kept_addr, RC_REFUSAL, RC_REFUSAL_LEN, MC_KEPT, MC_KEPT_LEN, MC_KNOCK, SEG_C_SIZE,
    SEG_M_SIZE in *.
  (* 0x13d70 ld a0,0x40(sp) = 0; 0x13d74 bnez (c & 7) *)
  pose proof (b1_ld8 _ _ _ B40) as R40.
  m02_show zstep. clear R40. m02_show zstep. m02_ntk.
  (* 0x13d78 ld a0,0x38(sp) = &c->n_refusals; 0x13d7c lw a0,0(a0); 0x13d80 bge s4,a0 -> out *)
  pose proof (b1_ld8 _ _ _ B38) as R38.
  pose proof (mb_rconf_nref rsegs M c rc (m02_rconf S c mm cap rc mc m0 M HM HI)) as (RN & LR8).
  unfold RC_NREF in RN.
  m02_show zstep. clear R38. m02_show zstep. clear RN.
  m02_show ltac:(rewrite (sx32_small (Z.of_nat (length (rc_refusal rc)))) by lia).
  m02_show zstep. m02_ntk.
  (* 0x13d84 bltu s9,s1; 0x13d88 a0 = s6 + 0x380; 0x13d8c bltu s10,a0: no wrap *)
  m02_show zstep. m02_ntk.
  m02_show zstep.
  m02_show zstep. m02_ntk.
  (* 0x13d90 s3 = s7 + s1; 0x13d94 a1 = s8 + s6; 0x13d98 mv a0,s3; 0x13d9c jal check_address *)
  m02_show zstep. m02_show zstep. m02_show zstep. m02_show zstep.
  eapply evt_cut.
  { apply CA with (lo := S - 65536) (gs := nth i (rc_refusal rc) []) (ws := fst (nth i (mc_kept mc) ([], false))).
    m02_show ltac:(rewrite !unsigned_lit by lia; unfold check_address_pre;
      split; [lia|]; split; [eapply m02b_cstrz_eq; [exact RZ | lia]|]; split; [unfold apart; left; lia|];
      split; [lia|]; split; [eapply m02b_cstr_eq; [exact KS | lia]|]; split; [unfold apart; left; lia|];
      split; [exact CK1|];
      split; [apply (m02_stack_ok S c mm cap rc mc m0 M HM HI); unfold CHECK_ADDRESS_STACK, M02_FRAME; lia
             | exact (m02_mem_inv S m0 M HI)]). }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m1 & -> & MU & WM & MI & ST & _).
  rewrite ret_pc_even by (try lia; reflexivity).
  m02_show ltac:(rewrite !unsigned_lit in MU by lia).
  assert (HI1 : M02_inv S m0 m1)
    by (apply (m02_inv_step S m0 M m1 _ HI MU WM MI); unfold CHECK_ADDRESS_STACK; [m02_subfp | m02_low]).
  assert (B40' : bytes_at rsegs m1 (S - 240 + 64) (le8 (Z_to_bv 64 0))).
  { apply (bytes_at_transport rsegs _ _ _ _ _ B40 MU). rewrite length_le8. unfold CHECK_ADDRESS_STACK.
    cbn [disjoint_from]. split; [lia | exact I]. }
  assert (B38' : bytes_at rsegs m1 (S - 240 + 56) (le8 (Z_to_bv 64 (c + 13512)))).
  { apply (bytes_at_transport rsegs _ _ _ _ _ B38 MU). rewrite length_le8. unfold CHECK_ADDRESS_STACK.
    cbn [disjoint_from]. split; [lia | exact I]. }
  clear MU WM MI ST B40 B38.
  (* 0x13da0 beqz s6 (i = 8); 0x13da4 bltu s5,s0; 0x13da8 a0 = s8 + s0; 0x13dac lw a1,0(a0) = kept_knock[i] *)
  m02_show zstep. m02_ntk.
  m02_show zstep. m02_ntk.
  m02_show zstep.
  pose proof (mb_kept rsegs m1 mm mc i (m02_mconf S c mm cap rc mc m0 m1 HM HI1) Hm16 Hi)
    as (_ & _ & _ & KN1 & _).
  pose proof (mb_refusal rsegs m1 c rc i (m02_rconf S c mm cap rc mc m0 m1 HM HI1) Hc16 ltac:(lia))
    as (RS1 & _ & _).
  unfold refusal_addr, kept_addr, RC_REFUSAL, RC_REFUSAL_LEN, MC_KEPT, MC_KEPT_LEN, MC_KNOCK in KN1, RS1.
  pose proof (m02_ld4 _ _ _ KN1) as RK.
  pose proof (m02b_b2z (snd (nth i (mc_kept mc) ([], false)))) as Hb.
  m02_show zstep. clear RK KN1.
  m02_show ltac:(rewrite (sx32_small (b2z (snd (nth i (mc_kept mc) ([], false))))) by lia).
  (* 0x13db0 mv a0,s3; 0x13db4 jal check_knock_refused *)
  m02_show zstep. m02_show zstep.
  pose proof (m02_ssp S c mm cap rc mc m0 m1 HM HI1) as (SG & g0 & SGd).
  eapply evt_cut.
  { apply CK with (lo := S - 65536) (gs := nth i (rc_refusal rc) []) (k := snd (nth i (mc_kept mc) ([], false))).
    m02_show ltac:(rewrite !unsigned_lit by lia; unfold check_knock_refused_pre;
      split; [lia|]; split; [eapply m02b_cstr_eq; [exact RS1 | lia]|]; split; [unfold apart; left; lia|];
      split; [reflexivity|]; split; [exact CK2|]; split; [exact SG|]; split; [exists g0; exact SGd|];
      split; [cbn; lia|]; split; [cbn; lia|];
      split; [apply (m02_stack_ok S c mm cap rc mc m0 m1 HM HI1); unfold CHECK_KNOCK_REFUSED_STACK, M02_FRAME; lia
             | exact (m02_mem_inv S m0 m1 HI1)]). }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> & MU & WM & MI & ST & _).
  rewrite ret_pc_even by (try lia; reflexivity).
  m02_show ltac:(rewrite !unsigned_lit in MU by lia).
  assert (HI2 : M02_inv S m0 m2)
    by (apply (m02_inv_step S m0 m1 m2 _ HI1 MU WM MI); unfold CHECK_KNOCK_REFUSED_STACK; [m02_subfp | m02_low]).
  assert (B40'' : bytes_at rsegs m2 (S - 240 + 64) (le8 (Z_to_bv 64 0))).
  { apply (bytes_at_transport rsegs _ _ _ _ _ B40' MU). rewrite length_le8. unfold CHECK_KNOCK_REFUSED_STACK.
    cbn [disjoint_from]. split; [lia | exact I]. }
  assert (B38'' : bytes_at rsegs m2 (S - 240 + 56) (le8 (Z_to_bv 64 (c + 13512)))).
  { apply (bytes_at_transport rsegs _ _ _ _ _ B38' MU). rewrite length_le8. unfold CHECK_KNOCK_REFUSED_STACK.
    cbn [disjoint_from]. split; [lia | exact I]. }
  clear MU WM MI ST B40' B38'.
  (* the latch: 0x13db8 lw a0,0x3ac(s11) = K; s4 = i + 1; s6 += 0x70; s1 += 0xc8; s0 += 4; 0x13dcc blt s4,a0 *)
  pose proof (mb_mconf_nkept rsegs m2 mm mc (m02_mconf S c mm cap rc mc m0 m2 HM HI2)) as (RNK & LK8).
  replace (mm + MC_NKEPT) with (mm + MC_N + 940) in RNK by (unfold MC_N, MC_NKEPT; lia).
  m02_show zstep. clear RNK.
  m02_show ltac:(rewrite (sx32_small (Z.of_nat (length (mc_kept mc)))) by lia).
  m02_show zstep. m02_show zstep. m02_show zstep. m02_show zstep. m02_show zstep.
  destruct k as [|k].
  - (* i + 1 = K: out to 0x13dd0 *)
    m02_ntk.
    rewrite <- (m02_not_lit mm) by lia.
    apply evt_done. unfold M02_mid. do 29 eexists.
    m02_show ltac:(split; [reflexivity|]). split; [exact FRM | exact HI2].
  - m02_tkn.
    m02_show ltac:(eapply (IH (Datatypes.S i)); [lia | lia | exact HI2 | exact B40'' | exact B38''
      | reflexivity | reflexivity | f_equal; lia | f_equal; lia | f_equal; lia | f_equal; lia
      | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity]).
Qed.

End Loop.

Theorem m02_B : check_refusals_contract -> check_address_contract -> check_knock_refused_contract -> M02_B_stmt.
Proof.
  intros CRF CA CK. unfold M02_B_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m0 m S c mm cap rc mc ret Esp E2 E11 FRM HMod HM HI.
  subst sp s2 s11. unfold M02_FRAME.
  pose proof (m02_bnds S c mm cap rc mc m0 HM) as (H16 & HT & H47 & Hc0 & Hc16 & Hc & Hm0 & Hm16 & Hm).
  unfold SEG_C_SIZE, SEG_M_SIZE in Hc, Hm.
  pose proof HMod as (_ & _ & HCR & _).
  destruct (mb_check_refusals_len rc mc HCR) as (EK & _).
  pose proof HM as (_ & HTM0 & _).
  rewrite (m02_not_lit mm) by lia.
  (* 0x13d04 ld a0,0x48(sp); 0x13d08 ld a1,0x50(sp); 0x13d0c jal check_refusals *)
  pose proof (b1_ld8 _ _ _ (m02_cellc S c mm cap rc mc m0 m HM HI)) as RC. unfold M02_FRAME in RC.
  pose proof (b1_ld8 _ _ _ (m02_cellm S c mm cap rc mc m0 m HM HI)) as RM. unfold M02_FRAME in RM.
  m02_show zstep. m02_show zstep. m02_show zstep.
  clear RC RM.
  eapply evt_cut.
  { apply CRF with (lo := S - 65536) (rc := rc) (mc := mc).
    rewrite !unsigned_lit by lia. unfold check_refusals_pre.
    split; [lia|]. split; [exact Hc16|]. split; [exact (m02_rconf S c mm cap rc mc m0 m HM HI)|].
    split; [unfold apart, SEG_C_SIZE; left; lia|]. split; [lia|]. split; [exact Hm16|].
    split; [exact (m02_mconf S c mm cap rc mc m0 m HM HI)|]. split; [unfold apart, SEG_M_SIZE; left; lia|].
    split; [exact HCR|].
    split; [apply (m02_stack_ok S c mm cap rc mc m0 m HM HI); unfold CHECK_REFUSALS_STACK, M02_FRAME; lia|].
    exact (m02_mem_inv S m0 m HI). }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m1 & -> & MU & WM & MI & ST & _).
  rewrite ret_pc_even by (try lia; reflexivity).
  assert (HI1 : M02_inv S m0 m1)
    by (apply (m02_inv_step S m0 m m1 _ HI MU WM MI); [m02_subfp | m02_low]).
  clear MU WM MI ST HI.
  (* 0x13d10 lw a0,0x3ac(s11) = K; 0x13d14 blez a0 *)
  pose proof (mb_mconf_nkept rsegs m1 mm mc (m02_mconf S c mm cap rc mc m0 m1 HM HI1)) as (RNK & L8).
  replace (mm + MC_NKEPT) with (mm + MC_N + 940) in RNK by (unfold MC_N, MC_NKEPT; lia).
  m02_show zstep. clear RNK.
  m02_show ltac:(rewrite (sx32_small (Z.of_nat (length (mc_kept mc)))) by lia).
  m02_show zstep.
  destruct (Nat.eq_dec (length (mc_kept mc)) 0) as [N0|N0].
  - (* K = 0: to 0x13dd0 *)
    m02_tkn.
    rewrite <- (m02_not_lit mm) by lia.
    apply evt_done. unfold M02_mid. do 29 eexists.
    m02_show ltac:(split; [reflexivity|]). split; [exact FRM | exact HI1].
  - m02_ntk.
    (* 0x13d18 s0 = 0; s1 = 0; s4 = 0; 0x13d24 ld a3,0x48(sp) = c; 0x13d28 andi a0,a3,7; 0x13d2c sd a0,0x40(sp) *)
    pose proof (b1_ld8 _ _ _ (m02_cellc S c mm cap rc mc m0 m1 HM HI1)) as RC. unfold M02_FRAME in RC.
    m02_show zstep. m02_show zstep. m02_show zstep. m02_show zstep. clear RC.
    m02_show zstep.
    m02_show ltac:(replace (Z.land c 7) with 0 by (change 7 with (2 ^ 3 - 1); rewrite zb_land_mask by lia;
      change (2 ^ 3) with 8; Z.div_mod_to_equations; lia)).
    destruct (m02_cells S c mm cap rc mc m0 m1 HM HI1 (S - 240 + 56) 16 ltac:(lia) ltac:(cbn; lia)) as (j & RW).
    destruct HI1 as (MU & WM & MIv & _).
    unfold M02_W, M02_FRAME in MU.
    m02_show zstep.
    (* 0x13d30 .. 0x13d48: the constants; a2 = c + 0x34c8; 0x13d4c sd a2,0x38(sp) *)
    m02_show zstep. m02_show zstep. m02_show zstep. m02_show zstep. m02_show zstep. m02_show zstep.
    m02_show zstep.
    m02_show zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?M1 _) => rename M1 into Ms end.
    assert (HIs : M02_inv S m0 Ms) by (apply (m02_inv_of S m0 Ms HTM0 H47 MU WM MIv)).
    clear MU WM MIv.
    pose proof (sl_cells_bytes _ _ _ RW) as RB. cbn [cells_bytes cbytes] in RB. rewrite app_nil_r in RB.
    apply bytes_at_app in RB as [B38 B40]. rewrite length_le8 in B40.
    replace (S - 240 + 56 + Z.of_nat 8) with (S - 240 + 64) in B40 by lia.
    clear RW.
    (* 0x13d50 s7 = c + 0x2e88; 0x13d54 ld a1,0x50(sp) = m; a0 = m + 0x200c; s8 = m + 0x238c; the three nots;
       0x13d6c s6 = -0x380 *)
    pose proof (b1_ld8 _ _ _ (m02_cellm S c mm cap rc mc m0 Ms HM HIs)) as RM. unfold M02_FRAME in RM.
    m02_show zstep. m02_show zstep. clear RM.
    m02_show zstep. m02_show zstep. m02_show zstep. m02_show zstep. m02_show zstep. m02_show zstep.
    m02_show ltac:(eapply (m02b_loop CA CK S c mm cap rc mc ret m0 gp tp F fc HMod HM FRM
                            (length (mc_kept mc)) 0%nat);
      [ lia | lia | exact HIs | exact B40 | exact B38
      | try cs_swrap; f_equal; lia | try cs_swrap; f_equal; lia
      | f_equal; lia | f_equal; lia | f_equal; lia | try cs_swrap; f_equal; lia
      | try cs_swrap; rewrite ?zb_lxor_ones by lia; f_equal; lia
      | try cs_swrap; f_equal; lia | try cs_swrap; f_equal; lia
      | try cs_swrap; rewrite ?zb_lxor_ones by lia; f_equal; lia
      | try cs_swrap; rewrite ?zb_lxor_ones by lia; f_equal; lia ]).
Qed.
