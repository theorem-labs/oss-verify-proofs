(** reac-pw/fuzz_segconf, UBSan build (image 1696d6c34ffd): piece P6 of reac_segconf_parse_file, the role branch
    (R:236-246 with reac_role_intent_parse inlined, RR:110-120; family F3). S_P6 of
    lib/U/Prog/reac_segconf_parse_file_pieces_c.v: ROLE -> INTENT and INTENT -> KREF or PROV.

    Code (UBSan binary):
    - ROLE 0x156b0 -> INTENT 0x15834: `lbu a1, 0(s7)`, `beqz a1` to 0x1581c (a0 = 0); the fold loop at 0x156bc
      (a0 = li, a2 = s7 + li, a3 = sp + 0xa0 + li; `addi -0x41; sltiu 0x1a; slli 5; add; sb`), the trap
      `beq a2, s5` at 0x156dc (s5 = -1, a2 = vp + li lies in buf), `lbu a1, 1(a2)`, `beqz a1` and `bltu 0x3e, a0`
      to 0x15820 (so li <= 63); at 0x15820 `ld a1, 0x40(sp)` = ~(sp + 0xa0) (pf_spill's item 6) and the trap
      `bltu a1, a0` at 0x15824 (falls through: li <= 63 and sp + 0x420 < 2^63), then `sb zero` = low[li] = 0.
    - INTENT 0x15834 -> KREF 0x158f0 (through 0x158dc: a2 = PF_STR_BADROLE) or PROV 0x15b70: bcmp(low, "auto", 5)
      at 0x15844, ("master", 7) at 0x1585c, ("slave", 6) at 0x15874, the tap / box word compares at 0x158a8 /
      0x158d8 against the spill slots sp + 0x28 / sp + 0x20 (pf_spill's items 3 / 2); a0 = 0 .. 4 on the five
      hits, joining at 0x15b4c: `ld a1, 0x88(sp)` (pf_curslot), `andi a1, a1, 3`, the trap `bnez` at 0x15b54
      (c mod 16 = 0, 356 = 4 * 89), `ld a1, 0x88(sp)`, `sw a0, 0x10(a1)`, `sw s11, 0x14(a1)` (s11 = 1),
      a0 = &seg[gi].role_file, a2 = "%s".
    The build-independent facts are lib/Prog/pfB_p6_spine.v; the frame and memory transport is the kit
    lib/U/Prog/pfB_kit.v (pf_mem). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac Bytes ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import StrFun SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env refuse_c reac_segconf_parse_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import reac_segconf_parse_file_pieces_c bcmp_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pfB_facts pfB_p6_spine.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import pfB_kit.
Import ListNotations.
Open Scope Z_scope.

(** ** Local facts *)
(** bcmp_c.v states its result with lib/U/Spec/StrFun's memcmp_model, O1 with lib/Spec/StrFun's: the same
    function. *)
Lemma p6u_memcmp_eq : forall n l r, U.Spec.StrFun.memcmp_model l r n = memcmp_model l r n.
Proof. intros n l r. reflexivity. Qed.

(** A mid-line context through pf_mem. *)
Lemma p6u_ctx_mem : forall m0 m fc sp lo v c t s o ln d n,
  pf_ctx m0 fc sp lo v c t s o ln d n -> pf_mem m0 m sp lo c -> pf_ctx m fc sp lo v c t s o ln d n.
Proof.
  intros m0 m fc sp lo v c t s o ln d n (ENV & TX & SPL & R) PM.
  pose proof ENV as (_ & _ & _ & _ & PE & _). pose proof PE as (FRM & _).
  split; [exact (pf_env_mem m0 m fc fc sp lo c v ENV PM FRM)|].
  split; [exact (pf_text_mem m0 m sp lo c t s TX PM)|].
  split; [exact (pf_spill_mem m0 m sp lo c SPL PM) | exact R].
Qed.

(** bcmp at a call site: its contract's post, as a continuation. *)
Lemma p6u_bcmp : forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc m (LB rs : list byte) v,
  bcmp_contract ->
  bytes_at rsegs m (bv_unsigned a0) LB -> bytes_at rsegs m (bv_unsigned a1) rs ->
  memcmp_model LB rs (Z.to_nat (bv_unsigned a2)) = Some v -> mem_inv rsegs m ->
  (forall m' (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
     munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> bytes_at rsegs m' (bv_unsigned a0) LB ->
     evt rsegs Q (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 v) x11 x12 x13 x14 x15 x16 x17
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 BCMP) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m LB rs v BC B0 B1 MM MI K.
  eapply evt_cut; [eapply BC; [exact B0 | exact B1 | rewrite p6u_memcmp_eq; exact MM | exact MI]|].
  intros ms' (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & -> & MU & WM
    & MI' & B0' & _).
  apply K; assumption.
Qed.

(** The literals "auto", "master", "slave" with their NUL in .rodata (0x1030e, 0x10548, 0x1075c). *)
Lemma p6u_lit : forall m a w, mem_inv rsegs m -> 0 <= a -> a + Z.of_nat (length (zb (w ++ [0]))) <= 2 ^ 64 ->
  ro_bytes_b rsegs a (zb (w ++ [0])) = true -> bytes_at rsegs m a (zb (w ++ [0])).
Proof.
  intros m a w MI H0 H1 H2. apply ro_bytes_at; [exact MI | exact H0 | exact H1 |].
  apply ro_bytes_b_sound. exact H2.
Qed.

Lemma p6u_lit_auto : forall m, mem_inv rsegs m -> bytes_at rsegs m 66318 (zb (S_auto ++ [0])).
Proof.
  intros m MI. apply p6u_lit; [exact MI | lia | change (length (zb (S_auto ++ [0]))) with 5%nat; lia |].
  vm_compute. reflexivity.
Qed.

Lemma p6u_lit_master : forall m, mem_inv rsegs m -> bytes_at rsegs m 66888 (zb (S_master ++ [0])).
Proof.
  intros m MI. apply p6u_lit; [exact MI | lia | change (length (zb (S_master ++ [0]))) with 7%nat; lia |].
  vm_compute. reflexivity.
Qed.

Lemma p6u_lit_slave : forall m, mem_inv rsegs m -> bytes_at rsegs m 67420 (zb (S_slave ++ [0])).
Proof.
  intros m MI. apply p6u_lit; [exact MI | lia | change (length (zb (S_slave ++ [0]))) with 6%nat; lia |].
  vm_compute. reflexivity.
Qed.

Lemma p6u_wfacts : forall w, forallb (fun x => negb (x =? 0) && (0 <=? x) && (x <? 256)) w = true ->
  ~ In 0 w /\ Forall (fun x => 0 <= x < 256) w.
Proof.
  intros w H. rewrite forallb_forall in H. split.
  - intros Hin. specialize (H 0 Hin). cbn in H. discriminate H.
  - apply Forall_forall. intros x Hx. specialize (H x Hx).
    apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [_ H2].
    apply Z.leb_le in H2. apply Z.ltb_lt in H3. lia.
Qed.

Lemma p6u_zx8 : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 c))) = c.
Proof. intros c Hc. rewrite (p6_u8 c Hc). apply unsigned_lit. lia. Qed.

Ltac p6u_fix_ret :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.

(** The tap compare (0x1587c .. 0x158a8): `lbu, lbu, lbu, lb; slli, or, slli, slli, or, or` build pf_word4 of the
    four bytes of low (sp + 0xa0 .. 0xa3), `ld a1, 0x28(sp)` reads the tap slot and `beq` goes to 0x15b14
    (role = 3) or falls to the box compare at 0x158ac. Stepped over abstract bytes, away from the walk's context
    (the plain twin's p6_tapcmp, lib/Prog/pf_p6.v). *)
Lemma p6u_tapcmp : forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc m (b0 b1 b2 b3 : byte),
  ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned sp + 160)) 1 = Some [b0] ->
  ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned sp + 161)) 1 = Some [b1] ->
  ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned sp + 162)) 1 = Some [b2] ->
  ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned sp + 163)) 1 = Some [b3] ->
  ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned sp + 40)) 8 = Some (le8 (Z_to_bv 64 PF_TAP_WORD)) ->
  (forall x10 x11 x12 x13 : word, pf_word4 [b0; b1; b2; b3] = PF_TAP_WORD ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6) F (Z_to_bv 64 0x15b14) fc None m (seg_rom rsegs))) ->
  (forall x10 x11 x12 x13 : word, pf_word4 [b0; b1; b2; b3] <> PF_TAP_WORD ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6) F (Z_to_bv 64 0x158ac) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6) F (Z_to_bv 64 0x1587c) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m b0 b1 b2 b3 R0 R1 R2 R3 RT KT KF.
  pose proof (p6_word4_range [b0; b1; b2; b3]) as W4R.
  do 12 zstep.
  rewrite (p6_word_val b0 b1 b2 b3).
  if_cases K;
    rewrite (p6_bveq_small (pf_word4 [b0; b1; b2; b3]) PF_TAP_WORD) in K by (unfold PF_TAP_WORD; lia).
  - apply Z.eqb_eq in K. apply KT. exact K.
  - apply Z.eqb_neq in K. apply KF. exact K.
Qed.

(** The box compare (0x158ac .. 0x158d8): the same, against the box slot sp + 0x20; `beq` goes to 0x15b48
    (role = 4) or falls to the bad-role refusal at 0x158dc. *)
Lemma p6u_boxcmp : forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc m (b0 b1 b2 b3 : byte),
  ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned sp + 160)) 1 = Some [b0] ->
  ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned sp + 161)) 1 = Some [b1] ->
  ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned sp + 162)) 1 = Some [b2] ->
  ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned sp + 163)) 1 = Some [b3] ->
  ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned sp + 32)) 8 = Some (le8 (Z_to_bv 64 PF_BOX_WORD)) ->
  (forall x10 x11 x12 x13 : word, pf_word4 [b0; b1; b2; b3] = PF_BOX_WORD ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6) F (Z_to_bv 64 0x15b48) fc None m (seg_rom rsegs))) ->
  (forall x10 x11 x12 x13 : word, pf_word4 [b0; b1; b2; b3] <> PF_BOX_WORD ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6) F (Z_to_bv 64 0x158dc) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6) F (Z_to_bv 64 0x158ac) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m b0 b1 b2 b3 R0 R1 R2 R3 RB KT KF.
  pose proof (p6_word4_range [b0; b1; b2; b3]) as W4R.
  do 12 zstep.
  rewrite (p6_word_val b0 b1 b2 b3).
  if_cases K;
    rewrite (p6_bveq_small (pf_word4 [b0; b1; b2; b3]) PF_BOX_WORD) in K by (unfold PF_BOX_WORD; lia).
  - apply Z.eqb_eq in K. apply KT. exact K.
  - apply Z.eqb_neq in K. apply KF. exact K.
Qed.

Ltac p6u_mlia := pf_prune; Z.div_mod_to_equations; lia.

Ltac p6u_weq := first [ reflexivity | f_equal; pf_lia | apply Z_to_bv_eqm; p6u_mlia ].

(** A trap branch (to the `unimp` at 0x15c7c): its condition contradicts the facts. *)
Ltac p6u_trap K := exfalso; try unfold pf_not in K; zify_cond K; try zb_masks;
  try unfold rseg_addr, RSEG_SIZE in K; p6u_mlia.

(** ** ROLE -> INTENT: the fold loop and the NUL store *)
Lemma p6u_role : forall n, H_INTENT n -> H_ROLE n.
Proof.
  intros n HI. unfold H_ROLE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo v c t s rc nm o ln d gi kp vp key val CTX ST RG CS KV HS8 HS7 KEY.
  rewrite (p6_rkey rc gi nm (ln + 1) (pf_tline s o) key val (proj1 KV) KEY).
  destruct KV as (_ & _ & _ & CV & IBV).
  pose proof CTX as (ENV & TX & SPL & Ho & Hn & LC).
  pose proof ST as (RCA & CUR & NMA & CNT).
  pose proof RG as (_ & _ & _ & _ & HS5 & _ & _).
  pose proof (pf_mem_refl m fc (bv_unsigned sp) lo c v rc ENV RCA) as PM0.
  pose proof (pf_mem_wok _ _ _ _ _ PM0) as WOK.
  destruct (pf_wok_nums _ _ _ WOK) as (N1 & N2 & N3 & N4 & N5).
  pose proof WOK as (_ & _ & _ & SPH & _).
  unfold PARSE_FILE_FRAME in SPH. change (2 ^ 63) with 9223372036854775808 in SPH.
  subst s7 s5.
  unfold pf_inb, PF_BUF in IBV.
  pose proof (pf_mem_stk _ _ _ _ _ PM0) as STK. unfold PARSE_FILE_FRAME in STK.
  destruct (stk_split rsegs m lo (bv_unsigned sp + 160) (bv_unsigned sp + 1056) STK ltac:(pf_lia)) as [_ STK1].
  destruct (stk_split rsegs m (bv_unsigned sp + 160) (bv_unsigned sp + 224) (bv_unsigned sp + 1056) STK1
    ltac:(pf_lia)) as [STKL _].
  destruct (stk_bytes rsegs m _ _ STKL ltac:(pf_lia)) as (LB0 & LL0 & BL0).
  assert (LL : length LB0 = 64%nat)
    by (rewrite LL0; replace (bv_unsigned sp + 224 - (bv_unsigned sp + 160)) with 64 by pf_lia; reflexivity).
  clear LL0 STK STK1 STKL.
  pose proof CV as (bsv & slv & BV & ZV & NZV & SLV).
  assert (LBV : length bsv = length val) by (rewrite <- ZV; unfold zs; symmetry; apply length_map).
  assert (RV : forall i, 0 <= nth i val 0 < 256).
  { intros i. rewrite <- ZV. unfold zs. destruct (Nat.lt_ge_cases i (length bsv)) as [Hi|Hi].
    - rewrite (nth_indep _ 0 (bv_unsigned ZERO)) by (rewrite length_map; exact Hi). rewrite map_nth.
      pose proof (bv_unsigned_in_range 8 (nth i bsv ZERO)) as R. unfold bv_modulus in R.
      change (2 ^ Z.of_N 8) with 256 in R. exact R.
    - rewrite nth_overflow by (rewrite length_map; exact Hi). lia. }
  assert (RVF : Forall (fun x => 0 <= x < 256) val).
  { apply Forall_forall. intros x Hx. destruct (In_nth val x 0 Hx) as (i & Hi & <-). apply RV. }
  assert (BVZ : bytes_at rsegs m vp (bsv ++ [ZERO])).
  { pose proof BV as BV'. replace (bsv ++ ZERO :: slv) with ((bsv ++ [ZERO]) ++ slv) in BV'
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in BV'. exact (proj1 BV'). }
  assert (HBV : forall i, (i <= length val)%nat -> nth_error (bsv ++ [ZERO]) i = Some (Z_to_bv 8 (nth i val 0))).
  { intros i Hi. rewrite <- ZV. apply p6_byte_at. rewrite LBV. exact Hi. }
  assert (NZE : forall i, (i <= length val)%nat -> nth i val 0 = 0 -> i = length val).
  { intros i Hi E. destruct (Nat.eq_dec i (length val)) as [->|Ne]; [reflexivity|].
    exfalso. exact (p6_nth_nz val i NZV ltac:(pf_lia) E). }
  set (Wl := [(bv_unsigned sp + 160, bv_unsigned sp + 224)]).
  lazymatch goal with |- evt _ ?QQ _ => set (Q := QQ) end.
  (* 0x15820: the trap on ~(sp + 0xa0) < li, low[li] = 0, then INTENT *)
  assert (EXIT : forall (li : nat) (m1 : word -> option byte) (x10 x11 x12 x13 x14 : word),
    (li = length val \/ li = 63%nat) -> (li <= length val)%nat -> (li <= 63)%nat ->
    x10 = Z_to_bv 64 (Z.of_nat li) ->
    pf_mem m m1 (bv_unsigned sp) lo c -> munch Wl m m1 ->
    bytes_at rsegs m1 (bv_unsigned sp + 160) (p6_lowb val LB0 li) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 (-1)) s6
                         (Z_to_bv 64 vp) s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x15820) fc None m1 (seg_rom rsegs))).
  { intros li m1 x10 x11 x12 x13 x14 Eli Hl1 Hl2 -> PM1 MU1 BL1.
    pose proof (pf_spill_mem m m1 (bv_unsigned sp) lo c SPL PM1) as SPL1.
    assert (RN : ov_read_bytes rsegs m1 (wa (bv_unsigned sp + 64)) 8 = Some (le8 (pf_not (bv_unsigned sp + 160)))).
    { destruct SPL1 as (S1 & _ & _).
      pose proof (pfb_saved_read rsegs m1 (bv_unsigned sp + 16) _ 6 S1 ltac:(cbn [length]; pf_lia)) as H.
      cbn [nth] in H. unfold PF_LOW in H.
      replace (bv_unsigned sp + 16 + 8 * Z.of_nat 6) with (bv_unsigned sp + 64) in H by pf_lia. exact H. }
    clear SPL1.
    assert (SO : store_ok rsegs m1 (wa (bv_unsigned sp + 160 + Z.of_nat li)) 1 = true)
      by (apply (pf_frame_store_ok m m1 (bv_unsigned sp) lo c);
          [exact PM1 | pf_lia | unfold PARSE_FILE_FRAME; pf_lia]).
    zstep. zstep.
    let K := fresh "KT" in if_cases K; [ first [ p6u_trap K | clear K ] .. ].
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?A ?B) _) =>
      replace A with (wa (bv_unsigned sp + 160 + Z.of_nat li)) by (unfold wa; p6u_weq);
      replace B with [ZERO] by reflexivity end.
    set (m2 := write_to_mem m1 (wa (bv_unsigned sp + 160 + Z.of_nat li)) [ZERO]).
    assert (PM2 : pf_mem m m2 (bv_unsigned sp) lo c).
    { unfold m2. apply pf_mem_store; [exact PM1 | pf_lia | cbn [length]; pf_lia | | exact SO].
      cbn [length]. unfold pf_Wp. cbn [inside]. right; right; right; left.
      unfold PF_SCRATCH, PF_NAMEBUF. pf_lia. }
    assert (MU2 : munch Wl m m2).
    { unfold m2. apply munch_write; [exact MU1 | pf_lia | cbn [length]; pf_lia |].
      unfold Wl. cbn [length inside]. left. pf_lia. }
    assert (BL2 : bytes_at rsegs m2 (bv_unsigned sp + 160)
                    (zb (map lower (firstn li val)) ++ ZERO :: skipn (S li) LB0)).
    { pose proof (bytes_at_write_inside rsegs m1 (bv_unsigned sp + 160) (p6_lowb val LB0 li) (Z.of_nat li) [ZERO]
        BL1) as NW.
      rewrite Nat2Z.id in NW. rewrite p6_lowb_fin in NW by pf_lia.
      apply NW; [pf_lia | rewrite p6_lowb_len by pf_lia; cbn [length]; pf_lia]. }
    clearbody m2.
    pose proof (p6u_ctx_mem _ _ _ _ _ _ _ _ _ _ _ _ _ CTX PM2) as CTX2.
    assert (RC2 : rconf_at rsegs m2 c rc).
    { eapply pfb_rconf_at_munch; [exact RCA | exact MU2 |]. unfold Wl, SEG_C_SIZE. cbn [disjoint_from].
      split; [pf_lia | exact I]. }
    pose proof (pf_nm_at_mem _ _ _ _ _ _ NMA PM2) as NM2.
    assert (CS2 : pf_curslot m2 (bv_unsigned sp) c (Some gi)).
    { eapply pf_curslot_munch; [exact CS | exact MU2 |]. unfold Wl, PF_CURSLOT. cbn [disjoint_from].
      split; [pf_lia | exact I]. }
    assert (CV2 : cstr_at rsegs m2 vp val).
    { eapply pfb_cstr_at_munch; [exact CV | exact MU2 |]. unfold Wl. cbn [disjoint_from].
      split; [pf_lia | exact I]. }
    eapply evt_mono.
    { eapply HI with (lo := lo) (v := v) (c := c) (t := t) (s := s) (rc := rc) (nm := nm) (o := o) (ln := ln)
        (d := d) (gi := gi) (vp := vp) (val := val).
      - exact CTX2.
      - split; [exact RC2 | split; [exact CUR | split; [exact NM2 | exact CNT]]].
      - exact RG.
      - exact CS2.
      - reflexivity.
      - exact CV2.
      - unfold pf_inb, PF_BUF. exact IBV.
      - exists (zb (map lower (firstn li val)) ++ ZERO :: skipn (S li) LB0). split; [|split].
        + rewrite length_app. cbn [length]. rewrite p6_zb_len by pf_lia. rewrite length_skipn. pf_lia.
        + unfold PF_LOW. exact BL2.
        + rewrite (p6_rlow_len val li NZV Eli Hl1 Hl2), (p6_rlow val li NZV Eli Hl1 Hl2).
          apply p6_lb_prefix; [exact RVF | exact Hl1]. }
    intros ms' HF. unfold Q. eapply pf_fin_weaken; [intros; reflexivity | exact PM2 | exact HF]. }
  (* the fold loop at 0x156bc *)
  assert (LOOP : forall (k li : nat) (m1 : word -> option byte) (x10 x11 x12 x13 x14 : word),
    (63 - li = k)%nat -> (li < 63)%nat -> (li < length val)%nat ->
    x10 = Z_to_bv 64 (Z.of_nat li) -> bv_unsigned x11 = nth li val 0 ->
    pf_mem m m1 (bv_unsigned sp) lo c -> munch Wl m m1 ->
    bytes_at rsegs m1 (bv_unsigned sp + 160) (p6_lowb val LB0 li) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 (-1)) s6
                         (Z_to_bv 64 vp) s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x156bc) fc None m1 (seg_rom rsegs))).
  { induction k as [|k IH]; intros li m1 x10 x11 x12 x13 x14 Hk Hli Hlv -> E11 PM1 MU1 BL1; [pf_lia|].
    pose proof (RV li) as Rc. rewrite <- E11 in Rc.
    assert (SO : store_ok rsegs m1 (wa (bv_unsigned sp + 160 + Z.of_nat li)) 1 = true)
      by (apply (pf_frame_store_ok m m1 (bv_unsigned sp) lo c);
          [exact PM1 | pf_lia | unfold PARSE_FILE_FRAME; pf_lia]).
    do 8 zstep.
    rewrite (p6_fold_le1 (bv_unsigned x11) Rc). rewrite E11.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 ?A _) _) =>
      replace A with (wa (bv_unsigned sp + 160 + Z.of_nat li)) by (unfold wa; p6u_weq) end.
    set (m2 := write_to_mem m1 (wa (bv_unsigned sp + 160 + Z.of_nat li)) [Z_to_bv 8 (lower (nth li val 0))]).
    assert (PM2 : pf_mem m m2 (bv_unsigned sp) lo c).
    { unfold m2. apply pf_mem_store; [exact PM1 | pf_lia | cbn [length]; pf_lia | | exact SO].
      cbn [length]. unfold pf_Wp. cbn [inside]. right; right; right; left.
      unfold PF_SCRATCH, PF_NAMEBUF. pf_lia. }
    assert (MU2 : munch Wl m m2).
    { unfold m2. apply munch_write; [exact MU1 | pf_lia | cbn [length]; pf_lia |].
      unfold Wl. cbn [length inside]. left. pf_lia. }
    assert (BL2 : bytes_at rsegs m2 (bv_unsigned sp + 160) (p6_lowb val LB0 (S li))).
    { pose proof (bytes_at_write_inside rsegs m1 (bv_unsigned sp + 160) (p6_lowb val LB0 li) (Z.of_nat li)
        [Z_to_bv 8 (lower (nth li val 0))] BL1) as NW.
      rewrite Nat2Z.id in NW. rewrite p6_lowb_step in NW by pf_lia.
      apply NW; [pf_lia | rewrite p6_lowb_len by pf_lia; cbn [length]; pf_lia]. }
    clearbody m2. clear PM1 MU1 BL1 SO.
    assert (RD : ov_read_bytes rsegs m2 (wa (vp + Z.of_nat (S li))) 1 = Some [Z_to_bv 8 (nth (S li) val 0)]).
    { apply (p6_read1 rsegs m2 vp (bsv ++ [ZERO]) (S li)); [|apply HBV; pf_lia].
      apply (bytes_at_transport rsegs Wl m m2 vp _ BVZ MU2). unfold Wl. cbn [disjoint_from].
      rewrite length_app, LBV. cbn [length]. split; [pf_lia | exact I]. }
    zstep.
    let K := fresh "KT" in if_cases K; [ first [ p6u_trap K | clear K ] .. ].
    zstep. zstep. zstep.
    if_cases K; zify_cond K; rewrite ?(p6_u8 (nth (S li) val 0) (RV (S li))) in K.
    - assert (E : S li = length val) by (apply NZE; [pf_lia | exact K]).
      eapply (EXIT (S li)); [left; exact E | pf_lia | pf_lia | p6u_weq | exact PM2 | exact MU2 | exact BL2].
    - zstep. zstep.
      if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by pf_lia.
      + eapply (EXIT (S li)); [right; pf_lia | pf_lia | pf_lia | p6u_weq | exact PM2 | exact MU2 | exact BL2].
      + zstep.
        assert (Lv : (S li < length val)%nat).
        { destruct (Nat.lt_ge_cases (S li) (length val)) as [L|L]; [exact L|].
          exfalso. apply K. rewrite nth_overflow by pf_lia. reflexivity. }
        eapply (IH (S li)); [pf_lia | pf_lia | exact Lv | p6u_weq | apply p6u_zx8; apply RV | exact PM2
          | exact MU2 | exact BL2]. }
  (* 0x156b0: val[0] *)
  assert (R0 : ov_read_bytes rsegs m (wa (vp + Z.of_nat 0)) 1 = Some [Z_to_bv 8 (nth 0 val 0)])
    by (apply (p6_read1 rsegs m vp (bsv ++ [ZERO]) 0); [exact BVZ | apply HBV; pf_lia]).
  unfold PF_PC_ROLE.
  zstep. zstep.
  if_cases K; zify_cond K; rewrite ?(p6_u8 (nth 0 val 0) (RV 0%nat)) in K.
  - assert (E : 0%nat = length val) by (apply NZE; [pf_lia | exact K]).
    zstep. eapply (EXIT 0%nat); [left; exact E | pf_lia | pf_lia | p6u_weq | exact PM0 | apply munch_refl
      | exact BL0].
  - assert (L0 : (0 < length val)%nat).
    { destruct val as [|x val']; [cbn in K; exfalso; apply K; reflexivity | cbn; pf_lia]. }
    zstep.
    eapply (LOOP 63%nat 0%nat); [pf_lia | pf_lia | exact L0 | p6u_weq | apply p6u_zx8; apply RV | exact PM0
      | apply munch_refl | exact BL0].
Qed.

(** ** INTENT -> KREF or PROV: the three bcmp calls, the two word compares, the role / role_set stores *)
Lemma p6u_intent : forall n, bcmp_contract -> H_KREF n -> H_PROV n -> H_INTENT n.
Proof.
  intros n BC HK HP. unfold H_INTENT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo v c t s rc nm o ln d gi vp val CTX ST RG CS HS7 CV IBV (LB & LLB & BLB & PLB).
  subst s7. unfold PF_LOW in BLB.
  pose proof CTX as (ENV & TX & SPL & Ho & Hn & LC).
  pose proof ST as (RCA & CUR & NMA & CNT).
  pose proof RG as (_ & _ & _ & _ & _ & _ & HS11). subst s11.
  pose proof ENV as (_ & _ & _ & _ & _ & _ & _ & MI0 & _).
  pose proof (pf_mem_refl m fc (bv_unsigned sp) lo c v rc ENV RCA) as PM0.
  pose proof (pf_mem_wok _ _ _ _ _ PM0) as WOK.
  destruct (pf_wok_nums _ _ _ WOK) as (N1 & N2 & N3 & N4 & N5).
  pose proof WOK as (_ & _ & _ & SPH & _ & _ & HC64 & C16 & _).
  unfold PARSE_FILE_FRAME in SPH. change (2 ^ 63) with 9223372036854775808 in SPH.
  unfold SEG_C_SIZE in HC64. change (2 ^ 64) with 18446744073709551616 in HC64.
  unfold pf_inb, PF_BUF in IBV.
  cbn [pf_cur_ok] in CUR.
  assert (GI32 : (gi < 32)%nat).
  { destruct RCA as (bs0 & _ & (_ & LS0 & _)). pf_lia. }
  pose proof CV as (bsv & slv & BV & ZV & NZV & SLV).
  set (l := r_low val 0 64) in *.
  assert (NZl : ~ In 0 l) by (apply p6_rlow_nz; exact NZV).
  lazymatch goal with |- evt _ ?QQ _ => set (Q := QQ) end.
  (* KREF: the bad-role refusal, through 0x158dc (a2 = PF_STR_BADROLE) *)
  assert (KREFP : forall (mk : word -> option byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    role_intent_parse l = None -> pf_mem m mk (bv_unsigned sp) lo c -> munch [] m mk ->
    evt rsegs Q (MS (mkR x1 sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5
                         s6 (Z_to_bv 64 vp) s8 s9 s10 (Z_to_bv 64 1) x28 x29 x30 x31)
                    F (Z_to_bv 64 0x158dc) fc None mk (seg_rom rsegs))).
  { intros mk x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 RN PMk MUk.
    zstep. zstep. zstep.
    eapply evt_mono.
    { eapply HK with (lo := lo) (v := v) (c := c) (t := t) (s := s) (rc := rc) (cur := Some gi) (nm := nm)
        (o := o) (ln := ln) (d := d) (f := F_badrole) (fp := PF_STR_BADROLE) (vp := vp) (x := val).
      - exact (p6u_ctx_mem _ _ _ _ _ _ _ _ _ _ _ _ _ CTX PMk).
      - split; [eapply pfb_rconf_at_munch; [exact RCA | exact MUk | exact I]|].
        split; [exact CUR|]. split; [exact (pf_nm_at_mem _ _ _ _ _ _ NMA PMk) | exact CNT].
      - exact RG.
      - eapply pf_curslot_munch; [exact CS | exact MUk | exact I].
      - left. reflexivity.
      - unfold PF_STR_BADROLE. first [reflexivity | apply bv_eq; vm_compute; reflexivity].
      - reflexivity.
      - eapply pfb_cstr_at_munch; [exact CV | exact MUk | exact I].
      - exact IBV. }
    intros ms' HF. unfold Q. rewrite (p6_step_none rc gi nm (ln + 1) val RN).
    eapply pf_fin_weaken; [intros; reflexivity | exact PMk | exact HF]. }
  (* PROV: at 0x15b4c with a0 = r: the cur slot, its trap, role = r, role_set = 1, a0 = &seg[gi].role_file *)
  assert (PROVP : forall (r : Z) (mk : word -> option byte)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    role_intent_parse l = Some r -> 0 <= r <= 4 -> pf_mem m mk (bv_unsigned sp) lo c -> munch [] m mk ->
    evt rsegs Q (MS (mkR x1 sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5
                         s6 (Z_to_bv 64 vp) s8 s9 s10 (Z_to_bv 64 1) x28 x29 x30 x31)
                    F (Z_to_bv 64 0x15b4c) fc None mk (seg_rom rsegs))).
  { intros r mk x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 RP Hr PMk MUk.
    assert (RCk : rconf_at rsegs mk c rc) by (eapply pfb_rconf_at_munch; [exact RCA | exact MUk | exact I]).
    assert (CSk : pf_curslot mk (bv_unsigned sp) c (Some gi))
      by (eapply pf_curslot_munch; [exact CS | exact MUk | exact I]).
    pose proof (pf_c_wr mk (bv_unsigned sp) lo c rc WOK RCk) as WR.
    destruct RCk as (bsc & BC0 & EC0).
    pose proof EC0 as (LBC & _).
    unfold SEG_C_SIZE in LBC.
    assert (RS : ov_read_bytes rsegs mk (wa (bv_unsigned sp + 136)) 8 = Some (le8 (Z_to_bv 64 (rseg_addr c gi)))).
    { unfold pf_curslot, PF_CURSLOT in CSk. cbn [pf_cur_ptr] in CSk.
      pose proof (bytes_at_ov_read rsegs mk _ _ 0 8 CSk ltac:(rewrite length_le8; pf_lia)) as H.
      replace (bv_unsigned sp + 136 + Z.of_nat 0) with (bv_unsigned sp + 136) in H by pf_lia.
      rewrite H. f_equal; cbn [skipn]; apply firstn_all2; rewrite length_le8; pf_lia. }
    zstep. zstep. zstep.
    let K := fresh "KT" in if_cases K; [ first [ p6u_trap K | clear K ] .. ].
    zstep.
    assert (SO1 : store_ok rsegs mk (wa (c + (356 * Z.of_nat gi + 16))) 4 = true)
      by (apply (wr_at_store_ok rsegs mk c SEG_C_SIZE); [exact WR | pf_lia | unfold SEG_C_SIZE; pf_lia]).
    assert (SO1r : store_ok rsegs mk (wa (rseg_addr c gi + 16)) 4 = true)
      by (replace (rseg_addr c gi + 16) with (c + (356 * Z.of_nat gi + 16)) by (unfold rseg_addr, RSEG_SIZE; pf_lia);
          exact SO1).
    zstep. clear SO1r.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?A _) _) =>
      replace A with (wa (c + (356 * Z.of_nat gi + 16))) by (unfold wa, rseg_addr, RSEG_SIZE; p6u_weq) end.
    set (m5 := write_to_mem mk (wa (c + (356 * Z.of_nat gi + 16))) (le4 (Z_to_bv 64 r))).
    set (Wc := [(rseg_addr c gi + 16, rseg_addr c gi + 24)]).
    pose proof (bytes_at_bound _ _ _ _ BC0) as BB. rewrite LBC in BB.
    assert (PM5 : pf_mem m m5 (bv_unsigned sp) lo c).
    { unfold m5. apply pf_mem_store; [exact PMk | pf_lia | rewrite length_le4; pf_lia | | rewrite length_le4; exact SO1].
      rewrite length_le4. unfold pf_Wp, RC_PARSE_W. cbn [inside]. right; right; right; right; left.
      unfold RC_N. pf_lia. }
    assert (MU5 : munch Wc mk m5).
    { unfold m5. apply munch_write; [apply munch_refl | pf_lia | rewrite length_le4; pf_lia |].
      rewrite length_le4. unfold Wc, rseg_addr, RSEG_SIZE. cbn [inside]. left. pf_lia. }
    assert (BC5 : bytes_at rsegs m5 c (upd_bytes bsc (356 * gi + 16) (le4 (Z_to_bv 64 r)))).
    { pose proof (bytes_at_write_inside rsegs mk c bsc (356 * Z.of_nat gi + 16) (le4 (Z_to_bv 64 r)) BC0) as NW.
      replace (Z.to_nat (356 * Z.of_nat gi + 16)) with (356 * gi + 16)%nat in NW by pf_lia.
      apply NW; [pf_lia | rewrite length_le4; pf_lia]. }
    assert (WR5 : wr_at rsegs m5 c SEG_C_SIZE) by (apply wr_at_write; exact WR).
    clearbody m5.
    assert (SO2 : store_ok rsegs m5 (wa (c + (356 * Z.of_nat gi + 20))) 4 = true)
      by (apply (wr_at_store_ok rsegs m5 c SEG_C_SIZE); [exact WR5 | pf_lia | unfold SEG_C_SIZE; pf_lia]).
    assert (SO2r : store_ok rsegs m5 (wa (rseg_addr c gi + 20)) 4 = true)
      by (replace (rseg_addr c gi + 20) with (c + (356 * Z.of_nat gi + 20)) by (unfold rseg_addr, RSEG_SIZE; pf_lia);
          exact SO2).
    zstep. clear SO2r.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?A _) _) =>
      replace A with (wa (c + (356 * Z.of_nat gi + 20))) by (unfold wa, rseg_addr, RSEG_SIZE; p6u_weq) end.
    set (m6 := write_to_mem m5 (wa (c + (356 * Z.of_nat gi + 20))) (le4 (Z_to_bv 64 1))).
    assert (PM6 : pf_mem m m6 (bv_unsigned sp) lo c).
    { unfold m6. apply pf_mem_store; [exact PM5 | pf_lia | rewrite length_le4; pf_lia | | rewrite length_le4; exact SO2].
      rewrite length_le4. unfold pf_Wp, RC_PARSE_W. cbn [inside]. right; right; right; right; left.
      unfold RC_N. pf_lia. }
    assert (MU6 : munch Wc mk m6).
    { unfold m6. apply munch_write; [exact MU5 | pf_lia | rewrite length_le4; pf_lia |].
      rewrite length_le4. unfold Wc, rseg_addr, RSEG_SIZE. cbn [inside]. left. pf_lia. }
    assert (BC6 : bytes_at rsegs m6 c
                    (upd_bytes (upd_bytes bsc (356 * gi + 16) (le4 (Z_to_bv 64 r))) (356 * gi + 20)
                       (le4 (Z_to_bv 64 1)))).
    { pose proof (bytes_at_write_inside rsegs m5 c _ (356 * Z.of_nat gi + 20) (le4 (Z_to_bv 64 1)) BC5) as NW.
      replace (Z.to_nat (356 * Z.of_nat gi + 20)) with (356 * gi + 20)%nat in NW by pf_lia.
      apply NW; [pf_lia | rewrite upd_bytes_length; rewrite ?length_le4; pf_lia]. }
    assert (RC6 : rconf_at rsegs m6 c (pf_prov_mid (PRole r) rc gi)).
    { exists (upd_bytes (upd_bytes bsc (356 * gi + 16) (le4 (Z_to_bv 64 r))) (356 * gi + 20) (le4 (Z_to_bv 64 1))).
      split; [exact BC6 | apply p6_role_rconf; [exact EC0 | exact CUR | pf_lia]]. }
    clearbody m6.
    assert (CS6 : pf_curslot m6 (bv_unsigned sp) c (Some gi)).
    { eapply pf_curslot_munch; [exact CSk | exact MU6 |]. unfold Wc, PF_CURSLOT, rseg_addr, RSEG_SIZE.
      cbn [disjoint_from]. split; [pf_lia | exact I]. }
    zstep. zstep. zstep.
    eapply evt_mono.
    { eapply HP with (lo := lo) (v := v) (c := c) (t := t) (s := s) (rc := rc) (nm := nm) (o := o) (ln := ln)
        (d := d) (k := PRole r) (gi := gi).
      - exact (p6u_ctx_mem _ _ _ _ _ _ _ _ _ _ _ _ _ CTX PM6).
      - split; [exact RC6|]. split; [apply p6_prov_cur_ok; exact CUR|].
        split; [exact (pf_nm_at_mem _ _ _ _ _ _ NMA PM6) | apply p6_prov_cnt; exact CNT].
      - exact RG.
      - exact CS6.
      - cbn [pf_prov_off]. unfold RS_ROLE_FILE, rseg_addr, RSEG_SIZE. p6u_weq.
      - unfold PF_STR_S. first [reflexivity | apply bv_eq; vm_compute; reflexivity]. }
    intros ms' HF. unfold Q. rewrite (p6_step_some rc gi nm (ln + 1) val r RP).
    eapply pf_fin_weaken; [intros; reflexivity | exact PM6 | exact HF]. }
  (* the literals and the three bcmp results *)
  destruct (p6u_wfacts S_auto ltac:(vm_compute; reflexivity)) as [NZA RA].
  destruct (p6u_wfacts S_master ltac:(vm_compute; reflexivity)) as [NZM RM].
  destruct (p6u_wfacts S_slave ltac:(vm_compute; reflexivity)) as [NZS RSL].
  destruct (memcmp_model_total LB (zb (S_auto ++ [0])) 5 ltac:(pf_lia) ltac:(apply Nat.leb_le; reflexivity))
    as [v1 MM1].
  pose proof (O1_bcmp_lit_holds LB l S_auto v1 NZl NZA RA PLB MM1) as O1A.
  pose proof (p6_memcmp_range _ _ _ _ MM1) as RV1.
  unfold PF_PC_INTENT. do 5 zstep.
  eapply (p6u_bcmp Q) with (LB := LB) (rs := zb (S_auto ++ [0])) (v := v1);
    [exact BC | rewrite unsigned_lit by pf_lia; exact BLB | rewrite unsigned_lit by pf_lia; apply p6u_lit_auto; exact MI0
    | rewrite unsigned_lit by pf_lia; exact MM1 | exact MI0 |].
  intros m1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 MU1 WM1 MI1 BL1.
  rewrite unsigned_lit in BL1 by pf_lia.
  assert (PM1 : pf_mem m m1 (bv_unsigned sp) lo c)
    by (eapply (pf_mem_call _ _ _ _ _ _ []); [exact PM0 | intros x _; exact I | exact MU1 | exact WM1 | exact MI1]).
  p6u_fix_ret. zstep.
  destruct (Z.eq_dec v1 0) as [E1|E1].
  { subst v1. try if_true.
    eapply (PROVP 0); [apply p6_rip_auto; apply O1A; reflexivity | pf_lia | exact PM1 | exact MU1]. }
  assert (C1 : bv_eqb (Z_to_bv 64 v1) (Z_to_bv 64 0) = false)
    by (rewrite p6_bveq_small by pf_lia; apply Z.eqb_neq; exact E1).
  if_cases K; [exfalso; congruence | clear K].
  assert (NA : strcmp l S_auto <> 0) by (intros H; apply E1; apply O1A; exact H).
  destruct (memcmp_model_total LB (zb (S_master ++ [0])) 7 ltac:(pf_lia) ltac:(apply Nat.leb_le; reflexivity))
    as [v2 MM2].
  pose proof (O1_bcmp_lit_holds LB l S_master v2 NZl NZM RM PLB MM2) as O1M.
  pose proof (p6_memcmp_range _ _ _ _ MM2) as RV2.
  do 5 zstep.
  eapply (p6u_bcmp Q) with (LB := LB) (rs := zb (S_master ++ [0])) (v := v2);
    [exact BC | rewrite unsigned_lit by pf_lia; exact BL1 | rewrite unsigned_lit by pf_lia; apply p6u_lit_master; exact MI1
    | rewrite unsigned_lit by pf_lia; exact MM2 | exact MI1 |].
  intros m2 z5 z6 z7 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 MU2 WM2 MI2 BL2.
  rewrite unsigned_lit in BL2 by pf_lia.
  assert (PM2 : pf_mem m m2 (bv_unsigned sp) lo c)
    by (eapply (pf_mem_call _ _ _ _ _ _ []); [exact PM1 | intros x _; exact I | exact MU2 | exact WM2 | exact MI2]).
  assert (MU2' : munch [] m m2) by (eapply munch_trans; [exact MU1 | exact MU2]).
  p6u_fix_ret. zstep.
  destruct (Z.eq_dec v2 0) as [E2|E2].
  { subst v2. try if_true. zstep. zstep.
    eapply (PROVP 1); [apply p6_rip_master; [exact NA | apply O1M; reflexivity] | pf_lia | exact PM2 | exact MU2']. }
  assert (C2 : bv_eqb (Z_to_bv 64 v2) (Z_to_bv 64 0) = false)
    by (rewrite p6_bveq_small by pf_lia; apply Z.eqb_neq; exact E2).
  if_cases K; [exfalso; congruence | clear K].
  assert (NM : strcmp l S_master <> 0) by (intros H; apply E2; apply O1M; exact H).
  destruct (memcmp_model_total LB (zb (S_slave ++ [0])) 6 ltac:(pf_lia) ltac:(apply Nat.leb_le; reflexivity))
    as [v3 MM3].
  pose proof (O1_bcmp_lit_holds LB l S_slave v3 NZl NZS RSL PLB MM3) as O1S.
  pose proof (p6_memcmp_range _ _ _ _ MM3) as RV3.
  do 5 zstep.
  eapply (p6u_bcmp Q) with (LB := LB) (rs := zb (S_slave ++ [0])) (v := v3);
    [exact BC | rewrite unsigned_lit by pf_lia; exact BL2 | rewrite unsigned_lit by pf_lia; apply p6u_lit_slave; exact MI2
    | rewrite unsigned_lit by pf_lia; exact MM3 | exact MI2 |].
  intros m3 w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 MU3 WM3 MI3 BL3.
  rewrite unsigned_lit in BL3 by pf_lia.
  assert (PM3 : pf_mem m m3 (bv_unsigned sp) lo c)
    by (eapply (pf_mem_call _ _ _ _ _ _ []); [exact PM2 | intros x _; exact I | exact MU3 | exact WM3 | exact MI3]).
  assert (MU3' : munch [] m m3) by (eapply munch_trans; [exact MU2' | exact MU3]).
  p6u_fix_ret. zstep.
  destruct (Z.eq_dec v3 0) as [E3|E3].
  { subst v3. try if_true. zstep. zstep.
    eapply (PROVP 2); [apply p6_rip_slave; [exact NA | exact NM | apply O1S; reflexivity] | pf_lia | exact PM3
      | exact MU3']. }
  assert (C3 : bv_eqb (Z_to_bv 64 v3) (Z_to_bv 64 0) = false)
    by (rewrite p6_bveq_small by pf_lia; apply Z.eqb_neq; exact E3).
  if_cases K; [exfalso; congruence | clear K].
  assert (NS : strcmp l S_slave <> 0) by (intros H; apply E3; apply O1S; exact H).
  (* the tap / box words *)
  assert (RDL : forall i : nat, (i < 64)%nat ->
            ov_read_bytes rsegs m3 (Z_to_bv 64 (bv_unsigned sp + 160 + Z.of_nat i)) 1 = Some [nth i LB ZERO]).
  { intros i Hi.
    exact (p6_read1 rsegs m3 (bv_unsigned sp + 160) LB i (nth i LB ZERO) BL3 ltac:(apply nth_error_nth'; pf_lia)). }
  assert (RD0 : ov_read_bytes rsegs m3 (Z_to_bv 64 (bv_unsigned sp + 160)) 1 = Some [nth 0 LB ZERO]).
  { pose proof (RDL 0%nat ltac:(pf_lia)) as H.
    replace (bv_unsigned sp + 160 + Z.of_nat 0) with (bv_unsigned sp + 160) in H by pf_lia. exact H. }
  assert (RD1 : ov_read_bytes rsegs m3 (Z_to_bv 64 (bv_unsigned sp + 161)) 1 = Some [nth 1 LB ZERO]).
  { pose proof (RDL 1%nat ltac:(pf_lia)) as H.
    replace (bv_unsigned sp + 160 + Z.of_nat 1) with (bv_unsigned sp + 161) in H by pf_lia. exact H. }
  assert (RD2 : ov_read_bytes rsegs m3 (Z_to_bv 64 (bv_unsigned sp + 162)) 1 = Some [nth 2 LB ZERO]).
  { pose proof (RDL 2%nat ltac:(pf_lia)) as H.
    replace (bv_unsigned sp + 160 + Z.of_nat 2) with (bv_unsigned sp + 162) in H by pf_lia. exact H. }
  assert (RD3 : ov_read_bytes rsegs m3 (Z_to_bv 64 (bv_unsigned sp + 163)) 1 = Some [nth 3 LB ZERO]).
  { pose proof (RDL 3%nat ltac:(pf_lia)) as H.
    replace (bv_unsigned sp + 160 + Z.of_nat 3) with (bv_unsigned sp + 163) in H by pf_lia. exact H. }
  clear RDL.
  pose proof (pf_spill_mem m m3 (bv_unsigned sp) lo c SPL PM3) as SPL3.
  destruct SPL3 as (SP3 & _ & _).
  assert (RT : ov_read_bytes rsegs m3 (Z_to_bv 64 (bv_unsigned sp + 40)) 8 = Some (le8 (Z_to_bv 64 PF_TAP_WORD))).
  { pose proof (pfb_saved_read rsegs m3 (bv_unsigned sp + 16) _ 3 SP3 ltac:(cbn [length]; pf_lia)) as H.
    cbn [nth] in H. unfold wa in H.
    replace (bv_unsigned sp + 16 + 8 * Z.of_nat 3) with (bv_unsigned sp + 40) in H by pf_lia. exact H. }
  assert (RB : ov_read_bytes rsegs m3 (Z_to_bv 64 (bv_unsigned sp + 32)) 8 = Some (le8 (Z_to_bv 64 PF_BOX_WORD))).
  { pose proof (pfb_saved_read rsegs m3 (bv_unsigned sp + 16) _ 2 SP3 ltac:(cbn [length]; pf_lia)) as H.
    cbn [nth] in H. unfold wa in H.
    replace (bv_unsigned sp + 16 + 8 * Z.of_nat 2) with (bv_unsigned sp + 32) in H by pf_lia. exact H. }
  clear SP3.
  destruct (O1_word_lit_holds LB l NZl ltac:(pf_lia) PLB) as [OT OB].
  assert (W4 : pf_word4 [nth 0 LB ZERO; nth 1 LB ZERO; nth 2 LB ZERO; nth 3 LB ZERO] = pf_word4 LB) by reflexivity.
  (* 0x1587c: the tap compare *)
  eapply p6u_tapcmp; [exact RD0 | exact RD1 | exact RD2 | exact RD3 | exact RT | |].
  { intros x10 x11 x12 x13 ET. rewrite W4 in ET. zstep. zstep.
    eapply (PROVP 3); [apply p6_rip_tap; [exact NA | exact NM | exact NS | apply OT; exact ET] | pf_lia | exact PM3
      | exact MU3']. }
  intros x10 x11 x12 x13 ET. rewrite W4 in ET.
  assert (NT : strcmp l S_tap <> 0) by (intros H; apply ET; apply OT; exact H).
  (* 0x158ac: the box compare *)
  eapply p6u_boxcmp; [exact RD0 | exact RD1 | exact RD2 | exact RD3 | exact RB | |].
  { intros q10 q11 q12 q13 EB. rewrite W4 in EB. zstep.
    eapply (PROVP 4); [apply p6_rip_box; [exact NA | exact NM | exact NS | exact NT | apply OB; exact EB] | pf_lia
      | exact PM3 | exact MU3']. }
  intros q10 q11 q12 q13 EB. rewrite W4 in EB.
  assert (NB : strcmp l S_box <> 0) by (intros H; apply EB; apply OB; exact H).
  eapply KREFP; [apply p6_rip_none; assumption | exact PM3 | exact MU3'].
Qed.

(** ** S_P6 *)
Theorem pf_p6_holds : bcmp_contract -> S_P6.
Proof.
  intros BC n. split; [apply p6u_role | intros HK HP; exact (p6u_intent n BC HK HP)].
Qed.
