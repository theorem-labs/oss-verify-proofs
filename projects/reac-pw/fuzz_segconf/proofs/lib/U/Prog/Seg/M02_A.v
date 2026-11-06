(* Segment M02 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (UBSan, ELF afc060e3cc9c), piece A (U/Prog/Seg/M02D.v):
   0x13c3c .. 0x13d04.
   check_segments(c = 0x48(sp), m = 0x50(sp), returned = s4) (0x13c48, premise M02_model's check_segments); the
   UBSan trap `ld a0,0x38(sp)` / `bnez` (m & 3 = 0: m is 16-aligned); i = s1 < m->n (`lw a0,0(s11)`, `blez` skips
   the loop for n = 0) with s0 = 256 i, s3 = m + 256 i, s5 = 33, s6 = 0x5a, s7 = c. Each turn (LOOP, by induction
   on the turns left, check_segments.v's form): the traps `beq s1,s5` (i = 33; i < n <= 32) and `bltu s2,s0`
   (s2 = ~m; m + 256 i does not wrap: m + 9236 <= 2^47), `sw s6,0x60(sp)`; reac_segconf_role(c, g->name, sp + 0x60)
   and check_role(a0, `lw` 0x60(sp), g); reac_segconf_model(c, name) and check_model(a0, g); reac_segconf_ignored
   and check_ignore; s4 = reac_segconf_role_file, a1 = reac_segconf_ignore_file, check_provenance(s4, a1, g), each
   premise from M02Bridge (the reader's answers as C strings, the model's entry) and the five conjuncts of
   check_seg rc g (M02_model's forallb); then `lw a0,0(s11)`, i + 1, `blt` back to LOOP or out to 0x13d04.
   Part of the proof of LLVMFuzzerTestOneInput: this file is piece A of segment M02 of its walk; no released proof
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env reac_segconf_find_c
  check_segments_c reac_segconf_role_c check_role_c reac_segconf_model_c check_model_c reac_segconf_ignored_c
  check_ignore_c reac_segconf_role_file_c reac_segconf_ignore_file_c check_provenance_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.Seg Require Import Tac_slot Tac_b1 M02D M02K.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg.M02_bridge.M02Bridge.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.check_segments.CsPure.
Import ListNotations.
Open Scope Z_scope.

Lemma m02a_b2z : forall b, 0 <= b2z b <= 1.
Proof. intros [|]; cbn; lia. Qed.

(* ---- The premises of a turn's callees, at a memory M of the segment ---- *)
Section Turn.
Variables (S c mm cap : Z) (rc : rconf) (mc : mconf) (m0 M : word -> option byte).
Hypothesis HM : M02_mem S c mm cap rc mc m0.
Hypothesis HI : M02_inv S m0 M.
Variable i : nat.
Hypothesis Hi : (i < length (mc_seg mc))%nat.

Lemma m02a_bnd : (length (mc_seg mc) <= 32)%nat /\ 0 <= Z.of_nat i < 32 /\
  0 < mm + 256 * Z.of_nat i /\ mm + 256 * Z.of_nat i + 256 <= S - 65536.
Proof.
  pose proof (m02_bnds S c mm cap rc mc m0 HM) as (_ & HT & H47 & _ & _ & _ & Hm0 & _ & Hm).
  pose proof (proj2 (mb_mconf_n rsegs M mm mc (m02_mconf S c mm cap rc mc m0 M HM HI))) as L32.
  unfold SEG_M_SIZE in Hm. repeat split; lia.
Qed.

Lemma m02a_q : forall depth, 0 <= depth <= 65296 ->
  query_pre depth M (S - 240) (S - 65536) c (mm + 256 * Z.of_nat i) rc (ms_name (nth i (mc_seg mc) mseg_d)).
Proof.
  intros depth Hd. pose proof m02a_bnd as (L32 & Hi32 & Hp & Hpe).
  pose proof (mb_mname rsegs M mm mc i (m02_mconf S c mm cap rc mc m0 M HM HI)
                (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (m02_bnds S c mm cap rc mc m0 HM)))))))))
                Hi) as (Hz & _ & _ & _ & Hl).
  apply (m02_qp S c mm cap rc mc m0 M HM HI); [unfold M02_FRAME; lia | lia | exact Hz |].
  unfold apart, M02_FRAME. left. lia.
Qed.

Lemma m02a_want : (mm + 256 * Z.of_nat i) mod 4 = 0 /\
  mseg_at rsegs M (mm + 256 * Z.of_nat i) (nth i (mc_seg mc) mseg_d) /\
  apart (mm + 256 * Z.of_nat i) MSEG_SIZE (S - 65536) (S - 240).
Proof.
  pose proof m02a_bnd as (L32 & Hi32 & Hp & Hpe).
  pose proof (m02_bnds S c mm cap rc mc m0 HM) as (_ & _ & _ & _ & _ & _ & _ & Hm16 & _).
  split; [Z.div_mod_to_equations; lia|].
  split; [exact (mb_mseg_at rsegs M mm mc i (m02_mconf S c mm cap rc mc m0 M HM HI) Hi)|].
  unfold apart, MSEG_SIZE. left. lia.
Qed.

Lemma m02a_role_pre :
  role_pre M (S - 240) (S - 65536) c (mm + 256 * Z.of_nat i) (S - 240 + 96) rc (ms_name (nth i (mc_seg mc) mseg_d)).
Proof.
  pose proof (m02_bnds S c mm cap rc mc m0 HM) as (H16 & HT & H47 & _).
  split; [apply m02a_q; unfold ROLE_STACK, FIND_STACK; lia|].
  right. split; [Z.div_mod_to_equations; lia|].
  split; [apply (m02_wr S c mm cap rc mc m0 M HM HI); lia|].
  unfold apart. right. lia.
Qed.

End Turn.

Lemma m02a_check_seg : forall rc g, check_seg rc g = true ->
  (match r_role rc (ms_name g) with
   | Some r => ms_role_set g && (r =? ms_role g)
   | None => negb (ms_role_set g)
   end) = true /\
  same_text (r_model rc (ms_name g)) (if ms_model_set g then Some (ms_model g) else None) = true /\
  Bool.eqb (r_ignored rc (ms_name g)) (ms_ignore g) = true /\
  same_text (r_role_file rc (ms_name g)) (if ms_role_set g then Some (ms_role_file g) else None) = true /\
  same_text (r_ignore_file rc (ms_name g)) (if ms_ignore_set g then Some (ms_ignore_file g) else None) = true.
Proof.
  intros rc g H. unfold check_seg in H.
  apply andb_true_iff in H as [H H5]. apply andb_true_iff in H as [H H4].
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  repeat split; assumption.
Qed.

(* ---- LOOP 0x13c74 ---- *)
Section Loop.
Hypothesis RO : reac_segconf_role_contract.
Hypothesis CR : check_role_contract.
Hypothesis MO : reac_segconf_model_contract.
Hypothesis CM : check_model_contract.
Hypothesis IG : reac_segconf_ignored_contract.
Hypothesis CI : check_ignore_contract.
Hypothesis RF : reac_segconf_role_file_contract.
Hypothesis IF : reac_segconf_ignore_file_contract.
Hypothesis CP : check_provenance_contract.
Variables (S c mm cap : Z) (rc : rconf) (mc : mconf) (ret : bool) (m0 : word -> option byte) (gp tp : word)
  (F : bvmap 5 word) (fc : bv 32).
Hypothesis HMod : M02_model rc mc ret.
Hypothesis HM : M02_mem S c mm cap rc mc m0.
Hypothesis FRM : frm0 fc.

Lemma m02a_loop : forall k i (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x24 x25 x26 x28 x29 x30 x31
                              w8 w9 w19 : word) (M : word -> option byte),
  (i + k = length (mc_seg mc))%nat -> (0 < k)%nat -> M02_inv S m0 M ->
  w8 = Z_to_bv 64 (256 * Z.of_nat i) -> w9 = Z_to_bv 64 (Z.of_nat i) -> w19 = Z_to_bv 64 (mm + 256 * Z.of_nat i) ->
  evt rsegs (M02_mid 0x13d04 S mm gp tp m0)
    (MS (mkR x1 (Z_to_bv 64 (S - 240)) gp tp x5 x6 x7 w8 w9 x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (18446744073709551615 - mm)) w19 x20 (Z_to_bv 64 33) (Z_to_bv 64 90) (Z_to_bv 64 c)
             x24 x25 x26 (Z_to_bv 64 (mm + MC_N)) x28 x29 x30 x31)
        F (Z_to_bv 64 0x13c74) fc None M (seg_rom rsegs)).
Proof.
  pose proof (m02_bnds S c mm cap rc mc m0 HM) as (H16 & HT & H47 & Hc0 & Hc16 & Hc & Hm0 & Hm16 & Hm).
  unfold SEG_C_SIZE, SEG_M_SIZE in Hc, Hm.
  pose proof HMod as (_ & HCS & _).
  pose proof HM as (_ & HTM0 & _).
  induction k as [|k IH];
    intros i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x24 x25 x26 x28 x29 x30 x31 w8 w9 w19 M
      Hik Hk HI E8 E9 E19; [lia|].
  subst w8 w9 w19.
  assert (Hi : (i < length (mc_seg mc))%nat) by lia.
  pose proof (m02a_bnd S c mm cap rc mc m0 M HM HI i Hi) as (L32 & Hi32 & Hp & Hpe).
  set (g := nth i (mc_seg mc) mseg_d) in *.
  pose proof (m02a_check_seg rc g (mb_check_seg_nth rc (mc_seg mc) i HCS Hi)) as (CS1 & CS2 & CS3 & CS4 & CS5).
  (* 0x13c74 beq s1,s5 (i = 33); 0x13c78 bltu s2,s0 (m + 256 i wraps): both refuted *)
  m02_show zstep. m02_ntk.
  m02_show zstep. m02_ntk.
  (* 0x13c7c sw s6,0x60(sp) *)
  destruct (m02_cells S c mm cap rc mc m0 M HM HI (S - 240 + 96) 4 ltac:(lia) ltac:(cbn; lia)) as (j & RW).
  destruct HI as (MU & WM & MIv & _).
  unfold M02_W, M02_FRAME in MU.
  m02_show zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?M1 _) => rename M1 into Ms end.
  assert (HIs : M02_inv S m0 Ms) by (apply (m02_inv_of S m0 Ms HTM0 H47 MU WM MIv)).
  clear MU WM MIv.
  (* 0x13c80 addi a2,sp,0x60; 0x13c84 mv a0,s7; 0x13c88 mv a1,s3; 0x13c8c jal reac_segconf_role *)
  m02_show zstep. m02_show zstep. m02_show zstep. m02_show zstep.
  (* The rest of the turn, from check_role's return (0x13c9c) on any later memory. *)
  assert (REST : forall (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word)
                        (m2 : word -> option byte),
    M02_inv S m0 m2 ->
    evt rsegs (M02_mid 0x13d04 S mm gp tp m0)
      (MS (mkR y1 (Z_to_bv 64 (S - 240)) gp tp y5 y6 y7 (Z_to_bv 64 (256 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat i))
               y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (18446744073709551615 - mm))
               (Z_to_bv 64 (mm + 256 * Z.of_nat i)) x20 (Z_to_bv 64 33) (Z_to_bv 64 90) (Z_to_bv 64 c)
               x24 x25 x26 (Z_to_bv 64 (mm + MC_N)) y28 y29 y30 y31)
          F (Z_to_bv 64 0x13c9c) fc None m2 (seg_rom rsegs))).
  { intros y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m2 HI2.
    pose proof (m02a_want S c mm cap rc mc m0 m2 HM HI2 i Hi) as (W4 & WS & WA).
    (* 0x13c9c mv a0,s7; 0x13ca0 mv a1,s3; 0x13ca4 jal reac_segconf_model *)
    m02_show zstep. m02_show zstep. m02_show zstep.
    eapply evt_cut.
    { apply MO with (lo := S - 65536) (rc := rc) (nm := ms_name g).
      m02_show ltac:(rewrite !unsigned_lit by lia;
        apply (m02a_q S c mm cap rc mc m0 m2 HM HI2 i Hi); unfold MODEL_STACK, FIND_STACK; lia). }
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & -> &
                MU & WM & MI & ST & _).
    rewrite ret_pc_even by (try lia; reflexivity).
    m02_show ltac:(rewrite !unsigned_lit in MU by lia).
    assert (HI3 : M02_inv S m0 m3)
      by (apply (m02_inv_step S m0 m2 m3 _ HI2 MU WM MI); unfold MODEL_STACK, FIND_STACK; [m02_subfp | m02_low]).
    clear MU WM MI ST.
    m02_show ltac:(rewrite !(unsigned_lit c) by lia).
    pose proof (m02_rconf S c mm cap rc mc m0 m3 HM HI3) as RC3.
    pose proof (mb_ptr_rng rsegs m3 c rc (ms_name g) RC3 ltac:(lia)) as (PRm & PRr & PRi & _).
    pose proof (mb_model rsegs m3 c rc (ms_name g) RC3 Hc0) as (OZ & OB).
    unfold SEG_C_SIZE in PRm, PRr, PRi, OB.
    pose proof (m02a_want S c mm cap rc mc m0 m3 HM HI3 i Hi) as (_ & WS3 & _).
    (* 0x13ca8 mv a1,s3; 0x13cac jal check_model *)
    m02_show zstep. m02_show zstep.
    eapply evt_cut.
    { apply CM with (lo := S - 65536) (o := r_model rc (ms_name g)) (g := g).
      m02_show ltac:(rewrite !unsigned_lit by lia;
        refine (conj W4 (conj WS3 (conj WA (conj OZ (conj _ (conj CS2 (conj _ _)))))));
        [ destruct (r_model rc (ms_name g)) as [s|] eqn:EM; [unfold apart; left; specialize (OB s eq_refl); lia
                                                           | exact I]
        | apply (m02_stack_ok S c mm cap rc mc m0 m3 HM HI3); unfold CHECK_MODEL_STACK, M02_FRAME; lia
        | exact (m02_mem_inv S m0 m3 HI3) ]). }
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & -> &
                MU & WM & MI & ST & _).
    rewrite ret_pc_even by (try lia; reflexivity).
    m02_show ltac:(rewrite !unsigned_lit in MU by lia).
    assert (HI4 : M02_inv S m0 m4)
      by (apply (m02_inv_step S m0 m3 m4 _ HI3 MU WM MI); unfold CHECK_MODEL_STACK; [m02_subfp | m02_low]).
    clear MU WM MI ST RC3 OZ OB WS3.
    (* 0x13cb0 mv a0,s7; 0x13cb4 mv a1,s3; 0x13cb8 jal reac_segconf_ignored *)
    m02_show zstep. m02_show zstep. m02_show zstep.
    eapply evt_cut.
    { apply IG with (lo := S - 65536) (rc := rc) (nm := ms_name g).
      m02_show ltac:(rewrite !unsigned_lit by lia;
        apply (m02a_q S c mm cap rc mc m0 m4 HM HI4 i Hi); unfold IGNORED_STACK, FIND_STACK; lia). }
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & -> &
                MU & WM & MI & ST & _).
    rewrite ret_pc_even by (try lia; reflexivity).
    m02_show ltac:(rewrite !unsigned_lit in MU by lia).
    assert (HI5 : M02_inv S m0 m5)
      by (apply (m02_inv_step S m0 m4 m5 _ HI4 MU WM MI); unfold IGNORED_STACK, FIND_STACK; [m02_subfp | m02_low]).
    clear MU WM MI ST.
    pose proof (m02a_b2z (r_ignored rc (ms_name g))) as Hb.
    pose proof (m02a_want S c mm cap rc mc m0 m5 HM HI5 i Hi) as (_ & WS5 & _).
    (* 0x13cbc mv a1,s3; 0x13cc0 jal check_ignore *)
    m02_show zstep. m02_show zstep.
    eapply evt_cut.
    { apply CI with (lo := S - 65536) (b := r_ignored rc (ms_name g)) (g := g).
      m02_show ltac:(rewrite !unsigned_lit by lia;
        refine (conj W4 (conj WS5 (conj WA (conj eq_refl (conj CS3 (conj _ _))))));
        [ apply (m02_stack_ok S c mm cap rc mc m0 m5 HM HI5); unfold CHECK_IGNORE_STACK, M02_FRAME; lia
        | exact (m02_mem_inv S m0 m5 HI5) ]). }
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & -> &
                MU & WM & MI & ST & _).
    rewrite ret_pc_even by (try lia; reflexivity).
    assert (HI6 : M02_inv S m0 m6)
      by (apply (m02_inv_step S m0 m5 m6 _ HI5 MU WM MI); [m02_subfp | m02_low]).
    clear MU WM MI ST WS5 Hb.
    (* 0x13cc4 mv a0,s7; 0x13cc8 mv a1,s3; 0x13ccc jal reac_segconf_role_file *)
    m02_show zstep. m02_show zstep. m02_show zstep.
    eapply evt_cut.
    { apply RF with (lo := S - 65536) (rc := rc) (nm := ms_name g).
      m02_show ltac:(rewrite !unsigned_lit by lia;
        apply (m02a_q S c mm cap rc mc m0 m6 HM HI6 i Hi); unfold ROLE_FILE_STACK, FIND_STACK; lia). }
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m7 & -> &
                MU & WM & MI & ST & _).
    rewrite ret_pc_even by (try lia; reflexivity).
    m02_show ltac:(rewrite !unsigned_lit in MU by lia).
    assert (HI7 : M02_inv S m0 m7)
      by (apply (m02_inv_step S m0 m6 m7 _ HI6 MU WM MI); unfold ROLE_FILE_STACK, FIND_STACK;
          [m02_subfp | m02_low]).
    clear MU WM MI ST.
    m02_show ltac:(rewrite !(unsigned_lit c) by lia).
    (* 0x13cd0 mv s4,a0; 0x13cd4 mv a0,s7; 0x13cd8 mv a1,s3; 0x13cdc jal reac_segconf_ignore_file *)
    m02_show zstep. m02_show zstep. m02_show zstep. m02_show zstep.
    eapply evt_cut.
    { apply IF with (lo := S - 65536) (rc := rc) (nm := ms_name g).
      m02_show ltac:(rewrite !unsigned_lit by lia;
        apply (m02a_q S c mm cap rc mc m0 m7 HM HI7 i Hi); unfold IGNORE_FILE_STACK, FIND_STACK; lia). }
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m8 & -> &
                MU & WM & MI & ST & _).
    rewrite ret_pc_even by (try lia; reflexivity).
    m02_show ltac:(rewrite !unsigned_lit in MU by lia).
    assert (HI8 : M02_inv S m0 m8)
      by (apply (m02_inv_step S m0 m7 m8 _ HI7 MU WM MI); unfold IGNORE_FILE_STACK, FIND_STACK;
          [m02_subfp | m02_low]).
    clear MU WM MI ST.
    m02_show ltac:(rewrite !(unsigned_lit c) by lia).
    pose proof (m02_rconf S c mm cap rc mc m0 m8 HM HI8) as RC8.
    pose proof (mb_role_file rsegs m8 c rc (ms_name g) RC8 Hc0) as (OZr & OBr).
    pose proof (mb_ignore_file rsegs m8 c rc (ms_name g) RC8 Hc0) as (OZi & OBi).
    unfold SEG_C_SIZE in OBr, OBi.
    pose proof (m02a_want S c mm cap rc mc m0 m8 HM HI8 i Hi) as (_ & WS8 & _).
    (* 0x13ce0 mv a1,a0; 0x13ce4 mv a0,s4; 0x13ce8 mv a2,s3; 0x13cec jal check_provenance *)
    m02_show zstep. m02_show zstep. m02_show zstep. m02_show zstep.
    eapply evt_cut.
    { apply CP with (lo := S - 65536) (orf := r_role_file rc (ms_name g)) (oif := r_ignore_file rc (ms_name g))
        (g := g).
      m02_show ltac:(rewrite !unsigned_lit by lia;
        refine (conj W4 (conj WS8 (conj WA (conj OZr (conj _ (conj OZi (conj _ (conj CS4 (conj CS5
          (conj _ _))))))))));
        [ destruct (r_role_file rc (ms_name g)) as [s|] eqn:EM; [unfold apart; left; specialize (OBr s eq_refl); lia
                                                               | exact I]
        | destruct (r_ignore_file rc (ms_name g)) as [s|] eqn:EM; [unfold apart; left; specialize (OBi s eq_refl); lia
                                                                 | exact I]
        | apply (m02_stack_ok S c mm cap rc mc m0 m8 HM HI8); unfold CHECK_PROVENANCE_STACK, M02_FRAME; lia
        | exact (m02_mem_inv S m0 m8 HI8) ]). }
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m9 & -> &
                MU & WM & MI & ST & _).
    rewrite ret_pc_even by (try lia; reflexivity).
    m02_show ltac:(rewrite !unsigned_lit in MU by lia).
    assert (HI9 : M02_inv S m0 m9)
      by (apply (m02_inv_step S m0 m8 m9 _ HI8 MU WM MI); unfold CHECK_PROVENANCE_STACK; [m02_subfp | m02_low]).
    clear MU WM MI ST RC8 OZr OBr OZi OBi WS8.
    (* the latch: 0x13cf0 lw a0,0(s11) = m->n; s1 = i + 1; s3, s0 += 256; 0x13d00 blt s1,a0 *)
    pose proof (mb_mconf_n rsegs m9 mm mc (m02_mconf S c mm cap rc mc m0 m9 HM HI9)) as (RN & _).
    m02_show zstep. clear RN.
    m02_show ltac:(rewrite (sx32_small (Z.of_nat (length (mc_seg mc)))) by lia).
    m02_show zstep. m02_show zstep. m02_show zstep. m02_show zstep.
    destruct k as [|k].
    - (* i + 1 = n: out to 0x13d04 *)
      m02_ntk.
      rewrite <- (m02_not_lit mm) by lia.
      apply evt_done. unfold M02_mid. do 29 eexists.
      m02_show ltac:(split; [reflexivity|]). split; [exact FRM | exact HI9].
    - m02_tkn.
      m02_show ltac:(eapply (IH (Datatypes.S i)); [lia | lia | exact HI9 | f_equal; lia | f_equal; lia
                                                   | f_equal; lia]). }
  destruct (r_role rc (ms_name g)) as [v|] eqn:ER.
  - (* the role is set: 1, and *out = v *)
    pose proof (mb_role_rng rsegs Ms c rc (ms_name g) v (m02_rconf S c mm cap rc mc m0 Ms HM HIs) ER) as Hv.
    eapply evt_cut.
    { apply RO with (lo := S - 65536) (rc := rc) (nm := ms_name g).
      m02_show ltac:(rewrite !unsigned_lit by lia; exact (m02a_role_pre S c mm cap rc mc m0 Ms HM HIs i Hi)). }
    intros ms' PO. unfold ret_post, role_W, ROLE_STACK, FIND_STACK in PO. rewrite ER in PO.
    m02_show ltac:(rewrite !unsigned_lit in PO by lia).
    rewrite (proj2 (Z.eqb_neq (S - 240 + 96) 0)) in PO by lia.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m1 & -> &
                    MU & WM & MI & ST & QR).
    rewrite ret_pc_even by (try lia; reflexivity).
    assert (HI1 : M02_inv S m0 m1)
      by (apply (m02_inv_step S m0 Ms m1 _ HIs MU WM MI); [m02_subfp | m02_low]).
    pose proof (m02_ld4 _ _ _ (QR ltac:(lia))) as RL.
    clear MU WM MI ST QR HIs RW.
    (* 0x13c90 lw a1,0x60(sp); 0x13c94 mv a2,s3; 0x13c98 jal check_role *)
    m02_show zstep. clear RL.
    m02_show ltac:(rewrite (sx32_small v) by lia).
    m02_show zstep. m02_show zstep.
    pose proof (m02a_want S c mm cap rc mc m0 m1 HM HI1 i Hi) as (W4 & WS & WA).
    try rewrite ER in CS1.
    eapply evt_cut.
    { apply CR with (lo := S - 65536) (o := Some v) (g := g).
      m02_show ltac:(rewrite !unsigned_lit by lia;
        refine (conj W4 (conj WS (conj WA (conj eq_refl (conj (conj eq_refl (proj2 Hv)) (conj CS1 (conj _ _)))))));
        [ apply (m02_stack_ok S c mm cap rc mc m0 m1 HM HI1); unfold CHECK_ROLE_STACK, M02_FRAME; lia
        | exact (m02_mem_inv S m0 m1 HI1) ]). }
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> &
                MU & WM & MI & ST & _).
    rewrite ret_pc_even by (try lia; reflexivity).
    apply REST. apply (m02_inv_step S m0 m1 m2 _ HI1 MU WM MI); [m02_subfp | m02_low].
  - (* the role is not set: 0, and r keeps 0x5a *)
    eapply evt_cut.
    { apply RO with (lo := S - 65536) (rc := rc) (nm := ms_name g).
      m02_show ltac:(rewrite !unsigned_lit by lia; exact (m02a_role_pre S c mm cap rc mc m0 Ms HM HIs i Hi)). }
    intros ms' PO. unfold ret_post, role_W, ROLE_STACK, FIND_STACK in PO. rewrite ER in PO.
    m02_show ltac:(rewrite !unsigned_lit in PO by lia).
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m1 & -> &
                    MU & WM & MI & ST & _).
    rewrite ret_pc_even by (try lia; reflexivity).
    assert (HI1 : M02_inv S m0 m1)
      by (apply (m02_inv_step S m0 Ms m1 _ HIs MU WM MI); [m02_subfp | m02_low]).
    pose proof (rw_cells_transport rsegs _ _ _ _ _ RW MU WM
                  ltac:(cbn [disjoint_from cells_size csize]; split; [lia | exact I])) as RW1.
    pose proof (sl_cells_bytes _ _ _ RW1) as RB. cbn [cells_bytes cbytes] in RB. rewrite app_nil_r in RB.
    pose proof (m02_ld4 _ _ _ RB) as RL.
    clear MU WM MI ST HIs RW RW1 RB.
    (* 0x13c90 lw a1,0x60(sp); 0x13c94 mv a2,s3; 0x13c98 jal check_role *)
    m02_show zstep. clear RL.
    m02_show ltac:(rewrite (sx32_small 90) by lia).
    m02_show zstep. m02_show zstep.
    pose proof (m02a_want S c mm cap rc mc m0 m1 HM HI1 i Hi) as (W4 & WS & WA).
    try rewrite ER in CS1.
    eapply evt_cut.
    { apply CR with (lo := S - 65536) (o := None) (g := g).
      m02_show ltac:(rewrite !unsigned_lit by lia;
        refine (conj W4 (conj WS (conj WA (conj eq_refl (conj I (conj CS1 (conj _ _)))))));
        [ apply (m02_stack_ok S c mm cap rc mc m0 m1 HM HI1); unfold CHECK_ROLE_STACK, M02_FRAME; lia
        | exact (m02_mem_inv S m0 m1 HI1) ]). }
    intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> &
                MU & WM & MI & ST & _).
    rewrite ret_pc_even by (try lia; reflexivity).
    apply REST. apply (m02_inv_step S m0 m1 m2 _ HI1 MU WM MI); [m02_subfp | m02_low].
Qed.

End Loop.

Theorem m02_A : check_segments_contract -> reac_segconf_role_contract -> check_role_contract ->
  reac_segconf_model_contract -> check_model_contract -> reac_segconf_ignored_contract -> check_ignore_contract ->
  reac_segconf_role_file_contract -> reac_segconf_ignore_file_contract -> check_provenance_contract -> M02_A_stmt.
Proof.
  intros CSG RO CR MO CM IG CI RF IF CP. unfold M02_A_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m0 S c mm cap rc mc ret Esp E2 E11 E4 FRM HMod HM.
  subst sp s2 s11 s4. unfold M02_FRAME.
  pose proof (m02_bnds S c mm cap rc mc m0 HM) as (H16 & HT & H47 & Hc0 & Hc16 & Hc & Hm0 & Hm16 & Hm).
  unfold SEG_C_SIZE, SEG_M_SIZE in Hc, Hm.
  pose proof HMod as (HSG & _).
  pose proof HM as (_ & HTM0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & C38 & _).
  pose proof (m02_inv_refl _ _ _ _ _ _ _ HM) as HI0.
  pose proof (m02a_b2z ret) as Hb.
  rewrite (m02_not_lit mm) by lia.
  (* 0x13c3c ld a0,0x48(sp); 0x13c40 ld a1,0x50(sp); 0x13c44 mv a2,s4; 0x13c48 jal check_segments *)
  pose proof (b1_ld8 _ _ _ (m02_cellc S c mm cap rc mc m0 m0 HM HI0)) as RC. unfold M02_FRAME in RC.
  pose proof (b1_ld8 _ _ _ (m02_cellm S c mm cap rc mc m0 m0 HM HI0)) as RM. unfold M02_FRAME in RM.
  m02_show zstep. m02_show zstep. m02_show zstep. m02_show zstep.
  clear RC RM.
  eapply evt_cut.
  { apply CSG with (lo := S - 65536) (rc := rc) (mc := mc) (ret := ret).
    rewrite !unsigned_lit by lia. unfold check_segments_pre.
    split; [lia|]. split; [exact Hc16|]. split; [exact (m02_rconf S c mm cap rc mc m0 m0 HM HI0)|].
    split; [unfold apart, SEG_C_SIZE; left; lia|]. split; [lia|]. split; [exact Hm16|].
    split; [exact (m02_mconf S c mm cap rc mc m0 m0 HM HI0)|]. split; [unfold apart, SEG_M_SIZE; left; lia|].
    split; [reflexivity|]. split; [exact HSG|].
    split; [apply (m02_stack_ok S c mm cap rc mc m0 m0 HM HI0); unfold CHECK_SEGMENTS_STACK, M02_FRAME; lia|].
    exact (m02_mem_inv S m0 m0 HI0). }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m1 & -> &
              MU & WM & MI & ST & _).
  rewrite ret_pc_even by (try lia; reflexivity).
  m02_show ltac:(rewrite !unsigned_lit in MU by lia).
  assert (HI1 : M02_inv S m0 m1)
    by (apply (m02_inv_step S m0 m0 m1 _ HI0 MU WM MI); unfold CHECK_SEGMENTS_STACK; [m02_subfp | m02_low]).
  assert (B38 : bytes_at rsegs m1 (S - 240 + 0x38) (le8 (Z_to_bv 64 0))).
  { replace 0 with (mm mod 4) by (Z.div_mod_to_equations; lia).
    apply (bytes_at_transport rsegs _ _ _ _ _ C38 MU). rewrite length_le8. unfold M02_FRAME, CHECK_SEGMENTS_STACK.
    cbn [disjoint_from]. split; [lia | exact I]. }
  clear MU WM MI ST C38.
  (* 0x13c4c ld a0,0x38(sp); 0x13c50 bnez a0 (m & 3 <> 0 traps) *)
  pose proof (b1_ld8 _ _ _ B38) as R38.
  m02_show zstep. clear R38 B38. m02_show zstep. m02_ntk.
  (* 0x13c54 lw a0,0(s11) = m->n; 0x13c58 blez a0 *)
  pose proof (mb_mconf_n rsegs m1 mm mc (m02_mconf S c mm cap rc mc m0 m1 HM HI1)) as (RN & L32).
  m02_show zstep. clear RN.
  m02_show ltac:(rewrite (sx32_small (Z.of_nat (length (mc_seg mc)))) by lia).
  m02_show zstep.
  destruct (Nat.eq_dec (length (mc_seg mc)) 0) as [N0|N0].
  - (* n = 0: to 0x13d04 *)
    m02_tkn.
    rewrite <- (m02_not_lit mm) by lia.
    apply evt_done. unfold M02_mid. do 29 eexists.
    m02_show ltac:(split; [reflexivity|]). split; [exact FRM | exact HI1].
  - m02_ntk.
    (* 0x13c5c s0 = 0; s1 = 0; s5 = 33; s6 = 0x5a; 0x13c6c ld s3,0x50(sp) = m; 0x13c70 ld s7,0x48(sp) = c *)
    pose proof (b1_ld8 _ _ _ (m02_cellc S c mm cap rc mc m0 m1 HM HI1)) as RC. unfold M02_FRAME in RC.
    pose proof (b1_ld8 _ _ _ (m02_cellm S c mm cap rc mc m0 m1 HM HI1)) as RM. unfold M02_FRAME in RM.
    m02_show zstep. m02_show zstep. m02_show zstep. m02_show zstep. m02_show zstep. m02_show zstep.
    clear RC RM.
    m02_show ltac:(eapply (m02a_loop RO CR MO CM IG CI RF IF CP S c mm cap rc mc ret m0 gp tp F fc HMod HM FRM
                            (length (mc_seg mc)) 0%nat);
      [lia | lia | exact HI1 | f_equal; lia | f_equal; lia | f_equal; lia]).
Qed.
