(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Spec/StrFun.v; 283 of its 315 lines of code are new or changed and 432 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the straight-line segments of reac-repacer/fuzz_wire's check_forward in image A, in the form
   and with the helpers of reac-repacer/fuzz_uci's lib/A/Prog/UciCvSegs.v (cv_c8s, cv_rw_c8s, cv_frame_words, cv_rd_all,
   cv_regs, cv_usub, cv_shift, cv_w, cv_finF, cv_memF, cv_lit) and the guarded shadow-checked byte reads of
   proofs/libreac/fuzz_decode/lib/A/Prog/reac_frame_is_reac_F.v (commit 88154566652a), the model steps
   of the plain walk lib/Prog/check_forward.v (eqb_facts, fwd_eval, fwd_done, fwd_audio). *)
(* WireCfSegs: the footprint (ExecF.evtF) runs of check_forward (fuzz_wire.asan 0x7fff0 = wire_sigma WS_check_forward),
   stepped by lib/Lib/StepF.v, split at its one call:
     cf_seg1_F  entry -> rp_fwd_class (0x80ec4, ra = CF_RET): the 0x30-byte frame (s3, s2, s1, s0, ra at 8(sp) ..
                0x28(sp)), s1 := bcast, s2 := n, the shadow base through GOT_CELL_K -> CELL_K into s3, s0 := f,
                a1 := n again;
     cf_tail_F  CF_RET -> the return: when n >= 18 the reads of f[12], f[13], f[0] (only when bcast <> 0), f[16],
                f[17], each after its shadow byte (the report arms are not taken: addressable), the want of
                fuzz_wire.c:50-70 computed into a1, the `bne a0, a1` not taken (a0 holds rp_fwd_class's result,
                lib/Prog/rp_fwd_class_c.v fwd_class_result, the want), ra and s0 .. s3 reloaded, sp += 0x30, `ret`. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import AsanKA AsanKAProof.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import WirePSyms WirePAddr.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require rp_fwd_class_F_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_fwd_class_c.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.
Module PFC := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_fwd_class_c.
Module LFF := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog.rp_fwd_class_F_c.

(* The entry, the one call (rp_fwd_class, the leaf's entry of lib/A/Prog/rp_fwd_class_F_c.v) and its return. *)
Definition CF_ENTRY : Z := wire_sigma WS_check_forward.
Definition CF_AT (off : Z) : Z := CF_ENTRY + off.
Definition CF_LEAF : Z := LFF.RP_FWD_CLASS.
Definition CF_RET : Z := CF_AT 0x38.

(* The frame: the caller's s3, s2, s1, s0, ra at 8(sp) .. 0x28(sp) of the 0x30-byte frame. *)
Definition cf_fr (c3 c2 c1 c0 cra : word) : list cell := [C8 c3; C8 c2; C8 c1; C8 c0; C8 cra].

(* ---- helpers (UciCvSegs.v:29-124) ---- *)

Lemma cf_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (byte_range b) as Hb.
  assert (HR : 0 <= bytes_le_to_Z bs). { rewrite bytes_le_to_Z_le_val. apply (proj1 (le_val_range _ (bytes_ok_map bs))). }
  rewrite lor_shiftl8_add by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8)%Z. change (2^8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.div_add, Z.div_small by lia. cbn [Z.add]. exact IH.
Qed.

Lemma cf_le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z_to_le_bytes_mod by lia.
  rewrite <- L at 1. apply cf_le_bytes_to_Z.
Qed.

Fixpoint cf_c8s (n : nat) (bs : list byte) : list cell :=
  match n with
  | O => []
  | S n' => C8 (Z_to_bv 64 (bytes_le_to_Z (firstn 8 bs))) :: cf_c8s n' (skipn 8 bs)
  end.

Lemma cf_c8s_spec : forall n bs, length bs = (8 * n)%nat ->
  cells_wf (cf_c8s n bs) /\ cells_bytes (cf_c8s n bs) = bs /\ cells_size (cf_c8s n bs) = (8 * n)%nat.
Proof.
  induction n as [|n IH]; intros bs L.
  - destruct bs; [|cbn in L; lia]. cbn. auto.
  - cbn [cf_c8s cells_wf cells_bytes cells_size cell_wf cbytes csize].
    assert (L8 : length (firstn 8 bs) = 8%nat) by (rewrite length_firstn; lia).
    assert (LS : length (skipn 8 bs) = (8 * n)%nat) by (rewrite length_skipn; lia).
    destruct (IH _ LS) as (W & B & S).
    split; [split; [exact I | exact W]|]. split; [|lia].
    rewrite cf_le8_of_bytes, B by exact L8. apply firstn_skipn.
Qed.

Lemma cf_rw_c8s : forall segs m A n bs, rw_cells segs m A [CB (8 * n) bs] -> rw_cells segs m A (cf_c8s n bs).
Proof.
  intros segs m A n bs [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [L _].
  destruct (cf_c8s_spec n bs L) as (W & B & S).
  split; [split|].
  - exact W.
  - rewrite B. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
  - rewrite S. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw. exact Hw.
Qed.

(* The carved 48 bytes, read as 6 words. *)
Lemma cf_frame_words : forall m A bs, rw_cells rsegs m A [CB 48 bs] ->
  exists v0 v8 v16 v24 v32 v40 : word,
    rw_cells rsegs m A [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40].
Proof.
  intros m A bs H. apply (cf_rw_c8s rsegs m A 6 bs) in H. cbn [cf_c8s] in H. do 6 eexists. exact H.
Qed.

Lemma cf_rd_all : forall m A bs, bytes_at rsegs m A bs ->
  ov_read_bytes rsegs m (Z_to_bv 64 A) (length bs) = Some bs.
Proof.
  intros m A bs H. change (Z_to_bv 64 A) with (wa A). replace A with (A + Z.of_nat 0) at 1 by lia.
  rewrite (bytes_at_ov_read rsegs m A bs 0 (length bs) H) by lia. cbn [skipn]. rewrite firstn_all. reflexivity.
Qed.

(* The shadow byte of a + i, 0 <= i < n, lies in the shadow range of [a, a + n) (reac_frame_is_reac_F.v
   is_reac_shadow_byte_rng). *)
Lemma cf_shadow_byte_rng : forall RNG a n i, 0 <= i < n ->
  ExecF.rng RNG (shadow_addr a) (shadow_addr (a + n - 1) - shadow_addr a + 1) ->
  ExecF.rng RNG (shadow_addr (a + i)) 1.
Proof.
  intros RNG a n i Hi H. eapply rng_sub'; [exact H|]. unfold shadow_addr. Z.div_mod_to_equations. lia.
Qed.

Ltac cf_regs := unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end.
Ltac cf_usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by nia end.
Ltac cf_shift := rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia.
Ltac cf_w := cf_shift; cf_usub; cf_shift; cf_usub;
  first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; f_equal; lia
        | f_equal; Z.div_mod_to_equations; nia ].
Ltac cf_memF k := lazymatch goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mm _) => k mm end.
(* StepF's step reads the start pc: each proof first computes every closed name of its goal to its value. *)
Ltac cf_lit X := let v := eval vm_compute in X in change X with v.
Ltac cf_lits :=
  repeat match goal with
  | |- context [CF_RET] => cf_lit CF_RET
  | |- context [CF_LEAF] => cf_lit CF_LEAF
  | |- context [CF_AT ?o] => cf_lit (CF_AT o)
  | |- context [CF_ENTRY] => cf_lit CF_ENTRY
  end.

(* ---- cf_seg1_F: CF_ENTRY -> rp_fwd_class (ra = CF_RET) ---- *)
Lemma cf_seg1_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n bc lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp ->
    bytes_at rsegs m GOT_CELL_K (le8 (wa CELL_K)) -> bytes_at rsegs m CELL_K (le8 (wa ASAN_K)) ->
    CELL_K + 8 <= bv_unsigned sp - 48 ->
    ExecF.rng RNG (bv_unsigned sp - 48) 48 -> ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m1 v0,
         ms' = MS (mkR (Z_to_bv 64 CF_RET) (Z_to_bv 64 (bv_unsigned sp - 48)) gp tp t0 t1 t2
                    (Z_to_bv 64 f) (Z_to_bv 64 bc) (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 bc) a3 a4 a5 a6 a7
                    (Z_to_bv 64 n) (Z_to_bv 64 ASAN_K) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CF_LEAF) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
         rw_cells rsegs m1 (bv_unsigned sp - 48) (C8 v0 :: cf_fr s3 s2 s1 s0 ra))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 bc) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CF_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f n bc lo
    ST LO GCK CK HLOW RFR RGC RCK.
  cf_lits.
  unfold GOT_CELL_K in RGC, GCK, HLOW. unfold CELL_K in RCK, GCK, CK, HLOW.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  destruct (cf_frame_words _ _ _ FR) as (v0 & v8 & v16 & v24 & v32 & v40 & FR'). clear FR.
  rename FR' into FR.
  do 6 step.
  (* the stores moved the two cell facts to the new memory (StepF's store transport) *)
  unfold ASAN_K in CK.
  pose proof (cf_rd_all _ _ _ GCK) as RDG. rewrite length_le8 in RDG.
  pose proof (cf_rd_all _ _ _ CK) as RDS. rewrite length_le8 in RDS.
  do 8 step.
  cf_memF ltac:(fun mm => apply evtF_done; exists mm, v0).
  replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia.
  split; [|split; [exact MU|split; [exact WM|exact FR]]].
  f_equal; cf_regs; try cf_w.
Qed.

(* ---- cf_tail_F: CF_RET -> the return ---- *)

(* Each test of the model whose answer a path fixed (lib/Prog/check_forward.v eqb_facts, fwd_eval). *)
Ltac cf_eqb_facts := repeat match goal with
  | |- context [Z.eqb ?x ?c] =>
      first [ rewrite (proj2 (Z.eqb_eq x c)) by lia | rewrite (proj2 (Z.eqb_neq x c)) by lia ]
  end.
Ltac cf_fwd_eval :=
  cbv beta iota zeta delta [PFC.fwd_class_result PFC.fwd_byte];
  first [ rewrite (proj2 (Z.ltb_lt _ _)) by lia | rewrite (proj2 (Z.ltb_ge _ _)) by lia ];
  cf_eqb_facts; cbn [andb orb negb]; reflexivity.
Ltac cf_byte_cond H := zify_cond H; rewrite ?zxb_u in H.

(* +0xa4 `bne a0, a1` .. +0xc0 `ret`, with a1 = v, the want, and the model rewritten to it. *)
Ltac cf_done v :=
  lazymatch goal with |- context [PFC.fwd_class_result ?n ?b ?bs] =>
    replace (PFC.fwd_class_result n b bs) with v by cf_fwd_eval end;
  step; if_false;
  do 7 step;
  apply evtF_done; do 3 eexists; first [reflexivity | f_equal].

(* A shadow byte k that allows its byte, at the `bnez` on it: k = 0 falls through; otherwise the `andi` into reg /
   `blt` of the partial granule return to the load (reac_frame_is_reac_F.v). Both arms reach the load with only reg
   changed, so the walk goes on from one goal, K, with reg (the variable in a3) generalized under the name a3. *)
Ltac cf_chk SK U MB k reg :=
  lazymatch goal with
  | |- ExecF.evtF ?s ?RNG ?Q (MS ?R ?F (if _ then _ else ?pE) ?fc ?rv ?m ?ro) =>
      let Rf := eval pattern reg in R in
      lazymatch Rf with
      | ?g reg =>
        let K := fresh "K" in
        assert (K : forall x : word, ExecF.evtF s RNG Q (MS (g x) F pE fc rv m ro));
        [ clear reg; let x := fresh "a3" in intro x; cbv beta
        | let C := fresh "C" in let Cu := fresh "Cu" in destruct SK as [C|[C Cu]];
          [ rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]; exact (K reg)
          | rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb]; step; step;
            rewrite land7, ?U, (lts_low _ k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb]; apply K ] ]
      end
  end.

(* The same check where the partial granule's `andi` writes a2 (f[0], f[17]): both arms are walked on. *)
Ltac cf_shchk SK U MB k :=
  let C := fresh "C" in let Cu := fresh "Cu" in destruct SK as [C|[C Cu]];
  [ rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]
  | rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb]; step; step;
    rewrite land7, ?U, (lts_low _ k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb] ].

(* +0xe0 (0x800d0, f[17]): `addi s0, s0, 17`, its shadow byte, the byte, `beqz a1` to AUDIO (1), else CTRL (2). *)
Ltac cf_f17 wf m RBUF RS MK SK MB k FB :=
  let w := fresh "w17" in let g := fresh "g17" in let h := fresh "h17" in
  let U := fresh "U17" in let G := fresh "G17" in let H := fresh "H17" in
  let RW := fresh "RW17" in let RH := fresh "RH17" in let R := fresh "R" in
  step; gen_addi wf w U;
  pose proof (rng_sub' _ _ _ (bv_unsigned w) 1 RBUF ltac:(lia)) as RW;
  step; gen_shr w g G; rewrite U in G;
  step; gen_addi g h H;
  pose proof (rng_sub' _ _ _ (bv_unsigned h) 1 RS ltac:(lia)) as RH;
  pose proof (rdw0 m h _ _ MK ltac:(lia)) as R; step; clear R;
  step;
  cf_shchk SK U MB k;
  (pose proof (rdw0 m w _ _ FB ltac:(lia)) as R; step; clear R;
   step; let HC := fresh "HC" in if_cases HC;
   [ cf_byte_cond HC; do 2 step; cf_done 1 | cf_byte_cond HC; do 2 step; cf_done 2 ]).

(* +0xc4 (0x800b4, f[16]): its shadow byte, the byte, `bnez a1` to CTRL (2), else f[17]. *)
Ltac cf_audio wf m RBUF a3 RS MK SK MB k FB RS' MK' SK' MB' k' FB' :=
  let w := fresh "w16" in let g := fresh "g16" in let h := fresh "h16" in
  let U := fresh "U16" in let G := fresh "G16" in let H := fresh "H16" in
  let RW := fresh "RW16" in let RH := fresh "RH16" in let R := fresh "R" in
  step; gen_addi wf w U;
  pose proof (rng_sub' _ _ _ (bv_unsigned w) 1 RBUF ltac:(lia)) as RW;
  step; gen_shr w g G; rewrite U in G;
  step; gen_addi g h H;
  pose proof (rng_sub' _ _ _ (bv_unsigned h) 1 RS ltac:(lia)) as RH;
  pose proof (rdw0 m h _ _ MK ltac:(lia)) as R; step; clear R;
  step;
  cf_chk SK U MB k a3;
  pose proof (rdw0 m w _ _ FB ltac:(lia)) as R; step; clear R;
  step; let HC := fresh "HC" in if_cases HC;
  [ cf_byte_cond HC; do 2 step; cf_done 2 | cf_byte_cond HC; cf_f17 wf m RBUF RS' MK' SK' MB' k' FB' ].

Lemma cf_tail_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v0 c3 c2 c1 c0 cra wf wn wb : word)
         (bs : list byte),
    rw_cells rsegs m (bv_unsigned sp) (C8 v0 :: cf_fr c3 c2 c1 c0 cra) ->
    bv_unsigned sp + 48 < 2 ^ 64 ->
    ExecF.rng RNG (bv_unsigned sp) 48 ->
    (18 <= bv_unsigned wn ->
       (18 <= length bs)%nat /\ bytes_at rsegs m (bv_unsigned wf) bs /\ addressable m (bv_unsigned wf) 18 /\
       ExecF.rng RNG (bv_unsigned wf) 18 /\
       ExecF.rng RNG (shadow_addr (bv_unsigned wf))
         (shadow_addr (bv_unsigned wf + 18 - 1) - shadow_addr (bv_unsigned wf) + 1)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists a1' a2' a3' : word,
         ms' = MS (mkR cra (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0 t1 t2 c0 c1
                    (Z_to_bv 64 (PFC.fwd_class_result (bv_unsigned wn) (bv_unsigned wb) bs)) a1' a2' a3'
                    a4 a5 a6 a7 c2 c3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc cra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 wf wb (Z_to_bv 64 (PFC.fwd_class_result (bv_unsigned wn) (bv_unsigned wb) bs))
               a1 a2 a3 a4 a5 a6 a7 wn (Z_to_bv 64 ASAN_K) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CF_RET) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    v0 c3 c2 c1 c0 cra wf wn wb bs FR HSP RFR HB.
  cf_lits. unfold ASAN_K.
  unfold cf_fr in FR. pose proof (rw_cells_bound _ _ _ _ FR) as HFB. cbn [cells_size csize Nat.add] in HFB.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word wf) as Rwf. unfold inr64 in Rwf.
  pose proof (zr_word wn) as Rwn. unfold inr64 in Rwn.
  pose proof (zr_word wb) as Rwb. unfold inr64 in Rwb.
  step. step. if_cases HL.
  - (* n < 18: DROP *)
    zify_cond HL. step. cf_done 0.
  - zify_cond HL.
    destruct (HB HL) as (LEN & BA & ADR & RBUF & RSH). clear HB.
    pose proof (cf_shadow_byte_rng RNG (bv_unsigned wf) 18 0 ltac:(lia) RSH) as RS0.
    pose proof (cf_shadow_byte_rng RNG (bv_unsigned wf) 18 12 ltac:(lia) RSH) as RS12.
    pose proof (cf_shadow_byte_rng RNG (bv_unsigned wf) 18 13 ltac:(lia) RSH) as RS13.
    pose proof (cf_shadow_byte_rng RNG (bv_unsigned wf) 18 16 ltac:(lia) RSH) as RS16.
    pose proof (cf_shadow_byte_rng RNG (bv_unsigned wf) 18 17 ltac:(lia) RSH) as RS17.
    rewrite Z.add_0_r in RS0. clear RSH.
    destruct ADR as (P0 & N0 & PE & AB).
    destruct (AB 0 ltac:(lia)) as (APP0 & k0 & MK0 & SK0).
    destruct (AB 12 ltac:(lia)) as (APP12 & k12 & MK12 & SK12).
    destruct (AB 13 ltac:(lia)) as (APP13 & k13 & MK13 & SK13).
    destruct (AB 16 ltac:(lia)) as (APP16 & k16 & MK16 & SK16).
    destruct (AB 17 ltac:(lia)) as (APP17 & k17 & MK17 & SK17).
    clear AB.
    rewrite Z.add_0_r in APP0, MK0, SK0.
    unfold shadow_addr, shadow_ok, ASAN_K in *.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in APP0, APP12, APP13, APP16, APP17, PE.
    pose proof (bytes_nth m _ bs 0 BA ltac:(lia)) as F0.
    pose proof (bytes_nth m _ bs 12 BA ltac:(lia)) as F12.
    pose proof (bytes_nth m _ bs 13 BA ltac:(lia)) as F13.
    pose proof (bytes_nth m _ bs 16 BA ltac:(lia)) as F16.
    pose proof (bytes_nth m _ bs 17 BA ltac:(lia)) as F17.
    change (Z.of_nat 0) with 0 in F0. rewrite Z.add_0_r in F0.
    change (Z.of_nat 12) with 12 in F12. change (Z.of_nat 13) with 13 in F13.
    change (Z.of_nat 16) with 16 in F16. change (Z.of_nat 17) with 17 in F17.
    pose proof (Z.mod_pos_bound (bv_unsigned wf) 8 ltac:(lia)) as MB0.
    pose proof (Z.mod_pos_bound (bv_unsigned wf + 12) 8 ltac:(lia)) as MB12.
    pose proof (Z.mod_pos_bound (bv_unsigned wf + 13) 8 ltac:(lia)) as MB13.
    pose proof (Z.mod_pos_bound (bv_unsigned wf + 16) 8 ltac:(lia)) as MB16.
    pose proof (Z.mod_pos_bound (bv_unsigned wf + 17) 8 ltac:(lia)) as MB17.
    (* f[12] *)
    step. gen_addi wf w12 U12.
    pose proof (rng_sub' _ _ _ (bv_unsigned w12) 1 RBUF ltac:(lia)) as RW12.
    step. gen_shr w12 g12 G12. rewrite U12 in G12.
    step. gen_addi g12 h12 H12.
    pose proof (rng_sub' _ _ _ (bv_unsigned h12) 1 RS12 ltac:(lia)) as RH12.
    pose proof (rdw0 m h12 _ _ MK12 ltac:(lia)) as R. step. clear R.
    step.
    cf_chk SK12 U12 MB12 k12 a3.
    pose proof (rdw0 m w12 _ _ F12 ltac:(lia)) as R. step. clear R.
    step. step. if_cases H12c.
    { cf_byte_cond H12c. step. cf_done 0. }
    cf_byte_cond H12c.
    (* f[13] *)
    step. gen_addi wf w13 U13.
    pose proof (rng_sub' _ _ _ (bv_unsigned w13) 1 RBUF ltac:(lia)) as RW13.
    step. gen_shr w13 g13 G13. rewrite U13 in G13.
    step. gen_addi g13 h13 H13.
    pose proof (rng_sub' _ _ _ (bv_unsigned h13) 1 RS13 ltac:(lia)) as RH13.
    pose proof (rdw0 m h13 _ _ MK13 ltac:(lia)) as R. step. clear R.
    step.
    cf_chk SK13 U13 MB13 k13 a3.
    pose proof (rdw0 m w13 _ _ F13 ltac:(lia)) as R. step. clear R.
    step. step. if_cases H13c.
    { cf_byte_cond H13c. step. cf_done 0. }
    cf_byte_cond H13c.
    (* bcast = 0: f[16] (and f[17]) *)
    step. if_cases HBc.
    { cf_byte_cond HBc. cf_audio wf m RBUF a3 RS16 MK16 SK16 MB16 k16 F16 RS17 MK17 SK17 MB17 k17 F17. }
    cf_byte_cond HBc.
    (* f[0] *)
    step. gen_shr wf g0 G0.
    step. gen_addi g0 h0 H0.
    pose proof (rng_sub' _ _ _ (bv_unsigned h0) 1 RS0 ltac:(lia)) as RH0.
    pose proof (rng_sub' _ _ _ (bv_unsigned wf) 1 RBUF ltac:(lia)) as RW0.
    pose proof (rdw0 m h0 _ _ MK0 ltac:(lia)) as R. step. clear R.
    step.
    cf_shchk SK0 Z.add_0_r MB0 k0;
    (pose proof (rdw0 m wf _ _ F0 ltac:(lia)) as R; step; clear R;
     step; step; let HC := fresh "H0c" in if_cases HC;
     [ cf_byte_cond HC; cf_audio wf m RBUF a3 RS16 MK16 SK16 MB16 k16 F16 RS17 MK17 SK17 MB17 k17 F17
     | cf_byte_cond HC; step; cf_done 0 ]).
Qed.
