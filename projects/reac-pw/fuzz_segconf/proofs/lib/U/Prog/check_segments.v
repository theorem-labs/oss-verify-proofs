(** check_segments (UBSan image 1696d6c34ffd, 0x149c0, 65 instructions, frame 80: ra s0-s8 at sp+72 .. sp+0):
    proof of [check_segments_contract] (U/Prog/check_segments_c.v) from strcmp's contract (U/Prog/strcmp_c.v,
    0x1f594). The image-free lemmas are the plain walk's [CsPure] (lib/Prog/check_segments.v).

    Code (UBSan binary; traps to the `unimp` at 0x14ab8):
      0x149c0-0x149e8  frame; s1 = c; `andi c,7` trap (c mod 16 = 0); s2 = m; `andi m,3` trap (m mod 16 = 0)
      0x14a04-0x14a24  s0 = returned; s7 = `lw` c->n (c + 0x2c80), `lw` m->n (m + 0x2000); bne -> abort
      0x14a28-0x14a38  `lw` c->overflow (c + 0x34d0) vs m->overflow (m + 0x2004); bne -> abort
      0x14a3c blez s7 -> EXIT; s3 = s4 = 0, s5 = ~c, s6 = ~m, s7 = n << 8, s8 = 32 (the bound counter)
      LOOP 0x14a58  beqz s8 trap (n <= 32); bltu s5,s3 and bltu s6,s4 traps (c + 356 i and m + 256 i do not wrap:
           bytes_at bounds); strcmp(c + s3, m + s4); bnez -> abort; s4 += 256; s3 += 356; s8 -= 1; bne s7,s4 -> LOOP
      EXIT 0x14a84  beqz s0 -> abort; restore; ret *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require check_segments.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import strcmp_c check_segments_c.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.check_segments.CsPure.
Import ListNotations.
Open Scope Z_scope.

Lemma cs_shl8 : forall x, Z.shiftl x 8 = 256 * x.
Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. lia. Qed.

(** The registers of the loop and exit states, from the forms the steps leave. *)
Ltac cs_weq := first [ lia | reflexivity | (f_equal; rewrite ?zb_lxor_ones, ?cs_shl8 by lia; lia) ].

Theorem check_segments_holds : strcmp_contract -> check_segments_contract.
Proof.
  intros SC. unfold check_segments_contract, check_segments_pre, CHECK_SEGMENTS, CHECK_SEGMENTS_STACK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    rc mc ret (C0 & C16 & (bsc & BC & EC) & AC & M0 & M16 & (bsm & BM & EM) & AM & RV & CS & (ST & SLO & S16 & SRO)
    & MI).
  clear C0 M0 S16.
  destruct (cs_true _ _ _ CS) as (Ln & Ov & _ & ->).
  pose proof EC as (LC & _ & _ & UNc & _ & _ & _ & _ & UOc & _).
  pose proof EM as (LM & N32 & _ & UNm & UOm & _).
  unfold SEG_C_SIZE in LC. unfold SEG_M_SIZE in LM. unfold apart, SEG_C_SIZE, SEG_M_SIZE in AC, AM.
  rewrite Ln in UNc. rewrite Ov in UOc.
  pose proof (bytes_at_bound _ _ _ _ BC) as BCb. pose proof (bytes_at_bound _ _ _ _ BM) as BMb.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof (bv_unsigned_in_range 64 a0) as RA0.
  pose proof (bv_unsigned_in_range 64 a1) as RA1.
  change (bv_modulus 64) with (2^64) in RSP, RA0, RA1.
  assert (Ea2 : a2 = Z_to_bv 64 1) by (rewrite <- (Z_to_bv_lit_self a2), RV; reflexivity).
  subst a2. clear RV.
  pose proof (Z_to_bv_lit_self sp) as Esp. pose proof (Z_to_bv_lit_self a0) as Ea0.
  pose proof (Z_to_bv_lit_self a1) as Ea1.
  set (Sp := bv_unsigned sp) in *. set (c := bv_unsigned a0) in *. set (mb := bv_unsigned a1) in *.
  rewrite <- Esp, <- Ea0, <- Ea1. clearbody Sp c mb. clear Esp Ea0 Ea1.
  (* the alignment traps: c mod 8 = 0 and m mod 4 = 0 *)
  assert (CL7 : Z.land c 7 = 0).
  { change 7 with (2 ^ 3 - 1). rewrite zb_land_mask by lia. change (2 ^ 3) with 8.
    Z.div_mod_to_equations. lia. }
  assert (ML3 : Z.land mb 3 = 0).
  { change 3 with (2 ^ 2 - 1). rewrite zb_land_mask by lia. change (2 ^ 2) with 4.
    Z.div_mod_to_equations. lia. }
  clear C16 M16.
  set (n := length (mc_seg mc)) in *.
  assert (En : n = length (mc_seg mc)) by reflexivity. clearbody n.
  pose proof (munch_refl [(Sp - 80, Sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  (* prologue: 0x149c0 - 0x149e8 *)
  zstep. carve_frame 80%nat ST.
  do 10 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?M _) => rename M into M1 end.
  pose proof (cs_rd4 rsegs M1 c bsc 11392 _ BC ltac:(lia) ltac:(lia) UNc) as RN.
  pose proof (cs_rd4 rsegs M1 mb bsm 8192 _ BM ltac:(lia) ltac:(lia) UNm) as MN.
  pose proof (cs_rd4 rsegs M1 c bsc 13520 _ BC ltac:(lia) ltac:(lia) UOc) as RO.
  pose proof (cs_rd4 rsegs M1 mb bsm 8196 _ BM ltac:(lia) ltac:(lia) UOm) as MO.
  assert (NM : forall i, (i < n)%nat -> exists sx, bytes_at rsegs M1 (c + 356 * Z.of_nat i) (sx ++ [ZERO]) /\
      ~ In ZERO sx /\ bytes_at rsegs M1 (mb + 256 * Z.of_nat i) (sx ++ [ZERO])).
  { intros i Hi. apply (names_at rsegs M1 c mb bsc bsm rc mc i BC EC BM EM CS). rewrite <- En. exact Hi. }
  lazymatch goal with |- evt _ ?Q _ => set (Post := Q) end.
  (* EXIT 0x14a84: s0 = 1, so beqz falls through; restore and return. *)
  assert (EPI : forall x1 x9 x10 x11 x12 x13 x18 x19 x20 x21 x22 x23 x24 : word,
    evt rsegs Post (MS (mkR x1 (Z_to_bv 64 (Sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 1) x9 x10 x11 x12 x13
                            a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x14a84) fc None M1 (seg_rom rsegs))).
  { intros x1 x9 x10 x11 x12 x13 x18 x19 x20 x21 x22 x23 x24.
    zstep. cs_ntk.
    do 12 zstep.
    release_frame FR ST Sp.
    apply evt_done. unfold Post, ret_void. cbv beta.
    exists t0, t1, t2, x10, x11, x12, x13, a4, a5, a6, a7, t3, t4, t5, t6, M1.
    split; [unfold mkR; repeat f_equal; lia|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [rewrite unsigned_lit by lia; exact ST | exact I]. }
  (* LOOP 0x14a58 after i entries, k = n - i left: s3 = 356 i, s4 = 256 i, s8 = 32 - i. *)
  assert (LOOP : forall k i (x1 x10 x11 x12 x13 w8 w9 w18 w19 w20 w21 w22 w23 w24 : word),
    (i + k = n)%nat -> (0 < k)%nat ->
    w8 = Z_to_bv 64 1 -> w9 = Z_to_bv 64 c -> w18 = Z_to_bv 64 mb ->
    w19 = Z_to_bv 64 (356 * Z.of_nat i) -> w20 = Z_to_bv 64 (256 * Z.of_nat i) ->
    w21 = Z_to_bv 64 (18446744073709551615 - c) -> w22 = Z_to_bv 64 (18446744073709551615 - mb) ->
    w23 = Z_to_bv 64 (256 * Z.of_nat n) -> w24 = Z_to_bv 64 (32 - Z.of_nat i) ->
    evt rsegs Post (MS (mkR x1 (Z_to_bv 64 (Sp + -80)) gp tp t0 t1 t2 w8 w9 x10 x11 x12 x13 a4 a5 a6 a7
                            w18 w19 w20 w21 w22 w23 w24 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x14a58) fc None M1 (seg_rom rsegs))).
  { induction k as [|k IH];
      intros i x1 x10 x11 x12 x13 w8 w9 w18 w19 w20 w21 w22 w23 w24 Hik Hk E8 E9 E18 E19 E20 E21 E22 E23 E24;
      [lia|].
    subst w8 w9 w18 w19 w20 w21 w22 w23 w24.
    destruct (NM i ltac:(lia)) as (sx & Bx & Nx & By).
    zstep. cs_ntk.
    zstep. cs_ntk.
    zstep. cs_ntk.
    zstep. zstep. zstep.
    eapply evt_cut.
    { eapply SC with (sx := sx) (sy := sx).
      - eapply bytes_at_eq; [exact Bx | rewrite ?unsigned_lit by lia; lia].
      - exact Nx.
      - eapply bytes_at_eq; [exact By | rewrite ?unsigned_lit by lia; lia].
      - exact Nx. }
    intros ms' (r & y11 & y12 & y13 & -> & Hr).
    assert (R0 : r = Z_to_bv 64 0) by (apply Hr; reflexivity). subst r.
    rewrite ret_pc_even by (try lia; reflexivity).
    zstep. cs_ntk.
    do 3 zstep.
    zstep.
    destruct k as [|k].
    - cs_ntk. eapply EPI.
    - cs_tkn. eapply (IH (S i)); cs_weq. }
  (* 0x149ec - 0x14a54 *)
  zstep.
  zstep. rewrite ?CL7.
  zstep. cs_ntk.
  zstep.
  zstep. rewrite ?ML3.
  zstep. cs_ntk.
  zstep.
  do 3 zstep.
  zstep. cs_swrap.
  zstep.
  zstep. clear RN.
  zstep. clear MN.
  rewrite (sx32_small (Z.of_nat n)) by lia.
  zstep. cs_ntk.
  zstep. cs_swrap.
  zstep.
  zstep. clear RO. zstep. clear MO.
  zstep. cs_ntk.
  zstep.
  destruct (Nat.eq_dec n 0) as [N0|N0].
  - cs_tkn. eapply EPI.
  - cs_ntk. do 6 zstep. eapply (LOOP n 0%nat); cs_weq.
Qed.
