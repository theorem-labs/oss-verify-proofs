(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 989 of its 1017 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/chain_words.v, with its module paths, module names, addresses and numbers changed; 684 of its 782 lines of code are new or changed and 919 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/arg_s.v, with its module paths, module names and numbers changed; 258 of its 325 lines of code are new or changed and 715 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/U/Prog/pcap_source_close.v, with its module paths and addresses changed; 98 of its 135 lines of code are new or changed and 288 lines of the source are left out. *)
(* text_buf (fuzz_link.c:655-666), PLAIN build: the three straight-line pieces of its walk on the
   plain image (link/ct/dis/plain/text_buf.s, 0x14fb0, 76 bytes). Every instruction is fetched and
   decoded from Img0.rsegs by `step`.
     0x14fb0 addi sp,sp,-16; sd ra,8(sp); sd s0,0(sp); beqz a0,+0x38
     0x14fc0 addi s0,a0,1; mv a0,s0; jal malloc (0x17514)
     0x14fcc beqz a0,+0x48 (abort); li a1,0x5a; mv a2,s0; ld ra,8(sp); ld s0,0(sp); addi sp,sp,16;
             j memset (0x1f060)   -- a tail call: memset returns to text_buf's caller
     0x14fe8 ld ra,8(sp); ld s0,0(sp); addi sp,sp,16; ret
   text_buf_zero: cap = 0, from the entry to the return. text_buf_pro: cap <> 0, from the entry to
   malloc's entry. text_buf_tail: from malloc's return (a0 <> 0) through memset to the return. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import memset_c.
Import ListNotations.
Open Scope Z_scope.

Ltac tb_weq := repeat (rewrite unsigned_lit by lia); first [ reflexivity | f_equal; lia ].

Lemma text_buf_zero :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    a0 = Z_to_bv 64 0 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp -> mem_inv rsegs m ->
    evt rsegs (fun ms' => exists sp' m',
        ms' = MS (mkR ra sp' gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None m' (seg_rom rsegs)
        /\ bv_unsigned sp' = bv_unsigned sp
        /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14fb0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo EA0 ST LO MI.
  subst a0.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  carve_frame 16%nat ST.
  zstep. zstep. zstep.
  zstep. try if_true.
  zstep. zstep. zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  apply evt_done.
  replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia.
  do 2 eexists. split; [reflexivity|].
  split; [rewrite ?unsigned_lit by lia; lia|].
  refine (conj _ (conj _ (conj _ _))); eassumption.
Qed.

Lemma text_buf_pro :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo cap : Z),
    bv_unsigned a0 = cap -> 0 < cap < 40 ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp -> mem_inv rsegs m ->
    evt rsegs (fun ms' => exists sp' s0' a0' m',
        ms' = MS (mkR (Z_to_bv 64 0x14fcc) sp' gp tp t0 t1 t2 s0' s1 a0' a1 a2 a3 a4 a5 a6 a7
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x17514) fc None m' (seg_rom rsegs)
        /\ bv_unsigned sp' = bv_unsigned sp - 16 /\ s0' = Z_to_bv 64 (cap + 1) /\ a0' = Z_to_bv 64 (cap + 1)
        /\ rw_cells rsegs m' (bv_unsigned sp - 16) [C8 s0; C8 ra]
        /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ stk rsegs m' lo (bv_unsigned sp - 16))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14fb0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo cap A0 CAP ST LO MI.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a0) as Ra0. unfold inr64 in Ra0.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  carve_frame 16%nat ST.
  zstep. zstep. zstep.
  zstep. if_false.
  zstep. zstep. zstep.
  apply evt_done.
  replace (bv_unsigned sp - 16) with (bv_unsigned sp + -16) by lia.
  do 4 eexists. split; [reflexivity|].
  split; [rewrite ?unsigned_lit by lia; lia|].
  split; [tb_weq|]. split; [tb_weq|].
  refine (conj _ (conj _ (conj _ (conj _ _)))); eassumption.
Qed.

Lemma text_buf_tail : memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo h cap : Z) (junk : list byte) (r0 R : word),
    a0 = Z_to_bv 64 h -> 0 < h -> s0 = Z_to_bv 64 (cap + 1) -> 0 <= cap < 40 ->
    rw_cells rsegs m h [CB (Z.to_nat (cap + 1)) junk] ->
    rw_cells rsegs m (bv_unsigned sp) [C8 r0; C8 R] ->
    stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp -> bv_unsigned sp + 16 < 2 ^ 63 ->
    h + cap + 1 <= lo -> mem_inv rsegs m ->
    evt rsegs (fun ms' => exists sp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
        ms' = MS (mkR R sp' gp tp t0' t1' t2' r0 s1 (Z_to_bv 64 h) a1' a2' a3' a4' a5' a6' a7'
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc R) fc None m' (seg_rom rsegs)
        /\ bv_unsigned sp' = bv_unsigned sp + 16
        /\ munch [(bv_unsigned sp, bv_unsigned sp + 16); (h, h + cap + 1)] m m'
        /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + 16)
        /\ rw_cells rsegs m' h [CB (Z.to_nat (cap + 1)) (repeat (Z_to_bv 8 0x5a) (Z.to_nat (cap + 1)))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14fcc) fc None m (seg_rom rsegs)).
Proof.
  intros HMEMSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo h cap junk r0 R EA0 H0 ES0 CAP BLK FR ST LS S63 HL MI.
  subst a0 s0.
  unfold memset_contract in HMEMSET.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  assert (UH : bv_unsigned (Z_to_bv 64 h) = h) by (apply unsigned_lit; lia).
  assert (UC : bv_unsigned (Z_to_bv 64 (cap + 1)) = cap + 1) by (apply unsigned_lit; lia).
  zstep. if_false.
  zstep. zstep. zstep. zstep. zstep.
  release_frame FR ST (bv_unsigned sp + 16).
  zstep.
  eapply evt_cut.
  { eapply HMEMSET with (junk := junk); [|exact MI].
    lazymatch goal with |- rw_cells _ _ (bv_unsigned ?X) [CB (Z.to_nat (bv_unsigned ?N)) _] =>
      replace (bv_unsigned X) with h by (rewrite ?unsigned_lit by lia; lia);
      replace (bv_unsigned N) with (cap + 1) by (rewrite ?unsigned_lit by lia; lia)
    end.
    exact BLK. }
  unfold memset_post.
  intros ms' (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & -> & MUc & WMc & MIc & BUFc).
  lazymatch type of MUc with munch [(bv_unsigned ?X, bv_unsigned ?X + bv_unsigned ?N)] _ _ =>
    assert (UX : bv_unsigned X = h) by (rewrite ?unsigned_lit by lia; lia);
    assert (UN : bv_unsigned N = cap + 1) by (rewrite ?unsigned_lit by lia; lia)
  end.
  rewrite UX, UN in MUc, BUFc.
  lazymatch type of BUFc with context [Z_to_bv 8 (bv_unsigned ?V mod 256)] =>
    replace (Z_to_bv 8 (bv_unsigned V mod 256)) with (Z_to_bv 8 0x5a) in BUFc
      by (rewrite ?unsigned_lit by lia; reflexivity)
  end.
  apply evt_done.
  do 16 eexists. split; [reflexivity|].
  split; [rewrite ?unsigned_lit by lia; lia|].
  split.
  { intros x Hx. apply MUc. cbn [outside] in *. split; [lia | exact I]. }
  split; [exact WMc|]. split; [exact MIc|].
  split.
  { apply (stk_transport_disjoint rsegs [(h, h + (cap + 1))] m m'); [exact ST | exact MUc | exact WMc |].
    cbn [disjoint_from]. split; [lia | exact I]. }
  exact BUFc.
Qed.
