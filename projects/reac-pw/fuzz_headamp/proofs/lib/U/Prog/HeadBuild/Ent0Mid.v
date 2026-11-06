(** The cut inside ent_build's kind 0 (the head-amp key, pod.h:224-262) in the UBSan image: 0x13abc, after c and p are
    read and ch[] (sp + 0x160) holds the channel text and its NUL, before the param pointer, the four parts, their
    join into t[] (sp + 0x178) and ent_text. Statement text only: the entry walks (the jump table's target 0x13530 and
    0x13a20) end here, and the walk from here ends at the join 0x13df0. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Tables Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.HeadBuild Require Import EntCut EntFacts.
Import ListNotations.
Open Scope Z_scope.

(** At 0x13abc: the turn's pod is the head-amp key of the channel text ch and the byte p (ent_build r = its
    ent_text with the input left r'), s7 = p, s2 = |r'|, s5 = s10 = the cursor, ch and its NUL at sp + 0x160 (no NUL
    inside, at most 21 bytes), e still zero; the constants of the head unchanged. *)
Definition case0_mid_at (sp gp tp s1 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (r : list byte) (src pp lo : Z) : Prop :=
  forall (ra t0 t1 t2 s2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s10 t3 t4 t5 t6 : word) m1 (p : Z) (ch r' : list byte),
    ent_build r = (ent_text (join_parts [HPFX; ch; if Z.testbit p 7 then [] else DOT; nth (Z.to_nat (p mod 8)) param []])
                     true, r') ->
    0 <= p < 256 -> s7 = Z_to_bv 64 p -> ~ In NUL ch -> (length ch <= 21)%nat ->
    bytes_at rsegs m1 (bv_unsigned sp + 0x160) (ch ++ [NUL]) ->
    s2 = Z_to_bv 64 (Z.of_nat (length r')) ->
    s5 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) -> s10 = s5 ->
    MemC sp m lo m1 (Z_to_bv 64 0) (Z_to_bv 64 0) (zeros 96) ->
    evt rsegs (QJ sp gp tp s1 F fc m r src pp lo (ent_build r))
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x178)) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2
               (Z_to_bv 64 (0xcccccccd * 2^32)) s4 s5 s6 s7 (Z_to_bv 64 pp) (Z_to_bv 64 95) s10 (Z_to_bv 64 4) t3 t4 t5 t6)
          F (Z_to_bv 64 0x13abc) fc None m1 (seg_rom rsegs)).
