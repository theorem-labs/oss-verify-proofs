(** The cut inside ent_build's kind 0 (ent_headamp_key, pod.h:224-262) where its two ways of making ch meet: 0x13538,
    after the digit text of c % 64 (c < 200) or odd_ch[c % 14] (c >= 200) is in ch[24] at sp + 0x138 with its NUL.
    From there: param[p % 8] (the relative table at 0x105f0), the separator by p's bit 7, the four parts at
    sp + 0x118, the strlen/memcpy loop into t[96] at sp + 0x150, then ent_text's memcpy into e.body and the NUL, to the
    join 0x13600. Statement text only. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Tables Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadBuild Require Import EntCut EntFacts.
Import ListNotations.
Open Scope Z_scope.

(** At 0x13538: s4 = p (the second byte read), s6 = the cursor after the turn's reads, the cell sp + 0x88 = |r'|,
    ch and its NUL at sp + 0x138, e still zero; the turn's result is the head-amp key of HPFX, ch, the separator and
    param[p % 8]. *)
Definition parts_at (sp gp tp s1 s8 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
    (src pp lo : Z) : Prop :=
  forall (p : Z) (ch r' : list byte) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 t3 t4 t5 t6 : word) m1,
    ent_build r = (ent_text (join_parts [HPFX; ch; if Z.testbit p 7 then [] else DOT; nth (Z.to_nat (p mod 8)) param []])
                     true, r') ->
    0 <= p < 256 -> s4 = Z_to_bv 64 p ->
    s6 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) ->
    (length ch <= 21)%nat -> ~ In NUL ch ->
    MemC sp m r src pp lo m1 (zeros 104) ->
    bytes_at rsegs m1 (bv_unsigned sp + 136) (le8 (Z_to_bv 64 (Z.of_nat (length r')))) ->
    bytes_at rsegs m1 (bv_unsigned sp + 312) (ch ++ [NUL]) ->
    evt rsegs (QJ sp gp tp s1 s8 F fc m r src pp lo (ent_build r))
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x150)) s1
               a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 95) s8 (Z_to_bv 64 (0xcccccccd * 2^32))
               (Z_to_bv 64 (bv_unsigned sp + 0x118)) (Z_to_bv 64 10) t3 t4 t5 t6)
          F (Z_to_bv 64 0x13538) fc None m1 (seg_rom rsegs)).
