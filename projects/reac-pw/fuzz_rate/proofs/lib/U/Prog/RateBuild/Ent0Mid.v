(** The cut inside ent_build's kind 0 (the head-amp key, pod.h:224-262) in the UBSan image: 0x13b64, after c and p are
    read and ch[] (sp + 0x170) holds the channel text and its NUL, before the param pointer, the four parts, their
    join into t[] (sp + 0x188) and ent_text. Statement text only: the walks of the c / p reads and of ch (Ent0C.v)
    end here, and the walk from here (Ent0T.v) ends at the join 0x13ee4. The form is reac-pw/fuzz_role's
    U/Prog/RoleBuild/Ent0Mid.v at rate's registers: p in s8, |r'| in t1, the
    cursor in s10, s6 = ch's end sp + 0x170 (the parts loop's bound). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Tables Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.RateBuild Require Import EntCut EntFacts.
Import ListNotations.
Open Scope Z_scope.

(** At 0x13b64: the turn's pod is the head-amp key of the channel text ch and the byte p (ent_build r = its
    ent_text with the input left r'), s8 = p, t1 = |r'|, s10 = the cursor, s6 = sp + 0x170, ch and its NUL at
    sp + 0x170 (no NUL inside, at most 21 bytes), e still zero; s0, s1, s2, s3, s4 as at the case entry (s5, s7, s9,
    s11 anything). *)
Definition case0_mid_at (sp gp tp s3 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (r : list byte) (src pp lo : Z) : Prop :=
  forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) m1 (p : Z)
         (ch r' : list byte),
    ent_build r = (ent_text (join_parts [HPFX; ch; if Z.testbit p 7 then [] else DOT; nth (Z.to_nat (p mod 8)) param []])
                     true, r') ->
    0 <= p < 256 -> s8 = Z_to_bv 64 p -> ~ In NUL ch -> (length ch <= 21)%nat ->
    bytes_at rsegs m1 (bv_unsigned sp + 0x170) (ch ++ [NUL]) ->
    t1 = Z_to_bv 64 (Z.of_nat (length r')) ->
    s10 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) ->
    s6 = Z_to_bv 64 (bv_unsigned sp + 0x170) ->
    MemC sp m lo m1 (Z_to_bv 64 0) (Z_to_bv 64 0) (zeros 96) ->
    evt rsegs (QJ sp gp tp s3 F fc m r src pp lo (ent_build r))
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x188)) (Z_to_bv 64 4) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 95) s3 (Z_to_bv 64 (0xcccccccd * 2^32)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13b64) fc None m1 (seg_rom rsegs)).
