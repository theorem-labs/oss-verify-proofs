(** The cut inside ent_build's kind 0 (ent_headamp_key, pod.h:224-262) where its two ways of making ch meet: 0x13428,
    after the digit text of c % 64 (c < 200) or odd_ch[c % 14] (c >= 200) is in ch[24] at sp + 0x110 with its NUL.
    From there: param[p % 8] (the relative table at 0x10618), the separator by p's bit 7, the four parts at
    sp + 0xf0, the strlen/memcpy loop into t[96] at sp + 0x128, then ent_text's memcpy into e.body and the NUL, to the
    join 0x134f0. Statement text only. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Tables Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog.RoleBuild Require Import EntCut EntFacts.
Import ListNotations.
Open Scope Z_scope.

(** At 0x13428: s4 = p (the second byte read), s6 = the cursor after the turn's reads, the cell sp + 0x78 = |r'|,
    ch and its NUL at sp + 0x110, e still zero; the turn's result is the head-amp key of HPFX, ch, the separator and
    param[p % 8]. *)
Definition parts_at (sp gp tp s7 s9 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
    (src pp lo : Z) : Prop :=
  forall (p : Z) (ch r' : list byte) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s11 t3 t4 t5 t6 : word) m1,
    ent_build r = (ent_text (join_parts [HPFX; ch; if Z.testbit p 7 then [] else DOT; nth (Z.to_nat (p mod 8)) param []])
                     true, r') ->
    0 <= p < 256 -> s4 = Z_to_bv 64 p ->
    s6 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) ->
    (length ch <= 21)%nat -> ~ In NUL ch ->
    MemC sp m r src pp lo m1 (zeros 104) ->
    bytes_at rsegs m1 (bv_unsigned sp + 120) (le8 (Z_to_bv 64 (Z.of_nat (length r')))) ->
    bytes_at rsegs m1 (bv_unsigned sp + 272) (ch ++ [NUL]) ->
    evt rsegs (QJ sp gp tp s7 s9 F fc m r src pp lo (ent_build r))
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x128)) (Z_to_bv 64 (bv_unsigned sp + 0xf0))
               a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (0xcccccccd * 2^32)) s3 s4 s5 s6 s7 (Z_to_bv 64 95) s9
               (Z_to_bv 64 10) s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13428) fc None m1 (seg_rom rsegs)).
