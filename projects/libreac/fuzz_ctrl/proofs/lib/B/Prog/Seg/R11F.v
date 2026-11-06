(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/R11.v (not in this delivery) r11_evt at a working branch 3803efccea0
     (blob f7db7f7f2ba027c81c5d52135df381a9b6ccd202);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: the run calls reac_identity_ingest, so it is split and there is no r11_evt_of_F.
     r11_pre_F re-runs R11.v:149-150 (the ten instructions 0x817ec .. 0x8185c, up to the callee entry);
     r11_post_F re-runs R11.v:175-191 (the run's Q from the callee post facts; no instruction follows the
     return point 0x81860, which is the run's exit cut).  No `_F` steps through the callee, and this file
     states no callee contract. *)
(* rule 24: no function proved. *)
(* The ten instructions of the pre stretch (R12.v:6-13 gives the listing of the shared tail):
     0x817ec li a1,1 / 0x817f0 beq a0,a1,0x81840 (taken: a0 = 1)
     0x81840 ld a0,240(s1) / 0x81844 lhu a1,0(a0)   a1 = the u16 at [A + 240] = fr + 2448
     0x81848 ld a0,232(s1) / 0x8184c ld a2,0(a0)    a2 = the body pointer at [A + 232] = fr + 2464
     0x81850 ld a0,224(s1) / 0x81854 ld a3,0(a0)    a3 = the body length at [A + 224] = fr + 2496
     0x81858 ld a0,144(s1)                          a0 = the identity record [A + 144] = fr + 2176
     0x8185c jal reac_identity_ingest (0x87e0c), ra = 0x81860.
   Seven loads, no store, no instrumented shadow check and no UBSan trap branch on the path, so the footprint
   premises are the seven loaded cells only: [A+240,+8), [A+232,+8), [A+224,+8), [A+144,+8), [fr+2448,+2),
   [fr+2464,+8), [fr+2496,+8). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel RcIdentLib RcReply RcParse RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_identity_ingest_c.
Import ListNotations.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Open Scope Z_scope.

Module RIM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.
Module RIG := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_identity_ingest_c.

(* The callee entry is RIG.REAC_IDENTITY_INGEST (lib/B/Prog/reac_identity_ingest_c.v:13, 0x87e0c): the
   callee's own constant, not a second local copy of the address. *)

(* The `lhu` result: a 16-bit value read back unchanged (R11.v:101). *)
Lemma r11f_zx16 : forall ad, 0 <= ad < 65536 -> zx16 (Z_to_bv 64 ad) = Z_to_bv 64 ad.
Proof. intros ad H. unfold zx16. rewrite MState.unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

(* ---- the pre stretch: 0x817ec .. 0x8185c, stopping AT the callee entry ---- *)

Lemma r11_pre_F : forall (RNG : footprint)
  (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A fr phi ad len : Z),
  s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 1 ->
  0 <= A -> A + 248 <= 2 ^ 64 -> 0 < fr -> fr + 3136 <= 2 ^ 64 ->
  0 < phi -> 0 < len -> phi + 38 + len <= 2 ^ 64 -> 0 <= ad < 65536 ->
  ro_cells rsegs m (A + 240) [C8 (Z_to_bv 64 (fr + 2448))] ->
  ro_cells rsegs m (A + 232) [C8 (Z_to_bv 64 (fr + 2464))] ->
  ro_cells rsegs m (A + 224) [C8 (Z_to_bv 64 (fr + 2496))] ->
  ro_cells rsegs m (A + 144) [C8 (Z_to_bv 64 (fr + 2176))] ->
  ro_cells rsegs m (fr + 2448) [C2 (Z_to_bv 64 ad)] ->
  ro_cells rsegs m (fr + 2464) [C8 (Z_to_bv 64 (phi + 38))] ->
  ro_cells rsegs m (fr + 2496) [C8 (Z_to_bv 64 len)] ->
  rng RNG (A + 240) 8 -> rng RNG (A + 232) 8 -> rng RNG (A + 224) 8 -> rng RNG (A + 144) 8 ->
  rng RNG (fr + 2448) 2 -> rng RNG (fr + 2464) 8 -> rng RNG (fr + 2496) 8 ->
  evtF rsegs RNG
    (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 RIG.REAC_IDENTITY_INGEST) fc None m (seg_rom rsegs) /\
       ra' = Z_to_bv 64 0x81860 /\ a0' = Z_to_bv 64 (fr + 2176) /\ a1' = Z_to_bv 64 ad /\
       a2' = Z_to_bv 64 (phi + 38) /\ a3' = Z_to_bv 64 len)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x817ec) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A fr phi ad len -> -> HA0 HA248 Hfr0 Hfr64 Hphi0 Hlen0 Hpl64 Had
    RO1 RO2 RO3 RO4 RC1 RC2 RC3 G1 G2 G3 G4 G5 G6 G7.
  step. step. if_true.
  do 8 step.
  apply evtF_done. do 16 eexists.
  split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [first [reflexivity | apply r11f_zx16; exact Had | symmetry; apply r11f_zx16; exact Had]|].
  split; reflexivity.
Qed.

(* ---- the post stretch: the run's Q at the return point 0x81860, from the callee post facts R11.v:175-191.
   No instruction lies between the return point and the run's exit cut, so this stretch steps nothing: it is the
   packaging the proved run does after its evt_cut. ---- *)

Lemma r11_post_F : forall (RNG : footprint)
  (ra' sp gp tp t0' t1' t2' s0 s1 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
   t3' t4' t5' t6' : word)
  (F : bvmap 5 word) (fc : bv 32) (m m' : word -> option byte) (spv fr ad lo : Z) (idb pb : list byte),
  sp = Z_to_bv 64 spv ->
  munch [(spv - 32, spv); (fr + 2176, fr + 2176 + 38)] m m' ->
  wmono rsegs m m' ->
  stk rsegs m' lo spv ->
  rw_cells rsegs m' (fr + 2176) [CB 38 (snd (RIM.ING idb ad pb))] ->
  evtF rsegs RNG
    (fun ms' => exists (R : bvmap 5 word) (m'' : word -> option byte),
       ms' = MS R F (Z_to_bv 64 0x81860) fc None m'' (seg_rom rsegs) /\
       getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
       getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 20 = s4 /\ getr R 21 = s5 /\ getr R 22 = s6 /\
       getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 27 = s11 /\
       getr R 10 = Z_to_bv 64 (fst (RIM.ING idb ad pb)) /\
       munch [(spv - 32, spv); (fr + 2176, fr + 2176 + 38)] m m'' /\ wmono rsegs m m'' /\
       stk rsegs m'' lo spv /\
       rw_cells rsegs m'' (fr + 2176) [CB 38 (snd (RIM.ING idb ad pb))])
    (MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fst (RIM.ING idb ad pb))) a1' a2' a3' a4' a5' a6' a7'
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x81860) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG ra' sp gp tp t0' t1' t2' s0 s1 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3' t4' t5' t6' F fc m m' spv fr ad lo idb pb -> MU WM ST RW.
  apply evtF_done. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact ST | exact RW].
Qed.
