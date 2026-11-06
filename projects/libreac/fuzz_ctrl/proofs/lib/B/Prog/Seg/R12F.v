(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/R12.v (not in this delivery) r12_evt at a working branch 3803efccea0
     (blob dba11fb6f43cab8beccbd1296d1528d724c5acdd);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: the run calls reac_identity_ingest, so it is split and there is no r12_evt_of_F.
     r12_pre_F re-runs R12.v:170-175 (the ten instructions 0x81834 .. 0x8185c, up to the callee entry);
     r12_post_F re-runs R12.v:200-221 (the run's Q from the callee post facts; no instruction follows the
     return point 0x81860, which is the run's exit cut).  No `_F` steps through the callee, and this file
     states no callee contract. *)
(* rule 24: no function proved. *)
(* The ten instructions of the pre stretch (R12.v:6-13):
     0x81834 li a1,1 / 0x81838 beq a0,a1,0x81840 (taken: a0 = fg_rf = 1)
     0x81840 ld a0,240(s1) / 0x81844 lhu a1,0(a0)   a1 = the u16 at [Ab + 240] = pa
     0x81848 ld a0,232(s1) / 0x8184c ld a2,0(a0)    a2 = the body pointer at [Ab + 232] = pp
     0x81850 ld a0,224(s1) / 0x81854 ld a3,0(a0)    a3 = the body length at [Ab + 224] = pn
     0x81858 ld a0,144(s1)                          a0 = the identity record [Ab + 144] = idp
     0x8185c jal reac_identity_ingest (0x87e0c), ra = 0x81860.
   Seven loads, no store, no instrumented shadow check and no UBSan trap branch on the path, so the footprint
   premises are the seven loaded cells only: [Ab+224,+24) (the three spills pn / pp / pa), [Ab+144,+8),
   [pa,+2), [pp,+8), [pn,+8). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_identity_ingest_c.
Import ListNotations.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Open Scope Z_scope.

Module RIM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.
Module RIG := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_identity_ingest_c.

(* The callee entry is RIG.REAC_IDENTITY_INGEST (lib/B/Prog/reac_identity_ingest_c.v:13, 0x87e0c): the
   callee's own constant, not a second local copy of the address. *)

(* The `lhu` result: a 16-bit value read back unchanged (R12.v:126). *)
Lemma r12f_zx16 : forall x, 0 <= x < 65536 -> zx16 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zx16. rewrite MState.unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

(* ---- the pre stretch: 0x81834 .. 0x8185c, stopping AT the callee entry ---- *)

Lemma r12_pre_F : forall (RNG : footprint)
  (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Ab idp pa pp pn ad p len : Z),
  s1 = Z_to_bv 64 Ab -> a0 = Z_to_bv 64 1 ->
  0 <= Ab -> Ab + 248 <= 2 ^ 64 ->
  0 < idp < 2 ^ 64 -> 0 < p < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> 0 <= ad < 65536 ->
  ro_cells rsegs m (Ab + 224) [C8 (Z_to_bv 64 pn); C8 (Z_to_bv 64 pp); C8 (Z_to_bv 64 pa)] ->
  ro_cells rsegs m (Ab + 144) [C8 (Z_to_bv 64 idp)] ->
  ro_cells rsegs m pa [C2 (Z_to_bv 64 ad)] ->
  ro_cells rsegs m pp [C8 (Z_to_bv 64 p)] ->
  ro_cells rsegs m pn [C8 (Z_to_bv 64 len)] ->
  rng RNG (Ab + 224) 24 -> rng RNG (Ab + 144) 8 ->
  rng RNG pa 2 -> rng RNG pp 8 -> rng RNG pn 8 ->
  evtF rsegs RNG
    (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 RIG.REAC_IDENTITY_INGEST) fc None m (seg_rom rsegs) /\
       ra' = Z_to_bv 64 0x81860 /\ a0' = Z_to_bv 64 idp /\ a1' = Z_to_bv 64 ad /\
       a2' = Z_to_bv 64 p /\ a3' = Z_to_bv 64 len)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x81834) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Ab idp pa pp pn ad p len -> -> HAb0 HAb Hidp Hp Hlen Had
    RO24 RO144 ROad ROp ROlen G24 G144 Gpa Gpp Gpn.
  step. step.
  lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with true by (vm_compute; reflexivity) end.
  cbv iota.
  do 8 step.
  apply evtF_done. do 16 eexists.
  split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [first [reflexivity | apply r12f_zx16; lia | symmetry; apply r12f_zx16; lia]|].
  split; reflexivity.
Qed.

(* ---- the post stretch: the run's Q at the return point 0x81860, from the callee post facts R12.v:200-221.
   No instruction lies between the return point and the run's exit cut, so this stretch steps nothing: it is the
   packaging the proved run does after its evt_cut. ---- *)

Lemma r12_post_F : forall (RNG : footprint)
  (ra' sp gp tp t0' t1' t2' s0 s1 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
   t3' t4' t5' t6' : word)
  (F : bvmap 5 word) (fc : bv 32) (m m' : word -> option byte) (spv idp ad lo : Z) (idb pb : list byte),
  sp = Z_to_bv 64 spv ->
  munch [(spv - 32, spv); (idp, idp + 38)] m m' ->
  wmono rsegs m m' ->
  stk rsegs m' lo spv ->
  rw_cells rsegs m' idp [CB 38 (snd (RIM.ING idb ad pb))] ->
  evtF rsegs RNG
    (fun ms' => exists (R : bvmap 5 word) (pc' : word) (m'' : word -> option byte),
       ms' = MS R F pc' fc None m'' (seg_rom rsegs) /\
       pc' = Z_to_bv 64 0x81860 /\
       getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
       getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 20 = s4 /\ getr R 21 = s5 /\ getr R 22 = s6 /\
       getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 27 = s11 /\
       getr R 10 = Z_to_bv 64 (fst (RIM.ING idb ad pb)) /\
       munch [(spv - 32, spv); (idp, idp + 38)] m m'' /\ wmono rsegs m m'' /\ stk rsegs m'' lo spv /\
       rw_cells rsegs m'' idp [CB 38 (snd (RIM.ING idb ad pb))])
    (MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fst (RIM.ING idb ad pb))) a1' a2' a3' a4' a5' a6' a7'
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (Z_to_bv 64 0x81860) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG ra' sp gp tp t0' t1' t2' s0 s1 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3' t4' t5' t6' F fc m m' spv idp ad lo idb pb -> MU WM ST RW.
  apply evtF_done. do 3 eexists. split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact ST | exact RW].
Qed.
