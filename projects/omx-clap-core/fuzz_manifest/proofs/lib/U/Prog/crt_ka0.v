From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import ManifestModel ManifestMem strlen_c.
Import ListNotations.
Open Scope Z_scope.

Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv iota
  end.

Lemma bveq_ne : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a <> b ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = false.
Proof.
  intros a b Ha Hb H. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. exact H.
Qed.

Lemma bveq_eq : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a = b ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = true.
Proof.
  intros a b Ha Hb H. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_eq. exact H.
Qed.

Definition frame_cells (j : list byte) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra : word) : list cell :=
  [CB 8 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma crt_pro : strlen_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (u us : list byte),
  stk rsegs m lo (bv_unsigned sp) -> lo + 112 <= bv_unsigned sp -> mem_inv rsegs m ->
  cstr_at m (bv_unsigned a0) u us ->
  bv_unsigned a0 + Z.of_nat (length u + 1 + length us) <= bv_unsigned sp - 112 ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) junk m',
      ms' = MS (mkR (Z_to_bv 64 0x13440) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' a0 s1
                    (Z_to_bv 64 0x102e7) a0 a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 (Z.of_nat (length u)))
                    s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x13e10) fc None m' (seg_rom rsegs) /\
      rw_cells rsegs m' (bv_unsigned sp + -112) (frame_cells junk s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra) /\
      munch [(bv_unsigned sp + -112, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x133ec) fc None m (seg_rom rsegs)).
Proof.
  intros STRLEN ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    u us ST LO MI CU HU.
  destruct CU as [BU [NU AU]].
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  carve_frame 112%nat ST.
  do 16 zstep.
  eapply evt_cut.
  { eapply STRLEN; [exact BU | | exact AU | exact MI].
    intros HIn. rewrite Forall_forall in NU. exact (NU _ HIn eq_refl). }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
    E & MUc & WMc & MIc & BU1).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x1342c)) with (Z_to_bv 64 0x1342c) by (apply bv_eq; vm_compute; reflexivity).
  transport_after_call rsegs m0 m1 MUc WMc.
  do 5 zstep.
  finish.
  exact FR.
Qed.

Definition exit_state (xra : word) (S : Z) (gp tp t0 t1 t2 xs0 xs1 res a1 a2 a3 a4 a5 a6 a7
    xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) : machine_state :=
  MS (mkR xra (Z_to_bv 64 (S + 112)) gp tp t0 t1 t2 xs0 xs1 res a1 a2 a3 a4 a5 a6 a7
          xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3 t4 t5 t6)
     F (Z_to_bv 64 0x14e4c) fc None m (seg_rom rsegs).

Lemma crt_exit : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (j : list byte)
    (xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xra : word),
  rw_cells rsegs m (bv_unsigned sp) (frame_cells j xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xra) ->
  bv_unsigned sp + 112 < 2 ^ 64 ->
  evt rsegs (fun ms' => ms' = exit_state xra (bv_unsigned sp) gp tp t0 t1 t2 xs0 xs1 s2 a1 a2 a3 a4 a5 a6 a7
                                 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3 t4 t5 t6 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x135c8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m j
    xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xra FR HI.
  unfold frame_cells in FR.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  do 16 zstep.
  apply evt_done. unfold exit_state. reflexivity.
Qed.

Lemma crt_zero : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (j : list byte)
    (xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xra : word),
  a0 = Z_to_bv 64 0 -> s3 = Z_to_bv 64 0 ->
  rw_cells rsegs m (bv_unsigned sp) (frame_cells j xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xra) ->
  bv_unsigned sp + 112 < 2 ^ 64 ->
  evt rsegs (fun ms' => ms' = MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + 112)) gp tp t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7
                                 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3 t4 t5 t6) F (ret_pc xra) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13440) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m j
    xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xra -> -> FR HI.
  unfold frame_cells in FR.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  zstep. if_lit.
  zstep. if_lit.
  do 15 zstep.
  apply evt_done. reflexivity.
Qed.

Lemma crt_mal : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n : Z),
  a0 = Z_to_bv 64 0 -> s3 = Z_to_bv 64 n -> 1 <= n <= 255 ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x1345c) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (3 * n + 64))
                                   (Z_to_bv 64 (3 * n + 64)) a1 a2 a3 a4 a5 a6 a7
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14f8c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13440) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n
    -> -> Hn.
  zstep. if_lit.
  zstep. if_false_by (bveq_ne n 0 ltac:(lia) ltac:(lia) ltac:(lia)).
  do 5 zstep.
  replace (Z.shiftl n 1 + n + 64) with (3 * n + 64) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  apply evt_done. reflexivity.
Qed.
