(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ALayout APrim APrimLem ATacA ACells LJ LJU PEnv ATacFix F_memset AAllocCarve.
Import ListNotations.
Open Scope Z_scope.

Section F5.
  Context {HC : HasCeiling}.

  #[using="Type"] Lemma set_shadow_f5_spec : forall (SA len lo q : Z) (old : list cell)
         (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F_ : bvmap 5 word) (fc : bv 32) (m : mem),
    rw_cells asegs m SA old -> Z.of_nat (cells_size old) = len -> 0 < len ->
    0x7fff8000 <= SA -> SA + len <= 0x10007fff8000 -> asan_env asegs m ->
    stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - A0_RT_STACK -> q < 2^64 ->
    mem_inv asegs m -> a0 = wz SA -> a1 = wz len ->
    evt asegs (set_shadow_f5_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc SA len lo m)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz A0_set_shadow_f5) fc None m (seg_rom asegs)).
  Proof.
    intros SA len lo q old ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m
      OLD LEN L0 SALO SAHI AE ST CLO LOQ QH MI -> ->.
    unfold A0_set_shadow_f5. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof AE as (_ & _ & (_ & _ & _ & _ & ERM & _ & _ & _ & _ & _ & _ & _ & _ & GOT & _)). unfold env_real_mem in ERM. unfold env_got_rms in GOT.
    zstep. zstep. zstep.
    zstep. zstep. zstep.
    destruct (rw_cells_forget asegs m SA old OLD) as (junk & OLDJ).
    replace (cells_size old) with (Z.to_nat len) in OLDJ by (rewrite <- LEN; apply Nat2Z.id).
    assert (USA : bv_unsigned (wz SA) = SA) by (apply Z_to_bv_small; change (bv_modulus 64) with (2^64); clear - SALO SAHI L0; lia).
    assert (ULN : bv_unsigned (wz len) = len) by (apply Z_to_bv_small; change (bv_modulus 64) with (2^64); clear - SALO SAHI L0; lia).
    eapply evt_cut.
    { eapply (memset_spec ra (wz q) gp tp _ _ _ s0 s1 (wz SA) (wz 245) (wz len) _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F_ fc m junk); [rewrite USA, ULN; exact OLDJ| exact MI]. }
    cbv beta. intros ms' PM. unfold memset_post in PM.
    destruct PM as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m' & -> & MU & WM & MI' & NEW).
    rewrite USA, ULN in MU, NEW. change (bv_unsigned (wz 245) mod 256) with 245 in NEW.
    apply evt_done. unfold set_shadow_f5_post.
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, m'. split; [reflexivity|].
    split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros xo_ (O1 & _); split; [exact O1| exact I]|].
    split; [exact WM|]. split; [exact MI'|].
    split.
    { apply shadow_cells_of_CB. rewrite repeat_length, map_repeat. exact NEW. }
    split.
    { eapply (stk_gtransport _ m m'); [exact ST| exact (gmunch_of_munch _ _ _ MU)| exact WM|]. cbn [disjoint_from]. clear - SAHI CLO ACR. lia. }
    eapply (asan_env_frame asegs); [exact AE| exact MU| exact WM|].
    unfold env_safe. repeat (apply Forall_cons || apply Forall_nil). cbn [fst snd]. left. clear - SALO. lia.
  Qed.

  #[using="Type"] Theorem set_shadow_f5_ok : set_shadow_f5_stmt.
  Proof. unfold set_shadow_f5_stmt. intros. eapply set_shadow_f5_spec; eassumption. Qed.
End F5.
