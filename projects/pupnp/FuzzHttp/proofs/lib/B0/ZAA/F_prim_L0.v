(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ALayout APrim.
Import ListNotations.
Open Scope Z_scope.

Definition gcts_entry := 0x60fe8%Z.

Section GCTS.
  Context {HC : HasCeiling}.
  Variable L : athread.
  Variables (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q : Z) (m0 : mem).

  Definition gcts_post (lo : Z) : machine_state -> Prop :=
    fun ms' => exists a1 m', ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz (at_thr L + 2800)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(q - 32, q)] m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m' /\ stk asegs m' lo q /\ thread_env L m'.

  #[using="Type"] Lemma gcts_spec : forall lo a0 a1,
    stk asegs m0 lo q -> alloc_ceiling <= lo -> lo <= q - 32 -> q mod 16 = 0 -> q <= 2^47 ->
    thread_env L m0 -> thread_layout_ok L -> mem_inv asegs m0 ->
    evt asegs (gcts_post lo)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz gcts_entry) fc None m0 (seg_rom asegs)).
  Proof.
    intros lo a0 a1 ST CLO LO AL QH TE TL MI. unfold gcts_entry.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR. unfold thread_layout_ok in TL.
    pose proof (munch_refl [(q - 32, q)] m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    te_split TE.
    assert (E : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    rewrite <- E in ST. carve_frame 16%nat ST. rewrite !E in *.
    zstep. sstep.
    zstep.
    carve_frame 16%nat ST.
    zstep. sstep.
    zstep. zstep. zstep. zstep.
    zstep. if_cases KT; zify_cond KT. { exfalso. revert KT. clear. intros KT. lia. }
    zstep. zstep.
    zstep.   zstep.
    change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
    zstep. zstep. zstep.
    zstep.   zstep.
    zstep. if_cases KC; zify_cond KC. { exfalso; lia. }
    zstep.   zstep. zstep.
    replace (q + -16 + -16 + 16) with (q + -16) by lia.
    zstep.
    release_frame FR0 ST (q + -16).
    zstep. if_cases KTH; zify_cond KTH. { exfalso; lia. }
    zstep. zstep.
    zstep. zstep. replace (q + -16 + 16) with q by lia. zstep.
    release_frame FR ST q.
    replace (at_thr L + 2047 + 753) with (at_thr L + 2800) by lia.
    apply evt_done. unfold gcts_post. eexists _, _. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
    unfold thread_env. repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.
End GCTS.
