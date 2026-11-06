(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.Ubsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbMuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbMuslMemmove2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbMuslMemmove.UbMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMuslMemmove.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.PuKeep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac not_kept ::= not_kept_fast.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPGen1.
Context {fx : FPState}.


Section SUMMARY.
  Variable rom : word -> option byte.

  Ltac post := repeat split; gres; rwH; rewrite ?at_addi; try reflexivity; try (f_equal; lia); try solve_keeps.

  (* [comment removed for export] *)
  Lemma mv_test_ft : forall (d s ret : word) n mem regs,
    (0 <= n < 2 ^ 63)%Z -> (bv_unsigned s + n < 2 ^ 64)%Z -> (bv_unsigned d + n < 2 ^ 64)%Z -> d <> s ->
    ~ ((0 < n)%Z /\ (bv_unsigned d + n <= bv_unsigned s \/ bv_unsigned s + n <= bv_unsigned d)%Z) ->
    getr regs 1 = ret -> getr regs 10 = d -> getr regs 11 = s -> getr regs 12 = Z_to_bv 64 n ->
    bv_unsigned (getr regs 14) = ((0 - (2 * n) mod 2 ^ 64) mod 2 ^ 64)%Z ->
    bv_unsigned (getr regs 13) = ((bv_unsigned s - (n + bv_unsigned d) mod 2 ^ 64) mod 2 ^ 64)%Z ->
    exists r, msteps RSEGS (mkst regs (0x736c8 : word) mem rom) (mkst r (0x736cc : word) mem rom)
      /\ getr r 1 = ret /\ getr r 10 = d /\ getr r 11 = s /\ getr r 12 = Z_to_bv 64 n /\ keeps regs r.
  Proof using.
    intros d s ret n mem regs Hn Hnws Hnwd Hds Hnap H1 H10 H11 H12 H14 H13.
    pose proof (u64_range s). pose proof (u64_range d).
    assert (Hne : bv_unsigned d <> bv_unsigned s) by (intros E; apply Hds; apply bv_eq; exact E).
    assert (LT : (bv_unsigned (getr regs 14) < bv_unsigned (getr regs 13))%Z).
    { rewrite H14, H13. destruct (Z.eq_dec n 0) as [->|Hn0].
      - change ((0 - (2 * 0) mod 2 ^ 64) mod 2 ^ 64)%Z with 0%Z. rewrite Z.add_0_l.
        rewrite (Z.mod_small (bv_unsigned d)) by lia.
        destruct (Z.lt_ge_cases (bv_unsigned s) (bv_unsigned d)).
        + rewrite (mod_eq_of _ _ (-1) (bv_unsigned s - bv_unsigned d + 2 ^ 64)); lia.
        + rewrite (mod_eq_of _ _ 0 (bv_unsigned s - bv_unsigned d)); lia.
      - apply apart_test_false; lia. }
    eexists. split.
    - stepb_ft F_73674 D_73674 ltac:(unfold c_ltu, bv_ltu; apply Z.ltb_lt; exact LT).
      apply mst_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Theorem memmove_overlap : forall mem0 (d s : word) (n : Z) (bs : list byte) regs (ret : word),
    (0 <= n < 2 ^ 63)%Z -> length bs = Z.to_nat n ->
    (forall i, (0 <= i < n)%Z -> mem0 (at_ s i) = Some (b_ bs i)) ->
    store_ok RSEGS mem0 d (Z.to_nat n) = true ->
    (bv_unsigned s + n < 2 ^ 64)%Z -> (bv_unsigned d + n < 2 ^ 64)%Z ->
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = d -> getr regs 11 = s -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps RSEGS (mkst regs (0x736b4 : word) mem0 rom) (mkst regs' ret (wbytes mem0 d bs) rom)
      /\ keeps regs regs'.
  Proof using.
    intros mem0 d s n bs regs ret Hn Hlen Hsrc Hdst Hnws Hnwd Hret H1 H10 H11 H12.
    pose proof (u64_range s). pose proof (u64_range d).
    destruct (decide (d = s)) as [Hds|Hds].
    - (* [comment removed for export] *)
      exists regs. split; [|apply keeps_refl].
      rewrite (move_id mem0 d s n bs Hn Hlen Hsrc Hdst Hnwd Hds).
      apply (mv_same d s ret mem0 rom Hret regs H1 H10 H11 Hds).
    - destruct (Z_lt_dec 0 n) as [Hnpos|Hn0];
      [destruct (Z_le_dec (bv_unsigned d + n) (bv_unsigned s)) as [Hap1|Hap1];
       [|destruct (Z_le_dec (bv_unsigned s + n) (bv_unsigned d)) as [Hap2|Hap2]]|].
      + (* [comment removed for export] *)
        apply (mv_apart_pos mem0 d s n bs rom); try assumption; try lia.
        constructor; try assumption; try lia; try (rewrite Hlen; assumption).
        apply (src_rdn mem0 s n bs Hn Hlen Hsrc Hnws).
      + (* [comment removed for export] *)
        apply (mv_apart_pos mem0 d s n bs rom); try assumption; try lia.
        constructor; try assumption; try lia; try (rewrite Hlen; assumption).
        apply (src_rdn mem0 s n bs Hn Hlen Hsrc Hnws).
      + (* [comment removed for export] *)
        destruct (mv_pro d s ret n mem0 rom Hn regs H1 H10 H11 H12 Hds) as (r & RUN & R1 & R10 & R11 & R12 & R14 & R13 & K).
        destruct (mv_test_ft d s ret n mem0 r Hn Hnws Hnwd Hds ltac:(lia) R1 R10 R11 R12 R14 R13) as (r1 & RUN1 & S1 & S10 & S11 & S12 & K1).
        destruct (Z.lt_ge_cases (bv_unsigned d) (bv_unsigned s)) as [Hlt|Hge].
        * destruct (fwd_entry mem0 d s n bs rom Hn Hlen Hsrc Hdst Hnws Hnwd Hlt r1 ret Hret S1 S10 S11 S12) as (r2 & RUN2 & K2).
          exists r2. split; [|eapply keeps_trans; [eapply keeps_trans|]; eassumption].
          rewrite <- (memF_n mem0 d n bs Hlen).
          eapply msteps_trans; [exact RUN|]. eapply msteps_trans; [exact RUN1|]. exact RUN2.
        * assert (Hgt : (bv_unsigned s < bv_unsigned d)%Z).
          { destruct (Z.eq_dec (bv_unsigned s) (bv_unsigned d)) as [E|E]; [|lia]. exfalso. apply Hds. apply bv_eq. symmetry. exact E. }
          destruct (bwd_entry mem0 d s n bs rom Hn Hlen Hsrc Hdst Hnws Hnwd Hgt r1 ret Hret S1 S10 S11 S12) as (r2 & RUN2 & K2).
          exists r2. split; [|eapply keeps_trans; [eapply keeps_trans|]; eassumption].
          rewrite <- (memB_0 mem0 d bs).
          eapply msteps_trans; [exact RUN|]. eapply msteps_trans; [exact RUN1|].
          rewrite <- (memB_n mem0 d n bs Hlen) at 1. exact RUN2.
      + (* [comment removed for export] *)
        assert (n = 0%Z) as Hz by lia.
        destruct (mv_pro d s ret n mem0 rom Hn regs H1 H10 H11 H12 Hds) as (r & RUN & R1 & R10 & R11 & R12 & R14 & R13 & K).
        destruct (mv_test_ft d s ret n mem0 r Hn Hnws Hnwd Hds ltac:(lia) R1 R10 R11 R12 R14 R13) as (r1 & RUN1 & S1 & S10 & S11 & S12 & K1).
        destruct (Z.lt_ge_cases (bv_unsigned d) (bv_unsigned s)) as [Hlt|Hge].
        * destruct (fwd_entry mem0 d s n bs rom Hn Hlen Hsrc Hdst Hnws Hnwd Hlt r1 ret Hret S1 S10 S11 S12) as (r2 & RUN2 & K2).
          exists r2. split; [|eapply keeps_trans; [eapply keeps_trans|]; eassumption].
          rewrite <- (memF_n mem0 d n bs Hlen).
          eapply msteps_trans; [exact RUN|]. eapply msteps_trans; [exact RUN1|]. exact RUN2.
        * assert (Hgt : (bv_unsigned s < bv_unsigned d)%Z).
          { destruct (Z.eq_dec (bv_unsigned s) (bv_unsigned d)) as [E|E]; [|lia]. exfalso. apply Hds. apply bv_eq. symmetry. exact E. }
          destruct (bwd_entry mem0 d s n bs rom Hn Hlen Hsrc Hdst Hnws Hnwd Hgt r1 ret Hret S1 S10 S11 S12) as (r2 & RUN2 & K2).
          exists r2. split; [|eapply keeps_trans; [eapply keeps_trans|]; eassumption].
          rewrite <- (memB_0 mem0 d bs).
          eapply msteps_trans; [exact RUN|]. eapply msteps_trans; [exact RUN1|].
          rewrite <- (memB_n mem0 d n bs Hlen) at 1. exact RUN2.
  Qed.

  (* [comment removed for export] *)
  Theorem memmove_apart : forall mem0 (d s : word) (n : Z) (bs : list byte) regs (ret : word),
    mcH mem0 d s n bs ->
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = d -> getr regs 11 = s -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps RSEGS (mkst regs (0x736b4 : word) mem0 rom) (mkst regs' ret (wbytes mem0 d bs) rom)
      /\ keeps regs regs'.
  Proof using.
    intros mem0 d s n bs regs ret HOK Hret H1 H10 H11 H12.
    pose proof (u64_range s). pose proof (u64_range d).
    destruct HOK as [Hn Hlen Hsrc Hdst Hdisj Hnws Hnwd].
    assert (Hn63 : (n < 2 ^ 63)%Z) by lia.
    destruct (decide (d = s)) as [Hds|Hds].
    - (* [comment removed for export] *)
      assert (n = 0%Z) by (rewrite Hds in Hdisj; lia). subst n.
      destruct bs; [|discriminate Hlen]. cbn [wbytes].
      exists regs. split; [|apply keeps_refl].
      apply (mv_same d s ret mem0 rom Hret regs H1 H10 H11 Hds).
    - destruct (Z_lt_dec 0 n) as [Hnpos|Hn0].
      + apply (mv_apart_pos mem0 d s n bs rom); try assumption. constructor; assumption.
      + assert (n = 0%Z) by lia. subst n.
        destruct bs; [|discriminate Hlen].
        destruct (mv_pro d s ret 0 mem0 rom ltac:(lia) regs H1 H10 H11 H12 Hds) as (r & RUN & R1 & R10 & R11 & R12 & R14 & R13 & K).
        destruct (mv_test_ft d s ret 0 mem0 r ltac:(lia) ltac:(lia) ltac:(lia) Hds ltac:(lia) R1 R10 R11 R12 R14 R13) as (r1 & RUN1 & S1 & S10 & S11 & S12 & K1).
        assert (Hsrc0 : forall i, (0 <= i < 0)%Z -> mem0 (at_ s i) = Some (b_ [] i)) by (intros; lia).
        assert (Hdst0 : store_ok RSEGS mem0 d (Z.to_nat 0) = true) by reflexivity.
        destruct (Z.lt_ge_cases (bv_unsigned d) (bv_unsigned s)) as [Hlt|Hge].
        * destruct (fwd_entry mem0 d s 0 [] rom ltac:(lia) eq_refl Hsrc0 Hdst0 ltac:(lia) ltac:(lia) Hlt r1 ret Hret S1 S10 S11 S12) as (r2 & RUN2 & K2).
          exists r2. split; [|eapply keeps_trans; [eapply keeps_trans|]; eassumption].
          rewrite <- (memF_n mem0 d 0 [] eq_refl).
          eapply msteps_trans; [exact RUN|]. eapply msteps_trans; [exact RUN1|]. exact RUN2.
        * assert (Hgt : (bv_unsigned s < bv_unsigned d)%Z).
          { destruct (Z.eq_dec (bv_unsigned s) (bv_unsigned d)) as [E|E]; [|lia]. exfalso. apply Hds. apply bv_eq. symmetry. exact E. }
          destruct (bwd_entry mem0 d s 0 [] rom ltac:(lia) eq_refl Hsrc0 Hdst0 ltac:(lia) ltac:(lia) Hgt r1 ret Hret S1 S10 S11 S12) as (r2 & RUN2 & K2).
          exists r2. split; [|eapply keeps_trans; [eapply keeps_trans|]; eassumption].
          rewrite <- (memB_0 mem0 d []).
          eapply msteps_trans; [exact RUN|]. eapply msteps_trans; [exact RUN1|].
          rewrite <- (memB_n mem0 d 0 [] eq_refl) at 1. exact RUN2.
  Qed.
End SUMMARY.
End FPGen1.
End UbMuslMemmove2.
Module UbStrlenHello.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.PuKeep.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
#[local] Ltac not_kept ::= not_kept_fast.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Abbreviation SSEGS := Ubsan.M.loaded_segments.
Section FPGen1.
Context {fx : FPState}.



(* [comment removed for export] *)
Lemma rdn_img1 : forall mem (a : word) b, mem a = None -> seg_rom SSEGS a = Some b -> rdn SSEGS mem a 1 = Some [b].
Proof using. intros mem a b Hm Hr. cbn [rdn]. rewrite Hm, Hr. reflexivity. Qed.

Lemma rdn_clear : forall k mem (x : word),
  (forall i, (0 <= i < Z.of_nat k)%Z -> mem (at_ x i) = None) -> (bv_unsigned x + Z.of_nat k <= 2 ^ 64)%Z ->
  rdn SSEGS mem x k = rdn SSEGS (fun _ => None) x k.
Proof using.
  induction k as [|k IH]; intros mem x Hm Hx; [reflexivity|]. cbn [rdn]. pose proof (u64_range x).
  pose proof (Hm 0%Z ltac:(lia)) as H0. rewrite at_0 in H0. rewrite H0.
  destruct (seg_rom SSEGS x); [|reflexivity].
  destruct k as [|k2]; [reflexivity|].
  rewrite (IH mem (x + 1)%bv); [reflexivity| |rewrite word_succ_at, at_u; lia].
  intros i Hi. rewrite word_succ_at, at_at. apply Hm. lia.
Qed.

Lemma rdn_img8 : forall mem (a : word) bs,
  (forall i, (0 <= i < 8)%Z -> mem (at_ a i) = None) -> (bv_unsigned a + 8 <= 2 ^ 64)%Z ->
  rdn SSEGS (fun _ => None) a 8 = Some bs -> rdn SSEGS mem a 8 = Some bs.
Proof using. intros mem a bs Hm Ha H8. rewrite (rdn_clear 8 mem a); [exact H8 | exact Hm | exact Ha]. Qed.

Lemma rom_128e4 : seg_rom SSEGS (0x128d1 : word) = Some (0x48 : byte).
Proof using. vm_refl_bv. Qed.
Lemma rom_128e5 : seg_rom SSEGS (0x128d2 : word) = Some (0x65 : byte).
Proof using. vm_refl_bv. Qed.
Lemma rom_128e6 : seg_rom SSEGS (0x128d3 : word) = Some (0x6c : byte).
Proof using. vm_refl_bv. Qed.
Lemma rom_128e7 : seg_rom SSEGS (0x128d4 : word) = Some (0x6c : byte).
Proof using. vm_refl_bv. Qed.
Lemma rom_128e8 : seg_rom SSEGS (0x128d5 : word) = Some (0x6f : byte).
Proof using. vm_refl_bv. Qed.
Lemma rom_128e9 : seg_rom SSEGS (0x128d6 : word) = Some (0x20 : byte).
Proof using. vm_refl_bv. Qed.
Lemma rom_128ea : seg_rom SSEGS (0x128d7 : word) = Some (0x57 : byte).
Proof using. vm_refl_bv. Qed.
Lemma rom_128eb : seg_rom SSEGS (0x128d8 : word) = Some (0x6f : byte).
Proof using. vm_refl_bv. Qed.
Lemma rom_128ec : seg_rom SSEGS (0x128d9 : word) = Some (0x72 : byte).
Proof using. vm_refl_bv. Qed.
Lemma rom_128ed : seg_rom SSEGS (0x128da : word) = Some (0x6c : byte).
Proof using. vm_refl_bv. Qed.
Lemma rom_128ee : seg_rom SSEGS (0x128db : word) = Some (0x64 : byte).
Proof using. vm_refl_bv. Qed.
Lemma rom_128ef : seg_rom SSEGS (0x128dc : word) = Some (0x00 : byte).
Proof using. vm_refl_bv. Qed.
Lemma rom8_13068 : rdn SSEGS (fun _ => None) (0x13050 : word) 8 = Some [(0x00 : byte); (0x01 : byte); (0x01 : byte); (0x01 : byte); (0x01 : byte); (0x01 : byte); (0x01 : byte); (0x01 : byte)].
Proof using. vm_refl_bv. Qed.
Lemma romv_13068 : bytes_le_to_Z [(0x00 : byte); (0x01 : byte); (0x01 : byte); (0x01 : byte); (0x01 : byte); (0x01 : byte); (0x01 : byte); (0x01 : byte)] = bv_unsigned (0x101010101010100 : word).
Proof using. vm_refl_bv. Qed.
Lemma rom8_13050 : rdn SSEGS (fun _ => None) (0x13038 : word) 8 = Some [(0x80 : byte); (0x80 : byte); (0x80 : byte); (0x80 : byte); (0x80 : byte); (0x80 : byte); (0x80 : byte); (0x80 : byte)].
Proof using. vm_refl_bv. Qed.
Lemma romv_13050 : bytes_le_to_Z [(0x80 : byte); (0x80 : byte); (0x80 : byte); (0x80 : byte); (0x80 : byte); (0x80 : byte); (0x80 : byte); (0x80 : byte)] = bv_unsigned (0x8080808080808080 : word).
Proof using. vm_refl_bv. Qed.
Lemma rom8_128e8 : rdn SSEGS (fun _ => None) (0x128d8 : word) 8 = Some [(0x6f : byte); (0x72 : byte); (0x6c : byte); (0x64 : byte); (0x00 : byte); (0x5f : byte); (0x5f : byte); (0x5a : byte)].
Proof using. vm_refl_bv. Qed.
Lemma romv_128e8 : bytes_le_to_Z [(0x6f : byte); (0x72 : byte); (0x6c : byte); (0x64 : byte); (0x00 : byte); (0x5f : byte); (0x5f : byte); (0x5a : byte)] = bv_unsigned (0x5a5f5f00646c726f : word).
Proof using. vm_refl_bv. Qed.

Section STRLEN.
  Variable mem : word -> option byte.
  Variable rom : word -> option byte.
  Hypothesis Himg : forall a : word, ((0x128d1 <= bv_unsigned a < 0x128e0) \/ (0x13038 <= bv_unsigned a < 0x13040) \/ (0x13050 <= bv_unsigned a < 0x13058))%Z -> mem a = None.

  Ltac img1 a := apply Himg; vm_compute; intuition lia.
  Ltac rd1 R := eapply rdn_img1; [apply Himg; cbv; intuition congruence | exact R].

  Theorem strlen_hello : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = (0x128d1 : word) ->
    exists regs',
      msteps SSEGS (mkst regs (0x73960 : word) mem rom) (mkst regs' ret mem rom)
      /\ keeps_cs regs regs' /\ getr regs' 10 = Z_to_bv 64 11.
  Proof using Himg.
    intros regs ret Hret H1 H10.
    eexists. split; [|split].
    - 
      stepn F_7390c D_7390c.
      stepn F_73910 D_73910.
      stepb_ft F_73914 D_73914 ltac:(rewrite ?H10; cond_compute).
      chain_step; [reflexivity | eapply step_lbu; [exact F_73918 | reflexivity | exact D_73918 | gres; rewrite ?H10; imm_norm; wlits; rd1 rom_128e4] | step_simpl]; vnorm.
      stepb_ft F_7391c D_7391c ltac:(rewrite ?H10; cond_compute).
      stepn F_73920 D_73920.
      stepn F_73924 D_73924.
      stepn F_73928 D_73928.
      stepn F_7392c D_7392c.
      stepb_ft F_73930 D_73930 ltac:(rewrite ?H10; cond_compute).
      chain_step; [reflexivity | eapply step_lbu; [exact F_73934 | reflexivity | exact D_73934 | gres; rewrite ?H10; imm_norm; wlits; rd1 rom_128e5] | step_simpl]; vnorm.
      stepn F_73938 D_73938.
      stepn F_7393c D_7393c.
      stepb_tk F_73940 D_73940 ltac:(rewrite ?H10; cond_compute).
      stepn F_73928 D_73928.
      stepn F_7392c D_7392c.
      stepb_ft F_73930 D_73930 ltac:(rewrite ?H10; cond_compute).
      chain_step; [reflexivity | eapply step_lbu; [exact F_73934 | reflexivity | exact D_73934 | gres; rewrite ?H10; imm_norm; wlits; rd1 rom_128e6] | step_simpl]; vnorm.
      stepn F_73938 D_73938.
      stepn F_7393c D_7393c.
      stepb_tk F_73940 D_73940 ltac:(rewrite ?H10; cond_compute).
      stepn F_73928 D_73928.
      stepn F_7392c D_7392c.
      stepb_ft F_73930 D_73930 ltac:(rewrite ?H10; cond_compute).
      chain_step; [reflexivity | eapply step_lbu; [exact F_73934 | reflexivity | exact D_73934 | gres; rewrite ?H10; imm_norm; wlits; rd1 rom_128e7] | step_simpl]; vnorm.
      stepn F_73938 D_73938.
      stepn F_7393c D_7393c.
      stepb_tk F_73940 D_73940 ltac:(rewrite ?H10; cond_compute).
      stepn F_73928 D_73928.
      stepn F_7392c D_7392c.
      stepb_ft F_73930 D_73930 ltac:(rewrite ?H10; cond_compute).
      chain_step; [reflexivity | eapply step_lbu; [exact F_73934 | reflexivity | exact D_73934 | gres; rewrite ?H10; imm_norm; wlits; rd1 rom_128e8] | step_simpl]; vnorm.
      stepn F_73938 D_73938.
      stepn F_7393c D_7393c.
      stepb_tk F_73940 D_73940 ltac:(rewrite ?H10; cond_compute).
      stepn F_73928 D_73928.
      stepn F_7392c D_7392c.
      stepb_ft F_73930 D_73930 ltac:(rewrite ?H10; cond_compute).
      chain_step; [reflexivity | eapply step_lbu; [exact F_73934 | reflexivity | exact D_73934 | gres; rewrite ?H10; imm_norm; wlits; rd1 rom_128e9] | step_simpl]; vnorm.
      stepn F_73938 D_73938.
      stepn F_7393c D_7393c.
      stepb_tk F_73940 D_73940 ltac:(rewrite ?H10; cond_compute).
      stepn F_73928 D_73928.
      stepn F_7392c D_7392c.
      stepb_ft F_73930 D_73930 ltac:(rewrite ?H10; cond_compute).
      chain_step; [reflexivity | eapply step_lbu; [exact F_73934 | reflexivity | exact D_73934 | gres; rewrite ?H10; imm_norm; wlits; rd1 rom_128ea] | step_simpl]; vnorm.
      stepn F_73938 D_73938.
      stepn F_7393c D_7393c.
      stepb_tk F_73940 D_73940 ltac:(rewrite ?H10; cond_compute).
      stepn F_73928 D_73928.
      stepn F_7392c D_7392c.
      stepb_tk F_73930 D_73930 ltac:(rewrite ?H10; cond_compute).
      stepn F_73948 D_73948.
      stepn F_7394c D_7394c.
      chain_step; [reflexivity | eapply step_ld; [exact F_73950 | reflexivity | exact D_73950 | gres; rewrite ?H10; imm_norm; wlits; apply rdn_img8; [intros i Hi; apply Himg; rewrite at_u by (rewrite bv_unsigned_BV; lia); rewrite bv_unsigned_BV; lia | rewrite bv_unsigned_BV; lia | exact rom8_13068] | exact romv_13068] | step_simpl]; vnorm.
      chain_step; [reflexivity | eapply step_ld; [exact F_73954 | reflexivity | exact D_73954 | gres; rewrite ?H10; imm_norm; wlits; apply rdn_img8; [intros i Hi; apply Himg; rewrite at_u by (rewrite bv_unsigned_BV; lia); rewrite bv_unsigned_BV; lia | rewrite bv_unsigned_BV; lia | exact rom8_13050] | exact romv_13050] | step_simpl]; vnorm.
      stepn F_73958 D_73958.
      stepn F_7395c D_7395c.
      chain_step; [reflexivity | eapply step_ld; [exact F_73960 | reflexivity | exact D_73960 | gres; rewrite ?H10; imm_norm; wlits; apply rdn_img8; [intros i Hi; apply Himg; rewrite at_u by (rewrite bv_unsigned_BV; lia); rewrite bv_unsigned_BV; lia | rewrite bv_unsigned_BV; lia | exact rom8_128e8] | exact romv_128e8] | step_simpl]; vnorm.
      stepn F_73964 D_73964.
      stepn F_73968 D_73968.
      stepn F_7396c D_7396c.
      stepn F_73970 D_73970.
      stepn F_73974 D_73974.
      stepb_ft F_73978 D_73978 ltac:(rewrite ?H10; cond_compute).
      chain_step; [reflexivity | eapply step_lbu; [exact F_7397c | reflexivity | exact D_7397c | gres; rewrite ?H10; imm_norm; wlits; rd1 rom_128eb] | step_simpl]; vnorm.
      stepn F_73980 D_73980.
      stepn F_73984 D_73984.
      stepb_tk F_73988 D_73988 ltac:(rewrite ?H10; cond_compute).
      chain_step; [reflexivity | eapply step_lbu; [exact F_7397c | reflexivity | exact D_7397c | gres; rewrite ?H10; imm_norm; wlits; rd1 rom_128ec] | step_simpl]; vnorm.
      stepn F_73980 D_73980.
      stepn F_73984 D_73984.
      stepb_tk F_73988 D_73988 ltac:(rewrite ?H10; cond_compute).
      chain_step; [reflexivity | eapply step_lbu; [exact F_7397c | reflexivity | exact D_7397c | gres; rewrite ?H10; imm_norm; wlits; rd1 rom_128ed] | step_simpl]; vnorm.
      stepn F_73980 D_73980.
      stepn F_73984 D_73984.
      stepb_tk F_73988 D_73988 ltac:(rewrite ?H10; cond_compute).
      chain_step; [reflexivity | eapply step_lbu; [exact F_7397c | reflexivity | exact D_7397c | gres; rewrite ?H10; imm_norm; wlits; rd1 rom_128ee] | step_simpl]; vnorm.
      stepn F_73980 D_73980.
      stepn F_73984 D_73984.
      stepb_tk F_73988 D_73988 ltac:(rewrite ?H10; cond_compute).
      chain_step; [reflexivity | eapply step_lbu; [exact F_7397c | reflexivity | exact D_7397c | gres; rewrite ?H10; imm_norm; wlits; rd1 rom_128ef] | step_simpl]; vnorm.
      stepn F_73980 D_73980.
      stepn F_73984 D_73984.
      stepb_ft F_73988 D_73988 ltac:(rewrite ?H10; cond_compute).
      stepn F_7398c D_7398c.
      stepjr F_73990 D_73990 ret ltac:(gres; rewrite ?H1; reflexivity).
      imm_norm. rewrite Hret. pu_refl.
    - solve_keeps_cs.
    - gres. rewrite H10. vm_compute. reflexivity.
  Qed.
End STRLEN.
End FPGen1.
End UbStrlenHello.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbMuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemsetCode OSSVerify.Proofs.glaze.binary_reflection.lib.GlzStrResizeUbsan2. Import OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbMuslMemmove.UbMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemsetCode OSSVerify.Proofs.glaze.binary_reflection.lib.GlzStrResizeUbsan2.UbMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.UbMuslMemmove UbMuslMemmove2 UbStrlenHello.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesLibc OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesMove OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesStr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import GPS. Import GCL. Import GNL. Import GNM. Import GNS.
Open Scope Z_scope.

#[local] Abbreviation USEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Lemma ubsan_segs_wr_ok : segs_wr_ok USEGS.
Proof.
  intros seg Hin Hw. cbn in Hin.
  repeat (destruct Hin as [<-|Hin]; [first [reflexivity | discriminate Hw] |]). destruct Hin.
Qed.

Theorem ubsan_fill_spec : fill_spec USEGS 0x73830 two64.
Proof.
  intros fx mem0 s c n regs ret Hn Hnw Hst Hc Hrok H1 H10 H11 H12.
  destruct (@memset_summary fx mem0 s c ret n (seg_rom USEGS) Hn Hnw Hst Hrok regs H10 H11 H12 H1)
    as (regs' & RUN & P10 & AG).
  exists regs'. split; [exact RUN|]. split; [| exact P10].
  apply keeps_kept_ok. apply ms_agree_keeps. exact AG.
Qed.

Theorem ubsan_copy_spec : copy_spec USEGS 0x732b0.
Proof.
  intros fx mem0 dst src n bs regs ret Hn Hlen Hrd Hst Hdisj Hnws Hnwd Hrok H1 H10 H11 H12.
  pose proof (u64_range (Z_to_bv 64 n)) as Hr.
  assert (HOK : mcH mem0 dst src n bs).
  { constructor; try assumption. pose proof (u64_range dst). lia. }
  destruct (@ref_memcpy fx mem0 dst src n bs (seg_rom USEGS) HOK regs ret Hrok H1 H10 H11 H12) as (regs' & RUN & K).
  exists regs'. split.
  { unfold mkstF. replace (Z_to_bv 64 0x732b0) with (0x732b0%bv : word) by (apply bv_eq; vm_compute; reflexivity). exact RUN. }
  split; [apply keeps_kept_ok; exact K|].
  rewrite (K 10%bv) by (cbn; tauto). exact H10.
Qed.

Theorem ubsan_copy_spec_mv : copy_spec USEGS 0x736b4.
Proof.
  intros fx mem0 dst src n bs regs ret Hn Hlen Hrd Hst Hdisj Hnws Hnwd Hrok H1 H10 H11 H12.
  assert (HOK : mcH mem0 dst src n bs).
  { constructor; try assumption. pose proof (u64_range dst). lia. }
  destruct (@memmove_apart fx (seg_rom USEGS) mem0 dst src n bs regs ret HOK Hrok H1 H10 H11 H12) as (regs' & RUN & K).
  exists regs'. split.
  { unfold mkstF. replace (Z_to_bv 64 0x736b4) with (0x736b4%bv : word) by (apply bv_eq; vm_compute; reflexivity). exact RUN. }
  split; [apply keeps_kept_ok; exact K|].
  rewrite (K 10%bv) by (cbn; tauto). exact H10.
Qed.

Theorem ubsan_move_spec : move_spec USEGS 0x736b4.
Proof.
  intros fx mem0 dst src n bs regs ret Hn Hlen Hsrc Hst Hnws Hnwd Hrok H1 H10 H11 H12.
  destruct (@memmove_overlap fx (seg_rom USEGS) mem0 dst src n bs regs ret Hn Hlen Hsrc Hst Hnws Hnwd Hrok H1 H10 H11 H12)
    as (regs' & RUN & K).
  exists regs'. split.
  { unfold mkstF. replace (Z_to_bv 64 0x736b4) with (0x736b4%bv : word) by (apply bv_eq; vm_compute; reflexivity). exact RUN. }
  split; [apply keeps_kept_ok; exact K|].
  rewrite (K 10%bv) by (cbn; tauto). exact H10.
Qed.

(* [comment removed for export] *)
Theorem ubsan_strlen_spec : strlen_lit_spec USEGS 0x73960 0x128d1 11 0x10000 0x75000.
Proof.
  intros fx mem0 regs ret Himg Hrok H1 H10.
  assert (Himg' : forall a : word, ((0x128d1 <= bv_unsigned a < 0x128e0) \/ (0x13038 <= bv_unsigned a < 0x13040)
                                     \/ (0x13050 <= bv_unsigned a < 0x13058))%Z -> mem0 a = None).
  { intros a Ha. apply Himg. lia. }
  destruct (@strlen_hello fx mem0 (seg_rom USEGS) Himg' regs ret Hrok H1
              ltac:(rewrite H10; apply bv_eq; vm_compute; reflexivity)) as (regs' & RUN & K & A0).
  exists regs'. split.
  { unfold mkstF. replace (Z_to_bv 64 0x73960) with (0x73960%bv : word) by (apply bv_eq; vm_compute; reflexivity). exact RUN. }
  split; [apply keeps_cs_kept_ok; exact K | exact A0].
Qed.

Section Plain.
Context {RC : run_ceil}.
Variable A : atable.
Variable nx0 : nat.
Variable SWIN : list (Z * Z).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable FDS0 : list (word * FdEntry).
Variable AINV : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINV_frame : forall Lc B C M M' mdl,
  AINV Lc B C M mdl -> (forall a, M' a <> M a -> owned SWIN PERMc SPTOPc Lc a /\ M' a <> None) -> AINV Lc B C M' mdl.
Variable FXOK : FX -> Prop.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.
Variable RZ : GPS.rz_t.
Hypothesis RZ_step : GPS.RZ_STEP USEGS RZ.
Hypothesis RZ_msteps : GPS.RZ_MSTEPS USEGS RZ.
Variable G : gtable.
Hypothesis G_memset : g_memset G = 0x73830.
Hypothesis G_memcpy : g_memcpy G = 0x732b0.
Hypothesis G_memmove : g_memmove G = 0x736b4.
Hypothesis G_strlen : g_strlen G = 0x73960.
Hypothesis G_ro : g_ro_lo G = 0x10000 /\ g_ro_hi G = 0x75000.   (* [comment removed for export] *)
Hypothesis G_hello : g_hello G = 0x128d1.

Theorem ubsan_OBL_memset : OBL_memset USEGS A nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ G.
Proof.
  eapply (node_memset_sound USEGS A nx0 SWIN PERMc SPTOPc); try eassumption; try exact ubsan_segs_wr_ok.
  rewrite G_memset. exact ubsan_fill_spec.
Qed.

Theorem ubsan_OBL_memcpy : OBL_memcpy USEGS A nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ G.
Proof.
  eapply (node_memcpy_sound USEGS A nx0 SWIN PERMc SPTOPc); try eassumption; try exact ubsan_segs_wr_ok.
  rewrite G_memcpy. exact ubsan_copy_spec.
Qed.

(* [comment removed for export] *)
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment USEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.

Theorem ubsan_OBL_memmove : OBL_memmove USEGS A nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ G.
Proof.
  eapply (node_memmove_sound USEGS A nx0 SWIN PERMc SPTOPc); try eassumption; try exact ubsan_segs_wr_ok.
  - rewrite G_memmove. exact ubsan_copy_spec_mv.
  - rewrite G_memmove. exact ubsan_move_spec.
Qed.

Theorem ubsan_OBL_strlen : OBL_strlen USEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ G.
Proof.
  eapply (node_strlen_sound USEGS nx0 SWIN PERMc SPTOPc); try eassumption.
  destruct G_ro as [-> ->]. rewrite G_strlen, G_hello. exact ubsan_strlen_spec.
Qed.
End Plain.
