(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Arr Walk Image. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_small R_thread R_cache_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Notation mem := (word -> option byte).

Definition rzlog_entry : Z := 0x1a1444.

Lemma rzlog_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (k lo : Z),
  (0 <= k < 8)%Z ->
  stk ctasegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 16)%Z -> (0xbcb000 <= lo)%Z ->
  mem_inv ctasegs m ->
  evt ctasegs (frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc k [(bv_unsigned sp - 16, bv_unsigned sp)]%Z lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (2 ^ (k + 4))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 rzlog_entry) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros Hk ST HLO HIMG MI. unfold rzlog_entry.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  let bs := eval vm_compute in (option.default [] (image_bytes ctasegs 0x105c0 8)) in
  assert (RC1 : ro_cells ctasegs m 0x105c0 [CB (length bs) bs])
    by (apply ro_cells_image; [exact MI| vm_compute; reflexivity| lia| cbn; lia]).
  let bs := eval vm_compute in (option.default [] (image_bytes ctasegs 0x10790 64)) in
  assert (RC2 : ro_cells ctasegs m 0x10790 [CB (length bs) bs])
    by (apply ro_cells_image; [exact MI| vm_compute; reflexivity| lia| cbn; lia]).
  cbn [length] in RC1, RC2.
  carve_frame 16%nat ST.
  assert (RZ : (16 <= 2 ^ (k + 4) <= 2048)%Z).
  { assert (K : (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7)%Z) by lia.
    destruct K as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; split; congruence. }
  do 6 zstep. ifF.
  rewrite (Z.mod_small (2 ^ (k + 4)) 4294967296) by lia.
  do 3 zstep. ifF.
  do 2 zstep.
  assert (P2 : Z.land (2 ^ (k + 4)) (2 ^ (k + 4) + -1) = 0%Z).
  { assert (K : (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7)%Z) by lia.
    destruct K as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; reflexivity. }
  rewrite P2. zstep. ifF.
  do 9 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let e := getreg 11%Z in lazymatch e with Z_to_bv 64 ?EA =>
    assert (RD : ov_read_bytes ctasegs mm (Z_to_bv 64 EA) 1 = Some [Z_to_bv 8 (k + 4)]);
    [ destruct RC2 as [_ RB];
      assert (K : (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7)%Z) by lia;
      destruct K as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]];
      lazymatch goal with |- ov_read_bytes _ _ (Z_to_bv 64 ?E) _ = _ =>
        let v := eval vm_compute in (E - 67472)%Z in
        let n := eval vm_compute in (Z.to_nat v) in
        pose proof (bytes_at_ov_read ctasegs mm 67472 _ n 1 RB ltac:(cbn; lia)) as R;
        unfold wa in R; replace (Z_to_bv 64 E) with (Z_to_bv 64 (67472 + Z.of_nat n)) by (f_equal; vm_compute; reflexivity);
        rewrite R; reflexivity end | ] end end.
  zstep. clear RD.
  unfold zxb. rewrite (Z_to_bv_small 8 (k + 4)) by (unfold bv_modulus; cbn [Z.of_N]; lia).
  do 3 zstep.
  replace (k + 4 + -4)%Z with k by lia.
  ifF.
  do 3 zstep.
  let e := getreg 14%Z in lazymatch e with Z_to_bv 64 ?EA =>
    assert (E4 : EA = (2 ^ (k + 4))%Z);
    [ assert (K : (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7)%Z) by lia;
      destruct K as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity | ] end.
  rewrite E4. ifF.
  do 3 zstep.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  finish.
Qed.
