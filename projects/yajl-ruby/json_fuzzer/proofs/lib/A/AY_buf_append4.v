(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep SFW1_lemmas.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlLeaf YajlBuf YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AI_shadow AYajlRep AYajl_iface AY_rz AY_buf_append1 AY_buf_append2 AY_buf_append3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition AAPP_SIZE : Z := 0x86aec.
Definition AAPP_LOOP : Z := 0x86b20.
Definition AAPP_LOOPX : Z := 0x86b34.
Definition AAPP_REA_RET : Z := 0x86ba4.

End RC__1.
Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma ens_need_loop_ge : forall f want need used, 0 < need -> need <= ens_need_loop f want need used.
Proof. aceil.
  induction f as [|f IH]; intros want need used Hn; cbn [ens_need_loop]; [lia|].
  destruct ((need - used <=? want) && (0 <? need)); [| lia].
  specialize (IH want (need * 2) used ltac:(lia)). lia.
Qed.

Lemma asize_loop : forall (P : acc -> Prop) (fuel : nat) (need : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s4 s5 s6v s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (used want : Z),
  0 < need < 2^31 -> 0 <= used < need -> 0 <= want < 2^31 ->
  want + used < need * 2 ^ (Z.of_nat fuel) ->
  ens_need_loop fuel want need used < 2^31 ->
  evtA asegs P (fun ms' => exists a2' a3',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz used) a2' a3' a4 a5 a6 a7 s2 (wz want) s4 s5
                     (wz (ens_need_loop fuel want need used)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (wz AAPP_LOOPX) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz used) (wz need) a3 a4 a5 a6 a7 s2 (wz want) s4 s5 s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz AAPP_LOOP) fc None m (seg_rom asegs)).
Proof. aceil.
  induction fuel as [|fuel IH]; intros until want; intros NB UB WB FB RB; unfold wz, AAPP_LOOP, AAPP_LOOPX in *.
  - cbn [ens_need_loop] in *. change (2 ^ Z.of_nat 0) with 1 in FB.
    zstepA. zstepA. if_cases K0; zify_cond K0. 1:{ kill K0. }
    zstepA. zstepA.
    replace (bv_swrap 32 (need - used)) with (need - used) by (rewrite ybv_swrap32_eq; rewrite Z.mod_small; lia).
    zstepA. if_cases K1; zify_cond K1. 1:{ kill K1. }
    apply evtA_done. eexists _, _. reflexivity.
  - cbn [ens_need_loop] in RB |- *.
    zstepA. zstepA. if_cases K0; zify_cond K0. 1:{ kill K0. }
    zstepA. zstepA.
    replace (bv_swrap 32 (need - used)) with (need - used) by (rewrite ybv_swrap32_eq; rewrite Z.mod_small; lia).
    destruct (Z.leb_spec (need - used) want); destruct (Z.ltb_spec 0 need); try lia; cbn [andb] in RB |- *.
    + pose proof (ens_need_loop_ge fuel want (need * 2) used ltac:(lia)) as GE.
      replace (bv_swrap 32 (Z.shiftl need 1)) with (need * 2)
        by (rewrite Z.shiftl_mul_pow2, ybv_swrap32_eq by lia; rewrite Z.mod_small; lia).
      zstepA. if_cases K1; zify_cond K1. 2:{ kill K1. }
      rewrite Nat2Z.inj_succ, Z.pow_succ_r in FB by lia.
      apply IH; try lia. all: replace (need * 2 * 2 ^ Z.of_nat fuel) with (need * (2 * 2 ^ Z.of_nat fuel)) by ring; exact FB.
    + zstepA. if_cases K1; zify_cond K1. 1:{ kill K1. }
      apply evtA_done. eexists _, _. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition asizeA_post (rav gp tp s0v s1v s3v s4v s8v s9v s11v : word) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem)
    (B D1 AF len1 used1 r SQ sh7 sh10 : Z) (j24 : list byte) : machine_state -> Prop :=
  fun ms' =>
    (r = len1 /\ exists a2 a3,
       ms' = MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 len1) (Z_to_bv 64 used1) a2 a3 a4 a5 a6 a7
                    (Z_to_bv 64 (B + 8)) s3v s4v (Z_to_bv 64 (B + 4)) (Z_to_bv 64 r) (Z_to_bv 64 sh7) s8v s9v (Z_to_bv 64 sh10) s11v t3 t4 t5 t6)
                F1 (Z_to_bv 64 AAPP_COPY) fc1 None m1 (seg_rom asegs))
    \/ (r <> len1 /\ exists (m' : mem),
       ms' = MS (mkR (Z_to_bv 64 AAPP_REA_RET) (Z_to_bv 64 SQ) gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 0) (Z_to_bv 64 D1) (Z_to_bv 64 r) (Z_to_bv 64 AY_REALLOC_W) a4 a5 a6 a7
                    (Z_to_bv 64 (B + 8)) s3v s4v (Z_to_bv 64 (B + 4)) (Z_to_bv 64 r) (Z_to_bv 64 sh7) s8v s9v (Z_to_bv 64 sh10) s11v t3 t4 t5 t6)
                F1 (Z_to_bv 64 AY_REALLOC_W) fc1 None m' (seg_rom asegs)
       /\ munch [(SQ, SQ + 24)] m1 m' /\ wmono asegs m1 m' /\ mem_inv asegs m'
       /\ rw_cells asegs m' SQ [CB 8 (firstn 8 j24); C8 (Z_to_bv 64 ((B + 24) / 8 + 2147450880)); C8 (Z_to_bv 64 (B + 24))]).

Lemma asizeA_seg : forall (P : acc -> Prop) (rav gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v s5v s6v s7v s10v t3 t4 t5 t6 : word)
    (F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem)
    (B D1 S nz AF len1 used1 lo SQ sh9 sh11 : Z) (j24 : list byte) (shbB shbH : list byte) (HB HN : Z),
  mem_inv asegs m1 -> alloc_ceiling <= lo -> lo + 8192 <= SQ -> SQ + 128 <= 2^47 ->
  rw_cells asegs m1 B [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 len1); C4 (Z_to_bv 64 used1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 D1); C8 (Z_to_bv 64 AF)] ->
  u8arr asegs m1 (2147450880 + B / 8) shbB -> shbB = blk_shadow 32 ->
  rw_cells asegs m1 SQ [CB 24 j24] ->
  rw_cells asegs m1 AF [C8 (Z_to_bv 64 AY_MALLOC_W); C8 (Z_to_bv 64 AY_REALLOC_W); C8 (Z_to_bv 64 AY_FREE_W); C8 (Z_to_bv 64 0)] ->
  u8arr asegs m1 (2147450880 + HB / 8) shbH -> shbH = blk_shadow HN -> HB <= AF -> AF + 32 <= HB + 8 * (HN / 8) -> AF mod 8 = 0 ->
  0 < HB -> HB mod 16 = 0 -> HB + HN <= alloc_ceiling -> 17594333495296 <= HB -> (HB + HN <= B \/ B + 32 <= HB) ->
  0 < B -> B mod 16 = 0 -> B + 32 <= alloc_ceiling -> 17594333495296 <= B ->
  0 <= used1 < len1 -> len1 < 2^31 -> 0 < nz -> used1 + nz < 2^30 ->
  sh9 = 2147450880 + (B + 16) / 8 -> sh11 = 2147450880 + B / 8 ->
  pol P SQ (SQ + 24) -> pol P B (B + 32) -> pol P (2147450880 + B / 8) (2147450880 + B / 8 + 4) ->
  pol P AF (AF + 32) -> pol P (2147450880 + HB / 8) (2147450880 + HB / 8 + (HN + 7) / 8) ->
  evtA asegs P (asizeA_post rav gp tp (Z_to_bv 64 (B + 16)) (Z_to_bv 64 B) (Z_to_bv 64 nz) (Z_to_bv 64 S) (Z_to_bv 64 2147450880) (Z_to_bv 64 sh9) (Z_to_bv 64 sh11)
                            t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F1 fc1 m1 B D1 AF len1 used1 (ens_need_loop ENS_FUEL nz len1 used1) SQ
                            ((B + 4) / 8 + 2147450880) ((B + 8) / 8 + 2147450880) j24)
    (MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 (Z_to_bv 64 (B + 16)) (Z_to_bv 64 B) a0 a1 a2 a3 a4 a5 a6 a7
             s2v (Z_to_bv 64 nz) (Z_to_bv 64 S) s5v s6v s7v (Z_to_bv 64 2147450880) (Z_to_bv 64 sh9) s10v (Z_to_bv 64 sh11) t3 t4 t5 t6)
        F1 (Z_to_bv 64 AAPP_SIZE) fc1 None m1 (seg_rom asegs)).
Proof. aceil.
  intros until HN.
  intros MI CEIL' LOQ SQH BC BSH BSHeq FR YAF HBS HBSeq HB1 HB2 AF8 HB0 HB16 HBHI HBS2 SBH B0 B16 BHI BSH2 UB L31 NPOS N30 E9 E11.
  intros PSTK PB PBS PHB PHBS.
  unfold AAPP_SIZE, AY_MALLOC_W, AY_REALLOC_W, AY_FREE_W in *. unfold pol in PSTK, PB, PBS, PHB, PHBS.
  pose proof (blk_shadow_length 32 ltac:(lia)) as BSHlen. rewrite <- BSHeq in BSHlen.
  pose proof (blk_shadow_length HN ltac:(lia)) as HBSlen. rewrite <- HBSeq in HBSlen.
  assert (B8 : B mod 8 = 0) by lia.
  pose proof (ens_need_loop_bounds nz len1 used1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as NB. cbv zeta in NB.
  set (r := ens_need_loop ENS_FUEL nz len1 used1) in *.
  assert (R31 : r < 2^31) by (clear -CEILB NB N30 L31 UB; lia).
  pose proof (munch_refl [(SQ, SQ + 24)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
  yhide FR. yhide YAF. yhide HBS. yhide PSTK. yhide PHB. yhide PHBS. yhide SBH.
  zstepA.                                                                           (* [comment removed for export] *)
  shadow_fast BSH (B + 4) 4.                                                        (* [comment removed for export] *)
  zstepA.                                                                           (* [comment removed for export] *)
  zstepA. shadow_addr. zstepA.                                                      (* [comment removed for export] *)
  shadow_at BSH (B + 8) 4. shadow_ld.                                              (* [comment removed for export] *)
  zstepA. rewrite ysx32_small by lia.                                               (* [comment removed for export] *)
  zstepA. if_false.                                                                 (* [comment removed for export] *)
  zstepA. rewrite ysx32_small by lia.                                               (* [comment removed for export] *)
  stepA.                                                                            (* [comment removed for export] *)
  eapply evtA_cut.
  { eapply (asize_loop P ENS_FUEL len1); try lia. change (2 ^ Z.of_nat ENS_FUEL) with (2^64). clear -CEILB UB N30 L31 NPOS. nia. }
  cbv beta. intros ms1 (a2s & a3s & ->). fold r. unfold wz, AAPP_LOOPX.
  zstepA. if_cases K1; zify_cond K1. 1:{ kill K1. }                                 (* [comment removed for export] *)
  zstepA. if_cases K2; zify_cond K2. 1:{ kill K2. }                                 (* [comment removed for export] *)
  clear K1 K2.
  zstepA. if_cases K3; zify_cond K3.                                                (* [comment removed for export] *)
  { assert (RL : r = len1) by (revert K3; rewrite ?unsigned_lit by lia; lia). clear K3.
    apply evtA_done. left. split; [exact RL|]. rewrite <- RL. eexists _, _. unfold AAPP_COPY. reflexivity. }
  assert (RNE : r <> len1) by (revert K3; rewrite ?unsigned_lit by lia; lia). clear K3.
  yshow FR. yshow PSTK.
  apply (rw_cells_split_CB asegs _ _ [] 24 _ [] [8;8;8]%nat) in FR; [| reflexivity]. cbn [app mk_CB_cells] in FR.
  zstepA.                                                                           (* [comment removed for export] *)
  zstepA. shadow_addr. zstepA.                                                      (* [comment removed for export] *)
  zstepA.                                                                           (* [comment removed for export] *)
  shadow_at BSH (B + 24) 8. shadow_ld. zstepA. if_false.                          (* [comment removed for export] *)
  zstepA.                                                                           (* [comment removed for export] *)
  yshow YAF. yshow HBS. yshow PHB. yshow PHBS. yshow SBH.
  eapply (rw_cells_transport asegs) in YAF; [| exact MU| exact WM| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  eapply (u8arr_transport asegs) in HBS; [| exact MU| exact WM| cbv [disjoint_from fst snd]; lia].
  yhide SBH. yhide FR. yhide PSTK.
  zstepA.                                                                           (* [comment removed for export] *)
  zstepA. shadow_fast HBS (AF + 8) 8.                                               (* [comment removed for export] *)
  zstepA. shadow_fast HBS (AF + 24) 8.                                              (* [comment removed for export] *)
  shadow_at BSH (B + 16) 8. shadow_ld. zstepA. if_false.                          (* [comment removed for export] *)
  zstepA. zstepA. zstepA. stepA.                                                    (* [comment removed for export] *)
  stepA.                                                                            (* [comment removed for export] *)
  yshow FR.
  apply evtA_done. right. split; [exact RNE|]. unfold AAPP_REA_RET. eexists _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  eapply rw_cells_recast; [exact FR| | reflexivity| reflexivity].
  pose proof (proj1 (proj1 FR)) as WF. exact WF.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma asizeB_seg : forall (P : acc -> Prop) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3v s4v t3 t4 t5 t6 : word)
    (F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem)
    (B D1 D2 AF len1 used1 r SQ sh7 sh9 sh10 sh11 : Z) (shbB : list byte),
  mem_inv asegs m1 ->
  rw_cells asegs m1 B [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 len1); C4 (Z_to_bv 64 used1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 D1); C8 (Z_to_bv 64 AF)] ->
  u8arr asegs m1 (2147450880 + B / 8) shbB -> shbB = blk_shadow 32 ->
  0 < B -> B mod 16 = 0 -> B + 32 <= alloc_ceiling -> 17594333495296 <= B ->
  0 < D2 < 2^64 -> 0 <= r < 2^31 ->
  sh7 = 2147450880 + (B + 4) / 8 -> sh9 = 2147450880 + (B + 16) / 8 -> sh10 = 2147450880 + (B + 8) / 8 -> sh11 = 2147450880 + B / 8 ->
  pol P B (B + 32) -> pol P (2147450880 + B / 8) (2147450880 + B / 8 + 4) ->
  evtA asegs P (fun ms' => exists (a0' a1' : word) (m' : mem),
      ms' = MS (mkR (Z_to_bv 64 AAPP_REA_RET) (Z_to_bv 64 SQ) gp tp t0 t1 t2 (Z_to_bv 64 (B + 16)) (Z_to_bv 64 B) a0' a1' a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 (B + 8)) s3v s4v (Z_to_bv 64 (B + 4)) (Z_to_bv 64 r) (Z_to_bv 64 sh7) (Z_to_bv 64 2147450880) (Z_to_bv 64 sh9) (Z_to_bv 64 sh10) (Z_to_bv 64 sh11) t3 t4 t5 t6)
               F1 (Z_to_bv 64 AAPP_COPY) fc1 None m' (seg_rom asegs)
      /\ munch [(B, B + 32)] m1 m' /\ wmono asegs m1 m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' B [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 r); C4 (Z_to_bv 64 used1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 D2); C8 (Z_to_bv 64 AF)])
    (MS (mkR (Z_to_bv 64 AAPP_REA_RET) (Z_to_bv 64 SQ) gp tp t0 t1 t2 (Z_to_bv 64 (B + 16)) (Z_to_bv 64 B) (Z_to_bv 64 D2) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (B + 8)) s3v s4v (Z_to_bv 64 (B + 4)) (Z_to_bv 64 r) (Z_to_bv 64 sh7) (Z_to_bv 64 2147450880) (Z_to_bv 64 sh9) (Z_to_bv 64 sh10) (Z_to_bv 64 sh11) t3 t4 t5 t6)
        F1 (Z_to_bv 64 AAPP_REA_RET) fc1 None m1 (seg_rom asegs)).
Proof. aceil.
  intros until shbB. intros MI BC BSH BSHeq B0 B16 BHI BSH2 D2R RR E7 E9 E10 E11 PB PBS.
  unfold AAPP_REA_RET, AAPP_COPY in *. unfold pol in PB, PBS.
  pose proof (blk_shadow_length 32 ltac:(lia)) as BSHlen. rewrite <- BSHeq in BSHlen.
  assert (B8 : B mod 8 = 0) by lia.
  pose proof (munch_refl [(B, B + 32)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
  shadow_at BSH (B + 16) 8. shadow_ld. zstepA. if_false.                          (* [comment removed for export] *)
  zstepA.                                                                           (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1. { kill K1. }                                   (* [comment removed for export] *)
  shadow_at BSH (B + 4) 4. shadow_ld. zstepA. if_false.                           (* [comment removed for export] *)
  zstepA.                                                                           (* [comment removed for export] *)
  finishA.
Qed.

(* [comment removed for export] *)
End RC__2.
