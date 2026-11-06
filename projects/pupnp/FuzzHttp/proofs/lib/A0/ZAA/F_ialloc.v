(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ATacA ACells F_imemset.
Import ListNotations.
Open Scope Z_scope.

Definition ialloc_entry := 0x63eb0%Z.
Notation IA_FLAG := 1323912%Z.
Notation IA_BASE := 740096%Z.
Notation IA_MAP1 := 740104%Z.
Notation IA_R3 := 1002304%Z.
Notation IA_R4 := 1005760%Z.
Notation IA_R1 := 1268488%Z.

Definition b8 (z : Z) : byte := Z_to_bv 8 z.
Definition zeros (n : nat) : list byte := repeat (Z_to_bv 8 0) n.

Ltac fold_cb_load :=
  match goal with
  | |- context [sext 64 (bv_extract ?o ?w (le_bytes_to_word ?l))] =>
      let v := eval vm_compute in (bv_unsigned (sext 64 (bv_extract o w (le_bytes_to_word l)))) in
      replace (sext 64 (bv_extract o w (le_bytes_to_word l))) with (Z_to_bv 64 v) by (vm_compute; reflexivity)
  | |- context [zext 64 (bv_extract ?o ?w (le_bytes_to_word ?l))] =>
      let v := eval vm_compute in (bv_unsigned (zext 64 (bv_extract o w (le_bytes_to_word l)))) in
      replace (zext 64 (bv_extract o w (le_bytes_to_word l))) with (Z_to_bv 64 v) by (vm_compute; reflexivity)
  | |- context [bv_extract ?o ?w (le_bytes_to_word ?l)] =>
      let v := eval vm_compute in (bv_unsigned (bv_extract o w (le_bytes_to_word l))) in
      replace (bv_extract o w (le_bytes_to_word l)) with (Z_to_bv w v) by (vm_compute; reflexivity)
  end.

Ltac bytes_eq :=
  cbn; repeat first [ reflexivity | apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|] ].

Section IA.
  Context {HC : HasCeiling}.

  Variables NM2 NM4 : Z.
  Hypothesis HNM2 : NM2 = 262144.
  Hypothesis HNM4 : NM4 = 262728.

  Definition ia_flag (inited : bool) : list cell := [CB 4 [b8 (if inited then 1 else 0); b8 0; b8 0; b8 0]].

  Definition ia_cells (inited : bool) (m : mem) : Prop :=
    rw_cells asegs m IA_FLAG (ia_flag inited)
    /\ (exists j0, rw_cells asegs m IA_BASE [CB 8 j0])
    /\ (exists j2, rw_cells asegs m IA_MAP1 [CB (Z.to_nat NM2) j2] /\ (inited = true -> j2 = zeros (Z.to_nat NM2)))
    /\ (exists j3, rw_cells asegs m IA_R3 [CB 3456 j3])
    /\ (exists j4, rw_cells asegs m IA_R4 [CB (Z.to_nat NM4) j4])
    /\ (exists j1, rw_cells asegs m IA_R1 [CB 40 j1]).

  Notation WIA q := [(q - 48, q); (IA_FLAG, IA_FLAG + 4); (IA_BASE, IA_BASE + 8 + NM2); (IA_R3, IA_R1 + 40)].

  Variables (ra gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q : Z) (m0 : mem).

  Definition ialloc_post (lo : Z) : machine_state -> Prop :=
    fun ms' => exists a1 a2 a3 a4 a5 a6 m',
      ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz IA_BASE) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch (WIA q) m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
      /\ ia_cells true m' /\ rw_cells asegs m' GOT_PAGE [C8 (wz PAGE_CELL)] /\ rw_cells asegs m' PAGE_CELL [C8 (wz 4096)]
      /\ stk asegs m' lo q.

  #[using="Type"] Lemma imemset_spec_z : forall (sp xa3 xa4 xa5 xa6 xs0 xs1 xs2 xs3 : word) (m : mem) (D c n : Z) (junk : list byte) xt0 xt1 xt2 xra,
    mem_inv asegs m -> 0 <= c < 256 -> 0 <= n < 2^63 -> 0 <= D -> D + n < 2^64 ->
    rw_cells asegs m D [CB (Z.to_nat n) junk] ->
    evt asegs (fun ms' => exists a1' a2' a3' m',
        ms' = MS (mkR xra sp gp tp xt0 xt1 xt2 xs0 xs1 (wz D) a1' a2' a3' xa4 xa5 xa6 a7 xs2 xs3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F_ (ret_pc xra) fc None m' (seg_rom asegs)
        /\ munch [(D, D + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' D [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))])
      (MS (mkR xra sp gp tp xt0 xt1 xt2 xs0 xs1 (wz D) (wz c) (wz n) xa3 xa4 xa5 xa6 a7 xs2 xs3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz imemset_entry) fc None m (seg_rom asegs)).
  Proof.
    intros. pose proof (imemset_spec xra sp gp tp xt0 xt1 xt2 xs0 xs1 (wz D) (wz c) (wz n) xa3 xa4 xa5 xa6 a7 xs2 xs3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m c n junk) as P.
    rewrite !unsigned_lit in P by lia.
    eapply evt_mono; [apply P; try assumption; try reflexivity; lia|].
    intros ms' Q. unfold imemset_post in Q. rewrite !unsigned_lit in Q by lia. exact Q.
  Qed.

  #[using="HNM2 HNM4"] Lemma ialloc_spec : forall lo (inited : bool) a0 a1 a2 a3 a4 a5 a6,
    stk asegs m0 lo q -> alloc_ceiling <= lo -> lo <= q - 48 -> q mod 16 = 0 -> q <= 2^47 ->
    ia_cells inited m0 -> rw_cells asegs m0 GOT_PAGE [C8 (wz PAGE_CELL)] -> rw_cells asegs m0 PAGE_CELL [C8 (wz 4096)] ->
    mem_inv asegs m0 ->
    evt asegs (ialloc_post lo)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz ialloc_entry) fc None m0 (seg_rom asegs)).
  Proof.
    intros lo inited a0 a1 a2 a3 a4 a5 a6 ST CLO LO AL QH IA GP PG MI. unfold ialloc_entry.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (munch_refl (WIA q) m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    destruct IA as (FL & [j0 C0] & [j2 [C2 Z2]] & [j3 C3] & [j4 C4'] & [j1 C1']). unfold ia_flag in FL.
    assert (E : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    rewrite <- E in ST. carve_frame 48%nat ST. rewrite !E in *.
    do 6 sstep.
    zstep. zstep.
    unfold b8 in *. destruct inited.
    -
      zstep.   fold_cb_load.
      zstep.
      zstep. if_cases K0; zify_cond K0. 2:{ exfalso. revert K0. clear. intros K0. rewrite ?unsigned_lit in K0 by lia. lia. }
      zstep. zstep.
      do 5 zstep. zstep. replace (q + -48 + 48) with q by lia. zstep.
      release_frame FR ST q.
      apply evt_done. unfold ialloc_post. eexists _, _, _, _, _, _, _. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
      split. { unfold ia_cells, ia_flag, b8. split; [exact FL|]. split; [eauto|]. split; [eauto|]. split; [eauto|]. split; eauto. }
      split; [exact GP|]. split; [exact PG| exact ST].
    -
      zstep.   fold_cb_load.
      zstep.
      zstep. if_cases K0; zify_cond K0. { exfalso. revert K0. clear. intros K0. rewrite ?unsigned_lit in K0 by lia. lia. }
      do 6 zstep.
      zstep.   change (bv_swrap 32 65280) with 65280.
      zstep.
      amo_step.
      do 4 zstep.
      amo_step.
      zstep. if_cases K1; zify_cond K1. { exfalso. revert K1. clear. intros K1. rewrite ?unsigned_lit in K1 by lia. lia. }
      zstep. zstep.
      zstep. if_cases K2; zify_cond K2. { exfalso. revert K2. clear. intros K2. cbn in K2. lia. }
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        apply (rw_cells_rebytes mm IA_FLAG _ [CB 4 [b8 0; b8 1; b8 0; b8 0]]) in FL; [| cbn; tauto| bytes_eq| reflexivity] end.
      unfold b8 in FL.
      zstep.   try fold_cb_load.
      Show.
      zstep. if_cases K3; zify_cond K3. { exfalso. revert K3. clear. intros K3. rewrite ?unsigned_lit in K3 by lia. lia. }

      do 7 zstep.
      zstep.
      call (imemset_spec_z (wz (q + -48)) _ _ _ _ _ _ _ _ _ IA_R1 0 40 j1).
      all: side (try (first [eassumption | lia])).

      sstep.
      do 4 zstep. rewrite <- HNM2.
      zstep.
      call (imemset_spec_z (wz (q + -48)) _ _ _ _ _ _ _ _ _ IA_MAP1 0 NM2 j2).
      all: side (try (first [eassumption | lia])).
      rewrite HNM2.

      do 5 zstep. change (Z.shiftl 27 7) with 3456.
      zstep.
      call (imemset_spec_z (wz (q + -48)) _ _ _ _ _ _ _ _ _ IA_R3 0 3456 j3).
      all: side (try (first [eassumption | lia])).

      do 5 zstep. try match goal with |- context [Z_to_bv 64 (bv_swrap 32 ?x)] => let v := eval vm_compute in (bv_swrap 32 x) in change (bv_swrap 32 x) with v end.
      rewrite <- HNM4.
      zstep.
      call (imemset_spec_z (wz (q + -48)) _ _ _ _ _ _ _ _ _ IA_R4 0 NM4 j4).
      all: side (try (first [eassumption | lia])).

      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        match goal with H : rw_cells asegs mm IA_R4 _ |- _ =>
          apply (rw_cells_split_CB asegs mm IA_R4 [] (Z.to_nat NM4) _ [] [8%nat; 8%nat; Z.to_nat (NM4 - 16)]) in H;
          [cbn [mk_CB_cells app] in H| cbn [sum_nat]; lia] end end.
      zstep. zstep. zstep.
      zstep. if_cases K4; zify_cond K4. 2:{ exfalso. revert K4. clear. intros K4. rewrite ?unsigned_lit in K4 by lia. lia. }
      do 4 zstep.
      try match goal with |- context [Z_to_bv 64 (bv_swrap 32 ?x)] => let v := eval vm_compute in (bv_swrap 32 x) in change (bv_swrap 32 x) with v end.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        match goal with H : rw_cells asegs mm IA_R4 _ |- _ =>
          split_chunk H 2%nat R4H R4T; match type of R4T with ?P => change P with (id P) in R4T end end;
        pose proof (munch_refl [(IA_R4, IA_R4 + 16); (IA_FLAG, IA_FLAG + 2)] mm) as MUr; pose proof (wmono_refl asegs mm) as WMr end.
      sstep.
      sstep.
      zstep.
      sstep.
      zstep.
      sstep.
      zstep. zstep.
      do 5 zstep. zstep. replace (q + -48 + 48) with q by lia. zstep.
      release_frame FR ST q.

      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
        apply (rw_cells_rebytes mf IA_FLAG _ [CB 4 [b8 1; b8 0; b8 0; b8 0]]) in FL; [| cbn; tauto| bytes_eq| reflexivity] end.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
        match type of C0 with rw_cells _ _ _ ?cs =>
          apply (rw_cells_merge asegs mf IA_BASE [] cs []) in C0; cbn [cells_size csize cells_bytes cbytes app Nat.add] in C0 end end.
      unfold id in R4T.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
        pose proof (rw_cells_transport asegs _ _ mf _ _ R4T MUr WMr ltac:(cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia)) as R4T' end.
      clear R4T. join_chunks R4H R4T' R4.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
        match type of R4 with rw_cells _ _ _ ?cs =>
          apply (rw_cells_merge asegs mf IA_R4 [] cs []) in R4; cbn [cells_size csize cells_bytes cbytes app] in R4 end end.
      match type of R4 with rw_cells _ _ _ [CB ?k ?l] => replace k with (Z.to_nat NM4) in R4 by lia end.
      apply evt_done. unfold ialloc_post. eexists _, _, _, _, _, _, _. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|].
      split. { unfold ia_cells, ia_flag. split; [exact FL|]. split; [eexists; eassumption|].
               split. { eexists. split; [eassumption| reflexivity]. }
               split; [eexists; eassumption|]. split; [eexists; exact R4| eexists; eassumption]. }
      split; [assumption|]. split; [assumption| assumption].
  Qed.
End IA.
