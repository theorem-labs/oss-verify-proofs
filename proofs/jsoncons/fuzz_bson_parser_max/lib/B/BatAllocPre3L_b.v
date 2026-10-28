(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatRzLog_b BatAllocA_b BatAllocSecA_b BatPoison_b BatAllocG_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Ltac inl := cbn [In]; repeat first [left; reflexivity | right].

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Theorem art_allocate_pre3a_sec : forall regs (M0 rom : word -> option byte) (raw : word) (sp ia n stk tp key tsd ctx t rl rs qr rz qz : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 10 = Z_to_bv 64 ia ->
  getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 8 -> getr regs 13 = Z_to_bv 64 stk -> getr regs 14 = Z_to_bv 64 1 -> getr regs 15 = Z_to_bv 64 1 ->
  (* [comment removed for export] *)
  1 <= n < 2 ^ 39 -> rl = AsanTab.rz_log n -> rz = 16 * 2 ^ rl -> rz = 16 * qz -> 1 <= qz <= 128 ->
  rs = (Z.max n 8 + 7) / 8 * 8 -> rs = 8 * qr -> Z.max n 8 <= rs <= Z.max n 8 + 7 -> 65536 < rs + rz ->
  (* [comment removed for export] *)
  0x10007fff8000 + 4096 <= sp -> sp + 2144 <= 2 ^ 47 -> sp <= stk -> stk + 16 <= sp + 4096 ->
  0x10000 <= ia -> ia + 4096 <= 0x696000 ->
  4096 <= t -> t + 4096 < 2 ^ 47 -> (t + 4096 <= 0x10000 \/ 0x696000 <= t) -> apart t 4096 (sp - 1952) 6048 ->
  apart ctx 4096 (sp - 1952) 6048 -> (ctx + 4096 <= 0x10000 \/ 0x696000 <= ctx) -> apart t 4096 ctx 4096 ->
  0x10100 <= tp -> tp + 8 <= 0x696000 -> 0x10000 <= tsd -> tsd + 1024 <= 0x696000 ->
  (* [comment removed for export] *)
  wrA M0 (sp - 1952) 1952 ->
  art_alloc_rodata M0 -> art_rz_rodata M0 -> art_tsd M0 tp key tsd ctx t ->
  cellA M0 0x140918 1 1 -> cellA M0 0x1c1ea2 1 0 -> cellA M0 (ia + 3616) 8 (2 ^ 40) -> cellA M0 (ia + 3624) 2 16 -> cellA M0 (ia + 3626) 2 2048 ->
  exists r5 (M5 : word -> option byte),
    msteps ASEGS (mkst regs (0x525e4 : word) M0 rom) (mkst r5 (0x56d3c : word) M5 rom)
    /\ getr r5 1 = (0x52884 : bv 64)%bv /\ getr r5 2 = Z_to_bv 64 (sp - 128) /\ getr r5 4 = Z_to_bv 64 tp /\ getr r5 8 = Z_to_bv 64 0 /\ getr r5 9 = Z_to_bv 64 n
    /\ getr r5 10 = Z_to_bv 64 ia /\ getr r5 11 = Z_to_bv 64 (t + 208) /\ getr r5 12 = Z_to_bv 64 (rs + rz + rz) /\ getr r5 13 = Z_to_bv 64 8
    /\ getr r5 19 = Z_to_bv 64 (rs + rz + rz) /\ getr r5 20 = Z_to_bv 64 rz /\ getr r5 21 = Z_to_bv 64 n /\ getr r5 22 = Z_to_bv 64 ia /\ getr r5 23 = Z_to_bv 64 stk
    /\ getr r5 25 = Z_to_bv 64 7 /\ getr r5 26 = Z_to_bv 64 t /\ getr r5 27 = Z_to_bv 64 1 /\ getr r5 3 = getr regs 3
    /\ mem_grows M0 M5
    /\ (forall x : word, ~ (sp - 144 <= U x < sp) -> M5 x = M0 x)
    /\ cellA M5 (sp - 128 + 120) 8 (U raw) /\ cellA M5 (sp - 128 + 112) 8 (U (getr regs 8)) /\ cellA M5 (sp - 128 + 104) 8 (U (getr regs 9))
    /\ cellA M5 (sp - 128 + 96) 8 (U (getr regs 18)) /\ cellA M5 (sp - 128 + 88) 8 (U (getr regs 19)) /\ cellA M5 (sp - 128 + 80) 8 (U (getr regs 20))
    /\ cellA M5 (sp - 128 + 72) 8 (U (getr regs 21)) /\ cellA M5 (sp - 128 + 64) 8 (U (getr regs 22)) /\ cellA M5 (sp - 128 + 56) 8 (U (getr regs 23))
    /\ cellA M5 (sp - 128 + 48) 8 (U (getr regs 24)) /\ cellA M5 (sp - 128 + 40) 8 (U (getr regs 25)) /\ cellA M5 (sp - 128 + 32) 8 (U (getr regs 26))
    /\ cellA M5 (sp - 128 + 24) 8 (U (getr regs 27)) /\ cellA M5 (sp - 128 + 8) 8 1 /\ cellA M5 (sp - 128 + 16) 8 16.
Proof.
  intros regs M0 rom raw sp ia n stk tp key tsd ctx t rl rs qr rz qz.
  intros H1 H2 H4 H10 H11 H12 H13 H14 H15.
  intros Hn Er Erz Erz16 Hqz Ers Ers8 Hrs Hprim.
  intros Hsp Hsp' Hstk Hstk' Hia Hia' Ht Ht' Timg Atsp Actx Cimg Atctx Htp0 Htp1 Htsd0 Htsd.
  intros W RO RZRO TSD Ci Cr Cmax Cmin16 Cmax2048.
  pose proof TSD as (Ttsd1 & Ttsd2 & Ttsd3 & Ttsd4 & Ttsd5 & TR).
  pose proof (AsanTab.rz_log_range n) as Hr. rewrite <- Er in Hr.
  change (hid (t + 4096 <= 0x10000 \/ 0x696000 <= t)) in Timg. change (hid (ctx + 4096 <= 0x10000 \/ 0x696000 <= ctx)) in Cimg.
  (* [comment removed for export] *)
  pose proof (art_alloc_a1_fn regs M0 rom raw sp ia n stk H1 H2 H10 H11 H12 H13 H14 H15 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(eapply wr_sub; [exact W|lia|lia]) ltac:(lia) RO Ci Cr) as RUN1.
  set (M1 := art_alloc_memA1 M0 sp raw regs) in RUN1.
  lazymatch type of RUN1 with msteps _ _ (mkst ?R _ _ _) => set (R1 := R) in RUN1 end.
  assert (AG1 : forall a k v, 0 <= a -> a + Z.of_nat k <= sp - 128 \/ sp <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA M0 a k v -> cellA M1 a k v).
  { intros a k v Ha Hak Hak' C. unfold M1, art_alloc_memA1. zcell. }
  assert (W1 : wrA M1 (sp - 1952) 1952) by (unfold M1, art_alloc_memA1; zwr).
  (* [comment removed for export] *)
  destruct (art_alloc_ladder R1 M1 rom n ltac:(unfold R1; gres; reflexivity) ltac:(unfold R1; gres; reflexivity) ltac:(lia)) as (r2 & RUN2 & P2_19 & K2).
  assert (KK2 : forall r v, r <> 10%bv -> r <> 19%bv -> getr R1 r = v -> getr r2 r = v). { intros r v N1 N2 E. rewrite K2 by assumption. exact E. }
  (* [comment removed for export] *)
  pose proof (art_alloc_a2_fn r2 M1 rom (sp - 128) ia
                (KK2 2%bv _ ltac:(discriminate) ltac:(discriminate) ltac:(unfold R1; gres; f_equal; lia))
                (KK2 26%bv _ ltac:(discriminate) ltac:(discriminate) ltac:(unfold R1; gres; reflexivity))
                ltac:(lia) ltac:(lia) ltac:(lia) Hia' ltac:(eapply wr_sub; [exact W1|lia|lia]) ltac:(lia)
                ltac:(destruct RZRO as (X1 & X2 & X3); repeat split; apply AG1; try assumption; cbn; lia)
                ltac:(apply AG1; first [exact Cmin16 | ond | oside]; cbn; lia) ltac:(apply AG1; first [exact Cmax2048 | ond | oside]; cbn; lia)) as RUN3.
  lazymatch type of RUN3 with msteps _ _ (mkst ?R _ ?MM _) => set (R3 := R) in RUN3; set (M3 := MM) in RUN3 end.
  assert (AG3 : forall a k v, 0 <= a -> a + Z.of_nat k <= sp - 128 - 16 \/ sp <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA M0 a k v -> cellA M3 a k v).
  { intros a k v Ha Hak Hak' C. unfold M3. do 2 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]). apply AG1; assumption || lia. }
  assert (W3 : wrA M3 (sp - 1952) 1952) by (unfold M3; zwr).
  (* [comment removed for export] *)
  destruct (art_alloc_clamp R3 M3 rom n rl ltac:(unfold R3; gres; reflexivity) ltac:(unfold R3; gres; reflexivity)
              ltac:(unfold R3; gres; rewrite P2_19; f_equal; symmetry; exact Er)
              ltac:(unfold R3; gres; apply (KK2 21%bv); [discriminate|discriminate|unfold R1; gres; reflexivity]) ltac:(lia)
              Er) as (r4 & RUN4 & P4_10 & P4_11 & P4_19 & K4).
  assert (KK4 : forall r v, r <> 10%bv -> r <> 11%bv -> r <> 19%bv -> getr R3 r = v -> getr r4 r = v). { intros r v N1 N2 N3 E. rewrite K4 by assumption. exact E. }
  (* [comment removed for export] *)
  assert (Q2 : getr r4 2 = Z_to_bv 64 (sp - 128)). { apply KK4; [discriminate|discriminate|discriminate|]. unfold R3; gres. f_equal; lia. }
  assert (Q4 : getr r4 4 = Z_to_bv 64 tp). { apply KK4; [discriminate|discriminate|discriminate|]. unfold R3; gres. apply (KK2 4%bv); [discriminate|discriminate|]. unfold R1; gres. exact H4. }
  assert (Q8 : getr r4 8 = Z_to_bv 64 8). { apply KK4; [discriminate|discriminate|discriminate|]. unfold R3; gres. apply (KK2 8%bv); [discriminate|discriminate|]. unfold R1; gres. reflexivity. }
  assert (Q18 : getr r4 18 = Z_to_bv 64 8). { apply KK4; [discriminate|discriminate|discriminate|]. unfold R3; gres. apply (KK2 18%bv); [discriminate|discriminate|]. unfold R1; gres. reflexivity. }
  assert (Q20 : getr r4 20 = Z_to_bv 64 65536). { apply KK4; [discriminate|discriminate|discriminate|]. unfold R3; gres. reflexivity. }
  assert (Q21 : getr r4 21 = Z_to_bv 64 n). { apply KK4; [discriminate|discriminate|discriminate|]. unfold R3; gres. apply (KK2 21%bv); [discriminate|discriminate|]. unfold R1; gres. reflexivity. }
  assert (Q22 : getr r4 22 = Z_to_bv 64 ia). { apply KK4; [discriminate|discriminate|discriminate|]. unfold R3; gres. apply (KK2 22%bv); [discriminate|discriminate|]. unfold R1; gres. reflexivity. }
  assert (Q26 : getr r4 26 = Z_to_bv 64 (ia + 2047)). { apply KK4; [discriminate|discriminate|discriminate|]. unfold R3; gres. apply (KK2 26%bv); [discriminate|discriminate|]. unfold R1; gres. reflexivity. }
  assert (Q23 : getr r4 23 = Z_to_bv 64 stk). { apply KK4; [discriminate|discriminate|discriminate|]. unfold R3; gres. apply (KK2 23%bv); [discriminate|discriminate|]. unfold R1; gres. reflexivity. }
  assert (Q25 : getr r4 25 = Z_to_bv 64 7). { apply KK4; [discriminate|discriminate|discriminate|]. unfold R3; gres. apply (KK2 25%bv); [discriminate|discriminate|]. unfold R1; gres. reflexivity. }
  assert (Q27 : getr r4 27 = Z_to_bv 64 1). { apply KK4; [discriminate|discriminate|discriminate|]. unfold R3; gres. apply (KK2 27%bv); [discriminate|discriminate|]. unfold R1; gres. reflexivity. }
  assert (Q24 : getr r4 24 = Z_to_bv 64 65535). { apply KK4; [discriminate|discriminate|discriminate|]. unfold R3; gres. reflexivity. }
  (* [comment removed for export] *)
  assert (TSD3 : art_tsd M3 tp key tsd ctx t). { unfold art_tsd. repeat split; try lia; (apply AG3; first [assumption | ond | oside]). }
  pose proof (art_alloc_a3_sec_fn r4 M3 rom (sp - 128) ia n rl rs rz tp key tsd ctx t Q2 Q4 Q8 ltac:(rewrite P4_10; f_equal; lia) Q18 P4_19 Q20 Q21 Q22 Q26
                ltac:(lia) ltac:(lia) ltac:(lia) Hia' ltac:(lia) ltac:(lia) ltac:(lia) Ers Erz ltac:(lia)
                ltac:(eapply wr_sub; [exact W3|lia|lia]) ltac:(apply AG3; first [exact Cmax | ond | oside]; cbn; lia) TSD3 ltac:(lia)
                ltac:(unfold apart; lia) ltac:(unfold apart; lia) ltac:(unfold apart in Actx |- *; lia)) as RUN5.
  lazymatch type of RUN5 with msteps _ _ (mkst ?R _ ?MM _) => set (R5 := R) in RUN5; set (M5 := MM) in RUN5 end.
  assert (AG5 : forall a k v, 0 <= a -> a + Z.of_nat k <= sp - 128 - 16 \/ sp <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA M0 a k v -> cellA M5 a k v).
  { intros a k v Ha Hak Hak' C. unfold M5. apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]. apply AG3; assumption || lia. }
  assert (W5 : wrA M5 (sp - 1952) 1952) by (unfold M5; zwr).
  assert (G5 : mem_grows M0 M5).
  { unfold M5, M3, M1, art_alloc_memA1. repeat (eapply mem_grows_trans; [|apply Wn_grows]). apply mem_grows_refl. }
  (* [comment removed for export] *)
  assert (AGt5 : forall a k v, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> (a + Z.of_nat k <= sp - 1952 \/ sp <= a) -> cellA M0 a k v -> cellA M5 a k v).
  { intros a k v Ha Hak O C. apply AG5; try assumption. lia. }
  assert (A05 : forall x : word, ~ (sp - 144 <= U x < sp) -> M5 x = M0 x).
  { intros x N1. unfold M5, M3, M1, art_alloc_memA1. zagree. }
  (* [comment removed for export] *)
  assert (Q3 : getr r4 3 = getr regs 3). { apply KK4; [discriminate|discriminate|discriminate|]. unfold R3; gres. apply (KK2 3%bv); [discriminate|discriminate|]. unfold R1; gres. reflexivity. }
  assert (AF5 : forall a k v, sp - 128 <= a -> a + Z.of_nat k <= sp -> cellA M1 a k v -> cellA M5 a k v).
  { intros a k v Ha Hak C. unfold M5, M3. do 3 (apply cell_Wn_other; [lia|lia|lia|lia|unfold apart; lia|]). exact C. }
  exists R5, M5.
  split. { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|]. exact RUN5. }
  split; [unfold R5; gres; reflexivity|]. split; [unfold R5; gres; reflexivity|]. split; [unfold R5; gres; exact Q4|]. split; [unfold R5; gres; reflexivity|].
  split; [unfold R5; gres; reflexivity|]. split; [unfold R5; gres; reflexivity|]. split; [unfold R5; gres; reflexivity|]. split; [unfold R5; gres; reflexivity|].
  split; [unfold R5; gres; reflexivity|]. split; [unfold R5; gres; reflexivity|]. split; [unfold R5; gres; reflexivity|]. split; [unfold R5; gres; exact Q21|].
  split; [unfold R5; gres; exact Q22|]. split; [unfold R5; gres; exact Q23|]. split; [unfold R5; gres; exact Q25|]. split; [unfold R5; gres; reflexivity|].
  split; [unfold R5; gres; exact Q27|].
  split; [unfold R5; gres; exact Q3|].
  split; [exact G5|]. split; [exact A05|].
  zsplit; (apply AF5; [lia|cbn; lia|unfold M1, art_alloc_memA1; zcell]).
Qed.
End FPX.
