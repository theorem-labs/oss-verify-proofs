(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge TacX SFModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import InNth.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsWalk.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N8Store.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma sx32_lit x : 0 <= x < 2^31 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. exact (sx32_wz x). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ACONST_n5 : forall m, ACONST m ->
     rw_cells asegs m AGOT_FSTLS [C8 (wz 1); C8 (wz 0xfffffffffffff800)]
  /\ rw_cells asegs m AREAL_TLSGA_CELL [C8 (wz AREAL_TLSGA)]
  /\ rw_cells asegs m AINITED_CELL [C1 (b8 1); C1 (b8 1)]
  /\ rw_cells asegs m ATSD_CELL [C1 (b8 1)]
  /\ rw_cells asegs m (ATSD_CELL + 4) [C4 (wz 0)]
  /\ rw_cells asegs m AMUSL_TSD [C8 (wz 0xc03038)]
  /\ rw_cells asegs m AMUSL_DTV [C8 (wz 0xbe1cc0)]
  /\ rw_cells asegs m AMUSL_DTV1 [C8 (wz 0xbe2490)]
  /\ rw_cells asegs m AGOT_CFLAGS [C8 (wz 0x73c428)]
  /\ rw_cells asegs m ACF_ITLS_CELL [C1 (b8 1)]
  /\ rw_cells asegs m AGOT_VERBOSITY [C8 (wz AVERBOSITY_CELL)]
  /\ rw_cells asegs m AVERBOSITY_CELL [C4 (wz 0)]
  /\ rw_cells asegs m AGOT_DTLS [C8 (wz 0x18)].
Proof. intros m AC. repeat split; (eapply ACONST_cell; [exact AC| in_nth]). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tryinit_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a1 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' (bv_unsigned sp - 16) (bv_unsigned sp).
Lemma tryinit_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  mem_inv asegs m -> rw_cells asegs m AINITED_CELL [C1 (b8 1); C1 (b8 1)] ->
  stk asegs m (bv_unsigned sp - 16) (bv_unsigned sp) -> aceil <= bv_unsigned sp - 16 ->
  evt asegs (tryinit_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1c69a8) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI C5 ST0 LO. unfold AINITED_CELL, b8 in C5. acb.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof ST0 as ST. carve_frame 16%nat ST.
  do 8 zstep.
  zstep. if_cases K; [exfalso|].
  { revert K. vm_compute. discriminate. }
  do 4 zstep.
  release_frame FR ST (bv_unsigned sp).
  unfold tryinit_post. finish.
Qed.

End HCW.


(* [comment removed for export] *)
Ltac head_of t := lazymatch t with ?f _ => head_of f | _ => t end.
Ltac call_pure SPEC :=
  eapply evt_cut; [ eapply SPEC | ];
  [ .. | let ms' := fresh "ms'" in let PO := fresh "POST" in
         intros ms' PO;
         (let T := type of PO in let h := head_of T in try unfold h in PO);
         destruct_exs PO; subst ms';
         try (lazymatch goal with
              | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
                  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
              end) ].

(* [comment removed for export] *)
Ltac call2 SPEC :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
      eapply evt_cut; [ eapply SPEC | let ms' := fresh "ms'" in let PO := fresh "POST" in
                                       intros ms' PO;
                                       (let T := type of PO in let h := head_of T in try unfold h in PO);
                                       zsimp_in PO; revert ms' PO; post_call segs m ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HCW2.
  Context {HCEIL : HeapCeil}.

Definition musl_tlsga_post (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a1 a2,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ATP) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom asegs).
Lemma musl_tlsga_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  mem_inv asegs m -> a0 = Z_to_bv 64 AGOT_FSTLS -> tp = Z_to_bv 64 ATP ->
  rw_cells asegs m AGOT_FSTLS [C8 (wz 1); C8 (wz 0xfffffffffffff800)] ->
  rw_cells asegs m AMUSL_DTV [C8 (wz 0xbe1cc0)] ->
  rw_cells asegs m AMUSL_DTV1 [C8 (wz 0xbe2490)] ->
  evt asegs (musl_tlsga_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x56aac8) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI Ha0 Htp G D0 D1. subst a0 tp.
  unfold AGOT_FSTLS, AMUSL_DTV, AMUSL_DTV1, ATP, wz in *.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  zstep. unfold musl_tlsga_post. finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gct_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (T : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a1 t1' m',   (* [comment removed for export] *)
    ms' = MS (mkR ra sp gp tp t0 t1' t2 s0 s1 (Z_to_bv 64 T) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' (bv_unsigned sp - 16) (bv_unsigned sp).
Lemma gct_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (ctx T : Z),
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  rw_cells asegs m ATSD_CELL [C1 (b8 1)] -> rw_cells asegs m (ATSD_CELL + 4) [C4 (wz 0)] ->
  rw_cells asegs m AMUSL_TSD [C8 (wz 0xc03038)] ->
  rw_cells asegs m ATSD0 [C8 (wz ctx)] -> rw_cells asegs m (ctx + 152) [C8 (wz T)] ->
  0 < ctx -> ctx + 160 <= aceil ->
  stk asegs m (bv_unsigned sp - 16) (bv_unsigned sp) -> aceil <= bv_unsigned sp - 16 ->
  evt asegs (gct_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc T m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1c9254) fc None m (seg_rom asegs)).
Proof.
  intros until T. intros MI Htp C1 C2 C3 C4 C5 CTX0 CTX1 ST0 LO. subst tp.
  acb; unfold ATSD_CELL, AMUSL_TSD, ATSD0, ATP, wz, b8 in *. change (6988128 + 4) with 6988132 in C2.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof ST0 as ST. carve_frame 16%nat ST.
  zstep. st1. zstep.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  zstep. if_cases K; [exfalso; revert K; vm_compute; discriminate|].
  zstep. rewrite (sx32_lit 0) by lia. zstep. zstep.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  zstep. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia|].
  zstep. zstep. zstep. zstep.
  release_frame FR ST (bv_unsigned sp). unfold gct_post. finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dtls_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 a5 a6 a7 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' (bv_unsigned sp - 144) (bv_unsigned sp).
Lemma dtls_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (D : Z),
  mem_inv asegs m -> tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 AGOT_FSTLS ->
  rw_cells asegs m AGOT_FSTLS [C8 (wz 1); C8 (wz 0xfffffffffffff800)] ->
  rw_cells asegs m AGOT_CFLAGS [C8 (wz 0x73c428)] -> rw_cells asegs m ACF_ITLS_CELL [C1 (b8 1)] ->
  rw_cells asegs m AGOT_VERBOSITY [C8 (wz AVERBOSITY_CELL)] -> rw_cells asegs m AVERBOSITY_CELL [C4 (wz 0)] ->
  rw_cells asegs m AGOT_DTLS [C8 (wz 0x18)] ->
  rw_cells asegs m (ATP + 24) [C8 (wz D)] -> rw_cells asegs m (D + 24) [C8 (wz ATP)] ->
  0 < D -> D + 32 <= aceil ->
  stk asegs m (bv_unsigned sp - 144) (bv_unsigned sp) -> aceil <= bv_unsigned sp - 144 ->
  evt asegs (dtls_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1d6cac) fc None m (seg_rom asegs)).
Proof.
  intros until D. intros MI Htp Ha0 G1 G2 C2 G3 C3 G4 TD DD D0 D1 ST0 LO. subst tp a0.
  acb; unfold AGOT_FSTLS, AGOT_CFLAGS, ACF_ITLS_CELL, AGOT_VERBOSITY, AVERBOSITY_CELL, AGOT_DTLS, ATP, wz, b8 in *.
  change (12459152 + 24) with 12459176 in TD.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof ST0 as ST. carve_frame 144%nat ST.
  (* [comment removed for export] *)
  zstep. do 13 st1.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.
  zstep. if_cases K1; [exfalso; revert K1; vm_compute; discriminate|].
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. rewrite (sx32_lit 0) by lia. zstep. zstep. zstep.
  (* [comment removed for export] *)
  zstep. if_cases K2; [exfalso; revert K2; vm_compute; discriminate|].
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  zstep. if_cases K3; zify_cond K3; [exfalso; rewrite ?unsigned_lit in K3 by lia; lia|].
  zstep. if_cases K4; zify_cond K4; [| exfalso; rewrite ?unsigned_lit in K4 by lia; lia].
  zstep. if_cases K5; zify_cond K5; [exfalso; rewrite ?unsigned_lit in K5 by lia; lia|].
  st1. st1. zstep.
  zstep. if_cases K6; [| exfalso; revert K6; vm_compute; discriminate].
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  zstep.
  zstep. if_cases K7; zify_cond K7; [exfalso; rewrite ?unsigned_lit in K7 by lia; lia|].
  (* [comment removed for export] *)
  zstep. do 13 zstep. zstep. zstep.
  release_frame FR ST (bv_unsigned sp). unfold dtls_post. finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition TLS_ICPT_STACK : Z := 176.
Definition tls_icpt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ATP) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ ACONST m' /\ athr_cells m'.
Lemma tls_icpt_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  mem_inv asegs m -> tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 AGOT_FSTLS ->
  ACONST m -> athr_cells m ->
  stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 176 ->
  evt asegs (tls_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1a8784) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros MI Htp Ha0 AC AT ST0 LO LOSP.
  pose proof (ACONST_n5 m AC) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
  destruct AT as (ctx & T & D & tb & te & A1 & A2 & A3 & A4 & A5 & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
  subst tp a0.
  acb; unfold AGOT_FSTLS, AREAL_TLSGA_CELL, AREAL_TLSGA, AINITED_CELL, ATSD_CELL, AMUSL_TSD, AMUSL_DTV, AMUSL_DTV1, AGOT_CFLAGS, ACF_ITLS_CELL, AGOT_VERBOSITY, AVERBOSITY_CELL, AGOT_DTLS, ATSD0, ATP, TLS_ICPT_STACK, wz, b8 in *.
  change (6988128 + 4) with 6988132 in G5. change (12459152 + 24) with 12459176 in A4.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof ST0 as ST. carve_frame 32%nat ST.
  (* [comment removed for export] *)
  zstep. zstep. st1. st1. st1. st1. zstep. zstep.
  destruct (stk_split asegs _ _ (bv_unsigned sp + -32 - 16) _ ST ltac:(lia)) as [STlo SThi].
  call2 tryinit_spec; try eassumption; [rewrite ?unsigned_lit by lia; exact SThi | rewrite ?unsigned_lit by lia; acb; lia |].
  rewrite ?unsigned_lit in * by lia.
  match goal with Hhi : stk asegs ?mx (bv_unsigned sp + -32 - 16) (bv_unsigned sp + -32),
                  Hlo : stk asegs ?mx lo (bv_unsigned sp + -32 - 16) |- _ =>
    pose proof (stk_merge asegs _ _ _ _ Hlo Hhi ltac:(lia)) as ST; clear Hlo Hhi end.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.
  call_pure musl_tlsga_spec; try eassumption; try reflexivity.
  (* [comment removed for export] *)
  zstep. zstep. if_cases K1; [exfalso; revert K1; vm_compute; discriminate|].
  zstep.
  destruct (stk_split asegs _ _ (bv_unsigned sp + -32 - 16) _ ST ltac:(lia)) as [STlo SThi].
  call2 gct_spec; try (first [exact MI0 | exact G4 | exact G5 | exact G6 | exact A1 | exact A2 | exact R1 | exact R3 | eassumption]); try reflexivity;
    [rewrite ?unsigned_lit by lia; exact SThi | rewrite ?unsigned_lit by lia; acb; lia |].
  rewrite ?unsigned_lit in * by lia.
  match goal with Hhi : stk asegs ?mx (bv_unsigned sp + -32 - 16) (bv_unsigned sp + -32),
                  Hlo : stk asegs ?mx lo (bv_unsigned sp + -32 - 16) |- _ =>
    pose proof (stk_merge asegs _ _ _ _ Hlo Hhi ltac:(lia)) as ST; clear Hlo Hhi end.
  (* [comment removed for export] *)
  zstep. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by lia; lia|].
  zstep. zstep. zstep. zstep. zstep. zstep.
  destruct (stk_split asegs _ _ (bv_unsigned sp + -32 - 144) _ ST ltac:(lia)) as [STlo SThi].
  call2 dtls_spec; try eassumption; try reflexivity;
    [rewrite ?unsigned_lit by lia; exact SThi | rewrite ?unsigned_lit by lia; acb; lia |].
  rewrite ?unsigned_lit in * by lia.
  match goal with Hhi : stk asegs ?mx (bv_unsigned sp + -32 - 144) (bv_unsigned sp + -32),
                  Hlo : stk asegs ?mx lo (bv_unsigned sp + -32 - 144) |- _ =>
    pose proof (stk_merge asegs _ _ _ _ Hlo Hhi ltac:(lia)) as ST; clear Hlo Hhi end.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  release_frame FR ST (bv_unsigned sp).
  unfold tls_icpt_post, TLS_ICPT_STACK. finish.
  all: lazymatch goal with
       | |- munch _ _ _ => exact MU
       | |- ACONST _ => eapply ACONST_frame; [exact AC| exact MU| exact WM|]; constructor; [|constructor];
                        apply aconst_ok_high; [| right; left]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia
       | |- athr_cells _ => exists ctx, T, D, tb, te;
            split; [exact A1|]; split; [exact A2|]; split; [exact A3|]; split; [exact A4|]; split; [exact A5|];
            acb; repeat split; lia
       end.
Qed.

End HCW2.

