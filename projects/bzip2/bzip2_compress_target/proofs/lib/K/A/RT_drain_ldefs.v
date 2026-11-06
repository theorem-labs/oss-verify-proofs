(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow R_sizeclass.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface R_cache_defs R_prim_defs R_glue_defs R_thread R_depot_defs R_quar_defs R_qrec_defs R_qrecycle R_qdorec R_qcbrec R_cdealloc RT_state RT_rep RT_freestate RT_drain_defs RT_drain_led RT_drain_start.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow R_sizeclass.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_cache_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_prim_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_glue_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_thread.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_depot_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_quar_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_qrec_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_qrecycle.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_qdorec.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_qcbrec.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_cdealloc.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_state.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_freestate.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_drain_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_drain_led.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_drain_start.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Record dlp : Type := mkDLP {
  dl_Σ0 : rtsA; dl_m0 : mem; dl_usp : Z; dl_lo : Z; dl_PMc : Model -> Prop;
  dl_gp : word; dl_s10 : word; dl_s11 : word; dl_F : bvmap 5 word; dl_fc : bv 32;
  dl_r0 : word; dl_r1 : word; dl_r2 : word; dl_r3 : word; dl_r4 : word; dl_r5 : word; dl_r6 : word; dl_r7 : word; dl_r8 : word;
  dl_r9 : word }.

(* [comment removed for export] *)
Definition wmono_out (G : list ivl) (m m' : mem) : Prop :=
  forall x : word, wview bsegs m x <> None -> outside G (bv_unsigned x) -> wview bsegs m' x <> None.

Lemma wmono_out_nil : forall (m m' : mem), wmono bsegs m m' -> wmono_out [] m m'.
Proof. intros m m' H x Hx _. exact (H x Hx). Qed.
Lemma wmono_out_wmono : forall G (m1 m2 m3 : mem), wmono_out G m1 m2 -> wmono bsegs m2 m3 -> wmono_out G m1 m3.
Proof. intros G m1 m2 m3 H1 H2 x Hx Ho. exact (H2 x (H1 x Hx Ho)). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Vocab.
Variable p : dlp.
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation C := (dl_usp p - 2288).
#[local] Notation T := (l_T (lay (dl_Σ0 p))).
#[local] Notation SB := (l_SB (lay (dl_Σ0 p))).

(* [comment removed for export] *)
Definition dl_gone (G : list ivl) : Prop :=
  Forall (fun r => forall a, fst r <= a < snd r -> ~ aclient (live Σ0) (frames Σ0) (C + 32) a /\ ~ (dl_lo p <= a < C + 32)) G.

(* [comment removed for export] *)
Definition dl_mem (j : list byte) (Σk : rtsA) (rest : list batch) (m : mem) : Prop :=
  ARTc Σk m /\ mem_inv bsegs m /\ stk bsegs m (dl_lo p) (C - 112) /\ (exists G, wmono_out G (dl_m0 p) m /\ dl_gone G)
  /\ rt_pres (live Σ0) (frames Σ0) (C + 32) (dl_m0 p) m
  /\ drec_frame m C j (T + 208) (usp - 2128) (Z_to_bv 64 0x3462c) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p)
       (dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p)
  /\ qcache_rep m C rest.

(* [comment removed for export] *)
Definition dl_sig (Σk : rtsA) : Prop :=
  lay Σk = lay Σ0 /\ live Σk = live Σ0 /\ frames Σk = frames Σ0 /\ credit Σk = credit Σ0 /\ ql Σk = [] /\ ca_init Σk = true.

(* [comment removed for export] *)
Definition dl_Q (j : list byte) (b : Z) (ents : list (Z * Z)) (i : nat) (rest : list batch) (Σk : rtsA) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
    ms = MS (mkR (Z_to_bv 64 0x348e8) (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST)
                 (Z_to_bv 64 (C - 104)) (Z_to_bv 64 (fst (nth i ents (0%Z, 0%Z)))) a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 864024) (Z_to_bv 64 864648) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
                 (Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
                 (dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
            (dl_F p) (Z_to_bv 64 qcbrec_entry) (dl_fc p) None m (seg_rom bsegs)
    /\ dl_mem j Σk rest m /\ qbatch m b (qfirst rest) ents.

(* [comment removed for export] *)
Definition dl_N (j : list byte) (b : Z) (ents : list (Z * Z)) (i : nat) (rest : list batch) (Σk : rtsA) : machine_state -> Prop :=
  fun ms => exists (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
    ms = MS (mkR ra0 (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 864024) (Z_to_bv 64 864648) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
                 (Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
                 (dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
            (dl_F p) (Z_to_bv 64 0x348e8) (dl_fc p) None m (seg_rom bsegs)
    /\ dl_mem j Σk rest m /\ qbatch m b (qfirst rest) ents.

(* [comment removed for export] *)
Definition dl_D (j : list byte) (b : Z) (ents : list (Z * Z)) (rest : list batch) (Σk : rtsA) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a4 a5 a6 a7 s6 s7 s8 s9 t3 t4 t5 t6 : word) (m : mem),
    ms = MS (mkR (Z_to_bv 64 0x34920) (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST)
                 (Z_to_bv 64 (T + 208)) (Z_to_bv 64 INST) (Z_to_bv 64 24) (Z_to_bv 64 b) a4 a5 a6 a7
                 (Z_to_bv 64 864024) (Z_to_bv 64 864648) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) s6 s7 s8 s9
                 (dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
            (dl_F p) (Z_to_bv 64 cdealloc_entry) (dl_fc p) None m (seg_rom bsegs)
    /\ dl_mem j Σk rest m /\ qbatch m b (qfirst rest) ents.

(* [comment removed for export] *)
Definition dl_B (j : list byte) (rest : list batch) (Σk : rtsA) : machine_state -> Prop :=
  fun ms => exists (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6 : word) (m : mem),
    ms = MS (mkR ra0 (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 864024) (Z_to_bv 64 864648) s4 (Z_to_bv 64 (2^37)) s6 s7 s8 s9 (dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
            (dl_F p) (Z_to_bv 64 0x34920) (dl_fc p) None m (seg_rom bsegs)
    /\ dl_mem j Σk rest m.

(* [comment removed for export] *)
Definition dl_R (Σk : rtsA) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
    ms = MS (mkR (Z_to_bv 64 0x3462c) (Z_to_bv 64 C) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (dl_r0 p) (dl_r1 p) a0 a1 a2 a3 a4 a5 a6 a7
                 (dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p) (dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
            (dl_F p) (ret_pc (Z_to_bv 64 0x3462c)) (dl_fc p) None m (seg_rom bsegs)
    /\ ARTc Σk m /\ mem_inv bsegs m /\ stk bsegs m (dl_lo p) C /\ (exists G, wmono_out G (dl_m0 p) m /\ dl_gone G)
    /\ rt_pres (live Σ0) (frames Σ0) (C + 32) (dl_m0 p) m /\ qcache_rep m C [].

(* [comment removed for export] *)
Definition dl_fin : config -> Prop :=
  fun cf => exists Σ' : rtsA, ASTA RTA Σ' (dl_PMc p) (dl_R Σ') cf /\ rt_wfP Σ' [] /\ dl_sig Σ'.

End Vocab.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma qwf_of_wfP : forall Σ P, rt_wfP Σ P -> qwf (l_SB (lay Σ)) P.
Proof.
  intros Σ P (H1 & HR & HV & HS & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9) & _).
  unfold qallP in Q4, Q5, Q6. unfold qentsP, qallP in Q7.
  split.
  { apply NoDup_ListNoDup in Q5. rewrite !map_app in Q5. apply NoDup_app_remove_l in Q5. apply NoDup_app_remove_l in Q5. exact Q5. }
  apply Forall_forall. intros b Hb.
  assert (Hb' : In b (ql Σ ++ qg Σ ++ P)) by (apply in_app_iff; right; apply in_app_iff; right; exact Hb).
  destruct (proj1 (Forall_forall _ _) Q4 b Hb') as (i & Hi & Eb). pose proof (proj1 (Forall_forall _ _) Q6 b Hb') as Hl.
  pose proof HR as (HR1 & _). pose proof (HR1 24 ltac:(lia)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W11).
  pose proof H1 as (_ & _ & _ & _ & _ & HSB & _). change (ClassSize 24) with 8192 in W11.
  assert (Hlt : (i < length (r_st (pr Σ 24)))%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  unfold p_abeg in Eb. change (ClassSize 24) with 8192 in Eb. unfold r24.
  split; [rewrite Eb; apply Z.mod_divide; [lia|]; apply Z.mod_divide in HSB; [|lia]; destruct HSB as (q & Hq);
          exists (q * 8 + 24 * 2 ^ 19 + Z.of_nat i); lia|].
  split; [lia|]. split; [lia|]. split; [exact Hl|].
  apply Forall_forall. intros e He.
  assert (Hq : In e (flat_map snd (ql Σ ++ qg Σ ++ P))) by (apply in_flat_map; exists b; split; [exact Hb' | exact He]).
  pose proof (qent_n_pos Σ e HR HS (proj1 (Forall_forall _ _) Q7 e Hq)). lia.
Qed.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow RT_iface R_sizeclass R_cache_defs R_prim_defs R_glue_defs R_thread
  R_depot_defs R_quar_defs R_qrec_defs R_qrecycle R_qdorec R_qcbrec R_cdealloc RT_state RT_rep RT_freestate RT_drain_defs RT_drain_led
  RT_drain_start.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Record dlp : Type := mkDLP {
  dl_Σ0 : rtsA; dl_m0 : mem; dl_usp : Z; dl_lo : Z; dl_PMc : Model -> Prop;
  dl_gp : word; dl_s10 : word; dl_s11 : word; dl_F : bvmap 5 word; dl_fc : bv 32;
  dl_r0 : word; dl_r1 : word; dl_r2 : word; dl_r3 : word; dl_r4 : word; dl_r5 : word; dl_r6 : word; dl_r7 : word; dl_r8 : word;
  dl_r9 : word }.

(* [comment removed for export] *)
Definition wmono_out (G : list ivl) (m m' : mem) : Prop :=
  forall x : word, wview asegs m x <> None -> outside G (bv_unsigned x) -> wview asegs m' x <> None.

Lemma wmono_out_nil : forall (m m' : mem), wmono asegs m m' -> wmono_out [] m m'.
Proof. intros m m' H x Hx _. exact (H x Hx). Qed.
Lemma wmono_out_wmono : forall G (m1 m2 m3 : mem), wmono_out G m1 m2 -> wmono asegs m2 m3 -> wmono_out G m1 m3.
Proof. intros G m1 m2 m3 H1 H2 x Hx Ho. exact (H2 x (H1 x Hx Ho)). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Vocab.
Variable p : dlp.
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation C := (dl_usp p - 2288).
#[local] Notation T := (l_T (lay (dl_Σ0 p))).
#[local] Notation SB := (l_SB (lay (dl_Σ0 p))).

(* [comment removed for export] *)
Definition dl_gone (G : list ivl) : Prop :=
  Forall (fun r => forall a, fst r <= a < snd r -> ~ aclient (live Σ0) (frames Σ0) (C + 32) a /\ ~ (dl_lo p <= a < C + 32)) G.

(* [comment removed for export] *)
Definition dl_mem (j : list byte) (Σk : rtsA) (rest : list batch) (m : mem) : Prop :=
  ARTc Σk m /\ mem_inv asegs m /\ stk asegs m (dl_lo p) (C - 112) /\ (exists G, wmono_out G (dl_m0 p) m /\ dl_gone G)
  /\ rt_pres (live Σ0) (frames Σ0) (C + 32) (dl_m0 p) m
  /\ drec_frame m C j (T + 208) (usp - 2128) (Z_to_bv 64 0x34744) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p)
       (dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p)
  /\ qcache_rep m C rest.

(* [comment removed for export] *)
Definition dl_sig (Σk : rtsA) : Prop :=
  lay Σk = lay Σ0 /\ live Σk = live Σ0 /\ frames Σk = frames Σ0 /\ credit Σk = credit Σ0 /\ ql Σk = [] /\ ca_init Σk = true.

(* [comment removed for export] *)
Definition dl_Q (j : list byte) (b : Z) (ents : list (Z * Z)) (i : nat) (rest : list batch) (Σk : rtsA) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
    ms = MS (mkR (Z_to_bv 64 0x34a00) (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST)
                 (Z_to_bv 64 (C - 104)) (Z_to_bv 64 (fst (nth i ents (0%Z, 0%Z)))) a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 809752) (Z_to_bv 64 810376) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
                 (Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
                 (dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
            (dl_F p) (Z_to_bv 64 qcbrec_entry) (dl_fc p) None m (seg_rom asegs)
    /\ dl_mem j Σk rest m /\ qbatch m b (qfirst rest) ents.

(* [comment removed for export] *)
Definition dl_N (j : list byte) (b : Z) (ents : list (Z * Z)) (i : nat) (rest : list batch) (Σk : rtsA) : machine_state -> Prop :=
  fun ms => exists (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
    ms = MS (mkR ra0 (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 809752) (Z_to_bv 64 810376) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
                 (Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
                 (dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
            (dl_F p) (Z_to_bv 64 0x34a00) (dl_fc p) None m (seg_rom asegs)
    /\ dl_mem j Σk rest m /\ qbatch m b (qfirst rest) ents.

(* [comment removed for export] *)
Definition dl_D (j : list byte) (b : Z) (ents : list (Z * Z)) (rest : list batch) (Σk : rtsA) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a4 a5 a6 a7 s6 s7 s8 s9 t3 t4 t5 t6 : word) (m : mem),
    ms = MS (mkR (Z_to_bv 64 0x34a38) (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST)
                 (Z_to_bv 64 (T + 208)) (Z_to_bv 64 INST) (Z_to_bv 64 24) (Z_to_bv 64 b) a4 a5 a6 a7
                 (Z_to_bv 64 809752) (Z_to_bv 64 810376) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) s6 s7 s8 s9
                 (dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
            (dl_F p) (Z_to_bv 64 cdealloc_entry) (dl_fc p) None m (seg_rom asegs)
    /\ dl_mem j Σk rest m /\ qbatch m b (qfirst rest) ents.

(* [comment removed for export] *)
Definition dl_B (j : list byte) (rest : list batch) (Σk : rtsA) : machine_state -> Prop :=
  fun ms => exists (ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6 : word) (m : mem),
    ms = MS (mkR ra0 (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 C) (Z_to_bv 64 INST) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 809752) (Z_to_bv 64 810376) s4 (Z_to_bv 64 (2^37)) s6 s7 s8 s9 (dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
            (dl_F p) (Z_to_bv 64 0x34a38) (dl_fc p) None m (seg_rom asegs)
    /\ dl_mem j Σk rest m.

(* [comment removed for export] *)
Definition dl_R (Σk : rtsA) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
    ms = MS (mkR (Z_to_bv 64 0x34744) (Z_to_bv 64 C) (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 (dl_r0 p) (dl_r1 p) a0 a1 a2 a3 a4 a5 a6 a7
                 (dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p) (dl_s10 p) (dl_s11 p) t3 t4 t5 t6)
            (dl_F p) (ret_pc (Z_to_bv 64 0x34744)) (dl_fc p) None m (seg_rom asegs)
    /\ ARTc Σk m /\ mem_inv asegs m /\ stk asegs m (dl_lo p) C /\ (exists G, wmono_out G (dl_m0 p) m /\ dl_gone G)
    /\ rt_pres (live Σ0) (frames Σ0) (C + 32) (dl_m0 p) m /\ qcache_rep m C [].

(* [comment removed for export] *)
Definition dl_fin : config -> Prop :=
  fun cf => exists Σ' : rtsA, ASTA RTA Σ' (dl_PMc p) (dl_R Σ') cf /\ rt_wfP Σ' [] /\ dl_sig Σ'.

End Vocab.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma qwf_of_wfP : forall Σ P, rt_wfP Σ P -> qwf (l_SB (lay Σ)) P.
Proof.
  intros Σ P (H1 & HR & HV & HS & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9) & _).
  unfold qallP in Q4, Q5, Q6. unfold qentsP, qallP in Q7.
  split.
  { apply NoDup_ListNoDup in Q5. rewrite !map_app in Q5. apply NoDup_app_remove_l in Q5. apply NoDup_app_remove_l in Q5. exact Q5. }
  apply Forall_forall. intros b Hb.
  assert (Hb' : In b (ql Σ ++ qg Σ ++ P)) by (apply in_app_iff; right; apply in_app_iff; right; exact Hb).
  destruct (proj1 (Forall_forall _ _) Q4 b Hb') as (i & Hi & Eb). pose proof (proj1 (Forall_forall _ _) Q6 b Hb') as Hl.
  pose proof HR as (HR1 & _). pose proof (HR1 24 ltac:(lia)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W11).
  pose proof H1 as (_ & _ & _ & _ & _ & HSB & _). change (ClassSize 24) with 8192 in W11.
  assert (Hlt : (i < length (r_st (pr Σ 24)))%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  unfold p_abeg in Eb. change (ClassSize 24) with 8192 in Eb. unfold r24.
  split; [rewrite Eb; apply Z.mod_divide; [lia|]; apply Z.mod_divide in HSB; [|lia]; destruct HSB as (q & Hq);
          exists (q * 8 + 24 * 2 ^ 19 + Z.of_nat i); lia|].
  split; [lia|]. split; [lia|]. split; [exact Hl|].
  apply Forall_forall. intros e He.
  assert (Hq : In e (flat_map snd (ql Σ ++ qg Σ ++ P))) by (apply in_flat_map; exists b; split; [exact Hb' | exact He]).
  pose proof (qent_n_pos Σ e HR HS (proj1 (Forall_forall _ _) Q7 e Hq)). lia.
Qed.
