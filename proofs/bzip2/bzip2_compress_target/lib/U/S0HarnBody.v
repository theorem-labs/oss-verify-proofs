(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require PropExec ShapeAlg.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require SegsS0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require EvtBridge.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
Module S0Memcmp.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.EvtBridge.
 Unset Lia Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Abbreviation mem := (word -> option byte).

Section M.
  Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).

  Definition mst (pc : Z) (t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (m : mem) : machine_state :=
    MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 pc) fc None m (seg_rom s0segs).
  Definition memcmp_post (t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (m : mem) : machine_state -> Prop :=
    fun ms' => exists a1' a2' a3' a4',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m (seg_rom s0segs).

  (* [comment removed for export] *)
  Lemma bytes_at_read1 : forall m p (l : list byte) i, bytes_at s0segs m p l -> (i < length l)%nat ->
    ov_read_bytes s0segs m (Z_to_bv 64 (p + Z.of_nat i)) 1 = Some [nth i l (Z_to_bv 8 0)].
  Proof.
    intros m p l i B Hi. pose proof (bytes_at_ov_read s0segs m p l i 1 B ltac:(lia)) as R. unfold wa in R. rewrite R.
    f_equal. rewrite <- (firstn_skipn i l) at 2. rewrite List.app_nth2 by (rewrite firstn_length; lia).
    rewrite firstn_length, Nat.min_l, Nat.sub_diag by lia.
    destruct (skipn i l) as [|b t] eqn:E; [| reflexivity]. exfalso. apply (f_equal (@length byte)) in E. rewrite skipn_length in E. cbn in E. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma memcmp_loop : forall k i t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (m : mem) (p q : Z) (l : list byte),
    mem_inv s0segs m -> bytes_at s0segs m p l -> bytes_at s0segs m q l -> (i + k = length l)%nat -> (1 <= k)%nat ->
    evt s0segs (memcmp_post t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m)
      (mst 0x30680 t0 t1 t2 s0 s1 (Z_to_bv 64 (p + Z.of_nat i)) (Z_to_bv 64 (q + Z.of_nat i)) (Z_to_bv 64 (Z.of_nat k)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m).
  Proof.
    induction k as [|k IH]; intros until l; intros MI BP BQ HIK HK; [lia|].
    pose proof (bytes_at_bound _ _ _ _ BP) as PB. pose proof (bytes_at_bound _ _ _ _ BQ) as QB.
    pose proof (bytes_at_read1 m p l i BP ltac:(lia)) as RP. pose proof (bytes_at_read1 m q l i BQ ltac:(lia)) as RQ.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl s0segs m) as WM. unfold mst.
    step. step. (* [comment removed for export] *)
    step. if_false. (* [comment removed for export] *)
    zstep. zstep. zstep. (* [comment removed for export] *)
    replace (p + Z.of_nat i + 1) with (p + Z.of_nat (S i)) by lia.
    replace (q + Z.of_nat i + 1) with (q + Z.of_nat (S i)) by lia.
    replace (Z.of_nat (S k) + -1) with (Z.of_nat k) by lia.
    step. if_cases K; zify_cond K.
    - (* [comment removed for export] *) apply (IH (S i)) with (l := l); try assumption; lia.
    - (* [comment removed for export] *) step. step. unfold memcmp_post. apply evt_done. repeat eexists; reflexivity.
  Qed.

  Lemma memcmp_eq : forall t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (m : mem) (p q : Z) (l : list byte),
    mem_inv s0segs m -> bytes_at s0segs m p l -> bytes_at s0segs m q l ->
    evt s0segs (memcmp_post t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m)
      (mst 0x30678 t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 q) (Z_to_bv 64 (Z.of_nat (length l))) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m).
  Proof.
    intros until l; intros MI BP BQ.
    pose proof (bytes_at_bound _ _ _ _ BP) as PB. pose proof (bytes_at_bound _ _ _ _ BQ) as QB.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl s0segs m) as WM. unfold mst.
    step. (* [comment removed for export] *)
    step. if_cases K; zify_cond K.
    - (* [comment removed for export] *) step. step. unfold memcmp_post. apply evt_done. repeat eexists; reflexivity.
    - replace p with (p + Z.of_nat 0) by lia. replace q with (q + Z.of_nat 0) by lia.
      apply (memcmp_loop (length l) 0) with (l := l); try assumption; lia.
  Qed.
End M.
End S0Memcmp.

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec ShapeAlg.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import EvtBridge.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require Import AllocLayout0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocCover AllocDcv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import U.S0HarnStmt U.S0B2BCStmt U.S0B2BDStmt U.S0TRDefs U.S0TRInv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables BzArr BzArrD BzCLemmasFs BzCStream BzCState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCDriver. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDState BzDOut BzR5a BzParams. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzRT1 BzRT2 BzRTB2 BzRT.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0HarnWalk.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0HarnWalk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0HarnBody.S0Memcmp.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Local Abbreviation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wfP_of (len : Z) : Z := if wf_of len =? 0 then 30 else wf_of len.
Lemma bs_of_rng : forall len, 1 <= bs_of len <= 9.
Proof. intros len. unfold bs_of. pose proof (Z.mod_pos_bound len 11 ltac:(lia)). lia. Qed.
Lemma wfP_of_rng : forall len, 1 <= wfP_of len <= 250.
Proof. intros len. unfold wfP_of, wf_of. pose proof (Z.mod_pos_bound len 251 ltac:(lia)). destruct (Z.eqb_spec (len mod 251) 0); lia. Qed.
Definition harnP (len : Z) : BzParams := mkBzParams (bs_of len) (wfP_of len) (bs_of_rng len) (wfP_of_rng len).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma map_u8_roundtrip : forall l : list byte, map (Z_to_bv 8) (map bv_unsigned l) = l.
Proof. induction l as [|b l IH]; [reflexivity|]. cbn [map]. rewrite IH. f_equal. apply definitions.Z_to_bv_bv_unsigned. Qed.
Lemma map_unsigned_u8 : forall l : list Z, bytes_ok l -> map bv_unsigned (map (Z_to_bv 8) l) = l.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|]. apply Forall_cons_iff in H as [H1 H2]. cbn.
  rewrite IH by exact H2. f_equal. apply Z_to_bv_small. unfold bv_modulus. cbn. lia.
Qed.
Lemma bytes_of_payload : forall l : list byte, bytes (map bv_unsigned l).
Proof.
  induction l as [|b l IH]; [constructor|]. cbn. constructor; [| exact IH].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.
Lemma lb_remove_cons_ne : forall p (b : ablock) LB, blk_id b <> p -> lb_remove p (b :: LB) = b :: lb_remove p LB.
Proof.
  intros p b LB H. unfold lb_remove. cbn [List.filter]. destruct (bid_eqb_spec (blk_id b) p); [contradiction|]. reflexivity.
Qed.
Lemma sub48_mod4 : forall u, u mod 16 = 0 -> (u - 48) mod 4 = 0.
Proof. intros u H. pose proof (Z.div_mod u 16 ltac:(lia)) as E. rewrite H in E. replace (u - 48) with ((u / 16 * 4 - 12) * 4) by lia. apply Z_mod_mult. Qed.
Lemma sub48_mod16 : forall u, u mod 16 = 0 -> (u - 48) mod 16 = 0.
Proof. intros u H. pose proof (Z.div_mod u 16 ltac:(lia)) as E. rewrite H in E. replace (u - 48) with ((u / 16 - 3) * 16) by lia. apply Z_mod_mult. Qed.
(* [comment removed for export] *)

Section ACeilS2. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.
Lemma alloc_ceiling_eq : alloc_ceiling = Z.max 0x7fff7f800000 (Z.min 0x7fffff800000 alloc_ceiling).
Proof. pose proof alloc_ceiling_range. lia. Qed.

Section Body.
  Context (AI : AllocIface s0segs S0_layout) (AC : AllocCover s0segs S0_layout AI).
  Hypothesis DCV : alloc_dcv_law s0segs S0_layout AI AC.
  Hypothesis FREEV : alloc_freev_law s0segs S0_layout AI AC.
  Hypothesis HC : forall BZP : BzParams, @b2bC_spec BZP ACEIL__ s0segs S0_layout AI AC S0CI.
  Hypothesis HD : b2bD_spec AI AC S0DI.

  (* [comment removed for export] *)
  Lemma rw_cells_split1 : forall m A c cs,
    rw_cells s0segs m A (c :: cs) -> rw_cells s0segs m A [c] /\ rw_cells s0segs m (A + Z.of_nat (csize c)) cs.
  Proof.
    intros m A c cs [[WF BA] WR]. cbn [cells_wf] in WF. destruct WF as [W1 W2].
    cbn [cells_bytes] in BA. apply (proj1 (bytes_at_app _ _ _ _ _)) in BA. destruct BA as [B1 B2].
    rewrite (cbytes_length c W1) in B2. cbn [cells_size] in WR. cps_destruct WR as (A1 & A2 & WW).
    split; (split; [split|]).
    - cbn. split; [exact W1| exact I].
    - cbn [cells_bytes]. rewrite app_nil_r. exact B1.
    - cbn [cells_size]. split; [lia|]. split; [lia|]. intros i Hi. apply WW. lia.
    - exact W2.
    - exact B2.
    - split; [lia|]. split; [lia|]. intros i Hi. replace (A + Z.of_nat (csize c) + i) with (A + (Z.of_nat (csize c) + i)) by lia. apply WW. lia.
  Qed.
  Lemma rw_cells_bytes_at1 : forall m A n bs cs, rw_cells s0segs m A (CB n bs :: cs) -> bytes_at s0segs m A bs.
  Proof.
    intros m A n bs cs H. apply rw_cells_split1 in H as [[[WF BA] _] _]. cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA. exact BA.
  Qed.

  Section Call.
    Variables (ra0 sp0 gp : word) (x8 x9 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
    Variables (m0 : mem) (MD0 : Model) (LB : list ablock) (src len lo B : Z) (payload : list byte) (k : nat) (K : TSet).
    Local Notation usp := (bv_unsigned sp0).
    Local Notation tpw := (Z_to_bv 64 0x441e0 : word).
    Hypothesis LEN : 0 <= len < 2 ^ 26.
    Hypothesis SB : usp <= B.
    Hypothesis PL : Z.of_nat (length payload) = len.
    Hypothesis CR : client_range S0_layout LB usp src len.
    Hypothesis SRCC : src + len <= alloc_ceiling.
    Hypothesis SRC16 : src mod 16 = 0.
    Hypothesis SRCB : len = 0 \/ exists b, In b LB /\ blk_addr b <= src /\ src + len <= blk_addr b + blk_size b.
    Hypothesis CL : alloc_ceiling <= lo.
    Hypothesis LO : lo <= usp - 65536.
    Hypothesis AL16 : usp mod 16 = 0.
    Hypothesis SPH : usp + 48 <= 2 ^ 47.
    Hypothesis KONT : forall ms' MD',
        harn_post AI AC S0I ra0 sp0 gp tpw x8 x9 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB m0 MD0 lo B k ms' MD' ->
        realizes s0segs (mkCfg ms' MD') K.
    Variable sA : ai_AS AI.
    Hypothesis HI0 : ai_inv AI sA LB m0 MD0.
    Hypothesis SRC0 : bytes_at s0segs m0 src payload.

    Lemma LB_ok : forall b, In b LB -> block_ok S0_layout (blk_addr b) (blk_size b).
    Proof. intros b Hb. exact (ai_inv_blocks AI HI0 Hb). Qed.
    Lemma LOI : 0x66000 <= lo.
    Proof. pose proof CL as X. rewrite alloc_ceiling_eq in X. lia. Qed.
    Lemma SRCPOS : 0 <= src /\ src + len <= 2 ^ 64.
    Proof. pose proof (bytes_at_bound _ _ _ _ SRC0) as X. rewrite PL in X. exact X. Qed.

    (* [comment removed for export] *)
    Definition P0 (a : Z) : Prop := client_addr S0_layout LB usp a.

    Local Notation HST := (hst sp0 gp tpw s4 s5 s6 s7 s8 s9 s10 s11 F fc).
    Local Notation UPPER := (upper ra0 x8 x9 x18 x19).

    (* [comment removed for export] *)
    Definition core (m : mem) : Prop :=
      mem_inv s0segs m /\ stk s0segs m lo (usp - 48) /\ (exists e, rw_cells s0segs m (errno_cell S0_layout) [C4 e])
      /\ ai_aux AI m B /\ harn_mem s0segs S0I m /\ pres P0 m0 m.

    Lemma P0_not_frame : forall a, usp - 48 <= a < usp -> ~ P0 a.
    Proof.
      intros a Ha [H|[H|(b & Hb & Hr)]]; [lia| |].
      - cbn [al_rw_lo al_img_hi S0_layout] in H. pose proof LOI. lia.
      - cps_pose (LB_ok b Hb) as (_ & _ & _ & Hc & _). pose proof CL. lia.
    Qed.
    Lemma P0_client : forall LBx SP a, (forall b, In b LB -> In b LBx) -> SP <= usp -> P0 a -> client_addr S0_layout LBx SP a.
    Proof.
      intros LBx SP a Hi HS [H|[H|(b & Hb & Hr)]]; [left; lia | right; left; exact H | right; right].
      exists b. split; [apply Hi; exact Hb | exact Hr].
    Qed.
    Lemma core_src : forall m, core m -> bytes_at s0segs m src payload.
    Proof.
      (intros m; cps_intros (_ & _ & _ & _ & _ & PR)). eapply pres_bytes_at; [exact PR | exact SRC0 |].
      intros a Ha. unfold P0. eapply client_range_addr; [exact CR | rewrite PL in Ha; exact Ha].
    Qed.
    (* [comment removed for export] *)
    Lemma harn_mem_pres : forall (Q : Z -> Prop) m m',
      (forall a, 0x32098 <= a < 0x33db0 \/ a = 0x64471 -> Q a) -> pres Q m m' -> harn_mem s0segs S0I m -> harn_mem s0segs S0I m'.
    Proof.
      (intros Q m m' HQ PR; cps_intros (G1 & G2 & G3 & G4 & G5 & G6 & G7)). unfold harn_mem. cbn [hi_got hi_relro hi_crc hi_crcx hi_rnums hi_libc S0I] in *.
      repeat match goal with |- _ /\ _ => split end;
        (eapply pres_rw_cells; [exact PR | eassumption | cbn; intros a Ha; apply HQ; lia]).
    Qed.
    Lemma P0_img : forall a, 0x32098 <= a < 0x33db0 \/ a = 0x64471 -> P0 a.
    Proof.
      intros a Ha. right. left. unfold errno_cell. cbn [al_rw_lo al_img_hi al_private al_tp S0_layout]. unfold S0_private. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma core_step : forall LBx m m' e',
      (forall b, In b LB -> In b LBx) ->
      core m -> heap_pres s0segs S0_layout LBx (usp - 48) m m' ->
      mem_inv s0segs m' -> stk s0segs m' lo (usp - 48) -> rw_cells s0segs m' (errno_cell S0_layout) [C4 e'] -> ai_aux AI m' B ->
      core m'.
    Proof.
      (intros LBx m m' e' Hi; cps_intros (MI & ST & ER & AX & HM & PR); intros HP MI' ST' ER' AX').
      assert (PR' : pres P0 m m') by (intros a Ha Hp; apply HP; [exact Ha | apply (P0_client LBx); [exact Hi | lia | exact Hp]]).
      split; [exact MI'|]. split; [exact ST'|]. split; [exists e'; exact ER'|]. split; [exact AX'|]. split.
      - apply (harn_mem_pres P0 m m'); [apply P0_img | exact PR' | exact HM].
      - eapply pres_trans; [exact PR | exact PR'].
    Qed.

    (* [comment removed for export] *)
    Lemma core_frame : forall W m m',
      core m -> munch W m m' -> wmono s0segs m m' -> mem_inv s0segs m' -> stk s0segs m' lo (usp - 48) ->
      Forall (fun iv => usp - 48 <= fst iv /\ snd iv <= usp) W -> core m'.
    Proof.
      (intros W m m'; cps_intros (MI & ST & [e ER] & AX & HM & PR); intros MU WM MI' ST' HW). pose proof LOI as LOI'.
      assert (OUT : forall a, (a < usp - 48 \/ usp <= a) -> outside W a).
      { intros a Ha. clear - HW Ha. induction W as [|[l h] W IH]; [exact I|]. apply Forall_cons_iff in HW as [H1 H2]. cbn in H1. split; [lia| apply IH; exact H2]. }
      pose proof (pres_of_munch W m m' MU WM) as PRW.
      split; [exact MI'|]. split; [exact ST'|]. split.
      { exists e. eapply pres_rw_cells; [exact PRW | exact ER | ]. cbn [cells_size csize]. unfold errno_cell. cbn [al_tp S0_layout]. intros a Ha. apply OUT. pose proof LO. left. lia. }
      split. { eapply (ai_aux_frame AI); [exact AX | exact MU | exact WM |]. rewrite Forall_forall in HW |- *. intros iv Hiv. specialize (HW iv Hiv).
               split; [lia|]. intros a Ha ST0. unfold al_static, S0_layout, S0_static in ST0. cbn in ST0. lia. }
      split. { apply (harn_mem_pres (outside W) m m'); [intros a Ha; apply OUT; lia | exact PRW | exact HM]. }
      eapply pres_trans; [exact PR|]. intros a Ha Hp. apply PRW; [exact Ha|]. apply OUT.
      destruct (Z.lt_ge_cases a (usp - 48)); [left; assumption| right]. destruct (Z.lt_ge_cases a usp); [| assumption].
      exfalso. apply (P0_not_frame a); [lia | exact Hp].
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Lemma stage8 : forall m MD (s' : ai_AS AI) ra t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 t3 t4 t5 t6 (j8 : list byte),
      ai_inv AI s' LB m MD -> ac_vm AC k s' MD -> vm_only MD0 MD -> core m ->
      rw_cells s0segs m (usp - 48) [CB 8 j8] -> rw_cells s0segs m (usp - 40) UPPER ->
      realizes s0segs (mkCfg (HST 0x13b48 ra t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 t3 t4 t5 t6 m) MD) K.
    Proof.
      intros until j8. (intros HI VM VMO; cps_intros (MI & ST & [e ER] & AX & HM & PR); intros LOW UP).
      destruct (ai_inv_model AI HI) as [HH HL].
      eapply (evt_realizes s0segs _ _ MD _ HH HL).
      { eapply (hG8 ra0 sp0 gp tpw x8 x9 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo LO LOI SPH AL16); [exact LOW | exact UP | exact ST | exact MI]. }
      intros ms' [-> ST'].
      apply KONT. unfold harn_post.
      exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, e, m, s'.
      split; [reflexivity|]. split; [exact HI|]. split; [exact VM|]. split; [exact VMO|]. split; [exact MI|]. split; [exact ST'|].
      split; [exact ER|]. split; [exact AX|]. split; [exact PR | exact HM].
    Qed.

    (* [comment removed for export] *)
    Lemma frame_pres : forall LBx m m' A cs, heap_pres s0segs S0_layout LBx (usp - 48) m m' ->
      rw_cells s0segs m A cs -> usp - 48 <= A -> rw_cells s0segs m' A cs.
    Proof. intros LBx m m' A cs HP H HA. eapply heap_pres_rw_cells; [exact HP | exact H | left; exact HA]. Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Lemma stage_free8 : forall m MD (s' : ai_AS AI) LBx t0 t1 t2 xs0 xs1 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 t3 t4 t5 t6 (j8 : list byte) (x : Z),
      ai_inv AI s' LBx m MD -> ac_vm AC k s' MD -> vm_only MD0 MD -> core m ->
      rw_cells s0segs m (usp - 48) [CB 8 j8] -> rw_cells s0segs m (usp - 40) UPPER ->
      ((x = 0 /\ LBx = LB) \/ (exists p n, LBx = (p, x, n) :: LB /\ ~ In p (map blk_id LB))) ->
      0 <= x < 2 ^ 64 ->
      realizes s0segs (mkCfg (MS (mkR (Z_to_bv 64 0x13b48) (Z_to_bv 64 (usp - 48)) gp tpw t0 t1 t2 xs0 xs1 (Z_to_bv 64 x) a1 a2 a3 a4 a5 a6 a7
                                       xs2 xs3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (al_free S0_layout)) fc None m (seg_rom s0segs)) MD) K.
    Proof.
      intros until x. intros HI VM VMO CO LOW UP XF XB. cps_pose CO as (MI & ST & [e ER] & AX & HM & PR).
      destruct (ai_inv_model AI HI) as [HH HL].
      destruct XF as [[-> ->]|(p & n & -> & NIN)].
      - (* [comment removed for export] *)
        apply (ai_free_null AI); [exact HH | exact HL | reflexivity |].
        rewrite ret_pc_even by (try reflexivity; lia). eapply stage8; eassumption.
      - (* [comment removed for export] *)
        pose proof FREEV as FV. unfold alloc_freev_law in FV.
        eapply (FV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m MD s' ((p, x, n) :: LB) k p x n lo B e); clear FV;
          [exact HI | exact VM | left; reflexivity | exact AX | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; exact ST | exact CL
          | rewrite unsigned_lit by lia; cbn [al_stack S0_layout]; lia | exact ER | exact MI | reflexivity | reflexivity |].
        intros s'' m'' MD'' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HI'' VMO'' VM'' MI'' ST'' ERR'' AX'' HP''.
        rewrite unsigned_lit in ST'', HP'' by lia. rewrite lb_remove_head in HI'', HP'' by exact NIN.
        rewrite ret_pc_even by (try reflexivity; lia).
        eapply (stage8 m'' MD'' s''); [exact HI'' | exact VM'' | eapply vm_only_trans; [exact VMO | exact VMO''] | | |].
        + eapply (core_step LB m m''); [auto | exact CO | exact HP'' | exact MI'' | exact ST'' | exact ERR'' | exact AX''].
        + eapply frame_pres; [exact HP'' | exact LOW | lia].
        + eapply frame_pres; [exact HP'' | exact UP | lia].
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Lemma stage7 : forall m MD (s' : ai_AS AI) LBx ra t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 xs2 t3 t4 t5 t6 (j8 : list byte) (ob : Z),
      ai_inv AI s' LBx m MD -> ac_vm AC k s' MD -> vm_only MD0 MD -> core m ->
      rw_cells s0segs m (usp - 48) [CB 8 j8] -> rw_cells s0segs m (usp - 40) UPPER ->
      ((ob = 0 /\ LBx = LB) \/ (exists po n2, LBx = (po, ob, n2) :: LB /\ ~ In po (map blk_id LB))) ->
      0 <= ob < 2 ^ 64 ->
      realizes s0segs (mkCfg (HST 0x13b40 ra t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 xs2 (Z_to_bv 64 ob) t3 t4 t5 t6 m) MD) K.
    Proof.
      intros until ob. intros HI VM VMO CO LOW UP OBF OB. pose proof CO as (MI & _).
      destruct (ai_inv_model AI HI) as [HH HL].
      eapply (evt_realizes s0segs _ _ MD _ HH HL).
      { eapply (hG7 sp0 gp tpw s4 s5 s6 s7 s8 s9 s10 s11 F fc lo LO LOI SPH AL16). exact MI. }
      intros ms' ->. unfold hst, hsp. change (Z_to_bv 64 0x293c4) with (Z_to_bv 64 (al_free S0_layout)).
      eapply stage_free8; eassumption.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Lemma stage6 : forall m MD (s' : ai_AS AI) (obl : list ablock) t0 t1 t2 xs0 xs1 a1 a2 a3 a4 a5 a6 a7 xs2 t3 t4 t5 t6
                          (c0 c4 : cell) (pz : bid) (zb nz ob : Z),
      ai_inv AI s' (obl ++ (pz, zb, nz) :: LB) m MD -> ac_vm AC k s' MD -> vm_only MD0 MD -> core m ->
      csize c0 = 4%nat -> csize c4 = 4%nat ->
      rw_cells s0segs m (usp - 48) [c0] -> rw_cells s0segs m (usp - 44) [c4] -> rw_cells s0segs m (usp - 40) UPPER ->
      ~ In pz (map blk_id LB) -> 0 < zb < 2 ^ 64 ->
      ((ob = 0 /\ obl = []) \/ (exists po n2, obl = [(po, ob, n2)] /\ po <> pz /\ ~ In po (map blk_id LB))) ->
      0 <= ob < 2 ^ 64 ->
      realizes s0segs (mkCfg (MS (mkR (Z_to_bv 64 0x13b40) (Z_to_bv 64 (usp - 48)) gp tpw t0 t1 t2 xs0 xs1 (Z_to_bv 64 zb) a1 a2 a3 a4 a5 a6 a7
                                       xs2 (Z_to_bv 64 ob) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (al_free S0_layout)) fc None m (seg_rom s0segs)) MD) K.
    Proof.
      intros until ob. intros HI VM VMO CO S0' S4' C0 C4' UP NIZ ZB OBL OB. cps_pose CO as (MI & ST & [e ER] & AX & HM & PR).
      pose proof FREEV as FV. unfold alloc_freev_law in FV.
      eapply (FV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m MD s' (obl ++ (pz, zb, nz) :: LB) k pz zb nz lo B e); clear FV;
        [exact HI | exact VM | apply in_or_app; right; left; reflexivity | exact AX | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; exact ST | exact CL
        | rewrite unsigned_lit by lia; cbn [al_stack S0_layout]; lia | exact ER | exact MI | reflexivity | reflexivity |].
      intros s'' m'' MD'' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HI'' VMO'' VM'' MI'' ST'' ERR'' AX'' HP''.
      rewrite unsigned_lit in ST'', HP'' by lia.
      assert (RM : lb_remove pz (obl ++ (pz, zb, nz) :: LB) = obl ++ LB).
      { destruct OBL as [[_ ->]|(po & n2 & -> & NE & _)]; cbn [app].
        - apply lb_remove_head. exact NIZ.
        - rewrite lb_remove_cons_ne by (cbn; exact NE). rewrite lb_remove_head by exact NIZ. reflexivity. }
      rewrite RM in HI'', HP''. rewrite ret_pc_even by (try reflexivity; lia).
      (* [comment removed for export] *)
      assert (LOW : exists j8, rw_cells s0segs m'' (usp - 48) [CB 8 j8]).
      { destruct (rw_cells_forget s0segs m'' (usp - 48) ([c0] ++ [c4])) as [j8 H8].
        - apply rw_cells_app.
          + eapply frame_pres; [exact HP'' | exact C0 | lia].
          + cbn [cells_size]. replace (usp - 48 + Z.of_nat (csize c0 + 0)) with (usp - 44) by (rewrite S0'; cbn; lia).
            eapply frame_pres; [exact HP'' | exact C4' | lia].
        - exists j8. cbn [cells_size app] in H8. rewrite S0', S4' in H8. exact H8. }
      destruct LOW as [j8 LOW].
      eapply (stage7 m'' MD'' s'' (obl ++ LB)); [exact HI'' | exact VM'' | eapply vm_only_trans; [exact VMO | exact VMO''] | | exact LOW | | | exact OB].
      + eapply (core_step (obl ++ LB) m m''); [intros b Hb; apply in_or_app; right; exact Hb | exact CO | exact HP'' | exact MI'' | exact ST'' | exact ERR'' | exact AX''].
      + eapply frame_pres; [exact HP'' | exact UP | lia].
      + destruct OBL as [[-> ->]|(po & n2 & -> & NE & NIO)]; [left; split; reflexivity | right; exists po, n2; split; [reflexivity | exact NIO]].
    Qed.

    (* [comment removed for export] *)
    Lemma harn_mem_D : forall m, harn_mem s0segs S0I m ->
      b2bD_tabs s0segs S0DI m /\ b2bD_got s0segs S0DI m (Z_to_bv 64 0) (Z_to_bv 64 0x33db0) /\ rw_cells s0segs m 0x64471 [C1 (Z_to_bv 8 0)].
    Proof.
      (intros m; cps_intros (G1 & G2 & G3 & G4 & G5 & G6 & G7)). cbn [hi_got hi_relro hi_crc hi_crcx hi_rnums hi_libc hi_stderrF S0I] in *.
      split; [split; [exact (proj1 (rw_cells_split1 m _ _ _ G5)) | exact G6]|]. split; [| exact G7]. split; [| exact G4].
      cbn [bd_got bd_stderrp bd_crc bd_rnums S0DI].
      change (rw_cells s0segs m 205032 ([C8 (Z_to_bv 64 204952)] ++ [C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 204960); C8 (Z_to_bv 64 209272); C8 (Z_to_bv 64 210352)])).
      apply rw_cells_app; [exact G1|]. apply rw_cells_app; [exact G2| exact G3].
    Qed.
    Lemma harn_mem_incs : forall m, harn_mem s0segs S0I m -> rw_cells s0segs m 0x33578 [CB 56 BzIncs.incs_bytes].
    Proof.
      (intros m; cps_intros (G1 & G2 & G3 & G4 & G5 & G6 & G7)). cbn [hi_got hi_relro hi_crc hi_crcx hi_rnums hi_libc hi_stderrF S0I] in *.
      exact (proj2 (rw_cells_split1 m _ _ _ G5)).
    Qed.
    Lemma D_harn_mem : forall m, b2bD_tabs s0segs S0DI m -> b2bD_got s0segs S0DI m (Z_to_bv 64 0) (Z_to_bv 64 0x33db0) ->
      rw_cells s0segs m 0x64471 [C1 (Z_to_bv 8 0)] -> rw_cells s0segs m 0x33578 [CB 56 BzIncs.incs_bytes] -> harn_mem s0segs S0I m.
    Proof.
      intros m [T1 T2] [G GS] LC INC. cbn [bd_got bd_stderrp bd_crc bd_rnums S0DI] in *.
      apply rw_cells_split1 in G as [G1 G]. apply rw_cells_split1 in G as [G2 G3].
      unfold harn_mem. cbn [hi_got hi_relro hi_crc hi_crcx hi_rnums hi_libc hi_stderrF S0I].
      split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact GS|].
      split; [exact (rw_cells_app m _ [CB 1024 bz_crc_table_bytes] [CB 56 BzIncs.incs_bytes] T1 INC)|].
      split; [exact T2| exact LC].
    Qed.
    (* [comment removed for export] *)
    Lemma harn_mem_C : forall m, harn_mem s0segs S0I m ->
      b2bC_mem S0CI m (Z_to_bv 64 0x33db0) /\ rw_cells s0segs m 0x320f0 [C8 (Z_to_bv 64 0)] /\ rw_cells s0segs m 0x320f8 [C8 (Z_to_bv 64 0x320a0)]
      /\ rw_cells s0segs m 0x32108 [C8 (Z_to_bv 64 0x335b0)]
      /\ rw_cells s0segs m 0x335b0 [CB 2048 bz_rnums_table_bytes] /\ rw_cells s0segs m 0x64471 [C1 (Z_to_bv 8 0)].
    Proof.
      (intros m; cps_intros (G1 & G2 & G3 & G4 & G5 & G6 & G7)). cbn [hi_got hi_relro hi_crc hi_crcx hi_rnums hi_libc hi_stderrF S0I] in *.
      apply rw_cells_split1 in G3 as [G3a G3]. apply rw_cells_split1 in G3 as [G3b G3c].
      unfold b2bC_mem, CmpCut.cimg_mem. cbn [CmpCut.ci_segs CmpCut.ci_got CmpCut.ci_stderrp CmpCut.ci_crc CmpCut.ci_crcx bc_ci S0CI CmpCut0.S0C].
      split; [| split; [exact G2| split; [exact G3a | split; [exact G3c | split; [exact G6 | exact G7]]]]].
      split; [exact G1|]. split; [exact G3b|]. split; [exact G4| exact G5].
    Qed.
    Lemma C_harn_mem : forall m sv, b2bC_mem S0CI m sv -> rw_cells s0segs m 0x320f0 [C8 (Z_to_bv 64 0)] -> rw_cells s0segs m 0x320f8 [C8 (Z_to_bv 64 0x320a0)]
      -> rw_cells s0segs m 0x32108 [C8 (Z_to_bv 64 0x335b0)] ->
      rw_cells s0segs m 0x335b0 [CB 2048 bz_rnums_table_bytes] -> rw_cells s0segs m 0x64471 [C1 (Z_to_bv 8 0)] ->
      sv = Z_to_bv 64 0x33db0 -> harn_mem s0segs S0I m.
    Proof.
      (intros m sv; cps_intros (M1 & M2 & M3 & M4); intros G2 G3a G3' G6 G7 ->).
      cbn [CmpCut.ci_segs CmpCut.ci_got CmpCut.ci_stderrp CmpCut.ci_crc CmpCut.ci_crcx bc_ci S0CI CmpCut0.S0C] in M1, M2, M3, M4.
      unfold harn_mem. cbn [hi_got hi_relro hi_crc hi_crcx hi_rnums hi_libc hi_stderrF S0I].
      split; [exact M1|]. split; [exact G2|]. split.
      { change (rw_cells s0segs m 205048 ([C8 (Z_to_bv 64 204960)] ++ [C8 (Z_to_bv 64 209272)] ++ [C8 (Z_to_bv 64 210352)])).
        apply rw_cells_app; [exact G3a | apply rw_cells_app; [exact M2 | exact G3']]. }
      split; [exact M3|]. split; [exact M4|]. split; [exact G6| exact G7].
    Qed.

    (* [comment removed for export] *)
    Lemma blk_not_P0 : forall (s : ai_AS AI) LBx m MD p x n a,
      ai_inv AI s LBx m MD -> (forall b, In b LB -> In b LBx) -> In (p, x, n) LBx -> ~ In p (map blk_id LB) ->
      P0 a -> ~ (x <= a < x + n).
    Proof.
      intros s LBx m MD p x n a HI Hi Hin NIN Hp Hr.
      cps_pose (ai_inv_blocks AI HI Hin) as (B1 & B2 & B3 & B4 & B5). cbn [blk_addr blk_size fst snd al_img_lo al_img_hi S0_layout] in *.
      destruct Hp as [H|[H|(b & Hb & Hrb)]].
      - pose proof CL. pose proof LO. lia.
      - cbn [al_rw_lo al_img_hi S0_layout] in H. lia.
      - assert (NE : b <> (p, x, n)).
        { intros ->. apply NIN. rewrite in_map_iff. exists (p, x, n). split; [reflexivity| exact Hb]. }
        pose proof (ai_inv_disjoint AI HI (Hi b Hb) Hin NE) as D. cbn [blk_addr blk_size fst snd] in D. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma pres_of_out : forall LBx m m' (dst dn dl : Z),
      (forall b, In b LB -> In b LBx) -> (dst <> 0 -> forall a, P0 a -> ~ (dst <= a < dst + dn)) -> usp - 48 <= dl -> dl + 4 <= usp ->
      (forall a : Z, 0 <= a < 2 ^ 64 -> client_addr S0_layout LBx (usp - 48) a -> ~ ((dst <> 0 /\ dst <= a < dst + dn) \/ (dl <= a < dl + 4)) ->
         m' (wa a) = m (wa a) /\ (wview s0segs m (wa a) <> None -> wview s0segs m' (wa a) <> None)) ->
      pres P0 m m'.
    Proof.
      intros LBx m m' dst dn dl Hi Hd D1 D2 HP a Ha Hp. apply HP; [exact Ha | apply (P0_client LBx); [exact Hi | lia | exact Hp] |].
      intros [[X0 X]|X]; [exact (Hd X0 a Hp X)|]. apply (P0_not_frame a); [lia | exact Hp].
    Qed.
    Lemma core_step' : forall m m' e',
      core m -> pres P0 m m' -> mem_inv s0segs m' -> stk s0segs m' lo (usp - 48) -> rw_cells s0segs m' (errno_cell S0_layout) [C4 e'] ->
      ai_aux AI m' B -> harn_mem s0segs S0I m' -> core m'.
    Proof.
      (intros m m' e'; cps_intros (MI & ST & ER & AX & HM & PR); intros PR' MI' ST' ER' AX' HM').
      split; [exact MI'|]. split; [exact ST'|]. split; [exists e'; exact ER'|]. split; [exact AX'|]. split; [exact HM'|].
      eapply pres_trans; [exact PR | exact PR'].
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Lemma stage5 : forall m MD (s' : ai_AS AI) t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (c0 c4 : cell) (pz po : bid) (zb ob n2 : Z),
      ai_inv AI s' ((po, ob, n2) :: (pz, zb, nZ_of len) :: LB) m MD -> ac_vm AC k s' MD -> vm_only MD0 MD -> core m ->
      csize c0 = 4%nat -> csize c4 = 4%nat ->
      rw_cells s0segs m (usp - 48) [c0] -> rw_cells s0segs m (usp - 44) [c4] -> rw_cells s0segs m (usp - 40) UPPER ->
      ~ In pz (map blk_id LB) -> 0 < zb < 2 ^ 64 -> po <> pz -> ~ In po (map blk_id LB) -> 0 < ob < 2 ^ 64 ->
      bytes_at s0segs m ob payload ->
      realizes s0segs (mkCfg (HST 0x30678 (Z_to_bv 64 0x13b34) t0 t1 t2 (Z_to_bv 64 len) (Z_to_bv 64 src)
                                 (Z_to_bv 64 src) (Z_to_bv 64 ob) (Z_to_bv 64 len) a3 a4 a5 a6 a7 (Z_to_bv 64 zb) (Z_to_bv 64 ob) t3 t4 t5 t6 m) MD) K.
    Proof.
      intros until n2. intros HI VM VMO CO S0' S4' C0 C4' UP NIZ ZB NE NIO OB OBP. pose proof CO as (MI & _).
      destruct (ai_inv_model AI HI) as [HH HL].
      eapply (evt_realizes s0segs _ _ MD _ HH HL).
      { unfold hst. rewrite <- PL. eapply memcmp_eq; [exact MI | apply core_src; exact CO | exact OBP]. }
      (intros ms'; cps_intros (a1' & a2' & a3' & a4' & ->)). rewrite ret_pc_even by (try reflexivity; lia).
      eapply (evt_realizes s0segs _ _ MD _ HH HL).
      { eapply (hG6 sp0 gp tpw s4 s5 s6 s7 s8 s9 s10 s11 F fc lo LO LOI SPH AL16). exact MI. }
      intros ms2 ->. unfold hst, hsp. change (Z_to_bv 64 0x293c4) with (Z_to_bv 64 (al_free S0_layout)).
      eapply (stage6 m MD s' [(po, ob, n2)]) with (pz := pz) (nz := nZ_of len) (c0 := c0) (c4 := c4);
        [exact HI | exact VM | exact VMO | exact CO | exact S0' | exact S4' | exact C0 | exact C4' | exact UP | exact NIZ | exact ZB | | lia].
      right. exists po, n2. split; [reflexivity|]. split; [exact NE | exact NIO].
    Qed.

    (* [comment removed for export] *)
    Lemma pres_frame_of_out : forall LBx m m' (dst dn dl flo : Z),
      (dst <> 0 -> dst + dn <= alloc_ceiling) -> dl + 4 <= flo -> usp - 48 <= flo ->
      (forall a : Z, 0 <= a < 2 ^ 64 -> client_addr S0_layout LBx (usp - 48) a -> ~ ((dst <> 0 /\ dst <= a < dst + dn) \/ (dl <= a < dl + 4)) ->
         m' (wa a) = m (wa a) /\ (wview s0segs m (wa a) <> None -> wview s0segs m' (wa a) <> None)) ->
      pres (fun a => flo <= a) m m'.
    Proof.
      intros LBx m m' dst dn dl flo D1 D2 D3 HP a Ha Hf. apply HP; [exact Ha | left; lia |]. pose proof CL. pose proof LO.
      intros [[X0 X]|X]; [pose proof (D1 X0); lia | lia].
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Lemma stage4 : forall m MD (s' : ai_AS AI) (obl : list ablock) t0 t1 t2 a6 a7 t3 t4 t5 t6 (pz : bid) (zb ob : Z)
                          (str : list Z) (junk' : list byte),
      let nZ := nZ_of len in let nz := Z.of_nat (length str) in
      ai_inv AI s' (obl ++ (pz, zb, nZ) :: LB) m MD -> ac_vm AC (3 + k)%nat s' MD -> vm_only MD0 MD -> core m ->
      rw_cells s0segs m (usp - 48) [C4 (Z_to_bv 64 (2 * len))] -> rw_cells s0segs m (usp - 44) [C4 (Z_to_bv 64 nz)] -> rw_cells s0segs m (usp - 40) UPPER ->
      ~ In pz (map blk_id LB) -> block_ok S0_layout zb nZ ->
      bytes_ok str -> nz <= nZ -> rw_cells s0segs m zb [CB (length str) (map (Z_to_bv 8) str); CB (Z.to_nat (nZ - nz)) junk'] ->
      (forall (small : Z) (junkD : BzDState.dst) (dl : Z), small = 0 \/ small = 1 -> len <= dl ->
         let '(r, n, out, _) := buffToBuffDecompress junkD str dl small in (r, n, out) = (BZ_OK, len, map bv_unsigned payload)) ->
      ((ob = 0 /\ obl = []) \/
       (exists po junk2, obl = [(po, ob, 2 * len)] /\ po <> pz /\ ~ In po (map blk_id LB) /\ block_ok S0_layout ob (2 * len) /\
                         rw_cells s0segs m ob [CB (Z.to_nat (2 * len)) junk2])) ->
      0 <= ob < 2 ^ 64 ->
      realizes s0segs (mkCfg (HST 0x15f2c (Z_to_bv 64 0x13b18) t0 t1 t2 (Z_to_bv 64 len) (Z_to_bv 64 src)
                                 (Z_to_bv 64 ob) (Z_to_bv 64 (usp - 48)) (Z_to_bv 64 zb) (Z_to_bv 64 nz) (Z_to_bv 64 (len mod 2)) (Z_to_bv 64 0) a6 a7
                                 (Z_to_bv 64 zb) (Z_to_bv 64 ob) t3 t4 t5 t6 m) MD) K.
    Proof.
      intros until junk'. cbv zeta. intros HI VM VMO CO C0 C4' UP NIZ ZOK STRB NZLE ZCH RT OBL OB.
      cps_pose CO as (MI & ST & [e ER] & AX & HM & PR). cps_pose ZOK as (Z1 & Z2 & Z3 & Z4 & Z5). cbn [al_img_lo al_img_hi S0_layout] in Z5.
      cps_pose (harn_mem_D m HM) as (TABS & GOT & LC).
      assert (NZ : 0 <= nZ_of len < 2 ^ 27).
      { unfold nZ_of. pose proof (Z.div_pos len 100 ltac:(lia) ltac:(lia)). pose proof (Z.mul_div_le len 100 ltac:(lia)). lia. }
      pose proof (Z.mod_pos_bound len 2 ltac:(lia)) as SM.
      assert (INZ : In (pz, zb, nZ_of len) (obl ++ (pz, zb, nZ_of len) :: LB)) by (apply in_or_app; right; left; reflexivity).
      assert (INCL : forall b, In b LB -> In b (obl ++ (pz, zb, nZ_of len) :: LB)) by (intros b Hb; apply in_or_app; right; right; exact Hb).
      (* [comment removed for export] *)
      assert (DSTF : exists p junk, (ob = 0 \/ (In (p, ob, 2 * len) (obl ++ (pz, zb, nZ_of len) :: LB) /\ rw_cells s0segs m ob [CB (Z.to_nat (2 * len)) junk]))
                                   /\ (ob <> 0 -> zb + Z.of_nat (length str) <= ob \/ ob + 2 * len <= zb)
                                   /\ (ob <> 0 -> ob + 2 * len <= alloc_ceiling)).
      { destruct OBL as [[-> ->]|(po & junk2 & -> & NE & NIO & BOK & OCH)].
        - exists pz, []. split; [left; reflexivity|]. split; intros X; exfalso; apply X; reflexivity.
        - exists po, junk2. split; [right; split; [left; reflexivity| exact OCH]|].
          assert (NEB : (po, ob, 2 * len) <> (pz, zb, nZ_of len)) by (intros E; injection E; intros; subst; apply NE; reflexivity).
          pose proof (ai_inv_disjoint AI HI (or_introl eq_refl : In (po, ob, 2 * len) ([(po, ob, 2 * len)] ++ (pz, zb, nZ_of len) :: LB)) INZ NEB) as D.
          cbn [blk_addr blk_size fst snd] in D. cps_destruct BOK as (_ & _ & _ & B4 & _). split; [intros _; lia| intros _; exact B4]. }
      cps_destruct DSTF as (p & junk & DSTF & APART & OBC). unfold hst, hsp.
      eapply (HD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m MD s' (obl ++ (pz, zb, nZ_of len) :: LB) p
                 ob (2 * len) (usp - 48) zb (Z.of_nat (length str)) (len mod 2) lo B (map (Z_to_bv 8) str) junk e (Z_to_bv 64 0) (Z_to_bv 64 0x33db0) k K);
        try reflexivity.
      - lia.
      - lia.
      - lia.
      - exact HI.
      - exact VM.
      - exact AX.
      - rewrite unsigned_lit by lia. lia.
      - exact DSTF.
      - exact C0.
      - rewrite unsigned_lit by lia. lia.
      - lia.
      - apply sub48_mod4. exact AL16.
      - lia.
      - eapply rw_cells_bytes_at1. exact ZCH.
      - rewrite length_map. reflexivity.
      - right. right. exists (pz, zb, nZ_of len). split; [exact INZ|]. cbn. lia.
      - lia.
      - lia.
      - exact Z2.
      - exact APART.
      - left. pose proof CL. pose proof LO. lia.
      - intros X. left. pose proof CL. pose proof LO. pose proof (OBC X). lia.
      - rewrite unsigned_lit by lia. exact ST.
      - exact CL.
      - rewrite unsigned_lit by lia. unfold B2BD_STACK. lia.
      - rewrite unsigned_lit by lia. apply sub48_mod16. exact AL16.
      - rewrite unsigned_lit by lia. lia.
      - exact ER.
      - exact MI.
      - exact TABS.
      - exact GOT.
      - (* [comment removed for export] *)
        intros ms' MD' POST.
        cps_destruct POST as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & e' & m' & s'' & rc & dlv
                          & -> & -> & HI' & VM' & VMO' & MI' & ST' & ER' & AX' & PRES' & DL' & DLV & TABS' & GOT' & RES').
        rewrite !unsigned_lit in ST', PRES' by lia. rewrite ret_pc_even by (try reflexivity; lia).
        destruct (ai_inv_model AI HI') as [HH' HL'].
        (* [comment removed for export] *)
        assert (PRF : pres (fun a => usp - 44 <= a) m m').
        { eapply (pres_frame_of_out _ m m' ob (2 * len) (usp - 48) (usp - 44)); [exact OBC | lia | lia | exact PRES']. }
        assert (C4'' : rw_cells s0segs m' (usp - 44) [C4 (Z_to_bv 64 (Z.of_nat (length str)))]) by (eapply pres_rw_cells; [exact PRF | exact C4' | cbn; intros; lia]).
        assert (UP' : rw_cells s0segs m' (usp - 40) UPPER) by (eapply pres_rw_cells; [exact PRF | exact UP | cbn; intros; lia]).
        assert (PR' : pres P0 m m').
        { eapply (pres_of_out _ m m' ob (2 * len) (usp - 48)); [exact INCL | | lia | lia | exact PRES'].
          intros X0 a Hp Hr. destruct OBL as [[-> _]|(po & junk2 & EO & NE & NIO & BOK & _)]; [lia|].
          refine (blk_not_P0 s' _ m MD po ob (2 * len) a HI INCL _ NIO Hp Hr). rewrite EO. left. reflexivity. }
        assert (LC' : rw_cells s0segs m' 0x64471 [C1 (Z_to_bv 8 0)]).
        { eapply pres_rw_cells; [exact PR' | exact LC | cbn; intros a Ha; apply P0_img; lia]. }
        assert (INC' : rw_cells s0segs m' 0x33578 [CB 56 BzIncs.incs_bytes]).
        { eapply pres_rw_cells; [exact PR' | exact (harn_mem_incs m HM) | cbn; intros a Ha; apply P0_img; lia]. }
        assert (CO' : core m') by (eapply (core_step' m m' e'); [exact CO | exact PR' | exact MI' | exact ST' | exact ER' | exact AX' | apply D_harn_mem; assumption]).
        (* [comment removed for export] *)
        rewrite (map_unsigned_u8 str STRB) in RES'.
        destruct RES' as [(RC & OB0 & DLV0) | [(RC & OBN & DLV0 & junkx & DSTX) | (OBN & junkD & junkx & MODEL)]].
        + (* [comment removed for export] *)
          subst rc. destruct OBL as [[_ ->]|(po & junk2 & -> & NE & NIO & BOK & _)]; [| destruct BOK; lia].
          eapply (evt_realizes s0segs _ _ MD' _ HH' HL').
          { eapply (hG5f sp0 gp tpw s4 s5 s6 s7 s8 s9 s10 s11 F fc lo LO LOI SPH AL16); [exact MI' | vm_compute; discriminate]. }
          intros ms2 ->. unfold hst, hsp. change (Z_to_bv 64 0x293c4) with (Z_to_bv 64 (al_free S0_layout)).
          eapply (stage6 m' MD' s'' []) with (pz := pz) (nz := nZ_of len) (c0 := C4 (Z_to_bv 64 dlv)) (c4 := C4 (Z_to_bv 64 (Z.of_nat (length str))));
            [exact HI' | exact VM' | eapply vm_only_trans; [exact VMO| exact VMO'] | exact CO' | reflexivity | reflexivity | exact DL' | exact C4'' | exact UP' | exact NIZ | lia | left; split; [exact OB0| reflexivity] | lia].
        + (* [comment removed for export] *)
          subst rc. destruct OBL as [[-> _]|(po & junk2 & -> & NE & NIO & BOK & _)]; [exfalso; apply OBN; reflexivity|].
          eapply (evt_realizes s0segs _ _ MD' _ HH' HL').
          { eapply (hG5f sp0 gp tpw s4 s5 s6 s7 s8 s9 s10 s11 F fc lo LO LOI SPH AL16); [exact MI' | vm_compute; discriminate]. }
          intros ms2 ->. unfold hst, hsp. change (Z_to_bv 64 0x293c4) with (Z_to_bv 64 (al_free S0_layout)).
          eapply (stage6 m' MD' s'' [(po, ob, 2 * len)]) with (pz := pz) (nz := nZ_of len) (c0 := C4 (Z_to_bv 64 dlv)) (c4 := C4 (Z_to_bv 64 (Z.of_nat (length str))));
            [exact HI' | exact VM' | eapply vm_only_trans; [exact VMO| exact VMO'] | exact CO' | reflexivity | reflexivity | exact DL' | exact C4'' | exact UP' | exact NIZ | lia | | lia].
          right. exists po, (2 * len). split; [reflexivity|]. split; [exact NE| exact NIO].
        + (* [comment removed for export] *)
          destruct OBL as [[-> _]|(po & junk2 & -> & NE & NIO & BOK & _)]; [exfalso; apply OBN; reflexivity|].
          specialize (RT (len mod 2) junkD (2 * len) ltac:(lia) ltac:(lia)).
          destruct (buffToBuffDecompress junkD str (2 * len) (len mod 2)) as [[[r n] out] dd].
          injection RT as Er En Eo. subst r n out. cps_destruct MODEL as (-> & MOK & _).
          cps_destruct (MOK eq_refl) as (-> & LENO & DSTX).
          rewrite length_map in DSTX. rewrite map_u8_roundtrip in DSTX.
          eapply (evt_realizes s0segs _ _ MD' _ HH' HL').
          { eapply (hG5t sp0 gp tpw s4 s5 s6 s7 s8 s9 s10 s11 F fc lo LO LOI SPH AL16); [exact MI' | exact LEN | exact DL']. }
          (intros ms2; cps_intros (v0 & v1 & v2 & ->)). unfold hst, hsp.
          eapply (stage5 m' MD' s'') with (pz := pz) (po := po) (n2 := 2 * len) (c0 := C4 (Z_to_bv 64 len)) (c4 := C4 (Z_to_bv 64 (Z.of_nat (length str))));
            [exact HI' | exact VM' | eapply vm_only_trans; [exact VMO| exact VMO'] | exact CO' | reflexivity | reflexivity | exact DL' | exact C4'' | exact UP'
            | exact NIZ | lia | exact NE | exact NIO | destruct BOK; lia | ].
          eapply rw_cells_bytes_at1. exact DSTX.
    Qed.

    (* [comment removed for export] *)
    Lemma src_apart : forall (s : ai_AS AI) LBx m MD p x n,
      ai_inv AI s LBx m MD -> (forall b, In b LB -> In b LBx) -> In (p, x, n) LBx -> ~ In p (map blk_id LB) ->
      src + len <= x \/ x + n <= src.
    Proof.
      intros s LBx m MD p x n HI Hi Hin NIN.
      cps_pose (ai_inv_blocks AI HI Hin) as (B1 & B2 & B3 & B4 & B5). cbn [blk_addr blk_size fst snd al_img_lo al_img_hi S0_layout] in *.
      pose proof CL as X1. pose proof LO as X2. pose proof SRCPOS as X3.
      destruct CR as [H|[(H1 & H2 & _)|(b & Hb & Hr1 & Hr2)]]; [right; lia | cbn [al_rw_lo al_img_hi S0_layout] in H1, H2; lia |].
      assert (NE : b <> (p, x, n)) by (intros ->; apply NIN; rewrite in_map_iff; exists (p, x, n); split; [reflexivity| exact Hb]).
      pose proof (ai_inv_disjoint AI HI (Hi b Hb) Hin NE) as D. cbn [blk_addr blk_size fst snd] in D. lia.
    Qed.
    Lemma src_pos : 0 < src.
    Proof.
      pose proof SRCPOS as X3. pose proof CL as X1. pose proof LO as X2. pose proof alloc_ceiling_range as X4.
      destruct CR as [H|[(H1 & _)|(b & Hb & Hr1 & _)]]; [lia | cbn [al_rw_lo S0_layout] in H1; lia |].
      pose proof (LB_ok b Hb) as (B1 & _). lia.
    Qed.
    Lemma SRCB' : forall LBx, (forall b, In b LB -> In b LBx) ->
      len = 0 \/ exists b, In b LBx /\ blk_addr b <= src /\ src + len <= blk_addr b + blk_size b.
    Proof. intros LBx Hi. destruct SRCB as [H|(b & Hb & Hr)]; [left; exact H| right; exists b; split; [apply Hi; exact Hb| exact Hr]]. Qed.
    Lemma CR' : forall LBx SP, (forall b, In b LB -> In b LBx) -> SP <= usp -> client_range S0_layout LBx SP src len.
    Proof.
      intros LBx SP Hi HS. destruct CR as [H|[H|(b & Hb & Hr)]]; [left; lia | right; left; exact H | right; right].
      exists b. split; [apply Hi; exact Hb| exact Hr].
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Lemma stage3 : forall m MD (s' : ai_AS AI) (kk : nat) LB1 t0 t1 t2 a7 t3 t4 t5 t6 (pz : bid) (zb : Z) (j4 junkz : list byte),
      let nZ := nZ_of len in
      ai_inv AI s' LB1 m MD -> ac_vm AC (11 + k)%nat s' MD -> vm_only MD0 MD -> core m ->
      rw_cells s0segs m (usp - 48) [CB 4 j4] -> rw_cells s0segs m (usp - 44) [C4 (Z_to_bv 64 nZ)] -> rw_cells s0segs m (usp - 40) UPPER ->
      ((zb = 0 /\ LB1 = LB) \/ (LB1 = (pz, zb, nZ) :: LB /\ ~ In pz (map blk_id LB) /\ block_ok S0_layout zb nZ /\ rw_cells s0segs m zb [CB (Z.to_nat nZ) junkz])) ->
      0 <= zb < 2 ^ 64 ->
      realizes s0segs (mkCfg (HST 0x15e1c (Z_to_bv 64 0x13adc) t0 t1 t2 (Z_to_bv 64 len) (Z_to_bv 64 src)
                                 (Z_to_bv 64 zb) (Z_to_bv 64 (usp - 48 + 4)) (Z_to_bv 64 src) (Z_to_bv 64 len) (Z_to_bv 64 (bs_of len)) (Z_to_bv 64 0) (Z_to_bv 64 (wf_of len)) a7
                                 (Z_to_bv 64 zb) x19 t3 t4 t5 t6 m) MD) K.
    Proof.
      intros until junkz. cbv zeta. intros HI VM VMO CO C0 C4' UP ZBF ZB.
      cps_pose CO as (MI & ST & [e ER] & AX & HM & PR).
      cps_pose (harn_mem_C m HM) as (CMEM & G2 & G3a & G3' & G6 & G7).
      assert (NZ : 0 <= nZ_of len < 2 ^ 27).
      { unfold nZ_of. pose proof (Z.div_pos len 100 ltac:(lia) ltac:(lia)). pose proof (Z.mul_div_le len 100 ltac:(lia)). lia. }
      assert (INCL : forall b, In b LB -> In b LB1) by (destruct ZBF as [[_ ->]|(-> & _)]; [auto| intros b Hb; right; exact Hb]).
      assert (DSTF : (zb = 0 \/ (In (pz, zb, nZ_of len) LB1 /\ rw_cells s0segs m zb [CB (Z.to_nat (nZ_of len)) junkz]))
                     /\ (zb <> 0 -> src + len <= zb \/ zb + nZ_of len <= src) /\ (zb <> 0 -> zb + nZ_of len <= alloc_ceiling)).
      { destruct ZBF as [[-> ->]|(-> & NIZ & ZOK & ZCH)].
        - split; [left; reflexivity|]. split; intros X; exfalso; apply X; reflexivity.
        - split; [right; split; [left; reflexivity| exact ZCH]|]. split; intros _.
          + eapply (src_apart s' _ m MD pz zb); [exact HI | exact INCL | left; reflexivity | exact NIZ].
          + cps_destruct ZOK as (_ & _ & _ & B4 & _). exact B4. }
      cps_destruct DSTF as (DSTF & APART & ZBC).
      pose proof src_pos as SP0. pose proof SRCPOS as SPR. unfold hst, hsp.
      eapply (HC (harnP len) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m MD s' LB1 pz
                 zb (nZ_of len) (usp - 44) src len (wf_of len) lo B payload junkz e (Z_to_bv 64 0x33db0) (7 + k)%nat K);
        try reflexivity.
      all: try (rewrite unsigned_lit by lia).
      - f_equal. lia.
      - unfold wf_of. pose proof (Z.mod_pos_bound len 251 ltac:(lia)). lia.
      - exact LEN.
      - exact HI.
      - eapply (ac_vm_le _ _ _ AC); [exact VM | lia].
      - exact AX.
      - lia.
      - exact DSTF.
      - exact C4'.
      - lia.
      - lia.
      - replace (usp - 44) with (usp - 48 + 4) by lia. rewrite <- Z.add_mod_idemp_l, (sub48_mod4 _ AL16) by lia. reflexivity.
      - lia.
      - apply core_src. exact CO.
      - exact PL.
      - apply CR'; [exact INCL | lia].
      - exact SP0.
      - exact SRCC.
      - exact SRC16.
      - apply SRCB'. exact INCL.
      - exact APART.
      - left. pose proof CL. pose proof LO. lia.
      - intros X. left. pose proof CL. pose proof LO. pose proof (ZBC X). lia.
      - exact ST.
      - exact CL.
      - unfold B2BC_STACK. lia.
      - apply sub48_mod16. exact AL16.
      - lia.
      - exact ER.
      - exact MI.
      - exact CMEM.
      - (* [comment removed for export] *)
        intros ms' MD' POST.
        cps_destruct POST as (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & e' & m' & s'' & rc & dlv
                          & -> & -> & HI' & VM' & VMO' & MI' & ST' & ER' & AX' & PRES' & DL' & DLV & CMEM' & RES').
        rewrite !unsigned_lit in ST', PRES' by lia. rewrite ret_pc_even by (try reflexivity; lia).
        destruct (ai_inv_model AI HI') as [HH' HL'].
        assert (PRF : pres (fun a => usp - 40 <= a) m m').
        { eapply (pres_frame_of_out _ m m' zb (nZ_of len) (usp - 44) (usp - 40)); [exact ZBC | lia | lia | exact PRES']. }
        assert (PRL : pres (fun a => usp - 48 <= a < usp - 44) m m').
        { intros a Ha Hf. apply PRES'; [exact Ha | left; lia |]. pose proof CL. pose proof LO. intros [[X0 X]|X]; [pose proof (ZBC X0); lia | lia]. }
        assert (C0' : rw_cells s0segs m' (usp - 48) [CB 4 j4]) by (eapply pres_rw_cells; [exact PRL | exact C0 | cbn; intros; lia]).
        assert (UP' : rw_cells s0segs m' (usp - 40) UPPER) by (eapply pres_rw_cells; [exact PRF | exact UP | cbn; intros; lia]).
        assert (PR' : pres P0 m m').
        { eapply (pres_of_out _ m m' zb (nZ_of len) (usp - 44)); [exact INCL | | lia | lia | exact PRES'].
          intros X0 a Hp Hr. destruct ZBF as [[-> _]|(-> & NIZ & _)]; [lia|].
          refine (blk_not_P0 s' _ m MD pz zb (nZ_of len) a HI INCL _ NIZ Hp Hr). left. reflexivity. }
        assert (IMG : forall A cs, rw_cells s0segs m A cs -> 0x32098 <= A -> A + Z.of_nat (cells_size cs) <= 0x33db0 \/ A = 0x64471 /\ cells_size cs = 1%nat -> rw_cells s0segs m' A cs).
        { intros A cs H HA HB. eapply pres_rw_cells; [exact PR' | exact H |]. intros a Ha. apply P0_img. lia. }
        assert (CO' : core m').
        { eapply (core_step' m m' e'); [exact CO | exact PR' | exact MI' | exact ST' | exact ER' | exact AX' |].
          apply (C_harn_mem m' (Z_to_bv 64 0x33db0)); [exact CMEM' | apply IMG; [exact G2| lia| cbn; lia] | apply IMG; [exact G3a| lia| cbn; lia] | apply IMG; [exact G3'| lia| cbn; lia]
                                                   | apply IMG; [exact G6| lia| cbn; lia] | apply IMG; [exact G7| lia| cbn; lia] | reflexivity]. }
        (* [comment removed for export] *)
        assert (LOW : exists j8, rw_cells s0segs m' (usp - 48) [CB 8 j8]).
        { destruct (rw_cells_forget s0segs m' (usp - 48) ([CB 4 j4] ++ [C4 (Z_to_bv 64 dlv)])) as [j8 H8].
          - apply rw_cells_app; [exact C0'|]. cbn [cells_size csize Nat.add]. replace (usp - 48 + Z.of_nat 4) with (usp - 44) by lia. exact DL'.
          - exists j8. exact H8. }
        destruct LOW as [j8 LOW].
        assert (ZBF' : (zb = 0 /\ LB1 = LB) \/ (exists p n, LB1 = (p, zb, n) :: LB /\ ~ In p (map blk_id LB))).
        { destruct ZBF as [[-> ->]|(-> & NIZ & _)]; [left; split; reflexivity| right; exists pz, (nZ_of len); split; [reflexivity| exact NIZ]]. }
        destruct (Z.eq_dec rc 0) as [RC0|RCNZ].
        + (* [comment removed for export] *)
          subst rc. destruct RES' as [(RC & _) | [(RC & _) | (a1 & a2 & ft & inU & uns & mtf & sel & selM & elen & code & rfreq & lenp & bsB & bsL & nIn & oP & nM & junk'
                                                       & -> & -> & -> & ARM)]]; [discriminate | discriminate |].
          cbv zeta in ARM. destruct ARM as (ZBNZ & [(_ & FIT & DLVE & ZCH') | (RC & _)]); [| discriminate].
          destruct ZBF as [[ZB0 _]|(-> & NIZ & ZOK & _)]; [exfalso; exact (ZBNZ ZB0)|].
          set (e0 := est_init znew znew znew inU uns mtf sel selM elen code rfreq lenp bsB bsL nIn oP nM) in *.
          set (str := @enc_stream (harnP len) e0 (map bv_unsigned payload)) in *.
          pose proof (init_ok znew znew znew inU uns mtf sel selM elen code rfreq lenp bsB bsL nIn oP nM zbok_znew' zbok_znew' bh_w32_znew) as IOK.
          cbv zeta in IOK. fold e0 in IOK. destruct IOK as [E0OK SIn].
          assert (PLZ : Z.of_nat (length (map bv_unsigned payload)) = len) by (rewrite length_map; exact PL).
          assert (STRB : bytes_ok str) by (subst str; apply enc_stream_bytes; [exact E0OK | apply SIn | apply bytes_of_payload]).
          (* [comment removed for export] *)
          eapply (evt_realizes s0segs _ _ MD' _ HH' HL').
          { eapply (hG3t sp0 gp tpw s4 s5 s6 s7 s8 s9 s10 s11 F fc lo LO LOI SPH AL16); [exact MI' | exact LEN | exact C0']. }
          (intros ms2; cps_intros (m3 & -> & MU3 & WM3 & MI3 & C03)). unfold hst, hsp.
          assert (ST3 : stk s0segs m3 lo (usp - 48)).
          { eapply stk_transport_disjoint; [exact ST' | exact MU3 | exact WM3 |]. cbn. split; [lia| exact I]. }
          assert (CO3 : core m3).
          { eapply (core_frame [(usp - 48, usp - 44)] m' m3); [exact CO' | exact MU3 | exact WM3 | exact MI3 | exact ST3 |]. constructor; [cbn; lia| constructor]. }
          assert (HI3 : ai_inv AI s'' ((pz, zb, nZ_of len) :: LB) m3 MD').
          { eapply (ai_inv_frame AI); [exact HI' | exact MU3 | exact WM3 |]. constructor; [| constructor]. left. cbn. pose proof CL. pose proof LO. lia. }
          cps_pose CO3 as (_ & _ & [e3 ER3] & AX3 & HM3 & PR3).
          pose proof (pres_of_munch _ m' m3 MU3 WM3) as PRM.
          assert (C43 : rw_cells s0segs m3 (usp - 44) [C4 (Z_to_bv 64 dlv)]) by (eapply pres_rw_cells; [exact PRM | exact DL' | cbn; intros; lia]).
          assert (UP3 : rw_cells s0segs m3 (usp - 40) UPPER) by (eapply pres_rw_cells; [exact PRM | exact UP' | cbn; intros; lia]).
          assert (ZCH3 : rw_cells s0segs m3 zb [CB (length str) (map (Z_to_bv 8) str); CB (Z.to_nat (nZ_of len - Z.of_nat (length str))) junk']).
          { eapply pres_rw_cells; [exact PRM | exact ZCH' |]. cbn [cells_size csize]. intros a Ha. pose proof (ZBC ZBNZ). pose proof CL. pose proof LO.
            cbn [outside]. lia. }
          change (Z_to_bv 64 0x29504) with (Z_to_bv 64 (al_malloc S0_layout)).
          pose proof DCV as DV. unfold alloc_dcv_law in DV.
          eapply (DV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 MD' s'' ((pz, zb, nZ_of len) :: LB) (3 + k)%nat (2 * len) lo B e3); clear DV;
            [exact HI3 | eapply (ac_vm_le _ _ _ AC); [exact VM'| unfold ac_cost; destruct (2 * len <? 1024); lia] | exact AX3 | rewrite unsigned_lit by lia; lia
            | rewrite unsigned_lit by lia; exact ST3 | exact CL | rewrite unsigned_lit by lia; cbn [al_stack S0_layout]; lia | exact ER3 | exact MI3 | reflexivity | reflexivity
            | unfold MAX_REQ_D; lia |].
          intros s4' LB4 m4 MD4 r2 v0 v1 v2 va1 va2 va3 va4 va5 va6 va7 v3 v4 v5 v6 e4 HI4 VMO4 VM4 MI4 ST4 ER4 AX4 HP4 RES4.
          rewrite !unsigned_lit in ST4, HP4 by lia. rewrite ret_pc_even by (try reflexivity; lia).
          destruct (ai_inv_model AI HI4) as [HH4 HL4].
          assert (CO4 : core m4) by (eapply (core_step ((pz, zb, nZ_of len) :: LB) m3 m4); [intros b Hb; right; exact Hb | exact CO3 | exact HP4 | exact MI4 | exact ST4 | exact ER4 | exact AX4]).
          assert (R2 : 0 <= r2 < 2 ^ 64).
          { destruct RES4 as [[-> _]|(_ & (B1 & _ & _ & B4 & _) & _)]; [lia|]. pose proof alloc_ceiling_range. lia. }
          eapply (evt_realizes s0segs _ _ MD4 _ HH4 HL4).
          { eapply (hG4 sp0 gp tpw s4 s5 s6 s7 s8 s9 s10 s11 F fc lo LO LOI SPH AL16) with (nz1 := dlv); [exact MI4 | exact LEN | lia | eapply frame_pres; [exact HP4 | exact C43 | lia]]. }
          (intros ms5; cps_intros (w0 & w1 & w2 & ->)). unfold hst, hsp. rewrite DLVE.
          assert (RT : forall (small : Z) (junkD : BzDState.dst) (dl : Z), small = 0 \/ small = 1 -> len <= dl ->
                    let '(r, n, out, _) := buffToBuffDecompress junkD str dl small in (r, n, out) = (BZ_OK, len, map bv_unsigned payload)).
          { intros small junkD dl Hs Hdl.
            pose proof (@rt_small (harnP len) small junkD e0 (map bv_unsigned payload) dl Hs E0OK (SIn _) (bytes_of_payload payload) ltac:(rewrite PLZ; exact Hdl)) as X.
            rewrite PLZ in X. exact X. }
          assert (ZCH4 : rw_cells s0segs m4 zb [CB (length str) (map (Z_to_bv 8) str); CB (Z.to_nat (nZ_of len - Z.of_nat (length str))) junk']).
          { eapply heap_pres_rw_cells; [exact HP4 | exact ZCH3 |]. right. right. exists (pz, zb, nZ_of len). split; [left; reflexivity|].
            cbn [blk_addr blk_size fst snd cells_size csize]. lia. }
          rewrite DLVE in C43.
          assert (VMO4' : vm_only MD0 MD4) by (eapply vm_only_trans; [exact VMO | eapply vm_only_trans; [exact VMO' | exact VMO4]]).
          destruct RES4 as [[-> ->]|(R2NZ & BOK2 & (po & -> & NIO2) & (junk2 & OCH))].
          * eapply (stage4 m4 MD4 s4' [] _ _ _ _ _ _ _ _ _ pz zb 0 str junk');
              [exact HI4 | exact VM4 | exact VMO4' | exact CO4 | eapply frame_pres; [exact HP4 | exact C03 | lia] | eapply frame_pres; [exact HP4 | exact C43 | lia] | eapply frame_pres; [exact HP4 | exact UP3 | lia]
              | exact NIZ | exact ZOK | exact STRB | exact FIT | exact ZCH4 | exact RT | left; split; reflexivity | lia].
          * cbn [map blk_id fst In] in NIO2.
            eapply (stage4 m4 MD4 s4' [(po, r2, 2 * len)] _ _ _ _ _ _ _ _ _ pz zb r2 str junk');
              [exact HI4 | exact VM4 | exact VMO4' | exact CO4 | eapply frame_pres; [exact HP4 | exact C03 | lia] | eapply frame_pres; [exact HP4 | exact C43 | lia] | eapply frame_pres; [exact HP4 | exact UP3 | lia]
              | exact NIZ | exact ZOK | exact STRB | exact FIT | exact ZCH4 | exact RT | | exact R2].
            right. exists po, junk2. split; [reflexivity|]. split; [intros E; apply NIO2; left; symmetry; exact E|]. split; [intros X; apply NIO2; right; exact X|].
            split; [exact BOK2 | exact OCH].
        + (* [comment removed for export] *)
          assert (RCM : rc mod 2 ^ 64 <> 0).
          { destruct RES' as [(-> & _) | [(-> & _) | (a1 & a2 & ft & inU & uns & mtf & sel & selM & elen & code & rfreq & lenp & bsB & bsL & nIn & oP & nM & junk'
                                                 & _ & _ & _ & ARM)]]; [vm_compute; discriminate | vm_compute; discriminate |].
            cbv zeta in ARM. destruct ARM as (_ & [(RC & _) | (-> & _)]); [exfalso; exact (RCNZ RC) | vm_compute; discriminate]. }
          eapply (evt_realizes s0segs _ _ MD' _ HH' HL').
          { eapply (hG3f sp0 gp tpw s4 s5 s6 s7 s8 s9 s10 s11 F fc lo LO LOI SPH AL16); [exact MI' | exact RCM]. }
          intros ms2 ->. unfold hst, hsp. change (Z_to_bv 64 0x293c4) with (Z_to_bv 64 (al_free S0_layout)).
          eapply (stage_free8 m' MD' s'' LB1); [exact HI' | eapply (ac_vm_le _ _ _ AC); [exact VM' | lia] | eapply vm_only_trans; [exact VMO | exact VMO']
                                               | exact CO' | exact LOW | exact UP' | exact ZBF' | exact ZB].
    Qed.
  End Call.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem harn_s0 : harn_spec AI AC S0I.
  Proof.
    unfold harn_spec.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m MD s LB src len lo B payload errv k K
           A0 A1 TP LEN HI VM AUX SB BA PL CR SRCC SRC16 SRCB ST CL LO AL16 SPH ERR MI HM KONT.
    subst a0 a1 tp. cbn [hi_entry S0I al_tp S0_layout].
    pose proof CL as LOI'. rewrite alloc_ceiling_eq in LOI'.
    pose proof (bytes_at_bound _ _ _ _ BA) as SRCR. rewrite PL in SRCR.
    destruct (ai_inv_model AI HI) as [HH HL].
    (* [comment removed for export] *)
    eapply (evt_realizes s0segs _ _ MD _ HH HL).
    { eapply (hG1 ra sp gp (Z_to_bv 64 279008) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo ltac:(unfold HARN_STACK in LO; lia) ltac:(lia) SPH AL16);
        [exact ST | exact MI | exact LEN | lia]. }
    (intros ms1; cps_intros (t0' & t1' & t2' & a1' & m1 & j4 & -> & MU1 & WM1 & MI1 & FR1 & ST1)). unfold hst, hsp.
    apply rw_cells_split1 in FR1 as [C0 FR1]. apply rw_cells_split1 in FR1 as [C4' UP]. cbn [csize Nat.add] in C4', UP.
    replace (bv_unsigned sp - 48 + Z.of_nat 4) with (bv_unsigned sp - 44) in C4', UP by lia.
    replace (bv_unsigned sp - 44 + Z.of_nat 4) with (bv_unsigned sp - 40) in UP by lia.
    assert (LO' : lo <= bv_unsigned sp - 65536) by (unfold HARN_STACK in LO; lia).
    assert (CO0 : core sp m LB lo B m).
    { split; [exact MI|]. split; [exact (proj1 (stk_split s0segs m lo (bv_unsigned sp - 48) (bv_unsigned sp) ST ltac:(lia)))|].
      split; [exists errv; exact ERR|]. split; [exact AUX|]. split; [exact HM| apply pres_refl]. }
    assert (CO1 : core sp m LB lo B m1).
    { eapply (core_frame sp m MD LB src lo B payload SB CL LO' s HI [(bv_unsigned sp - 48, bv_unsigned sp)] m m1);
        [exact CO0 | exact MU1 | exact WM1 | exact MI1 | exact ST1 |]. constructor; [cbn; lia| constructor]. }
    assert (HI1 : ai_inv AI s LB m1 MD).
    { eapply (ai_inv_frame AI); [exact HI | exact MU1 | exact WM1 |]. constructor; [| constructor]. left. cbn. lia. }
    cps_pose CO1 as (_ & _ & [e1 ER1] & AX1 & HM1 & PR1).
    assert (NZ : 0 <= nZ_of len < 2 ^ 27).
    { unfold nZ_of. pose proof (Z.div_pos len 100 ltac:(lia) ltac:(lia)). pose proof (Z.mul_div_le len 100 ltac:(lia)). lia. }
    (* [comment removed for export] *)
    change (Z_to_bv 64 0x29504) with (Z_to_bv 64 (al_malloc S0_layout)).
    pose proof DCV as DV. unfold alloc_dcv_law in DV.
    eapply (DV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 MD s LB (11 + k)%nat (nZ_of len) lo B e1); clear DV;
      [exact HI1 | eapply (ac_vm_le _ _ _ AC); [exact VM| unfold ac_cost, HARN_VM_NEED; destruct (nZ_of len <? 1024); lia] | exact AX1 | rewrite unsigned_lit by lia; lia
      | rewrite unsigned_lit by lia; exact ST1 | exact CL | rewrite unsigned_lit by lia; cbn [al_stack S0_layout]; lia | exact ER1 | exact MI1 | reflexivity | reflexivity
      | unfold MAX_REQ_D; lia |].
    intros sa2 LB2 m2 MD2 r v0 v1 v2 va1 va2 va3 va4 va5 va6 va7 v3 v4 v5 v6 e2 HI2 VMO2 VM2 MI2 ST2 ER2 AX2 HP2 RES2.
    rewrite !unsigned_lit in ST2, HP2 by lia. rewrite ret_pc_even by (try reflexivity; lia).
    destruct (ai_inv_model AI HI2) as [HH2 HL2].
    assert (CO2 : core sp m LB lo B m2).
    { eapply (core_step sp m LB src lo B payload LB m1 m2 e2); [auto | exact CO1 | exact HP2 | exact MI2 | exact ST2 | exact ER2 | exact AX2]. }
    assert (R : 0 <= r < 2 ^ 64).
    { destruct RES2 as [[-> _]|(_ & (B1 & _ & _ & B4 & _) & _)]; [lia|]. pose proof alloc_ceiling_range. lia. }
    (* [comment removed for export] *)
    eapply (evt_realizes s0segs _ _ MD2 _ HH2 HL2).
    { eapply (hG2 sp gp (Z_to_bv 64 279008) s4 s5 s6 s7 s8 s9 s10 s11 F fc lo LO' ltac:(lia) SPH AL16); [exact MI2 | exact LEN | lia | exact R]. }
    (intros ms3; cps_intros (w0 & w1 & w2 & ->)). unfold hst, hsp.
    destruct RES2 as [[-> ->]|(RNZ & BOK & (pz & -> & NIZ) & (junkz & ZCH))].
    - eapply (stage3 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m MD LB src len lo B payload k K LEN SB PL CR SRCC SRC16 SRCB CL LO' AL16 SPH KONT s HI BA
                m2 MD2 sa2 0%nat LB _ _ _ _ _ _ _ _ (0%N, 0, 0) 0 j4 []);
        [exact HI2 | exact VM2 | exact VMO2 | exact CO2 | | | | left; split; reflexivity | lia];
        (eapply (frame_pres sp LB m1 m2); [exact HP2 | eassumption | lia]).
    - eapply (stage3 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m MD LB src len lo B payload k K LEN SB PL CR SRCC SRC16 SRCB CL LO' AL16 SPH KONT s HI BA
                m2 MD2 sa2 0%nat ((pz, r, nZ_of len) :: LB) _ _ _ _ _ _ _ _ pz r j4 junkz);
        [exact HI2 | exact VM2 | exact VMO2 | exact CO2 | | | | right; split; [reflexivity| split; [exact NIZ | split; [exact BOK | exact ZCH]]] | lia];
        (eapply (frame_pres sp LB m1 m2); [exact HP2 | eassumption | lia]).
  Qed.
End Body.
End ACeilS2.
