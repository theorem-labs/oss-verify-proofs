(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface Sj_akit Sj_acps Sj_hkit Sj_num_akit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition PJ_APPEND_ELEM_A : Z := 0xb7eb0.
Definition PJ_APPEND_ARR_A : Z := 0xbb3e0.
Definition PJ_APPEND_OBJ_A : Z := 0xbb8b8.
Definition PJ_GROW_A : Z := 0xbdd9c.
Definition PJ_OSPUT_A : Z := 0xbdeb4.
Definition PJ_PADOUT_A : Z := 0xbe53c.
Definition PJ_TOCHARS_A : Z := 0xbff40.
Definition PJ_SF_A : Z := 0xf5ffc.
Definition PJ_XSPUTN_A : Z := 0x12081c.
Definition PJ_OVERFLOW_A : Z := 0xb0984.
Definition PJ_OS_CTOR_A : Z := 0xaeed8.
Definition PJ_OS_BASE_DTOR_A : Z := 0x113274.
Definition PJ_LOC_DTOR_A : Z := 0x146d8c.
Definition PJ_IOS_DTOR_A : Z := 0x120610.
Definition OPNEWARR_A : Z := 0x1788fc.
Definition OPDELARR_A : Z := 0x119d54.
Definition TPV_A : Z := 0x6be3e8.

Definition PJ_GROW_STACK_A : Z := 64 + 48 + RT_STACK.

Definition PJ_TC_STACK_A : Z := 224 + RT_STACK.

Definition ser_needA (d : nat) : Z := 432 + 50 * Z.of_nat d + PJ_TC_STACK_A.
Definition cont_needA (d : nat) : Z := 368 + ser_needA d.
Definition PJ_SER_STACK_A : Z := ser_needA 1024.

Definition PJ_GROWC : Z := 16384 + 2 * DCOST.
Lemma PJ_GROWC_val : PJ_GROWC = 2113536.
Proof. reflexivity. Qed.
Lemma mcost_le_growc : forall z, 0 <= z -> mcost z <= 2 * z + PJ_GROWC.
Proof. intros z Hz. rewrite PJ_GROWC_val. unfold mcost, DCOST. change (2 ^ 20) with 1048576. destruct (z <=? 64512); lia. Qed.

Record sbA : Type := mkSbA { sa_buf : Z; sa_size : Z; sa_cap : Z; sa_heap : bool; sa_k : Z }.

Definition sbchunkA (st : sbA) : list (Z * Z) := if sa_heap st then [(sa_buf st, sa_cap st)] else [].

Definition sbA0 (SB : Z) : sbA := mkSbA SB 0 64 false 0.

Definition sb_grownA (st : sbA) (NEW z : Z) : sbA := mkSbA NEW (sa_size st) z true (sa_k st + 1).

Definition sb_sized (st : sbA) (size : Z) : sbA := mkSbA (sa_buf st) size (sa_cap st) (sa_heap st) (sa_k st).

Definition pj_psi (len : Z) (st : sbA) : Z := 4 * (PJ_CAPMAX len - sa_cap st) + (24 - sa_k st) * PJ_GROWC.

Definition sb_accA (st : sbA) (i c : Z) : Prop := sa_size st <= 41 * (i - 1) + 6 * c + 2.
Definition sb_acc1A (st : sbA) (i c : Z) : Prop := sa_size st <= 41 * (i - 1) + 6 * c + 3.

Record pjenvA : Type := mkPJA {
  pa_lo : Z;
  pa_F : Z;  pa_kF : nat;
  pa_SB : Z;
  pa_DOC : Z;
  pa_TAPE : Z;  pa_NT : Z;  pa_SBUF : Z;  pa_NS : Z;
  pa_tws : list Z;  pa_sbs : list Z;
  pa_len : Z;
  pa_L : list (Z * Z) }.

Notation pa_T E := (Tf (pa_tws E)).
Notation pa_S E := (Tf (pa_sbs E)).
Notation pa_n E := (Z.of_nat (length (pa_tws E))).
Notation pa_sn E := (Z.of_nat (length (pa_sbs E))).

Record pjenvA_ok (E : pjenvA) : Prop := mkPJAok {
  ok_wfS : tape_wfS (pa_T E) (pa_S E) (pa_sn E) ck_any (pa_n E);
  ok_sbs : Forall (fun c => 0 <= c < 256) (pa_sbs E);
  ok_len : 0 <= pa_len E <= SJ_PADMAX;
  ok_sizes : 8 * pa_n E <= SJ_TAPE (pa_len E) /\ pa_sn E <= SJ_SBUF (pa_len E);

  ok_tape : pa_TAPE E mod 16 = 0 /\ 8 * pa_n E <= pa_NT E /\ 0 < pa_TAPE E /\ pa_TAPE E + pa_NT E <= pa_lo E /\ In (pa_TAPE E, pa_NT E) (pa_L E);
  ok_sbuf : pa_SBUF E mod 16 = 0 /\ pa_sn E <= pa_NS E /\ 0 < pa_SBUF E /\ pa_SBUF E + pa_NS E <= pa_lo E /\ In (pa_SBUF E, pa_NS E) (pa_L E);
  ok_Lpos : forall p n, In (p, n) (pa_L E) -> 0 < n;

  ok_frame : pa_F E mod 64 = 0 /\ SEGTOP_A <= pa_F E /\ pa_F E + fs_size (pa_kF E) <= pa_lo E;
  ok_sb : pa_SB E mod 32 = 0 /\ pa_F E <= pa_SB E /\ pa_SB E + 88 <= pa_F E + fs_size (pa_kF E) - 8;
  ok_doc : pa_DOC E mod 8 = 0 /\ pa_F E <= pa_DOC E /\ pa_DOC E + 16 <= pa_F E + fs_size (pa_kF E) - 8;
  ok_apart : pa_SB E + 88 <= pa_DOC E \/ pa_DOC E + 16 <= pa_SB E;

  ok_lo : 0x7fff7f800000 <= pa_lo E;

  ok_ns8 : pa_NS E mod 8 = 0 }.

Section WithRT.
Variable RT : rt_sig.

Definition pa_live (Σ : rts RT) (E : pjenvA) (st : sbA) : Prop :=
  rt_live RT Σ = sbchunkA st ++ pa_L E /\ In (pa_F E, pa_kF E) (rt_frames RT Σ) /\ rt_sp0 RT Σ - STACK_WIN <= pa_lo E.

Lemma pa_live_eq : forall Σ Σ' E st, pa_live Σ E st -> rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ ->
  rt_sp0 RT Σ' = rt_sp0 RT Σ -> pa_live Σ' E st.
Proof. intros Σ Σ' E st (A & B & C) E1 E2 E3. unfold pa_live. rewrite E1, E2, E3. exact (conj A (conj B C)). Qed.

Lemma pa_live_push : forall Σ Σ' E st fr, pa_live Σ E st -> rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = fr ++ rt_frames RT Σ ->
  rt_sp0 RT Σ' = rt_sp0 RT Σ -> pa_live Σ' E st.
Proof.
  intros Σ Σ' E st fr (A & B & C) E1 E2 E3. unfold pa_live. rewrite E1, E2, E3.
  split; [exact A|]. split; [apply in_or_app; right; exact B| exact C].
Qed.

End WithRT.

Definition SBINVA (E : pjenvA) (m : mem) (st : sbA) : Prop :=
  rw_cells bsegs m (pa_SB E + 64) [C8 (Z_to_bv 64 (sa_buf st)); C8 (Z_to_bv 64 (sa_size st)); C8 (Z_to_bv 64 (sa_cap st))]
  /\ 0 <= sa_size st <= sa_cap st
  /\ (exists bs, rw_cells bsegs m (sa_buf st) [CB (Z.to_nat (sa_cap st)) bs])
  /\ (exists ji, rw_cells bsegs m (pa_SB E) [CB 64 ji])
  /\ bytes_at bsegs m (shad (pa_SB E)) (repeat z8 11)
  /\ (0 <= sa_k st /\ 64 * 2 ^ (sa_k st) <= sa_cap st <= PJ_CAPMAX (pa_len E))
  /\ (if sa_heap st then 0 < sa_buf st /\ sa_buf st mod 16 = 0 /\ sa_buf st + sa_cap st <= pa_lo E
      else sa_buf st = pa_SB E /\ sa_cap st = 64 /\ sa_k st = 0).

Definition DOCREPA (E : pjenvA) (m : mem) : Prop :=
  rw_cells bsegs m (pa_DOC E) [C8 (Z_to_bv 64 (pa_TAPE E)); C8 (Z_to_bv 64 (pa_SBUF E))]
  /\ bytes_at bsegs m (shad (pa_DOC E)) [z8; z8]
  /\ bytes_at bsegs m (pa_TAPE E) (u64s (map (Z_to_bv 64) (pa_tws E)))
  /\ bytes_at bsegs m (pa_SBUF E) (map (Z_to_bv 8) (pa_sbs E)).

Definition docrep_rng (E : pjenvA) (x : Z) : Prop :=
  (pa_DOC E <= x < pa_DOC E + 16) \/ (shad (pa_DOC E) <= x < shad (pa_DOC E) + 2)
  \/ (pa_TAPE E <= x < pa_TAPE E + 8 * pa_n E) \/ (pa_SBUF E <= x < pa_SBUF E + pa_sn E).

Lemma DOCREPA_agree : forall E m m', DOCREPA E m -> agree_on (docrep_rng E) m m' -> DOCREPA E m'.
Proof.
  intros E m m' (H1 & H2 & H3 & H4) AG. unfold DOCREPA, docrep_rng in *.
  split; [| split; [| split]].
  - eapply rw_cells_agree_nw; [exact H1|]. intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. lia.
  - eapply bytes_at_agree; [exact H2|]. intros a Ha. apply AG. cbn [length] in Ha. lia.
  - eapply bytes_at_agree; [exact H3|]. intros a Ha. apply AG. rewrite u64s_length, length_map in Ha. lia.
  - eapply bytes_at_agree; [exact H4|]. intros a Ha. apply AG. rewrite length_map in Ha. lia.
Qed.

Definition sbinv_rng (E : pjenvA) (st : sbA) (x : Z) : Prop :=
  (pa_SB E <= x < pa_SB E + 88) \/ (shad (pa_SB E) <= x < shad (pa_SB E) + 11) \/ (sa_buf st <= x < sa_buf st + sa_cap st).

Lemma SBINVA_agree : forall E m m' st, SBINVA E m st -> agree_on (sbinv_rng E st) m m' -> SBINVA E m' st.
Proof.
  intros E m m' st (H1 & H2 & (bs & H3) & (ji & H4) & H5 & H6 & H7) AG. unfold SBINVA, sbinv_rng in *.
  split; [| split; [exact H2| split; [| split; [| split; [| split; [exact H6| exact H7]]]]]].
  - eapply rw_cells_agree_nw; [exact H1|]. intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. lia.
  - exists bs. eapply rw_cells_agree_nw; [exact H3|]. intros a Ha. apply AG. cbn [cells_size csize] in Ha. rewrite Nat.add_0_r, Z2Nat.id in Ha by lia. lia.
  - exists ji. eapply rw_cells_agree_nw; [exact H4|]. intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. lia.
  - eapply bytes_at_agree; [exact H5|]. intros a Ha. apply AG. rewrite repeat_length in Ha. lia.
Qed.

Lemma SBINVA_cap_pos : forall E m st, SBINVA E m st -> 64 <= sa_cap st.
Proof.
  intros E m st (_ & _ & _ & _ & _ & (K0 & HC & _) & _). assert (0 < 2 ^ sa_k st) by (apply Z.pow_pos_nonneg; lia). lia.
Qed.

Lemma SBINVA_k : forall E m st, pjenvA_ok E -> SBINVA E m st -> 0 <= sa_k st < 22.
Proof.
  intros E m st OK (_ & _ & _ & _ & _ & (K0 & HC & HM) & _).
  split; [exact K0|]. eapply (chain_fuel (pa_len E) (sa_cap st)); [apply (ok_len E OK)| exact K0| exact HC| exact HM].
Qed.

Lemma pj_psi_nonneg : forall E m st, pjenvA_ok E -> SBINVA E m st -> 0 <= pj_psi (pa_len E) st.
Proof.
  intros E m st OK I. pose proof (SBINVA_k E m st OK I). pose proof I as (_ & _ & _ & _ & _ & (_ & _ & HM) & _).
  unfold pj_psi. rewrite PJ_GROWC_val. lia.
Qed.

Lemma pj_psi_grow : forall len st NEW z, 0 <= sa_k st < 22 -> 64 <= sa_cap st -> 2 * sa_cap st <= z <= PJ_CAPMAX len ->
  mcost z <= pj_psi len st - pj_psi len (sb_grownA st NEW z).
Proof.
  intros len st NEW z K C Z1. pose proof (mcost_le_growc z ltac:(lia)) as M. unfold pj_psi, sb_grownA. cbn [sa_cap sa_k]. rewrite PJ_GROWC_val in *. lia.
Qed.

Lemma pj_psi_sized : forall len st n, pj_psi len (sb_sized st n) = pj_psi len st.
Proof. intros. reflexivity. Qed.

Lemma pj_psi_root : forall len SB, 0 <= len <= SJ_PADMAX -> pj_psi len (sbA0 SB) <= 2^30.
Proof.
  intros len SB HL. pose proof (PJ_CAPMAX_bound len HL). unfold pj_psi, sbA0. cbn [sa_cap sa_k]. rewrite PJ_GROWC_val. lia.
Qed.

Lemma sb_accA_out : forall E st i c, pjenvA_ok E -> 1 <= i <= pa_n E -> 0 <= c <= pa_sn E -> sb_accA st i c -> sa_size st <= PJ_OUTMAX (pa_len E).
Proof.
  intros E st i c OK Hi Hc HA. pose proof (ok_sizes E OK) as [HT HS].
  eapply (pj_out_bound (pa_len E) (pa_n E) (pa_sn E) i c); [apply (ok_len E OK)| exact HT| exact HS| exact Hi| exact Hc| exact HA].
Qed.

Lemma grow_request_okA : forall E m st need, pjenvA_ok E -> SBINVA E m st -> sa_cap st < need -> need <= PJ_OUTMAX (pa_len E) ->
  2 * sa_cap st <= Z.max (2 * sa_cap st) need <= PJ_CAPMAX (pa_len E).
Proof.
  intros E m st need OK I HN HB. pose proof (SBINVA_cap_pos E m st I). pose proof I as (_ & _ & _ & _ & _ & (_ & _ & HM) & _).
  unfold PJ_CAPMAX in *. lia.
Qed.

Definition PJ_LOC_LO_A : Z := 0x6bcc28.
Definition PJ_LOC_HI_A : Z := 0x6bdad8.
Definition PJ_LOC_IMP_A : Z := 0x6bd228.
Definition PJ_CTYPE_VPTR_A : Z := 0x17dca8.

Definition loc0_cellsA : list cell := [CB 3760 (repeat (Z_to_bv 8 0) 3760)].
Definition locb_cellsA (j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15 : list byte) : list cell :=
  [CB 64 j1;
   C8 (Z_to_bv 64 18446744073709551615);
   C4 (Z_to_bv 64 15);
   CB 380 j2;
   C8 (Z_to_bv 64 0x37998);
   C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1);
   CB 22 j3;
   C8 (Z_to_bv 64 0x6bd228);
   C1 (Z_to_bv 8 1);
   CB 199 j4;
   C8 (Z_to_bv 64 18446744073709551615);
   C4 (Z_to_bv 64 3);
   CB 4 j5;
   C8 (Z_to_bv 64 18446744073709551615);
   C4 (Z_to_bv 64 11);
   CB 180 j6;
   C8 (Z_to_bv 64 0x17e870);
   CB 400 j7;
   C8 (Z_to_bv 64 0x17dca8);
   CB 120 j8;
   C8 (Z_to_bv 64 0x17de60);
   CB 8 j9;
   C2 (Z_to_bv 64 11310);
   CB 6 j10;
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   CB 64 j11;
   C8 (Z_to_bv 64 0x6bd250);
   C8 (Z_to_bv 64 0x6bd340);
   CB 24 j12;
   C8 (Z_to_bv 64 0x6bd148);
   CB 56 j13;
   C8 (Z_to_bv 64 0x6bd1c8);
   CB 24 j14;
   C8 (Z_to_bv 64 0x6bcfb0);
   CB 2064 j15].

Definition LOC0A (m : mem) : Prop := rw_cells bsegs m PJ_LOC_LO_A loc0_cellsA.
Definition LOCBA (m : mem) : Prop := exists j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15, rw_cells bsegs m PJ_LOC_LO_A (locb_cellsA j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15).
Definition pj_locA (m : mem) : Prop := LOC0A m \/ LOCBA m.

Lemma loc0_cellsA_size : cells_size loc0_cellsA = 3760%nat.
Proof. reflexivity. Qed.
Lemma locb_cellsA_size : forall j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15, cells_size (locb_cellsA j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 j14 j15) = 3760%nat.
Proof. intros. reflexivity. Qed.

Lemma pj_locA_hull : forall m, pj_locA m -> exists bs, rw_cells bsegs m PJ_LOC_LO_A [CB 3760 bs].
Proof.
  intros m [H|(j1 & j2 & j3 & j4 & j5 & j6 & j7 & j8 & j9 & j10 & j11 & j12 & j13 & j14 & j15 & H)]; [exists (repeat (Z_to_bv 8 0) 3760); exact H|].
  apply rw_cells_forget in H. rewrite locb_cellsA_size in H. exact H.
Qed.
Lemma pj_locA_agree : forall m m', pj_locA m -> agree_on (fun a => PJ_LOC_LO_A <= a < PJ_LOC_HI_A) m m' -> pj_locA m'.
Proof.
  intros m m' [H|(j1 & j2 & j3 & j4 & j5 & j6 & j7 & j8 & j9 & j10 & j11 & j12 & j13 & j14 & j15 & H)] AG; [left| right; exists j1, j2, j3, j4, j5, j6, j7, j8, j9, j10, j11, j12, j13, j14, j15];
    (eapply rw_cells_agree_nw; [exact H|]; intros a Ha; apply AG; first [rewrite loc0_cellsA_size in Ha| rewrite locb_cellsA_size in Ha];
     change (Z.of_nat 3760) with 3760 in Ha; unfold PJ_LOC_LO_A, PJ_LOC_HI_A in *; lia).
Qed.
Lemma LOCBA_agree : forall m m', LOCBA m -> agree_on (fun a => PJ_LOC_LO_A <= a < PJ_LOC_HI_A) m m' -> LOCBA m'.
Proof.
  intros m m' (j1 & j2 & j3 & j4 & j5 & j6 & j7 & j8 & j9 & j10 & j11 & j12 & j13 & j14 & j15 & H) AG. exists j1, j2, j3, j4, j5, j6, j7, j8, j9, j10, j11, j12, j13, j14, j15.
  eapply rw_cells_agree_nw; [exact H|]. intros a Ha. apply AG. rewrite locb_cellsA_size in Ha. change (Z.of_nat 3760) with 3760 in Ha.
  unfold PJ_LOC_LO_A, PJ_LOC_HI_A in *. lia.
Qed.

Definition PJ_LOCKW_A : Z := 0x6de758.
Definition lockwA (m : mem) : Prop := rw_cells bsegs m PJ_LOCKW_A [C4 (Z_to_bv 64 0)].
Lemma lockwA_agree : forall m m', lockwA m -> agree_on (fun a => PJ_LOCKW_A <= a < PJ_LOCKW_A + 4) m m' -> lockwA m'.
Proof. intros m m' H AG. eapply rw_cells_agree_nw; [exact H|]. intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. lia. Qed.

Section Lib.
Variable SJLIB : mem -> Prop.
Definition pj_libA (m : mem) : Prop := SJLIB m /\ pj_locA m /\ lockwA m.
End Lib.

Definition os_hullA (m : mem) (OS : Z) : Prop :=
  (exists bs, rw_cells bsegs m OS [CB 288 bs]) /\ bytes_at bsegs m (shad OS) (repeat z8 36).

Section Stmts.
Variable RT : rt_sig.
Variable PMc : Model -> Prop.
Notation aevt := (aevt RT PMc).
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition grow_cpsA : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (E : pjenvA) (st : sbA) (z q : Z)
         (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  pjenvA_ok E -> pa_live RT Σ E st -> SBINVA E m st ->
  2 * sa_cap st <= z <= PJ_CAPMAX (pa_len E) ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m (pa_lo E) q -> pa_lo E + PJ_GROW_STACK_A <= q -> q + 16 <= USTACK_TOP -> q mod 16 = 0 ->
  Z.of_nat (length (rt_live RT Σ)) + 1 <= LIVE_MAX -> mcost z <= rt_credit RT Σ ->
  (forall (Σ' : rts RT) (NEW : Z) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' (pa_lo E) q ->
     SBINVA E m' (sb_grownA st NEW z) -> pa_live RT Σ' E (sb_grownA st NEW z) ->
     rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_credit RT Σ - mcost z <= rt_credit RT Σ' ->
     rt_pres_fp (pa_L E) (rt_frames RT Σ) q [(pa_SB E + 64, pa_SB E + 88)] m m' ->
     aevt Σ' K (MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (pa_SB E)) (wz z) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz PJ_GROW_A) fc None m (seg_rom bsegs)).

Definition ser_cpsA (d : nat) : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (E : pjenvA) (st : sbA) (i j c c' q : Z)
         (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  fdfs_only PMc -> mat_stable PMc ->
  pjenvA_ok E -> pa_live RT Σ E st -> SBINVA E m st -> DOCREPA E m ->
  elemS (pa_T E) (pa_S E) (pa_sn E) ck_any d i j c c' -> 1 <= i -> j <= pa_n E -> 0 <= c -> c' <= pa_sn E ->
  sb_acc1A st i c ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m (pa_lo E) q -> pa_lo E + ser_needA d <= q -> q + 16 <= USTACK_TOP -> q mod 16 = 0 -> frm0 fc ->
  fcount 3 (rt_frames RT Σ) + Z.of_nat d + 1 <= FRAMES_MAX3 -> Z.of_nat (length (rt_frames RT Σ)) + 2 * Z.of_nat d + 2 <= FRAMES_TOT ->
  Z.of_nat (length (pa_L E)) + 3 <= LIVE_MAX -> 2 * (j - i) + pj_psi (pa_len E) st <= rt_credit RT Σ ->
  (forall (Σ' : rts RT) (st' : sbA) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m',
     frm0 fc' -> ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' (pa_lo E) q ->
     SBINVA E m' st' -> DOCREPA E m' -> sb_accA st' j c' -> pa_live RT Σ' E st' ->
     rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ - 2 * (j - i) - pj_psi (pa_len E) st + pj_psi (pa_len E) st' <= rt_credit RT Σ' ->
     rt_pres_fp (pa_L E) (rt_frames RT Σ) q [(pa_SB E, pa_SB E + 88)] m m' ->
     aevt Σ' K (MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc' None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (pa_SB E)) (wz (pa_DOC E)) (wz i) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz PJ_APPEND_ELEM_A) fc None m (seg_rom bsegs)).

Definition cont_cpsA (k : bool) (d : nat) : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (E : pjenvA) (st : sbA) (i e n c c' q : Z)
         (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  fdfs_only PMc -> mat_stable PMc ->
  pjenvA_ok E -> pa_live RT Σ E st -> SBINVA E m st -> DOCREPA E m ->
  ty (pa_T E) i = (if k then t_obj else t_arr) -> tnext (pa_T E i) = e + 1 -> ty (pa_T E) e = end_ty k ->
  tilesS (itemS (pa_T E) (pa_S E) (pa_sn E) k d) (i + 1) e n c c' ->
  1 <= i -> e + 1 <= pa_n E -> 0 <= c -> c' <= pa_sn E ->
  sb_acc1A st i c ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m (pa_lo E) q -> pa_lo E + cont_needA d <= q -> q + 16 <= USTACK_TOP -> q mod 16 = 0 -> frm0 fc ->
  fcount 3 (rt_frames RT Σ) + Z.of_nat d + 1 <= FRAMES_MAX3 -> Z.of_nat (length (rt_frames RT Σ)) + 2 * Z.of_nat d + 3 <= FRAMES_TOT ->
  Z.of_nat (length (pa_L E)) + 3 <= LIVE_MAX -> 2 * (e - i) + pj_psi (pa_len E) st <= rt_credit RT Σ ->
  (forall (Σ' : rts RT) (st' : sbA) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m',
     frm0 fc' -> ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' (pa_lo E) q ->
     SBINVA E m' st' -> DOCREPA E m' -> sb_accA st' (e + 1) c' -> pa_live RT Σ' E st' ->
     rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ - 2 * (e - i) - pj_psi (pa_len E) st + pj_psi (pa_len E) st' <= rt_credit RT Σ' ->
     rt_pres_fp (pa_L E) (rt_frames RT Σ) q [(pa_SB E, pa_SB E + 88)] m m' ->
     aevt Σ' K (MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc' None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (pa_SB E)) (wz (pa_DOC E)) (wz i) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz (if k then PJ_APPEND_OBJ_A else PJ_APPEND_ARR_A)) fc None m (seg_rom bsegs)).

Definition SF_EMIN : Z := -324.
Definition SF_EMAX : Z := 308.
Definition sf_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (e : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz (e mod 4294967296)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom bsegs)
    /\ SF_EMIN <= e <= SF_EMAX.
Definition sf_stmtA : Prop :=
  forall (Σ : rts RT) (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (EX lo : Z),
  ART RT Σ m -> mem_inv bsegs m -> 0 <= EX <= 2047 ->
  stk bsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp -> 0x7fff7f800000 <= lo ->
  evt bsegs (sf_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz EX) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz PJ_SF_A) fc None m (seg_rom bsegs)).

Definition tochars_cpsA : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (NB q lo : Z) (fN : Z) (kN : nat)
         (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (junk : list byte),
  fdfs_only PMc -> mat_stable PMc ->
  In (fN, kN) (rt_frames RT Σ) -> fN <= NB -> NB + 40 <= fN + fs_size kN - 8 -> NB mod 8 = 0 ->
  rw_cells bsegs m NB [CB 40 junk] -> bytes_at bsegs m (shad NB) (repeat z8 5) ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo q -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + PJ_TC_STACK_A <= q ->
  q + 16 <= USTACK_TOP -> q mod 16 = 0 -> frm0 fc ->
  Z.of_nat (length (rt_frames RT Σ)) + 1 <= FRAMES_TOT -> 1 <= rt_credit RT Σ ->
  (forall (Σ' : rts RT) (e : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' (nb : list byte),
     frm0 fc' -> ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' lo q ->
     rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_credit RT Σ - 1 <= rt_credit RT Σ' ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(NB, NB + 40)] m m' ->
     NB < e <= NB + 27 -> rw_cells bsegs m' NB [CB 40 nb] ->
     aevt Σ' K (MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz e) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc' None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz NB) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz PJ_TOCHARS_A) fc None m (seg_rom bsegs)).

Definition PJ_LOC_GET_A : Z := 0x146cb4.
Definition PJ_LOC_STACK_A : Z := 1024 + RT_STACK.
Definition loc_get_cpsA : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (P q lo : Z)
         (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (jp : list byte),
  fdfs_only PMc -> mat_stable PMc ->
  pj_locA m -> libc_nl m -> lockwA m -> io_ssp m -> rw_cells bsegs m P [CB 8 jp] -> P mod 8 = 0 ->
  (forall i, 0 <= i < 8 -> aclient (rt_live RT Σ) (rt_frames RT Σ) q (P + i)) -> (P + 8 <= PJ_LOC_LO_A \/ 0x6de75c <= P) ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo q -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + PJ_LOC_STACK_A <= q ->
  q + 16 <= USTACK_TOP -> q mod 16 = 0 ->
  (forall t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     ART RT Σ m' -> mem_inv bsegs m' -> stk bsegs m' lo q -> LOCBA m' -> rw_cells bsegs m' P [C8 (wz PJ_LOC_IMP_A)] ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(PJ_LOC_LO_A, PJ_LOC_HI_A); (P, P + 8)] m m' ->
     aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz PJ_LOC_GET_A) fc None m (seg_rom bsegs)).

Definition PJ_OS_CTOR_STACK_A : Z := 112 + PJ_LOC_STACK_A.
Variable OSFRESHA : mem -> Z -> Prop.
Variable OSUSEDA : mem -> Z -> Prop.
Variable OSIOSA : mem -> Z -> Prop.
Definition ctor_cpsA : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (OS q lo fO : Z) (kO : nat)
         (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  fdfs_only PMc -> mat_stable PMc ->
  In (fO, kO) (rt_frames RT Σ) -> fO <= OS -> OS + 288 <= fO + fs_size kO - 8 -> OS mod 16 = 0 ->
  os_hullA m OS -> pj_locA m -> libc_nl m -> lockwA m -> io_ssp m ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo q -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + PJ_OS_CTOR_STACK_A <= q ->
  q + 16 <= USTACK_TOP -> q mod 16 = 0 ->
  (forall t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     ART RT Σ m' -> mem_inv bsegs m' -> stk bsegs m' lo q -> OSFRESHA m' OS -> os_hullA m' OS -> LOCBA m' ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(PJ_LOC_LO_A, PJ_LOC_HI_A); (OS, OS + 288)] m m' ->
     aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz OS) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz PJ_OS_CTOR_A) fc None m (seg_rom bsegs)).

Definition buf_clsA (Σ : rts RT) (fO : Z) (kO : nat) (BUF CAP : Z) : Prop :=
  (exists p k, In (p, k) (rt_live RT Σ) /\ p <= BUF /\ BUF + CAP <= p + k) \/ (fO <= BUF /\ BUF + CAP <= fO + fs_size kO - 8).
Lemma buf_clsA_rng : forall Σ fO kO BUF CAP N, buf_clsA Σ fO kO BUF CAP -> In (fO, kO) (rt_frames RT Σ) -> 0 <= N <= CAP -> rng_class RT Σ BUF N.
Proof.
  intros Σ fO kO BUF CAP N [(p & k & Hin & H1 & H2)|(H1 & H2)] INF HN; [left; exists p, k; split; [exact Hin| lia]|].
  right; left. exists fO, kO. split; [exact INF| lia].
Qed.
Lemma buf_clsA_aclient : forall Σ fO kO BUF CAP sp i, buf_clsA Σ fO kO BUF CAP -> In (fO, kO) (rt_frames RT Σ) -> 0 <= i < CAP ->
  aclient (rt_live RT Σ) (rt_frames RT Σ) sp (BUF + i).
Proof.
  intros Σ fO kO BUF CAP sp i [(p & k & Hin & H1 & H2)|(H1 & H2)] INF Hi; [right; right; left; exists p, k; split; [exact Hin| lia]|].
  right; right; right; left. exists fO, kO. split; [exact INF| lia].
Qed.
Definition PJ_OS_PUT_STACK_A : Z := 192 + 16 + 192 + 16 + 64 + 16 + RT_STACK.
Definition put_cpsA : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (OS BUF N CAP q lo fO : Z) (kO : nat)
         (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (bs : list byte),
  fdfs_only PMc -> mat_stable PMc ->
  In (fO, kO) (rt_frames RT Σ) -> fO <= OS -> OS + 288 <= fO + fs_size kO - 8 -> OS mod 16 = 0 ->
  OSFRESHA m OS -> os_hullA m OS -> LOCBA m ->
  rw_cells bsegs m BUF [CB (Z.to_nat CAP) bs] -> 0 <= N <= CAP -> 0 < BUF -> BUF + CAP <= lo -> acc bsegs m BUF N -> buf_clsA Σ fO kO BUF CAP ->
  (BUF + CAP <= OS \/ OS + 288 <= BUF) ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo q -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + PJ_OS_PUT_STACK_A <= q ->
  q + 16 <= USTACK_TOP -> q mod 16 = 0 ->
  Z.of_nat (length (rt_frames RT Σ)) + 2 <= FRAMES_TOT -> 2 <= rt_credit RT Σ ->
  (forall (Σ' : rts RT) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' lo q -> OSUSEDA m' OS -> os_hullA m' OS ->
     rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_credit RT Σ - 2 <= rt_credit RT Σ' ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(OS, OS + 288)] m m' ->
     aevt Σ' K (MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (OS + 128)) (wz BUF) (wz N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz PJ_OSPUT_A) fc None m (seg_rom bsegs)).

Definition PJ_IOS_DTOR_STACK_A : Z := 64 + RT_STACK.
Definition locdtor_evtA : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (P : Z),
  rw_cells bsegs m P [C8 (wz PJ_LOC_IMP_A)] -> LOCBA m -> mem_inv bsegs m ->
  evt bsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz PJ_LOC_DTOR_A) fc None m (seg_rom bsegs)).
Definition iosdtor_cpsA : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (OS q lo fO : Z) (kO : nat)
         (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  fdfs_only PMc -> mat_stable PMc ->
  In (fO, kO) (rt_frames RT Σ) -> fO <= OS -> OS + 288 <= fO + fs_size kO - 8 -> OS mod 16 = 0 ->
  OSIOSA m OS -> os_hullA m OS -> LOCBA m -> unwind_ok ra s0 (wz q) ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo q -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + PJ_IOS_DTOR_STACK_A <= q ->
  q + 16 <= USTACK_TOP -> q mod 16 = 0 ->
  (forall t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     ART RT Σ m' -> mem_inv bsegs m' -> stk bsegs m' lo q -> os_hullA m' OS ->
     rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(OS + 136, OS + 144)] m m' ->
     aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (OS + 136)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz PJ_IOS_DTOR_A) fc None m (seg_rom bsegs)).

End Stmts.
