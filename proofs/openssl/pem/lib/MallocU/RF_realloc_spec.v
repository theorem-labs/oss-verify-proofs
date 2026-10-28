(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OssFuzzTheorems.openssl.pem.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import F_malloc_free MallocBlocks MallocHINV MallocFacts_B Malloc_iface MallocReframe MallocFacts_R.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog MI_Inv MI_Ext MI_Geom MI_WFree.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import F_free_K F_free F_free_spec.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMallocKit_A RMalloc_iface RMalloc_ifaceP RF_malloc_top RF_realloc_frame RF_realloc_rep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require MallocFacts_inv.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require MallocFacts_inv3.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition RREALLOC_SYM : Z := 0x2b270c.     (* [comment removed for export] *)
Definition RREALLOC_MID : Z := 0x2b2aa8.     (* [comment removed for export] *)
Definition RREALLOC_TAIL : Z := 0x2b2ad0.    (* [comment removed for export] *)

Lemma strip_ctrl_eq st st' : ctrl_eq st st' -> strip st' = strip st.
Proof. intros []. unfold strip. congruence. Qed.

(* [comment removed for export] *)
Definition rrealloc_grow_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (A n0 n lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 RREALLOC_MID) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 A) (Z_to_bv 64 n)
                  a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (A + n0)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 rmalloc_entry) fc None m' (seg_rom usegs)
    /\ rw_cells usegs m' (bv_unsigned sp + -64) (rr_frame ra s0 s1 s2 s3 s4 s5 s6)
    /\ stk usegs m' lo (bv_unsigned sp + -64)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ RHEAP s LB m'.

Definition rrealloc_inplace_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' junk,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv]
    /\ rauxv_ok m' B
    /\ rheap_pres ((p, A, n) :: lb_remove p LB) (bv_unsigned sp) m m'
    /\ RHEAP s ((p, A, n) :: lb_remove p LB) m'
    /\ rw_cells usegs m' A [CB (Z.to_nat n) junk].

Definition rrealloc_prefix_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (p : bptr) (A n0 n lo B : Z) (errv : word),
  RHEAP s LB m -> In (p, A, n0) LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 0 <= n < MMAP_THRESHOLD ->
  evt usegs (fun ms' => rrealloc_grow_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB A n0 n lo m ms'
                        \/ rrealloc_inplace_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A n lo B errv m ms')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RREALLOC_SYM) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
Lemma rheap_pres_reframe : forall st LB0 (blk : block) g i r m m' lo sp Slo Flo P E n LBc,
  CINV st LB0 -> rmrep st m -> AREACH_from ref_reserved st LB0 -> In blk LB0 ->
  s_slots st !! blk_slot blk = Some (g, i) -> s_regions st !! fst (blk_slot blk) = Some r -> r_kind r = RKGroup ->
  alloc_ceiling <= lo -> lo <= Slo -> Slo <= sp ->
  r_base r + sstart (MR st g) i - 3 <= Flo -> r_base r <= Flo -> E <= r_base r + sstart (MR st g) (i + 1) - 4 ->
  E <= r_base r + round_up_pg (r_len r) -> P + n <= E ->
  rpres_except (fun x => Slo <= x < sp \/ (Flo <= x < E /\ ~ (P <= x < P + n))) m m' ->
  (forall b, In b LBc -> b = (blk_id blk, P, n) \/ In b (lbrm LB0 blk)) ->
  rheap_pres LBc sp m m'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st LB0 blk g i r m m' lo sp Slo Flo P E n LBc C MRm AR Hin Hs Hr Kr LO SLO SLS PLO PLO2 EHI ERG PNE PE HLB a Ha CA.
  apply PE; [exact Ha|].
  pose proof MRm as (WF & _). pose proof WF as (_ & WR & DJ & _).
  destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & RF).
  pose proof (rregion_addr_facts st m _ r MRm Hr) as (_ & _ & _ & RIMG).
  destruct (areach_blk_span st LB0 blk g i AR Hin Hs) as (r' & Hr' & _ & SPANB). rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
  unfold ceil_window in *.
  intros [FRM|[INB NB]].
  - (* [comment removed for export] *)
    destruct CA as [CA|[[CA NS]|(blk' & Hb' & Hab)]]; [lia| lia|].
    destruct (HLB _ Hb') as [->|Hb0]; cbn [blk_addr blk_size fst snd] in Hab; [lia|].
    unfold lbrm in Hb0. apply In_filter_iff in Hb0. destruct Hb0 as [HinL _].
    destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' HinL) as [(rg & Hrg & Krg & A16 & AEND & AL & UNK) _ _].
    destruct (WR _ _ Hrg) as (_ & _ & _ & RGC & _). lia.
  - (* [comment removed for export] *)
    destruct CA as [CA|[[CA NS]|(blk' & Hb' & Hab)]].
    + lia.
    + assert (0 < round_up_pg (r_len r)) by lia. specialize (RIMG H). lia.
    + destruct (HLB _ Hb') as [->|Hb0]; cbn [blk_addr blk_size fst snd] in Hab; [apply NB; exact Hab|].
      unfold lbrm in Hb0. apply In_filter_iff in Hb0. destruct Hb0 as [HinL NEQ].
      assert (NES : blk_slot blk' <> blk_slot blk).
      { intros E0. rewrite E0, aptr_eqb_refl in NEQ. cbn in NEQ. first [exact NEQ | exact (NEQ I) | discriminate NEQ]. }
      destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' HinL) as [(rg & Hrg & Krg & A16 & AEND & AL & UNK) _ _].
      destruct (N.eq_dec (fst (blk_slot blk')) (fst (blk_slot blk))) as [EF|NEF].
      * destruct (SPANB blk' HinL NES EF); lia.
      * pose proof (lr_lo_group rg Krg). pose proof (lr_lo_group r Kr). destruct (DJ _ _ _ _ Hrg Hr NEF); lia.
Qed.

Theorem rrealloc_prefix_spec : rrealloc_prefix_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n0 n lo B errv
         HP Hin AV HB ST LO SLO ERR MI TP A0 A1 N.
  pose proof HP as HP0.
  destruct HP as (st & LB0 & PERM & Hst & MRm & [BL AR]).
  assert (Hin0 : In (p, A, n0) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]).
  pose proof (MallocFacts_inv3.areach_cinv_proof _ _ AR) as C.
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) (p, A, n0) Hin0) as BK.
  destruct BK as [(g0 & i0 & b0 & _ & _ & _ & _ & _ & (off & O0 & OA & _)) _ _].
  destruct (MallocFacts_inv.areach_blk_facts st LB0 (p, A, n0) off AR Hin0 O0 OA) as (g & bg & i & ai & a & ar & ka & BF & S20 & NOGRP).
  cbn [blk_addr blk_slot blk_size fst snd] in OA, BF.
  set (c := fst p) in *.
  (* [comment removed for export] *)
  assert (INI : c_init_done (ctx st) <> 0).
  { destruct (MallocFacts_inv.areach_inv _ _ _ AR) as (L & LS & BL' & (IR & IA & _) & _).
    destruct (MI_Inv.ia_secret _ IA) as [_ [(_ & _ & E0)|(E1 & _)]]; [| unfold ctx; lia].
    exfalso. destruct (bf_area _ _ _ _ _ _ _ _ _ _ _ BF) as (Ha & _). rewrite E0 in Ha. rewrite lookup_empty in Ha. discriminate. }
  destruct (rrb_geo st LB0 c off n0 g bg i ai a ar ka C BF) as (r & Hr & Kr & B0 & S16 & SI0 & Hi & OFF & N0 & SPAN & FIT & O16 & RES0 & Ec & PM & Q1 & Q2).
  set (stride := get_stride (get_meta_rec st g)) in *.
  assert (ESS : sstart (MR st g) i = snd bg + 16 + stride * i).
  { unfold sstart, gbase, MR. rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF). cbn [default from_option id snd]. unfold UNIT. reflexivity. }
  assert (Hrc : s_regions st !! fst c = Some r) by (rewrite Ec; exact Hr).
  assert (EA : A = r_base r + (snd bg + 16 + stride * i + 16 * off)).
  { rewrite OA, (conc_region' st c r Hrc), Ec. cbn [snd]. unfold UNIT. lia. }
  pose proof MRm as (WF & _). pose proof WF as (_ & WR & _).
  destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & _).
  pose proof (rregion_addr_facts st m _ r MRm Hr) as (_ & _ & _ & RIMG).
  pose proof (round_up_pg_ge (r_len r)) as RUP.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (AR64 : 0 <= A < 2^64) by (unfold ceil_window in *; clear - EA B0 SI0 OFF SPAN O16 RB0 RBC CEIL_RANGE__; lia).
  assert (S20' : m_sizeclass (get_meta_rec st g) < 48 -> stride < 2 ^ 20).
  { intros X. specialize (S20 X). unfold MR in S20. fold stride in S20.
    pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as [I0 I1]. unfold MR in I1. clear - S20 S16 I0 I1. nia. }
  eapply evt_mono.
  { unfold RREALLOC_SYM.
    eapply (rrealloc_pre_rep st LB0 c off n0 g bg i ai a ar ka C BF INI
              ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo r n);
      [exact MRm| exact MI| exact Hr| | exact A1| exact N| exact ST| exact LO| exact SLO| exact S20'|].
    - rewrite A0, unsigned_lit by lia. exact EA.
    - intros b' gh Hgh Hf. specialize (NOGRP b' gh Hgh Hf). rewrite sstart_succ, ESS in NOGRP. fold stride in NOGRP. exact NOGRP. }
  fold stride. intros ms' [GROW|INP].
  - (* [comment removed for export] *)
    left. destruct GROW as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m1 & -> & FR & ST1 & MU & WM & MI1).
    unfold rrealloc_grow_post. exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, m1.
    split. { rewrite A0, <- EA. reflexivity. }
    split; [exact FR|]. split; [exact ST1|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|].
    eapply (RHEAP_frame_proof s LB m m1 _ HP0 MU WM). constructor; [| constructor]. left. cbn [fst]. lia.
  - (* [comment removed for export] *)
    right. destruct INP as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m1 & -> & MR2 & TK2 & MI2 & ST2 & PE & FIT' & ST20).
    rewrite <- EA in PE.
    replace (r_base r + (snd bg + 16 + stride * i + stride - 4)) with (A + (stride - 4 - 16 * off)) in PE by lia.
    set (E := A + (stride - 4 - 16 * off)) in *.
    set (st' := rf_setsize_st st c g bg i off n) in *.
    assert (CE : ctrl_eq st st') by (apply rf_full_ctrl).
    assert (NIMG : forall x, A - 3 <= x < E -> r_base r <= x < r_base r + round_up_pg (r_len r)) by (intros x Hx; unfold E in Hx; lia).
    assert (RIMG' : r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x353000 <= r_base r) by (apply RIMG; lia).
    pose proof (ruser_chunk st' m1 (aadd c (UNIT * off)) r n MR2 ltac:(rewrite (ce_regions _ _ CE); exact Hrc) Kr
                  ltac:(rewrite Ec; cbn [aadd snd]; unfold UNIT; lia) ltac:(rewrite Ec; cbn [aadd snd]; unfold UNIT; lia) ltac:(lia)) as (junk & UC).
    assert (ECONC : conc st' (aadd c (UNIT * off)) = A).
    { unfold conc, get_region. rewrite (ce_regions _ _ CE). cbn [aadd fst snd]. rewrite Hrc, EA, Ec. cbn [snd]. unfold UNIT. lia. }
    rewrite ECONC in UC.
    unfold rrealloc_inplace_post. exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, m1, junk.
    split. { rewrite A0. reflexivity. }
    split; [exact MI2|]. split; [exact ST2|].
    split. { eapply rpres_except_rw_cells; [exact PE| exact ERR|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
             assert (ETP : errno_addr tp = 3344580) by (unfold errno_addr; rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
             rewrite ETP. intros x Hx [X|[X _]]; [unfold ceil_window in *; lia| specialize (NIMG x X); lia]. }
    split. { eapply rauxv_ok_pres; [exact AV| exact PE| |].
             - intros x Hx [X|[X _]]; [lia| specialize (NIMG x X); unfold ceil_window in *; lia].
             - unfold RAUXV_CELL. intros x Hx [X|[X _]]; [unfold ceil_window in *; lia| specialize (NIMG x X); lia]. }
    pose proof (lb_remove_lbrm LB p A n0 (NoDup_map_perm blk_slot LB0 LB PERM (ci_nodup _ _ C)) Hin) as ELB.
    split.
    { eapply (rheap_pres_reframe st LB0 (p, A, n0) g i r m m1 lo (bv_unsigned sp) (bv_unsigned sp - 64) (A - 3) A E n); try eassumption.
      - exact (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF).
      - lia.
      - rewrite ESS. fold stride. lia.
      - lia.
      - rewrite sstart_succ, ESS. unfold MR. fold stride. unfold E. lia.
      - unfold E. lia.
      - unfold E. lia.
      - intros b [<-|Hb]; [left; reflexivity| right]. rewrite ELB in Hb. eapply In_lbrm_perm; [apply Permutation_sym; exact PERM| exact Hb]. }
    split; [| exact UC].
    exists st', ((p, A, n) :: lbrm LB0 (p, A, n0)).
    split. { rewrite ELB. apply perm_skip. apply lbrm_perm. exact PERM. }
    split. { rewrite (strip_ctrl_eq _ _ CE). exact Hst. }
    split; [exact MR2|]. split.
    + unfold brk_link in *. unfold ctx in *. rewrite (ce_ctx _ _ CE).
      destruct (c_brk (s_ctx st)) as [| |brid boff]; [exact I| exact I|]. rewrite BL. unfold conc, get_region. rewrite (ce_regions _ _ CE). reflexivity.
    + pose proof (areach_reframe st LB0 (p, A, n0) off n st' AR Hin0) as ARF. cbn [blk_id blk_slot blk_addr blk_size fst snd] in ARF. fold c in ARF.
      rewrite <- OA in ARF. apply ARF.
      replace ((A - conc st c) / UNIT) with off by (rewrite OA; replace (conc st c + UNIT * off - conc st c) with (off * UNIT) by lia; rewrite Z.div_mul by (unfold UNIT; lia); reflexivity).
      apply (reframe_ok_setsize st c g bg i off n0 n (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF)).
      * exists ai. exact (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF).
      * lia.
      * unfold MR. fold stride. unfold UNIT, IB. lia.
      * unfold MR. fold stride. unfold IB. lia.
Qed.
End WithCeiling0.
