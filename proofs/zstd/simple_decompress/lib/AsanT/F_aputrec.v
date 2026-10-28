(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MM_syscalls.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanCtrlProps.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase ABytes AKit AKit2 AKitQ ARep ARepKit ARepFrame
     F_apoison APoisonR_iface F_apoisonz F_aalloc3 F_asecdealloc F_arecsec AFrameD.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.
(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6443008 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6443008 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

(* [comment removed for export] *)
Abbreviation PUTREC_STACK := 704.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition putrec_W (sp t mb ms PA idx last : Z) : list (Z * Z) :=
  [(sp - PUTREC_STACK, sp); (t + 2800, t + 3168);
   (0xcc710, 0xcc719); (0xcc728, 0xcc738); (0xcc940, 0xcc944); (0xcc958, 0xcc968);
   (PA + 8 * idx, PA + 8 * idx + 8); (last + 24, last + 32); (mb, mb + ms); (shad mb, shad mb + shlen ms)]%Z.

Definition putrec_post (sp : word) (t mb ms PA nres nsec idx last lo : Z) (bases : list Z) (lw1 lw2 : word)
    (m m' : amem) : Prop :=
     munch (putrec_W (bv_unsigned sp) t mb ms PA idx last) m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
  /\ rw_cells bsegs m' 0xcc708 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 (nsec - 1))]
  /\ rw_cells bsegs m' 0xcc718 [C1 (Z_to_bv 8 0)]
  /\ junk_at m' 0xcc720 32
  /\ rw_cells bsegs m' 0xcc940 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ junk_at m' 0xcc958 16
  /\ u64arr bsegs m' PA (upd (map (Z_to_bv 64) bases) (Z.to_nat idx) (Z_to_bv 64 last))
  /\ (idx <> nsec - 1 -> rw_cells bsegs m' last [C8 (Z_to_bv 64 last); C8 lw1; C8 lw2; C8 (Z_to_bv 64 idx)])
  /\ (exists sj', u64arr bsegs m' (t + 2800) sj' /\ length sj' = 46%nat)
  /\ rw_cells bsegs m' (shad mb) [CB (Z.to_nat (shlen ms)) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen ms)))].

Lemma put_passthru_spec : forall RNG {R} (k : astate -> AM R) (st : astate) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (mb ms n idx PA nres nsec last ctx t SB lo nb fst0 lst qb : Z) (bases : list Z)
    (hsz lw1 lw2 : word) (srt hst hb1 : byte) (hctx : word) (sj : list word) (shj : list byte),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PUTREC_STACK -> bv_unsigned sp <= 2^47 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 0xcc970 -> a1 = Z_to_bv 64 (t + 80) -> a4 = Z_to_bv 64 (mb + 6128) -> a5 = Z_to_bv 64 n ->
  (* [comment removed for export] *)
  rw_cells bsegs m 0xcc9b0 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] -> Q_MAX < n ->
  rw_cells bsegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] -> 0 <= qb <= Q_CACHE ->
  (last + 32 <= t \/ t + 4096 <= last) -> last + 32 <= ATOP ->
  (* [comment removed for export] *)
  rw_cells bsegs m 0xcc6b8 [C8 (Z_to_bv 64 SB)] -> (mb + ms <= SB \/ SB + K_SPACE_SIZE + K_SPACE_EXTRA <= mb) -> 0 <= SB < 2^47 ->
  rw_cells bsegs m 0xcc6d8 [C8 (Z_to_bv 64 4096)] -> rw_cells bsegs m 0xcc6e0 [C8 (Z_to_bv 64 PA)] ->
  rw_cells bsegs m 0xcc708 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells bsegs m 0xcc718 [C1 srt] -> junk_at m 0xcc720 32 ->
  rw_cells bsegs m 0xcc940 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  junk_at m 0xcc958 16 ->
  (* [comment removed for export] *)
  rw_cells bsegs m 0xcf560 [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m 0xcf564 [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> t + 4096 <= ATOP ->
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->
  (* [comment removed for export] *)
  poison_cells m -> premap_cells m -> arelro0 m ->
  (* [comment removed for export] *)
  u64arr bsegs m PA (map (Z_to_bv 64) bases) -> Z.of_nat (length bases) = nsec ->
  0 <= idx < nsec -> nsec <= nres -> nth_error bases (Z.to_nat idx) = Some mb -> nth_error bases (Z.to_nat (nsec - 1)) = Some last ->
  ablk PA (PA + 8388608) -> PA + 8 * nres <= ATOP ->
  (* [comment removed for export] *)
  rw_cells bsegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 hsz; C8 (Z_to_bv 64 idx)] ->
  rw_cells bsegs m (mb + 6128) [C1 hst; C1 hb1; C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 hctx] -> 0 <= n < 2^32 ->
  Forall (fun ch => 0 <= ch < 2^64 /\ (ch <= mb + 6128 -> ch <= mb)) bases ->
  mb mod 4096 = 0 -> ablk mb (mb + ms) -> 8192 <= ms -> ms mod 4096 = 0 -> mb + ms <= ATOP ->
  rw_cells bsegs m (shad mb) [CB (Z.to_nat (shlen ms)) shj] ->
  (idx <> nsec - 1 ->
      rw_cells bsegs m last [C8 (Z_to_bv 64 last); C8 lw1; C8 lw2; C8 (Z_to_bv 64 (nsec - 1))]
   /\ ablk last (last + 32) /\ last + 32 <= ATOP /\ (last + 32 <= mb \/ mb + ms <= last)
   /\ (last + 32 <= t \/ t + 4096 <= last) /\ (last + 32 <= ctx \/ ctx + 4096 <= last) /\ (last + 32 <= PA \/ PA + 8 * nres <= last)) ->
  (* [comment removed for export] *)
  (mb + ms <= t \/ t + 4096 <= mb) -> (mb + ms <= ctx \/ ctx + 4096 <= mb) -> (mb + ms <= PA \/ PA + 8 * nres <= mb) ->
  (PA + 8 * nres <= t \/ t + 4096 <= PA) -> (PA + 8 * nres <= ctx \/ ctx + 4096 <= PA) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  4096 <= bv_unsigned ra ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG PA (8 * nres) ->
  rng RNG mb ms -> rng RNG (shad mb) (shlen ms) -> (idx <> nsec - 1 -> rng RNG last 32) ->
  AIMG_HI <= ctx -> iclr t 4096 -> nres <= 1048576 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall RNG1 rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      fp_le RNG RNG1 -> fstepS (NMunmap mb ms) rsp RNG1 RNG' ->
      putrec_post sp t mb ms PA nres nsec idx last lo bases lw1 lw2 m m' ->
      rw_cells bsegs m' (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
      implS bsegs RNG' (aembed ATOP (k (set_nsec (a_nsec st - 1) st))) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (aembed ATOP (large_dealloc st mb ms k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x37c08) fc None m (seg_rom bsegs)).
Proof.
  intros until shj.
  intros ST CEIL LO SPHI MI TP -> -> -> -> QCELL NBIG TC QBLE LDT0 LCE0 ISB DSP SB0 I64 I72 NSC SRT JST MTX JGL TI TK T88 TSD CT CX0 CX1 T0 T1 STATS LSJ PC PRM RR
         ARR LEN IDX NSR NTHI NTHL PA0 PA1 HDR ACH NR BR MAL MLO MS8K MSAL MCE SH LHDR DMT DMC DMP DPT DPC DCT RA
         RIMG RSTK RCTX RT RPA RMB RSH RLH CXI TIC NRB KONT. band_lin.   (* [comment removed for export] *)
  pose proof (ablk_lin _ _ MLO) as (ML1 & ML2 & ML3 & ML4). unfold AIMG_HI in ML1. band_int T0. band_int CX0. band_int MLO.   (* [comment removed for export] *)
  unfold ATP88, ATSD, K_SPACE_SIZE, K_SPACE_EXTRA in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  (* [comment removed for export] *)
  box ISB. box I64. box I72. box NSC. box SRT. box JST. box MTX. box JGL. box TI. box TK. box T88. box TSD. box CT. box STATS. box ARR. box HDR. box ACH. box SH.
  box LHDR. box TC. box QCELL. box DMT. box DMC. box DMP. box DPT. box DPC. box DCT. box LDT0.
  rewrite large_dealloc_unfold at 1 || idtac.
  iprefix.
  carve_frame 80%nat ST.
  do 9 step.                                                   (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  carry QCELL MU WM ltac:(clear -CEIL LO SPR; lia).
  step. step.                                                  (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  step. step. if_cases K1; zify_cond K1.                       (* [comment removed for export] *)
  { exfalso. unfold Q_MAX in *. clear -K1 NBIG NR. rewrite ?Z.mod_small in K1 by lia. lia. }
  carry ISB MU WM ltac:(clear -CEIL LO SPR; lia).
  step. step.                                                  (* [comment removed for export] *)
  destruct DSP as [DLO | DHI];
  [ step; if_cases K2; zify_cond K2; [ | exfalso; clear -K2 DLO MS8K SB0 MLO ML1 ML2 ML3 KAMLO KBMLO KEMLO KCMLO KDMLO; rewrite ?Z.mod_small in K2 by lia; lia ]
  | step; if_cases K2; zify_cond K2;
    [ exfalso; clear -K2 DHI SB0 MLO ML1 ML2 ML3 KAMLO KBMLO KEMLO KCMLO KDMLO MCE; rewrite ?Z.mod_small in K2 by lia; lia
    | step; zstep; zstep; step; if_cases K3; zify_cond K3; [ | exfalso; clear -K3 DHI SB0 MLO ML1 ML2 ML3 KAMLO KBMLO KEMLO KCMLO KDMLO MCE; rewrite ?Z.mod_small in K3 by lia; lia ] ] ].
  all: step; step.                                             (* [comment removed for export] *)
  all: step.                                                   (* [comment removed for export] *)
  all: apply evtF_done.
  (* [comment removed for export] *)
  all: carry I64 MU WM ltac:(clear -CEIL LO SPR; lia); carry I72 MU WM ltac:(clear -CEIL LO SPR; lia); carry NSC MU WM ltac:(clear -CEIL LO SPR; lia).
  all: carry SRT MU WM ltac:(clear -CEIL LO SPR; lia); carry MTX MU WM ltac:(clear -CEIL LO SPR; lia).
  all: unbox JST; lazymatch type of MU with munch ?W0 ?me ?mm => eapply (junk_frame W0 me mm) in JST; [| exact MU | exact WM | intros _; cbn; clear -CEIL LO SPR; lia] end.
  all: unbox JGL; lazymatch type of MU with munch ?W0 ?me ?mm => eapply (junk_frame W0 me mm) in JGL; [| exact MU | exact WM | intros _; cbn; clear -CEIL LO SPR; lia] end.
  all: carry TI MU WM ltac:(clear -CEIL LO SPR; lia); carry TK MU WM ltac:(clear -CEIL LO SPR; lia); carry T88 MU WM ltac:(clear -CEIL LO SPR; lia); carry TSD MU WM ltac:(clear -CEIL LO SPR; lia).
  all: carry CT MU WM ltac:(clear -CEIL LO SPR CX1; lia).
  all: carry STATS MU WM ltac:(rewrite LSJ; clear -CEIL LO SPR T1; lia).
  all: carry ARR MU WM ltac:(rewrite ?length_map; clear -CEIL LO SPR PA1 LEN NSR; lia).
  all: carry HDR MU WM ltac:(clear -CEIL LO SPR MCE MS8K; lia).
  all: carry ACH MU WM ltac:(clear -CEIL LO SPR MCE MS8K; lia).
  all: assert (SHR : 2148256256 <= shad mb /\ shad mb + shlen ms <= 0x10007fff8000 /\ 512 <= shlen ms)   (* [comment removed for export] *)
         by (unfold shad, shlen, ASHOFF; rewrite !Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear -MLO ML1 ML2 ML3 KAMLO KBMLO KEMLO KCMLO KDMLO MCE MS8K; Z.div_mod_to_equations; lia).
  all: unbox SH; lazymatch type of MU with munch ?Wc ?me ?mk =>
         apply (rw_cells_transport bsegs Wc me mk) in SH;
         [| exact MU | exact WM | cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear -SHR; lia); clear -SHR CEIL LO SPR; lia] end.
  all: lazymatch type of MU with munch ?Wc ?me ?mk =>
         pose proof (poison_cells_frameD Wc me mk PC MU) as PCk; pose proof (premap_cells_frameD Wc me mk PRM MU) as PRMk;
         pose proof (arelro0_munch Wc me mk RR MU) as RRk end.
  all: cbn [disjoint_from] in PCk, PRMk.
  all: do 7 (specialize (PCk ltac:(clear -CEIL LO SPR; lia))).
  all: do 7 (specialize (PRMk ltac:(clear -CEIL LO SPR; lia))).
  all: specialize (RRk ltac:(unfold ARELRO_LO, ARELRO_HI; repeat (apply Forall_cons; [cbn; clear -CEIL LO SPR; lia|]); apply Forall_nil)).
  all: unbox LHDR.
  all: lazymatch goal with |- implF _ _ _ _ _ _ (MS _ _ _ _ _ ?mk _) =>
         assert (LHDRk : idx <> nsec - 1 ->
            rw_cells bsegs mk last [C8 (Z_to_bv 64 last); C8 lw1; C8 lw2; C8 (Z_to_bv 64 (nsec - 1))]
            /\ ablk last (last + 32) /\ last + 32 <= ATOP /\ (last + 32 <= mb \/ mb + ms <= last)
            /\ (last + 32 <= t \/ t + 4096 <= last) /\ (last + 32 <= ctx \/ ctx + 4096 <= last) /\ (last + 32 <= PA \/ PA + 8 * nres <= last))
         by (intros NE; destruct (LHDR NE) as (LH & L1 & L2 & L3 & L4 & L5 & L6); split; [| split; [exact L1| split; [exact L2| split; [exact L3| split; [exact L4| split; [exact L5| exact L6]]]]]];
             eapply cells_frame; [exact LH | exact MU | exact WM | cbn; clear -CEIL LO SPR L1 L2; lia]) end.
  all: clear LHDR.
  all: eapply (recycle_sec_spec RNG k st Q) with (mb := mb) (ms := ms) (n := n) (idx := idx) (PA := PA) (nres := nres) (nsec := nsec) (last := last)
         (ctx := ctx) (t := t) (SB := SB) (CBA := bv_unsigned sp + -80) (lo := lo) (bases := bases) (lw1 := lw1) (lw2 := lw2) (sj := sj) (hsz := hsz) (srt := srt)
         (hst := hst) (hb1 := hb1) (hctx := hctx) (shj := shj).
  all: lazymatch goal with
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -CEIL LO LO0 SPR; lia); exact ST
       | |- mem_inv _ _ => exact MI
       | |- poison_cells _ => exact PCk
       | |- premap_cells _ => exact PRMk
       | |- arelro0 _ => exact RRk
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- rw_cells _ _ (_ + 152) _ => exact CT
       | |- rw_cells _ _ ATSD _ => exact TSD
       | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _] => exact HDR
       | |- rw_cells _ _ _ [C8 _; C8 _] => exact NSC
       | |- rw_cells _ _ _ [CB _ _] => exact SH
       | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact ACH
       | |- rw_cells _ _ _ _ => first [eassumption | exact SRT | exact ISB]
       | |- junk_at _ _ 32 => exact JST
       | |- junk_at _ _ 16 => exact JGL
       | |- u64arr _ _ _ (map _ _) => exact ARR
       | |- u64arr _ _ _ _ => exact STATS
       | |- length _ = _ => exact LSJ
       | |- @eq (option Z) _ _ => assumption
       | |- @eq Z _ _ => assumption
       | |- Forall _ _ => exact BR
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ 4096 => assumption
       | |- rng _ _ (8 * _) => exact RPA
       | |- rng _ (shad _) _ => exact RSH
       | |- rng _ _ (_ - _) => rewrite unsigned_lit by (clear -CEIL LO LO0 SPR; lia); eapply rng_sub'; [exact RSTK|]; clear -CEIL LO LO0 SPR; lia
       | |- rng _ _ _ => exact RMB
       | |- _ -> rng _ _ _ => exact RLH
       | |- _ -> _ /\ _ => exact LHDRk
       | |- _ \/ _ => first [left; exact DLO | right; exact DHI | unboxed DMT | unboxed DMC | unboxed DMP | unboxed DPT | unboxed DPC | unboxed DCT]
       | |- forall _, _ => idtac
       | |- _ => try assumption; atop_facts; rewrite ?unsigned_lit by (clear -CEIL LO LO0 SPR; lia); clear -CEIL LO LO0 SPR SPHI MLO ML1 ML2 ML3 KAMLO KBMLO KEMLO KCMLO KDMLO MS8K MSAL MCE CX0 KACX0 KBCX0 KCCX0 CX1 T0 KAT0 KBT0 KCT0 TIC T1 PA0 PA1 IDX NSR LEN RA MAL NR SB0; lia
       end.
  (* [comment removed for export] *)
  all: intros RNG1 rsp RNG' m' u0 u1 u2 b0 b1' b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 LE1 HF PP.
  all: pose proof PP as (MUd & MId & STd & NSCd & SRTd & JSTd & MTXd & JGLd & ARRd & LHDRd & STATSd & SHZd).
  all: rewrite ?unsigned_lit in MUd, STd by (clear -CEIL LO LO0 SPR; lia).
  all: unfold sdealloc_W in MUd.
  all: replace (ret_pc (Z_to_bv 64 228552)) with (Z_to_bv 64 228552 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  (* [comment removed for export] *)
  all: carry TC MU WM ltac:(clear -CEIL LO SPR T1; lia).
  all: pose proof (cells_frameD _ _ _ _ _ TC MUd ltac:(cbn; ub DMT; ub DPT; ub LDT0; clear -CEIL LO SPR T0 KAT0 KBT0 KCT0 TIC T1 MS8K IDX NSR PA0 SHR Y Y0 Y1; lia)) as TCd.
  (* [comment removed for export] *)
  all: lazymatch goal with FRq : rw_cells bsegs _ (bv_unsigned _ + -80) _ |- _ =>
         pose proof (cells_frameD _ _ _ _ _ FRq MUd ltac:(cbn; clear -CEIL LO SPR T1 MCE MS8K PA1 IDX NSR SHR LCE0; lia)) as FRd; clear FRq end.
  all: pose proof (fp_le_trans _ _ _ LE1 (fstepS_le _ _ _ _ HF)) as LE.
  all: pose proof (rng_fp_le _ _ _ _ LE RSTK) as RSTK'; pose proof (rng_fp_le _ _ _ _ LE RT) as RT'; pose proof (rng_fp_le _ _ _ _ LE RIMG) as RIMG'.
  all: clear RSTK RT RIMG RCTX RPA RMB RSH RLH.
  all: iprefix.
  all: step.                                                   (* [comment removed for export] *)
  all: step; if_cases K5; zify_cond K5; [ | exfalso; unfold Q_CACHE in *; clear -K5 QBLE; rewrite ?Z.mod_small in K5 by lia; lia ].   (* [comment removed for export] *)
  all: do 9 step.                                              (* [comment removed for export] *)
  all: release_frame FRd STd (bv_unsigned sp).
  all: step.                                                   (* [comment removed for export] *)
  all: apply evtF_done.
  all: eapply (KONT RNG1 rsp RNG' m'); [exact LE1 | exact HF | | exact TCd].
  all: unfold putrec_post, putrec_W.
  all: split; [| split; [exact MId| split; [exact STd| exact (proj2 (proj2 (proj2 PP)))]]].
  all: eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MUd]];
       let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia.
Qed.
End CANSEC1.
