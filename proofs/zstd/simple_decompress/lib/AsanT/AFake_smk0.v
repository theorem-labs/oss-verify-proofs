(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase F_tryinit F_aunwind F_tlsga F_m2s_b.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AKit FsKit AFake_sm0 AFake_sm0r.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma land16383_mod64 : forall x, Z.land (x mod 18446744073709551616) 16383 = Z.land x 16383.
Proof.
  intros x. change 16383 with (Z.ones 14). rewrite !Z.land_ones by lia.
  change 18446744073709551616 with (2^64). rewrite (Z.mod_mod_divide _ (2^64) (2^14)) by (exists (2^50); reflexivity). reflexivity.
Qed.
Lemma swrap32_small_k : forall z, (-2^31 <= z < 2^31)%Z -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma land16383_bound : forall x, 0 <= Z.land x 16383 < 16384.
Proof. intros x. change 16383 with (Z.ones 14). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.

Lemma probe_loop0 : forall RNG (Q : machine_state -> Prop) ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (fs h n i : Z),
  0 <= i <= n -> n < 16384 -> 0 <= h < 2^64 -> 0 <= fs -> fs + 4096 + 16384 <= 2^47 ->
  (forall j, i <= j < n -> exists b, rw_cells bsegs m (fs + 4096 + Z.land (h + j) 16383) [C1 b] /\ b <> Z_to_bv 8 0) ->
  rw_cells bsegs m (fs + 4096 + Z.land (h + n) 16383) [C1 (Z_to_bv 8 0)] ->
  rng RNG (fs + 4096) 16384 ->
  (forall a0' a7', evtF bsegs RNG Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (Z_to_bv 64 (fs + 4096)) (Z_to_bv 64 (h + n)) (Z_to_bv 64 16383) a4
                (Z_to_bv 64 (fs + 4096 + Z.land (h + n) 16383)) (Z_to_bv 64 (Z.land (h + n) 16383)) a7'
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 0x3ef88) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (16384 - i)) (Z_to_bv 64 (fs + 4096)) (Z_to_bv 64 (h + i)) (Z_to_bv 64 16383) a4
                a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 0x3ef10) fc None m (seg_rom bsegs)).
Proof.
  intros until i. intros HI HN HH FS0 FSHI BUSY FREE RFL K.
  revert a5 a6 a7.
  remember (n - i) as d eqn:ED. assert (D0 : 0 <= d) by lia. revert i HI BUSY ED.
  induction d as [d IH] using (well_founded_induction (Z.lt_wf 0)). intros i HI BUSY ED a5 a6 a7.
  pose proof (land16383_bound (h + i)) as PB.
  zstep. rewrite land16383_mod64.                  (* [comment removed for export] *)
  zstep.                                           (* [comment removed for export] *)
  destruct (Z.eq_dec i n) as [EIN|NE].
  - (* [comment removed for export] *)
    subst i. remember (Z.land (h + n) 16383) as pos eqn:EPOS. remember (fs + 4096 + pos) as flag eqn:EFLAG.
    zstep; rewrite ?zxb_lit by lia.                (* [comment removed for export] *)
    zstep. if_cases Kd; zify_cond Kd; [| exfalso; clear - Kd; lia].     (* [comment removed for export] *)
    subst flag pos. apply K.
  - (* [comment removed for export] *)
    destruct (BUSY i ltac:(lia)) as (b & FB & NZ).
    remember (Z.land (h + i) 16383) as pos eqn:EPOS. remember (fs + 4096 + pos) as flag eqn:EFLAG.
    zstep. cbv beta.                               (* [comment removed for export] *)
    assert (NZb : bv_unsigned b <> 0) by (intros E0; apply NZ; apply bv_eq; rewrite E0; reflexivity).
    pose proof (bv_unsigned_in_range _ b) as BR.
    zstep. if_cases Kd; zify_cond Kd; [exfalso; clear - Kd NZb BR; lia|].   (* [comment removed for export] *)
    zstep. rewrite (swrap32_small_k (16384 - i + -1)) by lia.              (* [comment removed for export] *)
    zstep.                                         (* [comment removed for export] *)
    zstep. if_cases Ke; zify_cond Ke; [| exfalso; clear - Ke NE HI HN ED; lia].  (* [comment removed for export] *)
    replace (16384 - i + -1) with (16384 - (i + 1)) by lia. replace (h + i + 1) with (h + (i + 1)) by lia.
    subst flag pos.
    eapply (IH (d - 1) ltac:(lia) ltac:(lia) (i + 1)); [lia| intros j Hj; apply BUSY; lia| lia].
Qed.
(* [comment removed for export] *)
Lemma probe_loop0_0 : forall RNG (Q : machine_state -> Prop) ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (fs h n : Z),
  0 <= n < 16384 -> 0 <= h < 2^64 -> 0 <= fs -> fs + 4096 + 16384 <= 2^47 ->
  (forall j, 0 <= j < n -> exists b, rw_cells bsegs m (fs + 4096 + Z.land (h + j) 16383) [C1 b] /\ b <> Z_to_bv 8 0) ->
  rw_cells bsegs m (fs + 4096 + Z.land (h + n) 16383) [C1 (Z_to_bv 8 0)] ->
  rng RNG (fs + 4096) 16384 ->
  (forall a0' a7', evtF bsegs RNG Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (Z_to_bv 64 (fs + 4096)) (Z_to_bv 64 (h + n)) (Z_to_bv 64 16383) a4
                (Z_to_bv 64 (fs + 4096 + Z.land (h + n) 16383)) (Z_to_bv 64 (Z.land (h + n) 16383)) a7'
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 0x3ef88) fc None m (seg_rom bsegs))) ->
  evtF bsegs RNG Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 16384) (Z_to_bv 64 (fs + 4096)) (Z_to_bv 64 h) (Z_to_bv 64 16383) a4
                a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 0x3ef10) fc None m (seg_rom bsegs)).
Proof.
  intros until n. intros HN HH FS0 FSHI BUSY FREE RFL K.
  pose proof (probe_loop0 RNG Q ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m fs h n 0
                ltac:(lia) ltac:(lia) HH FS0 FSHI ltac:(intros j Hj; apply BUSY; lia) FREE RFL K) as L.
  rewrite Z.add_0_r, Z.sub_0_r in L. exact L.
Qed.

(* [comment removed for export] *)
Lemma land16383_inj : forall h j n, 0 <= j < n -> n < 16384 -> Z.land (h + j) 16383 <> Z.land (h + n) 16383.
Proof.
  intros h j n Hj Hn. change 16383 with (Z.ones 14). rewrite !Z.land_ones by lia. intros E.
  assert (E2 : ((h + n) - (h + j)) mod 2^14 = 0).
  { rewrite Zminus_mod. rewrite E. rewrite Z.sub_diag. reflexivity. }
  replace ((h + n) - (h + j)) with (n - j) in E2 by lia. rewrite Z.mod_small in E2 by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma stack_malloc0_cspecK : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo ctx t B v fs h n pos flag F : Z) (j24 j56 sh0 h1 h2 : word) (hs : list byte),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 208 -> ATOP <= lo ->
  tp = Z_to_bv 64 ATP ->
  rt_inited m ->
  rw_cells bsegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  tlsga_cells m t B v (Z_to_bv 64 fs) ->
  rt_shbase m -> rt_layout m ->
  0 < ctx -> ctx + 4096 <= ATOP -> 0 < t -> t + 4096 <= ATOP -> iclr B 4096 -> B + 4096 <= ATOP -> 0 < v < 2^64 ->
  ablk fs (fs + 11571200) -> fs + 11571200 <= ATOP -> fs mod 4096 = 0 ->
  rw_cells bsegs m fs [C8 (Z_to_bv 64 h); C8 h1; C8 h2; CB 64 hs] -> 0 <= h < 2^64 ->
  rw_cells bsegs m (fs + 88) [C8 (Z_to_bv 64 20)] -> rw_cells bsegs m (fs + 96) [C1 (Z_to_bv 8 0)] ->
  (* [comment removed for export] *)
  0 <= n < 16384 ->
  (forall j, 0 <= j < n -> exists b, rw_cells bsegs m (fs + 4096 + Z.land (h + j) 16383) [C1 b] /\ b <> Z_to_bv 8 0) ->
  (* [comment removed for export] *)
  pos = Z.land (h + n) 16383 -> flag = fs + 4096 + pos -> F = fs + 36864 + pos * 64 ->
  rw_cells bsegs m flag [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m (F + 24) [C8 j24] -> rw_cells bsegs m (F + 56) [C8 j56] ->
  rw_cells bsegs m (shad F) [C8 sh0] ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG B 4096 ->
  rng RNG fs 11571200 -> rng RNG (shad fs) (shlen 11571200) ->
  evtF bsegs RNG (sm0_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo fs (h + n) flag F h1 h2 hs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 ASTKMALLOC0) fc None m (seg_rom bsegs)).
Proof.
  intros until hs.
  intros MI ST LO CEIL TP INI TI TK T88 TSD CT TC SHB LAY C0 C1 T0 T1 BLO BHI V
         FLO FHI FAL HNT HB LOG NGC HN BUSY POS FLAG FF FL0 F24 F56 SH0
         RIMG RSTK RCTX RT RB RFS RSH.
  pose proof (ablk_lin _ _ FLO) as (FLOL & _ & _ & _). unfold AIMG_HI in FLOL.   (* [comment removed for export] *)
  pose proof TC as TC0. destruct TC as (REAL & DESC & DTVP & DTV1 & G50 & CF & GB0 & VERB & G08 & DV & BD & (tb & te & T48)).
  pose proof (munch_refl (sm0_W (bv_unsigned sp) fs flag F) m) as MU. unfold sm0_W in MU. pose proof (wmono_refl bsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold AIMG_HI, AREAL_TLSGA, AFSDESC, ATP, ADTV, GOT_CFLAGS, ACFLAGS, ACF137, AVERB, ADTLSV, ATSDI, ATSDK, ATP88, ATSD, ASTKMALLOC0 in *.
  lit_in DTVP; lit_in DTV1.
  assert (PB : 0 <= pos < 16384).
  { subst pos. change 16383 with (Z.ones 14). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHD : shad F + 8 <= fs \/ fs + 11571200 <= shad F).   (* [comment removed for export] *)
  { pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR. rewrite SHF. clear - FLOB FHI FF PB ATR. lia. }
  carve_frame 32%nat ST.
  do 5 zstep.                               (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  box RCTX; box RT; box RB.   (* [comment removed for export] *)
  call_sp tlsga_icpt_spec;
    first [ exact MI | exact ST | exact TP | reflexivity | exact INI | exact TI | exact TK | exact T88 | exact TSD | exact CT
          | (unfold tlsga_cells; repeat lazymatch goal with |- _ /\ _ => split end; first [eassumption | do 2 eexists; eassumption])
          | exact RIMG | (unbox RCTX; exact RCTX) | (unbox RT; exact RT) | (unbox RB; exact RB) | exact BLO
          | lia | solve_rng | idtac ].
  unbox RCTX; unbox RT; unbox RB.
  rename POST into ST. unfold ATP.
  lazymatch goal with H : mem_inv bsegs _ |- _ => rename H into MI2 end.
  zstep.                                    (* [comment removed for export] *)
  zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka FLOL; lia|].   (* [comment removed for export] *)
  zstep; rewrite zxb_lit by lia.            (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. if_cases Kb; zify_cond Kb; [| exfalso; clear - Kb; lia].      (* [comment removed for export] *)
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  zstep; lits.                              (* [comment removed for export] *)
  zstep. if_cases Kc; zify_cond Kc; [exfalso; clear - Kc; lia|].      (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.               (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with W : wmono bsegs m ?m2 |- _ => rename m2 into mL end.
  assert (PBn : 0 <= Z.land (h + n) 16383 < 16384) by apply land16383_bound.
  assert (BUSY2 : forall j, 0 <= j < n -> exists b, rw_cells bsegs mL (fs + 4096 + Z.land (h + j) 16383) [Cells.C1 b] /\ b <> Z_to_bv 8 0).
  { intros j Hj. destruct (BUSY j Hj) as (b & Hb & Nb). exists b. split; [| exact Nb].
    eapply rw_cells_transport; [exact Hb| exact MU| exact WM|].
    pose proof (land16383_inj h j n ltac:(lia) ltac:(lia)) as NEQ. pose proof (land16383_bound (h + j)) as PBj.
    pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR.
    cbn [disjoint_from cells_size csize fst snd]. rewrite SHF. subst flag F pos.
    clear - NEQ PBj PBn FLOB FHI ATR LO CEIL HN Hj. repeat split; lia. }
  eapply probe_loop0_0 with (n := n) (fs := fs) (h := h);
    [ lia | exact HB | lia | (pose proof atop_range as ATR0; lia) | exact BUSY2
    | (rewrite <- POS, <- FLAG; exact FL0) | (eapply rng_sub'; [exact RFS| lia]) | intros a0' a7' ].
  (* [comment removed for export] *)
  rewrite <- POS. rewrite <- FLAG.
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. zstep.                             (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  match goal with |- context [Z_to_bv 64 (fs + 36864 + Z.shiftl pos 6)] =>
    replace (fs + 36864 + Z.shiftl pos 6) with F by (rewrite Z.shiftl_mul_pow2 by lia; change (2^6) with 64; lia) end.
  zstep. zstep.                             (* [comment removed for export] *)
  zstep.                                    (* [comment removed for export] *)
  zstep. call m2sb_spec;
    first [ eassumption
          | (pose proof FLO as FLOB; unfold ablk, AIMG_HI, KLS in FLOB; rewrite unsigned_lit by (atop_facts; lia); unfold KLOW, KHIGH, KEND;
             destruct FLOB as [FLOB|FLOB]; [left|right]; atop_facts; clear - FLOB FHI FF PB; lia)   (* [comment removed for export] *)
          | idtac ].
  rewrite unsigned_lit by lia.
  zstep. zstep. zstep.                      (* [comment removed for export] *)
  assert (RSF : rng RNG (shad F) 8).
  { eapply rng_sub'; [exact RSH|]. rewrite SHF. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    clear - FLOL FHI FF PB. Z.div_mod_to_equations. lia. }
  zstep.                                    (* [comment removed for export] *)
  do 6 zstep.                               (* [comment removed for export] *)
  lazymatch goal with H : stk bsegs _ lo _ |- _ => rename H into ST9 end.
  release_frame FR0 ST9 (bv_unsigned sp). finish.
Qed.
End CANSEC1.
