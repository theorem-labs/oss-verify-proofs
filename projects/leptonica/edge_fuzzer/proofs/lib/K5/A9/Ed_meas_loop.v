(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit
  Lept_objkit RT_trans Ed_iface Ed_fpkit Ed_statics Ed_fp Numa_kit Ed_numa_ival Ed_meas_defs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Definition MLW (sb fr : Z) : list (Z * Z) := [(sb - 16, sb); (fr + 32, fr + 36); (fr + 48, fr + 52)].

(* [comment removed for export] *)
Definition meas_loop_post (gp tp t0 t1 t2 s0 s2 s3 s5 s6 s7 s11 t3 t4 t5 t6 : word) (sb fr lo n : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (ra' a0' a1' a2' a3' a4' a5' a6' a7' s9' s10' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (wv wn : word),
    ms' = MS (mkR ra' (Z_to_bv 64 sb) gp tp t0 t1 t2 s0 (Z_to_bv 64 sb) a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 (fr + 48)) s5 s6 s7
                  (Z_to_bv 64 n) s9' s10' s11 t3 t4 t5 t6)
             F' (Z_to_bv 64 0x120fdc) (frm_clear fc') None m' (seg_rom asegs)
    /\ munch (MLW sb fr) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo sb
    /\ rw_cells asegs m' (fr + 32) [C4 wv] /\ rw_cells asegs m' (fr + 48) [C4 wn].

Lemma nth_error_ex' : forall {X} (l : list X) (i : nat), (i < length l)%nat -> exists x, nth_error l i = Some x.
Proof.
  intros X l i Hi. destruct (nth_error l i) as [x|] eqn:E; [exists x; reflexivity|]. apply nth_error_None in E. lia.
Qed.

Lemma outside_MLW_leaf : forall sb fr x, outside (MLW sb fr) x -> outside [(sb - 16, sb); (fr + 48, fr + 48 + 4)] x.
Proof. intros sb fr x H. unfold MLW in H. cbn [outside] in *. destruct H as (A & B & C & _). repeat split; try exact I; lia. Qed.

Lemma meas_loop : forall (k : nat) (i : Z)
    (ra a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 gp tp t0 t1 t2 s0 s2 s3 s5 s6 s7 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (sb fr lo n : Z) (live : list (Z * Z)) (na cap arr : Z) (vals : list word) (ks : list Z) (wv wn : word),
  Z.of_nat k = n - i -> 1 <= i < n -> n <= 20000 ->
  rw_cells asegs m (sb + 16) [C8 (Z_to_bv 64 (fr + 48)); C8 (Z_to_bv 64 (fr + 32)); C8 (Z_to_bv 64 (fr + 64))] ->
  rw_cells asegs m (sb + 48) [C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 1)] ->
  rw_cells asegs m (fr + 32) [C4 wv] -> rw_cells asegs m (fr + 48) [C4 wn] -> rw_cells asegs m (fr + 64) [C8 (Z_to_bv 64 na)] ->
  rw_cells asegs m (fr / 8 + SHB + 6) [C1 (Z_to_bv 8 4)] ->
  numa_obj live m na cap arr vals -> numa_ints vals ks -> Z.of_nat (length ks) = n ->
  (forall b kk x, In (b, kk) live -> b <= x < b + kk -> outside (MLW sb fr) x) ->
  acc asegs m na 32 -> acc asegs m arr (4 * cap) ->
  ro_cells asegs m g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)] ->
  ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] -> ED_RO m ->
  mem_inv asegs m -> stk asegs m lo sb ->
  lo <= sb - 16 -> sb + 208 <= 2^47 -> sb mod 16 = 0 -> 0x10007fff8000 <= lo ->
  na + 32 <= lo -> arr + 4 * cap <= lo -> fr + 128 <= lo ->
  (na + 32 <= 0x7fff7000 \/ 0x10007fff8000 <= na) -> (na + 32 <= 0x10000 \/ SEGTOP_A <= na) ->
  (arr + 4 * cap <= 0x7fff7000 \/ 0x10007fff8000 <= arr) -> (arr + 4 * cap <= 0x10000 \/ SEGTOP_A <= arr) ->
  (fr + 128 <= 0x7fff7000 \/ 0x10007fff8000 <= fr) -> SEGTOP_A <= fr -> fr mod 64 = 0 ->
  (fr + 128 <= na \/ na + 32 <= fr) -> (fr + 128 <= arr \/ arr + 4 * cap <= fr) ->
  evt asegs (meas_loop_post gp tp t0 t1 t2 s0 s2 s3 s5 s6 s7 s11 t3 t4 t5 t6 sb fr lo n m)
    (MS (mkR ra (Z_to_bv 64 sb) gp tp t0 t1 t2 s0 (Z_to_bv 64 sb) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (fr + 48)) s5 s6 s7
              (Z_to_bv 64 i) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x120f80) (frm_clear fc) None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i ra a0 a1 a2 a3 a4 a5 a6 a7 s9 s10 gp tp t0 t1 t2 s0 s2 s3 s5 s6 s7 s11 t3 t4 t5 t6 F fc m sb fr lo n live na cap arr vals ks wv wn
    HK HI HN SP16 SP48 VAL NVAL NAP SHN NOBJ NINT KLEN LOUT ACCn ACCa G1 G2 RO MI ST LO SHI SAL LOH NLO ALO FLO NSH NSEG ASH ASEG FRSH FRSEG FR64 FNA FARR.
  { lia. }
  pose proof (numa_obj_facts _ _ _ _ _ _ NOBJ) as (NLEN & NCAP & NA0 & NA16 & AR0 & AR16 & INn & INa & NNE).
  destruct (nth_error_ex' ks (Z.to_nat i) ltac:(lia)) as [ki Hki].
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SEGTOP_A, SHB in *.
  pose proof (munch_refl [(sb - 16, sb); (fr + 32, fr + 36); (fr + 48, fr + 52)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  lwalk [e_numaGetIValue].
  eapply evt_cut.
  { eapply (numaGetIValue_evt _ gp tp t0 t1 t2 s0 (Z_to_bv 64 sb) a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (fr + 48)) s5 s6 s7 (Z_to_bv 64 i) s9 s10 s11 t3 t4 t5 t6
              F fc m sb lo live na cap arr vals ks i (fr + 48) ki wn);
      first [ exact NOBJ | exact NINT | exact ACCn | exact ACCa | exact Hki | exact NVAL | exact G1 | exact G2 | exact RO | exact MI | exact ST
            | apply (acc_ushadow asegs m (fr + 48) 4); [clear - FR64; Z.div_mod_to_equations; lia | lia | lia
                | change (ushadow 4) with [Z_to_bv 8 4]; replace (shad (fr + 48)) with (fr / 8 + 2147450880 + 6) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
                  destruct SHN as [[_ B] _]; exact B ]
            | unfold SEGTOP_A; clear - HI HN LO SHI SAL LOH NLO ALO FLO NSH NSEG ASH ASEG FRSH FRSEG FR64 FNA FARR NA0 AR0 NCAP; first [lia | Z.div_mod_to_equations; lia] ]. }
  intros ms' PO. unfold numaGetIValue_post in PO.
  destruct PO as (a1' & a2' & a3' & a4' & a5' & a6' & a7' & F' & fc' & m' & -> & MU' & WM' & MI' & ST' & NVAL').
  rewrite (ret_pc_even 0x120f94) by (lia || reflexivity).
  (* [comment removed for export] *)
  assert (AGL : agree_on (outside [(sb - 16, sb); (fr + 48, fr + 48 + 4)]) m m') by (intros x Hx; exact (MU' x Hx)).
  assert (SP16' : rw_cells asegs m' (sb + 16) [C8 (Z_to_bv 64 (fr + 48)); C8 (Z_to_bv 64 (fr + 32)); C8 (Z_to_bv 64 (fr + 64))])
    by (apply (rw_cells_agree_nw asegs m m' _ _ SP16); eapply agree_sub; [exact AGL|]; cbv beta; intros x Hx; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; cbn [outside]; repeat split; try exact I; lia).
  assert (SP48' : rw_cells asegs m' (sb + 48) [C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 1)])
    by (apply (rw_cells_agree_nw asegs m m' _ _ SP48); eapply agree_sub; [exact AGL|]; cbv beta; intros x Hx; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; cbn [outside]; repeat split; try exact I; lia).
  assert (VAL' : rw_cells asegs m' (fr + 32) [C4 wv])
    by (apply (rw_cells_agree_nw asegs m m' _ _ VAL); eapply agree_sub; [exact AGL|]; cbv beta; intros x Hx; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; cbn [outside]; repeat split; try exact I; lia).
  assert (NAP' : rw_cells asegs m' (fr + 64) [C8 (Z_to_bv 64 na)])
    by (apply (rw_cells_agree_nw asegs m m' _ _ NAP); eapply agree_sub; [exact AGL|]; cbv beta; intros x Hx; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; cbn [outside]; repeat split; try exact I; lia).
  assert (SHN' : rw_cells asegs m' (fr / 8 + 2147450880 + 6) [C1 (Z_to_bv 8 4)])
    by (apply (rw_cells_agree_nw asegs m m' _ _ SHN); eapply agree_sub; [exact AGL|]; cbv beta; intros x Hx; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; cbn [outside];
        clear - Hx FRSH FRSEG LOH LO FLO SHI; repeat split; try exact I; Z.div_mod_to_equations; lia).
  assert (G1' : ro_cells asegs m' 1850336 [C8 (Z_to_bv 64 1937592)])
    by (apply (ro_cells_agree asegs m m' _ _ G1); eapply agree_sub; [exact AGL|]; cbv beta; intros x Hx; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; cbn [outside]; repeat split; try exact I; lia).
  assert (G2' : ro_cells asegs m' 1937592 [C8 (Z_to_bv 64 2147450880)])
    by (apply (ro_cells_agree asegs m m' _ _ G2); eapply agree_sub; [exact AGL|]; cbv beta; intros x Hx; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; cbn [outside]; repeat split; try exact I; lia).
  assert (RO' : ED_RO m').
  { destruct RO as [RO1 RO2]. unfold RO_SIGN_TAB, RO_HALF in *. split.
    - apply (ro_cells_agree asegs m m' _ _ RO1). eapply agree_sub; [exact AGL|]. cbv beta. intros x Hx. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. cbn [outside]. repeat split; try exact I; lia.
    - apply (ro_cells_agree asegs m m' _ _ RO2). eapply agree_sub; [exact AGL|]. cbv beta. intros x Hx. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. cbn [outside]. repeat split; try exact I; lia. }
  assert (NOBJ' : numa_obj live m' na cap arr vals).
  { apply (numa_obj_keep live m m' na cap arr vals); [| exact NOBJ]. intros b kk Hin a Ha. apply MU'.
    apply outside_MLW_leaf. exact (LOUT b kk (bv_unsigned a) Hin Ha). }
  assert (ACCn' : acc asegs m' na 32).
  { apply (acc_transport _ m m' na 32 ACCn MU'); [lia|]. unfold shad, SHB. cbn [disjoint_from].
    clear - NLO LOH LO NSH FRSH FRSEG NA0 SHI FLO. repeat split; try exact I; Z.div_mod_to_equations; lia. }
  assert (ACCa' : acc asegs m' arr (4 * cap)).
  { apply (acc_transport _ m m' arr (4 * cap) ACCa MU'); [lia|]. unfold shad, SHB. cbn [disjoint_from].
    clear - ALO LOH LO ASH FRSH FRSEG AR0 NCAP SHI FLO. repeat split; try exact I; Z.div_mod_to_equations; lia. }
  pose proof (munch_trans [(sb - 16, sb); (fr + 32, fr + 36); (fr + 48, fr + 52)] _ _ _ MU (munch_weaken _ _ m m' (outside_MLW_leaf sb fr) MU')) as MU2.
  pose proof (wmono_trans asegs _ _ _ WM WM') as WM2.
  clear MU WM AGL SP16 SP48 VAL NAP SHN G1 G2 RO NOBJ ACCn ACCa MI ST NVAL MU' WM'.
  rename MU2 into MU. rename WM2 into WM.
  (* [comment removed for export] *)
  pose proof (munch_refl [(fr + 32, fr + 36)] m') as MUS.
  (* [comment removed for export] *)
  lwalk [0x120f80; 0x120fdc].
  swrap32_fix.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
    assert (NOBJ0 : numa_obj live m0 na cap arr vals)
      by (apply (numa_obj_keep live m' m0 na cap arr vals); [| exact NOBJ'];
          let b := fresh "b" in let kk := fresh "kk" in let Hin := fresh "Hin" in let a := fresh "a" in let Ha := fresh "Ha" in
          intros b kk Hin a Ha; apply MUS; pose proof (LOUT b kk (bv_unsigned a) Hin Ha) as O; unfold MLW in O; cbn [outside] in O |- *; tauto);
    assert (RO0 : ED_RO m0)
      by (destruct RO' as [RO1 RO2]; unfold RO_SIGN_TAB, RO_HALF in *; split;
          [ apply (ro_cells_agree asegs m' m0 _ _ RO1) | apply (ro_cells_agree asegs m' m0 _ _ RO2) ];
          (intros x Hx; apply MUS; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; cbn [outside]; clear - Hx FRSEG; lia))
  end.
  clear NOBJ' RO' MUS.
  destruct k as [|k'].
  - (* [comment removed for export] *)
    brF.
    apply evt_done. unfold meas_loop_post.
    do 11 eexists. exists F', fc'. eexists. do 2 eexists.
    split; [replace (i + 1) with n by lia; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; eassumption.
  - (* [comment removed for export] *)
    brT.
    eapply evt_cut.
    + eapply (IH (i + 1)); try eassumption; try lia.
    + intros ms' PO. apply evt_done. unfold meas_loop_post in PO |- *.
      destruct PO as (ra'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & s9'' & s10'' & F'' & fc'' & m'' & wv'' & wn'' & E & MU'' & WM'' & R).
      do 11 eexists. exists F'', fc'', m'', wv'', wn''.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU'')|]. split; [exact (wmono_trans asegs _ _ _ WM WM'')| exact R].
Qed.
