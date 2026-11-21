(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import base decidable list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit Require PropExec StdModel ShapeAlg ModelAmb.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Walk Arr SysStep ITree Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require Import KInv. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require Import KLink. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require Import KEv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Malloc Require MM15. Import MM15. Import MM15.ProgDeps. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Malloc Require MM13. Import MM13. Import MM13.MallocBlocks. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Malloc Require MM12. Import MM12. Import MM12.Malloc_iface. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Malloc Require MM02. Import MM02. Import MM02.Malloc_ifaceP.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.PlainS7 Require Import PImg RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP F_memcpy.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Mr Require Import MrFeasNull MrFeasNull44 MrFeasSome1 MrFeasLift2 MrRoom MrRulesS7.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.MrP7 Require Import S7HeapPre S7HBase S7HConv S7TrTail S7RdLib S7RdInv S7RdRules.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section GROW.
Context {RCa1 : RunCtx}.
Context {rc : runConstT}.
Variable sp0 : Z.
Hypothesis SP0 : 0x7fff80000000 <= sp0 <= 0x800000000000.
Hypothesis SP16 : sp0 mod 16 = 0.
Hypothesis ATOPE : ATOP = sp0 - 8388608.
Variables (path : list byte) (stdin0 : ModelAmb.AmbIn) (fs0 : Fs) (tid : word) (content : list byte).
Variables (AI AIm : nat -> list bptr -> PState -> Model -> Prop).
Hypothesis RM : rule_malloc_grow AI AIm.
Hypothesis RF : rule_free_grow AI AIm.
Hypothesis AIm_perm : forall j X X' s mo, Permutation.Permutation X X' -> AIm j X s mo -> AIm j X' s mo.

Abbreviation RDI := (fun len => rd_inv sp0 tid content (G_rd path stdin0 fs0 tid len)).
Abbreviation GRD := (G_rd path stdin0 fs0 tid).

Lemma grow_step_rz : forall (j : nat) (A K : ShapeAlg.TSet) (pb : bptr) (buf cap : Z) (M : word -> option byte) (s : PState) (mo : Model)
    (x1 x3 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  RDI cap pb buf cap cap M s mo -> 65536 <= cap < 2 ^ 26 ->
  AI (S j) [pb] s mo ->
  A [] -> K [] ->
  (forall (M' : word -> option byte) (s' : PState) (mo' : Model)
          (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     RDI cap pb buf cap cap M' s' mo' ->
     realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR y1 (Z_to_bv 64 (sp0 - 128)) x3 (Z_to_bv 64 RATP) y5 y6 y7 x8 (Z_to_bv 64 buf)
                                    y10 y11 y12 y13 y14 y15 y16 y17 x18 (Z_to_bv 64 cap) (Z_to_bv 64 3) (Z_to_bv 64 (2 * cap))
                                    (Z_to_bv 64 0x22e79) (Z_to_bv 64 buf) x24 x25 x26 x27 y28 y29 y30 y31)
                               bvmap_empty (Z_to_bv 64 0x14b34) fc0 None M' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo') A) ->
  (forall (pb' : bptr) (nb : Z) (M' : word -> option byte) (s' : PState) (mo' : Model)
          (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
     RDI cap pb' nb (2 * cap) cap M' s' mo' -> AI j [pb'] s' mo' ->
     realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR y1 (Z_to_bv 64 (sp0 - 128)) x3 (Z_to_bv 64 RATP) y5 y6 y7 x8 (Z_to_bv 64 nb)
                                    y10 y11 y12 y13 y14 y15 y16 y17 x18 (Z_to_bv 64 cap) (Z_to_bv 64 3) (Z_to_bv 64 (2 * cap))
                                    (Z_to_bv 64 0x22e79) (Z_to_bv 64 buf) x24 x25 x26 x27 y28 y29 y30 y31)
                               bvmap_empty (Z_to_bv 64 0x14998) fc0 None M' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo') K) ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR x1 (Z_to_bv 64 (sp0 - 128)) x3 (Z_to_bv 64 RATP) x5 x6 x7 x8 (Z_to_bv 64 buf)
                                 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 cap) (Z_to_bv 64 3) x21
                                 (Z_to_bv 64 0x22e79) (Z_to_bv 64 buf) x24 x25 x26 x27 x28 x29 x30 x31)
                            bvmap_empty (Z_to_bv 64 0x14960) fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo)
           (ShapeAlg.t_alt2 A K).
Proof.
  intros until x31. intros RI CAP HAI HA0 HK0 KNULL KSOME.
  pose proof (rd_blk_range _ _ _ _ _ _ _ _ _ _ _ RI) as (BR1 & BR2 & BR3 & BR4).
  pose proof (ri_own _ _ _ _ _ _ _ _ _ _ _ RI) as HOWN.
  pose proof HOWN as [(L & _ & HKL & _) _].
  pose proof (kl_halt _ _ _ HKL) as Hh.
  pose proof (ns_nolazy _ _ _ _ _ _ _ (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb)) mo (kl_minv _ _ _ HKL)) as Hl.
  apply rz_evt; [exact Hh | exact Hl |].
  step. step.
  assert (SH : Z.shiftr cap 26 = 0) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
  rewrite unsigned_lit by lia. rewrite SH. if_false.
  step. step. step. apply evt_done.
  replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 cap) ≪ 1)) with (Z_to_bv 64 (2 * cap)).
  2:{ rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia. f_equal. lia. }
  pose proof RI as [HH _ (bs & BLK & PRE) LEN BASE].
  pose proof BASE as [ST UP (junk & FRM) (errv & ERR) MI AUX IMG TIDC].
  lazymatch goal with |- realizes _ (mkCfg (MS ?RR _ _ _ _ _ _) _) _ =>
    eapply (RM j RR M mo s [(pb, buf, cap)] [pb] (GRD cap) (2 * cap) (sp0 - 6144513) sp0 errv A K) end.   (* the stack window *)
  1:{ apply call_pre_intro.
      - exact HH.
      - exact HOWN.
      - apply frame_ok_G_rd.
      - exact AUX.
      - simp_regs; rewrite unsigned_lit by lia; lia.
      - simp_regs; rewrite unsigned_lit by lia; exact ST.
      - lia.
      - simp_regs; rewrite unsigned_lit by lia; unfold RMALLOC_STACK; lia.
      - simp_regs; rewrite rerrno_lit'; exact ERR.
      - exact MI.
      - simp_regs; reflexivity. }
  1: simp_regs; reflexivity. 1: lia. 1: exact HAI. 1: exact HA0. 1: exact HK0.
  intros R' M' mo' s' r MR OR HAIm.
  destruct MR as (KEPT & MI' & ST' & [errv' ERR'] & AUX' & HP & _ & _ & HR).
  revert HP ST' ERR'. simp_regs. rewrite !unsigned_lit by lia. rewrite rerrno_lit'. intros HP ST' ERR'.
  destruct r as [q|]; cbn [own_ret] in OR.
  2:{
    destruct HR as [Ha0 HH'].
    pose proof OR as [(L' & _ & HKL' & _) _].
    pose proof (kl_halt _ _ _ HKL') as Hh'.
    pose proof (ns_nolazy _ _ _ _ _ _ _ (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb)) mo' (kl_minv _ _ _ HKL')) as Hl'.
    use_kept KEPT. rewrite Ha0. forget_regs R'.
    rewrite ret_pc_even by (first [lia | reflexivity]).
    apply rz_evt; [exact Hh' | exact Hl' |].
    step. if_true. apply evt_done.
    eapply KNULL.
    eapply (rd_inv_heap_same sp0 tid content (GRD cap) (GRD cap) pb buf cap cap M M' s s' mo mo' errv');
      [exact RI | exact HP | exact HH' | exact OR | exact MI' | exact ST' | exact ERR' | exact AUX']. }
  destruct HR as (nb & junk2 & Ha0 & _ & HH' & NBLK & _).
  pose proof OR as [(L' & _ & HKL' & _) _].
  pose proof (kl_halt _ _ _ HKL') as Hh'.
  pose proof (ns_nolazy _ _ _ _ _ _ _ (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb)) mo' (kl_minv _ _ _ HKL')) as Hl'.
  pose proof (RHEAP_block_range_proof _ _ _ (q, nb, 2 * cap) HH' ltac:(left; reflexivity)) as (N1 & N2 & N3 & N4 & N5).
  cbn [blk_addr blk_size fst snd] in N1, N2, N3, N4, N5.
  pose proof (RHEAP_blocks_nodup_proof _ _ _ HH') as ND.
  assert (DISJ : nb + 2 * cap <= buf \/ buf + cap <= nb).
  { pose proof (RHEAP_blocks_disjoint_proof _ _ _ (q, nb, 2 * cap) (pb, buf, cap) HH' ltac:(left; reflexivity) ltac:(right; left; reflexivity)) as D.
    cbn [blk_id blk_addr blk_size fst snd] in D. apply D. cbn [map blk_id fst] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _].
    intros E. apply NI. left. symmetry. exact E. }
  pose proof (rw_cells_bound _ _ _ _ BLK) as BB. cbn [cells_size csize] in BB.
  assert (BLK' : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M' buf [CB (Z.to_nat cap) bs]).
  { eapply rheap_pres_rw_cells; [exact HP | exact BLK |]. right; right. exists (pb, buf, cap). split; [left; reflexivity|].
    cbn [cells_size csize blk_addr blk_size fst snd]. lia. }
  assert (BASE' : rd_base sp0 tid M')
    by (eapply rd_base_heap; [exact BASE | exact HP | lia | exact MI' | exact ST' | exact ERR' | exact AUX']).
  assert (LBS : length bs = Z.to_nat cap) by (destruct BLK as [[[W _] _] _]; exact W).
  use_kept KEPT. rewrite Ha0. forget_regs R'.
  rewrite ret_pc_even by (first [lia | reflexivity]).
  apply rz_evt; [exact Hh' | exact Hl' |].
  step.
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    let C := fresh "C" in assert (C : c = false);
    [ unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia | rewrite C; cbv iota; clear C ] end.
  step. step.
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    let C := fresh "C" in assert (C : c = false);
    [ unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia | rewrite C; cbv iota; clear C ] end.
  do 4 step.
  assert (NSPLIT : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M' nb [CB (Z.to_nat cap) (firstn (Z.to_nat cap) junk2)]
                   /\ rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M' (nb + cap) [CB (Z.to_nat cap) (firstn (Z.to_nat cap) (skipn (Z.to_nat cap) junk2))]).
  { pose proof (rw_cells_split_CB (run_segments psegs rc_inp rc_sp rc_mb) M' nb [] (Z.to_nat (2 * cap)) junk2 [] [Z.to_nat cap; Z.to_nat cap] NBLK
                  ltac:(cbn [sum_nat]; lia)) as SP.
    cbn [app mk_CB_cells] in SP.
    change [CB (Z.to_nat cap) (firstn (Z.to_nat cap) junk2); CB (Z.to_nat cap) (firstn (Z.to_nat cap) (skipn (Z.to_nat cap) junk2))]
      with ([CB (Z.to_nat cap) (firstn (Z.to_nat cap) junk2)] ++ [CB (Z.to_nat cap) (firstn (Z.to_nat cap) (skipn (Z.to_nat cap) junk2))]) in SP.
    apply (proj1 (rw_cells_app (run_segments psegs rc_inp rc_sp rc_mb) M' nb _ _)) in SP. cbn [cells_size csize] in SP.
    rewrite Nat.add_0_r, Z2Nat.id in SP by lia. exact SP. }
  destruct NSPLIT as [NB1 NB2].
  assert (SRC : bytes_at (run_segments psegs rc_inp rc_sp rc_mb) M' buf bs).
  { pose proof (rw_cells_bytes_at _ _ _ _ BLK') as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. exact X. }
  eapply evt_cut.
  { eapply memcpy_callv with (src := bs) (junk := firstn (Z.to_nat cap) junk2);
      [exact SRC | exact LBS | exact NB1 | lia | lia | lia | lia | exact MI']. }
  cbv beta. intros ms' PO.
  destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & -> & MUc & WMc & MI2 & NBC & _).
  assert (FW1 : Forall (fp_rd sp0) [(nb, nb + cap)]) by (constructor; [right; left; cbn [fst snd]; lia | constructor]).
  assert (HH2 : RHEAP s' [(q, nb, 2 * cap); (pb, buf, cap)] m2).
  { eapply RHEAP_frame_proof; [exact HH' | exact MUc | exact WMc |].
    constructor; [| constructor]. right; right. exists (q, nb, 2 * cap). split; [left; reflexivity|]. cbn. lia. }
  assert (FV1 : Forall (fun iv => snd iv <= ATOP -> (snd iv <= 0x10000 \/ 0x94000 <= fst iv) -> wv_out M' iv) [(nb, nb + cap)]).
  { (* the grown block's first half was writable (NB1) *)
    constructor; [|constructor]. intros _ _ a Ha _. cbn [fst snd] in Ha.
    destruct NB1 as [_ (_ & _ & WA)]. cbn [cells_size csize] in WA. rewrite Nat.add_0_r, Z2Nat.id in WA by lia.
    replace a with (nb + (a - nb)) by lia. apply WA. lia. }
  assert (BASE2 : rd_base sp0 tid m2) by (eapply rd_base_munch; [exact SP0 | exact ATOPE | exact BASE' | exact MUc | exact WMc | exact FW1 | exact FV1]).
  assert (BLK2 : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m2 buf [CB (Z.to_nat cap) bs]).
  { eapply rw_cells_transport; [exact BLK' | exact MUc | exact WMc |]. cbn [cells_size csize disjoint_from]. split; [lia | exact I]. }
  assert (NB2' : rw_cells (run_segments psegs rc_inp rc_sp rc_mb) m2 (nb + cap) [CB (Z.to_nat cap) (firstn (Z.to_nat cap) (skipn (Z.to_nat cap) junk2))]).
  { eapply rw_cells_transport; [exact NB2 | exact MUc | exact WMc |]. cbn [cells_size csize disjoint_from]. split; [lia | exact I]. }
  pose proof BASE2 as [ST2 _ _ (errv2 & ERR2) _ AUX2 _ _].
  replace (ret_pc (Z_to_bv 64 84368)) with (Z_to_bv 64 84368) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  do 2 step. apply evt_done.
  assert (OR' : OWN [pb; q] (GRD cap) s' mo') by (eapply OWN_perm; [apply Permutation.perm_swap | exact OR]).
  lazymatch goal with |- realizes _ (mkCfg (MS ?RR _ _ _ _ _ _) _) _ =>
    eapply (RF j RR m2 mo' s' [(q, nb, 2 * cap); (pb, buf, cap)] [q] (GRD cap) pb buf cap (sp0 - 6144513) sp0 errv2 K) end.
  1:{ apply call_pre_intro.
      - exact HH2.
      - exact OR'.
      - apply frame_ok_G_rd.
      - exact AUX2.
      - simp_regs; rewrite unsigned_lit by lia; lia.
      - simp_regs; rewrite unsigned_lit by lia; exact ST2.
      - lia.
      - simp_regs; rewrite unsigned_lit by lia; unfold RFREE_STACK; lia.
      - simp_regs; rewrite rerrno_lit'; exact ERR2.
      - exact MI2.
      - simp_regs; reflexivity. }
  1: right; left; reflexivity. 1: simp_regs; reflexivity.
  1: exact (AIm_perm j [q; pb] [pb; q] s' mo' (Permutation.perm_swap pb q []) HAIm).
  intros R3 M3 mo3 s3 KEPT3 MI3 ST3 ERR3 AUX3 HP3 HH3 HOWN3 HAI3.
  revert HP3 ST3 ERR3. simp_regs. rewrite !unsigned_lit by lia. rewrite rerrno_lit'. intros HP3 ST3 ERR3.
  change (lb_remove pb [(q, nb, 2 * cap); (pb, buf, cap)]) with (lb_remove (blk_id (pb, buf, cap)) [(q, nb, 2 * cap); (pb, buf, cap)]) in HP3, HH3.
  rewrite (lb_remove_second (q, nb, 2 * cap) (pb, buf, cap) ND) in HP3, HH3.
  use_kept KEPT3. forget_regs R3.
  rewrite ret_pc_even by (first [lia | reflexivity]).
  eapply KSOME; [|exact HAI3].
  constructor.
  - exact HH3.
  - exact HOWN3.
  -
    exists (bs ++ firstn (Z.to_nat cap) (skipn (Z.to_nat cap) junk2)). split.
    + assert (RNG : forall A n, nb <= A -> A + n <= nb + 2 * cap -> rclient_range [(q, nb, 2 * cap)] (sp0 - 128) A n).
      { intros A0 n0 H1 H2. right; right. exists (q, nb, 2 * cap). split; [left; reflexivity|]. cbn [blk_addr blk_size fst snd]. lia. }
      pose proof (rheap_pres_rw_cells _ _ _ _ _ _ HP3 NBC ltac:(apply RNG; cbn [cells_size csize]; lia)) as C1.
      pose proof (rheap_pres_rw_cells _ _ _ _ _ _ HP3 NB2' ltac:(apply RNG; cbn [cells_size csize]; lia)) as C2.
      pose proof (proj2 (rw_cells_app (run_segments psegs rc_inp rc_sp rc_mb) M3 nb [CB (Z.to_nat cap) bs] [CB (Z.to_nat cap) (firstn (Z.to_nat cap) (skipn (Z.to_nat cap) junk2))])) as J.
      cbn [cells_size csize] in J. rewrite Nat.add_0_r, Z2Nat.id in J by lia. specialize (J (conj C1 C2)).
      pose proof (rw_cells_merge (run_segments psegs rc_inp rc_sp rc_mb) M3 nb [] _ [] ltac:(rewrite app_nil_r; exact J)) as MG.
      cbn [app cells_size csize cells_bytes cbytes] in MG. rewrite app_nil_r, Nat.add_0_r in MG.
      replace (Z.to_nat (2 * cap)) with (Z.to_nat cap + Z.to_nat cap)%nat by lia. exact MG.
    + rewrite firstn_app. replace (Z.to_nat cap - length bs)%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r. exact PRE.
  - destruct LEN as [L1 L2]. lia.
  - eapply rd_base_heap; [exact BASE2 | exact HP3 | lia | exact MI3 | exact ST3 | exact ERR3 | exact AUX3].
Qed.
End GROW.
