(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_memset H_membuffer_init H_list_access H_ListAddTail H_freelist HU_list_kit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Definition parser_request_init_entry := 0x15a98%Z.
Definition parser_response_init_entry := 0x15b38%Z.
Ltac sstep := step; fix_lit_store.

Ltac split_chunk FR n H1 H2 :=
  lazymatch type of FR with rw_cells ?segs ?m ?A ?cs =>
    let cs1 := eval cbv beta iota delta [firstn skipn] in (firstn n cs) in
    let cs2 := eval cbv beta iota delta [firstn skipn] in (skipn n cs) in
    change (rw_cells segs m A (cs1 ++ cs2)) in FR;
    destruct (proj1 (rw_cells_app segs m A cs1 cs2) FR) as [H1 H2]; clear FR;
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in H2;
    try (lazymatch type of H2 with rw_cells _ _ (?a + ?b + ?c)%Z _ =>
           let v := eval vm_compute in (b + c)%Z in replace (a + b + c)%Z with (a + v)%Z in H2 by lia end)
  end.
Ltac recell FR i :=
  lazymatch type of FR with rw_cells ?segs ?m ?A ?cs =>
    let pre := eval cbv beta iota delta [firstn skipn] in (firstn i cs) in
    let post := eval cbv beta iota delta [firstn skipn] in (skipn (S i) cs) in
    lazymatch eval cbv beta iota delta [firstn skipn nth_error] in (nth_error cs i) with
    | Some (CB 8 ?b) => change (rw_cells segs m A (pre ++ CB 8 b :: post)) in FR; apply (rw_cells_CB_C8 segs m A pre b post) in FR; cbn [app] in FR
    | Some (CB 4 ?b) => change (rw_cells segs m A (pre ++ CB 4 b :: post)) in FR; apply (rw_cells_CB_C4 segs m A pre b post) in FR; cbn [app] in FR
    end end.

Lemma rw_cells_reshape : forall m A cs cs',
  rw_cells rsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[W B] WR] W' EB ES. split; [split; [exact W'| rewrite EB; exact B]| rewrite ES; exact WR].
Qed.

Ltac reshape H cs' :=
  lazymatch type of H with rw_cells _ ?m ?A ?cs =>
    let H' := fresh in
    assert (H' : rw_cells rsegs m A cs') by (eapply (rw_cells_reshape m A cs cs' H); [cbn; repeat split; reflexivity| vm_compute; reflexivity| vm_compute; reflexivity]);
    clear H; rename H' into H end.

Lemma memset0_call : forall (D n : Z) (junk : list byte)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc m,
  rw_cells rsegs m D [CB (Z.to_nat n) junk] -> mem_inv rsegs m -> (0 <= D /\ D + n < 2^64)%Z -> (0 <= n)%Z ->
  a0 = wz D -> a1 = wz 0 -> a2 = wz n ->
  evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz D) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(D, D + n)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' D [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x24660) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros DST MI HD HN -> -> ->.
  assert (E0 : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (E2 : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (E1 : bv_unsigned (Z_to_bv 64 0) = 0) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply (memset_spec _ _ _ _ _ _ _ _ _ (Z_to_bv 64 D) (Z_to_bv 64 0) (Z_to_bv 64 n)); rewrite ?E0, ?E2; eauto. }
  intros ms' Q. unfold memset_post in Q. rewrite !E0, !E1, !E2 in Q. cbn [Z.modulo] in Q. exact Q.
Qed.

Lemma ListInit_call : forall (qq lo L fcmp ffree : Z) (junk : list byte)
    ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc m,
  rw_cells rsegs m L [CB 96%nat junk] -> L <> 0%Z -> (L mod 8 = 0)%Z -> (0 <= fcmp < 2^64)%Z -> (0 <= ffree < 2^64)%Z ->
  stk rsegs m lo qq -> (64 <= lo)%Z -> (lo + 16 <= qq)%Z -> (qq < 2^64)%Z ->
  (L + 96 <= lo \/ qq <= L)%Z ->
  mem_inv rsegs m -> a0 = wz L -> a1 = wz fcmp -> a2 = wz ffree ->
  evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra (wz qq) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(qq - 16, qq); (L, L + 96)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo qq
      /\ rw_cells rsegs m' L (llist_cells (L + 24) L 0 0 0 ffree fcmp))
    (MS (mkR ra (wz qq) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ListInit_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros LC NZ LAL R1 R2 ST LO0 LO QQ SEP MI -> -> ->.
  assert (E : bv_unsigned (Z_to_bv 64 qq) = qq) by (apply unsigned_lit; lia).
  destruct (stk_split rsegs _ _ (qq - 16)%Z _ ST ltac:(lia)) as [STlo SThi].
  eapply evt_mono.
  { eapply (ListInit_spec L fcmp ffree junk _ (Z_to_bv 64 qq)); rewrite ?E; eauto; try lia. }
  intros ms' Q. unfold ListInit_post in Q. rewrite !E in Q. destruct_exs Q. destruct Q as (-> & MU & WM & MI' & ST' & LC').
  repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
  split; [| exact LC']. eapply stk_merge; [| exact ST'| lia]. eapply stk_transport_disjoint; [exact STlo| exact MU| exact WM|]. cbn. lia.
Qed.

Definition pinit_k5 (P pos : Z) : list cell :=
  [C8 (wz 0); C4 (wz 400); C4 (wz 0); C4 (wz pos); C4 (wz 1); C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz (P + 400)); C8 (wz 0); C4 (wz 0); C4 (wz 0)].
Definition parser_init_cells (m : mem) (P isreq meth pos : Z) : Prop :=
  rw_cells rsegs m P [C4 (wz 1); C4 (wz 0)]
  /\ rw_cells rsegs m (P + 8) [CB 216 (repeat (Z_to_bv 8 0) 216)]
  /\ rw_cells rsegs m (P + 224) [C4 (wz meth); C4 (wz 0)]
  /\ rw_cells rsegs m (P + 232) (mbuf_cells 0 0 0)
  /\ rw_cells rsegs m (P + 264) [C8 (wz 0); C4 (wz isreq); C4 (wz 0); C4 (wz 0); C4 (wz 0)]
  /\ rw_cells rsegs m (P + 288) (lhead_cells (P + 312) (P + 288) 0)
  /\ rw_cells rsegs m (P + 344) (fl_cells 0 0)
  /\ rw_cells rsegs m (P + 368) [C8 (wz 0x14068); C8 (wz 0x14038)]
  /\ rw_cells rsegs m (P + 384) [C8 (wz 0); C8 (wz 0)]
  /\ rw_cells rsegs m (P + 400) (mbuf_cells 0 0 0)
  /\ rw_cells rsegs m (P + 432) (pinit_k5 P pos).

Lemma parser_request_init_spec : forall (P : Z) (junk : list byte)
    ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc m lo,
  stk rsegs m lo (bv_unsigned sp) -> (lo + 48 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  rw_cells rsegs m P [CB 504 junk] -> (bv_unsigned sp <= P)%Z -> (P + 504 < 2^64)%Z -> P mod 8 = 0 ->
  evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (P, P + 504)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp)
      /\ parser_init_cells m' P 1 0 0)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz parser_request_init_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST LO LO0 MI PC PLO PHI PAL. unfold parser_request_init_entry.
  pose proof (word_lt64 sp) as SPB.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (P, P + 504)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST. do 5 sstep. zstep. zstep. zstep. zstep.
  call (memset0_call P 504 junk). all: side (first [exact PC| exact MI| reflexivity| lia]).
  rename MI0 into MI. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  apply (rw_cells_split_CB rsegs m1 P [] (Z.to_nat 504) _ [] [8; 216; 8; 32; 24; 96; 16; 32; 72]%nat) in POST; [| reflexivity].
  cbn [app mk_CB_cells] in POST.
  split_chunk POST 1%nat K1 R. split_chunk R 1%nat K2 R2. split_chunk R2 1%nat K3 R3. split_chunk R3 1%nat SB R4.
  split_chunk R4 1%nat K4 R5. split_chunk R5 1%nat LL R6. split_chunk R6 1%nat ENT R7. split_chunk R7 1%nat MBj K5.
  reshape K1 [C4 (wz 0); C4 (wz 0)]. reshape K3 [C4 (wz 0); C4 (wz 0)].
  reshape K4 [C8 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0)]. reshape ENT [C8 (wz 0); C8 (wz 0)].
  reshape K5 [C8 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0)].
  reshape K2 [CB 216 (repeat (Z_to_bv 8 0) 216)]. reshape SB [CB 32 (repeat (Z_to_bv 8 0) 32)].
  reshape LL [CB 96 (repeat (Z_to_bv 8 0) 96)]. reshape MBj [CB 32 (repeat (Z_to_bv 8 0) 32)].
  replace (P + Z.of_nat 8)%Z with (P + 8)%Z in K2 by lia.
  uwalk_ub_to 0x15af0%Z. step.
  call (ListInit_call (bv_unsigned sp + -32) lo (P + 288) 0x14038 0x14068 (repeat (Z_to_bv 8 0) 96)).
  all: side (first [exact LL| exact MI| exact ST| reflexivity| lia| (Z.div_mod_to_equations; lia)]).
  rename MI0 into MI. rename PC into ST. rename POST into LLC. replace (P + 288 + 24)%Z with (P + 312)%Z in LLC by lia. unfold llist_cells in LLC.
  zstep. zstep. zstep.
  call (membuffer_init_spec (P + 400) (repeat (Z_to_bv 8 0) 32)). all: side (first [exact MBj| exact MI| reflexivity| Z.div_mod_to_equations; lia]).
  rename MI0 into MI. rename POST into MBC. unfold mbuf_cells in MBC.
  zstep. zstep.
  call (membuffer_init_spec (P + 232) (repeat (Z_to_bv 8 0) 32)). all: side (first [exact SB| exact MI| reflexivity| Z.div_mod_to_equations; lia]).
  rename MI0 into MI. rename POST into SBC. unfold mbuf_cells in SBC.
  sstep. sstep. sstep. sstep. sstep.
  do 5 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|]. repeat (split; [eassumption|]).
  unfold parser_init_cells, pinit_k5, lhead_cells, fl_cells, mbuf_cells.
  destruct (rw_cells_take3 rsegs _ _ [C8 (wz 0); C8 (wz (P + 312)); C8 (wz 0); C8 (wz (P + 288)); C8 (wz 0); C8 (wz 0); C8 (wz 0)]
              [C8 (wz 0); C8 (wz LISTNODE_SIZEOF); C4 (wz FREELISTSIZE); C4 (wz 0)] [C8 (wz 82024); C8 (wz 81976)] LLC) as (L1 & L2 & L3).
  cbn [cells_size csize Nat.add] in L2, L3.
  replace (P + 288 + Z.of_nat 56)%Z with (P + 344)%Z in L2 by (cbn; lia). replace (P + 288 + Z.of_nat 56 + Z.of_nat 24)%Z with (P + 368)%Z in L3 by (cbn; lia).
  unfold LISTNODE_SIZEOF, FREELISTSIZE in L2.
  repeat match goal with |- _ /\ _ => split end; eassumption.
Qed.

Lemma parser_response_init_spec : forall (P : Z) (junk : list byte)
    (meth : Z) ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc m lo,
  stk rsegs m lo (bv_unsigned sp) -> (lo + 64 <= bv_unsigned sp)%Z -> (64 <= lo)%Z -> mem_inv rsegs m ->
  rw_cells rsegs m P [CB 504 junk] -> (bv_unsigned sp <= P)%Z -> (P + 504 < 2^64)%Z -> P mod 8 = 0 -> (0 <= meth < 2^32)%Z ->
  evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (P, P + 504)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp)
      /\ parser_init_cells m' P 0 meth 1)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz P) (wz meth) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz parser_response_init_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST LO LO0 MI PC PLO PHI PAL METH. unfold parser_response_init_entry.
  pose proof (word_lt64 sp) as SPB.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (P, P + 504)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST. do 6 sstep. zstep. zstep. zstep. zstep. zstep.
  call (memset0_call P 504 junk). all: side (first [exact PC| exact MI| reflexivity| lia]).
  rename MI0 into MI. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  apply (rw_cells_split_CB rsegs m1 P [] (Z.to_nat 504) _ [] [8; 216; 8; 32; 24; 96; 16; 32; 72]%nat) in POST; [| reflexivity].
  cbn [app mk_CB_cells] in POST.
  split_chunk POST 1%nat K1 R. split_chunk R 1%nat K2 R2. split_chunk R2 1%nat K3 R3. split_chunk R3 1%nat SB R4.
  split_chunk R4 1%nat K4 R5. split_chunk R5 1%nat LL R6. split_chunk R6 1%nat ENT R7. split_chunk R7 1%nat MBj K5.
  reshape K1 [C4 (wz 0); C4 (wz 0)]. reshape K3 [C4 (wz 0); C4 (wz 0)].
  reshape K4 [C8 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0)]. reshape ENT [C8 (wz 0); C8 (wz 0)].
  reshape K5 [C8 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0)].
  reshape K2 [CB 216 (repeat (Z_to_bv 8 0) 216)]. reshape SB [CB 32 (repeat (Z_to_bv 8 0) 32)].
  reshape LL [CB 96 (repeat (Z_to_bv 8 0) 96)]. reshape MBj [CB 32 (repeat (Z_to_bv 8 0) 32)].
  replace (P + Z.of_nat 8)%Z with (P + 8)%Z in K2 by lia.
  uwalk_ub_to 0x15b98%Z. step.
  call (ListInit_call (bv_unsigned sp + -48) lo (P + 288) 0x14038 0x14068 (repeat (Z_to_bv 8 0) 96)).
  all: side (first [exact LL| exact MI| exact ST| reflexivity| lia| (Z.div_mod_to_equations; lia)]).
  rename MI0 into MI. rename PC into ST. rename POST into LLC. replace (P + 288 + 24)%Z with (P + 312)%Z in LLC by lia. unfold llist_cells in LLC.
  zstep. zstep. zstep.
  call (membuffer_init_spec (P + 400) (repeat (Z_to_bv 8 0) 32)). all: side (first [exact MBj| exact MI| reflexivity| Z.div_mod_to_equations; lia]).
  rename MI0 into MI. rename POST into MBC. unfold mbuf_cells in MBC.
  zstep. zstep.
  call (membuffer_init_spec (P + 232) (repeat (Z_to_bv 8 0) 32)). all: side (first [exact SB| exact MI| reflexivity| Z.div_mod_to_equations; lia]).
  rename MI0 into MI. rename POST into SBC. unfold mbuf_cells in SBC.
  sstep. sstep. sstep. sstep. sstep. sstep. sstep.
  do 6 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|]. repeat (split; [eassumption|]).
  unfold parser_init_cells, pinit_k5, lhead_cells, fl_cells, mbuf_cells.
  destruct (rw_cells_take3 rsegs _ _ [C8 (wz 0); C8 (wz (P + 312)); C8 (wz 0); C8 (wz (P + 288)); C8 (wz 0); C8 (wz 0); C8 (wz 0)]
              [C8 (wz 0); C8 (wz LISTNODE_SIZEOF); C4 (wz FREELISTSIZE); C4 (wz 0)] [C8 (wz 82024); C8 (wz 81976)] LLC) as (L1 & L2 & L3).
  cbn [cells_size csize Nat.add] in L2, L3.
  replace (P + 288 + Z.of_nat 56)%Z with (P + 344)%Z in L2 by (cbn; lia). replace (P + 288 + Z.of_nat 56 + Z.of_nat 24)%Z with (P + 368)%Z in L3 by (cbn; lia).
  unfold LISTNODE_SIZEOF, FREELISTSIZE in L2.
  repeat match goal with |- _ /\ _ => split end; eassumption.
Qed.
