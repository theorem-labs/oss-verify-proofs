(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_d_base RZ_seq_d_last huf411_kit_rs seqS_kit_al.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac sn_xinv REP HH3 BUF STK MU WM MI :=
  cbn [seqd_xinv]; unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy in *; split; [do 3 eexists; exact REP|];
  split; [exact HH3|]; split; [exact BUF|]; split; [exact STK|]; split; [exact MU|]; split; [exact WM| exact MI].
Ltac sn_modsmall := repeat match goal with K : context [?x mod 2 ^ 64] |- _ => rewrite (Z.mod_small x) in K by lia end.
Ltac sn_fk FR k n := apply (rw_cells_forget _ _ _ k n) in FR; [|reflexivity]; cbn [firstn skipn] in FR.
Ltac sn_c8 FR := lazymatch type of FR with rw_cells _ _ _ (CB _ _ :: C8 _ :: _) => idtac end.
Ltac sn_c13 FR := lazymatch type of FR with rw_cells _ _ _ (CB _ _ :: [_; _; _; _; _; _; _; _; _; _; _; _; _]) => idtac end.
Ltac sn_forgetc FR n chk :=
  first [ sn_fk FR 1%nat n; chk FR | sn_fk FR 2%nat n; chk FR | sn_fk FR 3%nat n; chk FR | sn_fk FR 4%nat n; chk FR
        | sn_fk FR 5%nat n; chk FR | sn_fk FR 6%nat n; chk FR | sn_fk FR 7%nat n; chk FR | sn_fk FR 8%nat n; chk FR
        | sn_fk FR 9%nat n; chk FR | sn_fk FR 10%nat n; chk FR ].
Ltac sn_frame_last FR :=
  sn_forgetc FR 32%nat ltac:(sn_c8);
  lazymatch type of FR with rw_cells _ ?mm ?A (?c1 :: ?c2 :: ?rest) =>
    let FA := fresh "FA" in let FB := fresh "FB" in let FRL := fresh "FRL" in
    destruct (proj1 (rw_cells_app usegs mm A [c1; c2] rest) FR) as [FA FB];
    sn_forgetc FB 208%nat ltac:(sn_c13);
    lazymatch type of FB with rw_cells _ _ _ ?rest' =>
      pose proof (proj2 (rw_cells_app usegs mm A [c1; c2] rest') (conj FA FB)) as FRL end;
    cbn [app] in FRL; clear FR FA FB; rename FRL into FR
  end.
Ltac sn_trap :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d724) _ _ _ _) => first [ kx_trap_fast | rsk_unkeep; seqs_land_close ]
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac sn_fin PLAST PEXIT MUL WML MU WM PO REP HH3 BUF STK LRD FR RG0 SEP0 OSL :=
  hold MU; kx_mem; unfold held in *;
  let LRD2 := fresh "LRD2" in
  lazymatch type of MUL with munch _ ?ma ?mb =>
    lazymatch type of LRD with rdbl _ _ ?a ?b =>
      assert (LRD2 : rdbl usegs mb a b) by (eapply (rdbl_transport usegs _ ma mb); [exact LRD | exact MUL | intros x Hx; left; cbn [outside]; unfold WILDCOPY_OVERLENGTH in *; split; [lia|exact I]]) end end;
  lazymatch type of MUL with munch _ ?ma ?mb => transport_after_call usegs ma mb MUL WML end;
  subst PO; try sn_modsmall;
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d6b0) _ _ ?mm _) => sn_frame_last FR; eapply (PLAST mm)
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d6e4) _ _ ?mm _) => sn_forgetc FR 248%nat ltac:(sn_c13); eapply (PEXIT mm _ (ZERR ZE_dstSize_tooSmall))
  end;
  first [ exact RG0 | exact SEP0 | exact FR | exact OSL
        | solve [match goal with MI : mem_inv usegs ?mm |- seqd_xinv _ ?mm _ => sn_xinv REP HH3 BUF STK MU WM MI end]
        | solve [eapply rdbl_sub; [exact LRD2| lia| unfold WILDCOPY_OVERLENGTH; lia]]
        | solve [left; reflexivity]
        | solve [unfold ZERR, ZE_dstSize_tooSmall; lia]
        | solve [unfold WILDCOPY_OVERLENGTH in *; lia]
        | solve [auto] ].

Lemma seq_none : forall (P : sdp) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word),
  seqd_mem P -> seqd_ranges P -> seqd_side P -> seqd_sep P -> q_nbSeq P = 0 ->
  evt usegs (seqd_post P)
    (MS (mkR (q_ra P) (Z_to_bv 64 (q_SPV P)) (q_gp P) (q_tp P) t0 t1 t2 (q_s0 P) (q_s1 P) (Z_to_bv 64 (q_DCTX P)) (Z_to_bv 64 (q_DST P))
             (Z_to_bv 64 (q_CAP P)) (Z_to_bv 64 (q_SEQ P)) (Z_to_bv 64 (zlen (q_sq P))) (Z_to_bv 64 (q_nbSeq P)) a6 a7
             (q_s2 P) (q_s3 P) (q_s4 P) (q_s5 P) (q_s6 P) (q_s7 P) (q_s8 P) (q_s9 P) (q_s10 P) (q_s11 P) t3 t4 t5 t6)
        (q_F P) (Z_to_bv 64 PZD_SEQ_DEFAULT) (q_fc P) None (q_m P) (seg_rom usegs)).
Proof.
  intros P t0 t1 t2 a6 a7 t3 t4 t5 t6 MEM RG SIDE SEP NB0.
  pose proof (p_lastcopy P) as PLAST. pose proof (p_exit P) as PEXIT. pose proof RG as RG0. pose proof SEP as SEP0.
  assert (FE0 : seqd_fe P = q_fe P) by (unfold seqd_fe; rewrite NB0; reflexivity). rewrite FE0 in PLAST, PEXIT.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_mem seqd_ranges seqd_side seqd_sep seqd_post seqd_saved q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in MEM, RG, SIDE, SEP, NB0 |- *.
  cbn [q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in PLAST, PEXIT.
  destruct MEM as ((PT & REP & HH1 & HH3 & HH5) & (L1 & L2 & L3 & L4) & SQB & BUF & LRD & STK & MI).
  destruct (h5_view m DCTX ws HH5) as (j1 & j2 & j3 & J1 & J2 & J3 & H5V). rewrite L1, L2, L3, L4 in H5V. clear HH5 L1 L2 L3 L4 J1 J2 J3 SQB.
  unfold dctx_ptrs, dctx_h1, dctx_h3 in *.
  unfold PZD_SEQ_DEFAULT, DCTX_entropy_rep, DCTX_fseEntropy in *. match goal with |- evt _ ?Q _ => set (PO := Q) end. subst nbSeq.
  assert (R0 : 544 <= SPV < 2^47 /\ 0 <= lo <= SPV - 544) by lia.
  assert (B00 : 0 <= B0) by (destruct BUF as (HB & _); exact HB).
  assert (RA : 4096 <= DCTX /\ DCTX + 95992 < 2^47 /\ 0 <= DST < 2^47 /\ 0 <= CAP < 2^47 /\ DST + CAP < 2^47 /\ 4096 <= LITP /\ 0 <= LITSZ < 2^32 /\ LITP + LITSZ < 2^47 /\ B0 <= DST /\ DST + CAP <= B1)
    by (unfold DCTX_SIZEOF, WILDCOPY_OVERLENGTH in RG; lia).
  assert (SEPL : SPV <= DCTX \/ DCTX + 95992 <= SPV - 352) by (unfold off_stack, DCTX_SIZEOF in *; lia).
  assert (SEPB : SPV <= B0 \/ B1 <= SPV - 352) by (unfold off_stack in *; lia).
  assert (SEPLIT : SPV <= LITP \/ LITP + LITSZ + 32 <= SPV - 352) by (unfold off_stack, WILDCOPY_OVERLENGTH in *; lia).
  assert (OSL : off_stack lo SPV LITP LITSZ) by (unfold off_stack, WILDCOPY_OVERLENGTH in *; lia).
  assert (LOC01 : LOC = 0 \/ LOC = 1) by (unfold ZSTD_not_in_dst, ZSTD_in_dst in SIDE; tauto).
  assert (RB : LOC = 1 -> DST <= LITB <= DST + CAP /\ LITB <= LITP) by (unfold ZSTD_in_dst in SIDE; tauto).
  assert (RC : LOC = 0 -> LITP + (LITSZ + 32) <= B0 \/ B1 <= LITP) by (unfold ZSTD_not_in_dst, apart, WILDCOPY_OVERLENGTH in SIDE; intros E; destruct SIDE as (_ & _ & _ & _ & _ & _ & _ & SL); specialize (SL E); lia).
  assert (DNN : DST <> 0 -> 4096 <= B0) by tauto.
  assert (DZ : DST = 0 -> CAP = 0) by tauto.
  assert (AL8 : rsk_al DCTX 8) by (constructor; destruct SIDE as (D8 & _); exact D8).
  clear RG SIDE SEP.
  assert (MU : munch [(DST, DST + CAP); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (SPV - 544, SPV)] m m) by apply munch_refl.
  assert (WM : wmono usegs m m) by apply wmono_refl.
  assert (MUL : munch [(SPV - 352, SPV)] m m) by apply munch_refl.
  carve_frame 352%nat STK.
  (* [comment removed for export] *)
  hold PT. hold REP. hold HH1. hold HH3. hold H5V. hold BUF. hold LRD. hold STK. hold RG0. hold SEP0. hold PLAST. hold PEXIT.
  hold RA. hold SEPL. hold SEPB. hold SEPLIT. hold OSL. hold RB. hold RC. hold DNN. hold DZ. hold B00.
  hold MU.
  kx_run [0x1caa0] 20%nat [KZRange SPV 544 (2^47); KZWr (SPV - 352) 352] [].
  kx_mem. unfold held in MU.
  unfold held in PT, REP, HH1, HH3, H5V, BUF, LRD, STK, SEPL, SEPB, SEPLIT.
  lazymatch type of MUL with munch _ _ ?m' => assert (LRD' : rdbl usegs m' LITP (LITP + LITSZ + WILDCOPY_OVERLENGTH)) by (eapply (rdbl_transport usegs _ m m'); [exact LRD | exact MUL | intros x Hx; left; cbn [outside]; unfold WILDCOPY_OVERLENGTH in *; split; [lia|exact I]]) end.
  lazymatch type of MUL with munch _ _ ?m' => transport_after_call usegs m m' MUL WM end.
  clear LRD MUL. rename LRD' into LRD.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (MUL : munch [(SPV - 352, SPV)] mm mm) by apply munch_refl; assert (WML : wmono usegs mm mm) by apply wmono_refl end.
  hold PT. hold REP. hold HH3. hold BUF. hold STK. hold LRD. hold SEPB. hold SEPLIT.
  unfold held in RA.
  destruct LOC01 as [LV|LV]; subst LOC; [destruct (Z.eq_dec CAP 0) as [C0|C0]; [rewrite C0|] |].
  - kx_autoLx [0x1d6b0; 0x1d6e4] 60%nat [KZRange SPV 544 (2^47); KZRange DCTX 4096 (2^47); KZRange DST 0 (2^47); KZRange LITP 4096 (2^47); KZRange LITSZ 0 (2^32); KZRange (LITP + LITSZ) 4096 (2^47); KZWr (SPV - 352) 352; KZDisj (SPV - 352) 352 DCTX 95992] [].
    all: sn_trap.
    all: sn_fin PLAST PEXIT MUL WML MU WM PO REP HH3 BUF STK LRD FR RG0 SEP0 OSL.
  - assert (D4 : 4096 <= DST) by (unfold held in DNN, DZ; destruct (Z.eq_dec DST 0) as [E|E]; [exfalso; apply C0; exact (DZ E) | specialize (DNN E); lia]).
    kx_autoLx [0x1d6b0; 0x1d6e4] 60%nat [KZRange SPV 544 (2^47); KZRange DCTX 4096 (2^47); KZRange DST 4096 (2^47); KZRange CAP 1 (2^47); KZRange (DST + CAP) 4096 (2^47); KZRange LITP 4096 (2^47); KZRange LITSZ 0 (2^32); KZRange (LITP + LITSZ) 4096 (2^47); KZWr (SPV - 352) 352; KZDisj (SPV - 352) 352 DCTX 95992] [].
    all: sn_trap.
    all: sn_fin PLAST PEXIT MUL WML MU WM PO REP HH3 BUF STK LRD FR RG0 SEP0 OSL.
  - unfold held in RB. specialize (RB eq_refl).
    kx_autoLx [0x1d6b0; 0x1d6e4] 60%nat [KZRange SPV 544 (2^47); KZRange DCTX 4096 (2^47); KZRange DST 0 (2^47); KZRange LITB 0 (2^47); KZRange (LITB - DST) 0 (2^47); KZRange LITP 4096 (2^47); KZRange LITSZ 0 (2^32); KZRange (LITP + LITSZ) 4096 (2^47); KZWr (SPV - 352) 352; KZDisj (SPV - 352) 352 DCTX 95992] [].
    all: sn_trap.
    all: sn_fin PLAST PEXIT MUL WML MU WM PO REP HH3 BUF STK LRD FR RG0 SEP0 OSL.
Qed.
