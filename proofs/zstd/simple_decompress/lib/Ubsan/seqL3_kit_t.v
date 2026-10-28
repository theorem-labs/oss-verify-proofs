(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_lkit2 RZ_seq_l_rkit seqL3_kit_dbs.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seql_linv_dbs : forall P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP,
  seql_static P OEND LLO LEND LOCV -> seql_linv P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  forall m2 D1 D2,
  munch [(D1, D2); (y_SPV P + -688 - 80, y_SPV P + -688)] m1 m2 -> wmono usegs m1 m2 -> mem_inv usegs m2 ->
  stk usegs m2 (y_B0 P) (y_B1 P) -> stk usegs m2 (y_lo P) (y_SPV P + -688) -> y_DST P <= D1 -> D2 <= OEND ->
  seql_linv P OEND LLO LEND LOCV m2 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP.
Proof.
  intros P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV m2 D1 D2 MUL WML MI2 BUF2 STK2 HD1 HD2.
  destruct INV as ((jpad & jseq & FR) & TLL & TOF & TML & SQB & LIT & XLIT & (H5V & H5L) & XI).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  unfold seql_linv. cbn [seql_static seql_xinv y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in *.
  sd_static_open ST. unfold held in S12, S18, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35.
  pose proof (tbl_len_LL _ OKLL) as LLL. pose proof (tbl_len_OF _ OKOF) as LOF. pose proof (tbl_len_ML _ OKML) as LML.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & MU & WM & MI1).
  unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation in *.
  split; [exists jpad, jseq; eapply rw_cells_transport; [exact FR | exact MUL | exact WML |]; cbn [seql_frame disjoint_from cells_size csize Nat.add]; split; [clear - S24 S18 S1 S2 S3 S4 S5 S6 HD1 HD2; lia| split; [clear; lia| exact I]]|].
  split; [eapply bytes_at_transport; [exact TLL | exact MUL | cbn [disjoint_from]; split; [clear - S33 S1 S2 S3 S4 S5 S6 HD1 HD2 LLL; lia| split; [clear - S28 S18 LLL; lia| exact I]]]|].
  split; [eapply bytes_at_transport; [exact TOF | exact MUL | cbn [disjoint_from]; split; [clear - S34 S1 S2 S3 S4 S5 S6 HD1 HD2 LOF; lia| split; [clear - S29 S18 LOF; lia| exact I]]]|].
  split; [eapply bytes_at_transport; [exact TML | exact MUL | cbn [disjoint_from]; split; [clear - S35 S1 S2 S3 S4 S5 S6 HD1 HD2 LML; lia| split; [clear - S30 S18 LML; lia| exact I]]]|].
  split; [eapply bytes_at_transport; [exact SQB | exact MUL | cbn [disjoint_from]; rewrite length_map; split; [clear - S31 S1 S2 S3 S4 S5 S6 HD1 HD2; lia| split; [clear - S25 S18; lia| exact I]]]|].
  split; [destruct S12 as [(A1 & A2)|A]; [eapply rdbl_sub; [eapply rdbl_of_stk; exact BUF2 | exact A1 | exact A2] | eapply rdbl_transport; [exact LIT | exact MUL | intros x Hx; left; cbn [outside]; split; [clear - A S1 S2 S3 S4 S5 S6 HD1 HD2 Hx; lia| split; [clear - S26 S18 Hx; lia| exact I]]]]|].
  split; [intros HL2; eapply rdbl_transport; [exact (XLIT HL2) | exact MUL | intros x Hx; left; cbn [outside]; split; [clear - S32 S1 S2 S3 S4 S5 S6 HD1 HD2 Hx; lia| split; [clear - S27 S18 Hx; lia| exact I]]]|].
  split; [split; [eapply rw_cells_transport; [exact H5V | exact MUL | exact WML | unfold h5_vcells; cbn [disjoint_from cells_size csize Nat.add]; split; [clear - S32 S1 S2 S3 S4 S5 S6 HD1 HD2; lia| split; [clear - S27 S18; lia| exact I]]] | exact H5L]|].
  split; [exists r0', r1', r2'; eapply rw_cells_transport; [exact REP | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - S32 S1 S2 S3 S4 S5 S6 HD1 HD2; lia| split; [clear - S27 S18; lia| exact I]]]|].
  split; [eapply rw_cells_transport; [exact HH3 | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - S32 S1 S2 S3 S4 S5 S6 HD1 HD2; lia| split; [clear - S27 S18; lia| exact I]]]|].
  split; [exact BUF2|].
  split; [exact STK2|].
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx HD1 HD2 S5; lia]|].
  split; [eapply wmono_trans; [exact WM | exact WML] | exact MI2].
Qed.

Definition seql_dbs_post (P : slp) (OEND LLO LEND LOCV : Z) (c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ seql_linv P OEND LLO LEND LOCV m' c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP.

Lemma seql_dbs_spec : forall P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP (D S n : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc,
  seql_static P OEND LLO LEND LOCV -> seql_linv P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  y_DST P <= D -> 0 <= n -> D + n <= OEND -> LLO <= S -> S + n <= LEND + 32 -> sp = Z_to_bv 64 (y_SPV P + -688) ->
  evt usegs (seql_dbs_post P OEND LLO LEND LOCV c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PZD_SAFECOPY_DBS) fc None m1 (seg_rom usegs)).
Proof.
  intros P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP D S n ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ST INV HD Hn HDn HS1 HS2 HSP. subst sp.
  pose proof (seql_linv_dbs P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV) as STEP.
  pose proof (seql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  pose proof (seql_copy_facts P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV) as (BUF & LIT & F1 & F2 & F3 & F4 & F5 & F6).
  assert (XF : stk usegs m1 (y_lo P) (y_SPV P + -688) /\ y_lo P <= y_SPV P + -688 - 80 /\ 0 <= y_SPV P + -688 < 2^47 /\
               off_stack (y_lo P) (y_SPV P + -688) (y_B0 P) (y_B1 P - y_B0 P) /\ off_stack (y_lo P) (y_SPV P + -688) LLO (LEND + 32 - LLO)).
  { destruct INV as (_ & _ & _ & _ & _ & _ & _ & _ & XI). clear - ST XI.
    destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
    cbn [seql_static seql_xinv y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in *.
    sd_static_open ST. unfold held in S18, S24, S26. unfold off_stack.
    destruct XI as (_ & _ & _ & STK & _).
    split; [exact STK|]. split; [clear - S18; lia|]. split; [clear - S17; lia|]. split; [clear - S24 S18; lia| clear - S26 S18; lia]. }
  destruct XF as (STK & XF1 & XF2 & XF3 & XF4).
  eapply evt_mono.
  - eapply (zd_safecopy_dbs_proof ra gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 (y_SPV P + -688) (y_lo P) D S n (y_B0 P) (y_B1 P) LLO (LEND + 32));
      first [ exact BUF | exact LIT | exact STK | exact MI | exact XF3 | exact XF4 | reflexivity | lia ].
  - intros ms' (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & STK' & BUF' & _).
    do 16 eexists. split; [reflexivity|]. eapply STEP; [exact MU | exact WM | exact MI' | exact BUF' | exact STK' | exact HD | lia].
Qed.

Ltac seql_ring_pre l :=
  lazymatch l with
  | CB 192 (seql_ring_bytes _ _ _) :: _ => constr:(@nil cell)
  | ?c :: ?rest => let p := seql_ring_pre rest in constr:(c :: p)
  end.
Ltac seql_ring_post l :=
  lazymatch l with
  | CB 192 (seql_ring_bytes _ _ _) :: ?post => post
  | _ :: ?rest => seql_ring_post rest
  end.
Ltac seql_ring_shape FR :=
  lazymatch type of FR with
  | rw_cells ?u ?mm ?A ?l =>
      let pre := seql_ring_pre l in let post := seql_ring_post l in
      lazymatch l with context [CB 192 (seql_ring_bytes ?rl ?rm ?ro)] =>
        change (rw_cells u mm A (pre ++ CB 192 (seql_ring_bytes rl rm ro) :: post)) in FR end
  end.

Ltac seql_take n l :=
  lazymatch n with
  | O => constr:(@nil cell)
  | S ?n' => lazymatch l with ?c :: ?r => let t := seql_take n' r in constr:(c :: t) end
  end.
Ltac seql_drop n l :=
  lazymatch n with
  | O => l
  | S ?n' => lazymatch l with _ :: ?r => seql_drop n' r end
  end.
Ltac seql_ring_reshape FR j :=
  lazymatch type of FR with
  | rw_cells ?u ?mm ?A ?l =>
      let pre := seql_take 46%nat l in let rest := seql_drop 46%nat l in
      let blk := seql_take j rest in let post := seql_drop j rest in
      change (rw_cells u mm A (pre ++ blk ++ post)) in FR
  end.

Ltac seql_ring_open k FR :=
  seql_ring_shape FR;
  lazymatch type of FR with context [CB 192 (seql_ring_bytes ?rl ?rm ?ro)] =>
  lazymatch k with
  | 0 => apply (seql_ring_open_0 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR
  | 1 => apply (seql_ring_open_1 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR
  | 2 => apply (seql_ring_open_2 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR
  | 3 => apply (seql_ring_open_3 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR
  | 4 => apply (seql_ring_open_4 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR
  | 5 => apply (seql_ring_open_5 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR
  | 6 => apply (seql_ring_open_6 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR
  | 7 => apply (seql_ring_open_7 _ _ _ _ rl rm ro _ _ _ eq_refl eq_refl eq_refl) in FR
  end end; cbn [app] in FR.

Ltac seql_ring_close k FR :=
  lazymatch k with
  | 0 => seql_ring_reshape FR 4%nat; apply seql_ring_close_0 in FR
  | 1 => seql_ring_reshape FR 5%nat; apply seql_ring_close_1 in FR
  | 2 => seql_ring_reshape FR 5%nat; apply seql_ring_close_2 in FR
  | 3 => seql_ring_reshape FR 5%nat; apply seql_ring_close_3 in FR
  | 4 => seql_ring_reshape FR 5%nat; apply seql_ring_close_4 in FR
  | 5 => seql_ring_reshape FR 5%nat; apply seql_ring_close_5 in FR
  | 6 => seql_ring_reshape FR 5%nat; apply seql_ring_close_6 in FR
  | 7 => seql_ring_reshape FR 4%nat; apply seql_ring_close_7 in FR
  end; cbn [app] in FR.

Ltac seql_ring_unopen k FR :=
  seql_ring_close k FR;
  lazymatch type of FR with context [seql_ring_bytes (ring_upd ?rl ?j ?a) (ring_upd ?rm ?j ?b) (ring_upd ?ro ?j ?d)] =>
    change (seql_ring_bytes (ring_upd rl j a) (ring_upd rm j b) (ring_upd ro j d)) with (seql_ring_bytes rl rm ro) in FR end.

Ltac seql_ring_close_any FR :=
  first [ seql_ring_close 0 FR | seql_ring_close 1 FR | seql_ring_close 2 FR | seql_ring_close 3 FR
        | seql_ring_close 4 FR | seql_ring_close 5 FR | seql_ring_close 6 FR | seql_ring_close 7 FR ].

Ltac seql_ring_unopen_any FR :=
  first [ seql_ring_unopen 0 FR | seql_ring_unopen 1 FR | seql_ring_unopen 2 FR | seql_ring_unopen 3 FR
        | seql_ring_unopen 4 FR | seql_ring_unopen 5 FR | seql_ring_unopen 6 FR | seql_ring_unopen 7 FR ].

Ltac seql_yred := cbn [y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws].

Ltac seql_ring_open_eq k FR E1 E2 E3 :=
  seql_ring_shape FR;
  lazymatch k with
  | 0 => apply (seql_ring_open_0 _ _ _ _ _ _ _ _ _ _ E1 E2 E3) in FR
  | 1 => apply (seql_ring_open_1 _ _ _ _ _ _ _ _ _ _ E1 E2 E3) in FR
  | 2 => apply (seql_ring_open_2 _ _ _ _ _ _ _ _ _ _ E1 E2 E3) in FR
  | 3 => apply (seql_ring_open_3 _ _ _ _ _ _ _ _ _ _ E1 E2 E3) in FR
  | 4 => apply (seql_ring_open_4 _ _ _ _ _ _ _ _ _ _ E1 E2 E3) in FR
  | 5 => apply (seql_ring_open_5 _ _ _ _ _ _ _ _ _ _ E1 E2 E3) in FR
  | 6 => apply (seql_ring_open_6 _ _ _ _ _ _ _ _ _ _ E1 E2 E3) in FR
  | 7 => apply (seql_ring_open_7 _ _ _ _ _ _ _ _ _ _ E1 E2 E3) in FR
  end; cbn [app] in FR.

Ltac seql_dbs_intro INV :=
  let ms' := fresh "ms'" in
  intros ms' (?u0 & ?u1 & ?u2 & ?b0 & ?b1 & ?b2 & ?b3 & ?b4 & ?b5 & ?b6 & ?b7 & ?u3 & ?u4 & ?u5 & ?u6 & ?m' & -> & INV);
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
