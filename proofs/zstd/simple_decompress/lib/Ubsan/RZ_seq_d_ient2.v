(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdCellKit ZdDctxRep ZdSeqW KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_d_base RZ_seq_d_lbase RZ_seq_d_lkit RZ_seq_d_ibase RZ_seq_d_ient huf411_kit_rs seqS_kit_al seqD_kit_d_entz.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac sde_cb8_pre cs :=
  lazymatch cs with
  | CB 8 _ :: _ => constr:(@nil cell)
  | ?c :: ?rest => let p := sde_cb8_pre rest in constr:(c :: p)
  end.

Lemma seqd_pf8 : forall (m : fmem) A j (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word),
  rw_cells usegs m A (CB 248 j :: [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) ->
  exists c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 jbd u144 u152 u160 u168 u176 u184 c192 c200 c208 c216 jseq,
    rw_cells usegs m A [C8 c0; C8 c8; C8 c16; C8 c24; C8 c32; C8 c40; C8 c48; C8 c56; C8 c64; C8 c72; C8 c80; C8 c88; C8 c96; CB 40 jbd;
      C8 u144; C8 u152; C8 u160; C8 u168; C8 u176; C8 u184; C8 c192; C8 c200; C8 c208; C8 c216; CB 24 jseq;
      CB 104 (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++ le8 s1 ++ le8 s0 ++ le8 ra)].
Proof.
  intros m A j s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra FR.
  change (rw_cells usegs m A ([CB 248 j] ++ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ++ [])) in FR.
  apply rw_cells_merge in FR. cbn [cells_size csize Nat.add cells_bytes cbytes] in FR. rewrite !app_nil_r in FR.
  change (rw_cells usegs m A ([] ++ CB 248 j :: [CB 104 (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++ le8 s1 ++ le8 s0 ++ le8 ra)])) in FR.
  apply (rw_cells_split_CB usegs m A [] 248 j _ [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 40; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 24]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat lazymatch type of FR with rw_cells _ ?mm ?AA ?cs =>
    let pre := sde_cb8_pre cs in
    let w := fresh "w" in let FR' := fresh "FR" in
    destruct (cb8_as_c8 usegs mm AA pre _ _ FR) as (w & FR'); cbn [app] in FR'; clear FR; rename FR' into FR end.
  do 25 eexists. exact FR.
Qed.

Lemma sde_iinv_eq : forall P LEND m1 fr fr', seqd_iinv P LEND m1 fr -> fr = fr' -> seqd_iinv P LEND m1 fr'.
Proof. intros P LEND m1 fr fr' H E. subst fr'. exact H. Qed.

Ltac sde_iinv FR PT TLL TOF TML SQB LRD2 FE1 REP HH3 BUF STK MU WM :=
  eapply sde_iinv_eq;
  [ unfold seqd_iinv; cbn [q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws];
    split; [exact FR|]; split; [unfold dctx_ptrs; exact PT|]; split; [exact TLL|]; split; [exact TOF|]; split; [exact TML|]; split; [exact SQB|];
    split; [eapply rdbl_sub; [exact LRD2 | lia | unfold WILDCOPY_OVERLENGTH; lia]|];
    cbn [seqd_xinv]; rewrite FE1; unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy;
    split; [do 3 eexists; exact REP|]; split; [exact HH3|]; split; [exact BUF|]; split; [exact STK|]; split; [exact MU|];
    split; [exact WM| lazymatch goal with MIx : mem_inv usegs ?mm |- mem_inv usegs ?mm => exact MIx end]
  | unfold seqd_ifr, seqd_ifr_hd, seqd_ifr_tl;
    cbn [app q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws];
    repeat (lazymatch goal with |- cons _ _ = cons _ _ => f_equal | |- C8 _ = C8 _ => f_equal end); f_equal; lia ].

Lemma seqd_entry : forall (P : sdp) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word),
  seqd_mem P -> seqd_ranges P -> seqd_side P -> seqd_sep P -> seqd_tables P -> q_nbSeq P <> 0 ->
  q_SPV P mod 16 = 0 -> (q_LLT P mod 4 = 0 /\ q_OFT P mod 4 = 0 /\ q_MLT P mod 4 = 0) ->
  (forall OEND LEND, seqd_static P OEND LEND -> ai_1ac P OEND LEND) ->
  evt usegs (seqd_post P)
    (MS (mkR (q_ra P) (Z_to_bv 64 (q_SPV P)) (q_gp P) (q_tp P) t0 t1 t2 (q_s0 P) (q_s1 P) (Z_to_bv 64 (q_DCTX P)) (Z_to_bv 64 (q_DST P))
             (Z_to_bv 64 (q_CAP P)) (Z_to_bv 64 (q_SEQ P)) (Z_to_bv 64 (zlen (q_sq P))) (Z_to_bv 64 (q_nbSeq P)) a6 a7
             (q_s2 P) (q_s3 P) (q_s4 P) (q_s5 P) (q_s6 P) (q_s7 P) (q_s8 P) (q_s9 P) (q_s10 P) (q_s11 P) t3 t4 t5 t6)
        (q_F P) (Z_to_bv 64 PZD_SEQ_DEFAULT) (q_fc P) None (q_m P) (seg_rom usegs)).
Proof.
  intros P t0 t1 t2 a6 a7 t3 t4 t5 t6 MEM RG SIDE SEP TBL NZ AL16 AL4 CONT.
  pose proof (rsk_al_i _ _ AL16) as ALSP. destruct AL4 as (A1 & A2 & A3).
  pose proof (rsk_al_i _ _ A1) as ALLL. pose proof (rsk_al_i _ _ A2) as ALOF. pose proof (rsk_al_i _ _ A3) as ALML. clear AL16 A1 A2 A3.
  assert (CONT2 : forall OEND, ((q_LOC P = 0 /\ OEND = q_DST P + q_CAP P) \/ (q_LOC P = 1 /\ OEND = q_LITB P)) -> ai_1ac P OEND (q_LITP P + q_LITSZ P)).
  { intros OEND HO. destruct (Z.eq_dec (zlen (q_sq P)) 0) as [Z0|N0].
    - exact (seqd_ai1ac_z0 P OEND _ RG SEP TBL Z0 (rsk_al_e _ _ ALSP) eq_refl).
    - apply CONT. apply seqd_static_intro;
        [exact RG | exact SIDE | exact SEP | exact TBL | exact NZ | clear - N0; lia | exact (rsk_al_e _ _ ALSP)
        | exact (conj (rsk_al_e _ _ ALLL) (conj (rsk_al_e _ _ ALOF) (rsk_al_e _ _ ALML))) | reflexivity | exact HO]. }
  clear CONT ALSP ALLL ALOF ALML.
  pose proof RG as RG0. pose proof SEP as SEP0.
  assert (FE1 : seqd_fe P = Z_to_bv 64 1) by (unfold seqd_fe; destruct (Z.eqb_spec (q_nbSeq P) 0); [contradiction|reflexivity]).
  unfold ai_1ac in CONT2.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_mem seqd_ranges seqd_side seqd_sep seqd_tables seqd_post seqd_saved q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in MEM, RG, SIDE, SEP, TBL, NZ |- *.
  destruct MEM as ((PT & REP & HH1 & HH3 & HH5) & (L1 & L2 & L3 & L4) & SQB & BUF & LRD & STK & MI).
  destruct (h5_view m DCTX ws HH5) as (j1 & j2 & j3 & J1 & J2 & J3 & H5V). rewrite L1, L2, L3, L4 in H5V. clear HH5 L1 L2 L3 L4 J1 J2 J3.
  destruct TBL as ((TLL & O1) & (TOF & O2) & (TML & O3) & TR).
  unfold dctx_ptrs, dctx_h1, dctx_h3 in *.
  unfold PZD_SEQ_DEFAULT, DCTX_entropy_rep, DCTX_fseEntropy in *.
  assert (LSQ : Z.of_nat (length (map (Z_to_bv 8) sq)) = zlen sq) by (rewrite length_map; reflexivity).
  assert (DN : DST <> 0) by (intros E; destruct SIDE as (_ & _ & D3 & _); destruct (D3 E) as (_ & E2); contradiction).
  assert (RA : 544 <= SPV < 2^47 /\ 0 <= lo <= SPV - 544 /\ 4096 <= DCTX /\ DCTX + 95992 < 2^47 /\ 4096 <= DST < 2^47 /\ 0 <= CAP < 2^47 /\ DST + CAP < 2^47 /\
               4096 <= LITP /\ 0 <= LITSZ < 2^32 /\ LITP + LITSZ < 2^47 /\ 1 <= nbSeq <= 98047 /\ 0 <= zlen sq < 2^47 /\ 4096 <= SEQ < 2^47)
    by (unfold DCTX_SIZEOF, WILDCOPY_OVERLENGTH in RG; destruct SIDE as (_ & _ & _ & D4 & _); specialize (D4 DN); destruct BUF as (HB & _); lia).
  assert (LOC01 : LOC = 0 \/ LOC = 1) by (unfold ZSTD_not_in_dst, ZSTD_in_dst in SIDE; tauto).
  assert (RB : LOC = 1 -> DST <= LITB <= DST + CAP) by (unfold ZSTD_in_dst in SIDE; tauto).
  assert (AL8 : rsk_al DCTX 8) by (constructor; destruct SIDE as (D8 & _); exact D8).
  destruct TR as (_ & _ & _ & T7 & T8 & T9 & _ & _ & _ & T13 & T14 & T15). destruct SEP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  unfold off_stack, apart, DCTX_SIZEOF, WILDCOPY_OVERLENGTH, DCTX_litExtraBuffer in P1, P2, P3, P4, P5, P6, P7, P8, T7, T8, T9, T13, T14, T15.
  assert (X1 : SPV <= DCTX \/ DCTX + 95992 <= lo) by (clear - P1 RA; lia).
  assert (X2 : SPV <= B0 \/ B1 <= SPV - 352) by (clear - P2 RA; lia).
  assert (X3 : SPV <= LITP \/ LITP + LITSZ + 32 <= SPV - 352) by (clear - P4 RA; lia).
  assert (X4 : SPV <= SEQ \/ SEQ + zlen sq <= SPV - 352) by (clear - P3 RA; lia).
  assert (X5 : SPV <= LLT \/ LLT + 4104 <= SPV - 352) by (clear - T7 RA; lia).
  assert (X6 : SPV <= OFT \/ OFT + 2056 <= SPV - 352) by (clear - T8 RA; lia).
  assert (X7 : SPV <= MLT \/ MLT + 4104 <= SPV - 352) by (clear - T9 RA; lia).
  assert (X8 : B1 <= DCTX \/ DCTX + 95992 <= B0) by (clear - P5; lia).
  assert (X9 : SEQ + zlen sq <= DCTX + 26684 \/ DCTX + 95992 <= SEQ) by (clear - P7; lia).
  assert (X10 : LITP + LITSZ + 32 <= DCTX + 26684 \/ DCTX + 30372 <= LITP) by (clear - P8; lia).
  assert (X11 : LLT + 4104 <= DCTX + 26684 \/ DCTX + 95992 <= LLT) by (clear - T13; lia).
  assert (X12 : OFT + 2056 <= DCTX + 26684 \/ DCTX + 95992 <= OFT) by (clear - T14; lia).
  assert (X13 : MLT + 4104 <= DCTX + 26684 \/ DCTX + 95992 <= MLT) by (clear - T15; lia).
  pose proof (tbl_len_LL _ O1) as LLL. pose proof (tbl_len_OF _ O2) as LOF. pose proof (tbl_len_ML _ O3) as LML. clear O1 O2 O3.
  clear RG SIDE P1 P2 P3 P4 P5 P6 P7 P8 T7 T8 T9 T13 T14 T15.
  assert (MU : munch [(DST, DST + CAP); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (SPV - 544, SPV)] m m) by apply munch_refl.
  assert (WM : wmono usegs m m) by apply wmono_refl.
  assert (MUL : munch [(SPV - 352, SPV)] m m) by apply munch_refl.
  assert (R0 : 544 <= SPV < 2^47 /\ 0 <= lo <= SPV - 544) by (clear - RA; lia).
  carve_frame 352%nat STK.
  (* [comment removed for export] *)
  hold PT. hold REP. hold HH1. hold HH3. hold H5V. hold BUF. hold LRD. hold STK. hold TLL. hold TOF. hold TML. hold SQB.
  hold RG0. hold SEP0. hold CONT2. hold RA. hold RB. hold MU.
  hold X1. hold X2. hold X3. hold X4. hold X5. hold X6. hold X7. hold X8. hold X9. hold X10. hold X11. hold X12. hold X13.
  kx_run [0x1caa0] 20%nat [KZRange SPV 544 (2^47); KZWr (SPV - 352) 352] [].
  kx_mem. unfold held in MU.
  unfold held in PT, REP, HH1, HH3, H5V, BUF, LRD, STK, TLL, TOF, TML, SQB, X1, X2, X3, X4, X5, X6, X7.
  lazymatch type of MUL with munch _ _ ?m' => assert (LRD' : rdbl usegs m' LITP (LITP + LITSZ + WILDCOPY_OVERLENGTH)) by (eapply (rdbl_transport usegs _ m m'); [exact LRD | exact MUL | intros x Hx; left; cbn [outside]; unfold WILDCOPY_OVERLENGTH in *; split; [lia|exact I]]) end.
  lazymatch type of MUL with munch _ _ ?m' => transport_after_call usegs m m' MUL WM end.
  clear LRD MUL. rename LRD' into LRD.
  apply seqd_pf8 in FR. destruct FR as (j_c0 & j_c8 & j_c16 & j_c24 & j_c32 & j_c40 & j_c48 & j_c56 & j_c64 & j_c72 & j_c80 & j_c88 & j_c96 & jbd & j_u144 & j_u152 & j_u160 & j_u168 & j_u176 & j_u184 & j_p0 & j_p1 & j_p2 & j_c216 & jseq & FR).
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (MUL : munch [(DCTX + 30004, DCTX + 30004 + 4); (SPV - 352, SPV)] mm mm) by apply munch_refl; assert (WML : wmono usegs mm mm) by apply wmono_refl end.
  unfold held in X8, X9, X10, X11, X12, X13.
  hold PT. hold BUF. hold STK. hold LRD. hold TLL. hold TOF. hold TML. hold SQB. hold MU. hold WM.
  hold X2. hold X3. hold X4. hold X5. hold X6. hold X7. hold X8. hold X9. hold X10. hold X11. hold X12. hold X13.
  unfold held in RA.
  destruct LOC01 as [LV|LV]; subst LOC; [destruct (Z.eq_dec CAP 0) as [C0|C0]; [subst CAP|] |].
  - kx_autoLx [0x1d904] 80%nat
      [KZRange SPV 544 (2^47); KZRange DCTX 4096 (2^47); KZRange DST 4096 (2^47); KZRange LITP 4096 (2^47); KZRange LITSZ 0 (2^32);
       KZRange (LITP + LITSZ) 4096 (2^47); KZRange nbSeq 1 98047; KZRange (zlen sq) 0 (2^47); KZRange SEQ 4096 (2^47);
       KZWr (SPV - 352) 352; KZWr (DCTX + 29976) 32; KZDisj (SPV - 352) 352 DCTX 95992]
      [].
    all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d724) _ _ _ _) => first [kx_trap_fast | seqs_land_close | rsk_unkeep; seqs_land_close] end).
    all: kx_mem; unfold held in LRD, X3, X10;
      lazymatch type of MUL with munch _ ?ma ?mb =>
        assert (LRD2 : rdbl usegs mb LITP (LITP + LITSZ + WILDCOPY_OVERLENGTH)) by (eapply (rdbl_transport usegs _ ma mb); [exact LRD | exact MUL | intros x Hx; left; cbn [outside]; unfold WILDCOPY_OVERLENGTH in *; split; [lia| split; [lia|exact I]]]) end;
      unfold held in *;
      lazymatch type of MUL with munch _ ?ma ?mb => transport_after_call usegs ma mb MUL WML end.
    all: try replace (SPV + -352 + 104) with (SPV + -248) by lia.
    all: eapply (CONT2 DST); [cbn [q_LOC q_DST q_CAP q_LITB]; left; split; [reflexivity | lia] | sde_iinv FR PT TLL TOF TML SQB LRD2 FE1 REP HH3 BUF STK MU WM].
  - kx_autoLx [0x1d904] 80%nat
      [KZRange SPV 544 (2^47); KZRange DCTX 4096 (2^47); KZRange DST 4096 (2^47); KZRange CAP 1 (2^47); KZRange (DST + CAP) 4096 (2^47); KZRange LITP 4096 (2^47); KZRange LITSZ 0 (2^32);
       KZRange (LITP + LITSZ) 4096 (2^47); KZRange nbSeq 1 98047; KZRange (zlen sq) 0 (2^47); KZRange SEQ 4096 (2^47);
       KZWr (SPV - 352) 352; KZWr (DCTX + 29976) 32; KZDisj (SPV - 352) 352 DCTX 95992]
      [].
    all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d724) _ _ _ _) => first [kx_trap_fast | seqs_land_close | rsk_unkeep; seqs_land_close] end).
    all: kx_mem; unfold held in LRD, X3, X10;
      lazymatch type of MUL with munch _ ?ma ?mb =>
        assert (LRD2 : rdbl usegs mb LITP (LITP + LITSZ + WILDCOPY_OVERLENGTH)) by (eapply (rdbl_transport usegs _ ma mb); [exact LRD | exact MUL | intros x Hx; left; cbn [outside]; unfold WILDCOPY_OVERLENGTH in *; split; [lia| split; [lia|exact I]]]) end;
      unfold held in *;
      lazymatch type of MUL with munch _ ?ma ?mb => transport_after_call usegs ma mb MUL WML end.
    all: try replace (SPV + -352 + 104) with (SPV + -248) by lia.
    all: eapply (CONT2 (DST + CAP)); [cbn [q_LOC q_DST q_CAP q_LITB]; left; split; [reflexivity | lia] | sde_iinv FR PT TLL TOF TML SQB LRD2 FE1 REP HH3 BUF STK MU WM].
  - unfold held in RB. specialize (RB eq_refl).
    kx_autoLx [0x1d904] 80%nat
      [KZRange SPV 544 (2^47); KZRange DCTX 4096 (2^47); KZRange DST 4096 (2^47); KZRange LITB 4096 (2^47); KZRange LITP 4096 (2^47); KZRange LITSZ 0 (2^32);
       KZRange (LITP + LITSZ) 4096 (2^47); KZRange nbSeq 1 98047; KZRange (zlen sq) 0 (2^47); KZRange SEQ 4096 (2^47);
       KZWr (SPV - 352) 352; KZWr (DCTX + 29976) 32; KZDisj (SPV - 352) 352 DCTX 95992]
      [].
    all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d724) _ _ _ _) => first [kx_trap_fast | seqs_land_close | rsk_unkeep; seqs_land_close] end).
    all: kx_mem; unfold held in LRD, X3, X10;
      lazymatch type of MUL with munch _ ?ma ?mb =>
        assert (LRD2 : rdbl usegs mb LITP (LITP + LITSZ + WILDCOPY_OVERLENGTH)) by (eapply (rdbl_transport usegs _ ma mb); [exact LRD | exact MUL | intros x Hx; left; cbn [outside]; unfold WILDCOPY_OVERLENGTH in *; split; [lia| split; [lia|exact I]]]) end;
      unfold held in *;
      lazymatch type of MUL with munch _ ?ma ?mb => transport_after_call usegs ma mb MUL WML end.
    all: try replace (SPV + -352 + 104) with (SPV + -248) by lia.
    all: eapply (CONT2 LITB); [cbn [q_LOC q_DST q_CAP q_LITB]; right; split; [reflexivity | lia] | sde_iinv FR PT TLL TOF TML SQB LRD2 FE1 REP HH3 BUF STK MU WM].
Qed.
