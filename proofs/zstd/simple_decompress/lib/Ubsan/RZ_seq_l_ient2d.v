(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_ibase RZ_seq_l_iexit RZ_seq_l_ient.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma seql_entry_d : forall (P : slp) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word),
  seql_mem P -> seql_ranges P -> seql_side P -> seql_sep P -> seql_tables P -> y_nbSeq P <> 0 -> y_LOC P = 2 ->
  (forall OEND, (1 <= zlen (y_sq P) -> seql_static P OEND (y_LITP P) (y_LBE P) (y_LOC P)) -> ai_i0 P OEND (y_LITP P) (y_LBE P) (y_LOC P)) ->
  evt usegs (seql_post P)
    (MS (mkR (y_ra P) (Z_to_bv 64 (y_SPV P)) (y_gp P) (y_tp P) t0 t1 t2 (y_s0 P) (y_s1 P) (Z_to_bv 64 (y_DCTX P)) (Z_to_bv 64 (y_DST P))
             (Z_to_bv 64 (y_CAP P)) (Z_to_bv 64 (y_SEQ P)) (Z_to_bv 64 (zlen (y_sq P))) (Z_to_bv 64 (y_nbSeq P)) a6 a7
             (y_s2 P) (y_s3 P) (y_s4 P) (y_s5 P) (y_s6 P) (y_s7 P) (y_s8 P) (y_s9 P) (y_s10 P) (y_s11 P) t3 t4 t5 t6)
        (y_F P) (Z_to_bv 64 0x17a94) (y_fc P) None (y_m P) (seg_rom usegs)).
Proof.
  intros P t0 t1 t2 a6 a7 t3 t4 t5 t6 MEM RG SIDE SEP TBL NZ HC CONT.
  pose proof RG as RG0. pose proof SIDE as SIDE0. pose proof SEP as SEP0. pose proof TBL as TBL0.
  assert (FE1 : seql_fe P = Z_to_bv 64 1) by (unfold seql_fe; destruct (Z.eqb_spec (y_nbSeq P) 0); [contradiction|reflexivity]).
  unfold ai_i0 in CONT.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_mem seql_ranges seql_side seql_sep seql_tables seql_post seql_saved y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in MEM, RG, SIDE, SEP, TBL, NZ, HC, CONT |- *.
  destruct MEM as ((PT & REP & HH1 & HH3 & HH5) & (L1 & L2 & L3 & L4) & SQB & BUF & LRD & STK & MI).
  destruct (h5_view2 m DCTX ws HH5) as (H5O & H5L). pose proof H5O as H5V. unfold h5_vcells in H5V, H5O. rewrite L4 in H5O. rewrite L1, L2, L3, L4 in H5V. clear HH5 L1 L2 L3 L4.
  destruct TBL as ((TLL & _) & (TOF & _) & (TML & _) & TR).
  unfold dctx_ptrs, dctx_h1, dctx_h3 in *.
  unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation in *.
  assert (LSQ : Z.of_nat (length (map (Z_to_bv 8) sq)) = zlen sq) by (rewrite length_map; reflexivity).
  assert (RA : 896 <= SPV < 2^47 /\ 0 <= lo <= SPV - 896 /\ 4096 <= DCTX /\ DCTX + 95992 < 2^47 /\ 4096 <= DST < 2^47 /\ 0 <= CAP < 2^47 /\ 4096 <= DST + CAP < 2^47 /\
               4096 <= LITP < 2^47 /\ 4096 <= LBE < 2^47 /\ 1 <= nbSeq <= 98047 /\ 0 <= zlen sq < 2^47 /\ 4096 <= SEQ < 2^47)
    by (unfold DCTX_SIZEOF, WILDCOPY_OVERLENGTH in RG; lia).
  destruct TR as (_ & _ & _ & T7 & T8 & T9 & _ & _ & _ & T13 & T14 & T15). destruct SEP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  unfold off_stack, apart, DCTX_SIZEOF, WILDCOPY_OVERLENGTH, DCTX_litExtraBuffer in P1, P2, P3, P4, P5, P6, P7, P8, T7, T8, T9, T13, T14, T15.
  assert (X1 : SPV <= DCTX \/ DCTX + 95992 <= lo) by (clear - P1 RA; lia).
  assert (X2 : SPV <= B0 \/ B1 <= SPV - 688) by (clear - P2 RA; lia).
  assert (X3 : SPV <= LITP \/ LBE + 32 <= SPV - 688) by (clear - P4 RA; lia).
  assert (X4 : SPV <= SEQ \/ SEQ + zlen sq <= SPV - 688) by (clear - P3 RA; lia).
  assert (X5 : SPV <= LLT \/ LLT + 4104 <= SPV - 688) by (clear - T7 RA; lia).
  assert (X6 : SPV <= OFT \/ OFT + 2056 <= SPV - 688) by (clear - T8 RA; lia).
  assert (X7 : SPV <= MLT \/ MLT + 4104 <= SPV - 688) by (clear - T9 RA; lia).
  assert (X8 : B1 <= DCTX \/ DCTX + 95992 <= B0) by (clear - P5; lia).
  assert (X9 : SEQ + zlen sq <= DCTX + 26684 \/ DCTX + 95992 <= SEQ) by (clear - P7; lia).
  assert (X11 : LLT + 4104 <= DCTX + 26684 \/ DCTX + 95992 <= LLT) by (clear - T13; lia).
  assert (X12 : OFT + 2056 <= DCTX + 26684 \/ DCTX + 95992 <= OFT) by (clear - T14; lia).
  assert (X13 : MLT + 4104 <= DCTX + 26684 \/ DCTX + 95992 <= MLT) by (clear - T15; lia).
  (* [comment removed for export] *)
  assert (X10F : LOC <> 2 -> LBE + 32 <= DCTX + 26684 \/ DCTX + 30372 <= LITP) by (intros HN2; unfold ZSTD_split in P8; specialize (P8 HN2); clear - P8; lia).
  assert (PLS : LOC = 2 -> (LBE + 32 <= DCTX + 26684 \/ DCTX + 30372 <= LITP) /\ 32 <= CAP /\ rdbl usegs m (DCTX + 30372) (DCTX + 95940)).
  { intros E2. destruct SIDE as (_ & _ & _ & _ & D5). unfold seq_lit_placed, ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split, WILDCOPY_OVERLENGTH, DCTX_litExtraBuffer, DCTX_litExtraBuffer_sz in D5.
    destruct D5 as [(E & _)|[(E & _)|(_ & A & B & C)]]; [exfalso; lia | exfalso; lia |]. split; [clear - P5 A B RG; lia|]. split; [clear - A B RG RA; lia|]. replace (DCTX + 95940) with (DCTX + 30372 + 65568) by lia. exact C. }
  assert (PLB : LOC = 1 -> 4096 <= LITB < 2^47) by (intros E1; destruct SIDE as (_ & _ & _ & _ & D5); unfold seq_lit_placed, ZSTD_not_in_dst, ZSTD_in_dst, ZSTD_split in D5; destruct D5 as [(E & _)|[(_ & A & _)|(E & _)]]; [exfalso; lia | clear - A RA; lia | exfalso; lia]).
  assert (DAL : DCTX mod 8 = 0) by (destruct SIDE as (D1 & _); exact D1).
  pose proof HC as LOCK. clear HC.
  assert (TLS : Z.of_nat (length (map (Z_to_bv 8) (seq_table_bytes tLL))) <= 4104 /\ Z.of_nat (length (map (Z_to_bv 8) (seq_table_bytes tOF))) <= 2056 /\ Z.of_nat (length (map (Z_to_bv 8) (seq_table_bytes tML))) <= 4104)
    by (destruct TBL0 as ((_ & O1) & (_ & O2) & (_ & O3) & _); split; [apply tbl_len_LL; exact O1| split; [apply tbl_len_OF; exact O2 | apply tbl_len_ML; exact O3]]).
  destruct TLS as (LLL & LOF & LML).
  clear RG SIDE P1 P2 P3 P4 P5 P6 P7 P8 T7 T8 T9 T13 T14 T15.
  assert (MU : munch [(DST, DST + CAP); (DCTX + 26684, DCTX + 26684 + 12); (DCTX + 30004, DCTX + 30004 + 4); (DCTX + 30368, DCTX + 30368 + 4); (SPV - 896, SPV)] m m) by apply munch_refl.
  assert (WM : wmono usegs m m) by apply wmono_refl.
  assert (MUL : munch [(SPV - 688, SPV)] m m) by apply munch_refl.
  assert (R0 : 896 <= SPV < 2^47 /\ 0 <= lo <= SPV - 896) by (clear - RA; lia).
  carve_frame 688%nat STK.
  (* [comment removed for export] *)
  hold PT. hold REP. hold HH1. hold HH3. hold H5V. hold H5O. hold BUF. hold LRD. hold PLS. hold PLB. hold X10F. hold LOCK. hold STK. hold TLL. hold TOF. hold TML. hold SQB.
  hold RG0. hold SIDE0. hold SEP0. hold TBL0. hold CONT. hold RA. hold MU.
  hold X1. hold X2. hold X3. hold X4. hold X5. hold X6. hold X7. hold X8. hold X9. hold X11. hold X12. hold X13.
  kx_run [0x17acc] 20%nat [KZRange SPV 896 (2^47); KZWr (SPV - 688) 688] [].
  kx_mem. unfold held in MU.
  unfold held in PT, REP, HH1, HH3, H5V, H5O, BUF, LRD, STK, TLL, TOF, TML, SQB, X1, X2, X3, X4, X5, X6, X7.
  lazymatch type of MUL with munch _ _ ?m' => assert (LRD' : rdbl usegs m' LITP (LBE + WILDCOPY_OVERLENGTH)) by (eapply (rdbl_transport usegs _ m m'); [exact LRD | exact MUL | intros x Hx; left; cbn [outside]; unfold WILDCOPY_OVERLENGTH in *; split; [lia|exact I]]) end.
  lazymatch type of MUL with munch _ _ ?m' => assert (PLS' : LOC = 2 -> (LBE + 32 <= DCTX + 26684 \/ DCTX + 30372 <= LITP) /\ 32 <= CAP /\ rdbl usegs m' (DCTX + 30372) (DCTX + 95940))
    by (intros E2; pose proof PLS as PLSu; unfold held in PLSu; destruct (PLSu E2) as (A & B & XL); split; [exact A|]; split; [exact B|]; eapply (rdbl_transport usegs _ m m'); [exact XL | exact MUL | intros x Hx; left; cbn [outside]; split; [lia|exact I]]) end.
  lazymatch type of MUL with munch _ _ ?m' => transport_after_call usegs m m' MUL WM end.
  clear LRD PLS MUL. rename LRD' into LRD. rename PLS' into PLS. unfold WILDCOPY_OVERLENGTH in LRD.
  apply seql_prologue_frame in FR. destruct FR as (w_c0 & w_c8 & w_c16 & w_c24 & w_c32 & w_c40 & w_c48 & w_c56 & w_c64 & w_c72 & w_c80 & w_c88 & w_c96 & w_c104 & w_c112 & w_c120 & w_c128 & w_c136 & w_c144 & w_c152 & w_c160 & w_c168 & w_c176 & w_c184 & w_c192 & w_c200 & w_c208 & w_c216 & w_c224 & w_c232 & w_c240 & jbd & w_u288 & w_u296 & w_u304 & w_u312 & w_u320 & w_u328 & w_c336 & w_c344 & w_c352 & jring & w_c552 & jseq & FR).
  cbn [app] in FR.
  unfold held in X8, X9, X11, X12, X13, PLB, X10F, LOCK. try unfold held in RA.
  rename LOCK into LV.
  subst LOC. destruct (PLS eq_refl) as (X10 & C32 & XLIT2S). lazymatch type of LRD with rdbl _ ?mc _ _ => assert (XLITC : 2 = 2 -> rdbl usegs mc (DCTX + 30372) (DCTX + 95940)) by (intros _; exact XLIT2S) end. clear PLS PLB X10F XLIT2S.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (MUL : munch [(DCTX + 30004, DCTX + 30004 + 4); (SPV - 688, SPV)] mm mm) by apply munch_refl; assert (WML : wmono usegs mm mm) by apply wmono_refl end.
  hold PT. hold BUF. hold STK. hold LRD. hold XLITC. hold TLL. hold TOF. hold TML. hold SQB. hold MU. hold WM. hold H5O.
  hold X2. hold X3. hold X4. hold X5. hold X6. hold X7. hold X8. hold X9. hold X10. hold X11. hold X12. hold X13.
    kx_autoLx [0x1d904; 0x1ac04] 100%nat
    [KZRange SPV 896 (2^47); KZRange DCTX 4096 (2^47); KZRange DST 4096 (2^47); KZRange CAP 32 (2^47); KZRange (DST + CAP) 4096 (2^47); KZRange LITP 4096 (2^47); KZRange LBE 4096 (2^47);
     KZRange nbSeq 1 98047; KZRange (zlen sq) 0 (2^47); KZRange SEQ 4096 (2^47); KZAlign DCTX 8;
     KZWr (SPV - 688) 688; KZWr (DCTX + 29976) 32; KZDisj (SPV - 688) 688 DCTX 95992]
    [].
  all: try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x1ac04) _ _ _ _) => kx_trap_fast end).
  all: kx_mem; unfold held in LRD, XLITC, X3, X1, X10;
    lazymatch type of MUL with munch _ ?ma ?mb =>
      assert (LRD2 : rdbl usegs mb LITP (LBE + 32)) by (eapply (rdbl_transport usegs _ ma mb); [exact LRD | exact MUL | intros x Hx; left; cbn [outside]; split; [lia| split; [lia|exact I]]]);
      assert (XLIT2 : 2 = 2 -> rdbl usegs mb (DCTX + 30372) (DCTX + 95940)) by (intros HL2; eapply (rdbl_transport usegs _ ma mb); [exact (XLITC HL2) | exact MUL | intros x Hx; left; cbn [outside]; split; [lia| split; [lia|exact I]]]) end;
    unfold held in *;
    lazymatch type of MUL with munch _ ?ma ?mb => transport_after_call usegs ma mb MUL WML end.
  all: try replace (SPV + -688 + 248) with (SPV + -440) by lia.
  all: lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1d904) _ _ _ _) =>
        rewrite ?Z_to_bv_bv_unsigned;
        eapply (CONT (DST + CAP)); [ intros HZ; eapply seql_static_m2; [exact RG0 | exact SIDE0 | exact SEP0 | exact TBL0 | exact NZ | exact HZ | cbn [y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws]; reflexivity | cbn [y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws]; lia]
          | eapply seql_iinv_eq;
            [ (unfold seql_iinv; cbn [y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws]; split; [exact FR|]; split; [unfold dctx_ptrs; exact PT|]; split; [exact TLL|]; split; [exact TOF|]; split; [exact TML|]; split; [exact SQB|]; split; [exact LRD2|]; split; [exact XLIT2|]; split; [split; [unfold h5_vcells; exact H5O | exact H5L]|]; cbn [seql_xinv]; rewrite FE1; unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation; split; [do 3 eexists; exact REP|]; split; [exact HH3|]; split; [exact BUF|]; split; [exact STK|]; split; [exact MU|]; split; [exact WM| lazymatch goal with MIx : mem_inv usegs ?mm |- mem_inv usegs ?mm => exact MIx end])
            | unfold seql_ifr; cbn [app seql_saved y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws];
              repeat (lazymatch goal with |- cons _ _ = cons _ _ => f_equal | |- C8 _ = C8 _ => f_equal end); f_equal; lia ] ]
    end.
Qed.
