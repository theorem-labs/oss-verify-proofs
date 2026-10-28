From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface huf41_kit_reload seqD_kit_reload RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_lbase RZ_seq_s_lkit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition seqs_reload_post (P : ssp) (OEND LLO LEND LOCV : Z) (c0 c8 c40 lec c128 : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (BD : Z) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 a5 a6 m' cw',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BD) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ seqs_linv P OEND LLO LEND LOCV m' c0 c8 c40 lec c128 cw' (bc mod 8) (ptr - bc / 8) sLL sOF sML p0 p1 p2 LP.

Lemma seqs_reload_call : huf_reload_stmt_at PZD_RELOADI ->
  forall P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP (BD : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc,
  seqs_static P OEND LLO LEND LOCV -> seqs_linv P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  BD = v_SPV P + -248 -> 0 <= bc <= 64 -> v_SEQ P + 8 <= ptr -> ptr <= v_SEQ P + zlen (v_sq P) - 8 ->
  evt usegs (seqs_reload_post P OEND LLO LEND LOCV c0 c8 c40 lec c128 bc ptr sLL sOF sML p0 p1 p2 LP ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc BD)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BD) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PZD_RELOADI) fc None m1 (seg_rom usegs)).
Proof.
  intros RL P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP BD ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ST INV EBD HBC HP1 HP2.
  pose proof (seqs_linv_frame P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as TRANS.
  pose proof (seqs_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  destruct INV as ((jpad & jseq & FR) & _ & _ & _ & SQB & _).
  rewrite <- (firstn_skipn 17 (seqs_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)) in FR.
  rewrite <- (firstn_skipn 6 (skipn 17 _)) in FR.
  apply rw_cells_app in FR. destruct FR as (PRE & FR). apply rw_cells_app in FR. destruct FR as (BDC & POST).
  destruct P as [ra' gp' tp' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' F' fc' m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_static seqs_frame seqs_reload_post firstn skipn cells_size csize Nat.add v_SPV v_SEQ v_sq] in ST, PRE, BDC, POST, EBD, HP1, HP2, SQB |- *.
  sd_static_open ST.
  assert (LSQ : zlen (map (Z_to_bv 8) sq) = zlen sq) by (unfold zlen; rewrite length_map; reflexivity).
  replace (SPV + -384 + Z.of_nat 136) with BD in BDC by (clear - EBD; lia).
  eapply evt_mono.
  - eapply (RL ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 BD SEQ (zlen (map (Z_to_bv 8) sq)) bc ptr cw jpad (map (Z_to_bv 8) sq));
      [ exact MI | exact BDC | subst BD; clear - AL4; lia | exact SQB | reflexivity | clear - EBD S18; lia | clear - EBD S17; lia | clear - S13; lia
      | clear - LSQ S14; lia | unfold held in S25; clear - EBD S18 S25 LSQ; lia | clear - HBC; lia | clear - HP1; lia | clear - HP2 LSQ; lia ].
  - intros ms' (b1 & b2 & b3 & b4 & b5 & b6 & m' & cont' & -> & MU & WM & MI' & BDC').
    exists b1, b2, b3, b4, b5, b6, m', cont'. split; [reflexivity|].
    apply (TRANS m' c0 c8 c40 lec c128 cont' (bc mod 8) (ptr - bc / 8) sLL sOF sML p0 p1 p2 LP jpad jseq).
    + eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside v_SPV]. intros x Hx. clear - Hx EBD. lia.
    + exact WM.
    + exact MI'.
    + rewrite <- (firstn_skipn 17 (seqs_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
      rewrite <- (firstn_skipn 6 (skipn 17 _)).
      apply rw_cells_app. split; [|apply rw_cells_app; split]; cbn [v_SPV].
      * cbn [seqs_frame firstn skipn]. eapply rw_cells_transport; [exact PRE | exact MU | exact WM |].
        cbn [disjoint_from cells_size csize Nat.add]. split; [clear - EBD; lia | exact I].
      * cbn [seqs_frame firstn skipn cells_size csize Nat.add]. replace (SPV + -384 + Z.of_nat 136) with BD by (clear - EBD; lia). exact BDC'.
      * cbn [seqs_frame firstn skipn cells_size csize Nat.add]. eapply rw_cells_transport; [exact POST | exact MU | exact WM |].
        cbn [disjoint_from cells_size csize Nat.add]. split; [clear - EBD; lia | exact I].
Qed.
