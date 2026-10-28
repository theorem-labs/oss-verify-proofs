From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk Frame Exec.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface huf41_kit_reload seqD_kit_reload RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit RZ_seq_l_lkit2.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition seql_frame_pre (P : slp) (OEND : Z) (c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 : word) : list cell :=
  let '(mkSLP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  [C8 c0; C8 c8; C8 c16; C8 c24; C8 (Z_to_bv 64 (- (SPV - 352) - 1)); C8 c40; C8 c48; C8 (Z_to_bv 64 DCTX); C8 c64; C8 c72; C8 (Z_to_bv 64 (Z.min nbSeq 8)); C8 (Z_to_bv 64 (SPV - 344)); C8 (Z_to_bv 64 DST); C8 c104; C8 dend; C8 (Z_to_bv 64 PFX); C8 c128; C8 (Z_to_bv 64 (DCTX + 26684)); C8 (Z_to_bv 64 BITMASK); C8 c152; C8 (Z_to_bv 64 OEND); C8 c168; C8 c176; C8 c184; C8 (Z_to_bv 64 nbSeq); C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 (DCTX + 29896)); C8 c216; C8 c224; C8 c232; C8 c240].

Definition seql_frame_rest (P : slp) (sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z) (jseq : list byte) : list cell :=
  let '(mkSLP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  [C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (LLT + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (OFT + 8)); C8 (Z_to_bv 64 sML); C8 (Z_to_bv 64 (MLT + 8)); C8 p0; C8 p1; C8 p2; CB 192 (seql_ring_bytes rl rm ro); C8 (Z_to_bv 64 LP); CB 24 jseq;
   CB 104 (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++ le8 s1 ++ le8 s0 ++ le8 ra)].

Lemma seql_frame_split : forall P OEND c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP jpad jseq,
  seql_frame P OEND c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP jpad jseq =
  seql_frame_pre P OEND c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 ++
  bitd_cells cw (Z_to_bv 64 bc) jpad ptr (y_SEQ P) ++ seql_frame_rest P sLL sOF sML p0 p1 p2 rl rm ro LP jseq.
Proof. intros. destruct P. reflexivity. Qed.

Definition seql_rl_post (P : slp) (OEND LLO LEND LOCV : Z) (c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (rl rm ro : Z -> Z) (LP : Z)
    (ra gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 a5 a6 m' cw',
    ms' = MS (mkR ra (Z_to_bv 64 (y_SPV P + -688)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (y_SPV P + -440)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ seql_linv P OEND LLO LEND LOCV m' c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw' (bc mod 8) (ptr - bc / 8) sLL sOF sML p0 p1 p2 rl rm ro LP.

Lemma seql_rl_spec : forall P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP
    ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc,
  seql_static P OEND LLO LEND LOCV ->
  seql_linv P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  0 <= bc <= 64 -> y_SEQ P + 8 <= ptr -> ptr <= y_SEQ P + zlen (y_sq P) - 8 ->
  evt usegs (seql_rl_post P OEND LLO LEND LOCV c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP
               ra gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc)
    (MS (mkR ra (Z_to_bv 64 (y_SPV P + -688)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (y_SPV P + -440)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PZD_RELOADI) fc None m1 (seg_rom usegs)).
Proof.
  intros P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP
    ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ST INV HBC HP1 HP2.
  pose proof (seql_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  pose proof (seql_linv_step P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV) as STEP.
  destruct INV as ((jpad & jseq & FR) & _ & _ & _ & SQB & _ & _ & _ & XI).
  rewrite seql_frame_split in FR. apply rw_cells_app in FR. destruct FR as (F0 & FR). apply rw_cells_app in FR. destruct FR as (BDC & F2).
  destruct P as [ra' gp' tp' s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' F' fc' m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_xinv y_SPV y_SEQ y_sq y_B0 y_B1 y_DST y_lo] in XI, STEP, BDC, SQB, HP1, HP2 |- *.
  sd_static_open ST. unfold held in *.
  destruct XI as (_ & _ & BUF & _).
  match type of BDC with rw_cells _ _ (_ + Z.of_nat (cells_size ?CS)) _ => change (Z.of_nat (cells_size CS)) with 248 in BDC end.
  match type of F2 with rw_cells _ _ (_ + Z.of_nat (cells_size ?CS) + Z.of_nat (cells_size ?CT)) _ =>
    change (Z.of_nat (cells_size CS)) with 248 in F2; change (Z.of_nat (cells_size CT)) with 40 in F2 end.
  replace (SPV + -688 + 248) with (SPV + -440) in BDC by lia.
  assert (LSQ : Z.of_nat (length (map (Z_to_bv 8) sq)) = Z.of_nat (length sq)) by (rewrite length_map; reflexivity).
  assert (BDA : (SPV + -440) mod 8 = 0) by (clear - AL4; Z.div_mod_to_equations; lia).
  eapply evt_mono.
  - eapply (seqd_reload_proof ra (Z_to_bv 64 (SPV + -688)) gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
             (SPV + -440) SEQ (Z.of_nat (length sq)) bc ptr cw jpad (map (Z_to_bv 8) sq));
      [ exact MI | exact BDC | exact BDA | exact SQB | exact LSQ | clear - S17 S18; lia | clear - S17; lia | clear - S13; lia | clear - S14; lia
      | clear - S17 S18 S25; lia | clear - HBC; lia | clear - HP1; lia | clear - HP2; lia ].
  - intros ms' (b1 & b2 & b3 & b4 & b5 & b6 & m' & cw' & -> & MU & WM & MI' & BDC').
    exists b1, b2, b3, b4, b5, b6, m', cw'. split; [reflexivity|].
    eapply (STEP m' c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw' (bc mod 8) (ptr - bc / 8) sLL sOF sML p0 p1 p2 rl rm ro LP jpad jseq DST DST).
    + eapply munch_weaken; [|exact MU]. unfold sub_fp. cbn [outside]. intros x (H1 & H2 & _). split; [clear - H2; lia | exact I].
    + exact WM.
    + exact MI'.
    + eapply stk_transport_disjoint; [exact BUF | exact MU | exact WM |]. cbn [disjoint_from]. split; [clear - S18 S24; lia | exact I].
    + clear - S17; lia.
    + clear - S4; lia.
    + rewrite seql_frame_split. cbn [y_SEQ]. apply rw_cells_app. split.
      * eapply rw_cells_transport; [exact F0 | exact MU | exact WM |].
        match goal with |- disjoint_from _ _ (Z.of_nat (cells_size ?CS)) => change (Z.of_nat (cells_size CS)) with 248 end.
        cbn [disjoint_from]. split; [clear - S17; lia | exact I].
      * apply rw_cells_app. split.
        -- match goal with |- rw_cells _ _ (_ + Z.of_nat (cells_size ?CS)) _ => change (Z.of_nat (cells_size CS)) with 248 end.
           replace (SPV + -688 + 248) with (SPV + -440) by lia. exact BDC'.
        -- match goal with |- rw_cells _ _ (_ + Z.of_nat (cells_size ?CS) + Z.of_nat (cells_size ?CT)) _ =>
             change (Z.of_nat (cells_size CS)) with 248; change (Z.of_nat (cells_size CT)) with 40 end.
           eapply rw_cells_transport; [exact F2 | exact MU | exact WM |].
           cbn [disjoint_from]. split; [clear - S17; lia | exact I].
Qed.
