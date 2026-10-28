From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem HufWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_tbl_iface RF_huf_fdw_cut RF_huf_fdw_smb
  RF_huf_fdw_fil.
Import ListNotations.
Open Scope Z_scope.

Definition fdw_l1h_stmt : Prop :=
  forall (SP : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 m1 : fmem) (S DT DST dcap lo : Z) (bs : list Z)
         (dt : dtable) (POST : machine_state -> Prop) (jp : list byte) (x : dec) (st : dstatus) (d0 : bitD)
         (y1 y23 y24 y25 y26 y27 y31 : word),
  fdw_pre SP S DT DST dcap lo bs dt ->
  sm_ok dcap bs x -> st_ok (dt_tableLog dt) x -> fdw_mem m0 m1 SP S DT DST dcap lo bs dt x jp ->
  reload_dstream bs (de_bd x) = Ok (st, d0) ->
  (dstatus_eqb st Unfinished && (FseNCount.Zlength (de_out x) <? dcap - 3) = true ->
     forall (m2 : fmem) (jp2 : list byte) (z1 z24 z25 z26 z27 z28 : word),
       fdw_mem m0 m2 SP S DT DST dcap lo bs dt (mkDec (de_out x) (de_s1 x) (de_s2 x) d0) jp2 ->
       evt usegs POST (MS (mkR z1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 (-4)) (Z_to_bv 64 (-5)) (Z_to_bv 64 64)
                               (Z_to_bv 64 DST) (Z_to_bv 64 (2^61)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (DT + 4))
                               (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 S)
                               (Z_to_bv 64 (S + bd_ptr d0)) (Z_to_bv 64 (-3)) (Z_to_bv 64 (DST + dcap))
                               (Z_to_bv 64 65535) (Z_to_bv 64 BIT_MASK_TAB) (Z_to_bv 64 (DST + zlen (de_out x)))
                               (Z_to_bv 64 (DST + dcap - 3)) (Z_to_bv 64 (bd_bits d0)) z24 z25 z26 z27 z28
                               (Z_to_bv 64 (de_s2 x)) (Z_to_bv 64 (de_s1 x)) (Z_to_bv 64 (bd_cont d0)))
                           F (Z_to_bv 64 PFDW_L1D) fc None m2 (seg_rom usegs))) ->
  (dstatus_eqb st Unfinished && (FseNCount.Zlength (de_out x) <? dcap - 3) = false ->
     fdw_t1_K SP gp tp F fc m0 S DT DST dcap lo bs dt POST (mkDec (de_out x) (de_s1 x) (de_s2 x) d0)) ->
  evt usegs POST (MS (mkR y1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 (-4)) (Z_to_bv 64 (-5)) (Z_to_bv 64 64)
                          (Z_to_bv 64 DST) (Z_to_bv 64 (2^61)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (DT + 4))
                          (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 S)
                          (Z_to_bv 64 (S + bd_ptr (de_bd x))) (Z_to_bv 64 (-3)) (Z_to_bv 64 (DST + dcap))
                          (Z_to_bv 64 65535) (Z_to_bv 64 BIT_MASK_TAB) (Z_to_bv 64 (DST + zlen (de_out x)))
                          (Z_to_bv 64 (DST + dcap - 3)) y23 y24 y25 y26 y27 (Z_to_bv 64 (bd_bits (de_bd x)))
                          (Z_to_bv 64 (de_s2 x)) (Z_to_bv 64 (de_s1 x)) y31)
                      F (Z_to_bv 64 PFDW_L1) fc None m1 (seg_rom usegs)).

Definition fdw_l1_from_h_stmt : Prop := fdw_l1h_stmt -> fdw_l1_stmt.

Theorem fdw_l1_from_h_proof : fdw_l1_from_h_stmt.
Proof.
  unfold fdw_l1_from_h_stmt, fdw_l1_stmt.
  intros L1H SP gp tp F fc m0 S DT DST dcap lo bs dt POST f.
  induction f as [|f IH]; intros x r PRE ML KT; [discriminate|].
  destruct x as [out s1 s2 d].
  intros m1 jp y1 y23 y24 y25 y26 y27 y31 OK STO MEM.
  cbn [main_loop de_out de_s1 de_s2 de_bd] in ML.
  destruct (reload_dstream bs d) as [[st d0]| | |] eqn:RL; cbn [bind] in ML; try discriminate.
  pose proof PRE as (TL1 & TLC & COK & BY & _).
  pose proof (fi_reload_facts bs _ st d0 BY (proj1 OK) RL) as (BOK0 & BLE & _).
  cbn [de_bd de_out de_s1 de_s2] in BOK0, BLE, OK, STO.
  apply (L1H SP gp tp F fc m0 m1 S DT DST dcap lo bs dt POST jp (mkDec out s1 s2 d) st d0 y1 y23 y24 y25 y26 y27 y31
           PRE OK STO MEM RL).
  - intros CND m2 jp2 z1 z24 z25 z26 z27 z28 MEM2. cbn [de_out de_s1 de_s2 de_bd] in CND |- *.
    rewrite CND in ML.
    apply andb_true_iff in CND as (CU & CL). apply Z.ltb_lt in CL. unfold FseNCount.Zlength in CL.
    destruct (decode_sym dt false s1 d0) as [[[o0 s1a] d1]| | |] eqn:D1; cbn [bind] in ML; try discriminate.
    destruct (decode_sym dt false s2 d1) as [[[o1 s2a] d2]| | |] eqn:D2; cbn [bind] in ML; try discriminate.
    destruct (decode_sym dt false s1a d2) as [[[o2 s1b] d3]| | |] eqn:D3; cbn [bind] in ML; try discriminate.
    destruct (decode_sym dt false s2a d3) as [[[o3 s2b] d4]| | |] eqn:D4; cbn [bind] in ML; try discriminate.
    destruct OK as (BOK & B64 & OL & OBY). cbn [de_out de_bd] in BOK, B64, OL, OBY.
    refine (fdw_l1d_proof SP gp tp F fc m0 m2 S DT DST dcap lo bs dt POST jp2 out s1 s2 d0 o0 s1a o1 s2a o2 s1b o3 s2b
              d1 d2 d3 d4 z1 z24 z25 z26 z27 z28 PRE D1 D2 D3 D4 _ _ _ MEM2 _ _).
    + unfold sm_ok; cbn [de_out de_bd]. split; [exact BOK0 | split; [lia | split; [exact OL | exact OBY]]].
    + exact STO.
    + lia.
    + intros B. exact (IH _ r PRE ML KT).
    + intros B. destruct f as [|f]; [discriminate ML|].
      cbn [main_loop de_bd de_out de_s1 de_s2] in ML.
      destruct (reload_dstream bs d4) as [[st4 d5]| | |] eqn:RL4; cbn [bind] in ML; try discriminate.
      unfold reload_dstream in RL4. rewrite (proj2 (Z.ltb_lt 64 (bd_bits d4)) B) in RL4.
      injection RL4 as <- <-.
      cbn [dstatus_eqb andb de_out de_s1 de_s2] in ML. injection ML as ER. subst r. exact KT.
  - intros CND. cbn [de_out de_s1 de_s2 de_bd] in CND |- *. rewrite CND in ML.
    injection ML as ER. subst r. exact KT.
Qed.
