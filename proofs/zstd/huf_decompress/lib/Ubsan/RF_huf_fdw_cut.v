From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem HufWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_tbl_iface.
Import ListNotations.
Open Scope Z_scope.

Definition PFDW_F : Z := 0x1f7d8.
Definition PFDW_NF : Z := 0x1f914.
Definition PFDW_L1 : Z := 0x1fac8.
Definition PFDW_T1 : Z := 0x1fdd0.
Definition PFDW_EXIT : Z := 0x20450.
Definition PFDW_T2 : Z := 0x20438.
Definition PFDW_L3 : Z := 0x2016c.
Definition PFDW_FIN1 : Z := 0x207dc.
Definition PFDW_FIN2 : Z := 0x20808.

Definition bd_reg (S : Z) (d : bitD) : Z := if bd_zero d then ZEROFILLED_F else S + bd_ptr d.

Definition cells_ok (tl : Z) (cells : list dcell) : Prop :=
  Forall (fun c => 0 <= dc_symbol c < 256 /\ 0 <= dc_nbBits c <= tl /\ 0 <= dc_newState c
                   /\ dc_newState c + 2^(dc_nbBits c) <= 2^tl) cells.

Lemma zlen_tl : forall {A} (l : list A), (1 <= length l)%nat -> zlen (tl l) = zlen l - 1.
Proof.
  intros A l H. destruct l as [|a l]; cbn [tl length] in *; lia.
Qed.

Lemma bitdz_bitd : forall S d jp, bd_zero d = false -> bitdz_cells S d jp = bitd_cells S d jp.
Proof.
  intros S d jp Z. unfold bitdz_cells, bitd_cells. rewrite Z. reflexivity.
Qed.

Definition res_ok (r : res (list Z)) : Prop := match r with Ok _ | Err _ => True | Ub | NoFuel => False end.

Definition dres (DST dcap : Z) (r : res (list Z)) (m2 : fmem) (a4v : Z) : Prop :=
  match r with
  | Ok l => a4v = zlen l /\ exists junk, u8arr usegs m2 DST (map (Z_to_bv 8) l ++ junk) /\ zlen junk = dcap - zlen l
  | Err e => a4v = - e /\ 0 < e < 120
  | Ub | NoFuel => False
  end.

Definition sm_inv (m0 : fmem) (SP DST dcap : Z) (m1 : fmem) (out : list Z) : Prop :=
  (exists junk, u8arr usegs m1 DST (map (Z_to_bv 8) out ++ junk) /\ zlen junk = dcap - zlen out)
  /\ munch [(SP + 16, SP + 88); (DST, DST + dcap)] m0 m1 /\ wmono usegs m0 m1 /\ mem_inv usegs m1.

Definition sm_ok (dcap : Z) (bs : list Z) (x : dec) : Prop :=
  bitd_ok bs (de_bd x) /\ bd_bits (de_bd x) <= 64 /\ zlen (de_out x) <= dcap /\ Forall (fun c => 0 <= c < 256) (de_out x).

Definition sm_okr (dcap : Z) (bs : list Z) (x : dec) : Prop :=
  bitd_ok bs (de_bd x) /\ bd_bits (de_bd x) <= 2^29 /\ zlen (de_out x) <= dcap /\ Forall (fun c => 0 <= c < 256) (de_out x).

Definition st_ok (tl : Z) (x : dec) : Prop := 0 <= de_s1 x < 2^tl /\ 0 <= de_s2 x < 2^tl.

Definition fdw_pre (SP S DT DST dcap lo : Z) (bs : list Z) (dt : dtable) : Prop :=
  1 <= dt_tableLog dt <= 12 /\ zlen (dt_cells dt) = 2^(dt_tableLog dt) /\ cells_ok (dt_tableLog dt) (dt_cells dt)
  /\ Forall (fun c => 0 <= c < 256) bs
  /\ lo <= SP /\ SP mod 16 = 0 /\ SP + 192 <= 2^47
  /\ 8 <= S /\ S + zlen bs <= lo
  /\ 0 < DT /\ DT mod 4 = 0 /\ DT + 4 + 4 * 2^(dt_tableLog dt) <= lo
  /\ 4 <= DST /\ DST + dcap <= lo /\ 0 <= dcap <= 255
  /\ (DST + dcap <= DT \/ DT + 4 + 4 * 2^(dt_tableLog dt) <= DST)
  /\ (DST + dcap <= S \/ S + zlen bs <= DST)
  /\ (DT + 4 + 4 * 2^(dt_tableLog dt) <= S \/ S + zlen bs <= DT).

Definition fdw_mem (m0 m1 : fmem) (SP S DT DST dcap lo : Z) (bs : list Z) (dt : dtable) (x : dec) (jp : list byte)
    : Prop :=
  rw_cells usegs m1 (SP + 16) [C8 (Z_to_bv 64 (de_s2 x)); C8 (Z_to_bv 64 (DT + 4))]
  /\ rw_cells usegs m1 (SP + 32) [C8 (Z_to_bv 64 (de_s1 x)); C8 (Z_to_bv 64 (DT + 4))]
  /\ rw_cells usegs m1 (SP + 48) (bitdz_cells S (de_bd x) jp)
  /\ sm_inv m0 SP DST dcap m1 (de_out x)
  /\ bytes_at usegs m1 (DT + 4) (concat (map fse_cell_bytes (dt_cells dt)))
  /\ bytes_at usegs m1 S (map (Z_to_bv 8) bs)
  /\ stk usegs m1 lo SP.

Definition fdw_K (SP : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem) (DST dcap lo : Z)
    (POST : machine_state -> Prop) (r : res (list Z)) : Prop :=
  forall (m2 : fmem) (a4v : Z) (y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28
          y29 y30 y31 : word),
    munch [(SP + 16, SP + 88); (DST, DST + dcap)] m0 m2 -> wmono usegs m0 m2 ->
    mem_inv usegs m2 -> stk usegs m2 lo SP -> dres DST dcap r m2 a4v ->
    evt usegs POST (MS (mkR y1 (Z_to_bv 64 SP) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 a4v) y11 y12 y13 y14 y15 y16 y17 y18 y19
                            y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                        F (Z_to_bv 64 PFDW_EXIT) fc None m2 (seg_rom usegs)).

Definition fdw_t1_K (SP : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem) (S DT DST dcap lo : Z)
    (bs : list Z) (dt : dtable) (POST : machine_state -> Prop) (x : dec) : Prop :=
  forall (m1 : fmem) (jp : list byte) (y1 y5 y6 y7 y10 y15 y16 y17 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
    sm_okr dcap bs x -> st_ok (dt_tableLog dt) x -> fdw_mem m0 m1 SP S DT DST dcap lo bs dt x jp ->
    evt usegs POST (MS (mkR y1 (Z_to_bv 64 SP) gp tp y5 y6 y7 (Z_to_bv 64 DST) (Z_to_bv 64 (2^61)) y10
                            (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 1) (Z_to_bv 64 1) y15 y16 y17
                            (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 65535) (Z_to_bv 64 BIT_MASK_TAB)
                            (Z_to_bv 64 (DST + zlen (de_out x))) y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                        F (Z_to_bv 64 PFDW_T1) fc None m1 (seg_rom usegs)).

Definition fdw_l1_K (SP : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem) (S DT DST dcap lo : Z)
    (bs : list Z) (dt : dtable) (POST : machine_state -> Prop) (x : dec) : Prop :=
  forall (m1 : fmem) (jp : list byte) (y1 y23 y24 y25 y26 y27 y31 : word),
    sm_ok dcap bs x -> st_ok (dt_tableLog dt) x -> fdw_mem m0 m1 SP S DT DST dcap lo bs dt x jp ->
    evt usegs POST (MS (mkR y1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 (-4)) (Z_to_bv 64 (-5)) (Z_to_bv 64 64)
                            (Z_to_bv 64 DST) (Z_to_bv 64 (2^61)) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 (DT + 4))
                            (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 S)
                            (Z_to_bv 64 (S + bd_ptr (de_bd x))) (Z_to_bv 64 (-3)) (Z_to_bv 64 (DST + dcap))
                            (Z_to_bv 64 65535) (Z_to_bv 64 BIT_MASK_TAB) (Z_to_bv 64 (DST + zlen (de_out x)))
                            (Z_to_bv 64 (DST + dcap - 3)) y23 y24 y25 y26 y27 (Z_to_bv 64 (bd_bits (de_bd x)))
                            (Z_to_bv 64 (de_s2 x)) (Z_to_bv 64 (de_s1 x)) y31)
                        F (Z_to_bv 64 PFDW_L1) fc None m1 (seg_rom usegs)).

Definition fdw_t1_stmt : Prop :=
  forall (SP : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem) (S DT DST dcap lo : Z) (bs : list Z)
         (dt : dtable) (POST : machine_state -> Prop) (f : nat) (x : dec) (r : res (list Z)),
  fdw_pre SP S DT DST dcap lo bs dt ->
  tail_loop bs dt dcap false f x = r -> res_ok r ->
  fdw_K SP gp tp F fc m0 DST dcap lo POST r ->
  fdw_t1_K SP gp tp F fc m0 S DT DST dcap lo bs dt POST x.

Definition fdw_l1_stmt : Prop :=
  forall (SP : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem) (S DT DST dcap lo : Z) (bs : list Z)
         (dt : dtable) (POST : machine_state -> Prop) (f : nat) (x r : dec),
  fdw_pre SP S DT DST dcap lo bs dt ->
  main_loop bs dt dcap false f x = Ok r ->
  fdw_t1_K SP gp tp F fc m0 S DT DST dcap lo bs dt POST r ->
  fdw_l1_K SP gp tp F fc m0 S DT DST dcap lo bs dt POST x.

Definition fdw_entry_at (E : Z) (fast : bool) : Prop :=
  forall (SP : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem) (S DT DST dcap lo : Z) (bs : list Z)
         (dt : dtable) (fmw : word) (jd j1 j2 jb : list byte) (POST : machine_state -> Prop) (r : res (list Z))
         (x1 x5 x6 x7 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  fdw_pre SP S DT DST dcap lo bs dt ->
  (fast = true -> Forall (fun c => 1 <= dc_nbBits c) (dt_cells dt)) ->
  rw_cells usegs m0 DT [C2 (Z_to_bv 64 (dt_tableLog dt)); C2 fmw] ->
  bytes_at usegs m0 (DT + 4) (concat (map fse_cell_bytes (dt_cells dt))) ->
  bytes_at usegs m0 S (map (Z_to_bv 8) bs) ->
  rw_cells usegs m0 (SP + 16) [CB 16 j2] -> rw_cells usegs m0 (SP + 32) [CB 16 j1] ->
  rw_cells usegs m0 (SP + 48) [CB 40 jb] ->
  u8arr usegs m0 DST jd -> zlen jd = dcap ->
  stk usegs m0 lo SP -> mem_inv usegs m0 ->
  decompress_usingDTable bs dt dcap fast = r -> res_ok r ->
  fdw_K SP gp tp F fc m0 DST dcap lo POST r ->
  evt usegs POST (MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 DST) (Z_to_bv 64 DT) (Z_to_bv 64 1)
                          (Z_to_bv 64 1) (Z_to_bv 64 (zlen bs)) x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + dcap))
                          (Z_to_bv 64 S) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                      F (Z_to_bv 64 E) fc None m0 (seg_rom usegs)).

Definition fdw_nf_entry_stmt : Prop := fdw_entry_at PFDW_NF false.
Definition fdw_f_entry_stmt : Prop := fdw_entry_at PFDW_F true.

Definition fdw_fmem (m0 m1 : fmem) (SP S DT DST dcap lo : Z) (bs : list Z) (dt : dtable) (x : dec) (jp : list byte)
    : Prop :=
  (exists junk, u8arr usegs m1 DST (map (Z_to_bv 8) (de_out x) ++ junk) /\ zlen junk = dcap - zlen (de_out x))
  /\ (exists fb fp : word, rw_cells usegs m1 (SP + 16)
        [C8 (Z_to_bv 64 (de_s2 x)); C8 (Z_to_bv 64 (DT + 4)); C8 (Z_to_bv 64 (de_s1 x)); C8 (Z_to_bv 64 (DT + 4));
         C8 (Z_to_bv 64 (bd_cont (de_bd x))); C4 fb; CB 4 jp; C8 fp; C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (S + 8))])
  /\ munch [(SP + 16, SP + 88); (DST, DST + dcap)] m0 m1 /\ wmono usegs m0 m1 /\ mem_inv usegs m1
  /\ bytes_at usegs m1 (DT + 4) (concat (map fse_cell_bytes (dt_cells dt)))
  /\ bytes_at usegs m1 S (map (Z_to_bv 8) bs)
  /\ stk usegs m1 lo SP.

Definition fdw_t2_K (SP : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem) (S DT DST dcap lo : Z)
    (bs : list Z) (dt : dtable) (POST : machine_state -> Prop) (x : dec) : Prop :=
  forall (m1 : fmem) (jp : list byte) (y1 y10 y19 y20 y21 y22 y23 y24 y25 y26 y27 y29 y30 y31 : word),
    sm_okr dcap bs x -> st_ok (dt_tableLog dt) x -> fdw_fmem m0 m1 SP S DT DST dcap lo bs dt x jp ->
    evt usegs POST (MS (mkR y1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 (de_s1 x)) (Z_to_bv 64 (de_s2 x))
                            (Z_to_bv 64 (bd_bits (de_bd x))) (Z_to_bv 64 DST) (Z_to_bv 64 (DST + zlen (de_out x))) y10
                            (Z_to_bv 64 (S + 8)) (Z_to_bv 64 S) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4))
                            (Z_to_bv 64 (2^61)) (Z_to_bv 64 65535) (Z_to_bv 64 (bd_reg S (de_bd x)))
                            (Z_to_bv 64 (DST + dcap)) y19 y20 y21 y22 y23 y24 y25 y26 y27
                            (Z_to_bv 64 (bd_cont (de_bd x))) y29 y30 y31)
                        F (Z_to_bv 64 PFDW_T2) fc None m1 (seg_rom usegs)).

Definition fdw_t2_stmt : Prop :=
  forall (SP : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem) (S DT DST dcap lo : Z) (bs : list Z)
         (dt : dtable) (POST : machine_state -> Prop) (f : nat) (x : dec) (r : res (list Z)),
  fdw_pre SP S DT DST dcap lo bs dt ->
  tail_loop bs dt dcap true f x = r -> res_ok r ->
  fdw_K SP gp tp F fc m0 DST dcap lo POST r ->
  fdw_t2_K SP gp tp F fc m0 S DT DST dcap lo bs dt POST x.

Definition fdw_l3_K (SP : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem) (S DT DST dcap lo : Z)
    (bs : list Z) (dt : dtable) (POST : machine_state -> Prop) (x : dec) : Prop :=
  forall (m1 : fmem) (jp : list byte) (y1 y21 y22 y23 y24 y25 y26 y27 : word),
    sm_ok dcap bs x -> st_ok (dt_tableLog dt) x -> fdw_mem m0 m1 SP S DT DST dcap lo bs dt x jp ->
    evt usegs POST (MS (mkR y1 (Z_to_bv 64 SP) gp tp (Z_to_bv 64 (de_s1 x)) (Z_to_bv 64 (de_s2 x))
                            (Z_to_bv 64 (bd_bits (de_bd x))) (Z_to_bv 64 DST) (Z_to_bv 64 (DST + zlen (de_out x)))
                            (Z_to_bv 64 64) (Z_to_bv 64 (S + 8)) (Z_to_bv 64 S) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4))
                            (Z_to_bv 64 (2^61)) (Z_to_bv 64 (2^16 - 1)) (Z_to_bv 64 (S + bd_ptr (de_bd x)))
                            (Z_to_bv 64 (DST + dcap)) (Z_to_bv 64 (-5)) (Z_to_bv 64 (DST + dcap - 3)) y21 y22 y23 y24 y25 y26 y27
                            (Z_to_bv 64 (bd_cont (de_bd x))) (Z_to_bv 64 1) (Z_to_bv 64 (-3)) (Z_to_bv 64 (-4)))
                        F (Z_to_bv 64 PFDW_L3) fc None m1 (seg_rom usegs)).

Definition fdw_l3_stmt : Prop :=
  forall (SP : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem) (S DT DST dcap lo : Z) (bs : list Z)
         (dt : dtable) (POST : machine_state -> Prop) (f : nat) (x r : dec),
  fdw_pre SP S DT DST dcap lo bs dt ->
  Forall (fun c => 1 <= dc_nbBits c) (dt_cells dt) ->
  main_loop bs dt dcap true f x = Ok r ->
  fdw_t2_K SP gp tp F fc m0 S DT DST dcap lo bs dt POST r ->
  fdw_l3_K SP gp tp F fc m0 S DT DST dcap lo bs dt POST x.

Lemma fdw_rw_cells_app : forall m A B cs1 cs2,
  rw_cells usegs m A cs1 -> rw_cells usegs m B cs2 -> B = A + Z.of_nat (cells_size cs1) ->
  rw_cells usegs m A (cs1 ++ cs2).
Proof.
  intros m A B cs1 cs2 R1 R2 EB. subst B.
  unfold rw_cells, cells_at, wr_at in *.
  destruct R1 as ((W1 & B1) & V1a & V1b & V1c). destruct R2 as ((W2 & B2) & V2a & V2b & V2c).
  split; [split|].
  - apply (proj2 (cells_wf_app cs1 cs2)). split; assumption.
  - rewrite cells_bytes_app. apply (proj2 (bytes_at_app usegs m A _ _)).
    rewrite (cells_bytes_length cs1 W1). split; assumption.
  - rewrite cells_size_app, Nat2Z.inj_add. split; [lia|]. split; [lia|].
    intros i Hi. destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))) as [L|L].
    + apply V1c. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
      apply V2c. lia.
Qed.

Lemma fdw_mem_fmem : forall m0 m1 SP S DT DST dcap lo bs dt x jp,
  fdw_mem m0 m1 SP S DT DST dcap lo bs dt x jp -> fdw_fmem m0 m1 SP S DT DST dcap lo bs dt x jp.
Proof.
  intros m0 m1 SP S DT DST dcap lo bs dt x jp H.
  unfold fdw_mem, sm_inv in H. destruct H as (R16 & R32 & R48 & (J & MU & WM & MI) & BT & BS & SK).
  unfold fdw_fmem.
  refine (conj J (conj _ (conj MU (conj WM (conj MI (conj BT (conj BS SK))))))).
  exists (Z_to_bv 64 (bd_bits (de_bd x))),
         (Z_to_bv 64 (if bd_zero (de_bd x) then ZEROFILLED_F else S + bd_ptr (de_bd x))).
  pose proof (fdw_rw_cells_app _ _ _ _ _ R32 R48) as R3.
  specialize (R3 ltac:(cbn [cells_size csize]; lia)).
  pose proof (fdw_rw_cells_app _ _ _ _ _ R16 R3) as R1.
  specialize (R1 ltac:(cbn [cells_size csize]; lia)).
  exact R1.
Qed.

Definition fdw_fin_K (E n SP : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem) (DST dcap lo : Z)
    (POST : machine_state -> Prop) (out : list Z) (o : Z) : Prop :=
  forall (m1 : fmem) (y1 y5 y6 y7 y9 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
    sm_inv m0 SP DST dcap m1 out -> stk usegs m1 lo SP ->
    evt usegs POST (MS (mkR y1 (Z_to_bv 64 SP) gp tp y5 y6 y7 (Z_to_bv 64 DST) y9 (Z_to_bv 64 o)
                            (Z_to_bv 64 (DST + zlen out - n)) y12 y13 y14 y15 y16
                            y17 (Z_to_bv 64 (DST + zlen out - n + 1)) y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                        F (Z_to_bv 64 E) fc None m1 (seg_rom usegs)).

Definition fdw_fin_at (E n : Z) : Prop :=
  forall (SP : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem) (S DT DST dcap lo : Z) (bs : list Z)
         (dt : dtable) (POST : machine_state -> Prop) (out : list Z) (o : Z),
  fdw_pre SP S DT DST dcap lo bs dt -> 0 <= o < 256 -> n <= zlen out -> zlen out + 1 <= dcap ->
  fdw_K SP gp tp F fc m0 DST dcap lo POST (Ok (out ++ [o])) ->
  fdw_fin_K E n SP gp tp F fc m0 DST dcap lo POST out o.

Definition fdw_fin1_stmt : Prop := fdw_fin_at PFDW_FIN1 1.
Definition fdw_fin2_stmt : Prop := fdw_fin_at PFDW_FIN2 2.
