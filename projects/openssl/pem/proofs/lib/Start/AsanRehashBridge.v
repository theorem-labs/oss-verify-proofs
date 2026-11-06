(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import PropExec CatSim StoreOk AsanAcct RegEqv AxSymExec3 AsanNodesLibSound.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Exec MState Frame Mem Cells Step.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import AsanRehashModel AsanRehash AsanRehashSound AsanHookBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module RHB.
Import RHN.

#[local] Notation W := LBNS.W (only parsing).

Section RB.
Variable segs : list Segment.
Variable T : rtab.
Variables ilo ihi : Z.
Hypothesis SEG_below : forall a : word, find_segment segs (bv_unsigned a) 1 <> None -> bv_unsigned a < 2 ^ 47.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hilo : 0 <= ilo.

#[local] Notation cell := (LBNS.cell segs) (only parsing).
#[local] Notation wr_ok := (LBNS.wr_ok segs) (only parsing).
#[local] Notation rd_ok := LBNS.rd_ok (only parsing).

(* [comment removed for export] *)
Definition walk_stmt : Prop :=
  forall (map Bo No B N : Z) (olds ks' : list Z) (pl : list (Z * Z)) (ne0 tb0 : word) (RA : Z)
    (gp tp t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (sp : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  RHM.rehash0 N olds = Some (ks', pl) ->
  Z.of_nat (length olds) = No -> Forall (fun k => 0 <= k < 2 ^ 64) olds -> List.NoDup (List.filter RHM.is_live olds) ->
  64 <= N <= 2 ^ 20 -> Z.land (N - 1) N = 0 ->
  1 <= No <= 2 ^ 20 ->
  Step.rw_cells segs m map [Cells.C8 (Z_to_bv 64 B); Cells.C4 ne0; Cells.C4 tb0; Cells.C4 (Z_to_bv 64 N)] ->
  (forall j, 0 <= j < No -> Step.ro_cells segs m (Bo + 32 * j) [Cells.C8 (Z_to_bv 64 (nth (Z.to_nat j) olds 0))]) ->
  Frame.stk segs m Bo (Bo + 32 * No) ->
  Frame.stk segs m B (B + 32 * N) ->
  Frame.stk segs m (bv_unsigned sp - 16) (bv_unsigned sp) -> bv_unsigned sp mod 16 = 0 ->
  0 < Bo -> Bo + 32 * No <= 2 ^ 47 -> (Bo + 32 * No <= ilo \/ ihi <= Bo) -> Bo mod 8 = 0 ->
  0 < B -> B + 32 * N <= 2 ^ 47 -> (B + 32 * N <= ilo \/ ihi <= B) -> B mod 8 = 0 ->
  ihi <= bv_unsigned sp - 16 -> bv_unsigned sp < 2 ^ 47 ->
  (Bo + 32 * No <= B \/ B + 32 * N <= Bo) ->
  (bv_unsigned sp <= Bo \/ Bo + 32 * No <= bv_unsigned sp - 16) -> (bv_unsigned sp <= B \/ B + 32 * N <= bv_unsigned sp - 16) ->
  ilo <= map -> map + 20 <= ihi ->
  0 <= RA < 2 ^ 47 -> RA mod 4 = 0 ->
  Mem.mem_inv segs m ->
  Exec.evt segs (fun ms' => exists (a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' : word) (m' : word -> option byte),
      ms' = MState.MS (Frame.mkR (Z_to_bv 64 RA) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 map) (Z_to_bv 64 (Bo + 32 * No)) (Z_to_bv 64 (Bo + 32 * No)) a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6)
               F (Z_to_bv 64 RA) fc None m' (seg_rom segs)
      /\ Frame.munch [(map + 8, map + 16); (B, B + 32 * N); (bv_unsigned sp - 16, bv_unsigned sp)] m m'
      /\ Frame.wmono segs m m' /\ Mem.mem_inv segs m'
      /\ Step.rw_cells segs m' (map + 8) [Cells.C4 (Z_to_bv 64 (Z.of_nat (length pl))); Cells.C4 (Z_to_bv 64 0)]
      /\ (forall d, 0 <= d < N -> Step.rw_cells segs m' (B + 32 * d) [Cells.C8 (Z_to_bv 64 (nth (Z.to_nat d) ks' 0))]))
    (MState.MS (Frame.mkR (Z_to_bv 64 RA) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 map) (Z_to_bv 64 Bo) (Z_to_bv 64 (Bo + 32 * No)) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (r_entry T)) fc None m (seg_rom segs)).

(* [comment removed for export] *)
Definition HI (a : word) : bool := Z.leb (2 ^ 47) (bv_unsigned a).

Lemma HI_off : H_off_segments segs HI.
Proof.
  intros a Ha. unfold HI in Ha. apply Z.leb_le in Ha.
  destruct (find_segment segs (bv_unsigned a) 1) eqn:E; [|reflexivity].
  exfalso. assert (X : bv_unsigned a < 2 ^ 47) by (apply SEG_below; rewrite E; discriminate). lia.
Qed.

Lemma HI_low : forall x : word, bv_unsigned x < 2 ^ 47 -> HI x = false.
Proof. intros x Hx. unfold HI. apply Z.leb_gt. exact Hx. Qed.

(* [comment removed for export] *)
Lemma cell_restrict : forall (M : word -> option byte) a (n : nat) v, 0 <= a -> a + Z.of_nat n <= 2 ^ 47 ->
  cell M a n v -> cell (mrestrict HI M) a n v.
Proof.
  intros M a n v Ha Hn Hc. unfold LBNS.cell in *. rewrite <- Hc.
  apply rdn_ext; [rewrite LBNS.u_W by lia; lia|].
  intros x Hx. rewrite LBNS.u_W in Hx by lia. unfold mrestrict. rewrite HI_low by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bytes_of_cell : forall (m : word -> option byte) a (n : nat) v, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  cell m a n v -> Mem.bytes_at segs m a (word_to_le_bytes n v).
Proof.
  intros m a n v Ha Hn Hc. unfold LBNS.cell, LBNS.W in Hc. change (Z_to_bv 64 a) with (Mem.wa a) in Hc. revert a Ha Hn Hc.
  generalize (word_to_le_bytes n v) as bs. induction n as [|n IH]; intros bs a Ha Hn Hc; rewrite Mem.rdn_unfold in Hc.
  - injection Hc as <-. apply Mem.bytes_at_nil. lia.
  - destruct (Mem.mrd segs m (Mem.wa a)) as [b|] eqn:E; [| discriminate Hc]. rewrite Mem.wa_succ in Hc.
    destruct (rdn segs m (Mem.wa (a + 1)) n) as [r|] eqn:E2; [| discriminate Hc]. injection Hc as <-.
    pose proof (IH r (a + 1) ltac:(lia) ltac:(lia) E2) as (R0 & R1 & R).
    split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. destruct i as [|i]; cbn [nth_error].
    + rewrite Z.add_0_r. exact E.
    + replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. apply R. cbn [length] in Hi. lia.
Qed.

Lemma cell_of_bytes : forall (m : word -> option byte) a (n : nat) v,
  Mem.bytes_at segs m a (word_to_le_bytes n v) -> cell m a n v.
Proof.
  intros m a n v Hb. unfold LBNS.cell.
  pose proof (Mem.bytes_at_rdn segs m a _ 0 n Hb) as R. rewrite Z.add_0_r in R. cbn [skipn] in R.
  unfold word_to_le_bytes in *. rewrite Mem.length_Z_to_le_bytes in R. specialize (R ltac:(lia)).
  rewrite <- (Mem.length_Z_to_le_bytes n (bv_unsigned v)) in R at 2. rewrite firstn_all in R. exact R.
Qed.

(* [comment removed for export] *)
Lemma stk_of_rd_ok : forall (m : word -> option byte) a n, 0 <= a -> a + n <= 2 ^ 64 -> rd_ok m a n -> Frame.stk segs m a (a + n).
Proof.
  intros m a n Ha Hn Hrd. split; [exact Ha|]. split; [exact Hn|]. intros x Hx.
  specialize (Hrd (x - a) ltac:(lia)). replace (a + (x - a)) with x in Hrd by lia.
  change (LBNS.W x) with (Mem.wa x) in Hrd.
  destruct (m (Mem.wa x)) as [b|] eqn:E; [|exfalso; apply Hrd; reflexivity].
  split; [unfold wview; rewrite E; discriminate | exists b; unfold Mem.mrd; rewrite E; reflexivity].
Qed.

Lemma rd_ok_restrict : forall (M : word -> option byte) a n, 0 <= a -> a + n <= 2 ^ 47 -> rd_ok M a n -> rd_ok (mrestrict HI M) a n.
Proof.
  intros M a n Ha Hn Hrd i Hi. unfold mrestrict. rewrite HI_low by (rewrite LBNS.u_W by lia; lia). exact (Hrd i Hi).
Qed.

(* [comment removed for export] *)
Lemma wr_at_of_wr_ok : forall (M : word -> option byte) a n, 0 <= a -> a + n <= 2 ^ 47 -> wr_ok M a n -> Mem.wr_at segs (mrestrict HI M) a n.
Proof.
  intros M a n Ha Hn Hw. split; [exact Ha|]. split; [lia|]. intros i Hi.
  pose proof (Hw (a + i) 1%nat ltac:(lia) ltac:(lia)) as S. cbn [store_ok] in S.
  change (LBNS.W (a + i)) with (Mem.wa (a + i)) in S.
  rewrite (wview_mrestrict_eq segs HI M (Mem.wa (a + i))) by (apply HI_low; rewrite Mem.wa_unsigned by lia; lia).
  destruct (wview segs M (Mem.wa (a + i))); [discriminate | discriminate S].
Qed.

(* [comment removed for export] *)
Lemma cells_at_cons : forall (m : word -> option byte) a c cs, Cells.cell_wf c -> Mem.bytes_at segs m a (Cells.cbytes c) ->
  Cells.cells_at segs m (a + Z.of_nat (Cells.csize c)) cs -> Cells.cells_at segs m a (c :: cs).
Proof.
  intros m a c cs Hwf Hb [Hwfs Hbs]. split; [split; assumption|]. cbn [Cells.cells_bytes]. apply Mem.bytes_at_app.
  split; [exact Hb|]. rewrite Cells.cbytes_length by exact Hwf. exact Hbs.
Qed.
Lemma cells_at_nil : forall (m : word -> option byte) a, 0 <= a <= 2 ^ 64 -> Cells.cells_at segs m a [].
Proof. intros m a Ha. split; [exact I|]. apply Mem.bytes_at_nil. exact Ha. Qed.
Lemma cells_at_uncons : forall (m : word -> option byte) a c cs, Cells.cells_at segs m a (c :: cs) ->
  Mem.bytes_at segs m a (Cells.cbytes c) /\ Cells.cells_at segs m (a + Z.of_nat (Cells.csize c)) cs.
Proof.
  intros m a c cs [[Hwf Hwfs] Hb]. cbn [Cells.cells_bytes] in Hb. apply Mem.bytes_at_app in Hb as [Hb1 Hb2].
  rewrite Cells.cbytes_length in Hb2 by exact Hwf. split; [exact Hb1 | split; assumption].
Qed.

Theorem rehash_contract_of_walk : walk_stmt -> RHNS.rehash_contract segs T ilo ihi.
Proof.
  intros WALK regs M Bo No B N sp ra olds ks' pl ne0 tb0 G10 G11 G12 G2 G1 Hrh Hlen Hrng Hnd HN Hpow HNo Hra Hra4
    CB Cne Ctb CN Wm Hkeys Ord Nwr Nrd Swr Srd Sp16 Bo0 BoT Bo8 B0 BT B8 SpT BoI BI SpI Mlo Mhi AP1 AP2 AP3 RO.
  set (m := mrestrict HI M).
  assert (Usp : bv_unsigned (W sp) = sp) by (apply LBNS.u_W; lia).
  (* [comment removed for export] *)
  assert (P_map : Step.rw_cells segs m (r_map T) [Cells.C8 (Z_to_bv 64 B); Cells.C4 (W ne0); Cells.C4 (W tb0); Cells.C4 (Z_to_bv 64 N)]).
  { split; [| exact (wr_at_of_wr_ok M (r_map T) 20 ltac:(lia) ltac:(lia) Wm)].
    apply cells_at_cons; [exact I | exact (bytes_of_cell m (r_map T) 8 (W B) ltac:(lia) ltac:(lia) (cell_restrict M (r_map T) 8 (W B) ltac:(lia) ltac:(lia) CB)) |].
    apply cells_at_cons; [exact I | exact (bytes_of_cell m (r_map T + 8) 4 (W ne0) ltac:(lia) ltac:(lia) (cell_restrict M (r_map T + 8) 4 (W ne0) ltac:(lia) ltac:(lia) Cne)) |].
    cbn [Cells.csize]. replace (r_map T + Z.of_nat 8 + Z.of_nat 4) with (r_map T + 12) by lia.
    apply cells_at_cons; [exact I | exact (bytes_of_cell m (r_map T + 12) 4 (W tb0) ltac:(lia) ltac:(lia) (cell_restrict M (r_map T + 12) 4 (W tb0) ltac:(lia) ltac:(lia) Ctb)) |].
    cbn [Cells.csize]. replace (r_map T + 12 + Z.of_nat 4) with (r_map T + 16) by lia.
    apply cells_at_cons; [exact I | exact (bytes_of_cell m (r_map T + 16) 4 (W N) ltac:(lia) ltac:(lia) (cell_restrict M (r_map T + 16) 4 (W N) ltac:(lia) ltac:(lia) CN)) |].
    apply cells_at_nil. cbn [Cells.csize]. lia. }
  assert (P_keys : forall j, 0 <= j < No -> Step.ro_cells segs m (Bo + 32 * j) [Cells.C8 (Z_to_bv 64 (nth (Z.to_nat j) olds 0))]).
  { intros j Hj. apply cells_at_cons; [exact I | | apply cells_at_nil; cbn [Cells.csize]; lia].
    exact (bytes_of_cell m (Bo + 32 * j) 8 (W (nth (Z.to_nat j) olds 0)) ltac:(lia) ltac:(lia) (cell_restrict M (Bo + 32 * j) 8 (W (nth (Z.to_nat j) olds 0)) ltac:(lia) ltac:(lia) (Hkeys j Hj))). }
  pose proof (stk_of_rd_ok m Bo (32 * No) ltac:(lia) ltac:(lia) (rd_ok_restrict M Bo (32 * No) ltac:(lia) ltac:(lia) Ord)) as P_old.
  pose proof (stk_of_rd_ok m B (32 * N) ltac:(lia) ltac:(lia) (rd_ok_restrict M B (32 * N) ltac:(lia) ltac:(lia) Nrd)) as P_new.
  pose proof (stk_of_rd_ok m (sp - 16) 16 ltac:(lia) ltac:(lia) (rd_ok_restrict M (sp - 16) 16 ltac:(lia) ltac:(lia) Srd)) as P_frm.
  replace (sp - 16 + 16) with sp in P_frm by lia.
  assert (P_inv : Mem.mem_inv segs m).
  { apply Mem.mem_inv_intro.
    - intros a Ha. unfold Mem.seg_addr in Ha. unfold Mem.UTOP. change 0x800000000000 with (2 ^ 47). apply SEG_below.
      destruct (find_segment segs (bv_unsigned a) 1); [discriminate | discriminate Ha].
    - intros a b Hab. unfold m, mrestrict in Hab. destruct (HI a) eqn:EH; [discriminate Hab|].
      unfold HI in EH. apply Z.leb_gt in EH. split; [| unfold Mem.UTOP; change 0x800000000000 with (2 ^ 47); exact EH].
      unfold Mem.ro_addr. destruct (find_segment segs (bv_unsigned a) 1) as [sg|] eqn:Ef; [|reflexivity].
      destruct (seg_writable sg) eqn:Ew; [reflexivity|]. exfalso.
      destruct (find_segment_some_spec segs _ _ _ Ef) as (Hin & Hlo & Hhi).
      pose proof (RO sg Hin Ew (bv_unsigned a) ltac:(lia)) as X. rewrite LBNS.W_u in X. rewrite X in Hab. discriminate Hab. }
  (* [comment removed for export] *)
  pose proof (WALK (r_map T) Bo No B N olds ks' pl (W ne0) (W tb0) ra
                (getr regs (Z_to_bv 5 3)) (getr regs (Z_to_bv 5 4)) (getr regs (Z_to_bv 5 5)) (getr regs (Z_to_bv 5 6)) (getr regs (Z_to_bv 5 7))
                (getr regs (Z_to_bv 5 13)) (getr regs (Z_to_bv 5 14)) (getr regs (Z_to_bv 5 15)) (getr regs (Z_to_bv 5 16)) (getr regs (Z_to_bv 5 17))
                (getr regs (Z_to_bv 5 28)) (getr regs (Z_to_bv 5 29)) (getr regs (Z_to_bv 5 30)) (getr regs (Z_to_bv 5 31))
                (getr regs (Z_to_bv 5 8)) (getr regs (Z_to_bv 5 9)) (getr regs (Z_to_bv 5 18)) (getr regs (Z_to_bv 5 19)) (getr regs (Z_to_bv 5 20))
                (getr regs (Z_to_bv 5 21)) (getr regs (Z_to_bv 5 22)) (getr regs (Z_to_bv 5 23)) (getr regs (Z_to_bv 5 24)) (getr regs (Z_to_bv 5 25))
                (getr regs (Z_to_bv 5 26)) (getr regs (Z_to_bv 5 27)) (W sp) bvmap_empty (Z_to_bv 32 0) m
                Hrh Hlen Hrng Hnd HN Hpow HNo P_map P_keys P_old P_new) as X.
  rewrite Usp in X. specialize (X P_frm Sp16 Bo0 BoT BoI Bo8 B0 BT BI B8 SpI SpT AP1 AP2 AP3 Mlo Mhi Hra Hra4 P_inv).
  assert (Ecan : HBR.canon regs =
            Frame.mkR (Z_to_bv 64 ra) (W sp) (getr regs (Z_to_bv 5 3)) (getr regs (Z_to_bv 5 4)) (getr regs (Z_to_bv 5 5)) (getr regs (Z_to_bv 5 6)) (getr regs (Z_to_bv 5 7))
              (getr regs (Z_to_bv 5 8)) (getr regs (Z_to_bv 5 9)) (Z_to_bv 64 (r_map T)) (Z_to_bv 64 Bo) (Z_to_bv 64 (Bo + 32 * No))
              (getr regs (Z_to_bv 5 13)) (getr regs (Z_to_bv 5 14)) (getr regs (Z_to_bv 5 15)) (getr regs (Z_to_bv 5 16)) (getr regs (Z_to_bv 5 17))
              (getr regs (Z_to_bv 5 18)) (getr regs (Z_to_bv 5 19)) (getr regs (Z_to_bv 5 20))
              (getr regs (Z_to_bv 5 21)) (getr regs (Z_to_bv 5 22)) (getr regs (Z_to_bv 5 23)) (getr regs (Z_to_bv 5 24)) (getr regs (Z_to_bv 5 25))
              (getr regs (Z_to_bv 5 26)) (getr regs (Z_to_bv 5 27)) (getr regs (Z_to_bv 5 28)) (getr regs (Z_to_bv 5 29)) (getr regs (Z_to_bv 5 30))
              (getr regs (Z_to_bv 5 31))).
  { unfold HBR.canon.
    change (getr regs (Z_to_bv 5 1)) with (getr regs 1%bv). change (getr regs (Z_to_bv 5 2)) with (getr regs 2%bv).
    change (getr regs (Z_to_bv 5 10)) with (getr regs 10%bv). change (getr regs (Z_to_bv 5 11)) with (getr regs 11%bv).
    change (getr regs (Z_to_bv 5 12)) with (getr regs 12%bv). rewrite G1, G2, G10, G11, G12. reflexivity. }
  rewrite <- Ecan in X.
  destruct (HBR.evt_bridge segs HI HI_off Hwx _ regs (Z_to_bv 64 (r_entry T)) M (seg_rom segs) X)
    as (ms1 & ms2 & HQ & Hrun & Ereg & Efr & Epc & Esvc & Erv & Efc & Erom & Emem & HG).
  destruct HQ as (a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & m' & -> & Hmunch & Hwm & Hinv' & Hcnt & Hnew).
  cbn [MState.MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
  rewrite (HBR.mkst_eta ms2 Efr Esvc Erv Efc) in Hrun. rewrite Epc, Erom, Emem in Hrun.
  exists (ms_regs ms2), (munrestrict HI M m').
  split; [exact Hrun|].
  assert (Elow : forall x : word, bv_unsigned x < 2 ^ 47 -> munrestrict HI M m' x = m' x).
  { intros x Hx. unfold munrestrict. rewrite HI_low by exact Hx. reflexivity. }
  assert (Cup : forall a (n : nat) v, 0 <= a -> a + Z.of_nat n <= 2 ^ 47 -> cell m' a n v -> cell (munrestrict HI M m') a n v).
  { intros a n v Ha Hn Hc. unfold LBNS.cell in *. rewrite <- Hc. apply rdn_ext; [rewrite LBNS.u_W by lia; lia|].
    intros x Hx. rewrite LBNS.u_W in Hx by lia. apply Elow. lia. }
  split.
  { (* [comment removed for export] *)
    intros r Hnin. unfold getr. destruct (bv_eqb r 0) eqn:E0; [reflexivity|].
    assert (Hr : r <> 0%bv) by (intros ->; rewrite bv_eqb_refl in E0; discriminate E0).
    rewrite <- (Ereg r Hr). unfold LBNS.W in G1, G10, G12. rewrite <- G1, <- G2, <- G10, <- G12.
    destruct (HBR.reg_cases r Hr) as (k & Hk & ->).
    assert (Hk' : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12
                  \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23
                  \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31) by lia.
    clear - Hk' Hnin.
    repeat (destruct Hk' as [-> | Hk']); try (subst k);
      first [ reflexivity | exfalso; apply Hnin; vm_compute; solve [repeat (first [left; reflexivity | right])] ]. }
  destruct Hcnt as [Hcnt _]. apply cells_at_uncons in Hcnt as [Hc1 Hc2]. apply cells_at_uncons in Hc2 as [Hc2 _]. cbn [Cells.csize] in Hc2.
  replace (r_map T + 8 + Z.of_nat 4) with (r_map T + 12) in Hc2 by lia.
  split; [exact (Cup (r_map T + 8) 4%nat (W (Z.of_nat (length pl))) ltac:(lia) ltac:(lia) (cell_of_bytes m' _ 4 _ Hc1))|].
  split; [exact (Cup (r_map T + 12) 4%nat (W 0) ltac:(lia) ltac:(lia) (cell_of_bytes m' _ 4 _ Hc2))|].
  split.
  { intros d Hd. destruct (Hnew d Hd) as [Hcd _]. apply cells_at_uncons in Hcd as [Hcd _].
    exact (Cup (B + 32 * d) 8%nat (W (nth (Z.to_nat d) ks' 0)) ltac:(lia) ltac:(lia) (cell_of_bytes m' _ 8 _ Hcd)). }
  split.
  { intros x Hx. unfold munrestrict. destruct (HI x) eqn:EH; [reflexivity|].
    rewrite (Hmunch x).
    - unfold m, mrestrict. rewrite EH. reflexivity.
    - unfold RHNS.rh_FP, LBNS.inr in Hx. cbn [Frame.outside]. repeat split; try (intros Y; apply Hx; lia). }
  intros x Hx. unfold munrestrict. destruct (HI x) eqn:EH; [exact Hx|].
  apply HG. unfold mrestrict. rewrite EH. exact Hx.
Qed.

End RB.
End RHB.
