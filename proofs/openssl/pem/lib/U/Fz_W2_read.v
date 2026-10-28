(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy.
     From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_W1_defs Fz_W1_sync Fz_W1_bits Fz_W1_read Fz_W1_misc Fz_W3_iface Fz_W2_rep.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation wz := (Z_to_bv 64) (only parsing).
Definition hideP (X : Prop) : Prop := X.
Ltac hide H := lazymatch type of H with ?X => change X with (hideP X) in H end.

Lemma sgtz_pos : forall z, 0 < z < 2 ^ 63 -> v_slt (wz 0) (wz z) = wz 1.
Proof.
  intros z Hz. rewrite v_slt_b2z, !unsigned_lit by lia. rewrite !zb_lxor_sign by lia.
  rewrite (Z.mod_small (0 + 2 ^ 63)), (Z.mod_small (z + 2 ^ 63)) by lia. replace (0 + 2 ^ 63 <? z + 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bread_conv_proof :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo BI BB BM RP D len max off fl outl OUT PP meth : Z) (rmaxw flw : word) (junk ojunk oldb : list byte),
    a0 = wz BI -> a1 = wz OUT -> a2 = wz outl -> a3 = wz PP -> 0 < BI -> 0 < OUT -> 0 < outl -> outl <= len - off -> 0 < PP -> PP + 8 <= 2 ^ 64 ->
    ro_cells usegs m BI [C8 (wz 0); C8 (wz meth); C8 (wz 0); C8 (wz 0); C8 (wz 0)] -> ro_cells usegs m (meth + 40) [C8 (wz 0x183440)] ->
    rw_cells usegs m (BI + 48) [C4 (wz fl)] -> fl_ok fl -> ro_cells usegs m (BI + 64) [C8 (wz BB)] ->
    0 < BB -> BB + 16 < 2 ^ 63 -> ro_cells usegs m BB [C8 (wz BM); C8 (wz RP)] ->
    0 < RP -> rw_cells usegs m RP (readp_cells len D off rmaxw flw) ->
    0 < D -> 0 <= off -> len <= max -> max < 2 ^ 31 - 1 -> D + max < 2 ^ 63 ->
    length junk = Z.to_nat max -> rw_cells usegs m D [CB (Z.to_nat max) junk] ->
    length ojunk = Z.to_nat outl -> rw_cells usegs m OUT [CB (Z.to_nat outl) ojunk] ->
    rw_cells usegs m PP [CB 8 oldb] ->
    BI mod 8 = 0 -> BB mod 8 = 0 -> BM mod 8 = 0 -> RP mod 8 = 0 -> 0 < meth -> meth mod 8 = 0 -> PP mod 8 = 0 ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 112 ->
    BI + 128 <= lo -> BB + 16 <= lo -> RP + 32 <= lo -> D + max <= lo -> OUT + outl <= lo -> meth + 48 <= lo -> bv_unsigned sp <= PP ->
    (D + max <= RP \/ RP + 32 <= D) -> (OUT + outl <= D \/ D + max <= OUT) -> (OUT + outl <= RP \/ RP + 32 <= OUT) ->
    (OUT + outl <= BI \/ BI + 128 <= OUT) -> (BI + 128 <= D \/ D + max <= BI) -> (BI + 128 <= RP \/ RP + 32 <= BI) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' rmaxw' : word) (fl' : Z) (ojunk' : list byte) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (BI + 48, BI + 52); (OUT, OUT + outl); (RP, RP + 24); (PP, PP + 8)] m m'
                 /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
                 /\ fl_ok fl' /\ rw_cells usegs m' (BI + 48) [C4 (wz fl')]
                 /\ rw_cells usegs m' RP (readp_cells len D (off + outl) rmaxw' flw)
                 /\ length ojunk' = Z.to_nat outl /\ rw_cells usegs m' OUT [CB (Z.to_nat outl) ojunk']
                 /\ rw_cells usegs m' PP [C8 (wz outl)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz 0x10cd74) fc None m (seg_rom usegs)).
Proof.
  intros until oldb.
  intros -> -> -> -> HBI HOUT HOUTL HON HPP HPP64 HEAD MBRO FLC FLOK PTRC HBB HBB63 BBC HRP RPC HD HOFF0 HLEN HMAX HD63 LJ DBLK LOJ OUTB PPC
         BI8 BB8 BM8 RP8 HM0 HM8 PP8 ST LO0 LO
         SBI SBB SRP SD SOUT SMETH SPP APDR APOD APOR APOB APBD APBR MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (BI + 48, BI + 52); (OUT, OUT + outl); (RP, RP + 24); (PP, PP + 8)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  unfold readp_cells in RPC.
  ths. th_frame 32%nat [8; 8; 8; 8]%nat ST. do 4 ths. ths. ths.
  ths. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
  ths. ths. ths. ths. if_cases K1; zify_cond K1. 2: { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
  ths. ubs_if.
  ths. ths. ubs_if.
  ths.
  ths. ubs_if.
  ths. ths. ubs_if.
  ths. ths. ths.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mb end.
  eapply evt_cut.
  { eapply W1_read_data_proof with (lo := lo) (BI := BI) (BB := BB) (BM := BM) (RP := RP) (D := D) (len := len) (max := max) (off := off) (fl := fl) (outl := outl)
                                   (OUT := OUT) (rmaxw := rmaxw) (flw := flw) (junk := junk) (ojunk := ojunk); th_strip_ulit.
    1-3: reflexivity. all: try first [eassumption | lia]. all: cycle -1. 1: unfold Fz_W1_write.tbox; repeat split; lia.
  }
  cbv beta. intros ms' PO.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & rmaxw' & fl' & ojunk' & mz & -> & MUc & WMc & MIz & STz & FLOK' & FLCz & RPCz & LOJ' & OUTz).
  unfold readp_cells in RPCz. rewrite !unsigned_lit in MUc by lia. rewrite unsigned_lit in STz by lia. th_ret_lit.
  rewrite (Z.min_l outl (len - off)) in * by (clear - HON; lia).
  lazymatch goal with H : rw_cells usegs mb (bv_unsigned sp + -32) _ |- _ => rename H into FRc end.
  Ltac trw H MUc WMc := eapply rw_cells_transport in H; [| exact MUc| exact WMc| cbn [length disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]].
  Ltac trr H MUc := eapply ro_cells_transport in H; [| exact MUc| cbn [length disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]].
  trw FRc MUc WMc. 2: { clear - RSP SPP SBI SRP SOUT LO; lia. } trw PPC MUc WMc. 2: { clear - RSP SPP SBI SRP SOUT LO; lia. }
  assert (MUz : munch [(bv_unsigned sp - 112, bv_unsigned sp); (BI + 48, BI + 52); (OUT, OUT + outl); (RP, RP + 24); (PP, PP + 8)]%Z m mz).
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUc]. unfold sub_fp. cbn [outside]. clear - RSP. intros a Ha. lia. }
  pose proof (wmono_trans _ _ _ _ WM WMc) as WMz. clear MU WM MUc WMc.
  pose proof FLOK' as [FLR' FLB'].
  ths. rewrite (t_zx32_small fl') by lia. ths. ths. rewrite (unsigned_lit fl') in * by lia.
  ths. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. clear - K2 HOUTL; lia. } clear K2.
  ths. ths. ths. ths.
  ths. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. clear - K3 HOUTL HON HLEN HMAX HOFF0; lia. } clear K3.
  ths. if_cases K4; zify_cond K4.
  { exfalso. rewrite (ubs_land7 PP), (proj2 (Z.ltb_lt 0 PP)) in K4 by lia. cbv in K4. discriminate K4. } clear K4.
  ths. ths. ths. ths. ths. do 4 ths. ths. th_release FRc (bv_unsigned sp). ths.
  finish. 2: eassumption. 1: eapply fl_ok_land; [exact FLOK'| clear; lia]. 1: exact RPCz. 1: exact LOJ'. exact OUTz.
Qed.

(* [comment removed for export] *)
Lemma meth_bread : forall m meth, cimg m -> mem_inv usegs m -> (meth = M_MEM \/ meth = M_SECMEM) ->
  rw_cells usegs m (meth + 32) [C8 (wz 0x10cd74)] /\ rw_cells usegs m (meth + 40) [C8 (wz 0x183440)].
Proof.
  intros m meth CIMG MI [-> | ->]; unfold M_MEM, M_SECMEM.
  - cimg_cell CIMG m (0x2d3fc8 + 32) [C8 (wz 0x10cd74)] H1. cimg_cell CIMG m (0x2d3fc8 + 40) [C8 (wz 0x183440)] H2. split; [exact H1| exact H2].
  - cimg_cell CIMG m (0x2d4038 + 32) [C8 (wz 0x10cd74)] H1. cimg_cell CIMG m (0x2d4038 + 40) [C8 (wz 0x183440)] H2. split; [exact H1| exact H2].
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem bio_read_proof : bio_read_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB0 L f K po BI BM meth len max off OUT no n lo Bd blw ojunk
         CST SLO MBX HN OWNO NTO NNO LOJ OUTC SP16 -> -> ->.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  unfold BREAD_STACK, FZ_BIO_READ, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  destruct MBX as (BB & RP & fl & rrw & padw & nr & nw & OWNB & NDK & METH & HEAD & W1C & FLOK & TAIL & INNER).
  destruct INNER as (rmaxw & OWNbb & BBC & OWNbm & OWNrp & OFF & LENM & MAX31 & DOPT).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNB)) as (BI0 & BI16 & _ & BIC & BIIMG).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNbb)) as (BB0 & BB16 & _ & BBCe & BBIMG).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNbm)) as (BM0 & BM16 & _ & BMCe & BMIMG).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNrp)) as (RP0 & RP16 & _ & RPCe & RPIMG).
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNO)) as (OUT0 & _ & _ & OUTCe & OUTIMG).
  pose proof (meth_bread m meth CIMG MI METH) as [MBR MBRO].
  unfold bio_head in HEAD. unfold bio_tail in TAIL. unfold M_MEM, M_SECMEM in METH. unfold bio_w1_cells in W1C.
  assert (BI8 : BI mod 8 = 0) by (clear - BI16; Z.div_mod_to_equations; lia).
  assert (BB8 : BB mod 8 = 0) by (clear - BB16; Z.div_mod_to_equations; lia).
  assert (BM8 : BM mod 8 = 0) by (clear - BM16; Z.div_mod_to_equations; lia).
  assert (RP8 : RP mod 8 = 0) by (clear - RP16; Z.div_mod_to_equations; lia).
  assert (HM8 : meth mod 8 = 0) by (clear - METH; destruct METH as [-> | ->]; reflexivity).
  assert (PP8 : (bv_unsigned sp + -24) mod 8 = 0) by (clear - SP16; Z.div_mod_to_equations; lia).
  change ([C8 (wz 4294967297); C4 (wz fl); C4 rrw; C4 (wz 4294967295); C4 padw; C8 (wz BB)]) with ([C8 (wz 4294967297)] ++ [C4 (wz fl)] ++ [C4 rrw; C4 (wz 4294967295); C4 padw] ++ [C8 (wz BB)]) in W1C.
  apply (proj1 (rw_cells_app usegs m _ _ _)) in W1C. destruct W1C as [ISW W1C].
  apply (proj1 (rw_cells_app usegs m _ _ _)) in W1C. destruct W1C as [FLC W1C].
  apply (proj1 (rw_cells_app usegs m _ _ _)) in W1C. destruct W1C as [MIDC PTRC]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ app] in FLC, MIDC, PTRC.
  replace (BI + 40 + 8) with (BI + 48) in FLC by lia. replace (BI + 40 + 8 + 4) with (BI + 52) in MIDC by lia. replace (BI + 40 + 8 + 4 + 12) with (BI + 64) in PTRC by lia.
  change 4294967297 with (1 + 2 ^ 32 * 1) in ISW. apply (proj2 (t_cells_halves usegs m (BI + 40) 1 1 ltac:(lia) ltac:(lia))) in ISW.
  (* [comment removed for export] *)
  destruct (k_d K) as [pd|] eqn:KD. 2: { exfalso. destruct DOPT as (MAX0 & _). clear - MAX0 HN LENM OFF. lia. }
  destruct DOPT as (D & nm & junk0 & OWNd & MAXP & BMC & RPC & LJ & DC). unfold readp_cells in RPC.
  pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNd)) as (D0 & _ & _ & DCe & DIMG).
  (* [comment removed for export] *)
  pose proof NDK as NDK0. unfold mbio_blocks in NDK. rewrite KD in NDK. cbn [app] in NDK.
  assert (ND : k_bi K <> k_bb K /\ k_bi K <> k_bm K /\ k_bi K <> k_rp K /\ k_bi K <> pd /\ k_bb K <> k_rp K /\ k_bm K <> k_rp K /\ k_rp K <> pd).
  { clear - NDK. inversion NDK as [|x1 l1 N1 ND1]; subst. inversion ND1 as [|x2 l2 N2 ND2]; subst. inversion ND2 as [|x3 l3 N3 ND3]; subst. inversion ND3 as [|x4 l4 N4 ND4]; subst.
    cbn [In] in N1, N2, N3, N4. repeat split; intros E; rewrite E in *; tauto. }
  destruct ND as (N12 & N13 & N14 & N15 & N24 & N34 & N45). clear NDK.
  assert (NO : po <> k_bi K /\ po <> k_bb K /\ po <> k_bm K /\ po <> k_rp K /\ po <> pd).
  { generalize NTO KD; clear; intros NTO KD. unfold mbio_T in NTO. rewrite KD in NTO. repeat split; intros E; apply NTO; rewrite E; tauto. }
  destruct NO as (NO1 & NO2 & NO3 & NO4 & NO5).
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNB) (proj1 OWNbb) N12) as A12.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNB) (proj1 OWNbm) N13) as A13.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNB) (proj1 OWNrp) N14) as A14.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNB) (proj1 OWNd) N15) as A15.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNbb) (proj1 OWNrp) N24) as A24.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNbm) (proj1 OWNrp) N34) as A34.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNrp) (proj1 OWNd) N45) as A45.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNO) (proj1 OWNB) NO1) as AO1.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNO) (proj1 OWNbb) NO2) as AO2.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNO) (proj1 OWNbm) NO3) as AO3.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNO) (proj1 OWNrp) NO4) as AO4.
  pose proof (cstate_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST (proj1 OWNO) (proj1 OWNd) NO5) as AO5.
  hide N12. hide N13. hide N14. hide N15. hide N24. hide N34. hide N45. hide NO1. hide NO2. hide NO3. hide NO4. hide NO5. hide NTO.
  hide A12. hide A13. hide A14. hide A15. hide A24. hide A34. hide A45. hide AO1. hide AO2. hide AO3. hide AO4. hide AO5.
  hide BIIMG. hide BBIMG. hide BMIMG. hide RPIMG. hide OUTIMG. hide DIMG.
  assert (INB : In (k_bi K, BI, 128) LBall) by exact (proj1 OWNB). assert (INR : In (k_rp K, RP, 32) LBall) by exact (proj1 OWNrp). assert (INO : In (po, OUT, no) LBall) by exact (proj1 OWNO).
  (* [comment removed for export] *)
  destruct (rw_cells_CB_split_at usegs m OUT (Z.to_nat no) ojunk (Z.to_nat n) ltac:(clear - HN NNO; lia) OUTC) as [OA OZ]. clear OUTC.
  pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp); (BI + 48, BI + 52); (BI + 96, BI + 104); (OUT, OUT + n); (RP, RP + 24)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  (* [comment removed for export] *)
  cprefix. ths. th_frame 32%nat [8; 8; 8; 8]%nat ST. ths. ths. ths.
  ths. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. clear - K0 HN LENM MAX31 OFF; lia. } clear K0.
  ths. ths.
  (* [comment removed for export] *)
  lazymatch goal with H : stk usegs _ lo _ |- _ => rename H into ST1 end.
  ths. th_frame 80%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat ST1. do 9 ths. ths.
  ths. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. clear - K1 BI0 BIC CW; lia. } clear K1.
  ths. ths. ths. ubs_if.
  ths. ths. ths. ths.
  ths. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. clear - K2 METH; lia. } clear K2.
  ths. ths. ths. ubs_if.
  ths. ths. th_if_lit.
  ths. ths. ths. ths. th_if_lit.
  ths. ths. th_if_lit.
  ths. ths. th_if_lit.
  ths. ths. ubs_if.
  ths. ths. ubs_if.
  ths. ths. ths. ths. ths. ths.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mc0 end.
  lazymatch goal with H : stk usegs mc0 lo _ |- _ => rename H into STc end. lazymatch goal with H : mem_inv usegs mc0 |- _ => rename H into MIc end.
  lazymatch goal with H : munch _ m mc0 |- _ => rename H into MUq end. lazymatch goal with H : wmono usegs m mc0 |- _ => rename H into WMq end.
  lazymatch goal with H : rw_cells usegs mc0 (bv_unsigned sp + -32) _ |- _ => rename H into FR1 end.
  lazymatch goal with H : rw_cells usegs mc0 (bv_unsigned sp + -112) _ |- _ => rename H into FR2 end.
  lazymatch type of FR1 with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3] => change [c0; c1; c2; c3] with ([c0] ++ [c1] ++ [c2; c3]) in FR1 end.
  apply (proj1 (rw_cells_app usegs mc0 _ _ _)) in FR1. destruct FR1 as [FR1a FR1]. apply (proj1 (rw_cells_app usegs mc0 _ _ _)) in FR1. destruct FR1 as [PPC FR1c].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ app] in PPC, FR1c.
  replace (bv_unsigned sp + -32 + 8) with (bv_unsigned sp + -24) in PPC by lia. replace (bv_unsigned sp + -32 + 8 + 8) with (bv_unsigned sp + -16) in FR1c by lia.
  eapply evt_cut.
  { eapply bread_conv_proof with (lo := lo) (BI := BI) (BB := BB) (BM := BM) (RP := RP) (D := D) (len := len) (max := max) (off := off) (fl := fl) (outl := n) (OUT := OUT)
                                (PP := bv_unsigned sp + -24) (meth := meth) (rmaxw := rmaxw) (flw := wz (msec meth)) (junk := junk0) (ojunk := firstn (Z.to_nat n) ojunk).
    1-4: reflexivity.
    all: only 1-50: [> exact BI0| exact OUT0| clear - HN; lia| clear - HN; lia| clear - SLO SPR LO GLO; lia| clear - SPR SPB; lia
      | exact (proj1 HEAD)| exact (proj1 MBRO)| exact FLC| exact FLOK| exact (proj1 PTRC)| exact BB0| clear - BBCe CW; lia| exact (proj1 BBC)| exact RP0| unfold readp_cells; exact RPC
      | exact D0| clear - OFF; lia| exact LENM| exact MAX31| clear - DCe CW; lia| exact LJ| exact DC| rewrite firstn_length, LOJ; clear - HN NNO; lia| exact OA| exact PPC
      | exact BI8| exact BB8| exact BM8| exact RP8| clear - METH; lia| exact HM8| exact PP8
      | rewrite unsigned_lit by lia; exact STc| clear - LO CEIL_RANGE__; unfold ceil_window in *; lia| rewrite unsigned_lit by lia; clear - SLO SPR; lia
      | clear - BIC LO; lia| clear - BBCe LO; lia| clear - RPCe LO; lia| clear - DCe LO; lia| clear - OUTCe LO HN NNO; lia| clear - METH GLO; lia| rewrite unsigned_lit by lia; clear - SPR; lia
      | unfold hideP in A45; clear - A45; lia| unfold hideP in AO5; clear - AO5 HN NNO; lia| unfold hideP in AO4; clear - AO4 HN NNO; lia| unfold hideP in AO1; clear - AO1 HN NNO; lia
      | unfold hideP in A15; clear - A15; lia| unfold hideP in A14; clear - A14; lia| exact MIc]. }
  cbv beta. intros ms' PO.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & rmaxw' & fl' & ojunk' & mz & -> & MUc & WMc & MIz & STz & FLOK' & FLCz & RPCz & LOJ' & OUTz & PPz).
  unfold readp_cells in RPCz. rewrite !unsigned_lit in MUc by lia. rewrite unsigned_lit in STz by lia. th_ret_lit.
  trw FR1a MUc WMc. 2: { clear - SPR BIC OUTCe RPCe LO SLO HN NNO; lia. } trw FR1c MUc WMc. 2: { clear - SPR BIC OUTCe RPCe LO SLO HN NNO; lia. }
  trw FR2 MUc WMc. 2: { clear - SPR BIC OUTCe RPCe LO SLO HN NNO; lia. }
  trw HEAD MUc WMc. 2: { unfold hideP in AO1, A14; clear - SPR BIC OUTCe RPCe LO SLO HN NNO AO1 A14; lia. }
  trw ISW MUc WMc. 2: { unfold hideP in AO1, A14; clear - SPR BIC OUTCe RPCe LO SLO HN NNO AO1 A14; lia. }
  trw MIDC MUc WMc. 2: { unfold hideP in AO1, A14; clear - SPR BIC OUTCe RPCe LO SLO HN NNO AO1 A14; lia. }
  trw PTRC MUc WMc. 2: { unfold hideP in AO1, A14; clear - SPR BIC OUTCe RPCe LO SLO HN NNO AO1 A14; lia. }
  trw TAIL MUc WMc. 2: { unfold hideP in AO1, A14; clear - SPR BIC OUTCe RPCe LO SLO HN NNO AO1 A14; lia. }
  trw BBC MUc WMc. 2: { unfold hideP in A12, AO2, A24; clear - SPR BIC BBCe OUTCe RPCe LO SLO HN NNO A12 AO2 A24; lia. }
  trw BMC MUc WMc. 2: { unfold hideP in A13, AO3, A34; clear - SPR BIC BMCe OUTCe RPCe LO SLO HN NNO A13 AO3 A34; lia. }
  trw DC MUc WMc. 2: { unfold hideP in A15, AO5, A45; clear - SPR BIC DCe OUTCe RPCe LO SLO HN NNO A15 AO5 A45 MAXP; rewrite ?Z2Nat.id by lia; lia. }
  trw OZ MUc WMc. 2: { unfold hideP in AO1, AO4; clear - SPR BIC OUTCe RPCe LO SLO HN NNO AO1 AO4; rewrite ?Z2Nat.id by lia; lia. }
  assert (MUz : munch [(bv_unsigned sp - 224, bv_unsigned sp); (BI + 48, BI + 52); (BI + 96, BI + 104); (OUT, OUT + n); (RP, RP + 24)]%Z m mz).
  { eapply munch_trans; [exact MUq|]. eapply munch_weaken; [| exact MUc]. unfold sub_fp. cbn [outside]. clear - SPR. intros a Ha. lia. }
  pose proof (wmono_trans _ _ _ _ WMq WMc) as WMz. clear MUq WMq MUc WMc STc MIc OA PPC.
  assert (NR : 0 <= n < 2 ^ 31) by (clear - HN LENM MAX31 OFF; lia).
  (* [comment removed for export] *)
  ths. ths. ths. th_if_lit. ths. ubs_if. ths. ubs_if.
  ths. ths. ths. unfold hideP in A12, A13, A14, A15, AO1. ths. hide A12. hide A13. hide A14. hide A15. hide AO1.
  ths. ths. ths. th_if_lit. ths. ths. th_if_lit.
  ths. ths. th_if_lit. ths. ubs_if. ths. th_if_lit. ths.
  ths. if_cases K3; zify_cond K3. 2: { exfalso. rewrite ?unsigned_lit in K3 by lia. clear - K3; lia. } clear K3.
  ths. do 9 ths. ths. th_release FR2 (bv_unsigned sp - 32). ths.
  (* [comment removed for export] *)
  ths. th_if_lit.
  replace n with (n + 2 ^ 32 * 0) in PPz by (clear; lia). apply (proj2 (t_cells_halves usegs _ (bv_unsigned sp + -24) n 0 ltac:(clear - NR; lia) ltac:(clear; lia))) in PPz.
  ths. rewrite (t_sx32_small n) by (clear - NR; lia). ths. ths. ths. ths.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mf end.
  assert (FRm : rw_cells usegs mf (bv_unsigned sp + -24) ([C4 (wz n); C4 (wz 0)] ++ [C8 s0; C8 ra])).
  { apply (proj2 (rw_cells_app usegs mf _ _ _)). split; [exact PPz|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
    replace (bv_unsigned sp + -24 + 8) with (bv_unsigned sp + -16) by (clear; lia). exact FR1c. }
  assert (FRj : rw_cells usegs mf (bv_unsigned sp + -32) ([CB 8 (firstn 8 junk)] ++ [C4 (wz n); C4 (wz 0); C8 s0; C8 ra])).
  { apply (proj2 (rw_cells_app usegs mf _ _ _)). split; [exact FR1a|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
    replace (bv_unsigned sp + -32 + 8) with (bv_unsigned sp + -24) by (clear; lia). cbn [app] in FRm. exact FRm. }
  cbn [app] in FRj. clear FR1a PPz FR1c FRm. th_release FRj (bv_unsigned sp). ths.
  lazymatch goal with H : stk usegs mf lo _ |- _ => rename H into STf end. lazymatch goal with H : mem_inv usegs mf |- _ => rename H into MIf end.
  lazymatch goal with H : munch _ m mf |- _ => rename H into MUf end. lazymatch goal with H : wmono usegs m mf |- _ => rename H into WMf end.
  chere. apply climpl_done.
  exists (wz n), mf, LBall. split; [unfold cret; do 14 eexists; reflexivity|]. split; [clear; lia|]. split; [clear; unfold cgrow; lia|].
  split. { eapply (cstate_seg _ _ _ _ _ m mf _ sp _ lo Bd (bv_unsigned sp)); [exact CST| exact MUf| exact WMf| exact MIf| | clear - SLO SPR; lia| exact SPB| | exact STf| exact SPB].
    - apply Forall_cons; [apply cwin_stack; clear - SLO SPR; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (k_bi K, BI, 128)); [exact INB| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (k_bi K, BI, 128)); [exact INB| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (po, OUT, no)); [exact INO| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear - HN NNO; lia|].
      apply Forall_cons; [apply (cwin_block _ _ _ (k_rp K, RP, 32)); [exact INR| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia| apply Forall_nil].
    - cbn [disjoint_from]. unfold LX_FLAGS. unfold hideP in BIIMG, RPIMG, OUTIMG. clear - SLO SPR GLO BIIMG RPIMG OUTIMG HN NNO. lia. }
  split. { eapply cframe_seg; [apply cframe_refl| exact MUf| exact WMf| exact HP| clear - SLO SPR LO; lia|].
    apply Forall_cons; [apply cseg_ok_stack; clear - SLO SPR LO; lia|].
    apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (k_bi K, BI, 128)); [exact INB| intros b0 _ NT E; apply NT; rewrite E; left; unfold mbio_T; cbn [blk_id fst]; left; reflexivity| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia|].
    apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (k_bi K, BI, 128)); [exact INB| intros b0 _ NT E; apply NT; rewrite E; left; unfold mbio_T; cbn [blk_id fst]; left; reflexivity| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia|].
    apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (po, OUT, no)); [exact INO| intros b0 _ NT E; apply NT; rewrite E; right; reflexivity| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear - HN NNO; lia|].
    apply Forall_cons; [apply (cseg_ok_block _ _ _ _ _ (k_rp K, RP, 32)); [exact INR| intros b0 _ NT E; apply NT; rewrite E; left; unfold mbio_T; cbn [blk_id fst]; do 3 right; left; reflexivity| |]; unfold blk_addr, blk_size; cbn [fst snd]; clear; lia| apply Forall_nil]. }
  exists (ojunk' ++ skipn (Z.to_nat n) ojunk). split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split. { eexists BB, RP, fl', rrw, padw, _, nw. split; [exact OWNB|]. split; [exact NDK0|]. split; [unfold M_MEM, M_SECMEM; exact METH|]. split; [exact HEAD|].
    split. { unfold bio_w1_cells. change ([C8 (wz 4294967297); C4 (wz fl'); C4 rrw; C4 (wz 4294967295); C4 padw; C8 (wz BB)]) with ([C8 (wz 4294967297)] ++ [C4 (wz fl')] ++ [C4 rrw; C4 (wz 4294967295); C4 padw] ++ [C8 (wz BB)]).
      apply rw_cells_app. split; [change 4294967297 with (1 + 2 ^ 32 * 1); apply (proj1 (t_cells_halves usegs mf (BI + 40) 1 1 ltac:(lia) ltac:(lia))); exact ISW|].
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (BI + 40 + 8) with (BI + 48) by (clear; lia).
      apply rw_cells_app. split; [exact FLCz|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (BI + 48 + 4) with (BI + 52) by (clear; lia).
      apply rw_cells_app. split; [exact MIDC|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (BI + 52 + 12) with (BI + 64) by (clear; lia). exact PTRC. }
    split; [exact FLOK'|]. split; [exact TAIL|].
    exists rmaxw'. split; [exact OWNbb|]. split; [exact BBC|]. split; [exact OWNbm|]. split; [exact OWNrp|]. split; [clear - HN OFF; lia|]. split; [exact LENM|]. split; [exact MAX31|].
    rewrite KD. exists D, nm, junk0. split; [exact OWNd|]. split; [exact MAXP|]. split; [exact BMC|]. split; [exact RPCz|]. split; [exact LJ| exact DC]. }
  split; [rewrite length_app, skipn_length, LOJ', LOJ; clear - HN NNO; lia|].
  replace (Z.to_nat no) with (Z.to_nat n + (Z.to_nat no - Z.to_nat n))%nat at 1 by (clear - HN NNO; lia). exact (rw_cells_CB_join usegs mf OUT _ _ _ _ OUTz OZ).
Qed.
End WithCeiling0.
