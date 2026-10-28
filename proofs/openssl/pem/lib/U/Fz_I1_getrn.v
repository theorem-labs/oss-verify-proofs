(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import InitMem. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_kit Fz_cimg Fz_I1_defs Fz_I1_hash. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition FZ_GETRN : Z := 0xe9e4c.
Definition GETRN_STACK : Z := 96.

Lemma zx32_small : forall z, 0 <= z < 2^32 -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma m_remu : forall a b : word, bv_unsigned b <> 0 -> mul_div Instr.M_REMU a b = Z_to_bv 64 (bv_unsigned a mod bv_unsigned b).
Proof.
  intros a b Hb. unfold mul_div. destruct (Z.eqb_spec (bv_unsigned b) 0) as [E|_]; [contradiction|].
  apply bv_eq. rewrite bv_modu_unsigned, Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
  pose proof (bv_unsigned_in_range _ a) as RA. pose proof (bv_unsigned_in_range _ b) as RB. pose proof (Z.mod_pos_bound (bv_unsigned a) (bv_unsigned b) ltac:(lia)). lia.
Qed.
Lemma m_divu : forall a b : word, bv_unsigned b <> 0 -> mul_div Instr.M_DIVU a b = Z_to_bv 64 (bv_unsigned a / bv_unsigned b).
Proof.
  intros a b Hb. unfold mul_div. destruct (Z.eqb_spec (bv_unsigned b) 0) as [E|_]; [contradiction|].
  apply bv_eq. rewrite bv_divu_unsigned, Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
  pose proof (bv_unsigned_in_range _ a) as RA. pose proof (bv_unsigned_in_range _ b) as RB.
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

Lemma zlxor_sign : forall n, 0 <= n < 2^63 -> Z.lxor n 9223372036854775808 = n + 9223372036854775808.
Proof.
  intros n Hn. symmetry. rewrite Z.add_nocarry_lxor; [reflexivity|]. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_0. destruct (Z.eq_dec i 63) as [->|NE].
  - replace (Z.testbit n 63) with false; [reflexivity|]. symmetry. apply Z.bits_above_log2; [lia|].
    destruct (Z.eq_dec n 0) as [->|NZ]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
  - change 9223372036854775808 with (2^63). rewrite (Z.pow2_bits_eqb 63 i) by lia. replace (63 =? i) with false by (symmetry; apply Z.eqb_neq; lia). apply Bool.andb_false_r.
Qed.

Ltac ubs_slot i b :=
  replace (0 <? b) with true by (symmetry; apply Z.ltb_lt; lia); replace (8 * i + b <? 1) with false by (symmetry; apply Z.ltb_ge; lia); cbn [Z.b2z];
  zstep; th_if_lit; zstep; zstep;
  replace (8 * i + b <? b) with false by (symmetry; apply Z.ltb_ge; lia); rewrite (zlxor_sign (8 * i)) by lia;
  replace (8 * i + 9223372036854775808 <? 0 + 9223372036854775808) with false by (symmetry; apply Z.ltb_ge; lia); cbn [Z.b2z];
  zstep; zstep; zstep; th_if_lit; zstep; ubs_if; zstep; zstep; ubs_if.

Lemma cown_al8 : forall s LBall L m p A n nm, RHEAP s LBall m -> cown LBall L p A n nm -> A mod 8 = 0 /\ 0 < A.
Proof.
  intros s LBall L m p A n nm H [IN _]. pose proof (RHEAP_block_range_proof _ _ _ _ H IN) as RR.
  unfold rblock_range, blk_addr, blk_size in RR. cbn [fst snd] in RR. destruct RR as (P & AL & _).
  split; [| exact P]. clear - AL. Z.div_mod_to_equations. lia.
Qed.

Definition getrn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem)
    (LBall : list block) (L : @clist bptr) (B na hp : Z) (bks : list (list (bptr * Z))) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' i ns1 ns2 rn (h : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rn) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (hp, hp + 8)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ 0 <= i < na /\ nth (Z.to_nat i) bks [] = ns1 ++ ns2
    /\ lseg DVERR m' LBall L (B + 8 * i) ns1 rn /\ chain DVERR m' LBall L rn ns2
    /\ rw_cells usegs m' hp [C8 h].

Theorem getrn_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (LBall : list block) (L : @clist bptr) (lh : Z) (pl pb : bptr) (B nmb : Z) (g : lh_geo) (bks : list (list (bptr * Z))) (data hp lo : Z) (old : word) (sH : PState) (mH : mem),
  lh_rep DVERR m LBall L ERR_FNS lh pl pb B nmb g bks ->
  (exists kw : word, rw_cells usegs m data [C8 kw]) -> (data + 8 <= lo \/ bv_unsigned sp <= data) -> (hp + 8 <= data \/ data + 8 <= hp) -> cimg m ->
  a0 = Z_to_bv 64 lh -> a1 = Z_to_bv 64 data -> a2 = Z_to_bv 64 hp ->
  rw_cells usegs m hp [C8 old] -> bv_unsigned sp <= hp -> hp mod 8 = 0 -> data mod 8 = 0 -> 0 < data -> RHEAP sH LBall mH ->
  stk usegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - GETRN_STACK -> mem_inv usegs m ->
  evt usegs (getrn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m LBall L B (g_nn g) hp bks)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 FZ_GETRN) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m LBall L lh pl pb B nmb g bks data hp lo old sH mH
         REP KEY0 KLOC KHP CI A0 A1 A2 HPC HPS HPAL DAL DNZ RH ST GLO CLO SLO MI. subst a0 a1 a2.
  pose proof REP as (G & OL & RL & (x40 & x48 & err & pad & SC) & OB & RB & LEN & CH & EMP & ND).
  pose proof (lh_geo_bounds g G) as GB. destruct G as (G1 & G2 & G3 & G4 & G5 & G6).
  destruct g as [nn na p pmax items]. cbn [g_nn g_na g_p g_pmax g_items] in *.
  pose proof (cown_al8 _ _ _ _ _ _ _ _ RH OL) as (LAL & _). pose proof (cown_al8 _ _ _ _ _ _ _ _ RH OB) as (BAL & _).
  unfold lh_cells, ERR_FNS, lf_comp, lf_hash, lf_hashw, lf_compw, wz in SC. cbn [g_nn g_na g_p g_pmax g_items] in SC.
  pose proof err_hash_ok as HASH. unfold lh_hash_ok, ERR_FNS, lf_hash, lf_hashw in HASH.
  pose proof err_comp_ok as COMP. unfold lh_comp_ok, ERR_FNS, lf_comp, lf_compw in COMP.
  unfold FZ_GETRN, GETRN_STACK, GLOBALS_TOP, LH_KMAX in *.
  assert (KEYAT : forall mc, munch [(bv_unsigned sp - 96, bv_unsigned sp); (hp, hp + 8)]%Z m mc -> wmono usegs m mc -> cb_arg mc (Z_to_bv 64 (bv_unsigned sp + -64)) lo data).
  { intros mc MUc WMc. destruct KEY0 as [kw KC]. pose proof (bv_unsigned_in_range _ sp) as SPR0. change (bv_modulus 64) with (2^64) in SPR0. split; [| split; [| split]].
    - exists kw. eapply rw_cells_transport; [exact KC| exact MUc| exact WMc|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - rewrite unsigned_lit by lia. lia.
    - exact DAL.
    - exact DNZ. }
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (hp, hp + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  pose proof (rw_cells_bound _ _ _ _ HPC) as HPB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HPB.
  (* [comment removed for export] *)
  step. carve_frame 64%nat ST. do 9 step. step. step. ubs_if. do 5 step.
  step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CI0 : cimg mm) by (eapply cimg_seg; [exact CI| exact MU|]; intros a Ha; unfold cimg_addr, RMallocRep.RGOT_SSP in Ha; cbn [outside]; unfold ceil_window in *; lia) end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (KEYAT mm MU WM) as KA0 end.
  calle (eapply HASH with (d := data) (lo := lo)); try lia.
  step. step. step. step. ubs_if.
  step. step. rewrite (zx32_small pmax) by lia. step. if_cases KP; zify_cond KP. { exfalso. rewrite ?unsigned_lit in KP by lia. lia. }
  step. step.
  rewrite (zx32_small p) by lia. rewrite m_remu by (rewrite unsigned_lit by lia; lia). rewrite (unsigned_lit pmax) by lia.
  lazymatch goal with HPh : rw_cells _ _ hp [C8 ?hh] |- _ => set (h := hh) in * end.
  assert (WOUT : forall a, 0 <= a < alloc_ceiling -> outside [(bv_unsigned sp - 96, bv_unsigned sp); (hp, hp + 8)]%Z a) by (intros a Ha; cbn [outside]; lia).
  assert (SWR : forall z, 0 <= z < 2^31 -> bv_swrap 32 z = z).
  { intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z. rewrite Z.mod_small by lia. lia. }
  (* [comment removed for export] *)
  assert (SCAT : forall mc, munch [(bv_unsigned sp - 96, bv_unsigned sp); (hp, hp + 8)]%Z m mc -> wmono usegs m mc ->
    exists x40 x48 err pad, rw_cells usegs mc lh [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 954500); C8 (Z_to_bv 64 954384); C8 (Z_to_bv 64 0xe90d4); C8 (Z_to_bv 64 954612); C8 x40; C8 x48;
                     C4 (Z_to_bv 64 nn); C4 (Z_to_bv 64 na); C4 (Z_to_bv 64 p); C4 (Z_to_bv 64 pmax); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 items); C4 err; C4 pad]).
  { intros mc MUc WMc. destruct REP as (_ & _ & _ & (x40' & x48' & err' & pad' & SCm) & _). exists x40', x48', err', pad'.
    unfold lh_cells, ERR_FNS, lf_comp, lf_hash, lf_hashw, lf_compw, wz in SCm. cbn [g_nn g_na g_p g_pmax g_items] in SCm.
    eapply rw_cells_transport; [exact SCm| exact MUc| exact WMc|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
  (* [comment removed for export] *)
  assert (EXIT : forall (idx rn : Z) (ns1 ns2 : list (bptr * Z)) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 : word) (mc : mem),
    0 <= idx < nn -> nth (Z.to_nat idx) bks [] = ns1 ++ ns2 ->
    lseg DVERR m LBall L (B + 8 * idx) ns1 rn -> chain DVERR m LBall L rn ns2 ->
    rw_cells usegs mc (bv_unsigned sp + -64) [CB 8 (take 8 (take 16 (take 24 (take 32 (take 40 (take 48 (take 56 junk))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs mc lo (bv_unsigned sp + -64) -> rw_cells usegs mc hp [C8 h] ->
    munch [(bv_unsigned sp - 96, bv_unsigned sp); (hp, hp + 8)]%Z m mc -> wmono usegs m mc -> mem_inv usegs mc ->
    evt usegs (getrn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m LBall L B nn hp bks)
      (MS (mkR y0 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13
               y14 y15 (Z_to_bv 64 rn) y16 s6 s7 s8 s9 s10 s11 y17 y18 y19 y20)
          F (Z_to_bv 64 0xe9f64) fc None mc (seg_rom usegs))).
  { intros idx rn ns1 ns2 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 mc IDXR ENTH S1 C2 FRc STc HPc MUc WMc MIc.
    do 9 step. release_frame FRc STc (bv_unsigned sp). step.
    apply evt_done. unfold getrn_post. do 14 eexists. exists mc, idx, ns1, ns2, rn, h.
    assert (CR : 0 <= B + 8 * idx /\ B + 8 * idx + 8 <= alloc_ceiling) by lia.
    split; [reflexivity|]. split; [exact MUc|]. split; [exact WMc|]. split; [exact MIc|]. split; [exact STc|]. split; [exact IDXR|]. split; [exact ENTH|].
    split; [eapply lseg_munch; eassumption|]. split; [| exact HPc].
    eapply chain_munch; try eassumption. exact (lseg_end_range _ _ _ _ _ _ _ S1 CR). }
  (* [comment removed for export] *)
  assert (BODY : forall (idx : Z) (ns1 rest : list (bptr * Z)) (c : Z) (pn : bptr) (A : Z)
      (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : word) (mc : mem),
    0 <= idx < nn -> nth (Z.to_nat idx) bks [] = ns1 ++ (pn, A) :: rest ->
    lseg DVERR m LBall L (B + 8 * idx) ns1 c -> chain DVERR m LBall L c ((pn, A) :: rest) ->
    (forall (q : bptr) (Bq : Z) (rest' : list (bptr * Z)) (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 : word) (mc' : mem),
       rest = (q, Bq) :: rest' ->
       lseg DVERR m LBall L (B + 8 * idx) (ns1 ++ [(pn, A)]) (A + 8) -> chain DVERR m LBall L (A + 8) ((q, Bq) :: rest') ->
       rw_cells usegs mc' (bv_unsigned sp + -64) [CB 8 (take 8 (take 16 (take 24 (take 32 (take 40 (take 48 (take 56 junk))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
       stk usegs mc' lo (bv_unsigned sp + -64) -> rw_cells usegs mc' hp [C8 h] ->
       munch [(bv_unsigned sp - 96, bv_unsigned sp); (hp, hp + 8)]%Z m mc' -> wmono usegs m mc' -> mem_inv usegs mc' ->
       evt usegs (getrn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m LBall L B nn hp bks)
         (MS (mkR z0 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp z1 z2 z3 sp (Z_to_bv 64 lh) z4 z5 z6 z7 z8 z9 z10 z11
                  (Z_to_bv 64 data) h (Z_to_bv 64 (A + 8)) (Z_to_bv 64 Bq) s6 s7 s8 s9 s10 s11 z12 z13 z14 z15)
            F (Z_to_bv 64 0xe9f14) fc None mc' (seg_rom usegs))) ->
    rw_cells usegs mc (bv_unsigned sp + -64) [CB 8 (take 8 (take 16 (take 24 (take 32 (take 40 (take 48 (take 56 junk))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs mc lo (bv_unsigned sp + -64) -> rw_cells usegs mc hp [C8 h] ->
    munch [(bv_unsigned sp - 96, bv_unsigned sp); (hp, hp + 8)]%Z m mc -> wmono usegs m mc -> mem_inv usegs mc ->
    evt usegs (getrn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m LBall L B nn hp bks)
      (MS (mkR y0 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp y1 y2 y3 sp (Z_to_bv 64 lh) y4 y5 y6 y7 y8 y9 y10 y11
               (Z_to_bv 64 data) h (Z_to_bv 64 c) (Z_to_bv 64 A) s6 s7 s8 s9 s10 s11 y12 y13 y14 y15)
         F (Z_to_bv 64 0xe9f14) fc None mc (seg_rom usegs))).
  { intros idx ns1 rest c pn A y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 mc IDXR ENTH S1 C2 CONT FRc STc HPc MUc WMc MIc.
    pose proof C2 as (c' & (CC & OWN & RG & (d & hN & N1 & DVd & N2) & RSEG) & TERM).
    assert (DRd : 0x2c0638 <= d /\ d + 16 <= 0x32e038) by (pose proof (proj2 DVd d ltac:(lia)) as X; pose proof (proj2 DVd (d + 15) ltac:(lia)) as Y; unfold cimg_addr, RMallocRep.RGOT_SSP in X, Y; lia).
    set (nxt := match rest with [] => 0 | (_, Bq) :: _ => Bq end).
    assert (NXm : rw_cells usegs m (A + 8) [C8 (Z_to_bv 64 nxt)]).
    { unfold nxt. destruct rest as [|[q Bq] rest']; cbn [lseg] in RSEG; [subst c'; exact TERM| exact (proj1 RSEG)]. }
    assert (S1' : lseg DVERR m LBall L (B + 8 * idx) (ns1 ++ [(pn, A)]) (A + 8)).
    { eapply lseg_app; [exact S1|]. cbn [lseg]. split; [exact CC|]. split; [exact OWN|]. split; [exact RG|]. split; [exists d, hN; auto| reflexivity]. }
    (* [comment removed for export] *)
    assert (NEXT : forall (z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 : word) (mc2 : mem),
      rw_cells usegs mc2 (bv_unsigned sp + -64) [CB 8 (take 8 (take 16 (take 24 (take 32 (take 40 (take 48 (take 56 junk))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      stk usegs mc2 lo (bv_unsigned sp + -64) -> rw_cells usegs mc2 hp [C8 h] ->
      munch [(bv_unsigned sp - 96, bv_unsigned sp); (hp, hp + 8)]%Z m mc2 -> wmono usegs m mc2 -> mem_inv usegs mc2 ->
      evt usegs (getrn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m LBall L B nn hp bks)
        (MS (mkR z0 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp z1 z2 z3 sp (Z_to_bv 64 lh) z4 z5 z6 z7 z8 z9 z10 z11
                 (Z_to_bv 64 data) h z16 (Z_to_bv 64 A) s6 s7 s8 s9 s10 s11 z12 z13 z14 z15)
            F (Z_to_bv 64 0xe9f58) fc None mc2 (seg_rom usegs))).
    { intros z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 mc2 FR2 ST2 HP2 MU2 WM2 MI2.
      assert (NX2 : rw_cells usegs mc2 (A + 8) [C8 (Z_to_bv 64 nxt)]).
      { eapply rw_cells_transport; [exact NXm| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
      do 2 step.
      destruct rest as [|[q Bq] rest'].
      - (* [comment removed for export] *)
        step. if_cases K9; zify_cond K9. { exfalso. unfold nxt in K9. rewrite ?unsigned_lit in K9 by lia. lia. }
        eapply (EXIT idx (A + 8) (ns1 ++ [(pn, A)]) []); try eassumption.
        + rewrite <- app_assoc. exact ENTH.
        + exists (A + 8). split; [reflexivity|]. cbn [lseg] in RSEG. subst c'. exact TERM.
      - pose proof RSEG as (_ & _ & RGq & _). cbn [lseg] in RSEG.
        step. if_cases K9; zify_cond K9. 2:{ exfalso. unfold nxt in K9. rewrite ?unsigned_lit in K9 by lia. lia. }
        eapply (CONT q Bq rest'); try eassumption; [reflexivity|]. exists c'. split; [exact RSEG| exact TERM]. }
    assert (N1c : rw_cells usegs mc A [C8 (Z_to_bv 64 d)]).
    { eapply rw_cells_transport; [exact N1| exact MUc| exact WMc|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
    assert (N2c : rw_cells usegs mc (A + 16) [C8 hN]).
    { eapply rw_cells_transport; [exact N2| exact MUc| exact WMc|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
    destruct (SCAT mc MUc WMc) as (x40c & x48c & errc & padc & SCc).
    (* [comment removed for export] *)
    pose proof (cown_al8 _ _ _ _ _ _ _ _ RH OWN) as (AAL & _). step. step. ubs_if.
    step. step. if_cases K5.
    { eapply NEXT; eassumption. }
    (* [comment removed for export] *)
    step. step. if_cases K6; zify_cond K6. { exfalso. rewrite ?unsigned_lit in K6 by lia. lia. }
    do 4 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (CIc : cimg mm) by (eapply cimg_seg; [exact CI| exact MUc|]; intros a Ha; unfold cimg_addr, RMallocRep.RGOT_SSP in Ha; cbn [outside]; unfold ceil_window in *; lia) end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (KEYAT mm MUc WMc) as KAc; pose proof (cb_arg_dv mm (Z_to_bv 64 (bv_unsigned sp + -64)) lo d CIc DVd ltac:(unfold GLOBALS_TOP; lia)) as KAd end.
    calle (eapply COMP with (d1 := d) (d2 := data) (lo := lo)); try lia.
    step. if_cases K7.
    - (* [comment removed for export] *) eapply (EXIT idx c ns1 ((pn, A) :: rest)); eassumption.
    - step. eapply NEXT; eassumption. }
  (* [comment removed for export] *)
  assert (LOOP : forall (rest : list (bptr * Z)) (idx : Z) (ns1 : list (bptr * Z)) (c : Z) (pn : bptr) (A : Z)
      (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : word) (mc : mem),
    0 <= idx < nn -> nth (Z.to_nat idx) bks [] = ns1 ++ (pn, A) :: rest ->
    lseg DVERR m LBall L (B + 8 * idx) ns1 c -> chain DVERR m LBall L c ((pn, A) :: rest) ->
    rw_cells usegs mc (bv_unsigned sp + -64) [CB 8 (take 8 (take 16 (take 24 (take 32 (take 40 (take 48 (take 56 junk))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs mc lo (bv_unsigned sp + -64) -> rw_cells usegs mc hp [C8 h] ->
    munch [(bv_unsigned sp - 96, bv_unsigned sp); (hp, hp + 8)]%Z m mc -> wmono usegs m mc -> mem_inv usegs mc ->
    evt usegs (getrn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m LBall L B nn hp bks)
      (MS (mkR y0 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp y1 y2 y3 sp (Z_to_bv 64 lh) y4 y5 y6 y7 y8 y9 y10 y11
               (Z_to_bv 64 data) h (Z_to_bv 64 c) (Z_to_bv 64 A) s6 s7 s8 s9 s10 s11 y12 y13 y14 y15)
         F (Z_to_bv 64 0xe9f14) fc None mc (seg_rom usegs))).
  { induction rest as [|[q Bq] rest' IH]; intros idx ns1 c pn A y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 mc IDXR ENTH S1 C2 FRc STc HPc MUc WMc MIc.
    - eapply (BODY idx ns1 [] c pn A); try eassumption. intros q Bq rest' z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 mc' E. discriminate E.
    - eapply (BODY idx ns1 ((q, Bq) :: rest') c pn A); try eassumption.
      intros q0 Bq0 rest0 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 mc' E S1' C2' FR' ST' HP' MU' WM' MI'. inversion E; subst q0 Bq0 rest0.
      eapply (IH idx (ns1 ++ [(pn, A)]) (A + 8) q Bq); try eassumption. rewrite <- app_assoc. exact ENTH. }
  (* [comment removed for export] *)
  assert (IDX : forall (idx : Z) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 : word) (mc : mem),
    0 <= idx < nn ->
    rw_cells usegs mc (bv_unsigned sp + -64) [CB 8 (take 8 (take 16 (take 24 (take 32 (take 40 (take 48 (take 56 junk))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs mc lo (bv_unsigned sp + -64) -> rw_cells usegs mc hp [C8 h] ->
    munch [(bv_unsigned sp - 96, bv_unsigned sp); (hp, hp + 8)]%Z m mc -> wmono usegs m mc -> mem_inv usegs mc ->
    evt usegs (getrn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m LBall L B nn hp bks)
      (MS (mkR y0 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp y1 y2 y3 sp (Z_to_bv 64 lh) y4 (Z_to_bv 64 idx) y5 y6 y7 y8 y9 y10
               (Z_to_bv 64 data) h y11 y12 s6 s7 s8 s9 s10 s11 y13 y14 y15 y16)
         F (Z_to_bv 64 0xe9ed0) fc None mc (seg_rom usegs))).
  { intros idx y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 mc IDXR FRc STc HPc MUc WMc MIc.
    destruct (SCAT mc MUc WMc) as (x40c & x48c & errc & padc & SCc).
    pose proof (CH idx ltac:(lia)) as CHI.
    assert (EA : Z.land (bv_swrap 32 (idx + 0)) 18446744073709551615 ≪ 3 = 8 * idx).
    { rewrite Z.add_0_r, SWR by lia. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
      rewrite Z.shiftl_mul_pow2 by lia. lia. }
    destruct (nth (Z.to_nat idx) bks []) as [|[pn A] rest] eqn:ENTH.
    - (* [comment removed for export] *)
      pose proof CHI as (c' & E & TERM). cbn [lseg] in E. subst c'.
      assert (TC : rw_cells usegs mc (B + 8 * idx) [C8 (Z_to_bv 64 0)]).
      { eapply rw_cells_transport; [exact TERM| exact MUc| exact WMc|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
      remember (B + 8 * idx) as cb eqn:ECB.
      do 4 zstep. rewrite EA.
      zstep. zstep. ubs_slot idx B.
      replace (8 * idx + B) with cb by lia.
      zstep.
      zstep. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. reflexivity. }
      subst cb.
      eapply (EXIT idx (B + 8 * idx) [] []); try eassumption; reflexivity.
    - pose proof CHI as (c' & (CC & OWN & RG & NC & RSEG) & TERM).
      assert (TC : rw_cells usegs mc (B + 8 * idx) [C8 (Z_to_bv 64 A)]).
      { eapply rw_cells_transport; [exact CC| exact MUc| exact WMc|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
      remember (B + 8 * idx) as cb eqn:ECB.
      do 4 zstep. rewrite EA.
      zstep. zstep. ubs_slot idx B.
      replace (8 * idx + B) with cb by lia.
      zstep.
      zstep. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
      subst cb.
      eapply (LOOP rest idx [] (B + 8 * idx) pn A); try eassumption; reflexivity. }
  (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1.
  - eapply (IDX (bv_unsigned h mod pmax)); try eassumption. pose proof (Z.mod_pos_bound (bv_unsigned h) pmax ltac:(lia)). lia.
  - step. rewrite (zx32_small na) by lia. step. if_cases KN; zify_cond KN. { exfalso. rewrite ?unsigned_lit in KN by lia. lia. }
    step. rewrite m_remu by (rewrite unsigned_lit by lia; lia). rewrite (unsigned_lit na) by lia.
    eapply (IDX (bv_unsigned h mod na)); try eassumption.
    rewrite ?unsigned_lit in K1 by lia.
    pose proof (Z.mod_pos_bound (bv_unsigned h) na ltac:(lia)) as RB0.
    rewrite <- (Z.mod_mod_divide (bv_unsigned h) na pmax ltac:(exists 2; lia)) in K1.
    set (r := bv_unsigned h mod na) in *. clearbody r. clear - K1 RB0 G1 G2 G3 G4. subst na nn.
    assert (Q : r / pmax = 0 \/ r / pmax = 1) by (assert (0 <= r / pmax < 2) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]); lia).
    pose proof (Z.div_mod r pmax ltac:(lia)). destruct Q as [Q|Q]; rewrite Q in *; lia.
Qed.
End WithCeiling0.
