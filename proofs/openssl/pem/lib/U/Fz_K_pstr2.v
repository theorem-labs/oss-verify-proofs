(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhPure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_I1_defs Fz_I1_rep. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_I2_ppi. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import F_strlen F_memcpy Fz_K_rep Fz_K_pstr1.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation z64 := (Z_to_bv 64 0) (only parsing).

Definition q_of (nm : bool) (Q1 Q2 : Z) : Z := if nm then Q1 else Q2.
Definition sl_off (nm : bool) : Z := if nm then 32 else 40.
Definition cnt_of (nm : bool) (ni vi : Z) : Z := if nm then ni else vi.
Definition ni_after (nm : bool) (ni : Z) : Z := if nm then ni + 1 else ni.
Definition vi_after (nm : bool) (vi : Z) : Z := if nm then vi else vi + 1.
Definition FZ_SK_PUSH_ : Z := 0xe6c80.

(* [comment removed for export] *)
Definition pstr_seg2_post (sp gp tp s7 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (ra0 s0e s1e s2e s3e s4e s5e s6e s8e : word) (j8 : list byte)
    (nm : bool) (S LK lh1 lh2 ni vi Q1 Q2 Ls : Z) (str : list byte) (ps : bptr)
    (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (m : mem) (lo Bd : Z)
    : nat -> @clist bptr -> PState -> machine_state -> Prop :=
  fun f' L' s' ms' => exists (pn : bptr) (An : Z) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0xf0d9c) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp (Z_to_bv 64 S) (Z_to_bv 64 (q_of nm Q1 Q2)) (Z_to_bv 64 (An + 12))
                  a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (t_of nm lh1 lh2)) (Z_to_bv 64 (q_of nm Q1 Q2)) (Z_to_bv 64 Ls) (Z_to_bv 64 An) (Z_to_bv 64 (An + 12))
                  (Z_to_bv 64 (Z.of_nat (length str))) (Z_to_bv 64 (S + pidx_off nm)) s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 FZ_SK_PUSH_) fc None m' (seg_rom usegs)
    /\ (f - 1 <= f')%nat /\ L' = (pn, Z.of_nat (length str) + 16) :: L
    /\ cgrow L L' (wA (Z.of_nat (length str) + 16)) (wB (Z.of_nat (length str) + 16)) (wBig (Z.of_nat (length str) + 16))
    /\ cstate s' ((pn, An, Z.of_nat (length str) + 16) :: LBall) LB L' m' (Z_to_bv 64 (bv_unsigned sp + -96)) tp lo Bd
    /\ cframe (eq ps) [] (bv_unsigned sp - 96) s LBall L m s' ((pn, An, Z.of_nat (length str) + 16) :: LBall) L' m'
    /\ rblock_range An (Z.of_nat (length str) + 16)
    /\ rw_cells usegs m' (bv_unsigned sp + -96) (pstr_frame Ls j8 s8e s7 s6e s5e s4e s3e s2e s1e s0e ra0)
    /\ rw_cells usegs m' S (psd_cells LK lh1 lh2 (ni_after nm ni) (vi_after nm vi) Q1 Q2)
    /\ rw_cells usegs m' An [C8 (Z_to_bv 64 (An + 12)); C4 (Z_to_bv 64 (cnt_of nm ni vi + 1)); CB (Datatypes.S (length str)) (str ++ [Z_to_bv 8 0])].

Lemma pstr_seg2_true : crypto_malloc_stmt ->
  forall (sp gp tp s7 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (ra0 s0e s1e s2e s3e s4e s5e s6e s8e : word) (j8 : list byte)
         (y0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
         (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo Bd : Z)
         (S LK lh1 lh2 ni vi Q1 Q2 Ls : Z) (str slack : list byte) (ps : bptr),
  (1 <= f)%nat -> croom L (wA (Z.of_nat (length str) + 16)) (wB (Z.of_nat (length str) + 16)) (wBig (Z.of_nat (length str) + 16)) ->
  cstate s LBall LB L m (Z_to_bv 64 (bv_unsigned sp + -96)) tp lo Bd -> 96 <= bv_unsigned sp -> lo <= bv_unsigned sp - 96 - CM_STACK ->
  rw_cells usegs m (bv_unsigned sp + -96) (pstr_frame Ls j8 s8e s7 s6e s5e s4e s3e s2e s1e s0e ra0) ->
  In (ps, S, 48) LBall -> rw_cells usegs m S (psd_cells LK lh1 lh2 ni vi Q1 Q2) -> 0 <= ni -> ni + 1 < 2 ^ 31 -> 0 <= vi -> vi + 1 < 2 ^ 31 ->
  ro_bytes usegs Ls (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> (- (Ls + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  0x10000 <= Ls -> Ls + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= 0x2c0000 -> Z.of_nat (length str) < 2 ^ 20 ->
  climpl f L s
    (MS (mkR y0 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp (Z_to_bv 64 S) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (t_of true lh1 lh2)) (Z_to_bv 64 (nmz true)) (Z_to_bv 64 Ls) (Z_to_bv 64 0) (Z_to_bv 64 1) s7 (Z_to_bv 64 (pidx_off true)) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xf0cfc) fc None m (seg_rom usegs))
    (pstr_seg2_post sp gp tp s7 s9 s10 s11 F fc ra0 s0e s1e s2e s3e s4e s5e s6e s8e j8 true S LK lh1 lh2 ni vi Q1 Q2 Ls str ps s LBall LB L f m lo Bd).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CM. intros until ps. intros Hf ROOM CST SP96 SLO FR INS SCS NI0 NI1 VI0 VI1 ROB NONUL PAD SLOW SHIGH LEN.
  cbn [nmz t_of pidx_off q_of sl_off cnt_of ni_after vi_after] in *.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  unfold CM_STACK, RMALLOC_STACK, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. rewrite unsigned_lit in ST, SPB by lia.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  set (len := Z.of_nat (length str)) in *.
  pose proof (RHEAP_block_range_proof _ _ _ _ HP INS) as RS. unfold blk_addr, blk_size in RS. cbn [fst snd] in RS. destruct RS as (S0 & _ & _ & SC48 & SIMG).
  unfold psd_cells in SCS. unfold pstr_frame in FR.
  pose proof (munch_refl [(bv_unsigned sp - 96 - 8240, bv_unsigned sp - 96)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  assert (STRa : bytes_at usegs m Ls (str ++ Z_to_bv 8 0 :: slack)) by (apply ro_bytes_at; [exact MI| lia| rewrite length_app; cbn [length]; lia| exact ROB]).
  (* [comment removed for export] *)
  cprefix. step. step.
  tcall (strlen_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ str slack).
  all: try first [eassumption | lia].
  cbv beta delta [mkR]. fold len.
  (* [comment removed for export] *)
  step. step. step. step. step. step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => rename mm into mb end.
  lazymatch goal with H : stk _ mb _ _ |- _ => rename H into STb end. lazymatch goal with H : mem_inv _ mb |- _ => rename H into MIb end.
  assert (CSTb : cstate s LBall LB L mb (Z_to_bv 64 (bv_unsigned sp + -96)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m mb _ _ _ lo Bd (bv_unsigned sp - 96)); [exact CST| exact MU| exact WM| exact MIb| | lia| lia| | rewrite unsigned_lit by lia; exact STb| rewrite unsigned_lit by lia; lia].
    - constructor; [apply cwin_stack; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FRb : cframe (eq ps) [] (bv_unsigned sp - 96) s LBall L m s LBall L mb).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
  eapply climpl_seq.
  { eapply CM with (n := len + 16) (lo := lo) (B := Bd); [lia| exact ROOM| lia| exact CSTb| rewrite unsigned_lit by lia; unfold CM_STACK, RMALLOC_STACK; lia| subst len; reflexivity]. }
  intros f1 L1 st1 ms1 (v1 & m1 & LBall1 & RET1 & FU1 & GR1 & CST1 & FRM1 & (pn & An & junk1 & -> & -> & -> & RNG & NEW)).
  destruct RET1 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM1 by lia).
  pose proof FRM1 as (CFR1 & KP1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
  assert (INS1 : In (ps, S, 48) ((pn, An, len + 16) :: LBall)) by (right; exact INS).
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (ps, S, 48) CFR1 SCS INS (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize]; lia)) as SCS1.
  clear FR SCS STRa.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _). rewrite unsigned_lit in ST1 by lia.
  pose proof RNG as (An0 & An16 & _ & AnC & AnIMG).
  assert (An8 : An mod 8 = 0) by (clear - An16; Z.div_mod_to_equations; lia).
  assert (INA : In (pn, An, len + 16) ((pn, An, len + 16) :: LBall)) by (left; reflexivity).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _].
  assert (PNEW : forall q Aq nq, In (q, Aq, nq) LBall -> pn <> q).
  { intros q Aq nq Hin E. cbn [map blk_id fst] in ND1. inversion ND1 as [|xx ll NIx _]; subst xx ll. apply NIx. subst q. apply in_map_iff. exists (pn, Aq, nq). auto. }
  assert (APAS : An + (len + 16) <= S \/ S + 48 <= An) by (eapply (own_apart _ _ _ pn An (len + 16) ps S 48 HP1 INA INS1); exact (PNEW _ _ _ INS)).
  assert (STR1 : bytes_at usegs m1 Ls (str ++ Z_to_bv 8 0 :: slack)) by (apply ro_bytes_at; [exact MI1| lia| rewrite length_app; cbn [length]; lia| exact ROB]).
  assert (STRz : bytes_at usegs m1 Ls (str ++ [Z_to_bv 8 0])).
  { apply ro_bytes_at; [exact MI1| lia| rewrite length_app; cbn [length]; lia|].
    clear - ROB. revert ROB. generalize Ls. induction str as [|b str IH]; intros S0 H; cbn [app ro_bytes] in H |- *; [exact (conj (proj1 H) I)| exact (conj (proj1 H) (IH _ (proj2 H)))]. }
  (* [comment removed for export] *)
  change (Z.to_nat (len + 16)) with (Z.to_nat (len + 16)) in NEW.
  apply (rw_cells_split_CB usegs m1 An [] (Z.to_nat (len + 16)) junk1 [] [8; 4; Datatypes.S (length str); 3]%nat) in NEW; [| cbn [sum_nat]; lia].
  cbn [mk_CB_cells app] in NEW.
  (* [comment removed for export] *)
  change ([CB 8 (take 8 junk1); CB 4 (take 4 (drop 8 junk1)); CB (Datatypes.S (length str)) (take (Datatypes.S (length str)) (drop 4 (drop 8 junk1)));
           CB 3 (take 3 (drop (Datatypes.S (length str)) (drop 4 (drop 8 junk1))))])
    with ([CB 8 (take 8 junk1); CB 4 (take 4 (drop 8 junk1))] ++ [CB (Datatypes.S (length str)) (take (Datatypes.S (length str)) (drop 4 (drop 8 junk1)))]
          ++ [CB 3 (take 3 (drop (Datatypes.S (length str)) (drop 4 (drop 8 junk1))))]) in NEW.
  apply (proj1 (rw_cells_app usegs m1 _ _ _)) in NEW. destruct NEW as [NHD NEW]. apply (proj1 (rw_cells_app usegs m1 _ _ _)) in NEW. destruct NEW as [NBODY NTL].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in NBODY, NTL.
  replace (An + Z.of_nat 12) with (An + 12) in NBODY by lia.
  replace (An + Z.of_nat 12 + Z.pos (Pos.of_succ_nat (length str))) with (An + 12 + (len + 1)) in NTL by lia.
  pose proof (munch_refl [(An, An + (len + 16)); (S + 24, S + 32)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  (* [comment removed for export] *)
  cprefix. step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
  step. step. step. ubs_if. do 5 step. step.
  tcall (memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (str ++ [Z_to_bv 8 0])).
  all: try first [eassumption | lia | rewrite length_app; cbn [length]; lia].
  { replace (Z.to_nat (len + 1)) with (Datatypes.S (length str)) by lia. exact NBODY. }
  cbv beta delta [mkR].
  (* [comment removed for export] *)
  assert (SWR : forall z, 0 <= z < 2^31 -> bv_swrap 32 z = z).
  { intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z. rewrite Z.mod_small by lia. lia. }
  step. rewrite (t_sx32_small ni) by lia. step. rewrite (unsigned_lit ni), (SWR (ni + 1)) by lia.
  cstep.
  step. if_cases K3; zify_cond K3; rewrite ?Z_to_bv_signed, ?bv_swrap_small in K3 by (unfold bv_half_modulus, bv_modulus; cbn; lia).
  { exfalso. lia. } clear K3.
  cstep. cstep.
  step. if_cases K2; zify_cond K2; try (exfalso; rewrite ?unsigned_lit in K2 by lia; lia). clear K2.
  step. th_if_lit. step. step.
  step. step. step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mf end.
  chere. apply climpl_done. unfold pstr_seg2_post. cbn [nmz t_of pidx_off q_of sl_off cnt_of ni_after vi_after].
  exists pn, An. do 13 eexists. exists mf.
  split; [reflexivity|]. split; [exact FU1|]. split; [reflexivity|]. split; [exact GR1|].
  lazymatch goal with H : stk usegs mf _ _ |- _ => rename H into STf end. lazymatch goal with H : mem_inv usegs mf |- _ => rename H into MIf end.
  split. { eapply (cstate_seg _ _ _ _ _ m1 mf _ _ tp lo Bd (bv_unsigned sp - 96)); [exact CST1| exact MU1| exact WM1| exact MIf| | lia| lia| | rewrite unsigned_lit by lia; exact STf| rewrite unsigned_lit by lia; lia].
    - constructor; [| constructor; [| constructor]].
      + apply (cwin_block _ _ _ (pn, An, len + 16)); [exact INA| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
      + apply (cwin_block _ _ _ (ps, S, 48)); [exact INS1| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. clear - AnIMG SIMG An0 S0. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FRb| exact FRM1| lia| intros a X; exact X| intros q _ _ Y; exact Y]| exact MU1| exact WM1| exact HP1| lia|].
    constructor; [| constructor; [| constructor]].
    - apply (cseg_ok_block _ _ _ _ _ (pn, An, len + 16)); [exact INA| | |]; unfold blk_addr, blk_size; cbn [fst snd]; try lia.
      destruct FRb as (_ & KPb & _). exact (cfresh_new _ _ _ _ _ _ KPb ND1).
    - apply (cseg_ok_block _ _ _ _ _ (ps, S, 48)); [exact INS1| | |]; unfold blk_addr, blk_size; cbn [fst snd]; try lia.
      intros b0 _ NT E. apply NT. unfold blk_id in *. cbn [fst] in E. rewrite E. reflexivity. }
  split; [exact RNG|]. split; [unfold pstr_frame; assumption|]. split; [unfold psd_cells; assumption|].
  lazymatch goal with H0 : rw_cells usegs mf An ?c0, H12 : rw_cells usegs mf (An + 12) ?c12 |- _ =>
    pose proof (proj2 (rw_cells_app usegs mf An c0 c12) (conj H0 H12)) as NJ end.
  cbn [app] in NJ. replace (Z.to_nat (len + 1)) with (Datatypes.S (length str)) in NJ by lia. exact NJ.
Qed.

Lemma pstr_seg2_false : crypto_malloc_stmt ->
  forall (sp gp tp s7 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (ra0 s0e s1e s2e s3e s4e s5e s6e s8e : word) (j8 : list byte)
         (y0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
         (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo Bd : Z)
         (S LK lh1 lh2 ni vi Q1 Q2 Ls : Z) (str slack : list byte) (ps : bptr),
  (1 <= f)%nat -> croom L (wA (Z.of_nat (length str) + 16)) (wB (Z.of_nat (length str) + 16)) (wBig (Z.of_nat (length str) + 16)) ->
  cstate s LBall LB L m (Z_to_bv 64 (bv_unsigned sp + -96)) tp lo Bd -> 96 <= bv_unsigned sp -> lo <= bv_unsigned sp - 96 - CM_STACK ->
  rw_cells usegs m (bv_unsigned sp + -96) (pstr_frame Ls j8 s8e s7 s6e s5e s4e s3e s2e s1e s0e ra0) ->
  In (ps, S, 48) LBall -> rw_cells usegs m S (psd_cells LK lh1 lh2 ni vi Q1 Q2) -> 0 <= ni -> ni + 1 < 2 ^ 31 -> 0 <= vi -> vi + 1 < 2 ^ 31 ->
  ro_bytes usegs Ls (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> (- (Ls + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  0x10000 <= Ls -> Ls + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= 0x2c0000 -> Z.of_nat (length str) < 2 ^ 20 ->
  climpl f L s
    (MS (mkR y0 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp (Z_to_bv 64 S) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (t_of false lh1 lh2)) (Z_to_bv 64 (nmz false)) (Z_to_bv 64 Ls) (Z_to_bv 64 0) (Z_to_bv 64 1) s7 (Z_to_bv 64 (pidx_off false)) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xf0cfc) fc None m (seg_rom usegs))
    (pstr_seg2_post sp gp tp s7 s9 s10 s11 F fc ra0 s0e s1e s2e s3e s4e s5e s6e s8e j8 false S LK lh1 lh2 ni vi Q1 Q2 Ls str ps s LBall LB L f m lo Bd).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CM. intros until ps. intros Hf ROOM CST SP96 SLO FR INS SCS NI0 NI1 VI0 VI1 ROB NONUL PAD SLOW SHIGH LEN.
  cbn [nmz t_of pidx_off q_of sl_off cnt_of ni_after vi_after] in *.
  pose proof CST as (HP & CO & (errv & AV & SPB & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
  unfold CM_STACK, RMALLOC_STACK, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. rewrite unsigned_lit in ST, SPB by lia.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  set (len := Z.of_nat (length str)) in *.
  pose proof (RHEAP_block_range_proof _ _ _ _ HP INS) as RS. unfold blk_addr, blk_size in RS. cbn [fst snd] in RS. destruct RS as (S0 & _ & _ & SC48 & SIMG).
  unfold psd_cells in SCS. unfold pstr_frame in FR.
  pose proof (munch_refl [(bv_unsigned sp - 96 - 8240, bv_unsigned sp - 96)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  assert (STRa : bytes_at usegs m Ls (str ++ Z_to_bv 8 0 :: slack)) by (apply ro_bytes_at; [exact MI| lia| rewrite length_app; cbn [length]; lia| exact ROB]).
  (* [comment removed for export] *)
  cprefix. step. step.
  tcall (strlen_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ str slack).
  all: try first [eassumption | lia].
  cbv beta delta [mkR]. fold len.
  (* [comment removed for export] *)
  step. step. step. step. step. step. chere.
  lazymatch goal with |- climpl _ _ _ (MS _ _ _ _ _ ?mm _) _ => rename mm into mb end.
  lazymatch goal with H : stk _ mb _ _ |- _ => rename H into STb end. lazymatch goal with H : mem_inv _ mb |- _ => rename H into MIb end.
  assert (CSTb : cstate s LBall LB L mb (Z_to_bv 64 (bv_unsigned sp + -96)) tp lo Bd).
  { eapply (cstate_seg _ _ _ _ _ m mb _ _ _ lo Bd (bv_unsigned sp - 96)); [exact CST| exact MU| exact WM| exact MIb| | lia| lia| | rewrite unsigned_lit by lia; exact STb| rewrite unsigned_lit by lia; lia].
    - constructor; [apply cwin_stack; lia| constructor].
    - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
  assert (FRb : cframe (eq ps) [] (bv_unsigned sp - 96) s LBall L m s LBall L mb).
  { eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor]. }
  eapply climpl_seq.
  { eapply CM with (n := len + 16) (lo := lo) (B := Bd); [lia| exact ROOM| lia| exact CSTb| rewrite unsigned_lit by lia; unfold CM_STACK, RMALLOC_STACK; lia| subst len; reflexivity]. }
  intros f1 L1 st1 ms1 (v1 & m1 & LBall1 & RET1 & FU1 & GR1 & CST1 & FRM1 & (pn & An & junk1 & -> & -> & -> & RNG & NEW)).
  destruct RET1 as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->).
  cret_lit. repeat (rewrite unsigned_lit in FRM1 by lia).
  pose proof FRM1 as (CFR1 & KP1 & _).
  pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 FR ltac:(lia)) as FR1.
  assert (INS1 : In (ps, S, 48) ((pn, An, len + 16) :: LBall)) by (right; exact INS).
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (ps, S, 48) CFR1 SCS INS (fun X => X) ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize]; lia)) as SCS1.
  clear FR SCS STRa.
  pose proof CST1 as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _). rewrite unsigned_lit in ST1 by lia.
  pose proof RNG as (An0 & An16 & _ & AnC & AnIMG).
  assert (An8 : An mod 8 = 0) by (clear - An16; Z.div_mod_to_equations; lia).
  assert (INA : In (pn, An, len + 16) ((pn, An, len + 16) :: LBall)) by (left; reflexivity).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _].
  assert (PNEW : forall q Aq nq, In (q, Aq, nq) LBall -> pn <> q).
  { intros q Aq nq Hin E. cbn [map blk_id fst] in ND1. inversion ND1 as [|xx ll NIx _]; subst xx ll. apply NIx. subst q. apply in_map_iff. exists (pn, Aq, nq). auto. }
  assert (APAS : An + (len + 16) <= S \/ S + 48 <= An) by (eapply (own_apart _ _ _ pn An (len + 16) ps S 48 HP1 INA INS1); exact (PNEW _ _ _ INS)).
  assert (STR1 : bytes_at usegs m1 Ls (str ++ Z_to_bv 8 0 :: slack)) by (apply ro_bytes_at; [exact MI1| lia| rewrite length_app; cbn [length]; lia| exact ROB]).
  assert (STRz : bytes_at usegs m1 Ls (str ++ [Z_to_bv 8 0])).
  { apply ro_bytes_at; [exact MI1| lia| rewrite length_app; cbn [length]; lia|].
    clear - ROB. revert ROB. generalize Ls. induction str as [|b str IH]; intros S0 H; cbn [app ro_bytes] in H |- *; [exact (conj (proj1 H) I)| exact (conj (proj1 H) (IH _ (proj2 H)))]. }
  (* [comment removed for export] *)
  change (Z.to_nat (len + 16)) with (Z.to_nat (len + 16)) in NEW.
  apply (rw_cells_split_CB usegs m1 An [] (Z.to_nat (len + 16)) junk1 [] [8; 4; Datatypes.S (length str); 3]%nat) in NEW; [| cbn [sum_nat]; lia].
  cbn [mk_CB_cells app] in NEW.
  (* [comment removed for export] *)
  change ([CB 8 (take 8 junk1); CB 4 (take 4 (drop 8 junk1)); CB (Datatypes.S (length str)) (take (Datatypes.S (length str)) (drop 4 (drop 8 junk1)));
           CB 3 (take 3 (drop (Datatypes.S (length str)) (drop 4 (drop 8 junk1))))])
    with ([CB 8 (take 8 junk1); CB 4 (take 4 (drop 8 junk1))] ++ [CB (Datatypes.S (length str)) (take (Datatypes.S (length str)) (drop 4 (drop 8 junk1)))]
          ++ [CB 3 (take 3 (drop (Datatypes.S (length str)) (drop 4 (drop 8 junk1))))]) in NEW.
  apply (proj1 (rw_cells_app usegs m1 _ _ _)) in NEW. destruct NEW as [NHD NEW]. apply (proj1 (rw_cells_app usegs m1 _ _ _)) in NEW. destruct NEW as [NBODY NTL].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in NBODY, NTL.
  replace (An + Z.of_nat 12) with (An + 12) in NBODY by lia.
  replace (An + Z.of_nat 12 + Z.pos (Pos.of_succ_nat (length str))) with (An + 12 + (len + 1)) in NTL by lia.
  pose proof (munch_refl [(An, An + (len + 16)); (S + 24, S + 32)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  (* [comment removed for export] *)
  cprefix. step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
  step. step. step. ubs_if. do 5 step. step.
  tcall (memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (str ++ [Z_to_bv 8 0])).
  all: try first [eassumption | lia | rewrite length_app; cbn [length]; lia].
  { replace (Z.to_nat (len + 1)) with (Datatypes.S (length str)) by lia. exact NBODY. }
  cbv beta delta [mkR].
  (* [comment removed for export] *)
  assert (SWR : forall z, 0 <= z < 2^31 -> bv_swrap 32 z = z).
  { intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z. rewrite Z.mod_small by lia. lia. }
  step. rewrite (t_sx32_small vi) by lia. step. rewrite (unsigned_lit vi), (SWR (vi + 1)) by lia.
  cstep.
  step. if_cases K3; zify_cond K3; rewrite ?Z_to_bv_signed, ?bv_swrap_small in K3 by (unfold bv_half_modulus, bv_modulus; cbn; lia).
  { exfalso. lia. } clear K3.
  cstep. cstep.
  step. if_cases K2; zify_cond K2; try (exfalso; rewrite ?unsigned_lit in K2 by lia; lia). clear K2.
  step. th_if_lit. step.
  step. step. step. step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mf end.
  chere. apply climpl_done. unfold pstr_seg2_post. cbn [nmz t_of pidx_off q_of sl_off cnt_of ni_after vi_after].
  exists pn, An. do 13 eexists. exists mf.
  split; [reflexivity|]. split; [exact FU1|]. split; [reflexivity|]. split; [exact GR1|].
  lazymatch goal with H : stk usegs mf _ _ |- _ => rename H into STf end. lazymatch goal with H : mem_inv usegs mf |- _ => rename H into MIf end.
  split. { eapply (cstate_seg _ _ _ _ _ m1 mf _ _ tp lo Bd (bv_unsigned sp - 96)); [exact CST1| exact MU1| exact WM1| exact MIf| | lia| lia| | rewrite unsigned_lit by lia; exact STf| rewrite unsigned_lit by lia; lia].
    - constructor; [| constructor; [| constructor]].
      + apply (cwin_block _ _ _ (pn, An, len + 16)); [exact INA| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
      + apply (cwin_block _ _ _ (ps, S, 48)); [exact INS1| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. clear - AnIMG SIMG An0 S0. lia. }
  split. { eapply cframe_seg; [eapply cframe_call; [exact FRb| exact FRM1| lia| intros a X; exact X| intros q _ _ Y; exact Y]| exact MU1| exact WM1| exact HP1| lia|].
    constructor; [| constructor; [| constructor]].
    - apply (cseg_ok_block _ _ _ _ _ (pn, An, len + 16)); [exact INA| | |]; unfold blk_addr, blk_size; cbn [fst snd]; try lia.
      destruct FRb as (_ & KPb & _). exact (cfresh_new _ _ _ _ _ _ KPb ND1).
    - apply (cseg_ok_block _ _ _ _ _ (ps, S, 48)); [exact INS1| | |]; unfold blk_addr, blk_size; cbn [fst snd]; try lia.
      intros b0 _ NT E. apply NT. unfold blk_id in *. cbn [fst] in E. rewrite E. reflexivity. }
  split; [exact RNG|]. split; [unfold pstr_frame; assumption|]. split; [unfold psd_cells; assumption|].
  lazymatch goal with H0 : rw_cells usegs mf An ?c0, H12 : rw_cells usegs mf (An + 12) ?c12 |- _ =>
    pose proof (proj2 (rw_cells_app usegs mf An c0 c12) (conj H0 H12)) as NJ end.
  cbn [app] in NJ. replace (Z.to_nat (len + 1)) with (Datatypes.S (length str)) in NJ by lia. exact NJ.
Qed.
End WithCeiling0.
