(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel BnTree BnInv BnBridge BgState BgInv BgLib BgSpecs.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem BnTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap BnUKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require Import CtxKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Ltac to_implM :=
  lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
    lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_CTX_END : Z := 0x100da4.
Definition BN_CTX_END_STACK : Z := 16.

Lemma rel_loop : forall (n : nat) (POST : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : mem) (ac : Z) (Hs : list Z) (k : nat) (off : nat) (h0 c3 : Z) (rest : list cell),
  (S n <= 16 * k + off + 1)%nat -> (off <= 15)%nat -> (k < length Hs)%nat -> (length Hs <= 3)%nat ->
  0 < ac -> ac + 72 <= alloc_ceiling ->
  (forall j H, nth_error Hs j = Some H -> 0 < H /\ H + 400 <= alloc_ceiling /\ (H + 400 <= ac \/ ac + 72 <= H) /\ H mod 8 = 0) ->
  links m0 Hs -> munch [(ac + 8, ac + 16)] m0 m -> wmono bgusegs m0 m -> mem_inv bgusegs m ->
  rw_cells bgusegs m ac (C8 (wz h0) :: C8 (wz (nth k Hs 0)) :: C8 (wz c3) :: rest) ->
  (forall m' (x13 x14 : word),
      munch [(ac + 8, ac + 16)] m0 m' -> wmono bgusegs m0 m' -> mem_inv bgusegs m' ->
      rw_cells bgusegs m' ac (C8 (wz h0) :: C8 (wz (cur_addr Hs (mkGx (gx_items (@gx_nil bptr)) (pool_release (S n) off (Some k)) 0 None [] 0 0 0 false))) :: C8 (wz c3) :: rest) ->
      evt bgusegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ac) a1 (Z_to_bv 64 0) x13 x14 a5 a6 a7
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x100e68) fc None m' (seg_rom bgusegs))) ->
  evt bgusegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ac) a1 (Z_to_bv 64 (- Z.of_nat (S n))) (Z_to_bv 64 (Z.of_nat off)) a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x100e38) fc None m (seg_rom bgusegs)).
Proof.
  induction n as [|n IH]; intros until rest; intros Hn Ho Hk HL3 AC0 ACC HR LK0 MU WM MI CX K.
  -
    step. if_cases K0; zify_cond K0.
    +
      assert (off = 0%nat) as -> by (rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
      destruct (nth_error Hs k) as [Hk0|] eqn:EHk; [|apply nth_error_None in EHk; lia].
      pose proof (HR k Hk0 EHk) as (HK0 & HKC & HKS & HK8). rewrite (nth_error_nth _ _ _ EHk) in CX.
      assert (LNK : rw_cells bgusegs m (Hk0 + 384) [C8 (wz (match k with O => 0 | S k' => nth k' Hs 0 end)); C8 (wz (nth (S k) Hs 0))]).
      { eapply links_transport; [exact LK0| exact MU| exact WM| | exact EHk]. intros j H Hj. cbn [disjoint_from]. destruct (HR j H Hj) as (_ & _ & [?|?] & _); lia. }
      unfold MallocRep.wz in *.
      step.
      chk ltac:(fun C => rewrite land64_small in C by (clear - HK0 HKC; lia); clear - C HK0; lia).
      step. rewrite (land7_wrap _ HK8).
      chk ltac:(fun C => clear - C; lia).
      step. step. step.
      step. rewrite (swrap32_wrap64 (- Z.of_nat 1) 1) by lia. replace (- Z.of_nat 1 + 1) with 0 by lia.
      step. if_false.
      eapply K; [exact MU| exact WM| exact MI|].
      cbn [pool_release Nat.eqb item_prev]. destruct k as [|k']; cbn [cur_addr gx_current]; exact CX.
    + step. step. step.
      rewrite (swrap32_wrap64 (- Z.of_nat 1) 1) by lia. rewrite (swrap32_wrap64 (Z.of_nat off) (-1)) by lia. replace (- Z.of_nat 1 + 1) with 0 by lia.
      step. if_false.
      eapply K; [exact MU| exact WM| exact MI|].
      cbn [pool_release]. replace (off =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; rewrite ?unsigned_lit in K0 by lia; lia).
      cbn [pool_release cur_addr gx_current]. exact CX.
  - step. if_cases K0; zify_cond K0.
    +
      assert (off = 0%nat) as -> by (rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
      destruct k as [|k']; [lia|].
      destruct (nth_error Hs (S k')) as [Hk0|] eqn:EHk; [|apply nth_error_None in EHk; lia].
      pose proof (HR (S k') Hk0 EHk) as (HK0 & HKC & HKS & HK8). rewrite (nth_error_nth _ _ _ EHk) in CX.
      assert (LNK : rw_cells bgusegs m (Hk0 + 384) [C8 (wz (nth k' Hs 0)); C8 (wz (nth (S (S k')) Hs 0))]).
      { eapply links_transport; [exact LK0| exact MU| exact WM| | exact EHk]. intros j H Hj. cbn [disjoint_from]. destruct (HR j H Hj) as (_ & _ & [?|?] & _); lia. }
      unfold MallocRep.wz in *.
      step.
      chk ltac:(fun C => rewrite land64_small in C by (clear - HK0 HKC; lia); clear - C HK0; lia).
      step. rewrite (land7_wrap _ HK8).
      chk ltac:(fun C => clear - C; lia).
      step. step. step. step.
      rewrite (swrap32_wrap64 (- Z.of_nat (S (S n))) 1) by lia.
      step. if_cases K1; zify_cond K1.
      2:{ exfalso. clear - K1 Hn Hk HL3 Ho. change 18446744073709551615 with (Z.ones 64) in K1. rewrite Z.land_ones in K1 by lia.
          change (2 ^ 64) with 18446744073709551616 in K1. Z.div_mod_to_equations. lia. }
      replace (- Z.of_nat (S (S n)) + 1) with (- Z.of_nat (S n)) by lia.
      eapply (IH POST ra sp gp tp t0 t1 t2 s0 s1 a1 _ a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 _ ac Hs k' 15%nat h0 c3 rest);
        [lia| lia| lia| exact HL3| exact AC0| exact ACC| exact HR| exact LK0| exact MU| exact WM| exact MI| exact CX|].
      intros m' x13 x14 MU' WM' MI' CX'. eapply K; [exact MU'| exact WM'| exact MI'|].
      cbn [pool_release Nat.eqb item_prev] in CX' |- *. exact CX'.
    + step. step. step.
      rewrite (swrap32_wrap64 (- Z.of_nat (S (S n))) 1) by lia. rewrite (swrap32_wrap64 (Z.of_nat off) (-1)) by lia.
      step. if_cases K1; zify_cond K1.
      2:{ exfalso. clear - K1 Hn Hk HL3 Ho. change 18446744073709551615 with (Z.ones 64) in K1. rewrite Z.land_ones in K1 by lia.
          change (2 ^ 64) with 18446744073709551616 in K1. Z.div_mod_to_equations. lia. }
      replace (- Z.of_nat (S (S n)) + 1) with (- Z.of_nat (S n)) by lia.
      replace (Z.of_nat off + -1) with (Z.of_nat (off - 1)) by (rewrite ?unsigned_lit in K0 by lia; lia).
      eapply (IH POST ra sp gp tp t0 t1 t2 s0 s1 a1 _ a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m ac Hs k (off - 1)%nat h0 c3 rest);
        [rewrite ?unsigned_lit in K0 by lia; lia| lia| exact Hk| exact HL3| exact AC0| exact ACC| exact HR| exact LK0| exact MU| exact WM| exact MI| exact CX|].
      intros m' x13 x14 MU' WM' MI' CX'. eapply K; [exact MU'| exact WM'| exact MI'|].
      cbn [pool_release] in CX' |- *. replace (off =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; rewrite ?unsigned_lit in K0 by lia; lia). exact CX'.
Qed.

Lemma BN_CTX_end_walk : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BnRep.err_addrs)
    (lo B : Z) (errv : word) (ac : Z) (qc : bptr),
  bn_pre s bs m OW LB PL EA sp lo B errv BN_CTX_END_STACK -> tp = wz RATP -> pl_ctx PL = Some (ac, qc) -> a0 = wz ac ->
  implM bgusegs (interp (embed (BN_CTX_end (tree_ops bptr) bs))) s
    (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ OW' PL' _ => PL' = PL /\ OW' = OW))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz BN_CTX_END) fc None m (seg_rom bgusegs)).
Proof.
  intros until qc. intros (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI) -> EC ->.
  unfold BN_CTX_END_STACK, BN_CTX_END, GLOBALS_TOP, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
  pose proof WFS as (EL & BOK & EONE & (CE1 & CE2 & CE3 & CE4 & CE5 & CE6 & CE7 & CE8)).
  destruct (lib_state_cx_open [] bs m OW PL EA LS) as (Hs & IX & CV & LSC).
  apply (cx_view_some _ _ _ _ _ _ _ _ EC) in CV. destruct CV as (BC & LHs & CX & STK & HItems & HLinks). change BN_CTX_SZ with 72 in BC.
  pose proof (RH_range _ _ _ _ _ _ _ HEAP BC) as (CA0 & CA16 & _ & CAC & CAI).
  set (c := st_ctx bs) in *.
  unfold ctx_cells in CX. rewrite CE1, CE2, CE3 in CX. change (Z.of_nat 0) with 0 in CX. change (Z.b2z false) with 0 in CX.
  unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
  unfold BN_CTX_end, bbind, bgetctx, bret, bunr, bsetctx.
  cbn [bind ret unreachable lib_malloc lib_free tree_ops tbind fst snd]. fold c.
  rewrite CE1. cbn [Nat.eqb negb].
  destruct (rev (gx_frames c)) as [|fp rest] eqn:EREV.
  { cbn [embed interp]. apply implM_interp_unr. }
  unfold implM. iprefix.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (ac, ac + 72)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
  assert (CA8 : ac mod 8 = 0) by (clear - CA16; Z.div_mod_to_equations; lia).
  carve_frame 16%nat ST. do 4 step.
  step. if_cases KN; zify_cond KN; [exfalso; rewrite ?unsigned_lit in KN by lia; lia|]. clear KN.
  step. rewrite (land7_wrap _ CA8).
  chk ltac:(fun C => clear - C; lia).
  step. unfold MallocRep.wz at 1. rewrite (sx32_small 0) by lia.
  step. if_true.
  assert (EFR : gx_frames c = rev rest ++ [fp]).
  { rewrite <- (rev_involutive (gx_frames c)), EREV. reflexivity. }
  assert (DEPp : length (gx_frames c) = S (length rest)) by (rewrite EFR, length_app, length_rev; cbn; lia).
  assert (SSZ : gx_ssize c = 0%nat \/ gx_ssize c = 32%nat) by (unfold BG_DEPTH in CE8; lia).
  assert (DEP : (length (gx_frames c) <= 32)%nat) by (unfold BG_DEPTH in CE8; destruct CE8 as [(_ & E0 & _)|(_ & _ & ?)]; [rewrite E0; cbn|]; lia).
  assert (U48 : (gx_used c <= 48)%nat) by (unfold BN_CTX_POOL_SIZE in CE4; lia).
  assert (FPU : (fp <= gx_used c)%nat).
  { rewrite EFR in CE7. rewrite <- app_assoc in CE7. cbn [app] in CE7. eapply nondecr_last_two; exact CE7. }
  step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (length (gx_frames c)))) by lia.
  step.
  step. replace (Z.of_nat (length (gx_frames c)) + -1) with (Z.of_nat (length rest)) by lia.
  do 3 step.
  rewrite (unsigned_lit (Z.of_nat (length rest))) by lia. rewrite shl32_shr30 by lia.
  step.

  unfold stack_rep in STK. destruct (gx_indexes c) as [q|] eqn:EI; [|exfalso; destruct STK as (_ & _ & E2); rewrite E2 in DEPp; cbn in DEPp; lia].
  destruct STK as (HinI & SZ32 & stale & LEN & ARR). change FRAMES_SZ with 128 in HinI. unfold BN_CTX_START_FRAMES in SZ32, LEN.
  pose proof (RH_range _ _ _ _ _ _ _ HEAP HinI) as (IA0 & IA16 & _ & IAC & IAI).
  assert (NEI : qc <> q) by (eapply ids_pl_m; [exact IDS| eapply in_pl_ids_ctx; exact EC| apply idx_in_m; exact EI]).
  pose proof (RH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP BC HinI NEI) as CXI.
  remember (map (fun k : nat => wz (Z.of_nat k)) (gx_frames c) ++ stale) as ws eqn:Ews.
  assert (LWS : length ws = 32%nat) by (subst ws; rewrite length_app, length_map; exact LEN).
  assert (NTH : nth_error ws (Z.to_nat (Z.of_nat (length rest))) = Some (wz (Z.of_nat fp))).
  { rewrite Nat2Z.id, Ews, EFR, map_app. cbn [map]. rewrite <- app_assoc. cbn [app].
    rewrite nth_error_app2 by (rewrite length_map, length_rev; lia). rewrite length_map, length_rev, Nat.sub_diag. reflexivity. }
  chkw ltac:(fun C => clear - C IA0 IAC DEPp LEN; lia).
  step. rewrite (snez_pos_wz IX) by (clear - IA0 IAC; lia).
  step. rewrite (seqz_pos (IX + 4 * Z.of_nat (length rest))) by (clear - IA0 IAC DEPp LEN; lia).
  step.
  chk ltac:(fun C => clear - C; lia).
  chkw ltac:(fun C => clear - C IA0 IAC; lia).
  step. rewrite (land3_wrap (IX + 4 * Z.of_nat (length rest))) by (clear - IA16; Z.div_mod_to_equations; lia).
  chk ltac:(fun C => clear - C; lia).
  pose proof ARR as ARR0.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch type of MU with munch ?W0 _ _ =>
      apply (u32arr_transport bgusegs W0 m mx IX ws) in ARR; [| exact MU| exact WM| cbn [disjoint_from]; rewrite LWS; lia] end end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    let a := cur_mem_addr in
    pose proof (u32arr_read bgusegs mx IX ws (Z.of_nat (length rest)) (wz (Z.of_nat fp)) a ARR NTH ltac:(lia) ltac:(addr_tac)) as RD end.
  step. clear RD. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat fp)) by lia.
  step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (gx_used c))) by lia.
  set (num := (gx_used c - fp)%nat).
  set (pu' := if (fp <? gx_used c)%nat then (gx_pused c - num)%nat else gx_pused c).
  set (cur' := if (fp <? gx_used c)%nat then pool_release num ((gx_pused c - 1) mod BN_CTX_POOL_SIZE) (gx_current c) else gx_current c).
  set (c' := mkGx (gx_items c) cur' pu' (Some q) (rev rest) (gx_ssize c) fp 0%nat false).

  assert (HR : forall j H, nth_error Hs j = Some H -> 0 < H /\ H + 400 <= alloc_ceiling /\ (H + 400 <= ac \/ ac + 72 <= H) /\ H mod 8 = 0).
  { intros j H Hj. assert (Hj' : (j < length (gx_items c))%nat) by (rewrite <- LHs; apply nth_error_Some; congruence).
    destruct (nth_error (gx_items c) j) as [qj|] eqn:Eqj; [|apply nth_error_None in Eqj; lia].
    pose proof (HItems j qj Eqj) as Hin. rewrite (nth_error_nth _ _ _ Hj) in Hin. change ITEM_SZ with 400 in Hin.
    pose proof (RH_range _ _ _ _ _ _ _ HEAP Hin) as (B0 & B16 & _ & BCj & _). split; [exact B0|]. split; [exact BCj|].
    assert (NE : qc <> qj) by (eapply ids_pl_m; [exact IDS| eapply in_pl_ids_ctx; exact EC| apply item_in_m; eapply nth_error_In; exact Eqj]).
    pose proof (RH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP BC Hin NE). split; [lia|]. clear - B16. Z.div_mod_to_equations. lia. }
  lazymatch goal with |- evt _ ?Q (MS _ _ _ _ _ ?mx _) => rename mx into m1;
    assert (FIN : forall (x12 x13 x14 : word) (mX : mem),
      rw_cells bgusegs mX ac
        [C8 (wz (hd 0 Hs)); C8 (wz (cur_addr Hs c')); C8 (wz (last Hs 0)); C4 (wz (Z.of_nat pu')); C4 (wz (Z.of_nat (BN_CTX_POOL_SIZE * length (gx_items c)))); C8 (wz IX);
         C4 (wz (Z.of_nat (length rest))); C4 (wz (Z.of_nat (gx_ssize c))); C4 (wz (Z.of_nat (gx_used c)));
         C4 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0)] ->
      rw_cells bgusegs mX (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
      stk bgusegs mX lo (bv_unsigned sp + -16) ->
      munch [(bv_unsigned sp + -16, bv_unsigned sp); (ac, ac + 72)]%Z m mX -> wmono bgusegs m mX -> mem_inv bgusegs mX ->
      rw_cells bgusegs mX 3346164 [C4 errv] ->
      evt bgusegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 RATP) t0 t1 t2 sp s1 (Z_to_bv 64 ac)
                           (Z_to_bv 64 (Z.of_nat fp)) x12 x13 x14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 1052264) fc None mX (seg_rom bgusegs))) end.
  { intros x12 x13 x14 mX CXX FRX STX MUX WMX MIX ERRX.
    clear MU WM MI ERR ST FR CX ARR.
    unfold MallocRep.wz in *.
    step. step. step. step. step. release_frame FRX STX (bv_unsigned sp). step.
    ihere. to_implM. cbn [embed interp]. apply implM_ret. apply evt_done.
    lazymatch goal with |- bn_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
    fold num. fold pu'. fold cur'. fold c'.
    assert (HWL : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp + -16, bv_unsigned sp); (ac, ac + 72)]).
    { constructor; [left; cbn; lia|]. constructor; [right; left; exists (qc, ac, 72); cbn; auto with zarith| constructor]. }
    assert (LKF : links mF Hs).
    { eapply (links_keep s OW LB m mF bs PL EA ac qc Hs); [exact HEAP| exact PARTS| exact EC| exact LHs| exact HItems| exact HLinks| exact MUX| exact WMX|].
      constructor; [left; cbn; lia|]. constructor; [right; left; cbn; unfold BN_CTX_SZ; lia| constructor]. }
    assert (LSF : lib_state (set_ctx c' bs) mF OW PL EA).
    { unfold lib_state. eapply (lib_state_cx_close [] bs (set_ctx c' bs) mF OW PL EA Hs IX); [| exact ND| reflexivity| reflexivity| reflexivity| reflexivity| | |].
      - eapply (lib_state_frame s LB (bv_unsigned sp) B); [exact HEAP| exact LSC| exact MUX| exact WMX| exact FROK|].
        constructor; [apply w_stack; cbn; lia|].
        constructor; [apply w_cx; [reflexivity| intros x Hx; left; exists ac, qc; cbn in Hx; unfold BN_CTX_SZ; auto with zarith]| constructor].
      - apply st_wf_set_ctx; [exact WFS| reflexivity|].

        unfold ctx_wf, c'. cbn [gx_items gx_current gx_pused gx_indexes gx_frames gx_ssize gx_used gx_err_stack gx_too_many].
        split; [reflexivity|]. split; [reflexivity|].
        split. { subst pu' num. rewrite CE3. destruct (Nat.ltb_spec fp (gx_used c)); lia. }
        split; [lia|]. split; [exact CE5|].
        split. { subst cur' pu' num. destruct (Nat.ltb_spec fp (gx_used c)) as [Hlt|Hge].
                 - rewrite CE6, CE3. destruct (Nat.eqb_spec (gx_used c) 0) as [|Hu0]; [lia|].
                   unfold BN_CTX_POOL_SIZE. rewrite pool_release_spec by lia. replace (gx_used c - (gx_used c - fp))%nat with fp by lia. reflexivity.
                 - assert (fp = gx_used c) as -> by lia. exact CE6. }
        split. { rewrite EFR in CE7. rewrite <- app_assoc in CE7. cbn [app] in CE7. eapply nondecr_drop_last. exact CE7. }
        destruct CE8 as [(S1 & S2 & S3)|(S1 & S2 & S3)]; [rewrite EFR in S2; destruct (rev rest); discriminate|].
        right. split; [exact S1|]. split; [discriminate|]. rewrite EFR, length_app in S3. cbn [length] in S3. lia.
      - apply ids_ok_set_ctx_same; [exact IDS| reflexivity| cbn [gx_indexes]; symmetry; exact EI].
      - apply (cx_view_some _ _ _ _ _ _ _ _ EC). cbn [st_ctx set_ctx]. split; [exact BC|]. split; [exact LHs|]. split; [|split; [|split; [apply item_blocks_set_ctx; [reflexivity| exact HItems]| exact LKF]]].
        + unfold ctx_cells. subst c'. cbn [gx_items gx_current gx_pused gx_indexes gx_frames gx_ssize gx_used gx_err_stack gx_too_many Z.b2z].
          rewrite length_rev. exact CXX.
        + unfold stack_rep. subst c'. cbn [gx_indexes gx_ssize gx_frames]. split; [exact HinI|]. split; [exact SZ32|].
          exists (wz (Z.of_nat fp) :: stale). split; [rewrite length_rev; cbn [length]; rewrite DEPp in LEN; unfold BN_CTX_START_FRAMES; lia|].
          lazymatch type of MUX with munch ?W0 _ _ =>
            apply (u32arr_transport bgusegs W0 m mF IX ws) in ARR0; [| exact MUX| exact WMX| cbn [disjoint_from]; rewrite LWS; lia] end.
          rewrite Ews, EFR, map_app in ARR0. cbn [map] in ARR0. rewrite <- app_assoc in ARR0. cbn [app] in ARR0. exact ARR0. }
    unfold bn_post. do 15 eexists. exists mF, OW, PL, errv. split; [reflexivity|]. cbn [fst snd].
    split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MUX WMX HWL CEIL)|]. split; [exact LSF|].
    split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MUX WMX HWL SPB ltac:(lia)); unfold GLOBALS_TOP; lia|]. split; [exact STX|].
    split; [unfold LX_ERRNO, RATP; exact ERRX|]. split; [exact MIX|].
    split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MUX WMX HWL CEIL); unfold GLOBALS_TOP; lia|].
    split; [reflexivity|]. split; [reflexivity|].
    split; [apply refs_stable_ow; [reflexivity| auto]|]. split; reflexivity. }
  step. if_cases KR; zify_cond KR; rewrite ?unsigned_lit in KR by lia.
  -
    assert (ELT : (fp <? gx_used c)%nat = false) by (apply Nat.ltb_ge; lia).
    eapply FIN; [| exact FR| exact ST| exact MU| exact WM| exact MI| exact ERR].
    subst c' pu' cur'. rewrite ELT. unfold cur_addr. cbn [gx_current]. rewrite CE3. unfold cur_addr in CX. exact CX.
  -
    assert (ELT : (fp <? gx_used c)%nat = true) by (apply Nat.ltb_lt; lia).
    assert (PU1 : (1 <= gx_used c)%nat) by lia.
    step. unfold MallocRep.wz at 1. rewrite (sx32_small (Z.of_nat (gx_used c))) by lia.
    step. step. step.
    rewrite !(unsigned_lit (Z.of_nat fp)), !(unsigned_lit (Z.of_nat (gx_used c))) by lia.
    rewrite !(bk_swrap32_small (Z.of_nat fp - Z.of_nat (gx_used c))) by lia.
    replace (Z.of_nat (gx_used c) + (Z.of_nat fp - Z.of_nat (gx_used c))) with (Z.of_nat pu') by (subst pu' num; rewrite ELT, CE3; lia).
    step. step.
    rewrite (unsigned_lit (Z.of_nat (gx_used c) + -1)) by lia.
    replace (Z.land (Z.of_nat (gx_used c) + -1) 15) with (Z.of_nat ((gx_used c - 1) mod 16)).
    2:{ change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2 ^ 4) with 16. rewrite Nat2Z.inj_mod. f_equal. lia. }
    replace (Z.of_nat fp - Z.of_nat (gx_used c)) with (- Z.of_nat (S (gx_used c - fp - 1))) by lia.

    pose proof CE6 as ECUR. fold c in ECUR. replace (gx_used c =? 0)%nat with false in ECUR by (symmetry; apply Nat.eqb_neq; lia).
    pose proof (Nat.div_mod_eq (gx_used c - 1) 16) as DM. pose proof (Nat.mod_upper_bound (gx_used c - 1) 16 ltac:(lia)) as MB.
    assert (KLT : ((gx_used c - 1) / 16 < length Hs)%nat) by (rewrite LHs; unfold BN_CTX_POOL_SIZE in CE4; lia).
    unfold cur_addr in CX. rewrite ECUR in CX. unfold BN_CTX_POOL_SIZE, MallocRep.wz in CX.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    eapply (rel_loop (gx_used c - fp - 1) _ ra _ gp _ t0 t1 t2 sp s1 (Z_to_bv 64 (Z.of_nat fp)) _ a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
              m2 m2 ac Hs ((gx_used c - 1) / 16)%nat ((gx_used c - 1) mod 16)%nat);
      [lia| lia| exact KLT| rewrite LHs; exact CE5| lia| lia| exact HR| | apply munch_refl| apply wmono_refl| exact MI| exact CX|].
    { eapply links_keep; [exact HEAP| exact PARTS| exact EC| exact LHs| exact HItems| exact HLinks| exact MU| exact WM|].
      constructor; [left; cbn; lia|]. constructor; [right; left; cbn; unfold BN_CTX_SZ; lia| constructor]. }
    intros m' x13 x14 MU' WM' MI' CX'.
    eapply FIN; [| | | | | exact MI'|].
    + subst c' cur' num. rewrite ELT. unfold cur_addr. cbn [gx_current]. rewrite ECUR, CE3. unfold BN_CTX_POOL_SIZE.
      replace (gx_used c - fp)%nat with (S (gx_used c - fp - 1)) by lia. unfold cur_addr, MallocRep.wz in CX'. cbn [gx_current] in CX'. exact CX'.
    + eapply rw_cells_transport; [exact FR| exact MU'| exact WM'| cbn [disjoint_from cells_size csize Nat.add]; lia].
    + eapply stk_transport_disjoint; [exact ST| exact MU'| exact WM'| cbn [disjoint_from]; lia].
    + eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. intros x Hx. cbn [outside] in *. lia.
    + eapply wmono_trans; [exact WM| exact WM'].
    + eapply rw_cells_transport; [exact ERR| exact MU'| exact WM'| cbn [disjoint_from cells_size csize Nat.add]; lia].
Qed.

End WithCeiling0.
