(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel AtpModel OdModel Target Prog AtpImpl.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit Sj_h_dtor Atp_defs Atp_kitu Atp_h_defs.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Sj_stage1_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition exit_inv (sp0 : Z) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra : word)
    (m0 : mem) (s00 : PState) (LB : list block) (lo B D : Z) (d : list Z)
    (bv : bptr) (A cap n : Z) (els : list (Z * Z)) (psb pim pix poc pia : bptr) (SB nsb : Z) (LBX : list block) (m2 : mem) (st2 : PState) : Prop :=
  exists (IMPL IDX OC IA nix : Z) (errv2 : word) (jr j0 j304 jfd : list byte) (w320 w328 w336 w344 : word)
         (nsi nxt capv md bufv lenv docv : word) (b48 b49 : byte) (p12 p28 p50 : list byte),
    RHEAP st2 ((pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, nix) :: (pim, IMPL, 96) :: (psb, SB, nsb) :: LBX ++ (bv, A, 16 * cap) :: LB) m2
    /\ rauxv_ok m2 B /\ mem_inv usegs m2 /\ stk usegs m2 lo sp0 /\ rw_cells usegs m2 LX_ERRNO [C4 errv2]
    /\ ps_fa st2 = ps_fa s00 /\ ps_so st2 = ps_so s00
    /\ lx_pres LB (sp0 + 496) [LXW_SJ] m0 m2 /\ sj_statics m2 true /\ payload_ok m2 LB D d
    /\ vrep m2 (sp0 + 344) A (cap, n, Some bv) els jr
    /\ rw_cells usegs m2 sp0 [CB 288 j0]
    /\ rw_cells usegs m2 (sp0 + 288) [CB 8 j304; C8 (Z_to_bv 64 IMPL); C8 w320; C8 w328; C8 w336; C8 w344; C8 (Z_to_bv 64 SB)]
    /\ rw_cells usegs m2 IMPL (impl_cells16 (Z_to_bv 64 SJ_DPI_VPTR) nsi p12 (Z_to_bv 64 IDX) nxt p28 capv md b48 b49 p50 (Z_to_bv 64 OC) (Z_to_bv 64 IA) bufv lenv docv)
    /\ rw_cells usegs m2 (sp0 + 368) [CB 24 jfd]
    /\ rw_cells usegs m2 (sp0 + 392) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Ltac readdr H e := lazymatch type of H with rw_cells _ _ ?a _ => replace a with e in H by lia end.

Lemma rw_cells_split_at1 : forall m A cs n, rw_cells usegs m A cs ->
  rw_cells usegs m A (firstn n cs) /\ rw_cells usegs m (A + Z.of_nat (cells_size (firstn n cs))) (skipn n cs).
Proof. intros m A cs n H. rewrite <- (firstn_skipn n cs) in H. apply Sj_stage1_kit.rw_cells_app in H. exact H. Qed.

Lemma exit_inv_munch : forall (sp0 : Z) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra : word)
    (m0 : mem) (s00 : PState) (LB : list block) (lo B D : Z) (d : list Z)
    (bv : bptr) (A cap n : Z) (els : list (Z * Z)) (psb pim pix poc pia : bptr) (SB nsb : Z) (LBX : list block) (m3 m1 : mem) (st3 : PState) (j : list byte),
  RHEAP s00 LB m0 -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= sp0 -> sp0 + 496 <= B ->
  exit_inv sp0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra m0 s00 LB lo B D d bv A cap n els psb pim pix poc pia SB nsb LBX m3 st3 ->
  munch [(lo, sp0 + 288); (SB, SB + nsb)]%Z m3 m1 -> wmono usegs m3 m1 ->
  mem_inv usegs m1 -> stk usegs m1 lo sp0 -> rw_cells usegs m1 sp0 [CB 288 j] ->
  exit_inv sp0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra m0 s00 LB lo B D d bv A cap n els psb pim pix poc pia SB nsb LBX m1 st3.
Proof.
  intros until j. intros HEAP00 CEIL GLO LOSP QB XI MU WM MI1 ST1 LOW1.
  unfold GLOBALS_TOP in *.
  pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
  destruct XI as (IMPL & IDX & OC & IA & nix & errv2 & jr & j0 & j304 & jfd & w320 & w328 & w336 & w344
                  & nsi & nxt & capv & md & bufv & lenv & docv & b48 & b49 & p12 & p28 & p50
                  & HEAP2 & AUX2 & MI2 & ST2 & ERR2 & FA2 & SO2 & PRES2 & SJS2 & PL2 & VR2 & LOW & PA & THIS & XFD & SAVE).
  assert (ELX : LX_ERRNO = 609404) by reflexivity. rewrite ELX in ERR2.
  pose proof (LH_block_range _ _ _ _ HEAP2 ltac:(do 3 right; left; reflexivity)) as (IM0 & _ & _ & IMC & IMS).
  pose proof (LH_block_range _ _ _ _ HEAP2 ltac:(do 4 right; left; reflexivity)) as (SB0 & _ & SBN & SBC & SBS).
  pose proof (LH_block_range _ _ _ _ HEAP2 ltac:(do 5 right; apply in_or_app; right; left; reflexivity)) as (A0 & _ & _ & AC & AS).
  cbn [blk_addr blk_size fst snd] in IM0, IMC, IMS, SB0, SBN, SBC, SBS, A0, AC, AS. unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in IMC, SBC, AC.
  pose proof (RHEAP_pull _ [(pia, IA, 1024); (poc, OC, 8192); (pix, IDX, nix); (pim, IMPL, 96)] _ _ _ HEAP2) as HEAPSB. cbn [app] in HEAPSB.
  assert (SEPSB : forall a, in_block ((pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, nix) :: (pim, IMPL, 96) :: LBX ++ (bv, A, 16 * cap) :: LB) a -> ~ (SB <= a < SB + nsb))
    by (intros a IB; exact (LH_head_disj _ _ _ _ _ _ HEAPSB a IB)).
  assert (BLB : forall a, in_block LB a -> a < alloc_ceiling /\ ~ (SB <= a < SB + nsb)).
  { intros a (b & Hb & Hr). split.
    - pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & _). unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in BC. lia.
    - apply SEPSB. exists b. split; [do 4 right; apply in_or_app; right; right; exact Hb| exact Hr]. }
  pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
  assert (STKO : forall a, sp0 + 288 <= a -> SB + nsb <= a -> outside [(lo, sp0 + 288); (SB, SB + nsb)] a) by (intros a H1 H2; cbn [outside]; lia).
  destruct VR2 as (ELS & SZ & SV & BLK).
  exists IMPL, IDX, OC, IA, nix, errv2, jr, j, j304, jfd, w320, w328, w336, w344, nsi, nxt, capv, md, bufv, lenv, docv, b48, b49, p12, p28, p50.
  split. { eapply LH_frame; [exact HEAP2| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia|]. constructor; [| constructor].
           eapply (W_ok_block _ (psb, SB, nsb)); [do 4 right; left; reflexivity| cbn; lia| cbn; lia]. }
  split. { eapply rauxv_ok_frame; [exact AUX2| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
  split; [exact MI1|]. split; [exact ST1|].
  split. { rewrite ELX. eapply rw_cells_agree; [exact AG| exact ERR2|]. intros a Ha. cbn in Ha. cbn [outside]. lia. }
  split; [exact FA2|]. split; [exact SO2|].
  split. { eapply lx_pres_trans; [exact PRES2|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
           intros a Ha [HX HC]. cbn [outside]. destruct HC as [HC|[HC|HC]]; [lia| destruct (BLB a HC); lia| lia]. }
  split. { eapply sj_statics_agree; [exact AG| | exact SJS2]. intros a Ha. unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. cbn [outside]. lia. }
  split. { eapply payload_ok_agree; [exact AG| exact PL2|]. intros b a Hb Ha. destruct (BLB a ltac:(exists b; split; assumption)). cbn [outside]. lia. }
  split. { split; [exact ELS|]. split; [exact SZ|]. split.
           - eapply rw_cells_agree; [exact AG| exact SV|]. intros a Ha. cbn in Ha. apply STKO; lia.
           - eapply vblk_agree; [exact AG| | exact ELS| lia| exact BLK]. intros a _ Ha.
             assert (NSB : ~ (SB <= a < SB + nsb)) by (apply SEPSB; exists (bv, A, 16 * cap); split; [do 4 right; apply in_or_app; right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]).
             cbn [outside]. lia. }
  split; [exact LOW1|].
  split. { eapply rw_cells_agree; [exact AG| exact PA|]. intros a Ha. cbn in Ha. apply STKO; lia. }
  split. { eapply rw_cells_agree; [exact AG| exact THIS|]. intros a Ha. unfold impl_cells16 in Ha. cbn in Ha.
           assert (NSB : ~ (SB <= a < SB + nsb)) by (apply SEPSB; exists (pim, IMPL, 96); split; [do 3 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]).
           cbn [outside]. lia. }
  split. { eapply rw_cells_agree; [exact AG| exact XFD|]. intros a Ha. cbn in Ha. apply STKO; lia. }
  eapply rw_cells_agree; [exact AG| exact SAVE|]. intros a Ha. cbn in Ha. apply STKO; lia.
Qed.

Lemma vdtor_loop : forall Q (x1 sp gp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (A : Z) (k : nat),
  16 <= A -> A + 16 * Z.of_nat k < 2^63 -> (1 <= k)%nat ->
  evt usegs Q (MS (mkR x1 sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 A) a2 (Z_to_bv 64 16) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x2a07c) fc None m (seg_rom usegs)) ->
  evt usegs Q (MS (mkR x1 sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 (A + 16 * Z.of_nat k)) a2 (Z_to_bv 64 16) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x2a06c) fc None m (seg_rom usegs)).
Proof.
  intros until k. intros A16 AK K1 HK.
  revert AK K1. induction k as [|k IH]; intros AK K1; [lia|].
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.

  step. if_lia. step. if_lia. zstep.
  replace (A + 16 * Z.of_nat (S k) + -16) with (A + 16 * Z.of_nat k) by lia.
  step. if_cases K; zify_cond K.
  -
    apply IH; lia.
  -
    eapply evt_eq; [| exact HK]. atp_st_eq.
Qed.

Section Proofs.
  Hypothesis HF : rfree_stmt.

  Lemma od_exit_tail : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
      (m0 : mem) (s00 : PState) (LB : list block) (D : Z) (d : list Z) (lo B : Z) (canary : word)
      (bv : bptr) (A cap n : Z) (els : list (Z * Z)) (psb pim pix poc pia : bptr) (SB nsb : Z) (m2 : mem) (st2 : PState),
    RHEAP s00 LB m0 -> lx_statics m0 -> stderr_wfile m0 -> ssp_cells m0 canary ->
    bv_unsigned sp <= B -> B < 2^63 -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - LX_FUZZ_STACK ->
    tp = wz RATP -> bv_unsigned sp mod 16 = 0 -> cap < 2^26 -> frm0 fc1 ->
    exit_inv (bv_unsigned sp - 496) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra m0 s00 LB lo B D d bv A cap n els psb pim pix poc pia SB nsb [] m2 st2 ->
    implM usegs (mbind (del lops psb) (fun _ => mbind (del lops pia) (fun _ => mbind (del lops poc) (fun _ =>
                 mbind (del lops pix) (fun _ => mbind (del lops pim) (fun _ => mbind (vfree lops (cap, n, Some bv)) (fun _ => mret 0)))))))
          st2
          (rfuzz_one_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s00 LB D d lo B canary m0)
          (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp - 496)) gp tp xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
              F1 (Z_to_bv 64 0x273d8) fc1 None m2 (seg_rom usegs)).
  Proof.
    intros until st2. intros HEAP00 LXS0 SEW0 SSP0 SPB B63 CEIL GLO LO TP AL16 CAPB FRM1 XI.
    unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP in *. unfold MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (ESP : sp = Z_to_bv 64 (bv_unsigned sp)) by (symmetry; apply Z_to_bv_bv_unsigned).
    remember (bv_unsigned sp) as usp eqn:Eusp.
    remember (usp - 496) as sp0 eqn:Esp0.
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    subst tp.
    destruct XI as (IMPL & IDX & OC & IA & nix & errv2 & jr & j0 & j304 & jfd & w320 & w328 & w336 & w344
                    & nsi & nxt & capv & md & bufv & lenv & docv & b48 & b49 & p12 & p28 & p50
                    & HEAP2 & AUX2 & MI2 & ST2 & ERR2 & FA2 & SO2 & PRES2 & SJS2 & PL2 & VR2 & LOW & PA & THIS & XFD & SAVE).
    cbn [app] in HEAP2.
    assert (LO0 : 0 <= lo) by (destruct ST2 as [? _]; assumption).
    assert (ELX : LX_ERRNO = 609404) by reflexivity. rewrite ELX in ERR2.
    assert (BLB : forall a, in_block LB a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & _). unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in BC. lia. }
    pose proof (LH_block_range _ _ _ _ HEAP2 ltac:(do 3 right; left; reflexivity)) as (IM0 & IM16 & _ & IMC & IMS).
    pose proof (LH_block_range _ _ _ _ HEAP2 ltac:(do 4 right; left; reflexivity)) as (SB0 & _ & SBN & SBC & SBS).
    pose proof (LH_block_range _ _ _ _ HEAP2 ltac:(do 5 right; left; reflexivity)) as (A0 & A16 & _ & AC & AS).
    cbn [blk_addr blk_size fst snd] in IM0, IM16, IMC, IMS, SB0, SBN, SBC, SBS, A0, A16, AC, AS. unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in IMC, SBC, AC.
    assert (IM8 : IMPL mod 8 = 0) by (clear - IM16; pose proof (Z.mod_divide IMPL 16 ltac:(lia)) as [H _]; destruct (H IM16) as [q ->]; replace (q * 16) with (2 * q * 8) by lia; apply Z.mod_mul; lia).
    assert (SP8 : (sp0 + 344) mod 8 = 0).
    { clear - AL16 Esp0. pose proof (Z.mod_divide usp 16 ltac:(lia)) as [H _]. destruct (H AL16) as [q Hq]. replace (sp0 + 344) with ((2 * q - 19) * 8) by lia. apply Z.mod_mul. lia. }
    destruct VR2 as (ELS & SZ & SV & BLK).
    apply (rw_cells_split_CB usegs _ _ [] 288 _ [] [224; 8; 56]%nat) in LOW; [|reflexivity]. cbn [mk_CB_cells app] in LOW.
    repeat match type of LOW with context [CB ?n ?t] => lazymatch t with take _ _ => idtac end; let j := fresh "j" in set (j := t) in LOW; clearbody j end.
    assert (LXS2 : lx_statics m2).
    { eapply lx_statics_agree; [exact (agree_of_lx_pres _ _ _ _ _ PRES2)| | exact LXS0]. intros a Ha. apply lxs_addr_client; [exact Ha|].
      pose proof (lxs_addr_lt a Ha) as [R1 _]. unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, SJ_GOT_NOTHROW, SJ_GOT_TABS, SJ_IMPL_VT24, SJ_DPI_VPTR in Ha.
      unfold LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha. lia. }
    pose proof LXS2 as (_ & _ & _ & _ & VTD2 & _). unfold SJ_DPI_VPTR, MallocRep.wz in VTD2.
    unfold SJ_DPI_PARSE, SJ_DPI_STAGE1, SJ_DPI_STAGE2, SJ_DPI_STAGE2_NEXT, SJ_DPI_PARSE_STRING, SJ_DPI_PARSE_WOBBLY, SJ_DPI_SET_CAPACITY, SJ_DPI_SET_MAX_DEPTH, SJ_DPI_DTOR, SJ_DPI_DTOR_DEL in VTD2.
    pose proof (munch_refl [(sp0, sp0 + 496)]%Z m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    hide BLK. unfold impl_cells16, SJ_DPI_VPTR in THIS.
    unfold implM. iprefix.

    step. hstep. step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    destruct (rw_cells_split_at1 _ _ _ 1%nat PA) as [PA0 Q1]. cbn [firstn skipn cells_size csize Nat.add] in PA0, Q1.
    destruct (rw_cells_split_at1 _ _ _ 1%nat Q1) as [PIMPL PREST]. cbn [firstn skipn cells_size csize Nat.add] in PIMPL, PREST.
    clear PA Q1. readdr PIMPL (sp0 + 296). readdr PREST (sp0 + 304).
    pose proof (RHEAP_pull _ [(pia, IA, 1024); (poc, OC, 8192); (pix, IDX, nix); (pim, IMPL, 96)] _ _ _ HEAP2) as HEAP2'. cbn [app] in HEAP2'.
    assert (ND : List.NoDup (map blk_id ((psb, SB, nsb) :: (pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, nix) :: (pim, IMPL, 96) :: (bv, A, 16 * cap) :: LB))) by (eapply LH_nodup; exact HEAP2').
    assert (HEAP3 : RHEAP st2 ((psb, SB, nsb) :: (pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, nix) :: (pim, IMPL, 96) :: (bv, A, 16 * cap) :: LB) m3).
    { eapply LH_frame; [exact HEAP2'| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX3 : rauxv_ok m3 B).
    { eapply rauxv_ok_frame; [exact AUX2| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client LB (sp0 + 496) [LXW_SJ] a -> outside [(sp0, sp0 + 496)] a).
    { intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    assert (PRES3 : lx_pres LB (sp0 + 496) [LXW_SJ] m0 m3).
    { eapply lx_pres_trans; [exact PRES2|]. eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]. }
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG3.
    assert (SJS3 : sj_statics m3 true).
    { eapply sj_statics_agree; [exact AG3| | exact SJS2]. intros a Ha. unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. cbn [outside]. split; [lia| exact I]. }
    assert (PL3 : payload_ok m3 LB D d).
    { eapply payload_ok_agree; [exact AG3| exact PL2|]. intros b a Hb Ha. pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in BC. cbn [outside]. split; [lia| exact I]. }
    unhide BLK.
    apply (vblk_agree _ _ _ _ _ _ _ _ _ AG3) in BLK; [| intros a _ Ha; cbn [outside]; clear - Ha AC CEIL LO Esp0; lia| exact ELS| lia].
    clear AG3 MU WM HEAP2 HEAP2' AUX2 PRES2 SJS2 PL2 LXS2.
    ihere. to_implM. eapply implM_bind.
    { eapply (opdel_arr_proof HF) with (B := B) (lo := lo) (A := SB) (n := nsb);
        [exact HEAP3| left; reflexivity| exact AUX3| lia| eassumption| exact CEIL'| unfold RFREE_STACK; lia| eassumption| assumption| lia]. }
    cbv beta. intros [] st4 ms4 PO. unfold free_postZ in PO.
    destruct PO as (v5 & v6 & v7 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m4
                    & -> & MI4 & ST4 & ERR4 & AUX4 & HP4 & FA4 & SO4 & HEAP4).
    rewrite (lb_remove_hd _ _ _ _ ND) in HP4, HEAP4. clear ND.
    replace (ret_pc (Z_to_bv 64 0x273e8)) with (Z_to_bv 64 0x273e8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite ELX in ERR4.
    pose proof (agree_of_heap_pres _ _ _ _ HP4) as AG4.
    assert (FRH : forall a, sp0 <= a < sp0 + 496 -> rclient_addr ((pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, nix) :: (pim, IMPL, 96) :: (bv, A, 16 * cap) :: LB) sp0 a) by (intros a Ha; left; lia).
    apply (rw_cells_agree _ _ _ _ _ AG4) in PA0; [| intros a Ha; cbn in Ha; apply FRH; lia].
    apply (rw_cells_agree _ _ _ _ _ AG4) in PIMPL; [| intros a Ha; cbn in Ha; apply FRH; lia].
    apply (rw_cells_agree _ _ _ _ _ AG4) in PREST; [| intros a Ha; cbn in Ha; apply FRH; lia].
    apply (rw_cells_agree _ _ _ _ _ AG4) in LOW; [| intros a Ha; cbn in Ha; apply FRH; lia].
    apply (rw_cells_agree _ _ _ _ _ AG4) in XFD; [| intros a Ha; cbn in Ha; apply FRH; lia].
    apply (rw_cells_agree _ _ _ _ _ AG4) in SAVE; [| intros a Ha; cbn in Ha; apply FRH; lia].
    apply (rw_cells_agree _ _ _ _ _ AG4) in SV; [| intros a Ha; cbn in Ha; apply FRH; lia].
    apply (rw_cells_agree _ _ _ _ _ AG4) in THIS; [| intros a Ha; right; right; exists (pim, IMPL, 96); split; [do 3 right; left; reflexivity| cbn in Ha; cbn [blk_addr blk_size fst snd]; lia]].
    apply (vblk_agree _ _ _ _ _ _ _ _ _ AG4) in BLK; [| intros a _ Ha; right; right; exists (bv, A, 16 * cap); split; [do 4 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]| exact ELS| lia].
    pose proof (statics_heap _ _ _ _ HP4 ltac:(unfold GLOBALS_TOP; lia)) as (_ & SJSf & _). pose proof (SJSf _ SJS3) as SJS4. clear SJSf.
    assert (PL4 : payload_ok m4 LB D d).
    { eapply payload_ok_agree; [exact AG4| exact PL3|]. intros b a Hb Ha. right; right. exists b. split; [do 5 right; exact Hb| exact Ha]. }
    assert (PRES4 : lx_pres LB (sp0 + 496) [LXW_SJ] m0 m4).
    { eapply lx_pres_trans; [exact PRES3|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP4| lia| intros b Hb; do 5 right; exact Hb]. }
    assert (LXS4 : lx_statics m4).
    { eapply lx_statics_agree; [exact (agree_of_lx_pres _ _ _ _ _ PRES4)| | exact LXS0]. intros a Ha. apply lxs_addr_client; [exact Ha|].
      pose proof (lxs_addr_lt a Ha) as [R1 _]. unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, SJ_GOT_NOTHROW, SJ_GOT_TABS, SJ_IMPL_VT24, SJ_DPI_VPTR in Ha.
      unfold LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha. lia. }
    pose proof LXS4 as (_ & _ & _ & _ & VTD4 & _). unfold SJ_DPI_VPTR, MallocRep.wz in VTD4.
    unfold SJ_DPI_PARSE, SJ_DPI_STAGE1, SJ_DPI_STAGE2, SJ_DPI_STAGE2_NEXT, SJ_DPI_PARSE_STRING, SJ_DPI_PARSE_WOBBLY, SJ_DPI_SET_CAPACITY, SJ_DPI_SET_MAX_DEPTH, SJ_DPI_DTOR, SJ_DPI_DTOR_DEL in VTD4.
    clear AG4 HP4 HEAP3 AUX3 PRES3 SJS3 PL3 VTD2 FRH.
    pose proof (munch_refl [(sp0, sp0 + 496)]%Z m4) as MU. pose proof (wmono_refl usegs m4) as WM.
    hide BLK.
    unfold implM. iprefix.

    step. hstep. step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
    zstep. rewrite (Atp_kitu.land7_mod8 IMPL) by (first [exact IM8| lia]). step. if_true.
    step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    assert (HEAP5 : RHEAP st4 ((pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, nix) :: (pim, IMPL, 96) :: (bv, A, 16 * cap) :: LB) m5).
    { eapply LH_frame; [exact HEAP4| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX5 : rauxv_ok m5 B).
    { eapply rauxv_ok_frame; [exact AUX4| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (PRES5 : lx_pres LB (sp0 + 496) [LXW_SJ] m0 m5).
    { eapply lx_pres_trans; [exact PRES4|]. eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]. }
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG5.
    assert (SJS5 : sj_statics m5 true).
    { eapply sj_statics_agree; [exact AG5| | exact SJS4]. intros a Ha. unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. cbn [outside]. split; [lia| exact I]. }
    assert (PL5 : payload_ok m5 LB D d).
    { eapply payload_ok_agree; [exact AG5| exact PL4|]. intros b a Hb Ha. pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in BC. cbn [outside]. split; [lia| exact I]. }
    unhide BLK.
    apply (vblk_agree _ _ _ _ _ _ _ _ _ AG5) in BLK; [| intros a _ Ha; cbn [outside]; clear - Ha AC CEIL LO Esp0; lia| exact ELS| lia].
    clear AG5 MU WM HEAP4 AUX4 PRES4 SJS4 PL4 LXS4 VTD4.
    ihere. to_implM.
    eapply (dpidtor_cps HF) with (B := B) (lo := lo) (THIS := IMPL) (IDX := IDX) (OC := OC) (IA := IA);
      [exact HEAP5| exact AUX5| lia| eassumption| exact CEIL'| unfold RFREE_STACK; lia| rewrite ELX; eassumption| assumption| lia| unfold impl_cells16; eassumption|].
    intros st6 ms6 PO. unfold hpost in PO.
    destruct PO as (w5 & w6 & w7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m6
                    & -> & MI6 & ST6 & (errv6 & ERR6) & AUX6 & FA6 & SO6 & HEAP6 & PRES56).
    replace (ret_pc (Z_to_bv 64 0x2740c)) with (Z_to_bv 64 0x2740c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite ELX in ERR6.

    pose proof (agree_of_lx_pres _ _ _ _ _ PRES56) as AG56.
    assert (FRCL : forall a, sp0 <= a < sp0 + 496 -> lx_client ((bv, A, 16 * cap) :: LB) sp0 [] a).
    { intros a Ha. split; [cbn [rin_ivs]; tauto| left; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AG56) in PA0; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG56) in PIMPL; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG56) in PREST; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG56) in LOW; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG56) in XFD; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG56) in SAVE; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG56) in SV; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (vblk_agree _ _ _ _ _ _ _ _ _ AG56) in BLK;
      [| intros a _ Ha; split; [cbn [rin_ivs]; tauto| right; left; exists (bv, A, 16 * cap); split; [left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]]
       | exact ELS| lia].
    assert (PL6 : payload_ok m6 LB D d).
    { eapply payload_ok_agree; [exact AG56| exact PL5|]. intros b a Hb Ha. split; [cbn [rin_ivs]; tauto| right; left; exists b; split; [right; exact Hb| exact Ha]]. }
    assert (SJS6 : sj_statics m6 true).
    { eapply sj_statics_agree; [exact AG56| | exact SJS5]. intros a Ha. apply sjs_addr_client; [exact Ha|]. cbn [rin_ivs]. tauto. }
    assert (PRES6 : lx_pres LB (sp0 + 496) [LXW_SJ] m0 m6).
    { eapply lx_pres_trans; [exact PRES5|]. eapply (lx_pres_sub LB (sp0 + 496) _ _ _ _ _ _ PRES56); [lia| intros b0 Hb0; right; exact Hb0|].
      intros a Ha NX. cbn [rin_ivs] in Ha. tauto. }
    clear AG56 PRES56 HEAP5 AUX5 PRES5 SJS5 PL5 FRCL.
    pose proof (munch_refl [(sp0, sp0 + 496)]%Z m6) as MU. pose proof (wmono_refl usegs m6) as WM.
    assert (ND : List.NoDup (map blk_id ((bv, A, 16 * cap) :: LB))) by (eapply LH_nodup; exact HEAP6).
    hide BLK.
    unfold implM. iprefix.

    step. hstep. step. step.

    step. step. if_lia. zstep. rewrite (Atp_kitu.land7_mod8 (sp0 + 344)) by (first [exact SP8| lia]). step. if_false.
    step. step. if_lia. step. step.
    lazymatch goal with |- evt _ ?QQ (MS _ _ _ _ _ ?mc _) =>
    assert (VT : forall y5 y6 y7 y8 y9 y11 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31,
               evt usegs QQ (MS (mkR (Z_to_bv 64 160796) (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) y5 y6 y7 y8 y9 (Z_to_bv 64 A) y11 (Z_to_bv 64 (sp0 + 344)) y13 y14 y15 y16 y17
                                     y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                                F1 (Z_to_bv 64 0x2a07c) fc1 None mc (seg_rom usegs))) end.
    2:{ if_cases KE; zify_cond KE.
        -   apply VT.
        -
          rewrite ?unsigned_lit in KE by lia.
          step.
          replace (A + 16 * n) with (A + 16 * Z.of_nat (Z.to_nat n)) by lia.
          eapply (vdtor_loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A (Z.to_nat n)); [clear - A0 A16; pose proof (Z.mod_divide A 16 ltac:(lia)) as [H _]; destruct (H A16) as [q Hq]; lia| lia| lia|].
          apply VT. }
    intros y5 y6 y7 y8 y9 y11 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31.

    step. zstep. replace (A + 16 * cap + - A) with (16 * cap) by lia. hstep. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
    assert (HEAP7 : RHEAP st6 ((bv, A, 16 * cap) :: LB) m7).
    { eapply LH_frame; [exact HEAP6| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX7 : rauxv_ok m7 B).
    { eapply rauxv_ok_frame; [exact AUX6| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (PRES7 : lx_pres LB (sp0 + 496) [LXW_SJ] m0 m7).
    { eapply lx_pres_trans; [exact PRES6|]. eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]. }
    assert (SJS7 : sj_statics m7 true).
    { eapply sj_statics_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact SJS6]. intros a Ha. unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. cbn [outside]. split; [lia| exact I]. }
    assert (PL7 : payload_ok m7 LB D d).
    { eapply payload_ok_agree; [exact (agree_on_of_munch _ _ _ MU WM)| exact PL6|]. intros b a Hb Ha. pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in BC. cbn [outside]. split; [lia| exact I]. }
    clear MU WM BLK.
    ihere. to_implM. cbn [vfree]. eapply implM_bind.
    { eapply (opdel_sized_proof HF) with (B := B) (lo := lo) (A := A) (n := 16 * cap);
        [exact HEAP7| left; reflexivity| exact AUX7| lia| eassumption| exact CEIL'| unfold RFREE_STACK; lia| eassumption| assumption| lia]. }
    cbv beta. intros [] st8 ms8 PO. unfold free_postZ in PO.
    destruct PO as (z5 & z6 & z7 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m8
                    & -> & MI8 & ST8 & ERR8 & AUX8 & HP8 & FA8 & SO8 & HEAP8).
    rewrite (lb_remove_hd _ _ _ _ ND) in HP8, HEAP8.
    replace (ret_pc (Z_to_bv 64 0x2741c)) with (Z_to_bv 64 0x2741c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (agree_of_heap_pres _ _ _ _ HP8) as AG8.
    assert (FRH : forall a, sp0 <= a < sp0 + 496 -> rclient_addr LB sp0 a) by (intros a Ha; left; lia).
    lazymatch goal with H : rw_cells usegs m7 (sp0 + 344) _ |- _ => apply (rw_cells_agree _ _ _ _ _ AG8) in H; [rename H into SV8| intros a Ha; cbn in Ha; apply FRH; lia] end.
    apply (rw_cells_agree _ _ _ _ _ AG8) in PA0; [| intros a Ha; cbn in Ha; apply FRH; lia].
    apply (rw_cells_agree _ _ _ _ _ AG8) in PIMPL; [| intros a Ha; cbn in Ha; apply FRH; lia].
    apply (rw_cells_agree _ _ _ _ _ AG8) in PREST; [| intros a Ha; cbn in Ha; apply FRH; lia].
    apply (rw_cells_agree _ _ _ _ _ AG8) in LOW; [| intros a Ha; cbn in Ha; apply FRH; lia].
    apply (rw_cells_agree _ _ _ _ _ AG8) in XFD; [| intros a Ha; cbn in Ha; apply FRH; lia].
    apply (rw_cells_agree _ _ _ _ _ AG8) in SAVE; [| intros a Ha; cbn in Ha; apply FRH; lia].
    pose proof (statics_heap _ _ _ _ HP8 ltac:(unfold GLOBALS_TOP; lia)) as (_ & SJSf & _). pose proof (SJSf _ SJS7) as SJS8. clear SJSf.
    assert (PL8 : payload_ok m8 LB D d).
    { eapply payload_ok_agree; [exact AG8| exact PL7|]. intros b a Hb Ha. right; right. exists b. split; [exact Hb| exact Ha]. }
    assert (PRES8 : lx_pres LB (sp0 + 496) [LXW_SJ] m0 m8).
    { eapply lx_pres_trans; [exact PRES7|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP8| lia| intros b Hb; exact Hb]. }
    clear AG8 HP8 HEAP7 AUX7 PRES7 SJS7 PL7 HEAP6 AUX6 PRES6 SJS6 PL6.

    pose proof (rw_cells_join _ _ _ _ _ LOW PA0 ltac:(cbn [app cells_size csize Nat.add]; lia)) as J1.
    pose proof (rw_cells_join _ _ _ _ _ J1 PIMPL ltac:(cbn [app cells_size csize Nat.add]; lia)) as J2.
    pose proof (rw_cells_join _ _ _ _ _ J2 PREST ltac:(cbn [app cells_size csize Nat.add]; lia)) as J3.
    pose proof (rw_cells_join _ _ _ _ _ J3 SV8 ltac:(cbn [app cells_size csize Nat.add]; lia)) as J4.
    pose proof (rw_cells_join _ _ _ _ _ J4 XFD ltac:(cbn [app cells_size csize Nat.add]; lia)) as J5.
    pose proof (rw_cells_join _ _ _ _ _ J5 SAVE ltac:(cbn [app cells_size csize Nat.add]; lia)) as FR. cbn [app] in FR.
    clear J1 J2 J3 J4 J5 LOW PA0 PIMPL PREST SV8 XFD SAVE.
    pose proof (munch_refl [(sp0, sp0 + 496)]%Z m8) as MU. pose proof (wmono_refl usegs m8) as WM.
    apply implM_ret.

    step. do 13 step. step. release_frame FR ST8 (sp0 + 496). step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
    assert (PRESF : lx_pres LB (sp0 + 496) [LXW_SJ] m0 mF).
    { eapply lx_pres_trans; [exact PRES8|]. eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]. }
    pose proof (agree_of_lx_pres _ _ _ _ _ PRESF) as AGF.
    rewrite Esp0. replace (usp - 496 + 496) with usp by lia. rewrite <- ESP. rewrite Esp0 in PRESF. replace (usp - 496 + 496) with usp in PRESF by lia.
    apply evt_done. unfold rfuzz_one_post, lx_post_env, lx_env. cbn [app]. rewrite <- Eusp. do 15 eexists. exists F1, fc1, mF.
    split; [cbv delta [mkR]; reflexivity|].
    split.
    { split; [| split; [exact FRM1| split; [exact PRESF| split; congruence]]].
      exists errv6.
      split. { eapply LH_frame; [exact HEAP8| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      split. { eapply lx_statics_agree; [exact AGF| | exact LXS0]. intros a Ha. apply lxs_addr_client; [exact Ha|].
               pose proof (lxs_addr_lt a Ha) as [R1 _]. unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, SJ_GOT_NOTHROW, SJ_GOT_TABS, SJ_IMPL_VT24, SJ_DPI_VPTR in Ha.
               unfold LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha. lia. }
      split. { exists true. eapply sj_statics_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact SJS8]. intros a Ha.
               unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. cbn [outside]. split; [lia| exact I]. }
      split. { eapply stderr_wfile_agree; [exact AGF| | exact SEW0]. intros a Ha. apply stderr_addr_client; [exact Ha|].
               unfold stderr_addr in Ha. unfold LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha. lia. }
      split. { pose proof (ssp_canary_0 _ _ _ _ HEAP00 SSP0) as EC. rewrite EC. eapply RHEAP_ssp.
               eapply LH_frame; [exact HEAP8| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      split. { eapply rauxv_ok_frame; [exact AUX8| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      split; [lia|]. split; [exact B63|]. split; [rewrite Esp0 in ST8; replace (usp - 496 + 496) with usp in ST8 by lia; exact ST8|]. split; [exact CEIL'|]. split; [unfold GLOBALS_TOP; lia|].
      split. { unfold errno_addr, RATP. rewrite unsigned_lit by lia. exact ERR8. }
      split; [reflexivity| assumption]. }
    split. { eapply sj_statics_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact SJS8]. intros a Ha.
             unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. cbn [outside]. split; [lia| exact I]. }
    split; [reflexivity|]. split; [reflexivity|].
    eapply payload_ok_agree; [exact (agree_on_of_munch _ _ _ MU WM)| exact PL8|]. intros b a Hb Ha.
    pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (_ & _ & _ & BC & _). unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in BC. cbn [outside]. split; [lia| exact I].
  Qed.

  Lemma od_exit_del : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
      (m0 : mem) (s00 : PState) (LB : list block) (D : Z) (d : list Z) (lo B : Z) (canary : word)
      (bv : bptr) (A cap n : Z) (els : list (Z * Z)) (psb pim pix poc pia pcp : bptr) (SB nsb COPY ncp : Z) (m2 : mem) (st2 : PState),
    RHEAP s00 LB m0 -> lx_statics m0 -> stderr_wfile m0 -> ssp_cells m0 canary ->
    bv_unsigned sp <= B -> B < 2^63 -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - LX_FUZZ_STACK ->
    tp = wz RATP -> bv_unsigned sp mod 16 = 0 -> cap < 2^26 -> frm0 fc1 ->
    exit_inv (bv_unsigned sp - 496) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra m0 s00 LB lo B D d bv A cap n els psb pim pix poc pia SB nsb [(pcp, COPY, ncp)] m2 st2 ->
    implM usegs (mbind (del lops pcp) (fun _ =>
                 mbind (del lops psb) (fun _ => mbind (del lops pia) (fun _ => mbind (del lops poc) (fun _ =>
                 mbind (del lops pix) (fun _ => mbind (del lops pim) (fun _ => mbind (vfree lops (cap, n, Some bv)) (fun _ => mret 0))))))))
          st2
          (rfuzz_one_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s00 LB D d lo B canary m0)
          (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp - 496)) gp tp xt0 xt1 xt2 (Z_to_bv 64 COPY) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
              F1 (Z_to_bv 64 0x273d0) fc1 None m2 (seg_rom usegs)).
  Proof.
    intros until st2. intros HEAP00 LXS0 SEW0 SSP0 SPB B63 CEIL GLO LO TP AL16 CAPB FRM1 XI.
    pose proof TP as TP'. pose proof LO as LO'. pose proof GLO as GLO'.
    unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP in LO, GLO. unfold MallocRep.wz in TP.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    remember (bv_unsigned sp - 496) as sp0 eqn:Esp0.
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    subst tp.
    destruct XI as (IMPL & IDX & OC & IA & nix & errv2 & jr & j0 & j304 & jfd & w320 & w328 & w336 & w344
                    & nsi & nxt & capv & md & bufv & lenv & docv & b48 & b49 & p12 & p28 & p50
                    & HEAP2 & AUX2 & MI2 & ST2 & ERR2 & FA2 & SO2 & PRES2 & SJS2 & PL2 & VR2 & LOW & PA & THIS & XFD & SAVE).
    cbn [app] in HEAP2.
    assert (LO0 : 0 <= lo) by (destruct ST2 as [? _]; assumption).
    assert (ELX : LX_ERRNO = 609404) by reflexivity. rewrite ELX in ERR2.
    pose proof (LH_block_range _ _ _ _ HEAP2 ltac:(do 6 right; left; reflexivity)) as (A0 & _ & _ & AC & AS).
    cbn [blk_addr blk_size fst snd] in A0, AC, AS. unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in AC.
    destruct VR2 as (ELS & SZ & SV & BLK).
    pose proof (RHEAP_pull _ [(pia, IA, 1024); (poc, OC, 8192); (pix, IDX, nix); (pim, IMPL, 96); (psb, SB, nsb)] _ _ _ HEAP2) as HEAP2'. cbn [app] in HEAP2'.
    assert (ND : List.NoDup (map blk_id ((pcp, COPY, ncp) :: (pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, nix) :: (pim, IMPL, 96) :: (psb, SB, nsb) :: (bv, A, 16 * cap) :: LB))) by (eapply LH_nodup; exact HEAP2').
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    unfold implM. iprefix.

    step. step.
    ihere. to_implM. eapply implM_bind.
    { eapply (opdel_arr_proof HF) with (B := B) (lo := lo) (A := COPY) (n := ncp);
        [exact HEAP2'| left; reflexivity| exact AUX2| lia| eassumption| exact CEIL'| unfold RFREE_STACK; lia| rewrite ELX; eassumption| assumption| lia]. }
    cbv beta. intros [] st4 ms4 PO. unfold free_postZ in PO.
    destruct PO as (v5 & v6 & v7 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m4
                    & -> & MI4 & ST4 & ERR4 & AUX4 & HP4 & FA4 & SO4 & HEAP4).
    rewrite (lb_remove_hd _ _ _ _ ND) in HP4, HEAP4. clear ND.
    replace (ret_pc (Z_to_bv 64 0x273d8)) with (Z_to_bv 64 0x273d8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (agree_of_heap_pres _ _ _ _ HP4) as AG4.
    assert (FRH : forall a, sp0 <= a < sp0 + 496 -> rclient_addr ((pia, IA, 1024) :: (poc, OC, 8192) :: (pix, IDX, nix) :: (pim, IMPL, 96) :: (psb, SB, nsb) :: (bv, A, 16 * cap) :: LB) sp0 a) by (intros a Ha; left; lia).
    apply (rw_cells_agree _ _ _ _ _ AG4) in PA; [| intros a Ha; cbn in Ha; apply FRH; lia].
    apply (rw_cells_agree _ _ _ _ _ AG4) in LOW; [| intros a Ha; cbn in Ha; apply FRH; lia].
    apply (rw_cells_agree _ _ _ _ _ AG4) in XFD; [| intros a Ha; cbn in Ha; apply FRH; lia].
    apply (rw_cells_agree _ _ _ _ _ AG4) in SAVE; [| intros a Ha; cbn in Ha; apply FRH; lia].
    apply (rw_cells_agree _ _ _ _ _ AG4) in SV; [| intros a Ha; cbn in Ha; apply FRH; lia].
    apply (rw_cells_agree _ _ _ _ _ AG4) in THIS; [| intros a Ha; right; right; exists (pim, IMPL, 96); split; [do 3 right; left; reflexivity| cbn in Ha; cbn [blk_addr blk_size fst snd]; lia]].
    apply (vblk_agree _ _ _ _ _ _ _ _ _ AG4) in BLK; [| intros a _ Ha; right; right; exists (bv, A, 16 * cap); split; [do 5 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]| exact ELS| lia].
    pose proof (statics_heap _ _ _ _ HP4 ltac:(unfold GLOBALS_TOP; lia)) as (_ & SJSf & _). pose proof (SJSf _ SJS2) as SJS4. clear SJSf.
    assert (PL4 : payload_ok m4 LB D d).
    { eapply payload_ok_agree; [exact AG4| exact PL2|]. intros b a Hb Ha. right; right. exists b. split; [do 6 right; exact Hb| exact Ha]. }
    assert (PRES4 : lx_pres LB (sp0 + 496) [LXW_SJ] m0 m4).
    { eapply lx_pres_trans; [exact PRES2|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HP4| lia| intros b Hb; do 6 right; exact Hb]. }
    rewrite Esp0.
    eapply (od_exit_tail ra sp) with (B := B) (lo := lo) (canary := canary) (m0 := m0);
      [exact HEAP00| exact LXS0| exact SEW0| exact SSP0| exact SPB| exact B63| exact CEIL'| exact GLO'| exact LO'| reflexivity| exact AL16| exact CAPB| exact FRM1|].
    rewrite <- Esp0.
    exists IMPL, IDX, OC, IA, nix, errv2, jr, j0, j304, jfd, w320, w328, w336, w344, nsi, nxt, capv, md, bufv, lenv, docv, b48, b49, p12, p28, p50.
    cbn [app].
    split; [exact HEAP4|]. split; [exact AUX4|]. split; [exact MI4|]. split; [exact ST4|]. split; [exact ERR4|]. split; [congruence|]. split; [congruence|].
    split; [exact PRES4|]. split; [exact SJS4|]. split; [exact PL4|].
    split. { split; [exact ELS|]. split; [exact SZ|]. split; [exact SV| exact BLK]. }
    split; [exact LOW|]. split; [exact PA|]. split; [exact THIS|]. split; [exact XFD| exact SAVE].
  Qed.

  Lemma od_exit_err : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
      (m0 : mem) (s00 : PState) (LB : list block) (D : Z) (d : list Z) (lo B : Z) (canary : word)
      (bv : bptr) (A cap n : Z) (els : list (Z * Z)) (psb pim pix poc pia : bptr) (SB nsb : Z) (cpo : option bptr) (COPY ncp : Z) (m2 : mem) (st2 : PState),
    RHEAP s00 LB m0 -> lx_statics m0 -> stderr_wfile m0 -> ssp_cells m0 canary ->
    bv_unsigned sp <= B -> B < 2^63 -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - LX_FUZZ_STACK ->
    tp = wz RATP -> bv_unsigned sp mod 16 = 0 -> cap < 2^26 -> frm0 fc1 ->
    (cpo = None -> COPY = 0) ->
    exit_inv (bv_unsigned sp - 496) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra m0 s00 LB lo B D d bv A cap n els psb pim pix poc pia SB nsb
             (match cpo with Some p => [(p, COPY, ncp)] | None => [] end) m2 st2 ->
    implM usegs (mbind (match cpo with Some p => del lops p | None => mret tt end) (fun _ =>
                 mbind (del lops psb) (fun _ => mbind (del lops pia) (fun _ => mbind (del lops poc) (fun _ =>
                 mbind (del lops pix) (fun _ => mbind (del lops pim) (fun _ => mbind (vfree lops (cap, n, Some bv)) (fun _ => mret 0))))))))
          st2
          (rfuzz_one_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s00 LB D d lo B canary m0)
          (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp - 496)) gp tp xt0 xt1 xt2 (Z_to_bv 64 COPY) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 (Z_to_bv 64 (match cpo with Some _ => 0 | None => 1 end)) xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
              F1 (Z_to_bv 64 0x273cc) fc1 None m2 (seg_rom usegs)).
  Proof.
    intros until st2. intros HEAP00 LXS0 SEW0 SSP0 SPB B63 CEIL GLO LO TP AL16 CAPB FRM1 CNONE XI.
    destruct cpo as [pcp|].
    -
      assert (C0 : 0 < COPY < 2^63).
      { destruct XI as (IMPL & IDX & OC & IA & nix & errv2 & jr & j0 & j304 & jfd & w320 & w328 & w336 & w344
                    & nsi & nxt & capv & md & bufv & lenv & docv & b48 & b49 & p12 & p28 & p50 & HEAP2 & _).
        pose proof (LH_block_range _ _ _ _ HEAP2 ltac:(do 5 right; left; reflexivity)) as (C0 & _ & C1 & CC & _). cbn [blk_addr blk_size fst snd] in C0, C1, CC.
        unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in CC. pose proof alloc_ceiling_range. lia. }
      unfold implM. iprefix.
      step. if_false.
      ihere. to_implM.
      eapply (od_exit_del ra sp) with (B := B) (lo := lo) (canary := canary) (m0 := m0); eassumption.
    -
      unfold implM. iprefix.
      step. if_true.
      ihere. to_implM. apply implM_ret_bind.
      eapply (od_exit_tail ra sp) with (B := B) (lo := lo) (canary := canary) (m0 := m0); eassumption.
  Qed.

  Lemma od_exit_it : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
      (m0 : mem) (s00 : PState) (LB : list block) (D : Z) (d : list Z) (lo B : Z) (canary : word)
      (bv : bptr) (A cap n : Z) (els : list (Z * Z)) (psb pim pix poc pia pcp : bptr) (SB nsb : Z) (COPY ncp : Z) (m2 : mem) (st2 : PState),
    RHEAP s00 LB m0 -> lx_statics m0 -> stderr_wfile m0 -> ssp_cells m0 canary ->
    bv_unsigned sp <= B -> B < 2^63 -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - LX_FUZZ_STACK ->
    tp = wz RATP -> bv_unsigned sp mod 16 = 0 -> cap < 2^26 -> frm0 fc1 ->
    rw_cells usegs m2 (bv_unsigned sp - 496 + 136) [C8 (Z_to_bv 64 0)] ->
    exit_inv (bv_unsigned sp - 496) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra m0 s00 LB lo B D d bv A cap n els psb pim pix poc pia SB nsb
             [(pcp, COPY, ncp)] m2 st2 ->
    implM usegs (mbind (del lops pcp) (fun _ =>
                 mbind (del lops psb) (fun _ => mbind (del lops pia) (fun _ => mbind (del lops poc) (fun _ =>
                 mbind (del lops pix) (fun _ => mbind (del lops pim) (fun _ => mbind (vfree lops (cap, n, Some bv)) (fun _ => mret 0))))))))
          st2
          (rfuzz_one_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s00 LB D d lo B canary m0)
          (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp - 496)) gp tp xt0 xt1 xt2 (Z_to_bv 64 COPY) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
              F1 (Z_to_bv 64 0x29310) fc1 None m2 (seg_rom usegs)).
  Proof.
    intros until st2. intros HEAP00 LXS0 SEW0 SSP0 SPB B63 CEIL GLO LO TP AL16 CAPB FRM1 C136 XI.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (SP0R : 0 <= bv_unsigned sp - 496).
    { destruct XI as (IMPL & IDX & OC & IA & nix & errv2 & jr & j0 & j304 & jfd & w320 & w328 & w336 & w344
                    & nsi & nxt & capv & md & bufv & lenv & docv & b48 & b49 & p12 & p28 & p50 & _ & _ & _ & ST2 & _).
      destruct ST2 as (L0 & L1 & _). unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK in LO. lia. }
    remember (bv_unsigned sp - 496) as sp0 eqn:Esp0.
    unfold implM. iprefix.

    step. step. if_false. step.
    ihere. to_implM. rewrite Esp0.
    eapply (od_exit_del ra sp) with (B := B) (lo := lo) (canary := canary) (m0 := m0); try eassumption. rewrite <- Esp0. exact XI.
  Qed.
End Proofs.
End WithCeiling0.
