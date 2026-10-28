(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr Bytes FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun STree Malloc Monad Stdio SjModel AtpModel ElModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_h_kit Pj_relro.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage2_iface Atp_pid Atp_defs Atp_h_defs El_defs El_hdr El_h2 El_h3 El_act El_a22 El_throw_site.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_stage1_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Lemma Z_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. cbn [Z.of_N Z.pow_pos Pos.iter Z.mul Pos.mul] in Hb.
  assert (NN : 0 <= bytes_le_to_Z bs).
  { rewrite bytes_le_to_Z_le_val. pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)). lia. }
  rewrite lor_shiftl8_add by lia. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N Z.pow_pos Pos.iter Z.mul Pos.mul].
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace ((bv_unsigned b + 256 * bytes_le_to_Z bs) / 256) with (bytes_le_to_Z bs); [exact IH|].
    symmetry. rewrite Z.mul_comm. rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.
Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  assert (R : 0 <= bytes_le_to_Z bs < 2^64).
  { rewrite bytes_le_to_Z_le_val. pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as X. rewrite length_map, L in X. cbn in X. lia. }
  rewrite bv_wrap_small by (unfold bv_modulus; cbn [Z.of_N]; lia). rewrite <- L. apply Z_to_le_bytes_to_Z.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma rw_cells_CB8_C8 : forall m A (bs : list byte), rw_cells usegs m A [CB 8 bs] -> rw_cells usegs m A [C8 (le_bytes_to_word bs)].
Proof.
  intros m A bs H. pose proof H as [[W _] _]. cbn in W. destruct W as [L _].
  eapply rw_cells_recast; [exact H| cbn; auto| cbn [cells_bytes cbytes]; rewrite le8_of_bytes by exact L; reflexivity| reflexivity].
Qed.

Lemma act_env_site : forall E m0 m m1 m' s00 st st' LB D d sp0 lo B errv errv' bvp psb ptp pim pix poc pia A cap IMPL IDX OC IA jr
    j0 jres jos j313 j329 j361 j416 j441 nsi nxt capv md bufv lenv docv b48 b49 p12 p28 p50 s0 s1 s2 s3 s4 s5 s6 s7 s8 ra fc DF,
  0 <= DF <= 64 ->
  act_env E m0 m s00 st LB D d sp0 lo B errv bvp psb ptp pim pix poc pia A cap IMPL IDX OC IA jr j0 jres jos j313 j329 j361 j416 j441 nsi nxt capv md bufv lenv docv b48 b49 p12 p28 p50
          s0 s1 s2 s3 s4 s5 s6 s7 s8 ra fc ->
  munch [(lo, sp0)]%Z m m1 -> wmono usegs m m1 ->
  (forall a, 0 <= a < 2^64 -> rclient_addr (ae_LB E) sp0 a -> ~ (EL_EHG <= a < EL_EHG + 12) -> ~ (EL_UNW <= a < EL_UNW + 8) ->
     m' (wa a) = m1 (wa a) /\ (wview usegs m1 (wa a) <> None -> wview usegs m' (wa a) <> None)) ->
  mem_inv usegs m' -> stk usegs m' lo sp0 -> RHEAP st' (ae_LB E) m' -> ps_fa st' = ps_fa st -> ps_so st' = ps_so st ->
  rw_cells usegs m' LX_ERRNO [C4 errv'] -> rauxv_ok m' B ->
  rw_cells usegs m' EL_EHG [C8 (wz 0); C4 (wz 0)] -> rw_cells usegs m' EL_UNW (uw_cells true) ->
  act_env E m0 m' s00 st' LB D d sp0 lo B errv' bvp psb ptp pim pix poc pia A cap IMPL IDX OC IA jr j0 jres jos j313 j329 j361 j416 j441 nsi nxt capv md bufv lenv docv b48 b49 p12 p28 p50
          s0 s1 s2 s3 s4 s5 s6 s7 s8 ra fc
  /\ ps_fa st' = ps_fa st /\ ps_so st' = ps_so st.
Proof.
  intros until DF. intros HDF AE MU1 WM1 SAG MI' ST' HEAP' FA' SO' ERR' AUX' EHG' UNW'.
  destruct AE as (OK & AI & ELB & ELO & EB & EDOC & EP1 & HEAP00 & LXS0 & HEAP & AUX & QB & B63 & ST & CEIL & GLO & LO & ERR & MI & AL16 & FRM & PRES & SJS & PL & FD
                  & VR & NTH0 & J0 & RES & OS & ROOT & PA0 & PIMPL & PA16 & DCAP & P48 & THIS & XSEL & XFD & SAVE).
  unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP in *.
  pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (BLB : forall a, in_block LB a -> 0 < a < alloc_ceiling).
  { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP00 Hb) as (B0 & _ & _ & BC & _). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. lia. }
  assert (BLA : forall a, in_block (ae_LB E) a -> 0 < a < alloc_ceiling /\ (a < 0x10000 \/ 0x111000 <= a)).
  { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP Hb) as (B0 & _ & _ & BC & BI). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in BC. lia. }
  assert (LBsub : forall b, In b LB -> In b (ae_LB E)) by (intros b Hb; rewrite ELB; unfold el_blocks; do 7 right; exact Hb).

  set (P := fun a => rclient_addr (ae_LB E) sp0 a /\ ~ (EL_EHG <= a < EL_EHG + 12) /\ ~ (EL_UNW <= a < EL_UNW + 8)).
  assert (AG : agree_on P m m').
  { intros a Ha (HC & N1 & N2). destruct (SAG a Ha HC N1 N2) as [E2 W2].
    assert (OUT : outside [(lo, sp0)] a).
    { cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| lia| specialize (BLA a HC); lia]. }
    destruct (agree_on_of_munch _ _ _ MU1 WM1 a Ha OUT) as [E1 W1]. split; [congruence| auto]. }
  assert (FRP : forall a, sp0 <= a < sp0 + 528 -> P a) by (intros a Ha; subst P; cbv beta; split; [left; lia| lia]).
  assert (INB : forall b a, In b (ae_LB E) -> blk_addr b <= a < blk_addr b + blk_size b -> P a).
  { intros b a Hb Ha. assert (IB : in_block (ae_LB E) a) by (exists b; auto). specialize (BLA a IB). subst P; cbv beta. split; [right; right; exact IB| lia]. }
  assert (STP : forall a, 0xd6000 <= a < 0x111000 -> ~ ralloc_static a -> ~ (EL_EHG <= a < EL_EHG + 12) -> ~ (EL_UNW <= a < EL_UNW + 8) -> P a).
  { intros a Ha NR N1 N2. subst P; cbv beta. split; [right; left; split; [exact Ha| exact NR]| split; [exact N1| exact N2]]. }
  Ltac hif AG FRP H := apply (rw_cells_agree _ _ _ _ _ AG) in H; [| intros a Ha; try unfold p48_cells, el_root in Ha; cbn in Ha; apply FRP; lia].
  hif AG FRP J0. hif AG FRP RES. hif AG FRP OS. hif AG FRP PA0. hif AG FRP PIMPL. hif AG FRP PA16. hif AG FRP DCAP. hif AG FRP P48. hif AG FRP XSEL. hif AG FRP XFD. hif AG FRP SAVE.
  unfold el_root in ROOT. hif AG FRP ROOT.
  apply (rw_cells_agree _ _ _ _ _ AG) in THIS; [| intros a Ha; eapply INB; [rewrite ELB; unfold el_blocks; do 3 right; left; reflexivity| unfold impl_cells16 in Ha; cbn in Ha; cbn [blk_addr blk_size fst snd]; lia]].
  destruct VR as (ELS & SZ & SV & BLK). hif AG FRP SV.
  apply (vblk_agree _ _ _ _ _ _ _ _ _ AG) in BLK; [| intros a _ Ha; eapply INB; [rewrite ELB; unfold el_blocks; do 6 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]| exact ELS| lia].
  split; [| split; assumption].
  split; [exact OK|]. split.
  { eapply AINV_agree; [exact AI| exact AG| | | exact OK].
    - intros a (b & Hb & Hr). eapply INB; [exact Hb| exact Hr].
    - intros a Ha. rewrite EDOC in Ha. apply FRP; lia. }
  do 7 (split; [assumption|]). split; [exact HEAP'|]. split; [exact AUX'|].
  do 6 (split; [assumption|]). split; [exact ERR'|]. split; [exact MI'|]. split; [exact AL16|]. split; [exact FRM|]. split.
  { intros a Ha HCl. destruct (PRES a Ha HCl) as [E0 W0]. destruct HCl as [NX HC].
    assert (Pa : P a).
    { unfold LXW_SJ, LXW_UNW, SJ_STATICS_LO, SJ_STATICS_HI in NX. cbn [rin_ivs fst snd] in NX. subst P; cbv beta.
      split; [| clear - NX; lia]. destruct HC as [HC|[HC|HC]]; [left; lia| right; right; destruct HC as (b & Hb & Hr); exists b; split; [apply LBsub; exact Hb| exact Hr]| right; left; exact HC]. }
    destruct (AG a Ha Pa) as [E1 W1]. split; [congruence| auto]. }
  split. { destruct SJS as (SC & LOC & _). split; [| split; [| split; [exact EHG'| exists true; exact UNW']]].
           - eapply rw_cells_agree; [exact AG| exact SC|]. intros a Ha. cbn in Ha. unfold SJ_STATICS_LO in Ha. apply STP; [lia| | lia| lia].
             unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU.RMalloc_iface.ralloc_static, OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU.RMallocRep.RLIBC, OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU.RMallocRep.RCTX, OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU.RMallocRep.RERRNO, OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU.RMallocRep.RSSP_GUARD, OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU.RMallocRep.RGOT_SSP. lia.
           - eapply pj_locale_agree; [exact AG| | exact LOC]. intros a Ha. apply STP; [lia| | lia| lia].
             unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU.RMalloc_iface.ralloc_static, OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU.RMallocRep.RLIBC, OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU.RMallocRep.RCTX, OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU.RMallocRep.RERRNO, OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU.RMallocRep.RSSP_GUARD, OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU.RMallocRep.RGOT_SSP. lia. }
  split. { eapply payload_ok_agree; [exact AG| exact PL|]. intros b a Hb Ha. eapply INB; [apply LBsub; exact Hb| exact Ha]. }
  split; [exact FD|]. split; [split; [exact ELS| split; [exact SZ| split; [exact SV| exact BLK]]]|]. split; [exact NTH0|].
  split; [exact J0|]. split; [exact RES|]. split; [exact OS|]. split; [exact ROOT|].
  repeat (split; [assumption|]). exact SAVE.
Qed.

Theorem throw_slot_of_site : forall SITE DF RA XP XR, 0 <= DF <= 64 -> throw_site_stmt SITE DF RA XP XR -> throw_slot SITE DF RA XP XR.
Proof.
  intros SITE DF RA XP XR HDF TS. unfold throw_slot. intros until p50. intros AE MU1 WM1 MI1 ST1 FR1 XP1 XR1 HK.
  pose proof AE as AE'.
  destruct AE' as (OK & AI & ELB & ELO & EB & EDOC & EP1 & HEAP00 & LXS0 & HEAP & AUX & QB & B63 & ST & CEIL & GLO & LO & ERR & MI & AL16 & FRM & PRES & SJS & PL & FD
                   & VR & NTH0 & J0 & RES & OS & ROOT & PA0 & PIMPL & PA16 & DCAP & P48 & THIS & XSEL & XFD & SAVE).
  unfold LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP in *.
  pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).

  pose proof (agree_on_of_munch _ _ _ MU1 WM1) as AG1.
  assert (HEAP1 : RHEAP st (ae_LB E) m1).
  { eapply LH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
  assert (LXS : lx_statics m).
  { eapply lx_statics_agree; [exact (agree_of_lx_pres _ _ _ _ _ PRES)| | exact LXS0]. intros a Ha. apply lxs_addr_client; [exact Ha|].
    pose proof (lxs_addr_lt a Ha) as [R1 _]. unfold lxs_addr, LX_GOT_STDERR, LX_STDERR_PTR, SJ_GOT_NOTHROW, SJ_IMPL_VT24, SJ_DPI_VPTR in Ha.
    unfold LXW_SJ, LXW_UNW, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha. lia. }
  destruct (statics_munch _ _ _ rr_guard MU1 WM1 ltac:(intros a Ha; cbn [outside]; unfold GLOBALS_TOP in Ha; lia)) as (LXf & SJf & _ & _).
  pose proof (LXf LXS) as LXS1. pose proof (SJf _ SJS) as SJS1. clear LXf SJf.
  pose proof (lx_statics_pj _ LXS1) as (_ & _ & _ & _ & _ & RELRO1). pose proof (lx_statics_el _ LXS1) as (XD1 & HD1 & MR1 & _).
  destruct SJS1 as (_ & _ & EHG1 & uw & UNW1).
  pose proof (RHEAP_ssp _ _ _ HEAP1) as SSP1.
  assert (ELX : LX_ERRNO = 980196) by reflexivity. rewrite ELX in ERR.
  apply (rw_cells_agree _ _ _ _ _ AG1) in ERR; [| intros a Ha; cbn in Ha; cbn [outside]; lia].

  destruct (proj1 (rw_cells_app usegs m1 (sp0 + -16) [CB 8 jx] [C8 (Z_to_bv 64 RA)]) FR1) as [FRlo FRra].
  cbn [cells_size csize Nat.add] in FRra. replace (sp0 + -16 + Z.of_nat 8) with (sp0 + -16 + 8) in FRra by lia.
  apply rw_cells_CB8_C8 in FRlo.
  assert (USP : bv_unsigned (Z_to_bv 64 (sp0 - 16 - DF)) = sp0 - 16 - DF) by (apply unsigned_lit; lia).

  apply implM_bind_assoc_rev.
  eapply implM_bind.
  { pose proof (TS x1 (Z_to_bv 64 (sp0 - 16 - DF)) gp (Z_to_bv 64 RATP) t0 t1 t2 xs0 xs1 ya0 ya1 ya2 a3 a4 a5 a6 a7
                   xs2 xs3 xs4 xs5 xs6 xs7 xs8 s9 s10 s11 t3 t4 t5 t6 F fc m1 st (ae_LB E) lo B rr_guard errv
                   (le_bytes_to_word jx) uw) as T.
    cbv zeta in T. rewrite USP in T. replace (sp0 - 16 - DF + DF) with (sp0 + -16) in T by lia.
    eapply T;
      [ exact HEAP1
      | clear - AL16; replace (sp0 + -16) with (sp0 + 528 + (-34) * 16) by lia; rewrite Z.mod_add by lia; exact AL16
      | exact ST1| exact CEIL'| lia| lia| exact B63
      | eapply rauxv_ok_frame; [exact AUX| exact MU1| exact WM1|]; constructor; [cbn; unfold RAUXV_CELL; lia| constructor]
      | exact MI1| exact RELRO1| exact SSP1| exact XD1| exact HD1| exact MR1| exact EHG1| exact UNW1| exact FRlo| exact FRra| exact XP1| exact XR1
      | unfold errno_addr, RATP; rewrite unsigned_lit by lia; exact ERR| reflexivity ]. }
  cbv beta. intros [] st' ms' PO. unfold site_post in PO. rewrite ?USP in PO.
  destruct PO as (ra' & u0 & u1 & u2 & v0 & v1 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & u3 & u4 & u5 & u6 & F' & m' & errv'
                   & -> & FEQ & MI' & ST' & ERR' & AUX' & HEAP' & FA' & SO' & EHG' & UNW' & SAG).
  replace (sp0 + -16 + 16) with sp0 in * by lia.
  destruct (act_env_site E m0 m m1 m' s00 st st' LB D0 d sp0 lo B errv errv' bvp psb ptp pim pix poc pia A cap IMPL IDX OC IA jr
              j0 jres jos j313 j329 j361 j416 j441 nsi nxt capv md bufv lenv docv b48 b49 p12 p28 p50 s0 s1 s2 s3 s4 s5 s6 s7 s8 ra fc DF ltac:(lia)
              AE MU1 WM1 SAG MI' ST' HEAP' FA' SO' ltac:(unfold errno_addr, RATP in ERR'; rewrite unsigned_lit in ERR' by lia; exact ERR') AUX' EHG' UNW')
    as (AE2 & _ & _).

  pose proof (munch_refl ([] : list (Z * Z)) m') as MU. pose proof (wmono_refl usegs m') as WM.
  unfold implM. iprefix. unfold MallocRep.wz. step.
  ihere. apply HK. unfold EL_EXIT in *.
  eapply act_post_here; [exact AE2| exact FA'| exact SO'].
Qed.

Theorem throw_slot_cast : forall sel, 0 <= sel < 8 -> throw_slot (cast_site sel) (cast_D sel) 0x3c378 (cast_XP sel) xr_none.
Proof.
  intros sel Hs. apply throw_slot_of_site; [unfold cast_D; destruct (sel =? 5); lia|]. unfold cast_site, cast_D, cast_XP.
  assert (C : sel = 0 \/ sel = 1 \/ sel = 2 \/ sel = 3 \/ sel = 4 \/ sel = 5 \/ sel = 6 \/ sel = 7) by lia.
  destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]; cbn [Z.eqb Pos.eqb];
    first [exact throw_site_cast0 | exact throw_site_cast1 | exact throw_site_cast2 | exact throw_site_cast3
          | exact throw_site_cast4 | exact throw_site_cast5 | exact throw_site_cast6 | exact throw_site_cast7].
Qed.
Theorem throw_slot_begin : throw_slot 0x3d968 0 0x3c344 xp_none xr_none.
Proof. apply throw_slot_of_site; [lia|]. exact throw_site_begin. Qed.
Theorem throw_slot_end : throw_slot 0x3f010 64 0x3c3ec xp_end xr_end.
Proof. apply throw_slot_of_site; [lia|]. exact throw_site_end. Qed.
End WithCeiling0.
