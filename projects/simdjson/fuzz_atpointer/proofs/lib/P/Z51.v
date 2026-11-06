(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Image Z11w Z119 ITree Nodes Decode Arr FP MonadX Z10q.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Malloc Require Import Zei Zf6.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.MallocP Require Import Zhy Zhz Zi1.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim StrFun STree Malloc Monad Stdio Zpb Z3o Target Prog AtpImpl.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Layout Exit Zfr Zq5 Sj_kit Sj_new Zq6 Zpu Z9n Z4d Z4r Z4j Z4u Z4w Z4g.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Zvw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition atp_els (D : Z) (d : list Z) : list (Z * Z) :=
  map (pview D) (poffs d) ++ repeat (0, 0) (atp_P d - length (poffs d)).

Definition vec_post (sp0 : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (lo B D : Z) (d : list Z) (init : bool) (m : mem)
    (v : @vec bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 xs0 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 t3 t4 t5 t6 m' (errv' : word) (A cap : Z) (b : bptr) (jr : list byte)
                    (jo c48 c56 c64 c72 c80 j88 jr0 jr8 jr16 jr20 j169 jn : list byte),
    ms' = MS (mkR x1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) t0 t1 t2 xs0 (Z_to_bv 64 (sp0 + 128)) (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x27284) fc None m' (seg_rom psegs)
    /\ v = (cap, Z.of_nat (atp_P d), Some b) /\ cap < 2^26
    /\ mem_inv psegs m' /\ stk psegs m' lo sp0 /\ rw_cells psegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' ((b, A, 16 * cap) :: LB) m'
    /\ vrep m' (sp0 + 128) A v (atp_els D d) jr
    /\ lx_pres LB (sp0 + 256) [LXW_SJ] m m' /\ sj_statics m' init /\ payload_ok m' LB D d
    /\ rw_cells psegs m' sp0 [CB 24 jo]
    /\ rw_cells psegs m' (sp0 + 24) [CB 8 jr0; CB 8 jr8; CB 4 jr16; CB 4 jr20]
    /\ rw_cells psegs m' (sp0 + 48) [CB 8 c48; CB 8 c56; CB 8 c64; CB 8 c72; CB 8 c80; CB 40 j88]
    /\ rw_cells psegs m' (sp0 + 152) [C8 (Z_to_bv 64 (D + zlength d)); C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 7 j169]
    /\ rw_cells psegs m' (sp0 + 176) [CB 16 jn]
    /\ rw_cells psegs m' (sp0 + 192) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma rw_cells_split_at1 : forall m A cs n, rw_cells psegs m A cs ->
  rw_cells psegs m A (firstn n cs) /\ rw_cells psegs m (A + Z.of_nat (cells_size (firstn n cs))) (skipn n cs).
Proof. intros m A cs n H. rewrite <- (firstn_skipn n cs) in H. apply Zvw.rw_cells_app in H. exact H. Qed.

Lemma atp_els_length : forall D d, length (atp_els D d) = atp_P d.
Proof.
  intros D d. unfold atp_els, atp_P. rewrite length_app, length_map, repeat_length, poffs_length. lia.
Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma lftoi_vec_cps : forall {R} (k : vec -> M PState R) (Q : R -> PState -> machine_state -> Prop)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem)
      (s : PState) (LB : list block) (D : Z) (d : list Z) (init : bool) (lo B : Z) (errv canary : word),
    RHEAP s LB m -> lx_statics m -> sj_statics m init -> stderr_wfile m -> ssp_cells m canary ->
    rauxv_ok m B -> bv_unsigned sp <= B -> B < 2^63 ->
    stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - LX_FUZZ_STACK ->
    rw_cells psegs m (errno_addr tp) [C4 errv] -> tp = wz RATP ->
    mem_inv psegs m ->
    bv_unsigned sp mod 16 = 0 ->
    payload_ok m LB D d ->
    frm0 fc ->
    a0 = wz D -> a1 = wz (zlength d) ->
    (forall v s' ms', vec_post (bv_unsigned sp - 256) gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra F fc s LB lo B D d init m v s' ms' -> implM psegs (k v) s' Q ms') ->
    implM psegs (mbind (vpushes lops (atp_P d) vec0) k) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz LX_FUZZ) fc None m (seg_rom psegs)).
  Proof.
    intros until canary.
    intros HEAP LXS SJS SEW SSP AUX SPB B63 ST CEIL GLO LO ERR TP MI AL16 PL FRM -> -> HK.
    unfold LX_FUZZ, LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP in *. unfold Zf2.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (ESP : sp = Z_to_bv 64 (bv_unsigned sp)) by (symmetry; apply Z_to_bv_bv_unsigned).
    set (usp := bv_unsigned sp) in *.
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    subst tp. replace (errno_addr (Z_to_bv 64 RATP)) with 563116 in ERR by (unfold errno_addr, RATP; rewrite unsigned_lit by lia; reflexivity).
    pose proof PL as (PB & PRNG & D0 & DN & DLEN & PIN).
    assert (ZD : zlength d = Z.of_nat (length d)) by reflexivity. pose proof DLEN as DLEN'. change (2^26) with 67108864 in DLEN'.
    assert (LBL : length (to_bytes d) = length d) by apply to_bytes_length.
    assert (BLB : forall a, in_block LB a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & BC & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in BC. lia. }
    assert (DR : d = [] \/ D + zlength d <= alloc_ceiling).
    { destruct PIN as [E0|(b0 & Hb & Hb1 & Hb2)]; [left; exact E0| right]. pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & R4 & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in R4. lia. }
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client LB usp [LXW_SJ] a -> outside [(usp - 256, usp)] a).
    { intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    pose proof (munch_refl [(usp - 256, usp)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
    rewrite ESP. unfold implM. iprefix.
    step. carve_frame 256%nat ST.
    apply (rw_cells_split_CB psegs _ _ [] 256 junk [] [24; 8;8;4;4; 8;8;8;8;8; 40; 8;8;8; 8;8;1;7; 16; 8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.

    clear PB. do 8 step. step. step. hstep. step. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.

    destruct (rw_cells_split_at1 _ _ _ 1%nat FR) as [OUT R1]. cbn [firstn skipn cells_size csize Nat.add] in OUT, R1.
    destruct (rw_cells_split_at1 _ _ _ 4%nat R1) as [RES R2]. cbn [firstn skipn cells_size csize Nat.add] in RES, R2.
    destruct (rw_cells_split_at1 _ _ _ 5%nat R2) as [SCR R3]. cbn [firstn skipn cells_size csize Nat.add] in SCR, R3.
    destruct (rw_cells_split_at1 _ _ _ 1%nat R3) as [P88 R4]. cbn [firstn skipn cells_size csize Nat.add] in P88, R4.
    destruct (rw_cells_split_at1 _ _ _ 3%nat R4) as [XRV R5]. cbn [firstn skipn cells_size csize Nat.add] in XRV, R5.
    destruct (rw_cells_split_at1 _ _ _ 2%nat R5) as [XFD R6]. cbn [firstn skipn cells_size csize Nat.add] in XFD, R6.
    destruct (rw_cells_split_at1 _ _ _ 2%nat R6) as [XFC R7]. cbn [firstn skipn cells_size csize Nat.add] in XFC, R7.
    destruct (rw_cells_split_at1 _ _ _ 1%nat R7) as [ROOT SAVE]. cbn [firstn skipn cells_size csize Nat.add] in ROOT, SAVE.
    clear FR R1 R2 R3 R4 R5 R6 R7.

    remember (usp + -256) as sp0 eqn:Esp0.
    replace (usp + -128) with (sp0 + 128) by lia. replace (usp + -104) with (sp0 + 152) by lia.
    replace (sp0 + Z.of_nat 24) with (sp0 + 24) in RES by lia.
    replace (sp0 + Z.of_nat 24 + Z.of_nat 24) with (sp0 + 48) in SCR by lia.
    replace (sp0 + Z.of_nat 24 + Z.of_nat 24 + Z.of_nat 40) with (sp0 + 88) in P88 by lia.
    replace (sp0 + Z.of_nat 24 + Z.of_nat 24 + Z.of_nat 40 + Z.of_nat 40) with (sp0 + 128) in XRV by lia.
    replace (sp0 + Z.of_nat 24 + Z.of_nat 24 + Z.of_nat 40 + Z.of_nat 40 + Z.of_nat 24) with (sp0 + 152) in XFD by lia.
    replace (sp0 + Z.of_nat 24 + Z.of_nat 24 + Z.of_nat 40 + Z.of_nat 40 + Z.of_nat 24 + Z.of_nat 16) with (sp0 + 168) in XFC by lia.
    replace (sp0 + Z.of_nat 24 + Z.of_nat 24 + Z.of_nat 40 + Z.of_nat 40 + Z.of_nat 24 + Z.of_nat 16 + Z.of_nat 8) with (sp0 + 176) in ROOT by lia.
    replace (sp0 + Z.of_nat 24 + Z.of_nat 24 + Z.of_nat 40 + Z.of_nat 40 + Z.of_nat 24 + Z.of_nat 16 + Z.of_nat 8 + Z.of_nat 16) with (sp0 + 192) in SAVE by lia.
    assert (SPQ : sp0 + 256 = usp) by lia.
    assert (HEAP1 : RHEAP s LB m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
    assert (PRES1 : lx_pres LB usp [LXW_SJ] m m1) by (eapply lx_pres_of_munch; [exact MU| exact WM| subst sp0; exact CLI]).
    assert (SJS1 : sj_statics m1 init).
    { eapply sj_statics_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact SJS]. intros a Ha. unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha.
      cbn [outside]; split; [lia| exact I]. }
    assert (PL1 : payload_ok m1 LB D d).
    { eapply payload_ok_agree; [exact (agree_of_lx_pres _ _ _ _ _ PRES1)| exact PL|]. intros b a Hb Ha. split; [| right; left; exists b; split; assumption].
      pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & _ & BS). unfold LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha BS. lia. }
    clear MU WM.

    ihere. to_implM.
    replace (atp_P d) with (length (atp_parts d) + (Nat.max (length (atp_parts d)) 2 - length (atp_parts d)))%nat by (unfold atp_P; lia).
    apply implM_vpushes_split.
    eapply implM_bind.
    { eapply (splitinto_spec HM HF) with (B := B) (lo := lo);
        [exact HEAP1| exact AUX1| lia| exact B63| exact ST| exact CEIL'| unfold GLOBALS_TOP; lia| unfold RMALLOC_STACK; lia| eassumption| assumption
        | lia| lia| lia| exact PL1| exact XRV| exact XFD]. }
    cbv beta. intros v1 st1 ms1 PO. unfold splitinto_post in PO.
    destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & errv2 & A2 & cap2 & blk2 & jr2
                    & -> & Ev1 & BNIL & Ecap2 & MI2 & ST2 & ERR2 & AUX2 & FA2 & SO2 & HEAP2 & VR2 & XFD2 & PRES2).
    replace (ret_pc (Z_to_bv 64 0x271a4)) with (Z_to_bv 64 0x271a4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    subst v1.

    pose proof (agree_of_lx_pres _ _ _ _ _ PRES2) as AG2.
    assert (FRCL : forall a, sp0 <= a < sp0 + 256 -> ~ (sp0 + 128 <= a < sp0 + 152) -> ~ (sp0 + 152 <= a < sp0 + 168) -> lx_client LB sp0 [(sp0 + 128, sp0 + 128 + 24); (sp0 + 152, sp0 + 152 + 16)] a).
    { intros a Ha N1 N2. split; [cbn [rin_ivs fst snd]; lia| left; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AG2) in OUT; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in RES; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in SCR; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in P88; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in XFC; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in ROOT; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in SAVE; [| intros a Ha; cbn in Ha; apply FRCL; lia].
    assert (SJS2 : sj_statics m2 init).
    { eapply sj_statics_agree; [exact AG2| | exact SJS1]. intros a Ha. apply sjs_addr_client; [exact Ha|].
      unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. cbn [rin_ivs fst snd]. clear - Ha GLO LO SPQ. lia. }
    assert (BLB2 : forall a, in_block LB a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP2 ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & BC & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in BC. lia. }
    assert (PRES2' : lx_pres LB usp [LXW_SJ] m m2).
    { eapply lx_pres_trans; [exact PRES1|]. eapply (lx_pres_sub LB usp _ _ _ _ _ _ PRES2); [lia| intros b0 Hb0; exact Hb0|].
      intros a Ha NX. cbn [rin_ivs fst snd] in Ha. split; [lia|]. split; [intros IB; specialize (BLB2 a IB); lia| lia]. }
    assert (PL2 : payload_ok m2 LB D d).
    { eapply payload_ok_agree; [exact AG2| exact PL1|]. intros b a Hb Ha. pose proof (LH_block_range _ _ _ _ HEAP1 Hb) as (_ & _ & _ & BC & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in BC. split; [cbn [rin_ivs fst snd]; clear - Ha BC CEIL LO SPQ; lia| right; left; exists b; split; [exact Hb| exact Ha]]. }
    clear AG2 PRES2 PRES1 HEAP1 AUX1 SJS1 PL1 XRV XFD.

    pose proof (atp_P_bound d) as PBD. unfold atp_P in PBD. rewrite <- (poffs_length d) in *.
    assert (ELEN : length (map (pview D) (poffs d)) = length (poffs d)) by apply length_map.
    rewrite <- ELEN. replace (zlength (poffs d)) with (zlength (map (pview D) (poffs d))) in * by (unfold zlength; rewrite ELEN; reflexivity).
    eapply (empl_cps HM HF) with (B := B) (lo := lo);
      [exact HEAP2| exact AUX2| lia| exact B63| exact ST2| exact CEIL'| unfold GLOBALS_TOP; lia| unfold RMALLOC_STACK; lia| eassumption| assumption| subst sp0; clear - AL16;
        replace (usp + -256) with (usp + (-16) * 16) by lia; rewrite Z.mod_add by lia; exact AL16
      | exact VR2| exact Ecap2| unfold zlength; rewrite ELEN; clear - PBD DLEN' ZD; lia| | reflexivity| exact SCR|].
    { rewrite <- BNIL. split; [intros ->; reflexivity| intros E; destruct d as [|z l]; [reflexivity| exfalso]].
      rewrite poffs_eq in E. apply (f_equal (@length _)) in E. rewrite length_map in E. pose proof (poffs_of_nonnil 0 (z :: l)). destruct (poffs_of 0 (z :: l)); [congruence| discriminate]. }
    cbv beta. intros v2 st2 ms2 PO. unfold empl_post in PO.
    destruct PO as (y1 & y5 & y6 & y7 & y8 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y20 & y21 & y22 & y28 & y29 & y30 & y31 & m3 & errv3 & A3 & cap3 & b3 & jr3
                    & c48 & c56 & c64 & c72 & c80 & -> & Ev2 & CAP3 & MI3 & ST3 & ERR3 & AUX3 & FA3 & SO3 & HEAP3 & VR3 & SCR3 & PRES3).
    subst v2.
    apply HK. unfold vec_post.
    pose proof (agree_of_lx_pres _ _ _ _ _ PRES3) as AG3.
    assert (FRCL3 : forall a, sp0 <= a < sp0 + 256 -> ~ (sp0 + 48 <= a < sp0 + 88) -> ~ (sp0 + 128 <= a < sp0 + 152) -> lx_client LB sp0 [(sp0 + 48, sp0 + 88); (sp0 + 128, sp0 + 152)] a).
    { intros a Ha N1 N2. split; [cbn [rin_ivs fst snd]; lia| left; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AG3) in OUT; [| intros a Ha; cbn in Ha; apply FRCL3; lia].
    apply (rw_cells_agree _ _ _ _ _ AG3) in RES; [| intros a Ha; cbn in Ha; apply FRCL3; lia].
    apply (rw_cells_agree _ _ _ _ _ AG3) in P88; [| intros a Ha; cbn in Ha; apply FRCL3; lia].
    apply (rw_cells_agree _ _ _ _ _ AG3) in XFD2; [| intros a Ha; cbn in Ha; apply FRCL3; lia].
    apply (rw_cells_agree _ _ _ _ _ AG3) in XFC; [| intros a Ha; cbn in Ha; apply FRCL3; lia].
    apply (rw_cells_agree _ _ _ _ _ AG3) in ROOT; [| intros a Ha; cbn in Ha; apply FRCL3; lia].
    apply (rw_cells_agree _ _ _ _ _ AG3) in SAVE; [| intros a Ha; cbn in Ha; apply FRCL3; lia].
    assert (BLB3 : forall a, in_block LB a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP3 ltac:(right; exact Hb)) as (_ & _ & _ & BC & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in BC. lia. }
    do 21 eexists. exists m3, errv3, A3, cap3, b3, jr3. do 13 eexists.
    split; [cbv delta [mkR]; reflexivity|].
    split. { f_equal. f_equal. unfold atp_P. rewrite <- poffs_length, <- ELEN. reflexivity. }
    split; [exact CAP3|].
    split; [exact MI3|]. split; [exact ST3|]. split; [exact ERR3|]. split; [exact AUX3|]. split; [congruence|]. split; [congruence|].
    split; [exact HEAP3|].
    split. { unfold atp_els. unfold atp_P. rewrite <- poffs_length, <- ELEN.
             replace (Z.of_nat (Nat.max (length (map (pview D) (poffs d))) 2)) with (Z.of_nat (Nat.max (length (map (pview D) (poffs d))) 2)) by reflexivity. exact VR3. }
    split. { rewrite SPQ. eapply lx_pres_trans; [exact PRES2'|]. eapply (lx_pres_sub LB usp _ _ _ _ _ _ PRES3); [lia| intros b0 Hb0; exact Hb0|].
             intros a Ha NX. cbn [rin_ivs fst snd] in Ha. split; [lia|]. split; [intros IB; specialize (BLB3 a IB); lia| lia]. }
    split. { eapply sj_statics_agree; [exact AG3| | exact SJS2]. intros a Ha. apply sjs_addr_client; [exact Ha|].
             unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. cbn [rin_ivs fst snd]. clear - Ha GLO LO SPQ. lia. }
    split. { eapply payload_ok_agree; [exact AG3| exact PL2|]. intros b a Hb Ha. pose proof (LH_block_range _ _ _ _ HEAP2 ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & BC & _).
             unfold OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec.Malloc.MCEIL in BC. split; [cbn [rin_ivs fst snd]; clear - Ha BC CEIL LO SPQ; lia| right; left; exists b; split; [exact Hb| exact Ha]]. }
    split; [exact OUT|]. split; [exact RES|].
    split. { eapply (rw_cells_join _ _ _ _ _ SCR3 P88). cbn [cells_size csize Nat.add]. lia. }
    split. { eapply (rw_cells_join _ _ _ _ _ XFD2 XFC). cbn [cells_size csize Nat.add]. lia. }
    split; [exact ROOT| exact SAVE].
  Qed.
End Proofs.
End WithCeiling0.
