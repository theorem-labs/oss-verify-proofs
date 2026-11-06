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
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit F_memcpy Atp_h_defs Atp_h_push Atp_h_find Atp_h_split Atp_h_splitinto Od_empl.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Od_pro.
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

Notation od_els := OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P.Od_pro.od_els.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition pro_post (sp0 : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (lo B D : Z) (d : list Z) (init : bool) (m : mem)
    (v : @vec bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (A cap : Z) (b : bptr) (jr : list byte)
                    (j0 j288 jfd : list byte),
    ms' = MS (mkR x1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 (Z_to_bv 64 (od_action d)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x27180) fc None m' (seg_rom usegs)
    /\ v = (cap, Z.of_nat (od_P d), Some b) /\ cap < 2^26
    /\ mem_inv usegs m' /\ stk usegs m' lo sp0 /\ rw_cells usegs m' LX_ERRNO [C4 errv'] /\ rauxv_ok m' B
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' ((b, A, 16 * cap) :: LB) m'
    /\ vrep m' (sp0 + 344) A v (od_els D d) jr
    /\ lx_pres LB (sp0 + 496) [LXW_SJ] m m' /\ sj_statics m' init /\ payload_ok m' LB D d
    /\ rw_cells usegs m' sp0 [CB 288 j0]
    /\ rw_cells usegs m' (sp0 + 288) [CB 56 j288]
    /\ rw_cells usegs m' (sp0 + 368) [CB 24 jfd]
    /\ rw_cells usegs m' (sp0 + 392) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma rw_cells_split_at1 : forall m A cs n, rw_cells usegs m A cs ->
  rw_cells usegs m A (firstn n cs) /\ rw_cells usegs m (A + Z.of_nat (cells_size (firstn n cs))) (skipn n cs).
Proof. intros m A cs n H. rewrite <- (firstn_skipn n cs) in H. apply Sj_stage1_kit.rw_cells_app in H. exact H. Qed.

Lemma od_junk24 : forall m A (c1 c2 c3 c4 : cell), rw_cells usegs m A [c1; c2; c3; c4] ->
  csize c1 = 8%nat -> csize c2 = 8%nat -> csize c3 = 1%nat -> csize c4 = 7%nat ->
  rw_cells usegs m A [CB 24 (cbytes c1 ++ cbytes c2 ++ cbytes c3 ++ cbytes c4)].
Proof.
  intros m A c1 c2 c3 c4 H E1 E2 E3 E4. pose proof H as H0. destruct H0 as [[Hwf _] _]. cbn [cells_wf] in Hwf. destruct Hwf as (W1 & W2 & W3 & W4 & _).
  eapply rw_cells_recast; [exact H| | |].
  - cbn [cells_wf cell_wf]. rewrite !length_app, !cbytes_length by assumption. split; [lia| exact I].
  - cbn [cells_bytes cbytes]. rewrite ?app_nil_r. reflexivity.
  - cbn [cells_size csize]. lia.
Qed.

Lemma payload_ok_tl : forall m LB D b0 d', payload_ok m LB D (b0 :: d') -> payload_ok m LB (D + 1) d'.
Proof.
  intros m LB D b0 d' (PB & PR & D0 & DN & DL & PIN).
  assert (ZL : zlength (b0 :: d') = zlength d' + 1) by (unfold zlength; cbn [length]; lia).
  split. { change (to_bytes (b0 :: d')) with ([Z_to_bv 8 b0] ++ to_bytes d') in PB. apply bytes_at_app in PB. destruct PB as [_ PB]. cbn [length] in PB. exact PB. }
  split; [inversion PR; assumption|]. split; [lia|]. split; [lia|]. split; [lia|].
  destruct PIN as [E|(b & Hb & H1 & H2)]; [discriminate|]. destruct d' as [|c d'']; [left; reflexivity| right].
  exists b. split; [exact Hb|]. split; lia.
Qed.

Local Ltac norm_addr H v := lazymatch type of H with rw_cells _ _ ?a _ => replace a with v in H by lia end.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma od_pro_tail : forall {R} (k : vec -> M PState R) (Q : R -> PState -> machine_state -> Prop)
      (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra : word)
      (F : bvmap 5 word) (fc : bv 32) (m m2 : mem) (s st2 : PState) (LB : list block) (sp0 lo B D : Z) (d : list Z) (init : bool) (errv2 : word)
      (A2 cap2 : Z) (blk2 : option bptr) (els : list (Z * Z)) (jr2 j0 j288 jfd : list byte),
    RHEAP st2 (vblocks blk2 A2 cap2 ++ LB) m2 -> rauxv_ok m2 B -> sp0 + 496 <= B -> B < 2^63 ->
    stk usegs m2 lo sp0 -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= sp0 - (128 + RMALLOC_STACK) ->
    rw_cells usegs m2 LX_ERRNO [C4 errv2] -> mem_inv usegs m2 -> sp0 mod 16 = 0 ->
    vrep m2 (sp0 + 344) A2 (cap2, zlength els, blk2) els jr2 -> cap2 <= 2 * zlength els -> zlength els < 2^25 -> (blk2 = None <-> els = []) ->
    ps_fa st2 = ps_fa s -> ps_so st2 = ps_so s ->
    lx_pres LB (sp0 + 496) [LXW_SJ] m m2 -> sj_statics m2 init -> payload_ok m2 LB D d ->
    rw_cells usegs m2 sp0 [CB 288 j0] ->
    rw_cells usegs m2 (sp0 + 288) [CB 56 j288] ->
    rw_cells usegs m2 (sp0 + 368) [CB 24 jfd] ->
    rw_cells usegs m2 (sp0 + 392) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    els ++ repeat (0, 0) (Nat.max (length els) 1 - length els) = od_els D d -> Nat.max (length els) 1 = od_P d ->
    (forall v s' ms', pro_post sp0 gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra F fc s LB lo B D d init m v s' ms' -> implM usegs (k v) s' Q ms') ->
    implM usegs (mbind (vpushes lops (Nat.max (length els) 1 - length els) (cap2, zlength els, blk2)) k) st2 Q
      (MS (mkR x1 (Z_to_bv 64 sp0) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 (Z_to_bv 64 (od_action d)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x27168) fc None m2 (seg_rom usegs)).
  Proof.
    intros until jfd. intros HEAP2 AUX2 QB B63 ST2 CEIL GLO LO ERR2 MI2 AL16 VR2 CAPB ELB BN FA2 SO2 PRES2 SJS2 PL2 OUT J288 XFD SAVE EELS EP HK.
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (LO0 : 0 <= lo) by (destruct ST2 as [? _]; assumption).
    unfold GLOBALS_TOP, RMALLOC_STACK in *.
    eapply (od_empl_cps HM HF) with (B := B) (lo := lo);
      [exact HEAP2| exact AUX2| exact QB| exact B63| exact ST2| exact CEIL'| unfold GLOBALS_TOP; lia| unfold RMALLOC_STACK; lia| exact ERR2| exact MI2| exact AL16
      | exact VR2| exact CAPB| exact ELB| exact BN|].
    cbv beta. intros v2 st3 ms3 PO. unfold odempl_post in PO.
    destruct PO as (y1 & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m3 & errv3 & A3 & cap3 & b3 & jr3
                    & -> & Ev2 & CAP3 & MI3 & ST3 & ERR3 & AUX3 & FA3 & SO3 & HEAP3 & VR3 & PRES3).
    subst v2.
    apply HK. unfold pro_post.
    pose proof (agree_of_lx_pres _ _ _ _ _ PRES3) as AG3.
    assert (FRCL3 : forall a, sp0 <= a < sp0 + 496 -> ~ (sp0 + 344 <= a < sp0 + 368) -> lx_client LB sp0 [(sp0 + 344, sp0 + 368)] a).
    { intros a Ha N2. split; [cbn [rin_ivs fst snd]; lia| left; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AG3) in OUT; [| intros a Ha; cbn in Ha; apply FRCL3; lia].
    apply (rw_cells_agree _ _ _ _ _ AG3) in J288; [| intros a Ha; cbn in Ha; apply FRCL3; lia].
    apply (rw_cells_agree _ _ _ _ _ AG3) in XFD; [| intros a Ha; cbn in Ha; apply FRCL3; lia].
    apply (rw_cells_agree _ _ _ _ _ AG3) in SAVE; [| intros a Ha; cbn in Ha; apply FRCL3; lia].
    assert (BLB2 : forall a, in_block LB a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP2 ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & BC & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in BC. lia. }
    assert (BLB3 : forall a, in_block LB a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP3 ltac:(right; exact Hb)) as (_ & _ & _ & BC & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in BC. lia. }
    do 15 eexists. exists m3, errv3, A3, cap3, b3, jr3. exists j0, j288, jfd.
    split; [cbv delta [mkR]; reflexivity|].
    split. { rewrite <- EP. reflexivity. }
    split; [exact CAP3|].
    split; [exact MI3|]. split; [exact ST3|]. split; [exact ERR3|]. split; [exact AUX3|]. split; [congruence|]. split; [congruence|].
    split; [exact HEAP3|].
    split. { rewrite <- EELS. exact VR3. }
    split. { eapply lx_pres_trans; [exact PRES2|]. eapply (lx_pres_sub LB (sp0 + 496) _ _ _ _ _ _ PRES3); [lia| intros b0 Hb0; exact Hb0|].
             intros a Ha NX. cbn [rin_ivs fst snd] in Ha. split; [lia|]. split; [intros IB; specialize (BLB3 a IB); lia| lia]. }
    split. { eapply sj_statics_agree; [exact AG3| | exact SJS2]. intros a Ha. apply sjs_addr_client; [exact Ha|].
             unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. cbn [rin_ivs fst snd]. clear - Ha GLO LO. lia. }
    split. { eapply payload_ok_agree; [exact AG3| exact PL2|]. intros b a Hb Ha. pose proof (LH_block_range _ _ _ _ HEAP2 ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & BC & _).
             unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in BC. split; [cbn [rin_ivs fst snd]; clear - Ha BC CEIL LO; lia| right; left; exists b; split; [exact Hb| exact Ha]]. }
    split; [exact OUT|]. split; [exact J288|]. split; [exact XFD| exact SAVE].
  Qed.
  Lemma od_pro_cps : forall {R} (k : vec -> M PState R) (Q : R -> PState -> machine_state -> Prop)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem)
      (s : PState) (LB : list block) (D : Z) (d : list Z) (init : bool) (lo B : Z) (errv canary : word),
    RHEAP s LB m -> lx_statics m -> sj_statics m init -> stderr_wfile m -> ssp_cells m canary ->
    rauxv_ok m B -> bv_unsigned sp <= B -> B < 2^63 ->
    stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - LX_FUZZ_STACK ->
    rw_cells usegs m (errno_addr tp) [C4 errv] -> tp = wz RATP ->
    mem_inv usegs m ->
    bv_unsigned sp mod 16 = 0 ->
    payload_ok m LB D d ->
    frm0 fc ->
    a0 = wz D -> a1 = wz (zlength d) ->
    (forall v s' ms', pro_post (bv_unsigned sp - 496) gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra F fc s LB lo B D d init m v s' ms' -> implM usegs (k v) s' Q ms') ->
    implM usegs (mbind (vpushes lops (od_P d) vec0) k) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz LX_FUZZ) fc None m (seg_rom usegs)).
  Proof.
    intros until canary.
    intros HEAP LXS SJS SEW SSP AUX SPB B63 ST CEIL GLO LO ERR TP MI AL16 PL FRM -> -> HK.
    unfold LX_FUZZ, LX_FUZZ_STACK, SJ_CLIENT_FRAMES, RMALLOC_STACK, GLOBALS_TOP in *. unfold MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (ESP : sp = Z_to_bv 64 (bv_unsigned sp)) by (symmetry; apply Z_to_bv_bv_unsigned).
    set (usp := bv_unsigned sp) in *.
    pose proof CEIL as CEIL'. unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    subst tp. replace (errno_addr (Z_to_bv 64 RATP)) with 609404 in ERR by (unfold errno_addr, RATP; rewrite unsigned_lit by lia; reflexivity).
    pose proof PL as (PB & PRNG & D0 & DN & DLEN & PIN).
    assert (ZD : zlength d = Z.of_nat (length d)) by reflexivity. pose proof DLEN as DLEN'. change (2^26) with 67108864 in DLEN'.
    assert (LBL : length (to_bytes d) = length d) by apply to_bytes_length.
    assert (BLB : forall a, in_block LB a -> a < alloc_ceiling).
    { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & BC & _).
      unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in BC. lia. }
    assert (CLI : forall a, 0 <= a < 2^64 -> lx_client LB usp [LXW_SJ] a -> outside [(usp - 560, usp)] a).
    { intros a Ha [HX HC]. cbn [outside]. split; [| exact I]. destruct HC as [HC|[HC|HC]]; [lia| specialize (BLB a HC); lia| lia]. }
    pose proof (munch_refl [(usp - 560, usp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    rewrite ESP. unfold implM. iprefix.
    step. carve_frame 496%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 496 junk [] [288; 56; 8;8;8; 8;8;1;7; 8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity].
    cbn [mk_CB_cells app] in FR.

    clear PB. do 13 step. hstep.
    destruct d as [|b0 d'].
    -
      change (zlength (@nil Z)) with 0 in *.

      step. if_true. step. hstep. hstep. step. step. step.

      step. carve_frame 64%nat ST.
      apply (rw_cells_split_CB usegs _ _ [] 64 junk0 [] [32; 8;8;8;8]%nat) in FR0; [|reflexivity]. cbn [mk_CB_cells app] in FR0.
      hstep. step. step. step.
      step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
      step. step. step. hstep. hstep. hstep. step. if_true.
      step. step. step. step. step. release_frame FR0 ST (usp + -496). step.
      replace (ret_pc (Z_to_bv 64 0x27168)) with (Z_to_bv 64 0x27168) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.

      destruct (rw_cells_split_at1 _ _ _ 1%nat FR) as [OUT R1]. cbn [firstn skipn cells_size csize Nat.add] in OUT, R1.
      destruct (rw_cells_split_at1 _ _ _ 1%nat R1) as [J288 R2]. cbn [firstn skipn cells_size csize Nat.add] in J288, R2.
      destruct (rw_cells_split_at1 _ _ _ 3%nat R2) as [XRV R3]. cbn [firstn skipn cells_size csize Nat.add] in XRV, R3.
      destruct (rw_cells_split_at1 _ _ _ 4%nat R3) as [XFD SAVE]. cbn [firstn skipn cells_size csize Nat.add] in XFD, SAVE.
      clear FR R1 R2 R3.
      remember (usp + -496) as sp0 eqn:Esp0.
      norm_addr J288 (sp0 + 288). norm_addr XRV (sp0 + 344). norm_addr XFD (sp0 + 368). norm_addr SAVE (sp0 + 392).
      apply od_junk24 in XFD; [| reflexivity| reflexivity| reflexivity| reflexivity].
      assert (SPQ : sp0 + 496 = usp) by lia.
      assert (HEAP1 : RHEAP s LB m1).
      { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      assert (AUX1 : rauxv_ok m1 B).
      { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (PRES1 : lx_pres LB usp [LXW_SJ] m m1) by (eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]).
      assert (SJS1 : sj_statics m1 init).
      { eapply sj_statics_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact SJS]. intros a Ha. unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha.
        cbn [outside]; split; [lia| exact I]. }
      assert (PL1 : payload_ok m1 LB D []).
      { eapply payload_ok_agree; [exact (agree_of_lx_pres _ _ _ _ _ PRES1)| exact PL|]. intros b a Hb Ha. split; [| right; left; exists b; split; assumption].
        pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & _ & BS). unfold LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha BS. lia. }
      pose proof ST as ST1.
      clear MU WM.
      ihere. to_implM.
      change (od_P []) with (Nat.max (length (@nil (Z * Z))) 1 - length (@nil (Z * Z)))%nat.
      change (@vec0 bptr) with (0, zlength (@nil (Z * Z)), @None bptr).
      replace (Z_to_bv 64 0) with (Z_to_bv 64 (od_action [])) by reflexivity.
      eapply (od_pro_tail k Q) with (B := B) (lo := lo) (m := m) (s := s) (D := D) (d := []) (init := init) (A2 := 0) (cap2 := 0) (blk2 := None) (els := []) (jr2 := []);
        [exact HEAP1| exact AUX1| lia| exact B63| exact ST1| exact CEIL'| unfold GLOBALS_TOP; lia| unfold RMALLOC_STACK; lia| eassumption| assumption
        | subst sp0; clear - AL16; replace (usp + -496) with (usp + (-31) * 16) by lia; rewrite Z.mod_add by lia; exact AL16
        | | unfold zlength; cbn [length]; lia| reflexivity| split; reflexivity| reflexivity| reflexivity| rewrite SPQ; exact PRES1| exact SJS1| exact PL1| exact OUT| exact J288| exact XFD| exact SAVE| reflexivity| reflexivity| replace (usp - 496) with sp0 in HK by lia; exact HK].
      split; [reflexivity|]. split; [unfold zlength; cbn [length]; lia|]. split; [exact XRV|]. split; reflexivity.
    -
      assert (ZL : zlength (b0 :: d') = zlength d' + 1) by (unfold zlength; cbn [length]; lia).
      assert (ZL0 : 0 <= zlength d') by (unfold zlength; lia).
      assert (R0 : 0 <= b0 < 256) by (inversion PRNG; assumption).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0a end.
      assert (PL0 : payload_ok m0a LB D (b0 :: d')).
      { eapply payload_ok_agree; [exact (agree_of_lx_pres _ _ _ _ _ (lx_pres_of_munch _ _ _ _ _ _ MU WM CLI))| exact PL|]. intros b a Hb Ha. split; [| right; left; exists b; split; assumption].
        pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & _ & BS). unfold LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha BS. lia. }
      destruct PL0 as (PB0 & _).
      pose proof (u8ro_read usegs m0a D _ 0 _ (wa (D + 0)) PB0 eq_refl ltac:(lia) eq_refl) as RD0. clear PB0.

      step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K].
      step. step. if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; lia].

      replace (Z_to_bv 64 D) with (Z_to_bv 64 (D + 0)) by (f_equal; lia).
      step. rewrite (Sj_stage1_kit.zxb_small b0) by lia.
      zstep. zstep. step. step. zstep. zstep. step. zstep. zstep. zstep. step.
      rewrite (OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P.Od_pro.od_action_arith b0 R0). replace (zlength (b0 :: d') + -1) with (zlength d') by lia.

      step. step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      clear RD0.
      destruct (rw_cells_split_at1 _ _ _ 1%nat FR) as [OUT R1]. cbn [firstn skipn cells_size csize Nat.add] in OUT, R1.
      destruct (rw_cells_split_at1 _ _ _ 1%nat R1) as [J288 R2]. cbn [firstn skipn cells_size csize Nat.add] in J288, R2.
      destruct (rw_cells_split_at1 _ _ _ 3%nat R2) as [XRV R3]. cbn [firstn skipn cells_size csize Nat.add] in XRV, R3.
      destruct (rw_cells_split_at1 _ _ _ 2%nat R3) as [XFD R4]. cbn [firstn skipn cells_size csize Nat.add] in XFD, R4.
      destruct (rw_cells_split_at1 _ _ _ 2%nat R4) as [XFC SAVE]. cbn [firstn skipn cells_size csize Nat.add] in XFC, SAVE.
      clear FR R1 R2 R3 R4.
      remember (usp + -496) as sp0 eqn:Esp0.
      replace (usp + -152) with (sp0 + 344) by lia. replace (usp + -128) with (sp0 + 368) by lia.
      norm_addr J288 (sp0 + 288). norm_addr XRV (sp0 + 344). norm_addr XFD (sp0 + 368). norm_addr XFC (sp0 + 384). norm_addr SAVE (sp0 + 392).
      assert (SPQ : sp0 + 496 = usp) by lia.
      assert (HEAP1 : RHEAP s LB m1).
      { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
      assert (AUX1 : rauxv_ok m1 B).
      { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
      assert (PRES1 : lx_pres LB usp [LXW_SJ] m m1) by (eapply lx_pres_of_munch; [exact MU| exact WM| exact CLI]).
      assert (SJS1 : sj_statics m1 init).
      { eapply sj_statics_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact SJS]. intros a Ha. unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha.
        cbn [outside]; split; [lia| exact I]. }
      assert (PL1 : payload_ok m1 LB D (b0 :: d')).
      { eapply payload_ok_agree; [exact (agree_of_lx_pres _ _ _ _ _ PRES1)| exact PL|]. intros b a Hb Ha. split; [| right; left; exists b; split; assumption].
        pose proof (LH_block_range _ _ _ _ HEAP Hb) as (_ & _ & _ & _ & BS). unfold LXW_SJ, SJ_STATICS_LO, SJ_STATICS_HI. cbn [rin_ivs fst snd]. clear - Ha BS. lia. }
      pose proof (payload_ok_tl _ _ _ _ _ PL1) as PLT.
      clear MU WM.

      ihere. to_implM.
      assert (EPD : od_P (b0 :: d') = Nat.max (length (atp_parts d')) 1) by reflexivity.
      replace (od_P (b0 :: d')) with (length (atp_parts d') + (Nat.max (length (atp_parts d')) 1 - length (atp_parts d')))%nat by (rewrite EPD; lia).
      apply implM_vpushes_split.
      eapply implM_bind.
      { eapply (splitinto_spec HM HF) with (B := B) (lo := lo) (D := D + 1) (d := d');
          [exact HEAP1| exact AUX1| lia| exact B63| eassumption| exact CEIL'| unfold GLOBALS_TOP; lia| unfold RMALLOC_STACK; lia| eassumption| assumption
          | lia| lia| lia| subst sp0; clear - AL16; replace (usp + -496) with (usp + (-31) * 16) by lia; rewrite Z.mod_add by lia; exact AL16| exact PLT| exact XRV| exact XFD]. }
      cbv beta. intros v1 st1 ms1 PO. unfold splitinto_post in PO.
      destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m2 & errv2 & A2 & cap2 & blk2 & jr2
                      & -> & Ev1 & BNIL & Ecap2 & MI2 & ST2 & ERR2 & AUX2 & FA2 & SO2 & HEAP2 & VR2 & XFD2 & PRES2).
      replace (ret_pc (Z_to_bv 64 0x27168)) with (Z_to_bv 64 0x27168) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      subst v1.
      pose proof (agree_of_lx_pres _ _ _ _ _ PRES2) as AG2.
      assert (FRCL : forall a, sp0 <= a < sp0 + 496 -> ~ (sp0 + 344 <= a < sp0 + 368) -> ~ (sp0 + 368 <= a < sp0 + 384) -> lx_client LB sp0 [(sp0 + 344, sp0 + 344 + 24); (sp0 + 368, sp0 + 368 + 16)] a).
      { intros a Ha N1 N2. split; [cbn [rin_ivs fst snd]; lia| left; lia]. }
      apply (rw_cells_agree _ _ _ _ _ AG2) in OUT; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in J288; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in XFC; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      apply (rw_cells_agree _ _ _ _ _ AG2) in SAVE; [| intros a Ha; cbn in Ha; apply FRCL; lia].
      assert (SJS2 : sj_statics m2 init).
      { eapply sj_statics_agree; [exact AG2| | exact SJS1]. intros a Ha. apply sjs_addr_client; [exact Ha|].
        unfold sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in Ha. cbn [rin_ivs fst snd]. clear - Ha GLO LO SPQ. lia. }
      assert (BLB2 : forall a, in_block LB a -> a < alloc_ceiling).
      { intros a (b & Hb & Hr). pose proof (LH_block_range _ _ _ _ HEAP2 ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & BC & _).
        unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in BC. lia. }
      assert (PRES2' : lx_pres LB usp [LXW_SJ] m m2).
      { eapply lx_pres_trans; [exact PRES1|]. eapply (lx_pres_sub LB usp _ _ _ _ _ _ PRES2); [lia| intros b1 Hb1; exact Hb1|].
        intros a Ha NX. cbn [rin_ivs fst snd] in Ha. split; [lia|]. split; [intros IB; specialize (BLB2 a IB); lia| lia]. }
      assert (PL2 : payload_ok m2 LB D (b0 :: d')).
      { eapply payload_ok_agree; [exact AG2| exact PL1|]. intros b a Hb Ha. pose proof (LH_block_range _ _ _ _ HEAP1 Hb) as (_ & _ & _ & BC & _).
        unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec.Malloc.MCEIL in BC. split; [cbn [rin_ivs fst snd]; clear - Ha BC CEIL LO SPQ; lia| right; left; exists b; split; [exact Hb| exact Ha]]. }
      assert (XFD3 : exists jfd, rw_cells usegs m2 (sp0 + 368) [CB 24 jfd]).
      { eexists. eapply od_junk24; [eapply (rw_cells_join _ _ _ _ _ XFD2 XFC); cbn [cells_size csize Nat.add]; lia| reflexivity| reflexivity| reflexivity| reflexivity]. }
      destruct XFD3 as (jfd & XFD3).
      clear AG2 PRES2 PRES1 HEAP1 AUX1 SJS1 PL1 XRV XFD XFD2 XFC PLT.
      pose proof (od_P_bound (b0 :: d')) as PBD. rewrite EPD in PBD. rewrite <- (poffs_length d') in *.
      assert (ELEN : length (map (pview (D + 1)) (poffs d')) = length (poffs d')) by apply length_map.
      rewrite <- ELEN in *. replace (zlength (poffs d')) with (zlength (map (pview (D + 1)) (poffs d'))) in * by (unfold zlength; rewrite ELEN; reflexivity).
      eapply (od_pro_tail k Q) with (B := B) (lo := lo) (m := m) (s := s) (D := D) (d := b0 :: d') (init := init);
        [exact HEAP2| exact AUX2| lia| exact B63| exact ST2| exact CEIL'| unfold GLOBALS_TOP; lia| unfold RMALLOC_STACK; lia| eassumption| assumption
        | subst sp0; clear - AL16; replace (usp + -496) with (usp + (-31) * 16) by lia; rewrite Z.mod_add by lia; exact AL16
        | exact VR2| exact Ecap2| unfold zlength; change (2^25) with 33554432; cbn [length] in PBD; clear - PBD DLEN' ZD; unfold zlength in *; cbn [length] in *; lia
        | | congruence| congruence| rewrite SPQ; exact PRES2'| exact SJS2| exact PL2| exact OUT| exact J288| exact XFD3| exact SAVE| | | replace (usp - 496) with sp0 in HK by lia; exact HK].
      + rewrite <- BNIL. split; [intros ->; reflexivity| intros E; destruct d' as [|z l]; [reflexivity| exfalso]].
        rewrite poffs_eq in E. apply (f_equal (@length _)) in E. rewrite length_map in E. pose proof (poffs_of_nonnil 0 (z :: l)). destruct (poffs_of 0 (z :: l)); [congruence| discriminate].
      + unfold OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P.Od_pro.od_els. cbn [tl]. rewrite EPD, ELEN. reflexivity.
      + rewrite EPD. reflexivity.
  Qed.
End Proofs.
End WithCeiling0.
