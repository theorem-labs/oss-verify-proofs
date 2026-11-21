(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge SysStep Arr Ceiling.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prelim Stdio Prog ZTarget Target ZApi ZHarness ZInst.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Monad.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Rnd Z_kit Startup_glue.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Layout Drv_kit F_fwrite Zlib_iface Zh_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_irep Z_ikit Z_ukit Z_iend.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState RefInflateSafeD RefInflateSafeTY ZApiInst ZTaintI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
#[local] Transparent the_zapi.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation za := the_zapi.

(* [comment removed for export] *)
Definition inflateEnd_postX (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (S : Z) (ni ai ti no ao to : Z) (p1 p2 : list byte) (lo B : Z) (canary : word) (m : mem)
    (r : unit) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom usegs)
    /\ lx_post_env m m' s s' [] LB sp tp B lo canary [(S, S + ZS_SIZEOF)] fc'
    /\ a0 = wint Z_OK
    /\ (exists j : list byte, rw_cells usegs m' S (zs_pub ni ai ti no ao to p1 p2 ++ [CB 64 j])).

Section Api.
Variable R : zreps.
Definition inflateEnd_stmtX : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (S : Z) (is : IS za) (w : option bptr) (Aw : Z) (sp_ : bptr) (As : Z)
         (ni ai ti no ao to : Z) (p1 p2 : list byte) (lo B : Z) (errv canary : word),
  lx_env m s (iblocks w Aw sp_ As) LB sp tp B lo errv canary ->
  rw_cells usegs m S (zs_pub ni ai ti no ao to p1 p2) ->
  zr_i R m S (iblocks w Aw sp_ As) is ->
  strm_in_frame sp S B ->
  lo <= bv_unsigned sp - Z_INFLATEEND_STACK -> bv_unsigned sp mod 16 = 0 ->
  frm0 fc ->
  a0 = wz S ->
  implM usegs (bind lops (lib_free lops w) (fun _ => lib_free lops (Some sp_))) s
        (inflateEnd_postX ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S ni ai ti no ao to p1 p2 lo B canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz Z_INFLATEEND) fc None m (seg_rom usegs)).
End Api.

Section IENDX.
  Hypothesis FREE : rfree_stmt.
  Hypothesis HFRAME : RHEAP_frame_stmt.
  Hypothesis HBR : RHEAP_block_range_stmt.
  Hypothesis HND : RHEAP_blocks_nodup_stmt.

  (* [comment removed for export] *)
  Lemma iend_secondX : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m m1 : mem)
      (s st1 : PState) (LB : list block) (L : ilay) (sp_ : bptr) (lo B : Z) (errv1 canary : word)
      (ni ai ti no ao to : Z) (p1 p2 : list byte) (msg adler : Z) (dt : word) (p3 : list byte) (resv : word)
      (t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    lx_env m1 st1 [(sp_, il_As L, 7176)] LB (wz (bv_unsigned sp + -16)) tp B lo errv1 canary ->
    rw_cells usegs m1 (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
    rw_cells usegs m1 (il_S L) (zs_pub ni ai ti no ao to p1 p2) ->
    rw_cells usegs m1 (il_S L + 48) (izs_priv_cells L msg adler dt p3 resv) ->
    lx_pres LB (bv_unsigned sp) [(il_S L, il_S L + ZS_SIZEOF)] m m1 -> ps_so st1 = ps_so s -> ps_fa st1 = ps_fa s ->
    strm_in_frame sp (il_S L) B -> lo <= bv_unsigned sp - Z_INFLATEEND_STACK -> frm0 fc ->
    implM usegs (lib_free lops (Some sp_)) st1
      (inflateEnd_postX ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB (il_S L) ni ai ti no ao to p1 p2 lo B canary m)
      (MS (mkR (wz PC_IE_RET2) (wz (bv_unsigned sp + -16)) gp tp t0 t1 t2 (wz (il_S L)) s1 a0 (wz (il_As L)) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_ZCFREE) fc None m1 (seg_rom usegs)).
  Proof.
    intros until t6. intros ENV1 FR PUB ZQ PRES1 ESO1 EFA1 SIF LOSP FRM0.
    pose proof ENV1 as E1. unfold lx_env in E1. destruct E1 as (HP1 & _ & _ & _ & _ & AUX1 & SPB1 & B63 & ST1 & LOC1 & LOG1 & ERR1 & TP1 & MI1).
    destruct SIF as (SF1 & SF2 & SF3). unfold ZS_SIZEOF in SF2. unfold Z_INFLATEEND_STACK, RFREE_STACK in LOSP. unfold GLOBALS_TOP in LOG1.
    pose proof alloc_ceiling_range as CR.
    assert (E16 : bv_unsigned (wz (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
    eapply (izfree_last FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 st1 _ sp_ (il_As L) 7176 lo B errv1);
      [ exact HP1 | left; reflexivity | exact AUX1 | exact SPB1 | exact ST1 | exact LOC1 | rewrite E16; unfold RFREE_STACK; lia | exact ERR1 | exact MI1
      | exact TP1 | reflexivity | ].
    intros st2 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m2 MI2 ST2 ERR2 AUX2 HPR2 EFA2 ESO2 HP2.
    cbn [app] in HPR2, HP2. rewrite (lb_remove_head sp_ _ _ _ (HND _ _ _ HP1)) in HPR2, HP2. rewrite E16 in HPR2, ST2.
    assert (ENV2 : lx_env m2 st2 [] LB (wz (bv_unsigned sp + -16)) tp B lo errv1 canary).
    { eapply (lx_env_heap m1 m2 st1 st2); [exact ENV1| rewrite E16; exact HPR2| exact HP2| exact MI2| rewrite E16; exact ST2| exact ERR2| exact AUX2]. }
    assert (AGC : forall A0 n, bv_unsigned sp + -16 <= A0 -> 0 <= n -> A0 + n <= 2^64 -> Z_dview.agree_on A0 (A0 + n) m1 m2).
    { intros A0 n H1 H2 H3 a Ha. apply HPR2; [lia|]. left. lia. }
    apply (Z_dview.rw_cells_agree m1 m2) in FR; [|apply AGC; cbn [cells_size csize Nat.add]; lia].
    apply (Z_dview.rw_cells_agree m1 m2) in PUB; [|apply AGC; unfold zs_pub; cbn [cells_size csize Nat.add]; lia].
    apply (Z_dview.rw_cells_agree m1 m2) in ZQ; [|apply AGC; unfold izs_priv_cells; cbn [cells_size csize Nat.add]; lia].
    replace (ret_pc (wz PC_IE_RET2)) with (wz PC_IE_RET2) by (symmetry; apply ret_pc_even; [unfold PC_IE_RET2; lia| reflexivity]).
    eapply evt_mono; [exact (iend_tail L msg adler dt p3 resv lo ra sp gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m2
                                FR ST2 ltac:(lia) ltac:(lia) ZQ SF1 ltac:(lia) MI2)|].
    intros ms' (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m' & -> & MU' & WM' & MI' & STK' & (j & ZQ')).
    assert (BLB : forall b, In b LB -> blk_addr b + blk_size b <= lo /\ 0 < blk_addr b).
    { intros b Hb. pose proof (HBR _ _ _ b HP2 Hb) as (Q1 & Q2 & Q3 & Q4 & Q5). lia. }
    unfold inflateEnd_postX. exists v0, v1, v2, (wz 0), c1, c2, c3, c4, c5, c6, c7, v3, v4, v5, v6, F, fc, m'.
    split; [reflexivity|]. split; [|split].
    - unfold lx_post_env. split.
      { exists errv1. eapply (lx_env_munch [(lo, bv_unsigned sp); (il_S L + 48, il_S L + 112)] m2 m' st2 [] LB (wz (bv_unsigned sp + -16)) sp tp B lo errv1 canary HFRAME ENV2 MU' WM' MI' STK'); [lia| |].
        - constructor; [|constructor; [|constructor]]; unfold rclient_write_ok; cbn [fst snd]; left; lia.
        - intros a Ha. cbn [outside]. repeat split; lia. }
      split; [exact FRM0|]. split; [|split; congruence].
      eapply lx_pres_trans; [exact PRES1|]. eapply lx_pres_trans.
      { apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HPR2| lia| auto]. }
      apply (lx_pres_of_munch LB (bv_unsigned sp) _ _ m2 m' MU' WM').
      intros a (NX & HC). cbn [rin_ivs fst snd] in NX. unfold ZS_SIZEOF in NX. cbn [outside].
      destruct HC as [H|[(b & Hb & Hr)|[H _]]]; [| pose proof (BLB _ Hb)|]; repeat split; lia.
    - unfold wint, Z_OK. reflexivity.
    - apply (rw_cells_transport usegs [(lo, bv_unsigned sp); (il_S L + 48, il_S L + 112)] m2 m') in PUB; [| exact MU'| exact WM'| unfold zs_pub; cbn [cells_size csize Nat.add disjoint_from]; repeat split; lia].
      assert (HJ : rw_cells usegs m' (il_S L) (zs_pub ni ai ti no ao to p1 p2 ++ [CB 64 j])).
      { apply rw_cells_app. split; [exact PUB|]. unfold zs_pub. cbn [cells_size csize Nat.add]. exact ZQ'. }
      exists j. exact HJ.
  Qed.

  Variable R : zreps.
  Hypothesis ER : zr_i R = zr_i_def.

  Theorem inflateEnd_okX : inflateEnd_stmtX R.
  Proof.
    unfold inflateEnd_stmtX. intros until canary. intros ENV PUB ZR SIF LOSP SP16 FRM0 ->.
    rewrite ER in ZR. destruct ZR as (s_a & L & w' & sp' & ES & EL & HW & [HZQ HIST] & HI & HA & HPq).
    destruct (iblocks_inv' _ _ _ _ _ _ _ _ EL) as (-> & -> & EAs & EAw). subst S.
    destruct HZQ as (dt & p3 & resv & ZQ). destruct HIST as [GA GT Gl Gw Gc Gwin ARRS LAY].
    pose proof ENV as E0. unfold lx_env in E0. destruct E0 as (HP & LXS & ZLS & SEW & SSP & AUX & SPB & B63 & STK & LOC & LOG & ERR & TP & MI).
    pose proof SIF as (SF1 & SF2 & SF3). unfold ZS_SIZEOF in SF2. pose proof LOSP as LOSP'. unfold Z_INFLATEEND_STACK, RFREE_STACK in LOSP'. unfold GLOBALS_TOP in LOG.
    pose proof alloc_ceiling_range as CR.
    destruct HI as (_ & _ & HINV & _). destruct HINV as (_ & _ & HMF).
    pose proof (RefInflateSafeS2.MF_mode_range _ _ _ _ HMF) as RM. unfold HEAD, MEM, SYNC in RM.
    assert (RB : forall b, In b (Zlib_iface.iblocks w Aw sp_ As ++ LB) -> 0 < blk_addr b /\ blk_addr b + blk_size b <= lo).
    { intros b Hb. pose proof (HBR _ _ _ b HP Hb) as (Q1 & Q2 & Q3 & Q4 & Q5). lia. }
    assert (RAs : 0 < il_As L /\ il_As L + 7176 <= lo).
    { rewrite EAs. apply (RB (sp_, As, 7176)). apply in_or_app. left. unfold Zlib_iface.iblocks. apply in_or_app. right. left. reflexivity. }
    assert (RW : is_window_blk s_a <> None -> 0 < il_Aw L < 2 ^ 63).
    { intros NE. destruct w as [wp|]; [|exfalso; apply NE; apply HW; reflexivity].
      rewrite (EAw ltac:(discriminate)). pose proof (RB (wp, Aw, 32768) ltac:(apply in_or_app; left; left; reflexivity)) as Q. cbn [blk_addr blk_size fst snd] in Q. lia. }
    assert (E16 : bv_unsigned (wz (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
    eapply implM_evt; [exact (iend_to_free L s_a (zs_msg (iz_z is)) (zs_adler (iz_z is)) dt p3 resv lo ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                               STK ltac:(lia) ltac:(lia) ZQ GA SF1 ltac:(lia) (proj1 RAs) (proj2 RAs) ltac:(lia) RW MI SF3 (proj1 (proj2 (proj1 LAY))))|].
    intros ms1 (t0' & t1' & t2' & a0' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & FR & STK1 & MU1 & WM1 & MI1).
    assert (ENV1 : lx_env m1 s (Zlib_iface.iblocks w Aw sp_ As) LB (wz (bv_unsigned sp + -16)) tp B lo errv canary).
    { eapply (lx_env_munch [(lo, bv_unsigned sp)] m m1 s _ LB sp (wz (bv_unsigned sp + -16)) tp B lo errv canary HFRAME ENV MU1 WM1 MI1);
        [rewrite E16; exact STK1| rewrite E16; lia| |].
      - constructor; [|constructor]. unfold rclient_write_ok; cbn [fst snd]; left; lia.
      - intros a Ha. cbn [outside]. repeat split; lia. }
    apply (rw_cells_transport usegs [(lo, bv_unsigned sp)] m m1) in PUB; [| exact MU1| exact WM1| unfold zs_pub; cbn [cells_size csize Nat.add disjoint_from]; repeat split; lia].
    apply (rw_cells_transport usegs [(lo, bv_unsigned sp)] m m1) in ZQ; [| exact MU1| exact WM1| unfold izs_priv_cells; cbn [cells_size csize Nat.add disjoint_from]; repeat split; lia].
    assert (PRES1 : lx_pres LB (bv_unsigned sp) [(il_S L, il_S L + ZS_SIZEOF)] m m1).
    { apply (lx_pres_of_munch LB (bv_unsigned sp) _ [(lo, bv_unsigned sp)] m m1 MU1 WM1).
      intros a (NX & HC). cbn [outside].
      destruct HC as [H|[(b & Hb & Hr)|[H _]]]; [| pose proof (RB b ltac:(apply in_or_app; right; exact Hb))|]; repeat split; lia. }
    destruct w as [wp|].
    - (* [comment removed for export] *)
      destruct (is_window_blk s_a) as [wb|] eqn:EW; [|exfalso; pose proof (proj2 HW eq_refl) as Q; discriminate Q].
      rewrite (EAw ltac:(discriminate)) in *.
      pose proof ENV1 as E1. unfold lx_env in E1. destruct E1 as (HP1 & _ & _ & _ & _ & AUX1 & SPB1 & _ & ST1 & LOC1 & _ & ERR1 & TP1 & _).
      eapply (izfree FREE (fun _ => lib_free lops (Some sp_)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 s _ wp Aw 32768 lo B errv);
        [ exact HP1 | left; reflexivity | exact AUX1 | exact SPB1 | exact ST1 | exact LOC1 | rewrite E16; unfold RFREE_STACK; lia | exact ERR1 | exact MI1
        | exact TP1 | reflexivity | ].
      intros st2 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m2 MI2 ST2 ERR2 AUX2 HPR2 EFA2 ESO2 HP2.
      unfold Zlib_iface.iblocks, the_zapi in HPR2, HP2, HP1. cbn [z_wsize z_isize zinst app] in HPR2, HP2, HP1.
      rewrite (lb_remove_head wp _ _ _ (HND _ _ _ HP1)) in HPR2, HP2. rewrite E16 in HPR2, ST2.
      assert (ENV2 : lx_env m2 st2 [(sp_, il_As L, 7176)] LB (wz (bv_unsigned sp + -16)) tp B lo errv canary).
      { eapply (lx_env_heap m1 m2 s st2); [exact ENV1| rewrite E16; eapply rheap_pres_weaken; [exact HPR2| lia| intros bx Hb; right; exact Hb]| rewrite EAs; exact HP2| exact MI2
          | rewrite E16; exact ST2| exact ERR2| exact AUX2]. }
      assert (AGC : forall A0 n, bv_unsigned sp + -16 <= A0 -> 0 <= n -> A0 + n <= 2^64 -> Z_dview.agree_on A0 (A0 + n) m1 m2).
      { intros A0 n H1 H2 H3 a Ha. apply HPR2; [lia|]. left. lia. }
      apply (Z_dview.rw_cells_agree m1 m2) in FR; [|apply AGC; cbn [cells_size csize Nat.add]; lia].
      apply (Z_dview.rw_cells_agree m1 m2) in PUB; [|apply AGC; unfold zs_pub; cbn [cells_size csize Nat.add]; lia].
      apply (Z_dview.rw_cells_agree m1 m2) in ZQ; [|apply AGC; unfold izs_priv_cells; cbn [cells_size csize Nat.add]; lia].
      assert (PRES2 : lx_pres LB (bv_unsigned sp) [(il_S L, il_S L + ZS_SIZEOF)] m m2).
      { eapply lx_pres_trans; [exact PRES1|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HPR2| lia| intros bx Hb; right; exact Hb]. }
      replace (ret_pc (wz PC_IE_RET1)) with (wz PC_IE_RET1) by (symmetry; apply ret_pc_even; [unfold PC_IE_RET1; lia| reflexivity]).
      eapply implM_evt; [exact (iend_to_free2 L (zs_msg (iz_z is)) (zs_adler (iz_z is)) dt p3 resv lo ra sp gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m2
                                 FR ST2 ltac:(lia) ltac:(lia) ZQ SF1 ltac:(lia) MI2)|].
      intros ms3 (v0 & v1 & v2 & c0 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & ->).
      exact (iend_secondX ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m2 s st2 LB L sp_ lo B errv canary ni ai ti no ao to p1 p2
               (zs_msg (iz_z is)) (zs_adler (iz_z is)) dt p3 resv v0 v1 v2 c0 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6
               ENV2 FR PUB ZQ PRES2 ESO2 EFA2 SIF LOSP FRM0).
    - (* [comment removed for export] *)
      destruct (is_window_blk s_a) as [wb|] eqn:EW; [exfalso; pose proof (proj1 HW eq_refl) as Q; discriminate Q|].
      cbn [bind lops Target.ops lib_free lib_free_opt]. apply implM_ret_bind.
      rewrite <- EAs in ENV1.
      exact (iend_secondX ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s s LB L sp_ lo B errv canary ni ai ti no ao to p1 p2
               (zs_msg (iz_z is)) (zs_adler (iz_z is)) dt p3 resv t0' t1' t2' a0' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
               ENV1 FR PUB ZQ PRES1 eq_refl eq_refl SIF LOSP FRM0).
  Qed.
End IENDX.
End WithCeiling0.
