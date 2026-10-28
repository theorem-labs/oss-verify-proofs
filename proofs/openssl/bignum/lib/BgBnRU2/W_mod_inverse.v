(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnModel BnTree BnInv BnBridge BgState BgInv BgLib BgWords BgArith.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require BnDivWords.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require F_fwritex.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnArith BnMem BnTac BnTacX.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_small W_small2.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU2 Require Import W_small3.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep BnLeaves.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require Import BgLeaves W_div_tail.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require CtxKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU Require W_ctx W_ctx_get W_ctx_end W_copy W_cmp W_uadd W_usub.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU2 Require W_set_word W_rshift1 W_shift W_sub.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnEU Require Import ExpKit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnRU2 Require Import InvKit.
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

Local Notation ops := (tree_ops bptr).
Local Notation ST := (bstate bptr).

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BN_MOD_INVERSE : Z := 0x108500.
Definition INT_BN_MOD_INVERSE : Z := 0x107b60.
Definition BN_NNMOD : Z := 0x108af0.

Definition inv_rest (rR ra rn : bnref) : BM (M := btree bptr) unit :=
  bbind ops (BN_CTX_start ops) (fun _ =>
  bbind ops (BN_CTX_get ops) (fun rA =>
  bbind ops (BN_CTX_get ops) (fun rB =>
  bbind ops (BN_CTX_get ops) (fun rX =>
  bbind ops (BN_CTX_get ops) (fun rD =>
  bbind ops (BN_CTX_get ops) (fun rM =>
  bbind ops (BN_CTX_get ops) (fun rY =>
  bbind ops (BN_CTX_get ops) (fun rT =>
  bbind ops (BN_one ops rX) (fun _ =>
  bbind ops (BN_zero ops rY) (fun _ =>
  bbind ops (BN_copy ops rB ra) (fun _ =>
  bbind ops (BN_copy ops rA rn) (fun _ =>
  bbind ops (bbind ops (bget ops rA) (fun b => bset ops rA (bn_with_neg b false))) (fun _ =>
  bbind ops (bget ops rB) (fun bB =>
  bbind ops (BN_ucmp ops rB rA) (fun c =>
  bbind ops (if bn_neg bB || (0 <=? c) then BN_nnmod ops rB rB rA else bret ops tt) (fun _ =>
  bbind ops (BN_num_bits ops rn) (fun nb =>
  bbind ops (bget ops rn) (fun n2 =>
  bbind ops (if is_odd_pure n2 && (nb <=? 2048) then inv_binary_loop ops (Z.to_nat (2 * nb) + 2) rA rB rX rY rn else bunr ops) (fun _ =>
  bbind ops (BN_sub ops rY rn rY) (fun _ =>
  bbind ops (bget ops rA) (fun bA =>
  bbind ops (if is_one_pure bA then
               bbind ops (bget ops rY) (fun y => bbind ops (BN_ucmp ops rY rn) (fun c =>
               if negb (bn_neg y) && (c <? 0) then BN_copy ops rR rY else BN_nnmod ops rR rY rn))
             else bunr ops) (fun _ => BN_CTX_end ops)))))))))))))))))))))).

Definition BN_mod_inverse_r (rR ra rn : bnref) : BM (M := btree bptr) unit :=
  bbind ops (bget ops rn) (fun n =>
  bbind ops (bget ops ra) (fun a =>
  if abs_is_word_pure n 1 || is_zero_pure n then bunr ops
  else if has_flag a BN_FLG_CONSTTIME || has_flag n BN_FLG_CONSTTIME then bunr ops
  else inv_rest rR ra rn)).

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Variable CS : Z.
  Hypothesis CS128 : 128 <= CS.
  Hypothesis STK_START : W_ctx.BN_CTX_START_STACK <= CS.
  Hypothesis STK_GET : W_ctx_get.BN_CTX_GET_STACK <= CS.
  Hypothesis STK_END : W_ctx_end.BN_CTX_END_STACK <= CS.
  Hypothesis STK_SETW : W_set_word.BN_SET_WORD_STACK <= CS.
  Hypothesis STK_COPY : W_copy.BN_COPY_STACK <= CS.
  Hypothesis STK_UCMP : W_cmp.BN_UCMP_STACK <= CS.
  Hypothesis STK_UADD : W_uadd.BN_UADD_STACK <= CS.
  Hypothesis STK_USUB : W_usub.BN_USUB_STACK <= CS.
  Hypothesis STK_SUB : W_sub.BN_SUB_STACK <= CS.
  Hypothesis STK_RSH1 : W_rshift1.BN_RSHIFT1_STACK <= CS.
  Hypothesis STK_RSH : W_shift.BN_RSHIFT_W_STACK <= CS.
  Definition BN_MOD_INVERSE_STACK : Z := 256 + CS.

  Hypothesis BN_nnmod_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BgBnU.BnRep.err_addrs)
      (lo B : Z) (errv : word) (rr rx rm : bnref) (ar ax am ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv CS -> tp = wz RATP ->
    ref_at bs OW PL rr ar -> ref_at bs OW PL rx ax -> ref_at bs OW PL rm am -> hpl PL rr -> rx <> ROne -> rm <> ROne -> pl_ctx PL = Some (ac, qc) ->
    a0 = wz ar -> a1 = wz ax -> a2 = wz am -> a3 = wz ac ->
    implM bgusegs (interp (embed (BN_nnmod ops rr rx rm bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz 1))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_NNMOD) fc None m (seg_rom bgusegs)).

  Local Tactic Notation "apw" uconstr(L) := first [eapply (L HM HF) | eapply (L HM) | eapply (L HF) | eapply L].

  Section Body.
    Variables (ra gp sp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
    Variables (lo B : Z) (s : PState) (bs : bstate bptr) (OW LB : list block) (m : mem) (PL : placement) (EA : BgBnU.BnRep.err_addrs).
    Variables (rR ra_ rn : bnref) (aR aa an ac : Z) (qc : bptr).
    Hypothesis CEIL : alloc_ceiling <= lo.
    Hypothesis GLO' : GLOBALS_TOP <= lo.
    Hypothesis LO : lo <= bv_unsigned sp - (256 + CS).
    Hypothesis SPB : bv_unsigned sp <= B.
    Hypothesis B63 : B < 2^63.
    Hypothesis FROK : frames_ok PL (bv_unsigned sp) B.
    Hypothesis HPC : pl_ctx PL = Some (ac, qc).
    Hypothesis WRR : hpl PL rR.
    Hypothesis NROa : ra_ <> ROne.
    Hypothesis NROn : rn <> ROne.
    Hypothesis ARR : 0 < aR < 2^64.
    Hypothesis SP16 : bv_unsigned sp mod 16 = 0.

    Notation SPv := (bv_unsigned sp).
    Notation FB := (bv_unsigned sp + -256).
    Notation SPi := (bv_unsigned sp + -64).
    Notation NI := (bv_unsigned sp + -52).

    Lemma SPR2 : SPv < 2 ^ 64.
    Proof using. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. clear - SPR. lia. Qed.
    Lemma FBlo : lo <= FB. Proof using LO CS128. clear - LO CS128. lia. Qed.
    Lemma FBsp : FB <= SPv. Proof using. clear. lia. Qed.
    Lemma LOF : lo <= FB - CS. Proof using LO. clear - LO. lia. Qed.
    Lemma ESPF : bv_unsigned (Z_to_bv 64 FB) = FB.
    Proof using CEIL LO CS128. pose proof SPR2 as H. apply unsigned_lit. clear - H CEIL LO CS128. lia. Qed.

    Notation KENV := (kenv LB PL lo B SPv FB s bs OW m).
    Notation KCALL := (kcall LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK CS LOF).
    Notation KCALLE := (kcall_end LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK CS LOF).
    Notation KZERO := (k_is_zero LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK CS CS128 LOF).
    Notation KFLAGS := (k_get_flags LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK CS CS128 LOF).
    Notation KODD := (k_is_odd LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK CS CS128 LOF).
    Notation KONE := (k_is_one LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK CS CS128 LOF).
    Notation KWORD := (k_abs_is_word LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK CS CS128 LOF).
    Notation KBIT := (k_is_bit_set LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK CS CS128 LOF).
    Notation KBITS := (k_num_bits LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK CS CS128 LOF).

    Definition saved_i : list cell :=
      [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 (Z_to_bv 64 aR); C8 (Z_to_bv 64 aa); C8 (Z_to_bv 64 an); C8 (Z_to_bv 64 0); C8 sp;
       C8 (Z_to_bv 64 1082720)].
    Definition saved_w : list cell := [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
    Definition ifr_i (j1 : list byte) (yS dD : word) (jl : list byte) : list cell := [CB 40 j1; C8 yS; C8 dD; C8 (Z_to_bv 64 aR); CB 24 jl] ++ saved_i.
    Definition ifr0_i (j1 jD jl : list byte) : list cell := [CB 48 j1; CB 8 jD; C8 (Z_to_bv 64 aR); CB 24 jl] ++ saved_i.
    Definition ifr_w (j2 : list byte) : list cell := [CB 12 j2; C4 (Z_to_bv 64 0)] ++ saved_w.
    Definition ifr (j1 : list byte) (yS dD : word) (jl j2 : list byte) : list cell := ifr_i j1 yS dD jl ++ ifr_w j2.
    Definition ifr0 (j1 jD jl j2 : list byte) : list cell := ifr0_i j1 jD jl ++ ifr_w j2.

    Definition FINALQ : unit * ST -> PState -> machine_state -> Prop :=
      bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA
              (fun (_ : unit) (_ : ST) (_ : list block) (PL' : placement) (a0' : word) => PL' = PL /\ a0' = wz aR).

    Lemma BN_CTX_free_null_specU : forall
        (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
        (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
      stk bgusegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> mem_inv bgusegs m -> a0 = Z_to_bv 64 0 ->
      evt bgusegs (bn_small_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                   [(bv_unsigned sp - 64, bv_unsigned sp)] lo m (fun _ _ => True))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x100afc) fc None m (seg_rom bgusegs)).
    Proof.
      intros ra' sp' gp' tp' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6'
        F' fc' m' lo' STk LOk MIk ->.
      pose proof (munch_refl [(bv_unsigned sp' - 64, bv_unsigned sp')] m') as MU. pose proof (wmono_refl bgusegs m') as WM.
      carve_frame 64%nat STk. do 9 step. step. if_true.
      do 7 step. release_frame FR STk (bv_unsigned sp'). step. step.
      finish. exact I.
    Qed.

    Lemma inv_exit : forall j1 yS dD jl j2 stK bsK mK OWK
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
      KENV (ifr j1 yS dD jl j2) stK bsK mK OWK -> lib_state bsK mK OWK PL EA ->
      implM bgusegs (interp (embed (BN_CTX_end ops bsK))) stK FINALQ
        (MS (mkR rax (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 (Z_to_bv 64 SPi) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                 x18 (Z_to_bv 64 aR) x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
            F (Z_to_bv 64 0x108098) fc None mK (seg_rom bgusegs)).
    Proof.
      intros until t6. intros ENVK LSK.
      pose proof SPR2 as SPR. pose proof ESPF as ESP. pose proof LO as LO'. pose proof GLO' as GLO2. unfold GLOBALS_TOP in GLO2.
      unfold MallocRep.wz.
      unfold implM. iprefix. zstep. zstep. ihere. to_implM.
      eapply (KCALLE _ _ FINALQ); [exact ENVK | exact LSK
        | intros errv PRE; apw W_ctx_end.BN_CTX_end_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_END) | reflexivity | exact HPC | reflexivity]
        | intros v b o p a; cbv beta; intros [E _]; exact E |].
      intros u st' bs' m' OW' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV' LS' RS'; cbv beta; intros (_ & EOW).
      replace (ret_pc (Z_to_bv 64 1081504)) with (Z_to_bv 64 1081504) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (kenv_final LB PL lo B SPv FB s bs OW m _ _ _ _ _ ENV') as (F1 & F2 & STF & (errvF & F4) & F5 & F6 & F7 & F8 & F9 & FRF).
      unfold ifr in FRF. apply BgU.F_fwritex.rw_cells_app in FRF. destruct FRF as (FRI & FRW).
      assert (ESZ : FB + Z.of_nat (cells_size (ifr_i j1 yS dD jl)) = SPi).
      { unfold ifr_i, saved_i. cbn [cells_size csize app Nat.add]. clear. lia. }
      rewrite ESZ in FRW. clear ESZ.
      unfold ifr_i, saved_i in FRI. unfold ifr_w, saved_w in FRW. cbn [app] in FRI, FRW.
      do 2 zstep. do 13 zstep.
      release_frame FRI STF (bv_unsigned sp + -64). do 2 zstep.

      zstep. zstep. zstep. if_true.
      zstep. zstep.
      assert (ENVW : kenv LB PL lo B SPv SPi s bs OW m (ifr_w j2) st' bs' m' OW').
      { split; [exact F1|]. split; [exact F2|]. split; [exact STF|]. split; [exists errvF; exact F4|]. split; [exact F5|].
        split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [exact F9|]. split; [exact FRW|].
        unfold ifr_w, saved_w. cbn [cells_size csize app Nat.add]. clear. lia. }
      eapply evt_cut.
      { eapply (BN_CTX_free_null_specU _ (Z_to_bv 64 SPi)) with (lo := lo);
          [rewrite unsigned_lit by lia; exact STF | rewrite unsigned_lit by lia; lia | exact F5 | reflexivity]. }
      intros ms' PO. unfold bn_small_post in PO.
      destruct PO as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m'' & E & MUc & WMc & MIc & STc & _).
      subst ms'. rewrite unsigned_lit in MUc, STc by lia.
      destruct (kenv_below LB PL EA lo B SPv SPi s bs OW m CEIL GLO' ltac:(lia) ltac:(lia) SPB B63 SPR2 FROK (ifr_w j2) st' bs' m' m'' OW' 64
                  ENVW LS' ltac:(lia) ltac:(lia) MUc WMc STc MIc) as (ENVW' & LS'').
      clear ENVW F1 F2 STF F4 F5 F6 FRW.
      pose proof (kenv_final LB PL lo B SPv SPi s bs OW m _ _ _ _ _ ENVW') as (G1 & G2 & STG & (errvG & G4) & G5 & G6 & G7 & G8 & G9 & FRW).
      unfold ifr_w, saved_w in FRW. cbn [app] in FRW.
      replace (ret_pc (Z_to_bv 64 1082784)) with (Z_to_bv 64 1082784) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      zstep. do 6 zstep.
      release_frame FRW STG (bv_unsigned sp). do 2 zstep.
      apply evt_done. unfold FINALQ, bn_post. do 15 eexists. exists m'', OW', PL, errvG.
      split; [reflexivity|]. cbn [fst snd].
      split; [exact G1|]. split; [exact LS''|]. split; [exact G2|]. split; [exact STG|]. split; [exact G4|]. split; [exact G5|].
      split; [exact G6|]. split; [exact G7|]. split; [exact G8|]. split; [exact G9|]. split; reflexivity.
    Qed.

    Section Loops.
      Variables (rA rB rX rY : bnref) (aA aB aX aY : Z) (j1 : list byte) (dD : word) (jl j2 : list byte).
      Hypothesis HPA : hpl PL rA.
      Hypothesis HPB : hpl PL rB.
      Hypothesis HPX : hpl PL rX.
      Hypothesis HPY : hpl PL rY.

      Notation IFR := (ifr j1 (Z_to_bv 64 aY) dD jl j2).

      Definition IREFS (bsK : ST) (OWK : list block) : Prop :=
        ref_at bsK OWK PL rA aA /\ ref_at bsK OWK PL rB aB /\ ref_at bsK OWK PL rX aX /\ ref_at bsK OWK PL rY aY
        /\ ref_at bsK OWK PL rn an /\ ref_at bsK OWK PL rR aR.
      Lemma irefs_stable : forall bsK OWK bs' OW', IREFS bsK OWK -> refs_stable bsK OWK bs' OW' -> IREFS bs' OW'.
      Proof.
        intros bsK OWK bs' OW' (H1 & H2 & H3 & H4 & H5 & H6) RS.
        repeat split; eapply (ref_at_stable _ _ _ _ PL _ _ RS); assumption.
      Qed.

      Notation IMS rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x22 x23 x26 t3 t4 t5 t6 pc mem :=
        (MS (mkR rax (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 SPi) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                 x18 (Z_to_bv 64 aR) (Z_to_bv 64 NI) (Z_to_bv 64 an) x23 (Z_to_bv 64 aA) x22 (Z_to_bv 64 aB) x26 (Z_to_bv 64 aY) t3 t4 t5 t6)
            F (Z_to_bv 64 pc) fc None mem (seg_rom bgusegs)).

      Definition SHQ (pcq : Z) (bsK : ST) (OWK : list block) (lo18 hi18 : Z) (r : Z * ST) (st' : PState) (ms' : machine_state) : Prop :=
        exists mK' OWK' (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 x26 t3 t4 t5 t6 : word),
          ms' = IMS rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (fst r)) (Z_to_bv 64 aX) x23 x26 t3 t4 t5 t6 pcq mK'
          /\ KENV IFR st' (snd r) mK' OWK' /\ lib_state (snd r) mK' OWK' PL EA /\ refs_stable bsK OWK (snd r) OWK' /\ lo18 <= fst r <= hi18.

      Definition ANYQ {A : Type} (pcq : Z) (bsK : ST) (OWK : list block) (r : A * ST) (st' : PState) (ms' : machine_state) : Prop :=
        exists mK' OWK' (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x22 x23 x26 t3 t4 t5 t6 : word),
          ms' = IMS rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x22 x23 x26 t3 t4 t5 t6 pcq mK'
          /\ KENV IFR st' (snd r) mK' OWK' /\ lib_state (snd r) mK' OWK' PL EA /\ refs_stable bsK OWK (snd r) OWK'.

      Lemma shl_O : forall r1 r2 r3 shift (bsK : ST), inv_shift_loop ops 0 r1 r2 r3 shift bsK = bunr ops bsK.
      Proof. reflexivity. Qed.
      Lemma shl_S : forall f r1 r2 r3 shift (bsK : ST),
        inv_shift_loop ops (S f) r1 r2 r3 shift bsK =
        if is_bit_set_pure (getbn r1 bsK) shift then bret ops shift bsK
        else bbind ops (if is_odd_pure (getbn r2 bsK) then BN_uadd ops r2 r2 r3 else bret ops tt)
               (fun _ => bbind ops (BN_rshift1 ops r2 r2) (fun _ => inv_shift_loop ops f r1 r2 r3 (shift + 1))) bsK.
      Proof. intros. cbn [inv_shift_loop]. rewrite bbind_get. destruct (is_bit_set_pure (getbn r1 bsK) shift); [reflexivity|]. rewrite bbind_get. reflexivity. Qed.

      Local Ltac hres := let H := fresh "HRES" in intros ? ? ? ? ? H; hnf in H; exact (proj1 H).
      Local Ltac retpc n := replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      Lemma shift1_loop : forall f shift stK bsK mK OWK
          (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 x26 t3 t4 t5 t6 : word),
        KENV IFR stK bsK mK OWK -> lib_state bsK mK OWK PL EA -> IREFS bsK OWK ->
        0 <= shift -> shift + Z.of_nat f < 2^30 ->
        implM bgusegs (interp (embed (inv_shift_loop ops f rB rX rn shift bsK))) stK (SHQ 0x107f3c bsK OWK shift (shift + Z.of_nat f))
          (IMS rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 shift) (Z_to_bv 64 aX) x23 x26 t3 t4 t5 t6 0x107f2c mK).
      Proof.
        induction f as [|f IH]; intros until t6; intros ENVK LSK IR SH0 SHF.
        { rewrite shl_O. unfold bunr. cbn [unreachable tree_ops embed interp]. apply implM_interp_unr. }
        pose proof IR as (HAA & HAB & HAX & HAY & HAN & HAR).
        pose proof SPR2 as SPR. pose proof ESPF as ESP. pose proof GLO' as GLO2. unfold GLOBALS_TOP in GLO2.
        rewrite shl_S.
        unfold implM. iprefix. do 3 zstep.
        eapply KBIT; [exact ENVK | exact LSK | exact HAB | exact (proj1 HPB) | clear - SH0 SHF; lia |].
        intros m1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV1 LS1. clear ENVK LSK.
        retpc 1081144.
        assert (JOIN : forall stJ bsJ mJ OWJ (rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x26' t3' t4' t5' t6' : word),
                  KENV IFR stJ bsJ mJ OWJ -> lib_state bsJ mJ OWJ PL EA -> refs_stable bsK OWK bsJ OWJ ->
                  implM bgusegs (interp (embed (bbind ops (BN_rshift1 ops rX rX) (fun _ => inv_shift_loop ops f rB rX rn (shift + 1)) bsJ))) stJ
                    (SHQ 0x107f3c bsK OWK shift (shift + Z.of_nat (S f)))
                    (IMS rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 aX) (Z_to_bv 64 aX) (Z_to_bv 64 (shift + 1)) x26' t3' t4' t5' t6' 0x107fd4 mJ)).
        { intros until t6'. intros ENVJ LSJ RSJ.
          pose proof (irefs_stable _ _ _ _ IR RSJ) as IRJ. pose proof IRJ as (HAAj & HABj & HAXj & HAYj & HANj & HARj).
          unfold implM. iprefix. zstep.
          do 2 zstep. ihere. to_implM.
          eapply KCALL; [exact ENVJ | exact LSJ
            | intros errv PRE; apw W_rshift1.BN_rshift1_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_RSH1) | reflexivity | exact HAXj | exact (hpl_wref PL rX HPX) | reflexivity | reflexivity]
            | hres |].
          intros u st2 bs2 m2 OW2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV2 LS2 RS2 RES2. hnf in RES2. destruct RES2 as (_ & -> & _). unfold MallocRep.wz.
          retpc 1081312.
          unfold implM. iprefix. zstep. zstep. if_true.
          ihere. to_implM.
          eapply implM_mono.
          { eapply IH; [exact ENV2 | exact LS2 | exact (irefs_stable _ _ _ _ IRJ RS2) | clear - SH0; lia | clear - SHF; rewrite Nat2Z.inj_succ in SHF; lia]. }
          cbv beta. intros r st' ms' (mK' & OWK' & R).
          destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & E & K1 & K2 & K3 & K4).
          unfold SHQ. exists mK', OWK'. do 18 eexists. split; [exact E|]. split; [exact K1|]. split; [exact K2|].
          split; [eapply refs_stable_trans; [exact RSJ| eapply refs_stable_trans; [exact RS2| exact K3]]|].
          clear - K4. rewrite Nat2Z.inj_succ. lia. }
        destruct (is_bit_set_pure (getbn rB bsK) shift) eqn:EB; cbn [Z.b2z].
        -
          zstep. if_false.
          ihere. to_implM. unfold bret. cbn [ret tree_ops embed interp]. apply implM_interp_ret. apply evt_done.
          unfold SHQ. exists m1, OWK. do 18 eexists. split; [reflexivity|]. cbn [fst snd].
          split; [exact ENV1|]. split; [exact LS1|]. split; [apply refs_stable_refl|]. clear - SH0. lia.
        -
          zstep. if_true. zstep. zstep. rewrite (bn_swrap32_small (shift + 1)) by (clear - SH0 SHF; change (2^30) with 1073741824 in SHF; lia). if_cases KC; [zify_cond KC; rewrite !zb_signed, !unsigned_lit in KC by (clear - SH0 SHF; change (2^30) with 1073741824 in SHF; lia); exfalso; revert KC; clear - SH0 SHF; change (2^30) with 1073741824 in SHF; destruct (Z.ltb_spec (shift + 1) (2^63)), (Z.ltb_spec shift (2^63)); lia|]. do 3 zstep.
          eapply KODD; [exact ENV1 | exact LS1 | exact HAX | exact (proj1 HPX) |].
          intros m2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV2 LS2. clear ENV1 LS1.
          retpc 1081276.
          destruct (is_odd_pure (getbn rX bsK)) eqn:EO; cbn [Z.b2z].
          + zstep. if_false. do 4 zstep. ihere. to_implM.
            eapply KCALL; [exact ENV2 | exact LS2
              | intros errv PRE; apw W_uadd.BN_uadd_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_UADD) | reflexivity | exact HAX | exact HPX | exact HAX | exact (proj1 HPX)
                                                        | exact HAN | exact NROn | reflexivity | reflexivity | reflexivity]
              | hres |].
            intros u st3 bs3 m3 OW3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV3 LS3 RS3 RES3. hnf in RES3. destruct RES3 as (_ & -> & _). unfold MallocRep.wz.
            retpc 1081296.
            unfold implM. iprefix. zstep. if_false. ihere. to_implM.
            eapply JOIN; [exact ENV3 | exact LS3 | exact RS3].
          + zstep. if_true. ihere. to_implM. rewrite bbind_ret.
            eapply JOIN; [exact ENV2 | exact LS2 | apply refs_stable_refl].
      Qed.

      Lemma shift2_loop : forall f shift stK bsK mK OWK
          (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 x26 t3 t4 t5 t6 : word),
        KENV IFR stK bsK mK OWK -> lib_state bsK mK OWK PL EA -> IREFS bsK OWK ->
        0 <= shift -> shift + Z.of_nat f < 2^30 ->
        implM bgusegs (interp (embed (inv_shift_loop ops f rA rY rn shift bsK))) stK (SHQ 0x107fec bsK OWK shift (shift + Z.of_nat f))
          (IMS rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 shift) (Z_to_bv 64 aX) x23 x26 t3 t4 t5 t6 0x107f58 mK).
      Proof.
        induction f as [|f IH]; intros until t6; intros ENVK LSK IR SH0 SHF.
        { rewrite shl_O. unfold bunr. cbn [unreachable tree_ops embed interp]. apply implM_interp_unr. }
        pose proof IR as (HAA & HAB & HAX & HAY & HAN & HAR).
        pose proof SPR2 as SPR. pose proof ESPF as ESP. pose proof GLO' as GLO2. unfold GLOBALS_TOP in GLO2.
        rewrite shl_S.
        unfold implM. iprefix. do 3 zstep.
        eapply KBIT; [exact ENVK | exact LSK | exact HAA | exact (proj1 HPA) | clear - SH0 SHF; lia |].
        intros m1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV1 LS1. clear ENVK LSK.
        retpc 1081188.
        assert (JOIN : forall stJ bsJ mJ OWJ (rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
                  KENV IFR stJ bsJ mJ OWJ -> lib_state bsJ mJ OWJ PL EA -> refs_stable bsK OWK bsJ OWJ ->
                  implM bgusegs (interp (embed (bbind ops (BN_rshift1 ops rY rY) (fun _ => inv_shift_loop ops f rA rY rn (shift + 1)) bsJ))) stJ
                    (SHQ 0x107fec bsK OWK shift (shift + Z.of_nat (S f)))
                    (IMS rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 shift) (Z_to_bv 64 aX) (Z_to_bv 64 (shift + 1)) x26 t3' t4' t5' t6' 0x107f90 mJ)).
        { intros until t6'. intros ENVJ LSJ RSJ.
          pose proof (irefs_stable _ _ _ _ IR RSJ) as IRJ. pose proof IRJ as (HAAj & HABj & HAXj & HAYj & HANj & HARj).
          unfold implM. iprefix. do 3 zstep. ihere. to_implM.
          eapply KCALL; [exact ENVJ | exact LSJ
            | intros errv PRE; apw W_rshift1.BN_rshift1_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_RSH1) | reflexivity | exact HAYj | exact (hpl_wref PL rY HPY) | reflexivity | reflexivity]
            | hres |].
          intros u st2 bs2 m2 OW2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV2 LS2 RS2 RES2. hnf in RES2. destruct RES2 as (_ & -> & _). unfold MallocRep.wz.
          retpc 1081244.
          unfold implM. iprefix. zstep. zstep. if_true.
          ihere. to_implM.
          eapply implM_mono.
          { eapply IH; [exact ENV2 | exact LS2 | exact (irefs_stable _ _ _ _ IRJ RS2) | clear - SH0; lia | clear - SHF; rewrite Nat2Z.inj_succ in SHF; lia]. }
          cbv beta. intros r st' ms' (mK' & OWK' & R).
          destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & E & K1 & K2 & K3 & K4).
          unfold SHQ. exists mK', OWK'. do 18 eexists. split; [exact E|]. split; [exact K1|]. split; [exact K2|].
          split; [eapply refs_stable_trans; [exact RSJ| eapply refs_stable_trans; [exact RS2| exact K3]]|].
          clear - K4. rewrite Nat2Z.inj_succ. lia. }
        destruct (is_bit_set_pure (getbn rA bsK) shift) eqn:EB; cbn [Z.b2z].
        -
          zstep. if_true.
          ihere. to_implM. unfold bret. cbn [ret tree_ops embed interp]. apply implM_interp_ret. apply evt_done.
          unfold SHQ. exists m1, OWK. do 18 eexists. split; [reflexivity|]. cbn [fst snd].
          split; [exact ENV1|]. split; [exact LS1|]. split; [apply refs_stable_refl|]. clear - SH0. lia.
        - zstep. if_false. zstep. zstep. rewrite (bn_swrap32_small (shift + 1)) by (clear - SH0 SHF; change (2^30) with 1073741824 in SHF; lia). if_cases KC; [zify_cond KC; rewrite !zb_signed, !unsigned_lit in KC by (clear - SH0 SHF; change (2^30) with 1073741824 in SHF; lia); exfalso; revert KC; clear - SH0 SHF; change (2^30) with 1073741824 in SHF; destruct (Z.ltb_spec (shift + 1) (2^63)), (Z.ltb_spec shift (2^63)); lia|]. do 2 zstep.
          eapply KODD; [exact ENV1 | exact LS1 | exact HAY | exact (proj1 HPY) |].
          intros m2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV2 LS2. clear ENV1 LS1.
          retpc 1081208.
          destruct (is_odd_pure (getbn rY bsK)) eqn:EO; cbn [Z.b2z].
          + zstep. if_false. do 4 zstep. ihere. to_implM.
            eapply KCALL; [exact ENV2 | exact LS2
              | intros errv PRE; apw W_uadd.BN_uadd_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_UADD) | reflexivity | exact HAY | exact HPY | exact HAY | exact (proj1 HPY)
                                                        | exact HAN | exact NROn | reflexivity | reflexivity | reflexivity]
              | hres |].
            intros u st3 bs3 m3 OW3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV3 LS3 RS3 RES3. hnf in RES3. destruct RES3 as (_ & -> & _). unfold MallocRep.wz.
            retpc 1081228.
            unfold implM. iprefix. zstep. if_false. ihere. to_implM.
            eapply JOIN; [exact ENV3 | exact LS3 | exact RS3].
          + zstep. if_true. ihere. to_implM. rewrite bbind_ret.
            eapply JOIN; [exact ENV2 | exact LS2 | apply refs_stable_refl].
      Qed.

      Definition XQ (pcq : Z) (bsK : ST) (OWK : list block) (r : unit * ST) (st' : PState) (ms' : machine_state) : Prop :=
        exists mK' OWK' (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x23 x26 t3 t4 t5 t6 : word),
          ms' = IMS rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 aX) x23 x26 t3 t4 t5 t6 pcq mK'
          /\ KENV IFR st' (snd r) mK' OWK' /\ lib_state (snd r) mK' OWK' PL EA /\ refs_stable bsK OWK (snd r) OWK'.

      Definition inv_iter_k {C : Type} (K : BM (M := btree bptr) C) (nb : Z) : BM (M := btree bptr) C :=
        bbind ops (inv_shift_loop ops (Z.to_nat nb + 1) rB rX rn 0) (fun shift =>
        bbind ops (if 0 <? shift then BN_rshift ops rB rB shift else bret ops tt) (fun _ =>
        bbind ops (bget ops rA) (fun a =>
        bbind ops (inv_shift_loop ops (Z.to_nat (num_bits_pure a) + 1) rA rY rn 0) (fun shift =>
        bbind ops (if 0 <? shift then BN_rshift ops rA rA shift else bret ops tt) (fun _ =>
        bbind ops (BN_ucmp ops rB rA) (fun c =>
        bbind ops (if 0 <=? c then bbind ops (BN_uadd ops rX rX rY) (fun _ => BN_usub ops rB rB rA)
                   else bbind ops (BN_uadd ops rY rY rX) (fun _ => BN_usub ops rA rA rB)) (fun _ => K))))))).

      Lemma bin_O : forall (bsK : ST), inv_binary_loop ops 0 rA rB rX rY rn bsK = bunr ops bsK.
      Proof. reflexivity. Qed.
      Lemma bin_S : forall f (bsK : ST),
        inv_binary_loop ops (S f) rA rB rX rY rn bsK =
        if is_zero_pure (getbn rB bsK) then bret ops tt bsK
        else inv_iter_k (inv_binary_loop ops f rA rB rX rY rn) (num_bits_pure (getbn rB bsK)) bsK.
      Proof. intros. cbn [inv_binary_loop]. rewrite bbind_get. destruct (is_zero_pure (getbn rB bsK)); reflexivity. Qed.

      Lemma nbits_range : forall b : bignum bptr, bg_ok b -> 0 <= num_bits_pure b <= 32768.
      Proof.
        intros b (LIM & TD & DM & _). unfold BG_DMAX in DM. unfold num_bits_pure.
        destruct (Nat.eqb_spec (bn_top b) 0) as [E|NE]; [lia|].
        pose proof (limbs_nth (bn_buf b) (bn_top b - 1) LIM) as LN. unfold limb, BW in LN.
        pose proof (BnDivWords.num_bits_word_le (nth (bn_top b - 1) (bn_buf b) 0) 64 ltac:(lia) LN). unfold bn_dmax in *. lia.
      Qed.

      Lemma iter_body : forall {C : Type} (K : BM (M := btree bptr) C) (Q : C * ST -> PState -> machine_state -> Prop) nb stK bsK mK OWK
          (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 x26 t3 t4 t5 t6 : word),
        KENV IFR stK bsK mK OWK -> lib_state bsK mK OWK PL EA -> IREFS bsK OWK -> 0 <= nb <= 32768 ->
        (forall stJ bsJ mJ OWJ (rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x18' x23' x26' t3' t4' t5' t6' : word),
            KENV IFR stJ bsJ mJ OWJ -> lib_state bsJ mJ OWJ PL EA -> refs_stable bsK OWK bsJ OWJ ->
            implM bgusegs (interp (embed (K bsJ))) stJ Q
              (IMS rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x18' (Z_to_bv 64 aX) x23' x26' t3' t4' t5' t6' 0x108060 mJ)) ->
        implM bgusegs (interp (embed (inv_iter_k K nb bsK))) stK Q
          (IMS rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 aX) x23 x26 t3 t4 t5 t6 0x107f2c mK).
      Proof.
        intros until t6. intros ENVK LSK IR NB KK.
        pose proof SPR2 as SPR. pose proof ESPF as ESP. pose proof GLO' as GLO2. unfold GLOBALS_TOP in GLO2.
        unfold inv_iter_k.

        assert (J3 : forall st3 bs3 m3 OW3 (rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x18' x23' x26' t3' t4' t5' t6' : word),
                  KENV IFR st3 bs3 m3 OW3 -> lib_state bs3 m3 OW3 PL EA -> refs_stable bsK OWK bs3 OW3 ->
                  implM bgusegs (interp (embed (
                      bbind ops (BN_ucmp ops rB rA) (fun c =>
                      bbind ops (if 0 <=? c then bbind ops (BN_uadd ops rX rX rY) (fun _ => BN_usub ops rB rB rA)
                                 else bbind ops (BN_uadd ops rY rY rX) (fun _ => BN_usub ops rA rA rB)) (fun _ => K)) bs3))) st3 Q
                    (IMS rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x18' (Z_to_bv 64 aX) x23' x26' t3' t4' t5' t6' 0x108004 m3)).
        { intros until t6'. intros ENV3 LS3 RS3.
          pose proof (irefs_stable _ _ _ _ IR RS3) as IR3. pose proof IR3 as (HAA & HAB & HAX & HAY & HAN & HAR).
          unfold implM. iprefix. do 3 zstep. ihere. to_implM.
          eapply KCALL; [exact ENV3 | exact LS3
            | intros errv PRE; apw W_cmp.BN_ucmp_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_UCMP) | reflexivity | exact HAB | exact HAA
                                                     | exact (proj1 HPB) | exact (proj1 HPA) | reflexivity | reflexivity]
            | intros ? ? ? ? ? HRES; exact (proj1 (proj1 HRES)) |].
          intros c st4 bs4 m4 OW4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV4 LS4 RS4 RES4. destruct RES4 as ((_ & -> & CR & _ & _) & _).
          pose proof (irefs_stable _ _ _ _ IR3 RS4) as IR4. pose proof IR4 as (HAA4 & HAB4 & HAX4 & HAY4 & HAN4 & HAR4).
          retpc 1081360.
          eapply implM_embed_bind with (Q1 := XQ 0x108060 bs4 OW4).
          2:{ cbv beta. intros [u bs5] st5 ms5 (m5 & OW5 & R).
              destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & ENV5 & LS5 & RS5). cbn [fst snd] in *.
              eapply KK; [exact ENV5 | exact LS5 | eapply refs_stable_trans; [exact RS3| eapply refs_stable_trans; [exact RS4| exact RS5]]]. }
          unfold implM. iprefix.
          zstep. rewrite lts_signed by (clear - CR; lia).
          destruct (Z.ltb_spec c 0) as [CN|CP]; cbn [negb].
          -
            replace (0 <=? c) with false by (symmetry; apply Z.leb_gt; exact CN).
            pose proof ENV4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FRY & _). unfold ifr, ifr_i, saved_i, ifr_w, saved_w in FRY. cbn [app] in FRY. do 4 zstep. clear FRY. ihere. to_implM.
            eapply KCALL; [exact ENV4 | exact LS4
              | intros errv PRE; apw W_uadd.BN_uadd_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_UADD) | reflexivity | exact HAY4 | exact HPY | exact HAY4 | exact (proj1 HPY)
                                                        | exact HAX4 | exact (proj1 HPX) | reflexivity | reflexivity | reflexivity]
              | hres |].
            intros u st6 bs6 m6 OW6 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV6 LS6 RS6 RES6. hnf in RES6. destruct RES6 as (_ & -> & _). unfold MallocRep.wz.
            pose proof (irefs_stable _ _ _ _ IR4 RS6) as IR6. pose proof IR6 as (HAA6 & HAB6 & HAX6 & HAY6 & HAN6 & HAR6).
            retpc 1081416.
            unfold implM. iprefix. zstep. if_false. do 4 zstep. ihere. to_implM.
            eapply (KCALLE _ _ (XQ 0x108060 bs4 OW4)); [exact ENV6 | exact LS6
              | intros errv PRE; apw W_usub.BN_usub_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_USUB) | reflexivity | exact HAA6 | exact HPA | exact HAA6 | exact (proj1 HPA)
                                                        | exact HAB6 | exact (proj1 HPB) | reflexivity | reflexivity | reflexivity]
              | hres |].
            intros u' st7 bs7 m7 OW7 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV7 LS7 RS7 RES7. hnf in RES7. destruct RES7 as (_ & -> & _). unfold MallocRep.wz.
            retpc 1081436.
            zstep. if_false.
            apply evt_done. unfold XQ. exists m7, OW7. do 19 eexists. split; [reflexivity|]. cbn [fst snd].
            split; [exact ENV7|]. split; [exact LS7|]. eapply refs_stable_trans; [exact RS6| exact RS7].
          -
            replace (0 <=? c) with true by (symmetry; apply Z.leb_le; exact CP).
            pose proof ENV4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FRY & _). unfold ifr, ifr_i, saved_i, ifr_w, saved_w in FRY. cbn [app] in FRY. do 4 zstep. clear FRY. ihere. to_implM.
            eapply KCALL; [exact ENV4 | exact LS4
              | intros errv PRE; apw W_uadd.BN_uadd_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_UADD) | reflexivity | exact HAX4 | exact HPX | exact HAX4 | exact (proj1 HPX)
                                                        | exact HAY4 | exact (proj1 HPY) | reflexivity | reflexivity | reflexivity]
              | hres |].
            intros u st6 bs6 m6 OW6 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV6 LS6 RS6 RES6. hnf in RES6. destruct RES6 as (_ & -> & _). unfold MallocRep.wz.
            pose proof (irefs_stable _ _ _ _ IR4 RS6) as IR6. pose proof IR6 as (HAA6 & HAB6 & HAX6 & HAY6 & HAN6 & HAR6).
            retpc 1081380.
            unfold implM. iprefix. zstep. if_false. do 5 zstep. ihere. to_implM.
            eapply (KCALLE _ _ (XQ 0x108060 bs4 OW4)); [exact ENV6 | exact LS6
              | intros errv PRE; apw W_usub.BN_usub_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_USUB) | reflexivity | exact HAB6 | exact HPB | exact HAB6 | exact (proj1 HPB)
                                                        | exact HAA6 | exact (proj1 HPA) | reflexivity | reflexivity | reflexivity]
              | hres |].
            intros u' st7 bs7 m7 OW7 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV7 LS7 RS7 RES7. hnf in RES7. destruct RES7 as (_ & -> & _). unfold MallocRep.wz.
            retpc 1081436.
            zstep. if_false.
            apply evt_done. unfold XQ. exists m7, OW7. do 19 eexists. split; [reflexivity|]. cbn [fst snd].
            split; [exact ENV7|]. split; [exact LS7|]. eapply refs_stable_trans; [exact RS6| exact RS7]. }

        assert (J2 : forall st2 bs2 m2 OW2 (rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x18' x23' x26' t3' t4' t5' t6' : word),
                  KENV IFR st2 bs2 m2 OW2 -> lib_state bs2 m2 OW2 PL EA -> refs_stable bsK OWK bs2 OW2 ->
                  implM bgusegs (interp (embed (
                      bbind ops (bget ops rA) (fun a =>
                      bbind ops (inv_shift_loop ops (Z.to_nat (num_bits_pure a) + 1) rA rY rn 0) (fun shift =>
                      bbind ops (if 0 <? shift then BN_rshift ops rA rA shift else bret ops tt) (fun _ =>
                      bbind ops (BN_ucmp ops rB rA) (fun c =>
                      bbind ops (if 0 <=? c then bbind ops (BN_uadd ops rX rX rY) (fun _ => BN_usub ops rB rB rA)
                                 else bbind ops (BN_uadd ops rY rY rX) (fun _ => BN_usub ops rA rA rB)) (fun _ => K))))) bs2))) st2 Q
                    (IMS rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x18' (Z_to_bv 64 aX) x23' x26' t3' t4' t5' t6' 0x107f54 m2)).
        { intros until t6'. intros ENV2 LS2 RS2.
          pose proof (irefs_stable _ _ _ _ IR RS2) as IR2. pose proof IR2 as (HAA & HAB & HAX & HAY & HAN & HAR).
          rewrite bbind_get.
          destruct (kenv_open LB PL EA lo B SPv FB s bs OW m CEIL FROK _ _ _ _ _ rA aA ENV2 LS2 HAA (proj1 HPA)) as (DA & _ & _ & OKA & _).
          pose proof (nbits_range _ OKA) as NBA. clear OKA DA.
          unfold implM. iprefix. zstep. ihere. to_implM.
          unfold bbind at 1. cbn [bind tree_ops]. eapply implM_embed_bind.
          { eapply (shift2_loop (Z.to_nat (num_bits_pure (getbn rA bs2)) + 1) 0); [exact ENV2 | exact LS2 | exact IR2 | clear; lia
              | clear - NBA; change (2^30) with 1073741824; lia]. }
          cbv beta. intros [sh bs3] st3 ms3 (m3 & OW3 & R).
          destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & ENV3 & LS3 & RS3 & SHR). cbn [fst snd] in *.
          pose proof (irefs_stable _ _ _ _ IR2 RS3) as IR3. pose proof IR3 as (HAA3 & HAB3 & HAX3 & HAY3 & HAN3 & HAR3).
          assert (SH30 : 0 <= sh < 2^30) by (clear - SHR NBA; change (2^30) with 1073741824; lia).
          unfold implM. iprefix.
          zstep. if_cases KS; rewrite ?unsigned_lit in KS by (clear - SH30; change (2^30) with 1073741824 in SH30; lia); zify_cond KS.
          -
            replace (0 <? sh) with false by (symmetry; apply Z.ltb_ge; apply andb_false_iff in KS; rewrite !Z.ltb_ge in KS; clear - KS SH30; lia).
            ihere. to_implM. rewrite bbind_ret.
            eapply J3; [exact ENV3 | exact LS3 | eapply refs_stable_trans; [exact RS2| exact RS3]].
          - replace (0 <? sh) with true by (symmetry; apply Z.ltb_lt; lia).
            do 4 zstep. ihere. to_implM.
            eapply KCALL; [exact ENV3 | exact LS3
              | intros errv PRE; apw W_shift.BN_rshift_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_RSH) | reflexivity | exact HAA3 | exact HPA | exact HAA3 | exact (proj1 HPA)
                                                           | reflexivity | reflexivity | reflexivity | clear - SH30; change (2^31) with 2147483648; lia]
              | hres |].
            intros u st4 bs4 m4 OW4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV4 LS4 RS4 RES4. hnf in RES4. destruct RES4 as (_ & -> & _). unfold MallocRep.wz.
            retpc 1081344.
            unfold implM. iprefix. zstep. if_false. ihere. to_implM.
            eapply J3; [exact ENV4 | exact LS4 | eapply refs_stable_trans; [exact RS2| eapply refs_stable_trans; [exact RS3| exact RS4]]]. }

        pose proof IR as (HAA & HAB & HAX & HAY & HAN & HAR).
        unfold bbind at 1. cbn [bind tree_ops]. eapply implM_embed_bind.
        { eapply (shift1_loop (Z.to_nat nb + 1) 0); [exact ENVK | exact LSK | exact IR | clear; lia | clear - NB; change (2^30) with 1073741824; lia]. }
        cbv beta. intros [sh bs1] st1 ms1 (m1 & OW1 & R).
        destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & ENV1 & LS1 & RS1 & SHR). cbn [fst snd] in *.
        pose proof (irefs_stable _ _ _ _ IR RS1) as IR1. pose proof IR1 as (HAA1 & HAB1 & HAX1 & HAY1 & HAN1 & HAR1).
        assert (SH30 : 0 <= sh < 2^30) by (clear - SHR NB; change (2^30) with 1073741824; lia).
        unfold implM. iprefix.
        zstep. if_cases KS; rewrite ?unsigned_lit in KS by (clear - SH30; change (2^30) with 1073741824 in SH30; lia); zify_cond KS.
        - replace (0 <? sh) with false by (symmetry; apply Z.ltb_ge; apply andb_false_iff in KS; rewrite !Z.ltb_ge in KS; clear - KS SH30; lia).
          ihere. to_implM. rewrite bbind_ret.
          eapply J2; [exact ENV1 | exact LS1 | exact RS1].
        - replace (0 <? sh) with true by (symmetry; apply Z.ltb_lt; lia).
          do 4 zstep. ihere. to_implM.
          eapply KCALL; [exact ENV1 | exact LS1
            | intros errv PRE; apw W_shift.BN_rshift_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_RSH) | reflexivity | exact HAB1 | exact HPB | exact HAB1 | exact (proj1 HPB)
                                                         | reflexivity | reflexivity | reflexivity | clear - SH30; change (2^31) with 2147483648; lia]
            | hres |].
          intros u st2 bs2 m2 OW2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV2 LS2 RS2 RES2. hnf in RES2. destruct RES2 as (_ & -> & _). unfold MallocRep.wz.
          retpc 1081168.
          unfold implM. iprefix. zstep. if_false. ihere. to_implM.
          eapply J2; [exact ENV2 | exact LS2 | eapply refs_stable_trans; [exact RS1| exact RS2]].
      Qed.

      Lemma bin_check : forall f stK bsK mK OWK
          (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x23 x26 t3 t4 t5 t6 : word),
        KENV IFR stK bsK mK OWK -> lib_state bsK mK OWK PL EA -> IREFS bsK OWK ->
        implM bgusegs (interp (embed (inv_binary_loop ops f rA rB rX rY rn bsK))) stK (ANYQ 0x108198 bsK OWK)
          (IMS rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 aX) x23 x26 t3 t4 t5 t6 0x108060 mK).
      Proof.
        induction f as [|f IH]; intros until t6; intros ENVK LSK IR.
        { rewrite bin_O. unfold bunr. cbn [unreachable tree_ops embed interp]. apply implM_interp_unr. }
        pose proof IR as (HAA & HAB & HAX & HAY & HAN & HAR).
        pose proof SPR2 as SPR. pose proof ESPF as ESP. pose proof GLO' as GLO2. unfold GLOBALS_TOP in GLO2.
        rewrite bin_S.
        unfold implM. iprefix. do 2 zstep.
        eapply KZERO; [exact ENVK | exact LSK | exact HAB | exact (proj1 HPB) |].
        intros m1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV1 LS1.
        retpc 1081448.
        zstep. pose proof ENV1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FRY & _). unfold ifr, ifr_i, saved_i, ifr_w, saved_w in FRY. cbn [app] in FRY. zstep. clear FRY.
        destruct (is_zero_pure (getbn rB bsK)) eqn:EZ; cbn [Z.b2z].
        - zstep. if_true.
          ihere. to_implM. unfold bret. cbn [ret tree_ops embed interp]. apply implM_interp_ret. apply evt_done.
          unfold ANYQ. exists m1, OWK. do 20 eexists. split; [reflexivity|]. cbn [fst snd].
          split; [exact ENV1|]. split; [exact LS1|]. apply refs_stable_refl.
        - zstep. if_false. zstep.
          destruct (kenv_open LB PL EA lo B SPv FB s bs OW m CEIL FROK _ _ _ _ _ rB aB ENV1 LS1 HAB (proj1 HPB)) as (DB & _ & _ & OKB & _).
          pose proof (nbits_range _ OKB) as NBB. clear OKB DB.
          ihere. to_implM.
          eapply iter_body; [exact ENV1 | exact LS1 | exact IR | exact NBB |].
          intros until t6'. intros ENVJ LSJ RSJ.
          eapply implM_mono; [eapply IH; [exact ENVJ | exact LSJ | exact (irefs_stable _ _ _ _ IR RSJ)]|].
          cbv beta. intros r st' ms' (mK' & OWK' & R).
          destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & E & K1 & K2 & K3).
          unfold ANYQ. exists mK', OWK'. do 20 eexists. split; [exact E|]. split; [exact K1|]. split; [exact K2|].
          eapply refs_stable_trans; [exact RSJ| exact K3].
      Qed.

      Lemma ucmp_eq : forall r1 r2 (bsK : ST), bg_ok (getbn r1 bsK) -> bg_ok (getbn r2 bsK) ->
        BN_ucmp ops r1 r2 bsK = bret ops (ucmp_pure (getbn r1 bsK) (getbn r2 bsK)) bsK.
      Proof.
        intros r1 r2 bsK (_ & _ & _ & FLA) (_ & _ & _ & FLB).
        unfold BN_ucmp. rewrite !bbind_get. unfold has_flag.
        assert (EL4A : Z.land (bn_flags (getbn r1 bsK)) BN_FLG_CONSTTIME = 0) by (destruct FLA as [E|E]; rewrite E; reflexivity).
        assert (EL4B : Z.land (bn_flags (getbn r2 bsK)) BN_FLG_CONSTTIME = 0) by (destruct FLB as [E|E]; rewrite E; reflexivity).
        rewrite EL4A, EL4B. reflexivity.
      Qed.

      Lemma ucmp_bind_eq : forall {C : Type} r1 r2 (K : Z -> BM (M := btree bptr) C) (bsK : ST), bg_ok (getbn r1 bsK) -> bg_ok (getbn r2 bsK) ->
        bbind ops (BN_ucmp ops r1 r2) K bsK = K (ucmp_pure (getbn r1 bsK) (getbn r2 bsK)) bsK.
      Proof. intros C r1 r2 K bsK O1 O2. unfold bbind at 1. rewrite (ucmp_eq r1 r2 bsK O1 O2). reflexivity. Qed.

      Lemma inv_fin : forall stK bsK mK OWK
          (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x22 x23 x26 t3 t4 t5 t6 : word),
        KENV IFR stK bsK mK OWK -> lib_state bsK mK OWK PL EA -> IREFS bsK OWK ->
        implM bgusegs (interp (embed (
            bbind ops (BN_sub ops rY rn rY) (fun _ =>
            bbind ops (bget ops rA) (fun bA =>
            bbind ops (if is_one_pure bA then
                         bbind ops (bget ops rY) (fun y => bbind ops (BN_ucmp ops rY rn) (fun c =>
                         if negb (bn_neg y) && (c <? 0) then BN_copy ops rR rY else BN_nnmod ops rR rY rn))
                       else bunr ops) (fun _ => BN_CTX_end ops))) bsK))) stK FINALQ
          (IMS rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x22 x23 x26 t3 t4 t5 t6 0x108198 mK).
      Proof.
        intros until t6. intros ENVK LSK IR.
        pose proof IR as (HAA & HAB & HAX & HAY & HAN & HAR).
        pose proof SPR2 as SPR. pose proof ESPF as ESP. pose proof GLO' as GLO2. unfold GLOBALS_TOP in GLO2.
        unfold implM. iprefix. do 5 zstep. ihere. to_implM.
        eapply KCALL; [exact ENVK | exact LSK
          | intros errv PRE; apw W_sub.BN_sub_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_SUB) | reflexivity | exact HAY | exact HPY | exact HAN | exact NROn
                                                   | exact HAY | exact (proj1 HPY) | reflexivity | reflexivity | reflexivity]
          | hres |].
        intros u st1 bs1 m1 OW1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV1 LS1 RS1 RES1. hnf in RES1. destruct RES1 as (_ & ->). unfold MallocRep.wz.
        pose proof (irefs_stable _ _ _ _ IR RS1) as IR1. pose proof IR1 as (HAA1 & HAB1 & HAX1 & HAY1 & HAN1 & HAR1).
        retpc 1081772.
        rewrite bbind_get.
        destruct (is_one_pure (getbn rA bs1)) eqn:E1.
        2:{ unfold bbind, bunr. cbn [bind unreachable tree_ops tbind embed interp]. apply implM_interp_unr. }
        eapply implM_embed_bind with (Q1 := @ANYQ unit 0x108098 bs1 OW1).
        2:{ cbv beta. intros [u2 bs5] st5 ms5 (m5 & OW5 & R).
            destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & ENV5 & LS5 & RS5). cbn [fst snd] in *.
            eapply implM_mono; [eapply inv_exit; [exact ENV5 | exact LS5]|].
            cbv beta. intros r st' ms' H. exact H. }
        rewrite bbind_get.
        unfold implM. iprefix. zstep. if_false. do 2 zstep.
        eapply KONE; [exact ENV1 | exact LS1 | exact HAA1 | exact (proj1 HPA) |].
        intros m2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV2 LS2. clear ENV1 LS1.
        retpc 1081784. rewrite E1. cbn [Z.b2z].
        zstep. if_false.
        destruct (kenv_open LB PL EA lo B SPv FB s bs OW m CEIL FROK _ _ _ _ _ rY aY ENV2 LS2 HAY1 (proj1 HPY)) as (DY & BNY & _ & OKY & AY0 & SEPY & _).
        destruct (kenv_open LB PL EA lo B SPv FB s bs OW m CEIL FROK _ _ _ _ _ rn an ENV2 LS2 HAN1 NROn) as (DN & _ & _ & OKN & _).
        unfold bn_cells, MallocRep.wz in BNY.
        assert (AYR : 0 < aY < 2^64 /\ aY mod 8 = 0).
        { pose proof ENV2 as (HEAP2 & _). pose proof (lib_state_h_parts _ _ _ _ _ _ LS2) as PARTS2.
          pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 FROK HAY1 (proj1 HPY)) as (A0 & AC & AI).
          pose proof (OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU.BnUAlign.ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP2 PARTS2 HAY1 (proj1 HPY)) as (_ & A8).
          split; [split; [exact A0| clear - AC AI; lia] | exact A8]. }
        zstep. if_cases K0; rewrite ?unsigned_lit in K0 by (clear - AYR; lia); zify_cond K0; [exfalso; clear - K0 AYR; lia| clear K0].
        zstep.
        zstep. if_cases K1; rewrite ?unsigned_lit in K1 by (clear - AYR; lia); zify_cond K1.
        { exfalso. change 7 with (2^3 - 1) in K1. rewrite zb_land_mask in K1 by lia. clear - K1 AYR. lia. }
        clear K1.
        zstep. clear BNY DY DN AY0 SEPY.
        assert (NN : forall st3 m3 (rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x18' x22' x23' x26' t3' t4' t5' t6' : word),
                  KENV IFR st3 bs1 m3 OW1 -> lib_state bs1 m3 OW1 PL EA ->
                  implM bgusegs (interp (embed (BN_nnmod ops rR rY rn bs1))) st3 (@ANYQ unit 0x108098 bs1 OW1)
                    (IMS rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x18' x22' x23' x26' t3' t4' t5' t6' 0x1081e0 m3)).
        { intros until t6'. intros ENV3 LS3.
          unfold implM. iprefix. do 5 zstep. ihere. to_implM.
          eapply (KCALLE _ _ (@ANYQ unit 0x108098 bs1 OW1)); [exact ENV3 | exact LS3
            | intros errv PRE; eapply BN_nnmod_walk; [exact PRE | reflexivity | exact HAR1 | exact HAY1 | exact HAN1 | exact WRR | exact (proj1 HPY) | exact NROn | exact HPC
                                                   | reflexivity | reflexivity | reflexivity | reflexivity]
            | hres |].
          intros u' st7 bs7 m7 OW7 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV7 LS7 RS7 RES7. hnf in RES7. destruct RES7 as (_ & ->). unfold MallocRep.wz.
          retpc 1081844.
          pose proof ENV7 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FR7 & _).
          unfold ifr, ifr_i, ifr_w, saved_i, saved_w in FR7. cbn [app] in FR7.
          zstep. clear FR7. zstep. if_false. zstep.
          apply evt_done. unfold ANYQ. exists m7, OW7. do 20 eexists. split; [reflexivity|]. cbn [fst snd].
          split; [exact ENV7|]. split; [exact LS7| exact RS7]. }
        destruct (bn_neg (getbn rY bs1)) eqn:EN; cbn [Z.b2z negb andb].
        -
          zstep. if_true.
          ihere. to_implM. rewrite (ucmp_bind_eq rY rn _ bs1 OKY OKN). cbn [negb andb].
          eapply NN; [exact ENV2 | exact LS2].
        - zstep. if_false. do 3 zstep. ihere. to_implM.
          eapply KCALL; [exact ENV2 | exact LS2
            | intros errv PRE; apw W_cmp.BN_ucmp_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_UCMP) | reflexivity | exact HAY1 | exact HAN1
                                                     | exact (proj1 HPY) | exact NROn | reflexivity | reflexivity]
            | intros ? ? ? ? ? HRES; exact (proj1 (proj1 HRES)) |].
          intros c st4 bs4 m4 OW4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV4 LS4 RS4 RES4. destruct RES4 as ((_ & -> & CR & -> & ->) & _).
          retpc 1081820.
          unfold implM. iprefix.
          zstep. rewrite lts_signed by (clear - CR; lia).
          destruct (Z.ltb_spec c 0) as [CN|CP]; cbn [negb].
          +
            do 3 zstep. ihere. to_implM.
            eapply (KCALLE _ _ (@ANYQ unit 0x108098 bs1 OW1)); [exact ENV4 | exact LS4
              | intros errv PRE; apw W_copy.BN_copy_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_COPY) | reflexivity | exact HAR1 | exact HAY1 | exact (hpl_wref PL rR WRR)
                                                        | exact (proj1 HPY) | reflexivity | reflexivity]
              | hres |].
            intros u' st7 bs7 m7 OW7 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV7 LS7 RS7 RES7. hnf in RES7. destruct RES7 as (_ & -> & _). unfold MallocRep.wz.
            retpc 1082616.
            pose proof ENV7 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FR7 & _).
            unfold ifr, ifr_i, ifr_w, saved_i, saved_w in FR7. cbn [app] in FR7.
            zstep. zstep. clear FR7. zstep. if_cases KR; rewrite ?unsigned_lit in KR by (clear - ARR; lia); zify_cond KR. { exfalso. clear - KR ARR. lia. }
            zstep.
            apply evt_done. unfold ANYQ. exists m7, OW7. do 20 eexists. split; [reflexivity|]. cbn [fst snd].
            split; [exact ENV7|]. split; [exact LS7| exact RS7].
          + ihere. to_implM. eapply NN; [exact ENV4 | exact LS4].
      Qed.

      Lemma bin_top : forall f stK bsK mK OWK
          (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x23 x26 t3 t4 t5 t6 : word),
        KENV IFR stK bsK mK OWK -> lib_state bsK mK OWK PL EA -> IREFS bsK OWK ->
        implM bgusegs (interp (embed (inv_binary_loop ops (S f) rA rB rX rY rn bsK))) stK (ANYQ 0x108198 bsK OWK)
          (IMS rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 aX) x22 x23 x26 t3 t4 t5 t6 0x107f14 mK).
      Proof.
        intros until t6. intros ENVK LSK IR.
        pose proof IR as (HAA & HAB & HAX & HAY & HAN & HAR).
        pose proof SPR2 as SPR. pose proof ESPF as ESP. pose proof GLO' as GLO2. unfold GLOBALS_TOP in GLO2.
        rewrite bin_S.
        unfold implM. iprefix. do 2 zstep.
        eapply KZERO; [exact ENVK | exact LSK | exact HAB | exact (proj1 HPB) |].
        intros m1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV1 LS1.
        retpc 1081116. pose proof ENV1 as (HEAP1 & AUX1 & ST1 & (errv1 & ERR1) & MI1 & LXP1 & FA1 & SO1 & RSE1 & FR1 & FSZ1). unfold ifr, ifr_i, ifr_w, saved_i, saved_w in FR1. cbn [app] in FR1.
        destruct (is_zero_pure (getbn rB bsK)) eqn:EZ; cbn [Z.b2z].
        - zstep. zstep. if_true.
          ihere. to_implM. unfold bret. cbn [ret tree_ops embed interp]. apply implM_interp_ret. apply evt_done.
          unfold ANYQ. exists m1, OWK. do 20 eexists. split; [reflexivity|]. cbn [fst snd].
          split; [exact ENV1|]. split; [exact LS1|]. apply refs_stable_refl.
        - zstep. zstep. if_false. do 2 zstep.
          destruct (kenv_open LB PL EA lo B SPv FB s bs OW m CEIL FROK _ _ _ _ _ rB aB ENV1 LS1 HAB (proj1 HPB)) as (DB & _ & _ & OKB & _).
          pose proof (nbits_range _ OKB) as NBB. clear OKB DB.
          ihere. to_implM.
          eapply iter_body; [exact ENV1 | exact LS1 | exact IR | exact NBB |].
          intros until t6'. intros ENVJ LSJ RSJ.
          eapply implM_mono; [eapply bin_check; [exact ENVJ | exact LSJ | exact (irefs_stable _ _ _ _ IR RSJ)]|].
          cbv beta. intros r st' ms' (mK' & OWK' & R).
          destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & E & K1 & K2 & K3).
          unfold ANYQ. exists mK', OWK'. do 20 eexists. split; [exact E|]. split; [exact K1|]. split; [exact K2|].
          eapply refs_stable_trans; [exact RSJ| exact K3].
      Qed.
    End Loops.

    Local Ltac hres := let H := fresh "HRES" in intros ? ? ? ? ? H; hnf in H; exact (proj1 H).
    Local Ltac retpc n := replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    Lemma zero_bind_eq : forall {C : Type} r (K : unit -> BM (M := btree bptr) C) (bsK : ST),
      bbind ops (BN_zero ops r) K bsK = K tt (setbn r (bn_zero_pure (getbn r bsK)) bsK).
    Proof. reflexivity. Qed.
    Lemma get_set_bind_eq : forall {C : Type} r (g : bignum bptr -> bignum bptr) (K : unit -> BM (M := btree bptr) C) (bsK : ST),
      bbind ops (bbind ops (bget ops r) (fun b => bset ops r (g b))) K bsK = K tt (setbn r (g (getbn r bsK)) bsK).
    Proof. reflexivity. Qed.
    Lemma num_bits_bind_eq : forall {C : Type} r (K : Z -> BM (M := btree bptr) C) (bsK : ST), bg_ok (getbn r bsK) ->
      bbind ops (BN_num_bits ops r) K bsK = K (num_bits_pure (getbn r bsK)) bsK.
    Proof.
      intros C r K bsK (_ & _ & _ & FL). unfold bbind at 1. unfold BN_num_bits. rewrite bbind_get. unfold has_flag.
      assert (EL4 : Z.land (bn_flags (getbn r bsK)) BN_FLG_CONSTTIME = 0) by (destruct FL as [E|E]; rewrite E; reflexivity).
      rewrite EL4. reflexivity.
    Qed.

    Lemma inv_start : forall j1 jD jl j2 stK bsK mK OWK
        (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x22 x23 x25 x26 x27 t3 t4 t5 t6 : word),
      KENV (ifr0 j1 jD jl j2) stK bsK mK OWK -> lib_state bsK mK OWK PL EA ->
      ref_at bsK OWK PL rR aR -> ref_at bsK OWK PL ra_ aa -> ref_at bsK OWK PL rn an ->
      implM bgusegs (interp (embed (inv_rest rR ra_ rn bsK))) stK FINALQ
        (MS (mkR rax (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 SPi) (Z_to_bv 64 ac) a0 a1 a2 a3 a4 a5 a6 a7
                 x18 (Z_to_bv 64 aR) (Z_to_bv 64 NI) (Z_to_bv 64 an) x22 x23 (Z_to_bv 64 aa) x25 x26 x27 t3 t4 t5 t6)
            F (Z_to_bv 64 0x107df4) fc None mK (seg_rom bgusegs)).
    Proof.
      intros until t6. intros ENVK LSK HAR HAa HAn.
      pose proof SPR2 as SPR. pose proof ESPF as ESP. pose proof GLO' as GLO2. unfold GLOBALS_TOP in GLO2.
      pose proof FBlo as FBL. pose proof LOF as LOFF.
      unfold inv_rest.

      unfold implM. iprefix. do 2 zstep. ihere. to_implM.
      eapply KCALL; [exact ENVK | exact LSK
        | intros errv PRE; apw W_ctx.BN_CTX_start_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_START) | reflexivity | exact HPC | reflexivity]
        | hres |].
      intros u st0 bs0 m0 OW0 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV0 LS0 RS0 _. clear ENVK LSK.
      retpc 1080828.

      unfold implM. iprefix. do 2 zstep. ihere. to_implM.
      eapply KCALL; [exact ENV0 | exact LS0
        | intros errv PRE; apw W_ctx_get.BN_CTX_get_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_GET) | reflexivity | exact HPC | reflexivity]
        | hres |].
      intros rA st1 bs1 m1 OW1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV1 LS1 RS1 RES1. hnf in RES1. destruct RES1 as (_ & (iA & EiA) & (aA & HAA & ->) & _). clear ENV0 LS0.
      retpc 1080836.

      unfold implM. iprefix. do 3 zstep. ihere. to_implM.
      eapply KCALL; [exact ENV1 | exact LS1
        | intros errv PRE; apw W_ctx_get.BN_CTX_get_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_GET) | reflexivity | exact HPC | reflexivity]
        | hres |].
      intros rB st2 bs2 m2 OW2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV2 LS2 RS2 RES2. hnf in RES2. destruct RES2 as (_ & (iB & EiB) & (aB & HAB & ->) & _). clear ENV1 LS1.
      retpc 1080848.

      unfold implM. iprefix. do 3 zstep. ihere. to_implM.
      eapply KCALL; [exact ENV2 | exact LS2
        | intros errv PRE; apw W_ctx_get.BN_CTX_get_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_GET) | reflexivity | exact HPC | reflexivity]
        | hres |].
      intros rX st3 bs3 m3 OW3 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV3 LS3 RS3 RES3. hnf in RES3. destruct RES3 as (_ & (iX & EiX) & (aX & HAX & ->) & _). clear ENV2 LS2.
      retpc 1080860.

      unfold implM. iprefix. do 3 zstep. ihere. to_implM.
      eapply KCALL; [exact ENV3 | exact LS3
        | intros errv PRE; apw W_ctx_get.BN_CTX_get_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_GET) | reflexivity | exact HPC | reflexivity]
        | hres |].
      intros rD st4 bs4 m4 OW4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV4 LS4 RS4 RES4. hnf in RES4. destruct RES4 as (_ & (iD & EiD) & (aD & HAD & ->) & _). clear ENV3 LS3.
      retpc 1080872.
      unfold MallocRep.wz.

      pose proof ENV4 as (HEAP4 & AUX4 & ST4 & (errv4 & ERR4) & MI4 & LXP4 & FA4 & SO4 & RSE4 & FR4 & FSZ4).
      pose proof (lib_state_h_parts _ _ _ _ _ _ LS4) as PARTS4.
      pose proof (munch_refl [(FB, SPv)]%Z m4) as MU. pose proof (wmono_refl bgusegs m4) as WM.
      unfold LX_ERRNO, RATP in ERR4. change (3346328 - 164) with 3346164 in ERR4.
      unfold ifr0, ifr0_i, ifr_w, saved_i, saved_w in FR4. cbn [app] in FR4.
      remember (Z_to_bv 64 aD) as wD eqn:EwD.
      unfold implM. iprefix. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      assert (ENV5 : KENV (([CB 48 j1; C8 wD; C8 (Z_to_bv 64 aR); CB 24 jl] ++ saved_i) ++ ifr_w j2) st4 bs4 m5 OW4).
      { eapply (kenv_silent LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB FROK) with (W := [(FB, SPv)]) (errv' := errv4);
          [exact ENV4 | exact PARTS4 | exact MU | exact WM | constructor; [left; cbn [fst snd]; clear - FBL; lia | constructor]
          | exact ST4 | unfold LX_ERRNO, RATP; exact ERR4 | exact MI4 | exact FR4 | cbn; clear; lia]. }
      assert (LS5 : lib_state bs4 m5 OW4 PL EA).
      { eapply (lib_state_frame st4 LB SPv B [] bs4 m4 m5 OW4 PL EA _ HEAP4 LS4 MU WM FROK).
        constructor; [apply w_stack; cbn [fst snd]; clear - FBL CEIL; lia | constructor]. }
      clear ENV4 LS4 HEAP4 AUX4 ST4 ERR4 MI4 LXP4 FA4 SO4 RSE4 FR4 FSZ4 PARTS4 MU WM.
      subst wD.
      pose proof (ref_at_stable _ _ _ _ PL _ _ RS4 (ref_at_stable _ _ _ _ PL _ _ RS3 (ref_at_stable _ _ _ _ PL _ _ RS2 HAA))) as HAA4.
      pose proof (ref_at_stable _ _ _ _ PL _ _ RS4 (ref_at_stable _ _ _ _ PL _ _ RS3 HAB)) as HAB4.
      pose proof (ref_at_stable _ _ _ _ PL _ _ RS4 HAX) as HAX4.
      pose proof (refs_stable_trans _ _ _ _ _ _ RS0 (refs_stable_trans _ _ _ _ _ _ RS1 (refs_stable_trans _ _ _ _ _ _ RS2 (refs_stable_trans _ _ _ _ _ _ RS3 RS4)))) as RS04.
      pose proof (ref_at_stable _ _ _ _ PL _ _ RS04 HAR) as HAR4. pose proof (ref_at_stable _ _ _ _ PL _ _ RS04 HAa) as HAa4. pose proof (ref_at_stable _ _ _ _ PL _ _ RS04 HAn) as HAn4.
      clear HAA HAB HAX HAD RS0 RS1 RS2 RS3 RS4 RS04 HAR HAa HAn.

      do 2 zstep. ihere. to_implM.
      eapply KCALL; [exact ENV5 | exact LS5
        | intros errv PRE; apw W_ctx_get.BN_CTX_get_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_GET) | reflexivity | exact HPC | reflexivity]
        | hres |].
      intros rM st6 bs6 m6 OW6 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV6 LS6 RS6 RES6. hnf in RES6. destruct RES6 as (_ & _ & (aM & _ & ->) & _). clear ENV5 LS5.
      retpc 1080884.

      unfold implM. iprefix. do 3 zstep. ihere. to_implM.
      eapply KCALL; [exact ENV6 | exact LS6
        | intros errv PRE; apw W_ctx_get.BN_CTX_get_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_GET) | reflexivity | exact HPC | reflexivity]
        | hres |].
      intros rY st7 bs7 m7 OW7 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV7 LS7 RS7 RES7. hnf in RES7. destruct RES7 as (_ & (iY & EiY) & (aY & HAY & ->) & _). clear ENV6 LS6.
      retpc 1080896.

      unfold implM. iprefix. do 3 zstep. ihere. to_implM.
      eapply KCALL; [exact ENV7 | exact LS7
        | intros errv PRE; apw W_ctx_get.BN_CTX_get_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_GET) | reflexivity | exact HPC | reflexivity]
        | hres |].
      intros rT st8 bs8 m8 OW8 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV8 LS8 RS8 RES8. hnf in RES8. destruct RES8 as (_ & (iT & EiT) & (aT & HAT & ->) & _). clear ENV7 LS7.
      retpc 1080908.
      unfold MallocRep.wz.

      pose proof (refs_stable_trans _ _ _ _ _ _ RS6 (refs_stable_trans _ _ _ _ _ _ RS7 RS8)) as RS48.
      assert (HPA : hpl PL rA) by (rewrite EiA; apply hpl_pool).
      assert (HPB : hpl PL rB) by (rewrite EiB; apply hpl_pool).
      assert (HPX : hpl PL rX) by (rewrite EiX; apply hpl_pool).
      assert (HPY : hpl PL rY) by (rewrite EiY; apply hpl_pool).
      assert (HPT : hpl PL rT) by (rewrite EiT; apply hpl_pool).
      assert (IR8 : IREFS rA rB rX rY aA aB aX aY bs8 OW8).
      { unfold IREFS. split; [exact (ref_at_stable _ _ _ _ PL _ _ RS48 HAA4)|]. split; [exact (ref_at_stable _ _ _ _ PL _ _ RS48 HAB4)|].
        split; [exact (ref_at_stable _ _ _ _ PL _ _ RS48 HAX4)|]. split; [exact (ref_at_stable _ _ _ _ PL _ _ RS8 HAY)|].
        split; [exact (ref_at_stable _ _ _ _ PL _ _ RS48 HAn4)|]. exact (ref_at_stable _ _ _ _ PL _ _ RS48 HAR4). }
      pose proof (ref_at_stable _ _ _ _ PL _ _ RS48 HAa4) as HAa8.
      pose proof ENV8 as (HEAP8 & _). pose proof (lib_state_h_parts _ _ _ _ _ _ LS8) as PARTS8.
      pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP8 PARTS8 HAT HPT) as (T0 & TC & _).
      pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP8 PARTS8 (proj1 IR8) HPA) as (AA0 & AAC & _).
      pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP8 PARTS8 (proj1 (proj2 IR8)) HPB) as (AB0 & ABC & _).
      assert (AAR : 0 < aA < 2^64) by (clear - AA0 AAC CEIL LO SPR; lia).
      assert (ABR : 0 < aB < 2^64) by (clear - AB0 ABC CEIL LO SPR; lia).
      clear AA0 AAC AB0 ABC.
      clear HEAP8 PARTS8 RS6 RS7 RS8 RS48 HAA4 HAB4 HAX4 HAY HAn4 HAR4 HAa4 HAT EiA EiB EiX EiY EiT iA iB iX iY iT iD EiD.
      unfold implM. iprefix. pose proof ENV8 as (HEAP8' & AUX8 & ST8 & (errv8 & ERR8) & MI8 & LXP8 & FA8 & SO8 & RSE8 & FR8 & FSZ8). unfold ifr, ifr_i, ifr_w, saved_i, saved_w in FR8. cbn [app] in FR8.
      zstep. if_cases KT; rewrite ?unsigned_lit in KT by (clear - T0 TC CEIL LO SPR; lia); zify_cond KT. { exfalso. clear - KT T0. lia. }
      zstep.
      zstep. zstep. zstep. if_cases KIN; rewrite ?unsigned_lit in KIN by (clear - ARR; lia); zify_cond KIN. 2:{ exfalso. clear - KIN ARR. lia. }
      clear KT KIN T0 TC.

      do 3 zstep. ihere. to_implM. unfold BN_one.
      pose proof IR8 as (HAA & HAB & HAX & HAY & HAN & HAR).
      eapply KCALL; [exact ENV8 | exact LS8
        | intros errv PRE; apw W_set_word.BN_set_word_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_SETW) | reflexivity | exact HAX | exact (hpl_wref PL rX HPX)
                                                           | reflexivity | reflexivity | clear; lia]
        | hres |].
      intros u9 st9 bs9 m9 OW9 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV9 LS9 RS9 RES9. hnf in RES9. destruct RES9 as (_ & -> & _). unfold MallocRep.wz.
      pose proof (irefs_stable _ _ _ _ _ _ _ _ _ _ _ _ IR8 RS9) as IR9. pose proof (ref_at_stable _ _ _ _ PL _ _ RS9 HAa8) as HAa9.
      clear ENV8 LS8 IR8 HAa8 HAA HAB HAX HAY HAN HAR RS9.
      pose proof IR9 as (HAA & HAB & HAX & HAY & HAN & HAR).
      retpc 1080952.

      unfold implM. iprefix. zstep. if_false. do 2 zstep.
      eapply (zero_call LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK);
        [clear - LOFF CS128; lia | reflexivity | exact ENV9 | exact LS9 | exact HAY | exact (hpl_wref PL rY HPY) |].
      intros m10 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV10 LS10.
      set (bs10 := setbn rY (bn_zero_pure (getbn rY bs9)) bs9) in *.
      assert (IR10 : IREFS rA rB rX rY aA aB aX aY bs10 OW9).
      { unfold IREFS, bs10. repeat split; apply ref_at_setbn; assumption. }
      assert (HAa10 : ref_at bs10 OW9 PL ra_ aa) by (apply ref_at_setbn; exact HAa9).
      clear ENV9 LS9 IR9 HAa9 HAA HAB HAX HAY HAN HAR.
      pose proof IR10 as (HAA & HAB & HAX & HAY & HAN & HAR).
      retpc 1080964.

      do 3 zstep. ihere. to_implM. rewrite zero_bind_eq. fold bs10.
      eapply KCALL; [exact ENV10 | exact LS10
        | intros errv PRE; apw W_copy.BN_copy_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_COPY) | reflexivity | exact HAB | exact HAa10 | exact (hpl_wref PL rB HPB)
                                                   | exact NROa | reflexivity | reflexivity]
        | hres |].
      intros u11 st11 bs11 m11 OW11 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV11 LS11 RS11 RES11. hnf in RES11. destruct RES11 as (_ & -> & _). unfold MallocRep.wz.
      pose proof (irefs_stable _ _ _ _ _ _ _ _ _ _ _ _ IR10 RS11) as IR11.
      clear ENV10 LS10 IR10 HAa10 HAA HAB HAX HAY HAN HAR RS11.
      pose proof IR11 as (HAA & HAB & HAX & HAY & HAN & HAR).
      retpc 1080976.

      unfold implM. iprefix.
      zstep. if_cases KB; rewrite ?unsigned_lit in KB by (clear - ABR; lia); zify_cond KB. { exfalso. clear - KB ABR. lia. }
      do 3 zstep. ihere. to_implM.
      eapply KCALL; [exact ENV11 | exact LS11
        | intros errv PRE; apw W_copy.BN_copy_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_COPY) | reflexivity | exact HAA | exact HAN | exact (hpl_wref PL rA HPA)
                                                   | exact NROn | reflexivity | reflexivity]
        | hres |].
      intros u12 st12 bs12 m12 OW12 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV12 LS12 RS12 RES12. hnf in RES12. destruct RES12 as (_ & -> & _). unfold MallocRep.wz.
      pose proof (irefs_stable _ _ _ _ _ _ _ _ _ _ _ _ IR11 RS12) as IR12.
      clear ENV11 LS11 IR11 HAA HAB HAX HAY HAN HAR RS12 KB.
      pose proof IR12 as (HAA & HAB & HAX & HAY & HAN & HAR).
      retpc 1080992.

      rewrite get_set_bind_eq.
      unfold implM. iprefix.
      zstep. if_cases KA; rewrite ?unsigned_lit in KA by (clear - AAR; lia); zify_cond KA. { exfalso. clear - KA AAR. lia. }
      pose proof ENV12 as (HEAP12 & AUX12 & ST12' & (errv12 & ERR12) & MI12' & LXP12 & FA12 & SO12 & RSE12 & FR12 & FSZ12).
      pose proof (lib_state_h_parts _ _ _ _ _ _ LS12) as PARTS12.
      unfold LX_ERRNO, RATP in ERR12. change (3346328 - 164) with 3346164 in ERR12.
      unfold saved_i, ifr_w, saved_w in FR12. cbn [app] in FR12.
      apply (rw_cells_split_CB bgusegs m12 FB [] 48 j1 _ [40%nat; 8%nat]) in FR12; [|reflexivity]. cbn [app mk_CB_cells] in FR12.
      pose proof (munch_refl [(FB, SPv)]%Z m12) as MUf. pose proof (wmono_refl bgusegs m12) as WMf.
      zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m12s end.
      assert (ENV12s : KENV (ifr (firstn 40 j1) (Z_to_bv 64 aY) (Z_to_bv 64 aD) jl j2) st12 bs12 m12s OW12).
      { eapply (kenv_silent LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB FROK) with (W := [(FB, SPv)]) (errv' := errv12);
          [exact ENV12 | exact PARTS12 | exact MUf | exact WMf | constructor; [left; cbn [fst snd]; clear - FBL; lia | constructor]
          | exact ST12' | unfold LX_ERRNO, RATP; exact ERR12 | exact MI12' | unfold ifr, ifr_i, ifr_w, saved_i, saved_w; cbn [app]; exact FR12 | cbn; clear; lia]. }
      assert (LS12s : lib_state bs12 m12s OW12 PL EA).
      { eapply (lib_state_frame st12 LB SPv B [] bs12 m12 m12s OW12 PL EA _ HEAP12 LS12 MUf WMf FROK).
        constructor; [apply w_stack; cbn [fst snd]; clear - FBL CEIL; lia | constructor]. }
      clear ENV12 LS12 HEAP12 AUX12 ST12' ERR12 MI12' LXP12 FA12 SO12 RSE12 FR12 FSZ12 PARTS12 MUf WMf.
      assert (AAR8 : 0 < aA < 2^64 /\ aA mod 8 = 0).
      { pose proof ENV12s as (HEAPc & _). pose proof (lib_state_h_parts _ _ _ _ _ _ LS12s) as PARTSc.
        pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAPc PARTSc FROK HAA (proj1 HPA)) as (A0 & AC & AI).
        pose proof (OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU.BnUAlign.ref_at_ualign _ _ _ _ _ _ _ _ _ HEAPc PARTSc HAA (proj1 HPA)) as (_ & A8).
        split; [split; [exact A0| clear - AC AI; lia] | exact A8]. }
      zstep. if_cases KPA0; rewrite ?unsigned_lit in KPA0 by (clear - AAR8; lia); zify_cond KPA0; [exfalso; clear - KPA0 AAR8; lia| clear KPA0].
      zstep.
      zstep. if_cases KPA1; rewrite ?unsigned_lit in KPA1 by (clear - AAR8; lia); zify_cond KPA1.
      { exfalso. change 7 with (2^3 - 1) in KPA1. rewrite zb_land_mask in KPA1 by lia. clear - KPA1 AAR8. lia. }
      clear KPA1 AAR8.
      destruct (kenv_struct_store LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB B63 SPR2 FROK _ _ _ _ _ rA aA ENV12s LS12s HAA (proj1 HPA))
        as (DA & BNA & OKA & _ & SEPA & _ & _ & CLOSEA).
      unfold bn_cells, MallocRep.wz in BNA.
      pose proof ENV12s as (_ & _ & ST12 & _ & MI12 & _).
      pose proof (munch_refl [(aA, aA + 24)]%Z m12s) as MU. pose proof (wmono_refl bgusegs m12s) as WM.
      zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m13 end.
      destruct (CLOSEA m13 (bn_with_neg (getbn rA bs12) false) MU WM) as (ENV13 & LS13);
        [ exact BNA | reflexivity | reflexivity | exact OKA | exact ST12 | exact MI12 |].
      clear BNA MU WM ST12 MI12 CLOSEA DA OKA SEPA.
      clear KA.
      set (bs13 := setbn rA (bn_with_neg (getbn rA bs12) false) bs12) in *.
      assert (IR13 : IREFS rA rB rX rY aA aB aX aY bs13 OW12).
      { unfold IREFS, bs13. repeat split; apply ref_at_setbn; assumption. }
      clear ENV12s LS12s IR12 HAA HAB HAX HAY HAN HAR.
      pose proof IR13 as (HAA & HAB & HAX & HAY & HAN & HAR).
      assert (ABR8 : 0 < aB < 2^64 /\ aB mod 8 = 0).
      { pose proof ENV13 as (HEAPc & _). pose proof (lib_state_h_parts _ _ _ _ _ _ LS13) as PARTSc.
        pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAPc PARTSc FROK HAB (proj1 HPB)) as (A0 & AC & AI).
        pose proof (OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU.BnUAlign.ref_at_ualign _ _ _ _ _ _ _ _ _ HEAPc PARTSc HAB (proj1 HPB)) as (_ & A8).
        split; [split; [exact A0| clear - AC AI; lia] | exact A8]. }
      zstep. if_cases KPB0; rewrite ?unsigned_lit in KPB0 by (clear - ABR8; lia); zify_cond KPB0; [exfalso; clear - KPB0 ABR8; lia| clear KPB0].
      zstep.
      zstep. if_cases KPB1; rewrite ?unsigned_lit in KPB1 by (clear - ABR8; lia); zify_cond KPB1.
      { exfalso. change 7 with (2^3 - 1) in KPB1. rewrite zb_land_mask in KPB1 by lia. clear - KPB1 ABR8. lia. }
      clear KPB1 ABR8.

      assert (J5 : forall st5 bs5 m5' OW5 (rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
                KENV (ifr (firstn 40 j1) (Z_to_bv 64 aY) (Z_to_bv 64 aD) jl j2) st5 bs5 m5' OW5 -> lib_state bs5 m5' OW5 PL EA -> IREFS rA rB rX rY aA aB aX aY bs5 OW5 ->
                implM bgusegs (interp (embed (
                    bbind ops (BN_num_bits ops rn) (fun nb =>
                    bbind ops (bget ops rn) (fun n2 =>
                    bbind ops (if is_odd_pure n2 && (nb <=? 2048) then inv_binary_loop ops (Z.to_nat (2 * nb) + 2) rA rB rX rY rn else bunr ops) (fun _ =>
                    bbind ops (BN_sub ops rY rn rY) (fun _ =>
                    bbind ops (bget ops rA) (fun bA =>
                    bbind ops (if is_one_pure bA then
                                 bbind ops (bget ops rY) (fun y => bbind ops (BN_ucmp ops rY rn) (fun c =>
                                 if negb (bn_neg y) && (c <? 0) then BN_copy ops rR rY else BN_nnmod ops rR rY rn))
                               else bunr ops) (fun _ => BN_CTX_end ops)))))) bs5))) st5 FINALQ
                  (MS (mkR rax' (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) t0' t1' t2' (Z_to_bv 64 SPi) (Z_to_bv 64 ac) a0' a1' a2' a3' a4' a5' a6' a7'
                           (Z_to_bv 64 aX) (Z_to_bv 64 aR) (Z_to_bv 64 NI) (Z_to_bv 64 an) (Z_to_bv 64 aM) (Z_to_bv 64 aA) (Z_to_bv 64 aa) (Z_to_bv 64 aB)
                           (Z_to_bv 64 aT) (Z_to_bv 64 aY) t3' t4' t5' t6')
                      F (Z_to_bv 64 0x107ef4) fc None m5' (seg_rom bgusegs))).
      { intros until t6'. intros ENV5 LS5 IR5.
        pose proof IR5 as (HAA5 & HAB5 & HAX5 & HAY5 & HAN5 & HAR5).
        destruct (kenv_open LB PL EA lo B SPv FB s bs OW m CEIL FROK _ _ _ _ _ rn an ENV5 LS5 HAN5 NROn) as (DN & _ & _ & OKN & _).
        rewrite (num_bits_bind_eq rn _ bs5 OKN). rewrite bbind_get.
        pose proof (nbits_range _ OKN) as NBN. clear DN OKN.
        set (nb := num_bits_pure (getbn rn bs5)) in *.
        destruct (is_odd_pure (getbn rn bs5)) eqn:EO.
        2:{ cbn [andb]. unfold bbind, bunr. cbn [bind unreachable tree_ops tbind embed interp]. apply implM_interp_unr. }
        destruct (Z.leb_spec nb 2048) as [NB2|NB2].
        2:{ cbn [andb]. unfold bbind, bunr. cbn [bind unreachable tree_ops tbind embed interp]. apply implM_interp_unr. }
        cbn [andb].
        unfold implM. iprefix. do 2 zstep.
        eapply KODD; [exact ENV5 | exact LS5 | exact HAN5 | exact NROn |].
        intros m6' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV6' LS6'. clear ENV5 LS5.
        retpc 1081084. rewrite EO. cbn [Z.b2z].
        zstep. if_false. do 2 zstep.
        eapply KBITS; [exact ENV6' | exact LS6' | exact HAN5 | exact NROn |].
        intros m7' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV7' LS7'. clear ENV6' LS6'.
        retpc 1081096. fold nb.
        do 2 zstep.
        zstep. rewrite lts_signed by (clear - NBN; lia).
        replace (2048 <? nb) with false by (symmetry; apply Z.ltb_ge; exact NB2). cbn [negb].
        ihere. to_implM.
        replace (Z.to_nat (2 * nb) + 2)%nat with (S (Z.to_nat (2 * nb) + 1)) by (clear; lia).
        unfold bbind at 1. cbn [bind tree_ops]. eapply implM_embed_bind.
        { eapply (bin_top rA rB rX rY aA aB aX aY (firstn 40 j1) (Z_to_bv 64 aD) jl j2 HPA HPB HPX HPY); [exact ENV7' | exact LS7' | exact IR5]. }
        cbv beta. intros [u8 bs8'] st8' ms8' (m8' & OW8' & R).
        destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & ENV8' & LS8' & RS8'). cbn [fst snd] in *.
        eapply (inv_fin rA rB rX rY aA aB aX aY (firstn 40 j1) (Z_to_bv 64 aD) jl j2); [.. | exact ENV8' | exact LS8' | exact (irefs_stable _ _ _ _ _ _ _ _ _ _ _ _ IR5 RS8')]; assumption. }

      rewrite bbind_get.
      destruct (kenv_open LB PL EA lo B SPv FB s bs OW m CEIL FROK _ _ _ _ _ rB aB ENV13 LS13 HAB (proj1 HPB)) as (DB & BNB & _ & OKB & _).
      destruct (kenv_open LB PL EA lo B SPv FB s bs OW m CEIL FROK _ _ _ _ _ rA aA ENV13 LS13 HAA (proj1 HPA)) as (DA & _ & _ & OKA & _).
      unfold bn_cells, MallocRep.wz in BNB.
      zstep. clear BNB DB DA.
      assert (NN : forall st3 m3' (rax' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
                KENV (ifr (firstn 40 j1) (Z_to_bv 64 aY) (Z_to_bv 64 aD) jl j2) st3 bs13 m3' OW12 -> lib_state bs13 m3' OW12 PL EA ->
                implM bgusegs (interp (embed (
                    bbind ops (BN_nnmod ops rB rB rA) (fun _ =>
                    bbind ops (BN_num_bits ops rn) (fun nb =>
                    bbind ops (bget ops rn) (fun n2 =>
                    bbind ops (if is_odd_pure n2 && (nb <=? 2048) then inv_binary_loop ops (Z.to_nat (2 * nb) + 2) rA rB rX rY rn else bunr ops) (fun _ =>
                    bbind ops (BN_sub ops rY rn rY) (fun _ =>
                    bbind ops (bget ops rA) (fun bA =>
                    bbind ops (if is_one_pure bA then
                                 bbind ops (bget ops rY) (fun y => bbind ops (BN_ucmp ops rY rn) (fun c =>
                                 if negb (bn_neg y) && (c <? 0) then BN_copy ops rR rY else BN_nnmod ops rR rY rn))
                               else bunr ops) (fun _ => BN_CTX_end ops))))))) bs13))) st3 FINALQ
                  (MS (mkR rax' (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) t0' t1' t2' (Z_to_bv 64 SPi) (Z_to_bv 64 ac) a0' a1' a2' a3' a4' a5' a6' a7'
                           (Z_to_bv 64 aX) (Z_to_bv 64 aR) (Z_to_bv 64 NI) (Z_to_bv 64 an) (Z_to_bv 64 aM) (Z_to_bv 64 aA) (Z_to_bv 64 aa) (Z_to_bv 64 aB)
                           (Z_to_bv 64 aT) (Z_to_bv 64 aY) t3' t4' t5' t6')
                      F (Z_to_bv 64 0x107edc) fc None m3' (seg_rom bgusegs))).
      { intros until t6'. intros ENV3 LS3.
        unfold implM. iprefix. do 5 zstep. ihere. to_implM.
        eapply KCALL; [exact ENV3 | exact LS3
          | intros errv PRE; eapply BN_nnmod_walk; [exact PRE | reflexivity | exact HAB | exact HAB | exact HAA | exact HPB | exact (proj1 HPB) | exact (proj1 HPA) | exact HPC
                                                 | reflexivity | reflexivity | reflexivity | reflexivity]
          | hres |].
        intros u' stn bsn mn OWn ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENVn LSn RSn RESn. hnf in RESn. destruct RESn as (_ & ->). unfold MallocRep.wz.
        retpc 1081072.
        unfold implM. iprefix. zstep. if_false. ihere. to_implM.
        eapply J5; [exact ENVn | exact LSn | exact (irefs_stable _ _ _ _ _ _ _ _ _ _ _ _ IR13 RSn)]. }
      destruct (bn_neg (getbn rB bs13)) eqn:EN; cbn [Z.b2z orb].
      -
        zstep. if_true.
        ihere. to_implM. rewrite (ucmp_bind_eq rB rA _ bs13 OKB OKA).
        eapply NN; [exact ENV13 | exact LS13].
      - zstep. if_false. do 3 zstep. ihere. to_implM.
        eapply KCALL; [exact ENV13 | exact LS13
          | intros errv PRE; apw W_cmp.BN_ucmp_walk; [exact (bn_pre_le _ _ _ _ _ _ _ _ _ _ _ _ _ PRE STK_UCMP) | reflexivity | exact HAB | exact HAA
                                                   | exact (proj1 HPB) | exact (proj1 HPA) | reflexivity | reflexivity]
          | intros ? ? ? ? ? HRES; exact (proj1 (proj1 HRES)) |].
        intros c st4' bs4' m4' OW4' ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV4' LS4' RS4' RES4'. destruct RES4' as ((_ & -> & CR & -> & ->) & _).
        retpc 1081048.
        unfold implM. iprefix.
        zstep. rewrite lts_signed by (clear - CR; lia).
        destruct (Z.ltb_spec c 0) as [CN|CP]; cbn [negb].
        + replace (0 <=? c) with false by (symmetry; apply Z.leb_gt; exact CN).
          ihere. to_implM. rewrite bbind_ret.
          eapply J5; [exact ENV4' | exact LS4' | exact IR13].
        + replace (0 <=? c) with true by (symmetry; apply Z.leb_le; exact CP).
          ihere. to_implM.
          eapply NN; [exact ENV4' | exact LS4'].
    Qed.

    Definition ifrA (j1 jD jI jl j2 : list byte) : list cell :=
      ([CB 48 j1; CB 8 jD; CB 8 jI; CB 24 jl] ++ saved_i) ++ ifr_w j2.

    Lemma inv_early : forall j1 jD jI jl j2 stK mK
        (rax t0 t1 t2 a2 a3 a4 a5 a6 a7 x22 x23 x25 x26 x27 t3 t4 t5 t6 : word),
      KENV (ifrA j1 jD jI jl j2) stK bs mK OW -> lib_state bs mK OW PL EA ->
      ref_at bs OW PL rR aR -> ref_at bs OW PL ra_ aa -> ref_at bs OW PL rn an ->
      implM bgusegs (interp (embed (BN_mod_inverse_r rR ra_ rn bs))) stK FINALQ
        (MS (mkR rax (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 SPi) (Z_to_bv 64 ac) (Z_to_bv 64 an) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 an) (Z_to_bv 64 aR) (Z_to_bv 64 NI) (Z_to_bv 64 an) x22 x23 (Z_to_bv 64 aa) x25 x26 x27 t3 t4 t5 t6)
            F (Z_to_bv 64 0x107bb8) fc None mK (seg_rom bgusegs)).
    Proof.
      intros until t6. intros ENVK LSK HAR HAa HAn.
      pose proof SPR2 as SPR. pose proof ESPF as ESP. pose proof GLO' as GLO2. unfold GLOBALS_TOP in GLO2.
      pose proof FBlo as FBL. pose proof LOF as LOFF.
      unfold BN_mod_inverse_r. rewrite !bbind_get.
      destruct (abs_is_word_pure (getbn rn bs) 1 || is_zero_pure (getbn rn bs)) eqn:EG1.
      { unfold bunr. cbn [unreachable tree_ops embed interp]. apply implM_interp_unr. }
      destruct (has_flag (getbn ra_ bs) BN_FLG_CONSTTIME || has_flag (getbn rn bs) BN_FLG_CONSTTIME) eqn:EG2.
      { unfold bunr. cbn [unreachable tree_ops embed interp]. apply implM_interp_unr. }
      apply orb_false_elim in EG1. destruct EG1 as (EW & EZ).
      assert (NI4 : (SPv + -52) mod 4 = 0) by (clear - SP16; Z.div_mod_to_equations; lia).
      unfold implM. iprefix. zstep.
      eapply KWORD; [exact ENVK | exact LSK | exact HAn | exact NROn | clear; lia |].
      intros m1 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV1 LS1. clear ENVK LSK.
      retpc 1080252. rewrite EW. cbn [Z.b2z].
      zstep. zstep. if_false. do 2 zstep.
      eapply KZERO; [exact ENV1 | exact LS1 | exact HAn | exact NROn |].
      intros m2 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV2 LS2. clear ENV1 LS1.
      retpc 1080268. rewrite EZ. cbn [Z.b2z].
      zstep. if_true.

      pose proof ENV2 as (HEAP2 & AUX2 & ST2 & (errv2 & ERR2) & MI2 & LXP2 & FA2 & SO2 & RSE2 & FR2 & FSZ2).
      pose proof (lib_state_h_parts _ _ _ _ _ _ LS2) as PARTS2.
      pose proof (munch_refl [(FB, SPv)]%Z m2) as MU. pose proof (wmono_refl bgusegs m2) as WM.
      unfold LX_ERRNO, RATP in ERR2. change (3346328 - 164) with 3346164 in ERR2.
      unfold ifrA, ifr_w, saved_i, saved_w in FR2. cbn [app] in FR2.
      remember (Z_to_bv 64 aR) as wR eqn:EwR.
      zstep.
      zstep. if_cases KN1; rewrite ?unsigned_lit in KN1 by lia; zify_cond KN1.
      all: try (exfalso; clear - KN1 NI4 SPR LOFF CEIL GLO2 CS128; lia).
      zstep. if_cases KN2; rewrite ?unsigned_lit in KN2 by lia; zify_cond KN2.
      all: try (exfalso; clear - KN2 NI4; change 3 with (Z.ones 2) in KN2; rewrite Z.land_ones in KN2 by lia; change (2 ^ 2) with 4 in KN2; lia).
      zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      subst wR.
      assert (ENV3 : KENV (ifr0 j1 jD jl j2) stK bs m3 OW).
      { eapply (kenv_silent LB PL EA lo B SPv FB s bs OW m CEIL GLO' FBlo FBsp SPB FROK) with (W := [(FB, SPv)]) (errv' := errv2);
          [exact ENV2 | exact PARTS2 | exact MU | exact WM | constructor; [left; cbn [fst snd]; clear - FBL; lia | constructor]
          | exact ST2 | unfold LX_ERRNO, RATP; exact ERR2 | exact MI2 | exact FR2 | cbn; clear; lia]. }
      assert (LS3 : lib_state bs m3 OW PL EA).
      { eapply (lib_state_frame stK LB SPv B [] bs m2 m3 OW PL EA _ HEAP2 LS2 MU WM FROK).
        constructor; [apply w_stack; cbn [fst snd]; clear - FBL CEIL; lia | constructor]. }
      clear ENV2 LS2 HEAP2 AUX2 ST2 ERR2 MI2 LXP2 FA2 SO2 RSE2 FR2 FSZ2 PARTS2 MU WM errv2.

      apply orb_false_elim in EG2. destruct EG2 as (EFA & EFN). unfold has_flag in EFA, EFN.
      apply negb_false_iff in EFA. apply negb_false_iff in EFN. apply Z.eqb_eq in EFA. apply Z.eqb_eq in EFN. unfold BN_FLG_CONSTTIME in EFA, EFN.
      do 3 zstep.
      eapply KFLAGS; [exact ENV3 | exact LS3 | exact HAa | exact NROa | clear; lia |].
      intros m4 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV4 LS4. clear ENV3 LS3.
      retpc 1080384. rewrite EFA.
      zstep. if_false.

      do 3 zstep.
      eapply KFLAGS; [exact ENV4 | exact LS4 | exact HAn | exact NROn | clear; lia |].
      intros m6 ? ? ? ? ? ? ? ? ? ? ? ? ? ? ENV6 LS6. clear ENV4 LS4.
      retpc 1080400. rewrite EFN.
      zstep. if_true.
      ihere. to_implM.
      eapply inv_start; [exact ENV6 | exact LS6 | exact HAR | exact HAa | exact HAn].
    Qed.

  End Body.

  Lemma BN_mod_inverse_r_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BgBnU.BnRep.err_addrs)
      (lo B : Z) (errv : word) (rR ra_ rn : bnref) (aR aa an ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_MOD_INVERSE_STACK -> tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
    ref_at bs OW PL rR aR -> hpl PL rR -> ref_at bs OW PL ra_ aa -> ra_ <> ROne -> ref_at bs OW PL rn an -> rn <> ROne ->
    pl_ctx PL = Some (ac, qc) ->
    a0 = wz aR -> a1 = wz aa -> a2 = wz an -> a3 = wz ac ->
    implM bgusegs (interp (embed (BN_mod_inverse_r rR ra_ rn bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz aR))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MOD_INVERSE) fc None m (seg_rom bgusegs)).
  Proof.
    intros until qc. intros PRE -> SP16 HR HPR HA NROa HN NROn HPC -> -> -> ->.
    pose proof PRE as (HEAP & LS & FROK & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & MI).
    pose proof LO as LO'. unfold BN_MOD_INVERSE_STACK in LO'.
    unfold BN_MOD_INVERSE, MallocRep.wz.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (ref_at_hrange _ _ _ _ _ _ _ _ _ HEAP PARTS HR HPR) as (R0 & RC & _).
    assert (ARR : 0 < aR < 2^64) by (clear - R0 RC CEIL LO' SPR; lia). clear R0 RC.
    pose proof (munch_refl [(bv_unsigned sp - 256, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bgusegs m) as WM.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    assert (GLO' : GLOBALS_TOP <= lo) by exact GLO. unfold GLOBALS_TOP in GLO.
    unfold implM. iprefix.
    carve_frame 64%nat ST. do 7 zstep.

    destruct (lib_state_cx_open [] bs m OW PL EA LS) as (Hs & IX & CV & _).
    apply (CtxKit.cx_view_some _ _ _ _ _ _ _ _ HPC) in CV. destruct CV as (BC & _). change BN_CTX_SZ with 72 in BC.
    pose proof (RH_range _ _ _ _ _ _ _ HEAP BC) as (CA0 & _ & _ & CAC & _). clear BC Hs IX.
    do 6 zstep.
    zstep. if_cases KC; rewrite ?unsigned_lit in KC by (clear - CA0 CAC CEIL LO' SPR; lia); zify_cond KC; try (exfalso; clear - KC CA0; lia).
    do 5 zstep.
    replace (ret_pc (Z_to_bv 64 1082720)) with (Z_to_bv 64 1082720) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    remember (Z_to_bv 64 1082720) as rax eqn:Erax. remember (Z_to_bv 64 aR) as wR eqn:EwR. remember (Z_to_bv 64 aa) as wA eqn:EwA.
    remember (Z_to_bv 64 an) as wN eqn:EwN. remember (Z_to_bv 64 0) as w0 eqn:Ew0.
    carve_frame 192%nat ST. do 14 zstep. subst rax wR wA wN w0. do 8 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.

    apply (rw_cells_split_CB bgusegs _ _ [] 88 _ _ [48; 8; 8; 24]%nat) in FR0; [| reflexivity]. cbn [mk_CB_cells app] in FR0.
    lazymatch type of FR0 with rw_cells _ _ _ (CB 48 ?x1 :: CB 8 ?xD :: CB 8 ?xI :: CB 24 ?xl :: _) =>
      lazymatch type of FR with rw_cells _ _ _ (CB 12 ?x2 :: C4 _ :: _) =>
        assert (FRJ : rw_cells bgusegs m1 (bv_unsigned sp + -256) (ifrA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 aR aa an x1 xD xI xl x2))
      end end.
    { unfold ifrA, ifr_w, saved_i, saved_w. apply BgU.F_fwritex.rw_cells_app. split; [exact FR0|].
      cbn [cells_size csize app Nat.add]. replace (bv_unsigned sp + -256 + Z.of_nat 192) with (bv_unsigned sp + -64) by (clear; lia). exact FR. }
    clear FR FR0.
    assert (HWL0 : Forall (w_lib bs OW PL lo (bv_unsigned sp)) [(bv_unsigned sp - 256, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (WOK0 : Forall (w_ok OW LB bs PL EA (bv_unsigned sp) []) [(bv_unsigned sp - 256, bv_unsigned sp)]) by (constructor; [apply w_stack; cbn; lia| constructor]).
    pose proof (lib_state_frame s LB _ _ [] bs m m1 OW PL EA _ HEAP LS MU WM FROK WOK0) as LS1.
    lazymatch type of FRJ with rw_cells _ _ _ ?fr =>
      assert (ENV : kenv LB PL lo B (bv_unsigned sp) (bv_unsigned sp + -256) s bs OW m fr s bs m1 OW)
    end.
    { unfold kenv. split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL0 CEIL)|].
      split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HWL0 SPB ltac:(lia)); exact GLO'|].
      split; [exact ST|]. split; [exists errv; unfold LX_ERRNO, RATP; exact ERR|]. split; [exact MI|].
      split; [apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HWL0 CEIL); [exact GLO'| lia]|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply refs_stable_refl|]. split; [exact FRJ| cbn; lia]. }
    ihere. to_implM.
    eapply (inv_early ra gp sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo B s bs OW LB m PL EA rR ra_ rn aR aa an ac qc CEIL GLO' LO' SPB B63 FROK HPC HPR NROa NROn ARR SP16);
      [exact ENV | exact LS1 | exact HR | exact HA | exact HN].
  Qed.

  Lemma BN_mod_inverse_eq : forall rR ra rn, BN_mod_inverse ops rR ra rn = BN_mod_inverse_r rR ra rn.
  Proof. reflexivity. Qed.

  Lemma BN_mod_inverse_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (bs : bstate bptr) (OW LB : list block) (PL : placement) (EA : BgBnU.BnRep.err_addrs)
      (lo B : Z) (errv : word) (rR ra_ rn : bnref) (aR aa an ac : Z) (qc : bptr),
    bn_pre s bs m OW LB PL EA sp lo B errv BN_MOD_INVERSE_STACK -> tp = wz RATP -> bv_unsigned sp mod 16 = 0 ->
    ref_at bs OW PL rR aR -> hpl PL rR -> ref_at bs OW PL ra_ aa -> ra_ <> ROne -> ref_at bs OW PL rn an -> rn <> ROne ->
    pl_ctx PL = Some (ac, qc) ->
    a0 = wz aR -> a1 = wz aa -> a2 = wz an -> a3 = wz ac ->
    implM bgusegs (interp (embed (BN_mod_inverse ops rR ra_ rn bs))) s
      (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s bs OW LB lo B m PL EA (fun _ _ _ PL' a0' => PL' = PL /\ a0' = wz aR))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz BN_MOD_INVERSE) fc None m (seg_rom bgusegs)).
  Proof. intros until qc. rewrite BN_mod_inverse_eq. apply BN_mod_inverse_r_walk. Qed.
End Proofs.
End WithCeiling0.
