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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWordsCorrect BnModel BnTree BnInv BnBridge BgState BgInv BgLib.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_small W_small2 W_top.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Section Env.

  Variables (LB : list block) (PL : placement) (EA : BnRep.err_addrs) (lo B SPv FB : Z).
  Variables (s0 : PState) (bs0 : bstate bptr) (OW0 : list block) (m0 : mem).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis LOFB : lo <= FB.
  Hypothesis FBSP : FB <= SPv.
  Hypothesis SPB : SPv <= B.
  Hypothesis B63 : B < 2^63.
  Hypothesis SPR : SPv < 2^64.
  Hypothesis FROK : frames_ok PL SPv B.

  Definition kenv (fr : list cell) (st : PState) (bs : bstate bptr) (m : mem) (OW : list block) : Prop :=
    RHEAP st (OW ++ LB) m /\ rauxv_ok m B /\ stk bgusegs m lo FB /\ (exists errv : word, rw_cells bgusegs m LX_ERRNO [C4 errv]) /\ mem_inv bgusegs m
    /\ lx_pres LB SPv (XW PL) m0 m /\ ps_fa st = ps_fa s0 /\ ps_so st = ps_so s0 /\ refs_stable bs0 OW0 bs OW
    /\ rw_cells bgusegs m FB fr /\ Z.of_nat (cells_size fr) = SPv - FB.

  Lemma ESPv : bv_unsigned (Z_to_bv 64 FB) = FB.
  Proof using CEIL LOFB FBSP SPR. clear - CEIL LOFB FBSP SPR. apply unsigned_lit. lia. Qed.

  Lemma FROK_FB : frames_ok PL FB B.
  Proof using CEIL LOFB FBSP FROK. clear - CEIL LOFB FBSP FROK. eapply frames_ok_call; [exact FROK| exact CEIL| exact LOFB| exact FBSP]. Qed.

  Lemma kenv_pre : forall fr st bs m OW K,
    kenv fr st bs m OW -> lib_state bs m OW PL EA -> lo <= FB - K ->
    exists errv, bn_pre st bs m OW LB PL EA (Z_to_bv 64 FB) lo B errv K.
  Proof using CEIL GLO LOFB FBSP SPB B63 SPR FROK.
    intros fr st bs m OW K (HEAP & AUX & ST & (errv & ERR) & MI & _) LS HK. exists errv.
    unfold bn_pre. rewrite ESPv. split; [exact HEAP|]. split; [exact LS|]. split; [exact FROK_FB|].
    repeat (split; [first [assumption | lia]|]). assumption.
  Qed.

  Definition kpost (st : PState) (bs : bstate bptr) (m : mem) (OW : list block) (st' : PState) (bs' : bstate bptr) (m' : mem) (OW' : list block) : Prop :=
    RHEAP st' (OW' ++ LB) m' /\ lib_state bs' m' OW' PL EA /\ rauxv_ok m' B /\ stk bgusegs m' lo FB
    /\ (exists errv' : word, rw_cells bgusegs m' LX_ERRNO [C4 errv']) /\ mem_inv bgusegs m'
    /\ lx_pres LB FB (XW PL) m m' /\ ps_fa st' = ps_fa st /\ ps_so st' = ps_so st /\ refs_stable bs OW bs' OW'.

  Lemma kpost_refs : forall st bs m OW st' bs' m' OW', kpost st bs m OW st' bs' m' OW' -> refs_stable bs OW bs' OW'.
  Proof. intros st bs m OW st' bs' m' OW' (_ & _ & _ & _ & _ & _ & _ & _ & _ & RS). exact RS. Qed.

  Lemma kenv_post : forall fr st bs m OW st' bs' m' OW',
    kenv fr st bs m OW -> kpost st bs m OW st' bs' m' OW' -> kenv fr st' bs' m' OW' /\ lib_state bs' m' OW' PL EA.
  Proof using CEIL GLO LOFB FBSP FROK.
    intros fr st bs m OW st' bs' m' OW' (HEAP & AUX & ST & ERR & MI & LXP & FA & SO & RS & FR & FSZ)
           (HEAP' & LS' & AUX' & ST' & ERR' & MI' & LXP' & FA' & SO' & RS').
    split; [|exact LS'].
    unfold kenv. split; [exact HEAP'|]. split; [exact AUX'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact MI'|].
    split. { eapply lx_pres_trans; [exact LXP|]. eapply lx_pres_weaken; [exact LXP'| exact FBSP| auto| auto]. }
    split; [congruence|]. split; [congruence|].
    split; [eapply refs_stable_trans; eauto|].
    split; [|exact FSZ].
    eapply rw_cells_agree; [apply agree_of_lx_pres; exact LXP' | exact FR |].
    intros a Ha. eapply (xw_client PL LB FB SPv B); [exact (proj1 FROK)| lia|].
    unfold LIBW_bgr, BnRep.LIBW_bn, CONST_ONE, BN_STRUCT_SZ. cbn [rin_ivs app fst snd]. unfold GLOBALS_TOP in GLO. lia.
  Qed.

  Lemma bn_post_kpost : forall {A : Type} (ra gp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32)
      st bs OW m (RES : A -> bstate bptr -> list block -> placement -> word -> Prop) (r : A * bstate bptr) st' ms',
    bn_post ra (Z_to_bv 64 FB) gp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc st bs OW LB lo B m PL EA RES r st' ms' ->
    (forall v bs' OW' PL' a0', RES v bs' OW' PL' a0' -> PL' = PL) ->
    exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' OW',
      ms' = MS (mkR ra (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bgusegs)
      /\ kpost st bs m OW st' (snd r) m' OW' /\ RES (fst r) (snd r) OW' PL a0.
  Proof using CEIL LOFB FBSP SPR.
    intros A ra gp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc st bs OW m RES r st' ms' PO HPL. unfold bn_post in PO.
    destruct PO as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & OW' & PL' & errv' & E & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11).
    pose proof (HPL _ _ _ _ _ P11) as EPL. subst PL'.
    rewrite ESPv in *.
    exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', OW'. split; [exact E|]. split; [|exact P11].
    unfold kpost. repeat (split; [first [assumption | exists errv'; assumption]|]). assumption.
  Qed.

  Lemma kenv_silent : forall fr fr' st bs m m' OW W (errv' : word),
    kenv fr st bs m OW -> lib_parts bs OW PL EA -> munch W m m' -> wmono bgusegs m m' -> Forall (w_lib bs OW PL lo SPv) W ->
    stk bgusegs m' lo FB -> rw_cells bgusegs m' LX_ERRNO [C4 errv'] -> mem_inv bgusegs m' ->
    rw_cells bgusegs m' FB fr' -> Z.of_nat (cells_size fr') = SPv - FB ->
    kenv fr' st bs m' OW.
  Proof using CEIL GLO LOFB FBSP SPB FROK.
    intros fr fr' st bs m m' OW W errv' (HEAP & AUX & ST & ERR & MI & LXP & FA & SO & RS & FR & FSZ) PARTS MU WM HW ST' ERR' MI' FR' FSZ'.
    unfold kenv. split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HW CEIL)|].
    split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK AUX MU WM HW SPB); lia|].
    split; [exact ST'|]. split; [exists errv'; exact ERR'|]. split; [exact MI'|].
    split. { eapply lx_pres_trans; [exact LXP|]. apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK MU WM HW CEIL); lia. }
    split; [exact FA|]. split; [exact SO|]. split; [exact RS|]. split; [exact FR'| exact FSZ'].
  Qed.

  Lemma kenv_xw : forall fr st bs m m' OW W (errv' : word),
    kenv fr st bs m OW -> munch W m m' -> wmono bgusegs m m' ->
    Forall (fun iv : Z * Z => exists fi, In fi (pl_frames PL) /\ fst fi <= fst iv /\ snd iv <= snd fi) W ->
    stk bgusegs m' lo FB -> rw_cells bgusegs m' LX_ERRNO [C4 errv'] -> mem_inv bgusegs m' -> rw_cells bgusegs m' FB fr ->
    kenv fr st bs m' OW.
  Proof using CEIL GLO LOFB FBSP SPB FROK.
    intros fr st bs m m' OW W errv' (HEAP & AUX & ST & ERR & MI & LXP & FA & SO & RS & FR & FSZ) MU WM HW ST' ERR' MI' FR'.
    destruct FROK as (PLF & CSP & BXB).
    unfold kenv. split.
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. eapply Forall_impl; [|exact HW].
      intros [x y] (fi & Hin & H1 & H2). cbn [fst snd] in *. destruct (PLF fi Hin) as (P1 & P2). left. cbn [fst]. lia. }
    split.
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. eapply Forall_impl; [|exact HW].
      intros [x y] (fi & Hin & H1 & H2). cbn [fst snd] in *. destruct (PLF fi Hin) as (P1 & P2).
      pose proof alloc_ceiling_range as CR. unfold RAUXV_CELL, GLOBALS_TOP in *. split; [lia|]. right. lia. }
    split; [exact ST'|]. split; [exists errv'; exact ERR'|]. split; [exact MI'|].
    split.
    { eapply lx_pres_trans; [exact LXP|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
      intros a Ha [Hna Hc]. clear MU. induction HW as [|[x y] W' Hiv HW' IH]; [exact I|]. cbn [outside]. split; [|exact IH].
      intros Hx. destruct Hiv as (fi & Hin & H1 & H2). cbn [fst snd] in *.
      apply Hna. unfold XW. apply rin_ivs_app. right. apply rin_ivs_In. exists fi. split; [exact Hin| lia]. }
    split; [exact FA|]. split; [exact SO|]. split; [exact RS|]. split; [exact FR'| exact FSZ].
  Qed.

  Lemma kenv_final : forall fr st bs m OW,
    kenv fr st bs m OW ->
    RHEAP st (OW ++ LB) m /\ rauxv_ok m B /\ stk bgusegs m lo FB /\ (exists errv : word, rw_cells bgusegs m LX_ERRNO [C4 errv]) /\ mem_inv bgusegs m
    /\ lx_pres LB SPv (XW PL) m0 m /\ ps_fa st = ps_fa s0 /\ ps_so st = ps_so s0 /\ refs_stable bs0 OW0 bs OW /\ rw_cells bgusegs m FB fr.
  Proof. intros fr st bs m OW (HEAP & AUX & ST & ERR & MI & LXP & FA & SO & RS & FR & _). repeat (split; [assumption|]). assumption. Qed.

  Lemma kenv_setbn : forall fr st bs m OW r b, kenv fr st bs m OW -> kenv fr st (setbn r b bs) m OW.
  Proof.
    intros fr st bs m OW r b (HEAP & AUX & ST & ERR & MI & LXP & FA & SO & RS & FR & FSZ). unfold kenv.
    do 8 (split; [assumption|]). split; [|split; [exact FR| exact FSZ]].
    eapply refs_stable_trans; [exact RS| apply refs_stable_setbn].
  Qed.

  Lemma kenv_set_recp : forall fr st bs m OW x y, kenv fr st bs m OW -> kenv fr st (set_recp x y bs) m OW.
  Proof.
    intros fr st bs m OW x y (HEAP & AUX & ST & ERR & MI & LXP & FA & SO & RS & FR & FSZ). unfold kenv.
    do 8 (split; [assumption|]). split; [|split; [exact FR| exact FSZ]].
    eapply refs_stable_trans; [exact RS|]. intros PL' i a H. apply ref_at_set_recp. exact H.
  Qed.

  Lemma kenv_set_mont : forall fr st bs m OW x y, kenv fr st bs m OW -> kenv fr st (set_mont x y bs) m OW.
  Proof.
    intros fr st bs m OW x y (HEAP & AUX & ST & ERR & MI & LXP & FA & SO & RS & FR & FSZ). unfold kenv.
    do 8 (split; [assumption|]). split; [|split; [exact FR| exact FSZ]].
    eapply refs_stable_trans; [exact RS|]. intros PL' i a H. apply ref_at_set_mont. exact H.
  Qed.

  Lemma ctop_call : forall (POST : machine_state -> Prop) (fr : list cell) (st : PState) (bs : bstate bptr) (m : mem) (OW : list block) (r : bnref) (ar : Z)
      (ra gp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    lo <= FB - 16 ->
    kenv fr st bs m OW -> lib_state bs m OW PL EA -> ref_at bs OW PL r ar -> wref PL r ->
    (forall m' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14,
        kenv fr st (setbn r (bn_correct_top_pure (getbn r bs)) bs) m' OW ->
        lib_state (setbn r (bn_correct_top_pure (getbn r bs)) bs) m' OW PL EA ->
        evt bgusegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) y0 y1 y2 x8 x9 y3 y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom bgusegs))) ->
    evt bgusegs POST (MS (mkR ra (Z_to_bv 64 FB) gp (Z_to_bv 64 RATP) t0 t1 t2 x8 x9 (Z_to_bv 64 ar) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 BN_CORRECT_TOP) fc None m (seg_rom bgusegs)).
  Proof using CEIL GLO LOFB FBSP SPB B63 SPR FROK.
    intros until fc. intros LO16 ENV LS HA WR K.
    pose proof ENV as (HEAP & AUX & ST & (errv & ERR) & MI & LXP & FA & SO & RS & FR & FSZ).
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (proj1 WR) as NRO.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
    destruct (lib_state_open [] bs m OW PL EA r ar LS ND HA ltac:(intros []) NRO) as ((D & BN & ARR) & (OK1 & OK2 & OK3 & OK4) & LSH).
    destruct (bn_arr_facts st OW LB m HEAP bs PL EA _ _ PARTS FROK r D HV NRO ARR) as (U & LEN & D0 & DC & DI & SEP).
    pose proof (SEP r ar HA) as SEPr. clear SEP.
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HA NRO) as (A0 & AC & AI).
    set (b := getbn r bs) in *.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR. unfold BG_DMAX in OK3. unfold GLOBALS_TOP in GLO.
    pose proof (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HA NRO) as AL.
    assert (UP : ub_ptr_ok (Z.of_nat (bn_top b)) D).
    { intros T0. apply (bn_arr_ualign _ _ _ _ _ _ _ _ _ _ HEAP PARTS ARR). clear - T0 OK2. lia. }
    eapply evt_cut.
    { eapply bn_correct_top_spec with (lo := lo) (A := ar) (D := D) (b := b);
        [exact BN | exact AL | exact UP | exact U | exact OK1 | exact OK2 | clear - OK3; lia | rewrite ESPv; exact ST | rewrite ESPv; clear - LO16; lia | exact MI
        | rewrite ESPv; clear - AC CEIL LO16 FBSP; lia | rewrite ESPv; clear - DC CEIL LO16 FBSP; lia | exact SEPr | reflexivity]. }
    intros ms' PO. unfold bn_small_post in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & E & MUc & WMc & MIc & STc & RES).
    subst ms'. rewrite ESPv in *.
    assert (U' : u64arr bgusegs m' D (wlimbs (bn_buf b))).
    { eapply u64arr_transport; [exact U | exact MUc | exact WMc |]. cbn [disjoint_from]. rewrite wlimbs_len. fold (bn_dmax b).
      split; [clear - DC CEIL LO16 FBSP; lia|]. split; [clear - SEPr; lia| exact I]. }
    eapply (rw_cells_transport bgusegs _ m m') in FR; [| exact MUc | exact WMc | cbn [disjoint_from]; rewrite FSZ; split; [right; lia|]; split; [clear - AC CEIL LOFB FBSP; lia| exact I]].
    eapply (rw_cells_transport bgusegs _ m m') in ERR; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; split; [left; lia|]; split; [clear - AI A0; lia| exact I]].
    assert (WOK : Forall (w_okc OW LB bs PL EA SPv false [r]) [(FB - 16, FB); (ar, ar + 24)]).
    { constructor; [apply w_stack; cbn [fst snd]; lia|].
      constructor; [eapply (w_struct OW LB bs PL EA SPv false [r] _ r ar); [left; reflexivity| exact HA| exact NRO| cbn; lia| cbn; lia]| constructor]. }
    assert (HWL : Forall (w_lib bs OW PL lo SPv) [(FB - 16, FB); (ar, ar + 24)]).
    { constructor; [left; cbn [fst snd]; lia|]. constructor; [right; right; exists r, ar; cbn [fst snd]; split; [exact HA|]; split; [exact NRO| lia] | constructor]. }
    assert (LS' : lib_state (setbn r (bn_correct_top_pure b) bs) m' OW PL EA).
    { unfold lib_state. eapply (lib_state_close [] bs m' OW PL EA r ar); [| exact ND | exact HA | exact NRO | | |].
      - exact (lib_state_frame st LB SPv B [r] bs m m' OW PL EA _ HEAP LSH MUc WMc FROK WOK).
      - exists D. split; [exact RES|].
        assert (ARR' : bn_arr m' OW (pl_of PL r) D b) by (eapply bn_arr_of_u64arr; [exact ARR| exact U']).
        unfold bn_arr in ARR' |- *. unfold bn_correct_top_pure, bn_dmax in *. cbn [bn_d bn_buf]. exact ARR'.
      - destruct (strip_top_spec (bn_buf b) (bn_top b) OK2) as (S1 & _ & _).
        unfold bg_ok, bn_correct_top_pure, bn_dmax, BG_DMAX in *. cbn [bn_buf bn_top bn_flags].
        split; [exact OK1|]. split; [clear - S1 OK2; lia|]. split; [clear - OK3; lia| exact OK4].
      - apply ids_ok_setbn_same; [exact (proj1 (proj2 (proj2 PARTS))) | exact HV | reflexivity]. }
    eapply K; [| exact LS'].
    apply kenv_setbn.
    eapply (kenv_silent fr fr st bs m m' OW _ errv);
      [exact ENV | exact PARTS | exact MUc | exact WMc | exact HWL | exact STc | unfold LX_ERRNO, RATP; exact ERR | exact MIc | exact FR | exact FSZ].
  Qed.

  Lemma kenv_below : forall fr st bs m m' OW K,
    kenv fr st bs m OW -> lib_state bs m OW PL EA -> 0 <= K -> lo <= FB - K ->
    munch [(FB - K, FB)] m m' -> wmono bgusegs m m' -> stk bgusegs m' lo FB -> mem_inv bgusegs m' ->
    kenv fr st bs m' OW /\ lib_state bs m' OW PL EA.
  Proof using CEIL GLO LOFB FBSP SPB B63 SPR FROK.
    intros fr st bs m m' OW K ENV LS K0 LOK MU WM ST' MI'.
    pose proof ENV as (HEAP & AUX & ST & (errv & ERR) & MI & LXP & FA & SO & RS & FR & FSZ).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. unfold GLOBALS_TOP in GLO.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    eapply (rw_cells_transport bgusegs _ m m') in FR; [| exact MU | exact WM | cbn [disjoint_from]; rewrite FSZ; split; [right; lia| exact I]].
    eapply (rw_cells_transport bgusegs _ m m') in ERR; [| exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; split; [left; lia| exact I]].
    assert (HWL : Forall (w_lib bs OW PL lo SPv) [(FB - K, FB)]) by (constructor; [left; cbn [fst snd]; lia| constructor]).
    assert (WOK : Forall (w_okc OW LB bs PL EA SPv false []) [(FB - K, FB)]) by (constructor; [apply w_stack; cbn [fst snd]; lia| constructor]).
    split.
    - eapply (kenv_silent fr fr st bs m m' OW _ errv);
        [exact ENV | exact PARTS | exact MU | exact WM | exact HWL | exact ST' | unfold LX_ERRNO, RATP; exact ERR | exact MI' | exact FR | exact FSZ].
    - exact (lib_state_frame st LB SPv B [] bs m m' OW PL EA _ HEAP LS MU WM FROK WOK).
  Qed.

  Lemma kenv_open : forall fr st bs m OW r a,
    kenv fr st bs m OW -> lib_state bs m OW PL EA -> ref_at bs OW PL r a -> r <> ROne ->
    exists D, rw_cells bgusegs m a (bn_cells D (getbn r bs)) /\ u64arr bgusegs m D (wlimbs (bn_buf (getbn r bs)))
      /\ bg_ok (getbn r bs) /\ 0 < a /\ (a + 24 <= lo \/ SPv <= a) /\ (D + 8 * Z.of_nat (bn_dmax (getbn r bs)) <= lo \/ SPv <= D)
      /\ (a + 24 <= D \/ D + 8 * Z.of_nat (bn_dmax (getbn r bs)) <= a).
  Proof using CEIL FROK.
    intros fr st bs m OW r a ENV LS HA NRO.
    pose proof ENV as (HEAP & _). pose proof (RH_nodup_l _ _ _ _ HEAP) as ND. pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
    destruct (lib_state_open [] bs m OW PL EA r a LS ND HA ltac:(intros []) NRO) as ((D & BN & ARR) & OK & _).
    destruct (bn_arr_facts st OW LB m HEAP bs PL EA _ _ PARTS FROK r D HV NRO ARR) as (U & LEN & D0 & DC & DI & SEP).
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HA NRO) as (A0 & AC & AI).
    exists D. split; [exact BN|]. split; [exact U|]. split; [exact OK|]. split; [exact A0|].
    split; [clear - AC CEIL; lia|]. split; [clear - DC CEIL; lia|]. exact (SEP r a HA).
  Qed.

  Lemma kenv_open_u : forall fr st bs m OW r a,
    kenv fr st bs m OW -> lib_state bs m OW PL EA -> ref_at bs OW PL r a -> r <> ROne ->
    exists D, rw_cells bgusegs m a (bn_cells D (getbn r bs)) /\ u64arr bgusegs m D (wlimbs (bn_buf (getbn r bs)))
      /\ bg_ok (getbn r bs) /\ 0 < a /\ (a + 24 <= lo \/ SPv <= a) /\ (D + 8 * Z.of_nat (bn_dmax (getbn r bs)) <= lo \/ SPv <= D)
      /\ (a + 24 <= D \/ D + 8 * Z.of_nat (bn_dmax (getbn r bs)) <= a)
      /\ (0 < a /\ a mod 8 = 0) /\ ub_ptr_ok (Z.of_nat (bn_top (getbn r bs))) D.
  Proof using CEIL FROK.
    intros fr st bs m OW r a ENV LS HA NRO.
    pose proof ENV as (HEAP & _). pose proof (RH_nodup_l _ _ _ _ HEAP) as ND. pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
    destruct (lib_state_open [] bs m OW PL EA r a LS ND HA ltac:(intros []) NRO) as ((D & BN & ARR) & OK & _).
    destruct (bn_arr_facts st OW LB m HEAP bs PL EA _ _ PARTS FROK r D HV NRO ARR) as (U & LEN & D0 & DC & DI & SEP).
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HA NRO) as (A0 & AC & AI).
    exists D. split; [exact BN|]. split; [exact U|]. split; [exact OK|]. split; [exact A0|].
    split; [clear - AC CEIL; lia|]. split; [clear - DC CEIL; lia|]. split; [exact (SEP r a HA)|].
    split; [exact (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HA NRO)|].
    intros T0. apply (bn_arr_ualign _ _ _ _ _ _ _ _ _ _ HEAP PARTS ARR). destruct OK as (_ & OK2 & _). clear - T0 OK2. lia.
  Qed.

  Lemma zero_call : forall (POST : machine_state -> Prop) (fr : list cell) (st : PState) (bs : bstate bptr) (m : mem) (OW : list block) (r : bnref) (ar : Z)
      (ra gp tp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    lo <= FB - 16 -> tp = Z_to_bv 64 RATP ->
    kenv fr st bs m OW -> lib_state bs m OW PL EA -> ref_at bs OW PL r ar -> wref PL r ->
    (forall m' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14,
        kenv fr st (setbn r (bn_zero_pure (getbn r bs)) bs) m' OW ->
        lib_state (setbn r (bn_zero_pure (getbn r bs)) bs) m' OW PL EA ->
        evt bgusegs POST (MS (mkR ra (Z_to_bv 64 FB) gp tp y0 y1 y2 x8 x9 y3 y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom bgusegs))) ->
    evt bgusegs POST (MS (mkR ra (Z_to_bv 64 FB) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 ar) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 BN_ZERO_EX) fc None m (seg_rom bgusegs)).
  Proof using CEIL GLO LOFB FBSP SPB B63 SPR FROK.
    intros until fc. intros LO16 -> ENV LS HA WR K.
    pose proof ENV as (HEAP & AUX & ST & (errv & ERR) & MI & LXP & FA & SO & RS & FR & FSZ).
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (proj1 WR) as NRO.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
    destruct (lib_state_open [] bs m OW PL EA r ar LS ND HA ltac:(intros []) NRO) as ((D & BN & ARR) & (OK1 & OK2 & OK3 & OK4) & LSH).
    destruct (bn_arr_facts st OW LB m HEAP bs PL EA _ _ PARTS FROK r D HV NRO ARR) as (U & LEN & D0 & DC & DI & SEP).
    pose proof (SEP r ar HA) as SEPr. clear SEP.
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HA NRO) as (A0 & AC & AI).
    set (b := getbn r bs) in *.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR. unfold BG_DMAX in OK3. unfold GLOBALS_TOP in GLO.
    eapply evt_cut.
    { eapply BN_zero_ex_spec with (lo := lo) (A := ar) (D := D) (b := b);
        [exact BN | exact (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HA NRO) | rewrite ESPv; exact ST | rewrite ESPv; clear - LO16; lia | exact MI | rewrite ESPv; clear - AC CEIL LO16 FBSP; lia | reflexivity]. }
    intros ms' PO. unfold bn_small_post in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & E & MUc & WMc & MIc & STc & RES).
    subst ms'. rewrite ESPv in *.
    assert (U' : u64arr bgusegs m' D (wlimbs (bn_buf b))).
    { eapply u64arr_transport; [exact U | exact MUc | exact WMc |]. cbn [disjoint_from]. rewrite wlimbs_len. fold (bn_dmax b).
      split; [clear - DC CEIL LO16 FBSP; lia|]. split; [clear - SEPr; lia| exact I]. }
    eapply (rw_cells_transport bgusegs _ m m') in FR; [| exact MUc | exact WMc | cbn [disjoint_from]; rewrite FSZ; split; [right; lia|]; split; [clear - AC CEIL LOFB FBSP; lia| exact I]].
    eapply (rw_cells_transport bgusegs _ m m') in ERR; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; split; [left; lia|]; split; [clear - AI A0; lia| exact I]].
    assert (WOK : Forall (w_okc OW LB bs PL EA SPv false [r]) [(FB - 16, FB); (ar, ar + 24)]).
    { constructor; [apply w_stack; cbn [fst snd]; lia|].
      constructor; [eapply (w_struct OW LB bs PL EA SPv false [r] _ r ar); [left; reflexivity| exact HA| exact NRO| cbn; lia| cbn; lia]| constructor]. }
    assert (HWL : Forall (w_lib bs OW PL lo SPv) [(FB - 16, FB); (ar, ar + 24)]).
    { constructor; [left; cbn [fst snd]; lia|]. constructor; [right; right; exists r, ar; cbn [fst snd]; split; [exact HA|]; split; [exact NRO| lia] | constructor]. }
    assert (LS' : lib_state (setbn r (bn_zero_pure b) bs) m' OW PL EA).
    { unfold lib_state. eapply (lib_state_close [] bs m' OW PL EA r ar); [| exact ND | exact HA | exact NRO | | |].
      - exact (lib_state_frame st LB SPv B [r] bs m m' OW PL EA _ HEAP LSH MUc WMc FROK WOK).
      - exists D. split; [exact RES|].
        assert (ARR' : bn_arr m' OW (pl_of PL r) D b) by (eapply bn_arr_of_u64arr; [exact ARR| exact U']).
        unfold bn_arr in ARR' |- *. unfold bn_zero_pure, bn_dmax in *. cbn [bn_d bn_buf]. exact ARR'.
      - unfold bg_ok, bn_zero_pure, bn_dmax, BG_DMAX in *. cbn [bn_buf bn_top bn_flags].
        split; [exact OK1|]. split; [clear; lia|]. split; [clear - OK3; lia| exact OK4].
      - apply ids_ok_setbn_same; [exact (proj1 (proj2 (proj2 PARTS))) | exact HV | reflexivity]. }
    eapply K; [| exact LS'].
    apply kenv_setbn.
    eapply (kenv_silent fr fr st bs m m' OW _ errv);
      [exact ENV | exact PARTS | exact MUc | exact WMc | exact HWL | exact STc | unfold LX_ERRNO, RATP; exact ERR | exact MIc | exact FR | exact FSZ].
  Qed.

  Lemma kenv_struct_store : forall fr st bs m OW r a,
    kenv fr st bs m OW -> lib_state bs m OW PL EA -> ref_at bs OW PL r a -> r <> ROne ->
    exists D, rw_cells bgusegs m a (bn_cells D (getbn r bs)) /\ bg_ok (getbn r bs)
      /\ 0 < a /\ (a + 24 <= lo \/ SPv <= a) /\ a + 24 < 2^63 /\ (a + 24 <= 0x10000 \/ 0x353000 <= a)
      /\ forall m' b',
           munch [(a, a + 24)] m m' -> wmono bgusegs m m' -> rw_cells bgusegs m' a (bn_cells D b') ->
           bn_d b' = bn_d (getbn r bs) -> bn_buf b' = bn_buf (getbn r bs) -> bg_ok b' ->
           stk bgusegs m' lo FB -> mem_inv bgusegs m' ->
           kenv fr st (setbn r b' bs) m' OW /\ lib_state (setbn r b' bs) m' OW PL EA.
  Proof using CEIL GLO LOFB FBSP SPB B63 SPR FROK.
    intros fr st bs m OW r a ENV LS HA NRO.
    pose proof ENV as (HEAP & AUX & ST & (errv & ERR) & MI & LXP & FA & SO & RS & FR & FSZ).
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
    destruct (lib_state_open [] bs m OW PL EA r a LS ND HA ltac:(intros []) NRO) as ((D & BN & ARR) & OK & LSH).
    destruct (bn_arr_facts st OW LB m HEAP bs PL EA _ _ PARTS FROK r D HV NRO ARR) as (U & LEN & D0 & DC & DI & SEP).
    pose proof (SEP r a HA) as SEPr. clear SEP.
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HA NRO) as (A0 & AC & AI).
    set (b := getbn r bs) in *.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR. unfold GLOBALS_TOP in GLO.
    exists D. split; [exact BN|]. split; [exact OK|]. split; [exact A0|]. split; [clear - AC CEIL; lia|].
    split; [clear - AC; lia|]. split; [exact AI|].
    intros m' b' MU WM BN' Ed Eb OK' ST' MI'.
    assert (U' : u64arr bgusegs m' D (wlimbs (bn_buf b))).
    { eapply u64arr_transport; [exact U | exact MU | exact WM |]. cbn [disjoint_from]. rewrite wlimbs_len. fold (bn_dmax b).
      split; [clear - SEPr; lia| exact I]. }
    eapply (rw_cells_transport bgusegs _ m m') in FR; [| exact MU | exact WM | cbn [disjoint_from]; rewrite FSZ; split; [clear - AC CEIL LOFB FBSP; lia| exact I]].
    eapply (rw_cells_transport bgusegs _ m m') in ERR; [| exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - AI A0; lia| exact I]].
    assert (WOK : Forall (w_okc OW LB bs PL EA SPv false [r]) [(a, a + 24)]).
    { constructor; [eapply (w_struct OW LB bs PL EA SPv false [r] _ r a); [left; reflexivity| exact HA| exact NRO| cbn; lia| cbn; lia]| constructor]. }
    assert (HWL : Forall (w_lib bs OW PL lo SPv) [(a, a + 24)]).
    { constructor; [right; right; exists r, a; cbn [fst snd]; split; [exact HA|]; split; [exact NRO| lia] | constructor]. }
    assert (LS' : lib_state (setbn r b' bs) m' OW PL EA).
    { unfold lib_state. eapply (lib_state_close [] bs m' OW PL EA r a); [| exact ND | exact HA | exact NRO | | exact OK' |].
      - exact (lib_state_frame st LB SPv B [r] bs m m' OW PL EA _ HEAP LSH MU WM FROK WOK).
      - exists D. split; [exact BN'|].
        assert (ARR' : bn_arr m' OW (pl_of PL r) D b) by (eapply bn_arr_of_u64arr; [exact ARR| exact U']).
        unfold bn_arr in ARR' |- *. unfold bn_dmax in *. rewrite Ed, Eb. exact ARR'.
      - apply ids_ok_setbn_same; [exact (proj1 (proj2 (proj2 PARTS))) | exact HV |]. unfold bn_blocks, bn_dmax. fold b. rewrite Ed, Eb. reflexivity. }
    split; [| exact LS'].
    apply kenv_setbn.
    eapply (kenv_silent fr fr st bs m m' OW _ errv);
      [exact ENV | exact PARTS | exact MU | exact WM | exact HWL | exact ST' | unfold LX_ERRNO, RATP; exact ERR | exact MI' | exact FR | exact FSZ].
  Qed.

  Lemma kenv_tail : forall fr st bs m OW K (errv0 : word)
      (ra gp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (Fr : bvmap 5 word) (fc : bv 32) {A : Type}
      (RES : A -> bstate bptr -> list block -> placement -> word -> Prop),
    kenv fr st bs m OW -> lib_state bs m OW PL EA -> stk bgusegs m lo SPv -> lo <= SPv - K ->
    (exists errv, bn_pre st bs m OW LB PL EA (Z_to_bv 64 SPv) lo B errv K)
    /\ (forall r st' ms', bn_post ra (Z_to_bv 64 SPv) gp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 Fr fc st bs OW LB lo B m PL EA RES r st' ms' ->
                          bn_post ra (Z_to_bv 64 SPv) gp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 Fr fc s0 bs0 OW0 LB lo B m0 PL EA RES r st' ms').
  Proof using CEIL GLO LOFB FBSP SPB B63 SPR FROK.
    intros until RES. intros ENV LS ST' LOK.
    pose proof ENV as (HEAP & AUX & ST & (errv & ERR) & MI & LXP & FA & SO & RS & FR & FSZ).
    assert (ESP : bv_unsigned (Z_to_bv 64 SPv) = SPv) by (apply unsigned_lit; lia).
    split.
    - exists errv. unfold bn_pre. rewrite ESP. split; [exact HEAP|]. split; [exact LS|]. split; [exact FROK|].
      repeat (split; [first [assumption | lia]|]). assumption.
    - intros r st' ms' PO. unfold bn_post in *. rewrite ESP in *.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m9 & OW9 & PL9 & errv9 & -> & HEAP9 & LS9 & AUX9 & ST9 & ERR9
                      & MI9 & LXP9 & FA9 & SO9 & RST9 & RES9).
      do 15 eexists. exists m9, OW9, PL9, errv9. split; [reflexivity|]. repeat (split; [assumption|]).
      split; [eapply lx_pres_trans; [exact LXP| exact LXP9]|].
      split; [congruence|]. split; [congruence|]. split; [eapply refs_stable_trans; [exact RS| exact RST9]| exact RES9].
  Qed.

End Env.
End WithCeiling0.
