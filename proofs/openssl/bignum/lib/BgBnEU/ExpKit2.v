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
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap W_small W_small2 W_top.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgIface BnUAlign.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnEU Require Import ExpKit PlaceRecp.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Section Env2.
  Variables (LB : list block) (PL0 : placement) (EA : BnRep.err_addrs) (lo B SPv FB an : Z).
  Variables (s0 : PState) (bs0 : bstate bptr) (OW0 : list block) (m0 : mem).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis LOFB : lo <= FB.
  Hypothesis FBSP : FB <= SPv.
  Hypothesis SPB : SPv <= B.
  Hypothesis B63 : B < 2^63.
  Hypothesis SPR : SPv < 2^64.
  Hypothesis FROK0 : frames_ok PL0 SPv B.
  Hypothesis AN1 : FB <= an.
  Hypothesis AN2 : an + 60 <= SPv.

  Local Notation PL := (pl_place_recp PL0 an).

  Definition kenv2 (fr1 fr2 : list cell) (st : PState) (bs : bstate bptr) (m : mem) (OW : list block) : Prop :=
    RHEAP st (OW ++ LB) m /\ rauxv_ok m B /\ stk bgusegs m lo FB /\ (exists errv : word, rw_cells bgusegs m LX_ERRNO [C4 errv]) /\ mem_inv bgusegs m
    /\ lx_pres LB SPv (XW PL0) m0 m /\ ps_fa st = ps_fa s0 /\ ps_so st = ps_so s0 /\ refs_stable bs0 OW0 bs OW
    /\ rw_cells bgusegs m FB fr1 /\ Z.of_nat (cells_size fr1) = an - FB
    /\ rw_cells bgusegs m (an + 60) fr2 /\ Z.of_nat (cells_size fr2) = SPv - (an + 60).

  Lemma ESPv2 : bv_unsigned (Z_to_bv 64 FB) = FB.
  Proof using CEIL LOFB FBSP SPR. clear - CEIL LOFB FBSP SPR. apply unsigned_lit. lia. Qed.

  Lemma FROK2 : frames_ok PL FB B.
  Proof using CEIL LOFB FBSP SPB FROK0 AN1 AN2.
    eapply (frames_ok_place_recp PL0 an SPv B FB FROK0); clear - CEIL LOFB FBSP SPB AN1 AN2; lia.
  Qed.

  Lemma lx_unplace : forall st L SP' m m', RHEAP st (L ++ LB) m -> SP' <= SPv -> lx_pres LB SP' (XW PL) m m' -> lx_pres LB SPv (XW PL0) m m'.
  Proof using CEIL GLO LOFB AN1 AN2.
    intros st L SP' m m' HEAP HS H a Ha [Hx Hc]. apply H; [exact Ha|]. split.
    - intros Hx'. apply xw_place_recp in Hx'. destruct Hx' as [Hx'|Hr]; [exact (Hx Hx')|].
      destruct Hc as [Hc|[(b & Hb & Hr')|Hc]].
      + clear - Hc Hr AN2. lia.
      + pose proof (LH_block_range _ _ _ b HEAP ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & BC & _).
        clear - BC Hr Hr' CEIL LOFB AN1. lia.
      + unfold GLOBALS_TOP in GLO. clear - Hc Hr GLO LOFB AN1. lia.
    - destruct Hc as [Hc|[Hc|Hc]]; [left; clear - Hc HS; lia| right; left; exact Hc| right; right; exact Hc].
  Qed.

  Lemma frame_client2 : forall x, FB <= x < SPv -> ~ (an <= x < an + 60) -> lx_client LB FB (XW PL) x.
  Proof using CEIL GLO LOFB FROK0.
    intros x Hx Hn. split; [|left; lia]. unfold XW. rewrite rin_ivs_app. intros [H|H].
    - revert H. unfold LIBW_bgr, BnRep.LIBW_bn, CONST_ONE, BN_STRUCT_SZ. cbn [rin_ivs app fst snd]. unfold GLOBALS_TOP in GLO. clear - Hx GLO LOFB. lia.
    - apply rin_ivs_In in H. destruct H as (iv & Hin & Hiv). apply pl_frames_place_recp_In in Hin.
      destruct Hin as [->|[->|[->|Hin]]]; cbn [fst snd] in Hiv; try (clear - Hiv Hn; lia).
      destruct (proj1 FROK0 iv Hin) as [P1 P2]. clear - P1 Hiv Hx. lia.
  Qed.

  Lemma lib_state_own2 : forall st bs m m' OW W,
    RHEAP st (OW ++ LB) m -> lib_state bs m OW PL EA -> munch W m m' -> wmono bgusegs m m' ->
    Forall (fun iv : Z * Z => an + 60 <= fst iv /\ snd iv <= SPv) W ->
    lib_state bs m' OW PL EA.
  Proof using CEIL GLO LOFB FBSP SPB FROK0 AN1 AN2.
    intros st bs m m' OW W HEAP LS MU WM HW.
    eapply (lib_state_frame_above st LB FB B); [exact HEAP| exact LS| exact MU| exact WM| exact FROK2|].
    eapply Forall_impl; [|exact HW]. intros [x y] [H1 H2]. cbn [fst snd] in *.
    split; [clear - H1 GLO LOFB AN1; lia|]. split; [clear - H1 CEIL LOFB AN1; lia|].
    intros z Hz Hr. apply rin_ivs_In in Hr. destruct Hr as (iv & Hin & Hiv). apply pl_frames_place_recp_In in Hin.
    destruct Hin as [->|[->|[->|Hin]]]; cbn [fst snd] in Hiv; try (clear - Hiv Hz H1; lia).
    destruct (proj1 FROK0 iv Hin) as [P1 P2]. clear - P1 Hiv Hz H2. lia.
  Qed.

  Lemma kenv2_pre : forall fr1 fr2 st bs m OW K,
    kenv2 fr1 fr2 st bs m OW -> lib_state bs m OW PL EA -> lo <= FB - K ->
    exists errv, bn_pre st bs m OW LB PL EA (Z_to_bv 64 FB) lo B errv K.
  Proof using CEIL GLO LOFB FBSP SPB B63 SPR FROK0 AN1 AN2.
    intros fr1 fr2 st bs m OW K (HEAP & AUX & ST & (errv & ERR) & MI & _) LS HK. exists errv.
    unfold bn_pre. rewrite ESPv2. split; [exact HEAP|]. split; [exact LS|]. split; [exact FROK2|].
    repeat (split; [first [assumption | lia]|]). assumption.
  Qed.

  Definition kpost2 (st : PState) (bs : bstate bptr) (m : mem) (OW : list block) (st' : PState) (bs' : bstate bptr) (m' : mem) (OW' : list block) : Prop :=
    RHEAP st' (OW' ++ LB) m' /\ lib_state bs' m' OW' PL EA /\ rauxv_ok m' B /\ stk bgusegs m' lo FB
    /\ (exists errv' : word, rw_cells bgusegs m' LX_ERRNO [C4 errv']) /\ mem_inv bgusegs m'
    /\ lx_pres LB FB (XW PL) m m' /\ ps_fa st' = ps_fa st /\ ps_so st' = ps_so st /\ refs_stable bs OW bs' OW'.

  Lemma kpost2_refs : forall st bs m OW st' bs' m' OW', kpost2 st bs m OW st' bs' m' OW' -> refs_stable bs OW bs' OW'.
  Proof. intros st bs m OW st' bs' m' OW' (_ & _ & _ & _ & _ & _ & _ & _ & _ & RS). exact RS. Qed.

  Lemma kenv2_post : forall fr1 fr2 st bs m OW st' bs' m' OW',
    kenv2 fr1 fr2 st bs m OW -> kpost2 st bs m OW st' bs' m' OW' -> kenv2 fr1 fr2 st' bs' m' OW' /\ lib_state bs' m' OW' PL EA.
  Proof using CEIL GLO LOFB FBSP FROK0 AN1 AN2.
    intros fr1 fr2 st bs m OW st' bs' m' OW' (HEAP & AUX & ST & ERR & MI & LXP & FA & SO & RS & FR1 & FSZ1 & FR2 & FSZ2)
           (HEAP' & LS' & AUX' & ST' & ERR' & MI' & LXP' & FA' & SO' & RS').
    split; [|exact LS'].
    unfold kenv2. split; [exact HEAP'|]. split; [exact AUX'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact MI'|].
    split. { eapply lx_pres_trans; [exact LXP|]. eapply (lx_unplace st OW FB); [exact HEAP| exact FBSP| exact LXP']. }
    split; [congruence|]. split; [congruence|].
    split; [eapply refs_stable_trans; eauto|].
    split. { eapply rw_cells_agree; [apply agree_of_lx_pres; exact LXP' | exact FR1 |]. intros a Ha. apply frame_client2; clear - Ha FSZ1 AN1 AN2; lia. }
    split; [exact FSZ1|].
    split; [| exact FSZ2].
    eapply rw_cells_agree; [apply agree_of_lx_pres; exact LXP' | exact FR2 |]. intros a Ha. apply frame_client2; clear - Ha FSZ2 AN1 AN2; lia.
  Qed.

  Lemma kenv2_post_raw : forall fr1 fr2 st bs m OW st' bs' m' OW' (errv' : word),
    kenv2 fr1 fr2 st bs m OW ->
    RHEAP st' (OW' ++ LB) m' -> rauxv_ok m' B -> stk bgusegs m' lo FB -> rw_cells bgusegs m' LX_ERRNO [C4 errv'] -> mem_inv bgusegs m' ->
    lx_pres LB FB (XW PL) m m' -> ps_fa st' = ps_fa st -> ps_so st' = ps_so st -> refs_stable bs OW bs' OW' ->
    kenv2 fr1 fr2 st' bs' m' OW'.
  Proof using CEIL GLO LOFB FBSP FROK0 AN1 AN2.
    intros fr1 fr2 st bs m OW st' bs' m' OW' errv' (HEAP & AUX & ST & ERR & MI & LXP & FA & SO & RS & FR1 & FSZ1 & FR2 & FSZ2)
           HEAP' AUX' ST' ERR' MI' LXP' FA' SO' RS'.
    unfold kenv2. split; [exact HEAP'|]. split; [exact AUX'|]. split; [exact ST'|]. split; [exists errv'; exact ERR'|]. split; [exact MI'|].
    split. { eapply lx_pres_trans; [exact LXP|]. eapply (lx_unplace st OW FB); [exact HEAP| exact FBSP| exact LXP']. }
    split; [congruence|]. split; [congruence|].
    split; [eapply refs_stable_trans; eauto|].
    split. { eapply rw_cells_agree; [apply agree_of_lx_pres; exact LXP' | exact FR1 |]. intros a Ha. apply frame_client2; clear - Ha FSZ1 AN1 AN2; lia. }
    split; [exact FSZ1|].
    split; [| exact FSZ2].
    eapply rw_cells_agree; [apply agree_of_lx_pres; exact LXP' | exact FR2 |]. intros a Ha. apply frame_client2; clear - Ha FSZ2 AN1 AN2; lia.
  Qed.

  Lemma bn_post_kpost2 : forall {A : Type} (ra gp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32)
      st bs OW m (RES : A -> bstate bptr -> list block -> placement -> word -> Prop) (r : A * bstate bptr) st' ms',
    bn_post ra (Z_to_bv 64 FB) gp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc st bs OW LB lo B m PL EA RES r st' ms' ->
    (forall v bs' OW' PL' a0', RES v bs' OW' PL' a0' -> PL' = PL) ->
    exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' OW',
      ms' = MS (mkR ra (Z_to_bv 64 FB) gp (wz RATP) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bgusegs)
      /\ kpost2 st bs m OW st' (snd r) m' OW' /\ RES (fst r) (snd r) OW' PL a0.
  Proof using CEIL LOFB FBSP SPR.
    intros A ra gp x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 F fc st bs OW m RES r st' ms' PO HPL. unfold bn_post in PO.
    destruct PO as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & OW' & PL' & errv' & E & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11).
    pose proof (HPL _ _ _ _ _ P11) as EPL. subst PL'.
    rewrite ESPv2 in *.
    exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', OW'. split; [exact E|]. split; [|exact P11].
    unfold kpost2. repeat (split; [first [assumption | exists errv'; assumption]|]). assumption.
  Qed.

  Lemma kenv2_silent : forall fr1 fr2 fr1' fr2' st bs m m' OW W (errv' : word),
    kenv2 fr1 fr2 st bs m OW -> lib_parts bs OW PL EA -> munch W m m' -> wmono bgusegs m m' -> Forall (w_lib bs OW PL lo SPv) W ->
    stk bgusegs m' lo FB -> rw_cells bgusegs m' LX_ERRNO [C4 errv'] -> mem_inv bgusegs m' ->
    rw_cells bgusegs m' FB fr1' -> Z.of_nat (cells_size fr1') = an - FB ->
    rw_cells bgusegs m' (an + 60) fr2' -> Z.of_nat (cells_size fr2') = SPv - (an + 60) ->
    kenv2 fr1' fr2' st bs m' OW.
  Proof using CEIL GLO LOFB FBSP SPB FROK0 AN1 AN2.
    intros fr1 fr2 fr1' fr2' st bs m m' OW W errv' (HEAP & AUX & ST & ERR & MI & LXP & FA & SO & RS & _) PARTS MU WM HW ST' ERR' MI' F1 Z1 F2 Z2.
    pose proof FROK2 as FR2K.
    unfold kenv2. split; [exact (seg_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FR2K MU WM HW CEIL)|].
    split; [apply (seg_auxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FR2K AUX MU WM HW SPB); lia|].
    split; [exact ST'|]. split; [exists errv'; exact ERR'|]. split; [exact MI'|].
    split. { eapply lx_pres_trans; [exact LXP|]. eapply (lx_unplace st OW SPv); [exact HEAP| lia|].
             apply (seg_lx_pres _ _ _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FR2K MU WM HW CEIL); lia. }
    split; [exact FA|]. split; [exact SO|]. split; [exact RS|]. split; [exact F1|]. split; [exact Z1|]. split; [exact F2| exact Z2].
  Qed.

  Lemma kenv2_setbn : forall fr1 fr2 st bs m OW r b, kenv2 fr1 fr2 st bs m OW -> kenv2 fr1 fr2 st (setbn r b bs) m OW.
  Proof.
    intros fr1 fr2 st bs m OW r b (HEAP & AUX & ST & ERR & MI & LXP & FA & SO & RS & REST). unfold kenv2.
    do 8 (split; [assumption|]). split; [|exact REST].
    eapply refs_stable_trans; [exact RS| apply refs_stable_setbn].
  Qed.

  Lemma kenv2_below : forall fr1 fr2 st bs m m' OW K,
    kenv2 fr1 fr2 st bs m OW -> lib_state bs m OW PL EA -> 0 <= K -> lo <= FB - K ->
    munch [(FB - K, FB)] m m' -> wmono bgusegs m m' -> stk bgusegs m' lo FB -> mem_inv bgusegs m' ->
    kenv2 fr1 fr2 st bs m' OW /\ lib_state bs m' OW PL EA.
  Proof using CEIL GLO LOFB FBSP SPB B63 SPR FROK0 AN1 AN2.
    intros fr1 fr2 st bs m m' OW K ENV LS K0 LOK MU WM ST' MI'.
    pose proof ENV as (HEAP & AUX & ST & (errv & ERR) & MI & LXP & FA & SO & RS & FR1 & FSZ1 & FR2 & FSZ2).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS. unfold GLOBALS_TOP in GLO.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR.
    eapply (rw_cells_transport bgusegs _ m m') in FR1; [| exact MU | exact WM | cbn [disjoint_from]; rewrite FSZ1; split; [right; lia| exact I]].
    eapply (rw_cells_transport bgusegs _ m m') in FR2; [| exact MU | exact WM | cbn [disjoint_from]; rewrite FSZ2; split; [right; lia| exact I]].
    eapply (rw_cells_transport bgusegs _ m m') in ERR; [| exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; split; [left; lia| exact I]].
    assert (HWL : Forall (w_lib bs OW PL lo SPv) [(FB - K, FB)]) by (constructor; [left; cbn [fst snd]; lia| constructor]).
    assert (WOK : Forall (w_okc OW LB bs PL EA FB false []) [(FB - K, FB)]) by (constructor; [apply w_stack; cbn [fst snd]; lia| constructor]).
    split.
    - eapply (kenv2_silent fr1 fr2 fr1 fr2 st bs m m' OW _ errv);
        [exact ENV | exact PARTS | exact MU | exact WM | exact HWL | exact ST' | unfold LX_ERRNO, RATP; exact ERR | exact MI' | exact FR1 | exact FSZ1 | exact FR2 | exact FSZ2].
    - exact (lib_state_frame st LB FB B [] bs m m' OW PL EA _ HEAP LS MU WM FROK2 WOK).
  Qed.

  Lemma kenv2_open : forall fr1 fr2 st bs m OW r a,
    kenv2 fr1 fr2 st bs m OW -> lib_state bs m OW PL EA -> ref_at bs OW PL r a -> r <> ROne ->
    exists D, rw_cells bgusegs m a (bn_cells D (getbn r bs)) /\ u64arr bgusegs m D (wlimbs (bn_buf (getbn r bs)))
      /\ bg_ok (getbn r bs) /\ 0 < a /\ (a + 24 <= lo \/ FB <= a) /\ (D + 8 * Z.of_nat (bn_dmax (getbn r bs)) <= lo \/ FB <= D)
      /\ (a + 24 <= D \/ D + 8 * Z.of_nat (bn_dmax (getbn r bs)) <= a).
  Proof using CEIL LOFB FBSP SPB FROK0 AN1 AN2.
    intros fr1 fr2 st bs m OW r a ENV LS HA NRO.
    pose proof ENV as (HEAP & _). pose proof (RH_nodup_l _ _ _ _ HEAP) as ND. pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
    destruct (lib_state_open [] bs m OW PL EA r a LS ND HA ltac:(intros []) NRO) as ((D & BN & ARR) & OK & _).
    destruct (bn_arr_facts st OW LB m HEAP bs PL EA _ _ PARTS FROK2 r D HV NRO ARR) as (U & LEN & D0 & DC & DI & SEP).
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK2 HA NRO) as (A0 & AC & AI).
    exists D. split; [exact BN|]. split; [exact U|]. split; [exact OK|]. split; [exact A0|].
    split; [clear - AC CEIL; lia|]. split; [clear - DC CEIL; lia|]. exact (SEP r a HA).
  Qed.

  Lemma pool_struct_low : forall st bs m OW i a, RHEAP st (OW ++ LB) m -> ref_at bs OW PL (RPool i) a -> 0 < a /\ a + 24 <= lo.
  Proof using CEIL.
    intros st bs m OW i a HEAP HA. unfold ref_at in HA.
    replace (RPool i <? NFIX)%nat with false in HA by (symmetry; apply Nat.ltb_ge; unfold RPool; lia).
    destruct HA as (q & H & _ & Hin & ->).
    pose proof (RH_range _ _ _ _ _ _ _ HEAP Hin) as (B0 & _ & _ & BC & _).
    pose proof (Nat.mod_upper_bound (RPool i - NFIX) BN_CTX_POOL_SIZE ltac:(unfold BN_CTX_POOL_SIZE; lia)) as MB.
    unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *. clear - B0 BC MB CEIL. lia.
  Qed.

  Lemma zero_call2 : forall (POST : machine_state -> Prop) (fr1 fr2 : list cell) (st : PState) (bs : bstate bptr) (m : mem) (OW : list block) (r : bnref) (ar : Z)
      (ra gp tp t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    lo <= FB - 16 -> tp = Z_to_bv 64 RATP ->
    kenv2 fr1 fr2 st bs m OW -> lib_state bs m OW PL EA -> ref_at bs OW PL r ar -> wref PL r -> (ar + 24 <= lo \/ SPv <= ar) ->
    (forall m' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14,
        kenv2 fr1 fr2 st (setbn r (bn_zero_pure (getbn r bs)) bs) m' OW ->
        lib_state (setbn r (bn_zero_pure (getbn r bs)) bs) m' OW PL EA ->
        evt bgusegs POST (MS (mkR ra (Z_to_bv 64 FB) gp tp y0 y1 y2 x8 x9 y3 y4 y5 y6 y7 y8 y9 y10 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y11 y12 y13 y14)
                           F (ret_pc ra) fc None m' (seg_rom bgusegs))) ->
    evt bgusegs POST (MS (mkR ra (Z_to_bv 64 FB) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 ar) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 BN_ZERO_EX) fc None m (seg_rom bgusegs)).
  Proof using CEIL GLO LOFB FBSP SPB B63 SPR FROK0 AN1 AN2.
    intros until fc. intros LO16 -> ENV LS HA WR SEPA K.
    pose proof ENV as (HEAP & AUX & ST & (errv & ERR) & MI & LXP & FA & SO & RS & FR1 & FSZ1 & FR2 & FSZ2).
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (proj1 WR) as NRO.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
    destruct (lib_state_open [] bs m OW PL EA r ar LS ND HA ltac:(intros []) NRO) as ((D & BN & ARR) & (OK1 & OK2 & OK3 & OK4) & LSH).
    destruct (bn_arr_facts st OW LB m HEAP bs PL EA _ _ PARTS FROK2 r D HV NRO ARR) as (U & LEN & D0 & DC & DI & SEP).
    pose proof (SEP r ar HA) as SEPr. clear SEP.
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK2 HA NRO) as (A0 & AC & AI).
    set (b := getbn r bs) in *.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR. unfold BG_DMAX in OK3. unfold GLOBALS_TOP in GLO.
    eapply evt_cut.
    { eapply BN_zero_ex_spec with (lo := lo) (A := ar) (D := D) (b := b);
        [exact BN | exact (ref_at_ualign _ _ _ _ _ _ _ _ _ HEAP PARTS HA NRO) | rewrite ESPv2; exact ST | rewrite ESPv2; clear - LO16; lia | exact MI | rewrite ESPv2; clear - SEPA LO16 FBSP; lia | reflexivity]. }
    intros ms' PO. unfold bn_small_post in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & E & MUc & WMc & MIc & STc & RES).
    subst ms'. rewrite ESPv2 in *.
    assert (U' : u64arr bgusegs m' D (wlimbs (bn_buf b))).
    { eapply u64arr_transport; [exact U | exact MUc | exact WMc |]. cbn [disjoint_from]. rewrite wlimbs_len. fold (bn_dmax b).
      split; [clear - DC CEIL LO16 FBSP LOFB; lia|]. split; [clear - SEPr; lia| exact I]. }
    eapply (rw_cells_transport bgusegs _ m m') in FR1; [| exact MUc | exact WMc | cbn [disjoint_from]; rewrite FSZ1; split; [right; lia|]; split; [clear - SEPA LOFB FBSP AN1 AN2; lia| exact I]].
    eapply (rw_cells_transport bgusegs _ m m') in FR2; [| exact MUc | exact WMc | cbn [disjoint_from]; rewrite FSZ2; split; [right; clear - AN1; lia|]; split; [clear - SEPA LOFB FBSP AN1 AN2; lia| exact I]].
    eapply (rw_cells_transport bgusegs _ m m') in ERR; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; split; [left; lia|]; split; [clear - AI A0; lia| exact I]].
    assert (WOK : Forall (w_okc OW LB bs PL EA FB false [r]) [(FB - 16, FB); (ar, ar + 24)]).
    { constructor; [apply w_stack; cbn [fst snd]; lia|].
      constructor; [eapply (w_struct OW LB bs PL EA FB false [r] _ r ar); [left; reflexivity| exact HA| exact NRO| cbn; lia| cbn; lia]| constructor]. }
    assert (HWL : Forall (w_lib bs OW PL lo SPv) [(FB - 16, FB); (ar, ar + 24)]).
    { constructor; [left; cbn [fst snd]; lia|]. constructor; [right; right; exists r, ar; cbn [fst snd]; split; [exact HA|]; split; [exact NRO| lia] | constructor]. }
    assert (LS' : lib_state (setbn r (bn_zero_pure b) bs) m' OW PL EA).
    { unfold lib_state. eapply (lib_state_close [] bs m' OW PL EA r ar); [| exact ND | exact HA | exact NRO | | |].
      - exact (lib_state_frame st LB FB B [r] bs m m' OW PL EA _ HEAP LSH MUc WMc FROK2 WOK).
      - exists D. split; [exact RES|].
        assert (ARR' : bn_arr m' OW (pl_of PL r) D b) by (eapply bn_arr_of_u64arr; [exact ARR| exact U']).
        unfold bn_arr in ARR' |- *. unfold bn_zero_pure, bn_dmax in *. cbn [bn_d bn_buf]. exact ARR'.
      - unfold bg_ok, bn_zero_pure, bn_dmax, BG_DMAX in *. cbn [bn_buf bn_top bn_flags].
        split; [exact OK1|]. split; [clear; lia|]. split; [clear - OK3; lia| exact OK4].
      - apply ids_ok_setbn_same; [exact (proj1 (proj2 (proj2 PARTS))) | exact HV | reflexivity]. }
    eapply K; [| exact LS'].
    apply kenv2_setbn.
    eapply (kenv2_silent fr1 fr2 fr1 fr2 st bs m m' OW _ errv);
      [exact ENV | exact PARTS | exact MUc | exact WMc | exact HWL | exact STc | unfold LX_ERRNO, RATP; exact ERR | exact MIc | exact FR1 | exact FSZ1 | exact FR2 | exact FSZ2].
  Qed.

  Lemma kenv2_struct_store : forall fr1 fr2 st bs m OW r a,
    kenv2 fr1 fr2 st bs m OW -> lib_state bs m OW PL EA -> ref_at bs OW PL r a -> r <> ROne -> (a + 24 <= lo \/ SPv <= a) ->
    exists D, rw_cells bgusegs m a (bn_cells D (getbn r bs)) /\ bg_ok (getbn r bs)
      /\ 0 < a /\ a + 24 < 2^63 /\ (a + 24 <= 0x10000 \/ 0x353000 <= a)
      /\ forall m' b',
           munch [(a, a + 24)] m m' -> wmono bgusegs m m' -> rw_cells bgusegs m' a (bn_cells D b') ->
           bn_d b' = bn_d (getbn r bs) -> bn_buf b' = bn_buf (getbn r bs) -> bg_ok b' ->
           stk bgusegs m' lo FB -> mem_inv bgusegs m' ->
           kenv2 fr1 fr2 st (setbn r b' bs) m' OW /\ lib_state (setbn r b' bs) m' OW PL EA.
  Proof using CEIL GLO LOFB FBSP SPB B63 SPR FROK0 AN1 AN2.
    intros fr1 fr2 st bs m OW r a ENV LS HA NRO SEPA.
    pose proof ENV as (HEAP & AUX & ST & (errv & ERR) & MI & LXP & FA & SO & RS & FR1 & FSZ1 & FR2 & FSZ2).
    pose proof (RH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
    pose proof (ref_at_valid _ _ _ _ _ _ _ _ LS HA) as HV.
    destruct (lib_state_open [] bs m OW PL EA r a LS ND HA ltac:(intros []) NRO) as ((D & BN & ARR) & OK & LSH).
    destruct (bn_arr_facts st OW LB m HEAP bs PL EA _ _ PARTS FROK2 r D HV NRO ARR) as (U & LEN & D0 & DC & DI & SEP).
    pose proof (SEP r a HA) as SEPr. clear SEP.
    pose proof (ref_at_range _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK2 HA NRO) as (A0 & AC & AI).
    set (b := getbn r bs) in *.
    unfold LX_ERRNO, RATP in ERR. change (3346328 - 164) with 3346164 in ERR. unfold GLOBALS_TOP in GLO.
    exists D. split; [exact BN|]. split; [exact OK|]. split; [exact A0|].
    split; [clear - AC; lia|]. split; [exact AI|].
    intros m' b' MU WM BN' Ed Eb OK' ST' MI'.
    assert (U' : u64arr bgusegs m' D (wlimbs (bn_buf b))).
    { eapply u64arr_transport; [exact U | exact MU | exact WM |]. cbn [disjoint_from]. rewrite wlimbs_len. fold (bn_dmax b).
      split; [clear - SEPr; lia| exact I]. }
    eapply (rw_cells_transport bgusegs _ m m') in FR1; [| exact MU | exact WM | cbn [disjoint_from]; rewrite FSZ1; split; [clear - SEPA LOFB FBSP AN1 AN2; lia| exact I]].
    eapply (rw_cells_transport bgusegs _ m m') in FR2; [| exact MU | exact WM | cbn [disjoint_from]; rewrite FSZ2; split; [clear - SEPA LOFB FBSP AN1 AN2; lia| exact I]].
    eapply (rw_cells_transport bgusegs _ m m') in ERR; [| exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - AI A0; lia| exact I]].
    assert (WOK : Forall (w_okc OW LB bs PL EA FB false [r]) [(a, a + 24)]).
    { constructor; [eapply (w_struct OW LB bs PL EA FB false [r] _ r a); [left; reflexivity| exact HA| exact NRO| cbn; lia| cbn; lia]| constructor]. }
    assert (HWL : Forall (w_lib bs OW PL lo SPv) [(a, a + 24)]).
    { constructor; [right; right; exists r, a; cbn [fst snd]; split; [exact HA|]; split; [exact NRO| lia] | constructor]. }
    assert (LS' : lib_state (setbn r b' bs) m' OW PL EA).
    { unfold lib_state. eapply (lib_state_close [] bs m' OW PL EA r a); [| exact ND | exact HA | exact NRO | | exact OK' |].
      - exact (lib_state_frame st LB FB B [r] bs m m' OW PL EA _ HEAP LSH MU WM FROK2 WOK).
      - exists D. split; [exact BN'|].
        assert (ARR' : bn_arr m' OW (pl_of PL r) D b) by (eapply bn_arr_of_u64arr; [exact ARR| exact U']).
        unfold bn_arr in ARR' |- *. unfold bn_dmax in *. rewrite Ed, Eb. exact ARR'.
      - apply ids_ok_setbn_same; [exact (proj1 (proj2 (proj2 PARTS))) | exact HV |]. unfold bn_blocks, bn_dmax. fold b. rewrite Ed, Eb. reflexivity. }
    split; [| exact LS'].
    apply kenv2_setbn.
    eapply (kenv2_silent fr1 fr2 fr1 fr2 st bs m m' OW _ errv);
      [exact ENV | exact PARTS | exact MU | exact WM | exact HWL | exact ST' | unfold LX_ERRNO, RATP; exact ERR | exact MI' | exact FR1 | exact FSZ1 | exact FR2 | exact FSZ2].
  Qed.

  Lemma kenv_place : forall fr1 fr2 st bs m OW,
    kenv LB PL0 lo B SPv FB s0 bs0 OW0 m0 (fr1 ++ (bn_cells 0 (bn_nil 0) ++ bn_cells 0 (bn_nil 0) ++ [C4 (wz 0); C4 (wz 0); C4 (wz 0)]) ++ fr2) st bs m OW ->
    lib_state bs m OW PL0 EA -> Z.of_nat (cells_size fr1) = an - FB -> 0 < an -> an mod 8 = 0 ->
    pl_bn PL0 RRecpN = None -> pl_bn PL0 RRecpNr = None -> pl_recp PL0 = None ->
    kenv2 fr1 fr2 st (st_recp_init bs) m OW /\ lib_state (st_recp_init bs) m OW PL EA.
  Proof using CEIL GLO LOFB FBSP SPB FROK0 AN1 AN2.
    intros fr1 fr2 st bs m OW (HEAP & AUX & ST & ERR & MI & LXP & FA & SO & RS & FR & FSZ) LS Z1 A0 A8 E1 E2 E3.
    apply bk_rw_cells_app in FR. destruct FR as [F1 FR]. rewrite Z1 in FR. replace (FB + (an - FB)) with an in FR by lia.
    apply bk_rw_cells_app in FR. destruct FR as [FRC F2].
    change (Z.of_nat (cells_size (bn_cells 0 (bn_nil 0) ++ bn_cells 0 (bn_nil 0) ++ [C4 (wz 0); C4 (wz 0); C4 (wz 0)]))) with 60 in F2.
    apply bk_rw_cells_app in FRC. destruct FRC as [C1 FRC]. change (Z.of_nat (cells_size (bn_cells 0 (bn_nil 0)))) with 24 in FRC.
    apply bk_rw_cells_app in FRC. destruct FRC as [C2 C3]. change (Z.of_nat (cells_size (bn_cells 0 (bn_nil 0)))) with 24 in C3.
    replace (an + 24 + 24) with (an + 48) in C3 by lia.
    assert (Z2 : Z.of_nat (cells_size fr2) = SPv - (an + 60)).
    { rewrite !cells_size_app in FSZ. change (cells_size (bn_cells 0 (bn_nil 0))) with 24%nat in FSZ.
      change (cells_size [C4 (wz 0); C4 (wz 0); C4 (wz 0)]) with 12%nat in FSZ. clear - FSZ Z1. lia. }
    split.
    - unfold kenv2. do 5 (split; [assumption|]). split; [exact LXP|]. split; [exact FA|]. split; [exact SO|].
      split. { unfold st_recp_init. eapply refs_stable_trans; [exact RS|]. eapply refs_stable_trans; [|apply refs_stable_setbn].
               eapply refs_stable_trans; [|apply refs_stable_setbn]. intros PL' i a H. apply ref_at_set_recp. exact H. }
      split; [exact F1|]. split; [exact Z1|]. split; [exact F2| exact Z2].
    - unfold lib_state. eapply (lib_state_place_recp false [] bs m OW PL0 EA an SPv B); try assumption.
  Qed.

End Env2.
End WithCeiling0.
