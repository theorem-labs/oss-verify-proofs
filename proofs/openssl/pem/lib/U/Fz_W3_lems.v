(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_M_free Fz_M_secure
     Fz_M_clear_free Fz_M_clear_realloc Fz_W1_defs Fz_W1_sync Fz_W1_growc Fz_W1_writec Fz_W3_iface Fz_W2_rep Fz_W3_defs.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation wz := (Z_to_bv 64) (only parsing).
Definition hideP (X : Prop) : Prop := X.
Ltac hide H := lazymatch type of H with ?X => change X with (hideP X) in H end.

Section W3. Context {CE__ : Ceiling} {RN__ : RunRnd}.
  Variable libenv : mem -> list block -> Z -> Prop.
  Variable libenv_fp : list block -> Z -> Prop.
  Hypothesis libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
  Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a ->
    (0x2c0000 <= a < 0x353000 /\ ~ ralloc_static a /\ a <> LX_FLAGS) \/ (exists b, In b LBL /\ blk_addr b <= a < blk_addr b + blk_size b).
  Variable errst_at_rest : Z -> list block -> mem -> Prop.
  Variable errst_live : Z -> Z -> Z -> list block -> mem -> Prop.
  Variable errst_fp : Z -> list block -> Z -> Prop.
  Hypothesis errst_rest_agree : forall m m' E strs, errst_at_rest E strs m -> agree_on (errst_fp E strs) m m' -> errst_at_rest E strs m'.
  Hypothesis errst_live_agree : forall m m' E top bot strs, errst_live E top bot strs m -> agree_on (errst_fp E strs) m m' -> errst_live E top bot strs m'.
  Hypothesis errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ (exists b, In b strs /\ blk_addr b <= a < blk_addr b + blk_size b).
  Hypothesis errst_rest_live : forall m E, errst_at_rest E [] m -> errst_live E 0 0 [] m.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma libenv_cfr : forall m m' T SP LBall LBL E, libenv m LBL E -> cfr T [] SP LBall m m' -> incl_blocks LBL LBall -> (forall b, In b LBL -> ~ T (blk_id b)) ->
    libenv m' LBL E.
  Proof.
    intros m m' T SP LBall LBL E LE CFR INCL NT. eapply libenv_agree; [exact LE|]. eapply agree_on_mono; [exact CFR|].
    intros a Ha. destruct (libenv_fp_where _ _ Ha) as [(R1 & R2 & R3)|(b & Hb & Rb)].
    - right; right. split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. cbn. tauto.
    - right; left. exists b. split; [exact (INCL _ Hb)|]. split; [exact (NT _ Hb)| exact Rb].
  Qed.

  Lemma pem_err_cfr : forall en strs m m' T SP LBall, pem_err errst_at_rest errst_live en strs m -> cfr T [] SP LBall m m' ->
    In (e_pe en, e_E en, 904) LBall -> ~ T (e_pe en) -> incl_blocks strs LBall -> (forall b, In b strs -> ~ T (blk_id b)) -> pem_err errst_at_rest errst_live en strs m'.
  Proof.
    intros en strs m m' T SP LBall PE CFR INE NTE INCL NT.
    assert (AG : agree_on (errst_fp (e_E en) strs) m m').
    { eapply agree_on_mono; [exact CFR|]. intros a Ha. right; left. destruct (errst_fp_where _ _ _ Ha) as [R|(b & Hb & Rb)].
      - exists (e_pe en, e_E en, 904). split; [exact INE|]. split; [exact NTE|]. unfold blk_addr, blk_size; cbn [fst snd]. exact R.
      - exists b. split; [exact (INCL _ Hb)|]. split; [exact (NT _ Hb)| exact Rb]. }
    destruct PE as [[-> R]|(top & bot & LV & LEN)]; [left; split; [reflexivity| eapply errst_rest_agree; [exact R| exact AG]]| right].
    exists top, bot. split; [eapply errst_live_agree; [exact LV| exact AG]| exact LEN].
  Qed.

  Lemma incl_blocks_keep : forall (T : bptr -> Prop) LBL LB0 L0 LBc Lc, incl_blocks LBL LB0 -> ckeep T LB0 L0 LBc Lc -> (forall b, In b LBL -> ~ T (blk_id b)) -> incl_blocks LBL LBc.
  Proof. intros T LBL LB0 L0 LBc Lc INCL [K _] NT b Hb. apply K; [exact (INCL _ Hb)| exact (NT _ Hb)]. Qed.

  (* [comment removed for export] *)
  Lemma cown_keep : forall (LB LB' : list block) (L L' : @clist bptr) p A n nm,
    cown LB L p A n nm -> (In (p, A, n) LB -> In (p, A, n) LB') -> (In (p, nm) L -> In (p, nm) L') -> cown LB' L' p A n nm.
  Proof. intros LB LB' L L' p A n nm [I1 I2] K1 K2. split; [exact (K1 I1)| exact (K2 I2)]. Qed.

  Lemma pem_out_keep : forall ret m m' T SP (LB LB' : list block) (L L' : @clist bptr) PL news,
    pem_out ret m LB L (PL + 24) (PL + 16) (PL + 8) PL news -> cfr T [] SP LB m m' -> SP <= PL ->
    (forall p A n nm, In (p, A, n) news -> cown LB L p A n nm -> cown LB' L' p A n nm) -> incl_blocks news LB -> (forall b, In b news -> ~ T (blk_id b)) ->
    pem_out ret m' LB' L' (PL + 24) (PL + 16) (PL + 8) PL news.
  Proof.
    intros ret m m' T SP LB LB' L L' PL news PO CFR HSP KO INCL NT.
    destruct PO as [(-> & -> & C1 & C2 & C3 & (lw & C4))|(-> & qn & qh & qd & NM & HD & DT & nn & nh & dlen & bn & bh & bd & -> & O1 & O2 & O3 & R1 & R2 & R3 & C1 & C2 & C3 & C4 & L1 & B1 & Z1 & L2 & B2 & Z2 & L3 & B3)].
    - left. split; [reflexivity|]. split; [reflexivity|].
      split; [exact (cfr_cells_stack _ _ _ _ _ _ _ _ CFR C1 ltac:(lia))|]. split; [exact (cfr_cells_stack _ _ _ _ _ _ _ _ CFR C2 ltac:(lia))|].
      split; [exact (cfr_cells_stack _ _ _ _ _ _ _ _ CFR C3 ltac:(lia))| exists lw; exact (cfr_cells_stack _ _ _ _ _ _ _ _ CFR C4 ltac:(lia))].
    - right. split; [reflexivity|]. exists qn, qh, qd, NM, HD, DT, nn, nh, dlen, bn, bh, bd. split; [reflexivity|].
      assert (I3 : In (qn, NM, nn) [(qd, DT, dlen); (qh, HD, nh); (qn, NM, nn)]) by (do 2 right; left; reflexivity).
      assert (I2 : In (qh, HD, nh) [(qd, DT, dlen); (qh, HD, nh); (qn, NM, nn)]) by (right; left; reflexivity).
      assert (I1 : In (qd, DT, dlen) [(qd, DT, dlen); (qh, HD, nh); (qn, NM, nn)]) by (left; reflexivity).
      split; [exact (KO _ _ _ _ I3 O1)|]. split; [exact (KO _ _ _ _ I2 O2)|]. split; [exact (KO _ _ _ _ I1 O3)|]. split; [exact R1|]. split; [exact R2|]. split; [exact R3|].
      split; [exact (cfr_cells_stack _ _ _ _ _ _ _ _ CFR C1 ltac:(lia))|]. split; [exact (cfr_cells_stack _ _ _ _ _ _ _ _ CFR C2 ltac:(lia))|].
      split; [exact (cfr_cells_stack _ _ _ _ _ _ _ _ CFR C3 ltac:(lia))|]. split; [exact (cfr_cells_stack _ _ _ _ _ _ _ _ CFR C4 ltac:(lia))|].
      split; [exact L1|]. split; [exact (cfr_cells_block _ _ _ _ _ _ _ _ _ CFR B1 (INCL _ I3) (NT _ I3) ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia))|].
      split; [exact Z1|]. split; [exact L2|]. split; [exact (cfr_cells_block _ _ _ _ _ _ _ _ _ CFR B2 (INCL _ I2) (NT _ I2) ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia))|].
      split; [exact Z2|]. split; [exact L3|]. exact (cfr_cells_block _ _ _ _ _ _ _ _ _ CFR B3 (INCL _ I1) (NT _ I1) ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia)).
  Qed.

  Lemma nd_split : forall (l1 l2 : list bptr), List.NoDup (l1 ++ l2) -> List.NoDup l1 /\ List.NoDup l2 /\ (forall x, In x l1 -> In x l2 -> False).
  Proof.
    intros l1 l2 ND. split; [exact (List.NoDup_app_remove_r _ _ ND)|]. split; [exact (List.NoDup_app_remove_l _ _ ND)|].
    induction l1 as [|y l1 IH]; intros x Hx H2; [destruct Hx|]. cbn [app] in ND. inversion ND as [|y' l' NI ND']; subst.
    destruct Hx as [<-|Hx]; [apply NI; apply in_or_app; right; exact H2| exact (IH ND' x Hx H2)].
  Qed.
  Lemma mbio_T_blocks : forall K q, mbio_T K q <-> In q (mbio_blocks K).
  Proof.
    intros K q. unfold mbio_T, mbio_blocks. rewrite in_app_iff. cbn [In]. destruct (k_d K) as [d|]; cbn [In].
    - split; [intros [H|[H|[H|[H|H]]]]; [left| left| left| left| right; left; congruence]; auto| intros [[H|[H|[H|[H|[]]]]]|[H|[]]]; subst; tauto].
    - split; [intros [H|[H|[H|[H|H]]]]; [left| left| left| left| discriminate]; auto| intros [[H|[H|[H|[H|[]]]]]|[]]; subst; tauto].
  Qed.
  (* [comment removed for export] *)
  Definition wfree (LBc : list block) (lo hi : Z) (EX : bptr -> Prop) (iv : Z * Z) : Prop :=
    (lo <= fst iv /\ snd iv <= hi) \/ (exists b, In b LBc /\ ~ EX (blk_id b) /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).

  Lemma wfree_outside : forall (W : list (Z * Z)) s LBc LB0 L m sp tp lo hi B EX a,
    cstate s LBc LB0 L m sp tp lo B -> Forall (wfree LBc lo hi EX) W ->
    (a < lo /\ 0x2c0000 <= a < 0x353000 \/ exists b, In b LBc /\ EX (blk_id b) /\ blk_addr b <= a < blk_addr b + blk_size b) -> outside W a.
  Proof.
    intros W s LBc LB0 L m sp tp lo hi B EX a CST HW Ha. pose proof CST as (HP & _). pose proof (cstate_B _ _ _ _ _ _ _ _ _ CST) as (_ & LO & _).
    induction HW as [|[x y] W HX HW IH]; cbn; [exact I|]. split; [| exact IH]. unfold wfree in HX. cbn [fst snd] in HX.
    destruct HX as [[H1 H2]|(b & Hb & NX & H1 & H2)].
    - destruct Ha as [[Ha _]|(b & Hb & _ & Rb)]; [lia|]. pose proof (RHEAP_block_range_proof _ _ _ b HP Hb) as (_ & _ & _ & RC & _). lia.
    - pose proof (RHEAP_block_range_proof _ _ _ b HP Hb) as (R0 & _ & _ & RC & RR).
      destruct Ha as [[_ Ha]|(b' & Hb' & IX & Rb')]; [lia|].
      destruct (RHEAP_blocks_disjoint_proof _ _ _ b b' HP Hb Hb' ltac:(intros E; apply NX; rewrite E; exact IX)); lia.
  Qed.

  Lemma libenv_munch : forall (W : list (Z * Z)) m m' s LBc LB0 L sp tp lo hi B LBL E (EX : bptr -> Prop),
    libenv m LBL E -> munch W m m' -> wmono usegs m m' -> cstate s LBc LB0 L m sp tp lo B -> incl_blocks LBL LBc ->
    Forall (wfree LBc lo hi EX) W -> (forall b, In b LBL -> EX (blk_id b)) -> libenv m' LBL E.
  Proof.
    intros W m m' s LBc LB0 L sp tp lo hi B LBL E EX LE MU WM CST INCL HW HX. pose proof (cstate_B _ _ _ _ _ _ _ _ _ CST) as (_ & LO & GLO). unfold GLOBALS_TOP in GLO.
    eapply libenv_agree; [exact LE|]. eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU WM)|]. cbv beta. intros a Ha.
    eapply wfree_outside; [exact CST| exact HW|]. destruct (libenv_fp_where _ _ Ha) as [(R & _)|(b & Hb & Rb)]; [left; lia| right; exists b; split; [exact (INCL _ Hb)| split; [exact (HX _ Hb)| exact Rb]]].
  Qed.

  Lemma pem_err_munch : forall (W : list (Z * Z)) en strs m m' s LBc LB0 L sp tp lo hi B EX,
    pem_err errst_at_rest errst_live en strs m -> munch W m m' -> wmono usegs m m' -> cstate s LBc LB0 L m sp tp lo B ->
    In (e_pe en, e_E en, 904) LBc -> incl_blocks strs LBc -> Forall (wfree LBc lo hi EX) W -> EX (e_pe en) -> (forall b, In b strs -> EX (blk_id b)) ->
    pem_err errst_at_rest errst_live en strs m'.
  Proof.
    intros W en strs m m' s LBc LB0 L sp tp lo hi B EX PE MU WM CST INE INCL HW HXE HX.
    assert (AG : agree_on (errst_fp (e_E en) strs) m m').
    { eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU WM)|]. cbv beta. intros a Ha. eapply wfree_outside; [exact CST| exact HW|]. right.
      destruct (errst_fp_where _ _ _ Ha) as [R|(b & Hb & Rb)].
      - exists (e_pe en, e_E en, 904). split; [exact INE|]. split; [exact HXE|]. unfold blk_addr, blk_size; cbn [fst snd]. exact R.
      - exists b. split; [exact (INCL _ Hb)|]. split; [exact (HX _ Hb)| exact Rb]. }
    destruct PE as [[-> R]|(top & bot & LV & LEN)]; [left; split; [reflexivity| eapply errst_rest_agree; [exact R| exact AG]]| right].
    exists top, bot. split; [eapply errst_live_agree; [exact LV| exact AG]| exact LEN].
  Qed.

  Lemma mbio_fp_munch : forall (W : list (Z * Z)) m m' s LBc LB0 L sp tp lo hi B K EX,
    cstate s LBc LB0 L m sp tp lo B -> munch W m m' -> wmono usegs m m' -> Forall (wfree LBc lo hi EX) W -> (forall q, mbio_T K q -> EX q) ->
    agree_on (mbio_fp LBc K) m m'.
  Proof.
    intros W m m' s LBc LB0 L sp tp lo hi B K EX CST MU WM HW HX.
    eapply agree_on_mono; [exact (agree_on_of_munch _ _ _ MU WM)|]. cbv beta. intros a (b & Hb & Tb & Rb).
    eapply wfree_outside; [exact CST| exact HW|]. right. exists b. split; [exact Hb|]. split; [exact (HX _ Tb)| exact Rb].
  Qed.

  (* [comment removed for export] *)
  Lemma com_call : forall en s LBc Lc f m off rem rA rB rBig (T1 : bptr -> Prop) SPc s1 LB1 L1 m1 (f1 EV1 rem' : nat) dA dB dBig rA' rB' rBig',
    pem_com libenv en s LBc Lc f m off rem rA rB rBig ->
    cstate s1 LB1 (e_LB0 en) L1 m1 (wz (e_PL en + -208)) (e_tp en) (e_lo en) (e_B en) -> cframe T1 [] SPc s LBc Lc m s1 LB1 L1 m1 -> SPc <= e_PL en + -104 ->
    (f - EV1 <= f1)%nat -> (rem' + EV1 <= rem)%nat -> cgrow Lc L1 dA dB dBig -> 0 <= rA' -> rA' + dA <= rA -> 0 <= rB' -> rB' + dB <= rB -> 0 <= rBig' -> rBig' + dBig <= rBig ->
    (forall q, In q (map blk_id (e_LBall en)) \/ In q (map fst (e_L en)) -> ~ pem_T en q -> ~ T1 q) -> (forall q, mbio_T (e_K en) q -> ~ T1 q) -> ~ T1 (e_pe en) ->
    pem_com libenv en s1 LB1 L1 f1 m1 off rem' rA' rB' rBig'.
  Proof.
    intros en s LBc Lc f m off rem rA rB rBig T1 SPc s1 LB1 L1 m1 f1 EV1 rem' dA dB dBig rA' rB' rBig'
           (CST & FR0 & LE & INCL0 & INCL & NTL & OWNE & MB & OFF & EVF & FU & ROOM & CG & RA0 & RB0 & RBIG0 & PLB & PLC & SAVED & REST) CST1 FRM1 HSP FU1 REM GR1 DA DA' DB DB' DBIG DBIG' HT HK HE.
    pose proof FRM1 as (CFR1 & KP1 & _). pose proof KP1 as [KB1 KL1].
    assert (NT1 : forall b, In b (e_LBL en) -> ~ T1 (blk_id b)) by (intros b Hb; apply HT; [left; apply in_map; exact (INCL0 _ Hb)| exact (NTL _ Hb)]).
    assert (NE1 : forall b, In b (e_LBall en) -> ~ T1 (blk_id b)).
    { intros b Hb X. apply (HT (blk_id b)); [left; apply in_map; exact Hb| | exact X]. intros [TK|E]; [exact (HK _ TK X)| apply HE; rewrite <- E; exact X]. }
    assert (NEL : forall q nm, In (q, nm) (e_L en) -> ~ T1 q).
    { intros q nm Hq X. apply (HT q); [right; apply in_map_iff; exists (q, nm); split; [reflexivity| exact Hq]| | exact X]. intros [TK|E]; [exact (HK _ TK X)| apply HE; rewrite <- E; exact X]. }
    split; [exact CST1|]. split; [eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X| exact HT]|].
    split; [eapply libenv_cfr; [exact LE| exact CFR1| exact INCL| exact NT1]|]. split; [exact INCL0|]. split; [eapply incl_blocks_keep; [exact INCL| exact KP1| exact NT1]|]. split; [exact NTL|].
    split; [eapply cown_keep; [exact OWNE| intros I; exact (KB1 _ I HE)| intros I; exact (KL1 _ _ I HE)]|].
    split; [eapply mbio_rep_keep; [eapply mbio_rep_cfr; [exact MB| exact CFR1| exact HK]| intros b Hb Tb; exact (KB1 _ Hb (HK _ Tb))| intros p nm Hp Tp; exact (KL1 _ _ Hp (HK _ Tp))]|].
    split; [exact OFF|]. split; [exact EVF|]. split; [lia|].
    split; [eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GR1)| lia| lia| lia]|]. split; [eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ CG GR1)| lia| lia| lia]|].
    split; [lia|]. split; [lia|]. split; [lia|].
    split; [intros b Hb; exact (KB1 _ (PLB _ Hb) (NE1 _ Hb))|]. split; [intros q nm Hq; exact (KL1 _ _ (PLC _ _ Hq) (NEL _ _ Hq))|].
    split; [exact (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 SAVED ltac:(lia))| exact REST].
  Qed.

  (* [comment removed for export] *)
  Lemma com_callE : forall en s LBc Lc f m off rem rA rB rBig s1 LB1 L1 m1 (f1 EV1 rem' : nat) dA dB dBig rA' rB' rBig',
    pem_com libenv en s LBc Lc f m off rem rA rB rBig ->
    cstate s1 LB1 (e_LB0 en) L1 m1 (wz (e_PL en + -208)) (e_tp en) (e_lo en) (e_B en) -> cframe (eq (e_pe en)) [] (e_PL en + -208) s LBc Lc m s1 LB1 L1 m1 ->
    (f - EV1 <= f1)%nat -> (rem' + EV1 <= rem)%nat -> cgrow Lc L1 dA dB dBig -> 0 <= rA' -> rA' + dA <= rA -> 0 <= rB' -> rB' + dB <= rB -> 0 <= rBig' -> rBig' + dBig <= rBig ->
    (forall b, In b LBc -> In b LB1) -> (forall q nm, In (q, nm) Lc -> In (q, nm) L1) -> libenv m1 (e_LBL en) (e_E en) -> (forall q, mbio_T (e_K en) q -> e_pe en <> q) ->
    pem_com libenv en s1 LB1 L1 f1 m1 off rem' rA' rB' rBig'.
  Proof.
    intros en s LBc Lc f m off rem rA rB rBig s1 LB1 L1 m1 f1 EV1 rem' dA dB dBig rA' rB' rBig'
           (CST & FR0 & LE & INCL0 & INCL & NTL & OWNE & MB & OFF & EVF & FU & ROOM & CG & RA0 & RB0 & RBIG0 & PLB & PLC & SAVED & REST) CST1 FRM1 FU1 REM GR1 DA DA' DB DB' DBIG DBIG' KB KL LE1 HK.
    pose proof FRM1 as (CFR1 & _).
    split; [exact CST1|]. split; [eapply cframe_call; [exact FR0| exact FRM1| lia| intros a X; exact X| intros q _ NT X; apply NT; right; exact (eq_sym X)]|].
    split; [exact LE1|]. split; [exact INCL0|]. split; [intros b Hb; exact (KB _ (INCL _ Hb))|]. split; [exact NTL|].
    split; [destruct OWNE as [O1 O2]; split; [exact (KB _ O1)| exact (KL _ _ O2)]|].
    split; [eapply mbio_rep_keep; [eapply mbio_rep_cfr; [exact MB| exact CFR1| exact HK]| intros b Hb _; exact (KB _ Hb)| intros p nm Hp _; exact (KL _ _ Hp)]|].
    split; [exact OFF|]. split; [exact EVF|]. split; [lia|].
    split; [eapply croom_weaken; [exact (croom_grow _ _ _ _ _ _ _ _ ROOM GR1)| lia| lia| lia]|]. split; [eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ CG GR1)| lia| lia| lia]|].
    split; [lia|]. split; [lia|]. split; [lia|].
    split; [intros b Hb; exact (KB _ (PLB _ Hb))|]. split; [intros q nm Hq; exact (KL _ _ (PLC _ _ Hq))|].
    split; [exact (cfr_cells_stack _ _ _ _ _ _ _ _ CFR1 SAVED ltac:(lia))| exact REST].
  Qed.

  Lemma djf_forall : forall (W : list (Z * Z)) a n, Forall (fun iv => a + n <= fst iv \/ snd iv <= a) W -> disjoint_from W a n.
  Proof. intros W a n HW. induction HW as [|[x y] W HX HW IH]; cbn; [exact I|]. cbn in HX. split; [exact HX| exact IH]. Qed.

  (* [comment removed for export] *)
  Lemma com_seg : forall en s LBc Lc f m off rem rA rB rBig Wseg m' (EX : bptr -> Prop),
    pem_com libenv en s LBc Lc f m off rem rA rB rBig -> munch Wseg m m' -> wmono usegs m m' -> mem_inv usegs m' -> stk usegs m' (e_lo en) (e_PL en + -208) ->
    Forall (wfree LBc (e_lo en) (e_PL en + 32) EX) Wseg -> (forall b, In b (e_LBall en) -> EX (blk_id b)) -> disjoint_from Wseg (e_PL en + -104) 104 ->
    pem_com libenv en s LBc Lc f m' off rem rA rB rBig.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros en s LBc Lc f m off rem rA rB rBig Wseg m' EX COM MU WM MI' ST' HW HX DJ.
    pose proof COM as (CST & FR0 & LE & INCL0 & INCL & NTL & OWNE & MB & OFF & EVF & FU & ROOM & CG & RA0 & RB0 & RBIG0 & PLB & PLC & SAVED & SLO & PLBB & FLR & AL16 & EPE & EK).
    pose proof (cstate_B _ _ _ _ _ _ _ _ _ CST) as (_ & LO & GLO). pose proof CST as (HP & _). unfold BPUTS_STACK, WRITE_STACK, GROW_STACK in SLO. unfold GLOBALS_TOP in GLO.
    assert (WSP : 48 + 32 + (64 + (96 + CCR_STACK + CSM_STACK + CSF_STACK)) = 25200) by (unfold CCR_STACK, CCF_STACK, CSM_STACK, CSF_STACK, CF_STACK, CM_STACK, RMALLOC_STACK, RFREE_STACK; clear; lia).
    rewrite WSP in SLO. clear WSP. assert (SPR : 0 <= e_PL en < 2 ^ 64) by (pose proof (bv_unsigned_in_range _ (e_sp en)) as X; change (bv_modulus 64) with (2^64) in X; exact X).
    assert (HXm : forall q, In q (map blk_id (e_LBall en)) -> EX q) by (intros q Hq; apply in_map_iff in Hq; destruct Hq as (b & <- & Hb); exact (HX _ Hb)).
    split. { eapply (cstate_seg Wseg _ _ _ _ m m' _ _ _ (e_lo en) (e_B en) (e_PL en + 32)); [exact CST| exact MU| exact WM| exact MI'| | lia| exact PLBB| | rewrite unsigned_lit by lia; exact ST'| rewrite unsigned_lit by lia; lia].
      - eapply Forall_impl; [| exact HW]. cbv beta. intros [x y] [[H1 H2]|(b & Hb & _ & H1 & H2)]; [apply cwin_stack; cbn in H1, H2; lia| eapply cwin_block; [exact Hb| exact H1| exact H2]].
      - apply djf_forall. eapply Forall_impl; [| exact HW]. cbv beta. intros [x y] [[H1 H2]|(b & Hb & _ & H1 & H2)]; cbn [fst snd] in *; [unfold LX_FLAGS; lia|].
        pose proof (RHEAP_block_range_proof _ _ _ b HP Hb) as (_ & _ & _ & RC & RR). unfold LX_FLAGS, ceil_window in *. lia. }
    split. { eapply cframe_seg; [exact FR0| exact MU| exact WM| exact HP| lia|]. eapply Forall_impl; [| exact HW]. cbv beta.
             intros [x y] [[H1 H2]|(b & Hb & NX & H1 & H2)]; [apply cseg_ok_stack; cbn in H1, H2; lia| eapply cseg_ok_block; [exact Hb| | exact H1| exact H2]].
             intros b0 Hb0 _ E. apply NX. rewrite <- E. apply HXm. apply in_map. exact Hb0. }
    split; [eapply libenv_munch; [exact LE| exact MU| exact WM| exact CST| exact INCL| exact HW| intros b Hb; exact (HX _ (INCL0 _ Hb))]|].
    split; [exact INCL0|]. split; [exact INCL|]. split; [exact NTL|]. split; [exact OWNE|].
    split; [eapply mbio_rep_agree; [exact MB| eapply mbio_fp_munch; [exact CST| exact MU| exact WM| exact HW| intros q Tq; exact (HXm _ (EK _ Tq))]]|].
    split; [exact OFF|]. split; [exact EVF|]. split; [exact FU|]. split; [exact ROOM|]. split; [exact CG|]. split; [exact RA0|]. split; [exact RB0|]. split; [exact RBIG0|].
    split; [exact PLB|]. split; [exact PLC|]. split; [eapply rw_cells_transport; [exact SAVED| exact MU| exact WM| exact DJ]|]. split; [exact SLO|]. split; [exact PLBB|]. split; [exact FLR|]. split; [exact AL16|]. split; [exact EPE| exact EK].
  Qed.

  (* [comment removed for export] *)
  Lemma mbx_call : forall (m m1 : mem) T1 SP s LBc Lc s1 LB1 L1 K BI BM blw meth len max off,
    mbio_repx m LBc Lc K BI BM blw meth len max off -> cframe T1 [] SP s LBc Lc m s1 LB1 L1 m1 -> (forall q, mbio_T K q -> ~ T1 q) -> mbio_repx m1 LB1 L1 K BI BM blw meth len max off.
  Proof.
    intros m m1 T1 SP s LBc Lc s1 LB1 L1 K BI BM blw meth len max off MB (CFR1 & [KB1 KL1] & _) HK.
    eapply mbio_repx_keep; [eapply mbio_repx_cfr; [exact MB| exact CFR1| exact HK]| intros b Hb Tb; exact (KB1 _ Hb (HK _ Tb))| intros p nm Hp Tp; exact (KL1 _ _ Hp (HK _ Tp))].
  Qed.
  Lemma mbx_seg : forall Wseg (m m' : mem) s LBc LB0 Lc sp tp lo hi B K EX BI BM blw meth len max off,
    mbio_repx m LBc Lc K BI BM blw meth len max off -> cstate s LBc LB0 Lc m sp tp lo B -> munch Wseg m m' -> wmono usegs m m' -> Forall (wfree LBc lo hi EX) Wseg ->
    (forall q, mbio_T K q -> EX q) -> mbio_repx m' LBc Lc K BI BM blw meth len max off.
  Proof. intros. eapply mbio_repx_agree; [eassumption| eapply mbio_fp_munch; eassumption]. Qed.
  Lemma own_call : forall (m m1 : mem) T1 SP s (LBc LB1 : list block) (Lc L1 : @clist bptr) s1 p A n nm,
    cown LBc Lc p A n nm -> cframe T1 [] SP s LBc Lc m s1 LB1 L1 m1 -> ~ T1 p -> cown LB1 L1 p A n nm.
  Proof. intros m m1 T1 SP s LBc LB1 Lc L1 s1 p A n nm O (_ & [KB1 KL1] & _) NT. eapply cown_keep; [exact O| intros I; exact (KB1 _ I NT)| intros I; exact (KL1 _ _ I NT)]. Qed.
  Lemma err_call : forall en strs (m m1 : mem) T1 SP s LBc Lc s1 LB1 L1,
    pem_err errst_at_rest errst_live en strs m -> cframe T1 [] SP s LBc Lc m s1 LB1 L1 m1 -> In (e_pe en, e_E en, 904) LBc -> ~ T1 (e_pe en) ->
    incl_blocks strs LBc -> (forall b, In b strs -> ~ T1 (blk_id b)) -> pem_err errst_at_rest errst_live en strs m1 /\ incl_blocks strs LB1.
  Proof.
    intros en strs m m1 T1 SP s LBc Lc s1 LB1 L1 PE (CFR1 & [KB1 _] & _) INE NTE INCL NT.
    split; [eapply pem_err_cfr; [exact PE| exact CFR1| exact INE| exact NTE| exact INCL| exact NT]| intros b Hb; exact (KB1 _ (INCL _ Hb) (NT _ Hb))].
  Qed.

  Lemma rw_cells_CB0 : forall (m : mem) A, 0 <= A -> A <= 2 ^ 64 -> rw_cells usegs m A [CB 0%nat []].
  Proof. intros m A H1 H2. split; [split; [cbn; tauto| split; [exact H1| split; [cbn; lia| intros i Hi; cbn in Hi; lia]]]| split; [exact H1| split; [cbn; lia| intros i Hi; cbn in Hi; lia]]]. Qed.
  Lemma nd_drop : forall (l1 l2 : list bptr) x, List.NoDup (l1 ++ x :: l2) -> List.NoDup (l1 ++ l2).
  Proof.
    intros l1 l2 x ND. induction l1 as [|y l1 IH]; cbn [app] in *; [inversion ND; assumption|].
    inversion ND as [|y' l' NI ND']; subst. constructor; [| exact (IH ND')]. intros X. apply NI. apply in_app_iff in X. apply in_or_app. destruct X as [X|X]; [left; exact X| right; right; exact X].
  Qed.
  Lemma out4_split : forall (m : mem) PL a b c d, rw_cells usegs m PL [C8 a; C8 b; C8 c; C8 d] ->
    rw_cells usegs m PL [C8 a] /\ rw_cells usegs m (PL + 8) [C8 b] /\ rw_cells usegs m (PL + 16) [C8 c] /\ rw_cells usegs m (PL + 24) [C8 d].
  Proof.
    intros m PL a b c d H.
    destruct (proj1 (rw_cells_app usegs m PL [C8 a] [C8 b; C8 c; C8 d]) H) as [H1 H2]. destruct (proj1 (rw_cells_app usegs m _ [C8 b] [C8 c; C8 d]) H2) as [H3 H4].
    destruct (proj1 (rw_cells_app usegs m _ [C8 c] [C8 d]) H4) as [H5 H6]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in *.
    rewrite <- ?Z.add_assoc in *. cbn [Z.add Pos.add Pos.succ] in *. auto.
  Qed.
  (* [comment removed for export] *)
  Lemma strs_inL_keep : forall (L L' : @clist bptr) (strs : list block) (P : bptr -> Prop),
    strs_inL L strs -> (forall q nm, In (q, nm) L -> ~ P q -> In (q, nm) L') -> (forall b, In b strs -> ~ P (blk_id b)) -> strs_inL L' strs.
  Proof.
    unfold strs_inL. intros L L' strs P SL KL NP. apply Forall_forall. intros b Hb. pose proof (proj1 (Forall_forall _ _) SL b Hb) as [H1 H2].
    split; [| exact H2]. apply KL; [exact H1| exact (NP b Hb)].
  Qed.
  (* [comment removed for export] *)
  Lemma strs_call : forall strs T1 SP s (LBc LB1 : list block) (Lc L1 : @clist bptr) (m m1 : mem) s1,
    strs_inL Lc strs -> cframe T1 [] SP s LBc Lc m s1 LB1 L1 m1 -> (forall b, In b strs -> ~ T1 (blk_id b)) -> strs_inL L1 strs.
  Proof. intros strs T1 SP s LBc LB1 Lc L1 m m1 s1 SL (_ & [_ KL1] & _) NT. eapply strs_inL_keep; [exact SL| intros q nm Hq NX; exact (KL1 _ _ Hq NX)| exact NT]. Qed.
  Lemma mbio_blocks_len : forall K, (length (mbio_blocks K) <= 5)%nat.
  Proof. intros K. unfold mbio_blocks. rewrite length_app. destruct (k_d K); cbn; lia. Qed.

  (* [comment removed for export] *)
End W3.
