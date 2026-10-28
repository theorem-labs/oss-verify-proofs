(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude DecodeC Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_T_ekit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy.
     From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_M_free Fz_M_secure Fz_W1_defs Fz_W3_iface Fz_W2_rep Fz_W2_puts Fz_W3_defs Fz_W3_lems. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_W7_perm. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_W7_defs Fz_W7_x.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation wz := (Z_to_bv 64) (only parsing).
Ltac hide H := lazymatch type of H with ?X => change X with (hideP X) in H end.

(* [comment removed for export] *)
Definition olist (ob : option block) : list block := match ob with Some b => [b] | None => [] end.
Definition oval (ob : option block) : Z := match ob with Some b => blk_addr b | None => 0 end.
Definition oT (ob : option block) : bptr -> Prop := fun q => exists b, ob = Some b /\ q = blk_id b.

Lemma bents_cons : forall b bs, bents (b :: bs) = (blk_id b, blk_size b) :: bents bs.
Proof. reflexivity. Qed.
Lemma nodup_app_disj : forall (l1 l2 : list bptr) q, List.NoDup (l1 ++ l2) -> In q l2 -> ~ In q l1.
Proof.
  induction l1 as [|a l1 IH]; intros l2 q ND H2 H1; [exact H1|].
  cbn [app] in ND. inversion ND as [|a' l' NI ND']; subst.
  destruct H1 as [<-|H1]; [apply NI; apply in_app_iff; right; exact H2| exact (IH l2 q ND' H2 H1)].
Qed.

Section W7. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cfree_opt_stmt (ENTRY STK : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (ob : option block) (lo B : Z),
  (1 <= f)%nat -> cstate s LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - STK -> a0 = wz (oval ob) ->
  match ob with None => True | Some b => In b LBall /\ In (blk_id b, blk_size b) L end ->
  climpl f L s (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz ENTRY) fc None m (seg_rom usegs))
    (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LBall LB L f m lo B (oT ob) [] 1 0 0 0
       (fun _ LBall' L' _ => match ob with
                             | None => LBall' = LBall /\ L' = L
                             | Some b => LBall' = lb_remove (blk_id b) LBall /\ exists i, nth_error L i = Some (blk_id b, blk_size b) /\ L' = cremove i L
                             end)).

Lemma cfree_opt_plain : crypto_free_stmt -> cfree_opt_stmt FZ_CRYPTO_FREE CF_STACK.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f ob lo B Hf CST SLO -> HOB.
  destruct ob as [b|]; cbn [oval] in *.
  - destruct b as [[p A] n]. cbn [blk_id blk_addr blk_size fst snd] in *. destruct HOB as [INB INL].
    eapply climpl_mono.
    { eapply CF with (p := p) (n := n) (nm := n); [exact Hf| split; [exact INB| exact INL]| exact CST| exact SLO| reflexivity]. }
    cbv beta. intros f' L' s' ms' (v & m' & LBall' & CRET & FU & CG & CST' & CFR & R). exists v, m', LBall'. split; [exact CRET|]. split; [exact FU|].
    split; [unfold cgrow, wA, wB, wBig, TIER_A_MAX in *; destruct (Z.leb_spec n 236); destruct (Z.ltb_spec 236 n); lia|]. split; [exact CST'|].
    split; [eapply cframe_weakT; [exact CFR| intros q E; exists (p, A, n); split; [reflexivity| exact (eq_sym E)]]| exact R].
  - pose proof CST as (HP & _ & (errv & _ & SPB & ST & LO & _ & MI & _) & LXS & _ & _ & GLO). unfold CF_STACK, RFREE_STACK, GLOBALS_TOP in *.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    cprefix. tcallr crypto_free_null. all: try first [eassumption | reflexivity | lia].
    chere. apply climpl_done.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into mz end.
    lazymatch goal with H : stk usegs mz lo _ |- _ => rename H into STz end. lazymatch goal with H : mem_inv usegs mz |- _ => rename H into MIz end.
    do 2 eexists. exists LBall. split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|]. split; [unfold cgrow; lia|].
    split. { eapply (cstate_seg _ _ _ _ _ m mz _ sp _ lo B (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MIz| | lia| exact SPB| | exact STz| exact SPB].
      - constructor; [apply cwin_stack; lia| constructor]. - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
    split; [| auto]. eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor].
Qed.

Lemma cfree_opt_secure : crypto_secure_free_stmt -> cfree_opt_stmt FZ_SECURE_FREE CSF_STACK.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LBall LB L f ob lo B Hf CST SLO -> HOB.
  destruct ob as [b|]; cbn [oval] in *.
  - destruct b as [[p A] n]. cbn [blk_id blk_addr blk_size fst snd] in *. destruct HOB as [INB INL].
    eapply climpl_mono.
    { eapply CF with (p := p) (n := n) (nm := n); [exact Hf| split; [exact INB| exact INL]| exact CST| exact SLO| reflexivity]. }
    cbv beta. intros f' L' s' ms' (v & m' & LBall' & CRET & FU & CG & CST' & CFR & R). exists v, m', LBall'. split; [exact CRET|]. split; [exact FU|].
    split; [unfold cgrow, wA, wB, wBig, TIER_A_MAX in *; destruct (Z.leb_spec n 236); destruct (Z.ltb_spec 236 n); lia|]. split; [exact CST'|].
    split; [eapply cframe_weakT; [exact CFR| intros q E; exists (p, A, n); split; [reflexivity| exact (eq_sym E)]]| exact R].
  - pose proof CST as (HP & _ & (errv & _ & SPB & ST & LO & _ & MI & _) & LXS & _ & _ & GLO). unfold CSF_STACK, CF_STACK, RFREE_STACK, GLOBALS_TOP in *.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    cprefix. tcallr crypto_secure_free_null. all: try first [eassumption | reflexivity | lia].
    chere. apply climpl_done.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => rename mx into mz end.
    lazymatch goal with H : stk usegs mz lo _ |- _ => rename H into STz end. lazymatch goal with H : mem_inv usegs mz |- _ => rename H into MIz end.
    do 2 eexists. exists LBall. split; [unfold cret; do 14 eexists; reflexivity|]. split; [lia|]. split; [unfold cgrow; lia|].
    split. { eapply (cstate_seg _ _ _ _ _ m mz _ sp _ lo B (bv_unsigned sp)); [exact CST| exact MU| exact WM| exact MIz| | lia| exact SPB| | exact STz| exact SPB].
      - constructor; [apply cwin_stack; lia| constructor]. - cbn [disjoint_from]. unfold LX_FLAGS. lia. }
    split; [| auto]. eapply cframe_seg; [apply cframe_refl| exact MU| exact WM| exact HP| lia|]. constructor; [apply cseg_ok_stack; lia| constructor].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Client.
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
  Local Notation w7_comI := (w7_com libenv).

  (* [comment removed for export] *)
  Definition f7_inv (en : w7e) (st : PState) (LBc : list block) (Lc : @clist bptr) (mc : mem)
      (K : mbk) (BI len max off top bot : Z) (strs nws : list block) : Prop :=
       w7_comI en st LBc Lc mc (mbk_ents K max ++ bents strs ++ bents nws)
    /\ mbio_rep mc LBc Lc K BI M_MEM len max off
    /\ errst_live (w_E en) top bot strs mc /\ (length strs <= 2)%nat
    /\ Forall (fun b => In b LBc) strs /\ strs_inL Lc strs
    /\ Forall (fun b => In b LBc /\ In (blk_id b, blk_size b) Lc) nws
    /\ (forall q, In q (map blk_id (w_LBall en)) \/ In q (map fst (w_L en)) -> ~ mbio_T K q) /\ (forall b, In b (w_LBL en) -> ~ mbio_T K (blk_id b))
    /\ (forall b, In b (strs ++ nws) -> ~ mbio_T K (blk_id b)) /\ List.NoDup (map blk_id (strs ++ nws))
    /\ (forall b, In b (strs ++ nws) -> ~ (In (blk_id b) (map blk_id (w_LBall en)) \/ In (blk_id b) (map fst (w_L en))))
    /\ (forall b, In b (w_LBL en) -> ~ In (blk_id b) (map blk_id (strs ++ nws))).

  Lemma nodup_mid : forall (l1 : list bptr) x l2, List.NoDup (l1 ++ x :: l2) -> ~ In x (l1 ++ l2) /\ List.NoDup (l1 ++ l2).
  Proof.
    intros l1 x l2 ND. split; [| exact (NoDup_remove_1 _ _ _ ND)].
    intros X. apply in_app_iff in X. pose proof (NoDup_remove_2 _ _ _ ND) as NI. apply NI. apply in_app_iff. exact X.
  Qed.

  (* [comment removed for export] *)
  Lemma f7_step : forall en st LBc Lc mc K BI len max off top bot strs pre post (ob : option block) st1 LB1 L1 m1,
    f7_inv en st LBc Lc mc K BI len max off top bot strs (pre ++ olist ob ++ post) ->
    cstate st1 LB1 (w_LB en) L1 m1 (wz (w_SP en + -64)) (w_tp en) (w_lo en) (w_B en) ->
    cframe (oT ob) [] (w_SP en + -64) st LBc Lc mc st1 LB1 L1 m1 ->
    match ob with None => LB1 = LBc /\ L1 = Lc
                | Some b => LB1 = lb_remove (blk_id b) LBc /\ exists i, nth_error Lc i = Some (blk_id b, blk_size b) /\ L1 = cremove i Lc end ->
    f7_inv en st1 LB1 L1 m1 K BI len max off top bot strs (pre ++ post).
  Proof.
    intros en st LBc Lc mc K BI len max off top bot strs pre post ob st1 LB1 L1 m1
           (COM & MB & LIVE & LEN2 & SIN & SL & NWS & KFR & KL & KS & NDSN & SFR & SLBL) CST1 FRM1 R.
    pose proof COM as (CST & FR0 & LE & INCL0 & INCL & NPL & INE & INL & PERM & SAVED & SLO & SPB & B63 & AL16 & EPE & ROOM & PAY & DLEN & NDE & REL).
    pose proof FRM1 as (CFR1 & [KB1 KL1] & _).
    destruct ob as [b|]; cbn [olist] in *.
    - destruct R as (-> & i & HN & ->). change ([b] ++ post) with (b :: post) in *.
      rewrite !map_app in NDSN. cbn [map] in NDSN. rewrite app_assoc in NDSN.
      pose proof (nodup_mid _ _ _ NDSN) as [NIB NDSN']. rewrite <- app_assoc, <- !map_app in NIB. rewrite <- app_assoc, <- !map_app in NDSN'.
      assert (SUB : forall b', In b' (strs ++ pre ++ post) -> In b' (strs ++ pre ++ b :: post)) by (intros b' H; rewrite !in_app_iff in H |- *; cbn [In]; tauto).
      assert (SUB2 : forall b', In b' (pre ++ post) -> In b' (pre ++ b :: post)) by (intros b' H; rewrite !in_app_iff in H |- *; cbn [In]; tauto).
      assert (INb : In b (strs ++ pre ++ b :: post)) by (rewrite !in_app_iff; cbn [In]; tauto).
      assert (NBE : blk_id b <> w_pe en) by (intros E; apply (SFR b INb); left; rewrite E; exact (w_pe_in _ EPE)).
      assert (NBK : forall q, mbio_T K q -> q <> blk_id b) by (intros q Tq E; subst q; exact (KS b INb Tq)).
      assert (NBS : forall b', In b' (strs ++ pre ++ post) -> blk_id b' <> blk_id b) by (intros b' Hb' E; apply NIB; rewrite <- E; apply in_map; exact Hb').
      assert (KB : forall b', In b' LBc -> blk_id b' <> blk_id b -> In b' (lb_remove (blk_id b) LBc)) by (intros b' Hb' NE; apply lb_remove_In; split; [exact Hb'| exact NE]).
      assert (KLc : forall q nm, In (q, nm) Lc -> q <> blk_id b -> In (q, nm) (cremove i Lc)) by (intros q nm Hq NE; eapply cremove_keep; [exact HN| exact Hq| exact NE]).
      split.
      { eapply (com7_call libenv); [exact COM| exact CST1| exact FRM1| | | | apply KB; [exact INE| cbn; intros E; exact (NBE (eq_sym E))]| apply KLc; [exact INL| intros E; exact (NBE (eq_sym E))]| |].
        + intros q Hq _ (b' & E & ->). inversion E; subst b'. exact (SFR b INb Hq).
        + intros b' Hb' (b'' & E & X). inversion E; subst b''. apply (SLBL _ Hb'). rewrite X. apply in_map. exact INb.
        + eapply (libenv_cfr libenv libenv_fp libenv_agree libenv_fp_where); [exact LE| exact CFR1| exact INCL|].
          intros b' Hb' (b'' & E & X). inversion E; subst b''. apply (SLBL _ Hb'). rewrite X. apply in_map. exact INb.
        + intros b' Hb'. apply KB; [exact (INCL _ Hb')|]. intros X. apply (SLBL _ Hb'). rewrite X. apply in_map. exact INb.
        + rewrite !bents_app, bents_cons in PERM. rewrite bents_app.
          eapply perm_trans; [apply (perm_remove_one Lc i (blk_id b, blk_size b) (mbk_ents K max ++ bents strs ++ bents pre) (bents post) (w_L en)); [| exact HN]
                             | rewrite <- !app_assoc; apply Permutation_refl].
          eapply perm_trans; [exact PERM|]. rewrite <- !app_assoc. cbn [app]. apply Permutation_refl. }
      split; [eapply mbio_rep_keep; [eapply mbio_rep_cfr; [exact MB| exact CFR1| intros q Tq (b' & E & X); inversion E; subst b'; exact (NBK _ Tq X)]
              | intros b' Hb' Tb'; apply KB; [exact Hb'| exact (NBK _ Tb')]| intros p nm Hp Tp; apply KLc; [exact Hp| exact (NBK _ Tp)]]|].
      split. { eapply errst_live_agree; [exact LIVE|]. eapply agree_on_mono; [exact CFR1|]. cbv beta. intros a Ha. right; left.
        destruct (errst_fp_where _ _ _ Ha) as [Ra|(b' & Hb' & Rb')].
        - exists (w_pe en, w_E en, 904). split; [exact INE|]. split; [intros (b'' & E & X); inversion E; subst b''; exact (NBE (eq_sym X))| unfold blk_addr, blk_size; cbn [fst snd]; exact Ra].
        - exists b'. split; [exact (proj1 (Forall_forall _ _) SIN b' Hb')|]. split; [| exact Rb']. intros (b'' & E & X); inversion E; subst b''.
          exact (NBS b' ltac:(apply in_or_app; left; exact Hb') X). }
      split; [exact LEN2|].
      split; [apply Forall_forall; intros b' Hb'; apply KB; [exact (proj1 (Forall_forall _ _) SIN b' Hb')| exact (NBS b' ltac:(apply in_or_app; left; exact Hb'))]|].
      split; [eapply strs_inL_keep; [exact SL| intros q nm Hq NE; exact (KLc q nm Hq NE)| intros b' Hb'; exact (NBS b' ltac:(apply in_or_app; left; exact Hb'))]|].
      split. { apply Forall_forall. intros b' Hb'. pose proof (proj1 (Forall_forall _ _) NWS b' (SUB2 _ Hb')) as [H1 H2].
               pose proof (NBS b' ltac:(apply in_or_app; right; exact Hb')) as NE. split; [exact (KB _ H1 NE)| exact (KLc _ _ H2 NE)]. }
      split; [exact KFR|]. split; [exact KL|].
      split; [intros b' Hb'; exact (KS _ (SUB _ Hb'))|].
      split; [exact NDSN'|].
      split; [intros b' Hb'; exact (SFR _ (SUB _ Hb'))|].
      intros b' Hb' X. apply (SLBL _ Hb'). apply in_map_iff in X. destruct X as (b'' & <- & Hb''). apply in_map. exact (SUB _ Hb'').
    - destruct R as [-> ->]. cbn [app] in COM, NWS, KS, NDSN, SFR, SLBL |- *.
      assert (NT : forall q, ~ oT None q) by (intros q (b & E & _); discriminate).
      split.
      { eapply (com7_call libenv); [exact COM| exact CST1| exact FRM1| intros q _ _; apply NT| intros b _; apply NT| | exact INE| exact INL| exact INCL| exact PERM].
        eapply (libenv_cfr libenv libenv_fp libenv_agree libenv_fp_where); [exact LE| exact CFR1| exact INCL| intros b _; apply NT]. }
      split; [eapply mbio_rep_cfr; [exact MB| exact CFR1| intros q _; apply NT]|].
      split. { eapply errst_live_agree; [exact LIVE|]. eapply agree_on_mono; [exact CFR1|]. cbv beta. intros a Ha. right; left.
        destruct (errst_fp_where _ _ _ Ha) as [Ra|(b' & Hb' & Rb')].
        - exists (w_pe en, w_E en, 904). split; [exact INE|]. split; [apply NT| unfold blk_addr, blk_size; cbn [fst snd]; exact Ra].
        - exists b'. split; [exact (proj1 (Forall_forall _ _) SIN b' Hb')|]. split; [apply NT| exact Rb']. }
      split; [exact LEN2|]. split; [exact SIN|]. split; [exact SL|]. split; [exact NWS|]. split; [exact KFR|]. split; [exact KL|]. split; [exact KS|]. split; [exact NDSN|]. split; [exact SFR| exact SLBL].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition farm_pre (en : w7e) st LBc Lc f mc K BI len max off top bot strs (od oh on : option block) (ol : word) : Prop :=
       f7_inv en st LBc Lc mc K BI len max off top bot strs (olist od ++ olist oh ++ olist on) /\ (8 + length strs <= f)%nat
    /\ rw_cells usegs mc (w_SP en + -64) [C8 ol; C8 (wz (oval od)); C8 (wz (oval oh)); C8 (wz (oval on))].

  Definition FARM_stmt (pc : Z) : Prop :=
    forall (en : w7e) st LBc Lc f mc (K : mbk) (BI len max off top bot : Z) (strs : list block) (od oh on : option block)
           (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1v s2v t3 t4 t5 t6 ol : word),
    farm_pre en st LBc Lc f mc K BI len max off top bot strs od oh on ol ->
    climpl f Lc st (MS (mkR xra (wz (w_SP en + -64)) (w_gp en) (w_tp en) t0 t1 t2 (wz BI) s1v (wz (oval on)) a1 a2 a3 a4 a5 a6 a7
                       s2v (w_s3 en) (w_s4 en) (w_s5 en) (w_s6 en) (w_s7 en) (w_s8 en) (w_s9 en) (w_s10 en) (w_s11 en) t3 t4 t5 t6)
                 (w_F en) (wz pc) (w_fc en) None mc (seg_rom usegs))
      (w7_post libenv errst_at_rest en).

  (* [comment removed for export] *)
  Lemma f7_ob : forall en st LBc Lc mc K BI len max off top bot strs pre post ob,
    f7_inv en st LBc Lc mc K BI len max off top bot strs (pre ++ olist ob ++ post) ->
    match ob with None => True | Some b => In b LBc /\ In (blk_id b, blk_size b) Lc end.
  Proof.
    intros en st LBc Lc mc K BI len max off top bot strs pre post ob (_ & _ & _ & _ & _ & _ & NWS & _). destruct ob as [b|]; [| exact I].
    exact (proj1 (Forall_forall _ _) NWS b ltac:(apply in_or_app; right; apply in_or_app; left; left; reflexivity)).
  Qed.

  Ltac f7_facts INV :=
    lazymatch type of INV with f7_inv ?en ?st ?LBc ?Lc ?mc _ _ _ _ _ _ _ _ _ =>
      let COM := fresh "COM" in let CST := fresh "CST" in
      pose proof (proj1 INV) as COM;
      pose proof (proj1 COM) as CST
    end.

  Theorem FP7_proof : crypto_free_stmt -> X7_stmt libenv errst_at_rest errst_live -> FARM_stmt 0xe1bdc.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros CF X7P en st LBc Lc f mc K BI len max off top bot strs od oh on xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1v s2v t3 t4 t5 t6 ol (INV & FU & LOC).
    pose proof (cfree_opt_plain CF) as CFO. unfold cfree_opt_stmt in CFO. unfold X7_stmt, J_X7 in X7P.
    pose proof (proj1 INV) as COM. pose proof COM as (CST & FR0 & LE & INCL0 & INCL & NPL & INE & INL & PERM & SAVED & SLO & SPB & B63 & AL16 & EPE & ROOM & PAY & DLEN & NDE & REL).
    pose proof CST as (HP & CO & (errv & AV & SPB' & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold LX_FUZZ_STACK, GLOBALS_TOP in *.
    pose proof (bv_unsigned_in_range _ (w_sp en)) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold w_SP in *.
    rewrite unsigned_lit in ST by (clear - SPR SLO LO GLO; lia).
    pose proof (munch_refl ([] : list (Z * Z)) mc) as MU. pose proof (wmono_refl usegs mc) as WM.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. ths. ths. chere.
    eapply climpl_seq.
    { eapply CFO with (ob := on) (lo := w_lo en) (B := w_B en); [clear - FU; lia| exact CST| rewrite unsigned_lit by lia; unfold CF_STACK, RFREE_STACK; clear - SLO; lia| reflexivity
        | exact (f7_ob _ _ _ _ _ _ _ _ _ _ _ _ _ (olist od ++ olist oh) [] on ltac:(rewrite app_nil_r, <- app_assoc; exact INV))]. }
    cbv beta. intros f1 L1 st1 ms1 (v1 & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & R1).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM1 by lia.
    pose proof (f7_step _ _ _ _ _ _ _ _ _ _ _ _ _ (olist od ++ olist oh) [] on _ _ _ _ ltac:(rewrite app_nil_r, <- app_assoc; exact INV) CST1 FRM1 R1) as INV1.
    rewrite app_nil_r in INV1.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ (proj1 FRM1) LOC ltac:(clear; lia)) as LOC1.
    pose proof (proj1 INV1) as COM1. pose proof (proj1 COM1) as CST1'. pose proof CST1' as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _). unfold w_SP in ST1. rewrite unsigned_lit in ST1 by lia.
    clear MU WM HP MI ST ERR LATCH LXS CIMG FRM1 CST CST1 R1 INV COM.
    pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. ths. chere.
    eapply climpl_seq.
    { eapply CFO with (ob := oh) (lo := w_lo en) (B := w_B en); [clear - FU FU1; lia| exact CST1'| rewrite unsigned_lit by lia; unfold CF_STACK, RFREE_STACK; clear - SLO; lia| reflexivity
        | exact (f7_ob _ _ _ _ _ _ _ _ _ _ _ _ _ (olist od) [] oh ltac:(rewrite app_nil_r; exact INV1))]. }
    cbv beta. intros f2 L2 st2 ms2 (v2 & m2 & LB2 & RET & FU2 & GR2 & CST2 & FRM2 & R2).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM2 by lia.
    pose proof (f7_step _ _ _ _ _ _ _ _ _ _ _ _ _ (olist od) [] oh _ _ _ _ ltac:(rewrite app_nil_r; exact INV1) CST2 FRM2 R2) as INV2.
    rewrite app_nil_r in INV2.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ (proj1 FRM2) LOC1 ltac:(clear; lia)) as LOC2.
    pose proof (proj1 INV2) as COM2. pose proof (proj1 COM2) as CST2'. pose proof CST2' as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _). unfold w_SP in ST2. rewrite unsigned_lit in ST2 by lia.
    clear MU WM HP1 MI1 ST1 FRM2 CST1' CST2 R2 INV1 COM1 LOC1.
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. ths. chere.
    eapply climpl_seq.
    { eapply CFO with (ob := od) (lo := w_lo en) (B := w_B en); [clear - FU FU1 FU2; lia| exact CST2'| rewrite unsigned_lit by lia; unfold CF_STACK, RFREE_STACK; clear - SLO; lia| reflexivity
        | exact (f7_ob _ _ _ _ _ _ _ _ _ _ _ _ _ [] [] od ltac:(cbn [app]; rewrite app_nil_r; exact INV2))]. }
    cbv beta. intros f3 L3 st3 ms3 (v3 & m3 & LB3 & RET & FU3 & GR3 & CST3 & FRM3 & R3).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM3 by lia.
    pose proof (f7_step _ _ _ _ _ _ _ _ _ _ _ _ _ [] [] od _ _ _ _ ltac:(cbn [app]; rewrite app_nil_r; exact INV2) CST3 FRM3 R3) as INV3.
    cbn [app] in INV3.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ (proj1 FRM3) LOC2 ltac:(clear; lia)) as LOC3.
    destruct INV3 as (COM3 & MB3 & LIVE3 & LEN3 & SIN3 & SL3 & NWS3 & KFR3 & KL3 & KS3 & NDSN3 & SFR3 & SLBL3). rewrite app_nil_r in KS3, NDSN3, SFR3, SLBL3.
    pose proof (proj1 COM3) as CST3'. pose proof CST3' as (HP3 & _ & (errv3 & _ & _ & ST3 & _ & _ & MI3 & _) & _). unfold w_SP in ST3. rewrite unsigned_lit in ST3 by lia.
    clear MU WM HP2 MI2 ST2 FRM3 CST2' CST3 R3 INV2 COM2 LOC2.
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    (* [comment removed for export] *)
    cprefix. ths. chere.
    eapply (X7P en st3 LB3 L3 f3 m3 K BI len max off top bot strs); [| clear - FU FU1 FU2 FU3; lia| exact MB3| exact KFR3| exact KL3| exact KS3| exact LIVE3| exact LEN3| exact SIN3| exact SL3| exact NDSN3| exact SFR3| exact SLBL3| exact LOC3].
    lazymatch type of COM3 with w7_com _ _ _ _ _ _ ?add => replace add with (mbk_ents K max ++ bents strs) in COM3 by (cbn [bents map]; rewrite app_nil_r; reflexivity) end. exact COM3.
  Qed.
  Theorem FS7_proof : crypto_secure_free_stmt -> X7_stmt libenv errst_at_rest errst_live -> FARM_stmt 0xe1c14.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros CF X7P en st LBc Lc f mc K BI len max off top bot strs od oh on xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s1v s2v t3 t4 t5 t6 ol (INV & FU & LOC).
    pose proof (cfree_opt_secure CF) as CFO. unfold cfree_opt_stmt in CFO. unfold X7_stmt, J_X7 in X7P.
    pose proof (proj1 INV) as COM. pose proof COM as (CST & FR0 & LE & INCL0 & INCL & NPL & INE & INL & PERM & SAVED & SLO & SPB & B63 & AL16 & EPE & ROOM & PAY & DLEN & NDE & REL).
    pose proof CST as (HP & CO & (errv & AV & SPB' & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold LX_FUZZ_STACK, GLOBALS_TOP in *.
    pose proof (bv_unsigned_in_range _ (w_sp en)) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold w_SP in *.
    rewrite unsigned_lit in ST by (clear - SPR SLO LO GLO; lia).
    pose proof (munch_refl ([] : list (Z * Z)) mc) as MU. pose proof (wmono_refl usegs mc) as WM.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. ths. ths. chere.
    eapply climpl_seq.
    { eapply CFO with (ob := on) (lo := w_lo en) (B := w_B en); [clear - FU; lia| exact CST| rewrite unsigned_lit by lia; unfold CSF_STACK, CF_STACK, RFREE_STACK; clear - SLO; lia| reflexivity
        | exact (f7_ob _ _ _ _ _ _ _ _ _ _ _ _ _ (olist od ++ olist oh) [] on ltac:(rewrite app_nil_r, <- app_assoc; exact INV))]. }
    cbv beta. intros f1 L1 st1 ms1 (v1 & m1 & LB1 & RET & FU1 & GR1 & CST1 & FRM1 & R1).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM1 by lia.
    pose proof (f7_step _ _ _ _ _ _ _ _ _ _ _ _ _ (olist od ++ olist oh) [] on _ _ _ _ ltac:(rewrite app_nil_r, <- app_assoc; exact INV) CST1 FRM1 R1) as INV1.
    rewrite app_nil_r in INV1.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ (proj1 FRM1) LOC ltac:(clear; lia)) as LOC1.
    pose proof (proj1 INV1) as COM1. pose proof (proj1 COM1) as CST1'. pose proof CST1' as (HP1 & _ & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _). unfold w_SP in ST1. rewrite unsigned_lit in ST1 by lia.
    clear MU WM HP MI ST ERR LATCH LXS CIMG FRM1 CST CST1 R1 INV COM.
    pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. ths. chere.
    eapply climpl_seq.
    { eapply CFO with (ob := oh) (lo := w_lo en) (B := w_B en); [clear - FU FU1; lia| exact CST1'| rewrite unsigned_lit by lia; unfold CSF_STACK, CF_STACK, RFREE_STACK; clear - SLO; lia| reflexivity
        | exact (f7_ob _ _ _ _ _ _ _ _ _ _ _ _ _ (olist od) [] oh ltac:(rewrite app_nil_r; exact INV1))]. }
    cbv beta. intros f2 L2 st2 ms2 (v2 & m2 & LB2 & RET & FU2 & GR2 & CST2 & FRM2 & R2).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM2 by lia.
    pose proof (f7_step _ _ _ _ _ _ _ _ _ _ _ _ _ (olist od) [] oh _ _ _ _ ltac:(rewrite app_nil_r; exact INV1) CST2 FRM2 R2) as INV2.
    rewrite app_nil_r in INV2.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ (proj1 FRM2) LOC1 ltac:(clear; lia)) as LOC2.
    pose proof (proj1 INV2) as COM2. pose proof (proj1 COM2) as CST2'. pose proof CST2' as (HP2 & _ & (errv2 & _ & _ & ST2 & _ & _ & MI2 & _) & _). unfold w_SP in ST2. rewrite unsigned_lit in ST2 by lia.
    clear MU WM HP1 MI1 ST1 FRM2 CST1' CST2 R2 INV1 COM1 LOC1.
    pose proof (munch_refl ([] : list (Z * Z)) m2) as MU. pose proof (wmono_refl usegs m2) as WM.
    (* [comment removed for export] *)
    cprefix. ths. ths. ths. ths. chere.
    eapply climpl_seq.
    { eapply CFO with (ob := od) (lo := w_lo en) (B := w_B en); [clear - FU FU1 FU2; lia| exact CST2'| rewrite unsigned_lit by lia; unfold CSF_STACK, CF_STACK, RFREE_STACK; clear - SLO; lia| reflexivity
        | exact (f7_ob _ _ _ _ _ _ _ _ _ _ _ _ _ [] [] od ltac:(cbn [app]; rewrite app_nil_r; exact INV2))]. }
    cbv beta. intros f3 L3 st3 ms3 (v3 & m3 & LB3 & RET & FU3 & GR3 & CST3 & FRM3 & R3).
    destruct RET as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ->). cret_lit. rewrite unsigned_lit in FRM3 by lia.
    pose proof (f7_step _ _ _ _ _ _ _ _ _ _ _ _ _ [] [] od _ _ _ _ ltac:(cbn [app]; rewrite app_nil_r; exact INV2) CST3 FRM3 R3) as INV3.
    cbn [app] in INV3.
    pose proof (cfr_cells_stack _ _ _ _ _ _ _ _ (proj1 FRM3) LOC2 ltac:(clear; lia)) as LOC3.
    destruct INV3 as (COM3 & MB3 & LIVE3 & LEN3 & SIN3 & SL3 & NWS3 & KFR3 & KL3 & KS3 & NDSN3 & SFR3 & SLBL3). rewrite app_nil_r in KS3, NDSN3, SFR3, SLBL3.
    pose proof (proj1 COM3) as CST3'. pose proof CST3' as (HP3 & _ & (errv3 & _ & _ & ST3 & _ & _ & MI3 & _) & _). unfold w_SP in ST3. rewrite unsigned_lit in ST3 by lia.
    clear MU WM HP2 MI2 ST2 FRM3 CST2' CST3 R3 INV2 COM2 LOC2.
    pose proof (munch_refl ([] : list (Z * Z)) m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    (* [comment removed for export] *)
    eapply (X7P en st3 LB3 L3 f3 m3 K BI len max off top bot strs); [| clear - FU FU1 FU2 FU3; lia| exact MB3| exact KFR3| exact KL3| exact KS3| exact LIVE3| exact LEN3| exact SIN3| exact SL3| exact NDSN3| exact SFR3| exact SLBL3| exact LOC3].
    lazymatch type of COM3 with w7_com _ _ _ _ _ _ ?add => replace add with (mbk_ents K max ++ bents strs) in COM3 by (cbn [bents map]; rewrite app_nil_r; reflexivity) end. exact COM3.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition F7_stmt : Prop :=
    forall (en : w7e) st LBc Lc f mc (K : mbk) (BI len max off top bot : Z) (strs : list block) (od oh on : option block)
           (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v t3 t4 t5 t6 ol : word),
    farm_pre en st LBc Lc f mc K BI len max off top bot strs od oh on ol ->
    climpl f Lc st (MS (mkR xra (wz (w_SP en + -64)) (w_gp en) (w_tp en) t0 t1 t2 (wz BI) (wz (w_D en)) a0 a1 a2 a3 a4 a5 a6 a7
                       s2v (w_s3 en) (w_s4 en) (w_s5 en) (w_s6 en) (w_s7 en) (w_s8 en) (w_s9 en) (w_s10 en) (w_s11 en) t3 t4 t5 t6)
                 (w_F en) (wz J_F7) (w_fc en) None mc (seg_rom usegs))
      (w7_post libenv errst_at_rest en).

  Theorem F7_proof : FARM_stmt 0xe1bdc -> FARM_stmt 0xe1c14 -> F7_stmt.
  Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
    intros FP7P FS7P en st LBc Lc f mc K BI len max off top bot strs od oh on xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v t3 t4 t5 t6 ol PRE.
    pose proof PRE as (INV & FU & LOC). unfold FARM_stmt in FP7P, FS7P. unfold J_F7.
    pose proof (proj1 INV) as COM. pose proof COM as (CST & FR0 & LE & INCL0 & INCL & NPL & INE & INL & PERM & SAVED & SLO & SPB & B63 & AL16 & EPE & ROOM & PAY & DLEN & NDE & REL).
    pose proof CST as (HP & CO & (errv & AV & SPB' & ST & LO & ERR & MI & TP) & LXS & LATCH & CIMG & GLO).
    unfold LX_FUZZ_STACK, GLOBALS_TOP in *.
    pose proof (bv_unsigned_in_range _ (w_sp en)) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold w_SP in *.
    rewrite unsigned_lit in ST by (clear - SPR SLO LO GLO; lia).
    (* [comment removed for export] *)
    destruct PAY as (PB & PR & D0 & D63 & D26 & PBLK). unfold zlength in DLEN, D63, D26.
    destruct (w_d en) as [|c0 d'] eqn:ED; [cbn in DLEN; lia|].
    destruct PBLK as [X|(pb & INpb & PB1 & PB2)]; [discriminate|].
    assert (PBc : bytes_at usegs mc (w_D en) (to_bytes (c0 :: d'))).
    { pose proof FR0 as (CFR & _). eapply bytes_at_agree; [exact CFR| exact PB|]. intros a Ha. right; left. exists pb.
      split; [unfold w_LBall; apply in_or_app; right; exact INpb|]. split; [| unfold to_bytes in Ha; rewrite length_map in Ha; unfold zlength in PB2; lia].
      intros E. unfold w_LBall in NDE. rewrite map_app in NDE. apply (nodup_app_disj _ _ (w_pe en) NDE); [rewrite E; apply in_map; exact INpb| exact EPE]. }
    pose proof (bytes_at_read usegs mc (w_D en) (to_bytes (c0 :: d')) 0 1 PBc ltac:(clear; lia) ltac:(cbn; clear; lia)) as RD. cbn [firstn skipn to_bytes map Z.to_nat] in RD.
    pose proof RD as RD'. replace (wa (w_D en + 0)) with (Z_to_bv 64 (w_D en)) in RD' by (unfold wa; f_equal; clear; lia).
    pose proof (munch_refl ([] : list (Z * Z)) mc) as MU. pose proof (wmono_refl usegs mc) as WM.
    cprefix. zstep. clear RD RD'. ths. ths. ths. if_cases K0; zify_cond K0.
    - chere. eapply FS7P. exact PRE.
    - chere. eapply FP7P. exact PRE.
  Qed.
End Client.
End W7.
