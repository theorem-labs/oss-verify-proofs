(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire CtModel ApBase ApState ApErr ApBridge.
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem SFModel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface Malloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface RAligned_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Monad ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Printf_lib F_memcpy.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpInit HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApWalkTac ApErrKit ApIface W_err_new W_err_set_debug W_err_set_error W_get_object_walk ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtParseU Require Import PzDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctDefs W_sct_list_free SctRep W_sct_leaves W_sk_leaves SctStmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncU Require Import EncPure EncStmt EncKit W_sct_complete W_i2o_sct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope am_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Ltac to_implM :=
  lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
    lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.

Lemma zlength_app_l : forall {A} (a b : list A), zlength (a ++ b) = zlength a + zlength b.
Proof. intros. unfold zlength. rewrite length_app. lia. Qed.
Lemma zlength_ge0 : forall {A} (l : list A), 0 <= zlength l.
Proof. intros. unfold zlength. lia. Qed.

Definition INNER_HEAD : Z := 0x19d17c.   (* [comment removed for export] *)
Definition INNER_EXIT : Z := 0x19d1ec.   (* [comment removed for export] *)
Definition RAISE_B : Z := 0x19d2cc.      (* [comment removed for export] *)
Definition RAISE_RET_B : Z := 0x19d2f8.

(* [comment removed for export] *)
Lemma implM_ap_assoc {CE__ : Ceiling} : forall {A B C} (t : aprog bptr A) (f : A -> aprog bptr B) (g : B -> aprog bptr C) s Q ms,
  implM ctusegs (interp (ap_embed (apbind t (fun a => apbind (f a) g)))) s Q ms ->
  implM ctusegs (interp (ap_embed (apbind (apbind t f) g))) s Q ms.
Proof.
  intros A B C t f g. induction t as [a| |n k IH|p k IH|p n k IH|p n k IH|o k IH|p n k IH]; intros s Q ms H; cbn [apbind ap_embed interp] in *; try exact H.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r s1). exact H1.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [u s1] ms1 H1. cbn [fst snd] in *. apply (IH s1). exact H1.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r s1). exact H1.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r s1). exact H1.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r s1). exact H1.
  - unfold implM, Monad.mbind in *. eapply impl_ebind_cont; [|exact H]. intros [r s1] ms1 H1. cbn [fst snd] in *. apply (IH r s1). exact H1.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma sct_ok_of_rep : forall s L m adr x, RHEAP s L m -> sct_rep m L adr x -> sct_ok adr x.
Proof.
  intros s L m adr x HEAP (H1 & H2 & H3 & H4 & H5 & H6 & ND & VR & VN & HR & GR & TS & EL & OE & OS & OB).
  assert (AR : forall q n, arr_rep m L adr (Some (q, n)) -> 0 < adr q < 2^64 /\ 0 < n /\ adr q + n <= alloc_ceiling).
  { intros q n (Hn & HIn & _). pose proof (blk_bounds _ _ _ _ _ _ HEAP HIn) as (B1 & B2 & B3 & B4 & B5). lia. }
  unfold sct_ok. split; [exact VR|]. split; [exact HR|]. split; [exact GR|].
  split. { intros q n E. rewrite E in H5. pose proof (AR q n H5). unfold olen, MAX_SCT_SIZE in OS. rewrite E in OS. lia. }
  split. { intros q n E. rewrite E in H6. pose proof (AR q n H6). lia. }
  split. { intros q E. rewrite E in H3. cbn [osz32 option_map] in H3. pose proof (AR q 32 H3). lia. }
  unfold olen, MAX_SCT_SIZE in OE, OB, EL.
  split. { rewrite EL. destruct (sc_ext x) as [[q n]|]; [pose proof (proj1 H4); lia| lia]. }
  split. { rewrite sc_bloblen_olen. unfold olen. destruct (sc_blob x) as [[q n]|]; [pose proof (proj1 H6); lia| lia]. }
  split. { intros q n E. rewrite E in H4. pose proof (AR q n H4). lia. }
  split; [exact EL| rewrite sc_bloblen_olen; reflexivity].
Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Section Act.
  (* [comment removed for export] *)
  Variables (sp gp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z).
  Variables (lo B : Z) (canary : word) (K : list block) (adr : bptr -> Z) (k : skr bptr) (DER : Z).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis GLO : 3493888 <= lo.
  Hypothesis LOB : lo <= bv_unsigned sp - I2D_SCT_LIST_STACK.
  Hypothesis SPB : bv_unsigned sp <= B.
  Hypothesis B63 : B < 2 ^ 63.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis DERlo : bv_unsigned sp <= DER.
  Hypothesis DERhi : DER + 8 <= B.
  Hypothesis SKLB : forall b, In b (sk_blocks adr k) -> In b LB.   (* [comment removed for export] *)

  Definition XC : list (Z * Z) := [(DER, DER + 8)].
  Lemma XCB : Forall (fun iv => bv_unsigned sp <= fst iv /\ snd iv <= B) XC.
  Proof using DERhi DERlo. constructor; [cbn; lia| constructor]. Qed.
  Local Notation EINV := (einv sp m s LB E lo B canary K XC).

  Lemma SPR : 0 <= bv_unsigned sp < 2 ^ 64.
  Proof. pose proof (bv_unsigned_in_range 64 sp) as H. unfold bv_modulus in H. cbn in H. exact H. Qed.

  Lemma q16 : forall d, d mod 16 = 0 -> (bv_unsigned sp + d) mod 16 = 0.
  Proof using SP16. intros d Hd. rewrite Z.add_mod, SP16, Hd by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma k_facts : forall q sX stX mX OWX errvX boX NEW, EINV q sX stX mX OWX errvX boX NEW ->
    RHEAP sX (OWX ++ NEW ++ LB) mX /\ List.NoDup (map blk_id (OWX ++ NEW ++ LB))
    /\ (forall p Ap n, In (p, Ap, n) (OWX ++ NEW ++ LB) -> 0 < Ap /\ 0 <= n /\ Ap + n <= alloc_ceiling /\ (Ap + n <= 0x10000 \/ 0x355000 <= Ap) /\ Ap mod 16 = 0)
    /\ (forall p Ap n, In (p, Ap, n) NEW -> ~ In p (map blk_id (OWX ++ LB)))
    /\ (forall p Ap n pb PA psz, In (p, Ap, n) NEW -> In (pb, PA, psz) LB -> Ap + n <= PA \/ PA + psz <= Ap)
    /\ (forall p Ap n pb PA psz, In (p, Ap, n) NEW -> In (pb, PA, psz) OWX -> Ap + n <= PA \/ PA + psz <= Ap)
    /\ (forall p Ap n pb PA psz, In (p, Ap, n) NEW -> In (pb, PA, psz) NEW -> p <> pb -> Ap + n <= PA \/ PA + psz <= Ap).
  Proof. intros. eapply einv_facts; eassumption. Qed.
  Lemma k_ap_pre : forall q sX stX mX OWX errvX boX NEW stack,
    EINV q sX stX mX OWX errvX boX NEW -> q mod 16 = 0 -> lo <= q - stack ->
    ap_pre sX stX mX OWX (NEW ++ LB) E boX (Z_to_bv 64 q) lo B errvX canary stack
    /\ (forall b, In b K -> In b OWX) /\ (forall b, In b K -> ~ In (blk_id b) (es_ids stX ++ env_ids E)).
  Proof using B63 CEIL GLO SPB. intros. eapply einv_ap_pre; try eassumption; try exact XCB. Qed.
  Lemma k_after : forall q sX stX mX OWX errvX boX NEW sY stY mY OWY (errvY : word) boY XX NEW2,
    EINV q sX stX mX OWX errvX boX NEW ->
    ap_pre sY stY mY OWY (NEW2 ++ NEW ++ LB) E boY (Z_to_bv 64 q) lo B errvY canary 0 ->
    lx_pres (NEW ++ LB) q (XX ++ LIBW_AP) mX mY ->
    (forall a, rin_ivs XX a -> (lo <= a < bv_unsigned sp) \/ rin_ivs XC a \/ (exists p Ap n, In (p, Ap, n) NEW /\ Ap <= a < Ap + n)) ->
    ps_so sY = ps_so sX -> ps_fa sY = ps_fa sX -> blocks_kept K stY OWY mX mY ->
    EINV q sY stY mY OWY errvY boY (NEW2 ++ NEW).
  Proof using B63 CEIL DERhi DERlo GLO SPB.
    intros until NEW2. intros EI PRE LX HXX SO FA BK. pose proof SPR. pose proof EI as ((_ & _ & _ & _ & _ & LOQ0 & _) & _).
    eapply einv_after; try eassumption; try exact XCB. rewrite (unsigned_lit q) by lia. exact LX.
  Qed.
  Lemma k_munch : forall q q' sX stX mX OWX errvX boX NEW mY W,
    EINV q sX stX mX OWX errvX boX NEW -> munch W mX mY -> wmono ctusegs mX mY -> mem_inv ctusegs mY -> stk ctusegs mY lo q' -> lo <= q' <= bv_unsigned sp ->
    Forall (own_iv sp lo XC NEW) W -> EINV q' sX stX mY OWX errvX boX NEW.
  Proof using CEIL DERhi DERlo GLO SPB. intros. eapply einv_munch; try eassumption; try exact XCB. Qed.
  Lemma k_alloc : forall q sX stX mX OWX errvX boX NEW sY mY (errvY : word) pn A n,
    EINV q sX stX mX OWX errvX boX NEW -> rheap_pres (OWX ++ NEW ++ LB) q mX mY -> RHEAP sY ((pn, A, n) :: OWX ++ NEW ++ LB) mY ->
    mem_inv ctusegs mY -> stk ctusegs mY lo q -> rw_cells ctusegs mY LX_ERRNO [C4 errvY] -> rauxv_ok mY B -> ps_fa sY = ps_fa sX -> ps_so sY = ps_so sX ->
    EINV q sY stX mY OWX errvY boX ((pn, A, n) :: NEW).
  Proof. intros. eapply einv_alloc; try eassumption; try exact XCB. Qed.
  Lemma k_heap : forall q sX stX mX OWX errvX boX NEW sY mY (errvY : word) L1 LY NEW',
    EINV q sX stX mX OWX errvX boX NEW -> rheap_pres L1 q mX mY -> (forall b, In b OWX \/ In b LB -> In b L1) ->
    RHEAP sY LY mY -> Permutation LY (OWX ++ NEW' ++ LB) ->
    mem_inv ctusegs mY -> stk ctusegs mY lo q -> rw_cells ctusegs mY LX_ERRNO [C4 errvY] -> rauxv_ok mY B -> ps_fa sY = ps_fa sX -> ps_so sY = ps_so sX ->
    EINV q sY stX mY OWX errvY boX NEW'.
  Proof. intros. eapply einv_heap; try eassumption; try exact XCB. Qed.
  Lemma k_call : forall q sX stX mX OWX errvX boX NEW, EINV q sX stX mX OWX errvX boX NEW ->
    RHEAP sX (OWX ++ NEW ++ LB) mX /\ rauxv_ok mX B /\ q <= B /\ stk ctusegs mX lo q /\ alloc_ceiling <= lo /\ GLOBALS_TOP <= lo
    /\ rw_cells ctusegs mX LX_ERRNO [C4 errvX] /\ mem_inv ctusegs mX /\ crypto_statics mX /\ realloc_statics mX /\ ap_state stX mX OWX E boX /\ ap_img mX
    /\ bv_unsigned (Z_to_bv 64 q) = q.
  Proof using B63 CEIL GLO SPB. intros. eapply einv_call; try eassumption; try exact XCB. Qed.
  Lemma k_exit : forall sX stX mX OWX errvX boX NEW, EINV (bv_unsigned sp) sX stX mX OWX errvX boX NEW ->
    ap_pre sX stX mX OWX (NEW ++ LB) E boX sp lo B errvX canary 0
    /\ lx_pres LB (bv_unsigned sp) (XC ++ LIBW_AP) m mX /\ blocks_kept K stX OWX m mX /\ ps_so sX = ps_so s /\ ps_fa sX = ps_fa s
    /\ (forall b, In b NEW -> ~ In (blk_id b) (map blk_id (OWX ++ LB))).
  Proof using B63 CEIL GLO SP16 SPB. intros. eapply einv_exit; try eassumption; try exact XCB. Qed.

  (* [comment removed for export] *)
  Lemma item_facts : forall q sC stC mC OWC errvC boC NEW done x t,
    EINV q sC stC mC OWC errvC boC NEW -> sk_rep mC LB adr k -> sk_items k = done ++ x :: t ->
    let SA := adr (sk_blk k) in let D := optr adr (sk_data k) in let n := sk_num k in let i := zlength done in
    (0 < SA /\ SA + STACK_SIZE <= lo) /\ (0 < D /\ D + 8 * n <= lo) /\ 0 <= i < n /\ n < 2^23
    /\ ro_cells ctusegs mC SA [C4 (wz n)] /\ ro_cells ctusegs mC (SA + SKO_DATA) [C8 (wz D)]
    /\ ro_cells ctusegs mC (D + 8 * i) [C8 (wz (adr (sc_blk x)))]
    /\ sct_rep mC LB adr x /\ sct_ok adr x /\ (0 < adr (sc_blk x) /\ adr (sc_blk x) + SCT_SIZE <= lo)
    /\ (forall b, In b (sct_blocks adr x) -> In b LB).
  Proof using CEIL.
    intros until t. intros EI SK EQ. cbn zeta.
    pose proof (k_facts _ _ _ _ _ _ _ _ EI) as (HEAP & _).
    pose proof SK as (HIN & (sorted & SR & HC) & HD & HFI & ND).
    pose proof (blk_bounds _ _ _ _ _ _ HEAP ltac:(apply in_app_iff; right; apply in_app_iff; right; exact HIN)) as (B1 & B2 & B3 & B4 & B5). unfold STACK_SIZE in *.
    assert (LEN : sk_num k = zlength done + 1 + zlength t) by (unfold sk_num; rewrite EQ, zlength_app_l; unfold zlength; cbn [length]; lia).
    pose proof (zlength_ge0 done) as D0. pose proof (zlength_ge0 t) as T0.
    destruct (sk_data k) as [[q0 na]|] eqn:ED; cbn [optr].
    2:{ exfalso. rewrite HD in EQ. destruct done; discriminate. }
    destruct HD as (HQ & HNA & HNA2 & jb & HJ & HDB).
    pose proof (blk_bounds _ _ _ _ _ _ HEAP ltac:(apply in_app_iff; right; apply in_app_iff; right; exact HQ)) as (C1 & C2 & C3 & C4 & C5).
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    unfold sk_cells in HC.
    lazymatch type of HC with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?rest) =>
      pose proof (proj1 (proj1 (rw_cells_app mC _ [c0] (c1 :: c2 :: rest)) HC)) as X0;
      pose proof (proj2 (proj1 (rw_cells_app mC _ [c0; c1] (c2 :: rest)) HC)) as X1;
      pose proof (proj1 (proj1 (rw_cells_app mC _ [c2] rest) X1)) as X8 end.
    cbn [cells_size csize Nat.add] in X8. unfold SKO_DATA. replace (adr (sk_blk k) + Z.of_nat 8) with (adr (sk_blk k) + 8) in X8 by lia.
    rewrite ED in X8. cbn [optr] in X8.
    split; [exact (proj1 X0)|]. split; [exact (proj1 X8)|].
    split.
    { replace (zlength done) with (Z.of_nat (length done)) by reflexivity.
      pose proof (data_block_nth mC adr (adr q0) (sk_items k) jb (length done) x HDB ltac:(rewrite EQ; rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity)) as Y.
      unfold ptrw in Y. exact Y. }
    assert (HX : sct_rep mC LB adr x) by (apply (proj1 (Forall_forall _ _) HFI); rewrite EQ; apply in_app_iff; right; left; reflexivity).
    split; [exact HX|].
    split. { eapply sct_ok_of_rep; [exact HEAP| eapply sct_rep_mono; [| exact HX]]. intros b Hb. apply in_app_iff. right. apply in_app_iff. right. exact Hb. }
    pose proof (blk_bounds _ _ _ _ _ _ HEAP ltac:(apply in_app_iff; right; apply in_app_iff; right; exact (proj1 HX))) as (E1 & E2 & E3 & E4 & E5). unfold SCT_SIZE in *.
    split; [lia|]. intros b Hb. exact (sct_rep_blocks_in _ _ _ _ HX b Hb).
  Qed.

  (* [comment removed for export] *)
  Lemma sk_keep : forall q sX stX mX OWX errvX boX NEW mY W,
    EINV q sX stX mX OWX errvX boX NEW -> sk_rep mX LB adr k -> munch W mX mY -> wmono ctusegs mX mY ->
    Forall (own_iv sp lo XC NEW) W -> sk_rep mY LB adr k.
  Proof using CEIL DERlo LOB.
    intros until W. intros EI SK MU WM HW. pose proof SPR as SPR.
    pose proof (k_facts _ _ _ _ _ _ _ _ EI) as (HEAP & _ & BND & _ & DJL & _).
    eapply sk_rep_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact SK]. intros [[qb Ab] nb] a Hb Ha. cbn [blk_addr blk_size fst snd] in Ha.
    pose proof (sk_allblocks_in _ _ _ _ _ SK Hb) as HbL.
    pose proof (BND qb Ab nb ltac:(apply in_app_iff; right; apply in_app_iff; right; exact HbL)) as (B1 & B2 & B3 & B4 & B5).
    pose proof LOB as LOB'. unfold I2D_SCT_LIST_STACK, ERR_SET_ERROR_STACK in LOB'. pose proof CEIL as CEIL'. pose proof DERlo as DERlo'.
    clear SK HEAP MU WM. induction W as [|[u v] W' IHW]; [exact I|]. apply Forall_cons_iff in HW. destruct HW as [H1 H2].
    cbn [outside]. split; [| exact (IHW H2)]. unfold own_iv in H1. cbn [fst snd] in H1.
    destruct H1 as [H1|[H1|(p & Ap & n & HN & H3 & H4)]]; [std_lia__| unfold XC in H1; destruct H1 as [H1|[]]; injection H1; intros; std_lia__|].
    pose proof (DJL _ _ _ _ _ _ HN HbL). std_lia__.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition rpost (q : Z) (NEW : list block) (x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (Fq : bvmap 5 word) (retpc : Z) (mX : mem)
      (r : unit * ap_st bptr) (sY : PState) : machine_state -> Prop :=
    fun msY => exists (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (FY : bvmap 5 word) (fcY : bv 32) mY OWY (errvY : word) boY,
      msY = MS (mkR y1 (Z_to_bv 64 q) gp (wz RATP) y5 y6 y7 x8 x9 y10 y11 y12 y13 y14 y15 y16 y17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
               FY (Z_to_bv 64 retpc) fcY None mY (seg_rom ctusegs)
      /\ EINV q sY (snd r) mY OWY errvY boY NEW /\ lx_pres (NEW ++ LB) q LIBW_AP mX mY /\ frm0 fcY /\ (forall rr : reg, bv_unsigned rr <> 10 -> reg_get FY rr = reg_get Fq rr).

  Local Ltac after_post PO :=
    cbv beta in PO;
    destruct PO as (?q0 & ?q1 & ?q2 & ?q10 & ?q11 & ?q12 & ?q13 & ?q14 & ?q15 & ?q16 & ?q17 & ?q3 & ?q4 & ?q5 & ?q6 & ?F1 & ?fc1 & ?mA & ?OW1 & ?errv1 & ?bo1
                     & -> & ?FRM1 & ?FE1 & ?PREa & ?LXa & ?SOa & ?FAa & ?BKa & ?EBO1);
    subst bo1;
    lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.

  (* [comment removed for export] *)
  Lemma raise_A_seq : forall q sX stX mX OWX (errvX : word) boX NEW
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (Fq : bvmap 5 word) (fcq : bv 32),
    EINV q sX stX mX OWX errvX boX NEW -> q mod 16 = 0 -> lo <= q - ERR_SET_ERROR_STACK -> frm0 fcq ->
    implM ctusegs (interp (ap_embed (err_raise RS_i2o_notset stX))) sX (rpost q NEW x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 Fq 0x19cbe4 mX)
      (MS (mkR x1 (Z_to_bv 64 q) gp (wz RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          Fq (Z_to_bv 64 I2O_SCT_RAISE) fcq None mX (seg_rom ctusegs)).
  Proof using B63 CEIL DERhi DERlo GLO HF HM SPB.
    intros until fcq. intros EI Q16 LOQ FRM. pose proof SPR as SPR.
    pose proof (k_facts _ _ _ _ _ _ _ _ EI) as (HEAP0 & _).
    destruct (k_ap_pre _ _ _ _ _ _ _ _ ERR_SET_ERROR_STACK EI Q16 LOQ) as (PRE & KO & KI).
    pose proof EI as ((_ & _ & _ & _ & _ & LOQ0 & _) & _).
    assert (ESP : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    destruct (lit_ok_auto A_CT_OCT_C 19 ltac:(vm_compute; reflexivity)) as (fs & fk & LF).
    destruct (lit_ok_auto A_I2O_SCT 8 ltac:(vm_compute; reflexivity)) as (ns & nk & LN).
    unfold I2O_SCT_RAISE, err_raise.
    (* [comment removed for export] *)
    unfold implM. iprefix. step. ihere. to_implM.
    eapply implM_abind.
    { pose proof (ERR_new_walk HF boX) as W. unfold ap_stmt in W.
      eapply W; [eapply ap_pre_stack_le; [exact PRE| unfold ERR_NEW_STACK, ERR_SET_ERROR_STACK; lia]| reflexivity| exact FRM| reflexivity| exact KO| exact KI]. }
    intros r1 sA ms1 PO1. after_post PO1. rewrite ESP in *.
    pose proof (k_after q _ _ _ _ _ _ _ _ _ _ _ _ _ [] [] EI PREa LXa ltac:(intros a Ha; destruct Ha) SOa FAa BKa) as EIa.
    cbn [app] in EIa.
    destruct (k_ap_pre _ _ _ _ _ _ _ _ ERR_SET_ERROR_STACK EIa Q16 LOQ) as (PREa' & KOa & KIa).
    (* [comment removed for export] *)
    unfold implM. iprefix. do 5 step. step. ihere. to_implM.
    eapply implM_abind.
    { pose proof (ERR_set_debug_walk HM HF RS_i2o_notset A_CT_OCT_C A_I2O_SCT boX _ _ _ _ LF LN) as W. unfold ap_stmt in W.
      eapply W; [eapply ap_pre_stack_le; [exact PREa'| unfold ERR_SET_DEBUG_STACK, ERR_SET_ERROR_STACK; lia]| reflexivity| exact FRM1| | exact KOa| exact KIa].
      unfold A_CT_OCT_C, A_I2O_SCT, MallocRep.wz. cbn [rs_line RS_i2o_notset]. repeat split; reflexivity. }
    intros r2 sB0 ms2 PO2. after_post PO2. rewrite ESP in *.
    pose proof (k_after q _ _ _ _ _ _ _ _ _ _ _ _ _ [] [] EIa PREa0 LXa0 ltac:(intros a Ha; destruct Ha) SOa0 FAa0 BKa0) as EIb.
    cbn [app] in EIb.
    destruct (k_ap_pre _ _ _ _ _ _ _ _ ERR_SET_ERROR_STACK EIb Q16 LOQ) as (PREb & KOb & KIb).
    (* [comment removed for export] *)
    unfold implM. iprefix. do 3 step. step. ihere. to_implM.
    eapply implM_mono.
    { pose proof (ERR_set_error_walk RS_i2o_notset 50 106 boX) as W. unfold ap_stmt in W.
      eapply W; [exact PREb| reflexivity| exact FRM0| | exact KOb| exact KIb].
      unfold ERR_LIB_SYS, MallocRep.wz. repeat split; try reflexivity; lia. }
    intros r3 sC ms3 PO3. after_post PO3. rewrite ESP in *.
    pose proof (k_after q _ _ _ _ _ _ _ _ _ _ _ _ _ [] [] EIb PREa1 LXa1 ltac:(intros a Ha; destruct Ha) SOa1 FAa1 BKa1) as EIc.
    cbn [app] in EIc. cbn [fst snd].
    unfold rpost. do 18 eexists. eexists mA1, OW2, errv2. eexists. split; [reflexivity|].
    split; [exact EIc|]. split; [| split; [exact FRM2| intros rr Hr; rewrite (FE2 rr Hr), (FE0 rr Hr); apply (FE1 rr Hr)]].
    eapply lx_pres_trans; [exact LXa|]. eapply lx_pres_trans; [exact LXa0| exact LXa1].
  Qed.
  (* [comment removed for export] *)
  Lemma raise_B_seq : forall q sX stX mX OWX (errvX : word) boX NEW
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (Fq : bvmap 5 word) (fcq : bv 32),
    EINV q sX stX mX OWX errvX boX NEW -> q mod 16 = 0 -> lo <= q - ERR_SET_ERROR_STACK -> frm0 fcq ->
    implM ctusegs (interp (ap_embed (err_raise RS_i2o_list stX))) sX (rpost q NEW x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 Fq 0x19d2f8 mX)
      (MS (mkR x1 (Z_to_bv 64 q) gp (wz RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          Fq (Z_to_bv 64 RAISE_B) fcq None mX (seg_rom ctusegs)).
  Proof using B63 CEIL DERhi DERlo GLO HF HM SPB.
    intros until fcq. intros EI Q16 LOQ FRM. pose proof SPR as SPR.
    pose proof (k_facts _ _ _ _ _ _ _ _ EI) as (HEAP0 & _).
    destruct (k_ap_pre _ _ _ _ _ _ _ _ ERR_SET_ERROR_STACK EI Q16 LOQ) as (PRE & KO & KI).
    pose proof EI as ((_ & _ & _ & _ & _ & LOQ0 & _) & _).
    assert (ESP : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
    destruct (lit_ok_auto A_CT_OCT_C 19 ltac:(vm_compute; reflexivity)) as (fs & fk & LF).
    destruct (lit_ok_auto A_I2O_SCT_LIST 13 ltac:(vm_compute; reflexivity)) as (ns & nk & LN).
    unfold RAISE_B, err_raise.
    (* [comment removed for export] *)
    unfold implM. iprefix. step. ihere. to_implM.
    eapply implM_abind.
    { pose proof (ERR_new_walk HF boX) as W. unfold ap_stmt in W.
      eapply W; [eapply ap_pre_stack_le; [exact PRE| unfold ERR_NEW_STACK, ERR_SET_ERROR_STACK; lia]| reflexivity| exact FRM| reflexivity| exact KO| exact KI]. }
    intros r1 sA ms1 PO1. after_post PO1. rewrite ESP in *.
    pose proof (k_after q _ _ _ _ _ _ _ _ _ _ _ _ _ [] [] EI PREa LXa ltac:(intros a Ha; destruct Ha) SOa FAa BKa) as EIa.
    cbn [app] in EIa.
    destruct (k_ap_pre _ _ _ _ _ _ _ _ ERR_SET_ERROR_STACK EIa Q16 LOQ) as (PREa' & KOa & KIa).
    (* [comment removed for export] *)
    unfold implM. iprefix. do 5 step. step. ihere. to_implM.
    eapply implM_abind.
    { pose proof (ERR_set_debug_walk HM HF RS_i2o_list A_CT_OCT_C A_I2O_SCT_LIST boX _ _ _ _ LF LN) as W. unfold ap_stmt in W.
      eapply W; [eapply ap_pre_stack_le; [exact PREa'| unfold ERR_SET_DEBUG_STACK, ERR_SET_ERROR_STACK; lia]| reflexivity| exact FRM1| | exact KOa| exact KIa].
      unfold A_CT_OCT_C, A_I2O_SCT_LIST, MallocRep.wz. cbn [rs_line RS_i2o_list]. repeat split; reflexivity. }
    intros r2 sB0 ms2 PO2. after_post PO2. rewrite ESP in *.
    pose proof (k_after q _ _ _ _ _ _ _ _ _ _ _ _ _ [] [] EIa PREa0 LXa0 ltac:(intros a Ha; destruct Ha) SOa0 FAa0 BKa0) as EIb.
    cbn [app] in EIb.
    destruct (k_ap_pre _ _ _ _ _ _ _ _ ERR_SET_ERROR_STACK EIb Q16 LOQ) as (PREb & KOb & KIb).
    (* [comment removed for export] *)
    unfold implM. iprefix. do 3 step. step. ihere. to_implM.
    eapply implM_mono.
    { pose proof (ERR_set_error_walk RS_i2o_list 50 105 boX) as W. unfold ap_stmt in W.
      eapply W; [exact PREb| reflexivity| exact FRM0| | exact KOb| exact KIb].
      unfold ERR_LIB_SYS, MallocRep.wz. repeat split; try reflexivity; lia. }
    intros r3 sC ms3 PO3. after_post PO3. rewrite ESP in *.
    pose proof (k_after q _ _ _ _ _ _ _ _ _ _ _ _ _ [] [] EIb PREa1 LXa1 ltac:(intros a Ha; destruct Ha) SOa1 FAa1 BKa1) as EIc.
    cbn [app] in EIc. cbn [fst snd].
    unfold rpost. do 18 eexists. eexists mA1, OW2, errv2. eexists. split; [reflexivity|].
    split; [exact EIc|]. split; [| split; [exact FRM2| intros rr Hr; rewrite (FE2 rr Hr), (FE0 rr Hr); apply (FE1 rr Hr)]].
    eapply lx_pres_trans; [exact LXa|]. eapply lx_pres_trans; [exact LXa0| exact LXa1].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (B0T : Type) (kont : option bptr -> @AM bptr B0T) (QQ : B0T * ap_st bptr -> PState -> machine_state -> Prop).
  Variables (ra0 e8 e9 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 : word).
  Hypothesis KN : forall st' s' ms',
    i2d_post ra0 sp gp e8 e9 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 F s OW LB E lo B canary m K adr k DER (None, st') s' ms' ->
    implM ctusegs (interp (ap_embed (kont None st'))) s' QQ ms'.

  (* [comment removed for export] *)
  Definition Gk (r : option Z) : @AM bptr B0T :=
    match r with
    | None => kont None
    | Some len2 =>
        if MAX_SCT_LIST_SIZE <? len2 then err_raise RS_i2o_list ;;; kont None
        else data <- amalloc len2 ;; oct <- amalloc SZ_ASN1_STRING ;; der <- amalloc (der_hl len2 + len2) ;; afree data ;;; afree oct ;;; kont (Some der)
    end.

  (* [comment removed for export] *)
  Definition frame1 (j : list byte) (data : Z) : list cell :=
    [CB 8%nat j; C8 (Z_to_bv 64 data); C8 e20; C8 e19; C8 e18; C8 e9; C8 e8; C8 ra0].
  Definition frame2 (j : list byte) (pc2 : Z) : list cell :=
    [CB 8%nat j; C8 (Z_to_bv 64 pc2); C8 e24; C8 e23; C8 e22; C8 e21; C8 e20; C8 e19; C8 (Z_to_bv 64 DER); C8 e9; C8 sp; C8 (Z_to_bv 64 0x19d440)].
  Definition frame3 (j : list byte) : list cell :=
    [CB 8%nat j; C8 (Z_to_bv 64 0); C8 e24; C8 e23; C8 e22; C8 e21; C8 e20; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (adr (sk_blk k)));
     C8 (Z_to_bv 64 (bv_unsigned sp + -56)); C8 (Z_to_bv 64 (bv_unsigned sp + -64)); C8 (Z_to_bv 64 0x19d2a8)].

  (* [comment removed for export] *)
  Lemma fail_path : forall sC stC mC OWC (errvC : word) boC (FC : bvmap 5 word) (fcC : bv 32)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (A acc i : Z) j1 j2 j3,
    EINV (bv_unsigned sp + -320) sC stC mC OWC errvC boC [] ->
    rw_cells ctusegs mC (bv_unsigned sp + -64) (frame1 j1 0) -> rw_cells ctusegs mC (bv_unsigned sp + -160) (frame2 j2 0) -> rw_cells ctusegs mC (bv_unsigned sp + -256) (frame3 j3) ->
    rw_cells ctusegs mC (bv_unsigned sp + -320) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 acc); C8 (Z_to_bv 64 i); C8 (Z_to_bv 64 (adr (sk_blk k))); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (bv_unsigned sp + -160)); C8 (Z_to_bv 64 0x19d1d0)] ->
    rw_cells ctusegs mC DER [C8 (Z_to_bv 64 0)] -> sk_rep mC LB adr k -> frm0 fcC -> (forall rr : reg, bv_unsigned rr <> 10 -> reg_get FC rr = reg_get F rr) ->
    0 <= acc < 2^63 -> 0 <= i < 2^31 ->
    implM ctusegs (interp (ap_embed (abind (abind (err_raise RS_i2o_notset) (fun _ => abind (err_raise RS_i2o_list) (fun _ => aret None))) Gk stC))) sC QQ
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -320)) gp (wz RATP) x5 x6 x7 (Z_to_bv 64 (bv_unsigned sp + -256)) (Z_to_bv 64 0) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 A) (Z_to_bv 64 i) (Z_to_bv 64 acc) (Z_to_bv 64 0) (Z_to_bv 64 3) (Z_to_bv 64 (-1)) e24 e25 e26 e27 x28 x29 x30 x31)
          FC (Z_to_bv 64 I2O_SCT_RAISE) fcC None mC (seg_rom ctusegs)).
  Proof using B63 CEIL DERhi DERlo GLO HF HM KN LOB SP16 SPB.
    intros until j3. intros EI FR1 FR2 FR3 FR4 HDER SK FRM FE ACC IR. pose proof SPR as SPR.
    unfold I2D_SCT_LIST_STACK, ERR_SET_ERROR_STACK in LOB.
    (* [comment removed for export] *)
    unfold abind at 1. unfold abind at 1. apply implM_ap_assoc.
    eapply implM_apbind.
    { eapply raise_A_seq; [exact EI| apply q16; reflexivity| unfold ERR_SET_ERROR_STACK; lia| exact FRM]. }
    intros [u1 st1] s1 ms1 RP. unfold rpost in RP. cbn [fst snd] in RP.
    destruct RP as (y1 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & F1' & fc1 & m1 & OW1 & errv1 & bo1 & -> & EI1 & LX1 & FRM1 & FE1).
    cbn [app] in LX1. pose proof (agree_of_lx_pres _ _ _ _ _ LX1) as AG1.
    assert (CL1 : forall a, bv_unsigned sp + -320 <= a -> a < 2^64 -> lx_client LB (bv_unsigned sp + -320) LIBW_AP a).
    { intros a Ha Hb. split; [unfold LIBW_AP; cbn [rin_ivs fst snd]; lia| left; exact Ha]. }
    Ltac xlx H AG CL := apply (rw_cells_agree _ _ _ _ _ AG) in H; [| intros a Ha; apply CL; cbn in Ha; lia].
    xlx FR1 AG1 CL1. xlx FR2 AG1 CL1. xlx FR3 AG1 CL1. xlx FR4 AG1 CL1. xlx HDER AG1 CL1.
    pose proof (k_facts _ _ _ _ _ _ _ _ EI) as (HEAPC & _).
    assert (SK1 : sk_rep m1 LB adr k).
    { eapply sk_rep_agree; [exact AG1| | exact SK]. intros [[qb Ab] nb] a Hb Ha. cbn [blk_addr blk_size fst snd] in Ha.
      pose proof (sk_allblocks_in _ _ _ _ _ SK Hb) as HbL.
      pose proof (blk_bounds _ _ _ _ _ _ HEAPC ltac:(apply in_app_iff; right; apply in_app_iff; right; exact HbL)) as (B1 & B2 & B3 & B4 & B5).
      split; [unfold LIBW_AP; cbn [rin_ivs fst snd]; lia|]. right. left. exists (qb, Ab, nb). split; [exact HbL| cbn; lia]. }
    clear AG1 CL1 EI SK FRM HEAPC.
    pose proof (k_call _ _ _ _ _ _ _ _ EI1) as (_ & _ & _ & ST1 & _ & _ & _ & MI1 & CS1 & _).
    (* [comment removed for export] *)
    cbv beta. unfold implM. iprefix.
    assert (ESP4 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -256)) = bv_unsigned sp + -256) by (apply unsigned_lit; lia).
    replace (Z_to_bv 64 (bv_unsigned sp + -320)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -256)) + -64)) by (rewrite ESP4; f_equal; lia).
    eapply evt_cut.
    { eapply i2o_sct_fail_tail with (lo := lo); rewrite ?ESP4; [| exact MI1| unfold GLOBALS_TOP; lia| unfold I2O_SCT_LEN_STACK; lia| exact CS1|].
      - replace (bv_unsigned sp + -256 + -64) with (bv_unsigned sp + -320) by lia. exact ST1.
      - replace (bv_unsigned sp + -256 + -64) with (bv_unsigned sp + -320) by lia. exact FR4. }
    cbv beta. intros ms2 PO. rewrite ?ESP4 in PO. unfold I2O_SCT_LEN_STACK in PO.
    destruct PO as (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m2 & -> & MU2 & WM2 & MI2 & ST2).
    replace (ret_pc (Z_to_bv 64 0x19d1d0)) with (Z_to_bv 64 0x19d1d0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    Ltac xmu H MU WM := apply (fun H0 => rw_cells_transport _ _ _ _ _ _ H0 MU WM) in H; [| cbn [cells_size csize]; rewrite ?Nat.add_0_r, ?Z2Nat.id by lia; cbn; lia].
    xmu FR1 MU2 WM2. xmu FR2 MU2 WM2. xmu FR3 MU2 WM2. xmu HDER MU2 WM2.
    assert (EI2 : EINV (bv_unsigned sp + -256) s1 st1 m2 OW1 errv1 bo1 []).
    { eapply k_munch; [exact EI1| exact MU2| exact WM2| exact MI2| exact ST2| lia|]. constructor; [left; cbn; lia| constructor]. }
    pose proof (k_facts _ _ _ _ _ _ _ _ EI1) as (HEAP1 & _).
    assert (SK2 : sk_rep m2 LB adr k).
    { eapply sk_rep_agree; [apply (agree_on_of_munch _ _ _ MU2 WM2)| | exact SK1]. intros [[qb Ab] nb] a Hb Ha. cbn [blk_addr blk_size fst snd] in Ha.
      pose proof (sk_allblocks_in _ _ _ _ _ SK1 Hb) as HbL.
      pose proof (blk_bounds _ _ _ _ _ _ HEAP1 ltac:(apply in_app_iff; right; apply in_app_iff; right; exact HbL)) as (B1 & B2 & B3 & B4 & B5). cbn. lia. }
    clear MU2 WM2 MI1 ST1 CS1 EI1 SK1 FR4 HEAP1 LX1.
    pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m2) as MU. pose proof (wmono_refl ctusegs m2) as WM.
    unfold frame3 in FR3.
    (* [comment removed for export] *)
    zstep. btaken. zstep. zstep. btaken. zstep. do 10 zstep. zstep. release_frame FR3 ST2 (bv_unsigned sp + -160). zstep.
    (* [comment removed for export] *)
    zstep. zstep. btaken.
    ihere. to_implM.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (EI3 : EINV (bv_unsigned sp + -160) s1 st1 m3 OW1 errv1 bo1 []).
    { eapply k_munch; [exact EI2| exact MU| exact WM| assumption| exact ST2| lia|]. constructor; [left; cbn; lia| constructor]. }
    assert (SK3 : sk_rep m3 LB adr k).
    { pose proof (k_facts _ _ _ _ _ _ _ _ EI2) as (HEAP2 & _).
      eapply sk_rep_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact SK2]. intros [[qb Ab] nb] a Hb Ha. cbn [blk_addr blk_size fst snd] in Ha.
      pose proof (sk_allblocks_in _ _ _ _ _ SK2 Hb) as HbL.
      pose proof (blk_bounds _ _ _ _ _ _ HEAP2 ltac:(apply in_app_iff; right; apply in_app_iff; right; exact HbL)) as (B1 & B2 & B3 & B4 & B5). cbn. lia. }
    clear EI2 SK2 MU WM.
    (* [comment removed for export] *)
    unfold abind at 1. apply implM_ap_assoc.
    eapply implM_apbind.
    { eapply raise_B_seq; [exact EI3| apply q16; reflexivity| unfold ERR_SET_ERROR_STACK; lia| exact FRM1]. }
    intros [u2 st2] s2 ms2 RP. unfold rpost in RP. cbn [fst snd] in RP.
    destruct RP as (w1 & w5 & w6 & w7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & F2' & fc2 & m4 & OW2 & errv2 & bo2 & -> & EI4 & LX4 & FRM4 & FE4).
    cbn [app] in LX4. pose proof (agree_of_lx_pres _ _ _ _ _ LX4) as AG4.
    assert (CL4 : forall a, bv_unsigned sp + -160 <= a -> a < 2^64 -> lx_client LB (bv_unsigned sp + -160) LIBW_AP a).
    { intros a Ha Hb. split; [unfold LIBW_AP; cbn [rin_ivs fst snd]; lia| left; exact Ha]. }
    xlx FR1 AG4 CL4. xlx FR2 AG4 CL4. xlx HDER AG4 CL4.
    pose proof (k_facts _ _ _ _ _ _ _ _ EI3) as (HEAP3 & _).
    assert (SK4 : sk_rep m4 LB adr k).
    { eapply sk_rep_agree; [exact AG4| | exact SK3]. intros [[qb Ab] nb] a Hb Ha. cbn [blk_addr blk_size fst snd] in Ha.
      pose proof (sk_allblocks_in _ _ _ _ _ SK3 Hb) as HbL.
      pose proof (blk_bounds _ _ _ _ _ _ HEAP3 ltac:(apply in_app_iff; right; apply in_app_iff; right; exact HbL)) as (B1 & B2 & B3 & B4 & B5).
      split; [unfold LIBW_AP; cbn [rin_ivs fst snd]; lia|]. right. left. exists (qb, Ab, nb). split; [exact HbL| cbn; lia]. }
    clear AG4 CL4 EI3 SK3 HEAP3 LX4.
    pose proof (k_call _ _ _ _ _ _ _ _ EI4) as (_ & _ & _ & ST4 & _ & _ & _ & MI4 & _).
    (* [comment removed for export] *)
    cbv beta iota delta [apbind aret Gk fst snd].
    unfold implM. iprefix.
    pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m4) as MU. pose proof (wmono_refl ctusegs m4) as WM.
    unfold frame2 in FR2. unfold frame1 in FR1.
    (* [comment removed for export] *)
    zstep. do 10 zstep. zstep. release_frame FR2 ST4 (bv_unsigned sp + -64). zstep.
    zstep. zstep. btaken. zstep. do 6 zstep. zstep. release_frame FR1 ST4 (bv_unsigned sp). zstep.
    ihere. to_implM.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    assert (EI5 : EINV (bv_unsigned sp) s2 st2 m5 OW2 errv2 bo2 []).
    { eapply k_munch; [exact EI4| exact MU| exact WM| assumption| exact ST4| lia|]. constructor; [left; cbn; lia| constructor]. }
    pose proof (k_facts _ _ _ _ _ _ _ _ EI4) as (HEAP4 & _).
    assert (SK5 : sk_rep m5 LB adr k).
    { eapply sk_rep_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact SK4]. intros [[qb Ab] nb] a Hb Ha. cbn [blk_addr blk_size fst snd] in Ha.
      pose proof (sk_allblocks_in _ _ _ _ _ SK4 Hb) as HbL.
      pose proof (blk_bounds _ _ _ _ _ _ HEAP4 ltac:(apply in_app_iff; right; apply in_app_iff; right; exact HbL)) as (B1 & B2 & B3 & B4 & B5). cbn. lia. }
    destruct (k_exit _ _ _ _ _ _ _ EI5) as (PRE5 & LX5 & BK5 & SO5 & FA5 & FRESH5). cbn [app] in PRE5.
    apply KN. unfold i2d_post. cbn [fst snd].
    do 15 eexists. exists F2', fc2, m5, OW2, errv2, bo2, []. cbn [app].
    split; [reflexivity|]. split; [exact FRM4|]. split; [intros rr Hr; rewrite (FE4 rr Hr), (FE1 rr Hr); apply (FE rr Hr)|].
    split; [exact PRE5|]. split; [exact LX5|]. split; [exact SO5|]. split; [exact FA5|]. split; [exact BK5|].
    split; [intros b Hb; destruct Hb|]. split; [exact SK5|]. split; [reflexivity| exact HDER].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Fixpoint i2o_sum (l : list (sctr bptr)) : Z := match l with [] => 0 | x :: t => 2 + i2o_sct_len x + i2o_sum t end.
  Lemma i2o_sum_ge0 : forall l, Forall (sct_ok adr) l -> 0 <= i2o_sum l <= 196702 * zlength l.
  Proof using sp.
    induction l as [|x t IH]; intros H; cbn [i2o_sum]; [unfold zlength; cbn; lia|]. apply Forall_cons_iff in H. destruct H as [Hx Ht].
    specialize (IH Ht). unfold zlength in *. cbn [length].
    destruct Hx as (VR & HR & GR & SIGP & BLOBP & LOGP & ELR & BLR & EXTP & EXTL & BLBL).
    assert (SL : 0 <= sc_siglen x <= 65535) by (unfold sc_siglen; destruct (sc_sig x) as [[q n]|] eqn:ES; [pose proof (SIGP q n eq_refl); lia| lia]).
    unfold i2o_sct_len. destruct (sc_version x =? 0); lia.
  Qed.

  (* [comment removed for export] *)
  Definition len_done (stC : ap_st bptr) (sC : PState) (OWC : list block) (errvC : word) (boC : Z * Z) (FC : bvmap 5 word) (fcC : bv 32) (tot : Z) : Prop :=
    forall mD (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) j1 j2 j3,
      EINV (bv_unsigned sp + -256) sC stC mD OWC errvC boC [] ->
      rw_cells ctusegs mD (bv_unsigned sp + -64) (frame1 j1 0) -> rw_cells ctusegs mD (bv_unsigned sp + -160) (frame2 j2 0) -> rw_cells ctusegs mD (bv_unsigned sp + -256) (frame3 j3) ->
      rw_cells ctusegs mD DER [C8 (Z_to_bv 64 0)] -> sk_rep mD LB adr k ->
      Forall (fun x => sct_complete x = true) (sk_items k) ->
      implM ctusegs (interp (ap_embed (Gk (Some tot) stC))) sC QQ
        (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -256)) gp (wz RATP) y5 y6 y7 (Z_to_bv 64 (bv_unsigned sp + -160)) (Z_to_bv 64 0) y10 y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 (adr (sk_blk k))) (Z_to_bv 64 (sk_num k)) (Z_to_bv 64 tot) (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 (-1)) e24 e25 e26 e27 y28 y29 y30 y31)
            FC (Z_to_bv 64 INNER_EXIT) fcC None mD (seg_rom ctusegs)).

  Lemma len_loop : forall rest done acc sC stC mC OWC (errvC : word) boC (FC : bvmap 5 word) (fcC : bv 32)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) j1 j2 j3,
    sk_items k = done ++ rest -> Forall (sct_ok adr) (sk_items k) -> rest <> [] -> 0 <= acc -> acc + i2o_sum rest < 2^62 ->
    Forall (fun x => sct_complete x = true) done ->
    EINV (bv_unsigned sp + -256) sC stC mC OWC errvC boC [] ->
    rw_cells ctusegs mC (bv_unsigned sp + -64) (frame1 j1 0) -> rw_cells ctusegs mC (bv_unsigned sp + -160) (frame2 j2 0) -> rw_cells ctusegs mC (bv_unsigned sp + -256) (frame3 j3) ->
    rw_cells ctusegs mC DER [C8 (Z_to_bv 64 0)] -> sk_rep mC LB adr k -> frm0 fcC -> (forall rr : reg, bv_unsigned rr <> 10 -> reg_get FC rr = reg_get F rr) ->
    len_done stC sC OWC errvC boC FC fcC (acc + i2o_sum rest) ->
    implM ctusegs (interp (ap_embed (abind (i2o_len_pass rest acc) Gk stC))) sC QQ
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -256)) gp (wz RATP) x5 x6 x7 (Z_to_bv 64 (bv_unsigned sp + -160)) (Z_to_bv 64 0) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (adr (sk_blk k))) (Z_to_bv 64 (zlength done)) (Z_to_bv 64 acc) (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 (-1)) e24 e25 e26 e27 x28 x29 x30 x31)
          FC (Z_to_bv 64 INNER_HEAD) fcC None mC (seg_rom ctusegs)).
  Proof using B63 CEIL DERhi DERlo GLO HF HM KN LOB SP16 SPB.
    induction rest as [|x t IH]; intros until j3; intros EQ OKALL NE ACC0 ACCB DONEC EI FR1 FR2 FR3 HDER SK FRM FE DONE; [exfalso; apply NE; reflexivity|].
    pose proof DONE as DONE0. unfold len_done in DONE.
    pose proof SPR as SPR. unfold I2D_SCT_LIST_STACK, ERR_SET_ERROR_STACK in LOB.
    destruct (item_facts _ _ _ _ _ _ _ _ done x t EI SK EQ) as (SAR & DR & IR & NR & RNUM & RDAT & RITEM & REPX & OKX & [XA0 XLO] & XIN).
    pose proof (zlength_ge0 done) as D0.
    pose proof (k_call _ _ _ _ _ _ _ _ EI) as (HEAPC & _ & _ & ST & _ & _ & _ & MI & _).
    assert (OKT : Forall (sct_ok adr) t) by (rewrite EQ in OKALL; apply Forall_app in OKALL; destruct OKALL as [_ OK2]; apply Forall_cons_iff in OK2; exact (proj2 OK2)).
    pose proof (i2o_sum_ge0 t OKT) as SUMT. pose proof (zlength_ge0 t) as TT0.
    cbn [i2o_sum] in ACCB, DONE.
    assert (LENX : 0 <= i2o_sct_len x <= 196700).
    { destruct OKX as (VR & HR & GR & SIGP & BLOBP & LOGP & ELR & BLR & EXTP & EXTL & BLBL).
      assert (SL : 0 <= sc_siglen x <= 65535) by (unfold sc_siglen; destruct (sc_sig x) as [[q n]|] eqn:ES; [pose proof (SIGP q n eq_refl); lia| lia]).
      unfold i2o_sct_len. destruct (sc_version x =? 0); lia. }
    assert (ALG : adr (sk_blk k) mod 8 = 0 /\ optr adr (sk_data k) mod 8 = 0 /\ adr (sc_blk x) mod 8 = 0).
    { pose proof SK as (HIN & _ & HD & _).
      pose proof (blk_bounds _ _ _ _ _ _ HEAPC ltac:(apply in_app_iff; right; apply in_app_iff; right; exact HIN)) as (_ & _ & _ & _ & A5).
      pose proof (blk_bounds _ _ _ _ _ _ HEAPC ltac:(apply in_app_iff; right; apply in_app_iff; right; exact (proj1 REPX))) as (_ & _ & _ & _ & X5).
      destruct (sk_data k) as [[q0 na]|]; cbn [optr].
      - destruct HD as (HQ & _).
        pose proof (blk_bounds _ _ _ _ _ _ HEAPC ltac:(apply in_app_iff; right; apply in_app_iff; right; exact HQ)) as (_ & _ & _ & _ & D5).
        repeat split; Z.div_mod_to_equations; lia.
      - repeat split; Z.div_mod_to_equations; lia. }
    destruct ALG as (SAL & DAL & XAL).
    unfold frame3 in FR3. unfold INNER_HEAD.
    pose proof (munch_refl [(lo, bv_unsigned sp + -256)]%Z mC) as MU. pose proof (wmono_refl ctusegs mC) as WM.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -256)) = bv_unsigned sp + -256) by (apply unsigned_lit; lia).
    (* [comment removed for export] *)
    change (abind (i2o_len_pass (x :: t) acc) Gk stC)
      with (abind (fun st0 => (if sct_complete x then i2o_len_pass t (acc + 2 + i2o_sct_len x) else err_raise RS_i2o_notset ;;; err_raise RS_i2o_list ;;; aret None) st0) Gk stC).
    unfold implM. iprefix.
    (* [comment removed for export] *)
    zstep. btaken. zstep. zstep. zstep.
    eapply evt_cut.
    { eapply (OPENSSL_sk_value_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FC fcC _ lo (adr (sk_blk k)) (sk_num k) (optr adr (sk_data k)) (zlength done) (adr (sc_blk x)));
        [rewrite ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ESP; lia| exact SAR| exact DR| exact SAL| exact DAL| exact RNUM| exact RDAT| exact IR| lia| exact RITEM| reflexivity| reflexivity]. }
    unfold nid_post. cbv beta. intros ms1 PO. rewrite ?ESP in PO.
    destruct PO as (v5 & v6 & v7 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m1 & -> & MU1 & WM1 & MI1 & ST1).
    replace (ret_pc (Z_to_bv 64 0x19d1c8)) with (Z_to_bv 64 0x19d1c8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    xmu FR1 MU1 WM1. xmu FR2 MU1 WM1. xmu FR3 MU1 WM1. xmu HDER MU1 WM1.
    pose proof (proj1 (proj2 REPX)) as HX. apply (fun H0 => rw_cells_transport _ _ _ _ _ _ H0 MU1 WM1) in HX; [| rewrite sct_cells_size; unfold SCT_SIZE in *; cbn; lia].
    assert (EI1 : EINV (bv_unsigned sp + -256) sC stC m1 OWC errvC boC []).
    { eapply k_munch; [exact EI| exact MU1| exact WM1| exact MI1| exact ST1| lia|]. constructor; [left; cbn; lia| constructor]. }
    assert (SK1 : sk_rep m1 LB adr k).
    { eapply sk_rep_agree; [apply (agree_on_of_munch _ _ _ MU1 WM1)| | exact SK]. intros [[qb Ab] nb] a Hb Ha. cbn [blk_addr blk_size fst snd] in Ha.
      pose proof (sk_allblocks_in _ _ _ _ _ SK Hb) as HbL.
      pose proof (blk_bounds _ _ _ _ _ _ HEAPC ltac:(apply in_app_iff; right; apply in_app_iff; right; exact HbL)) as (B1 & B2 & B3 & B4 & B5). cbn. lia. }
    clear MU WM MU1 WM1 MI ST EI SK RNUM RDAT RITEM. rename MI1 into MI. rename ST1 into ST.
    pose proof (munch_refl [(lo, bv_unsigned sp + -256)]%Z m1) as MU. pose proof (wmono_refl ctusegs m1) as WM.
    (* [comment removed for export] *)
    zstep. zstep.
    eapply evt_cut.
    { eapply i2o_sct_len_seg with (lo := lo) (adr := adr) (x := x) (vs := 0); rewrite ?ESP;
        [exact ST| exact MI| unfold GLOBALS_TOP; lia| unfold I2O_SCT_LEN_STACK; lia| lia| exact XLO| exact XAL| exact HX| exact OKX| reflexivity| reflexivity]. }
    cbv beta. intros ms2 PO. rewrite ?ESP in PO. unfold I2O_SCT_LEN_STACK in PO.
    destruct PO as (m2 & MU2 & WM2 & MI2 & POST).
    xmu FR1 MU2 WM2. xmu FR2 MU2 WM2. xmu FR3 MU2 WM2. xmu HDER MU2 WM2.
    pose proof (k_facts _ _ _ _ _ _ _ _ EI1) as (HEAP1 & _).
    assert (SK2 : sk_rep m2 LB adr k).
    { eapply sk_rep_agree; [apply (agree_on_of_munch _ _ _ MU2 WM2)| | exact SK1]. intros [[qb Ab] nb] a Hb Ha. cbn [blk_addr blk_size fst snd] in Ha.
      pose proof (sk_allblocks_in _ _ _ _ _ SK1 Hb) as HbL.
      pose proof (blk_bounds _ _ _ _ _ _ HEAP1 ltac:(apply in_app_iff; right; apply in_app_iff; right; exact HbL)) as (B1 & B2 & B3 & B4 & B5). cbn. lia. }
    destruct (sct_complete x) eqn:CPL.
    - (* [comment removed for export] *)
      destruct POST as ((w5 & w6 & w7 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & ->) & ST2).
      replace (ret_pc (Z_to_bv 64 0x19d1d0)) with (Z_to_bv 64 0x19d1d0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (EI2 : EINV (bv_unsigned sp + -256) sC stC m2 OWC errvC boC []).
      { eapply k_munch; [exact EI1| exact MU2| exact WM2| exact MI2| exact ST2| lia|]. constructor; [left; cbn; lia| constructor]. }
      clear MU WM MU2 WM2 MI ST EI1 SK1 HX HEAP1. rename MI2 into MI. rename ST2 into ST.
      pose proof (munch_refl [(lo, bv_unsigned sp + -256)]%Z m2) as MU. pose proof (wmono_refl ctusegs m2) as WM.
      destruct (item_facts _ _ _ _ _ _ _ _ done x t EI2 SK2 EQ) as (_ & _ & _ & _ & RNUM & _).
      (* [comment removed for export] *)
      zstep. sfalse. zstep. zstep. zstep. rewrite (swrap32_small (zlength done + 1)) by lia. zstep. zstep.
      eapply evt_cut.
      { eapply (OPENSSL_sk_num_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FC fcC _ lo (adr (sk_blk k)) (sk_num k));
          [rewrite ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ESP; lia| exact SAR| exact SAL| exact RNUM| lia| reflexivity]. }
      unfold nid_post. cbv beta. intros ms3 PO. rewrite ?ESP in PO.
      destruct PO as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m3 & -> & MU3 & WM3 & MI3 & ST3).
      replace (ret_pc (Z_to_bv 64 0x19d1e8)) with (Z_to_bv 64 0x19d1e8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      xmu FR1 MU3 WM3. xmu FR2 MU3 WM3. xmu FR3 MU3 WM3. xmu HDER MU3 WM3.
      assert (EI3 : EINV (bv_unsigned sp + -256) sC stC m3 OWC errvC boC []).
      { eapply k_munch; [exact EI2| exact MU3| exact WM3| exact MI3| exact ST3| lia|]. constructor; [left; cbn; lia| constructor]. }
      pose proof (k_facts _ _ _ _ _ _ _ _ EI2) as (HEAP2 & _).
      assert (SK3 : sk_rep m3 LB adr k).
      { eapply sk_rep_agree; [apply (agree_on_of_munch _ _ _ MU3 WM3)| | exact SK2]. intros [[qb Ab] nb] a Hb Ha. cbn [blk_addr blk_size fst snd] in Ha.
        pose proof (sk_allblocks_in _ _ _ _ _ SK2 Hb) as HbL.
        pose proof (blk_bounds _ _ _ _ _ _ HEAP2 ltac:(apply in_app_iff; right; apply in_app_iff; right; exact HbL)) as (B1 & B2 & B3 & B4 & B5). cbn. lia. }
      clear MU WM MU3 WM3 MI ST EI2 SK2 HEAP2 RNUM. rename MI3 into MI. rename ST3 into ST.
      assert (LEN : sk_num k = zlength done + 1 + zlength t) by (unfold sk_num; rewrite EQ, zlength_app_l; unfold zlength; cbn [length]; lia).
      pose proof (zlength_ge0 t) as T0.
      (* [comment removed for export] *)
      zstep. destruct t as [|y t'].
      + (* [comment removed for export] *)
        replace (zlength (@nil (sctr bptr))) with 0 in LEN by reflexivity. rewrite Z.add_0_r in LEN.
        sfalse. ihere. to_implM.
        replace (zlength done + 1) with (sk_num k) by lia.
        lazymatch goal with |- implM _ _ _ _ ?ms => change (implM ctusegs (interp (ap_embed (Gk (Some (acc + 2 + i2o_sct_len x)) stC))) sC QQ ms) end.
        replace (acc + i2o_sct_len x + 2) with (acc + (2 + i2o_sct_len x + i2o_sum [])) by (cbn [i2o_sum]; lia).
        replace (acc + 2 + i2o_sct_len x) with (acc + (2 + i2o_sct_len x + i2o_sum [])) by (cbn [i2o_sum]; lia).
        eapply DONE; try eassumption. rewrite EQ. apply Forall_app. split; [exact DONEC| constructor; [exact CPL| constructor]].
      + (* [comment removed for export] *)
        assert (T1 : 1 <= zlength (y :: t')) by (unfold zlength; cbn [length]; lia).
        strue. ihere. to_implM.
        replace (zlength done + 1) with (zlength (done ++ [x])) by (rewrite zlength_app_l; unfold zlength; cbn [length]; lia).
        replace (acc + i2o_sct_len x + 2) with (acc + 2 + i2o_sct_len x) by lia.
        lazymatch goal with |- implM _ _ _ _ ?ms => change (implM ctusegs (interp (ap_embed (abind (i2o_len_pass (y :: t') (acc + 2 + i2o_sct_len x)) Gk stC))) sC QQ ms) end.
        eapply (IH (done ++ [x]) (acc + 2 + i2o_sct_len x)); try eassumption.
        * rewrite EQ, <- app_assoc. reflexivity.
        * discriminate.
        * lia.
        * cbn [i2o_sum] in *. lia.
        * apply Forall_app. split; [exact DONEC| constructor; [exact CPL| constructor]].
        * replace (acc + 2 + i2o_sct_len x + i2o_sum (y :: t')) with (acc + (2 + i2o_sct_len x + i2o_sum (y :: t'))) by lia. exact DONE0.
    - (* [comment removed for export] *)
      destruct POST as ((w5 & w6 & w7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & ->) & ST2 & FR4).
      assert (EI2 : EINV (bv_unsigned sp + -256 + -64) sC stC m2 OWC errvC boC []).
      { eapply k_munch; [exact EI1| exact MU2| exact WM2| exact MI2| exact ST2| lia|]. constructor; [left; cbn; lia| constructor]. }
      ihere. to_implM.
      replace (bv_unsigned sp + -256 + -64) with (bv_unsigned sp + -320) in * by lia.
      eapply fail_path; try eassumption; try lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma complete_v1_facts : forall x : sctr bptr, sc_version x = 0 -> sct_complete x = true ->
    exists lq sq sn, sc_logid x = Some lq /\ sc_sig x = Some (sq, sn) /\ sct_sig_complete x = true.
  Proof.
    intros x V0 C. unfold sct_complete in C. rewrite V0 in C. cbn [Z.eqb] in C.
    destruct (sc_logid x) as [lq|]; [| discriminate]. cbn [andb] in C.
    pose proof C as C'. unfold sct_sig_complete in C'. destruct (sc_sig x) as [[sq sn]|]; [| rewrite andb_false_r in C'; discriminate].
    exists lq, sq, sn. auto.
  Qed.
  Lemma complete_nv1_facts : forall x : sctr bptr, sc_version x <> 0 -> sct_complete x = true -> exists bq bn, sc_blob x = Some (bq, bn).
  Proof.
    intros x VN C. unfold sct_complete in C. destruct (sc_version x =? -1); [discriminate|].
    replace (sc_version x =? 0) with false in C by (symmetry; apply Z.eqb_neq; exact VN).
    destruct (sc_blob x) as [[bq bn]|]; [exists bq, bn; reflexivity| discriminate].
  Qed.

  (* [comment removed for export] *)
  Lemma arr_bytes : forall mC L q n, arr_rep mC L adr (Some (q, n)) ->
    0 < n /\ In (q, adr q, n) L /\ exists bs, bytes_at ctusegs mC (adr q) bs /\ length bs = Z.to_nat n /\ rw_cells ctusegs mC (adr q) [CB (Z.to_nat n) bs].
  Proof.
    intros mC L q n (Hn & HIn & bs & HC). split; [exact Hn|]. split; [exact HIn|]. exists bs.
    pose proof (cells_at_wf _ _ _ _ (proj1 HC)) as [W _]. cbn in W.
    pose proof (rw_cells_bytes_at _ _ _ _ HC) as BA. cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA. auto.
  Qed.

  (* [comment removed for export] *)
  Lemma item_write : forall ra t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (FC : bvmap 5 word) (fcC : bv 32)
      sC stC OWC (errvC : word) boC NEW (pd : bptr) AD len2 m1 x P junk,
    EINV (bv_unsigned sp + -160) sC stC m1 OWC errvC boC NEW -> In (pd, AD, len2) NEW ->
    sct_rep m1 LB adr x -> sct_ok adr x -> sct_complete x = true -> 0 < adr (sc_blk x) -> adr (sc_blk x) + SCT_SIZE <= lo ->
    AD <= P -> P + i2o_sct_len x <= AD + len2 ->
    rw_cells ctusegs m1 (bv_unsigned sp + -152) [C8 (Z_to_bv 64 P)] -> rw_cells ctusegs m1 P [CB (Z.to_nat (i2o_sct_len x)) junk] ->
    evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' bs,
         ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -160)) gp (wz RATP) t0' t1' t2' s0 s1 (Z_to_bv 64 (i2o_sct_len x)) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  FC (ret_pc ra) fcC None m' (seg_rom ctusegs)
         /\ munch [(bv_unsigned sp + -320, bv_unsigned sp + -160); (bv_unsigned sp + -152, bv_unsigned sp + -144); (P, P + i2o_sct_len x)]%Z m1 m'
         /\ wmono ctusegs m1 m' /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp + -160)
         /\ rw_cells ctusegs m' (bv_unsigned sp + -152) [C8 (Z_to_bv 64 (P + i2o_sct_len x))] /\ rw_cells ctusegs m' P [CB (Z.to_nat (i2o_sct_len x)) bs])
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -160)) gp (wz RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 (bv_unsigned sp + -152)) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FC (Z_to_bv 64 I2O_SCT) fcC None m1 (seg_rom ctusegs)).
  Proof using B63 CEIL GLO LOB SP16 SPB.
    intros until junk. intros EI HDIN REPX OKX CPL XA0 XLO ADP PHI HPP HBX.
    pose proof SPR as SPR. unfold I2D_SCT_LIST_STACK, ERR_SET_ERROR_STACK in LOB.
    pose proof (k_call _ _ _ _ _ _ _ _ EI) as (HEAP & _ & _ & ST & _ & _ & _ & MI & _).
    pose proof (k_facts _ _ _ _ _ _ _ _ EI) as (_ & _ & BND & _ & DJL & _).
    pose proof (BND pd AD len2 ltac:(apply in_app_iff; right; apply in_app_iff; left; exact HDIN)) as (AD0 & _ & ADC & _).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -160)) = bv_unsigned sp + -160) by (apply unsigned_lit; lia).
    pose proof REPX as (XINL & HX & AL & AE & AS & AB & _).
    assert (XAL : adr (sc_blk x) mod 8 = 0).
    { pose proof (BND _ _ _ ltac:(apply in_app_iff; right; apply in_app_iff; right; exact XINL)) as (_ & _ & _ & _ & X5). Z.div_mod_to_equations; lia. }
    assert (SEPLB : forall qb nb, In (qb, adr qb, nb) LB -> adr qb + nb <= lo /\ (adr qb + nb <= P \/ P + i2o_sct_len x <= adr qb)).
    { intros qb nb Hin. pose proof (BND qb (adr qb) nb ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hin)) as (_ & _ & B3 & _).
      pose proof (DJL _ _ _ _ _ _ HDIN Hin). lia. }
    pose proof (SEPLB _ _ XINL) as [_ SEPX].
    pose proof OKX as (VR & HR & GR & SIGP & BLOBP & LOGP & ELR & BLR & EXTP & EXTL & BLBL).
    destruct (Z.eq_dec (sc_version x) 0) as [V0|VN].
    - (* [comment removed for export] *)
      destruct (complete_v1_facts x V0 CPL) as (lq & sq & sn & EL & ES & SCPL).
      pose proof (SIGP sq sn ES) as [SQ0 SN].
      assert (LEN : i2o_sct_len x = 47 + sc_extlen x + sn) by (unfold i2o_sct_len, sc_siglen; rewrite V0, ES; cbn [Z.eqb]; lia).
      unfold osz32 in AL. rewrite EL in AL. cbn [option_map] in AL. rewrite ES in AS.
      destruct (arr_bytes _ _ _ _ AL) as (_ & INL & lid & LID & LIDL & _).
      destruct (arr_bytes _ _ _ _ AS) as (_ & INS & sig & SIG & SLEN & _).
      pose proof (SEPLB _ _ INL) as [LQLO SEPL]. pose proof (SEPLB _ _ INS) as [SQLO SEPS].
      assert (EXT : exists ext, forall eq, sc_ext x = Some (eq, sc_extlen x) ->
                adr eq + sc_extlen x <= lo /\ (adr eq + sc_extlen x <= P \/ P + 47 + sc_extlen x + sn <= adr eq)
                /\ bytes_at ctusegs m1 (adr eq) ext /\ length ext = Z.to_nat (sc_extlen x)).
      { destruct (sc_ext x) as [[eq' en']|] eqn:EX.
        - cbn in EXTL. destruct (arr_bytes _ _ _ _ AE) as (_ & INE & ext & EXB & EXL & _). exists ext. intros eq Heq.
          injection Heq. intros HEN HEQ. subst eq'. rewrite <- EXTL in *. pose proof (SEPLB _ _ INE). rewrite LEN in *. split; [lia|]. split; [lia|]. split; [exact EXB| exact EXL].
        - exists []. intros eq Heq. discriminate. }
      destruct EXT as [ext EXT].
      rewrite LEN in HBX, PHI.
      replace (47 + sc_extlen x + sn) with (1 + (46 + sc_extlen x + sn)) in HBX by lia.
      pose proof (cb_split2 m1 P 1 _ _ HBX ltac:(lia) ltac:(lia)) as [R0 HB1]. clear HBX. change (Z.to_nat 1) with 1%nat in R0.
      replace (46 + sc_extlen x + sn) with (32 + (14 + sc_extlen x + sn)) in HB1 by lia.
      pose proof (cb_split2 m1 _ 32 _ _ HB1 ltac:(lia) ltac:(lia)) as [R1 HB2]. clear HB1. change (Z.to_nat 32) with 32%nat in R1.
      replace (14 + sc_extlen x + sn) with (10 + (4 + sc_extlen x + sn)) in HB2 by lia.
      pose proof (cb_split2 m1 _ 10 _ _ HB2 ltac:(lia) ltac:(lia)) as [R2 HB3]. clear HB2. change (Z.to_nat 10) with 10%nat in R2.
      replace (P + 1 + 32) with (P + 33) in R2, HB3 by lia.
      replace (4 + sc_extlen x + sn) with (sc_extlen x + (4 + sn)) in HB3 by lia.
      pose proof (cb_split2 m1 _ (sc_extlen x) _ _ HB3 ltac:(lia) ltac:(lia)) as [R3 HB4]. clear HB3.
      replace (P + 33 + 10) with (P + 43) in R3, HB4 by lia.
      pose proof (cb_split2 m1 _ 4 sn _ HB4 ltac:(lia) ltac:(lia)) as [R4 R5]. clear HB4. change (Z.to_nat 4) with 4%nat in R4.
      replace (P + 43 + sc_extlen x + 4) with (P + 47 + sc_extlen x) in R5 by lia.
      eapply evt_cut.
      { eapply (i2o_sct_write_v1_spec) with (lo := lo) (adr := adr) (x := x) (vs := 0) (PP := bv_unsigned sp + -152) (P := P) (lq := lq) (sq := sq) (sn := sn)
          (en := sc_extlen x) (lid := lid) (ext := ext) (sig := sig); rewrite ?ESP;
          lazymatch goal with
          | |- stk _ _ _ _ => exact ST
          | |- mem_inv _ _ => exact MI
          | |- rw_cells _ _ (adr (sc_blk x)) _ => exact HX
          | |- sct_ok _ _ => exact OKX
          | |- bytes_at _ _ (adr lq) _ => exact LID
          | |- bytes_at _ _ (adr sq) _ => exact SIG
          | |- rw_cells _ _ (bv_unsigned sp + -152) _ => exact HPP
          | |- rw_cells _ _ P _ => exact R0
          | |- rw_cells _ _ (P + 1) _ => exact R1
          | |- rw_cells _ _ (P + 33) _ => exact R2
          | |- rw_cells _ _ (P + 43) _ => exact R3
          | |- rw_cells _ _ (P + 43 + _) _ => exact R4
          | |- rw_cells _ _ (P + 47 + _) _ => exact R5
          | |- (forall eq, _) => exact EXT
          | |- _ = _ => first [assumption| reflexivity| lia]
          | |- _ => first [assumption| unfold GLOBALS_TOP, I2O_SCT_W_STACK, I2O_SIG_STACK, SCT_SIZE in *; lia]
          end. }
      cbv beta. intros ms2 PO. rewrite ?ESP in PO. unfold I2O_SCT_W_STACK, I2O_SIG_STACK in PO.
      destruct PO as (w0 & w1 & w2 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m2 & hb0 & hb2 & hb3 & hb4
                       & -> & MU2 & WM2 & MI2 & ST2 & HPP2 & Q0 & Q1 & Q2 & Q3 & Q4 & Q5).
      apply evt_done. do 14 eexists. exists m2. eexists. rewrite LEN. split; [reflexivity|].
      split. { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros y Hy; lia. }
      split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|]. split; [replace (P + (47 + sc_extlen x + sn)) with (P + 47 + sc_extlen x + sn) by lia; exact HPP2|].
      change (CB 1%nat hb0) with (CB (Z.to_nat 1) hb0) in Q0. change (CB 32%nat lid) with (CB (Z.to_nat 32) lid) in Q1.
      change (CB 10%nat hb2) with (CB (Z.to_nat 10) hb2) in Q2. change (CB 4%nat hb4) with (CB (Z.to_nat 4) hb4) in Q4.
      pose proof (cb_join2 _ _ _ _ _ _ Q0 Q1 ltac:(lia) ltac:(lia)) as J1.
      replace (P + 33) with (P + (1 + 32)) in Q2 by lia. pose proof (cb_join2 _ _ _ _ _ _ J1 Q2 ltac:(lia) ltac:(lia)) as J2.
      replace (P + 43) with (P + (1 + 32 + 10)) in Q3 by lia. pose proof (cb_join2 _ _ _ _ _ _ J2 Q3 ltac:(lia) ltac:(lia)) as J3.
      replace (P + 43 + sc_extlen x) with (P + (1 + 32 + 10 + sc_extlen x)) in Q4 by lia. pose proof (cb_join2 _ _ _ _ _ _ J3 Q4 ltac:(lia) ltac:(lia)) as J4.
      replace (P + 47 + sc_extlen x) with (P + (1 + 32 + 10 + sc_extlen x + 4)) in Q5 by lia. pose proof (cb_join2 _ _ _ _ _ _ J4 Q5 ltac:(lia) ltac:(lia)) as J5.
      replace (1 + 32 + 10 + sc_extlen x + 4 + sn) with (47 + sc_extlen x + sn) in J5 by lia. exact J5.
    - (* [comment removed for export] *)
      destruct (complete_nv1_facts x VN CPL) as (bq & bn & EB).
      assert (LEN : i2o_sct_len x = bn).
      { unfold i2o_sct_len. replace (sc_version x =? 0) with false by (symmetry; apply Z.eqb_neq; exact VN). rewrite BLBL, EB. reflexivity. }
      rewrite EB in AB. destruct (arr_bytes _ _ _ _ AB) as (BN0 & INB & blob & BLOB & BLEN & _).
      pose proof (SEPLB _ _ INB) as [BQLO SEPB].
      rewrite LEN in HBX, PHI, SEPB.
      eapply evt_cut.
      { eapply (i2o_sct_write_nv1_spec) with (lo := lo) (adr := adr) (x := x) (vs := 0) (PP := bv_unsigned sp + -152) (P := P) (bq := bq) (bn := bn) (blob := blob);
          rewrite ?ESP;
          lazymatch goal with
          | |- stk _ _ _ _ => exact ST
          | |- mem_inv _ _ => exact MI
          | |- rw_cells _ _ (adr (sc_blk x)) _ => exact HX
          | |- sct_ok _ _ => exact OKX
          | |- bytes_at _ _ (adr bq) _ => exact BLOB
          | |- rw_cells _ _ (bv_unsigned sp + -152) _ => exact HPP
          | |- rw_cells _ _ P _ => exact HBX
          | |- _ = _ => first [assumption| reflexivity| lia]
          | |- _ <> _ => exact VN
          | |- _ => first [assumption| unfold GLOBALS_TOP, I2O_SCT_LEN_STACK, SCT_SIZE in *; lia]
          end. }
      cbv beta. intros ms2 PO. rewrite ?ESP in PO. unfold I2O_SCT_LEN_STACK in PO.
      destruct PO as (w0 & w1 & w2 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m2 & -> & MU2 & WM2 & MI2 & ST2 & HPP2 & Q0).
      apply evt_done. do 14 eexists. exists m2. eexists. rewrite LEN. split; [reflexivity|].
      split. { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros y Hy; lia. }
      split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact HPP2| exact Q0].
  Qed.

  Definition wl_post (mC : mem) (FC : bvmap 5 word) (fcC : bv 32) (AD len2 : Z) (j1 j2 : list byte)
      (sC : PState) (stC : ap_st bptr) (OWC : list block) (errvC : word) (boC : Z * Z) (NEW : list block) : machine_state -> Prop :=
    fun ms' => exists (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y23 y24 y28 y29 y30 y31 : word) m' bs,
      ms' = MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -160)) gp (wz RATP) y5 y6 y7 (Z_to_bv 64 (bv_unsigned sp + -64)) (Z_to_bv 64 (bv_unsigned sp + -56))
                    (Z_to_bv 64 (sk_num k)) y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (adr (sk_blk k))) (Z_to_bv 64 (sk_num k)) (Z_to_bv 64 len2) (Z_to_bv 64 0) (Z_to_bv 64 3)
                    y23 y24 e25 e26 e27 y28 y29 y30 y31)
               FC (Z_to_bv 64 INNER_EXIT) fcC None m' (seg_rom ctusegs)
      /\ munch [(lo, bv_unsigned sp + -64); (AD, AD + len2)]%Z mC m' /\ wmono ctusegs mC m' /\ mem_inv ctusegs m'
      /\ EINV (bv_unsigned sp + -160) sC stC m' OWC errvC boC NEW
      /\ rw_cells ctusegs m' (bv_unsigned sp + -64) (frame1 j1 AD) /\ rw_cells ctusegs m' (bv_unsigned sp + -160) (frame2 j2 (AD + len2))
      /\ rw_cells ctusegs m' DER [C8 (Z_to_bv 64 0)] /\ sk_rep m' LB adr k /\ rw_cells ctusegs m' AD [CB (Z.to_nat len2) bs].

  Lemma i2o_sum_app1 : forall d x, i2o_sum (d ++ [x]) = i2o_sum d + (2 + i2o_sct_len x).
  Proof using sp. induction d as [|y d IH]; intros x; cbn [i2o_sum app]; [lia| rewrite IH; lia]. Qed.

  Lemma write_loop : forall rest done acc mO mC sC stC OWC (errvC : word) boC NEW (pd : bptr) AD len2 (FC : bvmap 5 word) (fcC : bv 32)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x28 x29 x30 x31 : word) j1 j2 bsP junk,
    sk_items k = done ++ rest -> rest <> [] -> Forall (sct_ok adr) (sk_items k) -> Forall (fun x => sct_complete x = true) (sk_items k) ->
    acc = 2 + i2o_sum done -> len2 = 2 + i2o_sum (sk_items k) -> len2 <= 65535 ->
    munch [(lo, bv_unsigned sp + -64); (AD, AD + len2)]%Z mO mC -> wmono ctusegs mO mC ->
    EINV (bv_unsigned sp + -160) sC stC mC OWC errvC boC NEW -> In (pd, AD, len2) NEW ->
    rw_cells ctusegs mC (bv_unsigned sp + -64) (frame1 j1 AD) -> rw_cells ctusegs mC (bv_unsigned sp + -160) (frame2 j2 (AD + acc)) ->
    rw_cells ctusegs mC DER [C8 (Z_to_bv 64 0)] -> sk_rep mC LB adr k ->
    rw_cells ctusegs mC AD [CB (Z.to_nat acc) bsP] -> rw_cells ctusegs mC (AD + acc) [CB (Z.to_nat (len2 - acc)) junk] ->
    evt ctusegs (wl_post mO FC fcC AD len2 j1 j2 sC stC OWC errvC boC NEW)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -160)) gp (wz RATP) x5 x6 x7 (Z_to_bv 64 (bv_unsigned sp + -64)) (Z_to_bv 64 (bv_unsigned sp + -56)) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (adr (sk_blk k))) (Z_to_bv 64 (zlength done)) (Z_to_bv 64 acc) (Z_to_bv 64 0) (Z_to_bv 64 3) (Z_to_bv 64 (-1)) x24 e25 e26 e27 x28 x29 x30 x31)
          FC (Z_to_bv 64 INNER_HEAD) fcC None mC (seg_rom ctusegs)).
  Proof using B63 CEIL DERhi DERlo GLO LOB SP16 SPB.
    induction rest as [|x t IH]; intros until junk; intros EQ NE OKALL CALL ACC LEN2 L2B MUO WMO EI HDIN FR1 FR2 HDER SK HBP HBJ; [exfalso; apply NE; reflexivity|].
    pose proof SPR as SPR. unfold I2D_SCT_LIST_STACK, ERR_SET_ERROR_STACK in LOB.
    set (P0 := AD + acc) in *. assert (HP0 : P0 = AD + acc) by reflexivity. clearbody P0.   (* [comment removed for export] *)
    destruct (item_facts _ _ _ _ _ _ _ _ done x t EI SK EQ) as (SAR & DR & IR & NR & RNUM & RDAT & RITEM & REPX & OKX & [XA0 XLO] & XIN).
    pose proof (zlength_ge0 done) as D0.
    pose proof (k_call _ _ _ _ _ _ _ _ EI) as (HEAPC & _ & _ & ST & _ & _ & _ & MI & _).
    pose proof (k_facts _ _ _ _ _ _ _ _ EI) as (_ & _ & BND & FRESH & DJL & DJO & DJN).
    pose proof (BND pd AD len2 ltac:(apply in_app_iff; right; apply in_app_iff; left; exact HDIN)) as (AD0 & _ & ADC & ADI & _).
    pose proof (DJL _ _ _ _ _ _ HDIN (proj1 SK)) as DJS. unfold STACK_SIZE in DJS.
    assert (ALG : adr (sk_blk k) mod 8 = 0 /\ optr adr (sk_data k) mod 8 = 0 /\ adr (sc_blk x) mod 8 = 0).
    { pose proof SK as (HIN & _ & HD & _).
      pose proof (blk_bounds _ _ _ _ _ _ HEAPC ltac:(apply in_app_iff; right; apply in_app_iff; right; exact HIN)) as (_ & _ & _ & _ & A5).
      pose proof (blk_bounds _ _ _ _ _ _ HEAPC ltac:(apply in_app_iff; right; apply in_app_iff; right; exact (proj1 REPX))) as (_ & _ & _ & _ & X5).
      destruct (sk_data k) as [[q0 na]|]; cbn [optr].
      - destruct HD as (HQ & _).
        pose proof (blk_bounds _ _ _ _ _ _ HEAPC ltac:(apply in_app_iff; right; apply in_app_iff; right; exact HQ)) as (_ & _ & _ & _ & D5).
        repeat split; Z.div_mod_to_equations; lia.
      - repeat split; Z.div_mod_to_equations; lia. }
    destruct ALG as (SAL & DAL & XAL).
    assert (OKT : Forall (sct_ok adr) t) by (rewrite EQ in OKALL; apply Forall_app in OKALL; destruct OKALL as [_ OK2]; apply Forall_cons_iff in OK2; exact (proj2 OK2)).
    assert (OKD : Forall (sct_ok adr) done) by (rewrite EQ in OKALL; apply Forall_app in OKALL; exact (proj1 OKALL)).
    assert (CPL : sct_complete x = true) by (apply (proj1 (Forall_forall _ _) CALL); rewrite EQ; apply in_app_iff; right; left; reflexivity).
    pose proof (i2o_sum_ge0 t OKT) as SUMT. pose proof (i2o_sum_ge0 done OKD) as SUMD. pose proof (zlength_ge0 t) as TT0.
    assert (SUMEQ : i2o_sum (sk_items k) = i2o_sum done + (2 + i2o_sct_len x + i2o_sum t)).
    { rewrite EQ. clear. induction done as [|y d IHd]; cbn [i2o_sum app]; [lia| rewrite IHd; lia]. }
    assert (LENX : 0 <= i2o_sct_len x <= 196700).
    { destruct OKX as (VR & HR & GR & SIGP & BLOBP & LOGP & ELR & BLR & EXTP & EXTL & BLBL).
      assert (SL : 0 <= sc_siglen x <= 65535) by (unfold sc_siglen; destruct (sc_sig x) as [[q n]|] eqn:ES; [pose proof (SIGP q n eq_refl); lia| lia]).
      unfold i2o_sct_len. destruct (sc_version x =? 0); lia. }
    assert (LEN : sk_num k = zlength done + 1 + zlength t) by (unfold sk_num; rewrite EQ, zlength_app_l; unfold zlength; cbn [length]; lia).
    unfold frame2 in FR2. unfold INNER_HEAD. unfold STACK_SIZE in SAR. unfold SKO_DATA in RDAT.
    pose proof (munch_refl [(lo, bv_unsigned sp + -64); (AD, AD + len2)]%Z mC) as MU. pose proof (wmono_refl ctusegs mC) as WM.
    assert (OWN : Forall (own_iv sp lo XC NEW) [(lo, bv_unsigned sp + -64); (AD, AD + len2)]%Z).
    { constructor; [left; cbn; lia| constructor; [right; right; exists pd, AD, len2; cbn [fst snd]; split; [exact HDIN| lia]| constructor]]. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -160)) = bv_unsigned sp + -160) by (apply unsigned_lit; lia).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep. sfalse. zstep. zstep. ub. zstep. zstep. zstep. zstep.
    eapply evt_cut.
    { eapply (OPENSSL_sk_value_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FC fcC _ lo (adr (sk_blk k)) (sk_num k) (optr adr (sk_data k)) (zlength done) (adr (sc_blk x)));
        [rewrite ESP; exact ST| assumption| unfold GLOBALS_TOP; lia| rewrite ESP; lia| exact SAR| exact DR| exact SAL| exact DAL| exact RNUM| exact RDAT| exact IR| lia| exact RITEM| reflexivity| reflexivity]. }
    unfold nid_post. cbv beta. intros ms1 PO. rewrite ?ESP in PO.
    destruct PO as (v5 & v6 & v7 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m1 & -> & MU1 & WM1 & MI1 & ST1).
    replace (ret_pc (Z_to_bv 64 0x19d19c)) with (Z_to_bv 64 0x19d19c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    xmu FR1 MU1 WM1. xmu FR2 MU1 WM1. xmu HDER MU1 WM1. xmu HBP MU1 WM1. xmu HBJ MU1 WM1.
    apply (fun H0 => ro_cells_transport _ _ _ _ _ _ H0 MU1) in RNUM; [| cbn; lia].
    assert (MU' : munch [(lo, bv_unsigned sp + -64); (AD, AD + len2)]%Z mC m1).
    { eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU1]]; unfold sub_fp; cbn [outside]; intros y Hy; lia. }
    assert (WM' : wmono ctusegs mC m1) by (eapply wmono_trans; [exact WM| exact WM1]).
    assert (MUO' : munch [(lo, bv_unsigned sp + -64); (AD, AD + len2)]%Z mO m1).
    { eapply munch_trans; [exact MUO| eapply munch_weaken; [| exact MU1]]; unfold sub_fp; cbn [outside]; intros y Hy; lia. }
    assert (WMO' : wmono ctusegs mO m1) by (eapply wmono_trans; [exact WMO| exact WM1]).
    clear MU WM MU1 WM1 MI ST RDAT RITEM MUO WMO. rename MU' into MU. rename WM' into WM. rename MI1 into MI. rename ST1 into ST. rename MUO' into MUO. rename WMO' into WMO.
    assert (EI1 : EINV (bv_unsigned sp + -160) sC stC m1 OWC errvC boC NEW) by (eapply k_munch; [exact EI| exact MU| exact WM| exact MI| exact ST| lia| exact OWN]).
    assert (SK1 : sk_rep m1 LB adr k) by (eapply sk_keep; [exact EI| exact SK| exact MU| exact WM| exact OWN]).
    assert (REPX1 : sct_rep m1 LB adr x).
    { destruct (item_facts _ _ _ _ _ _ _ _ done x t EI1 SK1 EQ) as (_ & _ & _ & _ & _ & _ & _ & R & _). exact R. }
    (* [comment removed for export] *)
    replace (len2 - acc) with (2 + (len2 - acc - 2)) in HBJ by lia.
    pose proof (cb_split2 m1 P0 2 (len2 - acc - 2) junk HBJ ltac:(lia) ltac:(lia)) as [HB2 HBR]. clear HBJ.
    replace (len2 - acc - 2) with (i2o_sct_len x + (len2 - acc - 2 - i2o_sct_len x)) in HBR by lia.
    pose proof (cb_split2 m1 (P0 + 2) (i2o_sct_len x) (len2 - acc - 2 - i2o_sct_len x) _ HBR ltac:(lia) ltac:(lia)) as [HBX HBR']. clear HBR.
    replace (P0 + 2 + i2o_sct_len x) with (AD + (acc + 2 + i2o_sct_len x)) in HBR' by lia.
    (* [comment removed for export] *)
    pose proof (cells_at_wf _ _ _ _ (proj1 HB2)) as [WF2 _]. cbn in WF2.
    destruct (take (Z.to_nat 2) junk) as [|b0 [|b1 [|b2 br]]] eqn:EJ; cbn [length] in WF2; try lia. clear WF2 EJ.
    assert (HS2 : rw_cells ctusegs m1 P0 [C1 b0; C1 b1]).
    { eapply rw_cells_recast; [exact HB2| cbn; repeat split; reflexivity| reflexivity| reflexivity]. }
    clear HB2.
    (* [comment removed for export] *)
    zstep. zstep.
    pose proof (proj1 (rw_cells_app m1 _ [CB 8%nat j2] _) FR2) as [FRJ FR2a]. clear FR2. cbn [cells_size csize Nat.add] in FR2a.
    replace (bv_unsigned sp + -160 + Z.of_nat 8) with (bv_unsigned sp + -152) in FR2a by lia.
    pose proof (proj1 (rw_cells_app m1 _ [C8 (Z_to_bv 64 (P0 + 2))] _) FR2a) as [HPP FR2']. clear FR2a. cbn [cells_size csize Nat.add] in FR2'.
    replace (bv_unsigned sp + -152 + Z.of_nat 8) with (bv_unsigned sp + -144) in FR2' by lia.
    try replace (bv_unsigned sp + -64 + -96) with (bv_unsigned sp + -160) by lia.
    eapply evt_cut.
    { eapply item_write with (x := x) (P := P0 + 2) (pd := pd) (AD := AD) (len2 := len2); first [eassumption| lia]. }
    cbv beta. intros ms2 PO.
    destruct PO as (w0 & w1 & w2 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m2 & bsX & -> & MU2 & WM2 & MI2 & ST2 & HPP2 & HBX2).
    replace (ret_pc (Z_to_bv 64 0x19d1a4)) with (Z_to_bv 64 0x19d1a4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    xmu FR1 MU2 WM2. xmu FRJ MU2 WM2. xmu FR2' MU2 WM2. xmu HDER MU2 WM2. xmu HBP MU2 WM2. xmu HS2 MU2 WM2. xmu HBR' MU2 WM2.
    apply (fun H0 => ro_cells_transport _ _ _ _ _ _ H0 MU2) in RNUM; [| cbn; lia].
    assert (MU' : munch [(lo, bv_unsigned sp + -64); (AD, AD + len2)]%Z mC m2).
    { eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros y Hy; lia. }
    assert (WM' : wmono ctusegs mC m2) by (eapply wmono_trans; [exact WM| exact WM2]).
    assert (MUO' : munch [(lo, bv_unsigned sp + -64); (AD, AD + len2)]%Z mO m2).
    { eapply munch_trans; [exact MUO| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros y Hy; lia. }
    assert (WMO' : wmono ctusegs mO m2) by (eapply wmono_trans; [exact WMO| exact WM2]).
    clear MU WM MU2 WM2 MI ST EI1 SK1 REPX1 HPP HBX MUO WMO. rename MU' into MU. rename WM' into WM. rename MI2 into MI. rename ST2 into ST. rename MUO' into MUO. rename WMO' into WMO.
    assert (FR2 : rw_cells ctusegs m2 (bv_unsigned sp + -160) (frame2 j2 (P0 + 2 + i2o_sct_len x))).
    { unfold frame2. apply (proj2 (rw_cells_app m2 _ [CB 8%nat j2] _)). split; [exact FRJ|].
      cbn [cells_size csize Nat.add]. replace (bv_unsigned sp + -160 + Z.of_nat 8) with (bv_unsigned sp + -152) by lia.
      apply (proj2 (rw_cells_app m2 _ [C8 (Z_to_bv 64 (P0 + 2 + i2o_sct_len x))] _)). split; [exact HPP2|].
      cbn [cells_size csize Nat.add]. replace (bv_unsigned sp + -152 + Z.of_nat 8) with (bv_unsigned sp + -144) by lia. exact FR2'. }
    clear HPP2 FR2' FRJ. unfold frame2 in FR2.
    (* [comment removed for export] *)
    zstep. sfalse. ub. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. rewrite ?(swrap32_small (zlength done + 1)) by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2' end.
    eapply evt_cut.
    { eapply (OPENSSL_sk_num_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FC fcC _ lo (adr (sk_blk k)) (sk_num k));
        [rewrite ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ESP; lia| exact SAR| exact SAL| exact RNUM| lia| reflexivity]. }
    unfold nid_post. cbv beta. intros ms3 PO. rewrite ?ESP in PO.
    destruct PO as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m3 & -> & MU3 & WM3 & MI3 & ST3).
    replace (ret_pc (Z_to_bv 64 0x19d1e8)) with (Z_to_bv 64 0x19d1e8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    xmu FR1 MU3 WM3. xmu FR2 MU3 WM3. xmu HDER MU3 WM3. xmu HBP MU3 WM3. xmu HS2 MU3 WM3. xmu HBX2 MU3 WM3. xmu HBR' MU3 WM3.
    assert (MU' : munch [(lo, bv_unsigned sp + -64); (AD, AD + len2)]%Z mC m3).
    { eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU3]]; unfold sub_fp; cbn [outside]; intros y Hy; lia. }
    assert (WM' : wmono ctusegs mC m3) by (eapply wmono_trans; [exact WM| exact WM3]).
    assert (MUO' : munch [(lo, bv_unsigned sp + -64); (AD, AD + len2)]%Z mO m3).
    { eapply munch_trans; [exact MUO| eapply munch_weaken; [| exact MU3]]; unfold sub_fp; cbn [outside]; intros y Hy; lia. }
    assert (WMO' : wmono ctusegs mO m3) by (eapply wmono_trans; [exact WMO| exact WM3]).
    clear MU WM MU3 WM3 MI ST MUO WMO RNUM. rename MU' into MU. rename WM' into WM. rename MI3 into MI. rename ST3 into ST. rename MUO' into MUO. rename WMO' into WMO.
    assert (EI3 : EINV (bv_unsigned sp + -160) sC stC m3 OWC errvC boC NEW) by (eapply k_munch; [exact EI| exact MU| exact WM| exact MI| exact ST| lia| exact OWN]).
    assert (SK3 : sk_rep m3 LB adr k) by (eapply sk_keep; [exact EI| exact SK| exact MU| exact WM| exact OWN]).
    (* [comment removed for export] *)
    apply cells_blob in HS2. cbn [cells_size csize Nat.add] in HS2.
    lazymatch type of HS2 with rw_cells _ _ _ [CB _ ?l] => change (rw_cells ctusegs m3 P0 [CB (Z.to_nat 2) l]) in HS2 end.
    subst P0.
    pose proof (cb_join2 _ _ _ _ _ _ HBP HS2 ltac:(lia) ltac:(lia)) as J1.
    replace (AD + acc + 2) with (AD + (acc + 2)) in HBX2 by lia.
    pose proof (cb_join2 _ _ _ _ _ _ J1 HBX2 ltac:(lia) ltac:(lia)) as J2. clear J1 HBP HS2 HBX2.
    (* [comment removed for export] *)
    zstep. destruct t as [|y t'].
    + (* [comment removed for export] *)
      replace (zlength (@nil (sctr bptr))) with 0 in LEN by reflexivity. rewrite Z.add_0_r in LEN. cbn [i2o_sum] in SUMEQ.
      sfalse. apply evt_done. unfold wl_post.
      pose proof (cb_join2 _ _ _ _ _ _ J2 HBR' ltac:(lia) ltac:(lia)) as J3.
      replace (acc + 2 + i2o_sct_len x + (len2 - acc - 2 - i2o_sct_len x)) with len2 in J3 by lia.
      replace (zlength done + 1) with (sk_num k) by lia. replace (acc + i2o_sct_len x + 2) with len2 by lia.
      replace (AD + acc + 2 + i2o_sct_len x) with (AD + len2) in FR2 by lia.
      do 17 eexists. exists m3. eexists. split; [reflexivity|].
      split; [exact MUO|]. split; [exact WMO|]. split; [exact MI|]. split; [exact EI3|].
      split; [exact FR1|]. split; [exact FR2|]. split; [exact HDER|]. split; [exact SK3| exact J3].
    + (* [comment removed for export] *)
      assert (T1 : 1 <= zlength (y :: t')) by (unfold zlength; cbn [length]; lia).
      strue.
      replace (zlength done + 1) with (zlength (done ++ [x])) by (rewrite zlength_app_l; unfold zlength; cbn [length]; lia).
      replace (acc + i2o_sct_len x + 2) with (acc + 2 + i2o_sct_len x) by lia.
      replace (AD + acc + 2 + i2o_sct_len x) with (AD + (acc + 2 + i2o_sct_len x)) in FR2 by lia.
      replace (len2 - acc - 2 - i2o_sct_len x) with (len2 - (acc + 2 + i2o_sct_len x)) in HBR' by lia.
      eapply (IH (done ++ [x]) (acc + 2 + i2o_sct_len x)); try eassumption.
      * rewrite EQ, <- app_assoc. reflexivity.
      * discriminate.
      * rewrite i2o_sum_app1. lia.
  Qed.
  End Act.
End Proofs.
End WithCeiling0.
