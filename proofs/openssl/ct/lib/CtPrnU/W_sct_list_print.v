(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface RAligned_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG PrintfModel PrintfModelX ApBase ApState ApBridge CtSizes CtWire CtTime CtModel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Printf_apfmt Printf_ctfmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Printf_lib F_pop_arg F_printf_iface F_vsnprintf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac ApCells ApRepDefs ApRep ApWalkTac ApErrKit ApIface W_bio_push W_bio_write W_bio_printf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctDefs W_sct_list_free SctRep W_sct_leaves W_sk_leaves.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnU Require Import PrnFmt W_bio_hex_string W_sct_print_nv1 PrnSct PrnKit PrnTimeIface PrnSctV1 W_sct_print.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition SCT_LIST_PRINT : Z := 0x19dc28.
Definition SCT_LIST_LOOP : Z := 0x19dc84.
Definition SCT_LIST_EPI : Z := 0x19dccc.
(* [comment removed for export] *)
Definition A_SEP : Z := 0x2a387.
Definition SLK_SEP : list Z := [99; 114; 121; 112; 116; 111; 47].
(* [comment removed for export] *)
Definition SCT_LIST_PRINT_STACK (TSTK : Z) : Z := 80 + SCT_PRINT_STACK TSTK.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Lemma sep_at : forall m, mem_inv ctusegs m -> bytes_at ctusegs m A_SEP (zb [10] ++ Z_to_bv 8 0 :: zb SLK_SEP).
Proof.
  intros m MI.
  lazymatch goal with |- bytes_at _ _ _ ?bs =>
    let bs' := eval cbv in bs in
    change bs with bs';
    apply (ro_cells_bytes m A_SEP (length bs') bs');
    apply (ro_cells_image ctusegs m A_SEP bs' MI); [vm_compute; reflexivity| unfold A_SEP; lia| unfold A_SEP; cbn; lia]
  end.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma pcok_sep : forall m lo q (a3 a4 a5 a6 a7 : word), mem_inv ctusegs m -> STATIC_SPLIT <= lo ->
  printf_call_ok m lo q A_C10 FMT_C10 [Z_to_bv 64 A_SEP; a3; a4; a5; a6; a7] [PA_s [10]] [10].
Proof.
  intros m lo q a3 a4 a5 a6 a7 MI SL.
  eapply (pcok_C10 m lo q A_C10 A_SEP [10] (zb SLK_SEP)); [exact MI| exact SL| apply fmt_C10_at; exact MI| unfold A_C10; lia| unfold A_C10, STATIC_SPLIT; lia
    | apply sep_at; exact MI| constructor; [lia| apply Forall_nil]| reflexivity| unfold A_SEP; lia| unfold A_SEP, STATIC_SPLIT; change (zlength [10]) with 1; lia| change (zlength [10]) with 1; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma arr_rep_agree : forall P m m' L adr o,
  agree_on P m m' -> (forall q n a, o = Some (q, n) -> adr q <= a < adr q + n -> P a) -> arr_rep m L adr o -> arr_rep m' L adr o.
Proof.
  intros P m m' L adr [[q n]|] AG HP H; cbn in *; [| exact I]. destruct H as (Hn & HL & bs & HB). split; [exact Hn|]. split; [exact HL|]. exists bs.
  eapply rw_cells_agree; [exact AG| exact HB|]. intros a Ha. cbn in Ha. rewrite Nat.add_0_r, Z2Nat.id in Ha by lia. eapply HP; [reflexivity| lia].
Qed.

Lemma sct_rep_agree : forall P m m' L adr x,
  agree_on P m m' -> (forall b a, In b (sct_blocks adr x) -> blk_addr b <= a < blk_addr b + blk_size b -> P a) -> sct_rep m L adr x -> sct_rep m' L adr x.
Proof.
  intros P m m' L adr x AG HP (H1 & H2 & H3 & H4 & H5 & H6 & REST).
  assert (BL : forall b, (In b (oblk adr (osz32 (sc_logid x))) \/ In b (oblk adr (sc_ext x)) \/ In b (oblk adr (sc_sig x)) \/ In b (oblk adr (sc_blob x))
                          \/ b = (sc_blk x, adr (sc_blk x), SCT_SIZE)) -> In b (sct_blocks adr x)).
  { intros b Hb. unfold sct_blocks. rewrite !in_app_iff. cbn. destruct Hb as [Hb|[Hb|[Hb|[Hb| ->]]]]; tauto. }
  split; [exact H1|]. split.
  { eapply rw_cells_agree; [exact AG| exact H2|]. intros a Ha. apply (HP (sc_blk x, adr (sc_blk x), SCT_SIZE)); [apply BL; right; right; right; right; reflexivity|].
    cbn. rewrite sct_cells_size in Ha. unfold SCT_SIZE in *. lia. }
  split; [eapply arr_rep_agree; [exact AG| intros q n a Ho Ha; apply (HP (q, adr q, n)); [apply BL; left; rewrite Ho; left; reflexivity| cbn; lia]| exact H3]|].
  split; [eapply arr_rep_agree; [exact AG| intros q n a Ho Ha; apply (HP (q, adr q, n)); [apply BL; right; left; rewrite Ho; left; reflexivity| cbn; lia]| exact H4]|].
  split; [eapply arr_rep_agree; [exact AG| intros q n a Ho Ha; apply (HP (q, adr q, n)); [apply BL; right; right; left; rewrite Ho; left; reflexivity| cbn; lia]| exact H5]|].
  split; [eapply arr_rep_agree; [exact AG| intros q n a Ho Ha; apply (HP (q, adr q, n)); [apply BL; right; right; right; left; rewrite Ho; left; reflexivity| cbn; lia]| exact H6]|].
  exact REST.
Qed.

(* [comment removed for export] *)
Definition sk_allblocks (adr : bptr -> Z) (k : skr bptr) : list block :=
  scts_blocks adr (sk_items k) ++ dblk adr (sk_data k) ++ [(sk_blk k, adr (sk_blk k), STACK_SIZE)].

Lemma sk_allblocks_in : forall m L adr k b, sk_rep m L adr k -> In b (sk_allblocks adr k) -> In b L.
Proof.
  intros m L adr k b (HIN & _ & HD & HF & _) Hb. unfold sk_allblocks in Hb. rewrite !in_app_iff in Hb.
  assert (ITEMS : forall l, Forall (sct_rep m L adr) l -> In b (scts_blocks adr l) -> In b L).
  { intros l HFl. induction HFl as [|x t Hx HFt IH]; intros Hbl; [destruct Hbl|]. cbn in Hbl. apply in_app_iff in Hbl.
    destruct Hbl as [Hbl|Hbl]; [exact (sct_rep_blocks_in _ _ _ _ Hx _ Hbl)| exact (IH Hbl)]. }
  destruct Hb as [Hb|[Hb|Hb]].
  - exact (ITEMS _ HF Hb).
  - destruct (sk_data k) as [[q na]|]; cbn in Hb; [| destruct Hb]. destruct Hb as [<-|[]]. exact (proj1 HD).
  - destruct Hb as [<-|[]]. exact HIN.
Qed.

Lemma sk_rep_agree : forall P m m' L adr k,
  agree_on P m m' -> (forall b a, In b (sk_allblocks adr k) -> blk_addr b <= a < blk_addr b + blk_size b -> P a) -> sk_rep m L adr k -> sk_rep m' L adr k.
Proof.
  intros P m m' L adr k AG HP (HIN & (sorted & SR & HC) & HD & HF & ND).
  split; [exact HIN|]. split.
  { exists sorted. split; [exact SR|]. eapply rw_cells_agree; [exact AG| exact HC|]. intros a Ha. rewrite sk_cells_size in Ha.
    apply (HP (sk_blk k, adr (sk_blk k), STACK_SIZE)); [unfold sk_allblocks; rewrite !in_app_iff; right; right; left; reflexivity| cbn; exact Ha]. }
  split.
  { destruct (sk_data k) as [[q na]|] eqn:ED; [| exact HD]. destruct HD as (H1 & H2 & H3 & jb & H4 & H5). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    exists jb. split; [exact H4|]. eapply rw_cells_agree; [exact AG| exact H5|]. intros a Ha. rewrite data_block_size in Ha.
    apply (HP (q, adr q, 8 * na)); [unfold sk_allblocks; rewrite ED, !in_app_iff; right; left; left; reflexivity| cbn]. unfold sk_num in *. lia. }
  split; [| exact ND].
  apply Forall_forall. intros x Hx. eapply sct_rep_agree; [exact AG| | exact (proj1 (Forall_forall _ _) HF x Hx)].
  intros b a Hb Ha. apply (HP b); [| exact Ha]. unfold sk_allblocks. rewrite !in_app_iff. left.
  clear - Hx Hb. induction (sk_items k) as [|y t IH]; [destruct Hx|]. cbn. apply in_app_iff. destruct Hx as [<-|Hx]; [left; exact Hb| right; exact (IH Hx)].
Qed.

(* [comment removed for export] *)
Lemma sk_rep_lx : forall s OW LB m m' adr k SP,
  RHEAP s (OW ++ LB) m -> sk_rep m LB adr k -> lx_pres LB SP LIBW_AP m m' -> sk_rep m' LB adr k.
Proof.
  intros s OW LB m m' adr k SP HEAP SK LX. eapply sk_rep_agree; [apply (agree_of_lx_pres _ _ _ _ _ LX)| | exact SK].
  intros [[q A] n] a Hb Ha. cbn [blk_addr blk_size fst snd] in Ha. pose proof (sk_allblocks_in _ _ _ _ _ SK Hb) as HbL.
  pose proof (blk_bounds _ _ _ _ _ _ HEAP ltac:(apply in_app_iff; right; exact HbL)) as (B1 & B2 & B3 & B4 & B5).
  split; [unfold LIBW_AP; cbn [rin_ivs fst snd]; lia|]. right. left. exists (q, A, n). split; [exact HbL| cbn; exact Ha].
Qed.

Lemma sk_rep_munch : forall s OW LB m m' adr k (pbio : bptr) out lo q,
  RHEAP s (OW ++ LB) m -> sk_rep m LB adr k -> In (pbio, out, BIO_SIZE) OW -> alloc_ceiling <= lo ->
  munch [(lo, q); (out, out + 128)] m m' -> wmono ctusegs m m' -> sk_rep m' LB adr k.
Proof.
  intros s OW LB m m' adr k pbio out lo q HEAP SK HBIN CEIL MU WM. eapply sk_rep_agree; [apply (agree_on_of_munch _ _ _ MU WM)| | exact SK].
  intros [[qb A] n] a Hb Ha. cbn [blk_addr blk_size fst snd] in Ha. pose proof (sk_allblocks_in _ _ _ _ _ SK Hb) as HbL.
  pose proof (blk_bounds _ _ _ _ _ _ HEAP ltac:(apply in_app_iff; right; exact HbL)) as (B1 & B2 & B3 & B4 & B5).
  pose proof (LH_nodup _ _ _ HEAP) as ND. rewrite map_app in ND.
  assert (NE : qb <> pbio).
  { intros ->. eapply (NoDup_app_disjoint _ _ pbio ND); [apply in_map_iff; exists (pbio, out, BIO_SIZE); split; [reflexivity| exact HBIN]|].
    apply in_map_iff. exists (pbio, A, n). split; [reflexivity| exact HbL]. }
  pose proof (blk_disjoint _ _ _ _ _ _ _ _ _ HEAP ltac:(apply in_app_iff; right; exact HbL) ltac:(apply in_app_iff; left; exact HBIN) NE) as DJ.
  unfold BIO_SIZE in DJ. cbn. lia.
Qed.

Lemma sct_rep_mono : forall m L L' adr x, (forall b, In b L -> In b L') -> sct_rep m L adr x -> sct_rep m L' adr x.
Proof.
  intros m L L' adr x HL (H1 & H2 & H3 & H4 & H5 & H6 & REST).
  assert (AR : forall o, arr_rep m L adr o -> arr_rep m L' adr o) by (intros [[q n]|] H; cbn in *; [| exact I]; destruct H as (A1 & A2 & A3); split; [exact A1| split; [apply HL; exact A2| exact A3]]).
  split; [apply HL; exact H1|]. split; [exact H2|]. split; [apply AR; exact H3|]. split; [apply AR; exact H4|]. split; [apply AR; exact H5|]. split; [apply AR; exact H6|]. exact REST.
Qed.

(* [comment removed for export] *)
Lemma ap_pre_of_pn_lit : forall s st m OW LB E bo q lo B errv canary stack,
  pn_pre s st m OW LB E bo [] q lo B errv canary -> q mod 16 = 0 -> 0 <= q < 2^64 -> lo <= q - stack ->
  ap_pre s st m OW LB E bo (Z_to_bv 64 q) lo B errv canary stack.
Proof.
  intros until stack. intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & LO & A12 & A13 & A14) Q16 QR LOS. cbn [app] in A1.
  unfold ap_pre. rewrite errno_addr_lit. rewrite (unsigned_lit q) by lia. repeat (split; [first [assumption| lia]|]). exact Q16.
Qed.

Lemma pn_pre_of_ap_lit : forall s st m OW LB E bo q lo B errv canary stack,
  ap_pre s st m OW LB E bo (Z_to_bv 64 q) lo B errv canary stack -> 0 <= stack -> 0 <= q < 2^64 ->
  pn_pre s st m OW LB E bo [] q lo B errv canary.
Proof.
  intros until stack. intros PRE ST0 QR. destruct (pn_pre_of_ap _ _ _ _ _ _ _ _ _ _ _ _ _ PRE ST0) as (PN & _ & _). rewrite (unsigned_lit q) in PN by lia. exact PN.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SCT_LIST_print_spec (TSTK : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo B : Z) (errv canary : word) (K : list block)
         (adr : bptr -> Z) (k : skr bptr) (pbio : bptr) (out pv nw : Z),
    ap_pre s st m OW LB E bo sp lo B errv canary (SCT_LIST_PRINT_STACK TSTK) -> tp = wz RATP -> frm0 fc ->
    a0 = wz (adr (sk_blk k)) -> a1 = wz out -> a2 = wz 4 -> a3 = wz A_SEP -> a4 = wz 0 ->
    sk_rep m LB adr k ->
    In (pbio, out, BIO_SIZE) OW -> ~ In pbio (es_ids st ++ env_ids E) ->
    rw_cells ctusegs m out (bio_null_cells NULL_METHOD pv nw) -> 0 <= nw < 2^64 ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) -> (forall b, In b K -> blk_id b <> pbio) ->
    implM ctusegs (interp (ap_embed (sct_list_print k st))) s
          (ap_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s OW LB E lo B canary m K (sct_print_res st OW out pv))
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz SCT_LIST_PRINT) fc None m (seg_rom ctusegs)).

Section Proofs.
  Variable TSTK : Z.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Hypothesis T_ADJ_OK : gentime_adj_ok_stmt TSTK.
  Hypothesis T_ADJ_FAIL : gentime_adj_fail_stmt TSTK.
  Hypothesis T_SETSTR_OK : gentime_setstr_ok_stmt TSTK.
  Hypothesis T_SETSTR_FAIL : gentime_setstr_fail_stmt TSTK.
  Hypothesis T_PRINT : gentime_print_stmt TSTK.

  Section Act.
  (* [comment removed for export] *)
  Variables (sp gp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env).
  Variables (lo B : Z) (canary : word) (K : list block) (adr : bptr -> Z) (k : skr bptr) (pbio : bptr) (out pv : Z).
  Variables (vra v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : word).
  Hypothesis LOB : lo <= bv_unsigned sp - 80 - (96 + Z.max 8320 TSTK).
  Hypothesis SPB63 : bv_unsigned sp <= B /\ B < 2^63.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis HBIN : In (pbio, out, BIO_SIZE) OW.
  Hypothesis NI : ~ In pbio (es_ids st ++ env_ids E).
  Hypothesis KOW : forall b, In b K -> In b OW.
  Hypothesis KID : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).
  Hypothesis KNB : forall b, In b K -> blk_id b <> pbio.

  Definition lframe : list cell := [C8 v24; C8 v23; C8 v22; C8 v21; C8 v20; C8 v19; C8 v18; C8 v9; C8 v8; C8 vra].
  Local Notation POST := (ap_post vra sp gp v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 F fc s OW LB E lo B canary m K (sct_print_res st OW out pv)).

  Lemma kf : frozen (forall b, In b K -> In b ([] ++ OW ++ LB) /\ blk_id b <> pbio).
  Proof using KNB KOW. intros b Hb. split; [cbn [app]; apply in_app_iff; left; apply KOW; exact Hb| apply KNB; exact Hb]. Qed.

  (* [comment removed for export] *)
  Lemma lp_open : forall sC mC boC errvC, pn_pre sC st mC OW LB E boC [] (bv_unsigned sp + -80) lo B errvC canary ->
    RHEAP sC (OW ++ LB) mC /\ ap_state st mC OW E boC /\ stk ctusegs mC lo (bv_unsigned sp + -80) /\ alloc_ceiling <= lo /\ 3493888 <= lo
    /\ ssp_cells mC canary /\ mem_inv ctusegs mC /\ null_meth_cells mC
    /\ 0 < out /\ out + 128 <= alloc_ceiling /\ (out + 128 <= 0x10000 \/ 0x355000 <= out)
    /\ bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80 /\ 0 <= bv_unsigned sp < 2^64.
  Proof using HBIN LOB.
    intros sC mC boC errvC (HEAP & AS & _ & _ & _ & _ & _ & ST & CEIL & GLO & _ & _ & SSP & MI). cbn [app] in HEAP.
    pose proof AS as (_ & IMG & _). unfold GLOBALS_TOP in GLO.
    pose proof (blk_bounds _ _ _ _ _ _ HEAP ltac:(apply in_app_iff; left; exact HBIN)) as (B1 & B2 & B3 & B4 & B5). unfold BIO_SIZE in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    repeat (split; [first [assumption| apply null_meth_of_img; assumption| lia]|]).
    split; [apply unsigned_lit; lia| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma lp_finish : forall sC mC (errvC : word) boC (FcC : bvmap 5 word) (fcC : bv 32) nwC
      (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x22 x23 x24 t3 t4 t5 t6 : word),
    pn_pre sC st mC OW LB E boC [] (bv_unsigned sp + -80) lo B errvC canary -> pn_acc LB (bv_unsigned sp) K s sC m mC ->
    rw_cells ctusegs mC (bv_unsigned sp + -80) lframe -> 0 <= nwC < 2^64 -> rw_cells ctusegs mC out (bio_null_cells NULL_METHOD pv nwC) ->
    frm0 fcC -> sp_F F FcC ->
    evt ctusegs (POST (tt, st) sC)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp (wz RATP) t0 t1 t2 sp (Z_to_bv 64 0) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 A_SEP) (Z_to_bv 64 4) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sk_blk k))) x22 x23 x24 v25 v26 v27 t3 t4 t5 t6)
          FcC (Z_to_bv 64 SCT_LIST_EPI) fcC None mC (seg_rom ctusegs)).
  Proof using HBIN KID KOW LOB SP16 SPB63.
    intros until t6. intros PN ACC FR NW HB FRM HFC.
    pose proof (lp_open _ _ _ _ PN) as (HEAP & AS & ST & CEIL & GLO & SSP & MI & NM & OB0 & OB1 & OB2 & ESP & SPR).
    unfold lframe in FR. unfold SCT_LIST_EPI.
    pose proof (munch_refl [(lo, bv_unsigned sp + -80)] mC) as MU. pose proof (wmono_refl ctusegs mC) as WM.
    do 10 zstep.
    zstep. eapply stk_release in FR; [| exact ST| lia]. clear ST. rename FR into ST. cbn [cells_size csize Nat.add] in ST.
    replace (bv_unsigned sp + -80 + Z.of_nat 80) with (bv_unsigned sp) in ST by lia.
    zstep.
    apply evt_done. destruct ACC as (LX & KP & SO & FA). destruct PN as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _ & A9 & A10 & _ & A12 & A13 & _). cbn [app] in A1.
    unfold ap_post. do 15 eexists. exists FcC, fcC, mC, OW, errvC, boC. split; [unfold MallocRep.wz; reflexivity|].
    split; [exact FRM|]. split; [exact HFC|].
    split. { unfold ap_pre. rewrite errno_addr_lit. repeat (split; [first [assumption| lia]|]). exact SP16. }
    split; [exact LX|]. split; [exact SO|]. split; [exact FA|].
    split; [split; [exact KOW| split; [intros b Hb Hin; apply (KID b Hb); apply in_app_iff; left; exact Hin| exact KP]]|].
    split; [reflexivity|]. split; [reflexivity|]. exists nwC. split; [exact NW| exact HB].
  Qed.

  (* [comment removed for export] *)
  Lemma lp_item : forall sC mC done x t,
    RHEAP sC (OW ++ LB) mC -> alloc_ceiling <= lo -> sk_rep mC LB adr k -> sk_items k = done ++ x :: t ->
    let SA := adr (sk_blk k) in let D := optr adr (sk_data k) in let n := sk_num k in let i := zlength done in
    (0 < SA /\ SA + STACK_SIZE <= lo) /\ (0 < D /\ D + 8 * n <= lo) /\ SA mod 8 = 0 /\ D mod 8 = 0 /\ 0 <= i < n /\ n < 2^23
    /\ ro_cells ctusegs mC SA [C4 (wz n)] /\ ro_cells ctusegs mC (SA + SKO_DATA) [C8 (wz D)]
    /\ ro_cells ctusegs mC (D + 8 * i) [C8 (wz (adr (sc_blk x)))]
    /\ sct_rep mC (OW ++ LB) adr x /\ ~ In pbio (map blk_id (sct_blocks adr x)).
  Proof using HBIN LOB.
    intros sC mC done x t HEAP CEILLO SK EQ. cbn zeta.
    pose proof SK as (HIN & (sorted & SR & HC) & HD & HFI & ND).
    pose proof (blk_bounds _ _ _ _ _ _ HEAP ltac:(apply in_app_iff; right; exact HIN)) as (B1 & B2 & B3 & B4 & B5). unfold STACK_SIZE in *.
    assert (LEN : sk_num k = zlength done + 1 + zlength t) by (unfold sk_num; rewrite EQ, zlength_app'; unfold zlength; cbn [length]; lia).
    pose proof (zlength_nonneg'' done) as D0. pose proof (zlength_nonneg'' t) as T0.
    destruct (sk_data k) as [[q na]|] eqn:ED; cbn [optr].
    2:{ exfalso. rewrite HD in EQ. destruct done; discriminate. }
    destruct HD as (HQ & HNA & HNA2 & jb & HJ & HDB).
    pose proof (blk_bounds _ _ _ _ _ _ HEAP ltac:(apply in_app_iff; right; exact HQ)) as (C1 & C2 & C3 & C4 & C5).
    split; [lia|]. split; [lia|]. split; [clear - B5; Z.div_mod_to_equations; lia|]. split; [clear - C5; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|].
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
      pose proof (data_block_nth mC adr (adr q) (sk_items k) jb (length done) x HDB ltac:(rewrite EQ; rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity)) as Y.
      unfold ptrw in Y. exact Y. }
    assert (HX : sct_rep mC LB adr x) by (apply (proj1 (Forall_forall _ _) HFI); rewrite EQ; apply in_app_iff; right; left; reflexivity).
    split; [eapply sct_rep_mono; [| exact HX]; intros b Hb; apply in_app_iff; right; exact Hb|].
    pose proof (LH_nodup _ _ _ HEAP) as NDL. rewrite map_app in NDL.
    intros Hin. apply in_map_iff in Hin. destruct Hin as (b & Eb & Hb).
    eapply (NoDup_app_disjoint _ _ pbio NDL); [apply in_map_iff; exists (pbio, out, BIO_SIZE); split; [reflexivity| exact HBIN]|].
    rewrite <- Eb. apply in_map. exact (sct_rep_blocks_in _ _ _ _ HX _ Hb).
  Qed.

  (* [comment removed for export] *)
  Lemma lp_loop : forall t x done sC mC (errvC : word) boC (FcC : bvmap 5 word) (fcC : bv 32) nwC
      (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    sk_items k = done ++ x :: t ->
    pn_pre sC st mC OW LB E boC [] (bv_unsigned sp + -80) lo B errvC canary -> pn_acc LB (bv_unsigned sp) K s sC m mC ->
    rw_cells ctusegs mC (bv_unsigned sp + -80) lframe -> sk_rep mC LB adr k -> 0 <= nwC < 2^64 -> rw_cells ctusegs mC out (bio_null_cells NULL_METHOD pv nwC) ->
    frm0 fcC -> sp_F F FcC ->
    implM ctusegs (interp (ap_embed (scts_print (x :: t) st))) sC POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp (wz RATP) t0 t1 t2 sp (Z_to_bv 64 0) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 A_SEP) (Z_to_bv 64 4) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sk_blk k))) (Z_to_bv 64 (sk_num k)) (Z_to_bv 64 (zlength done)) (Z_to_bv 64 A_C10)
               v25 v26 v27 t3 t4 t5 t6)
          FcC (Z_to_bv 64 SCT_LIST_LOOP) fcC None mC (seg_rom ctusegs)).
  Proof using HBIN HF HM KID KNB KOW LOB NI SP16 SPB63 T_ADJ_FAIL T_ADJ_OK T_PRINT T_SETSTR_FAIL T_SETSTR_OK.
    induction t as [|y t IH]; intros x done sC mC errvC boC FcC fcC nwC x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 EQ PN ACC FR SK NW HB FRM HFC.
    all: pose proof (lp_open _ _ _ _ PN) as (HEAP & AS & ST & CEIL & GLO & SSP & MI & NM & OB0 & OB1 & OB2 & ESP & SPR).
    all: destruct (lp_item sC mC done x _ HEAP CEIL SK EQ) as (SAR & DR & SA8 & D8 & IR & NR & RNUM & RDAT & RITEM & REPX & HIDX).
    all: pose proof (zlength_nonneg'' done) as D0.
    all: unfold SCT_LIST_LOOP; pose proof (munch_refl [(lo, bv_unsigned sp + -80)] mC) as MU; pose proof (wmono_refl ctusegs mC) as WM.
    all: unfold lframe in FR.
    all: cbn [scts_print].
    all: unfold implM; iprefix.
    (* [comment removed for export] *)
    all: zstep; zstep; zstep.
    all: eapply evt_cut; [eapply (OPENSSL_sk_value_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FcC fcC mC lo (adr (sk_blk k)) (sk_num k) (optr adr (sk_data k)) (zlength done) (adr (sc_blk x)));
           [rewrite ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ESP; lia| exact SAR| exact DR| exact SA8| exact D8| exact RNUM| exact RDAT| exact IR| lia| exact RITEM| reflexivity| reflexivity]|].
    all: unfold nid_post; cbv beta; intros ms' PO; rewrite ?ESP in PO;
         destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mV & -> & MUv & WMv & MIv & STv).
    all: replace (ret_pc (Z_to_bv 64 1694864)) with (Z_to_bv 64 1694864) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    all: assert (MUv' : munch [(lo, bv_unsigned sp + -80); (out, out + 128)] mC mV) by (intros xx Hx; apply MUv; clear - Hx LOB; cbn in *; lia).
    all: destruct (pn_seg_bio sC st mC mV OW LB E boC [] (bv_unsigned sp + -80) (bv_unsigned sp + -80) lo B errvC canary _ (bv_unsigned sp) pbio out K
                  PN HBIN NI MUv' WMv ltac:(constructor; [left; cbn; lia| constructor; [right; cbn; unfold BIO_SIZE; lia| constructor]])
                  ltac:(lia) ltac:(lia) ltac:(lia) MIv STv kf) as (PNv & LXv & KPv).
    all: apply (rw_cells_transport ctusegs [(bv_unsigned sp + -80 - 16, bv_unsigned sp + -80)] mC mV) in FR; [| exact MUv| exact WMv| clear - LOB; cbn [disjoint_from cells_size csize Nat.add length]; lia].
    all: apply (rw_cells_transport ctusegs [(bv_unsigned sp + -80 - 16, bv_unsigned sp + -80)] mC mV) in HB; [| exact MUv| exact WMv| clear - LOB OB1 CEIL; cbn [disjoint_from cells_size csize Nat.add length bio_null_cells bio_cells]; lia].
    all: assert (SKv : sk_rep mV LB adr k) by (eapply (sk_rep_munch sC OW LB mC mV); [exact HEAP| exact SK| exact HBIN| exact CEIL| exact MUv'| exact WMv]).
    all: assert (REPv : sct_rep mV (OW ++ LB) adr x) by (eapply (sct_rep_munch sC (OW ++ LB) mC mV); [exact HEAP| exact REPX| apply in_app_iff; left; exact HBIN| exact HIDX| exact CEIL| exact MUv'| exact WMv]).
    all: assert (ACCv : pn_acc LB (bv_unsigned sp) K s sC m mV) by (eapply pn_acc_trans; [exact ACC|]; split; [exact LXv| split; [exact KPv| split; reflexivity]]).
    all: clear HEAP AS ST SSP MI NM MU WM MUv WMv MIv STv MUv' PN ACC SK REPX LXv KPv RNUM RDAT RITEM.
    (* [comment removed for export] *)
    all: zstep; zstep; zstep; zstep.
    all: apply evt_done.
    all: lazymatch goal with |- impl ?segs _ (?c ?st0) (epost ?EE) ?ms =>
           lazymatch EE with (fun p => ?QQ (fst p) (snd p)) => change (implM segs c st0 QQ ms) end end.
    all: eapply implM_abind;
         [eapply (SCT_print_walk TSTK HM HF T_ADJ_OK T_ADJ_FAIL T_SETSTR_OK T_SETSTR_FAIL T_PRINT
                    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FcC fcC mV sC st OW LB E boC lo B errvC canary K adr x pbio out pv nwC);
            [eapply ap_pre_of_pn_lit; [exact PNv| pose proof SP16 as SP16'; clear - SP16'; apply Z.mod_divide in SP16'; [| lia]; destruct SP16' as [qq Hq]; apply Z.mod_divide; [lia|]; exists (qq - 5); lia| lia| unfold SCT_PRINT_STACK; lia]
            | reflexivity| exact FRM| reflexivity| reflexivity| reflexivity| reflexivity| exact REPv| exact HBIN| exact NI| exact HIDX| exact HB| exact NW| exact KOW| exact KID| exact KNB]
         |].
    all: intros r sR msR PO; unfold ap_post in PO;
         destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & FR_ & fcR & mR & OWR & errvR & boR & -> & FRMR & FREGR & PRER & LXR & SOR & FAR & BKR & (ER & EOW & nwR & NWR & HBR));
         subst r OWR; cbn [fst snd]; rename FR_ into FcR.
    all: rewrite ?ESP in PRER; rewrite ?ESP in LXR.
    all: replace (ret_pc (Z_to_bv 64 1694880)) with (Z_to_bv 64 1694880) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    all: pose proof (pn_pre_of_ap_lit _ _ _ _ _ _ _ _ _ _ _ _ _ PRER ltac:(lia) ltac:(lia)) as PNR.
    all: pose proof (lp_open _ _ _ _ PNv) as (HEAPv & _).
    all: assert (ACCR : pn_acc LB (bv_unsigned sp) K s sR m mR)
           by (eapply pn_acc_trans; [exact ACCv|]; split; [eapply lx_pres_weaken; [exact LXR| lia| intros b Hb; exact Hb| intros a Ha; exact Ha]| split; [exact (proj2 (proj2 BKR))| split; assumption]]).
    all: assert (SKR : sk_rep mR LB adr k) by (eapply (sk_rep_lx sC OW LB mV mR); [exact HEAPv| exact SKv| exact LXR]).
    all: apply (rw_cells_agree _ _ _ _ _ (agree_of_lx_pres _ _ _ _ _ LXR)) in FR; [| intros a Ha; cbn in Ha; split; [unfold LIBW_AP; cbn [rin_ivs fst snd]; lia| left; lia]].
    all: assert (HFCR : sp_F F FcR) by (intros rr Hr; rewrite (FREGR rr Hr); apply HFC; exact Hr).
    all: clear PNv ACCv SKv REPv HEAPv HB NW FRM HFC LXR BKR PRER FREGR. all: clear mV.
    all: pose proof (lp_open _ _ _ _ PNR) as (HEAP & AS & ST & CEIL' & GLO' & SSP & MI & NM & _).
    all: destruct (lp_item sR mR done x _ HEAP CEIL SKR EQ) as (_ & _ & _ & _ & _ & _ & RNUM & _).
    all: pose proof (munch_refl [(lo, bv_unsigned sp + -80)] mR) as MU; pose proof (wmono_refl ctusegs mR) as WM.
    (* [comment removed for export] *)
    1: cbn [scts_print ap_embed aret]; apply implM_interp_ret.
    2: unfold implM; iprefix.
    all: zstep; zstep.
    all: eapply evt_cut; [eapply (OPENSSL_sk_num_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FcR fcR mR lo (adr (sk_blk k)) (sk_num k));
           [rewrite ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ESP; lia| exact SAR| exact SA8| exact RNUM| lia| reflexivity]|].
    all: unfold nid_post; cbv beta; intros ms' PO; rewrite ?ESP in PO;
         destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mN & -> & MUn & WMn & MIn & STn).
    all: replace (ret_pc (Z_to_bv 64 1694888)) with (Z_to_bv 64 1694888) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    all: assert (MUn' : munch [(lo, bv_unsigned sp + -80); (out, out + 128)] mR mN) by (intros xx Hx; apply MUn; clear - Hx LOB; cbn in *; lia).
    all: destruct (pn_seg_bio sR st mR mN OW LB E boR [] (bv_unsigned sp + -80) (bv_unsigned sp + -80) lo B errvR canary _ (bv_unsigned sp) pbio out K
                  PNR HBIN NI MUn' WMn ltac:(constructor; [left; cbn; lia| constructor; [right; cbn; unfold BIO_SIZE; lia| constructor]])
                  ltac:(lia) ltac:(lia) ltac:(lia) MIn STn kf) as (PNn & LXn & KPn).
    all: apply (rw_cells_transport ctusegs [(bv_unsigned sp + -80 - 16, bv_unsigned sp + -80)] mR mN) in FR; [| exact MUn| exact WMn| clear - LOB; cbn [disjoint_from cells_size csize Nat.add length]; lia].
    all: apply (rw_cells_transport ctusegs [(bv_unsigned sp + -80 - 16, bv_unsigned sp + -80)] mR mN) in HBR; [| exact MUn| exact WMn| clear - LOB OB1 CEIL; cbn [disjoint_from cells_size csize Nat.add length bio_null_cells bio_cells]; lia].
    all: assert (SKn : sk_rep mN LB adr k) by (eapply (sk_rep_munch sR OW LB mR mN); [exact HEAP| exact SKR| exact HBIN| exact CEIL| exact MUn'| exact WMn]).
    all: assert (ACCn : pn_acc LB (bv_unsigned sp) K s sR m mN) by (eapply pn_acc_trans; [exact ACCR|]; split; [exact LXn| split; [exact KPn| split; reflexivity]]).
    all: clear HEAP AS ST SSP MI NM MU WM MUn WMn MIn STn MUn' PNR ACCR SKR LXn KPn RNUM. all: clear mR.
    all: pose proof (lp_open _ _ _ _ PNn) as (HEAP & AS & ST & _ & _ & SSP & MI & NM & _).
    all: pose proof (munch_refl [(lo, bv_unsigned sp + -80)] mN) as MU; pose proof (wmono_refl ctusegs mN) as WM.
    2: pose proof (zlength_nonneg'' t) as TL0.
    1: assert (LEN : sk_num k = zlength done + 1) by (unfold sk_num; rewrite EQ, zlength_app'; unfold zlength; cbn [length]; lia).
    2: assert (LEN : sk_num k = zlength done + 2 + zlength t) by (unfold sk_num; rewrite EQ, zlength_app'; unfold zlength in *; cbn [length]; lia).
    all: zstep; rewrite (swrap32_small (sk_num k + -1)) by lia; uchk.
    - (* [comment removed for export] *)
      zstep. if_cases KB; zify_cond KB; [| exfalso; revert KB; rewrite ?signed_small, ?unsigned_lit by lia; lia]. try clear KB.
      zstep. rewrite (swrap32_small (zlength done + 1)) by lia.
      zstep. if_cases KN; zify_cond KN; [exfalso; revert KN; rewrite ?unsigned_lit by lia; lia|]. try clear KN.
      eapply lp_finish; [exact PNn| exact ACCn| exact FR| exact NWR| exact HBR| exact FRMR| exact HFCR].
    - (* [comment removed for export] *)
      zstep. if_cases KB; zify_cond KB; [exfalso; revert KB; rewrite ?signed_small, ?unsigned_lit by lia; lia|]. try clear KB.
      zstep. zstep. zstep. zstep.
      eapply evt_cut.
      { eapply (BIO_printf_null_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FcR fcR mN out pv nwR A_C10 lo canary);
          [rewrite ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ESP; unfold BIO_PRINTF_STACK, VSN_DEPTH; lia| rewrite ESP; lia| rewrite ESP; clear - SP16; Z.div_mod_to_equations; lia| exact SSP| exact FRMR
          | exact HBR| unfold obj_range, BIO_SIZE, GLOBALS_TOP; lia| pose proof (blk_bounds _ _ _ _ _ _ HEAP ltac:(apply in_app_iff; left; exact HBIN)) as (_ & _ & _ & _ & O16); clear - O16; Z.div_mod_to_equations; lia| exact NWR| exact NM| rewrite ESP; apply pcok_sep; [exact MI| unfold STATIC_SPLIT; lia]| reflexivity| reflexivity]. }
      cbv beta. unfold bio_printf_post. intros ms' PO. rewrite ?ESP in PO.
      destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & FcP & fcP & mP & -> & MUp & WMp & MIp & FRMp & FREGp & STp & SSPp & HBp).
      replace (ret_pc (Z_to_bv 64 1694916)) with (Z_to_bv 64 1694916) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rewrite <- bio_null_cells_mod in HBp.
      destruct (pn_seg_bio sR st mN mP OW LB E boR [] (bv_unsigned sp + -80) (bv_unsigned sp + -80) lo B errvR canary _ (bv_unsigned sp) pbio out K
                  PNn HBIN NI MUp WMp ltac:(constructor; [left; cbn; lia| constructor; [right; cbn; unfold BIO_SIZE; lia| constructor]])
                  ltac:(lia) ltac:(lia) ltac:(lia) MIp STp kf) as (PNp & LXp & KPp).
      apply (rw_cells_transport ctusegs [(lo, bv_unsigned sp + -80); (out, out + 128)] mN mP) in FR; [| exact MUp| exact WMp| clear - LOB OB1 CEIL; cbn [disjoint_from cells_size csize Nat.add length]; lia].
      assert (SKp : sk_rep mP LB adr k) by (eapply (sk_rep_munch sR OW LB mN mP); [exact HEAP| exact SKn| exact HBIN| exact CEIL| exact MUp| exact WMp]).
      assert (ACCp : pn_acc LB (bv_unsigned sp) K s sR m mP) by (eapply pn_acc_trans; [exact ACCn|]; split; [exact LXp| split; [exact KPp| split; reflexivity]]).
      assert (HFCp : sp_F F FcP) by (intros rr Hr; rewrite (FREGp rr Hr); apply HFCR; exact Hr).
      clear HEAP AS ST SSP MI NM MU WM MUp WMp MIp STp PNn ACCn SKn LXn0 || clear HEAP AS ST SSP MI NM MU WM MUp WMp MIp STp PNn ACCn SKn.
      pose proof (munch_refl [(lo, bv_unsigned sp + -80)] mP) as MU. pose proof (wmono_refl ctusegs mP) as WM.
      (* [comment removed for export] *)
      zstep. rewrite (swrap32_small (zlength done + 1)) by lia.
      zstep. if_cases KN; zify_cond KN; [| exfalso; revert KN; rewrite ?unsigned_lit by lia; lia]. try clear KN.
      apply evt_done.
      lazymatch goal with |- impl ?segs _ (?c ?st0) (epost ?EE) ?ms =>
        lazymatch EE with (fun p => ?QQ (fst p) (snd p)) => change (implM segs c st0 QQ ms) end end.
      replace (zlength done + 1) with (zlength (done ++ [x])) by (rewrite zlength_app'; reflexivity).
      eapply (IH y (done ++ [x])); [rewrite <- app_assoc; exact EQ| exact PNp| exact ACCp| exact FR| exact SKp| apply Z.mod_pos_bound; lia| exact HBp| exact FRMp| exact HFCp].
  Qed.
  End Act.

  Theorem SCT_LIST_print_walk : SCT_LIST_print_spec TSTK.
  Proof using HF HM T_ADJ_FAIL T_ADJ_OK T_PRINT T_SETSTR_FAIL T_SETSTR_OK.
    intros until nw. intros PRE TP FRM -> -> -> -> -> SK HBIN NI HB NW KOW KID KNB.
    destruct (pn_pre_of_ap _ _ _ _ _ _ _ _ _ _ _ _ _ PRE ltac:(unfold SCT_LIST_PRINT_STACK, SCT_PRINT_STACK; lia)) as (PN0 & LO0 & SP16). unfold SCT_LIST_PRINT_STACK, SCT_PRINT_STACK in LO0.
    pose proof PN0 as (HEAP & AS & IDS & DC & AUX & SPB & B63 & ST & CEIL & GLO & _ & ERR & SSP & MI). cbn [app] in HEAP.
    pose proof AS as (_ & IMG & _). unfold GLOBALS_TOP in GLO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (blk_bounds _ _ _ _ _ _ HEAP ltac:(apply in_app_iff; left; exact HBIN)) as (OB0 & OB1 & OB2 & OB3 & OB4). unfold BIO_SIZE in OB2, OB3.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
    pose proof (kf OW LB K pbio KOW KNB) as KF.
    subst tp. unfold sct_list_print, SCT_LIST_PRINT, MallocRep.wz.
    unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB.
    (* [comment removed for export] *)
    pose proof SK as (HKIN & (sorted & SR & HC) & HD & HFI & ND).
    pose proof (blk_bounds _ _ _ _ _ _ HEAP ltac:(apply in_app_iff; right; exact HKIN)) as (K1 & K2 & K3 & K4 & K5). unfold STACK_SIZE in *.
    assert (NUMR : 0 <= sk_num k < 2^23).
    { unfold sk_num in *. pose proof (zlength_nonneg'' (sk_items k)). destruct (sk_data k) as [[q na]|]; [destruct HD as (_ & H2 & H3 & _); lia| rewrite HD; cbn; unfold zlength; cbn; lia]. }
    unfold sk_cells in HC.
    assert (RNUM : ro_cells ctusegs m (adr (sk_blk k)) [C4 (wz (sk_num k))])
      by (lazymatch type of HC with rw_cells _ _ _ (?c0 :: ?rest) => exact (proj1 (proj1 (proj1 (rw_cells_app m _ [c0] rest) HC))) end).
    unfold MallocRep.wz in RNUM.
    clear HC HD HFI ND SR.
    assert (SEPK : adr (sk_blk k) + 56 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= adr (sk_blk k)) by lia.
    assert (SEPB : out + 128 <= lo \/ bv_unsigned sp <= out) by lia.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    unfold implM. iprefix.
    (* [comment removed for export] *)
    carve_frame 80%nat ST. zstep. do 10 zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. name_mem m1.
    eapply evt_cut; [eapply (OPENSSL_sk_num_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 lo (adr (sk_blk k)) (sk_num k));
           [rewrite ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ESP; lia| unfold STACK_SIZE; lia| clear - K5; Z.div_mod_to_equations; lia| exact RNUM| lia| reflexivity]|].
    unfold nid_post; cbv beta; intros ms' PO; rewrite ?ESP in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> & MU2 & WM2 & MI2 & ST2).
    replace (ret_pc (Z_to_bv 64 1694832)) with (Z_to_bv 64 1694832) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    assert (MU2' : munch [(lo, bv_unsigned sp); (out, out + 128)] m m2).
    { intros xx Hx. rewrite (MU2 xx); [apply MU| clear - Hx LO0; cbn in *; lia]. clear - Hx LO0; cbn in *; lia. }
    assert (WM2' : wmono ctusegs m m2) by (eapply wmono_trans; [exact WM| exact WM2]).
    destruct (pn_seg_bio s st m m2 OW LB E bo [] (bv_unsigned sp) (bv_unsigned sp + -80) lo B errv canary _ (bv_unsigned sp) pbio out K
                PN0 HBIN NI MU2' WM2' ltac:(constructor; [left; cbn; lia| constructor; [right; cbn; unfold BIO_SIZE; lia| constructor]])
                ltac:(lia) ltac:(lia) ltac:(lia) MI2 ST2 KF) as (PN2 & LX2 & KP2).
    apply (rw_cells_transport ctusegs [(bv_unsigned sp + -80 - 16, bv_unsigned sp + -80)] m1 m2) in FR; [| exact MU2| exact WM2| clear - LO0; cbn [disjoint_from cells_size csize Nat.add length]; lia].
    apply (rw_cells_transport ctusegs [(bv_unsigned sp + -80 - 16, bv_unsigned sp + -80)] m1 m2) in HB; [| exact MU2| exact WM2| clear - LO0 OB2 CEIL; cbn [disjoint_from cells_size csize Nat.add length]; lia].
    assert (SK2 : sk_rep m2 LB adr k) by (eapply (sk_rep_munch s OW LB m m2); [exact HEAP| exact SK| exact HBIN| exact CEIL| exact MU2'| exact WM2']).
    assert (ACC2 : pn_acc LB (bv_unsigned sp) K s s m m2) by (split; [exact LX2| split; [exact KP2| split; reflexivity]]).
    assert (HFC : sp_F F F) by (intros rr Hr; reflexivity).
    clear MU WM MU2 WM2 MI2 ST2 RNUM MI SSP ERR ST. clear m1.
    (* [comment removed for export] *)
    zstep. if_cases KZ; zify_cond KZ.
    - assert (N0 : sk_num k = 0) by (revert KZ; rewrite ?signed_small, ?unsigned_lit by lia; lia). clear KZ.
      assert (E0 : sk_items k = []) by (unfold sk_num in N0; destruct (sk_items k); [reflexivity| exfalso; revert N0; unfold zlength; cbn; lia]).
      rewrite E0. cbn [scts_print]. apply evt_done. apply implM_aret.
      change (bio_cells 2978032 1 0 0 pv nw) with (bio_null_cells NULL_METHOD pv nw) in HB.
      eapply (lp_finish sp gp F fc m s st OW LB E lo B canary K adr k pbio out pv _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(lia) (conj SPB B63) SP16 HBIN KOW KID);
        [exact PN2| exact ACC2| exact FR| exact NW| exact HB| exact FRM| exact HFC].
    - assert (NP : 0 < sk_num k) by (first [exact KZ0| revert KZ; rewrite ?signed_small, ?unsigned_lit by lia; lia]). try clear KZ. try clear KZ0 KZ1.
      destruct (sk_items k) as [|xi ti] eqn:EI; [exfalso; unfold sk_num in NP; rewrite EI in NP; revert NP; unfold zlength; cbn; lia|].
      zstep. zstep. zstep. zstep.
      apply evt_done.
      lazymatch goal with |- impl ?segs _ (?c ?st0) (epost ?EE) ?ms =>
        lazymatch EE with (fun p => ?QQ (fst p) (snd p)) => change (implM segs c st0 QQ ms) end end.
      change (bio_cells 2978032 1 0 0 pv nw) with (bio_null_cells NULL_METHOD pv nw) in HB.
      unfold A_C10. change (Z_to_bv 64 0) with (Z_to_bv 64 (zlength (@nil (sctr bptr)))) at 15 || idtac.
      eapply (lp_loop sp gp F fc m s st OW LB E lo B canary K adr k pbio out pv _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(lia) (conj SPB B63) SP16 HBIN NI KOW KID KNB ti xi []);
        [rewrite EI; reflexivity| exact PN2| exact ACC2| exact FR| exact SK2| exact NW| exact HB| exact FRM| exact HFC] || fail "LPAPPLY".
  Qed.
End Proofs.

End WithCeiling0.
