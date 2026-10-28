(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG CtSizes CtWire CtTime CtModel BnBase BnModel BnTree ApBase ApState ApLogic ApErr PrintfModel PrintfModelX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Printf_pieces Printf_piecesx Printf_apfmt Printf_ctfmt Printf_sn.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs I_lkit FX_lib F_pop_arg F_printf_iface I_vsnstmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem BnTacX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct RtCallA UnwindA UnwindX W_cryptoA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit W_bio_push Fr_bio_write_intern W_bio_write Fr_BIO_vprintf Fr_BIO_printf W_bio_printf W_bio_printf2 W_bio_vprintfG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require W_sct_list_free SctRep W_sk_leaves SctStmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnA Require Import PrnFmtA W_bio_hex_stringA PrnSctFmtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnP Require Import MagicDiv W_sct_print_B1.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac rstep := OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
(* [comment removed for export] *)
Ltac brc :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
    let v := eval vm_compute in c in
    lazymatch v with
    | true => replace (if c then a else b) with a by (vm_compute; reflexivity)
    | false => replace (if c then a else b) with b by (vm_compute; reflexivity)
    end
  end.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition prn_item_wt (x : sctr bptr) : Z :=
  if sc_version x =? 0 then CtSctP.SctRep.logid_len (sc_logid x) + sc_extlen x + sc_siglen x else sc_bloblen x.
Definition SCT_PRINT_BASE_A : Z := 48.
Definition sct_print_costA (x : sctr bptr) : Z := SCT_PRINT_BASE_A + HX_CRED (prn_item_wt x).
(* [comment removed for export] *)
Definition SC_BODY_STACK_A : Z := 704 + RT_STACK.
Definition SCT_PRINT_STACK_A : Z := 176 + SC_BODY_STACK_A.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sct_addr (adr : bptr -> Z) (x : sctr bptr) (a : Z) : Prop :=
  in_block (map (fun p => (p, adr p, 0)) []) a \/
  (adr (sc_blk x) <= a < adr (sc_blk x) + SCT_SIZE)
  \/ (exists q n, (osz32 (sc_logid x) = Some (q, n) \/ sc_ext x = Some (q, n) \/ sc_sig x = Some (q, n) \/ sc_blob x = Some (q, n)) /\ adr q <= a < adr q + n).

Lemma arr_repA_agree : forall m m' L adr o,
  arr_repA m L adr o -> agree_on (fun a => exists q n, o = Some (q, n) /\ adr q <= a < adr q + n) m m' -> arr_repA m' L adr o.
Proof.
  intros m m' L adr [[q n]|] H AG; [| exact I]. destruct H as (N0 & IN & bs & HC). split; [exact N0|]. split; [exact IN|]. exists bs.
  eapply rw_cells_agree; [exact AG| exact HC|]. intros a Ha. cbn in Ha. rewrite Nat.add_0_r, Z2Nat.id in Ha by lia. exists q, n. split; [reflexivity| exact Ha].
Qed.

Lemma sct_repA_agree : forall m m' L adr x,
  sct_repA m L adr x -> agree_on (sct_addr adr x) m m' -> sct_repA m' L adr x.
Proof.
  intros m m' L adr x H AG. pose proof H as (IN & AL & CELLS & A1 & A2 & A3 & A4 & REST).
  split; [exact IN|]. split; [exact AL|].
  split. { eapply rw_cells_agree; [exact AG| exact CELLS|]. intros a Ha. rewrite CtSctP.SctRep.sct_cells_size in Ha. right; left. exact Ha. }
  split. { eapply arr_repA_agree; [exact A1|]. eapply agree_on_mono; [exact AG|]. intros a (q & n & E & R). right; right. exists q, n. split; [| exact R]. left. exact E. }
  split. { eapply arr_repA_agree; [exact A2|]. eapply agree_on_mono; [exact AG|]. intros a (q & n & E & R). right; right. exists q, n. split; [| exact R]. right; left. exact E. }
  split. { eapply arr_repA_agree; [exact A3|]. eapply agree_on_mono; [exact AG|]. intros a (q & n & E & R). right; right. exists q, n. split; [| exact R]. right; right; left. exact E. }
  split. { eapply arr_repA_agree; [exact A4|]. eapply agree_on_mono; [exact AG|]. intros a (q & n & E & R). right; right. exists q, n. split; [| exact R]. right; right; right. exact E. }
  exact REST.
Qed.

(* [comment removed for export] *)
Lemma sct_addr_block : forall m L adr x a, sct_repA m L adr x -> sct_addr adr x a ->
  exists b, In b (sct_blocks adr x) /\ In b L /\ blk_addr b <= a < blk_addr b + blk_size b.
Proof.
  intros m L adr x a H Ha. pose proof H as (IN & AL & CELLS & A1 & A2 & A3 & A4 & REST).
  destruct Ha as [(b & Hb & _)|[Ha|(q & n & E & R)]]; [destruct Hb| |].
  - exists (sc_blk x, adr (sc_blk x), SCT_SIZE). split; [| split; [exact IN| cbn; exact Ha]].
    unfold CtSctP.W_sct_list_free.sct_blocks. rewrite !in_app_iff. right; right; right; right. left. reflexivity.
  - exists (q, adr q, n). cbn [blk_addr blk_size fst snd].
    assert (HIN : In (q, adr q, n) L /\ In (q, adr q, n) (sct_blocks adr x)).
    { unfold CtSctP.W_sct_list_free.sct_blocks. rewrite !in_app_iff.
      destruct E as [E|[E|[E|E]]].
      - unfold arr_repA in A1. rewrite E in A1. destruct A1 as (_ & I1 & _). split; [exact I1|]. left. unfold CtSctP.W_sct_list_free.osz32, option_map in E |- *. destruct (sc_logid x); [injection E as -> ->; left; reflexivity| discriminate].
      - unfold arr_repA in A2. rewrite E in A2. destruct A2 as (_ & I1 & _). split; [exact I1|]. right; left. rewrite E. left; reflexivity.
      - unfold arr_repA in A3. rewrite E in A3. destruct A3 as (_ & I1 & _). split; [exact I1|]. right; right; left. rewrite E. left; reflexivity.
      - unfold arr_repA in A4. rewrite E in A4. destruct A4 as (_ & I1 & _). split; [exact I1|]. right; right; right; left. rewrite E. left; reflexivity. }
    destruct HIN as [H1 H2]. split; [exact H2|]. split; [exact H1| exact R].
Qed.

(* [comment removed for export] *)
Lemma sx32_u32_nz : forall v, v <> 0 -> (v = -1 \/ 0 <= v < 256) -> bv_unsigned (sx32 (Z_to_bv 64 (CtSctP.SctRep.u32 v))) <> 0.
Proof.
  intros v NZ [->|R]; [vm_compute; discriminate|].
  unfold sx32, CtSctP.SctRep.u32. rewrite (Z.mod_small v) by lia. rewrite (unsigned_lit v) by lia. rewrite swrap32_sint32.
  unfold sint32. rewrite (Z.mod_small v) by lia. destruct (Z.ltb_spec v (2^31)); [| lia]. rewrite unsigned_lit by lia. exact NZ.
Qed.

Section SC.
Context {AR : ARun}.          (* [comment removed for export] *)
Local Notation RTS := (@ar_RT AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FRM := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Hypothesis PFC : printf_contracts RTS.

Variables (sp : word) (spa f lo : Z) (g : nat) (OW LB : list block) (pb : bptr) (out pv : Z) (adr : bptr -> Z) (x : sctr bptr).
Variables (m3 : mem) (Σ1 : rts RTS) (vra v8 gp : word) (j0 j8 j16 j32 j40 junk : list (bv 8)).

Hypothesis HEAP3 : AHEAP Σ1 OW LB m3.
Hypothesis CEIL : ACEIL <= lo.
Hypothesis LO : lo + SC_BODY_STACK_A <= spa.
Hypothesis SPAL : bv_unsigned sp - 176 <= spa.
Hypothesis SPAH : spa <= bv_unsigned sp - 160.
Hypothesis SPA32 : spa mod 32 = 0.
Hypothesis GSZ : Z.of_nat g = bv_unsigned sp - spa - 72.
Hypothesis TOP : bv_unsigned sp + 16 <= USTACK_TOP.
Hypothesis FLEN : (S (S (S (length FRM))) < FRAMES_MAX)%nat.
Hypothesis HBIN : In (pb, out, BIO_SIZE) OW.
Hypothesis REP3 : sct_repA m3 (OW ++ LB) adr x.
Hypothesis NPB : ~ In pb (map blk_id (sct_blocks adr x)).
Hypothesis GEO : fr_geo f 1.
Hypothesis FRESH : forall b, In b (OW ++ LB) -> off_fr f 1 b.

(* [comment removed for export] *)
Definition sc_lo (c24 : cell) : list cell := [CB 8 j0; CB 8 j8; CB 8 j16; c24; CB 8 j32; CB 8 j40; C8 (Z_to_bv 64 f); CB g junk].
Definition sc_inv (OWx LBc : list block) (c24 : cell) (lv : list (Z * Z)) (Σc : rts RTS) (m : mem) : Prop :=
  AHEAP Σc (OWx ++ OW) LBc m /\ rt_live RTS Σc = lv /\ mem_inv ctasegs m /\ stk ctasegs m lo spa
  /\ agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ outside [(out, out + 128)]%Z a) m3 m
  /\ rw_cells ctasegs m spa (sc_lo c24) /\ csize c24 = 8%nat
  /\ rw_cells ctasegs m (bv_unsigned sp + -16) [C8 v8; C8 vra]
  /\ sct_repA m (OW ++ LB) adr x
  /\ (forall b, In b LB -> In b LBc).
Definition sc_bio (m : mem) (nw : Z) : Prop := 0 <= nw < 2^64 /\ rw_cells ctasegs m out (bio_null_cells NULL_METHOD pv nw).

Local Ltac open_inv H := destruct H as (HEAP & LIVE & MI & ST & AGR & FRL & SZ & FRH & REP & LBI).

Lemma sc_factsA :
  0 < out /\ out + 128 <= ACEIL /\ SEGTOP_A <= ACEIL /\ SHHI <= ACEIL /\ ACEIL + STACK_WIN <= USTACK_TOP
  /\ (forall a, sct_addr adr x a -> a < ACEIL /\ outside [(out, out + 128)]%Z a /\ aclient_addr (OW ++ LB) (bv_unsigned sp) a).
Proof.
  assert (HBIN' : In (pb, out, 128) (OW ++ LB)) by (apply in_or_app; left; exact HBIN).
  pose proof (AH_range_gen _ _ _ _ _ HEAP3 HBIN') as (B0 & _ & _ & BC & _). cbn [blk_addr blk_size fst snd] in B0, BC.
  pose proof (AH_ceil _ _ _ _ HEAP3) as (C1 & C2 & C3).
  split; [exact B0|]. split; [exact BC|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
  intros a Ha. destruct (sct_addr_block _ _ _ _ _ REP3 Ha) as (b & Hb & HL & Hr).
  pose proof (AH_range_gen _ _ _ _ _ HEAP3 HL) as (_ & _ & _ & B3 & _).
  assert (NE : blk_id b <> blk_id (pb, out, 128)) by (cbn; intros E; apply NPB; rewrite <- E; apply in_map; exact Hb).
  pose proof (AH_disjoint_gen _ _ _ _ b (pb, out, 128) HEAP3 HL HBIN' NE) as DJ. cbn [blk_addr blk_size fst snd] in DJ.
  split; [clear - Hr B3; lia|]. split; [cbn [outside fst snd]; clear - Hr DJ; split; [lia| exact I]|].
  right; right. exists b. split; [exact HL| exact Hr].
Qed.

(* [comment removed for export] *)
Lemma sc_stkW : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> outside [(spa, spa + 56)]%Z a.
Proof.
  intros a Ha. pose proof (AH_ceil _ _ _ _ HEAP3) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  pose proof LO as LO'. unfold SC_BODY_STACK_A, RT_STACK in LO'. pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu.
  cbn [outside fst snd]. split; [| exact I].
  destruct Ha as [Ha|[Ha|(b & Hb & Hr)]].
  - clear - Ha SPAH; lia.
  - destruct Ha as [(lw & hi & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
    destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr CEILu LO' C1; unfold BnHeapA.ACEIL in *; lia.
  - pose proof (AH_range_gen _ _ _ _ b HEAP3 Hb) as (_ & _ & _ & B3 & _). unfold BnHeapA.ACEIL in B3. clear - Hr B3 CEILu LO'. lia.
Qed.

(* [comment removed for export] *)
Lemma sc_inv_store : forall OWx LBc c24 c24' lv Σc m m', sc_inv OWx LBc c24 lv Σc m ->
  munch [(spa, spa + 56)]%Z m m' -> wmono ctasegs m m' -> mem_inv ctasegs m' -> stk ctasegs m' lo spa ->
  rw_cells ctasegs m' spa (sc_lo c24') -> csize c24' = 8%nat -> rw_cells ctasegs m' (bv_unsigned sp + -16) [C8 v8; C8 vra] ->
  (forall b, In b LBc -> In b LB \/ (spa + 56 <= blk_addr b /\ blk_addr b + blk_size b <= USTACK_TOP) \/ blk_addr b + blk_size b <= spa) ->
  sc_inv OWx LBc c24' lv Σc m'.
Proof.
  intros OWx LBc c24 c24' lv Σc m m' INV MU WM MI' ST' FRL' SZ' FRH' HLB. destruct INV as (HEAP & LIVE & MI & ST & AGR & FRL & SZ & FRH & REP & LBI).
  pose proof (AH_ceil _ _ _ _ HEAP3) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  pose proof LO as LO'. unfold SC_BODY_STACK_A, RT_STACK in LO'. pose proof CEIL as CEILu. unfold BnHeapA.ACEIL in CEILu. pose proof TOP as TOPu. unfold USTACK_TOP in TOPu.
  split. { eapply AH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [left; cbn [fst snd]; clear - CEILu LO' TOPu SPAH; unfold BnHeapA.ACEIL, USTACK_TOP; lia| constructor]. }
  split; [exact LIVE|]. split; [exact MI'|]. split; [exact ST'|].
  split. { eapply agree_on_trans; [exact AGR|]. eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|]. intros a [Ha _]. exact (sc_stkW a Ha). }
  split; [exact FRL'|]. split; [exact SZ'|]. split; [exact FRH'|].
  split; [| exact LBI]. eapply sct_repA_agree; [exact REP|]. eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|].
  intros a Ha. destruct (proj2 (proj2 (proj2 (proj2 (proj2 sc_factsA)))) a Ha) as (_ & _ & C). exact (sc_stkW a C).
Qed.

Local Ltac facts :=
  pose proof sc_factsA as (OB0 & OBC & Cq1 & Cq2 & Cq3 & SCTA); unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in Cq1, Cq2, Cq3;
  pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
  pose proof LO as LO'; unfold SC_BODY_STACK_A, RT_STACK in LO';
  pose proof CEIL as CEILu; unfold BnHeapA.ACEIL in CEILu; pose proof TOP as TOPu; unfold USTACK_TOP in TOPu;
  pose proof OBC as OBCu; unfold BnHeapA.ACEIL in OBCu;
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - SPR LO' CEILu OBCu OB0 SPAL SPAH; lia).

(* [comment removed for export] *)
Lemma sc_printf : forall (Q : config -> Prop) (x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (Σc : rts RTS) (nw : Z) (lv : list (Z * Z)) (LBc : list block) (c24 : cell) (A : Z) (fmt : list Z) (args : list parg) (o : list Z)
    (retpc used budget : Z),
  sc_inv [] LBc c24 lv Σc m -> sc_bio m nw -> rt_credit RTS Σ1 - used <= rt_credit RTS Σc -> 0 <= used -> used + 3 <= budget -> budget <= rt_credit RTS Σ1 ->
  vfmtA_ok A fmt args o -> 0 < zlength o < 512 -> vargsA_ok OW LBc m [a2; a3; a4; a5; a6; a7] args ->
  a0 = Z_to_bv 64 out -> a1 = Z_to_bv 64 A -> x1 = Z_to_bv 64 retpc -> 0 <= retpc < 2^64 -> retpc mod 2 = 0 ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (Fc' : bvmap 5 word) (fc' : bv 32) (m' : mem) (Σc' : rts RTS),
     sc_inv [] LBc c24 lv Σc' m' -> sc_bio m' ((nw + zlength o) mod 2^64) -> rt_credit RTS Σ1 - (used + 3) <= rt_credit RTS Σc' ->
     agree_on (fun a => aclient_addr (OW ++ LBc) spa a /\ outside [(out, out + 128)]%Z a) m m' ->
     cps ctasegs (ASTA RTS Σc' PMc (eq
       (MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) t0' t1' t2' x8 x9 (Z_to_bv 64 (zlength o)) a1' a2' a3' a4' a5' a6' a7'
                x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')
           Fc' (Z_to_bv 64 retpc) fc' None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RTS Σc PMc (eq
    (MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
        Fc (Z_to_bv 64 BIO_PRINTF_A) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until budget. intros INV BIO CR U0 U3 CRED VF OLEN VARGS -> -> -> Hret EVEN K. destruct BIO as [NW HB]. open_inv INV. facts.
  eapply cps_step_rt.
  { eapply (BIO_printf_null_cpsA PFC) with (lo := lo) (OW := OW) (LB := LBc) (pb := pb) (out := out) (pv := pv) (nw := nw) (A := A) (o := o);
      rewrite ?ESPA; try reflexivity.
    - exact HEAP.
    - exact ST.
    - exact CEIL.
    - unfold BIO_PRINTF_NULL_STACK, BIO_VPRINTF_NULL_STACK, BIO_WRITE_NULL_STACK, BPRF_FRAME, BVPF_FRAME, BWI_FRAME, RT_STACK. clear - LO'. lia.
    - unfold USTACK_TOP. clear - TOPu SPAH. lia.
    - clear - SPA32. Z.div_mod_to_equations. lia.
    - exact MI.
    - clear - FLEN. lia.
    - clear - CR U0 U3 CRED. lia.
    - exact HBIN.
    - exact HB.
    - exact NW.
    - exact VF.
    - exact OLEN.
    - exact VARGS. }
  intros Σ2 msP PO LIVE2. unfold bio_printf_null_post in PO. rewrite ?ESPA in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & -> & MI2 & ST2 & AP2 & HEAP2 & _ & CR2 & HB2).
  rewrite (ret_pc_even retpc) by (first [exact EVEN | clear - Hret EVEN; lia]). unfold MallocRep.wz.
  unfold apres_ex, BIO_SIZE in AP2.
  assert (SZL : Z.of_nat (cells_size (sc_lo c24)) = 56 + Z.of_nat g) by (unfold sc_lo; cbn [cells_size csize]; rewrite SZ; clear; lia).
  assert (LBI' : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> aclient_addr (OW ++ LBc) spa a).
  { intros a [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha SPAH; lia| right; left; exact Ha| right; right; exists b; split; [| exact Hr]].
    apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; exact (LBI b Hb)]. }
  apply (rw_cells_agree _ _ _ _ _ AP2) in FRH; [| intros xa Hxa; cbn in Hxa; cbn [outside fst snd]; split; [left; unfold USTACK_TOP; clear - Hxa TOPu SPAH; lia| split; [clear - Hxa OBCu CEILu LO' SPAL SPAH; lia| exact I]]].
  apply (rw_cells_agree _ _ _ _ _ AP2) in FRL; [| intros xa Hxa; rewrite SZL in Hxa; cbn [outside fst snd]; split; [left; unfold USTACK_TOP; clear - Hxa TOPu SPAH SPAL GSZ; lia| split; [clear - Hxa OBCu CEILu LO' SPAL SPAH; lia| exact I]]].
  assert (REP2 : sct_repA m2 (OW ++ LB) adr x).
  { eapply sct_repA_agree; [exact REP|]. eapply agree_on_mono; [exact AP2|]. intros a Ha. destruct (SCTA a Ha) as (_ & O & C). split; [exact (LBI' a C)| exact O]. }
  eapply K.
  - split; [exact HEAP2|]. split; [rewrite LIVE2; exact LIVE|]. split; [exact MI2|]. split; [exact ST2|].
    split. { eapply agree_on_trans; [exact AGR|]. eapply agree_on_mono; [exact AP2|]. intros a [Ha Ho]. split; [exact (LBI' a Ha)| exact Ho]. }
    split; [exact FRL|]. split; [exact SZ|]. split; [exact FRH|]. split; [exact REP2| exact LBI].
  - split; [apply Z.mod_pos_bound; clear; lia| rewrite bio_null_cells_mod; exact HB2].
  - clear - CR CR2. lia.
  - exact AP2.
Qed.

(* [comment removed for export] *)
Lemma sc_hex : forall (Q : config -> Prop) (x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (Σc : rts RTS) (nw : Z) (lv : list (Z * Z)) (LBc : list block) (c24 : cell) (o : option (bptr * Z)) (D len : Z)
    (retpc used budget : Z),
  sc_inv [] LBc c24 lv Σc m -> sc_bio m nw -> rt_credit RTS Σ1 - used <= rt_credit RTS Σc -> 0 <= used -> used + HX_CRED len <= budget -> budget <= rt_credit RTS Σ1 ->
  (o = osz32 (sc_logid x) \/ o = sc_ext x \/ o = sc_sig x \/ o = sc_blob x) ->
  D = optr adr o -> len = olen o -> 0 <= len < 2^31 ->
  a0 = Z_to_bv 64 out -> a1 = Z_to_bv 64 20 -> a2 = Z_to_bv 64 16 -> a3 = Z_to_bv 64 D -> a4 = Z_to_bv 64 len ->
  x1 = Z_to_bv 64 retpc -> 0 <= retpc < 2^64 -> retpc mod 2 = 0 ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (Fc' : bvmap 5 word) (fc' : bv 32) (m' : mem) (Σc' : rts RTS) (nw' : Z),
     sc_inv [] LBc c24 lv Σc' m' -> sc_bio m' nw' -> rt_credit RTS Σ1 - (used + HX_CRED len) <= rt_credit RTS Σc' ->
     agree_on (fun a => aclient_addr (OW ++ LBc) spa a /\ outside [(out, out + 128)]%Z a) m m' ->
     cps ctasegs (ASTA RTS Σc' PMc (eq
       (MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) t0' t1' t2' x8 x9 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7'
                x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')
           Fc' (Z_to_bv 64 retpc) fc' None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RTS Σc PMc (eq
    (MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
        Fc (Z_to_bv 64 BIO_HEX_STRING_A) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until budget. intros INV BIO CR U0 UB CRED HO -> -> LEN -> -> -> -> -> -> Hret EVEN K. destruct BIO as [NW HB]. open_inv INV. facts.
  assert (HXN : 0 <= HX_CRED (olen o)) by (unfold HX_CRED; clear - LEN; lia).
  assert (LBI' : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> aclient_addr (OW ++ LBc) spa a).
  { intros a [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha SPAH; lia| right; left; exact Ha| right; right; exists b; split; [| exact Hr]].
    apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; exact (LBI b Hb)]. }
  pose proof REP as (_ & _ & _ & A1 & A2 & A3 & A4 & _).
  assert (AR' : arr_repA m (OW ++ LB) adr o) by (destruct HO as [->|[->|[->| ->]]]; assumption).
  assert (KK : forall (bd : bptr) (bs : list (bv 8)),
    (0 < olen o -> In (bd, optr adr o, olen o) (OW ++ LBc) /\ bd <> pb /\ rw_cells ctasegs m (optr adr o) [CB (Z.to_nat (olen o)) bs]) ->
    cps ctasegs (ASTA RTS Σc PMc (eq
      (MS (mkR (Z_to_bv 64 retpc) (Z_to_bv 64 spa) gp (wz TP_A) t0 t1 t2 x8 x9 (Z_to_bv 64 out) (Z_to_bv 64 20) (Z_to_bv 64 16) (Z_to_bv 64 (optr adr o)) (Z_to_bv 64 (olen o)) a5 a6 a7
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          Fc (Z_to_bv 64 BIO_HEX_STRING_A) fc None m (seg_rom ctasegs)))) Q).
  { intros bd bs DATA.
    eapply (BIO_hex_string_cpsA PFC) with (lo := lo) (OW := OW) (LB := LBc) (pb := pb) (out := out) (pv := pv) (nw := nw) (bd := bd) (bs := bs); rewrite ?ESPA; try reflexivity.
    - exact HEAP.
    - exact ST.
    - exact CEIL.
    - unfold HX_STACK_A, BIO_PRINTF_NULL_STACK, BIO_VPRINTF_NULL_STACK, BIO_WRITE_NULL_STACK, BPRF_FRAME, BVPF_FRAME, BWI_FRAME, RT_STACK. clear - LO'. lia.
    - unfold USTACK_TOP. clear - TOPu SPAH. lia.
    - clear - SPA32. Z.div_mod_to_equations. lia.
    - exact MI.
    - clear - FLEN. lia.
    - clear - CR U0 UB CRED HXN. lia.
    - exact HBIN.
    - exact HB.
    - exact NW.
    - exact LEN.
    - exact DATA.
    - intros Σ2 m2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 nw2 HEAP2 LIVE2 CR2 ST2 MI2 AP2 NW2 HB2.
      rewrite (ret_pc_even retpc) by (first [exact EVEN | clear - Hret EVEN; lia]). unfold MallocRep.wz.
      unfold apres_ex, BIO_SIZE in AP2.
      assert (SZL : Z.of_nat (cells_size (sc_lo c24)) = 56 + Z.of_nat g) by (unfold sc_lo; cbn [cells_size csize]; rewrite SZ; clear; lia).
      apply (rw_cells_agree _ _ _ _ _ AP2) in FRH; [| intros xa Hxa; cbn in Hxa; cbn [outside fst snd]; split; [left; unfold USTACK_TOP; clear - Hxa TOPu SPAH; lia| split; [clear - Hxa OBCu CEILu LO' SPAL SPAH; lia| exact I]]].
      apply (rw_cells_agree _ _ _ _ _ AP2) in FRL; [| intros xa Hxa; rewrite SZL in Hxa; cbn [outside fst snd]; split; [left; unfold USTACK_TOP; clear - Hxa TOPu SPAH SPAL GSZ; lia| split; [clear - Hxa OBCu CEILu LO' SPAL SPAH; lia| exact I]]].
      assert (REP2 : sct_repA m2 (OW ++ LB) adr x).
      { eapply sct_repA_agree; [exact REP|]. eapply agree_on_mono; [exact AP2|]. intros a Ha. destruct (SCTA a Ha) as (_ & O & C). split; [exact (LBI' a C)| exact O]. }
      eapply K.
      + split; [exact HEAP2|]. split; [rewrite LIVE2; exact LIVE|]. split; [exact MI2|]. split; [exact ST2|].
        split. { eapply agree_on_trans; [exact AGR|]. eapply agree_on_mono; [exact AP2|]. intros a [Ha Ho]. split; [exact (LBI' a Ha)| exact Ho]. }
        split; [exact FRL|]. split; [exact SZ|]. split; [exact FRH|]. split; [exact REP2| exact LBI].
      + split; [exact NW2| exact HB2].
      + clear - CR CR2. lia.
      + exact AP2. }
  destruct o as [[q n]|].
  - destruct AR' as (N0 & IN & bs & HC). apply (KK q bs). intros _. cbn [CtRepP.ApCells.optr CtSctP.SctRep.olen].
    split; [apply in_app_or in IN as [IN|IN]; apply in_or_app; [left; exact IN| right; exact (LBI _ IN)]|].
    split; [| exact HC]. intros E. apply NPB. rewrite <- E. unfold CtSctP.W_sct_list_free.sct_blocks. rewrite !map_app, !in_app_iff.
    destruct HO as [H|[H|[H|H]]].
    + left. unfold CtSctP.W_sct_list_free.osz32, option_map in H. destruct (sc_logid x); [injection H as <- _; left; reflexivity| discriminate].
    + right; left. rewrite <- H. left; reflexivity.
    + right; right; left. rewrite <- H. left; reflexivity.
    + right; right; right; left. rewrite <- H. left; reflexivity.
  - apply (KK pb []). intros Hn. exfalso. cbn in Hn. clear - Hn. lia.
Qed.

(* [comment removed for export] *)
Lemma sc_seg0 : forall (Q : config -> Prop) (x1 t0 t1 t2 a5 a6 a7 x23 x24 t3 t4 t5 t6 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (Σc : rts RTS) (nw : Z) (lv : list (Z * Z)) (c24 : cell) (budget : Z),
  sc_inv [] LB c24 lv Σc m -> sc_bio m nw -> rt_credit RTS Σ1 <= rt_credit RTS Σc -> 6 <= budget -> budget <= rt_credit RTS Σ1 ->
  (* [comment removed for export] *)
  (forall (x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (Fc' : bvmap 5 word) (fc' : bv 32) (m' : mem) (Σc' : rts RTS) (nw' : Z),
     sc_version x = 0 ->
     sc_inv [] LB c24 lv Σc' m' -> sc_bio m' nw' -> rt_credit RTS Σ1 - 6 <= rt_credit RTS Σc' ->
     cps ctasegs (ASTA RTS Σc' PMc (eq
       (MS (mkR x1' (Z_to_bv 64 spa) gp (wz TP_A) t0' t1' t2' sp (Z_to_bv 64 spa) a0' a1' a2' a3' a4' a5' a6' a7'
                (Z_to_bv 64 f) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) (Z_to_bv 64 0) (Z_to_bv 64 A_EMPTY_A) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) t3' t4' t5' t6')
           Fc' (Z_to_bv 64 0x337ef4) fc' None m' (seg_rom ctasegs)))) Q) ->
  (* [comment removed for export] *)
  (forall (x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (Fc' : bvmap 5 word) (fc' : bv 32) (m' : mem) (Σc' : rts RTS) (nw' : Z),
     sc_version x <> 0 ->
     sc_inv [] LB c24 lv Σc' m' -> sc_bio m' nw' -> rt_credit RTS Σ1 - 6 <= rt_credit RTS Σc' ->
     cps ctasegs (ASTA RTS Σc' PMc (eq
       (MS (mkR x1' (Z_to_bv 64 spa) gp (wz TP_A) t0' t1' t2' sp (Z_to_bv 64 spa) a0' a1' a2' a3' a4' a5' a6' a7'
                (Z_to_bv 64 f) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) (Z_to_bv 64 0) (Z_to_bv 64 A_EMPTY_A) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) t3' t4' t5' t6')
           Fc' (Z_to_bv 64 0x337ea4) fc' None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RTS Σc PMc (eq
    (MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 spa) (Z_to_bv 64 (-15)) (Z_to_bv 64 201742) (Z_to_bv 64 3374312) (Z_to_bv 64 (-13)) (Z_to_bv 64 (-8)) a5 a6 a7
             (Z_to_bv 64 f) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 4) (Z_to_bv 64 0) x23 x24 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) t3 t4 t5 t6)
        Fc (Z_to_bv 64 0x337e04) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until budget. intros INV BIO CR0 B6 CRED KV KNV. pose proof INV as INV'. pose proof BIO as BIO'. destruct BIO as [NW HB]. open_inv INV. facts.
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB. unfold sc_lo in FRL.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. brc. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done.
  eapply sc_printf with (nw := nw) (LBc := LB) (c24 := c24) (A := A_C1_A) (fmt := FMT_C1) (args := [PA_i 4; PA_s []]) (o := O_C1) (retpc := 0x337e6c) (used := 0) (budget := budget);
    [exact INV'| exact BIO'| clear - CR0; lia| clear; lia| clear - B6; lia| exact CRED
    | exact vfmtA_C1
    | rewrite zlength_O_C1; clear; lia
    | cbn [vargsA_ok]; split; [cbn [vargA_ok]; rewrite unsigned_lit by (clear; lia); clear; split; [lia| reflexivity]|]; split; [apply emptyA_vargA| exact I]
    | reflexivity| reflexivity| reflexivity| clear; lia| reflexivity|].
  intros t0b t1b t2b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b Fcb fcb m' Σc' INV BIO CR' _. clear dependent m. clear dependent Σc. rename m' into m. rename Σc' into Σc. rename CR' into CR. clear NW SZ LBI. pose proof INV as INV'. pose proof BIO as BIO'. destruct BIO as [NW HB]. open_inv INV.
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB. unfold sc_lo in FRL.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done.
  eapply sc_printf with (nw := (nw + zlength O_C1) mod 2^64) (LBc := LB) (c24 := c24) (A := A_C2_A) (fmt := FMT_C2) (args := [PA_i 8; PA_s []]) (o := O_C2) (retpc := 0x337e88) (used := 3) (budget := budget);
    [exact INV'| exact BIO'| exact CR| clear; lia| clear - B6; lia| exact CRED
    | exact vfmtA_C2
    | rewrite zlength_O_C2; clear; lia
    | cbn [vargsA_ok]; split; [cbn [vargA_ok]; rewrite unsigned_lit by (clear; lia); clear; split; [lia| reflexivity]|]; split; [apply emptyA_vargA| exact I]
    | reflexivity| reflexivity| reflexivity| clear; lia| reflexivity|].
  intros t0c t1c t2c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c Fcc fcc m' Σc' INV BIO CR' _. clear dependent m. clear dependent Σc. rename m' into m. rename Σc' into Σc. rename CR' into CR. clear NW SZ LBI. pose proof INV as INV'. pose proof BIO as BIO'. destruct BIO as [NW HB]. open_inv INV.
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB. unfold sc_lo in FRL.
  (* [comment removed for export] *)
  pose proof REP as (HSIN & AL16s & CELLS & _).
  ablock HEAP HSIN ACCS OFFS. unfold SCT_SIZE in ACCS, OFFS, HSIN.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HSIN) as (BS0 & _ & _ & BSC & BSI). cbn [blk_addr blk_size fst snd] in BS0, BSC, BSI. unfold BnHeapA.ACEIL in BSC.
  lazymatch type of BSI with ?T => change (frozen T) in BSI end.
  pose proof (munch_refl [(spa, spa + 56)]%Z m) as MU.
  assert (OFFW : offshW [(spa, spa + 56)]%Z) by (cbn [offshW]; clear - Cq1 Cq2 Cq3 CEILu LO' TOPu SPAL SPAH; alia).
  unfold CtSctP.SctRep.sct_cells, MallocRep.wz in CELLS.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. zstep.
  pose proof REP as (_ & _ & _ & _ & _ & _ & _ & _ & VR & _).
  destruct (Z.eq_dec (sc_version x) 0) as [V0|NV].
  - replace (sx32 (Z_to_bv 64 (CtSctP.SctRep.u32 (sc_version x)))) with (Z_to_bv 64 0) by (rewrite V0; reflexivity).
    zstep. brc. apply evt_done. eapply (KV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fcc fcc m Σc _ V0 INV' BIO' CR).
  - zstep. if_cases K; zify_cond K.
    + exfalso. exact (sx32_u32_nz _ NV VR K).
    +  apply evt_done. eapply (KNV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fcc fcc m Σc _ NV INV' BIO' CR).
Qed.

(* [comment removed for export] *)
Definition at_exit (Q : config -> Prop) (c24 : cell) (lv : list (Z * Z)) (budget : Z) : Prop :=
  forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x27 t3 t4 t5 t6 : word) (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (Σc : rts RTS) (nw : Z),
    sc_inv [] LB c24 lv Σc m -> sc_bio m nw -> rt_credit RTS Σ1 - budget <= rt_credit RTS Σc ->
    cps ctasegs (ASTA RTS Σc PMc (eq
      (MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 f) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) x27 t3 t4 t5 t6)
          Fc (Z_to_bv 64 0x338204) fc None m (seg_rom ctasegs)))) Q.

(* [comment removed for export] *)
Lemma sc_nv1 : forall (Q : config -> Prop) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (Σc : rts RTS) (nw : Z) (lv : list (Z * Z)) (c24 : cell) (used budget : Z),
  sc_version x <> 0 ->
  sc_inv [] LB c24 lv Σc m -> sc_bio m nw -> rt_credit RTS Σ1 - used <= rt_credit RTS Σc -> 0 <= used -> used + 3 + HX_CRED (sc_bloblen x) <= budget -> budget <= rt_credit RTS Σ1 ->
  at_exit Q c24 lv budget ->
  cps ctasegs (ASTA RTS Σc PMc (eq
    (MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 f) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) (Z_to_bv 64 0) (Z_to_bv 64 A_EMPTY_A) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) t3 t4 t5 t6)
        Fc (Z_to_bv 64 0x337ea4) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until budget. intros NV INV BIO CR U0 UB CRED KX. pose proof INV as INV'. pose proof BIO as BIO'. destruct BIO as [NW HB]. open_inv INV. facts.
  assert (HXN : 0 <= HX_CRED (sc_bloblen x)).
  { unfold HX_CRED, sc_bloblen. pose proof REP as (_ & _ & _ & _ & _ & _ & A4 & _). destruct (sc_blob x) as [[q n]|]; [destruct A4 as (N0 & _); clear - N0; lia| clear; lia]. }
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB. unfold sc_lo in FRL.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done.
  eapply sc_printf with (nw := nw) (LBc := LB) (c24 := c24) (A := A_C3_A) (fmt := FMT_C3) (args := [PA_i 20; PA_s []]) (o := O_C3) (retpc := 0x337ec0) (used := used) (budget := budget);
    [exact INV'| exact BIO'| exact CR| exact U0| clear - UB HXN; lia| exact CRED
    | exact vfmtA_C3
    | rewrite zlength_O_C3; clear; lia
    | cbn [vargsA_ok]; split; [cbn [vargA_ok]; rewrite unsigned_lit by (clear; lia); clear; split; [lia| reflexivity]|]; split; [apply emptyA_vargA| exact I]
    | reflexivity| reflexivity| reflexivity| clear; lia| reflexivity|].
  intros t0b t1b t2b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b Fcb fcb m' Σc' INV BIO CR' _. clear dependent m. clear dependent Σc. rename m' into m. rename Σc' into Σc. rename CR' into CR. clear NW SZ LBI.
  pose proof INV as INV'. pose proof BIO as BIO'. destruct BIO as [NW HB]. open_inv INV.
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB. unfold sc_lo in FRL.
  pose proof REP as (HSIN & AL16s & CELLS & _ & _ & _ & A4 & _ & VR & _ & _ & _ & _ & _ & _ & _ & BL).
  ablock HEAP HSIN ACCS OFFS. unfold SCT_SIZE in ACCS, OFFS, HSIN.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HSIN) as (BS0 & _ & _ & BSC & BSI). cbn [blk_addr blk_size fst snd] in BS0, BSC, BSI. unfold BnHeapA.ACEIL in BSC.
  lazymatch type of BSI with ?T => change (frozen T) in BSI end.
  pose proof (munch_refl [(spa, spa + 56)]%Z m) as MU.
  assert (OFFW : offshW [(spa, spa + 56)]%Z) by (cbn [offshW]; clear - Cq1 Cq2 Cq3 CEILu LO' TOPu SPAL SPAH; alia).
  unfold CtSctP.SctRep.sct_cells, MallocRep.wz in CELLS.
  assert (BLR : 0 <= sc_bloblen x <= MAX_SCT_SIZE).
  { unfold sc_bloblen. unfold CtSctP.SctRep.olen in BL. destruct (sc_blob x) as [[q n]|]; [destruct A4 as (N0 & _); clear - N0 BL; lia| clear; unfold MAX_SCT_SIZE; lia]. }
  unfold MAX_SCT_SIZE in BLR.
  (* [comment removed for export] *)
  lazymatch type of CELLS with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: C8 (Z_to_bv 64 (sc_bloblen x)) :: ?rest) =>
    apply (c8_small_as_c4 m _ [c0; c1; c2] (sc_bloblen x) rest) in CELLS; [| clear - BLR; lia] end.
  cbn [app] in CELLS.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. zstep. try rewrite (sx32_small (sc_bloblen x)) by (clear - BLR; lia). zstep. zstep. zstep. zstep. zstep.
  apply evt_done.
  eapply sc_hex with (nw := (nw + zlength O_C3) mod 2 ^ 64) (LBc := LB) (c24 := c24) (o := sc_blob x) (D := CtRepP.ApCells.optr adr (sc_blob x)) (len := sc_bloblen x)
                    (retpc := 0x338204) (used := used + 3) (budget := budget);
    [exact INV'| exact BIO'| exact CR| clear - U0; lia| clear - UB; lia| exact CRED
    | right; right; right; reflexivity| reflexivity| unfold sc_bloblen, CtSctP.SctRep.olen; reflexivity| clear - BLR; lia
    | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity
    | reflexivity| clear; lia| reflexivity|].
  intros t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d Fcd fcd m' Σc' nw' INV BIO CR' _.
  eapply KX; [exact INV| exact BIO| clear - CR' UB; lia].
Qed.

(* [comment removed for export] *)
Lemma sc_v1a : forall (Q : config -> Prop) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (Σc : rts RTS) (nw : Z) (lv : list (Z * Z)) (j24 : list (bv 8)) (used budget : Z),
  sc_version x = 0 ->
  sc_inv [] LB (CB 8 j24) lv Σc m -> sc_bio m nw -> rt_credit RTS Σ1 - used <= rt_credit RTS Σc -> 0 <= used ->
  used + 9 + HX_CRED (CtSctP.SctRep.logid_len (sc_logid x)) <= budget -> budget <= rt_credit RTS Σ1 ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (Fc' : bvmap 5 word) (fc' : bv 32) (m' : mem) (Σc' : rts RTS) (nw' : Z),
     sc_inv [] LB (C8 (Z_to_bv 64 f)) lv Σc' m' -> sc_bio m' nw' -> rt_credit RTS Σ1 - (used + 9 + HX_CRED (CtSctP.SctRep.logid_len (sc_logid x))) <= rt_credit RTS Σc' ->
     cps ctasegs (ASTA RTS Σc' PMc (eq
       (MS (mkR (Z_to_bv 64 0x337fc8) (Z_to_bv 64 spa) gp (wz TP_A) t0' t1' t2' sp (Z_to_bv 64 spa) (Z_to_bv 64 (adr (sc_blk x) + 40)) a1' a2' a3' a4' a5' a6' a7'
                (Z_to_bv 64 (sc_ts x)) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) (Z_to_bv 64 0) (Z_to_bv 64 A_EMPTY_A) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) t3' t4' t5' t6')
           Fc' (Z_to_bv 64 0x247010) fc' None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RTS Σc PMc (eq
    (MS (mkR x1 (Z_to_bv 64 spa) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 f) (Z_to_bv 64 out) (Z_to_bv 64 (adr (sc_blk x))) (Z_to_bv 64 20) (Z_to_bv 64 8) (Z_to_bv 64 0) (Z_to_bv 64 A_EMPTY_A) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) t3 t4 t5 t6)
        Fc (Z_to_bv 64 0x337ef4) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until budget. intros V0 INV BIO CR U0 UB CRED KTS. pose proof INV as INV'. pose proof BIO as BIO'. destruct BIO as [NW HB]. open_inv INV. facts.
  assert (HXN : 0 <= HX_CRED (CtSctP.SctRep.logid_len (sc_logid x))) by (unfold HX_CRED, CtSctP.SctRep.logid_len, CT_V1_HASHLEN; destruct (sc_logid x); clear; lia).
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB. unfold sc_lo in FRL.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.
  apply evt_done.
  eapply sc_printf with (nw := nw) (LBc := LB) (c24 := CB 8 j24) (A := A_C4_A) (fmt := FMT_C4) (args := []) (o := O_C4) (retpc := 0x337f04) (used := used) (budget := budget);
    [exact INV'| exact BIO'| exact CR| exact U0| clear - UB HXN; lia| exact CRED
    | exact vfmtA_C4| rewrite zlength_O_C4; clear; lia| exact I
    | reflexivity| reflexivity| reflexivity| clear; lia| reflexivity|].
  intros t0b t1b t2b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b Fcb fcb m' Σc' INV BIO CR' _. clear dependent m. clear dependent Σc. rename m' into m. rename Σc' into Σc. rename CR' into CR. clear NW SZ LBI.
  pose proof INV as INV'. pose proof BIO as BIO'. destruct BIO as [NW HB]. open_inv INV.
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB. unfold sc_lo in FRL.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. brc. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done.
  eapply sc_printf with (nw := (nw + zlength O_C4) mod 2 ^ 64) (LBc := LB) (c24 := CB 8 j24) (A := A_C5_A) (fmt := FMT_C5) (args := [PA_i 8; PA_s []]) (o := O_C5) (retpc := 0x337f4c) (used := used + 3) (budget := budget);
    [exact INV'| exact BIO'| exact CR| clear - U0; lia| clear - UB HXN; lia| exact CRED
    | exact vfmtA_C5| rewrite zlength_O_C5; clear; lia
    | cbn [vargsA_ok]; split; [cbn [vargA_ok]; rewrite unsigned_lit by (clear; lia); clear; split; [lia| reflexivity]|]; split; [apply emptyA_vargA| exact I]
    | reflexivity| reflexivity| reflexivity| clear; lia| reflexivity|].
  intros t0c t1c t2c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c Fcc fcc m' Σc' INV BIO CR' _. clear dependent m. clear dependent Σc. rename m' into m. rename Σc' into Σc. rename CR' into CR. clear NW SZ LBI.
  pose proof INV as INV'. pose proof BIO as BIO'. destruct BIO as [NW HB]. open_inv INV.
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB. unfold sc_lo in FRL.
  pose proof REP as (HSIN & AL16s & CELLS & A1 & _ & _ & A4 & _ & VR & _ & _ & _ & TSR & _).
  ablock HEAP HSIN ACCS OFFS. unfold SCT_SIZE in ACCS, OFFS, HSIN.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HSIN) as (BS0 & _ & _ & BSC & BSI). cbn [blk_addr blk_size fst snd] in BS0, BSC, BSI. unfold BnHeapA.ACEIL in BSC.
  lazymatch type of BSI with ?T => change (frozen T) in BSI end.
  pose proof (munch_refl [(spa, spa + 56)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFFW : offshW [(spa, spa + 56)]%Z) by (cbn [offshW]; clear - Cq1 Cq2 Cq3 CEILu LO' TOPu SPAL SPAH; alia).
  unfold CtSctP.SctRep.sct_cells, MallocRep.wz in CELLS.
  assert (LLR : 0 <= CtSctP.SctRep.logid_len (sc_logid x) <= 32) by (unfold CtSctP.SctRep.logid_len, CT_V1_HASHLEN; destruct (sc_logid x); clear; lia).
  lazymatch type of CELLS with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: C8 (Z_to_bv 64 (CtSctP.SctRep.logid_len (sc_logid x))) :: ?rest) =>
    apply (c8_small_as_c4 m _ [c0; c1; c2; c3; c4] (CtSctP.SctRep.logid_len (sc_logid x)) rest) in CELLS; [| clear - LLR; lia] end.
  cbn [app] in CELLS.
  assert (SEPS : adr (sc_blk x) + 104 <= spa \/ spa + 56 <= adr (sc_blk x)) by (clear - BSC CEILu LO'; lia).
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. zstep. zstep. try rewrite (sx32_small (CtSctP.SctRep.logid_len (sc_logid x))) by (clear - LLR; lia). zstep. zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename m into mold; rename mx into m end.
  assert (INV0 : sc_inv [] LB (C8 (Z_to_bv 64 f)) lv Σc m) by (eapply sc_inv_store; [exact INV'| exact MU| exact WM| exact MI| exact ST| exact FRL| reflexivity| exact FRH| intros b Hb; left; exact Hb]). clear dependent mold.
  assert (BIO0 : sc_bio m (((nw + zlength O_C4) mod 2 ^ 64 + zlength O_C5) mod 2 ^ 64)) by (split; [exact NW| unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz; exact HB]).
  apply evt_done.
  eapply sc_hex with (LBc := LB) (c24 := C8 (Z_to_bv 64 f)) (o := osz32 (sc_logid x)) (D := CtRepP.ApCells.optr adr (osz32 (sc_logid x))) (len := CtSctP.SctRep.logid_len (sc_logid x))
                    (retpc := 0x337f90) (used := used + 6) (budget := budget);
    [exact INV0| exact BIO0| clear - CR; lia| clear - U0; lia| clear - UB; lia| exact CRED
    | left; reflexivity| reflexivity| unfold CtSctP.W_sct_list_free.osz32, option_map, CtSctP.SctRep.logid_len, CtSctP.SctRep.olen; destruct (sc_logid x); reflexivity| clear - LLR; lia
    | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity
    | reflexivity| clear; lia| reflexivity|].
  intros t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d Fcd fcd m' Σc' nw' INV BIO CR' _.
  clear dependent m. clear dependent Σc. clear NW LBI SZ. try clear nw. rename m' into m. rename Σc' into Σc. rename CR' into CR. rename nw' into nw.
  pose proof INV as INV'. pose proof BIO as BIO'. destruct BIO as [NW HB]. open_inv INV.
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB. unfold sc_lo in FRL.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done.
  eapply sc_printf with (nw := nw) (LBc := LB) (c24 := C8 (Z_to_bv 64 f)) (A := A_C6_A) (fmt := FMT_C6) (args := [PA_i 8; PA_s []]) (o := O_C6) (retpc := 0x337fac)
                       (used := used + 6 + HX_CRED (CtSctP.SctRep.logid_len (sc_logid x))) (budget := budget);
    [exact INV'| exact BIO'| exact CR| clear - U0 HXN; lia| clear - UB; lia| exact CRED
    | exact vfmtA_C6| rewrite zlength_O_C6; clear; lia
    | cbn [vargsA_ok]; split; [cbn [vargA_ok]; rewrite unsigned_lit by (clear; lia); clear; split; [lia| reflexivity]|]; split; [apply emptyA_vargA| exact I]
    | reflexivity| reflexivity| reflexivity| clear; lia| reflexivity|].
  intros t0e t1e t2e a1e a2e a3e a4e a5e a6e a7e t3e t4e t5e t6e Fce fce m' Σc' INV BIO CR' _. clear dependent m. clear dependent Σc. rename m' into m. rename Σc' into Σc. rename CR' into CR. clear NW SZ LBI.
  pose proof INV as INV'. pose proof BIO as BIO'. destruct BIO as [NW HB]. open_inv INV.
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB. unfold sc_lo in FRL.
  pose proof REP as (_ & _ & CELLS & _). clear OFFS.
  ablock HEAP HSIN ACCS OFFS. unfold SCT_SIZE in ACCS, OFFS.
  pose proof (munch_refl [(spa, spa + 56)]%Z m) as MU.
  unfold CtSctP.SctRep.sct_cells, MallocRep.wz in CELLS.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. zstep.
  apply evt_done. eapply KTS; [exact INV'| exact BIO'| clear - CR; lia].
Qed.

(* [comment removed for export] *)
Lemma sc_inv_xfer : forall OWx OWx' LBc c24 lv Σc Σ' m m',
  sc_inv OWx LBc c24 lv Σc m -> AHEAP Σ' (OWx' ++ OW) LBc m' -> mem_inv ctasegs m' -> stk ctasegs m' lo spa ->
  agree_on (aclient_addr (OW ++ LB) spa) m m' ->
  sc_inv OWx' LBc c24 (rt_live RTS Σ') Σ' m'.
Proof.
  intros OWx OWx' LBc c24 lv Σc Σ' m m' INV HEAP' MI' ST' AG. destruct INV as (HEAP & LIVE & MI & ST & AGR & FRL & SZ & FRH & REP & LBI).
  pose proof (AH_ceil _ _ _ _ HEAP3) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  pose proof TOP as TOPu. unfold USTACK_TOP in TOPu.
  assert (LBI' : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> aclient_addr (OW ++ LB) spa a).
  { intros a [Ha|[Ha|Hb]]; [left; clear - Ha SPAH; lia| right; left; exact Ha| right; right; exact Hb]. }
  assert (SZL : Z.of_nat (cells_size (sc_lo c24)) = 56 + Z.of_nat g) by (unfold sc_lo; cbn [cells_size csize]; rewrite SZ; clear; lia).
  split; [exact HEAP'|]. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
  split. { eapply agree_on_trans; [exact AGR|]. eapply agree_on_mono; [exact AG|]. intros a [Ha _]. exact (LBI' a Ha). }
  split. { eapply rw_cells_agree; [exact AG| exact FRL|]. intros xa Hxa. rewrite SZL in Hxa. left. unfold USTACK_TOP. clear - Hxa TOPu SPAH SPAL GSZ. lia. }
  split; [exact SZ|].
  split. { eapply rw_cells_agree; [exact AG| exact FRH|]. intros xa Hxa. cbn in Hxa. left. unfold USTACK_TOP. clear - Hxa TOPu SPAH. lia. }
  split; [| exact LBI]. eapply sct_repA_agree; [exact REP|]. eapply agree_on_mono; [exact AG|]. intros a Ha.
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 sc_factsA)))) a Ha) as (_ & _ & C). exact (LBI' a C).
Qed.

Lemma sc_bio_xfer : forall m m' nw, sc_bio m nw -> agree_on (aclient_addr (OW ++ LB) spa) m m' -> sc_bio m' nw.
Proof.
  intros m m' nw [NW HB] AG. split; [exact NW|]. eapply rw_cells_agree; [exact AG| exact HB|]. intros xa Hxa. unfold bio_null_cells, bio_cells in Hxa. cbn in Hxa.
  right; right. exists (pb, out, 128). split; [apply in_or_app; left; exact HBIN| cbn; clear - Hxa; lia].
Qed.

Lemma sc_uw_xfer : forall m m' ras1, uw_chain USTACK_TOP m spa (bv_unsigned sp) ras1 -> agree_on (aclient_addr (OW ++ LB) spa) m m' ->
  uw_chain USTACK_TOP m' spa (bv_unsigned sp) ras1.
Proof. intros m m' ras1 UW AG. eapply uw_chain_agreeP; [exact AG| exact UW|]. intros a _ Ha. left. clear - Ha SPAH. lia. Qed.

End SC.
