(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApInv ApErr ApParse ApPrim ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts HxpInit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApIface ApWalkTac ApErrKit ApErrKit2 W_get_object W_get_object_walk W_c2i_int.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUbTab ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac ub1c :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let k := eval vm_compute in (ub_kind pc) in
      lazymatch k with
      | 1%Z => zstep
      | 2%Z => first [ (zstep; udecide) | uchk ]
      end
  end.
Local Ltac step := try udecide; repeat ub1c; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := try udecide; repeat ub1c; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 (Z_to_bv 64 ?z) => constr:(C1 (Z_to_bv 8 z))
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  | Z_to_le_bytes 1 ?z => constr:(C1 (Z_to_bv 8 z))
  end.

Ltac zc H := rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; try zsimp_in H; zify_bool H.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition CHECK_TLEN : Z := 0x11279c.
(* [comment removed for export] *)
Definition CHECK_TLEN_STACK : Z := 144 + GETOBJ_STACK.

(* [comment removed for export] *)
Lemma go_ret_prim : forall d op omax, let g := get_object d op omax in
  go_err g = None -> Z.land (go_ret g) 32 = 0 -> go_ret g = 0.
Proof.
  intros d op omax. cbn zeta. rewrite get_object_eq.
  destruct (omax <=? 0); [cbn; discriminate|]. destruct (go_hdr d op omax) as [[[tag p1] max1]|]; [|cbn; discriminate].
  destruct (get_length d p1 max1) as [[[inf len] p2]|]; [|cbn; discriminate].
  pose proof (land_32_cases (znth d op)) as C. unfold V_ASN1_CONSTRUCTED.
  destruct inf; cbn [andb].
  - destruct (Z.eqb_spec (Z.land (znth d op) 32) 0) as [E|E]; [cbn; discriminate|].
    destruct (omax - (p2 - op) <? len); cbn [go_err go_ret]; [discriminate|]. intros _ H. exfalso.
    destruct C as [C|C]; [lia|]. rewrite C in H. cbv in H. discriminate.
  - destruct (omax - (p2 - op) <? len); cbn [go_err go_ret]; [discriminate|]. intros _ H.
    destruct C as [C|C]; rewrite C; [reflexivity|]. rewrite C in H. cbv in H. discriminate.
Qed.

(* [comment removed for export] *)
Definition tlc_in (j31 : list byte) : list cell := [C1 (Z_to_bv 8 0); CB 31 j31].

(* [comment removed for export] *)
Lemma lx_pres_above : forall s OW LB SP SP' XC X m0 m m' lo,
  RHEAP s (OW ++ LB) m0 -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo ->
  lx_pres LB SP (XC ++ X) m m' -> SP <= SP' ->
  Forall (fun iv : Z * Z => lo <= fst iv /\ snd iv <= SP') XC ->
  lx_pres LB SP' X m m'.
Proof.
  intros s OW LB SP SP' XC X m0 m m' lo HEAP CEIL GLO LX LE HXC a Ha [HX Hc]. apply LX; [exact Ha|]. unfold GLOBALS_TOP in GLO.
  assert (OUT : ~ rin_ivs XC a).
  { clear LX HX. induction XC as [|[x y] XC IH]; cbn [rin_ivs fst snd]; [tauto|].
    apply Forall_cons_iff in HXC. destruct HXC as [[H1 H2] H3]. cbn [fst snd] in H1, H2.
    intros [Hin|Hin]; [| exact (IH H3 Hin)].
    destruct Hc as [Hc|[(b & Hb & Hr)|Hc]]; [lia| | unfold ralloc_static in Hc; lia].
    destruct b as [[q A] n]. cbn [blk_addr blk_size fst snd] in Hr.
    pose proof (blk_bounds _ _ _ q A n HEAP ltac:(apply in_app_iff; right; exact Hb)). lia. }
  split.
  - intros Hin. apply rin_ivs_app in Hin. destruct Hin as [Hin|Hin]; [exact (OUT Hin)| exact (HX Hin)].
  - destruct Hc as [Hc|Hc]; [left; lia| right; exact Hc].
Qed.

(* [comment removed for export] *)
Lemma implM_aret_evt : forall {A} (a : A) (st : ap_st bptr) s Q ms,
  implM ctusegs (interp (ap_embed (aret a st))) s Q ms -> evt ctusegs (Q (a, st) s) ms.
Proof. intros A a st s Q ms H. exact H. Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Hypothesis HGO : ASN1_get_object_spec.

  Theorem check_tlen_walk : forall
      (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
      (lo B : Z) (errv canary : word) (K : list block)
      (D : Z) (d : list Z) (op totlen exptag POLEN PINF PCST PPC TLC : Z) (jl : list byte) (bi bc : byte) (j31 : list byte)
      (POST : machine_state -> Prop),
    ap_pre s st m OW LB E bo sp lo B errv canary CHECK_TLEN_STACK -> tp = wz RATP -> frm0 fc ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) ->
    payload_ok m LB D d -> 0 <= op -> 0 < totlen -> op + totlen <= zlength d ->
    go_err (get_object d op totlen) = None -> go_tag (get_object d op totlen) = exptag -> go_cls (get_object d op totlen) = 0 ->
    Z.land (go_ret (get_object d op totlen)) 32 = 0 -> 0 <= exptag < 2^31 ->
    (* [comment removed for export] *)
    bv_unsigned sp <= PPC -> PPC + 8 <= PINF -> PINF + 1 = PCST -> PCST + 1 <= POLEN -> POLEN + 8 <= TLC -> TLC + 32 <= B ->
    PPC mod 8 = 0 -> POLEN mod 8 = 0 -> TLC mod 8 = 0 ->
    rw_cells ctusegs m POLEN [CB 8 jl] -> rw_cells ctusegs m PINF [C1 bi] -> rw_cells ctusegs m PCST [C1 bc] ->
    rw_cells ctusegs m PPC [C8 (wz (D + op))] -> rw_cells ctusegs m TLC (tlc_in j31) ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (OW' : list block) (errv' : word) (jt : list byte),
       frm0 fc' -> (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k) ->
       ap_pre s st m' OW' LB E bo sp lo B errv' canary 0 ->
       lx_pres LB (bv_unsigned sp) ([(POLEN, POLEN + 8); (PINF, PINF + 1); (PCST, PCST + 1); (PPC, PPC + 8); (TLC, TLC + 32)] ++ LIBW_AP) m m' ->
       blocks_kept K st OW' m m' ->
       rw_cells ctusegs m' POLEN [C8 (wz (go_len (get_object d op totlen)))] -> rw_cells ctusegs m' PINF [C1 (Z_to_bv 8 0)] -> rw_cells ctusegs m' PCST [C1 (Z_to_bv 8 0)] ->
       rw_cells ctusegs m' PPC [C8 (wz (D + go_p (get_object d op totlen)))] -> rw_cells ctusegs m' TLC [CB 32 jt] ->
       evt ctusegs POST
         (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (ret_pc ra) fc' None m' (seg_rom ctusegs))) ->
    evt ctusegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz POLEN) (wz 0) (wz 0) (wz PINF) (wz PCST) (wz PPC) (wz totlen) (wz exptag) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               (wz 0) (wz 0) (wz TLC) t6)
          F (wz CHECK_TLEN) fc None m (seg_rom ctusegs)).
  Proof using HGO.
    intros until POST. intros PRE TP FRM KOW KIDS PAY OP0 TL0 OPT EG ETAG ECLS ERET XT SPP A1 A2 A3 A4 A5 APPC AOLEN ATLC HOLEN HINF HCST HPPC HTLC KONT.
    set (g := get_object d op totlen) in *.
    pose proof PRE as PRE0.
    destruct PRE as (HEAP & AS & IDS & DC & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & SSP & MI & SP16).
    pose proof PAY as (HB & PF & D0 & D63 & D30 & HBLK).
    destruct HBLK as [->|(blk & HPB & PA1 & PA2)]; [exfalso; unfold zlength in OPT; cbn in OPT; lia|].
    destruct blk as [[pb PA] psz]. cbn [blk_addr blk_size fst snd] in PA1, PA2.
    pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_app_iff; right; exact HPB)) as (BB0 & BB1 & BB2 & BB3 & BB4). cbn [blk_addr blk_size fst snd] in BB0, BB1, BB2, BB3, BB4.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (EA : errno_addr (Z_to_bv 64 RATP) = 3355012) by (unfold errno_addr, RATP; rewrite unsigned_lit by lia; reflexivity).
    unfold MallocRep.wz in ERR. rewrite EA in ERR.
    assert (DLEN : Z.of_nat (length (to_bytes d)) = zlength d) by apply zlength_to_bytes.
    pose proof (get_object_bounds d op totlen ltac:(eapply Forall_impl; [| exact PF]; cbv beta; intros; lia) TL0) as GB. cbv zeta in GB. fold g in GB. rewrite EG in GB.
    destruct GB as (GB1 & GB2 & GB3).
    pose proof (go_ret_prim d op totlen EG ERET) as RET0. fold g in RET0.
    unfold CHECK_TLEN_STACK, GETOBJ_STACK, ERR_SET_ERROR_STACK, GLOBALS_TOP, CHECK_TLEN, MallocRep.wz in *.
    pose proof (munch_refl [(bv_unsigned sp - 8592, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -144)) = bv_unsigned sp + -144) by (apply unsigned_lit; lia).
    unfold tlc_in in HTLC.
    subst tp.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUp.
    repeat match goal with H : rw_cells ctusegs m _ _ |- _ => let T := type of H in change (frozen T) in H
                          | H : ro_cells ctusegs m _ _ |- _ => let T := type of H in change (frozen T) in H
                          | H : bytes_at ctusegs m _ _ |- _ => let T := type of H in change (frozen T) in H end.
    carve_frame 144%nat ST. do 15 step.
    name_mem mP. unfold frozen in *.
    match goal with W : wmono ctusegs m mP |- _ => transport_after_call ctusegs m mP MUp W end. clear MUp.
    step. step. step.
    step. step. step. step. if_cases KLEN; zc KLEN.
    { exfalso. revert KLEN. rewrite ?signed_small by lia. lia. }
    do 5 step. step.
    step. if_cases KCTX; zc KCTX; [exfalso; lia|].
    step. step. step. if_cases KVAL; zc KVAL; [| exfalso; apply KVAL; reflexivity].
    step. do 4 step. step.
    name_mem m1.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: CB 16 ?j :: ?rest) =>
      change (c0 :: c1 :: c2 :: CB 16 j :: rest) with ([c0; c1] ++ [c2] ++ [CB 16 j] ++ rest) in FR end.
    apply rw_cells_app in FR. destruct FR as [FRA FR]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR.
    apply rw_cells_app in FR. destruct FR as [FRP FR]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR.
    apply rw_cells_app in FR. destruct FR as [FRX FRS]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRS.
    replace (bv_unsigned sp + -144 + 16) with (bv_unsigned sp + -128) in FRP by lia.
    replace (bv_unsigned sp + -144 + 16 + 8) with (bv_unsigned sp + -120) in FRX by lia.
    replace (bv_unsigned sp + -144 + 16 + 8 + 16) with (bv_unsigned sp + -104) in FRS by lia.
    lazymatch type of FRX with rw_cells _ _ _ [CB 16 ?jj] => set (jx := jj) in FRX; clearbody jx end.
    assert (FRX' : rw_cells ctusegs m1 (bv_unsigned sp + -120) [CB 8 (firstn 8 jx); CB 4 (firstn 4 (skipn 8 jx)); CB 4 (skipn 12 jx)]).
    { pose proof FRX as [[Wf _] _]. cbn in Wf. destruct Wf as [L16 _].
      eapply rw_cells_recast; [exact FRX| cbn; rewrite !length_firstn, !length_skipn; repeat split; first [lia | exact I]| | cbn; lia].
      cbn [cells_bytes cbytes app]. rewrite !app_nil_r.
      transitivity (firstn 8 jx ++ skipn 8 jx); [| apply firstn_skipn]. f_equal.
      transitivity (firstn 4 (skipn 8 jx) ++ skipn 4 (skipn 8 jx)); [| apply firstn_skipn]. f_equal. rewrite skipn_skipn. reflexivity. }
    clear FRX.
    lazymatch type of FRX' with rw_cells _ _ _ [?c1; ?c2; ?c3] => change [c1; c2; c3] with ([c1] ++ [c2] ++ [c3]) in FRX' end.
    apply rw_cells_app in FRX'. destruct FRX' as [FRL FRX']. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRX'.
    apply rw_cells_app in FRX'. destruct FRX' as [FRC FRT]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRT.
    replace (bv_unsigned sp + -120 + 8) with (bv_unsigned sp + -112) in FRC by lia.
    replace (bv_unsigned sp + -120 + 8 + 4) with (bv_unsigned sp + -108) in FRT by lia.
    assert (PRE1 : ap_pre s st m1 OW LB E bo (Z_to_bv 64 (bv_unsigned sp + -144)) lo B errv canary GETOBJ_STACK).
    { eapply (ap_pre_seg s st m m1); [exact PRE0| exact MU| exact WM| exact MI| rewrite ESP; exact ST| | rewrite ESP; unfold GETOBJ_STACK, ERR_SET_ERROR_STACK; lia| rewrite ESP; lia
        | rewrite ESP; replace (bv_unsigned sp + -144) with (bv_unsigned sp - 144) by lia; rewrite Zminus_mod, SP16; reflexivity| exact ERR].
      constructor; [cbn; lia| constructor]. }
    assert (PAY1 : payload_ok m1 LB D d).
    { split; [exact HB|]. split; [exact PF|]. split; [lia|]. split; [lia|]. split; [lia|]. right. exists (pb, PA, psz). split; [exact HPB|]. cbn. lia. }
    assert (LX1 : forall X, lx_pres LB (bv_unsigned sp) X m m1).
    { intros X. eapply lx_pres_of_munch; [exact MU| exact WM|]. intros a Ha [HX Hc]. cbn. split; [| exact I].
      destruct Hc as [Hc|[(b & Hb & Hr)|Hc]]; [lia| | unfold ralloc_static in Hc; lia].
      destruct b as [[q A] n]. cbn [blk_addr blk_size fst snd] in Hr.
      pose proof (blk_bounds _ _ _ q A n HEAP ltac:(apply in_app_iff; right; exact Hb)). lia. }
    assert (KP1 : kept K m m1).
    { eapply (kept_stack s OW LB); [exact HEAP| exact KOW| exact CEIL| exact MU|]. constructor; [cbn; lia| constructor]. }
    (* [comment removed for export] *)
    eapply evt_cut.
    { apply (implM_aret_evt tt st s). replace (aret tt st) with (go_eff g st) by (unfold go_eff; rewrite EG; reflexivity).
      pose proof HGO as W. unfold ASN1_get_object_spec in W.
      eapply W with (K := K) (d := d) (op := op) (omax := totlen)
                      (PP := bv_unsigned sp + -128) (PL := bv_unsigned sp + -120) (PT := bv_unsigned sp + -108) (PC := bv_unsigned sp + -112);
        [ exact PRE1 | reflexivity | exact FRM | exact KOW | exact KIDS
        | exact PAY1 | lia | lia | lia
        | rewrite ESP; unfold go_cells_ok; lia | lia | lia | lia | lia
        | exact FRP | exact FRL | exact FRT | exact FRC
        | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity ]. }
    cbv beta. intros ms2 PO2. unfold getobj_post in PO2. fold g in PO2. rewrite EG in PO2. rewrite ?ESP in PO2.
    destruct PO2 as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & F2 & fc2 & m2 & OW2 & errv2 & jl' & j2' & j3'
                     & -> & FRM2 & FEQ2 & PRE2 & LX2 & SO2 & FA2 & BK2 & HPP2 & -> & HPL2 & HPT2 & HPC2).
    unfold MallocRep.wz in HPP2, HPL2, HPT2, HPC2. rewrite RET0. rewrite ETAG in HPT2. rewrite ECLS in HPC2.
    replace (ret_pc (Z_to_bv 64 (1124564 + 4))) with (Z_to_bv 64 1124568) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof PRE2 as (HEAP2 & AS2 & IDS2 & DC2 & AUX2 & _ & _ & ST2 & _ & _ & _ & ERR2 & SSP2 & MI2 & _). rewrite ESP in ST2.
    unfold MallocRep.wz in ERR2. rewrite EA in ERR2.
    pose proof (agree_of_lx_pres _ _ _ _ _ LX2) as AG2.
    assert (CL : forall a, bv_unsigned sp + -104 <= a \/ (bv_unsigned sp + -144 <= a < bv_unsigned sp + -128) ->
                 lx_client LB (bv_unsigned sp + -144) ([(bv_unsigned sp + -128, bv_unsigned sp + -128 + 8); (bv_unsigned sp + -120, bv_unsigned sp + -120 + 8);
                                                        (bv_unsigned sp + -108, bv_unsigned sp + -108 + 4); (bv_unsigned sp + -112, bv_unsigned sp + -112 + 4)] ++ LIBW_AP) a).
    { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd app]; lia| left; lia]. }
    apply (rw_cells_agree _ _ _ _ _ AG2) in FRA; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in FRS; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in HOLEN; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in HINF; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in HCST; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in HPPC; [| intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AG2) in HTLC; [| intros a Ha; apply CL; cbn in Ha; lia].
    clear AG2 CL MU WM MI ST ERR HB FRP FRL FRC FRT.
    pose proof (munch_refl [(bv_unsigned sp - 8592, bv_unsigned sp); (POLEN, POLEN + 8); (PINF, PINF + 1); (PCST, PCST + 1); (PPC, PPC + 8); (TLC, TLC + 32)]%Z m2) as MU.
    pose proof (wmono_refl ctusegs m2) as WM.
    unfold MallocRep.wz.
    (* [comment removed for export] *)
    step. step. step. step. step.
    step. step. step. step.
    step. step. step. step. rewrite ?unsigned_lit by lia.
    replace (bv_swrap 32 (D + go_p g - (D + op))) with (go_p g - op) by (rewrite swrap32_small by lia; lia).
    change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
    step. if_false.
    step. step. if_cases KTL; zc KTL; [| exfalso; revert KTL; rewrite ?signed_small by lia; lia].
    step. step. if_false.
    step. if_cases KXN; zc KXN; [exfalso; revert KXN; rewrite ?signed_small by lia; lia|].
    step. rewrite (sx32_small exptag) by lia. step. if_false.
    step. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0). step. if_false.
    step. if_cases KC2; zc KC2; [exfalso; lia|].
    step. step. step. if_true.
    step. if_cases KI; zc KI; [exfalso; lia|]. step.
    step. if_cases KS; zc KS; [exfalso; lia|]. zstep. step.
    step. if_cases KO; zc KO; [exfalso; lia|]. step. step.
    step. if_true. step. if_true.
    step. step. step. step.
    do 13 step. step.
    release_frame FRA ST2 (bv_unsigned sp + -128). release_frame HPP2 ST2 (bv_unsigned sp + -120). release_frame HPL2 ST2 (bv_unsigned sp + -112).
    release_frame HPC2 ST2 (bv_unsigned sp + -108). release_frame HPT2 ST2 (bv_unsigned sp + -104). release_frame FRS ST2 (bv_unsigned sp).
    step. name_mem mF.
    assert (HW : Forall (fun iv : Z * Z => lo <= fst iv /\ snd iv <= B)
                   [(bv_unsigned sp - 8592, bv_unsigned sp); (POLEN, POLEN + 8); (PINF, PINF + 1); (PCST, PCST + 1); (PPC, PPC + 8); (TLC, TLC + 32)]%Z).
    { repeat (constructor; [cbn; lia|]). constructor. }
    eapply KONT with (jt := cells_bytes _).
    - exact FRM2.
    - exact FEQ2.
    - eapply (ap_pre_seg s st m2 mF) with (stack := 0); [exact PRE2| exact MU| exact WM| exact MI2| exact ST2| exact HW| lia| lia| exact SP16| ].
      match goal with H : rw_cells ctusegs mF 3355012 _ |- _ => exact H end.
    - eapply lx_pres_trans; [apply LX1|]. eapply lx_pres_trans.
      + eapply lx_pres_weaken; [| apply Z.le_refl| intros b Hb; exact Hb| intros a Ha; apply rin_ivs_app; right; exact Ha].
        eapply (lx_pres_above s OW LB) with (lo := lo); [exact HEAP| exact CEIL| unfold GLOBALS_TOP; lia| exact LX2| lia|].
        repeat (constructor; [cbn; lia|]). constructor.
      + eapply lx_pres_of_munch; [exact MU| exact WM|]. intros a Ha [HX Hc]. cbn [rin_ivs app fst snd] in HX. apply seg_outside.
        constructor.
        { (* [comment removed for export] *)
          cbn [fst snd]. destruct Hc as [Hc|[(b & Hb & Hr)|Hc]]; [clear - Hc; lia| | unfold ralloc_static in Hc; clear - Hc GLO LO; lia].
          destruct b as [[q A] n]. cbn [blk_addr blk_size fst snd] in Hr.
          pose proof (blk_bounds _ _ _ q A n HEAP ltac:(apply in_app_iff; right; exact Hb)) as BBX. clear - Hr BBX CEIL LO. lia. }
        constructor; [cbn [fst snd]; intros Hin; apply HX; left; exact Hin|].
        constructor; [cbn [fst snd]; intros Hin; apply HX; right; left; exact Hin|].
        constructor; [cbn [fst snd]; intros Hin; apply HX; right; right; left; exact Hin|].
        constructor; [cbn [fst snd]; intros Hin; apply HX; right; right; right; left; exact Hin|].
        constructor; [cbn [fst snd]; intros Hin; apply HX; right; right; right; right; left; exact Hin|]. constructor.
    - destruct BK2 as (K1 & K2 & K3). split; [exact K1|]. split; [exact K2|].
      eapply kept_trans; [exact KP1|]. eapply kept_trans; [exact K3|].
      eapply (kept_of_munch s (OW2 ++ LB) _ m2 mF K lo); [exact HEAP2| intros b Hb; apply in_app_iff; left; exact (K1 b Hb)| exact CEIL| exact MU|].
      eapply Forall_impl; [| exact HW]. intros iv [Hx Hy]. left. exact Hx.
    - exact HOLEN.
    - exact HINF.
    - exact HCST.
    - exact HPPC.
    - apply rw_cells_CB_of in HTLC. exact HTLC.
  Qed.
End Proofs.
End WithCeiling0.
