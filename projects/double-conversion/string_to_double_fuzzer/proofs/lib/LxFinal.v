(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Wellfounded.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk LibIface BnContract.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LxLin LxState LxMem LxStep LxCheck LxSem LxWf LxSoundVal LxSoundMem LxSoundMem2
     LxOrder LxOrderWf LxSoundStep LxSoundMatch LxSoundExplore LxGlue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import LXL LXS LXM LXI LXC LXSEM LXWF LXSV LXSM.
Open Scope Z_scope.

Module LXF.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ms_eta : forall ms : machine_state,
  ms_svc_pending ms = None -> ms_resv ms = None ->
  ms = @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (ms_rom ms).
Proof. intros [regs fregs pc svc resv fcsr mem rom] Hs Hr. cbn in *. subst. reflexivity. Qed.

Lemma w64_lit : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (w64 a) = a.
Proof. intros a Ha. unfold w64. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. Qed.

Lemma w64_succ : forall a, (w64 a + 1)%bv = w64 (a + 1).
Proof.
  intros a. apply bv_eq. unfold w64. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod. change (bv_wrap 64 1) with 1.
  rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdn_ext : forall segs (m m' : word -> option byte) n a,
  (forall i, 0 <= i < Z.of_nat n -> m' (w64 (a + i)) = m (w64 (a + i))) ->
  rdn segs m' (w64 a) n = rdn segs m (w64 a) n.
Proof.
  intros segs m m' n. induction n as [|n IH]; intros a Hag; [reflexivity|].
  cbn [rdn]. pose proof (Hag 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. rewrite H0.
  rewrite w64_succ. rewrite (IH (a + 1)) by (intros i Hi; replace (a + 1 + i) with (a + (1 + i)) by lia; apply Hag; lia).
  reflexivity.
Qed.

Lemma havoc_regs_get : forall rs i j,
  list_get (havoc_regs rs i) j Top = if existsb (Nat.eqb (i + j)%nat) keep_regs then list_get rs j Top else Top.
Proof.
  induction rs as [|v r IH]; intros i j; cbn [havoc_regs list_get].
  - destruct (existsb _ _); reflexivity.
  - destruct j as [|j]; [rewrite Nat.add_0_r; reflexivity|].
    rewrite IH. replace (S i + j)%nat with (i + S j)%nat by lia. reflexivity.
Qed.

Lemma list_get_below : forall rs n r, forallb (fun v => aval_below v n) rs = true -> aval_below (list_get rs r Top) n = true.
Proof.
  induction rs as [|v l IH]; intros n r H; [destruct r; reflexivity|].
  cbn [forallb] in H. apply andb_prop in H as [H1 H2]. destruct r; cbn [list_get]; [exact H1 | apply IH; exact H2].
Qed.

Lemma keep_cs : forall k : nat, existsb (Nat.eqb k) keep_regs = true -> In (Z.of_nat k) cs_regs.
Proof.
  intros k H. apply existsb_exists in H as (k' & Hin & E). apply Nat.eqb_eq in E. subst k'.
  unfold keep_regs in Hin. unfold cs_regs. cbn [In] in Hin.
  repeat (destruct Hin as [<-|Hin]; [cbn; tauto|]). destruct Hin.
Qed.

(* [comment removed for export] *)
Lemma decode_exec_rom : forall segs ms w ms',
  drop_access_report (decode_exec_accesses segs ms w) = MachineOk ms' -> ms_rom ms' = ms_rom ms.
Proof.
  intros segs ms w ms' H. unfold decode_exec_accesses in H.
  destruct (is_ecall w); [cbn in H; injection H as <-; reflexivity|].
  destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
  match type of H with context [interp_eff_accesses ?a ?b ?c] => destruct (interp_eff_accesses a b c) as [rep| |] end; try discriminate.
  destruct rep as [[c m] acc]. cbn in H. injection H as <-. reflexivity.
Qed.

Lemma step_rom : forall segs ms ms', RiscvSemantics.step segs ms = MachineOk ms' -> ms_rom ms' = ms_rom ms.
Proof.
  intros segs ms ms' H. unfold RiscvSemantics.step, step_accesses in H.
  destruct (fetch_word segs (ms_pc ms)) as [w|]; [eapply decode_exec_rom; exact H|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|]; [eapply decode_exec_rom; exact H|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|]; [eapply decode_exec_rom; exact H|].
  unfold fetch_failure in H. destruct (negb _); [discriminate|].
  match type of H with context [if ?t then MachineFault else MachineUnmodeled] => destruct t; discriminate end.
Qed.

Lemma msteps_rom : forall segs ms ms', msteps segs ms ms' -> ms_rom ms' = ms_rom ms.
Proof.
  intros segs ms ms' H. induction H as [ms | ms ms1 ms2 Hsvc Hstep Hms IH]; [reflexivity|].
  rewrite IH. eapply step_rom. exact Hstep.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CBD.
  Variable U : uenv.
  Variable G : sym -> Z.
  Variable M0 : word -> option byte.
  Hypothesis UOK : uenv_ok U.
  Hypothesis HCBD : cbd_stmt (ue_segs U) (ue_cbd_pc U) (ue_cbd_fr U).
  Let segs := ue_segs U.

  (* [comment removed for export] *)
  Lemma reg_ok : forall rho S ms r, R U G M0 rho S ms -> (1 <= r < 32)%nat ->
    val_ok rho (getreg S r) (getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat r))).
  Proof.
    intros rho S ms r HR Hr. unfold getreg. destruct (Nat.eqb_spec r 0); [lia|].
    rewrite <- (LXG.getr_reg_get (ms_regs ms) r Hr). exact (r_regs _ _ _ _ _ _ HR r Hr).
  Qed.

  Theorem apply_cbd_sound : forall rho S S' ms,
    wf_state S = true -> R U G M0 rho S ms -> apply_cbd U S = Some S' ->
    exists ms' rho', msteps (ue_segs U) ms ms' /\ R U G M0 rho' S' ms' /\ agree (s_next S) rho rho' /\ (s_next S <= s_next S')%nat.
  Proof.
    intros rho S S' ms Hwf HR H.
    destruct (wf_parts S Hwf) as (Wregs & Wctx & Wstk & Warrs & Wpc & Wpay & Wdisj & W18 & Wcw & Wad).
    pose proof (r_vs _ _ _ _ _ _ HR) as HVS. destruct HVS as [HC HCB].
    (* [comment removed for export] *)
    unfold apply_cbd in H.
    destruct (Z.eqb_spec (s_pc S) (ue_cbd_pc U)) as [EPC|]; [|discriminate].
    destruct (in_ranges 0x13a88 48 (ue_ro U)) eqn:HTBL; [|discriminate].
    destruct (Z.leb_spec 0 (ue_cbd_fr U)) as [HFR0|]; [|discriminate]. cbn [negb] in H.
    destruct (sp_off S) as [k|] eqn:Hsp; [|discriminate].
    destruct (getreg S 1) as [|lra|? ? ? ?|? ?] eqn:G1; try discriminate.
    destruct (getreg S 11) as [|l1|? ? ? ?|? ?] eqn:G11; try discriminate.
    destruct (getreg S 12) as [|l2|? ? ? ?|? ?] eqn:G12; try discriminate.
    destruct (getreg S 14) as [|l4|? ? ? ?|? ?] eqn:G14; try discriminate.
    destruct (is_const lra) as [ra|] eqn:Hra; [|discriminate].
    unfold sext32_view in H.
    destruct (sexact32 (s_ctx S) l1) eqn:X1; [|discriminate].
    destruct (low32s_view (s_ctx S) l4) as [l4s|] eqn:X4; [|discriminate].
    destruct (in_window U (k - ue_cbd_fr U) (ue_cbd_fr U)) eqn:HWIN; [|discriminate].
    destruct (Z.eqb_spec (k mod 16) 0) as [HK16|]; [|discriminate].
    destruct (Z.eqb_spec (ra mod 4) 0) as [HRA4|]; [|discriminate].
    destruct (Z.leb_spec 0 ra) as [HRA0|]; [|discriminate].
    destruct (Z.ltb_spec ra two64) as [HRA64|]; [|discriminate]. cbn [negb] in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
    apply andb_prop in COND as [COND HRESV]. apply andb_prop in COND as [COND NOSTR]. apply andb_prop in COND as [COND OKE].
    apply andb_prop in COND as [COND OKEXP]. apply andb_prop in COND as [OKBUF OKLEN].
    destruct (s_resv S) eqn:ERESV; [discriminate|].
    apply andb_prop in NOSTR as [NOSTRc NOSTRa].
    apply andb_prop in OKLEN as [LEN1 LEN2]. apply andb_prop in OKEXP as [OKEXP EXP2]. apply andb_prop in OKEXP as [_ EXP1].
    apply andb_prop in OKE as [E1 E2].
    destruct (fresh_val (set_regs (drop_below S k) (havoc_regs (s_regs (drop_below S k)) 0)) (Itv (Some (-1)) (Some 1)))
      as [rv S3] eqn:Hfv.
    injection H as ES'.
    (* [comment removed for export] *)
    set (sp0 := rho SYM_SP0) in *. set (fr := ue_cbd_fr U) in *.
    set (len := evl rho l1). set (expo := evl rho l2). set (e := evl rho l4s). set (a4 := evl rho l4). set (sp := sp0 + k).
    assert (HA4 : a4 mod 2 ^ 32 = e mod 2 ^ 32).
    { subst e a4. unfold low32s_view in X4. destruct (sexact32 (s_ctx S) l4); [injection X4; intros <-; reflexivity|].
      destruct (in_range (s_ctx S) l4 two31 two32); [|discriminate]. injection X4; intros <-.
      rewrite laddc_sound, (Zplus_mod (evl rho l4)). replace ((- two32) mod 2 ^ 32) with 0 by reflexivity.
      rewrite Z.add_0_r, Z.mod_mod by lia. reflexivity. }
    pose proof (entails_sound rho _ _ None HC LEN1) as NL1. rewrite laddc_sound in NL1.
    pose proof (entails_sound rho _ _ None HC LEN2) as NL2. rewrite laddc_sound, lneg_sound in NL2.
    pose proof (entails_sound rho _ _ None HC EXP1) as NX1. rewrite laddc_sound, ladd_sound in NX1.
    pose proof (entails_sound rho _ _ None HC EXP2) as NX2. rewrite laddc_sound, lneg_sound, ladd_sound in NX2.
    pose proof (entails_sound rho _ _ None HC E1) as NE1. rewrite laddc_sound in NE1.
    pose proof (entails_sound rho _ _ None HC E2) as NE2. rewrite laddc_sound, lneg_sound in NE2.
    fold len in NL1, NL2, NX1, NX2. fold expo in NX1, NX2. fold e in NE1, NE2.
    apply LXSMT.in_window_sound in HWIN. destruct HWIN as [HW1 HW2].
    pose proof (r_sp0 _ _ _ _ _ _ HR) as [SP1 SP2]. pose proof (r_align _ _ _ _ _ _ HR) as [AL1 AL2].
    pose proof (uo_fr U UOK) as UFR. fold sp0 in SP1, SP2, AL1.
    (* [comment removed for export] *)
    pose proof (reg_ok rho S ms 1 HR ltac:(lia)) as R1. rewrite G1 in R1. cbn [val_ok] in R1. rewrite (is_const_sound rho lra ra Hra) in R1.
    pose proof (reg_ok rho S ms 2 HR ltac:(lia)) as R2.
    pose proof (LXSM2.classify_spec rho (getreg S 2) _ (s_next S) R2 (LXSS.getreg_below S 2 Hwf) W18) as CL2.
    unfold sp_off in Hsp. destruct (classify (getreg S 2)) as [[k'|?|?|?]|]; try discriminate. injection Hsp as ->. fold sp0 in CL2.
    pose proof (reg_ok rho S ms 11 HR ltac:(lia)) as R11. rewrite G11 in R11. cbn [val_ok] in R11. fold len in R11.
    pose proof (reg_ok rho S ms 12 HR ltac:(lia)) as R12. rewrite G12 in R12. cbn [val_ok] in R12. fold expo in R12.
    pose proof (reg_ok rho S ms 14 HR ltac:(lia)) as R14. rewrite G14 in R14. cbn [val_ok] in R14. fold a4 in R14.
    pose proof (reg_ok rho S ms 10 HR ltac:(lia)) as R10.
    (* [comment removed for export] *)
    assert (BUF : exists buf, getr (ms_regs ms) (Z_to_bv 5 10) = w64 buf /\ sp <= buf /\
                  exists a f, In a (s_arrs S) /\ ar_fact a = Some f /\ af_blo f = 48 /\ af_bhi f = 57 /\
                              ar_lo a <= buf - sp0 /\ buf - sp0 + len <= ar_lo a + evl rho (af_len f)).
    { pose proof (LXSM2.classify_spec rho (getreg S 10) _ (s_next S) R10 (LXSS.getreg_below S 10 Hwf) W18) as CL10.
      destruct (classify (getreg S 10)) as [[off|off|?|?]|]; try discriminate.
      - destruct (arr_find (s_arrs S) (s_ctx S) (lconst off) 1) as [a|] eqn:Hfind; [|discriminate].
        destruct (ar_fact a) as [f|] eqn:Hf; [|discriminate].
        apply andb_prop in OKBUF as [OKBUF Hcov]. apply andb_prop in OKBUF as [OKBUF Hbhi]. apply andb_prop in OKBUF as [Hk Hblo].
        apply Z.leb_le in Hk. apply Z.eqb_eq in Hblo. apply Z.eqb_eq in Hbhi.
        destruct (LXSM2.arr_find_spec rho _ _ _ _ _ HC Hfind) as (Hin & Hlo & _). rewrite lconst_sound in Hlo.
        pose proof (entails_sound rho _ _ None HC Hcov) as Hc. rewrite lsub_sound, !laddc_sound in Hc. fold len in Hc.
        exists (sp0 + off). split; [exact CL10|]. split; [unfold sp; lia|].
        exists a, f. repeat split; try assumption; lia.
      - destruct CL10 as [CL10 _].
        destruct (arr_find (s_arrs S) (s_ctx S) off 1) as [a|] eqn:Hfind; [|discriminate].
        destruct (ar_fact a) as [f|] eqn:Hf; [|discriminate].
        apply andb_prop in OKBUF as [OKBUF Hcov]. apply andb_prop in OKBUF as [OKBUF Hbhi]. apply andb_prop in OKBUF as [Hk Hblo].
        apply Z.eqb_eq in Hblo. apply Z.eqb_eq in Hbhi.
        pose proof (entails_sound rho _ _ None HC Hk) as Hk'. rewrite laddc_sound in Hk'.
        destruct (LXSM2.arr_find_spec rho _ _ _ _ _ HC Hfind) as (Hin & Hlo & _).
        pose proof (entails_sound rho _ _ None HC Hcov) as Hc. rewrite lsub_sound, laddc_sound, ladd_sound in Hc. fold len in Hc.
        exists (sp0 + evl rho off). split; [exact CL10|]. split; [unfold sp; lia|].
        exists a, f. repeat split; try assumption; lia. }
    clear OKBUF R10. destruct BUF as (buf & R10 & Hspbuf & a & f & Hina & Hf & Hblo & Hbhi & Hlo & Hcov).
    pose proof (proj1 (Forall_forall _ _) (r_arrs _ _ _ _ _ _ HR) a Hina) as AOK. fold sp0 in AOK.
    assert (DIG : forall i, 0 <= i < len -> sp0 + ar_lo a + (buf - sp0 - ar_lo a + i) < sp0 + ar_hi a /\
              exists d, rdn segs (ms_mem ms) (Z_to_bv 64 (buf + i)) 1 = Some [d] /\ 48 <= bv_unsigned d <= 57).
    { intros i Hi.
      destruct (LXSM2.arr_fact_byte U rho (ms_mem ms) sp0 a f (buf - sp0 - ar_lo a + i) AOK Hf ltac:(lia)) as (d & Hrd & _ & Hd & _).
      split.
      - destruct AOK as (_ & _ & AF). rewrite Hf in AF. destruct AF as (_ & _ & AF & _). pose proof (proj1 (AF (buf - sp0 - ar_lo a + i) ltac:(lia))). lia.
      - exists d. replace (buf + i) with (sp0 + ar_lo a + (buf - sp0 - ar_lo a + i)) by lia.
        split; [exact Hrd | rewrite Hblo, Hbhi in Hd; exact Hd]. }
    assert (ARHI : ar_hi a <= 0) by (destruct AOK as (_ & X & _); exact X).
    assert (BUFHI : buf + len <= sp0) by (pose proof (proj1 (DIG (len - 1) ltac:(lia))); lia).
    (* [comment removed for export] *)
    pose proof (r_resv _ _ _ _ _ _ HR) as RRESV. rewrite ERESV in RRESV. cbn [resv_ok] in RRESV.
    destruct (ms_resv ms) eqn:EMR; [destruct RRESV|].
    pose proof (ms_eta ms (r_svc _ _ _ _ _ _ HR) EMR) as ETA.
    set (fx := mkFP (ms_fregs ms) (ms_fcsr ms)) in ETA.
    rewrite (r_pc _ _ _ _ _ _ HR), EPC in ETA.
    (* [comment removed for export] *)
    destruct (r_win _ _ _ _ _ _ HR) as [WDEF WSEG]. fold sp0 in WDEF, WSEG.
    assert (STOK : store_ok segs (ms_mem ms) (Z_to_bv 64 (sp - fr)) (Z.to_nat fr) = true).
    { apply store_ok_of_all; [change (Z_to_bv 64 (sp - fr)) with (w64 (sp - fr)); rewrite w64_lit, Z2Nat.id by lia; unfold sp; lia|].
      intros x Hx. change (Z_to_bv 64 (sp - fr)) with (w64 (sp - fr)) in Hx. rewrite w64_lit, Z2Nat.id in Hx by (unfold sp; lia).
      destruct (WDEF (bv_unsigned x) ltac:(unfold sp in Hx; lia)) as [b Hb]. rewrite w64_of_unsigned in Hb.
      unfold wview. rewrite Hb. discriminate. }
    (* [comment removed for export] *)
    destruct (HCBD fx (ms_regs ms) (ms_mem ms) (ms_rom ms) sp buf len expo e a4 (w64 ra) (getr (ms_regs ms) (Z_to_bv 5 13))
                R1 ltac:(rewrite w64_lit by (unfold LXI.two64 in HRA64; rewrite two64_eq in HRA64; lia); exact HRA4)
                CL2 ltac:(unfold sp; rewrite Z.add_mod, AL1, HK16 by lia; reflexivity) ltac:(unfold sp; lia) ltac:(unfold sp; lia)
                R10 ltac:(unfold sp in Hspbuf; lia) ltac:(lia) R11 R12 eq_refl R14 HA4
                ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(intros i Hi; exact (proj2 (DIG i Hi))) STOK ltac:(left; exact Hspbuf)
                ltac:(unfold CBD_TBL_HI, sp; lia)
                ltac:(intros a0 b Ha0 Hb; apply (proj2 (proj2 (r_abs _ _ _ _ _ _ HR)) a0 b); [|exact Hb];
                      replace a0 with (0x13a88 + (a0 - 0x13a88)) by lia; apply (LXSM2.in_ranges_Z _ 48); [exact HTBL | unfold CBD_TBL_LO, CBD_TBL_HI in Ha0; lia]))
      as (regs' & mem' & MS & KEEP & (r & A0 & Hr) & FRAME & GROW).
    unfold w64 in ETA. rewrite <- ETA in MS.
    (* [comment removed for export] *)
    assert (VS2 : VS rho (set_regs (drop_below S k) (havoc_regs (s_regs (drop_below S k)) 0))) by (split; [exact HC | exact HCB]).
    destruct (fresh_val_sound rho _ (Itv (Some (-1)) (Some 1)) r VS2 ltac:(unfold in_itv; cbn; lia)) as (rho' & VEXT & VS3 & VOK & VB).
    rewrite Hfv in VEXT, VS3, VOK, VB. cbn [fst snd] in VEXT, VS3, VOK, VB.
    destruct VEXT as (AG & NX & Epc & Eregs & Estk & Earrs & Eabs & Eresv & Edepth & Epcache & Epay).
    cbn [s_next s_pc s_regs s_stk s_arrs s_abs s_resv s_depth s_pcache s_pay set_regs drop_below set_arrs set_stk] in AG, NX, Epc, Eregs, Estk, Earrs, Eabs, Eresv, Edepth, Epcache, Epay.
    assert (HG : forall x, (x < NGLOB)%nat -> rho' x = rho x) by (intros x Hx; apply AG; unfold NGLOB in Hx; lia).
    assert (GSP : rho' SYM_SP0 = sp0) by (apply HG; unfold SYM_SP0, NGLOB; lia).
    assert (GDATA : rho' SYM_DATA = rho SYM_DATA) by (apply HG; unfold SYM_DATA, NGLOB; lia).
    assert (GN : rho' SYM_N = rho SYM_N) by (apply HG; unfold SYM_N, NGLOB; lia).
    assert (GRA : rho' SYM_RA = rho SYM_RA) by (apply HG; unfold SYM_RA, NGLOB; lia).
    (* [comment removed for export] *)
    assert (SAME : forall z, 0 <= z < 2 ^ 64 -> (z < sp - fr \/ sp <= z) -> mem' (w64 z) = ms_mem ms (w64 z)).
    { intros z Hz Hout. apply FRAME. rewrite w64_lit by exact Hz. lia. }
    exists (@mkst fx regs' (w64 ra) mem' (ms_rom ms)), rho'.
    split; [exact MS|]. split; [|split; [exact AG | subst S'; cbn [s_next set_pc setreg Nat.eqb set_regs]; lia]].
    subst S'. unfold setreg. cbn [Nat.eqb].
    destruct HR as [Rglob Rpc Rsvc Rregs Rvs Rstk Rarrs Rwin Rpay Rabs Rresv Rfrm Rframe Rsp0 Ralign Rra Rdata].
    fold sp0 in Rstk, Rarrs, Rpay, Rframe.
    constructor; cbn [s_pc s_regs s_ctx s_next s_stk s_arrs s_abs s_pcache s_resv s_pay set_pc set_regs
                      ms_pc_val ms_svc_pending ms_regs ms_mem ms_resv ms_fcsr mkst fp_csr fp_regs];
      rewrite ?Estk, ?Earrs, ?Eabs, ?Eresv, ?Epcache, ?Epay, ?GSP, ?GDATA, ?GN, ?GRA.
    - (* [comment removed for export] *) intros x Hx. rewrite HG by exact Hx. apply Rglob. exact Hx.
    - (* [comment removed for export] *) reflexivity.
    - (* [comment removed for export] *) reflexivity.
    - (* [comment removed for export] *) rewrite Eregs. intros q Hq. rewrite LXSS.list_get_set.
      destruct (Nat.eqb q 10 &&& Nat.ltb 10 (length (havoc_regs (s_regs S) 0)))%bool eqn:Eq.
      + apply andb_prop in Eq as [Eq _]. apply Nat.eqb_eq in Eq. subst q.
        rewrite (LXG.getr_reg_get regs' 10 ltac:(lia)). change (Z.of_nat 10) with 10. rewrite A0. exact VOK.
      + rewrite havoc_regs_get. cbn [Nat.add]. destruct (existsb (Nat.eqb q) keep_regs) eqn:Kq; [|exact I].
        rewrite (LXG.getr_reg_get regs' q Hq), (KEEP (Z.of_nat q) (keep_cs q Kq)), <- (LXG.getr_reg_get (ms_regs ms) q Hq).
        eapply val_ok_agree; [apply list_get_below; exact Wregs | exact AG | exact (Rregs q Hq)].
    - (* [comment removed for export] *) exact VS3.
    - (* [comment removed for export] *)
      apply Forall_forall. intros c Hc. unfold cells_drop_below in Hc. apply LXSM2.In_filterP in Hc as [Hc Hkeep]. cbv beta in Hkeep.
      pose proof (LXSMT.forallb_In _ _ _ _ NOSTRc Hc) as NS. cbv beta in NS.
      assert (Hoff : k <= c_off c).
      { destruct (Z.leb_spec (c_off c + c_w c) k); [exfalso; exact Hkeep|]. cbn in NS. apply Z.leb_le in NS. exact NS. }
      pose proof (proj1 (Forall_forall _ _) Rstk c Hc) as (A1 & A2 & A3 & bs & Hrd & Hvb).
      split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. exists bs. split.
      + rewrite <- Hrd. apply rdn_ext. intros i Hi. apply SAME; [unfold sp in *; lia | right; unfold sp; lia].
      + eapply val_bytes_ok_agree; [exact (LXSMT.forallb_In _ _ _ _ Wstk Hc) | exact AG | exact Hvb].
    - (* [comment removed for export] *)
      apply Forall_forall. intros a' Ha'. apply LXSM2.In_filterP in Ha' as [Ha' Hkeep]. cbv beta in Hkeep.
      pose proof (LXSMT.forallb_In _ _ _ _ NOSTRa Ha') as NS. cbv beta in NS.
      assert (Hlo' : k <= ar_lo a').
      { destruct (Z.leb_spec (ar_hi a') k); [exfalso; exact Hkeep|]. cbn in NS. apply Z.leb_le in NS. exact NS. }
      pose proof (proj1 (Forall_forall _ _) Rarrs a' Ha') as (A1 & A2 & AF).
      split; [exact A1|]. split; [exact A2|]. destruct (ar_fact a') as [f'|] eqn:Ef'; [|exact I].
      destruct AF as (F1 & F2 & AF & AFst). split; [exact F1|]. split; [exact F2|].
      pose proof (LXSMT.forallb_In _ _ _ _ Warrs Ha') as FB. cbv beta in FB. rewrite Ef' in FB. cbn [afact_below] in FB.
      split.
      + intros j Hj.
        rewrite (evl_agree (s_next S) rho rho') in Hj by first [exact FB | exact AG].
        destruct (AF j Hj) as (J1 & b & Hb & Hrange). split; [exact J1|]. exists b. split; [|exact Hrange].
        apply LXSM2.rd1_rdn. apply LXSM2.rd1_rdn in Hb. rewrite <- Hb. apply rdn_ext.
        intros i Hi. apply SAME; [lia | right; unfold sp; lia].
      + intros H1.
        rewrite (evl_agree (s_next S) rho rho') in H1 by first [exact FB | exact AG].
        destruct (AF 0 ltac:(lia)) as (J1 & _). destruct (AFst H1) as (b & Hb & Hrange). exists b. split; [|exact Hrange].
        apply LXSM2.rd1_rdn. apply LXSM2.rd1_rdn in Hb. rewrite <- Hb. apply rdn_ext.
        intros i Hi. apply SAME; [lia | right; unfold sp; lia].
    - (* [comment removed for export] *) split; [|exact WSEG]. intros z Hz. destruct (WDEF z Hz) as [b Hb]. exact (GROW _ _ Hb).
    - (* [comment removed for export] *)
      unfold payload_ok. rewrite ?GSP, ?GDATA, ?GN.
      destruct Rpay as (P1 & P2 & P3 & P4). pose proof Rdata as (D1 & D2 & D3).
      assert (PSAME : forall i, 0 <= i < rho SYM_N -> LXSEM.rd1 U mem' (rho SYM_DATA + i) = LXSEM.rd1 U (ms_mem ms) (rho SYM_DATA + i)).
      { intros i Hi. unfold LXSEM.rd1. rewrite (rdn_ext segs (ms_mem ms) mem' 1); [reflexivity|].
        intros i' Hi'. rewrite Z.add_0_r || replace (rho SYM_DATA + i + i') with (rho SYM_DATA + i) by lia.
        apply SAME; [lia | unfold sp; lia]. }
      split; [|split; [exact P2 | split]].
      + intros i Hi. rewrite PSAME by exact Hi. apply P1. exact Hi.
      + intros off sx x Hin. pose proof (LXSMT.forallb_In _ _ _ _ Wpc Hin) as B. cbv beta in B. apply andb_prop in B as [Bo Bx]. apply Nat.ltb_lt in Bx.
        rewrite (evl_agree (s_next S) rho rho'), (AG x Bx) by first [exact Bo | exact AG].
        destruct (P3 off sx x Hin) as (Q1 & b & Qb & Qx). split; [exact Q1|]. exists b. rewrite PSAME by exact Q1. split; assumption.
      + intros off i Hin. pose proof (LXSMT.forallb_In _ _ _ _ Wpay Hin) as B. cbn [fst] in B.
        rewrite (evl_agree (s_next S) rho rho') by first [exact B | exact AG].
        destruct (P4 off i Hin) as (Q1 & b & Qb & Qi). split; [exact Q1|]. exists b. rewrite PSAME by exact Q1. split; assumption.
    - (* [comment removed for export] *)
      destruct Rabs as (B1 & B2 & B3). split; [|split].
      + intros z b Hg. destruct (B1 z b Hg) as (Z1 & Z2 & Z3). pose proof (uo_small U UOK z (or_introl Z1)).
        split; [exact Z1|]. split; [exact Z2|]. rewrite SAME; [exact Z3 | lia | unfold sp; lia].
      + intros z Hz Hg. pose proof (uo_small U UOK z (or_introl Hz)). rewrite SAME; [exact (B2 z Hz Hg) | lia | unfold sp; lia].
      + intros z b Hz Hb. pose proof (uo_small U UOK z (or_intror Hz)). rewrite SAME in Hb; [exact (B3 z b Hz Hb) | lia | unfold sp; lia].
    - (* [comment removed for export] *) rewrite ERESV. exact I.
    - (* [comment removed for export] *) exact Rfrm.
    - (* [comment removed for export] *) destruct Rframe as [F1 F2]. split.
      + intros z Hw Hrw. rewrite <- (F1 z Hw Hrw). apply FRAME. unfold sp. lia.
      + intros z b Hb. destruct (F2 z b Hb) as [b' Hb']. exact (GROW _ _ Hb').
    - exact Rsp0.
    - exact Ralign.
    - exact Rra.
    - exact Rdata.
  Qed.
End CBD.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem lx_lib_stmt : forall (UP : uenv) (UnA UnB : unitT) (ENTRY NMAX : Z) (HULL : Z * Z) (LIBR SNAP : list (Z * Z)) (CAN : Z),
  LXG.uenv_okb UP = true -> LXG.glue_okb UP HULL LIBR SNAP = true ->
  ue_scells UP = [(CAN, SYM_SC0)] ->                      (* [comment removed for export] *)
  un_env UnA = UP -> un_env UnB = UP ->
  un_snap UnA = SNAP -> un_snap UnB = SNAP ->
  nth_error (un_cuts UnA) 0 = Some (entry_cut ENTRY NMAX []) ->
  nth_error (un_cuts UnB) 0 = Some (entry_cut ENTRY NMAX SNAP) ->
  check_unit UnA = true -> un_total UnA = true ->
  check_unit UnB = true -> un_total UnB = true ->
  cbd_stmt (ue_segs UP) (ue_cbd_pc UP) (ue_cbd_fr UP) ->
  lib_stmt (ue_segs UP) ENTRY (ue_fr UP) NMAX HULL LIBR SNAP (ue_ro UP) CAN.
Proof.
  intros UP UnA UnB ENTRY NMAX HULL LIBR SNAP CAN HUOK HGOK HSC EA EB SA SB CA CB CHKA TOTA CHKB TOTB HCBD.
  pose proof (LXG.uenv_okb_sound UP HUOK) as UOK. pose proof (LXG.glue_okb_sound UP HULL LIBR SNAP HGOK) as GOK.
  unfold lib_stmt.
  intros fx regs mem rom ret sp data n Hx1 Hret4 Hx2 Hx10 Hx11 Hn Hd1 Hd2 Hd3 Hs1 Hs2 Hs3 Hdisj Himg Hnoseg Hpay Hst Hro Hcan [Hstat Hhull] Hfrm.
  (* [comment removed for export] *)
  assert (G2 : LXG.greg regs 2 = bv_unsigned sp) by (unfold LXG.greg; rewrite Hx2; reflexivity).
  assert (G10 : LXG.greg regs 10 = bv_unsigned data) by (unfold LXG.greg; rewrite Hx10; reflexivity).
  assert (G1 : LXG.greg regs 1 = bv_unsigned ret) by (unfold LXG.greg; rewrite Hx1; reflexivity).
  assert (RO' : ro_ok (ue_segs UP) (ue_ro UP) mem) by exact Hro.
  (* [comment removed for export] *)
  assert (UNIT : exists Un abs0, un_env Un = UP /\ un_snap Un = SNAP /\ check_unit Un = true /\ un_total Un = true /\
                 In (entry_cut ENTRY NMAX abs0) (un_cuts Un) /\
                 ((abs0 = [] /\ statics_pristine LIBR mem) \/ (abs0 = SNAP /\ statics_snap SNAP mem))).
  { destruct Hstat as [HP | HS].
    - exists UnA, []. repeat split; try assumption. + eapply nth_error_In; exact CA. + left; split; [reflexivity | exact HP].
    - exists UnB, SNAP. repeat split; try assumption. + eapply nth_error_In; exact CB. + right; split; [reflexivity | exact HS]. }
  clear CA CB CHKA CHKB TOTA TOTB SA SB EA EB Hstat UnA UnB.
  destruct UNIT as (Un & abs0 & EU & SU & CHK & TOT & HIN & HABS). subst UP.
  (* [comment removed for export] *)
  destruct Hcan as [c Hc].
  pose proof (LXG.entry_scells (un_env Un) UOK regs n c mem
                ltac:(intros a x Hin; rewrite HSC in Hin; destruct Hin as [Hin|[]]; injection Hin; intros _ <-; exact Hc)) as SCOK.
  (* [comment removed for export] *)
  pose proof (LXG.entry_R (un_env Un) HULL LIBR SNAP UOK GOK fx regs mem rom n (bv_unsigned c) ENTRY NMAX abs0) as ER.
  cbv zeta in ER. rewrite G2, G10, G1 in ER.
  specialize (ER Hx11 Hn Hret4 Hd1 Hd2 Hd3 Hs1 Hs2 Hs3 Hdisj Hnoseg Hpay Hst RO' HABS Hhull Hfrm).
  (* [comment removed for export] *)
  destruct (LXSE.unit_sound Un (LXG.rho_entry regs n (bv_unsigned c)) mem UOK SCOK
              (apply_cbd_sound (un_env Un) (LXG.rho_entry regs n (bv_unsigned c)) mem UOK HCBD)
              CHK TOT (LXG.rho_entry regs n (bv_unsigned c)) (@mkst fx regs (Z_to_bv 64 ENTRY) mem rom))
    as (ms' & S & rho' & MS & EXIT & HR').
  { exists (entry_cut ENTRY NMAX abs0). split; [exact HIN | exact ER]. }
  (* [comment removed for export] *)
  destruct (LXG.exit_post (un_env Un) HULL LIBR SNAP UOK GOK (LXG.rho_entry regs n (bv_unsigned c)) mem fx regs mem n (bv_unsigned c) Un S rho' ms'
              eq_refl eq_refl eq_refl SU Hhull EXIT HR') as (fx' & regs' & mem' & Ems' & KEEP & A0 & FRAME & STAT & FRM').
  exists fx', regs', mem'.
  rewrite Ems' in MS. pose proof (msteps_rom _ _ _ MS) as ROM. cbn [ms_rom mkst] in ROM. rewrite ROM in MS.
  rewrite Hx1 in MS. rewrite G2 in FRAME.
  split; [exact MS|]. split; [exact KEEP|]. split; [exact A0|]. split; [exact FRAME|]. split; [exact STAT | exact FRM'].
Qed.

End LXF.
