(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmCurSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_strinit2_zero_csrc_u Cut_strinit2_sso_csrc_u Cut_strinit2_n23_csrc_u Cut_strinit2_long_csrc_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutDemo Require Pm10Memmove_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmGrow Require Import GrowKit_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module SI2.
Module Z0 := Cut_strinit2_zero_csrc_u.  Module S0 := Cut_strinit2_sso_csrc_u.  Module N23 := Cut_strinit2_n23_csrc_u.  Module LG := Cut_strinit2_long_csrc_u.
Definition MALLOC : Z := PML.PC_MALLOC.  Definition FREE : Z := PML.PC_FREE.  Definition MEMMOVE : Z := 0xb7c98.
Definition RET : Z := Eval vm_compute in hd 0 Cut_strinit2_sso_csrc_T_u.ENDS.
Definition SCRT : Z := Eval vm_compute in CH.hd_scr S0.HDECL.
Definition CSAVED := CL5.CSAVED.
Definition has := GK.has.
Definition NFV : nat := 32.
Notation NOGOTO := (fun _ _ _ _ t => match t with CC.TGoto _ _ => false | CC.TOther _ => true end).

Definition e_o := EVar 10.  Definition e_src := EVar 11.  Definition SP := EVar 2.
Definition round8 (x : expr) (c : Z) : expr := EAlu ALU_ADD (EMd M_MUL (ELit 8) (EAlu ALU_SRL x (ELit 3))) (ELit c).

Lemma ret_at : CL.is_ret_at GK.RSEGS RET.
Proof. CL.solve_is_ret. Qed.
Lemma csaved_lt : forall y : reg, In (ridx y) CSAVED -> (ridx y < NFV)%nat.
Proof. intros y Hy. unfold CSAVED, CL5.CSAVED in Hy. cbn [In] in Hy. unfold NFV. intuition lia. Qed.
Lemma round8_val : forall E x v, bv_unsigned (edenot E x) = v -> 0 <= v < 2 ^ 60 -> bv_unsigned (edenot E (round8 x 8)) = 8 * (v / 8) + 8.
Proof.
  intros E x v Hx Hv. unfold round8.
  change (edenot E (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EAlu ALU_SRL x (ELit 3))) (ELit 8)))
    with (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 8) (edenot E (EAlu ALU_SRL x (ELit 3)))) (Z_to_bv 64 8)).
  rewrite u_add64, u_mul64, u_srl_lit, Hx. rewrite !u64_of_Z by lia. change (2 ^ ((3 mod two64) mod 64)) with 8.
  pose proof (Z.div_le_upper_bound v 8 (2 ^ 57) ltac:(lia) ltac:(lia)). pose proof (Z.div_pos v 8 ltac:(lia) ltac:(lia)).
  rewrite (Z.mod_small (8 * (v / 8))) by lia. apply Z.mod_small. lia.
Qed.
Lemma u_eadd : forall E e1 e2, bv_unsigned (edenot E (APC.eadd e1 e2)) = (bv_unsigned (edenot E e1) + bv_unsigned (edenot E e2)) mod 2 ^ 64.
Proof. intros E e1 e2. unfold APC.eadd. rewrite mkAlu_denot, u_add64. reflexivity. Qed.
Fixpoint exprs_eqb (a b : list expr) : bool := match a, b with [], [] => true | x :: a', y :: b' => (expr_eqb x y && exprs_eqb a' b')%bool | _, _ => false end.
Lemma exprs_eqb_eq : forall a b, exprs_eqb a b = true -> a = b.
Proof. induction a as [|x a IH]; intros [|y b] H; try discriminate H; [reflexivity|]. cbn in H. apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1. rewrite H1, (IH b H2). reflexivity. Qed.

Definition E0_of (R : bvmap 5 word) (txt : list Z) : env := Env (reg_ev R (fun _ => Z_to_bv 64 0)) (fun id => nth id [[]; map (Z_to_bv 8) txt] []).

Section ChkLong.
Variable lit23 : bool.
Variables (BLS : list CA.blocks) (CPS : list CC.cutpoint) (RETS : list (nat * nat * nat * Z)).
Definition e_n : expr := if lit23 then ELit 23 else EVar 12.
Definition CAPX : expr := if lit23 then ELit 26 else round8 (EVar 12) 8.
Definition pre (i : nat) : bool := Nat.eqb i 0.
Definition hd_base (i : nat) : expr := fst (hd (ELit 0, ELit 0) (nth i BLS [])).
Definition hd_size (i : nat) : expr := snd (hd (ELit 0, ELit 0) (nth i BLS [])).
Definition exit_chk (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in let pe := hd_base i in let ce := hd_size i in
  (CL.ps_at ps [RET] && CL.ps_keeps ps CSAVED && CH2.blocks_vars_lt (CC.cp_nx c) (nth i BLS []) && Nat.leb NFV (CC.cp_nx c)
   && negb (pre i) && match nth i BLS [] with [_] => true | _ => false end && expr_eqb ce CAPX
   && has cells (KWord (SA e_o 0) 8 (APC.eaddz ce 1)) && has cells (KWord (SA e_o 8) 8 e_n) && has cells (KWord (SA e_o 16) 8 pe)
   && has cells (KBlob (SA pe 0) e_n 1) && has cells (KWord (if lit23 then SA pe 23 else SA (APC.eadd e_n pe) 0) 1 (ELit 0)))%bool.
Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      if CH2.is_call MALLOC FREE [MEMMOVE] pc then
        match CH2.ret_of RETS i k with
        | Some j => (Nat.leb NFV (CC.cp_nx c)
                     && if Z.eqb pc MALLOC then (pre i && negb (pre j) && expr_eqb (CA.ps_reg ps 10) CAPX)
                        else (negb (pre i) && negb (pre j)))%bool
        | None => false
        end
      else exit_chk i c ps
  end.
Definition COMMON : list kentry :=
  [KUnk (SA e_o 0) (ELit 24); KWr (SA e_o 0) (ELit 24); KRange e_o (2 ^ 40) (2 ^ 47); KAlign e_o 8;
   KUnk (SA SP (- SCRT)) (ELit SCRT); KWr (SA SP (- SCRT)) (ELit SCRT); KRange SP (2 ^ 40) (2 ^ 47); KAlign SP 16; KDisj (SA SP (- SCRT)) (ELit SCRT) (SA e_o 0) (ELit 24);
   KBlob (SA e_src 0) e_n 1; KUnk (SA e_src 0) e_n; KRange e_src 4096 (2 ^ 47); KDisj (SA SP (- SCRT)) (ELit SCRT) (SA e_src 0) e_n; KDisj (SA e_o 0) (ELit 24) (SA e_src 0) e_n] ++
  (if lit23 then [] else [KRange e_n 24 (2 ^ 26)]).
Definition kn_chk (cp0 : CC.cutpoint) : bool :=
  (forallb (fun K => has COMMON K) (CC.cp_know cp0) && exprs_eqb (CC.cp_regs cp0) (if lit23 then sr_upd sr_id 12 (ELit 23) else sr_id))%bool.
End ChkLong.

Lemma leaf_n23 : CH2.leaves_all N23.CPS N23.TAGS (leaf_chk true N23.BLS N23.RETS) = true.  Proof. vmc_refl. Qed.
Lemma leaf_lg : CH2.leaves_all LG.CPS LG.TAGS (leaf_chk false LG.BLS LG.RETS) = true.  Proof. vmc_refl. Qed.
Lemma kn_n23 : kn_chk true N23.cp0 = true.  Proof. vmc_refl. Qed.
Lemma kn_lg : kn_chk false LG.cp0 = true.  Proof. vmc_refl. Qed.
Lemma heap_n23 : CH2.heap_chk NFV N23.HDECL N23.BLS N23.CPS GK.HULL_LO GK.HULL_HI N23.TAGS N23.RETS MALLOC FREE [MEMMOVE] = true.  Proof. vmc_refl. Qed.
Lemma heap_lg : CH2.heap_chk NFV LG.HDECL LG.BLS LG.CPS GK.HULL_LO GK.HULL_HI LG.TAGS LG.RETS MALLOC FREE [MEMMOVE] = true.  Proof. vmc_refl. Qed.
Lemma ng_n23 : CH2.leaves_all N23.CPS N23.TAGS NOGOTO = true.  Proof. vmc_refl. Qed.
Lemma ng_lg : CH2.leaves_all LG.CPS LG.TAGS NOGOTO = true.  Proof. vmc_refl. Qed.

Section Long.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps GK.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom GK.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom GK.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Variable lit23 : bool.
Variables (HDECL : CH.hdecl) (BLS : list CA.blocks) (CPS : list CC.cutpoint) (TAGS : list (list CC.tag)) (RETS : list (nat * nat * nat * Z)) (cp0 : CC.cutpoint).
Hypothesis H_hd : HDECL = CH.HD SCRT 8224 [(e_src, 0, e_n lit23)] [(e_o, 0, ELit 24)] [].
Hypothesis H_cp0 : nth_error CPS 0 = Some cp0.
Hypothesis H_pc : CC.cp_pc cp0 = PMCS.PC_STRINIT2.
Hypothesis H_BL0 : nth 0 BLS [] = [].
Hypothesis H_kn : kn_chk lit23 cp0 = true.
Hypothesis plans : forall i c, nth_error CPS i = Some c -> CC.plan_sound GK.RSEGS c.
Hypothesis tags_ok : CC.tags_chk CPS TAGS NFV = true.
Hypothesis heap_ok : CH2.heap_chk NFV HDECL BLS CPS GK.HULL_LO GK.HULL_HI TAGS RETS MALLOC FREE [MEMMOVE] = true.
Hypothesis no_goto : CH2.leaves_all CPS TAGS NOGOTO = true.
Hypothesis leaf_ok : CH2.leaves_all CPS TAGS (leaf_chk lit23 BLS RETS) = true.

Definition Cred (cr0 : credit) (cap : Z) (i : nat) (E : env) (cr : credit) : Prop := cr = if pre i then cr0 else debit L cr0 cap.

Lemma long_ok : forall (LB : list (Z * Z)) (cr : credit) (o src sp r : Z) (txt : list Z),
  PML.cps_heap L HI PMCS.PC_STRINIT2 r sp (48 + PMS.OPNEW_SCR) LB cr
      (fun R M => (if lit23 then Z.of_nat (length txt) = 23 else 24 <= Z.of_nat (length txt)) /\
                  PML.entry L R M sp r (48 + PMS.OPNEW_SCR) /\ PML.a0 R o /\ PML.a1 R src /\ PML.a2 R (Z.of_nat (length txt)) /\ Z.of_nat (length txt) < 2 ^ 26 /\
                  L5.bytes_at GK.RSEGS M src txt /\ L5.defined M src (Z.of_nat (length txt)) /\ PML.obj_on_stack L sp o 24 /\ L5.defined M o 24 /\
                  (exists b, In b LB /\ fst b <= src /\ src + Z.of_nat (length txt) <= fst b + snd b) /\
                  credit_ok L cr (PML.str_cap (Z.of_nat (length txt))))
      (fun R M R' M' LB' cr' LBk W => W = [(o, 24)] /\ LBk = LB /\
          exists p, let cap := PML.str_cap (Z.of_nat (length txt)) in
             PML.str_at_w M' o (PML.SLong cap p txt) /\ L5C.fresh_block L LB M' p cap /\ LB' = (p, cap) :: LB /\ cr' = debit L cr cap).
Proof.
  intros LB cr o src sp r txt. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hvar & Hentry & Ha0 & Ha1 & Ha2 & Hlen & Hbytes & Hdef & Hobj & Hdo & Hsrc & Hcredit) Hcont.
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (S1 & S2 & S3 & S4 & S5).
  unfold PMS.OPNEW_SCR, PML.HEAP_STACK in *.
  destruct Hobj as (O1 & O2 & O3).
  set (n := Z.of_nat (length txt)) in *.
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_stack L LAY) as LSTK. unfold PML.HEAP_STACK in LSTK.
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & _).
  set (E0 := E0_of R txt).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 src) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V12 : ev E0 12 = Z_to_bv 64 n) by (rewrite <- Ha2; exact (EV 12%bv)).
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by lia.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; lia).
  assert (U12 : bv_unsigned (ev E0 12) = n) by (rewrite V12; apply u64_of_Z; lia).
  destruct Hsrc as (b & Hb & Hbq1 & Hbq2).
  destruct (Hwf _ Hb) as ((B0' & B1' & B2' & B3' & B4') & Bdef & Bap).
  assert (U11 : bv_unsigned (ev E0 11) = src) by (rewrite V11; apply u64_of_Z; lia).
  assert (Hn24 : 23 <= n) by (destruct lit23; lia).
  set (cap := PML.str_cap n) in *.
  assert (Hcap : cap = if lit23 then 26 else 8 * (n / 8) + 8).
  { unfold cap, PML.str_cap. destruct lit23; [rewrite Hvar; reflexivity|]. rewrite CL5.lor7 by lia.
    pose proof (Z.div_le_lower_bound n 8 3 ltac:(lia) ltac:(lia)). destruct (Z.eqb_spec (8 * (n / 8) + 7) 23); lia. }
  assert (FR : forall E1, env_agree NFV E0 E1 ->
            bv_unsigned (ev E1 2) = sp /\ bv_unsigned (ev E1 10) = o /\ bv_unsigned (ev E1 11) = src /\ bv_unsigned (ev E1 12) = n /\ eb E1 = eb E0).
  { intros E1 [A B]. rewrite <- !A by (unfold NFV; lia). repeat split; try assumption. symmetry. exact B. }
  assert (VX : forall E1, env_agree NFV E0 E1 -> bv_unsigned (edenot E1 (e_n lit23)) = n /\ bv_unsigned (edenot E1 (CAPX lit23)) = cap).
  { intros E1 Hag1. destruct (FR E1 Hag1) as (F2 & F10 & F11 & F12 & _). unfold e_n, CAPX. rewrite Hcap. destruct lit23.
    - cbn [edenot]. rewrite !u64_of_Z by lia. lia.
    - split; [exact F12|]. apply round8_val; [exact F12 | lia]. }
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= 0x7fff7f800000) by (rewrite ILO, IHI; lia).
  assert (LYE : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L) by (rewrite ILO, IHI, (PmLayout.ly_errno L LAY); lia).
  assert (STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
    by (rewrite H_hd; change (CH.hd_scr (CH.HD SCRT 8224 [(e_src, 0, e_n lit23)] [(e_o, 0, ELit 24)] [])) with SCRT; unfold SCRT; repeat split; lia).
  assert (SCRP : 0 <= CH.hd_scr HDECL) by (rewrite H_hd; change (CH.hd_scr (CH.HD SCRT 8224 [(e_src, 0, e_n lit23)] [(e_o, 0, ELit 24)] [])) with SCRT; unfold SCRT; lia).
  assert (NF32 : (32 <= NFV)%nat) by (unfold NFV; lia).
  assert (W_OK : forall (w : L5.range) (a : Z), In w [(o, 24)] -> L5.in_rng w a -> CH2.wclient L sp a).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. split; [lia | left; lia]. }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs HDECL) -> SGP.region_vars_lt NFV rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w [(o, 24)] /\ L5.in_rng w a)).
  { rewrite H_hd. intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CH2.in_reg, estart, elenZ, e_o in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by lia. exists (o, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  unfold PML.cfg. rewrite <- H_pc. rewrite <- LS.
  eapply CH2.heap_cert_sound with (NF := NFV) (E0 := E0) (M0 := M) (model0 := model) (LBrest := LB) (sp0 := sp) (d := HDECL)
    (W := [(o, 24)]) (BLS := BLS) (Cred := Cred cr cap) (CPS := CPS) (TAGS := TAGS) (RETS := RETS) (MALLOC := MALLOC) (FREE := FREE)
    (COPIES := [MEMMOVE]) (IMG_LO := GK.HULL_LO) (IMG_HI := GK.HULL_HI) (FPI := PML.fp_ok) (i := 0%nat) (E := E0) (HI := HI).
  - exact HIok.
  - exact LYI.
  - exact LYE.
  - exact (PmLayout.ly_ro L LAY).
  - rewrite LSTK. lia.
  - exact STKF.
  - exact SCRP.
  - rewrite LSTK, H_hd. reflexivity.
  - exact NF32.
  - exact U2.
  - rewrite V4, (PmLayout.ly_tp L LAY). reflexivity.
  - exact W_OK.
  -   rewrite H_hd. intros rg [<-|[]]. split; [destruct lit23; vm_compute; reflexivity|]. intros a Ha. unfold CH2.in_reg, estart in Ha. cbn [a_base a_off] in Ha.
    unfold elenZ in Ha. rewrite (proj1 (VX E0 (CC.env_agree_refl _ _))) in Ha. unfold e_src in Ha. cbn [edenot] in Ha. rewrite U11 in Ha.
    split; [lia|]. right; right. exists b. split; [exact Hb | lia].
  - exact WRS_OK.
  - rewrite H_hd. intros rg a [].
  - exact HKnil.
  - exact ILO.
  - exact IHI.
  - rewrite LS. exact FPM.
  - rewrite LS. exact plans.
  - exact tags_ok.
  - exact heap_ok.
  - exact (PmLayout.ly_malloc L LAY).
  - exact (PmLayout.ly_free L LAY).
  - intros pc [<-|[]]. exact (Pm10Memmove_u.memmove_copy1 L LS).
  - intros i c kk ps j sg IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ no_goto _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X.
  -
    intros i c kk ps j cj IL Hret Hcj E E' R' M1 M1' cr' HagE Hag HLF HC.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X.
    change (CH2.is_call MALLOC FREE [MEMMOVE] MALLOC) with true in X. cbv beta iota in X. rewrite Hret in X. change (Z.eqb MALLOC MALLOC) with true in X. cbv beta iota in X.
    apply andb_prop in X as [XA X]. apply Nat.leb_le in XA. repeat (apply andb_prop in X as [X ?Y]). apply expr_eqb_eq in Y. apply negb_true_iff in Y0.
    assert (HagE' : env_agree NFV E0 E') by (eapply CC.env_agree_trans; [exact HagE | eapply CC.env_agree_le; [exact Hag | exact XA]]).
    rewrite Y, (proj2 (VX E' HagE')). unfold Cred in HC. rewrite X in HC. subst cr'. split; [exact Hcredit|].
    intros E2 Hag2. unfold Cred. rewrite Y0. reflexivity.
  -
    intros i c kk ps pc j cj IL Hcall Hnm Hret Hcj E E' R' M1 M1' cr' HagE Hag HLF HC E2 Hag2.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. rewrite Hcall, Hret in X.
    destruct (Z.eqb_spec pc MALLOC) as [->|_]; [contradiction|].
    apply andb_prop in X as [XA X]. apply andb_prop in X as [X1 X2]. apply negb_true_iff in X1, X2. unfold Cred in *. rewrite X2. rewrite X1 in HC. exact HC.
  -
    intros i c kk ps pc IL Hnc fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF _.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_ok _ _ _ _ _ IL) as X. unfold leaf_chk in X. rewrite Hnc in X. unfold exit_chk in X.
    pose proof (CH2.exit_amb L HI HIok LYI LYE (PmLayout.ly_ro L LAY) NFV E0 M model LB sp HDECL [(o, 24)] BLS (Cred cr cap) STKF SCRP NF32 U2 W_OK WRS_OK
                  CPS GK.HULL_LO GK.HULL_HI TAGS RETS MALLOC FREE [MEMMOVE] heap_ok i c kk ps pc IL Hnc E E' R1 R' M1 M' m1 HAt HAmb Hag HLF) as HA'.
    repeat (apply andb_prop in X as [X ?Y]).

    apply Z.eqb_eq in X. apply Nat.leb_le in Y7. apply negb_true_iff in Y6. apply expr_eqb_eq in Y4.
    pose proof HA' as HA2. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr1 & Hdf1).
    assert (HagE' : env_agree NFV E0 E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | exact Y7]]).
    destruct (FR E' HagE') as (F2 & F10 & F11 & F12 & FB). destruct (VX E' HagE') as (UN & UCAP).
    rewrite LS in HLF.
    assert (CELL : forall X0, has (SR.ps_cells ps) X0 = true -> kentry_ok GK.RSEGS E' M' X0).
    { intros X0 HX. apply (CC.lf_cells _ _ _ _ _ _ _ HLF). exact (GK.has_In _ _ HX). }
    unfold hd_base, hd_size in *. destruct (nth i BLS []) as [|[pe ce] [|]] eqn:HBL; try discriminate Y5. cbn [hd fst snd] in *. subst ce.
    set (pX := bv_unsigned (edenot E' pe)) in *.
    assert (HH2 : hi_heap HI ((pX, cap) :: LB) cr1 M' (m_vmmaps m1)).
    { unfold CH2.cur in HH1. rewrite HBL in HH1. rewrite <- (CH2.den_agree _ E E' _ Hag Y8) in HH1. unfold CH2.den in HH1. cbn [map fst snd] in HH1. fold pX in HH1.
      rewrite UCAP in HH1. exact HH1. }
    destruct (hio_wf L SCFG HI HIok _ _ _ _ HH2) as (Hwf2 & Hnd2 & _).
    destruct (Hwf2 (pX, cap) (or_introl eq_refl)) as ((Q0 & Q1 & Q2 & Q3 & Q4) & Qdef & Qap). cbn [fst snd lb_remove] in Q0, Q1, Q2, Q3, Q4, Qdef, Qap. rewrite Z.eqb_refl in Qap.
    assert (Hbig : n < cap) by (rewrite Hcap; destruct lit23; [lia|]; pose proof (Z.mod_pos_bound n 8 ltac:(lia)); pose proof (Z.div_mod n 8 ltac:(lia)); lia).
    assert (UW0 : bv_unsigned (edenot E' (APC.eaddz (CAPX lit23) 1)) = cap + 1).
    { unfold APC.eaddz. rewrite mkAlu_denot, u_add64. rewrite UCAP. cbn [edenot]. rewrite (u64_of_Z 1) by lia. apply Z.mod_small. lia. }
    assert (W0 : L5.u64_at GK.RSEGS M' o (cap + 1)).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ o _ (CELL _ Y3)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | exact UW0]. }
    assert (W8 : L5.u64_at GK.RSEGS M' (o + 8) n).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ (o + 8) _ (CELL _ Y2)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | exact UN]. }
    assert (W16 : L5.u64_at GK.RSEGS M' (o + 16) pX).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ (o + 16) _ (CELL _ Y1)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | reflexivity]. }
    assert (BS : L5.bytes_at GK.RSEGS M' pX txt).
    { apply (CL5.kblob_elim GK.RSEGS E' M' _ _ 1%nat pX txt (CELL _ Y0)); [unfold estart; cbn [a_base a_off]; fold pX; lia | rewrite FB; reflexivity]. }
    assert (NUL : L5.u8_at GK.RSEGS M' (pX + n) 0).
    { apply (CL5.kword8_zero_elim GK.RSEGS E' M' _ _ (CELL _ Y)). unfold estart. destruct lit23; cbn [a_base a_off]; [fold pX; lia|].
      rewrite u_eadd, UN. fold pX. rewrite Z.mod_small by lia. lia. }
    assert (KEEP : forall y : reg, In (ridx y) CSAVED -> getr R' y = getr R y).
    { intros y Hy. rewrite (CL.ps_keeps_sound GK.RSEGS c ps E0 E' R' M1 M' CSAVED NFV y HLF Y9 HagE' Hy (csaved_lt y Hy)). exact (EV y). }
    assert (HRP : regs_preserved R R') by (intros y Hy; apply KEEP; exact (CL5.csaved_in y Hy)).
    assert (Hra' : getr R' 1%bv = Z_to_bv 64 r) by (rewrite (KEEP 1%bv ltac:(left; reflexivity)); exact Hra).
    assert (Hds : L5.defined M (sp - CH.hd_scr HDECL) (CH.hd_scr HDECL)) by (rewrite H_hd; change (CH.hd_scr (CH.HD SCRT 8224 [(e_src, 0, e_n lit23)] [(e_o, 0, ELit 24)] [])) with SCRT; unfold SCRT; exact S5).
    pose proof (CH2.amb_hpres L HI LYI LYE NFV E0 M model LB sp HDECL [(o, 24)] BLS (Cred cr cap) STKF NF32 i E M' m1 HA2 Hds) as HP.
    rewrite H_hd in HP; change (CH.hd_scr (CH.HD SCRT 8224 [(e_src, 0, e_n lit23)] [(e_o, 0, ELit 24)] [])) with SCRT in HP; unfold SCRT in HP.
    rewrite X, LS. eapply CL.ret_cps; [exact ret_at | exact (proj1 Hmo1) | exact (proj1 (proj2 Hmo1)) | |].
    { rewrite Hra'. apply Hoare.ret_ok_even. destruct Hraok as [R1' R2']. rewrite u64_of_Z by lia. exact R2'. }
    rewrite Hra'.
    unfold Cred in HC1. rewrite Y6 in HC1. subst cr1.
    apply (Hcont fx' R' M' m1 ((pX, cap) :: LB) (debit L cr cap) LB [(o, 24)] HFP); [| exact HRP | exact HP | exact Hbv1 | exact HH2].
    split; [reflexivity|]. split; [reflexivity|]. exists pX. cbv zeta. fold n cap.
    split; [|split; [|auto]].
    + split; [|exact Hbig]. unfold L5.lstr_long. fold n.
      split; [rewrite Z.bit0_odd, Z.odd_add, <- Z.negb_even, Hcap; destruct lit23; [reflexivity | rewrite Z.even_add, Z.even_mul; reflexivity]|].
      split; [exact W0|]. split; [exact W8|]. split; [exact W16|]. split; [exact BS | exact NUL].
    + split; [repeat split; assumption|]. split; [exact Qap | exact Qdef].
  - exact H_cp0.
  -
    rewrite LS.
    assert (Hds : L5.defined M (sp - 8288) 8288) by exact S5.
    unfold kn_chk in H_kn. apply andb_prop in H_kn as [HKN HRG]. apply exprs_eqb_eq in HRG.
    split.
    { rewrite HRG. destruct lit23; [|exact (regs_ok_id R _ _)]. apply (regs_ok_pin E0 sr_id R 12%bv); [exact (regs_ok_id R _ _)|]. rewrite Ha2. cbn [edenot]. fold n. rewrite Hvar. reflexivity. }
    assert (COM : Forall (kentry_ok GK.RSEGS E0 M) (COMMON lit23)).
    { assert (EN : elenZ E0 (e_n lit23) = n) by (unfold elenZ; exact (proj1 (VX E0 (CC.env_agree_refl _ _)))).
      assert (ENl : lit23 = true -> n = 23) by (intros ->; exact Hvar).
      unfold COMMON, SP, SCRT, e_o, e_src. rewrite Forall_app. split; [|unfold e_n; destruct lit23; [apply Forall_nil | apply Forall_cons; [e_range | apply Forall_nil]]].
      repeat (apply Forall_cons); [.. | apply Forall_nil].
      + e_unk. + e_wr. + e_range. + e_align O3.
      + e_unk. + e_wr. + e_range. + e_align S1. + e_disj.
      + eapply CL5.kblob_intro with (bs := txt) (A := src); [ev_start | exact EN | lia | fold n; lia | lia | reflexivity | exact Hbytes | fold n; ev_def].
      + eapply CL5.kunk_intro with (A := src) (N := n); [ev_start | exact EN | lia | lia | lia | exact Hdef].
      + e_range.
      + eapply CL5.kdisj_intro with (A1 := sp - 8288) (N1 := 8288) (A2 := src) (N2 := n); [ev_start | ev_len | ev_start | exact EN | lia].
      + eapply CL5.kdisj_intro with (A1 := o) (N1 := 24) (A2 := src) (N2 := n); [ev_start | ev_len | ev_start | exact EN | lia].
      }
    unfold know_ok. apply Forall_forall. intros K0 HK0. rewrite forallb_forall in HKN. exact (proj1 (Forall_forall _ _) COM K0 (GK.has_In _ _ (HKN K0 HK0))).
  -
    split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr. split; [|reflexivity]. unfold CH2.cur. rewrite H_BL0. exact HH.
  - exact Hfp.
Qed.
End Long.

Lemma heap_s : CH2.heap_chk NFV S0.HDECL S0.BLS S0.CPS GK.HULL_LO GK.HULL_HI S0.TAGS S0.RETS MALLOC FREE [MEMMOVE] = true.  Proof. vmc_refl. Qed.
Lemma heap_z : CH2.heap_chk NFV Z0.HDECL Z0.BLS Z0.CPS GK.HULL_LO GK.HULL_HI Z0.TAGS Z0.RETS MALLOC FREE [] = true.  Proof. vmc_refl. Qed.
Lemma ng_s : CH2.leaves_all S0.CPS S0.TAGS NOGOTO = true.  Proof. vmc_refl. Qed.
Definition leaf_s (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      if CH2.is_call MALLOC FREE [MEMMOVE] pc then negb (Z.eqb pc MALLOC)
      else (CL.ps_at ps [RET] && CL.ps_keeps ps CSAVED && Nat.leb NFV (CC.cp_nx c)
            && has (SR.ps_cells ps) (KWord (SA e_o 0) 1 (EMd M_MUL (ELit 2) (EVar 12))) && has (SR.ps_cells ps) (KBlob (SA e_o 1) (EVar 12) 1)
            && has (SR.ps_cells ps) (KWord (SA (APC.eadd e_o (EVar 12)) 1) 1 (ELit 0)))%bool
  end.
Lemma leaf_s_ok : CH2.leaves_all S0.CPS S0.TAGS leaf_s = true.  Proof. vmc_refl. Qed.
Definition leaf_z (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc => (negb (CH2.is_call MALLOC FREE [] pc) && CL.ps_at ps [RET] && CL.ps_keeps ps CSAVED && Nat.leb NFV (CC.cp_nx c)
                     && has (SR.ps_cells ps) (KWord (SA e_o 0) 1 (ELit 0)) && has (SR.ps_cells ps) (KWord (SA e_o 1) 1 (ELit 0)))%bool
  end.
Lemma leaf_z_ok : CH2.leaves_all Z0.CPS Z0.TAGS leaf_z = true.  Proof. vmc_refl. Qed.

Section Final.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps GK.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom GK.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom GK.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Definition ok_n23 := long_ok L HI HIok LAY FPM true N23.HDECL N23.BLS N23.CPS N23.TAGS N23.RETS N23.cp0 eq_refl eq_refl eq_refl eq_refl kn_n23 N23.plans N23.tags_ok heap_n23 ng_n23 leaf_n23.
Definition ok_lg := long_ok L HI HIok LAY FPM false LG.HDECL LG.BLS LG.CPS LG.TAGS LG.RETS LG.cp0 eq_refl eq_refl eq_refl eq_refl kn_lg LG.plans LG.tags_ok heap_lg ng_lg leaf_lg.

Lemma sso_ok : forall (LB : list (Z * Z)) (cr : credit) (o src sp r : Z) (txt : list Z),
  PML.cps_heap L HI PMCS.PC_STRINIT2 r sp (48 + PMS.OPNEW_SCR) LB cr
      (fun R M => 1 <= Z.of_nat (length txt) <= 22 /\
                  PML.entry L R M sp r (48 + PMS.OPNEW_SCR) /\ PML.a0 R o /\ PML.a1 R src /\ PML.a2 R (Z.of_nat (length txt)) /\
                  L5.bytes_at GK.RSEGS M src txt /\ L5.defined M src (Z.of_nat (length txt)) /\ PML.obj_on_stack L sp o 24 /\ L5.defined M o 24 /\
                  (exists b, In b LB /\ fst b <= src /\ src + Z.of_nat (length txt) <= fst b + snd b))
      (fun R M R' M' LB' cr' LBk W => W = [(o, 24)] /\ LBk = LB /\ PML.str_at_w M' o (PML.SShort txt) /\ LB' = LB /\ cr' = cr).
Proof.
  intros LB cr o src sp r txt. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hvar & Hentry & Ha0 & Ha1 & Ha2 & Hbytes & Hdef & Hobj & Hdo & Hsrc) Hcont.
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (S1 & S2 & S3 & S4 & S5).
  unfold PMS.OPNEW_SCR, PML.HEAP_STACK in *.
  destruct Hobj as (O1 & O2 & O3).
  set (n := Z.of_nat (length txt)) in *.
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_stack L LAY) as LSTK. unfold PML.HEAP_STACK in LSTK.
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & _).
  set (E0 := E0_of R txt).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 src) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V12 : ev E0 12 = Z_to_bv 64 n) by (rewrite <- Ha2; exact (EV 12%bv)).
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by lia.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; lia).
  assert (U12 : bv_unsigned (ev E0 12) = n) by (rewrite V12; apply u64_of_Z; lia).
  destruct Hsrc as (b & Hb & Hbq1 & Hbq2).
  destruct (Hwf _ Hb) as ((B0' & B1' & B2' & B3' & B4') & Bdef & Bap).
  assert (U11 : bv_unsigned (ev E0 11) = src) by (rewrite V11; apply u64_of_Z; lia).
  assert (FR : forall E1, env_agree NFV E0 E1 ->
            bv_unsigned (ev E1 2) = sp /\ bv_unsigned (ev E1 10) = o /\ bv_unsigned (ev E1 11) = src /\ bv_unsigned (ev E1 12) = n /\ eb E1 = eb E0).
  { intros E1 [A B]. rewrite <- !A by (unfold NFV; lia). repeat split; try assumption. symmetry. exact B. }
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= 0x7fff7f800000) by (rewrite ILO, IHI; lia).
  assert (LYE : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L) by (rewrite ILO, IHI, (PmLayout.ly_errno L LAY); lia).
  assert (STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr S0.HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
    by (change (CH.hd_scr S0.HDECL) with SCRT; unfold SCRT; repeat split; lia).
  assert (SCRP : 0 <= CH.hd_scr S0.HDECL) by (change (CH.hd_scr S0.HDECL) with SCRT; unfold SCRT; lia).
  assert (NF32 : (32 <= NFV)%nat) by (unfold NFV; lia).
  assert (W_OK : forall (w : L5.range) (a : Z), In w [(o, 24)] -> L5.in_rng w a -> CH2.wclient L sp a).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. split; [lia | left; lia]. }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs S0.HDECL) -> SGP.region_vars_lt NFV rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w [(o, 24)] /\ L5.in_rng w a)).
  { idtac. intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CH2.in_reg, estart, elenZ, e_o in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by lia. exists (o, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  unfold PML.cfg. change PMCS.PC_STRINIT2 with (CC.cp_pc S0.cp0). rewrite <- LS.
  eapply CH2.heap_cert_sound with (NF := NFV) (E0 := E0) (M0 := M) (model0 := model) (LBrest := LB) (sp0 := sp) (d := S0.HDECL)
    (W := [(o, 24)]) (BLS := S0.BLS) (Cred := fun _ _ cr' => cr' = cr) (CPS := S0.CPS) (TAGS := S0.TAGS) (RETS := S0.RETS) (MALLOC := MALLOC) (FREE := FREE)
    (COPIES := [MEMMOVE]) (IMG_LO := GK.HULL_LO) (IMG_HI := GK.HULL_HI) (FPI := PML.fp_ok) (i := 0%nat) (E := E0) (HI := HI).
  - exact HIok.
  - exact LYI.
  - exact LYE.
  - exact (PmLayout.ly_ro L LAY).
  - rewrite LSTK. lia.
  - exact STKF.
  - exact SCRP.
  - rewrite LSTK. reflexivity.
  - exact NF32.
  - exact U2.
  - rewrite V4, (PmLayout.ly_tp L LAY). reflexivity.
  - exact W_OK.
  - intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CH2.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U11, U12 in Ha. split; [lia|]. right; right. exists b. split; [exact Hb | lia].
  - exact WRS_OK.
  - intros rg a [].
  - exact HKnil.
  - exact ILO.
  - exact IHI.
  - rewrite LS. exact FPM.
  - rewrite LS. exact S0.plans.
  - exact S0.tags_ok.
  - exact heap_s.
  - exact (PmLayout.ly_malloc L LAY).
  - exact (PmLayout.ly_free L LAY).
  - intros pc [<-|[]]. exact (Pm10Memmove_u.memmove_copy1 L LS).
  - intros i c kk ps j sg IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ ng_s _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X.
  - intros i c kk ps j cj IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ leaf_s_ok _ _ _ _ _ IL) as X. unfold leaf_s in X.
    change (CH2.is_call MALLOC FREE [MEMMOVE] MALLOC) with true in X. cbv beta iota in X. rewrite Z.eqb_refl in X. discriminate X.
  - intros i c kk ps pc j cj IL Hcall Hnm Hret Hcj E E' R' M1 M1' cr' HagE Hag HLF HC E2 Hag2. exact HC.
  -
    intros i c kk ps pc IL Hnc fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF _.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_s_ok _ _ _ _ _ IL) as X. unfold leaf_s in X. rewrite Hnc in X.
    pose proof (CH2.exit_amb L HI HIok LYI LYE (PmLayout.ly_ro L LAY) NFV E0 M model LB sp S0.HDECL [(o, 24)] S0.BLS (fun _ _ cr' => cr' = cr) STKF SCRP NF32 U2 W_OK WRS_OK
                  S0.CPS GK.HULL_LO GK.HULL_HI S0.TAGS S0.RETS MALLOC FREE [MEMMOVE] heap_s i c kk ps pc IL Hnc E E' R1 R' M1 M' m1 HAt HAmb Hag HLF) as HA'.
    repeat (apply andb_prop in X as [X ?Y]).

    apply Z.eqb_eq in X. apply Nat.leb_le in Y2.
    pose proof HA' as HA2. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr1 & Hdf1). subst cr1.
    assert (HagE' : env_agree NFV E0 E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | exact Y2]]).
    destruct (FR E' HagE') as (F2 & F10 & F11 & F12 & FB).
    rewrite LS in HLF.
    assert (CELL : forall X0, has (SR.ps_cells ps) X0 = true -> kentry_ok GK.RSEGS E' M' X0).
    { intros X0 HX. apply (CC.lf_cells _ _ _ _ _ _ _ HLF). exact (GK.has_In _ _ HX). }
    assert (HBL : nth i S0.BLS [] = []) by (destruct i as [|[|[|]]]; reflexivity). unfold CH2.cur in HH1. rewrite HBL in HH1. cbn [CH2.den map app] in HH1.
    assert (B0 : L5.u8_at GK.RSEGS M' o (2 * n)).
    { apply (GK.kword8_elim E' M' _ _ o (2 * n) (CELL _ Y1)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]]. }
    assert (BS : L5.bytes_at GK.RSEGS M' (o + 1) txt).
    { apply (CL5.kblob_elim GK.RSEGS E' M' _ _ 1%nat (o + 1) txt (CELL _ Y0)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | rewrite FB; reflexivity]. }
    assert (NUL : L5.u8_at GK.RSEGS M' (o + 1 + n) 0).
    { apply (CL5.kword8_zero_elim GK.RSEGS E' M' _ _ (CELL _ Y)). unfold estart. cbn [a_base a_off]. rewrite u_eadd. unfold e_o. cbn [edenot]. rewrite F10, F12. rewrite Z.mod_small by lia. lia. }
    assert (KEEP : forall y : reg, In (ridx y) CSAVED -> getr R' y = getr R y).
    { intros y Hy. rewrite (CL.ps_keeps_sound GK.RSEGS c ps E0 E' R' M1 M' CSAVED NFV y HLF Y3 HagE' Hy (csaved_lt y Hy)). exact (EV y). }
    assert (HRP : regs_preserved R R') by (intros y Hy; apply KEEP; exact (CL5.csaved_in y Hy)).
    assert (Hra' : getr R' 1%bv = Z_to_bv 64 r) by (rewrite (KEEP 1%bv ltac:(left; reflexivity)); exact Hra).
    assert (Hds : L5.defined M (sp - CH.hd_scr S0.HDECL) (CH.hd_scr S0.HDECL)) by (change (CH.hd_scr S0.HDECL) with SCRT; unfold SCRT; exact S5).
    pose proof (CH2.amb_hpres L HI LYI LYE NFV E0 M model LB sp S0.HDECL [(o, 24)] S0.BLS (fun _ _ cr' => cr' = cr) STKF NF32 i E M' m1 HA2 Hds) as HP.
    change (CH.hd_scr S0.HDECL) with SCRT in HP; unfold SCRT in HP.
    rewrite X, LS. eapply CL.ret_cps; [exact ret_at | exact (proj1 Hmo1) | exact (proj1 (proj2 Hmo1)) | |].
    { rewrite Hra'. apply Hoare.ret_ok_even. destruct Hraok as [R1' R2']. rewrite u64_of_Z by lia. exact R2'. }
    rewrite Hra'.
    apply (Hcont fx' R' M' m1 LB cr LB [(o, 24)] HFP); [| exact HRP | exact HP | exact Hbv1 | exact HH1].
    split; [reflexivity|]. split; [reflexivity|]. split; [|auto]. unfold PML.str_at_w, L5.lstr_short. fold n. split; [lia|]. split; [exact B0|]. split; [exact BS | exact NUL].
  - reflexivity.
  -
    rewrite LS.
    assert (Hds : L5.defined M (sp - 8288) 8288) by exact S5.
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok, S0.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_unk. + e_wr. + e_range. + e_align O3.
    + e_unk. + e_wr. + e_range. + e_align S1. + e_disj.
    + eapply CL5.kblob_intro with (bs := txt) (A := src); [ev_start | unfold elenZ; cbn [edenot]; exact U12 | lia | fold n; lia | lia | reflexivity | exact Hbytes | fold n; ev_def].
    + e_unk. + e_range. + e_disj. + e_disj. + e_range.
  - split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr. split; [|reflexivity]. exact HH.
  - exact Hfp.
Qed.

Lemma zero_ok : forall (LB : list (Z * Z)) (cr : credit) (o src sp r : Z),
  PML.cps_heap L HI PMCS.PC_STRINIT2 r sp (48 + PMS.OPNEW_SCR) LB cr
      (fun R M => PML.entry L R M sp r (48 + PMS.OPNEW_SCR) /\ PML.a0 R o /\ PML.a1 R src /\ PML.a2 R 0 /\ PML.obj_on_stack L sp o 24 /\ L5.defined M o 24)
      (fun R M R' M' LB' cr' LBk W => W = [(o, 24)] /\ LBk = LB /\ PML.str_at_w M' o (PML.SShort []) /\ LB' = LB /\ cr' = cr).
Proof.
  intros LB cr o src sp r. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & Ha0 & Ha1 & Ha2 & Hobj & Hdo) Hcont.
  set (txt := @nil Z). change 0 with (Z.of_nat (length txt)) in Ha2. assert (Hn0 : Z.of_nat (length txt) = 0) by reflexivity.
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (S1 & S2 & S3 & S4 & S5).
  unfold PMS.OPNEW_SCR, PML.HEAP_STACK in *.
  destruct Hobj as (O1 & O2 & O3).
  set (n := Z.of_nat (length txt)) in *.
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_stack L LAY) as LSTK. unfold PML.HEAP_STACK in LSTK.
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & _).
  set (E0 := E0_of R txt).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 src) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V12 : ev E0 12 = Z_to_bv 64 n) by (rewrite <- Ha2; exact (EV 12%bv)).
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by lia.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; lia).
  assert (U12 : bv_unsigned (ev E0 12) = n) by (rewrite V12; apply u64_of_Z; lia).
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= 0x7fff7f800000) by (rewrite ILO, IHI; lia).
  assert (LYE : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L) by (rewrite ILO, IHI, (PmLayout.ly_errno L LAY); lia).
  assert (STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr Z0.HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
    by (change (CH.hd_scr Z0.HDECL) with SCRT; unfold SCRT; repeat split; lia).
  assert (SCRP : 0 <= CH.hd_scr Z0.HDECL) by (change (CH.hd_scr Z0.HDECL) with SCRT; unfold SCRT; lia).
  assert (NF32 : (32 <= NFV)%nat) by (unfold NFV; lia).
  assert (W_OK : forall (w : L5.range) (a : Z), In w [(o, 24)] -> L5.in_rng w a -> CH2.wclient L sp a).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. split; [lia | left; lia]. }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs Z0.HDECL) -> SGP.region_vars_lt NFV rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w [(o, 24)] /\ L5.in_rng w a)).
  { idtac. intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CH2.in_reg, estart, elenZ, e_o in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by lia. exists (o, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  unfold PML.cfg. change PMCS.PC_STRINIT2 with (CC.cp_pc Z0.cp0). rewrite <- LS.
  eapply CH2.heap_cert_sound with (NF := NFV) (E0 := E0) (M0 := M) (model0 := model) (LBrest := LB) (sp0 := sp) (d := Z0.HDECL)
    (W := [(o, 24)]) (BLS := Z0.BLS) (Cred := fun _ _ cr' => cr' = cr) (CPS := Z0.CPS) (TAGS := Z0.TAGS) (RETS := Z0.RETS) (MALLOC := MALLOC) (FREE := FREE)
    (COPIES := []) (IMG_LO := GK.HULL_LO) (IMG_HI := GK.HULL_HI) (FPI := PML.fp_ok) (i := 0%nat) (E := E0) (HI := HI).
  - exact HIok.
  - exact LYI.
  - exact LYE.
  - exact (PmLayout.ly_ro L LAY).
  - rewrite LSTK. lia.
  - exact STKF.
  - exact SCRP.
  - rewrite LSTK. reflexivity.
  - exact NF32.
  - exact U2.
  - rewrite V4, (PmLayout.ly_tp L LAY). reflexivity.
  - exact W_OK.
  - intros rg [].
  - exact WRS_OK.
  - intros rg a [].
  - exact HKnil.
  - exact ILO.
  - exact IHI.
  - rewrite LS. exact FPM.
  - rewrite LS. exact Z0.plans.
  - exact Z0.tags_ok.
  - exact heap_z.
  - exact (PmLayout.ly_malloc L LAY).
  - exact (PmLayout.ly_free L LAY).
  - intros pc [].
  - intros i c kk ps j sg IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ leaf_z_ok _ _ _ _ _ IL) as X. discriminate X.
  - intros i c kk ps j cj IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ leaf_z_ok _ _ _ _ _ IL) as X. unfold leaf_z in X.
    change (CH2.is_call MALLOC FREE [] MALLOC) with true in X. discriminate X.
  - intros i c kk ps pc j cj IL Hcall. exfalso. pose proof (CH2.leaves_all_sound _ _ _ leaf_z_ok _ _ _ _ _ IL) as X. unfold leaf_z in X. rewrite Hcall in X. discriminate X.
  -
    intros i c kk ps pc IL Hnc fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF _.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_z_ok _ _ _ _ _ IL) as X. unfold leaf_z in X. rewrite Hnc in X. cbn [negb andb] in X.
    pose proof (CH2.exit_amb L HI HIok LYI LYE (PmLayout.ly_ro L LAY) NFV E0 M model LB sp Z0.HDECL [(o, 24)] Z0.BLS (fun _ _ cr' => cr' = cr) STKF SCRP NF32 U2 W_OK WRS_OK
                  Z0.CPS GK.HULL_LO GK.HULL_HI Z0.TAGS Z0.RETS MALLOC FREE [] heap_z i c kk ps pc IL Hnc E E' R1 R' M1 M' m1 HAt HAmb Hag HLF) as HA'.
    repeat (apply andb_prop in X as [X ?Y]).

    apply Z.eqb_eq in X. apply Nat.leb_le in Y1.
    pose proof HA' as HA2. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr1 & Hdf1). subst cr1.
    assert (HagE' : env_agree NFV E0 E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | exact Y1]]).
    assert (F10 : bv_unsigned (ev E' 10) = o) by (destruct HagE' as [A _]; rewrite <- A by (unfold NFV; lia); exact U10).
    rewrite LS in HLF.
    assert (CELL : forall X0, has (SR.ps_cells ps) X0 = true -> kentry_ok GK.RSEGS E' M' X0).
    { intros X0 HX. apply (CC.lf_cells _ _ _ _ _ _ _ HLF). exact (GK.has_In _ _ HX). }
    assert (HBL : nth i Z0.BLS [] = []) by (destruct i as [|[|]]; reflexivity). unfold CH2.cur in HH1. rewrite HBL in HH1. cbn [CH2.den map app] in HH1.
    assert (B0 : L5.u8_at GK.RSEGS M' o 0).
    { apply (CL5.kword8_zero_elim GK.RSEGS E' M' _ _ (CELL _ Y0)). unfold estart, e_o. cbn [a_base a_off edenot]. rewrite F10. lia. }
    assert (NUL : L5.u8_at GK.RSEGS M' (o + 1) 0).
    { apply (CL5.kword8_zero_elim GK.RSEGS E' M' _ _ (CELL _ Y)). unfold estart, e_o. cbn [a_base a_off edenot]. rewrite F10. lia. }
    assert (KEEP : forall y : reg, In (ridx y) CSAVED -> getr R' y = getr R y).
    { intros y Hy. rewrite (CL.ps_keeps_sound GK.RSEGS c ps E0 E' R' M1 M' CSAVED NFV y HLF Y2 HagE' Hy (csaved_lt y Hy)). exact (EV y). }
    assert (HRP : regs_preserved R R') by (intros y Hy; apply KEEP; exact (CL5.csaved_in y Hy)).
    assert (Hra' : getr R' 1%bv = Z_to_bv 64 r) by (rewrite (KEEP 1%bv ltac:(left; reflexivity)); exact Hra).
    assert (Hds : L5.defined M (sp - CH.hd_scr Z0.HDECL) (CH.hd_scr Z0.HDECL)) by (change (CH.hd_scr Z0.HDECL) with SCRT; unfold SCRT; exact S5).
    pose proof (CH2.amb_hpres L HI LYI LYE NFV E0 M model LB sp Z0.HDECL [(o, 24)] Z0.BLS (fun _ _ cr' => cr' = cr) STKF NF32 i E M' m1 HA2 Hds) as HP.
    change (CH.hd_scr Z0.HDECL) with SCRT in HP; unfold SCRT in HP.
    rewrite X, LS. eapply CL.ret_cps; [exact ret_at | exact (proj1 Hmo1) | exact (proj1 (proj2 Hmo1)) | |].
    { rewrite Hra'. apply Hoare.ret_ok_even. destruct Hraok as [R1' R2']. rewrite u64_of_Z by lia. exact R2'. }
    rewrite Hra'.
    apply (Hcont fx' R' M' m1 LB cr LB [(o, 24)] HFP); [| exact HRP | exact HP | exact Hbv1 | exact HH1].
    split; [reflexivity|]. split; [reflexivity|]. split; [|auto]. unfold PML.str_at_w, L5.lstr_short. cbn [length Z.of_nat]. split; [lia|]. split; [exact B0|].
    split; [intros j Hj; cbn in Hj; lia | rewrite Z.add_0_r; exact NUL].
  - reflexivity.
  -
    rewrite LS.
    assert (Hds : L5.defined M (sp - 8288) 8288) by exact S5.
    split.
    { change (CC.cp_regs Z0.cp0) with (sr_upd sr_id 12 (ELit 0)). apply (regs_ok_pin E0 sr_id R 12%bv); [exact (regs_ok_id R _ _)|]. rewrite Ha2. reflexivity. }
    unfold know_ok, Z0.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_unk. + e_wr. + e_range. + e_align O3.
    + e_unk. + e_wr. + e_range. + e_align S1. + e_disj.
  - split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr. split; [|reflexivity]. exact HH.
  - exact Hfp.
Qed.

Theorem strinit2_ok : PMCS.strinit2_spec L HI.
Proof.
  intros LB cr o src sp r txt. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & Ha0 & Ha1 & Ha2 & Hlen & Hbytes & Hdef & Hobj & Hdo & Hsrc & Hcredit) Hcont.
  destruct txt as [|c0 txt'].
  - apply (zero_ok LB cr o src sp r fx R M model K HH Hmo HKnil Hfp); [repeat (split; [assumption|]); assumption|].
    intros fx' R' M' model' LB' cr' LBk W HFP (HW & HLBk & Hstr & HLB & Hcr) HRP HP Hbv HH2.
    apply (Hcont fx' R' M' model' LB' cr' LBk W HFP); [|assumption..]. split; [exact HW|]. split; [exact HLBk|]. left. cbn [length]. split; [lia|]. auto.
  - set (txt := c0 :: txt') in *. destruct Hsrc as [Hnil|Hsrc]; [discriminate Hnil|].
    assert (Hn1 : 1 <= Z.of_nat (length txt)) by (unfold txt; cbn [length]; lia).
    destruct (Z_le_gt_dec (Z.of_nat (length txt)) 22) as [Hs|Hl].
    + apply (sso_ok LB cr o src sp r txt fx R M model K HH Hmo HKnil Hfp); [split; [lia|]; repeat (split; [assumption|]); assumption|].
      intros fx' R' M' model' LB' cr' LBk W HFP (HW & HLBk & Hstr & HLB & Hcr) HRP HP Hbv HH2.
      apply (Hcont fx' R' M' model' LB' cr' LBk W HFP); [|assumption..]. split; [exact HW|]. split; [exact HLBk|]. left. split; [lia|]. auto.
    + assert (H23 : (23 <= length txt)%nat) by lia. specialize (Hcredit H23).
      destruct (Z.eq_dec (Z.of_nat (length txt)) 23) as [He|Hne].
      * apply (ok_n23 LB cr o src sp r txt fx R M model K HH Hmo HKnil Hfp); [split; [exact He|]; repeat (split; [assumption|]); assumption|].
        intros fx' R' M' model' LB' cr' LBk W HFP (HW & HLBk & Hpost) HRP HP Hbv HH2.
        apply (Hcont fx' R' M' model' LB' cr' LBk W HFP); [|assumption..]. split; [exact HW|]. split; [exact HLBk|]. right. split; [exact H23 | exact Hpost].
      * apply (ok_lg LB cr o src sp r txt fx R M model K HH Hmo HKnil Hfp); [split; [lia|]; repeat (split; [assumption|]); assumption|].
        intros fx' R' M' model' LB' cr' LBk W HFP (HW & HLBk & Hpost) HRP HP Hbv HH2.
        apply (Hcont fx' R' M' model' LB' cr' LBk W HFP); [|assumption..]. split; [exact HW|]. split; [exact HLBk|]. right. split; [exact H23 | exact Hpost].
Qed.
End Final.
End SI2.

