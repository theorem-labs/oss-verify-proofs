(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_append_range_zero_csrc_T_u Cut_append_range_zero_csrc_u Cut_append_range_b0_csrc_T_u Cut_append_range_b0_csrc_u Cut_append_range_b1_csrc_T_u Cut_append_range_b1_csrc_u
  Cut_append_range_a0_csrc_T_u Cut_append_range_a0_csrc_u Cut_append_range_a1_csrc_T_u Cut_append_range_a1_csrc_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutDemo Require Pm10Memmove_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmGrow Require Import GrowKit_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module AR.
Definition MALLOC : Z := PML.PC_MALLOC.  Definition FREE : Z := PML.PC_FREE.  Definition MEMMOVE : Z := 0xb7c98.
Definition RET : Z := Eval vm_compute in hd 0 Cut_append_range_b1_csrc_T_u.ENDS.
Definition SCRT : Z := Eval vm_compute in CH.hd_scr Cut_append_range_b1_csrc_u.HDECL.
Definition CSAVED := CL5.CSAVED.
Definition has := GK.has.
Definition NFV : nat := 48.

Definition e_o := EVar 10.  Definition e_q := EVar 11.  Definition e_k := EVar 32.  Definition e_p := EVar 34.  Definition e_n := EVar 35.
Definition CAP : expr := EMd M_MUL (ELit 2) e_k.
Definition CAP2 : expr := EAlu ALU_ADD (EMd M_MUL (ELit 4) e_k) (ELit (-2)).
Definition round8 (x : expr) (c : Z) : expr := EAlu ALU_ADD (EMd M_MUL (ELit 8) (EAlu ALU_SRL x (ELit 3))) (ELit c).

Section Chk.
Variable s0 : bool.
Variables (BLS : list CA.blocks) (CPS : list CC.cutpoint) (RETS : list (nat * nat * nat * Z)).
Definition e_size : expr := if s0 then ELit 0 else EVar 33.
Definition NEED : expr := if s0 then e_n else EAlu ALU_ADD (EVar 33) e_n.
Definition ROOM : expr := if s0 then EAlu ALU_ADD (EMd M_MUL (ELit 2) e_k) (ELit (-1))
                          else EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 2) e_k) (EMd M_MUL (ELit (-1)) (EVar 33))) (ELit (-1)).
Definition pre (i : nat) : bool := (Nat.eqb i 0 || Nat.eqb i 3)%bool.
Definition hd_base (i : nat) : expr := fst (hd (ELit 0, ELit 0) (nth i BLS [])).
Definition hd_size (i : nat) : expr := snd (hd (ELit 0, ELit 0) (nth i BLS [])).
Definition arm_chk (cells : list kentry) (e : expr) : bool :=
  (has cells (KRange (EAlu ALU_SLTU ROOM e_n) 1 1)
   && ((expr_eqb e (round8 NEED 8) && has cells (KRange (EAlu ALU_SLTU CAP2 NEED) 1 1))
       || (expr_eqb e (round8 CAP2 8) && has cells (KRange (EAlu ALU_SLTU CAP2 NEED) 0 0))))%bool.
Definition exit_chk (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in let pe := hd_base i in let ce := hd_size i in
  (CL.ps_at ps [RET] && CL.ps_keeps ps CSAVED && CH2.blocks_vars_lt (CC.cp_nx c) (nth i BLS []) && Nat.leb NFV (CC.cp_nx c)
   && has cells (KWord (SA e_o 0) 8 (APC.eaddz ce 1)) && has cells (KWord (SA e_o 8) 8 NEED) && has cells (KWord (SA e_o 16) 8 pe)
   && (s0 || has cells (KBlob (SA pe 0) e_size 0))
   && has cells (KBlob (SA (APC.eadd e_size pe) 0) e_n 1)
   && has cells (KWord (SA (APC.eadd e_size (APC.eadd e_n pe)) 0) 1 (ELit 0))
   && match nth i BLS [] with [_] => true | _ => false end
   && (if pre i then (expr_eqb pe e_p && expr_eqb ce CAP && has cells (KRange (EAlu ALU_SLTU ROOM e_n) 0 0))
       else (arm_chk cells ce && has cells (KDisj (SA pe 0) ce (SA e_p 0) CAP)
             && match pe with EVar v => Nat.leb NFV v | _ => false end)))%bool.
Definition leaf_facts_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      if CH2.is_call MALLOC FREE [MEMMOVE] pc then
        match CH2.ret_of RETS i k with
        | Some j =>
            match nth_error CPS j with
            | Some cj =>
                (Nat.leb NFV (CC.cp_nx c) && Nat.leb (CC.cp_nx c) (CC.cp_nx cj - APC.NCS)
                 && if Z.eqb pc MALLOC then (pre i && negb (pre j) && expr_eqb (hd_size j) (CA.ps_reg ps 10) && APC.expr_vars_lt NFV (hd_size j) && arm_chk (SR.ps_cells ps) (hd_size j))
                    else (Bool.eqb (pre i) (pre j) && (pre i || (expr_eqb (hd_size i) (hd_size j) && APC.expr_vars_lt NFV (hd_size i)))))%bool
            | None => false
            end
        | None => false
        end
      else exit_chk i c ps
  end.
End Chk.

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

Definition E0_of (R : bvmap 5 word) (k size p n : Z) (s src : list Z) : env :=
  Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [k; size; p; n] 0))) (fun id => nth id [map (Z_to_bv 8) s; map (Z_to_bv 8) src] []).

Definition SP : expr := EVar 2.
Definition COMMON (s0 : bool) : list kentry :=
  let size := e_size s0 in
  [KWord (SA e_o 0) 8 (APC.eaddz CAP 1); KWord (SA e_o 8) 8 size; KWord (SA e_o 16) 8 e_p; KRange e_k 12 (2 ^ 46)] ++
  (if s0 then [] else [KRange size 1 (2 ^ 26); KRange (APC.esub (APC.eaddz CAP (-1)) size) 0 (2 ^ 47); KRange (APC.eadd size e_n) 1 (2 ^ 26); KBlob (SA e_p 0) size 0]) ++
  [KUnk (SA e_p 0) CAP; KWr (SA e_p 0) CAP; KRange e_p 4096 (2 ^ 47); KAlign e_p 16;
   KUnk (SA e_o 0) (ELit 24); KWr (SA e_o 0) (ELit 24); KRange e_o 4096 (2 ^ 47); KAlign e_o 8;
   KBlob (SA e_q 0) e_n 1; KUnk (SA e_q 0) e_n; KRange e_q 4096 (2 ^ 47); KRange e_n 1 (2 ^ 26);
   KUnk (SA SP (- SCRT)) (ELit SCRT); KWr (SA SP (- SCRT)) (ELit SCRT); KRange SP (2 ^ 40) (2 ^ 47); KAlign SP 16;
   KDisj (SA SP (- SCRT)) (ELit SCRT) (SA e_o 0) (ELit 24); KDisj (SA SP (- SCRT)) (ELit SCRT) (SA e_p 0) CAP; KDisj (SA SP (- SCRT)) (ELit SCRT) (SA e_q 0) e_n;
   KDisj (SA e_o 0) (ELit 24) (SA e_p 0) CAP; KDisj (SA e_o 0) (ELit 24) (SA e_q 0) e_n; KDisj (SA e_p 0) CAP (SA e_q 0) e_n].
Definition PS1 (s0 : bool) : expr := APC.eaddz (APC.eadd (e_size s0) e_p) 1.
Definition POSX (s0 below : bool) : list kentry :=
  (if below then [KRange (APC.esub (APC.esub e_p e_q) e_n) 0 (2 ^ 47)]
   else [KRange (APC.esub (APC.esub e_q e_p) CAP) 0 (2 ^ 47); KRange (APC.esub (APC.esub e_q e_p) (APC.eaddz (e_size s0) 1)) 0 (2 ^ 47)]) ++

  (let bit := if below then 1 else 0 in [KRange (EAlu ALU_SLTU e_q e_p) bit bit; KRange (EAlu ALU_SLTU e_q (PS1 s0)) bit bit]).
Fixpoint exprs_eqb (a b : list expr) : bool := match a, b with [], [] => true | x :: a', y :: b' => (expr_eqb x y && exprs_eqb a' b')%bool | _, _ => false end.
Lemma exprs_eqb_eq : forall a b, exprs_eqb a b = true -> a = b.
Proof. induction a as [|x a IH]; intros [|y b] H; try discriminate H; [reflexivity|]. cbn in H. apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1. rewrite H1, (IH b H2). reflexivity. Qed.
Definition kn_chk (s0 below : bool) (cp0 : CC.cutpoint) : bool :=
  (forallb (fun K => has (COMMON s0 ++ POSX s0 below) K) (CC.cp_know cp0)
   && exprs_eqb (CC.cp_regs cp0) (sr_upd sr_id 12 (APC.eadd e_q e_n)))%bool.

Lemma ret_at : CL.is_ret_at GK.RSEGS RET.
Proof. CL.solve_is_ret. Qed.

Lemma csaved_lt : forall y : reg, In (ridx y) CSAVED -> (ridx y < NFV)%nat.
Proof. intros y Hy. unfold CSAVED, CL5.CSAVED in Hy. cbn [In] in Hy. unfold NFV. intuition lia. Qed.
Lemma grow_room : forall need cap, 0 <= need -> 1 <= cap -> need < 8 * (Z.max need (2 * (cap - 1)) / 8) + 8.
Proof. intros need cap H0 H1. pose proof (Z.mod_pos_bound (Z.max need (2 * (cap - 1))) 8 ltac:(lia)). pose proof (Z.div_mod (Z.max need (2 * (cap - 1))) 8 ltac:(lia)). lia. Qed.

Section Gen.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps GK.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom GK.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom GK.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Variables (s0 below : bool).
Variables (HDECL : CH.hdecl) (BLS : list CA.blocks) (CPS : list CC.cutpoint) (TAGS : list (list CC.tag)) (RETS : list (nat * nat * nat * Z)) (cp0 : CC.cutpoint).
Hypothesis H_hd : HDECL = CH.HD SCRT 8224 [(e_q, 0, e_n)] [(e_o, 0, ELit 24)] [].
Hypothesis H_cp0 : nth_error CPS 0 = Some cp0.
Hypothesis H_pc : CC.cp_pc cp0 = PML.PC_APPEND_RANGE.
Hypothesis H_BL0 : nth 0 BLS [] = [(e_p, CAP)].
Hypothesis H_kn : kn_chk s0 below cp0 = true.
Hypothesis plans : forall i c, nth_error CPS i = Some c -> CC.plan_sound GK.RSEGS c.
Hypothesis tags_ok : CC.tags_chk CPS TAGS NFV = true.
Hypothesis heap_ok : CH2.heap_chk NFV HDECL BLS CPS GK.HULL_LO GK.HULL_HI TAGS RETS MALLOC FREE [MEMMOVE] = true.
Hypothesis no_goto : CH2.leaves_all CPS TAGS (fun _ _ _ _ t => match t with CC.TGoto _ _ => false | CC.TOther _ => true end) = true.
Hypothesis leaf_facts_ok : CH2.leaves_all CPS TAGS (leaf_facts_chk s0 BLS CPS RETS) = true.

Definition Cred (cr0 : credit) (i : nat) (E : env) (cr : credit) : Prop :=
  cr = if pre i then cr0 else debit L cr0 (snd (hd (0, 0) (CH2.den E (nth i BLS [])))).

Lemma gen_ok : forall (LB : list (Z * Z)) (cr : credit) (o cap p q sp r : Z) (s src : list Z),
  PML.cps_heap L HI PML.PC_APPEND_RANGE r sp PMS.STR_SCR LB cr
      (fun R M => (24 <= cap /\ src <> [] /\ (if s0 then s = [] else s <> []) /\
                   (if below then q + Z.of_nat (length src) <= p else p + cap <= q)) /\
                  PML.entry L R M sp r PMS.STR_SCR /\ PML.a0 R o /\ PML.a1 R q /\ PML.a2 R (q + Z.of_nat (length src)) /\
                  PML.str_at M o (PML.SLong cap p s) /\ In (p, cap) LB /\ PML.obj_on_stack L sp o 24 /\
                  L5.bytes_at GK.RSEGS M q src /\ L5.defined M q (Z.of_nat (length src)) /\
                  (exists b, In b LB /\ fst b <> p /\ fst b <= q /\ q + Z.of_nat (length src) <= fst b + snd b) /\
                  Z.of_nat (length s) + Z.of_nat (length src) < 2 ^ 26 /\
                  (cap <= Z.of_nat (length s) + Z.of_nat (length src) -> credit_ok L cr (PML.grow_cap cap (Z.of_nat (length s) + Z.of_nat (length src)))))
      (fun R M R' M' LB' cr' LBk W => PMS.str_grown L LB cr M' o cap p (s ++ src) LB' cr' LBk /\ W = [(o, 24)]).
Proof.
  intros LB cr o cap p q sp r s src. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp ((H24 & Hne & Hs0 & Hpos) & Hentry & Ha0 & Ha1 & Ha2 & Hstr & HinLB & Hobj & Hbytes & Hdef & Hsrc & Hlen & Hcredit) Hcont.
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (S1 & S2 & S3 & S4 & S5).
  unfold PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK in *.
  destruct Hstr as ((Hbit & Hw0 & Hw8 & Hw16 & Hbs & Hnul) & Hc8 & Hslt).
  destruct Hsrc as (b & Hb & Hbp & Hbq1 & Hbq2).
  destruct Hobj as (O1 & O2 & O3).
  set (n := Z.of_nat (length src)) in *. set (size := Z.of_nat (length s)) in *.
  assert (Hn1 : 1 <= n) by (destruct src; [contradiction | unfold n; cbn [length]; lia]).
  assert (Hsz : if s0 then size = 0 else 1 <= size) by (destruct s0; [subst s; reflexivity | destruct s; [contradiction | unfold size; cbn [length]; lia]]).
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_stack L LAY) as LSTK. unfold PML.HEAP_STACK in LSTK.
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & _).
  destruct (Hwf _ HinLB) as ((P0 & P1 & P2 & P3 & P4) & Pdef & Pap). cbn [fst snd] in *.
  destruct (Hwf _ Hb) as ((B0' & B1' & B2' & B3' & B4') & Bdef & Bap).
  pose proof (CH2.heap_own_front L HI HIok LB cr M _ p cap HH HinLB) as HH'.
  set (k := cap / 2). assert (Hk : cap = 2 * k) by (unfold k; assert (cap mod 2 = 0) by (rewrite <- (Z.mod_mod_divide cap 8 2) by (exists 4; reflexivity); rewrite Hc8; reflexivity); rewrite (Z.div_mod cap 2) at 1 by lia; lia).
  set (E0 := E0_of R k size p n s src).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 q) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 k) by reflexivity.
  assert (V33 : ev E0 33 = Z_to_bv 64 size) by reflexivity.
  assert (V34 : ev E0 34 = Z_to_bv 64 p) by reflexivity.
  assert (V35 : ev E0 35 = Z_to_bv 64 n) by reflexivity.
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by lia.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; lia).
  assert (U11 : bv_unsigned (ev E0 11) = q) by (rewrite V11; apply u64_of_Z; lia).
  assert (U32 : bv_unsigned (ev E0 32) = k) by (rewrite V32; apply u64_of_Z; lia).
  assert (U33 : bv_unsigned (ev E0 33) = size) by (rewrite V33; apply u64_of_Z; lia).
  assert (U34 : bv_unsigned (ev E0 34) = p) by (rewrite V34; apply u64_of_Z; lia).
  assert (U35 : bv_unsigned (ev E0 35) = n) by (rewrite V35; apply u64_of_Z; lia).
  assert (HinRest : In b (lb_remove p LB)) by (destruct b as [bb bm]; exact (L5C.in_lb_remove_neq p bb bm LB Hb Hbp)).
  pose proof (Pap b HinRest) as Hapart.

  assert (FR : forall E1, env_agree NFV E0 E1 ->
            bv_unsigned (ev E1 2) = sp /\ bv_unsigned (ev E1 10) = o /\ bv_unsigned (ev E1 11) = q /\
            bv_unsigned (ev E1 32) = k /\ bv_unsigned (ev E1 33) = size /\ bv_unsigned (ev E1 34) = p /\ bv_unsigned (ev E1 35) = n /\ eb E1 = eb E0).
  { intros E1 [A B]. rewrite <- !A by (unfold NFV; lia). repeat split; try assumption. symmetry. exact B. }
  assert (VX : forall E1, env_agree NFV E0 E1 ->
            bv_unsigned (edenot E1 (e_size s0)) = size /\ bv_unsigned (edenot E1 (NEED s0)) = size + n /\ bv_unsigned (edenot E1 (ROOM s0)) = 2 * k - size - 1 /\
            bv_unsigned (edenot E1 CAP2) = 4 * k - 2 /\ bv_unsigned (edenot E1 CAP) = cap).
  { intros E1 Hag1. destruct (FR E1 Hag1) as (F2 & F10 & F11 & F32 & F33 & F34 & F35 & _). unfold e_size, NEED, ROOM, CAP2, CAP, e_n, e_k.
    destruct s0; (split; [first [exact F33 | cbn [edenot]; rewrite u64_of_Z by lia; lia]|]); (split; [apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]|]);
      (split; [apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]|]); (split; apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia | lin_eval; rw_atoms; lia | lia]). }

  assert (ARM : forall E1 M1 cells e, env_agree NFV E0 E1 -> (forall K0, In K0 cells -> kentry_ok GK.RSEGS E1 M1 K0) -> arm_chk s0 cells e = true ->
            bv_unsigned (edenot E1 e) = PML.grow_cap cap (size + n) /\ cap <= size + n).
  { intros E1 M1 cells e Hag1 Hc Harm. destruct (FR E1 Hag1) as (F2 & F10 & F11 & F32 & F33 & F34 & F35 & _). destruct (VX E1 Hag1) as (US & UN & UR & UC & _).
    unfold arm_chk in Harm. apply andb_prop in Harm as [Hg Harm].
    assert (HAS : forall X, has cells X = true -> kentry_ok GK.RSEGS E1 M1 X) by (intros X HX; apply Hc; exact (GK.has_In _ _ HX)).
    pose proof (HAS _ Hg) as G0. cbn [kentry_ok] in G0. change (edenot E1 (EAlu ALU_SLTU (ROOM s0) e_n)) with (alu64 ALU_SLTU (edenot E1 (ROOM s0)) (edenot E1 e_n)) in G0.
    rewrite u_sltu64, UR in G0. unfold e_n in G0. cbn [edenot] in G0. rewrite F35 in G0.
    destruct (Z.ltb_spec (2 * k - size - 1) n) as [Hgrow|]; [|lia]. split; [|lia].
    unfold PML.grow_cap. apply orb_prop in Harm as [Harm|Harm]; apply andb_prop in Harm as [He Hf]; apply expr_eqb_eq in He; subst e;
      pose proof (HAS _ Hf) as G2; cbn [kentry_ok] in G2; change (edenot E1 (EAlu ALU_SLTU CAP2 (NEED s0))) with (alu64 ALU_SLTU (edenot E1 CAP2) (edenot E1 (NEED s0))) in G2;
      rewrite u_sltu64, UC, UN in G2.
    - destruct (Z.ltb_spec (4 * k - 2) (size + n)) as [Hlt|]; [|lia].
      rewrite Z.max_l by lia. rewrite CL5.lor7 by lia. rewrite (round8_val E1 (NEED s0) (size + n) UN) by lia. lia.
    - destruct (Z.ltb_spec (4 * k - 2) (size + n)) as [|Hge]; [lia|].
      rewrite Z.max_r by lia. replace (2 * (cap - 1)) with (4 * k - 2) by lia. rewrite CL5.lor7 by lia. rewrite (round8_val E1 CAP2 (4 * k - 2) UC) by lia. lia. }

  assert (HSCR : CH.hd_scr HDECL = SCRT) by (rewrite H_hd; reflexivity).
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= 0x7fff7f800000) by (rewrite ILO, IHI; lia).
  assert (LYE : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L) by (rewrite ILO, IHI, (PmLayout.ly_errno L LAY); lia).
  assert (STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
    by (rewrite HSCR; unfold SCRT; repeat split; lia).
  assert (SCRP : 0 <= CH.hd_scr HDECL) by (rewrite HSCR; unfold SCRT; lia).
  assert (NF32 : (32 <= NFV)%nat) by (unfold NFV; lia).
  assert (W_OK : forall (w : L5.range) (a : Z), In w [(o, 24)] -> L5.in_rng w a -> CH2.wclient L sp a).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. split; [lia | left; lia]. }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs HDECL) -> SGP.region_vars_lt NFV rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w [(o, 24)] /\ L5.in_rng w a)).
  { rewrite H_hd. intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CH2.in_reg, estart, elenZ, e_o in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by lia. exists (o, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  unfold PML.cfg. rewrite <- H_pc. rewrite <- LS.
  eapply CH2.heap_cert_sound with (NF := NFV) (E0 := E0) (M0 := M) (model0 := model) (LBrest := lb_remove p LB) (sp0 := sp) (d := HDECL)
    (W := [(o, 24)]) (BLS := BLS) (Cred := Cred cr) (CPS := CPS) (TAGS := TAGS) (RETS := RETS) (MALLOC := MALLOC) (FREE := FREE)
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
  -   rewrite H_hd. intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CH2.in_reg, estart, elenZ, e_q, e_n in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U11, U35 in Ha. split; [lia|]. right; right. exists b. split; [exact HinRest | lia].
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
    pose proof (CH2.leaves_all_sound _ _ _ leaf_facts_ok _ _ _ _ _ IL) as X. unfold leaf_facts_chk in X.
    change (CH2.is_call MALLOC FREE [MEMMOVE] MALLOC) with true in X. cbv beta iota in X. rewrite Hret, Hcj in X. change (Z.eqb MALLOC MALLOC) with true in X. cbv beta iota in X.
    apply andb_prop in X as [X XM]. apply andb_prop in X as [XA XB]. apply Nat.leb_le in XA, XB.
    repeat (apply andb_prop in XM as [XM ?Z]). apply expr_eqb_eq in Z1. apply negb_true_iff in Z2.
    assert (HagE' : env_agree NFV E0 E') by (eapply CC.env_agree_trans; [exact HagE | eapply CC.env_agree_le; [exact Hag | exact XA]]).
    rewrite LS in HLF. destruct (ARM E' M1' (SR.ps_cells ps) (hd_size BLS j) HagE' (CC.lf_cells _ _ _ _ _ _ _ HLF) Z) as [Hval Hgrow].
    unfold Cred in HC. rewrite XM in HC. subst cr'. rewrite <- Z1. rewrite Hval. split; [apply Hcredit; lia|].
    intros E2 Hag2. unfold Cred. rewrite Z2. rewrite GK.den_hd. fold (hd_size BLS j). f_equal. rewrite <- Hval.
    f_equal. apply (SR.edenot_agree_AP NFV E' E2); [eapply CC.env_agree_le; [exact Hag2 | lia] | exact Z0].
  -
    intros i c kk ps pc j cj IL Hcall Hnm Hret Hcj E E' R' M1 M1' cr' HagE Hag HLF HC E2 Hag2.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_facts_ok _ _ _ _ _ IL) as X. unfold leaf_facts_chk in X. rewrite Hcall, Hret, Hcj in X.
    destruct (Z.eqb_spec pc MALLOC) as [->|_]; [contradiction|].
    apply andb_prop in X as [X XM]. apply andb_prop in X as [XA XB]. apply Nat.leb_le in XA, XB. apply andb_prop in XM as [Y Z]. apply Bool.eqb_prop in Y.
    unfold Cred in *. rewrite <- Y. destruct (pre i) eqn:Hpre; [exact HC|]. cbn [orb] in Z. apply andb_prop in Z as [Z2 Z3]. apply expr_eqb_eq in Z2.
    rewrite HC. f_equal. rewrite !GK.den_hd. fold (hd_size BLS i) (hd_size BLS j). rewrite <- Z2. f_equal.
    apply (SR.edenot_agree_AP NFV E E2); [|exact Z3].
    eapply CC.env_agree_trans; [eapply CC.env_agree_le; [exact Hag | exact XA] | eapply CC.env_agree_le; [exact Hag2 | lia]].
  -
    intros i c kk ps pc IL Hnc fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF _.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_facts_ok _ _ _ _ _ IL) as X. unfold leaf_facts_chk in X. rewrite Hnc in X. unfold exit_chk in X.
    pose proof (CH2.exit_amb L HI HIok LYI LYE (PmLayout.ly_ro L LAY) NFV E0 M model (lb_remove p LB) sp HDECL [(o, 24)] BLS (Cred cr) STKF SCRP NF32 U2 W_OK WRS_OK
                  CPS GK.HULL_LO GK.HULL_HI TAGS RETS MALLOC FREE [MEMMOVE] heap_ok i c kk ps pc IL Hnc E E' R1 R' M1 M' m1 HAt HAmb Hag HLF) as HA'.
    repeat (apply andb_prop in X as [X ?Y]).

    apply Z.eqb_eq in X. apply Nat.leb_le in Y7.
    pose proof HA' as HA2. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr1 & Hdf1).
    assert (HagE' : env_agree NFV E0 E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | exact Y7]]).
    destruct (FR E' HagE') as (F2 & F10 & F11 & F32 & F33 & F34 & F35 & FB). destruct (VX E' HagE') as (US & UN & UR & UC & UCAP).
    rewrite LS in HLF.
    assert (CELL : forall X0, has (SR.ps_cells ps) X0 = true -> kentry_ok GK.RSEGS E' M' X0).
    { intros X0 HX. apply (CC.lf_cells _ _ _ _ _ _ _ HLF). exact (GK.has_In _ _ HX). }
    unfold hd_base, hd_size in *. destruct (nth i BLS []) as [|[pe ce] [|]] eqn:HBL; try discriminate Y0. cbn [hd fst snd] in *.
    set (pX := bv_unsigned (edenot E' pe)) in *. set (capX := bv_unsigned (edenot E' ce)) in *.
    assert (HH2 : hi_heap HI ((pX, capX) :: lb_remove p LB) cr1 M' (m_vmmaps m1)).
    { unfold CH2.cur in HH1. rewrite HBL in HH1. rewrite <- (CH2.den_agree _ E E' _ Hag Y8) in HH1. exact HH1. }
    destruct (hio_wf L SCFG HI HIok _ _ _ _ HH2) as (Hwf2 & Hnd2 & _).
    destruct (Hwf2 (pX, capX) (or_introl eq_refl)) as ((Q0 & Q1 & Q2 & Q3 & Q4) & Qdef & Qap). cbn [fst snd lb_remove] in Q0, Q1, Q2, Q3, Q4, Qdef, Qap. rewrite Z.eqb_refl in Qap.

    assert (UW0 : bv_unsigned (edenot E' (APC.eaddz ce 1)) = capX + 1).
    { unfold APC.eaddz. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite (u64_of_Z 1) by lia. fold capX. apply Z.mod_small. lia. }
    assert (USP : bv_unsigned (edenot E' (APC.eadd (e_size s0) pe)) = size + pX) by (rewrite u_eadd, US; fold pX; apply Z.mod_small; lia).
    assert (UNSP : bv_unsigned (edenot E' (APC.eadd (e_size s0) (APC.eadd e_n pe))) = size + (n + pX)).
    { rewrite !u_eadd, US. unfold e_n. cbn [edenot]. rewrite F35. fold pX. rewrite (Z.mod_small (n + pX)) by lia. apply Z.mod_small. lia. }
    assert (W0 : L5.u64_at GK.RSEGS M' o (capX + 1)).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ o _ (CELL _ Y6)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | exact UW0]. }
    assert (W8 : L5.u64_at GK.RSEGS M' (o + 8) (size + n)).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ (o + 8) _ (CELL _ Y5)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | exact UN]. }
    assert (W16 : L5.u64_at GK.RSEGS M' (o + 16) pX).
    { apply (CL5.kword64_elim GK.RSEGS E' M' _ _ (o + 16) _ (CELL _ Y4)); [unfold estart, e_o; cbn [a_base a_off edenot]; rewrite F10; lia | reflexivity]. }
    assert (NUL : L5.u8_at GK.RSEGS M' (pX + (size + n)) 0).
    { apply (CL5.kword8_zero_elim GK.RSEGS E' M' _ _ (CELL _ Y1)). unfold estart. cbn [a_base a_off]. rewrite UNSP. lia. }
    assert (BSRC : L5.bytes_at GK.RSEGS M' (pX + size) src).
    { apply (CL5.kblob_elim GK.RSEGS E' M' _ _ 1%nat (pX + size) src (CELL _ Y2)); [unfold estart; cbn [a_base a_off]; rewrite USP; lia | rewrite FB; reflexivity]. }
    assert (BS : L5.bytes_at GK.RSEGS M' pX s).
    { apply orb_prop in Y3 as [Y3|Y3].
      - rewrite Y3 in Hs0. subst s. intros j Hj. cbn in Hj. lia.
      - apply (CL5.kblob_elim GK.RSEGS E' M' _ _ 0%nat pX s (CELL _ Y3)); [unfold estart; cbn [a_base a_off]; fold pX; lia | rewrite FB; reflexivity]. }
    assert (STR : Z.even capX = true -> L5.lstr_long GK.RSEGS M' o (s ++ src) (capX + 1) pX).
    { intros Hev. unfold L5.lstr_long. rewrite length_app, Nat2Z.inj_add. fold size n.
      split; [rewrite Z.bit0_odd, Z.odd_add, <- Z.negb_even, Hev; reflexivity|]. split; [exact W0|]. split; [exact W8|].
      split; [exact W16|]. split; [apply CL5.bytes_at_app; [exact BS | fold size; exact BSRC] | exact NUL]. }

    assert (KEEP : forall y : reg, In (ridx y) CSAVED -> getr R' y = getr R y).
    { intros y Hy. rewrite (CL.ps_keeps_sound GK.RSEGS c ps E0 E' R' M1 M' CSAVED NFV y HLF Y9 HagE' Hy (csaved_lt y Hy)). exact (EV y). }
    assert (HRP : regs_preserved R R') by (intros y Hy; apply KEEP; exact (CL5.csaved_in y Hy)).
    assert (Hra' : getr R' 1%bv = Z_to_bv 64 r) by (rewrite (KEEP 1%bv ltac:(left; reflexivity)); exact Hra).
    assert (Hds : L5.defined M (sp - CH.hd_scr HDECL) (CH.hd_scr HDECL)).
    { rewrite HSCR. unfold SCRT. intros j Hj. replace (sp - 8400 + j) with (sp - (256 + (16 + 8224)) + (j + 96)) by lia. apply S5. lia. }
    pose proof (CH2.amb_hpres L HI LYI LYE NFV E0 M model (lb_remove p LB) sp HDECL [(o, 24)] BLS (Cred cr) STKF NF32 i E M' m1 HA2 Hds) as HP0.
    rewrite HSCR in HP0.
    assert (HP : L5C.hpres L (lb_remove p LB) sp (256 + (16 + 8224)) [(o, 24)] M M').
    { apply (GK.hpres_scr L _ sp SCRT); [unfold SCRT; lia | exact S5 | lia | rewrite (PmLayout.ly_errno L LAY); lia | lia | lia | exact HP0]. }
    rewrite X, LS. eapply CL.ret_cps; [exact ret_at | exact (proj1 Hmo1) | exact (proj1 (proj2 Hmo1)) | |].
    { rewrite Hra'. apply Hoare.ret_ok_even. destruct Hraok as [R1' R2']. rewrite u64_of_Z by lia. exact R2'. }
    rewrite Hra'.
    assert (LEN : Z.of_nat (length (s ++ src)) = size + n) by (rewrite length_app, Nat2Z.inj_add; reflexivity).
    destruct (pre i) eqn:Hpre.
    +
      apply andb_prop in Y as [Y Yg]. apply andb_prop in Y as [Yp Yc]. apply expr_eqb_eq in Yp, Yc. subst pe ce.
      assert (EpX : pX = p) by (unfold pX, e_p; cbn [edenot]; exact F34).
      assert (EcX : capX = cap) by (unfold capX; exact UCAP).
      assert (Hroom : size + n < cap).
      { pose proof (CELL _ Yg) as G0. cbn [kentry_ok] in G0. change (edenot E' (EAlu ALU_SLTU (ROOM s0) e_n)) with (alu64 ALU_SLTU (edenot E' (ROOM s0)) (edenot E' e_n)) in G0.
        rewrite u_sltu64, UR in G0. unfold e_n in G0. cbn [edenot] in G0. rewrite F35 in G0. destruct (Z.ltb_spec (2 * k - size - 1) n); lia. }
      unfold Cred in HC1. rewrite Hpre in HC1. subst cr1. rewrite EpX, EcX in *.
      apply (Hcont fx' R' M' m1 LB cr (lb_remove p LB) [(o, 24)] HFP); [| exact HRP | exact HP | exact Hbv1 | exact (CH2.heap_own_back L HI HIok LB cr M' _ p cap HH2 HinLB Hnd)].
      split; [|reflexivity]. left. split; [|auto]. split; [apply STR; rewrite Hk; rewrite Z.even_mul; reflexivity|]. split; [exact Hc8 | rewrite LEN; exact Hroom].
    +
      apply andb_prop in Y as [Y Yv]. apply andb_prop in Y as [Ya Yd].
      destruct (ARM E' M' (SR.ps_cells ps) ce HagE' (CC.lf_cells _ _ _ _ _ _ _ HLF) Ya) as [Hcap Hgrow]. fold capX in Hcap.
      assert (Hlor : capX = 8 * (Z.max (size + n) (2 * (cap - 1)) / 8) + 8) by (rewrite Hcap; unfold PML.grow_cap; rewrite CL5.lor7 by lia; lia).
      assert (Hcr : cr1 = debit L cr capX).
      { unfold Cred in HC1. rewrite Hpre in HC1. rewrite HC1. f_equal. rewrite GK.den_hd, HBL. cbn [hd snd]. unfold capX. f_equal.
        apply (SR.edenot_agree_AP (CC.cp_nx c) E E' ce Hag). unfold CH2.blocks_vars_lt in Y8. cbn [forallb fst snd] in Y8. apply andb_prop in Y8 as [Y8 _]. apply andb_prop in Y8 as [_ Y8]. exact Y8. }
      subst cr1.
      assert (Hdisj : pX + capX <= p \/ p + cap <= pX).
      { pose proof (CELL _ Yd) as G0. cbn [kentry_ok] in G0. unfold estart, elenZ in G0. cbn [a_base a_off] in G0. fold pX capX in G0.
        rewrite UCAP in G0. unfold e_p in G0. cbn [edenot] in G0. rewrite F34 in G0. lia. }
      apply (Hcont fx' R' M' m1 ((pX, capX) :: lb_remove p LB) (debit L cr capX) (lb_remove p LB) [(o, 24)] HFP); [| exact HRP | exact HP | exact Hbv1 | exact HH2].
      split; [|reflexivity]. right. exists pX. cbv zeta. rewrite LEN, <- Hcap. split; [lia|].
      split; [split; [apply STR; rewrite Hlor; rewrite Z.even_add, Z.even_mul; reflexivity|]; split; [rewrite Hlor; rewrite Z.add_comm, Z.mul_comm, Z.mod_add by lia; reflexivity|]|].
      { rewrite ?LEN, Hlor. apply grow_room; clear - H24 Hn1 Hlen Hslt; lia. }
      split; [|auto]. split; [repeat split; assumption|]. split; [|exact Qdef].
      intros b0 Hb0. destruct (Z.eq_dec (fst b0) p) as [e0|ne0].
      * rewrite (CH2.nodup_fst_eq LB b0 (p, cap) Hnd Hb0 HinLB e0). cbn [fst snd]. exact Hdisj.
      * destruct b0 as [bb bm]. exact (Qap (bb, bm) (L5C.in_lb_remove_neq p bb bm LB Hb0 ne0)).
  - exact H_cp0.
  -
    rewrite LS.
    assert (Hdo : L5.defined M o 24).
    { apply GK.defined_3x8; [exact (GK.defined_of_u64 M o _ Hw0 ltac:(unfold GK.HULL_HI; lia) ltac:(lia)) | exact (GK.defined_of_u64 M (o + 8) _ Hw8 ltac:(unfold GK.HULL_HI; lia) ltac:(lia))
                            | exact (GK.defined_of_u64 M (o + 16) _ Hw16 ltac:(unfold GK.HULL_HI; lia) ltac:(lia))]. }
    assert (Hdq : L5.defined M q n) by exact Hdef.
    assert (Hdp : L5.defined M p cap) by exact Pdef.
    assert (Hds : L5.defined M (sp - 8400) 8400) by (intros i Hi; replace (sp - 8400 + i) with (sp - (256 + (16 + 8224)) + (i + 96)) by lia; apply S5; lia).
    assert (W0 : edenot E0 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 32)) (ELit 1)) = Z_to_bv 64 (cap + 1)).
    { rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]. }
    unfold kn_chk in H_kn. apply andb_prop in H_kn as [HKN HRG]. apply exprs_eqb_eq in HRG.
    split.
    { rewrite HRG. apply (regs_ok_pin E0 sr_id R 12%bv); [exact (regs_ok_id R _ _)|]. rewrite Ha2.
      rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. symmetry. rewrite u_eadd. unfold e_q, e_n. cbn [edenot]. rewrite U11, U35. apply Z.mod_small. lia. }
    assert (COM : Forall (kentry_ok GK.RSEGS E0 M) (COMMON s0)).
    { unfold COMMON, e_size, SP, SCRT, CAP, e_o, e_p, e_q, e_n, e_k. rewrite !Forall_app. split; [|split].
      - repeat (apply Forall_cons); [.. | apply Forall_nil].
        + eapply CL5.kword64_intro with (A := o) (z := cap + 1); [ev_start | lia | lia | exact W0 | exact Hw0].
        + eapply CL5.kword64_intro with (A := o + 8) (z := size); [ev_start | lia | lia | destruct s0; [rewrite Hsz; reflexivity | exact V33] | exact Hw8].
        + eapply CL5.kword64_intro with (A := o + 16) (z := p); [ev_start | lia | lia | exact V34 | exact Hw16].
        + e_range.
      - destruct s0; [apply Forall_nil|]. repeat (apply Forall_cons); [.. | apply Forall_nil].
        + e_range. + e_range. + e_range.
        + eapply CL5.kblob_intro with (bs := s) (A := p); [ev_start | unfold elenZ; cbn [edenot]; exact U33 | lia | fold size; lia | lia | reflexivity | exact Hbs | fold size; ev_def].
      - repeat (apply Forall_cons); [.. | apply Forall_nil].
        + e_unk. + e_wr. + e_range. + e_align P2.
        + e_unk. + e_wr. + e_range. + e_align O3.
        + eapply CL5.kblob_intro with (bs := src) (A := q); [ev_start | unfold elenZ; cbn [edenot]; exact U35 | lia | fold n; lia | lia | reflexivity | exact Hbytes | fold n; ev_def].
        + e_unk. + e_range. + e_range.
        + e_unk. + e_wr. + e_range. + e_align S1.
        + e_disj. + e_disj. + e_disj. + e_disj. + e_disj. + e_disj. }
    assert (POS : Forall (kentry_ok GK.RSEGS E0 M) (POSX s0 below)).
    { assert (UPS : bv_unsigned (edenot E0 (PS1 s0)) = size + p + 1).
      { unfold PS1, e_size, e_p. destruct s0; (apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]). }
      assert (SL : forall x y va vb (bit : bool), bv_unsigned (edenot E0 x) = va -> bv_unsigned (edenot E0 y) = vb -> (if bit then va < vb else vb <= va) ->
                   kentry_ok GK.RSEGS E0 M (KRange (EAlu ALU_SLTU x y) (if bit then 1 else 0) (if bit then 1 else 0))).
      { intros x y va vb bit Hxv Hyv Hcmp. cbn [kentry_ok]. change (edenot E0 (EAlu ALU_SLTU x y)) with (alu64 ALU_SLTU (edenot E0 x) (edenot E0 y)).
        rewrite u_sltu64, Hxv, Hyv. clear - Hcmp. destruct bit; destruct (Z.ltb_spec va vb); lia. }
      unfold POSX. rewrite Forall_app. split.
      - unfold e_size, CAP, e_p, e_q, e_n, e_k. destruct below.
        + repeat (apply Forall_cons); [.. | apply Forall_nil]. e_range.
        + destruct s0; (repeat (apply Forall_cons); [e_range | e_range | apply Forall_nil]).
      - destruct below; (repeat (apply Forall_cons); [.. | apply Forall_nil]).
        + apply (SL e_q e_p q p true U11 U34). lia.
        + apply (SL e_q (PS1 s0) q (size + p + 1) true U11 UPS). lia.
        + apply (SL e_q e_p q p false U11 U34). lia.
        + apply (SL e_q (PS1 s0) q (size + p + 1) false U11 UPS). lia. }
    unfold know_ok. apply Forall_forall. intros K0 HK0. rewrite forallb_forall in HKN. pose proof (GK.has_In _ _ (HKN K0 HK0)) as HIN.
    apply in_app_or in HIN as [HIN|HIN]; [exact (proj1 (Forall_forall _ _) COM K0 HIN) | exact (proj1 (Forall_forall _ _) POS K0 HIN)].
  -
    split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr. split; [|reflexivity]. unfold CH2.cur. rewrite H_BL0.
    replace (CH2.den E0 [(e_p, CAP)]) with [(p, cap)]; [exact HH'|].
    unfold CH2.den, e_p, CAP, e_k. cbn [map fst snd].
    f_equal. f_equal; [cbn [edenot]; symmetry; exact U34 | symmetry; apply CL5.u_lin; [lin_eval; rewrite U32; lia | lia]].
  - exact Hfp.
Qed.
End Gen.

Module B0 := Cut_append_range_b0_csrc_u.  Module B1 := Cut_append_range_b1_csrc_u.  Module A0 := Cut_append_range_a0_csrc_u.  Module A1 := Cut_append_range_a1_csrc_u.
Module Z0 := Cut_append_range_zero_csrc_u.  Module Z0T := Cut_append_range_zero_csrc_T_u.
Notation NOGOTO := (fun _ _ _ _ t => match t with CC.TGoto _ _ => false | CC.TOther _ => true end).
Lemma leaf_b0 : CH2.leaves_all B0.CPS B0.TAGS (leaf_facts_chk true B0.BLS B0.CPS B0.RETS) = true.  Proof. vmc_refl. Qed.
Lemma leaf_b1 : CH2.leaves_all B1.CPS B1.TAGS (leaf_facts_chk false B1.BLS B1.CPS B1.RETS) = true.  Proof. vmc_refl. Qed.
Lemma leaf_a0 : CH2.leaves_all A0.CPS A0.TAGS (leaf_facts_chk true A0.BLS A0.CPS A0.RETS) = true.  Proof. vmc_refl. Qed.
Lemma leaf_a1 : CH2.leaves_all A1.CPS A1.TAGS (leaf_facts_chk false A1.BLS A1.CPS A1.RETS) = true.  Proof. vmc_refl. Qed.
Lemma kn_b0 : kn_chk true true B0.cp0 = true.  Proof. vmc_refl. Qed.
Lemma kn_b1 : kn_chk false true B1.cp0 = true.  Proof. vmc_refl. Qed.
Lemma kn_a0 : kn_chk true false A0.cp0 = true.  Proof. vmc_refl. Qed.
Lemma kn_a1 : kn_chk false false A1.cp0 = true.  Proof. vmc_refl. Qed.
Lemma heap_b0 : CH2.heap_chk NFV B0.HDECL B0.BLS B0.CPS GK.HULL_LO GK.HULL_HI B0.TAGS B0.RETS MALLOC FREE [MEMMOVE] = true.  Proof. vmc_refl. Qed.
Lemma heap_b1 : CH2.heap_chk NFV B1.HDECL B1.BLS B1.CPS GK.HULL_LO GK.HULL_HI B1.TAGS B1.RETS MALLOC FREE [MEMMOVE] = true.  Proof. vmc_refl. Qed.
Lemma heap_a0 : CH2.heap_chk NFV A0.HDECL A0.BLS A0.CPS GK.HULL_LO GK.HULL_HI A0.TAGS A0.RETS MALLOC FREE [MEMMOVE] = true.  Proof. vmc_refl. Qed.
Lemma heap_a1 : CH2.heap_chk NFV A1.HDECL A1.BLS A1.CPS GK.HULL_LO GK.HULL_HI A1.TAGS A1.RETS MALLOC FREE [MEMMOVE] = true.  Proof. vmc_refl. Qed.
Lemma ng_b0 : CH2.leaves_all B0.CPS B0.TAGS NOGOTO = true.  Proof. vmc_refl. Qed.
Lemma ng_b1 : CH2.leaves_all B1.CPS B1.TAGS NOGOTO = true.  Proof. vmc_refl. Qed.
Lemma ng_a0 : CH2.leaves_all A0.CPS A0.TAGS NOGOTO = true.  Proof. vmc_refl. Qed.
Lemma ng_a1 : CH2.leaves_all A1.CPS A1.TAGS NOGOTO = true.  Proof. vmc_refl. Qed.

Lemma heap_z : CH2.heap_chk Z0T.NF Z0.HDECL Z0.BLS Z0.CPS GK.HULL_LO GK.HULL_HI Z0.TAGS Z0.RETS MALLOC FREE [] = true.
Proof. vmc_refl. Qed.
Lemma exit_z : CH2.leaves_all Z0.CPS Z0.TAGS (fun _ c _ ps t => match t with CC.TGoto _ _ => false | CC.TOther pc =>
   (negb (CH2.is_call MALLOC FREE [] pc) && CL.ps_at ps [RET] && CL.ps_keeps ps CSAVED && Nat.leb Z0T.NF (CC.cp_nx c))%bool end) = true.
Proof. vmc_refl. Qed.

Section Final.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps GK.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom GK.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom GK.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Definition ok_b0 := gen_ok L HI HIok LAY FPM true true B0.HDECL B0.BLS B0.CPS B0.TAGS B0.RETS B0.cp0 eq_refl eq_refl eq_refl eq_refl kn_b0 B0.plans B0.tags_ok heap_b0 ng_b0 leaf_b0.
Definition ok_b1 := gen_ok L HI HIok LAY FPM false true B1.HDECL B1.BLS B1.CPS B1.TAGS B1.RETS B1.cp0 eq_refl eq_refl eq_refl eq_refl kn_b1 B1.plans B1.tags_ok heap_b1 ng_b1 leaf_b1.
Definition ok_a0 := gen_ok L HI HIok LAY FPM true false A0.HDECL A0.BLS A0.CPS A0.TAGS A0.RETS A0.cp0 eq_refl eq_refl eq_refl eq_refl kn_a0 A0.plans A0.tags_ok heap_a0 ng_a0 leaf_a0.
Definition ok_a1 := gen_ok L HI HIok LAY FPM false false A1.HDECL A1.BLS A1.CPS A1.TAGS A1.RETS A1.cp0 eq_refl eq_refl eq_refl eq_refl kn_a1 A1.plans A1.tags_ok heap_a1 ng_a1 leaf_a1.

Lemma zero_ok : forall (LB : list (Z * Z)) (cr : credit) (o cap p q sp r : Z) (s : list Z),
  PML.cps_heap L HI PML.PC_APPEND_RANGE r sp PMS.STR_SCR LB cr
      (fun R M => 24 <= cap /\ PML.entry L R M sp r PMS.STR_SCR /\ PML.a0 R o /\ PML.a1 R q /\ PML.a2 R q /\ 0 <= q < 2 ^ 47 /\
                  PML.str_at M o (PML.SLong cap p s) /\ In (p, cap) LB /\ PML.obj_on_stack L sp o 24 /\ Z.of_nat (length s) < 2 ^ 26)
      (fun R M R' M' LB' cr' LBk W => PMS.str_grown L LB cr M' o cap p s LB' cr' LBk /\ W = [(o, 24)]).
Proof.
  intros LB cr o cap p q sp r s. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (H24 & Hentry & Ha0 & Ha1 & Ha2 & Hq & Hstr & HinLB & Hobj & Hlen) Hcont.
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (S1 & S2 & S3 & S4 & S5).
  unfold PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK in *.
  pose proof Hstr as ((Hbit & Hw0 & Hw8 & Hw16 & Hbs & Hnul) & Hc8 & Hslt).
  destruct Hobj as (O1 & O2 & O3). set (size := Z.of_nat (length s)) in *.
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_stack L LAY) as LSTK. unfold PML.HEAP_STACK in LSTK.
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & _).
  destruct (Hwf _ HinLB) as ((P0 & P1 & P2 & P3 & P4) & Pdef & Pap). cbn [fst snd] in *.
  set (k := cap / 2). assert (Hk : cap = 2 * k) by (unfold k; assert (cap mod 2 = 0) by (rewrite <- (Z.mod_mod_divide cap 8 2) by (exists 4; reflexivity); rewrite Hc8; reflexivity); rewrite (Z.div_mod cap 2) at 1 by lia; lia).
  set (E0 := E0_of R k size p 0 s []).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 q) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V33 : ev E0 33 = Z_to_bv 64 size) by reflexivity.
  assert (V34 : ev E0 34 = Z_to_bv 64 p) by reflexivity.
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by lia.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; lia).
  assert (U11 : bv_unsigned (ev E0 11) = q) by (rewrite V11; apply u64_of_Z; lia).
  assert (U32 : bv_unsigned (ev E0 32) = k) by (change (ev E0 32) with (Z_to_bv 64 k); apply u64_of_Z; lia).
  assert (U33 : bv_unsigned (ev E0 33) = size) by (rewrite V33; apply u64_of_Z; lia).
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= 0x7fff7f800000) by (rewrite ILO, IHI; lia).
  assert (LYE : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L) by (rewrite ILO, IHI, (PmLayout.ly_errno L LAY); lia).
  assert (STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr Z0.HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
    by (change (CH.hd_scr Z0.HDECL) with SCRT; unfold SCRT; repeat split; lia).
  assert (SCRP : 0 <= CH.hd_scr Z0.HDECL) by (change (CH.hd_scr Z0.HDECL) with SCRT; unfold SCRT; lia).
  assert (NF32 : (32 <= Z0T.NF)%nat) by (unfold Z0T.NF; lia).
  assert (W_OK : forall (w : L5.range) (a : Z), In w [] -> L5.in_rng w a -> CH2.wclient L sp a) by (intros w a []).
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs Z0.HDECL) -> SGP.region_vars_lt Z0T.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w [] /\ L5.in_rng w a)) by (intros rg []).
  unfold PML.cfg. change PML.PC_APPEND_RANGE with (CC.cp_pc Z0.cp0). rewrite <- LS.
  eapply CH2.heap_cert_sound with (NF := Z0T.NF) (E0 := E0) (M0 := M) (model0 := model) (LBrest := LB) (sp0 := sp) (d := Z0.HDECL)
    (W := []) (BLS := Z0.BLS) (Cred := fun _ _ cr' => cr' = cr) (CPS := Z0.CPS) (TAGS := Z0.TAGS) (RETS := Z0.RETS) (MALLOC := MALLOC) (FREE := FREE)
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
  -   intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CH2.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by lia. split; [lia|]. left. lia.
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
  - intros i c kk ps j sg IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ exit_z _ _ _ _ _ IL) as X. discriminate X.
  - intros i c kk ps j cj IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ exit_z _ _ _ _ _ IL) as X. cbv beta iota in X. apply andb_prop in X as [X _]. apply andb_prop in X as [X _]. apply andb_prop in X as [X _]. discriminate X.
  - intros i c kk ps pc j cj IL Hcall. exfalso. pose proof (CH2.leaves_all_sound _ _ _ exit_z _ _ _ _ _ IL) as X. cbv beta iota in X. rewrite Hcall in X. discriminate X.
  -
    intros i c kk ps pc IL Hnc fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF _.
    pose proof (CH2.leaves_all_sound _ _ _ exit_z _ _ _ _ _ IL) as X. cbv beta iota in X. rewrite Hnc in X. cbn [negb andb] in X.
    apply andb_prop in X as [X Xnf]. apply andb_prop in X as [Xpc Xk]. apply CL.ps_at_sound in Xpc. destruct Xpc as [Xpc|[]]. apply Nat.leb_le in Xnf.
    pose proof (CH2.exit_amb L HI HIok LYI LYE (PmLayout.ly_ro L LAY) Z0T.NF E0 M model LB sp Z0.HDECL [] Z0.BLS (fun _ _ cr' => cr' = cr) STKF SCRP NF32 U2 W_OK WRS_OK
                  Z0.CPS GK.HULL_LO GK.HULL_HI Z0.TAGS Z0.RETS MALLOC FREE [] heap_z i c kk ps pc IL Hnc E E' R1 R' M1 M' m1 HAt HAmb Hag HLF) as HA'.
    pose proof HA' as HA2. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr1 & Hdf1). subst cr1.
    assert (HagE' : env_agree Z0T.NF E0 E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | exact Xnf]]).
    rewrite LS in HLF.
    assert (KEEP : forall y : reg, In (ridx y) CSAVED -> getr R' y = getr R y).
    { intros y Hy. rewrite (CL.ps_keeps_sound GK.RSEGS c ps E0 E' R' M1 M' CSAVED Z0T.NF y HLF Xk HagE' Hy (csaved_lt y Hy)). exact (EV y). }
    assert (HRP : regs_preserved R R') by (intros y Hy; apply KEEP; exact (CL5.csaved_in y Hy)).
    assert (Hra' : getr R' 1%bv = Z_to_bv 64 r) by (rewrite (KEEP 1%bv ltac:(left; reflexivity)); exact Hra).
    assert (Hds : L5.defined M (sp - CH.hd_scr Z0.HDECL) (CH.hd_scr Z0.HDECL)).
    { change (CH.hd_scr Z0.HDECL) with SCRT. unfold SCRT. intros j Hj. replace (sp - 8400 + j) with (sp - (256 + (16 + 8224)) + (j + 96)) by lia. apply S5. lia. }
    pose proof (CH2.amb_hpres L HI LYI LYE Z0T.NF E0 M model LB sp Z0.HDECL [] Z0.BLS (fun _ _ cr' => cr' = cr) STKF NF32 i E M' m1 HA2 Hds) as HP0.
    change (CH.hd_scr Z0.HDECL) with SCRT in HP0. unfold SCRT in HP0.

    assert (AG : forall a m, (sp <= a /\ a + m <= hl_sptop L) \/ (p <= a /\ a + m <= p + cap) -> L5C.agree_on M M' a m).
    { intros a m Hr. apply (L5C.frame_agree L LB sp 8400 [] M M' a m HP0). intros j Hj. destruct Hr as [Hr|Hr].
      - apply L5C.kept_stack; [lia | lia | lia | rewrite (PmLayout.ly_errno L LAY); lia | lia | apply L5C.outside_nil].
      - apply (L5C.kept_block L LB sp 8400 [] p cap j HinLB); [lia | lia | lia | rewrite (PmLayout.ly_errno L LAY); lia | apply L5C.outside_nil]. }
    assert (Hstr' : PML.str_at M' o (PML.SLong cap p s)).
    { split; [|split; assumption]. unfold L5.lstr_long. split; [exact Hbit|].
      split; [apply (L5C.u64_at_agree GK.RSEGS M M' o _ (AG o 8 ltac:(lia))); [lia | lia | exact Hw0]|].
      split; [apply (L5C.u64_at_agree GK.RSEGS M M' (o + 8) _ (AG (o + 8) 8 ltac:(lia))); [lia | lia | exact Hw8]|].
      split; [apply (L5C.u64_at_agree GK.RSEGS M M' (o + 16) _ (AG (o + 16) 8 ltac:(lia))); [lia | lia | exact Hw16]|].
      split; [apply (L5C.bytes_at_agree GK.RSEGS M M' p s (AG p size ltac:(lia))); [lia | fold size; lia | exact Hbs]|].
      apply (L5C.u8_at_agree GK.RSEGS M M' _ _ (AG (p + size) 1 ltac:(lia))); [lia | lia | exact Hnul]. }
    assert (HP : L5C.hpres L (lb_remove p LB) sp (256 + (16 + 8224)) [(o, 24)] M M').
    { apply L5C.hpres_intro.
      - intros a (K1 & K2 & K3 & K4). apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP0). split; [exact K1|]. split; [|split; [exact K3 | apply L5C.outside_nil]].
        destruct K2 as [(b0 & Hb0 & Hr0)|[[C1 C2]|C]]; [left; exists b0; split; [exact (L5C.in_lb_remove p b0 LB Hb0) | exact Hr0] | right; left; split; [exact C1 | lia] | right; right; exact C].
      - intros j Hj. apply (Hdf1 (sp - (256 + (16 + 8224)) + j)); [lia | | apply S5; lia].
        split; [right; left; split; lia | unfold in_errno; rewrite (PmLayout.ly_errno L LAY); lia].
      - intros a Ha HC HE Hd. apply (L5C.hpres_cdef _ _ _ _ _ _ _ a HP0 Ha); [|exact HE | exact Hd].
        destruct HC as [(b0 & Hb0 & Hr0)|[[C1 C2]|C]]; [left; exists b0; split; [exact (L5C.in_lb_remove p b0 LB Hb0) | exact Hr0] | right; left; split; [exact C1 | lia] | right; right; exact C]. }
    rewrite <- Xpc, LS. eapply CL.ret_cps; [exact ret_at | exact (proj1 Hmo1) | exact (proj1 (proj2 Hmo1)) | |].
    { rewrite Hra'. apply Hoare.ret_ok_even. destruct Hraok as [R1' R2']. rewrite u64_of_Z by lia. exact R2'. }
    rewrite Hra'.
    assert (HBL : nth i Z0.BLS [] = []) by (destruct i as [|[|]]; reflexivity). unfold CH2.cur in HH1. rewrite HBL in HH1.
    apply (Hcont fx' R' M' m1 LB cr (lb_remove p LB) [(o, 24)] HFP); [| exact HRP | exact HP | exact Hbv1 | exact HH1].
    split; [|reflexivity]. left. auto.
  - reflexivity.
  -
    rewrite LS.
    assert (Hdo : L5.defined M o 24).
    { apply GK.defined_3x8; [exact (GK.defined_of_u64 M o _ Hw0 ltac:(unfold GK.HULL_HI; lia) ltac:(lia)) | exact (GK.defined_of_u64 M (o + 8) _ Hw8 ltac:(unfold GK.HULL_HI; lia) ltac:(lia))
                            | exact (GK.defined_of_u64 M (o + 16) _ Hw16 ltac:(unfold GK.HULL_HI; lia) ltac:(lia))]. }
    assert (Hds : L5.defined M (sp - 8400) 8400) by (intros i Hi; replace (sp - 8400 + i) with (sp - (256 + (16 + 8224)) + (i + 96)) by lia; apply S5; lia).
    assert (W0 : edenot E0 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 32)) (ELit 1)) = Z_to_bv 64 (cap + 1)).
    { rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]. }
    split.
    { change (CC.cp_regs Z0.cp0) with (sr_upd sr_id 12 (EVar 11)). apply (regs_ok_pin E0 sr_id R 12%bv); [exact (regs_ok_id R _ _)|]. rewrite Ha2. cbn [edenot]. symmetry. exact V11. }
    unfold know_ok, Z0.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply CL5.kword64_intro with (A := o) (z := cap + 1); [ev_start | lia | lia | exact W0 | exact Hw0].
    + eapply CL5.kword64_intro with (A := o + 8) (z := size); [ev_start | lia | lia | exact V33 | exact Hw8].
    + eapply CL5.kword64_intro with (A := o + 16) (z := p); [ev_start | lia | lia | exact V34 | exact Hw16].
    + e_range.
    + e_unk. + e_range. + e_align O3. + e_range.
    + e_unk. + e_wr. + e_range. + e_align S1.
    + e_disj.
  -
    split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr. split; [|reflexivity]. exact HH.
  - exact Hfp.
Qed.

Theorem str_append_range_ok : PMS.str_append_range_spec L HI.
Proof.
  intros LB cr o cap p q sp r s src. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & Ha0 & Ha1 & Ha2 & Hstr & H24 & HinLB & Hobj & Hbytes & Hdef & Hsrc & Hlen & Hcredit) Hcont.
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & _).
  destruct (Hwf _ HinLB) as ((P0 & P1 & P2 & P3 & P4) & Pdef & Pap). cbn [fst snd] in *.
  pose proof Hsrc as (b & Hb & Hbp & Hbq1 & Hbq2).
  destruct (Hwf _ Hb) as ((B0' & B1' & B2' & B3' & B4') & _ & _).
  assert (HinRest : In b (lb_remove p LB)) by (destruct b as [bb bm]; exact (L5C.in_lb_remove_neq p bb bm LB Hb Hbp)).
  pose proof (Pap b HinRest) as Hapart.
  destruct src as [|c0 src'].
  -
    cbn [length Z.of_nat] in *. rewrite Z.add_0_r in *.
    apply (zero_ok LB cr o cap p q sp r s fx R M model K HH Hmo HKnil Hfp).
    { split; [exact H24|]. repeat (split; [assumption|]). split; [pose proof (PmLayout.ly_img_lo L LAY); destruct Hentry as (_ & _ & _ & _ & (_ & _ & _ & ? & _)); lia|]. repeat (split; [assumption|]). lia. }
    intros fx' R' M' model' LB' cr' LBk W HFP (Hpost & HW) HRP HP Hbv HH2.
    apply (Hcont fx' R' M' model' LB' cr' LBk W HFP); [|assumption..]. split; [|exact HW]. rewrite app_nil_r. exact Hpost.
  - set (src := c0 :: src') in *. assert (Hne : src <> []) by discriminate.
    assert (POSD : q + Z.of_nat (length src) <= p \/ p + cap <= q) by (destruct Hapart; [right | left]; lia).
    destruct s as [|c1 s'].
    + destruct POSD as [Hp|Hp].
      * apply (ok_b0 LB cr o cap p q sp r [] src fx R M model K HH Hmo HKnil Hfp); [|exact Hcont].
        split; [repeat split; assumption|]. repeat (split; [assumption|]). assumption.
      * apply (ok_a0 LB cr o cap p q sp r [] src fx R M model K HH Hmo HKnil Hfp); [|exact Hcont].
        split; [repeat split; assumption|]. repeat (split; [assumption|]). assumption.
    + assert (Hsne : c1 :: s' <> []) by discriminate. destruct POSD as [Hp|Hp].
      * apply (ok_b1 LB cr o cap p q sp r (c1 :: s') src fx R M model K HH Hmo HKnil Hfp); [|exact Hcont].
        split; [repeat split; assumption|]. repeat (split; [assumption|]). assumption.
      * apply (ok_a1 LB cr o cap p q sp r (c1 :: s') src fx R M model K HH Hmo HKnil Hfp); [|exact Hcont].
        split; [repeat split; assumption|]. repeat (split; [assumption|]). assumption.
Qed.
End Final.
End AR.
