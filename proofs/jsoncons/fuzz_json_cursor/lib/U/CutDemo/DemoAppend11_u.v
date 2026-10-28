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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_append_csrc_T_u Cut_append_csrc_u Cut_append0_csrc_T_u Cut_append0_csrc_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutDemo Require Pm10Memmove_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := Cut_append_csrc_u.
Module GT := Cut_append_csrc_T_u.
Module Z0 := Cut_append0_csrc_u.
Module Z0T := Cut_append0_csrc_T_u.
Definition MALLOC : Z := 0xa9144.  Definition FREE : Z := 0xa9004.  Definition MEMMOVE : Z := 0xb7c98.

Lemma heap_ok : CH2.heap_chk GT.NF G.HDECL G.BLS G.CPS 0x10000 0xf8000 G.TAGS G.RETS MALLOC FREE [MEMMOVE] = true.
Proof. vmc_refl. Qed.

Lemma heap_ok0 : CH2.heap_chk Z0T.NF Z0.HDECL Z0.BLS Z0.CPS 0x10000 0xf8000 Z0.TAGS Z0.RETS 0xa9144 0xa9004 [] = true.
Proof. vmc_refl. Qed.
Lemma exit_ok0 : CH2.leaves_all Z0.CPS Z0.TAGS (fun _ c _ ps t => match t with CC.TGoto _ _ => false | CC.TOther pc =>
   (negb (CH2.is_call 0xa9144 0xa9004 [] pc) && CL.ps_at ps [0x64150] && CL.ps_keeps ps [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat && Nat.leb Z0T.NF (CC.cp_nx c))%bool end) = true.
Proof. vmc_refl. Qed.

Lemma no_goto : CH2.leaves_all G.CPS G.TAGS (fun _ _ _ _ t => match t with CC.TGoto _ _ => false | CC.TOther _ => true end) = true.
Proof. vmc_refl. Qed.

Definition pre (i : nat) : bool := (Nat.eqb i 0 || Nat.eqb i 3)%bool.
Definition hd_base (i : nat) : expr := fst (hd (ELit 0, ELit 0) (nth i G.BLS [])).
Definition hd_size (i : nat) : expr := snd (hd (ELit 0, ELit 0) (nth i G.BLS [])).
Definition e_n := EVar 12.  Definition e_size := EVar 33.  Definition e_k := EVar 32.
Definition NEED : expr := EAlu ALU_ADD e_n e_size.
Definition CAP2 : expr := EAlu ALU_ADD (EMd M_MUL (ELit 4) e_k) (ELit (-2)).
Definition ROOM : expr := EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 2) e_k) (EMd M_MUL (ELit (-1)) e_size)) (ELit (-1)).
Definition round8 (x : expr) (c : Z) : expr := EAlu ALU_ADD (EMd M_MUL (ELit 8) (EAlu ALU_SRL x (ELit 3))) (ELit c).
Definition has (cells : list kentry) (X : kentry) : bool := existsb (APC.kentry_eqb X) cells.
Definition arm_chk (cells : list kentry) (e : expr) : bool :=
  (has cells (KRange (EAlu ALU_SLTU ROOM e_n) 1 1)
   && ((expr_eqb e (round8 NEED 8) && has cells (KRange (EAlu ALU_SLTU CAP2 NEED) 1 1))
       || (expr_eqb e (round8 CAP2 8) && has cells (KRange (EAlu ALU_SLTU CAP2 NEED) 0 0))))%bool.
Definition CSAVED : list nat := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition exit_chk (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in let pe := hd_base i in let ce := hd_size i in
  (CL.ps_at ps [0x64150] && CL.ps_keeps ps CSAVED && CH2.blocks_vars_lt (CC.cp_nx c) (nth i G.BLS []) && Nat.leb GT.NF (CC.cp_nx c)
   && has cells (KWord (SA (EVar 10) 0) 8 (APC.eaddz ce 1)) && has cells (KWord (SA (EVar 10) 8) 8 NEED) && has cells (KWord (SA (EVar 10) 16) 8 pe)
   && (has cells (KBlob (SA pe 0) e_size 0) || has cells (KRange e_size 0 0))
   && has cells (KBlob (SA (EAlu ALU_ADD e_size pe) 0) e_n 1)
   && has cells (KWord (SA (EAlu ALU_ADD e_n (EAlu ALU_ADD e_size pe)) 0) 1 (ELit 0))
   && match nth i G.BLS [] with [_] => true | _ => false end
   && (if pre i then (expr_eqb pe (EVar 34) && expr_eqb ce (EMd M_MUL (ELit 2) e_k) && has cells (KRange (EAlu ALU_SLTU ROOM e_n) 0 0))
       else (arm_chk cells ce && has cells (KDisj (SA pe 0) ce (SA (EVar 34) 0) (EMd M_MUL (ELit 2) e_k))
             && match pe with EVar v => Nat.leb GT.NF v | _ => false end)))%bool.
Definition leaf_facts_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      if CH2.is_call MALLOC FREE [MEMMOVE] pc then
        match CH2.ret_of G.RETS i k with
        | Some j =>
            match nth_error G.CPS j with
            | Some cj =>
                (Nat.leb GT.NF (CC.cp_nx c) && Nat.leb (CC.cp_nx c) (CC.cp_nx cj - APC.NCS)
                 && if Z.eqb pc MALLOC then (pre i && negb (pre j) && expr_eqb (hd_size j) (CA.ps_reg ps 10) && APC.expr_vars_lt GT.NF (hd_size j) && arm_chk (SR.ps_cells ps) (hd_size j))
                    else (Bool.eqb (pre i) (pre j) && (pre i || (expr_eqb (hd_size i) (hd_size j) && APC.expr_vars_lt GT.NF (hd_size i)))))%bool
            | None => false
            end
        | None => false
        end
      else exit_chk i c ps
  end.
Lemma leaf_facts_ok : CH2.leaves_all G.CPS G.TAGS leaf_facts_chk = true.
Proof. vmc_refl. Qed.

Lemma ev_reg : forall R rest ebs (x : reg), ev (Env (reg_ev R rest) ebs) (ridx x) = getr R x.
Proof.
  intros R rest ebs x. cbn [ev]. unfold reg_ev.
  assert (H : (ridx x < 32)%nat) by (unfold ridx; pose proof (bv_unsigned_in_range _ x) as B; change (bv_modulus 5) with 32 in B; lia).
  apply Nat.ltb_lt in H. rewrite H. rewrite CC.reg_of_ridx. reflexivity.
Qed.

Lemma ret_at : CL.is_ret_at RSEGS 0x64150.
Proof. CL.solve_is_ret. Qed.

Lemma csaved_in : forall r : reg, In (bv_unsigned r) callee_saved_idx -> In (ridx r) CSAVED.
Proof.
  intros r H. unfold ridx. unfold callee_saved_idx in H. cbn [In] in H.
  repeat (destruct H as [H|H]; [rewrite <- H; cbn; tauto|]). destruct H.
Qed.

Lemma den_hd : forall E bl, snd (hd (0, 0) (CH2.den E bl)) = bv_unsigned (edenot E (snd (hd (ELit 0, ELit 0) bl))).
Proof. intros E [|b r]; reflexivity. Qed.

Lemma lor7 : forall x, 0 <= x -> Z.lor x 7 = 8 * (x / 8) + 7.
Proof.
  intros x Hx. pose proof (Z.add_lor_land x 7) as H.
  assert (L : Z.land x 7 = x mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
  rewrite L in H. pose proof (Z.div_mod x 8 ltac:(lia)). lia.
Qed.

Ltac lin_form := unfold lden; repeat (match goal with |- context [lin_of ?e] => let l := fresh "l" in set (l := lin_of e); vm_compute in l; subst l end);
                 cbn [fst snd tden]; unfold uE.
Ltac lin_eval := unfold lden; repeat (match goal with |- context [lin_of ?e] => let l := fresh "l" in set (l := lin_of e); vm_compute in l; subst l end);
                 cbn [fst snd tden]; unfold uE; cbn [edenot].

Ltac rw_atoms := repeat match goal with H : bv_unsigned (ev _ _) = _ |- _ => rewrite H end.
Ltac ev_start := unfold estart; cbn [a_base a_off edenot]; rw_atoms; first [reflexivity | lia].
Ltac ev_len := apply CL5.elen_lin; [lin_eval; rw_atoms; reflexivity | lia].
Ltac ev_def := match goal with H : L5.defined _ _ _ |- _ => eapply (L5.defined_sub _ _ _ _ _ H); lia end.
Ltac e_range := eapply CL5.krange_intro; [lin_eval; rw_atoms; reflexivity | lia | lia].
Ltac e_align H := eapply CL5.kalign_intro; [lin_eval; rw_atoms; reflexivity | lia | lia | rewrite ?Z.add_0_l, ?Z.add_0_r, ?Z.mul_1_l; exact H].
Ltac e_disj := eapply CL5.kdisj_intro; [ev_start | ev_len | ev_start | ev_len | lia].
Ltac e_unk := eapply CL5.kunk_intro; [ev_start | ev_len | lia | lia | lia | ev_def].
Ltac e_wr := eapply CL5.kwr_intro; [ev_start | ev_len | lia | lia | lia | ev_def].

Lemma defined_of_u64 : forall (M : PML.mem) a v, L5.u64_at RSEGS M a v -> 0xf8000 <= a -> a + 8 <= 2 ^ 64 -> L5.defined M a 8.
Proof.
  intros M a v Hu Ha H8 i Hi. unfold L5.u64_at in Hu.
  apply (APS.rdn_bytes_some RSEGS A0 src0_in_hull M (Z_to_bv 64 a) 8 _ Hu).
  - rewrite !u64_of_Z by lia. cbn. lia.
  - rewrite u64_of_Z by lia. unfold APS.in_hull. cbn [APC.img_lo APC.img_hi A0]. apply andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.

Section AppendOk.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Definition SCRT : Z := 8480.

Definition Cred (cr0 : credit) (i : nat) (E : env) (cr : credit) : Prop :=
  cr = if pre i then cr0 else debit L cr0 (snd (hd (0, 0) (CH2.den E (nth i G.BLS [])))).

Lemma append_pos : forall (LB : list (Z * Z)) (cr : credit) (o cap p q sp r : Z) (s src : list Z),
  PML.cps_heap L HI PML.PC_STR_APPEND r sp PMS.STR_SCR LB cr
      (fun R M => (24 <= cap /\ src <> []) /\ PML.entry L R M sp r PMS.STR_SCR /\ PML.a0 R o /\ PML.a1 R q /\ PML.a2 R (Z.of_nat (length src)) /\
                  PML.str_at M o (PML.SLong cap p s) /\ In (p, cap) LB /\ PML.obj_on_stack L sp o 24 /\
                  L5.bytes_at RSEGS M q src /\ L5.defined M q (Z.of_nat (length src)) /\
                  (src = [] \/ exists b, In b LB /\ fst b <> p /\ fst b <= q /\ q + Z.of_nat (length src) <= fst b + snd b) /\
                  Z.of_nat (length s) + Z.of_nat (length src) < 2 ^ 26 /\
                  (cap <= Z.of_nat (length s) + Z.of_nat (length src) -> credit_ok L cr (PML.grow_cap cap (Z.of_nat (length s) + Z.of_nat (length src)))))
      (fun R M R' M' LB' cr' LBk W => PMS.str_grown L LB cr M' o cap p (s ++ src) LB' cr' LBk /\ W = [(o, 24)]).
Proof.
  intros LB cr o cap p q sp r s src. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp ((H24 & Hne) & Hentry & Ha0 & Ha1 & Ha2 & Hstr & HinLB & Hobj & Hbytes & Hdef & Hsrc & Hlen & Hcredit) Hcont.
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (S1 & S2 & S3 & S4 & S5).
  unfold PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK in *.
  destruct Hstr as ((Hbit & Hw0 & Hw8 & Hw16 & Hbs & Hnul) & Hc8 & Hslt).
  destruct Hsrc as [->|(b & Hb & Hbp & Hbq1 & Hbq2)]; [contradiction|].
  destruct Hobj as (O1 & O2 & O3).
  set (n := Z.of_nat (length src)) in *. set (size := Z.of_nat (length s)) in *.
  assert (Hn1 : 1 <= n) by (destruct src; [contradiction | unfold n; cbn [length]; lia]).
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_stack L LAY) as LSTK. unfold PML.HEAP_STACK in LSTK.

  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & _).
  destruct (Hwf _ HinLB) as ((P0 & P1 & P2 & P3 & P4) & Pdef & Pap). cbn [fst snd] in *.
  destruct (Hwf _ Hb) as ((B0 & B1 & B2 & B3 & B4) & Bdef & Bap).
  pose proof (CH2.heap_own_front L HI HIok LB cr M _ p cap HH HinLB) as HH'.
  set (k := cap / 2). assert (Hk : cap = 2 * k) by (unfold k; assert (cap mod 2 = 0) by (rewrite <- (Z.mod_mod_divide cap 8 2) by (exists 4; reflexivity); rewrite Hc8; reflexivity); rewrite (Z.div_mod cap 2) at 1 by lia; lia).
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [k; size; p] 0))) (fun id => nth id [map (Z_to_bv 8) s; map (Z_to_bv 8) src] [])).
  assert (EV : forall x : reg, ev E0 (ridx x) = getr R x) by (intros x; apply ev_reg).
  assert (V1 : ev E0 1 = Z_to_bv 64 r) by (rewrite <- Hra; exact (EV 1%bv)).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V11 : ev E0 11 = Z_to_bv 64 q) by (rewrite <- Ha1; exact (EV 11%bv)).
  assert (V12 : ev E0 12 = Z_to_bv 64 n) by (rewrite <- Ha2; exact (EV 12%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 k) by reflexivity.
  assert (V33 : ev E0 33 = Z_to_bv 64 size) by reflexivity.
  assert (V34 : ev E0 34 = Z_to_bv 64 p) by reflexivity.
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by lia.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; lia).
  assert (U11 : bv_unsigned (ev E0 11) = q) by (rewrite V11; apply u64_of_Z; lia).
  assert (U12 : bv_unsigned (ev E0 12) = n) by (rewrite V12; apply u64_of_Z; lia).
  assert (U32 : bv_unsigned (ev E0 32) = k) by (rewrite V32; apply u64_of_Z; lia).
  assert (U33 : bv_unsigned (ev E0 33) = size) by (rewrite V33; apply u64_of_Z; lia).
  assert (U34 : bv_unsigned (ev E0 34) = p) by (rewrite V34; apply u64_of_Z; lia).
  assert (HinRest : In b (lb_remove p LB)) by (destruct b as [bb bm]; exact (L5C.in_lb_remove_neq p bb bm LB Hb Hbp)).
  pose proof (Pap b HinRest) as Hapart.

  assert (FR : forall E1, env_agree GT.NF E0 E1 ->
            bv_unsigned (ev E1 2) = sp /\ bv_unsigned (ev E1 10) = o /\ bv_unsigned (ev E1 11) = q /\ bv_unsigned (ev E1 12) = n /\
            bv_unsigned (ev E1 32) = k /\ bv_unsigned (ev E1 33) = size /\ bv_unsigned (ev E1 34) = p /\ eb E1 = eb E0).
  { intros E1 [A B]. rewrite <- !A by (unfold GT.NF; lia). repeat split; try assumption. symmetry. exact B. }

  assert (ARM : forall E1 M1 cells e, env_agree GT.NF E0 E1 -> (forall K0, In K0 cells -> kentry_ok RSEGS E1 M1 K0) -> arm_chk cells e = true ->
            bv_unsigned (edenot E1 e) = PML.grow_cap cap (size + n) /\ cap <= size + n).
  { intros E1 M1 cells e Hag1 Hc Harm. destruct (FR E1 Hag1) as (F2 & F10 & F11 & F12 & F32 & F33 & F34 & _).
    unfold arm_chk, round8, NEED, CAP2, ROOM, e_n, e_size, e_k in Harm. apply andb_prop in Harm as [Hg Harm].
    assert (HAS : forall X, has cells X = true -> kentry_ok RSEGS E1 M1 X).
    { intros X HX. apply Hc. unfold has in HX. apply existsb_exists in HX as (Y & HY & He). apply APS.kentry_eqb_eq in He. subst Y. exact HY. }
    assert (UN : bv_unsigned (edenot E1 (EAlu ALU_ADD (EVar 12) (EVar 33))) = n + size) by (apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]).
    assert (UC : bv_unsigned (edenot E1 (EAlu ALU_ADD (EMd M_MUL (ELit 4) (EVar 32)) (ELit (-2)))) = 4 * k - 2) by (apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]).
    assert (UR : bv_unsigned (edenot E1 (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 2) (EVar 32)) (EMd M_MUL (ELit (-1)) (EVar 33))) (ELit (-1)))) = 2 * k - size - 1)
      by (apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]).
    pose proof (HAS _ Hg) as G. cbn [kentry_ok] in G. cbn [edenot] in G. rewrite u_sltu64 in G. cbn [edenot] in UR. rewrite UR, F12 in G.
    destruct (Z.ltb_spec (2 * k - size - 1) n) as [Hgrow|]; [|lia]. split; [|lia].
    unfold PML.grow_cap. replace (size + n) with (n + size) by lia. apply orb_prop in Harm as [Harm|Harm]; apply andb_prop in Harm as [He Hf]; apply expr_eqb_eq in He; subst e;
      pose proof (HAS _ Hf) as G2; cbn [kentry_ok] in G2; cbn [edenot] in G2; rewrite u_sltu64 in G2; cbn [edenot] in UC, UN; rewrite UC, UN in G2.
    - destruct (Z.ltb_spec (4 * k - 2) (n + size)) as [Hlt|]; [|lia].
      rewrite Z.max_l by lia. rewrite lor7 by lia.
      apply CL5.u_lin; [lin_form; rewrite u_srl_lit; cbn [edenot]; rewrite UN; change (2 ^ ((3 mod two64) mod 64)) with 8; lia|].
      pose proof (Z.div_le_upper_bound (n + size) 8 (2 ^ 26) ltac:(lia) ltac:(lia)). pose proof (Z.div_pos (n + size) 8 ltac:(lia) ltac:(lia)). lia.
    - destruct (Z.ltb_spec (4 * k - 2) (n + size)) as [|Hge]; [lia|].
      rewrite Z.max_r by lia. replace (2 * (cap - 1)) with (4 * k - 2) by lia. rewrite lor7 by lia.
      apply CL5.u_lin; [lin_form; rewrite u_srl_lit; cbn [edenot]; rewrite UC; change (2 ^ ((3 mod two64) mod 64)) with 8; lia|].
      pose proof (Z.div_le_upper_bound (4 * k - 2) 8 (2 ^ 26) ltac:(lia) ltac:(lia)). pose proof (Z.div_pos (4 * k - 2) 8 ltac:(lia) ltac:(lia)). lia. }

  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= 0x7fff7f800000) by (rewrite ILO, IHI; lia).
  assert (LYE : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L) by (rewrite ILO, IHI, (PmLayout.ly_errno L LAY); lia).
  assert (STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr G.HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
    by (change (CH.hd_scr G.HDECL) with 8480; repeat split; lia).
  assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (change (CH.hd_scr G.HDECL) with 8480; lia).
  assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  assert (W_OK : forall (w : L5.range) (a : Z), In w [(o, 24)] -> L5.in_rng w a -> CH2.wclient L sp a).
  { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. split; [lia | left; lia]. }
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w [(o, 24)] /\ L5.in_rng w a)).
  { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CH2.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
    rewrite U10 in Ha. rewrite u64_of_Z in Ha by lia. exists (o, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
  unfold PML.cfg. change PML.PC_STR_APPEND with (CC.cp_pc G.cp0). rewrite <- LS.
  eapply CH2.heap_cert_sound with (NF := GT.NF) (E0 := E0) (M0 := M) (model0 := model) (LBrest := lb_remove p LB) (sp0 := sp) (d := G.HDECL)
    (W := [(o, 24)]) (BLS := G.BLS) (Cred := Cred cr) (CPS := G.CPS) (TAGS := G.TAGS) (RETS := G.RETS) (MALLOC := MALLOC) (FREE := FREE)
    (COPIES := [MEMMOVE]) (IMG_LO := 0x10000) (IMG_HI := 0xf8000) (FPI := PML.fp_ok) (i := 0%nat) (E := E0) (HI := HI).
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
    rewrite U11, U12 in Ha. split; [lia|]. right; right. exists b. split; [exact HinRest | lia].
  - exact WRS_OK.
  - intros rg a [].
  - exact HKnil.
  - exact ILO.
  - exact IHI.
  - rewrite LS. exact FPM.
  - rewrite LS. exact G.plans.
  - exact G.tags_ok.
  - exact heap_ok.
  - exact (PmLayout.ly_malloc L LAY).
  - exact (PmLayout.ly_free L LAY).
  - intros pc [<-|[]]. exact (Pm10Memmove_u.memmove_copy1 L LS).
  -   intros i c kk ps j sg IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ no_goto _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X.
  -
    intros i c kk ps j cj IL Hret Hcj E E' R' M1 M1' cr' HagE Hag HLF HC.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_facts_ok _ _ _ _ _ IL) as X. unfold leaf_facts_chk in X.
    change (CH2.is_call MALLOC FREE [MEMMOVE] MALLOC) with true in X. cbv beta iota in X. rewrite Hret, Hcj in X. change (Z.eqb MALLOC MALLOC) with true in X. cbv beta iota in X.
    repeat (apply andb_prop in X as [X ?Y]). repeat (apply andb_prop in Y as [Y ?Z]). apply Nat.leb_le in X, Y0. apply expr_eqb_eq in Z1. apply negb_true_iff in Z2.
    assert (HagE' : env_agree GT.NF E0 E') by (eapply CC.env_agree_trans; [exact HagE | eapply CC.env_agree_le; [exact Hag | exact X]]).
    rewrite LS in HLF. destruct (ARM E' M1' (SR.ps_cells ps) (hd_size j) HagE' (CC.lf_cells _ _ _ _ _ _ _ HLF) Z) as [Hval Hgrow].
    unfold Cred in HC. rewrite Y in HC. subst cr'. rewrite <- Z1. rewrite Hval. split; [apply Hcredit; lia|].
    intros E2 Hag2. unfold Cred. rewrite Z2. rewrite den_hd. fold (hd_size j). f_equal. rewrite <- Hval.
    f_equal. apply (SR.edenot_agree_AP GT.NF E' E2); [eapply CC.env_agree_le; [exact Hag2 | lia] | exact Z0].
  -
    intros i c kk ps pc j cj IL Hcall Hnm Hret Hcj E E' R' M1 M1' cr' HagE Hag HLF HC E2 Hag2.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_facts_ok _ _ _ _ _ IL) as X. unfold leaf_facts_chk in X. rewrite Hcall, Hret, Hcj in X.
    destruct (Z.eqb_spec pc MALLOC) as [->|_]; [contradiction|]. repeat (apply andb_prop in X as [X ?Y]). apply andb_prop in Y as [Y Z].
    apply Nat.leb_le in X, Y0. apply Bool.eqb_prop in Y.
    unfold Cred in *. rewrite <- Y. destruct (pre i) eqn:Hpre; [exact HC|]. cbn [orb] in Z. apply andb_prop in Z as [Z2 Z3]. apply expr_eqb_eq in Z2.
    rewrite HC. f_equal. rewrite !den_hd. fold (hd_size i) (hd_size j). rewrite <- Z2. f_equal.
    apply (SR.edenot_agree_AP GT.NF E E2); [|exact Z3].
    eapply CC.env_agree_trans; [eapply CC.env_agree_le; [exact Hag | exact X] | eapply CC.env_agree_le; [exact Hag2 | lia]].
  -
    intros i c kk ps pc IL Hnc fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF _.
    pose proof (CH2.leaves_all_sound _ _ _ leaf_facts_ok _ _ _ _ _ IL) as X. unfold leaf_facts_chk in X. rewrite Hnc in X. unfold exit_chk in X.
    pose proof (CH2.exit_amb L HI HIok LYI LYE (PmLayout.ly_ro L LAY) GT.NF E0 M model (lb_remove p LB) sp G.HDECL [(o, 24)] G.BLS (Cred cr) STKF SCRP NF32 U2 W_OK WRS_OK
                  G.CPS 0x10000 0xf8000 G.TAGS G.RETS MALLOC FREE [MEMMOVE] heap_ok i c kk ps pc IL Hnc E E' R1 R' M1 M' m1 HAt HAmb Hag HLF) as HA'.
    repeat (apply andb_prop in X as [X ?Y]). clear Y10.
    apply Z.eqb_eq in X. apply Nat.leb_le in Y7.
    pose proof HA' as HA2. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr1 & Hdf1).
    assert (HagE' : env_agree GT.NF E0 E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | exact Y7]]).
    destruct (FR E' HagE') as (F2 & F10 & F11 & F12 & F32 & F33 & F34 & FB).
    rewrite LS in HLF.
    assert (CELL : forall X0, has (SR.ps_cells ps) X0 = true -> kentry_ok RSEGS E' M' X0).
    { intros X0 HX. apply (CC.lf_cells _ _ _ _ _ _ _ HLF). unfold has in HX. apply existsb_exists in HX as (Y' & HY & He). apply APS.kentry_eqb_eq in He. subst Y'. exact HY. }

    unfold hd_base, hd_size in *. destruct (nth i G.BLS []) as [|[pe ce] [|]] eqn:HBL; try discriminate Y0. cbn [hd fst snd] in *.
    set (pX := bv_unsigned (edenot E' pe)) in *. set (capX := bv_unsigned (edenot E' ce)) in *.
    assert (HH2 : hi_heap HI ((pX, capX) :: lb_remove p LB) cr1 M' (m_vmmaps m1)).
    { unfold CH2.cur in HH1. rewrite HBL in HH1. rewrite <- (CH2.den_agree _ E E' _ Hag Y8) in HH1. exact HH1. }
    destruct (hio_wf L SCFG HI HIok _ _ _ _ HH2) as (Hwf2 & Hnd2 & _).
    destruct (Hwf2 (pX, capX) (or_introl eq_refl)) as ((Q0 & Q1 & Q2 & Q3 & Q4) & Qdef & Qap). cbn [fst snd lb_remove] in Q0, Q1, Q2, Q3, Q4, Qdef, Qap. rewrite Z.eqb_refl in Qap.

    assert (UN : bv_unsigned (edenot E' NEED) = n + size) by (apply CL5.u_lin; [unfold NEED, e_n, e_size; lin_eval; rw_atoms; lia | lia]).
    assert (UW0 : bv_unsigned (edenot E' (APC.eaddz ce 1)) = capX + 1).
    { unfold APC.eaddz. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite (u64_of_Z 1) by lia. fold capX. apply Z.mod_small. lia. }
    assert (USP : bv_unsigned (edenot E' (EAlu ALU_ADD e_size pe)) = size + pX).
    { cbn [edenot e_size]. rewrite u_add64, F33. fold pX. apply Z.mod_small. lia. }
    assert (UNSP : bv_unsigned (edenot E' (EAlu ALU_ADD e_n (EAlu ALU_ADD e_size pe))) = n + (size + pX)).
    { cbn [edenot e_n e_size]. rewrite !u_add64, F12, F33. fold pX. rewrite (Z.mod_small (size + pX)) by lia. apply Z.mod_small. lia. }
    assert (W0 : L5.u64_at RSEGS M' o (capX + 1)).
    { apply (CL5.kword64_elim RSEGS E' M' _ _ o _ (CELL _ Y6)); [unfold estart; cbn [a_base a_off edenot]; rewrite F10; lia | exact UW0]. }
    assert (W8 : L5.u64_at RSEGS M' (o + 8) (n + size)).
    { apply (CL5.kword64_elim RSEGS E' M' _ _ (o + 8) _ (CELL _ Y5)); [unfold estart; cbn [a_base a_off edenot]; rewrite F10; lia | exact UN]. }
    assert (W16 : L5.u64_at RSEGS M' (o + 16) pX).
    { apply (CL5.kword64_elim RSEGS E' M' _ _ (o + 16) _ (CELL _ Y4)); [unfold estart; cbn [a_base a_off edenot]; rewrite F10; lia | reflexivity]. }
    assert (NUL : L5.u8_at RSEGS M' (pX + (size + n)) 0).
    { apply (CL5.kword8_zero_elim RSEGS E' M' _ _ (CELL _ Y1)). unfold estart. cbn [a_base a_off]. rewrite UNSP. lia. }
    assert (BSRC : L5.bytes_at RSEGS M' (pX + size) src).
    { apply (CL5.kblob_elim RSEGS E' M' _ _ 1%nat (pX + size) src (CELL _ Y2)); [unfold estart; cbn [a_base a_off]; rewrite USP; lia | rewrite FB; reflexivity]. }
    assert (BS : L5.bytes_at RSEGS M' pX s).
    { apply orb_prop in Y3 as [Y3|Y3].
      - apply (CL5.kblob_elim RSEGS E' M' _ _ 0%nat pX s (CELL _ Y3)); [unfold estart; cbn [a_base a_off]; fold pX; lia | rewrite FB; reflexivity].
      - pose proof (CELL _ Y3) as G. cbn [kentry_ok edenot e_size] in G. rewrite F33 in G. assert (Hs0 : s = []) by (destruct s; [reflexivity | unfold size in G; cbn [length] in G; lia]).
        subst s. intros j Hj. cbn in Hj. lia. }
    assert (STR : Z.even capX = true -> L5.lstr_long RSEGS M' o (s ++ src) (capX + 1) pX).
    { intros Hev. unfold L5.lstr_long. rewrite length_app, Nat2Z.inj_add. fold size n.
      split; [rewrite Z.bit0_odd, Z.odd_add, <- Z.negb_even, Hev; reflexivity|]. split; [exact W0|]. split; [replace (size + n) with (n + size) by lia; exact W8|].
      split; [exact W16|]. split; [apply CL5.bytes_at_app; [exact BS | fold size; exact BSRC] | exact NUL]. }

    assert (KEEP : forall x : reg, In (ridx x) CSAVED -> getr R' x = getr R x).
    { intros x Hx. assert (Hx32 : (ridx x < GT.NF)%nat) by (unfold CSAVED in Hx; cbn [In] in Hx; unfold GT.NF; intuition lia).
      rewrite (CL.ps_keeps_sound RSEGS c ps E0 E' R' M1 M' CSAVED GT.NF x HLF Y9 HagE' Hx Hx32). exact (EV x). }
    assert (HRP : regs_preserved R R') by (intros x Hx; apply KEEP; exact (csaved_in x Hx)).
    assert (Hra' : getr R' 1%bv = Z_to_bv 64 r) by (rewrite (KEEP 1%bv ltac:(left; reflexivity)); exact Hra).
    assert (Hds : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)).
    { change (CH.hd_scr G.HDECL) with 8480. intros j Hj. replace (sp - 8480 + j) with (sp - (256 + (16 + 8224)) + (j + 16)) by lia. apply S5. lia. }
    pose proof (CH2.amb_hpres L HI LYI LYE GT.NF E0 M model (lb_remove p LB) sp G.HDECL [(o, 24)] G.BLS (Cred cr) STKF NF32 i E M' m1 HA2 Hds) as HP0.
    change (CH.hd_scr G.HDECL) with 8480 in HP0.
    assert (HP : L5C.hpres L (lb_remove p LB) sp (256 + (16 + 8224)) [(o, 24)] M M').
    { apply L5C.hpres_intro.
      - intros a (K1 & K2 & K3 & K4). apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP0). split; [exact K1|]. split; [|split; assumption].
        destruct K2 as [B|[[C1 C2]|C]]; [left; exact B | right; left; split; [exact C1 | lia] | right; right; exact C].
      - intros j Hj. apply (Hdf1 (sp - (256 + (16 + 8224)) + j)); [lia | | apply S5; lia].
        split; [right; left; split; lia | unfold in_errno; rewrite (PmLayout.ly_errno L LAY); lia].
      - intros a Ha HC HE Hd. apply (L5C.hpres_cdef _ _ _ _ _ _ _ a HP0 Ha); [|exact HE | exact Hd].
        destruct HC as [B|[[C1 C2]|C]]; [left; exact B | right; left; split; [exact C1 | lia] | right; right; exact C]. }
    rewrite X, LS. eapply CL.ret_cps; [exact ret_at | exact (proj1 Hmo1) | exact (proj1 (proj2 Hmo1)) | |].
    { rewrite Hra'. apply Hoare.ret_ok_even. destruct Hraok as [R1' R2']. rewrite u64_of_Z by lia. exact R2'. }
    rewrite Hra'.
    assert (LEN : Z.of_nat (length (s ++ src)) = size + n) by (rewrite length_app, Nat2Z.inj_add; reflexivity).
    destruct (pre i) eqn:Hpre.
    +
      apply andb_prop in Y as [Y Yg]. apply andb_prop in Y as [Yp Yc]. apply expr_eqb_eq in Yp, Yc. subst pe ce.
      assert (EpX : pX = p) by (unfold pX; cbn [edenot]; exact F34).
      assert (EcX : capX = cap) by (unfold capX; apply CL5.u_lin; [unfold e_k; lin_eval; rw_atoms; lia | lia]).
      assert (Hroom : size + n < cap).
      { pose proof (CELL _ Yg) as G. unfold ROOM, e_n, e_size, e_k in G. cbn [kentry_ok] in G. cbn [edenot] in G. rewrite u_sltu64 in G.
        assert (UR : bv_unsigned (edenot E' (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 2) (EVar 32)) (EMd M_MUL (ELit (-1)) (EVar 33))) (ELit (-1)))) = 2 * k - size - 1)
          by (apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]).
        cbn [edenot] in UR. rewrite UR, F12 in G. destruct (Z.ltb_spec (2 * k - size - 1) n); lia. }
      unfold Cred in HC1. rewrite Hpre in HC1. subst cr1. rewrite EpX, EcX in *.
      apply (Hcont fx' R' M' m1 LB cr (lb_remove p LB) [(o, 24)] HFP); [| exact HRP | exact HP | exact Hbv1 | exact (CH2.heap_own_back L HI HIok LB cr M' _ p cap HH2 HinLB Hnd)].
      split; [|reflexivity]. left. split; [|auto]. split; [apply STR; rewrite Hk; rewrite Z.even_mul; reflexivity|]. split; [exact Hc8 | rewrite LEN; exact Hroom].
    +
      apply andb_prop in Y as [Y Yv]. apply andb_prop in Y as [Ya Yd].
      destruct (ARM E' M' (SR.ps_cells ps) ce HagE' (CC.lf_cells _ _ _ _ _ _ _ HLF) Ya) as [Hcap Hgrow]. fold capX in Hcap.
      assert (Hlor : capX = 8 * (Z.max (size + n) (2 * (cap - 1)) / 8) + 8) by (rewrite Hcap; unfold PML.grow_cap; rewrite lor7 by lia; lia).
      assert (Hcr : cr1 = debit L cr capX).
      { unfold Cred in HC1. rewrite Hpre in HC1. rewrite HC1. f_equal. rewrite den_hd, HBL. cbn [hd snd]. unfold capX. f_equal.
        apply (SR.edenot_agree_AP (CC.cp_nx c) E E' ce Hag). unfold CH2.blocks_vars_lt in Y8. cbn [forallb fst snd] in Y8. apply andb_prop in Y8 as [Y8 _]. apply andb_prop in Y8 as [_ Y8]. exact Y8. }
      subst cr1.
      assert (Hdisj : pX + capX <= p \/ p + cap <= pX).
      { pose proof (CELL _ Yd) as G. cbn [kentry_ok] in G. unfold estart, elenZ in G. cbn [a_base a_off] in G. fold pX capX in G.
        assert (E2k : bv_unsigned (edenot E' (EMd M_MUL (ELit 2) e_k)) = cap) by (apply CL5.u_lin; [unfold e_k; lin_eval; rw_atoms; lia | lia]).
        assert (E34 : bv_unsigned (edenot E' (EVar 34)) = p) by (cbn [edenot]; exact F34).
        rewrite E2k, E34 in G. lia. }
      apply (Hcont fx' R' M' m1 ((pX, capX) :: lb_remove p LB) (debit L cr capX) (lb_remove p LB) [(o, 24)] HFP); [| exact HRP | exact HP | exact Hbv1 | exact HH2].
      split; [|reflexivity]. right. exists pX. cbv zeta. rewrite LEN, <- Hcap. split; [lia  |].
      split; [split; [apply STR; rewrite Hlor; rewrite Z.even_add, Z.even_mul; reflexivity|]; split; [rewrite Hlor; rewrite Z.add_comm, Z.mul_comm, Z.mod_add by lia; reflexivity|]|].
      { rewrite Hlor. pose proof (Z.mod_pos_bound (Z.max (size + n) (2 * (cap - 1))) 8 ltac:(lia)). pose proof (Z.div_mod (Z.max (size + n) (2 * (cap - 1))) 8 ltac:(lia)). lia. }
      split; [|auto]. split; [repeat split; assumption|]. split; [|exact Qdef].
      intros b0 Hb0. destruct (Z.eq_dec (fst b0) p) as [e0|ne0].
      * rewrite (CH2.nodup_fst_eq LB b0 (p, cap) Hnd Hb0 HinLB e0). cbn [fst snd]. exact Hdisj.
      * destruct b0 as [bb bm]. exact (Qap (bb, bm) (L5C.in_lb_remove_neq p bb bm LB Hb0 ne0)).
  - reflexivity.
  -
    rewrite LS.
    assert (Hdo : L5.defined M o 24).
    { intros i Hi. destruct (Z_lt_dec i 8); [|destruct (Z_lt_dec i 16)].
      - exact (defined_of_u64 M o _ Hw0 ltac:(lia) ltac:(lia) i ltac:(lia)).
      - replace (o + i) with (o + 8 + (i - 8)) by lia. exact (defined_of_u64 M (o + 8) _ Hw8 ltac:(lia) ltac:(lia) (i - 8) ltac:(lia)).
      - replace (o + i) with (o + 16 + (i - 16)) by lia. exact (defined_of_u64 M (o + 16) _ Hw16 ltac:(lia) ltac:(lia) (i - 16) ltac:(lia)). }
    assert (Hdq : L5.defined M q n) by exact Hdef.
    assert (Hdp : L5.defined M p cap) by exact Pdef.
    assert (Hds : L5.defined M (sp - 8480) 8480) by (intros i Hi; replace (sp - 8480 + i) with (sp - (256 + (16 + 8224)) + (i + 16)) by lia; apply S5; lia).
    assert (EL : forall e v, lden E0 (lin_of e) = v -> 0 <= v < 2 ^ 64 -> elenZ E0 e = v) by (intros; apply CL5.elen_lin; assumption).
    assert (L2k : lden E0 (lin_of (EMd Instr.M_MUL (ELit 2) (EVar 32))) = cap) by (lin_eval; rewrite U32; lia).
    assert (W0 : edenot E0 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 32)) (ELit 1)) = Z_to_bv 64 (cap + 1)).
    { rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]. }
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok, G.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply CL5.kword64_intro with (A := o) (z := cap + 1); [ev_start | lia | lia | exact W0 | exact Hw0].
    + eapply CL5.kword64_intro with (A := o + 8) (z := size); [ev_start | lia | lia | exact V33 | exact Hw8].
    + eapply CL5.kword64_intro with (A := o + 16) (z := p); [ev_start | lia | lia | exact V34 | exact Hw16].
    + e_range. + e_range. + e_range. + e_range.
    + eapply CL5.kblob_intro with (bs := s) (A := p); [ev_start | unfold elenZ; cbn [edenot]; exact U33 | lia | fold size; lia | lia | reflexivity | exact Hbs | fold size; ev_def].
    + e_unk. + e_wr. + e_range. + e_align P2.
    + e_unk. + e_wr. + e_range. + e_align O3.
    + eapply CL5.kblob_intro with (bs := src) (A := q); [ev_start | unfold elenZ; cbn [edenot]; exact U12 | lia | fold n; lia | lia | reflexivity | exact Hbytes | fold n; ev_def].
    + e_unk. + e_range. + e_range.
    + e_unk. + e_wr. + e_range. + e_align S1.
    + e_disj. + e_disj. + e_disj. + e_disj. + e_disj. + e_disj.
  -
    split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]].
    exists cr. split; [|reflexivity]. unfold CH2.cur.
    replace (CH2.den E0 (nth 0 G.BLS [])) with [(p, cap)]; [exact HH'|].
    change (nth 0 G.BLS []) with [(EVar 34, EMd Instr.M_MUL (ELit 2) (EVar 32))]. unfold CH2.den. cbn [map fst snd].
    f_equal. f_equal; [cbn [edenot]; symmetry; exact U34 | symmetry; apply CL5.u_lin; [lin_eval; rewrite U32; lia | lia]].
  - exact Hfp.
Qed.

Lemma append_zero : forall (LB : list (Z * Z)) (cr : credit) (o cap p q sp r : Z) (s : list Z),
  PML.cps_heap L HI PML.PC_STR_APPEND r sp PMS.STR_SCR LB cr
      (fun R M => 24 <= cap /\ PML.entry L R M sp r PMS.STR_SCR /\ PML.a0 R o /\ PML.a1 R q /\ PML.a2 R 0 /\
                  PML.str_at M o (PML.SLong cap p s) /\ In (p, cap) LB /\ PML.obj_on_stack L sp o 24 /\ Z.of_nat (length s) < 2 ^ 26)
      (fun R M R' M' LB' cr' LBk W => PMS.str_grown L LB cr M' o cap p s LB' cr' LBk /\ W = [(o, 24)]).
Proof.
  intros LB cr o cap p q sp r s. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (H24 & Hentry & Ha0 & Ha1 & Ha2 & Hstr & HinLB & Hobj & Hlen) Hcont.
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (S1 & S2 & S3 & S4 & S5).
  unfold PMS.STR_SCR, PMS.OPNEW_SCR, PML.HEAP_STACK in *.
  pose proof Hstr as ((Hbit & Hw0 & Hw8 & Hw16 & Hbs & Hnul) & Hc8 & Hslt).
  destruct Hobj as (O1 & O2 & O3). set (size := Z.of_nat (length s)) in *.
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_stack L LAY) as LSTK. unfold PML.HEAP_STACK in LSTK.
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & _).
  destruct (Hwf _ HinLB) as ((P0 & P1 & P2 & P3 & P4) & Pdef & Pap). cbn [fst snd] in *.
  set (k := cap / 2). assert (Hk : cap = 2 * k) by (unfold k; assert (cap mod 2 = 0) by (rewrite <- (Z.mod_mod_divide cap 8 2) by (exists 4; reflexivity); rewrite Hc8; reflexivity); rewrite (Z.div_mod cap 2) at 1 by lia; lia).
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [k; size] 0))) (fun _ => [])).
  assert (EV : forall x : reg, ev E0 (ridx x) = getr R x) by (intros x; apply ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V10 : ev E0 10 = Z_to_bv 64 o) by (rewrite <- Ha0; exact (EV 10%bv)).
  assert (V12 : ev E0 12 = Z_to_bv 64 0) by (rewrite <- Ha2; exact (EV 12%bv)).
  assert (V33 : ev E0 33 = Z_to_bv 64 size) by reflexivity.
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by lia.
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = o) by (rewrite V10; apply u64_of_Z; lia).
  assert (U12 : bv_unsigned (ev E0 12) = 0) by (rewrite V12; apply u64_of_Z; lia).
  assert (U32 : bv_unsigned (ev E0 32) = k) by (change (ev E0 32) with (Z_to_bv 64 k); apply u64_of_Z; lia).
  assert (U33 : bv_unsigned (ev E0 33) = size) by (rewrite V33; apply u64_of_Z; lia).
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= 0x7fff7f800000) by (rewrite ILO, IHI; lia).
  assert (LYE : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L) by (rewrite ILO, IHI, (PmLayout.ly_errno L LAY); lia).
  assert (STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr Z0.HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
    by (change (CH.hd_scr Z0.HDECL) with 8480; repeat split; lia).
  assert (SCRP : 0 <= CH.hd_scr Z0.HDECL) by (change (CH.hd_scr Z0.HDECL) with 8480; lia).
  assert (NF32 : (32 <= Z0T.NF)%nat) by (unfold Z0T.NF; lia).
  assert (W_OK : forall (w : L5.range) (a : Z), In w [] -> L5.in_rng w a -> CH2.wclient L sp a) by (intros w a []).
  assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs Z0.HDECL) -> SGP.region_vars_lt Z0T.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w [] /\ L5.in_rng w a)) by (intros rg []).
  unfold PML.cfg. change PML.PC_STR_APPEND with (CC.cp_pc Z0.cp0). rewrite <- LS.
  eapply CH2.heap_cert_sound with (NF := Z0T.NF) (E0 := E0) (M0 := M) (model0 := model) (LBrest := LB) (sp0 := sp) (d := Z0.HDECL)
    (W := []) (BLS := Z0.BLS) (Cred := fun _ _ cr' => cr' = cr) (CPS := Z0.CPS) (TAGS := Z0.TAGS) (RETS := Z0.RETS) (MALLOC := 0xa9144) (FREE := 0xa9004)
    (COPIES := []) (IMG_LO := 0x10000) (IMG_HI := 0xf8000) (FPI := PML.fp_ok) (i := 0%nat) (E := E0) (HI := HI).
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
  - exact heap_ok0.
  - exact (PmLayout.ly_malloc L LAY).
  - exact (PmLayout.ly_free L LAY).
  - intros pc [].
  - intros i c kk ps j sg IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ exit_ok0 _ _ _ _ _ IL) as X. discriminate X.
  - intros i c kk ps j cj IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ exit_ok0 _ _ _ _ _ IL) as X. cbv beta iota in X. apply andb_prop in X as [X _]. apply andb_prop in X as [X _]. apply andb_prop in X as [X _]. discriminate X.
  - intros i c kk ps pc j cj IL Hcall. exfalso. pose proof (CH2.leaves_all_sound _ _ _ exit_ok0 _ _ _ _ _ IL) as X. cbv beta iota in X. rewrite Hcall in X. discriminate X.
  -
    intros i c kk ps pc IL Hnc fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF _.
    pose proof (CH2.leaves_all_sound _ _ _ exit_ok0 _ _ _ _ _ IL) as X. cbv beta iota in X. rewrite Hnc in X. cbn [negb andb] in X.
    apply andb_prop in X as [X Xnf]. apply andb_prop in X as [Xpc Xk]. apply CL.ps_at_sound in Xpc. destruct Xpc as [Xpc|[]]. apply Nat.leb_le in Xnf.
    pose proof (CH2.exit_amb L HI HIok LYI LYE (PmLayout.ly_ro L LAY) Z0T.NF E0 M model LB sp Z0.HDECL [] Z0.BLS (fun _ _ cr' => cr' = cr) STKF SCRP NF32 U2 W_OK WRS_OK
                  Z0.CPS 0x10000 0xf8000 Z0.TAGS Z0.RETS 0xa9144 0xa9004 [] heap_ok0 i c kk ps pc IL Hnc E E' R1 R' M1 M' m1 HAt HAmb Hag HLF) as HA'.
    pose proof HA' as HA2. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr1 & Hdf1). subst cr1.
    assert (HagE' : env_agree Z0T.NF E0 E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | exact Xnf]]).
    rewrite LS in HLF.
    assert (KEEP : forall x : reg, In (ridx x) CSAVED -> getr R' x = getr R x).
    { intros x Hx. assert (Hx32 : (ridx x < Z0T.NF)%nat) by (unfold CSAVED in Hx; cbn [In] in Hx; unfold Z0T.NF; intuition lia).
      rewrite (CL.ps_keeps_sound RSEGS c ps E0 E' R' M1 M' CSAVED Z0T.NF x HLF Xk HagE' Hx Hx32). exact (EV x). }
    assert (HRP : regs_preserved R R') by (intros x Hx; apply KEEP; exact (csaved_in x Hx)).
    assert (Hra' : getr R' 1%bv = Z_to_bv 64 r) by (rewrite (KEEP 1%bv ltac:(left; reflexivity)); exact Hra).
    assert (Hds : L5.defined M (sp - CH.hd_scr Z0.HDECL) (CH.hd_scr Z0.HDECL)).
    { change (CH.hd_scr Z0.HDECL) with 8480. intros j Hj. replace (sp - 8480 + j) with (sp - (256 + (16 + 8224)) + (j + 16)) by lia. apply S5. lia. }
    pose proof (CH2.amb_hpres L HI LYI LYE Z0T.NF E0 M model LB sp Z0.HDECL [] Z0.BLS (fun _ _ cr' => cr' = cr) STKF NF32 i E M' m1 HA2 Hds) as HP0.
    change (CH.hd_scr Z0.HDECL) with 8480 in HP0.

    assert (AG : forall a m, (sp <= a /\ a + m <= hl_sptop L) \/ (p <= a /\ a + m <= p + cap) -> L5C.agree_on M M' a m).
    { intros a m Hr. apply (L5C.frame_agree L LB sp 8480 [] M M' a m HP0). intros j Hj. destruct Hr as [Hr|Hr].
      - apply L5C.kept_stack; [lia | lia | lia | rewrite (PmLayout.ly_errno L LAY); lia | lia | apply L5C.outside_nil].
      - apply (L5C.kept_block L LB sp 8480 [] p cap j HinLB); [lia | lia | lia | rewrite (PmLayout.ly_errno L LAY); lia | apply L5C.outside_nil]. }
    assert (Hstr' : PML.str_at M' o (PML.SLong cap p (s ++ []))).
    { rewrite app_nil_r. split; [|split; assumption]. unfold L5.lstr_long. split; [exact Hbit|].
      split; [apply (L5C.u64_at_agree RSEGS M M' o _ (AG o 8 ltac:(lia))); [lia | lia | exact Hw0]|].
      split; [apply (L5C.u64_at_agree RSEGS M M' (o + 8) _ (AG (o + 8) 8 ltac:(lia))); [lia | lia | exact Hw8]|].
      split; [apply (L5C.u64_at_agree RSEGS M M' (o + 16) _ (AG (o + 16) 8 ltac:(lia))); [lia | lia | exact Hw16]|].
      split; [apply (L5C.bytes_at_agree RSEGS M M' p s (AG p size ltac:(lia))); [lia | fold size; lia | exact Hbs]|].
      apply (L5C.u8_at_agree RSEGS M M' _ _ (AG (p + size) 1 ltac:(lia))); [lia | lia | exact Hnul]. }
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
    split; [|reflexivity]. left. rewrite app_nil_r in Hstr'. auto.
  - reflexivity.
  -
    rewrite LS.
    assert (Hdo8 : L5.defined M o 8) by exact (defined_of_u64 M o _ Hw0 ltac:(lia) ltac:(lia)).
    assert (Hds : L5.defined M (sp - 8480) 8480) by (intros i Hi; replace (sp - 8480 + i) with (sp - (256 + (16 + 8224)) + (i + 16)) by lia; apply S5; lia).
    assert (W0 : edenot E0 (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 32)) (ELit 1)) = Z_to_bv 64 (cap + 1)).
    { rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]. }
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok, Z0.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + eapply CL5.kword64_intro with (A := o) (z := cap + 1); [ev_start | lia | lia | exact W0 | exact Hw0].
    + eapply CL5.kword64_intro with (A := o + 8) (z := size); [ev_start | lia | lia | exact V33 | exact Hw8].
    + e_range. + e_range. + e_range. + e_range. + e_range. + e_align O3.
    + e_unk. + e_wr. + e_range. + e_align S1. + e_disj.
  -
    split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
    split; [|split; [reflexivity | intros a _ _ Hd; exact Hd]]. exists cr. split; [exact HH | reflexivity].
  - exact Hfp.
Qed.

Theorem str_append_ok : PMS.str_append_spec L HI.
Proof.
  intros LB cr o cap p q sp r s src. unfold PML.cps_heap. intros fx R M model K HH Hmo HKnil Hfp Hpre Hcont.
  destruct Hpre as (Hentry & Ha0 & Ha1 & Ha2 & Hstr & H24 & HinLB & Hobj & Hbytes & Hdef & Hsrc & Hlen & Hcredit).
  destruct src as [|c0 src'] eqn:Esrc.
  - apply (append_zero LB cr o cap p q sp r s fx R M model K HH Hmo HKnil Hfp).
    { change (Z.of_nat (length (@nil Z))) with 0 in *. split; [exact H24|]. split; [exact Hentry|]. split; [exact Ha0|]. split; [exact Ha1|]. split; [exact Ha2|].
      split; [exact Hstr|]. split; [exact HinLB|]. split; [exact Hobj | lia]. }
    intros fx' R' M' model' LB' cr' LBk W HF HP. apply (Hcont fx' R' M' model' LB' cr' LBk W HF). rewrite app_nil_r. exact HP.
  - rewrite <- Esrc in *. apply (append_pos LB cr o cap p q sp r s src fx R M model K HH Hmo HKnil Hfp); [|exact Hcont].
    split; [split; [exact H24 | rewrite Esrc; discriminate]|]. repeat (split; [assumption|]). exact Hcredit.
Qed.
End AppendOk.

