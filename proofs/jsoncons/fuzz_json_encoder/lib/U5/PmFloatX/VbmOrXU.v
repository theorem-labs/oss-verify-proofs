(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmEncSpecs2_u5 Pm6Sums_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_vbm_or_fast_xsrc_T_u5 Cut_vbm_or_fast_xsrc_u5 Cut_vbm_or_grow0_xsrc_T_u5 Cut_vbm_or_grow0_xsrc_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmGrow Require Import GrowKit_u5 Memcpy1_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5 ParseBridges4_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5 EncAppendK_u5 EncKit_u5 EncKit3_u5 EncOpNew_u5 EncOpNewU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmFloatX Require Import VbhKitX_u5 VbmKitX_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Heap Require Import HeapIfaceU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module VBM_ORU.
Import PML. Import PMES.
Module F := Cut_vbm_or_fast_xsrc_u5.   Module FT := Cut_vbm_or_fast_xsrc_T_u5.
Module G0 := Cut_vbm_or_grow0_xsrc_u5.   Module G0T := Cut_vbm_or_grow0_xsrc_T_u5.
Definition MALLOC : Z := PML.PC_MALLOC.  Definition FREE : Z := PML.PC_FREE.  Definition OPNEW : Z := PML.PC_OPNEW.  Definition MEMCPY : Z := MC1.MEMCPY.
Definition TAILPC : Z := PMES2.bk_tail PMES2.BK_OBJECT.
Definition KEPTN : list nat := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition has := GK.has.
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.

Lemma kept_lt48 : forall y : reg, In (ridx y) KEPTN -> (ridx y < 48)%nat.
Proof. intros y Hy. unfold KEPTN in Hy. cbn [In] in Hy. intuition lia. Qed.
Lemma kept_in : forall r : reg, In (bv_unsigned r) [3; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> In (ridx r) KEPTN.
Proof. intros r H. unfold ridx, KEPTN. cbn [In] in H. repeat (destruct H as [H|H]; [rewrite <- H; cbn; tauto|]). destruct H. Qed.
Lemma reg_of_leaf : forall segs c ps E' R' (M1 M' : PML.mem) (x : bv 5) n e,
  CC.leaf_facts segs c ps E' R' M1 M' -> CL.ps_reg_is ps n e = true -> bv_unsigned x = Z.of_nat n -> getr R' x = edenot E' e.
Proof.
  intros segs c ps E' R' M1 M' x n e HLF Hchk Hx. pose proof (CL.ps_reg_is_sound segs c ps E' R' M1 M' n e HLF Hchk) as G0.
  rewrite <- Hx, Z_to_bv_bv_unsigned in G0. exact G0.
Qed.

Definition ctxb_fast : expr := EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit 32) (EVar 33)).
Definition exit_fast (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in
  (Z.eqb (SR.ps_pc ps) TAILPC && CL.ps_keeps ps KEPTN && Nat.leb FT.NF (CC.cp_nx c) && Nat.eqb i 0
   && CH2.blocks_eqb (nth i F.BLS []) [(EVar 32, EVar 34)]
   && CL.ps_reg_is ps 2 (EVar 2) && CL.ps_reg_is ps 8 (EVar 8) && CL.ps_reg_is ps 10 (EAlu ALU_ADD ctxb_fast (ELit 32))
   && has cells (KWord (SA (EVar 8) 264) 8 (EVar 32)) && has cells (KWord (SA (EVar 8) 280) 8 (EAlu ALU_ADD (EVar 32) (EVar 34)))
   && has cells (KWord (SA ctxb_fast 0) 4 (ELit 0)) && has cells (KWord (SA ctxb_fast 4) 1 (ELit 0))
   && has cells (KWord (SA ctxb_fast 6) 1 (ELit 0)) && has cells (KWord (SA ctxb_fast 24) 8 (ELit 0)))%bool.
Definition leaf_fast (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with CC.TGoto _ _ => false | CC.TOther pc => (negb (CH2.is_call MALLOC FREE [] pc) && exit_fast i c ps)%bool end.
Lemma heap_ok_fast : CH2.heap_chk FT.NF F.HDECL F.BLS F.CPS GK.HULL_LO GK.HULL_HI F.TAGS F.RETS MALLOC FREE [] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma no_goto_fast : CH2.leaves_all F.CPS F.TAGS (fun _ _ _ _ t => match t with CC.TGoto _ _ => false | CC.TOther _ => true end) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma leaf_fast_ok : CH2.leaves_all F.CPS F.TAGS leaf_fast = true.
Proof. vm_compute. reflexivity. Qed.
Lemma regs_fast : CC.cp_regs F.cp0 = sr_upd (sr_upd sr_id 9 (EAlu ALU_ADD (EVar 8) (ELit 264))) 18 ctxb_fast.
Proof. vm_compute. reflexivity. Qed.

Definition exit_grow0 (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in
  (Z.eqb (SR.ps_pc ps) TAILPC && CL.ps_keeps ps KEPTN && Nat.leb (S G0T.NF) (CC.cp_nx c) && Nat.eqb i 2
   && CH2.blocks_eqb (nth i G0.BLS []) [(EVar 48, ELit 32)]
   && CL.ps_reg_is ps 2 (EVar 2) && CL.ps_reg_is ps 8 (EVar 8) && CL.ps_reg_is ps 10 (EAlu ALU_ADD (EVar 48) (ELit 32))
   && has cells (KWord (SA (EVar 8) 264) 8 (EVar 48)) && has cells (KWord (SA (EVar 8) 280) 8 (EAlu ALU_ADD (EVar 48) (ELit 32)))
   && has cells (KWord (SA (EVar 48) 0) 4 (ELit 0)) && has cells (KWord (SA (EVar 48) 4) 1 (ELit 0))
   && has cells (KWord (SA (EVar 48) 6) 1 (ELit 0)) && has cells (KWord (SA (EVar 48) 24) 8 (ELit 0)))%bool.
Definition opnew_leaf (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) : bool :=
  match CH2.ret_of G0.RETS i k with
  | Some j =>
      match nth_error G0.CPS j with
      | Some cj => (Nat.eqb i 0 && Nat.eqb j 1 && Z.eqb (SR.ps_pc ps) OPNEW && Nat.leb G0T.NF (CC.cp_nx c)
                    && expr_eqb (nth 10 (CA.ps_reglist ps) (ELit 0)) (ELit 32)
                    && isSome (EON.opnew_chk G0T.NF G0.HDECL c ps cj (nth i G0.BLS []) (nth j G0.BLS [])))%bool
      | None => false
      end
  | None => false
  end.
Definition NEWS0 : list kentry := [KUnk (SA (EVar 48) 0) (ELit 0)].
Definition memcpy_leaf (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) : bool :=
  match CH2.ret_of G0.RETS i k with
  | Some j =>
      match nth_error G0.CPS j with
      | Some cj => (Z.eqb (SR.ps_pc ps) MEMCPY && CL.ps_reg_is ps 10 (EVar 48) && CL.ps_reg_is ps 11 (ELit 0) && CL.ps_reg_is ps 12 (ELit 0)
                    && CH2.blocks_eqb (nth j G0.BLS []) (nth i G0.BLS [])
                    && match CH2.custom_chk G0T.NF G0.HDECL 0 0 (nth i G0.BLS []) [] NEWS0 (Some (EVar 48)) c ps cj (nth i G0.BLS []) with
                       | Some ci => Nat.ltb 48 (CH2.ci_nx ci)
                       | None => false
                       end)%bool
      | None => false
      end
  | None => false
  end.
Definition leaf_grow0 (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => false
  | CC.TOther pc =>
      if CH2.is_call MALLOC FREE [] pc then false
      else if Z.eqb pc OPNEW then opnew_leaf i c k ps
      else if Z.eqb pc MEMCPY then memcpy_leaf i c k ps
      else exit_grow0 i c ps
  end.
Lemma heap_ok_grow0 : CH2.heap_chk G0T.NF G0.HDECL G0.BLS G0.CPS GK.HULL_LO GK.HULL_HI G0.TAGS G0.RETS MALLOC FREE [] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma no_goto_grow0 : CH2.leaves_all G0.CPS G0.TAGS (fun _ _ _ _ t => match t with CC.TGoto _ _ => false | CC.TOther _ => true end) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma leaf_grow0_ok : CH2.leaves_all G0.CPS G0.TAGS leaf_grow0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma regs_grow0 : CC.cp_regs G0.cp0 = sr_upd (sr_upd sr_id 9 (EAlu ALU_ADD (EVar 8) (ELit 264))) 18 (EVar 32).
Proof. vm_compute. reflexivity. Qed.

Ltac andn H := let A := fresh "A" in apply andb_prop in H as [H A].
Lemma kept_pres : forall R R' : bvmap 5 word, APSX.kept_ok R R' -> regs_preserved R R'.
Proof.
  intros R R' H r Hr. apply H.
  - intros ->. cbn in Hr. intuition discriminate.
  - unfold callee_saved_idx in Hr. cbn [In] in Hr. unfold ridx, APC.caller_saved.
    repeat (destruct Hr as [Hr|Hr]; [rewrite <- Hr; cbv; intuition discriminate|]). destruct Hr.
Qed.

Section Mid.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps GK.RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom GK.RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom GK.RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis OPNEWXU : PMES.opnew_x_specU L HI.

Lemma hh_perm : forall LB LB' cr M VM, hi_heap HI LB cr M VM -> Permutation LB LB' -> hi_heap HI LB' cr M VM.
Proof.
  intros LB LB' cr M VM HH HP. destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (_ & Hnd & _).
  apply (hio_perm L SCFG HI HIok LB LB' cr M VM HH).
  - intros b0. split; [apply (Permutation_in b0 HP) | apply (Permutation_in b0 (Permutation_sym HP))].
  - apply base.NoDup_ListNoDup. apply (Permutation_NoDup (Permutation_map fst HP)). apply base.NoDup_ListNoDup. exact Hnd.
Qed.

Theorem mid_ok : PMES2.mid_obj_root_spec L HI.
Proof.
  unfold PMES2.mid_obj_root_spec, PMES2.mid_spec, PMES2.cps_seg.
  intros LBo cr sp V S2 b capb dI dD es fx R M model K HH Hmo HKnil Hfp PRE Hcont.
  destruct PRE as (Hsp & Htp & Hstk & Hsp16 & H8 & H9 & HGX & HRX & HOBJ & HSTK & Hdep & Hobjs & Hdef64 & Hgrow).
  unfold PMES2.is_root in HGX. subst es. unfold PMES2.RX_OBJ_ROOT in HRX. rename HRX into H18.
  assert (MS : PMES2.MID_SCR = 8384) by reflexivity. rewrite MS in *.
  destruct Hstk as (SK1 & SK2 & SK3 & SK4 & SK5).
  unfold PMES2.FRAME, ENC_SIZE in *. destruct Hobjs as (OV1 & OV2 & OV3).
  pose proof (PmLayout.ly_segs L LAY) as LS. pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI. pose proof (PmLayout.ly_stack L LAY) as LSTK. unfold PML.HEAP_STACK in LSTK.
  pose proof (PmLayout.ly_errno L LAY) as LER.
  destruct HSTK as (T1 & T2 & T3 & T4 & T5 & _). assert (D0 : PMES.depth (@nil ectx) = 0) by reflexivity. rewrite ?D0 in *.
  unfold O_STACK in T1, T2, T3. replace (V + 264 + 8) with (V + 272) in T2 by lia. replace (V + 264 + 16) with (V + 280) in T3 by lia.
  assert (Hd264 : L5.defined M (V + 264) 24).
  { intros j Hj. destruct (Z_lt_dec j 8) as [Hj8|Hj8]; [|destruct (Z_lt_dec j 16) as [Hj16|Hj16]].
    - exact (PB.defined_of_u64 M (V + 264) _ T1 ltac:(lia) ltac:(lia) j ltac:(lia)).
    - replace (V + 264 + j) with (V + 272 + (j - 8)) by lia. exact (PB.defined_of_u64 M (V + 272) _ T2 ltac:(lia) ltac:(lia) (j - 8) ltac:(lia)).
    - replace (V + 264 + j) with (V + 280 + (j - 16)) by lia. exact (PB.defined_of_u64 M (V + 280) _ T3 ltac:(lia) ltac:(lia) (j - 16) ltac:(lia)). }
  pose proof HOBJ as HOBJ0.
  destruct HOBJ0 as (_ & _ & _ & _ & _ & E28 & _ & E30 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ecol & _ & _ & _ & (_ & E344) & _ & _ & _).
  unfold O_SPLITS, O_COLUMN, O_OBRACE in E28, E30, Ecol, E344. replace (V + 28 + 2) with (V + 30) in E30 by lia. replace (V + 336 + 8) with (V + 344) in E344 by lia.
  destruct (EAK.u64_of_defined M (V + 296) Ecol) as (col & Hcolr & Hcolu).
  assert (CLO : 0x7fff7f800000 <= hl_ceil L) by lia.
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (Hwf & Hnd & Hcr0 & _).
  set (E0 := Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [b; 0; capb; col] 0))) (fun _ => [])).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
  assert (V4 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite <- Htp; exact (EV 4%bv)).
  assert (V8 : ev E0 8 = Z_to_bv 64 V) by (rewrite <- H8; exact (EV 8%bv)).
  assert (V32 : ev E0 32 = Z_to_bv 64 b) by reflexivity.
  assert (V33 : ev E0 33 = Z_to_bv 64 0) by reflexivity.
  assert (V34 : ev E0 34 = Z_to_bv 64 capb) by reflexivity.
  assert (V35 : ev E0 35 = Z_to_bv 64 col) by reflexivity.
  assert (HBC0 : 0 <= b /\ b + capb <= hl_ceil L /\ 0 <= capb <= 32768).
  { destruct T5 as [[Hc0 Hb0]|(kk & Hkk & Hck)]; [lia|]. assert (Hpk : 2 ^ kk <= 2 ^ 10) by (apply Z.pow_le_mono_r; lia). change (2 ^ 10) with 1024 in Hpk.
    assert (Hp0 : 0 < 2 ^ kk) by (apply Z.pow_pos_nonneg; lia).
    assert (HinLB : In (b, capb) (LBo ++ stack_blocks b capb)) by (unfold stack_blocks; destruct (Z.eqb_spec capb 0); [nia|]; apply in_or_app; right; left; reflexivity).
    destruct (Hwf _ HinLB) as ((P0 & _ & _ & _ & P4) & _). cbn [fst snd] in P0, P4. nia. }
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; lia).
  assert (U8 : bv_unsigned (ev E0 8) = V) by (rewrite V8; apply u64_of_Z; lia).
  assert (U32 : bv_unsigned (ev E0 32) = b) by (rewrite V32; apply u64_of_Z; lia).
  assert (U33 : bv_unsigned (ev E0 33) = 0) by (rewrite V33; apply u64_of_Z; lia).
  assert (U34 : bv_unsigned (ev E0 34) = capb) by (rewrite V34; apply u64_of_Z; lia).
  assert (U35 : bv_unsigned (ev E0 35) = col) by (rewrite V35; apply u64_of_Z; lia).
  assert (FR : forall E1, env_agree 48 E0 E1 ->
            bv_unsigned (ev E1 2) = sp /\ bv_unsigned (ev E1 8) = V /\ bv_unsigned (ev E1 32) = b /\ bv_unsigned (ev E1 33) = 0 /\
            bv_unsigned (ev E1 34) = capb /\ bv_unsigned (ev E1 35) = col).
  { intros E1 [AG _]. rewrite <- !AG by lia. repeat split; assumption. }
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= 0x7fff7f800000) by (rewrite ILO, IHI; lia).
  assert (LYE : hl_img_lo L <= hl_errno L /\ hl_errno L + 4 <= hl_img_hi L) by (rewrite ILO, IHI, LER; lia).
  assert (TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite V4, (PmLayout.ly_tp L LAY); reflexivity).
  assert (LSTK0 : 0 <= hl_stack L) by (rewrite LSTK; lia).
  set (W := PMES2.W_mid PMES2.BK_OBJECT V sp).
  assert (W_OK : forall (w : L5.range) (a : Z), In w W -> L5.in_rng w a -> CH2.wclient L sp a).
  { intros w a Hw Hin. unfold W, PMES2.W_mid, PMES2.LOC, O_STACK in Hw. cbn [PMES2.bk_arr PMES2.BK_OBJECT] in Hw.
    destruct Hw as [<-|[<-|[]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin; (split; [lia | left; lia]). }
  assert (FPM0 : forall (fx0 fx' : FPState) R0 pc M1 R' pc' M', msteps (hl_segs L) (@mkst fx0 R0 (Z_to_bv 64 pc) M1 (seg_rom (hl_segs L))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs L))) -> PML.fp_ok fx0 -> PML.fp_ok fx')
    by (rewrite LS; exact FPM).
  assert (KST : forall (M' : PML.mem) LBk, L5C.hpres L LBk sp 8384 W M M' ->
            forall a, sp + 32 <= a < 2 ^ 64 -> ~ (V + 264 <= a < V + 288) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros M' LBk HP a Ha Hna. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP).
    apply (L5C.kept_stack_stk L LBk M sp 8384 W a); [repeat split; try lia; exact SK5 | lia | lia | rewrite LER; lia |].
    unfold W, PMES2.W_mid, PMES2.LOC, O_STACK. cbn [PMES2.bk_arr PMES2.BK_OBJECT].
    apply L5C.outside_cons; [unfold L5.in_rng; cbn [fst snd]; lia|]. apply L5C.outside_cons; [unfold L5.in_rng; cbn [fst snd]; lia | apply L5C.outside_nil]. }
  assert (OBJ' : forall (M' : PML.mem) LBk, L5C.hpres L LBk sp 8384 W M M' -> PMES2.enc_objx M' V S2 dI dD).
  { intros M' LBk HP. assert (AGV : forall a n, V <= a -> a + n <= V + 408 -> (a + n <= V + 264 \/ V + 288 <= a) -> L5C.agree_on M M' a n).
    { intros a n Ha Hn Hx i1 Hi1. apply (KST M' LBk HP); lia. }
    apply (EK3.enc_objx_agree M M' V S2 dI dD ltac:(lia) ltac:(unfold ENC_SIZE; lia)); unfold O_STACK, O_INDENT, O_COLON, O_COLUMN, ENC_SIZE.
    - apply AGV; lia. - apply AGV; lia. - apply AGV; lia.
    - apply (L5C.defined_agree M M' (V + 296) 8); [apply AGV; lia | exact Ecol].
    - exact HOBJ. }
  destruct T5 as [[Hc0 Hb0]|(kk & Hkk & Hck)].
  -
    subst capb b. rewrite VBK.stack_blocks_zero, app_nil_r in HH.
    destruct (Hgrow eq_refl) as (Hcredit & Hn). unfold stack_grow in Hcredit, Hn. cbn in Hcredit, Hn.
    set (Cred := fun (i : nat) (_ : env) (cr' : credit) => cr' = match nth i G0.BLS [] with [] => cr | _ :: _ => debit L cr 32 end).
    assert (CRED_BLK : forall i j E E2 cr0, CH2.den E2 (nth j G0.BLS []) = CH2.den E (nth i G0.BLS []) -> Cred i E cr0 -> Cred j E2 cr0).
    { intros i j E E2 cr0 Hd HC. unfold Cred in *.
      destruct (nth j G0.BLS []) as [|x l], (nth i G0.BLS []) as [|y l']; first [exact HC | discriminate Hd | (cbn [CH2.den map] in Hd; discriminate Hd) | (cbn in Hd; discriminate Hd)]. }
    assert (STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr G0.HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
      by (change (CH.hd_scr G0.HDECL) with 8384; repeat split; lia).
    assert (SCRP : 0 <= CH.hd_scr G0.HDECL) by (change (CH.hd_scr G0.HDECL) with 8384; lia).
    assert (NF32 : (32 <= G0T.NF)%nat) by (unfold G0T.NF; lia).
    assert (HSTKE : hl_stack L = CH.hd_hstk G0.HDECL) by (rewrite LSTK; reflexivity).
    assert (DEF0 : L5.defined M (sp - CH.hd_scr G0.HDECL) (CH.hd_scr G0.HDECL)) by (change (CH.hd_scr G0.HDECL) with 8384; exact SK5).
    assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G0.HDECL) -> SGP.region_vars_lt G0T.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> CH2.sclient L LBo sp a)).
    { intros rg Hrg. unfold G0.HDECL, G0T.HDECL in Hrg. cbn [CH.hd_crs] in Hrg.
      repeat (destruct Hrg as [<-|Hrg]); [..|destruct Hrg]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
      all: rewrite U8 in Ha; rewrite u64_of_Z in Ha by lia; (split; [lia | left; lia]). }
    assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G0.HDECL) -> SGP.region_vars_lt G0T.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w W /\ L5.in_rng w a)).
    { intros rg Hrg. unfold G0.HDECL, G0T.HDECL in Hrg. cbn [CH.hd_wrs] in Hrg.
      repeat (destruct Hrg as [<-|Hrg]); [..|destruct Hrg]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
      - rewrite U8 in Ha. rewrite u64_of_Z in Ha by lia. exists (V + O_STACK, 24). split; [left; reflexivity | unfold L5.in_rng, O_STACK; cbn [fst snd]; lia].
      - rewrite U2 in Ha. rewrite u64_of_Z in Ha by lia. exists (sp, 32). split; [right; left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
    unfold PML.cfg. change PMES2.PC_MID_OBJ_ROOT with (CC.cp_pc G0.cp0). rewrite <- LS.
    eapply CH2.heap_cert_sound with (NF := G0T.NF) (E0 := E0) (M0 := M) (model0 := model) (LBrest := LBo) (sp0 := sp) (d := G0.HDECL)
      (W := W) (BLS := G0.BLS) (Cred := Cred) (CPS := G0.CPS) (TAGS := G0.TAGS) (RETS := G0.RETS) (MALLOC := MALLOC) (FREE := FREE)
      (COPIES := []) (IMG_LO := GK.HULL_LO) (IMG_HI := GK.HULL_HI) (FPI := PML.fp_ok) (i := 0%nat) (E := E0) (HI := HI).
    + exact HIok.
    + exact LYI.
    + exact LYE.
    + exact (PmLayout.ly_ro L LAY).
    + exact LSTK0.
    + exact STKF.
    + exact SCRP.
    + exact HSTKE.
    + exact NF32.
    + exact U2.
    + exact TP0.
    + exact W_OK.
    + exact CRS_OK.
    + exact WRS_OK.
    + intros rg a [].
    + exact HKnil.
    + exact ILO.
    + exact IHI.
    + exact FPM0.
    + rewrite LS. exact G0.plans.
    + exact G0.tags_ok.
    + exact heap_ok_grow0.
    + exact (PmLayout.ly_malloc L LAY).
    + exact (PmLayout.ly_free L LAY).
    + intros pc [].
    + intros i c0' kk0 ps j sg IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ no_goto_grow0 _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X.
    + intros i c0' kk0 ps j cj IL Hret Hcj E E' R' M1 M1' cr' HagE Hag HLF HC. exfalso.
      pose proof (CH2.leaves_all_sound _ _ _ leaf_grow0_ok _ _ _ _ _ IL) as X. unfold leaf_grow0 in X. change (CH2.is_call MALLOC FREE [] MALLOC) with true in X. discriminate X.
    + intros i c0' kk0 ps pc j cj IL Hcall Hnm Hret Hcj. exfalso.
      pose proof (CH2.leaves_all_sound _ _ _ leaf_grow0_ok _ _ _ _ _ IL) as X. unfold leaf_grow0 in X. rewrite Hcall in X. discriminate X.
    + intros i c0' kk0 ps pc IL Hnc.
      pose proof (CH2.leaves_all_sound _ _ _ leaf_grow0_ok _ _ _ _ _ IL) as X. unfold leaf_grow0 in X. rewrite Hnc in X.
      destruct (Z.eqb_spec pc OPNEW) as [->|Hno].
      { try rewrite Z.eqb_refl in X. cbn beta iota in X. unfold opnew_leaf, isSome in X.
        destruct (CH2.ret_of G0.RETS i kk0) as [j|] eqn:Hret; cbn beta iota in X; [|discriminate X].
        destruct (nth_error G0.CPS j) as [cj|] eqn:Hcj; cbn beta iota in X; [|discriminate X].
        destruct (EON.opnew_chk G0T.NF G0.HDECL c0' ps cj (nth i G0.BLS []) (nth j G0.BLS [])) as [ci|] eqn:Hchk; cbn beta iota in X; [|rewrite andb_false_r in X; discriminate X].
        do 5 andn X.
        apply Nat.eqb_eq in X.
        match goal with H : Nat.eqb j 1 = true |- _ => apply Nat.eqb_eq in H; rename H into Xj end.
        match goal with H : Z.eqb (SR.ps_pc ps) OPNEW = true |- _ => apply Z.eqb_eq in H; rename H into Xpc end.
        match goal with H : expr_eqb _ (ELit 32) = true |- _ => apply expr_eqb_eq in H; rename H into X10 end.
        set (XI := fun (_ : nat) (_ : env) (_ : PML.mem) => True).
        assert (LO : CC.leaf_ok (hl_segs L) G0.CPS (CH2.amb3 L HI G0T.NF E0 M model LBo sp G0.HDECL W G0.BLS Cred XI) K PML.fp_ok i c0' ps).
        { apply (EONU.opnew_leaf_okU L HI HIok LAY G0T.NF E0 M model LBo sp G0.HDECL W G0.BLS Cred STKF SCRP NF32 U2 TP0 W_OK
                   CRS_OK WRS_OK ltac:(intros rg a []) G0.CPS G0.TAGS G0.RETS K HKnil XI DEF0 OPNEWXU i c0' kk0 ps j cj ci IL Hret Hcj Xpc Hchk); [|intros; exact I].
          intros E E' R' M1 M1' cr1 HagE' Hag HLF HC. unfold Cred in HC. rewrite X in HC. cbn in HC. subst cr1.
          rewrite X10. unfold EON.uv, PB.uv. cbn [edenot]. rewrite u64_of_Z by lia.
          split; [unfold NBU; lia|]. split; [exact Hcredit|]. intros E2 _. unfold Cred. rewrite Xj. reflexivity. }
        intros fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF HIH.
        apply (LO fx' E R1 M1 m1 E' R' M' HAt (conj HAmb I) HFP Hag HLF).
        intros j0 cj0 fx2 E2 R2 M2 model2 Hcj0 HAt2 [HA2 _] HFP2 Hlt. exact (HIH j0 cj0 fx2 E2 R2 M2 model2 Hcj0 HAt2 HA2 HFP2 Hlt). }
      try (apply Z.eqb_neq in Hno; rewrite Hno in X). cbn beta iota in X.
      destruct (Z.eqb_spec pc MEMCPY) as [->|Hnm].
      { try rewrite Z.eqb_refl in X. cbn beta iota in X. unfold memcpy_leaf in X.
        destruct (CH2.ret_of G0.RETS i kk0) as [j|] eqn:Hret; cbn beta iota in X; [|discriminate X].
        destruct (nth_error G0.CPS j) as [cj|] eqn:Hcj; cbn beta iota in X; [|discriminate X].
        destruct (CH2.custom_chk G0T.NF G0.HDECL 0 0 (nth i G0.BLS []) [] NEWS0 (Some (EVar 48)) c0' ps cj (nth i G0.BLS [])) as [ci|] eqn:Hchk;
          cbn beta iota in X; [|rewrite andb_false_r in X; discriminate X].
        apply andb_prop in X as [X Mnx]. apply andb_prop in X as [X Mbl]. apply andb_prop in X as [X M12]. apply andb_prop in X as [X M11]. apply andb_prop in X as [X M10].
        apply Z.eqb_eq in X. apply Nat.ltb_lt in Mnx.
        set (XI := fun (_ : nat) (_ : env) (_ : PML.mem) => True).
        assert (LO : CC.leaf_ok (hl_segs L) G0.CPS (CH2.amb3 L HI G0T.NF E0 M model LBo sp G0.HDECL W G0.BLS Cred XI) K PML.fp_ok i c0' ps).
        { apply (PB4.pure_leaf_ok L HI HIok LAY G0T.NF E0 M model LBo sp G0.HDECL W G0.BLS Cred STKF SCRP NF32 U2 TP0 W_OK CRS_OK WRS_OK
                   ltac:(intros rg a []) G0.CPS G0.TAGS G0.RETS K XI DEF0 CRED_BLK MEMCPY 0 0%nat [] NEWS0 (Some (EVar 48)) [] i c0' kk0 ps j cj ci IL Hret Hcj X Hchk Mbl).
          - intros w a [].
          - intros E1 _ w a [].
          - intros fx1 E1 E1' R1' M1a M1b model1 _ _ HLF1 _ _ _ HENT _ HFP1 Hhalt Hlazy CONT.
            destruct HENT as (Hra & Hraok & _ & _ & _).
            assert (G10 : getr R1' 10%bv = edenot E1' (EVar 48)) by exact (reg_of_leaf _ c0' ps E1' R1' M1a M1b 10%bv 10 _ HLF1 M10 eq_refl).
            assert (G11 : getr R1' 11%bv = Z_to_bv 64 0) by exact (reg_of_leaf _ c0' ps E1' R1' M1a M1b 11%bv 11 _ HLF1 M11 eq_refl).
            assert (G12 : getr R1' 12%bv = Z_to_bv 64 0) by exact (reg_of_leaf _ c0' ps E1' R1' M1a M1b 12%bv 12 _ HLF1 M12 eq_refl).
            pose proof (u64_range (getr R1' 10%bv)) as RD.
            destruct (src0_copy_spec_memcpy fx1 M1b (getr R1' 10%bv) (getr R1' 11%bv) 0 [] R1' (getr R1' 1%bv)) as (R2 & HMS & HKO & H10).
            { lia. } { reflexivity. } { reflexivity. } { reflexivity. }
            { right. rewrite G11. rewrite u64_of_Z by lia. lia. }
            { rewrite G11. rewrite u64_of_Z by lia. lia. }
            { lia. }
            { rewrite Hra. apply Hoare.ret_ok_even. destruct Hraok as (Hr1 & Hr2). rewrite u64_of_Z by lia. exact Hr2. }
            { reflexivity. } { reflexivity. } { reflexivity. } { exact G12. }
            unfold PML.cfg.
            eapply chain_mst_srealizes; [exact Hhalt | exact Hlazy | exact HMS |].
            rewrite Hra. change (wbytes M1b (getr R1' 10%bv) []) with M1b.
            apply (CONT fx1 R2 M1b [] eq_refl HFP1).
            + exact (kept_pres R1' R2 HKO).
            + apply L5.frame_but_refl.
            + apply mem_grows_refl.
            + rewrite H10, G10. cbn [edenot]. destruct (CH2.retEx_agree E1' (CH2.ci_nx ci) [] R2) as [AG _]. apply AG. lia.
            + intros X0 HX0. unfold NEWS0 in HX0. destruct HX0 as [<-|[]].
              pose proof (u64_range (edenot (CH2.retEx E1' (CH2.ci_nx ci) [] R2) (EVar 48))) as RA.
              eapply CL5.kunk_intro with (A := bv_unsigned (edenot (CH2.retEx E1' (CH2.ci_nx ci) [] R2) (EVar 48))) (N := 0).
              * unfold estart. cbn [a_base a_off]. first [lia | (rewrite Z.mod_small by lia; lia)].
              * reflexivity.
              * lia.
              * lia.
              * lia.
              * intros i0 Hi0. lia.
            + intros _. exact I. }
        intros fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF HIH.
        apply (LO fx' E R1 M1 m1 E' R' M' HAt (conj HAmb I) HFP Hag HLF).
        intros j0 cj0 fx2 E2 R2 M2 model2 Hcj0 HAt2 [HA2 _] HFP2 Hlt. exact (HIH j0 cj0 fx2 E2 R2 M2 model2 Hcj0 HAt2 HA2 HFP2 Hlt). }
      try (apply Z.eqb_neq in Hnm; rewrite Hnm in X). cbn beta iota in X.
      intros fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF _. unfold exit_grow0 in X.
      pose proof (CH2.exit_amb L HI HIok LYI LYE (PmLayout.ly_ro L LAY) G0T.NF E0 M model LBo sp G0.HDECL W G0.BLS Cred STKF SCRP NF32 U2 W_OK WRS_OK
                    G0.CPS GK.HULL_LO GK.HULL_HI G0.TAGS G0.RETS MALLOC FREE [] heap_ok_grow0 i c0' kk0 ps pc IL Hnc E E' R1 R' M1 M' m1 HAt HAmb Hag HLF) as HA'.
      do 13 andn X.
      apply Z.eqb_eq in X.
      match goal with H : Nat.leb _ (CC.cp_nx c0') = true |- _ => apply Nat.leb_le in H; rename H into XNF end.
      match goal with H : Nat.eqb i 2 = true |- _ => apply Nat.eqb_eq in H; rename H into Xi end. subst i.
      match goal with H : CH2.blocks_eqb _ _ = true |- _ => apply CH2.blocks_eqb_eq in H; rename H into XBL end.
      pose proof HA' as HA2. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr1 & Hdf1).
      unfold Cred in HC1. cbn in HC1. subst cr1.
      assert (HagE' : env_agree G0T.NF E0 E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | lia]]).
      destruct (FR E' HagE') as (F2 & F8 & _ & _ & _ & _).
      assert (A48 : ev E' 48 = ev E 48) by (destruct Hag as [AG _]; symmetry; apply AG; unfold G0T.NF in XNF; lia).
      rewrite LS in HLF.
      assert (CELL : forall X0, has (SR.ps_cells ps) X0 = true -> kentry_ok GK.RSEGS E' M' X0).
      { intros X0 HX. apply (CC.lf_cells _ _ _ _ _ _ _ HLF). exact (GK.has_In _ _ HX). }
      assert (REG : forall (x : bv 5) n e, CL.ps_reg_is ps n e = true -> bv_unsigned x = Z.of_nat n -> getr R' x = edenot E' e).
      { intros x n e Hc' Hx. exact (reg_of_leaf _ c0' ps E' R' M1 M' x n e HLF Hc' Hx). }
      assert (KEEP : forall y : reg, In (ridx y) KEPTN -> getr R' y = getr R y).
      { intros y Hy. match goal with H : CL.ps_keeps ps KEPTN = true |- _ => rewrite (CL.ps_keeps_sound GK.RSEGS c0' ps E0 E' R' M1 M' KEPTN G0T.NF y HLF H HagE' Hy (kept_lt48 y Hy)) end. exact (EV y). }
      unfold CH2.cur in HH1. rewrite XBL in HH1. cbn [CH2.den map app fst snd edenot] in HH1.
      set (b' := bv_unsigned (ev E 48)) in *.
      assert (U48 : bv_unsigned (ev E' 48) = b') by (rewrite A48; reflexivity).
      destruct (hio_wf L SCFG HI HIok _ _ _ _ HH1) as (Hwf2 & _).
      destruct (Hwf2 (b', 32) ltac:(left; reflexivity)) as ((B0 & B1 & B2 & B3 & B4) & Bdef & _). cbn [fst snd] in B0, B1, B2, B3, B4, Bdef.
      pose proof (CH2.amb_hpres L HI LYI LYE G0T.NF E0 M model LBo sp G0.HDECL W G0.BLS Cred STKF NF32 2%nat E M' m1 HA2 DEF0) as HP.
      change (CH.hd_scr G0.HDECL) with 8384 in HP.
      rewrite X, LS.
      apply (Hcont fx' R' M' m1 (LBo ++ [(b', 32)]) (debit L cr 32) LBo W HFP); [| exact HP | exact Hbv1 | apply (hh_perm _ _ _ _ _ HH1); apply Permutation_cons_append].
      exists b', 32.
      split. { rewrite (REG 2%bv 2%nat _ ltac:(eassumption) eq_refl). rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' _)). f_equal. cbn [edenot]. exact F2. }
      split; [rewrite (KEEP 4%bv ltac:(cbn; tauto)); exact Htp|].
      split. { rewrite (REG 8%bv 8%nat _ ltac:(eassumption) eq_refl). rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' _)). f_equal. cbn [edenot]. exact F8. }
      split. { rewrite (REG 10%bv 10%nat _ ltac:(eassumption) eq_refl). rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' _)). f_equal. rewrite ?D0. apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]. }
      split; [intros y Hy; apply KEEP; apply kept_in; exact Hy|].
      split; [exact (OBJ' M' LBo HP)|].
      split.
      { unfold PMES2.stack_mid. rewrite ?D0. unfold O_STACK.
        assert (C264 : u64 M' (V + 264) b').
        { pose proof (PB2.kword64_elim E' M' _ _ (V + 264) (CELL (KWord (SA (EVar 8) 264) 8 (EVar 48)) ltac:(assumption)) ltac:(ev_start)) as T.
          unfold PB.uv in T. cbn [edenot] in T. rewrite U48 in T. exact T. }
        assert (C280 : u64 M' (V + 264 + 16) (b' + 32)).
        { pose proof (PB2.kword64_elim E' M' _ _ (V + 264 + 16) (CELL (KWord (SA (EVar 8) 280) 8 (EAlu ALU_ADD (EVar 48) (ELit 32))) ltac:(assumption)) ltac:(ev_start)) as T.
          replace (PB.uv E' (EAlu ALU_ADD (EVar 48) (ELit 32))) with (b' + 32) in T by (unfold PB.uv; symmetry; apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]). exact T. }
        assert (CX0 : u32 M' b' 0).
        { pose proof (PB2.kword32_elim E' M' _ _ b' (CELL (KWord (SA (EVar 48) 0) 4 (ELit 0)) ltac:(assumption)) ltac:(ev_start)) as T.
          unfold PB.uv in T. cbn [edenot] in T. rewrite (u64_of_Z 0) in T by lia. exact T. }
        assert (CX4 : u8 M' (b' + 4) 0).
        { pose proof (PB2.kword8_elim E' M' _ _ (b' + 4) (CELL (KWord (SA (EVar 48) 4) 1 (ELit 0)) ltac:(assumption)) ltac:(ev_start)) as T.
          unfold PB.uv in T. cbn [edenot] in T. rewrite (u64_of_Z 0) in T by lia. exact T. }
        assert (CX6 : u8 M' (b' + 6) 0).
        { pose proof (PB2.kword8_elim E' M' _ _ (b' + 6) (CELL (KWord (SA (EVar 48) 6) 1 (ELit 0)) ltac:(assumption)) ltac:(ev_start)) as T.
          unfold PB.uv in T. cbn [edenot] in T. rewrite (u64_of_Z 0) in T by lia. exact T. }
        assert (CX24 : u64 M' (b' + 24) 0).
        { pose proof (PB2.kword64_elim E' M' _ _ (b' + 24) (CELL (KWord (SA (EVar 48) 24) 8 (ELit 0)) ltac:(assumption)) ltac:(ev_start)) as T.
          unfold PB.uv in T. cbn [edenot] in T. rewrite (u64_of_Z 0) in T by lia. exact T. }
        split; [exact C264|]. split; [exact C280|].
        split; [lia|]. split; [exists 0; cbn; lia|]. split; [intros i0 Hi0; cbn in Hi0; lia|].
        replace (b' + 32 * 0) with b' by lia.
        unfold ctx_at. cbn [ec_arr ec_nla ec_count b2z].
        split; [exact CX0|]. split; [exact CX4|]. split; [exact CX6|]. split; [exact CX24|]. split; [lia|]. exact Bdef. }
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      right. split; [reflexivity|]. split; reflexivity.
    + reflexivity.
    + rewrite LS. split.
      { rewrite regs_grow0. apply VBK.regs_ok_updn; [lia| |].
        - apply VBK.regs_ok_updn; [lia| exact (regs_ok_id R _ _) |].
          replace (Z_to_bv 5 (Z.of_nat 9)) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite H9. unfold O_STACK.
          rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. symmetry. apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia].
        - cbn [edenot]. replace (Z_to_bv 5 (Z.of_nat 18)) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite H18, V32. reflexivity. }
      unfold know_ok, G0.cp0. cbn [CC.cp_know].
      repeat (apply Forall_cons); [.. | apply Forall_nil]; first
        [ eapply CL5.kword64_intro; [ev_start | lia | lia | | first [exact T1 | exact T2 | exact T3 | exact Hcolu | exact E344]]; rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)); f_equal; try (apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia])
        | eapply PB2.kword8_intro; [ev_start | lia | lia | reflexivity | lia | first [exact E28 | exact E30]]
        | e_range
        | e_align OV3 | e_align SK1
        | e_unk | e_wr | e_disj
        | idtac ].
      all: fail "entry knowledge left".
    + split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [reflexivity | intros a _ _ Hdd; exact Hdd]].
      exists cr. split; [|reflexivity]. unfold CH2.cur. change (CH2.den E0 (nth 0 G0.BLS [])) with (@nil (Z * Z)). exact HH.
    + exact Hfp.
  -
    assert (Hpk : 2 ^ kk <= 2 ^ 10) by (apply Z.pow_le_mono_r; lia). change (2 ^ 10) with 1024 in Hpk.
    assert (Hp0 : 0 < 2 ^ kk) by (apply Z.pow_pos_nonneg; lia).
    assert (Hcnz : capb <> 0) by lia.
    rewrite (VBK.stack_blocks_pos b capb Hcnz) in HH.
    assert (HinLB : In (b, capb) (LBo ++ stack_blocks b capb)) by (rewrite (VBK.stack_blocks_pos b capb Hcnz); apply in_or_app; right; left; reflexivity).
    destruct (Hwf _ HinLB) as ((P0 & P1 & P2 & P3 & P4) & Pdef & _). cbn [fst snd] in P0, P1, P2, P3, P4, Pdef.
    assert (PdefL : L5.defined M b capb) by (first [exact Pdef | (intros j Hj; apply Pdef; lia)]).
    pose proof (hh_perm _ _ _ _ _ HH (Permutation_sym (Permutation_cons_append LBo (b, capb)))) as HH0.
    set (Cred := fun (_ : nat) (_ : env) (cr' : credit) => cr' = cr).
    assert (STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr F.HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47)
      by (change (CH.hd_scr F.HDECL) with 8384; repeat split; lia).
    assert (SCRP : 0 <= CH.hd_scr F.HDECL) by (change (CH.hd_scr F.HDECL) with 8384; lia).
    assert (NF32 : (32 <= FT.NF)%nat) by (unfold FT.NF; lia).
    assert (HSTKE : hl_stack L = CH.hd_hstk F.HDECL) by (rewrite LSTK; reflexivity).
    assert (DEF0 : L5.defined M (sp - CH.hd_scr F.HDECL) (CH.hd_scr F.HDECL)) by (change (CH.hd_scr F.HDECL) with 8384; exact SK5).
    assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs F.HDECL) -> SGP.region_vars_lt FT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> CH2.sclient L LBo sp a)).
    { intros rg Hrg. unfold F.HDECL, FT.HDECL in Hrg. cbn [CH.hd_crs] in Hrg.
      repeat (destruct Hrg as [<-|Hrg]); [..|destruct Hrg]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
      all: rewrite U8 in Ha; rewrite u64_of_Z in Ha by lia; (split; [lia | left; lia]). }
    assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs F.HDECL) -> SGP.region_vars_lt FT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w W /\ L5.in_rng w a)).
    { intros rg Hrg. unfold F.HDECL, FT.HDECL in Hrg. cbn [CH.hd_wrs] in Hrg.
      repeat (destruct Hrg as [<-|Hrg]); [..|destruct Hrg]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
      - rewrite U8 in Ha. rewrite u64_of_Z in Ha by lia. exists (V + O_STACK, 24). split; [left; reflexivity | unfold L5.in_rng, O_STACK; cbn [fst snd]; lia].
      - rewrite U2 in Ha. rewrite u64_of_Z in Ha by lia. exists (sp, 32). split; [right; left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia]. }
    unfold PML.cfg. change PMES2.PC_MID_OBJ_ROOT with (CC.cp_pc F.cp0). rewrite <- LS.
    eapply CH2.heap_cert_sound with (NF := FT.NF) (E0 := E0) (M0 := M) (model0 := model) (LBrest := LBo) (sp0 := sp) (d := F.HDECL)
      (W := W) (BLS := F.BLS) (Cred := Cred) (CPS := F.CPS) (TAGS := F.TAGS) (RETS := F.RETS) (MALLOC := MALLOC) (FREE := FREE)
      (COPIES := []) (IMG_LO := GK.HULL_LO) (IMG_HI := GK.HULL_HI) (FPI := PML.fp_ok) (i := 0%nat) (E := E0) (HI := HI).
    + exact HIok.
    + exact LYI.
    + exact LYE.
    + exact (PmLayout.ly_ro L LAY).
    + exact LSTK0.
    + exact STKF.
    + exact SCRP.
    + exact HSTKE.
    + exact NF32.
    + exact U2.
    + exact TP0.
    + exact W_OK.
    + exact CRS_OK.
    + exact WRS_OK.
    + intros rg a [].
    + exact HKnil.
    + exact ILO.
    + exact IHI.
    + exact FPM0.
    + rewrite LS. exact F.plans.
    + exact F.tags_ok.
    + exact heap_ok_fast.
    + exact (PmLayout.ly_malloc L LAY).
    + exact (PmLayout.ly_free L LAY).
    + intros pc [].
    + intros i c0' kk0 ps j sg IL. exfalso. pose proof (CH2.leaves_all_sound _ _ _ no_goto_fast _ _ _ _ _ IL) as X. cbv beta iota in X. discriminate X.
    + intros i c0' kk0 ps j cj IL Hret Hcj E E' R' M1 M1' cr' HagE Hag HLF HC. exfalso.
      pose proof (CH2.leaves_all_sound _ _ _ leaf_fast_ok _ _ _ _ _ IL) as X. unfold leaf_fast in X. change (CH2.is_call MALLOC FREE [] MALLOC) with true in X. cbn [negb andb] in X. discriminate X.
    + intros i c0' kk0 ps pc j cj IL Hcall Hnm Hret Hcj. exfalso.
      pose proof (CH2.leaves_all_sound _ _ _ leaf_fast_ok _ _ _ _ _ IL) as X. unfold leaf_fast in X. rewrite Hcall in X. cbn [negb andb] in X. discriminate X.
    + intros i c0' kk0 ps pc IL Hnc.
      pose proof (CH2.leaves_all_sound _ _ _ leaf_fast_ok _ _ _ _ _ IL) as X. unfold leaf_fast in X. rewrite Hnc in X. cbn [negb andb] in X. unfold exit_fast in X.
      intros fx' E R1 M1 m1 E' R' M' HAt HAmb HFP Hag HLF _.
      pose proof (CH2.exit_amb L HI HIok LYI LYE (PmLayout.ly_ro L LAY) FT.NF E0 M model LBo sp F.HDECL W F.BLS Cred STKF SCRP NF32 U2 W_OK WRS_OK
                    F.CPS GK.HULL_LO GK.HULL_HI F.TAGS F.RETS MALLOC FREE [] heap_ok_fast i c0' kk0 ps pc IL Hnc E E' R1 R' M1 M' m1 HAt HAmb Hag HLF) as HA'.
      do 13 andn X.
      apply Z.eqb_eq in X.
      match goal with H : Nat.leb _ (CC.cp_nx c0') = true |- _ => apply Nat.leb_le in H; rename H into XNF end.
      match goal with H : Nat.eqb i 0 = true |- _ => apply Nat.eqb_eq in H; rename H into Xi end. subst i.
      match goal with H : CH2.blocks_eqb _ _ = true |- _ => apply CH2.blocks_eqb_eq in H; rename H into XBL end.
      pose proof HA' as HA2. destruct HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr1 & Hdf1).
      unfold Cred in HC1. subst cr1.
      assert (HagE' : env_agree FT.NF E0 E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | exact XNF]]).
      destruct (FR E' HagE') as (F2 & F8 & F32 & F33 & F34 & _).
      assert (A32 : ev E 32 = ev E0 32) by (destruct HagE1 as [AG _]; symmetry; apply AG; unfold FT.NF; lia).
      assert (A34 : ev E 34 = ev E0 34) by (destruct HagE1 as [AG _]; symmetry; apply AG; unfold FT.NF; lia).
      rewrite LS in HLF.
      assert (CELL : forall X0, has (SR.ps_cells ps) X0 = true -> kentry_ok GK.RSEGS E' M' X0).
      { intros X0 HX. apply (CC.lf_cells _ _ _ _ _ _ _ HLF). exact (GK.has_In _ _ HX). }
      assert (REG : forall (x : bv 5) n e, CL.ps_reg_is ps n e = true -> bv_unsigned x = Z.of_nat n -> getr R' x = edenot E' e).
      { intros x n e Hc' Hx. exact (reg_of_leaf _ c0' ps E' R' M1 M' x n e HLF Hc' Hx). }
      assert (KEEP : forall y : reg, In (ridx y) KEPTN -> getr R' y = getr R y).
      { intros y Hy. match goal with H : CL.ps_keeps ps KEPTN = true |- _ => rewrite (CL.ps_keeps_sound GK.RSEGS c0' ps E0 E' R' M1 M' KEPTN FT.NF y HLF H HagE' Hy (kept_lt48 y Hy)) end. exact (EV y). }
      unfold CH2.cur in HH1. rewrite XBL in HH1. cbn [CH2.den map app fst snd edenot] in HH1. rewrite A32, A34, U32, U34 in HH1.
      pose proof (CH2.amb_hpres L HI LYI LYE FT.NF E0 M model LBo sp F.HDECL W F.BLS Cred STKF NF32 0%nat E M' m1 HA2 DEF0) as HP.
      change (CH.hd_scr F.HDECL) with 8384 in HP.
      destruct (hio_wf L SCFG HI HIok _ _ _ _ HH1) as (Hwf2 & _).
      destruct (Hwf2 (b, capb) ltac:(left; reflexivity)) as (_ & Bdef & _). cbn [fst snd] in Bdef.
      rewrite X, LS.
      apply (Hcont fx' R' M' m1 (LBo ++ [(b, capb)]) cr LBo W HFP); [| exact HP | exact Hbv1 | apply (hh_perm _ _ _ _ _ HH1); apply Permutation_cons_append].
      exists b, capb.
      split. { rewrite (REG 2%bv 2%nat _ ltac:(eassumption) eq_refl). rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' _)). f_equal. cbn [edenot]. exact F2. }
      split; [rewrite (KEEP 4%bv ltac:(cbn; tauto)); exact Htp|].
      split. { rewrite (REG 8%bv 8%nat _ ltac:(eassumption) eq_refl). rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' _)). f_equal. cbn [edenot]. exact F8. }
      split. { rewrite (REG 10%bv 10%nat _ ltac:(eassumption) eq_refl). rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' _)). f_equal. rewrite ?D0. unfold ctxb_fast. apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]. }
      split; [intros y Hy; apply KEEP; apply kept_in; exact Hy|].
      split; [exact (OBJ' M' LBo HP)|].
      split.
      { unfold PMES2.stack_mid. rewrite ?D0. unfold O_STACK.
        assert (CB : forall o, 0 <= o <= 32 -> estart E' (SA ctxb_fast o) = b + o).
        { intros o Ho. assert (Ub : bv_unsigned (edenot E' ctxb_fast) = b) by (unfold ctxb_fast; apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]).
          unfold estart. cbn [a_base a_off]. rewrite Ub. first [reflexivity | lia | (rewrite Z.mod_small; lia)]. }
        assert (C264 : u64 M' (V + 264) b).
        { pose proof (PB2.kword64_elim E' M' _ _ (V + 264) (CELL (KWord (SA (EVar 8) 264) 8 (EVar 32)) ltac:(assumption)) ltac:(ev_start)) as T.
          unfold PB.uv in T. cbn [edenot] in T. rewrite F32 in T. exact T. }
        assert (C280 : u64 M' (V + 264 + 16) (b + capb)).
        { pose proof (PB2.kword64_elim E' M' _ _ (V + 264 + 16) (CELL (KWord (SA (EVar 8) 280) 8 (EAlu ALU_ADD (EVar 32) (EVar 34))) ltac:(assumption)) ltac:(ev_start)) as T.
          replace (PB.uv E' (EAlu ALU_ADD (EVar 32) (EVar 34))) with (b + capb) in T by (unfold PB.uv; symmetry; apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]). exact T. }
        assert (CX0 : u32 M' b 0).
        { pose proof (PB2.kword32_elim E' M' _ _ b (CELL (KWord (SA ctxb_fast 0) 4 (ELit 0)) ltac:(assumption)) ltac:(rewrite CB by lia; lia)) as T.
          unfold PB.uv in T. cbn [edenot] in T. rewrite (u64_of_Z 0) in T by lia. exact T. }
        assert (CX4 : u8 M' (b + 4) 0).
        { pose proof (PB2.kword8_elim E' M' _ _ (b + 4) (CELL (KWord (SA ctxb_fast 4) 1 (ELit 0)) ltac:(assumption)) ltac:(rewrite CB by lia; lia)) as T.
          unfold PB.uv in T. cbn [edenot] in T. rewrite (u64_of_Z 0) in T by lia. exact T. }
        assert (CX6 : u8 M' (b + 6) 0).
        { pose proof (PB2.kword8_elim E' M' _ _ (b + 6) (CELL (KWord (SA ctxb_fast 6) 1 (ELit 0)) ltac:(assumption)) ltac:(rewrite CB by lia; lia)) as T.
          unfold PB.uv in T. cbn [edenot] in T. rewrite (u64_of_Z 0) in T by lia. exact T. }
        assert (CX24 : u64 M' (b + 24) 0).
        { pose proof (PB2.kword64_elim E' M' _ _ (b + 24) (CELL (KWord (SA ctxb_fast 24) 8 (ELit 0)) ltac:(assumption)) ltac:(rewrite CB by lia; lia)) as T.
          unfold PB.uv in T. cbn [edenot] in T. rewrite (u64_of_Z 0) in T by lia. exact T. }
        split; [exact C264|]. split; [exact C280|].
        split; [nia|]. split; [exists kk; lia|]. split; [intros i0 Hi0; cbn in Hi0; lia|].
        replace (b + 32 * 0) with b by lia.
        unfold ctx_at. cbn [ec_arr ec_nla ec_count b2z].
        split; [exact CX0|]. split; [exact CX4|]. split; [exact CX6|]. split; [exact CX24|]. split; [lia|]. intros j0 Hj0. apply Bdef. lia. }
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      left. split; [nia|]. split; [reflexivity|]. split; reflexivity.
    + reflexivity.
    + rewrite LS. split.
      { rewrite regs_fast. apply VBK.regs_ok_updn; [lia| |].
        - apply VBK.regs_ok_updn; [lia| exact (regs_ok_id R _ _) |].
          replace (Z_to_bv 5 (Z.of_nat 9)) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite H9. unfold O_STACK.
          rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. symmetry. apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia].
        - replace (Z_to_bv 5 (Z.of_nat 18)) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite H18. rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. symmetry. unfold ctxb_fast. apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia]. }
      unfold know_ok, F.cp0. cbn [CC.cp_know].
      repeat (apply Forall_cons); [.. | apply Forall_nil]; first
        [ eapply CL5.kword64_intro; [ev_start | lia | lia | | first [exact T1 | exact T2 | exact T3 | exact Hcolu | exact E344]]; rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)); f_equal; try (apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia])
        | eapply PB2.kword8_intro; [ev_start | lia | lia | reflexivity | lia | first [exact E28 | exact E30]]
        | e_range
        | e_align OV3 | e_align SK1 | e_align P2
        | e_unk | e_wr | e_disj
        | idtac ].
      all: fail "entry knowledge left".
    + split; [exact Hmo|]. split; [apply L5C.model_but_vm_refl|]. split; [apply CC.env_agree_refl|].
      split; [|split; [reflexivity | intros a _ _ Hdd; exact Hdd]].
      exists cr. split; [|reflexivity]. unfold CH2.cur. change (nth 0 F.BLS []) with [(EVar 32, EVar 34)]. cbn [CH2.den map app fst snd edenot]. rewrite U32, U34. exact HH0.
    + exact Hfp.
Qed.
End Mid.
End VBM_ORU.
