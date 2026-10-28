(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core StreamSim. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmFloatCSpecs_u Pm10StrtodGSpec_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseBridges_u ParseBridges2_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmSmall Require Import SmallPure SmallCall SmallSums2 SmallInl.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_decstr_to_double_csrc_T_u Cut_decstr_to_double_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module DecstrGProof.
Module G := Cut_decstr_to_double_csrc_u.  Module GT := Cut_decstr_to_double_csrc_T_u.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Definition SCR : Z := CH.hd_scr G.HDECL.
Definition F0 : list SGP.region := CC.cp_F G.cp0.
Definition ERRNO : Z := PML.TP - 164.
Definition FCLASS : Z := Eval vm_compute in hd 0 (List.filter (fun pc => negb (Z.eqb pc PML.PC_STRTOD)) (map (fun r : nat * nat * nat * Z => snd r) G.RETS)).
Definition CALLS : list Z := [PML.PC_STRTOD; FCLASS].
Lemma cut_facts : CC.cps_all G.CPS (fun _ c => SP.cut_chk GT.NF F0 c) = true.
Proof. vmc_refl. Qed.
Lemma exit_facts : CC.others_all G.CPS G.TAGS (fun _ ps id => if SP.is_call CALLS id then true else SP.exit_chk GT.ENDS ps) = true.
Proof. vmc_refl. Qed.
Definition a1_of (x : expr) : expr := EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SLTU x (ELit 1)) (ELit (-1))) (ELit 34).
Definition a1_chk (o : option expr) : bool :=
  match o with Some (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SLTU x _) _) _ as e) => expr_eqb e (a1_of x) | _ => false end.
Definition post_chk (ps : SR.post_spec) : bool := (CL.ps_reg_is ps 10 (APC.eadd (EVar 10) (EVar 11)) && a1_chk (SP.reg_of ps 11))%bool.
Lemma post_facts : CC.others_all G.CPS G.TAGS (fun _ ps id => if SP.is_call CALLS id then true else post_chk ps) = true.
Proof. vmc_refl. Qed.
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition ENDP (ps : SR.post_spec) : expr * Z := split_lit (nth 11 (CA.ps_reglist ps) (ELit 0)).
Definition call_leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto _ _ => true
  | CC.TOther pc =>
      if SP.is_call CALLS pc then
        if negb (Z.eqb (SR.ps_pc ps) pc) then false else
        match CH2.ret_of G.RETS i k with
        | Some j => match nth_error G.CPS j with
                    | Some cj =>
                        let cells := SR.ps_cells ps in
                        if Z.eqb pc PML.PC_STRTOD then
                          let '(eb, ek) := ENDP ps in
                          match SPC.call_chk GT.NF SCR [] PML.STRTOD_SCR_V 0 [(EVar 2, ek, ELit 8); (ELit 0, ERRNO, ELit 4)]
                                  [KWord (SA (EVar 2) ek) 8 (APC.eadd (EVar 10) (EVar 11))] None c ps cj with
                          | Some ci => (Nat.leb GT.NF (CH2.ci_nx ci) && expr_eqb eb (EVar 2) && Z.leb (CH2.ci_csp ci) ek && Z.leb (ek + 8) 0
                                        && expr_eqb (nth 10 (CA.ps_reglist ps) (ELit 0)) (EVar 10)
                                        && forallb (PB.has cells) [KBlob (SA (EVar 10) 0) (EVar 11) 0; KWord (SA (APC.eadd (EVar 10) (EVar 11)) 0) 1 (ELit 0); KImg 0x10000 PML.IMG_RO_HI])%bool
                          | None => false end
                        else SPI.inl_chk c ps cj 4 [10%nat] None
                    | None => false end
        | None => false end
      else true
  end.
Lemma call_facts : CH2.leaves_all G.CPS G.TAGS call_leaf_chk = true.
Proof. vmc_refl. Qed.
Lemma fclass_site : SPI.site_fclass_chk RSEGS FCLASS = Some 10%nat.
Proof. vmc_refl. Qed.
Lemma rets : forall pc, In pc GT.ENDS -> CL.is_ret_at RSEGS pc.
Proof. intros pc [<-|[]]; CL.solve_is_ret. Qed.

Lemma errno_wr : StreamSim.wseg_ok RSEGS (Z_to_bv 64 ERRNO) 4 = true.
Proof. vmc_refl. Qed.

Lemma a1_sound : forall E o, a1_chk o = true -> exists e c, o = Some e /\ bv_unsigned (edenot E e) = c /\ In c [0; 34].
Proof.
  intros E o H. destruct o as [e|]; [|discriminate]. exists e.
  assert (X : exists x, e = a1_of x).
  { destruct e as [| |op1 e1 e2| | | | |]; try discriminate. destruct op1; try discriminate.
    destruct e1 as [| |op2 e3 e4| | | | |]; try discriminate. destruct op2; try discriminate.
    destruct e3 as [| |op3 e5 e6| | | | |]; try discriminate. destruct op3; try discriminate.
    exists e5. cbn [a1_chk] in H. apply expr_eqb_eq in H. exact H. }
  destruct X as (x & ->). unfold a1_of. cbn [edenot]. rewrite u_and64, u_add64, u_sltu64.
  destruct (bv_unsigned (edenot E x) <? bv_unsigned (Z_to_bv 64 1)); [exists 0 | exists 34]; (split; [reflexivity|]); (split; [vm_compute; reflexivity | cbn [In]; tauto]).
Qed.

Section S.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.
Hypothesis STRTOD_OK : STGS.strtod_g_spec L PML.STRTOD_SCR_V.

Theorem decstr_to_double_g_ok : PMFC.decstr_to_double_g_spec L PML.STRTOD_SCR_V.
Proof.
  intros s dp sp r txt fx R M model K Hh Hl HK0 Hfp
         ((Hra & Hraok & Hsp & Htp & Hstk) & Ha0 & Ha1 & Ha2 & IMGRO & Hbytes & Hnul & Hnum & Hlen & Hdefd & Hdp1 & Hdp2 & Hdeft & Hs1 & Hs2 & Hap1 & Hap2) Hcont.
  pose proof (L5C.stk_floor _ _ _ _ Hstk) as FL. pose proof Hstk as (S1 & S2 & S3 & S4 & S5).
  unfold PML.STRTOD_SCR_V in *. change (96 + 8944) with 9040 in *.
  set (len := Z.of_nat (length txt)) in *.
  assert (Hlen0 : 0 <= len) by (unfold len; lia).
  set (E0 := Env (reg_ev R (fun _ => Z_to_bv 64 0)) (fun id => match id with 0%nat => map (Z_to_bv 8) txt | _ => [] end)).
  assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
  assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite (EV 2%bv), Hsp; apply u64_of_Z; lia).
  assert (U10 : bv_unsigned (ev E0 10) = s) by (rewrite (EV 10%bv), Ha0; apply u64_of_Z; lia).
  assert (U11 : bv_unsigned (ev E0 11) = len) by (rewrite (EV 11%bv), Ha1; apply u64_of_Z; lia).
  assert (U12 : bv_unsigned (ev E0 12) = dp) by (rewrite (EV 12%bv), Ha2; apply u64_of_Z; lia).
  assert (TPV : PML.TP - 164 = ERRNO) by reflexivity.
  pose proof Hap2 as Hap2'. unfold PML.TP in Hap2'.
  assert (WE : forall Mx : mem, L5.writable RSEGS Mx ERRNO 4) by (intros Mx; apply (SP.writable_static RSEGS Mx ERRNO 4 errno_wr); unfold ERRNO, PML.TP; lia).
  assert (NF32' : (32 <= GT.NF)%nat) by (unfold GT.NF; lia).
  assert (TP0 : ev E0 4 = Z_to_bv 64 PML.TP) by (rewrite (EV 4%bv); exact Htp).
  assert (SCRV : SCR = 9040) by reflexivity.
  assert (STKF : L5C.stk (hl_sptop L) M sp SCR) by (rewrite SCRV; exact Hstk).
  assert (CRS_OK : forall rg, In rg (@nil SGP.region) -> SGP.region_vars_lt GT.NF rg = true /\ forall a, CH2.in_reg E0 rg a -> a < sp - SCR \/ sp <= a) by (intros rg []).
  unfold PML.cfg. change PML.PC_DECSTR_DOUBLE with (CC.cp_pc G.cp0).
  eapply (SP.pure_fun_sound RSEGS PML.fp_ok FPM G.CPS G.TAGS GT.NF F0 GT.ENDS eq_refl NF32' G.plans G.tags_ok cut_facts rets CALLS exit_facts
            fx R M model K E0 G.cp0 r Hh Hl Hfp EV Hra Hraok eq_refl).
  -
    split; [exact (regs_ok_id R _ _)|]. unfold know_ok, G.cp0. cbn [CC.cp_know].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_range.
    + eapply CL5.kblob_intro with (bs := txt) (A := s); [ev_start | unfold elenZ; cbn [edenot]; rewrite U11; reflexivity | lia | fold len; lia | lia | reflexivity | exact Hbytes | eapply (L5.defined_sub _ _ _ _ _ Hdeft); fold len; lia].
    + eapply PB2.kword8_intro with (A := s + len) (z := 0); [sp_startl (s + len) | lia | lia | reflexivity | lia | exact Hnul].
    + sp_unk Hdeft.
    + sp_unk S5. + sp_wr S5. + e_range. + e_align S1.
    + sp_unk Hdefd. + sp_wr Hdefd. + e_range.
    + eapply (SP.kwr_of_writable RSEGS E0 M _ _ ERRNO 4); [sp_start | ev_len | unfold ERRNO, PML.TP; lia | unfold ERRNO, PML.TP; lia | exact (WE M)].
    + cbn [kentry_ok]. split; [lia | split; [lia | exact IMGRO]].
    + sp_disj. + sp_disj. + sp_disj.
    + eapply CL5.krange_intro with (v := s + len); [lin_eval; rw_atoms; lia | lia | lia].
  -
    intros i c tags k ps0 id Hc Htags Hps Htag Hic.
    assert (IL : CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther id)) by (exists tags; repeat split; assumption).
    pose proof (CH2.leaves_all_sound _ _ _ call_facts _ _ _ _ _ IL) as X. unfold call_leaf_chk in X. rewrite Hic in X.
    destruct (Z.eqb_spec (SR.ps_pc ps0) id) as [Hpc|]; [|discriminate X]. cbn [negb] in X.
    destruct (CH2.ret_of G.RETS i k) as [j|] eqn:Hret; [|discriminate]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate].
    pose proof (SP.SUBF G.CPS GT.NF F0 eq_refl cut_facts E0 i c Hc) as HSUB.
    destruct (Z.eqb_spec id PML.PC_STRTOD) as [->|N1].
    +
      destruct (ENDP ps0) as [eb ek] eqn:Hendp. change PML.STRTOD_SCR_V with 8944 in X. cbv beta iota in X.
      destruct (SPC.call_chk GT.NF SCR [] 8944 0 [(EVar 2, ek, ELit 8); (ELit 0, ERRNO, ELit 4)] [KWord (SA (EVar 2) ek) 8 (APC.eadd (EVar 10) (EVar 11))] None c ps0 cj) as [ci|] eqn:Hchk; [|discriminate].
      apply andb_prop in X as [X Xc]. apply andb_prop in X as [X Xa0]. apply andb_prop in X as [X Xk2]. apply andb_prop in X as [X Xk1]. apply andb_prop in X as [Xnx Xeb].
      apply expr_eqb_eq in Xeb, Xa0. apply Z.leb_le in Xk1, Xk2. apply Nat.leb_le in Xnx. subst eb.
      intros fx' E1 R1 M1 m1 E' R' M' HAt1 HAmb HFP Hag HLF HIH. rewrite Hpc.
      destruct (SPC.pure_call_ret RSEGS PML.fp_ok G.CPS GT.NF E0 M model F0 K sp SCR (hl_sptop L) PML.TP NF32' U2 TP0 STKF ltac:(rewrite SCRV; lia) [] CRS_OK
                  8944 0%nat _ _ _ i c ps0 j cj ci Hcj Hchk HSUB E1 R1 M1 m1 E' R' M' HAt1 HAmb Hag HLF HIH)
        as ((-> & HagE' & HR & HK & Gra & Graok & Gsp & Gtp & Gstk & Gfr & Ggr & _ & Gc1 & Gs0 & Gc2) & CONT).
      set (csp := CH2.ci_csp ci) in *. rewrite SCRV in Gc2.
      assert (A2 : bv_unsigned (ev E' 2) = sp) by (destruct HagE' as [Y _]; rewrite <- (Y 2%nat) by (unfold GT.NF; lia); exact U2).
      assert (A10 : bv_unsigned (ev E' 10) = s) by (destruct HagE' as [Y _]; rewrite <- (Y 10%nat) by (unfold GT.NF; lia); exact U10).
      assert (A11 : bv_unsigned (ev E' 11) = len) by (destruct HagE' as [Y _]; rewrite <- (Y 11%nat) by (unfold GT.NF; lia); exact U11).
      assert (EB' : eb E' 0%nat = map (Z_to_bv 8) txt) by (destruct HagE' as [_ Y]; rewrite <- Y; reflexivity).

      assert (G10 : getr R' 10%bv = Z_to_bv 64 s).
      { rewrite (HR 10%bv). unfold sr_get. change (bv_eqb (10%bv : bv 5) 0) with false. cbv iota. change (ridx 10%bv) with 10%nat. rewrite Xa0. cbn [edenot].
        rewrite <- A10. symmetry. apply Z_to_bv_bv_unsigned. }
      assert (G11 : getr R' 11%bv = Z_to_bv 64 (sp + ek)).
      { rewrite (HR 11%bv). unfold sr_get. change (bv_eqb (11%bv : bv 5) 0) with false. cbv iota. change (ridx 11%bv) with 11%nat.
        rewrite <- (Z_to_bv_bv_unsigned _ (edenot E' _)). f_equal. unfold ENDP in Hendp. rewrite (APS.split_lit_denot E' _ _ _ Hendp). cbn [edenot]. rewrite A2. apply u64_of_Z. lia. }
      rewrite forallb_forall in Xc.
      pose proof (PB.has_ok E' M' _ _ HK (Xc _ ltac:(left; reflexivity))) as KB.
      pose proof (PB.has_ok E' M' _ _ HK (Xc _ ltac:(right; left; reflexivity))) as KZ.
      pose proof (PB.has_ok E' M' _ _ HK (Xc _ ltac:(right; right; left; reflexivity))) as KI.
      assert (ES10 : estart E' (SA (EVar 10) 0) = s) by ev_start.
      assert (ESZ : estart E' (SA (APC.eadd (EVar 10) (EVar 11)) 0) = s + len) by (sp_startl (s + len)).
      destruct (CL5.kblob_elim RSEGS E' M' _ _ _ s txt KB ES10 EB') as [HB' _].
      pose proof (CL5.kword8_zero_elim RSEGS E' M' _ (s + len) KZ ESZ) as HZ'.
      assert (IMG' : PML.img_ro M') by (cbn [kentry_ok] in KI; exact (proj2 (proj2 KI))).
      apply (STRTOD_OK s (sp + ek) (sp + csp) (CC.cp_pc cj) txt fx' R' M' model K Hh Hl HK0 HFP).
      { split; [split; [exact Gra | split; [exact Graok | split; [exact Gsp | split; [exact Gtp | exact Gstk]]]]|].
        split; [exact G10|]. split; [exact G11|]. split; [exact IMG'|]. split; [exact HB'|]. split; [exact HZ'|]. split; [exact Hnum|]. split; [exact Hlen|].
        split; [intros q Hq; apply Ggr; replace (sp + ek + q) with (sp - 9040 + (9040 + ek + q)) by lia; apply S5; lia|]. split; [lia|]. split; [lia|].
        fold len. split; [lia|]. split; [lia|]. split; [exact Hap2|]. split; [intros q Hq; apply Ggr; exact (Hdeft q Hq)|]. split; [exact Hs1 | exact Hs2]. }
      intros fx2 R2 M2 HFP2 P1 Hrp2 Hfb2 Hgr2. unfold PML.cfg. fold len in P1.
      assert (STKIN : In (EVar 2, - SCR, ELit SCR) F0) by (left; reflexivity).
      apply (CONT fx2 R2 M2 [] [(sp + ek, 8); (PML.TP - 164, 4)] eq_refl HFP2 (CH2.regs_preserved_kept R' R2 Hrp2)); [exact I | exact Hfb2 | exact Hgr2 | | |].
      * intros w a [<-|[<-|[]]] Hin; unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
        -- exists (EVar 2, ek, ELit 8). split; [left; reflexivity|]. unfold CH2.in_reg.
           assert (Es : estart E' (SA (EVar 2) ek) = sp + ek) by ev_start. assert (El : elenZ E' (ELit 8) = 8) by ev_len. rewrite Es, El. exact Hin.
        -- exists (ELit 0, ERRNO, ELit 4). split; [right; left; reflexivity|]. unfold CH2.in_reg.
           assert (Es : estart E' (SA (ELit 0) ERRNO) = ERRNO) by sp_start. assert (El : elenZ E' (ELit 4) = 4) by ev_len. rewrite Es, El. rewrite <- TPV. exact Hin.
      * apply (SPC.hwf_intro GT.NF E0 F0 sp SCR NF32' U2 ltac:(rewrite SCRV; lia) csp 8944 _ Gc1 Gs0 ltac:(rewrite SCRV; lia) STKIN ltac:(rewrite SCRV; lia)).
        intros w [<-|[<-|[]]]; cbn [fst snd].
        -- exists (EVar 2), (- SCR), (ELit SCR). split; [left; reflexivity|].
           assert (Es : estart E0 (SA (EVar 2) (- SCR)) = sp - SCR) by (rewrite SCRV; ev_start). assert (El : elenZ E0 (ELit SCR) = SCR) by (rewrite SCRV; ev_len). rewrite Es, El, SCRV. lia.
        -- exists (ELit 0), ERRNO, (ELit 4). split; [right; right; left; reflexivity|].
           assert (Es : estart E0 (SA (ELit 0) ERRNO) = ERRNO) by sp_start. assert (El : elenZ E0 (ELit 4) = 4) by ev_len. rewrite Es, El, <- TPV. lia.
      * intros X0 [<-|[]] _.
        set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2).
        assert (Hag2 : env_agree GT.NF E' E2) by (eapply CC.env_agree_le; [exact (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2) | exact Xnx]).
        assert (B2 : bv_unsigned (ev E2 2) = sp) by (destruct Hag2 as [Y _]; rewrite <- (Y 2%nat) by (unfold GT.NF; lia); exact A2).
        eapply CL5.kword64_intro with (A := sp + ek) (z := s + len); [ev_start | lia | lia | | exact P1].
        apply PB.edenot_of_uv. rewrite (PB.uv_agree GT.NF E' E2 (APC.eadd (EVar 10) (EVar 11)) Hag2 eq_refl). rewrite PB.uv_eadd. unfold PB.uv. cbn [edenot]. rewrite A10, A11. apply Z.mod_small. lia.
    +
      assert (id = FCLASS) as -> by (unfold SP.is_call, CALLS in Hic; cbn [existsb] in Hic; destruct (Z.eqb_spec id PML.PC_STRTOD); [contradiction|]; destruct (Z.eqb_spec id FCLASS); [assumption | discriminate]).
      eapply (SPI.inl_leaf_ok RSEGS G.CPS GT.NF E0 M model F0 K Hh Hl PML.fp_ok i c ps0 j cj 4 [10%nat] Hcj X HSUB (SP.NFle G.CPS GT.NF F0 cut_facts i c Hc)).
      rewrite Hpc. apply SPI.fclass_step; [unfold FCLASS; lia | exact fclass_site].
  -
    intros fx' i c tags k ps0 id E' R' M1 M' Hc Htags Hps Htag Hic HFP HagE HLF Hfr Hgr Hrp.
    pose proof (CC.others_all_sound _ _ _ post_facts i c tags k ps0 id Hc Htags Hps Htag) as X. cbv beta in X. rewrite Hic in X. apply andb_prop in X as [X10 X11].
    apply (Hcont fx' R' M' HFP); [| exact Hrp | | exact Hgr].
    + split.
      * unfold PML.a0. rewrite (SP.reg_is_sound RSEGS _ _ _ _ _ _ 10%bv _ _ HLF X10 eq_refl). apply PB.edenot_of_uv.
        rewrite (PB.uv_agree GT.NF E0 E' (APC.eadd (EVar 10) (EVar 11)) HagE eq_refl). rewrite PB.uv_eadd. unfold PB.uv. cbn [edenot]. rewrite U10, U11. fold len. apply Z.mod_small. lia.
      * destruct (a1_sound E' _ X11) as (e & c0 & He & Hc0 & Hin). exists c0. split; [|exact Hin].
        rewrite (SP.reg_of_sound RSEGS _ _ _ _ _ _ 11%bv _ _ HLF He eq_refl). rewrite <- Hc0. symmetry. apply Z_to_bv_bv_unsigned.
    + apply (SP.frame_but_of_outside E0 F0 _ M M'); [|exact Hfr].
      intros rb rlo rlen Hin. right. unfold F0 in Hin. cbn [G.cp0 CC.cp_F In] in Hin.
      destruct Hin as [X|[X|[X|[]]]]; injection X as <- <- <-.
      * exists (sp - 9040, 9040). split; [left; reflexivity|]. cbn [fst snd]. assert (Es : estart E0 (SA (EVar 2) (-9040)) = sp - 9040) by ev_start. assert (El : elenZ E0 (ELit 9040) = 9040) by ev_len. rewrite Es, El. lia.
      * exists (dp, 8). split; [right; left; reflexivity|]. cbn [fst snd]. assert (Es : estart E0 (SA (EVar 12) 0) = dp) by ev_start. assert (El : elenZ E0 (ELit 8) = 8) by ev_len. rewrite Es, El. lia.
      * exists (PML.TP - 164, 4). split; [right; right; left; reflexivity|]. cbn [fst snd]. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite (u64_of_Z 0), (u64_of_Z 4) by lia. unfold PML.TP. lia.
Qed.
End S.
End DecstrGProof.

