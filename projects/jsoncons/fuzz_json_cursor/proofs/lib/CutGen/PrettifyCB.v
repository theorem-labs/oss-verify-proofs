(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm9PlanKit Pm9L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtB CutShA CutShB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmFloatCSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import PrKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_pr_cboth_T Cut_pr_cboth_D Cut_pr_cboth.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := Cut_pr_cboth_D.  Module GF := Cut_pr_cboth.  Module GT := Cut_pr_cboth_T.
Abbreviation RSEGS := Pm9PlanKit.RSEGS.

Module PRC.
Definition PC_OPNEW : Z := 1363704.
Definition PC_MM : Z := 520748.
Definition RET : Z := 856368.
Definition TJ1 : Z := 856036.
Definition TJ2 : Z := 859532.
Definition PUSHB : Z := 990424.
Definition SBz : Z := 2147450880.
Definition oV : nat := 15.  Definition oE := EVar 15.  Definition bufE := EVar 10.  Definition nbE := EVar 100.
Definition BNEW : list (expr * expr) := [(nbE, ELit 48)].
Definition FFS : list (list (expr * Z * Z)) := map (fun _ => []) G.CPS.
Definition STAT : list kentry := [KImg GT.GLO GT.GHI; KWord (SA (ELit 0) 1432824) 8 (ELit SBz)].
Definition CPF0 : list SGP.region := [(EVar 2, -4496, ELit 4496); (oE, 0, ELit 24)].
Definition CPF1 : list SGP.region := CPF0 ++ [(nbE, 0, ELit 48)].
Definition news_of (nb : nat) (cj : CC.cutpoint) : list kentry := List.filter (fun X => negb (APC.kentry_vars_lt nb X)) (CC.cp_know cj).
Definition isSome {A} (o : option A) : bool := match o with Some _ => true | None => false end.
Definition SHPCS : list Z := [855780; 855888; 856260; 856160; 856492].
Definition blk_of (i : nat) : option expr := match nth i G.BLS [] with [(b, _)] => Some b | _ => None end.
Definition reg_of (ps : SR.post_spec) (r : nat) : option expr := option_map snd (find (fun ie : nat * expr => Nat.eqb (fst ie) r) (SR.ps_regs ps)).
Definition isnil {A} (l : list A) : bool := match l with [] => true | _ => false end.

Definition sh_cur (ps : SR.post_spec) : option expr :=
  match CA.ps_reg ps 10 with EAlu ALU_ADD (EAlu ALU_SRL cur (ELit 3)) (ELit sb) => if Z.eqb sb SBz then Some cur else None | _ => None end.
Definition meas_kv (m : expr) : option (nat * Z) :=
  match m with EAlu ALU_ADD (EMd M_MUL (ELit 64) (EVar kv)) (ELit a) => Some (kv, a) | _ => None end.

Definition IDS (nx : nat) : CC.subst := map (fun v => (v, EVar v)) (seq GT.NF (nx - GT.NF)).
Definition sh_ok (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) (j : nat) : bool :=
  match nth_error G.CPS j, sh_cur ps, meas_kv (CC.cp_meas c) with
  | Some cj, Some cur, Some (kv, a) =>
      match meas_kv (CC.esubstL GT.NF (IDS (CC.cp_nx cj)) (CC.cp_meas cj)) with
      | Some (kv', b) =>
          (Nat.eqb kv kv' && CSL.shl_chk GT.NF c ps cj (IDS (CC.cp_nx cj)) 10 10 (SR.ps_pc ps + 4) cur SBz kv a b
           && CHA.goto_amb_chk GT.NF G.HDECL c (nth i G.BLS []) (nth j G.BLS []) (nth i FFS []) (nth j FFS []) (IDS (CC.cp_nx cj))
           && PRK.cur_ok bufE cur (SR.ps_cells ps) && CC.has_cell (SR.ps_cells ps) (KZero (SA (CHA.SRL3 bufE) SBz) (ELit 3))
           && Bool.eqb (isnil (nth i G.BLS [])) (isnil (nth j G.BLS [])))%bool
      | None => false end
  | _, _, _ => false end.
Definition sh_target (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : option nat := List.find (sh_ok i c ps) (seq 0 (length G.CPS)).

Definition leaf_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  let cells := SR.ps_cells ps in
  match t with
  | CC.TGoto j _ => Bool.eqb (isnil (nth i G.BLS [])) (isnil (nth j G.BLS []))
  | CC.TOther pc =>
      if Z.eqb pc PC_OPNEW then
        match CH2.ret_of G.RETS i k with
        | Some j => match nth_error G.CPS j with
                    | Some cj => let nx := (CC.cp_nx cj - APC.NCS)%nat in let news := news_of (nx + 4) cj in
                        (Z.eqb (SR.ps_pc ps) PC_OPNEW && CH2.blocks_eqb (nth i G.BLS []) [] && CH2.blocks_eqb (nth j G.BLS []) BNEW && Nat.eqb nx 96
                         && CBA.regions_eqb (CC.cp_F c) CPF0
                         && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 4112 0 [] [] [] news None c ps cj [] [] BNEW [])
                         && CRB.fresh_news_ok 65536 7028736 G.HDECL GT.SCELLS GT.GLO GT.GHI cells nx [] [] (nx + 4) (ELit 48) news
                         && CL.ps_reg_is ps 10 (ELit 48))%bool
                    | None => false end
        | None => false end
      else if Z.eqb pc PC_MM then
        match CH2.ret_of G.RETS i k with
        | Some j => match nth_error G.CPS j with
                    | Some cj =>
                        (Z.eqb (SR.ps_pc ps) PC_MM && CH2.blocks_eqb (nth i G.BLS []) BNEW && CH2.blocks_eqb (nth j G.BLS []) BNEW
                         && CBA.regions_eqb (CC.cp_F c) CPF1 && Nat.leb 101 (CC.cp_nx c)
                         && isSome (CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI 2560 0 BNEW [] [(nbE, 0, ELit 22)] STAT (Some nbE) c ps cj BNEW [] BNEW [])
                         && CL.ps_reg_is ps 10 nbE && CL.ps_reg_is ps 11 (EAlu ALU_ADD oE (ELit 1)) && CL.ps_reg_is ps 12 (ELit 22)
                         && CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) [])%bool
                    | None => false end
        | None => false end
      else if Z.eqb pc RET then
        (Z.eqb (SR.ps_pc ps) RET && CBA.exit_base_chk GT.NF RET c ps && CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) [] && Nat.leb GT.NF (CC.cp_nx c)
         && match blk_of i with None => CH2.blocks_eqb (nth i G.BLS []) [] && PRK.short_ok oV cells
                                 | Some b => CH2.blocks_eqb (nth i G.BLS []) [(b, ELit 48)] && PRK.long_ok oV true 23 47 b cells end)%bool
      else if (Z.eqb pc TJ1 || Z.eqb pc TJ2)%bool then
        (Z.eqb (SR.ps_pc ps) pc && CRB.tail_base_chk GT.NF PUSHB c (PRK.ps_at ps PUSHB) && CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) []
         && CL.ps_reg_is ps 10 oE && match reg_of ps 11 with Some e => AP.fact_ok cells (KRange e 0 255) | None => false end
         && match blk_of i with None => CH2.blocks_eqb (nth i G.BLS []) [] && PRK.short_nonul_ok oV cells
                                 | Some b => CH2.blocks_eqb (nth i G.BLS []) [(b, ELit 48)] && PRK.long_ok oV false 23 46 b cells end)%bool
      else if existsb (Z.eqb pc) SHPCS then
        (Z.eqb (SR.ps_pc ps) pc && isSome (CSL1.site_chk1 RSEGS pc) && isSome (sh_target i c ps))%bool
      else false
  end.
Lemma leaf_ok : CH2.leaves_all G.CPS G.TAGS leaf_chk = true.
Proof. vmc_refl. Qed.
Lemma heap_ok : CHA.heap_chkA GT.NF G.HDECL G.BLS FFS G.CPS G.TAGS = true.
Proof. vmc_refl. Qed.
Lemma ret_at : CL.is_ret_at RSEGS RET.
Proof. CL.solve_is_ret. Qed.
Lemma tj1 : PRK.is_j_at RSEGS TJ1 PUSHB.
Proof. PRK.solve_is_j. Qed.
Lemma tj2 : PRK.is_j_at RSEGS TJ2 PUSHB.
Proof. PRK.solve_is_j. Qed.
Lemma sites : forall pc, existsb (Z.eqb pc) SHPCS = true -> CSL1.site_chk1 RSEGS pc = Some (10%nat, 10%nat) /\ 0 <= pc /\ pc + 4 < 2 ^ 64.
Proof.
  intros pc H. unfold SHPCS in H. cbn [existsb] in H.
  repeat (apply orb_prop in H as [H|H]; [apply Z.eqb_eq in H; subst pc; split; [vm_compute; reflexivity | clear; lia]|]). discriminate H.
Qed.
Lemma nx_all : forall i c, nth_error G.CPS i = Some c -> (GT.NF <= CC.cp_nx c)%nat.
Proof.
  intros i c H. assert (F : forallb (fun c => Nat.leb GT.NF (CC.cp_nx c)) G.CPS = true) by vmc_refl.
  rewrite forallb_forall in F. apply Nat.leb_le. apply F. exact (nth_error_In _ _ H).
Qed.
Lemma reg_of_sound : forall segs c ps E' R' (M M' : word -> option byte) r e, CC.leaf_facts segs c ps E' R' M M' -> reg_of ps r = Some e ->
  getr R' (Z_to_bv 5 (Z.of_nat r)) = edenot E' e.
Proof.
  intros segs c ps E' R' M M' r e HLF H. unfold reg_of in H. destruct (find _ _) as [[r' e']|] eqn:Hf; [|discriminate H]. cbn [option_map snd] in H. injection H as ->.
  apply find_some in Hf as [Hin Hr]. cbn [fst] in Hr. apply Nat.eqb_eq in Hr. subst r'. exact (proj2 (CC.lf_regs _ _ _ _ _ _ _ HLF _ _ Hin)).
Qed.
End PRC.

Lemma nth_map_nil : forall {T U : Type} (l : list T) (i : nat), nth i (map (fun _ => @nil U) l) [] = [].
Proof. intros T U l. induction l as [|x l IH]; intros [|i]; cbn [map nth]; try reflexivity. apply IH. Qed.

Lemma regs_ok_upd_same : forall E sr (R : bvmap 5 word) (r : reg) e, regs_ok E sr R -> r <> 0%bv -> edenot E e = getr R r -> regs_ok E (sr_upd sr (ridx r) e) R.
Proof.
  intros E sr R r e H Hr He. pose proof (regs_ok_upd E sr R r (getr R r) e H He) as X.
  assert (B : bv_eqb r 0 = false) by (destruct (bv_eqb r 0) eqn:Hb; [exfalso; apply Hr; apply bv_eq; unfold bv_eqb in Hb; lia | reflexivity]).
  rewrite B in X. intros y. rewrite <- (X y). destruct (bv_eq_dec _ y r) as [->|Hy]; [rewrite getr_same; [reflexivity | exact Hr] | rewrite (getr_other _ _ _ _ Hy); reflexivity].
Qed.

Lemma u_lin_mod : forall E e v, lden E (lin_of e) = v -> bv_unsigned (edenot E e) = v mod 2 ^ 64.
Proof.
  intros E e v H. pose proof (lin_of_sound E e) as [q Hq]. unfold uE in Hq. rewrite H in Hq. pose proof (u64_range (edenot E e)) as Hu. unfold two64 in Hu.
  rewrite Hq, Z_mod_plus_full, Z.mod_small by lia. reflexivity.
Qed.

Section PrettifyOk.
Context {SCFG_P : ScfgP}.
Abbreviation mem := (word -> option byte).
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PMSA.fp_ok fx -> PMSA.fp_ok fx'.
Hypothesis OPNEW_OK : PMSA.opnew_specA L ar HI PRC.PC_OPNEW.
Hypothesis MEMMOVE_LIBC : amemcpy_spec_at L ar SCFG HI PRC.PC_MM false.
Hypothesis PUSH_SHORT : PMFCA.str_push_back_short_specA L ar HI PRC.PUSHB.
Hypothesis PUSH_L48 : PMFCA.str_push_back_l48_specA L ar HI PRC.PUSHB.

Definition hid (P : Prop) : Prop := P.
Ltac ev0 := unfold estart; cbn [a_base a_off edenot]; rw_atoms; clear; lia.

Definition XB (LB : list (Z * Z)) (FF : list fframe) (p n : Z) (M : mem) : Prop :=
  (ablock_range L ar p n /\ blocks_apart p n LB /\ fframes_apart p n FF) /\ L5.defined M p n /\ shadow_blk M p n.

Lemma src_in_fobj : forall LB FF LK cr A (M : mem) V sp scr o q n bs,
  ri_inv HI LB FF LK cr A M V -> CL5A.ainfr FF o 24 -> o mod 8 = 0 -> shadow_zero M o 3 -> 0 <= q -> 0 <= n -> q + n <= 24 ->
  rdn (hl_segs L) M (Z_to_bv 64 (o + q)) (Z.to_nat n) = Some bs ->
  CRC.mem_src L ar LB FF sp scr M (o + q) n bs.
Proof.
  intros LB FF LK cr A M V sp scr o q n bs HH Ofr O8 Osh Hq Hn Hqn Hrd.
  pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH)) as RFx.
  destruct (CL5A.infr_rng L ar LB FF o 24 RFx Ofr ltac:(lia)) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  split; [|split; [lia|split; [|split; [|exact Hrd]]]].
  - intros a Ha. left. unfold shadow_zero in Osh. replace (S a) with (S o + (a - o) / 8).
    + apply Osh. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
    + unfold S. apply Z.mod_divide in O8; [|lia]. destruct O8 as [t ->].
      assert (E1 : a / 8 = (a - t * 8) / 8 + t) by (rewrite <- Z.div_add by lia; f_equal; lia).
      assert (E2 : t * 8 / 8 = t) by (apply Z.div_mul; lia). lia.
  - destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & _). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & _).
    unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI in *. split; [lia|]. split; [lia|]. left. lia.
  - intros i Hi. right. destruct (CL5A.infr_wok L ar LB FF sp scr o 24 (o + q + i) RFx Ofr ltac:(lia)) as (_ & G2 & _). exact (aclientw_client _ _ _ _ _ _ _ G2).
Qed.

Theorem prettify_ok : PMFCA.prettify_specA L ar HI 855636.
Proof.
  intros LB FF LK cr A buf len k o sp r s0. unfold PMSA.cps_asan.
  intros fx R M model K HH Hmo HKnil Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs
         (Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5 & Hlen & Hk & Hdefb & Hb8 & Hbsh & Hbobj & Hstr & Hs0 & Hdefo & (Ofr & O8 & Osh) & Hapart & Hstksh & Hcred) Hcont.
  unfold PMSA.a0, PMSA.a1, PMSA.a2, PMSA.a3, PMFCA.PR_SCR, PMSA.STR_SCR, PMSA.OPNEW_SCR, PMSA.MALLOC_SCR, PMSA.stksh in *. change (128 + (256 + (16 + 4096))) with 4496 in *.

  pose proof (L5A.aly_segs L C LAY) as LS. pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  assert (LYI : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO) by (rewrite ILO, IHI; unfold BIGSHADOW_LO; clear; lia).
  assert (LYR : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L) by (intros a Ha; rewrite ILO, IHI; exact (L5A.aly_ro_img L C LAY a Ha)).
  assert (LYB : segs_below_b (hl_segs L) (hl_img_hi L) = true) by (rewrite LS, IHI; exact L5A.segs_below).
  assert (LYN : wx_segs_nowrap (hl_segs L)) by (rewrite LS; exact L5A.wx_nowrap).
  assert (LYHN : hl_img_lo L <= 65536 /\ 7028736 <= hl_img_hi L) by (rewrite ILO, IHI; clear; lia).
  pose proof (L5A.aly_scr_mem L C LAY) as SCRMEM.

  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH) as WF. pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ WF) as RFx.
  destruct (CHA.rf_ceil _ _ _ _ RFx) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RFx) as (SP1 & SP16). pose proof (CHA.wf_top _ _ _ _ _ _ _ _ WF) as TOP47.
  destruct Hstk as (S1 & S2 & S3 & S4 & S5 & S6).
  destruct (CL5A.infr_rng L ar LB FF o 24 RFx Ofr ltac:(clear; lia)) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  destruct (CL5A.infr_rng L ar LB FF buf 24 RFx Hbobj ltac:(clear; lia)) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
  unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *.
  change (hid (o + 24 <= 2147446784 \/ 17594333495296 <= o)) in O5. change (hid (o + 24 <= hl_img_lo L \/ hl_img_hi L <= o)) in O7.
  change (hid (buf + 24 <= 2147446784 \/ 17594333495296 <= buf)) in B5. change (hid (buf + 24 <= hl_img_lo L \/ hl_img_hi L <= buf)) in B7.
  assert (FSLO : hl_img_hi L <= ar_fs ar).
  { destruct (CHA.rf_fs _ _ _ _ RFx) as ((A0' & _) & _ & [A4|A4]); [|exact A4]. unfold FS_BYTES in A4. rewrite ILO in A4. clear - A0' A4. lia. }
  rewrite IHI in FSLO.
  assert (SHR : forall q n a, 0 <= q -> 0 < n -> q + n <= 2 ^ 47 -> in_shadow_of q n a -> 2147450880 <= a < 17594333495296) by exact CHA.shadow_range.

  set (WW := [(o, 24)] : list L5.range).
  assert (SCRV : CH.hd_scr G.HDECL = 4496) by reflexivity.
  assert (OSHK : forall a, S o <= a < S o + 3 -> CHA.akept L ar LB FF sp (CH.hd_scr G.HDECL) WW a).
  { intros a Ha. pose proof (CL5A.shreg_in_shadow o 3 a O8 ltac:(clear; lia) ltac:(unfold S in Ha; clear - Ha; lia)) as SH. change (8 * 3) with 24 in SH.
    destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr G.HDECL) o 24 a RFx Ofr ltac:(clear; lia) SH) as (G1 & G2 & G3).
    split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2)|]. intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
    pose proof (SHR o 24 a ltac:(clear - O3; lia) ltac:(clear; lia) ltac:(clear - O6; lia) SH) as SRa. unfold hid in O5. clear - Hin SRa O5. lia. }
  assert (DEFO : forall LBx LKx crx Ax (Mx : mem) Vx, ri_inv HI LBx FF LKx crx Ax Mx Vx -> L5.defined Mx o 24).
  { intros LBx LKx crx Ax Mx Vx HHx. destruct Ofr as (f & Hf & F1 & F2). destruct (CHA.wf_frm _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHx) f Hf) as (_ & _ & _ & _ & FD & _).
    intros q Hq. replace (o + q) with (ff_addr f + (o + q - ff_addr f)) by (clear; lia). apply FD. clear - Hq F1 F2. lia. }
  assert (KSTK : forall a, S (sp - 4496) <= a < S (sp - 4496) + (Z.max (ar_sptop ar) (ar_stack_top ar) - (sp - 4496)) / 8 -> CHA.akept L ar LB FF sp (CH.hd_scr G.HDECL) WW a).
  { intros a Ha. assert (AL : (sp - 4496) mod 8 = 0) by (clear - S1; pose proof (Z_div_mod_eq_full sp 16) as D; rewrite S1, Z.add_0_r in D; rewrite D; replace (16 * (sp / 16) - 4496) with ((2 * (sp / 16) - 562) * 8) by lia; apply Z_mod_mult).
    destruct (PTA.stksh_rng ar sp 4496 a ltac:(clear - S2; lia) AL C8 (proj2 SP1) TOP47 ltac:(clear - CL; lia) Ha) as (G1 & G2).
    split; [exact G1|]. split; [right; right; right; right; left; exact G2|]. intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
    unfold in_shadow_of, S, SB in G2. unfold hid in O5. clear - Hin G2 O5 CL. lia. }

  assert (RUN : forall (g : nat -> word) i0 c0, nth_error G.CPS i0 = Some c0 -> CC.cp_pc c0 = 855636 -> nth i0 G.BLS [] = [] ->
                CCA.AtV RSEGS c0 (Env (reg_ev R g) (fun _ => [])) R A M model ->
                srealizes (hl_segs L) SCFG (mkCfg (@mkst fx R (Z_to_bv 64 855636) M (seg_rom (hl_segs L))) model) K).
  { intros g i0 c0 Hc0 Hpc0 Hbl0 HAt0.
    set (E0 := Env (reg_ev R g) (fun _ => [])).
    assert (EV : forall y : reg, ev E0 (ridx y) = getr R y) by (intros y; apply CL5.ev_reg).
    assert (V2 : ev E0 2 = Z_to_bv 64 sp) by (rewrite <- Hsp; exact (EV 2%bv)).
    assert (V4 : ev E0 4 = Z_to_bv 64 (hl_tp L)) by (rewrite <- Htp; exact (EV 4%bv)).
    assert (V10 : ev E0 10 = Z_to_bv 64 buf) by (rewrite <- Ha0; exact (EV 10%bv)).
    assert (V15 : ev E0 15 = Z_to_bv 64 o) by (rewrite <- Ha5; exact (EV 15%bv)).
    assert (U2 : bv_unsigned (ev E0 2) = sp) by (rewrite V2; apply u64_of_Z; clear - S2 S3 SP1 CL; lia).
    assert (U10 : bv_unsigned (ev E0 10) = buf) by (rewrite V10; apply u64_of_Z; clear - B3 B6; lia).
    assert (U15 : bv_unsigned (ev E0 15) = o) by (rewrite V15; apply u64_of_Z; clear - O3 O6; lia).

    assert (STKF : sp mod 16 = 0 /\ ahl_ceil ar + 4096 + CH.hd_scr G.HDECL <= sp /\ sp <= ar_sptop ar) by (rewrite SCRV; split; [exact S1 | clear - S2 S3; lia]).
    assert (SCRP : 0 <= CH.hd_scr G.HDECL) by (rewrite SCRV; clear; lia).
    assert (NF32 : (32 <= GT.NF)%nat) by (unfold GT.NF; clear; lia).
    assert (WOK : forall (w : L5.range) (a : Z), In w WW -> L5.in_rng w a ->
              0 <= a < 2 ^ 64 /\ aclientw L ar LB FF sp (CH.hd_scr G.HDECL) a /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar))).
    { intros w a [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. exact (CL5A.infr_wok L ar LB FF sp _ o 24 a RFx Ofr Hin). }
    assert (WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> exists w : L5.range, In w WW /\ L5.in_rng w a)).
    { intros rg [<-|[]]. split; [vm_compute; reflexivity|]. intros a Ha. unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha.
      rewrite U15 in Ha. rewrite u64_of_Z in Ha by (clear; lia). exists (o, 24). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia]. }
    assert (CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CHA.in_reg E0 rg a -> CHA.sclientA L ar LB FF sp G.HDECL a)).
    { intros rg Hrg. change (CH.hd_crs G.HDECL) with [(EVar 10, 0, ELit 24); (CHA.SRL3 (EVar 10), 2147450880, ELit 3); (CHA.SRL3 (EVar 15), 2147450880, ELit 3)] in Hrg.
      destruct Hrg as [<-|[<-|[<-|[]]]]; (split; [vm_compute; reflexivity|]); intros a Ha.
      - unfold CHA.in_reg, estart, elenZ in Ha. cbn [a_base a_off edenot] in Ha. rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
        destruct (CL5A.infr_wok L ar LB FF sp (CH.hd_scr G.HDECL) buf 24 a RFx Hbobj ltac:(clear - Ha; lia)) as (G1 & G2 & G3).
        split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3].
      - unfold CHA.in_reg in Ha. rewrite CL5A.estart_srl3 in Ha. unfold CL5A.uv, elenZ in Ha. cbn [edenot] in Ha. rewrite U10 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
        pose proof (CL5A.shreg_in_shadow buf 3 a Hb8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia)) as SH. change (8 * 3) with 24 in SH.
        destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr G.HDECL) buf 24 a RFx Hbobj ltac:(clear; lia) SH) as (G1 & G2 & G3).
        split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3].
      - unfold CHA.in_reg in Ha. rewrite CL5A.estart_srl3 in Ha. unfold CL5A.uv, elenZ in Ha. cbn [edenot] in Ha. rewrite U15 in Ha. rewrite u64_of_Z in Ha by (clear; lia).
        pose proof (CL5A.shreg_in_shadow o 3 a O8 ltac:(clear; lia) ltac:(unfold SB; clear - Ha; lia)) as SH. change (8 * 3) with 24 in SH.
        destruct (CL5A.infr_sh_wok L ar LB FF sp (CH.hd_scr G.HDECL) o 24 a RFx Ofr ltac:(clear; lia) SH) as (G1 & G2 & G3).
        split; [exact G1|]. split; [exact (aclientw_client _ _ _ _ _ _ _ G2) | exact G3]. }
    assert (IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a).
    { intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. rewrite ILO, IHI. split; [clear - Ha; lia|]. intros Hs. pose proof (L5A.aly_static_lo L C LAY a Hs). clear - Ha H. lia. }
    assert (DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL)) by (rewrite SCRV; exact S5).
    assert (SCOK : incl GT.SCELLS (asc_cells C) /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) GT.SCELLS).
    { split; [intros y [<-|[]]; apply (L5A.aly_cells L C LAY); left; reflexivity | rewrite IHI; repeat constructor; cbn; clear; lia]. }
    assert (GOTOK : asc_got_lo C <= GT.GLO /\ GT.GHI <= asc_got_hi C /\ 0 <= GT.GLO /\ GT.GHI <= hl_img_hi L).
    { rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI. unfold GT.GLO, GT.GHI. clear. lia. }

    set (Cred := fun (i : nat) (_ : env) (cr1 : credit) => if PRC.isnil (nth i G.BLS []) then cr1 = cr else cr1 = adebit L cr 48).
    set (XI := fun (i : nat) (E : env) (_ : list (Z * Z)) (M1 : mem) (_ : Model) => forall p n, In (p, n) (CH2.den E (nth i G.BLS [])) -> XB LB FF p n M1).

    assert (NOFOOT : forall LBown a, Forall (fun bb => fst bb + snd bb <= 2147446784 \/ 17594333495296 <= fst bb) LBown -> 2147450880 <= a < 17594333495296 ->
                     ~ CHA.afoot_sem sp G.HDECL WW LBown [] a).
    { intros LBown a HF Ha [X|[X|[X|[X|X]]]].
      - rewrite SCRV in X. clear - X Ha S2 CL. lia.
      - destruct X as (w & [<-|[]] & Hin). unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold hid in O5. clear - Hin Ha O5. lia.
      - destruct X as (bb & Hbb & Hin). pose proof (proj1 (Forall_forall _ _) HF bb Hbb) as G0. cbv beta in G0. clear - Hin Ha G0. lia.
      - destruct X as (f & [] & _).
      - destruct X as (f & [] & _). }
    assert (FFSnil : forall i, nth i PRC.FFS [] = []) by (intros i; unfold PRC.FFS; apply nth_map_nil).

    assert (XBT : forall i c ps E E' R1 R' A1 M1 m1 M' m', CHA.foot_chk GT.NF G.HDECL c (nth i G.BLS []) [] = true -> CCA.AtV (hl_segs L) c E R1 A1 M1 m1 ->
                  CHA.aamb L ar HI GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS PRC.FFS Cred 0 i E A1 M1 m1 -> env_agree (CC.cp_nx c) E E' ->
                  CCA.leaf_factsA (hl_segs L) c ps E' R' A1 M1 m1 M' m' -> XI i E A1 M1 m1 -> XI i E A1 M' m').
    { intros i c ps E E' R1 R' A1 M1 m1 M' m' Hfoot HAt HA Hag HLF HXI q n Hin. destruct (HXI q n Hin) as (HAF & HD & HSB). split; [exact HAF|]. split.
      - intros x Hx. apply (CCA.lfa_grows _ _ _ _ _ _ _ _ _ _ HLF). exact (HD x Hx).
      - pose proof HAF as ((Q0 & Q1 & Q16 & Q3 & Q4 & (Q5 & Q6 & Q7)) & _ & _).
        apply (PTA.shadow_blk_ag M1 M' (fun a => in_shadow_of q n a)); [| clear - Q3; lia | intros a Ha; exact Ha | exact (CHA.mod8_of_16 _ Q16) | exact HSB]. intros a Ha.
        pose proof (SHR q n a ltac:(clear - Q0; lia) Q3 Q7 Ha) as SRa.
        refine (CBA.leaf_frame L ar C HI HIok GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS PRC.FFS Cred 0 STKF SCRP NF32 U2 WRS_OK
                  i c ps E E' R1 R' A1 M1 m1 M' m' _ HAt HA Hag HLF a ltac:(clear - SRa; lia) _); [rewrite FFSnil; exact Hfoot|].
        rewrite FFSnil. apply (NOFOOT _ a); [| exact SRa]. apply Forall_forall. intros [q' n'] Hq'. destruct (HXI q' n' Hq') as (((R0 & R1' & R16 & R3' & R4' & (R5' & R6' & R7')) & _ & _) & _ & _).
        cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI in R6'. clear - R6'. lia. }
    assert (DEN : forall E, CH2.den E PRC.BNEW = [(CL5A.uv E PRC.nbE, 48)]).
    { intros E. unfold CH2.den, PRC.BNEW, PRC.nbE, CL5A.uv. cbn [map fst snd edenot]. rewrite (u64_of_Z 48) by (clear; lia). reflexivity. }
    assert (XGEN : forall i c ps j s E R1 E' R' A1 M1 m1 M' m',
              CHA.goto_amb_chk GT.NF G.HDECL c (nth i G.BLS []) (nth j G.BLS []) (nth i PRC.FFS []) (nth j PRC.FFS []) s = true ->
              CCA.AtV (hl_segs L) c E R1 A1 M1 m1 -> CHA.aamb L ar HI GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS PRC.FFS Cred 0 i E A1 M1 m1 ->
              env_agree (CC.cp_nx c) E E' -> CCA.leaf_factsA (hl_segs L) c ps E' R' A1 M1 m1 M' m' -> XI i E A1 M1 m1 -> XI j (CC.env_over GT.NF s E') A1 M' m').
    { intros i c ps j s E R1 E' R' A1 M1 m1 M' m' X HAt HA Hag HLF HXI q n Hin. unfold CHA.goto_amb_chk in X.
      apply andb_prop in X as [X _]. apply andb_prop in X as [Hfoot Hbe]. apply CH2.blocks_eqb_eq in Hbe.
      rewrite <- CH2.den_bsubst, Hbe in Hin.
      pose proof Hfoot as Hfoot'. unfold CHA.foot_chk in Hfoot'. apply andb_prop in Hfoot' as [Hfoot' _]. apply andb_prop in Hfoot' as [Hfoot' _]. apply andb_prop in Hfoot' as [_ Hbv].
      rewrite (CH2.den_agree _ E E' _ Hag Hbv) in Hin.
      rewrite FFSnil in Hfoot. exact (XBT i c ps E E' R1 R' A1 M1 m1 M' m' Hfoot HAt HA Hag HLF HXI q n Hin). }
    assert (IFB : forall (b x y : bool), (if b then x else y) = true -> (b = true /\ x = true) \/ (b = false /\ y = true)) by (intros [] x y H; [left|right]; split; auto).
    rewrite <- LS in FPM. unfold PMSA.cfg. rewrite <- Hpc0.
    eapply (CHA.cert_soundA L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS PRC.FFS Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
              G.CPS K PMSA.fp_ok XI G.TAGS) with (i := i0) (E := E0).
    - exact FPM.
    - rewrite LS. exact GF.plans.
    - exact GF.tags_ok.
    - exact PRC.heap_ok.
    -
      intros i c kk ps0 j sg HIL E E' R' M1 M' cr1 _ _ _ HC. pose proof (CH2.leaves_all_sound _ _ _ PRC.leaf_ok _ _ _ _ _ HIL) as X. cbv beta iota in X.
      unfold Cred in *. apply Bool.eqb_prop in X. rewrite <- X. exact HC.
    -
      intros i c kk ps0 j sg HIL E R1 E' R' A1 M1 m1 M' m' HAt HA Hag HLF HXI q n Hin.
      pose proof (CH2.leaves_all_sound _ _ _ PRC.heap_ok _ _ _ _ _ HIL) as X. cbv beta iota in X. unfold CHA.goto_amb_chk in X.
      apply andb_prop in X as [X _]. apply andb_prop in X as [Hfoot Hbe]. apply CH2.blocks_eqb_eq in Hbe.
      rewrite <- CH2.den_bsubst, Hbe in Hin.
      pose proof Hfoot as Hfoot'. unfold CHA.foot_chk in Hfoot'. apply andb_prop in Hfoot' as [Hfoot' _]. apply andb_prop in Hfoot' as [Hfoot' _]. apply andb_prop in Hfoot' as [_ Hbv].
      rewrite (CH2.den_agree _ E E' _ Hag Hbv) in Hin.
      rewrite FFSnil in Hfoot. exact (XBT i c ps0 E E' R1 R' A1 M1 m1 M' m' Hfoot HAt HA Hag HLF HXI q n Hin).
    -
      intros i c kk ps0 pc HIL. pose proof (CH2.leaves_all_sound _ _ _ PRC.leaf_ok _ _ _ _ _ HIL) as X. unfold PRC.leaf_chk in X. cbv beta iota zeta in X.
      pose proof (CBA.callee_leaf L ar C HI HIok LYI LYR GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS PRC.FFS Cred 0 STKF SCRP NF32 U2 V4 (incl_refl _) WOK Hffrs CRS_OK WRS_OK IMG_OK
                    G.CPS K PMSA.fp_ok DEF0 S6 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK XI HKnil) as CALLEE.
      assert (Hci : nth_error G.CPS i = Some c) by (destruct HIL as (tg & Hc & _); exact Hc).
      pose proof (PRC.nx_all i c Hci) as NXc.
      apply IFB in X as [[Ep X]|[Ep X]].
      {
        apply Z.eqb_eq in Ep. subst pc.
        destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret; [|discriminate X].
        destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate X].
        set (nx := (CC.cp_nx cj - APC.NCS)%nat) in *. set (news := PRC.news_of (nx + 4) cj) in *.
        apply andb_prop in X as [X Y10]. apply andb_prop in X as [X YNEWS]. apply andb_prop in X as [X Y5]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X YN].
        apply andb_prop in X as [X YBj]. apply andb_prop in X as [Y0 YBi]. apply Z.eqb_eq in Y0. apply Nat.eqb_eq in YN. apply CH2.blocks_eqb_eq in YBi, YBj.
        lazymatch type of Y5 with PRC.isSome ?tm = true => destruct tm as [ci|] eqn:Hchk; [|discriminate] end. clear Y5.
        intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi].
        assert (HcB : CHA.curB LB G.BLS i E = LB) by (unfold CHA.curB; rewrite YBi; reflexivity).
        assert (HcF : CHA.curF FF sp PRC.FFS i E = FF) by (unfold CHA.curF; rewrite FFSnil; reflexivity).
        refine (CALLEE PRC.PC_OPNEW 4112 0%nat [] [] news None 0 i c ps0 j cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
          [rewrite !FFSnil, YBi, YBj; exact Hchk | rewrite !FFSnil; reflexivity | rewrite FFSnil; cbn [length Z.of_nat]; clear; lia |].
        rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
        destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP & Hc1 & Hsz0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
        assert (Hcr1 : cr1 = cr) by (unfold Cred in HC1; rewrite YBi in HC1; exact HC1). subst cr1.
        assert (NXeq : CH2.ci_nx ci = 96%nat) by (destruct HV as (_ & _ & _ & _ & HV5); clear - HV5 YN; unfold nx, APC.NCS in *; lia).
        pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
        assert (REG : forall (q : nat) (e : expr) (z : Z), CL.ps_reg_is ps0 q e = true -> CL5A.uv E' e = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z).
        { intros q e z Hq Hz. rewrite (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ q _ HLFv Hq). rewrite <- Hz. symmetry. apply Z_to_bv_bv_unsigned. }
        eexists. eexists. split; [exact (OPNEW_OK LB FF LK1 cr A1 48 (sp + CH2.ci_csp ci) (CC.cp_pc cj))|].
        split; [split; [exact (REG 10%nat (ELit 48) 48 Y10 ltac:(unfold CL5A.uv; cbn [edenot]; apply u64_of_Z; clear; lia)) | split; [clear; lia | exact Hcred]]|].
        intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (u & Hu & Hfresh & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
        pose proof Hfresh as (Hrng & Hbap & Hfap & Hdef & Hsh). pose proof Hrng as (NQ0 & NQ1 & NQ16 & NQ3 & NQ4 & (NQ5 & NQ6 & NQ7)).
        exists []. split; [reflexivity|]. cbv zeta. split; [exact I|].
        pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
        set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
        assert (UR : 0 <= u < 2 ^ 64) by (clear - NQ5 NQ7 NQ3; lia).
        assert (Hvu : CL5A.uv E2 PRC.nbE = u).
        { unfold CL5A.uv, PRC.nbE. cbn [edenot]. pose proof (CH2.retEx_a0 E' (CH2.ci_nx ci) [] R2) as G0. cbn [length] in G0. rewrite Nat.add_0_r in G0.
          unfold E2. rewrite NXeq in G0 |- *. change (96 + 4)%nat with 100%nat in G0. unfold PMSA.a0 in Hu. rewrite G0, Hu. apply u64_of_Z. exact UR. }
        split; [apply incl_refl|]. split; [intros w a []|]. split; [intros w a []|].
        assert (HBj : CHA.curB LB G.BLS j E2 = (u, 48) :: LB) by (unfold CHA.curB; rewrite YBj, (DEN E2), Hvu; reflexivity).
        split; [rewrite HBj; exact HH2|]. split; [unfold Cred; rewrite YBj; reflexivity|].
        split; [intros q n Hin; rewrite YBj, (DEN E2), Hvu in Hin; destruct Hin as [Hin|[]]; injection Hin as <- <-;
                split; [split; [exact Hrng | split; [exact Hbap | exact Hfap]] | split; [exact Hdef | exact Hsh]]|].
        intros X0 HX0 _.
        refine (CRB.news_sound L ar C HI HIok LYI 65536 7028736 LYHN GT.NF E0 LB FF sp G.HDECL WW STKF SCRP NF32 U2 WOK CRS_OK WRS_OK GT.SCELLS GT.GLO GT.GHI SCOK GOTOK
                  E' E2 (CH2.ci_nx ci) (SR.ps_cells ps0) [] [] 100%nat (ELit 48) M' M2 A1 A2 m' m2 LB ((u, 48) :: LB) FF FF LK1 LK2 cr (adebit L cr 48) u 48 news
                  HagE' Hag2 HK HH1 _ eq_refl Hvu _ _ Hrng Hbap Hfap Hdef Hsh HH2 (or_introl eq_refl) _ X0 HX0);
          [reflexivity | rewrite NXeq; reflexivity | unfold elenZ; cbn [edenot]; apply u64_of_Z; clear; lia | rewrite NXeq; rewrite YN in YNEWS; exact YNEWS]. }
      apply IFB in X as [[Ep2 X]|[Ep2 X]].
      {
        apply Z.eqb_eq in Ep2. subst pc.
        destruct (CH2.ret_of G.RETS i kk) as [j|] eqn:Hret; [|discriminate X].
        destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate X].
        apply andb_prop in X as [X Xfoot]. apply andb_prop in X as [X Y12]. apply andb_prop in X as [X Y11]. apply andb_prop in X as [X Y10]. apply andb_prop in X as [X Y5].
        apply andb_prop in X as [X Ynx]. apply andb_prop in X as [X YF]. apply andb_prop in X as [X YBj]. apply andb_prop in X as [Y0 YBi].
        apply Z.eqb_eq in Y0. apply Nat.leb_le in Ynx. apply CH2.blocks_eqb_eq in YBi, YBj.
        lazymatch type of Y5 with PRC.isSome ?tm = true => destruct tm as [ci|] eqn:Hchk; [|discriminate] end. clear Y5.
        intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXi].
        pose proof (XBT i c ps0 E E' R1 R' A1 M1 m1 M' m' Xfoot HAt HA Hag HLF HXi) as HXi'.
        set (nb := CL5A.uv E PRC.nbE) in *.
        destruct (HXi' nb 48 ltac:(rewrite YBi, DEN; left; reflexivity)) as (HAFP & HDF' & HSB').
        pose proof HAFP as (Hrng & Hbap & Hfap). pose proof Hrng as (Q0 & Q1 & Q16 & Q3 & Q4 & (Q5 & Q6 & Q7)). unfold BIGSHADOW_LO, BIGSHADOW_HI in Q6.
        assert (HcB : CHA.curB LB G.BLS i E = (nb, 48) :: LB) by (unfold CHA.curB; rewrite YBi, (DEN E); reflexivity).
        assert (HcF : CHA.curF FF sp PRC.FFS i E = FF) by (unfold CHA.curF; rewrite FFSnil; reflexivity).
        refine (CALLEE PRC.PC_MM 2560 0%nat PRC.BNEW [(PRC.nbE, 0, ELit 22)] PRC.STAT (Some PRC.nbE) 0 i c ps0 j cj ci Hcj _ Y0 _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _);
          [rewrite !FFSnil, YBi, YBj; exact Hchk | rewrite !FFSnil; reflexivity | rewrite FFSnil; cbn [length Z.of_nat]; clear; lia |].
        rewrite HcB, HcF. intros cr1 LK1 CF HH1 HLK1 HC1.
        destruct CF as [HA' HR Hreq HV HK [HRA HRAok] (HSP0 & Hc1 & Hsz0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
        assert (Hcr1 : cr1 = adebit L cr 48) by (unfold Cred in HC1; rewrite YBi in HC1; exact HC1). subst cr1.
        assert (W15 : bv_unsigned (ev E' 15) = o) by (rewrite <- (proj1 HagE' 15%nat) by (apply Nat.ltb_lt; reflexivity); exact U15).
        assert (NB' : CL5A.uv E' PRC.nbE = nb) by (unfold nb, CL5A.uv, PRC.nbE; cbn [edenot]; rewrite <- (proj1 Hag 100%nat) by (clear - Ynx; lia); reflexivity).
        assert (W100 : bv_unsigned (ev E' 100) = nb) by (unfold CL5A.uv, PRC.nbE in NB'; cbn [edenot] in NB'; exact NB').
        pose proof HA' as (_ & _ & _ & _ & _ & Hfr1 & _).
        assert (OSH' : shadow_zero M' o 3).
        { apply (CL5A.shadow_zero_same M M'); [|exact Osh]. intros j0 Hj0. exact (Hfr1 (S o + j0) (OSHK (S o + j0) ltac:(clear - Hj0; lia))). }
        assert (REG : forall (q : nat) (e : expr) (z : Z), CL.ps_reg_is ps0 q e = true -> bv_unsigned (edenot E' e) = z -> getr R' (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z).
        { intros q e z Hq Hz. rewrite (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ q _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) Hq). rewrite <- Hz. symmetry. apply Z_to_bv_bv_unsigned. }
        destruct (PRK.bytes_of_defined (hl_segs L) M' 22 (o + 1) ltac:(clear - O3; lia) ltac:(clear - O6; lia)
                    ltac:(apply (L5.defined_sub _ o 24 (o + 1) _ (DEFO _ _ _ _ _ _ HH1)); clear; lia)) as (s & Hls & Hbs).
        assert (LENST : length s = Z.to_nat 22) by (rewrite Hls; reflexivity).
        eexists. eexists. split.
        { exact (CRC.memcpy_cps L ar HI PMSA.fp_ok PRC.PC_MM MEMMOVE_LIBC 2560 ((nb, 48) :: LB) FF LK1 (adebit L cr 48) A1 nb (o + 1) 22 (map (Z_to_bv 8) s) (sp + CH2.ci_csp ci) (CC.cp_pc cj)
                   ltac:(rewrite SCRMEM; clear; lia)). }
        split.
        { unfold CRC.memcpy_pre.
          split; [exact (REG 10%nat _ nb Y10 NB')|].
          split; [exact (REG 11%nat _ (o + 1) Y11 ltac:(apply CL5.u_lin; [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia]))|].
          split; [exact (REG 12%nat _ 22 Y12 ltac:(cbn [edenot]; apply u64_of_Z; clear; lia))|].
          split; [exact (CRC.dst_in_block L ar C HI HIok _ FF LK1 _ A1 M' _ (sp + CH2.ci_csp ci) 2560 nb 48 nb 22 HH1 (or_introl eq_refl) HSB' ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia))|].
          split.
          - refine (src_in_fobj _ FF LK1 _ A1 M' _ (sp + CH2.ci_csp ci) 2560 o 1 22 (map (Z_to_bv 8) s) HH1 Ofr O8 OSH' ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) _).
            rewrite <- LENST. apply (L5C.bytes_at_rdn (hl_segs L) M' s (o + 1) ltac:(clear - O3; lia) ltac:(rewrite Hls; clear - O6; lia)). exact Hbs.
          - destruct Ofr as (f & Hf & F1 & F2). pose proof (Hfap f Hf) as AP. clear - AP F1 F2. lia. }
        {
          intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (Ha0' & Hnew & -> & -> & -> & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
          exists []. split; [reflexivity|]. cbv zeta.
          pose proof (CH2.retEx_agree E' (CH2.ci_nx ci) [] R2 : env_agree (CH2.ci_nx ci) E' (CH2.retEx E' (CH2.ci_nx ci) [] R2)) as Hag2.
          set (E2 := CH2.retEx E' (CH2.ci_nx ci) [] R2) in *.
          assert (NB2 : CL5A.uv E2 PRC.nbE = nb) by (unfold CL5A.uv, PRC.nbE; cbn [edenot]; rewrite <- (proj1 Hag2 100%nat) by (destruct HV as (_ & _ & HV3 & _); clear - HV3 Ynx; lia); exact W100).
          assert (T100 : bv_unsigned (ev E2 100) = nb) by (unfold CL5A.uv, PRC.nbE in NB2; cbn [edenot] in NB2; exact NB2).
          split; [unfold PRC.nbE; cbn [edenot]; rewrite Ha0', <- T100; apply Z_to_bv_bv_unsigned|].
          split; [rewrite (DEN E'), NB'; apply incl_refl|].
          split.
          { intros w a [<-|[]] Hin. exists (PRC.nbE, 0, ELit 22). split; [left; reflexivity|]. unfold CHA.in_reg, estart, elenZ. cbn [a_base a_off].
            change (bv_unsigned (edenot E' PRC.nbE)) with (CL5A.uv E' PRC.nbE). rewrite NB'.
            cbn [edenot]. rewrite u64_of_Z by (clear; lia). unfold L5.in_rng in Hin. cbn [fst snd] in Hin. clear - Hin. lia. }
          split.
          { intros w a [<-|[]] Hin (Ka & Kc & _). unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
            refine (CHA.obj_not_client L ar LYI LB FF sp (CH.hd_scr G.HDECL) nb 48 a RFx (conj Q5 (conj Q6 Q7)) ltac:(clear; lia) (CHA.mod8_of_16 _ Q16) Q4 Q1 _ Hfap (or_introl _) Kc).
            - exact Hbap.
            - clear - Hin. lia. }
          split; [unfold CHA.curB; rewrite YBj, (DEN E2), NB2; exact HH2|].
          split; [unfold Cred; rewrite YBj; reflexivity|].
          pose proof HP as (HP1 & HP2 & HP3).
          split.
          { intros q n Hin. rewrite YBj, (DEN E2), NB2 in Hin. destruct Hin as [Hin|[]]. injection Hin as <- <-. split; [exact HAFP|]. split.
            - intros q Hq. apply (HP3 (nb + q)); [clear - Hq Q0 Q7; lia | left; exists (nb, 48); split; [left; reflexivity | cbn [fst snd]; clear - Hq; lia] |].
              exact (HDF' q Hq).
            - apply (PTA.shadow_blk_ag M' M2 (fun a => in_shadow_of nb 48 a)); [| clear; lia | intros a Ha; exact Ha | exact (CHA.mod8_of_16 _ Q16) | exact HSB'].
              intros a Ha. pose proof (SHR nb 48 a ltac:(clear - Q0; lia) ltac:(clear; lia) Q7 Ha) as SRa.
              apply HP1. split; [clear - SRa; lia|]. split; [do 6 right; exists (nb, 48); split; [left; reflexivity | exact Ha]|].
              intros w [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. clear - Hin SRa Q6. lia. }
          intros X0 HX0 _. unfold PRC.STAT in HX0. cbn [In] in HX0.
          destruct HX0 as [<-|[<-|[]]]; apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 NF32 GT.SCELLS GT.GLO GT.GHI SCOK GOTOK _ _ _ _ _ _ _ E2 _ HH2); reflexivity. } }
      apply IFB in X as [[Ep3 X]|[Ep3 X]].
      {
        apply Z.eqb_eq in Ep3. subst pc.
        apply andb_prop in X as [X YS]. apply andb_prop in X as [X Ynx]. apply andb_prop in X as [X Xfoot]. apply andb_prop in X as [Ypc Xbase].
        intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA HXi].
        pose proof (XBT i c ps0 E E' R1 R' A1 M1 m1 M' m' Xfoot HAt HA Hag HLF HXi) as HXi'.
        refine (CBA.exit_ret L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS PRC.FFS Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK
                  K DEF0 R r EV Hra Hraok PRC.RET i c ps0 _ Xbase _ (FFSnil i) fx' E R1 A1 M1 m1 E' R' M' m' HAt HA Hag HLF _);
          [rewrite LS; exact PRC.ret_at | rewrite FFSnil; exact Xfoot |].
        intros model2 cr1 LK1 HRP HP Hrt HA0 Hmo2 HLK1 HH1 HC1 HagE' HA'.
        assert (W15 : bv_unsigned (ev E' 15) = o) by (rewrite <- (proj1 HagE' 15%nat) by (apply Nat.ltb_lt; reflexivity); exact U15).
        pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS PRC.FFS Cred 0 i E A1 M' m' HA') as Hoff.
        assert (KN : know_ok (hl_segs L) E' (CCA.vis A1 m' M') (SR.ps_cells ps0)).
        { apply Forall_forall. intros X0 HX0. exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HX0). }
        pose proof (DEFO _ _ _ _ _ _ HH1) as DO'.
        rewrite SCRV in HP.
        destruct (PRC.blk_of i) as [b|] eqn:Hbk.
        -
          apply andb_prop in YS as [YB YS]. apply CH2.blocks_eqb_eq in YB.
          assert (Hcr1 : cr1 = adebit L cr 48) by (unfold Cred in HC1; rewrite YB in HC1; exact HC1). subst cr1.
          set (p := CL5A.uv E b).
          assert (DENi : CH2.den E (nth i G.BLS []) = [(p, 48)]) by (rewrite YB; unfold CH2.den; cbn [map fst snd edenot]; rewrite (u64_of_Z 48) by (clear; lia); reflexivity).
          assert (HB : CHA.curB LB G.BLS i E = (p, 48) :: LB) by (unfold CHA.curB; rewrite DENi; reflexivity). rewrite HB in HH1.
          destruct (HXi' p 48 ltac:(rewrite DENi; left; reflexivity)) as (HAFP & HDF & HSB).
          pose proof HAFP as (Hrng & Hbap & Hfap). pose proof Hrng as (Q0 & Q1 & Q16 & Q3 & Q4 & (Q5 & Q6 & Q7)).
          assert (Pb : CL5A.uv E' b = p).
          { pose proof Xfoot as Xf. unfold CHA.foot_chk in Xf. apply andb_prop in Xf as [Xf _]. apply andb_prop in Xf as [Xf _]. apply andb_prop in Xf as [_ Hbv].
            pose proof (CH2.den_agree _ E E' _ Hag Hbv) as DA. rewrite YB in DA. unfold CH2.den in DA. cbn [map fst snd] in DA. injection DA as DA. exact DA. }
          destruct (PRK.long_ok_sound (hl_segs L) PRC.oV true 23 47 E' _ b _ o YS KN W15 ltac:(clear - O3; lia) ltac:(clear - O6; lia)
                      ltac:(change (bv_unsigned (edenot E' b)) with (CL5A.uv E' b); rewrite Pb; clear - Q0 Q7; lia) ltac:(clear; lia) ltac:(clear; lia)) as (Sz & HSz & Hw0 & Hw8 & Hw16 & Hnul).
          change (bv_unsigned (edenot E' b)) with (CL5A.uv E' b) in Hw16, Hnul. rewrite Pb in Hw16, Hnul. specialize (Hnul eq_refl).
          destruct (PRK.bytes_of_defined (hl_segs L) M' (Z.to_nat Sz) p ltac:(clear - Q0; lia) ltac:(clear - Q0 Q7 HSz; lia)
                      ltac:(apply (L5.defined_sub _ p 48 p _ HDF); clear - HSz; lia)) as (s' & Hls & Hbs).
          assert (LS' : Z.of_nat (length s') = Sz) by (rewrite Hls; clear - HSz; lia).
          apply (Hcont fx' R' M' model2 ((p, 48) :: LB) (adebit L cr 48) LB WW LK1 A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
          split; [|split; reflexivity]. exists s'. split; [clear - LS' HSz; lia|]. right. exists p. split; [clear - LS' HSz; lia|]. split.
          { unfold PMLA.str_at, L5.lstr_long. rewrite LS'. split; [|split; [reflexivity | clear - HSz; lia]].
            split; [reflexivity|]. split; [exact (CL5A.u64_full (hl_segs L) _ Hoff _ _ _ Hw0)|]. split; [exact (CL5A.u64_full (hl_segs L) _ Hoff _ _ _ Hw8)|].
            split; [exact (CL5A.u64_full (hl_segs L) _ Hoff _ _ _ Hw16)|]. split; [exact Hbs | exact (CL5A.u8_full (hl_segs L) _ Hoff _ _ _ Hnul)]. }
          split; [exact DO'|]. split; [split; [exact Hrng | split; [exact Hbap | split; [exact Hfap | split; [exact HDF | exact HSB]]]]|]. split; reflexivity.
        -
          apply andb_prop in YS as [YB YS]. apply CH2.blocks_eqb_eq in YB.
          assert (Hcr1 : cr1 = cr) by (unfold Cred in HC1; rewrite YB in HC1; exact HC1). subst cr1.
          assert (HB : CHA.curB LB G.BLS i E = LB) by (unfold CHA.curB; rewrite YB; reflexivity). rewrite HB in HH1.
          destruct (PRK.short_ok_sound (hl_segs L) PRC.oV E' _ _ o YS KN W15 ltac:(clear - O3; lia) ltac:(clear - O6; lia)) as (h & Hh & Hb0 & Hnul).
          destruct (PRK.bytes_of_defined (hl_segs L) M' (Z.to_nat h) (o + 1) ltac:(clear - O3; lia) ltac:(clear - O6 Hh; lia)
                      ltac:(apply (L5.defined_sub _ o 24 (o + 1) _ DO'); clear - Hh; lia)) as (s' & Hls & Hbs).
          assert (LS' : Z.of_nat (length s') = h) by (rewrite Hls; clear - Hh; lia).
          apply (Hcont fx' R' M' model2 LB cr LB WW LK1 A1 HFP); [| exact HRP | exact HP | exact Hrt | exact HA0 | exact Hmo2 | exact HLK1 | exact HH1].
          split; [|split; reflexivity]. exists s'. split; [clear - LS' Hh; lia|]. left. split; [clear - LS' Hh; lia|]. split.
          { unfold PMLA.str_at, L5.lstr_short. rewrite LS'. split; [clear - LS' Hh; lia|]. split; [exact (CL5A.u8_full (hl_segs L) _ Hoff _ _ _ Hb0)|].
            split; [exact Hbs | exact (CL5A.u8_full (hl_segs L) _ Hoff _ _ _ Hnul)]. }
          split; [exact DO'|]. split; reflexivity. }
      apply IFB in X as [[Ep4 X]|[Ep4 X]].
      {
        apply andb_prop in X as [X YS]. apply andb_prop in X as [X Y11]. apply andb_prop in X as [X Y10]. apply andb_prop in X as [X Xfoot]. apply andb_prop in X as [X Xtail].
        apply Z.eqb_eq in X. rename X into Ypc.
        assert (HJ : PRK.is_j_at (hl_segs L) pc PRC.PUSHB) by (rewrite LS; apply orb_prop in Ep4 as [H|H]; apply Z.eqb_eq in H; subst pc; [exact PRC.tj1 | exact PRC.tj2]).
        assert (Hpcr : 0 <= pc < 2 ^ 64) by (apply orb_prop in Ep4 as [H|H]; apply Z.eqb_eq in H; subst pc; unfold PRC.TJ1, PRC.TJ2; clear; lia).
        intros fx' E R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF _. pose proof HAX as [HA HXi].
        pose proof (XBT i c ps0 E E' R1 R' A1 M1 m1 M' m' Xfoot HAt HA Hag HLF HXi) as HXi'.
        refine (PRK.tailj_leaf L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS PRC.FFS Cred 0 STKF SCRP NF32 U2 V4 (incl_refl _) WOK Hffrs WRS_OK
                  K PMSA.fp_ok DEF0 S6 HKnil R r EV Hra Hraok pc PRC.PUSHB PMSA.STR_SCR 0 i c ps0 HJ Ypc Hpcr Xtail _ (FFSnil i) _ _ fx' E R1 A1 M1 m1 E' R' M' m' HAt HA HFP Hag HLF _);
          [rewrite FFSnil; exact Xfoot | rewrite SCRV; unfold PMSA.STR_SCR, PMSA.OPNEW_SCR, PMSA.MALLOC_SCR; clear; lia | clear; lia |].
        intros cr1 LK1 HRP HP HH1 HLK1 HC1 HagE' HA'.
        assert (W15 : bv_unsigned (ev E' 15) = o) by (rewrite <- (proj1 HagE' 15%nat) by (apply Nat.ltb_lt; reflexivity); exact U15).
        pose proof (CBA.amb_off L ar C HI HIok LYB GT.NF E0 M model A LB FF LK sp G.HDECL WW G.BLS PRC.FFS Cred 0 i E A1 M' m' HA') as Hoff.
        pose proof (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) as HLFv.
        assert (KN : know_ok (hl_segs L) E' (CCA.vis A1 m' M') (SR.ps_cells ps0)) by (apply Forall_forall; intros X0 HX0; exact (CC.lf_cells _ _ _ _ _ _ _ HLFv _ HX0)).
        pose proof (DEFO _ _ _ _ _ _ HH1) as DO'.
        rewrite SCRV in HP. pose proof HP as (HP1 & HP2 & HP3).
        assert (OSH' : shadow_zero M' o 3).
        { apply (CL5A.shadow_zero_same M M'); [|exact Osh]. intros j0 Hj0. exact (HP1 (S o + j0) (OSHK (S o + j0) ltac:(clear - Hj0; lia))). }
        assert (STK' : PMSA.stksh ar M' sp PMSA.STR_SCR).
        { unfold PMSA.stksh, PMSA.STR_SCR, PMSA.OPNEW_SCR, PMSA.MALLOC_SCR. apply (PTA.stksh_mono ar M' sp 4496 sp (256 + (16 + 4096))); [| | | clear; lia].
          - apply (PTA.stksh_ag ar M M' sp 4496); [|exact Hstksh]. intros a Ha. exact (HP1 a (KSTK a Ha)).
          - clear - S1. pose proof (Z_div_mod_eq_full sp 16) as D. rewrite S1, Z.add_0_r in D. rewrite D. replace (16 * (sp / 16) - 4496) with ((2 * (sp / 16) - 562) * 8) by lia. apply Z_mod_mult.
          - clear - S1. pose proof (Z_div_mod_eq_full sp 16) as D. rewrite S1, Z.add_0_r in D. rewrite D. replace (16 * (sp / 16) - (256 + (16 + 4096))) with ((2 * (sp / 16) - 546) * 8) by lia. apply Z_mod_mult. }
        assert (RA0' : getr R' 10%bv = Z_to_bv 64 o).
        { replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity). rewrite (CL.ps_reg_is_sound (hl_segs L) c ps0 E' R' _ _ 10 _ HLFv Y10).
          unfold PRC.oE. cbn [edenot]. rewrite <- W15. symmetry. apply Z_to_bv_bv_unsigned. }
        destruct (PRC.reg_of ps0 11) as [e11|] eqn:Hr11; [|discriminate Y11].
        pose proof (APS.fact_ok_sound (hl_segs L) E' _ _ _ KN Y11) as Hch. cbn [kentry_ok] in Hch.
        set (ch := bv_unsigned (edenot E' e11)) in *.
        assert (RA1' : getr R' 11%bv = Z_to_bv 64 ch).
        { replace (11%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 11)) by (apply bv_eq; reflexivity). rewrite (PRC.reg_of_sound _ c ps0 E' R' _ _ 11 e11 HLFv Hr11). unfold ch. symmetry. apply Z_to_bv_bv_unsigned. }
        assert (HTRANS : forall M2 W2, CHA.ahpres L ar LB FF sp PMSA.STR_SCR W2 M' M2 -> W2 = [(o, 24)] -> CHA.ahpres L ar LB FF sp 4496 WW M M2).
        { intros M2 W2 HP2' ->. unfold PMSA.STR_SCR, PMSA.OPNEW_SCR, PMSA.MALLOC_SCR in HP2'.
          apply (CRB.ahpres_trans L ar LB LB LB FF sp 4496 (256 + (16 + 4096)) WW WW [(o, 24)] M M' M2 HP HP2' (incl_refl _) (incl_refl _));
            [clear; lia | clear - S3 SP1; lia | clear - CL; lia | clear - S2; lia | intros w a Hw Ha; exists w; split; [exact Hw | exact Ha] | intros w a Hw Ha; exists w; split; [exact Hw | exact Ha]]. }
        destruct (PRC.blk_of i) as [b|] eqn:Hbk.
        -
          apply andb_prop in YS as [YB YS]. apply CH2.blocks_eqb_eq in YB.
          assert (Hcr1 : cr1 = adebit L cr 48) by (unfold Cred in HC1; rewrite YB in HC1; exact HC1). subst cr1.
          set (p := CL5A.uv E b).
          assert (DENi : CH2.den E (nth i G.BLS []) = [(p, 48)]) by (rewrite YB; unfold CH2.den; cbn [map fst snd edenot]; rewrite (u64_of_Z 48) by (clear; lia); reflexivity).
          assert (HB : CHA.curB LB G.BLS i E = (p, 48) :: LB) by (unfold CHA.curB; rewrite DENi; reflexivity). rewrite HB.
          destruct (HXi' p 48 ltac:(rewrite DENi; left; reflexivity)) as (HAFP & HDF & HSB).
          pose proof HAFP as (Hrng & Hbap & Hfap). pose proof Hrng as (Q0 & Q1 & Q16 & Q3 & Q4 & (Q5 & Q6 & Q7)).
          assert (Pb : CL5A.uv E' b = p).
          { pose proof Xfoot as Xf. unfold CHA.foot_chk in Xf. apply andb_prop in Xf as [Xf _]. apply andb_prop in Xf as [Xf _]. apply andb_prop in Xf as [_ Hbv].
            pose proof (CH2.den_agree _ E E' _ Hag Hbv) as DA. rewrite YB in DA. unfold CH2.den in DA. cbn [map fst snd] in DA. injection DA as DA. exact DA. }
          destruct (PRK.long_ok_sound (hl_segs L) PRC.oV false 23 46 E' _ b _ o YS KN W15 ltac:(clear - O3; lia) ltac:(clear - O6; lia)
                      ltac:(change (bv_unsigned (edenot E' b)) with (CL5A.uv E' b); rewrite Pb; clear - Q0 Q7; lia) ltac:(clear; lia) ltac:(clear; lia)) as (Sz & HSz & Hw0 & Hw8 & Hw16 & _).
          change (bv_unsigned (edenot E' b)) with (CL5A.uv E' b) in Hw16. rewrite Pb in Hw16.
          destruct (PRK.bytes_of_defined (hl_segs L) M' (Z.to_nat Sz) p ltac:(clear - Q0; lia) ltac:(clear - Q0 Q7 HSz; lia)
                      ltac:(apply (L5.defined_sub _ p 48 p _ HDF); clear - HSz; lia)) as (s & Hls & Hbs).
          assert (LS' : Z.of_nat (length s) = Sz) by (rewrite Hls; clear - HSz; lia).
          eexists. eexists. split; [exact (PUSH_L48 ((p, 48) :: LB) FF LK1 (adebit L cr 48) A1 o p ch sp r s)|].
          split.
          { split; [exact RA0'|]. split; [exact RA1'|]. split; [clear - Hch; lia|]. split.
            { unfold PMFCA.l48_nonul. rewrite LS'. split; [exact (CL5A.u64_full (hl_segs L) _ Hoff _ _ _ Hw0)|]. split; [exact (CL5A.u64_full (hl_segs L) _ Hoff _ _ _ Hw8)|].
              split; [exact (CL5A.u64_full (hl_segs L) _ Hoff _ _ _ Hw16) | exact Hbs]. }
            split; [clear - LS' HSz; lia|]. split; [left; reflexivity|]. split; [exact HSB|]. split; [split; [exact Ofr | split; [exact O8 | exact OSH']]|]. exact STK'. }
          intros fx2 R2 M2 model2 LB' cr' LBk Wc LK2 A2 HFP2 (Hstr2 & Hsb2 & -> & -> & -> & ->) HRP2 HP2' Hrt2 HA2 Hmo2 HLK2 HH2.
          assert (RM : lb_remove p ((p, 48) :: LB) = LB) by (cbn [lb_remove fst]; rewrite Z.eqb_refl; reflexivity). rewrite RM in HP2'.
          apply (Hcont fx2 R2 M2 model2 ((p, 48) :: LB) (adebit L cr 48) LB WW LK2 A2 HFP2); [| exact HRP2 | exact (HTRANS M2 _ HP2' eq_refl) | exact Hrt2 | exact HA2 | exact Hmo2 | exact HLK2 | exact HH2].
          split; [|split; reflexivity]. exists (s ++ [ch]). split; [rewrite length_app; cbn [length]; clear - LS' HSz; lia|]. right. exists p.
          split; [rewrite length_app; cbn [length]; clear - LS' HSz; lia|]. split; [exact Hstr2|]. split; [exact (DEFO _ _ _ _ _ _ HH2)|].
          split; [|split; reflexivity]. split; [exact Hrng|]. split; [exact Hbap|]. split; [exact Hfap|]. split; [|exact Hsb2].
          destruct (CHA.wf_blk _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH2) (p, 48) (or_introl eq_refl)) as (_ & Bdef & _). exact Bdef.
        -
          apply andb_prop in YS as [YB YS]. apply CH2.blocks_eqb_eq in YB.
          assert (Hcr1 : cr1 = cr) by (unfold Cred in HC1; rewrite YB in HC1; exact HC1). subst cr1.
          assert (HB : CHA.curB LB G.BLS i E = LB) by (unfold CHA.curB; rewrite YB; reflexivity). rewrite HB.
          destruct (PRK.short_nonul_sound (hl_segs L) PRC.oV E' _ _ o YS KN W15 ltac:(clear - O3; lia) ltac:(clear - O6; lia)) as (h & Hh & Hb0).
          destruct (PRK.bytes_of_defined (hl_segs L) M' (Z.to_nat h) (o + 1) ltac:(clear - O3; lia) ltac:(clear - O6 Hh; lia)
                      ltac:(apply (L5.defined_sub _ o 24 (o + 1) _ DO'); clear - Hh; lia)) as (s & Hls & Hbs).
          assert (LS' : Z.of_nat (length s) = h) by (rewrite Hls; clear - Hh; lia).
          eexists. eexists. split; [exact (PUSH_SHORT LB FF LK1 cr A1 o ch sp r s)|].
          split.
          { split; [exact RA0'|]. split; [exact RA1'|]. split; [clear - Hch; lia|]. split.
            { unfold PMFCA.sso_nonul. rewrite LS'. split; [clear - LS' Hh; lia|]. split; [exact (CL5A.u8_full (hl_segs L) _ Hoff _ _ _ Hb0) | exact Hbs]. }
            split; [exact DO'|]. split; [split; [exact Ofr | split; [exact O8 | exact OSH']]|]. split; [exact STK'|]. intros _. exact Hcred. }
          intros fx2 R2 M2 model2 LB' cr' LBk Wc LK2 A2 HFP2 (HG & -> & ->) HRP2 HP2' Hrt2 HA2 Hmo2 HLK2 HH2.
          apply (Hcont fx2 R2 M2 model2 LB' cr' LB WW LK2 A2 HFP2); [| exact HRP2 | exact (HTRANS M2 _ HP2' eq_refl) | exact Hrt2 | exact HA2 | exact Hmo2 | exact HLK2 | exact HH2].
          split; [|split; reflexivity]. exists (s ++ [ch]). split; [rewrite length_app; cbn [length]; clear - LS' Hh; lia | exact HG]. }
      apply IFB in X as [[Ep5 X]|[Ep5 X]]; [|discriminate X].
      {
        apply andb_prop in X as [X YT]. apply andb_prop in X as [Ypc Ysite]. apply Z.eqb_eq in Ypc.
        destruct (PRC.sites pc Ep5) as (Hsite & Hpcl & Hpc4). rewrite <- LS, <- Ypc in Hsite.
        destruct (PRC.sh_target i c ps0) as [j|] eqn:Hj; [|discriminate YT]. clear YT.
        unfold PRC.sh_target in Hj. apply find_some in Hj as [_ Hok]. unfold PRC.sh_ok in Hok.
        destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate Hok].
        destruct (PRC.sh_cur ps0) as [cur|] eqn:Hcur; [|discriminate Hok].
        destruct (PRC.meas_kv (CC.cp_meas c)) as [[kv a]|] eqn:Hm1; [|discriminate Hok].
        destruct (PRC.meas_kv (CC.esubstL GT.NF (PRC.IDS (CC.cp_nx cj)) (CC.cp_meas cj))) as [[kv' b]|] eqn:Hm2; [|discriminate Hok].
        apply andb_prop in Hok as [Hok Ybl]. apply andb_prop in Hok as [Hok Yz]. apply andb_prop in Hok as [Hok Ycur]. apply andb_prop in Hok as [Hok Ygoto].
        apply andb_prop in Hok as [Ykv Yshl].
        apply (CSL1.shload1_leaf L ar C HI HIok LYI LYR LYB LYN GT.NF E0 M model A LB FF LK sp G.HDECL WW WW G.BLS PRC.FFS Cred 0 STKF SCRP NF32 U2 (incl_refl _) WOK WRS_OK G.CPS K PMSA.fp_ok XI
                 i c ps0 j cj (PRC.IDS (CC.cp_nx cj)) 10%nat 10%nat cur PRC.SBz kv a b Hcj Hsite Yshl Ygoto).
        - rewrite Ypc. split; [exact Hpcl | exact Hpc4].
        - intros Ex Ex' Rx Rx' Ax Mx mx Mx1 mx1 HAt' HA' HXx Hag' HLF'. split.
          + assert (HagE : env_agree GT.NF E0 Ex) by exact (proj1 (proj2 (proj2 (proj2 HA')))).
            assert (W10 : bv_unsigned (ev Ex' 10) = buf).
            { rewrite <- (proj1 Hag' 10%nat) by (clear - NXc; unfold GT.NF in *; lia). rewrite <- (proj1 HagE 10%nat) by (apply Nat.ltb_lt; reflexivity). exact U10. }
            assert (KNx : know_ok (hl_segs L) Ex' (CCA.vis Ax mx1 Mx1) (SR.ps_cells ps0)).
            { apply Forall_forall. intros X0 HX0. exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF') _ HX0). }
            pose proof (PRK.cur_ok_sound (hl_segs L) Ex' _ PRC.bufE cur _ Ycur KNx ltac:(unfold CL5A.uv, PRC.bufE; cbn [edenot]; rewrite W10; clear - B3 B6; lia)) as CR.
            unfold CL5A.uv, PRC.bufE in CR. cbn [edenot] in CR. rewrite W10 in CR.
            exists (CHA.SRL3 PRC.bufE), PRC.SBz, (ELit 3), buf. split; [apply CC.has_cell_In; exact Yz|].
            split; [rewrite CL5A.estart_srl3; unfold CL5A.uv, PRC.bufE; cbn [edenot]; rewrite W10; reflexivity|]. split; [exact Hb8|].
            cbn [edenot]. rewrite u64_of_Z by (clear; lia). clear - CR. lia.
          + exact (XGEN i c ps0 j (PRC.IDS (CC.cp_nx cj)) Ex Rx Ex' Rx' Ax Mx mx Mx1 mx1 Ygoto HAt' HA' Hag' HLF' HXx).
        - intros Ea Eb Rb Ma Mb cr1 _ _ _ HC. unfold Cred in *. apply Bool.eqb_prop in Ybl. rewrite <- Ybl. exact HC. }
    - exact Hc0.
    - rewrite LS. exact HAt0.
    -
      split.
      + split; [exact Hmo|]. split; [exact (L5LZ.sbm_model_rt _ _ (same_but_materialized_refl model))|]. split; [apply incl_refl|]. split; [apply CC.env_agree_refl|].
        split; [|split; [intros a _; reflexivity | intros a _ _ Hd; exact Hd]].
        exists cr, LK. unfold CHA.curB, CHA.curF. rewrite Hbl0, FFSnil. cbn [CH2.den CHA.denF map app length].
        split; [exact HH|]. split; [apply incl_refl|]. split; [unfold Cred; rewrite Hbl0; reflexivity | rewrite Z.sub_0_r; exact Hroom].
      + intros q n Hin. rewrite Hbl0 in Hin. destruct Hin.
    - exact Hfp. }

  assert (N0 : Z.of_nat (length s0) = 0 \/ Z.of_nat (length s0) = 1) by (destruct Hs0 as [->| ->]; [left|right]; reflexivity).
  set (n0 := Z.of_nat (length s0)) in *.
  set (gh := fun (x : Z) (v : nat) => Z_to_bv 64 (nth (v - 32) [n0; x] 0)).
  assert (EVg : forall x (y : reg), ev (Env (reg_ev R (gh x)) (fun _ => [])) (ridx y) = getr R y) by (intros x y; apply CL5.ev_reg).
  assert (G32 : forall x, ev (Env (reg_ev R (gh x)) (fun _ => [])) 32 = Z_to_bv 64 n0) by (intros x; reflexivity).
  assert (G33 : forall x, ev (Env (reg_ev R (gh x)) (fun _ => [])) 33 = Z_to_bv 64 x) by (intros x; reflexivity).
  assert (CLV : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 0 a -> (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)) -> ahid A model (Z_to_bv 64 a) = false)
    by (intros a Ha Hcl Hs; exact (CHA.client_vis L ar C HI HIok _ _ _ _ _ _ model sp 0 a HH Ha Hcl Hs)).
  assert (VO : CL5A.visr (ahid A model) o 24).
  { intros q Hq. destruct (CL5A.infr_wok L ar LB FF sp 0 o 24 (o + q) RFx Ofr ltac:(clear - Hq; lia)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
  assert (VB : CL5A.visr (ahid A model) buf 24).
  { intros q Hq. destruct (CL5A.infr_wok L ar LB FF sp 0 buf 24 (buf + q) RFx Hbobj ltac:(clear - Hq; lia)) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
  assert (VS : CL5A.visr (ahid A model) (sp - 4496) 4496).
  { intros q Hq. apply CLV; [clear - Hq S2 S3 CL SP1; lia | right; left; split; [clear - Hq S2 S3 SP1; lia | clear; lia] |].
    apply (CL5A.not_stk_shadow_app L ar LB FF _ RFx). unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - Hq S2 CL. lia. }
  assert (VSH : forall p, CL5A.ainfr FF p 24 -> p mod 8 = 0 -> shadow_zero M p 3 -> shadow_zero (CCA.vis A model M) p 3).
  { intros p Hp Hp8 HZ j Hj. apply (CL5A.byte_vis _ M). 2: exact (HZ j Hj).
    pose proof (CL5A.shreg_in_shadow p 3 (S p + j) Hp8 ltac:(clear; lia) ltac:(unfold S; clear - Hj; lia)) as SH. change (8 * 3) with 24 in SH.
    destruct (CL5A.infr_sh_wok L ar LB FF sp 0 p 24 (S p + j) RFx Hp ltac:(clear; lia) SH) as (G1 & G2 & G3). exact (CLV _ G1 (aclientw_client _ _ _ _ _ _ _ G2) G3). }
  assert (BASEOK : forall x, know_ok (hl_segs L) (Env (reg_ev R (gh x)) (fun _ => [])) (CCA.vis A model M) (skipn 2 (CC.cp_know G.cp0))).
  { intros x. set (Mv := CCA.vis A model M). set (E0 := Env (reg_ev R (gh x)) (fun _ => [])).
    assert (U2 : bv_unsigned (ev E0 2) = sp) by (change 2%nat with (ridx 2%bv); rewrite (EVg x 2%bv), Hsp; apply u64_of_Z; clear - S2 S3 SP1 CL; lia).
    assert (U10 : bv_unsigned (ev E0 10) = buf) by (change 10%nat with (ridx 10%bv); rewrite (EVg x 10%bv), Ha0; apply u64_of_Z; clear - B3 B6; lia).
    assert (U11 : bv_unsigned (ev E0 11) = len) by (change 11%nat with (ridx 11%bv); rewrite (EVg x 11%bv), Ha1; apply u64_of_Z; clear - Hlen; lia).
    assert (U15 : bv_unsigned (ev E0 15) = o) by (change 15%nat with (ridx 15%bv); rewrite (EVg x 15%bv), Ha5; apply u64_of_Z; clear - O3 O6; lia).
    assert (U32 : bv_unsigned (ev E0 32) = n0) by (unfold E0; rewrite G32; apply u64_of_Z; clear - N0; lia).
    assert (DO : L5.defined Mv o 24) by (apply (CL5A.defined_vis _ M o 24 VO); exact Hdefo).
    assert (DB : L5.defined Mv buf 24) by (apply (CL5A.defined_vis _ M buf 24 VB); exact Hdefb).
    assert (DS : L5.defined Mv (sp - 4496) 4496) by (apply (CL5A.defined_vis _ M _ _ VS); exact S5).
    destruct Hstr as (Hl22 & Hb0 & Hbs & Hnul).
    unfold know_ok. let l := eval vm_compute in (skipn 2 (CC.cp_know G.cp0)) in change (skipn 2 (CC.cp_know G.cp0)) with l.
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 ltac:(unfold GT.NF; lia) GT.SCELLS GT.GLO GT.GHI
               ltac:(split; [intros y [<-|[]]; apply (L5A.aly_cells L C LAY); left; reflexivity | rewrite IHI; repeat constructor; cbn; clear; lia])
               ltac:(rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI; unfold GT.GLO, GT.GHI; clear; lia) _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + apply (CHA.static_sound L ar C HI HIok LYI GT.NF 0 ltac:(unfold GT.NF; lia) GT.SCELLS GT.GLO GT.GHI
               ltac:(split; [intros y [<-|[]]; apply (L5A.aly_cells L C LAY); left; reflexivity | rewrite IHI; repeat constructor; cbn; clear; lia])
               ltac:(rewrite (L5A.aly_got_lo L C LAY), (L5A.aly_got_hi L C LAY), IHI; unfold GT.GLO, GT.GHI; clear; lia) _ _ _ _ _ _ _ E0 _ HH). reflexivity.
    + eapply CL5.krange_intro with (v := len); [lin_eval; rw_atoms; rewrite ?U11; clear; lia | clear - Hlen; lia | clear - Hlen; lia].
    + eapply CL5A.kword8_intro with (A := o) (z := 2 * n0); [ev0 | clear - O3; lia | clear - O6; lia | | clear - N0; lia |].
      * rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)). f_equal. apply CL5.u_lin; [lin_eval; rw_atoms; rewrite ?U32; clear; lia | clear - N0; lia].
      * apply (CL5A.u8_vis (hl_segs L)); [clear - O3; lia | clear - O6; lia | exact (CL5A.visr_sub _ o 24 o 1 VO ltac:(clear; lia) ltac:(clear; lia)) | exact Hb0].
    + eapply CL5.krange_intro with (v := n0); [lin_eval; rw_atoms; rewrite ?U32; clear; lia | clear - N0; lia | clear - N0; lia].
    + eapply CL5.kunk_intro with (A := o + 1) (N := n0); [ev0 | unfold elenZ; cbn [edenot]; exact U32 | clear - O3; lia | clear - O6 N0; lia | clear - O6; lia |].
      apply (L5.defined_sub _ o 24 (o + 1) n0 DO ltac:(clear; lia) ltac:(clear - N0; lia)).
    + eapply CL5.kunk_intro with (A := buf) (N := 24); [ev0 | reflexivity | clear - B3; lia | clear - B6; lia | clear - B6; lia | exact DB].
    + eapply CL5.krange_intro with (v := buf); [lin_eval; rw_atoms; clear; lia | clear - B3 B6; lia | clear - B1 B4 FSLO S2 S3 SP1 CL; lia].
    + eapply CL5.kalign_intro with (v := buf); [lin_eval; rw_atoms; clear; lia | clear - B3 B6; lia | clear; lia | exact Hb8].
    + apply (CL5A.shz_intro (hl_segs L) E0 Mv (EVar 10) 3 buf); [unfold CL5A.uv; cbn [edenot]; exact U10 | clear; lia | clear - B3 B6; lia | exact (VSH buf Hbobj Hb8 Hbsh)].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := buf) (N2 := 24); [reflexivity | reflexivity | ev0 | reflexivity | unfold hid in B5; clear - B5; lia].
    + eapply CL5.kunk_intro with (A := o) (N := 24); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DO].
    + eapply CL5.kwr_intro with (A := o) (N := 24); [ev0 | reflexivity | clear - O3; lia | clear - O6; lia | clear - O6; lia | exact DO].
    + eapply CL5.krange_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear - O1 O4 FSLO S2 S3 SP1 CL; lia].
    + eapply CL5.kalign_intro with (v := o); [lin_eval; rw_atoms; clear; lia | clear - O3 O6; lia | clear; lia | exact O8].
    + apply (CL5A.shz_intro (hl_segs L) E0 Mv (EVar 15) 3 o); [unfold CL5A.uv; cbn [edenot]; exact U15 | clear; lia | clear - O3 O6; lia | exact (VSH o Ofr O8 Osh)].
    + eapply CL5.kdisj_intro with (A1 := 2147446784) (N1 := 17592186048512) (A2 := o) (N2 := 24); [reflexivity | reflexivity | ev0 | reflexivity | unfold hid in O5; clear - O5; lia].
    + eapply CL5.kunk_intro with (A := sp - 4496) (N := 4496); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.kwr_intro with (A := sp - 4496) (N := 4496); [ev0 | reflexivity | clear - S2 CL; lia | clear - S3 SP1; lia | clear - S3 SP1; lia | exact DS].
    + eapply CL5.krange_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear - S2 S3 CL SP1; lia].
    + eapply CL5.kalign_intro with (v := sp); [lin_eval; rw_atoms; clear; lia | clear - S2 S3 CL SP1; lia | clear; lia | exact S1].
    + eapply CL5.kdisj_intro with (A1 := sp - 4496) (N1 := 4496) (A2 := o) (N2 := 24); [ev0 | reflexivity | ev0 | reflexivity | clear - O4 S2; lia].
    + eapply CL5.kdisj_intro with (A1 := sp - 4496) (N1 := 4496) (A2 := buf) (N2 := 24); [ev0 | reflexivity | ev0 | reflexivity | clear - B4 S2; lia].
    + eapply CL5.kdisj_intro with (A1 := buf) (N1 := 24) (A2 := o) (N2 := 24); [ev0 | reflexivity | ev0 | reflexivity | unfold PMLA.apart in Hapart; clear - Hapart; lia]. }

  assert (U11g : forall x, bv_unsigned (ev (Env (reg_ev R (gh x)) (fun _ => [])) 11) = len)
    by (intros x; change 11%nat with (ridx 11%bv); rewrite (EVg x 11%bv), Ha1; apply u64_of_Z; clear - Hlen; lia).
  assert (U33g : forall x, 0 <= x < 2 ^ 64 -> bv_unsigned (ev (Env (reg_ev R (gh x)) (fun _ => [])) 33) = x) by (intros x Hx; rewrite G33; apply u64_of_Z; exact Hx).
  assert (REGSOK : forall (c0 : CC.cutpoint) x e12, CC.cp_regs c0 = sr_upd (sr_upd (sr_upd sr_id 12 e12) 13 (ELit 18446744073709551612)) 14 (ELit 17) ->
            bv_unsigned (edenot (Env (reg_ev R (gh x)) (fun _ => [])) e12) = k mod 2 ^ 64 -> regs_ok (Env (reg_ev R (gh x)) (fun _ => [])) (CC.cp_regs c0) R).
  { intros c0 x e12 Hc He. rewrite Hc.
    apply (regs_ok_upd_same _ _ _ (14%bv : reg)); [apply (regs_ok_upd_same _ _ _ (13%bv : reg)); [apply (regs_ok_upd_same _ _ _ (12%bv : reg)); [apply regs_ok_id | discriminate |] | discriminate |] | discriminate |].
    - rewrite Ha2. rewrite <- (Z_to_bv_bv_unsigned _ (edenot _ e12)), He. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zmod_mod. reflexivity.
    - cbn [edenot]. rewrite Ha3. apply bv_eq. reflexivity.
    - cbn [edenot]. rewrite Ha4. reflexivity. }
  assert (CR0 : forall c0, CC.cp_regs c0 = CC.cp_regs G.cp0 -> CC.cp_regs c0 = sr_upd (sr_upd (sr_upd sr_id 12 (EVar 12)) 13 (ELit 18446744073709551612)) 14 (ELit 17))
    by (intros c0 ->; vm_compute; reflexivity).
  assert (SK : forall x, know_ok (hl_segs L) (Env (reg_ev R (gh x)) (fun _ => [])) (CCA.vis A model M) (skipn 2 (CC.cp_know G.cp0))) by exact BASEOK.
  rewrite LS in SK.
  destruct (Z_lt_le_dec (len + k) (-3)) as [C5|C5].
  {
    set (x := - (len + k)). apply (RUN (gh x) 7%nat G.cp7 eq_refl eq_refl eq_refl). split.
    - apply (REGSOK G.cp7 x (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EVar 11)) (EMd M_MUL (ELit (-1)) (EVar 33)))); [vm_compute; reflexivity|].
      apply u_lin_mod. lin_eval; rw_atoms; rewrite (U11g x), (U33g x) by (unfold x; clear - Hk Hlen C5; lia); unfold x; clear; lia.
    - unfold know_ok. replace (CC.cp_know G.cp7) with ([KRange (EVar 33) 4 342] ++ skipn 2 (CC.cp_know G.cp0)) by vmc_refl.
      apply Forall_app. split; [|exact (SK x)]. repeat apply Forall_cons; [|apply Forall_nil].
      eapply CL5.krange_intro with (v := x); [lin_eval; rewrite (U33g x) by (unfold x; clear - Hk Hlen C5; lia); clear; lia | unfold x; clear - Hk Hlen C5; lia | unfold x; clear - Hk Hlen C5; lia]. }
  destruct (Z_lt_le_dec (len + k) 1) as [C3|C3].
  {
    assert (Z3 : len + k = 0 \/ len + k = -1 \/ len + k = -2 \/ len + k = -3) by (clear - C3 C5; lia).
    assert (E3 : forall i0 c0 e12, nth_error G.CPS i0 = Some c0 -> CC.cp_pc c0 = 855636 -> nth i0 G.BLS [] = [] ->
                 CC.cp_regs c0 = sr_upd (sr_upd (sr_upd sr_id 12 e12) 13 (ELit 18446744073709551612)) 14 (ELit 17) ->
                 bv_unsigned (edenot (Env (reg_ev R (gh 0)) (fun _ => [])) e12) = k mod 2 ^ 64 ->
                 CC.cp_know c0 = skipn 2 (CC.cp_know G.cp0) ->
                 srealizes (hl_segs L) SCFG (mkCfg (@mkst fx R (Z_to_bv 64 855636) M (seg_rom (hl_segs L))) model) K).
    { intros i0 c0 e12 Hc0 Hpc Hbl Hr He Hkn. apply (RUN (gh 0) i0 c0 Hc0 Hpc Hbl). split; [exact (REGSOK c0 0 _ Hr He)|]. unfold know_ok. rewrite Hkn. exact (SK 0). }
    pose proof (U11g 0) as X11.
    destruct Z3 as [Z0|[Z0|[Z0|Z0]]].
    - apply (E3 2%nat G.cp2 (EMd M_MUL (ELit (-1)) (EVar 11)) eq_refl eq_refl eq_refl); [vm_compute; reflexivity | | vm_compute; reflexivity].
      apply u_lin_mod. lin_eval; rw_atoms; clear - Z0; lia.
    - apply (E3 3%nat G.cp3 (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EVar 11)) (ELit (-1))) eq_refl eq_refl eq_refl); [vm_compute; reflexivity | | vm_compute; reflexivity].
      apply u_lin_mod. lin_eval; rw_atoms; clear - Z0; lia.
    - apply (E3 4%nat G.cp4 (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EVar 11)) (ELit (-2))) eq_refl eq_refl eq_refl); [vm_compute; reflexivity | | vm_compute; reflexivity].
      apply u_lin_mod. lin_eval; rw_atoms; clear - Z0; lia.
    - apply (E3 5%nat G.cp5 (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EVar 11)) (ELit (-3))) eq_refl eq_refl eq_refl); [vm_compute; reflexivity | | vm_compute; reflexivity].
      apply u_lin_mod. lin_eval; rw_atoms; clear - Z0; lia. }
  destruct (Z_lt_le_dec 17 (len + k)) as [C4|C4].
  {
    set (x := len + k). apply (RUN (gh x) 6%nat G.cp6 eq_refl eq_refl eq_refl). split.
    - apply (REGSOK G.cp6 x (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EVar 11)) (EVar 33))); [vm_compute; reflexivity|].
      apply u_lin_mod. lin_eval; rw_atoms; rewrite (U11g x), (U33g x) by (unfold x; clear - Hk Hlen C4; lia); unfold x; clear; lia.
    - unfold know_ok. replace (CC.cp_know G.cp6) with ([KRange (EVar 33) 18 330] ++ skipn 2 (CC.cp_know G.cp0)) by vmc_refl.
      apply Forall_app. split; [|exact (SK x)]. repeat apply Forall_cons; [|apply Forall_nil].
      eapply CL5.krange_intro with (v := x); [lin_eval; rewrite (U33g x) by (unfold x; clear - Hk Hlen C4; lia); clear; lia | unfold x; clear - Hk Hlen C4; lia | unfold x; clear - Hk Hlen C4; lia]. }
  destruct (Z_lt_le_dec k 0) as [C2|C2].
  {
    set (x := len + k). apply (RUN (gh x) 1%nat G.cp1 eq_refl eq_refl eq_refl). split.
    - apply (REGSOK G.cp1 x (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EVar 11)) (EVar 33))); [vm_compute; reflexivity|].
      apply u_lin_mod. lin_eval; rw_atoms; rewrite (U11g x), (U33g x) by (unfold x; clear - Hk Hlen C3 C4; lia); unfold x; clear; lia.
    - unfold know_ok.
      replace (CC.cp_know G.cp1) with ([KRange (EVar 33) 1 17; KRange (EAlu ALU_ADD (EVar 11) (EMd M_MUL (ELit (-1)) (EVar 33))) 1 20;
                                        KRange (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EVar 11)) (EVar 33)) 18446744073709551596 18446744073709551615] ++ skipn 2 (CC.cp_know G.cp0))
        by vmc_refl.
      assert (X33 : bv_unsigned (ev (Env (reg_ev R (gh x)) (fun _ => [])) 33) = x) by (apply U33g; unfold x; clear - Hk Hlen C3 C4; lia).
      pose proof (U11g x) as X11.
      apply Forall_app. split; [|exact (SK x)]. repeat apply Forall_cons; [| | | apply Forall_nil].
      + eapply CL5.krange_intro with (v := x); [lin_eval; rw_atoms; clear; lia | unfold x; clear - Hk Hlen C3; lia | unfold x; clear - C3 C4; lia].
      + eapply CL5.krange_intro with (v := len - x); [lin_eval; rw_atoms; unfold x; clear - Hk Hlen C2 C3; lia | unfold x; clear - Hk Hlen C2 C3; lia | unfold x; clear - Hlen Hk C2 C3; lia].
      + cbn [kentry_ok]. rewrite (u_lin_mod _ _ (x - len)) by (lin_eval; rw_atoms; clear; lia). unfold x. clear - Hk Hlen C2 C3. lia. }
  {
    apply (RUN (gh 0) 0%nat G.cp0 eq_refl eq_refl eq_refl). split.
    - apply (REGSOK G.cp0 0 (EVar 12)); [apply CR0; reflexivity|]. change (edenot (Env (reg_ev R (gh 0)) (fun _ => [])) (EVar 12)) with (ev (Env (reg_ev R (gh 0)) (fun _ => [])) (ridx 12%bv)).
      rewrite (EVg 0 12%bv), Ha2. rewrite u64_of_Z by (clear - C2 C4 Hlen; lia). rewrite Z.mod_small by (clear - C2 C4 Hlen; lia). reflexivity.
    - unfold know_ok. replace (CC.cp_know G.cp0) with ([KRange (EVar 12) 0 16; KRange (EAlu ALU_ADD (EVar 11) (EVar 12)) 1 17] ++ skipn 2 (CC.cp_know G.cp0)) by vmc_refl.
      assert (X12 : bv_unsigned (ev (Env (reg_ev R (gh 0)) (fun _ => [])) 12) = k)
        by (change 12%nat with (ridx 12%bv); rewrite (EVg 0 12%bv), Ha2; apply u64_of_Z; clear - C2 C4 Hlen; lia).
      pose proof (U11g 0) as X11.
      apply Forall_app. split; [|exact (SK 0)]. repeat apply Forall_cons; [| | apply Forall_nil].
      + eapply CL5.krange_intro with (v := k); [lin_eval; rw_atoms; clear; lia | clear - C2 C4 Hlen; lia | clear - C2 C4 Hlen; lia].
      + eapply CL5.krange_intro with (v := len + k); [lin_eval; rw_atoms; clear - C2 C4 Hlen; lia | clear - C2 C4 Hlen; lia | clear - C2 C3 C4 Hlen; lia]. }
Qed.
End PrettifyOk.
