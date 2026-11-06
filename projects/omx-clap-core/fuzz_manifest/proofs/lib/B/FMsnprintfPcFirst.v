(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMsnprintfPcFirst.v at a working branch 5d8d8a15571, relocated A->B by Theorem Labs tools over the unstripped twins; every image numeral re-derived by symbol / section (a Theorem Labs lane reloc report). *)
(* musl printf_core (fm.asan 0x8f278), first pass printf_core (0, fmt, &ap2, nl_arg, nl_type) for fm's seven snprintf
   formats: one engine run from the entry to the `ret` at 0x900a0 (the first conversion returns 0, nothing is called),
   then the return. Only the stack window [sp0 - SNK_STK, sp0 + OSP_PC) changes. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMsnprintfPc0 FMsnprintfPcA.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* ---- the runs: each format's first pass stops at the `ret` with a0 = 0 and the entry registers back ---- *)
Definition pf_chk (e : sstate) : bool :=
  (ss_pc e =? 0x900a0) &&
  match ss_resv e with None => true | Some _ => false end &&
  sv_eqb (sr_get (ss_regs e) 10%bv) (SLit 0) &&
  sv_eqb (sr_get (ss_regs e) 1%bv) (SOff 1 0) &&
  sv_eqb (sr_get (ss_regs e) 2%bv) (SOff 2 OSP_PC) &&
  forallb (fun i => sv_eqb (sr_get (ss_regs e) (Z_to_bv 5 (Z.of_nat i))) (SOff i 0))
    [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat &&
  match ss_mem e with
  | r0 :: _ => match YP09.r_base r0 with Some 2%nat => true | _ => false end &&
      (YP09.r_wlo r0 =? - SNK_STK) && (YP09.r_whi r0 =? OSP_PC)
  | [] => false
  end.
Lemma pf_chk_sound : forall e, pf_chk e = true ->
  ss_pc e = 0x900a0 /\ ss_resv e = None /\ sr_get (ss_regs e) 10%bv = SLit 0 /\
  sr_get (ss_regs e) 1%bv = SOff 1 0 /\ sr_get (ss_regs e) 2%bv = SOff 2 OSP_PC /\
  (forall i, In i [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat ->
     sr_get (ss_regs e) (Z_to_bv 5 (Z.of_nat i)) = SOff i 0) /\
  exists r0 rest, ss_mem e = r0 :: rest /\ YP09.r_base r0 = Some 2%nat /\ YP09.r_wlo r0 = - SNK_STK /\
    YP09.r_whi r0 = OSP_PC.
Proof.
intros e H. unfold pf_chk in H.
apply andb_prop in H as [H Hm]. apply andb_prop in H as [H Hf]. apply andb_prop in H as [H S2].
apply andb_prop in H as [H S1]. apply andb_prop in H as [H S10]. apply andb_prop in H as [Hpc Hrv].
apply Z.eqb_eq in Hpc. apply sv_eqb_eq in S10. apply sv_eqb_eq in S1. apply sv_eqb_eq in S2.
split; [exact Hpc|]. split; [destruct (ss_resv e); [discriminate Hrv | reflexivity]|].
split; [exact S10|]. split; [exact S1|]. split; [exact S2|]. split.
- intros i Hi. apply sv_eqb_eq. exact (proj1 (forallb_forall _ _) Hf i Hi).
- destruct (ss_mem e) as [|r0 rest]; [discriminate Hm|].
  destruct (YP09.r_base r0) as [[|[|[|n]]]|] eqn:Eb; try discriminate Hm.
  apply andb_prop in Hm as [Hm Hwhi]. apply andb_prop in Hm as [_ Hwlo].
  apply Z.eqb_eq in Hwlo. apply Z.eqb_eq in Hwhi.
  exists r0, rest. repeat split; assumption.
Qed.
Definition pf_whole_e : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL (pc_t0 FMT_whole)).
Lemma pf_whole_r : sym_runN tfibsegs tfibmusl_tbl FUEL (pc_t0 FMT_whole) = (pf_whole_e, RS_stopped (SR_jalr (SOff 1 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma pf_whole_c : pf_chk pf_whole_e = true. Proof. vm_compute. reflexivity. Qed.
Definition pf_tw_e : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL (pc_t0 FMT_tw)).
Lemma pf_tw_r : sym_runN tfibsegs tfibmusl_tbl FUEL (pc_t0 FMT_tw) = (pf_tw_e, RS_stopped (SR_jalr (SOff 1 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma pf_tw_c : pf_chk pf_tw_e = true. Proof. vm_compute. reflexivity. Qed.
Definition pf_tx_e : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL (pc_t0 FMT_tx)).
Lemma pf_tx_r : sym_runN tfibsegs tfibmusl_tbl FUEL (pc_t0 FMT_tx) = (pf_tx_e, RS_stopped (SR_jalr (SOff 1 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma pf_tx_c : pf_chk pf_tx_e = true. Proof. vm_compute. reflexivity. Qed.
Definition pf_t1_e : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL (pc_t0 FMT_t1)).
Lemma pf_t1_r : sym_runN tfibsegs tfibmusl_tbl FUEL (pc_t0 FMT_t1) = (pf_t1_e, RS_stopped (SR_jalr (SOff 1 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma pf_t1_c : pf_chk pf_t1_e = true. Proof. vm_compute. reflexivity. Qed.
Definition pf_t2_e : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL (pc_t0 FMT_t2)).
Lemma pf_t2_r : sym_runN tfibsegs tfibmusl_tbl FUEL (pc_t0 FMT_t2) = (pf_t2_e, RS_stopped (SR_jalr (SOff 1 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma pf_t2_c : pf_chk pf_t2_e = true. Proof. vm_compute. reflexivity. Qed.
Definition pf_t3_e : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL (pc_t0 FMT_t3)).
Lemma pf_t3_r : sym_runN tfibsegs tfibmusl_tbl FUEL (pc_t0 FMT_t3) = (pf_t3_e, RS_stopped (SR_jalr (SOff 1 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma pf_t3_c : pf_chk pf_t3_e = true. Proof. vm_compute. reflexivity. Qed.
Definition pf_t1x_e : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL (pc_t0 FMT_t1x)).
Lemma pf_t1x_r : sym_runN tfibsegs tfibmusl_tbl FUEL (pc_t0 FMT_t1x) = (pf_t1x_e, RS_stopped (SR_jalr (SOff 1 0))).
Proof. vm_compute. reflexivity. Qed.
Lemma pf_t1x_c : pf_chk pf_t1x_e = true. Proof. vm_compute. reflexivity. Qed.
Lemma pf_ret_word : clookup tfibmusl_tbl 0x900a0 = Some RET_WORD_r.
Proof. vm_compute. reflexivity. Qed.
(* ---- the windows: pc_t0 writes only [sp0 - SNK_STK, sp0 + OSP_PC); the final state's stack window is the same ---- *)
Lemma pf_win : forall E f sp0 a, bv_unsigned (ew E 2) = sp0 -> in_wrange E (ss_mem (pc_t0 f)) a ->
  sp0 - SNK_STK <= a < sp0 + OSP_PC.
Proof.
intros E f sp0 a E2 (r & Hin & Ha). cbn [pc_t0 ss_mem In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; unfold pc_stk0, pc_gotc, pc_can, pc_ro, img_ro_region in Ha;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; [rewrite E2 in Ha | | | ]; lia.
Qed.
Lemma pf_wr : forall E e (ms : machine_state) (W : world tfibsegs) r0 rest a sp0,
  st_ok tfibsegs E e (restrict (w_H W) ms) -> ss_mem e = r0 :: rest -> YP09.r_base r0 = Some 2%nat ->
  YP09.r_wlo r0 = - SNK_STK -> YP09.r_whi r0 = OSP_PC -> bv_unsigned (ew E 2) = sp0 ->
  sp0 - SNK_STK <= a < sp0 + OSP_PC -> writable_at tfibsegs (mrestrict (w_H W) (ms_mem ms)) a.
Proof.
intros E e ms W r0 rest a sp0 HS Hmem Hb Hwlo Hwhi E2 Ha.
destruct HS as (_ & _ & _ & _ & _ & _ & _ & (_ & Hok & _) & _).
rewrite Hmem in Hok. pose proof (Forall_inv Hok) as Hr0. unfold region_ok in Hr0. cbv zeta in Hr0.
destruct Hr0 as (_ & _ & Hw & _). rewrite Hb, Hwlo, Hwhi in Hw. cbn [base_val] in Hw. rewrite E2 in Hw.
cbn [restrict ms_mem] in Hw.
replace a with (sp0 + (a - sp0)) by lia. apply Hw. lia.
Qed.
End r.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
(* the GOT cell holds the guard's address: AR's constant cell, read below the shadow where ARU's memory is mem *)
Lemma pf_got : forall ly S U W mem md, ARU tfibsegs B ly S U W mem md ->
  val_mem tfibsegs (mrestrict (w_H W) mem) FM_GOT_canary 8 FM_canary.
Proof.
intros ly S U W mem md HA.
pose proof (got_canary_of_AR B TB ly S W (unpoison U mem) md (ARU_AR tfibsegs B ly S U W mem md HA)) as Hg.
intros k Hk.
transitivity (mbyte tfibsegs (mrestrict (w_H W) (unpoison U mem)) (A_GOT_CANARY + Z.of_nat k)); [|exact (Hg k Hk)].
change A_GOT_CANARY with FM_GOT_canary. unfold mbyte, mrestrict.
rewrite (ARU_mem_low tfibsegs B ly S U W mem md (Z_to_bv 64 (FM_GOT_canary + Z.of_nat k)) HA); [reflexivity|].
rewrite unsigned_lit_small by (unfold FM_GOT_canary; lia). unfold FM_GOT_canary, SHADOW_OFF. lia.
Qed.
(* the entry state: atom 2 = sp0, the other register atoms the registers, atom 33 the guard's value *)
Lemma pf_entry : forall E ly S U W regs mem md sp0 f cval,
  snk_base B ly S U W mem md sp0 -> snk_regs B regs (sp0 + OSP_PC) -> rom_viewN tfibsegs B W mem ->
  getr regs 10 = w64 0 -> getr regs 11 = w64 f -> getr regs 12 = w64 (sp0 + OSP_PC) ->
  getr regs 13 = w64 (sp0 + OSP_PC + 0x60) -> getr regs 14 = w64 (sp0 + OSP_PC + 0x108) ->
  bv_unsigned (ew E 2) = sp0 -> (forall i (r : bv 5), i <> 2%nat -> Z.of_nat i = bv_unsigned r -> ew E i = getr regs r) ->
  ew E 33 = Z_to_bv 64 cval -> val_mem tfibsegs (mrestrict (w_H W) mem) FM_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
  st_ok tfibsegs E (pc_t0 f) (restrict (w_H W) (mkst regs (Z_to_bv 64 A_PCORE) mem (seg_rom tfibsegs))).
Proof.
intros E ly S U W regs mem md sp0 f cval HB HR HRV G10 G11 G12 G13 G14 E2 HE E33 Hcan Hcv.
pose proof HB as (HA & Hac & Hsp44 & Hsp16 & Hstk & Htop & Hsp47 & Hhigh & Hpres & Hzsh).
pose proof HR as (G1 & G2 & G3 & G4).
pose proof (pf_got ly S U W mem md HA) as Hgot.
rewrite restrict_mkst_fx. unfold pc_t0. apply kentry.
- apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [
    match goal with |- getr _ ?r = sv_denot _ (sr_get ?sr ?r) =>
      let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
    cbn [sv_denot];
    first [ reflexivity
          | (rewrite Z.add_0_r;
             match goal with |- getr _ ?r = Z_to_bv 64 (bv_unsigned (ew _ ?i)) =>
               rewrite (HE i r) by (cbv; first [discriminate | reflexivity]) end;
             rewrite Z_to_bv_bv_unsigned; reflexivity)
          | (rewrite E2; first [rewrite G2 | rewrite G12 | rewrite G13 | rewrite G14]; unfold w64; f_equal;
             unfold OSP_PC; lia)
          | (first [rewrite G10 | rewrite G11]; reflexivity) ] |]).
  destruct Hr.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  + unfold region_ok, pc_stk0. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E2. split; [unfold SNK_STK; lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply YE2y.apresent_writable. apply Hpres. unfold snk_band, SNK_STK, OSP_PC in *. lia.
  + unfold region_ok, pc_gotc. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    unfold FM_GOT_canary. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0); [reflexivity | unfold FM_canary; zside | zside |].
    rewrite Z.add_0_l. exact Hgot.
  + unfold region_ok, pc_can. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    unfold FM_canary. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ cval); [| zside | zside | rewrite Z.add_0_l; exact Hcan].
    cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + exact (pc_ro_ok B E W mem TB HRV).
- apply pairwise_disjoint_of_extents. unfold pc_stk0, pc_gotc, pc_can, pc_ro, img_ro_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2.
  unfold SNK_STK, FM_GOT_canary, FM_canary, IMG_RO_LO, IMG_RO_HI.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I].
  cbn [pc_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
  change (2 ^ 4) with 16. repeat split; lia.
Qed.
(* the frame: only the window [sp0 - SNK_STK, sp0 + OSP_PC) changed, and its bytes are writable *)
Lemma pf_frame : forall ly S U W mem md sp0 mem' md',
  snk_base B ly S U W mem md sp0 -> same_but_materialized md md' ->
  (forall z : word, ~ (sp0 - SNK_STK <= bv_unsigned z < sp0 + OSP_PC) -> mem' z = mem z) ->
  (forall a, sp0 - SNK_STK <= a < sp0 + OSP_PC -> writable_at tfibsegs (mrestrict (w_H W) mem') a) ->
  snk_frame B ly S U W mem md sp0 (sp0 + OSP_PC) (fun _ => False) mem' md'.
Proof.
intros ly S U W mem md sp0 mem' md' HB Hsb HF HW.
pose proof HB as (HA & Hac & Hsp44 & Hsp16 & Hstk & Htop & Hsp47 & Hhigh & Hpres & Hzsh).
assert (Hlit : forall a, sp0 - SNK_STK <= a < sp0 + 0x200 -> 0 <= a < 2 ^ 64)
  by (intros a Ha; unfold kHighMemBeg in *; lia).
assert (HpB : forall a, snk_band sp0 a -> apresent (w_H W) mem' a).
{ intros a Ha. unfold snk_band in Ha. destruct (Z_lt_le_dec a (sp0 + OSP_PC)) as [L|L].
  - apply (YE7f.apresent_of_writable (w_H W) mem' a);
      [apply Hlit; lia | apply YE7f.high_not_img; unfold kHighMemBeg, kLowMemEnd in *; lia | apply HW; lia].
  - apply (YF0x.apresent_same (w_H W) mem mem' a);
      [apply HF; rewrite unsigned_lit_small by (apply Hlit; lia); lia | apply Hpres; unfold snk_band; lia]. }
assert (AVB : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - SNK_STK <= a < sp0 + OSP_PC) ->
  aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a).
{ intros a Hr Ha. apply YF0x.aview_same. apply HF. rewrite unsigned_lit_small by lia. exact Ha. }
pose proof (same_but_materialized_frame md md' Hsb) as MF.
split; [|split; [exact Hsb | split; [exact HpB | split]]].
- apply (ARU_frame tfibsegs B LAWS ly S U W mem md mem' md' HA).
  + intros a Hr Hown. apply AVB; [exact Hr|]. intros Hs.
    exact (ARU_stack tfibsegs B LAWS ly S U W mem md a HA ltac:(unfold OSP_PC in *; lia) Hown).
  + intros a Hv. rewrite (YE2y.aview_mod (w_H W) mem' a). rewrite (YE2y.aview_mod (w_H W) mem a) in Hv.
    assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    destruct (Z_lt_le_dec (a mod 2 ^ 64) (sp0 - SNK_STK)) as [L1|L1]; [rewrite AVB by lia; exact Hv|].
    destruct (Z_lt_le_dec (a mod 2 ^ 64) (sp0 + OSP_PC)) as [L2|L2]; [| rewrite AVB by lia; exact Hv].
    apply YE2y.aview_some_of_apresent. apply HpB. unfold snk_band, OSP_PC in *. lia.
  + apply MF. + apply MF. + apply MF.
  + intros a Ha Hh. unfold YG0d.w64 in Hh |- *.
    assert (Har : 0 <= a < 2 ^ 64) by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia).
    destruct (Z_lt_le_dec a (sp0 - SNK_STK)) as [L1|L1]; [apply HF; rewrite unsigned_lit_small by lia; lia|].
    destruct (Z_lt_le_dec a (sp0 + OSP_PC)) as [L2|L2];
      [exfalso; destruct (HpB a ltac:(unfold snk_band, OSP_PC in *; lia)) as [Hf _]; rewrite Hf in Hh; discriminate Hh|].
    apply HF. rewrite unsigned_lit_small by lia. lia.
- intros a Hr Hb _. exact (AVB a Hr Hb).
- intros a Hpa. rewrite (YE2y.apresent_mod _ mem' a). rewrite (YE2y.apresent_mod _ mem a) in Hpa.
  assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  destruct (Z_lt_le_dec (a mod 2 ^ 64) (sp0 - SNK_STK)) as [L1|L1];
    [apply (YF0x.apresent_same (w_H W) mem mem' _); [apply HF; rewrite unsigned_lit_small by lia; lia | exact Hpa]|].
  destruct (Z_lt_le_dec (a mod 2 ^ 64) (sp0 + OSP_PC)) as [L2|L2];
    [apply HpB; unfold snk_band, OSP_PC in *; lia|].
  apply (YF0x.apresent_same (w_H W) mem mem' _); [apply HF; rewrite unsigned_lit_small by lia; lia | exact Hpa].
Qed.
(* the return at 0x900a0: back at ra with the frame, the callee-saved registers and a0 = 0 *)
Lemma pf_ret : forall E e ms' md1 ly S U W regs mem md sp0,
  snk_base B ly S U W mem md sp0 -> snk_regs B regs (sp0 + OSP_PC) ->
  bv_unsigned (ew E 2) = sp0 -> (forall i (r : bv 5), i <> 2%nat -> Z.of_nat i = bv_unsigned r -> ew E i = getr regs r) ->
  pf_chk e = true -> st_ok tfibsegs E e (restrict (w_H W) ms') -> same_but_materialized md md1 ->
  (forall z : word, ~ (sp0 - SNK_STK <= bv_unsigned z < sp0 + OSP_PC) -> ms_mem ms' z = mem z) ->
  SRr tfibsegs W (mkCfg ms' md1)
    (snk_post B ly S U W regs mem md sp0 (sp0 + OSP_PC) (fun _ => False) 0 (fun _ => True)).
Proof.
intros E e ms' md1 ly S U W regs mem md sp0 HB HR E2 HE Hck HS Hsb HF.
destruct (pf_chk_sound e Hck) as (Hpc & Hrv & S10 & S1 & S2 & Hf & r0 & rest & Hmem & Hb0 & Hwlo & Hwhi).
pose proof HR as (G1 & G2 & G3 & G4).
apply (SRr_ret_at tfibsegs tfibmusl_tbl tfibmusl_tbl_ok Hwx_tfa W E e ms' md1 _ HS Hrv ltac:(rewrite Hpc; exact pf_ret_word)).
intros mat'. split; [reflexivity|].
exists (ms_regs ms'), (ms_mem ms'), (with_vm_backing (m_vm_lazy md1) mat' md1).
assert (G : forall i, In i [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat ->
  getr (ms_regs ms') (Z_to_bv 5 (Z.of_nat i)) = getr regs (Z_to_bv 5 (Z.of_nat i))).
{ intros i Hi. rewrite (st_ok_restrict_reg tfibsegs (w_H W) E e ms' _ HS), (Hf i Hi). cbn [sv_denot].
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. assert (Hi32 : (i < 32)%nat /\ i <> 2%nat) by (cbn in Hi; lia).
  apply HE; [lia|]. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia.
  reflexivity. }
assert (R1 : getr (ms_regs ms') 1 = getr regs 1).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 1 HS), S1. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  apply (HE 1%nat 1%bv); [lia | reflexivity]. }
assert (R2 : getr (ms_regs ms') 2 = getr regs 2).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 2 HS), S2. cbn [sv_denot]. rewrite E2, G2. reflexivity. }
split.
{ unfold cfg_at, raZ, w64. f_equal. f_equal. rewrite R1. unfold YK0s.ret_ok in G1. rewrite G1.
  rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
{ apply (pf_frame ly S U W mem md sp0 (ms_mem ms') _ HB).
  - eapply same_but_materialized_trans; [exact Hsb | apply with_vm_backing_same].
  - exact HF.
  - intros a Ha. exact (pf_wr E e ms' W r0 rest a sp0 HS Hmem Hb0 Hwlo Hwhi E2 Ha). }
split.
{ intros r Hr. unfold acallee_saved in Hr.
  destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [exact R2 | exact (G 3%nat ltac:(cbn; tauto)) | exact (G 4%nat ltac:(cbn; tauto))
    | exact (G 8%nat ltac:(cbn; tauto)) | exact (G 9%nat ltac:(cbn; tauto)) |].
  assert (Hc : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]];
    [exact (G 18%nat ltac:(cbn; tauto)) | exact (G 19%nat ltac:(cbn; tauto)) | exact (G 20%nat ltac:(cbn; tauto))
    | exact (G 21%nat ltac:(cbn; tauto)) | exact (G 22%nat ltac:(cbn; tauto)) | exact (G 23%nat ltac:(cbn; tauto))
    | exact (G 24%nat ltac:(cbn; tauto)) | exact (G 25%nat ltac:(cbn; tauto)) | exact (G 26%nat ltac:(cbn; tauto))
    | exact (G 27%nat ltac:(cbn; tauto))]. }
split; [|exact I].
rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 10 HS), S10. reflexivity.
Qed.
(* one format: the entry, the engine run, the return *)
Lemma pcore0_gen : forall f e, sym_runN tfibsegs tfibmusl_tbl FUEL (pc_t0 f) = (e, RS_stopped (SR_jalr (SOff 1 0))) ->
  pf_chk e = true ->
  forall ly S U W regs mem md sp0,
  snk_base B ly S U W mem md sp0 -> snk_regs B regs (sp0 + OSP_PC) -> rom_viewN tfibsegs B W mem ->
  getr regs 10 = w64 0 -> getr regs 11 = w64 f -> getr regs 12 = w64 (sp0 + OSP_PC) ->
  getr regs 13 = w64 (sp0 + OSP_PC + 0x60) -> getr regs 14 = w64 (sp0 + OSP_PC + 0x108) ->
  SRr tfibsegs W (cfg_at tfibsegs A_PCORE regs mem md)
    (snk_post B ly S U W regs mem md sp0 (sp0 + OSP_PC) (fun _ => False) 0 (fun _ => True)).
Proof.
intros f e Hrun Hck ly S U W regs mem md sp0 HB HR HRV G10 G11 G12 G13 G14.
pose proof HB as (HA & Hac & Hsp44 & Hsp16 & Hstk & Htop & Hsp47 & Hhigh & Hpres & Hzsh).
destruct (canary_val (w_H W) mem) as (cval & Hcan & Hcv).
assert (E2 : bv_unsigned (ew (kenv regs sp0 [Z_to_bv 64 0; Z_to_bv 64 cval]) 2) = sp0)
  by (rewrite kenv_2; apply unsigned_lit_small; unfold kHighMemBeg, SNK_STK in *; lia).
assert (HE : forall i (r : bv 5), i <> 2%nat -> Z.of_nat i = bv_unsigned r ->
  ew (kenv regs sp0 [Z_to_bv 64 0; Z_to_bv 64 cval]) i = getr regs r) by (intros i r Hi Hr; apply kenv_reg; assumption).
assert (E33 : ew (kenv regs sp0 [Z_to_bv 64 0; Z_to_bv 64 cval]) 33 = Z_to_bv 64 cval)
  by (change 33%nat with (32 + 1)%nat; rewrite kenv_x; reflexivity).
pose proof (pf_entry _ ly S U W regs mem md sp0 f cval HB HR HRV G10 G11 G12 G13 G14 E2 HE E33 Hcan Hcv) as HS0.
unfold cfg_at, w64.
apply (SRr_run_gen tfibsegs tfibmusl_tbl tfibmusl_tbl_ok Hwx_tfa W FUEL _ (pc_t0 f) e _ _ md _ HS0 Hrun).
intros ms' mat' HS' HF _. cbn [ms_mem mkst] in HF.
apply (pf_ret _ e ms' _ ly S U W regs mem md sp0 HB HR E2 HE Hck HS' (with_vm_backing_same md mat')).
intros z Hz. apply HF. intros Hin. apply Hz. exact (pf_win _ f sp0 _ E2 Hin).
Qed.
Theorem pcore0_realizesU : apcore0_realizesU B A_PCORE.
Proof.
intros ly S U W regs mem md sp0 f ps HB HR HRV G10 G11 G12 G13 G14 Hin.
cbn [FM_SN_FMTS In] in Hin.
destruct Hin as [Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[]]]]]]]]; injection Hq as Hq _; subst f.
- exact (pcore0_gen FMT_whole pf_whole_e pf_whole_r pf_whole_c ly S U W regs mem md sp0 HB HR HRV G10 G11 G12 G13 G14).
- exact (pcore0_gen FMT_tw pf_tw_e pf_tw_r pf_tw_c ly S U W regs mem md sp0 HB HR HRV G10 G11 G12 G13 G14).
- exact (pcore0_gen FMT_tx pf_tx_e pf_tx_r pf_tx_c ly S U W regs mem md sp0 HB HR HRV G10 G11 G12 G13 G14).
- exact (pcore0_gen FMT_t1 pf_t1_e pf_t1_r pf_t1_c ly S U W regs mem md sp0 HB HR HRV G10 G11 G12 G13 G14).
- exact (pcore0_gen FMT_t2 pf_t2_e pf_t2_r pf_t2_c ly S U W regs mem md sp0 HB HR HRV G10 G11 G12 G13 G14).
- exact (pcore0_gen FMT_t3 pf_t3_e pf_t3_r pf_t3_c ly S U W regs mem md sp0 HB HR HRV G10 G11 G12 G13 G14).
- exact (pcore0_gen FMT_t1x pf_t1x_e pf_t1x_r pf_t1x_c ly S U W regs mem md sp0 HB HR HRV G10 G11 G12 G13 G14).
Qed.
End p.
