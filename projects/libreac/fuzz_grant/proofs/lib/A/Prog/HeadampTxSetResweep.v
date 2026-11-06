(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_headamp_tx_set_resweep on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* reac_headamp_tx_set_resweep (0x85058) on the ASan build: the two stores that
   set the re-assert period and clear its counter. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaRun PaShadow PaStep PaJournal GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantBase
YC1g HeadampTxEffective.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require SegSetModel reac_headamp_tx_set_resweep_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Ltac tx_reg HS r v pf H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?vl ?Ex ?ss (restrict ?Hh ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    assert (H : getr (ms_regs ms) r = v)
      by (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ss ms r HS) _);
          change (sv_denot Ex e = v); pf)
  end.

Section D. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section F.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Definition A_tx_set_resweepP : Z := BASE + AF_reac_headamp_tx_set_resweep.
Definition TRSW_STK : Z := 16 + ESTACK.
Definition rsw_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 140737479966720 4);
            (32%nat, mkAF SBz SBz 0) ] [] [].
Definition RSWR : YP09.region := YP09.mkRegion (Some 10%nat) 452 460 452 460 [].
Definition rsw_regions : smem := [ stack_region 16; got_regionP; bcell_regionP 32; RSWR ].
Definition ss_rsw : sstate := mkSS AF_reac_headamp_tx_set_resweep sr_atoms rsw_regions None rsw_facts.
Definition rsw_SH : list shent := [ mkSHE 10 0 460 ].
Definition ERS (regs : bvmap 5 word) : env := Eimg (Ereg regs [Z_to_bv 64 SBz]).

Section H.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).

Definition trsw_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (tx : Z) (T : list byte)
  : world SEGS -> config -> Prop :=
  apost_base SEGS B TRSW_STK [(tx + 452, tx + 460)] regs ly S W mem md 0
    (fun ly' S' W' regs' mem' md' =>
       ly' = ly /\ S' = S /\ W' = W /\
       obj_at SEGS (mrestrict (w_H W) mem') tx LAY_TX
         (tx_vals (reac_headamp_tx_set_resweep_c.set_resweep_T T (getr regs 11)))).

Definition theadamp_tx_set_resweep_spec : Prop :=
  forall ly S W (regs : bvmap 5 word) mem md ch0 (tx : Z) (T : list byte),
  afn_pre SEGS B TRSW_STK ly S W regs mem md ch0 ->
  getr regs 10 = w64 tx ->
  In (tx, TX_SIZE) (ablocks B ly S) -> length T = 460%nat ->
  obj_at SEGS (mrestrict (w_H W) mem) tx LAY_TX (tx_vals T) ->
  SRr SEGS W (cfg_at SEGS A_tx_set_resweepP regs mem md) (trsw_post regs ly S W mem md tx T).

Lemma rsw_entry : forall ly S W (regs : bvmap 5 word) mem md ch0 (tx : Z),
  afn_pre SEGS B TRSW_STK ly S W regs mem md ch0 ->
  getr regs 10 = w64 tx ->
  In (tx, TX_SIZE) (ablocks B ly S) ->
  st_ok_pi SEGS VAL (ERS regs) ss_rsw
    (restrict (w_H W) (mkst regs (Z_to_bv 64 A_tx_set_resweepP) mem (seg_rom SEGS)))
  /\ sh_ok SEGS CBx rsw_SH (ERS regs) (mrestrict (w_H W) mem).
Proof.
  intros ly S W regs mem md ch0 tx HPRE H10 Htx.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchn & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  assert (WS : TRSW_STK = 4112) by reflexivity.
  destruct (al_blocks _ _ LAWS ly S W mem md tx TX_SIZE HAR Htx) as (Htx16 & Htx4096 & Htxceil & Htxia & Htxpres & _).
  change (req_size TX_SIZE) with 460 in *.
  pose proof (blk_off_imgP B ly S W mem md tx TX_SIZE HAR Htx) as Htximg.
  change (req_size TX_SIZE) with 460 in Htximg.
  destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
  rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
  pose proof (pa_obj_img 32 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
  pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
  rewrite restrict_mkst_fx.
  set (E := ERS regs).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SBz]) n)
    by (intros n Hn; subst E; unfold ERS; apply Eimg_low; exact Hn).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E10 : ew E 10 = Z_to_bv 64 tx) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (E32 : ew E 32 = Z_to_bv 64 SBz) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (Egot : ew E 242%nat = Z_to_bv 64 (VAL (A_OBJ 1)))
    by (change 242%nat with (A_OBJ 1); subst E; unfold ERS; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Ecell : ew E 273%nat = Z_to_bv 64 (VAL (A_OBJ 32)))
    by (change 273%nat with (A_OBJ 32); subst E; unfold ERS; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
  { intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
  split.
  - unfold ss_rsw, A_tx_set_resweepP. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold rsw_regions, stack_region, got_regionP, bcell_regionP, RSWR.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
      * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 32) 0) (VAL (A_OBJ 32)));
        [cbn [sv_denot]; change (A_OBJ 32) with 273%nat; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | pose proof (pa_val_range (A_OBJ 32)); zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
      * rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) Ecell) by (pose proof (pa_val_range (A_OBJ 32)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 32)) 0 8 CBx SBz);
        [cbn [sv_denot CBx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SBz; zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
      * rewrite (VB 10%nat tx E10) by lia.
        split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Htxpres (tx + o) ltac:(lia))).
    + apply pairwise_disjoint_of_extents.
      unfold rsw_regions, stack_region, got_regionP, bcell_regionP, RSWR, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB 10%nat tx E10) by lia.
      rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) Ecell) by (pose proof (pa_val_range (A_OBJ 32)); lia).
      cbn [base_val]. rewrite Usp.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR Htx4096 Htxceil Htximg.
      clear. unfold off_img. intros. repeat split; lia.
    + split; [|split; exact I].
      cbn [rsw_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, E10, E32, !unsigned_lit_small by (unfold SBz; lia).
      change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 Hal16 Htx16 Htx4096 Htxceil.
      clear. unfold SBz. intros. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok, rsw_SH. apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_block SEGS B LAWS ly S W mem md E CBx 10 tx TX_SIZE 0 460 HAR Htx).
    + unfold U, CBx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold SBz; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by lia. reflexivity.
    + lia.
    + change (req_size TX_SIZE) with 460. lia.
Qed.

Theorem pb_headamp_tx_set_resweep : theadamp_tx_set_resweep_spec.
Proof.
unfold theadamp_tx_set_resweep_spec.
intros ly S W regs mem md ch0 tx T HPRE H10 Htx HTl HTo.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (rsw_entry ly S W regs mem md ch0 tx HPRE H10 Htx) as [HS SHOK].
pose proof (ajournal_init SEGS B TRSW_STK [(tx + 452, tx + 460)] ly S W regs mem md ch0 HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchn & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : TRSW_STK = 4112) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md tx TX_SIZE HAR Htx) as (Htx16 & Htx4096 & Htxceil & Htxia & Htxpres & _).
change (req_size TX_SIZE) with 460 in *.
remember (ERS regs) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold ERS; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SBz]) n)
  by (intros n Hn; subst E; unfold ERS; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 tx) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = getr regs 11) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SBz]) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Eu10 : bv_unsigned (ew E 10) = tx) by (rewrite E10; apply unsigned_lit_small; lia).
clear HEdef EL.
unfold cfg_at. change (w64 A_tx_set_resweepP) with (Z_to_bv 64 A_tx_set_resweepP).
paj_run_tok RUN HS HJ SHOK EFFspan;
  [ lazymatch goal with |- awr_ok ?Ey ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok Ey rs' stk sp0 fp b0 bc lyy own) end;
    eapply awr_ok_cons_stack;
      [reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp
       | azlit_tac | azlit_tac |];
    apply awr_ok_cons_ro; [azlit_tac|];
    apply awr_ok_cons_ro; [azlit_tac|];
    eapply (awr_ok_cons_block _ _ _ _ _ _ _ _ _ _ 10%nat tx TX_SIZE);
      [reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Eu10
       | exact Htx | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; change (req_size TX_SIZE) with 460; lia
       | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; exists (tx + 452, tx + 460);
         split; [left; reflexivity | cbn [fst snd]; lia]
       | apply awr_ok_nil]
  | ].
(* the two stores are done; the walk is at the return *)
lazymatch type of HS with
| st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msx) 3%nat
     (YP09.mkRegion (Some 10%nat) 452 460 452 460
        [YP09.mkChunk 456 (CVal 4 (SLit 0)); YP09.mkChunk 452 (CVal 4 (SOff 11 0))]) HS
     ltac:(vm_compute; reflexivity)) as HRfin
end.
cbn [restrict ms_mem] in HRfin.
assert (Eu10' : forall (Ex : env), ew Ex 10 = ew E 10 -> bv_unsigned (ew Ex 10) = tx)
  by (intros Ex Hx; rewrite Hx; exact Eu10).
tx_reg HS (1%bv : bv 5) (getr regs 1)
  ltac:(cbn [sv_denot extK ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia;
        rewrite E1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) R1.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat9. cbn [ms_regs ms_mem]. rewrite R1, Hra.
unfold trsw_post, apost_base. cbv beta.
lazymatch type of HS with
| st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  exists ly, S, (ms_regs msx), (ms_mem msx); eexists;
  split; [reflexivity|];
  split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|];
  split; [eapply (aregs_preserved_of_st_ok SEGS _ Ex _ _ regs [Z_to_bv 64 SBz] HS);
          [ split; [intros n Hn; cbn [extK ew ewset];
                    replace (n =? 513)%nat with false by (symmetry; apply Nat.eqb_neq; lia);
                    replace (n =? 512)%nat with false by (symmetry; apply Nat.eqb_neq; lia);
                    exact (proj1 HAE n Hn) | cbn [extK ew ewset]; exact (proj2 HAE) ]
          | vm_compute; reflexivity]|];
  split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]
end.
(* the table: the two fields the stores set, every other byte kept *)
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
lazymatch type of HRfin with
| region_ok _ ?Ex _ _ =>
  assert (Ex11 : sv_denot Ex (SOff 11 0) = getr regs 11)
    by (cbn [sv_denot extK ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia;
        rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
  assert (Ex10 : bv_unsigned (ew Ex 10) = tx)
    by (cbn [extK ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Eu10)
end.
apply (proj2 (tx_obj_bytes SEGS _ tx _)).
intros i Hi. pose proof (tx_fbyte_range i Hi) as Hir.
assert (HL1 : length (Mem.upd_bytes T 452 (Mem.le4 (getr regs 11))) = 460%nat)
  by (rewrite Mem.upd_bytes_length; [exact HTl | rewrite Mem.length_le4; lia]).
unfold reac_headamp_tx_set_resweep_c.set_resweep_T.
rewrite (SegSetModel.nth_upd_bytes _ _ 456 (Z.to_nat i)) by (rewrite Mem.length_le4; lia).
rewrite Mem.length_le4.
destruct (Z_lt_le_dec i 452) as [Hlo | Hlo].
- (* kept *)
  replace ((456 <=? Z.to_nat i)%nat && (Z.to_nat i <? 456 + 4)%nat)%bool with false
    by (symmetry; apply andb_false_iff; left; apply Nat.leb_gt; lia).
  rewrite (SegSetModel.nth_upd_bytes _ _ 452 (Z.to_nat i)) by (rewrite Mem.length_le4; lia).
  rewrite Mem.length_le4.
  replace ((452 <=? Z.to_nat i)%nat && (Z.to_nat i <? 452 + 4)%nat)%bool with false
    by (symmetry; apply andb_false_iff; left; apply Nat.leb_gt; lia).
  rewrite <- (proj1 (tx_obj_bytes SEGS (mrestrict (w_H W) mem) tx T) HTo i Hi).
  apply (mbyte_of_aview SEGS (w_H W) (w_H W) mem _ (tx + i)).
  apply (F2 tx TX_SIZE i Htx Htx ltac:(change (req_size TX_SIZE) with 460; lia)).
  intros (r & Hin & Hr). destruct Hin as [<- | []]. cbn [fst snd] in Hr. lia.
- destruct (Z_lt_le_dec i 456) as [Hmid | Hmid].
  + (* the period, 452..455 *)
    replace ((456 <=? Z.to_nat i)%nat && (Z.to_nat i <? 456 + 4)%nat)%bool with false
      by (symmetry; apply andb_false_iff; left; apply Nat.leb_gt; lia).
    rewrite (SegSetModel.nth_upd_bytes _ _ 452 (Z.to_nat i)) by (rewrite Mem.length_le4; lia).
    rewrite Mem.length_le4.
    replace ((452 <=? Z.to_nat i)%nat && (Z.to_nat i <? 452 + 4)%nat)%bool with true
      by (symmetry; apply andb_true_iff; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia).
    rewrite (le4_byte_of_word (getr regs 11) (Z.to_nat i - 452) ltac:(lia)).
    replace (Z.of_nat (Z.to_nat i - 452)) with (i - 452) by lia.
    rewrite <- Ex11.
    replace (tx + i) with (tx + 452 + (i - 452)) by lia.
    apply (byte_of_region SEGS _ _ 10%nat tx _ 452 460 452 460 452 4 (SOff 11 0) (i - 452) HRfin Ex10);
      [right; left; reflexivity | cbn; lia].
  + (* the counter, 456..459 *)
    replace ((456 <=? Z.to_nat i)%nat && (Z.to_nat i <? 456 + 4)%nat)%bool with true
      by (symmetry; apply andb_true_iff; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia).
    rewrite (le4_byte_of_word (Z_to_bv 64 0) (Z.to_nat i - 456) ltac:(lia)).
    replace (Z.of_nat (Z.to_nat i - 456)) with (i - 456) by lia.
    replace (tx + i) with (tx + 456 + (i - 456)) by lia.
    rewrite (byte_of_region SEGS _ _ 10%nat tx _ 452 460 452 460 456 4 (SLit 0) (i - 456) HRfin Ex10
               ltac:(left; reflexivity) ltac:(cbn; lia)).
    try (f_equal; cbn [sv_denot]; reflexivity).
Qed.

End H.
End F.
End D.
