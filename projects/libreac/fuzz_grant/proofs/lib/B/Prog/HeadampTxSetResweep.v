(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_headamp_tx_set_resweep on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/HeadampTxSetResweep.v at a working branch 5651bf66924 (blob 2f92e82a66a, the blob the walk was ported from), restated over image B's listing, addresses and walk layer (lib/B/Prog) against GrantBContracts.v; on B the shadow-base cell is listing object 35 (A: 32, the shadow-base atom stays 32), the entry offset is 0x543c, and the 4-byte store at tx + 456 lies in the block's last partial granule (shadow 4), whose slow path returns to the store. *)
(* Image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/HeadampTxSetResweep.v (source cited in the line above): the same
   walk over image B's listing and walk layer (lib/B/Prog), against the contract GrantBContracts.v states.
   reac_headamp_tx_set_resweep (image B 0x85e78, 33 instructions; image A 0x85058, 29): the two stores that set
   the re-assert period (tx + 452 := low 32 bits of a1) and clear its counter (tx + 456 := 0).
   What image B adds over image A, and where this file differs from the donor:
   - the UBSan null and alignment guards 0x85e80 (`beqz a0`) and 0x85e88 (`andi a2,a0,3; bnez a2`), whose trap is
     0x85ed4 (`unimp`): both are decided inside the run from atom 10's facts (lo 4096, 16-alignment), which
     AR_blocks_law gives for the live block through al_blocks;
   - the shadow-base cell is object 35 (image A: 32), so bcell_regionP, the GOT chunk and Ecell are re-keyed;
   - the entry offset is AF_reac_headamp_tx_set_resweep = 0x543c (lib/B/Prog/GrantList.v:39; image A's own
     listing has 0x49a8 at lib/A/Prog/GrantList.v:33).
   The two report branches 0x85ee8 and 0x85ef8 (`__asan_report_store4`; the second is the last slot of the
   function and falls into reac_headamp_tx_next 0x85efc) are refuted inside the run from rsw_SH: the block's
   shadow makes the slow block's `blt` jump back to the store, so neither call is reached. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaRun PaShadow PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib YC1g GrantBContracts.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require SegSetModel.
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
(* The sink head stays a section variable, as in GrantBContracts.v: no sink_head instance is in lib/B's Require
   closure. *)
Context {SK : YI16.sink_head}.
Section F.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Definition RSW_P : Z := BASE + AF_reac_headamp_tx_set_resweep.
(* The shadow offset of this runtime, held in the extra env slot (atom 32). *)
Definition RSW_SB : Z := 0x7fff8000.
Definition RSW_CB : sv := SOff 32 0.
Definition RSWspan : Z * Z := (RSW_SB, RSW_SB + 2 ^ 44 - 1).
(* atom 10 is tx: 4096 <= tx, tx below the allocation ceiling, 16-aligned. The two UBSan guards 0x85e80 and
   0x85e88 are decided from these. *)
Definition rsw_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 140737479966720 4);
            (32%nat, mkAF RSW_SB RSW_SB 0) ] [] [].
Definition RSWR : YP09.region := YP09.mkRegion (Some 10%nat) 452 460 452 460 [].
Definition rsw_regions : smem := [ stack_region 16; got_regionP; bcell_regionP 32; RSWR ].
Definition ss_rsw : sstate := mkSS AF_reac_headamp_tx_set_resweep sr_atoms rsw_regions None rsw_facts.
Definition rsw_SH : list shent := [ mkSHE 10 0 460 ].
Definition ERS (regs : bvmap 5 word) : env := Eimg (Ereg regs [Z_to_bv 64 RSW_SB]).

Section H.
Variable B : asyms.

Lemma rsw_entry : forall (LAWS : AR_laws SEGS B) (TL : PALib B)
  ly S W (regs : bvmap 5 word) mem md ch0 (tx : Z),
  afn_pre SEGS B STK_reac_headamp_tx_set_resweep ly S W regs mem md ch0 ->
  getr regs 10 = w64 tx ->
  In (tx, ATx.TX_SIZE) (ablocks B ly S) ->
  st_ok_pi SEGS VAL (ERS regs) ss_rsw
    (restrict (w_H W) (mkst regs (Z_to_bv 64 RSW_P) mem (seg_rom SEGS)))
  /\ sh_ok SEGS RSW_CB rsw_SH (ERS regs) (mrestrict (w_H W) mem).
Proof.
  intros LAWS TL ly S W regs mem md ch0 tx HPRE H10 Htx.
  pose proof (pal_got_shadow B TL) as HBgot. pose proof (pal_cell B TL) as HBcell.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchn & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  assert (WS : STK_reac_headamp_tx_set_resweep = 4112) by reflexivity.
  destruct (al_blocks _ _ LAWS ly S W mem md tx ATx.TX_SIZE HAR Htx)
    as (Htx16 & Htx4096 & Htxceil & Htxia & Htxpres & _).
  change (req_size ATx.TX_SIZE) with 460 in *.
  (* image B's own bounds, through blk_off_imgB: on the integration tree off_img is lib/B/YCbq.v's, over image B's
     top 0x5fb000; the walk does not depend on which. *)
  pose proof (blk_off_imgB B ly S W mem md tx ATx.TX_SIZE HAR Htx) as Htximg.
  change (req_size ATx.TX_SIZE) with 460 in Htximg.
  rewrite IMG_LO_B_val, IMG_TOP_B_val in Htximg.
  destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
  rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
  pose proof (pa_obj_img 35 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
  pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
  (* image B states its range as IMG_LO_B / IMG_TOP_B, never as a numeral (GrantTop.v:3), so lia needs the two
     value lemmas before it can use these bounds. *)
  rewrite IMG_LO_B_val, IMG_TOP_B_val in HcellR, HgotR.
  rewrite restrict_mkst_fx.
  set (E := ERS regs).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 RSW_SB]) n)
    by (intros n Hn; subst E; unfold ERS; apply Eimg_low; exact Hn).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E10 : ew E 10 = Z_to_bv 64 tx) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (E32 : ew E 32 = Z_to_bv 64 RSW_SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (Egot : ew E 242%nat = Z_to_bv 64 (VAL (A_OBJ 1)))
    by (change 242%nat with (A_OBJ 1); subst E; unfold ERS; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Ecell : ew E 276%nat = Z_to_bv 64 (VAL (A_OBJ 35)))
    by (change 276%nat with (A_OBJ 35); subst E; unfold ERS; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
  { intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
  split.
  - unfold ss_rsw, RSW_P. apply pa_entry_st_ok_full.
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
        apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 35) 0) (VAL (A_OBJ 35)));
        [cbn [sv_denot]; change (A_OBJ 35) with 276%nat; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | pose proof (pa_val_range (A_OBJ 35)); zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
      * rewrite (VB (A_OBJ 35) (VAL (A_OBJ 35)) Ecell) by (pose proof (pa_val_range (A_OBJ 35)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 35)) 0 8 RSW_CB RSW_SB);
        [cbn [sv_denot RSW_CB]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold RSW_SB; zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
      * rewrite (VB 10%nat tx E10) by lia.
        split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Htxpres (tx + o) ltac:(lia))).
    + apply pairwise_disjoint_of_extents.
      unfold rsw_regions, stack_region, got_regionP, bcell_regionP, RSWR, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB 10%nat tx E10) by lia.
      rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      rewrite (VB (A_OBJ 35) (VAL (A_OBJ 35)) Ecell) by (pose proof (pa_val_range (A_OBJ 35)); lia).
      cbn [base_val]. rewrite Usp.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR Htx4096 Htxceil Htximg.
      clear. intros. repeat split; lia.
    + split; [|split; exact I].
      cbn [rsw_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, E10, E32, !unsigned_lit_small by (unfold RSW_SB; lia).
      change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 Hal16 Htx16 Htx4096 Htxceil.
      clear. unfold RSW_SB. intros. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok, rsw_SH. apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_block SEGS B LAWS ly S W mem md E RSW_CB 10 tx ATx.TX_SIZE 0 460 HAR Htx).
    + unfold U, RSW_CB. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold RSW_SB; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by lia. reflexivity.
    + lia.
    + change (req_size ATx.TX_SIZE) with 460. lia.
Qed.

Theorem pb_reac_headamp_tx_set_resweep : walk_reac_headamp_tx_set_resweep B.
Proof.
unfold walk_reac_headamp_tx_set_resweep, hyps_reac_headamp_tx_set_resweep, RT_LAWS, RT_PALIB.
intros (LAWS & TL).
unfold tb_reac_headamp_tx_set_resweep_spec.
(* The report branch 0x85ef8 (the 4-byte store at tx + 456, in the block's last partial granule, shadow 4) is
   refuted from the block's own shadow entry rsw_SH = [mkSHE 10 0 460] at the `shent_ok_of_block` step below:
   ((tx + 456) & 7) + 3 = 3 < 4 sends the slow block's `blt` back to the store, exactly as image A discharges its
   own 456 store. The contract no longer carries a separate `bytes_ok W mem (tx + 456) 4` premise for it
   (dropped at a working branch 4d7ced43548). *)
intros ly S W regs mem md ch0 tx T HPRE H10 Htx HTl HTo.
pose proof (paj_run B LAWS) as RUN.
pose proof (paj_ret_at (PL := PL_grant) (PI := PI)) as RET.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (rsw_entry LAWS TL ly S W regs mem md ch0 tx HPRE H10 Htx) as [HS SHOK].
pose proof (ajournal_init SEGS B STK_reac_headamp_tx_set_resweep [(tx + 452, tx + 460)]
  ly S W regs mem md ch0 HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchn & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : STK_reac_headamp_tx_set_resweep = 4112) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md tx ATx.TX_SIZE HAR Htx)
  as (Htx16 & Htx4096 & Htxceil & Htxia & Htxpres & _).
change (req_size ATx.TX_SIZE) with 460 in *.
remember (ERS regs) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold ERS; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 RSW_SB]) n)
  by (intros n Hn; subst E; unfold ERS; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 tx) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = getr regs 11) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 RSW_SB]) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Eu10 : bv_unsigned (ew E 10) = tx) by (rewrite E10; apply unsigned_lit_small; lia).
clear HEdef EL.
unfold cfg_at. change (w64 (BASE + AF_reac_headamp_tx_set_resweep)) with (Z_to_bv 64 RSW_P).
(* The whole body: the frame and the save of ra, the two UBSan guards (decided from atom 10's facts), the two
   shadow checks with the slow block at tx + 456, the two stores, and the return. *)
paj_run_tok RUN HS HJ SHOK RSWspan;
  [ lazymatch goal with |- awr_ok ?Ey ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok Ey rs' stk sp0 fp b0 bc lyy own) end;
    eapply awr_ok_cons_stack;
      [reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp
       | azlit_tac | azlit_tac |];
    apply awr_ok_cons_ro; [azlit_tac|];
    apply awr_ok_cons_ro; [azlit_tac|];
    eapply (awr_ok_cons_block _ _ _ _ _ _ _ _ _ _ 10%nat tx ATx.TX_SIZE);
      [reflexivity | cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Eu10
       | exact Htx | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; change (req_size ATx.TX_SIZE) with 460; lia
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
unfold tb_reac_headamp_tx_set_resweep_post, apost_base. cbv beta.
lazymatch type of HS with
| st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  exists ly, S, (ms_regs msx), (ms_mem msx); eexists;
  split; [reflexivity|];
  split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|];
  split; [eapply (aregs_preserved_of_st_ok SEGS _ Ex _ _ regs [Z_to_bv 64 RSW_SB] HS);
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
apply (proj2 (ATx.tx_obj_bytes SEGS _ tx _)).
intros i Hi. pose proof (ATx.tx_fbyte_range i Hi) as Hir.
assert (HL1 : length (Mem.upd_bytes T 452 (Mem.le4 (getr regs 11))) = 460%nat)
  by (rewrite Mem.upd_bytes_length; [exact HTl | rewrite Mem.length_le4; lia]).
unfold HdRswC.set_resweep_T.
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
  rewrite <- (proj1 (ATx.tx_obj_bytes SEGS (mrestrict (w_H W) mem) tx T) HTo i Hi).
  apply (mbyte_of_aview SEGS (w_H W) (w_H W) mem _ (tx + i)).
  apply (F2 tx ATx.TX_SIZE i Htx Htx ltac:(change (req_size ATx.TX_SIZE) with 460; lia)).
  intros (r & Hin & Hr). destruct Hin as [<- | []]. cbn [fst snd] in Hr. lia.
- destruct (Z_lt_le_dec i 456) as [Hmid | Hmid].
  + (* the period, 452..455 *)
    replace ((456 <=? Z.to_nat i)%nat && (Z.to_nat i <? 456 + 4)%nat)%bool with false
      by (symmetry; apply andb_false_iff; left; apply Nat.leb_gt; lia).
    rewrite (SegSetModel.nth_upd_bytes _ _ 452 (Z.to_nat i)) by (rewrite Mem.length_le4; lia).
    rewrite Mem.length_le4.
    replace ((452 <=? Z.to_nat i)%nat && (Z.to_nat i <? 452 + 4)%nat)%bool with true
      by (symmetry; apply andb_true_iff; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia).
    rewrite (ATx.le4_byte_of_word (getr regs 11) (Z.to_nat i - 452) ltac:(lia)).
    replace (Z.of_nat (Z.to_nat i - 452)) with (i - 452) by lia.
    rewrite <- Ex11.
    replace (tx + i) with (tx + 452 + (i - 452)) by lia.
    apply (ATx.byte_of_region SEGS _ _ 10%nat tx _ 452 460 452 460 452 4 (SOff 11 0) (i - 452) HRfin Ex10);
      [right; left; reflexivity | cbn; lia].
  + (* the counter, 456..459 *)
    replace ((456 <=? Z.to_nat i)%nat && (Z.to_nat i <? 456 + 4)%nat)%bool with true
      by (symmetry; apply andb_true_iff; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia).
    rewrite (ATx.le4_byte_of_word (Z_to_bv 64 0) (Z.to_nat i - 456) ltac:(lia)).
    replace (Z.of_nat (Z.to_nat i - 456)) with (i - 456) by lia.
    replace (tx + i) with (tx + 456 + (i - 456)) by lia.
    rewrite (ATx.byte_of_region SEGS _ _ 10%nat tx _ 452 460 452 460 456 4 (SLit 0) (i - 456) HRfin Ex10
               ltac:(left; reflexivity) ltac:(cbn; lia)).
    try (f_equal; cbn [sv_denot]; reflexivity).
Qed.

End H.
End F.
End D.
