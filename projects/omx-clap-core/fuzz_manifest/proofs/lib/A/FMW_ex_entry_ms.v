(* G4.ExEntry: the scan's setup 0x81200..0x8125c (fuzz_manifest.c:134) from EX_MS to EX_L with i = d = 0: the nine frame
   slots (ex_slots, d = 0), s3 = 0, s1 = '@', s6 = 6, s2 = 5, s0 = ' ', a5 = ':', a6 = the NUL/space mask; the answer
   is the scan's (whole = false). ex_MS_seg (FMW_ex_entry_kit.v). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib FMW_ex_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_ex_entry_kit.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* EX_MS: sp = F (atom 2), the frame with a write window over the nine slots F+0x18 .. F+0x67 *)
Definition ems_frame : YP09.region := YP09.mkRegion (Some 2%nat) 0 208 0x18 0x68 [].
Definition ss_MS : sstate := mkSS EX_MS sr_atoms [ems_frame] None (mkFacts [(2%nat, EE_SP)] [] []).

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Lemma ems_cfg : forall (W : world tfibsegs) pc regs mem md Q,
  SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) Q ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs)) md) Q.
Proof. intros W pc regs mem md Q H. exact H. Qed.

Lemma ems_entry : forall (W : world tfibsegs) mem regs3 Fz,
  getr regs3 2 = w64 Fz -> 2 ^ 46 <= Fz <= 2 ^ 47 - 208 -> Fz mod 16 = 0 ->
  (forall a, Fz + 0x18 <= a < Fz + 0x68 -> apresent (w_H W) mem a) ->
  st_ok tfibsegs (Ereg regs3 []) ss_MS (restrict (w_H W) (mkst regs3 (Z_to_bv 64 EX_MS) mem (seg_rom tfibsegs))).
Proof.
  intros W mem regs3 Fz R2 HF1 HF2 Hpr.
  rewrite restrict_mkst_fx.
  set (E := Ereg regs3 []).
  assert (U2 : bv_unsigned (ew E 2) = Fz)
    by (unfold E; rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
  unfold ss_MS. apply (entry_st_ok_full tfibsegs); change (Ereg regs3 []) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, ems_frame.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U2.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable tfibsegs). apply Hpr. lia.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok, EE_SP. cbn [af_lo af_hi af_al2].
    rewrite U2. change (2 ^ 4) with 16. split; [|exact I]. split; [lia|]. split; [exact HF2 | lia].
Qed.

Theorem ex_MS_holds : ex_MS_seg B.
Proof.
  intros cx ly3 S3 W3 regs3 mem3 md3 HK ((HB & HC & Hn & R9 & R18 & R23) & Hwh).
  pose proof (AR_laws_ok tfibsegs B) as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (ee_base_facts B cx HB) as (Hal & Hsp & Hsp47 & _ & _).
  assert (HSTK : STK_expected = 8432) by reflexivity.
  pose proof HC as (HJ & Hbl & HGL & R2 & R3 & R4 & R25 & HSV & HRO & Ct & Cu & Kt & Ku).
  pose proof Ct as (_ & Ht4 & Htc & _). pose proof Cu as (_ & Hu4 & Huc & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & Hlen & _).
  assert (HFe : cx_F cx = cx_sp cx - 208) by reflexivity.
  assert (HFm : cx_F cx mod 16 = 0).
  { rewrite HFe. replace (cx_sp cx - 208) with (cx_sp cx + (-13) * 16) by lia. rewrite Z_mod_plus_full. exact Hal. }
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  pose proof (ems_entry W3 mem3 regs3 (cx_F cx) R2 ltac:(rewrite HFe; lia) HFm
    ltac:(intros a Ha; apply Hpres; rewrite HFe in Ha; lia)) as HS.
  set (E := Ereg regs3 []) in *.
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs3 q)
    by (intros n q Hnq; subst E; apply ew_Ereg_nat; exact Hnq).
  assert (U2 : bv_unsigned (ew E 2) = cx_F cx)
    by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; rewrite HFe; lia).
  assert (SHOK : sh_ok tfibsegs EE_Bx [] E
    (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 EX_MS) mem3 (seg_rom tfibsegs))))) by constructor.
  change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 EX_MS) mem3 (seg_rom tfibsegs))) in HJ.
  unfold cfg_at. change (w64 EX_MS) with (Z_to_bv 64 EX_MS).
  aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan EX_L.
  { (* named arguments and both shapes of awr_ok: the core may put `segs B` in front (Reloc aeb12aaa12b) *)
    first
      [ lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
          let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end
      | lazymatch goal with |- awr_ok ?sg ?Bv ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
          let rs' := eval vm_compute in rs in change (awr_ok sg Bv E rs' stk sp0 fp b0 bc ly own) end ];
    eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -208);
      [reflexivity | rewrite U2, HFe; lia | cbn; lia | cbn; lia | apply awr_ok_nil]. }
  (* the memory: changed only in the slot window *)
  pose proof (fw_win tfibsegs _ _ _ _ _ (cx_sp cx - STK_expected) (cx_F cx + 104) HFr) as KW.
  assert (KM : ee_kept W3 (cx_sp cx - STK_expected) (cx_F cx + 104) mem3 (ms_mem ms)).
  { intros a Ha Hn'. apply KW; [|exact Ha|exact Hn'].
    lazymatch goal with |- Forall _ ?rs => let v := eval vm_compute in rs in change rs with v end.
    repeat apply Forall_cons; try apply Forall_nil;
      cbn [YP09.r_whi YP09.r_wlo YP09.r_base base_val]; first [left; lia | right; rewrite U2; rewrite HFe; lia]. }
  clear KW.
  (* the slots, from the run's frame region *)
  assert (HSL : ex_slots cx W3 (ms_mem ms) 0).
  { lazymatch type of HS with st_ok _ _ ?ss _ =>
      let r := eval vm_compute in (nth_error (ss_mem ss) 0) in
      lazymatch r with Some ?rg =>
        pose proof (fw_region_nth tfibsegs _ ss _ 0 rg HS ltac:(vm_compute; reflexivity)) as HR end end.
    rewrite restrict_mem in HR.
    unfold ex_slots.
    repeat split;
    lazymatch goal with |- val_mem _ _ (cx_F cx + ?o) 8 ?v =>
      eapply (fw_field tfibsegs E _ 2 (cx_F cx) _ _ _ _ _ o 8 _ v HR U2);
      [ cbn [In]; repeat (first [left; reflexivity | right])
      | ..
      | cbn; lia ] end.
    all: first
      [ reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64);
        first [apply Z.mod_pos_bound; lia | unfold cx_n, EX_PREFIX, EX_MASK1; lia]
      | cbn [sv_denot]; rewrite (EE 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R9
      | cbn [sv_denot]; rewrite (EE 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R18
      | cbn [sv_denot]; rewrite (EE 23%nat 23%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R23
      | cbn [sv_denot]; rewrite (EE 23%nat 23%bv eq_refl), R23; unfold w64;
        rewrite unsigned_lit_small by lia; reflexivity
      | cbn [sv_denot]; rewrite (EE 9%nat 9%bv eq_refl), (EE 23%nat 23%bv eq_refl), R9, R23; unfold w64;
        rewrite !unsigned_lit_small by lia; rewrite Z.add_0_r, zmd64_sound, zalu64_sound;
        apply Z_to_bv64_eq_mod; unfold zalu64, zmd64, zcanon, M64; cbn [zalu_raw zmd_raw];
        rewrite !Z.mod_mod by lia; rewrite <- Z.mul_mod by lia; rewrite <- Z.add_mod by lia;
        replace (cx_u cx + -2 + cx_t cx * 18446744073709551615) with ((cx_u cx - cx_t cx - 2) + cx_t cx * 2 ^ 64)
          by lia;
        rewrite Z_mod_plus_full; reflexivity ]. }
  ee_mk HS. apply ems_cfg.
  apply (HK ly3 S3 W3 (ms_regs ms) (ms_mem ms) _).
  split; [exact HB|]. split.
  { apply (ee_com_keep B cx ly3 S3 W3 regs3 mem3 md3 _ _ _ HB HC HJ KM);
      ee_g HS; apply EE; reflexivity. }
  split; [exact HSL|].
  split.
  { split; [ee_g HS; rewrite (EE 23%nat 23%bv eq_refl); exact R23|].
    split; [ee_g HS; reflexivity|]. split; [ee_g HS; reflexivity|]. ee_g HS; reflexivity. }
  split.
  { split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hn|].
    unfold cx_res. apply ee_names_scan; assumption. }
  split; [ee_g HS; reflexivity|]. split; [ee_g HS; reflexivity|].
  split; [ee_g HS; reflexivity | ee_g HS; reflexivity].
Qed.
End W.

Print Assumptions ex_MS_holds.
