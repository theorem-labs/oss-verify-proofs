(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import FPSteps. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import SymStepR AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AxSymExecF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AX2F.
Open Scope Z_scope.

Module AX2FS.

(* [comment removed for export] *)
Definition fx_of (ms : machine_state) : FPState := mkFP (ms_fregs ms) (ms_fcsr ms).

Lemma fx_of_mkst : forall (fx : FPState) regs pc mem rom, fx_of (@mkst fx regs pc mem rom) = fx.
Proof. intros [fr cs] regs pc mem rom. reflexivity. Qed.

Lemma fx_of_mkstR : forall (fx : FPState) regs pc mem rom rv, fx_of (@mkstR fx regs pc mem rom rv) = fx.
Proof. intros [fr cs] regs pc mem rom rv. reflexivity. Qed.

Lemma rm_okb_sound : forall rm, rm_okb rm = true -> (bv_unsigned rm <= 4 \/ bv_unsigned rm = 7)%Z.
Proof.
  intros rm H. unfold rm_okb in H. apply orb_prop in H as [H|H]; [left; apply Z.leb_le; exact H | right; apply Z.eqb_eq; exact H].
Qed.

(* [comment removed for export] *)
Lemma fp_step_fclass : forall (fx : FPState) segs regs pc mem rom w fmt rd rs1,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fclass fmt rd rs1, 4%Z) ->
  exists v : word,
  RiscvSemantics.step segs (@mkst fx regs pc mem rom) =
  MachineOk (@mkst fx (if bv_eqb rd 0 then regs else regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w fmt rd rs1 Hf He Hd.
  destruct fx as [fr cs].
  eexists. fp_pipeline Hf He Hd.
  destruct (is_x0 rd); cbv beta iota; rewrite b_npc4; [reflexivity|]. reflexivity.
Qed.

Section FSound.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition st_okXF (E : env) (base rom : word -> option byte) (ss : sym_state) (ms : machine_state) : Prop :=
  frm_zero (ms_fcsr ms) /\ @st_okX (fx_of ms) segs E base rom ss ms.

(* [comment removed for export] *)
Lemma st_okXF_entry : forall (fx : FPState) E base rom ss ms,
  frm_zero (@fp_csr fx) ->
  (forall E', eagree (s_next ss) E E' -> @st_ok fx segs E' base rom ss ms) ->
  st_okXF E base rom (clr ss) ms.
Proof.
  intros fx E base rom ss ms Hz Hst.
  destruct (Hst E (eagree_refl _ _)) as (regs & Hms & _).
  assert (Hfx : fx_of ms = fx) by (rewrite Hms; apply fx_of_mkst).
  split; [rewrite Hms; destruct fx; exact Hz|].
  rewrite Hfx. apply st_okX_clr. exact Hst.
Qed.

(* [comment removed for export] *)
Lemma st_okXF_exit : forall E base rom ss ms,
  st_okXF E base rom ss ms -> s_resv ss = None ->
  forall E', eagree (s_next ss) E E' -> @st_ok (fx_of ms) segs E' base rom ss ms.
Proof.
  intros E base rom ss ms [Hz HX] Hr E' Ha. apply st_okR_ok; [apply HX; exact Ha | exact Hr].
Qed.

Lemma st_okXF_agree : forall E E' base rom ss ms,
  st_okXF E base rom ss ms -> eagree (s_next ss) E E' -> st_okXF E' base rom ss ms.
Proof.
  intros E E' base rom ss ms [Hz HX] Ha. split; [exact Hz|]. eapply st_okX_agree; [exact HX | exact Ha].
Qed.

(* [comment removed for export] *)
Lemma find_readbase_flat_storeok : forall i fk a n,
  find_readbase i (flat_sc fk a n ++ storeok_sc fk a n) = None.
Proof.
  intros i fk a n. unfold flat_sc, storeok_sc.
  destruct (base_range fk (a_base a)) as [[lo hi]|]; [destruct (_ && _)%bool|]; destruct (wr_covered fk fk a n); reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma img_bytes_all_sound : forall lo cnt n i, img_bytes_all segs lo cnt n = true -> (0 <= i < Z.of_nat cnt)%Z ->
  exists zs, img_bytes segs (lo + i) n = Some zs.
Proof.
  intros lo cnt n. revert lo. induction cnt as [|c IH]; intros lo i H Hi; [lia|].
  cbn [img_bytes_all] in H. destruct (img_bytes segs lo n) as [zs|] eqn:Hz; [|discriminate].
  destruct (Z.eq_dec i 0) as [->|Hne].
  - rewrite Z.add_0_r. exists zs. exact Hz.
  - destruct (IH (lo + 1)%Z (i - 1)%Z H ltac:(lia)) as [zs' Hzs']. exists zs'. replace (lo + i)%Z with (lo + 1 + (i - 1))%Z by lia. exact Hzs'.
Qed.
Lemma fload_img_sound : forall E base kn e n,
  know_ok segs E base kn -> fload_img_ok segs kn e n = true ->
  exists bs, rdn segs base (edenot E e) n = Some bs.
Proof.
  intros E base kn e n Hkn H. unfold fload_img_ok in H.
  destruct (erange kn e) as [[lo hi]|] eqn:Her; [|discriminate].
  destruct (Z.leb 0 lo && Z.leb lo hi && Z.leb (hi - lo) 4096 && Z.leb (hi + Z.of_nat n) two64)%bool eqn:H1; [|discriminate].
  destruct (existsb (fun K => match K with KImg il ih => Z.leb il lo && Z.leb (hi + Z.of_nat n) ih | _ => false end) kn) eqn:Himg; [|discriminate].
  rename H into Hall. rename H1 into H. apply andb_prop in H as [H H64].
  apply andb_prop in H as [H Hw]. apply andb_prop in H as [H0 Hlh].
  apply Z.leb_le in H0. apply Z.leb_le in Hlh. apply Z.leb_le in Hw. apply Z.leb_le in H64.
  pose proof (erange_sound segs E base kn e lo hi Hkn Her) as Hv.
  apply existsb_exists in Himg as (K & HinK & HK).
  destruct K as [| | |il ih| | | | | |]; try discriminate HK. apply andb_prop in HK as [Hil Hih]. apply Z.leb_le in Hil. apply Z.leb_le in Hih.
  pose proof (proj1 (Forall_forall _ _) Hkn _ HinK) as HKI. cbn [kentry_ok] in HKI. destruct HKI as (_ & _ & Hnone).
  destruct (img_bytes_all_sound lo (Z.to_nat (hi - lo + 1)) n (bv_unsigned (edenot E e) - lo)%Z Hall ltac:(lia)) as [zs Hzs].
  replace (lo + (bv_unsigned (edenot E e) - lo))%Z with (bv_unsigned (edenot E e)) in Hzs by lia.
  unfold two64 in H64.
  destruct (rdn_img segs base n (edenot E e) zs ltac:(lia) ltac:(intros j Hj; apply Hnone; lia) Hzs) as (bs & Hbs & _).
  exists bs. exact Hbs.
Qed.

Lemma sym_stepF_fp_sound : forall (fx : FPState) E base rom ss ms i ss' scs scr' w,
  is_fp_instr i = true ->
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4%Z) ->
  sym_stepF segs i ss scr_nil = SOk ss' scs scr' ->
  x_filter segs ss ss' scs = [] -> (s_next ss <= s_next ss')%nat ->
  frm_zero (@fp_csr fx) ->
  @st_okX fx segs E base rom ss ms ->
  exists E' ms', eagree (s_next ss) E E'
    /\ RiscvSemantics.step segs ms = MachineOk ms'
    /\ st_okXF E' base rom ss' ms'.
Proof.
  intros fx E base rom ss ms i ss' scs scr' w Hfp Hf He Hd Hs Hfil Hle Hz HX.
  unfold sym_stepF in Hs. rewrite Hfp in Hs. cbn [negb] in Hs.
  destruct (s_clean ss) eqn:Hcl; [|discriminate]. cbn [negb] in Hs.
  apply s_clean_None in Hcl.
  pose proof (st_okX_R _ _ _ _ _ _ HX) as HR0.
  destruct (st_okR_parts _ E base rom ss ms HR0) as (Hregs0 & Hmem0 & Hlf0 & Hkn0 & Hms).
  rewrite Hcl in Hms. cbn [resv_denot] in Hms. rewrite mkstR_None in Hms.
  set (regs := ms_regs ms) in *.
  set (pc := Z_to_bv 64 (s_pc ss)) in *. set (MEM := mem_denot E base (s_log ss)) in *.
  pose proof (facts_of_ok segs E base _ Hkn0) as Hfk. set (fk := facts_of (s_know ss)) in *.
  (* [comment removed for export] *)
  assert (PARTS : forall E'', eagree (s_next ss) E E'' ->
            regs_ok E'' (s_regs ss) regs /\ mem_denot E'' base (s_log ss) = MEM /\ log_flat E'' (s_log ss)
            /\ know_ok segs E'' base (s_know ss)).
  { intros E'' Ha''. destruct (st_okR_parts _ E'' base rom ss ms (HX E'' Ha'')) as (R1 & M1 & L1 & K1 & _).
    split; [exact R1|]. split; [|split; [exact L1 | exact K1]]. rewrite <- Hmem0. symmetry. exact M1. }
  (* [comment removed for export] *)
  assert (GEN : forall (fx' : FPState) sr' regs' nx' E',
    frm_zero (@fp_csr fx') ->
    eagree (s_next ss) E E' -> (s_next ss <= nx')%nat ->
    (forall E'', eagree nx' E' E'' -> regs_ok E'' sr' regs') ->
    RiscvSemantics.step segs ms = MachineOk (@mkst fx' regs' (v_addi pc 4) MEM rom) ->
    exists E2 ms', eagree (s_next ss) E E2 /\ RiscvSemantics.step segs ms = MachineOk ms'
      /\ st_okXF E2 base rom (SSR (s_pc ss + 4) sr' (s_log ss) (s_know ss) nx' (s_resv ss)) ms').
  { intros fx' sr' regs' nx' E' Hz' Ha' Hle' Hregs' Hstep.
    exists E'. eexists. split; [exact Ha'|]. split; [exact Hstep|].
    split; [destruct fx'; exact Hz'|].
    rewrite fx_of_mkst. intros E'' Ha''. cbn [s_next] in Ha''.
    assert (HaE : eagree (s_next ss) E E'') by (eapply eagree_trans; [exact Ha' | eapply eagree_le; [exact Ha'' | exact Hle']]).
    destruct (PARTS E'' HaE) as (R1 & M1 & L1 & K1).
    exists regs'. cbn [s_pc s_regs s_log s_know s_resv s_next]. rewrite Hcl. cbn [resv_denot]. rewrite mkstR_None.
    split; [unfold pc; rewrite SymExec.v_addi_lit, M1; reflexivity|].
    split; [exact (Hregs' E'' Ha'')|]. split; [exact L1 | exact K1]. }
  (* [comment removed for export] *)
  assert (GEN_same : forall (fx' : FPState),
    frm_zero (@fp_csr fx') ->
    RiscvSemantics.step segs ms = MachineOk (@mkst fx' regs (v_addi pc 4) MEM rom) ->
    exists E2 ms', eagree (s_next ss) E E2 /\ RiscvSemantics.step segs ms = MachineOk ms'
      /\ st_okXF E2 base rom (sjump ss (s_pc ss + 4)) ms').
  { intros fx' Hz' Hstep. unfold sjump.
    apply (GEN fx' (s_regs ss) regs (s_next ss) E Hz' (eagree_refl _ _) ltac:(lia)); [|exact Hstep].
    intros E'' Ha''. exact (proj1 (PARTS E'' Ha'')). }
  assert (GEN_fresh : forall (fx' : FPState) rd (v : word),
    frm_zero (@fp_csr fx') ->
    RiscvSemantics.step segs ms = MachineOk (@mkst fx' (if bv_eqb rd 0 then regs else regupd regs rd v) (v_addi pc 4) MEM rom) ->
    exists E2 ms', eagree (s_next ss) E E2 /\ RiscvSemantics.step segs ms = MachineOk ms'
      /\ st_okXF E2 base rom (sfresh ss rd (s_pc ss + 4)) ms').
  { intros fx' rd v Hz' Hstep. unfold sfresh.
    apply (GEN fx' _ (if bv_eqb rd 0 then regs else regupd regs rd v) (S (s_next ss)) (eupd E (s_next ss) v) Hz' (eagree_upd _ _ _) ltac:(lia)); [|exact Hstep].
    intros E'' Ha''.
    assert (HaE : eagree (s_next ss) E E'') by (eapply eagree_trans; [apply eagree_upd | eapply eagree_le; [exact Ha'' | lia]]).
    apply regs_ok_upd; [exact (proj1 (PARTS E'' HaE))|]. cbn [edenot].
    destruct Ha'' as [Hv _]. rewrite <- (Hv (s_next ss)) by lia. apply eupd_at. }
  assert (GEN_set0 : forall (fx' : FPState) rd,
    frm_zero (@fp_csr fx') ->
    RiscvSemantics.step segs ms = MachineOk (@mkst fx' (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 0)) (v_addi pc 4) MEM rom) ->
    exists E2 ms', eagree (s_next ss) E E2 /\ RiscvSemantics.step segs ms = MachineOk ms'
      /\ st_okXF E2 base rom (sset ss rd (ELit 0) (s_pc ss + 4)) ms').
  { intros fx' rd Hz' Hstep. unfold sset.
    apply (GEN fx' _ (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 0)) (s_next ss) E Hz' (eagree_refl _ _) ltac:(lia)); [|exact Hstep].
    intros E'' Ha''. apply regs_ok_upd; [exact (proj1 (PARTS E'' Ha''))|]. apply edenot_lit. }
  (* [comment removed for export] *)
  destruct i; try discriminate Hfp.
  - (* [comment removed for export] *)
    destruct op; try discriminate.
    destruct (bv_eqb rs1 0 && Z.eqb (bv_unsigned csr) 2)%bool eqn:Hc; [|discriminate].
    injection Hs as <- <- <-. apply andb_prop in Hc as [Hrs1 Hcsr].
    assert (rs1 = 0%bv) as -> by (apply bv_eq; unfold bv_eqb in Hrs1; apply Z.eqb_eq in Hrs1; exact Hrs1).
    assert (csr = 2%bv) as -> by (apply bv_eq; apply Z.eqb_eq in Hcsr; exact Hcsr).
    destruct (GEN_set0 fx rd Hz) as (E2 & ms' & H1 & H2 & H3).
    { rewrite Hms. apply (fp_step_frrm fx segs regs pc MEM rom w rd Hf He Hd Hz). }
    exists E2, ms'. auto.
  - (* [comment removed for export] *)
    destruct op; try discriminate.
    destruct (bv_eqb rd 0 && Z.eqb (bv_unsigned csr) 1)%bool eqn:Hc; [|discriminate].
    injection Hs as <- <- <-. apply andb_prop in Hc as [Hrd Hcsr].
    assert (rd = 0%bv) as -> by (apply bv_eq; unfold bv_eqb in Hrd; apply Z.eqb_eq in Hrd; exact Hrd).
    assert (csr = 1%bv) as -> by (apply bv_eq; apply Z.eqb_eq in Hcsr; exact Hcsr).
    destruct (fp_step_csrsi_fflags fx segs regs pc MEM rom w uimm Hf He Hd Hz) as (cs' & Hz' & Hstep).
    destruct (GEN_same (mkFP (@fp_regs fx) cs') Hz') as (E2 & ms' & H1 & H2 & H3); [rewrite Hms; exact Hstep|].
    exists E2, ms'. auto.
  - (* [comment removed for export] *)
    set (n := fmt_bytes fmt) in Hs.
    set (a := to_saddrK fk (sr_get (s_regs ss) rs1) (bv_signed imm)) in Hs.
    destruct ((match s_log ss with [] => true | _ => false end
               && fload_img_ok segs (s_know ss) (mkAlu ALU_ADD (sr_get (s_regs ss) rs1) (ELit (bv_signed imm))) n)%bool) eqn:Himg.
    { (* [comment removed for export] *)
      destruct (s_log ss) as [|le lrest] eqn:Hlog; [|discriminate Himg].
      cbn [andb] in Himg. rename Himg into Hok.
      injection Hs as <- <- <-.
      assert (Hn18 : (1 <= n)%nat /\ (n <= 8)%nat) by (unfold n; destruct fmt; cbn; lia). destruct Hn18 as [Hn1 Hn8].
      destruct (PARTS E (eagree_refl _ _)) as (R1 & M1 & L1 & K1).
      destruct (fload_img_sound E base (s_know ss) _ n K1 Hok) as [bs Hrd].
      rewrite mkAlu_denot, edenot_lit, alu_add, v_add_lit, <- (R1 rs1) in Hrd.
      change (v_addi (getr regs rs1) (bv_signed imm)) with (v_addi (getr regs rs1) (bv_signed imm)) in Hrd || idtac.
      assert (HM : MEM = base) by reflexivity.
      destruct fmt.
      + destruct (GEN (mkFP (bvmap_set rd (nan_box (bv_extract 0 32 (le_bytes_to_word bs))) (@fp_regs fx)) (@fp_csr fx))
                     (s_regs ss) regs (s_next ss) E Hz (eagree_refl _ _) ltac:(lia)) as (E2 & ms' & H1 & H2 & H3).
        { intros E'' Ha''. apply (proj1 (PARTS E'' Ha'')). }
        { rewrite Hms, HM. apply (fp_step_flw fx segs regs pc base rom w rd rs1 imm _ bs Hf He Hd eq_refl). exact Hrd. }
        exists E2, ms'. auto.
      + destruct (GEN (mkFP (bvmap_set rd (bv_extract 0 64 (le_bytes_to_word bs)) (@fp_regs fx)) (@fp_csr fx))
                     (s_regs ss) regs (s_next ss) E Hz (eagree_refl _ _) ltac:(lia)) as (E2 & ms' & H1 & H2 & H3).
        { intros E'' Ha''. apply (proj1 (PARTS E'' Ha'')). }
        { rewrite Hms, HM. apply (fp_step_fld fx segs regs pc base rom w rd rs1 imm _ bs Hf He Hd eq_refl). exact Hrd. }
        exists E2, ms'. auto. }
    destruct (sym_read segs ss fk scr_nil a n false) as [[[[v0 rscs] rscr] nx']|] eqn:Hr; [|discriminate Hs].
    injection Hs as <- <- <-. cbn [s_next] in Hle.
    assert (Hn18 : (1 <= n)%nat /\ (n <= 8)%nat) by (unfold n; destruct fmt; cbn; lia). destruct Hn18 as [Hn1 Hn8].
    (* [comment removed for export] *)
    destruct (x_scs_valuation segs E base rom ss (SSR (s_pc ss + 4) (s_regs ss) (s_log ss) (s_know ss) nx' (s_resv ss)) rscs ms
                Hfil Hle HX) as (E1 & Ha1 & Hscs).
    destruct (PARTS E1 Ha1) as (R1 & M1 & L1 & K1).
    destruct (sym_read_sound segs E1 base ss scr_nil a n false v0 rscs rscr nx' Hr (Hscs E1 (eagree_refl _ _)) L1 K1 Hn1 Hn8)
      as [Hfl (bs & Hrd & Hlen & _)].
    rewrite M1 in Hrd.
    assert (Hadr : adenot E1 a = v_addi (getr regs rs1) (bv_signed imm)).
    { subst a. rewrite (to_saddrK_denot segs E1 base fk _ _ (facts_of_ok segs E1 base _ K1)), R1. reflexivity. }
    rewrite Hadr in Hrd.
    destruct fmt.
    + (* [comment removed for export] *)
      destruct (GEN (mkFP (bvmap_set rd (nan_box (bv_extract 0 32 (le_bytes_to_word bs))) (@fp_regs fx)) (@fp_csr fx))
                   (s_regs ss) regs nx' E1 Hz Ha1 Hle) as (E2 & ms' & H1 & H2 & H3).
      { intros E'' Ha''. apply (proj1 (PARTS E'' ltac:(eapply eagree_trans; [exact Ha1 | eapply eagree_le; [exact Ha'' | exact Hle]]))). }
      { rewrite Hms. apply (fp_step_flw fx segs regs pc MEM rom w rd rs1 imm _ bs Hf He Hd eq_refl). exact Hrd. }
      exists E2, ms'. auto.
    + (* [comment removed for export] *)
      destruct (GEN (mkFP (bvmap_set rd (bv_extract 0 64 (le_bytes_to_word bs)) (@fp_regs fx)) (@fp_csr fx))
                   (s_regs ss) regs nx' E1 Hz Ha1 Hle) as (E2 & ms' & H1 & H2 & H3).
      { intros E'' Ha''. apply (proj1 (PARTS E'' ltac:(eapply eagree_trans; [exact Ha1 | eapply eagree_le; [exact Ha'' | exact Hle]]))). }
      { rewrite Hms. apply (fp_step_fld fx segs regs pc MEM rom w rd rs1 imm _ bs Hf He Hd eq_refl). exact Hrd. }
      exists E2, ms'. auto.
  - (* [comment removed for export] *)
    set (n := fmt_bytes fmt) in *.
    set (a := to_saddrK fk (sr_get (s_regs ss) rs1) (bv_signed imm)) in *.
    injection Hs as <- <- <-.
    assert (Hn18 : (1 <= n)%nat /\ (n <= 8)%nat) by (unfold n; destruct fmt; cbn; lia). destruct Hn18 as [Hn1 Hn8].
    (* [comment removed for export] *)
    set (sval := match fmt with
                 | FMT_D => reg_get (@fp_regs fx) rs2
                 | FMT_S => Z_to_bv 64 (bv_unsigned (low32 (reg_get (@fp_regs fx) rs2)))
                 end).
    set (E' := eupd E (s_next ss) sval).
    assert (Ha' : eagree (s_next ss) E E') by apply eagree_upd.
    (* [comment removed for export] *)
    assert (SCS : forall E'', eagree (s_next ss) E E'' -> scs_denot segs base E'' (flat_sc fk a n ++ storeok_sc fk a n)).
    { intros E'' Ha''. destruct (PARTS E'' Ha'') as (_ & _ & _ & K1).
      unfold scs_denot. apply Forall_forall. intros sc Hin.
      eapply (x_discharge_sound segs E E'' base ss _ (find_readbase (s_next ss) (flat_sc fk a n ++ storeok_sc fk a n)));
        [exact K1 | exact Ha'' | eapply (x_filter_nil segs); [exact Hfil|exact Hin] | ].
      rewrite find_readbase_flat_storeok. intros; discriminate. }
    assert (ADR : forall E'', eagree (s_next ss) E E'' -> adenot E'' a = v_addi (getr regs rs1) (bv_signed imm)).
    { intros E'' Ha''. destruct (PARTS E'' Ha'') as (R1 & _ & _ & K1).
      subst a. rewrite (to_saddrK_denot segs E'' base fk _ _ (facts_of_ok segs E'' base _ K1)), R1. reflexivity. }
    assert (FLOK : forall E'', eagree (s_next ss) E E'' ->
              flat E'' a (Z.of_nat n) /\ RiscvSemantics.store_ok segs MEM (v_addi (getr regs rs1) (bv_signed imm)) n = true).
    { intros E'' Ha''. destruct (PARTS E'' Ha'') as (R1 & M1 & _ & K1).
      pose proof (facts_of_ok segs E'' base _ K1) as Hfk''.
      destruct (flat_sc_sound segs E'' base fk _ _ _ Hfk'' Hn1 Hn8 (SCS E'' Ha'')) as [Hfl Hsc].
      split; [exact Hfl|].
      pose proof (storeok_sc_sound segs E'' base fk a n Hfk'' Hfl Hn1 Hn8 Hsc) as Hok.
      rewrite <- (ADR E'' Ha''). rewrite <- M1. eapply store_ok_mono; [apply mem_denot_grows | exact Hok]. }
    destruct (FLOK E (eagree_refl _ _)) as [_ Hok].
    exists E'. eexists. split; [exact Ha'|].
    assert (STEP : RiscvSemantics.step segs ms =
                   MachineOk (@mkst fx regs (v_addi pc 4) (wbytes MEM (v_addi (getr regs rs1) (bv_signed imm)) (word_to_le_bytes n sval)) rom)).
    { rewrite Hms. destruct fmt.
      - rewrite (fp_step_fsw fx segs regs pc MEM rom w rs1 rs2 imm _ Hf He Hd eq_refl Hok). do 2 f_equal.
        unfold sval, word_to_le_bytes. rewrite u_small; [reflexivity|].
        pose proof (bv_unsigned_in_range _ (low32 (reg_get (@fp_regs fx) rs2))) as Hr32. unfold bv_modulus in Hr32. cbn in Hr32. lia.
      - rewrite (fp_step_fsd fx segs regs pc MEM rom w rs1 rs2 imm _ Hf He Hd eq_refl Hok). reflexivity. }
    split; [exact STEP|].
    split; [cbn [ms_fcsr mkst]; destruct fx; exact Hz|].
    rewrite fx_of_mkst. intros E'' Ha''. cbn [s_next] in Ha''.
    assert (HaE : eagree (s_next ss) E E'') by (eapply eagree_trans; [exact Ha' | eapply eagree_le; [exact Ha'' | lia]]).
    destruct (PARTS E'' HaE) as (R1 & M1 & L1 & K1). destruct (FLOK E'' HaE) as [Hfl'' _].
    exists regs. cbn [s_pc s_regs s_log s_know s_resv]. rewrite Hcl. cbn [resv_denot mem_denot]. rewrite mkstR_None.
    split.
    + unfold pc. rewrite SymExec.v_addi_lit, M1, (ADR E'' HaE). cbn [edenot].
      destruct Ha'' as [Hv _]. rewrite <- (Hv (s_next ss)) by lia. unfold E'. rewrite eupd_at. reflexivity.
    + split; [exact R1|]. split; [|exact K1]. cbn [log_flat]. split; [exact Hn8|]. split; [exact Hfl'' | exact L1].
  - (* [comment removed for export] *) discriminate.
  - (* [comment removed for export] *)
    destruct (rm_okb rm) eqn:Hrm; [|discriminate]. injection Hs as <- <- <-.
    destruct (fp_step_fari fx segs regs pc MEM rom w op fmt rd rs1 rs2 rm Hf He Hd Hz (rm_okb_sound rm Hrm)) as (fr' & cs' & Hz' & Hstep).
    destruct (GEN_same (mkFP fr' cs') Hz') as (E2 & ms' & H1 & H2 & H3); [rewrite Hms; exact Hstep|].
    exists E2, ms'. auto.
  - (* [comment removed for export] *) discriminate.
  - (* [comment removed for export] *)
    injection Hs as <- <- <-.
    destruct (fp_step_fsgnj fx segs regs pc MEM rom w op fmt rd rs1 rs2 Hf He Hd) as (fr' & Hstep).
    destruct (GEN_same (mkFP fr' (@fp_csr fx)) Hz) as (E2 & ms' & H1 & H2 & H3); [rewrite Hms; exact Hstep|].
    exists E2, ms'. auto.
  - (* [comment removed for export] *) discriminate.
  - (* [comment removed for export] *)
    injection Hs as <- <- <-.
    destruct (fp_step_fcmp fx segs regs pc MEM rom w op fmt rd rs1 rs2 Hf He Hd Hz) as (b & cs' & Hz' & Hstep).
    destruct (GEN_fresh (mkFP (@fp_regs fx) cs') rd (if b then Z_to_bv 64 1 else Z_to_bv 64 0) Hz') as (E2 & ms' & H1 & H2 & H3);
      [rewrite Hms; exact Hstep|].
    exists E2, ms'. auto.
  - (* [comment removed for export] *)
    destruct (rm_okb rm) eqn:Hrm; [|discriminate]. cbn [negb] in Hs.
    pose proof (rm_okb_sound rm Hrm) as Hrm'.
    destruct (fcvt_is_fp dst) eqn:Hdst.
    + injection Hs as <- <- <-.
      assert (Hdst' : dst = FC_S \/ dst = FC_D) by (destruct dst; try discriminate; auto).
      destruct (fp_step_fcvt_to_f fx segs regs pc MEM rom w dst src rd rs1 rm Hf He Hd Hdst' Hz Hrm') as (fr' & cs' & Hz' & Hstep).
      destruct (GEN_same (mkFP fr' cs') Hz') as (E2 & ms' & H1 & H2 & H3); [rewrite Hms; exact Hstep|].
      exists E2, ms'. auto.
    + destruct (fcvt_is_fp src) eqn:Hsrc; [|discriminate]. injection Hs as <- <- <-.
      assert (Hdst' : dst = FC_W \/ dst = FC_WU \/ dst = FC_L \/ dst = FC_LU) by (destruct dst; try discriminate; auto).
      assert (Hsrc' : src = FC_S \/ src = FC_D) by (destruct src; try discriminate; auto).
      destruct (fp_step_fcvt_to_x fx segs regs pc MEM rom w dst src rd rs1 rm Hf He Hd Hdst' Hsrc' Hz Hrm') as (v & cs' & Hz' & Hstep).
      destruct (GEN_fresh (mkFP (@fp_regs fx) cs') rd v Hz') as (E2 & ms' & H1 & H2 & H3); [rewrite Hms; exact Hstep|].
      exists E2, ms'. auto.
  - (* [comment removed for export] *)
    destruct dir.
    + (* [comment removed for export] *)
      injection Hs as <- <- <-.
      destruct fmt.
      * destruct (GEN_fresh fx rd (sext 64 (low32 (reg_get (@fp_regs fx) rs1))) Hz) as (E2 & ms' & H1 & H2 & H3);
          [rewrite Hms; apply (fp_step_fmv_x_w fx segs regs pc MEM rom w rd rs1 Hf He Hd)|].
        exists E2, ms'. auto.
      * destruct (GEN_fresh fx rd (reg_get (@fp_regs fx) rs1) Hz) as (E2 & ms' & H1 & H2 & H3);
          [rewrite Hms; apply (fp_step_fmv_x_d fx segs regs pc MEM rom w rd rs1 Hf He Hd)|].
        exists E2, ms'. auto.
    + (* [comment removed for export] *)
      injection Hs as <- <- <-.
      destruct fmt.
      * destruct (GEN_same (mkFP (bvmap_set rd (nan_box (low32 (getr regs rs1))) (@fp_regs fx)) (@fp_csr fx)) Hz) as (E2 & ms' & H1 & H2 & H3);
          [rewrite Hms; apply (fp_step_fmv_w_x fx segs regs pc MEM rom w rd rs1 Hf He Hd)|].
        exists E2, ms'. auto.
      * destruct (GEN_same (mkFP (bvmap_set rd (getr regs rs1) (@fp_regs fx)) (@fp_csr fx)) Hz) as (E2 & ms' & H1 & H2 & H3);
          [rewrite Hms; apply (fp_step_fmv_d_x fx segs regs pc MEM rom w rd rs1 Hf He Hd)|].
        exists E2, ms'. auto.
  - (* [comment removed for export] *)
    injection Hs as <- <- <-.
    destruct (fp_step_fclass fx segs regs pc MEM rom w fmt rd rs1 Hf He Hd) as (v & Hstep).
    destruct (GEN_fresh fx rd v Hz) as (E2 & ms' & H1 & H2 & H3); [rewrite Hms; exact Hstep|].
    exists E2, ms'. auto.
Qed.

(* [comment removed for export] *)
Lemma sym_stepXF_sound : forall K E base rom ss ms i ssx scr' w,
  fetch_word segs (Z_to_bv 64 (s_pc ss)) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (i, 4%Z) ->
  sym_stepXF segs K i ss scr_nil = SOk ssx [] scr' ->
  st_okXF E base rom ss ms ->
  exists E' ms', eagree (s_next ss) E E'
    /\ (s_next ss <= s_next ssx)%nat
    /\ RiscvSemantics.step segs ms = MachineOk ms'
    /\ st_okXF E' base rom ssx ms'.
Proof.
  intros K E base rom ss ms i ssx scr' w Hf He Hd H [Hz HX].
  destruct (is_fp_instr i) eqn:Hfp.
  - unfold sym_stepXF in H.
    destruct (sym_stepF segs i ss scr_nil) as [ss' scs scr2|] eqn:Hst; [|discriminate].
    destruct (Nat.leb (s_next ss) (s_next ss')) eqn:Hle; [|discriminate]. apply Nat.leb_le in Hle.
    injection H as Hss Hfil Hscr. subst ssx scr'.
    destruct (sym_stepF_fp_sound (fx_of ms) E base rom ss ms i ss' scs scr2 w Hfp Hf He Hd Hst Hfil Hle
                ltac:(destruct ms; exact Hz) HX) as (E' & ms' & Ha & Hstep & HXF).
    exists E', ms'. split; [exact Ha|]. split; [rewrite (cap_rd_fp K i ss' Hfp); exact Hle|].
    split; [exact Hstep|]. rewrite (cap_rd_fp K i ss' Hfp). exact HXF.
  - rewrite (sym_stepXF_notfp segs K i ss scr_nil Hfp) in H.
    destruct (@sym_stepX_sound (fx_of ms) segs K E base rom ss ms i ssx scr' w Hf He Hd H HX) as (E' & ms' & Ha & Hle & Hstep & HX').
    exists E', ms'. split; [exact Ha|]. split; [exact Hle|]. split; [exact Hstep|].
    pose proof (st_okX_fx' := @st_okX_R (fx_of ms) segs _ _ _ _ _ HX').
    destruct st_okX_fx' as (rr & Hms' & _).
    assert (Hfx : fx_of ms' = fx_of ms) by (rewrite Hms'; apply fx_of_mkstR).
    split.
    + rewrite Hms'. exact Hz.
    + rewrite Hfx. exact HX'.
Qed.

(* [comment removed for export] *)
Lemma sym_execTXF_go_sound : forall t K fuel first stops ss ck base rom,
  itab_sound segs t ->
  sym_execTXF_go segs t K fuel first stops ss ck = ck \/
  (let r := sym_execTXF_go segs t K fuel first stops ss ck in
   s_resv r = None /\ (s_next ss <= s_next r)%nat /\
   (forall E ms, st_okXF E base rom ss ms ->
      exists E' mr, eagree (s_next ss) E E' /\ msteps segs ms mr /\ st_okXF E' base rom r mr)).
Proof.
  intros t K fuel. induction fuel as [|f IH]; intros first stops ss ck base rom Ht.
  - cbn [sym_execTXF_go]. destruct (s_clean ss) eqn:Hc; [right|left; reflexivity].
    split; [apply s_clean_None; exact Hc|]. split; [lia|].
    intros E ms Hst. exists E, ms. split; [apply eagree_refl|]. split; [apply mst_refl|exact Hst].
  - assert (Hstop : (if s_clean ss then ss else ck) = ck \/
            (let r := (if s_clean ss then ss else ck) in
             s_resv r = None /\ (s_next ss <= s_next r)%nat /\
             (forall E ms, st_okXF E base rom ss ms ->
                exists E' mr, eagree (s_next ss) E E' /\ msteps segs ms mr /\ st_okXF E' base rom r mr))).
    { destruct (s_clean ss) eqn:Hc; [right|left; reflexivity].
      split; [apply s_clean_None; exact Hc|]. split; [lia|].
      intros E ms Hst. exists E, ms. split; [apply eagree_refl|]. split; [apply mst_refl|exact Hst]. }
    cbn [sym_execTXF_go].
    destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [exact Hstop|].
    destruct (itab_lookup t (s_pc ss)) as [i|] eqn:Hl; [|exact Hstop].
    pose proof (Ht _ _ Hl) as Hen. unfold itab_entry in Hen.
    destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|] eqn:Hf; [|discriminate].
    destruct (is_ecall w) eqn:Hec; [discriminate|].
    destruct (decode_any w) as [[i' sz]|] eqn:Hd; [|discriminate].
    destruct (Z.eqb sz 4) eqn:Hsz; [|discriminate]. apply Z.eqb_eq in Hsz. subst sz.
    injection Hen as ->.
    destruct (sym_stepXF segs K i ss scr_nil) as [ss2 scs2 scr2|] eqn:Hstep; [|exact Hstop].
    destruct scs2 as [|x l]; [|exact Hstop].
    set (ck' := if s_clean ss2 then ss2 else ck).
    specialize (IH false stops ss2 ck' base rom Ht).
    (* [comment removed for export] *)
    assert (HLE : (s_next ss <= s_next ss2)%nat).
    { unfold sym_stepXF in Hstep. destruct (sym_stepF segs i ss scr_nil) as [ss3 scs3 scr3|]; [|discriminate].
      destruct (Nat.leb (s_next ss) (s_next ss3)) eqn:Hle3; [|discriminate]. apply Nat.leb_le in Hle3.
      injection Hstep as <- _ _. unfold cap_rd. destruct K; [exact Hle3|].
      destruct (rd_of i); [|exact Hle3]. destruct (bv_eqb _ _); [exact Hle3|]. destruct (esize_le _ _); [exact Hle3|].
      cbn [s_next]. lia. }
    assert (ONE : forall E ms, st_okXF E base rom ss ms ->
              exists E' msA, eagree (s_next ss) E E' /\ msteps segs ms msA /\ st_okXF E' base rom ss2 msA).
    { intros E ms Hst.
      destruct (sym_stepXF_sound K E base rom ss ms i ss2 scr2 w Hf Hec Hd Hstep Hst) as (E' & msA & Ha & Hle & HstepA & HstA).
      exists E', msA. split; [exact Ha|]. split; [|exact HstA].
      eapply mst_step; [destruct (st_okX_R _ _ _ _ _ _ (proj2 Hst)) as (rr & -> & _); reflexivity | exact HstepA | apply mst_refl]. }
    destruct IH as [Hck|(Hr & Hle2 & Hrun)].
    + subst ck'. destruct (s_clean ss2) eqn:Hc2.
      * right. rewrite Hck. split; [apply s_clean_None; exact Hc2|]. split; [exact HLE|].
        intros E ms Hst. destruct (ONE E ms Hst) as (E' & msA & Ha & Hms & HstA).
        exists E', msA. split; [exact Ha|]. split; [exact Hms | exact HstA].
      * left. exact Hck.
    + right. split; [exact Hr|]. split; [lia|].
      intros E ms Hst.
      destruct (ONE E ms Hst) as (E' & msA & Ha & HmsA & HstA).
      destruct (Hrun E' msA HstA) as (E2 & mr & Ha2 & Hmr & Hstr).
      exists E2, mr. split; [|split; [eapply msteps_trans; [exact HmsA | exact Hmr] | exact Hstr]].
      eapply eagree_trans; [exact Ha | eapply eagree_le; [exact Ha2 | exact HLE]].
Qed.

(* [comment removed for export] *)
Theorem sym_execTXF_sound : forall (fx : FPState) t K fuel first stops ss E base rom ms,
  itab_sound segs t ->
  frm_zero (@fp_csr fx) ->
  (forall E', eagree (s_next ss) E E' -> @st_ok fx segs E' base rom ss ms) ->
  let ss' := sym_execTXF segs t K fuel first stops ss in
  exists E' ms', eagree (s_next ss) E E'
    /\ (s_next ss <= s_next ss')%nat
    /\ msteps segs ms ms'
    /\ frm_zero (ms_fcsr ms')
    /\ (forall E'', eagree (s_next ss') E' E'' -> @st_ok (fx_of ms') segs E'' base rom ss' ms').
Proof.
  intros fx t K fuel first stops ss E base rom ms Ht Hz Hst. unfold sym_execTXF.
  pose proof (st_okXF_entry fx E base rom ss ms Hz Hst) as HXF.
  destruct (sym_execTXF_go_sound t K fuel first stops (clr ss) (clr ss) base rom Ht) as [Hck|(Hr & Hle & Hrun)].
  - rewrite Hck. exists E, ms. split; [apply eagree_refl|]. split; [cbn [s_next clr]; lia|].
    split; [apply mst_refl|]. split; [exact (proj1 HXF)|].
    intros E'' Ha. eapply st_okXF_exit; [exact HXF | reflexivity | exact Ha].
  - destruct (Hrun E ms HXF) as (E' & mr & Ha & Hmr & HXF').
    exists E', mr. split; [exact Ha|]. split; [exact Hle|]. split; [exact Hmr|]. split; [exact (proj1 HXF')|].
    intros E'' Ha''. eapply st_okXF_exit; [exact HXF' | exact Hr | exact Ha''].
Qed.

Theorem sym_execTXF_ex : forall (fx : FPState) t K fuel first stops ss E base rom ms,
  itab_sound segs t ->
  frm_zero (@fp_csr fx) ->
  (forall E', eagree (s_next ss) E E' -> @st_ok fx segs E' base rom ss ms) ->
  let ss' := sym_execTXF segs t K fuel first stops ss in
  exists E' R (fx' : FPState), eagree (s_next ss) E E'
    /\ (s_next ss <= s_next ss')%nat
    /\ regs_ok E' (s_regs ss') R
    /\ log_flat E' (s_log ss')
    /\ know_ok segs E' base (s_know ss')
    /\ frm_zero (@fp_csr fx')
    /\ msteps segs ms (@mkst fx' R (Z_to_bv 64 (s_pc ss')) (mem_denot E' base (s_log ss')) rom)
    /\ (forall E'', eagree (s_next ss') E' E'' ->
          @st_ok fx' segs E'' base rom ss' (@mkst fx' R (Z_to_bv 64 (s_pc ss')) (mem_denot E' base (s_log ss')) rom)).
Proof.
  intros fx t K fuel first stops ss E base rom ms Ht Hz Hst.
  destruct (sym_execTXF_sound fx t K fuel first stops ss E base rom ms Ht Hz Hst) as (E' & ms' & Ha & Hle & Hms & Hz' & HALL).
  destruct (HALL E' (eagree_refl _ _)) as (R & Heq & Hregs & Hlf & Hkn).
  exists E', R, (fx_of ms'). split; [exact Ha|]. split; [exact Hle|]. split; [exact Hregs|]. split; [exact Hlf|]. split; [exact Hkn|].
  split; [destruct ms'; exact Hz'|].
  rewrite <- Heq. split; [exact Hms | exact HALL].
Qed.

Theorem sym_execTXF_resv : forall t K fuel first stops ss,
  itab_sound segs t -> s_resv (sym_execTXF segs t K fuel first stops ss) = None.
Proof.
  intros t K fuel first stops ss Ht. unfold sym_execTXF.
  destruct (sym_execTXF_go_sound t K fuel first stops (clr ss) (clr ss) (fun _ => None) (fun _ => None) Ht) as [Hck|(Hr & _)].
  - rewrite Hck. reflexivity.
  - exact Hr.
Qed.

End FSound.
End AX2FS.
