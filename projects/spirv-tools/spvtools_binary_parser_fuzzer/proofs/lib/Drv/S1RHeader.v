(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb AllocCeil RunRandom PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes ShapeLaws MmapSim FileSim AgentLib Frame SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibWritev RefNodes RefMemcpyLib Hoare LibMaskBits SRealizes SNodes SLibWritev LibIface LibBudget S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import SymDriveS2 RunsLib S1CxxTable StaticsGen S1Statics S1SpecConsts S1Spec S1ExitBase S1StdioDefs S1ExitKn S1ExitDefs S1Exit S1ExitGlue S1LibStdioCall S1RwWindow S1Cells S1KnCells S1KnIvs
  S1AddrFacts S1RBase S1RKn DrvMallocT S1RLoopN S1TargetDefs S1TargetBlocks.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import S1MainEntry S1RHeader_defs.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac reg_in :=
  first [ solve [ cbn [In]; repeat first [ left; reflexivity | right ] ]
        | solve [ cbn [In]; let HH := fresh "HH" in intros HH;
                  repeat (destruct HH as [HH|HH]; [apply bv_eq in HH; cbv in HH; discriminate HH|]); exact HH ]
        | cbv; tauto ].

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen_s FUELh STOPSh scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen_s FUELh STOPSh scr NX true.

Section FXALL2.
Context {fx : FPState}.

Lemma data_store_ok : forall M d m, (0 <= d)%Z -> (d + Z.of_nat m <= 0x34000)%Z ->
  store_ok RSEGS M (Z_to_bv 64 (0xee000 + d)) m = true.
Proof. intros M d m Hd Hm. apply S1RwWindow.store_ok_rwZ; lia. Qed.

Lemma know_img_clear : forall E M kn (lo hi : Z),
  know_ok RSEGS E M kn -> existsb (is_kimg_cov lo (hi - lo)) kn = true -> img_clear M lo hi.
Proof.
  intros E M kn lo hi HK Hb i Hi. apply existsb_exists in Hb as (K & HinK & Hc).
  destruct K; try discriminate Hc. cbn [is_kimg_cov] in Hc. apply andb_prop in Hc as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) HK _ HinK) as (_ & _ & Hn). apply Hn. lia.
Qed.

Lemma w2le1_byte : forall (x : byte), word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned x)) = [x].
Proof.
  intros x. pose proof (bv_unsigned_in_range _ x) as Hx. change (bv_modulus 8) with 256%Z in Hx.
  unfold word_to_le_bytes. cbn [Z_to_le_bytes]. f_equal.
  rewrite u_small by lia. apply Z_to_bv_bv_unsigned.
Qed.

Record xfacts (sp0 tid : Z) (M : word -> option byte) : Prop := {
  xf_mf    : main_frame sp0 M;
  xf_stack : stack_writableZ M sp0;
  xf_tid   : cell M 0x100610 4 tid;
  xf_locale: cell M 0x100688 8 0x120980;
  xf_nlocks: cell M 0x12094b 1 0;
  xf_cxx   : cxx_cells_ok M;
  xf_clear : Forall (fun iv => img_clear M (fst iv) (snd iv)) (exit_clear_common ++ exit_clear_u1);
  xf_f0 : cell M 0xee1b0 4 5;
  xf_f1 : cell M 0xee1b8 8 0;
  xf_f2 : cell M 0xee1c0 8 0;
  xf_f3 : cell M 0xee1d0 8 0x120e98;
  xf_f4 : cell M 0xee1d8 8 0x120e98;
  xf_f5 : cell M 0xee1e8 8 0x120e98;
  xf_f6 : cell M 0xee238 4 0xffffffff
}.

Section Header.
  Context {AC : AllocCeiling} {RRND : RunRandom} {AMB : Amb}.
  Variable MI : MallocIface SEGS L.
  Variable AINV0 : AS MI -> LibIface.mem -> Model -> Prop.
  Variables (TIGHT FRESH44 : AS MI -> Prop).
  Hypothesis DM : drv_mallocT MI AINV0 TIGHT FRESH44.
  Variables (sp0 tid p1 : Z) (path content : list byte) (fs0 : Fs).
  Hypothesis Hsp : (0x7fff80000000 <= sp0 <= 0x800000000000 /\ sp0 mod 16 = 0)%Z.
  Hypothesis Hp1 : (sp0 <= p1 /\ p1 + Z.of_nat (length path) + 1 < 2 ^ 63)%Z.
  Hypothesis Htid : (0 < tid < 2 ^ 22)%Z.
  Variables (p cap : Z) (A : AS MI) (R0 : bvmap 5 word) (M0 : word -> option byte) (mo : Model).
  Hypothesis RE : rend MI TIGHT sp0 tid p1 path content fs0 p cap A R0 M0 mo.
  Hypothesis HAC : (alloc_ceiling = sp0 - 8388608)%Z.

  Let L : Z := Z.of_nat (length content).
  Let spw : word := Z_to_bv 64 sp0.
  Let pw : word := Z_to_bv 64 p.

  Definition valsh : list word :=
    [spw; Z_to_bv 64 p1; Z_to_bv 64 cap; pw; Z_to_bv 64 tid; Z_to_bv 64 L; Z_to_bv 64 (hdr_b0 content); Z_to_bv 64 (hdr_b1 content);
     Z_to_bv 64 rr_canary] ++ junk_vals R0.

  Lemma re_facts : (0x122000 <= p)%Z /\ (p + cap <= alloc_ceiling)%Z /\ (65536 <= cap <= 2 ^ 26)%Z /\ (L < cap)%Z.
  Proof.
    destruct (re_cap _ _ _ _ _ _ _ _ _ _ _ _ _ _ RE) as [HLc (j & Hj & Hcap)].
    pose proof (cap_of_range j Hj) as CR. rewrite <- Hcap in CR.
    destruct (buf_geom MI A M0 mo p cap (re_abs _ _ _ _ _ _ _ _ _ _ _ _ _ _ RE)
                (re_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ RE) ltac:(lia)) as (H1 & H2 & H3).
    repeat split; try lia.
  Qed.

  Lemma content_byte : forall j, (j < length content)%nat ->
    rdn RSEGS M0 (Z_to_bv 64 (p + Z.of_nat j)) 1%nat
    = Some (word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned (nth j content (Z_to_bv 8 0))))).
  Proof.
    intros j Hj. pose proof re_facts as (P1f & P2 & P3 & P4). pose proof HAC as Hcv. pose proof ac_bounds_lit as Hcb.
    pose proof (rdn_nth RSEGS M0 (length content) _ content j (re_content _ _ _ _ _ _ _ _ _ _ _ _ _ _ RE) Hj) as H.
    rewrite w_add_nat in H. rewrite u_small in H by lia. rewrite w2le1_byte. exact H.
  Qed.

  Lemma static_cell : forall (a : Z) (zs : list Z) (n : nat) (v : Z),
    In (a, zs) (static_cells MI) -> length zs = n ->
    map (Z_to_bv 8) zs = word_to_le_bytes n (Z_to_bv 64 v) -> cell M0 a n v.
  Proof.
    intros a zs n v Hin Hl He. unfold cell. rewrite <- He, <- Hl.
    exact (ai_static_cells MI A M0 mo a zs (ra_ainv _ _ _ _ (re_abs _ _ _ _ _ _ _ _ _ _ _ _ _ _ RE)) Hin).
  Qed.

  Lemma hdr_sym : regs_ok (ENVh content valsh) sr_H R0 /\ know_ok RSEGS (ENVh content valsh) M0 kn_H.
  Proof.
    pose proof re_facts as (P1f & P2 & P3 & P4). pose proof HAC as Hcv. pose proof ac_bounds_lit as Hcb.
    pose proof (dm_consts _ _ _ _ DM) as [MSc BIGc NMAXc RBc SCg SCn SCp].
    destruct RE as [Rsp Rgp Rtp Rs0 Rs1 Rs2 Rs3 Rs4 Rs5 Rs6 QM QA QT QL Qcap Qcont Qfds Qfs].
    set (vals := valsh). set (E := ENVh content vals).
    assert (E0 : ev E 0 = spw) by reflexivity.
    assert (E1 : ev E 1 = Z_to_bv 64 p1) by reflexivity.
    assert (E2 : ev E 2 = Z_to_bv 64 cap) by reflexivity.
    assert (E3 : ev E 3 = pw) by reflexivity.
    assert (E4 : ev E 4 = Z_to_bv 64 tid) by reflexivity.
    assert (E5 : ev E 5 = Z_to_bv 64 L) by reflexivity.
    assert (EJ : forall i, (i < 32)%nat -> ev E (9 + i) = getr R0 (Z_to_bv 5 (Z.of_nat i))).
    { intros i Hi. unfold E, ENVh, vals, valsh. cbn [ev]. unfold vals_ev.
      change (9 + i)%nat with (length [spw; Z_to_bv 64 p1; Z_to_bv 64 cap; pw; Z_to_bv 64 tid; Z_to_bv 64 L; Z_to_bv 64 (hdr_b0 content);
                                        Z_to_bv 64 (hdr_b1 content); Z_to_bv 64 rr_canary] + i)%nat.
      rewrite app_nth2_plus. unfold junk_vals. rewrite (nth_map_seq (fun i => getr R0 (Z_to_bv 5 (Z.of_nat i)))) by exact Hi.
      reflexivity. }
    assert (Uspw : bv_unsigned spw = sp0) by (unfold spw; apply u_small; lia).
    assert (Upw : bv_unsigned pw = p) by (unfold pw; apply u_small; lia).
    split.
    -
      apply S1MainEntry.regs_ok_by_index. intros i Hi.
      destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
        cbn [nth sr_H S1MainEntry.all_regs].
      all: try (lazymatch goal with |- _ = edenot _ (J ?n) =>
                  unfold J; change (edenot E (EVar (9 + n))) with (ev E (9 + n)%nat); rewrite EJ by lia; reflexivity end).
      all: try (lazymatch goal with |- _ = edenot _ (spx ?k) =>
                  unfold spx; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot]; rewrite E0, Uspw;
                  rewrite Rsp; f_equal; lia end).
      all: try (change (edenot E (EVar 1)) with (ev E 1); rewrite E1; assumption).
      all: try (change (edenot E (EVar 2)) with (ev E 2); rewrite E2; assumption).
      all: try (change (edenot E (EVar 3)) with (ev E 3); rewrite E3; unfold pw; assumption).
      all: try (change (edenot E (EVar 5)) with (ev E 5); rewrite E5; assumption).
      all: cbn [edenot]; first [assumption | apply getr_zero | rewrite getr_zero; apply bv_eq; reflexivity | reflexivity].
    -
      assert (SPX : forall k, edenot E (spx k) = Z_to_bv 64 (sp0 + k)).
      { intros k. unfold spx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite E0, Uspw. reflexivity. }
      unfold kn_H.
      apply know_ok_app; split; [ | apply know_ok_app; split; [ | apply know_ok_app; split; [ | apply know_ok_app; split;
        [ apply S1KnIvs.know_ivs; rewrite S1KnIvs.hdr_ivs_eq; exact (rm_img _ _ _ _ _ QM)
        | apply know_drv_cells; exact (rmem_drv_cells _ _ _ _ _ QM) ]]]].
      +
        destruct (rm_mf _ _ _ _ _ QM) as [F1 F2 F3 F4 F5 F6 F7 F8 F9]. unfold cell in *.
        unfold kn_Hstack, know_ok. repeat apply Forall_cons; try apply Forall_nil;
          cbn [kentry_ok]; unfold flat, estart, elenZ, adenot, v_addi; cbn [a_base a_off]; rewrite ?SPX; cbn [edenot]; rewrite ?E0, ?Uspw.
        * split; [lia | exact (proj2 Hsp)].
        * lia.
        * split; [lia|]. intros d m Hd Hm. replace (sp0 + -8388608 + d)%Z with (sp0 - 8388608 + d)%Z by lia. apply (rm_stack _ _ _ _ _ QM); lia.
        * split; [lia|]. split; [lia|]. replace (sp0 + -56)%Z with (sp0 - 56)%Z by lia. exact F1.
        * split; [lia|]. split; [lia|]. replace (sp0 + -64)%Z with (sp0 - 64)%Z by lia. exact F2.
        * split; [lia|]. split; [lia|]. replace (sp0 + -72)%Z with (sp0 - 72)%Z by lia. exact F3.
        * split; [lia|]. split; [lia|]. replace (sp0 + -80)%Z with (sp0 - 80)%Z by lia. exact F4.
        * split; [lia|]. split; [lia|]. replace (sp0 + -88)%Z with (sp0 - 88)%Z by lia. exact F5.
        * split; [lia|]. split; [lia|]. replace (sp0 + -96)%Z with (sp0 - 96)%Z by lia. exact F6.
        * split; [lia|]. split; [lia|]. replace (sp0 + -104)%Z with (sp0 - 104)%Z by lia. exact F7.
        * split; [lia|]. split; [lia|]. replace (sp0 + -112)%Z with (sp0 - 112)%Z by lia. exact F8.
        * split; [lia|]. split; [lia|]. replace (sp0 + -120)%Z with (sp0 - 120)%Z by lia. exact F9.
      +
        unfold kn_Hbuf, know_ok. repeat apply Forall_cons; try apply Forall_nil;
          cbn [kentry_ok]; unfold flat, estart, elenZ, adenot, v_addi; cbn [a_base a_off edenot]; rewrite ?E0, ?E2, ?E3, ?Uspw, ?Upw.
        * lia.
        * rewrite u_small by lia. lia.
      +
        unfold kn_Himage, know_ok. repeat apply Forall_cons; try apply Forall_nil;
          cbn [kentry_ok]; unfold flat, estart, elenZ, adenot, v_addi; cbn [a_base a_off edenot]; rewrite ?E4;
          change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; rewrite ?Z.add_0_l.
        * split; [lia|]. intros d m Hd Hm. apply data_store_ok; lia.
        * split; [lia|]. split; [lia|]. exact (rm_tid _ _ _ _ _ QM).
        * split; [lia|]. split; [lia|]. exact (rm_self _ _ _ _ _ QM).
        * split; [lia|]. split; [lia|]. change (ev (ENVh content valsh) 8) with (Z_to_bv 64 rr_canary).
          eapply static_cell; [exact SCg | apply length_map |].
          rewrite map_map. erewrite map_ext; [apply map_id|]. intros b. apply Z_to_bv_bv_unsigned.
        * split; [lia|]. split; [lia|]. eapply static_cell; [exact SCp | reflexivity | apply byte_list_eq; vm_compute; reflexivity].
        * split; [lia|]. split; [lia|]. eapply static_cell; [exact SCn | reflexivity | apply byte_list_eq; vm_compute; reflexivity].
        * rewrite u_small by lia. lia.
  Qed.

  Lemma hdr_know_short : know_ok RSEGS (ENVh content valsh) M0 kn_H ->
    (length content < 6)%nat -> know_ok RSEGS (ENVh content valsh) M0 kn_short.
  Proof.
    intros HK Hlt. unfold kn_short. apply know_ok_app. split; [exact HK|].
    apply know_ok_cons; [|constructor]. apply krange_intro.
    change (edenot (ENVh content valsh) (EVar 5)) with (Z_to_bv 64 L). unfold L. rewrite u_small by lia. lia.
  Qed.

  Lemma hdr_know_long : know_ok RSEGS (ENVh content valsh) M0 kn_H ->
    (6 <= length content)%nat -> know_ok RSEGS (ENVh content valsh) M0 kn_long.
  Proof.
    intros HK Hge. pose proof re_facts as (P1f & P2 & P3 & P4). pose proof HAC as Hcv. pose proof ac_bounds_lit as Hcb.
    pose proof (bv_unsigned_in_range _ (nth 0 content (Z_to_bv 8 0))) as B0.
    pose proof (bv_unsigned_in_range _ (nth 1 content (Z_to_bv 8 0))) as B1.
    change (bv_modulus 8) with 256%Z in B0, B1.
    assert (Upw : bv_unsigned pw = p) by (unfold pw; apply u_small; lia).
    unfold kn_long. apply know_ok_app. split; [exact HK|].
    apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|apply know_ok_cons; [|constructor]]]]].
    - apply krange_intro. change (edenot (ENVh content valsh) (EVar 5)) with (Z_to_bv 64 L). unfold L. rewrite u_small by lia. lia.
    - cbn [kentry_ok]. split; [lia|]. split; [apply flat_intro; cbn [edenot ev ENVh valsh vals_ev nth app]; rewrite ?Upw; lia|].
      unfold adenot, v_addi. cbn [a_base a_off edenot]. change (ev (ENVh content valsh) 3) with pw. rewrite Upw.
      change (ev (ENVh content valsh) 6) with (Z_to_bv 64 (hdr_b0 content)). unfold hdr_b0.
      replace (p + 0)%Z with (p + Z.of_nat 0)%Z by lia. apply content_byte. lia.
    - cbn [kentry_ok]. split; [lia|]. split; [apply flat_intro; cbn [edenot ev ENVh valsh vals_ev nth app]; rewrite ?Upw; lia|].
      unfold adenot, v_addi. cbn [a_base a_off edenot]. change (ev (ENVh content valsh) 3) with pw. rewrite Upw.
      change (ev (ENVh content valsh) 7) with (Z_to_bv 64 (hdr_b1 content)). unfold hdr_b1.
      replace (p + 1)%Z with (p + Z.of_nat 1)%Z by lia. apply content_byte. lia.
    - apply krange_intro. change (edenot (ENVh content valsh) (EVar 6)) with (Z_to_bv 64 (hdr_b0 content)). unfold hdr_b0.
      rewrite u_small by lia. lia.
    - apply krange_intro. change (edenot (ENVh content valsh) (EVar 7)) with (Z_to_bv 64 (hdr_b1 content)). unfold hdr_b1.
      rewrite u_small by lia. lia.
  Qed.

  Lemma fds_std_2 : fd_lookup fds_std (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Proof. reflexivity. Qed.
  Lemma msg_short_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x1409c) 31 = Some msg_short.
  Proof. vm_compute. reflexivity. Qed.
  Lemma msg_overrun_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x11537) 31 = Some msg_overrun.
  Proof. vm_compute. reflexivity. Qed.

  Ltac xcell HK a n := let H := fresh in unfold cell; krd HK a n H; exact H.

  Lemma xfacts_of_kn : forall (vals : list word) (M : word -> option byte) (kn : list kentry),
    vals_ev vals 0 = spw -> vals_ev vals 4 = Z_to_bv 64 tid ->
    know_ok RSEGS (ENVh content vals) M kn ->
    (kn = knSB \/ kn = knOB) ->
    xfacts sp0 tid M.
  Proof.
    intros vals M kn P0 P4 HK Hkn.
    assert (Uspw : bv_unsigned spw = sp0) by (unfold spw; apply u_small; lia).
    assert (MF : forall k v, (k = -56 /\ v = 0xcfab0 \/ k = -72 /\ v = 2 \/ k = -80 /\ v = 0x655e8 \/ k = -96 /\ v = 0 \/ k = -104 /\ v = 0 \/ k = -112 /\ v = 0 \/ k = -120 /\ v = 0)%Z ->
                 kread RSEGS kn (EVar 0) k 8 = Some (ELit v) -> cell M (sp0 + k) 8 v).
    { intros k v Hk HR. unfold cell.
      pose proof (kread_rdn RSEGS (ENVh content vals) M kn (EVar 0) k 8 (ELit v) HK HR ltac:(lia) ltac:(lia)
                    ltac:(apply flat_intro; cbn [edenot ev ENVh]; rewrite ?P0, ?Uspw; lia)) as H.
      unfold adenot, v_addi in H. cbn [a_base a_off edenot ev ENVh] in H. rewrite P0, Uspw in H. exact H. }
    assert (MFs : forall k (e : expr) (v : word), edenot (ENVh content vals) e = v -> (-120 <= k <= -48)%Z ->
                 kread RSEGS kn (EVar 0) k 8 = Some e -> rdn RSEGS M (Z_to_bv 64 (sp0 + k)) 8 = Some (word_to_le_bytes 8 v)).
    { intros k e v He Hk HR.
      pose proof (kread_rdn RSEGS (ENVh content vals) M kn (EVar 0) k 8 e HK HR ltac:(lia) ltac:(lia)
                    ltac:(apply flat_intro; cbn [edenot ev ENVh]; rewrite ?P0, ?Uspw; lia)) as H.
      unfold adenot, v_addi in H. cbn [a_base a_off] in H. change (edenot (ENVh content vals) (EVar 0)) with (vals_ev vals 0) in H.
      rewrite P0, Uspw, He in H. exact H. }
    assert (SPXv : forall k, edenot (ENVh content vals) (spx k) = Z_to_bv 64 (sp0 + k)).
    { intros k. unfold spx. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVh]. rewrite P0, Uspw. reflexivity. }
    constructor.
    -   constructor.
      + apply (MF (-56)%Z); [tauto | destruct Hkn as [-> | ->]; vm_compute; reflexivity].
      + unfold cell. replace (sp0 - 64)%Z with (sp0 + -64)%Z by lia. apply (MFs (-64)%Z (spx 8)); [rewrite SPXv; reflexivity | lia | destruct Hkn as [-> | ->]; vm_compute; reflexivity].
      + apply (MF (-72)%Z); [tauto | destruct Hkn as [-> | ->]; vm_compute; reflexivity].
      + apply (MF (-80)%Z); [tauto | destruct Hkn as [-> | ->]; vm_compute; reflexivity].
      + unfold cell. replace (sp0 - 88)%Z with (sp0 + -88)%Z by lia. apply (MFs (-88)%Z (spx 32)); [rewrite SPXv; reflexivity | lia | destruct Hkn as [-> | ->]; vm_compute; reflexivity].
      + apply (MF (-96)%Z); [tauto | destruct Hkn as [-> | ->]; vm_compute; reflexivity].
      + apply (MF (-104)%Z); [tauto | destruct Hkn as [-> | ->]; vm_compute; reflexivity].
      + apply (MF (-112)%Z); [tauto | destruct Hkn as [-> | ->]; vm_compute; reflexivity].
      + apply (MF (-120)%Z); [tauto | destruct Hkn as [-> | ->]; vm_compute; reflexivity].
    -   intros d m Hd Hm.
      assert (HW : kentry_ok RSEGS (ENVh content vals) M (KWr (SA (EVar 0) (-8388608)) 8388608)).
      { eapply (proj1 (Forall_forall _ _) HK). destruct Hkn as [-> | ->]; unfold knSB, knOB;
        repeat first [ apply in_eq | apply in_cons ]. }
      cbn [kentry_ok] in HW. destruct HW as [_ HW]. unfold estart in HW. cbn [a_base a_off edenot ev ENVh] in HW. rewrite P0, Uspw in HW.
      replace (sp0 - 8388608 + d)%Z with (sp0 + -8388608 + d)%Z by lia. apply HW; lia.
    -   unfold cell. destruct Hkn as [-> | ->]; (krd HK 0x100610%Z 4%nat H; cbn [edenot ev ENVh] in H; rewrite P4 in H;
        rewrite ext_val_zx_id in H by (rewrite u_small by lia; cbn; lia); exact H).
    - destruct Hkn as [-> | ->]; xcell HK 0x100688%Z 8%nat.
    - destruct Hkn as [-> | ->]; xcell HK 0x12094b%Z 1%nat.
    - unfold cxx_cells_ok, cells_ok, exit_cxx_cells. destruct Hkn as [-> | ->]; (repeat apply Forall_cons; try apply Forall_nil; krd_solve HK).
    - unfold exit_clear_common, exit_clear_u1. cbn [app].
      destruct Hkn as [-> | ->]; (repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
        (eapply (know_img_clear _ _ _ _ _ HK); vm_compute; reflexivity)).
    - destruct Hkn as [-> | ->]; xcell HK 0xee1b0%Z 4%nat.
    - destruct Hkn as [-> | ->]; xcell HK 0xee1b8%Z 8%nat.
    - destruct Hkn as [-> | ->]; xcell HK 0xee1c0%Z 8%nat.
    - destruct Hkn as [-> | ->]; xcell HK 0xee1d0%Z 8%nat.
    - destruct Hkn as [-> | ->]; xcell HK 0xee1d8%Z 8%nat.
    - destruct Hkn as [-> | ->]; xcell HK 0xee1e8%Z 8%nat.
    - destruct Hkn as [-> | ->]; xcell HK 0xee238%Z 4%nat.
  Qed.

  Definition xf_ivs : list (Z * Z) :=
    ([(0x100610, 0x100614); (0x100688, 0x100690); (0xee1b0, 0xee1b4); (0xee1b8, 0xee1c8); (0xee1d0, 0xee1e0); (0xee1e8, 0xee1f0); (0xee238, 0xee23c)]
     ++ (exit_clear_common ++ exit_clear_u1) ++ map (fun c : Z * nat * Z => match c with (a, w, _) => (a, a + Z.of_nat w) end) exit_cxx_cells)%Z.
  Lemma xf_ivs_facts : Forall (fun iv : Z * Z => 0x10000 <= fst iv /\ snd iv <= 0x122000
       /\ (snd iv <= 0x100614 \/ 0x100618 <= fst iv) /\ (snd iv <= 0x120ac0 \/ 0x120e68 <= fst iv)
       /\ (snd iv <= 0x120978 \/ 0x120980 <= fst iv) /\ (snd iv <= 0x12094b \/ 0x12094c <= fst iv)
       /\ (snd iv <= 0x120928 \/ 0x120930 <= fst iv) /\ (snd iv <= 0x1216ac \/ 0x1216b4 <= fst iv))%Z xf_ivs.
  Proof. unfold xf_ivs, exit_clear_common, exit_clear_u1, exit_cxx_cells. cbn [app map]. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. Qed.

  Lemma xf_ivs_agree : forall (F : Z -> Prop) (M M' : word -> option byte),
    frame_eq F M M' ->
    (forall a, (0x10000 <= a < 0x122000)%Z -> ~ mng_static a -> ~ errno_win S1Layout.L a -> ~ F a) ->
    forall lo hi, In (lo, hi) xf_ivs -> forall i, (lo <= i < hi)%Z -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i).
  Proof.
    intros F M M' FR HF lo hi Hin i Hi. pose proof (proj1 (Forall_forall _ _) xf_ivs_facts _ Hin) as X. cbn [fst snd] in X.
    apply FR. rewrite u64_lit by lia. apply HF; [lia | unfold mng_static; lia | unfold errno_win, zwin; cbn; lia].
  Qed.

  Lemma xfacts_free : forall (A' A'' : AS MI) (M M' : word -> option byte) (mo' mo'' : Model),
    xfacts sp0 tid M -> rabs MI A' M mo' -> In (p, cap) (live MI A') ->
    ainv MI A'' M' mo'' ->
    (forall a, owned MI A'' a -> owned MI A' a \/ (p <= a < p + cap)%Z) ->
    frame_eq (fun a => owned MI A' a \/ (p <= a < p + cap)%Z \/ zwin (sp0 - 128 - MALLOC_STACK MI) (sp0 - 128) a \/ errno_win S1Layout.L a) M M' ->
    (forall a : word, M a <> None -> M' a <> None \/ owned MI A' (bv_unsigned a) \/ (p <= bv_unsigned a < p + cap)%Z \/ errno_win S1Layout.L (bv_unsigned a)) ->
    xfacts sp0 tid M'.
  Proof.
    intros A' A'' M M' mo' mo'' XF RA' Hin AI'' OWN FR DEF.
    pose proof re_facts as (P1f & P2 & P3 & P4). pose proof HAC as Hcv. pose proof ac_bounds_lit as Hcb.
    pose proof (dm_consts _ _ _ _ DM) as [MSc BIGc NMAXc RBc SCg SCn SCp].
    pose proof (ra_ainv _ _ _ _ RA') as AI'.
    destruct (ai_live_block MI A' M mo' p cap AI' Hin) as (_ & _ & _ & Hpc & Hpb).
    assert (HF : forall a, (0x10000 <= a < 0x122000)%Z -> ~ mng_static a -> ~ errno_win S1Layout.L a ->
              ~ (owned MI A' a \/ (p <= a < p + cap)%Z \/ zwin (sp0 - 128 - MALLOC_STACK MI) (sp0 - 128) a \/ errno_win S1Layout.L a)).
    { intros a Ha Hs He [H|[H|[H|H]]].
      - apply Hs. apply (ra_own _ _ _ _ RA' a H). apply img_iff. exact Ha.
      - apply (proj1 (proj2 (Hpb a H))). apply img_iff. exact Ha.
      - unfold zwin in H. rewrite MSc in H. lia.
      - exact (He H). }
    pose proof (xf_ivs_agree _ M M' FR HF) as AG. unfold xf_ivs in AG.
    assert (AGS : forall i, (sp0 - 128 <= i < sp0)%Z -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi. apply FR. rewrite u64_lit by lia. intros [H|[H|[H|H]]].
      - exact (high_not_owned MI A' M mo' i AI' ltac:(lia) H).
      - lia.
      - unfold zwin in H. lia.
      - exact (high_not_errno i ltac:(lia) H). }
    destruct XF as [X1 X2 X3 X4 X5 X6 X7 F0 F1 F2 F3 F4 F5 F6].
    Ltac agcell AG H lo hi := eapply cell_agree; [cbn; lia | lia | | exact H]; intros i Hi; apply (AG lo hi); [cbn; tauto | cbn in Hi |- *; lia].
    constructor.
    - eapply main_frame_frame; [lia | lia | | exact X1]. intros i Hi. apply AGS. lia.
    - eapply (stack_def_xfer sp0 Hsp); [exact X2|]. intros a Ha Hd.
      destruct (DEF (Z_to_bv 64 a) Hd) as [H|[H|[H|H]]]; [exact H | exfalso; rewrite u64_lit in H by lia ..].
      + exact (high_not_owned MI A' M mo' a AI' ltac:(lia) H).
      + lia.
      + exact (high_not_errno a ltac:(lia) H).
    - agcell AG X3 0x100610%Z 0x100614%Z.
    - agcell AG X4 0x100688%Z 0x100690%Z.
    -
      unfold cell. pose proof (ai_static_cells MI A'' M' mo'' 0x12094b [0%Z] AI'' SCn) as H. exact H.
    - unfold cxx_cells_ok, cells_ok in *. apply Forall_forall. intros [[a w] v] Hc.
      pose proof (proj1 (Forall_forall _ _) X6 _ Hc) as H. cbn beta iota in H |- *.
      pose proof (proj1 (Forall_forall _ _) drv_cells_range _ ltac:(unfold drv_cells; apply in_or_app; left; exact Hc)) as HR. cbn beta iota in HR.
      eapply rdn_agree; [lia | lia | | exact H]. intros i Hi. eapply AG; [|exact Hi].
      apply in_or_app. right. apply in_or_app. right. apply in_map_iff. exists (a, w, v). split; [reflexivity | exact Hc].
    - apply Forall_forall. intros [lo hi] Hc. cbn [fst snd].
      pose proof (proj1 (Forall_forall _ _) X7 _ Hc) as H. cbn [fst snd] in H.
      eapply img_clear_agree; [|exact H]. intros i Hi. eapply AG; [|exact Hi].
      apply in_or_app. right. apply in_or_app. left. exact Hc.
    - agcell AG F0 0xee1b0%Z 0xee1b4%Z.
    - agcell AG F1 0xee1b8%Z 0xee1c8%Z.
    - agcell AG F2 0xee1b8%Z 0xee1c8%Z.
    - agcell AG F3 0xee1d0%Z 0xee1e0%Z.
    - agcell AG F4 0xee1d0%Z 0xee1e0%Z.
    - agcell AG F5 0xee1e8%Z 0xee1f0%Z.
    - agcell AG F6 0xee238%Z 0xee23c%Z.
  Qed.

  Definition entry_in_b (spi : nat) (wlo whi alo ahi : Z) (e : sentry) : bool :=
    match e with
    | SE (SA (EVar i) k) w _ => (Nat.eqb i spi && (wlo <=? k)%Z && (k + Z.of_nat w <=? whi)%Z)%bool
    | SE (SA (ELit z) a) w _ => (Z.eqb z 0 && (alo <=? a)%Z && (a + Z.of_nat w <=? ahi)%Z)%bool
    | _ => false
    end.
  Definition log_in_b (spi : nat) (wlo whi alo ahi : Z) (log : list sentry) : bool := forallb (entry_in_b spi wlo whi alo ahi) log.

  Lemma mem_denot_foot : forall E base log (spi : nat) (wlo whi alo ahi : Z) (x : word),
    log_in_b spi wlo whi alo ahi log = true ->
    (- 8192 <= wlo)%Z -> (whi <= 0)%Z -> (0 <= alo <= ahi)%Z -> (ahi + 8192 <= bv_unsigned (ev E spi))%Z ->
    ~ (bv_unsigned (ev E spi) + wlo <= bv_unsigned x < bv_unsigned (ev E spi) + whi)%Z ->
    ~ (alo <= bv_unsigned x < ahi)%Z ->
    mem_denot E base log x = base x.
  Proof.
    intros E base log spi wlo whi alo ahi x Hb Hwlo Hwhi Halo Hhi N1 N2. pose proof (u64_range (ev E spi)) as Usp. pose proof (u64_range x) as Ux.
    induction log as [|[[b k] w v] rest IH]; [reflexivity|].
    cbn [log_in_b forallb] in Hb. apply andb_prop in Hb as [He Hrest].
    cbn [entry_in_b] in He. destruct b as [z|i| | | | | |]; try discriminate He.
    - apply andb_prop in He as [He H2]. apply andb_prop in He as [H0 H1].
      apply Z.eqb_eq in H0. subst z. apply Z.leb_le in H1. apply Z.leb_le in H2.
      cbn [mem_denot]. rewrite wbytes_outside.
      + apply IH. exact Hrest.
      + rewrite length_N_to_le_bytes. unfold in_rng, adenot, v_addi. cbn [a_base a_off edenot].
        rewrite (u64_lit 0), u64_lit by lia. lia.
      + rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite (u64_lit 0), u64_lit by lia. lia.
    - apply andb_prop in He as [He H2]. apply andb_prop in He as [H0 H1].
      apply Nat.eqb_eq in H0. subst i. apply Z.leb_le in H1. apply Z.leb_le in H2.
      cbn [mem_denot]. rewrite wbytes_outside.
      + apply IH. exact Hrest.
      + rewrite length_N_to_le_bytes. unfold in_rng, adenot, v_addi. cbn [a_base a_off edenot]. rewrite u64_lit by lia. lia.
      + rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite u64_lit by lia. lia.
  Qed.

  Lemma rabs_agree : forall (M M' : word -> option byte),
    rabs MI A M mo -> mem_grows M M' ->
    (forall x : word, M' x <> M x -> (sp0 - 65536 <= bv_unsigned x < sp0 - 128)%Z \/ (0xee1b0 <= bv_unsigned x < 0xee480)%Z) ->
    rabs MI A M' mo.
  Proof.
    intros M M' RA HG HW. pose proof HAC as Hcv. pose proof ac_bounds_lit as Hcb. pose proof (ra_ainv _ _ _ _ RA) as AI.
    constructor; try (destruct RA; assumption).
    eapply (ai_frame MI A M M' mo mo AI); [ | exact HG | reflexivity | reflexivity].
    intros a Ho. destruct (Classical_Prop.classic (M' a = M a)) as [E|NE]; [exact E|]. exfalso.
    destruct (HW _ NE) as [Hr|Hr].
    - exact (high_not_owned MI A M mo (bv_unsigned a) AI ltac:(lia) Ho).
    - refine (_ (ra_own _ _ _ _ RA (bv_unsigned a) Ho ltac:(apply img_iff; lia))). unfold mng_static. lia.
  Qed.

  Lemma rabs_after_log : forall (vals : list word) (M : word -> option byte) (log : list sentry),
    rabs MI A M mo -> vals_ev vals 0 = spw -> log_in_b 0 (-4112) (-128) 0xee1b0 0xee480 log = true ->
    rabs MI A (mem_denot (ENVh content vals) M log) mo.
  Proof.
    intros vals M log RA P0 Hb. assert (Uspw : bv_unsigned spw = sp0) by (unfold spw; apply u_small; lia).
    eapply rabs_agree; [exact RA | apply mem_denot_grows |].
    intros x NE. destruct (Classical_Prop.classic ((sp0 - 65536 <= bv_unsigned x < sp0 - 128)%Z \/ (0xee1b0 <= bv_unsigned x < 0xee480)%Z)) as [H|H]; [exact H|].
    exfalso. apply NE. apply (mem_denot_foot (ENVh content vals) M log 0 (-4112) (-128) 0xee1b0 0xee480 x Hb); try lia.
    all: cbn [ev ENVh]; rewrite P0, Uspw; lia.
  Qed.

  Lemma rabs_after_stdio : forall (M M' : word -> option byte) (su f : Z),
    rabs MI A M mo -> mem_grows M M' ->
    (sp0 - 4112 <= su - 112)%Z -> (su <= sp0 - 128)%Z -> (0xee1b0 <= f)%Z -> (f + 232 <= 0xee480)%Z ->
    (forall x : word, ~ (su - 112 <= bv_unsigned x < su)%Z -> ~ (f + 32 <= bv_unsigned x < f + 48)%Z ->
                      ~ (f + 56 <= bv_unsigned x < f + 64)%Z -> M' x = M x) ->
    rabs MI A M' mo.
  Proof.
    intros M M' su f RA HG H1 H2 H3 H4 HF. eapply rabs_agree; [exact RA | exact HG |].
    intros x NE. destruct (Classical_Prop.classic ((sp0 - 65536 <= bv_unsigned x < sp0 - 128)%Z \/ (0xee1b0 <= bv_unsigned x < 0xee480)%Z)) as [H|H]; [exact H|].
    exfalso. apply NE. apply HF; lia.
  Qed.

  Definition err_tail_stmt (sr : list expr) (kn : list kentry) : Prop :=
    forall vals R M,
      length vals = 73%nat -> vals_ev vals 0 = spw -> vals_ev vals 3 = pw -> vals_ev vals 4 = Z_to_bv 64 tid ->
      regs_ok (ENVh content vals) sr R -> know_ok RSEGS (ENVh content vals) M kn -> rabs MI A M mo ->
      srealizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0xd1fa0) M (seg_rom RSEGS)) mo) (t_exit (exit_code 2) fs0).

  Lemma err_tail : forall sr kn, (sr = srSB /\ kn = knSB) \/ (sr = srOB /\ kn = knOB) -> err_tail_stmt sr kn.
  Proof.
    intros sr kn Hsk vals R M HL P0 P3 P4 HR HK RA.
    pose proof re_facts as (P1f & P2 & P3c & P4c). pose proof HAC as Hcv. pose proof ac_bounds_lit as Hcb.
    pose proof (dm_consts _ _ _ _ DM) as [MSc BIGc NMAXc RBc SCg SCn SCp].
    assert (Uspw : bv_unsigned spw = sp0) by (unfold spw; apply u_small; lia).
    assert (Upw : bv_unsigned pw = p) by (unfold pw; apply u_small; lia).
    assert (XF : xfacts sp0 tid M) by (eapply (xfacts_of_kn vals M kn P0 P4 HK); destruct Hsk as [[_ ->]|[_ ->]]; tauto).
    pose proof (ra_ainv _ _ _ _ RA) as AI. destruct (ra_mstd _ _ _ _ RA) as [Hh Hlz Hmat].
    pose proof (re_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ RE) as LV. pose proof (re_tight _ _ _ _ _ _ _ _ _ _ _ _ _ _ RE) as TI.
    assert (Hin : In (p, cap) (live MI A)) by (rewrite LV; left; reflexivity).

    assert (S1 : sr_get sr 1%bv = ELit 0x657e4) by (destruct Hsk as [[-> _]|[-> _]]; reflexivity).
    assert (S2 : sr_get sr 2%bv = EAlu Instr.ALU_ADD (EVar 0) (ELit (-128))) by (destruct Hsk as [[-> _]|[-> _]]; reflexivity).
    assert (S3 : sr_get sr 3%bv = ELit 0x10800) by (destruct Hsk as [[-> _]|[-> _]]; reflexivity).
    assert (S4 : sr_get sr 4%bv = ELit 0x1006b8) by (destruct Hsk as [[-> _]|[-> _]]; reflexivity).
    assert (S8 : sr_get sr 8%bv = ELit 2) by (destruct Hsk as [[-> _]|[-> _]]; reflexivity).
    assert (S9 : sr_get sr 9%bv = EVar 3) by (destruct Hsk as [[-> _]|[-> _]]; reflexivity).
    assert (S10 : sr_get sr 10%bv = EVar 3) by (destruct Hsk as [[-> _]|[-> _]]; reflexivity).
    assert (G1 : getr R 1 = Z_to_bv 64 0x657e4) by (rewrite (reg_val _ _ _ 1%bv HR), S1; reflexivity).
    assert (G2 : getr R 2 = Z_to_bv 64 (sp0 - 128)).
    { rewrite (reg_val _ _ _ 2%bv HR), S2, edenot_add_lit. unfold adenot, v_addi; cbn [a_base a_off edenot ev ENVh]. rewrite P0, Uspw; reflexivity. }
    assert (G3 : getr R 3 = Z_to_bv 64 0x10800) by (rewrite (reg_val _ _ _ 3%bv HR), S3; reflexivity).
    assert (G4 : getr R 4 = Z_to_bv 64 0x1006b8) by (rewrite (reg_val _ _ _ 4%bv HR), S4; reflexivity).
    assert (G8 : getr R 8 = Z_to_bv 64 2) by (rewrite (reg_val _ _ _ 8%bv HR), S8; reflexivity).
    assert (G9 : getr R 9 = Z_to_bv 64 p) by (rewrite (reg_val _ _ _ 9%bv HR), S9; cbn [edenot ev ENVh]; rewrite P3; reflexivity).
    assert (G10 : getr R 10 = Z_to_bv 64 p) by (rewrite (reg_val _ _ _ 10%bv HR), S10; cbn [edenot ev ENVh]; rewrite P3; reflexivity).
    replace (Z_to_bv 64 0xd1fa0) with (Z_to_bv 64 (ly_free S1Layout.L)) by reflexivity.
    eapply (dm_free _ _ _ _ DM fx A R M mo p cap (sp0 - 128)%Z 0x657e4%Z (t_exit (exit_code 2) fs0) AI TI (ra_mstd _ _ _ _ RA)).
    -   intros w Hi Hnrw.
      assert (Hw : (0x10000 <= bv_unsigned w < 0xee000)%Z).
      { apply img_iff in Hi. destruct (Z.lt_ge_cases (bv_unsigned w) 0xee000); [lia|]. exfalso. apply Hnrw.
        exists 0xee000%Z, 0x122000%Z. split; [left; reflexivity | lia]. }
      rewrite <- (Z_to_bv_bv_unsigned 64 w).
      pose proof (proj1 (Forall_forall _ _) (xf_clear _ _ _ XF) (0x10000, 0xee000)%Z ltac:(unfold exit_clear_common; cbn; tauto)) as C.
      cbn [fst snd] in C. apply C. lia.
    - constructor.
      + exact G1.
      + apply bv_eq. vm_compute. reflexivity.
      + lia.
      + exact G2.
      + rewrite Zminus_mod, (proj2 Hsp). reflexivity.
      + lia.
      + exact G3.
      + exact G4.
    - exact G10.
    - right. exact Hin.
    - rewrite MSc. lia.
    - rewrite MSc. unfold stack_room.
      replace (Z_to_bv 64 (sp0 - 128 - 8192)) with (Z_to_bv 64 (sp0 - 8388608 + 8380288)) by (f_equal; lia).
      apply (xf_stack _ _ _ XF); lia.
    - rewrite MSc. intros a Ha. unfold zwin in Ha. exact (high_not_owned MI A M mo a AI ltac:(lia)).
    -
      intros A' R' M' mo' AI' TI' MS' FS' FDS' KEPT LDEL CP BG OWN FR DEF.
      pose proof (xfacts_free A A' M M' mo mo' XF RA Hin AI' OWN FR DEF) as XF'.
      destruct (blk_Y R' M' (seg_rom RSEGS) sp0 2 p 0 0 1 (0%bv : word) (0%bv : word) (0%bv : word) (0%bv : word) (0%bv : word) (0%bv : word) (0%bv : word) (0%bv : word) Hsp ltac:(lia)
                  ltac:(rewrite (KEPT 3%bv) by reg_in; exact G3) ltac:(rewrite (KEPT 4%bv) by reg_in; exact G4)
                  ltac:(rewrite (KEPT 2%bv) by reg_in; exact G2) ltac:(rewrite (KEPT 8%bv) by reg_in; exact G8)
                  ltac:(rewrite (KEPT 9%bv) by reg_in; exact G9) (xf_mf _ _ _ XF')) as (R2 & MS2 & Y2 & Y4 & Y10).
      replace (Z_to_bv 64 0x657e4) with (Z_to_bv 64 RET_FREE_MAIN) by reflexivity.
      eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | exact MS2 |].
      replace (Z_to_bv 64 EXITPC) with (0xd00fc%bv : word) by (apply bv_eq; reflexivity).
      replace (t_exit (exit_code 2) fs0) with (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs mo'))
        by (rewrite FS', (re_fs _ _ _ _ _ _ _ _ _ _ _ _ _ _ RE); f_equal; apply bv_eq; reflexivity).
      apply s1_exit_u1. destruct XF' as [X1 X2 X3 X4 X5 X6 X7 F0 F1 F2 F3 F4 F5 F6]. unfold cell in *.
      constructor; rewrite ?Y2, ?Y4, ?Y10; rewrite ?u_small by lia; try assumption.
      + lia.
      + rewrite Zminus_mod, (proj2 Hsp). reflexivity.
      + unfold EXIT_STACK. replace (Z_to_bv 64 (sp0 - 48 - 1024)) with (Z_to_bv 64 (sp0 - 8388608 + 8387536)) by (f_equal; lia).
        change (Z.to_nat 1024) with 1024%nat. apply X2; lia.
      + reflexivity.
      + reflexivity.
      + exists tid. split; [lia | exact X3].
      + exact (ms_halt _ MS').
      + exact (ms_lazy _ MS').
  Qed.

  Ltac usmall_off := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 (bv_unsigned ?x + ?k))] => rewrite (u_small (bv_unsigned x + k)) by lia end.

  Ltac stdio_then_tail vals res msg msg_img msg_addr SRB KNB HL P0 P3 P4 HR HK RA1 MH ML Uspw :=
    lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
    lazymatch type of HR with regs_ok _ ?sr ?Rc =>
    unfold t_die, W;
    let HC := fresh "HC" in
    assert (HC : stdio_call (length vals) sr kn = Some res) by (rewrite HL; vm_compute; reflexivity);
    apply (stdio_call_sound_fr vals (blobs_ev [content]) sr kn Rc Mc mo res [] msg
             (t_exit (exit_code 2) fs0) HR HK HC); clear HC;
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn res];
      try (replace (Z.of_nat (@length byte msg)) with 31%Z by reflexivity); cbn [length Z.of_nat];
    [ cbn [edenot]; rewrite ?u_small by lia; lia
    | cbn [edenot]; lia
    | cbn [edenot]; lit_u; reflexivity
    | lia
    | left; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENVh]; rewrite P0;
      usmall_off; rewrite ?u_small by lia; lia
    | left; rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENVh]; rewrite P0;
      usmall_off; rewrite ?u_small by lia; lia
    | cbn [edenot]; rewrite ?u_small by lia; lia
    | reflexivity
    | cbn [edenot]; replace (@length byte msg) with 31%nat by reflexivity;
      rewrite (kimg_rdn RSEGS (ENVh content vals) _ kn ltac:(let i := kidx kn (is_kimg_cov msg_addr 31) in exact i)
                 _ _ msg_addr 31 HK eq_refl) by (cbn; lia);
      apply msg_img
    | rewrite (re_fds _ _ _ _ _ _ _ _ _ _ _ _ _ _ RE); apply fds_std_2
    | exact MH
    | exact ML
    | apply t_exit_has_nil
    | clear HR HK;
      let R' := fresh "R" in let M' := fresh "M" in let HR' := fresh "HR" in let HK' := fresh "HK" in
      let FR' := fresh "FR" in let HG' := fresh "HG" in let RA2 := fresh "RA2" in
      intros R' M' HR' HK' FR' HG';
      rewrite edenot_add_lit in FR'; unfold adenot, v_addi in FR'; cbn [a_base a_off edenot ev ENVh] in FR';
      rewrite P0, Uspw in FR'; rewrite u_small in FR' by lia;
      assert (RA2 : rabs MI A M' mo) by (eapply (rabs_after_stdio _ M' (sp0 - 192)%Z 0xee1b0%Z RA1 HG'); [lia|lia|lia|lia|exact FR']);
      clear FR' HG' RA1;

      run_block_keep scr0 73%nat;
      lazymatch goal with
      | EQM : ?M2 = mem_denot _ M' [] |- _ => cbn [mem_denot] in EQM; subst M2
      end;
      lazymatch goal with
      | HR2 : regs_ok _ _ ?Rc2, HK2 : know_ok _ _ _ _ |- _ =>
      apply (err_tail SRB KNB ltac:(tauto) (vals ++ junk_vals R') Rc2 M');
      [ rewrite length_app, junk_vals_length, HL; reflexivity
      | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
      | rewrite vals_ev_app_l by (rewrite HL; lia); exact P3
      | rewrite vals_ev_app_l by (rewrite HL; lia); exact P4
      | exact HR2 | exact HK2 | exact RA2 ]
      end ]
    end end.

  Theorem header_short : (length content < 6)%nat ->
    srealizes RSEGS (mkCfg (mkst R0 (Z_to_bv 64 0x656e4) M0 (seg_rom RSEGS)) mo) (t_die msg_short fs0).
  Proof.
    intros Hlt. destruct hdr_sym as (HR & HK0).
    pose proof (hdr_know_short HK0 Hlt) as HK. clear HK0.
    pose proof re_facts as (P1f & P2 & P3c & P4c). pose proof HAC as Hcv. pose proof ac_bounds_lit as Hcb.
    pose proof (re_abs _ _ _ _ _ _ _ _ _ _ _ _ _ _ RE) as RA.
    pose proof (ms_halt _ (ra_mstd _ _ _ _ RA)) as MH. pose proof (ms_lazy _ (ra_mstd _ _ _ _ RA)) as ML.
    assert (Uspw : bv_unsigned spw = sp0) by (unfold spw; apply u_small; lia).
    set (vals := valsh) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold valsh; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = spw) by reflexivity.
    assert (P3 : vals_ev vals 3 = pw) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 tid) by reflexivity.
    clearbody vals.

    run_block_keep scr0 41%nat.
    lazymatch goal with EQM : ?M1 = mem_denot _ M0 ?lg |- _ =>
      assert (RA1 : rabs MI A M1 mo) by (rewrite EQM; apply (rabs_after_log vals M0 lg RA P0); vm_compute; reflexivity);
      clear EQM end.

    stdio_then_tail vals scS msg_short msg_short_img 0x1409c%Z srSB knSB HL P0 P3 P4 HR HK RA1 MH ML Uspw.
  Qed.

  Theorem header_overrun :
    (6 <= length content)%nat -> (Z.of_nat (length content) < 6 + hdr_cfglen content)%Z ->
    srealizes RSEGS (mkCfg (mkst R0 (Z_to_bv 64 0x656e4) M0 (seg_rom RSEGS)) mo) (t_die msg_overrun fs0).
  Proof.
    intros Hge Hov. destruct hdr_sym as (HR & HK0).
    pose proof (hdr_know_long HK0 Hge) as HK. clear HK0.
    pose proof re_facts as (P1f & P2 & P3c & P4c). pose proof HAC as Hcv. pose proof ac_bounds_lit as Hcb.
    pose proof (re_abs _ _ _ _ _ _ _ _ _ _ _ _ _ _ RE) as RA.
    pose proof (ms_halt _ (ra_mstd _ _ _ _ RA)) as MH. pose proof (ms_lazy _ (ra_mstd _ _ _ _ RA)) as ML.
    assert (Uspw : bv_unsigned spw = sp0) by (unfold spw; apply u_small; lia).
    pose proof (hdr_cfglen_range content) as CR. assert (LB : (0 <= L < 2 ^ 26)%Z) by (unfold L; lia).
    set (vals := valsh) in *.
    assert (HL : length vals = 41%nat) by (subst vals; unfold valsh; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = spw) by reflexivity.
    assert (P3 : vals_ev vals 3 = pw) by reflexivity.
    assert (P4 : vals_ev vals 4 = Z_to_bv 64 tid) by reflexivity.
    assert (P5 : vals_ev vals 5 = Z_to_bv 64 L) by reflexivity.
    assert (P6 : vals_ev vals 6 = Z_to_bv 64 (hdr_b0 content)) by reflexivity.
    assert (P7 : vals_ev vals 7 = Z_to_bv 64 (hdr_b1 content)) by reflexivity.
    clearbody vals.

    run_block_keep scr_taken 41%nat.
    {
      unfold sc_denot. fold cfglen_x. cbn [edenot].
      rewrite (cfglen_val content vals P6 P7). change (ev (ENVh content vals) 5) with (vals_ev vals 5). rewrite P5.
      rewrite alu_add. unfold v_add. cbn [branch_taken]. unfold bv_ltu.
      rewrite (u_small (hdr_cfglen content)) by lia. change (bv_unsigned (Z_to_bv 64 6)) with 6%Z.
      rewrite !u_small by lia. apply Z.ltb_lt. lia. }
    lazymatch goal with EQM : ?M1 = mem_denot _ M0 ?lg |- _ =>
      assert (RA1 : rabs MI A M1 mo) by (rewrite EQM; apply (rabs_after_log vals M0 lg RA P0); vm_compute; reflexivity);
      clear EQM end.

    stdio_then_tail vals scO msg_overrun msg_overrun_img 0x11537%Z srOB knOB HL P0 P3 P4 HR HK RA1 MH ML Uspw.
  Qed.

  Theorem header_ok : forall K,
    (6 + hdr_cfglen content <= Z.of_nat (length content))%Z ->
    (forall R' M', tpre MI sp0 tid p1 path TIGHT content fs0 p cap A R' M' mo ->
       srealizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x658b8) M' (seg_rom RSEGS)) mo) K) ->
    srealizes RSEGS (mkCfg (mkst R0 (Z_to_bv 64 0x656e4) M0 (seg_rom RSEGS)) mo) K.
  Proof.
    intros K Hok HK_T. destruct hdr_sym as (HR & HK0).
    pose proof (hdr_cfglen_range content) as CR.
    pose proof (hdr_know_long HK0 ltac:(lia)) as HK. clear HK0.
    pose proof re_facts as (P1f & P2 & P3c & P4c). pose proof HAC as Hcv. pose proof ac_bounds_lit as Hcb.
    pose proof (re_abs _ _ _ _ _ _ _ _ _ _ _ _ _ _ RE) as RA.
    pose proof (ms_halt _ (ra_mstd _ _ _ _ RA)) as MH. pose proof (ms_lazy _ (ra_mstd _ _ _ _ RA)) as ML.
    assert (Uspw : bv_unsigned spw = sp0) by (unfold spw; apply u_small; lia).
    assert (Upw : bv_unsigned pw = p) by (unfold pw; apply u_small; lia).
    assert (LB : (0 <= L < 2 ^ 26)%Z) by (unfold L; lia).
    pose proof (bv_unsigned_in_range _ (nth 1 content (Z_to_bv 8 0))) as B1. change (bv_modulus 8) with 256%Z in B1.

    set (cb := fun i : nat => Z_to_bv 64 (bv_unsigned (nth (Z.to_nat (hdr_cfglen content) + 2 + i) content (Z_to_bv 8 0)))).
    assert (HL : length valsh = 41%nat) by (unfold valsh; rewrite length_app, junk_vals_length; reflexivity).

    pose proof (env_app_regs valsh [cb 1%nat; cb 0%nat; cb 2%nat; cb 3%nat] (blobs_ev [content]) sr_H R0
                  ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR1.
    pose proof (env_app_know RSEGS valsh [cb 1%nat; cb 0%nat; cb 2%nat; cb 3%nat] (blobs_ev [content]) M0 kn_long
                  ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK1.
    clear HR HK.
    set (vals := valsh ++ [cb 1%nat; cb 0%nat; cb 2%nat; cb 3%nat]) in *.
    change (Env (vals_ev vals) (blobs_ev [content])) with (ENVh content vals) in HR1, HK1.
    rename HR1 into HR. rename HK1 into HK.
    assert (P0 : vals_ev vals 0 = spw) by reflexivity.
    assert (P3 : vals_ev vals 3 = pw) by reflexivity.
    assert (P5 : vals_ev vals 5 = Z_to_bv 64 L) by reflexivity.
    assert (P6 : vals_ev vals 6 = Z_to_bv 64 (hdr_b0 content)) by reflexivity.
    assert (P7 : vals_ev vals 7 = Z_to_bv 64 (hdr_b1 content)) by reflexivity.
    assert (PB41 : vals_ev vals 41 = cb 1%nat).
    { unfold vals. replace 41%nat with (length valsh + 0)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    assert (PB42 : vals_ev vals 42 = cb 0%nat).
    { unfold vals. replace 42%nat with (length valsh + 1)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    assert (PB43 : vals_ev vals 43 = cb 2%nat).
    { unfold vals. replace 43%nat with (length valsh + 2)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    assert (PB44 : vals_ev vals 44 = cb 3%nat).
    { unfold vals. replace 44%nat with (length valsh + 3)%nat by (rewrite HL; reflexivity). rewrite vals_ev_app_r. reflexivity. }
    clearbody vals.
    pose proof (cfglen_val content vals P6 P7) as CV.

    assert (CB : forall i, (i < 4)%nat ->
      rdn RSEGS M0 (Z_to_bv 64 (p + hdr_cfglen content + 2 + Z.of_nat i)) 1%nat
      = Some [nth (Z.to_nat (hdr_cfglen content) + 2 + i) content (Z_to_bv 8 0)]).
    { intros i Hi.
      replace (p + hdr_cfglen content + 2 + Z.of_nat i)%Z
        with (p + Z.of_nat (Z.to_nat (hdr_cfglen content) + 2 + i))%Z by lia.
      rewrite content_byte by lia. rewrite w2le1_byte. reflexivity. }

    run_block_keep scr_fall 41%nat.
    all: try (unfold sc_denot; fold cfglen_x).

    all: try (lazymatch goal with
              | |- branch_taken _ _ _ = false =>
                  cbn [edenot]; rewrite CV; change (ev (ENVh content vals) 5) with (vals_ev vals 5); rewrite P5;
                  rewrite alu_add; unfold v_add; cbn [branch_taken]; unfold bv_ltu;
                  rewrite (u_small (hdr_cfglen content)) by lia; change (bv_unsigned (Z_to_bv 64 6)) with 6%Z;
                  rewrite !u_small by lia; apply Z.ltb_ge; lia
              end).

    all: try (lazymatch goal with
              | |- exists bs, rdn _ _ (adenot _ (SA _ ?k)) 1 = Some bs /\ _ =>
                  let i := eval vm_compute in (Z.to_nat (k - 2)) in
                  eexists; split;
                  [ unfold adenot, v_addi; cbn [a_base a_off edenot]; rewrite CV;
                    change (ev (ENVh content vals) 3) with (vals_ev vals 3); rewrite P3;
                    rewrite alu_add; unfold v_add; rewrite Upw;
                    rewrite (u_small (hdr_cfglen content)) by lia; rewrite !u_small by lia;
                    replace (p + hdr_cfglen content + k)%Z
                      with (p + hdr_cfglen content + 2 + Z.of_nat i)%Z by lia;
                    apply (CB i); lia
                  | lazymatch goal with |- _ = edenot _ (EVar ?n) => change (edenot (ENVh content vals) (EVar n)) with (vals_ev vals n) end;
                    first [rewrite PB41 | rewrite PB42 | rewrite PB43 | rewrite PB44];
                    unfold cb, extz; cbn [lez bytes_le_to_Z Z.shiftl]; rewrite Z.lor_0_r; reflexivity ]
              | |- flat _ (SA _ ?k) _ =>
                  unfold flat, estart, elenZ; cbn [a_base a_off]; fold cfglen_x; cbn [edenot]; rewrite CV;
                  change (ev (ENVh content vals) 3) with (vals_ev vals 3); rewrite P3;
                  rewrite alu_add; unfold v_add; rewrite Upw; rewrite (u_small (hdr_cfglen content)) by lia; rewrite !u_small by lia; lia
              end).
    all: let n := numgoals in idtac "after-block goals:" n.

    lazymatch goal with |- srealizes _ (mkCfg (mkst _ _ ?Mx _) _) _ =>
      lazymatch goal with EQ : Mx = _ |- _ => cbn [mem_denot] in EQ; subst Mx end end.
    apply HK_T.
    assert (A6 : edenot (ENVh content vals) (EAlu ALU_ADD (EAlu ALU_ADD (EVar 3) cfglen_x) (ELit 6))
                  = Z_to_bv 64 (p + 6 + hdr_cfglen content)).
    { cbn [edenot]. rewrite CV. change (ev (ENVh content vals) 3) with (vals_ev vals 3); rewrite P3.
      rewrite !alu_add. unfold v_add. rewrite (alu_add pw). unfold v_add. rewrite Upw. rewrite (u_small (hdr_cfglen content)) by lia.
      rewrite (u_small (p + hdr_cfglen content)) by lia. change (bv_unsigned (Z_to_bv 64 6)) with 6%Z. f_equal. lia. }
    assert (APL : edenot (ENVh content vals) (EAlu ALU_ADD (EAlu ALU_ADD (EVar 5) (EMd M_MUL (ELit (-1)) cfglen_x)) (ELit (-6)))
                  = Z_to_bv 64 (hdr_paylen content)).
    { cbn [edenot]. rewrite CV. change (ev (ENVh content vals) 5) with (vals_ev vals 5); rewrite P5.
      rewrite !alu_add, m_mul. unfold v_add, v_mul. rewrite ?alu_add. unfold v_add.
      apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
      rewrite (Z.mod_small L), (Z.mod_small (hdr_cfglen content)) by lia.
      change ((-1) mod 2 ^ 64)%Z with 18446744073709551615%Z. change ((-6) mod 2 ^ 64)%Z with 18446744073709551610%Z.
      rewrite Zplus_mod_idemp_l.
      replace (L + (18446744073709551615 * hdr_cfglen content) mod 2 ^ 64 + 18446744073709551610)%Z
        with (L + 18446744073709551610 + (18446744073709551615 * hdr_cfglen content) mod 2 ^ 64)%Z by lia.
      rewrite Zplus_mod_idemp_r.
      apply (mod_eq_shift _ _ (hdr_cfglen content + 1)); [lia|]. unfold hdr_paylen, L. lia. }
    assert (AP2 : edenot (ENVh content vals) (EAlu ALU_ADD (EVar 3) (ELit 2)) = Z_to_bv 64 (p + 2)).
    { rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVh]. rewrite P3, Upw. reflexivity. }
    constructor.
    - regv HR (1 : reg). reflexivity.
    - regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENVh]. rewrite P0, Uspw. f_equal; lia.
    - regv HR (3 : reg). reflexivity.
    - regv HR (4 : reg). reflexivity.
    - regv HR (8 : reg). exact AP2.
    - regv HR (9 : reg). cbn [edenot ev ENVh]. exact P3.
    - regv HR (10 : reg). exact AP2.
    - regv HR (11 : reg). exact CV.
    - regv HR (12 : reg). exact A6.
    - regv HR (13 : reg). exact APL.
    - regv HR (18 : reg). exact CV.
    - regv HR (19 : reg). exact A6.
    - regv HR (20 : reg). exact APL.
    - regv HR (21 : reg). change (edenot (ENVh content vals) (EExt true 0 1 (EVar 7))) with (sx8F (vals_ev vals 7)).
      rewrite P7. apply sx8F_val. unfold hdr_b1. lia.
    - regv HR (22 : reg). reflexivity.
    - exact (re_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ RE).
    - exact RA.
    - exact (re_tight _ _ _ _ _ _ _ _ _ _ _ _ _ _ RE).
    - exact (re_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ RE).
    - unfold L in *. lia.
    - exact Hok.
    - exact (re_content _ _ _ _ _ _ _ _ _ _ _ _ _ _ RE).
    - exact (re_fds _ _ _ _ _ _ _ _ _ _ _ _ _ _ RE).
    - exact (re_fs _ _ _ _ _ _ _ _ _ _ _ _ _ _ RE).
  Qed.

End Header.
End FXALL2.
