(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3Sound HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import PmLibDefs_u PmLibSpecs_u PmLayout_u PmFloatCSpecs_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import MState Mem Exec Frame Cells Step Arr.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Bridge Require Import BrRegs BrBase BrXfer BrMem.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.TU Require Import FiWalk_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmGrow Require Import GrowKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTU Require Import TuWdBr_u TuFromInt_u.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module TFI64.
Section F.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.

Lemma heap_keep_fi : forall SP o LB cr (M M' : PML.mem) VM, hl_sptop L - 2 ^ 23 + 384 <= SP -> SP <= o -> o + 24 <= hl_sptop L ->
  0x7fff80000000 <= hl_sptop L <= 2 ^ 47 -> hi_heap HI LB cr M VM ->
  (forall x : word, outside (FI_W SP o) (bv_unsigned x) -> M' x = M x) ->
  (forall a, (SP - 384 <= a < SP) \/ (o <= a < o + 24) -> M' (Z_to_bv 64 a) <> None) ->
  hi_heap HI LB cr M' VM.
Proof.
  intros SP o LB cr M M' VM H1 H2 H3 H4 HH Hf Hd. apply (hio_frame L SCFG HI HIok LB cr M M' VM HH).
  - intros a Ha HP. apply Hf. rewrite L5.unsigned_lit by lia. unfold FI_W. cbn [outside].
    destruct HP as [(P1 & _) | P]; [lia|]. apply (PmLayout.ly_ro L LAY) in P. rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY) in P. lia.
  - intros x Hx. destruct (classic (outside (FI_W SP o) (bv_unsigned x))) as [HO|HO].
    + rewrite (Hf x HO). exact Hx.
    + rewrite <- (Z_to_bv_bv_unsigned x). apply Hd. unfold FI_W in HO. cbn [outside] in HO. pose proof (u64_range x). lia.
Qed.

Lemma hpres_fi : forall SP o LB cr (M M' : PML.mem) VM scr, hi_heap HI LB cr M VM -> 384 <= scr -> SP <= o ->
  hl_sptop L - 2 ^ 23 + scr <= SP -> o + 24 <= hl_sptop L -> 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 ->
  L5.defined M (SP - scr) scr ->
  (forall x : word, outside (FI_W SP o) (bv_unsigned x) -> M' x = M x) ->
  (forall a, (SP - 384 <= a < SP) \/ (o <= a < o + 24) -> M' (Z_to_bv 64 a) <> None) ->
  L5C.hpres L LB SP scr [(o, 24)] M M'.
Proof.
  intros SP o LB cr M M' VM scr HH Hs H1 H2 H3 H4 HD Hf Hd.
  assert (ILO : hl_img_lo L = 0x10000) by exact (PmLayout.ly_img_lo L LAY). assert (IHI : hl_img_hi L = 0xf8000) by exact (PmLayout.ly_img_hi L LAY).
  assert (HBL : forall b, In b LB -> fst b + snd b <= hl_ceil L).
  { intros b Hb. destruct (hio_wf L SCFG HI HIok LB cr M VM HH) as (WF & _). destruct (WF b Hb) as ((_ & _ & _ & _ & X) & _). exact X. }
  apply L5C.hpres_intro.
  - intros a (Ka & KC & KE & KW). apply Hf. rewrite L5.unsigned_lit by lia. unfold FI_W. cbn [outside].
    assert (Hoa : ~ (o <= a < o + 24)) by (intros Hin; exact (KW (o, 24) (or_introl eq_refl) Hin)).
    split; [|split; [lia | exact I]].
    destruct KC as [(b & Hb & Hr) | [(C1 & C2) | (C1 & C2)]]; [pose proof (HBL b Hb); lia | lia | lia].
  - intros j Hj. destruct (Z_lt_dec j (scr - 384)) as [Hlt|Hge].
    + rewrite Hf; [apply HD; lia|]. rewrite L5.unsigned_lit by lia. unfold FI_W. cbn [outside]. lia.
    + apply Hd. lia.
  - intros a Ha HC HE HN. destruct (classic ((SP - 384 <= a < SP) \/ (o <= a < o + 24))) as [HR|HR]; [apply Hd; exact HR|].
    rewrite Hf; [exact HN|]. rewrite L5.unsigned_lit by lia. unfold FI_W. cbn [outside]. lia.
Qed.

Theorem from_integer_i64_ok : PMFC.from_integer_i64_spec L HI.
Proof.
  intros LB cr o v sp r. unfold PML.cps_heap.
  intros fx R M model K HH Hmo HKnil Hfp (Hentry & Ha0 & Hv & Ha1 & Hstr & Hdo & Hobj & Himg) Hcont.
  destruct Hentry as (Hra & Hraok & Hsp & Htp & Hstk). destruct Hstk as (S1 & S2 & S3 & S4 & S5).
  replace (PMFC.FROMINT_SCR) with 8816 in S2, S5 by vmc_refl.
  destruct Hobj as (O1 & O2 & O3). pose proof Hmo as (Hh & Hl & _).
  assert (Hr64 : 0 <= r < 2 ^ 64) by (destruct Hraok; lia).
  unfold PML.cfg. eapply TWB.cj_evt_srz; [exact Hh | exact Hl | |].
  - unfold canon_regs. rewrite Hsp. unfold PML.a0, PML.a1 in Ha0, Ha1. rewrite Ha0, Ha1.
    eapply (fi_entry (getr R 1) (getr R 3) (getr R 4) (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22)
                     (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) (@fp_regs fx) (@fp_csr fx) sp o M).
    all: try lia.
    + apply u8arr_of_rw_cells with (n := 24%nat). apply TWB.defined_rw_cells; [exact Hdo | lia | lia].
    + apply TWB.ovl_bytes_length.
    + destruct Hstr as (_ & Hb0 & _ & _). cbn [length Z.of_nat] in Hb0. rewrite Z.mul_0_r in Hb0.
      pose proof (Hdo 0 ltac:(lia)) as D0. rewrite Z.add_0_r in D0.
      unfold L5.u8_at in Hb0. pose proof (CL5.overlay_byte _ _ _ _ Hb0 D0) as E0.
      rewrite <- (TWB.ovl_bytes_nth M o 24 0 ltac:(lia)); [unfold wa; rewrite Z.add_0_r; exact E0 | unfold wa; rewrite Z.add_0_r; exact D0].
    + destruct Hstr as (_ & _ & _ & Hb1). cbn [length Z.of_nat] in Hb1. rewrite Z.add_0_r in Hb1.
      pose proof (Hdo 1 ltac:(lia)) as D1. unfold L5.u8_at in Hb1. pose proof (CL5.overlay_byte _ _ _ _ Hb1 D1) as E1.
      rewrite <- (TWB.ovl_bytes_nth M o 24 1 ltac:(lia)); [unfold wa; exact E1 | unfold wa; exact D1].
    + apply TWB.stk_of_defined; [| lia | lia]. replace (sp - (sp - 384)) with 384 by lia. eapply L5.defined_sub; [exact S5 | lia | lia].
    + apply TWB.mem_inv_of_clear. intros i Hi. apply Himg. unfold PML.IMG_RO_HI. lia.
    + reflexivity.
  -
    intros ms1 ms1' HP EQV. unfold fi_post in HP.
    destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & c & bs & -> & Hc & BU & BL & B0 & BN & ST & MU & WM & MI).
    destruct (ms_eqv_MS_inv _ _ _ _ _ _ _ EQV) as [Ems REQ]. rewrite Ems. set (R' := ms_regs ms1') in *.
    assert (RG : forall n, getr (mkR (getr R 1) (Z_to_bv 64 sp) (getr R 3) (getr R 4) t0' t1' t2' (getr R 8) (getr R 9) (Z_to_bv 64 c) a1' a2' a3' a4' a5' a6' a7'
                    (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)
                    t3' t4' t5' t6') n = getr R' n) by (intros n; apply getr_eqv; exact REQ).
    replace (ret_pc (getr R 1)) with (Z_to_bv 64 r) by (rewrite Hra; symmetry; apply ret_pc_even; [lia | exact (proj2 Hraok)]).
    change (mkCfg (MS R' (@fp_regs fx) (Z_to_bv 64 r) (@fp_csr fx) None m' (seg_rom TWB.CSEGS)) model) with (@PML.cfg fx R' r m' model).
    assert (DOB : L5.defined m' o 24) by (pose proof (TWB.u8arr_defined _ _ _ BU ltac:(lia)) as X; rewrite BL in X; exact X).
    assert (DST : L5.defined m' (sp - 384) 384) by (pose proof (TWB.stk_defined _ _ _ ST ltac:(lia) ltac:(lia)) as X; replace (sp - (sp - 384)) with 384 in X by lia; exact X).
    assert (HD : forall a, (sp - 384 <= a < sp) \/ (o <= a < o + 24) -> m' (Z_to_bv 64 a) <> None).
    { intros a [Ha|Ha]; [pose proof (DST (a - (sp - 384)) ltac:(lia)) as X | pose proof (DOB (a - o) ltac:(lia)) as X];
        match type of X with _ (Z_to_bv 64 ?e) <> None => replace e with a in X by lia end; exact X. }
    destruct (TFI.bytes_of_defined m' (Z.to_nat c) (o + 1) ltac:(lia) ltac:(lia)) as (s' & Hsl & Hbs).
    { rewrite Z2Nat.id by lia. intros j Hj. replace (o + 1 + j) with (o + (1 + j)) by lia. apply DOB. lia. }
    assert (LEN : Z.of_nat (length s') = c) by (rewrite Hsl; apply Z2Nat.id; lia).
    apply (Hcont fx R' m' model LB cr LB [(o, 24)] Hfp).
    + exists s'. split; [lia|]. split.
      * unfold PML.str_at, L5.lstr_short. rewrite LEN. split; [lia|]. split; [|split; [exact Hbs|]].
        -- pose proof (TWB.u8_of_u8arr m' o bs 0 _ BU B0) as X. rewrite Z.add_0_r in X.
           replace (bv_unsigned (Z_to_bv 8 (2 * c))) with (2 * c) in X; [exact X|].
           rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn -[Z.pow]. rewrite Z.mod_small; [reflexivity | lia].
        -- pose proof (TWB.u8_of_u8arr m' o bs (Z.to_nat (1 + c)) _ BU BN) as X. rewrite Z2Nat.id in X by lia. replace (o + (1 + c)) with (o + 1 + c) in X by lia. exact X.
      * split; [unfold PML.a0; rewrite <- RG; rewrite LEN; reflexivity|]. repeat split.
    + intros y Hy. unfold callee_saved_idx in Hy. rewrite <- (definitions.Z_to_bv_bv_unsigned _ y). rewrite <- RG.
      cbn [In] in Hy. repeat (destruct Hy as [Hy|Hy]; [rewrite <- Hy; first [reflexivity | (transitivity (Z_to_bv 64 sp); [reflexivity | rewrite <- Hsp; reflexivity])] |]).
      destruct Hy.
    + replace PMFC.FROMINT_SCR with 8816 by vmc_refl.
      apply (hpres_fi sp o LB cr M m' (m_vmmaps model) 8816 HH ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S5 MU HD).
    + apply L5C.model_but_vm_refl.
    + apply (heap_keep_fi sp o LB cr M m' (m_vmmaps model) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HH MU HD).
Qed.
End F.
End TFI64.
