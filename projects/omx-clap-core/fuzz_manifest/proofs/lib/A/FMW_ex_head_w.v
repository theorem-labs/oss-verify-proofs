(* G4.ExHead.HeadWord: the inlined ex_prefix_word loop of expected's scan head (fuzz_manifest.c:86-92) on fm.asan:
   hd_W, from EX_W 0x812a4 (a2 = k) to EX_CONT/EX_L (mismatch), to EX_W at k + 1 (match, k < 5) or to EX_TL (k = 5).
   Each iteration: the word's shadow byte s (IMG's cstr_ok of ex_prefix_word.word 0x20d20: s = 0 or 7), the entry state
   ss_W k s (hd_W_entry), a run to 0x812d8, the word byte region (hd_W_swap), a run to the beq 0x812dc, the branches. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib FMW_ex_base FMW_ex_head_d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_ex_head_m FMW_ex_head_e FMW_ex_head_x FMW_ex_head_t.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ---- pure helpers ---- *)
Lemma hw_m_eq : forall c w : Z, (c =? w) = true -> ((c =? w) || (c =? w - 32)) = true.
Proof. intros c w H. rewrite H. reflexivity. Qed.
Lemma hw_m_eq32 : forall c w : Z, negb (w - 32 =? c) = false -> ((c =? w) || (c =? w - 32)) = true.
Proof.
  intros c w H. apply Bool.negb_false_iff in H. rewrite Z.eqb_sym in H. rewrite H. apply Bool.orb_true_r.
Qed.

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* after A/FMpoisonW.v val_mem1_of_aview (with A/AE2y.v aview_byte_ex inlined) *)
Lemma hw_val1_of_aview : forall H mem a v,
  aview tfibsegs H mem a = Some v -> val_mem tfibsegs (mrestrict H mem) a 1 v.
Proof.
  intros H mem a v Hv. unfold aview in Hv.
  destruct (mbyte tfibsegs (mrestrict H mem) a) as [b|] eqn:Hb; [|discriminate].
  cbn in Hv. injection Hv as <-.
  intros k Hk. replace k with 0%nat by lia.
  cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal. unfold le_byte, YG0f.le_byte, YO0f.le_byte.
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R.
  change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
  rewrite Z.mod_mod by lia. rewrite Z.mod_small by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma hw_cfg : forall W pc regs mem md (Q : world tfibsegs -> config -> Prop),
  SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) Q ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs)) md) Q.
Proof. intros W pc regs mem md Q H. exact H. Qed.
End f.

(* ---- tactics (after FMW_plain.v fw_reg, pl_mk, pl_g, pl_av) ---- *)
Ltac hw_reg HS r :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    rewrite (st_ok_restrict_reg segs H E ss ms r HS); change (sr_get (ss_regs ss) r) with e end.
Ltac hw_mk HS := rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl);
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
    let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end.
Ltac hw_g HS :=
  lazymatch goal with |- getr _ ?r = _ => hw_reg HS r end;
  cbn [sv_denot ew ewset Nat.eqb]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
Ltac hw_av :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- _ =>
    let AVn := fresh "AVn" in
    pose proof (fw_nowin tfibsegs _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as AVn;
    lazymatch goal with AV : forall a, _ -> aview ?sg ?Hw m0 a = aview _ _ ?mem1 a |- _ =>
      let AV2 := fresh "AV" in
      assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> aview sg Hw m1 a = aview sg Hw mem1 a)
        by (intros a Ha; rewrite (AVn a Ha); exact (AV a Ha));
      clear AV AVn; rename AV2 into AV end end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  repeat match goal with H : context [with_vm_backing (m_vm_lazy (with_vm_backing _ _ _)) _ _] |- _ =>
    rewrite wvb_collapse in H end.

(* The iteration's facts are found by their shape: the entry env E with EE (registers), E19/E20/E25/E32 (atoms
   19, 20, 25, 32), the text byte c with Hceq, the entry facts (ex_at_L at the EX_W state, Hik, ...), AV (memory kept),
   VW (the word bytes), IH (the next iteration). *)
Ltac hw_EE := lazymatch goal with H : forall (n : nat) (q : _), _ -> ew _ n = getr _ q |- _ => apply H; reflexivity end.
Ltac hw_U32 Hc :=
  first [rewrite branch_eq_U in Hc | rewrite branch_ne_U in Hc];
  lazymatch goal with H32 : ew _ 32 = Z_to_bv 64 ?c0 |- _ =>
    rewrite (U_atom _ 32 c0) in Hc by (first [cbn [ew ewset Nat.eqb]; exact H32 | lia]) end;
  rewrite U_SLit, zcanon_id in Hc by (unfold M64; lia).
Ltac hw_kept HS := unfold hd_kept_regs; repeat match goal with |- _ /\ _ => split end;
  hw_g HS; first [hw_EE | symmetry; assumption].
Ltac hw_lits HS := unfold hd_lits; repeat match goal with |- _ /\ _ => split end;
  hw_g HS; first [reflexivity | apply bv_eq; vm_compute; reflexivity].
Ltac hw_getr HS := hw_g HS;
  first [ reflexivity | assumption | hw_EE
        | lazymatch goal with H19 : ew _ 19 = w64 _ |- _ => rewrite H19 end;
          unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia ].
Ltac hw_ci :=
  first [eapply hd_m_ci_step | change ManifestModel.prefix_lc with (firstn 6 ManifestModel.prefix_lc); eapply hd_m_ci_step];
  [lia | lia | assumption |
   lazymatch goal with Hn : nth _ (_ ++ [0]) 0 = nth _ _ 0 |- _ => rewrite <- Hn end; assumption].
Ltac hw_scan :=
  apply hd_m_scan_step; [assumption | assumption | apply hd_m_none_ci; [assumption |
    eapply hd_m_ci_fail; [eassumption | lia | eassumption | eassumption]]].
Ltac hw_keep :=
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha _;
  lazymatch goal with AV : forall x, 0 <= x < 2 ^ 64 -> aview _ _ _ x = aview _ _ _ x |- _ => exact (AV a Ha) end.
Ltac hw_close0 HS HJ :=
  lazymatch goal with
  | |- hd_jr _ _ _ _ _ _ _ => exact HJ
  | |- hd_keep _ _ _ _ => hw_keep
  | |- hd_kept_regs _ _ => hw_kept HS
  | |- hd_lits _ => hw_lits HS
  | |- getr _ _ = _ => hw_getr HS
  | |- ex_at_L _ _ _ _ _ _ _ _ _ _ _ => lazymatch goal with H : ex_at_L _ _ _ _ _ _ _ _ _ _ _ |- _ => exact H end
  end.
Ltac hw_at HS HJ :=
  lazymatch goal with H : ex_at_L _ _ _ _ _ _ _ _ ?r ?m ?md |- _ =>
    eapply hd_at_step with (regs1 := r) (mem1 := m) (md1 := md) end;
  hw_close0 HS HJ.
Ltac hw_close HS HJ :=
  lazymatch goal with
  | |- ex_seg_L_from _ _ _ => lazymatch goal with H : ex_seg_L_from _ _ _ |- _ => exact H end
  | |- ex_seg_P _ => lazymatch goal with H : ex_seg_P _ |- _ => exact H end
  | |- ex_at_L _ _ _ _ _ _ _ _ (ms_regs _) _ _ => hw_at HS HJ
  | |- ex_scan _ _ _ _ => hw_scan
  | |- hd_arm1 _ _ = false => lazymatch goal with H : hd_arm1 _ _ = false |- _ => exact H end
  | |- ManifestModel.ci_eqb _ _ = true => hw_ci
  | |- (_ < _)%nat => lia
  | |- (_ <= _)%nat => lia
  | |- _ => hw_close0 HS HJ
  end.
Ltac hw_swap HS kz sz :=
  lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict (w_H ?Wx) ?msx) =>
  lazymatch goal with
  | AV : forall x, _ -> aview _ _ _ x = aview _ _ ?m1 x |- _ =>
    let HS2 := fresh "HS2" in
    assert (HS2 : st_ok tfibsegs Ex
      (mkSS (ss_pc ssx) (ss_regs ssx) [hd_wbyte kz; hd_wsh sz] (ss_resv ssx) (ss_facts ssx)) (restrict (w_H Wx) msx));
    [ eapply hd_W_swap with (k := kz) (s := sz);
      [ exact HS | vm_compute; reflexivity | vm_compute; reflexivity
      | cbn [ew ewset Nat.eqb]; lazymatch goal with H25 : ew _ 25 = _ |- _ => exact H25 end
      | lia
      | rewrite restrict_mem; apply (fw_val_eqv tfibsegs (w_H Wx) m1 (ms_mem msx));
        [ exact AV | unfold EX_WORD; lia | unfold EX_WORD; lia
        | lazymatch goal with VW : forall k, _ -> val_mem _ _ (EX_WORD + k) _ _ |- _ => apply VW; lia end ] ]
    | clear HS; rename HS2 into HS ] end end.
Ltac hw_next HS HJ SHOK :=
  aj_run_to_tok EX_tbl_ok HS HJ SHOK HD_Bspan EX_W; [awr_ok_tac|];
  hw_av; hw_mk HS;
  apply (hw_cfg _ EX_W);
  lazymatch goal with
  | IH : (_ < 5)%nat -> _, HA : ex_at_L _ ?cx ?i ?d ?f ?ly ?S ?W _ _ _,
    LF : ex_seg_L_from _ _ _, SP : ex_seg_P _ |- _ =>
    eapply (IH ltac:(lia) cx i d f ly S W _ _ _ LF SP) end;
  hw_close HS HJ.
Ltac hw_tl HS HJ SHOK :=
  aj_run_to_tok EX_tbl_ok HS HJ SHOK HD_Bspan EX_TL; [awr_ok_tac|];
  hw_av; hw_mk HS;
  apply (hw_cfg _ EX_TL);
  lazymatch goal with HA : ex_at_L _ ?cx ?i ?d ?f ?ly ?S ?W _ _ _ |- _ =>
    eapply hd_T with (cx := cx) (i := i) (d := d) (f := f) (ly3 := ly) (S3 := S) end;
  hw_close HS HJ.
(* a match (text byte = w_k or w_k - 32): the next iteration (k < 5) or EX_TL (k = 5) *)
Ltac hw_go lem Hc HS HJ SHOK :=
  lazymatch goal with H32 : ew _ 32 = Z_to_bv 64 ?c0 |- _ =>
  lazymatch goal with Hceq : c0 = nth _ (_ ++ [0]) 0 |- _ =>
  lazymatch goal with Hk : (?i0 + ?kn <= length ?t0)%nat |- _ =>
    let HM0 := fresh "HM0" in
    assert (HM0 : ((nth (i0 + kn) (t0 ++ [0]) 0 =? nth kn ManifestModel.prefix_lc 0) ||
                   (nth (i0 + kn) (t0 ++ [0]) 0 =? nth kn ManifestModel.prefix_lc 0 - 32)) = true)
      by (rewrite <- Hceq; apply lem; exact Hc);
    clear Hc;
    let Hlt := fresh "Hlt" in let Hnth := fresh "Hnth" in
    destruct (hd_m_match_lt t0 i0 kn Hk ltac:(lia) HM0) as [Hlt Hnth];
    lazymatch kn with
    | 5%nat => hw_tl HS HJ SHOK
    | _ => hw_next HS HJ SHOK
    end end end end.
(* a mismatch: EX_CONT, then EX_L at i + 1 *)
Ltac hw_exitL HS HJ SHOK D1 D2 :=
  lazymatch goal with H32 : ew _ 32 = Z_to_bv 64 ?c0 |- _ =>
  lazymatch goal with Hceq : c0 = nth _ (_ ++ [0]) 0 |- _ =>
    rewrite Hceq in D1; apply Bool.negb_true_iff in D2; rewrite Z.eqb_sym, Hceq in D2 end end;
  aj_run_to_tok EX_tbl_ok HS HJ SHOK HD_Bspan EX_L; [awr_ok_tac|];
  hw_av; hw_mk HS;
  apply (hw_cfg _ EX_L);
  lazymatch goal with HA : ex_at_L _ ?cx ?i ?d ?f ?ly ?S ?W ?r ?m ?md |- _ =>
    eapply hd_exit_L with (i := i) (d := d) (f := f) (f' := pred f) (ly3 := ly) (S3 := S)
      (regs1 := r) (mem1 := m) (md1 := md) end;
  hw_close HS HJ.
Ltac hw_case HS HJ SHOK :=
  lazymatch type of HS with st_ok _ _ (ss_W ?kz0 ?sz) _ =>
    let kz := eval vm_compute in kz0 in
    aj_run_tok EX_tbl_ok HS HJ SHOK HD_Bspan; [awr_ok_tac|];
    hw_av;
    hw_swap HS kz sz;
    aj_run_tok EX_tbl_ok HS HJ SHOK HD_Bspan; [awr_ok_tac|];
    hw_av;
    srr_branch_tok EX_tbl_ok HS SHOK HD_Bspan;
    [ lazymatch goal with Hc : branch_taken _ _ _ = _ |- _ => hw_U32 Hc; hw_go hw_m_eq Hc HS HJ SHOK end
    | lazymatch goal with D1 : branch_taken _ _ _ = _ |- _ =>
        hw_U32 D1;
        aj_run_tok EX_tbl_ok HS HJ SHOK HD_Bspan; [awr_ok_tac|];
        hw_av;
        srr_branch_tok EX_tbl_ok HS SHOK HD_Bspan;
        [ lazymatch goal with D2 : branch_taken _ _ _ = _ |- _ => hw_U32 D2; hw_exitL HS HJ SHOK D1 D2 end
        | lazymatch goal with Hc : branch_taken _ _ _ = _ |- _ => hw_U32 Hc; hw_go hw_m_eq32 Hc HS HJ SHOK end ]
      end ]
  end.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis IMG : fm_img_facts tfibsegs B.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* ex_prefix_word.word (0x20d20, "prefix", an asan global): its shadow byte and its bytes at an EX_W state *)
Lemma hw_word_facts : forall cx i d f ly3 S3 W3 regs1 mem1 md1,
  ex_at_L B cx i d f ly3 S3 W3 regs1 mem1 md1 ->
  (exists s, val_mem tfibsegs (mrestrict (w_H W3) mem1) (SHADOW_OFF + HD_WSH) 1 s /\ (s = 0 \/ s = 7)) /\
  (forall k, 0 <= k < 6 -> val_mem tfibsegs (mrestrict (w_H W3) mem1) (EX_WORD + k) 1
     (nth (Z.to_nat k) ManifestModel.prefix_lc 0)).
Proof.
  intros cx i d f ly3 S3 W3 regs1 mem1 md1 HAT.
  destruct HAT as (_ & HC & _).
  destruct HC as (HJ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
  destruct (IMG ly3 S3 W3 mem1 md1 (proj1 HJ) HRO) as (_ & _ & _ & HSTR & _).
  rewrite Forall_forall in HSTR.
  assert (Hin : In (0x20d20, ManifestModel.prefix_lc) FM_RO_STRS).
  { unfold FM_RO_STRS. cbn [In]. right; right; left. reflexivity. }
  destruct (HSTR _ Hin) as [HCW _].
  cbn [fst snd] in HCW.
  destruct HCW as ((HGa & _) & _ & _ & _ & _ & HRA & _).
  change (Z.of_nat (length ManifestModel.prefix_lc)) with 6 in HRA.
  split.
  - destruct (HRA 0x20d26 ltac:(lia)) as (s & Hs & Hok).
    change (shadow_of_addr SHADOW_OFF 0x20d26) with (SHADOW_OFF + HD_WSH) in Hs.
    exists s. split; [exact (hw_val1_of_aview _ _ _ _ Hs)|].
    unfold saddr_ok in Hok. change (0x20d26 mod 8) with 6 in Hok. lia.
  - intros k Hk.
    assert (Hl : length ManifestModel.prefix_lc = 6%nat) by reflexivity.
    destruct (HGa (Z.to_nat k) ltac:(rewrite length_app, Hl; cbn [length]; lia)) as [Hv _].
    rewrite app_nth1 in Hv by lia.
    rewrite Z2Nat.id in Hv by lia. exact Hv.
Qed.

Definition hw_goal (k : nat) : Prop := forall cx i d f ly3 S3 W3 regs1 mem1 md1,
  ex_seg_L_from B cx i -> ex_seg_P B ->
  ex_at_L B cx i d f ly3 S3 W3 regs1 mem1 md1 ->
  getr regs1 20 = w64 (cx_t cx + Z.of_nat i) -> getr regs1 12 = w64 (Z.of_nat k) ->
  (i < length (cx_tb cx))%nat -> (i + k <= length (cx_tb cx))%nat ->
  hd_arm1 (cx_tb cx) i = false ->
  ManifestModel.ci_eqb (firstn k (skipn i (cx_tb cx))) (firstn k ManifestModel.prefix_lc) = true ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_W regs1 mem1 md1) (ex_post B cx).

Lemma hw_iter : forall k, (k < 6)%nat -> ((k < 5)%nat -> hw_goal (S k)) -> hw_goal k.
Proof.
  intros k Hk6 IH. unfold hw_goal in IH |- *.
  intros cx i d f ly3 S3 W3 regs1 mem1 md1 HLF HSP HAT R20 R12 Hi Hik Harm Hci.
  pose proof LAWS as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  destruct (hw_word_facts cx i d f ly3 S3 W3 regs1 mem1 md1 HAT) as ((s & Vs & Hs) & VW).
  pose proof HAT as (HB & HC & _ & HSR & HSC & R19 & _ & _ & _).
  pose proof HC as (HJ & _ & _ & _ & _ & _ & R25 & _ & _ & HCt & _).
  pose proof HSR as (_ & R22 & R18 & R8).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Htb).
  assert (Hib : Z.of_nat i < 2 ^ 32) by (unfold MANIFEST_MAX in Htb; lia).
  pose proof HCt as ((HGa & _) & _).
  destruct (HGa (i + k)%nat ltac:(rewrite length_app; cbn [length]; lia)) as [_ Hcr].
  clear HGa HCt HC HB HSR.
  destruct (hd_W_entry B cx i d f k s ly3 S3 W3 regs1 mem1 md1 HAT R20 R12 Hk6 Hik Vs ltac:(lia)) as [HS SHOK].
  set (c := nth (i + k) (cx_tb cx ++ [0]) 0) in *.
  assert (Hceq : c = nth (i + k) (cx_tb cx ++ [0]) 0) by reflexivity.
  clearbody c.
  remember (Ereg regs1 [Z_to_bv 64 c]) as E eqn:HE.
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs1 q)
    by (intros n q Hn; rewrite HE; apply ew_Ereg_nat; exact Hn).
  assert (E32 : ew E 32 = Z_to_bv 64 c) by (rewrite HE; exact (ew_Ereg_extra regs1 _ 0)).
  clear HE.
  assert (E19 : ew E 19 = w64 (Z.of_nat i)) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
  assert (E20 : ew E 20 = w64 (cx_t cx + Z.of_nat i)) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
  assert (E25 : ew E 25 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
  assert (AV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem1 a = aview tfibsegs (w_H W3) mem1 a)
    by reflexivity.
  change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 EX_W) mem1 (seg_rom tfibsegs))) in HJ, SHOK.
  unfold cfg_at. change (w64 EX_W) with (Z_to_bv 64 EX_W).
  (* s = 0 / 7, k = 0..5: twelve concrete walks (hw_case) *)
  destruct Hs as [-> | ->]; (destruct k as [|[|[|[|[|[|k]]]]]]; [..| exfalso; lia]).
  all: solve [hw_case HS HJ SHOK].
Qed.

Lemma hw_all : forall n k, (k < 6)%nat -> (6 - k = n)%nat -> hw_goal k.
Proof.
  induction n as [|n IHn]; intros k Hk Hn; [lia|].
  apply (hw_iter k Hk). intros Hk5. apply (IHn (S k)); lia.
Qed.

Lemma hd_W : forall k cx i d f ly3 S3 W3 regs1 mem1 md1,
  ex_seg_L_from B cx i -> ex_seg_P B ->
  ex_at_L B cx i d f ly3 S3 W3 regs1 mem1 md1 ->
  getr regs1 20 = w64 (cx_t cx + Z.of_nat i) -> getr regs1 12 = w64 (Z.of_nat k) ->
  (k < 6)%nat -> (i < length (cx_tb cx))%nat -> (i + k <= length (cx_tb cx))%nat ->
  hd_arm1 (cx_tb cx) i = false ->
  ManifestModel.ci_eqb (firstn k (skipn i (cx_tb cx))) (firstn k ManifestModel.prefix_lc) = true ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_W regs1 mem1 md1) (ex_post B cx).
Proof.
  intros k cx i d f ly3 S3 W3 regs1 mem1 md1 HLF HSP HAT R20 R12 Hk Hi Hik Harm Hci.
  exact (hw_all (6 - k) k Hk eq_refl cx i d f ly3 S3 W3 regs1 mem1 md1 HLF HSP HAT R20 R12 Hi Hik Harm Hci).
Qed.

End s.

Print Assumptions hd_W.
