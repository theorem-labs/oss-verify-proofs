(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk MemSplit SeqExec FPSteps FPStepsV.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefPrintfLib.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptStructs GrayLib LibAtomic LeptExec.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fr_denot (E : env) (L : list (reg * expr)) (fr : bvmap 5 word) : bvmap 5 word :=
  fold_right (fun kv f => bvmap_set (fst kv) (edenot E (snd kv)) f) fr L.
Fixpoint fr_find (L : list (reg * expr)) (k : nat) : option expr :=
  match L with [] => None | (r, e) :: t => if Nat.eqb (ridx r) k then Some e else fr_find t k end.

Lemma fr_get : forall E L fr (r : reg),
  reg_get (fr_denot E L fr) r = match fr_find L (ridx r) with Some e => edenot E e | None => reg_get fr r end.
Proof.
  intros E L fr r. induction L as [|[r' e] t IH]; [reflexivity|]. cbn [fr_denot fold_right fr_find fst snd].
  destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hk.
  - apply Nat.eqb_eq in Hk. apply ridx_inj in Hk. subst r'. apply fpv_get_same.
  - rewrite fpv_get_other; [exact IH|]. intros ->. rewrite Nat.eqb_refl in Hk. discriminate Hk.
Qed.
Lemma fr_set : forall E L fr (r : reg) (e : expr) (v : word), v = edenot E e -> bvmap_set r v (fr_denot E L fr) = fr_denot E ((r, e) :: L) fr.
Proof. intros E L fr r e v ->. reflexivity. Qed.

(* [comment removed for export] *)
Definition fpv_rdw (fmt : ffmt) (w : word) : Z := match fmt with FMT_S => bv_unsigned (unbox_s w) | FMT_D => bv_unsigned w end.
Lemma fr_read : forall E L fr fmt (r : reg) (w : word),
  reg_get (fr_denot E L fr) r = w -> fpv_read (fr_denot E L fr) fmt r = fpv_rdw fmt w.
Proof. intros E L fr fmt r w H. unfold fpv_read, fpv_rdw. rewrite H. reflexivity. Qed.

Lemma fr_get_lit : forall E L fr (r : reg) (z : Z), fr_find L (ridx r) = Some (ELit z) -> reg_get (fr_denot E L fr) r = Z_to_bv 64 z.
Proof. intros E L fr r z H. rewrite fr_get, H. reflexivity. Qed.
Lemma fr_get_expr : forall E L fr (r : reg) (e : expr), fr_find L (ridx r) = Some e -> reg_get (fr_denot E L fr) r = edenot E e.
Proof. intros E L fr r e H. rewrite fr_get, H. reflexivity. Qed.
(* [comment removed for export] *)
Lemma fr_get_unknown : forall E L fr (r r' : reg) (i : nat),
  fr_find L (ridx r) = None -> ev E i = Z_to_bv 64 (bv_unsigned (reg_get fr r')) -> ridx r' = ridx r -> reg_get (fr_denot E L fr) r = edenot E (EVar i).
Proof.
  intros E L fr r r' i H Hv Hr. rewrite fr_get, H. cbn [edenot]. rewrite Hv, zbv_self. apply ridx_inj in Hr. subst r'. reflexivity.
Qed.

(* [comment removed for export] *)
Definition fr_vars_lt (b : nat) (L : list (reg * expr)) : bool := forallb (fun kv => expr_vars_lt b (snd kv)) L.
Lemma fr_denot_agree : forall b E E' L fr, env_agree b E E' -> fr_vars_lt b L = true -> fr_denot E L fr = fr_denot E' L fr.
Proof.
  intros b E E' L fr Ha. induction L as [|[r e] t IH]; intros H; [reflexivity|]. cbn [fr_vars_lt forallb snd] in H. apply andb_true_iff in H as [H1 H2].
  cbn [fr_denot fold_right fst snd]. rewrite (edenot_agree b E E' e Ha H1). f_equal. apply IH. exact H2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma exf_extract64 : forall w : word, bv_extract 0 64 w = w.
Proof.
  intros w. apply bv_eq. rewrite bv_extract_unsigned. change (Z.of_N 0) with 0%Z. rewrite Z.shiftr_0_r.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.
Lemma exf_store4 : forall w : word, Z_to_le_bytes 4 (bv_unsigned (low32 w)) = word_to_le_bytes 4 w.
Proof.
  intros w. unfold low32, word_to_le_bytes. rewrite bv_extract_unsigned. change (Z.of_N 0) with 0%Z. rewrite Z.shiftr_0_r.
  apply Z_to_le_bytes_wrap. cbn. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Bridges.
Variable segs : list Segment.
(* [comment removed for export] *)
#[local] Instance exf_fxd : FPState := mkFP bvmap_empty (Z_to_bv 32 0).

Lemma exf_snoc : forall (fx fx' : FPState) rom R R' pc (M M' : word -> option byte) ms0,
  msteps segs ms0 (@mkst fx R (Z_to_bv 64 pc) M rom) ->
  RiscvSemantics.step segs (@mkst fx R (Z_to_bv 64 pc) M rom) = MachineOk (@mkst fx' R' (v_addi (Z_to_bv 64 pc) 4) M' rom) ->
  msteps segs ms0 (@mkst fx' R' (Z_to_bv 64 (pc + 4)) M' rom).
Proof.
  intros fx fx' rom R R' pc M M' ms0 Hms Hst. eapply (ex_msteps_snoc segs); [exact Hms | reflexivity |].
  rewrite Hst, zbv_addi. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma exf_storeok_sound : forall E base kn a (n : nat),
  know_ok segs E base kn -> (1 <= n)%nat -> (n <= 8)%nat ->
  scs_denot segs base E (flat_sc kn a n ++ storeok_sc kn a n) ->
  flat E a (Z.of_nat n) /\ RiscvSemantics.store_ok segs base (adenot E a) n = true.
Proof.
  intros E base kn a n Hkn Hn1 Hn8 Hsc.
  apply (flat_sc_sound segs E base _ _ _ _ Hkn Hn1 Hn8) in Hsc as [Hfl Hsc]. split; [exact Hfl|].
  unfold storeok_sc in Hsc. destruct (wr_covered kn a n) eqn:Hw.
  - clear Hsc. revert Hw. induction kn as [|K rest IH]; intros Hw; cbn [wr_covered] in Hw; [discriminate|].
    apply Forall_cons_iff in Hkn as [HK Hrest].
    destruct K as [| | | | | |[kb kk] len|]; try (apply IH; assumption).
    destruct (expr_eqb (a_base a) kb && Z.leb kk (a_off a) && Z.leb (a_off a + Z.of_nat n) (kk + len))%bool eqn:Hc; [|apply IH; assumption].
    apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
    apply expr_eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
    cbn [kentry_ok] in HK. destruct HK as [Hfk Hs0].
    replace (adenot E a) with (Z_to_bv 64 (estart E (SA kb kk) + (a_off a - kk))).
    + apply Hs0; lia.
    + apply bv_eq. rewrite (flat_u E _ _ Hfl). unfold estart. cbn [a_base a_off]. rewrite <- H1.
      destruct Hfl as (?&?&?&?). unfold estart in *. rewrite u_small by lia. lia.
  - apply scs_denot_cons in Hsc as [Hok _]. cbn [sc_denot] in Hok. exact Hok.
Qed.

(* [comment removed for export] *)
Lemma exf_fstore : forall E L fr cs m rom R pc sr log kn ms0 w fmt rs1 rs2 (imm : bv 12) (e : expr),
  msteps segs ms0 (@mkst (mkFP (fr_denot E L fr) cs) R (Z_to_bv 64 pc) (mem_denot E m log) rom) ->
  regs_ok E sr R -> log_flat E log -> know_ok segs E m kn ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (FStore fmt rs1 rs2 imm, 4%Z) ->
  reg_get (fr_denot E L fr) rs2 = edenot E e ->
  forall (n : nat) (a : saddr) (scs0 : list sidecond),
  n = match fmt with FMT_S => 4%nat | FMT_D => 8%nat end -> to_saddrK kn (sr_get sr rs1) (bv_signed imm) = a ->
  flat_sc kn a n ++ storeok_sc kn a n = scs0 -> scs_denot segs m E scs0 ->
  msteps segs ms0 (@mkst (mkFP (fr_denot E L fr) cs) R (Z_to_bv 64 (pc + 4)) (mem_denot E m (SE a n e :: log)) rom)
  /\ log_flat E (SE a n e :: log).
Proof.
  intros E L fr cs m rom R pc sr log kn ms0 w fmt rs1 rs2 imm e Hms HR Hlf HK Hf He Hd Hv n a scs0 En Ea Es Hsc. subst scs0.
  assert (Hn : (1 <= n)%nat /\ (n <= 8)%nat) by (subst n; destruct fmt; lia). destruct Hn as [Hn1 Hn8].
  destruct (exf_storeok_sound E m kn a n HK Hn1 Hn8 Hsc) as [Hfl Hok].
  assert (Hadr : v_addi (getr R rs1) (bv_signed imm) = adenot E a).
  { rewrite <- Ea. rewrite (to_saddrK_denot segs E m _ _ _ HK), (reg_val _ _ _ rs1 HR). reflexivity. }
  split; [| cbn [log_flat]; split; [exact Hn8 | split; [exact Hfl | exact Hlf]]].
  assert (Hok' : RiscvSemantics.store_ok segs (mem_denot E m log) (adenot E a) n = true) by (eapply store_ok_mono; [apply mem_denot_grows | exact Hok]).
  apply (exf_snoc _ _ rom R R pc (mem_denot E m log) _ ms0 Hms). cbn [mem_denot].
  subst n. destruct fmt.
  - rewrite (fp_step_fsw (mkFP (fr_denot E L fr) cs) segs R (Z_to_bv 64 pc) (mem_denot E m log) rom w rs1 rs2 imm (adenot E a) Hf He Hd Hadr Hok').
    cbn [fp_regs]. rewrite Hv, exf_store4. reflexivity.
  - rewrite (fp_step_fsd (mkFP (fr_denot E L fr) cs) segs R (Z_to_bv 64 pc) (mem_denot E m log) rom w rs1 rs2 imm (adenot E a) Hf He Hd Hadr Hok').
    cbn [fp_regs]. rewrite Hv. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma exf_fld : forall E L fr cs m rom R pc sr log kn ms0 w rd rs (imm : bv 12) (v : expr) scs,
  msteps segs ms0 (@mkst (mkFP (fr_denot E L fr) cs) R (Z_to_bv 64 pc) (mem_denot E m log) rom) ->
  regs_ok E sr R -> log_flat E log -> know_ok segs E m kn ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (FLoad FMT_D rd rs imm, 4%Z) ->
  forall (rb : expr) (rk : Z) (scs0 : list sidecond),
  to_saddrK kn (sr_get sr rs) (bv_signed imm) = SA rb rk ->
  ex_lookup segs kn log rb rk 8 = Some (v, scs) ->
  flat_sc kn (SA rb rk) 8 ++ scs = scs0 -> scs_denot segs m E scs0 ->
  msteps segs ms0 (@mkst (mkFP (fr_denot E ((rd, v) :: L) fr) cs) R (Z_to_bv 64 (pc + 4)) (mem_denot E m log) rom).
Proof.
  intros E L fr cs m rom R pc sr log kn ms0 w rd rs imm v scs Hms HR Hlf HK Hf He Hd rb rk scs0 Ea Hlk Es Hsc. subst scs0.
  apply (flat_sc_sound segs E m kn (SA rb rk) 8%nat scs HK ltac:(lia) ltac:(lia)) in Hsc as [Hfl Hsc].
  destruct (ex_lookup_sound segs E m kn log rb rk 8 v scs HK Hlf ltac:(lia) ltac:(lia) Hlk Hsc Hfl) as (bs & Hrd & Hlen & Hval).
  assert (Hadr : v_addi (getr R rs) (bv_signed imm) = adenot E (SA rb rk)).
  { rewrite <- Ea. rewrite (to_saddrK_denot segs E m _ _ _ HK), (reg_val _ _ _ rs HR). reflexivity. }
  apply (exf_snoc _ _ rom R R pc (mem_denot E m log) _ ms0 Hms).
  rewrite (fp_step_fld (mkFP (fr_denot E L fr) cs) segs R (Z_to_bv 64 pc) (mem_denot E m log) rom w rd rs imm (adenot E (SA rb rk)) bs Hf He Hd Hadr Hrd).
  cbn [fp_regs fp_csr]. rewrite (fr_set E L fr rd v); [reflexivity|].
  rewrite exf_extract64. unfold le_bytes_to_word. exact Hval.
Qed.

(* [comment removed for export] *)
Lemma exf_flw : forall E L fr cs m rom R pc sr log kn ms0 w rd rs (imm : bv 12) (v : expr) scs (zr : Z),
  msteps segs ms0 (@mkst (mkFP (fr_denot E L fr) cs) R (Z_to_bv 64 pc) (mem_denot E m log) rom) ->
  regs_ok E sr R -> log_flat E log -> know_ok segs E m kn ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (FLoad FMT_S rd rs imm, 4%Z) ->
  forall (rb : expr) (rk : Z) (scs0 : list sidecond),
  to_saddrK kn (sr_get sr rs) (bv_signed imm) = SA rb rk ->
  ex_lookup segs kn log rb rk 4 = Some (v, scs) ->
  flat_sc kn (SA rb rk) 4 ++ scs = scs0 -> scs_denot segs m E scs0 ->
  nan_box (bv_extract 0 32 (edenot E v)) = Z_to_bv 64 zr ->
  msteps segs ms0 (@mkst (mkFP (fr_denot E ((rd, ELit zr) :: L) fr) cs) R (Z_to_bv 64 (pc + 4)) (mem_denot E m log) rom).
Proof.
  intros E L fr cs m rom R pc sr log kn ms0 w rd rs imm v scs zr Hms HR Hlf HK Hf He Hd rb rk scs0 Ea Hlk Es Hsc Hz. subst scs0.
  apply (flat_sc_sound segs E m kn (SA rb rk) 4%nat scs HK ltac:(lia) ltac:(lia)) in Hsc as [Hfl Hsc].
  destruct (ex_lookup_sound segs E m kn log rb rk 4 v scs HK Hlf ltac:(lia) ltac:(lia) Hlk Hsc Hfl) as (bs & Hrd & Hlen & Hval).
  assert (Hadr : v_addi (getr R rs) (bv_signed imm) = adenot E (SA rb rk)).
  { rewrite <- Ea. rewrite (to_saddrK_denot segs E m _ _ _ HK), (reg_val _ _ _ rs HR). reflexivity. }
  apply (exf_snoc _ _ rom R R pc (mem_denot E m log) _ ms0 Hms).
  rewrite (fp_step_flw (mkFP (fr_denot E L fr) cs) segs R (Z_to_bv 64 pc) (mem_denot E m log) rom w rd rs imm (adenot E (SA rb rk)) bs Hf He Hd Hadr Hrd).
  cbn [fp_regs fp_csr]. rewrite (fr_set E L fr rd (ELit zr)); [reflexivity|].
  unfold le_bytes_to_word. rewrite Hval. exact Hz.
Qed.

(* [comment removed for export] *)
Lemma exf_fmv_d_x : forall E L fr cs rom R pc sr (M : word -> option byte) ms0 w rd rs1,
  msteps segs ms0 (@mkst (mkFP (fr_denot E L fr) cs) R (Z_to_bv 64 pc) M rom) -> regs_ok E sr R ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (Fmv FMV_F_X FMT_D rd rs1, 4%Z) ->
  msteps segs ms0 (@mkst (mkFP (fr_denot E ((rd, sr_get sr rs1) :: L) fr) cs) R (Z_to_bv 64 (pc + 4)) M rom).
Proof.
  intros E L fr cs rom R pc sr M ms0 w rd rs1 Hms HR Hf He Hd. apply (exf_snoc _ _ rom R R pc M _ ms0 Hms).
  rewrite (fp_step_fmv_d_x (mkFP (fr_denot E L fr) cs) segs R (Z_to_bv 64 pc) M rom w rd rs1 Hf He Hd). cbn [fp_regs fp_csr].
  rewrite (fr_set E L fr rd (sr_get sr rs1)); [reflexivity | apply (reg_val _ _ _ rs1 HR)].
Qed.
Lemma exf_fmv_w_x : forall E L fr cs rom R pc sr (M : word -> option byte) ms0 w rd rs1 (zr : Z),
  msteps segs ms0 (@mkst (mkFP (fr_denot E L fr) cs) R (Z_to_bv 64 pc) M rom) -> regs_ok E sr R ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (Fmv FMV_F_X FMT_S rd rs1, 4%Z) ->
  nan_box (low32 (edenot E (sr_get sr rs1))) = Z_to_bv 64 zr ->
  msteps segs ms0 (@mkst (mkFP (fr_denot E ((rd, ELit zr) :: L) fr) cs) R (Z_to_bv 64 (pc + 4)) M rom).
Proof.
  intros E L fr cs rom R pc sr M ms0 w rd rs1 zr Hms HR Hf He Hd Hz. apply (exf_snoc _ _ rom R R pc M _ ms0 Hms).
  rewrite (fp_step_fmv_w_x (mkFP (fr_denot E L fr) cs) segs R (Z_to_bv 64 pc) M rom w rd rs1 Hf He Hd). cbn [fp_regs fp_csr].
  rewrite (fr_set E L fr rd (ELit zr)); [reflexivity | rewrite (reg_val _ _ _ rs1 HR); exact Hz].
Qed.

(* [comment removed for export] *)
Lemma exf_fsgnj : forall E L fr cs rom R pc (M : word -> option byte) ms0 w op fmt rd rs1 rs2 (w1 w2 : word) (zr : Z),
  msteps segs ms0 (@mkst (mkFP (fr_denot E L fr) cs) R (Z_to_bv 64 pc) M rom) ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (Fsgnj op fmt rd rs1 rs2, 4%Z) ->
  reg_get (fr_denot E L fr) rs1 = w1 -> reg_get (fr_denot E L fr) rs2 = w2 -> fpv_sgnj op fmt w1 w2 = Z_to_bv 64 zr ->
  msteps segs ms0 (@mkst (mkFP (fr_denot E ((rd, ELit zr) :: L) fr) cs) R (Z_to_bv 64 (pc + 4)) M rom).
Proof.
  intros E L fr cs rom R pc M ms0 w op fmt rd rs1 rs2 w1 w2 zr Hms Hf He Hd H1 H2 Hz. apply (exf_snoc _ _ rom R R pc M _ ms0 Hms).
  rewrite (fpv_step_fsgnj (mkFP (fr_denot E L fr) cs) segs R (Z_to_bv 64 pc) M rom w op fmt rd rs1 rs2 Hf He Hd). cbn [fp_regs fp_csr].
  rewrite H1, H2. rewrite (fr_set E L fr rd (ELit zr)); [reflexivity | exact Hz].
Qed.

(* [comment removed for export] *)
Lemma exf_fcvt_ff : forall E L fr cs rom R pc (M : word -> option byte) ms0 w dst src rd rs1 (rm : bv 3) md df sf (w1 : word) (res zr : Z) (fl : fflags),
  msteps segs ms0 (@mkst (mkFP (fr_denot E L fr) cs) R (Z_to_bv 64 pc) M rom) ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (Fcvt dst src rd rs1 rm, 4%Z) ->
  (dst = FC_S /\ df = FMT_S \/ dst = FC_D /\ df = FMT_D) -> (src = FC_S /\ sf = FMT_S \/ src = FC_D /\ sf = FMT_D) ->
  frm_zero cs -> rmode_of_field (bv_unsigned rm) 0 = Some md ->
  reg_get (fr_denot E L fr) rs1 = w1 ->
  fp_convert (fp_format sf) (fp_format df) md (fpv_rdw sf w1) = (res, fl) -> fpv_box df res = Z_to_bv 64 zr ->
  msteps segs ms0 (@mkst (mkFP (fr_denot E ((rd, ELit zr) :: L) fr) (fpv_acc cs fl)) R (Z_to_bv 64 (pc + 4)) M rom).
Proof.
  intros E L fr cs rom R pc M ms0 w dst src rd rs1 rm md df sf w1 res zr fl Hms Hf He Hd Hdst Hsrc FZ Hmd Hr Hc Hb.
  apply (exf_snoc _ _ rom R R pc M _ ms0 Hms).
  rewrite (fpv_step_fcvt_f_of_f (mkFP (fr_denot E L fr) cs) segs R (Z_to_bv 64 pc) M rom w dst src rd rs1 rm md df sf Hf He Hd Hdst Hsrc FZ Hmd). cbn [fp_regs fp_csr].
  rewrite (fr_read E L fr sf rs1 w1 Hr), Hc. cbn [fst snd]. rewrite (fr_set E L fr rd (ELit zr)); [reflexivity | exact Hb].
Qed.

(* [comment removed for export] *)
Lemma exf_fcmp : forall E L fr cs rom R pc sr (M : word -> option byte) ms0 w op fmt rd rs1 rs2 (w1 w2 : word) (b : bool) (fl : fflags),
  msteps segs ms0 (@mkst (mkFP (fr_denot E L fr) cs) R (Z_to_bv 64 pc) M rom) -> regs_ok E sr R ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (Fcmp op fmt rd rs1 rs2, 4%Z) ->
  reg_get (fr_denot E L fr) rs1 = w1 -> reg_get (fr_denot E L fr) rs2 = w2 ->
  fpv_cmp op fmt (fpv_rdw fmt w1) (fpv_rdw fmt w2) = (b, fl) ->
  exists R', regs_ok E (if bv_eqb rd 0 then sr else sr_upd sr (ridx rd) (ELit (if b then 1 else 0))) R'
    /\ msteps segs ms0 (@mkst (mkFP (fr_denot E L fr) (fpv_acc cs fl)) R' (Z_to_bv 64 (pc + 4)) M rom).
Proof.
  intros E L fr cs rom R pc sr M ms0 w op fmt rd rs1 rs2 w1 w2 b fl Hms HR Hf He Hd H1 H2 Hc.
  eexists. split; [| apply (exf_snoc _ _ rom R _ pc M _ ms0 Hms);
    rewrite (fpv_step_fcmp (mkFP (fr_denot E L fr) cs) segs R (Z_to_bv 64 pc) M rom w op fmt rd rs1 rs2 Hf He Hd); cbn [fp_regs fp_csr];
    rewrite (fr_read E L fr fmt rs1 w1 H1), (fr_read E L fr fmt rs2 w2 H2), Hc; cbn [fst snd]; reflexivity].
  apply regs_ok_upd; [exact HR|]. destruct b; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma exf_fma : forall E L fr cs rom R pc (M : word -> option byte) ms0 w op fmt rd rs1 rs2 rs3 (rm : bv 3) md (w1 w2 w3 : word) (res zr : Z) (fl : fflags),
  msteps segs ms0 (@mkst (mkFP (fr_denot E L fr) cs) R (Z_to_bv 64 pc) M rom) ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (Fma op fmt rd rs1 rs2 rs3 rm, 4%Z) ->
  frm_zero cs -> rmode_of_field (bv_unsigned rm) 0 = Some md ->
  reg_get (fr_denot E L fr) rs1 = w1 -> reg_get (fr_denot E L fr) rs2 = w2 -> reg_get (fr_denot E L fr) rs3 = w3 ->
  fpv_fma op fmt md (fpv_rdw fmt w1) (fpv_rdw fmt w2) (fpv_rdw fmt w3) = (res, fl) -> fpv_box fmt res = Z_to_bv 64 zr ->
  msteps segs ms0 (@mkst (mkFP (fr_denot E ((rd, ELit zr) :: L) fr) (fpv_acc cs fl)) R (Z_to_bv 64 (pc + 4)) M rom).
Proof.
  intros E L fr cs rom R pc M ms0 w op fmt rd rs1 rs2 rs3 rm md w1 w2 w3 res zr fl Hms Hf He Hd FZ Hmd H1 H2 H3 Hc Hb.
  apply (exf_snoc _ _ rom R R pc M _ ms0 Hms).
  rewrite (fpv_step_fma (mkFP (fr_denot E L fr) cs) segs R (Z_to_bv 64 pc) M rom w op fmt rd rs1 rs2 rs3 rm md Hf He Hd FZ Hmd). cbn [fp_regs fp_csr].
  rewrite (fr_read E L fr fmt rs1 w1 H1), (fr_read E L fr fmt rs2 w2 H2), (fr_read E L fr fmt rs3 w3 H3), Hc. cbn [fst snd].
  rewrite (fr_set E L fr rd (ELit zr)); [reflexivity | exact Hb].
Qed.

(* [comment removed for export] *)
Lemma exf_fari : forall E L fr cs rom R pc (M : word -> option byte) ms0 w op fmt rd rs1 rs2 (rm : bv 3) md (w1 w2 : word) (res zr : Z) (fl : fflags),
  msteps segs ms0 (@mkst (mkFP (fr_denot E L fr) cs) R (Z_to_bv 64 pc) M rom) ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (Fari op fmt rd rs1 rs2 rm, 4%Z) ->
  frm_zero cs -> rmode_of_field (bv_unsigned rm) 0 = Some md ->
  reg_get (fr_denot E L fr) rs1 = w1 -> reg_get (fr_denot E L fr) rs2 = w2 ->
  fpv_ari op fmt md (fpv_rdw fmt w1) (fpv_rdw fmt w2) = (res, fl) -> fpv_box fmt res = Z_to_bv 64 zr ->
  msteps segs ms0 (@mkst (mkFP (fr_denot E ((rd, ELit zr) :: L) fr) (fpv_acc cs fl)) R (Z_to_bv 64 (pc + 4)) M rom).
Proof.
  intros E L fr cs rom R pc M ms0 w op fmt rd rs1 rs2 rm md w1 w2 res zr fl Hms Hf He Hd FZ Hmd H1 H2 Hc Hb.
  apply (exf_snoc _ _ rom R R pc M _ ms0 Hms).
  rewrite (fpv_step_fari (mkFP (fr_denot E L fr) cs) segs R (Z_to_bv 64 pc) M rom w op fmt rd rs1 rs2 rm md Hf He Hd FZ Hmd). cbn [fp_regs fp_csr].
  rewrite (fr_read E L fr fmt rs1 w1 H1), (fr_read E L fr fmt rs2 w2 H2), Hc. cbn [fst snd].
  rewrite (fr_set E L fr rd (ELit zr)); [reflexivity | exact Hb].
Qed.

(* [comment removed for export] *)
Lemma exf_fcvt_xf : forall E L fr cs rom R pc sr (M : word -> option byte) ms0 w dst src rd rs1 (rm : bv 3) md sf sgn bits (w1 : word) (zr : Z) (fl : fflags),
  msteps segs ms0 (@mkst (mkFP (fr_denot E L fr) cs) R (Z_to_bv 64 pc) M rom) -> regs_ok E sr R ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (Fcvt dst src rd rs1 rm, 4%Z) ->
  (dst = FC_W /\ sgn = true /\ bits = 32%Z \/ dst = FC_WU /\ sgn = false /\ bits = 32%Z \/
   dst = FC_L /\ sgn = true /\ bits = 64%Z \/ dst = FC_LU /\ sgn = false /\ bits = 64%Z) ->
  (src = FC_S /\ sf = FMT_S \/ src = FC_D /\ sf = FMT_D) ->
  frm_zero cs -> rmode_of_field (bv_unsigned rm) 0 = Some md ->
  reg_get (fr_denot E L fr) rs1 = w1 ->
  fpv_x_of_f sf md sgn bits (fpv_rdw sf w1) = Z_to_bv 64 zr -> snd (fp_to_int (fp_format sf) md sgn bits (fpv_rdw sf w1)) = fl ->
  exists R', regs_ok E (if bv_eqb rd 0 then sr else sr_upd sr (ridx rd) (ELit zr)) R'
    /\ msteps segs ms0 (@mkst (mkFP (fr_denot E L fr) (fpv_acc cs fl)) R' (Z_to_bv 64 (pc + 4)) M rom).
Proof.
  intros E L fr cs rom R pc sr M ms0 w dst src rd rs1 rm md sf sgn bits w1 zr fl Hms HR Hf He Hd Hdst Hsrc FZ Hmd H1 Hv Hfl.
  eexists. split; [| apply (exf_snoc _ _ rom R _ pc M _ ms0 Hms);
    rewrite (fpv_step_fcvt_x_of_f (mkFP (fr_denot E L fr) cs) segs R (Z_to_bv 64 pc) M rom w dst src rd rs1 rm md sf sgn bits Hf He Hd Hdst Hsrc FZ Hmd); cbn [fp_regs fp_csr];
    rewrite (fr_read E L fr sf rs1 w1 H1), Hfl, Hv; reflexivity].
  apply regs_ok_upd; [exact HR | reflexivity].
Qed.
End Bridges.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac exf_default1 fdef k :=
  lazymatch fdef with
  | (?k', ?i) :: ?t => lazymatch k' with k => constr:(i) | _ => exf_default1 t k end
  | _ => fail 100 "exf: no default variable for FP register" k
  end.
Ltac exf_default fdef k := let l := eval vm_compute in fdef in exf_default1 l k.
(* [comment removed for export] *)
Ltac exf_closed E L fr r G cont :=
  let o := eval vm_compute in (fr_find L (ridx r)) in
  lazymatch o with
  | Some (ELit ?z) =>
      assert (G : reg_get (fr_denot E L fr) r = Z_to_bv 64 z) by (apply fr_get_lit; vm_cast_no_check (eq_refl (Some (ELit z))));
      cont z
  | _ => fail 100 "exf: FP register" r "does not hold a closed value:" o
  end.
(* [comment removed for export] *)
Ltac exf_scs r0 := first [ exact I | (split_scs; ex_sc r0) ].
(* [comment removed for export] *)
Ltac exf_reabs Hms FZ :=
  lazymatch type of Hms with
  | msteps _ _ (@mkst (mkFP _ (fpv_acc ?cs ?fl)) _ _ _ _) =>
      let FZ' := fresh "FZ" in let cs' := fresh "cs" in
      pose proof (fpv_frm_acc cs fl FZ) as FZ';
      set (cs' := fpv_acc cs fl) in Hms, FZ'; clearbody cs'; clear FZ; rename FZ' into FZ
  end.

Ltac exf_disj := first [ (repeat split; reflexivity) | (left; exf_disj) | (right; exf_disj) ].

(* [comment removed for export] *)
Ltac exf_fcvt_ff_tac segs E L fr cs rom R pc M ms0 w dst src rd rs1 rm md df Hms F D FZ :=
  let sf := lazymatch src with FC_S => constr:(FMT_S) | FC_D => constr:(FMT_D) end in
  let G1 := fresh "G" in let Hms' := fresh "Hms" in
  exf_closed E L fr rs1 G1 ltac:(fun z1 =>
    let r := eval vm_compute in (fp_convert (fp_format sf) (fp_format df) md (fpv_rdw sf (Z_to_bv 64 z1))) in
    lazymatch r with
    | (?res, ?fl) =>
        let zr := eval vm_compute in (bv_unsigned (fpv_box df res)) in
        pose proof (exf_fcvt_ff segs E L fr cs rom R pc M ms0 w dst src rd rs1 rm md df sf (Z_to_bv 64 z1) res zr fl Hms F (eq_refl _) D
                      ltac:(exf_disj) ltac:(exf_disj) FZ ltac:(vm_cast_no_check (eq_refl (Some md))) G1
                      ltac:(vm_cast_no_check (eq_refl (res, fl))) ltac:(apply bv_eq; vm_cast_no_check (eq_refl zr))) as Hms';
        clear F D G1 Hms; rename Hms' into Hms; exf_reabs Hms FZ
    end).

(* [comment removed for export] *)
Ltac exf_fcvt_xf_tac segs E L fr cs rom R pc sr M ms0 w dst src rd rs1 rm md HR Hms F D FZ :=
  let sf := lazymatch src with FC_S => constr:(FMT_S) | FC_D => constr:(FMT_D) end in
  let sgn := lazymatch dst with FC_W => constr:(true) | FC_L => constr:(true) | FC_WU => constr:(false) | FC_LU => constr:(false) end in
  let bits := lazymatch dst with FC_W => constr:(32%Z) | FC_WU => constr:(32%Z) | FC_L => constr:(64%Z) | FC_LU => constr:(64%Z) end in
  let G1 := fresh "G" in let Hms' := fresh "Hms" in let R' := fresh "R" in let HR' := fresh "HR" in
  exf_closed E L fr rs1 G1 ltac:(fun z1 =>
    let zr := eval vm_compute in (bv_unsigned (fpv_x_of_f sf md sgn bits (fpv_rdw sf (Z_to_bv 64 z1)))) in
    let fl := eval vm_compute in (snd (fp_to_int (fp_format sf) md sgn bits (fpv_rdw sf (Z_to_bv 64 z1)))) in
    destruct (exf_fcvt_xf segs E L fr cs rom R pc sr M ms0 w dst src rd rs1 rm md sf sgn bits (Z_to_bv 64 z1) zr fl Hms HR F (eq_refl _) D
                ltac:(exf_disj) ltac:(exf_disj) FZ ltac:(vm_cast_no_check (eq_refl (Some md))) G1
                ltac:(apply bv_eq; vm_cast_no_check (eq_refl zr)) ltac:(vm_cast_no_check (eq_refl fl))) as (R' & HR' & Hms');
    clear F D G1 Hms; (let HRo := fresh "HRo" in rename HR into HRo); rename HR' into HR; rename Hms' into Hms;
    lazymatch type of HR with regs_ok _ ?sr' _ => let sr'' := eval vm_compute in sr' in change (regs_ok E sr'' R') in HR end;
    exf_reabs Hms FZ).

Ltac exf_step fdef HR Hlf HK Hms FZ :=
  lazymatch type of Hms with
  | msteps ?segs ?ms0 (@mkst (mkFP (fr_denot ?E ?L ?fr) ?cs) ?R (Z_to_bv 64 ?pc) ?M ?rom) =>
    lazymatch type of HR with
    | regs_ok _ ?sr _ =>
      lazymatch type of HK with
      | know_ok _ _ ?m ?kn =>
        let r0 := lazymatch E with ex_envL _ ?r0 _ => r0 end in
        let F := fresh "F" in let D := fresh "D" in let Hms' := fresh "Hms" in
        ex_fetch segs pc F D;
        lazymatch type of D with
        (* [comment removed for export] *)
        | decode_any ?w = Some (FStore ?fmt ?rs1 ?rs2 ?imm, _) =>
            lazymatch M with
            | mem_denot _ _ ?log =>
              let n := lazymatch fmt with FMT_S => constr:(4%nat) | FMT_D => constr:(8%nat) end in
              let a := eval vm_compute in (to_saddrK kn (sr_get sr rs1) (bv_signed imm)) in
              let scs0 := eval vm_compute in (flat_sc kn a n ++ storeok_sc kn a n) in
              let o := eval vm_compute in (fr_find L (ridx rs2)) in
              let Hlf' := fresh "Hlf" in let Hv := fresh "Hv" in
              lazymatch o with
              | Some ?e =>
                  assert (Hv : reg_get (fr_denot E L fr) rs2 = edenot E e) by (apply fr_get_expr; vm_cast_no_check (eq_refl (Some e)));
                  destruct (exf_fstore segs E L fr cs m rom R pc sr log kn ms0 w fmt rs1 rs2 imm e Hms HR Hlf HK F (eq_refl _) D Hv n a scs0
                              (eq_refl _) ltac:(vm_cast_no_check (eq_refl a)) ltac:(vm_cast_no_check (eq_refl scs0)) ltac:(exf_scs r0)) as [Hms' Hlf']
              | None =>
                  let k := eval vm_compute in (ridx rs2) in
                  let i := exf_default fdef k in
                  assert (Hv : reg_get (fr_denot E L fr) rs2 = edenot E (EVar i))
                    by (eapply fr_get_unknown; [vm_cast_no_check (eq_refl (@None expr)) | reflexivity | reflexivity]);
                  destruct (exf_fstore segs E L fr cs m rom R pc sr log kn ms0 w fmt rs1 rs2 imm (EVar i) Hms HR Hlf HK F (eq_refl _) D Hv n a scs0
                              (eq_refl _) ltac:(vm_cast_no_check (eq_refl a)) ltac:(vm_cast_no_check (eq_refl scs0)) ltac:(exf_scs r0)) as [Hms' Hlf']
              end;
              clear F D Hv Hms Hlf; rename Hms' into Hms; rename Hlf' into Hlf
            end
        (* [comment removed for export] *)
        | decode_any ?w = Some (FLoad FMT_D ?rd ?rs ?imm, _) =>
            lazymatch M with
            | mem_denot _ _ ?log =>
              let a := eval vm_compute in (to_saddrK kn (sr_get sr rs) (bv_signed imm)) in
              lazymatch a with
              | SA ?rb ?rk =>
                let lk := eval vm_compute in (ex_lookup segs kn log rb rk 8) in
                lazymatch lk with
                | Some (?v, ?scs) =>
                    let scs0 := eval vm_compute in (flat_sc kn a 8 ++ scs) in
                    pose proof (exf_fld segs E L fr cs m rom R pc sr log kn ms0 w rd rs imm v scs Hms HR Hlf HK F (eq_refl _) D rb rk scs0
                                  ltac:(vm_cast_no_check (eq_refl a)) ltac:(vm_cast_no_check (eq_refl lk)) ltac:(vm_cast_no_check (eq_refl scs0))
                                  ltac:(exf_scs r0)) as Hms';
                    clear F D Hms; rename Hms' into Hms
                | _ => fail 100 "exf: fld finds no value at" a
                end
              end
            end
        (* [comment removed for export] *)
        | decode_any ?w = Some (FLoad FMT_S ?rd ?rs ?imm, _) =>
            lazymatch M with
            | mem_denot _ _ ?log =>
              let a := eval vm_compute in (to_saddrK kn (sr_get sr rs) (bv_signed imm)) in
              lazymatch a with
              | SA ?rb ?rk =>
                let lk := eval vm_compute in (ex_lookup segs kn log rb rk 4) in
                lazymatch lk with
                | Some (ELit ?z, ?scs) =>
                    let scs0 := eval vm_compute in (flat_sc kn a 4 ++ scs) in
                    let zr := eval vm_compute in (bv_unsigned (nan_box (bv_extract 0 32 (Z_to_bv 64 z)))) in
                    pose proof (exf_flw segs E L fr cs m rom R pc sr log kn ms0 w rd rs imm (ELit z) scs zr Hms HR Hlf HK F (eq_refl _) D rb rk scs0
                                  ltac:(vm_cast_no_check (eq_refl a)) ltac:(vm_cast_no_check (eq_refl lk)) ltac:(vm_cast_no_check (eq_refl scs0))
                                  ltac:(exf_scs r0)
                                  ltac:(change (nan_box (bv_extract 0 32 (Z_to_bv 64 z)) = Z_to_bv 64 zr); apply bv_eq; vm_cast_no_check (eq_refl zr))) as Hms';
                    clear F D Hms; rename Hms' into Hms
                | _ => fail 100 "exf: flw needs a closed value at" a "found" lk
                end
              end
            end
        (* [comment removed for export] *)
        | decode_any ?w = Some (Fmv FMV_F_X FMT_D ?rd ?rs1, _) =>
            pose proof (exf_fmv_d_x segs E L fr cs rom R pc sr M ms0 w rd rs1 Hms HR F (eq_refl _) D) as Hms';
            lazymatch type of Hms' with
            | msteps _ _ (@mkst (mkFP (fr_denot _ ((_, ?e) :: _) _) _) _ _ _ _) =>
                let e' := eval vm_compute in e in
                change (msteps segs ms0 (@mkst (mkFP (fr_denot E ((rd, e') :: L) fr) cs) R (Z_to_bv 64 (pc + 4)) M rom)) in Hms'
            end;
            clear F D Hms; rename Hms' into Hms
        | decode_any ?w = Some (Fmv FMV_F_X FMT_S ?rd ?rs1, _) =>
            let e := eval vm_compute in (sr_get sr rs1) in
            lazymatch e with
            | ELit ?z =>
                let zr := eval vm_compute in (bv_unsigned (nan_box (low32 (Z_to_bv 64 z)))) in
                pose proof (exf_fmv_w_x segs E L fr cs rom R pc sr M ms0 w rd rs1 zr Hms HR F (eq_refl _) D
                              ltac:(change (nan_box (low32 (Z_to_bv 64 z)) = Z_to_bv 64 zr); apply bv_eq; vm_cast_no_check (eq_refl zr))) as Hms';
                clear F D Hms; rename Hms' into Hms
            | _ => fail 100 "exf: fmv.w.x of a non-literal register" e
            end
        (* [comment removed for export] *)
        | decode_any ?w = Some (Fcvt ?dst ?src ?rd ?rs1 ?rm, _) =>
            let mdo := eval vm_compute in (rmode_of_field (bv_unsigned rm) 0) in
            lazymatch mdo with
            | Some ?md =>
              lazymatch dst with
              | FC_S => exf_fcvt_ff_tac segs E L fr cs rom R pc M ms0 w dst src rd rs1 rm md FMT_S Hms F D FZ
              | FC_D => exf_fcvt_ff_tac segs E L fr cs rom R pc M ms0 w dst src rd rs1 rm md FMT_D Hms F D FZ
              | _ => exf_fcvt_xf_tac segs E L fr cs rom R pc sr M ms0 w dst src rd rs1 rm md HR Hms F D FZ
              end
            end
        (* [comment removed for export] *)
        | decode_any ?w = Some (Fcmp ?op ?fmt ?rd ?rs1 ?rs2, _) =>
            let G1 := fresh "G" in let G2 := fresh "G" in
            exf_closed E L fr rs1 G1 ltac:(fun z1 => exf_closed E L fr rs2 G2 ltac:(fun z2 =>
              let r := eval vm_compute in (fpv_cmp op fmt (fpv_rdw fmt (Z_to_bv 64 z1)) (fpv_rdw fmt (Z_to_bv 64 z2))) in
              lazymatch r with
              | (?b, ?fl) =>
                  let R' := fresh "R" in let HR' := fresh "HR" in
                  destruct (exf_fcmp segs E L fr cs rom R pc sr M ms0 w op fmt rd rs1 rs2 (Z_to_bv 64 z1) (Z_to_bv 64 z2) b fl Hms HR F (eq_refl _) D G1 G2
                              ltac:(vm_cast_no_check (eq_refl (b, fl)))) as (R' & HR' & Hms');
                  clear F D G1 G2 Hms; (let HRo := fresh "HRo" in rename HR into HRo); rename HR' into HR; rename Hms' into Hms;
                  lazymatch type of HR with regs_ok _ ?sr' _ => let sr'' := eval vm_compute in sr' in change (regs_ok E sr'' R') in HR end;
                  exf_reabs Hms FZ
              end))
        (* [comment removed for export] *)
        | decode_any ?w = Some (Fma ?op ?fmt ?rd ?rs1 ?rs2 ?rs3 ?rm, _) =>
            let mdo := eval vm_compute in (rmode_of_field (bv_unsigned rm) 0) in
            lazymatch mdo with
            | Some ?md =>
              let G1 := fresh "G" in let G2 := fresh "G" in let G3 := fresh "G" in
              exf_closed E L fr rs1 G1 ltac:(fun z1 => exf_closed E L fr rs2 G2 ltac:(fun z2 => exf_closed E L fr rs3 G3 ltac:(fun z3 =>
                let r := eval vm_compute in (fpv_fma op fmt md (fpv_rdw fmt (Z_to_bv 64 z1)) (fpv_rdw fmt (Z_to_bv 64 z2)) (fpv_rdw fmt (Z_to_bv 64 z3))) in
                lazymatch r with
                | (?res, ?fl) =>
                    let zr := eval vm_compute in (bv_unsigned (fpv_box fmt res)) in
                    pose proof (exf_fma segs E L fr cs rom R pc M ms0 w op fmt rd rs1 rs2 rs3 rm md (Z_to_bv 64 z1) (Z_to_bv 64 z2) (Z_to_bv 64 z3) res zr fl
                                  Hms F (eq_refl _) D FZ ltac:(vm_cast_no_check (eq_refl (Some md))) G1 G2 G3
                                  ltac:(vm_cast_no_check (eq_refl (res, fl))) ltac:(apply bv_eq; vm_cast_no_check (eq_refl zr))) as Hms';
                    clear F D G1 G2 G3 Hms; rename Hms' into Hms; exf_reabs Hms FZ
                end)))
            end
        (* [comment removed for export] *)
        | decode_any ?w = Some (Fari ?op ?fmt ?rd ?rs1 ?rs2 ?rm, _) =>
            let mdo := eval vm_compute in (rmode_of_field (bv_unsigned rm) 0) in
            lazymatch mdo with
            | Some ?md =>
              let G1 := fresh "G" in let G2 := fresh "G" in
              exf_closed E L fr rs1 G1 ltac:(fun z1 => exf_closed E L fr rs2 G2 ltac:(fun z2 =>
                let r := eval vm_compute in (fpv_ari op fmt md (fpv_rdw fmt (Z_to_bv 64 z1)) (fpv_rdw fmt (Z_to_bv 64 z2))) in
                lazymatch r with
                | (?res, ?fl) =>
                    let zr := eval vm_compute in (bv_unsigned (fpv_box fmt res)) in
                    pose proof (exf_fari segs E L fr cs rom R pc M ms0 w op fmt rd rs1 rs2 rm md (Z_to_bv 64 z1) (Z_to_bv 64 z2) res zr fl
                                  Hms F (eq_refl _) D FZ ltac:(vm_cast_no_check (eq_refl (Some md))) G1 G2
                                  ltac:(vm_cast_no_check (eq_refl (res, fl))) ltac:(apply bv_eq; vm_cast_no_check (eq_refl zr))) as Hms';
                    clear F D G1 G2 Hms; rename Hms' into Hms; exf_reabs Hms FZ
                end))
            end
        | decode_any _ = ?d => fail 100 "exf_step: no bridge for" d
        end
      end
    end
  end.

(* [comment removed for export] *)
Ltac exf_open Hms :=
  lazymatch type of Hms with
  | msteps ?segs ?ms0 (@mkst (mkFP ?fr ?cs) ?R ?pc (mem_denot ?E ?m ?log) ?rom) =>
      change (msteps segs ms0 (@mkst (mkFP (fr_denot E [] fr) cs) R pc (mem_denot E m log) rom)) in Hms
  end.

(* [comment removed for export] *)
Ltac exf_at_stop stops Hms :=
  lazymatch type of Hms with
  | msteps _ _ (mkst _ (Z_to_bv 64 ?pc) _ _) =>
      let b := eval vm_compute in (existsb (Z.eqb pc) stops) in
      lazymatch b with true => idtac | false => fail end
  end.
Ltac exf_pcnorm Hms :=
  lazymatch type of Hms with
  | msteps ?segs ?ms0 (@mkst ?fxk ?R (Z_to_bv 64 ?pc) ?M ?rom) =>
      let pc' := eval vm_compute in pc in change (msteps segs ms0 (@mkst fxk R (Z_to_bv 64 pc') M rom)) in Hms
  end.
Ltac ex_drive_loop fuel stops scr fdef HR Hlf HK Hms FZ :=
  first [ exf_at_stop stops Hms
        | (exf_step fdef HR Hlf HK Hms FZ; exf_pcnorm Hms;
           first [ exf_at_stop stops Hms
                 | (ex_cont fuel stops scr HR Hlf HK Hms; ex_drive_loop fuel stops scr fdef HR Hlf HK Hms FZ) ]) ].
Ltac ex_drive fuel stops scr fdef HR Hlf HK Hms FZ :=
  ex_cont fuel stops scr HR Hlf HK Hms; ex_drive_loop fuel stops scr fdef HR Hlf HK Hms FZ.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ex_st (segs : list Segment) (E : env) (m rom : word -> option byte) (ms0 : machine_state) (fxk : FPState)
                 (pc : Z) (sr : list expr) (log : list sentry) : Prop :=
  exists R, regs_ok E sr R /\ log_flat E log /\ msteps segs ms0 (@mkst fxk R (Z_to_bv 64 pc) (mem_denot E m log) rom).

Section Bundled.
Variable segs : list Segment.

Lemma ex_st_open : forall E m rom (fxk : FPState) R pc sr, regs_ok E sr R ->
  ex_st segs E m rom (@mkst fxk R (Z_to_bv 64 pc) m rom) fxk pc sr [].
Proof. intros E m rom fxk R pc sr HR. exists R. split; [exact HR|]. split; [exact I | apply mst_refl]. Qed.

Lemma ex_st_cont : forall fuel stops scr pc sr log kn nx pc' sr' log' kn' nx' scs scr' E m rom ms0 (fxk : FPState),
  sym_exec segs fuel true stops scr (SS pc sr log kn nx) [] = (SS pc' sr' log' kn' nx', scs, scr') ->
  know_ok segs E m kn -> scs_denot segs m E scs ->
  ex_st segs E m rom ms0 fxk pc sr log -> ex_st segs E m rom ms0 fxk pc' sr' log'.
Proof.
  intros fuel stops scr pc sr log kn nx pc' sr' log' kn' nx' scs scr' E m rom ms0 fxk Hex HK Hsc (R & HR & Hlf & Hms).
  destruct (@ex_cont_sound fxk segs fuel stops scr pc sr log kn nx _ scs scr' E m rom R ms0 Hex HR Hlf HK Hsc Hms) as (R' & HR' & Hlf' & Hms').
  exists R'. cbn [s_regs s_log s_pc] in *. split; [exact HR'|]. split; [exact Hlf' | exact Hms'].
Qed.

Lemma exb_fstore : forall E L fr cs m rom pc sr log kn ms0 w fmt rs1 rs2 (imm : bv 12) (e : expr),
  ex_st segs E m rom ms0 (mkFP (fr_denot E L fr) cs) pc sr log -> know_ok segs E m kn ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (FStore fmt rs1 rs2 imm, 4%Z) ->
  reg_get (fr_denot E L fr) rs2 = edenot E e ->
  forall (n : nat) (a : saddr) (scs0 : list sidecond),
  n = match fmt with FMT_S => 4%nat | FMT_D => 8%nat end -> to_saddrK kn (sr_get sr rs1) (bv_signed imm) = a ->
  flat_sc kn a n ++ storeok_sc kn a n = scs0 -> scs_denot segs m E scs0 ->
  ex_st segs E m rom ms0 (mkFP (fr_denot E L fr) cs) (pc + 4) sr (SE a n e :: log).
Proof.
  intros E L fr cs m rom pc sr log kn ms0 w fmt rs1 rs2 imm e (R & HR & Hlf & Hms) HK Hf He Hd Hv n a scs0 En Ea Es Hsc.
  destruct (exf_fstore segs E L fr cs m rom R pc sr log kn ms0 w fmt rs1 rs2 imm e Hms HR Hlf HK Hf He Hd Hv n a scs0 En Ea Es Hsc) as [Hms' Hlf'].
  exists R. split; [exact HR|]. split; [exact Hlf' | exact Hms'].
Qed.

Lemma exb_fld : forall E L fr cs m rom pc sr log kn ms0 w rd rs (imm : bv 12) (v : expr) scs,
  ex_st segs E m rom ms0 (mkFP (fr_denot E L fr) cs) pc sr log -> know_ok segs E m kn ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (FLoad FMT_D rd rs imm, 4%Z) ->
  forall (rb : expr) (rk : Z) (scs0 : list sidecond),
  to_saddrK kn (sr_get sr rs) (bv_signed imm) = SA rb rk -> ex_lookup segs kn log rb rk 8 = Some (v, scs) ->
  flat_sc kn (SA rb rk) 8 ++ scs = scs0 -> scs_denot segs m E scs0 ->
  ex_st segs E m rom ms0 (mkFP (fr_denot E ((rd, v) :: L) fr) cs) (pc + 4) sr log.
Proof.
  intros E L fr cs m rom pc sr log kn ms0 w rd rs imm v scs (R & HR & Hlf & Hms) HK Hf He Hd rb rk scs0 Ea Hlk Es Hsc.
  exists R. split; [exact HR|]. split; [exact Hlf|].
  exact (exf_fld segs E L fr cs m rom R pc sr log kn ms0 w rd rs imm v scs Hms HR Hlf HK Hf He Hd rb rk scs0 Ea Hlk Es Hsc).
Qed.

Lemma exb_flw : forall E L fr cs m rom pc sr log kn ms0 w rd rs (imm : bv 12) (v : expr) scs (zr : Z),
  ex_st segs E m rom ms0 (mkFP (fr_denot E L fr) cs) pc sr log -> know_ok segs E m kn ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (FLoad FMT_S rd rs imm, 4%Z) ->
  forall (rb : expr) (rk : Z) (scs0 : list sidecond),
  to_saddrK kn (sr_get sr rs) (bv_signed imm) = SA rb rk -> ex_lookup segs kn log rb rk 4 = Some (v, scs) ->
  flat_sc kn (SA rb rk) 4 ++ scs = scs0 -> scs_denot segs m E scs0 ->
  nan_box (bv_extract 0 32 (edenot E v)) = Z_to_bv 64 zr ->
  ex_st segs E m rom ms0 (mkFP (fr_denot E ((rd, ELit zr) :: L) fr) cs) (pc + 4) sr log.
Proof.
  intros E L fr cs m rom pc sr log kn ms0 w rd rs imm v scs zr (R & HR & Hlf & Hms) HK Hf He Hd rb rk scs0 Ea Hlk Es Hsc Hz.
  exists R. split; [exact HR|]. split; [exact Hlf|].
  exact (exf_flw segs E L fr cs m rom R pc sr log kn ms0 w rd rs imm v scs zr Hms HR Hlf HK Hf He Hd rb rk scs0 Ea Hlk Es Hsc Hz).
Qed.

Lemma exb_fmv_d_x : forall E L fr cs m rom pc sr log ms0 w rd rs1,
  ex_st segs E m rom ms0 (mkFP (fr_denot E L fr) cs) pc sr log ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (Fmv FMV_F_X FMT_D rd rs1, 4%Z) ->
  ex_st segs E m rom ms0 (mkFP (fr_denot E ((rd, sr_get sr rs1) :: L) fr) cs) (pc + 4) sr log.
Proof.
  intros E L fr cs m rom pc sr log ms0 w rd rs1 (R & HR & Hlf & Hms) Hf He Hd. exists R. split; [exact HR|]. split; [exact Hlf|].
  exact (exf_fmv_d_x segs E L fr cs rom R pc sr _ ms0 w rd rs1 Hms HR Hf He Hd).
Qed.
Lemma exb_fmv_w_x : forall E L fr cs m rom pc sr log ms0 w rd rs1 (zr : Z),
  ex_st segs E m rom ms0 (mkFP (fr_denot E L fr) cs) pc sr log ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (Fmv FMV_F_X FMT_S rd rs1, 4%Z) ->
  nan_box (low32 (edenot E (sr_get sr rs1))) = Z_to_bv 64 zr ->
  ex_st segs E m rom ms0 (mkFP (fr_denot E ((rd, ELit zr) :: L) fr) cs) (pc + 4) sr log.
Proof.
  intros E L fr cs m rom pc sr log ms0 w rd rs1 zr (R & HR & Hlf & Hms) Hf He Hd Hz. exists R. split; [exact HR|]. split; [exact Hlf|].
  exact (exf_fmv_w_x segs E L fr cs rom R pc sr _ ms0 w rd rs1 zr Hms HR Hf He Hd Hz).
Qed.

Lemma exb_fsgnj : forall E L fr cs m rom pc sr log ms0 w op fmt rd rs1 rs2 (w1 w2 : word) (zr : Z),
  ex_st segs E m rom ms0 (mkFP (fr_denot E L fr) cs) pc sr log ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (Fsgnj op fmt rd rs1 rs2, 4%Z) ->
  reg_get (fr_denot E L fr) rs1 = w1 -> reg_get (fr_denot E L fr) rs2 = w2 -> fpv_sgnj op fmt w1 w2 = Z_to_bv 64 zr ->
  ex_st segs E m rom ms0 (mkFP (fr_denot E ((rd, ELit zr) :: L) fr) cs) (pc + 4) sr log.
Proof.
  intros E L fr cs m rom pc sr log ms0 w op fmt rd rs1 rs2 w1 w2 zr (R & HR & Hlf & Hms) Hf He Hd H1 H2 Hz. exists R. split; [exact HR|]. split; [exact Hlf|].
  exact (exf_fsgnj segs E L fr cs rom R pc _ ms0 w op fmt rd rs1 rs2 w1 w2 zr Hms Hf He Hd H1 H2 Hz).
Qed.

Lemma exb_fcvt_ff : forall E L fr cs m rom pc sr log ms0 w dst src rd rs1 (rm : bv 3) md df sf (w1 : word) (res zr : Z) (fl : fflags),
  ex_st segs E m rom ms0 (mkFP (fr_denot E L fr) cs) pc sr log ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (Fcvt dst src rd rs1 rm, 4%Z) ->
  (dst = FC_S /\ df = FMT_S \/ dst = FC_D /\ df = FMT_D) -> (src = FC_S /\ sf = FMT_S \/ src = FC_D /\ sf = FMT_D) ->
  frm_zero cs -> rmode_of_field (bv_unsigned rm) 0 = Some md -> reg_get (fr_denot E L fr) rs1 = w1 ->
  fp_convert (fp_format sf) (fp_format df) md (fpv_rdw sf w1) = (res, fl) -> fpv_box df res = Z_to_bv 64 zr ->
  ex_st segs E m rom ms0 (mkFP (fr_denot E ((rd, ELit zr) :: L) fr) (fpv_acc cs fl)) (pc + 4) sr log.
Proof.
  intros E L fr cs m rom pc sr log ms0 w dst src rd rs1 rm md df sf w1 res zr fl (R & HR & Hlf & Hms) Hf He Hd Hdst Hsrc FZ Hmd Hr Hc Hb.
  exists R. split; [exact HR|]. split; [exact Hlf|].
  exact (exf_fcvt_ff segs E L fr cs rom R pc _ ms0 w dst src rd rs1 rm md df sf w1 res zr fl Hms Hf He Hd Hdst Hsrc FZ Hmd Hr Hc Hb).
Qed.

Lemma exb_fcmp : forall E L fr cs m rom pc sr log ms0 w op fmt rd rs1 rs2 (w1 w2 : word) (b : bool) (fl : fflags),
  ex_st segs E m rom ms0 (mkFP (fr_denot E L fr) cs) pc sr log ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (Fcmp op fmt rd rs1 rs2, 4%Z) ->
  reg_get (fr_denot E L fr) rs1 = w1 -> reg_get (fr_denot E L fr) rs2 = w2 ->
  fpv_cmp op fmt (fpv_rdw fmt w1) (fpv_rdw fmt w2) = (b, fl) ->
  ex_st segs E m rom ms0 (mkFP (fr_denot E L fr) (fpv_acc cs fl)) (pc + 4) (if bv_eqb rd 0 then sr else sr_upd sr (ridx rd) (ELit (if b then 1 else 0))) log.
Proof.
  intros E L fr cs m rom pc sr log ms0 w op fmt rd rs1 rs2 w1 w2 b fl (R & HR & Hlf & Hms) Hf He Hd H1 H2 Hc.
  destruct (exf_fcmp segs E L fr cs rom R pc sr _ ms0 w op fmt rd rs1 rs2 w1 w2 b fl Hms HR Hf He Hd H1 H2 Hc) as (R' & HR' & Hms').
  exists R'. split; [exact HR'|]. split; [exact Hlf | exact Hms'].
Qed.

Lemma exb_fma : forall E L fr cs m rom pc sr log ms0 w op fmt rd rs1 rs2 rs3 (rm : bv 3) md (w1 w2 w3 : word) (res zr : Z) (fl : fflags),
  ex_st segs E m rom ms0 (mkFP (fr_denot E L fr) cs) pc sr log ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (Fma op fmt rd rs1 rs2 rs3 rm, 4%Z) ->
  frm_zero cs -> rmode_of_field (bv_unsigned rm) 0 = Some md ->
  reg_get (fr_denot E L fr) rs1 = w1 -> reg_get (fr_denot E L fr) rs2 = w2 -> reg_get (fr_denot E L fr) rs3 = w3 ->
  fpv_fma op fmt md (fpv_rdw fmt w1) (fpv_rdw fmt w2) (fpv_rdw fmt w3) = (res, fl) -> fpv_box fmt res = Z_to_bv 64 zr ->
  ex_st segs E m rom ms0 (mkFP (fr_denot E ((rd, ELit zr) :: L) fr) (fpv_acc cs fl)) (pc + 4) sr log.
Proof.
  intros E L fr cs m rom pc sr log ms0 w op fmt rd rs1 rs2 rs3 rm md w1 w2 w3 res zr fl (R & HR & Hlf & Hms) Hf He Hd FZ Hmd H1 H2 H3 Hc Hb.
  exists R. split; [exact HR|]. split; [exact Hlf|].
  exact (exf_fma segs E L fr cs rom R pc _ ms0 w op fmt rd rs1 rs2 rs3 rm md w1 w2 w3 res zr fl Hms Hf He Hd FZ Hmd H1 H2 H3 Hc Hb).
Qed.

Lemma exb_fari : forall E L fr cs m rom pc sr log ms0 w op fmt rd rs1 rs2 (rm : bv 3) md (w1 w2 : word) (res zr : Z) (fl : fflags),
  ex_st segs E m rom ms0 (mkFP (fr_denot E L fr) cs) pc sr log ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (Fari op fmt rd rs1 rs2 rm, 4%Z) ->
  frm_zero cs -> rmode_of_field (bv_unsigned rm) 0 = Some md ->
  reg_get (fr_denot E L fr) rs1 = w1 -> reg_get (fr_denot E L fr) rs2 = w2 ->
  fpv_ari op fmt md (fpv_rdw fmt w1) (fpv_rdw fmt w2) = (res, fl) -> fpv_box fmt res = Z_to_bv 64 zr ->
  ex_st segs E m rom ms0 (mkFP (fr_denot E ((rd, ELit zr) :: L) fr) (fpv_acc cs fl)) (pc + 4) sr log.
Proof.
  intros E L fr cs m rom pc sr log ms0 w op fmt rd rs1 rs2 rm md w1 w2 res zr fl (R & HR & Hlf & Hms) Hf He Hd FZ Hmd H1 H2 Hc Hb.
  exists R. split; [exact HR|]. split; [exact Hlf|].
  exact (exf_fari segs E L fr cs rom R pc _ ms0 w op fmt rd rs1 rs2 rm md w1 w2 res zr fl Hms Hf He Hd FZ Hmd H1 H2 Hc Hb).
Qed.

Lemma exb_fcvt_xf : forall E L fr cs m rom pc sr log ms0 w dst src rd rs1 (rm : bv 3) md sf sgn bits (w1 : word) (zr : Z) (fl : fflags),
  ex_st segs E m rom ms0 (mkFP (fr_denot E L fr) cs) pc sr log ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (Fcvt dst src rd rs1 rm, 4%Z) ->
  (dst = FC_W /\ sgn = true /\ bits = 32%Z \/ dst = FC_WU /\ sgn = false /\ bits = 32%Z \/
   dst = FC_L /\ sgn = true /\ bits = 64%Z \/ dst = FC_LU /\ sgn = false /\ bits = 64%Z) ->
  (src = FC_S /\ sf = FMT_S \/ src = FC_D /\ sf = FMT_D) ->
  frm_zero cs -> rmode_of_field (bv_unsigned rm) 0 = Some md -> reg_get (fr_denot E L fr) rs1 = w1 ->
  fpv_x_of_f sf md sgn bits (fpv_rdw sf w1) = Z_to_bv 64 zr -> snd (fp_to_int (fp_format sf) md sgn bits (fpv_rdw sf w1)) = fl ->
  ex_st segs E m rom ms0 (mkFP (fr_denot E L fr) (fpv_acc cs fl)) (pc + 4) (if bv_eqb rd 0 then sr else sr_upd sr (ridx rd) (ELit zr)) log.
Proof.
  intros E L fr cs m rom pc sr log ms0 w dst src rd rs1 rm md sf sgn bits w1 zr fl (R & HR & Hlf & Hms) Hf He Hd Hdst Hsrc FZ Hmd H1 Hv Hfl.
  destruct (exf_fcvt_xf segs E L fr cs rom R pc sr _ ms0 w dst src rd rs1 rm md sf sgn bits w1 zr fl Hms HR Hf He Hd Hdst Hsrc FZ Hmd H1 Hv Hfl) as (R' & HR' & Hms').
  exists R'. split; [exact HR'|]. split; [exact Hlf | exact Hms'].
Qed.

(* [comment removed for export] *)
Lemma exf_lw_ext : forall v : word, v_lw v = ext_val true 0 4 v.
Proof.
  intros v. unfold v_lw, ext_val, ext_Z. f_equal. change (8 * Z.of_nat 0)%Z with 0%Z. change (2 ^ 0)%Z with 1%Z. rewrite Z.div_1_r.
  change (8 * N.of_nat 4)%N with 32%N. change (8 * Z.of_nat 4)%Z with 32%Z.
  unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2 ^ 32)%Z. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma exb_amoadd_w : forall E m rom pc sr log kn ms0 (fxk : FPState) w aq rl rd rs1 rs2 (v : expr) scs,
  ex_st segs E m rom ms0 fxk pc sr log -> know_ok segs E m kn ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (Amo AMO_ADD AW aq rl rd rs1 rs2, 4%Z) ->
  forall (rb : expr) (rk : Z) (scs0 : list sidecond),
  to_saddrK kn (sr_get sr rs1) 0 = SA rb rk -> ex_lookup segs kn log rb rk 4 = Some (v, scs) ->
  flat_sc kn (SA rb rk) 4 ++ storeok_sc kn (SA rb rk) 4 = scs0 -> scs_denot segs m E scs0 -> scs_denot segs m E scs ->
  (2 <=? ealign kn (sr_get sr rs1))%Z = true ->
  ex_st segs E m rom ms0 fxk (pc + 4) (if bv_eqb rd 0 then sr else sr_upd sr (ridx rd) (mkExt true 0 4 v))
        (SE (SA rb rk) 4 (mkAlu ALU_ADD v (sr_get sr rs2)) :: log).
Proof.
  intros E m rom pc sr log kn ms0 fxk w aq rl rd rs1 rs2 v scs (R & HR & Hlf & Hms) HK Hf He Hd rb rk scs0 Ea Hlk Es Hsc0 Hsc Hal. subst scs0.
  destruct (exf_storeok_sound segs E m kn (SA rb rk) 4%nat HK ltac:(lia) ltac:(lia) Hsc0) as [Hfl Hok].
  destruct (ex_lookup_sound segs E m kn log rb rk 4 v scs HK Hlf ltac:(lia) ltac:(lia) Hlk Hsc Hfl) as (bs & Hrd & Hlen & Hval).
  assert (Hadr : getr R rs1 = adenot E (SA rb rk)).
  { rewrite <- Ea, (to_saddrK_denot segs E m _ _ _ HK), (reg_val _ _ _ rs1 HR). unfold v_addi. symmetry. apply Z_to_bv_u_plus0. }
  assert (Hal4 : (bv_unsigned (getr R rs1) mod 4 = 0)%Z).
  { rewrite (reg_val _ _ _ rs1 HR). destruct (ealign_sound segs E m kn (sr_get sr rs1) HK) as [[A0 A1] A2]. apply Z.leb_le in Hal.
    apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (2 ^ ealign kn (sr_get sr rs1))); [|exact A2].
    exists (2 ^ (ealign kn (sr_get sr rs1) - 2))%Z. change 4%Z with (2 ^ 2)%Z. rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (Hv' : bytes_le_to_Z bs = bv_unsigned (edenot E v)).
  { rewrite <- Hval. pose proof (bytes_le_to_Z_bound bs) as B. pose proof (bytes_le_to_Z_nonneg bs) as B0. rewrite Hlen in B.
    change (8 * Z.of_nat 4)%Z with 32%Z in B. rewrite u_small; [reflexivity | lia]. }
  assert (Hok' : RiscvSemantics.store_ok segs (mem_denot E m log) (getr R rs1) 4 = true).
  { rewrite Hadr. eapply store_ok_mono; [apply mem_denot_grows | exact Hok]. }
  rewrite <- Hadr in Hrd.
  pose proof (step_amoadd_w segs R (Z_to_bv 64 pc) (mem_denot E m log) rom w aq rl rd rs1 rs2 bs (edenot E v) Hf He Hd Hal4 Hrd Hv' Hok') as ST.
  eexists. split; [| split; [| apply (exf_snoc segs _ _ rom R _ pc (mem_denot E m log) _ ms0 Hms); rewrite ST; cbn [mem_denot];
                               rewrite mkAlu_denot, <- (reg_val _ _ _ rs2 HR), <- Hadr; reflexivity]].
  - apply regs_ok_upd; [exact HR|]. rewrite mkExt_denot by lia. symmetry. apply exf_lw_ext.
  - cbn [log_flat]. split; [lia|]. split; [exact Hfl | exact Hlf].
Qed.
End Bundled.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ex_scbr_ok (s : sidecond) : bool :=
  match s with
  | SCBr t c a b =>
      match ladd (lin_of a) (lscale (-1) (lin_of b)) with
      | (k, []) => if Z.eqb (k mod 2 ^ 64) 0 then false else match c with BC_NE => t | BC_EQ => negb t | _ => false end
      | _ => false
      end
  | _ => false
  end.
Lemma ex_scbr_ok_sound : forall segs m E s, ex_scbr_ok s = true -> sc_denot segs m E s.
Proof.
  intros segs m E s H. destruct s as [t c a b| | | | | |]; try discriminate H. cbn [ex_scbr_ok] in H. cbn [sc_denot].
  destruct (ladd (lin_of a) (lscale (-1) (lin_of b))) as [k ts] eqn:El. destruct ts as [|]; [|discriminate H].
  destruct (Z.eqb (k mod 2 ^ 64) 0) eqn:Ek; [discriminate H|]. apply Z.eqb_neq in Ek.
  assert (NE : edenot E a <> edenot E b).
  { intros EQ. apply Ek.
    pose proof (ladd_sound E (lin_of a) (lscale (-1) (lin_of b))) as S1. rewrite El in S1. unfold lden in S1 at 1. cbn [fst snd tden] in S1.
    pose proof (lin_of_sound E a) as Sa. pose proof (lin_of_sound E b) as Sb. pose proof (lscale_sound E (-1) (lin_of b)) as Ss.
    unfold uE in Sa, Sb. rewrite EQ in Sa.
    destruct S1 as [q1 S1]. destruct Sa as [qa Sa]. destruct Sb as [qb Sb]. destruct Ss as [qs Ss].
    assert (k = (qa - qb + q1 + qs) * 2 ^ 64)%Z by lia. subst k. apply Z_mod_mult. }
  assert (NB : bv_eqb (edenot E a) (edenot E b) = false).
  { unfold bv_eqb. apply Z.eqb_neq. intros X. apply NE. apply bv_eq. exact X. }
  destruct c; try discriminate H; cbn [branch_taken]; rewrite NB; cbn [negb]; [destruct t; [discriminate H | reflexivity] | symmetry; exact H].
Qed.
Lemma ex_scbr_all : forall segs m E scs, forallb ex_scbr_ok scs = true -> scs_denot segs m E scs.
Proof.
  intros segs m E scs H. unfold scs_denot. apply Forall_forall. intros s Hin. rewrite forallb_forall in H. apply ex_scbr_ok_sound. exact (H s Hin).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac exb_open HR HK ST :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?regs =>
    lazymatch type of HK with
    | know_ok ?segs _ ?base _ =>
      lazymatch goal with
      | |- context [@mkst (mkFP ?fr ?cs) regs (Z_to_bv 64 ?pc) base ?rom] =>
          lazymatch fr with
          | fr_denot _ _ _ => pose proof (ex_st_open segs E base rom (mkFP fr cs) regs pc sr HR) as ST
          | _ => pose proof (ex_st_open segs E base rom (mkFP (fr_denot E [] fr) cs) regs pc sr HR) as ST
          end
      end
    end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac exb_scs r0 := first [ exact I | (apply ex_scbr_all; vm_compute; reflexivity) | (split_scs; ex_sc r0) ].

(* [comment removed for export] *)
Ltac exb_cont fuel stops scr HK ST k :=
  lazymatch type of ST with
  | ex_st ?segs ?E ?m ?rom ?ms0 ?fxk ?pc ?sr ?log =>
    lazymatch type of HK with
    | know_ok _ _ _ ?kn =>
        let nx := ex_nx E in
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr log kn nx) []) in
        lazymatch r with
        | (SS ?pc' ?sr' ?log' ?kn' ?nx', ?scs, ?scr') =>
            let ST' := fresh "ST" in
            let r0 := lazymatch E with ex_envL _ ?r0 _ => r0 end in
            pose proof (ex_st_cont segs fuel stops scr pc sr log kn nx pc' sr' log' kn nx' scs scr' E m rom ms0 fxk
                          ltac:(vm_cast_no_check (eq_refl (SS pc' sr' log' kn nx', scs, scr'))) HK ltac:(exb_scs r0) ST) as ST';
            clear ST; rename ST' into ST; k scr'
        end
    end
  end.

(* [comment removed for export] *)
Ltac exb_reabs ST FZ :=
  lazymatch type of ST with
  | ex_st _ _ _ _ _ (mkFP _ (fpv_acc ?cs ?fl)) _ _ _ =>
      let FZ' := fresh "FZ" in pose proof (fpv_frm_acc cs fl FZ) as FZ'; clear FZ; rename FZ' into FZ
  end.
Ltac exb_norm ST :=
  lazymatch type of ST with
  | ex_st ?segs ?E ?m ?rom ?ms0 ?fxk ?pc ?sr ?log =>
      let pc' := eval vm_compute in pc in let sr' := eval vm_compute in sr in
      change (ex_st segs E m rom ms0 fxk pc' sr' log) in ST
  end.

Ltac exb_closed E L fr r G cont := exf_closed E L fr r G cont.

(* [comment removed for export] *)
Ltac exb_fstep fdef HK ST FZ :=
  lazymatch type of ST with
  | ex_st ?segs ?E ?m ?rom ?ms0 (mkFP (fr_denot _ ?L ?fr) ?cs) ?pc ?sr ?log =>
    lazymatch type of HK with
    | know_ok _ _ _ ?kn =>
        let r0 := lazymatch E with ex_envL _ ?r0 _ => r0 end in
        let F := fresh "F" in let D := fresh "D" in let ST' := fresh "ST" in
        ex_fetch segs pc F D;
        lazymatch type of D with
        | decode_any ?w = Some (FStore ?fmt ?rs1 ?rs2 ?imm, _) =>
            let n := lazymatch fmt with FMT_S => constr:(4%nat) | FMT_D => constr:(8%nat) end in
            let a := eval vm_compute in (to_saddrK kn (sr_get sr rs1) (bv_signed imm)) in
            let scs0 := eval vm_compute in (flat_sc kn a n ++ storeok_sc kn a n) in
            let o := eval vm_compute in (fr_find L (ridx rs2)) in
            let Hv := fresh "Hv" in
            let e := lazymatch o with
                     | Some ?e => e
                     | None => let k := eval vm_compute in (ridx rs2) in let i := exf_default fdef k in constr:(EVar i)
                     end in
            assert (Hv : reg_get (fr_denot E L fr) rs2 = edenot E e)
              by (lazymatch o with
                  | Some _ => apply fr_get_expr; vm_cast_no_check (eq_refl o)
                  | None => eapply fr_get_unknown; [vm_cast_no_check (eq_refl (@None expr)) | reflexivity | reflexivity]
                  end);
            pose proof (exb_fstore segs E L fr cs m rom pc sr log kn ms0 w fmt rs1 rs2 imm e ST HK F (eq_refl _) D Hv n a scs0
                          (eq_refl _) ltac:(vm_cast_no_check (eq_refl a)) ltac:(vm_cast_no_check (eq_refl scs0)) ltac:(exb_scs r0)) as ST';
            clear F D Hv ST; rename ST' into ST
        | decode_any ?w = Some (FLoad FMT_D ?rd ?rs ?imm, _) =>
            let a := eval vm_compute in (to_saddrK kn (sr_get sr rs) (bv_signed imm)) in
            lazymatch a with
            | SA ?rb ?rk =>
              let lk := eval vm_compute in (ex_lookup segs kn log rb rk 8) in
              lazymatch lk with
              | Some (?v, ?scs) =>
                  let scs0 := eval vm_compute in (flat_sc kn a 8 ++ scs) in
                  pose proof (exb_fld segs E L fr cs m rom pc sr log kn ms0 w rd rs imm v scs ST HK F (eq_refl _) D rb rk scs0
                                ltac:(vm_cast_no_check (eq_refl a)) ltac:(vm_cast_no_check (eq_refl lk)) ltac:(vm_cast_no_check (eq_refl scs0))
                                ltac:(exb_scs r0)) as ST';
                  clear F D ST; rename ST' into ST
              | _ => fail 100 "exb: fld finds no value at" a
              end
            end
        | decode_any ?w = Some (FLoad FMT_S ?rd ?rs ?imm, _) =>
            let a := eval vm_compute in (to_saddrK kn (sr_get sr rs) (bv_signed imm)) in
            lazymatch a with
            | SA ?rb ?rk =>
              let lk := eval vm_compute in (ex_lookup segs kn log rb rk 4) in
              lazymatch lk with
              | Some (ELit ?z, ?scs) =>
                  let scs0 := eval vm_compute in (flat_sc kn a 4 ++ scs) in
                  let zr := eval vm_compute in (bv_unsigned (nan_box (bv_extract 0 32 (Z_to_bv 64 z)))) in
                  pose proof (exb_flw segs E L fr cs m rom pc sr log kn ms0 w rd rs imm (ELit z) scs zr ST HK F (eq_refl _) D rb rk scs0
                                ltac:(vm_cast_no_check (eq_refl a)) ltac:(vm_cast_no_check (eq_refl lk)) ltac:(vm_cast_no_check (eq_refl scs0))
                                ltac:(exb_scs r0)
                                ltac:(change (nan_box (bv_extract 0 32 (Z_to_bv 64 z)) = Z_to_bv 64 zr); apply bv_eq; vm_cast_no_check (eq_refl zr))) as ST';
                  clear F D ST; rename ST' into ST
              | _ => fail 100 "exb: flw needs a closed value at" a "found" lk
              end
            end
        | decode_any ?w = Some (Fmv FMV_F_X FMT_D ?rd ?rs1, _) =>
            pose proof (exb_fmv_d_x segs E L fr cs m rom pc sr log ms0 w rd rs1 ST F (eq_refl _) D) as ST';
            lazymatch type of ST' with
            | ex_st _ _ _ _ _ (mkFP (fr_denot _ ((_, ?e) :: _) _) _) ?pc' _ _ =>
                let e' := eval vm_compute in e in
                change (ex_st segs E m rom ms0 (mkFP (fr_denot E ((rd, e') :: L) fr) cs) pc' sr log) in ST'
            end;
            clear F D ST; rename ST' into ST
        | decode_any ?w = Some (Fmv FMV_F_X FMT_S ?rd ?rs1, _) =>
            let e := eval vm_compute in (sr_get sr rs1) in
            lazymatch e with
            | ELit ?z =>
                let zr := eval vm_compute in (bv_unsigned (nan_box (low32 (Z_to_bv 64 z)))) in
                pose proof (exb_fmv_w_x segs E L fr cs m rom pc sr log ms0 w rd rs1 zr ST F (eq_refl _) D
                              ltac:(change (nan_box (low32 (Z_to_bv 64 z)) = Z_to_bv 64 zr); apply bv_eq; vm_cast_no_check (eq_refl zr))) as ST';
                clear F D ST; rename ST' into ST
            | _ => fail 100 "exb: fmv.w.x of a non-literal register" e
            end
        | decode_any ?w = Some (Fsgnj ?op ?fmt ?rd ?rs1 ?rs2, _) =>
            let G1 := fresh "G" in let G2 := fresh "G" in
            exf_closed E L fr rs1 G1 ltac:(fun z1 => exf_closed E L fr rs2 G2 ltac:(fun z2 =>
              let zr := eval vm_compute in (bv_unsigned (fpv_sgnj op fmt (Z_to_bv 64 z1) (Z_to_bv 64 z2))) in
              pose proof (exb_fsgnj segs E L fr cs m rom pc sr log ms0 w op fmt rd rs1 rs2 (Z_to_bv 64 z1) (Z_to_bv 64 z2) zr ST F (eq_refl _) D G1 G2
                            ltac:(apply bv_eq; vm_cast_no_check (eq_refl zr))) as ST';
              clear F D G1 G2 ST; rename ST' into ST))
        | decode_any ?w = Some (Fcvt ?dst ?src ?rd ?rs1 ?rm, _) =>
            let mdo := eval vm_compute in (rmode_of_field (bv_unsigned rm) 0) in
            let md := lazymatch mdo with Some ?md => md end in
            let sf := lazymatch src with FC_S => constr:(FMT_S) | FC_D => constr:(FMT_D) | _ => constr:(FMT_D) end in
            let G1 := fresh "G" in
            lazymatch dst with
            | FC_S =>
                exf_closed E L fr rs1 G1 ltac:(fun z1 =>
                  let r := eval vm_compute in (fp_convert (fp_format sf) (fp_format FMT_S) md (fpv_rdw sf (Z_to_bv 64 z1))) in
                  lazymatch r with (?res, ?fl) =>
                    let zr := eval vm_compute in (bv_unsigned (fpv_box FMT_S res)) in
                    pose proof (exb_fcvt_ff segs E L fr cs m rom pc sr log ms0 w dst src rd rs1 rm md FMT_S sf (Z_to_bv 64 z1) res zr fl ST F (eq_refl _) D
                                  ltac:(exf_disj) ltac:(exf_disj) FZ ltac:(vm_cast_no_check (eq_refl (Some md))) G1
                                  ltac:(vm_cast_no_check (eq_refl (res, fl))) ltac:(apply bv_eq; vm_cast_no_check (eq_refl zr))) as ST';
                    clear F D G1 ST; rename ST' into ST; exb_reabs ST FZ end)
            | FC_D =>
                exf_closed E L fr rs1 G1 ltac:(fun z1 =>
                  let r := eval vm_compute in (fp_convert (fp_format sf) (fp_format FMT_D) md (fpv_rdw sf (Z_to_bv 64 z1))) in
                  lazymatch r with (?res, ?fl) =>
                    let zr := eval vm_compute in (bv_unsigned (fpv_box FMT_D res)) in
                    pose proof (exb_fcvt_ff segs E L fr cs m rom pc sr log ms0 w dst src rd rs1 rm md FMT_D sf (Z_to_bv 64 z1) res zr fl ST F (eq_refl _) D
                                  ltac:(exf_disj) ltac:(exf_disj) FZ ltac:(vm_cast_no_check (eq_refl (Some md))) G1
                                  ltac:(vm_cast_no_check (eq_refl (res, fl))) ltac:(apply bv_eq; vm_cast_no_check (eq_refl zr))) as ST';
                    clear F D G1 ST; rename ST' into ST; exb_reabs ST FZ end)
            | _ =>
                let sgn := lazymatch dst with FC_W => constr:(true) | FC_L => constr:(true) | FC_WU => constr:(false) | FC_LU => constr:(false) end in
                let bits := lazymatch dst with FC_W => constr:(32%Z) | FC_WU => constr:(32%Z) | FC_L => constr:(64%Z) | FC_LU => constr:(64%Z) end in
                exf_closed E L fr rs1 G1 ltac:(fun z1 =>
                  let zr := eval vm_compute in (bv_unsigned (fpv_x_of_f sf md sgn bits (fpv_rdw sf (Z_to_bv 64 z1)))) in
                  let fl := eval vm_compute in (snd (fp_to_int (fp_format sf) md sgn bits (fpv_rdw sf (Z_to_bv 64 z1)))) in
                  pose proof (exb_fcvt_xf segs E L fr cs m rom pc sr log ms0 w dst src rd rs1 rm md sf sgn bits (Z_to_bv 64 z1) zr fl ST F (eq_refl _) D
                                ltac:(exf_disj) ltac:(exf_disj) FZ ltac:(vm_cast_no_check (eq_refl (Some md))) G1
                                ltac:(apply bv_eq; vm_cast_no_check (eq_refl zr)) ltac:(vm_cast_no_check (eq_refl fl))) as ST';
                  clear F D G1 ST; rename ST' into ST; exb_reabs ST FZ)
            end
        | decode_any ?w = Some (Fcmp ?op ?fmt ?rd ?rs1 ?rs2, _) =>
            let G1 := fresh "G" in let G2 := fresh "G" in
            exf_closed E L fr rs1 G1 ltac:(fun z1 => exf_closed E L fr rs2 G2 ltac:(fun z2 =>
              let r := eval vm_compute in (fpv_cmp op fmt (fpv_rdw fmt (Z_to_bv 64 z1)) (fpv_rdw fmt (Z_to_bv 64 z2))) in
              lazymatch r with (?b, ?fl) =>
                pose proof (exb_fcmp segs E L fr cs m rom pc sr log ms0 w op fmt rd rs1 rs2 (Z_to_bv 64 z1) (Z_to_bv 64 z2) b fl ST F (eq_refl _) D G1 G2
                              ltac:(vm_cast_no_check (eq_refl (b, fl)))) as ST';
                clear F D G1 G2 ST; rename ST' into ST; exb_reabs ST FZ end))
        | decode_any ?w = Some (Fma ?op ?fmt ?rd ?rs1 ?rs2 ?rs3 ?rm, _) =>
            let mdo := eval vm_compute in (rmode_of_field (bv_unsigned rm) 0) in
            let md := lazymatch mdo with Some ?md => md end in
            let G1 := fresh "G" in let G2 := fresh "G" in let G3 := fresh "G" in
            exf_closed E L fr rs1 G1 ltac:(fun z1 => exf_closed E L fr rs2 G2 ltac:(fun z2 => exf_closed E L fr rs3 G3 ltac:(fun z3 =>
              let r := eval vm_compute in (fpv_fma op fmt md (fpv_rdw fmt (Z_to_bv 64 z1)) (fpv_rdw fmt (Z_to_bv 64 z2)) (fpv_rdw fmt (Z_to_bv 64 z3))) in
              lazymatch r with (?res, ?fl) =>
                let zr := eval vm_compute in (bv_unsigned (fpv_box fmt res)) in
                pose proof (exb_fma segs E L fr cs m rom pc sr log ms0 w op fmt rd rs1 rs2 rs3 rm md (Z_to_bv 64 z1) (Z_to_bv 64 z2) (Z_to_bv 64 z3) res zr fl
                              ST F (eq_refl _) D FZ ltac:(vm_cast_no_check (eq_refl (Some md))) G1 G2 G3
                              ltac:(vm_cast_no_check (eq_refl (res, fl))) ltac:(apply bv_eq; vm_cast_no_check (eq_refl zr))) as ST';
                clear F D G1 G2 G3 ST; rename ST' into ST; exb_reabs ST FZ end)))
        | decode_any ?w = Some (Fari ?op ?fmt ?rd ?rs1 ?rs2 ?rm, _) =>
            let mdo := eval vm_compute in (rmode_of_field (bv_unsigned rm) 0) in
            let md := lazymatch mdo with Some ?md => md end in
            let G1 := fresh "G" in let G2 := fresh "G" in
            exf_closed E L fr rs1 G1 ltac:(fun z1 => exf_closed E L fr rs2 G2 ltac:(fun z2 =>
              let r := eval vm_compute in (fpv_ari op fmt md (fpv_rdw fmt (Z_to_bv 64 z1)) (fpv_rdw fmt (Z_to_bv 64 z2))) in
              lazymatch r with (?res, ?fl) =>
                let zr := eval vm_compute in (bv_unsigned (fpv_box fmt res)) in
                pose proof (exb_fari segs E L fr cs m rom pc sr log ms0 w op fmt rd rs1 rs2 rm md (Z_to_bv 64 z1) (Z_to_bv 64 z2) res zr fl
                              ST F (eq_refl _) D FZ ltac:(vm_cast_no_check (eq_refl (Some md))) G1 G2
                              ltac:(vm_cast_no_check (eq_refl (res, fl))) ltac:(apply bv_eq; vm_cast_no_check (eq_refl zr))) as ST';
                clear F D G1 G2 ST; rename ST' into ST; exb_reabs ST FZ end))
        | decode_any ?w = Some (Amo AMO_ADD AW ?aq ?rl ?rd ?rs1 ?rs2, _) =>
            let a := eval vm_compute in (to_saddrK kn (sr_get sr rs1) 0) in
            lazymatch a with
            | SA ?rb ?rk =>
              let lk := eval vm_compute in (ex_lookup segs kn log rb rk 4) in
              lazymatch lk with
              | Some (?v, ?scs) =>
                  let scs0 := eval vm_compute in (flat_sc kn a 4 ++ storeok_sc kn a 4) in
                  pose proof (exb_amoadd_w segs E m rom pc sr log kn ms0 _ w aq rl rd rs1 rs2 v scs ST HK F (eq_refl _) D rb rk scs0
                                ltac:(vm_cast_no_check (eq_refl a)) ltac:(vm_cast_no_check (eq_refl lk)) ltac:(vm_cast_no_check (eq_refl scs0))
                                ltac:(exb_scs r0) ltac:(exb_scs r0) ltac:(vm_cast_no_check (eq_refl true))) as ST';
                  clear F D ST; rename ST' into ST
              | _ => fail 100 "exb: amoadd.w finds no value at" a
              end
            end
        | decode_any _ = Some (Branch ?c ?rs1 ?rs2 ?imm, _) =>
            let a := eval vm_compute in (sr_get sr rs1) in let b := eval vm_compute in (sr_get sr rs2) in
            fail 100 "exb_fstep: UNDECIDED BRANCH at" pc ":" c a b
        | decode_any _ = ?d => fail 100 "exb_fstep: no bridge for" d "at" pc
        end
    end
  end.

Ltac exb_at_stop stops ST :=
  lazymatch type of ST with
  | ex_st _ _ _ _ _ _ ?pc _ _ =>
      let b := eval vm_compute in (existsb (Z.eqb pc) stops) in
      lazymatch b with true => idtac | false => fail end
  end.
Ltac exb_drive_loop fuel stops scr fdef HK ST FZ :=
  first [ exb_at_stop stops ST
        | (exb_fstep fdef HK ST FZ; exb_norm ST;
           first [ exb_at_stop stops ST
                 | exb_cont fuel stops scr HK ST ltac:(fun scr' => exb_drive_loop fuel stops scr' fdef HK ST FZ) ]) ].
Ltac exb_drive fuel stops scr fdef HK ST FZ :=
  exb_cont fuel stops scr HK ST ltac:(fun scr' => exb_drive_loop fuel stops scr' fdef HK ST FZ).

(* [comment removed for export] *)
Ltac exb_exit ST R HR Hlf Hms := destruct ST as (R & HR & Hlf & Hms).

(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import RelocLept.

(* [comment removed for export] *)
Definition ex_bz (b : bool) : Z := if b then 1%Z else 0%Z.
Definition ex_lin_ltu (kn : list kentry) (x y : expr) : option bool :=
  match ladd (lin_of x) (lscale (-1) (lin_of y)) with
  | (k, []) =>
      let ks := snorm k in
      match erange kn y with
      | Some (lo, hi) => if ((0 <=? lo) && (0 <=? lo + ks) && (hi + ks <? 2 ^ 64) && (hi <? 2 ^ 64))%Z%bool then Some (ks <? 0)%Z else None
      | None => None
      end
  | _ => None
  end.
(* [comment removed for export] *)
Definition ex_neg_rng (kn : list kentry) (e : expr) : option (Z * Z) :=
  match lin_of e with
  | (k, [(c1, v)]) =>
      if Z.eqb (c1 mod 2 ^ 64) (2 ^ 64 - 1) then
        match erange kn v with
        | Some (lo, hi) => let ks := snorm k in
            if ((0 <=? lo) && (hi <? 2 ^ 64) && (ks - lo <? 0) && (- 2 ^ 64 <? ks - hi))%Z%bool then Some (2 ^ 64 + ks - hi, 2 ^ 64 + ks - lo)%Z else None
        | None => None
        end
      else None
  | _ => None
  end.
Fixpoint ex_rng (kn : list kentry) (e : expr) : option (Z * Z) :=
  match ex_neg_rng kn e with Some r => Some r | None =>
  match e with
  | EAlu ALU_XOR x (ELit m) =>
      match ex_rng kn x with
      | Some (lo, hi) =>
          if Z.eqb (m mod 2 ^ 64) (2 ^ 64 - 1) then (if ((0 <=? lo) && (hi <? 2 ^ 64))%Z%bool then Some (2 ^ 64 - 1 - hi, 2 ^ 64 - 1 - lo)%Z else erange kn e)
          else if ((lo =? hi) && (0 <=? lo) && (lo <? 2 ^ 64))%Z%bool then Some (Z.lxor lo (m mod 2 ^ 64), Z.lxor lo (m mod 2 ^ 64)) else erange kn e
      | None => erange kn e
      end
  | EAlu ALU_XOR x y =>
      match ex_rng kn x, ex_rng kn y with
      | Some (xl, xh), Some (yl, yh) =>
          if ((xl =? xh) && (yl =? yh) && (0 <=? xl) && (xl <? 2 ^ 64) && (0 <=? yl) && (yl <? 2 ^ 64))%Z%bool then Some (Z.lxor xl yl, Z.lxor xl yl) else erange kn e
      | _, _ => erange kn e
      end
  | EAlu ALU_SLTU x y =>
      match ex_lin_ltu kn x y with
      | Some b => Some (ex_bz b, ex_bz b)
      | None =>
          match ex_rng kn x, ex_rng kn y with
          | Some (al, ah), Some (bl, bh) => match itv_ltu al ah bl bh with Some b => Some (ex_bz b, ex_bz b) | None => erange kn e end
          | _, _ => erange kn e
          end
      end
  | _ => erange kn e
  end end.
(* [comment removed for export] *)
Definition ex_ptr_ne (kn : list kentry) (a b : expr) : bool :=
  let sa := to_saddr a 0 in let sb := to_saddr b 0 in
  (ranges_apart kn (a_base sa) (a_off sa) 1 (a_base sb) (a_off sb) 1
   && match flat_sc kn sa 1 with [] => true | _ => false end && match flat_sc kn sb 1 with [] => true | _ => false end)%bool.
Definition ex_decide (kn : list kentry) (c : branch_cond) (a b : expr) : option bool :=
  match decide_branch kn c a b with
  | Some t => Some t
  | None =>
      match (match c, ladd (lin_of a) (lscale (-1) (lin_of b)) with
             | BC_NE, (k, []) => if Z.eqb (k mod 2 ^ 64) 0 then None else Some true
             | BC_EQ, (k, []) => if Z.eqb (k mod 2 ^ 64) 0 then None else Some false
             | _, _ => None
             end) with
      | Some t => Some t
      | None =>
          match (match c with BC_LTU => ex_lin_ltu kn a b | BC_GEU => option_map negb (ex_lin_ltu kn a b)
                         | BC_NE => if ex_ptr_ne kn a b then Some true else None | BC_EQ => if ex_ptr_ne kn a b then Some false else None
                         | _ => None end) with
          | Some t => Some t
          | None => match ex_rng kn a, ex_rng kn b with
                    | Some (al, ah), Some (bl, bh) => range_branch c al ah bl bh
                    | _, _ => None
                    end
          end
      end
  end.

Section Auto.
Context {fx0 : FPState}.
Variable segs : list Segment.

Lemma ex_lin_diff : forall E (a b : expr) (k : Z), ladd (lin_of a) (lscale (-1) (lin_of b)) = (k, []) ->
  exists q : Z, (bv_unsigned (edenot E a) = bv_unsigned (edenot E b) + k + q * 2 ^ 64)%Z.
Proof.
  intros E a b k El.
  pose proof (ladd_sound E (lin_of a) (lscale (-1) (lin_of b))) as S1. rewrite El in S1. unfold lden in S1 at 1. cbn [fst snd tden] in S1.
  pose proof (lin_of_sound E a) as Sa. pose proof (lin_of_sound E b) as Sb. pose proof (lscale_sound E (-1) (lin_of b)) as Ss.
  unfold uE in Sa, Sb. destruct S1 as [q1 S1]. destruct Sa as [qa Sa]. destruct Sb as [qb Sb]. destruct Ss as [qs Ss].
  exists (qb - qa - q1 - qs)%Z. lia.
Qed.

Lemma ex_lin_ltu_sound : forall E M kn x y t, know_ok segs E M kn -> ex_lin_ltu kn x y = Some t ->
  (bv_unsigned (edenot E x) <? bv_unsigned (edenot E y))%Z = t.
Proof.
  intros E M kn x y t HK H. unfold ex_lin_ltu in H.
  destruct (ladd (lin_of x) (lscale (-1) (lin_of y))) as [k ts] eqn:El. destruct ts as [|]; [|discriminate H].
  destruct (erange kn y) as [[lo hi]|] eqn:Er; [|discriminate H].
  destruct ((0 <=? lo) && (0 <=? lo + snorm k) && (hi + snorm k <? 2 ^ 64) && (hi <? 2 ^ 64))%Z%bool eqn:Ec; [|discriminate H].
  injection H as <-. apply andb_true_iff in Ec as [Ec C4]. apply andb_true_iff in Ec as [Ec C3]. apply andb_true_iff in Ec as [C1 C2].
  apply Z.leb_le in C1, C2. apply Z.ltb_lt in C3, C4.
  pose proof (erange_sound segs E M kn y lo hi HK Er) as Ry. pose proof (u64_range (edenot E x)) as Rx.
  destruct (ex_lin_diff E x y k El) as [q Hq]. destruct (eqm_snorm k) as [q2 Hs].
  assert (EQ : (bv_unsigned (edenot E x) = bv_unsigned (edenot E y) + snorm k)%Z).
  { assert (X : (bv_unsigned (edenot E x) - (bv_unsigned (edenot E y) + snorm k) = (q - q2) * 2 ^ 64)%Z) by lia.
    assert (Q0 : (q - q2 = 0)%Z) by nia. lia. }
  rewrite EQ. destruct (Z.ltb_spec (snorm k) 0); [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma ex_neg_rng_sound : forall E M kn e lo hi, know_ok segs E M kn -> ex_neg_rng kn e = Some (lo, hi) ->
  (lo <= bv_unsigned (edenot E e) <= hi)%Z.
Proof.
  intros E M kn e lo hi HK H. unfold ex_neg_rng in H. destruct (lin_of e) as [k ts] eqn:El.
  destruct ts as [|[c1 v] [|]]; try discriminate H.
  destruct (Z.eqb (c1 mod 2 ^ 64) (2 ^ 64 - 1)) eqn:Ec1; [|discriminate H]. apply Z.eqb_eq in Ec1.
  destruct (erange kn v) as [[l h]|] eqn:Er; [|discriminate H].
  destruct ((0 <=? l) && (h <? 2 ^ 64) && (snorm k - l <? 0) && (- 2 ^ 64 <? snorm k - h))%Z%bool eqn:Ec; [|discriminate H]. injection H as <- <-.
  apply andb_true_iff in Ec as [Ec C4]. apply andb_true_iff in Ec as [Ec C3]. apply andb_true_iff in Ec as [C1 C2].
  apply Z.leb_le in C1. apply Z.ltb_lt in C2, C3, C4.
  pose proof (erange_sound segs E M kn v l h HK Er) as Rv. pose proof (u64_range (edenot E e)) as Re.
  pose proof (lin_of_sound E e) as Se. rewrite El in Se. unfold lden in Se. cbn [fst snd tden] in Se. unfold uE in Se. destruct Se as [q Hq].
  destruct (eqm_snorm k) as [q2 Hs]. pose proof (Z.div_mod c1 (2 ^ 64) ltac:(lia)) as Dc. rewrite Ec1 in Dc.
  set (uv := bv_unsigned (edenot E v)) in *. set (ue := bv_unsigned (edenot E e)) in *.
  set (T := ((c1 / 2 ^ 64 + 1) * uv)%Z).
  assert (ET : (c1 * uv = 2 ^ 64 * T - uv)%Z) by (rewrite Dc at 1; unfold T; ring).
  clearbody T. clear Dc Ec1.
  assert (X : (ue - (2 ^ 64 + snorm k - uv) = (T - q - q2 - 1) * 2 ^ 64)%Z) by lia.
  assert (Q0 : (T - q - q2 - 1 = 0)%Z) by lia. lia.
Qed.

Lemma ex_rng_sound : forall E M kn e lo hi, know_ok segs E M kn -> ex_rng kn e = Some (lo, hi) ->
  (lo <= bv_unsigned (edenot E e) <= hi)%Z.
Proof.
  intros E M kn e. induction e as [x|v|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx l n e' IH|sx k j n]; intros lo hi HK H;
    cbn [ex_rng] in H;
    (destruct (ex_neg_rng kn _) as [r|] eqn:En in H; [injection H as ->; exact (ex_neg_rng_sound E M kn _ lo hi HK En)|]);
    try (exact (erange_sound segs E M kn _ lo hi HK H)).
  assert (G : erange kn (EAlu op a b) = Some (lo, hi) -> (lo <= bv_unsigned (edenot E (EAlu op a b)) <= hi)%Z) by (apply (erange_sound segs E M kn _ lo hi HK)).
  destruct op; try (exact (G H)).
  - (* [comment removed for export] *)
    destruct (ex_lin_ltu kn a b) as [t|] eqn:El.
    + injection H as <- <-. cbn [edenot]. rewrite u_sltu64, (ex_lin_ltu_sound E M kn a b t HK El). destruct t; cbn [ex_bz]; lia.
    + destruct (ex_rng kn a) as [[al ah]|] eqn:Ea; [|exact (G H)]. destruct (ex_rng kn b) as [[bl bh]|] eqn:Eb; [|exact (G H)].
      destruct (itv_ltu al ah bl bh) as [t|] eqn:Ei; [|exact (G H)]. injection H as <- <-.
      cbn [edenot]. rewrite u_sltu64, (itv_ltu_sound al ah bl bh _ _ t (IHa al ah HK eq_refl) (IHb bl bh HK eq_refl) Ei). destruct t; cbn [ex_bz]; lia.
  - (* [comment removed for export] *)
    assert (GEN : match ex_rng kn a, ex_rng kn b with
                  | Some (xl, xh), Some (yl, yh) =>
                      if ((xl =? xh) && (yl =? yh) && (0 <=? xl) && (xl <? 2 ^ 64) && (0 <=? yl) && (yl <? 2 ^ 64))%Z%bool then Some (Z.lxor xl yl, Z.lxor xl yl) else erange kn (EAlu ALU_XOR a b)
                  | _, _ => erange kn (EAlu ALU_XOR a b)
                  end = Some (lo, hi) -> (lo <= bv_unsigned (edenot E (EAlu ALU_XOR a b)) <= hi)%Z).
    { intros H'. destruct (ex_rng kn a) as [[xl xh]|] eqn:Ea; [|exact (G H')]. destruct (ex_rng kn b) as [[yl yh]|] eqn:Eb; [|exact (G H')].
      destruct ((xl =? xh) && (yl =? yh) && (0 <=? xl) && (xl <? 2 ^ 64) && (0 <=? yl) && (yl <? 2 ^ 64))%Z%bool eqn:Ec; [|exact (G H')].
      injection H' as <- <-. repeat (apply andb_true_iff in Ec as [Ec ?]). apply Z.eqb_eq in Ec.
      pose proof (IHa xl xh HK eq_refl) as Ra. pose proof (IHb yl yh HK eq_refl) as Rb.
      match goal with X : (yl =? yh)%Z = true |- _ => apply Z.eqb_eq in X end.
      cbn [edenot]. rewrite u_xor64. replace (bv_unsigned (edenot E a)) with xl by lia. replace (bv_unsigned (edenot E b)) with yl by lia. lia. }
    destruct b as [m| | | | | | |]; try (exact (GEN H)).
    destruct (ex_rng kn a) as [[l h]|] eqn:Er; [|exact (G H)]. pose proof (IHa l h HK eq_refl) as Ra. pose proof (u64_range (edenot E a)) as Ua.
    destruct (Z.eqb (m mod 2 ^ 64) (2 ^ 64 - 1)) eqn:Em.
    + apply Z.eqb_eq in Em. destruct ((0 <=? l) && (h <? 2 ^ 64))%Z%bool eqn:Ec; [|exact (G H)]. injection H as <- <-.
      cbn [edenot]. rewrite u_xor64, u_lit64a, Em, lxor_ones64 by lia. lia.
    + destruct ((l =? h) && (0 <=? l) && (l <? 2 ^ 64))%Z%bool eqn:Ec; [|exact (G H)]. injection H as <- <-.
      apply andb_true_iff in Ec as [Ec _]. apply andb_true_iff in Ec as [C1 _]. apply Z.eqb_eq in C1.
      cbn [edenot]. rewrite u_xor64, u_lit64a. replace (bv_unsigned (edenot E a)) with l by lia. lia.
Qed.

Lemma ex_ptr_ne_sound : forall E M kn a b, know_ok segs E M kn -> ex_ptr_ne kn a b = true -> bv_eqb (edenot E a) (edenot E b) = false.
Proof.
  intros E M kn a b HK H. unfold ex_ptr_ne in H. apply andb_true_iff in H as [H F2]. apply andb_true_iff in H as [H F1].
  set (sa := to_saddr a 0) in *. set (sb := to_saddr b 0) in *.
  assert (FA : flat E sa 1).
  { destruct (flat_sc kn sa 1) eqn:Ef; [|discriminate F1]. pose proof (flat_sc_sound segs E M kn sa 1%nat [] HK ltac:(lia) ltac:(lia)) as X. rewrite Ef in X. exact (proj1 (X (Forall_nil _))). }
  assert (FB : flat E sb 1).
  { destruct (flat_sc kn sb 1) eqn:Ef; [|discriminate F2]. pose proof (flat_sc_sound segs E M kn sb 1%nat [] HK ltac:(lia) ltac:(lia)) as X. rewrite Ef in X. exact (proj1 (X (Forall_nil _))). }
  pose proof (ranges_apart_sound segs E M kn _ _ _ _ _ _ HK H) as D.
  pose proof (flat_u E sa 1 FA) as UA. pose proof (flat_u E sb 1 FB) as UB.
  assert (EA : adenot E sa = edenot E a) by (unfold sa; rewrite to_saddr_denot; unfold v_addi; apply Z_to_bv_u_plus0).
  assert (EB : adenot E sb = edenot E b) by (unfold sb; rewrite to_saddr_denot; unfold v_addi; apply Z_to_bv_u_plus0).
  rewrite EA in UA. rewrite EB in UB. unfold bv_eqb. apply Z.eqb_neq. destruct sa as [ba ka], sb as [bb kb]. cbn [a_base a_off] in D. lia.
Qed.

Lemma ex_decide_sound : forall E M kn c a b t, know_ok segs E M kn -> ex_decide kn c a b = Some t ->
  branch_taken c (edenot E a) (edenot E b) = t.
Proof.
  intros E M kn c a b t HK H. unfold ex_decide in H.
  destruct (decide_branch kn c a b) as [t0|] eqn:Ed; [injection H as <-; exact (decide_branch_sound segs E M kn c a b t0 HK Ed)|].
  assert (LIN : forall k, ladd (lin_of a) (lscale (-1) (lin_of b)) = (k, []) -> (k mod 2 ^ 64 <> 0)%Z -> bv_eqb (edenot E a) (edenot E b) = false).
  { intros k El Ek. unfold bv_eqb. apply Z.eqb_neq. intros X. apply Ek. destruct (ex_lin_diff E a b k El) as [q Hq].
    assert (k = (- q) * 2 ^ 64)%Z by lia. subst k. apply Z_mod_mult. }
  destruct (match c, ladd (lin_of a) (lscale (-1) (lin_of b)) with
            | BC_NE, (k, []) => if Z.eqb (k mod 2 ^ 64) 0 then None else Some true
            | BC_EQ, (k, []) => if Z.eqb (k mod 2 ^ 64) 0 then None else Some false
            | _, _ => None
            end) as [t1|] eqn:El.
  - injection H as <-. destruct (ladd (lin_of a) (lscale (-1) (lin_of b))) as [k ts] eqn:Ek. destruct ts as [|]; [|destruct c; discriminate El].
    destruct (Z.eqb (k mod 2 ^ 64) 0) eqn:Ez; [destruct c; discriminate El|]. apply Z.eqb_neq in Ez.
    destruct c; try discriminate El; injection El as <-; cbn [branch_taken]; rewrite (LIN k eq_refl Ez); reflexivity.
  - destruct (match c with BC_LTU => ex_lin_ltu kn a b | BC_GEU => option_map negb (ex_lin_ltu kn a b)
                         | BC_NE => if ex_ptr_ne kn a b then Some true else None | BC_EQ => if ex_ptr_ne kn a b then Some false else None
                         | _ => None end) as [t2|] eqn:E2.
    + injection H as <-. destruct c; try discriminate E2; cbn [branch_taken]; unfold bv_ltu.
      * destruct (ex_ptr_ne kn a b) eqn:Ep; [|discriminate E2]. injection E2 as <-. exact (ex_ptr_ne_sound E M kn a b HK Ep).
      * destruct (ex_ptr_ne kn a b) eqn:Ep; [|discriminate E2]. injection E2 as <-. rewrite (ex_ptr_ne_sound E M kn a b HK Ep). reflexivity.
      * exact (ex_lin_ltu_sound E M kn a b t2 HK E2).
      * destruct (ex_lin_ltu kn a b) as [t3|] eqn:E3; [|discriminate E2]. injection E2 as <-. rewrite (ex_lin_ltu_sound E M kn a b t3 HK E3). reflexivity.
    + destruct (ex_rng kn a) as [[al ah]|] eqn:Ea; [|discriminate H]. destruct (ex_rng kn b) as [[bl bh]|] eqn:Eb; [|discriminate H].
      exact (range_branch_sound c al ah bl bh _ _ t (ex_rng_sound E M kn a al ah HK Ea) (ex_rng_sound E M kn b bl bh HK Eb) H).
Qed.

Definition ex_sc_auto (kn : list kentry) (s : sidecond) : bool :=
  match s with
  | SCBr t c a b => match ex_decide kn c a b with Some t' => Bool.eqb t t' | None => false end
  | _ => false
  end.
Lemma ex_scs_auto : forall E M kn scs, know_ok segs E M kn -> forallb (ex_sc_auto kn) scs = true -> scs_denot segs M E scs.
Proof.
  intros E M kn scs HK H. unfold scs_denot. apply Forall_forall. intros s Hin. rewrite forallb_forall in H. specialize (H s Hin).
  destruct s as [t c a b| | | | | |]; try discriminate H. cbn [ex_sc_auto] in H. cbn [sc_denot].
  destruct (ex_decide kn c a b) as [t'|] eqn:Ed; [|discriminate H]. apply Bool.eqb_prop in H. subst t'.
  exact (ex_decide_sound E M kn c a b t HK Ed).
Qed.

(* [comment removed for export] *)
Fixpoint ex_auto (rounds fuel : nat) (stops : list Z) (first : bool) (scr : scripts) (ss : sym_state) (acc : list sidecond)
  : sym_state * list sidecond * scripts :=
  match rounds with
  | O => (ss, acc, scr)
  | S r =>
      match sym_exec segs fuel first stops scr ss [] with
      | (ss1, scs1, scr1) =>
          if existsb (Z.eqb (s_pc ss1)) stops then (ss1, scs1 ++ acc, scr1) else
          match fetch_word segs (Z_to_bv 64 (s_pc ss1)) with
          | Some w =>
              match decode_any w with
              | Some (Branch c rs1 rs2 imm, _) =>
                  match ex_decide (s_know ss1) c (sr_get (s_regs ss1) rs1) (sr_get (s_regs ss1) rs2) with
                  | Some d =>
                      match sym_exec segs 1 true stops (SCR [d] [] []) ss1 [] with
                      | (ss2, scs2, _) => ex_auto r fuel stops false scr1 ss2 (scs2 ++ scs1 ++ acc)
                      end
                  | None => (ss1, scs1 ++ acc, scr1)
                  end
              | _ => (ss1, scs1 ++ acc, scr1)
              end
          | None => (ss1, scs1 ++ acc, scr1)
          end
      end
  end.

Lemma ex_auto_sound : forall rounds fuel stops first scr ss acc ss' scs scr' E base rom ms,
  ex_auto rounds fuel stops first scr ss acc = (ss', scs, scr') -> scs_denot segs base E scs -> st_ok segs E base rom ss ms ->
  exists ms', msteps segs ms ms' /\ st_ok segs E base rom ss' ms'.
Proof.
  induction rounds as [|r IH]; intros fuel stops first scr ss acc ss' scs scr' E base rom ms Hex Hsc Hst.
  { cbn in Hex. injection Hex as <- <- <-. exists ms. split; [apply mst_refl | exact Hst]. }
  cbn [ex_auto] in Hex.
  destruct (sym_exec segs fuel first stops scr ss []) as [[ss1 scs1] scr1] eqn:E1.
  assert (STOP : (ss1, scs1 ++ acc, scr1) = (ss', scs, scr') -> exists ms', msteps segs ms ms' /\ st_ok segs E base rom ss' ms').
  { intros X. injection X as <- <- <-. apply scs_denot_app in Hsc as [H1 _].
    exact (sym_exec_sound segs fuel first stops scr ss [] ss1 scs1 scr1 E base rom ms E1 H1 Hst). }
  destruct (existsb (Z.eqb (s_pc ss1)) stops); [exact (STOP Hex)|].
  destruct (fetch_word segs (Z_to_bv 64 (s_pc ss1))) as [w|]; [|exact (STOP Hex)].
  destruct (decode_any w) as [[i sz]|]; [|exact (STOP Hex)].
  destruct i; try (exact (STOP Hex)).
  match type of Hex with context [ex_decide ?k ?c ?a ?b] => destruct (ex_decide k c a b) as [d|]; [|exact (STOP Hex)] end.
  destruct (sym_exec segs 1 true stops (SCR [d] [] []) ss1 []) as [[ss2 scs2] scr2] eqn:E2.
  pose proof (IH fuel stops false scr1 ss2 (scs2 ++ scs1 ++ acc) ss' scs scr' E base rom) as IH'.
  assert (Hsc' : scs_denot segs base E scs) by exact Hsc.
  (* [comment removed for export] *)
  assert (SUF : forall rounds fuel stops first scr ss acc ss' scs scr', ex_auto rounds fuel stops first scr ss acc = (ss', scs, scr') -> exists pre, scs = pre ++ acc).
  { clear. induction rounds as [|r IH]; intros fuel stops first scr ss acc ss' scs scr' H.
    - cbn in H. injection H as <- <- <-. exists []. reflexivity.
    - cbn [ex_auto] in H. destruct (sym_exec segs fuel first stops scr ss []) as [[ss1 scs1] scr1].
      assert (ST : (ss1, scs1 ++ acc, scr1) = (ss', scs, scr') -> exists pre, scs = pre ++ acc) by (intros X; injection X as <- <- <-; exists scs1; reflexivity).
      destruct (existsb (Z.eqb (s_pc ss1)) stops); [exact (ST H)|].
      destruct (fetch_word segs (Z_to_bv 64 (s_pc ss1))) as [w|]; [|exact (ST H)].
      destruct (decode_any w) as [[i sz]|]; [|exact (ST H)]. destruct i; try (exact (ST H)).
      match type of H with context [ex_decide ?k ?c ?a ?b] => destruct (ex_decide k c a b) as [d|]; [|exact (ST H)] end.
      destruct (sym_exec segs 1 true stops (SCR [d] [] []) ss1 []) as [[ss2 scs2] scr2].
      destruct (IH _ _ _ _ _ _ _ _ _ H) as [pre ->]. exists (pre ++ scs2 ++ scs1). rewrite <- !app_assoc. reflexivity. }
  destruct (SUF _ _ _ _ _ _ _ _ _ _ Hex) as [pre ->].
  apply scs_denot_app in Hsc as [_ Hsc2]. apply scs_denot_app in Hsc2 as [H2 Hsc1]. apply scs_denot_app in Hsc1 as [H1 _].
  destruct (sym_exec_sound segs fuel first stops scr ss [] ss1 scs1 scr1 E base rom ms E1 H1 Hst) as (ms1 & M1 & St1).
  destruct (sym_exec_sound segs 1 true stops (SCR [d] [] []) ss1 [] ss2 scs2 scr2 E base rom ms1 E2 H2 St1) as (ms2 & M2 & St2).
  destruct (IH' ms2 Hex Hsc' St2) as (ms' & M3 & St3).
  exists ms'. split; [eapply msteps_trans; [exact M1 | eapply msteps_trans; [exact M2 | exact M3]] | exact St3].
Qed.
End Auto.

Lemma ex_st_auto : forall segs rounds fuel stops scr pc sr log kn nx pc' sr' log' kn' nx' scs scr' E m rom ms0 (fxk : FPState),
  ex_auto segs rounds fuel stops true scr (SS pc sr log kn nx) [] = (SS pc' sr' log' kn' nx', scs, scr') ->
  know_ok segs E m kn -> scs_denot segs m E scs ->
  ex_st segs E m rom ms0 fxk pc sr log -> ex_st segs E m rom ms0 fxk pc' sr' log'.
Proof.
  intros segs rounds fuel stops scr pc sr log kn nx pc' sr' log' kn' nx' scs scr' E m rom ms0 fxk Hex HK Hsc (R & HR & Hlf & Hms).
  destruct (@ex_auto_sound fxk segs rounds fuel stops true scr (SS pc sr log kn nx) [] _ scs scr' E m rom (@mkst fxk R (Z_to_bv 64 pc) (mem_denot E m log) rom) Hex Hsc)
    as (ms' & M1 & (R' & -> & HR' & Hlf' & _)).
  { exists R. cbn [s_pc s_log s_regs s_know]. split; [reflexivity|]. split; [exact HR|]. split; [exact Hlf | exact HK]. }
  exists R'. cbn [s_regs s_log s_pc] in *. split; [exact HR'|]. split; [exact Hlf' | eapply msteps_trans; [exact Hms | exact M1]].
Qed.

(* [comment removed for export] *)
Ltac exb_sc1 HK r0 :=
  first [ (lazymatch goal with |- sc_denot ?sg ?m ?E (SCBr ?t ?c ?a ?b) =>
             apply (ex_decide_sound sg E m _ c a b t HK); vm_compute; reflexivity end)
        | ex_sc r0 ].
(* [comment removed for export] *)
Ltac exb_scs_auto HK r0 := first [ exact I | (apply (ex_scs_auto _ _ _ _ _ HK); vm_compute; reflexivity) | (split_scs; exb_sc1 HK r0) ].
(* [comment removed for export] *)
Ltac exb_autoS rounds fuel stops scr HK ST k :=
  lazymatch type of ST with
  | ex_st ?segs ?E ?m ?rom ?ms0 ?fxk ?pc ?sr ?log =>
    lazymatch type of HK with
    | know_ok _ _ _ ?kn =>
        let nx := ex_nx E in
        let r := eval vm_compute in (ex_auto segs rounds fuel stops true scr (SS pc sr log kn nx) []) in
        lazymatch r with
        | (SS ?pc' ?sr' ?log' ?kn' ?nx', ?scs, ?scr') =>
            let ST' := fresh "ST" in
            let r0 := lazymatch E with ex_envL _ ?r0 _ => r0 end in
            pose proof (ex_st_auto segs rounds fuel stops scr pc sr log kn nx pc' sr' log' kn nx' scs scr' E m rom ms0 fxk
                          ltac:(vm_cast_no_check (eq_refl (SS pc' sr' log' kn nx', scs, scr'))) HK ltac:(exb_scs_auto HK r0) ST) as ST';
            clear ST; rename ST' into ST; k scr'
        end
    end
  end.
Ltac exb_auto rounds fuel stops HK ST := exb_autoS rounds fuel stops (SCR [] [] []) HK ST ltac:(fun _ => idtac).
(* [comment removed for export] *)
Ltac exb_at_jalr ST :=
  lazymatch type of ST with
  | ex_st ?segs _ _ _ _ _ ?pc _ _ =>
      let d := eval vm_compute in (match fetch_word segs (Z_to_bv 64 pc) with Some w => decode_any w | None => None end) in
      lazymatch d with Some (Jalr _ _ _, _) => idtac | _ => fail end
  end.
Ltac exb_adriveS_loop rounds fuel stops scr fdef HK ST FZ :=
  first [ exb_at_stop stops ST | exb_at_jalr ST
        | (exb_fstep fdef HK ST FZ; exb_norm ST;
           first [ exb_at_stop stops ST
                 | exb_autoS rounds fuel stops scr HK ST ltac:(fun scr' => exb_adriveS_loop rounds fuel stops scr' fdef HK ST FZ) ]) ].
(* [comment removed for export] *)
Ltac exb_adriveS rounds fuel stops scr fdef HK ST FZ :=
  exb_autoS rounds fuel stops scr HK ST ltac:(fun scr' => exb_adriveS_loop rounds fuel stops scr' fdef HK ST FZ).
Ltac exb_adrive rounds fuel stops fdef HK ST FZ := exb_adriveS rounds fuel stops (SCR [] [] []) fdef HK ST FZ.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma exb_ret_sound : forall segs E m rom ms0 (fxk : FPState) pc sr log w rd rs1 (imm : bv 12) (retw : word),
  ex_st segs E m rom ms0 fxk pc sr log ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (Jalr rd rs1 imm, 4%Z) ->
  bv_eqb rd 0 = true -> bv_signed imm = 0%Z -> edenot E (sr_get sr rs1) = retw -> ret_ok retw ->
  exists R, regs_ok E sr R /\ log_flat E log /\ msteps segs ms0 (@mkst fxk R retw (mem_denot E m log) rom).
Proof.
  intros segs E m rom ms0 fxk pc sr log w rd rs1 imm retw (R & HR & Hlf & Hms) Hf He Hd Hrd Himm Hra Hok.
  exists R. split; [exact HR|]. split; [exact Hlf|].
  eapply (ex_msteps_snoc segs); [exact Hms | reflexivity |].
  rewrite (step_jalr_gen segs R (Z_to_bv 64 pc) (mem_denot E m log) rom w rd rs1 imm Hf He Hd). rewrite Hrd, Himm.
  rewrite (reg_val _ _ _ rs1 HR), Hra. unfold ret_ok in Hok. change (jalr_tgt retw 0) with (v_jalr retw 0). rewrite Hok. reflexivity.
Qed.
(* [comment removed for export] *)
Ltac exb_ret ST retw Hra Hok R HR Hlf Hms :=
  lazymatch type of ST with
  | ex_st ?segs ?E ?m ?rom ?ms0 ?fxk ?pc ?sr ?log =>
      let F := fresh "F" in let D := fresh "D" in
      ex_fetch segs pc F D;
      lazymatch type of D with
      | decode_any ?w = Some (Jalr ?rd ?rs1 ?imm, _) =>
          let X := fresh "X" in
          assert (X : edenot E (sr_get sr rs1) = retw) by (etransitivity; [|exact Hra]; reflexivity);
          destruct (exb_ret_sound segs E m rom ms0 fxk pc sr log w rd rs1 imm retw ST F (eq_refl _) D
                      ltac:(vm_cast_no_check (eq_refl true)) ltac:(vm_cast_no_check (eq_refl 0%Z)) X Hok)
            as (R & HR & Hlf & Hms);
          clear F D X
      end
  end.
