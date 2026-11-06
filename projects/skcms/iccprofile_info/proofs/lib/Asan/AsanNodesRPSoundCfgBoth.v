(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.skcms.iccprofile_info.images Require Import AsanUbsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare AgentLib.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import SpinAlgCfg AsanAcctShapeCfg AsanPlanSoundCfg AsanPlanSoundSumsCfg.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import BothAsanRegionPoisoned BothAsanReadCheck BothAsanQCheckWalk BothAsanPlanImages BothSumsAsanSpecs.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanNodesRP.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Import AX2 AX2S AP APS APSX APSXC.
Unset Lia Cache.
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac el_lia_core := first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                                | Zify.zify; xlia zchecker ].
Local Ltac el_goal_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithFP1. Context {FP : PropExec.FPState}.
Definition cell8 (SEGS : list Segment) (m : word -> option byte) (a v : Z) : Prop :=
  rdn SEGS m (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v)).

(* [comment removed for export] *)
Definition img_cell (SEGS : list Segment) (a v : Z) : Prop :=
  forall m, (forall i, a <= i < a + 8 -> m (Z_to_bv 64 i) = None) -> cell8 SEGS m a v.
Record rp_img (SEGS : list Segment) (T : RPN.rptab) : Prop := {
  ri_gsb : img_cell SEGS (RPN.rp_gsb T) (RPN.rp_csb T);
  ri_gm1 : img_cell SEGS (RPN.rp_gm1 T) (RPN.rp_cm1 T);
  ri_gm2 : img_cell SEGS (RPN.rp_gm2 T) (RPN.rp_cm2 T);
  ri_ghi : img_cell SEGS (RPN.rp_ghi T) (RPN.rp_chi T);
  ri_cm1 : img_cell SEGS (RPN.rp_cm1 T) 0;
  ri_cm2 : img_cell SEGS (RPN.rp_cm2 T) 0
}.

(* [comment removed for export] *)
Definition rp_spec (SEGS : list Segment) (T : RPN.rptab) : Prop :=
  forall mem (beg n usp : Z) (regs : bvmap 5 word) (ra : word) (kb : byte),
    16 <= n <= 2 ^ 40 -> 0 <= beg ->
    (beg + n <= RPN.kLowEnd \/ (RPN.kHighBeg <= beg /\ beg + n <= RPN.kHighEnd)) ->
    80 <= usp < 2 ^ 64 ->
    RPN.SB + (beg + n - 1) / 8 < usp - 72 ->
    (forall g, beg / 8 <= g < (beg + n - 1) / 8 -> mem (Z_to_bv 64 (RPN.SB + g)) = Some (Z_to_bv 8 0)) ->
    rdn SEGS mem (Z_to_bv 64 (RPN.SB + (beg + n - 1) / 8)) 1 = Some [kb] ->
    (mem (Z_to_bv 64 (RPN.SB + (beg + n - 1) / 8)) = Some (Z_to_bv 8 0) \/ (beg + n - 1) mod 8 < bv_unsigned kb < 8) ->
    (forall a, usp - 72 <= a < usp -> store_ok SEGS mem (Z_to_bv 64 a) 1 = true) ->
    cell8 SEGS mem (RPN.rp_gsb T) (RPN.rp_csb T) -> cell8 SEGS mem (RPN.rp_csb T) RPN.SB ->
    cell8 SEGS mem (RPN.rp_gm1 T) (RPN.rp_cm1 T) -> cell8 SEGS mem (RPN.rp_cm1 T) 0 ->
    cell8 SEGS mem (RPN.rp_gm2 T) (RPN.rp_cm2 T) -> cell8 SEGS mem (RPN.rp_cm2 T) 0 ->
    cell8 SEGS mem (RPN.rp_ghi T) (RPN.rp_chi T) -> cell8 SEGS mem (RPN.rp_chi T) RPN.kHighEnd ->
    ret_ok ra -> getr regs 1%bv = ra -> getr regs 2%bv = Z_to_bv 64 usp ->
    getr regs 10%bv = Z_to_bv 64 beg -> getr regs 11%bv = Z_to_bv 64 n ->
    exists regs' mem',
      msteps SEGS (mkst regs (Z_to_bv 64 (RPN.rp_entry T)) mem (seg_rom SEGS)) (mkst regs' ra mem' (seg_rom SEGS))
      /\ kept_ok regs regs' /\ getr regs' 10%bv = Z_to_bv 64 0
      /\ (forall x : word, bv_unsigned x < usp - 72 \/ usp <= bv_unsigned x -> mem' x = mem x)
      /\ mem_grows mem mem'.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_img : forall SEGS n m (a : Z),
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, a <= i < a + Z.of_nat n -> m (Z_to_bv 64 i) = None) ->
  rdn SEGS m (Z_to_bv 64 a) n = rdn SEGS (fun _ => None) (Z_to_bv 64 a) n.
Proof.
  intros SEGS n. induction n as [|n IH]; intros m a Ha Hn Hm; [reflexivity|].
  cbn [rdn]. rewrite (Hm a) by lia.
  rewrite zbv_add1. rewrite (IH m (a + 1)); [reflexivity | lia | lia |].
  intros i Hi. apply Hm. lia.
Qed.

(* [comment removed for export] *)
Lemma map_unsigned_inj : forall (x y : list byte), map bv_unsigned x = map bv_unsigned y -> x = y.
Proof.
  induction x as [|a x IH]; intros [|b y] H; cbn in H; try discriminate; [reflexivity|].
  injection H as Hab Hxy. f_equal; [apply bv_eq; exact Hab | apply IH; exact Hxy].
Qed.
Lemma obytes_eq_of_unsigned : forall (x y : option (list byte)),
  option_map (map bv_unsigned) x = option_map (map bv_unsigned) y -> x = y.
Proof.
  intros [x|] [y|] H; cbn in H; try discriminate; [|reflexivity].
  injection H as H. f_equal. apply map_unsigned_inj. exact H.
Qed.
End WithFP1.

Ltac img_cell_vm :=
  intros m Hm; unfold cell8; rewrite (rdn_img _ 8 m) by (first [lia | intros i Hi; apply Hm; lia]);
  apply obytes_eq_of_unsigned; vm_compute; reflexivity.
Section WithFP2. Context {FP : PropExec.FPState}.
Lemma asan_rp_img : rp_img ASEGS RPN.RP_BOTH.
Proof. constructor; cbn [RPN.rp_gsb RPN.rp_csb RPN.rp_gm1 RPN.rp_cm1 RPN.rp_gm2 RPN.rp_cm2 RPN.rp_ghi RPN.rp_chi RPN.RP_BOTH]; img_cell_vm. Qed.

Lemma rp_clob_sub : forall r : bv 5, rp_clob r = true -> In (ridx r) caller_saved.
Proof.
  intros r H. unfold rp_clob in H.
  repeat (apply orb_prop in H; destruct H as [H|H]);
    apply (f_equal negb) in H; cbn [negb] in H;
    match type of H with negb (bv_eqb r ?k) = false => destruct (bv_eq_dec 5 r k) as [->|NE]; [cbn; tauto | rewrite (bv_eqb_neq _ _ NE) in H; discriminate H] end.
Qed.

Lemma asan_rp_spec : rp_spec ASEGS RPN.RP_BOTH.
Proof.
  intros mem beg n usp regs ra kb Hn Hbeg Hrng Husp Hdisj Hz Hkb Hkok Hstk C1 C2 C3 C4 C5 C6 C7 C8 Hret H1 H2 H10 H11.
  assert (H : rpH mem beg n usp kb).
  { constructor; try assumption.
    unfold cells, cell. repeat split; assumption. }
  destruct (as_region_is_poisoned mem (seg_rom ASEGS) beg n usp kb H regs ra Hret H1 H2 H10 H11)
    as (regs' & Hms & Ha0 & Hsp & Hra & Hkeep).
  exists regs', (rp_frame mem usp ra (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)).
  split; [|split; [|split; [exact Ha0|split]]].
  - cbn [RPN.rp_entry RPN.RP_BOTH].
    match type of Hms with msteps _ (mkst _ ?p _ _) _ => replace (Z_to_bv 64 0x53bdc) with p by (apply bv_eq; reflexivity) end.
    exact Hms.
  - intros r Hr0 Hcs. destruct (bv_eq_dec 5 r 2%bv) as [->|Hne2]; [rewrite Hsp, H2; reflexivity|].
    apply Hkeep. destruct (rp_clob r) eqn:E; [|reflexivity]. exfalso. exact (Hcs (rp_clob_sub r E)).
  - intros x Hx. unfold rp_frame.
    rewrite !wbytes_out; try reflexivity; rewrite ?length_N_to_le_bytes, ?zbv_u by lia; lia.
  - unfold rp_frame. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
Qed.

(* [comment removed for export] *)
Definition rc_spec (SEGS : list Segment) (T : RPN.rptab) : Prop :=
  forall mem (rom : word -> option byte) (buf res : Z) (regs : bvmap 5 word),
    1 <= res <= 64 -> 0 <= buf -> buf + 64 < 2 ^ 64 ->
    cell8 SEGS mem (RPN.rp_gsb T) (RPN.rp_csb T) -> cell8 SEGS mem (RPN.rp_csb T) RPN.SB ->
    (forall j, 0 <= j < 16 -> mem (Z_to_bv 64 ((RPN.SB + buf / 8) / 8 * 8 + j)) = Some (Z_to_bv 8 0)) ->
    getr regs 9%bv = Z_to_bv 64 buf -> getr regs 10%bv = Z_to_bv 64 res ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 (RPN.rc_entry T)) mem rom) (mkst regs' (Z_to_bv 64 (RPN.rc_exit T)) mem rom)
      /\ getr regs' 11%bv = Z_to_bv 64 (RPN.SB + buf / 8)
      /\ getr regs' 12%bv = Z_to_bv 64 (RPN.SB + (buf + res - 1) / 8)
      /\ getr regs' 13%bv = Z_to_bv 64 (buf + res - 1)
      /\ getr regs' 14%bv = Z_to_bv 64 0 /\ getr regs' 15%bv = Z_to_bv 64 0
      /\ getr regs' 20%bv = v_addi (v_addi (getr regs 8%bv) (-2048)) (-72)
      /\ (forall r, r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 20%bv -> getr regs' r = getr regs r).

Lemma asan_rc_spec : rc_spec ASEGS RPN.RP_BOTH.
Proof.
  intros mem rom buf res regs Hres Hbuf Hbuf64 C1 C2 Hz H9 H10.
  destruct (as_read_check mem rom buf res Hres Hbuf Hbuf64 C1 C2 Hz regs H9 H10) as (regs' & Hms & Hrest).
  exists regs'. split; [|exact Hrest].
  cbn [RPN.rc_entry RPN.rc_exit RPN.RP_BOTH].
  match type of Hms with msteps _ (mkst _ ?p _ _) (mkst _ ?q _ _) =>
    replace (Z_to_bv 64 0x43710) with p by (apply bv_eq; reflexivity);
    replace (Z_to_bv 64 0x43768) with q by (apply bv_eq; reflexivity) end.
  exact Hms.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition qc_entry (T : RPN.rptab) (src : bool) : Z := if src then RPN.qs_entry T else RPN.qd_entry T.
Definition qc_exit (T : RPN.rptab) (src : bool) : Z := if src then RPN.qs_exit T else RPN.qd_exit T.
Definition qc_rb (src : bool) : bv 5 := if src then 11%bv else 10%bv.
Definition qc_re (src : bool) : bv 5 := if src then 19%bv else 20%bv.
Definition qc_clob (src : bool) (r : bv 5) : bool :=
  (bv_eqb r 13%bv || bv_eqb r 14%bv || bv_eqb r 15%bv || bv_eqb r 16%bv || bv_eqb r 17%bv || bv_eqb r (qc_re src))%bool.
Definition qc_spec (SEGS : list Segment) (T : RPN.rptab) (src : bool) : Prop :=
  forall mem (beg en : Z) (regs : bvmap 5 word) (kb : byte),
    1 <= beg -> beg <= en - 1 -> en <= 2 ^ 47 ->
    getr regs (qc_rb src) = Z_to_bv 64 beg -> getr regs (qc_re src) = Z_to_bv 64 en ->
    cell8 SEGS mem (RPN.rp_gsb T) (RPN.rp_csb T) -> cell8 SEGS mem (RPN.rp_csb T) RPN.SB ->
    (exists bs1, rdn SEGS mem (Z_to_bv 64 ((RPN.SB + beg / 8) / 8 * 8)) 8 = Some bs1) ->
    (exists bs2, rdn SEGS mem (Z_to_bv 64 ((RPN.SB + (en - 1) / 8) / 8 * 8)) 8 = Some bs2) ->
    (forall g, beg / 8 <= g < (en - 1) / 8 -> mem (Z_to_bv 64 (RPN.SB + g)) = Some (Z_to_bv 8 0)) ->
    rdn SEGS mem (Z_to_bv 64 (RPN.SB + (en - 1) / 8)) 1 = Some [kb] ->
    (bv_signed kb = 0 \/ (en - 1) mod 8 < bv_signed kb) ->
    exists regs',
      msteps SEGS (mkst regs (Z_to_bv 64 (qc_entry T src)) mem (seg_rom SEGS)) (mkst regs' (Z_to_bv 64 (qc_exit T src)) mem (seg_rom SEGS))
      /\ getr regs' (qc_re src) = Z_to_bv 64 (en - 1)
      /\ (forall r, qc_clob src r = false -> getr regs' r = getr regs r).

Section Sound.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Hypothesis SEGS_wx : AsanAcct.wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_okP A.
Hypothesis SEGS_wr : segs_wr_ok SEGS.      (* [comment removed for export] *)
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis NX0_sp : nx0_sp_ok nx0.   (* [comment removed for export] *)
Variable FS0 : Fs.Fs.
Variable T : RPN.rptab.
Hypothesis IMG : rp_img SEGS T.
Hypothesis SPEC : rp_spec SEGS T.
Hypothesis RSPEC : rc_spec SEGS T.
Hypothesis QSPEC : forall src, qc_spec SEGS T src.   (* [comment removed for export] *)

Lemma u_spw_sub72 : forall (spw : word), 72 <= bv_unsigned spw ->
  bv_unsigned (Sem.alu64 ALU_ADD spw (Z_to_bv 64 (-72))) = bv_unsigned spw - 72.
Proof.
  intros spw Hs. pose proof (u64_range spw). rewrite alu_add. unfold v_add.
  rewrite (u_lit64 (-72)). unfold two64.
  change ((-72) mod 2 ^ 64) with (2 ^ 64 - 72).
  replace (bv_unsigned spw + (2 ^ 64 - 72)) with ((bv_unsigned spw - 72) + 1 * 2 ^ 64) by lia.
  rewrite u_lit64. unfold two64. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma srl3_div8 : forall (x y : word), bv_unsigned y mod 64 = 3 ->
  Sem.alu64 ALU_SRL x y = Z_to_bv 64 (bv_unsigned x / 8).
Proof.
  intros x y Hy. rewrite alu_srl. unfold v_srl. rewrite Hy. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

#[local] Notation M_of E cs model FULL := (Mr A argH E cs model FULL).

(* [comment removed for export] *)
Lemma lit_cell_sound : forall E M k cell v,
  know_ok SEGS E M k -> 0 <= cell -> RPN.lit_cell SEGS k cell v = true -> cell8 SEGS M cell v.
Proof.
  intros E M k cell v HK Hc H. unfold RPN.lit_cell in H. apply andb_prop in H as [Hfl H].
  destruct (know_lookup SEGS k (ELit 0) cell 8 false [] []) as [e sc hs|sc hs|] eqn:HL; try discriminate.
  destruct sc; [|discriminate].
  destruct (erange k e) as [[lo hi]|] eqn:Her; [|discriminate].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst lo hi.
  pose proof (erange_sound SEGS E M k e v v HK Her) as Hv.
  destruct (flat_x_sound SEGS E M k (ELit 0) cell (ELit 8) HK Hfl) as (Clo & Chi & _).
  assert (HCst : estart E (SA (ELit 0) cell) = cell).
  { unfold estart; cbn [a_base a_off edenot]. rewrite u64_lit by lia. lia. }
  destruct (lookup_piece SEGS E M k (ELit 0) cell 8 e hs HK ltac:(lia) HL ltac:(unfold flat; rewrite HCst; rewrite HCst in Chi; cbn [edenot] in Chi; rewrite u64_lit in Chi by lia; lia))
    as (bs & Hrd & Hlen & Hbs).
  rewrite HCst in Hrd. unfold cell8. rewrite Hrd, <- Hbs. do 2 f_equal.
  rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E e)). f_equal. lia.
Qed.

Lemma img8_sound : forall E M k a v,
  know_ok SEGS E M k -> RPN.img8 k a = true -> img_cell SEGS a v -> cell8 SEGS M a v.
Proof.
  intros E M k a v HK H Himg. apply Himg. intros i Hi. exact (img_cov_sound SEGS E M k a (a + 8) HK H i Hi).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma v_add_zbv_mod : forall a b, v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. unfold v_add. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite <- Z.add_mod by lia. reflexivity.
Qed.
Lemma u8_lit0 : bv_unsigned (Z_to_bv 8 0) = 0.
Proof. reflexivity. Qed.
Lemma eaddz_denot : forall E a z, edenot E (eaddz a z) = Sem.alu64 ALU_ADD (edenot E a) (Z_to_bv 64 z).
Proof. intros. unfold eaddz. rewrite mkAlu_denot. reflexivity. Qed.
(* [comment removed for export] *)
Lemma qc_sh_denot : forall E M k x (xv : Z),
  know_ok SEGS E M k -> edenot E x = Z_to_bv 64 xv -> 0 <= xv < 2 ^ 64 ->
  edenot E (eadd (ELit RPN.SB) (mkSrl k x 3)) = Z_to_bv 64 (RPN.SB + xv / 8) /\ 0 <= RPN.SB + xv / 8 < 2 ^ 62.
Proof.
  intros E M k x xv HK Hx Hxv. unfold eadd. rewrite mkAlu_denot.
  rewrite (mkSrl_denot SEGS E M k x 3 (Z_to_bv 64 3) HK ltac:(rewrite u64_lit by lia; reflexivity)).
  rewrite Hx, (srl3_div8 (Z_to_bv 64 xv) (Z_to_bv 64 3)) by (rewrite u64_lit by lia; reflexivity).
  rewrite (zbv_u xv) by lia. cbn [edenot]. rewrite alu_add.
  assert (Hx8 : 0 <= xv / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite v_add_zbv by (unfold RPN.SB; lia). unfold RPN.SB in *. split; [reflexivity | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sh_facts (M : word -> option byte) (bz y1 : Z) (kb : byte) (kmax : Z) (zok : bool) : Prop :=
  (forall g, bz / 8 <= g < y1 / 8 -> M (Z_to_bv 64 (RPN.SB + g)) = Some (Z_to_bv 8 0))
  /\ rdn SEGS M (Z_to_bv 64 (RPN.SB + y1 / 8)) 1 = Some [kb]
  /\ bv_unsigned kb <= Z.max 0 kmax
  /\ (M (Z_to_bv 64 (RPN.SB + y1 / 8)) = Some (Z_to_bv 8 0) \/ (zok = true /\ bv_unsigned kb = 0) \/ y1 mod 8 < bv_unsigned kb).
(* [comment removed for export] *)
Definition words_facts (M : word -> option byte) (bz y1 : Z) : Prop :=
  forall a, (RPN.SB + bz / 8) / 8 * 8 <= a -> a + 8 <= RPN.SB + y1 / 8 + 8 -> exists bs, rdn SEGS M (Z_to_bv 64 a) 8 = Some bs.

Lemma sh_facts_zok : forall M bz y1 kb kmax zok, sh_facts M bz y1 kb kmax false -> sh_facts M bz y1 kb kmax zok.
Proof.
  intros M bz y1 kb kmax zok (H1 & H2 & H3 & H4). split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
  destruct H4 as [H | [[H _] | H]]; [left; exact H | discriminate H | right; right; exact H].
Qed.
Lemma rdn1_M0 : forall M (a : word), M a = Some (Z_to_bv 8 0) -> rdn SEGS M a 1 = Some [Z_to_bv 8 0].
Proof. intros M a H. cbn [rdn]. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sh_local_sound : forall E M k x y (xv yv kmax : Z) (zok : bool),
  know_ok SEGS E M k ->
  edenot E x = Z_to_bv 64 xv -> edenot E y = Z_to_bv 64 yv -> 0 <= xv <= yv -> yv < 2 ^ 64 ->
  RPN.qc_shadow_ok SEGS k (eadd (ELit RPN.SB) (mkSrl k x 3)) (eadd (ELit RPN.SB) (mkSrl k y 3)) y kmax zok = true ->
  exists kb, sh_facts M xv yv kb kmax zok.
Proof.
  intros E M k x y xv yv kmax zok HKN Hx Hy Hxy Hy64 Hsh.
  unfold RPN.qc_shadow_ok in Hsh.
  destruct (split_lit (eadd (ELit RPN.SB) (mkSrl k x 3))) as [lb lk] eqn:Hsl.
  destruct (split_lit (eadd (ELit RPN.SB) (mkSrl k y 3))) as [hb hk] eqn:Hsh2.
  apply andb_prop in Hsh as [Hsh HD]. apply andb_prop in Hsh as [Hss Hfll].
  destruct (qc_sh_denot E M k x xv HKN Hx ltac:(lia)) as [Dshb Rshb].
  destruct (qc_sh_denot E M k y yv HKN Hy ltac:(lia)) as [Dshe Rshe].
  assert (HL : edenot E (esub (eadd (ELit RPN.SB) (mkSrl k y 3)) (eadd (ELit RPN.SB) (mkSrl k x 3)))
               = Z_to_bv 64 (yv / 8 - xv / 8)).
  { unfold esub. rewrite mkAlu_denot, Dshb, Dshe, alu_sub. unfold v_sub. rewrite !zbv_u by lia. f_equal. lia. }
  assert (Hdv : xv / 8 <= yv / 8) by (apply Z.div_le_mono; lia).
  pose proof (w_split_lit_denot E _ lb lk Hsl) as Hslb. rewrite Dshb in Hslb.
  destruct (w_flat_x_sound SEGS E M k lb lk _ HKN Hfll) as (Llo & Lhi & _).
  rewrite eaddz_denot, HL, alu_add, v_add_zbv_mod, u64_lit in Lhi by lia.
  set (Hs := estart E (SA lb lk)) in *.
  assert (HHs : Hs = RPN.SB + xv / 8).
  { apply (f_equal bv_unsigned) in Hslb. unfold Hs, estart in Llo, Lhi |- *. cbn [a_base a_off] in Llo, Lhi |- *.
    rewrite !u64_lit in Hslb by lia. lia. }
  apply orb_prop in HD as [HzA | HDb].
  - destruct (kzero_x_sound SEGS E M k k lb lk _ HKN HKN HzA) as (Zb & _ & _).
    unfold elenZ in Zb. rewrite eaddz_denot, HL, alu_add, v_add_zbv_mod, u64_lit in Zb by lia. fold Hs in Zb. rewrite HHs in Zb.
    assert (ZZ : forall g, xv / 8 <= g <= yv / 8 -> M (Z_to_bv 64 (RPN.SB + g)) = Some (Z_to_bv 8 0)).
    { intros g Hg. replace (RPN.SB + g) with (RPN.SB + xv / 8 + (g - xv / 8)) by lia. apply Zb. lia. }
    exists (Z_to_bv 8 0). split; [|split; [|split]].
    + intros g Hg. apply ZZ. lia.
    + apply rdn1_M0. apply ZZ. lia.
    + rewrite u8_lit0. lia.
    + left. apply ZZ. lia.
  - apply andb_prop in HDb as [HDb HLK]. apply andb_prop in HDb as [HzB Hflp].
    destruct (kzero_x_sound SEGS E M k k lb lk _ HKN HKN HzB) as (Zb & _ & _).
    unfold elenZ in Zb. rewrite HL, u64_lit in Zb by lia. fold Hs in Zb. rewrite HHs in Zb.
    destruct (know_lookup SEGS k hb hk 1 false [] []) as [v0 scs hs|scs hs|] eqn:HL1; try discriminate HLK.
    destruct scs; [|discriminate HLK].
    destruct (erange k (extK k v0)) as [[lo hi]|] eqn:Her'; [|discriminate HLK].
    apply andb_prop in HLK as [HLK Hval]. apply andb_prop in HLK as [Hlo0 Hhik].
    apply Z.leb_le in Hlo0. apply Z.leb_le in Hhik.
    pose proof (erange_sound SEGS E M k _ lo hi HKN Her') as Hv. rewrite (extK_denot SEGS E M k v0 HKN) in Hv.
    pose proof (w_split_lit_denot E _ hb hk Hsh2) as HPw. rewrite Dshe in HPw.
    destruct (w_flat_x_sound SEGS E M k hb hk (ELit 1) HKN Hflp) as (Plo & Phi & _).
    set (P := estart E (SA hb hk)) in *.
    replace (bv_unsigned (edenot E (ELit 1))) with 1 in Phi by (cbn [edenot]; rewrite u64_lit by lia; reflexivity).
    pose proof (know_lookup_sound SEGS E M k hb hk 1 false [] [] HKN ltac:(lia) ltac:(lia)) as XL.
    rewrite HL1 in XL. destruct (XL ltac:(constructor) ltac:(unfold flat; fold P; lia)) as (bs3 & Hrd3 & Hlen3 & Hv3). clear XL.
    rewrite adenot_SA in Hrd3. fold P in Hrd3.
    destruct bs3 as [|kb [|]]; [discriminate Hlen3 | | discriminate Hlen3].
    cbn [extz] in Hv3. rewrite bytes_le_single in Hv3.
    pose proof (u8_range kb) as Hkr.
    assert (Hvk : bv_unsigned (edenot E v0) = bv_unsigned kb) by (rewrite <- Hv3; apply u64_lit; lia).
    assert (HPe : Z_to_bv 64 P = Z_to_bv 64 (RPN.SB + yv / 8)).
    { rewrite HPw. unfold P, estart. cbn [a_base a_off]. reflexivity. }
    exists kb. split; [|split; [|split]].
    + intros g Hg. replace (RPN.SB + g) with (RPN.SB + xv / 8 + (g - xv / 8)) by lia. apply Zb. lia.
    + rewrite <- HPe. exact Hrd3.
    + lia.
    + apply orb_prop in Hval as [Hh0|Hge].
      * right; left. apply andb_prop in Hh0 as [Hz Hh0]. apply Z.eqb_eq in Hh0. split; [exact Hz | lia].
      * right; right. pose proof (lin_ge0_sound SEGS E M k _ _ HKN Hge) as XG. cbn [xt_den] in XG.
        rewrite (extK_denot SEGS E M k v0 HKN) in XG.
        rewrite (mkAnd_denot SEGS E M k _ _ HKN), Hy in XG. cbn [edenot] in XG. rewrite alu_and in XG.
        unfold v_and in XG. rewrite (zbv_u yv) in XG by lia. rewrite (zbv_u 7) in XG by lia.
        change (Z.land yv 7) with (Z.land yv (Z.ones 3)) in XG. rewrite Z.land_ones in XG by lia.
        change (2 ^ 3) with 8 in XG. pose proof (Z.mod_pos_bound yv 8 ltac:(lia)).
        rewrite zbv_u in XG by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma covers_lit_sound : forall E M k zb lo hi,
  know_ok SEGS E M k -> RPN.covers_lit k zb lo hi = true ->
  forall a, bv_unsigned (edenot E zb) + lo <= a < bv_unsigned (edenot E zb) + hi ->
  0 <= a < 2 ^ 64 /\ rd1 SEGS M (Z_to_bv 64 a) <> None.
Proof.
  intros E M k zb lo hi HK H a Ha. unfold RPN.covers_lit in H.
  apply existsb_exists in H as (K & Hin & HKb).
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as KOK.
  destruct (RPN.readable_lit_entry K) as [[[b o] l]|] eqn:HR; [|discriminate].
  apply andb_prop in HKb as [HKb H2]. apply andb_prop in HKb as [Hb H1].
  apply expr_eqb_eq in Hb. subst b. apply Z.leb_le in H1. apply Z.leb_le in H2.
  set (zbv := bv_unsigned (edenot E zb)) in *.
  assert (GEN : flat E (SA zb o) (elenZ E (ELit l))
                /\ (forall i, 0 <= i < elenZ E (ELit l) -> rd1 SEGS M (Z_to_bv 64 (estart E (SA zb o) + i)) <> None)).
  { destruct K as [sa0 w v|sa n|sa n kk|lo' hi'|e m|e lo' hi'|sa n|a1 n1 a2 n2|sa n c|sa n | kinv_id kinv_args]; cbn [RPN.readable_lit_entry] in HR;
      try discriminate; destruct sa as [b' o']; destruct n as [l'| | | | | | |]; try discriminate; injection HR as -> -> ->;
      cbn [kentry_ok] in KOK.
    - destruct KOK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. unfold rd1. rewrite (Hz i Hi). discriminate.
    - destruct KOK as [Hfl Hw]. split; [exact Hfl|]. intros i Hi.
      specialize (Hw i 1%nat ltac:(lia) ltac:(cbn; lia)). cbn [store_ok] in Hw.
      destruct (wview SEGS M (Z_to_bv 64 (estart E (SA zb o) + i))) as [bb|] eqn:Hv; [|discriminate].
      unfold rd1. rewrite (wview_rd1 SEGS SEGS_wr M _ bb Hv). discriminate.
    - destruct KOK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. unfold rd1. rewrite (Hz i Hi). discriminate.
    - destruct KOK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. unfold rd1.
      destruct (M (Z_to_bv 64 (estart E (SA zb o) + i))) as [bb|] eqn:HM; [discriminate | exfalso; exact (Hz i Hi HM)]. }
  destruct GEN as [Hfl Hrd]. unfold flat, estart, elenZ in Hfl, Hrd. cbn [a_base a_off edenot] in Hfl, Hrd.
  fold zbv in Hfl, Hrd.
  assert (HL : bv_unsigned (Z_to_bv 64 l) = l mod two64).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). reflexivity. }
  rewrite HL in Hfl, Hrd.
  split; [lia|]. replace a with (zbv + o + (a - zbv - o)) by lia. apply Hrd. lia.
Qed.

Lemma words_of_cover : forall E M k zb lo hi,
  know_ok SEGS E M k -> RPN.covers_lit k zb lo hi = true ->
  forall a, bv_unsigned (edenot E zb) + lo <= a -> a + 8 <= bv_unsigned (edenot E zb) + hi ->
  exists bs, rdn SEGS M (Z_to_bv 64 a) 8 = Some bs.
Proof.
  intros E M k zb lo hi HK H a H1 H2.
  pose proof (covers_lit_sound E M k zb lo hi HK H) as C.
  destruct (C a ltac:(lia)) as [Ha _].
  destruct (C (a + 7) ltac:(lia)) as [Ha7 _].
  destruct (rdn_defined SEGS M 8 (Z_to_bv 64 a) ltac:(rewrite u64_lit by lia; cbn; lia)) as (bs & Hbs & _).
  { intros j Hj. rewrite u64_lit by lia. apply (proj2 (C (a + Z.of_nat j) ltac:(lia))). }
  exists bs. exact Hbs.
Qed.

Lemma u_mul8 : forall E zb, 8 * bv_unsigned (edenot E zb) < two64 ->
  bv_unsigned (edenot E (EMd M_MUL (ELit 8) zb)) = 8 * bv_unsigned (edenot E zb).
Proof.
  intros E zb H. cbn [edenot]. rewrite u_mul64, u64_lit by lia. pose proof (u64_range (edenot E zb)).
  unfold two64 in H. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma qc_cover_sound : forall E M k begE enE words (bz ez : Z) kmax zok,
  know_ok SEGS E M k -> RPN.qc_cover k begE enE words = true ->
  bv_unsigned (edenot E begE) = bz -> bv_unsigned (edenot E enE) = ez -> bz + 1 <= ez ->
  (exists kb, sh_facts M bz (ez - 1) kb kmax zok) /\ (words = true -> words_facts M bz (ez - 1)).
Proof.
  intros E M k begE enE words bz ez kmax zok HK H Hbz Hez Hlt.
  unfold RPN.qc_cover in H. apply existsb_exists in H as (K & Hin & HKb).
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as KOK.
  destruct K as [sa0 w v|sa n|sa n kk|lo' hi'|e m|e lo' hi'|sa n|a1 n1 a2 n2|sa n c|sa n | kinv_id kinv_args]; try discriminate.
  destruct sa as [zb zk]. destruct n as [zl| | | | | | |]; try discriminate.
  unfold RPN.qc_cover1 in HKb.
  destruct (xlo k zb) as [zblo|] eqn:Hzlo; [|discriminate]. destruct (xhi k zb) as [zbhi|] eqn:Hzhi; [|discriminate].
  apply andb_prop in HKb as [HKb HW]. apply andb_prop in HKb as [HKb HG2]. apply andb_prop in HKb as [HKb HG1].
  apply andb_prop in HKb as [HKb HB5]. apply andb_prop in HKb as [HKb HB4]. apply andb_prop in HKb as [HKb HB3].
  apply andb_prop in HKb as [HKb HB2]. rename HKb into HB1.
  apply Z.ltb_lt in HB1. apply Z.leb_le in HB2. apply Z.leb_le in HB3. apply Z.ltb_lt in HB4. apply Z.ltb_lt in HB5.
  pose proof (xlo_sound SEGS E M k zb zblo HK Hzlo) as Zlo. pose proof (xhi_sound SEGS E M k zb zbhi HK Hzhi) as Zhi.
  set (zbv := bv_unsigned (edenot E zb)) in *.
  pose proof (u_mul8 E zb ltac:(fold zbv; lia)) as U8. fold zbv in U8.
  pose proof (lin_ge0_sound SEGS E M k _ _ HK HG1) as G1. cbn [xt_den] in G1. rewrite U8, Hbz in G1.
  pose proof (lin_ge0_sound SEGS E M k _ _ HK HG2) as G2. cbn [xt_den] in G2. rewrite U8, Hez in G2.
  cbn [kentry_ok] in KOK. destruct KOK as [Hfl Hz]. unfold flat, estart, elenZ in Hfl, Hz. cbn [a_base a_off edenot] in Hfl, Hz.
  fold zbv in Hfl, Hz. rewrite u64_lit in Hfl, Hz by (unfold two64 in *; unfold RPN.SB in *; lia).
  set (Z0 := zbv + zk) in *.
  (* [comment removed for export] *)
  assert (ZZ : forall g, bz / 8 <= g <= (ez - 1) / 8 -> M (Z_to_bv 64 (RPN.SB + g)) = Some (Z_to_bv 8 0)).
  { intros g Hg.
    assert (Hg1 : Z0 - RPN.SB <= bz / 8) by (apply Z.div_le_lower_bound; lia).
    assert (Hg2 : (ez - 1) / 8 < Z0 - RPN.SB + zl) by (apply Z.div_lt_upper_bound; lia).
    replace (RPN.SB + g) with (zbv + zk + (RPN.SB + g - Z0)) by lia. apply Hz. lia. }
  split.
  - exists (Z_to_bv 8 0). split; [|split; [|split]].
    + intros g Hg. apply ZZ. lia.
    + apply rdn1_M0. apply ZZ. split; [apply Z.div_le_mono; lia | lia].
    + rewrite u8_lit0. lia.
    + left. apply ZZ. split; [apply Z.div_le_mono; lia | lia].
  - intros Hw. subst words. cbn [negb orb] in HW.
    intros a Ha1 Ha2. apply (words_of_cover E M k zb _ _ HK HW a).
    + fold zbv. unfold RPN.hull_lo.
      assert (Hg1 : Z0 - RPN.SB <= bz / 8) by (apply Z.div_le_lower_bound; lia).
      destruct (Z.leb_spec 3 (ealign k zb)) as [Hal|Hal].
      * destruct (ealign_sound SEGS E M k zb HK) as [_ [q Hq]]. fold zbv in Hq.
        assert (H8 : exists q', zbv = 8 * q').
        { exists (q * 2 ^ (ealign k zb - 3)). rewrite Hq.
          replace (ealign k zb) with ((ealign k zb - 3) + 3) at 1 by lia. rewrite Z.pow_add_r by lia. change (2 ^ 3) with 8. lia. }
        destruct H8 as [q' Hq'].
        pose proof (Z.div_mod zk 8 ltac:(lia)). pose proof (Z.mod_pos_bound zk 8 ltac:(lia)).
        pose proof (Z.div_mod (RPN.SB + bz / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (RPN.SB + bz / 8) 8 ltac:(lia)).
        assert (zbv / 8 * 8 = zbv) by (rewrite Hq', (Z.mul_comm 8 q'), Z.div_mul by lia; reflexivity).
        assert ((zbv + zk - zk mod 8) / 8 * 8 = zbv + zk - zk mod 8).
        { replace (zbv + zk - zk mod 8) with ((q' + zk / 8) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
        assert (Hm : (zbv + zk - zk mod 8) / 8 <= (RPN.SB + bz / 8) / 8) by (apply Z.div_le_mono; lia).
        lia.
      * lia.
    + fold zbv. assert (Hg2 : (ez - 1) / 8 < Z0 - RPN.SB + zl) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma u_and7 : forall (x : word), bv_unsigned (Sem.alu64 ALU_AND x (Z_to_bv 64 7)) = bv_unsigned x mod 8.
Proof.
  intros x. pose proof (u64_range x) as Hx. rewrite alu_and. unfold v_and. rewrite (zbv_u 7) by lia.
  change (Z.land (bv_unsigned x) 7) with (Z.land (bv_unsigned x) (Z.ones 3)). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  pose proof (Z.mod_pos_bound (bv_unsigned x) 8 ltac:(lia)). apply zbv_u. lia.
Qed.
Lemma and7_of_sound : forall E M k m ne,
  know_ok SEGS E M k -> RPN.and7_of k m ne = true -> bv_unsigned (edenot E m) = bv_unsigned (edenot E ne) mod 8.
Proof.
  intros E M k m ne HK H. unfold RPN.and7_of in H. apply orb_prop in H as [H | H].
  - apply expr_eqb_eq in H. subst m. rewrite (mkAnd_denot SEGS E M k _ _ HK). cbn [edenot]. apply u_and7.
  - destruct m as [ | | op ne' b | | | | | ]; try discriminate H. destruct op; try discriminate H.
    destruct b as [z | | | | | | | ]; try discriminate H.
    destruct (Z.eq_dec z 7) as [-> | Hz]; [| destruct z as [|p|p]; try discriminate H; destruct p as [p|p|]; try discriminate H;
        destruct p as [p|p|]; try discriminate H; destruct p as [p|p|]; try discriminate H; exfalso; apply Hz; reflexivity].
    apply andb_prop in H as [G1 G2].
    pose proof (lin_ge0_sound SEGS E M k _ _ HK G1) as L1. pose proof (lin_ge0_sound SEGS E M k _ _ HK G2) as L2.
    cbn [xt_den] in L1, L2. cbn [edenot]. rewrite u_and7. f_equal. lia.
Qed.
Definition vval (n : Z) : Z := if Z.eqb (n mod 8) 0 then 250 else n mod 8.
Lemma vval_range : forall n, 0 <= vval n <= 250 /\ vval n <> 0.
Proof. intros n. unfold vval. pose proof (Z.mod_pos_bound n 8 ltac:(lia)). destruct (Z.eqb_spec (n mod 8) 0); lia. Qed.
Lemma vshape0_sound : forall E M k v ne,
  know_ok SEGS E M k -> RPN.vshape0 k v ne = true -> bv_unsigned (edenot E v) = vval (bv_unsigned (edenot E ne)).
Proof.
  intros E M k v ne HK H. unfold RPN.vshape0 in H.
  repeat lazymatch type of H with
    | (_ && _)%bool = true => fail
    | (match ?x with _ => _ end) = true => destruct x; try discriminate H
    end.
  lazymatch type of H with ((expr_eqb ?a ?b) && _)%bool = true => idtac end.
  apply andb_prop in H as [He H7]. apply expr_eqb_eq in He. subst.
  pose proof (and7_of_sound E M k _ ne HK H7) as Hm.
  cbn [edenot]. rewrite u_add64, u_mul64, alu_sltu. unfold v_sltu, c_ltu, bv_ltu. rewrite Hm.
  rewrite (zbv_u 1), (zbv_u 250) by lia. unfold vval.
  pose proof (Z.mod_pos_bound (bv_unsigned (edenot E ne)) 8 ltac:(lia)) as Hr.
  destruct (Z.eqb_spec (bv_unsigned (edenot E ne) mod 8) 0) as [H0 | H0].
  - rewrite H0. cbn [Z.ltb]. match goal with |- context [bv_unsigned (Z_to_bv 64 1)] => rewrite (zbv_u 1) by lia | _ => idtac end. reflexivity.
  - destruct (Z.ltb_spec (bv_unsigned (edenot E ne) mod 8) 1); [lia|].
    match goal with |- context [bv_unsigned (Z_to_bv 64 0)] => rewrite (zbv_u 0) by lia | _ => idtac end.
    rewrite ?Z.mul_0_r. change (0 mod 2 ^ 64) with 0. rewrite ?Z.add_0_r. apply Z.mod_small. lia.
Qed.
Lemma vshape_sound : forall E M k v ne,
  know_ok SEGS E M k -> RPN.vshape k v ne = true -> bv_unsigned (edenot E v) = vval (bv_unsigned (edenot E ne)).
Proof.
  intros E M k v ne HK H. unfold RPN.vshape in H. apply orb_prop in H as [H | H]; [exact (vshape0_sound E M k v ne HK H)|].
  destruct v as [ | | | | | | sx lo n v' | ]; try discriminate H. destruct sx; [discriminate H|].
  destruct lo as [|lo]; [|discriminate H]. destruct n as [|[|n]]; try discriminate H.
  pose proof (vshape0_sound E M k v' ne HK H) as H0. pose proof (vval_range (bv_unsigned (edenot E ne))).
  cbn [edenot]. rewrite u_ext_zx0_small; [exact H0|]. change (2 ^ (8 * Z.of_nat 1)) with 256. lia.
Qed.

(* [comment removed for export] *)
Lemma sh_alloc_sound : forall E M k begE enE words kmax (bz ez : Z),
  know_ok SEGS E M k -> RPN.sh_alloc SEGS k begE enE words kmax = true ->
  bv_unsigned (edenot E begE) = bz -> bv_unsigned (edenot E enE) = ez ->
  bz + 1 <= ez /\ (exists kb, sh_facts M bz (ez - 1) kb kmax false) /\ (words = true -> words_facts M bz (ez - 1)).
Proof.
  intros E M k begE enE words kmax bz ez HK H Hbz Hez.
  pose proof (u64_range (edenot E begE)) as Rb. rewrite Hbz in Rb. pose proof (u64_range (edenot E enE)) as Re. rewrite Hez in Re.
  unfold RPN.sh_alloc in H.
  set (nE := esub enE begE) in H.
  set (shb := eadd (ELit RPN.SB) (mkSrl k begE 3)) in H.
  destruct (split_lit shb) as [lb lk] eqn:Hsl.
  set (zl := mkSrl k nE 3) in H.
  set (zl0 := match xlo k zl, xhi k zl with Some a, Some b => if Z.eqb a b then ELit a else zl | _, _ => zl end) in H.
  destruct (split_lit (eadd shb zl0)) as [hb hk] eqn:Hsh.
  destruct (xhi k nE) as [nhi|] eqn:Hnhi; [|discriminate].
  apply andb_prop in H as [H HP]. apply andb_prop in H as [H HW]. apply andb_prop in H as [H HKZ].
  apply andb_prop in H as [H HFL]. apply andb_prop in H as [HAL HGE].
  apply Z.leb_le in HAL.
  (* [comment removed for export] *)
  pose proof (lin_ge0_sound SEGS E M k _ _ HK HGE) as G. cbn [xt_den] in G. rewrite Hbz, Hez in G.
  set (n := ez - bz).
  assert (HnE : edenot E nE = Z_to_bv 64 n).
  { unfold nE, esub. rewrite mkAlu_denot, alu_sub. unfold v_sub. rewrite Hbz, Hez. reflexivity. }
  assert (HunE : bv_unsigned (edenot E nE) = n) by (rewrite HnE; apply u64_lit; lia).
  pose proof (xhi_sound SEGS E M k nE nhi HK Hnhi) as Hn. rewrite HunE in Hn.
  (* [comment removed for export] *)
  destruct (ealign_sound SEGS E M k begE HK) as [_ [q0 Hq0]]. rewrite Hbz in Hq0.
  assert (H8 : exists q, bz = 8 * q).
  { exists (q0 * 2 ^ (ealign k begE - 3)). rewrite Hq0.
    replace (ealign k begE) with ((ealign k begE - 3) + 3) at 1 by lia. rewrite Z.pow_add_r by lia. change (2 ^ 3) with 8. lia. }
  destruct H8 as [q Hq].
  assert (Hbz8 : bz / 8 = q) by (rewrite Hq, Z.mul_comm; apply Z.div_mul; lia).
  (* [comment removed for export] *)
  destruct (qc_sh_denot E M k begE bz HK ltac:(rewrite <- Hbz; symmetry; apply Z_to_bv_bv_unsigned) ltac:(lia)) as [Dshb Rshb].
  fold shb in Dshb.
  pose proof (w_split_lit_denot E _ lb lk Hsl) as Hslb. rewrite Dshb in Hslb.
  (* [comment removed for export] *)
  assert (Dzl : edenot E zl = Z_to_bv 64 (n / 8)).
  { unfold zl. rewrite (mkSrl_denot SEGS E M k nE 3 (Z_to_bv 64 3) HK ltac:(rewrite u64_lit by lia; reflexivity)).
    rewrite HnE, (srl3_div8 (Z_to_bv 64 n) (Z_to_bv 64 3)) by (rewrite u64_lit by lia; reflexivity).
    rewrite (zbv_u n) by lia. reflexivity. }
  assert (Hn8 : 0 <= n / 8 <= n) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (Dzl0 : edenot E zl0 = Z_to_bv 64 (n / 8)).
  { subst zl0. destruct (xlo k zl) as [za|] eqn:Hza; [|exact Dzl]. destruct (xhi k zl) as [zb|] eqn:Hzb; [|exact Dzl].
    destruct (Z.eqb_spec za zb) as [Eab|]; [|exact Dzl]. subst zb.
    pose proof (xlo_sound SEGS E M k zl za HK Hza) as X1. pose proof (xhi_sound SEGS E M k zl za HK Hzb) as X2.
    rewrite Dzl, u64_lit in X1, X2 by lia. cbn [edenot]. f_equal. lia. }
  destruct (w_flat_x_sound SEGS E M k lb lk _ HK HFL) as (Llo & Lhi & _).
  rewrite eaddz_denot, Dzl, alu_add, v_add_zbv_mod, u64_lit in Lhi by lia.
  set (Hs := estart E (SA lb lk)) in *.
  assert (HHs : Hs = RPN.SB + q).
  { apply (f_equal bv_unsigned) in Hslb. unfold Hs, estart in Llo, Lhi |- *. cbn [a_base a_off] in Llo, Lhi |- *.
    rewrite !u64_lit in Hslb by lia. lia. }
  (* [comment removed for export] *)
  assert (ZZ : forall g, q <= g < q + n / 8 -> M (Z_to_bv 64 (RPN.SB + g)) = Some (Z_to_bv 8 0)).
  { assert (KZ : zl0 = ELit 0 \/ kzero_x k k lb lk zl0 = true).
    { revert HKZ. generalize zl0 as zz. intros zz HKZ.
      destruct zz as [[|p|p]| | | | | | | ]; try (right; exact HKZ); left; reflexivity. }
    destruct KZ as [Ez | HKZ'].
    - rewrite Ez in Dzl0. cbn [edenot] in Dzl0. apply (f_equal bv_unsigned) in Dzl0. rewrite !u64_lit in Dzl0 by lia.
      intros g Hg. exfalso. lia.
    - destruct (kzero_x_sound SEGS E M k k lb lk zl0 HK HK HKZ') as (Zb & _ & _).
      unfold elenZ in Zb. rewrite Dzl0, u64_lit in Zb by lia. fold Hs in Zb. rewrite HHs in Zb.
      intros g Hg. replace (RPN.SB + g) with (RPN.SB + q + (g - q)) by lia. apply Zb. lia. }
  (* [comment removed for export] *)
  pose proof (w_split_lit_denot E _ hb hk Hsh) as HPw.
  unfold eadd at 1 in HPw. rewrite mkAlu_denot, Dshb, Dzl0, alu_add, v_add_zbv_mod in HPw.
  (* [comment removed for export] *)
  assert (Hlast : (ez - 1) / 8 = q + (n - 1) / 8).
  { replace (ez - 1) with (q * 8 + (n - 1)) by lia. rewrite Z.div_add_l by lia. reflexivity. }
  pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Hm8. pose proof (Z.div_mod n 8 ltac:(lia)) as Hdm.
  (* [comment removed for export] *)
  assert (PBYTE : forall v0 hs, flat_x k hb hk (ELit 1) = true -> know_lookup SEGS k hb hk 1 false [] [] = LHit v0 [] hs ->
            exists kb : byte, rdn SEGS M (Z_to_bv 64 (RPN.SB + q + n / 8)) 1 = Some [kb] /\ bv_unsigned (edenot E v0) = bv_unsigned kb).
  { intros v0 hs Hflp HL1.
    destruct (w_flat_x_sound SEGS E M k hb hk (ELit 1) HK Hflp) as (Plo & Phi & _).
    set (P := estart E (SA hb hk)) in *.
    replace (bv_unsigned (edenot E (ELit 1))) with 1 in Phi by (cbn [edenot]; rewrite u64_lit by lia; reflexivity).
    assert (HPP : P = RPN.SB + q + n / 8).
    { apply (f_equal bv_unsigned) in HPw. unfold P, estart in Plo, Phi |- *. cbn [a_base a_off] in Plo, Phi |- *.
      rewrite !u64_lit in HPw by lia. lia. }
    pose proof (know_lookup_sound SEGS E M k hb hk 1 false [] [] HK ltac:(lia) ltac:(lia)) as XL.
    rewrite HL1 in XL. destruct (XL ltac:(constructor) ltac:(unfold flat; fold P; lia)) as (bs3 & Hrd3 & Hlen3 & Hv3). clear XL.
    rewrite adenot_SA in Hrd3. fold P in Hrd3. rewrite HPP in Hrd3.
    destruct bs3 as [|kb [|]]; [discriminate Hlen3 | | discriminate Hlen3].
    cbn [extz] in Hv3. rewrite bytes_le_single in Hv3. pose proof (u8_range kb) as Hkr.
    exists kb. split; [exact Hrd3|]. rewrite <- Hv3. apply u64_lit. lia. }
  (* [comment removed for export] *)
  assert (CASE0 : n mod 8 = 0 -> exists kb, sh_facts M bz (ez - 1) kb kmax false).
  { intros Hm0.
    assert (Hd : (n - 1) / 8 = n / 8 - 1).
    { replace (n - 1) with ((n / 8 - 1) * 8 + 7) by lia. rewrite Z.div_add_l by lia. change (7 / 8) with 0. lia. }
    exists (Z_to_bv 8 0). split; [|split; [|split]].
    * intros g Hg. apply ZZ. lia.
    * apply rdn1_M0. apply ZZ. lia.
    * rewrite u8_lit0. lia.
    * left. apply ZZ. lia. }
  assert (CASE1 : forall kb : byte, 1 <= n mod 8 -> rdn SEGS M (Z_to_bv 64 (RPN.SB + q + n / 8)) 1 = Some [kb] ->
            n mod 8 <= bv_unsigned kb <= Z.max 0 kmax -> exists kb', sh_facts M bz (ez - 1) kb' kmax false).
  { intros kb H1 Hrd Hkb.
    assert (Hd : (n - 1) / 8 = n / 8).
    { replace (n - 1) with (n / 8 * 8 + (n mod 8 - 1)) by lia. rewrite Z.div_add_l by lia. rewrite (Z.div_small (n mod 8 - 1)) by lia. lia. }
    exists kb. split; [|split; [|split]].
    * intros g Hg. apply ZZ. lia.
    * rewrite Hlast, Hd. replace (RPN.SB + (q + n / 8)) with (RPN.SB + q + n / 8) by lia. exact Hrd.
    * lia.
    * right; right.
      assert (Hmod : (ez - 1) mod 8 = n mod 8 - 1).
      { replace (ez - 1) with ((n mod 8 - 1) + (q + n / 8) * 8) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
      lia. }
  (* [comment removed for export] *)
  destruct (erange k (mkAnd k nE (ELit 7))) as [[rlo rhi]|] eqn:Her; [|discriminate].
  pose proof (erange_sound SEGS E M k _ rlo rhi HK Her) as Hr.
  rewrite (mkAnd_denot SEGS E M k _ _ HK) in Hr. cbn [edenot] in Hr. rewrite u_and7, HunE in Hr.
  split; [lia|]. split.
  - apply orb_prop in HP as [HP | HU]; [apply orb_prop in HP as [H0 | HP]|].
    + (* [comment removed for export] *)
      apply Z.eqb_eq in H0. apply CASE0. lia.
    + (* [comment removed for export] *)
      apply andb_prop in HP as [HP HLK]. apply andb_prop in HP as [H1 Hflp]. apply Z.leb_le in H1.
      destruct (know_lookup SEGS k hb hk 1 false [] []) as [v0 scs hs|scs hs|] eqn:HL1; try discriminate HLK.
      destruct scs; [|discriminate HLK].
      destruct (PBYTE v0 hs Hflp eq_refl) as (kb & Hrd3 & Hvk).
      apply (CASE1 kb); [lia | exact Hrd3 |].
      apply orb_prop in HLK as [HVS | HLK].
      * (* [comment removed for export] *)
        apply andb_prop in HVS as [HVS Hk7]. apply Z.leb_le in Hk7.
        pose proof (vshape_sound E M k _ nE HK HVS) as XV. rewrite (extK_denot SEGS E M k v0 HK), HunE in XV.
        unfold vval in XV. destruct (Z.eqb_spec (n mod 8) 0); lia.
      * destruct (erange k (extK k v0)) as [[lo hi]|] eqn:Her'; [|discriminate HLK].
        apply andb_prop in HLK as [HLK Hval]. apply andb_prop in HLK as [Hlo0 Hhik].
        apply Z.leb_le in Hlo0. apply Z.leb_le in Hhik.
        pose proof (erange_sound SEGS E M k _ lo hi HK Her') as Hv. rewrite (extK_denot SEGS E M k v0 HK) in Hv.
        pose proof (lin_ge0_sound SEGS E M k _ _ HK Hval) as XG. cbn [xt_den] in XG.
        rewrite (extK_denot SEGS E M k v0 HK) in XG.
        rewrite (mkAnd_denot SEGS E M k _ _ HK) in XG. cbn [edenot] in XG. rewrite u_and7, HunE in XG. lia.
    + (* [comment removed for export] *)
      apply andb_prop in HU as [HU HVS]. apply andb_prop in HU as [Hflp Hk7]. apply Z.leb_le in Hk7.
      destruct (know_lookup SEGS k hb hk 1 false [] []) as [v0 scs hs|scs hs|] eqn:HL1; try discriminate HVS.
      destruct scs; [|discriminate HVS].
      destruct (Z.eq_dec (n mod 8) 0) as [Hm0 | Hm1]; [apply CASE0; exact Hm0|].
      destruct (PBYTE v0 hs Hflp eq_refl) as (kb & Hrd3 & Hvk).
      apply (CASE1 kb); [lia | exact Hrd3 |].
      pose proof (vshape_sound E M k _ nE HK HVS) as XV. rewrite (extK_denot SEGS E M k v0 HK), HunE in XV.
      unfold vval in XV. destruct (Z.eqb_spec (n mod 8) 0); lia.
  - clear PBYTE CASE0 CASE1 Hr Her HP. intros Hwd. subst words. cbn [negb orb] in HW.
    intros a Ha1 Ha2. apply (words_of_cover E M k lb _ _ HK HW a).
    + unfold RPN.hull_lo. unfold Hs, estart in HHs. cbn [a_base a_off] in HHs.
      set (lbv := bv_unsigned (edenot E lb)) in *.
      rewrite Hbz8 in Ha1.
      destruct (Z.leb_spec 3 (ealign k lb)) as [Hal|Hal]; [|lia].
      destruct (ealign_sound SEGS E M k lb HK) as [_ [q1 Hq1]]. fold lbv in Hq1.
      assert (H8 : exists q', lbv = 8 * q').
      { exists (q1 * 2 ^ (ealign k lb - 3)). rewrite Hq1.
        replace (ealign k lb) with ((ealign k lb - 3) + 3) at 1 by lia. rewrite Z.pow_add_r by lia. change (2 ^ 3) with 8. lia. }
      destruct H8 as [q' Hq'].
      pose proof (Z.div_mod lk 8 ltac:(lia)). pose proof (Z.mod_pos_bound lk 8 ltac:(lia)).
      pose proof (Z.div_mod (RPN.SB + q) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (RPN.SB + q) 8 ltac:(lia)).
      assert ((lbv + lk - lk mod 8) / 8 * 8 = lbv + lk - lk mod 8).
      { replace (lbv + lk - lk mod 8) with ((q' + lk / 8) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
      assert (Hm : (lbv + lk - lk mod 8) / 8 <= (RPN.SB + q) / 8) by (apply Z.div_le_mono; lia).
      lia.
    + unfold Hs, estart in HHs. cbn [a_base a_off] in HHs. rewrite Hlast in Ha2.
      assert ((n - 1) / 8 <= nhi / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

Theorem node_rpoison_sound :
  APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (RPN.node_rpoison SEGS nx0 T).
Proof.
  intros cs cs' E R FULL model TT HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := Mr A argH E cs model FULL) in *.
  rewrite RPN.node_rpoison_eq in Hn. (* [comment removed for export] *) unfold RPN.node_rpoison_ref in Hn.
  destruct (Z.eqb (pc cs) (RPN.rp_entry T)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
  destruct (split_lit (eaddz (reg cs 2) (-72))) as [qb qk] eqn:Hsq.
  destruct (xlo (kn cs) (reg cs 11)) as [nlo|] eqn:Hnlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 11)) as [nhi|] eqn:Hnhi; [|discriminate].
  destruct (xlo (kn cs) (reg cs 10)) as [blo|] eqn:Hblo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [bhi|] eqn:Hbhi; [|discriminate].
  destruct (xlo (kn cs) (reg cs 2)) as [splo|] eqn:Hsplo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 2)) as [sphi|] eqn:Hsphi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Lhi]. apply andb_prop in Hcond as [Hcond Lsb].
  apply andb_prop in Hcond as [Hcond Icm2]. apply andb_prop in Hcond as [Hcond Icm1].
  apply andb_prop in Hcond as [Hcond Ighi]. apply andb_prop in Hcond as [Hcond Igm2].
  apply andb_prop in Hcond as [Hcond Igm1]. apply andb_prop in Hcond as [Hcond Igsb].
  apply andb_prop in Hcond as [Hcond Hflq]. apply andb_prop in Hcond as [Hcond Hwr].
  apply andb_prop in Hcond as [Hcond B8]. apply andb_prop in Hcond as [Hcond B7]. apply andb_prop in Hcond as [Hcond B6]. apply andb_prop in Hcond as [Hcond B5].
  apply andb_prop in Hcond as [Hcond B4]. apply andb_prop in Hcond as [Hcond B3]. apply andb_prop in Hcond as [Hcond B2]. apply andb_prop in Hcond as [Hcond B1].
  apply andb_prop in Hcond as [Hcond P8]. apply andb_prop in Hcond as [Hcond P7]. apply andb_prop in Hcond as [Hcond P6]. apply andb_prop in Hcond as [Hcond P5].
  apply andb_prop in Hcond as [Hcond P4]. apply andb_prop in Hcond as [Hcond P3]. apply andb_prop in Hcond as [Hcond P2]. apply andb_prop in Hcond as [Hcond P1].
  apply andb_prop in Hcond as [Hcond Hdisj]. apply andb_prop in Hcond as [Hcond Hsphi']. apply andb_prop in Hcond as [Hcond Hsplo'].
  apply andb_prop in Hcond as [Hcond Hshc]. apply andb_prop in Hcond as [Hcond Hrng].
  apply andb_prop in Hcond as [Hn16 Hn40].
  apply Z.leb_le in Hn16. apply Z.leb_le in Hn40. apply Z.leb_le in Hsplo'. apply Z.ltb_lt in Hsphi'. apply Z.ltb_lt in Hdisj.
  apply Z.leb_le in P1. apply Z.leb_le in P2. apply Z.leb_le in P3. apply Z.leb_le in P4. apply Z.leb_le in P5. apply Z.leb_le in P6. apply Z.leb_le in P7. apply Z.leb_le in P8.
  apply Z.leb_le in B1. apply Z.leb_le in B2. apply Z.leb_le in B3. apply Z.leb_le in B4. apply Z.leb_le in B5. apply Z.leb_le in B6. apply Z.leb_le in B7. apply Z.leb_le in B8.
  unfold two64 in Hsphi'.
  (* [comment removed for export] *)
  destruct (ret_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 2 HC ltac:(lia)) as R2.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 11 HC ltac:(lia)) as R11.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi2.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hblo) as Hblo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hbhi) as Hbhi2.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hsplo) as Hsplo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hsphi) as Hsphi2.
  set (begw := edenot E (reg cs 10)) in *. set (spw := edenot E (reg cs 2)) in *. set (nw := edenot E (reg cs 11)) in *.
  set (n := bv_unsigned nw) in *. set (usp := bv_unsigned spw) in *. set (beg := bv_unsigned begw) in *.
  pose proof (u64_range nw) as Hnr. fold n in Hnr. pose proof (u64_range begw) as Hbr. fold beg in Hbr.
  pose proof (u64_range spw) as Hsr. fold usp in Hsr.
  assert (HnwN : Z_to_bv 64 n = nw) by (apply Z_to_bv_bv_unsigned).
  assert (HspW : Z_to_bv 64 usp = spw) by (apply Z_to_bv_bv_unsigned).
  assert (HbgW : Z_to_bv 64 beg = begw) by (apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  pose proof (w_split_lit_denot E _ qb qk Hsq) as Hq.
  unfold eaddz in Hq. rewrite mkAlu_denot in Hq. cbn [edenot] in Hq. fold spw in Hq.
  destruct (kwritable_sound SEGS E M (kn cs) (kn cs) qb qk 72 HKN HKN Hwr ltac:(lia)) as (Qst & Qlo & Qhi).
  set (Q := estart E (SA qb qk)) in *.
  assert (HQ : Q = usp - 72).
  { apply (f_equal bv_unsigned) in Hq. rewrite (u_spw_sub72 spw) in Hq by lia. fold usp in Hq.
    rewrite u_lit64 in Hq. unfold two64 in Hq. rewrite (Z.mod_small Q) in Hq by lia. lia. }
  assert (Hstk : forall a, usp - 72 <= a < usp -> store_ok SEGS M (Z_to_bv 64 a) 1 = true).
  { intros a Ha. apply store_ok_of_all; [cbn; rewrite u64_lit by lia; lia|].
    intros x Hx. eapply (store_ok_all SEGS M 72 (Z_to_bv 64 Q)); [rewrite u64_lit by lia; cbn; lia | exact Qst |].
    rewrite u64_lit in Hx |- * by lia. cbn in Hx |- *. lia. }
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (Hrng2 : beg + n <= RPN.kLowEnd \/ (RPN.kHighBeg <= beg /\ beg + n <= RPN.kHighEnd)).
  { apply orb_prop in Hrng as [Hr|Hr].
    - left. apply orb_prop in Hr as [Hr|Hr]; [apply Z.leb_le in Hr; lia|].
      pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN Hr) as G. cbn [xt_den edenot] in G. fold begw nw in G. fold beg n in G.
      rewrite u64_lit in G by (unfold RPN.kLowEnd; lia). lia.
    - apply andb_prop in Hr as [Hr1 Hr2]. apply Z.leb_le in Hr1. right. split; [lia|].
      apply orb_prop in Hr2 as [Hr2|Hr2]; [apply Z.leb_le in Hr2; lia|].
      pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN Hr2) as G. cbn [xt_den edenot] in G. fold begw nw in G. fold beg n in G.
      rewrite u64_lit in G by (unfold RPN.kHighEnd; lia). lia. }
  assert (Hb64 : beg + n < 2 ^ 64).
  { unfold RPN.kLowEnd, RPN.kHighBeg, RPN.kHighEnd in *. destruct Hrng2 as [Hr|[_ Hr]]; lia. }
  assert (Hen : edenot E (eadd (reg cs 10) (reg cs 11)) = Z_to_bv 64 (beg + n)).
  { unfold eadd. rewrite mkAlu_denot, alu_add. fold begw nw. unfold v_add. fold beg n. reflexivity. }
  assert (Huen : bv_unsigned (edenot E (eadd (reg cs 10) (reg cs 11))) = beg + n) by (rewrite Hen; apply u64_lit; lia).
  assert (He1 : edenot E (eaddz (eadd (reg cs 10) (reg cs 11)) (-1)) = Z_to_bv 64 (beg + n - 1)).
  { rewrite eaddz_denot, Hen, alu_add, v_add_zbv_mod. f_equal; lia. }
  assert (SH : exists kb, sh_facts M beg (beg + n - 1) kb 7 false).
  { lazymatch type of Hshc with (if ?a then true else if ?b then true else ?c) = true =>
      assert (Hshc' : ((a || b) || c)%bool = true) by (destruct a; [reflexivity|]; destruct b; [reflexivity|]; exact Hshc) end.
    clear Hshc. apply orb_prop in Hshc' as [Hshc | HCV]; [apply orb_prop in Hshc as [HA | HB]|].
    - exact (sh_local_sound E M (kn cs) (reg cs 10) _ beg (beg + n - 1) 7 false HKN (eq_sym HbgW) He1 ltac:(lia) ltac:(lia) HA).
    - destruct (sh_alloc_sound E M (kn cs) (reg cs 10) _ false 7 beg (beg + n) HKN HB eq_refl Huen) as (_ & X & _). exact X.
    - destruct (qc_cover_sound E M (kn cs) (reg cs 10) _ false beg (beg + n) 7 false HKN HCV eq_refl Huen ltac:(lia)) as [X _]. exact X. }
  destruct SH as (kb & HzS & HkS & Hkmax & Hkok).
  (* [comment removed for export] *)
  pose proof (img8_sound E M (kn cs) _ _ HKN Igsb (ri_gsb _ _ IMG)) as C1.
  pose proof (lit_cell_sound E M (kn cs) _ _ HKN B5 Lsb) as C2.
  pose proof (img8_sound E M (kn cs) _ _ HKN Igm1 (ri_gm1 _ _ IMG)) as C3.
  pose proof (img8_sound E M (kn cs) _ _ HKN Icm1 (ri_cm1 _ _ IMG)) as C4.
  pose proof (img8_sound E M (kn cs) _ _ HKN Igm2 (ri_gm2 _ _ IMG)) as C5.
  pose proof (img8_sound E M (kn cs) _ _ HKN Icm2 (ri_cm2 _ _ IMG)) as C6.
  pose proof (img8_sound E M (kn cs) _ _ HKN Ighi (ri_ghi _ _ IMG)) as C7.
  pose proof (lit_cell_sound E M (kn cs) _ _ HKN B8 Lhi) as C8.

  (* [comment removed for export] *)
  assert (Hkok' : M (Z_to_bv 64 (RPN.SB + (beg + n - 1) / 8)) = Some (Z_to_bv 8 0) \/ (beg + n - 1) mod 8 < bv_unsigned kb < 8).
  { destruct Hkok as [H0 | [[H0 _] | H0]]; [left; exact H0 | discriminate H0 | right; lia]. }
  destruct (SPEC M beg n usp R (Z_to_bv 64 ret) kb ltac:(lia) ltac:(lia) Hrng2 ltac:(lia) ltac:(lia) HzS HkS Hkok' Hstk
              C1 C2 C3 C4 C5 C6 C7 C8 Hrok R1 ltac:(rewrite HspW; exact R2) ltac:(rewrite HbgW; exact R10) ltac:(rewrite HnwN; exact R11))
    as (regs' & M' & Hms & Hkept & Ha0 & Hout & Hgr).
  eapply (call_node_sound SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH argH_high argH_agree SINV_frame SINV_agree NX0_sp FS0
            cs cs' E R FULL model TT ret (Some (ELit 0)) _ regs' M' HC Hn).
  - rewrite Hpc. exact Hms.
  - exact Hkept.
  - cbn [edenot]. exact Ha0.
  - eapply w_know_ok_havoc; [exact HKN | | exact Hgr].
    intros x Hx. change (estart E (SA qb qk)) with Q in Hx.
    replace (elenZ E (ELit 72)) with 72 in Hx by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
    apply Hout. lia.
  - exact Hk.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma v_addi_as_add : forall (x : word) i, v_addi x i = Sem.alu64 ALU_ADD x (Z_to_bv 64 i).
Proof.
  intros x i. rewrite alu_add. unfold v_add, v_addi. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma nth_rc_regs : forall sr e1 e2 e3 e20 i,
  nth i (RPN.rc_regs sr e1 e2 e3 e20) (ELit 0) =
  if Nat.eqb i 20 then e20 else if Nat.eqb i 15 then ELit 0 else if Nat.eqb i 14 then ELit 0
  else if Nat.eqb i 13 then e3 else if Nat.eqb i 12 then e2 else if Nat.eqb i 11 then e1 else nth i sr (ELit 0).
Proof.
  intros. unfold RPN.rc_regs.
  rewrite (nth_sr_upd 20). destruct (Nat.eqb i 20); [reflexivity|].
  rewrite (nth_sr_upd 15). destruct (Nat.eqb i 15); [reflexivity|].
  rewrite (nth_sr_upd 14). destruct (Nat.eqb i 14); [reflexivity|].
  rewrite (nth_sr_upd 13). destruct (Nat.eqb i 13); [reflexivity|].
  rewrite (nth_sr_upd 12). destruct (Nat.eqb i 12); [reflexivity|].
  rewrite (nth_sr_upd 11). reflexivity.
Qed.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Theorem node_readcheck_sound :
  APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (RPN.node_readcheck SEGS nx0 T).
Proof.
  intros cs cs' E R FULL model TT HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := Mr A argH E cs model FULL) in *.
  rewrite RPN.node_readcheck_eq in Hn. (* [comment removed for export] *) unfold RPN.node_readcheck_ref in Hn.
  destruct (Z.eqb (pc cs) (RPN.rc_entry T)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (split_lit (reg cs 9)) as [bb bk] eqn:Hsb.
  destruct (split_lit (eadd (ELit (RPN.SB + bk / 8 - (RPN.SB + bk / 8) mod 8)) (mkSrl (kn cs) bb 3))) as [hb hk] eqn:Hsh.
  destruct (xlo (kn cs) (reg cs 10)) as [rlo|] eqn:Hrlo; [|discriminate].
  destruct (xhi (kn cs) (reg cs 10)) as [rhi|] eqn:Hrhi; [|discriminate].
  destruct (xhi (kn cs) (reg cs 9)) as [dhi|] eqn:Hdhi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Lsb]. apply andb_prop in Hcond as [Hcond Igsb].
  apply andb_prop in Hcond as [Hcond B2]. apply andb_prop in Hcond as [Hcond B1].
  apply andb_prop in Hcond as [Hcond Hkz]. apply andb_prop in Hcond as [Hcond Hflh].
  apply andb_prop in Hcond as [Hcond Hfresh]. apply andb_prop in Hcond as [Hcond Hflb]. apply andb_prop in Hcond as [Hcond Hal].
  apply andb_prop in Hcond as [Hcond Hd64]. apply andb_prop in Hcond as [Hr1 Hr64].
  apply Z.leb_le in Hr1. apply Z.leb_le in Hr64. apply Z.ltb_lt in Hd64. apply Z.leb_le in Hal. apply Z.leb_le in B1. apply Z.leb_le in B2.
  unfold two64 in Hd64. injection Hn as <-.
  (* [comment removed for export] *)
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 9 HC ltac:(lia)) as R9.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 HC ltac:(lia)) as R10.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 8 HC ltac:(lia)) as R8.
  replace (Z_to_bv 5 (Z.of_nat 8)) with (8%bv : bv 5) in R8 by (apply bv_eq; reflexivity).
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hrlo) as Hrlo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hrhi) as Hrhi2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hdhi) as Hdhi2.
  set (dw := edenot E (reg cs 9)) in *. set (rw := edenot E (reg cs 10)) in *.
  set (buf := bv_unsigned dw) in *. set (res := bv_unsigned rw) in *.
  pose proof (u64_range dw) as Hbr. fold buf in Hbr. pose proof (u64_range rw) as Hrr. fold res in Hrr.
  assert (HdwB : Z_to_bv 64 buf = dw) by (apply Z_to_bv_bv_unsigned).
  assert (HrwR : Z_to_bv 64 res = rw) by (apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  pose proof (w_split_lit_denot E (reg cs 9) bb bk Hsb) as Hbeg. fold dw in Hbeg.
  destruct (flat_x_sound SEGS E M (kn cs) bb bk (ELit 1) HKN Hflb) as (Blo & Bhi & _).
  set (bbu := bv_unsigned (edenot E bb)) in *.
  replace (bv_unsigned (edenot E (ELit 1))) with 1 in Bhi by (cbn [edenot]; rewrite u64_lit by lia; reflexivity).
  assert (HuB : buf = bbu + bk).
  { unfold buf. rewrite Hbeg. unfold estart in Blo, Bhi. cbn [a_base a_off] in Blo, Bhi. fold bbu in Blo, Bhi. apply u64_lit. lia. }
  destruct (ealign_sound SEGS E M (kn cs) bb HKN) as [Hea1 Hea2]. fold bbu in Hea2.
  assert (Hal64 : exists q, bbu = 64 * q).
  { destruct Hea2 as [q Hq8]. exists (q * 2 ^ (ealign (kn cs) bb - 6)). rewrite Hq8.
    replace (ealign (kn cs) bb) with ((ealign (kn cs) bb - 6) + 6) at 1 by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 6) with 64. lia. }
  destruct Hal64 as [q Hq64].
  assert (Hdiv4 : bbu / 8 = 8 * q) by (rewrite Hq64; replace (64 * q) with (8 * q * 8) by lia; apply Z.div_mul; lia).
  assert (Hdiv1 : buf / 8 = 8 * q + bk / 8).
  { rewrite HuB, Hq64. replace (64 * q + bk) with (8 * q * 8 + bk) by lia. rewrite Z.div_add_l by lia. reflexivity. }
  (* [comment removed for export] *)
  pose proof (w_split_lit_denot E _ hb hk Hsh) as Hsa.
  unfold eadd in Hsa. rewrite mkAlu_denot in Hsa.
  rewrite (mkSrl_denot SEGS E M (kn cs) bb 3 (Z_to_bv 64 3) HKN ltac:(rewrite u64_lit by lia; reflexivity)) in Hsa.
  rewrite (srl3_div8 (edenot E bb) (Z_to_bv 64 3)) in Hsa by (rewrite u64_lit by lia; reflexivity). fold bbu in Hsa.
  cbn [edenot] in Hsa. rewrite alu_add in Hsa. unfold v_add in Hsa.
  destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) hb hk (ELit 16) HKN HKN Hkz) as (Zb & Hlo' & Hhi').
  set (H := estart E (SA hb hk)) in *.
  change (bv_unsigned (edenot E hb) + hk) with H in Hsa.
  replace (elenZ E (ELit 16)) with 16 in Zb, Hhi' by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
  pose proof (Z.mod_pos_bound (RPN.SB + bk / 8) 8 ltac:(lia)) as Hm.
  assert (HH : H = (RPN.SB + buf / 8) / 8 * 8).
  { apply (f_equal bv_unsigned) in Hsa. rewrite Hdiv4 in Hsa.
    rewrite !u_lit64 in Hsa. unfold two64 in Hsa. rewrite Hdiv1. unfold RPN.SB in *.
    rewrite <- Z.add_mod in Hsa by lia.
    rewrite (Z.mod_small (2147450880 + bk / 8 - (2147450880 + bk / 8) mod 8 + 8 * q)) in Hsa by lia.
    rewrite (Z.mod_small H) in Hsa by lia. lia. }
  assert (Hz : forall j, 0 <= j < 16 -> M (Z_to_bv 64 ((RPN.SB + buf / 8) / 8 * 8 + j)) = Some (Z_to_bv 8 0)).
  { intros j Hj. rewrite <- HH. apply Zb. lia. }
  (* [comment removed for export] *)
  pose proof (img8_sound E M (kn cs) _ _ HKN Igsb (ri_gsb _ _ IMG)) as C1.
  pose proof (lit_cell_sound E M (kn cs) _ _ HKN B2 Lsb) as C2.
  (* [comment removed for export] *)
  destruct (RSPEC M (seg_rom SEGS) buf res R ltac:(lia) ltac:(lia) ltac:(lia) C1 C2 Hz
              ltac:(rewrite HdwB; exact R9) ltac:(rewrite HrwR; exact R10))
    as (regs' & Hms & P11 & P12 & P13 & P14 & P15 & P20 & Pother).
  lazymatch type of Hk with context [mk_ss _ ?sr _ _] =>
    eapply (call_core SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH argH_high argH_agree SINV_frame SINV_agree NX0_sp FS0
              cs E E R FULL model TT (RPN.rc_exit T) sr (kn cs) (nxt cs) regs' M HC Hfresh (env_agree_refl _ E))
  end.
  - rewrite Hpc. exact Hms.
  - (* [comment removed for export] *)
    apply regs_ok_pointwise. intros r Hr0.
    pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) as HR.
    assert (HRr : forall r' : bv 5, r' <> 0%bv -> getr R r' = edenot E (nth (ridx r') (s_regs (a_ss cs)) (ELit 0))).
    { intros r' Hr'. rewrite (HR r'). unfold sr_get. destruct (bv_eqb r' 0%bv) eqn:E0; [|reflexivity].
      exfalso. apply Hr'. apply bv_eq. unfold bv_eqb in E0. apply Z.eqb_eq in E0. exact E0. }
    cbn [s_regs mk_ss]. rewrite nth_rc_regs.
    assert (RX : forall n (rb : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rb -> Nat.eqb (ridx r) n = true -> r = rb).
    { intros n rb Hn Hrb E1. apply Nat.eqb_eq in E1. rewrite (reg_of_ridx r n E1). apply bv_eq.
      rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. exact Hrb. }
    destruct (Nat.eqb (ridx r) 20) eqn:E20; [apply (RX 20%nat 20%bv ltac:(lia) eq_refl) in E20; subst r|].
    { rewrite P20, R8. unfold eaddz. do 2 rewrite mkAlu_denot. cbn [edenot]. do 2 rewrite v_addi_as_add. reflexivity. }
    destruct (Nat.eqb (ridx r) 15) eqn:E15; [apply (RX 15%nat 15%bv ltac:(lia) eq_refl) in E15; subst r; rewrite P15; reflexivity|].
    destruct (Nat.eqb (ridx r) 14) eqn:E14; [apply (RX 14%nat 14%bv ltac:(lia) eq_refl) in E14; subst r; rewrite P14; reflexivity|].
    destruct (Nat.eqb (ridx r) 13) eqn:E13; [apply (RX 13%nat 13%bv ltac:(lia) eq_refl) in E13; subst r|].
    { rewrite P13. unfold eaddz, eadd. do 2 rewrite mkAlu_denot. cbn [edenot]. fold dw rw. rewrite <- HdwB, <- HrwR.
      rewrite <- v_addi_as_add. rewrite alu_add. rewrite v_add_zbv by lia. rewrite v_addi_zbv by lia. first [reflexivity | f_equal; lia]. }
    destruct (Nat.eqb (ridx r) 12) eqn:E12; [apply (RX 12%nat 12%bv ltac:(lia) eq_refl) in E12; subst r|].
    { rewrite P12. unfold eadd, eaddz. rewrite mkAlu_denot.
      rewrite (mkSrl_denot SEGS E M (kn cs) _ 3 (Z_to_bv 64 3) HKN ltac:(rewrite u64_lit by lia; reflexivity)).
      do 2 rewrite mkAlu_denot. cbn [edenot]. fold dw rw. rewrite <- HdwB, <- HrwR.
      rewrite <- (v_addi_as_add (Sem.alu64 ALU_ADD (Z_to_bv 64 buf) (Z_to_bv 64 res))).
      rewrite (alu_add (Z_to_bv 64 buf)). rewrite (v_add_zbv buf res) by lia. rewrite v_addi_zbv by lia.
      replace (buf + res + -1) with (buf + res - 1) by lia.
      rewrite (srl3_div8 _ (Z_to_bv 64 3)) by (rewrite u64_lit by lia; reflexivity). rewrite zbv_u by lia.
      rewrite alu_add. rewrite v_add_zbv_mod. reflexivity. }
    destruct (Nat.eqb (ridx r) 11) eqn:E11; [apply (RX 11%nat 11%bv ltac:(lia) eq_refl) in E11; subst r|].
    { rewrite P11. unfold eadd. rewrite mkAlu_denot.
      rewrite (mkSrl_denot SEGS E M (kn cs) bb 3 (Z_to_bv 64 3) HKN ltac:(rewrite u64_lit by lia; reflexivity)).
      rewrite (srl3_div8 (edenot E bb) (Z_to_bv 64 3)) by (rewrite u64_lit by lia; reflexivity). fold bbu. rewrite Hdiv4.
      cbn [edenot]. rewrite alu_add, v_add_zbv_mod. rewrite Hdiv1. apply (f_equal (Z_to_bv 64)). lia. }
    rewrite Pother; [apply HRr; exact Hr0
                   | intros ->; cbv in E11; discriminate E11 | intros ->; cbv in E12; discriminate E12
                   | intros ->; cbv in E13; discriminate E13 | intros ->; cbv in E14; discriminate E14
                   | intros ->; cbv in E15; discriminate E15 | intros ->; cbv in E20; discriminate E20 ].
  - exact HKN.
  - intros R' FULL' model' HC' Hfs'. apply (Hk E R' FULL' model' (conj (env_agree_refl _ E) (env_agree_refl _ E)) HC' Hfs').
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma qc_word_sound : forall E M k x b kk (xv : Z),
  know_ok SEGS E M k -> RPN.qc_word k x = (b, kk) -> edenot E x = Z_to_bv 64 xv -> 0 <= xv < 2 ^ 64 ->
  flat_x k b kk (ELit 8) = true ->
  estart E (SA b kk) = (RPN.SB + xv / 8) / 8 * 8 /\ 0 <= (RPN.SB + xv / 8) / 8 * 8 /\ (RPN.SB + xv / 8) / 8 * 8 + 8 <= 2 ^ 64.
Proof.
  intros E M k x b kk xv HK Hq Hx Hxv Hfl. unfold RPN.qc_word in Hq.
  pose proof (w_split_lit_denot E _ b kk Hq) as Hsa.
  rewrite (mkAnd_denot SEGS E M k _ _ HK) in Hsa. unfold eadd in Hsa. rewrite mkAlu_denot in Hsa.
  rewrite (mkSrl_denot SEGS E M k x 3 (Z_to_bv 64 3) HK ltac:(rewrite u64_lit by lia; reflexivity)) in Hsa.
  rewrite Hx, (srl3_div8 (Z_to_bv 64 xv) (Z_to_bv 64 3)) in Hsa by (rewrite u64_lit by lia; reflexivity).
  rewrite (zbv_u xv) in Hsa by lia. cbn [edenot] in Hsa. rewrite alu_add, alu_and in Hsa.
  assert (Hx8 : 0 <= xv / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite v_add_zbv in Hsa by (unfold RPN.SB; lia). unfold two64, v_and in Hsa.
  rewrite !zbv_u in Hsa by (unfold RPN.SB; lia). rewrite land_m8 in Hsa by (unfold RPN.SB; lia).
  destruct (w_flat_x_sound SEGS E M k b kk (ELit 8) HK Hfl) as (Hlo' & Hhi' & _).
  replace (bv_unsigned (edenot E (ELit 8))) with 8 in Hhi' by (cbn [edenot]; rewrite u64_lit by lia; reflexivity).
  unfold estart in *. cbn [a_base a_off] in *.
  pose proof (Z.mul_div_le (RPN.SB + xv / 8) 8 ltac:(lia)) as Hm1.
  pose proof (Z.div_pos (RPN.SB + xv / 8) 8 ltac:(unfold RPN.SB; lia) ltac:(lia)) as Hm2.
  apply (f_equal bv_unsigned) in Hsa. rewrite !zbv_u in Hsa by (unfold RPN.SB in *; lia).
  unfold RPN.SB in *. lia.
Qed.

Theorem node_quick_sound : forall src,
  APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (RPN.node_quick SEGS nx0 T src).
Proof.
  intros src cs cs' E R FULL model TT HC _ Hn Hk.
  pose proof HC as HKN. apply co_know in HKN.
  set (M := Mr A argH E cs model FULL) in *.
  rewrite RPN.node_quick_eq in Hn. (* [comment removed for export] *) unfold RPN.node_quick_ref in Hn.
  set (rb := if src then 11%nat else 10%nat) in Hn.
  set (re := if src then 19%nat else 20%nat) in Hn.
  set (entry := if src then RPN.qs_entry T else RPN.qd_entry T) in Hn.
  set (exitpc := if src then RPN.qs_exit T else RPN.qd_exit T) in Hn.
  destruct (Z.eqb (pc cs) entry) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (RPN.qc_word (kn cs) (reg cs rb)) as [b1 k1] eqn:Hq1.
  destruct (RPN.qc_word (kn cs) (eaddz (reg cs re) (-1))) as [b2 k2] eqn:Hq2.
  destruct (xlo (kn cs) (reg cs rb)) as [blo|] eqn:Hblo; [|discriminate].
  destruct (xhi (kn cs) (reg cs rb)) as [bhi|] eqn:Hbhi; [|discriminate].
  destruct (xlo (kn cs) (reg cs re)) as [elo|] eqn:Helo; [|discriminate].
  destruct (xhi (kn cs) (reg cs re)) as [ehi|] eqn:Hehi; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hfresh]. apply andb_prop in Hcond as [Hcond Lsb]. apply andb_prop in Hcond as [Hcond Igsb].
  apply andb_prop in Hcond as [Hcond C0]. apply andb_prop in Hcond as [Hcond G0].
  apply andb_prop in Hcond as [Hcond HV].
  apply andb_prop in Hcond as [Hcond Hle].
  apply andb_prop in Hcond as [Hcond E47]. apply andb_prop in Hcond as [Hcond E2].
  apply andb_prop in Hcond as [B1 B47].
  apply Z.leb_le in B1. apply Z.ltb_lt in B47. apply Z.leb_le in E2. apply Z.leb_le in E47. apply Z.leb_le in C0. apply Z.leb_le in G0.
  match type of Hn with Some (with_ss cs (mk_ss _ ?sr _ _)) = Some cs' => set (sr2 := sr) in Hn end.
  injection Hn as <-.
  destruct (w_fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  (* [comment removed for export] *)
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model rb HC ltac:(subst rb; destruct src; lia)) as Rb.
  pose proof (w_reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model re HC ltac:(subst re; destruct src; lia)) as Re.
  replace (Z_to_bv 5 (Z.of_nat rb)) with (qc_rb src) in Rb by (subst rb; destruct src; apply bv_eq; reflexivity).
  replace (Z_to_bv 5 (Z.of_nat re)) with (qc_re src) in Re by (subst re; destruct src; apply bv_eq; reflexivity).
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hblo) as Hblo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hbhi) as Hbhi2.
  pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Helo) as Helo2.
  pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hehi) as Hehi2.
  set (bw := edenot E (reg cs rb)) in *. set (ew := edenot E (reg cs re)) in *.
  set (beg := bv_unsigned bw) in *. set (en := bv_unsigned ew) in *.
  pose proof (u64_range bw) as Hbr. fold beg in Hbr. pose proof (u64_range ew) as Her. fold en in Her.
  assert (HbwB : Z_to_bv 64 beg = bw) by (apply Z_to_bv_bv_unsigned).
  assert (HewE : Z_to_bv 64 en = ew) by (apply Z_to_bv_bv_unsigned).
  assert (Hbw : edenot E (reg cs rb) = Z_to_bv 64 beg) by (fold bw; symmetry; exact HbwB).
  assert (Hew1 : edenot E (eaddz (reg cs re) (-1)) = Z_to_bv 64 (en - 1)).
  { unfold eaddz. rewrite mkAlu_denot. cbn [edenot]. fold ew. rewrite <- HewE, alu_add, v_add_zbv_mod. f_equal; lia. }
  (* [comment removed for export] *)
  pose proof (lin_ge0_sound SEGS E M (kn cs) _ _ HKN Hle) as Hle2. cbn [xt_den] in Hle2.
  rewrite Hew1, Hbw, !u64_lit in Hle2 by lia.
  assert (Hdv : beg / 8 <= (en - 1) / 8) by (apply Z.div_le_mono; lia).
  pose proof (Z.div_pos beg 8 ltac:(lia) ltac:(lia)) as Hb8.
  pose proof (Z.mul_div_le (RPN.SB + beg / 8) 8 ltac:(lia)) as Hw1a.
  pose proof (Z.mul_div_le (RPN.SB + (en - 1) / 8) 8 ltac:(lia)) as Hw2a.
  pose proof (Z.div_le_mono ((RPN.SB + beg / 8)) ((RPN.SB + (en - 1) / 8)) 8 ltac:(lia) ltac:(lia)) as Hw12.
  pose proof (Z_div_mod_eq_full (RPN.SB + (en - 1) / 8) 8) as Hw2b. pose proof (Z.mod_pos_bound (RPN.SB + (en - 1) / 8) 8 ltac:(lia)) as Hw2c.
  (* [comment removed for export] *)
  assert (FACTS : (exists bs1, rdn SEGS M (Z_to_bv 64 ((RPN.SB + beg / 8) / 8 * 8)) 8 = Some bs1)
                  /\ (exists bs2, rdn SEGS M (Z_to_bv 64 ((RPN.SB + (en - 1) / 8) / 8 * 8)) 8 = Some bs2)
                  /\ exists kb, sh_facts M beg (en - 1) kb 127 true).
  { lazymatch type of HV with (if ?a then true else if ?b then true else ?c) = true =>
      assert (HV' : ((a || b) || c)%bool = true) by (destruct a; [reflexivity|]; destruct b; [reflexivity|]; exact HV) end.
    clear HV. apply orb_prop in HV' as [HV | HCV]; [apply orb_prop in HV as [HA | HB]|].
    - (* [comment removed for export] *)
      apply andb_prop in HA as [HA Hsh].
      apply andb_prop in HA as [HA Hrd2]. apply andb_prop in HA as [HA Hfl2].
      apply andb_prop in HA as [Hfl1 Hrd1].
      destruct (qc_word_sound E M (kn cs) _ _ _ beg HKN Hq1 Hbw ltac:(lia) Hfl1) as (W1 & W1lo & W1hi).
      destruct (qc_word_sound E M (kn cs) _ _ _ (en - 1) HKN Hq2 Hew1 ltac:(lia) Hfl2) as (W2 & W2lo & W2hi).
      destruct (kn_readable_sound SEGS E M (kn cs) M (kn cs) b1 k1 8 HKN HKN ltac:(lia) ltac:(lia) Hrd1) as (_ & bs1 & Hbs1 & _).
      destruct (kn_readable_sound SEGS E M (kn cs) M (kn cs) b2 k2 8 HKN HKN ltac:(lia) ltac:(lia) Hrd2) as (_ & bs2 & Hbs2 & _).
      rewrite adenot_SA, W1 in Hbs1. rewrite adenot_SA, W2 in Hbs2.
      split; [exists bs1; exact Hbs1 | split; [exists bs2; exact Hbs2 |]].
      exact (sh_local_sound E M (kn cs) (reg cs rb) _ beg (en - 1) 127 true HKN Hbw Hew1 ltac:(lia) ltac:(lia) Hsh).
    - (* [comment removed for export] *)
      destruct (sh_alloc_sound E M (kn cs) (reg cs rb) (reg cs re) true 127 beg en HKN HB eq_refl eq_refl) as (_ & [kb0 X] & W).
      specialize (W eq_refl). split; [|split; [|exists kb0; apply sh_facts_zok; exact X]]; apply W; lia.
    - (* [comment removed for export] *)
      destruct (qc_cover_sound E M (kn cs) (reg cs rb) (reg cs re) true beg en 127 true HKN HCV eq_refl eq_refl ltac:(lia)) as [X W].
      specialize (W eq_refl). split; [|split; [|exact X]]; apply W; lia. }
  destruct FACTS as ((bs1 & Hbs1) & (bs2 & Hbs2) & kb & HzS & HkS & Hkmax & Hkok0).
  pose proof (u8_range kb) as Hkr.
  assert (Hsk : bv_signed kb = bv_unsigned kb).
  { unfold bv_signed. apply bv_swrap_small. change (bv_half_modulus 8) with 128. lia. }
  assert (Hkok : bv_signed kb = 0 \/ (en - 1) mod 8 < bv_signed kb).
  { rewrite Hsk. destruct Hkok0 as [H0 | [[_ H0] | H0]]; [| left; exact H0 | right; exact H0].
    left. cbn [rdn] in HkS. rewrite H0 in HkS. injection HkS as <-. reflexivity. }
  (* [comment removed for export] *)
  pose proof (img8_sound E M (kn cs) _ _ HKN Igsb (ri_gsb _ _ IMG)) as C1.
  pose proof (lit_cell_sound E M (kn cs) _ _ HKN C0 Lsb) as C2.
  (* [comment removed for export] *)
  destruct (QSPEC src M beg en R kb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Rb; exact Hbw) ltac:(rewrite Re; fold ew; symmetry; exact HewE)
              C1 C2 (ex_intro _ bs1 Hbs1) (ex_intro _ bs2 Hbs2) HzS HkS Hkok) as (regs' & Hms & Hre & Hother).
  set (VALS := [getr regs' 13%bv; getr regs' 14%bv; getr regs' 15%bv; getr regs' 16%bv; getr regs' 17%bv]).
  set (E' := ext_list E (nxt cs) VALS).
  pose proof (ext_list_agree E (nxt cs) VALS) as Hag. fold E' in Hag.
  eapply (call_core SEGS A nx0 LIMIT SEGS_wx SEGS_in_hull HULL_ok SINV argH argH_high argH_agree SINV_frame SINV_agree NX0_sp FS0
            cs E E' R FULL model TT exitpc sr2 (kn cs) (nxt cs + 5)%nat regs' M HC Hfresh Hag).
  - rewrite Hpc. exact Hms.
  - (* [comment removed for export] *)
    apply regs_ok_pointwise. intros r Hr0.
    pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) as HR.
    assert (HRr : forall r' : bv 5, r' <> 0%bv -> getr R r' = edenot E (nth (ridx r') (s_regs (a_ss cs)) (ELit 0))).
    { intros r' Hr'. rewrite (HR r'). unfold sr_get. destruct (bv_eqb r' 0%bv) eqn:E0; [|reflexivity].
      exfalso. apply Hr'. apply bv_eq. unfold bv_eqb in E0. apply Z.eqb_eq in E0. exact E0. }
    assert (OLD : forall i, (i < 32)%nat -> edenot E' (nth i (s_regs (a_ss cs)) (ELit 0)) = edenot E (nth i (s_regs (a_ss cs)) (ELit 0))).
    { intros i Hi. symmetry. apply (edenot_agree' (nxt cs)); [exact Hag|]. apply nth_sr_vars_lt'; assumption. }
    assert (RX : forall n (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr -> Nat.eqb (ridx r) n = true -> r = rr).
    { intros n rr Hn' Hrb EQ1. apply Nat.eqb_eq in EQ1. rewrite (reg_of_ridx r n EQ1). apply bv_eq.
      rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. exact Hrb. }
    subst sr2. rewrite !nth_sr_upd.
    pose proof (ext_list_at E (nxt cs) VALS 0 ltac:(cbn; lia)) as X0.
    pose proof (ext_list_at E (nxt cs) VALS 1 ltac:(cbn; lia)) as X1.
    pose proof (ext_list_at E (nxt cs) VALS 2 ltac:(cbn; lia)) as X2.
    pose proof (ext_list_at E (nxt cs) VALS 3 ltac:(cbn; lia)) as X3.
    pose proof (ext_list_at E (nxt cs) VALS 4 ltac:(cbn; lia)) as X4.
    fold E' in X0, X1, X2, X3, X4. cbn [nth VALS] in X0, X1, X2, X3, X4.
    replace (nxt cs + 0)%nat with (nxt cs) in X0 by lia. replace (nxt cs + 1)%nat with (S (nxt cs)) in X1 by lia.
    replace (nxt cs + 2)%nat with (S (S (nxt cs))) in X2 by lia. replace (nxt cs + 3)%nat with (S (S (S (nxt cs)))) in X3 by lia.
    replace (nxt cs + 4)%nat with (S (S (S (S (nxt cs))))) in X4 by lia.
    destruct (Nat.eqb (ridx r) 17) eqn:E17; [apply (RX 17%nat 17%bv ltac:(lia) eq_refl) in E17; subst r; cbn [edenot]; symmetry; exact X4|].
    destruct (Nat.eqb (ridx r) 16) eqn:E16; [apply (RX 16%nat 16%bv ltac:(lia) eq_refl) in E16; subst r; cbn [edenot]; symmetry; exact X3|].
    destruct (Nat.eqb (ridx r) 15) eqn:E15; [apply (RX 15%nat 15%bv ltac:(lia) eq_refl) in E15; subst r; cbn [edenot]; symmetry; exact X2|].
    destruct (Nat.eqb (ridx r) 14) eqn:E14; [apply (RX 14%nat 14%bv ltac:(lia) eq_refl) in E14; subst r; cbn [edenot]; symmetry; exact X1|].
    destruct (Nat.eqb (ridx r) 13) eqn:E13; [apply (RX 13%nat 13%bv ltac:(lia) eq_refl) in E13; subst r; cbn [edenot]; symmetry; exact X0|].
    destruct (Nat.eqb (ridx r) re) eqn:Ere; [apply (RX re (qc_re src) ltac:(subst re; destruct src; lia) ltac:(subst re; destruct src; reflexivity)) in Ere; subst r|].
    { rewrite Hre. unfold eaddz. rewrite mkAlu_denot. cbn [edenot]. unfold reg. rewrite OLD by (subst re; destruct src; lia).
      fold (reg cs re). fold ew. rewrite <- HewE, alu_add, v_add_zbv_mod. f_equal; lia. }
    assert (N13 : r <> 13%bv) by (intros ->; cbv in E13; discriminate E13).
    assert (N14 : r <> 14%bv) by (intros ->; cbv in E14; discriminate E14).
    assert (N15 : r <> 15%bv) by (intros ->; cbv in E15; discriminate E15).
    assert (N16 : r <> 16%bv) by (intros ->; cbv in E16; discriminate E16).
    assert (N17 : r <> 17%bv) by (intros ->; cbv in E17; discriminate E17).
    assert (Nre : r <> qc_re src) by (intros ->; subst re; destruct src; cbv in Ere; discriminate Ere).
    rewrite Hother; [ rewrite OLD by (apply ridx_range); apply HRr; exact Hr0 |].
    unfold qc_clob. rewrite (bv_eqb_neq _ _ N13), (bv_eqb_neq _ _ N14), (bv_eqb_neq _ _ N15), (bv_eqb_neq _ _ N16),
      (bv_eqb_neq _ _ N17), (bv_eqb_neq _ _ Nre). reflexivity.
  - eapply know_ok_agree'; [exact Hag | exact Fkn | exact HKN].
  - intros R' FULL' model' HC' Hfs'. apply (Hk E' R' FULL' model'); [| exact HC' | exact Hfs'].
    split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag].
Qed.

Theorem rp_xn_sound : forall id args, APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (RPN.xn SEGS nx0 T id args).
Proof.
  intros id args. unfold RPN.xn.
  destruct (Nat.eqb id 100); [apply node_rpoison_sound|].
  destruct (Nat.eqb id 101); [apply node_readcheck_sound|].
  destruct (Nat.eqb id 102); [apply node_quick_sound|].
  destruct (Nat.eqb id 103); [apply node_quick_sound|].
  intros cs cs' E R FULL model TT _ _ H. discriminate H.
Qed.
End Sound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section AsanNode.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis NX0_sp : nx0_sp_ok nx0.   (* [comment removed for export] *)
Variable FS0 : Fs.Fs.

(* [comment removed for export] *)
Lemma asan_qc_spec : forall src, qc_spec ASEGS RPN.RP_BOTH src.
Proof.
  intros src mem beg en regs kb Hbeg Hbe Hen Hb He C1 C2 Hw1 Hw2 Hz Hk Hkok.
  destruct (quick_check src mem (seg_rom ASEGS) beg en regs kb Hbeg Hbe Hen Hb He C1 C2 Hw1 Hw2 Hz Hk Hkok)
    as (regs' & Hms & Hre & Hrest).
  exists regs'. split; [|split; [exact Hre | exact Hrest]].
  destruct src; cbn [qc_entry qc_exit RPN.qs_entry RPN.qs_exit RPN.qd_entry RPN.qd_exit RPN.RP_BOTH];
    match type of Hms with msteps _ (mkst _ ?p _ _) (mkst _ ?q _ _) =>
      match goal with |- msteps _ (mkst _ (Z_to_bv 64 ?a) _ _) (mkst _ (Z_to_bv 64 ?b) _ _) =>
        replace (Z_to_bv 64 a) with p by (apply bv_eq; reflexivity);
        replace (Z_to_bv 64 b) with q by (apply bv_eq; reflexivity) end end;
    exact Hms.
Qed.

Theorem asan_rp_ext_sound : forall id args, APSC.node1_stmt_fp ASEGS INFO_BOTH nx0 LIMIT SINV argH FS0 FP always (RPN.xn ASEGS nx0 RPN.RP_BOTH id args).
Proof.
  exact (rp_xn_sound ASEGS INFO_BOTH nx0 LIMIT asan_wx asan_in_hull asan_hull_ok asan_segs_wr SINV argH argH_high argH_agree SINV_frame SINV_agree NX0_sp FS0
           RPN.RP_BOTH asan_rp_img asan_rp_spec asan_rc_spec asan_qc_spec).
Qed.
End AsanNode.
End WithFP2.

