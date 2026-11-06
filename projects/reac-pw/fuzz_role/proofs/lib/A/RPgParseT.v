(* reac_role_prop_parse's segment T (lib/A/RPgParseBase.v segT_stmt): the flag at the cut T 0x83224 and the store of
   the role at Q, to the `ret` 0x83324, on reac-pw/fuzz_role's ASan image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6, the same bytes).
   The code from T (a0 = the 32-bit flag v sign-extended, s0 = Q, s3 = SHADOW_OFF, sp = F):
     0x83224 addi a2,zero,2; 0x83228 addi a1,zero,-1; 0x8322c bgeu a0,a2 -> 0x832f4 (v not in {0, 1});
     0x83230 srli a1,s0,3; 0x83234 add a1,a1,s3; 0x83238 lb a1,0(a1); 0x8323c bnez a1 -> 0x833d0 (the instrumented
     check of the 4 bytes at Q; the slow path 0x833d0 andi a2,s0,7 / addi a2,a2,3 / blt a2,a1 -> 0x83240, else the
     error-path call at 0x833e0); 0x83240 sw a0,0(s0); 0x83244 addi a1,zero,1; 0x83248 j 0x832f4;
     0x832f4 mv a0,a1; 0x832f8 .. 0x8331c the ten saved words back; 0x83320 addi sp,sp,0x60; 0x83324 ret.
   The walk is split at its entry on v: for v in {0, 1} the entry state holds the frame region, a writable region of 4
   bytes at Q (atom 8) and the shadow entry of Q's 4 bytes (from call_ok's range_addressable Q 4, unchanged at the
   cut: Q's shadow bytes lie below the allocator's ceiling, so outside the callee's stack); the atom fact 0 <= a0 <= 1
   decides the bgeu (not taken), the shadow engine passes the check, and the run stores v at Q and returns 1. For v
   not in {0, 1} the entry state holds the frame region only; the atom fact 2 <= a0 decides the bgeu (taken) and the
   run returns -1 with no store. Both runs are engine runs on the concrete image (aj_run_tok) at the float state the
   cut gives (T_ok runs at fx2; the walk below is generic in its float state). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Role.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgParseBase.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgCfgChanges.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------- the entry states ---------------------------------- *)
(* the role cell: 4 writable bytes at s0 = Q (atom 8) *)
Definition q_region : YP09.region := YP09.mkRegion (Some 8%nat) 0 4 0 4 [].
(* the lowest F can be: the allocator's ceiling at its least (CEIL_MIN) *)
Definition T_FLO : Z := 0x7fff7f800000.
Definition t_rs_st : smem := [frame_region []; q_region].
Definition t_rs_sk : smem := [frame_region []].
(* atoms: F (sp), Q (s0), the flag (a0) and SHADOW_OFF (s3) *)
Definition t_G_st : facts :=
mkFacts [(2%nat, mkAF T_FLO (2 ^ 47) 4); (8%nat, mkAF 0 (2 ^ 47 - 4) 2); (10%nat, mkAF 0 1 0); (19%nat, mkAF SBr SBr 0)] [] [].
Definition t_G_sk : facts :=
mkFacts [(2%nat, mkAF T_FLO (2 ^ 47) 4); (10%nat, mkAF 2 (2 ^ 64 - 1) 0); (19%nat, mkAF SBr SBr 0)] [] [].
Definition t_SH_st : list shent := [mkSHE 8 0 4].
Definition ss_t_st : sstate := mkSS PC_T sr_atoms t_rs_st None t_G_st.
Definition ss_t_sk : sstate := mkSS PC_T sr_atoms t_rs_sk None t_G_sk.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.

(* what the walk's leaf must give, for the post Post of the call *)
Definition t_leaf (x : pctx) (v : Z) (Post : world rsegs -> config -> Prop) : Prop :=
forall regsF memF md3,
ajournal rsegs B (x_STK x) (x_sp0 x) (x_FP x) (x_ly x) (x_S x) (x_W0 x) (x_mem0 x) (x_md0 x) (x_own x)
(x_lyc x) (x_Sc x) (x_W x) memF md3 (x_k x) ->
same_io (x_mdc x) md3 ->
aregs_preserved (x_regs x) regsF ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp x - T_parse_STK <= a < x_sp x) ->
 ~ (fst (Role.flag_rc v) <> None /\ x_Q x <= a < x_Q x + 4) ->
 aview rsegs (w_H (x_W x)) memF a = aview rsegs (w_H (x_W x)) (x_memc x) a) ->
getr regsF 10 = w64 (snd (Role.flag_rc v)) ->
match fst (Role.flag_rc v) with
| Some r => val_mem rsegs (mrestrict (w_H (x_W x)) memF) (x_Q x) 4 (Role.role_z r)
| None => True
end ->
Post (x_W x) (mkCfg (mkst regsF (getr (x_regs x) 1) memF (seg_rom rsegs)) md3).

(* Q's 4 bytes at the cut: in the caller's stack window or in a side-stack frame the caller holds (rl_wcell), so
   present, apart from the shadow band, and writable under the caller's journal (awr_byte's first or fourth case) *)
Lemma t_q_facts : forall x regs2 mem2 md2, pre_ok B x -> FI B x regs2 mem2 md2 ->
0 <= x_Q x /\ x_Q x + 4 <= 2 ^ 47 /\
(forall a, x_Q x <= a < x_Q x + 4 -> apresent (w_H (x_W x)) mem2 a) /\
(forall a, x_Q x <= a < x_Q x + 4 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 17592186044416)) /\
(forall a, x_Q x <= a < x_Q x + 4 ->
 awr_byte (x_STK x) (x_sp0 x) (x_FP x) (ablocks B (x_ly x) (x_S x)) (ablocks B (x_lyc x) (x_Sc x)) (x_lyc x) (x_own x) a).
Proof.
intros x regs2 mem2 md2 Hpre HFI.
pose proof Hpre as (_ & _ & _ & _ & HWC & _).
destruct HFI as (HJ & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof alloc_ceiling_value as [[Hc1 Hc2] _]. pose proof alloc_ceiling_lt as Hclt.
destruct HWC as [[Hw | (cid & pos & Hown & Hcid & Hf1 & Hf2)] _].
- unfold SHADOW_OFF. split; [lia|]. split; [lia|]. split; [intros a Ha; apply Hpres; lia|].
  split; [intros a Ha; lia|]. intros a Ha. left. lia.
- assert (Hin : In (cid, pos) (frames (x_Sc x))) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
  destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hin) as (_ & Happ & HFp & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
  destruct Happ as [Ha0 [Ha1 | [Ha1 Ha2]]].
  + unfold SHADOW_OFF. split; [lia|]. split; [lia|]. split; [intros a Ha; apply (proj1 (HFp a ltac:(lia)))|].
    split; [intros a Ha; lia|].
    intros a Ha. right; right; right. exists cid, pos. split; [exact Hown | left; unfold in_zr; cbn [fst snd]; lia].
  + unfold SHADOW_OFF. split; [lia|]. split; [lia|]. split; [intros a Ha; apply (proj1 (HFp a ltac:(lia)))|].
    split; [intros a Ha; lia|].
    intros a Ha. right; right; right. exists cid, pos. split; [exact Hown | left; unfold in_zr; cbn [fst snd]; lia].
Qed.

(* Q's shadow bytes at the cut are as at the call: they lie below the allocator's ceiling *)
Lemma t_q_ra : forall x regs2 mem2 md2, pre_ok B x -> FI B x regs2 mem2 md2 -> 0 <= x_Q x -> x_Q x + 4 <= 2 ^ 47 ->
range_addressable (aview rsegs (w_H (x_W x)) mem2) SHADOW_OFF (x_Q x) 4.
Proof.
intros x regs2 mem2 md2 Hpre HFI HQ0 HQ47.
pose proof Hpre as (_ & _ & _ & _ & _ & _ & HRA & _).
pose proof (pre_stack B x Hpre) as (Hceil & _).
pose proof alloc_ceiling_lt as Hclt.
intros a Ha. destruct (HRA a Ha) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite <- Hs. unfold shadow_of_addr.
pose proof (shadow_below_ceiling a ltac:(unfold kHighMemEnd; lia)) as M.
assert (0 <= a / 8) by (apply Z.div_pos; lia).
apply (kept_view B x regs2 mem2 md2 _ HFI); unfold SHADOW_OFF in *; lia.
Qed.

(* the registers the entry reads, as numbers *)
Lemma t_cut_regs : forall x regs2 mem2 md2, pre_ok B x -> FI B x regs2 mem2 md2 -> 0 <= x_Q x -> x_Q x + 4 <= 2 ^ 47 ->
bv_unsigned (getr regs2 2) = x_F x /\ T_FLO <= x_F x /\ x_F x + FRAME <= 2 ^ 47 /\ x_F x mod 16 = 0 /\
bv_unsigned (getr regs2 8) = x_Q x /\ bv_unsigned (getr regs2 19) = SHADOW_OFF.
Proof.
intros x regs2 mem2 md2 Hpre HFI HQ0 HQ47.
pose proof (pre_stack B x Hpre) as (Hceil & Hsp & H47 & Hal & Hwin).
pose proof alloc_ceiling_value as [[Hc1 Hc2] _].
destruct HFI as (_ & _ & _ & _ & H2 & _ & H8 & H19).
rewrite H2, H8, H19. unfold w64. unfold x_F, FRAME, T_parse_STK, ESTACK, T_FLO, SHADOW_OFF in *.
rewrite !unsigned_lit_small by lia. repeat split; lia.
Qed.

(* ---------------------------------- the walk ---------------------------------- *)
Ltac t_inwr B2 B8 :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
first [ rewrite B2 in Hb; unfold x_F, FRAME, T_parse_STK, ESTACK in *; first [left; lia | lia]
      | rewrite B8 in Hb; right; lia ] | ]);
destruct Hr.
Ltac t_r10 R10 :=
lazymatch goal with HS : st_ok ?segs ?E ?ss (restrict ?H ?ms) |- _ =>
let e := eval vm_compute in (sr_get (ss_regs ss) (10%bv : bv 5)) in
assert (R10 : getr (ms_regs ms) (10%bv : bv 5) = sv_denot E e) by exact (st_ok_restrict_reg segs H E ss ms (10%bv : bv 5) HS)
end.

(* v in {0, 1}: the check of Q passes, v is stored at Q, 1 is returned *)
Lemma T_walk_st : forall x v regs2 mem2 md2 (Post : world rsegs -> config -> Prop),
pre_ok B x -> FI B x regs2 mem2 md2 -> getr regs2 10 = w64 v -> v = 0 \/ v = 1 -> t_leaf x v Post ->
SRr rsegs (x_W x) (cfg_at rsegs PC_T regs2 mem2 md2) Post.
Proof.
intros x v regs2 mem2 md2 Post Hpre HFI H10 Hv HL.
pose proof (t_q_facts x regs2 mem2 md2 Hpre HFI) as (HQ0 & HQ47 & HQp & HQapp & HQw).
pose proof (t_q_ra x regs2 mem2 md2 Hpre HFI HQ0 HQ47) as HRA2.
pose proof (t_cut_regs x regs2 mem2 md2 Hpre HFI HQ0 HQ47) as (G2 & HF0 & HF47 & HFal & G8 & G19).
pose proof (pre_stack B x Hpre) as (Hceil & Hsp & H47 & Hal & Hwin).
pose proof Hpre as ((_ & Hra & _) & _ & _ & _ & (_ & HQsp) & HQ4 & _).
pose proof HFI as (HJ & Hio & HK & _ & H2 & Hcs & H8 & H19).
pose proof parse_wx as Hwx. pose proof parse_segs_low as Hsegs.
assert (V10 : bv_unsigned (getr regs2 10) = v) by (rewrite H10; unfold w64; apply unsigned_lit_small; lia).
(* the entry state *)
assert (HS : st_ok rsegs (cut_env x regs2 []) ss_t_st
  (restrict (w_H (x_W x)) (mkst regs2 (Z_to_bv 64 PC_T) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_t_st, cut_env. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold t_rs_st. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + exact (frame_region_ok B x regs2 mem2 md2 [] [] HFI Hpre (Forall_nil _)).
    + unfold region_ok, q_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl), G8.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable rsegs). apply HQp. lia.
  - unfold t_rs_st, frame_region, q_region. cbn [pairwise_disjoint all_disjoint].
    unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), (ew_Ereg_nat regs2 _ 8 8%bv eq_refl), G2, G8.
    refine (conj (conj _ I) (conj I I)). unfold x_F, FRAME, T_parse_STK, ESTACK in *. lia.
  - unfold facts_ok, t_G_st. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2].
    rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), (ew_Ereg_nat regs2 _ 8 8%bv eq_refl),
      (ew_Ereg_nat regs2 _ 10 10%bv eq_refl), (ew_Ereg_nat regs2 _ 19 19%bv eq_refl), G2, G8, V10, G19.
    change (2 ^ 4) with 16. change (2 ^ 2) with 4. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
    unfold SBr, SHADOW_OFF, x_F, FRAME, T_FLO in *.
    repeat split; lia. }
remember (cut_env x regs2 []) as E eqn:HE.
assert (HEc : forall n, (n < 43)%nat -> ew E n = ew (cut_env x regs2 []) n) by (intros n _; subst E; reflexivity).
assert (E8 : ew E 8 = Z_to_bv 64 (x_Q x)) by (subst E; rewrite (cut_env_reg x regs2 [] 8 8%bv eq_refl); exact H8).
assert (E10 : ew E 10 = Z_to_bv 64 v) by (subst E; rewrite (cut_env_reg x regs2 [] 10 10%bv eq_refl); exact H10).
assert (E19 : ew E 19 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (cut_env_reg x regs2 [] 19 19%bv eq_refl); exact H19).
assert (B2 : bv_unsigned (ew E 2) = x_F x) by (subst E; rewrite (cut_env_reg x regs2 [] 2 2%bv eq_refl); exact G2).
assert (B8 : bv_unsigned (ew E 8) = x_Q x) by (subst E; rewrite (cut_env_reg x regs2 [] 8 8%bv eq_refl); exact G8).
clear HE.
(* the shadow entry of Q's 4 bytes *)
assert (SHOK : sh_ok rsegs PBx t_SH_st E (mrestrict (w_H (x_W x)) mem2)).
{ unfold sh_ok, t_SH_st. apply Forall_cons; [|apply Forall_nil].
  apply shent_ok_of_range with (a := x_Q x) (n := 4) (p := x_Q x); [exact HRA2 | | | lia | lia |].
  - unfold PBx. apply (U_atom E 19); [exact E19 | unfold SHADOW_OFF; lia].
  - apply (U_atom E 8); [exact E8 | lia].
  - intros a Ha. rewrite Z.min_l, Z.max_r in Ha by lia. apply HQapp. lia. }
(* the bytes outside the callee's stack and Q are as at the call *)
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ ((x_sp x - T_parse_STK <= a < x_sp x) \/ (x_Q x <= a < x_Q x + 4)) ->
  aview rsegs (w_H (x_W x)) mem2 a = aview rsegs (w_H (x_W x)) (x_memc x) a).
{ intros a Ha Hz. apply HK; [exact Ha | intros Hc; apply Hz; left; exact Hc]. }
clear HK.
unfold cfg_at. change (w64 PC_T) with (Z_to_bv 64 PC_T).
(* 0x83224 .. 0x83324: the bgeu falls through (0 <= a0 <= 1), the check of Q passes, sw a0,0(s0), a1 = 1, the
   epilogue; the run stops at the ret *)
aj_run_tok parse_tbl_ok HS HJ SHOK RTBspan.
- lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fp b0 bc ly own) end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (x_F x - x_sp0 x));
  [reflexivity | rewrite B2; lia | cbn [YP09.r_wlo]; unfold x_F, FRAME, T_parse_STK, ESTACK in *; lia
  | cbn [YP09.r_whi]; unfold x_F, FRAME in *; lia |].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 8%nat (x_Q x)); [reflexivity | exact B8 | |].
  + cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply HQw. lia.
  + apply awr_ok_nil.
- (* the bytes the run may write: the frame (in the callee's stack) and Q *)
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    pose proof (RPgCfgChanges.kept_run (fun a => (x_sp x - T_parse_STK <= a < x_sp x) \/ (x_Q x <= a < x_Q x + 4))
      _ _ _ _ _ _ KE HFr) as KS end.
  lazymatch type of KS with ?P -> _ => assert (KW : P) by (t_inwr B2 B8) end.
  specialize (KS KW). clear KW KE.
  lazymatch goal with HS' : st_ok _ ?E' ?ss' (restrict _ ?ms') |- _ =>
    assert (HAg : forall n, (n < 43)%nat -> ew E' n = ew E n) by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity);
    t_r10 R10;
    destruct (leaf_regs B x regs2 [] E' ss' ms' (w_H (x_W x)) Hpre HS'
      ltac:(intros n Hn; rewrite HAg by exact Hn; apply HEc; exact Hn) ltac:(vm_compute; reflexivity) H2 Hcs) as [Hpr LR1];
    (* the 4 bytes at Q: the chunk the store left *)
    pose proof (st_ok_mem_ok rsegs _ _ _ HS') as (_ & HM & _);
    cbn [ss_mem] in HM;
    apply Forall_cons_iff in HM as [_ HM]; apply Forall_cons_iff in HM as [HQr _];
    destruct HQr as (_ & _ & _ & HC);
    cbn [YP09.r_base YP09.r_chunks base_val] in HC;
    apply Forall_cons_iff in HC as [Hc _];
    pose proof (val_of_chunk_ok rsegs E' _ _ 0 4%N (SOff 10 0) v Hc
      ltac:(rewrite sv_denot_SOff0, HAg by lia; exact E10) ltac:(destruct Hv as [-> | ->]; cbn; lia) ltac:(cbn; lia)) as VQ;
    rewrite HAg, B8, Z.add_0_r in VQ by lia;
    eapply (SRr_ret_at rsegs parse_tbl parse_tbl_ok parse_wx (x_W x) E'); [exact HS' | reflexivity | vm_compute; reflexivity |]
  end.
  intros mat'. rewrite LR1, Hra. apply HL.
  + eapply ajournal_materialize; first [exact LAWS | exact Hsegs | exact HJ].
  + let rec kio := first [ exact Hio | apply same_io_refl
      | eapply same_io_trans; [| apply RPgCfgChanges.same_io_wvb]; kio ] in kio.
  + exact Hpr.
  + intros a Ha Hn1 Hn2. apply KS; [exact Ha|]. intros [Hz | Hz]; [exact (Hn1 Hz)|].
    apply Hn2. split; [destruct Hv as [-> | ->]; cbv; intros Hn; discriminate Hn | exact Hz].
  + rewrite R10, denot_lit_U, U_lit by lia. destruct Hv as [-> | ->]; reflexivity.
  + destruct Hv as [-> | ->]; exact VQ.
Qed.

(* v not in {0, 1}: -1 is returned, nothing is stored *)
Lemma T_walk_sk : forall x v regs2 mem2 md2 (Post : world rsegs -> config -> Prop),
pre_ok B x -> FI B x regs2 mem2 md2 -> getr regs2 10 = w64 v -> - 2 ^ 31 <= v < 2 ^ 31 -> v <> 0 -> v <> 1 ->
t_leaf x v Post ->
SRr rsegs (x_W x) (cfg_at rsegs PC_T regs2 mem2 md2) Post.
Proof.
intros x v regs2 mem2 md2 Post Hpre HFI H10 Hv Hv0 Hv1 HL.
pose proof (t_q_facts x regs2 mem2 md2 Hpre HFI) as (HQ0 & HQ47 & _).
pose proof (t_cut_regs x regs2 mem2 md2 Hpre HFI HQ0 HQ47) as (G2 & HF0 & HF47 & HFal & _ & G19).
pose proof (pre_stack B x Hpre) as (Hceil & Hsp & H47 & Hal & Hwin).
pose proof Hpre as ((_ & Hra & _) & _).
pose proof HFI as (HJ & Hio & HK & _ & H2 & Hcs & H8 & H19).
pose proof parse_wx as Hwx. pose proof parse_segs_low as Hsegs.
assert (Hfr : Role.flag_rc v = (None, -1)).
{ unfold Role.flag_rc. destruct (Z.eqb_spec v 0); [lia|]. destruct (Z.eqb_spec v 1); [lia|]. reflexivity. }
assert (V10 : 2 <= bv_unsigned (getr regs2 10) <= 2 ^ 64 - 1).
{ rewrite H10. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  destruct (Z_lt_le_dec v 0).
  - rewrite <- (Z_mod_plus_full v 1 (2 ^ 64)). rewrite Z.mod_small by lia. lia.
  - rewrite Z.mod_small by lia. lia. }
(* the entry state *)
assert (HS : st_ok rsegs (cut_env x regs2 []) ss_t_sk
  (restrict (w_H (x_W x)) (mkst regs2 (Z_to_bv 64 PC_T) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_t_sk, cut_env. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold t_rs_sk. apply Forall_cons; [|apply Forall_nil].
    exact (frame_region_ok B x regs2 mem2 md2 [] [] HFI Hpre (Forall_nil _)).
  - unfold t_rs_sk. cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  - unfold facts_ok, t_G_sk. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2].
    rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), (ew_Ereg_nat regs2 _ 10 10%bv eq_refl),
      (ew_Ereg_nat regs2 _ 19 19%bv eq_refl), G2, G19.
    change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
    unfold SBr, SHADOW_OFF, x_F, FRAME, T_FLO in *.
    repeat split; lia. }
remember (cut_env x regs2 []) as E eqn:HE.
assert (HEc : forall n, (n < 43)%nat -> ew E n = ew (cut_env x regs2 []) n) by (intros n _; subst E; reflexivity).
assert (B2 : bv_unsigned (ew E 2) = x_F x) by (subst E; rewrite (cut_env_reg x regs2 [] 2 2%bv eq_refl); exact G2).
clear HE.
assert (SHOK : sh_ok rsegs PBx [] E (mrestrict (w_H (x_W x)) mem2)) by apply Forall_nil.
unfold cfg_at. change (w64 PC_T) with (Z_to_bv 64 PC_T).
(* 0x83224 .. 0x83324: the bgeu is taken (2 <= a0), a0 = a1 = -1, the epilogue; the run stops at the ret *)
aj_run_tok parse_tbl_ok HS HJ SHOK RTBspan.
- lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fp b0 bc ly own) end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (x_F x - x_sp0 x));
  [reflexivity | rewrite B2; lia | cbn [YP09.r_wlo]; unfold x_F, FRAME, T_parse_STK, ESTACK in *; lia
  | cbn [YP09.r_whi]; unfold x_F, FRAME in *; lia |].
  apply awr_ok_nil.
- lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    pose proof (RPgCfgChanges.kept_run (fun a => x_sp x - T_parse_STK <= a < x_sp x)
      _ _ _ _ _ _ HK HFr) as KS end.
  lazymatch type of KS with ?P -> _ => assert (KW : P) by (t_inwr B2 B2) end.
  specialize (KS KW). clear KW.
  lazymatch goal with HS' : st_ok _ ?E' ?ss' (restrict _ ?ms') |- _ =>
    assert (HAg : forall n, (n < 43)%nat -> ew E' n = ew E n) by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity);
    t_r10 R10;
    destruct (leaf_regs B x regs2 [] E' ss' ms' (w_H (x_W x)) Hpre HS'
      ltac:(intros n Hn; transitivity (ew E n); [apply HAg; exact Hn | apply HEc; exact Hn])
      ltac:(vm_compute; reflexivity) H2 Hcs) as [Hpr LR1];
    eapply (SRr_ret_at rsegs parse_tbl parse_tbl_ok parse_wx (x_W x) E'); [exact HS' | reflexivity | vm_compute; reflexivity |]
  end.
  intros mat'. rewrite LR1, Hra. apply HL.
  + eapply ajournal_materialize; first [exact LAWS | exact Hsegs | exact HJ].
  + let rec kio := first [ exact Hio | apply same_io_refl
      | eapply same_io_trans; [| apply RPgCfgChanges.same_io_wvb]; kio ] in kio.
  + exact Hpr.
  + intros a Ha Hn1 _. exact (KS a Ha Hn1).
  + rewrite R10, Hfr, denot_lit_U, U_lit by lia. cbn [snd]. unfold w64. apply bv_eq.
    rewrite !Z_to_bv_unsigned. reflexivity.
  + rewrite Hfr. exact I.
Qed.

Lemma T_walk : forall x v regs2 mem2 md2 (Post : world rsegs -> config -> Prop),
pre_ok B x -> FI B x regs2 mem2 md2 -> getr regs2 10 = w64 v -> - 2 ^ 31 <= v < 2 ^ 31 -> t_leaf x v Post ->
SRr rsegs (x_W x) (cfg_at rsegs PC_T regs2 mem2 md2) Post.
Proof.
intros x v regs2 mem2 md2 Post Hpre HFI H10 Hv HL.
destruct (Z.eq_dec v 0) as [Hv0 | Hv0]; [apply (T_walk_st x v regs2 mem2 md2 Post Hpre HFI H10 (or_introl Hv0) HL)|].
destruct (Z.eq_dec v 1) as [Hv1 | Hv1]; [apply (T_walk_st x v regs2 mem2 md2 Post Hpre HFI H10 (or_intror Hv1) HL)|].
exact (T_walk_sk x v regs2 mem2 md2 Post Hpre HFI H10 Hv Hv0 Hv1 HL).
Qed.
End w.

(* ---------------------------------- the segment ---------------------------------- *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* the call's premises at another float state with a zero rounding mode *)
Lemma pre_ok_fx : forall (fxb : YK11.FPState) x, @pre_ok fx rc SK B x -> YK0o.frm_zero (@fp_csr fxb) ->
@pre_ok fxb rc SK B x.
Proof.
intros fxb x H Hz. destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & _).
exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 (conj A9 Hz))))))))).
Qed.

Theorem segT_ok : segT_stmt B MT.
Proof.
unfold segT_stmt, T_ok. intros x v Hpre fx2 regs2 mem2 md2 HT.
destruct HT as (HFI & H10 & Hv & Hfx & Hres).
pose proof (pre_ok_fx fx2 x Hpre (proj2 Hfx)) as Hpre2.
apply (@T_walk fx2 rc SK B LAWS x v regs2 mem2 md2 (@PPOST fx rc SK B MT x false) Hpre2 HFI H10 Hv).
unfold t_leaf. intros regsF memF md3 HJ Hio Hpr HK HR10 HRQ.
assert (Hr : rl_parse_res false (x_bs x) = Role.flag_rc v) by exact Hres.
apply (@ppost_intro fx rc SK B MT MTL x false fx2 regsF memF md3 HJ Hio Hpr Hfx); rewrite Hr; assumption.
Qed.
End b.
