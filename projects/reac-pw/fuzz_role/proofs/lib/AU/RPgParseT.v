(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgParseT.v at d428443238a; for image B
   (fuzz_role.asan-ubsan): the image and the base are lib/AU/Img0.v's and lib/AU/RPgParseBase.v's, the pcs are image
   B's, the flag is in a1 (A: a0) and image B tests sext.w a1 against 1 and 0 before the store, so the entry is split
   three ways (v = 1, v = 0, v not in {0, 1}) with the outcomes of those two tests as entry conditions (sx11,
   t_cond_ok); atom 8 (s0 = Q) has the lower bound 4 (from the base's pre_q) so the engine decides image B's two trap
   branches on Q; a0 holds the value returned (no mv at the epilogue). *)
(* reac_role_prop_parse's segment T (lib/AU/RPgParseBase.v segT_stmt): the flag at the cut T 0x83488 and the store of
   the role at Q, to the `ret` 0x835c4, on reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, the same loaded bytes).
   The code from T (a1 = the 32-bit flag v sign-extended, s0 = Q, s3 = SHADOW_OFF, sp = F):
     0x83488 sext.w a2,a1; 0x8348c addi a0,zero,1; 0x83490 beq a2,a0 -> 0x8349c (v = 1); 0x83494 addi a0,zero,-1;
     0x83498 bnez a2 -> 0x83598 (v not in {0, 1}: a0 = -1, the epilogue);
     0x8349c beqz s0 -> 0x835c8 (the trap of Q = 0); 0x834a0 andi a0,s0,3; 0x834a4 bnez a0 -> 0x835c8 (the trap of
     Q & 3); 0x834a8 srli a0,s0,3; 0x834ac add a0,a0,s3; 0x834b0 lb a0,0(a0); 0x834b4 bnez a0 -> 0x8366c (the
     instrumented check of the 4 bytes at Q; the slow path 0x8366c andi a2,s0,7 / 0x83670 addi a2,a2,3 / 0x83674
     blt a2,a0 -> 0x834b8, else 0x83678 mv a0,s0 and the error-path call 0x8367c jal 0x586e4); 0x834b8 sw a1,0(s0);
     0x834bc addi a0,zero,1; 0x834c0 j 0x83598; 0x83598 .. 0x835bc the ten saved words back; 0x835c0 addi sp,sp,0x60;
     0x835c4 ret.
   The engine forms a2 = sext.w a1 as the term sx11 (the 32-bit add of atom 11 and 0, sign-extended) and does not
   decide its tests against 1 and 0 from ranges, so the walk is split at its entry on v and each entry state carries
   the outcomes as conditions, proved from a1 = v by t_cond_ok:
   - v = 1 (sx11 = 1: the beq is taken) and v = 0 (sx11 <> 1 and sx11 = 0: the beq and the bnez fall through): the
     entry state holds the frame region, a writable region of 4 bytes at Q (atom 8) and the shadow entry of Q's 4
     bytes (from call_ok's range_addressable Q 4, unchanged at the cut: Q's shadow bytes lie below the allocator's
     ceiling, so outside the callee's stack). The two trap branches to the `unimp` 0x835c8 are not taken: atom 8 has
     the fact mkAF 4 (2 ^ 47 - 4) 2, that is 4 <= Q <= 2^47 - 4 and Q mod 4 = 0 (from the base's pre_q, 0 < Q and
     Q mod 4 = 0, and t_q_facts's Q + 4 <= 2^47), so the engine decides 0x8349c beqz s0 (not taken as s0 >= 4) and
     0x834a4 bnez a0 (not taken as a0 = s0 & 3 = 0) by itself. Q's 4 bytes are marked usable, so the instrumented
     check passes and the error-path call 0x8367c is not reached; the run stores v at Q and returns 1.
   - v not in {0, 1} (sx11 <> 1 and sx11 <> 0: the bnez is taken): the entry state holds the frame region only; the
     run returns -1 with no store.
   All three runs are engine runs on the concrete image (aj_run_tok) at the float state the cut gives (T_ok runs at
   fx2; the walk below is generic in its float state). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgParseBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------- the flag's tests ---------------------------------- *)
(* a2 = sext.w a1 as the engine forms it *)
Definition sx11 : sv := SAluw ALU_ADD (SOff 11 0) (SLit 0).

Lemma t_sx11_U : forall E v, ew E 11 = Z_to_bv 64 v -> - 2 ^ 31 <= v < 2 ^ 31 -> U E sx11 = v mod 2 ^ 64.
Proof.
intros E v H11 Hv. rewrite U_of_S. unfold sx11. rewrite S_SAluw, U_SOff, U_SLit, H11. cbn [zalu_raw].
rewrite Z_to_bv_unsigned.
lazymatch goal with |- bv_wrap 64 (bv_swrap 32 ?X) = _ => replace (bv_swrap 32 X) with v end.
- unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). reflexivity.
- transitivity (bv_swrap 32 v); [symmetry; apply swrap32_id; lia|]. apply swrap32_congr.
  unfold zcanon, two32, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

(* the outcome of beq / bne sx11, k for a small k *)
Lemma t_cond_ok : forall E v c k, ew E 11 = Z_to_bv 64 v -> - 2 ^ 31 <= v < 2 ^ 31 -> 0 <= k < 2 ^ 31 ->
(c = BC_EQ /\ v = k) \/ (c = BC_NE /\ v <> k) -> acond_ok E (mkAC c sx11 (SLit k)).
Proof.
intros E v c k H11 Hv Hk Hc. unfold acond_ok. cbn [ac_c ac_a ac_b].
pose proof (t_sx11_U E v H11 Hv) as HU.
destruct Hc as [[-> Hvk] | [-> Hvk]].
- rewrite branch_eq_U, HU, U_lit by lia. apply Z.eqb_eq. subst k. apply Z.mod_small. lia.
- rewrite branch_ne_U, HU, U_lit by lia. apply negb_true_iff, Z.eqb_neq. lia.
Qed.

Ltac t_cond_side := first [ left; split; [reflexivity | lia] | right; split; [reflexivity | lia] | lia ].

(* ---------------------------------- the entry states ---------------------------------- *)
(* the role cell: 4 writable bytes at s0 = Q (atom 8) *)
Definition q_region : YP09.region := YP09.mkRegion (Some 8%nat) 0 4 0 4 [].
(* the lowest F can be: the allocator's ceiling at its least (CEIL_MIN) *)
Definition T_FLO : Z := 0x7fff7f800000.
Definition t_rs_st : smem := [frame_region []; q_region].
Definition t_rs_sk : smem := [frame_region []].
(* the outcomes of 0x83490 beq a2,a0 (a0 = 1) and 0x83498 bnez a2 for v in {0, 1} *)
Definition t_cst (v : Z) : list acond :=
if v =? 1 then [mkAC BC_EQ sx11 (SLit 1)] else [mkAC BC_NE sx11 (SLit 1); mkAC BC_EQ sx11 (SLit 0)].
(* atoms: F (sp), Q (s0; at least 4 and 4-aligned, so the trap branches 0x8349c and 0x834a4 are decided) and
   SHADOW_OFF (s3) *)
Definition t_G_st (v : Z) : facts :=
mkFacts [(2%nat, mkAF T_FLO (2 ^ 47) 4); (8%nat, mkAF 4 (2 ^ 47 - 4) 2); (19%nat, mkAF SBr SBr 0)] (t_cst v) [].
Definition t_G_sk : facts :=
mkFacts [(2%nat, mkAF T_FLO (2 ^ 47) 4); (19%nat, mkAF SBr SBr 0)] [mkAC BC_NE sx11 (SLit 1); mkAC BC_NE sx11 (SLit 0)] [].
Definition t_SH_st : list shent := [mkSHE 8 0 4].
Definition ss_t_st (v : Z) : sstate := mkSS PC_T sr_atoms t_rs_st None (t_G_st v).
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

(* v in {0, 1}: the trap branches on Q are not taken, the check of Q passes, v is stored at Q, 1 is returned *)
Lemma T_walk_st : forall x v regs2 mem2 md2 (Post : world rsegs -> config -> Prop),
pre_ok B x -> FI B x regs2 mem2 md2 -> getr regs2 11 = w64 v -> v = 0 \/ v = 1 -> t_leaf x v Post ->
SRr rsegs (x_W x) (cfg_at rsegs PC_T regs2 mem2 md2) Post.
Proof.
intros x v regs2 mem2 md2 Post Hpre HFI H11 Hv HL.
pose proof (t_q_facts x regs2 mem2 md2 Hpre HFI) as (HQ0 & HQ47 & HQp & HQapp & HQw).
pose proof (t_q_ra x regs2 mem2 md2 Hpre HFI HQ0 HQ47) as HRA2.
pose proof (t_cut_regs x regs2 mem2 md2 Hpre HFI HQ0 HQ47) as (G2 & HF0 & HF47 & HFal & G8 & G19).
pose proof (pre_stack B x Hpre) as (Hceil & Hsp & H47 & Hal & Hwin).
pose proof (pre_q B LAWS x Hpre) as (HQpos & HQ4).
pose proof Hpre as ((_ & Hra & _) & _ & _ & _ & (_ & HQsp) & _).
pose proof HFI as (HJ & Hio & HK & _ & H2 & Hcs & H8 & H19).
pose proof parse_wx as Hwx. pose proof parse_segs_low as Hsegs.
(* Q is at least 4: 0 < Q and Q mod 4 = 0 (the base's pre_q) *)
assert (HQ4l : 4 <= x_Q x) by (clear - HQpos HQ4; lia).
assert (E11c : ew (cut_env x regs2 []) 11 = Z_to_bv 64 v) by (rewrite (cut_env_reg x regs2 [] 11 11%bv eq_refl); exact H11).
(* the entry state *)
assert (HS : st_ok rsegs (cut_env x regs2 []) (ss_t_st v)
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
  - unfold facts_ok, t_G_st. cbn [f_atoms f_conds f_alias atoms_ok alias_ok]. split; [|split; [|exact I]].
    + (* atom 8's fact 4 <= Q <= 2^47 - 4, Q mod 4 = 0: from 0 < Q, Q mod 4 = 0 and Q + 4 <= 2^47 *)
      unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), (ew_Ereg_nat regs2 _ 8 8%bv eq_refl),
        (ew_Ereg_nat regs2 _ 19 19%bv eq_refl), G2, G8, G19.
      change (2 ^ 4) with 16. change (2 ^ 2) with 4. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
      unfold SBr, SHADOW_OFF, x_F, FRAME, T_FLO in *.
      repeat split; lia.
    + (* the tests of sext.w a1 against 1 and 0 *)
      destruct Hv as [Hv | Hv]; rewrite Hv in E11c |- *; unfold t_cst; cbn [Z.eqb Pos.eqb conds_ok].
      * split; [apply (t_cond_ok _ 0 BC_NE 1 E11c); t_cond_side|].
        split; [apply (t_cond_ok _ 0 BC_EQ 0 E11c); t_cond_side | exact I].
      * split; [apply (t_cond_ok _ 1 BC_EQ 1 E11c); t_cond_side | exact I]. }
remember (cut_env x regs2 []) as E eqn:HE.
assert (HEc : forall n, (n < 43)%nat -> ew E n = ew (cut_env x regs2 []) n) by (intros n _; subst E; reflexivity).
assert (E8 : ew E 8 = Z_to_bv 64 (x_Q x)) by (subst E; rewrite (cut_env_reg x regs2 [] 8 8%bv eq_refl); exact H8).
assert (E11 : ew E 11 = Z_to_bv 64 v) by (subst E; exact E11c).
assert (E19 : ew E 19 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (cut_env_reg x regs2 [] 19 19%bv eq_refl); exact H19).
assert (B2 : bv_unsigned (ew E 2) = x_F x) by (subst E; rewrite (cut_env_reg x regs2 [] 2 2%bv eq_refl); exact G2).
assert (B8 : bv_unsigned (ew E 8) = x_Q x) by (subst E; rewrite (cut_env_reg x regs2 [] 8 8%bv eq_refl); exact G8).
clear HE E11c.
(* the shadow entry of Q's 4 bytes: they are marked usable (call_ok), so the check at 0x834a8 .. 0x83674 passes and
   the error-path call at 0x8367c is not reached *)
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
(* 0x83488 .. 0x835c4: the beq / bnez on sext.w a1 decided from the entry conditions, the trap branches 0x8349c /
   0x834a4 decided from atom 8's fact, the check of Q passes, sw a1,0(s0), a0 = 1, the epilogue; the run stops at
   the ret. The two values of v give two concrete entry states (one run each). *)
destruct Hv as [Hvc | Hvc]; rewrite Hvc in HS.
- aj_run_tok parse_tbl_ok HS HJ SHOK RTBspan.
  + lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fp b0 bc ly own) end.
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (x_F x - x_sp0 x));
    [reflexivity | rewrite B2; lia | cbn [YP09.r_wlo]; unfold x_F, FRAME, T_parse_STK, ESTACK in *; lia
    | cbn [YP09.r_whi]; unfold x_F, FRAME in *; lia |].
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 8%nat (x_Q x)); [reflexivity | exact B8 | |].
    * cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply HQw. lia.
    * apply awr_ok_nil.
  + (* the bytes the run may write: the frame (in the callee's stack) and Q *)
    lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
      pose proof (kept_run (fun a => (x_sp x - T_parse_STK <= a < x_sp x) \/ (x_Q x <= a < x_Q x + 4))
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
      pose proof (val_of_chunk_ok rsegs E' _ _ 0 4%N (SOff 11 0) v Hc
        ltac:(rewrite sv_denot_SOff0, HAg by lia; exact E11) ltac:(rewrite Hvc; cbn; lia) ltac:(cbn; lia)) as VQ;
      rewrite HAg, B8, Z.add_0_r in VQ by lia;
      eapply (SRr_ret_at rsegs parse_tbl parse_tbl_ok parse_wx (x_W x) E'); [exact HS' | reflexivity | vm_compute; reflexivity |]
    end.
    intros mat'. rewrite LR1, Hra. apply HL.
    * eapply ajournal_materialize; first [exact LAWS | exact Hsegs | exact HJ].
    * let rec kio := first [ exact Hio | apply same_io_refl
        | eapply same_io_trans; [| apply same_io_wvb]; kio ] in kio.
    * exact Hpr.
    * intros a Ha Hn1 Hn2. apply KS; [exact Ha|]. intros [Hz | Hz]; [exact (Hn1 Hz)|].
      apply Hn2. split; [rewrite Hvc; cbv; intros Hn; discriminate Hn | exact Hz].
    * rewrite R10, denot_lit_U, U_lit by lia. rewrite Hvc. reflexivity.
    * rewrite Hvc in VQ |- *. exact VQ.
- aj_run_tok parse_tbl_ok HS HJ SHOK RTBspan.
  + lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fp b0 bc ly own) end.
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (x_F x - x_sp0 x));
    [reflexivity | rewrite B2; lia | cbn [YP09.r_wlo]; unfold x_F, FRAME, T_parse_STK, ESTACK in *; lia
    | cbn [YP09.r_whi]; unfold x_F, FRAME in *; lia |].
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 8%nat (x_Q x)); [reflexivity | exact B8 | |].
    * cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply HQw. lia.
    * apply awr_ok_nil.
  + lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
      pose proof (kept_run (fun a => (x_sp x - T_parse_STK <= a < x_sp x) \/ (x_Q x <= a < x_Q x + 4))
        _ _ _ _ _ _ KE HFr) as KS end.
    lazymatch type of KS with ?P -> _ => assert (KW : P) by (t_inwr B2 B8) end.
    specialize (KS KW). clear KW KE.
    lazymatch goal with HS' : st_ok _ ?E' ?ss' (restrict _ ?ms') |- _ =>
      assert (HAg : forall n, (n < 43)%nat -> ew E' n = ew E n) by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity);
      t_r10 R10;
      destruct (leaf_regs B x regs2 [] E' ss' ms' (w_H (x_W x)) Hpre HS'
        ltac:(intros n Hn; rewrite HAg by exact Hn; apply HEc; exact Hn) ltac:(vm_compute; reflexivity) H2 Hcs) as [Hpr LR1];
      pose proof (st_ok_mem_ok rsegs _ _ _ HS') as (_ & HM & _);
      cbn [ss_mem] in HM;
      apply Forall_cons_iff in HM as [_ HM]; apply Forall_cons_iff in HM as [HQr _];
      destruct HQr as (_ & _ & _ & HC);
      cbn [YP09.r_base YP09.r_chunks base_val] in HC;
      apply Forall_cons_iff in HC as [Hc _];
      pose proof (val_of_chunk_ok rsegs E' _ _ 0 4%N (SOff 11 0) v Hc
        ltac:(rewrite sv_denot_SOff0, HAg by lia; exact E11) ltac:(rewrite Hvc; cbn; lia) ltac:(cbn; lia)) as VQ;
      rewrite HAg, B8, Z.add_0_r in VQ by lia;
      eapply (SRr_ret_at rsegs parse_tbl parse_tbl_ok parse_wx (x_W x) E'); [exact HS' | reflexivity | vm_compute; reflexivity |]
    end.
    intros mat'. rewrite LR1, Hra. apply HL.
    * eapply ajournal_materialize; first [exact LAWS | exact Hsegs | exact HJ].
    * let rec kio := first [ exact Hio | apply same_io_refl
        | eapply same_io_trans; [| apply same_io_wvb]; kio ] in kio.
    * exact Hpr.
    * intros a Ha Hn1 Hn2. apply KS; [exact Ha|]. intros [Hz | Hz]; [exact (Hn1 Hz)|].
      apply Hn2. split; [rewrite Hvc; cbv; intros Hn; discriminate Hn | exact Hz].
    * rewrite R10, denot_lit_U, U_lit by lia. rewrite Hvc. reflexivity.
    * rewrite Hvc in VQ |- *. exact VQ.
Qed.

(* v not in {0, 1}: -1 is returned, nothing is stored *)
Lemma T_walk_sk : forall x v regs2 mem2 md2 (Post : world rsegs -> config -> Prop),
pre_ok B x -> FI B x regs2 mem2 md2 -> getr regs2 11 = w64 v -> - 2 ^ 31 <= v < 2 ^ 31 -> v <> 0 -> v <> 1 ->
t_leaf x v Post ->
SRr rsegs (x_W x) (cfg_at rsegs PC_T regs2 mem2 md2) Post.
Proof.
intros x v regs2 mem2 md2 Post Hpre HFI H11 Hv Hv0 Hv1 HL.
pose proof (t_q_facts x regs2 mem2 md2 Hpre HFI) as (HQ0 & HQ47 & _).
pose proof (t_cut_regs x regs2 mem2 md2 Hpre HFI HQ0 HQ47) as (G2 & HF0 & HF47 & HFal & _ & G19).
pose proof (pre_stack B x Hpre) as (Hceil & Hsp & H47 & Hal & Hwin).
pose proof Hpre as ((_ & Hra & _) & _).
pose proof HFI as (HJ & Hio & HK & _ & H2 & Hcs & H8 & H19).
pose proof parse_wx as Hwx. pose proof parse_segs_low as Hsegs.
assert (Hfr : Role.flag_rc v = (None, -1)).
{ unfold Role.flag_rc. destruct (Z.eqb_spec v 0); [lia|]. destruct (Z.eqb_spec v 1); [lia|]. reflexivity. }
assert (E11c : ew (cut_env x regs2 []) 11 = Z_to_bv 64 v) by (rewrite (cut_env_reg x regs2 [] 11 11%bv eq_refl); exact H11).
(* the entry state *)
assert (HS : st_ok rsegs (cut_env x regs2 []) ss_t_sk
  (restrict (w_H (x_W x)) (mkst regs2 (Z_to_bv 64 PC_T) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_t_sk, cut_env. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold t_rs_sk. apply Forall_cons; [|apply Forall_nil].
    exact (frame_region_ok B x regs2 mem2 md2 [] [] HFI Hpre (Forall_nil _)).
  - unfold t_rs_sk. cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  - unfold facts_ok, t_G_sk. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [|split; [|exact I]].
    + unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), (ew_Ereg_nat regs2 _ 19 19%bv eq_refl), G2, G19.
      change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
      unfold SBr, SHADOW_OFF, x_F, FRAME, T_FLO in *.
      repeat split; lia.
    + (* the tests of sext.w a1 against 1 and 0: both unequal *)
      split; [apply (t_cond_ok _ v BC_NE 1 E11c); t_cond_side|].
      split; [apply (t_cond_ok _ v BC_NE 0 E11c); t_cond_side | exact I]. }
remember (cut_env x regs2 []) as E eqn:HE.
assert (HEc : forall n, (n < 43)%nat -> ew E n = ew (cut_env x regs2 []) n) by (intros n _; subst E; reflexivity).
assert (B2 : bv_unsigned (ew E 2) = x_F x) by (subst E; rewrite (cut_env_reg x regs2 [] 2 2%bv eq_refl); exact G2).
clear HE E11c.
assert (SHOK : sh_ok rsegs PBx [] E (mrestrict (w_H (x_W x)) mem2)) by apply Forall_nil.
unfold cfg_at. change (w64 PC_T) with (Z_to_bv 64 PC_T).
(* 0x83488 .. 0x835c4: the beq falls through and the bnez is taken (the entry conditions), a0 = -1, the epilogue;
   the run stops at the ret *)
aj_run_tok parse_tbl_ok HS HJ SHOK RTBspan.
- lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fp b0 bc ly own) end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (x_F x - x_sp0 x));
  [reflexivity | rewrite B2; lia | cbn [YP09.r_wlo]; unfold x_F, FRAME, T_parse_STK, ESTACK in *; lia
  | cbn [YP09.r_whi]; unfold x_F, FRAME in *; lia |].
  apply awr_ok_nil.
- lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    pose proof (kept_run (fun a => x_sp x - T_parse_STK <= a < x_sp x)
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
      | eapply same_io_trans; [| apply same_io_wvb]; kio ] in kio.
  + exact Hpr.
  + intros a Ha Hn1 _. exact (KS a Ha Hn1).
  + rewrite R10, Hfr, denot_lit_U, U_lit by lia. cbn [snd]. unfold w64. apply bv_eq.
    rewrite !Z_to_bv_unsigned. reflexivity.
  + rewrite Hfr. exact I.
Qed.

Lemma T_walk : forall x v regs2 mem2 md2 (Post : world rsegs -> config -> Prop),
pre_ok B x -> FI B x regs2 mem2 md2 -> getr regs2 11 = w64 v -> - 2 ^ 31 <= v < 2 ^ 31 -> t_leaf x v Post ->
SRr rsegs (x_W x) (cfg_at rsegs PC_T regs2 mem2 md2) Post.
Proof.
intros x v regs2 mem2 md2 Post Hpre HFI H11 Hv HL.
destruct (Z.eq_dec v 0) as [Hv0 | Hv0]; [apply (T_walk_st x v regs2 mem2 md2 Post Hpre HFI H11 (or_introl Hv0) HL)|].
destruct (Z.eq_dec v 1) as [Hv1 | Hv1]; [apply (T_walk_st x v regs2 mem2 md2 Post Hpre HFI H11 (or_intror Hv1) HL)|].
exact (T_walk_sk x v regs2 mem2 md2 Post Hpre HFI H11 Hv Hv0 Hv1 HL).
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
destruct HT as (HFI & H11 & Hv & Hfx & Hres).
pose proof (pre_ok_fx fx2 x Hpre (proj2 Hfx)) as Hpre2.
apply (@T_walk fx2 rc SK B LAWS x v regs2 mem2 md2 (@PPOST fx rc SK B MT x false) Hpre2 HFI H11 Hv).
unfold t_leaf. intros regsF memF md3 HJ Hio Hpr HK HR10 HRQ.
assert (Hr : rl_parse_res false (x_bs x) = Role.flag_rc v) by exact Hres.
apply (@ppost_intro fx rc SK B MT MTL x false fx2 regsF memF md3 HJ Hio Hpr Hfx); rewrite Hr; assumption.
Qed.
End b.
