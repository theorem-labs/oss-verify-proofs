(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgParseT.v at afaa3cb55c1d; for
   reac-pw/fuzz_rate's reac_rate_prop_parse at image A: module paths and names are rate's, the pcs are those of
   fuzz_rate.asan, the range test of v and its return of -1 are removed (rate's T has no test: role's T_walk_sk, its
   entry state and the split of T_walk go), the store writes v mod 2^32 at Q and returns 1 (val_of_chunk_mod is new). *)
(* reac_rate_prop_parse's segment T (lib/A/RtPgParseBase.v segT_stmt): the store of the value v at Q from the cut T
   0x847d0 to the `ret` 0x848c8, on reac-pw/fuzz_rate's ASan image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, the same loaded bytes).
   The code from T (a0 = the 64-bit word of the integer v, -2^31 <= v < 2^31, s0 = Q, s3 = SHADOW_OFF, sp = F):
     0x847d0 srli a1,s0,3; 0x847d4 add a1,a1,s3; 0x847d8 lb a1,0(a1); 0x847dc bnez a1 -> 0x8495c (the instrumented
     check of the 4 bytes at Q; the slow path 0x8495c andi a2,s0,7 / 0x84960 addi a2,a2,3 / 0x84964 blt a2,a1 ->
     0x847e0, else 0x84968 mv a0,s0 and the error-path call 0x8496c jal 0x58dd8); 0x847e0 sw a0,0(s0);
     0x847e4 addi a1,zero,1; 0x847e8 j 0x84898; 0x84898 mv a0,a1; 0x8489c .. 0x848c0 the ten saved words back;
     0x848c4 addi sp,sp,0x60; 0x848c8 ret.
   There is no test of v: the code stores every v. The entry state holds the frame region, a writable region of 4
   bytes at Q (atom 8) and the shadow entry of Q's 4 bytes (from call_ok's range_addressable Q 4: the bytes are marked
   usable; unchanged at the cut, as Q's shadow bytes lie below the allocator's ceiling, so outside the callee's
   stack). With that entry the shadow engine passes the check, so the error path is not reached; the run stores the
   low 4 bytes of a0 at Q (v mod 2^32) and returns 1. The run is an engine run on the concrete image (aj_run_tok) at
   the float state the cut gives (T_ok runs at fx2; the walk below is generic in its float state). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YK0o YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Rate.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import Img0 RtPgBase RtPgCSpec RtPgParseBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------- the entry state ---------------------------------- *)
(* the int cell: 4 writable bytes at s0 = Q (atom 8) *)
Definition q_region : YP09.region := YP09.mkRegion (Some 8%nat) 0 4 0 4 [].
(* the lowest F can be: the allocator's ceiling at its least (CEIL_MIN) *)
Definition T_FLO : Z := 0x7fff7f800000.
Definition t_rs : smem := [frame_region []; q_region].
(* atoms: F (sp), Q (s0) and SHADOW_OFF (s3) *)
Definition t_G : facts :=
mkFacts [(2%nat, mkAF T_FLO (2 ^ 47) 4); (8%nat, mkAF 0 (2 ^ 47 - 4) 2); (19%nat, mkAF SBr SBr 0)] [] [].
Definition t_SH : list shent := [mkSHE 8 0 4].
Definition ss_t : sstate := mkSS PC_T sr_atoms t_rs None t_G.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.

(* the n bytes a chunk CVal n e holds: the low n bytes of the word e denotes, so v mod 2 ^ (8 n) for every integer v
   whose 64-bit word that is (v may be negative) *)
Lemma val_of_chunk_mod : forall E mem base off (n : N) (e : sv) v,
YP09.chunk_ok rsegs E mem base (YP09.mkChunk off (CVal n e)) ->
sv_denot E e = Z_to_bv 64 v -> Z.of_N n <= 8 ->
val_mem rsegs mem (base + off) (N.to_nat n) (v mod 2 ^ (8 * Z.of_N n)).
Proof.
intros E mem base off n e v H He Hn k Hk. unfold YP09.chunk_ok in H.
cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len] in H.
pose proof (N_nat_Z n) as Hnn.
destruct (H (Z.of_nat k) ltac:(lia)) as (b & Hb1 & Hb2). cbn [YP09.cbyte] in Hb1. rewrite He in Hb1.
injection Hb1 as <-. rewrite Hb2. f_equal.
unfold YP09.byte_of_word, YO0f.le_byte. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with (2 ^ 8). change (2 ^ Z.of_N 64) with (2 ^ 64). change 256 with (2 ^ 8).
rewrite Hnn. rewrite !Z.mod_mod by (apply Z.pow_nonzero; lia).
apply Z.bits_inj'. intros i Hi.
destruct (Z.lt_ge_cases i 8) as [Hi8 | Hi8].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite !Z.mod_pow2_bits_low by lia.
  reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* what the walk's leaf must give, for the post Post of the call: a0 = 1 and v mod 2^32 at Q *)
Definition t_leaf (x : pctx) (v : Z) (Post : world rsegs -> config -> Prop) : Prop :=
forall regsF memF md3,
ajournal rsegs B (x_STK x) (x_sp0 x) (x_FP x) (x_ly x) (x_S x) (x_W0 x) (x_mem0 x) (x_md0 x) (x_own x)
(x_lyc x) (x_Sc x) (x_W x) memF md3 (x_k x) ->
same_io (x_mdc x) md3 ->
aregs_preserved (x_regs x) regsF ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp x - T_parse_STK <= a < x_sp x) -> ~ (x_Q x <= a < x_Q x + 4) ->
 aview rsegs (w_H (x_W x)) memF a = aview rsegs (w_H (x_W x)) (x_memc x) a) ->
getr regsF 10 = w64 1 ->
val_mem rsegs (mrestrict (w_H (x_W x)) memF) (x_Q x) 4 (v mod 2 ^ 32) ->
Post (x_W x) (mkCfg (mkst regsF (getr (x_regs x) 1) memF (seg_rom rsegs)) md3).

(* Q's 4 bytes at the cut: in the caller's stack window or in a side-stack frame the caller holds (rt_wcell), so
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

(* the check of Q passes, the low 4 bytes of v are stored at Q, 1 is returned *)
Lemma T_walk : forall x v regs2 mem2 md2 (Post : world rsegs -> config -> Prop),
pre_ok B x -> FI B x regs2 mem2 md2 -> getr regs2 10 = w64 v -> t_leaf x v Post ->
SRr rsegs (x_W x) (cfg_at rsegs PC_T regs2 mem2 md2) Post.
Proof.
intros x v regs2 mem2 md2 Post Hpre HFI H10 HL.
pose proof (t_q_facts x regs2 mem2 md2 Hpre HFI) as (HQ0 & HQ47 & HQp & HQapp & HQw).
pose proof (t_q_ra x regs2 mem2 md2 Hpre HFI HQ0 HQ47) as HRA2.
pose proof (t_cut_regs x regs2 mem2 md2 Hpre HFI HQ0 HQ47) as (G2 & HF0 & HF47 & HFal & G8 & G19).
pose proof (pre_stack B x Hpre) as (Hceil & Hsp & H47 & Hal & Hwin).
pose proof Hpre as ((_ & Hra & _) & _ & _ & _ & (_ & HQsp) & HQ4 & _).
pose proof HFI as (HJ & Hio & HK & _ & H2 & Hcs & H8 & H19).
pose proof parse_wx as Hwx. pose proof parse_segs_low as Hsegs.
(* the entry state *)
assert (HS : st_ok rsegs (cut_env x regs2 []) ss_t
  (restrict (w_H (x_W x)) (mkst regs2 (Z_to_bv 64 PC_T) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_t, cut_env. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold t_rs. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + exact (frame_region_ok B x regs2 mem2 md2 [] [] HFI Hpre (Forall_nil _)).
    + unfold region_ok, q_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl), G8.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable rsegs). apply HQp. lia.
  - unfold t_rs, frame_region, q_region. cbn [pairwise_disjoint all_disjoint].
    unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), (ew_Ereg_nat regs2 _ 8 8%bv eq_refl), G2, G8.
    refine (conj (conj _ I) (conj I I)). unfold x_F, FRAME, T_parse_STK, ESTACK in *. lia.
  - unfold facts_ok, t_G. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2].
    rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), (ew_Ereg_nat regs2 _ 8 8%bv eq_refl),
      (ew_Ereg_nat regs2 _ 19 19%bv eq_refl), G2, G8, G19.
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
(* the shadow entry of Q's 4 bytes: they are marked usable (call_ok), so the check at 0x847d0 .. 0x84964 passes and
   the error-path call at 0x8496c is not reached *)
assert (SHOK : sh_ok rsegs PBx t_SH E (mrestrict (w_H (x_W x)) mem2)).
{ unfold sh_ok, t_SH. apply Forall_cons; [|apply Forall_nil].
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
(* 0x847d0 .. 0x848c8: the check of Q passes, sw a0,0(s0), a1 = 1, the epilogue; the run stops at the ret *)
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
    pose proof (kept_run (fun a => (x_sp x - T_parse_STK <= a < x_sp x) \/ (x_Q x <= a < x_Q x + 4))
      _ _ _ _ _ _ KE HFr) as KS end.
  lazymatch type of KS with ?P -> _ => assert (KW : P) by (t_inwr B2 B8) end.
  specialize (KS KW). clear KW KE.
  lazymatch goal with HS' : st_ok _ ?E' ?ss' (restrict _ ?ms') |- _ =>
    assert (HAg : forall n, (n < 43)%nat -> ew E' n = ew E n) by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity);
    t_r10 R10;
    destruct (leaf_regs B x regs2 [] E' ss' ms' (w_H (x_W x)) Hpre HS'
      ltac:(intros n Hn; rewrite HAg by exact Hn; apply HEc; exact Hn) ltac:(vm_compute; reflexivity) H2 Hcs) as [Hpr LR1];
    (* the 4 bytes at Q: the chunk the store left, the low 4 bytes of a0 *)
    pose proof (st_ok_mem_ok rsegs _ _ _ HS') as (_ & HM & _);
    cbn [ss_mem] in HM;
    apply Forall_cons_iff in HM as [_ HM]; apply Forall_cons_iff in HM as [HQr _];
    destruct HQr as (_ & _ & _ & HC);
    cbn [YP09.r_base YP09.r_chunks base_val] in HC;
    apply Forall_cons_iff in HC as [Hc _];
    pose proof (val_of_chunk_mod E' _ _ 0 4%N (SOff 10 0) v Hc
      ltac:(rewrite sv_denot_SOff0, HAg by lia; exact E10) ltac:(cbn; lia)) as VQ;
    rewrite HAg, B8, Z.add_0_r in VQ by lia;
    eapply (SRr_ret_at rsegs parse_tbl parse_tbl_ok parse_wx (x_W x) E'); [exact HS' | reflexivity | vm_compute; reflexivity |]
  end.
  intros mat'. rewrite LR1, Hra. apply HL.
  + eapply ajournal_materialize; first [exact LAWS | exact Hsegs | exact HJ].
  + let rec kio := first [ exact Hio | apply same_io_refl
      | eapply same_io_trans; [| apply same_io_wvb]; kio ] in kio.
  + exact Hpr.
  + intros a Ha Hn1 Hn2. apply KS; [exact Ha|]. intros [Hz | Hz]; [exact (Hn1 Hz) | exact (Hn2 Hz)].
  + rewrite R10, denot_lit_U, U_lit by lia. reflexivity.
  + exact VQ.
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
destruct HT as (HFI & H10 & _ & Hfx & Hres).
pose proof (pre_ok_fx fx2 x Hpre (proj2 Hfx)) as Hpre2.
apply (@T_walk fx2 rc SK B LAWS x v regs2 mem2 md2 (@PPOST fx rc SK B MT x false) Hpre2 HFI H10).
unfold t_leaf. intros regsF memF md3 HJ Hio Hpr HK HR10 HRQ.
assert (Hr : Rate.harness_parse false (x_bs x) = (Some v, 1)) by exact Hres.
apply (@ppost_intro fx rc SK B MT MTL x false fx2 regsF memF md3 HJ Hio Hpr Hfx); rewrite Hr; cbn [fst snd].
- intros a Ha Hn1 Hn2. apply HK; [exact Ha | exact Hn1 |]. intros Hq. apply Hn2. split; [|exact Hq].
  let Hn := fresh "Hn" in intros Hn; discriminate Hn.
- exact HR10.
- exact HRQ.
Qed.
End b.
