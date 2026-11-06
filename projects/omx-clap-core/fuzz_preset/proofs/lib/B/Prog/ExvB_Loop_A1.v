(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Does not rest on tex_word_specX. Old-pin kit 4f18c75d4900: carries EXB's memnorm keep (exv_rm's second half,
   exvl_P (e_mem E)) across the runs to KIT_RUNs's memnorm premise at LK. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B, ex_value, segment CL piece A1, the KID FETCH: exvl_A1 proves
   CUT_CLm n m (B 0x83a60 = exv_pc 0x534) from CUT_LK n m (B 0x83b1c = exv_pc 0x5f0), both at every float state,
   over B's listing with the table engine (SRr_run_to_tok_AJx_inv over B_prog_tbl with P := exvl_P (e_mem E),
   ExvB_Loop_exw.v's idioms), from the seats of
   ExvB_Loop_a1_seat.v. Three arms, one engine lemma each, then one LK step (a1_fin: EXBs by KIT_RUNs, CUT_LK):
   - A a1_run0 (vv = 152(s1) = 0, B 0x83a60-0x83a64, 0x83b14-0x83b18): s4 = 0, s8 = 1, nothing written;
   - B a1_runL (vv <> 0, i >= count, B 0x83a60-0x83a84, 0x83af4-0x83b10): the node's count read under its shadow
     check (B 0x83a78 not taken: KIT_NODE's range_addressable), the shadow of in->differs (B 0x83afc not taken:
     EXB's range_addressable q 40, so the slow path B 0x83d50 / report B 0x83d54 is unreachable), s4 = 0, s8 = 1,
     sw s8, 0(q + 32): in->differs := 1; the bookkeeping by PURE_PREF_LONG;
   - C a1_runK (vv <> 0, i < count, B 0x83a60-0x83af0): count and kids read under their shadow checks (B 0x83a78,
     0x83a98 not taken), the three UBSan checks of the kid address kids + 56 i not taken (B 0x83abc decided by the
     engine from the seat's kids fact, B 0x83ac0 pointer wrap refuted by a1_U_kid, B 0x83adc mulh overflow refuted by
     a1_U_mulh / a1_U_sra; KIT_NODE: 4096 <= kids, kids + 56 count <= alloc_ceiling; i <= len <= 3 * 2 ^ 20),
     beqz kids decided by the same fact, s8 = 0, s4 = kids + 56 i (exv_child); the bookkeeping by PURE_PREF_CONS.
   The parent node is apart from the shadow band, from ex_value's frame and from the cursor (a1_node: its home is a
   Lam block or a live fake frame, inside the application range, or the caller's stack above alloc_ceiling).
   Rule 24: proves no function (kind: segment lemma).
   Numerals: 9, 19, 20, 22-27 (WORD: register numbers s1, s3, s4, s6, s7, s8, s9, s10, s11); 2, 3, 4, 8, 18
   (WORD: register numbers of EXB); 8 .. 176, 288, 319 (LENGTH: B's spill slots and ex_value's frame); 24, 32, 36,
   40, 56 (LENGTH: pj node fields / node size, in->differs and its 4 bytes, struct ex); 0x534, 0x5f0 (DERIVED: cut
   offsets); 539420 (DERIVED: exv_pc 0x5f0 computed, the engine state's literal pc at LK); 16688
   (DERIVED: STK_ex_value 0 computed); 3145728 = 3 * 2 ^ 20 (LENGTH: the text bound of EXV_PRE); 4096, 2 ^ 47,
   2 ^ 63, 2 ^ 64, 2 ^ 32, 17592186044416 = 2 ^ 44 (LENGTH: address-space / shadow-band bounds); 63, 3, 1, 0 (WORD:
   shift amounts and literals of the code); 91, 123, 5, 6 (WORD: ASCII / tree tags of the statements). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames FCiface YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import
ExvB_Stmt ExvB_Loop_kit ExvB_Loop_Stmt ExvB_Open_sh ExvB_Open_kt ExvB_Loop_a1_seat ExvB_Loop_exw.
Import ListNotations.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

(* the LK pc as a literal (the engine's states carry literals) *)
Lemma a1_lk_eq : exv_pc 0x5f0 = 539420.
Proof. vm_compute. reflexivity. Qed.

(* the registers the fetch leaves alone (EXB's, s8 excepted, plus s6 / s7 / s11 of the cut) *)
Definition A1_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 22; 23; 25; 26; 27]%bv.

(* ---- the table-engine idioms of ExvB_Loop_exw.v (the _inv forms: HPM carried), at this piece's table ---- *)
Ltac a1_after HS HJ SHOK HPM :=
let ws := fresh "ws" in let ms' := fresh "ms" in let mat' := fresh "mat" in
let Hlen := fresh "Hlen" in let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in
intros ws ms' mat' Hlen HS SHOK HJ HPM HF HFr HG;
cbn [sh_j sh_ss] in Hlen, HS, SHOK;
repeat (let w := fresh "w" in
destruct ws as [|w ws]; [discriminate Hlen | cbn [length] in Hlen; apply eq_add_S in Hlen || injection Hlen as Hlen]);
(destruct ws; [clear Hlen | discriminate Hlen]);
cbn [extK length Nat.add] in HS, SHOK;
cbn [ms_mem mkst] in HF, HFr, HG, HJ, HPM;
try match type of HS with context [restrict _ ?msn] =>
repeat match goal with
| old : machine_state |- _ => lazymatch old with msn => fail | _ => clear old end
end
end;
srr_norm_model.
Ltac a1_run RUN HS HJ SHOK HPM :=
lazymatch type of HS with
| st_ok ?sg ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
let K := eval vm_compute in (run_K 0 Bx SH ss) in
let r := eval vm_compute in (sym_runN_tok sg A1_TBL K Bx BAND_SPAN SH FUEL ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_tok sg A1_TBL K Bx BAND_SPAN SH FUEL ss = (st', rs)) by (vm_compute; reflexivity);
eapply (RUN W FUEL E K Bx BAND_SPAN SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS SHOK
ltac:(vm_compute; reflexivity) Hrun I HJ HPM);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK HPM; try match type of ms with machine_state => clear ms | _ => idtac end;
a1_after HS HJ SHOK HPM ]
end end
end.
Ltac a1_runto RUNTO HS HJ SHOK HPM stop :=
lazymatch type of HS with
| st_ok ?sg ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
let K := eval vm_compute in (run_K 0 Bx SH ss) in
let r := eval vm_compute in (sym_run_toN_tok sg A1_TBL K Bx BAND_SPAN SH FUEL stop ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_tok sg A1_TBL K Bx BAND_SPAN SH FUEL stop ss = (st', rs)) by (vm_compute; reflexivity);
eapply (RUNTO W FUEL stop E K Bx BAND_SPAN SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS SHOK
ltac:(vm_compute; reflexivity) Hrun I HJ HPM);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK HPM; try match type of ms with machine_state => clear ms | _ => idtac end;
a1_after HS HJ SHOK HPM ]
end end
end.
Ltac a1_branch HS SHOK :=
lazymatch type of HS with
| st_ok ?sg ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
let K := eval vm_compute in (run_K 0 Bx SH ss) in
let r := eval vm_compute in (snd (sym_runN_tok sg A1_TBL K Bx BAND_SPAN SH 1 ss)) in
lazymatch r with
| TS_stopped (SR_branch ?c ?a ?b) =>
apply (SRr_sym_branch sg W E ss ms _ _ c a b HS); clear HS;
let Hc := fresh "Hc" in intros Hc HS
| _ => fail "a1_branch: not stuck at a branch:" r
end end
end.
Ltac a1_kept HFr Zs ev :=
lazymatch type of HFr with frame_of ?E ?rs (mrestrict ?H ?m) (mrestrict _ ?m') =>
let KP := fresh "KEPT" in
assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview rsegs H m' a = aview rsegs H m a);
[ apply (exw_kept rsegs E rs H m m' Zs HFr); intros b_ wlo_ whi_ a0_ Hin_ Hrr_; vm_compute in Hin_;
repeat (destruct Hin_ as [Hq_ | Hin_]; [injection Hq_ as <- <- <-; cbn [base_val] in Hrr_; ev Hrr_; cbv beta; lia|]);
destruct Hin_
| cbv beta in KP ]
end.

(* ---- the stack need of ex_value at any nesting (its frame plus the deepest callee) ---- *)
Lemma a1_stk0 : @STK_ex_value prh_img_B 0 = 16688.
Proof. vm_compute. reflexivity. Qed.
Lemma a1_stk : forall n : nat, 16688 <= @STK_ex_value prh_img_B n.
Proof.
intros n. rewrite <- a1_stk0. unfold STK_ex_value.
assert (HF : 0 <= @pi_frame prh_img_B F_ex_value) by (vm_compute; discriminate).
assert (H1 : 1 <= Z.of_nat (S n)) by lia.
nia.
Qed.

Section x. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis HYP : EXV_HYP B ARx SK.
Hypothesis KRUN : forall fx : YK11.FPState, KIT_RUNs (fx := fx) B ARx SK.
Hypothesis KNODE : forall fx : YK11.FPState, KIT_NODE (fx := fx) B ARx SK.
Hypothesis PCONS : PURE_PREF_CONS.
Hypothesis PLONG : PURE_PREF_LONG.

(* the premises of EXV_PRE this piece reads *)
Lemma a1_pre : forall E, EXV_PRE B ARx E ->
  ARx (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) /\
  alloc_ceiling + exv_STK E <= exv_sp E /\ 0 <= e_d E /\ exv_sp E + e_d E <= 2 ^ 47 /\
  exv_sp E <= e_q E /\ e_q E + 40 <= exv_sp E + e_d E /\ e_q E mod 8 = 0 /\
  (e_v E = 0 \/ forall z, PRH_Reader.pj_footR (e_v E) (e_D E) z ->
     ~ (e_q E <= z < e_q E + 40) /\ ~ (exv_sp E - exv_STK E <= z < exv_sp E)).
Proof.
intros E HP. unfold EXV_PRE in HP. cbv zeta in HP.
destruct HP as (HFP & _ & _ & _ & _ & _ & Hq8 & _ & Hspq & Hqd & Hwin & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & Htree & _).
destruct HFP as (HFN & _). destruct HFN as (HAR & _ & _ & _ & _ & Hastk & _).
destruct Hastk as (_ & HSTK0 & Hceil & Hslo & _ & H47 & _ & _ & Htop2).
destruct Hwin as (Hd0 & _ & Htop & _).
assert (A1 : alloc_ceiling + exv_STK E <= exv_sp E) by (unfold exv_sp; clear - Hceil Hslo; lia).
assert (A2 : exv_sp E + e_d E <= 2 ^ 47) by (unfold exv_sp in *; clear - Htop H47 Htop2; lia).
split; [exact HAR|]. split; [exact A1|]. split; [exact Hd0|]. split; [exact A2|].
split; [exact Hspq|]. split; [exact Hqd|]. split; [exact Hq8|].
destruct Htree as [Hv0 | (_ & _ & HDJ)]; [left; exact Hv0|].
right. intros z Hz. destruct (HDJ z Hz) as (_ & Hq & Hsp & _). split; [exact Hq | exact Hsp].
Qed.

(* the frame geometry: s1 sits inside ex_value's own stack window, below the cursor *)
Lemma a1_geo : forall E, EXV_PRE B ARx E ->
  alloc_ceiling <= exv_s1 E /\ exv_s1 E + 176 <= exv_sp E /\ exv_sp E - exv_STK E <= exv_s1 E /\
  exv_s1 E + 176 <= e_q E /\ alloc_ceiling <= e_q E /\ e_q E + 40 <= 2 ^ 47 /\ e_q E mod 8 = 0 /\
  exv_sp E + e_d E <= 2 ^ 47 /\ 0 <= e_d E /\ exv_s1 E + 176 <= 2 ^ 47 /\
  exv_sp E <= e_q E /\ e_q E + 40 <= exv_sp E + e_d E.
Proof.
intros E HP. destruct (a1_pre E HP) as (_ & Hsp & Hd0 & Hd47 & Hspq & Hqd & Hq8 & _).
pose proof (exv_s1_le E) as ((S1a & S1b) & _).
pose proof (a1_stk (e_n E)) as HSTK.
pose proof alloc_ceiling_val as (AC1 & AC2).
unfold exv_STK in *. clear HP.
repeat split; clear - Hsp Hd0 Hd47 Hspq Hqd Hq8 S1a S1b HSTK AC1 AC2; lia.
Qed.

(* the parent node: inside the application range, so apart from the shadow band; apart from ex_value's frame and
   from the cursor (its home is a Lam block, a live fake frame or the caller's stack) *)
Lemma a1_node : forall (fx : YK11.FPState) E lyc Sc Hpc Wc regs memc mdc k pos,
  EXV_PRE B ARx E -> EXB (fx := fx) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos -> e_v E <> 0 ->
  4096 <= e_v E /\ e_v E + 56 <= 2 ^ 47 /\
  (forall x, e_v E <= x < e_v E + 56 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)) /\
  (forall x, e_v E <= x < e_v E + 56 -> ~ (exv_s1 E <= x < exv_sp E) /\ ~ (e_q E <= x < e_q E + 40)).
Proof.
intros fx E lyc Sc Hpc Wc regs memc mdc k pos HPRE HB Hv.
pose proof (eh_laws B ARx SK HYP) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@cf_head_nonneg cp) as CH0.
pose proof (a1_geo E HPRE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
destruct (a1_pre E HPRE) as (_ & _ & _ & _ & _ & _ & _ & [Hv0 | HDJ]); [exfalso; exact (Hv Hv0)|].
assert (H47e : ly_stk_hi (e_ly E) <= 2 ^ 47).
{ unfold EXV_PRE in HPRE. cbv zeta in HPRE. destruct HPRE as (HFP & _).
  destruct HFP as (HFN & _). destruct HFN as (_ & _ & _ & _ & _ & Hastk & _).
  destruct Hastk as (_ & _ & _ & _ & _ & H47 & _). exact H47. }
unfold EXB in HB. cbv zeta in HB.
destruct HB as (HJ & HWIN & HFR & HFZ & HHp & HAB & HRM & HLED & HCNT & R2 & R8 & R9 & R18 & R24 & R25 & R26 & R19
  & R3 & R4 & HSV & H176 & HFL & HSRC & HTB & HWD & HSB & HQR & HTREE).
pose proof (proj1 HJ) as HAR. cbv beta in HAR.
assert (Hhi : ly_stk_hi lyc <= 2 ^ 47).
{ pose proof HJ as (_ & Hly & _).
  destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehi & _). lia. }
assert (SP : spZ regs = exv_s1 E).
{ unfold spZ. rewrite R2. unfold w64. apply unsigned_lit_small. clear - G1 G10 C1. lia. }
destruct HTREE as [Hv0 | HT]; [exfalso; exact (Hv Hv0)|].
destruct HT as (Hnd & Hhome & Hra & Hhull).
assert (HALL : (4096 <= e_v E /\ e_v E + 56 <= 2 ^ 47) /\
  (forall x, e_v E <= x < e_v E + 56 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416))).
{ destruct Hhome as [(b & m & Hin & H1 & H2) | [(cid & pos' & Hin & H1 & H2) | (H1 & H2)]].
  - pose proof HLED as (_ & _ & HBL & _). rewrite Forall_forall in HBL.
    destruct (HBL (b, m) Hin) as (Hm0 & Hblk & _ & _ & _). cbn [fst snd] in *.
    destruct (alx_blocks rsegs B ARx LAWS lyc Sc Hpc Wc memc mdc (b - cf_head) (m + cf_head) HAR Hblk)
      as (_ & H4096 & Hce & Happ & _).
    assert (Hrq : m + cf_head <= req_size (m + cf_head))
      by (unfold req_size; destruct (Z.eqb_spec (m + cf_head) 0); lia).
    split; [clear - H1 H2 H4096 Hce Hrq CH0 C1; lia|].
    intros x Hx.
    destruct (in_app_addr (b - cf_head) (req_size (m + cf_head)) x Happ ltac:(clear - Hx H1 H2 Hrq CH0; lia))
      as (Ha1 & Ha2).
    unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. clear - Ha1 Ha2. lia.
  - destruct (frames_bounds_x rsegs B ARx LAWS lyc Sc Hpc Wc memc mdc cid pos' HAR Hin) as (F1 & F2 & F3).
    pose proof (fs_frame_bytes_nonneg cid) as FB.
    split; [clear - H1 H2 F1 F2 FB C1; lia|].
    intros x Hx.
    destruct (in_app_addr (frame_addr lyc cid pos') (fs_frame_bytes cid) x F3 ltac:(clear - Hx H1 H2; lia))
      as (Ha1 & Ha2).
    unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. clear - Ha1 Ha2. lia.
  - rewrite SP in H1. split; [clear - H1 H2 G1 Hhi C1; lia|].
    intros x Hx. unfold SHADOW_OFF. clear - H1 Hx G1 C1. lia. }
split; [exact (proj1 (proj1 HALL))|]. split; [exact (proj2 (proj1 HALL))|].
split; [exact (proj2 HALL)|].
intros x Hx. destruct (HDJ x ltac:(left; clear - Hx; lia)) as (Hq & Hsp). split; [|exact Hq].
intros Hc. apply Hsp. clear - Hc G3. lia.
Qed.

(* ---- the bookkeeping of exv_dif at LK, one lemma per arm ---- *)
(* no node was being compared (vv = 0): in->differs is untouched *)
Lemma a1_bk0 : forall E (o : bool) (dlc : Z) acc,
  exv_dif E o 0 dlc acc -> (dlc = 0 \/ dlc = 1) ->
  forall nm u dl', (dl' = 0 \/ dl' = 1) ->
  (dl' = 1 <-> dlc = 1 \/ (0 <> 0 /\ ~ exv_same o (e_t E) (length acc) nm u)) ->
  exv_dif E o 0 dl' ((nm, u) :: acc).
Proof.
intros E o dlc acc Hdif Hdlc nm u dl' Hdl' Hiff.
assert (Heq : dl' = dlc).
{ destruct Hdl' as [Ha|Ha]; destruct Hdlc as [Hb|Hb]; subst; try reflexivity.
  - exact (proj2 Hiff (or_introl eq_refl)).
  - exfalso. destruct (proj1 Hiff eq_refl) as [Hc | (Hc & _)]; [discriminate | exact (Hc eq_refl)]. }
subst dl'.
destruct Hdif as [(_ & Hz & Hnz) | (_ & Hvv & _)]; [|exfalso; exact (Hvv eq_refl)].
left. split; [reflexivity|]. split; [exact Hz | exact Hnz].
Qed.

(* the node has no item i: in->differs := 1, and the prefix can no longer match *)
Lemma a1_bkL : forall E (o : bool) (vv dlc : Z) acc,
  PURE_PREF_LONG -> exv_dif E o vv dlc acc -> vv <> 0 -> (exv_count (e_t E) <= length acc)%nat ->
  forall nm u dl', (dl' = 0 \/ dl' = 1) ->
  (dl' = 1 <-> 1 = 1 \/ (0 <> 0 /\ ~ exv_same o (e_t E) (length acc) nm u)) ->
  exv_dif E o vv dl' ((nm, u) :: acc).
Proof.
intros E o vv dlc acc PL Hdif Hvv Hge nm u dl' Hdl' Hiff.
assert (Hdl1 : dl' = 1) by (apply Hiff; left; reflexivity).
destruct Hdif as [(H0 & _) | (Hve & _ & Htag & Hdc)]; [exfalso; exact (Hvv H0)|].
right. split; [exact Hve|]. split; [exact Hvv|]. split; [exact Htag|].
split; [intros _; right; exact (PL o (e_t E) acc nm u Hge) | intros _; exact Hdl1].
Qed.

(* the node has item i: the kid is compared, so the prefix grows by one item *)
Lemma a1_bkK : forall E (o : bool) (vv dlc kid : Z) acc,
  PURE_PREF_CONS -> exv_dif E o vv dlc acc -> vv <> 0 -> kid <> 0 ->
  (length acc < exv_count (e_t E))%nat ->
  forall nm u dl', (dl' = 0 \/ dl' = 1) ->
  (dl' = 1 <-> dlc = 1 \/ (kid <> 0 /\ ~ exv_same o (e_t E) (length acc) nm u)) ->
  exv_dif E o vv dl' ((nm, u) :: acc).
Proof.
intros E o vv dlc kid acc PC Hdif Hvv Hkid Hlt nm u dl' Hdl' Hiff.
destruct Hdif as [(H0 & _) | (Hve & _ & Htag & Hdc)]; [exfalso; exact (Hvv H0)|].
right. split; [exact Hve|]. split; [exact Hvv|]. split; [exact Htag|].
pose proof (PC o (e_t E) acc nm u Hlt Htag) as PCi.
split.
- intros H1. apply Hiff in H1. destruct H1 as [H1 | (_ & Hns)].
  + apply Hdc in H1. destruct H1 as [H1 | H1]; [left; exact H1|].
    right. intros Hp. apply H1. exact (proj1 (proj1 PCi Hp)).
  + right. intros Hp. apply Hns. exact (proj2 (proj1 PCi Hp)).
- intros H1. destruct Hdl' as [Hz | Ho]; [|exact Ho]. exfalso.
  assert (Hn1 : ~ (dlc = 1 \/ (kid <> 0 /\ ~ exv_same o (e_t E) (length acc) nm u))).
  { intros HR. pose proof (proj2 Hiff HR) as Hc. rewrite Hz in Hc. discriminate Hc. }
  assert (Hdlc0 : dlc <> 1) by (intros Hc; apply Hn1; left; exact Hc).
  assert (Hsame : ~ ~ exv_same o (e_t E) (length acc) nm u)
    by (intros Hns; apply Hn1; right; split; [exact Hkid | exact Hns]).
  assert (Hpref : ~ ~ exv_pref o acc (e_t E))
    by (intros Hnp; apply Hdlc0; apply Hdc; right; exact Hnp).
  destruct H1 as [Hdl1 | Hnp]; [apply Hdlc0; apply Hdc; left; exact Hdl1|].
  apply Hpref. intros Hp. apply Hsame. intros Hs. apply Hnp. apply PCi. split; [exact Hp | exact Hs].
Qed.

(* ---- arm A: vv = 0 (B 0x83a60-0x83a64, 0x83b14-0x83b18): no node, no write ---- *)
Lemma a1_run0 : forall (fx : YK11.FPState) E lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos
    (Q : world rsegs -> config -> Prop),
  EXV_PRE B ARx E -> EXB (fx := fx) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  exv_spill E Wc memc 152 0 ->
  (forall (regs' : bvmap 5 word) memc' mdc',
     ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E)
       (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] lyc Sc Hpc Wc memc' mdc' k ->
     exvl_P (e_mem E) memc' ->
     (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H Wc) memc' a = aview rsegs (w_H Wc) memc a) ->
     (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
     (forall r, In r A1_KEPT -> getr regs' r = getr regs r) ->
     getr regs' 20 = w64 0 -> getr regs' 24 = w64 1 ->
     SRr rsegs Wc (cfg_at (fx := fx) rsegs (exv_pc 0x5f0) regs' memc' mdc') Q) ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs (exv_pc 0x534) regs memc mdc) Q.
Proof.
intros fx E lyc Sc Hpc Wc regs memc mdc k pos Q HPRE HB S152 HK.
pose proof (eh_laws B ARx SK HYP) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (a1_geo E HPRE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof HB as HBc. unfold EXB in HBc. cbv zeta in HBc.
destruct HBc as (HJ0 & HWIN & HFR & HFZ & HHp & HAB & HRM & HLED & HCNT & R2 & R8 & R9 & R18 & R24 & R25 & R26 & R19
  & R3 & R4 & HSV & H176 & HFL & HSRC & HTB & HWD & HSB & HQR & HTREE).
rewrite a1_lk_eq in HK.
assert (HPM : exvl_P (e_mem E) memc) by exact (proj2 HRM).
pose proof (SRr_run_to_tok_AJx_inv (SK := SK) rsegs B prh_pst ARx LAWS B_prog_segs_low A1_TBL B_prog_tbl_ok B_prog_wx
  (exvl_P (e_mem E)) (exvl_PLAW (e_mem E))) as RUNTO.
assert (U9 : bv_unsigned (ew (Ereg regs (@nil word)) 9) = exv_s1 E).
{ rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), R9. unfold w64. apply unsigned_lit_small.
  clear - G1 G10 C1. lia. }
assert (HS : st_ok rsegs (Ereg regs (@nil word)) ss_a10
  (restrict (w_H Wc) (mkst regs (Z_to_bv 64 A1_PC) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_a10. apply (exw_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute; reflexivity.
  - unfold a1_rs0. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [clear - G1 C1; lia|]. split; [clear - G1 G10 C1; lia|].
    split; [intros o Ho; clear - Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs _ _ (exv_s1 E) 152 8 (SLit 0) 0); [reflexivity | cbn; lia | zside | exact S152].
  - unfold a1_rs0. cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - split; [exact I|]. split; [exact I | exact I]. }
assert (SHOK : sh_ok rsegs a1_Bx a1_SH0 (Ereg regs (@nil word)) (mrestrict (w_H Wc) memc))
  by (unfold a1_SH0, sh_ok; apply Forall_nil).
assert (AG : env_agree 32 (Ereg regs (@nil word)) (Ereg regs (@nil word))) by apply env_agree_refl.
unfold cfg_at. change (w64 (exv_pc 0x534)) with (Z_to_bv 64 A1_PC).
a1_runto RUNTO HS HJ0 SHOK HPM A1_LK.
{ intros a_ (r_ & Hin_ & Hr_); vm_compute in Hin_;
  repeat (destruct Hin_ as [<- | Hin_];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr_; exfalso; clear - Hr_; lia|]);
  destruct Hin_. }
a1_kept HFr (fun a : Z => False) ltac:(fun h => idtac).
prreg HS (20%bv : bv 5) R20. prreg HS (24%bv : bv 5) R24'.
pmkst HS.
apply HK.
- exact HJ0.
- exact HPM.
- intros a Ha. apply KEPT; [exact Ha | intros Hf; exact Hf].
- intros a Ha. exact (apresent_grows _ _ _ a HG Ha).
- intros r Hr. cbn [ms_regs restrict].
  exact (regs_kept_of_st_ok rsegs _ _ _ regs _ A1_KEPT HS AG ltac:(vm_compute; reflexivity) r Hr).
- cbn [ms_regs restrict]. rewrite R20. reflexivity.
- cbn [ms_regs restrict]. rewrite R24'. reflexivity.
Qed.

(* the spilled shadow address of a cursor cell, as the code builds it (B 0x83a34-0x83a54) *)
Lemma a1_denot_shq : forall (EV : env) n m c v sb, ew EV n = Z_to_bv 64 v -> ew EV m = Z_to_bv 64 sb ->
  0 <= v -> 0 <= c -> v + c < 2 ^ 63 -> 0 <= sb < 2 ^ 32 ->
  sv_denot EV (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff m 0)) = Z_to_bv 64 (sb + (v + c) / 8).
Proof.
intros EV n m c v sb Hn Hm Hv0 Hc Hv Hsb.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot EV (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff m 0)))).
f_equal.
change (U EV (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff m 0)) = sb + (v + c) / 8).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Hn, Hm.
rewrite !unsigned_lit_small by lia. rewrite Z.add_0_r.
change (Z.land (U EV (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos (v + c) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_lt_upper_bound (v + c) 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (zcanon_id (v + c)) by (unfold M64; lia). rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia).
rewrite (zcanon_id sb) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* ex_value's own stack window is present at every state of the journal *)
Lemma a1_pres : forall E lyc Sc Hpc Wc memc mdc k pos,
  ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E)
    (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] lyc Sc Hpc Wc memc mdc k ->
  forall a, exv_sp E - exv_STK E <= a < exv_sp E + e_d E -> apresent (w_H Wc) memc a.
Proof.
intros E lyc Sc Hpc Wc memc mdc k pos HJ a Ha.
destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _).
apply HP. clear - Ha. lia.
Qed.

(* ---- arm B: vv <> 0 and i >= count (B 0x83a60-0x83b10): no item i, in->differs := 1 ---- *)
Lemma a1_runL : forall (fx : YK11.FPState) E lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos
    (cnt iZ : Z) (Q : world rsegs -> config -> Prop),
  EXV_PRE B ARx E -> EXB (fx := fx) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  e_v E <> 0 -> e_v E mod 8 = 0 ->
  val_mem rsegs (mrestrict (w_H Wc) memc) (e_v E + 40) 8 cnt -> 0 <= cnt -> 0 <= iZ < 2 ^ 32 -> cnt <= iZ ->
  range_addressable (aview rsegs (w_H Wc) memc) SHADOW_OFF (e_v E) 56 ->
  exv_spill E Wc memc 152 (e_v E) -> exv_spill E Wc memc 88 (e_v E + 40) ->
  exv_spill E Wc memc 136 iZ -> exv_spill E Wc memc 72 (shadow_addr (e_q E + 32)) ->
  exv_spill E Wc memc 80 (e_q E + 32) ->
  (forall (regs' : bvmap 5 word) memc' mdc',
     ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E)
       (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] lyc Sc Hpc Wc memc' mdc' k ->
     exvl_P (e_mem E) memc' ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (e_q E + 32 <= a < e_q E + 36) ->
        aview rsegs (w_H Wc) memc' a = aview rsegs (w_H Wc) memc a) ->
     (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
     (forall r, In r A1_KEPT -> getr regs' r = getr regs r) ->
     getr regs' 20 = w64 0 -> getr regs' 24 = w64 1 ->
     val_mem rsegs (mrestrict (w_H Wc) memc') (e_q E + 32) 4 1 ->
     SRr rsegs Wc (cfg_at (fx := fx) rsegs (exv_pc 0x5f0) regs' memc' mdc') Q) ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs (exv_pc 0x534) regs memc mdc) Q.
Proof.
intros fx E lyc Sc Hpc Wc regs memc mdc k pos cnt iZ Q HPRE HB Hv Hv8 Vcnt Hcnt0 Hi Hci Hvra S152 S88 S136 S72 S80 HK.
pose proof (eh_laws B ARx SK HYP) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (a1_geo E HPRE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (a1_node fx E lyc Sc Hpc Wc regs memc mdc k pos HPRE HB Hv) as (N1 & N2 & N3 & N4).
pose proof HB as HBc. unfold EXB in HBc. cbv zeta in HBc.
destruct HBc as (HJ0 & HWIN & HFR & HFZ & HHp & HAB & HRM & HLED & HCNT & R2 & R8 & R9 & R18 & R24 & R25 & R26 & R19
  & R3 & R4 & HSV & H176 & HFL & HSRC & HTB & HWD & HSB & HQR & HTREE).
pose proof (a1_pres E lyc Sc Hpc Wc memc mdc k pos HJ0) as HPRES.
(* the node is apart from ex_value's frame and from the cursor, as intervals *)
assert (ND1 : e_v E + 56 <= exv_s1 E \/ exv_sp E <= e_v E).
{ destruct (Z_le_gt_dec (e_v E + 56) (exv_s1 E)) as [H|H]; [left; exact H|].
  destruct (Z_le_gt_dec (exv_sp E) (e_v E)) as [H2|H2]; [right; exact H2|].
  exfalso. destruct (Z_le_gt_dec (e_v E) (exv_s1 E)) as [H3|H3].
  - destruct (N4 (exv_s1 E) ltac:(clear - H H3; lia)) as (Hs & _). apply Hs. clear - G2. lia.
  - destruct (N4 (e_v E) ltac:(clear; lia)) as (Hs & _). apply Hs. clear - H2 H3. lia. }
assert (ND2 : e_v E + 56 <= e_q E \/ e_q E + 40 <= e_v E).
{ destruct (Z_le_gt_dec (e_v E + 56) (e_q E)) as [H|H]; [left; exact H|].
  destruct (Z_le_gt_dec (e_q E + 40) (e_v E)) as [H2|H2]; [right; exact H2|].
  exfalso. destruct (Z_le_gt_dec (e_v E) (e_q E)) as [H3|H3].
  - destruct (N4 (e_q E) ltac:(clear - H H3; lia)) as (_ & Hq). apply Hq. clear; lia.
  - destruct (N4 (e_v E) ltac:(clear; lia)) as (_ & Hq). apply Hq. clear - H2 H3. lia. }
rewrite a1_lk_eq in HK.
assert (HPM : exvl_P (e_mem E) memc) by exact (proj2 HRM).
pose proof (SRr_run_to_tok_AJx_inv (SK := SK) rsegs B prh_pst ARx LAWS B_prog_segs_low A1_TBL B_prog_tbl_ok B_prog_wx
  (exvl_P (e_mem E)) (exvl_PLAW (e_mem E))) as RUNTO.
set (EX := Ereg regs [w64 (e_v E); w64 iZ; w64 cnt]).
assert (E9 : ew EX 9 = w64 (exv_s1 E)) by (unfold EX; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E19 : ew EX 19 = w64 (e_q E)) by (unfold EX; rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
assert (E25 : ew EX 25 = w64 SHADOW_OFF) by (unfold EX; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
assert (E32 : ew EX 32 = w64 (e_v E)) by (unfold EX; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew EX 33 = w64 iZ) by (unfold EX; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew EX 34 = w64 cnt) by (unfold EX; exact (ew_Ereg_extra regs _ 2)).
assert (U9 : bv_unsigned (ew EX 9) = exv_s1 E)
  by (rewrite E9; unfold w64; apply unsigned_lit_small; clear - G1 G10 C1; lia).
assert (U19 : bv_unsigned (ew EX 19) = e_q E)
  by (rewrite E19; unfold w64; apply unsigned_lit_small; clear - G5 G6 C1; lia).
assert (U25 : bv_unsigned (ew EX 25) = SHADOW_OFF)
  by (rewrite E25; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew EX 32) = e_v E)
  by (rewrite E32; unfold w64; apply unsigned_lit_small; clear - N1 N2; lia).
assert (U33 : bv_unsigned (ew EX 33) = iZ)
  by (rewrite E33; unfold w64; apply unsigned_lit_small; clear - Hi; lia).
assert (U34 : bv_unsigned (ew EX 34) = cnt)
  by (rewrite E34; unfold w64; apply unsigned_lit_small; clear - Hcnt0 Hci Hi; lia).
assert (HS : st_ok rsegs EX ss_a1L (restrict (w_H Wc) (mkst regs (Z_to_bv 64 A1_PC) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_a1L. apply (exw_st_ok_full rsegs).
  - unfold EX. apply regs_ok_Ereg.
  - vm_compute; reflexivity.
  - unfold a1_rsL. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [clear - G1 C1; lia|]. split; [clear - G1 G10 C1; lia|].
      split; [intros o Ho; clear - Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val rsegs EX _ (exv_s1 E) 152 8 (SOff 32 0) (e_v E));
          [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | clear - N1 N2; cbn; lia | zside | exact S152].
      * apply (chunk_ok_val rsegs EX _ (exv_s1 E) 88 8 (SOff 32 40) (e_v E + 40));
          [cbn [sv_denot]; rewrite U32; reflexivity | clear - N1 N2; cbn; lia | zside | exact S88].
      * apply (chunk_ok_val rsegs EX _ (exv_s1 E) 136 8 (SOff 33 0) iZ);
          [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | clear - Hi; cbn; lia | zside | exact S136].
      * apply (chunk_ok_val rsegs EX _ (exv_s1 E) 72 8 a1_shq (shadow_addr (e_q E + 32)));
          [unfold a1_shq, shadow_addr; apply (a1_denot_shq EX 19 25 32 (e_q E) SHADOW_OFF E19 E25);
             [clear - G5 C1; lia | lia | clear - G5 G6 C1; lia | unfold SHADOW_OFF; lia]
          | unfold shadow_addr, SHADOW_OFF; clear - G5 G6 C1;
            pose proof (Z.div_pos (e_q E + 32) 8 ltac:(lia) ltac:(lia));
            pose proof (Z.div_lt_upper_bound (e_q E + 32) 8 (2 ^ 45) ltac:(lia) ltac:(lia)); cbn; lia
          | zside | exact S72].
      * apply (chunk_ok_val rsegs EX _ (exv_s1 E) 80 8 (SOff 19 32) (e_q E + 32));
          [cbn [sv_denot]; rewrite U19; reflexivity | clear - G5 G6 C1; cbn; lia | zside | exact S80].
    + rewrite U32. split; [clear - N1; lia|]. split; [clear - N1 N2; lia|].
      split; [intros o Ho; clear - Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val rsegs EX _ (e_v E) 40 8 (SOff 34 0) cnt);
        [cbn [sv_denot]; rewrite U34, Z.add_0_r; reflexivity | clear - Hcnt0 Hci Hi; cbn; lia | zside | exact Vcnt].
    + rewrite U19. split; [clear - G5 C1; lia|]. split; [clear - G6; lia|].
      split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable rsegs). apply HPRES. clear - Ho G3 G4 G12. lia.
  - apply pairwise_disjoint_of_extents. unfold a1_rsL. cbn [map]. unfold extent_of_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32, U19.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; clear - ND1 ND2 G2 G4 N1 N2; lia.
  - split.
    + cbn [f_atoms atoms_ok a1_GL]. unfold afact_ok, a1_fq, a1_fsb, a1_fv. cbn [af_lo af_hi af_al2].
      rewrite U19, U25, U32. try change (2 ^ 3) with 8. try change (2 ^ 0) with 1.
      repeat split;
        try (clear - G5 G6 C1 N1 N2 G7 Hv8;
             first [exact G7 | exact Hv8 | apply Z.mod_1_r | exact I | lia]).
    + split; [|exact I]. cbn [f_conds conds_ok a1_GL]. split; [|exact I].
      unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U, !U_SOff, U33, U34, !Z.add_0_r.
      rewrite !zcanon_id by (unfold M64; clear - Hi Hcnt0 Hci; lia).
      apply negb_true_iff, Z.ltb_ge. clear - Hci. lia. }
assert (HBx : U EX a1_Bx = SHADOW_OFF)
  by (unfold a1_Bx; rewrite U_SOff, U25, Z.add_0_r; apply zcanon_id; unfold M64, SHADOW_OFF; lia).
assert (SHOK : sh_ok rsegs a1_Bx a1_SHL EX (mrestrict (w_H Wc) memc)).
{ unfold a1_SHL, sh_ok. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (shent_ok_of_range rsegs (w_H Wc) memc EX a1_Bx 32 (e_v E) 56 (e_v E) 0 56 Hvra HBx);
      [rewrite U_SOff, U32, Z.add_0_r; apply zcanon_id; unfold M64; clear - N1 N2; lia
      | clear; lia | clear; lia |].
    intros x Hx. apply N3. clear - Hx. lia.
  - apply (shent_ok_of_range rsegs (w_H Wc) memc EX a1_Bx 19 (e_q E) 40 (e_q E) 0 40 HQR HBx);
      [rewrite U_SOff, U19, Z.add_0_r; apply zcanon_id; unfold M64; clear - G5 G6 C1; lia
      | clear; lia | clear; lia |].
    intros x Hx. unfold SHADOW_OFF. clear - Hx G5 C1. lia. }
assert (AG : env_agree 32 EX EX) by apply env_agree_refl.
unfold cfg_at. change (w64 (exv_pc 0x534)) with (Z_to_bv 64 A1_PC).
a1_runto RUNTO HS HJ0 SHOK HPM A1_LK.
{ intros a_ (r_ & Hin_ & Hr_); vm_compute in Hin_;
  repeat (destruct Hin_ as [<- | Hin_];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr_;
     first [ exfalso; clear - Hr_; lia
           | rewrite U19 in Hr_; left; clear - Hr_ G3 G4 G12; lia ]|]);
  destruct Hin_. }
a1_kept HFr (fun a : Z => e_q E + 32 <= a < e_q E + 36)
  ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U19 in h).
prreg HS (20%bv : bv 5) R20'. prreg HS (24%bv : bv 5) R24''.
pose proof (exw_region_nth rsegs _ _ _ 2 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
pose proof (exw_field rsegs _ _ 19%nat (e_q E) _ _ _ _ _ 32 4 (SLit 1) 1 RQ
  ltac:(exact U19) ltac:(left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(zside)) as VQ.
pmkst HS.
apply HK.
- exact HJ0.
- exact HPM.
- intros a Ha Hn. apply KEPT; [exact Ha | exact Hn].
- intros a Ha. exact (apresent_grows _ _ _ a HG Ha).
- intros r Hr. cbn [ms_regs restrict].
  exact (regs_kept_of_st_ok rsegs _ _ _ regs _ A1_KEPT HS AG ltac:(vm_compute; reflexivity) r Hr).
- cbn [ms_regs restrict]. rewrite R20'. reflexivity.
- cbn [ms_regs restrict]. rewrite R24''. reflexivity.
- cbn [ms_mem restrict]. exact VQ.
Qed.

(* ---- the kid address and the two UBSan guards of the fetch (B 0x83ac0 pointer wrap, 0x83adc mulh overflow) ---- *)
Lemma a1_U_mul : forall (EV : env) n x, ew EV n = Z_to_bv 64 x -> 0 <= x -> 56 * x < 2 ^ 63 ->
  U EV (SMd M_MUL (SOff n 0) (SLit 56)) = x * 56.
Proof.
intros EV n x Hn H0 H1. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom EV n x Hn ltac:(lia)), (U_lit EV 56 ltac:(lia)).
apply zcanon_id. unfold M64. lia.
Qed.

Lemma a1_U_kid : forall (EV : env) n m x y, ew EV n = Z_to_bv 64 x -> ew EV m = Z_to_bv 64 y ->
  0 <= x -> 0 <= y -> 56 * x + y < 2 ^ 63 ->
  U EV (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit 56)) (SOff m 0)) = x * 56 + y.
Proof.
intros EV n m x y Hn Hm H0 H0' H1. rewrite U_SAlu. cbn [zalu_raw].
rewrite (a1_U_mul EV n x Hn H0 ltac:(lia)), (U_atom EV m y Hm ltac:(lia)).
apply zcanon_id. unfold M64. lia.
Qed.

Lemma a1_U_mulh : forall (EV : env) n x, ew EV n = Z_to_bv 64 x -> 0 <= x -> 56 * x < 2 ^ 63 ->
  U EV (SMd M_MULH (SOff n 0) (SLit 56)) = 0.
Proof.
intros EV n x Hn H0 H1. rewrite U_SMd. cbn [zmd_raw Z.of_N].
rewrite (U_atom EV n x Hn ltac:(lia)), (U_lit EV 56 ltac:(lia)).
rewrite !swrap64_id by (unfold half64; lia).
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma a1_U_sra : forall (EV : env) n x, ew EV n = Z_to_bv 64 x -> 0 <= x -> 56 * x < 2 ^ 63 ->
  U EV (SAlu ALU_SRA (SMd M_MUL (SOff n 0) (SLit 56)) (SLit 63)) = 0.
Proof.
intros EV n x Hn H0 H1. rewrite U_SAlu. cbn [zalu_raw].
rewrite (a1_U_mul EV n x Hn H0 H1), (U_lit EV 63 ltac:(lia)).
change (Z.land 63 63) with 63. rewrite swrap64_id by (unfold half64; lia).
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma a1_denot_add : forall (EV : env) n m x y, ew EV n = Z_to_bv 64 x -> ew EV m = Z_to_bv 64 y ->
  0 <= x -> 0 <= y -> x + y < 2 ^ 64 ->
  sv_denot EV (SAlu ALU_ADD (SOff n 0) (SOff m 0)) = Z_to_bv 64 (x + y).
Proof.
intros EV n m x y Hn Hm H0 H0' H1.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot EV (SAlu ALU_ADD (SOff n 0) (SOff m 0)))). f_equal.
change (U EV (SAlu ALU_ADD (SOff n 0) (SOff m 0)) = x + y).
rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom EV n x Hn ltac:(lia)), (U_atom EV m y Hm ltac:(lia)).
apply zcanon_id. unfold M64. lia.
Qed.

(* ---- arm C: vv <> 0 and i < count (B 0x83a60-0x83af0): s4 = kids + 56 i, s8 = 0, no write ---- *)
Lemma a1_runK : forall (fx : YK11.FPState) E lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos
    (cnt iZ kids : Z) (Q : world rsegs -> config -> Prop),
  EXV_PRE B ARx E -> EXB (fx := fx) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  e_v E <> 0 -> e_v E mod 8 = 0 ->
  val_mem rsegs (mrestrict (w_H Wc) memc) (e_v E + 40) 8 cnt ->
  val_mem rsegs (mrestrict (w_H Wc) memc) (e_v E + 24) 8 kids ->
  range_addressable (aview rsegs (w_H Wc) memc) SHADOW_OFF (e_v E) 56 ->
  0 <= iZ -> iZ <= 3145728 -> iZ < cnt -> 4096 <= kids -> kids + 56 * cnt <= alloc_ceiling ->
  exv_spill E Wc memc 152 (e_v E) -> exv_spill E Wc memc 88 (e_v E + 40) ->
  exv_spill E Wc memc 136 iZ -> exv_spill E Wc memc 56 (e_v E + 24) ->
  exv_spill E Wc memc 112 (56 * iZ) ->
  (forall (regs' : bvmap 5 word) memc' mdc',
     ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E)
       (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] lyc Sc Hpc Wc memc' mdc' k ->
     exvl_P (e_mem E) memc' ->
     (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H Wc) memc' a = aview rsegs (w_H Wc) memc a) ->
     (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
     (forall r, In r A1_KEPT -> getr regs' r = getr regs r) ->
     getr regs' 20 = w64 (kids + 56 * iZ) -> getr regs' 24 = w64 0 ->
     SRr rsegs Wc (cfg_at (fx := fx) rsegs (exv_pc 0x5f0) regs' memc' mdc') Q) ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs (exv_pc 0x534) regs memc mdc) Q.
Proof.
intros fx E lyc Sc Hpc Wc regs memc mdc k pos cnt iZ kids Q HPRE HB Hv Hv8 Vcnt Vkids Hvra
  Hi0 Hi3 Hic Hk0 Hkc S152 S88 S136 S56 S112 HK.
pose proof (eh_laws B ARx SK HYP) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (a1_geo E HPRE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (a1_node fx E lyc Sc Hpc Wc regs memc mdc k pos HPRE HB Hv) as (N1 & N2 & N3 & N4).
pose proof HB as HBc. unfold EXB in HBc. cbv zeta in HBc.
destruct HBc as (HJ0 & HWIN & HFR & HFZ & HHp & HAB & HRM & HLED & HCNT & R2 & R8 & R9 & R18 & R24 & R25 & R26 & R19
  & R3 & R4 & HSV & H176 & HFL & HSRC & HTB & HWD & HSB & HQR & HTREE).
assert (ND1 : e_v E + 56 <= exv_s1 E \/ exv_sp E <= e_v E).
{ destruct (Z_le_gt_dec (e_v E + 56) (exv_s1 E)) as [H|H]; [left; exact H|].
  destruct (Z_le_gt_dec (exv_sp E) (e_v E)) as [H2|H2]; [right; exact H2|].
  exfalso. destruct (Z_le_gt_dec (e_v E) (exv_s1 E)) as [H3|H3].
  - destruct (N4 (exv_s1 E) ltac:(clear - H H3; lia)) as (Hs & _). apply Hs. clear - G2. lia.
  - destruct (N4 (e_v E) ltac:(clear; lia)) as (Hs & _). apply Hs. clear - H2 H3. lia. }
rewrite a1_lk_eq in HK.
assert (HPM : exvl_P (e_mem E) memc) by exact (proj2 HRM).
pose proof (SRr_run_to_tok_AJx_inv (SK := SK) rsegs B prh_pst ARx LAWS B_prog_segs_low A1_TBL B_prog_tbl_ok B_prog_wx
  (exvl_P (e_mem E)) (exvl_PLAW (e_mem E))) as RUNTO.
set (EX := Ereg regs [w64 (e_v E); w64 iZ; w64 cnt; w64 kids; w64 (56 * iZ)]).
assert (E9 : ew EX 9 = w64 (exv_s1 E)) by (unfold EX; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E25 : ew EX 25 = w64 SHADOW_OFF) by (unfold EX; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
assert (E32 : ew EX 32 = w64 (e_v E)) by (unfold EX; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew EX 33 = w64 iZ) by (unfold EX; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew EX 34 = w64 cnt) by (unfold EX; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew EX 35 = w64 kids) by (unfold EX; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew EX 36 = w64 (56 * iZ)) by (unfold EX; exact (ew_Ereg_extra regs _ 4)).
assert (U9 : bv_unsigned (ew EX 9) = exv_s1 E)
  by (rewrite E9; unfold w64; apply unsigned_lit_small; clear - G1 G10 C1; lia).
assert (U25 : bv_unsigned (ew EX 25) = SHADOW_OFF)
  by (rewrite E25; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew EX 32) = e_v E)
  by (rewrite E32; unfold w64; apply unsigned_lit_small; clear - N1 N2; lia).
assert (U33 : bv_unsigned (ew EX 33) = iZ)
  by (rewrite E33; unfold w64; apply unsigned_lit_small; clear - Hi0 Hi3; lia).
assert (U34 : bv_unsigned (ew EX 34) = cnt)
  by (rewrite E34; unfold w64; apply unsigned_lit_small; clear - Hi0 Hic Hk0 Hkc C1; lia).
assert (U35 : bv_unsigned (ew EX 35) = kids)
  by (rewrite E35; unfold w64; apply unsigned_lit_small; clear - Hi0 Hic Hk0 Hkc C1; lia).
assert (U36 : bv_unsigned (ew EX 36) = 56 * iZ)
  by (rewrite E36; unfold w64; apply unsigned_lit_small; clear - Hi0 Hi3; lia).
assert (HS : st_ok rsegs EX ss_a1K (restrict (w_H Wc) (mkst regs (Z_to_bv 64 A1_PC) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_a1K. apply (exw_st_ok_full rsegs).
  - unfold EX. apply regs_ok_Ereg.
  - vm_compute; reflexivity.
  - unfold a1_rsK. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [clear - G1 C1; lia|]. split; [clear - G1 G10 C1; lia|].
      split; [intros o Ho; clear - Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val rsegs EX _ (exv_s1 E) 152 8 (SOff 32 0) (e_v E));
          [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | clear - N1 N2; cbn; lia | zside | exact S152].
      * apply (chunk_ok_val rsegs EX _ (exv_s1 E) 88 8 (SOff 32 40) (e_v E + 40));
          [cbn [sv_denot]; rewrite U32; reflexivity | clear - N1 N2; cbn; lia | zside | exact S88].
      * apply (chunk_ok_val rsegs EX _ (exv_s1 E) 136 8 (SOff 33 0) iZ);
          [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | clear - Hi0 Hi3; cbn; lia | zside | exact S136].
      * apply (chunk_ok_val rsegs EX _ (exv_s1 E) 56 8 (SOff 32 24) (e_v E + 24));
          [cbn [sv_denot]; rewrite U32; reflexivity | clear - N1 N2; cbn; lia | zside | exact S56].
      * apply (chunk_ok_val rsegs EX _ (exv_s1 E) 112 8 (SOff 36 0) (56 * iZ));
          [cbn [sv_denot]; rewrite U36, Z.add_0_r; reflexivity | clear - Hi0 Hi3; cbn; lia | zside | exact S112].
    + rewrite U32. split; [clear - N1; lia|]. split; [clear - N1 N2; lia|].
      split; [intros o Ho; clear - Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val rsegs EX _ (e_v E) 24 8 (SOff 35 0) kids);
          [cbn [sv_denot]; rewrite U35, Z.add_0_r; reflexivity
          | clear - Hi0 Hic Hk0 Hkc C1; cbn; lia | zside | exact Vkids].
      * apply (chunk_ok_val rsegs EX _ (e_v E) 40 8 (SOff 34 0) cnt);
          [cbn [sv_denot]; rewrite U34, Z.add_0_r; reflexivity
          | clear - Hi0 Hic Hk0 Hkc C1; cbn; lia | zside | exact Vcnt].
  - apply pairwise_disjoint_of_extents. unfold a1_rsK. cbn [map]. unfold extent_of_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; clear - ND1 G2 N1 N2; lia.
  - split.
    + cbn [f_atoms atoms_ok a1_GK]. unfold afact_ok, a1_fsb, a1_fv, a1_fi, a1_fk. cbn [af_lo af_hi af_al2].
      rewrite U25, U32, U33, U35. try change (2 ^ 3) with 8. try change (2 ^ 0) with 1.
      repeat split;
        try (clear - N1 N2 Hv8 Hi0 Hi3 Hk0 Hkc Hic C1;
             first [exact Hv8 | apply Z.mod_1_r | exact I | lia]).
    + split; [|exact I]. cbn [f_conds conds_ok a1_GK]. split; [|exact I].
      unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_ltu_U, !U_SOff, U33, U34, !Z.add_0_r.
      rewrite !zcanon_id by (unfold M64; clear - Hi0 Hi3 Hic Hk0 Hkc C1; lia).
      apply Z.ltb_lt. clear - Hic. lia. }
assert (HBx : U EX a1_Bx = SHADOW_OFF)
  by (unfold a1_Bx; rewrite U_SOff, U25, Z.add_0_r; apply zcanon_id; unfold M64, SHADOW_OFF; lia).
assert (SHOK : sh_ok rsegs a1_Bx a1_SHK EX (mrestrict (w_H Wc) memc)).
{ unfold a1_SHK, sh_ok. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range rsegs (w_H Wc) memc EX a1_Bx 32 (e_v E) 56 (e_v E) 0 56 Hvra HBx);
    [rewrite U_SOff, U32, Z.add_0_r; apply zcanon_id; unfold M64; clear - N1 N2; lia
    | clear; lia | clear; lia |].
  intros x Hx. apply N3. clear - Hx. lia. }
assert (AG : env_agree 32 EX EX) by apply env_agree_refl.
unfold cfg_at. change (w64 (exv_pc 0x534)) with (Z_to_bv 64 A1_PC).
a1_runto RUNTO HS HJ0 SHOK HPM A1_LK.
{ intros a_ (r_ & Hin_ & Hr_); vm_compute in Hin_;
  repeat (destruct Hin_ as [<- | Hin_];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr_; exfalso; clear - Hr_; lia|]);
  destruct Hin_. }
a1_kept HFr (fun a : Z => False) ltac:(fun h => idtac).
rename KEPT into K1. rename HG into HG1. clear HF HFr.
a1_branch HS SHOK.
- exfalso. rewrite branch_ltu_U in Hc.
  rewrite (a1_U_kid EX 33 35 iZ kids E33 E35 ltac:(lia) ltac:(clear - Hk0; lia)
    ltac:(clear - Hi0 Hi3 Hk0 Hkc Hic C1; lia)) in Hc.
  rewrite (U_atom EX 35 kids E35 ltac:(clear - Hi0 Hic Hk0 Hkc C1; lia)) in Hc.
  apply Z.ltb_lt in Hc. clear - Hc Hi0 Hk0. lia.
- clear Hc. a1_runto RUNTO HS HJ0 SHOK HPM A1_LK.
  { intros a_ (r_ & Hin_ & Hr_); vm_compute in Hin_;
    repeat (destruct Hin_ as [<- | Hin_];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr_; exfalso; clear - Hr_; lia|]);
    destruct Hin_. }
  a1_kept HFr (fun a : Z => False) ltac:(fun h => idtac).
  rename KEPT into K2. rename HG into HG2. clear HF HFr.
  a1_branch HS SHOK.
  + exfalso. rewrite branch_ne_U in Hc.
    rewrite U_SAlu in Hc. cbn [zalu_raw] in Hc. rewrite (U_lit EX 0 ltac:(lia)) in Hc.
    rewrite U_SAlu in Hc. cbn [zalu_raw] in Hc.
    rewrite (a1_U_mulh EX 33 iZ E33 ltac:(lia) ltac:(clear - Hi0 Hi3; lia)) in Hc.
    rewrite (a1_U_sra EX 33 iZ E33 ltac:(lia) ltac:(clear - Hi0 Hi3; lia)) in Hc.
    vm_compute in Hc. discriminate Hc.
  + clear Hc. a1_runto RUNTO HS HJ0 SHOK HPM A1_LK.
    { intros a_ (r_ & Hin_ & Hr_); vm_compute in Hin_;
      repeat (destruct Hin_ as [<- | Hin_];
        [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr_; exfalso; clear - Hr_; lia|]);
      destruct Hin_. }
    a1_kept HFr (fun a : Z => False) ltac:(fun h => idtac).
    rename KEPT into K3. rename HG into HG3. clear HF HFr.
    pose proof (st_ok_restrict_reg rsegs (w_H Wc) _ _ _ 20%bv HS) as R20'.
    lazymatch type of R20' with _ = sv_denot ?Ex (sr_get ?l _) =>
      let e := eval vm_compute in (sr_get l 20%bv) in change (sr_get l 20%bv) with e in R20' end.
    rewrite (a1_denot_add EX 35 36 kids (56 * iZ) E35 E36 ltac:(clear - Hk0; lia)
      ltac:(clear - Hi0; lia) ltac:(clear - Hi0 Hi3 Hk0 Hkc Hic C1; lia)) in R20'.
    prreg HS (24%bv : bv 5) R24''.
    pmkst HS.
    apply HK.
    * exact HJ0.
    * exact HPM.
    * intros a Ha. exact (eq_trans (K3 a Ha (fun h : False => h))
        (eq_trans (K2 a Ha (fun h : False => h)) (K1 a Ha (fun h : False => h)))).
    * intros a Ha. exact (apresent_grows _ _ _ a HG3 (apresent_grows _ _ _ a HG2
        (apresent_grows _ _ _ a HG1 Ha))).
    * intros r Hr. cbn [ms_regs restrict].
      exact (regs_kept_of_st_ok rsegs _ _ _ regs _ A1_KEPT HS AG ltac:(vm_compute; reflexivity) r Hr).
    * cbn [ms_regs restrict]. cbn [ms_regs restrict] in R20'. rewrite R20'. reflexivity.
    * cbn [ms_regs restrict]. rewrite R24''. reflexivity.
Qed.

(* ---- the facts at LK: the text length, the cursor and the spills across the fetch ---- *)
Lemma a1_len : forall E, EXV_PRE B ARx E -> exv_len E <= 3 * 2 ^ 20.
Proof.
intros E HP. unfold EXV_PRE in HP. cbv zeta in HP.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlen & _). exact Hlen.
Qed.

(* the cursor's first four words kept, in->differs read anew *)
Lemma a1_cur_keep : forall (Wc : world rsegs) memc memc' q p e dep scr dl dl',
  (forall a, q <= a < q + 32 -> aview rsegs (w_H Wc) memc' a = aview rsegs (w_H Wc) memc a) ->
  prhex_cur Wc memc q p e dep scr dl -> val_mem rsegs (mrestrict (w_H Wc) memc') (q + 32) 4 dl' ->
  prhex_cur Wc memc' q p e dep scr dl'.
Proof.
intros Wc memc memc' q p e dep scr dl dl' HK (V0 & V8 & V16 & V24 & _) V32.
assert (KV : forall a n v, q <= a -> a + Z.of_nat n <= q + 32 ->
  val_mem rsegs (mrestrict (w_H Wc) memc) a n v -> val_mem rsegs (mrestrict (w_H Wc) memc') a n v).
{ intros a n v H1 H2 Hv. apply (exw_val_kept rsegs (w_H Wc) memc memc' a n v); [|exact Hv].
  intros x Hx. apply HK. clear - H1 H2 Hx. lia. }
unfold prhex_cur.
split; [apply KV; [lia | cbn; lia | exact V0]|].
split; [apply KV; [lia | cbn; lia | exact V8]|].
split; [apply KV; [lia | cbn; lia | exact V16]|].
split; [apply KV; [lia | cbn; lia | exact V24] | exact V32].
Qed.

(* the whole cursor kept *)
Lemma a1_cur_all : forall (Wc : world rsegs) memc memc' q p e dep scr dl,
  0 <= q -> q + 40 <= 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H Wc) memc' a = aview rsegs (w_H Wc) memc a) ->
  prhex_cur Wc memc q p e dep scr dl -> prhex_cur Wc memc' q p e dep scr dl.
Proof.
intros Wc memc memc' q p e dep scr dl Hq0 Hq1 HK Hc.
apply (a1_cur_keep Wc memc memc' q p e dep scr dl dl); [intros a Ha; apply HK; clear - Ha Hq0 Hq1; lia | exact Hc |].
destruct Hc as (_ & _ & _ & _ & V32).
apply (exw_val_kept rsegs (w_H Wc) memc memc' (q + 32) 4 dl); [|exact V32].
intros x Hx. apply HK. cbn in Hx. clear - Hx Hq0 Hq1. lia.
Qed.

(* the spills [s1 + 8, s1 + 160) lie below the cursor, so a write to in->differs keeps them *)
Lemma a1_spills_kept : forall E (Wc : world rsegs) memc memc' lyc pos c vv (i : nat),
  EXV_PRE B ARx E ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (e_q E + 32 <= a < e_q E + 36) ->
     aview rsegs (w_H Wc) memc' a = aview rsegs (w_H Wc) memc a) ->
  exv_spills E Wc memc lyc pos c vv i -> exv_spills E Wc memc' lyc pos c vv i.
Proof.
intros E Wc memc memc' lyc pos c vv i HPRE HK HSP.
pose proof (a1_geo E HPRE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & _).
assert (KS : forall o v, 8 <= o <= 152 -> exv_spill E Wc memc o v -> exv_spill E Wc memc' o v).
{ intros o v Ho Hs. unfold exv_spill in *.
  apply (exw_val_kept rsegs (w_H Wc) memc memc' (exv_s1 E + o) 8 v); [|exact Hs].
  intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply HK; clear - Hx Ho G1 G4 G10 C1; lia. }
unfold exv_spills in *. cbv zeta in *.
destruct HSP as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18
  & S19).
repeat split; apply KS; first [clear; lia | assumption].
Qed.

(* ---- LK: EXBs at the fetch's end (KIT_RUNs), the spills kept, the downstream cut ---- *)
Lemma a1_fin : forall (fx : YK11.FPState) n m E lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos
    (c : Z) (i cap : nat) (acc : list (list Z * PjTree.jv)) (ip vv : Z)
    (regs' : bvmap 5 word) memc' mdc' (dlc' kid fl : Z) (tk : PjTree.jv),
  CUT_LK (fx := fx) B ARx SK n m ->
  e_n E = n -> EXV_PRE B ARx E -> EXB (fx := fx) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  exv_i1 E < exv_len E -> nth (Z.to_nat (exv_i1 E)) (e_x E) 0 = c -> (c = 91 \/ c = 123) ->
  e_dep E + 1 <= 32 -> length acc = i ->
  0 <= ip <= exv_len E -> Z.of_nat i <= ip -> exv_len E - ip <= m ->
  exv_V E = exv_L (S (Z.to_nat (e_dep E))) (c =? 123) i cap acc (skipn (Z.to_nat ip) (e_x E)) ->
  getr regs 27 = w64 c -> getr regs 22 = w64 (shadow_addr (e_q E + 8)) -> getr regs 23 = w64 (e_q E + 8) ->
  exv_spills E Wc memc lyc pos c vv i ->
  ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E)
    (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] lyc Sc Hpc Wc memc' mdc' k ->
  exvl_P (e_mem E) memc' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (e_q E + 32 <= a < e_q E + 36) ->
     aview rsegs (w_H Wc) memc' a = aview rsegs (w_H Wc) memc a) ->
  (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
  (forall r, In r A1_KEPT -> getr regs' r = getr regs r) ->
  getr regs' 20 = w64 kid -> getr regs' 24 = w64 fl ->
  prhex_cur Wc memc' (e_q E) (e_x0 E + ip) (e_x0 E + exv_len E) (e_dep E + 1) (e_scr E) dlc' ->
  (dlc' = 0 \/ dlc' = 1) ->
  ((kid = 0 /\ fl = 1) \/
   (fl = 0 /\ vv = e_v E /\ PjTree.tag (e_t E) = (if (c =? 123) then 6 else 5) /\
    exv_child E Wc memc' i kid tk)) ->
  (forall nm u dl', (dl' = 0 \/ dl' = 1) ->
     (dl' = 1 <-> dlc' = 1 \/ (kid <> 0 /\ ~ exv_same (c =? 123) (e_t E) i nm u)) ->
     exv_dif E (c =? 123) vv dl' ((nm, u) :: acc)) ->
  SRr rsegs Wc (cfg_at (fx := fx) rsegs (exv_pc 0x5f0) regs' memc' mdc') (EXV_POST B ARx SK E).
Proof.
intros fx n m E lyc Sc Hpc Wc regs memc mdc k pos c i cap acc ip vv regs' memc' mdc' dlc' kid fl tk
  HLK Hn HPRE HB Hi1 Hc Hc2 Hdep Hacc Hip Hii Hm HV H27 H22 H23 HSP HJ' HPM' HK' HG' HR' R20 R24 Hcur Hdl HKID HBK.
assert (HBs : EXBs (fx := fx) B ARx SK E lyc Sc Hpc Wc regs' memc' mdc' k pos).
{ apply (KRUN fx E lyc Sc Hpc Wc regs memc mdc k pos regs' memc' mdc' HPRE).
  - exists regs. split; [exact HB | intros r _; reflexivity].
  - exact HJ'.
  - intros a Ha _ _ Hn32. exact (HK' a Ha Hn32).
  - exact HG'.
  - exact HPM'.
  - intros r Hr Hr24. apply HR'. unfold exv_bregs in Hr. unfold A1_KEPT.
    repeat (destruct Hr as [<- | Hr];
      [first [exfalso; apply Hr24; reflexivity | repeat (first [left; reflexivity | right])] |]).
    destruct Hr. }
apply (HLK E lyc Sc Hpc Wc regs' memc' mdc' k pos c i cap acc ip vv dlc' kid fl tk Hn HPRE HBs Hi1 Hc Hc2 Hdep Hacc
  Hcur Hip Hdl Hii Hm HV HKID HBK R20 R24).
- rewrite (HR' 27%bv ltac:(unfold A1_KEPT; repeat (first [left; reflexivity | right]))). exact H27.
- rewrite (HR' 22%bv ltac:(unfold A1_KEPT; repeat (first [left; reflexivity | right]))). exact H22.
- rewrite (HR' 23%bv ltac:(unfold A1_KEPT; repeat (first [left; reflexivity | right]))). exact H23.
- exact (a1_spills_kept E Wc memc memc' lyc pos c vv i HPRE HK' HSP).
Qed.

(* ---- the piece: CL (exv_pc 0x534) to LK (exv_pc 0x5f0) ---- *)
Lemma exvl_A1 : forall n m, (forall fx : YK11.FPState, CUT_LK (fx := fx) B ARx SK n m) ->
  forall fx : YK11.FPState, CUT_CLm (fx := fx) B ARx SK n m.
Proof.
intros n m HLK fx. unfold CUT_CLm. intros E lyc Sc Hpc Wc regs memc mdc k pos c i cap acc ip vv dlc. cbv zeta.
intros Hn HPRE HB Hi1 Hc Hc2 Hdep Hacc Hcur Hip Hdl Hii Hm HV Hdif H27 H22 H23
  S152 S88 S56 S48 S40 S80 S24 S16 S72 S8 S32 S136 S112 S128 S64 S104 S96 S120 S144.
assert (HSP : exv_spills E Wc memc lyc pos c vv i) by (unfold exv_spills; cbv zeta; repeat split; assumption).
pose proof (a1_geo E HPRE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (a1_len E HPRE) as HLEN.
pose proof asan_consts as (C1 & _).
assert (HiZ : 0 <= Z.of_nat i <= 3145728) by (clear - Hii Hip HLEN; lia).
assert (HBs : EXBs (fx := fx) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos)
  by (exists regs; split; [exact HB | intros r _; reflexivity]).
destruct (Z.eq_dec vv 0) as [Hv0 | Hv0].
- (* A: no node to compare *)
  subst vv.
  apply (a1_run0 fx E lyc Sc Hpc Wc regs memc mdc k pos _ HPRE HB S152).
  intros regs' memc' mdc' HJ' HPM' HK' HG' HR' R20 R24.
  apply (a1_fin fx n m E lyc Sc Hpc Wc regs memc mdc k pos c i cap acc ip 0 regs' memc' mdc' dlc 0 1 PjTree.JNull
    (HLK fx) Hn HPRE HB Hi1 Hc Hc2 Hdep Hacc Hip Hii Hm HV H27 H22 H23 HSP HJ' HPM'
    (fun a Ha _ => HK' a Ha) HG' HR' R20 R24).
  + exact (a1_cur_all Wc memc memc' (e_q E) _ _ _ _ dlc ltac:(clear - G5 C1; lia) ltac:(clear - G6; lia) HK' Hcur).
  + exact Hdl.
  + left. split; reflexivity.
  + intros nm u dl' Hdl' Hiff. rewrite <- Hacc in Hiff.
    exact (a1_bk0 E (c =? 123) dlc acc Hdif Hdl nm u dl' Hdl' Hiff).
- (* the node at e_v E *)
  pose proof Hdif as Hdif'.
  destruct Hdif as [(Hvz & _) | (Hve & _ & Htag & _)]; [exfalso; exact (Hv0 Hvz)|].
  subst vv.
  destruct (KNODE fx E lyc Sc Hpc Wc regs memc mdc k pos HPRE HBs Hv0)
    as (kids & Vcnt & Vkids & Hvra & Hv8 & Hv4 & Hv63 & Hkids).
  destruct (Nat.lt_ge_cases i (exv_count (e_t E))) as [Hlt | Hge].
  + (* C: item i exists *)
    destruct (Hkids ltac:(clear - Hlt; lia)) as (Hk0 & Hkc).
    apply (a1_runK fx E lyc Sc Hpc Wc regs memc mdc k pos (Z.of_nat (exv_count (e_t E))) (Z.of_nat i) kids _
      HPRE HB Hv0 Hv8 Vcnt Vkids Hvra ltac:(clear - HiZ; lia) ltac:(clear - HiZ; lia) ltac:(clear - Hlt; lia)
      Hk0 Hkc S152 S88 S136 S56 S112).
    intros regs' memc' mdc' HJ' HPM' HK' HG' HR' R20 R24.
    apply (a1_fin fx n m E lyc Sc Hpc Wc regs memc mdc k pos c i cap acc ip (e_v E) regs' memc' mdc' dlc
      (kids + 56 * Z.of_nat i) 0 (exv_kidt (e_t E) i) (HLK fx) Hn HPRE HB Hi1 Hc Hc2 Hdep Hacc Hip Hii Hm HV
      H27 H22 H23 HSP HJ' HPM' (fun a Ha _ => HK' a Ha) HG' HR' R20 R24).
    * exact (a1_cur_all Wc memc memc' (e_q E) _ _ _ _ dlc ltac:(clear - G5 C1; lia) ltac:(clear - G6; lia) HK'
        Hcur).
    * exact Hdl.
    * right. split; [reflexivity|]. split; [reflexivity|]. split; [exact Htag|].
      split; [exact Hv0|]. split; [exact Hlt|]. split; [reflexivity|].
      exists kids. split; [|split; [clear - Hk0 Hkc C1 HiZ; lia | reflexivity]].
      apply (exw_val_kept rsegs (w_H Wc) memc memc' (e_v E + 24) 8 kids); [|exact Vkids].
      intros x Hx. apply HK'. change (Z.of_nat 8) with 8 in Hx. clear - Hx Hv4 Hv63. lia.
    * intros nm u dl' Hdl' Hiff. rewrite <- Hacc in Hiff.
      exact (a1_bkK E (c =? 123) (e_v E) dlc (kids + 56 * Z.of_nat (length acc)) acc PCONS Hdif' Hv0
        ltac:(clear - Hk0; lia) ltac:(rewrite Hacc; exact Hlt) nm u dl' Hdl' Hiff).
  + (* B: no item i *)
    apply (a1_runL fx E lyc Sc Hpc Wc regs memc mdc k pos (Z.of_nat (exv_count (e_t E))) (Z.of_nat i) _
      HPRE HB Hv0 Hv8 Vcnt ltac:(clear; lia) ltac:(clear - HiZ; lia) ltac:(clear - Hge; lia) Hvra
      S152 S88 S136 S72 S80).
    intros regs' memc' mdc' HJ' HPM' HK' HG' HR' R20 R24 VQ.
    apply (a1_fin fx n m E lyc Sc Hpc Wc regs memc mdc k pos c i cap acc ip (e_v E) regs' memc' mdc' 1 0 1
      PjTree.JNull (HLK fx) Hn HPRE HB Hi1 Hc Hc2 Hdep Hacc Hip Hii Hm HV H27 H22 H23 HSP HJ' HPM' HK' HG' HR' R20
      R24).
    * apply (a1_cur_keep Wc memc memc' _ _ _ _ _ dlc 1); [|exact Hcur | exact VQ].
      intros a Ha. apply HK'; clear - Ha G5 G6 C1; lia.
    * right; reflexivity.
    * left. split; reflexivity.
    * intros nm u dl' Hdl' Hiff. rewrite <- Hacc in Hiff.
      exact (a1_bkL E (c =? 123) (e_v E) dlc acc PLONG Hdif' Hv0 ltac:(clear - Hge Hacc; lia) nm u dl' Hdl' Hiff).
Qed.
End x.

Print Assumptions exvl_A1.
