(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v; 1536 of its 1692 lines of code are new or changed and 1217 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_write_value.v, with its module paths and module names changed; 518 of its 589 lines of code are new or changed and 1621 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/ZZwv_cent.v, with its module paths and numbers changed; 843 of its 905 lines of code are new or changed and 527 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the ITEM LOOP of the lib/B (fs.asan-ubsan) container arms of write_value:
   the piece algebra of WriterValue.wvpieces' two container arms (ZZwvB_tree's wv_items / wv_mems), the first
   indent after the opening bracket (wvc_step_open), and the two loops (wvc_loop_arr / wvc_loop_obj), each turn of
   which is a run of ZZwvB_runs2 and a call of ZZwvB_arm, ending in the closing tail put (ZZwvB_close).
   Image A has no twin of this file: its container arms are unproved.
   rule 24: proves no function (kind: segment lemma) - the item loop of the container arms of write_value B.
   Rule 24 (proof-index, a Theorem Labs lane, unpiped): write_value has RELEASED proofs for fs's PLAIN and UBSAN
   builds only (lib/Prog, lib/U/Prog), none for an ASan image; 0x84010 is not in the released set. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_rres FSW_ret FSW_rd FSW_pj FSH_Fn_writer
FSW_write_value_entry ZZwvB_defs ZZwvB_arm ZZwvB_comp ZZwvB_kit ZZwvB_tree ZZwvB_inv ZZwvB_call ZZwvB_call2 ZZwvB_call3
ZZwvB_ret ZZwvB_res ZZwvB_runs1 ZZwvB_runs2 ZZwvB_step ZZwvB_arm ZZwvB_arm2 ZZwvB_entry ZZwvB_close.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterValue PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance
   resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section A. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis HPUT : put_spec B tfibsegs.
Hypothesis HPS : put_string_spec B tfibsegs.
Hypothesis HIND : indent_spec B tfibsegs.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Section St.
Variable F : wvc_fix.
Variables (ly0 : alayout) (S0 : astate) (U0 : list (Z * Z)) (W0 : world tfibsegs) (mem0 : word -> option byte)
  (md0 : Model) (regs0 : bvmap 5 word).
Hypothesis HE_sp16 : wf_sp F mod 16 = 0.
Hypothesis HE_ot16 : wf_ot F mod 16 = 0.
Hypothesis HE_oot : wf_o F + 32 <= wf_ot F.
Hypothesis HE_o8 : wf_o F mod 8 = 0.
Hypothesis HE_top : wf_ot F <= ly_top ly0.
Hypothesis HE_top47 : ly_top ly0 <= 2 ^ 47.
Hypothesis HE_lo : alloc_ceiling + STK_write_value (wf_m F) <= wf_sp F.
Hypothesis HE_gp : YK11.getr regs0 3%bv = w64 (as_gp B).
Hypothesis HE_tp : YK11.getr regs0 4%bv = w64 (as_tp B).
Hypothesis HE_cap0 : 0 <= wf_cap0 F.
Hypothesis HE_capl : wf_cap0 F <= wf_live F.
Hypothesis HE_cnt0 : 0 <= wf_cnt0 F.
Hypothesis HE_p : 0 <= wf_p F < alloc_ceiling.
Hypothesis HE_d : 0 <= wf_d F.
Hypothesis HE_dd : wf_d F + Z.of_nat (PjTree.depth (wf_t F)) <= 2 ^ 31 - 1.
Hypothesis HE_room : Z.of_nat (length (wf_text0 F)) + Z.of_nat (length (concat (wvc_WP F))) + 1 <= WMAX.
Hypothesis HE_bud : wbudget_pre S0 (wf_cap0 F) (wf_cnt0 F) (wf_live F) (WriterApp.putN (wvc_st0 F) (wvc_WP F)).
Hypothesis HE_frl : Z.of_nat (length (frames S0)) <= FRL_CRT_CALLEE.
Hypothesis HE_foot : forall x, wf_o F <= x < wf_ot F -> ~ PjStruct.pj_foot (wf_v F) (wf_D F) x.
Hypothesis HE_plain : jv_plain (wf_t F).
Hypothesis HE_ty :
  (wf_ty F = 5 /\ exists items, wf_t F = PjTree.JArr items /\ wf_n F = Z.of_nat (length items) /\ wf_keys F = 0) \/
  (wf_ty F = 6 /\ exists members, wf_t F = PjTree.JObj members /\ wf_n F = Z.of_nat (length members)).
Hypothesis HE_hdr : exists num capn,
  PjStruct.pj_hdr tfibsegs (rdW W0 mem0) (wf_v F) (wf_ty F) num (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) capn.
Hypothesis HE_n : 0 <= wf_n F < 2 ^ 54.
Hypothesis HE_kk : 0 < wf_n F -> 4096 <= wf_kids F /\ wf_kids F + 56 * wf_n F <= alloc_ceiling /\
                   (wf_ty F = 6 -> 4096 <= wf_keys F /\ wf_keys F + 8 * wf_n F <= alloc_ceiling).
Hypothesis HE_capM : wf_cap0 F <= WMAX.
Hypothesis HE_s0 : s0Z regs0 < alloc_ceiling \/ s0Z regs0 = wf_o F \/ wf_o F + 48 <= s0Z regs0.
Hypothesis HE_sp : spZ regs0 = wf_sp F.
Hypothesis HE_pre : exists ch0, fpreU tfibsegs B (STK_write_value (wf_m F)) ly0 S0 U0 W0 regs0 mem0 md0 ch0.

(* ================= the piece algebra of the two loops ================= *)
(* firstn (S j) l = firstn j l ++ [u] at an index that exists *)
Lemma wvc_firstn_S : forall (X : Type) (l : list X) j u,
  nth_error l j = Some u -> firstn (S j) l = firstn j l ++ [u].
Proof.
intros X l. induction l as [|x r IH]; intros j u H; [destruct j; discriminate H|].
destruct j as [|j]; cbn [nth_error firstn app] in H |- *.
- injection H as <-. reflexivity.
- f_equal. exact (IH j u H).
Qed.

Lemma wvc_firstn_len : forall (X : Type) (l : list X) j, (j <= length l)%nat -> length (firstn j l) = j.
Proof. intros X l j H. rewrite length_firstn. lia. Qed.

(* one item's group, for the array *)
Lemma wvc_items_step : forall items j u,
  nth_error items j = Some u ->
  wv_items (wvc_pp F) (wf_d F) 0%nat (firstn (S j) items) =
  wv_items (wvc_pp F) (wf_d F) 0%nat (firstn j items)
  ++ WriterValue.wcomma j ++ WriterValue.wind (wvc_pp F) (wf_d F + 1)
     ++ WriterValue.wvpieces u (wvc_pp F) (wf_d F + 1).
Proof.
intros items j u H.
rewrite (wvc_firstn_S _ items j u H), wv_items_app, (wvc_firstn_len _ items j).
2: { apply Nat.lt_le_incl. apply nth_error_Some. rewrite H. discriminate. }
cbn [plus]. rewrite wv_items_cons. cbn [wv_items]. rewrite !app_nil_r. reflexivity.
Qed.

(* one member's group, for the object *)
Lemma wvc_mems_step : forall members j nm u,
  nth_error members j = Some (nm, u) ->
  wv_mems (wvc_pp F) (wf_d F) 0%nat (firstn (S j) members) =
  wv_mems (wvc_pp F) (wf_d F) 0%nat (firstn j members)
  ++ WriterValue.wcomma j ++ WriterValue.wind (wvc_pp F) (wf_d F + 1)
     ++ WriterSpec.spieces nm ++ [WriterValue.wsep (wvc_pp F)]
     ++ WriterValue.wvpieces u (wvc_pp F) (wf_d F + 1).
Proof.
intros members j nm u H.
rewrite (wvc_firstn_S _ members j (nm, u) H), wv_mems_app, (wvc_firstn_len _ members j).
2: { apply Nat.lt_le_incl. apply nth_error_Some. rewrite H. discriminate. }
cbn [plus]. rewrite wv_mems_cons. cbn [wv_mems]. rewrite !app_nil_r. reflexivity.
Qed.

(* ================= the glue of the loop: ranges, the loop registers, the env, the frame chunks ================= *)
(* a container's depth is at least one, so the item depth d + 1 is an int32 (ZZwvB_step.wvc_d1's argument) *)
Lemma wvc_lp_d1 : wf_d F + 1 < 2 ^ 31.
Proof.
pose proof HE_dd as Hdd.
destruct HE_ty as [(_ & items & Ht & _ & _) | (_ & members & Ht & _)];
  rewrite Ht in Hdd; cbn [PjTree.depth] in Hdd; lia.
Qed.

(* the caller's journal window covers write_value's frame, which lies above the allocator's ceiling *)
Lemma wvc_lp_stk : wf_ot F - wvc_STK F <= wf_sp F - WVC_F /\ alloc_ceiling <= wf_sp F - WVC_F.
Proof. unfold wvc_STK. pose proof (wvc_stk (wf_m F)) as (Hs & _). lia. Qed.

Lemma wvc_lp_sp : forall ly Sa U (W : world tfibsegs) m buf st,
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly Sa U W m buf st -> wf_sp F + 8 <= wf_o F /\ wf_sp F <= wf_ot F.
Proof.
intros ly Sa U W m buf st H.
pose proof (wvc_sem_o_sp B F ly0 S0 U0 W0 mem0 regs0 ly Sa U W m buf st H). lia.
Qed.

(* a run between two calls writes write_value's frame only: the writer facts move to the memory at the call *)
Lemma wvc_lp_run : forall ly Sa U (W : world tfibsegs) m m' md' buf st,
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly Sa U W m buf st ->
  ARU tfibsegs B ly Sa U W m' md' ->
  (forall x : word, ~ (wf_sp F - WVC_F <= bv_unsigned x < wf_sp F) -> rdW W m' x = rdW W m x) ->
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly Sa U W m' buf st.
Proof.
intros ly Sa U W m m' md' buf st HS HA HF.
pose proof wvc_lp_stk as (_ & Hlo).
exact (wvc_sem_run B F ly0 S0 U0 W0 mem0 regs0 ly Sa U W m m' md' buf st HS HA HF Hlo ltac:(lia) ltac:(lia)).
Qed.

Lemma wvc_lp_vlow : forall ly Sa U (W : world tfibsegs) m md buf st,
  ARU tfibsegs B ly Sa U W m md ->
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly Sa U W m buf st -> 4096 <= wf_v F /\ wf_v F + 56 <= alloc_ceiling.
Proof.
intros ly Sa U W m md buf st HA HS.
destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HPO & _).
exact (fsw_pobj_low B ly Sa W _ md m (wf_v F) (proj1 HA) HPO).
Qed.

(* the node's header at any state of the arm (ZZwvB_step.wvc_hdr_at's argument) *)
Lemma wvc_lp_hdr : forall ly Sa U (W : world tfibsegs) m buf st,
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly Sa U W m buf st ->
  exists num capn,
    PjStruct.pj_hdr tfibsegs (rdW W m) (wf_v F) (wf_ty F) num (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) capn.
Proof.
intros ly Sa U W m buf st HSEM. destruct HE_hdr as (num & capn & H). exists num, capn.
apply (PjStruct.pj_hdr_eq tfibsegs (rdW W0 mem0)); [exact H|].
destruct HSEM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNB & _). exact HNB.
Qed.

(* ---- the loop's registers at a call (the register premises the four call steps share) ---- *)
Definition lp_regs (R : bvmap 5 word) (i : Z) : Prop :=
  YK11.getr R 8%bv = w64 (wf_o F) /\ YK11.getr R 9%bv = w64 (wf_v F) /\ YK11.getr R 19%bv = w64 (wf_p F) /\
  YK11.getr R 21%bv = w64 i /\ YK11.getr R 23%bv = w64 (56 * i) /\ YK11.getr R 25%bv = w64 (8 * i) /\
  YK11.getr R 18%bv = w64 (wf_v F + 40) /\ YK11.getr R 20%bv = w64 ((wf_v F + 24) / 8 + SHADOW_OFF) /\
  YK11.getr R 22%bv = w64 (wf_d F + 1) /\ YK11.getr R 24%bv = w64 (wf_v F + 24) /\
  YK11.getr R 26%bv = w64 0 /\ YK11.getr R 27%bv = w64 ((wf_v F + 40) / 8 + SHADOW_OFF) /\
  YK11.getr R 3%bv = YK11.getr regs0 3%bv /\ YK11.getr R 4%bv = YK11.getr regs0 4%bv /\
  spZ R = wf_sp F - WVC_F.

Ltac wvc_lp_in := cbv [In]; repeat (first [left; reflexivity | right]).
Ltac wvc_lp_ras := unfold WV_CONT_RAS; cbv [In]; repeat (first [left; reflexivity | right]).

Lemma lp_r9 : forall R i, lp_regs R i -> YK11.getr R 9%bv = w64 (wf_v F).
Proof. intros R i H. exact (proj1 (proj2 H)). Qed.

(* a run that keeps every loop register *)
Lemma lp_regs_keep : forall R R' i,
  lp_regs R i ->
  YK11.getr R' 2%bv = YK11.getr R 2%bv ->
  (forall q, In q [3;4;8;9;18;19;20;21;22;23;24;25;26;27]%bv -> YK11.getr R' q = YK11.getr R q) ->
  lp_regs R' i.
Proof.
intros R R' i (R8 & R9 & R19 & R21 & R23 & R25 & R18 & R20 & R22 & R24 & R26 & R27 & R3 & R4 & Hsp) H2 HK.
unfold lp_regs. unfold spZ in *. rewrite H2.
rewrite !HK by wvc_lp_in.
repeat split; assumption.
Qed.

(* the item test's run: the item index moves to i2 *)
Lemma lp_regs_step : forall R R' i i2,
  lp_regs R i ->
  YK11.getr R' 2%bv = YK11.getr R 2%bv ->
  (forall q, In q [3;4;8;9;18;19;20;22;24;26;27]%bv -> YK11.getr R' q = YK11.getr R q) ->
  YK11.getr R' 21%bv = w64 i2 -> YK11.getr R' 23%bv = w64 (56 * i2) -> YK11.getr R' 25%bv = w64 (8 * i2) ->
  lp_regs R' i2.
Proof.
intros R R' i i2 (R8 & R9 & R19 & R21 & R23 & R25 & R18 & R20 & R22 & R24 & R26 & R27 & R3 & R4 & Hsp) H2 HK
  S21 S23 S25.
unfold lp_regs. unfold spZ in *. rewrite H2, S21, S23, S25.
rewrite !HK by wvc_lp_in.
repeat split; assumption.
Qed.

(* ---- the loop invariant, taken apart ---- *)
Lemma wvc_lp_unpack : forall r i ke key P (W : world tfibsegs) ms mdc ly Sa U buf,
  wvc_inv B F r i ke key P ly0 S0 U0 W0 mem0 md0 regs0 W ms mdc ly Sa U buf ->
  wvc_at B (wvc_E F regs0 (ms_regs ms) ke key) (wvc_ssL (wf_ty F) (wf_p F) r) (wvc_SHL (wf_ty F)) W ms
    (wvc_STK F) (wf_ot F) (wvc_FP F) ly0 S0 W0 (unpoison U0 mem0) md0 [] ly Sa U mdc (wevk (wf_cap0 F) (wvc_stP F P)) /\
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly Sa U W (ms_mem ms) buf (wvc_stP F P) /\
  lp_regs (ms_regs ms) i /\ 0 <= i < wf_n F /\ ke = wf_keys F + 8 * i.
Proof.
intros r i ke key P W ms mdc ly Sa U buf H.
unfold wvc_inv in H. cbv zeta in H.
destruct H as (HAT & HSEM & R8 & R9 & R19 & R21 & R23 & R3 & R4 & R18 & R20 & R22 & R24 & R25 & R26 & R27 & Hsp &
  Hi & Hke).
split; [exact HAT|]. split; [exact HSEM|]. split; [|split; [exact Hi | exact Hke]].
unfold lp_regs. repeat split; assumption.
Qed.

(* ---- the env at a resume point: the registers and the arm's atoms the segments read ---- *)
Lemma wvc_lp_env : forall R i ke key, lp_regs R i ->
  ew (wvc_E F regs0 R ke key) 8 = Z_to_bv 64 (wf_o F) /\ ew (wvc_E F regs0 R ke key) 9 = Z_to_bv 64 (wf_v F) /\
  ew (wvc_E F regs0 R ke key) 19 = Z_to_bv 64 (wf_p F) /\ ew (wvc_E F regs0 R ke key) 21 = Z_to_bv 64 i /\
  ew (wvc_E F regs0 R ke key) 23 = Z_to_bv 64 (56 * i) /\
  bv_unsigned (ew (wvc_E F regs0 R ke key) 2) = wf_sp F - WVC_F /\
  ew (wvc_E F regs0 R ke key) (xatom 1) = Z_to_bv 64 (wf_kids F) /\
  ew (wvc_E F regs0 R ke key) (xatom 2) = Z_to_bv 64 (wf_keys F) /\
  ew (wvc_E F regs0 R ke key) (xatom 3) = Z_to_bv 64 (wf_n F) /\
  ew (wvc_E F regs0 R ke key) (xatom 4) = Z_to_bv 64 (wf_d F) /\
  ew (wvc_E F regs0 R ke key) (xatom 18) = Z_to_bv 64 ke /\ ew (wvc_E F regs0 R ke key) (xatom 19) = Z_to_bv 64 key.
Proof.
intros R i ke key (R8 & R9 & R19 & R21 & R23 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp).
unfold wvc_E. rewrite !fsw_ew_xatom.
rewrite (ew_Ereg_nat R _ 8 8%bv eq_refl), (ew_Ereg_nat R _ 9 9%bv eq_refl), (ew_Ereg_nat R _ 19 19%bv eq_refl),
  (ew_Ereg_nat R _ 21 21%bv eq_refl), (ew_Ereg_nat R _ 23 23%bv eq_refl), (ew_Ereg_nat R _ 2 2%bv eq_refl).
split; [exact R8|]. split; [exact R9|]. split; [exact R19|]. split; [exact R21|]. split; [exact R23|].
split; [exact Hsp|].
repeat split; reflexivity.
Qed.

(* the same at the open point (no loop register yet) *)
Lemma wvc_lp_envO : forall R ke key,
  YK11.getr R 8%bv = w64 (wf_o F) -> YK11.getr R 9%bv = w64 (wf_v F) -> YK11.getr R 19%bv = w64 (wf_p F) ->
  spZ R = wf_sp F - WVC_F ->
  ew (wvc_E F regs0 R ke key) 8 = Z_to_bv 64 (wf_o F) /\ ew (wvc_E F regs0 R ke key) 9 = Z_to_bv 64 (wf_v F) /\
  ew (wvc_E F regs0 R ke key) 19 = Z_to_bv 64 (wf_p F) /\
  bv_unsigned (ew (wvc_E F regs0 R ke key) 2) = wf_sp F - WVC_F /\
  ew (wvc_E F regs0 R ke key) 32 = Z_to_bv 64 SHADOW_OFF /\
  ew (wvc_E F regs0 R ke key) (xatom 3) = Z_to_bv 64 (wf_n F) /\
  ew (wvc_E F regs0 R ke key) (xatom 4) = Z_to_bv 64 (wf_d F).
Proof.
intros R ke key R8 R9 R19 Hsp.
split; [unfold wvc_E; rewrite (ew_Ereg_nat R _ 8 8%bv eq_refl); exact R8|].
split; [unfold wvc_E; rewrite (ew_Ereg_nat R _ 9 9%bv eq_refl); exact R9|].
split; [unfold wvc_E; rewrite (ew_Ereg_nat R _ 19 19%bv eq_refl); exact R19|].
split; [unfold wvc_E; rewrite (ew_Ereg_nat R _ 2 2%bv eq_refl); exact Hsp|].
split; [apply wvc_E_32|].
split; unfold wvc_E; rewrite fsw_ew_xatom; reflexivity.
Qed.

(* ---- the frame chunks in another env that agrees on the atoms they name (ZZwvB_res.wvc_csL_after, at one
   memory) ---- *)
Lemma wvc_lp_csL : forall E E' m b p,
  Forall (YP09.chunk_ok tfibsegs E m b) (wvc_csL p) ->
  ew E' 9 = ew E 9 -> ew E' 32 = ew E 32 -> (forall j, (4 <= j <= 17)%nat -> ew E' (xatom j) = ew E (xatom j)) ->
  Forall (YP09.chunk_ok tfibsegs E' m b) (wvc_csL p).
Proof.
intros E E' m b p HC E9 E32 HX.
apply Forall_forall. intros c Hc.
pose proof (proj1 (Forall_forall _ _) HC c Hc) as Hck. clear HC.
unfold wvc_csL, wvc_cs0 in Hc. cbn [seq map app In] in Hc.
repeat (destruct Hc as [<- | Hc]); [..| destruct Hc].
all: apply (wvr_chunk_move E E' _ _ _ _ Hck); [|intros i _; reflexivity].
all: intros i _; cbn [YP09.cbyte YP09.c_val YP09.c_off sv_denot wvc_shv]; rewrite ?E9, ?E32;
  try (rewrite HX by lia); reflexivity.
Qed.

(* the chunks a run left, in the env the next call step reads (another register file, key slot and key) *)
Lemma wvc_lp_chunks : forall R R' ke key ke' key' m,
  YK11.getr R' 9%bv = w64 (wf_v F) -> YK11.getr R 9%bv = w64 (wf_v F) ->
  Forall (YP09.chunk_ok tfibsegs (wvc_E F regs0 R ke key) m (wf_sp F - WVC_F)) (wvc_csL (wf_p F)) ->
  Forall (YP09.chunk_ok tfibsegs (wvc_E F regs0 R' ke' key') m (wf_sp F - WVC_F)) (wvc_csL (wf_p F)).
Proof.
intros R R' ke key ke' key' m H9' H9 HC.
apply (wvc_lp_csL _ _ m _ (wf_p F) HC).
- unfold wvc_E. rewrite (ew_Ereg_nat R' _ 9 9%bv eq_refl), (ew_Ereg_nat R _ 9 9%bv eq_refl).
  exact (eq_trans H9' (eq_sym H9)).
- rewrite !wvc_E_32. reflexivity.
- intros jj Hjj. unfold wvc_E. rewrite !fsw_ew_xatom.
  do 18 (destruct jj as [|jj]; [reflexivity|]). exfalso. lia.
Qed.

(* ---- the object's key pointer: the key region of the loop state holds it at the key slot ---- *)
Lemma wvc_lp_mod : forall a, Z_to_bv 64 (a mod 2 ^ 64) = Z_to_bv 64 a.
Proof.
intros a. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma wvc_lp_keyR_nth : forall p r, nth_error (ss_mem (wvc_ssL 6 p r)) 4 = Some wvc_keyR.
Proof. intros p r. reflexivity. Qed.

Lemma wvc_lp_key : forall E ss ms (W : world tfibsegs) m' ke key,
  st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) 4 = Some wvc_keyR ->
  ew E (xatom 18) = Z_to_bv 64 ke -> ew E (xatom 19) = Z_to_bv 64 key ->
  0 <= ke -> ke + 8 <= wf_sp F - WVC_F -> wf_sp F <= 2 ^ 64 ->
  (forall x : word, ~ (wf_sp F - WVC_F <= bv_unsigned x < wf_sp F) -> rdW W m' x = rdW W (ms_mem ms) x) ->
  PjStruct.pj_u64 tfibsegs (rdW W m') ke (key mod 2 ^ 64).
Proof.
intros E ss ms W m' ke key HS Hn E18 E19 Hk0 Hk1 Hsp HF.
assert (HWF : WVC_F = 192) by reflexivity.
pose proof (fsw_region_nth E ss (restrict (w_H W) ms) 4 wvc_keyR HS Hn) as HR.
cbn [ms_mem restrict] in HR. unfold wvc_keyR in HR.
assert (Hkm : 0 <= key mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
assert (HV : val_mem tfibsegs (rdW W (ms_mem ms)) (ke + 0) (N.to_nat 8) (key mod 2 ^ 64)).
{ apply (fsw_field E _ (xatom 18) ke _ 0 8 0 0 0 8%N (SOff (xatom 19) 0) (key mod 2 ^ 64) HR).
  - rewrite E18. apply unsigned_lit_small. lia.
  - cbn [In]. left. reflexivity.
  - rewrite fsw_SOff0, E19. symmetry. apply wvc_lp_mod.
  - change (8 * Z.of_N 8) with 64. lia.
  - lia. }
apply (fsw_val_pj_u64 tfibsegs); [| exact Hkm | lia | lia].
intros k Hk. etransitivity; [| exact (HV k Hk)].
rewrite Z.add_0_r. unfold mbyte. rewrite (HF (Z_to_bv 64 (ke + Z.of_nat k))); [reflexivity|].
rewrite unsigned_lit_small by lia. lia.
Qed.

(* ---- the literals the arm puts between the items ---- *)
Lemma wvc_lp_comma_ro : In (WVC_COMMA, [44]) FS_RO_STRS.
Proof. unfold FS_RO_STRS, WVC_COMMA. cbv [In]. repeat (first [left; reflexivity | right]). Qed.

Lemma wvc_lp_sep_ro : In (wvc_sep (wf_p F), WriterValue.wsep (wvc_pp F)) FS_RO_STRS.
Proof.
unfold wvc_pp, wvc_sep, WriterValue.wsep. destruct (wf_p F =? 0); cbn [negb];
  unfold FS_RO_STRS, WVC_COLON, WVC_COLON_SP; cbv [In]; repeat (first [left; reflexivity | right]).
Qed.

Lemma wvc_lp_seplen : Z.of_nat (length (WriterValue.wsep (wvc_pp F))) = wvc_seplen (wf_p F).
Proof. unfold wvc_pp, wvc_seplen, WriterValue.wsep. destruct (wf_p F =? 0); reflexivity. Qed.

(* ---- the pieces at the loop's resume points ---- *)
Lemma wvc_lp_PITEM_arr : forall items j u, nth_error items j = Some u ->
  wvc_PIND_arr F items j ++ WriterValue.wvpieces u (wvc_pp F) (wf_d F + 1) = wvc_PITEM_arr F items j.
Proof.
intros items j u Hu. unfold wvc_PIND_arr, wvc_PITEM_arr. rewrite (wvc_items_step items j u Hu).
rewrite <- !app_assoc. reflexivity.
Qed.

Lemma wvc_lp_PIND_arr_S : forall items j,
  (wvc_PITEM_arr F items j ++ [[44]]) ++ WriterValue.wind (wvc_pp F) (wf_d F + 1) = wvc_PIND_arr F items (S j).
Proof. intros items j. unfold wvc_PIND_arr, wvc_PITEM_arr. rewrite <- !app_assoc. reflexivity. Qed.

Lemma wvc_lp_PITEM_obj : forall members j nm u, nth_error members j = Some (nm, u) ->
  ((wvc_PIND_obj F members j ++ WriterSpec.spieces nm) ++ [WriterValue.wsep (wvc_pp F)])
    ++ WriterValue.wvpieces u (wvc_pp F) (wf_d F + 1) = wvc_PITEM_obj F members j.
Proof.
intros members j nm u Hu. unfold wvc_PIND_obj, wvc_PITEM_obj. rewrite (wvc_mems_step members j nm u Hu).
rewrite <- !app_assoc. reflexivity.
Qed.

Lemma wvc_lp_PIND_obj_S : forall members j,
  (wvc_PITEM_obj F members j ++ [[44]]) ++ WriterValue.wind (wvc_pp F) (wf_d F + 1) = wvc_PIND_obj F members (S j).
Proof. intros members j. unfold wvc_PIND_obj, wvc_PITEM_obj. rewrite <- !app_assoc. reflexivity. Qed.

(* ---- the model split of the arm's pieces at item j ---- *)
Lemma wvc_lp_pieces_arr : forall items p d, items <> [] ->
  WriterValue.wvpieces (PjTree.JArr items) p d = [91] :: wv_items p d 0%nat items ++ WriterValue.wind p d ++ [[93]].
Proof. intros items p d H. rewrite wv_pieces_arr. destruct items as [|x r]; [congruence | reflexivity]. Qed.

Lemma wvc_lp_pieces_obj : forall members p d, members <> [] ->
  WriterValue.wvpieces (PjTree.JObj members) p d =
  [123] :: wv_mems p d 0%nat members ++ WriterValue.wind p d ++ [[125]].
Proof. intros members p d H. rewrite wv_pieces_obj. destruct members as [|x r]; [congruence | reflexivity]. Qed.

Lemma wvc_lp_split_arr : forall items j u,
  wf_t F = PjTree.JArr items -> wf_ty F = 5 -> nth_error items j = Some u ->
  wvc_WP F = wvc_PIND_arr F items j ++ WriterValue.wvpieces u (wvc_pp F) (wf_d F + 1) ++
    (wv_items (wvc_pp F) (wf_d F) (S j) (skipn (S j) items) ++ WriterValue.wind (wvc_pp F) (wf_d F) ++ [[93]]).
Proof.
intros items j u Ht Hty Hu.
assert (Hj : (j < length items)%nat) by (apply nth_error_Some; rewrite Hu; discriminate).
unfold wvc_WP. rewrite Ht. change (negb (wf_p F =? 0)) with (wvc_pp F).
rewrite wvc_lp_pieces_arr by (destruct items; [exfalso; cbn [length] in Hj; lia | discriminate]).
rewrite <- (firstn_skipn (S j) items) at 1.
rewrite wv_items_app, (wvc_firstn_len _ items (S j)) by lia.
rewrite (wvc_items_step items j u Hu).
unfold wvc_PIND_arr, wvc_POPEN. rewrite Hty.
rewrite <- !app_assoc. reflexivity.
Qed.

Lemma wvc_lp_split_obj : forall members j nm u,
  wf_t F = PjTree.JObj members -> wf_ty F = 6 -> nth_error members j = Some (nm, u) ->
  wvc_WP F = wvc_PIND_obj F members j ++ WriterSpec.spieces nm ++ [WriterValue.wsep (wvc_pp F)] ++
    WriterValue.wvpieces u (wvc_pp F) (wf_d F + 1) ++
    (wv_mems (wvc_pp F) (wf_d F) (S j) (skipn (S j) members) ++ WriterValue.wind (wvc_pp F) (wf_d F) ++ [[125]]).
Proof.
intros members j nm u Ht Hty Hu.
assert (Hj : (j < length members)%nat) by (apply nth_error_Some; rewrite Hu; discriminate).
unfold wvc_WP. rewrite Ht. change (negb (wf_p F =? 0)) with (wvc_pp F).
rewrite wvc_lp_pieces_obj by (destruct members; [exfalso; cbn [length] in Hj; lia | discriminate]).
rewrite <- (firstn_skipn (S j) members) at 1.
rewrite wv_mems_app, (wvc_firstn_len _ members (S j)) by lia.
rewrite (wvc_mems_step members j nm u Hu).
unfold wvc_PIND_obj, wvc_POPEN. rewrite Hty.
rewrite <- !app_assoc. reflexivity.
Qed.

(* ---- the call steps of ZZwvB_arm / ZZwvB_close at a run's end state. Each closes the callee lemma's own Section
   hypotheses by eassumption (they are this Section's, word for word), so it does not depend on which of them that
   lemma's proof uses ---- *)
Lemma wvc_lp_put : forall r2 i' Pd Pc Rest ly Sa U (W : world tfibsegs) ms mdc buf s (bs : list Z)
    (Q : world tfibsegs -> config -> Prop),
  ms = mkst (ms_regs ms) (w64 A_put) (ms_mem ms) (seg_rom tfibsegs) ->
  wvc_WP F = Pd ++ Pc ++ Rest -> Pc = [bs] ->
  ajournal tfibsegs B (wvc_STK F) (wf_ot F) (wvc_FP F) ly0 S0 W0 (unpoison U0 mem0) md0 []
    ly Sa W (unpoison U (ms_mem ms)) mdc (wevk (wf_cap0 F) (wvc_stP F Pd)) ->
  ARU tfibsegs B ly Sa U W (ms_mem ms) mdc ->
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly Sa U W (ms_mem ms) buf (wvc_stP F Pd) ->
  Forall (YP09.chunk_ok tfibsegs (wvc_E F regs0 (ms_regs ms) (wf_keys F + 8 * i') 0) (rdW W (ms_mem ms))
    (wf_sp F - WVC_F)) (wvc_csL (wf_p F)) ->
  lp_regs (ms_regs ms) i' -> 0 <= i' < wf_n F ->
  YK11.getr (ms_regs ms) 1%bv = w64 r2 -> In r2 WV_CONT_RAS ->
  YK11.getr (ms_regs ms) 10%bv = w64 (wf_o F) -> YK11.getr (ms_regs ms) 11%bv = w64 s ->
  YK11.getr (ms_regs ms) 12%bv = w64 (Z.of_nat (length bs)) ->
  In (s, bs) FS_RO_STRS ->
  (forall W' ms2 mdc2 ly' S' U' buf' key', wle W W' ->
     wvc_inv B F r2 i' (wf_keys F + 8 * i') key' (Pd ++ Pc) ly0 S0 U0 W0 mem0 md0 regs0 W' ms2 mdc2 ly' S' U' buf' ->
     SRr tfibsegs W' (mkCfg ms2 mdc2) Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros r2 i' Pd Pc Rest ly Sa U W ms mdc buf s bs Q Hms HWP HPc HJ HARU HSEM HCH HR Hi R1 Hr2 R10 R11 R12 Hs HK.
destruct HR as (R8 & R9 & R19 & R21 & R23 & R25 & R18 & R20 & R22 & R24 & R26 & R27 & R3 & R4 & Hsp).
rewrite Hms. change (SRr tfibsegs W (cfg_at tfibsegs A_put (ms_regs ms) (ms_mem ms) mdc) Q).
eapply wvc_call_put; eassumption.
Qed.

Lemma wvc_lp_indent : forall r2 i' Pd Pc Rest ly Sa U (W : world tfibsegs) ms mdc buf dep
    (Q : world tfibsegs -> config -> Prop),
  ms = mkst (ms_regs ms) (w64 A_indent) (ms_mem ms) (seg_rom tfibsegs) ->
  wvc_WP F = Pd ++ Pc ++ Rest -> Pc = WriterValue.wind (wvc_pp F) dep ->
  ajournal tfibsegs B (wvc_STK F) (wf_ot F) (wvc_FP F) ly0 S0 W0 (unpoison U0 mem0) md0 []
    ly Sa W (unpoison U (ms_mem ms)) mdc (wevk (wf_cap0 F) (wvc_stP F Pd)) ->
  ARU tfibsegs B ly Sa U W (ms_mem ms) mdc ->
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly Sa U W (ms_mem ms) buf (wvc_stP F Pd) ->
  Forall (YP09.chunk_ok tfibsegs (wvc_E F regs0 (ms_regs ms) (wf_keys F + 8 * i') 0) (rdW W (ms_mem ms))
    (wf_sp F - WVC_F)) (wvc_csL (wf_p F)) ->
  lp_regs (ms_regs ms) i' -> 0 <= i' < wf_n F ->
  YK11.getr (ms_regs ms) 1%bv = w64 r2 -> In r2 WV_CONT_RAS ->
  YK11.getr (ms_regs ms) 10%bv = w64 (wf_o F) -> YK11.getr (ms_regs ms) 11%bv = w64 (wf_p F) ->
  YK11.getr (ms_regs ms) 12%bv = w64 dep -> 0 <= dep < 2 ^ 31 ->
  (forall W' ms2 mdc2 ly' S' U' buf' key', wle W W' ->
     wvc_inv B F r2 i' (wf_keys F + 8 * i') key' (Pd ++ Pc) ly0 S0 U0 W0 mem0 md0 regs0 W' ms2 mdc2 ly' S' U' buf' ->
     SRr tfibsegs W' (mkCfg ms2 mdc2) Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros r2 i' Pd Pc Rest ly Sa U W ms mdc buf dep Q Hms HWP HPc HJ HARU HSEM HCH HR Hi R1 Hr2 R10 R11 R12 Hdep HK.
destruct HR as (R8 & R9 & R19 & R21 & R23 & R25 & R18 & R20 & R22 & R24 & R26 & R27 & R3 & R4 & Hsp).
rewrite Hms. change (SRr tfibsegs W (cfg_at tfibsegs A_indent (ms_regs ms) (ms_mem ms) mdc) Q).
eapply wvc_call_indent; eassumption.
Qed.

Lemma wvc_lp_ps : forall r2 i' Pd Pc Rest ly Sa U (W : world tfibsegs) ms mdc buf x kk (nm : list Z)
    (Q : world tfibsegs -> config -> Prop),
  ms = mkst (ms_regs ms) (w64 A_put_string) (ms_mem ms) (seg_rom tfibsegs) ->
  wvc_WP F = Pd ++ Pc ++ Rest -> Pc = WriterSpec.spieces nm ->
  ajournal tfibsegs B (wvc_STK F) (wf_ot F) (wvc_FP F) ly0 S0 W0 (unpoison U0 mem0) md0 []
    ly Sa W (unpoison U (ms_mem ms)) mdc (wevk (wf_cap0 F) (wvc_stP F Pd)) ->
  ARU tfibsegs B ly Sa U W (ms_mem ms) mdc ->
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly Sa U W (ms_mem ms) buf (wvc_stP F Pd) ->
  Forall (YP09.chunk_ok tfibsegs (wvc_E F regs0 (ms_regs ms) (wf_keys F + 8 * i') x) (rdW W (ms_mem ms))
    (wf_sp F - WVC_F)) (wvc_csL (wf_p F)) ->
  lp_regs (ms_regs ms) i' -> 0 <= i' < wf_n F ->
  YK11.getr (ms_regs ms) 1%bv = w64 r2 -> In r2 WV_CONT_RAS ->
  YK11.getr (ms_regs ms) 10%bv = w64 (wf_o F) -> YK11.getr (ms_regs ms) 11%bv = w64 x ->
  PjStruct.pj_cstr tfibsegs (rdW W (ms_mem ms)) (fun a k => In (a, k) (wf_UL F)) x kk nm ->
  In (x, kk) (wf_D F) -> plain_bytes nm ->
  (forall W' ms2 mdc2 ly' S' U' buf' key', wle W W' ->
     wvc_inv B F r2 i' (wf_keys F + 8 * i') key' (Pd ++ Pc) ly0 S0 U0 W0 mem0 md0 regs0 W' ms2 mdc2 ly' S' U' buf' ->
     SRr tfibsegs W' (mkCfg ms2 mdc2) Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros r2 i' Pd Pc Rest ly Sa U W ms mdc buf x kk nm Q Hms HWP HPc HJ HARU HSEM HCH HR Hi R1 Hr2 R10 R11
  Hcs HxD Hpl HK.
destruct HR as (R8 & R9 & R19 & R21 & R23 & R25 & R18 & R20 & R22 & R24 & R26 & R27 & R3 & R4 & Hsp).
rewrite Hms. change (SRr tfibsegs W (cfg_at tfibsegs A_put_string (ms_regs ms) (ms_mem ms) mdc) Q).
eapply wvc_call_ps; eassumption.
Qed.

Lemma wvc_lp_item : forall r2 i' Pd Pc Rest ly Sa U (W : world tfibsegs) ms mdc buf (u : PjTree.jv) Du
    (Q : world tfibsegs -> config -> Prop),
  ms = mkst (ms_regs ms) (w64 A_write_value) (ms_mem ms) (seg_rom tfibsegs) ->
  write_value_spec_at B tfibsegs (S (2 - wf_m F)) ->
  wvc_WP F = Pd ++ Pc ++ Rest -> Pc = WriterValue.wvpieces u (wvc_pp F) (wf_d F + 1) ->
  (PjTree.depth (wf_t F) <= wf_m F)%nat -> (wf_m F <= 2)%nat ->
  (PjTree.depth u < PjTree.depth (wf_t F))%nat -> (wf_m F >= 1)%nat ->
  ajournal tfibsegs B (wvc_STK F) (wf_ot F) (wvc_FP F) ly0 S0 W0 (unpoison U0 mem0) md0 []
    ly Sa W (unpoison U (ms_mem ms)) mdc (wevk (wf_cap0 F) (wvc_stP F Pd)) ->
  ARU tfibsegs B ly Sa U W (ms_mem ms) mdc ->
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly Sa U W (ms_mem ms) buf (wvc_stP F Pd) ->
  Forall (YP09.chunk_ok tfibsegs (wvc_E F regs0 (ms_regs ms) (wf_keys F + 8 * i') 0) (rdW W (ms_mem ms))
    (wf_sp F - WVC_F)) (wvc_csL (wf_p F)) ->
  lp_regs (ms_regs ms) i' -> 0 <= i' < wf_n F ->
  YK11.getr (ms_regs ms) 1%bv = w64 r2 -> In r2 WV_CONT_RAS ->
  YK11.getr (ms_regs ms) 10%bv = w64 (wf_o F) -> YK11.getr (ms_regs ms) 11%bv = w64 (wf_kids F + 56 * i') ->
  YK11.getr (ms_regs ms) 12%bv = w64 (wf_p F) -> YK11.getr (ms_regs ms) 13%bv = w64 (wf_d F + 1) ->
  PjStruct.pj_node tfibsegs (rdW W (ms_mem ms)) (fun a k => In (a, k) (wf_UL F)) (wf_kids F + 56 * i') u Du ->
  (forall b, In b Du -> In b (wf_D F)) -> jv_plain u ->
  (forall x, wf_kids F + 56 * i' <= x < wf_kids F + 56 * i' + 56 -> PjStruct.pj_foot (wf_v F) (wf_D F) x) ->
  (forall W' ms2 mdc2 ly' S' U' buf' key', wle W W' ->
     wvc_inv B F r2 i' (wf_keys F + 8 * i') key' (Pd ++ Pc) ly0 S0 U0 W0 mem0 md0 regs0 W' ms2 mdc2 ly' S' U' buf' ->
     SRr tfibsegs W' (mkCfg ms2 mdc2) Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros r2 i' Pd Pc Rest ly Sa U W ms mdc buf u Du Q Hms HWV HWP HPc Hd1 Hd2 Hd3 Hd4 HJ HARU HSEM HCH HR Hi
  R1 Hr2 R10 R11 R12 R13 HN HDu Hpl Hft HK.
destruct HR as (R8 & R9 & R19 & R21 & R23 & R25 & R18 & R20 & R22 & R24 & R26 & R27 & R3 & R4 & Hsp).
rewrite Hms. change (SRr tfibsegs W (cfg_at tfibsegs A_write_value (ms_regs ms) (ms_mem ms) mdc) Q).
eapply wvc_call_item; eassumption.
Qed.

Lemma wvc_lp_close_ind : forall Pd Pc Rest ly Sa U (W : world tfibsegs) ms mdc buf
    (Q : world tfibsegs -> config -> Prop),
  ms = mkst (ms_regs ms) (w64 A_indent) (ms_mem ms) (seg_rom tfibsegs) ->
  wvc_WP F = Pd ++ Pc ++ Rest -> Pc = WriterValue.wind (wvc_pp F) (wf_d F) ->
  ajournal tfibsegs B (wvc_STK F) (wf_ot F) (wvc_FP F) ly0 S0 W0 (unpoison U0 mem0) md0 []
    ly Sa W (unpoison U (ms_mem ms)) mdc (wevk (wf_cap0 F) (wvc_stP F Pd)) ->
  ARU tfibsegs B ly Sa U W (ms_mem ms) mdc ->
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly Sa U W (ms_mem ms) buf (wvc_stP F Pd) ->
  Forall (YP09.chunk_ok tfibsegs (wvc_E F regs0 (ms_regs ms) (wf_keys F + 8 * wf_n F) 0) (rdW W (ms_mem ms))
    (wf_sp F - WVC_F)) (wvc_csL (wf_p F)) ->
  lp_regs (ms_regs ms) (wf_n F) ->
  YK11.getr (ms_regs ms) 1%bv = w64 WVC_R_CLOSE ->
  YK11.getr (ms_regs ms) 10%bv = w64 (wf_o F) -> YK11.getr (ms_regs ms) 11%bv = w64 (wf_p F) ->
  YK11.getr (ms_regs ms) 12%bv = w64 (wf_d F) ->
  0 < wf_n F ->
  (forall W' ms2 mdc2 ly' S' U' buf', wle W W' ->
     wvc_invN B F ly0 S0 U0 W0 mem0 md0 regs0 (Pd ++ Pc) W' ms2 mdc2 ly' S' U' buf' ->
     SRr tfibsegs W' (mkCfg ms2 mdc2) Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros Pd Pc Rest ly Sa U W ms mdc buf Q Hms HWP HPc HJ HARU HSEM HCH HR R1 R10 R11 R12 Hn HK.
destruct HR as (R8 & R9 & R19 & R21 & R23 & R25 & R18 & R20 & R22 & R24 & R26 & R27 & R3 & R4 & Hsp).
rewrite Hms. change (SRr tfibsegs W (cfg_at tfibsegs A_indent (ms_regs ms) (ms_mem ms) mdc) Q).
eapply wvc_call_indent_close; eassumption.
Qed.

Lemma wvc_lp_close : forall Pd ly Sa U (W : world tfibsegs) ms mdc buf,
  wvc_WP F = Pd ++ wvc_PCLOSE F ->
  wvc_invN B F ly0 S0 U0 W0 mem0 md0 regs0 Pd W ms mdc ly Sa U buf ->
  SRr tfibsegs W (mkCfg ms mdc)
    (wv_post B (wf_m F) (wf_ot F) (wf_o F) (wf_v F) (wf_p F) (wf_d F) (wf_t F) (wf_D F) (wf_UL F)
       (wf_buf0 F) (wf_cap0 F) (wf_failed0 F) (wf_text0 F) (wf_live F) (wf_peak0 F) (wf_cnt0 F) (wf_fail0 F)
       regs0 ly0 S0 U0 W0 mem0 md0).
Proof. intros Pd ly Sa U W ms mdc buf HWP HN. eapply wvc_arm_close; eassumption. Qed.


(* ================= the item loop ================= *)
(* ---- ARRAY: at the per-item indent's return with j items done, the arm runs to its post. One turn of the loop is
   wvc_seg_ind_arr (the run to the recursive call, through the UBSan guards 0x8424c / 0x84250 / 0x84268 of the kids
   slot, ruled out by wvc_gfA, wvc_cKIDS and wvc_cMULH) + wvc_call_item, then either wvc_seg_item_next +
   wvc_call_put (the comma) + wvc_seg_comma + wvc_call_indent, or wvc_seg_item_last + wvc_call_indent_close and the
   closing tail put (wvc_arm_close). ---- *)
Lemma wvc_loop_arr : forall items,
  wf_t F = PjTree.JArr items -> wf_ty F = 5 -> wf_keys F = 0 ->
  write_value_spec_at B tfibsegs (S (2 - wf_m F)) -> (1 <= wf_m F <= 2)%nat ->
  (PjTree.depth (wf_t F) <= wf_m F)%nat ->
  forall (r j : nat), (length items - j <= r)%nat -> (j < length items)%nat ->
  forall ly S U (W : world tfibsegs) ms mdc buf key,
  wvc_inv B F WVC_R_IND (Z.of_nat j) (wf_keys F + 8 * Z.of_nat j) key (wvc_PIND_arr F items j)
    ly0 S0 U0 W0 mem0 md0 regs0 W ms mdc ly S U buf ->
  SRr tfibsegs W (mkCfg ms mdc)
    (wv_post B (wf_m F) (wf_ot F) (wf_o F) (wf_v F) (wf_p F) (wf_d F) (wf_t F) (wf_D F) (wf_UL F)
       (wf_buf0 F) (wf_cap0 F) (wf_failed0 F) (wf_text0 F) (wf_live F) (wf_peak0 F) (wf_cnt0 F) (wf_fail0 F)
       regs0 ly0 S0 U0 W0 mem0 md0).
Proof.
intros items Ht Hty Hk0 HWV Hm Hdep r.
induction r as [|r IH]; intros j Hr Hj ly Sa U W ms mdc buf key HINV; [exfalso; lia|].
assert (Hlen : wf_n F = Z.of_nat (length items)).
{ destruct HE_ty as [(_ & items' & Ht' & Hn' & _) | (Hty' & _)]; [|lia].
  rewrite Ht in Ht'. injection Ht' as Eit. subst items'. exact Hn'. }
destruct (nth_error items j) as [u|] eqn:Hu; [|apply nth_error_None in Hu; exfalso; lia].
destruct (HE_kk ltac:(lia)) as (Hkd1 & Hkd2 & _).
pose proof HE_plain as Hpl0. rewrite Ht in Hpl0.
pose proof wvc_lp_stk as (Hstk & Hlo).
pose proof wvc_lp_d1 as Hd1.
destruct (wvc_lp_unpack _ _ _ _ _ _ _ _ _ _ _ _ HINV) as (HAT & HSEM & HR & Hi & _).
rewrite Hty in HAT.
destruct (wvc_lp_env _ _ (wf_keys F + 8 * Z.of_nat j) key HR)
  as (E8 & E9 & E19 & E21 & E23 & E2 & EX1 & EX2 & EX3 & EX4 & EX18 & EX19).
pose proof (wvc_lp_sp _ _ _ _ _ _ _ HSEM) as (Hosp & Hspot).
(* (1) the indent returned: the run to the item's write_value *)
eapply (wvc_seg_ind_arr B W ms mdc _ (wf_p F) (Z.of_nat j) (wf_n F) (wf_d F) (wf_kids F) (wvc_STK F) (wf_ot F)
          (wf_sp F));
  [ exact HAT | exact E21 | exact E23 | exact EX1 | exact EX4 | exact Hi | lia | lia | exact Hkd2 | exact HE_d
  | exact Hd1 | exact E2 | exact Hspot | exact Hstk | ].
intros ms1 mdc1 Hms1 HJ1 HARU1 HFR1 HCH1 R1_1 R10_1 R11_1 R12_1 R13_1 R2_1 RK1.
pose proof (wvc_lp_run _ _ _ _ _ _ _ _ _ HSEM HARU1 HFR1) as HSEM1.
pose proof (lp_regs_keep _ _ _ HR R2_1 RK1) as HR1.
pose proof HSEM1 as (_ & _ & _ & _ & _ & _ & _ & _ & HN1 & _).
rewrite Ht in HN1.
destruct (wv_arr_item _ _ _ _ _ _ _ HN1 Hu)
  as (num1 & kids1 & n1 & cap1 & Di1 & Dpre1 & Du & Dpost1 & HH1 & En1 & Hnc1 & Hc1 & _ & ED1 & _ & HU1 & HDu1 & _).
destruct (wvc_lp_hdr _ _ _ _ _ _ _ HSEM1) as (num1' & capn1' & HH1').
assert (Ek1 : kids1 = wf_kids F).
{ destruct HH1 as (_ & _ & _ & _ & Hk & _). destruct HH1' as (_ & _ & _ & _ & Hk' & _).
  exact (PjStruct.pj_u64_uniq _ _ _ _ _ Hk Hk'). }
subst kids1.
(* (2) the item's write_value, at the level below *)
eapply (wvc_lp_item WVC_R_ITEM (Z.of_nat j) (wvc_PIND_arr F items j) (WriterValue.wvpieces u (wvc_pp F) (wf_d F + 1))
          (wv_items (wvc_pp F) (wf_d F) (S j) (skipn (S j) items) ++ WriterValue.wind (wvc_pp F) (wf_d F) ++ [[93]])
          ly Sa U W ms1 mdc1 buf u Du);
  [ exact Hms1 | exact HWV | exact (wvc_lp_split_arr items j u Ht Hty Hu) | reflexivity | exact Hdep | lia
  | rewrite Ht; exact (wv_depth_item items j u Hu) | lia | exact HJ1 | exact HARU1 | exact HSEM1
  | exact (wvc_lp_chunks (ms_regs ms) (ms_regs ms1) (wf_keys F + 8 * Z.of_nat j) key (wf_keys F + 8 * Z.of_nat j) 0
             _ (lp_r9 _ _ HR1) (lp_r9 _ _ HR) HCH1)
  | exact HR1 | exact Hi | exact R1_1 | wvc_lp_ras | exact (eq_trans R10_1 E8) | exact R11_1
  | exact (eq_trans R12_1 E19) | exact R13_1 | exact HU1 | exact HDu1 | exact (wv_plain_item items j u Hpl0 Hu)
  | apply (wv_foot_kids (wf_v F) (wf_D F) (wf_kids F) cap1 (Z.of_nat j)); [rewrite ED1; left; reflexivity | lia | lia]
  | ].
intros W2 ms2 mdc2 ly2 S2 U2 buf2 key2 _ HINV2.
rewrite (wvc_lp_PITEM_arr items j u Hu) in HINV2.
destruct (wvc_lp_unpack _ _ _ _ _ _ _ _ _ _ _ _ HINV2) as (HAT2 & HSEM2 & HR2 & _ & _).
rewrite Hty in HAT2.
destruct (wvc_lp_env _ _ (wf_keys F + 8 * Z.of_nat j) key2 HR2)
  as (E8b & E9b & E19b & E21b & E23b & E2b & EX1b & EX2b & EX3b & EX4b & EX18b & EX19b).
destruct (Nat.lt_ge_cases (S j) (length items)) as [Hnx | Hla].
- (* (3) another item follows: the comma's put and the next item's indent, then the loop at item j + 1 *)
  destruct (nth_error items (S j)) as [u'|] eqn:Hu'; [|apply nth_error_None in Hu'; exfalso; lia].
  eapply (wvc_seg_item_next B W2 ms2 mdc2 _ 5 (wf_p F) (Z.of_nat j) (wf_n F) (wf_keys F) (wvc_STK F) (wf_ot F)
            (wf_sp F));
    [ exact HAT2 | left; reflexivity | exact E21b | exact E23b | exact EX2b | exact EX3b | exact EX18b
    | lia | lia | lia | lia | lia | exact E2b | exact Hspot | exact Hstk | ].
  intros ms3 mdc3 Hms3 HJ3 HARU3 HFR3 HCH3 R1_3 R10_3 R11_3 R12_3 R21_3 R23_3 R25_3 R2_3 RK3.
  pose proof (wvc_lp_run _ _ _ _ _ _ _ _ _ HSEM2 HARU3 HFR3) as HSEM3.
  pose proof (lp_regs_step _ _ _ (Z.of_nat j + 1) HR2 R2_3 RK3 R21_3 R23_3 R25_3) as HR3.
  eapply (wvc_lp_put WVC_R_COMMA (Z.of_nat j + 1) (wvc_PITEM_arr F items j) [[44]]
            (WriterValue.wind (wvc_pp F) (wf_d F + 1) ++ WriterValue.wvpieces u' (wvc_pp F) (wf_d F + 1) ++
             (wv_items (wvc_pp F) (wf_d F) (S (S j)) (skipn (S (S j)) items) ++
              WriterValue.wind (wvc_pp F) (wf_d F) ++ [[93]]))
            ly2 S2 U2 W2 ms3 mdc3 buf2 WVC_COMMA [44]);
    [ exact Hms3
    | rewrite (wvc_lp_split_arr items (S j) u' Ht Hty Hu'); unfold wvc_PIND_arr, wvc_PITEM_arr;
      rewrite <- !app_assoc; reflexivity
    | reflexivity | exact HJ3 | exact HARU3 | exact HSEM3
    | exact (wvc_lp_chunks (ms_regs ms2) (ms_regs ms3) (wf_keys F + 8 * Z.of_nat j) key2
               (wf_keys F + 8 * (Z.of_nat j + 1)) 0 _ (lp_r9 _ _ HR3) (lp_r9 _ _ HR2) HCH3)
    | exact HR3 | lia | exact R1_3 | wvc_lp_ras | exact (eq_trans R10_3 E8b) | exact R11_3 | exact R12_3
    | exact wvc_lp_comma_ro | ].
  intros W4 ms4 mdc4 ly4 S4 U4 buf4 key4 _ HINV4.
  destruct (wvc_lp_unpack _ _ _ _ _ _ _ _ _ _ _ _ HINV4) as (HAT4 & HSEM4 & HR4 & Hi4 & _).
  rewrite Hty in HAT4.
  destruct (wvc_lp_env _ _ (wf_keys F + 8 * (Z.of_nat j + 1)) key4 HR4)
    as (E8c & E9c & E19c & E21c & E23c & E2c & EX1c & EX2c & EX3c & EX4c & EX18c & EX19c).
  eapply (wvc_seg_comma B W4 ms4 mdc4 _ 5 (wf_p F) (wf_d F) (wvc_STK F) (wf_ot F) (wf_sp F));
    [ exact HAT4 | left; reflexivity | exact EX4c | exact HE_d | exact Hd1 | exact E2c | exact Hspot | exact Hstk | ].
  intros ms5 mdc5 Hms5 HJ5 HARU5 HFR5 HCH5 R1_5 R10_5 R11_5 R12_5 R2_5 RK5.
  pose proof (wvc_lp_run _ _ _ _ _ _ _ _ _ HSEM4 HARU5 HFR5) as HSEM5.
  pose proof (lp_regs_keep _ _ _ HR4 R2_5 RK5) as HR5.
  eapply (wvc_lp_indent WVC_R_IND (Z.of_nat j + 1) (wvc_PITEM_arr F items j ++ [[44]])
            (WriterValue.wind (wvc_pp F) (wf_d F + 1))
            (WriterValue.wvpieces u' (wvc_pp F) (wf_d F + 1) ++
             (wv_items (wvc_pp F) (wf_d F) (S (S j)) (skipn (S (S j)) items) ++
              WriterValue.wind (wvc_pp F) (wf_d F) ++ [[93]]))
            ly4 S4 U4 W4 ms5 mdc5 buf4 (wf_d F + 1));
    [ exact Hms5
    | rewrite (wvc_lp_split_arr items (S j) u' Ht Hty Hu'); unfold wvc_PIND_arr, wvc_PITEM_arr;
      rewrite <- !app_assoc; reflexivity
    | reflexivity | exact HJ5 | exact HARU5 | exact HSEM5
    | exact (wvc_lp_chunks (ms_regs ms4) (ms_regs ms5) (wf_keys F + 8 * (Z.of_nat j + 1)) key4
               (wf_keys F + 8 * (Z.of_nat j + 1)) 0 _ (lp_r9 _ _ HR5) (lp_r9 _ _ HR4) HCH5)
    | exact HR5 | exact Hi4 | exact R1_5 | wvc_lp_ras | exact (eq_trans R10_5 E8c) | exact (eq_trans R11_5 E19c)
    | exact R12_5 | lia | ].
  intros W6 ms6 mdc6 ly6 S6 U6 buf6 key6 _ HINV6.
  rewrite (wvc_lp_PIND_arr_S items j) in HINV6.
  apply (IH (S j) ltac:(lia) Hnx ly6 S6 U6 W6 ms6 mdc6 buf6 key6).
  rewrite Nat2Z.inj_succ. exact HINV6.
- (* (3') the last item: the closing indent, then the tail put of the bracket *)
  assert (Esk : skipn (S j) items = []) by (apply skipn_all2; lia).
  assert (HWPl : wvc_WP F = wvc_PITEM_arr F items j ++ WriterValue.wind (wvc_pp F) (wf_d F) ++ [[93]]).
  { rewrite (wvc_lp_split_arr items j u Ht Hty Hu), Esk, <- (wvc_lp_PITEM_arr items j u Hu).
    rewrite <- !app_assoc. reflexivity. }
  eapply (wvc_seg_item_last B W2 ms2 mdc2 _ 5 (wf_p F) (Z.of_nat j) (wf_n F) (wf_d F) (wf_keys F) (wvc_STK F)
            (wf_ot F) (wf_sp F));
    [ exact HAT2 | left; reflexivity | exact E21b | exact E23b | exact EX2b | exact EX3b | exact EX4b | exact EX18b
    | lia | lia | lia | lia | lia | exact HE_d | lia | exact E2b | exact Hspot | exact Hstk | ].
  intros ms3 mdc3 Hms3 HJ3 HARU3 HFR3 HCH3 R1_3 R10_3 R11_3 R12_3 R21_3 R23_3 R25_3 R2_3 RK3.
  pose proof (wvc_lp_run _ _ _ _ _ _ _ _ _ HSEM2 HARU3 HFR3) as HSEM3.
  pose proof (lp_regs_step _ _ _ (Z.of_nat j + 1) HR2 R2_3 RK3 R21_3 R23_3 R25_3) as HR3.
  assert (Enj : Z.of_nat j + 1 = wf_n F) by lia.
  rewrite Enj in HR3.
  eapply (wvc_lp_close_ind (wvc_PITEM_arr F items j) (WriterValue.wind (wvc_pp F) (wf_d F)) [[93]]
            ly2 S2 U2 W2 ms3 mdc3 buf2);
    [ exact Hms3 | exact HWPl | reflexivity | exact HJ3 | exact HARU3 | exact HSEM3
    | exact (wvc_lp_chunks (ms_regs ms2) (ms_regs ms3) (wf_keys F + 8 * Z.of_nat j) key2 (wf_keys F + 8 * wf_n F) 0
               _ (lp_r9 _ _ HR3) (lp_r9 _ _ HR2) HCH3)
    | exact HR3 | exact R1_3 | exact (eq_trans R10_3 E8b) | exact (eq_trans R11_3 E19b) | exact R12_3 | lia | ].
  intros W5 ms5 mdc5 ly5 S5 U5 buf5 _ HINVN.
  apply (wvc_lp_close (wvc_PITEM_arr F items j ++ WriterValue.wind (wvc_pp F) (wf_d F)) ly5 S5 U5 W5 ms5 mdc5 buf5);
    [|exact HINVN].
  rewrite HWPl. unfold wvc_PCLOSE. rewrite Hty. rewrite <- !app_assoc. reflexivity.
Qed.

(* ---- OBJECT: the same loop with the key's put_string and the separator's put between the indent and the item
   (the UBSan guards 0x841d8 / 0x841e0 / 0x841e4 / 0x841e8 / 0x841f4 of the key slot are on wvc_seg_ind_obj, ruled
   out by wvc_gfK, wvc_cI60 and wvc_cKEYS) ---- *)
Lemma wvc_loop_obj : forall members,
  wf_t F = PjTree.JObj members -> wf_ty F = 6 ->
  write_value_spec_at B tfibsegs (S (2 - wf_m F)) -> (1 <= wf_m F <= 2)%nat ->
  (PjTree.depth (wf_t F) <= wf_m F)%nat ->
  forall (r j : nat), (length members - j <= r)%nat -> (j < length members)%nat ->
  forall ly S U (W : world tfibsegs) ms mdc buf key,
  wvc_inv B F WVC_R_IND (Z.of_nat j) (wf_keys F + 8 * Z.of_nat j) key (wvc_PIND_obj F members j)
    ly0 S0 U0 W0 mem0 md0 regs0 W ms mdc ly S U buf ->
  SRr tfibsegs W (mkCfg ms mdc)
    (wv_post B (wf_m F) (wf_ot F) (wf_o F) (wf_v F) (wf_p F) (wf_d F) (wf_t F) (wf_D F) (wf_UL F)
       (wf_buf0 F) (wf_cap0 F) (wf_failed0 F) (wf_text0 F) (wf_live F) (wf_peak0 F) (wf_cnt0 F) (wf_fail0 F)
       regs0 ly0 S0 U0 W0 mem0 md0).
Proof.
intros members Ht Hty HWV Hm Hdep r.
induction r as [|r IH]; intros j Hr Hj ly Sa U W ms mdc buf key HINV; [exfalso; lia|].
assert (Hlen : wf_n F = Z.of_nat (length members)).
{ destruct HE_ty as [(Hty' & _) | (_ & members' & Ht' & Hn')]; [lia|].
  rewrite Ht in Ht'. injection Ht' as Em. subst members'. exact Hn'. }
destruct (nth_error members j) as [[nm u]|] eqn:Hu; [|apply nth_error_None in Hu; exfalso; lia].
destruct (HE_kk ltac:(lia)) as (Hkd1 & Hkd2 & Hky).
destruct (Hky Hty) as (Hky1 & Hky2).
pose proof HE_plain as Hpl0. rewrite Ht in Hpl0.
destruct (wv_plain_mem members j nm u Hpl0 Hu) as (Hpnm & Hpu).
pose proof wvc_lp_stk as (Hstk & Hlo).
pose proof wvc_lp_d1 as Hd1.
destruct (wvc_lp_unpack _ _ _ _ _ _ _ _ _ _ _ _ HINV) as (HAT & HSEM & HR & Hi & _).
rewrite Hty in HAT.
pose proof HAT as (HS0 & _).
destruct (wvc_lp_env _ _ (wf_keys F + 8 * Z.of_nat j) key HR)
  as (E8 & E9 & E19 & E21 & E23 & E2 & EX1 & EX2 & EX3 & EX4 & EX18 & EX19).
pose proof (wvc_lp_sp _ _ _ _ _ _ _ HSEM) as (Hosp & Hspot).
(* (1) the indent returned: the run to the key's put_string *)
eapply (wvc_seg_ind_obj B W ms mdc _ (wf_p F) (Z.of_nat j) (wf_n F) (wf_keys F) (wvc_STK F) (wf_ot F) (wf_sp F));
  [ exact HAT | exact E21 | exact EX2 | exact EX18 | exact Hi | lia | lia | exact Hky2 | exact E2 | exact Hspot
  | exact Hstk | ].
intros ms1 mdc1 Hms1 HJ1 HARU1 HFR1 HCH1 R1_1 R10_1 R11_1 R2_1 RK1.
pose proof (wvc_lp_run _ _ _ _ _ _ _ _ _ HSEM HARU1 HFR1) as HSEM1.
pose proof (lp_regs_keep _ _ _ HR R2_1 RK1) as HR1.
(* the key pointer the run loaded is the one the key slot holds (the loop state's key region) *)
assert (HKY : PjStruct.pj_u64 tfibsegs (rdW W (ms_mem ms1)) (wf_keys F + 8 * Z.of_nat j) (key mod 2 ^ 64)).
{ apply (wvc_lp_key _ _ ms W (ms_mem ms1) _ key HS0 (wvc_lp_keyR_nth _ _) EX18 EX19); [lia | lia | lia | exact HFR1]. }
pose proof HSEM1 as (_ & _ & _ & _ & _ & _ & _ & _ & HN1 & _).
rewrite Ht in HN1.
destruct (wv_obj_mem _ _ _ _ _ _ _ _ HN1 Hu)
  as (num1 & kids1 & keys1 & n1 & cap1 & Di1 & Dpre1 & x1 & kk1 & Du1 & Dpost1 & HH1 & En1 & Hnc1 & Hc1 & _ & _ &
      ED1 & _ & Hx1 & Hcs1 & _ & _ & HxD1 & _).
destruct (wvc_lp_hdr _ _ _ _ _ _ _ HSEM1) as (num1' & capn1' & HH1').
assert (Eky1 : keys1 = wf_keys F).
{ destruct HH1 as (_ & _ & _ & _ & _ & Hk & _). destruct HH1' as (_ & _ & _ & _ & _ & Hk' & _).
  exact (PjStruct.pj_u64_uniq _ _ _ _ _ Hk Hk'). }
subst keys1.
assert (Ex1 : x1 = key mod 2 ^ 64) by exact (PjStruct.pj_u64_uniq _ _ _ _ _ Hx1 HKY).
subst x1.
(* (2) the key's put_string *)
eapply (wvc_lp_ps WVC_R_KEY (Z.of_nat j) (wvc_PIND_obj F members j) (WriterSpec.spieces nm)
          ([WriterValue.wsep (wvc_pp F)] ++ WriterValue.wvpieces u (wvc_pp F) (wf_d F + 1) ++
           (wv_mems (wvc_pp F) (wf_d F) (S j) (skipn (S j) members) ++ WriterValue.wind (wvc_pp F) (wf_d F) ++
            [[125]]))
          ly Sa U W ms1 mdc1 buf (key mod 2 ^ 64) kk1 nm);
  [ exact Hms1 | exact (wvc_lp_split_obj members j nm u Ht Hty Hu) | reflexivity | exact HJ1 | exact HARU1
  | exact HSEM1
  | exact (wvc_lp_chunks (ms_regs ms) (ms_regs ms1) (wf_keys F + 8 * Z.of_nat j) key (wf_keys F + 8 * Z.of_nat j)
             (key mod 2 ^ 64) _ (lp_r9 _ _ HR1) (lp_r9 _ _ HR) HCH1)
  | exact HR1 | exact Hi | exact R1_1 | wvc_lp_ras | exact (eq_trans R10_1 E8)
  | exact (eq_trans R11_1 (eq_trans EX19 (eq_sym (wvc_lp_mod key)))) | exact Hcs1 | exact HxD1 | exact Hpnm | ].
intros W2 ms2 mdc2 ly2 S2 U2 buf2 key2 _ HINV2.
destruct (wvc_lp_unpack _ _ _ _ _ _ _ _ _ _ _ _ HINV2) as (HAT2 & HSEM2 & HR2 & _ & _).
rewrite Hty in HAT2.
destruct (wvc_lp_env _ _ (wf_keys F + 8 * Z.of_nat j) key2 HR2)
  as (E8b & E9b & E19b & E21b & E23b & E2b & EX1b & EX2b & EX3b & EX4b & EX18b & EX19b).
(* (3) the key's put_string returned: the run to the separator's put *)
eapply (wvc_seg_key B W2 ms2 mdc2 _ (wf_p F) (wvc_STK F) (wf_ot F) (wf_sp F));
  [ exact HAT2 | exact E2b | exact Hspot | exact Hstk | ].
intros ms3 mdc3 Hms3 HJ3 HARU3 HFR3 HCH3 R1_3 R10_3 R11_3 R12_3 R2_3 RK3.
pose proof (wvc_lp_run _ _ _ _ _ _ _ _ _ HSEM2 HARU3 HFR3) as HSEM3.
pose proof (lp_regs_keep _ _ _ HR2 R2_3 RK3) as HR3.
(* (4) the separator's put *)
eapply (wvc_lp_put WVC_R_SEP (Z.of_nat j) (wvc_PIND_obj F members j ++ WriterSpec.spieces nm)
          [WriterValue.wsep (wvc_pp F)]
          (WriterValue.wvpieces u (wvc_pp F) (wf_d F + 1) ++
           (wv_mems (wvc_pp F) (wf_d F) (S j) (skipn (S j) members) ++ WriterValue.wind (wvc_pp F) (wf_d F) ++
            [[125]]))
          ly2 S2 U2 W2 ms3 mdc3 buf2 (wvc_sep (wf_p F)) (WriterValue.wsep (wvc_pp F)));
  [ exact Hms3
  | rewrite (wvc_lp_split_obj members j nm u Ht Hty Hu); rewrite <- !app_assoc; reflexivity
  | reflexivity | exact HJ3 | exact HARU3 | exact HSEM3
  | exact (wvc_lp_chunks (ms_regs ms2) (ms_regs ms3) (wf_keys F + 8 * Z.of_nat j) key2 (wf_keys F + 8 * Z.of_nat j) 0
             _ (lp_r9 _ _ HR3) (lp_r9 _ _ HR2) HCH3)
  | exact HR3 | exact Hi | exact R1_3 | wvc_lp_ras | exact (eq_trans R10_3 E8b) | exact R11_3
  | rewrite wvc_lp_seplen; exact R12_3 | exact wvc_lp_sep_ro | ].
intros W4 ms4 mdc4 ly4 S4 U4 buf4 key4 _ HINV4.
destruct (wvc_lp_unpack _ _ _ _ _ _ _ _ _ _ _ _ HINV4) as (HAT4 & HSEM4 & HR4 & _ & _).
rewrite Hty in HAT4.
destruct (wvc_lp_env _ _ (wf_keys F + 8 * Z.of_nat j) key4 HR4)
  as (E8c & E9c & E19c & E21c & E23c & E2c & EX1c & EX2c & EX3c & EX4c & EX18c & EX19c).
(* (5) the separator's put returned: the run to the value's write_value *)
eapply (wvc_seg_sep B W4 ms4 mdc4 _ (wf_p F) (Z.of_nat j) (wf_n F) (wf_d F) (wf_kids F) (wvc_STK F) (wf_ot F)
          (wf_sp F));
  [ exact HAT4 | exact E21c | exact E23c | exact EX1c | exact EX4c | exact Hi | lia | lia | exact Hkd2 | exact HE_d
  | exact Hd1 | exact E2c | exact Hspot | exact Hstk | ].
intros ms5 mdc5 Hms5 HJ5 HARU5 HFR5 HCH5 R1_5 R10_5 R11_5 R12_5 R13_5 R2_5 RK5.
pose proof (wvc_lp_run _ _ _ _ _ _ _ _ _ HSEM4 HARU5 HFR5) as HSEM5.
pose proof (lp_regs_keep _ _ _ HR4 R2_5 RK5) as HR5.
pose proof HSEM5 as (_ & _ & _ & _ & _ & _ & _ & _ & HN5 & _).
rewrite Ht in HN5.
destruct (wv_obj_mem _ _ _ _ _ _ _ _ HN5 Hu)
  as (num5 & kids5 & keys5 & n5 & cap5 & Di5 & Dpre5 & x5 & kk5 & Du & Dpost5 & HH5 & En5 & Hnc5 & Hc5 & _ & _ &
      ED5 & _ & _ & _ & HU5 & HDu5 & _ & _).
destruct (wvc_lp_hdr _ _ _ _ _ _ _ HSEM5) as (num5' & capn5' & HH5').
assert (Ekd5 : kids5 = wf_kids F).
{ destruct HH5 as (_ & _ & _ & _ & Hk & _). destruct HH5' as (_ & _ & _ & _ & Hk' & _).
  exact (PjStruct.pj_u64_uniq _ _ _ _ _ Hk Hk'). }
subst kids5.
(* (6) the value's write_value, at the level below *)
eapply (wvc_lp_item WVC_R_ITEM (Z.of_nat j)
          ((wvc_PIND_obj F members j ++ WriterSpec.spieces nm) ++ [WriterValue.wsep (wvc_pp F)])
          (WriterValue.wvpieces u (wvc_pp F) (wf_d F + 1))
          (wv_mems (wvc_pp F) (wf_d F) (S j) (skipn (S j) members) ++ WriterValue.wind (wvc_pp F) (wf_d F) ++ [[125]])
          ly4 S4 U4 W4 ms5 mdc5 buf4 u Du);
  [ exact Hms5 | exact HWV
  | rewrite (wvc_lp_split_obj members j nm u Ht Hty Hu); rewrite <- !app_assoc; reflexivity
  | reflexivity | exact Hdep | lia | rewrite Ht; exact (wv_depth_mem members j nm u Hu) | lia
  | exact HJ5 | exact HARU5 | exact HSEM5
  | exact (wvc_lp_chunks (ms_regs ms4) (ms_regs ms5) (wf_keys F + 8 * Z.of_nat j) key4 (wf_keys F + 8 * Z.of_nat j) 0
             _ (lp_r9 _ _ HR5) (lp_r9 _ _ HR4) HCH5)
  | exact HR5 | exact Hi | exact R1_5 | wvc_lp_ras | exact (eq_trans R10_5 E8c) | exact R11_5
  | exact (eq_trans R12_5 E19c) | exact R13_5 | exact HU5 | exact HDu5 | exact Hpu
  | apply (wv_foot_kids (wf_v F) (wf_D F) (wf_kids F) cap5 (Z.of_nat j)); [rewrite ED5; left; reflexivity | lia | lia]
  | ].
intros W6 ms6 mdc6 ly6 S6 U6 buf6 key6 _ HINV6.
rewrite (wvc_lp_PITEM_obj members j nm u Hu) in HINV6.
destruct (wvc_lp_unpack _ _ _ _ _ _ _ _ _ _ _ _ HINV6) as (HAT6 & HSEM6 & HR6 & _ & _).
rewrite Hty in HAT6.
destruct (wvc_lp_env _ _ (wf_keys F + 8 * Z.of_nat j) key6 HR6)
  as (E8d & E9d & E19d & E21d & E23d & E2d & EX1d & EX2d & EX3d & EX4d & EX18d & EX19d).
destruct (Nat.lt_ge_cases (S j) (length members)) as [Hnx | Hla].
- (* (7) another member follows: the comma's put and the next member's indent, then the loop at member j + 1 *)
  destruct (nth_error members (S j)) as [[nm' u']|] eqn:Hu'; [|apply nth_error_None in Hu'; exfalso; lia].
  eapply (wvc_seg_item_next B W6 ms6 mdc6 _ 6 (wf_p F) (Z.of_nat j) (wf_n F) (wf_keys F) (wvc_STK F) (wf_ot F)
            (wf_sp F));
    [ exact HAT6 | right; reflexivity | exact E21d | exact E23d | exact EX2d | exact EX3d | exact EX18d
    | lia | lia | lia | lia | exact Hky2 | exact E2d | exact Hspot | exact Hstk | ].
  intros ms7 mdc7 Hms7 HJ7 HARU7 HFR7 HCH7 R1_7 R10_7 R11_7 R12_7 R21_7 R23_7 R25_7 R2_7 RK7.
  pose proof (wvc_lp_run _ _ _ _ _ _ _ _ _ HSEM6 HARU7 HFR7) as HSEM7.
  pose proof (lp_regs_step _ _ _ (Z.of_nat j + 1) HR6 R2_7 RK7 R21_7 R23_7 R25_7) as HR7.
  eapply (wvc_lp_put WVC_R_COMMA (Z.of_nat j + 1) (wvc_PITEM_obj F members j) [[44]]
            (WriterValue.wind (wvc_pp F) (wf_d F + 1) ++ WriterSpec.spieces nm' ++ [WriterValue.wsep (wvc_pp F)] ++
             WriterValue.wvpieces u' (wvc_pp F) (wf_d F + 1) ++
             (wv_mems (wvc_pp F) (wf_d F) (S (S j)) (skipn (S (S j)) members) ++
              WriterValue.wind (wvc_pp F) (wf_d F) ++ [[125]]))
            ly6 S6 U6 W6 ms7 mdc7 buf6 WVC_COMMA [44]);
    [ exact Hms7
    | rewrite (wvc_lp_split_obj members (S j) nm' u' Ht Hty Hu'); unfold wvc_PIND_obj, wvc_PITEM_obj;
      rewrite <- !app_assoc; reflexivity
    | reflexivity | exact HJ7 | exact HARU7 | exact HSEM7
    | exact (wvc_lp_chunks (ms_regs ms6) (ms_regs ms7) (wf_keys F + 8 * Z.of_nat j) key6
               (wf_keys F + 8 * (Z.of_nat j + 1)) 0 _ (lp_r9 _ _ HR7) (lp_r9 _ _ HR6) HCH7)
    | exact HR7 | lia | exact R1_7 | wvc_lp_ras | exact (eq_trans R10_7 E8d) | exact R11_7 | exact R12_7
    | exact wvc_lp_comma_ro | ].
  intros W8 ms8 mdc8 ly8 S8 U8 buf8 key8 _ HINV8.
  destruct (wvc_lp_unpack _ _ _ _ _ _ _ _ _ _ _ _ HINV8) as (HAT8 & HSEM8 & HR8 & Hi8 & _).
  rewrite Hty in HAT8.
  destruct (wvc_lp_env _ _ (wf_keys F + 8 * (Z.of_nat j + 1)) key8 HR8)
    as (E8e & E9e & E19e & E21e & E23e & E2e & EX1e & EX2e & EX3e & EX4e & EX18e & EX19e).
  eapply (wvc_seg_comma B W8 ms8 mdc8 _ 6 (wf_p F) (wf_d F) (wvc_STK F) (wf_ot F) (wf_sp F));
    [ exact HAT8 | right; reflexivity | exact EX4e | exact HE_d | exact Hd1 | exact E2e | exact Hspot | exact Hstk | ].
  intros ms9 mdc9 Hms9 HJ9 HARU9 HFR9 HCH9 R1_9 R10_9 R11_9 R12_9 R2_9 RK9.
  pose proof (wvc_lp_run _ _ _ _ _ _ _ _ _ HSEM8 HARU9 HFR9) as HSEM9.
  pose proof (lp_regs_keep _ _ _ HR8 R2_9 RK9) as HR9.
  eapply (wvc_lp_indent WVC_R_IND (Z.of_nat j + 1) (wvc_PITEM_obj F members j ++ [[44]])
            (WriterValue.wind (wvc_pp F) (wf_d F + 1))
            (WriterSpec.spieces nm' ++ [WriterValue.wsep (wvc_pp F)] ++ WriterValue.wvpieces u' (wvc_pp F) (wf_d F + 1) ++
             (wv_mems (wvc_pp F) (wf_d F) (S (S j)) (skipn (S (S j)) members) ++
              WriterValue.wind (wvc_pp F) (wf_d F) ++ [[125]]))
            ly8 S8 U8 W8 ms9 mdc9 buf8 (wf_d F + 1));
    [ exact Hms9
    | rewrite (wvc_lp_split_obj members (S j) nm' u' Ht Hty Hu'); unfold wvc_PIND_obj, wvc_PITEM_obj;
      rewrite <- !app_assoc; reflexivity
    | reflexivity | exact HJ9 | exact HARU9 | exact HSEM9
    | exact (wvc_lp_chunks (ms_regs ms8) (ms_regs ms9) (wf_keys F + 8 * (Z.of_nat j + 1)) key8
               (wf_keys F + 8 * (Z.of_nat j + 1)) 0 _ (lp_r9 _ _ HR9) (lp_r9 _ _ HR8) HCH9)
    | exact HR9 | exact Hi8 | exact R1_9 | wvc_lp_ras | exact (eq_trans R10_9 E8e) | exact (eq_trans R11_9 E19e)
    | exact R12_9 | lia | ].
  intros W10 ms10 mdc10 ly10 S10 U10 buf10 key10 _ HINV10.
  rewrite (wvc_lp_PIND_obj_S members j) in HINV10.
  apply (IH (S j) ltac:(lia) Hnx ly10 S10 U10 W10 ms10 mdc10 buf10 key10).
  rewrite Nat2Z.inj_succ. exact HINV10.
- (* (7') the last member: the closing indent, then the tail put of the brace *)
  assert (Esk : skipn (S j) members = []) by (apply skipn_all2; lia).
  assert (HWPl : wvc_WP F = wvc_PITEM_obj F members j ++ WriterValue.wind (wvc_pp F) (wf_d F) ++ [[125]]).
  { rewrite (wvc_lp_split_obj members j nm u Ht Hty Hu), Esk, <- (wvc_lp_PITEM_obj members j nm u Hu).
    rewrite <- !app_assoc. reflexivity. }
  eapply (wvc_seg_item_last B W6 ms6 mdc6 _ 6 (wf_p F) (Z.of_nat j) (wf_n F) (wf_d F) (wf_keys F) (wvc_STK F)
            (wf_ot F) (wf_sp F));
    [ exact HAT6 | right; reflexivity | exact E21d | exact E23d | exact EX2d | exact EX3d | exact EX4d | exact EX18d
    | lia | lia | lia | lia | exact Hky2 | exact HE_d | lia | exact E2d | exact Hspot | exact Hstk | ].
  intros ms7 mdc7 Hms7 HJ7 HARU7 HFR7 HCH7 R1_7 R10_7 R11_7 R12_7 R21_7 R23_7 R25_7 R2_7 RK7.
  pose proof (wvc_lp_run _ _ _ _ _ _ _ _ _ HSEM6 HARU7 HFR7) as HSEM7.
  pose proof (lp_regs_step _ _ _ (Z.of_nat j + 1) HR6 R2_7 RK7 R21_7 R23_7 R25_7) as HR7.
  assert (Enj : Z.of_nat j + 1 = wf_n F) by lia.
  rewrite Enj in HR7.
  eapply (wvc_lp_close_ind (wvc_PITEM_obj F members j) (WriterValue.wind (wvc_pp F) (wf_d F)) [[125]]
            ly6 S6 U6 W6 ms7 mdc7 buf6);
    [ exact Hms7 | exact HWPl | reflexivity | exact HJ7 | exact HARU7 | exact HSEM7
    | exact (wvc_lp_chunks (ms_regs ms6) (ms_regs ms7) (wf_keys F + 8 * Z.of_nat j) key6 (wf_keys F + 8 * wf_n F) 0
               _ (lp_r9 _ _ HR7) (lp_r9 _ _ HR6) HCH7)
    | exact HR7 | exact R1_7 | exact (eq_trans R10_7 E8d) | exact (eq_trans R11_7 E19d) | exact R12_7 | lia | ].
  intros W8 ms8 mdc8 ly8 S8 U8 buf8 _ HINVN.
  apply (wvc_lp_close (wvc_PITEM_obj F members j ++ WriterValue.wind (wvc_pp F) (wf_d F)) ly8 S8 U8 W8 ms8 mdc8 buf8);
    [|exact HINVN].
  rewrite HWPl. unfold wvc_PCLOSE. rewrite Hty. rewrite <- !app_assoc. reflexivity.
Qed.

(* ---- the open point with n <> 0: the run to the first indent (wvc_seg_open_ind, through the UBSan guard 0x8418c
   on d + 1, ruled out by wvc_cSLT) and that indent, giving the loop invariant at item 0 ---- *)
Lemma wvc_step_open : forall ly S U (W : world tfibsegs) ms mdc buf (Q : world tfibsegs -> config -> Prop),
  0 < wf_n F ->
  (exists Rest, wvc_WP F = wvc_POPEN F ++ WriterValue.wind (wvc_pp F) (wf_d F + 1) ++ Rest) ->
  wvc_invO B F ly0 S0 U0 W0 mem0 md0 regs0 W ms mdc ly S U buf ->
  (forall W' ms2 mdc2 ly' S' U' buf' key', wle W W' ->
     wvc_inv B F WVC_R_IND 0 (wf_keys F) key'
       (wvc_POPEN F ++ WriterValue.wind (wvc_pp F) (wf_d F + 1))
       ly0 S0 U0 W0 mem0 md0 regs0 W' ms2 mdc2 ly' S' U' buf' ->
     SRr tfibsegs W' (mkCfg ms2 mdc2) Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros ly Sa U W ms mdc buf Q Hn (Rest & HWP) HINV HK.
unfold wvc_invO in HINV. cbv zeta in HINV.
destruct HINV as (HAT & HSEM & R8 & R9 & R19 & R3 & R4 & Hsp).
pose proof (wvc_lp_sp _ _ _ _ _ _ _ HSEM) as (Hosp & Hspot).
pose proof wvc_lp_stk as (Hstk & Hlo).
pose proof wvc_lp_d1 as Hd1.
pose proof HAT as (_ & _ & _ & HARU0).
pose proof (wvc_lp_vlow _ _ _ _ _ _ _ _ HARU0 HSEM) as (Hv1 & Hv2).
pose proof asan_consts as (C1 & _).
destruct (wvc_lp_envO (ms_regs ms) (wf_keys F) 0 R8 R9 R19 Hsp) as (E8 & E9 & E19 & E2 & E32 & EX3 & EX4).
(* the run to the first item's indent (the UBSan guard 0x8418c is ruled out inside wvc_seg_open_ind) *)
eapply (wvc_seg_open_ind B W ms mdc _ (wf_ty F) (wf_n F) (wf_d F) (wf_p F) (wvc_STK F) (wf_ot F) (wf_sp F));
  [ exact HAT
  | destruct HE_ty as [(Hty & _) | (Hty & _)]; [left | right]; exact Hty
  | exact EX3 | lia | lia | exact EX4 | exact HE_d | exact Hd1 | exact E19 | exact HE_p | exact E2
  | exact Hspot | exact Hstk | ].
intros ms1 mdc1 HJ1 HARU1 HFR1 HCH1 R1_1 R10_1 R11_1 R12_1 R2_1 RK1 R18_1 R20_1 R21_1 R22_1 R23_1 R24_1 R25_1
  R26_1 R27_1 Hms1.
pose proof (wvc_lp_run _ _ _ _ _ _ _ _ _ HSEM HARU1 HFR1) as HSEM1.
(* the loop registers at item 0, from the run's symbolic values *)
assert (HR1 : lp_regs (ms_regs ms1) 0).
{ unfold lp_regs.
  rewrite (RK1 8%bv ltac:(wvc_lp_in)), (RK1 9%bv ltac:(wvc_lp_in)), (RK1 19%bv ltac:(wvc_lp_in)),
    (RK1 3%bv ltac:(wvc_lp_in)), (RK1 4%bv ltac:(wvc_lp_in)).
  unfold spZ in *. rewrite R2_1.
  split; [exact R8|]. split; [exact R9|]. split; [exact R19|]. split; [exact R21_1|].
  split; [exact R23_1|]. split; [exact R25_1|].
  split; [rewrite R18_1; apply wvc_den_val; apply (wvc_u_off _ 9 (wf_v F)); [exact E9 | lia | lia]|].
  split; [rewrite R20_1; apply wvc_den_val; apply (wvc_shv_U _ 24 (wf_v F));
          [exact E9 | exact E32 | lia | lia | lia]|].
  split; [exact R22_1|].
  split; [rewrite R24_1; apply wvc_den_val; apply (wvc_u_off _ 9 (wf_v F)); [exact E9 | lia | lia]|].
  split; [exact R26_1|].
  split; [rewrite R27_1; apply wvc_den_val; apply (wvc_shv_U _ 40 (wf_v F));
          [exact E9 | exact E32 | lia | lia | lia]|].
  split; [exact R3|]. split; [exact R4|]. exact Hsp. }
(* the first item's indent, at depth d + 1 (WriterValue.wcomma 0 = [], so the pieces are the bracket and the indent) *)
eapply (wvc_lp_indent WVC_R_IND 0 (wvc_POPEN F) (WriterValue.wind (wvc_pp F) (wf_d F + 1)) Rest
          ly Sa U W ms1 mdc1 buf (wf_d F + 1));
  [ exact Hms1 | exact HWP | reflexivity | exact HJ1 | exact HARU1 | exact HSEM1
  | exact (wvc_lp_chunks (ms_regs ms) (ms_regs ms1) (wf_keys F) 0 (wf_keys F + 8 * 0) 0 _ (lp_r9 _ _ HR1) R9 HCH1)
  | exact HR1 | lia | exact R1_1 | wvc_lp_ras | exact (eq_trans R10_1 E8) | exact (eq_trans R11_1 E19)
  | exact R12_1 | lia | ].
intros W2 ms2 mdc2 ly2 S2 U2 buf2 key2 Hle HINV2.
apply (HK W2 ms2 mdc2 ly2 S2 U2 buf2 key2 Hle).
replace (wf_keys F) with (wf_keys F + 8 * 0) by lia. exact HINV2.
Qed.

End St.
End A.
