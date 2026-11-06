(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/B/Prog/LLVMFuzzerTestOneInput_segX_exit_td.v, with its module paths, module names and numbers changed; 635 of its 665 lines of code are new or changed and 322 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S4_PsRet.v, with its module names changed; 143 of its 195 lines of code are new or changed and 613 lines of the source are left out. *)
(* fuzz_preset lib/A, slice S4 (parse_string's decode stretch, part C): the WALK HELPERS of S4_PsDec.v. The engine
   facts a run from PS_DEC needs between its leaves: the out byte w is never a shadow byte, a shadow obligation at the
   current memory from the entry's text range, the cut a run reaches first (cut_of), the branch facts in Z.
   Numerals: 1276 / 1352 / 452 (DERIVED: offsets inside parse_string of the free cut, the success tail, the hex loop),
   2 ^ 47 / 2 ^ 44 / 8 (DERIVED: the address band, its shadow, a granule); no ADDRESS.
   GENERIC-P (a Theorem Labs lane 12:18Z / 12:22Z; base 44a91d58bb5): dec_w_ns is over
   ps_at_decP .. P (Variable P right after SK, as in S4_PsDecKit.v). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0p YCbqG YGcfNames YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_Charge PRH_FnAlloc PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CallerJ S4_PsBase S4_PsDecModel S4_PsDecKit.
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* the program listing's tables (the instance of record PL_prog_A) *)
Definition TPIx := @pl_tpi A_prog_listing PL_prog_A.
Definition TWx := @pl_tw A_prog_listing PL_prog_A.
(* the cut a run from ss reaches without a branch: the free cut, the success tail, the hex loop, or none (0) *)
Definition cut_of (K : nat) (ss : sstate) : Z :=
  let t c := match sym_run_toN_pi_tok TPIx TWx K dBx dBspan SH_o FUEL (PSO + c) ss with
             | (st', PTS_running) => (ss_pc (sh_ss st') =? PSO + c)%Z | _ => false end in
  if t 1276 then 1276 else if t 1352 then 1352 else if t 452 then 452 else if t 328 then 328 else 0.

(* the index of the first region of a state over atom n *)
Fixpoint idx_base (n : nat) (rs : smem) (k : nat) : nat :=
  match rs with
  | [] => k
  | rg :: rs' => if obase_eqb (YP09.r_base rg) (Some n) then k else idx_base n rs' (S k)
  end.

(* a signed compare of two values below 2 ^ 63 is the unsigned one *)
Lemma bt_lt_U : forall E a b, 0 <= U E a < 2 ^ 63 -> 0 <= U E b < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (U E a <? U E b).
Proof.
  intros E a b Ha Hb. cbn [branch_taken]. unfold bv_lts.
  change (bv_signed (sv_denot E a)) with (Sg E a). change (bv_signed (sv_denot E b)) with (Sg E b).
  rewrite !S_of_U. unfold bv_swrap, bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_half_modulus 64) with (2 ^ 63).
  rewrite (Z.mod_small (U E a + 2 ^ 63)) by lia. rewrite (Z.mod_small (U E b + 2 ^ 63)) by lia.
  replace (U E a + 2 ^ 63 - 2 ^ 63) with (U E a) by lia. replace (U E b + 2 ^ 63 - 2 ^ 63) with (U E b) by lia. reflexivity.
Qed.
Lemma bt_ge_U : forall E a b, 0 <= U E a < 2 ^ 63 -> 0 <= U E b < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (U E a <? U E b).
Proof.
  intros E a b Ha Hb. rewrite <- (bt_lt_U E a b Ha Hb). cbn [branch_taken]. reflexivity.
Qed.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instances PS_PrhImg PS_PAListing PS_PAImg.
#[local] Notation segs := (@pa_segs _ A_prog_listing PS_PAImg).
#[local] Notation VAL := (@pa_val _ A_prog_listing PS_PAImg).
#[local] Notation BASE := (@pa_val _ A_prog_listing PS_PAImg A_TEXT).
(* a leaf of a run, at the cut offset c, as the configuration a cut statement names *)
Lemma leaf_cfg : forall (W : world segs) E ss ms md Q c,
  st_ok_pi segs VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = PSO + c ->
  SRr segs W (cfg_at segs (ps_pc c) (ms_regs ms) (ms_mem ms) md) Q -> SRr segs W {| cfg_ms := ms; cfg_model := md |} Q.
Proof.
  intros W E ss ms md Q c HS Hrv Hpc H.
  rewrite (st_ok_pi_restrict_mkst (w_H W) E ss ms HS Hrv), Hpc.
  unfold cfg_at, ps_pc, PSO in *. replace (BASE + (PS_OFF + c)) with (BASE + PS_OFF + c) by lia. exact H.
Qed.
(* the byte a one-byte chunk of a region holds *)
Lemma val_mem_chunk1 : forall E m base e c, YP09.chunk_ok segs E m base (YP09.mkChunk 0 (CVal 1 e)) -> U E e = c -> 0 <= c < 256 ->
  val_mem segs m base 1 c.
Proof.
  intros E m base e c Hc HU Hc0 k Hk. assert (k = 0%nat) by lia. subst k.
  destruct (Hc 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2). cbn [cbyte YP09.c_val YP09.c_off] in Hb1, Hb2.
  injection Hb1 as <-. rewrite !Z.add_0_r in Hb2. cbn [Z.of_nat]. rewrite Z.add_0_r, Hb2. f_equal.
  unfold byte_of_word, YO0f.le_byte. fold (U E e). rewrite HU. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. change (8 * Z.of_nat 0) with 0. change (8 * 0) with 0. change (8 * Z.of_nat 1) with 8.
  rewrite !Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !(Z.mod_small c 256) by lia. reflexivity.
Qed.
Lemma region_of_st : forall E ss ms i rg, st_ok_pi segs VAL E ss ms -> nth_error (ss_mem ss) i = Some rg ->
  region_ok segs E (ms_mem ms) rg.
Proof.
  intros E ss ms i rg HS Hi. destruct (st_ok_mem_ok segs E _ ms HS) as (_ & Hrs & _).
  apply (proj1 (Forall_forall _ _) Hrs). destruct ss. cbn in Hi |- *. eapply nth_error_In. exact Hi.
Qed.
(* a shadow obligation of a run at the current memory mem', from the entry memory's text range *)
Lemma ob_range_w : forall H mem mem' E Bx x a n p m w,
  (forall y : word, bv_unsigned y <> w -> mrestrict H mem' y = mrestrict H mem y) ->
  (forall y, 0 <= y < 2 ^ 47 -> shadow_addr y <> w) -> 0 <= a -> a + n <= 2 ^ 47 ->
  range_addressable (aview segs H mem) SHADOW_OFF a n ->
  U E Bx = SHADOW_OFF -> U E x = p -> a <= p -> p + m <= a + n ->
  range_addressable (rd_of segs (mrestrict H mem')) (U E Bx) (U E x) m.
Proof.
  intros H mem mem' E Bx x a n p m w HM Hns Ha Han Hra HB Hx Hap Hpm.
  apply (ob_range segs H mem' E Bx x a n p m); [|exact HB | exact Hx | exact Hap | exact Hpm].
  eapply range_addressable_agree; [|exact Hra]. intros y Hy. apply aview_eq_of. apply HM.
  assert (Hy8 : 0 <= y / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  replace (shadow_of_addr SHADOW_OFF y) with (shadow_addr y) by reflexivity.
  rewrite unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia). apply Hns. lia.
Qed.
(* a text byte at the current memory: the stretch wrote only the out byte w *)
Lemma txt_cur : forall (W : world segs) mem mc w text tb x,
  (forall y : word, bv_unsigned y <> w -> mrestrict (w_H W) mc y = mrestrict (w_H W) mem y) ->
  garr8 segs (mrestrict (w_H W) mem) text tb -> text <= x < text + Z.of_nat (length tb) -> x <> w -> 0 <= x < 2 ^ 64 ->
  val_mem segs (mrestrict (w_H W) mc) x 1 (nth (Z.to_nat (x - text)) tb 0).
Proof.
  intros W mem mc w text tb x HM Hg Hx Hw Hx64. destruct (garr8_at _ text tb x Hg Hx) as [V _].
  apply (val_mem_keep W W mem mc x 1 _); [|exact V]. intros i Hi. cbn in Hi. apply aview_eq_of. apply HM.
  rewrite unsigned_lit_small by lia. lia.
Qed.
(* a shadow obligation over bytes whose shadow reads 0 at the current memory (alx_zshadow_byte: the machine stack) *)
Lemma ob_stack : forall H mem E Bx x p m,
  (forall a, p <= a < p + m -> aview segs H mem (SHADOW_OFF + a / 8) = Some 0) ->
  U E Bx = SHADOW_OFF -> U E x = p -> range_addressable (rd_of segs (mrestrict H mem)) (U E Bx) (U E x) m.
Proof.
  intros H mem E Bx x p m Hz HB Hx. rewrite HB, Hx. intros a Ha. exists 0. split; [|left; reflexivity].
  rewrite <- (aview_rd_of segs). unfold shadow_of_addr. apply Hz. exact Ha.
Qed.
End h.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Existing Instances PS_PrhImg PS_PAListing PS_PAImg.
#[local] Notation segs := (@pa_segs _ A_prog_listing PS_PAImg).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
(* the cut invariant (S4_PsBase.v Section gp; S4_PsDecKit.v's Variable P) *)
Variable P : (word -> option byte) -> Prop.
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.
Hypothesis HW : prh_head_wide.
(* the out byte is an application byte: never the shadow byte of an address below 2 ^ 47 *)
Lemma dec_w_ns : forall CTX CW D ly S Hp W regs mem md out w r Q,
  ps_pre B ARx CTX CW D -> ps_at_decP B ARx SK P D ly S Hp W regs mem md out w r Q ->
  forall y, 0 <= y < 2 ^ 47 -> shadow_addr y <> w.
Proof.
  intros CTX CW D ly S Hp W regs mem md out w r Q HPRE HDEC.
  destruct (dec_facts B ARx SK P LAWS HW CTX CW D ly S Hp W regs mem md out w r Q HPRE HDEC)
    as (Esp & Hsp & Hsp16 & Hspq & Hq47 & Hq8 & Ht0 & Htp & Hr & Htc & Hlen & Hout & Hw & Hoc & Hap & HAR).
  pose proof HDEC as (_ & (_ & _ & _ & _ & Eab & _) & _).
  pose proof cf_head_nonneg as Hh0.
  assert (Hin_o : In (out - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly S)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
  destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HAR Hin_o) as (_ & H4096o & Hco & Happ & _).
  rewrite (ps_req (Z.of_nat Q + 1 + cf_head)) in Hco, Happ by lia.
  intros y Hy E. assert (Hy8 : 0 <= y / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  unfold shadow_addr in E. subst w. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.
End w.

(* ---- one decode step from the cursor r, as the walk's leaves meet it ---- *)
Section m.
Variables (tb : list Z) (text r : Z).
Hypothesis Hr : text <= r < text + Z.of_nat (length tb).
Let b0 := nth (Z.to_nat (r - text)) tb 0.
Let b1 := nth (Z.to_nat (r + 1 - text)) tb 0.
Lemma lw_rest_end : forall x, text + Z.of_nat (length tb) <= x -> rest_atR tb text x = [].
Proof. intros x Hx. unfold rest_atR. apply skipn_all2. lia. Qed.
Lemma lw_rest0 : rest_atR tb text r = b0 :: rest_atR tb text (r + 1).
Proof. apply psd_rest_cons; [lia|]. apply nth_error_nth'. lia. Qed.
Lemma lw_rest1 : r + 1 < text + Z.of_nat (length tb) -> rest_atR tb text (r + 1) = b1 :: rest_atR tb text (r + 2).
Proof. intros H. replace (r + 2) with (r + 1 + 1) by lia. apply psd_rest_cons; [lia|]. apply nth_error_nth'. lia. Qed.
Lemma lw_escape_none : forall e, e <> 34 -> e <> 92 -> e <> 47 -> e <> 98 -> e <> 102 -> e <> 110 -> e <> 114 -> e <> 116 ->
  PjGrammar.escape e = None.
Proof.
  intros e H1 H2 H3 H4 H5 H6 H7 H8. unfold PjGrammar.escape.
  rewrite (proj2 (Z.eqb_neq e 34) H1), (proj2 (Z.eqb_neq e 92) H2), (proj2 (Z.eqb_neq e 47) H3), (proj2 (Z.eqb_neq e 98) H4),
    (proj2 (Z.eqb_neq e 102) H5), (proj2 (Z.eqb_neq e 110) H6), (proj2 (Z.eqb_neq e 114) H7), (proj2 (Z.eqb_neq e 116) H8).
  reflexivity.
Qed.
(* the refusals *)
Lemma lw_none_ctl : b0 <> 34 -> b0 < 32 -> PjGrammar.decode (rest_atR tb text r) = None.
Proof. intros H1 H2. rewrite lw_rest0. apply psd_dec_ctl; assumption. Qed.
Lemma lw_none_plain_end : b0 <> 34 -> 32 <= b0 -> b0 <> 92 -> text + Z.of_nat (length tb) <= r + 1 ->
  PjGrammar.decode (rest_atR tb text r) = None.
Proof. intros H1 H2 H3 H4. rewrite lw_rest0, (lw_rest_end (r + 1) H4), psd_dec_plain by assumption. reflexivity. Qed.
Lemma lw_none_bs_end : b0 = 92 -> text + Z.of_nat (length tb) <= r + 1 -> PjGrammar.decode (rest_atR tb text r) = None.
Proof. intros H1 H2. rewrite lw_rest0, (lw_rest_end (r + 1) H2), H1. reflexivity. Qed.
Lemma lw_none_bad : b0 = 92 -> r + 1 < text + Z.of_nat (length tb) -> b1 <> 117 -> PjGrammar.escape b1 = None ->
  PjGrammar.decode (rest_atR tb text r) = None.
Proof. intros H1 H2 H3 H4. rewrite lw_rest0, (lw_rest1 H2), H1. apply psd_dec_esc_bad; assumption. Qed.
Lemma lw_none_esc_end : forall c, b0 = 92 -> r + 1 < text + Z.of_nat (length tb) -> b1 <> 117 -> PjGrammar.escape b1 = Some c ->
  text + Z.of_nat (length tb) <= r + 2 -> PjGrammar.decode (rest_atR tb text r) = None.
Proof.
  intros c H1 H2 H3 H4 H5. rewrite lw_rest0, (lw_rest1 H2), H1, (psd_dec_esc _ _ _ H3 H4), (lw_rest_end (r + 2) H5). reflexivity.
Qed.
(* the steps *)
Lemma lw_step_plain : b0 <> 34 -> 32 <= b0 -> b0 <> 92 ->
  PjGrammar.decode (rest_atR tb text r) = PjGrammar.emit [b0] (PjGrammar.decode (rest_atR tb text (r + 1))) /\
  PjGrammar.scan (rest_atR tb text r) =
    option_map (fun q => (q + Z.to_nat (r + 1 - r))%nat) (PjGrammar.scan (rest_atR tb text (r + 1))).
Proof.
  intros H1 H2 H3. rewrite lw_rest0. split; [apply psd_dec_plain; assumption|].
  rewrite (psd_scan_plain _ _ H1 H3). replace (Z.to_nat (r + 1 - r)) with 1%nat by lia.
  destruct (PjGrammar.scan (rest_atR tb text (r + 1))); cbn; [f_equal; lia | reflexivity].
Qed.
Lemma lw_step_esc : forall c, b0 = 92 -> r + 1 < text + Z.of_nat (length tb) -> b1 <> 117 -> PjGrammar.escape b1 = Some c ->
  PjGrammar.decode (rest_atR tb text r) = PjGrammar.emit [c] (PjGrammar.decode (rest_atR tb text (r + 2))) /\
  PjGrammar.scan (rest_atR tb text r) =
    option_map (fun q => (q + Z.to_nat (r + 2 - r))%nat) (PjGrammar.scan (rest_atR tb text (r + 2))).
Proof.
  intros c H1 H2 H3 H4. rewrite lw_rest0, (lw_rest1 H2), H1. split; [apply psd_dec_esc; assumption|].
  rewrite psd_scan_esc. replace (Z.to_nat (r + 2 - r)) with 2%nat by lia.
  destruct (PjGrammar.scan (rest_atR tb text (r + 2))); cbn; [f_equal; lia | reflexivity].
Qed.
End m.

(* branch facts in Z *)
Ltac bnorm H :=
  repeat first [ rewrite negb_true_iff in H | rewrite negb_false_iff in H | rewrite Z.eqb_eq in H
               | rewrite Z.eqb_neq in H | rewrite Z.ltb_lt in H | rewrite Z.ltb_ge in H ].
