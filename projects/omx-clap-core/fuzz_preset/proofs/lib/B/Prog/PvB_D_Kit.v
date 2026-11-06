(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_D1p56.v, with its module paths and module names changed; 298 of its 342 lines of code are new or changed and 697 lines of the source are left out. *)
(* fuzz_preset image B (asan-ubsan), parse_value 0x8637c (lane PValueB, segment D): the helpers the dispatch walk
   (PvB_D.v) and its three call arms (PvB_D_CLit.v, PvB_D_CStr.v, PvB_D_CItems.v) share: list / byte facts, the
   dispatch's branch conditions on the byte c (atom 34), the shadow address q / 8 + base, the frame pv_frame keeps,
   and the tactics of a no-write stretch (chaining the byte equalities and presence growth along runs, a register's
   value at the end of a run, the env agreement across havoc / ewset, closed nat side conditions), and fpre's
   return-address bound at a call (the kit of record's fpre last conjunct `raZ regs < YM05.alloc_ceiling`: the jal's
   return pc is a listing slot, below the ceiling).
   Rule 24: proves no function (kind: segment helpers). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PvB_Defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Instance PIB : PrhImg := prh_img_B.

(* ---- a listing slot's pc is below the run's allocation ceiling (PvB_NC.v pnc_slot_lt_ceil, restated: no D file
   imports PvB_NC.v; the proof is PRW_StepKit.pa_slot_lt_ceil's, cold/h-hpreset-7-walk-S7b c3a0b928f54). The slot's
   word is fetched from an image segment (pa_cert, pa_tbl_ok), so the pc is in_img, so below kLowMemEnd
   (pa_segs_low), which is below CEIL_MIN <= YM05.alloc_ceiling. ---- *)
Section pc. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {L : ptable asym} {PL : PAListing L} {PI : PAImg L}.
Lemma pvd_slot_lt_ceil : forall k e, 0 <= k < 2 ^ 40 -> plookup pl_tpi k = Some e ->
  pa_val A_TEXT + k < YM05.alloc_ceiling.
Proof.
intros k e Hk40 Hk. pose proof pa_B_ok as HB. rewrite <- pl_tpi_eq in Hk.
pose proof (cert_slot asym (clookup pa_tbl) pa_val pa_sigma L pa_cert k e Hk) as [Hc Hk0].
unfold pi_slot_check in Hc.
destruct (clookup pa_tbl (pa_val A_TEXT + k)) as [wz|] eqn:Hf; [|discriminate].
pose proof (pa_tbl_ok _ _ Hf) as Hfw.
unfold fetch_word in Hfw. destruct (negb _); [discriminate|].
unfold code_read in Hfw.
destruct (find_segment pa_segs (bv_unsigned (Z_to_bv 64 (pa_val A_TEXT + k))) (Z.of_N 4)) as [sg|] eqn:Hfs; [|discriminate].
destruct (find_segment_hit _ _ _ _ Hfs) as (Hin & Hlo & Hhi).
assert (Himg : in_img pa_segs (bv_unsigned (Z_to_bv 64 (pa_val A_TEXT + k)))).
{ exists sg. split; [exact Hin|]. change (Z.of_N 4) with 4 in Hhi. lia. }
pose proof (pa_segs_low _ Himg) as HR.
rewrite Z_to_bv_unsigned in HR. unfold bv_wrap in HR. change (bv_modulus 64) with (2 ^ 64) in HR.
rewrite Z.mod_small in HR by lia.
pose proof (@YM05.alloc_ceiling_value rc) as [[HC _] _]. unfold kLowMemEnd in HR. lia.
Qed.
End pc.

Section c.
Context {fx0 : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the kit rule: YCbqG's 16-field record at the harness head length (the instance's AR_laws_x_xs) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.

(* fpre's return-address bound at a call whose ra is the listing slot BASE + ret *)
Lemma pvd_ret_lt_ceil : forall (regs : bvmap 5 word) ret e, getr regs 1 = Z_to_bv 64 (BASE + ret) ->
  0 <= ret < 2 ^ 40 -> plookup (@pl_tpi _ PL_prog_B) ret = Some e -> raZ regs < YM05.alloc_ceiling.
Proof.
intros regs ret e R1 Hr Hk. pose proof (@pa_B_ok _ B_prog_listing PA) as HB.
unfold raZ. rewrite R1, unsigned_lit_small by lia.
exact (pvd_slot_lt_ceil (PL := PL_prog_B) (PI := PA) ret e Hr Hk).
Qed.

(* a stack byte reads shadow 0 at every allocator state (YCbqG's alx_zshadow_byte) *)
Lemma pvd_stack_ra : forall ly S Hp W mem md a n, ARx ly S Hp W mem md ->
  ly_stk_lo ly <= a -> a + n <= ly_stk_hi ly ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a n.
Proof.
intros ly S Hp W mem md a n HAR Hlo Hhi x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr. apply (alx_zshadow_byte SEGS B ARx LAWS ly S Hp W mem md x HAR). lia.
Qed.

(* ---- small list / byte helpers ---- *)
Lemma pvd_cons_of_len : forall (l : list Z), (0 < length l)%nat -> exists c y, l = c :: y.
Proof. intros [|c y] H; [cbn in H; lia | exists c, y; reflexivity]. Qed.
Lemma pvd_nth_skipn : forall (l : list Z) k b rest, skipn k l = b :: rest -> nth k l 0 = b /\ (k < length l)%nat.
Proof.
induction l as [|x l IH]; intros [|k] b rest H; cbn in H; try discriminate.
- injection H as -> ->. cbn. split; [reflexivity | lia].
- destruct (IH k b rest H) as [H1 H2]. cbn. split; [exact H1 | lia].
Qed.
(* a run whose regions have no write window changes no byte *)
Lemma pvd_nowin : forall E rs (m m' : word -> option byte),
  (forall a, ~ in_wrange E rs a) -> frame_of E rs m m' -> forall x, m' x = m x.
Proof. intros E rs m m' Hn HF x. apply HF. apply Hn. Qed.
Lemma pvd_mbyte_eq : forall (m m' : word -> option byte), (forall x, m' x = m x) ->
  forall a, mbyte SEGS m' a = mbyte SEGS m a.
Proof. intros m m' H a. unfold mbyte. rewrite H. reflexivity. Qed.

(* ---- the dispatch compares the zero-extended byte with small constants ---- *)
Lemma pvd_blt_U : forall E a b, U E a < half64 -> U E b < half64 ->
  branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (U E a <? U E b).
Proof. intros E a b Ha Hb. cbn [branch_taken]. unfold bv_lts. unfold U in Ha, Hb.
rewrite !signed_of_small by assumption. reflexivity. Qed.
Definition zbr (cond : branch_cond) (x y : Z) : bool :=
  match cond with
  | BC_EQ => x =? y | BC_NE => negb (x =? y) | BC_LT | BC_LTU => x <? y | BC_GE | BC_GEU => negb (x <? y)
  end.
Lemma pvd_br_gen : forall E a b x y cond, U E a = x -> U E b = y -> 0 <= x < 256 -> 0 <= y < 256 ->
  branch_taken cond (sv_denot E a) (sv_denot E b) = zbr cond x y.
Proof.
intros E a b x y cond Ha Hb Hx Hy.
assert (Ha' : U E a < half64) by (rewrite Ha; unfold half64; lia).
assert (Hb' : U E b < half64) by (rewrite Hb; unfold half64; lia).
destruct cond; cbn [zbr].
- rewrite branch_eq_U, Ha, Hb. reflexivity.
- rewrite branch_ne_U, Ha, Hb. reflexivity.
- rewrite pvd_blt_U, Ha, Hb by assumption. reflexivity.
- change (branch_taken BC_GE (sv_denot E a) (sv_denot E b)) with (negb (branch_taken BC_LT (sv_denot E a) (sv_denot E b))).
  rewrite pvd_blt_U, Ha, Hb by assumption. reflexivity.
- rewrite branch_ltu_U, Ha, Hb. reflexivity.
- rewrite branch_geu_U, Ha, Hb. reflexivity.
Qed.
Lemma pvd_br_kc : forall E' c k cond, U E' (SExt false 8 (SOff 34 0)) = c -> 0 <= c < 256 -> 0 <= k < 256 ->
  branch_taken cond (sv_denot E' (SLit k)) (sv_denot E' (SExt false 8 (SOff 34 0))) = zbr cond k c.
Proof. intros E' c k cond Hu Hc Hk. apply pvd_br_gen; [apply U_lit; lia | exact Hu | exact Hk | exact Hc]. Qed.
Lemma pvd_br_ck : forall E' c k cond, U E' (SExt false 8 (SOff 34 0)) = c -> 0 <= c < 256 -> 0 <= k < 256 ->
  branch_taken cond (sv_denot E' (SExt false 8 (SOff 34 0))) (sv_denot E' (SLit k)) = zbr cond c k.
Proof. intros E' c k cond Hu Hc Hk. apply pvd_br_gen; [exact Hu | apply U_lit; lia | exact Hc | exact Hk]. Qed.
(* the shadow address q / 8 + base the code computes (h-verbs-1's skw_denot_shx, skip_ws_x.v) *)
Lemma pvd_denot_shx : forall E n m v sb, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 sb -> 0 <= v < 2 ^ 63 ->
  0 <= sb < 2 ^ 32 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff m 0)) = Z_to_bv 64 (sb + v / 8).
Proof.
intros E n m v sb Hn Hm Hv Hsb.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff m 0)))). f_equal.
change (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff m 0)) = sb + v / 8).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Hn, Hm.
rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r.
change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos v 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound v 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (zcanon_id v) by (unfold M64; lia). rewrite (zcanon_id (v / 8)) by (unfold M64; lia).
rewrite (zcanon_id sb) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma pvd_U_w64 : forall E e z, U E e = z -> 0 <= z < 2 ^ 64 -> sv_denot E e = w64 z.
Proof. intros E e z H Hz. apply bv_eq. unfold U in H. rewrite H. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. Qed.

(* ---- the frame pv_frame states survives a change that keeps its bytes (the real frame [Y, sp0), the fake frame
   [fa, fa + 64) and the fake frame's 8 shadow bytes) and keeps their presence ---- *)
Lemma pvd_frame_tr : forall regs0 sp0 Y fa fl shb (W : world SEGS) mem mem',
  (forall a, (Y <= a < sp0 \/ fa <= a < fa + 64 \/ SHADOW_OFF + fa / 8 <= a < SHADOW_OFF + fa / 8 + 8) ->
     mbyte SEGS (rdW W mem') a = mbyte SEGS (rdW W mem) a) ->
  (forall a, (Y <= a < sp0 \/ fa <= a < fa + 64) -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
  pv_frame regs0 sp0 Y fa fl shb W mem -> pv_frame regs0 sp0 Y fa fl shb W mem'.
Proof.
intros regs0 sp0 Y fa fl shb W mem mem' HK HP (HYr & HY32 & HPR & Vsav & V48 & Vm & Vd & Vp & Vf & HPf & Hl & G).
assert (VT : forall a n v, (forall kk, (kk < n)%nat -> Y <= a + Z.of_nat kk < sp0 \/ fa <= a + Z.of_nat kk < fa + 64) ->
  val_mem SEGS (rdW W mem) a n v -> val_mem SEGS (rdW W mem') a n v).
{ intros a n v Hr Hv kk Hk. rewrite HK; [exact (Hv kk Hk)|]. destruct (Hr kk Hk) as [H1|H1]; [left|right; left]; exact H1. }
unfold pv_frame. split; [exact HYr|]. split; [exact HY32|].
split; [intros a Ha; apply HP; [left; exact Ha | exact (HPR a Ha)]|].
split.
{ rewrite Forall_forall in Vsav |- *. intros [o r] Hin. apply VT; [|exact (Vsav _ Hin)].
  intros kk Hk. left. cbn [fst].
  assert (Ho : -104 <= o <= -8).
  { unfold pv_saved in Hin. repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <-; lia|]). destruct Hin. }
  lia. }
split; [apply VT; [intros kk Hk; left; lia | exact V48]|].
split; [apply VT; [intros kk Hk; right; lia | exact Vm]|].
split; [apply VT; [intros kk Hk; right; lia | exact Vd]|].
split; [apply VT; [intros kk Hk; right; lia | exact Vp]|].
split; [apply VT; [intros kk Hk; right; lia | exact Vf]|].
split; [intros a Ha; apply HP; [right; exact Ha | exact (HPf a Ha)]|].
split; [exact Hl|].
intros j Hj. destruct (G j Hj) as [Gv Gr]. split; [|exact Gr].
intros kk Hk. rewrite HK; [exact (Gv kk Hk)|]. right; right. rewrite Hl in Hj. cbn in Hk. lia.
Qed.
Lemma pvd_agree_ewset : forall k0 E0 E n w, (k0 <= n)%nat -> env_agree k0 E0 E -> env_agree k0 E0 (ewset E n w).
Proof.
intros k0 E0 E n w Hk [HA HD]. split; [intros m Hm; rewrite ew_ewset_other by lia; apply HA; exact Hm|].
rewrite ed_ewset. exact HD.
Qed.
(* an image atom plus an offset (the .rodata words, `auipc` + `addi`) *)
Lemma pvd_soff_img : forall E n k, img_env VAL A_LIM E -> (A_TEXT <= n < A_LIM)%nat ->
  sv_denot E (SOff n k) = w64 (VAL n + k).
Proof.
intros E n k HE Hn. apply bv_eq. unfold w64. rewrite Z_to_bv_unsigned.
change (bv_unsigned (sv_denot E (SOff n k))) with (U E (SOff n k)). rewrite U_SOff, (HE n Hn).
unfold zcanon, M64, bv_wrap. reflexivity.
Qed.
(* the node's bytes may be written by parse_value's own code (the string arm's type word and str word): rd_pre's
   prhReader_at puts v in a ledger block, an allocator block, or a caller's fake frame (its window case is excluded by
   rd_pre's `v + 56 <= sp \/ sp + e <= v`), each inside pe_FP en; so each byte is awr_byte's block case or YCbqG's
   caller-frame case wr_fp_frame, and none is an image byte *)
Lemma pvd_v_wr : forall en lyc Sc own,
  pv_pre B ARx en ->
  ablocks B lyc Sc = ablocks B (pe_ly en) (pe_S en) ->
  (forall c p, frame_addr lyc c p = frame_addr (pe_ly en) c p) ->
  forall a, pe_v en <= a < pe_v en + 56 ->
    (awr_byte (pe_STK en + pe_e en) (pe_sp en + pe_e en) (pe_FP en) (ablocks B (pe_ly en) (pe_S en))
       (ablocks B lyc Sc) lyc own a \/ wr_fp_frame (pe_FP en) (pe_S en) lyc a) /\ ~ in_img SEGS a.
Proof.
intros en lyc Sc own HPRE Eab EF a Ha.
assert (HFPRE : fpre B ARx (pe_STK en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_regs en) (pe_mem en) (pe_md en)
  (pe_ch en)) by (unfold pv_pre in HPRE; tauto).
assert (HRDP : rd_pre (fx := fx0) B (pe_STK en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_regs en)
  (pe_mem en) (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) (pe_own en) (pe_e en)
  (pe_q en) (pe_text en)
  (pe_len en) (pe_p en) (pe_d en) (pe_tb en) (pe_v en)) by (unfold pv_pre in HPRE; tauto).
pose proof HFPRE as (HAFN & _). pose proof HAFN as (HAR & _).
pose proof HRDP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnode & _ & _ & Hvwin & HLED & _).
pose proof Hnode as (_ & _ & _ & _ & Hvat & _).
assert (HinFP : inFP (pe_FP en) a).
{ exists (pe_v en, pe_v en + 56). split; [unfold pe_FP; right; right; left; reflexivity | cbn [fst snd]; lia]. }
pose proof (@cf_head_nonneg cp) as Hch.
destruct Hvat as [(a0 & k & Hin & H1 & H2) | [(b & m & Hin & Hnl & H1 & H2) | [(cid & p' & Hin & H1 & H2) | (H1 & H2)]]].
- pose proof HLED as (_ & _ & HF & _). rewrite Forall_forall in HF.
  destruct (HF (a0, k) Hin) as (Hk0 & Hab0 & _). cbn [fst snd] in Hk0, Hab0.
  assert (Hreq : a0 - cf_head <= a < a0 - cf_head + req_size (k + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
  split.
  + left. right. left. split; [exact HinFP|]. exists (a0 - cf_head), (k + cf_head).
    split; [rewrite Eab; exact Hab0 | exact Hreq].
  + exact (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ a HAR Hab0 Hreq).
- assert (Hreq : b <= a < b + req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  split.
  + left. right. left. split; [exact HinFP|]. exists b, m. split; [rewrite Eab; exact Hin | exact Hreq].
  + exact (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ a HAR Hin Hreq).
- split.
  + right. split; [exact HinFP|]. exists cid, p'. split; [exact Hin|].
    unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF. lia.
  + exact (frm_img_x SEGS B ARx LAWS _ _ _ _ _ _ cid p' a HAR Hin ltac:(lia)).
- exfalso. destruct Hvwin; lia.
Qed.
(* the node lies apart from parse_value's own fake frame (0, pos), the frame its prologue took after entry: the node is
   in a block or a caller's frame, which the allocator invariant separates from every other live frame *)
Lemma pvd_v_apart : forall en lyc Sc Hpc Wc memc mdc pos,
  pv_pre B ARx en -> ARx lyc Sc Hpc Wc memc mdc ->
  frames Sc = (0, pos) :: frames (pe_S en) -> ablocks B lyc Sc = ablocks B (pe_ly en) (pe_S en) ->
  (forall c p, frame_addr lyc c p = frame_addr (pe_ly en) c p) ->
  forall a, pe_v en <= a < pe_v en + 56 ->
    ~ (frame_addr lyc 0 pos <= a < frame_addr lyc 0 pos + fs_frame_bytes 0).
Proof.
intros en lyc Sc Hpc Wc memc mdc pos HPRE HAR Efr Eab EF a Ha Hfa.
assert (HRDP : rd_pre (fx := fx0) B (pe_STK en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_regs en)
  (pe_mem en) (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) (pe_own en) (pe_e en)
  (pe_q en) (pe_text en)
  (pe_len en) (pe_p en) (pe_d en) (pe_tb en) (pe_v en)) by (unfold pv_pre in HPRE; tauto).
pose proof HRDP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnode & _ & _ & Hvwin & HLED & _).
pose proof Hnode as (_ & _ & _ & _ & Hvat & _).
assert (HinF : In (0, pos) (frames Sc)) by (rewrite Efr; left; reflexivity).
pose proof (@cf_head_nonneg cp) as Hch.
destruct Hvat as [(a0 & k & Hin & H1 & H2) | [(b & m & Hin & Hnl & H1 & H2) | [(cid & p' & Hin & H1 & H2) | (H1 & H2)]]].
- pose proof HLED as (_ & _ & HF & _). rewrite Forall_forall in HF.
  destruct (HF (a0, k) Hin) as (Hk0 & Hab0 & _). cbn [fst snd] in Hk0, Hab0. rewrite <- Eab in Hab0.
  pose proof (sep_block_frame_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ 0 pos HAR Hab0 HinF) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. unfold req_size in Hd.
  destruct (Z.eqb_spec (k + cf_head) 0); lia.
- rewrite <- Eab in Hin.
  pose proof (sep_block_frame_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc _ _ 0 pos HAR Hin HinF) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. unfold req_size in Hd.
  destruct (Z.eqb_spec m 0); lia.
- destruct (in_split _ _ Hin) as (l2 & l3 & Hl).
  pose proof (sep_frames_pos_x SEGS B ARx LAWS lyc Sc Hpc Wc memc mdc (0, pos) (cid, p') [] l2 l3 HAR
    ltac:(rewrite Efr, Hl; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite <- !EF in H1, H2. lia.
- destruct Hvwin; lia.
Qed.
(* a chunk of a symbolic state, and the value it pins (PvB_A.v pva_cv / pva_cv_ok / pva_val, in this file's names) *)
Definition pvd_cv (rs : smem) (j : nat) (off w : Z) : option YP09.chunk :=
  match find_region rs (Some j) off w with Some r => find_chunk (YP09.r_chunks r) off w | None => None end.
Lemma pvd_cv_ok : forall E ss ms j off w c, st_ok SEGS E ss ms -> pvd_cv (ss_mem ss) j off w = Some c ->
  YP09.chunk_ok SEGS E (ms_mem ms) (bv_unsigned (ew E j)) c.
Proof.
intros E ss ms j off w c HS H. unfold pvd_cv in H.
destruct (find_region (ss_mem ss) (Some j) off w) as [r|] eqn:Hr; [|discriminate H].
destruct (find_region_sound _ _ _ _ _ Hr) as (Hin & Hb & _).
destruct (find_chunk_sound _ _ _ _ H) as (Hcin & _).
destruct (st_ok_mem_ok SEGS E ss ms HS) as (_ & Hrs & _).
destruct (proj1 (Forall_forall _ _) Hrs r Hin) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hcin) as Hck. rewrite Hb in Hck. exact Hck.
Qed.
Lemma pvd_val : forall E ss ms j off (w : N) e v b a, st_ok SEGS E ss ms ->
  pvd_cv (ss_mem ss) j off (Z.of_N w) = Some (YP09.mkChunk off (CVal w e)) ->
  bv_unsigned (ew E j) = b -> a = b + off -> U E e = v -> Z.of_N w <= 8 -> 0 <= v < 2 ^ (8 * Z.of_N w) ->
  val_mem SEGS (ms_mem ms) a (N.to_nat w) v.
Proof.
intros E ss ms j off w e v b a HS H Hb Ha HU Hw Hv. subst a.
pose proof (pvd_cv_ok E ss ms j off (Z.of_N w) _ HS H) as Hck. rewrite Hb in Hck.
apply (val_of_chunk_ok SEGS E _ _ off w e v Hck); [|exact Hv | exact Hw].
rewrite <- HU. unfold U. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
End c.
(* closed nat side conditions of the env lemmas (register numbers), without lia over the walk's context *)
Ltac pvd_nat :=
  first [ apply Nat.ltb_lt; reflexivity | apply Nat.leb_le; reflexivity
        | let H := fresh in intro H; discriminate H
        | apply (proj1 (Nat.eqb_neq _ _)); reflexivity ].
(* the write premise of a stretch whose regions have no write window *)
Ltac pvd_awr0 :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr); cbn [ss_mem add_cond add_atom In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    clear - Hr; lia|]);
  destruct Hin.
(* closed small bounds *)
Ltac pvd_closed := split; vm_compute; first [reflexivity | discriminate].
(* a dispatch branch on the byte c: its condition in Z (Hc8 : 0 <= c < 256) *)
Ltac pvd_brc Hc UCg c Hc8 :=
  first [ rewrite (pvd_br_kc _ c) in Hc
            by (first [apply UCg; rewrite ?ew_ewset_other, ?ew_havoc_old by pvd_nat; reflexivity | exact Hc8 | pvd_closed])
        | rewrite (pvd_br_ck _ c) in Hc
            by (first [apply UCg; rewrite ?ew_ewset_other, ?ew_havoc_old by pvd_nat; reflexivity | exact Hc8 | pvd_closed]) ];
  cbn [zbr] in Hc.
(* the walk's no-write stretches: chain the byte equalities and the presence growth along the runs *)
Ltac pvd_eq_chain W0 m0 :=
  repeat match goal with
  | EQ : forall x, mrestrict (w_H W0) ?m1 x = mrestrict (w_H W0) m0 x,
    HFr : frame_of ?Ex ?rs (mrestrict (w_H W0) ?m1) (mrestrict (w_H W0) ?m2) |- _ =>
      lazymatch goal with
      | _ : forall x, mrestrict (w_H W0) m2 x = mrestrict (w_H W0) m0 x |- _ => fail
      | _ => let H := fresh "EQ" in
             assert (H : forall x, mrestrict (w_H W0) m2 x = mrestrict (w_H W0) m0 x)
               by (intros x; rewrite (pvd_nowin Ex rs _ _ ltac:(pvd_awr0) HFr x); apply EQ)
      end
  end.
Ltac pvd_gr_chain W0 m0 :=
  repeat match goal with
  | GR : forall a, apresent (w_H W0) m0 a -> apresent (w_H W0) ?m1 a,
    HG : mem_grows (mrestrict (w_H W0) ?m1) (mrestrict (w_H W0) ?m2) |- _ =>
      lazymatch goal with
      | _ : forall a, apresent (w_H W0) m0 a -> apresent (w_H W0) m2 a |- _ => fail
      | _ => let H := fresh "GR" in
             assert (H : forall a, apresent (w_H W0) m0 a -> apresent (w_H W0) m2 a)
               by (intros a Ha; apply (apresent_grows _ _ _ a HG), GR, Ha)
      end
  end.
(* the value of a register at the end of a run (a cut: st_ok_pi; a call stop: st_ok of the setpc state), with the
   symbolic value kept folded *)
Ltac pvd_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
Ltac pvd_agree HAE :=
  repeat first [ exact HAE | apply pvd_agree_ewset; [pvd_nat|] | apply env_agree_havoc_ge; [pvd_nat|] ].
(* the registers a run keeps (each its own atom at the end), at a cut or a call stop; L is given explicitly (the
   forallb check is vm_computed and must hold no evar) *)
Ltac pvd_kept HS HAE regs0 xtra0 L KR :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    let HA := fresh "HA" in
    assert (HA : env_agree 32 (Ereg regs0 xtra0) E) by ((pvd_agree HAE));
    assert (KR : forall r, In r L -> getr (ms_regs ms) r = getr regs0 r)
      by (intros r Hr; (exact (regs_kept_of_st_ok_pi E ss (restrict H ms) regs0 xtra0 L HS HA
            ltac:(vm_compute; reflexivity) r Hr)));
    clear HA
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    let HA := fresh "HA" in
    assert (HA : env_agree 32 (Ereg regs0 xtra0) E) by ((pvd_agree HAE));
    assert (KR : forall r, In r L -> getr (ms_regs ms) r = getr regs0 r)
      by (intros r Hr; (exact (regs_kept_of_st_ok segs E ss (restrict H ms) regs0 xtra0 L HS HA
            ltac:(vm_compute; reflexivity) r Hr)));
    clear HA
  end.
