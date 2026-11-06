(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: IMAGE B (fs.asan-ubsan) walk of parse_value 0x82fcc, stage lemmas. HEADER: see
   FSW_parse_value_holds.v (the composition into parse_value_spec k, the rule-24 line, the reuse search, the port
   sources, every pc walked and every report site). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/Prog/FSW_parse_value.v, with its module names and numbers changed; 1163 of its 1272 lines of code are new or changed and 1247 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan, image B) twin of lib/A/FSW_put_string.v at
   a working branch ca67007c8c2 (a Theorem Labs lane), and another Theorem Labs lane: same lemma names and statement shapes;
   imports point at lib/B's image files and walk kit (YB1v, YB1w, FSH_Base, FSH_Rt, FSPstat, FSH_Fn_writer,
   FSW_K, FSW_K3, FSW_ret, FSW_frame, FSW_frame3, FSW_rd, FSW_strkit and lib/B's put_string files); the
   image-agnostic FSupoison, FSupoisonU, FSupoisonStack, FSH_YC20, FSH_Gen and FSW_writer_model stay lib/A's.
   Every address, cut, branch, offset and register of put_string's own code is RE-MEASURED on image B
   (A_put_string 0x85fc8, 928 bytes; the neutral excerpt put_string.fuzz_state.asan-ubsan.s), never copied.
   rule 24: proves no function (kind: segment lemma). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSW_put_string.v; 751 of its 823 lines of code are new or changed and 1200 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan, image B) twin of lib/A/ZZpsg2.v at
   a working branch ca67007c8c2 (a Theorem Labs lane), and another Theorem Labs lane: same lemma names and statement shapes;
   imports point at lib/B's image files and walk kit (YB1v, YB1w, FSH_Base, FSH_Rt, FSPstat, FSH_Fn_writer,
   FSW_K, FSW_K3, FSW_ret, FSW_frame, FSW_frame3, FSW_rd, FSW_strkit and lib/B's put_string files); the
   image-agnostic FSupoison, FSupoisonU, FSupoisonStack, FSH_YC20, FSH_Gen and FSW_writer_model stay lib/A's.
   Every address, cut, branch, offset and register of put_string's own code is RE-MEASURED on image B
   (A_put_string 0x85fc8, 928 bytes; the neutral excerpt put_string.fuzz_state.asan-ubsan.s), never copied.
   rule 24: proves no function (kind: segment lemma). *)
(* SEG2 of ZZpsclose.ps_close on image B (image A: lib/A/ZZpsg2.v) - from the opening put's return (PS_OPEN_RET
   0x860dc) through the scan loop (or the empty-string arm) and the run put to its return (PS_END_RET 0x862a0).
   - psg2_call: put #2 itself, from ANY call-site state the two opening arms reach (the journal and ARU at the call,
     a memory that agrees with put #1's return off the seven stack slots [sp1 + 8, sp1 + 64), the call's registers),
     through FSW_put_string.ps_put_call and ZZpsres.psr_resume, to ps_inv at PS_END_RET.
   - psg2: the split on the string: bs = [] by ZZpsjoin.psj_open_empty; bs = c :: l by psj_open_head, ZZpsloop.psl_scan
     and psj_end_put2; both then psg2_call.
   IMAGE B (MEASURED on the excerpt, read by the runs of ZZpsjoin / ZZpsloop): put_string keeps the string s in
   s2 = x18 for the whole function (image A: s10 = x26), so every register / atom 26 of A's text that means s or the
   run start r is 18 here (psg2_call's call-site premise on x18, ps_inv's x18 clause, the atoms the join and the loop
   state). The run put's a2 is s4 - 1 - s2 on image B (0x8627c `addi s4,s4,-1`, 0x86290 `sub a2,s4,s2`: qe - r, the
   same value as A's x24 - x26); a0 = s3 = o, a1 = s2 = r = s. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YCeo.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSupoison FSupoisonU FSH_YC20 FSH_Gen FSW_writer_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_ret FSW_frame FSW_frame3 FSW_put_string ZZpsjoin ZZpsclose ZZpsloop ZZpskeep ZZpsmodel ZZpssep ZZpsres ZZpsg1k ZZpsg2k ZZpsg3k.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require
FSH_Fn_writer FSW_strkit.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterRet.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================= closed arithmetic (lia only here) ================= *)
(* put_string's stack budget covers its own frame above put's (FRAME_put_string: the 192-byte own drop, up to 31 bytes of
   re-align and the 64-byte fake frame's reserve); stated as a margin, not as the two values, so that a change of a
   runtime budget inside STK_put moves both sides alike *)
Lemma psg2_stk : 287 <= STK_put_string - STK_put /\ 0 <= STK_put.
Proof. split; vm_compute; intro H; discriminate H. Qed.

Lemma psg2_sp1 : forall sp0, sp0 mod 16 = 0 ->
  sp0 - 223 <= 32 * ((sp0 - PS_FRAME_OWN) / 32) <= sp0 - 192 /\ 32 * ((sp0 - PS_FRAME_OWN) / 32) mod 32 = 0.
Proof.
intros sp0 H. unfold PS_FRAME_OWN. split; [Z.div_mod_to_equations; lia|].
rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

Lemma psg2_off16 : forall sp1 ot, sp1 mod 32 = 0 -> ot mod 16 = 0 -> (sp1 - ot) mod 16 = 0.
Proof. intros sp1 ot H1 H2. Z.div_mod_to_equations. lia. Qed.

Lemma psg2_win : forall sp0 sp1 ot, sp0 - 223 <= sp1 <= sp0 - 192 -> sp0 <= ot ->
  STK_put - (sp1 - ot) <= STK_put_string + (ot - sp0) /\
  ot - (STK_put_string + (ot - sp0)) <= sp0 + -104 /\
  ot - (STK_put_string + (ot - sp0)) <= ot - (STK_put + (ot - sp1)) /\
  ot - (STK_put_string + (ot - sp0)) <= sp1.
Proof. intros sp0 sp1 ot H1 H2. pose proof psg2_stk. lia. Qed.

Lemma psg2_peak : forall peak p1 p2 live cap c1 c2, c1 <= c2 ->
  peak <= p1 <= Z.max peak (live - cap + c1) ->
  p1 <= p2 <= Z.max p1 (live + c1 - cap - c1 + c2) ->
  peak <= p2 <= Z.max peak (live - cap + c2).
Proof. intros. lia. Qed.

Lemma psg2_live : forall live cap c1 c2, live + c1 - cap + c2 - c1 = live + c2 - cap.
Proof. intros. ring. Qed.

(* the hull of the string's shadow lies in the shadow band, below alloc_ceiling *)
Lemma psg2_hull_lo : forall s n t, 0 <= s -> s + n < 2 ^ 47 ->
  shadow_addr s / 8 * 8 <= t < shadow_addr (s + n) / 8 * 8 + 8 -> 0 <= t < 0x10007fff8000.
Proof. intros s n t H0 H1 Ht. unfold shadow_addr, SHADOW_OFF in Ht. Z.div_mod_to_equations. lia. Qed.

(* the save area of ps_sv_chunks lies in [-104, 0) *)
Lemma psg2_sv_rng : Forall (fun c => -104 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= 0) ps_sv_chunks.
Proof. vm_compute. repeat constructor; discriminate. Qed.

(* ================= the model of the first two puts ================= *)
Lemma psg2_st2 : forall f t c n fl (bs : list Z),
  ps_st f t c n fl [[34]; bs] = WriterApp.put1 (ps_st f t c n fl [[34]]) bs.
Proof. reflexivity. Qed.

Lemma psg2_flds : forall st (b : list Z),
  WriterApp.w_failed (WriterApp.put1 st b) = WriterApp.w_failed (WriterApp.put1 (psm_rs st) b) /\
  WriterApp.w_text (WriterApp.put1 st b) = WriterApp.w_text (WriterApp.put1 (psm_rs st) b) /\
  WriterApp.w_cap (WriterApp.put1 st b) = WriterApp.w_cap (WriterApp.put1 (psm_rs st) b) /\
  WriterApp.w_cnt (WriterApp.put1 st b) = WriterApp.w_cnt (WriterApp.put1 (psm_rs st) b) /\
  WriterApp.w_fail (WriterApp.put1 st b) = WriterApp.w_fail (WriterApp.put1 (psm_rs st) b).
Proof.
intros st b. rewrite (psm_put1_eq st b).
cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail].
repeat split; reflexivity.
Qed.

Lemma psg2_wevk : forall f t c n fl (bs : list Z),
  FSH_Fn_writer.wevk c (ps_st f t c n fl [[34]; bs]) =
  FSH_Fn_writer.wevk c (ps_st f t c n fl [[34]]) +
  FSH_Fn_writer.wevk (WriterApp.w_cap (ps_st f t c n fl [[34]])) (WriterApp.put1 (psm_rs (ps_st f t c n fl [[34]])) bs).
Proof.
intros f t c n fl bs. rewrite psg2_st2. apply psm_wevk_step.
change (ps_st f t c n fl [[34]]) with (WriterApp.put1 (WriterApp.mkW f t c n fl []) [34]).
apply psm_inv_step, psm_inv_init.
Qed.

Lemma psg2_wmax : forall f t c n fl (bs : list Z), plain_bytes bs ->
  Z.of_nat (length t) + Z.of_nat (length (WriterSpec.wstr bs)) + 1 <= FSH_Fn_writer.WMAX ->
  Z.of_nat (length (WriterApp.w_text (ps_st f t c n fl [[34]]))) + Z.of_nat (length bs) + 1 <= FSH_Fn_writer.WMAX.
Proof.
intros f t c n fl bs Hp H.
pose proof (WriterRet.put1_text (WriterApp.mkW f t c n fl []) [34]) as T.
change (ps_st f t c n fl [[34]]) with (WriterApp.put1 (WriterApp.mkW f t c n fl []) [34]).
rewrite (FSW_writer_model.wstr_plain_length bs Hp) in H.
cbn [WriterApp.w_text length] in T. lia.
Qed.

Lemma psg2_caps : forall f t c n fl (bs : list Z), 0 <= c ->
  c <= WriterApp.w_cap (ps_st f t c n fl [[34]]) /\
  WriterApp.w_cap (ps_st f t c n fl [[34]]) <= WriterApp.w_cap (WriterApp.put1 (psm_rs (ps_st f t c n fl [[34]])) bs).
Proof.
intros f t c n fl bs Hc.
pose proof (WriterRet.put1_cap (WriterApp.mkW f t c n fl []) [34] Hc) as C1.
change (ps_st f t c n fl [[34]]) with (WriterApp.put1 (WriterApp.mkW f t c n fl []) [34]).
split; [exact C1|].
refine (WriterRet.put1_cap (psm_rs (WriterApp.put1 (WriterApp.mkW f t c n fl []) [34])) bs _).
cbn [WriterApp.w_cap] in C1. unfold psm_rs. cbn [WriterApp.w_cap]. lia.
Qed.

Lemma psg2_c0 : forall c c1, 0 <= c -> c <= c1 -> c1 = 0 -> c = 0.
Proof. intros. lia. Qed.

(* ================= lists, environments, chunks ================= *)
Lemma psg2_garr8_pre : forall (m : word -> option byte) p (l l' : list Z),
  garr8 tfibsegs m p (l ++ l') -> garr8 tfibsegs m p l.
Proof.
intros m p l l' H j Hj. destruct (H j ltac:(rewrite length_app; lia)) as (A & B0).
rewrite app_nth1 in A, B0 by exact Hj. split; assumption.
Qed.

Lemma psg2_ly : forall n ly ly' cid pos, layout_le n ly ly' ->
  frame_addr ly' cid pos = frame_addr ly cid pos /\ flag_addr ly' cid pos = flag_addr ly cid pos /\
  ly_top ly' = ly_top ly.
Proof.
intros n ly ly' cid pos (_ & _ & _ & _ & _ & HF & _ & _ & Ht & _). unfold frame_addr, flag_addr. rewrite HF.
split; [reflexivity | split; [reflexivity | exact Ht]].
Qed.

Lemma psg2_spZ : forall (regs : bvmap 5 word) v, YK11.getr regs 2%bv = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> spZ regs = v.
Proof. intros regs v H Hv. unfold spZ. rewrite H. apply wz. exact Hv. Qed.
Lemma psg2_s0Z : forall (regs : bvmap 5 word) v, YK11.getr regs 8%bv = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> s0Z regs = v.
Proof. intros regs v H Hv. unfold s0Z. rewrite H. apply wz. exact Hv. Qed.
Lemma psg2_raZ : forall (regs : bvmap 5 word) v, YK11.getr regs 1%bv = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> raZ regs = v.
Proof. intros regs v H Hv. unfold raZ. rewrite H. apply wz. exact Hv. Qed.

Lemma psg2_ew : forall (regs : bvmap 5 word) X (r : bv 5) n v, Z.of_nat n = bv_unsigned r ->
  YK11.getr regs r = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew (Ereg regs X) n) = v.
Proof. intros regs X r n v Hn H Hv. rewrite (ew_Ereg_nat regs X n r Hn), H. apply wz. exact Hv. Qed.

(* the callee-saved registers the walk reads after put #2 (image B: x18 holds s; image A read x26) *)
Lemma psg2_pres : forall regsc regs', aregs_preserved regsc regs' ->
  forall r : bv 5, In (bv_unsigned r) [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24] -> YK11.getr regs' r = YK11.getr regsc r.
Proof.
intros regsc regs' HP r Hr. apply (fsw_pres regsc regs' r HP). unfold acallee_saved.
cbn [In] in Hr. lia.
Qed.

Lemma psg2_dn_xa : forall regs regs' X k,
  sv_denot (Ereg regs X) (SOff (xatom k) 0) = sv_denot (Ereg regs' X) (SOff (xatom k) 0).
Proof. intros regs regs' X k. rewrite !fsw_SOff0, !ps_ew_x. reflexivity. Qed.

Lemma psg2_dn_lit : forall E E' z, sv_denot E (SLit z) = sv_denot E' (SLit z).
Proof. intros E E' z. rewrite !psl_lit_denot. reflexivity. Qed.

(* a chunk list carried to another env (that denotes every value the same) and another memory (that agrees on the
   list's bytes) *)
Lemma psg2_cks_mv : forall E E' (m m' : word -> option byte) b lo hi cs,
  (forall c, In c cs -> exists w v, YP09.c_val c = CVal w v /\ sv_denot E v = sv_denot E' v) ->
  (forall c, In c cs -> lo <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= hi) ->
  (forall a, b + lo <= a < b + hi -> mbyte tfibsegs m' a = mbyte tfibsegs m a) ->
  Forall (YP09.chunk_ok tfibsegs E m b) cs -> Forall (YP09.chunk_ok tfibsegs E' m' b) cs.
Proof.
intros E E' m m' b lo hi cs Hv Hr Hm HF. rewrite Forall_forall in HF |- *. intros c Hc i Hi.
destruct (HF c Hc i Hi) as (bb & H1 & H2). exists bb. split.
- destruct (Hv c Hc) as (w & v & Ec & Ed). rewrite Ec in H1 |- *. cbn [YP09.cbyte] in H1 |- *.
  rewrite <- Ed. exact H1.
- destruct (Hr c Hc) as [R1 R2]. rewrite (Hm (b + YP09.c_off c + i) ltac:(lia)). exact H2.
Qed.

Lemma psg2_hdr_v : forall regs regs' X c, In c ps_hdr_chunks ->
  exists w v, YP09.c_val c = CVal w v /\ sv_denot (Ereg regs X) v = sv_denot (Ereg regs' X) v.
Proof.
intros regs regs' X c Hc. unfold ps_hdr_chunks in Hc.
destruct Hc as [<- | [<- | [<- | [<- | []]]]]; (eexists _, _; split; [reflexivity|]);
  first [apply psg2_dn_lit | apply psg2_dn_xa].
Qed.
Lemma psg2_hdr_r : forall c, In c ps_hdr_chunks -> 0 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= 64.
Proof. intros c Hc. unfold ps_hdr_chunks in Hc. destruct Hc as [<- | [<- | [<- | [<- | []]]]]; cbn; lia. Qed.
Lemma psg2_fsh_v : forall E E' c, In c ps_fsh_chunks ->
  exists w v, YP09.c_val c = CVal w v /\ sv_denot E v = sv_denot E' v.
Proof.
intros E E' c Hc. unfold ps_fsh_chunks in Hc.
repeat (destruct Hc as [<- | Hc]; [eexists _, _; split; [reflexivity | apply psg2_dn_lit]|]). destruct Hc.
Qed.
Lemma psg2_fsh_r : forall c, In c ps_fsh_chunks -> 0 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= 8.
Proof.
intros c Hc. unfold ps_fsh_chunks in Hc. repeat (destruct Hc as [<- | Hc]; [cbn; lia|]). destruct Hc.
Qed.
Lemma psg2_sv_v : forall regs regs' X c, In c ps_sv_chunks ->
  exists w v, YP09.c_val c = CVal w v /\ sv_denot (Ereg regs X) v = sv_denot (Ereg regs' X) v.
Proof.
intros regs regs' X c Hc. unfold ps_sv_chunks in Hc. apply in_map_iff in Hc as (k & <- & _).
eexists _, _. split; [reflexivity | apply psg2_dn_xa].
Qed.
Lemma psg2_sv_r : forall c, In c ps_sv_chunks -> -104 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= 0.
Proof. intros c Hc. exact (proj1 (Forall_forall _ _) psg2_sv_rng c Hc). Qed.
Lemma psg2_s0_v : forall regs regs' X c, YK11.getr regs' 24%bv = YK11.getr regs 24%bv -> In c psj_scs0 ->
  exists w v, YP09.c_val c = CVal w v /\ sv_denot (Ereg regs X) v = sv_denot (Ereg regs' X) v.
Proof.
intros regs regs' X c E24 Hc. unfold psj_scs0 in Hc. destruct Hc as [<- | []].
eexists _, _. split; [reflexivity|].
rewrite !fsw_SOff0, (ew_Ereg_nat regs X 24 24%bv eq_refl), (ew_Ereg_nat regs' X 24 24%bv eq_refl), E24.
reflexivity.
Qed.
Lemma psg2_s0_r : forall c, In c psj_scs0 -> 80 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= 88.
Proof. intros c Hc. unfold psj_scs0 in Hc. destruct Hc as [<- | []]. cbn. lia. Qed.

(* wsrc_kept of the string with its terminating zero gives it for the string alone (put reads only bs) *)
Lemma psg2_wsrc_pre : forall B ly S U (W : world tfibsegs) mem buf s (bs : list Z),
  FSH_Fn_writer.wsrc_kept B tfibsegs ly S U W mem buf s (bs ++ [0]) ->
  FSH_Fn_writer.wsrc_kept B tfibsegs ly S U W mem buf s bs.
Proof.
intros B ly S U W mem buf s bs H. pose proof (pss_len0 bs) as EL.
destruct H as [(E & _) | [(p & k & Hp & Hb & Hs1 & Hs2) | [(p & k & Hp & Hb & Hs1 & Hs2 & Hr) | (l & Hl & Hlen)]]].
- exfalso. exact (app_cons_not_nil bs [] 0 (eq_sym E)).
- right; left. exists p, k. split; [exact Hp|]. split; [exact Hb|]. split; [exact Hs1 | lia].
- right; right; left. exists p, k. split; [exact Hp|]. split; [exact Hb|]. split; [exact Hs1|].
  split; [lia|]. intros r Hr'. destruct (Hr r Hr') as [H1 | H1]; [left; exact H1 | right; lia].
- right; right; right. exists l. split; [exact Hl|]. rewrite length_app in Hlen. cbn [length] in Hlen. lia.
Qed.

(* ================= helpers of the two opening arms ================= *)
Section A0. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Lemma psg2_bv : forall (w : word) v, bv_unsigned w = v -> w = Z_to_bv 64 v.
Proof. intros w v H. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma psg2_reg_at : forall (H : word -> bool) E ss ms (r : bv 5) n,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> YK11.getr (ms_regs ms) r = ew E n.
Proof. intros H E ss ms r n HS Hg. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hg. apply fsw_SOff0. Qed.

Lemma psg2_len : forall s c (l : list Z),
  Z_to_bv 64 (s + 1 + Z.of_nat (length l) - s) = Z_to_bv 64 (Z.of_nat (length (c :: l))).
Proof. intros s c l. f_equal. cbn [length]. lia. Qed.

(* the frame's shadow granule lies in the shadow band *)
Lemma psg2_shF_band : forall F, 0 <= F -> F + 64 <= 2 ^ 47 ->
  SHADOW_OFF <= shadow_addr F /\ shadow_addr F + 8 <= SHADOW_OFF + 17592186044416.
Proof. intros F H1 H2. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

(* a cell of the scan (ZZpsloop.psl_cell) carried to a memory that agrees at its byte and its shadow byte: the text
   of ZZpsloop.v's psl_cell_eq (a Theorem Labs lane, :209-227) with that pointwise premise *)
Lemma psg2_cell_mv : forall (W : world tfibsegs) (m m' : word -> option byte) shF a v,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  m' (Z_to_bv 64 (SHADOW_OFF + a / 8)) = m (Z_to_bv 64 (SHADOW_OFF + a / 8)) ->
  psl_cell W m shF a v -> psl_cell W m' shF a v.
Proof.
intros W m m' shF a v E1 E2 (HRA & HV & HB & HS & HP).
split; [|split; [|exact (conj HB (conj HS HP))]].
- eapply range_addressable_agree; [|exact HRA]. intros x Hx.
  unfold aview, shadow_of_addr. replace x with a by lia. unfold mbyte, mrestrict. rewrite E2. reflexivity.
- intros i Hi. destruct i as [|i]; [|exfalso; exact (psl_nat_lt1 i Hi)].
  pose proof (HV 0%nat Hi) as H0. cbn [Z.of_nat] in H0 |- *. rewrite Z.add_0_r in H0 |- *.
  unfold mbyte, mrestrict in H0 |- *. rewrite E1. exact H0.
Qed.

(* one literal byte read through two chunks of the same value *)
Lemma psg2_byte_eq : forall E E' (m m' : word -> option byte) b off z z',
  YP09.chunk_ok tfibsegs E m b (YP09.mkChunk off (CVal 1 (SLit z))) ->
  YP09.chunk_ok tfibsegs E' m' b (YP09.mkChunk off (CVal 1 (SLit z'))) ->
  byte_of_word (Z_to_bv 64 (zcanon z)) 0 = byte_of_word (Z_to_bv 64 (zcanon z')) 0 ->
  mbyte tfibsegs m' (b + off) = mbyte tfibsegs m (b + off).
Proof.
intros E E' m m' b off z z' H1 H2 Hz.
destruct (H1 0 ltac:(cbn; lia)) as (b1 & C1 & M1). destruct (H2 0 ltac:(cbn; lia)) as (b2 & C2 & M2).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in C1, C2, M1, M2. rewrite psl_lit_denot in C1, C2.
rewrite Z.add_0_r in M1, M2. rewrite M1, M2. injection C1 as <-. injection C2 as <-. rewrite Hz. reflexivity.
Qed.

(* the frame's eight shadow bytes as the loop leaves them (psl_sh_region, +4 = PSL_POIS) and as ps_fsh_chunks states
   them (+4 = 248) are the same bytes *)
Lemma psg2_sh_eq : forall E E' (m m' : word -> option byte) shF,
  Forall (YP09.chunk_ok tfibsegs E m shF) (YP09.r_chunks psl_sh_region) ->
  Forall (YP09.chunk_ok tfibsegs E' m' shF) ps_fsh_chunks ->
  forall a, shF <= a < shF + 8 -> mbyte tfibsegs m a = mbyte tfibsegs m' a.
Proof.
intros E E' m m' shF HA HB a Ha. rewrite Forall_forall in HA, HB.
assert (D : a = shF + 0 \/ a = shF + 1 \/ a = shF + 2 \/ a = shF + 3 \/ a = shF + 4 \/ a = shF + 5 \/
            a = shF + 6 \/ a = shF + 7) by lia.
destruct D as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]].
- apply (psg2_byte_eq E' E m' m shF 0 241 241); [apply HB | apply HA | reflexivity];
    cbn; solve [repeat first [left; reflexivity | right]].
- apply (psg2_byte_eq E' E m' m shF 1 241 241); [apply HB | apply HA | reflexivity];
    cbn; solve [repeat first [left; reflexivity | right]].
- apply (psg2_byte_eq E' E m' m shF 2 241 241); [apply HB | apply HA | reflexivity];
    cbn; solve [repeat first [left; reflexivity | right]].
- apply (psg2_byte_eq E' E m' m shF 3 241 241); [apply HB | apply HA | reflexivity];
    cbn; solve [repeat first [left; reflexivity | right]].
- apply (psg2_byte_eq E' E m' m shF 4 248 (2 ^ 64 - 8)); [apply HB | apply HA | apply bv_eq; vm_compute; reflexivity];
    cbn; solve [repeat first [left; reflexivity | right]].
- apply (psg2_byte_eq E' E m' m shF 5 243 243); [apply HB | apply HA | reflexivity];
    cbn; solve [repeat first [left; reflexivity | right]].
- apply (psg2_byte_eq E' E m' m shF 6 243 243); [apply HB | apply HA | reflexivity];
    cbn; solve [repeat first [left; reflexivity | right]].
- apply (psg2_byte_eq E' E m' m shF 7 243 243); [apply HB | apply HA | reflexivity];
    cbn; solve [repeat first [left; reflexivity | right]].
Qed.

(* the call-site register files of the two arms (MEASURED by ZZpsjoin's runs), at the registers the walk reads
   (image B: x18 = s2 = s, untouched by both arms; image A read x26) *)
Lemma psg2_E0_regs :
  sr_get psj_regsE0 2%bv = SOff 2 0 /\ sr_get psj_regsE0 3%bv = SOff 3 0 /\ sr_get psj_regsE0 4%bv = SOff 4 0 /\
  sr_get psj_regsE0 8%bv = SOff 8 0 /\ sr_get psj_regsE0 9%bv = SOff 9 0 /\ sr_get psj_regsE0 19%bv = SOff 19 0 /\
  sr_get psj_regsE0 21%bv = SOff 24 0 /\ sr_get psj_regsE0 22%bv = SOff 47 0 /\
  sr_get psj_regsE0 23%bv = SOff 32 0 /\ sr_get psj_regsE0 24%bv = SOff 24 0 /\ sr_get psj_regsE0 18%bv = SOff 18 0.
Proof. repeat apply conj; vm_compute; reflexivity. Qed.
Lemma psg2_P2_regs :
  sr_get psj_put2_regs 2%bv = SOff 2 0 /\ sr_get psj_put2_regs 3%bv = SOff 3 0 /\
  sr_get psj_put2_regs 4%bv = SOff 4 0 /\ sr_get psj_put2_regs 8%bv = SOff 8 0 /\
  sr_get psj_put2_regs 9%bv = SOff 9 0 /\ sr_get psj_put2_regs 19%bv = SOff 19 0 /\
  sr_get psj_put2_regs 22%bv = SOff 22 0 /\ sr_get psj_put2_regs 23%bv = SOff 32 0 /\
  sr_get psj_put2_regs 18%bv = SOff 18 0.
Proof. repeat apply conj; vm_compute; reflexivity. Qed.

(* a shadow byte of an address below 2^47 lies in the shadow band *)
Lemma psg2_sh_lo : forall a, 0 <= a < 2 ^ 47 -> 0 <= SHADOW_OFF + a / 8 < 0x10007fff8000.
Proof. intros a H. unfold SHADOW_OFF. Z.div_mod_to_equations. lia. Qed.
End A0.

Section G2. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* put's contract (FSW_put_string's Section hypothesis HPUT) and fs's image facts (approved by a Theorem Labs lane 2026-10-29 as a
   named open hypothesis of the walk: ZZpsg3k.ps_str_keep re-derives cstr_ok of a table string from them) *)
Hypothesis HPUT : FSH_Fn_writer.put_spec B tfibsegs.
Hypothesis HIMG : fs_img_facts tfibsegs B.

(* ================= put #2: from the call site to its return ================= *)
Lemma psg2_call : forall ly S U W regs mem md ch ot o s buf cap failed (text bs : list Z) live peak cnt fail
    pos ly1 S1 U1 W1 regs1 mem1 md1 buf1 regsc memc mdc (Q : world tfibsegs -> config -> Prop),
  ps_pre B ly S U W regs mem md ch ot o s buf cap failed text bs live peak cnt fail ->
  ps_inv B ly S U W regs mem md ot o s bs buf cap failed text live peak cnt fail pos ly
    [[34]] PS_OPEN_RET (ps_ret_ss PS_OPEN_RET (Z.of_nat (length bs)) psj_scs0 [ps_str_region (Z.of_nat (length bs))])
    ly1 S1 U1 W1 regs1 mem1 md1 buf1 ->
  (* the call site *)
  ajournal tfibsegs B (STK_put_string + (ot - spZ regs)) ot (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf cap)
    ly S W (unpoison U mem) md [(0, pos)] ly1 S1 W1 (unpoison U1 memc) mdc
    (FSH_Fn_writer.wevk cap (ps_st failed text cap cnt fail [[34]])) ->
  ARU tfibsegs B ly1 S1 U1 W1 memc mdc ->
  pske_agree W1 W1 mem1 memc
    (fun a => 32 * ((spZ regs - PS_FRAME_OWN) / 32) + 8 <= a < 32 * ((spZ regs - PS_FRAME_OWN) / 32) + 64) ->
  YK11.getr regsc 1%bv = Z_to_bv 64 PS_END_RET -> YK11.getr regsc 10%bv = Z_to_bv 64 o ->
  YK11.getr regsc 11%bv = Z_to_bv 64 s -> YK11.getr regsc 12%bv = Z_to_bv 64 (Z.of_nat (length bs)) ->
  YK11.getr regsc 2%bv = YK11.getr regs1 2%bv -> YK11.getr regsc 8%bv = YK11.getr regs1 8%bv ->
  YK11.getr regsc 9%bv = YK11.getr regs1 9%bv -> YK11.getr regsc 19%bv = YK11.getr regs1 19%bv ->
  YK11.getr regsc 21%bv = YK11.getr regs1 21%bv -> YK11.getr regsc 22%bv = YK11.getr regs1 22%bv ->
  YK11.getr regsc 23%bv = YK11.getr regs1 23%bv -> YK11.getr regsc 24%bv = YK11.getr regs1 24%bv ->
  (* image B: s is in s2 = x18 (image A: s10 = x26) *)
  YK11.getr regsc 18%bv = YK11.getr regs1 18%bv ->
  YK11.getr regsc 3%bv = YK11.getr regs1 3%bv -> YK11.getr regsc 4%bv = YK11.getr regs1 4%bv ->
  (forall ly2 S2 U2 W2 regs2 mem2 md2 buf2,
     ps_inv B ly S U W regs mem md ot o s bs buf cap failed text live peak cnt fail pos ly
       [[34]; bs] PS_END_RET (ps_ret_ss PS_END_RET (Z.of_nat (length bs)) psj_scs0 [])
       ly2 S2 U2 W2 regs2 mem2 md2 buf2 ->
     SRr tfibsegs W2 (mkCfg (mkst regs2 (Z_to_bv 64 PS_END_RET) mem2 (seg_rom tfibsegs)) md2) Q) ->
  SRr tfibsegs W1 (cfg_at tfibsegs A_put regsc memc mdc) Q.
Proof.
intros ly S U W regs mem md ch ot o s buf cap failed text bs live peak cnt fail pos ly1 S1 U1 W1 regs1 mem1 md1 buf1
  regsc memc mdc Q PRE INV1 HJc HARUc HAG C1 C10 C11 C12 C2 C8 C9 C19 C21 C22 C23 C24 C18 C3 C4 KONT.
pose proof PRE as (HPRE & Hheads & Hfr & G10 & G11 & HOUT & HGLOB & HHEAD & Hspo & Hoot & Hot16 & Hottop & Hchain
  & HFP & HPRESENT & Hcstr & Hsrck & Hbok & Hnz & Hplain & Hsep & Hwmax & Hcap & Hlive & Hbp).
pose proof INV1 as (Hin1 & Hfr1 & _ & HJ1 & HARU1 & HS1 & _ & R2 & R8 & R9 & R19 & R21 & R22 & R23 & R24 & R18
  & R3 & R4 & C80 & Chdr & Cfsh & HUS1 & HOUT1 & HBK1 & HBS1 & HKP1 & HCS1 & (peak1 & HPK1a & HPK1b) & HSRC1 & HHD1
  & HHS1 & HRO1 & HPR1).
pose proof asan_consts as (AC1 & _ & AC3 & _ & _).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (fsw_sp B _ ly S U W regs mem md ch (proj1 HPRE)) as (Hal16 & Hceil0 & H470 & _).
pose proof HPRE as ((HPa & _ & _) & HRO0).
pose proof HPa as (_ & Hret0 & Hra40 & Hgp0 & Htp0 & Hstk0 & _ & Hch0 & _).
pose proof Hstk0 as (_ & _ & _ & _ & _ & Hshi0 & _ & _ & Htop0).
pose proof (psk_aru_pre B _ ly S U W regs mem md ch HPRE) as HARU0.
pose proof (proj1 HARUc) as HARc.
pose proof HJ1 as (_ & HL1 & _).
destruct (psg2_ly _ _ _ 0 pos HL1) as (EF1 & EFL1 & Etop1).
destruct (frames_bounds tfibsegs B LAWS ly1 S1 W1 (unpoison U1 memc) mdc 0 pos HARc Hin1) as (HF4 & HFc & HFapp).
destruct (al_frames _ _ LAWS ly1 S1 W1 (unpoison U1 memc) mdc 0 pos HARc Hin1) as (HF32 & _ & HFp & HFsh).
rewrite EF1 in HF4, HFc, HFapp, HF32, HFp, HFsh. rewrite pss_fb0 in HFc, HFapp, HFp. change (64 / 8) with 8 in HFsh.
pose proof (psk_wout_blk B ly1 S1 W1 mem1 o buf1 _ _ _ HOUT1) as (Hb1in & Hb10).
pose proof (psk_wout_blk B ly S W mem o buf cap failed text HOUT) as (Hb0in & _).
pose proof HOUT as (_ & _ & _ & _ & _ & (Hc0 & _) & _).
pose proof HGLOB as (_ & _ & _ & _ & _ & _ & (Hn0 & _) & _).
pose proof Hcstr as (_ & Hs4096 & Hsceil & _).
set (sp1 := 32 * ((spZ regs - PS_FRAME_OWN) / 32)) in *.
set (X := fs_extraT ++ ps_xs regs (flag_addr ly 0 pos) ++ [Z_to_bv 64 (shadow_addr (frame_addr ly 0 pos))]) in *.
set (st1 := ps_st failed text cap cnt fail [[34]]) in *.
destruct (psg2_sp1 (spZ regs) Hal16) as (Hsp1 & Hal1). fold sp1 in Hsp1, Hal1.
pose proof psg2_stk as HSTK.
assert (Hceil : alloc_ceiling + 287 <= spZ regs) by (clear - Hceil0 HSTK; lia).
destruct (psg2_win (spZ regs) sp1 ot Hsp1 ltac:(clear - Hspo Hoot; lia)) as (W1a & W1b & W1c & W1d).
assert (Hsp64 : 0 <= sp1 < 2 ^ 64) by (clear - Hsp1 Hceil AC1 H470; lia).
assert (Hs064 : 0 <= spZ regs < 2 ^ 64) by (clear - Hceil AC1 H470; lia).
assert (Esp : spZ regsc = sp1) by (apply psg2_spZ; [rewrite C2; exact R2 | exact Hsp64]).
assert (Es0 : s0Z regsc = spZ regs) by (apply psg2_s0Z; [rewrite C8; exact R8 | exact Hs064]).
destruct (psg2_caps failed text cap cnt fail bs Hc0) as (Ccap1 & Ccap2). fold st1 in Ccap1, Ccap2.
(* ---- the call-site memory agrees with put #1's return off the seven slots ---- *)
assert (Hslot : forall a, a < sp1 + 8 \/ sp1 + 64 <= a -> ~ (sp1 + 8 <= a < sp1 + 64)) by (intros a Ha; lia).
assert (MB : forall a, 0 <= a < 2 ^ 64 -> a < sp1 + 8 \/ sp1 + 64 <= a ->
               mbyte tfibsegs (mrestrict (w_H W1) memc) a = mbyte tfibsegs (mrestrict (w_H W1) mem1) a)
  by (intros a Ha Hn; exact (pske_mbyte W1 W1 mem1 memc _ a HAG Ha (Hslot a Hn))).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPWc & _).
(* ---- put_string's own saved ra / s0 at s0 - 8 / s0 - 16, from the return state's save area ---- *)
pose proof (fsw_region_nth (Ereg regs1 X) _ _ 0 (YP09.mkRegion (Some 8%nat) (-104) 0 (-104) 0 ps_sv_chunks) HS1
  eq_refl) as R80. cbn [ms_mem restrict] in R80.
assert (E8 : bv_unsigned (ew (Ereg regs1 X) 8) = spZ regs) by exact (psg2_ew regs1 X 8%bv 8 _ eq_refl R8 Hs064).
assert (Ex0 : bv_unsigned (ew (Ereg regs1 X) (xatom 0)) = raZ regs).
{ rewrite ps_ew_x. unfold X. cbn [nth fs_extraT ps_xs app]. reflexivity. }
assert (Ex1 : bv_unsigned (ew (Ereg regs1 X) (xatom 1)) = s0Z regs).
{ rewrite ps_ew_x. unfold X. cbn [nth fs_extraT ps_xs app]. reflexivity. }
destruct (ps_saved_words (Ereg regs1 X) (w_H W1) mem1 (spZ regs) (raZ regs) (s0Z regs) R80 E8 Ex0 Ex1
            (u64_range _) (u64_range _)) as (RD8m & RD16m).
assert (AGm : forall a, spZ regs - 16 <= a < spZ regs ->
                aview tfibsegs (w_H W1) memc a = aview tfibsegs (w_H W1) mem1 a).
{ intros a Ha. unfold aview.
  rewrite (MB a ltac:(clear - Ha Hceil AC1 H470; lia) ltac:(right; clear - Ha Hsp1; lia)). reflexivity. }
assert (RD8 : rdword (aview tfibsegs (w_H W1) (unpoison U1 memc)) (spZ regs - 8) = Some (raZ regs)).
{ apply (ps_rdword_unpoison B ly1 S1 U1 W1 memc mdc _ _ HARUc);
    [rewrite AC3; clear - Hceil AC1; lia | clear - H470; lia|].
  rewrite (rdword_ext (aview tfibsegs (w_H W1) mem1) (aview tfibsegs (w_H W1) memc) (spZ regs - 8));
    [exact RD8m | intros k Hk; apply AGm; clear - Hk; lia]. }
assert (RD16 : rdword (aview tfibsegs (w_H W1) (unpoison U1 memc)) (spZ regs - 16) = Some (s0Z regs)).
{ apply (ps_rdword_unpoison B ly1 S1 U1 W1 memc mdc _ _ HARUc);
    [rewrite AC3; clear - Hceil AC1; lia | clear - H470; lia|].
  rewrite (rdword_ext (aview tfibsegs (w_H W1) mem1) (aview tfibsegs (w_H W1) memc) (spZ regs - 16));
    [exact RD16m | intros k Hk; apply AGm; clear - Hk; lia]. }
(* ---- the call-site reader agrees with the entry's above sp0, off the out-object ---- *)
assert (AGc : forall a, spZ regs <= a < 2 ^ 64 -> ~ (o <= a < o + 32) ->
                aview tfibsegs (w_H W1) (unpoison U1 memc) a = aview tfibsegs (w_H W) (unpoison U mem) a).
{ apply (ps_chain_agree B (STK_put_string + (ot - spZ regs)) ot _ ly S U W mem md [(0, pos)] ly1 S1 U1 W1 memc mdc _
           (spZ regs) o HJc HARU0 HARUc ltac:(clear - HSTK; lia) ltac:(clear - Hceil; lia)).
  intros x Hx Hxo. destruct (HKP1 x Hx Hxo) as (M1 & _).
  rewrite (MB x ltac:(clear - Hx Hoot Hottop Htop0 Hshi0 Hceil AC1; lia) ltac:(right; clear - Hx Hsp1; lia)).
  exact M1. }
(* ======== put's premises at the call ======== *)
assert (P_ro : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W1) memc)).
{ intros a Ha Ho He. pose proof (FSW_rd.fsw_roP_img a Ha) as Hi. pose proof (fs_segs_img a Hi) as Hl.
  unfold aview. rewrite (MB a ltac:(unfold FS_IMG_END in Hl; clear - Hl; lia)
                            ltac:(left; unfold FS_IMG_END in Hl; clear - Hl Hsp1 Hceil AC1; lia)).
  exact (HRO1 a Ha Ho He). }
assert (P_sp : spZ regsc = ot + (sp1 - ot)) by (rewrite Esp; ring).
assert (P_off : (sp1 - ot) mod 16 = 0) by exact (psg2_off16 sp1 ot Hal1 Hot16).
assert (P_neg : sp1 - ot <= 0) by (clear - Hsp1 Hspo Hoot; lia).
assert (P_ret : YK0s.ret_ok (YK11.getr regsc 1%bv)) by (rewrite C1; vm_compute; reflexivity).
assert (P_ra4 : 4096 <= raZ regsc)
  by (rewrite (psg2_raZ regsc PS_END_RET C1 ltac:(unfold PS_END_RET; lia)); unfold PS_END_RET; lia).
assert (P_gp : YK11.getr regsc 3%bv = w64 (as_gp B)) by (rewrite C3, R3; exact Hgp0).
assert (P_tp : YK11.getr regsc 4%bv = w64 (as_tp B)) by (rewrite C4, R4; exact Htp0).
assert (P_chain : achain ly1 (aview tfibsegs (w_H W1) (unpoison U1 memc)) (spZ regsc) (s0Z regsc) (ps_ch1 ly regs ch)).
{ rewrite Esp, Es0.
  apply (ps_chain_call B ly S U W regs mem md ch o ly1 W1 (unpoison U1 memc) sp1 (proj1 HPRE) HFP Etop1);
    [ | exact RD8 | exact RD16 | clear - Hsp1; lia].
  intros a Ha Ho. apply AGc; [clear - Ha Htop0 Hshi0; lia | exact Ho]. }
assert (P_fr : Z.of_nat (length (frames S1)) <= FRL_CRT_CALLEE + 1)
  by (rewrite Hfr1; exact (ps_frames_callee (0, pos) (frames S) Hfr)).
assert (P_out : FSH_Fn_writer.wout_ok B tfibsegs ly1 S1 W1 memc o buf1 (WriterApp.w_cap st1) (WriterApp.w_failed st1)
                  (WriterApp.w_text st1)).
{ apply (pske_wout_ok B ly1 S1 ly1 S1 W1 W1 mem1 memc _ o buf1 _ _ _ HAG (Z.le_refl _)
           ltac:(clear - Hoot Hottop Htop0 Hshi0; lia)); [ | | intros H; exact H | exact HOUT1].
  - intros a Ha. apply Hslot. right. clear - Ha Hspo Hsp1. lia.
  - intros Hc. destruct (al_blocks _ _ LAWS ly1 S1 W1 (unpoison U1 memc) mdc _ _ HARc (Hb1in Hc))
      as (_ & H4 & Hc' & _).
    pose proof HOUT1 as (_ & _ & _ & _ & _ & (Hcap1 & _) & _).
    pose proof (req_size_pos (WriterApp.w_cap st1 + HEAD) ltac:(unfold HEAD; clear - Hcap1; lia)) as (_ & Hrq).
    split; [unfold HEAD in *; clear - H4; lia|]. split; [unfold HEAD in *; clear - Hc' Hrq AC1; lia|].
    intros a Ha. apply Hslot. left. unfold HEAD in *. clear - Ha Hc' Hrq Hsp1 Hceil. lia. }
assert (P_glob : fs_glob tfibsegs W1 memc (live + WriterApp.w_cap st1 - cap) peak1 (WriterApp.w_cnt st1)
                   (WriterApp.w_fail st1)).
{ apply (pske_glob W1 W1 mem1 memc _ _ _ _ _ HAG); [|exact HPK1b].
  intros a Ha. apply Hslot. left. pose proof (pss_pstat_rng a Ha) as [_ H2]. clear - H2 Hsp1 Hceil AC1. lia. }
assert (P_spo : spZ regsc <= o) by (rewrite Esp; clear - Hsp1 Hspo; lia).
assert (P_top : ot <= ly_top ly1) by (rewrite Etop1; exact Hottop).
assert (P_cho : o = spZ regsc + 8 /\ raZ regsc < alloc_ceiling \/
                spZ regsc + 16 <= o /\ exists ra nfp,
                  rdword (aview tfibsegs (w_H W1) (unpoison U1 memc)) (o - 8) = Some ra /\
                  rdword (aview tfibsegs (w_H W1) (unpoison U1 memc)) (o - 16) = Some nfp /\
                  (ra < 4096 \/ nfp < alloc_ceiling)).
{ apply (psk_chain_o (aview tfibsegs (w_H W) (unpoison U mem)) _ regs regsc o Hchain); [ | | | exact RD8].
  - rewrite Esp. clear - Hsp1. lia.
  - intros a Ha. apply AGc; [clear - Ha Hspo Hoot Hottop Htop0 Hshi0 Hceil AC1; lia | clear - Ha; lia].
  - intros a Ha. apply ps_aview_some. apply HPWc. clear - Ha Hoot Hspo HSTK. lia. }
assert (P_pres : forall a, spZ regsc <= a < ot -> apresent (w_H W1) memc a).
{ rewrite Esp. intros a Ha.
  apply (fsw_apresent_unpoison B ly1 S1 U1 W1 memc mdc a HARUc);
    [rewrite AC3; clear - Ha Hsp1 Hceil AC1 Hoot Hottop Htop0 Hshi0; lia|].
  apply HPWc. clear - Ha Hsp1 HSTK. lia. }
assert (HCSc : cstr_ok tfibsegs W1 memc s bs).
{ apply (pske_cstr_ok W1 W1 mem1 memc _ s bs HAG); [ | | exact HCS1].
  - intros a Ha. apply Hslot. left. clear - Ha Hsceil Hsp1 Hceil. lia.
  - intros t Ht. apply Hslot. left.
    destruct (psg2_hull_lo s (Z.of_nat (length bs)) t ltac:(clear - Hs4096; lia) ltac:(clear - Hsceil AC1; lia) Ht)
      as [_ Hh].
    clear - Hh Hsp1 Hceil AC1. lia. }
assert (P_zb : zbytes_at tfibsegs W1 memc s bs) by exact (psg2_garr8_pre _ s bs [0] (proj1 (proj1 HCSc))).
assert (P_src : FSH_Fn_writer.wsrc_kept B tfibsegs ly1 S1 U1 W1 memc buf1 s bs).
{ apply psg2_wsrc_pre.
  apply (pske_wsrc_kept B ly1 S1 U1 ly1 S1 U1 W1 W1 mem1 memc _ buf1 s (bs ++ [0]) HAG (incl_refl _) (incl_refl _));
    [|exact HSRC1].
  intros p k _ Hb _ _.
  destruct (al_blocks _ _ LAWS ly1 S1 W1 (unpoison U1 memc) mdc _ _ HARc Hb) as (_ & H4 & Hc' & _ & _ & _ & Hk).
  pose proof (req_size_pos (k + HEAD) ltac:(clear - Hk; lia)) as (Hr1 & _).
  split; [unfold HEAD in *; clear - H4; lia|]. split; [clear - Hc' Hr1 AC1; lia|].
  intros a Ha. apply Hslot. left. clear - Ha Hc' Hr1 Hsp1 Hceil. lia. }
assert (P_s : 0 <= s /\ s + Z.of_nat (length bs) <= alloc_ceiling) by (clear - Hs4096 Hsceil; lia).
assert (P_sep : s + Z.of_nat (length bs) <= o \/ ot <= s) by (clear - Hsep; lia).
assert (P_wmax : Z.of_nat (length (WriterApp.w_text st1)) + Z.of_nat (length bs) + 1 <= FSH_Fn_writer.WMAX)
  by exact (psg2_wmax failed text cap cnt fail bs Hplain Hwmax).
pose proof HBK1 as (P_capw & Hbb1 & _).
assert (P_capl : WriterApp.w_cap st1 <= live + WriterApp.w_cap st1 - cap) by (clear - Hlive; lia).
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & Hnev1 & _).
pose proof (psm_wbudget_pre2 S S1 failed text cap cnt fail live (live + WriterApp.w_cap st1 - cap) bs st1
  (WriterApp.put1 (psm_rs st1) bs) (WriterApp.put1 (psm_rs (WriterApp.put1 (psm_rs st1) bs)) [34])
  Hplain Hc0 Hn0 eq_refl eq_refl eq_refl Hbp eq_refl Hnev1 Hbb1) as P_bud.
assert (P_s0r : forall regs', aregs_preserved regsc regs' -> YK11.getr regs' 8%bv = Z_to_bv 64 (spZ regs)).
{ intros r' HP. rewrite (psg2_pres regsc r' HP 8%bv ltac:(vm_compute; lia)), C8. exact R8. }
assert (P_csok : forall regs', Forall (YP09.chunk_ok tfibsegs (Ereg regs' X) (mrestrict (w_H W1) memc) (spZ regs))
                                 ps_sv_chunks).
{ intros r'. destruct R80 as (_ & _ & _ & C8s).
  cbn [YP09.r_base YP09.r_chunks base_val] in C8s. rewrite E8 in C8s.
  apply (psg2_cks_mv (Ereg regs1 X) (Ereg r' X) (mrestrict (w_H W1) mem1) (mrestrict (w_H W1) memc) (spZ regs)
           (-104) 0 ps_sv_chunks (psg2_sv_v regs1 r' X) psg2_sv_r); [|exact C8s].
  intros a Ha. apply MB; [clear - Ha Hceil AC1 H470; lia | right; clear - Ha Hsp1; lia]. }
assert (P_fpr : forall a, inFP (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf1 (WriterApp.w_cap st1)) a ->
   (inFP (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf cap) a /\
      exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n) \/
   in_tmp_block (ablocks B ly S) (ablocks B ly1 S1) a \/
   (inFP (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf cap) a /\ in_img tfibsegs a) \/
   in_frames ly1 [(0, pos)] a)
  by (intros a Ha; exact (psk_fp_rel B ly S ly1 S1 W1 (unpoison U1 memc) mdc buf cap buf1 (WriterApp.w_cap st1)
                            [(0, pos)] a HARc HBS1 Hb1in Ha)).
assert (P_froff : forall a, (frame_addr ly1 0 pos <= a < frame_addr ly1 0 pos + fs_frame_bytes 0 \/
                             shadow_addr (frame_addr ly1 0 pos) <= a
                               < shadow_addr (frame_addr ly1 0 pos) + fs_frame_bytes 0 / 8) ->
                    ~ inFP (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf1 (WriterApp.w_cap st1)) a)
  by (intros a Ha; exact (pss_fr_off_fp B ly1 S1 W1 (unpoison U1 memc) mdc 0 pos buf1 (WriterApp.w_cap st1) a memc o
                            (WriterApp.w_failed st1) (WriterApp.w_text st1) HARc Hin1 (Z.le_refl 0) P_out Ha)).
(* ======== the call ======== *)
refine (ps_put_call B HPUT (STK_put_string + (ot - spZ regs)) ot (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf cap)
  [(0, pos)] ly S U U1 W mem md W1 ly1 S1 memc mdc (FSH_Fn_writer.wevk cap st1) regsc (sp1 - ot) (ps_ch1 ly regs ch)
  pos PS_END_RET o s (Z.of_nat (length bs)) buf1 (WriterApp.w_cap st1) (WriterApp.w_failed st1) (WriterApp.w_text st1)
  bs (live + WriterApp.w_cap st1 - cap) peak1 (WriterApp.w_cnt st1) (WriterApp.w_fail st1) ot (spZ regs) (-104) 0
  ps_sv_chunks X Q
  HJc HARUc P_ro P_sp P_off P_neg W1a P_ret P_ra4 P_gp P_tp P_chain HHS1 P_fr C10 C11 C12 P_out P_glob HHD1
  P_spo Hoot Hot16 P_top P_cho P_pres P_zb P_src eq_refl Hbok P_s P_sep P_wmax P_capw P_capl P_bud C1 P_s0r Hal16
  ltac:(clear - Hspo Hoot; lia) W1b ltac:(clear; lia) (Z.le_refl 0) ltac:(rewrite Esp; exact W1c) (Z.le_refl ot)
  ltac:(rewrite Esp; clear - Hsp1 Hspo Hoot; lia) ltac:(vm_compute; reflexivity) psg2_sv_rng P_csok
  ltac:(rewrite Esp; clear - Hsp1; lia) ltac:(clear - Hspo Hoot; lia) ltac:(left; clear - Hspo; lia)
  P_fpr Hin1 P_froff _).
(* ======== put's return ======== *)
intros st' buf' U' ly' S' W' regs' mem' md' Est' Hsw HJ' HARU' HP HOUT' HBK' HBS' HKP' HPK' HSRC' HFR' HS'.
subst st'.
set (s2 := WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed st1) (WriterApp.w_text st1) (WriterApp.w_cap st1)
                             (WriterApp.w_cnt st1) (WriterApp.w_fail st1) []) bs) in *.
set (st2 := ps_st failed text cap cnt fail [[34]; bs]).
assert (Ef2 : WriterApp.w_failed st2 = WriterApp.w_failed s2) by exact (proj1 (psg2_flds st1 bs)).
assert (Et2 : WriterApp.w_text st2 = WriterApp.w_text s2) by exact (proj1 (proj2 (psg2_flds st1 bs))).
assert (Ec2 : WriterApp.w_cap st2 = WriterApp.w_cap s2) by exact (proj1 (proj2 (proj2 (psg2_flds st1 bs)))).
assert (En2 : WriterApp.w_cnt st2 = WriterApp.w_cnt s2)
  by exact (proj1 (proj2 (proj2 (proj2 (psg2_flds st1 bs))))).
assert (El2 : WriterApp.w_fail st2 = WriterApp.w_fail s2)
  by exact (proj2 (proj2 (proj2 (proj2 (psg2_flds st1 bs))))).
(* ---- the registers the rest of the walk reads ---- *)
assert (QP : forall r : bv 5, In (bv_unsigned r) [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24] ->
               YK11.getr regs' r = YK11.getr regsc r) by exact (psg2_pres regsc regs' HP).
assert (Q2 : YK11.getr regs' 2%bv = Z_to_bv 64 sp1) by (rewrite (QP 2%bv ltac:(vm_compute; lia)), C2; exact R2).
assert (Q8 : YK11.getr regs' 8%bv = Z_to_bv 64 (spZ regs)) by (rewrite (QP 8%bv ltac:(vm_compute; lia)), C8; exact R8).
assert (Q9 : YK11.getr regs' 9%bv = Z_to_bv 64 sp1) by (rewrite (QP 9%bv ltac:(vm_compute; lia)), C9; exact R9).
assert (Q19 : YK11.getr regs' 19%bv = Z_to_bv 64 o) by (rewrite (QP 19%bv ltac:(vm_compute; lia)), C19; exact R19).
assert (Q21 : YK11.getr regs' 21%bv = Z_to_bv 64 (frame_addr ly 0 pos))
  by (rewrite (QP 21%bv ltac:(vm_compute; lia)), C21; exact R21).
assert (Q22 : YK11.getr regs' 22%bv = Z_to_bv 64 (shadow_addr (frame_addr ly 0 pos)))
  by (rewrite (QP 22%bv ltac:(vm_compute; lia)), C22; exact R22).
assert (Q23 : YK11.getr regs' 23%bv = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (QP 23%bv ltac:(vm_compute; lia)), C23; exact R23).
assert (Q24 : YK11.getr regs' 24%bv = Z_to_bv 64 (frame_addr ly 0 pos))
  by (rewrite (QP 24%bv ltac:(vm_compute; lia)), C24; exact R24).
assert (Q18 : YK11.getr regs' 18%bv = Z_to_bv 64 s) by (rewrite (QP 18%bv ltac:(vm_compute; lia)), C18; exact R18).
assert (Q3 : YK11.getr regs' 3%bv = YK11.getr regs 3%bv) by (rewrite (QP 3%bv ltac:(vm_compute; lia)), C3; exact R3).
assert (Q4 : YK11.getr regs' 4%bv = YK11.getr regs 4%bv) by (rewrite (QP 4%bv ltac:(vm_compute; lia)), C4; exact R4).
(* ---- the layout and the frame list ---- *)
pose proof HJ' as (_ & HL' & _ & _ & _ & HfrS' & _).
destruct (psg2_ly _ _ _ 0 pos HL') as (EF' & EFL' & Etop').
assert (Hin' : In (0, pos) (frames S')) by (rewrite HfrS'; left; reflexivity).
(* ---- the frame's three chunk sets at the return ---- *)
rewrite EF1, pss_fb0 in HFR'. change (64 / 8) with 8 in HFR'.
assert (Hfrm : forall a, frame_addr ly 0 pos <= a < frame_addr ly 0 pos + 64 ->
                 mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H W1) mem1) a).
{ intros a Ha. rewrite (HFR' a (or_introl Ha)).
  apply MB; [clear - Ha HF4 HFc AC1; lia | left; clear - Ha HFc Hsp1 Hceil; lia]. }
assert (Hshm : forall a, shadow_addr (frame_addr ly 0 pos) <= a < shadow_addr (frame_addr ly 0 pos) + 8 ->
                 mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H W1) mem1) a).
{ intros a Ha. rewrite (HFR' a (or_intror Ha)).
  pose proof (psr_sh_bd (frame_addr ly 0 pos) HF4 HFc) as Shb.
  apply MB; [clear - Ha Shb AC1; lia | left; clear - Ha Shb Hsp1 Hceil; lia]. }
assert (Hslm : forall a, sp1 + 80 <= a < sp1 + 88 ->
                 mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H W1) mem1) a).
{ intros a Ha.
  destruct (HKP' a ltac:(rewrite Esp; clear - Ha Hsp1 Hspo Hoot; lia) ltac:(clear - Ha Hsp1 Hspo; lia)) as (M2 & _).
  rewrite M2. apply MB; [clear - Ha Hsp1 Hceil AC1 H470; lia | right; clear - Ha; lia]. }
assert (E24' : ew (Ereg regs' X) 24 = ew (Ereg regs1 X) 24)
  by (rewrite (ew_Ereg_nat regs' X 24 24%bv eq_refl), (ew_Ereg_nat regs1 X 24 24%bv eq_refl), Q24, R24; reflexivity).
assert (Ex13 : ew (Ereg regs' X) (xatom 13) = ew (Ereg regs1 X) (xatom 13)) by (rewrite !ps_ew_x; reflexivity).
pose proof (ps_slot_move (Ereg regs1 X) (Ereg regs' X) _ _ sp1 E24' Hslm C80) as H80'.
pose proof (ps_hdr_move (Ereg regs1 X) (Ereg regs' X) _ _ (frame_addr ly 0 pos) Ex13 Hfrm Chdr) as Hhdr'.
pose proof (ps_fsh_move (Ereg regs1 X) (Ereg regs' X) _ _ (shadow_addr (frame_addr ly 0 pos)) Hshm Cfsh) as Hfsh'.
(* ---- the return state ---- *)
pose proof (psr_resume B (STK_put_string + (ot - spZ regs)) ot (spZ regs) _ ly S W (unpoison U mem) md [(0, pos)]
  ly' S' U' W' mem' md' _ regs' regs PS_END_RET (Z.of_nat (length bs)) pos (frame_addr ly 0 pos) (flag_addr ly 0 pos)
  sp1 s psj_scs0 [] HS' HJ' HARU' Hin' (eq_sym EF') (eq_sym EFL') Q8 Q9 Q21 Q22 Q23 Q24 Q18 W1d
  ltac:(clear - Hsp1; lia) ltac:(clear - Hspo Hoot; lia) Hal1 (Zle_0_nat _)
  ltac:(clear - Hs4096 Hsceil AC1; lia) ltac:(vm_compute; reflexivity) ltac:(constructor; [exact H80' | constructor])
  Hhdr' Hfsh' eq_refl ltac:(constructor) ltac:(apply Forall_forall; intros r0 _; exact I) I) as HSret.
(* ---- the spec's relations, composed from the entry ---- *)
assert (Hc10 : WriterApp.w_cap st1 = 0 -> cap = 0) by exact (psg2_c0 cap _ Hc0 Ccap1).
pose proof (psm_uswap2_ar tfibsegs B ly1 S1 U1 W1 memc mdc U U' buf buf1 buf' cap (WriterApp.w_cap st1)
  HARUc Hb10 Hc10 HUS1 Hsw) as I22.
pose proof (psm_bswap2_ar tfibsegs B ly1 S1 W1 (unpoison U1 memc) mdc (ablocks B ly S) (ablocks B ly' S') buf buf1 buf'
  cap (WriterApp.w_cap st1) (WriterApp.w_cap s2) HARc Hb10 HBS1 HBS') as HBS2.
destruct (ps_heads_put B ly1 S1 U1 W1 memc mdc ly' S' U' W' mem' md' o buf1 buf' (WriterApp.w_cap st1)
  (WriterApp.w_cap s2) (WriterApp.w_failed s2) (WriterApp.w_text s2) HARUc HHS1 Hb10 HHD1 HARU' HOUT' HBS' Hsw)
  as (I31 & I30').
pose proof (psk_arodata_ret B _ ot ly S U W mem md [(0, pos)] ly' S' U' W' mem' md' _ buf cap HJ' HARU0 HARU' Hb0in
  HRO0) as I32.
destruct (ps_str_keep B HIMG _ ot ly S U W mem md [(0, pos)] ly' S' U' W' mem' md' _ buf cap buf' (WriterApp.w_cap s2)
  s bs HARU0 HRO0 HJ' HARU' I31 I32 HBS2 I22 Hb0in Hcstr Hsrck) as (I27 & I29).
assert (I4 : ajournal tfibsegs B (STK_put_string + (ot - spZ regs)) ot (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf cap)
               ly S W (unpoison U mem) md [(0, pos)] ly' S' W' (unpoison U' mem') md' (FSH_Fn_writer.wevk cap st2))
  by (unfold st2; rewrite psg2_wevk; exact HJ').
assert (I23 : FSH_Fn_writer.wout_ok B tfibsegs ly' S' W' mem' o buf' (WriterApp.w_cap st2) (WriterApp.w_failed st2)
                (WriterApp.w_text st2)) by (rewrite Ec2, Ef2, Et2; exact HOUT').
assert (I24 : FSH_Fn_writer.wbudget_kept S S' failed cap cnt (WriterApp.w_failed st2) (WriterApp.w_cap st2)
                (WriterApp.w_cnt st2)).
{ rewrite Ef2, Ec2, En2. exact (psm_wbudget_kept2 S S1 S1 S' failed cap cnt _ _ _ _ _ _ HBK1 (Z.le_refl _) HBK'). }
assert (I25 : FSH_Fn_writer.bswap (ablocks B ly S) (ablocks B ly' S') buf buf' cap (WriterApp.w_cap st2))
  by (rewrite Ec2; exact HBS2).
assert (I26 : wkeep tfibsegs W W' mem mem' (spZ regs) ot o 32).
{ intros a Ha Hno. destruct (HKP1 a Ha Hno) as (M1 & Wr1).
  destruct (HKP' a ltac:(rewrite Esp; clear - Ha Hsp1; lia) Hno) as (M2 & Wr2).
  assert (Ha64 : 0 <= a < 2 ^ 64) by (clear - Ha Hoot Hottop Htop0 Hshi0 Hceil AC1; lia).
  assert (Hns : a < sp1 + 8 \/ sp1 + 64 <= a) by (right; clear - Ha Hsp1; lia).
  split; [rewrite M2, (MB a Ha64 Hns); exact M1|].
  exact (iff_trans Wr1 (iff_trans (pske_writable W1 W1 mem1 memc _ a HAG Ha64 (Hslot a Hns)
                                     (or_introl (HPR1 a ltac:(clear - Ha Hsp1; lia)))) Wr2)). }
assert (I28 : exists peak', peak <= peak' <= Z.max peak (live - cap + WriterApp.w_cap st2) /\
                fs_glob tfibsegs W' mem' (live + WriterApp.w_cap st2 - cap) peak' (WriterApp.w_cnt st2)
                  (WriterApp.w_fail st2)).
{ rewrite Ec2, En2, El2. destruct HPK' as (p2 & Hp2a & Hp2b). exists p2. split.
  - exact (psg2_peak peak peak1 p2 live cap (WriterApp.w_cap st1) (WriterApp.w_cap s2) Ccap2 HPK1a Hp2a).
  - rewrite <- (psg2_live live cap (WriterApp.w_cap st1) (WriterApp.w_cap s2)). exact Hp2b. }
assert (I30 : WriterApp.w_cap st2 <> 0 -> In (buf' - HEAD, HEAD) U') by (rewrite Ec2; exact I30').
assert (I33 : forall a, sp1 <= a < ot -> apresent (w_H W') mem' a).
{ pose proof HJ' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPW' & _).
  intros a Ha. apply (fsw_apresent_unpoison B ly' S' U' W' mem' md' a HARU');
    [rewrite AC3; clear - Ha Hsp1 Hceil AC1 Hoot Hottop Htop0 Hshi0; lia|].
  apply HPW'. clear - Ha Hsp1 HSTK. lia. }
apply (KONT ly' S' U' W' regs' mem' md' buf').
exact (conj Hin' (conj HfrS' (conj eq_refl (conj I4 (conj HARU' (conj HSret (conj eq_refl (conj Q2 (conj Q8 (conj Q9
  (conj Q19 (conj Q21 (conj Q22 (conj Q23 (conj Q24 (conj Q18 (conj Q3 (conj Q4 (conj H80' (conj Hhdr' (conj Hfsh'
  (conj I22 (conj I23 (conj I24 (conj I25 (conj I26 (conj I27 (conj I28 (conj I29 (conj I30 (conj I31 (conj I32
  I33)))))))))))))))))))))))))))))))).
Qed.

(* ================= SEG2 of ZZpsclose.ps_close ================= *)
Lemma psg2 : forall ly S U W regs mem md ch ot o s buf cap failed (text bs : list Z) live peak cnt fail
     pos lyc ly1 S1 U1 W1 regs1 mem1 md1 buf1 (Q : world tfibsegs -> config -> Prop),
   ps_pre B ly S U W regs mem md ch ot o s buf cap failed text bs live peak cnt fail ->
   ps_inv B ly S U W regs mem md ot o s bs buf cap failed text live peak cnt fail pos lyc
     [[34]] PS_OPEN_RET (ps_ret_ss PS_OPEN_RET (Z.of_nat (length bs)) psj_scs0 [ps_str_region (Z.of_nat (length bs))])
     ly1 S1 U1 W1 regs1 mem1 md1 buf1 ->
   (forall ly2 S2 U2 W2 regs2 mem2 md2 buf2,
      ps_inv B ly S U W regs mem md ot o s bs buf cap failed text live peak cnt fail pos lyc
        [[34]; bs] PS_END_RET (ps_ret_ss PS_END_RET (Z.of_nat (length bs)) psj_scs0 [])
        ly2 S2 U2 W2 regs2 mem2 md2 buf2 ->
      SRr tfibsegs W2 (mkCfg (mkst regs2 (Z_to_bv 64 PS_END_RET) mem2 (seg_rom tfibsegs)) md2) Q) ->
   SRr tfibsegs W1 (mkCfg (mkst regs1 (Z_to_bv 64 PS_OPEN_RET) mem1 (seg_rom tfibsegs)) md1) Q.
Proof.
intros ly S U W regs mem md ch ot o s buf cap failed text bs live peak cnt fail pos lyc ly1 S1 U1 W1 regs1 mem1 md1
  buf1 Q PRE INV1 KONT.
pose proof INV1 as (_ & _ & Hlyc & _). subst lyc.
pose proof PRE as (HPRE & _ & _ & _ & _ & _ & _ & _ & Hspo & Hoot & _ & Hottop & _ & _ & _ & Hcstr & Hsrck & Hbok
  & _ & Hplain & _).
pose proof INV1 as (Hin1 & _ & _ & HJ1 & HARU1 & HS1 & _ & R2 & R8 & R9 & R19 & R21 & R22 & R23 & R24 & R18
  & R3 & R4 & _ & _ & Cfsh & _ & _ & _ & HBS1 & _ & HCS1 & _).
pose proof asan_consts as (AC1 & _ & AC3 & _ & _).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (fsw_sp B _ ly S U W regs mem md ch (proj1 HPRE)) as (Hal16 & Hceil0 & H470 & _).
pose proof HPRE as ((HPa & _ & _) & _).
pose proof HPa as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & _ & _ & _ & Hshi0 & _ & _ & Htop0).
pose proof HJ1 as (_ & HL1 & _).
destruct (psg2_ly _ _ _ 0 pos HL1) as (EF1 & _ & _).
pose proof (proj1 HARU1) as HAR1.
destruct (frames_bounds tfibsegs B LAWS ly1 S1 W1 (unpoison U1 mem1) md1 0 pos HAR1 Hin1) as (HF4 & HFc & _).
rewrite EF1 in HF4, HFc. rewrite pss_fb0 in HFc.
pose proof HCS1 as ((Hg1 & _) & Hs4096 & Hsceil & _ & _ & Hra1 & _).
set (sp1 := 32 * ((spZ regs - PS_FRAME_OWN) / 32)) in *.
set (X := fs_extraT ++ ps_xs regs (flag_addr ly 0 pos) ++ [Z_to_bv 64 (shadow_addr (frame_addr ly 0 pos))]) in *.
destruct (psg2_sp1 (spZ regs) Hal16) as (Hsp1 & Hal1). fold sp1 in Hsp1, Hal1.
pose proof psg2_stk as HSTK.
assert (Hceil : alloc_ceiling + 287 <= spZ regs) by (clear - Hceil0 HSTK; lia).
destruct (psg2_win (spZ regs) sp1 ot Hsp1 ltac:(clear - Hspo Hoot; lia)) as (_ & _ & _ & W1d).
pose proof (psg2_shF_band (frame_addr ly 0 pos) ltac:(clear - HF4; lia) ltac:(clear - HFc AC1; lia)) as SHB.
(* ---- the atoms of the return state's env (image B: s on atom 18 = s2) ---- *)
assert (E18 : bv_unsigned (ew (Ereg regs1 X) 18) = s)
  by exact (psg2_ew regs1 X 18%bv 18 s eq_refl R18 ltac:(clear - Hs4096 Hsceil AC1; lia)).
assert (E19 : bv_unsigned (ew (Ereg regs1 X) 19) = o)
  by exact (psg2_ew regs1 X 19%bv 19 o eq_refl R19 ltac:(clear - Hspo Hoot Hottop Htop0 Hshi0 Hceil AC1; lia)).
assert (E24 : bv_unsigned (ew (Ereg regs1 X) 24) = frame_addr ly 0 pos)
  by exact (psg2_ew regs1 X 24%bv 24 _ eq_refl R24 ltac:(clear - HF4 HFc AC1; lia)).
assert (E9 : bv_unsigned (ew (Ereg regs1 X) 9) = sp1)
  by exact (psg2_ew regs1 X 9%bv 9 sp1 eq_refl R9 ltac:(clear - Hsp1 Hceil AC1 H470; lia)).
assert (EW47 : ew (Ereg regs1 X) 47 = Z_to_bv 64 (shadow_addr (frame_addr ly 0 pos)))
  by (unfold X; change 47%nat with (32 + 15)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E47 : bv_unsigned (ew (Ereg regs1 X) 47) = shadow_addr (frame_addr ly 0 pos))
  by (rewrite EW47; apply wz; clear - SHB; unfold SHADOW_OFF in *; lia).
assert (EW32 : ew (Ereg regs1 X) 32 = Z_to_bv 64 SHADOW_OFF)
  by (unfold X; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
(* ---- the string: off the frame, the frame's shadow and the shadow band ---- *)
assert (Hkeep : forall p n, In (p, n) (ablocks B ly S) -> p <> buf - HEAD -> In (p, n) (ablocks B ly1 S1))
  by (intros p n Hin Hne; exact (pss_bswap_keep _ _ _ _ _ _ p n HBS1 Hin Hne)).
assert (SEP : forall x, s <= x < s + Z.of_nat (length bs) + 1 ->
    ~ (frame_addr ly 0 pos <= x < frame_addr ly 0 pos + 64) /\
    ~ (shadow_addr (frame_addr ly 0 pos) <= shadow_addr x < shadow_addr (frame_addr ly 0 pos) + 8) /\
    ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)).
{ intros x Hx. rewrite <- EF1.
  exact (pss_str_off_fr B ly S U W mem buf s bs ly1 S1 W1 (unpoison U1 mem1) md1 pos x Hcstr Hsrck HAR1 Hin1 Hkeep Hx). }
assert (Hsc1 : s + 1 <= alloc_ceiling) by (clear - Hsceil; lia).
assert (HRA0 : range_addressable (aview tfibsegs (w_H W1) mem1) SHADOW_OFF s 1)
  by (intros x Hx; apply Hra1; clear - Hx; lia).
pose proof (Hg1 0%nat ltac:(rewrite length_app; cbn [length]; lia)) as (HV0 & _).
cbn [Z.of_nat] in HV0. rewrite Z.add_0_r in HV0.
assert (HAPP : ~ (SHADOW_OFF <= s < SHADOW_OFF + 17592186044416))
  by exact (proj2 (proj2 (SEP s ltac:(clear; lia)))).
destruct bs as [|c l].
- (* ======== the empty string: the byte at s is the terminating zero ======== *)
  cbn [app nth] in HV0.
  apply (psj_open_empty B _ s o (Ereg regs1 X) (mkst regs1 (Z_to_bv 64 PS_OPEN_RET) mem1 (seg_rom tfibsegs)) _ ot _
           ly S W (unpoison U mem) md [(0, pos)] ly1 S1 U1 W1 md1 _ Q HS1 HJ1 HARU1 (Z.le_refl 0) E18 E19 Hsc1 HAPP
           HRA0 HV0).
  intros ms' mat' HSc HJc HARUc MEQ C1 C10 C11 C12.
  destruct psg2_E0_regs as (G2 & G3 & G4 & G8 & G9 & G19 & G21 & G22 & G23 & G24 & G18).
  assert (C2 : YK11.getr (ms_regs ms') 2%bv = YK11.getr regs1 2%bv)
    by (rewrite (psg2_reg_at _ _ _ _ 2%bv 2 HSc G2); exact (ew_Ereg_nat regs1 X 2 2%bv eq_refl)).
  assert (C3 : YK11.getr (ms_regs ms') 3%bv = YK11.getr regs1 3%bv)
    by (rewrite (psg2_reg_at _ _ _ _ 3%bv 3 HSc G3); exact (ew_Ereg_nat regs1 X 3 3%bv eq_refl)).
  assert (C4 : YK11.getr (ms_regs ms') 4%bv = YK11.getr regs1 4%bv)
    by (rewrite (psg2_reg_at _ _ _ _ 4%bv 4 HSc G4); exact (ew_Ereg_nat regs1 X 4 4%bv eq_refl)).
  assert (C8 : YK11.getr (ms_regs ms') 8%bv = YK11.getr regs1 8%bv)
    by (rewrite (psg2_reg_at _ _ _ _ 8%bv 8 HSc G8); exact (ew_Ereg_nat regs1 X 8 8%bv eq_refl)).
  assert (C9 : YK11.getr (ms_regs ms') 9%bv = YK11.getr regs1 9%bv)
    by (rewrite (psg2_reg_at _ _ _ _ 9%bv 9 HSc G9); exact (ew_Ereg_nat regs1 X 9 9%bv eq_refl)).
  assert (C19 : YK11.getr (ms_regs ms') 19%bv = YK11.getr regs1 19%bv)
    by (rewrite (psg2_reg_at _ _ _ _ 19%bv 19 HSc G19); exact (ew_Ereg_nat regs1 X 19 19%bv eq_refl)).
  assert (C24 : YK11.getr (ms_regs ms') 24%bv = YK11.getr regs1 24%bv)
    by (rewrite (psg2_reg_at _ _ _ _ 24%bv 24 HSc G24); exact (ew_Ereg_nat regs1 X 24 24%bv eq_refl)).
  assert (C18 : YK11.getr (ms_regs ms') 18%bv = YK11.getr regs1 18%bv)
    by (rewrite (psg2_reg_at _ _ _ _ 18%bv 18 HSc G18); exact (ew_Ereg_nat regs1 X 18 18%bv eq_refl)).
  assert (C21 : YK11.getr (ms_regs ms') 21%bv = YK11.getr regs1 21%bv)
    by (rewrite (psg2_reg_at _ _ _ _ 21%bv 24 HSc G21), (ew_Ereg_nat regs1 X 24 24%bv eq_refl), R24, R21;
        reflexivity).
  assert (C22 : YK11.getr (ms_regs ms') 22%bv = YK11.getr regs1 22%bv)
    by (rewrite (psg2_reg_at _ _ _ _ 22%bv 47 HSc G22), EW47, R22; reflexivity).
  assert (C23 : YK11.getr (ms_regs ms') 23%bv = YK11.getr regs1 23%bv)
    by (rewrite (psg2_reg_at _ _ _ _ 23%bv 32 HSc G23), EW32, R23; reflexivity).
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W1) _ _ ms' HSc eq_refl) at 1.
  exact (psg2_call ly S U W regs mem md ch ot o s buf cap failed text [] live peak cnt fail pos ly1 S1 U1 W1 regs1 mem1
    md1 buf1 (ms_regs ms') (ms_mem ms') _ Q PRE INV1 HJc HARUc (ps_agree_pt W1 mem1 (ms_mem ms') _ MEQ)
    C1 C10 C11 C12 C2 C8 C9 C19 C21 C22 C23 C24 C18 C3 C4 KONT).
- (* ======== a non-empty plain string: s[0] seated, the scan loop, the run of bytes ======== *)
  cbn [app nth] in HV0.
  pose proof (Forall_inv Hplain) as HPc. pose proof (Forall_inv Hbok) as HBc.
  destruct (psl_byte_rng c HPc (proj2 HBc)) as (lo & hi & Hrng & Hc).
  assert (Hq : s + 1 + Z.of_nat (length l) <= 2 ^ 47 - 8)
    by (pose proof Hsceil as H'; cbn [length] in H'; clear - H' AC1; lia).
  apply (psj_open_head B _ lo hi c s o (frame_addr ly 0 pos) sp1 (Ereg regs1 X)
           (mkst regs1 (Z_to_bv 64 PS_OPEN_RET) mem1 (seg_rom tfibsegs)) _ ot _ ly S W (unpoison U mem) md [(0, pos)]
           ly1 S1 U1 W1 md1 _ Q HS1 HJ1 HARU1 (Zle_0_nat _) E18 E19 E24 E47 E9 W1d
           ltac:(clear - Hsp1 Hspo Hoot; lia) Hrng Hc Hsc1 HAPP HRA0 HV0).
  intros ms2 mat2 E' HSH HJ2 HARU2 HAT HBD HAGR MEQ2 _ HV8 HV16.
  (* ---- the scan ---- *)
  assert (HAW : forall a, shadow_addr (frame_addr ly 0 pos) <= a < shadow_addr (frame_addr ly 0 pos) + 8 ->
            awr_byte tfibsegs B (STK_put_string + (ot - spZ regs)) ot (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf cap)
              (ablocks B ly S) (ablocks B ly1 S1) ly1 [(0, pos)] (frames S) a).
  { intros a Ha. left. right. right. right. exists 0, pos. split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite EF1. change (fs_frame_bytes 0 / 8) with 8. exact Ha. }
  assert (HCELL : forall i, (i <= length l)%nat ->
            psl_cell W1 (ms_mem ms2) (shadow_addr (frame_addr ly 0 pos)) (s + 1 + Z.of_nat i) (nth i (l ++ [0]) 0)).
  { intros i Hi.
    assert (Hx : s <= s + 1 + Z.of_nat i < s + Z.of_nat (length (c :: l)) + 1) by (cbn [length]; clear - Hi; lia).
    destruct (SEP _ Hx) as (N1 & N2 & N3).
    assert (Ha64 : 0 <= s + 1 + Z.of_nat i < 2 ^ 64) by (clear - Hx Hsceil Hs4096 AC1; lia).
    pose proof (psg2_sh_lo (s + 1 + Z.of_nat i) ltac:(clear - Hx Hsceil Hs4096 AC1; lia)) as (L1 & L2).
    apply (psg2_cell_mv W1 mem1 (ms_mem ms2)).
    - exact (MEQ2 _ Ha64 ltac:(clear - Hx Hsceil Hsp1 Hceil; lia)).
    - exact (MEQ2 (SHADOW_OFF + (s + 1 + Z.of_nat i) / 8) ltac:(clear - L1 L2; lia)
               ltac:(clear - L2 Hsp1 Hceil AC1; lia)).
    - split; [|split; [|split; [|split]]].
      + intros x Hxx. apply Hra1. clear - Hxx Hx. lia.
      + pose proof (Hg1 (Datatypes.S i) ltac:(rewrite length_app; cbn [length]; clear - Hi; lia)) as (HVi & _).
        replace (s + 1 + Z.of_nat i) with (s + Z.of_nat (Datatypes.S i)) by lia. exact HVi.
      + intros Hin. apply N3. clear - Hin SHB. lia.
      + exact N2.
      + exact N3. }
  apply (psl_scan B l lo hi E' ms2 _ ot _ ly S W (unpoison U mem) md [(0, pos)] ly1 S1 U1 W1 _ _ pos s
           (shadow_addr (frame_addr ly 0 pos)) c (frame_addr ly 0 pos + 32) o s Q Hrng HSH HJ2 HARU2 Hin1
           ltac:(rewrite EF1; reflexivity) HAT HBD HAW (Forall_inv_tail Hplain) (Forall_inv_tail Hbok) Hq HCELL).
  intros ms3 mat3 E'' HSE HJ3 HARU3 HATE MEQ3 HAG3.
  (* psl_at_end on image B: c on atom 25, r on atom 18 (image A: c on 18, r on 26) *)
  pose proof HATE as (_ & A21 & A22 & A24 & A18 & A19 & A32).
  assert (A9 : bv_unsigned (ew E'' 9) = sp1)
    by (rewrite (HAG3 9%nat ltac:(cbn; repeat (first [left; reflexivity | right]))),
                (HAGR 9%nat ltac:(cbn; repeat (first [left; reflexivity | right]))); exact E9).
  assert (HV8' : val_mem tfibsegs (mrestrict (w_H W1) (ms_mem ms3)) (sp1 + 8) 8 (frame_addr ly 0 pos)).
  { apply (psj_val_mem_pt (w_H W1) (ms_mem ms2) (ms_mem ms3) (sp1 + 8) 8 _); [|exact HV8].
    intros k Hk. apply MEQ3;
      [clear - Hk Hsp1 Hceil AC1 H470; lia | clear - Hk Hsp1 Hceil SHB AC1; unfold SHADOW_OFF in SHB; lia]. }
  assert (HV16' : val_mem tfibsegs (mrestrict (w_H W1) (ms_mem ms3)) (sp1 + 16) 8 (frame_addr ly 0 pos)).
  { apply (psj_val_mem_pt (w_H W1) (ms_mem ms2) (ms_mem ms3) (sp1 + 16) 8 _); [|exact HV16].
    intros k Hk. apply MEQ3;
      [clear - Hk Hsp1 Hceil AC1 H470; lia | clear - Hk Hsp1 Hceil SHB AC1; unfold SHADOW_OFF in SHB; lia]. }
  (* ---- from the loop's end to put #2's call ---- *)
  apply (psj_end_put2 B [psl_sh_region] psl_G sp1 (frame_addr ly 0 pos) (s + 1 + Z.of_nat (length l)) s o E'' ms3 _ ot
           _ ly S W (unpoison U mem) md [(0, pos)] ly1 S1 U1 W1 _ _ Q HSE HJ3 HARU3 A9 A21 A24 A18 A19
           ltac:(clear - Hsp1 Hceil AC1 H470; lia) ltac:(clear - HF4; lia) HV8' HV16').
  intros ms4 mat4 HS4 HJ4 HARU4 MEQ4 C1 C10 C11 C12 C21' C24'.
  destruct psg2_P2_regs as (G2 & G3 & G4 & G8 & G9 & G19 & G22 & G23 & G18).
  assert (AG : forall n, In n [2%nat; 3%nat; 4%nat; 8%nat; 9%nat; 27%nat] -> ew E'' n = ew (Ereg regs1 X) n)
    by (intros n Hn; rewrite (HAG3 n Hn); exact (HAGR n Hn)).
  assert (C2 : YK11.getr (ms_regs ms4) 2%bv = YK11.getr regs1 2%bv)
    by (rewrite (psg2_reg_at _ _ _ _ 2%bv 2 HS4 G2), (AG 2%nat ltac:(cbn; repeat (first [left; reflexivity | right])));
        exact (ew_Ereg_nat regs1 X 2 2%bv eq_refl)).
  assert (C3 : YK11.getr (ms_regs ms4) 3%bv = YK11.getr regs1 3%bv)
    by (rewrite (psg2_reg_at _ _ _ _ 3%bv 3 HS4 G3), (AG 3%nat ltac:(cbn; repeat (first [left; reflexivity | right])));
        exact (ew_Ereg_nat regs1 X 3 3%bv eq_refl)).
  assert (C4 : YK11.getr (ms_regs ms4) 4%bv = YK11.getr regs1 4%bv)
    by (rewrite (psg2_reg_at _ _ _ _ 4%bv 4 HS4 G4), (AG 4%nat ltac:(cbn; repeat (first [left; reflexivity | right])));
        exact (ew_Ereg_nat regs1 X 4 4%bv eq_refl)).
  assert (C8 : YK11.getr (ms_regs ms4) 8%bv = YK11.getr regs1 8%bv)
    by (rewrite (psg2_reg_at _ _ _ _ 8%bv 8 HS4 G8), (AG 8%nat ltac:(cbn; repeat (first [left; reflexivity | right])));
        exact (ew_Ereg_nat regs1 X 8 8%bv eq_refl)).
  assert (C9 : YK11.getr (ms_regs ms4) 9%bv = YK11.getr regs1 9%bv)
    by (rewrite (psg2_reg_at _ _ _ _ 9%bv 9 HS4 G9), (AG 9%nat ltac:(cbn; repeat (first [left; reflexivity | right])));
        exact (ew_Ereg_nat regs1 X 9 9%bv eq_refl)).
  assert (C19 : YK11.getr (ms_regs ms4) 19%bv = YK11.getr regs1 19%bv)
    by (rewrite (psg2_reg_at _ _ _ _ 19%bv 19 HS4 G19), (psg2_bv _ _ A19), R19; reflexivity).
  assert (C22 : YK11.getr (ms_regs ms4) 22%bv = YK11.getr regs1 22%bv)
    by (rewrite (psg2_reg_at _ _ _ _ 22%bv 22 HS4 G22), (psg2_bv _ _ A22), R22; reflexivity).
  assert (C23 : YK11.getr (ms_regs ms4) 23%bv = YK11.getr regs1 23%bv)
    by (rewrite (psg2_reg_at _ _ _ _ 23%bv 32 HS4 G23), A32, R23; reflexivity).
  assert (C18 : YK11.getr (ms_regs ms4) 18%bv = YK11.getr regs1 18%bv)
    by (rewrite (psg2_reg_at _ _ _ _ 18%bv 18 HS4 G18), (psg2_bv _ _ A18), R18; reflexivity).
  assert (C21 : YK11.getr (ms_regs ms4) 21%bv = YK11.getr regs1 21%bv) by (rewrite C21', R21; reflexivity).
  assert (C24 : YK11.getr (ms_regs ms4) 24%bv = YK11.getr regs1 24%bv) by (rewrite C24', R24; reflexivity).
  assert (C12'' : YK11.getr (ms_regs ms4) 12%bv = Z_to_bv 64 (Z.of_nat (length (c :: l))))
    by (rewrite C12; exact (psg2_len s c l)).
  (* ---- the call-site memory agrees with put #1's return off the seven slots ---- *)
  assert (HAG4 : pske_agree W1 W1 mem1 (ms_mem ms4) (fun a => sp1 + 8 <= a < sp1 + 64)).
  { pose proof (fsw_region_nth E'' _ _ 0 psl_sh_region HS4 eq_refl) as RS4. cbn [ms_mem restrict] in RS4.
    destruct RS4 as (_ & _ & _ & Cs4).
    change (YP09.base_val E'' (YP09.r_base psl_sh_region)) with (bv_unsigned (ew E'' 22)) in Cs4.
    rewrite A22 in Cs4.
    pose proof (proj1 HARU4) as HAR4.
    destruct (al_frames _ _ LAWS ly1 S1 W1 (unpoison U1 (ms_mem ms4)) _ 0 pos HAR4 Hin1) as (_ & _ & _ & Hsh4).
    rewrite EF1 in Hsh4. change (fs_frame_bytes 0 / 8) with 8 in Hsh4.
    assert (RAW : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 8 <= a < sp1 + 64) ->
                    ~ (shadow_addr (frame_addr ly 0 pos) <= a < shadow_addr (frame_addr ly 0 pos) + 8) ->
                    ms_mem ms4 (Z_to_bv 64 a) = mem1 (Z_to_bv 64 a)).
    { intros a Ha Hs Hg. rewrite (MEQ4 _), (MEQ3 a Ha Hg). exact (MEQ2 a Ha Hs). }
    split.
    - intros a Ha Hs.
      destruct (Z_lt_le_dec a (shadow_addr (frame_addr ly 0 pos))) as [Hl | Hl];
        [|destruct (Z_lt_le_dec a (shadow_addr (frame_addr ly 0 pos) + 8)) as [Hu | Hu]].
      + exact (psj_mbyte_pt (w_H W1) mem1 (ms_mem ms4) a (RAW a Ha Hs ltac:(clear - Hl; lia))).
      + exact (psg2_sh_eq E'' (Ereg regs1 X) _ _ _ Cs4 Cfsh a (conj Hl Hu)).
      + exact (psj_mbyte_pt (w_H W1) mem1 (ms_mem ms4) a (RAW a Ha Hs ltac:(clear - Hu; lia))).
    - intros a Ha Hs Hp.
      destruct (Z_lt_le_dec a (shadow_addr (frame_addr ly 0 pos))) as [Hl | Hl];
        [|destruct (Z_lt_le_dec a (shadow_addr (frame_addr ly 0 pos) + 8)) as [Hu | Hu]].
      + unfold apresent in *. rewrite (RAW a Ha Hs ltac:(clear - Hl; lia)). exact Hp.
      + destruct (Hsh4 (a - shadow_addr (frame_addr ly 0 pos)) ltac:(clear - Hl Hu; lia)) as (Hp4 & Hno4).
        replace (shadow_addr (frame_addr ly 0 pos) + (a - shadow_addr (frame_addr ly 0 pos))) with a in Hp4, Hno4
          by ring.
        exact (fsw_apresent_notowned B ly1 S1 U1 W1 (ms_mem ms4) _ a HARU4 Ha Hno4 Hp4).
      + unfold apresent in *. rewrite (RAW a Ha Hs ltac:(clear - Hu; lia)). exact Hp. }
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W1) _ _ ms4 HS4 eq_refl) at 1.
  exact (psg2_call ly S U W regs mem md ch ot o s buf cap failed text (c :: l) live peak cnt fail pos ly1 S1 U1 W1
    regs1 mem1 md1 buf1 (ms_regs ms4) (ms_mem ms4) _ Q PRE INV1 HJ4 HARU4 HAG4
    C1 C10 C11 C12'' C2 C8 C9 C19 C21 C22 C23 C24 C18 C3 C4 KONT).
Qed.

(* the statement check: psg2 IS the second premise of ps_close (this typechecks only if psg2's type converts to it) *)
Definition psg2_fits := fun seg1 => ps_close B seg1 psg2.

End G2.
