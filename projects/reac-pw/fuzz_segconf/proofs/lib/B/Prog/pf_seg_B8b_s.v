(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of check_round_trip on the ASan build of plugin-hostd/fuzz_command
   (0x87fd8, 286 instructions), proving tcheck_round_trip_spec (check_round_trip_c.v), in the shape of cgif_file_fuzzer's
   walks (lib/A/AChc.v, ACh1..ACh8.v, AChf.v): one statement per point between two calls (ST_B .. ST_EPI below), each
   segment proved by a run of the symbolic executor over the position-abstract listing (CmdPaLib.v) from a fresh seed,
   the inline checks removed by the shadow tokens (PaShadow.v), and the call at its end composed into the journal:
   the class-5 side-stack frame by aj_stack_malloc_atS (PaCall.v) and, from check_round_trip_k.v, aj_set_shadow_atS
   (__asan_set_shadow_f8/_00) and aj_stack_free_cls_atS (__asan_stack_free_5); the strdup wrapper by crts4_strdup_sub,
   the free wrapper by afree04_sub (PaCall.v), the strcmp wrapper by aj_art_at (PaArt.v); the program callees
   rec_calls_copy, joined, send_message and rec_calls_free by cl_callS_wide and rec_calls_equal by cl_callS_na
   (PaNoChain.v), each with its contract as a Section hypothesis. The skip path (no word, or the daemon did not act)
   joins the epilogue at 0x88314; the abort edges (0x8838c) are excluded by rt_okA and the callees' posts.
   Re-fit to statement passes 4, 4b and 5: the callee and runtime hypotheses hold at every
   FP state (forall fx0) and the segments use them at the ambient fx. send_message reaches the printf wrappers, so the
   points before its return (ST_B .. ST_F) prove the FP-existential post crt_postF (apost_baseF); crt_s6 calls
   send_message by PaFx.v's cl_callS_wideF with the rounding-mode premise HFRM and goes on at the FP state fx1 it
   returns (srr_after_callF_base). The points after it (ST_G .. ST_EPI) prove apost_base at the ambient FP state, so
   once the sections close they hold at fx1 (crt_G, used so by tcheck_round_trip_spec_holds). The skip path lifts
   ST_EPI's post by apost_baseF_of_base (crts3_skip). Pass 5 removed astack_pres: s0 is the frame pointer sp0 at every
   call, so each call's frame chain is the prologue's frame record (ra at sp0 - 8, the entry s0 at sp0 - 16, from
   crt_frame) on afn_pre's chain (achain_push, crt_chain), and chain_pre for the runtime allocation entries is
   achain_chain_pre of it. joined's new premises at its call: len's 8 bytes present (the journal's window), and
   (pass 5b) the stack from len - 16 present, from the statement's astack_pres kept by astack_pres_journal. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 521 of its 608 lines of code are new or changed and 4966 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the shared step of
   segment B8b of reac_segconf_parse_file's walk, the two instructions both B8b pieces PROV2 and JOIN end in:
     0x88e4c jal wrapper_snprintf (pa_sigma SS___interceptor_trampoline_snprintf = 0x43af0; return 0x88e50 =
             BASE + PF_B8B_RET_SNPC)
     0x88e50 j 0x88600 (TAIL)
   pb8b_snp_tail: from the state at 0x88e4c (pf_base at the line scope, the snprintf arguments a0 = d, a1 = n,
   a2 = "%s" 0x21340, a3 = src, the TAIL registers s9 / s6 already set, and a description of what pf_st holds once
   the string and its NUL are at d) the walk reaches the post of H_TAIL, by RtFormat.asnprintf_realizes at
   SS___interceptor_trampoline_snprintf (the Section hypothesis SNP), the FP-state lift of PaFx and HA_TAIL at the
   FP state snprintf returns. Two destinations (pb8b_dsts): PROV2's &c->seg[gi].ignore_file, inside the block c's
   first footprint range, and JOIN's cur_name F + 0x20 (16 bytes), inside the walk's own class-5 frame.
   A B8b sub-lane of the image-B G3 walk owner, 2026-10-30. proves function reac_segconf_parse_file (segment B8b, the
   shared call step; reuse search and CONFIRM: the rule-24 lookup record).
   ADAPTED from a working branch's lib/A/Prog/pf_a3_k.v (a3_snp_site, a3_mset_site: the snprintf step over
   the walk's journal through image A's segment-A8b lemma pfa8b_aj_snprintf_atSF, here pf_seg_B8b_t.v's pb8b_aj_snprintf_atSF) and
   the image-B cut rebuild of a lane clone lib/B/Prog/pf_seg_B10b_j.v (the B10b segment lane,
   961c19ce3f65: its keep lemmas, generalised here to any write set), re-derived on image B's code.
   The call keeps every byte outside the written range [d, d + |snprintf_s n "%s" [src]| + 1) and its stack window
   [s1 - 8192, s1) (CMD_SNP_K = 2 * ESTACK at sp = s1, pf_fi's register list); the cut's objects are carried
   across that keep clause by pb8b_kp_* below (each fact names the bytes it reads: stack slots and saved registers
   at or above s1, image bytes below kImgEnd, shadow bytes below kHighMemBeg, the text apart from d). No UBSan trap
   and no instrumented check lies in these two instructions. Positional names: none from an image-A table. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtFormat RtPFShared RtPFCmd.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaSB
PaCall PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c
SegInstB pf_pieces pf_seg_B8b_d pf_seg_B8b_t.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require pf_seg_B8b_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================ small tools ================================ *)
Ltac pb8bs_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 | st_ok ?sg ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_restrict_reg sg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Ltac pb8bs_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.
Lemma pb8bs_bvr : forall (rr : bvmap 5 word) (r : bv 5) k v, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = v ->
  getr rr r = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
(* a register list carried to a new register file that agrees on each of its registers *)
Lemma pb8bs_rg_tr : forall (rX rY : bvmap 5 word) L,
  pf_rg rX L -> (forall r v, In (r, v) L -> getr rY (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) -> pf_rg rY L.
Proof.
intros rX rY L H HE. unfold pf_rg in *. rewrite Forall_forall in *. intros [r v] Hin. cbn [fst snd].
rewrite (HE r v Hin). exact (H (r, v) Hin).
Qed.
(* the unowned read-only view from the cut's arodata (pf_a3_k.v a3_rom_view) *)
Lemma pb8bs_rom_view : forall {rc : YM05.RunCeil} segs B RLO RHI (W : world segs) mem,
  arodata_okP segs RLO RHI B (aview segs (w_H W) mem) -> RtDefs.rt_rom_view segs B W mem.
Proof. intros rc0 segs B RLO RHI W mem H a Hrom Ho He. apply H; [left; exact Hrom | exact Ho | exact He]. Qed.
(* what snprintf(d, n, "%s", s) leaves at d: sn_bytes (n - 1) s is the model's string and its NUL *)
Lemma pb8bs_sn_bytes : forall (n : Z) (s : list Z), ~ In 0 s ->
  RtPFShared.sn_bytes (n - 1) s = snprintf_s n F_s [AS s] ++ [0].
Proof.
intros n s H. unfold RtPFShared.sn_bytes. rewrite pf_seg_B8b_m.pb8b_snprintf_s_gen, cut_nul_id by exact H.
reflexivity.
Qed.
Lemma pb8bs_sn_len : forall (n : Z) (s : list Z), ~ In 0 s ->
  RtPFShared.sn_len (n - 1) s = Z.of_nat (S (length (snprintf_s n F_s [AS s]))).
Proof.
intros n s H. unfold RtPFShared.sn_len. rewrite pb8bs_sn_bytes by exact H. rewrite length_app. cbn [length]. lia.
Qed.
Lemma pb8bs_sn_len_le : forall (n : Z) (s : list Z), 1 <= n -> 1 <= RtPFShared.sn_len (n - 1) s <= n.
Proof.
intros n s Hn. unfold RtPFShared.sn_len, RtPFShared.sn_bytes. rewrite length_app, length_firstn. cbn [length]. lia.
Qed.
(* the shadow cells of a 32-aligned frame's bytes F + 32 .. F + 47 (pf_a3_k.v a3_shadow_sub) *)
Lemma pb8bs_shadow_sub : forall F j, F mod 32 = 0 -> 0 <= j < 16 ->
  shadow_addr (F + 32 + j) = shadow_addr F + 4 + j / 8.
Proof.
intros F j HF Hj. pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite HF, Z.add_0_r in D.
set (q := F / 32) in D. clearbody q. subst F. unfold shadow_addr.
replace (32 * q + 32 + j) with (j + (4 * q + 4) * 8) by lia.
replace (32 * q) with ((4 * q) * 8) by lia.
rewrite Z.div_add, Z.div_mul by lia. lia.
Qed.
(* cur_name's two shadow cells are 0 at the line scope *)
Lemma pb8bs_shb_cn : forall i, 4 <= i < 6 -> pf_shb PF_SC_LINE i = 0.
Proof. intros i Hi. unfold pf_shb, PF_SC_LINE, pf_io. cbn [sc_cn]. destruct (i <? 4) eqn:E; [apply Z.ltb_lt in E; lia|].
destruct (i <? 6) eqn:E'; [reflexivity | apply Z.ltb_ge in E'; lia]. Qed.

(* ================================ the destinations ================================ *)
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* the two places the shared snprintf writes: inside the block c's first footprint range (PROV2's
   &c->seg[gi].ignore_file) or cur_name (JOIN) *)
Definition pb8b_dsts (v : pfv) (pos dst L : Z) : Prop :=
  (p_c v <= dst /\ dst + L <= p_c v + seg_spec.RC_N + 4) \/ (dst = pf_F v pos + PF_O_CN /\ L = 16).

(* ================================ keeping a reader across a write set ================================ *)
(* rd' agrees with rd outside the write set Wr, and every byte rd shows rd' shows (pf_seg_B10b_j.v b10j_kept with
   the write set a parameter) *)
Definition pb8b_kp (Wr : Z -> Prop) (rd rd' : reader) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> rd' a = rd a) /\
  (forall a, 0 <= a < 2 ^ 64 -> rd a <> None -> rd' a <> None).

Section k.
Variable Wr : Z -> Prop.
Variables rd rd' : reader.
Hypothesis K : pb8b_kp Wr rd rd'.
Lemma pb8b_kp_byte : forall x, 0 <= x < 2 ^ 64 -> ~ Wr x -> rd' x = rd x.
Proof. intros x Hx Hn. exact (proj1 K x Hx Hn). Qed.
Lemma pb8b_kp_rdword : forall a, 0 <= a -> a + 8 <= 2 ^ 64 -> (forall k, 0 <= k < 8 -> ~ Wr (a + k)) ->
  rdword rd' a = rdword rd a.
Proof.
intros a H0 H1 Ho. apply rdword_ext. intros k Hk.
replace (a + k) with (a + k) by reflexivity. apply (proj1 K); [lia | apply Ho; lia].
Qed.
Lemma pb8b_kp_tail : forall e, 0 <= e -> e + 8 <= 2 ^ 64 -> sa_tail rd e -> sa_tail rd' e.
Proof.
intros e H0 H1 H x Hx. pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
exact (proj2 K x ltac:(lia) (H x Hx)).
Qed.
Lemma pb8b_kp_hull : forall q n, 0 <= q -> q + n <= 2 ^ 63 -> 0 < n -> shadow_hull_vis rd q n ->
  shadow_hull_vis rd' q n.
Proof.
intros q n H0 H1 Hn H s Hs. apply (proj2 K s); [|exact (H s Hs)].
unfold shadow_addr, SHADOW_OFF in Hs.
pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (q + n - 1) 8 ltac:(lia)).
pose proof (Z.div_pos (2147450880 + q / 8) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)).
lia.
Qed.
Lemma pb8b_kp_str : forall p s, 0 <= p -> p + Z.of_nat (length s) + 8 <= 2 ^ 64 ->
  (forall x, p <= x < p + Z.of_nat (length s) + 1 -> ~ Wr x) -> sa_str rd p s -> sa_str rd' p s.
Proof.
intros p s H0 H1 Ho [[Hz Hn] Ht].
split; [split; [|exact Hn] | exact (pb8b_kp_tail (p + Z.of_nat (length s)) ltac:(lia) ltac:(lia) Ht)].
intros i Hi. pose proof Hi as Hi'. rewrite length_app in Hi'. cbn [length] in Hi'.
rewrite (proj1 K (p + Z.of_nat i)); [exact (Hz i Hi) | lia | apply Ho; lia].
Qed.
Lemma pb8b_kp_addr : forall q n, 0 <= q -> q + n <= kHighMemEnd ->
  (forall x, kLowMemEnd <= x < kHighMemBeg -> ~ Wr x) -> sa_addr rd q n -> sa_addr rd' q n.
Proof.
intros q n Hq Hn NS (H0 & H1 & H2 & H3 & H4). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
split; [|intros Hp; exact (pb8b_kp_hull _ _ H0 H1 Hp (H4 Hp))].
intros x Hx. destruct (H3 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
pose proof (YCbq.shadow_addr_bounds x ltac:(lia)) as Bx. pose proof asan_consts as (_ & E2 & E3 & E4 & E5).
unfold shadow_of_addr in *. unfold shadow_addr in Bx.
rewrite (proj1 K); [exact Hs | lia | apply NS; lia].
Qed.
Lemma pb8b_kp_bytes : forall p (bs : list byte), 0 <= p -> p + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall x, p <= x < p + Z.of_nat (length bs) -> ~ Wr x) -> sa_bytes rd p bs -> sa_bytes rd' p bs.
Proof.
intros p bs H0 H1 Ho H i Hi. rewrite (proj1 K (p + Z.of_nat i)); [exact (H i Hi) | lia | apply Ho; lia].
Qed.
Lemma pb8b_kp_nm : forall a nm, 0 <= a -> a + 16 <= 2 ^ 64 -> (forall x, a <= x < a + 16 -> ~ Wr x) ->
  pf_nm rd a nm -> pf_nm rd' a nm.
Proof.
intros a nm H0 H1 Ho (f & Hb & He). exists f. split; [|exact He].
destruct He as [Hl _]. apply (pb8b_kp_bytes a f H0); [rewrite Hl; lia | rewrite Hl; exact Ho | exact Hb].
Qed.
Lemma pb8b_kp_rconf : forall c cf, 0 <= c -> c + seg_spec.SEG_C_SIZE <= 2 ^ 64 ->
  (forall x, c <= x < c + seg_spec.SEG_C_SIZE -> ~ Wr x) -> sa_rconf rd c cf -> sa_rconf rd' c cf.
Proof.
intros c cf H0 H1 Ho (bs & Hb & Henc). exists bs. split; [|exact Henc].
destruct Henc as [Hl _]. apply (pb8b_kp_bytes c bs H0); [rewrite Hl; lia | rewrite Hl; exact Ho | exact Hb].
Qed.
(* image facts: the image bytes are not written *)
Hypothesis NI : forall x, 0x10000 <= x < kImgEnd -> ~ Wr x.
Lemma pb8b_kp_lit : forall a s, sa_lit SEGS B rd a s -> sa_lit SEGS B rd' a s.
Proof.
intros a s (Ha & Hs & Hp & Hr & Hi). split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
assert (HI : forall x, a <= x < a + (Z.of_nat (length s) + 1) -> 0x10000 <= x < kImgEnd)
  by (intros x Hx; exact (pa_img_range x (proj1 (Hi x Hx)))).
pose proof (HI a ltac:(lia)) as HA. pose proof (HI (a + Z.of_nat (length s)) ltac:(lia)) as HE.
unfold kImgEnd in *.
apply (pb8b_kp_str a s); [lia | lia | | exact Hs]. intros x Hx. apply NI. apply HI. lia.
Qed.
Lemma pb8b_kp_cat : forall cat, sa_cat SEGS B rd cat -> sa_cat SEGS B rd' cat.
Proof.
intros cat (Hp & Hi & Hrows). split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp. split; [|exact (pb8b_kp_lit tp _ Hl)].
assert (Hn' : (Z.of_nat i < 11)) by (unfold pin_spec.CAT_N in Hn; lia).
assert (HR : forall k, 0 <= k < 8 -> 0x10000 <= pin_spec.row_addr cat i + k < kImgEnd).
{ intros k Hk. apply pa_img_range. apply Hi. unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES. lia. }
pose proof (HR 0 ltac:(lia)) as HR0. pose proof (HR 7 ltac:(lia)) as HR7. unfold kImgEnd in *.
rewrite (pb8b_kp_rdword (pin_spec.row_addr cat i)); [exact Htp | lia | lia |].
intros k Hk. apply NI. apply HR. exact Hk.
Qed.
Lemma pb8b_kp_rod : arodata_okP SEGS RLO_A RHI_A B rd -> arodata_okP SEGS RLO_A RHI_A B rd'.
Proof.
intros H a Hro Ho He.
assert (HI : 0x10000 <= a < kImgEnd).
{ destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
  - apply pa_img_range. exists sg. split; [exact Hsg | exact Hr].
  - unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, kImgEnd in *. lia. }
unfold kImgEnd in HI. rewrite (proj1 K a); [exact (H a Hro Ho He) | lia | apply NI; unfold kImgEnd; lia].
Qed.
Lemma pb8b_kp_ssp : sa_ssp rd gotwA guardA -> sa_ssp rd' gotwA guardA.
Proof.
intros (G1 & g & G2).
split; [rewrite (pb8b_kp_rdword gotwA); [exact G1 | unfold gotwA; lia | unfold gotwA; lia |
  intros k Hk; apply NI; unfold gotwA, kImgEnd; lia]|].
exists g. rewrite (pb8b_kp_rdword guardA); [exact G2 | unfold guardA; lia | unfold guardA; lia |
  intros k Hk; apply NI; unfold guardA, kImgEnd; lia].
Qed.
(* the caller's objects: the text's bytes are not written, the shadow and the image are not written *)
Hypothesis NS : forall x, kLowMemEnd <= x < kHighMemBeg -> ~ Wr x.
Lemma pb8b_kp_obj : forall v lyc Sc, pf_obj B v lyc Sc rd ->
  p_t v + pf_len v <= alloc_ceiling -> p_c v + seg_spec.SEG_C_SIZE <= alloc_ceiling ->
  (forall x, p_t v <= x < p_t v + pf_len v -> ~ Wr x) -> pf_obj B v lyc Sc rd'.
Proof.
intros v lyc Sc (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) Ht Hc HT.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof H2 as (Ht0 & _). pose proof H4 as (Hc0 & _).
split; [apply (pb8b_kp_str (p_t v) (p_s v)); [lia | unfold pf_len in *; lia | intros x Hx; apply HT; unfold pf_len; lia | exact H1]|].
split; [apply (pb8b_kp_addr _ _ Ht0); [lia | exact NS | exact H2]|]. split; [exact H3|].
split; [apply (pb8b_kp_addr _ _ Hc0); [lia | exact NS | exact H4]|]. split; [exact H5|].
split; [exact (pb8b_kp_cat _ H6)|].
split; [intros x Hx; exact (pb8b_kp_lit _ _ (H7 x Hx))|].
split; [exact (pb8b_kp_rod H8) | exact (pb8b_kp_ssp H9)].
Qed.
End k.
Lemma pb8b_kp_trans : forall Wr rd1 rd2 rd3, pb8b_kp Wr rd1 rd2 -> pb8b_kp Wr rd2 rd3 -> pb8b_kp Wr rd1 rd3.
Proof.
intros Wr rd1 rd2 rd3 [A1 B1] [A2 B2]. split.
- intros a Ha Hn. rewrite (A2 a Ha Hn). exact (A1 a Ha Hn).
- intros a Ha Hv. exact (B2 a Ha (B1 a Ha Hv)).
Qed.
Lemma pb8b_kp_eq : forall Wr rd1 rd2, (forall a, 0 <= a < 2 ^ 64 -> rd2 a = rd1 a) -> pb8b_kp Wr rd1 rd2.
Proof. intros Wr rd1 rd2 H. split; [intros a Ha _; exact (H a Ha) | intros a Ha Hv; rewrite (H a Ha); exact Hv]. Qed.
Lemma pb8b_kp_mono : forall (Wr Wr' : Z -> Prop) rd1 rd2, (forall a, Wr a -> Wr' a) -> pb8b_kp Wr rd1 rd2 ->
  pb8b_kp Wr' rd1 rd2.
Proof. intros Wr Wr' rd1 rd2 HW [A1 B1]. split; [intros a Ha Hn; apply A1; [exact Ha | intros H; exact (Hn (HW a H))] | exact B1]. Qed.

(* ================================ the destination's facts ================================ *)
(* every premise of pb8b_aj_snprintf_atSF about the written range, from the cut facts, in both cases; and the
   bytes of the cut that a write there must miss (the text, the frame's flag pointer) *)
Lemma pb8b_dst_facts : forall {fx : YK11.FPState} v pos lyc Sc Wc rX memc mdc memT mdT dst L,
  pf_cx B v -> pf_fi (fx := fx) B v pos lyc Sc Wc rX memc mdc -> pf_obj B v lyc Sc (rdW Wc memc) ->
  AR SEGS B lyc Sc Wc memT mdT -> pf_fsh (rdW Wc memT) (pf_SH v pos) PF_SC_LINE ->
  pb8b_dsts v pos dst L -> 1 <= L <= 96 ->
  4096 <= dst /\ dst + L <= alloc_ceiling /\ off_img dst L /\
  (dst + L <= 0x7fff7000 \/ 0x10007fff8000 <= dst) /\
  (forall a, dst <= a < dst + L ->
     awr_byte SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (ablocks B (p_ly v) (p_S v))
       (ablocks B lyc Sc) (frames (p_S v)) lyc [(5, pos)] a) /\
  (forall a, dst <= a < dst + L -> inFP (seg_spec.RC_PARSE_W (p_c v)) a -> writable_at SEGS (mrestrict (w_H Wc) memT) a) /\
  amem_range dst (L + 8) /\
  range_addressable (rdW Wc memT) SHADOW_OFF dst L /\ shadow_hull_vis (rdW Wc memT) dst L /\
  (forall x, p_t v <= x < p_t v + pf_len v -> ~ (dst <= x < dst + L)) /\
  (forall x, pf_F v pos + fs_frame_bytes 5 - 8 <= x < pf_F v pos + fs_frame_bytes 5 -> ~ (dst <= x < dst + L)).
Proof.
intros fx v pos lyc Sc Wc rX memc mdc memT mdT dst L HCX HFI HOBJ HART HFSH HD HL.
destruct (pb8b_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HG & Hin & EF & Hfrs & HAR).
pose proof HG as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & F5).
destruct (pb8b_cblk B v pos lyc Sc Wc rX memc mdc HCX HFI HOBJ) as (Hc0 & Hc16 & Hc4096 & Hcceil & HcA & HcH & Hcap).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HOBJ as (_ & _ & HtH & _).
destruct HtH as (bt & mt & Hbt & Hbt1 & Hbt2).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc bt mt HAR Hbt) as (_ & Hbt4096 & Hbtceil & Hbtapp & _ & _ & Hmt).
pose proof (req_size_pos mt ltac:(lia)) as [_ Hrqt].
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc bt mt 5 pos HAR Hbt Hin) as Hsept.
unfold zdisjoint in Hsept. cbn [fst snd] in Hsept. rewrite EF in Hsept. change (fs_frame_bytes 5) with 2048 in Hsept.
change (fs_frame_bytes 5) with 2048.
pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & _ & (fe & (RP & _)) & _).
pose proof RP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDJ & _).
unfold sa_disj in HDJ. unfold seg_spec.cstr_span in HDJ.
pose proof (Z.mod_pos_bound (- (p_t v + Z.of_nat (length (p_s v)) + 1)) 8 ltac:(lia)) as Hspm.
destruct HD as [(Hd1 & Hd2) | (Hd1 & Hd2)].
- (* the block c *)
  destruct HcH as (b & m & Hb & Hb1 & Hb2).
  destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hb) as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & Hm).
  destruct (al_blocks _ _ LAWS lyc Sc Wc memT mdT b m HART Hb) as (_ & _ & _ & _ & HbpT & _ & _).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hrq].
  pose proof (blk_off_imgP B lyc Sc Wc memc mdc b m HAR Hb) as Hoff.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
  unfold seg_spec.SEG_C_SIZE, seg_spec.RC_N in *.
  split; [lia|]. split; [lia|].
  split; [exact (pb8b_off_img_sub b (req_size m) dst L Hoff ltac:(lia) ltac:(lia) ltac:(lia))|].
  split; [lia|].
  split.
  { intros a Ha. right; left. split.
    - apply pb8b_fp_block; unfold seg_spec.RC_N; lia.
    - exists b, m. split; [exact Hb | lia]. }
  split; [intros a Ha _; apply (apresent_writable SEGS); exact (proj1 (HbpT a ltac:(lia)))|].
  split; [exact (amem_range_of_block SEGS B LAWS lyc Sc Wc memT mdT b m dst (L + 8) HART Hb ltac:(lia) ltac:(lia))|].
  split; [exact (range_addressable_of_block SEGS B LAWS lyc Sc Wc memT mdT b m dst L HART Hb ltac:(lia) ltac:(lia))|].
  split; [exact (shadow_hull_vis_of_block SEGS B LAWS lyc Sc Wc memT mdT b m dst L HART Hb ltac:(lia) ltac:(lia) ltac:(lia))|].
  split; [intros x Hx Hd; unfold pf_len in Hx; lia|].
  intros x Hx Hd. lia.
- (* cur_name *)
  subst dst L. unfold PF_O_CN in *.
  destruct (al_frames _ _ LAWS lyc Sc Wc memT mdT 5 pos HART Hin) as (HFal & HFapp & HFb & HFsh).
  rewrite EF in HFal, HFapp, HFb, HFsh. change (fs_frame_bytes 5) with 2048 in HFapp, HFb.
  change (fs_frame_bytes 5 / 8) with 256 in HFsh.
  change (shadow_addr (pf_F v pos)) with (pf_SH v pos) in HFsh.
  pose proof (frm_off_imgP B lyc Sc Wc memc mdc 5 pos HAR Hin) as Hoff. rewrite EF in Hoff.
  change (fs_frame_bytes 5) with 2048 in Hoff.
  destruct (pb8b_SHb v pos HG) as (ESH & SH1 & SH2 & F8).
  split; [lia|]. split; [lia|].
  split; [exact (pb8b_off_img_sub (pf_F v pos) 2048 (pf_F v pos + 0x20) 16 Hoff ltac:(lia) ltac:(lia) ltac:(lia))|].
  split; [lia|].
  split.
  { intros a Ha. right; right; right; left. exists 5, pos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 5) with 2048. lia. }
  split.
  { intros a Ha Hfp. exfalso. apply pb8b_fp_in in Hfp. unfold seg_spec.SEG_C_SIZE in *. lia. }
  split; [apply amem_range_high; [lia | lia | lia]|].
  split.
  { intros x Hx. exists 0. split; [|left; reflexivity].
    set (j := x - pf_F v pos - 32).
    assert (Hj : 0 <= j / 8 < 2) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (Ex : shadow_of_addr SHADOW_OFF x = shadow_addr (pf_F v pos + 32 + j))
      by (unfold shadow_of_addr, shadow_addr, j; f_equal; f_equal; lia).
    rewrite Ex, (pb8bs_shadow_sub _ j F3 ltac:(lia)).
    replace (shadow_addr (pf_F v pos) + 4 + j / 8) with (pf_SH v pos + (4 + j / 8)) by (unfold pf_SH; lia).
    rewrite (HFSH (4 + j / 8)) by lia. rewrite pb8bs_shb_cn by lia. reflexivity. }
  split.
  { intros s Hs.
    pose proof (pb8bs_shadow_sub _ 0 F3 ltac:(lia)) as S0. rewrite Z.add_0_r in S0.
    pose proof (pb8bs_shadow_sub _ 15 F3 ltac:(lia)) as S15.
    replace (pf_F v pos + 32 + 16 - 1) with (pf_F v pos + 32 + 15) in Hs by lia.
    rewrite S15, S0 in Hs.
    assert (E0 : 0 / 8 = 0) by reflexivity. assert (E1 : 15 / 8 = 1) by reflexivity.
    rewrite E0, E1, Z.add_0_r in Hs. change (shadow_addr (pf_F v pos)) with (pf_SH v pos) in Hs.
    pose proof (Z.div_mod (pf_SH v pos + 4) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (pf_SH v pos + 4) 8 ltac:(lia)) as B1.
    pose proof (Z.div_mod (pf_SH v pos + 4 + 1) 8 ltac:(lia)) as D2.
    pose proof (Z.mod_pos_bound (pf_SH v pos + 4 + 1) 8 ltac:(lia)) as B2.
    pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)) as D32. rewrite F3, Z.add_0_r in D32.
    assert (Hsl : pf_SH v pos <= s < pf_SH v pos + 256) by (unfold SHADOW_OFF in ESH; lia).
    destruct (HFsh (s - pf_SH v pos) ltac:(lia)) as [Hp _].
    replace s with (pf_SH v pos + (s - pf_SH v pos)) by lia.
    exact (aview_some_of_apresent SEGS _ _ _ Hp). }
  split; [intros x Hx Hd; unfold pf_len in *; lia|].
  intros x Hx Hd. lia.
Qed.

(* the slots of PF_SL lie at s1 + 0x00 .. 0xd8 (pf_seg_B10b_j.v b10j_PF_SL_offs) *)
Lemma pb8b_PF_SL_offs : forall v pos ov, In ov (PF_SL v pos) -> 0x00 <= fst ov <= 0xd8.
Proof.
intros v pos ov H. unfold PF_SL in H. cbn [In] in H.
repeat (destruct H as [<- | H]; [cbn [fst]; lia|]). destruct H.
Qed.

(* ================================ the shared step ================================ *)
Hypothesis SNP : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_snprintf) gotwA guardA.
Section x. Context {fx : YK11.FPState}.

Lemma pb8b_snp_tail : forall n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d (dst L src : Z) (str : list Z),
  HA_TAIL B n ->
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  pf_lctx (p_s v) o ln d -> (length (skipn o (p_s v)) < n)%nat ->
  pf_rg rX (PF_RL v pos ++ [(25, p_t v + Z.of_nat o); (22, ln)]) ->
  pf_rg rX [(10, dst); (11, L); (12, seg_litA_rc F_s); (13, src)] ->
  pb8b_dsts v pos dst L -> 1 <= L <= 96 ->
  sa_str (rdW Wc memc) src str -> sa_addr (rdW Wc memc) src (Z.of_nat (length str) + 1) ->
  (length str <= 65535)%nat -> 0 < src -> amem_range src (Z.of_nat (length str) + 8) ->
  src + seg_spec.cstr_span src str <= alloc_ceiling ->
  sa_disj src (seg_spec.cstr_span src str) dst L ->
  (forall rd' : reader,
     (forall k, (k <= length (snprintf_s L F_s [AS str]))%nat ->
        rd' (dst + Z.of_nat k) = Some (nth k (snprintf_s L F_s [AS str] ++ [0]) 0)) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (dst <= a < dst + Z.of_nat (S (length (snprintf_s L F_s [AS str])))) ->
        ~ (pf_s1 v - 8192 <= a < pf_s1 v) -> rd' a = rdW Wc memc a) ->
     pf_st v pos rd' cf cur nm (length (skipn o (p_s v)))) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_PROV2) rX memc mdc)
    (PF_POSTr B v (fst (fst (r_lines (cf, cur, nm) ln (lines (skipn o (p_s v))))))).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf cur nm o ln d dst L src str TAIL HB HCTX HN HRG HRA HD HL
  HSTR HSA HSL Hsrc0 HSAM HSPAN HDISJ HPOST.
pose proof HB as (HCX & HFI & HOBJ & HSL0 & HFSH).
destruct (pb8b_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HG & Hin & EF & Hfrs & HAR).
pose proof HG as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & F5).
destruct (pb8b_SHb v pos HG) as (ESH & SH1 & SH2 & F8).
destruct (pb8b_cblk B v pos lyc Sc Wc rX memc mdc HCX HFI HOBJ) as (Hc0 & Hc16 & Hc4096 & Hcceil & HcA & HcH & Hcap).
pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof STK_values as (_ & _ & _ & ESTK & _).
pose proof HOBJ as (_ & _ & HtH & _ & _ & _ & HLIT & HROD & HSSP).
destruct HtH as (bt & mt & Hbt & Hbt1 & Hbt2).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc bt mt HAR Hbt) as (_ & Hbt4096 & Hbtceil & Hbtapp & _ & _ & Hmt).
pose proof (req_size_pos mt ltac:(lia)) as [_ Hrqt].
assert (Htceil : p_t v + pf_len v <= alloc_ceiling) by lia.
assert (NZ : ~ In 0 str) by (destruct HSTR as [[_ Hn] _]; exact Hn).
assert (Hlen : Z.of_nat (length str) <= 65535).
{ apply Nat2Z.inj_le in HSL. assert (E : Z.of_nat 65535 = 65535) by (vm_compute; reflexivity). lia. }
pose proof (pb8bs_sn_len_le L str ltac:(lia)) as HSNL.
(* ---- 0x88e4c: the call ---- *)
set (E := Eimg (Ereg rX [])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr rX r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (HS : st_ok_pi SEGS VAL E (mkSS PF_PROV2 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_PROV2)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. tauto.
  - unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor]. }
unfold cfg_at. change (w64 (BASE + PF_PROV2)) with (Z_to_bv 64 (BASE + PF_PROV2)).
paj_run_shc (SRr_run_pi_AJ (fx := fx) B LAWS) (SRr_run_pi_AJ_call (fx := fx) B LAWS) HS HJ.
{ apply awr_ok_nil. }
pb8bs_clear_md.
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs:=SEGS) E _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [intros b0 wlo whi a0 Hin0 Hrr; vm_compute in Hin0; destruct Hin0 | exact Ha | tauto]. }
clear HF HFr HG.
assert (Q1 : getr (ms_regs ms) (Z_to_bv 5 1) = Z_to_bv 64 (BASE + 16528))
  by (pb8bs_rreg HS; apply (codeptr_val _ 16528 HEI)).
change (BASE + 16528) with (BASE + PF_B8B_RET_SNPC) in Q1.
assert (QK : forall r, In r [2; 3; 4; 8; 9; 10; 11; 12; 13; 18; 20; 21; 22; 25; 26] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [pb8bs_rreg HS; rewrite pb8b_den_atom0; apply EE; reflexivity |]). destruct Hr. }
set (LT := PF_RL v pos ++ [(25, p_t v + Z.of_nat o); (22, ln)]) in *.
set (L0 := [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v); (20, SHADOW_OFF)]) in *.
set (LA := [(10, dst); (11, L); (12, seg_litA_rc F_s); (13, src)]) in *.
assert (RGm : pf_rg (ms_regs ms) (L0 ++ LT ++ LA)).
{ apply (pb8bs_rg_tr rX); [apply pb8b_rg_app; [exact HRG0 | apply pb8b_rg_app; [exact HRG | exact HRA]]|].
  intros r w Hrw. apply QK. subst L0 LT LA. unfold PF_RL in Hrw. cbn [In app] in Hrw |- *.
  repeat (destruct Hrw as [Hq | Hrw]; [injection Hq as <- _; pb8b_in |]). destruct Hrw. }
pmkst HS.
(* the readers at the call: the run wrote nothing *)
set (rd0 := rdW Wc memc) in *.
set (rdT := rdW Wc (ms_mem ms)) in *.
assert (KT : forall Wr, pb8b_kp Wr rd0 rdT) by (intros Wr; apply pb8b_kp_eq; exact K0).
pose proof (proj1 HJ) as HART.
assert (NIF : forall x, 0x10000 <= x < kImgEnd -> ~ False) by (intros; tauto).
assert (NSF : forall x, kLowMemEnd <= x < kHighMemBeg -> ~ False) by (intros; tauto).
assert (HFSHT : pf_fsh rdT (pf_SH v pos) PF_SC_LINE).
{ intros i Hi. rewrite (K0 (pf_SH v pos + i)) by lia. exact (HFSH i Hi). }
destruct (pb8b_dst_facts v pos lyc Sc Wc rX memc mdc (ms_mem ms) mdv dst L HCX HFI HOBJ HART HFSHT HD HL)
  as (Hd4096 & Hdceil & Hdoff & Hdapp & Hdawr & Hdwr & Hdamr & Hdra & Hdhv & HdT & HdFL).
assert (HSTRT : sa_str rdT src str).
{ apply (pb8b_kp_str (fun _ => False) rd0 rdT (KT _)); [lia | | intros; tauto | exact HSTR].
  unfold seg_spec.cstr_span in HSPAN. pose proof (Z.mod_pos_bound (- (src + Z.of_nat (length str) + 1)) 8 ltac:(lia)). lia. }
assert (HSAT : sa_addr rdT src (Z.of_nat (length str) + 1)).
{ apply (pb8b_kp_addr (fun _ => False) rd0 rdT (KT _)); [lia | | exact NSF | exact HSA].
  unfold seg_spec.cstr_span in HSPAN. pose proof (Z.mod_pos_bound (- (src + Z.of_nat (length str) + 1)) 8 ltac:(lia)). lia. }
assert (HLITT : sa_lit SEGS B rdT (seg_litA_rc F_s) F_s).
{ apply (pb8b_kp_lit (fun _ => False) rd0 rdT (KT _) NIF). apply HLIT.
  unfold PARSE_FILE_LITS. apply in_or_app. left. left. reflexivity. }
assert (HSSPT : sa_ssp rdT gotwA guardA) by exact (pb8b_kp_ssp (fun _ => False) rd0 rdT (KT _) NIF HSSP).
assert (HRODT : arodata_okP SEGS RLO_A RHI_A B rdT) by exact (pb8b_kp_rod (fun _ => False) rd0 rdT (KT _) NIF HROD).
pose proof pf_B_values as (_ & _ & _ & EGW & EGD & _ & _ & _ & _ & _ & ELF).
assert (Harg : argZ (ms_regs ms) 3 = src).
{ unfold argZ. replace (Z_to_bv 5 (10 + 3)) with (Z_to_bv 5 13) by (apply bv_eq; reflexivity).
  rewrite (pb8b_rg _ _ 13 src RGm ltac:(subst L0 LT LA; unfold PF_RL; pb8b_in)). unfold w64.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. destruct HSA as (HL0 & HL63 & _). change (bv_modulus 64) with (2 ^ 64). lia. }
assert (Hsp : spZ (ms_regs ms) = pf_sp0 v + (pf_s1 v - pf_sp0 v)).
{ unfold spZ. rewrite (pb8b_rg_bv _ _ 2 (pf_s1 v) 2%bv RGm ltac:(subst L0; pb8b_in) eq_refl).
  unfold w64. rewrite unsigned_lit_small by lia. lia. }
(* ---- the snprintf ---- *)
eapply SRr_bind.
{ apply (pb8b_aj_snprintf_atSF SEGS B LAWS pa_segs_low gotwA guardA (pa_sigma SS___interceptor_trampoline_snprintf)
    (SNP fx) Wc (ms_regs ms) (ms_mem ms) STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v))
    (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdv 0 dst L (seg_litA_rc F_s) str
    (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + PF_B8B_RET_SNPC)) HJ).
  - exact (pb8b_rg_bv _ _ 10 dst 10%bv RGm ltac:(subst L0 LT LA; unfold PF_RL; pb8b_in) eq_refl).
  - exact (pb8b_rg_bv _ _ 11 L 11%bv RGm ltac:(subst L0 LT LA; unfold PF_RL; pb8b_in) eq_refl).
  - exact (pb8b_rg_bv _ _ 12 (seg_litA_rc F_s) 12%bv RGm ltac:(subst L0 LT LA; unfold PF_RL; pb8b_in) eq_refl).
  - lia.
  - lia.
  - lia.
  - exact Hsp.
  - exact (pb8b_m16 _ _ S6 S3).
  - lia.
  - rewrite ESTK. unfold RtPFCmd.CMD_SNP_K, ESTACK. lia.
  - exact (pb8b_rg_bv _ _ 3 (as_gp B) 3%bv RGm ltac:(subst L0; pb8b_in) eq_refl).
  - exact (pb8b_rg_bv _ _ 4 (as_tp B) 4%bv RGm ltac:(subst L0; pb8b_in) eq_refl).
  - apply (pb8bs_bvr _ _ 1); [reflexivity | exact Q1].
  - assert (ERET : PF_B8B_RET_SNPC = 16528) by (vm_compute; reflexivity).
    rewrite ERET. apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [exact (Hdawr a Ha)|]. unfold RtPFCmd.CMD_SNP_K, ESTACK. lia.
  - intros a Ha Hfp _. exact (Hdwr a Ha Hfp).
  - exact Hdamr.
  - exact Hdra.
  - exact Hdhv.
  - exact (pb8b_off_img_sub dst L dst (RtPFShared.sn_len (L - 1) str) Hdoff ltac:(lia) ltac:(lia) ltac:(lia)).
  - unfold RtPFCmd.CMD_IMG_HI, RtPFCmd.CMD_SNP_K, ESTACK, kImgEnd. lia.
  - exact HSSPT.
  - unfold gotwA. lia.
  - unfold gotwA, RtPFCmd.CMD_IMG_HI, kImgEnd. lia.
  - unfold guardA. lia.
  - unfold guardA, RtPFCmd.CMD_IMG_HI, kImgEnd. lia.
  - unfold gotwA, RtPFCmd.CMD_IMG_LO. lia.
  - unfold guardA, RtPFCmd.CMD_IMG_LO. lia.
  - (* "%s" with the one string argument str at src *)
    destruct HLITT as (Hf0 & Hfstr & Hpin & _ & _).
    pose proof (Hpin lyc Sc Wc (ms_mem ms) mdv HART) as Hfad. rewrite pb8b_F_s_len in Hfad.
    apply (pb8b_FR_s_regs _ _ _ src str (ms_regs ms) Harg Hf0).
    + rewrite ELF. unfold RtPFCmd.CMD_IMG_LO. lia.
    + rewrite ELF. unfold RtPFCmd.CMD_GOTW. lia.
    + exact Hfstr.
    + exact Hfad.
    + rewrite ELF. unfold RtPFShared.snp_out. rewrite Hsp.
      constructor; [unfold zdisjoint; cbn [fst snd]; unfold RtPFCmd.CMD_SNP_K, ESTACK; lia|].
      constructor; [unfold zdisjoint; cbn [fst snd]; unfold off_img in Hdoff; lia | constructor].
    + exact Hsrc0.
    + exact (pb8b_bytes_range_aview SEGS (w_H Wc) (ms_mem ms) src str HSTRT).
    + lia.
    + exact HSTRT.
    + exact HSAT.
    + exact HSAM.
    + unfold RtPFShared.snp_out. rewrite Hsp. unfold sa_disj in HDISJ.
      constructor; [unfold zdisjoint; cbn [fst snd]; unfold RtPFCmd.CMD_SNP_K, ESTACK; lia|].
      constructor; [unfold zdisjoint; cbn [fst snd]; lia | constructor].
  - lia.
  - exact (pb8bs_rom_view SEGS B RLO_A RHI_A Wc (ms_mem ms) HRODT).
  - exact HFRM. }
cbv beta. intros W2 c2 _ (-> & fx1 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HP2 & H10 & Hby & Hkeep & Hgr & Hsame).
replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) in Hkeep by lia.
change RtPFCmd.CMD_SNP_K with 8192 in Hkeep.
rewrite (pb8bs_sn_len L str NZ) in Hby, Hkeep, HSNL. rewrite (pb8bs_sn_bytes L str NZ) in Hby.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES2 & _). rewrite ESTK in HPRES2.
unfold PF_POSTr. eapply (srr_apost_baseF_lift SEGS fx1); [exact Hfx|].
(* ---- 0x88e50: j TAIL, at the FP state snprintf returned ---- *)
set (E2 := Eimg (Ereg regs2 [])).
assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
assert (EE2 : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E2 k = getr regs2 r)
  by (intros k r Hk; subst E2; apply ew_Eimg_Ereg_nat; exact Hk).
assert (HS2 : st_ok_pi (fx := fx1) SEGS VAL E2 (mkSS PF_B8B_RET_SNPC sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H Wc) (@mkst fx1 regs2 (Z_to_bv 64 (BASE + PF_B8B_RET_SNPC)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E2. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. tauto.
  - unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor]. }
paj_run_to_sh (SRr_run_to_pi_AJ (fx := fx1) B LAWS) HS2 HJ2 PF_TAIL.
{ apply awr_ok_nil. }
cbn [ms_mem mkst] in HFr, HG, HF.
pb8bs_clear_md.
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms0) a = rdW Wc mem2 a).
{ intros a Ha. apply (kept_of_frame (segs:=SEGS) E2 _ (w_H Wc) mem2 (ms_mem ms0) (fun _ => False) HFr);
    [intros b0 wlo whi a0 Hin0 Hrr; vm_compute in Hin0; destruct Hin0 | exact Ha | tauto]. }
assert (QK3 : forall r, In r [2; 3; 4; 8; 9; 18; 20; 21; 22; 25; 26] ->
    getr (ms_regs ms0) (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [pb8bs_rreg HS2; rewrite pb8b_den_atom0; apply EE2; reflexivity |]). destruct Hr. }
pmkst HS2.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
  change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_TAIL) rg mm mdx) end.
set (rd2 := rdW Wc mem2) in *.
set (rd3 := rdW Wc (ms_mem ms0)) in *.
(* the write set of the call and what the cut keeps across it *)
set (Wr := fun a => (dst <= a < dst + L) \/ (pf_s1 v - 8192 <= a < pf_s1 v)).
assert (KP : pb8b_kp Wr rd0 rd3).
{ split.
  - intros a Ha Hn. rewrite (K3 a Ha). rewrite Hkeep; [exact (K0 a Ha) | exact Ha | |].
    + intros Hq. apply Hn. left. lia.
    + intros Hq. apply Hn. right. exact Hq.
  - intros a Ha Hv. rewrite (K3 a Ha). rewrite <- (K0 a Ha) in Hv.
    destruct (Z_lt_le_dec a (pf_s1 v - 8192)) as [Hw1 | Hw1];
      [| destruct (Z_lt_le_dec a (pf_s1 v)) as [Hw2 | Hw2]].
    + destruct (Z_le_gt_dec dst a) as [Hd1 | Hd1];
        [destruct (Z_lt_le_dec a (dst + Z.of_nat (S (length (snprintf_s L F_s [AS str]))))) as [Hd2 | Hd2]|].
      * pose proof (Hby (a - dst) ltac:(lia)) as Hb. replace (dst + (a - dst)) with a in Hb by lia.
        rewrite Hb. discriminate.
      * rewrite (Hkeep a Ha) by lia. exact Hv.
      * rewrite (Hkeep a Ha) by lia. exact Hv.
    + apply (aview_some_of_apresent SEGS). apply HPRES2. lia.
    + rewrite (Hkeep a Ha) by lia. exact Hv. }
assert (NI : forall x, 0x10000 <= x < kImgEnd -> ~ Wr x).
{ intros x Hx [Hq | Hq]; unfold off_img, kImgEnd in *; lia. }
assert (NS : forall x, kLowMemEnd <= x < kHighMemBeg -> ~ Wr x).
{ intros x Hx [Hq | Hq]; lia. }
assert (NK : forall x, pf_s1 v <= x < 2 ^ 64 -> ~ Wr x).
{ intros x Hx [Hq | Hq]; lia. }
(* ---- TAIL at fx1 ---- *)
apply (TAIL fx1 v pos lyc Sc Wc (ms_regs ms0) (ms_mem ms0) mdv0 cf cur nm o ln d).
assert (RG3 : forall r w, In (r, w) (L0 ++ LT) -> getr (ms_regs ms0) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r w Hrw. assert (Hr : In r [2; 3; 4; 8; 9; 18; 20; 21; 22; 25; 26]).
  { subst L0 LT. unfold PF_RL in Hrw. cbn [In app] in Hrw |- *.
    repeat (destruct Hrw as [Hq | Hrw]; [injection Hq as <- _; tauto |]). destruct Hrw. }
  rewrite (QK3 r Hr). rewrite (HP2 r).
  - apply QK. cbn [In] in Hr |- *. tauto.
  - unfold acallee_saved. cbn [In] in Hr. lia. }
assert (RG3a : pf_rg (ms_regs ms0) (L0 ++ LT)).
{ apply (pb8bs_rg_tr rX); [apply pb8b_rg_app; [exact HRG0 | exact HRG] | exact RG3]. }
split; [|split; [exact HCTX | split; [exact HN | split]]].
- (* pf_base at the line scope *)
  split; [exact HCX|].
  split.
  { split; [exact HJ2|]. split; [exact Hly|]. split; [exact HSc|]. split; [exact HPERM|].
    split.
    { intros j r Hj. assert (Hj13 : (j < 13)%nat)
        by (change 13%nat with (length PF_SAVED); apply nth_error_Some; rewrite Hj; discriminate).
      rewrite (pb8b_kp_rdword Wr rd0 rd3 KP); [exact (HSAV j r Hj) | lia | lia |].
      intros k Hk. apply NK. lia. }
    split.
    { rewrite (pb8b_kp_rdword Wr rd0 rd3 KP); [exact HFLAG | change (fs_frame_bytes 5) with 2048; lia
        | change (fs_frame_bytes 5) with 2048; lia |].
      intros k Hk [Hq | Hq]; [apply (HdFL (pf_F v pos + fs_frame_bytes 5 - 8 + k)); [change (fs_frame_bytes 5) with 2048 in *; lia | exact Hq]
        | change (fs_frame_bytes 5) with 2048 in *; lia]. }
    split; [exact (fxrel_frm0 fx fx1 HFRM Hfx)|].
    split; [exact HTF|].
    split.
    { unfold pf_sl in *. apply Forall_cons; [|apply Forall_nil]. apply Forall_inv in HC8. cbn [fst snd] in *.
      rewrite (pb8b_kp_rdword Wr rd0 rd3 KP); [exact HC8 | lia | lia | intros k Hk; apply NK; lia]. }
    apply (pb8b_rg_sub _ _ _ RG3a). intros x Hx. apply in_or_app. left. exact Hx. }
  split.
  { apply (pb8b_kp_obj Wr rd0 rd3 KP NI NS v lyc Sc HOBJ Htceil ltac:(lia)).
    intros x Hx [Hq | Hq]; [exact (HdT x Hx Hq) | unfold pf_len in *; lia]. }
  split.
  { unfold pf_sl in *. rewrite Forall_forall in *. intros ov Hov.
    pose proof (pb8b_PF_SL_offs v pos ov Hov) as Ho.
    rewrite (pb8b_kp_rdword Wr rd0 rd3 KP); [exact (HSL0 ov Hov) | lia | lia | intros k Hk; apply NK; lia]. }
  intros i Hi. rewrite (pb8b_kp_byte Wr rd0 rd3 KP); [exact (HFSH i Hi) | lia | apply NS; lia].
- (* pf_st: what the piece says the call leaves *)
  apply HPOST.
  + intros k Hk. pose proof (K3 (dst + Z.of_nat k) ltac:(lia)) as E3. unfold rd3 in E3. rewrite E3.
    pose proof (Hby (Z.of_nat k) ltac:(lia)) as Hk'. rewrite Nat2Z.id in Hk'. exact Hk'.
  + intros a Ha Hd Hw. pose proof (K3 a Ha) as E3. unfold rd3 in E3. rewrite E3, (Hkeep a Ha Hd Hw).
    exact (K0 a Ha).
- (* the registers *)
  apply (pb8b_rg_sub _ _ _ RG3a). intros x Hx. apply in_or_app. right. exact Hx.
Qed.
End x.
End e.
End f.
End d.
