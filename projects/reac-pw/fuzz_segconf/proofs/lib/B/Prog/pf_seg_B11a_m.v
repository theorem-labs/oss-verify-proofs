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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 414 of its 496 lines of code are new or changed and 4971 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/pf_seg_B2.v; 120 of its 214 lines of code are new or changed and 402 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the MODEL piece of
   segment B11a of reac_segconf_parse_file's walk, b11_model_ok : B11_CHK_stmt n -> H_MODEL n
   (lib/B/Prog/pf_seg_B11a_k.v, lib/B/Prog/pf_pieces.v). The B11a segment lane of the image-B G3 walk owner, 2026-10-30.
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk, segment B11a's entry MODEL -> CHK).
   ADAPTED from a working branch + U piece walks; the run and the rebuild of the cut are the
   B10b segment lane's pf_seg_B10b_j.v form (a PLAIN run that writes frame shadow cells through s5, the cells read back from
   the region, every other byte kept).
   The code (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s), MODEL 0x886d4 .. 0x886dc, 3 instructions, no
   call, no inline check, no UBSan trap:
     0x886d4 sb zero,92(s5); 0x886d8 sb zero,93(s5); 0x886dc sb zero,94(s5)   model low's three shadow cells
                                                                               0x5c .. 0x5e to 0: in scope
   then CHK 0x886e0. The spine step: with key <> "role" and key = "model", SegModel.r_key's model branch is
   b11_step (pf_seg_B11a_f.v b11f_r_key), so H_MODEL's post is b11_post. No Section hypothesis. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B11a_k pf_seg_B11a_g
  pf_seg_B11a_f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- small tools (pf_seg_B10b_j.v's, from the image-A A2 segment lane's pf_a2.v) ---------- *)
Lemma b11m_den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma b11m_zrange : forall (f : Z -> bool) lo (n : nat),
  forallb (fun k => f (lo + Z.of_nat k)) (seq 0 n) = true -> forall i, lo <= i < lo + Z.of_nat n -> f i = true.
Proof.
intros f lo n H i Hi. rewrite forallb_forall in H.
specialize (H (Z.to_nat (i - lo)) ltac:(apply in_seq; lia)).
replace (lo + Z.of_nat (Z.to_nat (i - lo))) with i in H by lia. exact H.
Qed.
Ltac b11m_in := cbn [In app]; repeat first [left; reflexivity | right].
Ltac b11m_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Ltac b11m_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.
Lemma b11m_set_fs_id : forall s, set_fs (st_fs s) s = s.
Proof. intros s. destruct s. reflexivity. Qed.
(* model low's three cells: 0x00 in PF_SC_L146, 0xf8 in PF_SC_LINE; every other cell the same in both *)
Lemma b11m_shb_l146 : forall i, 0x5c <= i < 0x5f -> pf_shb PF_SC_L146 i = 0.
Proof.
intros i Hi. apply Z.eqb_eq. revert i Hi.
apply (b11m_zrange (fun i => pf_shb PF_SC_L146 i =? 0) 0x5c 3). vm_compute. reflexivity.
Qed.
Lemma b11m_shb_same : forall i, ~ (0x5c <= i < 0x5f) -> pf_shb PF_SC_LINE i = pf_shb PF_SC_L146 i.
Proof.
intros i Hi. unfold pf_shb, PF_SC_LINE, PF_SC_L146. cbn [sc_cn sc_buf sc_low sc_l146 sc_known].
destruct (i <? 4); [reflexivity|]. destruct (i <? 6); [reflexivity|]. destruct (i <? 8); [reflexivity|].
destruct (i <? 72); [reflexivity|]. destruct (i <? 80); [reflexivity|]. destruct (i <? 88); [reflexivity|].
destruct (i <? 92) eqn:E92; [reflexivity|]. destruct (i <? 95) eqn:E95; [|reflexivity].
apply Z.ltb_ge in E92. apply Z.ltb_lt in E95. lia.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.

(* ---------- reading a region the run wrote (pf_a2.v) ---------- *)
Definition b11m_cell_ok (cs : list YP09.chunk) (od v : Z) : bool :=
  existsb (fun c => match YP09.c_val c with
    | CVal w (SLit z) => (YP09.c_off c =? od) && (N.eqb w 1) && (bv_unsigned (byte_of_word (Z_to_bv 64 z) 0) =? v)
    | _ => false end) cs.
Lemma b11m_cell_of_region : forall E H m n b lo hi wlo whi cs od v,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> b11m_cell_ok cs od v = true -> aview SEGS H m (b + od) = Some v.
Proof.
intros E H m n b lo hi wlo whi cs od v HR Hb Hc.
apply existsb_exists in Hc as (c & Hin & Hc).
destruct c as [o [w e | | | ]]; cbn [YP09.c_val YP09.c_off] in Hc; try discriminate.
destruct e; try discriminate.
apply andb_prop in Hc as [Hc Hv]. apply andb_prop in Hc as [Ho Hw].
apply Z.eqb_eq in Ho. apply N.eqb_eq in Hw. apply Z.eqb_eq in Hv. subst o w.
unfold region_ok in HR. cbv zeta in HR. cbn [YP09.r_base YP09.r_chunks base_val] in HR.
destruct HR as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck.
destruct (Hck 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2). cbn [cbyte YP09.c_val YP09.c_off sv_denot] in Hb1, Hb2.
injection Hb1 as <-. rewrite Hb, Z.add_0_r in Hb2.
unfold aview. rewrite Hb2. cbn [option_map]. rewrite Hv. reflexivity.
Qed.

(* ---------- the seed at MODEL (0x886d4) ---------- *)
(* every register its own atom; model low's three shadow cells writable on s5's atom (x21 = SH, PF_RL) *)
Definition b11m_regions : smem := [YP09.mkRegion (Some 21%nat) 0x5c 0x5f 0x5c 0x5f []].
Definition b11m_ss : sstate := mkSS B11_MODEL sr_atoms b11m_regions None (mkFacts [] [] []).

Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let b11m_RUNTO := SRr_run_to_pi_AJ (fx := fx) B LAWS.

Lemma b11m_seed : forall v pos (Wc : world SEGS) (rX : bvmap 5 word) memc,
  b11_G v pos ->
  getr rX (Z_to_bv 5 21) = w64 (pf_SH v pos) ->
  (forall i, 0 <= i < 256 -> apresent (w_H Wc) memc (pf_SH v pos + i)) ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [])) b11m_ss
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + B11_MODEL)) memc (seg_rom SEGS))).
Proof.
intros v pos Wc rX memc HG R21 Hsh.
destruct (b11_SHb v pos HG) as (ESH & SH1 & SH2 & F8).
pose proof asan_consts as (C1 & _).
set (E := Eimg (Ereg rX [])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U21 : bv_unsigned (ew E 21) = pf_SH v pos)
  by (rewrite (EE 21%nat (Z_to_bv 5 21) eq_refl), R21; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold b11m_ss. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold b11m_regions. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U21. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hsh. lia.
- cbn. tauto.
- unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor].
Qed.

(* ---------- the piece: MODEL -> CHK ---------- *)
Lemma b11m_model : forall n, B11_CHK_stmt (fx := fx) B n -> H_MODEL (fx := fx) B n.
Proof.
intros n CHK v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val HI Hrole Hmodel.
destruct HI as (HBASE & HMID & HST & HKV & HSL70 & HRG).
pose proof (b11_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HBASE) as (HG & Hin & EF & Hfrs & HAR & Hly & _ & Hsh).
pose proof HG as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
destruct (b11_SHb v pos HG) as (ESH & SH1 & SH2 & F8).
pose proof HBASE as (HCX & HFI & HOBJ & HSL & HFSH).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & HFRM & _ & _ & HRG0).
pose proof asan_consts as (C1 & _).
(* the post: r_key's model branch is b11_step (b11f_r_key) *)
destruct HKV as (Hsplit & _ & _ & HSTRV & HINBV).
rewrite (b11f_r_key cf gi nm (pf_tline (p_s v) o) key val (ln + 1) Hsplit Hrole Hmodel).
change (pf_postm B v (b11_step cf gi nm val ln) o ln) with (b11_post B v cf gi nm val o ln).
unfold PF_RL, PF_RM in HRG.
assert (R21 : getr rX (Z_to_bv 5 21) = w64 (pf_SH v pos)) by (apply (b11_rg_get rX _ 21 _ HRG); b11m_in).
pose proof (b11m_seed v pos Wc rX memc HG R21 Hsh) as HS.
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n0 r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U21 : bv_unsigned (ew E 21) = pf_SH v pos)
  by (rewrite (EE 21%nat (Z_to_bv 5 21) eq_refl), R21; unfold w64; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 (BASE + PF_MODEL)) with (Z_to_bv 64 (BASE + B11_MODEL)).
(* 0x886d4 .. 0x886dc: the three shadow stores, up to CHK *)
paj_run_to_sh b11m_RUNTO HS HJ B11_CHK.
{ intros a (r & Hr & Ha). unfold b11m_ss, b11m_regions in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  right; right; right; left. exists 5, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
  rewrite EF. change (fs_frame_bytes 5 / 8) with 256. change (shadow_addr (pf_F v pos)) with (pf_SH v pos).
  rewrite U21 in Ha. lia. }
cbn [ms_mem mkst] in HFr, HG0, HF.
b11m_clear_md.
(* what the run kept and what it wrote *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_SH v pos + 0x5c <= a < pf_SH v pos + 0x5f) ->
    rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. apply (kept_of_frame (segs:=SEGS) E (ss_mem b11m_ss) (w_H Wc) memc (ms_mem ms)
    (fun a => pf_SH v pos + 0x5c <= a < pf_SH v pos + 0x5f) HFr); [|exact Ha | exact Hn].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. cbv beta.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U21 in Hrr; lia |]).
  destruct Hin'. }
assert (M1 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG0 Hv)).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H Wc) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
cbn [ms_mem restrict] in HR0.
assert (C3 : forall i, 0x5c <= i < 0x5f -> rdW Wc (ms_mem ms) (pf_SH v pos + i) = Some 0).
{ intros i Hi. apply (b11m_cell_of_region E (w_H Wc) (ms_mem ms) 21 _ _ _ _ _ _ i _ HR0 U21). revert i Hi.
  apply (b11m_zrange (fun i => b11m_cell_ok _ i 0) 0x5c 3). vm_compute. reflexivity. }
assert (KP : b11_kept v pos true None (rdW Wc memc) (rdW Wc (ms_mem ms))).
{ split.
  - intros a Ha Hn. apply K1; [exact Ha|]. intros Hw. apply Hn. unfold b11_Wr. right; right; left. split; [reflexivity | exact Hw].
  - intros a _ Hv. exact (M1 a Hv). }
(* the registers at CHK: every register the cut's *)
assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [b11m_rreg HS; rewrite b11m_den_atom0; apply EE; reflexivity |]). destruct Hr. }
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
  change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + B11_CHK) rg mm mdx) end.
apply (CHK v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv cf nm o ln d gi vp val).
assert (HC5 : sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE) by (destruct HOBJ as (_ & _ & _ & _ & H5 & _); exact H5).
split; [split; [|split; [exact HMID|split; [|split; [|split]]]]|].
- (* pf_base at PF_SC_L146 *)
  apply (b11_move B fx v pos lyc Sc Wc rX memc mdc PF_SC_LINE Sc Wc (ms_regs ms) (ms_mem ms) mdv PF_SC_L146 true None
    HBASE I HJ ltac:(exists (st_fs Sc); symmetry; apply b11m_set_fs_id) (Permutation_refl _) KP).
  + unfold pf_rg, b11_FI. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
      (rewrite QK; [apply (b11_rg_get rX _ _ _ HRG0); b11m_in | b11m_in]).
  + exact HFRM.
  + intros i Hi. destruct (Z_lt_le_dec i 0x5c) as [Hlo | Hlo]; [|destruct (Z_lt_le_dec i 0x5f) as [Hhi | Hhi]].
    * rewrite K1 by lia. rewrite <- b11m_shb_same by lia. exact (HFSH i Hi).
    * rewrite (C3 i ltac:(lia)). rewrite b11m_shb_l146 by lia. reflexivity.
    * rewrite K1 by lia. rewrite <- b11m_shb_same by lia. exact (HFSH i Hi).
- (* pf_st *)
  destruct HST as (HRC & HCUR & HNM & HCNT & HC0).
  split; [exact (b11_keep_rconf B v pos lyc Sc Wc memc mdc true _ _ _ HG HAR Hin EF KP HC5 HRC)|].
  split; [exact HCUR|]. split; [exact (b11_keep_nm v pos true None _ _ nm HG I KP HNM)|]. split; [exact HCNT|].
  exact (b11_keep_slot v pos true None _ _ 0xc0 _ HG I KP ltac:(lia) HC0).
- exact (b11_keep_buf_str v pos true None _ _ vp val HG I KP HINBV HSTRV).
- exact HINBV.
- apply (b11_keep_sl v pos true None _ _ _ HG I KP); [|exact HSL70]. intros ov [<- | []]. cbn [fst]. lia.
- unfold pf_rg, PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    (rewrite QK; [apply (b11_rg_get rX _ _ _ HRG); b11m_in | b11m_in]).
Qed.
End x.

(* the piece at every FP state *)
Theorem b11_model_ok : forall (fx : YK11.FPState) (n : nat), B11_CHK_stmt (fx := fx) B n -> H_MODEL (fx := fx) B n.
Proof. intros fx n H. exact (b11m_model (fx := fx) n H). Qed.
End d.
