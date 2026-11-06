(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW8Geo.v at 888d1ffb4c3; module paths fuzz_role -> fuzz_headamp, RPgBase / RPgCSpec / RPgImgA / RPgMem / RPgSeg -> HPgBase / HPgCSpec / HPgImgA / HPgMem / HPgSeg, the rl_ / rm_ / rs_ prefixes -> hd_ / hm_ / hs_; the frame for locals is class 4 (1024 bytes, 128 shadow bytes), the real frame 0x1e0 bytes; hd_seg_pre's pp facts come from its hd_fresh_block conjunct and its R alignment is 32. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgMem HPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgW8Kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Arguments x_STK {segs} h. #[local] Arguments x_sp0 {segs} h. #[local] Arguments x_FP {segs} h.
#[local] Arguments x_ly {segs} h. #[local] Arguments x_S {segs} h. #[local] Arguments x_W0 {segs} h.
#[local] Arguments x_mem0 {segs} h. #[local] Arguments x_md0 {segs} h. #[local] Arguments x_own {segs} h.
#[local] Arguments x_k {segs} h. #[local] Arguments x_regs {segs} h. #[local] Arguments x_lyc {segs} h.
#[local] Arguments x_Sc {segs} h. #[local] Arguments x_W {segs} h. #[local] Arguments x_memc {segs} h.
#[local] Arguments x_mdc {segs} h. #[local] Arguments x_RLO {segs} h. #[local] Arguments x_RHI {segs} h.
#[local] Arguments x_e {segs} h. #[local] Arguments x_pos {segs} h.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* a register / an R-relative cell of a cut list, by membership *)
Lemma wg_reg : forall segs H mem (regs : bvmap 5 word) e L r v,
  Forall (fun f => hd_at segs H mem regs e (fst f) (snd f)) L -> In (LReg r, v) L ->
  getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros segs H mem regs e L r v HF Hin. exact (proj1 (Forall_forall _ _) HF _ Hin). Qed.
Lemma wg_cell : forall segs H mem (regs : bvmap 5 word) e L o v,
  Forall (fun f => hd_at segs H mem regs e (fst f) (snd f)) L -> In (LCell XR o, v) L ->
  val_mem segs (mrestrict H mem) (e_R e + o) 8 (v mod 2 ^ 64).
Proof. intros segs H mem regs e L o v HF Hin. exact (proj1 (Forall_forall _ _) HF _ Hin). Qed.
Ltac wg_in := unfold hs_Rc, hs_Rc0, hs_L_Dc, hs_L_Dc0, hs_Kc; cbn [app];
  repeat (first [left; reflexivity | right]); fail.

(* the pods ent[] records at a cut inside the params Struct: at most 32, each well formed *)
Lemma wg_pc_ents : forall sh ps es,
  Forall (fun kv => pval_wf (snd kv)) ps -> Forall ent_wf (all_ents ps) -> Forall ent_wf es ->
  (length es <= 32)%nat ->
  (length (pc_ents (PbCut sh ps (Some es))) <= 32)%nat /\ Forall ent_wf (pc_ents (PbCut sh ps (Some es))).
Proof.
intros sh ps es Hp Ha He Hl. unfold pc_ents, first_params. cbn [pc_props pc_open].
destruct (find _ ps) as [[k v]|] eqn:E; cbn [option_map snd].
- apply find_some in E as [Hin _].
  destruct v as [z|es'].
  + split; [cbn; lia | constructor].
  + split.
    * exact (proj1 (Forall_forall _ _) Hp _ Hin).
    * apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) Ha). unfold all_ents.
      apply in_flat_map. exists (k, PStruct es'). split; [exact Hin | exact Hx].
- split; assumption.
Qed.

(* ent[] is es when no params property is among ps *)
Lemma wg_pc_ents_first : forall sh ps es, hs_first ps = 1 -> pc_ents (PbCut sh ps (Some es)) = es.
Proof.
intros sh ps es H1. unfold hs_first in H1. destruct (existsb _ ps) eqn:Ex; [cbn in H1; discriminate H1|].
unfold pc_ents, first_params. cbn [pc_props pc_open].
destruct (find _ ps) as [kv|] eqn:E; [|reflexivity].
exfalso. apply find_some in E as [Hin Hk].
pose proof (proj2 (existsb_exists (fun kv : Z * pval => fst kv =? POD_PROP_PARAMS) ps)
  (ex_intro _ kv (conj Hin Hk))) as Ex'. congruence.
Qed.

(* what a journal state of the piece gives about pp, the frame F and their shadow bytes *)
Lemma w8_now : forall STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W mem md k pp F pos,
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W mem md k ->
  In (pp, Layout.PP_SIZE) (ablocks B ly2 S2) -> In (4, pos) (frames S2) -> frame_addr ly2 4 pos = F ->
  (forall i, 0 <= i < 2468 -> aview rsegs (w_H W) mem (shadow_addr pp + i) = Some 0) /\
  (forall i, 0 <= i < 19744 -> apresent (w_H W) mem (pp + i)) /\
  (forall i, 0 <= i < 1024 -> apresent (w_H W) mem (F + i)) /\
  (forall i, 0 <= i < 128 -> apresent (w_H W) mem (shadow_addr F + i)) /\
  (forall a n, pp <= a -> a + n <= pp + 19744 ->
     range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF a n /\
     (0 < n -> shadow_hull_vis (aview rsegs (w_H W) mem) a n)) /\
  (forall o n, 0xf0 <= o -> o + n <= 0x158 -> 0 < n -> shadow_hull_vis (aview rsegs (w_H W) mem) (F + o) n).
Proof using B MT.
intros STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W mem md k pp F pos HJ Hpp Hfr HF.
destruct HJ as [HAR _]. subst F.
destruct (al_blocks _ _ (YG0q.AR_laws_ok rsegs B) ly2 S2 W mem md pp Layout.PP_SIZE HAR Hpp)
  as (_ & _ & _ & _ & Hpres & _).
destruct (al_shadow _ _ (YG0q.AR_laws_ok rsegs B) ly2 S2 W mem md pp Layout.PP_SIZE HAR Hpp)
  as [(_ & _ & Hsh) _].
destruct (al_frames _ _ (YG0q.AR_laws_ok rsegs B) ly2 S2 W mem md 4 pos HAR Hfr) as (Fal & _ & Fpres & Fsh).
change (req_size Layout.PP_SIZE) with 19744 in Hpres, Hsh.
change (fs_frame_bytes 4) with 1024 in Fpres, Fsh. change (1024 / 8) with 128 in Fsh.
change ((19744 + 7) / 8) with 2468 in Hsh. change (19744 / 8) with 2468 in Hsh.
split.
{ intros i Hi. specialize (Hsh i Hi).
  replace (i <? 2468) with true in Hsh by (symmetry; apply Z.ltb_lt; lia).
  exact Hsh. }
split.
{ intros i Hi. exact (proj1 (Hpres (pp + i) ltac:(lia))). }
split.
{ intros i Hi. exact (proj1 (Fpres (frame_addr ly2 4 pos + i) ltac:(lia))). }
split.
{ intros i Hi. exact (proj1 (Fsh i ltac:(lia))). }
split.
{ intros a n Ha Hn. apply (hm_blk_ra rsegs B ly2 S2 W mem md pp Layout.PP_SIZE a n HAR Hpp Ha).
  change (req_size Layout.PP_SIZE) with 19744. lia. }
intros o n Ho Hn Hn0 s Hs. apply (aview_some_of_apresent rsegs).
remember (frame_addr ly2 4 pos) as F eqn:EF.
assert (Hb : shadow_addr F <= s < shadow_addr F + 128).
{ unfold shadow_addr, SHADOW_OFF in *. clear - Fal Ho Hn Hn0 Hs. Z.div_mod_to_equations. lia. }
replace s with (shadow_addr F + (s - shadow_addr F)) by lia.
exact (proj1 (Fsh (s - shadow_addr F) ltac:(lia))).
Qed.

(* what the cut J (with the segment's start record) gives the piece's first block and the calls *)
Lemma w8_J_facts : forall cx rest sh np ps cnt es rr r ed ly2 S2 W2 regs2 mem2 md2,
  hs_start_M01 rsegs B cx rest ->
  hs_cut_J rsegs B MT cx sh np ps cnt es rest rr r ed ly2 S2 W2 regs2 mem2 md2 ->
  let e := x_e cx in
  let L := Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) in
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem2 md2 (x_k cx) /\
  In (e_pp e, Layout.PP_SIZE) (ablocks B ly2 S2) /\ ~ In (e_pp e, Layout.PP_SIZE) (ablocks B (x_ly cx) (x_S cx)) /\
  In (4, x_pos cx) (frames S2) /\ frame_addr ly2 4 (x_pos cx) = e_F e /\
  getr regs2 2 = w64 (e_R e) /\ getr regs2 3 = w64 (as_gp B) /\ getr regs2 4 = w64 (as_tp B) /\
  getr regs2 9 = w64 (e_R e) /\ getr regs2 19 = w64 (shadow_addr (e_F e)) /\
  getr regs2 20 = w64 (shadow_addr (e_pp e + 0x4000)) /\ getr regs2 21 = w64 (e_pp e + 0x4000) /\
  getr regs2 23 = w64 SHADOW_OFF /\ getr regs2 27 = w64 (e_pp e) /\
  Forall (fun c => val_mem rsegs (mrestrict (w_H W2) mem2) (e_R e + fst c) 8 (snd c mod 2 ^ 64))
    (wslot_vals (e_F e) (e_pp e) (hs_first ps) (Z.of_nat (length es)) cnt) /\
  hm_bytes rsegs (w_H W2) mem2 (e_F e + 0xf0) (ent_mem ed) /\
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_F e + 0xf0) 4 (e_type ed) /\
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_F e + 0xf4) 4 (e_size ed) /\
  hm_bytes rsegs (w_H W2) mem2 (e_pp e) (pc_image (PbCut sh ps (Some es))) /\
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_pp e + 0x4000) 8 L /\
  (hs_first ps = 1 -> val_mem rsegs (mrestrict (w_H W2) mem2) (e_pp e + 0x4d14) 4 (Z.of_nat (length es))) /\
  hd_fsh rsegs (w_H W2) mem2 (e_F e) hs_PJ /\
  e_pp e mod 16 = 0 /\ in_app (e_pp e) 19744 /\ e_pp e + 19744 <= alloc_ceiling /\
  e_F e mod 32 = 0 /\ in_app (e_F e) 1024 /\ e_F e + 1024 <= alloc_ceiling /\
  (e_pp e + 19744 <= e_F e \/ e_F e + 1024 <= e_pp e) /\
  alloc_ceiling + T_SEG_STK <= e_R e /\ e_R e mod 16 = 0 /\ e_R e + 0x1e0 <= x_sp0 cx /\
  x_sp0 cx mod 16 = 0 /\ x_sp0 cx <= 2 ^ 47 /\ x_sp0 cx - x_STK cx <= e_R e - T_SEG_STK /\
  0 <= L <= 5384 /\ L mod 8 = 0 /\ ent_wf ed /\
  (length es < 32)%nat /\ Z.of_nat (length es) < cnt /\ cnt <= 32 /\
  (hs_first ps = 0 \/ hs_first ps = 1) /\
  hs_first ps = Z.b2z (pc_first (PbCut sh ps (Some es))) /\
  Forall (fun kv => pval_wf (snd kv)) ps /\ Forall ent_wf (all_ents ps) /\ Forall ent_wf es /\ (length ps <= 2)%nat.
Proof.
intros cx rest sh np ps cnt es rr r ed ly2 S2 W2 regs2 mem2 md2 HS HJ e L. subst e L.
destruct HS as (Hpre & _ & _ & _).
unfold hs_pre, hd_seg_pre in Hpre.
destruct Hpre as (HJ0 & _ & Hr2 & Hr3 & Hr4 & HeS & HRal & HRsz & HRstk & Hown & HeF & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & (_ & Hppc & Hppn)).
unfold hs_cut_J, hs_pod_base, hs_core, hs_mid in HJ.
destruct HJ as (((HJ2 & Hregs & Hfr & Hperm & _ & _ & _) & _ & _ & _ & Hwfs & _ & _ & _ & _ & _ & _ & _ & _ &
  Hps2 & Hcnt & Hes & Hes32 & Hescnt) & Hat & Hfsh & Hpp & He & _ & Hwf).
destruct HJ0 as (_ & Hly0 & _ & _ & _ & Hfr0 & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
pose proof HJ2 as (HAR2 & Hly2 & _).
unfold hs_at_cx, hs_at in Hat.
assert (Hpp2 : In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B ly2 S2))
  by exact (Permutation_in _ (Permutation_sym Hperm) Hppc).
assert (Hfr2 : In (4, x_pos cx) (frames S2)) by (rewrite Hfr, Hfr0; apply in_or_app; left; exact Hown).
assert (HFeq : frame_addr ly2 4 (x_pos cx) = e_F (x_e cx)).
{ rewrite HeF. unfold frame_addr. destruct Hly2 as (_ & _ & _ & _ & _ & EF2 & _).
  destruct Hly0 as (_ & _ & _ & _ & _ & EF0 & _). rewrite EF2, EF0. reflexivity. }
destruct (al_blocks _ _ (YG0q.AR_laws_ok rsegs B) ly2 S2 W2 mem2 md2 _ _ HAR2 Hpp2) as (Bal & _ & Bceil & Bapp & _).
destruct (al_frames _ _ (YG0q.AR_laws_ok rsegs B) ly2 S2 W2 mem2 md2 _ _ HAR2 Hfr2) as (Fal & Fapp & _).
destruct (frames_bounds rsegs B (YG0q.AR_laws_ok rsegs B) ly2 S2 W2 mem2 md2 _ _ HAR2 Hfr2) as (_ & Fceil & _).
pose proof (sep_block_frame rsegs B (YG0q.AR_laws_ok rsegs B) ly2 S2 W2 mem2 md2 _ _ _ _ HAR2 Hpp2 Hfr2) as Hdis.
rewrite HFeq in Fal, Fapp, Fceil, Hdis.
change (req_size Layout.PP_SIZE) with 19744 in Bceil, Bapp, Hdis.
change (fs_frame_bytes 4) with 1024 in Fapp, Fceil, Hdis.
unfold zdisjoint in Hdis. cbn [fst snd] in Hdis.
destruct Hstk as (Ssp & _ & Slo & Slosp & Shi & Shi47 & _).
change (hi_rsz headamp_himg_A) with 0x1e0 in HRsz.
destruct Hwfs as (_ & Hpsw & Hall & _).
assert (Hpw : Forall (fun kv => pval_wf (snd kv)) ps)
  by (eapply Forall_impl; [|exact Hpsw]; intros kv [_ Hk]; exact Hk).
destruct (pc_buf_len_open sh ps es Hpw Hall Hes) as [HL Hdiv].
destruct (wg_pc_ents sh ps es Hpw Hall Hes ltac:(lia)) as [Hent32 Hentwf].
assert (Hbody : Forall (fun e => (length (e_body e) <= 96)%nat) (pc_ents (PbCut sh ps (Some es))))
  by (eapply Forall_impl; [|exact Hentwf]; intros x (_ & Hx1 & Hx2); lia).
assert (Hb : Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) <= POD_BUF_MAX) by (unfold POD_BUF_MAX; lia).
assert (Hpp' : hm_bytes rsegs (w_H W2) mem2 (e_pp (x_e cx)) (pc_image (PbCut sh ps (Some es)))) by exact Hpp.
unfold pc_image in Hpp'.
assert (He' : hm_bytes rsegs (w_H W2) mem2 (e_F (x_e cx) + 0xf0) (ent_mem ed)) by exact He.
assert (Hlen_e : (8 <= length (ent_mem ed))%nat) by (unfold ent_mem, le32; cbn [length app Z_to_le_bytes]; lia).
pose proof (hm_bytes_field rsegs (w_H W2) mem2 _ _ 0 4 (e_type ed) He' eq_refl ltac:(lia)) as Hty.
pose proof (hm_bytes_field rsegs (w_H W2) mem2 _ _ 4 4 (e_size ed) He' eq_refl ltac:(lia)) as Hsz.
split; [exact HJ2|].
split; [exact Hpp2|].
split; [exact Hppn|].
split; [exact Hfr2|].
split; [exact HFeq|].
split; [exact (eq_trans (Hregs 2 (or_introl eq_refl)) Hr2)|].
split; [exact (eq_trans (Hregs 3 (or_intror (or_introl eq_refl))) Hr3)|].
split; [exact (eq_trans (Hregs 4 (or_intror (or_intror eq_refl))) Hr4)|].
split; [apply (wg_reg _ _ _ _ _ _ 9 _ Hat); wg_in|].
split; [apply (wg_reg _ _ _ _ _ _ 19 _ Hat); wg_in|].
split; [apply (wg_reg _ _ _ _ _ _ 20 _ Hat); wg_in|].
split; [apply (wg_reg _ _ _ _ _ _ 21 _ Hat); wg_in|].
split; [apply (wg_reg _ _ _ _ _ _ 23 _ Hat); wg_in|].
split; [apply (wg_reg _ _ _ _ _ _ 27 _ Hat); wg_in|].
split.
{ unfold wslot_vals.
  repeat (apply Forall_cons; [cbn [fst snd]; apply (wg_cell _ _ _ _ _ _ _ _ Hat); wg_in |]).
  apply Forall_nil. }
split; [exact He|].
split; [replace (e_F (x_e cx) + 0xf0) with (e_F (x_e cx) + 0xf0 + Z.of_nat 0) by lia; exact Hty|].
split; [replace (e_F (x_e cx) + 0xf4) with (e_F (x_e cx) + 0xf0 + Z.of_nat 4) by lia; exact Hsz|].
split; [exact Hpp|].
split; [exact (hm_pp_len rsegs _ _ _ _ _ _ Hb Hent32 Hbody _ _ _ Hpp')|].
split.
{ intros H1. pose proof (hm_pp_n_ent rsegs _ _ _ _ _ _ Hb Hent32 Hbody _ _ _ Hpp') as X.
  rewrite (wg_pc_ents_first sh ps es H1) in X. exact X. }
split; [exact Hfsh|].
split; [exact Bal|]. split; [exact Bapp|]. split; [lia|].
split; [exact Fal|]. split; [exact Fapp|]. split; [lia|].
split; [exact Hdis|].
split; [lia|].
split; [apply Z.mod_divide in HRal; [|lia]; destruct HRal as [q Hq]; rewrite Hq;
  replace (q * 32) with ((2 * q) * 16) by ring; apply Z_mod_mult|].
split; [lia|].
split; [exact Ssp|].
split; [lia|].
split; [exact HRstk|].
split; [lia|].
split; [apply (proj2 (Z.mod_divide _ 8 ltac:(discriminate))); exact Hdiv|].
split; [exact Hwf|].
split; [exact Hes32|].
split; [exact Hescnt|].
split; [lia|].
split; [unfold hs_first; destruct (negb _); [right|left]; reflexivity|].
split; [reflexivity|].
split; [exact Hpw|].
split; [exact Hall|].
split; [exact Hes|].
exact Hps2.
Qed.
End w.
