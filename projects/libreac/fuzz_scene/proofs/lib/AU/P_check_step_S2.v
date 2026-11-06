(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AChf.v, with its module paths, module names and addresses changed; 145 of its 210 lines of code are new or changed and 301 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/A/P_check_step_S0.v, with its module paths and module names changed; 603 of its 652 lines of code are new or changed and 161 lines of the source are left out. *)
(* Segment S2 of the ASan walk of check_step in fuzz_scene.asan-ubsan (sha256
   e98b1ed286c1aa5c3d558cb2069011d2413d58b2122f741531364382a528833f): 0x835c4 .. 0x8362c, proved (rule 24: no
   function proved; this lane proves ONE segment lemma of the walk against the cut statement of
   P_check_step_cut.v, with the callees as Section hypotheses).
   Pre: cs_st2 at 0x835c4; post: cs_st3 at 0x8362c.
   The three arms of k: k = 0 (payload bcmp(blk + 9, body, 24)), 1 <= k <= 341 (bcmp(blk + 7, body + scene_off k,
   26)) and k = 342 (bcmp(blk + 7, body + 8890, 14) and then the trailer bcmp(blk + 21, check_step.trailer, 12)
   at 0x83624). Every call goes through s2_bcmp (aj_bcmp_at, AU/YCbq.v:2062, lib.AU's YCbq per gate 6o) at
   check_step's own frame sp0 - 128; the `bnez a0` after each call is refuted from `v = w64 0 <-> bytes equal`
   and the block's bytes (s2_payload_nth / s2_trailer_nth of P_check_step_S2_aux.v).
   The UBSan guards: 0x835d8 (~blk <u 7/9) and, on the k = 0 / k = 342 arms, 0x835e0 (~body <u off) by
   kill_not_trap (lib/AU/U_NotTrap.v, at bcd4b91d8d9); on the 1 <= k <= 341 arm the
   second guard compares against the off atom, so kill_not_trap_atom (below) closes it from
   0 <= body /\ body + scene_off k < 2 ^ 64. 0x83604 and 0x83610 are decided in the run from the blk atom's
   range fact. Donor: the addframe walk's bcmp (cgif A/ACkh.v:33 tfibX_ABCMP, A/ACjf.v:152). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YCbq.  (* image-specific: lib.AU (gate 6o) *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaRun PaShadow SceneSyms SceneList ScenePa.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaJournal ScenePaLib SceneBase SceneRo SceneFrame YC1h YC85.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import YC1g YC4b YC45.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import U_NotTrap.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneBlock RcModel RcParse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import P_reac_ctrl_checksum_verify P_reac_ctrl_parse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_check_step_frame P_check_step_cut P_check_step_S2_aux.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The sink head is an explicit Section Context the glue instantiates with scene's own (a Theorem Labs lane 22:57Z): never chosen by
   instance search (a global src0_sink_head comes into scope with the relocated core's YI5b). *)
Context (SK : YI16.sink_head). #[local] Existing Instance SK.
Section f.
Context {PI : PAImg scene_listing}.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ scene_listing PI).
Section h.
Variable B : asyms.
(* A Theorem Labs lane: the read-only range stays below the sink's overflow head (cgif A/ACeh.v ro_tfa_below_ofl). *)
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
(* relocated laws and the glue's bindings (cgif A/ACk1.v:64-74, :82; ScenePaLib.v:307, SceneFrame.v:96). *)
(* LAWS and SMP are theorems, not hypotheses (an internal review, CHECKSTEP-REVIEW item R4): AR_laws_ok (Reusable/YG0q.v:803) and
   the model law ml_stack_malloc_progress (YG0d.v:520-521). The UAR flag reads 1 in every AR state by
   al_const (AR_const_law, YG0d.v:461-467), so no flag hypothesis is taken. *)
Hypothesis ML : model_laws (as_universe B).
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let SMP : stack_malloc_progressP B := ml_stack_malloc_progress _ ML.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
(* A Theorem Labs lane. *)
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA SS___interceptor_trampoline_bcmp).
(* scene's start-up shadow of check_step's two globals as named facts of B (an internal review, CHECKSTEP-REVIEW item R2): full
   granules in as_zero_shadow, the partial granules and the f9 redzones as constant cells; the walk derives
   range_addressable and shadow_hull_vis from am_const (YG0n.v:211) and al_zshadow (YG0d.v:435-438), as cgif
   A/AE2m.v:20-54 does. shadow_addr 0x20d80 = 0x7fffc1b0, shadow_addr 0x20da0 = 0x7fffc1b4. *)
Hypothesis HB_Z_TR : Exists (zr_sub (A_CS_TRAILER, 8)) (as_zero_shadow B).
Hypothesis HB_Z_CF : Exists (zr_sub (A_CS_CFRAME, 48)) (as_zero_shadow B).
Hypothesis HB_C_CS : forall ly,
  In (z1 (ANum (shadow_addr A_CS_TRAILER + 1)) 4) (as_const B ly) /\
  In (z1 (ANum (shadow_addr A_CS_TRAILER + 2)) 0xf9) (as_const B ly) /\
  In (z1 (ANum (shadow_addr A_CS_TRAILER + 3)) 0xf9) (as_const B ly) /\
  In (z1 (ANum (shadow_addr A_CS_CFRAME + 6)) 2) (as_const B ly) /\
  Forall (fun i => In (z1 (ANum (shadow_addr A_CS_CFRAME + i)) 0xf9) (as_const B ly)) [7; 8; 9; 10; 11].
(* static fact of the listing, closed by vm_compute on scene's PI: the two globals' addresses (same in both images); with HB_Z_TR / HB_Z_CF / HB_C_CS it pins every shadow byte of the 8-aligned hulls. *)
Hypothesis HB_ADDR : A_CS_TRAILER = 0x20d80 /\ A_CS_CFRAME = 0x20da0.
Hypothesis HRO_TR : ro_bytes SEGS pa_relro_lo pa_relro_hi B A_CS_TRAILER scene_trailer.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (PI := PI).
Local Ltac pin HS r e Hr :=
  let H := fresh "HSp" in
  pose proof (ast_ok_pi_set_reg_fp _ _ _ r e HS eq_refl
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite Hr; reflexivity)) as H;
  clear HS; rename H into HS; cbn [add_atom ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
Local Ltac addf HS n f Hf :=
  let H := fresh "HSf" in
  pose proof (st_ok_pi_add_fact _ _ _ n f HS Hf) as H; clear HS; rename H into HS.
(* the guard 0x835e0 with off held in an atom (1 <= k <= 341): ~body <u off is refuted from body + off < 2^64 *)
Local Ltac kill_not_trap_atom Hb Ho :=
  lazymatch goal with H : branch_taken BC_LTU (sv_denot _ (SAlu ALU_XOR (SOff ?n 0) (SLit (-1)))) (sv_denot _ (SOff ?m 0)) = true |- _ =>
  exfalso; rewrite branch_ltu_U in H;
  lazymatch type of Hb with _ = Z_to_bv 64 ?g => lazymatch type of Ho with _ = Z_to_bv 64 ?o =>
  rewrite (U_not_atom _ n g Hb) in H by lia; rewrite (U_atom _ m o Ho) in H by lia;
  apply Z.ltb_lt in H; lia end end end.
(* What the two calls and the plain runs leave untouched: every byte outside the callee window below the
   realigned sp (the 13 saved slots at sp0 - 104 .. sp0 - 8, the fake frame and its flag word, the block, the
   body and the image are all above it). *)
Definition s2_kept (W : world SEGS) (sp1 : Z) (m m' : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 2 * ESTACK <= a < sp1) ->
aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Lemma s2_kept_refl : forall W sp1 m, s2_kept W sp1 m m.
Proof. intros W sp1 m a _ _. reflexivity. Qed.
Lemma s2_kept_trans : forall W sp1 m m' m'', s2_kept W sp1 m m' -> s2_kept W sp1 m' m'' -> s2_kept W sp1 m m''.
Proof. intros W sp1 m m' m'' H1 H2 a Ha Hn. rewrite (H2 a Ha Hn). exact (H1 a Ha Hn). Qed.
Lemma s2_kept_of_frame : forall W sp1 E m m', frame_of E [] m m' -> s2_kept W sp1 m m'.
Proof.
intros W sp1 E m m' HF a _ _. apply (aview_eq_of SEGS).
unfold mrestrict. rewrite (HF (Z_to_bv 64 a) ltac:(intros (r & Hin & _); exact Hin)). reflexivity.
Qed.
(* One call of the bcmp wrapper from check_step's own frame (sp = sp0 - 128): aj_bcmp_at with the segment's
   constants discharged. *)
Lemma s2_bcmp : forall (W0 W : world SEGS) sp0 ly S mem md fpos ly1 S1
  (regsT : bvmap 5 word) memT mdT (x y n : Z) (raw : word),
ajournal SEGS B TCHECK_STEP_STK sp0 [] ly S W0 mem md [(CS_CID, fpos)] ly1 S1 W memT mdT 0 ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n ->
0 <= n < 2 ^ 32 -> 4096 <= x -> x + n <= alloc_ceiling -> 4096 <= y -> y + n <= alloc_ceiling ->
spZ regsT = sp0 - CHECK_STEP_FRAME ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall i, 0 <= i < n -> aview SEGS (w_H W) memT (x + i) <> None) ->
(forall i, 0 <= i < n -> aview SEGS (w_H W) memT (y + i) <> None) ->
amem_range x n -> amem_range y n ->
range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x n ->
(0 < n -> shadow_hull_vis (aview SEGS (w_H W) memT) x n) ->
range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF y n ->
(0 < n -> shadow_hull_vis (aview SEGS (w_H W) memT) y n) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA SS___interceptor_trampoline_bcmp)) memT (seg_rom SEGS)) mdT)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B TCHECK_STEP_STK sp0 [] ly S W0 mem md [(CS_CID, fpos)] ly1 S1 W mem2 md2 0 /\
aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
(v = w64 0 <-> forall i, 0 <= i < n -> aview SEGS (w_H W) memT (x + i) = aview SEGS (w_H W) memT (y + i)) /\
s2_kept W (sp0 - CHECK_STEP_FRAME) memT mem2).
Proof.
intros W0 W sp0 ly S mem md fpos ly1 S1 regsT memT mdT x y n raw
HJ Q10 Q11 Q12 Hn Hx0 Hxn Hy0 Hyn Hsp Qgp Qtp Qra Hraw HSX HSY HMX HMY HRX HHX HRY HHY.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof pa_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (FFS : TCHECK_STEP_STK = 8496) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
rewrite FFS in Hslo.
assert (HCF : CHECK_STEP_FRAME = 128) by reflexivity.
assert (Hdis : forall a, 4096 <= a -> a <= alloc_ceiling ->
  ~ (sp0 + (- CHECK_STEP_FRAME) - 2 * ESTACK <= a < sp0 + (- CHECK_STEP_FRAME))) by (intros a H1 H2 H3; lia).
eapply SRr_mono.
{ eapply (aj_bcmp_at SEGS B LAWS Hsegs (SIGMA SS___interceptor_trampoline_bcmp) ABCMP W regsT memT
    TCHECK_STEP_STK sp0 [] ly S W0 mem md [(CS_CID, fpos)] ly1 S1 mdT 0 x y n (- CHECK_STEP_FRAME) raw HJ).
  - exact Q10. - exact Q11. - exact Q12. - exact Hn.
  - lia. - lia. - lia. - lia.
  - rewrite Hsp. lia.
  - rewrite HCF. reflexivity.
  - lia.
  - lia.
  - exact Qgp. - exact Qtp. - exact Qra. - exact Hraw.
  - intros a Ha. split; [replace a with (x + (a - x)) by lia; apply HSX; lia | rewrite Hsp; lia].
  - intros a Ha. split; [replace a with (y + (a - y)) by lia; apply HSY; lia | rewrite Hsp; lia].
  - intros a Ha. apply Hdis; lia.
  - intros a Ha. apply Hdis; lia.
  - exact HMX. - exact HMY. - exact HRX. - exact HHX. - exact HRY. - exact HHY. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|]. split; [exact Hv|]. split; [exact Hcmp|].
intros a Ha Hout. apply Hfr; [exact Ha | lia].
Qed.
Lemma s2_kept_of_frame_r : forall (W : world SEGS) sp1 E rs (m m' : word -> option byte),
rs = [] -> frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> s2_kept W sp1 m m'.
Proof.
intros W sp1 E rs m m' -> HF a _ _. apply (aview_eq_of SEGS).
exact (HF (Z_to_bv 64 a) ltac:(intros (r & Hin & _); exact Hin)).
Qed.
Lemma s2_rdword_kept : forall (W : world SEGS) sp1 (m m' : word -> option byte) a v,
s2_kept W sp1 m m' -> 0 <= a -> a + 8 <= 2 ^ 64 ->
(forall kk, 0 <= kk < 8 -> ~ (sp1 - 2 * ESTACK <= a + kk < sp1)) ->
rdword (aview SEGS (w_H W) m) a = Some v -> rdword (aview SEGS (w_H W) m') a = Some v.
Proof.
intros W sp1 m m' a v HK H0 H8 Hns H.
rewrite (rdword_ext (aview SEGS (w_H W) m) (aview SEGS (w_H W) m') a); [exact H|].
intros kk Hkk. apply HK; [lia | exact (Hns kk Hkk)].
Qed.
(* the entry frame that holds the block, and the body block, are read back unchanged at any journal point *)
Lemma s2_keep_frame : forall sp0 ly S (W0 : world SEGS) mem md own ly1 S1 (W : world SEGS) memT mdT cid pos a,
ajournal SEGS B TCHECK_STEP_STK sp0 [] ly S W0 mem md own ly1 S1 W memT mdT 0 ->
In (cid, pos) (frames S) -> frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid ->
aview SEGS (w_H W) memT a = aview SEGS (w_H W0) mem a.
Proof.
intros sp0 ly S W0 mem md own ly1 S1 W memT mdT cid pos a HJ Hin Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
apply (F4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | intros (r & Hr & _); exact Hr].
Qed.
Lemma s2_keep_block : forall sp0 ly S (W0 : world SEGS) mem md own ly1 S1 (W : world SEGS) memT mdT p n i,
ajournal SEGS B TCHECK_STEP_STK sp0 [] ly S W0 mem md own ly1 S1 W memT mdT 0 ->
In (p, n) (ablocks B ly S) -> ablocks B ly1 S1 = ablocks B ly S -> 0 <= i < req_size n ->
aview SEGS (w_H W) memT (p + i) = aview SEGS (w_H W0) mem (p + i).
Proof.
intros sp0 ly S W0 mem md own ly1 S1 W memT mdT p n i HJ Hin Hab Hi.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
apply (F2 p n i Hin ltac:(rewrite Hab; exact Hin) Hi). intros (r & Hr & _); exact Hr.
Qed.
Local Ltac acc_keep KM :=
  lazymatch goal with HFr : frame_of ?E ?rs (mrestrict (w_H ?W) ?m) (mrestrict (w_H ?W) ?m') |- _ =>
    let K := fresh "KMs" in
    pose proof (s2_kept_trans _ _ _ _ _ KM (s2_kept_of_frame_r _ _ E rs m m' eq_refl HFr)) as K;
    clear KM HFr; rename K into KM end.
Lemma s2_frame_addr_le : forall n ly ly', layout_le n ly ly' -> forall cid pos, frame_addr ly' cid pos = frame_addr ly cid pos.
Proof. intros n ly ly' (_ & _ & _ & _ & _ & HF & _) cid pos. unfold frame_addr. rewrite HF. reflexivity. Qed.
(* the bnez after a call whose result register is pinned to 0 *)
Local Ltac kill_ne0 EA :=
  lazymatch goal with H : branch_taken BC_NE (sv_denot ?Ex (SOff ?n 0)) (sv_denot _ (SLit 0)) = true |- _ =>
  exfalso; rewrite branch_ne_U in H; rewrite (U_atom Ex n 0 EA ltac:(lia)) in H;
  rewrite U_lit in H by lia; cbn in H; discriminate H end.
(* one register of the cut state: read it off the symbolic state, map its atom to the cut's registers *)
Local Ltac cs_reg3 HS EE n r H :=
  let Hr := fresh "Hr" in prreg HS r Hr; rewrite Hr; clear Hr; rewrite (EE n r eq_refl); exact H.
Local Ltac prreg_raw HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) => pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) => pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr
  end;
  lazymatch type of Hr with _ = sv_denot _ (sr_get (ss_regs ?ssx) _) =>
    let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
    change (sr_get (ss_regs ssx) r) with e in Hr end;
  cbn [ms_regs restrict mkst] in Hr.
Lemma cs_S2 : CS_S2_stmt SK B.
Proof.
unfold CS_S2_stmt.
intros ly S W regs mem md ch blk body k b fpos ly1 S1 W1 regs1 mem1 md1 HST.
pose proof HST as (HPRE & HFRM & R19 & R20 & R21 & R24 & R22 & R23 & R5 & R12).
pose proof HPRE as (HAFN & Hsp32 & Htop32 & Hnfr & HROD & A10 & A11 & A12 & Hk & HFO & HBODY & Hlenb & Hbody & Hblk & Hnev & Hlive).
pose proof HAFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HFRM as (HJ & Hab & Hflag & Hsaved & R2 & R3 & R4 & R8 & R18 & R25 & R26 & R27).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : TCHECK_STEP_STK = 8496) by reflexivity.
assert (HCF : CHECK_STEP_FRAME = 128) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
pose proof HFO as ((cid & pos & Hinf & Hcid & Hfal & Hflo & Hfhi) & Hblk8 & HRAblk).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR Hinf) as (HF4096 & HFceil & HFapp).
destruct (al_blocks _ _ LAWS _ _ _ _ _ body CS_BODY_LEN HAR HBODY) as (_ & Hb4096 & Hbceil & Hbapp & Hbpres & _ & _).
assert (RSB : req_size CS_BODY_LEN = 8904) by reflexivity. rewrite RSB in Hbceil, Hbapp, Hbpres.
unfold CS_BLK_LEN in Hfhi. unfold CS_LAST in Hk.
pose proof (fs_frame_bytes_nonneg cid) as Hfb0.
assert (OFFR : 0 <= scene_off k <= 8890)
by (unfold scene_off; destruct (Z.eqb_spec k 0); [lia|]; destruct (Z.eqb_spec k 342); lia).
assert (HTR : A_CS_TRAILER = 0x20d80) by exact (proj1 HB_ADDR).
assert (HTRv : @pa_val _ scene_listing PI 248%nat = 0x20d80) by exact (proj1 HB_ADDR).
remember (Eimg (Ereg regs1 [])) as E eqn:HE.
assert (HEI : img_env (@pa_val _ scene_listing PI) A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HS : st_ok_pi SEGS (@pa_val _ scene_listing PI) E (mkSS (AF_check_step + 0x330) sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (@pa_val _ scene_listing PI A_TEXT + (AF_check_step + 0x330))) mem1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. exact I.
  - unfold facts_ok. cbn. tauto. }
clear HE.
unfold cfg_at.
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ ?pcw _ _) _) _ =>
  replace pcw with (Z_to_bv 64 (@pa_val _ scene_listing PI A_TEXT + (AF_check_step + 0x330))) by (unfold CS_PC2, A_check_step, w64; rewrite Z.add_assoc; reflexivity) end.
assert (E19 : ew E 19 = Z_to_bv 64 blk) by (rewrite (EE 19%nat 19%bv eq_refl), R19; reflexivity).
assert (E5 : ew E 5 = Z_to_bv 64 body) by (rewrite (EE 5%nat 5%bv eq_refl), R5; reflexivity).
assert (E12 : ew E 12 = Z_to_bv 64 (scene_off k)) by (rewrite (EE 12%nat 12%bv eq_refl), R12; reflexivity).
assert (E20 : ew E 20 = Z_to_bv 64 k) by (rewrite (EE 20%nat 20%bv eq_refl), R20; reflexivity).
assert (RG19 : 0 <= blk /\ blk + 9 < 2 ^ 64) by lia.
assert (F19 : afact_ok E 19 (mkAF 4096 (2 ^ 47) 0))
by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E19, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
assert (F5 : afact_ok E 5 (mkAF 4096 (2 ^ 47) 0))
by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E5, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
addf HS 19%nat (mkAF 4096 (2 ^ 47) 0) F19. addf HS 5%nat (mkAF 4096 (2 ^ 47) 0) F5.
destruct (Z.eq_dec k 0) as [Hk0 | Hk0]; [| destruct (Z.eq_dec k 342) as [Hk342 | Hk342]].
- subst k.
  assert (R12' : getr regs1 12%bv = w64 0) by (rewrite R12; reflexivity).
  assert (R24' : getr regs1 24%bv = w64 24) by (rewrite R24; reflexivity).
  assert (RGB : 0 <= body /\ body + 0 < 2 ^ 64) by lia.
  pose proof (s2_kept_refl W1 (spZ regs - CHECK_STEP_FRAME) mem1) as KM.
  pin HS (20%bv : bv 5) (SLit 0) R20. pin HS (12%bv : bv 5) (SLit 0) R12'. pin HS (24%bv : bv 5) (SLit 24) R24'.
  paj_run_shc RUNP RUNC HS HJ; [apply awr_ok_nil |]. acc_keep KM.
  psrr_branch_pi RUNP BR HS; [kill_not_trap E19 RG19 |].
  paj_run_shc RUNP RUNC HS HJ; [apply awr_ok_nil |]. acc_keep KM.
  psrr_branch_pi RUNP BR HS; [kill_not_trap E5 RGB |].
  paj_run_shc RUNP RUNC HS HJ; [apply awr_ok_nil |]. acc_keep KM.
  (* 0x835f0: bcmp(blk + 9, body, 24) *)
  pose proof HJ as (HAR_T & Hly & _ & _ & _ & Hfrs1 & _).
  pmkst HS.
  prreg_raw HS (10%bv : bv 5) Ra0. prreg_raw HS (11%bv : bv 5) Ra1. prreg_raw HS (12%bv : bv 5) Ra2.
  prreg_raw HS (1%bv : bv 5) Rra. prreg_raw HS (2%bv : bv 5) Qsp.
  prreg_raw HS (3%bv : bv 5) Qgp. prreg_raw HS (4%bv : bv 5) Qtp.
  eapply SRr_bind.
  { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
      eapply (s2_bcmp W W1 (spZ regs) ly S mem md fpos ly1 S1 rg mm mdx (blk + 9) body 24
        (Z_to_bv 64 (@pa_val _ scene_listing PI A_TEXT + 3408))) end.
    - exact HJ.
    - rewrite Ra0. cbn [sv_denot]. rewrite E19, unsigned_lit_small by lia. reflexivity.
    - rewrite Ra1. cbn [sv_denot]. rewrite E5, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
    - rewrite Ra2. cbn [sv_denot]. reflexivity.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - unfold spZ at 1. rewrite Qsp. cbn [sv_denot]. rewrite Z.add_0_r, (EE 2%nat (2%bv : bv 5) eq_refl), R2.
      unfold w64. rewrite !(unsigned_lit_small (spZ regs - CHECK_STEP_FRAME)) by lia. reflexivity.
    - rewrite Qgp. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 3%nat (3%bv : bv 5) eq_refl), R3. exact Hgp.
    - rewrite Qtp. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 4%nat (4%bv : bv 5) eq_refl), R4. exact Htp.
    - rewrite Rra. cbn [sv_denot]. rewrite (img_env_codeptr E HEI 3408). reflexivity.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros i Hi. replace (blk + 9 + i) with (blk + (9 + i)) by lia.
      rewrite (s2_keep_frame _ _ _ _ _ _ _ _ _ _ _ _ cid pos (blk + (9 + i)) HJ Hinf ltac:(lia)).
      rewrite (Hblk (9 + i) ltac:(unfold CS_BLK_LEN; lia)). discriminate.
    - intros i Hi.
      rewrite (s2_keep_block _ _ _ _ _ _ _ _ _ _ _ _ body CS_BODY_LEN i HJ HBODY Hab ltac:(rewrite RSB; lia)).
      rewrite (Hbody i ltac:(unfold CS_BODY_LEN; lia)). discriminate.
    - apply (amem_range_sub_app (frame_addr ly cid pos) (fs_frame_bytes cid) (blk + 9) 24 HFapp HFceil); lia.
    - apply (amem_range_of_block SEGS B LAWS ly S W mem md body CS_BODY_LEN body 24 HAR HBODY); rewrite ?RSB; lia.
    - apply (range_addressable_sub _ SHADOW_OFF blk 34 (blk + 9) 24); [| lia | lia].
      eapply (range_addressable_entry_frame SEGS B LAWS);
      [ exact HJ | exact Hinf | exact Hcid | exact Hflo | exact Hfhi | exact Hfal
      | intros xx (r & Hr & _); destruct Hr | exact HAR | exact HRAblk ].
    - intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS _ _ _ _ _ cid pos (blk + 9) 24).
      + exact HAR_T.
      + rewrite Hfrs1. right. exact Hinf.
      + rewrite (s2_frame_addr_le _ _ _ Hly). lia.
      + rewrite (s2_frame_addr_le _ _ _ Hly). lia.
      + lia.
    - apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 _ _ body CS_BODY_LEN body 24 HAR_T);
      [rewrite Hab; exact HBODY | lia | rewrite RSB; lia].
    - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly1 S1 W1 _ _ body CS_BODY_LEN body 24 HAR_T);
      [rewrite Hab; exact HBODY | lia | rewrite RSB; lia | lia]. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & KMc).
  assert (Hlb : length b = 8904%nat) by (rewrite Hlenb; reflexivity).
  assert (Hv0 : v = w64 0).
  { apply (proj2 Hcmp). intros i Hi.
    replace (blk + 9 + i) with (blk + (9 + i)) by lia.
    rewrite (s2_keep_frame _ _ _ _ _ _ _ _ _ _ _ _ cid pos (blk + (9 + i)) HJ Hinf ltac:(lia)).
    rewrite (s2_keep_block _ _ _ _ _ _ _ _ _ _ _ _ body CS_BODY_LEN i HJ HBODY Hab ltac:(rewrite RSB; lia)).
    rewrite (Hblk (9 + i) ltac:(unfold CS_BLK_LEN; lia)), (Hbody i ltac:(unfold CS_BODY_LEN; lia)).
    pose proof (s2_payload_nth b 0 i Hlb ltac:(lia) ltac:(change (scene_len 0) with 24; lia)) as HPN.
    change (if 0 =? 0 then 9 else 7) with 9 in HPN. change (scene_off 0) with 0 in HPN.
    rewrite Z.add_0_l in HPN. rewrite HPN. reflexivity. }
  pose proof (s2_kept_trans _ _ _ _ _ KM KMc) as KMn. clear KM KMc. rename KMn into KM.
  clear HJ. rename HJ2 into HJ.
  jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W1) mem2) HP2 (@nil nat) HS2.
  specialize (HS2 (Forall_nil _)).
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  assert (HEI2 : img_env (@pa_val _ scene_listing PI) A_LIM (havoc E 512 (map (getr regs2) CLOB)))
    by (apply img_env_havoc_hi; [exact HEI | cbv; lia]).
  assert (EA0 : ew (havoc E 512 (map (getr regs2) CLOB)) 516 = Z_to_bv 64 0).
  { change 516%nat with (512 + 4)%nat. rewrite (ew_havoc_new E 512 _ 4 (Z_to_bv 64 0)) by (cbv; lia).
    cbv [CLOB]. cbn [map nth]. rewrite Hv, Hv0. reflexivity. }
  paj_run_shc RUNP RUNC HS HJ; [apply awr_ok_nil |]. acc_keep KM.
  psrr_branch_pi RUNP BR HS; [kill_ne0 EA0 |].
  paj_run_to_shc RUNTOP HS HJ (AF_check_step + 0x398); [apply awr_ok_nil |]. acc_keep KM.
  (* ---- the cut 0x8362c: cs_st3 ---- *)
  pose proof HJ as (HAR_F & Hly_F & _ & _ & _ & Hfrs_F & _).
  assert (Hin1 : In (CS_CID, fpos) (frames S1)) by (rewrite Hfrs_F; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR_F Hin1) as (HFF4096 & HFFceil & _).
  assert (HFB : fs_frame_bytes CS_CID = 256) by reflexivity.
  apply SRr_ret. cbv beta. pmkst HS.
  lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?R _ ?M _) ?MD = _ /\ _ => exists ly1, S1, R, M, MD end.
  split.
  { unfold cfg_at. f_equal. f_equal. unfold w64, CS_PC3, A_check_step, AF_check_step. f_equal. lia. }
  unfold cs_st3, cs_frame.
  split; [exact HPRE|].
  split.
  { split; [exact HJ|]. split; [exact Hab|].
    split.
    { eapply (s2_rdword_kept _ _ mem1 _ _ _ KM); [lia | lia | intros kk Hkk; lia | exact Hflag]. }
    split.
    { intros j Hj. eapply (s2_rdword_kept _ _ mem1 _ _ _ KM);
      [lia | lia | intros kk Hkk; lia | exact (Hsaved j Hj)]. }
    split; [cs_reg3 HS EE 2%nat (2%bv : bv 5) R2|].
    split; [cs_reg3 HS EE 3%nat (3%bv : bv 5) R3|].
    split; [cs_reg3 HS EE 4%nat (4%bv : bv 5) R4|].
    split; [cs_reg3 HS EE 8%nat (8%bv : bv 5) R8|].
    split; [cs_reg3 HS EE 18%nat (18%bv : bv 5) R18|].
    split; [cs_reg3 HS EE 25%nat (25%bv : bv 5) R25|].
    split; [cs_reg3 HS EE 26%nat (26%bv : bv 5) R26 | cs_reg3 HS EE 27%nat (27%bv : bv 5) R27]. }
  split; [cs_reg3 HS EE 19%nat (19%bv : bv 5) R19|].
  split; [cs_reg3 HS EE 21%nat (21%bv : bv 5) R21|].
  split; [let Hr := fresh "Hr" in prreg HS (24%bv : bv 5) Hr; rewrite Hr; reflexivity|].
  split; [cs_reg3 HS EE 22%nat (22%bv : bv 5) R22 | cs_reg3 HS EE 23%nat (23%bv : bv 5) R23].
- subst k.
  assert (R12' : getr regs1 12%bv = w64 8890) by (rewrite R12; reflexivity).
  assert (R24' : getr regs1 24%bv = w64 14) by (rewrite R24; reflexivity).
  assert (RGB : 0 <= body /\ body + 8890 < 2 ^ 64) by lia.
  pose proof (s2_kept_refl W1 (spZ regs - CHECK_STEP_FRAME) mem1) as KM.
  pin HS (20%bv : bv 5) (SLit 342) R20. pin HS (12%bv : bv 5) (SLit 8890) R12'. pin HS (24%bv : bv 5) (SLit 14) R24'.
  paj_run_shc RUNP RUNC HS HJ; [apply awr_ok_nil |]. acc_keep KM.
  psrr_branch_pi RUNP BR HS; [kill_not_trap E19 RG19 |].
  paj_run_shc RUNP RUNC HS HJ; [apply awr_ok_nil |]. acc_keep KM.
  psrr_branch_pi RUNP BR HS; [kill_not_trap E5 RGB |].
  paj_run_shc RUNP RUNC HS HJ; [apply awr_ok_nil |]. acc_keep KM.
  (* 0x835f0: bcmp(blk + 7, body + 8890, 14) *)
  pose proof HJ as (HAR_T & Hly & _ & _ & _ & Hfrs1 & _).
  pmkst HS.
  prreg_raw HS (10%bv : bv 5) Ra0. prreg_raw HS (11%bv : bv 5) Ra1. prreg_raw HS (12%bv : bv 5) Ra2.
  prreg_raw HS (1%bv : bv 5) Rra. prreg_raw HS (2%bv : bv 5) Qsp.
  prreg_raw HS (3%bv : bv 5) Qgp. prreg_raw HS (4%bv : bv 5) Qtp.
  eapply SRr_bind.
  { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
      eapply (s2_bcmp W W1 (spZ regs) ly S mem md fpos ly1 S1 rg mm mdx (blk + 7) (body + 8890) 14
        (Z_to_bv 64 (@pa_val _ scene_listing PI A_TEXT + 3408))) end.
    - exact HJ.
    - rewrite Ra0. cbn [sv_denot]. rewrite E19, unsigned_lit_small by lia. reflexivity.
    - rewrite Ra1. cbn [sv_denot]. rewrite E5, unsigned_lit_small by lia. reflexivity.
    - rewrite Ra2. cbn [sv_denot]. reflexivity.
    - lia. - lia. - lia. - lia. - lia.
    - unfold spZ at 1. rewrite Qsp. cbn [sv_denot]. rewrite Z.add_0_r, (EE 2%nat (2%bv : bv 5) eq_refl), R2.
      unfold w64. rewrite !(unsigned_lit_small (spZ regs - CHECK_STEP_FRAME)) by lia. reflexivity.
    - rewrite Qgp. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 3%nat (3%bv : bv 5) eq_refl), R3. exact Hgp.
    - rewrite Qtp. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 4%nat (4%bv : bv 5) eq_refl), R4. exact Htp.
    - rewrite Rra. cbn [sv_denot]. rewrite (img_env_codeptr E HEI 3408). reflexivity.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros i Hi. replace (blk + 7 + i) with (blk + (7 + i)) by lia.
      rewrite (s2_keep_frame _ _ _ _ _ _ _ _ _ _ _ _ cid pos (blk + (7 + i)) HJ Hinf ltac:(lia)).
      rewrite (Hblk (7 + i) ltac:(unfold CS_BLK_LEN; lia)). discriminate.
    - intros i Hi. replace (body + 8890 + i) with (body + (8890 + i)) by lia.
      rewrite (s2_keep_block _ _ _ _ _ _ _ _ _ _ _ _ body CS_BODY_LEN (8890 + i) HJ HBODY Hab ltac:(rewrite RSB; lia)).
      rewrite (Hbody (8890 + i) ltac:(unfold CS_BODY_LEN; lia)). discriminate.
    - apply (amem_range_sub_app (frame_addr ly cid pos) (fs_frame_bytes cid) (blk + 7) 14 HFapp HFceil); lia.
    - apply (amem_range_of_block SEGS B LAWS ly S W mem md body CS_BODY_LEN (body + 8890) 14 HAR HBODY); rewrite ?RSB; lia.
    - apply (range_addressable_sub _ SHADOW_OFF blk 34 (blk + 7) 14); [| lia | lia].
      eapply (range_addressable_entry_frame SEGS B LAWS);
      [ exact HJ | exact Hinf | exact Hcid | exact Hflo | exact Hfhi | exact Hfal
      | intros xx (r & Hr & _); destruct Hr | exact HAR | exact HRAblk ].
    - intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS _ _ _ _ _ cid pos (blk + 7) 14).
      + exact HAR_T.
      + rewrite Hfrs1. right. exact Hinf.
      + rewrite (s2_frame_addr_le _ _ _ Hly). lia.
      + rewrite (s2_frame_addr_le _ _ _ Hly). lia.
      + lia.
    - apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 _ _ body CS_BODY_LEN (body + 8890) 14 HAR_T);
      [rewrite Hab; exact HBODY | lia | rewrite RSB; lia].
    - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly1 S1 W1 _ _ body CS_BODY_LEN (body + 8890) 14 HAR_T);
      [rewrite Hab; exact HBODY | lia | rewrite RSB; lia | lia]. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & KMc).
  assert (Hlb : length b = 8904%nat) by (rewrite Hlenb; reflexivity).
  assert (Hv0 : v = w64 0).
  { apply (proj2 Hcmp). intros i Hi.
    replace (blk + 7 + i) with (blk + (7 + i)) by lia.
    replace (body + 8890 + i) with (body + (8890 + i)) by lia.
    rewrite (s2_keep_frame _ _ _ _ _ _ _ _ _ _ _ _ cid pos (blk + (7 + i)) HJ Hinf ltac:(lia)).
    rewrite (s2_keep_block _ _ _ _ _ _ _ _ _ _ _ _ body CS_BODY_LEN (8890 + i) HJ HBODY Hab ltac:(rewrite RSB; lia)).
    rewrite (Hblk (7 + i) ltac:(unfold CS_BLK_LEN; lia)), (Hbody (8890 + i) ltac:(unfold CS_BODY_LEN; lia)).
    pose proof (s2_payload_nth b 342 i Hlb ltac:(lia) ltac:(change (scene_len 342) with 14; lia)) as HPN.
    change (if 342 =? 0 then 9 else 7) with 7 in HPN. change (scene_off 342) with 8890 in HPN.
    rewrite HPN. reflexivity. }
  pose proof (s2_kept_trans _ _ _ _ _ KM KMc) as KMn. clear KM KMc. rename KMn into KM.
  clear HJ. rename HJ2 into HJ.
  jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W1) mem2) HP2 (@nil nat) HS2.
  specialize (HS2 (Forall_nil _)).
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  assert (HEI2 : img_env (@pa_val _ scene_listing PI) A_LIM (havoc E 512 (map (getr regs2) CLOB)))
    by (apply img_env_havoc_hi; [exact HEI | cbv; lia]).
  assert (EA0 : ew (havoc E 512 (map (getr regs2) CLOB)) 516 = Z_to_bv 64 0).
  { change 516%nat with (512 + 4)%nat. rewrite (ew_havoc_new E 512 _ 4 (Z_to_bv 64 0)) by (cbv; lia).
    cbv [CLOB]. cbn [map nth]. rewrite Hv, Hv0. reflexivity. }
  paj_run_shc RUNP RUNC HS HJ; [apply awr_ok_nil |]. acc_keep KM.
  psrr_branch_pi RUNP BR HS; [kill_ne0 EA0 |].
  paj_run_shc RUNP RUNC HS HJ; [apply awr_ok_nil |]. acc_keep KM.
  (* 0x83624: bcmp(blk + 21, check_step.trailer, 12) *)
  pose proof HJ as (HAR_T2 & Hly2 & _ & _ & _ & Hfrs2 & _).
  pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B TCHECK_STEP_STK (spZ regs) []
    ly S W mem md [(CS_CID, fpos)] ly1 S1 _ _ _ 0 HJ HROD) as HRODT.
  pmkst HS.
  prreg_raw HS (10%bv : bv 5) Rb0. prreg_raw HS (11%bv : bv 5) Rb1. prreg_raw HS (12%bv : bv 5) Rb2.
  prreg_raw HS (1%bv : bv 5) Rrb. prreg_raw HS (2%bv : bv 5) Qsp2.
  prreg_raw HS (3%bv : bv 5) Qgp2. prreg_raw HS (4%bv : bv 5) Qtp2.
  eapply SRr_bind.
  { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
      eapply (s2_bcmp W W1 (spZ regs) ly S mem md fpos ly1 S1 rg mm mdx (blk + 21) A_CS_TRAILER 12
        (Z_to_bv 64 (@pa_val _ scene_listing PI A_TEXT + 3460))) end.
    - exact HJ.
    - rewrite Rb0. cbn [sv_denot]. rewrite ew_havoc_old by (cbv; lia).
      rewrite E19, unsigned_lit_small by lia. reflexivity.
    - rewrite Rb1. cbn [sv_denot]. rewrite ew_havoc_old by (cbv; lia).
      rewrite (img_env_atomP E 248%nat HEI ltac:(unfold A_TEXT, A_LIM; lia)).
      rewrite Z.add_0_r, unsigned_lit_small by (rewrite HTRv; lia). reflexivity.
    - rewrite Rb2. cbn [sv_denot]. reflexivity.
    - lia. - lia. - lia. - rewrite HTR; lia. - rewrite HTR; lia.
    - unfold spZ at 1. rewrite Qsp2. cbn [sv_denot]. rewrite ew_havoc_old by (cbv; lia).
      rewrite Z.add_0_r, (EE 2%nat (2%bv : bv 5) eq_refl), R2.
      unfold w64. rewrite !(unsigned_lit_small (spZ regs - CHECK_STEP_FRAME)) by lia. reflexivity.
    - rewrite Qgp2. cbn [sv_denot]. rewrite ew_havoc_old by (cbv; lia).
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 3%nat (3%bv : bv 5) eq_refl), R3. exact Hgp.
    - rewrite Qtp2. cbn [sv_denot]. rewrite ew_havoc_old by (cbv; lia).
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 4%nat (4%bv : bv 5) eq_refl), R4. exact Htp.
    - rewrite Rrb. cbn [sv_denot]. rewrite (img_env_codeptr _ HEI2 3460). reflexivity.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros i Hi. replace (blk + 21 + i) with (blk + (21 + i)) by lia.
      rewrite (s2_keep_frame _ _ _ _ _ _ _ _ _ _ _ _ cid pos (blk + (21 + i)) HJ Hinf ltac:(lia)).
      rewrite (Hblk (21 + i) ltac:(unfold CS_BLK_LEN; lia)). discriminate.
    - intros i Hi. destruct (HRO_TR i ltac:(change (Z.of_nat (length scene_trailer)) with 12; lia)) as (Hro & Hno & Hne & Hval).
      rewrite (HRODT _ Hro Hno Hne), Hval. discriminate.
    - apply (amem_range_sub_app (frame_addr ly cid pos) (fs_frame_bytes cid) (blk + 21) 12 HFapp HFceil); lia.
    - apply amem_range_high; [lia | left; rewrite HTR; lia | rewrite HTR; lia].
    - apply (range_addressable_sub _ SHADOW_OFF blk 34 (blk + 21) 12); [| lia | lia].
      eapply (range_addressable_entry_frame SEGS B LAWS);
      [ exact HJ | exact Hinf | exact Hcid | exact Hflo | exact Hfhi | exact Hfal
      | intros xx (r & Hr & _); destruct Hr | exact HAR | exact HRAblk ].
    - intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS _ _ _ _ _ cid pos (blk + 21) 12).
      + exact HAR_T2.
      + rewrite Hfrs2. right. exact Hinf.
      + rewrite (s2_frame_addr_le _ _ _ Hly2). lia.
      + rewrite (s2_frame_addr_le _ _ _ Hly2). lia.
      + lia.
    - exact (proj1 (s2_trailer_shadow B HB_Z_TR HB_Z_CF HB_C_CS HB_ADDR ly1 S1 W1 _ _ HAR_T2)).
    - intros _. exact (proj2 (s2_trailer_shadow B HB_Z_TR HB_Z_CF HB_C_CS HB_ADDR ly1 S1 W1 _ _ HAR_T2)). }
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & v2 & -> & HJ3 & HP3 & Hv2 & Hcmp2 & KMc2).
  assert (Hv0b : v2 = w64 0).
  { apply (proj2 Hcmp2). intros i Hi.
    replace (blk + 21 + i) with (blk + (21 + i)) by lia.
    rewrite (s2_keep_frame _ _ _ _ _ _ _ _ _ _ _ _ cid pos (blk + (21 + i)) HJ Hinf ltac:(lia)).
    rewrite (Hblk (21 + i) ltac:(unfold CS_BLK_LEN; lia)).
    destruct (HRO_TR i ltac:(change (Z.of_nat (length scene_trailer)) with 12; lia)) as (Hro & Hno & Hne & Hval).
    rewrite (HRODT _ Hro Hno Hne), Hval.
    rewrite (s2_trailer_nth b i Hlb ltac:(lia)). reflexivity. }
  pose proof (s2_kept_trans _ _ _ _ _ KM KMc2) as KMn. clear KM KMc2. rename KMn into KM.
  clear HJ. rename HJ3 into HJ.
  jafter_call_keep_hi HS 1024%nat regs3 (mrestrict (w_H W1) mem3) HP3 (@nil nat) HS3.
  specialize (HS3 (Forall_nil _)).
  clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
  assert (HEI3 : img_env (@pa_val _ scene_listing PI) A_LIM
    (havoc (havoc E 512 (map (getr regs2) CLOB)) 1024 (map (getr regs3) CLOB)))
    by (apply img_env_havoc_hi; [exact HEI2 | cbv; lia]).
  assert (EA0b : ew (havoc (havoc E 512 (map (getr regs2) CLOB)) 1024 (map (getr regs3) CLOB)) 1028
    = Z_to_bv 64 0).
  { change 1028%nat with (1024 + 4)%nat.
    rewrite (ew_havoc_new _ 1024 _ 4 (Z_to_bv 64 0)) by (cbv; lia).
    cbv [CLOB]. cbn [map nth]. rewrite Hv2, Hv0b. reflexivity. }
  paj_run_shc RUNP RUNC HS HJ; [apply awr_ok_nil |]. acc_keep KM.
  psrr_branch_pi RUNP BR HS; [kill_ne0 EA0b |].
  paj_run_to_shc RUNTOP HS HJ (AF_check_step + 0x398); [apply awr_ok_nil |]. acc_keep KM.
  (* ---- the cut 0x8362c: cs_st3 ---- *)
  pose proof HJ as (HAR_F & Hly_F & _ & _ & _ & Hfrs_F & _).
  assert (Hin1 : In (CS_CID, fpos) (frames S1)) by (rewrite Hfrs_F; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR_F Hin1) as (HFF4096 & HFFceil & _).
  assert (HFB : fs_frame_bytes CS_CID = 256) by reflexivity.
  apply SRr_ret. cbv beta. pmkst HS.
  lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?R _ ?M _) ?MD = _ /\ _ => exists ly1, S1, R, M, MD end.
  split.
  { unfold cfg_at. f_equal. f_equal. unfold w64, CS_PC3, A_check_step, AF_check_step. f_equal. lia. }
  unfold cs_st3, cs_frame.
  split; [exact HPRE|].
  split.
  { split; [exact HJ|]. split; [exact Hab|].
    split.
    { eapply (s2_rdword_kept _ _ mem1 _ _ _ KM); [lia | lia | intros kk Hkk; lia | exact Hflag]. }
    split.
    { intros j Hj. eapply (s2_rdword_kept _ _ mem1 _ _ _ KM);
      [lia | lia | intros kk Hkk; lia | exact (Hsaved j Hj)]. }
    split; [cs_reg3 HS EE 2%nat (2%bv : bv 5) R2|].
    split; [cs_reg3 HS EE 3%nat (3%bv : bv 5) R3|].
    split; [cs_reg3 HS EE 4%nat (4%bv : bv 5) R4|].
    split; [cs_reg3 HS EE 8%nat (8%bv : bv 5) R8|].
    split; [cs_reg3 HS EE 18%nat (18%bv : bv 5) R18|].
    split; [cs_reg3 HS EE 25%nat (25%bv : bv 5) R25|].
    split; [cs_reg3 HS EE 26%nat (26%bv : bv 5) R26 | cs_reg3 HS EE 27%nat (27%bv : bv 5) R27]. }
  split; [cs_reg3 HS EE 19%nat (19%bv : bv 5) R19|].
  split; [cs_reg3 HS EE 21%nat (21%bv : bv 5) R21|].
  split; [let Hr := fresh "Hr" in prreg HS (24%bv : bv 5) Hr; rewrite Hr; reflexivity|].
  split; [cs_reg3 HS EE 22%nat (22%bv : bv 5) R22 | cs_reg3 HS EE 23%nat (23%bv : bv 5) R23].
- assert (L26 : scene_len k = 26) by (unfold scene_len; rewrite (proj2 (Z.eqb_neq k 0) Hk0), (proj2 (Z.eqb_neq k 342) Hk342); reflexivity).
  assert (OFFM : scene_off k = 24 + 26 * (k - 1))
  by (unfold scene_off; rewrite (proj2 (Z.eqb_neq k 0) Hk0), (proj2 (Z.eqb_neq k 342) Hk342); reflexivity).
  assert (R24' : getr regs1 24%bv = w64 26) by (rewrite R24, L26; reflexivity).
  pose proof (s2_kept_refl W1 (spZ regs - CHECK_STEP_FRAME) mem1) as KM.
  assert (F20 : afact_ok E 20 (mkAF 1 341 0))
  by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E20, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
  addf HS 20%nat (mkAF 1 341 0) F20.
  pin HS (24%bv : bv 5) (SLit 26) R24'.
  paj_run_shc RUNP RUNC HS HJ; [apply awr_ok_nil |]. acc_keep KM.
  psrr_branch_pi RUNP BR HS; [kill_not_trap E19 RG19 |].
  paj_run_shc RUNP RUNC HS HJ; [apply awr_ok_nil |]. acc_keep KM.
  psrr_branch_pi RUNP BR HS; [kill_not_trap_atom E5 E12 |].
  paj_run_shc RUNP RUNC HS HJ; [apply awr_ok_nil |]. acc_keep KM.
  (* 0x835f0: bcmp(blk + 7, body + scene_off k, 26) *)
  pose proof HJ as (HAR_T & Hly & _ & _ & _ & Hfrs1 & _).
  pmkst HS.
  prreg_raw HS (10%bv : bv 5) Ra0. prreg_raw HS (11%bv : bv 5) Ra1. prreg_raw HS (12%bv : bv 5) Ra2.
  prreg_raw HS (1%bv : bv 5) Rra. prreg_raw HS (2%bv : bv 5) Qsp.
  prreg_raw HS (3%bv : bv 5) Qgp. prreg_raw HS (4%bv : bv 5) Qtp.
  eapply SRr_bind.
  { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
      eapply (s2_bcmp W W1 (spZ regs) ly S mem md fpos ly1 S1 rg mm mdx (blk + 7) (body + scene_off k) 26
        (Z_to_bv 64 (@pa_val _ scene_listing PI A_TEXT + 3408))) end.
    - exact HJ.
    - rewrite Ra0. cbn [sv_denot]. rewrite E19, unsigned_lit_small by lia. reflexivity.
    - assert (U5 : bv_unsigned (ew E 5) = body) by (rewrite E5; apply unsigned_lit_small; lia).
      assert (U12 : bv_unsigned (ew E 12) = scene_off k) by (rewrite E12; apply unsigned_lit_small; lia).
      rewrite Ra1, denot_lit_U, (U_add_off_atom E 5 0 12 0) by (rewrite ?U5, ?U12; unfold M64; lia).
      rewrite U5, U12. unfold w64. f_equal. lia.
    - rewrite Ra2. cbn [sv_denot]. reflexivity.
    - lia. - lia. - lia. - lia. - lia.
    - unfold spZ at 1. rewrite Qsp. cbn [sv_denot]. rewrite Z.add_0_r, (EE 2%nat (2%bv : bv 5) eq_refl), R2.
      unfold w64. rewrite !(unsigned_lit_small (spZ regs - CHECK_STEP_FRAME)) by lia. reflexivity.
    - rewrite Qgp. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 3%nat (3%bv : bv 5) eq_refl), R3. exact Hgp.
    - rewrite Qtp. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 4%nat (4%bv : bv 5) eq_refl), R4. exact Htp.
    - rewrite Rra. cbn [sv_denot]. rewrite (img_env_codeptr E HEI 3408). reflexivity.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros i Hi. replace (blk + 7 + i) with (blk + (7 + i)) by lia.
      rewrite (s2_keep_frame _ _ _ _ _ _ _ _ _ _ _ _ cid pos (blk + (7 + i)) HJ Hinf ltac:(lia)).
      rewrite (Hblk (7 + i) ltac:(unfold CS_BLK_LEN; lia)). discriminate.
    - intros i Hi. replace (body + scene_off k + i) with (body + (scene_off k + i)) by lia.
      rewrite (s2_keep_block _ _ _ _ _ _ _ _ _ _ _ _ body CS_BODY_LEN (scene_off k + i) HJ HBODY Hab
        ltac:(rewrite RSB; lia)).
      rewrite (Hbody (scene_off k + i) ltac:(unfold CS_BODY_LEN; lia)). discriminate.
    - apply (amem_range_sub_app (frame_addr ly cid pos) (fs_frame_bytes cid) (blk + 7) 26 HFapp HFceil); lia.
    - apply (amem_range_of_block SEGS B LAWS ly S W mem md body CS_BODY_LEN (body + scene_off k) 26 HAR HBODY);
      rewrite ?RSB; lia.
    - apply (range_addressable_sub _ SHADOW_OFF blk 34 (blk + 7) 26); [| lia | lia].
      eapply (range_addressable_entry_frame SEGS B LAWS);
      [ exact HJ | exact Hinf | exact Hcid | exact Hflo | exact Hfhi | exact Hfal
      | intros xx (r & Hr & _); destruct Hr | exact HAR | exact HRAblk ].
    - intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS _ _ _ _ _ cid pos (blk + 7) 26).
      + exact HAR_T.
      + rewrite Hfrs1. right. exact Hinf.
      + rewrite (s2_frame_addr_le _ _ _ Hly). lia.
      + rewrite (s2_frame_addr_le _ _ _ Hly). lia.
      + lia.
    - apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 _ _ body CS_BODY_LEN (body + scene_off k) 26 HAR_T);
      [rewrite Hab; exact HBODY | lia | rewrite RSB; lia].
    - intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly1 S1 W1 _ _ body CS_BODY_LEN (body + scene_off k) 26 HAR_T);
      [rewrite Hab; exact HBODY | lia | rewrite RSB; lia | lia]. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & KMc).
  assert (Hlb : length b = 8904%nat) by (rewrite Hlenb; reflexivity).
  assert (Hv0 : v = w64 0).
  { apply (proj2 Hcmp). intros i Hi.
    replace (blk + 7 + i) with (blk + (7 + i)) by lia.
    replace (body + scene_off k + i) with (body + (scene_off k + i)) by lia.
    rewrite (s2_keep_frame _ _ _ _ _ _ _ _ _ _ _ _ cid pos (blk + (7 + i)) HJ Hinf ltac:(lia)).
    rewrite (s2_keep_block _ _ _ _ _ _ _ _ _ _ _ _ body CS_BODY_LEN (scene_off k + i) HJ HBODY Hab
      ltac:(rewrite RSB; lia)).
    rewrite (Hblk (7 + i) ltac:(unfold CS_BLK_LEN; lia)), (Hbody (scene_off k + i) ltac:(unfold CS_BODY_LEN; lia)).
    pose proof (s2_payload_nth b k i Hlb ltac:(lia) ltac:(rewrite L26; lia)) as HPN.
    rewrite (proj2 (Z.eqb_neq k 0) Hk0) in HPN. change (if false then 9 else 7) with 7 in HPN.
    rewrite HPN. reflexivity. }
  pose proof (s2_kept_trans _ _ _ _ _ KM KMc) as KMn. clear KM KMc. rename KMn into KM.
  clear HJ. rename HJ2 into HJ.
  jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W1) mem2) HP2 (@nil nat) HS2.
  specialize (HS2 (Forall_nil _)).
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  assert (HEI2 : img_env (@pa_val _ scene_listing PI) A_LIM (havoc E 512 (map (getr regs2) CLOB)))
    by (apply img_env_havoc_hi; [exact HEI | cbv; lia]).
  assert (EA0 : ew (havoc E 512 (map (getr regs2) CLOB)) 516 = Z_to_bv 64 0).
  { change 516%nat with (512 + 4)%nat. rewrite (ew_havoc_new E 512 _ 4 (Z_to_bv 64 0)) by (cbv; lia).
    cbv [CLOB]. cbn [map nth]. rewrite Hv, Hv0. reflexivity. }
  paj_run_shc RUNP RUNC HS HJ; [apply awr_ok_nil |]. acc_keep KM.
  psrr_branch_pi RUNP BR HS; [kill_ne0 EA0 |].
  paj_run_to_shc RUNTOP HS HJ (AF_check_step + 0x398); [apply awr_ok_nil |]. acc_keep KM.
  (* ---- the cut 0x8362c: cs_st3 ---- *)
  pose proof HJ as (HAR_F & Hly_F & _ & _ & _ & Hfrs_F & _).
  assert (Hin1 : In (CS_CID, fpos) (frames S1)) by (rewrite Hfrs_F; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR_F Hin1) as (HFF4096 & HFFceil & _).
  assert (HFB : fs_frame_bytes CS_CID = 256) by reflexivity.
  apply SRr_ret. cbv beta. pmkst HS.
  lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?R _ ?M _) ?MD = _ /\ _ => exists ly1, S1, R, M, MD end.
  split.
  { unfold cfg_at. f_equal. f_equal. unfold w64, CS_PC3, A_check_step, AF_check_step. f_equal. lia. }
  unfold cs_st3, cs_frame.
  split; [exact HPRE|].
  split.
  { split; [exact HJ|]. split; [exact Hab|].
    split.
    { eapply (s2_rdword_kept _ _ mem1 _ _ _ KM); [lia | lia | intros kk Hkk; lia | exact Hflag]. }
    split.
    { intros j Hj. eapply (s2_rdword_kept _ _ mem1 _ _ _ KM);
      [lia | lia | intros kk Hkk; lia | exact (Hsaved j Hj)]. }
    split; [cs_reg3 HS EE 2%nat (2%bv : bv 5) R2|].
    split; [cs_reg3 HS EE 3%nat (3%bv : bv 5) R3|].
    split; [cs_reg3 HS EE 4%nat (4%bv : bv 5) R4|].
    split; [cs_reg3 HS EE 8%nat (8%bv : bv 5) R8|].
    split; [cs_reg3 HS EE 18%nat (18%bv : bv 5) R18|].
    split; [cs_reg3 HS EE 25%nat (25%bv : bv 5) R25|].
    split; [cs_reg3 HS EE 26%nat (26%bv : bv 5) R26 | cs_reg3 HS EE 27%nat (27%bv : bv 5) R27]. }
  split; [cs_reg3 HS EE 19%nat (19%bv : bv 5) R19|].
  split; [cs_reg3 HS EE 21%nat (21%bv : bv 5) R21|].
  split; [let Hr := fresh "Hr" in prreg HS (24%bv : bv 5) Hr; rewrite Hr; rewrite L26; reflexivity|].
  split; [cs_reg3 HS EE 22%nat (22%bv : bv 5) R22 | cs_reg3 HS EE 23%nat (23%bv : bv 5) R23].
Qed.
End h.
End f.
End d.
Print Assumptions cs_S2.
