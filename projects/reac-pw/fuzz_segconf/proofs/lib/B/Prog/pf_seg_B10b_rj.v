(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the helpers of the
   bad-role refusal piece PB10_R of segment B10b of reac_segconf_parse_file's walk (the piece is
   pf_seg_B10b_r.v). The B10b segment lane of the image-B G3 walk owner, 2026-10-30. proves no function (kind: walk lemmas of a
   segment piece).
   ADAPTED from a working branch's lib/A/Prog/pf_a7_q.v (the mid-walk seed with read-only slot regions)
   and pf_a7_u.v (the cut rebuilt after refuse), and this lane's pf_seg_B10b_j.v (the run to a cut from a seed
   with every register its own atom), re-derived on image B's code.
     b10r_seed   the symbolic state at BAD (0x88960): every register its own atom, three read-only one-word
                 regions on s1's atom for the slots the run reads (0x40 = cur_name, 0x70 = vp, 0xc8 = c), held
                 by the extra atoms 33, 34, 32.
     b10r_jump   the `j 0x88dc8` at 0x8897c (BASE + PF_BADRET): from JOIN's state there, H_JOIN gives the post.
     b10r_after  the cut JOIN rebuilt at the FP state refuse returned at, from the cut at the call, refuse's
                 journal and post and the callee-saved registers; then b10r_jump.
   Section hypotheses: OBJ (b10r_lit_atom: listing object 60 is F_badrole's literal), VRO and SSPX
   (b10r_after, through pf_seg_B10b_rk.b10r_base_move: pf_obj's arodata_okP and sa_ssp after the call), all from
   the segment's piece list, section 3. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YG0d_tail.
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
PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B10b_k pf_seg_B10b_rk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* 0x8897c, where the refuse call returns (BAD's last instruction, the `j` to JOIN) *)
Definition PF_BADRET : Z := AF_reac_segconf_parse_file + 0xb44.
Lemma b10r_pcs : seg_text + PF_BAD = 0x88960 /\ seg_text + PF_BADRET = 0x8897c.
Proof. vm_compute. split; reflexivity. Qed.

(* the three one-word read-only regions on s1's atom: the slots 0x40 (cur_name), 0x70 (vp), 0xc8 (c) *)
Definition b10r_regions : smem :=
  [YP09.mkRegion (Some 9%nat) 0x40 0x48 0 0 [YP09.mkChunk 0x40 (CVal 8 (SOff 33 0))];
   YP09.mkRegion (Some 9%nat) 0x70 0x78 0 0 [YP09.mkChunk 0x70 (CVal 8 (SOff 34 0))];
   YP09.mkRegion (Some 9%nat) 0xc8 0xd0 0 0 [YP09.mkChunk 0xc8 (CVal 8 (SOff 32 0))]].
Definition b10r_ss : sstate := mkSS PF_BAD sr_atoms b10r_regions None (mkFacts [] [] []).
(* the seed of the `j` at 0x8897c: no region, every register its own atom *)
Definition b10r_ssj : sstate := mkSS PF_BADRET sr_atoms [] None (mkFacts [] [] []).

Lemma b10r_rg_pres : forall (r1 r2 : bvmap 5 word) L, aregs_preserved r1 r2 ->
  Forall (fun rv => acallee_saved (fst rv)) L -> pf_rg r1 L -> pf_rg r2 L.
Proof.
intros r1 r2 L HP HC H. unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hin.
rewrite (HP (fst rv) (HC rv Hin)). exact (H rv Hin).
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma b10r_RL_cs : forall v pos, Forall (fun rv => acallee_saved (fst rv)) (PF_RL v pos).
Proof.
intros v pos. unfold PF_RL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia.
Qed.
Lemma b10r_RM_cs : forall v o ln, Forall (fun rv => acallee_saved (fst rv)) (PF_RM v o ln).
Proof.
intros v o ln. unfold PF_RM. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia.
Qed.
(* pf_fi's six registers (sp, gp, tp, s0, s1, s4 = the shadow base) are callee-saved *)
Lemma b10r_FI_cs : forall B v,
  Forall (fun rv => acallee_saved (fst rv))
    [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v); (20, SHADOW_OFF)].
Proof.
intros B v. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia.
Qed.

(* the environment of the seed at BAD: the registers, then c, cur_name and vp *)
Definition b10r_extra (v : pfv) (pos vp : Z) : list word :=
  [w64 (p_c v); w64 (pf_F v pos + PF_O_CN); w64 vp].
Definition b10r_E (rX : bvmap 5 word) (v : pfv) (pos vp : Z) : env := Eimg (Ereg rX (b10r_extra v pos vp)).
Lemma b10r_E_img : forall rX v pos vp, img_env VAL A_LIM (b10r_E rX v pos vp).
Proof. intros. unfold b10r_E. apply Eimg_env. Qed.
Lemma b10r_E_agree : forall rX v pos vp, env_agree 32 (Ereg rX (b10r_extra v pos vp)) (b10r_E rX v pos vp).
Proof.
intros rX v pos vp. split; [|reflexivity].
intros n Hn. unfold b10r_E. apply Eimg_low. unfold A_TEXT. lia.
Qed.
Lemma b10r_ew_reg : forall rX v pos vp k (r : bv 5), Z.of_nat k = bv_unsigned r ->
  ew (b10r_E rX v pos vp) k = getr rX r.
Proof. intros. unfold b10r_E. apply ew_Eimg_Ereg_nat. assumption. Qed.
Lemma b10r_ew_extra : forall rX v pos vp j, (j < 3)%nat ->
  ew (b10r_E rX v pos vp) (32 + j) = nth j (b10r_extra v pos vp) (Z_to_bv 64 0).
Proof.
intros rX v pos vp j Hj. unfold b10r_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra.
Qed.
Lemma b10r_ew_c : forall rX v pos vp, ew (b10r_E rX v pos vp) 32 = w64 (p_c v).
Proof. intros. exact (b10r_ew_extra rX v pos vp 0 ltac:(lia)). Qed.
Lemma b10r_ew_cn : forall rX v pos vp, ew (b10r_E rX v pos vp) 33 = w64 (pf_F v pos + PF_O_CN).
Proof. intros. exact (b10r_ew_extra rX v pos vp 1 ltac:(lia)). Qed.
Lemma b10r_ew_vp : forall rX v pos vp, ew (b10r_E rX v pos vp) 34 = w64 vp.
Proof. intros. exact (b10r_ew_extra rX v pos vp 2 ltac:(lia)). Qed.

(* the literal a2 holds at the call: listing object 60 is .str.15, F_badrole's text (SegInstB's map) *)
Section o.
Hypothesis OBJ : seg_val_objs (PI := PI).
Lemma b10r_lit_atom : forall E, img_env VAL A_LIM E -> ew E (A_OBJ 60) = w64 (seg_litA_rc F_badrole).
Proof.
intros E HE. rewrite (img_env_atomP E (A_OBJ 60) HE) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
rewrite (OBJ 60%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.
End o.

Variable B : asyms.

(* ======================= the `j` at 0x8897c: PF_BADRET -> JOIN ======================= *)
Section j.
Context {fx : YK11.FPState}.
Let LAWSj : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let b10r_RUNTO := SRr_run_to_pi_AJ (fx := fx) B LAWSj.

Lemma b10r_jump : forall n, H_JOIN (fx := fx) B n ->
  forall v pos lyc Sc Wc rX memc mdc cfx nm o ln d gi,
  INV_JOIN (fx := fx) B n v pos lyc Sc Wc rX memc mdc cfx nm o ln d gi ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_BADRET) rX memc mdc) (pf_postm B v (cfx, Some gi, nm) o ln).
Proof.
intros n HJOIN v pos lyc Sc Wc rX memc mdc cfx nm o ln d gi HI.
pose proof HI as (HBASE & HMID & HST & HRG).
pose proof HBASE as (HCX & HFI & HOBJ & HSL & HFSH).
pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
set (E := Eimg (Ereg rX (@nil word))).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr rX r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (HS : st_ok_pi SEGS VAL E b10r_ssj
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_BADRET)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold b10r_ssj. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. exact I.
  - unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor]. }
unfold cfg_at. change (w64 (BASE + PF_BADRET)) with (Z_to_bv 64 (BASE + PF_BADRET)).
paj_run_to_sh b10r_RUNTO HS HJ PF_JOIN.
{ intros a (r & Hr & Ha). unfold b10r_ssj in Hr. cbn [ss_mem In] in Hr. destruct Hr. }
cbn [ms_mem mkst] in HFr, HG, HF.
b10r_clear_md.
assert (Hmem : ms_mem ms = memc).
{ apply functional_extensionality. intros x. unfold frame_of in HF. rewrite HF; [reflexivity|].
  intros (r & Hr & Ha). unfold b10r_ssj in Hr. cbn [ss_mem In] in Hr. destruct Hr. }
assert (QK : forall r, In r [2; 3; 4; 8; 9; 20; 18; 21; 26; 25; 22] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [b10r_rreg HS; rewrite b10r_den_atom0; apply EE; reflexivity |]). destruct Hr. }
pmkst HS.
rewrite Hmem in HJ |- *.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
  change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_JOIN) rg mm mdx) end.
apply (HJOIN v pos lyc Sc Wc (ms_regs ms) memc _ cfx nm o ln d gi).
split.
{ split; [exact HCX|].
  split.
  { split; [exact HJ|]. split; [exact Hly|]. split; [exact HSc|]. split; [exact HPERM|].
    split; [exact HSAV|]. split; [exact HFLAG|]. split; [exact HFRM|]. split; [exact HTF|].
    split; [exact HC8|].
    unfold pf_rg. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
      (rewrite QK; [apply (b10r_rg rX _ _ _ HRG0); b10r_in | b10r_in]). }
  split; [exact HOBJ|]. split; [exact HSL | exact HFSH]. }
split; [exact HMID|].
split; [exact HST|].
unfold pf_rg, PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
  (rewrite QK; [apply (b10r_rg rX _ _ _ HRG); b10r_in | b10r_in]).
Qed.
End j.

Section x.
Context {fx : YK11.FPState}.

(* ======================= the seed at BAD (0x88960) ======================= *)
Lemma b10r_seed : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val,
  INV_BAD B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val ->
  st_ok_pi SEGS VAL (b10r_E rX v pos vp) b10r_ss
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_BAD)) memc (seg_rom SEGS))).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HI.
pose proof HI as (HB & HMID & HST & HVS & HVI & HSL70 & HRH & HRG).
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
destruct (b10r_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HGEO & Hin & EF & Hfrs & HAR & Hceil).
pose proof HGEO as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & Fapp & _).
destruct (b10r_cx B v HCX) as (Hc0 & Hc16 & HcB & _ & _ & _ & _).
pose proof HFI as (HJ & Hly & _ & _ & _ & _ & _ & _ & HC8 & HRG0).
pose proof asan_consts as (C1 & _).
destruct HVI as [HV1 HV2].
set (E := b10r_E rX v pos vp).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr rX r)
  by (intros k r Hk; subst E; apply b10r_ew_reg; exact Hk).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (b10r_rg rX _ 9 _ HRG0); b10r_in).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; apply b10r_w64_u; lia).
(* the three slots *)
assert (W40 : rdword (rdW Wc memc) (pf_s1 v + 0x40) = Some (pf_F v pos + PF_O_CN))
  by (exact (proj1 (Forall_forall _ _) HSL (0x40, pf_F v pos + PF_O_CN) ltac:(unfold PF_SL; b10r_in))).
assert (W70 : rdword (rdW Wc memc) (pf_s1 v + 0x70) = Some vp)
  by (exact (proj1 (Forall_forall _ _) HSL70 (0x70, vp) ltac:(b10r_in))).
assert (WC8 : rdword (rdW Wc memc) (pf_s1 v + 0xc8) = Some (p_c v))
  by (exact (proj1 (Forall_forall _ _) HC8 (0xc8, p_c v) ltac:(b10r_in))).
rewrite restrict_mkst_fx. unfold b10r_ss, b10r_regions. apply pa_entry_st_ok_full.
- subst E. unfold b10r_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite U9.
  + split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ (pf_s1 v) 0x40 8%N (SOff 33 0) (pf_F v pos + PF_O_CN)).
    * rewrite b10r_den_atom0. subst E. rewrite b10r_ew_cn. reflexivity.
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold PF_O_CN. lia.
    * lia.
    * exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ W40).
  + split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ (pf_s1 v) 0x70 8%N (SOff 34 0) vp).
    * rewrite b10r_den_atom0. subst E. rewrite b10r_ew_vp. reflexivity.
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold PF_O_BUF in HV1, HV2. lia.
    * lia.
    * exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ W70).
  + split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ (pf_s1 v) 0xc8 8%N (SOff 32 0) (p_c v)).
    * rewrite b10r_den_atom0. subst E. rewrite b10r_ew_c. reflexivity.
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    * lia.
    * exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ WC8).
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor].
Qed.

(* ======================= the cut JOIN at the FP state refuse returned at ======================= *)
Section m.
Hypothesis VRO : seg_val_relro (PI := PI).
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.

(* from the cut at the call (pf_base at the call's registers regsc; the cut's registers rX hold PF_RL ++ PF_RM),
   refuse's two journals, its post and the callee-saved registers, the walk reaches the post from 0x8897c *)
Lemma b10r_after : forall (fx1 : YK11.FPState) n, H_JOIN (fx := fx1) B n ->
  forall v pos lyc Sc Wc (rX regsc : bvmap 5 word) memc mdq cf nm o ln d gi (val : list Z) ly2 S2
    (W2 : world SEGS) regs2 mem2 md2,
  pf_base (fx := fx) B v pos lyc Sc Wc regsc memc mdq PF_SC_LOW -> pf_mid v o ln d n ->
  pf_st v pos (rdW Wc memc) cf (Some gi) nm (length (skipn o (p_s v))) ->
  pf_rg rX (PF_RL v pos ++ PF_RM v o ln) -> aregs_preserved rX regsc ->
  fxrel fx fx1 ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] ly2 S2 W2 mem2 md2 0 ->
  ajournal SEGS B STK_refuse (pf_s1 v) (refuse_W (p_c v) cf) lyc Sc Wc memc mdq [] ly2 S2 W2 mem2 md2 EV_refuse ->
  aregs_preserved regsc regs2 ->
  sa_rconf (rdW W2 mem2) (p_c v) (refuse cf (ln + 1) F_badrole [AS nm; AS val]) ->
  sa_noalloc B lyc Sc ly2 S2 ->
  SRr SEGS W2 (cfg_at (fx := fx1) SEGS (BASE + PF_BADRET) regs2 mem2 md2)
    (pf_postm (fx := fx1) B v (refuse cf (ln + 1) F_badrole [AS nm; AS val], Some gi, nm) o ln).
Proof.
intros fx1 n HJOIN v pos lyc Sc Wc rX regsc memc mdq cf nm o ln d gi val ly2 S2 W2 regs2 mem2 md2
  HBc HMID HST HRG HPR Hfx1 HJ2 HJc2 HP2 HRC2 HNA2.
destruct HNA2 as (HPERM2 & Hly2 & HS2e).
pose proof HST as (HRC & HCUR & HNM & HCNT & HCURS).
pose proof HMID as (Ho & Hle & Hlctx).
pose proof HBc as (HCX & HFI & _).
destruct (b10r_geo B v pos lyc Sc Wc regsc memc mdq HCX HFI) as (HGEO & _).
pose proof HGEO as (S1 & S2' & S3 & S4 & _).
pose proof (b10r_keeps_refuse B v pos lyc Sc Wc regsc memc mdq PF_SC_LOW cf ly2 S2 W2 mem2 md2 EV_refuse
  HBc HJc2 HPERM2) as HK.
assert (HPR2 : aregs_preserved rX regs2) by exact (aregs_preserved_trans _ _ _ HPR HP2).
assert (HB2 : pf_base (fx := fx1) B v pos ly2 S2 W2 regs2 mem2 md2 PF_SC_LOW).
{ apply (b10r_base_move B VRO SSPX fx1 v pos lyc Sc Wc regsc memc mdq PF_SC_LOW ly2 S2 W2 regs2 mem2 md2
    HBc Hfx1 HJ2 Hly2 HS2e HPERM2 HK).
  intros r Hr. apply HP2. unfold acallee_saved. cbn [In] in Hr. lia. }
pose proof HK as (K1 & K2 & K3 & K4).
assert (HINV2 : INV_JOIN (fx := fx1) B n v pos ly2 S2 W2 regs2 mem2 md2
  (refuse cf (ln + 1) F_badrole [AS nm; AS val]) nm o ln d gi).
{ split; [exact HB2|]. split; [exact HMID|].
  split.
  - split; [exact HRC2|].
    split.
    { cbn [pf_cur_ok] in HCUR |- *. destruct (refuse_proj cf (ln + 1) F_badrole [AS nm; AS val]) as (Hs & _).
      rewrite Hs. exact HCUR. }
    split.
    { apply (b10r_nm_move v pos (rdW Wc memc) _ nm HNM).
      intros a Ha. apply K4. left. exact Ha. }
    split.
    { exact (pf_cnt_refuse cf (ln + 1) F_badrole [AS nm; AS val] _ _
        (pf_next_skipn_lt (p_s v) o Ho) HCNT). }
    rewrite (rdword_ext (rdW Wc memc) (rdW W2 mem2)); [exact HCURS|].
    intros k Hk. apply K1. lia.
  - apply (b10r_rg_pres rX regs2 _ HPR2); [|exact HRG].
    apply Forall_app. split; [apply b10r_RL_cs | apply b10r_RM_cs]. }
exact (b10r_jump (fx := fx1) n HJOIN v pos ly2 S2 W2 regs2 mem2 md2
  (refuse cf (ln + 1) F_badrole [AS nm; AS val]) nm o ln d gi HINV2).
Qed.
End m.
End x.
End d.
