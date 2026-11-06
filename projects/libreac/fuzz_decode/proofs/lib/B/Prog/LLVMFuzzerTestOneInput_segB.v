(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* LLVMFuzzerTestOneInput_segB: segments 2 and 3 of the image-B (asan-ubsan) walk of libreac/fuzz_decode's
   LLVMFuzzerTestOneInput, against their statements in lib/B/Prog/LLVMFuzzerTestOneInput_segs.v:
   - llvm_b_early_ret (llvm_b_early_ret_stmt): +0x104 -> +0xae0. Its start state carries 2 ^ 26 <= n, and the
     slot pre dec_b_base pins n < 2 ^ 26: the edge is never taken.
   - llvm_b_early (llvm_b_early_stmt): +0x074 .. +0x278 and malloc #1, to llvm_b_st_27c. It is cut at +0x258
     (`sd a7, 0(s1)`, where the four mode arms and the n = 0 arm meet): eb_front_fx walks +0x074 .. +0x258 in
     thirteen leaves (n = 0, and n = 1 / 2 / >= 3 times the four modes), eb_tail_fx walks +0x258 .. +0x278, calls
     malloc (YC85 amalloc04_sub) and lands in llvm_b_st_27c. Refuted on the way: the size test's taken edge (+0x104,
     so llvm_b_st_104 is never the post), the length-dispatch edges the size excludes (+0x114, +0x13c, +0x168), the
     ASan report guards +0x130 / +0x158 / +0x1d0 (the token engine's slow-path obligations, discharged from the input
     block's shadow), and the five UBSan guards into +0xb84 (+0x120 / +0x148 / +0x1c0 decided by the input pointer's
     range, +0x260 / +0x270 in eb_tail_fx).
   The walks use the Pa engine of lib/A/Prog (PaRun / PaShadow / PaJournal) over image B's listing
   (lib/B/Prog/DecodeBPa.v, DecodeBPaLib.v, DecodeBImg.v): the plain run for the frame record, its shadow and the
   mode select, the token run for the input reads. The plain run lemmas of fuzz_boxreg's lib/B/Prog/BoxBFrame.v
   (a working branch, from cgif lib/YC44.v) are copied below with the listing's names (dbsym)
   and module paths changed, under the prefix eb_. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YI00 YI0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0s YM05 YImgTop YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YI16.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaRun PaShadow PaJournal YC1g YC1h YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBList DecodeBAddr
  DecodeBPa DecodeBPaLib DecodeBImg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import check_round_trip_cg
  LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* 0. The plain (non-token) run lemmas and region rewindowing           *)
(* ------------------------------------------------------------------ *)
(* BoxBFrame.v set_window / list_upd / ast_ok_set_region / region_ok_rewindow, names prefixed eb_. *)
Definition eb_set_window (r : YP09.region) (wlo whi : Z) : YP09.region :=
YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) wlo whi (YP09.r_chunks r).
Fixpoint eb_list_upd {A} (l : list A) (i : nat) (x : A) : list A :=
match l, i with
| [], _ => []
| _ :: t, O => x :: t
| h :: t, S i' => h :: eb_list_upd t i' x
end.
Lemma eb_zall_disjoint_of_all : forall E r rs,
all_disjoint E r rs -> zall_disjoint (extent_of_region E r) (map (extent_of_region E) rs).
Proof.
intros E r rs. induction rs as [|r' rs IH]; cbn; intros H; [exact I|].
destruct H as [H1 H2]. split; [|exact (IH H2)]. unfold zdisj, extent_of_region, extent_disjoint in *. cbn [fst snd]. exact H1.
Qed.
Lemma eb_zpairwise_of_pairwise : forall E rs,
pairwise_disjoint E rs -> zpairwise_disjoint (map (extent_of_region E) rs).
Proof.
intros E rs. induction rs as [|r rs IH]; cbn; intros H; [exact I|].
destruct H as [H1 H2]. split; [exact (eb_zall_disjoint_of_all E r rs H1) | exact (IH H2)].
Qed.
Lemma eb_map_extent_list_upd : forall E rs i r r',
nth_error rs i = Some r -> extent_of_region E r' = extent_of_region E r ->
map (extent_of_region E) (eb_list_upd rs i r') = map (extent_of_region E) rs.
Proof.
intros E rs. induction rs as [|h t IH]; intros [|i] r r' Hn He; cbn in *; try discriminate.
- injection Hn as ->. rewrite He. reflexivity.
- rewrite (IH i r r' Hn He). reflexivity.
Qed.
Lemma eb_Forall_list_upd : forall {A} (P : A -> Prop) (l : list A) i x,
Forall P l -> P x -> Forall P (eb_list_upd l i x).
Proof.
intros A P l. induction l as [|h t IH]; intros [|i] x Hl Hx; cbn; [exact Hl | exact Hl | |]; inversion Hl; subst; constructor; auto.
Qed.
Section ebf. Context {fx : YK11.FPState}.
Lemma eb_region_ok_rewindow : forall segs E m r wlo whi,
region_ok segs E m r ->
(forall o, wlo <= o < whi -> writable_at segs m (base_val E (YP09.r_base r) + o)) ->
region_ok segs E m (eb_set_window r wlo whi).
Proof.
intros segs E m r wlo whi (H1 & H2 & H3 & H4) Hw. unfold region_ok, eb_set_window.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [exact H1|]. split; [exact H2|]. split; [exact Hw | exact H4].
Qed.
Lemma eb_st_ok_set_region : forall segs E ss ms i r r',
st_ok segs E ss ms -> nth_error (ss_mem ss) i = Some r ->
extent_of_region E r' = extent_of_region E r ->
regions_wf (eb_list_upd (ss_mem ss) i r') = true ->
region_ok segs E (ms_mem ms) r' ->
st_ok segs E (mkSS (ss_pc ss) (ss_regs ss) (eb_list_upd (ss_mem ss) i r') (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros segs E ss ms i r r' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hn He Hwf' Hr'.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9].
split; [exact Hwf'|]. split; [exact (eb_Forall_list_upd _ _ i r' Hok Hr')|].
apply pairwise_disjoint_of_extents. rewrite (eb_map_extent_list_upd E _ i r r' Hn He).
apply eb_zpairwise_of_pairwise. exact Hpd.
Qed.
End ebf.

Section eb0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation SEGS := decodesegsB0.
#[local] Notation PI := (@PI_decodeb rc).
#[local] Notation VAL := (@pa_val _ decodeb_listing PI).
Lemma eb_st_ok_pi_set_region : forall E ss ms i r r',
st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r ->
extent_of_region E r' = extent_of_region E r ->
regions_wf (eb_list_upd (ss_mem ss) i r') = true ->
region_ok SEGS E (ms_mem ms) r' ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) (eb_list_upd (ss_mem ss) i r') (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms i r r' HS Hn He Hw Hr. destruct ss as [p0 r0 f0 m0 v0 g0].
exact (eb_st_ok_set_region SEGS E _ ms i r r' HS Hn He Hw Hr).
Qed.
(* Re-window region i of the symbolic memory (its bytes and chunks unchanged). *)
Lemma eb_rewindow : forall E ss ms i r wlo whi,
st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r ->
regions_wf (eb_list_upd (ss_mem ss) i (eb_set_window r wlo whi)) = true ->
(forall o, wlo <= o < whi -> writable_at SEGS (ms_mem ms) (base_val E (YP09.r_base r) + o)) ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) (eb_list_upd (ss_mem ss) i (eb_set_window r wlo whi)) (ss_resv ss)
  (ss_facts ss)) ms.
Proof.
intros E ss ms i r wlo whi HS Hn Hw Hwr.
apply (eb_st_ok_pi_set_region E ss ms i r); [exact HS | exact Hn | destruct r; reflexivity | exact Hw |].
apply eb_region_ok_rewindow; [|exact Hwr].
destruct ss as [p0 r0 f0 m0 v0 g0].
exact (st_ok_region_nth (segs := SEGS) E _ ms i r HS Hn).
Qed.
End eb0.

(* BoxBFrame.v SRr_run_pi_AJ / SRr_run_to_pi_AJ: a plain run (no shadow tokens) under the caller's journal. *)
Section eb1. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {L : ptable dbsym} {PL : PAListing L} {PI : PAImg L}.
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
Definition eb_run_post_pi_AJ (W : world SEGS) (E : env) (ss ss' : sstate)
(ms : machine_state) (STK sp0 : Z) (FP : list (Z * Z)) ly S W0 mem md own lyc Sc (mdc : Model) (k : Z)
(Q : world SEGS -> config -> Prop) : Prop :=
forall ms' mat',
st_ok_pi SEGS VAL E ss' (restrict (w_H W) ms') ->
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
SRr SEGS W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
Definition eb_plain_stop (st : prun_status dbsym) : Prop :=
match st with PRS_running | PRS_stopped _ => True | _ => False end.
Lemma eb_run_to_pi_AJ : forall W n stop E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q,
img_env VAL A_LIM E ->
st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
sym_run_toN_pi pl_tpi n stop ss = (ss', st) -> eb_plain_stop st ->
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
eb_run_post_pi_AJ W E ss ss' ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q ->
SRr SEGS W (mkCfg ms mdc) Q.
Proof.
intros W n stop E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q HE HS Hrun Hst HJ Hwr Hk.
unfold sym_run_toN_pi in Hrun. rewrite <- pl_tpi_eq in Hrun.
destruct (PaRun.sym_run_to_pi_sound dbsym SEGS (clookup pa_tbl) VAL pa_sigma L pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim
_ _ E ss ss' st _ HE HS Hrun) as (msr' & Hms & HP & _ & Hfr).
eapply (SRr_chain_AJ SEGS B LAWS pa_segs_low pa_wx W E (abs_ss VAL ss) (abs_ss VAL ss') ms msr');
[ exact Hms | destruct st; cbn [prun_post] in HP; first [exact HP | destruct Hst] | destruct ss; exact Hfr | exact HJ | destruct ss; exact Hwr | ].
intros ms' mat' HS' HJ' HF HF' HG. apply (Hk ms' mat' HS' HJ'); destruct ss; first [exact HF | exact HF' | exact HG].
Qed.
End eb1.
Ltac eb_after_run_plain HS HJ :=
let ms' := fresh "ms" in let mat := fresh "mat" in
let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in
intros ms' mat HS HJ HF HFr HG;
cbn [ms_mem YK11.mkst] in HF, HFr, HG;
try lazymatch goal with |- SRr _ _ (mkCfg _ ?md) _ =>
  lazymatch md with
  | with_vm_backing _ _ _ => let mdv := fresh "mdv" in set (mdv := md) in *; clearbody mdv
  end
end.
Ltac eb_run_to_sh RUNTOP HS HJ stop :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of RUNTOP with
| forall W n stop E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q, _ -> _ -> sym_run_toN_pi ?tpi n stop ss = _ -> _ =>
let r := eval vm_compute in (sym_run_toN_pi tpi FUEL stop ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_pi tpi FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "eb_run_to_sh: no hypothesis  img_env _ _ E" end in
eapply (RUNTOP W FUEL stop E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun I HJ);
[ clear Hrun | clear Hrun HS HJ; eb_after_run_plain HS HJ ]
end
end
| _ => fail "eb_run_to_sh: HS must be  st_ok_pi segs val E ss (restrict (w_H W) ms)"
end.

(* ------------------------------------------------------------------ *)
(* 1. The mode tables                                                    *)
(* ------------------------------------------------------------------ *)
(* The three 12-byte mode tables {rate, nch, ns} of the read-only load that the RELRO words decodeb_obj 4 / 5 / 6
   point to, as fuzz_decode.asan-ubsan holds them (read from the pinned image: 0x99f60 -> 0x20d60 {44100, 40, 12},
   0x99f68 -> 0x20da0 {96000, 40, 12}, 0x99f70 -> 0x20d80 {48000, 40, 12}). *)
Definition DEC_TAB4 : Z := 0x20d60.
Definition DEC_TAB5 : Z := 0x20da0.
Definition DEC_TAB6 : Z := 0x20d80.
Definition DEC_TAB_NCH : Z := 40.
Definition DEC_TAB_NS : Z := 12.
(* The three as_const rows of dec_crt_cells that hold the mode tables' pointer words. The tables' two fields are
   not rows: the walk reads them through the image view (DEC_RO_RD, eb_rom_view_rd / eb_rom_val below). *)
Definition eb_mode_cells (B : asyms) : Prop :=
  forall ly,
    In (z8 (ANum (decodeb_obj 4)) DEC_TAB4) (as_const B ly) /\
    In (z8 (ANum (decodeb_obj 5)) DEC_TAB5) (as_const B ly) /\
    In (z8 (ANum (decodeb_obj 6)) DEC_TAB6) (as_const B ly).

Section eb. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := dec_B_sink_head.
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := decodesegsB0.
Local Abbreviation rd W mem := (mrestrict (w_H W) mem).
(* The three pointer-word rows of the statement's dec_crt_cells, picked by their type. *)
Lemma eb_mode_cells_of : dec_crt_cells B -> eb_mode_cells B.
Proof.
intros H ly. specialize (H ly). unfold DEC_TAB4, DEC_TAB5, DEC_TAB6.
repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
split; [assumption | split; assumption].
Qed.
#[local] Notation BASE_OK := (dec_b_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI).

(* ------------------------------------------------------------------ *)
(* 2. +0x104 -> +0xae0: never taken                                      *)
(* ------------------------------------------------------------------ *)
Theorem llvm_b_early_ret :
  llvm_b_early_ret_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
unfold llvm_b_early_ret_stmt.
intros LAWS MTL cx W' c' HB _ H104. exfalso.
destruct H104 as (fx' & ly' & S' & regs' & mem' & md' & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hn & _).
unfold dec_b_base, dec_lib_pre_x in HB.
destruct HB as (_ & _ & _ & _ & Hn' & _). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The cut at +0x258                                                 *)
(* ------------------------------------------------------------------ *)
(* +0x258 (`sd a7, 0(s1)`): the four mode arms (+0x254) and the n = 0 arm (+0x1ac) meet. The frame record and its
   poison are written, the local is unpoisoned and holds the geometry the mode reads (when the mode is the local),
   the frame is in a7 and in the spill slots 8 / 16 / 112, and malloc #1 is ahead. *)
Definition eb_mid (cx : dctx) : world segs -> config -> Prop :=
  fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md' (mode nch ns : Z),
    c' = mkCfg (@YK11.mkst fx' regs' (w64 (DEC_A_LLVMF + 0x258)) mem' (YK11.seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    dec_b_core B cx ly' S' W' regs' mem' md' 0 /\
    ablocks B ly' S' = ablocks B (d_ly cx) (d_S cx) /\
    mo_le MT (d_S cx) S' 0 /\ mo_ok MT S' (dec_rest_074 MT (d_n cx)) /\
    YK11.getr regs' 17 = w64 (d_F cx) /\
    YK11.getr regs' 18 = w64 SHADOW_OFF /\
    YK11.getr regs' 19 = w64 (d_n cx) /\
    YK11.getr regs' 24 = w64 (d_p cx + dec_b_u (d_n cx)) /\
    YK11.getr regs' 20 = w64 (dec_b_len (d_n cx)) /\
    YK11.getr regs' 21 = w64 mode /\
    YK11.getr regs' 23 = w64 (mode + 4) /\
    YK11.getr regs' 22 = w64 (mode + 8) /\
    dec_b_mode_ok cx W' mem' mode nch ns /\
    ((mode = DEC_TAB4 \/ mode = DEC_TAB5 \/ mode = DEC_TAB6) /\ nch = DEC_TAB_NCH /\ ns = DEC_TAB_NS \/
     mode = d_F cx + 32) /\
    dec_b_fsh cx (aview segs (w_H W') mem') 0 4 /\
    dec_b_slot cx (aview segs (w_H W') mem') 8 (d_SH cx) /\
    dec_b_slot cx (aview segs (w_H W') mem') 16 (d_F cx) /\
    dec_b_slot cx (aview segs (w_H W') mem') 112 (d_F cx).

(* ---- memory facts a step keeps ---- *)
Lemma eb_rdword_keep : forall (r r' : reader) a v,
  (forall i, 0 <= i < 8 -> r' (a + i) = r (a + i)) -> rdword r a = Some v -> rdword r' a = Some v.
Proof.
intros r r' a v Hk Hr. unfold rdword in *.
pose proof (Hk 0 ltac:(lia)) as K0. rewrite Z.add_0_r in K0.
pose proof (Hk 1 ltac:(lia)) as K1. pose proof (Hk 2 ltac:(lia)) as K2. pose proof (Hk 3 ltac:(lia)) as K3.
pose proof (Hk 4 ltac:(lia)) as K4. pose proof (Hk 5 ltac:(lia)) as K5. pose proof (Hk 6 ltac:(lia)) as K6.
pose proof (Hk 7 ltac:(lia)) as K7.
rewrite K0, K1, K2, K3, K4, K5, K6, K7. exact Hr.
Qed.
Lemma eb_saved_keep : forall cx (r r' : reader),
  (forall a, d_sp0 cx - 104 <= a < d_sp0 cx -> r' a = r a) -> dec_b_saved cx r -> dec_b_saved cx r'.
Proof.
intros cx r r' Hk H. unfold dec_b_saved in *. rewrite Forall_forall in *. intros o Hin.
apply (eb_rdword_keep r r'); [|exact (H o Hin)].
assert (Hb : 8 <= fst o <= 104).
{ unfold dec_b_saved_at in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin]; [cbn [fst]; lia|]). destruct Hin. }
intros i Hi. apply Hk. lia.
Qed.
Lemma eb_fsh_keep : forall cx (r r' : reader) b4 b5,
  (forall i, 0 <= i < 8 -> r' (d_SH cx + i) = r (d_SH cx + i)) -> dec_b_fsh cx r b4 b5 -> dec_b_fsh cx r' b4 b5.
Proof.
intros cx r r' b4 b5 Hk (H1 & H2 & H3 & H4).
split; [intros i Hi; rewrite Hk by lia; exact (H1 i Hi)|].
split; [rewrite Hk by lia; exact H2|]. split; [rewrite Hk by lia; exact H3|].
intros i Hi. rewrite Hk by lia. exact (H4 i Hi).
Qed.
Lemma eb_slot_keep : forall cx (r r' : reader) off v,
  (forall i, 0 <= i < 8 -> r' (d_sp1 cx + off + i) = r (d_sp1 cx + off + i)) ->
  dec_b_slot cx r off v -> dec_b_slot cx r' off v.
Proof. intros cx r r' off v Hk H. unfold dec_b_slot in *. exact (eb_rdword_keep r r' _ v Hk H). Qed.
Lemma eb_val_mem_moved : forall H H' (m m' : word -> option byte) a n v,
  (forall k, 0 <= k < Z.of_nat n -> aview segs H' m' (a + k) = aview segs H m (a + k)) ->
  val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v Hk Hv k Hkn. specialize (Hk (Z.of_nat k) ltac:(lia)). unfold aview in Hk.
rewrite (Hv k Hkn) in Hk. destruct (mbyte segs (mrestrict H' m') (a + Z.of_nat k)) as [b'|]; cbn in Hk; [|discriminate].
injection Hk as Hk. f_equal. apply bv_eq. exact Hk.
Qed.
Lemma eb_garr8_keep : forall H H' (m m' : word -> option byte) a l,
  (forall i, 0 <= i < Z.of_nat (length l) -> aview segs H' m' (a + i) = aview segs H m (a + i)) ->
  garr8 segs (mrestrict H m) a l -> garr8 segs (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hb]. split; [|exact Hb].
apply (eb_val_mem_moved H H' m m' _ 1 _); [|exact Hv].
intros k Hk1. replace (a + Z.of_nat j + k) with (a + (Z.of_nat j + k)) by lia. apply Hk. lia.
Qed.
Lemma eb_val_mem_of_bytes : forall H (mem : word -> option byte) a (n : nat) v,
  (forall k, (k < n)%nat -> aview segs H mem (a + Z.of_nat k) = Some (le_byte v n k)) ->
  val_mem segs (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hr k Hk. pose proof (Hr k Hk) as Hb.
destruct (aview_byte segs H mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.
Lemma eb_rdword_of_bytes : forall (r : reader) a v, 0 <= v < 2 ^ 64 ->
  (forall k, (k < 8)%nat -> r (a + Z.of_nat k) = Some (le_byte v 8 k)) -> rdword r a = Some v.
Proof.
intros r a v Hv B0. unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (B0 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (B0 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (B0 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (B0 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (B0 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (B0 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (B0 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (B0 7%nat) by lia.
f_equal. apply le_bytes8. exact Hv.
Qed.
Lemma eb_rdword_of_val_mem : forall H (mem : word -> option byte) a v,
  val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H mem) a = Some v.
Proof.
intros H mem a v Hv Hr. apply eb_rdword_of_bytes; [exact Hr|].
intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia.
Qed.
(* The mode tables' rows as AR's const law shows them at any state. *)
Lemma eb_cell8 : forall ly S (W : world segs) mem md a v, AR segs B ly S W mem md ->
  In (z8 (ANum a) v) (as_const B ly) -> 0 <= v < 2 ^ 64 -> rdword (aview segs (w_H W) mem) a = Some v.
Proof.
intros ly S W mem md a v HAR Hin Hv. pose proof (am_const _ _ _ _ (proj1 HAR)) as HK. rewrite Forall_forall in HK.
specialize (HK _ Hin). unfold cell_holds in HK. cbn [z8 c8 c_at c_w c_val aeval] in HK.
apply eb_rdword_of_bytes; [exact Hv | exact HK].
Qed.
(* The DEC_RO_RD bytes show the image's read-only bytes at any state of the slot's journal: the entry's rom_view
   (dec_b_rom) carried by the journal's image clause (YCbq.v:362), which dec_ro_rd_scoped opens at every DEC_RO_RD
   byte (lib/B/Prog/LLVMFuzzerTestOneInput_segX_exit_defs.v ex_rom_rd). *)
Lemma eb_rom_view_rd : forall cx STK own ly' S' (W' : world segs) mem' md' k,
  dec_ro_rd_unowned B -> dec_rom_no_errno B -> dec_b_rom cx ->
  @ajournal rc tfib_sink_head segs B STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    own ly' S' W' mem' md' k ->
  dec_rom_view_rd W' mem'.
Proof.
intros cx STK own ly' S' W' mem' md' k HO HE HR HJ a Ha.
destruct (dec_ro_rd_rom_clean a Ha) as [Hrom _].
destruct (dec_ro_rd_scoped B HO HE a Ha) as [Hno Hne].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (HR a Hrom) | | exact Hno | exact Hne | apply fp_spares_closed; exact sink_closed_nil].
destruct Hrom as (sg & Hin & _ & Hr). exists sg. split; [exact Hin | lia].
Qed.
(* n bytes at a inside one DEC_RO_RD range, read as the image holds them (the check is closed: vm_compute). *)
Lemma eb_rom_val : forall (W : world segs) mem lo m a (n : nat) v,
  dec_rom_view_rd W mem -> In (lo, m) DEC_RO_RD -> lo <= a -> a + Z.of_nat n <= lo + m ->
  forallb (fun k => match YK11.seg_rom segs (Z_to_bv 64 (a + Z.of_nat k)) with
                    | Some b => bv_unsigned b =? le_byte v n k | None => false end) (seq 0 n) = true ->
  val_mem segs (rd W mem) a n v.
Proof.
intros W mem lo m a n v HV Hin H1 H2 HC.
apply eb_val_mem_of_bytes. intros k Hk.
rewrite HV by (apply Exists_exists; exists (lo, m); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
rewrite forallb_forall in HC. specialize (HC k ltac:(apply in_seq; lia)).
destruct (YK11.seg_rom segs (Z_to_bv 64 (a + Z.of_nat k))) as [b|]; [|discriminate HC].
apply Z.eqb_eq in HC. cbn [option_map]. rewrite HC. reflexivity.
Qed.
Lemma eb_mode_ok_tab : forall cx ly S (W : world segs) mem md mode, dec_crt_cells B -> AR segs B ly S W mem md ->
  dec_rom_view_rd W mem ->
  (mode = DEC_TAB4 \/ mode = DEC_TAB5 \/ mode = DEC_TAB6) ->
  dec_b_mode_ok cx W mem mode DEC_TAB_NCH DEC_TAB_NS.
Proof.
intros cx ly S W mem md mode HC HAR HV Hm.
destruct (eb_mode_cells_of HC ly) as (P4 & P5 & P6).
unfold dec_b_mode_ok, DEC_TAB_NCH, DEC_TAB_NS in *.
change (40 mod 2 ^ 32) with 40. change (12 mod 2 ^ 32) with 12.
destruct Hm as [-> | [-> | ->]].
- split; [left; apply (eb_cell8 ly S W mem md); [exact HAR | exact P4 | unfold DEC_TAB4; lia]|].
  split; [lia|]. split; [lia|]. unfold DEC_TAB4.
  split; (apply (eb_rom_val W mem 0x20d64 8);
    [ exact HV | unfold DEC_RO_RD; repeat (first [left; reflexivity | right]) | lia | lia | vm_compute; reflexivity ]).
- split; [right; left; apply (eb_cell8 ly S W mem md); [exact HAR | exact P5 | unfold DEC_TAB5; lia]|].
  split; [lia|]. split; [lia|]. unfold DEC_TAB5.
  split; (apply (eb_rom_val W mem 0x20da4 8);
    [ exact HV | unfold DEC_RO_RD; repeat (first [left; reflexivity | right]) | lia | lia | vm_compute; reflexivity ]).
- split; [right; right; left; apply (eb_cell8 ly S W mem md); [exact HAR | exact P6 | unfold DEC_TAB6; lia]|].
  split; [lia|]. split; [lia|]. unfold DEC_TAB6.
  split; (apply (eb_rom_val W mem 0x20d84 8);
    [ exact HV | unfold DEC_RO_RD; repeat (first [left; reflexivity | right]) | lia | lia | vm_compute; reflexivity ]).
Qed.
Lemma eb_mode_ok_local_keep : forall cx (W W' : world segs) mem mem' nch ns,
  (forall a, d_F cx + 36 <= a < d_F cx + 44 -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  dec_b_mode_ok cx W mem (d_F cx + 32) nch ns -> dec_b_mode_ok cx W' mem' (d_F cx + 32) nch ns.
Proof.
intros cx W W' mem mem' nch ns Hk (_ & Hn1 & Hn2 & Hv4 & Hv8).
split; [right; right; right; reflexivity|]. split; [exact Hn1|]. split; [exact Hn2|].
split; [apply (eb_val_mem_moved (w_H W) (w_H W') mem mem' _ 4 _); [|exact Hv4]
       | apply (eb_val_mem_moved (w_H W) (w_H W') mem mem' _ 4 _); [|exact Hv8]];
  intros k Hk4; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hk4; apply Hk; lia.
Qed.
(* What the rest of the walk may still spend after malloc #1. *)
Lemma eb_rest_27c_nonneg : ameter_laws MT -> 0 <= dec_rest_27c MT.
Proof.
intros ML. unfold dec_rest_27c, dec_rest_418, dec_rest_5cc, dec_rest_6f0, dec_rest_840, dec_rest_96c, dec_crt_cost_max.
pose proof (mo_free_nonneg MT ML).
pose proof (mo_malloc_nonneg MT ML 48387 ltac:(lia)). pose proof (mo_malloc_nonneg MT ML 1920 ltac:(lia)).
pose proof (mo_malloc_nonneg MT ML 1016 ltac:(lia)). pose proof (mo_malloc_nonneg MT ML 1440 ltac:(lia)).
lia.
Qed.
(* The call chain a callee of this function sees: its own frame record (ra at sp0 - 8, the caller's s0 at sp0 - 16)
   on top of the entry's empty chain (boxreg BoxBLxDefs.v lch / lx_achain). *)
Definition eb_ch (cx : dctx) : list (Z * Z * Z) :=
  if d_sp0 cx + 16 <? ly_top (d_ly cx) then [(d_sp0 cx, raZ (d_regs cx), s0Z (d_regs cx))] else [].
Lemma eb_chain_at : forall cx ly' S' (W' : world segs) mem' md' k (regsT : bvmap 5 word),
  BASE_OK cx ->
  @ajournal rc tfib_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly' S' W' mem' md' k ->
  dec_b_saved cx (aview segs (w_H W') mem') ->
  spZ regsT = d_sp1 cx -> s0Z regsT = d_sp0 cx -> 4096 <= raZ regsT ->
  d_sp0 cx - 240 <= d_sp1 cx <= d_sp0 cx - 224 ->
  chain_pre ly' (aview segs (w_H W') mem') regsT (eb_ch cx).
Proof.
intros cx ly' S' W' mem' md' k regsT HB HJ Hsv Hsp Hs0 Hra Hsp1.
pose proof HB as (HPRE & _). pose proof HPRE as (_ & _ & Hra4 & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & _ & H47 & _ & Htop & Htop2).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & HF1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _).
change DEC_LLVMF_STK with 32768 in *. unfold d_sp0 in *.
apply (achain_chain_pre ly' _ (d_sp1 cx) (spZ (d_regs cx)) _ regsT); [| lia | exact Hs0 | exact Hra].
apply (achain_ly_top (d_ly cx)); [exact Etop|].
unfold eb_ch, d_sp0. destruct (Z.ltb_spec (spZ (d_regs cx) + 16) (ly_top (d_ly cx))) as [Hlt | Hge].
- assert (Hal8 : spZ (d_regs cx) mod 8 = 0).
  { pose proof (Z.div_mod (spZ (d_regs cx)) 16 ltac:(lia)) as D. rewrite Hal16, Z.add_0_r in D. rewrite D.
    replace (16 * (spZ (d_regs cx) / 16)) with ((2 * (spZ (d_regs cx) / 16)) * 8) by lia. apply Z_mod_mult. }
  unfold dec_b_saved, dec_b_saved_at in Hsv. rewrite Forall_forall in Hsv.
  pose proof (Hsv (8, 1) ltac:(cbn; auto)) as H8. pose proof (Hsv (16, 8) ltac:(cbn; auto)) as H16.
  cbn [fst snd] in H8, H16.
  apply (achain_push _ _ _ _ _ _ _ _ Hch); [lia | | exact H8 | exact H16 | exact Hra4 | lia | exact Hal8 | lia | lia].
  intros a Ha. apply HF1; lia.
- left. split; [right; left; lia | reflexivity].
Qed.
Lemma eb_trace_at : forall cx (regsT : bvmap 5 word),
  BASE_OK cx -> dec_llvmf_utraces RA_LLVMF B -> raZ regsT = DEC_A_LLVMF + 0x27c ->
  In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT (eb_ch cx)) (as_universe B).
Proof.
intros cx regsT HB HU Hra. pose proof HB as (_ & Hra_eq & _).
unfold eb_ch. destruct (_ <? _).
- destruct (HU [RA_LLVMF] ltac:(cbn; auto)) as (Hm & _).
  specialize (Hm (DEC_A_LLVMF + 0x27c) ltac:(unfold DEC_LLVMF_RA_MALLOC; cbn [map In]; auto)).
  unfold call_trace0, unwind_of_chain, dec_utrace in *. cbn [flat_map app] in *.
  rewrite Hra, Hra_eq. exact Hm.
- destruct (HU [] ltac:(cbn; auto)) as (Hm & _).
  specialize (Hm (DEC_A_LLVMF + 0x27c) ltac:(unfold DEC_LLVMF_RA_MALLOC; cbn [map In]; auto)).
  unfold call_trace0, unwind_of_chain, dec_utrace in *. cbn [flat_map app] in *.
  rewrite Hra. exact Hm.
Qed.
Lemma eb_new_block : AR_laws segs B -> forall ly S (W : world segs) mem md l res n,
  AR segs B ly S W mem md -> ablocks B ly S = l ++ [(res, n)] -> 0 < req_size n -> ~ In (res, n) l.
Proof.
intros LAWS ly S W mem md l res n HAR E Hq Hin. apply in_split in Hin as (l1 & l2 & El).
pose proof (sep_blocks_pos segs B LAWS ly S W mem md (res, n) (res, n) l1 l2 [] HAR) as Hd.
rewrite E, El, <- app_assoc in Hd. cbn [app] in Hd. specialize (Hd eq_refl).
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. +0x258 .. +0x278 and malloc #1                                    *)
(* ------------------------------------------------------------------ *)
Section tail. Context {fx : YK11.FPState}.
#[local] Notation PI := (@PI_decodeb rc).
#[local] Notation VAL := (@pa_val rc decodeb_listing PI).
#[local] Notation BASE := (@pa_val rc decodeb_listing PI A_TEXT).
(* The tail's symbolic state: the registers are their own atoms (atom 32 is SHADOW_OFF), and the one region is the
   spill slot 0(s1) the tail writes. *)
Definition eb_Et (regs : bvmap 5 word) : env := Eimg (PI := PI) (Ereg regs [w64 SHADOW_OFF]).
Definition eb_ss_t : sstate :=
  mkSS 600 sr_atoms [YP09.mkRegion (Some 9%nat) 0 8 0 8 []] None
    (mkFacts [(9%nat, mkAF 0x7fff7f800000 (2 ^ 47) 5); (32%nat, mkAF SB SB 0)] [] []).
Lemma eb_Et_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (eb_Et regs) n = YK11.getr regs r.
Proof.
intros regs n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
unfold eb_Et. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.

Ltac eb_atreg HS r Hr :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
Ltac eb_keepreg HS r n Hr :=
  eb_atreg HS r Hr; lazymatch goal with SV0 : forall n, sv_denot ?E (SOff n 0) = ew ?E n |- _ =>
    rewrite SV0 in Hr; lazymatch goal with E := eb_Et ?regs |- _ =>
      unfold E in Hr; rewrite (eb_Et_reg regs n r) in Hr by reflexivity; fold E in Hr end end.
Ltac kp HP2 r := exact (HP2 r ltac:(unfold acallee_saved; lia)).

Ltac eb_keep_of HFr WIN Zs K :=
  lazymatch type of HFr with frame_of ?Ex ?rsx (mrestrict ?Hx ?m0) (mrestrict ?Hx ?m1) =>
    let Hw := fresh "Hw" in
    assert (Hw : windows rsx = [(Some 9%nat, 0, 8)]) by (vm_compute; reflexivity);
    pose proof (kept_of_frame (segs := decodesegsB0) Ex rsx Hx m0 m1 Zs HFr (WIN rsx Hw)) as K; clear Hw
  end.

Lemma eb_tail_fx : forall (cx : dctx) ly S (W : world segs) regs mem md (mode nch ns : Z),
  pc_wrap_malloc (as_code B) = decodeb_sigma DB___interceptor_trampoline_malloc ->
  dec_llvmf_utraces RA_LLVMF B -> dec_crt_cells B -> dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT ->
  @amalloc04_rule fx rc tfib_sink_head segs B MT ->
  BASE_OK cx -> dec_b_rom cx ->
  frm_zero (@fp_csr fx) ->
  dec_b_core B cx ly S W regs mem md 0 ->
  ablocks B ly S = ablocks B (d_ly cx) (d_S cx) ->
  mo_le MT (d_S cx) S 0 -> mo_ok MT S (dec_rest_074 MT (d_n cx)) ->
  YK11.getr regs 17 = w64 (d_F cx) ->
  YK11.getr regs 18 = w64 SHADOW_OFF ->
  YK11.getr regs 19 = w64 (d_n cx) ->
  YK11.getr regs 24 = w64 (d_p cx + dec_b_u (d_n cx)) ->
  YK11.getr regs 20 = w64 (dec_b_len (d_n cx)) ->
  YK11.getr regs 21 = w64 mode ->
  YK11.getr regs 23 = w64 (mode + 4) ->
  YK11.getr regs 22 = w64 (mode + 8) ->
  dec_b_mode_ok cx W mem mode nch ns ->
  ((mode = DEC_TAB4 \/ mode = DEC_TAB5 \/ mode = DEC_TAB6) /\ nch = DEC_TAB_NCH /\ ns = DEC_TAB_NS \/
   mode = d_F cx + 32) ->
  dec_b_fsh cx (aview segs (w_H W) mem) 0 4 ->
  dec_b_slot cx (aview segs (w_H W) mem) 8 (d_SH cx) ->
  dec_b_slot cx (aview segs (w_H W) mem) 16 (d_F cx) ->
  dec_b_slot cx (aview segs (w_H W) mem) 112 (d_F cx) ->
  SRr segs W (mkCfg (@YK11.mkst fx regs (w64 (DEC_A_LLVMF + 0x258)) mem (YK11.seg_rom segs)) md)
    (llvm_b_st_27c B MT cx).
Proof.
intros cx ly S W regs mem md mode nch ns HPCM HUTR HCELLS HOWN HNOERR LAWS MTL AMALLOC HB HROM Hfrm HCORE Hbl Hmle
  Hmok R17 R18 R19 R24 R20 R21 R23 R22 HMOK Hmode HFSH HS8 HS16 HS112.
pose proof HCORE as (HJ & Hfrs & R8 & R9 & Rsp & Hsp1b & Hsp1al & R3 & R4 & Hsaved & HF4096 & HFal & HFpres & HFL
  & Hpin & Hgarr).
pose proof HB as (HPRE & Hra_eq & R10e & R11e & Hpn & Hlen & Hgarr0 & Hfr0 & Hnev & Hlive & Hro & Hrom
  & Hsink & Hfd & Hfs & Hmeta & Hmok0 & Hfrm0).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
pose proof HJ as (HAR1 & Hly & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly HAR0 Hly) as (_ & Efa & _).
assert (HfaS : frame_addr ly DEC_FCLASS (d_fpos cx) = d_F cx) by (rewrite Efa; reflexivity).
assert (Hfin : In (DEC_FCLASS, d_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (Hfb : fs_frame_bytes DEC_FCLASS = 64) by (vm_compute; reflexivity).
destruct (frames_bounds _ _ LAWS _ _ _ _ _ _ _ HAR1 Hfin) as (HFb0 & HFb1 & HFb2).
rewrite HfaS in HFb0, HFb1, HFb2. rewrite Hfb in HFb1, HFb2.
change (DEC_LLVMF_STK) with 32768 in *.
set (E := eb_Et regs).
assert (HEI : img_env VAL A_LIM E) by (unfold E, eb_Et; apply Eimg_env).
assert (E9 : ew E 9 = w64 (d_sp1 cx)) by (unfold E; rewrite (eb_Et_reg regs 9 9%bv) by reflexivity; exact R9).
assert (E32 : ew E 32 = w64 SHADOW_OFF)
  by (unfold E, eb_Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp1 : bv_unsigned (ew E 9) = d_sp1 cx) by (rewrite E9; unfold w64; apply unsigned_lit_small; unfold d_sp0 in *; lia).
assert (HS : st_ok_pi segs VAL E eb_ss_t
  (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 600)) mem (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold eb_ss_t.
  refine (@pa_entry_st_ok_full fx rc decodeb_listing PI E 600 sr_atoms regs _ _ (mrestrict (w_H W) mem) _ _ _ _ _).
  - unfold E, eb_Et. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp1. unfold d_sp0 in *.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply HJpres. lia.
  - cbn. repeat split; exact I.
  - split; [|split; exact I]. cbn [atoms_ok f_atoms]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp1, E32. unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r. unfold SB, SHADOW_OFF, d_sp0 in *.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
assert (SHOK : sh_ok segs (SOff 32 0) [] E (mrestrict (w_H W) mem)) by constructor.
pose proof (@paj_run fx rc tfib_sink_head decodeb_listing PL_decodeb PI B LAWS) as RUN.
pose proof (@paj_branch fx rc decodeb_listing PI) as BR.
change (w64 (DEC_A_LLVMF + 0x258)) with (Z_to_bv 64 (BASE + 600)).
paj_run_tok RUN HS HJ SHOK Bspan.
{ cbn [ss_mem eb_ss_t].
  eapply (awr_ok_cons_stack_off E _ _ _ _ _ _ _ _ _ 9%nat (d_sp1 cx - d_sp0 cx));
    [reflexivity | rewrite Usp1; lia | cbn; lia | cbn; lia | apply awr_ok_nil]. }
(* the UBSan wrap check of body + length (+0x260, `bltu a0, s8` -> +0xb84) *)
assert (E20 : ew E 20 = w64 (dec_b_len (d_n cx))) by (unfold E; rewrite (eb_Et_reg regs 20 20%bv) by reflexivity; exact R20).
assert (E24 : ew E 24 = w64 (d_p cx + dec_b_u (d_n cx))) by (unfold E; rewrite (eb_Et_reg regs 24 24%bv) by reflexivity; exact R24).
assert (Hlen0 : 0 <= dec_b_len (d_n cx) < 2 ^ 26) by (unfold dec_b_len; lia).
set (pu := bv_unsigned (w64 (d_p cx + dec_b_u (d_n cx)))) in *.
assert (Hpu : 0 <= pu < 2 ^ 64) by (unfold pu; apply (bv_unsigned_in_range 64)).
assert (U20 : U E (SOff 20 0) = dec_b_len (d_n cx)) by (apply U_atom; [exact E20 | lia]).
assert (U24 : U E (SOff 24 0) = pu) by (unfold U; cbn [sv_denot]; rewrite E24, Z.add_0_r; unfold pu; rewrite Z_to_bv_bv_unsigned; reflexivity).
(* no wrap: n = 0 adds nothing; otherwise the body ends inside the input block, below the stack *)
assert (HNW : pu + dec_b_len (d_n cx) < 2 ^ 64 /\ (0 < dec_b_len (d_n cx) -> 4096 <= pu)).
{ destruct Hpn as [(Hn0 & _) | ((Hn1 & Hn2) & Hpin0)].
  - rewrite Hn0. unfold dec_b_len. cbn. lia.
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hpin0) as (_ & Hp4096 & Hpceil & _).
    pose proof (req_size_pos (d_n cx) ltac:(lia)) as (_ & Hrq).
    assert (Hpu' : pu = d_p cx + dec_b_u (d_n cx)) by (unfold pu, w64; apply unsigned_lit_small; unfold dec_b_u; lia).
    rewrite Hpu'. unfold dec_b_len, dec_b_u. lia. }
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_ltu_U, U_SAlu, U20, U24 in Hc. cbn [zalu_raw] in Hc.
  unfold zcanon, M64 in Hc. rewrite Z.mod_small in Hc by lia. apply Z.ltb_lt in Hc. lia. }
paj_run_tok RUN HS HJ SHOK Bspan.
{ cbn [ss_mem add_cond].
  eapply (awr_ok_cons_stack_off E _ _ _ _ _ _ _ _ _ 9%nat (d_sp1 cx - d_sp0 cx));
    [reflexivity | rewrite Usp1; lia | cbn; lia | cbn; lia | apply awr_ok_nil]. }
(* the UBSan null-offset check of the body pointer (+0x270, `beqz a0` -> +0xb84): (s8 <> 0) xor (s8 + s4 = 0) is 1 *)
destruct HNW as (HNW1 & HNW2). clear Hc.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_eq_U in Hc. rewrite !U_SAlu, !U_SLit, U20, U24 in Hc. cbn [zalu_raw] in Hc.
  assert (Hz : zcanon (dec_b_len (d_n cx) + pu) = dec_b_len (d_n cx) + pu) by (apply zcanon_id; rewrite M64_val; lia).
  repeat rewrite Hz in Hc. change (zcanon 0) with 0 in Hc. change (zcanon 1) with 1 in Hc.
  destruct (Z.ltb_spec 0 pu); destruct (Z.ltb_spec (dec_b_len (d_n cx) + pu) 1); cbn in Hc; try discriminate;
  try (pose proof (HNW2 ltac:(lia)); lia); lia. }
paj_run_tok RUN HS HJ SHOK Bspan.
{ cbn [ss_mem add_cond].
  eapply (awr_ok_cons_stack_off E _ _ _ _ _ _ _ _ _ 9%nat (d_sp1 cx - d_sp0 cx));
    [reflexivity | rewrite Usp1; lia | cbn; lia | cbn; lia | apply awr_ok_nil]. }
(* the run's three steps wrote only the slot 0(s1) *)
assert (WIN : forall rsx, windows rsx = [(Some 9%nat, 0, 8)] ->
  forall b wlo whi a, In (b, wlo, whi) (windows rsx) -> base_val E b + wlo <= a < base_val E b + whi ->
  d_sp1 cx <= a < d_sp1 cx + 8).
{ intros rsx Hw b wlo whi a Hin Ha. rewrite Hw in Hin. destruct Hin as [Hq | []]. injection Hq as <- <- <-.
  cbn [base_val] in Ha. rewrite Usp1 in Ha. lia. }
eb_keep_of HFr WIN (fun x => d_sp1 cx <= x < d_sp1 cx + 8) K0.
eb_keep_of HFr0 WIN (fun x => d_sp1 cx <= x < d_sp1 cx + 8) K1.
eb_keep_of HFr1 WIN (fun x => d_sp1 cx <= x < d_sp1 cx + 8) K2.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx <= a < d_sp1 cx + 8) ->
  aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) mem a).
{ intros a Ha Hn. etransitivity; [exact (K2 a Ha Hn)|]. etransitivity; [exact (K1 a Ha Hn)|]. exact (K0 a Ha Hn). }
clear K0 K1 K2 HF HFr HG HF0 HFr0 HG0 HF1 HFr1 HG1.
(* the slot 0(s1) holds the frame *)
assert (HS0 : rdword (aview segs (w_H W) (ms_mem ms1)) (d_sp1 cx + 0) = Some (d_F cx)).
{ pose proof (st_ok_region_nth (segs := segs) E _ _ 0 _ HS eq_refl) as HR. cbn [restrict ms_mem] in HR.
  apply eb_rdword_of_val_mem; [|lia].
  apply (field_of_region E _ 9 (d_sp1 cx) _ 0 8 0 8 0 8%N (SOff 17 0) (d_F cx) HR Usp1 ltac:(cbn; auto));
    [ | cbn; lia | cbn; lia ].
  cbn [sv_denot]. rewrite Z.add_0_r. unfold E. rewrite (eb_Et_reg regs 17 17%bv) by reflexivity. rewrite R17.
  unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
(* the registers at the call *)
assert (SV0 : forall n, sv_denot E (SOff n 0) = ew E n)
  by (intros nn; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
eb_atreg HS (1%bv : bv 5) Q1.
assert (Q1' : YK11.getr (ms_regs ms1) 1 = Z_to_bv 64 (BASE + 636)) by (rewrite Q1; exact (codeptr_val E 636 HEI)).
clear Q1. rename Q1' into Q1.
eb_atreg HS (10%bv : bv 5) Q10. rewrite SV0, E20 in Q10.
eb_keepreg HS (2%bv : bv 5) 2%nat Q2. eb_keepreg HS (3%bv : bv 5) 3%nat Q3. eb_keepreg HS (4%bv : bv 5) 4%nat Q4.
eb_keepreg HS (8%bv : bv 5) 8%nat Q8. eb_keepreg HS (9%bv : bv 5) 9%nat Q9.
eb_keepreg HS (18%bv : bv 5) 18%nat Q18. eb_keepreg HS (19%bv : bv 5) 19%nat Q19.
eb_keepreg HS (20%bv : bv 5) 20%nat Q20. eb_keepreg HS (21%bv : bv 5) 21%nat Q21.
eb_keepreg HS (22%bv : bv 5) 22%nat Q22. eb_keepreg HS (23%bv : bv 5) 23%nat Q23.
eb_keepreg HS (24%bv : bv 5) 24%nat Q24.
assert (HraT : raZ (ms_regs ms1) = DEC_A_LLVMF + 0x27c) by (unfold raZ; rewrite Q1; vm_compute; reflexivity).
assert (HspT : spZ (ms_regs ms1) = d_sp1 cx) by (unfold spZ; rewrite Q2; exact Rsp).
assert (Hs0T : s0Z (ms_regs ms1) = d_sp0 cx).
{ unfold s0Z. rewrite Q8, R8. unfold w64. apply unsigned_lit_small. unfold d_sp0 in *. lia. }
(* the memory at the call: the seat's, but for slot 0 *)
assert (Hsaved1 : dec_b_saved cx (aview segs (w_H W) (ms_mem ms1))).
{ apply (eb_saved_keep cx (aview segs (w_H W) mem)); [|exact Hsaved].
  intros a Ha. apply KEEP; unfold d_sp0 in *; lia. }
(* malloc (len) (+0x278) by amalloc04_rule *)
pmkst HS.
change (pa_sigma DB___interceptor_trampoline_malloc) with (decodeb_sigma DB___interceptor_trampoline_malloc).
rewrite <- HPCM.
assert (HnevS : st_nev S < EV_MAX).
{ pose proof HJ as (_ & _ & _ & _ & _ & _ & Hn' & _). unfold DEC_EV_LIB in Hnev. lia. }
assert (Hbb : blocks_bytes S = blocks_bytes (d_S cx)).
{ rewrite (blocks_bytes_bsum B ly S), (blocks_bytes_bsum B (d_ly cx) (d_S cx)), Hbl. reflexivity. }
assert (Hlenn : dec_b_len (d_n cx) <= d_n cx) by (unfold dec_b_len; lia).
pose proof (eb_rest_27c_nonneg MTL) as Hr27.
pose proof (mo_malloc_mono MT MTL (dec_b_len (d_n cx)) (d_n cx) ltac:(lia)) as Hmono.
eapply SRr_mono.
{ eapply (amalloc04_sub (SK := tfib_sink_head) segs B LAWS (@pa_segs_low rc decodeb_listing PI) MT AMALLOC W
    (ms_regs ms1) (ms_mem ms1) 32768 (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly S _ 0 (dec_b_len (d_n cx)) (d_sp1 cx - d_sp0 cx) (YK11.getr (ms_regs ms1) 1)
    (eb_ch cx) HJ Q10).
  - unfold MALLOC_MAX. lia.
  - rewrite Hbb. unfold DEC_LIVE_LIB, LIVE_MAX in *. lia.
  - rewrite HspT. lia.
  - unfold d_sp0 in *. rewrite Zminus_mod, Hsp0al.
    assert (H16 : d_sp1 cx mod 16 = 0).
    { pose proof (Z.div_mod (d_sp1 cx) 32 ltac:(lia)) as D. rewrite Hsp1al, Z.add_0_r in D. rewrite D.
      replace (32 * (d_sp1 cx / 32)) with ((2 * (d_sp1 cx / 32)) * 16) by lia. apply Z_mod_mult. }
    rewrite H16. reflexivity.
  - lia.
  - unfold ASTACK. lia.
  - rewrite Q3. exact R3.
  - rewrite Q4. exact R4.
  - reflexivity.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact HnevS.
  - apply (eb_chain_at cx ly S W (ms_mem ms1) _ 0 (ms_regs ms1) HB HJ Hsaved1 HspT Hs0T); [|lia].
    rewrite HraT. unfold DEC_A_LLVMF, decodeb_text, AF_LLVMFuzzerTestOneInput. lia.
  - exact (eb_trace_at cx (ms_regs ms1) HB HUTR HraT).
  - apply (mo_ok_le MT MTL S _ _ Hmok). unfold dec_rest_074. lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Hres & Hfr2 & Hr4 & Hbl2 & HK & MLE & HJm).
replace (d_sp0 cx + (d_sp1 cx - d_sp0 cx) - ASTACK) with (d_sp1 cx - ASTACK) in HK by lia.
replace (d_sp0 cx + (d_sp1 cx - d_sp0 cx)) with (d_sp1 cx) in HK by lia.
change (0 + 1) with 1 in HJ2.
pose proof HK as (HK1 & HK2 & HK3 & HK4 & HK5 & HK6).
pose proof HJ2 as (HAR2 & Hly2 & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR0 Hly2) as (_ & Efa2 & _).
assert (HfaS2 : frame_addr ly2 DEC_FCLASS (d_fpos cx) = d_F cx) by (rewrite Efa2; reflexivity).
assert (Hfin2 : In (DEC_FCLASS, d_fpos cx) (frames S2)) by (rewrite Hfr2, Hfrs; left; reflexivity).
assert (Hrin2 : In (res, dec_b_len (d_n cx)) (ablocks B ly2 S2)) by (rewrite Hbl2; apply in_or_app; right; left; reflexivity).
pose proof (sep_block_frame segs B LAWS _ _ _ _ _ _ _ _ _ HAR2 Hrin2 Hfin2) as HdF.
unfold zdisjoint in HdF. cbn [fst snd] in HdF. rewrite HfaS2, Hfb in HdF.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hrin2) as (_ & Hres4096 & Hresceil & Hresapp & _).
pose proof (req_size_pos (dec_b_len (d_n cx)) ltac:(lia)) as (Hrq1 & Hrq2).
assert (Hsp1c : alloc_ceiling + 4096 <= d_sp1 cx) by (unfold d_sp0 in *; lia).
assert (HFd8 : 0 <= d_F cx / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hresapp, HFb2.
(* what the call kept: the frame and its shadow (HK4), the stack above sp1 (HK1), then what the run kept *)
assert (FK : forall a, d_F cx <= a < d_F cx + 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a).
{ intros a Ha. transitivity (aview segs (w_H W) (ms_mem ms1) a).
  - apply (HK4 DEC_FCLASS (d_fpos cx) a Hfin).
    + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite HfaS, Hfb. lia.
    + cbv beta. lia.
  - apply KEEP; lia. }
assert (FSK : forall a, d_SH cx <= a < d_SH cx + 8 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a).
{ intros a Ha. unfold d_SH, shadow_addr, SHADOW_OFF in Ha. transitivity (aview segs (w_H W) (ms_mem ms1) a).
  - apply (HK4 DEC_FCLASS (d_fpos cx) a Hfin).
    + right. unfold in_zr. cbn [fst snd]. rewrite HfaS, Hfb. unfold shadow_addr, SHADOW_OFF. change (64 / 8) with 8. lia.
    + cbv beta. lia.
  - apply KEEP; lia. }
assert (SK : forall a, d_sp1 cx + 8 <= a < d_sp0 cx -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a).
{ intros a Ha. unfold d_sp0 in *. transitivity (aview segs (w_H W) (ms_mem ms1) a).
  - apply HK1; unfold ASTACK; lia.
  - apply KEEP; lia. }
assert (Hnew : ~ In (res, dec_b_len (d_n cx)) (ablocks B ly S))
  by (apply (eb_new_block LAWS ly2 S2 W2 mem2 md2 _ _ _ HAR2 Hbl2); lia).
assert (PK : forall i, 0 <= i < Z.of_nat (length (map (fun b : byte => bv_unsigned b) (d_pl cx))) ->
  aview segs (w_H W2) mem2 (d_p cx + i) = aview segs (w_H W) mem (d_p cx + i)).
{ intros i Hi. rewrite length_map, <- Hlen in Hi.
  assert (Hpin1 : In (d_p cx, d_n cx) (ablocks B ly S)) by (apply Hpin; lia).
  assert (Hpin2 : In (d_p cx, d_n cx) (ablocks B ly2 S2)) by (rewrite Hbl2; apply in_or_app; left; exact Hpin1).
  assert (Hne : (d_p cx, d_n cx) <> (res, dec_b_len (d_n cx))) by (intros Heq; rewrite Heq in Hpin1; exact (Hnew Hpin1)).
  pose proof (sep_blocks segs B LAWS _ _ _ _ _ _ _ _ _ HAR2 Hpin2 Hrin2 Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hpin2) as (_ & Hp4096 & Hpceil & _).
  pose proof (req_size_pos (d_n cx) ltac:(lia)) as (_ & Hrqn).
  transitivity (aview segs (w_H W) (ms_mem ms1) (d_p cx + i)).
  - apply (HK2 (d_p cx) (d_n cx) i Hpin1); [lia | cbv beta; lia].
  - apply KEEP; lia. }
unfold llvm_b_st_27c. cbv beta.
exists fx, ly2, S2, regs2, mem2, md2, res, mode, nch, ns.
split; [rewrite Q1; reflexivity|].
split; [exact Hfrm|].
split.
{ unfold dec_b_core.
  split; [exact HJ2|].
  split; [rewrite Hfr2; exact Hfrs|].
  split; [transitivity (YK11.getr (ms_regs ms1) 8); [kp HP2 8 | rewrite Q8; exact R8]|].
  split; [transitivity (YK11.getr (ms_regs ms1) 9); [kp HP2 9 | rewrite Q9; exact R9]|].
  split; [rewrite <- Rsp; unfold spZ; f_equal; transitivity (YK11.getr (ms_regs ms1) 2); [kp HP2 2 | exact Q2]|].
  split; [exact Hsp1b|]. split; [exact Hsp1al|].
  split; [transitivity (YK11.getr (ms_regs ms1) 3); [kp HP2 3 | rewrite Q3; exact R3]|].
  split; [transitivity (YK11.getr (ms_regs ms1) 4); [kp HP2 4 | rewrite Q4; exact R4]|].
  split; [apply (eb_saved_keep cx (aview segs (w_H W) mem)); [|exact Hsaved]; intros a Ha; apply SK; lia|].
  split; [exact HF4096|]. split; [exact HFal|].
  split; [intros a Ha; destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR2 Hfin2) as (_ & _ & HFp & _);
          rewrite HfaS2, Hfb in HFp; exact (proj1 (HFp a Ha))|].
  split; [apply (eb_rdword_keep (aview segs (w_H W) mem)); [|exact HFL]; intros i Hi; apply FK; lia|].
  split; [intros Hn; rewrite Hbl2; apply in_or_app; left; exact (Hpin Hn)|].
  exact (eb_garr8_keep (w_H W) (w_H W2) mem mem2 _ _ PK Hgarr). }
split; [rewrite Hbl2, Hbl; reflexivity|].
split; [exact Hr4|].
split; [unfold dec_spent_27c; apply (mo_le_mono MT MTL _ _ (0 + mo_malloc MT (dec_b_len (d_n cx))));
        [exact (mo_le_trans MT MTL _ _ _ _ _ Hmle MLE) | lia]|].
split; [apply (mo_ok_step MT MTL S S2 (mo_malloc MT (dec_b_len (d_n cx))) _);
        [apply (mo_ok_le MT MTL S _ _ Hmok); unfold dec_rest_074; lia | exact MLE]|].
split.
{ split; [|split].
  - apply (eb_slot_keep cx (aview segs (w_H W) (ms_mem ms1))); [|exact HS0].
    intros i Hi. unfold d_sp0 in *. apply HK1; unfold ASTACK; lia.
  - apply (eb_slot_keep cx (aview segs (w_H W) mem)); [|exact HS8]. intros i Hi. apply SK. unfold d_sp0 in *. lia.
  - apply (eb_slot_keep cx (aview segs (w_H W) mem)); [|exact HS16]. intros i Hi. apply SK. unfold d_sp0 in *. lia. }
split; [exact Hres|].
split; [transitivity (YK11.getr (ms_regs ms1) 18); [kp HP2 18 | rewrite Q18; exact R18]|].
split; [transitivity (YK11.getr (ms_regs ms1) 19); [kp HP2 19 | rewrite Q19; exact R19]|].
split; [transitivity (YK11.getr (ms_regs ms1) 24); [kp HP2 24 | rewrite Q24; exact R24]|].
split; [transitivity (YK11.getr (ms_regs ms1) 20); [kp HP2 20 | rewrite Q20; exact R20]|].
split; [transitivity (YK11.getr (ms_regs ms1) 21); [kp HP2 21 | rewrite Q21; exact R21]|].
split; [transitivity (YK11.getr (ms_regs ms1) 23); [kp HP2 23 | rewrite Q23; exact R23]|].
split; [transitivity (YK11.getr (ms_regs ms1) 22); [kp HP2 22 | rewrite Q22; exact R22]|].
split.
{ destruct Hmode as [(Hm & -> & ->) | ->].
  - exact (eb_mode_ok_tab cx ly2 S2 W2 mem2 md2 mode HCELLS HAR2
      (eb_rom_view_rd cx _ _ ly2 S2 W2 mem2 md2 _ HOWN HNOERR HROM HJ2) Hm).
  - apply (eb_mode_ok_local_keep cx W W2 mem mem2 nch ns); [|exact HMOK]. intros a Ha. apply FK. lia. }
split; [apply (eb_fsh_keep cx (aview segs (w_H W) mem)); [|exact HFSH]; intros i Hi; apply FSK; lia|].
apply (eb_slot_keep cx (aview segs (w_H W) mem)); [|exact HS112]. intros i Hi. apply SK. unfold d_sp0 in *. lia.
Qed.
End tail.

(* ------------------------------------------------------------------ *)
(* 5. +0x074 .. +0x258                                                   *)
(* ------------------------------------------------------------------ *)
(* The input's first three bytes (0 past the end), which fuzz_u8 reads at +0x134 / +0x15c / +0x1d4. *)
Definition eb_byte (cx : dctx) (i : nat) : Z := nth i (map (fun b : byte => bv_unsigned b) (d_pl cx)) 0.
(* The front's symbolic state at +0x074 (slot 29), one per size case k = min n 3 (the size's range [nlo, nhi] is a
   fact on s3, so that the size tests +0x114 / +0x13c / +0x168 are decided): the registers are their own atoms (a0 is
   the frame F, s1 = sp1, s2 = SHADOW_OFF, s3 = n, s8 = p); atom 32 is the frame's shadow address, 33 .. 35 the input
   bytes. Regions: 0 the spill slots 8 .. 119 at s1; 1 the frame's first 48 bytes (the record and the local); 2 its
   eight shadow bytes; 3 .. 5 the three RELRO pointer words (as_const rows); 6 the input's first k bytes. *)
Definition eb_rspill : YP09.region := YP09.mkRegion (Some 9%nat) 0 120 8 120 [].
Definition eb_rframe : YP09.region := YP09.mkRegion (Some 10%nat) 0 48 0 48 [].
Definition eb_rfsh (wlo whi : Z) : YP09.region := YP09.mkRegion (Some 32%nat) 0 8 wlo whi [].
Definition eb_robj (i : nat) (t : Z) : YP09.region := YP09.mkRegion (Some (A_OBJ i)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit t))].
Definition eb_pay_chunks : list YP09.chunk :=
  [YP09.mkChunk 0 (CVal 1 (SOff 33 0)); YP09.mkChunk 1 (CVal 1 (SOff 34 0)); YP09.mkChunk 2 (CVal 1 (SOff 35 0))].
Definition eb_rpay (k : nat) : YP09.region := YP09.mkRegion (Some 24%nat) 0 (Z.of_nat k) 0 0 (firstn k eb_pay_chunks).
Definition eb_mem_f (k : nat) : YP09.smem :=
  [eb_rspill; eb_rframe; eb_rfsh 0 8; eb_robj 4 DEC_TAB4; eb_robj 5 DEC_TAB5; eb_robj 6 DEC_TAB6] ++
  match k with O => [] | _ => [eb_rpay k] end.
Definition eb_pay_facts : list (nat * afact) :=
  [(33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0)].
Definition eb_atoms_f (k : nat) (nlo nhi : Z) : list (nat * afact) :=
  [(9%nat, mkAF 0x7fff7f800000 (2 ^ 47) 5); (10%nat, mkAF 4096 0x7fffff800000 5); (18%nat, mkAF SB SB 0);
   (19%nat, mkAF nlo nhi 0)] ++
  match k with O => [] | _ => (24%nat, mkAF 4096 0x7fffff800000 4) :: firstn k eb_pay_facts end.
Definition eb_alias : list (sv * sv) := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 18 0), SOff 32 0)].
Definition eb_ss_f (k : nat) (nlo nhi : Z) : sstate :=
  mkSS 116 sr_atoms (eb_mem_f k) None (mkFacts (eb_atoms_f k nlo nhi) [] eb_alias).

Section front. Context {fx : YK11.FPState}.
#[local] Notation PI := (@PI_decodeb rc).
#[local] Notation VAL := (@pa_val rc decodeb_listing PI).
#[local] Notation BASE := (@pa_val rc decodeb_listing PI A_TEXT).
Definition eb_Ef (regs : bvmap 5 word) (cx : dctx) : env :=
  Eimg (PI := PI) (Ereg regs [w64 (d_SH cx); w64 (eb_byte cx 0); w64 (eb_byte cx 1); w64 (eb_byte cx 2)]).
Lemma eb_Ef_reg : forall regs cx n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (eb_Ef regs cx) n = YK11.getr regs r.
Proof.
intros regs cx n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
unfold eb_Ef. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma eb_Ef_x : forall regs cx j, (j < 4)%nat ->
  ew (eb_Ef regs cx) (32 + j) = nth j [w64 (d_SH cx); w64 (eb_byte cx 0); w64 (eb_byte cx 1); w64 (eb_byte cx 2)] (Z_to_bv 64 0).
Proof. intros regs cx j Hj. unfold eb_Ef. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.
Lemma eb_Ef_32 : forall regs cx, ew (eb_Ef regs cx) 32 = w64 (d_SH cx).
Proof. intros regs cx. exact (eb_Ef_x regs cx 0 ltac:(lia)). Qed.
Lemma eb_Ef_33 : forall regs cx, ew (eb_Ef regs cx) 33 = w64 (eb_byte cx 0).
Proof. intros regs cx. exact (eb_Ef_x regs cx 1 ltac:(lia)). Qed.
Lemma eb_Ef_34 : forall regs cx, ew (eb_Ef regs cx) 34 = w64 (eb_byte cx 1).
Proof. intros regs cx. exact (eb_Ef_x regs cx 2 ltac:(lia)). Qed.
Lemma eb_Ef_35 : forall regs cx, ew (eb_Ef regs cx) 35 = w64 (eb_byte cx 2).
Proof. intros regs cx. exact (eb_Ef_x regs cx 3 ltac:(lia)). Qed.
Lemma eb_Ef_img : forall regs cx n, (A_TEXT <= n < A_LIM)%nat -> ew (eb_Ef regs cx) n = Z_to_bv 64 (VAL n).
Proof. intros regs cx n Hn. unfold eb_Ef. apply Eimg_img. exact Hn. Qed.

(* lib/A/Prog/YC1h.v frm_off_imgP at image B's PAImg. *)
Lemma eb_frm_off_img : forall ly S (W : world segs) mem md cid pos,
  AR segs B ly S W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos + fs_frame_bytes cid <= IMG_LO \/ IMG_TOP <= frame_addr ly cid pos.
Proof.
intros ly S W mem md cid pos (M & LG & _) Hin.
pose proof (@pa_img_cover rc decodeb_listing PI ly S md (am_layout _ _ _ _ M) LG) as [C1 C2].
pose proof (frame_facts B ly S _ cid pos M Hin) as (Fc & Fp & _ & _ & _ & _ & _ & _ & F64 & _).
destruct (Z.le_gt_cases (frame_addr ly cid pos + fs_frame_bytes cid) IMG_LO) as [|H1]; [left; lia|].
destruct (Z.le_gt_cases IMG_TOP (frame_addr ly cid pos)) as [|H2]; [right; lia|]. exfalso.
apply (client_byte_not_img B ly S _ (Z.max (frame_addr ly cid pos) IMG_LO) M).
- right. exists (cid, pos). split; [exact Hin|]. left. unfold in_zr. cbn [fst snd]. lia.
- unfold in_zr. pose proof IMG_lt. lia.
Qed.
Lemma eb_byte_range : forall cx i, 0 <= eb_byte cx i < 256.
Proof.
intros cx i. unfold eb_byte. destruct (nth_in_or_default i (map (fun b : byte => bv_unsigned b) (d_pl cx)) 0) as [Hin | ->].
- apply in_map_iff in Hin as (b & <- & _). pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr. exact Hr.
- lia.
Qed.
(* The seat at +0x074. *)
Lemma eb_seat_f : forall (cx : dctx) ly S (W : world segs) regs mem md (k : nat) nlo nhi,
  AR_laws segs B -> dec_crt_cells B -> BASE_OK cx ->
  dec_b_core B cx ly S W regs mem md 0 ->
  YK11.getr regs 10 = w64 (d_F cx) -> YK11.getr regs 18 = w64 SHADOW_OFF ->
  YK11.getr regs 19 = w64 (d_n cx) -> YK11.getr regs 24 = w64 (d_p cx) ->
  k = Z.to_nat (dec_b_u (d_n cx)) -> nlo <= d_n cx <= nhi -> 0 <= nlo -> nhi < 2 ^ 26 ->
  st_ok_pi segs VAL (eb_Ef regs cx) (eb_ss_f k nlo nhi)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 116)) mem (YK11.seg_rom segs))).
Proof.
intros cx ly S W regs mem md k nlo nhi LAWS HCELLS HB HCORE R10 R18 R19 R24 Hk Hn Hnlo Hnhi.
pose proof HCORE as (HJ & Hfrs & R8 & R9 & Rsp & Hsp1b & Hsp1al & R3 & R4 & Hsaved & HF4096 & HFal & HFpres & HFL
  & Hpin & Hgarr).
pose proof HB as (HPRE & Hra_eq & R10e & R11e & Hpn & Hlen & _).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR1 & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
change DEC_LLVMF_STK with 32768 in *. unfold d_sp0 in *.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly HAR0 Hly) as (_ & Efa & _).
assert (HfaS : frame_addr ly DEC_FCLASS (d_fpos cx) = d_F cx) by (rewrite Efa; reflexivity).
assert (Hfin : In (DEC_FCLASS, d_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (Hfb : fs_frame_bytes DEC_FCLASS = 64) by (vm_compute; reflexivity).
destruct (frames_bounds _ _ LAWS _ _ _ _ _ _ _ HAR1 Hfin) as (HFb0 & HFb1 & HFb2).
rewrite HfaS in HFb0, HFb1, HFb2. rewrite Hfb in HFb1, HFb2.
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR1 Hfin) as (_ & _ & _ & HFsh).
rewrite HfaS, Hfb in HFsh. change (64 / 8) with 8 in HFsh.
pose proof (eb_frm_off_img ly S W mem md DEC_FCLASS (d_fpos cx) HAR1 Hfin) as HFoff. rewrite HfaS, Hfb in HFoff.
pose proof IMG_LO_val as HILO. pose proof IMG_TOP_val as HITOP.
assert (HFd8 : 0 <= d_F cx / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HFal8 : d_F cx mod 8 = 0).
{ pose proof (Z.div_mod (d_F cx) 32 ltac:(lia)) as D. rewrite HFal, Z.add_0_r in D. rewrite D.
  replace (32 * (d_F cx / 32)) with ((4 * (d_F cx / 32)) * 8) by lia. apply Z_mod_mult. }
set (E := eb_Ef regs cx).
assert (E9 : bv_unsigned (ew E 9) = d_sp1 cx)
  by (unfold E; rewrite (eb_Ef_reg regs cx 9 9%bv) by reflexivity; rewrite R9; unfold w64; apply unsigned_lit_small; lia).
assert (E10 : bv_unsigned (ew E 10) = d_F cx)
  by (unfold E; rewrite (eb_Ef_reg regs cx 10 10%bv) by reflexivity; rewrite R10; unfold w64; apply unsigned_lit_small; lia).
assert (E18 : bv_unsigned (ew E 18) = SHADOW_OFF)
  by (unfold E; rewrite (eb_Ef_reg regs cx 18 18%bv) by reflexivity; rewrite R18; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (E19 : bv_unsigned (ew E 19) = d_n cx)
  by (unfold E; rewrite (eb_Ef_reg regs cx 19 19%bv) by reflexivity; rewrite R19; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : bv_unsigned (ew E 32) = d_SH cx).
{ unfold E. rewrite eb_Ef_32. unfold w64. apply unsigned_lit_small.
  unfold d_SH, shadow_addr, SHADOW_OFF. lia. }
assert (EOBJ : forall i, (i < 16)%nat -> bv_unsigned (ew E (A_OBJ i)) = decodeb_obj i).
{ intros i Hi. unfold E. rewrite eb_Ef_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  rewrite unsigned_lit_small by (exact (pa_val_range (PAImg := PI) (A_OBJ i))).
  clear - Hi. do 16 (destruct i as [|i]; [reflexivity|]). lia. }
(* the input block and its first k bytes *)
assert (Hk3 : (k <= 3)%nat) by (subst k; unfold dec_b_u; lia).
assert (HPAY : (0 < k)%nat -> 4096 <= d_p cx /\ d_p cx + d_n cx <= alloc_ceiling /\ d_p cx mod 16 = 0 /\
  in_app (d_p cx) (req_size (d_n cx)) /\ In (d_p cx, d_n cx) (ablocks B ly S) /\ (k <= Z.to_nat (d_n cx))%nat).
{ intros Hk0. assert (Hn0 : 0 < d_n cx) by (subst k; unfold dec_b_u in Hk0; lia).
  pose proof (Hpin Hn0) as Hpin1.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR1 Hpin1) as (Hp16 & Hp4096 & Hpceil & Hpapp & _).
  pose proof (req_size_pos (d_n cx) ltac:(lia)) as (_ & Hrq).
  split; [lia|]. split; [lia|]. split; [exact Hp16|]. split; [exact Hpapp|]. split; [exact Hpin1|].
  subst k. unfold dec_b_u. lia. }
rewrite restrict_mkst_fx. unfold eb_ss_f.
refine (@pa_entry_st_ok_full fx rc decodeb_listing PI E 116 sr_atoms regs _ _ (mrestrict (w_H W) mem) _ _ _ _ _).
- unfold E, eb_Ef. apply regs_ok_Eimg_Ereg.
- destruct k as [|[|[|[|k]]]]; [vm_compute; reflexivity .. | lia].
- (* the regions *)
  assert (R0 : region_ok segs E (mrestrict (w_H W) mem) eb_rspill).
  { unfold region_ok, eb_rspill. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply HJpres. lia. }
  assert (R1 : region_ok segs E (mrestrict (w_H W) mem) eb_rframe).
  { unfold region_ok, eb_rframe. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E10. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply HFpres. lia. }
  assert (R2 : region_ok segs E (mrestrict (w_H W) mem) (eb_rfsh 0 8)).
  { unfold region_ok, eb_rfsh. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E32. unfold d_SH, shadow_addr, SHADOW_OFF in *. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). exact (proj1 (HFsh o Ho)). }
  destruct (eb_mode_cells_of HCELLS ly) as (P4 & P5 & P6).
  assert (RO : forall (i : nat) t, (i = 4 \/ i = 5 \/ i = 6)%nat -> In (z8 (ANum (decodeb_obj i)) t) (as_const B ly) ->
    0 <= t < 2 ^ 64 -> region_ok segs E (mrestrict (w_H W) mem) (eb_robj i t)).
  { intros i t Hi Hin Ht.
    assert (Hob : 0 <= decodeb_obj i /\ decodeb_obj i + 8 <= 2 ^ 64) by (destruct Hi as [-> | [-> | ->]]; cbn; lia).
    unfold region_ok, eb_robj. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite (EOBJ i ltac:(lia)).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs E _ (decodeb_obj i) 0 8 (SLit t) t); [cbn [sv_denot]; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. apply (val_mem_of_rdword segs (w_H W) mem). exact (eb_cell8 ly S W mem md _ _ HAR1 Hin Ht). }
  apply Forall_app. split.
  + repeat apply Forall_cons; try apply Forall_nil; try assumption;
      apply RO; first [lia | assumption | unfold DEC_TAB4, DEC_TAB5, DEC_TAB6; lia].
  + destruct k as [|k']; [apply Forall_nil|].
    apply Forall_cons; [|apply Forall_nil].
    destruct (HPAY ltac:(lia)) as (Hp4096 & Hpceil & Hp16 & Hpapp & Hpin1 & Hkn).
    assert (E24 : bv_unsigned (ew E 24) = d_p cx)
      by (unfold E; rewrite (eb_Ef_reg regs cx 24 24%bv) by reflexivity; rewrite R24; unfold w64; apply unsigned_lit_small; lia).
    assert (BYTE : forall j : nat, (j <= k')%nat ->
      YP09.chunk_ok segs E (mrestrict (w_H W) mem) (d_p cx) (YP09.mkChunk (Z.of_nat j) (CVal 1 (SOff (33 + j) 0)))).
    { intros j Hj. rewrite Hlen in Hkn.
      assert (Hjl : (j < length (map (fun b : byte => bv_unsigned b) (d_pl cx)))%nat) by (rewrite length_map; lia).
      destruct (Hgarr j Hjl) as (Hv & Hb).
      apply (chunk_ok_val segs E _ (d_p cx) (Z.of_nat j) 1 (SOff (33 + j) 0) (eb_byte cx j)); [| cbn; unfold eb_byte; lia | cbn; lia | exact Hv].
      cbn [sv_denot]. rewrite Z.add_0_r. unfold E.
      destruct j as [|[|[|j]]]; [rewrite eb_Ef_33 | rewrite eb_Ef_34 | rewrite eb_Ef_35 | lia];
        unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity. }
    unfold region_ok, eb_rpay. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E24. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    destruct k' as [|[|[|k']]]; [ | | | lia]; cbn [firstn eb_pay_chunks];
      repeat apply Forall_cons; try apply Forall_nil;
      first [exact (BYTE 0%nat ltac:(lia)) | exact (BYTE 1%nat ltac:(lia)) | exact (BYTE 2%nat ltac:(lia))].
- (* disjointness *)
  apply pairwise_disjoint_of_extents.
  pose proof (pa_obj_img (PAImg := PI) 4 ltac:(lia)) as Ho4. pose proof (pa_obj_img (PAImg := PI) 6 ltac:(lia)) as Ho6.
  cbn [pa_val PI_decodeb] in Ho4, Ho6. unfold decodeb_val, A_OBJ, A_TEXT, A_HI in Ho4, Ho6. cbn in Ho4, Ho6.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFb2.
  destruct k as [|k'].
  + unfold eb_mem_f, eb_rspill, eb_rframe, eb_rfsh, eb_robj, extent_of_region. cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E9, E10, E32, !EOBJ by lia. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold d_SH, shadow_addr, SHADOW_OFF. cbn [decodeb_obj]. repeat split; lia.
  + destruct (HPAY ltac:(lia)) as (Hp4096 & Hpceil & Hp16 & Hpapp & Hpin1 & Hkn).
    assert (E24 : bv_unsigned (ew E 24) = d_p cx)
      by (unfold E; rewrite (eb_Ef_reg regs cx 24 24%bv) by reflexivity; rewrite R24; unfold w64; apply unsigned_lit_small; lia).
    pose proof (sep_block_frame segs B LAWS _ _ _ _ _ _ _ _ _ HAR1 Hpin1 Hfin) as HdF.
    unfold zdisjoint in HdF. cbn [fst snd] in HdF. rewrite HfaS, Hfb in HdF.
    pose proof (blk_off_imgP (PI := PI) B ly S W mem md _ _ HAR1 Hpin1) as Hpoff.
    pose proof (req_size_pos (d_n cx) ltac:(lia)) as (_ & Hrq).
    unfold off_img in Hpoff. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
    rewrite Hlen in Hkn.
    unfold eb_mem_f, eb_rspill, eb_rframe, eb_rfsh, eb_robj, eb_rpay, extent_of_region.
    cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E9, E10, E32, E24, !EOBJ by lia. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold d_SH, shadow_addr, SHADOW_OFF. cbn [decodeb_obj]. rewrite <- Hlen in Hkn. repeat split; lia.
- (* the facts *)
  split; [|split; [exact I|]].
  + assert (EB : forall j, (j < 3)%nat -> bv_unsigned (ew E (33 + j)) = eb_byte cx j).
    { intros j Hj. pose proof (eb_byte_range cx j) as Hr. unfold E.
      destruct j as [|[|[|j]]]; [rewrite eb_Ef_33 | rewrite eb_Ef_34 | rewrite eb_Ef_35 | lia];
        unfold w64; apply unsigned_lit_small; lia. }
    pose proof (EB 0%nat ltac:(lia)) as E33. pose proof (EB 1%nat ltac:(lia)) as E34. pose proof (EB 2%nat ltac:(lia)) as E35.
    cbn [Nat.add] in E33, E34, E35.
    pose proof (eb_byte_range cx 0) as Hb0. pose proof (eb_byte_range cx 1) as Hb1. pose proof (eb_byte_range cx 2) as Hb2.
    assert (Hsp32 : d_sp1 cx mod 2 ^ 5 = 0) by (change (2 ^ 5) with 32; exact Hsp1al).
    assert (HF32 : d_F cx mod 2 ^ 5 = 0) by (change (2 ^ 5) with 32; exact HFal).
    destruct k as [|[|[|[|k]]]]; [ | | | | lia]; cbn [f_atoms eb_atoms_f app firstn eb_pay_facts atoms_ok]; unfold afact_ok;
      cbn [af_lo af_hi af_al2]; rewrite ?E9, ?E10, ?E18, ?E19, ?E33, ?E34, ?E35; rewrite ?Z.pow_0_r, ?Z.mod_1_r;
      try (destruct (HPAY ltac:(lia)) as (Hp4096 & Hpceil & Hp16 & _);
           assert (E24 : bv_unsigned (ew E 24) = d_p cx)
             by (unfold E; rewrite (eb_Ef_reg regs cx 24 24%bv) by reflexivity; rewrite R24; unfold w64;
                 apply unsigned_lit_small; lia);
           rewrite E24; change (2 ^ 4) with 16);
      unfold SB, SHADOW_OFF in *; repeat match goal with |- _ /\ _ => split end;
      first [exact I | lia | assumption].
  + cbn [eb_alias alias_ok f_alias]. split; [|exact I].
    assert (E10' : ew E 10 = Z_to_bv 64 (d_F cx)) by (unfold E; rewrite (eb_Ef_reg regs cx 10 10%bv) by reflexivity; exact R10).
    assert (E18' : ew E 18 = Z_to_bv 64 SHADOW_OFF) by (unfold E; rewrite (eb_Ef_reg regs cx 18 18%bv) by reflexivity; exact R18).
    assert (E32' : ew E 32 = Z_to_bv 64 (SHADOW_OFF + d_F cx / 8)) by (unfold E; rewrite eb_Ef_32; reflexivity).
    exact (shadow_decl_ok E 10 18 32 (d_F cx) SHADOW_OFF E10' ltac:(lia) E18' E32').
Qed.

(* The write windows of the front's regions: the spill slots are in the function's stack window, the frame's
   first 48 bytes and its shadow are the function's own frame (in_frames); the rest are read only. *)
Lemma eb_awr_f : forall cx (E : env) ly cs0 wlo1 whi1 cs1 wlo whi cs2 rest bl0 blc,
  frame_addr ly DEC_FCLASS (d_fpos cx) = d_F cx ->
  bv_unsigned (ew E 9) = d_sp1 cx -> bv_unsigned (ew E 10) = d_F cx -> bv_unsigned (ew E 32) = d_SH cx ->
  d_sp0 cx - 240 <= d_sp1 cx <= d_sp0 cx - 224 -> 0 <= wlo1 -> whi1 <= 48 -> 0 <= wlo -> whi <= 8 ->
  Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rest ->
  awr_ok E (YP09.mkRegion (Some 9%nat) 0 120 8 120 cs0 :: YP09.mkRegion (Some 10%nat) 0 48 wlo1 whi1 cs1 ::
            YP09.mkRegion (Some 32%nat) 0 8 wlo whi cs2 :: rest) DEC_LLVMF_STK (d_sp0 cx) [] bl0 blc ly
    [(DEC_FCLASS, d_fpos cx)].
Proof.
intros cx E ly cs0 wlo1 whi1 cs1 wlo whi cs2 rest bl0 blc Hfa H9 H10 H32 Hsp Hwlo1 Hwhi1 Hwlo Hwhi Hro.
assert (Hfb : fs_frame_bytes DEC_FCLASS = 64) by (vm_compute; reflexivity).
change DEC_LLVMF_STK with 32768.
eapply (awr_ok_cons_stack_off E _ _ _ _ _ _ _ _ _ 9%nat (d_sp1 cx - d_sp0 cx)); [reflexivity | lia | cbn; lia | cbn; lia |].
eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 10%nat (d_F cx)); [reflexivity | exact H10 | |].
{ intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists DEC_FCLASS, (d_fpos cx).
  split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite Hfa, Hfb. lia. }
eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 32%nat (d_SH cx)); [reflexivity | exact H32 | |].
{ intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right. exists DEC_FCLASS, (d_fpos cx).
  split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite Hfa, Hfb. change (64 / 8) with 8.
  unfold d_SH in Ha. lia. }
induction Hro as [|r rest Hr Hrest IH]; [apply awr_ok_nil|]. apply awr_ok_cons_ro; [exact Hr | exact IH].
Qed.
Lemma eb_U_srl26 : forall E x, U E (SAlu ALU_SRL x (SLit 26)) = U E x / 2 ^ 26.
Proof.
intros E x. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. change (Z.land (zcanon 26) 63) with 26.
rewrite Z.shiftr_div_pow2 by lia. apply zcanon_id. rewrite M64_val.
pose proof (U_range E x) as Hx. rewrite M64_val in Hx.
split; [apply Z.div_pos; lia|]. apply (Z.le_lt_trans _ (U E x)); [apply Z.div_le_upper_bound; lia | lia].
Qed.
(* The front writes only its three windows: the spill slots 8 .. 119 at s1, the frame's first 48 bytes, the frame's
   eight shadow bytes. *)
Definition eb_win (cx : dctx) (a : Z) : Prop :=
  (d_sp1 cx + 8 <= a < d_sp1 cx + 120) \/ (d_F cx <= a < d_F cx + 48) \/ (d_SH cx <= a < d_SH cx + 8).
Lemma eb_keep_step : forall cx E rs H (m0 m1 m2 : word -> option byte),
  frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> eb_win cx a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ eb_win cx a -> aview segs H m1 a = aview segs H m0 a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ eb_win cx a -> aview segs H m2 a = aview segs H m0 a.
Proof.
intros cx E rs H m0 m1 m2 HF HW K a Ha Hn.
rewrite (kept_of_frame (segs := segs) E rs H m1 m2 (eb_win cx) HF HW a Ha Hn). exact (K a Ha Hn).
Qed.
(* The token engine's obligation for an input read at p + j: the byte is addressable (the input block's shadow). *)
Lemma eb_ob_input : forall cx ly S (W : world segs) mem md (E : env) j,
  AR_laws segs B -> AR segs B ly S W mem md -> In (d_p cx, d_n cx) (ablocks B ly S) ->
  ew E 18 = w64 SHADOW_OFF -> ew E 24 = w64 (d_p cx) -> 4096 <= d_p cx -> d_p cx + d_n cx <= alloc_ceiling ->
  0 <= j < d_n cx ->
  range_addressable (rd_of segs (mrestrict (w_H W) mem)) (U E (SOff 18 0)) (U E (SOff 24 j)) 1.
Proof.
intros cx ly S W mem md E j LAWS HAR Hin H18 H24 Hp Hpc Hj. pose proof asan_consts as (C1 & _).
rewrite (U_atom E 18 SHADOW_OFF H18) by (unfold SHADOW_OFF; lia).
rewrite U_SOff, H24. unfold w64. rewrite unsigned_lit_small by lia. rewrite zcanon_id by (rewrite M64_val; lia).
pose proof (req_size_pos (d_n cx) ltac:(lia)) as (_ & Hrq).
exact (range_addressable_of_block segs B LAWS ly S W mem md (d_p cx) (d_n cx) (d_p cx + j) 1 HAR Hin ltac:(lia) ltac:(lia)).
Qed.
(* The fake frame (its first 64 bytes) and its eight shadow bytes are writable at any state of the walk. *)
Lemma eb_frame_writable : forall cx ly S (W : world segs) mem md,
  AR_laws segs B -> AR segs B ly S W mem md -> In (DEC_FCLASS, d_fpos cx) (frames S) ->
  frame_addr ly DEC_FCLASS (d_fpos cx) = d_F cx ->
  (forall o, 0 <= o < 64 -> writable_at segs (mrestrict (w_H W) mem) (d_F cx + o)) /\
  (forall o, 0 <= o < 8 -> writable_at segs (mrestrict (w_H W) mem) (d_SH cx + o)).
Proof.
intros cx ly S W mem md LAWS HAR Hfin Hfa.
assert (Hfb : fs_frame_bytes DEC_FCLASS = 64) by (vm_compute; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR Hfin) as (_ & _ & HFp & HFsh).
rewrite Hfa, Hfb in HFp. rewrite Hfa, Hfb in HFsh. change (64 / 8) with 8 in HFsh.
split; intros o Ho; apply (apresent_writable segs).
- exact (proj1 (HFp (d_F cx + o) ltac:(lia))).
- exact (proj1 (HFsh o Ho)).
Qed.
Lemma eb_brute : forall (P : Z -> bool), forallb (fun i => P (Z.of_nat i)) (seq 0 256) = true ->
  forall b, 0 <= b < 256 -> P b = true.
Proof.
intros P H b Hb. rewrite forallb_forall in H. replace b with (Z.of_nat (Z.to_nat b)) by lia. apply H.
apply in_seq. lia.
Qed.
(* Facts a region of the symbolic memory shows at a leaf. *)
Lemma eb_slot_of_region : forall E (m : word -> option byte) H n b cs lo hi wlo whi od e v,
  region_ok segs E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 8 e)) cs -> U E e = v ->
  rdword (aview segs H m) (b + od) = Some v.
Proof.
intros E m H n b cs lo hi wlo whi od e v HR Hb Hin Hv.
pose proof (field_of_region_any (segs := segs) E _ n b cs lo hi wlo whi od 8 e HR Hb Hin ltac:(lia)) as Hf.
change (8 * Z.of_N 8) with 64 in Hf. fold (U E e) in Hf. rewrite Z.mod_small in Hf by exact (U_range E e).
rewrite Hv in Hf. pose proof (U_range E e) as Hr. rewrite Hv, M64_val in Hr.
exact (eb_rdword_of_val_mem H m (b + od) v Hf Hr).
Qed.
Lemma eb_byte_of_region : forall E (m : word -> option byte) H n b cs lo hi wlo whi od e v,
  region_ok segs E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal 1 e)) cs -> U E e mod 256 = v ->
  aview segs H m (b + od) = Some v.
Proof.
intros E m H n b cs lo hi wlo whi od e v HR Hb Hin Hv.
pose proof (field_of_region_any (segs := segs) E _ n b cs lo hi wlo whi od 1 e HR Hb Hin ltac:(lia)) as Hf.
change (8 * Z.of_N 1) with 8 in Hf. fold (U E e) in Hf. change (2 ^ 8) with 256 in Hf. rewrite Hv in Hf.
specialize (Hf 0%nat ltac:(cbn; lia)). rewrite Z.add_0_r in Hf.
unfold aview. rewrite Hf. cbn [option_map]. f_equal.
assert (Hvr : 0 <= v < 256) by (rewrite <- Hv; apply Z.mod_pos_bound; lia).
clear - Hvr. apply Z.eqb_eq. revert v Hvr. apply eb_brute. vm_compute. reflexivity.
Qed.
(* A signed byte as the 64-bit word lb / slli 56 + srai 56 make of it. *)
Definition eb_sb (b : Z) : Z := if b <? 128 then b else b - 256.
Definition eb_sbyte (E : env) (e : sv) : Prop := exists b, 0 <= b < 256 /\ U E e = zcanon (eb_sb b).
Lemma eb_sbyte_sra : forall E x, 0 <= U E x < 256 ->
  eb_sbyte E (SAlu ALU_SRA (SAlu ALU_SLL x (SLit 56)) (SLit 56)).
Proof.
intros E x Hx. exists (U E x). split; [exact Hx|]. rewrite !U_SAlu, !U_SLit. cbn [zalu_raw].
generalize (U E x) Hx. intros b Hb. apply Z.eqb_eq. revert b Hb. apply eb_brute. vm_compute. reflexivity.
Qed.
Lemma eb_sbyte_sext : forall E x, 0 <= U E x < 256 -> eb_sbyte E (SExt true 8 x).
Proof.
intros E x Hx. exists (U E x). split; [exact Hx|]. rewrite U_SExt.
generalize (U E x) Hx. intros b Hb. apply Z.eqb_eq. revert b Hb. apply eb_brute. vm_compute. reflexivity.
Qed.
Lemma eb_sbyte_zero : forall E e, U E e = 0 -> eb_sbyte E e.
Proof. intros E e H. exists 0. split; [lia|]. rewrite H. reflexivity. Qed.
Lemma eb_local_fields : forall E (m : word -> option byte) H b cs lo hi wlo whi e36 e40,
  region_ok segs E (mrestrict H m) (YP09.mkRegion (Some 10%nat) lo hi wlo whi cs) -> bv_unsigned (ew E 10) = b ->
  In (YP09.mkChunk 36 (CVal 4 e36)) cs -> In (YP09.mkChunk 40 (CVal 4 e40)) cs ->
  eb_sbyte E e36 -> eb_sbyte E e40 ->
  exists nch ns, -128 <= nch <= 127 /\ -128 <= ns <= 127 /\
    val_mem segs (mrestrict H m) (b + 36) 4 (nch mod 2 ^ 32) /\ val_mem segs (mrestrict H m) (b + 40) 4 (ns mod 2 ^ 32).
Proof.
intros E m H b cs lo hi wlo whi e36 e40 HR Hb H36 H40 (b1 & Hb1 & E1) (b2 & Hb2 & E2).
assert (Hsb : forall z, 0 <= z < 256 -> -128 <= eb_sb z <= 127 /\ zcanon (eb_sb z) mod 2 ^ 32 = eb_sb z mod 2 ^ 32).
{ intros z Hz. unfold eb_sb, zcanon, M64. destruct (Z.ltb_spec z 128).
  - rewrite (Z.mod_small z) by lia. lia.
  - split; [lia|]. rewrite <- (Z_mod_plus_full (z - 256) 1 (2 ^ 64)). rewrite Z.mul_1_l.
    rewrite (Z.mod_small (z - 256 + 2 ^ 64)) by lia.
    rewrite <- (Z_mod_plus_full (z - 256) (2 ^ 32) (2 ^ 32)).
    replace (z - 256 + 2 ^ 32 * 2 ^ 32) with (z - 256 + 2 ^ 64) by lia. reflexivity. }
exists (eb_sb b1), (eb_sb b2).
destruct (Hsb b1 Hb1) as (R1 & M1). destruct (Hsb b2 Hb2) as (R2 & M2).
split; [exact R1|]. split; [exact R2|].
pose proof (field_of_region_any (segs := segs) E _ 10 b cs lo hi wlo whi 36 4 e36 HR Hb H36 ltac:(lia)) as F1.
pose proof (field_of_region_any (segs := segs) E _ 10 b cs lo hi wlo whi 40 4 e40 HR Hb H40 ltac:(lia)) as F2.
change (8 * Z.of_N 4) with 32 in F1, F2. fold (U E e36) in F1. fold (U E e40) in F2.
rewrite E1, M1 in F1. rewrite E2, M2 in F2. split; [exact F1 | exact F2].
Qed.

(* The state at +0x258 from what a leaf of the front shows. *)
Lemma eb_leaf : forall (cx : dctx) ly S (W : world segs) regs mem md regs' mem' md' (mode : Z),
  AR_laws segs B -> BASE_OK cx -> frm_zero (@fp_csr fx) -> dec_crt_cells B ->
  dec_ro_rd_unowned B -> dec_rom_no_errno B -> dec_b_rom cx ->
  dec_b_core B cx ly S W regs mem md 0 ->
  ablocks B ly S = ablocks B (d_ly cx) (d_S cx) ->
  mo_le MT (d_S cx) S 0 -> mo_ok MT S (dec_rest_074 MT (d_n cx)) ->
  @ajournal rc tfib_sink_head segs B 32768 (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly S W mem' md' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ eb_win cx a -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
  YK11.getr regs' 2 = YK11.getr regs 2 -> YK11.getr regs' 3 = YK11.getr regs 3 ->
  YK11.getr regs' 4 = YK11.getr regs 4 -> YK11.getr regs' 8 = YK11.getr regs 8 ->
  YK11.getr regs' 9 = YK11.getr regs 9 ->
  YK11.getr regs' 17 = w64 (d_F cx) -> YK11.getr regs' 18 = w64 SHADOW_OFF ->
  YK11.getr regs' 19 = w64 (d_n cx) -> YK11.getr regs' 24 = w64 (d_p cx + dec_b_u (d_n cx)) ->
  YK11.getr regs' 20 = w64 (dec_b_len (d_n cx)) -> YK11.getr regs' 21 = w64 mode ->
  YK11.getr regs' 23 = w64 (mode + 4) -> YK11.getr regs' 22 = w64 (mode + 8) ->
  dec_b_slot cx (aview segs (w_H W) mem') 8 (d_SH cx) ->
  dec_b_slot cx (aview segs (w_H W) mem') 16 (d_F cx) ->
  dec_b_slot cx (aview segs (w_H W) mem') 112 (d_F cx) ->
  dec_b_fsh cx (aview segs (w_H W) mem') 0 4 ->
  ((mode = DEC_TAB4 \/ mode = DEC_TAB5 \/ mode = DEC_TAB6) \/
   mode = d_F cx + 32 /\ exists nch ns, -128 <= nch <= 127 /\ -128 <= ns <= 127 /\
     val_mem segs (rd W mem') (d_F cx + 36) 4 (nch mod 2 ^ 32) /\
     val_mem segs (rd W mem') (d_F cx + 40) 4 (ns mod 2 ^ 32)) ->
  eb_mid cx W (mkCfg (@YK11.mkst fx regs' (w64 (DEC_A_LLVMF + 0x258)) mem' (YK11.seg_rom segs)) md').
Proof.
intros cx ly S W regs mem md regs' mem' md' mode LAWS HB Hfrm HCELLS HOWN HNOERR HROM HCORE Hbl Hmle Hmok HJ' KEEP
  Q2 Q3 Q4 Q8 Q9 Q17 Q18 Q19 Q24 Q20 Q21 Q23 Q22 HS8 HS16 HS112 HFSH HMODE.
pose proof HCORE as (HJ & Hfrs & R8 & R9 & Rsp & Hsp1b & Hsp1al & R3 & R4 & Hsaved & HF4096 & HFal & HFpres & HFL
  & Hpin & Hgarr).
pose proof HB as (HPRE & _ & _ & _ & Hpn & Hlen & _).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
change DEC_LLVMF_STK with 32768 in *.
pose proof HJ' as (HAR' & Hly' & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly HAR0 Hly') as (_ & Efa & _).
assert (HfaS : frame_addr ly DEC_FCLASS (d_fpos cx) = d_F cx) by (rewrite Efa; reflexivity).
assert (Hfin : In (DEC_FCLASS, d_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (Hfb : fs_frame_bytes DEC_FCLASS = 64) by (vm_compute; reflexivity).
destruct (frames_bounds _ _ LAWS _ _ _ _ _ _ _ HAR' Hfin) as (HFb0 & HFb1 & HFb2).
rewrite HfaS in HFb0, HFb1, HFb2. rewrite Hfb in HFb1, HFb2.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFb2.
assert (HFd8 : 0 <= d_F cx / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (Hsp1c : alloc_ceiling + 4096 <= d_sp1 cx) by (unfold d_sp0 in *; lia).
assert (NW : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx + 8 <= a < d_sp1 cx + 120) -> ~ (d_F cx <= a < d_F cx + 48) ->
  ~ (d_SH cx <= a < d_SH cx + 8) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a).
{ intros a Ha N1 N2 N3. apply KEEP; [exact Ha|]. unfold eb_win. tauto. }
unfold eb_mid; cbv beta. exists fx, ly, S, regs', mem', md'.
destruct HMODE as [Hm | (-> & nch & ns & Hn1 & Hn2 & Hv4 & Hv8)].
1: exists mode, DEC_TAB_NCH, DEC_TAB_NS.
2: exists (d_F cx + 32), nch, ns.
all: split; [reflexivity|]. all: split; [exact Hfrm|].
all: split.
1,3: unfold dec_b_core;
  split; [exact HJ'|]; split; [exact Hfrs|];
  split; [rewrite Q8; exact R8|]; split; [rewrite Q9; exact R9|];
  split; [unfold spZ in *; rewrite Q2; exact Rsp|];
  split; [exact Hsp1b|]; split; [exact Hsp1al|];
  split; [rewrite Q3; exact R3|]; split; [rewrite Q4; exact R4|];
  split; [apply (eb_saved_keep cx (aview segs (w_H W) mem)); [|exact Hsaved]; intros a Ha; apply NW;
          unfold d_SH, shadow_addr, SHADOW_OFF, d_sp0 in *; lia|];
  split; [exact HF4096|]; split; [exact HFal|];
  split; [intros a Ha; destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR' Hfin) as (_ & _ & HFp & _);
          rewrite HfaS, Hfb in HFp; exact (proj1 (HFp a Ha))|];
  split; [apply (eb_rdword_keep (aview segs (w_H W) mem)); [|exact HFL]; intros i Hi; apply NW;
          unfold d_SH, shadow_addr, SHADOW_OFF, d_sp0 in *; lia|];
  split; [exact Hpin|];
  apply (eb_garr8_keep (w_H W) (w_H W) mem mem'); [|exact Hgarr];
  intros i Hi; rewrite length_map, <- Hlen in Hi;
  pose proof (Hpin ltac:(lia)) as Hpin1;
  pose proof (sep_block_frame segs B LAWS _ _ _ _ _ _ _ _ _ HAR' Hpin1 Hfin) as HdF;
  unfold zdisjoint in HdF; cbn [fst snd] in HdF; rewrite HfaS, Hfb in HdF;
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR' Hpin1) as (_ & Hp4096 & Hpceil & Hpapp & _);
  pose proof (req_size_pos (d_n cx) ltac:(lia)) as (_ & Hrq);
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp;
  apply NW; unfold d_SH, shadow_addr, SHADOW_OFF, d_sp0 in *; lia.
all: split; [exact Hbl|]. all: split; [exact Hmle|]. all: split; [exact Hmok|].
all: split; [exact Q17|]. all: split; [exact Q18|]. all: split; [exact Q19|]. all: split; [exact Q24|].
all: split; [exact Q20|]. all: split; [exact Q21|]. all: split; [exact Q23|]. all: split; [exact Q22|].
- split; [exact (eb_mode_ok_tab cx ly S W mem' md' mode HCELLS HAR'
            (eb_rom_view_rd cx _ _ ly S W mem' md' _ HOWN HNOERR HROM HJ') Hm)|].
  split; [left; split; [exact Hm | split; reflexivity]|].
  split; [exact HFSH|]. split; [exact HS8|]. split; [exact HS16|]. exact HS112.
- split.
  { split; [right; right; right; reflexivity|]. split; [exact Hn1|]. split; [exact Hn2|].
    replace (d_F cx + 32 + 4) with (d_F cx + 36) by lia. replace (d_F cx + 32 + 8) with (d_F cx + 40) by lia.
    split; [exact Hv4 | exact Hv8]. }
  split; [right; reflexivity|].
  split; [exact HFSH|]. split; [exact HS8|]. split; [exact HS16|]. exact HS112.
Qed.
Ltac eb_branch_plain RUNTOP BR HS :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
    lazymatch type of RUNTOP with
    | forall W n stop E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q, _ -> _ -> sym_run_toN_pi ?tpi n stop ss = _ -> _ =>
      let r := eval vm_compute in (sym_step_pi tpi ss) in
      lazymatch r with
      | PStop (SR_branch ?c ?a ?b) =>
        apply (BR W E ss ms _ _ c a b HS); clear HS; let Hc := fresh "Hc" in intros Hc HS
      | _ => fail "eb_branch_plain: not stuck at a branch:" r
      end
    end
  end.

Ltac eb_win_tac E9 E10 E32 :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros b wlo whi a Hin Ha; vm_compute in Hin;
  repeat (destruct Hin as [Hin | Hin];
    [ injection Hin as <- <- <-; cbn [base_val ew ewset extK Nat.eqb] in Ha;
      lazymatch type of Ha with
      | _ + ?l <= _ < _ + ?l => lia
      | _ => rewrite ?E9, ?E10, ?E32 in Ha; unfold eb_win; lia
      end | ]);
  destruct Hin.
Ltac eb_clear_old_ms HS :=
  try match type of HS with context [restrict _ ?msn] =>
    repeat match goal with
    | old : machine_state |- _ => lazymatch old with msn => fail | _ => clear old end
    end
  end.
Ltac eb_keep cx K HFr E9 E10 E32 :=
  lazymatch type of HFr with frame_of ?Ex ?rs (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
    let K' := fresh "K" in
    pose proof (eb_keep_step cx Ex rs H _ m1 m2 HFr ltac:(eb_win_tac E9 E10 E32) K) as K'; clear K HFr; rename K' into K
  end.
(* Re-window region i of HS's symbolic memory; tac proves the window writable. *)
Ltac eb_rewin HS i wlo whi tac :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss ?ms =>
    let r := eval vm_compute in (nth_error (ss_mem ss) i) in
    lazymatch r with Some ?rg =>
      let HS' := fresh "HS" in
      pose proof (eb_rewindow E ss ms i rg wlo whi HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(idtac; tac)) as HS';
      clear HS; rename HS' into HS;
      lazymatch type of HS with st_ok_pi _ _ _ ?ss2 _ =>
        let ss3 := eval vm_compute in ss2 in change ss2 with ss3 in HS end
    end
  end.
Ltac eb_awr_tac cx HfaS E9 E10 E32 Hsp1b :=
  cbn [ss_mem add_cond];
  apply (eb_awr_f cx _ _); [ exact HfaS | cbn [ew ewset extK Nat.eqb]; exact E9 | cbn [ew ewset extK Nat.eqb]; exact E10
    | cbn [ew ewset extK Nat.eqb]; exact E32 | exact Hsp1b | lia | lia | lia | lia
    | repeat apply Forall_cons; try apply Forall_nil; cbn; lia].

Ltac eb_in_tac := repeat (first [ left; reflexivity | right ]).
(* +0x074 .. +0x258. *)
Lemma eb_front_fx : forall (cx : dctx) ly S (W : world segs) regs mem md,
  dec_crt_cells B -> dec_ro_rd_unowned B -> dec_rom_no_errno B -> AR_laws segs B -> BASE_OK cx -> dec_b_rom cx ->
  frm_zero (@fp_csr fx) ->
  dec_b_core B cx ly S W regs mem md 0 ->
  ablocks B ly S = ablocks B (d_ly cx) (d_S cx) ->
  mo_le MT (d_S cx) S 0 -> mo_ok MT S (dec_rest_074 MT (d_n cx)) ->
  YK11.getr regs 10 = w64 (d_F cx) -> YK11.getr regs 18 = w64 SHADOW_OFF ->
  YK11.getr regs 19 = w64 (d_n cx) -> YK11.getr regs 24 = w64 (d_p cx) ->
  SRr segs W (mkCfg (@YK11.mkst fx regs (w64 (DEC_A_LLVMF + 0x074)) mem (YK11.seg_rom segs)) md) (eb_mid cx).
Proof.
intros cx ly S W regs mem md HCELLS HOWN HNOERR LAWS HB HROM Hfrm HCORE Hbl Hmle Hmok R10 R18 R19 R24.
pose proof HCORE as (HJ & Hfrs & R8 & R9 & Rsp & Hsp1b & Hsp1al & R3 & R4 & Hsaved & HF4096 & HFal & HFpres & HFL
  & Hpin & Hgarr).
pose proof HB as (HPRE & Hra_eq & R10e & R11e & Hpn & Hlen & _).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
change DEC_LLVMF_STK with 32768 in *.
pose proof HJ as (HAR1 & Hly & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly HAR0 Hly) as (_ & Efa & _).
assert (HfaS : frame_addr ly DEC_FCLASS (d_fpos cx) = d_F cx) by (rewrite Efa; reflexivity).
assert (Hcases : d_n cx = 0 \/ d_n cx = 1 \/ d_n cx = 2 \/ 3 <= d_n cx < 2 ^ 26) by lia.
pose proof (@eb_run_to_pi_AJ fx rc tfib_sink_head decodeb_listing PL_decodeb PI B LAWS) as RUNTOP.
pose proof (@paj_run fx rc tfib_sink_head decodeb_listing PL_decodeb PI B LAWS) as RUN.
pose proof (@paj_branch fx rc decodeb_listing PI) as BR.
set (E := eb_Ef regs cx).
assert (HEI : img_env VAL A_LIM E) by (unfold E, eb_Ef; apply Eimg_env).
assert (E9 : bv_unsigned (ew E 9) = d_sp1 cx)
  by (unfold E; rewrite (eb_Ef_reg regs cx 9 9%bv) by reflexivity; rewrite R9; unfold w64; apply unsigned_lit_small; unfold d_sp0 in *; lia).
destruct (frames_bounds _ _ LAWS _ _ _ _ _ _ _ HAR1 ltac:(rewrite Hfrs; left; reflexivity)) as (HFb0 & HFb1 & HFb2).
rewrite HfaS in HFb0, HFb1, HFb2.
assert (E10 : bv_unsigned (ew E 10) = d_F cx)
  by (unfold E; rewrite (eb_Ef_reg regs cx 10 10%bv) by reflexivity; rewrite R10; unfold w64; apply unsigned_lit_small;
      change (fs_frame_bytes DEC_FCLASS) with 64 in HFb1; lia).
assert (HFd8 : 0 <= d_F cx / 8 <= 2 ^ 44)
  by (change (fs_frame_bytes DEC_FCLASS) with 64 in HFb1; split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (E32 : bv_unsigned (ew E 32) = d_SH cx).
{ unfold E. rewrite eb_Ef_32. unfold w64. apply unsigned_lit_small. unfold d_SH, shadow_addr, SHADOW_OFF. lia. }
assert (E19 : U E (SOff 19 0) = d_n cx).
{ apply U_atom; [unfold E; rewrite (eb_Ef_reg regs cx 19 19%bv) by reflexivity; exact R19 | lia]. }
assert (E18 : ew E 18 = w64 SHADOW_OFF) by (unfold E; rewrite (eb_Ef_reg regs cx 18 18%bv) by reflexivity; exact R18).
assert (E24 : ew E 24 = w64 (d_p cx)) by (unfold E; rewrite (eb_Ef_reg regs cx 24 24%bv) by reflexivity; exact R24).
assert (HPAY : 0 < d_n cx -> 4096 <= d_p cx /\ d_p cx + d_n cx <= alloc_ceiling).
{ intros Hn0. pose proof (Hpin Hn0) as Hpin1.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR1 Hpin1) as (_ & Hp4096 & Hpceil & _).
  pose proof (req_size_pos (d_n cx) ltac:(lia)) as (_ & Hrq). lia. }
assert (ER2 : ew E 2 = YK11.getr regs 2) by (unfold E; apply (eb_Ef_reg regs cx 2 2%bv); reflexivity).
assert (ER3 : ew E 3 = YK11.getr regs 3) by (unfold E; apply (eb_Ef_reg regs cx 3 3%bv); reflexivity).
assert (ER4 : ew E 4 = YK11.getr regs 4) by (unfold E; apply (eb_Ef_reg regs cx 4 4%bv); reflexivity).
assert (ER8 : ew E 8 = YK11.getr regs 8) by (unfold E; apply (eb_Ef_reg regs cx 8 8%bv); reflexivity).
assert (ER9 : ew E 9 = YK11.getr regs 9) by (unfold E; apply (eb_Ef_reg regs cx 9 9%bv); reflexivity).
assert (ER10 : ew E 10 = w64 (d_F cx)) by (unfold E; rewrite (eb_Ef_reg regs cx 10 10%bv) by reflexivity; exact R10).
assert (ER19 : ew E 19 = w64 (d_n cx)) by (unfold E; rewrite (eb_Ef_reg regs cx 19 19%bv) by reflexivity; exact R19).
assert (U19 : bv_unsigned (ew E 19) = d_n cx) by (rewrite ER19; unfold w64; apply unsigned_lit_small; lia).
assert (Hfin : In (DEC_FCLASS, d_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
change (w64 (DEC_A_LLVMF + 0x074)) with (Z_to_bv 64 (BASE + 116)).
assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ eb_win cx a -> aview segs (w_H W) mem a = aview segs (w_H W) mem a)
  by (intros; reflexivity).
destruct Hcases as [Hn | [Hn | [Hn | Hn]]].
1: pose proof (eb_seat_f cx ly S W regs mem md 0 0 0 LAWS HCELLS HB HCORE R10 R18 R19 R24
     ltac:(rewrite Hn; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
2: pose proof (eb_seat_f cx ly S W regs mem md 1 1 1 LAWS HCELLS HB HCORE R10 R18 R19 R24
     ltac:(rewrite Hn; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
3: pose proof (eb_seat_f cx ly S W regs mem md 2 2 2 LAWS HCELLS HB HCORE R10 R18 R19 R24
     ltac:(rewrite Hn; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
4: pose proof (eb_seat_f cx ly S W regs mem md 3 3 (2 ^ 26 - 1) LAWS HCELLS HB HCORE R10 R18 R19 R24
     ltac:(unfold dec_b_u; rewrite Z.min_r by lia; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
all: fold E in HS.
(* R1: the frame record, its poison, the spill of the frame to 112(s1), up to the size test (+0x104) *)
all: eb_run_to_sh RUNTOP HS HJ 600%Z; [ eb_awr_tac cx HfaS E9 E10 E32 Hsp1b | eb_keep cx K HFr E9 E10 E32; clear HF HG ].
(* the size test (+0x104): taken needs 2 ^ 26 <= n *)
all: eb_branch_plain RUNTOP BR HS;
  [ exfalso; rewrite branch_ne_U, eb_U_srl26, E19, Z.div_small in Hc by lia; rewrite U_SLit in Hc; vm_compute in Hc;
    discriminate Hc
  | clear Hc ].
(* R2: to the first input read (n >= 1) or to +0x258 (n = 0) *)
all: eb_run_to_sh RUNTOP HS HJ 600%Z;
  [ eb_awr_tac cx HfaS E9 E10 E32 Hsp1b | eb_keep cx K HFr E9 E10 E32; clear HF HG; eb_clear_old_ms HS ].
(* n = 0: the length test (+0x114) is taken; R3 runs the n = 0 arm to +0x258 *)
1: eb_branch_plain RUNTOP BR HS;
  [ clear Hc
  | exfalso; rewrite branch_eq_U, E19, U_SLit, Hn in Hc; vm_compute in Hc; discriminate Hc ].
1: eb_run_to_sh RUNTOP HS HJ 600%Z;
  [ eb_awr_tac cx HfaS E9 E10 E32 Hsp1b | eb_keep cx K HFr E9 E10 E32; clear HF HG; eb_clear_old_ms HS ].
(* n >= 1: the input reads run on the token engine, which refuses a writable window over the frame (whose address
   range may meet the shadow band) or over its shadow: both are closed for the reads (which store nothing). *)
2-4: assert (U24 : bv_unsigned (ew E 24) = d_p cx)
  by (destruct (HPAY ltac:(lia)); rewrite E24; unfold w64; apply unsigned_lit_small; lia).
2-4: eb_rewin HS 1%nat 0 0 ltac:(intros ? ?; lia).
2-4: eb_rewin HS 2%nat 0 0 ltac:(intros ? ?; lia).
2-4: lazymatch goal with HS : st_ok_pi _ _ ?Ex _ (restrict (w_H ?Wx) ?msx) |- _ =>
  assert (SHOK : sh_ok segs (SOff 18 0) [] Ex (mrestrict (w_H Wx) (ms_mem msx))) by constructor end.
2-4: paj_run_tok RUN HS HJ SHOK Bspan.
all: try lazymatch goal with |- range_addressable _ _ _ _ =>
  destruct (HPAY ltac:(lia)) as (Hp4096 & Hpceil);
  eapply (eb_ob_input cx ly S W); [ exact LAWS | exact (proj1 HJ) | apply Hpin; lia | exact E18 | exact E24 | lia | lia | lia ] end.
all: try lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => eb_awr_tac cx HfaS E9 E10 E32 Hsp1b end.
all: try (eb_keep cx K HFr E9 E10 E32; clear HF HG; eb_clear_old_ms HS).
(* n = 1 (+0x13c `beqz a3`, a3 = n - 1) and n = 2 (+0x168 `bne a3, a4`, a4 = 1): the length dispatch *)
2-3: eb_branch_plain RUNTOP BR HS.
2-5: first [ exfalso; rewrite ?branch_eq_U, ?branch_ne_U in Hc; rewrite ?U_SOff, ?U_SLit in Hc;
             cbn [ew ewset Nat.eqb] in Hc; rewrite U19, Hn in Hc; vm_compute in Hc; discriminate Hc
           | clear Hc ].
2-3: paj_run_tok RUN HS HJ SHOK Bspan.
all: try lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => eb_awr_tac cx HfaS E9 E10 E32 Hsp1b end.
all: try (eb_keep cx K HFr E9 E10 E32; clear HF HG; eb_clear_old_ms HS).
(* n >= 1 at +0x1f0: the frame and its shadow are opened again for the local's unpoison and its three words *)
2-4: eb_rewin HS 1%nat 0 48 ltac:(intros o Ho; cbn [ms_mem restrict base_val YP09.r_base ew ewset Nat.eqb];
  rewrite E10; exact (proj1 (eb_frame_writable cx ly S W _ _ LAWS (proj1 HJ) Hfin HfaS) o ltac:(lia))).
2-4: eb_rewin HS 2%nat 0 8 ltac:(intros o Ho; cbn [ms_mem restrict base_val YP09.r_base ew ewset Nat.eqb];
  rewrite E32; exact (proj2 (eb_frame_writable cx ly S W _ _ LAWS (proj1 HJ) Hfin HfaS) o Ho)).
2-4: eb_run_to_sh RUNTOP HS HJ 600%Z;
  [ eb_awr_tac cx HfaS E9 E10 E32 Hsp1b | eb_keep cx K HFr E9 E10 E32; clear HF HG; eb_clear_old_ms HS ].
(* the mode select: +0x210 `blt` (byte0 & 3 > 1), then +0x228 `bne` (byte0 & 3 = 2) or +0x214 `bnez`; every
   arm is a leaf *)
2-4: eb_branch_plain RUNTOP BR HS; clear Hc.
2-7: eb_run_to_sh RUNTOP HS HJ 600%Z;
  [ eb_awr_tac cx HfaS E9 E10 E32 Hsp1b | eb_keep cx K HFr E9 E10 E32; clear HF HG; eb_clear_old_ms HS ].
2-7: eb_branch_plain RUNTOP BR HS; clear Hc.
2-13: eb_run_to_sh RUNTOP HS HJ 600%Z;
  [ eb_awr_tac cx HfaS E9 E10 E32 Hsp1b | eb_keep cx K HFr E9 E10 E32; clear HF HG; eb_clear_old_ms HS ].
(* the leaves *)
all: lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?Wx) ?msx) |- _ =>
  pmkst HS; apply SRr_ret; change (Z_to_bv 64 (BASE + 600)) with (w64 (DEC_A_LLVMF + 0x258));
  pose proof (st_ok_region_nth (segs := segs) Ex _ _ 0 _ HS eq_refl) as HR0;
  pose proof (st_ok_region_nth (segs := segs) Ex _ _ 1 _ HS eq_refl) as HR1;
  pose proof (st_ok_region_nth (segs := segs) Ex _ _ 2 _ HS eq_refl) as HR2;
  cbn [restrict ms_mem] in HR0, HR1, HR2;
  eapply (eb_leaf cx ly S W regs mem md (ms_regs msx) (ms_mem msx) _ _ LAWS HB Hfrm HCELLS HOWN HNOERR HROM HCORE Hbl
    Hmle Hmok HJ K)
end.
(* the registers *)
all: try lazymatch goal with |- YK11.getr (ms_regs _) ?r = _ =>
  lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ => let Q := fresh "Q" in prreg HS r Q; rewrite Q; clear Q end;
  rewrite ?E9, ?E10, ?E32, ?U19; try rewrite U24;
  rewrite ?ER2, ?ER3, ?ER4, ?ER8, ?ER9, ?ER10, ?E18, ?ER19, ?E24;
  lazymatch goal with
  | |- _ = w64 ?m => tryif is_evar m then reflexivity
                     else first [ reflexivity | unfold w64; f_equal; unfold dec_b_u, dec_b_len; lia ]
  | |- _ => first [ reflexivity | unfold w64; f_equal; unfold dec_b_u, dec_b_len; lia ]
  end end.
(* the spill slots 8 / 16 / 112 *)
all: try lazymatch goal with |- dec_b_slot _ _ _ _ =>
  unfold dec_b_slot; eapply (eb_slot_of_region _ _ _ 9 (d_sp1 cx));
  [ exact HR0 | cbn [ew ewset Nat.eqb]; exact E9 | eb_in_tac
  | rewrite U_SOff; cbn [ew ewset Nat.eqb]; rewrite ?E10, ?E32, Z.add_0_r; apply zcanon_id; rewrite M64_val;
    unfold d_SH, shadow_addr, SHADOW_OFF in *; lia ] end.
(* the frame's shadow: left redzone, the local unpoisoned (0, 4), right redzone *)
all: try lazymatch goal with |- dec_b_fsh _ _ _ _ => unfold dec_b_fsh; split; [|split; [|split]] end.
all: try lazymatch goal with |- forall i, 0 <= i < 4 -> _ =>
  let i := fresh "i" in let Hi := fresh "Hi" in let Hci := fresh "Hci" in
  intros i Hi; assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3) as Hci by lia; destruct Hci as [-> | [-> | [-> | ->]]] end.
all: try lazymatch goal with |- forall i, 6 <= i < 8 -> _ =>
  let i := fresh "i" in let Hi := fresh "Hi" in let Hci := fresh "Hci" in
  intros i Hi; assert (i = 6 \/ i = 7) as Hci by lia; destruct Hci as [-> | ->] end.
all: try lazymatch goal with |- aview segs _ _ (d_SH _ + _) = Some _ =>
  eapply (eb_byte_of_region _ _ _ 32 (d_SH cx));
  [ exact HR2 | cbn [ew ewset Nat.eqb]; exact E32 | eb_in_tac | rewrite U_SLit; vm_compute; reflexivity ] end.
(* the mode: a table pointer word, or the local with its two fields *)
all: try lazymatch goal with |- (?m = _ \/ _ \/ _) \/ _ =>
  lazymatch m with
  | d_F _ + 32 =>
    right; split; [reflexivity|];
    eapply (eb_local_fields _ _ _ (d_F cx)); [ exact HR1 | cbn [ew ewset Nat.eqb]; exact E10 | eb_in_tac | eb_in_tac | | ];
    lazymatch goal with
    | |- eb_sbyte _ (SAlu ALU_SRA _ _) =>
      apply eb_sbyte_sra; rewrite U_SOff; cbn [ew ewset Nat.eqb]; unfold E; rewrite eb_Ef_34; unfold w64;
      pose proof (eb_byte_range cx 1); rewrite unsigned_lit_small by lia; rewrite Z.add_0_r, zcanon_id by (rewrite M64_val; lia);
      lia
    | |- eb_sbyte _ (SExt true 8 _) =>
      apply eb_sbyte_sext; rewrite U_SOff; cbn [ew ewset Nat.eqb]; unfold E; rewrite eb_Ef_35; unfold w64;
      pose proof (eb_byte_range cx 2); rewrite unsigned_lit_small by lia; rewrite Z.add_0_r, zcanon_id by (rewrite M64_val; lia);
      lia
    | |- eb_sbyte _ (SLit _) => apply eb_sbyte_zero; rewrite U_SLit; reflexivity
    | |- eb_sbyte _ (SOff 19 _) => apply eb_sbyte_zero; rewrite U_SOff; cbn [ew ewset Nat.eqb]; rewrite U19, Hn; reflexivity
    end
  | _ => left; first [ left; reflexivity | right; left; reflexivity | right; right; reflexivity ]
  end end.
Qed.
End front.

(* ------------------------------------------------------------------ *)
(* 6. llvm_b_early: the front to +0x258, then the tail to llvm_b_st_27c  *)
(* ------------------------------------------------------------------ *)
Theorem llvm_b_early :
  llvm_b_early_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
unfold llvm_b_early_stmt.
intros HPCM HUTR HCELLS HOWN HNOERR LAWS MLAWS MTL AMALLOC cx W c HB HROM H074.
destruct H074 as (fx & ly & S & regs & mem & md & -> & Hfrm & HCORE & Hbl & Hmle & Hmok & R10 & R18 & R19 & R24 & _).
eapply SRr_bind.
{ exact (eb_front_fx (fx := fx) cx ly S W regs mem md HCELLS HOWN HNOERR LAWS HB HROM Hfrm HCORE Hbl Hmle Hmok
    R10 R18 R19 R24). }
intros W2 c2 _ (fx2 & ly2 & S2 & regs2 & mem2 & md2 & mode & nch & ns & -> & Hfrm2 & HCORE2 & Hbl2 & Hmle2 & Hmok2
  & R17 & R18' & R19' & R24' & R20 & R21 & R23 & R22 & HMOK & Hmode & HFSH & HS8 & HS16 & HS112).
eapply SRr_bind.
{ exact (eb_tail_fx (fx := fx2) cx ly2 S2 W2 regs2 mem2 md2 mode nch ns HPCM HUTR HCELLS HOWN HNOERR LAWS MTL
    (AMALLOC fx2) HB HROM Hfrm2 HCORE2 Hbl2 Hmle2 Hmok2 R17 R18' R19' R24' R20 R21 R23 R22 HMOK Hmode HFSH HS8 HS16
    HS112). }
intros W3 c3 _ H3. apply SRr_ret. left. exact H3.
Qed.

End eb.
