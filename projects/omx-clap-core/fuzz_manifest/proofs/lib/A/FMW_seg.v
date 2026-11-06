(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACep.v, with its module paths changed; 257 of its 299 lines of code are new or changed and 184 lines of the source are left out. *)
(* fm program part, walk glue shared by the FMW_* walks: the B facts a walk reads, reading a symbolic region back as
   val_mem, the entry symbolic state of a function, and the call glue for runtime routines (FMH_Rt.v rt_post_ro and the
   snprintf post) over the caller's ajournal. Stated for tfibsegs. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d YC20.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI00 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AF0l ACej FMPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMW_kit FMW_K.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

(* the facts about B a walk reads: the code addresses (A/AF0l.v), the shadow-base .got slot and cell in every AR state
   (from TfibSyms' constant cells, A/AF0m.v:80, :175, through ARm am_const), and fuzz/alloc.c's statics off the
   runtime's statics *)
Record FmB : Prop := {
  fb_code : as_code B = Tfib_code;
  fb_cells : forall ly S (W : world tfibsegs) mem md, AR tfibsegs B ly S W mem md ->
    val_mem tfibsegs (rdW W mem) FMW_GOT_shadow 8 FMW_shadow_cell /\ val_mem tfibsegs (rdW W mem) FMW_shadow_cell 8 FMW_SB;
  (* fuzz/alloc.c's statics are neither runtime-owned statics nor errno (TfibB: ts_owned / ts_errno) *)
  fb_pstat : forall a, inFP FM_PSTAT_FP a -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)
}.

Lemma fmw_writable_kept : forall H (m m2 : word -> option byte) a,
(apresent H m a -> apresent H m2 a) -> writable_at tfibsegs (mrestrict H m) a -> writable_at tfibsegs (mrestrict H m2) a.
Proof.
intros H m m2 a Hp Hw. unfold writable_at, wview, mrestrict in *. revert Hw.
destruct (H (Z_to_bv 64 a)) eqn:EH; intros Hw; [exact Hw|].
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
- destruct (Hp (conj EH (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
- destruct (m2 (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
Lemma fmw_region_kept_aview : forall E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview tfibsegs H m2 a = aview tfibsegs H m a) ->
(forall a, apresent H m a -> apresent H m2 a) ->
region_kept tfibsegs E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview tfibsegs). apply Hav. exact Ha.
- apply fmw_writable_kept. apply Hp.
Qed.

(* ---- the entry symbolic state of a function with a frame of F bytes: every register its own atom, atom 32 = the
   shadow base; regions: the frame below sp (writable, empty), the .got slot and the shadow-base cell ---- *)
Definition fmw_entry_ss (pc F : Z) : sstate :=
mkSS pc sr_atoms [fmw_stack_region F []; fmw_got_region; fmw_bcell_region 32] None
(mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF FMW_SB FMW_SB 0)] [] []).

Lemma fmw_entry_sb : forall (FB : FmB) W ly S regs mem md STK pc F,
AR tfibsegs B ly S W mem md -> astk_ok STK ly (spZ regs) -> 0 <= F <= STK ->
(forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W) mem a) ->
regions_wf [fmw_stack_region F []; fmw_got_region; fmw_bcell_region 32] = true ->
st_ok tfibsegs (Ereg regs [Z_to_bv 64 FMW_SB]) (fmw_entry_ss pc F)
(restrict (w_H W) (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs))).
Proof.
intros FB W ly S regs mem md STK pc F HAR Hstk HF Hpres HWF.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (fb_cells FB ly S W mem md HAR) as (Kgot & Kcell).
rewrite restrict_mkst_fx.
set (E := Ereg regs [Z_to_bv 64 FMW_SB]).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 FMW_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
unfold fmw_entry_ss. apply (entry_st_ok_full tfibsegs); change (Ereg regs [Z_to_bv 64 FMW_SB]) with E.
- apply regs_ok_Ereg.
- exact HWF.
- unfold fmw_stack_region, fmw_got_region, fmw_bcell_region.
repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable tfibsegs). apply Hpres. lia.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
unfold FMW_GOT_shadow. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 0x999b0) at 1.
apply (chunk_ok_val tfibsegs E _ 0 0x999b0 8 (SLit FMW_shadow_cell) FMW_shadow_cell); [reflexivity | unfold FMW_shadow_cell; zside | zside |].
exact Kgot.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
unfold FMW_shadow_cell. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 0xa1d78) at 1.
apply (chunk_ok_val tfibsegs E _ 0 0xa1d78 8 (SOff 32 0) FMW_SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold FMW_SB; zside | zside |].
exact Kcell.
- apply pairwise_disjoint_of_extents.
unfold fmw_stack_region, fmw_got_region, fmw_bcell_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite Usp.
unfold FMW_GOT_shadow, FMW_shadow_cell.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 Hstk0 HF. clear. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32. rewrite !unsigned_lit_small by (unfold FMW_SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil C1 Hstk0 Hal16. clear. unfold FMW_SB. intros.
repeat match goal with |- _ /\ _ => split end; lia.
Qed.

(* ---- the relro view rides through any ajournal whose footprint is empty ---- *)
Lemma fmw_relro_img : forall a, FM_RLO <= a < FM_RHI -> in_img tfibsegs a.
Proof.
intros a Ha. unfold FM_RLO, FM_RHI in Ha. unfold in_img. eexists. split; [right; right; left; reflexivity|].
match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) => let l := eval vm_compute in lo in let h := eval vm_compute in sz in
change lo with l; change sz with h end. lia.
Qed.
(* ---- runtime call windows over the caller's journal ---- *)
Lemma fmw_ecall_pre_k : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs STK1 (o : Z),
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
spZ regs = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK <= STK1 -> STK1 - o <= STK ->
YK0s.ret_ok (getr regs 1) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
ecall_pre_k tfibsegs B STK1 lyc Sc W regs memc mdc.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs STK1 o HJ Hsp Hal Hneg HE Hbud Hra Hgp Htp.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _ & HQT).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (ESTACK = 4096) as Hes by reflexivity.
split; [|split; [|split]].
- eapply (ecall_pre_at tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs o HJ Hsp Hal Hneg); [lia | exact Hra | exact Hgp | exact Htp].
- rewrite Eslo. exact Hceil.
- rewrite Eslo, Hsp. lia.
- intros a Ha. apply Hpres. rewrite Hsp in Ha. lia.
Qed.

(* a runtime routine with an rt_post_ro contract (FMH_Rt.v), called from a journal state: the caller's journal is
   kept (the routine writes only its stack window below the caller's sp) *)
Lemma fmw_aj_rt_ro : forall W regs mem mdc pc STK sp0 FP ly S W0 mem0 md0 lyc Sc k STK1 (R : Z -> Prop) (o : Z),
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 [] lyc Sc W mem mdc k ->
spZ regs = sp0 + o -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
SRr tfibsegs W (cfg_at tfibsegs pc regs mem mdc) (rt_post_ro tfibsegs B STK1 lyc Sc W regs mem mdc R) ->
SRr tfibsegs W (cfg_at tfibsegs pc regs mem mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 v,
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom tfibsegs)) md2 /\
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 [] lyc Sc W mem2 md2 k /\
aregs_preserved regs regs2 /\ getr regs2 10 = w64 v /\ 0 <= v < 2 ^ 64 /\ R v /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK1 <= a < spZ regs) -> aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) mem a)).
Proof.
intros W regs mem mdc pc STK sp0 FP ly S W0 mem0 md0 lyc Sc k STK1 R o HJ Hsp Hneg Hstk1 Hbud HC.
eapply SRr_mono; [exact HC|]. cbv beta.
intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HAR2 & HP & Hsame & H10 & Hv & HR & Hfr & Hgr).
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [|exact (conj HP (conj H10 (conj Hv (conj HR Hfr))))].
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
eapply (ajournal_after_write tfibsegs B LAWS fmw_segs_low STK sp0 FP ly S W0 mem0 md0 [] lyc Sc W mem mdc k mem2 md2
(fun a => spZ regs - STK1 <= a < spZ regs) Sc []).
- exact HJ.
- exact Hfr.
- exact Hgr.
- exact Hsame.
- intros a Ha. left. left. left. rewrite Hsp in Ha. lia.
- exact HAR2.
- reflexivity.
- reflexivity.
- lia.
- exact Hfrs.
- exact HQT.
Qed.

(* ---- facts about memory below alloc_ceiling (strings, their shadow, fuzz/alloc.c's statics) survive any step that
   leaves the view of that part of memory unchanged (the frame of a run whose windows are on the stack, the memory
   frame of an rt_post_ro call) ---- *)
Definition low_same (W W' : world tfibsegs) (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < alloc_ceiling -> aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a.
Lemma low_same_refl : forall W m, low_same W W m m.
Proof. intros W m a _. reflexivity. Qed.
Lemma low_same_trans : forall W1 W2 W3 m1 m2 m3, low_same W1 W2 m1 m2 -> low_same W2 W3 m2 m3 -> low_same W1 W3 m1 m3.
Proof. intros W1 W2 W3 m1 m2 m3 H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.
Lemma low_same_of_frame : forall E rs W (m m' : word -> option byte),
  frame_of E rs (rdW W m) (rdW W m') ->
  (forall r, In r rs -> r_whi r <= r_wlo r \/ alloc_ceiling <= base_val E (r_base r) + r_wlo r) ->
  low_same W W m m'.
Proof.
intros E rs W m m' HF Hw a Ha. apply (aview_eq_of tfibsegs). apply HF.
rewrite unsigned_lit_small by (pose proof (proj1 alloc_ceiling_val); lia).
intros (r & Hin & Hr). destruct (Hw r Hin) as [H1 | H1]; lia.
Qed.
Lemma low_same_of_win : forall W m m' lo hi,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  alloc_ceiling <= lo -> low_same W W m m'.
Proof. intros W m m' lo hi H Hlo a Ha. pose proof (proj1 alloc_ceiling_val). apply H; lia. Qed.
Lemma val_mem_low : forall W W' m m' a n v, low_same W W' m m' -> 0 <= a -> a + Z.of_nat n <= alloc_ceiling ->
  val_mem tfibsegs (rdW W m) a n v -> val_mem tfibsegs (rdW W' m') a n v.
Proof.
intros W W' m m' a n v HL Ha Hn Hv. eapply (val_mem_kept tfibsegs); [|exact Hv]. intros k Hk. apply HL. lia.
Qed.
Lemma garr8_low : forall W W' m m' p l, low_same W W' m m' -> 0 <= p -> p + Z.of_nat (length l) <= alloc_ceiling ->
  garr8 tfibsegs (rdW W m) p l -> garr8 tfibsegs (rdW W' m') p l.
Proof.
intros W W' m m' p l HL Hp Hl Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
eapply val_mem_low; [exact HL | lia | cbn; lia | exact Hv].
Qed.
Lemma shadow_low : forall x, 0 <= x < kHighMemEnd -> 0 <= SHADOW_OFF + x / 8 < alloc_ceiling.
Proof.
intros x Hx. pose proof (proj1 alloc_ceiling_val). unfold kHighMemEnd, SHADOW_OFF in *.
split; [pose proof (Z.div_pos x 8); lia|]. assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma cstr_ok_low : forall W W' m m' p l, low_same W W' m m' -> cstr_ok tfibsegs W m p l -> cstr_ok tfibsegs W' m' p l.
Proof.
intros W W' m m' p l HL ((Hg & Hnz) & H4096 & Hceil & H32 & Ham & Hra & Hhull & Htail).
pose proof (proj1 alloc_ceiling_val) as AC.
assert (Hp47 : p + Z.of_nat (length l) + 8 <= kHighMemEnd) by (unfold kHighMemEnd; lia).
split; [split; [|exact Hnz]|].
{ eapply garr8_low; [exact HL | lia | rewrite length_app; cbn; lia | exact Hg]. }
split; [exact H4096|]. split; [exact Hceil|]. split; [exact H32|]. split; [exact Ham|]. split; [|split].
- eapply range_addressable_agree; [|exact Hra]. intros x Hx. unfold shadow_of_addr. apply HL. apply shadow_low. lia.
- intros s Hs. rewrite (HL s). { exact (Hhull s Hs). }
  unfold shadow_addr in Hs. pose proof (shadow_low p ltac:(lia)). pose proof (shadow_low (p + (Z.of_nat (length l) + 1) - 1) ltac:(lia)).
  pose proof (Z.div_mod (SHADOW_OFF + p / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SHADOW_OFF + p / 8) 8 ltac:(lia)).
  pose proof (Z.div_mod (SHADOW_OFF + (p + (Z.of_nat (length l) + 1) - 1) / 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (SHADOW_OFF + (p + (Z.of_nat (length l) + 1) - 1) / 8) 8 ltac:(lia)).
  assert ((p + (Z.of_nat (length l) + 1) - 1) / 8 < 2 ^ 44 - 2) by (apply Z.div_lt_upper_bound; unfold kHighMemEnd in *; lia).
  unfold SHADOW_OFF in *. lia.
- intros a Ha. rewrite (HL a) by (pose proof (Z.mod_pos_bound (p + Z.of_nat (length l)) 8 ltac:(lia)); lia). exact (Htail a Ha).
Qed.
Lemma arodata_low : forall (W W' : world tfibsegs) m m', low_same W W' m m' ->
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) m) -> arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W') m').
Proof.
intros W W' m m' HL HR a Hro Ho He. pose proof (proj1 alloc_ceiling_val) as AC.
assert (Ha : 0 <= a < alloc_ceiling).
{ destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [|unfold FM_RLO, FM_RHI in Hr; lia].
  assert (Hi : in_img tfibsegs a) by (exists sg; split; [exact Hin | exact Hr]).
  pose proof (fmw_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl. lia. }
rewrite (HL a Ha). exact (HR a Hro Ho He).
Qed.
Lemma fm_glob_low : forall W W' m m' live peak cnt fail, low_same W W' m m' ->
  fm_glob tfibsegs W m live peak cnt fail -> fm_glob tfibsegs W' m' live peak cnt fail.
Proof.
intros W W' m m' live peak cnt fail HL (H1 & H2 & H3 & H4 & R).
pose proof (proj1 alloc_ceiling_val) as AC.
split; [|split; [|split; [|split]]]; try exact R;
(eapply val_mem_low; [exact HL | unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL; lia | unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL; cbn; lia | eassumption]).
Qed.

(* ---- a mid-function symbolic state built from concrete facts: every register its own atom; atom 32 = the shadow
   base; atoms 33.. = the values of the frame slots at offsets offs above sp (the frame [sp, sp + F) is writable) ---- *)
Fixpoint fmw_chunks (k0 : nat) (offs : list Z) : list YP09.chunk :=
  match offs with [] => [] | o :: t => YP09.mkChunk o (CVal 8 (SOff k0 0)) :: fmw_chunks (S k0) t end.
Definition fmw_frame_region (F : Z) (offs : list Z) : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 F 0 F (fmw_chunks 33 offs).
Definition fmw_env (regs : bvmap 5 word) (vals : list Z) : env := Ereg regs (Z_to_bv 64 FMW_SB :: map (Z_to_bv 64) vals).
Lemma fmw_chunks_ok : forall E m b offs (k0 : nat) (f : nat -> Z),
  (forall j o, nth_error offs j = Some o -> ew E (k0 + j) = Z_to_bv 64 (f j) /\ 0 <= f j < 2 ^ 64 /\ val_mem tfibsegs m (b + o) 8 (f j)) ->
  Forall (YP09.chunk_ok tfibsegs E m b) (fmw_chunks k0 offs).
Proof.
intros E m b offs. induction offs as [|o t IH]; intros k0 f Hf; cbn [fmw_chunks]; constructor.
- destruct (Hf 0%nat o eq_refl) as (He & Hr & Hv). rewrite Nat.add_0_r in He.
  apply (chunk_ok_val tfibsegs E m b o 8 (SOff k0 0) (f 0%nat)); [cbn [sv_denot]; rewrite He, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | exact Hr | lia | exact Hv].
- apply (IH (S k0) (fun j => f (S j))). intros j o' Ho'. destruct (Hf (S j) o' Ho') as (He & Hr & Hv).
  split; [replace (S k0 + j)%nat with (k0 + S j)%nat by lia; exact He | split; [exact Hr | exact Hv]].
Qed.
Lemma fmw_env_extra : forall regs vals j, (j < length vals)%nat ->
  ew (fmw_env regs vals) (33 + j) = Z_to_bv 64 (nth j vals 0).
Proof.
intros regs vals j Hj. unfold fmw_env. replace (33 + j)%nat with (32 + S j)%nat by lia. rewrite ew_Ereg_extra.
cbn [nth]. rewrite <- (map_nth (Z_to_bv 64) vals 0 j). reflexivity.
Qed.
Lemma fmw_env_sb : forall regs vals, ew (fmw_env regs vals) 32 = Z_to_bv 64 FMW_SB.
Proof. intros regs vals. unfold fmw_env. exact (ew_Ereg_extra regs _ 0). Qed.
Lemma fmw_env_reg : forall regs vals n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (fmw_env regs vals) n = getr regs r.
Proof. intros regs vals n r H. unfold fmw_env. exact (ew_Ereg_nat regs _ n r H). Qed.
Lemma fmw_mid_entry : forall (W : world tfibsegs) regs mem pc F offs vals rs fs,
  0 <= spZ regs -> spZ regs + F <= 2 ^ 64 ->
  (forall a, spZ regs <= a < spZ regs + F -> apresent (w_H W) mem a) ->
  length vals = length offs ->
  (forall j o, nth_error offs j = Some o -> val_mem tfibsegs (rdW W mem) (spZ regs + o) 8 (nth j vals 0) /\ 0 <= nth j vals 0 < 2 ^ 64) ->
  regions_wf (fmw_frame_region F offs :: rs) = true ->
  Forall (region_ok tfibsegs (fmw_env regs vals) (rdW W mem)) rs ->
  pairwise_disjoint (fmw_env regs vals) (fmw_frame_region F offs :: rs) ->
  atoms_ok (fmw_env regs vals) fs ->
  st_ok tfibsegs (fmw_env regs vals) (mkSS pc sr_atoms (fmw_frame_region F offs :: rs) None (mkFacts fs [] []))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs))).
Proof.
intros W regs mem pc F offs vals rs fs Hsp0 Hsp1 Hpres Hlen Hvals Hwf Hrs Hpd Hfs.
rewrite restrict_mkst_fx. unfold fmw_env at 1. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- exact Hwf.
- constructor; [|exact Hrs].
  assert (Usp : bv_unsigned (ew (fmw_env regs vals) 2) = spZ regs) by (rewrite (fmw_env_reg regs vals 2 2%bv eq_refl); reflexivity).
  unfold region_ok, fmw_frame_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  change (Ereg regs (Z_to_bv 64 FMW_SB :: map (Z_to_bv 64) vals)) with (fmw_env regs vals). rewrite Usp.
  split; [lia|]. split; [lia|]. split.
  + intros o Ho. apply (apresent_writable tfibsegs). apply Hpres. lia.
  + apply (fmw_chunks_ok _ _ _ offs 33 (fun j => nth j vals 0)). intros j o Ho.
    destruct (Hvals j o Ho) as [Hv Hr]. split; [|split; [exact Hr | exact Hv]].
    apply fmw_env_extra. rewrite Hlen. apply nth_error_Some. rewrite Ho. discriminate.
- exact Hpd.
- split; [exact Hfs | split; exact I].
Qed.

(* the symbolic state a walk resumes from when the next stretch touches no memory: every register its own atom *)
Definition fss_nr (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
Lemma fmw_resume_nr : forall (W : world tfibsegs) regs extra mem pc,
  st_ok tfibsegs (Ereg regs extra) (fss_nr pc) (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs))).
Proof.
intros W regs extra mem pc. rewrite restrict_mkst_fx. unfold fss_nr. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- reflexivity.
- constructor.
- cbn. tauto.
- split; [exact I | split; exact I].
Qed.
Lemma same_below_frame : forall E rs m m' lo, frame_of E rs m m' ->
  Forall (fun r => YP09.r_whi r <= YP09.r_wlo r \/ lo <= base_val E (YP09.r_base r) + YP09.r_wlo r) rs -> lo <= 2 ^ 64 ->
  same_below m m' lo.
Proof.
intros E rs m m' lo HF Hrs Hlo x Hx. apply HF. intros (r & Hin & Hr).
rewrite unsigned_lit_small in Hr by lia.
destruct (proj1 (Forall_forall _ _) Hrs r Hin) as [H|H]; lia.
Qed.
Lemma frame_nil_same : forall E m m', frame_of E [] m m' -> same_below m m' (2 ^ 64).
Proof. intros E m m' HF x _. apply HF. intros (r & [] & _). Qed.
End s.
