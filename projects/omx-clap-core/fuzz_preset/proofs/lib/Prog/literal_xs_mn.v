(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset literal KEEPS memnorm: the image-free part of lib/{A,B}/Prog/literal_mn.v.
   rule 24: proves function literal (reuse search: `proof-index skip_ws hex4 put_utf8 literal`, 2026-10-28T21:1xZ, exit 0; named-list cold grep 2026-10-29 exit 0; CONFIRM R24ReaderLeaf 2026-10-28T21:15Z). VERBATIM: `literal: 8 file(s) named for it, 22 file(s) use its address, 0 related; in an earlier delivery 1 named for it and 524 name(s) that hold it, in 741 tree(s)` - named hits are fuzz_preset/fuzz_state released PLAIN + UBSAN proofs; none on asan builds; cold AsanRT walks template only.
   memnorm: YAkMemnorm.memnorm segs m (lib/Reusable/YAkMemnorm.v:41), the body of YAjMemnorm.memnorm written over LPS only.
   WHAT:
   - tliteral_leaf_postXmn / tliteral_leafXmn: lib/Prog/literal_xs.v's tliteral_leaf_postX / tliteral_leafX (same quantifiers, same premises) with ONE conjunct appended LAST to the post, `YAkMemnorm.memnorm segs memc -> YAkMemnorm.memnorm segs mem2` (the m-form, PRH_Base.v fQmn); no entry premise. The post's two result arms share mem2, so the conjunct after the disjunction holds in each arm.
   - tliteral_leaf_postXP / tliteral_leafXP: the run's form, over an invariant Pinv of the full overlay: Pinv memc right after the journal premise, Pinv mem2 as the last conjunct.
   - tliteral_leafXmn_of: tliteral_leafXP at the invariant R m := (YAkMemnorm.memnorm segs memc -> YAkMemnorm.memnorm segs m) of the entry memory memc (the srr_inv_laws_imp form of YGcallMxmn.v's header, h-hpreset-7 11:30Z) gives tliteral_leafXmn: R memc holds trivially, and R mem2 is the m-form conjunct. The call rules state their keeps as the same implication (YGcallMxmn.v b47cf7942c3d, s1b's), so the walk composes them; no case split, no entry premise.
   - msteps_keeps segs Pinv: the statement of SRr_msteps_inv (YC80x.v since s1b 459129c18903; YSRrMemnorm.v before; lib/B/Prog/skip_ws_mn.v's spelling), a hypothesis here, instantiated in the image files after `Require YSRrMemnorm`.
   - Twins over msteps_keeps of the two runners lib/{A,B}/Prog/literal_x.v uses: SRr_chain_pi_tok_AJxP / SRr_run_pi_tok_AJxP (YC80x.v's SRr_chain_pi_tok_AJx / SRr_run_pi_tok_AJx, the proof of YSRrMemnorm.v's _inv twins with SRr_msteps_inv replaced by msteps_keeps) and SRr_chain_pi_tok_AJx_frP / SRr_run_pi_tok_AJx_frP (literal_xs.v's _fr runners, likewise); paj_run_xP / paj_run_x_frP at the image instance; the tactic paj_run_tok_xP (YSRrMemnorm.v's paj_run_tok_x_inv). In each the Pinv premise comes right after the journal premise.
   - read-only premise (2026-10-29): tliteral_leafXmn / tliteral_leafXP take PresetRodata.arodata_okP segs rlo rhi B (aview segs (w_H W) memc) (lib/Spec/PresetRodata.v 4eb7e95e7e93, its one home at the kit decff67d721f), as lib/Prog/literal_xs.v's tliteral_leafX does (its header says why: rom_view segs W memc needed pal_rom_ok, FALSE at TfibB, 68059ec877b). Section a's rlo rhi come after ARx, so each text takes them before VRA.
   - image-bounds premise (#102), as lib/Prog/literal_xs.v's: YCbq.off_img_at ilo itop q 16 at the caller's image bounds (Section a's ilo itop, after rlo rhi), in place of the image-A-bound YCbq.off_img q 16.
   ORDER: no file Required here loads lib/Lib/LiaTwx2.v (YAkMemnorm.v's header), so the image walks that use this file run under the lia lib/{A,B}/Prog/literal_x.v were proved with. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import literal_xs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRodata.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable Pinv : (word -> option byte) -> Prop.
Definition msteps_keeps : Prop :=
forall (W : world segs) ms msr' model (Q : world segs -> config -> Prop),
msteps segs (restrict (w_H W) ms) msr' ->
Pinv (ms_mem ms) ->
(forall model', same_but_materialized model model' ->
hclean (w_H W) msr' ->
Pinv (ms_mem (unrestrict (w_H W) (ms_mem ms) msr')) ->
SRr segs W (mkCfg (unrestrict (w_H W) (ms_mem ms) msr') model') Q) ->
SRr segs W (mkCfg ms model) Q.
End k.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variables rlo rhi : Z.
Variables ilo itop : Z.
Definition tliteral_leaf_postXmn (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (Hp : list Z) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (Hpc : list Z) (W : world segs)
(memc : word -> option byte) (k : Z) (regs : bvmap 5 word) (q v ty p text : Z) (txt cw : list Z)
: world segs -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom segs)) md2 /\
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regs regs2 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - LIT_STK <= a < spZ regs) -> ~ (q <= a < q + 8) -> ~ (v <= a < v + 4) ->
aview segs (w_H W) mem2 a = aview segs (w_H W) memc a) /\
((PjGrammar.prefixb cw (skipn (Z.to_nat (p - text)) txt) = true /\ getr regs2 10 = w64 0 /\
val_mem segs (mrestrict (w_H W) mem2) q 8 (p + Z.of_nat (length cw)) /\
val_mem segs (mrestrict (w_H W) mem2) v 4 ty) \/
(PjGrammar.prefixb cw (skipn (Z.to_nat (p - text)) txt) = false /\ getr regs2 10 = w64 (-1) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - LIT_STK <= a < spZ regs) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memc a))) /\
(YAkMemnorm.memnorm segs memc -> YAkMemnorm.memnorm segs mem2).
Definition tliteral_leafXmn (VRA a : Z) : Prop :=
forall STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k (regs : bvmap 5 word)
(q w ty v p text len : Z) (txt cw slack : list Z),
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
YK0s.ret_ok (getr regs 1) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 q -> getr regs 11 = w64 w -> getr regs 12 = w64 ty -> getr regs 13 = w64 v ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - LIT_STK -> spZ regs <= sp0 ->
q mod 8 = 0 -> 4096 <= q -> amem_range q 16 -> off_img_at ilo itop q 16 -> (spZ regs <= q \/ q + 16 <= spZ regs - LIT_STK) ->
(forall x, q <= x < q + 8 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x /\ apresent (w_H W) memc x) ->
val_mem segs (mrestrict (w_H W) memc) q 8 p -> val_mem segs (mrestrict (w_H W) memc) (q + 8) 8 (text + len) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF q 16 ->
0 < text -> text <= p <= text + len -> text + len < 2 ^ 62 -> Z.of_nat (length txt) = len ->
garr8 segs (mrestrict (w_H W) memc) text txt ->
amem_range text len -> range_addressable (aview segs (w_H W) memc) SHADOW_OFF text len ->
(0 < len -> shadow_hull_vis (aview segs (w_H W) memc) text len) ->
(spZ regs <= text \/ text + len <= spZ regs - LIT_STK) ->
0 < w -> Z.of_nat (length cw) + 1 < 2 ^ 32 -> w + Z.of_nat (length cw) + 1 + Z.of_nat (length slack) <= 2 ^ 63 ->
garr8 segs (mrestrict (w_H W) memc) w (cw ++ 0 :: slack) ->
~ In 0 cw -> (- (w + Z.of_nat (length cw) + 1)) mod 8 <= Z.of_nat (length slack) ->
amem_range w (Z.of_nat (length cw) + 1) ->
amem_range8 w (Z.of_nat (length cw) + 1) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF w (Z.of_nat (length cw) + 1) ->
shadow_hull_vis (aview segs (w_H W) memc) w (Z.of_nat (length cw) + 1) ->
(spZ regs <= w \/ w + Z.of_nat (length cw) + 1 + Z.of_nat (length slack) <= spZ regs - LIT_STK) ->
PresetRodata.arodata_okP segs rlo rhi B (aview segs (w_H W) memc) ->
0 <= ty <= 2 -> v mod 8 = 0 -> 4096 <= v -> amem_range v 4 -> (forall x, v <= x < v + 4 -> ~ in_img segs x) ->
(spZ regs <= v \/ v + 4 <= spZ regs - LIT_STK) ->
(forall x, v <= x < v + 4 ->
  (awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x \/ wr_fp_frame FP S lyc x) /\ apresent (w_H W) memc x) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF v VRA ->
(q + 16 <= v \/ v + 4 <= q) ->
SRr segs W (cfg_at segs a regs memc mdc)
(tliteral_leaf_postXmn STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc k regs q v ty p text txt cw).
Definition tliteral_leaf_postXP (Pinv : (word -> option byte) -> Prop) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
(Hp : list Z) (W0 : world segs) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
(Hpc : list Z) (W : world segs) (memc : word -> option byte) (k : Z) (regs : bvmap 5 word) (q v ty p text : Z) (txt cw : list Z)
: world segs -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom segs)) md2 /\
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regs regs2 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - LIT_STK <= a < spZ regs) -> ~ (q <= a < q + 8) -> ~ (v <= a < v + 4) ->
aview segs (w_H W) mem2 a = aview segs (w_H W) memc a) /\
((PjGrammar.prefixb cw (skipn (Z.to_nat (p - text)) txt) = true /\ getr regs2 10 = w64 0 /\
val_mem segs (mrestrict (w_H W) mem2) q 8 (p + Z.of_nat (length cw)) /\
val_mem segs (mrestrict (w_H W) mem2) v 4 ty) \/
(PjGrammar.prefixb cw (skipn (Z.to_nat (p - text)) txt) = false /\ getr regs2 10 = w64 (-1) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - LIT_STK <= a < spZ regs) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memc a))) /\
Pinv mem2.
Definition tliteral_leafXP (Pinv : (word -> option byte) -> Prop) (VRA a : Z) : Prop :=
forall STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k (regs : bvmap 5 word)
(q w ty v p text len : Z) (txt cw slack : list Z),
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
Pinv memc ->
YK0s.ret_ok (getr regs 1) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 q -> getr regs 11 = w64 w -> getr regs 12 = w64 ty -> getr regs 13 = w64 v ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - LIT_STK -> spZ regs <= sp0 ->
q mod 8 = 0 -> 4096 <= q -> amem_range q 16 -> off_img_at ilo itop q 16 -> (spZ regs <= q \/ q + 16 <= spZ regs - LIT_STK) ->
(forall x, q <= x < q + 8 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x /\ apresent (w_H W) memc x) ->
val_mem segs (mrestrict (w_H W) memc) q 8 p -> val_mem segs (mrestrict (w_H W) memc) (q + 8) 8 (text + len) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF q 16 ->
0 < text -> text <= p <= text + len -> text + len < 2 ^ 62 -> Z.of_nat (length txt) = len ->
garr8 segs (mrestrict (w_H W) memc) text txt ->
amem_range text len -> range_addressable (aview segs (w_H W) memc) SHADOW_OFF text len ->
(0 < len -> shadow_hull_vis (aview segs (w_H W) memc) text len) ->
(spZ regs <= text \/ text + len <= spZ regs - LIT_STK) ->
0 < w -> Z.of_nat (length cw) + 1 < 2 ^ 32 -> w + Z.of_nat (length cw) + 1 + Z.of_nat (length slack) <= 2 ^ 63 ->
garr8 segs (mrestrict (w_H W) memc) w (cw ++ 0 :: slack) ->
~ In 0 cw -> (- (w + Z.of_nat (length cw) + 1)) mod 8 <= Z.of_nat (length slack) ->
amem_range w (Z.of_nat (length cw) + 1) ->
amem_range8 w (Z.of_nat (length cw) + 1) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF w (Z.of_nat (length cw) + 1) ->
shadow_hull_vis (aview segs (w_H W) memc) w (Z.of_nat (length cw) + 1) ->
(spZ regs <= w \/ w + Z.of_nat (length cw) + 1 + Z.of_nat (length slack) <= spZ regs - LIT_STK) ->
PresetRodata.arodata_okP segs rlo rhi B (aview segs (w_H W) memc) ->
0 <= ty <= 2 -> v mod 8 = 0 -> 4096 <= v -> amem_range v 4 -> (forall x, v <= x < v + 4 -> ~ in_img segs x) ->
(spZ regs <= v \/ v + 4 <= spZ regs - LIT_STK) ->
(forall x, v <= x < v + 4 ->
  (awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x \/ wr_fp_frame FP S lyc x) /\ apresent (w_H W) memc x) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF v VRA ->
(q + 16 <= v \/ v + 4 <= q) ->
SRr segs W (cfg_at segs a regs memc mdc)
(tliteral_leaf_postXP Pinv STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc k regs q v ty p text txt cw).
Lemma tliteral_leafXmn_of : forall VRA a,
(forall memc0, tliteral_leafXP (fun m => YAkMemnorm.memnorm segs memc0 -> YAkMemnorm.memnorm segs m) VRA a) ->
tliteral_leafXmn VRA a.
Proof.
intros VRA a H. unfold tliteral_leafXmn.
intros STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k regs q w ty v p text len txt cw slack HJ.
exact (H memc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k regs q w ty v p text len txt cw slack HJ (fun Hm => Hm)).
Qed.
End a.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Variable psym : Type.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Variable fetch : Z -> option Z.
Variable val : nat -> Z.
Variable sigma : psym -> Z.
Variable listing : ptable psym.
Variable tpi0 : ptree psym.
Variable tw0 : ctable.
Hypothesis Hfetch : forall pc w, fetch pc = Some w -> fetch_word segs (Z_to_bv 64 pc) = Some (Z_to_bv 32 w).
Hypothesis Hcert : pi_check psym fetch val sigma listing = true.
Hypothesis HB : 0 <= val A_TEXT /\ val A_TEXT + 2 ^ 40 < 2 ^ 64 /\ val A_TEXT mod 4 = 0.
Variable A_LIM : nat.
Hypothesis HLIM0 : (A_TEXT < A_LIM)%nat.
Hypothesis HLIM : forallb (pinstr_atoms_ltb A_LIM) listing = true.
Hypothesis HLEN : 4 * Z.of_nat (length listing) <= 2 ^ 40.
Hypothesis Htpi : ptree_of_list listing = tpi0.
Hypothesis Htw : tw_of 0 listing = tw0.
Variable Pinv : (word -> option byte) -> Prop.
Hypothesis MSI : msteps_keeps segs Pinv.
Definition run_post_pi_tok_AJxP (W : world segs) (E : env) (K : nat) (Bx : sv) (SH : list shent) (ss : sstate) (st' : shst)
(r : ptrun_status psym)
(ms : machine_state) (STK sp0 : Z) (FP : list (Z * Z)) ly S Hp W0 mem md own lyc Sc Hpc (mdc : Model) (k : Z)
(Q : world segs -> config -> Prop) : Prop :=
forall ws ms' mat',
length ws = sh_j st' ->
img_env val A_LIM (extK E K ws) ->
match r with
| PTS_call s => st_ok segs (extK E K ws) (setpc (sh_ss st') (sigma s)) (restrict (w_H W) ms')
| _ => st_ok_pi segs val (extK E K ws) (sh_ss st') (restrict (w_H W) ms')
end ->
sh_ok segs Bx SH (extK E K ws) (mrestrict (w_H W) (ms_mem ms')) ->
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
Pinv (ms_mem ms') ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
Lemma SRr_chain_pi_tok_AJxP : forall W E K Bx SH ws ss (st' : shst) (r : ptrun_status psym) ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
img_env val A_LIM (extK E K ws) ->
match r with
| PTS_call s => st_ok segs (extK E K ws) (setpc (sh_ss st') (sigma s)) msr'
| _ => st_ok_pi segs val (extK E K ws) (sh_ss st') msr'
end ->
sh_ok segs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Pinv (ms_mem ms) ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_pi_tok_AJxP W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W E K Bx SH ws ss st' r ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q Hms Hlen HE' HS' Hsh' Hfr HJ HPm Hwr Hk.
apply (MSI W ms msr' mdc Q Hms HPm).
intros model' Hsame Hcl HPm'.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen HE').
- rewrite Hrr. exact HS'.
- rewrite Hmm. exact Hsh'.
- eapply (ajournal_x_exec (SK := SK) segs B PST ARx LAWS segs_low) with (Wr := in_wrange E (ss_mem ss)); [exact HJ | | | | | exact Hwr].
+ rewrite Hmm. exact Hfr.
+ rewrite Hmm. exact Hgr.
+ intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
+ rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame.
- exact HPm'.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.
Lemma SRr_run_pi_tok_AJxP : forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env val A_LIM E ->
st_ok_pi segs val E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_pi_tok tpi0 tw0 K Bx Bspan SH n ss = (st', r) ->
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Pinv (ms_mem ms) ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_pi_tok_AJxP W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ HPm Hobl Hwr Hk.
rewrite <- Htpi, <- Htw in Hrun.
destruct (sym_run_pi_tok_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN K Bx Bspan SH HK n E ss _ st' r
HE HS Hsh Hchk Hrun Hobl) as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
eapply SRr_chain_pi_tok_AJxP; [exact Hms | exact Hlen | exact HE' | | exact Hsh' | exact Hfr | exact HJ | exact HPm | exact Hwr | exact Hk].
destruct r; cbn [ptok_post] in HP; first [exact HP | destruct HP].
Qed.
Lemma SRr_chain_pi_tok_AJx_frP : forall W E K Bx SH ws ss (st' : shst) (r : ptrun_status psym) ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
img_env val A_LIM (extK E K ws) ->
match r with
| PTS_call s => st_ok segs (extK E K ws) (setpc (sh_ss st') (sigma s)) msr'
| _ => st_ok_pi segs val (extK E K ws) (sh_ss st') msr'
end ->
sh_ok segs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Pinv (ms_mem ms) ->
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
run_post_pi_tok_AJxP W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W E K Bx SH ws ss st' r ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q Hms Hlen HE' HS' Hsh' Hfr HJ HPm Hwr Hk.
apply (MSI W ms msr' mdc Q Hms HPm).
intros model' Hsame Hcl HPm'.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen HE').
- rewrite Hrr. exact HS'.
- rewrite Hmm. exact Hsh'.
- eapply (ajournal_x_exec_fr (SK := SK) segs B PST ARx LAWS segs_low) with (Wr := in_wrange E (ss_mem ss)); [exact HJ | | | | | exact Hwr].
  + rewrite Hmm. exact Hfr.
  + rewrite Hmm. exact Hgr.
  + intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
  + rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame.
- exact HPm'.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.
Lemma SRr_run_pi_tok_AJx_frP : forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env val A_LIM E ->
st_ok_pi segs val E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_pi_tok tpi0 tw0 K Bx Bspan SH n ss = (st', r) ->
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Pinv (ms_mem ms) ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
run_post_pi_tok_AJxP W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ HPm Hobl Hwr Hk.
rewrite <- Htpi, <- Htw in Hrun.
destruct (sym_run_pi_tok_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN K Bx Bspan SH HK n E ss _ st' r
HE HS Hsh Hchk Hrun Hobl) as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
eapply SRr_chain_pi_tok_AJx_frP; [exact Hms | exact Hlen | exact HE' | | exact Hsh' | exact Hfr | exact HJ | exact HPm | exact Hwr | exact Hk].
destruct r; cbn [ptok_post] in HP; first [exact HP | destruct HP].
Qed.
End e.
Section g.
Context {L : ptable asym} {PL : PAListing L} {PI : PAImg L}.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world pa_segs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x pa_segs B ARx HL.
Variable Pinv : (word -> option byte) -> Prop.
Hypothesis MSI : msteps_keeps pa_segs Pinv.
Definition paj_run_xP := SRr_run_pi_tok_AJxP asym pa_segs B PST ARx LAWS pa_segs_low (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq Pinv MSI.
Definition paj_run_x_frP := SRr_run_pi_tok_AJx_frP asym pa_segs B PST ARx LAWS pa_segs_low (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq Pinv MSI.
End g.
End d.
Ltac paj_after_run_tokP HS HJ SHOK HPM :=
let ws := fresh "ws" in let ms' := fresh "ms" in let mat' := fresh "mat" in
let Hlen := fresh "Hlen" in let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in let HEI := fresh "HEI" in
intros ws ms' mat' Hlen HEI HS SHOK HJ HPM HF HFr HG;
cbn [sh_j sh_ss] in Hlen, HS, SHOK;
repeat (let w := fresh "w" in
destruct ws as [|w ws]; [discriminate Hlen | cbn [length] in Hlen; apply eq_add_S in Hlen || injection Hlen as Hlen]);
(destruct ws; [clear Hlen | discriminate Hlen]);
cbn [extK length Nat.add] in HS, SHOK, HEI;
cbn [ms_mem mkst] in HF, HFr, HG, HJ, HPM;
try match type of HS with context [restrict _ ?msn] =>
repeat match goal with
| old : machine_state |- _ => lazymatch old with msn => fail | _ => clear old end
end
end;
srr_norm_model.
Ltac paj_run_tok_xP RUN HS HJ SHOK HPM Bspan :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
lazymatch paj_tables RUN with (?tpi, ?tw) =>
let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
let r := eval vm_compute in (sym_runN_pi_tok tpi tw K Bx Bspan SH FUEL ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_pi_tok tpi tw K Bx Bspan SH FUEL ss = (st', rs)) by (vm_compute; reflexivity);
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "paj_run_tok_xP: no hypothesis  img_env _ _ E" end in
eapply (RUN W FUEL E K Bx Bspan SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(unfold A_LIM; cbn; lia) HEI HS SHOK
ltac:(vm_compute; reflexivity) Hrun HJ HPM);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK HPM; try match type of ms with machine_state => clear ms | _ => idtac end;
paj_after_run_tokP HS HJ SHOK HPM ]
end end
end
| _ => fail "paj_run_tok_xP: HS must be  st_ok_pi segs val E ss (restrict (w_H W) ms)"
end.
