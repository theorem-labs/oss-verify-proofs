(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgRt.v at 6ebe35ba632; its rt_chain is ported here as rl_c23_chain (statement kept, proof by the kernel's achain_push); the rest of this file is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPostMal.v at 01f4363fe7d; ported to reac-pw/fuzz_headamp image A: role's C2 -> C3 step (malloc(pod), rh_S_C23_stmt) restated as headamp's C6 -> C7 step (malloc(first), lib/A/HPgSegM.v hq_S_C67_stmt) with the prefix rl_c23 / c23 -> hk, the jal 0x820c0 -> 0x83740, malloc's entry 0x52428 -> 0x53060, role's frame 0x1a0 -> headamp's 0x1e0, k = 1 -> 3 events, role's request len -> 3 max(rc, 0) + (it == 0); the call runs at the float state fx2 the cut states (AMALLOC quantified over the float state); the post is HPgSegM's whole hq_cut_C7 (role's rh_at_C3 asked the call's post only), built from the rule's post with the allocator invariant at the new state, acall_kept and image A's cut lists; the errno cell's readability is new (every byte of image A's four segments has an image byte). *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): THE malloc(first) STEP of the
   walk of LLVMFuzzerTestOneInput, C6 = 0x83740 -> C7 = 0x83744, i.e. lib/A/HPgSegM.v hq_S_C67_stmt at the concrete
   segments lib/A/Img0.v rsegs. Proves no function (kind: segment lemma).

   THE CODE. At C6 a0 = 3 max(rc, 0) + (3 max(rc, 0) == 0) (HPgImgA hi_L6: (LReg 10, XRc3NZ)), which is in
   [1, 27] (HPgSiteA headamp_A_site_malloc_first with -1 <= rc <= cap <= 9). 0x83740 is `jal 0x53060`: ra := 0x83744,
   pc := 0x53060, the runtime's malloc entry of image A (pc_wrap_malloc, the 4-byte jump to the wrapper). C7 = 0x83744
   is the return address.

   THE ROUTE.
   1. The engine runs the one `jal` from an entry state with every register an atom (hk_entry, the one-word table
      hk_tbl at 0x83740); it stops at 0x53060 with ra the literal 0x83744, every other register its own atom and no
      byte written.
   2. The kernel's journal malloc rule YCbq.aj_malloc_at04 at the harness journal hq_j (STK = LLVMF_STK, sp0 = S,
      FP = [], own = [(4, pos)], k = 3), with o = R - S (R = e_R e the 32-aligned real-frame base, S 16-aligned, so
      o is 16-aligned and -0x1f0 <= o <= -0x1e0), the event and live-byte budgets from hq_base, and the caller chain
      from the harness entry: the entry's achain (afn_pre, ch = []) pushed with the frame record the prologue stored
      at S - 8 (ra) and S - 16 (s0), which hq_kept carries (hk_chain), s0 = S at C6 (hi_L6: (LReg 8, XS)).
   3. The rule's post gives hq_at_C7: the journal at four events, a0 = first >= 4096, the callee-saved registers of
      C6 kept, frames kept, the block appended, acall_kept at [R - ASTACK, R); and hq_cut_C7 at the env with the new
      block (hq_env_first): the block list (first fresh: two copies of it in the allocator's list would overlap,
      YCbq.sep_blocks_pos), sp / gp / tp, hi_L7 (HPgSiteA headamp_A_site_cut7 over hi_L6 kept by acall_kept), the
      frame's shadow and flag cell (acall_kept's frame clause; first lies apart from the frame and its shadow), the
      thirteen saves and the three float saves (above R: acall_kept's stack clause), the pp / pod / out bytes
      (acall_kept's block clause: each block apart from first), the shadow of pod, out and first (HPgMem.hm_blk_ra
      at the new state) and the errno cell readable (hk_errno_rd: errno lies in the image, api_env, and every byte
      of image A's four segments has an image byte, hk_segs_ok).

   SECTION HYPOTHESES (each is what the harness level supplies):
     AMALLOC     forall fx', amalloc_realizes rsegs B   the runtime's malloc against the model, at every float
                                                         state (the call runs at the state C6 states, fx2)
     errno_low   api_env rsegs B                        errno cell and the allocator's one-entry traces
     ML          model_laws (as_universe B)             the allocator model's laws
     HPCM        pc_wrap_malloc (as_code B) = 0x53060   the code record: malloc's entry is the jal's target
     HSTK_C67    ASTACK + HQ_RSZ + 16 <= LLVMF_STK      the call's stack budget: ASTACK - o <= LLVMF_STK
     HEV_C67     4 <= EV_LIB                            room for this event (the fourth): st_nev < EV_MAX
     HLIVE_C67   Layout.PP_SIZE + 5440 + 30 + 27 <= LIVE_LIB  room for first after pp, pod, out:
                                                         blocks_bytes + 3 max(rc, 0) + (it == 0) <= LIVE_MAX
     HTRACE_C67  the malloc trace at ra = 0x83744 is in the universe (scene's rt_trace_in_stmt, one site).
   AXIOMS (Print Assumptions below): the primitive int / string / array axioms and Stdlib's
   functional_extensionality_dep. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YK07.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YO0f YG0s YG0q YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Model Layout Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgMem HPgSteps HPgSiteA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the one instruction word the engine runs: the `jal` at C6 ---- *)
Definition HK_PC : Z := 0x83740.
Definition hk_tbl : ctable := build_table rsegs HK_PC 1 TEmpty.
Lemma hk_tbl_ok : table_ok rsegs hk_tbl.
Proof. apply build_table_ok0. unfold HK_PC. lia. Qed.

(* the entry state at C6: the registers as atoms, no region, no fact (at any float state) *)
Definition hk_ss : sstate := mkSS HK_PC sr_atoms [] None (mkFacts [] [] []).
Lemma hk_entry : forall (fx' : YK11.FPState) (W : world rsegs) regs memc,
@st_ok rsegs fx' (Ereg regs rt_extra) hk_ss
  (restrict (w_H W) (@mkst fx' regs (Z_to_bv 64 HK_PC) memc (seg_rom rsegs))).
Proof.
intros fx' W regs memc. rewrite restrict_mkst_fx. unfold hk_ss. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I.
Qed.

(* ---- every byte of image A's four segments has an image byte (each segment is one hex chunk of its size) ---- *)
Definition hk_seg_ok (sg : Segment) : bool :=
  seg_readable sg &&
  match seg_bytes sg with
  | [s] => N.leb (seg_size sg) (Z.to_N (Uint63.to_Z (PrimString.length s) / 2)) && scanN s 64 0 (seg_size sg)
  | _ => false
  end.
Lemma hk_segs_ok : forallb hk_seg_ok rsegs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma hk_find_some : forall (l : list Segment) a,
(exists sg, In sg l /\ Z.of_N (seg_base sg) <= a < Z.of_N (seg_base sg) + Z.of_N (seg_size sg)) ->
exists sg, find_segment l a 1 = Some sg.
Proof.
induction l as [|s0 l IH]; intros a (sg & Hin & Hr); [destruct Hin|].
cbn [find_segment]. cbv zeta.
match goal with |- context [if ?c then _ else _] => destruct c eqn:Eb end.
- exists s0. reflexivity.
- destruct Hin as [<-|Hin].
  + exfalso. apply andb_false_iff in Eb as [Eb|Eb]; apply Z.leb_gt in Eb; lia.
  + exact (IH a (ex_intro _ sg (conj Hin Hr))).
Qed.
Lemma hk_seg_rom_img : forall a, 0 <= a < 2 ^ 64 -> in_img rsegs a -> seg_rom rsegs (Z_to_bv 64 a) <> None.
Proof.
intros a Ha Himg. destruct (hk_find_some rsegs a Himg) as (sg & Hf).
pose proof Hf as Hf'. apply find_segment_some_spec in Hf' as (Hin & H1 & H2).
pose proof (proj1 (forallb_forall _ _) hk_segs_ok sg Hin) as Hok. unfold hk_seg_ok in Hok.
apply andb_prop in Hok as [Hr Hb].
unfold seg_rom, memory_read. rewrite unsigned_lit_small by exact Ha.
change (Z.of_N 1) with 1. rewrite Hf, Hr. cbv beta iota zeta.
destruct (seg_bytes sg) as [|s [|s' rest]] eqn:Eb; try discriminate Hb.
apply andb_prop in Hb as [Hle Hscan]. apply N.leb_le in Hle.
change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
destruct (segment_byte_at [s] (Z.to_N (a - Z.of_N (seg_base sg)))) as [b|] eqn:Es.
- cbn. discriminate.
- exfalso. apply (segment_byte_at_some1 s (seg_size sg) (Z.to_N (a - Z.of_N (seg_base sg))) Hscan Hle); [|exact Es].
  rewrite Z2N.id by lia. lia.
Qed.
Lemma hk_aview_some : forall H (mem : word -> option byte) a, 0 <= a < 2 ^ 64 -> in_img rsegs a ->
exists v, aview rsegs H mem a = Some v /\ 0 <= v < 256.
Proof.
intros H mem a Ha Himg. unfold aview, mbyte.
destruct (mrestrict H mem (Z_to_bv 64 a)) as [b|] eqn:E.
- exists (bv_unsigned b). split; [reflexivity|]. pose proof (bv_unsigned_in_range 8 b) as Hb.
  change (bv_modulus 8) with 256 in Hb. exact Hb.
- destruct (seg_rom rsegs (Z_to_bv 64 a)) as [b|] eqn:E2.
  + exists (bv_unsigned b). split; [reflexivity|]. pose proof (bv_unsigned_in_range 8 b) as Hb.
    change (bv_modulus 8) with 256 in Hb. exact Hb.
  + exfalso. exact (hk_seg_rom_img a Ha Himg E2).
Qed.
(* four bytes as one little-endian 4-byte value *)
Lemma hk_le4 : forall v0 v1 v2 v3, 0 <= v0 < 256 -> 0 <= v1 < 256 -> 0 <= v2 < 256 -> 0 <= v3 < 256 ->
YG0f.le_byte (v0 + 256 * v1 + 65536 * v2 + 16777216 * v3) 4 0 = v0 /\
YG0f.le_byte (v0 + 256 * v1 + 65536 * v2 + 16777216 * v3) 4 1 = v1 /\
YG0f.le_byte (v0 + 256 * v1 + 65536 * v2 + 16777216 * v3) 4 2 = v2 /\
YG0f.le_byte (v0 + 256 * v1 + 65536 * v2 + 16777216 * v3) 4 3 = v3.
Proof.
intros v0 v1 v2 v3 H0 H1 H2 H3. unfold YG0f.le_byte. rewrite !Z.shiftr_div_pow2 by lia.
change (2 ^ (8 * Z.of_nat 4)) with 4294967296. change (2 ^ (8 * Z.of_nat 0)) with 1.
change (2 ^ (8 * Z.of_nat 1)) with 256. change (2 ^ (8 * Z.of_nat 2)) with 65536.
change (2 ^ (8 * Z.of_nat 3)) with 16777216.
split; [|split; [|split]]; Z.to_euclidean_division_equations; lia.
Qed.
(* the errno cell is readable at every memory: its four bytes lie in the image (api_env) *)
Lemma hk_errno_rd : forall (B : asyms) H (mem : word -> option byte), api_env rsegs B ->
exists ev, rd32 (aview rsegs H mem) (as_errno B) ev.
Proof.
intros B H mem (He & Hi & _).
assert (G : forall k, 0 <= k < 4 -> exists v, aview rsegs H mem (as_errno B + k) = Some v /\ 0 <= v < 256).
{ intros k Hk. apply hk_aview_some; [unfold kLowMemEnd in He; lia | apply Hi; lia]. }
destruct (G 0 ltac:(lia)) as (v0 & A0 & B0). destruct (G 1 ltac:(lia)) as (v1 & A1 & B1).
destruct (G 2 ltac:(lia)) as (v2 & A2 & B2). destruct (G 3 ltac:(lia)) as (v3 & A3 & B3).
destruct (hk_le4 v0 v1 v2 v3 B0 B1 B2 B3) as (L0 & L1 & L2 & L3).
exists (v0 + 256 * v1 + 65536 * v2 + 16777216 * v3).
unfold rd32. intros k Hk.
destruct k as [|[|[|[|k]]]]; [| | | | lia].
- change (Z.of_nat 0) with 0. rewrite A0, L0. reflexivity.
- change (Z.of_nat 1) with 1. rewrite A1, L1. reflexivity.
- change (Z.of_nat 2) with 2. rewrite A2, L2. reflexivity.
- change (Z.of_nat 3) with 3. rewrite A3, L3. reflexivity.
Qed.

(* ---- an 8-byte cell as a word of the view (the converse of YCbq.val_mem_of_rdword) ---- *)
Section h. Context {rc : YM05.RunCeil}.
(* the frame's shadow bytes lie apart from every application range (a heap block) *)
Lemma hk_shadow_apart : forall F p n i, in_app F 1024 -> in_app p n -> alloc_ceiling <= 0x7fffff800000 ->
0 <= i < 128 -> ~ (p <= shadow_addr F + i < p + n).
Proof.
intros F p n i HF Hp Hc Hi. unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in HF, Hp.
unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)).
lia.
Qed.
Lemma hk_rdword_of_val_mem : forall H mem a v, 0 <= v < 2 ^ 64 ->
val_mem rsegs (mrestrict H mem) a 8 v -> rdword (aview rsegs H mem) a = Some v.
Proof.
intros H mem a v Hv Hm. unfold val_mem in Hm.
pose proof (Hm 0%nat ltac:(lia)) as H0. pose proof (Hm 1%nat ltac:(lia)) as H1. pose proof (Hm 2%nat ltac:(lia)) as H2.
pose proof (Hm 3%nat ltac:(lia)) as H3. pose proof (Hm 4%nat ltac:(lia)) as H4. pose proof (Hm 5%nat ltac:(lia)) as H5.
pose proof (Hm 6%nat ltac:(lia)) as H6. pose proof (Hm 7%nat ltac:(lia)) as H7.
cbv [Z.of_nat Pos.of_succ_nat Pos.succ] in H0, H1, H2, H3, H4, H5, H6, H7. rewrite Z.add_0_r in H0.
unfold rdword, aview. cbv beta.
rewrite H0, H1, H2, H3, H4, H5, H6, H7. cbn [option_map].
assert (Hb : forall k, bv_unsigned (Z_to_bv 8 (YO0f.le_byte v 8 k)) = YG0f.le_byte v 8 k).
{ intros k. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  change (YO0f.le_byte v 8 k) with (YG0f.le_byte v 8 k). rewrite YG0s.le_byte_8. apply Z.mod_mod. lia. }
rewrite !Hb. f_equal. apply YG0s.le_bytes8. exact Hv.
Qed.
(* a cell fact of HPgBase as a word of the view *)
Lemma hk_cell : forall H mem regs e b o v, 0 <= v < 2 ^ 64 ->
hd_at rsegs H mem regs e (LCell b o) v -> rdword (aview rsegs H mem) (hd_xv e b + o) = Some v.
Proof.
intros H mem regs e b o v Hv Hc. cbn [hd_at] in Hc. rewrite Z.mod_small in Hc by exact Hv.
apply hk_rdword_of_val_mem; assumption.
Qed.

(* ---- register names: a literal and Z_to_bv 5 of its number name the same register ---- *)
Lemma hk_getr_eq : forall regs (b b' : bv 5), bv_unsigned b = bv_unsigned b' -> getr regs b = getr regs b'.
Proof. intros regs b b' E. apply bv_eq in E. subst b'. reflexivity. Qed.
Lemma hk_csaved : forall r, acallee_saved r -> bv_unsigned (Z_to_bv 5 r) = r.
Proof.
intros r Hr. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
apply Z.mod_small. unfold acallee_saved in Hr. lia.
Qed.

(* ---- the caller chain at a call from the harness frame [knock APgRt.v rt_chain] ---- *)
Lemma hk_chain : forall ly (rd rd' : reader) (regs : bvmap 5 word) sp',
achain ly rd (spZ regs) (s0Z regs) [] -> ly_top ly <= 2 ^ 64 ->
(forall a, spZ regs <= a < 2 ^ 64 -> rd' a = rd a) ->
rdword rd' (spZ regs - 8) = Some (raZ regs) -> rdword rd' (spZ regs - 16) = Some (s0Z regs) -> 4096 <= raZ regs ->
alloc_ceiling <= spZ regs -> spZ regs mod 8 = 0 -> sp' + 16 <= spZ regs ->
achain ly rd' sp' (spZ regs) (if spZ regs + 16 <? ly_top ly then [(spZ regs, raZ regs, s0Z regs)] else []).
Proof.
intros ly rd rd' regs sp' Hch Htop64 Hk H8 H16 Hra Hceil Hal Hsp'.
destruct (Z.ltb_spec (spZ regs + 16) (ly_top ly)) as [Hlt | Hge].
- exact (achain_push ly rd rd' (spZ regs) (s0Z regs) (raZ regs) [] sp' Hch Htop64 Hk H8 H16 Hra Hceil Hal ltac:(lia) Hsp').
- left. split; [right; left; lia | reflexivity].
Qed.
End h.

(* the side goals of a register the run did not touch (clob = [ra]) *)
Ltac hk_rk :=
first
[ solve [vm_compute; let Hx := fresh "Hx" in intros Hx; discriminate Hx]
| solve [let Hx := fresh "Hx" in intros Hx; cbn [In] in Hx;
         repeat (destruct Hx as [Hx|Hx]; [apply (f_equal (@bv_unsigned 5)) in Hx; vm_compute in Hx; discriminate Hx|]);
         exact Hx] ].

Section b. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* the caller chain the malloc call sees: the harness entry's own record (sp, ra, s0) when its frame is below the
   stack top (scene P_LLVMFuzzerTestOneInput_ctx.v rt_ch) *)
Definition hk_ch (hx : hq_hcx rsegs) : list (Z * Z * Z) :=
if spZ (h_regs rsegs hx) + 16 <? ly_top (h_ly rsegs hx)
then [(spZ (h_regs rsegs hx), raZ (h_regs rsegs hx), s0Z (h_regs rsegs hx))] else [].
Section d.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
Hypothesis AMALLOC : forall fx' : YK11.FPState, amalloc_realizes (fx := fx') rsegs B.
Hypothesis errno_low : api_env rsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis HPCM : pc_wrap_malloc (as_code B) = 0x53060.
Hypothesis HSTK_C67 : ASTACK + HQ_RSZ + 16 <= LLVMF_STK.
Hypothesis HEV_C67 : 4 <= EV_LIB.
Hypothesis HLIVE_C67 : Layout.PP_SIZE + 5440 + 30 + 27 <= LIVE_LIB.
Hypothesis HTRACE_C67 : forall (regsT : bvmap 5 word) (hx : hq_hcx rsegs),
raZ (h_regs rsegs hx) = RA_LLVMF -> raZ regsT = HQ_C7 ->
In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT (hk_ch hx)) (as_universe B).

Theorem hq_A_S_C67 : hq_S_C67_stmt rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof using AMALLOC errno_low ML HPCM HSTK_C67 HEV_C67 HLIVE_C67 HTRACE_C67.
unfold hq_S_C67_stmt. intros hx fx2 pos e r ly6 S6 W6 regs6 mem6 md6 HB HC.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
destruct HB as (HPRE & Hra0 & _ & _ & _ & _ & _ & Hfr0 & Hev0 & Hlive0 & _).
destruct HPRE as (HAR0 & Hraok0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
destruct Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HC as (HAC & Hfrm & Hrec & Hrapod & Hraout & Hcells & Herr).
destruct HAC as (HJ6 & Hperm6 & Hfresh6 & Hsp6 & Hgp6 & Htp6 & Hgeo & HL6 & Hfsh6 & Hkept6).
pose proof Hgeo as (HeS & HeR & HeF).
destruct Hrec as (Hwf & Hlen & Hlenb & Hpp & Hpod & Hpod16 & Hhull & Hamem & Hcap & Hnull & Hrc).
unfold hq_j in HJ6.
pose proof HJ6 as (HAR6 & Hly6 & _ & _ & _ & Hfrs6 & Hnev & _ & F1 & _).
pose proof Hly6 as (_ & _ & _ & _ & _ & EF6 & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _ & _ & _ & _).
pose proof HSTK_C67 as HSTK. unfold ASTACK, HQ_RSZ in HSTK.
(* the geometry: S = 16 t, R = 32 q with S - 0x1e0 = 32 q + r, 0 <= r < 32, so S - R is 0x1e0 or 0x1f0 *)
rewrite HeS in HeR. unfold HQ_RSZ in HeR.
pose proof (Z.div_mod (spZ (h_regs rsegs hx) - 0x1e0) 32 ltac:(lia)) as Dq.
pose proof (Z.mod_pos_bound (spZ (h_regs rsegs hx) - 0x1e0) 32 ltac:(lia)) as Bq.
pose proof (Z.div_mod (spZ (h_regs rsegs hx)) 16 ltac:(lia)) as D16. rewrite Hal16, Z.add_0_r in D16.
assert (HRb : alloc_ceiling + 16384 <= e_R e /\ e_R e + 0x1e0 <= spZ (h_regs rsegs hx) /\
  spZ (h_regs rsegs hx) - e_R e <= 0x1f0) by lia.
assert (HR64 : 0 <= e_R e < 2 ^ 64) by lia.
assert (HS64 : 0 <= spZ (h_regs rsegs hx) < 2 ^ 64) by lia.
assert (HAL : (e_R e - spZ (h_regs rsegs hx)) mod 16 = 0).
{ replace (e_R e - spZ (h_regs rsegs hx))
    with ((2 * ((spZ (h_regs rsegs hx) - 0x1e0) / 32) - spZ (h_regs rsegs hx) / 16) * 16) by lia.
  apply Z.mod_mul. lia. }
assert (HS8 : spZ (h_regs rsegs hx) mod 8 = 0).
{ replace (spZ (h_regs rsegs hx)) with ((2 * (spZ (h_regs rsegs hx) / 16)) * 8) by lia. apply Z.mod_mul. lia. }
(* the C6 values a0 = the request and s0 = S *)
pose proof HL6 as HL6c. unfold hd_cut in HL6c. cbn [hi_L6 headamp_himg_A] in HL6c. unfold headamp_A_L67 in HL6c.
apply Forall_cons_iff in HL6c as [C10 HL6c]. apply Forall_cons_iff in HL6c as [C8 _].
cbn [fst snd hd_at] in C10, C8. cbn [hd_xv] in C8. rewrite HeS in C8.
(* the parse's answer: -1 <= rc <= cap and at most cap cells, so the request is in [1, 27] *)
pose proof (Headamp.parse_props_total (hd_props (e_null e) (Model.buf r)) (e_cap e) ltac:(lia)) as Hok.
apply answer_ok_parts in Hok as (Hcase & _).
assert (Hrcb : -1 <= e_rc e <= e_cap e) by (rewrite Hrc; destruct Hcase as [(H1 & _)|(H1 & _)]; lia).
assert (Hncl : Z.of_nat (length (ans_cells (Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e))))
  <= e_cap e) by (destruct Hcase as [(_ & Hc0 & _)|(Hr0 & Hl0 & _)]; [rewrite Hc0; cbn [length]; lia | lia]).
clear Hcase.
destruct (headamp_A_site_malloc_first e Hrcb Hcap) as (Hn & HN).
assert (Hrq : req_size (hd_xv e XRc3NZ) = hd_xv e XRc3NZ)
  by (unfold req_size; destruct (Z.eqb_spec (hd_xv e XRc3NZ) 0); lia).
(* the frame record the prologue stored: ra at S - 8, s0 at S - 16 *)
destruct Hkept6 as (Hcl6 & Hfs6).
pose proof Hcl6 as Hcl6c.
unfold hq_cells, hq_saves_L in Hcl6c. cbn [seq map app] in Hcl6c.
apply Forall_cons_iff in Hcl6c as [K0 Hcl6c]. apply Forall_cons_iff in Hcl6c as [K1 _].
cbv beta in K0, K1. cbn [fst snd] in K0, K1.
pose proof (hk_cell _ _ _ _ _ _ _ (u64_range _) K0) as W8.
pose proof (hk_cell _ _ _ _ _ _ _ (u64_range _) K1) as W16.
cbn [hd_xv] in W8, W16. rewrite HeS in W8, W16.
assert (R8 : rdword (aview rsegs (w_H W6) mem6) (spZ (h_regs rsegs hx) - 8) = Some (raZ (h_regs rsegs hx))).
{ replace (spZ (h_regs rsegs hx) - 8) with (spZ (h_regs rsegs hx) + (-8 - 8 * Z.of_nat 0)) by lia. exact W8. }
assert (R16 : rdword (aview rsegs (w_H W6) mem6) (spZ (h_regs rsegs hx) - 16) = Some (s0Z (h_regs rsegs hx))).
{ replace (spZ (h_regs rsegs hx) - 16) with (spZ (h_regs rsegs hx) + (-8 - 8 * Z.of_nat 1)) by lia. exact W16. }
clear W8 W16 K0 K1.
(* 1. the `jal`: one engine step to 0x53060 *)
pose proof (hk_entry fx2 W6 regs6 mem6) as HS.
assert (SHOK : sh_ok rsegs RTBx [] (Ereg regs6 rt_extra) (mrestrict (w_H W6) mem6)) by constructor.
assert (HAE : env_agree 32 (Ereg regs6 rt_extra) (Ereg regs6 rt_extra)) by apply env_agree_refl.
unfold cfg_at. change (w64 HQ_C6) with (Z_to_bv 64 HK_PC).
aj_run_tok hk_tbl_ok HS HJ6 SHOK RTBspan; [awr_ok_tac |].
(* no byte written; every register but ra its own atom; ra the literal 0x83744 *)
assert (Hm : ms_mem ms = mem6).
{ apply functional_extensionality. intros x. apply HF. intros (rg & Hrg & _). exact Hrg. }
assert (RK : forall rr : bv 5, bv_unsigned rr <> 0 -> ~ In rr [Z_to_bv 5 1] -> getr (ms_regs ms) rr = getr regs6 rr).
{ eapply (regs_kept_of_st_ok rsegs _ _ ms regs6 rt_extra (w_H W6) _ HS HAE). vm_compute. reflexivity. }
assert (HRA : getr (ms_regs ms) 1 = Z_to_bv 64 0x83744).
{ rewrite (hk_getr_eq (ms_regs ms) 1 (Z_to_bv 5 1)) by reflexivity.
  rewrite (st_ok_restrict_reg rsegs (w_H W6) _ _ ms (Z_to_bv 5 1) HS).
  lazymatch type of HS with st_ok _ _ ?ss _ =>
    replace (sr_get (ss_regs ss) (Z_to_bv 5 1)) with (SLit 0x83744) by (vm_compute; reflexivity) end.
  reflexivity. }
(* 2. the call's premises *)
assert (HA10 : getr (ms_regs ms) 10 = w64 (hd_xv e XRc3NZ)).
{ rewrite RK by hk_rk. rewrite (hk_getr_eq regs6 10 (Z_to_bv 5 10)) by reflexivity. exact C10. }
assert (HLV : blocks_bytes S6 + hd_xv e XRc3NZ <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly6 S6), (bsum_perm _ _ Hperm6), bsum_app,
    <- (blocks_bytes_bsum B (h_ly rsegs hx) (h_S rsegs hx)).
  unfold hq_blocks5, bsum. cbn [fold_right snd]. change Layout.PP_SIZE with 19744 in *. lia. }
assert (HSP : spZ (ms_regs ms) = spZ (h_regs rsegs hx) + (e_R e - spZ (h_regs rsegs hx))).
{ unfold spZ at 1. rewrite RK by hk_rk. rewrite Hsp6. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (HNEG : e_R e - spZ (h_regs rsegs hx) <= 0) by lia.
assert (HBUD : ASTACK - (e_R e - spZ (h_regs rsegs hx)) <= LLVMF_STK) by (unfold ASTACK; lia).
assert (HGP : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite RK by hk_rk; exact Hgp6).
assert (HTP : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite RK by hk_rk; exact Htp6).
assert (HRAOK : YK0s.ret_ok (Z_to_bv 64 0x83744)) by (unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity).
assert (HEV : st_nev S6 < EV_MAX) by lia.
assert (HRAZ : raZ (ms_regs ms) = 0x83744) by (unfold raZ; rewrite HRA; apply unsigned_lit_small; lia).
assert (HCH : chain_pre ly6 (aview rsegs (w_H W6) mem6) (ms_regs ms) (hk_ch hx)).
{ apply (achain_chain_pre ly6 _ (e_R e) (spZ (h_regs rsegs hx))).
  - apply (achain_ly_top (h_ly rsegs hx) ly6 _ _ _ _ Etop). unfold hk_ch.
    apply (hk_chain (h_ly rsegs hx) (aview rsegs (w_H (h_W rsegs hx)) (h_mem rsegs hx))).
    + exact Hch0.
    + lia.
    + intros a Ha. apply F1; lia.
    + exact R8.
    + exact R16.
    + exact Hra40.
    + lia.
    + exact HS8.
    + lia.
  - rewrite HSP. lia.
  - unfold s0Z. rewrite RK by hk_rk. rewrite (hk_getr_eq regs6 8 (Z_to_bv 5 8)) by reflexivity.
    rewrite C8. unfold w64. apply unsigned_lit_small. lia.
  - rewrite HRAZ. lia. }
assert (HTR : In (call_trace0 (pc_malloc_ra0 (as_code B)) (ms_regs ms) (hk_ch hx)) (as_universe B)).
{ apply HTRACE_C67; [exact Hra0 | rewrite HRAZ; reflexivity]. }
(* the machine state at 0x53060 = pc_wrap_malloc *)
rewrite (st_ok_restrict_mkst rsegs (w_H W6) _ _ ms HS eq_refl).
lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?s)] =>
  replace (ss_pc s) with (pc_wrap_malloc (as_code B)) by (rewrite HPCM; vm_compute; reflexivity) end.
rewrite Hm. rewrite Hm in HJ6.
eapply SRr_mono.
{ exact (aj_malloc_at04 rsegs B LAWS Hsegs errno_low ML (AMALLOC fx2) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    HJ6 HA10 HN HLV HSP HAL HNEG HBUD HGP HTP HRA HRAOK HEV HCH HTR). }
(* 3. the post at C7 *)
cbv beta. intros W7 c7 _ (ly7 & S7 & regs7 & mem7 & md7 & first & Ec7 & HJ7 & Hpres7 & H107 & Hfr7 & Hfirst & Hab7 & Hkept7).
replace (spZ (h_regs rsegs hx) + (e_R e - spZ (h_regs rsegs hx))) with (e_R e) in Hkept7 by lia.
pose proof Hkept7 as (KK1 & KK2 & _ & KK4 & _ & _).
pose proof HJ7 as (HAR7 & Hly7 & _).
pose proof Hly7 as (_ & _ & _ & _ & _ & EF7 & _).
(* the callee-saved registers of C6 *)
assert (KR : forall rr, acallee_saved rr -> getr regs7 (Z_to_bv 5 rr) = getr regs6 (Z_to_bv 5 rr)).
{ intros rr Hr. rewrite (Hpres7 rr Hr). apply RK.
  - rewrite (hk_csaved rr Hr). unfold acallee_saved in Hr. lia.
  - intros [Hx|[]]. apply (f_equal (@bv_unsigned 5)) in Hx. rewrite (hk_csaved rr Hr) in Hx.
    change (bv_unsigned (Z_to_bv 5 1)) with 1 in Hx. unfold acallee_saved in Hr. lia. }
(* the blocks: pp, pod, out live at C6, first appended, each apart from first *)
assert (Hin6 : forall b, In b (hq_blocks5 e) -> In b (ablocks B ly6 S6)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym Hperm6)). apply in_or_app. right. exact Hb. }
assert (Hin7 : forall b, In b (ablocks B ly6 S6) -> In b (ablocks B ly7 S7)).
{ intros b Hb. rewrite Hab7. apply in_or_app. left. exact Hb. }
assert (Hpp6 : In (e_pp e, Layout.PP_SIZE) (ablocks B ly6 S6)) by (apply Hin6; cbn; left; reflexivity).
assert (Hpod6 : In (e_pod e, e_len e) (ablocks B ly6 S6)) by (apply Hin6; cbn; right; left; reflexivity).
assert (Hout6 : In (e_out e, 3 * (e_cap e + 1)) (ablocks B ly6 S6)) by (apply Hin6; cbn; right; right; left; reflexivity).
assert (Hfirst7 : In (first, hd_xv e XRc3NZ) (ablocks B ly7 S7))
  by (rewrite Hab7; apply in_or_app; right; left; reflexivity).
assert (Hapart : forall p m, In (p, m) (ablocks B ly6 S6) ->
  p + req_size m <= first \/ first + req_size (hd_xv e XRc3NZ) <= p).
{ intros p m Hb. apply in_split in Hb as (l1 & l2 & El).
  pose proof (sep_blocks_pos rsegs B LAWS ly7 S7 W7 mem7 md7 (p, m) (first, hd_xv e XRc3NZ) l1 l2 [] HAR7
    ltac:(rewrite Hab7, El, <- app_assoc; reflexivity)) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia. }
assert (Hfresh : ~ In (first, hd_xv e XRc3NZ) (ablocks B (h_ly rsegs hx) (h_S rsegs hx))).
{ intros Hx. assert (Hx6 : In (first, hd_xv e XRc3NZ) (ablocks B ly6 S6))
    by (apply (Permutation_in _ (Permutation_sym Hperm6)); apply in_or_app; left; exact Hx).
  pose proof (Hapart _ _ Hx6) as Hd. rewrite Hrq in Hd. lia. }
(* the frame for locals: at F in both layouts, apart from first and from first's range in the shadow *)
assert (HinF6 : In (HQ_CID, pos) (frames S6)) by (rewrite Hfrs6; left; reflexivity).
assert (HinF7 : In (HQ_CID, pos) (frames S7)) by (rewrite Hfr7; exact HinF6).
assert (FA6 : frame_addr ly6 HQ_CID pos = e_F e) by (rewrite HeF; unfold frame_addr; rewrite EF6; reflexivity).
assert (FA7 : frame_addr ly7 HQ_CID pos = e_F e) by (rewrite HeF; unfold frame_addr; rewrite EF7; reflexivity).
assert (Hfb : fs_frame_bytes HQ_CID = 1024) by reflexivity.
pose proof (sep_block_frame rsegs B LAWS ly7 S7 W7 mem7 md7 first (hd_xv e XRc3NZ) HQ_CID pos HAR7 Hfirst7 HinF7)
  as HdF.
rewrite FA7, Hfb in HdF. unfold zdisjoint in HdF. cbn [fst snd] in HdF.
destruct (al_frames _ _ LAWS ly6 S6 W6 mem6 md6 HQ_CID pos HAR6 HinF6) as (HF32 & HFapp & _).
rewrite FA6, Hfb in HFapp.
destruct (al_blocks _ _ LAWS ly7 S7 W7 mem7 md7 first (hd_xv e XRc3NZ) HAR7 Hfirst7) as (_ & _ & _ & Hfapp & _).
assert (HshF : forall i, 0 <= i < 128 ->
  ~ (first <= shadow_addr (e_F e) + i < first + req_size (hd_xv e XRc3NZ))).
{ intros i Hi. pose proof C1 as [_ C1h]. exact (hk_shadow_apart _ _ _ _ HFapp Hfapp C1h Hi). }
(* the four blocks' bytes: kept by the call when they lie apart from first *)
assert (Hkb : forall p m i, In (p, m) (ablocks B ly6 S6) -> 0 <= i < req_size m ->
  aview rsegs (w_H W7) mem7 (p + i) = aview rsegs (w_H W6) mem6 (p + i)).
{ intros p m i Hb Hi. apply (KK2 p m i Hb Hi). pose proof (Hapart p m Hb). cbv beta. lia. }
assert (Hrq_out : req_size (3 * (e_cap e + 1)) = 3 * (e_cap e + 1))
  by (unfold req_size; destruct (Z.eqb_spec (3 * (e_cap e + 1)) 0); lia).
assert (Hrq_pod : req_size (e_len e) = e_len e) by (unfold req_size; destruct (Z.eqb_spec (e_len e) 0); lia).
(* the real frame above R: kept by the call *)
assert (Hkr : forall a, e_R e <= a < spZ (h_regs rsegs hx) -> aview rsegs (w_H W7) mem7 a = aview rsegs (w_H W6) mem6 a).
{ intros a Ha. apply KK1; lia. }
(* ===== hq_at_C7 ===== *)
unfold hq_at_C7. exists first, ly7, S7, regs7, mem7, md7.
split; [rewrite Ec7; reflexivity|].
split; [exact Hfirst|].
split; [exact H107|].
split; [exact KR|].
split; [exact Hfr7|].
split; [exact Hab7|].
split; [exact Hkept7|].
(* ===== hq_cut_C7 at the env with first ===== *)
unfold hq_cut_C7, hq_at_cut.
split.
{ split; [exact HJ7|].
  split.
  { change (hq_blocks7 (hq_env_first e first)) with (hq_blocks5 e ++ [(first, hd_xv e XRc3NZ)]).
    rewrite Hab7, app_assoc. apply Permutation_app_tail. exact Hperm6. }
  split.
  { change (hq_blocks7 (hq_env_first e first)) with (hq_blocks5 e ++ [(first, hd_xv e XRc3NZ)]).
    apply Forall_app. split; [exact Hfresh6|].
    apply Forall_cons; [|apply Forall_nil]. cbv beta. cbn [fst]. split; [exact Hfresh | lia]. }
  split.
  { rewrite (hk_getr_eq regs7 2 (Z_to_bv 5 2)) by reflexivity. rewrite (KR 2) by (unfold acallee_saved; lia).
    rewrite (hk_getr_eq regs6 (Z_to_bv 5 2) 2) by reflexivity. exact Hsp6. }
  split.
  { rewrite (hk_getr_eq regs7 3 (Z_to_bv 5 3)) by reflexivity. rewrite (KR 3) by (unfold acallee_saved; lia).
    rewrite (hk_getr_eq regs6 (Z_to_bv 5 3) 3) by reflexivity. exact Hgp6. }
  split.
  { rewrite (hk_getr_eq regs7 4 (Z_to_bv 5 4)) by reflexivity. rewrite (KR 4) by (unfold acallee_saved; lia).
    rewrite (hk_getr_eq regs6 (Z_to_bv 5 4) 4) by reflexivity. exact Htp6. }
  split; [exact Hgeo|].
  split.
  { (* hi_L7: hi_L6 kept (its cells lie above R), then a0 = first *)
    assert (HcutA : hd_cut rsegs (w_H W7) mem7 regs6 e (hi_L6 headamp_himg_A)).
    { apply (hm_cut_kept rsegs (w_H W6) mem6 (w_H W7) mem7 regs6 regs6 e _ HL6).
      intros f Hf. cbn [hi_L6 headamp_himg_A] in Hf. unfold headamp_A_L67 in Hf. cbn [In] in Hf.
      repeat (destruct Hf as [<-|Hf]; [cbn [fst hm_keeps hd_xv]; first [reflexivity | (intros i Hi; apply Hkr; lia)] |]).
      destruct Hf. }
    assert (HcutA' : hd_cut rsegs (w_H W7) mem7 regs6 (hq_env_first e first) (hi_L6 headamp_himg_A)).
    { unfold hd_cut in HcutA |- *. apply Forall_forall. intros f Hf.
      pose proof (proj1 (Forall_forall _ _) HcutA f Hf) as Hx.
      cbn [hi_L6 headamp_himg_A] in Hf. unfold headamp_A_L67 in Hf. cbn [In] in Hf.
      repeat (destruct Hf as [<-|Hf]; [exact Hx|]). destruct Hf. }
    apply (headamp_A_site_cut7 rsegs (w_H W7) mem7 mem7 regs6 regs7 (hq_env_first e first) HcutA').
    - rewrite (hk_getr_eq regs7 (Z_to_bv 5 10) 10) by reflexivity. exact H107.
    - intros rr _ Hrr. apply KR. cbn [In] in Hrr. unfold acallee_saved. lia.
    - intros o _ i _. reflexivity. }
  split.
  { (* the frame's shadow, kept by the call's frame clause *)
    apply (hm_fsh_kept rsegs (w_H W6) mem6 (w_H W7) mem7 (e_F e) _ Hfsh6).
    intros i Hi. assert (Hl : length (hi_shB headamp_himg_A) = 80%nat) by (vm_compute; reflexivity).
    rewrite Hl in Hi. cbn [Z.of_nat Pos.of_succ_nat] in Hi.
    apply (KK4 HQ_CID pos); [exact HinF6 | right | cbv beta; apply HshF; lia].
    unfold in_zr. cbn [fst snd]. rewrite FA6, Hfb. change (1024 / 8) with 128. lia. }
  { (* the thirteen saves and the flag cell, and the three float saves *)
    split.
    - assert (Hcl7 : Forall (fun f => hd_at rsegs (w_H W7) mem7 regs7 e (fst f) (snd f))
        (hq_cells (h_regs rsegs hx) (flag_addr (h_ly rsegs hx) HQ_CID pos))).
      { apply (hm_atl_kept rsegs (w_H W6) mem6 (w_H W7) mem7 regs6 regs7 e _ Hcl6).
        intros f Hf. unfold hq_cells, hq_saves_L in Hf. apply in_app_or in Hf as [Hf|Hf].
        + apply in_map_iff in Hf as (j & <- & Hj). apply in_seq in Hj. cbn [fst hm_keeps hd_xv].
          intros i Hi. apply Hkr. lia.
        + destruct Hf as [<-|[]]. cbn [fst hm_keeps hd_xv]. intros i Hi. unfold HQ_FLAG.
          apply (KK4 HQ_CID pos); [exact HinF6 | left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite FA6, Hfb; lia
          | cbv beta; lia]. }
      apply Forall_forall. intros f Hf. pose proof (proj1 (Forall_forall _ _) Hcl7 f Hf) as Hx.
      unfold hq_cells, hq_saves_L in Hf. apply in_app_or in Hf as [Hf|Hf].
      + apply in_map_iff in Hf as (j & <- & _). exact Hx.
      + destruct Hf as [<-|[]]. exact Hx.
    - destruct Hfs6 as (v0 & v1 & v2 & G0 & G1 & G2). exists v0, v1, v2.
      cbn [hd_at hd_xv hq_env_first e_S] in G0, G1, G2 |- *.
      split; [|split];
      (eapply (hd_val_mem_kept rsegs (w_H W6) (w_H W7) mem6 mem7); [|eassumption]);
      intros i Hi; apply Hkr; lia. } }
split; [exact Hfrm|].
split.
{ (* the record's data *)
  split; [exact Hwf|]. split; [exact Hlen|]. split; [exact Hlenb|].
  split.
  { apply (hd_garr8_kept rsegs (w_H W6) (w_H W7) mem6 mem7 (e_pp e)); [|exact Hpp].
    intros j Hj. unfold hd_zbytes in Hj. rewrite length_map in Hj.
    pose proof (Layout.length_pp_bytes r Hwf) as HLp.
    apply (Hkb _ _ _ Hpp6). change (req_size Layout.PP_SIZE) with 19744. change Layout.PP_SIZE with 19744 in HLp. lia. }
  split.
  { apply (hd_garr8_kept rsegs (w_H W6) (w_H W7) mem6 mem7 (e_pod e)); [|exact Hpod].
    intros j Hj. unfold hd_zbytes in Hj. rewrite length_map in Hj.
    apply (Hkb _ _ _ Hpod6). rewrite Hrq_pod. lia. }
  split; [exact Hpod16|].
  split.
  { exact (proj2 (hm_blk_ra rsegs B ly7 S7 W7 mem7 md7 (e_pod e) (e_len e) (e_pod e) (e_len e) HAR7 (Hin7 _ Hpod6)
      ltac:(lia) ltac:(rewrite Hrq_pod; lia)) ltac:(lia)). }
  split; [exact Hamem|]. split; [exact Hcap|]. split; [exact Hnull | exact Hrc]. }
split.
{ exact (proj1 (hm_blk_ra rsegs B ly7 S7 W7 mem7 md7 (e_pod e) (e_len e) (e_pod e) (e_len e) HAR7 (Hin7 _ Hpod6)
    ltac:(lia) ltac:(rewrite Hrq_pod; lia))). }
split.
{ exact (proj1 (hm_blk_ra rsegs B ly7 S7 W7 mem7 md7 (e_out e) (3 * (e_cap e + 1)) (e_out e) (3 * (e_cap e + 1))
    HAR7 (Hin7 _ Hout6) ltac:(lia) ltac:(rewrite Hrq_out; lia))). }
split.
{ exact (proj1 (hm_blk_ra rsegs B ly7 S7 W7 mem7 md7 first (hd_xv e XRc3NZ) first (hd_xv e XRc3NZ)
    HAR7 Hfirst7 ltac:(lia) ltac:(rewrite Hrq; lia))). }
split.
{ apply (hd_garr8_kept rsegs (w_H W6) (w_H W7) mem6 mem7 (e_out e)); [|exact Hcells].
  intros j Hj. unfold hd_zbytes in Hj. rewrite length_map, length_ha_cells_bytes in Hj.
  cbn [hq_env_first e_null e_cap] in Hj.
  apply (Hkb _ _ _ Hout6). rewrite Hrq_out. lia. }
exact (hk_errno_rd B (w_H W7) mem7 errno_low).
Qed.
(* inside the Section: the kernel's axioms and the Section hypotheses named in the header *)
Print Assumptions hq_A_S_C67.
End d.
End b.
Print Assumptions hq_A_S_C67.
