(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgRt.v at 6ebe35ba632; its rt_chain is ported here as rl_c23_chain (statement kept, proof by the kernel's achain_push); the rest of this file is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPostMal.v at b561c36fcf63 for reac-pw/fuzz_rate image A: role's C2 / C3 (0x820c0 / 0x820c4), malloc entry 0x52428 and real frame 0x1a0 become rate's 0x828b4 / 0x828b8, 0x52bb4 and 0x1e0; rl_ becomes rt_ (rt_c23_chain, rt_c23_ch, c23_rt_cell); the entry state is this file's own c23_entry in place of RPgCfgChanges.cfg_entry; rate's statement is in continuation form, so the malloc rule's post is bound (SRr_bind) and the cut rh_cut_C3 is built from it (c23_env_pod, c23_cut_move, c23_at_move and the block / frame / shadow separation are new) and handed to the continuation. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgPostMal.v at 8af9cea6f917 for reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan): image A's C2 / C3 (0x828b4 / 0x828b8), malloc entry 0x52bb4, real frame 0x1e0, class-3 frame (512 bytes, 64 shadow bytes, 56-byte pattern, flag word F + 0x1f8) and C2 list (cells up to R + 0x120) become image B's 0x82a2c / 0x82a30, 0x52c0c, 0x220, class-4 frame (1024 bytes, 128 shadow bytes, 88-byte pattern, flag word F + 0x3f8) and C2 list (cells up to R + 0x168); lib/A RtPgSeg / RtPgSteps / RtPgSiteA / RtPgImgA become lib/AU RtPgSegB / RtPgStepsB / RtPgSiteB / RtPgImgB (rh_ -> rhb_, rs_ / RS_ -> rsb_ / RSB_, rts_ -> rtsb_, rate_A_ -> rate_B_), images.Asan becomes images.AsanUbsan; c23_ becomes c23b_ (C23_SB C23B_SB), rt_c23_chain / rt_c23_ch / rt_A_S_C23 become rtb_c23_chain / rtb_c23_ch / rt_B_S_C23. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgPostMalB.v at db4fc362bebf for reac-pw/fuzz_role image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role and the segments lib/AU/Img0.v rsegs; rate B's C2 / C3 (0x82a2c / 0x82a30), malloc entry 0x52c0c, real frame 0x220 (o in [-0x230, -0x220]) and C2 list (cells up to R + 0x168) become role B's 0x82164 / 0x82168, 0x524c0, 0x200 (o in [-0x210, -0x200]) and cells up to R + 0x140 (the same class-4 frame); RtPgBase / RtPgSegB / RtPgStepsB / RtPgSiteB / RtPgImgB become RPgBase / RPgHarn / RPgSteps / RPgSiteA / RPgImgA (rt_ -> rl_, rt_renv q_X -> rl_env e_X, rhb_ / RSB_ -> rh_ / RH_, rate_B_ -> role_B_); c23b_ / C23B_ become c23_ / C23_, rtb_c23_chain / rtb_c23_ch / rt_B_S_C23 become rl_c23_chain / rl_c23_ch / rl_B_S_C23; c23b_env_pod is RPgHarn's rh_env_pod; the C3 values come from role_B_site_cut3 (register and cell premises in its own form). *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): THE malloc(pod) STEP of the
   walk of LLVMFuzzerTestOneInput, C2 = 0x82164 -> C3 = 0x82168, i.e. lib/AU/RPgHarn.v rh_S_C23_stmt at the concrete
   segments of image B (lib/AU/Img0.v rsegs). Proves no function (kind: segment lemma).

   THE CODE. At C2 a0 = len + (len == 0) (hi_L2: (LReg 10, XLenNZ); 0x82158 `ld s8,0(s6)` (or 0x81f28),
   0x8215c `seqz a0,s8`, 0x82160 `add a0,s8,a0`), and 8 <= len <= 5440 (rh_cut_C2), so a0 = len. 0x82164 is
   `jal 0x524c0`: ra := 0x82168, pc := 0x524c0, the malloc wrapper's entry of image B (pc_wrap_malloc =
   RPgSteps.RL_MALLOC). C3 = 0x82168 (`beqz a0`) is the return address.

   THE ROUTE.
   1. The engine runs the one `jal` from an entry state with every register an atom (c23_entry, the one-word table
      c23_tbl at 0x82164); it stops at 0x524c0 with ra the literal 0x82168, every other register its own atom, and
      no byte written.
   2. The kernel's journal malloc rule YCbq.aj_malloc_at04 at the harness journal rh_j (STK = LLVMF_STK, sp0 = S,
      FP = [], own = [(4, pos)], k = 1), with o = R - S (R = e_R e = 32 * floor((S - 0x200) / 32), so o is
      16-aligned, -0x210 <= o <= -0x200), the event and live-byte budgets from rh_base, and the caller chain from the
      harness entry: the entry's achain (afn_pre, ch = []) pushed with the frame record the prologue stored at S - 8
      (ra) and S - 16 (s0), which rh_kept carries (rl_c23_chain), s0 = S at C2 (hi_L2: (LReg 8, XS)).
   3. The rule's post (two events, a0 = pod >= 4096, the callee-saved registers of C2 kept, frames kept, the block
      appended, acall_kept outside [R - ASTACK, R) and the new block) gives rh_cut_C3 at rh_env_pod e pod: the
      blocks (the new block is not among the entry's, because AR keeps the live blocks pairwise disjoint), sp / gp /
      tp, the C3 values (RPgSiteA.role_B_site_cut3: the R-relative cells of hi_L2 lie in [R, R + 0x148), above the
      callee's stack), the 13 saves at [S - 0x68, S), the flag word at F + 0x3f8 and the class-4 frame's 128 shadow
      bytes (the frame's 1024 bytes and its shadow are disjoint from the new block: AR's frame/block separation and
      in_app of the block), and pp's 19744 bytes (pp and the new block are disjoint live blocks). The continuation
      rh_from_C3 takes it from there.

   SECTION HYPOTHESES (each is what the harness level supplies):
     AMALLOC     amalloc_realizes rsegs B             the runtime's malloc against the model
     errno_low   api_env rsegs B                      errno cell and the allocator's one-entry traces
     ML          model_laws (as_universe B)           the allocator model's laws
     HPCM        pc_wrap_malloc (as_code B) = 0x524c0 the code record: malloc's entry (RL_MALLOC) is the jal's target
     HSTK_C23    ASTACK + RH_RSZ + 16 <= LLVMF_STK    the call's stack budget: ASTACK - o <= LLVMF_STK
     HEV_C23     2 <= EV_LIB                          room for this event: st_nev < EV_MAX
     HLIVE_C23   Layout.PP_SIZE + 5440 <= LIVE_LIB    room for pod after pp: blocks_bytes + len <= LIVE_MAX
     HTRACE_C23  the malloc trace at ra = 0x82168 is in the universe (one site).
   AXIOMS: the primitive int / string / array axioms and Stdlib's functional_extensionality_dep, which the kernel's
   engine runner YCbq.SRr_run_tok_AJ uses. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YO0f YG0s YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Layout Model.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgImgA RPgHarn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require RPgSteps RPgSiteA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the harness entry record's projections with the segment list implicit, as RPgHarn's own text reads them *)
Local Arguments h_ly {_} _. Local Arguments h_S {_} _. Local Arguments h_W {_} _.
Local Arguments h_regs {_} _. Local Arguments h_mem {_} _. Local Arguments h_md {_} _.

(* ---- the one instruction word the engine runs: the `jal` at C2 ---- *)
Definition c23_tbl : ctable := build_table rsegs RH_C2 1 TEmpty.
Lemma c23_tbl_ok : table_ok rsegs c23_tbl.
Proof. apply build_table_ok0. unfold RH_C2. lia. Qed.
(* the walk's context: env slot 32 is the shadow base (no shadow entry is used) *)
Definition C23_SB : Z := 0x7fff8000.
Definition c23_Bx : sv := SOff 32 0.
Definition c23_span : Z * Z := (C23_SB, C23_SB + 2 ^ 44 - 1).
Definition c23_extra : list word := [Z_to_bv 64 C23_SB].

(* a cut entry the pod does not name: its value is not the pod, and it is a register or a cell R + o, 0 <= o <= 0x140 *)
Definition c23_xr_ok (f : rl_loc * rl_x) : bool :=
  match snd f with XPod => false | _ => true end &&
  match fst f with LReg _ => true | LCell XR o => (0 <=? o) && (o <=? 0x140) | LCell _ _ => false end.
Lemma c23_xv_pod : forall e p x, match x with XPod => false | _ => true end = true ->
rl_xv (rh_env_pod e p) x = rl_xv e x.
Proof. intros e p x H. destruct x; first [reflexivity | discriminate H]. Qed.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- memories equal at every word give the same view, presence, words and kept clauses ---- *)
Lemma c23_aview_mem : forall H (m m' : word -> option byte), (forall x, m' x = m x) ->
forall a, aview rsegs H m' a = aview rsegs H m a.
Proof. intros H m m' Hm a. unfold aview, mbyte, mrestrict. cbv beta. rewrite Hm. reflexivity. Qed.
Lemma c23_apresent_mem : forall H (m m' : word -> option byte), (forall x, m' x = m x) ->
forall a, apresent H m a -> apresent H m' a.
Proof. intros H m m' Hm a [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite Hm. exact Hb. Qed.
Lemma c23_rdword_mem : forall H (m m' : word -> option byte) a, (forall x, m' x = m x) ->
rdword (aview rsegs H m') a = rdword (aview rsegs H m) a.
Proof. intros H m m' a Hm. apply rdword_ext. intros k _. apply c23_aview_mem. exact Hm. Qed.

(* ---- an 8-byte cell as a word of the view (the converse of YCbq.val_mem_of_rdword) ---- *)
Lemma c23_rdword_of_val_mem : forall H mem a v, 0 <= v < 2 ^ 64 ->
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
(* a cell fact of RPgBase as a word of the view *)
Lemma c23_rl_cell : forall H mem regs e b o v, 0 <= v < 2 ^ 64 ->
rl_at rsegs H mem regs e (LCell b o) v -> rdword (aview rsegs H mem) (rl_xv e b + o) = Some v.
Proof.
intros H mem regs e b o v Hv Hc. cbn [rl_at] in Hc. rewrite Z.mod_small in Hc by exact Hv.
apply c23_rdword_of_val_mem; assumption.
Qed.

(* ---- register names: a literal and Z_to_bv 5 of its number name the same register ---- *)
Lemma c23_getr_eq : forall regs (b b' : bv 5), bv_unsigned b = bv_unsigned b' -> getr regs b = getr regs b'.
Proof. intros regs b b' E. apply bv_eq in E. subst b'. reflexivity. Qed.
Lemma c23_csaved : forall r, acallee_saved r -> bv_unsigned (Z_to_bv 5 r) = r.
Proof.
intros r Hr. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
apply Z.mod_small. unfold acallee_saved in Hr. lia.
Qed.

(* ---- the caller chain at a call from the harness frame [knock APgRt.v rt_chain] ---- *)
Lemma rl_c23_chain : forall ly (rd rd' : reader) (regs : bvmap 5 word) sp',
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

Lemma c23_acall_kept_mem : forall B ly S W (m m' : word -> option byte) W3 m3 slo shi (E : Z -> Prop),
(forall x, m' x = m x) ->
acall_kept rsegs B ly S W m' W3 m3 slo shi E -> acall_kept rsegs B ly S W m W3 m3 slo shi E.
Proof.
intros B ly S W m m' W3 m3 slo shi E Hm (K1 & K2 & K3 & K4 & K5 & K6).
pose proof (c23_aview_mem (w_H W) m m' Hm) as Hv.
split; [intros a Ha Hs; rewrite <- Hv; exact (K1 a Ha Hs)|].
split; [intros b n i Hb Hi HE; rewrite <- Hv; exact (K2 b n i Hb Hi HE)|].
split; [intros a Ha Ho He; rewrite <- Hv; exact (K3 a Ha Ho He)|].
split; [intros cid pos a Hf Hr HE; rewrite <- Hv; exact (K4 cid pos a Hf Hr HE)|].
split; [intros a Ha Hs Hp; exact (K5 a Ha Hs (c23_apresent_mem (w_H W) m m' Hm a Hp))|].
exact K6.
Qed.

(* ---- a cut list moved to another world and memory, at the run's quantities with the pod filled in: its registers
   as they were, its cells R + o (0 <= o <= 0x140) with the same bytes ---- *)
Lemma c23_cut_move : forall H H' (mem mem' : word -> option byte) (regs : bvmap 5 word) (e : rl_env) p
  (L : list (rl_loc * rl_x)),
forallb c23_xr_ok L = true ->
(forall o k, 0 <= o <= 0x140 -> 0 <= k < 8 -> aview rsegs H' mem' (e_R e + o + k) = aview rsegs H mem (e_R e + o + k)) ->
rl_cut rsegs H mem regs e L -> rl_cut rsegs H' mem' regs (rh_env_pod e p) L.
Proof.
intros H H' mem mem' regs e p L Hok Hk HC. unfold rl_cut in *. rewrite Forall_forall in *.
intros [l x] Hin. pose proof (HC (l, x) Hin) as Hf. pose proof (proj1 (forallb_forall _ _) Hok (l, x) Hin) as Hb.
unfold c23_xr_ok in Hb. cbn [fst snd] in *. apply andb_prop in Hb as [Hx Hl].
rewrite (c23_xv_pod e p x Hx).
destruct l as [r | b o]; cbn [rl_at] in *.
- exact Hf.
- destruct b; simpl in Hl; try discriminate Hl.
  change ((0 <=? o) && (o <=? 0x140) = true) in Hl.
  apply andb_prop in Hl as [H0 H1]. apply Z.leb_le in H0. apply Z.leb_le in H1.
  cbn [rl_xv rh_env_pod e_R] in *.
  apply (val_mem_kept rsegs H H' mem mem'); [| exact Hf].
  intros k Hk'. change (Z.of_nat 8) with 8 in Hk'. apply Hk; lia.
Qed.
(* ---- a list of (location, value) facts moved to another world, memory and register file ---- *)
Lemma c23_at_move : forall H H' (mem mem' : word -> option byte) (regs regs' : bvmap 5 word) (e e' : rl_env)
  (L : list (rl_loc * Z)),
(forall r v, In (LReg r, v) L -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
(forall b o v, In (LCell b o, v) L -> rl_xv e' b = rl_xv e b /\
  forall k, 0 <= k < 8 -> aview rsegs H' mem' (rl_xv e b + o + k) = aview rsegs H mem (rl_xv e b + o + k)) ->
Forall (fun f => rl_at rsegs H mem regs e (fst f) (snd f)) L ->
Forall (fun f => rl_at rsegs H' mem' regs' e' (fst f) (snd f)) L.
Proof.
intros H H' mem mem' regs regs' e e' L Hr Hc HF. rewrite Forall_forall in *.
intros [l v] Hin. pose proof (HF (l, v) Hin) as Hf. cbn [fst snd] in *.
destruct l as [r | b o]; cbn [rl_at] in *.
- rewrite (Hr r v Hin). exact Hf.
- destruct (Hc b o v Hin) as [Eb Hk]. rewrite Eb.
  apply (val_mem_kept rsegs H H' mem mem'); [| exact Hf].
  intros k Hk'. change (Z.of_nat 8) with 8 in Hk'. apply Hk. exact Hk'.
Qed.
End h.

(* the side goals of a register a run did not touch (clob = [ra]) *)
Ltac c23_rk :=
first
[ solve [vm_compute; let Hx := fresh "Hx" in intros Hx; discriminate Hx]
| solve [let Hx := fresh "Hx" in intros [Hx|[]]; apply (f_equal (@bv_unsigned 5)) in Hx; vm_compute in Hx; discriminate Hx] ].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* the entry state at pc: the registers as atoms, no region, no fact *)
Definition c23_ss (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
Lemma c23_entry : forall pc (W : world rsegs) regs memc, 0 <= pc ->
st_ok rsegs (Ereg regs c23_extra) (c23_ss pc) (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
intros pc W regs memc Hpc.
rewrite restrict_mkst_fx.
unfold c23_ss. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I.
Qed.
(* the caller chain the malloc call sees: the harness entry's own record (sp, ra, s0) when its frame is below the
   stack top *)
Definition rl_c23_ch (hx : rh_hcx rsegs) : list (Z * Z * Z) :=
if spZ (h_regs hx) + 16 <? ly_top (h_ly hx) then [(spZ (h_regs hx), raZ (h_regs hx), s0Z (h_regs hx))] else [].
Section d.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
Hypothesis AMALLOC : amalloc_realizes rsegs B.
Hypothesis errno_low : api_env rsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis HPCM : pc_wrap_malloc (as_code B) = 0x524c0.
Hypothesis HSTK_C23 : ASTACK + RH_RSZ + 16 <= LLVMF_STK.
Hypothesis HEV_C23 : 2 <= EV_LIB.
Hypothesis HLIVE_C23 : Layout.PP_SIZE + 5440 <= LIVE_LIB.
Hypothesis HTRACE_C23 : forall (regsT : bvmap 5 word) (hx : rh_hcx rsegs),
raZ (h_regs hx) = RA_LLVMF -> raZ regsT = RH_C3 ->
In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT (rl_c23_ch hx)) (as_universe B).

Theorem rl_B_S_C23 : rh_S_C23_stmt rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof using AMALLOC errno_low ML HPCM HSTK_C23 HEV_C23 HLIVE_C23 HTRACE_C23.
intros hx POST HB HC3 pos e rest ly2 S2 W2 regs2 mem2 md2 HC.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof RPgSteps.rl_wx as Hwx. pose proof RPgSteps.rl_segs_low as Hsegs.
destruct HB as (HPRE & Hra0 & _ & _ & _ & _ & _ & _ & Hev0 & Hlive0 & _).
destruct HPRE as (HAR0 & Hraok0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
destruct Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HC as (HCOM & Hpp0 & Hfsh2 & Hlen & Hpp2).
destruct HCOM as (HJ & Hfr2 & Hperm2 & Hnin2 & Hsp2 & Hgp2 & Htp2 & Hgeo2 & Hhdr2 & Hhok2 & Hcut2 & Hkept2).
pose proof Hgeo2 as (HeS & HeR & HeF).
unfold rh_j in HJ.
pose proof HJ as (_ & Hly2 & _ & _ & _ & _ & Hnev & _ & F1 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF2' & _ & _ & Etop & _).
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
pose proof HSTK_C23 as HSTK. unfold ASTACK, RH_RSZ in HSTK.
(* the geometry: S = 16 t, R = 32 q with S - 512 = 32 q + r, 0 <= r < 32, so r is 0 or 16 *)
rewrite HeS in HeR. unfold RH_RSZ in HeR.
pose proof (Z.div_mod (spZ (h_regs hx) - 0x200) 32 ltac:(lia)) as Dq.
pose proof (Z.mod_pos_bound (spZ (h_regs hx) - 0x200) 32 ltac:(lia)) as Bq.
pose proof (Z.div_mod (spZ (h_regs hx)) 16 ltac:(lia)) as D16. rewrite Hal16, Z.add_0_r in D16.
assert (HRb : alloc_ceiling + 16384 <= e_R e /\ e_R e + 512 <= spZ (h_regs hx) /\ spZ (h_regs hx) - e_R e <= 528) by lia.
assert (HR64 : 0 <= e_R e < 2 ^ 64) by zlia.
assert (HS64 : 0 <= spZ (h_regs hx) < 2 ^ 64) by zlia.
assert (HAL : (e_R e - spZ (h_regs hx)) mod 16 = 0).
{ replace (e_R e - spZ (h_regs hx)) with ((2 * ((spZ (h_regs hx) - 0x200) / 32) - spZ (h_regs hx) / 16) * 16) by lia.
  apply Z.mod_mul. lia. }
assert (HS8 : spZ (h_regs hx) mod 8 = 0).
{ replace (spZ (h_regs hx)) with ((2 * (spZ (h_regs hx) / 16)) * 8) by lia. apply Z.mod_mul. lia. }
clear Dq Bq D16.
(* the C2 values a0 = len and s0 = S *)
pose proof Hcut2 as Hc. unfold rl_cut in Hc. change (hi_L2 role_himg_B) with (role_B_L23 XLenNZ) in Hc.
unfold role_B_L23 in Hc.
apply Forall_cons_iff in Hc as [C10 Hc]. apply Forall_cons_iff in Hc as [C8 _].
cbn [fst snd rl_at rl_xv] in C10, C8.
replace (e_len e =? 0) with false in C10 by (symmetry; apply Z.eqb_neq; lia). rewrite Z.add_0_r in C10.
rewrite HeS in C8.
(* the frame record the prologue stored: ra at S - 8, s0 at S - 16 *)
pose proof Hkept2 as Hk. unfold rh_kept, rh_cells, rh_saves_L in Hk. cbn [seq map app] in Hk.
apply Forall_cons_iff in Hk as [K0 Hk]. apply Forall_cons_iff in Hk as [K1 _].
cbv beta in K0, K1. cbn [fst snd] in K0, K1.
pose proof (c23_rl_cell _ _ _ _ _ _ _ (u64_range _) K0) as W8.
pose proof (c23_rl_cell _ _ _ _ _ _ _ (u64_range _) K1) as W16.
cbn [rl_xv] in W8, W16. rewrite HeS in W8, W16.
assert (R8 : rdword (aview rsegs (w_H W2) mem2) (spZ (h_regs hx) - 8) = Some (raZ (h_regs hx))).
{ replace (spZ (h_regs hx) - 8) with (spZ (h_regs hx) + (-8 - 8 * Z.of_nat 0)) by lia. exact W8. }
assert (R16 : rdword (aview rsegs (w_H W2) mem2) (spZ (h_regs hx) - 16) = Some (s0Z (h_regs hx))).
{ replace (spZ (h_regs hx) - 16) with (spZ (h_regs hx) + (-8 - 8 * Z.of_nat 1)) by lia. exact W16. }
clear W8 W16 K0 K1.
(* 1. the `jal`: one engine step to 0x524c0 *)
pose proof (c23_entry RH_C2 W2 regs2 mem2 ltac:(unfold RH_C2; lia)) as HS.
assert (SHOK : sh_ok rsegs c23_Bx [] (Ereg regs2 c23_extra) (mrestrict (w_H W2) mem2)) by constructor.
assert (HAE : env_agree 32 (Ereg regs2 c23_extra) (Ereg regs2 c23_extra)) by apply env_agree_refl.
unfold cfg_at. change (w64 RH_C2) with (Z_to_bv 64 RH_C2).
aj_run_tok c23_tbl_ok HS HJ SHOK c23_span; [awr_ok_tac |].
(* no byte written; every register but ra its own atom; ra the literal 0x82168 *)
assert (Hm : forall x, ms_mem ms x = mem2 x).
{ intros x. apply HF. intros (rg & Hrg & _). exact Hrg. }
assert (RK : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r [Z_to_bv 5 1] -> getr (ms_regs ms) r = getr regs2 r).
{ eapply (RPgSteps.regs_kept_of_st_ok rsegs _ _ ms regs2 c23_extra (w_H W2) _ HS HAE). vm_compute. reflexivity. }
assert (HRA : getr (ms_regs ms) 1 = Z_to_bv 64 0x82168).
{ rewrite (c23_getr_eq (ms_regs ms) 1 (Z_to_bv 5 1)) by reflexivity.
  lazymatch type of HS with st_ok _ ?E ?ss _ =>
    let e1 := eval vm_compute in (sr_get (ss_regs ss) (Z_to_bv 5 1)) in
    assert (R1 : getr (ms_regs ms) (Z_to_bv 5 1) = sv_denot E e1)
      by exact (st_ok_restrict_reg rsegs (w_H W2) E ss ms (Z_to_bv 5 1) HS) end.
  cbn [sv_denot] in R1. rewrite R1. reflexivity. }
(* 2. the call's premises *)
assert (HA10 : getr (ms_regs ms) 10 = w64 (e_len e)).
{ rewrite RK by c23_rk. rewrite (c23_getr_eq regs2 10 (Z_to_bv 5 10)) by reflexivity. exact C10. }
assert (HN : 0 <= e_len e < MALLOC_MAX) by (unfold MALLOC_MAX; lia).
assert (HLV : blocks_bytes S2 + e_len e <= LIVE_MAX).
{ assert (EB : forall ly S, blocks_bytes S = bsum (ablocks B ly S)) by (intros; apply blocks_bytes_bsum).
  rewrite (EB ly2 S2), (bsum_perm _ _ Hperm2), bsum_app, <- (EB (h_ly hx) (h_S hx)).
  change (bsum [(e_pp e, Layout.PP_SIZE)]) with (Layout.PP_SIZE + 0). lia. }
assert (HSP : spZ (ms_regs ms) = spZ (h_regs hx) + (e_R e - spZ (h_regs hx))).
{ unfold spZ at 1. rewrite RK by c23_rk. rewrite Hsp2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (HNEG : e_R e - spZ (h_regs hx) <= 0) by lia.
assert (HBUD : ASTACK - (e_R e - spZ (h_regs hx)) <= LLVMF_STK) by (unfold ASTACK; lia).
assert (HGP : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite RK by c23_rk; exact Hgp2).
assert (HTP : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite RK by c23_rk; exact Htp2).
assert (HRAOK : YK0s.ret_ok (Z_to_bv 64 0x82168)) by (unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity).
assert (HEV : st_nev S2 < EV_MAX) by lia.
assert (HRAZ : raZ (ms_regs ms) = 0x82168) by (unfold raZ; rewrite HRA; apply unsigned_lit_small; lia).
assert (HCH : chain_pre ly2 (aview rsegs (w_H W2) (ms_mem ms)) (ms_regs ms) (rl_c23_ch hx)).
{ apply (achain_chain_pre ly2 _ (e_R e) (spZ (h_regs hx))).
  - apply (achain_ly_top (h_ly hx) ly2 _ _ _ _ Etop). unfold rl_c23_ch.
    apply (rl_c23_chain (h_ly hx) (aview rsegs (w_H (h_W hx)) (h_mem hx))).
    + exact Hch0.
    + zlia.
    + intros a Ha. rewrite (c23_aview_mem (w_H W2) mem2 (ms_mem ms) Hm). apply F1; zlia.
    + rewrite (c23_rdword_mem (w_H W2) mem2 (ms_mem ms) _ Hm). exact R8.
    + rewrite (c23_rdword_mem (w_H W2) mem2 (ms_mem ms) _ Hm). exact R16.
    + exact Hra40.
    + lia.
    + exact HS8.
    + lia.
  - rewrite HSP. lia.
  - unfold s0Z. rewrite RK by c23_rk. rewrite (c23_getr_eq regs2 8 (Z_to_bv 5 8)) by reflexivity.
    rewrite C8. unfold w64. apply unsigned_lit_small. lia.
  - rewrite HRAZ. lia. }
assert (HTR : In (call_trace0 (pc_malloc_ra0 (as_code B)) (ms_regs ms) (rl_c23_ch hx)) (as_universe B)).
{ apply HTRACE_C23; [exact Hra0 | rewrite HRAZ; reflexivity]. }
(* the machine state at 0x524c0 = pc_wrap_malloc *)
pose proof (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl) as Ems.
rewrite Ems at 1.
lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?s)] =>
  replace (ss_pc s) with (pc_wrap_malloc (as_code B)) by (rewrite HPCM; vm_compute; reflexivity) end.
eapply SRr_bind.
{ exact (aj_malloc_at04 rsegs B LAWS Hsegs errno_low ML AMALLOC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    HJ HA10 HN HLV HSP HAL HNEG HBUD HGP HTP HRA HRAOK HEV HCH HTR). }
(* 3. the cut at C3, built from the rule's post, and the continuation from it *)
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & res & Ec3 & HJ3 & Hpres3 & H103 & Hfr3 & Hres & Hab3 & Hkept3).
replace (spZ (h_regs hx) + (e_R e - spZ (h_regs hx))) with (e_R e) in Hkept3 by lia.
apply (c23_acall_kept_mem B ly2 S2 W2 mem2 (ms_mem ms) W3 mem3 _ _ _ Hm) in Hkept3.
destruct Hkept3 as (K1 & K2 & _ & K4 & _ & _).
clear HAL HS8.
pose proof HJ3 as (HAR3 & Hly3 & _).
assert (E1024 : fs_frame_bytes RH_CID = 1024) by reflexivity.
assert (EF2 : frame_addr ly2 RH_CID pos = e_F e).
{ rewrite HeF. unfold frame_addr. rewrite EF2'. reflexivity. }
assert (EF3 : frame_addr ly3 RH_CID pos = e_F e).
{ rewrite HeF. unfold frame_addr. destruct Hly3 as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
assert (Hnew3 : In (res, e_len e) (ablocks B ly3 S3)) by (rewrite Hab3; apply in_or_app; right; left; reflexivity).
assert (Hpp2in : In (e_pp e, Layout.PP_SIZE) (ablocks B ly2 S2)).
{ apply (Permutation_in _ (Permutation_sym Hperm2)). apply in_or_app. right. left. reflexivity. }
assert (Hpp3in : In (e_pp e, Layout.PP_SIZE) (ablocks B ly3 S3)) by (rewrite Hab3; apply in_or_app; left; exact Hpp2in).
assert (Hfr3' : frames S3 = [(RH_CID, pos)]) by (rewrite Hfr3; exact Hfr2).
assert (Hfin2 : In (RH_CID, pos) (frames S2)) by (rewrite Hfr2; left; reflexivity).
assert (Hfin3 : In (RH_CID, pos) (frames S3)) by (rewrite Hfr3'; left; reflexivity).
assert (Hrs : 1 <= req_size (e_len e) <= 5440) by (unfold req_size; destruct (Z.eqb_spec (e_len e) 0); lia).
(* the new block is disjoint from the frame for locals, from the frame's shadow and from pp *)
assert (NF : forall a, e_F e <= a < e_F e + 1024 -> ~ (res <= a < res + req_size (e_len e))).
{ pose proof (sep_block_frame rsegs B LAWS ly3 S3 W3 mem3 md3 res (e_len e) RH_CID pos HAR3 Hnew3 Hfin3) as DF.
  rewrite EF3, E1024 in DF. unfold zdisjoint in DF. cbn [fst snd] in DF. intros a Ha Hb. lia. }
assert (NS : forall i, 0 <= i < 128 -> ~ (res <= shadow_addr (e_F e) + i < res + req_size (e_len e))).
{ destruct (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 res (e_len e) HAR3 Hnew3) as (_ & _ & _ & [Hh1 Hh2] & _).
  destruct (frames_bounds rsegs B LAWS ly3 S3 W3 mem3 md3 RH_CID pos HAR3 Hfin3) as (Hf0 & Hfc & _).
  rewrite EF3 in Hf0, Hfc. rewrite E1024 in Hfc.
  pose proof (shadow_addr_bounds (e_F e) ltac:(lia)) as SB1.
  pose proof (shadow_addr_bounds (e_F e + 1024) ltac:(lia)) as SB2.
  pose proof (shadow_range_end (e_F e) 1024 ltac:(lia)) as SRE.
  change (1024 / 8) with 128 in SRE. unfold kLowShadowBeg in Hh2. intros i Hi Hb. lia. }
assert (NP : forall i, 0 <= i < Layout.PP_SIZE -> ~ (res <= e_pp e + i < res + req_size (e_len e))).
{ assert (Hne : (e_pp e, Layout.PP_SIZE) <> (res, e_len e))
    by (intros Eq; injection Eq as _ Ez; unfold Layout.PP_SIZE in Ez; lia).
  pose proof (sep_blocks rsegs B LAWS ly3 S3 W3 mem3 md3 (e_pp e) Layout.PP_SIZE res (e_len e) HAR3 Hpp3in Hnew3 Hne) as Dpp.
  unfold zdisjoint in Dpp. cbn [fst snd] in Dpp. change (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Dpp.
  intros i Hi Hb. lia. }
(* the callee-saved registers of C2 at C3 (the `jal` changes only ra, the call keeps them) *)
assert (KR : forall r, acallee_saved r -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)).
{ intros r Hr. rewrite (Hpres3 r Hr). apply RK.
  - rewrite (c23_csaved r Hr). unfold acallee_saved in Hr. lia.
  - intros [Hx|[]]. apply (f_equal (@bv_unsigned 5)) in Hx. rewrite (c23_csaved r Hr) in Hx.
    change (bv_unsigned (Z_to_bv 5 1)) with 1 in Hx. unfold acallee_saved in Hr. lia. }
assert (OK2 : forallb c23_xr_ok (role_B_L23 XLenNZ) = true) by (vm_compute; reflexivity).
rewrite Ec3.
apply (HC3 pos (rh_env_pod e res) rest ly3 S3 W3 regs3 mem3 md3).
unfold rh_cut_C3. split.
{ unfold rh_common.
  split; [unfold rh_j; exact HJ3|].
  split; [exact Hfr3'|].
  split.
  { unfold rh_env_pod. cbn [e_pp e_pod e_len]. rewrite Hab3.
    change [(e_pp e, Layout.PP_SIZE); (res, e_len e)] with ([(e_pp e, Layout.PP_SIZE)] ++ [(res, e_len e)]).
    rewrite app_assoc. apply Permutation_app_tail. exact Hperm2. }
  split.
  { unfold rh_env_pod. cbn [e_pp e_pod e_len].
    apply Forall_cons; [exact (Forall_inv Hnin2)|]. apply Forall_cons; [|constructor].
    intros Hin.
    assert (Hin2 : In (res, e_len e) (ablocks B ly2 S2))
      by (apply (Permutation_in _ (Permutation_sym Hperm2)); apply in_or_app; left; exact Hin).
    apply in_split in Hin2 as (l1 & l2 & El).
    pose proof (sep_blocks_pos rsegs B LAWS ly3 S3 W3 mem3 md3 (res, e_len e) (res, e_len e) l1 l2 [] HAR3
      ltac:(rewrite Hab3, El, <- app_assoc; reflexivity)) as Hd.
    unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia. }
  split.
  { rewrite (c23_getr_eq regs3 2 (Z_to_bv 5 2)) by reflexivity. rewrite (KR 2) by (unfold acallee_saved; lia).
    rewrite <- (c23_getr_eq regs2 2 (Z_to_bv 5 2)) by reflexivity. exact Hsp2. }
  split.
  { rewrite (c23_getr_eq regs3 3 (Z_to_bv 5 3)) by reflexivity. rewrite (KR 3) by (unfold acallee_saved; lia).
    rewrite <- (c23_getr_eq regs2 3 (Z_to_bv 5 3)) by reflexivity. exact Hgp2. }
  split.
  { rewrite (c23_getr_eq regs3 4 (Z_to_bv 5 4)) by reflexivity. rewrite (KR 4) by (unfold acallee_saved; lia).
    rewrite <- (c23_getr_eq regs2 4 (Z_to_bv 5 4)) by reflexivity. exact Htp2. }
  split; [exact Hgeo2|].
  split; [exact Hhdr2|].
  split; [exact Hhok2|].
  split.
  { apply (RPgSiteA.role_B_site_cut3 rsegs (w_H W3) mem3 mem3 regs2 regs3 (rh_env_pod e res)).
    - apply (c23_cut_move (w_H W2) (w_H W3) mem2 mem3 regs2 e res _ OK2); [|exact Hcut2].
      intros o k Ho Hk. apply K1; lia.
    - rewrite <- (c23_getr_eq regs3 10 (Z_to_bv 5 10)) by reflexivity. exact H103.
    - intros r _ Hr. apply KR. cbn [In] in Hr. unfold acallee_saved. lia.
    - intros o _ i _. reflexivity. }
  unfold rh_kept.
  apply (c23_at_move (w_H W2) (w_H W3) mem2 mem3 regs2 regs3 e (rh_env_pod e res) _); [| | exact Hkept2].
  - intros r v Hin. exfalso. unfold rh_cells, rh_saves_L in Hin.
    apply in_app_or in Hin as [Hin | [Hin | []]]; [apply in_map_iff in Hin as (j & Ej & _) |]; discriminate.
  - intros b o v Hin. unfold rh_cells, rh_saves_L in Hin. apply in_app_or in Hin as [Hin | [Hin | []]].
    + apply in_map_iff in Hin as (j & Ej & Hj). apply in_seq in Hj. injection Ej as <- <- _.
      split; [reflexivity|]. intros k Hk. cbn [rl_xv]. rewrite HeS. apply K1; lia.
    + injection Hin as <- <- _. split; [reflexivity|]. intros k Hk. cbn [rl_xv].
      apply (K4 RH_CID pos); [exact Hfin2 | left | cbv beta; apply NF; lia].
      unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF2, E1024. lia. }
split; [exact Hpp0|].
split; [cbn [e_pod rh_env_pod]; lia|].
split.
{ unfold rl_fsh. intros i Hi. change (e_F (rh_env_pod e res)) with (e_F e).
  change (Z.of_nat (length (hi_shA role_himg_B))) with 88 in Hi.
  rewrite (K4 RH_CID pos (shadow_addr (e_F e) + i) Hfin2).
  - exact (Hfsh2 i ltac:(change (Z.of_nat (length (hi_shA role_himg_B))) with 88; exact Hi)).
  - right. unfold in_zr. cbn [fst snd]. rewrite EF2, E1024. change (1024 / 8) with 128. lia.
  - apply NS. lia. }
split; [exact Hlen|].
change (e_pp (rh_env_pod e res)) with (e_pp e).
pose proof (Layout.length_pp_bytes (fst (Model.pod_build rest))
  (Model.pod_build_wf rest _ (snd (Model.pod_build rest)) (surjective_pairing _))) as Elen.
intros j Hj. rewrite length_map in Hj.
destruct (Hpp2 j ltac:(rewrite length_map; exact Hj)) as [Hv Hb]. split; [|exact Hb].
apply (val_mem_kept rsegs (w_H W2) (w_H W3) mem2 mem3); [|exact Hv].
intros k Hk. change (Z.of_nat 1) with 1 in Hk.
replace (e_pp e + Z.of_nat j + k) with (e_pp e + (Z.of_nat j + k)) by lia.
apply (K2 (e_pp e) Layout.PP_SIZE); [exact Hpp2in | change (req_size Layout.PP_SIZE) with Layout.PP_SIZE; lia |].
intros HE. exact (NP (Z.of_nat j + k) ltac:(lia) HE).
Qed.
End d.
End b.
