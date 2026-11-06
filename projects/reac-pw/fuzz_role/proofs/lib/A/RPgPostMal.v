(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgRt.v at 6ebe35ba632; its rt_chain is ported here as rl_c23_chain (statement kept, proof by the kernel's achain_push); the rest of this file is new. *)
(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6, same loaded bytes): THE malloc(pod) STEP of the
   walk of LLVMFuzzerTestOneInput, C2 = 0x820c0 -> C3 = 0x820c4, i.e. lib/A/RPgHarn.v rh_S_C23_stmt at the concrete
   segments lib/A/Img0.v rsegs. Proves no function (kind: segment lemma).

   THE CODE. At C2 a0 = len + (len == 0) (rl_cut hi_L2: (LReg 10, XLenNZ)), and 8 <= len <= 5440 (rh_cut_C2), so
   a0 = len. 0x820c0 is `jal 0x52428`: ra := 0x820c4, pc := 0x52428, which is the runtime's malloc entry of image A
   (pc_wrap_malloc, the 4-byte jump to the wrapper). C3 = 0x820c4 is the return address.

   THE ROUTE.
   1. The engine runs the one `jal` from an entry state with every register an atom (RPgCfgChanges.cfg_entry, the
      one-word table c23_tbl at 0x820c0); it stops at 0x52428 with ra the literal 0x820c4 and every other register
      its own atom, and no byte written.
   2. The kernel's journal malloc rule YCbq.aj_malloc_at04 (the "04" form: it runs the call through amreal_SRr04,
      whose returning paths end with the model's flag true, and ml_malloc_ns gives a null result the flag false, so
      its post has 4096 <= res only) at the harness journal rh_j (STK = LLVMF_STK, sp0 = S,
      FP = [], own = [(3, pos)], k = 1), with o = R - S (R = e_R e the 32-aligned real-frame base, so o is 16-aligned,
      -432 <= o <= -416), the event and live-byte budgets from rh_base, and the caller chain from the harness entry:
      the entry's achain (afn_pre, ch = []) pushed with the frame record the prologue stored at S - 8 (ra) and S - 16
      (s0), which rh_kept carries (rl_c23_chain), s0 = S at C2 (rl_cut hi_L2: (LReg 8, XS)).
   3. The rule's post gives rh_at_C3: the journal at two events, a0 = pod >= 4096, the callee-saved registers of
      C2 kept (the `jal` changes only ra), frames kept, the block appended, acall_kept at [R - ASTACK, R).

   SECTION HYPOTHESES (each is what the harness level supplies):
     AMALLOC     amalloc_realizes rsegs B             the runtime's malloc against the model
     errno_low   api_env rsegs B                      errno cell and the allocator's one-entry traces
     ML          model_laws (as_universe B)           the allocator model's laws
     HPCM        pc_wrap_malloc (as_code B) = 0x52428 the code record: malloc's entry is the jal's target
     HSTK_C23    ASTACK + RH_RSZ + 16 <= LLVMF_STK    the call's stack budget: ASTACK - o <= LLVMF_STK
     HEV_C23     2 <= EV_LIB                          room for this event: st_nev < EV_MAX
     HLIVE_C23   Layout.PP_SIZE + 5440 <= LIVE_LIB    room for pod after pp: blocks_bytes + len <= LIVE_MAX
     HTRACE_C23  the malloc trace at ra = 0x820c4 is in the universe (scene's rt_trace_in_stmt, one site).
   AXIOMS (Print Assumptions below): the primitive int / string / array axioms and Stdlib's
   functional_extensionality_dep, which the kernel's engine runner YCbq.SRr_run_tok_AJ uses. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YO0f YG0s YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgHarn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgCfgChanges RPgSteps.
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
End h.

(* the side goals of a register a run did not touch (clob = [ra]) *)
Ltac c23_rk :=
first
[ solve [vm_compute; let Hx := fresh "Hx" in intros Hx; discriminate Hx]
| solve [let Hx := fresh "Hx" in intros [Hx|[]]; apply (f_equal (@bv_unsigned 5)) in Hx; vm_compute in Hx; discriminate Hx] ].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* the caller chain the malloc call sees: the harness entry's own record (sp, ra, s0) when its frame is below the
   stack top (scene P_LLVMFuzzerTestOneInput_ctx.v rt_ch) *)
Definition rl_c23_ch (hx : rh_hcx rsegs) : list (Z * Z * Z) :=
if spZ (h_regs hx) + 16 <? ly_top (h_ly hx) then [(spZ (h_regs hx), raZ (h_regs hx), s0Z (h_regs hx))] else [].
Section d.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
Hypothesis AMALLOC : amalloc_realizes rsegs B.
Hypothesis errno_low : api_env rsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis HPCM : pc_wrap_malloc (as_code B) = 0x52428.
Hypothesis HSTK_C23 : ASTACK + RH_RSZ + 16 <= LLVMF_STK.
Hypothesis HEV_C23 : 2 <= EV_LIB.
Hypothesis HLIVE_C23 : Layout.PP_SIZE + 5440 <= LIVE_LIB.
Hypothesis HTRACE_C23 : forall (regsT : bvmap 5 word) (hx : rh_hcx rsegs),
raZ (h_regs hx) = RA_LLVMF -> raZ regsT = RH_C3 ->
In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT (rl_c23_ch hx)) (as_universe B).

Theorem rl_A_S_C23 : rh_S_C23_stmt rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof using AMALLOC errno_low ML HPCM HSTK_C23 HEV_C23 HLIVE_C23 HTRACE_C23.
intros hx pos e ly2 S2 W2 regs2 mem2 md2 HB HC.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof RPgCfgChanges.cfg_wx as Hwx. pose proof RPgCfgChanges.cfg_segs_low as Hsegs.
destruct HB as (HPRE & Hra0 & _ & _ & _ & _ & _ & _ & Hev0 & Hlive0 & _).
destruct HPRE as (HAR0 & Hraok0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
destruct Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HC as (HJ & Hperm & Hsp2 & Hgp2 & Htp2 & Hgeo & Hlen8 & Hcut & Hkept).
destruct Hgeo as (HeS & HeR & _).
unfold rh_j in HJ.
pose proof HJ as (_ & Hly & _ & _ & _ & _ & Hnev & _ & F1 & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _ & _ & _ & _).
pose proof HSTK_C23 as HSTK. unfold ASTACK, RH_RSZ in HSTK.
(* the geometry: S = 16 t, R = 32 q with S - 416 = 32 q + r, 0 <= r < 32 *)
rewrite HeS in HeR. unfold RH_RSZ in HeR.
pose proof (Z.div_mod (spZ (h_regs hx) - 0x1a0) 32 ltac:(lia)) as Dq.
pose proof (Z.mod_pos_bound (spZ (h_regs hx) - 0x1a0) 32 ltac:(lia)) as Bq.
pose proof (Z.div_mod (spZ (h_regs hx)) 16 ltac:(lia)) as D16. rewrite Hal16, Z.add_0_r in D16.
assert (HRb : alloc_ceiling + 16384 <= e_R e /\ e_R e + 416 <= spZ (h_regs hx) /\ spZ (h_regs hx) - e_R e <= 432) by lia.
assert (HR64 : 0 <= e_R e < 2 ^ 64) by zlia.
assert (HS64 : 0 <= spZ (h_regs hx) < 2 ^ 64) by zlia.
assert (HAL : (e_R e - spZ (h_regs hx)) mod 16 = 0).
{ replace (e_R e - spZ (h_regs hx)) with ((2 * ((spZ (h_regs hx) - 0x1a0) / 32) - spZ (h_regs hx) / 16) * 16) by lia.
  apply Z.mod_mul. lia. }
assert (HS8 : spZ (h_regs hx) mod 8 = 0).
{ replace (spZ (h_regs hx)) with ((2 * (spZ (h_regs hx) / 16)) * 8) by lia. apply Z.mod_mul. lia. }
(* the C2 values a0 = len and s0 = S *)
unfold rl_cut in Hcut. cbn [hi_L2 role_himg_A] in Hcut. unfold role_A_L23 in Hcut.
apply Forall_cons_iff in Hcut as [C10 Hcut]. apply Forall_cons_iff in Hcut as [C8 _].
cbn [fst snd rl_at rl_xv] in C10, C8.
replace (e_len e =? 0) with false in C10 by (symmetry; apply Z.eqb_neq; lia). rewrite Z.add_0_r in C10.
rewrite HeS in C8.
(* the frame record the prologue stored: ra at S - 8, s0 at S - 16 *)
unfold rh_kept, rh_cells, rh_saves_L in Hkept. cbn [seq map app] in Hkept.
apply Forall_cons_iff in Hkept as [K0 Hkept]. apply Forall_cons_iff in Hkept as [K1 _].
cbv beta in K0, K1. cbn [fst snd] in K0, K1.
pose proof (c23_rl_cell _ _ _ _ _ _ _ (u64_range _) K0) as W8.
pose proof (c23_rl_cell _ _ _ _ _ _ _ (u64_range _) K1) as W16.
cbn [rl_xv] in W8, W16. rewrite HeS in W8, W16.
assert (R8 : rdword (aview rsegs (w_H W2) mem2) (spZ (h_regs hx) - 8) = Some (raZ (h_regs hx))).
{ replace (spZ (h_regs hx) - 8) with (spZ (h_regs hx) + (-8 - 8 * Z.of_nat 0)) by lia. exact W8. }
assert (R16 : rdword (aview rsegs (w_H W2) mem2) (spZ (h_regs hx) - 16) = Some (s0Z (h_regs hx))).
{ replace (spZ (h_regs hx) - 16) with (spZ (h_regs hx) + (-8 - 8 * Z.of_nat 1)) by lia. exact W16. }
clear W8 W16 K0 K1.
(* 1. the `jal`: one engine step to 0x52428 *)
pose proof (RPgCfgChanges.cfg_entry RH_C2 W2 regs2 mem2 ltac:(unfold RH_C2; lia)) as HS.
assert (SHOK : sh_ok rsegs RPgCfgChanges.RTBx [] (Ereg regs2 RPgCfgChanges.rt_extra) (mrestrict (w_H W2) mem2)) by constructor.
assert (HAE : env_agree 32 (Ereg regs2 RPgCfgChanges.rt_extra) (Ereg regs2 RPgCfgChanges.rt_extra)) by apply env_agree_refl.
unfold cfg_at. change (w64 RH_C2) with (Z_to_bv 64 RH_C2).
aj_run_tok c23_tbl_ok HS HJ SHOK RPgCfgChanges.RTBspan; [awr_ok_tac |].
(* no byte written; every register but ra its own atom; ra the literal 0x820c4 *)
assert (Hm : forall x, ms_mem ms x = mem2 x).
{ intros x. apply HF. intros (rg & Hrg & _). exact Hrg. }
assert (RK : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r [Z_to_bv 5 1] -> getr (ms_regs ms) r = getr regs2 r).
{ eapply (RPgSteps.regs_kept_of_st_ok rsegs _ _ ms regs2 RPgCfgChanges.rt_extra (w_H W2) _ HS HAE). vm_compute. reflexivity. }
assert (HRA : getr (ms_regs ms) 1 = Z_to_bv 64 0x820c4).
{ rewrite (c23_getr_eq (ms_regs ms) 1 (Z_to_bv 5 1)) by reflexivity.
  lazymatch type of HS with st_ok _ ?E ?ss _ =>
    let e1 := eval vm_compute in (sr_get (ss_regs ss) (Z_to_bv 5 1)) in
    assert (R1 : getr (ms_regs ms) (Z_to_bv 5 1) = sv_denot E e1)
      by exact (st_ok_restrict_reg rsegs (w_H W2) E ss ms (Z_to_bv 5 1) HS) end.
  cbn [sv_denot] in R1. rewrite R1. reflexivity. }
(* 2. the call's premises *)
assert (HA10 : getr (ms_regs ms) 10 = w64 (e_len e)).
{ rewrite RK by c23_rk. rewrite (c23_getr_eq regs2 10 (Z_to_bv 5 10)) by reflexivity. exact C10. }
assert (HN : 0 <= e_len e < MALLOC_MAX) by (change MALLOC_MAX with 268435456; lia).
assert (HLV : blocks_bytes S2 + e_len e <= LIVE_MAX).
{ assert (EB : forall ly S, blocks_bytes S = bsum (ablocks B ly S)) by (intros; apply blocks_bytes_bsum).
  rewrite (EB ly2 S2), (bsum_perm _ _ Hperm), bsum_app, <- (EB (h_ly hx) (h_S hx)).
  change (bsum [(e_pp e, Layout.PP_SIZE)]) with (Layout.PP_SIZE + 0). lia. }
assert (HSP : spZ (ms_regs ms) = spZ (h_regs hx) + (e_R e - spZ (h_regs hx))).
{ unfold spZ at 1. rewrite RK by c23_rk. rewrite Hsp2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (HNEG : e_R e - spZ (h_regs hx) <= 0) by lia.
assert (HBUD : ASTACK - (e_R e - spZ (h_regs hx)) <= LLVMF_STK) by (unfold ASTACK; lia).
assert (HGP : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite RK by c23_rk; exact Hgp2).
assert (HTP : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite RK by c23_rk; exact Htp2).
assert (HRAOK : YK0s.ret_ok (Z_to_bv 64 0x820c4)) by (unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity).
assert (HEV : st_nev S2 < EV_MAX) by lia.
assert (HRAZ : raZ (ms_regs ms) = 0x820c4) by (unfold raZ; rewrite HRA; apply unsigned_lit_small; lia).
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
(* the machine state at 0x52428 = pc_wrap_malloc *)
pose proof (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl) as Ems.
rewrite Ems at 1.
lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?s)] =>
  replace (ss_pc s) with (pc_wrap_malloc (as_code B)) by (rewrite HPCM; vm_compute; reflexivity) end.
eapply SRr_mono.
{ exact (aj_malloc_at04 rsegs B LAWS Hsegs errno_low ML AMALLOC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    HJ HA10 HN HLV HSP HAL HNEG HBUD HGP HTP HRA HRAOK HEV HCH HTR). }
(* 3. the post at C3 *)
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & res & Ec3 & HJ3 & Hpres3 & H103 & Hfr3 & Hres & Hab3 & Hkept3).
unfold rh_at_C3. exists res, ly3, S3, regs3, mem3, md3.
split; [rewrite Ec3; reflexivity|].
split; [unfold rh_j; exact HJ3|].
split; [exact Hres|].
split; [exact H103|].
split.
{ intros r Hr. rewrite (Hpres3 r Hr). apply RK.
  - rewrite (c23_csaved r Hr). unfold acallee_saved in Hr. lia.
  - intros [Hx|[]]. apply (f_equal (@bv_unsigned 5)) in Hx. rewrite (c23_csaved r Hr) in Hx.
    change (bv_unsigned (Z_to_bv 5 1)) with 1 in Hx. unfold acallee_saved in Hr. lia. }
split; [exact Hfr3|].
split; [exact Hab3|].
replace (spZ (h_regs hx) + (e_R e - spZ (h_regs hx))) with (e_R e) in Hkept3 by lia.
exact (c23_acall_kept_mem B ly2 S2 W2 mem2 (ms_mem ms) W3 mem3 _ _ _ Hm Hkept3).
Qed.
(* inside the Section: the kernel's axioms and the Section hypotheses named in the header *)
Print Assumptions rl_A_S_C23.
End d.
End b.
Print Assumptions rl_A_S_C23.
