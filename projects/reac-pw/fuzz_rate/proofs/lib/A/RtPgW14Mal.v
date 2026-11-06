(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgRt.v at 6ebe35ba632; its rt_chain is ported here as rl_c23_chain (statement kept, proof by the kernel's achain_push); the rest of this file is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPostMal.v at f5c24e17b400 for reac-pw/fuzz_rate image A: its helpers (memories equal at every word, a cell as a word of the view, register names, the caller chain, acall_kept across equal memories) are kept with the prefix w14m_; the step is rate's malloc(buf) step C4 -> C6 (five instructions before the call, a continuation statement whose cut C6 is rebuilt here) in place of role's C2 -> C3. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): THE malloc(buf) STEP of the
   walk of LLVMFuzzerTestOneInput, C4 = 0x82e84 -> C6 = 0x82e98, i.e. lib/A/RtPgSeg.v rh_S_C46_stmt at the concrete
   segments of image A (the image module's loaded_segments). Proves no function (kind: segment lemma).

   THE CODE (C4 .. C6):
     0x82e84 ld s3,0x50(s1)      s3 = buflen (the real frame's cell R+0x50, hi_L4: (LCell XR 0x50, XBuflen))
     0x82e88 seqz s7,s3
     0x82e8c add s7,s3,s7        s7 = buflen + (buflen == 0) = rt_bl buflen
     0x82e90 mv a0,s7
     0x82e94 jal 0x52bb4         ra := 0x82e98 = C6; 0x52bb4 is the runtime's malloc entry of image A
                                 (pc_wrap_malloc, the 4-byte jump to the wrapper)
   No instrumented check, no store.

   THE ROUTE.
   1. The engine runs the five words (w14m_tbl) from an entry state with every register an atom and the real
      frame's cell R+0x50 as the one region (read only, at s1 = atom 9, its value the env slot 33 = buflen); it
      stops at 0x52bb4 with s3 = buflen, s7 = a0 = rt_bl buflen (checked over the 24 values of buflen), ra the literal
      0x82e98, every other register its own atom, and no byte written.
   2. The kernel's journal malloc rule YCbq.aj_malloc_at04 at the harness journal rh_j (STK = LLVMF_STK, sp0 = S,
      FP = [], own = [(3, pos)], k = 2), with o = R - S (R the 32-aligned real-frame base, so o is 16-aligned and
      -0x1f0 <= o <= -0x1e0), the event and live-byte budgets from rh_base (len <= 5440 from RtPgSiteA.rt_len_bounds
      and rh_hdr's len = rt_len rest), and the caller chain from the harness entry: the entry's achain (afn_pre,
      ch = []) pushed with the frame record the prologue stored at S - 8 (ra) and S - 16 (s0), which rh_kept carries
      (w14m_chain), s0 = S at C4 (hi_L4: (LReg 8, XS)).
   3. The rule's post gives rh_cut_C6 at e' = e with q_buf := res (w14m_eb; every other quantity as at C4) and the
      same float state: three events, the block (res, rt_bl buflen) appended (not among the entry's blocks: the
      kernel's block separation at the post state), a0 = res >= 4096, s0 s1 s3 s4 s7 kept by aregs_preserved, the
      real-frame cells R+0x18 / 0x78 / 0xc0 / 0x120 / 0x138 and the 13 saves at [S - 0x68, S) kept (acall_kept: at or
      above R, outside [R - ASTACK, R)), the frame's flag word F + 0x1f8 and its 56 shadow bytes kept (acall_kept's
      frame clause; the new block is disjoint from F by the post state's separation law and from F's shadow bytes,
      which lie in the shadow band, because a block lies in application memory). Then the rh_from_C6 hypothesis.

   SECTION HYPOTHESES (each is what the harness level supplies):
     AMALLOC     forall fy, amalloc_realizes (fx := fy) rsegs B   the runtime's malloc against the model, at every
                 float state: C4's float state fx4 is the one the parse returns (rh_from_C4 quantifies it)
     errno_low   api_env rsegs B                      errno cell and the allocator's one-entry traces
     ML          model_laws (as_universe B)           the allocator model's laws
     HPCM        pc_wrap_malloc (as_code B) = 0x52bb4 the code record: malloc's entry is the jal's target
     HSTK_C46    ASTACK + RS_RSZ + 16 <= LLVMF_STK    the call's stack budget: ASTACK - o <= LLVMF_STK
     HEV_C46     3 <= EV_LIB                          room for this event after two: st_nev < EV_MAX
     HLIVE_C46   Layout.PP_SIZE + 5440 + 23 <= LIVE_LIB  room for buf after pp and pod (len <= 5440, buf <= 23)
     HTRACE_C46  the malloc trace at ra = 0x82e98 is in the universe (role's HTRACE_C23 form, one site).
   AXIOMS (Print Assumptions below): the primitive int / string / array axioms and Stdlib's
   functional_extensionality_dep, which the kernel's engine runner uses. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YO0f YG0s YG0q YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgSeg RtPgMem RtPgSiteA.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RtPgSteps.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* image A's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.
(* the harness entry record's projections with the segment list implicit, as RtPgSeg's own text reads them *)
Local Arguments h_ly {_} _. Local Arguments h_S {_} _. Local Arguments h_W {_} _.
Local Arguments h_regs {_} _. Local Arguments h_mem {_} _. Local Arguments h_md {_} _.

(* ---- the five instruction words the engine runs: 0x82e84 .. 0x82e94 ---- *)
Definition w14m_tbl : ctable := build_table rsegs RS_C4 5 TEmpty.
Lemma w14m_tbl_ok : table_ok rsegs w14m_tbl.
Proof. apply build_table_ok0. unfold RS_C4. lia. Qed.
(* the engine's shadow base: env slot 32 (no instrumented check runs here); env slot 33 is buflen *)
Definition w14m_Bx : sv := SOff 32 0.
Definition w14m_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition w14m_extra (bl : Z) : list word := [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 bl].
(* the real frame at s1 = R (atom 9): [R, R + 0x58) known, nothing writable, the cell R+0x50 = env slot 33 *)
Definition w14m_cell : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 0x58 0 0 [YP09.mkChunk 0x50 (CVal 8 (SOff 33 0))].
Definition w14m_ss : sstate := mkSS RS_C4 sr_atoms [w14m_cell] None (mkFacts [] [] []).

(* the quantities at C6: those of C4 with buf := b *)
Definition w14m_eb (e : rt_renv) (b : Z) : rt_renv :=
  {| q_S := q_S e; q_R := q_R e; q_F := q_F e; q_pp := q_pp e; q_pod := q_pod e; q_buf := b; q_len := q_len e;
     q_fl := q_fl e; q_mask := q_mask e; q_buflen := q_buflen e; q_b3 := q_b3 e; q_b4 := q_b4 e; q_b5 := q_b5 e;
     q_b6 := q_b6 e; q_src := q_src e; q_left := q_left e |}.
Ltac w14m_red := cbn [fst snd rt_at rt_xv w14m_eb q_S q_R q_F q_pp q_pod q_buf q_len q_fl q_mask q_buflen q_b3 q_b4
  q_b5 q_b6 q_src q_left].

(* the caller chain the malloc call sees: the harness entry's own record (sp, ra, s0) when its frame is below the
   stack top *)
Definition w14m_ch (hx : rh_hcx rsegs) : list (Z * Z * Z) :=
if spZ (h_regs hx) + 16 <? ly_top (h_ly hx) then [(spZ (h_regs hx), raZ (h_regs hx), s0Z (h_regs hx))] else [].

(* the 24 values of buflen (byte 2 mod 24) *)
Lemma w14m_cases24 : forall b, 0 <= b < 24 ->
b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7 \/ b = 8 \/ b = 9 \/ b = 10 \/ b = 11 \/
b = 12 \/ b = 13 \/ b = 14 \/ b = 15 \/ b = 16 \/ b = 17 \/ b = 18 \/ b = 19 \/ b = 20 \/ b = 21 \/ b = 22 \/ b = 23.
Proof. intros b Hb. lia. Qed.

(* the last two entries of a pairwise list are related *)
Lemma w14m_pw_last2 : forall {X : Type} (R : X -> X -> Prop) l x y, pairwise R (l ++ [x; y]) -> R x y.
Proof.
intros X R l x y. induction l as [|z l IH]; cbn [app pairwise]; intros H.
- destruct H as [H _]. exact (Forall_inv H).
- exact (IH (proj2 H)).
Qed.

(* ---- register names: a literal and Z_to_bv 5 of its number name the same register ---- *)
Lemma w14m_getr_eq : forall regs (b b' : bv 5), bv_unsigned b = bv_unsigned b' -> getr regs b = getr regs b'.
Proof. intros regs b b' E. apply bv_eq in E. subst b'. reflexivity. Qed.

(* the side goals of a register the run did not touch (clob = [ra; a0; s3; s7]) *)
Ltac w14m_rk :=
first
[ solve [vm_compute; let Hx := fresh "Hx" in intros Hx; discriminate Hx]
| solve [let Hx := fresh "Hx" in intros Hx;
         repeat (destruct Hx as [Hx|Hx]; [apply (f_equal (@bv_unsigned 5)) in Hx; vm_compute in Hx; discriminate Hx|]);
         destruct Hx] ].

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- memories equal at every word give the same view and words ---- *)
Lemma w14m_aview_mem : forall H (m m' : word -> option byte), (forall x, m' x = m x) ->
forall a, aview rsegs H m' a = aview rsegs H m a.
Proof. intros H m m' Hm a. unfold aview, mbyte, mrestrict. cbv beta. rewrite Hm. reflexivity. Qed.
Lemma w14m_rdword_mem : forall H (m m' : word -> option byte) a, (forall x, m' x = m x) ->
rdword (aview rsegs H m') a = rdword (aview rsegs H m) a.
Proof. intros H m m' a Hm. apply rdword_ext. intros k _. apply w14m_aview_mem. exact Hm. Qed.

(* ---- an 8-byte cell as a word of the view (the converse of YCbq.val_mem_of_rdword) ---- *)
Lemma w14m_rdword_of_val_mem : forall H mem a v, 0 <= v < 2 ^ 64 ->
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
(* a cell fact of RtPgBase as a word of the view *)
Lemma w14m_rt_cell : forall H mem regs e b o v, 0 <= v < 2 ^ 64 ->
rt_at rsegs H mem regs e (LCell b o) v -> rdword (aview rsegs H mem) (rt_xv e b + o) = Some v.
Proof.
intros H mem regs e b o v Hv Hc. cbn [rt_at] in Hc. rewrite Z.mod_small in Hc by exact Hv.
apply w14m_rdword_of_val_mem; assumption.
Qed.

(* ---- the caller chain at a call from the harness frame [knock APgRt.v rt_chain, role RPgPostMal.v rl_c23_chain] ---- *)
Lemma w14m_chain : forall ly (rd rd' : reader) (regs : bvmap 5 word) sp',
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

(* ---- a cut fact over cells of a list carried to other quantities and another memory ---- *)
Lemma w14m_kept_cells : forall H mem H' mem' regs regs' e e' (L : list (rt_loc * Z)),
(forall f, In f L -> exists b o, fst f = LCell b o /\ rt_xv e' b = rt_xv e b /\
  forall v, val_mem rsegs (mrestrict H mem) (rt_xv e b + o) 8 v -> val_mem rsegs (mrestrict H' mem') (rt_xv e b + o) 8 v) ->
Forall (fun f => rt_at rsegs H mem regs e (fst f) (snd f)) L ->
Forall (fun f => rt_at rsegs H' mem' regs' e' (fst f) (snd f)) L.
Proof.
intros H mem H' mem' regs regs' e e' L HL HF. rewrite Forall_forall in *. intros f Hf.
destruct (HL f Hf) as (b & o & Ef & Eb & Hk). specialize (HF f Hf). rewrite Ef in HF |- *. cbn [rt_at] in HF |- *.
rewrite Eb. apply Hk. exact HF.
Qed.

(* ---- the shadow bytes of a 32-aligned 512-byte frame below the allocator's ceiling are not in a block of the
   application memory ---- *)
Lemma w14m_sh_not_blk : forall F p n i, F mod 32 = 0 -> 0 <= F -> F + 512 <= alloc_ceiling -> in_app p n ->
0 <= i < 64 -> ~ (p <= shadow_addr F + i < p + n).
Proof.
intros F p n i H32 HF0 HFc Happ Hi.
pose proof (RtPgSteps.rts_fsh_of F (8 * i) H32 ltac:(lia)) as E.
replace (8 * i / 8) with i in E by (rewrite Z.mul_comm, Z.div_mul; lia).
rewrite <- E. apply rtm_shadow_not_app; [|exact Happ].
pose proof asan_consts as (C1 & _ & _ & C4 & _). lia.
Qed.

(* ---- the entry state of the run at C4: every register its own atom, the cell R+0x50 as the one region ---- *)
Lemma w14m_entry : forall (W : world rsegs) regs2 mem2 R bl,
getr regs2 (Z_to_bv 5 9) = w64 R -> 0 <= R -> R + 0x58 <= 2 ^ 64 -> 0 <= bl < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x50) 8 bl ->
st_ok rsegs (Ereg regs2 (w14m_extra bl)) w14m_ss
  (restrict (w_H W) (mkst regs2 (Z_to_bv 64 RS_C4) mem2 (seg_rom rsegs))).
Proof.
intros W regs2 mem2 R bl H9 HR0 HR1 Hbl Hv.
rewrite restrict_mkst_fx. unfold w14m_ss.
assert (E9 : bv_unsigned (ew (Ereg regs2 (w14m_extra bl)) 9) = R).
{ rewrite (ew_Ereg_nat regs2 _ 9 (Z_to_bv 5 9) eq_refl). rewrite H9. unfold w64. apply unsigned_lit_small. lia. }
apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold w14m_cell.
  apply (rtm_ro_region rsegs _ _ _ 9 R 0 0x58); [exact E9 | lia | lia |].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val rsegs _ _ R 0x50 8 (SOff 33 0) bl); [| cbn; lia | cbn; lia | exact Hv].
  apply bv_eq. rewrite denot_SOff, Z.add_0_r. change 33%nat with (32 + 1)%nat. rewrite ew_Ereg_extra.
  cbn [nth w14m_extra]. rewrite unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
- cbn. tauto.
- repeat split.
Qed.

Lemma w14m_acall_kept_mem : forall B ly S W (m m' : word -> option byte) W3 m3 slo shi (E : Z -> Prop),
(forall x, m' x = m x) ->
acall_kept rsegs B ly S W m' W3 m3 slo shi E -> acall_kept rsegs B ly S W m W3 m3 slo shi E.
Proof.
intros B ly S W m m' W3 m3 slo shi E Hm (K1 & K2 & K3 & K4 & K5 & K6).
pose proof (w14m_aview_mem (w_H W) m m' Hm) as Hv.
split; [intros a Ha Hs; rewrite <- Hv; exact (K1 a Ha Hs)|].
split; [intros b n i Hb Hi HE; rewrite <- Hv; exact (K2 b n i Hb Hi HE)|].
split; [intros a Ha Ho He; rewrite <- Hv; exact (K3 a Ha Ho He)|].
split; [intros cid pos a Hf Hr HE; rewrite <- Hv; exact (K4 cid pos a Hf Hr HE)|].
split; [intros a Ha Hs Hp; apply (K5 a Ha Hs); destruct Hp as [Hh [b Hb]]; split; [exact Hh|]; exists b; rewrite Hm; exact Hb|].
exact K6.
Qed.
End h.

(* ======================================= the step, at the section's float state ======================================= *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
Hypothesis AMALLOC : forall fy : YK11.FPState, amalloc_realizes (fx := fy) rsegs B.
Hypothesis errno_low : api_env rsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis HPCM : pc_wrap_malloc (as_code B) = 0x52bb4.
Hypothesis HSTK_C46 : ASTACK + RS_RSZ + 16 <= LLVMF_STK.
Hypothesis HEV_C46 : 3 <= EV_LIB.
Hypothesis HLIVE_C46 : Layout.PP_SIZE + 5440 + 23 <= LIVE_LIB.
Hypothesis HTRACE_C46 : forall (regsT : bvmap 5 word) (hx : rh_hcx rsegs),
raZ (h_regs hx) = RA_LLVMF -> raZ regsT = RS_C6 ->
In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT (w14m_ch hx)) (as_universe B).

Lemma w14m_step : forall (hx : rh_hcx rsegs) POST,
rh_base rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx ->
rh_from_C6 rsegs B LLVMF_STK hx POST ->
forall pos e rest ly2 S2 W2 regs2 mem2 md2,
rh_cut_C4 rsegs B LLVMF_STK hx fx pos e rest ly2 S2 W2 regs2 mem2 md2 ->
SRr rsegs W2 (cfg_at rsegs RS_C4 regs2 mem2 md2) POST.
Proof using AMALLOC errno_low ML HPCM HSTK_C46 HEV_C46 HLIVE_C46 HTRACE_C46.
intros hx POST HB HK pos e rest ly2 S2 W2 regs2 mem2 md2 HC.
pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof RtPgSteps.rts_wx as Hwx. pose proof RtPgSteps.rts_segs_low as Hsegs.
destruct HB as (HPRE & Hra0 & _ & _ & _ & _ & _ & _ & Hev0 & Hlive0 & _).
destruct HPRE as (HAR0 & Hraok0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
destruct Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HC as (HCm & Hpp0 & Hpod0 & Hfsh & Hfrm).
destruct HCm as (HJ & Hfr2 & Hperm & Hfresh & Hsp2 & Hgp2 & Htp2 & Hgeo & Hhdr & Hhok & Hcut & Hkept).
pose proof Hgeo as (HeS & HeR & HeF).
pose proof Hhdr as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HlenE).
pose proof Hhok as (_ & _ & Hbuf24 & _).
unfold rh_j in HJ.
pose proof HJ as (HAR2 & Hly & _ & _ & _ & _ & Hnev & _ & F1 & _).
destruct Hly as (_ & _ & _ & _ & _ & EF2 & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _ & _ & C4 & _).
pose proof HSTK_C46 as HSTK. unfold ASTACK, RS_RSZ in HSTK.
pose proof (rt_len_bounds rest) as Hlenb. rewrite <- HlenE in Hlenb.
pose proof (rate_A_site_malloc_buf e Hhok) as (_ & Hbl & Hblm). cbn [rt_xv] in Hblm.
(* the geometry: S = 16 t, R = 32 q with S - 480 = 32 q + r, 0 <= r < 32 *)
assert (HeR' : q_R e = 32 * ((spZ (h_regs hx) - 0x1e0) / 32)) by (rewrite HeR, HeS; reflexivity).
pose proof (Z.div_mod (spZ (h_regs hx) - 0x1e0) 32 ltac:(lia)) as Dq.
pose proof (Z.mod_pos_bound (spZ (h_regs hx) - 0x1e0) 32 ltac:(lia)) as Bq.
pose proof (Z.div_mod (spZ (h_regs hx)) 16 ltac:(lia)) as D16. rewrite Hal16, Z.add_0_r in D16.
assert (HRb : alloc_ceiling + 16384 <= q_R e /\ q_R e + 0x1e0 <= spZ (h_regs hx) /\ spZ (h_regs hx) - q_R e <= 0x1f0)
by lia.
assert (HR64 : 0 <= q_R e /\ spZ (h_regs hx) <= 2 ^ 47) by lia.
assert (HAL : (q_R e - spZ (h_regs hx)) mod 16 = 0).
{ replace (q_R e - spZ (h_regs hx)) with ((2 * ((spZ (h_regs hx) - 0x1e0) / 32) - spZ (h_regs hx) / 16) * 16) by lia.
  apply Z.mod_mul. lia. }
assert (HS8 : spZ (h_regs hx) mod 8 = 0).
{ replace (spZ (h_regs hx)) with ((2 * (spZ (h_regs hx) / 16)) * 8) by lia. apply Z.mod_mul. lia. }
(* the C4 values *)
unfold rt_cut in Hcut. cbn [hi_L4 rate_himg_A] in Hcut.
apply Forall_cons_iff in Hcut as [C8 Hcut]. apply Forall_cons_iff in Hcut as [C9 Hcut].
apply Forall_cons_iff in Hcut as [C20 Hcut]. apply Forall_cons_iff in Hcut as [M18 Hcut].
apply Forall_cons_iff in Hcut as [M50 Hcut]. apply Forall_cons_iff in Hcut as [M78 Hcut].
apply Forall_cons_iff in Hcut as [Mc0 Hcut]. apply Forall_cons_iff in Hcut as [M120 Hcut].
apply Forall_cons_iff in Hcut as [M138 _].
cbn [fst snd rt_at rt_xv] in C8, C9, C20, M18, M50, M78, Mc0, M120, M138.
rewrite (Z.mod_small (q_buflen e)) in M50 by lia.
(* the frame record the prologue stored: ra at S - 8, s0 at S - 16 *)
pose proof Hkept as Hkept0.
unfold rh_kept, rh_cells, rh_saves_L in Hkept. cbn [seq map app] in Hkept.
apply Forall_cons_iff in Hkept as [K0 Hkept]. apply Forall_cons_iff in Hkept as [K1 _].
cbv beta in K0, K1. cbn [fst snd] in K0, K1.
pose proof (w14m_rt_cell _ _ _ _ _ _ _ (u64_range _) K0) as W8.
pose proof (w14m_rt_cell _ _ _ _ _ _ _ (u64_range _) K1) as W16.
cbn [rt_xv] in W8, W16. rewrite HeS in W8, W16.
assert (R8 : rdword (aview rsegs (w_H W2) mem2) (spZ (h_regs hx) - 8) = Some (raZ (h_regs hx))).
{ replace (spZ (h_regs hx) - 8) with (spZ (h_regs hx) + (-8 - 8 * Z.of_nat 0)) by lia. exact W8. }
assert (R16 : rdword (aview rsegs (w_H W2) mem2) (spZ (h_regs hx) - 16) = Some (s0Z (h_regs hx))).
{ replace (spZ (h_regs hx) - 16) with (spZ (h_regs hx) + (-8 - 8 * Z.of_nat 1)) by lia. exact W16. }
clear W8 W16 K0 K1.
(* 1. the five words: an engine run to 0x52bb4 *)
pose proof (w14m_entry W2 regs2 mem2 (q_R e) (q_buflen e) C9 ltac:(lia) ltac:(lia) ltac:(lia) M50) as HS.
remember (Ereg regs2 (w14m_extra (q_buflen e))) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs2 (w14m_extra (q_buflen e))) E) by (subst E; apply env_agree_refl).
assert (E33 : ew E 33 = Z_to_bv 64 (q_buflen e))
by (subst E; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (SHOK : sh_ok rsegs w14m_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
unfold cfg_at. change (w64 RS_C4) with (Z_to_bv 64 RS_C4).
aj_run_tok w14m_tbl_ok HS HJ SHOK w14m_Bspan; [awr_ok_tac |].
(* no byte written; every register but ra, a0, s3, s7 its own atom *)
assert (Hm : forall x, ms_mem ms x = mem2 x).
{ intros x. apply HF. intros (rg & Hrg & Ha). cbn [w14m_ss ss_mem In] in Hrg.
  destruct Hrg as [<- | []]. cbn [w14m_cell YP09.r_wlo YP09.r_whi] in Ha. lia. }
assert (RK : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r [Z_to_bv 5 1; Z_to_bv 5 10; Z_to_bv 5 19; Z_to_bv 5 23] ->
  getr (ms_regs ms) r = getr regs2 r).
{ eapply (RtPgSteps.regs_kept_of_st_ok rsegs _ _ ms regs2 (w14m_extra (q_buflen e)) (w_H W2) _ HS HAE).
  vm_compute. reflexivity. }
let R := fresh "R19" in rreg HS (19%bv : bv 5) R.
let R := fresh "R23" in rreg HS (23%bv : bv 5) R.
let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
assert (V19 : getr (ms_regs ms) (Z_to_bv 5 19) = w64 (q_buflen e)).
{ etransitivity; [exact R19|]. rewrite ?E33. reflexivity. }
assert (V23 : getr (ms_regs ms) (Z_to_bv 5 23) = w64 (rt_bl (q_buflen e))).
{ etransitivity; [exact R23|]. rewrite ?E33. pose proof (w14m_cases24 (q_buflen e) ltac:(lia)) as Hc.
  repeat (destruct Hc as [Hc|Hc]; [rewrite Hc; vm_compute; reflexivity|]). rewrite Hc; vm_compute; reflexivity. }
assert (V10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (rt_bl (q_buflen e))).
{ etransitivity; [exact R10|]. rewrite ?E33. pose proof (w14m_cases24 (q_buflen e) ltac:(lia)) as Hc.
  repeat (destruct Hc as [Hc|Hc]; [rewrite Hc; vm_compute; reflexivity|]). rewrite Hc; vm_compute; reflexivity. }
assert (V1 : getr (ms_regs ms) 1 = Z_to_bv 64 0x82e98) by (etransitivity; [exact R1|]; reflexivity).
(* 2. the call's premises *)
assert (HA10 : getr (ms_regs ms) 10 = w64 (rt_bl (q_buflen e))) by exact V10.
assert (HLV : blocks_bytes S2 + rt_bl (q_buflen e) <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ Hperm), bsum_app, <- (blocks_bytes_bsum B (h_ly hx) (h_S hx)).
  cbn [bsum fold_right fst snd]. lia. }
assert (HSP : spZ (ms_regs ms) = spZ (h_regs hx) + (q_R e - spZ (h_regs hx))).
{ unfold spZ at 1. rewrite RK by w14m_rk. rewrite Hsp2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (HNEG : q_R e - spZ (h_regs hx) <= 0) by lia.
assert (HBUD : ASTACK - (q_R e - spZ (h_regs hx)) <= LLVMF_STK) by (unfold ASTACK; lia).
assert (HGP : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite RK by w14m_rk; exact Hgp2).
assert (HTP : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite RK by w14m_rk; exact Htp2).
assert (HRAOK : YK0s.ret_ok (Z_to_bv 64 0x82e98)) by (unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity).
assert (HEV : st_nev S2 < EV_MAX) by lia.
assert (HRAZ : raZ (ms_regs ms) = 0x82e98) by (unfold raZ; rewrite V1; apply unsigned_lit_small; lia).
assert (HCH : chain_pre ly2 (aview rsegs (w_H W2) (ms_mem ms)) (ms_regs ms) (w14m_ch hx)).
{ apply (achain_chain_pre ly2 _ (q_R e) (spZ (h_regs hx))).
  - apply (achain_ly_top (h_ly hx) ly2 _ _ _ _ Etop). unfold w14m_ch.
    apply (w14m_chain (h_ly hx) (aview rsegs (w_H (h_W hx)) (h_mem hx))).
    + exact Hch0.
    + lia.
    + intros a Ha. rewrite (w14m_aview_mem (w_H W2) mem2 (ms_mem ms) Hm). apply F1; lia.
    + rewrite (w14m_rdword_mem (w_H W2) mem2 (ms_mem ms) _ Hm). exact R8.
    + rewrite (w14m_rdword_mem (w_H W2) mem2 (ms_mem ms) _ Hm). exact R16.
    + exact Hra40.
    + lia.
    + exact HS8.
    + lia.
  - rewrite HSP. lia.
  - unfold s0Z. rewrite RK by w14m_rk. rewrite (w14m_getr_eq regs2 8 (Z_to_bv 5 8)) by reflexivity.
    rewrite C8, HeS. unfold w64. apply unsigned_lit_small. lia.
  - rewrite HRAZ. lia. }
assert (HTR : In (call_trace0 (pc_malloc_ra0 (as_code B)) (ms_regs ms) (w14m_ch hx)) (as_universe B)).
{ apply HTRACE_C46; [exact Hra0 | rewrite HRAZ; reflexivity]. }
(* the machine state at 0x52bb4 = pc_wrap_malloc *)
lazymatch goal with HSx : st_ok _ ?Ex ?ssx (restrict ?Hx ms) |- _ =>
  pose proof (st_ok_restrict_mkst rsegs Hx Ex ssx ms HSx eq_refl) as Ems end.
rewrite Ems at 1.
lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?s)] =>
  replace (ss_pc s) with (pc_wrap_malloc (as_code B)) by (rewrite HPCM; vm_compute; reflexivity) end.
eapply SRr_bind.
{ exact (aj_malloc_at04 rsegs B LAWS Hsegs errno_low ML (AMALLOC fx) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    HJ HA10 Hblm HLV HSP HAL HNEG HBUD HGP HTP V1 HRAOK HEV HCH HTR). }
(* 3. the cut C6 *)
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & res & Ec3 & HJ3 & Hpres3 & H103 & Hfr3 & Hres & Hab3 & Hkept3).
subst c3.
change (SRr rsegs W3 (cfg_at rsegs RS_C6 regs3 mem3 md3) POST).
apply (HK fx pos (w14m_eb e res) rest ly3 S3 W3 regs3 mem3 md3).
pose proof HJ3 as (HAR3 & Hly3 & _).
destruct Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
assert (EFa2 : frame_addr ly2 3 pos = q_F e) by (rewrite HeF; unfold frame_addr, RS_CID; rewrite EF2; reflexivity).
assert (EFa3 : frame_addr ly3 3 pos = q_F e) by (rewrite HeF; unfold frame_addr, RS_CID; rewrite EF3; reflexivity).
assert (Hin2 : In (3, pos) (frames S2)) by (rewrite Hfr2; left; reflexivity).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 3 pos HAR2 Hin2) as (F32 & _).
destruct (al_sep _ _ LAWS ly2 S2 W2 mem2 md2 HAR2) as [_ Fsep].
pose proof (proj1 (Forall_forall _ _) Fsep (3, pos) Hin2) as (F4096 & Fceil). cbn [fst snd] in F4096, Fceil.
rewrite EFa2 in F32, F4096, Fceil. change (fs_frame_bytes 3) with 512 in Fceil.
assert (Hreq : req_size (rt_bl (q_buflen e)) = rt_bl (q_buflen e))
by (unfold req_size; destruct (Z.eqb_spec (rt_bl (q_buflen e)) 0); lia).
(* the new block: in application memory, disjoint from the frame for locals *)
assert (Hnew : In (res, rt_bl (q_buflen e)) (ablocks B ly3 S3))
by (rewrite Hab3; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 res _ HAR3 Hnew) as (_ & _ & _ & Hrapp & _).
destruct (al_sep _ _ LAWS ly3 S3 W3 mem3 md3 HAR3) as [Hsep3 _].
rewrite Hab3, Hfr3, Hfr2, map_app, <- app_assoc in Hsep3. cbn [map app fst snd] in Hsep3.
apply w14m_pw_last2 in Hsep3. unfold zdisjoint in Hsep3. cbn [fst snd] in Hsep3. unfold RS_CID in Hsep3.
rewrite EFa3 in Hsep3. change (fs_frame_bytes 3) with 512 in Hsep3. rewrite Hreq in Hsep3, Hrapp.
(* what the call kept *)
destruct Hkept3 as (KA0 & _ & _ & KF0 & _ & _).
assert (KA : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (q_R e - ASTACK <= a < q_R e) ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha Hs. rewrite (KA0 a Ha ltac:(lia)). apply (w14m_aview_mem (w_H W2) mem2 (ms_mem ms) Hm). }
assert (KF : forall a, (q_F e <= a < q_F e + 512 \/ shadow_addr (q_F e) <= a < shadow_addr (q_F e) + 64) ->
  ~ (res <= a < res + rt_bl (q_buflen e)) -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha Hn. rewrite (KF0 3 pos a Hin2).
  - apply (w14m_aview_mem (w_H W2) mem2 (ms_mem ms) Hm).
  - unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFa2. change (fs_frame_bytes 3) with 512.
    change (512 / 8) with 64. exact Ha.
  - cbv beta. rewrite Hreq. exact Hn. }
assert (KC : forall off v, 0 <= off <= 0x138 ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (q_R e + off) 8 v -> val_mem rsegs (mrestrict (w_H W3) mem3) (q_R e + off) 8 v).
{ intros off v Ho Hv. apply (val_mem_kept rsegs (w_H W2) (w_H W3) mem2 mem3 _ 8 v); [|exact Hv].
  intros k Hk. change (Z.of_nat 8) with 8 in Hk. apply KA; [lia | lia]. }
assert (KS : forall o v, -0x68 <= o <= -8 ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (q_S e + o) 8 v -> val_mem rsegs (mrestrict (w_H W3) mem3) (q_S e + o) 8 v).
{ intros o v Ho Hv. apply (val_mem_kept rsegs (w_H W2) (w_H W3) mem2 mem3 _ 8 v); [|exact Hv].
  intros k Hk. change (Z.of_nat 8) with 8 in Hk. apply KA; [lia | lia]. }
assert (KFl : forall v, val_mem rsegs (mrestrict (w_H W2) mem2) (q_F e + 0x1f8) 8 v ->
  val_mem rsegs (mrestrict (w_H W3) mem3) (q_F e + 0x1f8) 8 v).
{ intros v Hv. apply (val_mem_kept rsegs (w_H W2) (w_H W3) mem2 mem3 _ 8 v); [|exact Hv].
  intros k Hk. change (Z.of_nat 8) with 8 in Hk. apply KF; [left; lia | lia]. }
assert (KR : forall r, acallee_saved r -> ~ In (Z_to_bv 5 r) [Z_to_bv 5 1; Z_to_bv 5 10; Z_to_bv 5 19; Z_to_bv 5 23] ->
  getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)).
{ intros r Hr Hn. rewrite (Hpres3 r Hr). apply RK; [|exact Hn].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small; unfold acallee_saved in Hr; lia. }
unfold rh_cut_C6, rh_common.
split.
{ split; [unfold rh_j; exact HJ3|].
  split; [rewrite Hfr3; exact Hfr2|].
  split.
  { w14m_red. rewrite Hab3.
    replace (ablocks B (h_ly hx) (h_S hx) ++ [(q_pp e, Layout.PP_SIZE); (q_pod e, q_len e); (res, rt_bl (q_buflen e))])
      with ((ablocks B (h_ly hx) (h_S hx) ++ [(q_pp e, Layout.PP_SIZE); (q_pod e, q_len e)]) ++ [(res, rt_bl (q_buflen e))])
      by (rewrite <- app_assoc; reflexivity).
    apply Permutation_app_tail. exact Hperm. }
  split.
  { w14m_red.
    change [(q_pp e, Layout.PP_SIZE); (q_pod e, q_len e); (res, rt_bl (q_buflen e))]
      with ([(q_pp e, Layout.PP_SIZE); (q_pod e, q_len e)] ++ [(res, rt_bl (q_buflen e))]).
    apply Forall_app. split; [exact Hfresh|]. apply Forall_cons; [|apply Forall_nil].
    intros Hin.
    assert (Hin2' : In (res, rt_bl (q_buflen e)) (ablocks B ly2 S2)).
    { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. exact Hin. }
    apply in_split in Hin2' as (l1 & l2 & El).
    pose proof (sep_blocks_pos rsegs B LAWS ly3 S3 W3 mem3 md3 (res, rt_bl (q_buflen e)) (res, rt_bl (q_buflen e))
      l1 l2 [] HAR3 ltac:(rewrite Hab3, El, <- app_assoc; reflexivity)) as Hd.
    unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite Hreq in Hd. lia. }
  split.
  { w14m_red. assert (Q : getr regs3 (Z_to_bv 5 2) = w64 (q_R e))
      by (rewrite (KR 2 ltac:(unfold acallee_saved; lia)) by w14m_rk; exact Hsp2).
    exact Q. }
  split.
  { assert (Q : getr regs3 (Z_to_bv 5 3) = w64 (as_gp B))
      by (rewrite (KR 3 ltac:(unfold acallee_saved; lia)) by w14m_rk; exact Hgp2).
    exact Q. }
  split.
  { assert (Q : getr regs3 (Z_to_bv 5 4) = w64 (as_tp B))
      by (rewrite (KR 4 ltac:(unfold acallee_saved; lia)) by w14m_rk; exact Htp2).
    exact Q. }
  split; [unfold rh_geo; w14m_red; exact Hgeo|].
  split; [unfold rh_hdr; w14m_red; exact Hhdr|].
  split; [unfold rt_hdr_ok; w14m_red; exact Hhok|].
  split.
  { unfold rt_cut. cbn [hi_L6 rate_himg_A rate_A_L56 rate_A_L56_tl].
    apply Forall_cons; [w14m_red; exact H103|].
    apply Forall_cons; [w14m_red; rewrite (KR 8 ltac:(unfold acallee_saved; lia)) by w14m_rk; exact C8|].
    apply Forall_cons; [w14m_red; rewrite (KR 9 ltac:(unfold acallee_saved; lia)) by w14m_rk; exact C9|].
    apply Forall_cons; [w14m_red; rewrite (Hpres3 19 ltac:(unfold acallee_saved; lia)); exact V19|].
    apply Forall_cons; [w14m_red; rewrite (KR 20 ltac:(unfold acallee_saved; lia)) by w14m_rk; exact C20|].
    apply Forall_cons; [w14m_red; rewrite (Hpres3 23 ltac:(unfold acallee_saved; lia)); exact V23|].
    apply Forall_cons; [w14m_red; apply KC; [lia | exact M18]|].
    apply Forall_cons; [w14m_red; apply KC; [lia | exact M78]|].
    apply Forall_cons; [w14m_red; apply KC; [lia | exact Mc0]|].
    apply Forall_cons; [w14m_red; apply KC; [lia | exact M120]|].
    apply Forall_cons; [w14m_red; apply KC; [lia | exact M138]|].
    apply Forall_nil. }
  { apply (w14m_kept_cells (w_H W2) mem2 (w_H W3) mem3 regs2 regs3 e (w14m_eb e res)); [|exact Hkept0].
    intros f Hf. unfold rh_cells, rh_saves_L in Hf. apply in_app_or in Hf. destruct Hf as [Hf|Hf].
    - apply in_map_iff in Hf as (j & <- & Hj). apply in_seq in Hj.
      exists XS, (-8 - 8 * Z.of_nat j). split; [reflexivity|]. split; [reflexivity|].
      intros v Hv. cbn [rt_xv] in Hv |- *. apply KS; [lia | exact Hv].
    - destruct Hf as [<- | []]. exists XF, 0x1f8. split; [reflexivity|]. split; [reflexivity|].
      intros v Hv. cbn [rt_xv] in Hv |- *. apply KFl. exact Hv. } }
split; [w14m_red; exact Hpp0|].
split; [w14m_red; exact Hpod0|].
split; [w14m_red; lia|].
split; [|exact Hfrm].
w14m_red. apply (rtm_fsh_kept rsegs (w_H W2) mem2 (w_H W3) mem3 (q_F e) rs_PB Hfsh).
intros i Hi. assert (Hi' : 0 <= i < 56) by (unfold rs_PB in Hi; rewrite (proj2 rate_A_sh_len) in Hi; exact Hi).
apply KF; [right; lia|].
apply (w14m_sh_not_blk (q_F e) res (rt_bl (q_buflen e)) i F32 ltac:(lia) Fceil Hrapp ltac:(lia)).
Qed.
End w.

(* ======================================= the statement ======================================= *)
Section m. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
Hypothesis AMALLOC : forall fy : YK11.FPState, amalloc_realizes (fx := fy) rsegs B.
Hypothesis errno_low : api_env rsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis HPCM : pc_wrap_malloc (as_code B) = 0x52bb4.
Hypothesis HSTK_C46 : ASTACK + RS_RSZ + 16 <= LLVMF_STK.
Hypothesis HEV_C46 : 3 <= EV_LIB.
Hypothesis HLIVE_C46 : Layout.PP_SIZE + 5440 + 23 <= LIVE_LIB.
Hypothesis HTRACE_C46 : forall (regsT : bvmap 5 word) (hx : rh_hcx rsegs),
raZ (h_regs hx) = RA_LLVMF -> raZ regsT = RS_C6 ->
In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT (w14m_ch hx)) (as_universe B).

Theorem rt_w14_S_C46_A : rh_S_C46_stmt rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof using AMALLOC errno_low ML HPCM HSTK_C46 HEV_C46 HLIVE_C46 HTRACE_C46.
intros hx POST HB HK fx4 pos e rest ly2 S2 W2 regs2 mem2 md2 HC.
exact (w14m_step (fx := fx4) B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK
  AMALLOC errno_low ML HPCM HSTK_C46 HEV_C46 HLIVE_C46 HTRACE_C46 hx POST HB HK pos e rest ly2 S2 W2 regs2 mem2 md2 HC).
Qed.
(* inside the Section: the kernel's axioms and the Section hypotheses named in the header *)
Print Assumptions rt_w14_S_C46_A.
End m.
About rt_w14_S_C46_A.
Print Assumptions rt_w14_S_C46_A.
