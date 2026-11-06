(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the first stretch of the inlined words_of of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86760 .. 0x867b4: strnlen of the message, the three mallocs stored at 120/128/136(sp) and their NULL tests reloaded from the frame), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_s41.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (a call and back, the caller's facts carried past it) and A/ACh6.v (a segment from one point of the function to the next, the next point's statement a premise). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_s41.v, with its module paths, module names and numbers changed; 2758 of its 2894 lines of code are new or changed and 886 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/LLVMFuzzerTestOneInput_s20.v, with its module paths, module names and numbers changed; 165 of its 685 lines of code are new or changed and 2374 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): file group _s20, piece f:
   the two calloc steps of the test harness's entry function LLVMFuzzerTestOneInput (0x84d34),
     s20_L5  : NZ (0x857a8) -> K857bc   ld s2,40(s1); addi s3,s2,1; li a1,18; mv a0,s3; jal calloc   (SegList.v:718-722)
     s20_S12 : K857bc (0x857bc) -> K857cc   mv s8,a0; li a1,20; mv a0,s3; jal calloc            (SegList.v:723-726)
   against the statements of LLVMFuzzerTestOneInput_s20.v / _s20k.v / _defs.v exactly.

   proves function LLVMFuzzerTestOneInput (reuse search: origin/main@6e24fa4d602c origin/ossv/recipes@3abc3740de97
   origin/ossv/candidates@ee89628c9971 origin/release/pau-projects-recipes@b6a0088adcb4 / the stream's proof index
   LLVMFuzzerTestOneInput + four-ref git grep; output pasted verbatim in
   the walk's shared brief; checker (fresh, read-only): CONFIRM; none: written new)

   COPIED (not Required: one file group never depends on another file group's file): _s12's kit
   proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_s12k.v at commit 734c2dd5a567
   (file sha256 17b5161969267f5a), lines 48-100 (acalloc04_sub, the walk form of RtSegCalloc.aseg_calloc04_rule,
   verbatim) and lines 102-445 (lk_* -> s20f_*, lt_calloc_at -> s20f_calloc_at), in this file's Section; the one
   change: s20f_after_alloc / s20f_calloc_at also give the bytes of every old block of another size kept (calloc's
   acall_kept with sep_blocks), which K857bc / K857cc need for c, m (lt_cm) and tab (zero_atA).
   The run steps follow _s12's lt_seg_S02 (LLVMFuzzerTestOneInput_s12.v at that sha) and _s13's seed of the
   slot 40(s1) (LLVMFuzzerTestOneInput_s13.v s13_seed1). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YGCalloc YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaSB SegGlob PaDenot PaLibF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c SegInstA
  LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s10k LLVMFuzzerTestOneInput_s20k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require m_find_c check_absent_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSegCalloc RtPFSeg RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.

(* ============================== the calloc rule's walk form (generic in segs) ============================== *)
(* verbatim from commit 734c2dd5a567 LLVMFuzzerTestOneInput_s12k.v:48-100 *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section g.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Variable MT : ameter_ops.
Variables pc_calloc cstk : Z.
(* PaCall.v's amalloc04_sub with the calloc rule: a0 = m, a1 = n, the window cstk in place of ASTACK, the zero
   bytes of the new block in the post *)
Lemma acalloc04_sub : RtSegCalloc.aseg_calloc04_rule segs B MT pc_calloc cstk ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (m n : Z) (o : Z) raw ch,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 m -> getr regsT 11 = w64 n ->
0 <= m -> 0 <= n -> m * n < MALLOC_MAX -> m * n <= YGCalloc.PRIM_MAX -> blocks_bytes Sc + m * n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= cstk -> cstk - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
mo_ok MT Sc (mo_malloc MT (m * n)) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc_calloc) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, m * n)] /\
acall_kept segs B lyc Sc W memT W2 mem2 (sp0 + o - cstk) (sp0 + o) (fun a => res <= a < res + req_size (m * n)) /\
(forall i, 0 <= i < m * n -> aview segs (w_H W2) mem2 (res + i) = Some 0) /\
mo_le MT Sc S2 (mo_malloc MT (m * n)) /\
ajournal segs B cstk (sp0 + o) [] lyc Sc W memT mdc [] ly2 S2 W2 mem2 md2 1).
Proof.
intros AC W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k m n o raw ch HJ Ha0 Ha1 Hm Hn Hmn Hprim Hlive Hsp
  Ho16 Ho Hc0 Hstk Hgp Htp Hra Hraw Hnev Hch MOK.
pose proof (ajournal_sub_init segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k cstk (sp0 + o) [] o
  HJ eq_refl Ho16 Ho Hc0 Hstk) as HJ1.
eapply SRr_mono.
{ eapply (AC W regsT memT cstk (sp0 + o) [] lyc Sc W memT mdc [] lyc Sc mdc 0 m n 0 raw ch HJ1 Ha0 Ha1 Hm Hn Hmn Hprim
    Hlive);
  first [exact Hgp | exact Htp | exact Hra | exact Hraw | exact Hnev | exact Hch | exact MOK | reflexivity | lia | idtac]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP & Hres & Hfr & Hr4 & Hbl & HK & Hz & MLE).
exists ly2, S2, regs2, mem2, md2, res. split; [reflexivity|].
split.
{ change own with ([] ++ own). eapply (ajournal_sub_tok segs B LAWS segs_low); [exact HJ | exact HJ2 | lia | lia |].
  intros a (r & Hr & _). destruct Hr. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr|]. split; [exact Hr4|]. split; [exact Hbl|].
replace (sp0 + o + 0 - cstk) with (sp0 + o - cstk) in HK by lia. replace (sp0 + o + 0) with (sp0 + o) in HK by lia.
split; [exact HK|]. split; [exact Hz|]. split; [exact MLE|]. replace (0 + 1) with 1 in HJ2 by reflexivity. exact HJ2.
Qed.
End g.
End c.

(* ============================== lists, words, registers (_s12's s12k.v:102-116) ============================== *)
Fixpoint s20f_bsum (bl : list (Z * Z)) : Z := match bl with [] => 0 | b :: l => snd b + s20f_bsum l end.
Lemma s20f_bsum_app : forall l1 l2, s20f_bsum (l1 ++ l2) = s20f_bsum l1 + s20f_bsum l2.
Proof. induction l1 as [|b l IH]; intros l2; cbn [s20f_bsum app]; [reflexivity | rewrite IH; ring]. Qed.
Lemma s20f_bsum_perm : forall l1 l2, Permutation l1 l2 -> s20f_bsum l1 = s20f_bsum l2.
Proof. intros l1 l2 H. induction H; cbn [s20f_bsum]; [reflexivity | rewrite IHPermutation; reflexivity | ring | congruence]. Qed.
Lemma s20f_pres_reg : forall regs regs' (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.
Lemma s20f_word_kept : forall (rd rd' : reader) a v,
  (forall x, a <= x < a + 8 -> rd' x = rd x) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v HK H. rewrite (rdword_ext rd rd' a); [exact H|]. intros k Hk. apply HK. lia. Qed.

(* cap is the first payload byte mod 40 (SegModel.decode; _s13's s13_cap_range) *)
Lemma s20f_cap_range : forall pl, 0 <= seg_spec.seg_cap pl < 40.
Proof.
intros pl. unfold seg_spec.seg_cap, seg_spec.seg_pay, SegModel.decode.
destruct (SegModel.fuzz_u8 (seg_spec.seg_in pl)) as [b0 i1].
destruct (SegModel.fuzz_u8 i1) as [fl i2]. destruct (SegModel.fuzz_u8 i2) as [b2 i3].
cbn [SegModel.p_cap]. apply Z.mod_pos_bound. lia.
Qed.

(* the shadow base (no instrumented check in either run) and the band of the token runner *)
Definition s20f_X : sv := SLit SHADOW_OFF.
Definition s20f_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the seed of s20_L5 at 0x857a8: every register its own atom, the slot 40(s1) = cap as a read-only word (atom 32) *)
Definition s20f_rg5 : smem := [YP09.mkRegion (Some 9%nat) 40 48 40 40 [YP09.mkChunk 40 (CVal 8 (SOff 32 0))]].
Definition s20f_ss5 : sstate := mkSS LO_NZ sr_atoms s20f_rg5 None (mkFacts [] [] []).

Section dh. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section fh.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the s1 slots K857bc / K857cc state lie in [S1, S1 + 192) *)
Lemma s20f_slots_rng : forall cx c m o v,
  In (o, v) (LT_L cx c m ++ [(152, shadow_addr (m + seg_spec.MC_N))]) -> 0 <= o <= 184.
Proof.
intros cx c m o v Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
- unfold LT_L in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- _; lia|]). destruct Hin.
- destruct Hin as [Hq | []]. injection Hq as <- _. lia.
Qed.
Lemma s20f_slots_kept : forall cx (rd rd' : reader) L,
  (forall o v, In (o, v) L -> 0 <= o <= 184) ->
  (forall a, x_s1 cx <= a < x_s1 cx + 192 -> rd' a = rd a) ->
  lt_slots cx rd L -> lt_slots cx rd' L.
Proof.
intros cx rd rd' L HO HK HL o v Hin.
apply (s20f_word_kept rd); [|exact (HL o v Hin)].
intros x Hx. pose proof (HO o v Hin). apply HK. lia.
Qed.
(* lt_cm reads only the bytes of c and m *)
Lemma s20f_cm_kept : forall (rd rd' : reader) c m st,
  (forall a, c <= a < c + seg_spec.SEG_C_SIZE -> rd' a = rd a) ->
  (forall a, m <= a < m + seg_spec.SEG_M_SIZE -> rd' a = rd a) ->
  lt_cm rd c m st -> lt_cm rd' c m st.
Proof.
intros rd rd' c m st Kc Km Hcm.
unfold lt_cm, sa_rconf, sa_mconf, sa_mconfp in *.
destruct Hcm as ((bc & Hbc & Hec) & (bm & Hbm & Hem)).
split.
- exists bc. split; [|exact Hec]. pose proof (proj1 Hec) as Hl. intros i Hi. rewrite Kc by lia. exact (Hbc i Hi).
- exists bm. split; [|exact Hem]. pose proof (proj1 Hem) as Hl. intros i Hi. rewrite Km by lia. exact (Hbm i Hi).
Qed.


Definition s20f_E (regs : bvmap 5 word) (extra : list word) : env := Eimg (Ereg regs extra).
Lemma s20f_E_reg : forall regs extra n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (s20f_E regs extra) n = getr regs r.
Proof.
intros regs extra n r H. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold s20f_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact H.
Qed.
(* the seed of a stretch with no region and no fact (_s12's s12_seed0) *)
Lemma s20f_seed0 : forall pc (W : world SEGS) regs mem,
  st_ok_pi SEGS VAL (s20f_E regs []) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros pc W regs mem. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold s20f_E. apply regs_ok_Eimg_Ereg.
- reflexivity.
- apply Forall_nil.
- exact I.
- split; [exact I | split; [exact I | exact I]].
Qed.
(* the seed of s20_L5 (_s13's s13_seed1, with the 8-byte word at 40(s1)) *)
Lemma s20f_seed5 : forall (W : world SEGS) (regs : bvmap 5 word) mem s1 cap,
  getr regs 9 = w64 s1 -> 0 <= s1 -> s1 + 48 <= 2 ^ 64 -> 0 <= cap < 2 ^ 64 ->
  rdword (rdW W mem) (s1 + 40) = Some cap ->
  st_ok_pi SEGS VAL (s20f_E regs [Z_to_bv 64 cap]) s20f_ss5
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_NZ)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 cap R9 Hs1a Hs1b Hcap Hw40.
set (E := s20f_E regs [Z_to_bv 64 cap]).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 cap]) n)
  by (intros n Hn; subst E; unfold s20f_E; apply Eimg_low; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 s1)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E32 : ew E 32 = Z_to_bv 64 cap) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (VB : base_val E (Some 9%nat) = s1) by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; lia).
pose proof (val_mem_of_rdword SEGS (w_H W) mem (s1 + 40) cap Hw40) as HV8.
unfold s20f_ss5. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. unfold s20f_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold s20f_rg5. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite VB.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ s1 40 8 (SOff 32 0) cap);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | exact HV8].
- apply pairwise_disjoint_of_extents. unfold s20f_rg5, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi zpairwise_disjoint zall_disjoint]. repeat split.
- split; [exact I | split; [exact I | exact I]].
Qed.
(* a run whose regions have no write window keeps every byte *)
Lemma s20f_nowin_kept : forall E (rs : smem) (W : world SEGS) (m m' : word -> option byte),
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
  forall a, 0 <= a < 2 ^ 64 -> rdW W m' a = rdW W m a.
Proof.
intros E rs W m m' HF Hro a Ha.
apply (kept_of_frame (segs:=SEGS) E rs (w_H W) m m' (fun _ => False) HF); [|exact Ha|tauto].
intros b wlo whi a' Hin Ha'. unfold windows in Hin. apply in_map_iff in Hin. destruct Hin as (r & Heq & Hr).
rewrite forallb_forall in Hro. specialize (Hro r Hr). apply Z.leb_le in Hro.
injection Heq as Hb Hl Hh. subst. lia.
Qed.

(* _s12's s12k.v:125-137 *)
Lemma s20f_blocks_bytes : forall B ly S, blocks_bytes S = s20f_bsum (ablocks B ly S).
Proof.
intros B ly S. unfold blocks_bytes, ablocks, blocks. induction (st_chunks S) as [|c cs IH]; [reflexivity|].
cbn [fold_right List.filter]. destruct (is_alloc c); cbn [map s20f_bsum snd fst]; [rewrite IH; reflexivity | exact IH].
Qed.
Lemma s20f_frame_addr : forall B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S (W : world SEGS) mem md k,
  ajournal SEGS B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k ->
  forall cid pos, frame_addr ly cid pos = frame_addr ly0 cid pos.
Proof.
intros B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k HJ cid pos.
destruct HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF. reflexivity.
Qed.
End fh.
End dh.

(* ============================== the segment lemmas (the common Section header, verbatim) ============================== *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* image numbers of the runtime rows (instantiated by the close) *)
Variables (cstk snp_lo snp_hi : Z) (snp_cr : list (Z * Z)).
(* the runtime entries and callees S11 / S12 reach, at every FP state *)
Hypothesis ACALLOC4 : forall fx0 : YK11.FPState,
  @RtSegCalloc.aseg_calloc04_rule fx0 rc SK SEGS B MT (SIG SS___interceptor_trampoline_calloc) cstk.
Hypothesis HCSTK : 0 <= cstk /\ LTOI_FRAME_MAX + cstk <= STK_LLVMFuzzerTestOneInput.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_asnprintf_realizes fx0 rc SEGS B snp_lo snp_hi snp_cr (SIG SS___interceptor_trampoline_snprintf)
    gotwA guardA.
(* row 4's image numbers (_s15's text, shared by both harness snprintf sites): the harness's formats lie in
   [snp_lo, gotwA) (FR_seg), the read-only ranges inside [snp_lo, snp_hi), and [snp_lo, snp_hi) below the
   allocator ceiling and the fake stack (dest_off_globals for a destination in the class-3 frame); at image A
   snp_lo := 0x10000, snp_hi := YG0f.kImgEnd, each a computation *)
Hypothesis HSNP_LIT : forall x, In x LLVMFuzzerTestOneInput_c.LTOI_LITS ->
  snp_lo <= seg_litA_fz x /\ seg_litA_fz x + Z.of_nat (length x) + 1 <= gotwA.
Hypothesis HSNP_CR : Forall (fun r => snp_lo <= fst r /\ 0 <= snd r /\ fst r + snd r <= snp_hi) snp_cr.
Hypothesis HSNP_LO : 0 <= snp_lo.
Hypothesis HSNP_CEIL : snp_hi <= alloc_ceiling.
Hypothesis HSNP_FAKE : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> snp_hi <= ly_F ly.
Hypothesis ASTRLEN : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
Hypothesis HM_FIND : forall fx0 : YK11.FPState,
  @m_find_c.m_find_contract fx0 rc SK SEGS B (BASE + AF_m_find) STK_m_find RLO_A RHI_A.
Hypothesis HCHECK_ABSENT : forall fx0 : YK11.FPState,
  @check_absent_c.check_absent_contract fx0 rc SK SEGS B (BASE + AF_check_absent) STK_check_absent RLO_A RHI_A.
(* the walk hypotheses (the close discharges them at image A) *)
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis TL : PALib B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis IMGS : s10_img.
Hypothesis BSYM : AF0m.SegBSyms B.

Let RUN := paj_run B LAWS.

(* ---------------- _s12's call step (s12k.v:152-445), adapted ---------------- *)
(* the entry sp and the realigned base S1 (andi sp,sp,-32 at 0x84d74 after addi sp,sp,-320) *)
Lemma s20f_sp : forall cx, lt_base B MT cx ->
  x_sp0 cx mod 16 = 0 /\ alloc_ceiling + STK_LLVMFuzzerTestOneInput <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  x_s1 cx mod 32 = 0 /\ x_sp0 cx - LTOI_FRAME_MAX <= x_s1 cx /\ x_s1 cx <= x_sp0 cx - 320.
Proof.
intros cx HB. destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
unfold x_s1, x_sp0, LT_FRAME, LTOI_FRAME_MAX in *.
set (s := spZ (x_regs cx)) in *. clearbody s.
repeat split; lia.
Qed.

(* a live block of a state is a harness block of that state: at or above 4096, 16-aligned, addressable *)
Lemma s20f_hblk : forall ly S (W : world SEGS) mem md a n,
  AR SEGS B ly S W mem md -> In (a, n) (ablocks B ly S) -> lt_hblk B ly S (rdW W mem) a n.
Proof.
intros ly S W mem md a n HAR Hin.
destruct (al_blocks _ _ LAWS ly S W mem md a n HAR Hin) as (H16 & H4096 & Hceil & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [_ Hreq].
pose proof asan_consts as (C1 & _).
split; [exact Hin|]. split; [exact H4096|]. split; [exact H16|].
split; [lia|]. split; [lia|].
split; [exact (amem_range_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
intros Hn0. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia) Hn0).
Qed.

(* a chain for the call's chain_pre: the stack from S1 to the layout's top is mapped (the entry's astack_pres
   carried by the journal; longl, the footprint, is below the stack), and s0 = SP0 is at least S1 + 320 *)
Lemma s20f_chain : forall cx ly S (W : world SEGS) regs mem md k o,
  lt_base B MT cx -> lt_frame B cx ly S W regs mem md k o -> 4096 <= raZ regs ->
  exists ch, chain_pre ly (rdW W mem) regs ch.
Proof.
intros cx ly S W regs mem md k o HB HF Hra.
pose proof (s20f_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
destruct HF as (HJ & R2 & _ & _ & R8 & _).
pose proof HB as (_ & HPRES & _).
pose proof asan_consts as (C1 & _).
assert (Esp : spZ regs = x_s1 cx)
  by (unfold spZ; rewrite R2; unfold w64; rewrite YP03.unsigned_lit_small by lia; reflexivity).
assert (Es0 : s0Z regs = x_sp0 cx)
  by (unfold s0Z; rewrite R8; unfold w64; rewrite YP03.unsigned_lit_small by lia; reflexivity).
apply chain_pre_any; [exact Hra| |].
- rewrite Esp. apply (astack_rd_mono ly _ (x_sp0 cx - STK_LLVMFuzzerTestOneInput)); [lia|].
  apply astack_rd_of_pres.
  apply (astack_pres_journal SEGS B pa_segs_low STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
    (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k HJ HPRES).
  intros a (r & Hr & Ha) Ha2. exfalso. unfold ltoi_PG in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  unfold longlA, A_LONGL, LONGL_N in Ha. lia.
- rewrite Esp, Es0. lia.
Qed.

(* the facts of a point after one allocator call of the harness at sp = S1: the journal from the entry goes on with
   one event, the kept registers and every byte the facts read are the same, the new block joins the harness's
   (newest first), the budget pays one event; and (beyond _s12's text) every old block of another size keeps
   its bytes *)
Lemma s20f_after_alloc : forall cx ly S (W : world SEGS) regsT memT md k acc rem o O
  ly2 S2 (W2 : world SEGS) regs2 mem2 md2 res nb slo,
  lt_base B MT cx -> lt_core B MT cx ly S W regsT memT md k acc rem o O ->
  1 <= rem -> 0 <= nb <= 65536 ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly2 S2 W2 mem2 md2 (k + 1) ->
  aregs_preserved regsT regs2 -> frames S2 = frames S ->
  ablocks B ly2 S2 = ablocks B ly S ++ [(res, nb)] ->
  acall_kept SEGS B ly S W memT W2 mem2 slo (x_s1 cx) (fun a => res <= a < res + req_size nb) ->
  mo_le MT S S2 (mo_malloc MT nb) ->
  lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_malloc MT nb) (rem - 1) o ((res, nb) :: O) /\
  lt_hblk B ly2 S2 (rdW W2 mem2) res nb /\
  (forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memT a) /\
  (forall b nb', In (b, nb') (ablocks B ly S) -> nb' <> nb ->
     forall a, b <= a < b + nb' -> rdW W2 mem2 a = rdW W memT a).
Proof.
intros cx ly S W regsT memT md k acc rem o O ly2 S2 W2 regs2 mem2 md2 res nb slo HB HC Hrem Hnb HJ2 HP Hfr2 Hbl HKc MLE.
pose proof (s20f_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _).
destruct HC as (HF & HI & HBL & HBUD).
destruct HF as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H176 & HSH).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof (proj1 HJ2) as HAR2.
pose proof HKc as (K1 & K2 & K3 & K4 & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof ASAN_CEIL_range as (CR & _).
assert (HinF : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (HinF2 : In (LT_FCLS, x_fpos cx) (frames S2)) by (rewrite Hfr2; exact HinF).
assert (HinB2 : In (res, nb) (ablocks B ly2 S2)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx)
  by exact (s20f_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ _ _).
assert (EF2 : frame_addr ly2 LT_FCLS (x_fpos cx) = x_fr cx)
  by exact (s20f_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 _ _).
assert (F512 : fs_frame_bytes LT_FCLS = 512) by (vm_compute; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S W memT md LT_FCLS (x_fpos cx) HAR HinF) as (Hf0 & Hfc & _).
rewrite EF in Hf0. rewrite EF, F512 in Hfc.
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 res nb HAR2 HinB2) as (_ & Hr4096 & Hrceil & Hrapp & _ & _ & _).
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 res nb LT_FCLS (x_fpos cx) HAR2 HinB2 HinF2) as Hsep.
rewrite EF2, F512 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
(* the stack above S1 *)
assert (KS : forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memT a).
{ intros a Ha. pose proof ltoi_stk_room as HSR. unfold LTOI_FRAME_MAX in HSR.
  apply K1; [split; [lia | exact (proj2 Ha)] |]. intros [_ Hc]. lia. }
(* the frame's bytes *)
assert (KF : forall a, x_fr cx <= a < x_fr cx + 512 -> rdW W2 mem2 a = rdW W memT a).
{ intros a Ha. apply (K4 LT_FCLS (x_fpos cx) a HinF).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF, F512. lia.
  - cbv beta. intros Hr. lia. }
(* the frame's shadow bytes *)
assert (KH : forall i, 0 <= i < 64 -> rdW W2 mem2 (x_sh cx + i) = rdW W memT (x_sh cx + i)).
{ intros i Hi. apply (K4 LT_FCLS (x_fpos cx) _ HinF).
  - right. unfold in_zr. cbn [fst snd]. rewrite EF, F512. unfold x_sh. lia.
  - cbv beta. intros Hr. unfold in_app, kLowShadowBeg, ASAN_CEIL in Hrapp. unfold x_sh, shadow_addr, SHADOW_OFF in Hr.
    pose proof (req_size_pos nb ltac:(lia)) as [Hq1 _]. lia. }
(* an old block of another size: apart from the new one (AR's block law at the return) *)
assert (KB : forall b nb', In (b, nb') (ablocks B ly S) -> nb' <> nb ->
  forall a, b <= a < b + nb' -> rdW W2 mem2 a = rdW W memT a).
{ intros b nb' Hin Hne a Ha.
  assert (Hin2 : In (b, nb') (ablocks B ly2 S2)) by (rewrite Hbl; apply in_or_app; left; exact Hin).
  assert (Hneq : (b, nb') <> (res, nb)) by (intros Heq; injection Heq as _ Heq; exact (Hne Heq)).
  pose proof (sep_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 b nb' res nb HAR2 Hin2 HinB2 Hneq) as Hd.
  destruct (al_blocks _ _ LAWS ly S W memT md b nb' HAR Hin) as (_ & _ & _ & _ & _ & _ & Hnb').
  pose proof (req_size_pos nb' ltac:(lia)) as [_ Hq']. pose proof (req_size_pos nb ltac:(lia)) as [_ Hq].
  unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  replace a with (b + (a - b)) by ring.
  apply (K2 b nb' (a - b) Hin ltac:(lia)). cbv beta. lia. }
split; [|split; [exact (s20f_hblk ly2 S2 W2 mem2 md2 res nb HAR2 HinB2) | split; [exact KS | exact KB]]].
split; [|split; [|split]].
- (* the frame *)
  split; [exact HJ2|].
  rewrite (s20f_pres_reg _ _ 2%bv 2 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (s20f_pres_reg _ _ 3%bv 3 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (s20f_pres_reg _ _ 4%bv 4 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (s20f_pres_reg _ _ 8%bv 8 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (s20f_pres_reg _ _ 9%bv 9 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
  split.
  { intros i r Hi. assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
    change (length LT_SAVED) with 13%nat in Hi13.
    apply (s20f_word_kept (rdW W memT)); [|exact (HSV i r Hi)]. intros x Hx. apply KS. lia. }
  split; [apply (s20f_word_kept (rdW W memT)); [|exact HH0]; intros x Hx; apply KF; lia|].
  split; [apply (s20f_word_kept (rdW W memT)); [|exact HH8]; intros x Hx; apply KF; lia|].
  split; [apply (s20f_word_kept (rdW W memT)); [|exact HH16]; intros x Hx; apply KF; unfold LT_FLAGW; lia|].
  split; [apply (s20f_word_kept (rdW W memT)); [|exact HFL]; intros x Hx; apply KF; unfold LT_FLAGW in *; lia|].
  split; [apply (s20f_word_kept (rdW W memT)); [|exact H176]; intros x Hx; apply KS; lia|].
  intros i Hi. rewrite (lt_fsh_len o) in Hi. rewrite KH by lia. exact (HSH i ltac:(rewrite lt_fsh_len; exact Hi)).
- (* the image facts *)
  exact (s10_lt_img_kept B IMGS BSYM cx W2 mem2 (rdW W memT) HAR2 K3 HI).
- (* the blocks *)
  unfold lt_blocks in *. rewrite Hbl.
  eapply Permutation_trans; [apply Permutation_app_tail; exact HBL|].
  cbn [app]. apply Permutation_sym. apply Permutation_cons_append.
- (* the budget *)
  destruct HBUD as (B1 & B2 & B3 & B4 & B5 & B6).
  pose proof (mo_malloc_mono MT MTL nb 65536 ltac:(lia)) as M1.
  pose proof (mo_malloc_nonneg MT MTL nb ltac:(lia)) as M0.
  pose proof (mo_free_nonneg MT MTL) as M3.
  assert (HU : mo_malloc MT nb <= LT_U MT) by (unfold LT_U; lia).
  unfold lt_bud. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact (mo_le_trans MT MTL _ _ _ _ _ B4 MLE)|]. split; [lia|].
  set (U := LT_U MT) in *. clearbody U. nia.
Qed.

(* the facts of a point carried across a run of the walk that writes at most the s1 slots [S1 + lo, S1 + hi) below
   176(s1), keeps sp, gp, tp, s0, s1 and the allocator state (its journal from the entry at the same count) *)
Lemma s20f_core_run : forall cx ly S (W : world SEGS) regs mem md k acc rem o O regs' mem' md' lo hi,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + lo <= a < x_s1 cx + hi) -> rdW W mem' a = rdW W mem a) ->
  0 <= lo <= hi -> hi <= 176 ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  lt_core B MT cx ly S W regs' mem' md' k acc rem o O.
Proof.
intros cx ly S W regs mem md k acc rem o O regs' mem' md' lo hi HB HC HJ' HK Hlo Hhi P2 P3 P4 P8 P9.
pose proof (s20f_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _).
destruct HC as (HF & HI & HBL & HBUD).
destruct HF as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H176 & HSH).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof (proj1 HJ') as HAR'.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof ltoi_stk_room as HSR. unfold LTOI_FRAME_MAX in HSR.
assert (HinF : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx)
  by exact (s20f_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ _ _).
assert (F512 : fs_frame_bytes LT_FCLS = 512) by (vm_compute; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR HinF) as (Hf0 & Hfc & _).
rewrite EF in Hf0. rewrite EF, F512 in Hfc.
assert (KA : forall a, 0 <= a < x_s1 cx + lo \/ x_s1 cx + hi <= a < 2 ^ 64 -> rdW W mem' a = rdW W mem a).
{ intros a Ha. apply HK.
  - destruct Ha as [Ha | Ha]; split; lia.
  - intros [Hc1 Hc2]. destruct Ha as [Ha | Ha]; lia. }
split; [|split; [|split]].
- split; [exact HJ'|].
  rewrite P2, P3, P4, P8, P9.
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
  split.
  { intros i r Hi. assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
    change (length LT_SAVED) with 13%nat in Hi13.
    apply (s20f_word_kept (rdW W mem)); [|exact (HSV i r Hi)]. intros x Hx. apply KA. right. lia. }
  split; [apply (s20f_word_kept (rdW W mem)); [|exact HH0]; intros x Hx; apply KA; left; lia|].
  split; [apply (s20f_word_kept (rdW W mem)); [|exact HH8]; intros x Hx; apply KA; left; lia|].
  split; [apply (s20f_word_kept (rdW W mem)); [|exact HH16]; intros x Hx; apply KA; left; lia|].
  split; [apply (s20f_word_kept (rdW W mem)); [|exact HFL]; intros x Hx; apply KA; left; unfold LT_FLAGW in *; lia|].
  split; [apply (s20f_word_kept (rdW W mem)); [|exact H176]; intros x Hx; apply KA; right; lia|].
  intros i Hi. rewrite KA; [exact (HSH i Hi)|]. left. rewrite (lt_fsh_len o) in Hi.
  unfold x_sh, shadow_addr, SHADOW_OFF. lia.
- apply (s10_lt_img_kept B IMGS BSYM cx W mem' (rdW W mem) HAR'); [|exact HI].
  intros a Ha _ _. apply KA. left. pose proof (pa_segs_low a Ha). lia.
- exact HBL.
- exact HBUD.
Qed.

(* the premises an allocator call of the harness asks, from lt_core at the call *)
Lemma s20f_call_pre : forall cx ly S (W : world SEGS) regsT memT md k acc rem o O nb,
  lt_base B MT cx -> lt_core B MT cx ly S W regsT memT md k acc rem o O ->
  1 <= rem -> 0 <= nb <= 65536 -> s20f_bsum O + nb <= LIVE_LTOI ->
  spZ regsT = x_sp0 cx + (x_s1 cx - x_sp0 cx) /\ (x_s1 cx - x_sp0 cx) mod 16 = 0 /\ x_s1 cx - x_sp0 cx <= 0 /\
  - LTOI_FRAME_MAX <= x_s1 cx - x_sp0 cx /\
  getr regsT 3 = w64 (as_gp B) /\ getr regsT 4 = w64 (as_tp B) /\ st_nev S < EV_MAX /\
  blocks_bytes S + nb <= LIVE_MAX /\ mo_ok MT S (mo_malloc MT nb).
Proof.
intros cx ly S W regsT memT md k acc rem o O nb HB HC Hrem Hnb Hsum.
pose proof (s20f_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof HC as (HF & _ & HBL & HBUD).
pose proof HF as (HJ & R2 & R3 & R4 & _).
pose proof HB as (HPRE0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev & Hlive & Hmo).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
pose proof HBUD as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof asan_consts as (C1 & _).
pose proof (mo_malloc_mono MT MTL nb 65536 ltac:(lia)) as M1.
pose proof (mo_malloc_nonneg MT MTL nb ltac:(lia)) as M0.
pose proof (mo_free_nonneg MT MTL) as M3.
assert (HU : mo_malloc MT nb <= LT_U MT) by (unfold LT_U; lia).
assert (HRU : LT_U MT <= rem * LT_U MT) by nia.
split; [unfold spZ; rewrite R2; unfold w64; rewrite YP03.unsigned_lit_small by lia; lia|].
split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite R3; exact Hgp0|]. split; [rewrite R4; exact Htp0|].
split; [unfold EV_LTOI in *; lia|].
split.
{ rewrite (s20f_blocks_bytes B ly S), (s20f_bsum_perm _ _ HBL), s20f_bsum_app.
  unfold x_bl0. rewrite <- (s20f_blocks_bytes B (x_ly cx) (x_S cx)). unfold LIVE_LTOI in *. lia. }
apply (mok_station MT (x_S cx) S (XM_LTOI MT (x_pl cx)) acc (mo_malloc MT nb) MTL Hmo B4 M0). lia.
Qed.

(* ---- one call of the calloc wrapper (row 13, at the calloc trampoline) from a point where lt_core holds (_s12's
   lt_calloc_at, with the old blocks of another size kept in the continuation) ---- *)
Lemma s20f_calloc_at : forall cx ly S (W : world SEGS) regsT memT md k acc rem o O (m n : Z) raw Q,
  lt_base B MT cx -> lt_core B MT cx ly S W regsT memT md k acc rem o O ->
  1 <= rem -> 0 <= m -> 0 <= n -> m * n <= 64512 -> s20f_bsum O + m * n <= LIVE_LTOI ->
  getr regsT 10 = w64 m -> getr regsT 11 = w64 n -> getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  (forall ly2 S2 (W2 : world SEGS) regs2 mem2 md2 res,
     lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_malloc MT (m * n)) (rem - 1) o ((res, m * n) :: O) ->
     lt_hblk B ly2 S2 (rdW W2 mem2) res (m * n) ->
     zero_atA (rdW W2 mem2) res (m * n) ->
     aregs_preserved regsT regs2 -> getr regs2 10 = w64 res ->
     (forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memT a) ->
     (forall b nb', In (b, nb') (ablocks B ly S) -> nb' <> m * n ->
        forall a, b <= a < b + nb' -> rdW W2 mem2 a = rdW W memT a) ->
     SRr SEGS W2 (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (pa_sigma SS___interceptor_trampoline_calloc)) memT (seg_rom SEGS)) md) Q.
Proof.
intros cx ly S W regsT memT md k acc rem o O m n raw Q HB HC Hrem Hm Hn Hmn Hsum H10 H11 H1 Hraw Hra4 HK.
assert (Hmn0 : 0 <= m * n) by nia.
destruct (s20f_call_pre cx ly S W regsT memT md k acc rem o O (m * n) HB HC Hrem ltac:(lia) Hsum)
  as (Hsp & Ho16 & Ho0 & Hom & Hgp & Htp & Hnev & Hlv & MOK).
pose proof HC as (HF & _).
pose proof (proj1 HF) as HJ.
destruct HCSTK as [Hc0 Hc1].
destruct (s20f_chain cx ly S W regsT memT md k o HB HF ltac:(unfold raZ; rewrite H1; exact Hra4)) as (ch & Hch).
eapply SRr_bind.
{ exact (acalloc04_sub SEGS B LAWS pa_segs_low MT (pa_sigma SS___interceptor_trampoline_calloc) cstk (ACALLOC4 fx)
    W regsT memT STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md k m n (x_s1 cx - x_sp0 cx) raw ch HJ H10 H11 Hm Hn
    ltac:(unfold MALLOC_MAX; lia) ltac:(unfold YGCalloc.PRIM_MAX; lia) Hlv Hsp Ho16 Ho0 Hc0 ltac:(lia) Hgp Htp H1 Hraw
    Hnev Hch MOK). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HPr & Hres & Hfr & _ & Hbl & HKp & Hz & MLE & _).
replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) in HKp by ring.
destruct (s20f_after_alloc cx ly S W regsT memT md k acc rem o O ly2 S2 W2 regs2 mem2 md2 res (m * n) _
  HB HC Hrem ltac:(lia) HJ2 HPr Hfr Hbl HKp MLE) as (HC2 & HH2 & HK2 & HKB).
exact (HK ly2 S2 W2 regs2 mem2 md2 res HC2 HH2 Hz HPr Hres HK2 HKB).
Qed.

(* ---------------- s20_L5: 0x857a8 .. 0x857b8, then calloc(cap + 1, 18) to K857bc ---------------- *)
Lemma s20_L5 : LTA_K857bc B MT -> S20_NZ_stmt B MT.
Proof.
intros HKA. unfold S20_NZ_stmt.
intros cx ly S W regs mem md k acc c m HB Hfrm HCTX R26.
pose proof (HKA fx) as HK. clear HKA.
destruct HCTX as (HC & HHc & HHm & HSL & HCM).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (s20f_cap_range (x_pl cx)) as Hcap. change (seg_spec.seg_cap (x_pl cx)) with (x_cap cx) in Hcap.
pose proof HC as (HF & _). pose proof HF as (HJ & R2 & R3 & R4 & R8 & R9 & _).
pose proof (s20f_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof asan_consts as (C1 & _).
assert (Hw40 : rdword (rdW W mem) (x_s1 cx + 40) = Some (x_cap cx)).
{ apply HSL. apply in_or_app. left. unfold LT_L. cbn [In]. right; right; right; right; left. reflexivity. }
pose proof (s20f_seed5 W regs mem (x_s1 cx) (x_cap cx) R9 ltac:(lia) ltac:(lia) ltac:(lia) Hw40) as HS.
assert (SHOK : sh_ok SEGS s20f_X [] (s20f_E regs [Z_to_bv 64 (x_cap cx)]) (mrestrict (w_H W) mem))
  by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (s20f_E regs [Z_to_bv 64 (x_cap cx)])) by (unfold s20f_E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr ->
  ew (s20f_E regs [Z_to_bv 64 (x_cap cx)]) n = getr regs rr)
  by (intros n rr Hn; exact (s20f_E_reg regs _ n rr Hn)).
assert (E32 : ew (s20f_E regs [Z_to_bv 64 (x_cap cx)]) 32 = Z_to_bv 64 (x_cap cx))
  by (unfold s20f_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
remember (s20f_E regs [Z_to_bv 64 (x_cap cx)]) as E eqn:HE. clear HE.
unfold cfg_at, w64.
(* 0x857a8 .. 0x857b8: s2 := 40(s1) = cap, s3 := cap + 1, a1 := 18, a0 := s3, jal calloc *)
paj_run_tok RUN HS HJ SHOK s20f_span.
{ change (ss_mem s20f_ss5) with s20f_rg5. unfold s20f_rg5.
  apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19.
unfold LTOI_FRAME_MAX in Hs1lo. unfold STK_LLVMFuzzerTestOneInput in Hsp0.
assert (KR : forall r : bv 5, In r [2; 3; 4; 8; 9; 26]%bv -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ let P := fresh "P" in lazymatch goal with |- getr _ ?rr = _ => prreg HS rr P end;
      rewrite P; apply EEo; reflexivity | ]).
  destruct Hr. }
pose proof (s20f_nowin_kept E _ W mem (ms_mem ms) HFr eq_refl) as KM.
pose proof (s20f_core_run cx ly S W regs mem md k acc 6 LFO0 [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)]
  (ms_regs ms) (ms_mem ms) md1 0 0 HB HC HJ
  ltac:(intros a Ha _; exact (KM a Ha)) ltac:(lia) ltac:(lia)
  (KR 2%bv ltac:(cbn; tauto)) (KR 3%bv ltac:(cbn; tauto)) (KR 4%bv ltac:(cbn; tauto))
  (KR 8%bv ltac:(cbn; tauto)) (KR 9%bv ltac:(cbn; tauto))) as HC1.
assert (Ucap : Z_to_bv 64 (bv_unsigned (ew E 32) + 1) = w64 (x_cap cx + 1)).
{ rewrite E32. unfold w64. rewrite YP03.unsigned_lit_small by lia. reflexivity. }
pose proof HHc as (HinC & _ & _ & Hc0 & Hc63 & _). pose proof HHm as (HinM & _ & _ & Hm0 & Hm63 & _).
assert (Htn : x_tabn cx = 18 * (x_cap cx + 1)) by reflexivity.
eapply (s20f_calloc_at cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc 6 LFO0
  [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] (x_cap cx + 1) 18 _ _ HB HC1).
- lia.
- lia.
- lia.
- lia.
- cbn [s20f_bsum snd]. unfold seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE, LIVE_LTOI. lia.
- rewrite P10. exact Ucap.
- rewrite P11. reflexivity.
- exact P1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- rewrite YP03.unsigned_lit_small by lia. lia.
- intros ly2 S2 W2 regs2 mem2 md2 tab HC2 HHt HZ HPr Hres HKS HKB.
  replace ((x_cap cx + 1) * 18) with (x_tabn cx) in HC2, HHt, HZ, HKB by (rewrite Htn; ring).
  replace (6 - 1) with 5 in HC2 by reflexivity.
  pose proof HC2 as (HF2 & _ & HBL2 & _). pose proof (proj1 (proj1 HF2)) as HAR2.
  assert (Hpres : forall r z, acallee_saved z -> Z_to_bv 5 z = r -> getr regs2 r = getr (ms_regs ms) r)
    by (intros r z Hz Hr; exact (s20f_pres_reg _ _ r z HPr Hz Hr)).
  apply (HK cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_malloc MT (x_tabn cx)) c m tab HB Hfrm HC2).
  + apply (s20f_hblk ly2 S2 W2 mem2 md2 c _ HAR2).
    unfold lt_blocks in HBL2. apply (Permutation_in _ (Permutation_sym HBL2)). cbn [app]. right; right; left. reflexivity.
  + apply (s20f_hblk ly2 S2 W2 mem2 md2 m _ HAR2).
    unfold lt_blocks in HBL2. apply (Permutation_in _ (Permutation_sym HBL2)). cbn [app]. right; left. reflexivity.
  + exact HHt.
  + exact HZ.
  + exact Hres.
  + rewrite (Hpres 18%bv 18) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
    rewrite P18, E32. reflexivity.
  + rewrite (Hpres 19%bv 19) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
    rewrite P19. exact Ucap.
  + rewrite (Hpres 26%bv 26) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
    rewrite (KR 26%bv ltac:(cbn; tauto)). exact R26.
  + apply (s20f_slots_kept cx (rdW W mem)); [intros o v Hin; exact (s20f_slots_rng _ _ _ o v Hin) | | exact HSL].
    intros a Ha. rewrite HKS by lia. apply KM. lia.
  + apply (s20f_cm_kept (rdW W mem)); [| | exact HCM].
    * intros a Ha. rewrite (HKB c seg_spec.SEG_C_SIZE HinC ltac:(rewrite Htn; unfold seg_spec.SEG_C_SIZE; lia) a Ha).
      apply KM. unfold seg_spec.SEG_C_SIZE in *. lia.
    * intros a Ha. rewrite (HKB m seg_spec.SEG_M_SIZE HinM ltac:(rewrite Htn; unfold seg_spec.SEG_M_SIZE; lia) a Ha).
      apply KM. unfold seg_spec.SEG_M_SIZE in *. lia.
Qed.

(* ---------------- s20_S12: 0x857bc .. 0x857c8, then calloc(cap + 1, 20) to K857cc ---------------- *)
Lemma s20_S12 : LTA_K857cc B MT -> LT_K857bc_stmt B MT.
Proof.
intros HKA. unfold LT_K857bc_stmt.
intros cx ly S W regs mem md k acc c m tab HB Hfrm HC HHc HHm HHt HZt R10 R18 R19 R26 HSL HCM.
pose proof (HKA fx) as HK. clear HKA.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (s20f_seed0 LO_K857bc W regs mem) as HS.
assert (SHOK : sh_ok SEGS s20f_X [] (s20f_E regs []) (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (s20f_E regs [])) by (unfold s20f_E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (s20f_E regs []) n = getr regs rr)
  by (intros n rr Hn; exact (s20f_E_reg regs [] n rr Hn)).
pose proof HC as (HF & _). pose proof (proj1 HF) as HJ.
remember (s20f_E regs []) as E eqn:HE. clear HE.
unfold cfg_at, w64.
(* 0x857bc .. 0x857c8: s8 := a0 (tab), a1 := 20, a0 := s3 (cap + 1), jal calloc *)
paj_run_tok RUN HS HJ SHOK s20f_span.
{ apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (24%bv : bv 5) P24.
assert (KR : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 26]%bv -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ let P := fresh "P" in lazymatch goal with |- getr _ ?rr = _ => prreg HS rr P end;
      rewrite P; apply EEo; reflexivity | ]).
  destruct Hr. }
pose proof (s20f_nowin_kept E _ W mem (ms_mem ms) HFr eq_refl) as KM.
pose proof (s20f_cap_range (x_pl cx)) as Hcap. change (seg_spec.seg_cap (x_pl cx)) with (x_cap cx) in Hcap.
pose proof (s20f_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
unfold LTOI_FRAME_MAX in Hs1lo. unfold STK_LLVMFuzzerTestOneInput in Hsp0.
pose proof asan_consts as (C1 & _).
pose proof (s20f_core_run cx ly S W regs mem md k acc 5 LFO0
  [(tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)]
  (ms_regs ms) (ms_mem ms) md1 0 0 HB HC HJ
  ltac:(intros a Ha _; exact (KM a Ha)) ltac:(lia) ltac:(lia)
  (KR 2%bv ltac:(cbn; tauto)) (KR 3%bv ltac:(cbn; tauto)) (KR 4%bv ltac:(cbn; tauto))
  (KR 8%bv ltac:(cbn; tauto)) (KR 9%bv ltac:(cbn; tauto))) as HC1.
pose proof HHc as (HinC & _ & _ & Hc0 & Hc63 & _). pose proof HHm as (HinM & _ & _ & Hm0 & Hm63 & _).
pose proof HHt as (HinT & _ & _ & Ht0 & Ht63 & _).
assert (Htn : x_tabn cx = 18 * (x_cap cx + 1)) by reflexivity.
assert (Hmn : x_mtn cx = 20 * (x_cap cx + 1)) by reflexivity.
eapply (s20f_calloc_at cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc 5 LFO0
  [(tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] (x_cap cx + 1) 20 _ _ HB HC1).
- lia.
- lia.
- lia.
- lia.
- cbn [s20f_bsum snd]. rewrite Htn. unfold seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE, LIVE_LTOI. lia.
- rewrite P10, (EEo 19%nat 19%bv eq_refl). exact R19.
- rewrite P11. reflexivity.
- exact P1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- rewrite YP03.unsigned_lit_small by lia. lia.
- intros ly2 S2 W2 regs2 mem2 md2 mt HC2 HHmt HZmt HPr Hres HKS HKB.
  replace ((x_cap cx + 1) * 20) with (x_mtn cx) in HC2, HHmt, HZmt, HKB by (rewrite Hmn; ring).
  replace (5 - 1) with 4 in HC2 by reflexivity.
  pose proof HC2 as (HF2 & _ & HBL2 & _). pose proof (proj1 (proj1 HF2)) as HAR2.
  assert (Hpres : forall r z, acallee_saved z -> Z_to_bv 5 z = r -> getr regs2 r = getr (ms_regs ms) r)
    by (intros r z Hz Hr; exact (s20f_pres_reg _ _ r z HPr Hz Hr)).
  apply (HK cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_malloc MT (x_mtn cx)) c m tab mt HB Hfrm HC2).
  + apply (s20f_hblk ly2 S2 W2 mem2 md2 c _ HAR2).
    unfold lt_blocks in HBL2. apply (Permutation_in _ (Permutation_sym HBL2)). cbn [app].
    right; right; right; left. reflexivity.
  + apply (s20f_hblk ly2 S2 W2 mem2 md2 m _ HAR2).
    unfold lt_blocks in HBL2. apply (Permutation_in _ (Permutation_sym HBL2)). cbn [app]. right; right; left. reflexivity.
  + apply (s20f_hblk ly2 S2 W2 mem2 md2 tab _ HAR2).
    unfold lt_blocks in HBL2. apply (Permutation_in _ (Permutation_sym HBL2)). cbn [app]. right; left. reflexivity.
  + exact HHmt.
  + intros i Hi. rewrite (HKB tab (x_tabn cx) HinT ltac:(rewrite Htn, Hmn; lia) (tab + i) ltac:(lia)).
    rewrite KM by lia. exact (HZt i Hi).
  + exact HZmt.
  + exact Hres.
  + rewrite (Hpres 18%bv 18) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
    rewrite (KR 18%bv ltac:(cbn; tauto)). exact R18.
  + rewrite (Hpres 24%bv 24) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
    rewrite P24, (EEo 10%nat 10%bv eq_refl). exact R10.
  + rewrite (Hpres 26%bv 26) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
    rewrite (KR 26%bv ltac:(cbn; tauto)). exact R26.
  + apply (s20f_slots_kept cx (rdW W mem)); [intros o v Hin; exact (s20f_slots_rng _ _ _ o v Hin) | | exact HSL].
    intros a Ha. rewrite HKS by lia. apply KM. lia.
  + apply (s20f_cm_kept (rdW W mem)); [| | exact HCM].
    * intros a Ha. rewrite (HKB c seg_spec.SEG_C_SIZE HinC ltac:(rewrite Hmn; unfold seg_spec.SEG_C_SIZE; lia) a Ha).
      apply KM. unfold seg_spec.SEG_C_SIZE in *. lia.
    * intros a Ha. rewrite (HKB m seg_spec.SEG_M_SIZE HinM ltac:(rewrite Hmn; unfold seg_spec.SEG_M_SIZE; lia) a Ha).
      apply KM. unfold seg_spec.SEG_M_SIZE in *. lia.
Qed.

End e.
End f.
End d.
