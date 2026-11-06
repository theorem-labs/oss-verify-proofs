(* check_no_overread 0x811c8 (fs.c), fs.asan: the fuzz_free call step of the tail, i.e. a Theorem Labs lane's
   `cno_call_ffree_T B` (lib/A/FSW_check_no_overread.v:1070, the CTX-free Prop at a working branch fb4231f5e1e),
   proved here with the name cno_call_ffree. The sites are 0x81420 / 0x81428 / 0x81430 (return addresses 0x81424 /
   0x8142c / 0x81434), one lemma for the three: the call shapes agree and nothing in the step depends on which
   return address it is. Rule 24: this file proves PART of check_no_overread only (one call step).
   The walk file is a Theorem Labs lane's and is not edited here; the shared helpers (cno_geom, cno_frame, cno_sf_not_ush,
   cno_unp_*, cno_glob_kept, ...) are a Theorem Labs lane's, used by path from lib/A/FSW_check_no_overread_tail.v, not copied.

   The step (MEASURED control flow in the walk file's header): at the call the walk holds its class-1 fake frame
   (own = [(1, pos)]), sp = s1 = sp1, s0 = sp0, and the prologue's two words at sp0 - 8 / sp0 - 16, which are the
   callee's frame-pointer chain (cno_chain). fuzz_free's own contract (FSH_Fn_alloc.v fuzz_free_spec, the CTX-free
   form of a working branch 05f474949ed) is the Section hypothesis FFREE; it takes no call-trace row, so
   this file has no TRACE_* hypothesis. Both arms:
     p = 0   : the callee returns at once, kc = 0, U' = U, ablocks and the ledger unchanged;
     p <> 0  : the block's head (p - HEAD, HEAD) leaves U, one event (kc = 1), the block leaves ablocks and
               g_live drops by n.
   The journal composition is FSW_K3.v:215 fsw_ajournal_sub4. Its callee-footprint premise is why the p <> 0 arm
   needs `~ In (p - HEAD, n + HEAD) (ablocks B (c_ly cx) (c_S cx))` (a Theorem Labs lane added it at 04:42Z): the freed
   block's bytes are in the callee's FP, and the composition admits them only as in_tmp_block of the ENTRY blocks,
   i.e. as a block the walk itself made.

   LOOKUP (rule 24): the walk file's header carries the index runs; re-CONFIRMED for this lane (a Theorem Labs lane,
   2026-10-29 03:4xZ): `proof-index check_no_overread`, unpiped, rc=0, index v5
   built 2026-10-29T01:50:18Z (main f4cc67298b7, ossv/recipes 5121fb8693b, ossv/candidates ee89628c997,
   release/pau-projects-recipes b6a0088adcb): 20 named / 50 by address / 36 related / 9 lemma(s), 71 hit lines, all
   under lib/Prog, lib/Prog/CF, lib/U/Prog, lib/U/Prog/CF (plain and UBSan), none under lib/A or lib/B; full output
   (internal path). TEMPLATE (text only, never Required): the bespoke A-build
   proof on a working branch 1da71ab56d4, lib/A/Prog/check_no_overread_mid_r4.v (CnoSt_8..CnoSt_10, the
   three fuzz_free calls of the same sites) and check_no_overread_mid_st.v; it is built on the pre-ruling model
   (AA / a_call_pre_tp / its own ALedger), so nothing is bridged from it. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG05 YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_ret
FSW_rres FSW_frame FSW_malloc_free FSW_rd FSH_Fn_cno FSH_Fn_alloc FSW_check_no_overread_tbl
FSW_check_no_overread FSW_check_no_overread_tail.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---- the four allocator statics are off every read-only byte: the relro range [FS_RLO, FS_RHI) ends below
   g_fail_at (0xa3ca0), and every read-only segment of the pinned image ends at or below it (MEASURED here) ---- *)
Lemma cno_ff_ro_segs : forallb (fun s => seg_writable s ||
  (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0xa3ca0)) tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cno_ff_ro_off_pstat : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FS_PSTAT_FP a.
Proof.
intros a Ha (r & Hr & Hrng).
assert (Hlo : 0xa3ca0 <= a).
{ unfold FS_PSTAT_FP in Hr. cbn [In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hrng; lia. }
destruct Ha as [(s & Hs & Hw & Hr2) | Hr2].
- pose proof (proj1 (forallb_forall _ _) cno_ff_ro_segs s Hs) as Hb. cbn beta in Hb.
  apply orb_true_iff in Hb. destruct Hb as [Hb | Hb]; [rewrite Hw in Hb; discriminate|].
  apply Z.leb_le in Hb. lia.
- unfold FS_RLO, FS_RHI in Hr2. lia.
Qed.
(* FS_PSTAT_FP never opens the sink: every range starts above 0 *)
Lemma cno_ff_pstat_closed : ~ YI16.sink_open_fp FS_PSTAT_FP.
Proof. apply sink_closed_pos. unfold FS_PSTAT_FP. repeat constructor; cbn; lia. Qed.

Section F. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
(* the callee's contract (S0 statement, lib/A/FSH_Fn_alloc.v fuzz_free_spec) *)
Hypothesis FFREE : fuzz_free_spec tfibsegs B.

(* ---- the read-only view at the call. FSW_rd.v:573 arodata_kept is this fact for a journal whose own list is
   EMPTY; the walk holds its fake frame at every call site, so its journal's own list is [(1, pos)] and that lemma
   does not apply by path. Only the journal's image clause is used, which does not look at own. (Kit request to the
   owner of FSW_rd.v: make `own` a parameter of arodata_kept; this lemma then goes away.) ---- *)
Lemma cno_ff_arodata : forall STK sp0 FP ly S Uc (Wc : world tfibsegs) memc mdc own ly' S' U'
  (W' : world tfibsegs) mem' md' k,
  ajournal tfibsegs B STK sp0 FP ly S Wc (unpoison Uc memc) mdc own ly' S' W' (unpoison U' mem') md' k ->
  ARU tfibsegs B ly S Uc Wc memc mdc -> ARU tfibsegs B ly' S' U' W' mem' md' ->
  ~ YI16.sink_open_fp FP ->
  (forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FP a) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H Wc) memc) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') mem').
Proof.
intros STK sp0 FP ly S Uc Wc memc mdc own ly' S' U' W' mem' md' k HJ HARU HARU' Hcl Hro HR a Ha Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
pose proof (fsw_roP_img a Ha) as Hi. pose proof (fs_segs_img a Hi) as Hl. unfold FS_IMG_END in Hl.
assert (A64 : 0 <= a < 2 ^ 64) by lia.
assert (NS : ~ (SHADOW_OFF <= a < kHighMemBeg)) by (unfold SHADOW_OFF; lia).
rewrite <- (cno_unp_out B ly' S' U' W' mem' md' a HARU' A64 NS).
rewrite (F3 a Hi Ho He (Hro a Ha) (fp_spares_closed FP a Hcl)).
rewrite (cno_unp_out B ly S Uc Wc memc mdc a HARU A64 NS).
exact (HR a Ha Ho He).
Qed.

(* ---- the callee's frame-pointer chain at the call: check_no_overread keeps s0 = sp0 with ra and s0 saved at
   sp0 - 8 / sp0 - 16, so the callee sees the walk's record on top of the walk's own chain (cno_chain) ---- *)
Lemma cno_ff_chain : forall cx k ly S U (W : world tfibsegs) mem md regs,
  cno_base B cx -> cno_J B cx k ly S W (unpoison U mem) md -> ARU tfibsegs B ly S U W mem md ->
  getr regs 2 = w64 (cno_sp1 cx) -> getr regs 8 = w64 (cno_sp0 cx) ->
  rdword (aview tfibsegs (w_H W) mem) (cno_sp0 cx - 8) = Some (raZ (c_regs cx)) ->
  rdword (aview tfibsegs (w_H W) mem) (cno_sp0 cx - 16) = Some (s0Z (c_regs cx)) ->
  achain ly (aview tfibsegs (w_H W) (unpoison U mem)) (spZ regs) (s0Z regs)
    ((cno_sp0 cx, raZ (c_regs cx), s0Z (c_regs cx)) :: c_ch cx).
Proof.
intros cx k ly S U W mem md regs HBASE HJ HARU Hsp Hs0 Hw8 Hw16.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HBASE as (HPRE0 & _ & _ & HTOP & _).
pose proof HPRE0 as (HAPU0 & _). pose proof HAPU0 as (HAP0 & OK0 & PO0).
pose proof HAP0 as (HAR0 & Hret0 & Hra40 & _ & _ & Hstk0 & _ & Hch0 & _).
pose proof (fsw_ARU B STK_check_no_overread (c_ly cx) (c_S cx) (c_U cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx)
  (c_ch cx) HAPU0) as HARU0.
destruct (cno_geom B cx k ly S W (unpoison U mem) md HJ)
  as (Hal16 & Hceil0 & H47 & Hsp1a & Hsp1b & Hsp1al & Ho16 & Hslo & Etop).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & _ & Hstat & _).
pose proof Hstat as (_ & _ & _ & _ & Hshi' & H47' & _ & Htop2' & Htop').
assert (FS : STK_check_no_overread = 16847) by reflexivity.
assert (Hsp0r : 0 <= cno_sp0 cx < 2 ^ 64) by (unfold cno_sp0, spZ; apply u64_range).
assert (Esp : spZ regs = cno_sp1 cx) by (unfold spZ; rewrite Hsp; unfold w64; apply wz; lia).
assert (Es0 : s0Z regs = cno_sp0 cx) by (unfold s0Z; rewrite Hs0; unfold w64; apply wz; lia).
rewrite Esp, Es0.
(* the two saved words, read through the unpoisoned view: they are stack bytes, far above the shadow band *)
assert (Hbr : forall b, cno_sp0 cx - 16 <= b -> b + 8 <= cno_sp0 cx ->
  rdword (aview tfibsegs (w_H W) (unpoison U mem)) b = rdword (aview tfibsegs (w_H W) mem) b).
{ intros b Hb1 Hb2. apply rdword_ext. intros i Hi.
  apply (cno_unp_out B ly S U W mem md (b + i) HARU); [lia | unfold SHADOW_OFF; lia]. }
apply (cno_chain ly (aview tfibsegs (w_H (c_W cx)) (unpoison (c_U cx) (c_mem cx)))
  (aview tfibsegs (w_H W) (unpoison U mem)) (cno_sp0 cx) (s0Z (c_regs cx)) (c_ch cx) (raZ (c_regs cx))
  (cno_sp1 cx)).
- apply (achain_ly_top (c_ly cx) ly); [exact Etop | exact Hch0].
- rewrite Etop. exact HTOP.
- lia.
- intros a Ha. apply F1; lia.
- rewrite (Hbr (cno_sp0 cx - 8) ltac:(lia) ltac:(lia)). exact Hw8.
- rewrite (Hbr (cno_sp0 cx - 16) ltac:(lia) ltac:(lia)). exact Hw16.
- exact Hra40.
- lia.
- apply (Z.mod_divide _ 8 ltac:(lia)). apply Z.mod_divide in Hal16 as [q Hq]; [|lia]. exists (2 * q). lia.
- lia.
Qed.

(* ---- the callee's premise at the call (FSW_ret.v:184 fsw_fpreU_atFP) ---- *)
Lemma cno_ff_pre : forall cx k ly S U (W : world tfibsegs) regs mem md,
  cno_base B cx -> cno_site B cx k ly S U W regs mem md ->
  fpreU tfibsegs B STK_fuzz_free ly S U W regs mem md
    ((cno_sp0 cx, raZ (c_regs cx), s0Z (c_regs cx)) :: c_ch cx).
Proof.
intros cx k ly S U W regs mem md HBASE HSITE.
destruct HSITE as (HJ & HARU & FH & Hsp & Hs0 & Hgp & Htp & Hret & Hra4 & Hw8 & Hw16).
pose proof HBASE as (HPRE0 & _).
pose proof HPRE0 as (HAPU0 & HRO0). pose proof HAPU0 as (HAP0 & OK0 & PO0).
pose proof HAP0 as (HAR0 & Hret0 & Hra40 & Hgp0 & Htp0 & _).
pose proof (fsw_ARU B STK_check_no_overread (c_ly cx) (c_S cx) (c_U cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx)
  (c_ch cx) HAPU0) as HARU0.
destruct (cno_geom B cx k ly S W (unpoison U mem) md HJ)
  as (Hal16 & Hceil0 & H47 & Hsp1a & Hsp1b & Hsp1al & Ho16 & Hslo & Etop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : STK_check_no_overread = 16847) by reflexivity.
assert (Hsp0r : 0 <= cno_sp0 cx < 2 ^ 64) by (unfold cno_sp0, spZ; apply u64_range).
assert (Esp : spZ regs = cno_sp1 cx) by (unfold spZ; rewrite Hsp; unfold w64; apply wz; lia).
assert (HSTK : STK_fuzz_free + 191 <= STK_check_no_overread) by (vm_compute; discriminate).
apply (fsw_fpreU_atFP B STK_check_no_overread (cno_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) U (c_W cx)
  (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(1, c_fpos cx)] ly S W mem md k regs STK_fuzz_free
  (cno_sp1 cx - cno_sp0 cx) _ HJ HARU).
- exact (cno_ff_arodata STK_check_no_overread (cno_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_U cx) (c_W cx)
    (c_mem cx) (c_md cx) [(1, c_fpos cx)] ly S U W mem md k HJ HARU0 HARU cno_ff_pstat_closed
    cno_ff_ro_off_pstat HRO0).
- lia.
- exact Ho16.
- lia.
- vm_compute; discriminate.
- lia.
- exact Hret.
- exact Hra4.
- rewrite Hgp. exact Hgp0.
- rewrite Htp. exact Htp0.
- exact (cno_ff_chain cx k ly S U W mem md regs HBASE HJ HARU Hsp Hs0 Hw8 Hw16).
Qed.

(* ---- the step after the call, shared by the two arms: the journal composition (FSW_K3.v:215 fsw_ajournal_sub4),
   ARU at the callee's U', and the bytes cno_ret asks the step to keep (the walk's saved words and slots, its fake
   frame and the frame's sixteen shadow bytes, and every block live before and after) ---- *)
Lemma cno_ff_after : forall cx k ly S U (W : world tfibsegs) regs mem md FP1 kc ly' S' U'
  (W' : world tfibsegs) mem' md',
  cno_base B cx -> cno_J B cx k ly S W (unpoison U mem) md -> ARU tfibsegs B ly S U W mem md ->
  FSupoisonU.fs_heads B ly S U -> FSupoisonU.fs_heads B ly' S' U' ->
  getr regs 2 = w64 (cno_sp1 cx) ->
  ajournal tfibsegs B STK_fuzz_free (spZ regs) FP1 ly S W (unpoison U mem) md [] ly' S' W'
    (unpoison U' mem') md' kc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  (forall a, inFP FP1 a ->
     (inFP FS_PSTAT_FP a /\ exists b m, In (b, m) (ablocks B ly S) /\ b <= a < b + req_size m) \/
     in_tmp_block (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly S) a \/
     (inFP FS_PSTAT_FP a /\ in_img tfibsegs a)) ->
  (forall a, inFP FP1 a -> ~ (cno_F cx <= a < cno_F cx + 128)) ->
  (forall a, inFP FP1 a -> ~ (cno_SF cx <= a < cno_SF cx + 16)) ->
  (forall b m i, In (b, m) (ablocks B ly S) -> In (b, m) (ablocks B ly' S') -> 0 <= i < req_size m ->
     ~ inFP FP1 (b + i)) ->
  cno_J B cx (k + kc) ly' S' W' (unpoison U' mem') md' /\ ARU tfibsegs B ly' S' U' W' mem' md' /\
  (forall a, cno_zone cx a -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
  (forall b m i, In (b, m) (ablocks B ly S) -> In (b, m) (ablocks B ly' S') -> 0 <= i < req_size m ->
     aview tfibsegs (w_H W') mem' (b + i) = aview tfibsegs (w_H W) mem (b + i)).
Proof.
intros cx k ly S U W regs mem md FP1 kc ly' S' U' W' mem' md'
  HBASE HJ HARU FH FH' Hsp HJc OK' PO' HFP HFPF HFPS HFPB.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HBASE as (HPRE0 & _). pose proof HPRE0 as (HAPU0 & _).
pose proof HAPU0 as (HAP0 & OK0 & PO0). pose proof HAP0 as (HAR0 & _).
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
destruct (cno_geom B cx k ly S W (unpoison U mem) md HJ)
  as (Hal16 & Hceil0 & H47 & Hsp1a & Hsp1b & Hsp1al & Ho16 & Hslo & Etop).
destruct (cno_frame B cx k ly S U W mem md HAR0 HJ HARU)
  as (Hinfr & EF & HF4096 & HFceil & HFapp & HFal & HSF1 & HSF2).
assert (FS : STK_check_no_overread = 16847) by reflexivity.
assert (Hsp0r : 0 <= cno_sp0 cx < 2 ^ 64) by (unfold cno_sp0, spZ; apply u64_range).
destruct HFapp as (_ & HFlh). unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFlh.
assert (Esp : spZ regs = cno_sp1 cx) by (unfold spZ; rewrite Hsp; unfold w64; apply wz; lia).
assert (HSTK : STK_fuzz_free + 191 <= STK_check_no_overread) by (vm_compute; discriminate).
(* the composed journal and ARU at the end *)
assert (HJ2 : cno_J B cx (k + kc) ly' S' W' (unpoison U' mem') md').
{ unfold cno_J. change [(1, c_fpos cx)] with ([] ++ [(1, c_fpos cx)]).
  apply (fsw_ajournal_sub4 B STK_check_no_overread (cno_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(1, c_fpos cx)] ly S W (unpoison U mem) md k
    STK_fuzz_free (spZ regs) FP1 [] ly' S' W' (unpoison U' mem') md' kc HJ HJc ltac:(lia) ltac:(lia)).
  intros a Ha. destruct (HFP a Ha) as [H1 | [H1 | H1]];
    [left; exact H1 | right; left; exact H1 | right; right; left; exact H1]. }
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md')
  by (split; [exact (proj1 HJ2) | split; [exact OK' | exact PO']]).
split; [exact HJ2|]. split; [exact HARU'|].
(* the callee journal's own keep clauses *)
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & _ & G4 & _).
(* the stack window of the walk: the saved words and the three slots lie ABOVE the callee's sp *)
assert (KSTK : forall a, cno_sp1 cx <= a -> a < cno_sp0 cx ->
  aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a).
{ intros a Ha1 Ha2.
  assert (A64 : 0 <= a < 2 ^ 64) by lia.
  assert (NS : ~ (SHADOW_OFF <= a < kHighMemBeg)) by (unfold SHADOW_OFF, kHighMemBeg; lia).
  rewrite <- (cno_unp_out B ly' S' U' W' mem' md' a HARU' A64 NS).
  rewrite <- (cno_unp_out B ly S U W mem md a HARU A64 NS).
  apply G1; [lia | rewrite Esp; lia]. }
(* the fake frame and its shadow: the callee journal's frames clause, off its footprint *)
assert (KFR : forall a, (cno_F cx <= a < cno_F cx + 128 \/ cno_SF cx <= a < cno_SF cx + 16) ->
  aview tfibsegs (w_H W') (unpoison U' mem') a = aview tfibsegs (w_H W) (unpoison U mem) a).
{ intros a Ha. apply (G4 1 (c_fpos cx) a Hinfr).
  - unfold frame_rng, in_zr. cbn [fst snd]. rewrite <- EF.
    change (fs_frame_bytes 1) with 128. change (128 / 8) with 16.
    unfold cno_SF in Ha. destruct Ha as [Ha | Ha]; [left; exact Ha | right; exact Ha].
  - intros Hin. destruct Ha as [Ha | Ha]; [exact (HFPF a Hin Ha) | exact (HFPS a Hin Ha)]. }
split.
{ intros a Ha. unfold cno_zone in Ha.
  destruct Ha as [Ha | [Ha | [Ha | Ha]]].
  - apply KSTK; lia.
  - apply KSTK; lia.
  - (* the frame: application memory, so the unpoisoned view and the machine's agree at both ends *)
    assert (A64 : 0 <= a < 2 ^ 64) by lia.
    assert (NS : ~ (SHADOW_OFF <= a < kHighMemBeg)).
    { unfold SHADOW_OFF, kHighMemBeg. destruct HFlh as [X | [X Y]]; lia. }
    rewrite <- (cno_unp_out B ly' S' U' W' mem' md' a HARU' A64 NS).
    rewrite <- (cno_unp_out B ly S U W mem md a HARU A64 NS).
    apply KFR. left. exact Ha.
  - (* the frame's sixteen shadow bytes: no range of U or of U' covers them (cno_sf_not_ush) *)
    assert (A64 : 0 <= a < 2 ^ 64)
      by (unfold SHADOW_OFF in HSF1; unfold kHighMemBeg in HSF2; lia).
    rewrite <- (cno_unp_off W' U' mem' a A64
      (cno_sf_not_ush B cx (k + kc) ly' S' U' W' mem' md' a HAR0 HJ2 HARU' FH' Ha)).
    rewrite <- (cno_unp_off W U mem a A64
      (cno_sf_not_ush B cx k ly S U W mem md a HAR0 HJ HARU FH Ha)).
    apply KFR. right. exact Ha. }
(* a block live before and after: the callee journal's blocks clause, off its footprint; block bytes are
   application memory, so the unpoisoned views and the machines' agree *)
intros b m i Hb0 Hb1 Hi.
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md b m HAR Hb0) as (_ & Hb4096 & Hbceil & Hbapp & _).
destruct Hbapp as (_ & Hblh). unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hblh.
assert (A64 : 0 <= b + i < 2 ^ 64) by lia.
assert (NS : ~ (SHADOW_OFF <= b + i < kHighMemBeg)).
{ unfold SHADOW_OFF, kHighMemBeg. destruct Hblh as [X | [X Y]]; lia. }
rewrite <- (cno_unp_out B ly' S' U' W' mem' md' (b + i) HARU' A64 NS).
rewrite <- (cno_unp_out B ly S U W mem md (b + i) HARU A64 NS).
exact (G2 b m i Hb0 Hb1 Hi (HFPB b m i Hb0 Hb1 Hi)).
Qed.

(* ================= the call step ================= *)
Hypothesis IMG : fs_img_facts tfibsegs B.


Lemma cno_call_ffree : cno_call_ffree_T B.
Proof.
unfold cno_call_ffree_T.
intros cx k ly S U W regs mem md p n live peak cnt fail HBASE HSITE Hra Hap Hglob Harm Hk1.
pose proof HSITE as (HJ & HARU & FH & Hsp & Hs0 & Hgp & Htp & Hret & Hra4 & Hw8 & Hw16).
pose proof HBASE as (HPRE0 & FH0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev0 & _).
pose proof HPRE0 as (HAPU0 & HRO0). pose proof HAPU0 as (HAP0 & OK0 & PO0).
pose proof HAP0 as (HAR0 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
destruct (cno_geom B cx k ly S W (unpoison U mem) md HJ)
  as (Hal16 & Hceil0 & H47 & Hsp1a & Hsp1b & Hsp1al & Ho16 & Hslo & Etop).
destruct (cno_frame B cx k ly S U W mem md HAR0 HJ HARU)
  as (Hinfr & EF & HF4096 & HFceil & HFapp & HFal & HSF1 & HSF2).
assert (FS : STK_check_no_overread = 16847) by reflexivity.
assert (Hsp0r : 0 <= cno_sp0 cx < 2 ^ 64) by (unfold cno_sp0, spZ; apply u64_range).
assert (Esp : spZ regs = cno_sp1 cx) by (unfold spZ; rewrite Hsp; unfold w64; apply wz; lia).
(* the callee's room: the walk's journal bounds the events it has spent *)
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
assert (HEV : st_nev S + 1 <= EV_MAX) by (unfold EV_check_no_overread in *; lia).
pose proof (cno_ff_pre cx k ly S U W regs mem md HBASE HSITE) as HPREc.
(* the call *)
eapply SRr_mono.
{ exact (FFREE ly S U W regs mem md ((cno_sp0 cx, raZ (c_regs cx), s0Z (c_regs cx)) :: c_ch cx) p n live peak cnt
    fail Hap Hglob FH
    ltac:(destruct Harm as [-> | (Hp0 & HU & Hrb & Hnl & _)];
          [left; split; [reflexivity | exact HPREc]
          |right; split; [exact Hp0|]; destruct HU as (U1 & U2 & HU); exists U1, U2;
           split; [exact HU|]; split; [exact HPREc | split; [exact Hrb | exact Hnl]]])
    ltac:(intros _; exact HEV)). }
cbv beta. intros W' c' _ [(Hp0 & HPOST) | (Hp0 & U1 & U2 & HU & HPOST)].
- (* ---- the p = 0 arm: the callee returns at once; no event, no block, U unchanged ---- *)
  left. split; [exact Hp0|].
  destruct HPOST as (ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HP' & Eab' & FH' & Hglob').
  unfold cno_ret. exists ly', S', regs', mem', md'.
  split; [rewrite Ec; unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
  destruct (cno_ff_after cx k ly S U W regs mem md [] 0 ly' S' U W' mem' md' HBASE HJ HARU FH FH'
    Hsp HJc OK' PO'
    ltac:(intros a (r & [] & _))
    ltac:(intros a (r & [] & _)) ltac:(intros a (r & [] & _)) ltac:(intros b m i _ _ _ (r & [] & _)))
    as (HJ2 & HARU2 & KZ & KB).
  split; [exact HJ2|].
  split; [exact HARU2|]. split; [exact FH'|]. split; [exact HP'|].
  split; [intros a Ha _; exact (KZ a Ha)|].
  split; [intros b m i Hb0 Hb1 Hi _; exact (KB b m i Hb0 Hb1 Hi)|].
  split; [exact Eab' | exact Hglob'].
- (* ---- the p <> 0 arm: one event, the head leaves U, the block leaves ablocks ---- *)
  destruct Harm as [Hz | (_ & _ & Hrb & Hnl & Hnew)]; [exfalso; exact (Hp0 Hz)|].
  destruct Hrb as (Hbk & Hp16 & Hn0 & _).
  right. split; [exact Hp0|]. exists U1, U2. split; [exact HU|].
  destruct HPOST as (ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HP' & Esplit & FH' & Hglob').
  unfold cno_ret. exists ly', S', regs', mem', md'.
  split; [rewrite Ec; unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
  (* the freed block is the walk's own: its bytes are in_tmp_block of the ENTRY blocks *)
  assert (Hrq : req_size (n + HEAD) = n + HEAD)
    by (unfold req_size, HEAD; destruct (Z.eqb_spec (n + 16) 0); lia).
  destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md _ _ HAR Hbk)
    as (_ & Hb4096 & Hbceil & Hbapp & _).
  rewrite Hrq in Hbceil, Hbapp.
  destruct Hbapp as (_ & Hblh). unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hblh.
  assert (HFPcase : forall a, inFP (FS_PSTAT_FP ++ ablocks_fp [(p - HEAD, n + HEAD)]) a ->
    (inFP FS_PSTAT_FP a /\ in_img tfibsegs a) \/
    (p - HEAD <= a < p - HEAD + (n + HEAD) /\ ~ in_img tfibsegs a)).
  { intros a (r & Hr & Hrng). apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    - left. split; [exists r; split; [exact Hr | exact Hrng]|].
      assert (Hin8 : exists g, In (g, g + 8) FS_PSTAT_FP /\ g <= a < g + 8).
      { unfold FS_PSTAT_FP in Hr |- *. cbn [In] in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hrng;
          [exists 0xa3ca0 | exists 0x5da5c0 | exists 0x5da5e0 | exists 0x5da600];
          (split; [cbn [In]; tauto | lia]). }
      destruct Hin8 as (g & Hg & Ha8).
      exact (proj1 (cno_pstat_byte B g a Hg Ha8 IMG)).
    - unfold ablocks_fp in Hr. cbn [map In] in Hr. destruct Hr as [<- | []].
      cbn [fst snd] in Hrng. rewrite Hrq in Hrng.
      right. split; [exact Hrng|].
      exact (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md _ _ a HAR Hbk ltac:(rewrite Hrq; lia)). }
  destruct (cno_ff_after cx k ly S U W regs mem md (FS_PSTAT_FP ++ ablocks_fp [(p - HEAD, n + HEAD)]) 1
    ly' S' (U1 ++ U2) W' mem' md' HBASE HJ HARU FH FH' Hsp HJc OK' PO')
    as (HJ2 & HARU2 & KZ & KB).
  + (* the callee's footprint: the statics, or the freed block, which is a block the walk itself made *)
    intros a Ha. destruct (HFPcase a Ha) as [(H1 & H2) | (H1 & _)].
    * right; right. split; [exact H1 | exact H2].
    * right; left. exists (p - HEAD), (n + HEAD). split; [exact Hbk|]. split; [exact Hnew|].
      rewrite Hrq. exact H1.
  + (* the frame is no static (the statics are image bytes, a frame byte is not) and no byte of the freed block *)
    intros a Ha HaF. destruct (HFPcase a Ha) as [(H1 & H2) | (H1 & H2)].
    * exact (frm_img tfibsegs B LAWS ly S W (unpoison U mem) md 1 (c_fpos cx) a HAR Hinfr
               ltac:(change (fs_frame_bytes 1) with 128; rewrite <- EF; lia) H2).
    * pose proof (sep_block_frame tfibsegs B LAWS ly S W (unpoison U mem) md _ _ 1 (c_fpos cx) HAR Hbk Hinfr) as D.
      unfold zdisjoint in D. cbn [fst snd] in D. rewrite Hrq in D.
      change (fs_frame_bytes 1) with 128 in D. rewrite <- EF in D. lia.
  + (* the frame's shadow bytes are in the shadow band: the statics are below it, the block is application memory *)
    intros a Ha HaS. destruct (HFPcase a Ha) as [(H1 & H2) | (H1 & H2)].
    * destruct H1 as (r & Hr & Hrng).
      assert (Hin8 : exists g, In (g, g + 8) FS_PSTAT_FP /\ g <= a < g + 8).
      { unfold FS_PSTAT_FP in Hr |- *. cbn [In] in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hrng;
          [exists 0xa3ca0 | exists 0x5da5c0 | exists 0x5da5e0 | exists 0x5da600];
          (split; [cbn [In]; tauto | lia]). }
      destruct Hin8 as (g & Hg & Ha8).
      pose proof (proj2 (proj2 (proj2 (cno_pstat_byte B g a Hg Ha8 IMG)))) as Hbelow. lia.
    * unfold SHADOW_OFF in HSF1. unfold kHighMemBeg in HSF2. destruct Hblh as [X | [X Y]]; lia.
  + (* a block live before AND after is not the freed one: the freed block's slot is gone from ablocks ly' S'
       (the callee's split), so the live one sits at another position of ablocks ly S, and two positions of
       ablocks are disjoint (sep_blocks_pos) *)
    intros b m i Hb0 Hb1 Hi Ha. destruct (HFPcase (b + i) Ha) as [(H1 & H2) | (H1 & H2)].
    * exact (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md b m (b + i) HAR Hb0 ltac:(lia) H2).
    * destruct Esplit as (l1 & l2 & Es1 & Es2). rewrite Es2 in Hb1.
      apply in_app_or in Hb1. destruct Hb1 as [Hb1 | Hb1]; apply in_split in Hb1 as (q1 & q2 & Eq).
      -- pose proof (sep_blocks_pos tfibsegs B LAWS ly S W (unpoison U mem) md (b, m) (p - HEAD, n + HEAD)
           q1 q2 l2 HAR ltac:(rewrite Es1, Eq, <- app_assoc; reflexivity)) as D.
         unfold zdisjoint, block_rng in D. cbn [fst snd] in D. rewrite Hrq in D. lia.
      -- pose proof (sep_blocks_pos tfibsegs B LAWS ly S W (unpoison U mem) md (p - HEAD, n + HEAD) (b, m)
           l1 q1 q2 HAR ltac:(rewrite Es1, Eq; reflexivity)) as D.
         unfold zdisjoint, block_rng in D. cbn [fst snd] in D. rewrite Hrq in D. lia.
  + split; [exact HJ2|]. split; [exact HARU2|]. split; [exact FH'|]. split; [exact HP'|].
    split; [intros a Ha _; exact (KZ a Ha)|].
    split; [intros b m i Hb0 Hb1 Hi _; exact (KB b m i Hb0 Hb1 Hi)|].
    split; [exact Esplit | exact Hglob'].
Qed.
End F.
