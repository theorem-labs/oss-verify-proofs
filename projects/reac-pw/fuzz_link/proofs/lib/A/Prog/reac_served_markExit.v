(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextEntry), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/NextEntry.v at a working branch af735a950e2 (blob 8725db69d2a; the walk was ported from blob 7788bf8f6e4 at a working branch afd75724b5b, which differs from it only by 4 added and 0 removed lines, the licence header), restated over image B's listing, addresses and walk layer (lib/B/Prog) against GrantBContracts.v; frame 96 with twelve saved registers, UBSan traps T1 and T2, and the .rodata divisor read at 0x85fa4 (IMG_NEXT_DIV3) *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/NextEntry.v, with its module paths and module names changed; 542 of its 591 lines of code are new or changed and 711 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_link_alias_readExit.v, with its module paths and module names changed; 882 of its 941 lines of code are new or changed and 532 lines of the source are left out. *)
(* reac_served_mark (fuzz_link.asan 0x895a8) on image A: THE RESTORE AND EXIT PIECES of its walk,
   `srm_exit_obl` and `srm_restore_obl` of lib/A/Prog/reac_served_markDefs.v.

   From the EXIT cut +0x360 (0x89908) the code
     +0x360..+0x368  stores the retired magic 0x45e0360e at F + 0 (sd a0,0(s9), s9 = s3 = F)
     +0x36c          `beqz s3` -> +0x388, not taken: 4096 <= F (the range fact on F's atom decides it)
     +0x370..+0x378  meta_fill_f5(shadow(F), 64) (0x55f7c)
     +0x37c..+0x380  `ld a0,0x1f8(s3); sb zero,0(a0)`: the inline release of the frame's flag byte
     +0x458..+0x494  a0 := s5; sp := s0 - 0x80; the twelve restores; `ret`
   and from the RESTORE cut +0x2cc (0x89874) the 36 `sb a0,i(s2)` with a0 = -8 put the two buffers' shadow
   back to 0xf8 (Defs `srm_bufsh_off`: SH + 4 .. SH + 7 and SH + 12 .. SH + 43) and fall into the EXIT cut,
   which is why `srm_restore_ok` takes `srm_exit_obl` and ends by applying it.

   The runs are the plain gx runs of lib/A/Prog/LinkWalkSide.v (`paj_run_call_plain_x`, `paj_run_to_plain_x`,
   `paj_flag_plain_x`); meta_fill_f5 is its `aj_gx_set_shadow_at` over the Section hypothesis
   `aset_shadow_realizes pa_segs B 0x55f7c 0xf5` (discharged at the image by lib/A/Rt/SetShadow.v
   `link_set_shadow_f5`); the return is LinkPaLib.v `paj_ret_at`, the post LinkWalkSide.v `apost_side_gen`
   lifted to `apostF` by link_amem.v `apostF_of_apost`.

   The memory algebra is two named lemmas. `srx_pf_move` moves a cut's result `srm_pf` across a step that
   changes only bytes of the call's side frame (its range, its shadow, its flag byte: LinkWalkSide.v
   `aside_rng`); its pieces are the shared ones -- lib/A/Prog/reac_served_markXfer.v (`xfer_gnl_img`,
   `xfer_amemfile_k`, `xfer_amarks`, the xf_* byte algebra) and lib/A/Prog/LinkWalkShadow.v (`akb_not_side`) --
   and the two objects of the Post that Xfer does not carry in this shape, the fake kernel's bytes
   (`anlk_at`) and its interface table (`aiftab_at`), move here. `srx_base_move` re-states `srm_base` at the
   state the RESTORE run reaches.

   Model (read, not imported): reac_link_alias_write's exit, the same code shape with 11 saves.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.reac_pw.fuzz_link.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 SetShadowDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AB1v AF0m AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi LinkWalkSide LinkWalkShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c reac_served_markDefs reac_served_markXfer
reac_served_markUniq.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   0. The symbolic states
   Atoms 0..31 are the registers at the cut; 32..43 the twelve saved words (ra, s0, s1, s2 .. s10 of the entry);
   44 the frame's flag address (the word at F + 504). s3 = s9 = F is atom 19, s2 = shadow(F) is atom 18,
   s0 = the entry sp is atom 8.
   ========================================================================== *)
Definition srx_FR : YP09.region := YP09.mkRegion (Some 19%nat) 0 512 0 8 [YP09.mkChunk 504 (CVal 8 (SOff 44 0))].
Definition srx_FL0 : YP09.region := YP09.mkRegion (Some 44%nat) 0 1 0 0 [].
Definition srx_FL : YP09.region := YP09.mkRegion (Some 44%nat) 0 1 0 1 [].
Definition srx_saves_chunks : list YP09.chunk :=
  map (fun j => YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0))) (seq 0 12).
Definition srx_saves : YP09.region := YP09.mkRegion (Some 8%nat) (-96) 0 0 0 srx_saves_chunks.
Definition srx_facts : facts := mkFacts [(19%nat, HPTR 6); (44%nat, HPTR 0)] [] [].
Definition srx_ssE0 : sstate := mkSS SRM_CUT_EXIT sr_atoms [srx_FR; srx_FL0; srx_saves] None srx_facts.

(* the RESTORE cut: the two buffers' shadow bytes, inside F's 64 shadow bytes *)
Definition srx_SHR : YP09.region := YP09.mkRegion (Some 18%nat) 0 64 4 44 [].
Definition srx_factsR : facts := mkFacts [(18%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 3)] [] [].
Definition srx_ssR : sstate := mkSS SRM_CUT_RESTORE sr_atoms [srx_SHR] None srx_factsR.

(* the registers the epilogue restores, and gp / tp / s11, which no step of the two pieces writes *)
Definition srx_kregs : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv].

(* split exactly the n top conjunctions of a right-nested conjunction, never unfolding a definition that hides
   another conjunction (akept, ajournal_gx) *)
Ltac srx_splitn n := lazymatch n with O => idtac | S ?m => split; [| srx_splitn m] end.

(* ==========================================================================
   1. Small helpers
   ========================================================================== *)
Lemma srx_ms_eta `{fx : YK11.FPState} : forall ms : machine_state,
  ms_fregs ms = fp_regs -> ms_svc_pending ms = None -> ms_resv ms = None -> ms_fcsr ms = fp_csr ->
  ms = mkst (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (ms_rom ms).
Proof. intros [] H1 H2 H3 H4; cbn in *; subst; reflexivity. Qed.

Lemma srx_wvb_fds_fs : forall l X m,
  m_fds (with_vm_backing l X m) = m_fds m /\ m_fs (with_vm_backing l X m) = m_fs m.
Proof. intros l X []. split; reflexivity. Qed.

Lemma srx_sbm_fds_fs : forall m m', same_but_materialized m m' -> m_fds m' = m_fds m /\ m_fs m' = m_fs m.
Proof. intros m m' H. rewrite H. apply srx_wvb_fds_fs. Qed.

Lemma srx_apresent_grows : forall (H : word -> bool) (m m' : word -> option byte) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a HG [Hh [b Hb]]. split; [exact Hh|].
specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG. rewrite Hh in HG. rewrite Hb in HG.
destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; apply HG; [discriminate | reflexivity]].
Qed.

Lemma srx_grows_of_apresent : forall (H : word -> bool) (m m' : word -> option byte),
  (forall a, apresent H m a -> apresent H m' a) -> mem_grows (mrestrict H m) (mrestrict H m').
Proof.
intros H m m' HP x Hx. unfold mrestrict in *.
destruct (H x) eqn:Eh; [exact Hx|].
destruct (m x) as [b|] eqn:Em; [|exfalso; apply Hx; reflexivity].
assert (Hp : apresent H m (bv_unsigned x)).
{ split; [rewrite Z_to_bv_bv_unsigned; exact Eh | exists b; rewrite Z_to_bv_bv_unsigned; exact Em]. }
destruct (HP _ Hp) as [_ [b' Hb']]. rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate.
Qed.

(* the three byte classes of the side frame (SRM_CID, fpos), unfolded *)
Lemma srx_side_unfold : forall ly fpos a,
  aside_rng ly SRM_CID fpos a <->
  (frame_addr ly SRM_CID fpos <= a < frame_addr ly SRM_CID fpos + 512) \/
  (SHADOW_OFF + frame_addr ly SRM_CID fpos / 8 <= a < SHADOW_OFF + frame_addr ly SRM_CID fpos / 8 + 64) \/
  a = flag_addr ly SRM_CID fpos.
Proof.
intros ly fpos a. unfold aside_rng, in_zr, frame_rng, shadow_addr. cbn [fst snd].
change (fs_frame_bytes SRM_CID) with 512. change (512 / 8) with 64. tauto.
Qed.

(* a word read is the word it was when its eight bytes did not change *)
Lemma srx_rdword_agree : forall (rd rd' : reader) a,
  (forall x, a <= x < a + 8 -> rd' x = rd x) -> rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. unfold rdword.
rewrite (H a ltac:(lia)), (H (a + 1) ltac:(lia)), (H (a + 2) ltac:(lia)), (H (a + 3) ltac:(lia)),
  (H (a + 4) ltac:(lia)), (H (a + 5) ltac:(lia)), (H (a + 6) ltac:(lia)), (H (a + 7) ltac:(lia)).
reflexivity.
Qed.

(* ==========================================================================
   2. The walk
   ========================================================================== *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HV : LinkVals.
(* the runtime's symbols of image A (lib/A/AF0m.v), instance lib/A/AD2l.v PcapB_syms *)
Hypothesis TB : PcapSyms B.
(* the segments the listing is certified against (the library walks' convention); the link PAImg instance
   discharges it by reflexivity. Reached only through Xfer's g_nl facts. *)
Hypothesis HSEGS : SEGS = tfibsegs.
(* the relro window lies in the image (the top file discharges it from HSEGS and PcapRelroA) *)
Hypothesis RELRO_IMG : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.
(* meta_fill_f5 (0x55f7c): discharged at the image by lib/A/Rt/SetShadow.v link_set_shadow_f5 *)
Hypothesis ASSF5 : aset_shadow_realizes SEGS B 0x55f7c 0xf5.

(* the symbol tree a run lemma evaluates over, read off its own type: a fact about the run must name THIS tree
   (stating it at another name for the same tree sends the unifier into evaluating the run) *)
Ltac srx_tpi RUN :=
  lazymatch type of RUN with
  | context [sym_runN_pi ?t _ _] => t
  | context [sym_run_toN_pi ?t _ _ _] => t
  end.

Let SLOW := @pa_segs_low rc link_listing PI.
Let SIMG := @pa_img_range rc link_listing PI.

(* the shared facts, applied without counting the Section prefix *)
Ltac srxh := first [ eassumption | exact LAWS | exact SLOW | exact SIMG | exact TB | exact HSEGS | exact RELRO_IMG ].

(* ---- the entry's view of a byte the call keeps ---- *)
Lemma srx_view_kept : forall cx fpos ly3 S3 (W3 : world SEGS) (ms3 : machine_state) md3 a,
  srm_pre SK B cx -> srm_base fx SK B cx fpos (srm_E cx) ly3 S3 W3 ms3 md3 ->
  akb SEGS B (sm_lyc cx) (sm_Sc cx) (srm_sp cx - REAC_SERVED_MARK_AK) (srm_sp cx) a ->
  ~ srm_E cx a -> ~ aside_rng (sm_lyc cx) SRM_CID fpos a ->
  aview SEGS (w_H W3) (ms_mem ms3) a = aview SEGS (w_H (sm_W cx)) (sm_memc cx) a.
Proof.
intros cx fpos ly3 S3 W3 ms3 md3 a HPRE HBASE Hakb HnE Hns.
unfold srm_base in HBASE. cbv zeta in HBASE.
destruct HBASE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HK3 & _).
destruct HPRE as ((HJ & _) & _ & _).
eapply akept_akb_gx; [exact HJ | exact HK3 | exact Hakb | intros [HE | Hs]; [exact (HnE HE) | exact (Hns Hs)]].
Qed.

(* ---- g_nl's bytes: in the image, outside the runtime's statics and errno, hence akb ---- *)
Lemma srx_gnl_img : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof. intros a Ha. eapply xfer_gnl_img; srxh. Qed.

Lemma srx_gnl_akb : forall lyc Sc slo shi a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> akb SEGS B lyc Sc slo shi a.
Proof. intros lyc Sc slo shi a Ha. destruct (srx_gnl_img a Ha) as (H1 & H2 & H3). right. right. left. auto. Qed.

(* ---- the write set: where it lies ---- *)
Lemma srx_E_inv : forall cx a, srm_E cx a ->
  (LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4) \/
  (srm_mk cx <> 0 /\ srm_mk cx <= a < srm_mk cx + MK_SIZE) \/
  (sm_sink cx <> 0 /\ sm_sink cx <= a < sm_sink cx + AMF_BLOCK).
Proof.
intros cx a HE. unfold srm_E, srm_wr, reac_served_mark_awr, inFP in HE.
destruct HE as (r & Hr & Ha). cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha.
- left. exact Ha.
- right. left. unfold aivl in Ha. cbn [fst snd] in Ha.
  destruct (Z.eqb_spec (aarg (sm_regs cx) 0) 0) as [E0|E0]; [lia|].
  unfold srm_mk. split; [exact E0 | exact Ha].
- right. right. unfold aivl in Ha. cbn [fst snd] in Ha.
  destruct (Z.eqb_spec (sm_sink cx) 0) as [E0|E0]; [lia | split; [exact E0 | exact Ha]].
Qed.

(* an image byte outside g_nl's request ring is no byte of the write set: the two other objects of the write
   set are heap blocks of the call (YCbq.v blk_img) *)
Lemma srx_img_notE : forall cx a, srm_pre SK B cx -> in_img SEGS a ->
  ~ (LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4) -> ~ srm_E cx a.
Proof.
intros cx a HPRE Hi Hg HE.
destruct HPRE as (HAP & _ & HAPRE).
destruct HAP as (HJ & _).
assert (HARc : AR SEGS B (sm_lyc cx) (sm_Sc cx) (sm_W cx) (sm_memc cx) (sm_mdc cx))
  by (eapply ajournal_gx_AR; exact HJ).
destruct HAPRE as (kb0 & tb0 & nm0 & k00 & HinSink & HLed & _ & _ & _ & _ & _ & _ & _ & Hsink0 & _).
destruct (srx_E_inv cx a HE) as [H1 | [(Hmk0 & Hmk) | (Hsk0 & Hsk)]].
- exact (Hg H1).
- destruct (HLed Hmk0) as (HinMk & _).
  assert (NIMG : ~ in_img SEGS a)
    by (eapply blk_img; try first [exact LAWS | exact HARc | exact HinMk | exact Hmk]).
  exact (NIMG Hi).
- assert (NIMG : ~ in_img SEGS a)
    by (eapply blk_img; try first [exact LAWS | exact HARc | exact HinSink | exact Hsk]).
  exact (NIMG Hi).
Qed.

(* ---- the fake kernel's bytes and its interface table across a step ---- *)
Lemma srx_anlk_move : forall (W3 : world SEGS) m3 (W5 : world SEGS) m5 bs,
  anlk_at SEGS (rdW W3 m3) LA_G_NL bs ->
  (forall x, LA_G_NL <= x < LA_G_NL + NK_SIZE -> mbyte SEGS (rdW W5 m5) x = mbyte SEGS (rdW W3 m3) x) ->
  (forall x, LA_G_NL <= x < LA_G_NL + NK_SIZE -> writable_at SEGS (rdW W5 m5) x) ->
  anlk_at SEGS (rdW W5 m5) LA_G_NL bs.
Proof.
intros W3 m3 W5 m5 bs [[U R] L] Hk Hw. split; [|exact L]. split.
- apply (xf_abytes SEGS (rdW W3 m3) (rdW W5 m5) LA_G_NL bs); [|exact U].
  intros i Hi. apply Hk. rewrite L in Hi. unfold NK_SIZE in *. lia.
- intros i Hi. apply Hw. unfold NK_SIZE in *. lia.
Qed.

Lemma srx_aiftab_move : forall (W0 : world SEGS) m0 (W5 : world SEGS) m5 bs bs' tab,
  aiftab_at SEGS (rdW W0 m0) LA_G_NL bs tab -> nk_n_if bs' = nk_n_if bs ->
  (forall x, LA_G_NL + NK_IF_NAME <= x < LA_G_NL + NK_SIZE ->
     mbyte SEGS (rdW W5 m5) x = mbyte SEGS (rdW W0 m0) x) ->
  (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
     au64_at SEGS (rdW W0 m0) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
     acstr_at SEGS (rdW W0 m0) p n2 ->
     forall x, p <= x <= p + Z.of_nat (length n2) ->
       mbyte SEGS (rdW W5 m5) x = mbyte SEGS (rdW W0 m0) x) ->
  aiftab_at SEGS (rdW W5 m5) LA_G_NL bs' tab.
Proof.
intros W0 m0 W5 m5 bs bs' tab (L & L80 & E) Hn DC DS.
split; [rewrite Hn; exact L|]. split; [exact L80|]. intros i n2 ix Hi.
destruct (E i n2 ix Hi) as (R & p & P & Pz & C & I).
assert (Li : (i < length tab)%nat) by (apply nth_error_Some; congruence).
assert (Hli : Z.of_nat i < Z.of_nat (length tab)) by lia.
split; [exact R|]. exists p. split; [|split; [exact Pz | split]].
- apply (xf_val_mem SEGS (rdW W0 m0) (rdW W5 m5) _ 8 p); [|exact P].
  intros j Hj. apply DC. unfold NK_IF_NAME, NK_SIZE in *. lia.
- pose proof (xf_acstr_range SEGS (rdW W0 m0) p n2 C) as Rp.
  apply (xf_acstr SEGS (rdW W0 m0) (rdW W5 m5) p n2); [|exact C].
  intros j Hj. apply (DS i n2 ix p Hi P C). lia.
- apply (xf_val_mem SEGS (rdW W0 m0) (rdW W5 m5) _ 4 ix); [|exact I].
  intros j Hj. apply DC. unfold NK_IF_INDEX, NK_SIZE, NK_IF_NAME in *. lia.
Qed.

(* ==========================================================================
   3. THE CUT'S RESULT ACROSS A STEP THAT TOUCHES ONLY THE SIDE FRAME
   ========================================================================== *)
Lemma srx_pf_move : forall cx fpos ly3 S3 (W3 : world SEGS) (ms3 : machine_state) md3 rcv m5 S5 md5,
  srm_pre SK B cx ->
  srm_base fx SK B cx fpos (srm_E cx) ly3 S3 W3 ms3 md3 ->
  srm_pf cx rcv (rdW W3 (ms_mem ms3)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ aside_rng (sm_lyc cx) SRM_CID fpos a ->
     aview SEGS (w_H W3) m5 a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) m5 a) ->
  AR SEGS B ly3 S5 W3 m5 md5 -> ablocks B ly3 S5 = ablocks B ly3 S3 ->
  srm_pf cx rcv (rdW W3 m5).
Proof.
intros cx fpos ly3 S3 W3 ms3 md3 rcv m5 S5 md5 HPRE HBASE HPF HKEEP HPRS HAR5 HBL5.
pose proof HPRE as HPRE0. pose proof HBASE as HBASE0.
pose proof (srm_gspan_of_pre SK B cx HPRE) as HGS.
unfold srm_gspan_ok in HGS. cbv zeta in HGS. destruct HGS as (_ & HGT).
unfold srm_base in HBASE. cbv zeta in HBASE.
destruct HBASE as (_ & _ & _ & _ & _ & HJ3 & Hfrs3 & Hnin & _ & Hperm
  & (S1 & W1 & mem1 & md1 & HAR1 & Hfrs1 & Hbl1)
  & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HK3 & _).
destruct HPRE as (HAP & HRD & HAPRE).
destruct HAP as (HJ & _).
destruct HAPRE as (kb0 & tb0 & nm0 & k00 & HinSink & HLed & HNLK0 & _ & _ & _ & HTABOK & _ & _ & Hsink0 & _).
set (m3 := ms_mem ms3) in *.
assert (HAR3 : AR SEGS B ly3 S3 W3 m3 md3) by (eapply ajournal_gx_AR; exact HJ3).
assert (HinF : In (SRM_CID, fpos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
(* the frame slot of the call lies in its class's range *)
assert (HPOS : 0 <= fpos < fs_frames SRM_CID).
{ pose proof (proj1 HAR1) as M1.
  pose proof (proj1 (Forall_forall _ _)
    (wfs_live _ (wf_fakestack _ _ _ _ _ (am_wf B (sm_lyc cx) S1 _ M1))) (SRM_CID, fpos) HinF) as [_ X].
  cbn [fst snd] in X. exact X. }
(* a byte the call keeps is none of the side frame's *)
assert (NSIDE : forall a, akb SEGS B (sm_lyc cx) (sm_Sc cx)
    (srm_sp cx - REAC_SERVED_MARK_AK) (srm_sp cx) a -> ~ aside_rng (sm_lyc cx) SRM_CID fpos a).
{ intros a Ha. eapply (akb_not_side SK SEGS B);
    try first [ exact LAWS | exact TB | exact SIMG | exact HJ | exact HPOS | exact Hnin | exact Ha
              | (unfold SRM_CID; lia) ]. }
assert (NSBLK : forall b m a, In (b, m) (ablocks B (sm_lyc cx) (sm_Sc cx)) -> b <= a < b + req_size m ->
  ~ aside_rng (sm_lyc cx) SRM_CID fpos a).
{ intros b m a Hb Ha. apply NSIDE. right. left. exists b, m. split; [exact Hb | exact Ha]. }
assert (NSGNL : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> ~ aside_rng (sm_lyc cx) SRM_CID fpos a)
  by (intros a Ha; apply NSIDE; apply (srx_gnl_akb _ _ _ _ a Ha)).
assert (GNLB : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> 0 <= a < 2 ^ 64)
  by (intros a Ha; unfold LA_G_NL, NK_SIZE in Ha; lia).
assert (MBGNL : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE ->
  mbyte SEGS (rdW W3 m5) a = mbyte SEGS (rdW W3 m3) a).
{ intros a Ha. apply (xf_mbyte SEGS). apply HKEEP; [exact (GNLB a Ha) | exact (NSGNL a Ha)]. }
(* g_nl at the cut is g_nl at the entry *)
assert (VGNL : forall a, LA_G_NL + NK_IF_NAME <= a < LA_G_NL + NK_SIZE ->
  aview SEGS (w_H W3) m3 a = aview SEGS (w_H (sm_W cx)) (sm_memc cx) a).
{ intros a Ha.
  assert (Ha' : LA_G_NL <= a < LA_G_NL + NK_SIZE) by (unfold NK_IF_NAME, NK_SIZE in *; lia).
  eapply (srx_view_kept cx fpos ly3 S3 W3 ms3 md3 a HPRE0 HBASE0);
  [ apply (srx_gnl_akb _ _ _ _ a Ha')
  | apply (srx_img_notE cx a HPRE0); [ exact (proj1 (srx_gnl_img a Ha'))
                                     | unfold NK_IF_NAME, NK_N_SENT in *; lia ]
  | exact (NSGNL a Ha') ]. }
assert (MB0GNL : forall a, LA_G_NL + NK_IF_NAME <= a < LA_G_NL + NK_SIZE ->
  mbyte SEGS (rdW W3 m5) a = mbyte SEGS (srm_m0 cx) a).
{ intros a Ha. unfold srm_m0.
  assert (Ha' : LA_G_NL <= a < LA_G_NL + NK_SIZE) by (unfold NK_IF_NAME, NK_SIZE in *; lia).
  rewrite (MBGNL a Ha'). apply (xf_mbyte SEGS). exact (VGNL a Ha). }
assert (WRGNL : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> writable_at SEGS (rdW W3 m5) a).
{ intros a Ha.
  assert (HW : awrange SEGS (rdW W3 m5) LA_G_NL NK_SIZE) by (eapply xfer_gnl_awrange; srxh).
  specialize (HW (a - LA_G_NL) ltac:(lia)).
  replace (LA_G_NL + (a - LA_G_NL)) with a in HW by lia. exact HW. }
(* the two heap blocks of the call the Post speaks of *)
assert (HinSink3 : In (sm_sink cx, AMF_BLOCK) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); exact HinSink).
assert (HinSink5 : In (sm_sink cx, AMF_BLOCK) (ablocks B ly3 S5)) by (rewrite HBL5; exact HinSink3).
assert (NSFILE : forall a, sm_sink cx <= a < sm_sink cx + AMF_BLOCK -> ~ aside_rng (sm_lyc cx) SRM_CID fpos a).
{ intros a Ha. apply (NSBLK (sm_sink cx) AMF_BLOCK a HinSink).
  change (req_size AMF_BLOCK) with AMF_BLOCK. exact Ha. }
(* the frame addresses of the two layouts agree, so aside_rng is one set *)
assert (EFA : forall c p, frame_addr ly3 c p = frame_addr (sm_lyc cx) c p /\
                          flag_addr ly3 c p = flag_addr (sm_lyc cx) c p).
{ intros c p.
  assert (E3 : frame_addr ly3 c p = frame_addr (sm_ly cx) c p /\ flag_addr ly3 c p = flag_addr (sm_ly cx) c p)
    by (eapply aj_gx_frame_addr; srxh).
  assert (Ec : frame_addr (sm_lyc cx) c p = frame_addr (sm_ly cx) c p /\
               flag_addr (sm_lyc cx) c p = flag_addr (sm_ly cx) c p)
    by (eapply aj_gx_frame_addr; srxh).
  split; [rewrite (proj1 E3), (proj1 Ec); reflexivity | rewrite (proj2 E3), (proj2 Ec); reflexivity]. }
assert (ESIDE : forall a, aside_rng ly3 SRM_CID fpos a <-> aside_rng (sm_lyc cx) SRM_CID fpos a).
{ intros a. rewrite !srx_side_unfold, (proj1 (EFA SRM_CID fpos)), (proj2 (EFA SRM_CID fpos)). tauto. }
assert (HKEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ aside_rng ly3 SRM_CID fpos a ->
  aview SEGS (w_H W3) m5 a = aview SEGS (w_H W3) m3 a)
  by (intros a Ha Hs; apply HKEEP; [exact Ha | rewrite <- ESIDE; exact Hs]).
(* the kept clause of the step *)
assert (HKEPT : akept SEGS B ly3 S3 W3 m3 W3 m5 alloc_ceiling alloc_ceiling (aside_rng ly3 SRM_CID fpos)).
{ pose proof asan_consts as ((C1 & C2) & _).
  apply (akept_step SK SEGS B LAWS SLOW ly3 S3 W3 m3 md3 W3 m3 W3 m5
    alloc_ceiling alloc_ceiling (fun _ : Z => False) (aside_rng ly3 SRM_CID fpos)
    (aside_rng ly3 SRM_CID fpos)).
  - exact HAR3.
  - lia.
  - lia.
  - apply (akept_refl SK SEGS B LAWS SLOW ly3 S3 W3 m3 alloc_ceiling alloc_ceiling (fun _ : Z => False)).
    intros a Ha. lia.
  - exact HKEEP3.
  - intros a _ Hp. exact (HPRS a Hp).
  - intros a Ha. destruct Ha.
  - intros a Ha. left. exact Ha. }
assert (NSFILE3 : forall a, sm_sink cx <= a < sm_sink cx + AMF_BLOCK -> ~ aside_rng ly3 SRM_CID fpos a)
  by (intros a Ha; rewrite ESIDE; exact (NSFILE a Ha)).
(* ---- the Post ---- *)
unfold srm_pf in HPF |- *. intros regs' Hr10.
pose proof (HPF regs' Hr10) as HP.
unfold reac_served_mark_apost in HP |- *. destruct HP as (PA & PB & PC).
split; [|split].
- (* the FILE: k' bytes pending, at the same block *)
  intros k Hk. destruct (PA k Hk) as (k' & Hkb & Hmf).
  exists k'. split; [exact Hkb|].
  eapply xfer_amemfile_k;
    try first [ exact LAWS | exact HSEGS | exact TB | exact HKEPT | exact HAR5
              | exact HinSink3 | exact HinSink5 | exact NSFILE3 | exact Hmf ].
- (* the refusal arm: a0 = - E_INVAL and g_nl untouched *)
  intros H0. destruct (PB H0) as (Hrc & Hn). split; [exact Hrc|].
  intros kbs HN. apply (srx_anlk_move W3 m3 W3 m5 kbs); [exact (Hn kbs HN) | exact MBGNL | exact WRGNL].
- (* the marking arm *)
  intros H0 kbs tab nm gbs HN HT HA HG.
  pose proof (PC H0 kbs tab nm gbs HN HT HA HG) as HM. cbv zeta in HM |- *.
  (* the Post's objects are the entry Pre's: two readings of the same bytes are equal *)
  destruct HNLK0 as (HNL0 & _ & _ & _ & _ & HIT0 & _).
  assert (Ekb : kbs = kb0) by (eapply anlk_at_unique; [exact HN | exact HNL0]).
  subst kbs.
  assert (Etb : tab = tb0) by (eapply aiftab_at_unique; [exact HT | exact HIT0]).
  subst tab.
  destruct HM as (Hrc & (gbs' & Hgm & Hgw & Hgn & Hgl) & (kbs' & N1 & N2 & N3 & N4 & N5 & N6 & N7)).
  split; [exact Hrc|]. split.
  + (* the marks block: a heap block of the call *)
    exists gbs'. split; [|split; [exact Hgw | split; [exact Hgn | exact Hgl]]].
    destruct (HLed H0) as (HinMk & _).
    assert (HinMk3 : In (srm_mk cx, MK_SIZE) (ablocks B ly3 S3))
      by (apply (Permutation_in _ (Permutation_sym Hperm)); exact HinMk).
    assert (HinMk5 : In (srm_mk cx, MK_SIZE) (ablocks B ly3 S5)) by (rewrite HBL5; exact HinMk3).
    assert (NSMK3 : forall a, srm_mk cx <= a < srm_mk cx + MK_SIZE ->
      ~ aside_rng ly3 SRM_CID fpos a).
    { intros a Ha. rewrite ESIDE. apply (NSBLK (srm_mk cx) MK_SIZE a HinMk).
      change (req_size MK_SIZE) with MK_SIZE. exact Ha. }
    eapply xfer_amarks;
      try first [ exact LAWS | exact HSEGS | exact TB | exact HKEPT | exact HAR5
                | exact HinMk3 | exact HinMk5 | exact NSMK3 | exact Hgm ].
  + (* the fake kernel and its interface table *)
    exists kbs'.
    refine (conj _ (conj N2 (conj N3 (conj N4 (conj N5 (conj _ N7)))))).
    * apply (srx_anlk_move W3 m3 W3 m5 kbs'); [exact N1 | exact MBGNL | exact WRGNL].
    * (* rebuilt from the ENTRY's table (the Post quantifies it at the entry memory) *)
      apply (srx_aiftab_move (sm_W cx) (sm_memc cx) W3 m5 kb0 kbs' tb0 HT).
      -- (* nk_n_if kbs' = nk_n_if kbs: through the cut's reading *)
         destruct N6 as (L6 & _). destruct HT as (L0 & _). rewrite L6, L0. reflexivity.
      -- intros x Hx. exact (MB0GNL x Hx).
      -- intros i n2 ix p Hi Hp Hc x Hx.
         (* the string's granule span is a byte the call keeps *)
         assert (Hpr : 0 <= p < 2 ^ 64).
         { pose proof (xf_acstr_range SEGS (srm_m0 cx) p n2 Hc) as Rp. lia. }
         assert (HAKB : akb SEGS B (sm_lyc cx) (sm_Sc cx)
                          (srm_sp cx - REAC_SERVED_MARK_AK) (srm_sp cx) x).
         { apply (HGT kb0 tb0 i n2 ix p x HNL0 HIT0 Hi Hp Hc).
           unfold srm_gspan. pose proof (xf_acstr_range SEGS (srm_m0 cx) p n2 Hc) as Rp.
           assert (Hm : 0 <= (p + Z.of_nat (length n2)) mod 8 < 8) by (apply Z.mod_pos_bound; lia). lia. }
         (* the string is apart from every object of the write set *)
         assert (HnE : ~ srm_E cx x).
         { destruct (HTABOK i n2 ix p Hi Hp Hpr) as (_ & Hgnl & Herr & Hfb & Hmkp).
           intros HE.
           destruct (srx_E_inv cx x HE) as [H1 | [(Hmk0 & Hmk) | (Hsk0 & Hsk)]].
           - unfold apart_gnl in Hgnl. unfold NK_N_SENT, NK_SIZE in *. destruct Hgnl; lia.
           - unfold srm_mk in Hmk0, Hmk. specialize (Hmkp Hmk0). unfold apart in Hmkp.
             destruct Hmkp; lia.
           - unfold apart in Hfb. destruct Hfb; lia. }
         assert (Hns : ~ aside_rng (sm_lyc cx) SRM_CID fpos x) by exact (NSIDE x HAKB).
         assert (Hxb : 0 <= x < 2 ^ 64).
         { pose proof (xf_acstr_range SEGS (srm_m0 cx) p n2 Hc) as Rp. lia. }
         assert (Vx : aview SEGS (w_H W3) m5 x = aview SEGS (w_H (sm_W cx)) (sm_memc cx) x).
         { rewrite (HKEEP x Hxb Hns).
           exact (srx_view_kept cx fpos ly3 S3 W3 ms3 md3 x HPRE0 HBASE0 HAKB HnE Hns). }
         unfold srm_m0. exact (xf_mbyte SEGS _ _ _ _ x Vx).
Qed.

(* ==========================================================================
   4. The EXIT piece
   ========================================================================== *)
Theorem srm_exit_ok : srm_exit_obl fx SK B.
Proof.
intros cx fpos ly3 S3 W3 ms3 md3 HPRE HGS HGI.
pose proof HPRE as HPRE0.
destruct HGI as (rcv & Hpc & R21 & HPF & HBASE).
pose proof HBASE as HBASE0.
unfold srm_base in HBASE. cbv zeta in HBASE.
destruct HBASE as (Zrsv & Zsvc & Zrom & Zfrg & Zfcsr & HJ3 & Hfrs3 & Hnin & HfsS3 & Hperm
  & (S1 & W1 & mem1 & md1 & HAR1 & Hfrs1 & Hbl1)
  & R2 & R9 & R8 & R18 & R19 & R25 & R26 & R20 & R22 & R3 & R4 & R27
  & Hra8 & Hsav & Hflag & HFpres & HSpres & HK3 & Hfds3 & Hfs3 & HRO3 & Hfrm0).
destruct HPRE as (HAP & HRD & HAPRE).
pose proof HAP as HAP0.
destruct HAP as (HJ & HGX & HRO0 & Hraok & Hra4 & Hgp & Htp & Hsp16 & Hwlo & Hwhi & Hnev & Hroom & Hajw & Hnro).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
set (regs := sm_regs cx) in *. set (R := ms_regs ms3) in *. set (m3 := ms_mem ms3) in *.
set (sp := srm_sp cx) in *. set (sp1 := srm_sp1 cx) in *.
set (F := srm_F cx fpos) in *. set (FL := srm_FL cx fpos) in *. set (SH := srm_SH cx fpos) in *.
assert (Esp : spZ regs = sp) by reflexivity.
rewrite Esp in Hwlo, Hwhi, Hsp16.
(* ---- the journal's row and the window ---- *)
assert (HROW : alloc_ceiling <= ly_stk_lo (sm_lyc cx) /\ ly_stk_hi (sm_lyc cx) <= 2 ^ 47 /\
  ly_stk_lo (sm_lyc cx) + sm_STK cx <= sm_sp0 cx /\ sm_sp0 cx + sm_XO cx <= ly_stk_hi (sm_lyc cx))
  by (eapply ajournal_gx_row; exact HJ).
assert (Hspr : 0 <= sp < 2 ^ 64) by (unfold sp, srm_sp, spZ; apply bv_unsigned_in_range).
assert (HKv : REAC_SERVED_MARK_AK = 9504) by reflexivity.
assert (HXO0 : 0 <= sm_XO cx) by (destruct HJ as (_ & HX & _); exact HX).
assert (HspK : alloc_ceiling <= sp - REAC_SERVED_MARK_AK) by lia.
assert (Hsp47 : sp <= 2 ^ 47) by lia.
(* ---- the frame, its shadow and its flag byte ---- *)
assert (HAR3 : AR SEGS B ly3 S3 W3 m3 md3) by (eapply ajournal_gx_AR; exact HJ3).
assert (HinF : In (SRM_CID, fpos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
assert (HinF3 : In (SRM_CID, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (E3 : frame_addr ly3 SRM_CID fpos = frame_addr (sm_ly cx) SRM_CID fpos /\
             flag_addr ly3 SRM_CID fpos = flag_addr (sm_ly cx) SRM_CID fpos)
  by (eapply aj_gx_frame_addr; srxh).
assert (Ecl : frame_addr (sm_lyc cx) SRM_CID fpos = frame_addr (sm_ly cx) SRM_CID fpos /\
              flag_addr (sm_lyc cx) SRM_CID fpos = flag_addr (sm_ly cx) SRM_CID fpos)
  by (eapply aj_gx_frame_addr; srxh).
assert (EF : frame_addr ly3 SRM_CID fpos = F)
  by (unfold F, srm_F; rewrite (proj1 E3), (proj1 Ecl); reflexivity).
assert (EFL : flag_addr ly3 SRM_CID fpos = FL)
  by (unfold FL, srm_FL; rewrite (proj2 E3), (proj2 Ecl); reflexivity).
assert (EFl : frame_addr (sm_lyc cx) SRM_CID fpos = F) by reflexivity.
assert (EFLl : flag_addr (sm_lyc cx) SRM_CID fpos = FL) by reflexivity.
assert (HFB : 4096 <= frame_addr (sm_lyc cx) SRM_CID fpos /\
  frame_addr (sm_lyc cx) SRM_CID fpos + fs_frame_bytes SRM_CID <= alloc_ceiling /\
  in_app (frame_addr (sm_lyc cx) SRM_CID fpos) (fs_frame_bytes SRM_CID))
  by (eapply frames_bounds; try first [exact LAWS | exact HAR1 | exact HinF]).
destruct HFB as (HF4096 & HFceil & HFapp).
rewrite EFl in HF4096, HFceil, HFapp. change (fs_frame_bytes SRM_CID) with 512 in HFceil, HFapp.
assert (HAL : frame_addr (sm_lyc cx) SRM_CID fpos mod 64 = 0 /\
  fs_frame_bytes SRM_CID mod 64 = 0 /\ 64 <= fs_frame_bytes SRM_CID)
  by (eapply frame_al64; try first [exact LAWS | exact HAR1 | exact HinF]).
destruct HAL as (HFal & _ & _).
rewrite EFl in HFal.
destruct (al_frames SEGS B LAWS _ _ _ _ _ SRM_CID fpos HAR1 HinF)
  as (_ & _ & HFnown & HFSnown).
rewrite EFl in HFnown, HFSnown. change (fs_frame_bytes SRM_CID) with 512 in HFnown, HFSnown.
change (512 / 8) with 64 in HFSnown.
destruct (al_flag SEGS B LAWS _ _ _ _ _ SRM_CID fpos HAR1 HinF)
  as (_ & HFLown & HFLapp & HFLceil).
rewrite EFLl in HFLown, HFLapp, HFLceil.
assert (HSHeq : SH = SHADOW_OFF + F / 8) by reflexivity.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp, HFLapp.
assert (HF8 : 0 <= F / 8 /\ F / 8 + 64 <= (F + 512) / 8).
{ split; [apply Z.div_pos; lia|]. replace (F + 512) with (F + 64 * 8) by lia. rewrite Z.div_add by lia. lia. }
assert (HF8c : (F + 512) / 8 <= 17592184995840).
{ replace 17592184995840 with (140737479966720 / 8) by reflexivity. apply Z.div_le_mono; lia. }
assert (HSHb : SHADOW_OFF + 64 <= SH + 1 /\ SH + 64 <= SHADOW_OFF + 2 ^ 44) by (unfold SHADOW_OFF in *; lia).
assert (HFLnF : ~ (F <= FL < F + 512)) by (intros Hc; exact (proj2 (HFnown FL Hc) HFLown)).
assert (HFLnS : ~ (SH <= FL < SH + 64)).
{ intros Hc. apply (proj2 (HFSnown (FL - shadow_addr F) ltac:(unfold shadow_addr; lia))).
  replace (shadow_addr F + (FL - shadow_addr F)) with FL by lia. exact HFLown. }
assert (HFb : 0 <= F < 2 ^ 64) by lia.
assert (HFLb : 0 <= FL < 2 ^ 64) by lia.
assert (HSHr : 0 <= SH < 2 ^ 64) by (unfold SHADOW_OFF in *; lia).
assert (HSH8 : SH mod 8 = 0).
{ destruct (div8_of_mul64 F HFal) as (E8m & _).
  unfold SH, srm_SH, shadow_addr. fold F. rewrite E8m. unfold SHADOW_OFF. lia. }
assert (UF : bv_unsigned (w64 F) = F) by (unfold w64; apply unsigned_lit_small; lia).
assert (UFL : bv_unsigned (w64 FL) = FL) by (unfold w64; apply unsigned_lit_small; lia).
assert (Usp : bv_unsigned (w64 sp) = sp) by (unfold w64; apply unsigned_lit_small; lia).
assert (USH : bv_unsigned (w64 SH) = SH) by (unfold w64; apply unsigned_lit_small; lia).
(* the realigned stack pointer s1 *)
destruct (sp1_facts (sp - SRM_FRAME) ltac:(unfold SRM_FRAME; lia)
  ltac:(unfold SRM_FRAME; rewrite Zminus_mod, Hsp16; reflexivity)) as (Hsp1r & Hsp1al32 & Hsp1al16).
change (32 * ((sp - SRM_FRAME) / 32)) with sp1 in Hsp1r, Hsp1al32, Hsp1al16.
unfold SRM_FRAME in Hsp1r.
assert (Usp1 : bv_unsigned (w64 sp1) = sp1) by (unfold w64; apply unsigned_lit_small; lia).
(* ---- the environment ---- *)
set (extra := [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20;
               getr regs 21; getr regs 22; getr regs 23; getr regs 24; getr regs 25; getr regs 26; w64 FL]).
set (E := Eimg (Ereg R extra)).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg R extra) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (EREG : forall n (r : Prelude.reg), Z.of_nat n = bv_unsigned r -> ew E n = getr R r).
{ intros n r Hr. rewrite EL; [exact (ew_Ereg_nat _ _ n r Hr)|].
  pose proof (u5_range r) as Hu. unfold A_TEXT. lia. }
assert (EX : forall j, (j < 13)%nat -> ew E (32 + j) = nth j extra (w64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ j)).
assert (EXn : forall j n, (j < 13)%nat -> n = (32 + j)%nat -> ew E n = nth j extra (w64 0))
  by (intros j n Hj ->; exact (EX j Hj)).
assert (E19 : ew E 19 = w64 F) by (rewrite (EREG 19%nat 19%bv eq_refl); exact R19).
assert (E18 : ew E 18 = w64 SH) by (rewrite (EREG 18%nat 18%bv eq_refl); exact R18).
assert (E8 : ew E 8 = w64 sp) by (rewrite (EREG 8%nat 8%bv eq_refl); exact R8).
assert (E2 : ew E 2 = w64 sp1) by (rewrite (EREG 2%nat 2%bv eq_refl); exact R2).
assert (E44 : ew E 44 = w64 FL) by (exact (EXn 12%nat 44%nat ltac:(lia) eq_refl)).
assert (U19 : bv_unsigned (ew E 19) = F) by (rewrite E19; exact UF).
assert (U8 : bv_unsigned (ew E 8) = sp) by (rewrite E8; exact Usp).
assert (U44 : bv_unsigned (ew E 44) = FL) by (rewrite E44; exact UFL).
(* the saved words, as the saves region's chunks *)
assert (HSAV : forall j, (j < 12)%nat ->
  val_mem SEGS (rdW W3 m3) (sp + (-8 - 8 * Z.of_nat j)) 8 (bv_unsigned (nth j extra (w64 0)))).
{ intros j Hj. apply (val_mem_of_rdword SEGS (w_H W3) m3).
  destruct j as [|j'].
  - replace (sp + (-8 - 8 * Z.of_nat 0)) with (sp - 8) by lia. exact Hra8.
  - replace (sp + (-8 - 8 * Z.of_nat (S j'))) with (sp - 16 - 8 * Z.of_nat j') by lia.
    rewrite (Hsav (Z.of_nat j') ltac:(lia)). f_equal.
    do 10 (destruct j' as [|j']; [reflexivity|]). destruct j' as [|j']; [reflexivity | exfalso; lia]. }
assert (HCH : forall j, (j < 12)%nat -> YP09.chunk_ok SEGS E (rdW W3 m3) sp
   (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0)))).
{ intros j Hj.
  apply (chunk_ok_val SEGS E _ sp (-8 - 8 * Z.of_nat j) 8 (SOff (32 + j) 0)
    (bv_unsigned (nth j extra (w64 0))));
  [ cbn [sv_denot]; rewrite (EX j ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | pose proof (bv_unsigned_in_range 64 (nth j extra (w64 0))) as Hu;
    change (bv_modulus 64) with (2 ^ 64) in Hu; change (8 * Z.of_N 8) with 64; lia
  | zside
  | exact (HSAV j Hj) ]. }
(* ---- the symbolic state at the cut ---- *)
assert (HS0 : st_ok_pi SEGS VAL E srx_ssE0 (restrict (w_H W3) ms3)).
{ rewrite (srx_ms_eta ms3 Zfrg Zsvc Zrsv Zfcsr), Hpc, Zrom, restrict_mkst_fx.
  unfold srx_ssE0. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
      unfold region_ok, srx_FR, srx_FL0, srx_saves;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U19. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (xf_wr SEGS); apply HFpres; unfold SRM_FB; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ F 504 8 (SOff 44 0) FL);
      [ cbn [sv_denot]; rewrite E44, Z.add_0_r, UFL; reflexivity
      | change (8 * Z.of_N 8) with 64; lia | zside
      | exact (val_mem_of_rdword SEGS (w_H W3) m3 _ _ Hflag) ].
    + rewrite U44. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_nil.
    + rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      unfold srx_saves_chunks. apply Forall_map, Forall_forall. intros j Hj.
      apply in_seq in Hj. apply HCH. lia.
  - apply pairwise_disjoint_of_extents.
    unfold srx_FR, srx_FL0, srx_saves, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U19, U44, U8.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [srx_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
    rewrite U19, U44. change (2 ^ 6) with 64. change (2 ^ 0) with 1.
    repeat split; try lia; try apply Z.mod_1_r. }
assert (HS : st_ok_pi SEGS VAL E (mkSS (ss_pc srx_ssE0) (sr_set (ss_regs srx_ssE0) 25%bv (SOff 19 0))
  (ss_mem srx_ssE0) (ss_resv srx_ssE0) (ss_facts srx_ssE0)) (restrict (w_H W3) ms3)).
{ apply (ast_ok_pi_set_reg_fp E _ _ (25%bv : bv 5) (SOff 19 0) HS0 ltac:(vm_compute; reflexivity)).
  rewrite (sv_off0 E 19 F E19). cbn [ms_regs restrict]. fold R. rewrite R25. reflexivity. }
clear HS0.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts srx_ssE0] in HS.
clearbody E.
(* ---- +0x360 .. +0x378: the retired magic, `beqz s3` (not taken), up to meta_fill_f5 ---- *)
pose proof (paj_run_call_plain_x SK B LAWS (sm_G cx) HGX (sm_XO cx) (sm_OUT cx)) as RUNC.
lazymatch type of HS with
| st_ok_pi _ _ _ ?ss _ =>
  let tpi := srx_tpi RUNC in
  let r := eval vm_compute in (sym_runN_pi tpi FUEL ss) in
  lazymatch r with
  | (?ss', ?st) => assert (Hrun1 : sym_runN_pi tpi FUEL ss = (ss', st)) by (vm_compute; reflexivity)
  end
end.
eapply RUNC; try first [exact HEI | exact HS | exact Hrun1 | exact HJ3].
{ intros a (r & Hr & Ha). cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val srx_FR srx_FL0 srx_saves] in Ha;
  [| lia | lia].
  rewrite U19 in Ha. left.
  eapply (aj_gx_awr_frame SK SEGS B LAWS SLOW); [exact HJ3 | left; reflexivity|].
  left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF. change (fs_frame_bytes SRM_CID) with 512. lia. }
clear Hrun1.
intros ms1 mat1 HS1 HJ1 _ HFr1 HG1.
prreg HS1 (10%bv : bv 5) Q10. prreg HS1 (11%bv : bv 5) Q11. prreg HS1 (1%bv : bv 5) Q1.
prreg HS1 (2%bv : bv 5) Q2. prreg HS1 (3%bv : bv 5) Q3. prreg HS1 (4%bv : bv 5) Q4.
pmkst HS1.
set (md1c := with_vm_backing (m_vm_lazy md3) mat1 md3) in *.
(* ---- meta_fill_f5(shadow(F), 64) ---- *)
destruct HV as [Htext Hobj Hhi Hsig].
assert (Esig : pa_sigma LS___asan_set_shadow_f5 = 0x55f7c) by (rewrite Hsig; reflexivity).
eapply SRr_bind.
{ eapply (aj_gx_set_shadow_at SK SEGS B LAWS SLOW (pa_sigma LS___asan_set_shadow_f5) 0xf5);
  [ rewrite Esig; exact ASSF5 | exact HGX | exact HJ1 | left; reflexivity | | | | | | | | | | | | ].
  - rewrite Q10, E18. reflexivity.
  - rewrite Q11. reflexivity.
  - lia.
  - rewrite EF. unfold shadow_addr. fold F. lia.
  - rewrite EF. unfold shadow_addr. change (fs_frame_bytes SRM_CID / 8) with 64. fold F. lia.
  - unfold spZ. rewrite Q2, E2, Usp1. exact Hsp1al16.
  - unfold spZ. rewrite Q2, E2, Usp1. change ESTACK with 4096. lia.
  - unfold spZ. rewrite Q2, E2, Usp1. lia.
  - rewrite Q3, (EREG 3%nat 3%bv eq_refl), R3. exact Hgp.
  - rewrite Q4, (EREG 4%nat 4%bv eq_refl), R4. exact Htp.
  - reflexivity.
  - rewrite Q1. apply ret_ok_codeptr_v; [unfold SRM_CUT_EXIT, AF_reac_served_mark; lia | reflexivity]. }
cbv beta.
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hf5 & Hmf & Hpres2 & Hsbm2).
assert (HAR2 : AR SEGS B ly3 S3 W3 mem2 md2) by (eapply ajournal_gx_AR; exact HJ2).
destruct (al_frames SEGS B LAWS _ _ _ _ _ SRM_CID fpos HAR2 HinF3) as (_ & _ & HFpres2 & _).
rewrite EF in HFpres2. change (fs_frame_bytes SRM_CID) with 512 in HFpres2.
destruct (al_flag SEGS B LAWS _ _ _ _ _ SRM_CID fpos HAR2 HinF3) as (HFLpres2 & _).
rewrite EFL in HFLpres2.
(* the state after the call *)
jafter_call_keep_pi HS1 48%nat regs2 (mrestrict (w_H W3) mem2) HP2 [0; 1; 2]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil;
    split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha.
  - rewrite U19 in Ha. apply (xf_mbyte SEGS). apply Hmf; [lia|]. unfold SHADOW_OFF in *; lia.
  - intros _. rewrite U19 in Ha. apply (xf_wr SEGS). apply HFpres2. lia.
  - rewrite U44 in Ha. apply (xf_mbyte SEGS). apply Hmf; [lia|]. intros Hc. apply HFLnS.
    replace FL with a by lia. exact Hc.
  - lia.
  - rewrite U8 in Ha. apply (xf_mbyte SEGS). apply Hmf; [lia|]. unfold SHADOW_OFF in *; lia.
  - lia. }
rewrite <- restrict_mkst_fx in HS2.
assert (Hraw : getr (ms_regs ms1) 1 = Z_to_bv 64 (BASE + (SRM_CUT_EXIT + 28))) by (rewrite Q1; reflexivity).
rewrite Hraw.
remember (havoc E 48 (map (getr regs2) CLOB)) as Ev2 eqn:HE2 in HS2.
assert (HEI2 : img_env VAL A_LIM Ev2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall nn, (nn < 48)%nat -> ew Ev2 nn = ew E nn)
  by (intros nn Hnn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hnn).
clear HE2.
assert (V19 : bv_unsigned (ew Ev2 19) = F) by (rewrite OLD2 by lia; exact U19).
assert (V44 : bv_unsigned (ew Ev2 44) = FL) by (rewrite OLD2 by lia; exact U44).
assert (V8 : bv_unsigned (ew Ev2 8) = sp) by (rewrite OLD2 by lia; exact U8).
(* the flag byte becomes writable *)
lazymatch type of HS2 with st_ok_pi _ _ _ ?ssx ?msx =>
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) srx_FL0) in
  pose proof (st_ok_pi_region_nth Ev2 ssx msx 1 r1 HS2 ltac:(vm_compute; reflexivity)) as HR1;
  pose proof (ast_ok_pi_set_region Ev2 ssx msx 1 r1 (set_window r1 0 1) HS2 ltac:(vm_compute; reflexivity)
    ltac:(reflexivity) ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS Ev2 _ r1 0 1 HR1 ltac:(intros o Ho; cbn [YP09.r_base base_val];
       rewrite V44; replace (FL + o) with FL by lia; cbn [ms_mem restrict mkst];
       apply (xf_wr SEGS); exact HFLpres2))) as HS3
end.
clear HS2 HR1. norm_pi HS3.
(* ---- +0x37c .. +0x494: the inline release, a0 := s5, sp, the twelve restores, up to `ret` ---- *)
pose proof (paj_flag_plain_x SK B LAWS (sm_G cx) HGX (sm_XO cx) (sm_OUT cx)) as RUNF.
lazymatch type of HS3 with
| st_ok_pi _ _ _ ?ss _ =>
  let tpi := srx_tpi RUNF in
  let r := eval vm_compute in (sym_runN_pi tpi FUEL ss) in
  lazymatch r with
  | (?ss', ?st) => assert (Hrun2 : sym_runN_pi tpi FUEL ss = (ss', st)) by (vm_compute; reflexivity)
  end
end.
eapply RUNF; try first [exact HEI2 | exact HS3 | exact Hrun2 | exact I | exact HJ2].
{ unfold SRM_CID. lia. }
{ intros a (r & Hr & Ha). cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  - rewrite V19 in Ha. left.
    eapply (aj_gx_awr_frame SK SEGS B LAWS SLOW); [exact HJ2 | left; reflexivity|].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF. change (fs_frame_bytes SRM_CID) with 512. lia.
  - rewrite V44 in Ha. right. right. right. rewrite EFL. lia.
  - lia. }
{ intros msr HSr.
  lazymatch type of HSr with st_ok_pi _ _ _ ?ssx _ =>
    let r1 := eval vm_compute in (nth 1 (ss_mem ssx) srx_FL) in
    pose proof (st_ok_pi_region_nth Ev2 ssx msr 1 r1 HSr ltac:(vm_compute; reflexivity)) as HR1;
    pose proof (field_of_region Ev2 (ms_mem msr) 44 FL _ 0 1 0 1 0 1%N (SLit 0) 0 HR1 V44
      ltac:(cbn; tauto) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as Vfl;
    change (N.to_nat 1) with 1%nat in Vfl; specialize (Vfl 0%nat ltac:(lia));
    replace (FL + 0 + Z.of_nat 0) with FL in Vfl by lia;
    rewrite EFL, Vfl; reflexivity
  end. }
clear Hrun2.
intros ms5 mat5 HS5 HJ5 _ HFr5 HG5.
(* ---- `ret` ---- *)
prreg HS5 (1%bv : bv 5) P1. prreg HS5 (2%bv : bv 5) P2. prreg HS5 (3%bv : bv 5) P3.
prreg HS5 (4%bv : bv 5) P4. prreg HS5 (8%bv : bv 5) P8. prreg HS5 (9%bv : bv 5) P9.
prreg HS5 (10%bv : bv 5) P10. prreg HS5 (18%bv : bv 5) P18. prreg HS5 (19%bv : bv 5) P19.
prreg HS5 (20%bv : bv 5) P20. prreg HS5 (21%bv : bv 5) P21. prreg HS5 (22%bv : bv 5) P22.
prreg HS5 (23%bv : bv 5) P23. prreg HS5 (24%bv : bv 5) P24. prreg HS5 (25%bv : bv 5) P25.
prreg HS5 (26%bv : bv 5) P26. prreg HS5 (27%bv : bv 5) P27.
lazymatch type of HS5 with
| st_ok_pi _ _ _ ?ss _ =>
  let tpi := srx_tpi RUNF in
  assert (Hret : plookup tpi (ss_pc ss) = Some (PW RET_WORD_r)) by (vm_compute; reflexivity)
end.
eapply (paj_ret_at W3 Ev2 _ ms5 _ _ HS5 eq_refl Hret).
intros mat6.
assert (Era : getr (ms_regs ms5) 1 = getr regs 1).
{ rewrite P1, OLD2 by lia. rewrite (EXn 0%nat 32%nat ltac:(lia) eq_refl). reflexivity. }
rewrite Era.
assert (Hjalr : v_jalr (getr regs 1) 0 = getr regs 1) by exact Hraok.
rewrite Hjalr.
pose proof (ajournal_gx_materialize SEGS B LAWS SLOW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat6 HJ5) as HJ6.
(* ---- what the epilogue changed: only bytes of the side frame ---- *)
assert (HWR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 8) ->
  aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) m3 a).
{ intros a Ha Hn. apply (YCbq.aview_eq_of SEGS). apply HFr1.
  rewrite unsigned_lit_small by lia.
  intros (r & Hr & Hra). cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val srx_FR srx_FL0 srx_saves] in Hra;
  [rewrite U19 in Hra | |]; lia. }
assert (HWR5 : forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 8) -> a <> FL ->
  aview SEGS (w_H W3) (ms_mem ms5) a = aview SEGS (w_H W3) mem2 a).
{ intros a Ha Hn Hfl. apply (YCbq.aview_eq_of SEGS). apply HFr5.
  rewrite unsigned_lit_small by lia.
  intros (r & Hr & Hra). cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra;
  [rewrite V19 in Hra | rewrite V44 in Hra |]; lia. }
assert (HKEEP : forall a, 0 <= a < 2 ^ 64 -> ~ aside_rng (sm_lyc cx) SRM_CID fpos a ->
  aview SEGS (w_H W3) (ms_mem ms5) a = aview SEGS (w_H W3) m3 a).
{ intros a Ha Hs. rewrite srx_side_unfold, EFl, EFLl in Hs.
  rewrite (HWR5 a Ha ltac:(lia) ltac:(lia)), (Hmf a Ha ltac:(lia)).
  apply HWR1; [exact Ha | lia]. }
assert (HPRS : forall a, apresent (w_H W3) m3 a -> apresent (w_H W3) (ms_mem ms5) a).
{ intros a Ha. apply (srx_apresent_grows (w_H W3) mem2); [exact HG5|]. apply Hpres2.
  exact (srx_apresent_grows (w_H W3) m3 (ms_mem ms1) a HG1 Ha). }
(* ---- the post ---- *)
unfold srm_post. apply apostF_of_apost.
eapply (apost_side_gen SK SEGS B LAWS SLOW REAC_SERVED_MARK_AK 0 (srm_E cx)
  (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx) (sm_FP cx) (sm_ly cx) (sm_S cx) (sm_W0 cx)
  (sm_mem0 cx) (sm_md0 cx) (sm_own cx) (sm_lyc cx) (sm_Sc cx) (sm_W cx) (sm_memc cx) (sm_mdc cx) (sm_k cx)
  regs (ms_regs ms5) ly3 (stack_free_state SRM_CID fpos S3) W3 (ms_mem ms5) _ (sm_k cx) SRM_CID fpos
  S1 W1 mem1 md1 _ HJ HJ6 ltac:(lia)).
- destruct (srx_wvb_fds_fs (m_vm_lazy (with_vm_backing (m_vm_lazy md2) mat5 md2)) mat6
    (with_vm_backing (m_vm_lazy md2) mat5 md2)) as (A1 & _).
  destruct (srx_wvb_fds_fs (m_vm_lazy md2) mat5 md2) as (A2 & _).
  destruct (srx_sbm_fds_fs _ _ Hsbm2) as (A3 & _).
  destruct (srx_wvb_fds_fs (m_vm_lazy md3) mat1 md3) as (A4 & _).
  rewrite A1, A2, A3. unfold md1c. rewrite A4. exact Hfds3.
- destruct (srx_wvb_fds_fs (m_vm_lazy (with_vm_backing (m_vm_lazy md2) mat5 md2)) mat6
    (with_vm_backing (m_vm_lazy md2) mat5 md2)) as (_ & A1).
  destruct (srx_wvb_fds_fs (m_vm_lazy md2) mat5 md2) as (_ & A2).
  destruct (srx_sbm_fds_fs _ _ Hsbm2) as (_ & A3).
  destruct (srx_wvb_fds_fs (m_vm_lazy md3) mat1 md3) as (_ & A4).
  rewrite A1, A2, A3. unfold md1c. rewrite A4. exact Hfs3.
- apply aregs_preserved_eqs.
  + rewrite P2, OLD2, E8 by lia. unfold w64, sp, srm_sp, spZ. apply Z_to_bv_bv_unsigned.
  + rewrite P3, OLD2, (EREG 3%nat 3%bv eq_refl) by lia. exact R3.
  + rewrite P4, OLD2, (EREG 4%nat 4%bv eq_refl) by lia. exact R4.
  + rewrite P8, OLD2 by lia. exact (EXn 1%nat 33%nat ltac:(lia) eq_refl).
  + rewrite P9, OLD2 by lia. exact (EXn 2%nat 34%nat ltac:(lia) eq_refl).
  + rewrite P18, OLD2 by lia. exact (EXn 3%nat 35%nat ltac:(lia) eq_refl).
  + rewrite P19, OLD2 by lia. exact (EXn 4%nat 36%nat ltac:(lia) eq_refl).
  + rewrite P20, OLD2 by lia. exact (EXn 5%nat 37%nat ltac:(lia) eq_refl).
  + rewrite P21, OLD2 by lia. exact (EXn 6%nat 38%nat ltac:(lia) eq_refl).
  + rewrite P22, OLD2 by lia. exact (EXn 7%nat 39%nat ltac:(lia) eq_refl).
  + rewrite P23, OLD2 by lia. exact (EXn 8%nat 40%nat ltac:(lia) eq_refl).
  + rewrite P24, OLD2 by lia. exact (EXn 9%nat 41%nat ltac:(lia) eq_refl).
  + rewrite P25, OLD2 by lia. exact (EXn 10%nat 42%nat ltac:(lia) eq_refl).
  + rewrite P26, OLD2 by lia. exact (EXn 11%nat 43%nat ltac:(lia) eq_refl).
  + rewrite P27, OLD2, (EREG 27%nat 27%bv eq_refl) by lia. exact R27.
- exact HAR1.
- exact Hfrs1.
- exact Hbl1.
- eapply (akept_step SK SEGS B LAWS SLOW (sm_lyc cx) (sm_Sc cx) (sm_W cx) (sm_memc cx) (sm_mdc cx)
    W3 m3 W3 (ms_mem ms5) (sp - REAC_SERVED_MARK_AK) sp _ _ (aside_rng (sm_lyc cx) SRM_CID fpos));
  [ eapply ajournal_gx_AR; exact HJ | exact HspK | lia | exact HK3 | exact HKEEP | | | ].
  + intros a _ Hp. exact (HPRS a Hp).
  + intros a Ha. exact Ha.
  + intros a Ha. left. right. exact Ha.
- cbv beta. split; [|split].
  + apply (set_fs_trans S3 (stack_free_state SRM_CID fpos S3) (sm_Sc cx));
    [exact HfsS3 | apply stack_free_state_set_fs].
  + rewrite stack_free_state_set_fs, ablocks_set_fs. exact Hperm.
  + assert (P10' : getr (ms_regs ms5) 10 = w64 rcv)
      by (rewrite P10, OLD2, (EREG 21%nat 21%bv eq_refl) by lia; exact R21).
    eapply (srx_pf_move cx fpos ly3 S3 W3 ms3 md3 rcv (ms_mem ms5)
      (stack_free_state SRM_CID fpos S3) _ HPRE0 HBASE0 HPF HKEEP HPRS);
    [ eapply ajournal_gx_AR; exact HJ6
    | rewrite stack_free_state_set_fs, ablocks_set_fs; reflexivity
    | exact P10' ].
Qed.

(* ==========================================================================
   5. The RESTORE piece
   ========================================================================== *)
Theorem srm_restore_ok : srm_exit_obl fx SK B -> srm_restore_obl fx SK B.
Proof.
intros HEXIT cx fpos ly3 S3 W3 ms3 md3 HPRE HGS HGI.
pose proof HPRE as HPRE0.
destruct HGI as (rcv & Hpc & R21 & HPF & HBASE).
pose proof HBASE as HBASE0.
unfold srm_base in HBASE. cbv zeta in HBASE.
destruct HBASE as (Zrsv & Zsvc & Zrom & Zfrg & Zfcsr & HJ3 & Hfrs3 & Hnin & HfsS3 & Hperm
  & (S1 & W1 & mem1 & md1 & HAR1 & Hfrs1 & Hbl1)
  & R2 & R9 & R8 & R18 & R19 & R25 & R26 & R20 & R22 & R3 & R4 & R27
  & Hra8 & Hsav & Hflag & HFpres & HSpres & HK3 & Hfds3 & Hfs3 & HRO3 & Hfrm0).
destruct HPRE as (HAP & HRD & HAPRE).
pose proof HAP as HAP0.
destruct HAP as (HJ & HGX & HRO0 & Hraok & Hra4 & Hgp & Htp & Hsp16 & Hwlo & Hwhi & Hnev & Hroom & Hajw & Hnro).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
set (regs := sm_regs cx) in *. set (R := ms_regs ms3) in *. set (m3 := ms_mem ms3) in *.
set (sp := srm_sp cx) in *.
set (F := srm_F cx fpos) in *. set (FL := srm_FL cx fpos) in *. set (SH := srm_SH cx fpos) in *.
assert (Esp : spZ regs = sp) by reflexivity.
rewrite Esp in Hwlo, Hwhi, Hsp16.
assert (HROW : alloc_ceiling <= ly_stk_lo (sm_lyc cx) /\ ly_stk_hi (sm_lyc cx) <= 2 ^ 47 /\
  ly_stk_lo (sm_lyc cx) + sm_STK cx <= sm_sp0 cx /\ sm_sp0 cx + sm_XO cx <= ly_stk_hi (sm_lyc cx))
  by (eapply ajournal_gx_row; exact HJ).
assert (Hspr : 0 <= sp < 2 ^ 64) by (unfold sp, srm_sp, spZ; apply bv_unsigned_in_range).
assert (HKv : REAC_SERVED_MARK_AK = 9504) by reflexivity.
assert (HXO0 : 0 <= sm_XO cx) by (destruct HJ as (_ & HX & _); exact HX).
assert (HspK : alloc_ceiling <= sp - REAC_SERVED_MARK_AK) by lia.
assert (HAR3 : AR SEGS B ly3 S3 W3 m3 md3) by (eapply ajournal_gx_AR; exact HJ3).
assert (HinF : In (SRM_CID, fpos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
assert (E3 : frame_addr ly3 SRM_CID fpos = frame_addr (sm_ly cx) SRM_CID fpos /\
             flag_addr ly3 SRM_CID fpos = flag_addr (sm_ly cx) SRM_CID fpos)
  by (eapply aj_gx_frame_addr; srxh).
assert (Ecl : frame_addr (sm_lyc cx) SRM_CID fpos = frame_addr (sm_ly cx) SRM_CID fpos /\
              flag_addr (sm_lyc cx) SRM_CID fpos = flag_addr (sm_ly cx) SRM_CID fpos)
  by (eapply aj_gx_frame_addr; srxh).
assert (EF : frame_addr ly3 SRM_CID fpos = F)
  by (unfold F, srm_F; rewrite (proj1 E3), (proj1 Ecl); reflexivity).
assert (EFl : frame_addr (sm_lyc cx) SRM_CID fpos = F) by reflexivity.
assert (HFB : 4096 <= frame_addr (sm_lyc cx) SRM_CID fpos /\
  frame_addr (sm_lyc cx) SRM_CID fpos + fs_frame_bytes SRM_CID <= alloc_ceiling /\
  in_app (frame_addr (sm_lyc cx) SRM_CID fpos) (fs_frame_bytes SRM_CID))
  by (eapply frames_bounds; try first [exact LAWS | exact HAR1 | exact HinF]).
destruct HFB as (HF4096 & HFceil & HFapp).
rewrite EFl in HF4096, HFceil, HFapp. change (fs_frame_bytes SRM_CID) with 512 in HFceil, HFapp.
assert (HAL : frame_addr (sm_lyc cx) SRM_CID fpos mod 64 = 0 /\
  fs_frame_bytes SRM_CID mod 64 = 0 /\ 64 <= fs_frame_bytes SRM_CID)
  by (eapply frame_al64; try first [exact LAWS | exact HAR1 | exact HinF]).
destruct HAL as (HFal & _ & _).
rewrite EFl in HFal.
assert (HSHeq : SH = SHADOW_OFF + F / 8) by reflexivity.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
assert (HF8 : 0 <= F / 8 /\ F / 8 + 64 <= (F + 512) / 8).
{ split; [apply Z.div_pos; lia|]. replace (F + 512) with (F + 64 * 8) by lia. rewrite Z.div_add by lia. lia. }
assert (HF8c : (F + 512) / 8 <= 17592184995840).
{ replace 17592184995840 with (140737479966720 / 8) by reflexivity. apply Z.div_le_mono; lia. }
assert (HSHr : 0 <= SH < 2 ^ 64) by (unfold SHADOW_OFF in *; lia).
assert (HSHhi : SH + 64 <= 2 ^ 64) by (unfold SHADOW_OFF in *; lia).
assert (HSH8 : SH mod 8 = 0).
{ destruct (div8_of_mul64 F HFal) as (E8m & _).
  unfold SH, srm_SH, shadow_addr. fold F. rewrite E8m. unfold SHADOW_OFF. lia. }
assert (USH : bv_unsigned (w64 SH) = SH) by (unfold w64; apply unsigned_lit_small; lia).
(* ---- the environment and the symbolic state at the RESTORE cut ---- *)
set (E := Eimg (Ereg R ([] : list word))).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg R ([] : list word)) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (EREG : forall n (r : Prelude.reg), Z.of_nat n = bv_unsigned r -> ew E n = getr R r).
{ intros n r Hr. rewrite EL; [exact (ew_Ereg_nat _ _ n r Hr)|].
  pose proof (u5_range r) as Hu. unfold A_TEXT. lia. }
assert (E18 : ew E 18 = w64 SH) by (rewrite (EREG 18%nat 18%bv eq_refl); exact R18).
assert (U18 : bv_unsigned (ew E 18) = SH) by (rewrite E18; exact USH).
assert (HS0 : st_ok_pi SEGS VAL E srx_ssR (restrict (w_H W3) ms3)).
{ rewrite (srx_ms_eta ms3 Zfrg Zsvc Zrsv Zfcsr), Hpc, Zrom, restrict_mkst_fx.
  unfold srx_ssR. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold region_ok, srx_SHR.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U18. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (xf_wr SEGS); apply HSpres; unfold SRM_SHN; lia|]. apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint].
    repeat split; exact I.
  - split; [|split; [exact I | exact I]].
    cbn [srx_factsR f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U18. change (2 ^ 3) with 8. repeat split; try lia; try exact HSH8. }
(* ---- the run +0x2cc .. +0x360: the 36 shadow stores ---- *)
pose proof (paj_run_to_plain_x SK B LAWS (sm_G cx) HGX (sm_XO cx) (sm_OUT cx)) as RUNT.
lazymatch type of HS0 with
| st_ok_pi _ _ _ ?ss _ =>
  let tpi := srx_tpi RUNT in
  let r := eval vm_compute in (sym_run_toN_pi tpi FUEL SRM_CUT_EXIT ss) in
  lazymatch r with
  | (?ss', ?st) =>
    assert (Hrun : sym_run_toN_pi tpi FUEL SRM_CUT_EXIT ss = (ss', st)) by (vm_compute; reflexivity)
  end
end.
eapply RUNT; try first [exact HEI | exact HS0 | exact Hrun | exact I | exact HJ3].
{ intros a (r & Hr & Ha). cbn [In] in Hr.
  destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val srx_SHR] in Ha.
  rewrite U18 in Ha. left.
  eapply (aj_gx_awr_frame SK SEGS B LAWS SLOW); [exact HJ3 | left; reflexivity|].
  right. unfold in_zr. cbn [fst snd]. rewrite EF. unfold shadow_addr.
  change (fs_frame_bytes SRM_CID / 8) with 64. unfold SH, srm_SH, shadow_addr in Ha. fold F in Ha. lia. }
clear Hrun.
intros ms4 mat4 HS4 HJ4 _ HFr4 HG4.
set (md4 := with_vm_backing (m_vm_lazy md3) mat4 md3) in *.
(* the shape of the state the run reached *)
assert (Hms4 : ms4 = mkst (ms_regs ms4) (Z_to_bv 64 (BASE + SRM_CUT_EXIT)) (ms_mem ms4) (seg_rom SEGS)).
{ lazymatch type of HS4 with st_ok_pi _ _ _ ?ssx _ =>
    assert (Epc : ss_pc ssx = SRM_CUT_EXIT) by (vm_compute; reflexivity);
    rewrite <- Epc; eapply st_ok_pi_restrict_mkst;
      try first [ exact HS4 | (vm_compute; reflexivity) ]
  end. }
destruct (ms_shape_mkst SEGS ms4 _ _ _ Hms4) as (Z4rsv & Z4svc & Z4rom & Z4frg & Z4fcsr & Z4pc).
(* the registers: the run writes only a0 *)
assert (HKREG : forall r, In r srx_kregs -> getr (ms_regs ms4) r = getr R r).
{ intros r Hr.
  exact (regs_kept_of_st_ok_pi E _ (restrict (w_H W3) ms4) R ([] : list word) srx_kregs HS4
    ltac:(split;
      [ intros n Hn; first [apply Eimg_low | symmetry; apply Eimg_low]; unfold A_TEXT; lia
      | reflexivity ])
    ltac:(vm_compute; reflexivity) r Hr). }
assert (KR : forall (r : Prelude.reg), In r srx_kregs -> getr (ms_regs ms4) r = getr R r)
  by exact HKREG.
(* what the run changed: only the two buffers' shadow bytes, inside F's shadow *)
assert (HKEEP4 : forall a, 0 <= a < 2 ^ 64 -> ~ (SH + 4 <= a < SH + 44) ->
  aview SEGS (w_H W3) (ms_mem ms4) a = aview SEGS (w_H W3) m3 a).
{ intros a Ha Hn. apply (YCbq.aview_eq_of SEGS). apply HFr4.
  rewrite unsigned_lit_small by lia.
  intros (r & Hr & Hra). cbn [In] in Hr.
  destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val srx_SHR] in Hra.
  rewrite U18 in Hra. lia. }
assert (HSIDE4 : forall a, SH + 4 <= a < SH + 44 -> aside_rng (sm_lyc cx) SRM_CID fpos a).
{ intros a Ha. apply srx_side_unfold. right. left. unfold SH, srm_SH, shadow_addr in Ha. fold F in Ha.
  rewrite EFl. lia. }
assert (HKEEPS : forall a, 0 <= a < 2 ^ 64 -> ~ aside_rng (sm_lyc cx) SRM_CID fpos a ->
  aview SEGS (w_H W3) (ms_mem ms4) a = aview SEGS (w_H W3) m3 a)
  by (intros a Ha Hs; apply HKEEP4; [exact Ha | intros Hc; exact (Hs (HSIDE4 a Hc))]).
assert (HPRS4 : forall a, apresent (w_H W3) m3 a -> apresent (w_H W3) (ms_mem ms4) a)
  by (intros a Ha; exact (srx_apresent_grows (w_H W3) m3 (ms_mem ms4) a HG4 Ha)).
(* ---- the EXIT cut at the state the run reached ---- *)
eapply (HEXIT cx fpos ly3 S3 W3 ms4 md4 HPRE0 HGS).
exists rcv. split; [|split; [|split]].
- rewrite Z4pc. reflexivity.
- rewrite (KR 21%bv ltac:(cbv; tauto)). exact R21.
- eapply (srx_pf_move cx fpos ly3 S3 W3 ms3 md3 rcv (ms_mem ms4) S3 md4 HPRE0 HBASE0 HPF HKEEPS HPRS4);
  [ eapply ajournal_gx_AR; exact HJ4 | reflexivity ].
- (* srm_base at the new state *)
  unfold srm_base. cbv zeta. srx_splitn 32%nat.
  + exact Z4rsv.
  + exact Z4svc.
  + exact Z4rom.
  + exact Z4frg.
  + exact Z4fcsr.
  + exact HJ4.
  + exact Hfrs3.
  + exact Hnin.
  + exact HfsS3.
  + exact Hperm.
  + exists S1, W1, mem1, md1. split; [exact HAR1 | split; [exact Hfrs1 | exact Hbl1]].
  + rewrite (KR 2%bv ltac:(cbv; tauto)). exact R2.
  + rewrite (KR 9%bv ltac:(cbv; tauto)). exact R9.
  + rewrite (KR 8%bv ltac:(cbv; tauto)). exact R8.
  + rewrite (KR 18%bv ltac:(cbv; tauto)). exact R18.
  + rewrite (KR 19%bv ltac:(cbv; tauto)). exact R19.
  + rewrite (KR 25%bv ltac:(cbv; tauto)). exact R25.
  + rewrite (KR 26%bv ltac:(cbv; tauto)). exact R26.
  + rewrite (KR 20%bv ltac:(cbv; tauto)). exact R20.
  + rewrite (KR 22%bv ltac:(cbv; tauto)). exact R22.
  + rewrite (KR 3%bv ltac:(cbv; tauto)). exact R3.
  + rewrite (KR 4%bv ltac:(cbv; tauto)). exact R4.
  + rewrite (KR 27%bv ltac:(cbv; tauto)). exact R27.
  + rewrite (srx_rdword_agree (aview SEGS (w_H W3) m3) (aview SEGS (w_H W3) (ms_mem ms4))
      (srm_sp cx - 8)).
    * exact Hra8.
    * intros x Hx. fold sp in Hx. apply HKEEP4; [lia | unfold SH, srm_SH, shadow_addr; fold F; unfold SHADOW_OFF; lia].
  + intros j Hj.
    rewrite (srx_rdword_agree (aview SEGS (w_H W3) m3) (aview SEGS (w_H W3) (ms_mem ms4))
      (srm_sp cx - 16 - 8 * j)).
    * exact (Hsav j Hj).
    * intros x Hx. fold sp in Hx. apply HKEEP4; [lia | unfold SH, srm_SH, shadow_addr; fold F; unfold SHADOW_OFF; lia].
  + rewrite (srx_rdword_agree (aview SEGS (w_H W3) m3) (aview SEGS (w_H W3) (ms_mem ms4))
      (srm_F cx fpos + SRM_FLAGPTR)).
    * exact Hflag.
    * intros x Hx. fold F in Hx. apply HKEEP4; [unfold SRM_FLAGPTR in *; lia|].
      unfold SH, srm_SH, shadow_addr. fold F. unfold SHADOW_OFF, SRM_FLAGPTR in *. lia.
  + intros a Ha. exact (HPRS4 a (HFpres a Ha)).
  + intros a Ha. exact (HPRS4 a (HSpres a Ha)).
  + eapply (akept_step SK SEGS B LAWS SLOW (sm_lyc cx) (sm_Sc cx) (sm_W cx) (sm_memc cx) (sm_mdc cx)
      W3 m3 W3 (ms_mem ms4) (sp - REAC_SERVED_MARK_AK) sp _ _ (aside_rng (sm_lyc cx) SRM_CID fpos));
    [ eapply ajournal_gx_AR; exact HJ | exact HspK | lia | exact HK3 | exact HKEEPS | | | ].
    * intros a _ Hp. exact (HPRS4 a Hp).
    * intros a Ha. exact Ha.
    * intros a Ha. left. right. exact Ha.
  + unfold md4. destruct (srx_wvb_fds_fs (m_vm_lazy md3) mat4 md3) as (A1 & _). rewrite A1. exact Hfds3.
  + unfold md4. destruct (srx_wvb_fds_fs (m_vm_lazy md3) mat4 md3) as (_ & A2). rewrite A2. exact Hfs3.
  + (* the read-only image: the shadow bytes the run wrote are off the image *)
    intros a Hro Hown Herr.
    assert (Hin : in_img SEGS a).
    { destruct Hro as [(s & Hs & Hw & Hb) | Hw]; [exists s; split; [exact Hs | exact Hb] | exact (RELRO_IMG a Hw)]. }
    assert (Hlow : 0 <= a < kLowMemEnd) by exact (SLOW a Hin).
    rewrite HKEEP4; [exact (HRO3 a Hro Hown Herr) | unfold kLowMemEnd in Hlow; lia |].
    unfold SH, srm_SH, shadow_addr, SHADOW_OFF, kLowMemEnd in *. lia.
  + exact Hfrm0.
Qed.

End b.
End a.

About srm_exit_ok.
About srm_restore_ok.
Print Assumptions srm_exit_ok.
Print Assumptions srm_restore_ok.
