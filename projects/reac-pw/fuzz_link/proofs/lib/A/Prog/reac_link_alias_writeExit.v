(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextEntry), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/NextEntry.v at a working branch af735a950e2 (blob 8725db69d2a; the walk was ported from blob 7788bf8f6e4 at a working branch afd75724b5b, which differs from it only by 4 added and 0 removed lines, the licence header), restated over image B's listing, addresses and walk layer (lib/B/Prog) against GrantBContracts.v; frame 96 with twelve saved registers, UBSan traps T1 and T2, and the .rodata divisor read at 0x85fa4 (IMG_NEXT_DIV3) *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/NextEntry.v, with its module paths and module names changed; 542 of its 591 lines of code are new or changed and 711 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_link_alias_readExit.v, with its module names changed; 478 of its 531 lines of code are new or changed and 538 lines of the source are left out. *)
(* reac_link_alias_write (fuzz_link.asan 0x88f54) on image A: THE EXIT PIECE of its walk, `aw_exit_obl` of
   lib/A/Prog/reac_link_alias_writeDefs.v. From the exit cut +0x3a4 (0x892f8) the code
     +0x3a4..+0x3ac  stores the retired magic 0x45e0360e at F + 0 (sd a0,0(s8))
     +0x3b0          `beqz s3` -> +0x3cc, not taken: F >= 4096 (the fact on F's atom decides it)
     +0x3b4..+0x3bc  meta_fill_f5(F's shadow, 64) (0x55f7c)
     +0x3c0..+0x3c4  `ld a0,0x1f8(s3); sb zero,0(a0)`: the inline release of the frame's flag byte
     +0x49c..+0x4d0  a0 := s5; the eleven restores from the saves at sp0 - 8 .. sp0 - 80; `ret`
   and this file builds the whole post `aw_post` (link_amem.v apost over the caller's journal) from it.

   The runs are the PLAIN gx runs of lib/A/Prog/LinkWalkSide.v (`paj_run_call_plain_x`, `paj_flag_plain_x`):
   the state's writable windows are F's first word and the flag byte. meta_fill_f5 is LinkWalkSide.v's
   `aj_gx_set_shadow_at` over the Section hypothesis `aset_shadow_realizes ... 0xf5` (discharged at the image by
   lib/A/Rt/SetShadow.v `link_set_shadow_f5`); the return is LinkPaLib.v `paj_ret_at`, the post LinkWalkSide.v
   `apost_side_gen`.

   The memory algebra is the named lemma `aw_pf_move`: the cut's result `aw_pf` survives any step that changes
   only bytes of the call's side frame, its shadow and its flag byte. It ties the interface table at the cut to the
   call's read set through the table's pointer cells, which lie outside the write set and outside the runtime's
   statics (`PcapSyms B`), and then uses LinkWalkShadow.v `akb_not_side` (a read-set byte is no byte of the
   side frame, in all four `akb` cases). The kept clause of the post is the cut's `akept` carried across the
   epilogue by LinkWalkSide.v `akept_step`.

   The view transport and uniqueness lemmas are in lib/A/Prog/reac_link_alias_writeArmsA.v (aw_anlk_move,
   aw_aiftab_move, aw_acstr_range, aw_au64_det). The run tactics and the state construction follow libreac/fuzz_pcap's
   lib/A/Prog/PcapSourceOpenB.v `opb_epi` and PcapFrame.v `paj_run_flag_sh` (origin/ossv/recipes).

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 SetShadowDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import nl_talk_c reac_link_alias_write_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro reac_link_alias_writeDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_link_alias_writeArmsA LinkWalkShadow.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   0. The symbolic state at the exit cut
   Atoms 0..31 are the registers at the cut; 32..41 the ten saved words (ra, s0, s1, s2..s8 of the entry);
   42 the frame's flag address (the word at F + 504). s3 = s8 = F is atom 19.
   ========================================================================== *)
Definition awx_FR : YP09.region := YP09.mkRegion (Some 19%nat) 0 512 0 8 [YP09.mkChunk 504 (CVal 8 (SOff 42 0))].
Definition awx_FL0 : YP09.region := YP09.mkRegion (Some 42%nat) 0 1 0 0 [].
Definition awx_FL : YP09.region := YP09.mkRegion (Some 42%nat) 0 1 0 1 [].
Definition awx_saves_chunks : list YP09.chunk :=
  map (fun j => YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0))) (seq 0 10).
Definition awx_saves : YP09.region := YP09.mkRegion (Some 8%nat) (-80) 0 0 0 awx_saves_chunks.
Definition awx_facts : facts := mkFacts [(19%nat, HPTR 6); (42%nat, HPTR 0)] [] [].
Definition awx_ss0 : sstate := mkSS AW_CUT_EXIT sr_atoms [awx_FR; awx_FL0; awx_saves] None awx_facts.

(* ==========================================================================
   1. Small helpers
   ========================================================================== *)
Lemma awx_ms_eta `{fx : YK11.FPState} : forall ms : machine_state,
  ms_fregs ms = fp_regs -> ms_svc_pending ms = None -> ms_resv ms = None -> ms_fcsr ms = fp_csr ->
  ms = mkst (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (ms_rom ms).
Proof. intros [] H1 H2 H3 H4; cbn in *; subst; reflexivity. Qed.

Lemma awx_wvb_fds_fs : forall l X m, m_fds (with_vm_backing l X m) = m_fds m /\ m_fs (with_vm_backing l X m) = m_fs m.
Proof. intros l X []. split; reflexivity. Qed.

Lemma awx_sbm_fds_fs : forall m m', same_but_materialized m m' -> m_fds m' = m_fds m /\ m_fs m' = m_fs m.
Proof. intros m m' H. rewrite H. apply awx_wvb_fds_fs. Qed.

Lemma awx_apresent_grows : forall (H : word -> bool) (m m' : word -> option byte) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a HG [Hh [b Hb]]. split; [exact Hh|].
specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG. rewrite Hh in HG. rewrite Hb in HG.
destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; apply HG; [discriminate | reflexivity]].
Qed.

(* the three bytes classes of the side frame (3, fpos), unfolded *)
Lemma awx_side_unfold : forall ly fpos a,
  aside_rng ly 3 fpos a <->
  (frame_addr ly 3 fpos <= a < frame_addr ly 3 fpos + 512) \/
  (SHADOW_OFF + frame_addr ly 3 fpos / 8 <= a < SHADOW_OFF + frame_addr ly 3 fpos / 8 + 64) \/
  a = flag_addr ly 3 fpos.
Proof.
intros ly fpos a. unfold aside_rng, in_zr, frame_rng, shadow_addr. cbn [fst snd].
change (fs_frame_bytes 3) with 512. change (512 / 8) with 64. tauto.
Qed.


(* ==========================================================================
   3. The exit piece
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
(* The runtime's symbols of image A: AF0m.v PcapSyms, instance lib/A/AD2l.v PcapB_syms. Used for the runtime's
   statics only (ts_owned), to place g_nl's interface-table cells outside them. *)
Hypothesis HB : PcapSyms B.
(* The segments the listing is certified against (the library walks' convention): used only to place g_nl's bytes in
   the image and in a writable segment (a computation over tfibsegs). The link PAImg instance discharges it by
   reflexivity. *)
Hypothesis HSEGS : SEGS = tfibsegs.
(* meta_fill_f5 (0x55f7c): discharged at the image by lib/A/Rt/SetShadow.v link_set_shadow_f5. *)
Hypothesis ASS : aset_shadow_realizes SEGS B (pa_sigma LS___asan_set_shadow_f5) 0xf5.

(* ---- g_nl: in the image, writable, outside the runtime's statics ---- *)
Lemma awx_gnl_not_owned : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> ~ Exists (in_zr a) (as_owned_static B).
Proof.
intros a Ha Hex. rewrite (ts_owned _ HB) in Hex.
assert (C : forallb (fun r : Z * Z => (fst r + snd r <=? LA_G_NL) || (LA_G_NL + NK_SIZE <=? fst r))%bool
  Tfib_owned_static = true) by (vm_compute; reflexivity).
apply Exists_exists in Hex as (r & Hr & Hz). rewrite forallb_forall in C. specialize (C r Hr).
unfold in_zr in Hz. apply Bool.orb_true_iff in C as [C|C]; apply Z.leb_le in C; lia.
Qed.

Lemma awx_gnl_img : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> in_img SEGS a.
Proof.
intros a Ha. rewrite HSEGS.
destruct (find_segment tfibsegs LA_G_NL NK_SIZE) as [sg|] eqn:Hf; [|vm_compute in Hf; discriminate Hf].
destruct (find_segment_hit _ _ _ _ Hf) as (Hin & H1 & H2). exists sg. split; [exact Hin | lia].
Qed.

Lemma awx_gnl_writable : forall m a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> writable_at SEGS m a.
Proof. intros m a Ha. rewrite HSEGS. apply LA_G_NL_writable. unfold NK_SIZE in Ha. exact Ha. Qed.

Lemma awx_jAR : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k -> AR SEGS B ly' S' W' mem' md'.
Proof. intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k (_ & _ & (memS & HJi & _) & _). exact (proj1 HJi). Qed.

(* ---- the cut's result survives a step that changes only bytes of the side frame (3, fpos) ---- *)
Lemma aw_pf_move : forall cx fpos ly3 S3 W3 ms3 md3 rcv (m5 : word -> option byte),
  aw_pre SK B cx -> aw_base SK B cx fpos ly3 S3 W3 ms3 md3 -> aw_pf cx rcv W3 (ms_mem ms3) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ aside_rng (aw_lyc cx) 3 fpos a ->
     aview SEGS (w_H W3) m5 a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  aw_pf cx rcv W3 m5.
Proof.
intros cx fpos ly3 S3 W3 ms3 md3 rcv m5 HPRE HBASE HPF HKEEP.
unfold aw_base in HBASE. cbv zeta in HBASE.
destruct HBASE as (_ & _ & _ & _ & _ & HJ3 & Hfrs3 & Hnin & HfsS3 & Hperm & (S1 & W1 & mem1 & md1 & HAR1 & Hfrs1 & Hbl1)
  & Hfa3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HK3 & _).
destruct HPRE as (HAP & HRD & HAPRE).
pose proof HAP as (HJc & _).
destruct HAPRE as (kb0 & tb0 & nm0 & al0 & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & Herr) & _).
assert (HinF : In (3, fpos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
pose proof (frame_facts B (aw_lyc cx) S1 _ 3 fpos (proj1 HAR1) HinF) as (_ & Hfpos & _).
destruct HK3 as (_ & _ & K3 & _).
(* a byte outside the side frame is kept by the step *)
assert (HMB : forall x, 0 <= x < 2 ^ 64 -> ~ aside_rng (aw_lyc cx) 3 fpos x ->
  mbyte SEGS (rdW W3 m5) x = mbyte SEGS (rdW W3 (ms_mem ms3)) x).
{ intros x Hx Hs. apply (YCbq.mbyte_of_aview SEGS). apply HKEEP; assumption. }
(* g_nl's bytes are image bytes, hence not the side frame's *)
assert (HGS : forall x, LA_G_NL <= x < LA_G_NL + NK_SIZE -> ~ aside_rng (aw_lyc cx) 3 fpos x).
{ intros x Hx Hs. apply (proj2 (aside_rng_low SK SEGS B LAWS pa_segs_low _ _ _ _ _ 3 fpos x HAR1 HinF Hs)).
  exact (awx_gnl_img x Hx). }
assert (HGB : forall x, LA_G_NL <= x < LA_G_NL + NK_SIZE -> 0 <= x < 2 ^ 64)
  by (intros x Hx; unfold LA_G_NL, NK_SIZE in Hx; lia).
(* the table's cells at the cut are the call's *)
assert (HCELL : forall x, LA_G_NL + NK_IF_NAME <= x < LA_G_NL + NK_SIZE ->
  aview SEGS (w_H W3) (ms_mem ms3) x = aview SEGS (w_H (aw_W cx)) (aw_memc cx) x).
{ intros x Hx. assert (Hx' : LA_G_NL <= x < LA_G_NL + NK_SIZE) by (unfold NK_IF_NAME in Hx; lia).
  apply K3.
  - exact (awx_gnl_img x Hx').
  - exact (awx_gnl_not_owned x Hx').
  - unfold apart_gnl in Herr. destruct Herr; lia.
  - intros [HE | Hs].
    + unfold aw_E, aw_wr, reac_link_alias_write_awr, inFP in HE. destruct HE as (r & Hr & Hra).
      destruct Hr as [<- | []]. cbn [fst snd] in Hra. unfold NK_IF_NAME, NK_N_SENT in *. lia.
    + exact (HGS x Hx' Hs). }
intros kbs tab nm al NK IT SN SA.
pose proof (HPF kbs tab nm al NK IT SN SA) as HP. cbv zeta in HP |- *.
destruct HP as (Hrc & kbs' & N1 & N2 & N3 & N4 & N5 & N6 & N7).
split; [exact Hrc|]. exists kbs'.
refine (conj _ (conj N2 (conj N3 (conj N4 (conj N5 (conj _ N7)))))).
- apply (aw_anlk_move SEGS (rdW W3 (ms_mem ms3)) (rdW W3 m5) LA_G_NL kbs' N1).
  + intros x Hx. apply HMB; [exact (HGB x Hx) | exact (HGS x Hx)].
  + intros x Hx. apply awx_gnl_writable. exact Hx.
- pose proof N6 as (Lt & L80 & _).
  apply (aw_aiftab_move SEGS (rdW W3 (ms_mem ms3)) (rdW W3 m5) LA_G_NL kbs' tab N6).
  + intros x Hx. apply HMB; [apply HGB | apply HGS]; assumption.
  + intros i n2 ix p Hi Hp Hc x Hx.
    assert (Li : (i < length tab)%nat) by (apply nth_error_Some; congruence).
    pose proof (aw_acstr_range SEGS _ p n2 Hc) as Rp.
    (* the cell holds the call's pointer *)
    assert (Hp0 : au64_at SEGS (aw_m0 cx) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p).
    { unfold aw_m0. apply (val_mem_moved SEGS (w_H W3) (w_H (aw_W cx)) (ms_mem ms3) (aw_memc cx)
        (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) 8 p);
        [|exact Hp].
      intros k Hk. symmetry. apply HCELL. unfold NK_IF_NAME, NK_SIZE. lia. }
    pose proof IT as (_ & _ & IT0). destruct (IT0 i n2 ix Hi) as (_ & p0 & P0 & _ & C0 & _).
    pose proof (aw_acstr_range SEGS _ p0 n2 C0) as Rp0.
    pose proof (aw_au64_det SEGS _ _ p p0 Hp0 P0 ltac:(lia) ltac:(lia)) as Ep. subst p0.
    apply HMB; [lia|].
    apply (akb_not_side SK SEGS B pa_img_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK) (aw_sp cx) 3 fpos x HJc ltac:(lia) Hfpos Hnin).
    apply HRD. right. right. exists kbs, tab, i, n2, ix, p. exact (conj NK (conj IT (conj Hi (conj Hp0 (conj C0 Hx))))).
Qed.

(* ---- the contract's Post from the cut's result and a0 ---- *)
Lemma aw_apost_of_pf : forall cx rcv (W2 : world SEGS) (regs2 : bvmap 5 word) mem2,
  getr regs2 10 = w64 rcv -> aw_pf cx rcv W2 mem2 ->
  reac_link_alias_write_apost SEGS (aw_regs cx) (aw_m0 cx) regs2 (rdW W2 mem2).
Proof.
intros cx rcv W2 regs2 mem2 R10 HPF kbs tab nm al NK IT SN SA.
pose proof (HPF kbs tab nm al NK IT SN SA) as HP. cbv zeta in HP |- *.
destruct HP as (Hrc & HK). split; [rewrite R10, Hrc; reflexivity | exact HK].
Qed.

(* ---- the run tactics (PcapFrame.v paj_run_sh / paj_run_flag_sh, the call variant) ---- *)
Ltac aw_run_call RUNC HS HJ :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
    lazymatch type of RUNC with
    | forall W n E ss ss' s ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q, _ -> _ -> sym_runN_pi ?tpi n ss = _ -> _ =>
      let r := eval vm_compute in (sym_runN_pi tpi FUEL ss) in
      lazymatch r with
      | (?ss', PRS_call ?s) =>
        let Hrun := fresh "Hrun" in
        assert (Hrun : sym_runN_pi tpi FUEL ss = (ss', PRS_call s)) by (vm_compute; reflexivity);
        let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI end in
        eapply (RUNC W FUEL E ss ss' s ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun HJ);
        [ clear Hrun | clear Hrun ]
      | ?other => fail "aw_run_call: the run does not stop at a call:" other
      end
    end
  end.
Ltac aw_run_flag RUNF HS HJ :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
    lazymatch type of RUNF with
    | forall W n E ss ss' st ms STK sp0 FP ly S W0 mem md own' lyc Sc mdc k cid pos Q, _ -> _ -> sym_runN_pi ?tpi n ss = _ -> _ =>
      let r := eval vm_compute in (sym_runN_pi tpi FUEL ss) in
      lazymatch r with
      | (?ss', ?st) =>
        let Hrun := fresh "Hrun" in
        assert (Hrun : sym_runN_pi tpi FUEL ss = (ss', st)) by (vm_compute; reflexivity);
        let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI end in
        eapply (RUNF W FUEL E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun I HJ);
        [ clear Hrun | clear Hrun | clear Hrun | clear Hrun ]
      end
    end
  end.

(* ==========================================================================
   4. aw_exit
   ========================================================================== *)
Theorem aw_exit : aw_exit_obl SK B.
Proof.
intros cx fpos ly3 S3 W3 ms3 md3 HPRE HGI.
pose proof HPRE as HPRE0.
destruct HGI as (rcv & Hpc & R21 & HBASE & HPF).
pose proof HBASE as HBASE0.
unfold aw_base in HBASE. cbv zeta in HBASE.
destruct HBASE as (Zrsv & Zsvc & Zrom & Zfrg & Zfcsr & HJ3 & Hfrs3 & Hnin & HfsS3 & Hperm
  & (S1 & W1 & mem1 & md1 & HAR1 & Hfrs1 & Hbl1) & Hfa3 & R2 & R9 & R8 & R18 & R19 & R24 & R3 & R4 & R25 & R26 & R27
  & Hra8 & Hsav & Hflag & HFpres & HSpres & HK3 & Hfds3 & Hfs3 & _).
destruct HPRE as ((HJ & HGX & _ & Hraok & _ & Hgp & Htp & Hsp16 & Hwlo & Hwhi & _) & HRD & _).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_value as (ACv & _).
set (regs := aw_regs cx) in *. set (R := ms_regs ms3) in *. set (m3 := ms_mem ms3) in *.
set (sp := aw_sp cx) in *.
change (spZ regs) with sp in Hsp16, Hwlo, Hwhi.
change AW_CID with 3 in *.
set (F := aw_F cx fpos) in *. set (FL := aw_FL cx fpos) in *. set (SH := aw_SH cx fpos) in *.
(* ---- the journal's window and the stack ---- *)
pose proof HJ as (HSTK0 & HXO0 & (memS & HJi & _) & _).
pose proof HJi as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (Hspr : 0 <= sp < 2 ^ 64)
  by (pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hu; change (bv_modulus 64) with (2 ^ 64) in Hu; exact Hu).
assert (HKv : REAC_LINK_ALIAS_WRITE_AK = 8560) by reflexivity.
assert (HspK : alloc_ceiling <= sp - REAC_LINK_ALIAS_WRITE_AK) by lia.
assert (Hsp47 : sp <= 2 ^ 47) by lia.
(* ---- the frame, its shadow and its flag byte ---- *)
pose proof (awx_jAR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
assert (HinF : In (3, fpos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
assert (HinF3 : In (3, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
destruct (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 3 fpos HJ3) as (EF3 & EFL3).
destruct (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 3 fpos HJ) as (EFc & EFLc).
assert (EF : frame_addr ly3 3 fpos = F) by (unfold F, aw_F, AW_CID; rewrite EF3, EFc; reflexivity).
assert (EFL : flag_addr ly3 3 fpos = FL) by (unfold FL, aw_FL, AW_CID; rewrite EFL3, EFLc; reflexivity).
assert (EFl : frame_addr (aw_lyc cx) 3 fpos = F) by reflexivity.
assert (EFLl : flag_addr (aw_lyc cx) 3 fpos = FL) by reflexivity.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 fpos HAR1 HinF) as (HF4096 & HFceil & HFapp).
rewrite EFl in HF4096, HFceil, HFapp. change (fs_frame_bytes 3) with 512 in HFceil, HFapp.
pose proof (frame_al64 SEGS B _ _ _ _ _ 3 fpos HAR1 HinF) as (HFal & _ & _). rewrite EFl in HFal.
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 fpos HAR1 HinF) as (_ & _ & HFnown & HFSnown).
rewrite EFl in HFnown, HFSnown. change (fs_frame_bytes 3) with 512 in HFnown, HFSnown.
change (512 / 8) with 64 in HFSnown.
destruct (al_flag _ _ LAWS _ _ _ _ _ 3 fpos HAR1 HinF) as (_ & HFLown & HFLapp & HFLceil).
rewrite EFLl in HFLown, HFLapp, HFLceil.
assert (HSHeq : SH = SHADOW_OFF + F / 8) by reflexivity.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp, HFLapp.
destruct HFapp as (_ & HFapp'). destruct HFLapp as (HFL4096 & _).
assert (HF8 : 0 <= F / 8 /\ F / 8 + 64 <= (F + 512) / 8).
{ split; [apply Z.div_pos; lia|]. replace (F + 512) with (F + 64 * 8) by lia. rewrite Z.div_add by lia. lia. }
assert (HF8c : (F + 512) / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
change (0x7fffff800000 / 8) with 17592184995840 in HF8c.
assert (HSHb : SHADOW_OFF <= SH /\ SH + 64 <= SHADOW_OFF + 2 ^ 44) by (rewrite HSHeq; unfold SHADOW_OFF; lia).
assert (HFLnF : ~ (F <= FL < F + 512)) by (intros Hc; exact (proj2 (HFnown FL Hc) HFLown)).
assert (HFLnS : ~ (SH <= FL < SH + 64)).
{ intros Hc. apply (proj2 (HFSnown (FL - shadow_addr F) ltac:(unfold shadow_addr; lia))).
  replace (shadow_addr F + (FL - shadow_addr F)) with FL by lia. exact HFLown. }
assert (HdFL : FL + 1 <= F \/ F + 512 <= FL).
{ destruct (Z_lt_le_dec FL F) as [Hl|Hl]; [left; lia|].
  destruct (Z_lt_le_dec FL (F + 512)) as [Hh|Hh]; [exfalso; apply HFLnF; lia | right; lia]. }
assert (HFvsSH : forall a, F <= a < F + 512 -> ~ (SH <= a < SH + 64)).
{ intros a Ha Hc. unfold SHADOW_OFF in HSHb.
  destruct HFapp' as [H1 | (H1 & H2)]; lia. }
assert (HFb : 0 <= F < 2 ^ 64) by lia.
assert (HFLb : 0 <= FL < 2 ^ 64) by lia.
assert (HSHr : 0 <= SH < 2 ^ 64) by (unfold SHADOW_OFF in *; lia).
assert (UF : bv_unsigned (w64 F) = F) by (unfold w64; apply unsigned_lit_small; lia).
assert (UFL : bv_unsigned (w64 FL) = FL) by (unfold w64; apply unsigned_lit_small; lia).
assert (Usp : bv_unsigned (w64 sp) = sp) by (unfold w64; apply unsigned_lit_small; lia).
(* the realigned stack pointer s1 *)
destruct (sp1_facts (sp - AW_FRAME) ltac:(unfold AW_FRAME; lia)
  ltac:(unfold AW_FRAME; rewrite Zminus_mod, Hsp16; reflexivity)) as (Hsp1r & Hsp1al32 & Hsp1al16).
change (32 * ((sp - AW_FRAME) / 32)) with (aw_sp1 cx) in Hsp1r, Hsp1al32, Hsp1al16.
unfold AW_FRAME in Hsp1r.
set (sp1 := aw_sp1 cx) in *.
assert (Usp1 : bv_unsigned (w64 sp1) = sp1) by (unfold w64; apply unsigned_lit_small; lia).
(* ---- the environment: the registers at the cut, the saved words, the flag address ---- *)
set (extra := [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20;
               getr regs 21; getr regs 22; getr regs 23; getr regs 24; w64 FL]).
set (E := Eimg (Ereg R extra)).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg R extra) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (EREG : forall n (r : Prelude.reg), Z.of_nat n = bv_unsigned r -> ew E n = getr R r).
{ intros n r Hr. rewrite EL; [exact (ew_Ereg_nat _ _ n r Hr)|].
  pose proof (u5_range r) as Hu. unfold A_TEXT. lia. }
assert (EX : forall j, (j < 11)%nat -> ew E (32 + j) = nth j extra (w64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ j)).
assert (E19 : ew E 19 = w64 F) by (rewrite (EREG 19%nat 19%bv eq_refl); exact R19).
assert (E18 : ew E 18 = w64 SH) by (rewrite (EREG 18%nat 18%bv eq_refl); exact R18).
assert (E8 : ew E 8 = w64 sp) by (rewrite (EREG 8%nat 8%bv eq_refl); exact R8).
assert (E2 : ew E 2 = w64 sp1) by (rewrite (EREG 2%nat 2%bv eq_refl); exact R2).
assert (E42 : ew E 42 = w64 FL) by (exact (EX 10%nat ltac:(lia))).
assert (U19 : bv_unsigned (ew E 19) = F) by (rewrite E19; exact UF).
assert (U8 : bv_unsigned (ew E 8) = sp) by (rewrite E8; exact Usp).
assert (U42 : bv_unsigned (ew E 42) = FL) by (rewrite E42; exact UFL).
(* the saved words, as the saves region's chunks *)
assert (HSAV : forall j, (j < 10)%nat ->
  val_mem SEGS (rdW W3 m3) (sp + (-8 - 8 * Z.of_nat j)) 8 (bv_unsigned (nth j extra (w64 0)))).
{ intros j Hj. apply (val_mem_of_rdword SEGS (w_H W3) m3).
  destruct j as [|j'].
  - replace (sp + (-8 - 8 * Z.of_nat 0)) with (sp - 8) by lia. exact Hra8.
  - replace (sp + (-8 - 8 * Z.of_nat (S j'))) with (sp - 16 - 8 * Z.of_nat j') by lia.
    rewrite (Hsav (Z.of_nat j') ltac:(lia)). f_equal.
    do 9 (destruct j' as [|j']; [reflexivity|]). lia. }
assert (HCH : forall j, (j < 10)%nat -> YP09.chunk_ok SEGS E (rdW W3 m3) sp
   (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0)))).
{ intros j Hj.
  apply (chunk_ok_val SEGS E _ sp (-8 - 8 * Z.of_nat j) 8 (SOff (32 + j) 0)
    (bv_unsigned (nth j extra (w64 0))));
  [ cbn [sv_denot]; rewrite (EX j ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | pose proof (bv_unsigned_in_range 64 (nth j extra (w64 0))) as Hu; change (bv_modulus 64) with (2 ^ 64) in Hu;
    change (8 * Z.of_N 8) with 64; lia
  | zside
  | exact (HSAV j Hj) ]. }
(* ---- the symbolic state at the cut ---- *)
assert (HS0 : st_ok_pi SEGS VAL E awx_ss0 (restrict (w_H W3) ms3)).
{ rewrite (awx_ms_eta ms3 Zfrg Zsvc Zrsv Zfcsr), Hpc, Zrom, restrict_mkst_fx.
  unfold awx_ss0. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
      unfold region_ok, awx_FR, awx_FL0, awx_saves;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U19. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (YCbq.apresent_writable SEGS); apply HFpres; unfold AW_FB; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ F 504 8 (SOff 42 0) FL);
      [ cbn [sv_denot]; rewrite E42, Z.add_0_r, UFL; reflexivity
      | change (8 * Z.of_N 8) with 64; lia | zside
      | exact (val_mem_of_rdword SEGS (w_H W3) m3 _ _ Hflag) ].
    + rewrite U42. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_nil.
    + rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      unfold awx_saves_chunks. apply Forall_map, Forall_forall. intros j Hj.
      apply in_seq in Hj. apply HCH. lia.
  - apply pairwise_disjoint_of_extents.
    unfold awx_FR, awx_FL0, awx_saves, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U19, U42, U8.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [ (left; lia) | (right; lia) | (destruct HdFL; [right | left]; lia) ].
  - split; [|split; [exact I | exact I]].
    cbn [awx_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
    rewrite U19, U42. change (2 ^ 6) with 64. change (2 ^ 0) with 1.
    repeat split; first [lia | apply Z.mod_1_r]. }
assert (HS : st_ok_pi SEGS VAL E (mkSS (ss_pc awx_ss0) (sr_set (ss_regs awx_ss0) 24%bv (SOff 19 0))
  (ss_mem awx_ss0) (ss_resv awx_ss0) (ss_facts awx_ss0)) (restrict (w_H W3) ms3)).
{ apply (ast_ok_pi_set_reg_fp E _ _ (24%bv : bv 5) (SOff 19 0) HS0 ltac:(vm_compute; reflexivity)).
  rewrite (sv_off0 E 19 F E19). cbn [ms_regs restrict]. exact (eq_sym R24). }
clear HS0.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts awx_ss0] in HS.
clearbody E.
(* ---- the run +0x3a4 .. +0x3bc: the retired magic, `beqz s3` (not taken), up to meta_fill_f5 ---- *)
pose proof (paj_run_call_plain_x SK B LAWS (aw_G cx) HGX (aw_XO cx) (aw_OUT cx)) as RUNC.
aw_run_call RUNC HS HJ3.
{ intros a (r & Hr & Ha). cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val awx_FR awx_FL0 awx_saves] in Ha;
  [| exfalso; lia | exfalso; lia].
  rewrite U19 in Ha. left.
  apply (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 3 fpos a HJ3
    ltac:(left; reflexivity)).
  left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 3) with 512. lia. }
intros ms1 mat1 HS1 HJ1 _ HFr1 HG1.
(* the registers at the call *)
prreg HS1 (10%bv : bv 5) Q10. prreg HS1 (11%bv : bv 5) Q11. prreg HS1 (1%bv : bv 5) Q1.
prreg HS1 (2%bv : bv 5) Q2. prreg HS1 (3%bv : bv 5) Q3. prreg HS1 (4%bv : bv 5) Q4.
pmkst HS1.
set (sig5 := pa_sigma LS___asan_set_shadow_f5).
eapply SRr_bind.
{ eapply (aj_gx_set_shadow_at SK SEGS B LAWS pa_segs_low sig5 0xf5 ASS
    _ _ _ W3 (ms_regs ms1) (ms_mem ms1) _ _ _ _ _ _ _ _ _ ly3 S3 _ _
    3 fpos SH 64 (getr (ms_regs ms1) 1) HGX HJ1 ltac:(left; reflexivity)).
  - rewrite Q10, E18. reflexivity.
  - rewrite Q11. reflexivity.
  - lia.
  - rewrite EF. unfold shadow_addr. lia.
  - rewrite EF. unfold shadow_addr. change (fs_frame_bytes 3 / 8) with 64. lia.
  - unfold spZ. rewrite Q2, E2, Usp1. exact Hsp1al16.
  - unfold spZ. rewrite Q2, E2, Usp1. change ESTACK with 4096. lia.
  - unfold spZ. rewrite Q2, E2, Usp1. lia.
  - rewrite Q3, (EREG 3%nat 3%bv eq_refl), R3. exact Hgp.
  - rewrite Q4, (EREG 4%nat 4%bv eq_refl), R4. exact Htp.
  - reflexivity.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
cbv beta.
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hf5 & Hmf & Hpres2 & Hsbm2).
pose proof (awx_jAR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 fpos HAR2 HinF3) as (_ & _ & HFpres2 & _).
rewrite EF in HFpres2. change (fs_frame_bytes 3) with 512 in HFpres2.
destruct (al_flag _ _ LAWS _ _ _ _ _ 3 fpos HAR2 HinF3) as (HFLpres2 & _).
rewrite EFL in HFLpres2.
(* the state after the call *)
jafter_call_keep_pi HS1 48%nat regs2 (mrestrict (w_H W3) mem2) HP2 [0; 1; 2]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil;
    split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha.
  - rewrite U19 in Ha. apply (YCbq.mbyte_of_aview SEGS). apply Hmf; [lia|].
    apply HFvsSH. lia.
  - intros _. rewrite U19 in Ha. apply (YCbq.apresent_writable SEGS). apply (proj1 (HFpres2 a ltac:(lia))).
  - rewrite U42 in Ha. apply (YCbq.mbyte_of_aview SEGS). apply Hmf; [lia|]. intros Hc. apply HFLnS.
    replace FL with a by lia. exact Hc.
  - exfalso; lia.
  - rewrite U8 in Ha. apply (YCbq.mbyte_of_aview SEGS). apply Hmf; [lia|]. unfold SHADOW_OFF in *; lia.
  - exfalso; lia. }
rewrite <- restrict_mkst_fx in HS2.
assert (Hraw : getr (ms_regs ms1) 1 = Z_to_bv 64 (BASE + 29000)) by (rewrite Q1; reflexivity).
rewrite Hraw.
remember (havoc E 48 (map (getr regs2) CLOB)) as Ev2 eqn:HE2 in HS2.
assert (HEI2 : img_env VAL A_LIM Ev2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall nn, (nn < 48)%nat -> ew Ev2 nn = ew E nn)
  by (intros nn Hnn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hnn).
clear HE2.
assert (V19 : bv_unsigned (ew Ev2 19) = F) by (rewrite OLD2 by lia; exact U19).
assert (V42 : bv_unsigned (ew Ev2 42) = FL) by (rewrite OLD2 by lia; exact U42).
assert (V8 : bv_unsigned (ew Ev2 8) = sp) by (rewrite OLD2 by lia; exact U8).
(* the flag byte becomes writable *)
lazymatch type of HS2 with st_ok_pi _ _ _ ?ssx ?msx =>
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) awx_FL0) in
  pose proof (st_ok_pi_region_nth Ev2 ssx msx 1 r1 HS2 ltac:(vm_compute; reflexivity)) as HR1;
  pose proof (ast_ok_pi_set_region Ev2 ssx msx 1 r1 (set_window r1 0 1) HS2 ltac:(vm_compute; reflexivity)
    ltac:(reflexivity) ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS Ev2 _ r1 0 1 HR1 ltac:(intros o Ho; cbn [YP09.r_base base_val];
       rewrite V42; replace (FL + o) with FL by lia; cbn [ms_mem restrict mkst];
       apply (YCbq.apresent_writable SEGS); exact HFLpres2))) as HS3
end.
clear HS2 HR1. norm_pi HS3.
(* ---- the run +0x3c0 .. +0x4d0: the inline release, a0 := s5, the restores, up to `ret` ---- *)
pose proof (paj_flag_plain_x SK B LAWS (aw_G cx) HGX (aw_XO cx) (aw_OUT cx)) as RUNF.
aw_run_flag RUNF HS3 HJ2.
{ try unfold AW_CID; lia. }
{ intros a (r & Hr & Ha). cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  - rewrite V19 in Ha. left.
    apply (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 3 fpos a HJ2
      ltac:(left; reflexivity)).
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 3) with 512. lia.
  - rewrite V42 in Ha. right. right. right. rewrite EFL. lia.
  - exfalso; lia. }
{ intros msr HSr.
  lazymatch type of HSr with st_ok_pi _ _ _ ?ssx _ =>
    let r1 := eval vm_compute in (nth 1 (ss_mem ssx) awx_FL) in
    pose proof (st_ok_pi_region_nth Ev2 ssx msr 1 r1 HSr ltac:(vm_compute; reflexivity)) as HR1;
    pose proof (field_of_region Ev2 (ms_mem msr) 42 FL _ 0 1 0 1 0 1%N (SLit 0) 0 HR1 V42
      ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(clear; lia) ltac:(clear; lia)) as Vfl;
    change (N.to_nat 1) with 1%nat in Vfl; specialize (Vfl 0%nat ltac:(clear; lia));
    replace (FL + 0 + Z.of_nat 0) with FL in Vfl by (clear; lia);
    rewrite EFL, Vfl; reflexivity
  end. }
intros ms5 mat5 HS5 HJ5 _ HFr5 HG5.
(* ---- `ret` ---- *)
prreg HS5 (1%bv : bv 5) P1. prreg HS5 (2%bv : bv 5) P2. prreg HS5 (3%bv : bv 5) P3.
prreg HS5 (4%bv : bv 5) P4. prreg HS5 (8%bv : bv 5) P8. prreg HS5 (9%bv : bv 5) P9.
prreg HS5 (10%bv : bv 5) P10. prreg HS5 (18%bv : bv 5) P18. prreg HS5 (19%bv : bv 5) P19.
prreg HS5 (20%bv : bv 5) P20. prreg HS5 (21%bv : bv 5) P21. prreg HS5 (22%bv : bv 5) P22.
prreg HS5 (23%bv : bv 5) P23. prreg HS5 (24%bv : bv 5) P24. prreg HS5 (25%bv : bv 5) P25.
prreg HS5 (26%bv : bv 5) P26. prreg HS5 (27%bv : bv 5) P27.
pose proof (paj_ret_at (L := link_listing) (PL := PL_link) (PI := PI) W3 Ev2 _ ms5
  (with_vm_backing (m_vm_lazy md2) mat5 md2) (aw_post SK B cx) HS5 eq_refl) as RET5.
apply RET5; [vm_compute; reflexivity|]. clear RET5.
intros mat6.
assert (Era : getr (ms_regs ms5) 1 = getr regs 1).
{ rewrite P1, OLD2 by lia. exact (EX 0%nat ltac:(lia)). }
unfold YK0s.ret_ok in Hraok. rewrite Era, Hraok.
pose proof (ajournal_gx_materialize SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat6 HJ5) as HJ6.
(* ---- what the epilogue changed: only bytes of the side frame ---- *)
assert (HWR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 8) ->
  aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) m3 a).
{ intros a Ha Hn. apply (YCbq.aview_eq_of SEGS). apply HFr1.
  rewrite unsigned_lit_small by lia.
  intros (r & Hr & Hra). cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val awx_FR awx_FL0 awx_saves] in Hra;
  [rewrite U19 in Hra; apply Hn; lia | lia | lia]. }
assert (HWR5 : forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 8) -> a <> FL ->
  aview SEGS (w_H W3) (ms_mem ms5) a = aview SEGS (w_H W3) mem2 a).
{ intros a Ha Hn Hfl. apply (YCbq.aview_eq_of SEGS). apply HFr5.
  rewrite unsigned_lit_small by lia.
  intros (r & Hr & Hra). cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra;
  [rewrite V19 in Hra; apply Hn; lia | rewrite V42 in Hra; apply Hfl; lia | lia]. }
assert (HKEEP : forall a, 0 <= a < 2 ^ 64 -> ~ aside_rng (aw_lyc cx) 3 fpos a ->
  aview SEGS (w_H W3) (ms_mem ms5) a = aview SEGS (w_H W3) m3 a).
{ intros a Ha Hs.
  assert (N1 : ~ (F <= a < F + 8))
    by (intros ?; apply Hs; apply (proj2 (awx_side_unfold _ fpos a)); left; rewrite EFl; lia).
  assert (N2 : a <> FL)
    by (intros ?; apply Hs; apply (proj2 (awx_side_unfold _ fpos a)); right; right; rewrite EFLl; assumption).
  assert (N3 : ~ (SH <= a < SH + 64))
    by (intros ?; apply Hs; apply (proj2 (awx_side_unfold _ fpos a)); right; left; rewrite EFl; lia).
  rewrite (HWR5 a Ha N1 N2), (Hmf a Ha N3). exact (HWR1 a Ha N1). }
assert (HPRS : forall a, apresent (w_H W3) m3 a -> apresent (w_H W3) (ms_mem ms5) a).
{ intros a Ha. apply (awx_apresent_grows (w_H W3) mem2); [exact HG5|]. apply Hpres2.
  exact (awx_apresent_grows (w_H W3) m3 (ms_mem ms1) a HG1 Ha). }
(* ---- the post ---- *)
unfold aw_post.
eapply (apost_side_gen SK SEGS B LAWS pa_segs_low REAC_LINK_ALIAS_WRITE_AK 0 (aw_E cx)
  (aw_G cx) (aw_XO cx) (aw_OUT cx) (aw_STK cx) (aw_sp0 cx) (aw_FP cx) (aw_ly cx) (aw_S cx) (aw_W0 cx)
  (aw_mem0 cx) (aw_md0 cx) (aw_own cx) (aw_lyc cx) (aw_Sc cx) (aw_W cx) (aw_memc cx) (aw_mdc cx) (aw_k cx)
  regs (ms_regs ms5) ly3 (stack_free_state 3 fpos S3) W3 (ms_mem ms5) _ (aw_k cx) 3 fpos S1 W1 mem1 md1 _
  HJ HJ6 ltac:(lia)).
- destruct (awx_wvb_fds_fs (m_vm_lazy (with_vm_backing (m_vm_lazy md2) mat5 md2)) mat6
    (with_vm_backing (m_vm_lazy md2) mat5 md2)) as (A1 & _).
  destruct (awx_wvb_fds_fs (m_vm_lazy md2) mat5 md2) as (A2 & _).
  destruct (awx_sbm_fds_fs _ _ Hsbm2) as (A3 & _).
  destruct (awx_wvb_fds_fs (m_vm_lazy md3) mat1 md3) as (A4 & _).
  rewrite A1, A2, A3, A4. exact Hfds3.
- destruct (awx_wvb_fds_fs (m_vm_lazy (with_vm_backing (m_vm_lazy md2) mat5 md2)) mat6
    (with_vm_backing (m_vm_lazy md2) mat5 md2)) as (_ & A1).
  destruct (awx_wvb_fds_fs (m_vm_lazy md2) mat5 md2) as (_ & A2).
  destruct (awx_sbm_fds_fs _ _ Hsbm2) as (_ & A3).
  destruct (awx_wvb_fds_fs (m_vm_lazy md3) mat1 md3) as (_ & A4).
  rewrite A1, A2, A3, A4. exact Hfs3.
- apply aregs_preserved_eqs.
  + rewrite P2, OLD2, E8 by lia. unfold w64, sp, aw_sp, spZ. apply Z_to_bv_bv_unsigned.
  + rewrite P3, OLD2, (EREG 3%nat 3%bv eq_refl) by lia. exact R3.
  + rewrite P4, OLD2, (EREG 4%nat 4%bv eq_refl) by lia. exact R4.
  + rewrite P8, OLD2 by lia. exact (EX 1%nat ltac:(lia)).
  + rewrite P9, OLD2 by lia. exact (EX 2%nat ltac:(lia)).
  + rewrite P18, OLD2 by lia. exact (EX 3%nat ltac:(lia)).
  + rewrite P19, OLD2 by lia. exact (EX 4%nat ltac:(lia)).
  + rewrite P20, OLD2 by lia. exact (EX 5%nat ltac:(lia)).
  + rewrite P21, OLD2 by lia. exact (EX 6%nat ltac:(lia)).
  + rewrite P22, OLD2 by lia. exact (EX 7%nat ltac:(lia)).
  + rewrite P23, OLD2 by lia. exact (EX 8%nat ltac:(lia)).
  + rewrite P24, OLD2 by lia. exact (EX 9%nat ltac:(lia)).
  + rewrite P25, OLD2, (EREG 25%nat 25%bv eq_refl) by lia. exact R25.
  + rewrite P26, OLD2, (EREG 26%nat 26%bv eq_refl) by lia. exact R26.
  + rewrite P27, OLD2, (EREG 27%nat 27%bv eq_refl) by lia. exact R27.
- exact HAR1.
- exact Hfrs1.
- exact Hbl1.
- apply (akept_step SK SEGS B LAWS pa_segs_low (aw_lyc cx) (aw_Sc cx) (aw_W cx) (aw_memc cx) (aw_mdc cx)
    W3 m3 W3 (ms_mem ms5) (sp - REAC_LINK_ALIAS_WRITE_AK) sp _ _ (aside_rng (aw_lyc cx) 3 fpos)
    (awx_jAR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) HspK ltac:(lia) HK3 HKEEP).
  + intros a _ Hp. exact (HPRS a Hp).
  + intros a Ha. exact Ha.
  + intros a Ha. left. right. exact Ha.
- cbv beta. split; [|split].
  + apply (set_fs_trans S3 (stack_free_state 3 fpos S3) (aw_Sc cx)).
    * apply set_fs_of_exists. exact HfsS3.
    * apply stack_free_state_set_fs.
  + rewrite stack_free_state_set_fs, ablocks_set_fs. exact Hperm.
  + apply (aw_apost_of_pf cx rcv W3 (ms_regs ms5) (ms_mem ms5)).
    * rewrite P10, OLD2, (EREG 21%nat 21%bv eq_refl) by lia. exact R21.
    * exact (aw_pf_move cx fpos ly3 S3 W3 ms3 md3 rcv (ms_mem ms5) HPRE0 HBASE0 HPF HKEEP).
Qed.

End b.
End a.

About aw_exit.
Print Assumptions aw_exit.
