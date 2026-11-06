(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/bzip2/bzip2_compress_target/lib/K/A/L_hkit.v, with its module paths and module names changed; 801 of its 858 lines of code are new or changed and 196 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/Prog/reac_served_unmark_all.v, with its module paths and module names changed; 980 of its 1095 lines of code are new or changed and 743 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_served_unmark_allReadK.v, with its module names changed; 634 of its 727 lines of code are new or changed and 1002 lines of the source are left out. *)
(* reac_served_unmark_all (fuzz_link.asan 0x89ed4, listing offset AF_reac_served_unmark_all) on image A, THE READ
   PIECE, stage 1: from the HEAD cut (+0x1d8, round c) through reac_link_alias_read to its return (+0x270).
     +0x1d8..+0x254  the alias buffer's 32 shadow bytes := 0 (s2 + 4 .. s2 + 0x23): a PLAIN run (the token engine
                     refuses a writable shadow window; LinkWalkSide.v paj_run_call_plain_x)
     +0x258..+0x26c  a4 := 256, a0 := s6 (m->name[c]), a1 := 0, a2 := 0, a3 := s5 (F + 32), jal 0x8867c
     the call        reac_link_alias_read_c.v reac_link_alias_read_acontract (Section hypothesis HRD) under SRr_bind
   It proves `um_read_a : forall c, um_from (fun cx => um_gi_rd cx c) -> um_head_obl c`, where um_gi_rd is the state
   at +0x270 (the read's answer in a0, its alias in F + 32, the model step taken), which
   reac_served_unmark_allReadB.v continues to MID / JOIN.

   Proves no function (kind: segment lemma of reac_served_unmark_all's walk). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit PcapRelro YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c reac_served_unmark_all_c reac_link_alias_read_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
LinkWalk LinkWalkSide LinkWalkPi LinkWalkCall LinkWalkShadow LinkWalkZsh.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_served_unmark_allDefs reac_served_unmark_allReadK.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_served_unmark_allTailVis.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AF0m AB1v.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* No global sink_head instance is in scope: every journal below is the Section's SK. *)
Fail Definition sink_head_probe_um_read_a : YI16.sink_head := _.

(* ==========================================================================
   0. The symbolic state at the HEAD cut: atoms 0..31 are the registers at the cut; F's shadow region (s2 = atom
      18), writable at s2 + 4 .. s2 + 0x23
   ========================================================================== *)
Definition UM_RET_RD : Z := AF_reac_served_unmark_all + 0x270.
Definition urd_SHR : YP09.region := YP09.mkRegion (Some 18%nat) 0 64 4 36 [].
Definition urd_facts : facts := mkFacts [(18%nat, mkAF 0x7fff8000 (0x7fff8000 + 2 ^ 44) 3)] [] [].
Definition urd_ss0 : sstate := mkSS UM_CUT_HEAD sr_atoms [urd_SHR] None urd_facts.

(* the stored byte of a `CVal 1 (SLit 0)` chunk *)
Definition urd_z1b (j : Z) (c : YP09.chunk) : bool :=
  (YP09.c_off c =? j) && match YP09.c_val c with CVal w (SLit z) => N.eqb w 1 && Z.eqb z 0 | _ => false end.

Lemma urd_z1b_in : forall j cs, existsb (urd_z1b j) cs = true -> In (YP09.mkChunk j (CVal 1 (SLit 0))) cs.
Proof.
  intros j cs H. apply existsb_exists in H as ([od cv] & Hin & Hb). unfold urd_z1b in Hb.
  cbn [YP09.c_off YP09.c_val] in Hb. apply andb_true_iff in Hb as [Hj Hv]. apply Z.eqb_eq in Hj. subst od.
  destruct cv; cbn in Hv; try discriminate. destruct v; cbn in Hv; try discriminate.
  apply andb_true_iff in Hv as [Hw Hz]. apply N.eqb_eq in Hw. apply Z.eqb_eq in Hz. subst. exact Hin.
Qed.

Section s.
Variable segs : list Segment.

Lemma urd_zero_byte : forall E m n b cs lo hi wlo whi j,
  region_ok segs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk j (CVal 1 (SLit 0))) cs -> mbyte segs m (b + j) = Some (zb 0).
Proof.
  intros E m n b cs lo hi wlo whi j HR Hb Hin.
  pose proof (field_of_region_any E m n b cs lo hi wlo whi j 1%N (SLit 0) HR Hb Hin ltac:(lia)) as V.
  specialize (V 0%nat ltac:(cbn; lia)). rewrite Z.add_0_r in V. rewrite V. reflexivity.
Qed.

(* every present byte of a range: a buffer of unknown contents *)
Lemma urd_abuf_present : forall (H : word -> bool) (m : word -> option byte) a n,
  0 <= a -> a + n <= 2 ^ 64 -> 0 <= n -> (forall x, a <= x < a + n -> apresent H m x) -> abuf segs (mrestrict H m) a n.
Proof.
  intros H m a n Ha Hn Hn0 HP.
  exists (map (fun i => match mrestrict H m (Z_to_bv 64 (a + Z.of_nat i)) with Some b => b | None => zb 0 end)
            (seq 0 (Z.to_nat n))).
  rewrite length_map, length_seq. split; [lia|]. split.
  - split; [exact Ha|]. split; [rewrite length_map, length_seq; lia|].
    intros i Hi. rewrite length_map, length_seq in Hi. rewrite nth_error_map, nth_error_seq.
    replace (i <? Z.to_nat n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi). cbn [option_map Nat.add].
    destruct (HP (a + Z.of_nat i) ltac:(lia)) as [Hh [b Hb]].
    unfold mbyte, mrestrict. rewrite Hh, Hb. reflexivity.
  - intros i Hi. rewrite length_map, length_seq in Hi. apply (YCbq.apresent_writable segs). apply HP. lia.
Qed.
End s.

Local Set Default Proof Using "All".
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
(* AR's laws (the frame); the listing's values (the link instance, LinkImgInst.v pi_link_vals); the start-up
   symbols (AF0m.v PcapSyms, instance lib/A AD2l.PcapB_syms); the segments for the computations over the image
   (LinkImgInst.v pi_link_segs); the relro window in the image (the top file); reac_link_alias_read's contract
   (lib/A/Prog/reac_link_alias_read.v reac_link_alias_read_aproof). *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : SEGS = tfibsegs.
Hypothesis RELRO_IMG : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.
Hypothesis LV : LinkVals.
Hypothesis HRD : reac_link_alias_read_acontract SK SEGS PCAP_RLO PCAP_RHI B.

(* +0x270, round c: reac_link_alias_read returned. a0 is its answer; its alias is the C string at F + 32; the model
   step of the round is taken as far as the answer and the alias decide it. *)
Definition um_gi_rd (cx : umcx) (c : nat) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  ms_pc_val ms3 = w64 (BASE + UM_RET_RD) /\
  um_loop cx c fpos W3 ms3 /\
  um_base SK B cx fpos ly3 S3 W3 ms3 md3 /\
  (forall i, 0 <= i < 32 -> aview SEGS (w_H W3) (ms_mem ms3) (um_SH cx fpos + 4 + i) = Some 0) /\
  exists kbs al,
    acstr_at SEGS (rdW W3 (ms_mem ms3)) (um_F cx fpos + UM_ALIAS) al /\
    (getr (ms_regs ms3) 10 <> w64 0 -> um_kinv cx (rdW W3 (ms_mem ms3)) kbs (S c)) /\
    (getr (ms_regs ms3) 10 = w64 0 -> bl_eqb al S_SERVED = false -> um_kinv cx (rdW W3 (ms_mem ms3)) kbs (S c)) /\
    (getr (ms_regs ms3) 10 = w64 0 -> bl_eqb al S_SERVED = true -> um_kinv_mid cx (rdW W3 (ms_mem ms3)) kbs c).

Section c.
Variable cx : umcx.
Variable fpos : Z.
Hypothesis HPRE : um_pre SK B cx.
Hypothesis HNIN : ~ In (UM_CID, fpos) (frames (um_Sc cx)).
Hypothesis HS1W : exists S1 W1 mem1 md1, AR SEGS B (um_lyc cx) S1 W1 mem1 md1 /\
  frames S1 = (UM_CID, fpos) :: frames (um_Sc cx) /\ ablocks B (um_lyc cx) S1 = ablocks B (um_lyc cx) (um_Sc cx).
#[local] Notation F := (um_F cx fpos).
#[local] Notation SH := (um_SH cx fpos).
#[local] Notation Eacc := (fun a => um_E cx a \/ aside_rng (um_lyc cx) UM_CID fpos a).
#[local] Notation AJ ly S W m md :=
  (ajournal_gx SEGS B (um_G cx) (um_XO cx) (um_OUT cx) (um_STK cx) (um_sp0 cx) (um_FP cx)
     (um_ly cx) (um_S cx) (um_W0 cx) (um_mem0 cx) (um_md0 cx) ((UM_CID, fpos) :: um_own cx) ly S W m md (um_k cx)).
#[local] Notation INV := (rk_inv SK B cx fpos).
#[local] Notation RKA := (SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W) (only parsing).

(* the alias buffer's bytes are side-frame bytes, outside the image *)
Lemma urd_F_side : forall a, F <= a < F + 512 -> aside_rng (um_lyc cx) UM_CID fpos a /\ ~ in_img SEGS a.
Proof.
  intros a Ha. destruct HS1W as (S1 & W1 & mem1 & md1 & HAR1 & Hfrs1 & _).
  assert (Hin : In (UM_CID, fpos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
  assert (Hs : aside_rng (um_lyc cx) UM_CID fpos a)
    by (apply (proj2 (rk_side_unfold SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W a)); left; exact Ha).
  split; [exact Hs|].
  exact (proj2 (aside_rng_low SK SEGS B LAWS pa_segs_low _ S1 W1 mem1 md1 UM_CID fpos a HAR1 Hin Hs)).
Qed.

(* ---- the marks block's bytes are read-set bytes of a callee called from inside the side frame ---- *)
Lemma urd_mk_akb : forall ly3 S3 W3 m3 md3 slo shi a,
  AJ ly3 S3 W3 m3 md3 -> INV ly3 S3 W3 m3 md3 ->
  um_sp cx - REAC_SERVED_UNMARK_ALL_AK <= slo -> shi <= um_sp cx ->
  um_mk cx <= a < um_mk cx + MK_SIZE -> akb SEGS B ly3 S3 slo shi a.
Proof.
  intros ly3 S3 W3 m3 md3 slo shi a HJ3 HI Hslo Hshi Ha.
  pose proof HI as (_ & Hfrs & _ & Hperm & Hfa & _ & _ & _ & _ & _ & _ & _ & Hm & _).
  pose proof HPRE as ((HJ & HGX & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hajw & _) & _).
  destruct (rk_mk SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W Hm) as (_ & M1 & _ & _ & M4 & _ & M6 & _ & _).
  pose proof (aj_stk_row_eq SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as (L1 & H1).
  pose proof (aj_stk_row_eq SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (L2 & H2).
  unfold apart_frame, REAC_SERVED_UNMARK_ALL_AK, REAC_SERVED_UNMARK_ALL_AFRAME, REAC_SERVED_UNMARK_ALL_ASLACK,
    AUN_ALIAS_READ_STK in M4, Hslo.
  change (spZ (um_regs cx)) with (um_sp cx) in M4.
  unfold amem_range, apart, MK_SIZE in *.
  apply (ajw_akb SK SEGS B LAWS (um_G cx) (um_XO cx) (um_OUT cx) (um_STK cx) (um_sp0 cx) (um_FP cx) (um_ly cx)
    (um_S cx) (um_W0 cx) (um_mem0 cx) (um_md0 cx) (um_own cx) (um_lyc cx) (um_Sc cx) (um_W cx) (um_memc cx)
    (um_mdc cx) (um_k cx) ly3 S3 slo shi a HGX HJ).
  - exact (rk_mk_ajw SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W a Hm Ha).
  - lia.
  - rk_consts. lia.
  - lia.
  - congruence.
  - congruence.
  - intros b mm Hb. exact (Permutation_in _ (Permutation_sym Hperm) Hb).
  - intros c0 q Hcq. rewrite Hfrs. right. exact Hcq.
  - exact Hfa.
Qed.

(* ---- the invariant after reac_link_alias_read: the callee's post composed with the invariant at the call ---- *)
Lemma urd_inv_call : forall ly3 S3 W3 m1 md1 (regs1 : bvmap 5 word) ly2 S2 W2 mem2 md2,
  INV ly3 S3 W3 m1 md1 ->
  AJ ly3 S3 W3 m1 md1 ->
  spZ regs1 = um_sp1 cx ->
  aarg regs1 1 = 0 -> aarg regs1 3 = F + 32 -> aarg regs1 4 = 256 ->
  AJ ly2 S2 W2 mem2 md2 -> frames S2 = frames S3 -> S2 = set_fs (st_fs S2) S3 ->
  Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) ->
  m_fds md2 = m_fds md1 -> m_fs md2 = m_fs md1 ->
  akept SEGS B ly3 S3 W3 m1 W2 mem2 (spZ regs1 - REAC_LINK_ALIAS_READ_AK) (spZ regs1)
    (fun a => inFP (reac_link_alias_read_awr regs1 (rdW W3 m1)) a) ->
  (forall a, inFP (reac_link_alias_read_awr regs1 (rdW W3 m1)) a -> ~ YC20.in_roP SEGS PCAP_RLO PCAP_RHI a) ->
  INV ly2 S2 W2 mem2 md2 /\
  (forall a, SH <= a < SH + 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) m1 a).
Proof.
  intros ly3 S3 W3 m1 md1 regs1 ly2 S2 W2 mem2 md2 HI HJ1 Hsp A1 A3 A4 HJ2 Hfr2 HS2 Hperm2 Hfds2 Hfs2 HK2 HNRO.
  pose proof HI as (_ & Hfrs & (fs3 & HfsS3) & Hperm & Hfa & Hra & Hsv & Hfl & HK & Hfds & Hfs' & Hro & Hm & Hs1 & Hs2 & Hmk).
  destruct (rk_win SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W) as (W16 & Wc & Wlo & Whi & W47 & S1lo & S1al & _).
  destruct (rk_F SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W) as (F1 & F2 & F3 & F4 & F5 & F6).
  unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in F5.
  destruct (rk_SH SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W) as (SH1 & SH2 & SH3 & SH4).
  pose proof (rk_F_app SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W) as FAPP.
  pose proof HK2 as (K1 & K2 & K3 & K4 & K5 & K6).
  rewrite Hsp in K1, HK2. rewrite REAC_LINK_ALIAS_READ_AK_val in K1, HK2.
  (* the callee's write set *)
  assert (HE : forall a, inFP (reac_link_alias_read_awr regs1 (rdW W3 m1)) a ->
    (LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4) \/ (F + 32 <= a < F + 288)).
  { intros a (r & Hr & Hrr). cbn [reac_link_alias_read_awr In] in Hr. destruct Hr as [<- | [<- | [<- | []]]].
    - left. exact Hrr.
    - exfalso. unfold aivl in Hrr. rewrite A1 in Hrr. cbn [fst snd Z.eqb] in Hrr. lia.
    - right. unfold aivl in Hrr. rewrite A3, A4 in Hrr.
      replace (F + 32 =? 0) with false in Hrr by (symmetry; apply Z.eqb_neq; lia). cbn [fst snd] in Hrr. lia. }
  assert (HEn : forall a, (alloc_ceiling <= a \/ (SH <= a < SH + 64) \/ (F + 504 <= a < F + 512)) ->
    ~ inFP (reac_link_alias_read_awr regs1 (rdW W3 m1)) a).
  { intros a Ha HEa. destruct (HE a HEa) as [H|H]; rk_consts; unfold LA_G_NL, NK_N_SENT in H; lia. }
  (* the bytes above s1 are kept *)
  assert (Hup : forall a, um_sp1 cx <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) m1 a).
  { intros a Ha. apply K1; [rk_consts; lia | lia | apply HEn; left; rk_consts; lia]. }
  (* the side frame's bytes and its shadow are kept but for the alias buffer *)
  assert (HinF3 : In (UM_CID, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  assert (HFk : forall a, F <= a < F + 512 -> ~ (F + 32 <= a < F + 288) ->
    aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) m1 a).
  { intros a Ha Hn. apply (K4 UM_CID fpos a HinF3).
    - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Hfa. change (fs_frame_bytes UM_CID) with 512.
      unfold um_F in Ha. exact Ha.
    - intros HEa. destruct (HE a HEa) as [H|H]; [|exact (Hn H)]. rk_consts. unfold LA_G_NL, NK_N_SENT in H. lia. }
  assert (HSk : forall a, SH <= a < SH + 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) m1 a).
  { intros a Ha. apply (K4 UM_CID fpos a HinF3).
    - right. unfold in_zr. cbn [fst snd]. rewrite Hfa. change (fs_frame_bytes UM_CID / 8) with 64.
      unfold um_SH in Ha. unfold shadow_addr. exact Ha.
    - apply HEn. right. left. exact Ha. }
  split; [|exact HSk].
  unfold rk_inv.
  split; [exact HJ2|].
  split; [rewrite Hfr2; exact Hfrs|].
  split; [exists (st_fs S2); rewrite HS2 at 1; rewrite HfsS3; reflexivity|].
  split; [exact (Permutation_trans Hperm2 Hperm)|].
  split.
  { intros c0 q. destruct (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c0 q HJ2) as (E2 & _).
    destruct (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c0 q HJ1) as (E3 & _).
    rewrite E2, <- E3. exact (Hfa c0 q). }
  split.
  { rewrite <- Hra. apply rk_rdword_eq. intros i Hi. apply Hup. lia. }
  split.
  { intros j Hj. rewrite <- (Hsv j Hj). apply rk_rdword_eq. intros i Hi. apply Hup. lia. }
  split.
  { rewrite <- Hfl. apply rk_rdword_eq. intros i Hi. unfold UM_FLAGPTR in *. apply HFk; lia. }
  split.
  { apply (akept_trans_ly SK SEGS B LAWS pa_segs_low (um_lyc cx) (um_Sc cx) (um_W cx) (um_memc cx) ly3 S3 W3 m1 W2 mem2
      (um_sp cx - REAC_SERVED_UNMARK_ALL_AK) (um_sp cx) (um_sp1 cx - 8592) (um_sp1 cx) Eacc
      (fun a => inFP (reac_link_alias_read_awr regs1 (rdW W3 m1)) a) Eacc).
    - unfold REAC_SERVED_UNMARK_ALL_AK, REAC_SERVED_UNMARK_ALL_AFRAME, REAC_SERVED_UNMARK_ALL_ASLACK,
        AUN_ALIAS_READ_STK. lia.
    - lia.
    - exact HK.
    - exact HK2.
    - unfold REAC_SERVED_UNMARK_ALL_AK, REAC_SERVED_UNMARK_ALL_AFRAME, REAC_SERVED_UNMARK_ALL_ASLACK,
        AUN_ALIAS_READ_STK. lia.
    - lia.
    - intros b mm Hb. exact (Permutation_in _ (Permutation_sym Hperm) Hb).
    - intros f Hf. rewrite Hfrs. right. exact Hf.
    - exact Hfa.
    - intros a Ha. exact Ha.
    - intros a HEa. destruct (HE a HEa) as [H|H].
      + left. unfold um_E, um_wr, reac_served_unmark_all_awr, inFP.
        exists (LA_G_NL, LA_G_NL + NK_N_SENT + 4). split; [left; reflexivity | exact H].
      + right. apply (proj2 (rk_side_unfold SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W a)). left. lia. }
  split; [rewrite Hfds2; exact Hfds|]. split; [rewrite Hfs2; exact Hfs'|].
  split.
  { intros a Hro_a Ho He.
    rewrite (K3 a (rk_ro_img SK B LAWS TB HSEGS RELRO_IMG a Hro_a) Ho He (fun HEa => HNRO a HEa Hro_a)).
    exact (Hro a Hro_a Ho He). }
  split; [exact Hm|].
  split.
  { rewrite <- Hs1. apply rk_rdword_eq. intros i Hi. unfold UM_SLOT_EMPTY. apply Hup. lia. }
  split.
  { rewrite <- Hs2. apply rk_rdword_eq. intros i Hi. unfold UM_SLOT_LIM. apply Hup. lia. }
  intros a Ha. rewrite <- (Hmk a Ha).
  eapply akept_akb_gx; [exact HJ1 | exact HK2 | |].
  - apply (urd_mk_akb ly3 S3 W3 m1 md1 (um_sp1 cx - 8592) (um_sp1 cx) a HJ1 HI); [| |exact Ha];
      unfold REAC_SERVED_UNMARK_ALL_AK, REAC_SERVED_UNMARK_ALL_AFRAME, REAC_SERVED_UNMARK_ALL_ASLACK,
        AUN_ALIAS_READ_STK; lia.
  - destruct (rk_mk SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W Hm) as (_ & M1 & _ & _ & _ & M5 & _ & _ & _).
    intros HEa. destruct (HE a HEa) as [H|H].
    + unfold apart_gnl, MK_SIZE in *. unfold NK_N_SENT, NK_SIZE in *. lia.
    + apply (rk_mk_not_side SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W a Hm Ha). apply (proj2 (rk_side_unfold SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W a)).
      left. lia.
Qed.

(* ---- reac_link_alias_read's apre at the call (+0x26c) ---- *)
Lemma urd_apre : forall ly3 S3 W3 m1 md1 (regs1 : bvmap 5 word),
  AJ ly3 S3 W3 m1 md1 -> INV ly3 S3 W3 m1 md1 ->
  aarg regs1 1 = 0 -> aarg regs1 3 = F + 32 -> aarg regs1 4 = 256 -> spZ regs1 = um_sp1 cx ->
  getr regs1 1 = Z_to_bv 64 (BASE + UM_RET_RD) ->
  getr regs1 3 = getr (um_regs cx) 3 -> getr regs1 4 = getr (um_regs cx) 4 ->
  apre SK SEGS PCAP_RLO PCAP_RHI B REAC_LINK_ALIAS_READ_AK 0 REAC_LINK_ALIAS_READ_ASIDE
    (reac_link_alias_read_awr regs1 (rdW W3 m1)) (um_G cx) (um_XO cx) (um_OUT cx) (um_STK cx) (um_sp0 cx)
    (um_FP cx) (um_ly cx) (um_S cx) (um_W0 cx) (um_mem0 cx) (um_md0 cx) ((UM_CID, fpos) :: um_own cx)
    ly3 S3 W3 m1 md1 (um_k cx) regs1.
Proof.
  intros ly3 S3 W3 m1 md1 regs1 HJ1 HI A1 A3 A4 Hsp Q1 Q3 Q4.
  pose proof HI as (_ & Hfrs & _ & Hperm & Hfa & _ & _ & _ & _ & _ & _ & Hro & _).
  pose proof HPRE as ((HJ & HGX & _ & _ & _ & Hgp & Htp & _ & _ & _ & Hnev & Hside & Hajw & Hnro) & _).
  destruct (rk_win SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W) as (W16 & Wc & Wlo & Whi & W47 & S1lo & S1al & S1al16).
  destruct (rk_F SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W) as (F1 & F2 & F3 & F4 & F5 & F6).
  pose proof pa_B_ok as PB.
  assert (Hrd : forall a, inFP (reac_link_alias_read_awr regs1 (rdW W3 m1)) a ->
    (LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4) \/ (F + 32 <= a < F + 288)).
  { intros a (r & Hr & Hrr). cbn [reac_link_alias_read_awr In] in Hr. destruct Hr as [<- | [<- | [<- | []]]].
    - left. exact Hrr.
    - exfalso. unfold aivl in Hrr. rewrite A1 in Hrr. cbn [fst snd Z.eqb] in Hrr. lia.
    - right. unfold aivl in Hrr. rewrite A3, A4 in Hrr.
      replace (F + 32 =? 0) with false in Hrr by (symmetry; apply Z.eqb_neq; lia). cbn [fst snd] in Hrr. lia. }
  assert (Hgnl : forall a, LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4 -> inFP (um_wr cx) a).
  { intros a Ha. exists (LA_G_NL, LA_G_NL + NK_N_SENT + 4). split; [left; reflexivity | exact Ha]. }
  split; [exact HJ1|]. split; [exact HGX|]. split; [exact Hro|].
  split; [rewrite Q1; unfold UM_RET_RD; apply ret_ok_codeptr_v; [unfold AF_reac_served_unmark_all; lia | reflexivity]|].
  split; [unfold raZ; rewrite Q1; unfold UM_RET_RD, AF_reac_served_unmark_all; rewrite unsigned_lit_small; lia|].
  split; [rewrite Q3; exact Hgp|]. split; [rewrite Q4; exact Htp|].
  rewrite Hsp, REAC_LINK_ALIAS_READ_AK_val.
  split; [exact S1al16|].
  split; [lia|]. split; [lia|]. split; [exact Hnev|].
  split.
  { apply (aside_room_push (um_Sc cx) S3 REAC_SERVED_UNMARK_ALL_ASIDE REAC_LINK_ALIAS_READ_ASIDE UM_CID fpos Hfrs Hside).
    intros c' d' Hin. unfold REAC_LINK_ALIAS_READ_ASIDE in Hin. cbn [In] in Hin.
    destruct Hin as [E | [E | []]]; injection E as <- <-.
    - exists 1. split; [unfold REAC_SERVED_UNMARK_ALL_ASIDE; cbn [In]; right; left; reflexivity | cbn; lia].
    - exists 1. split; [unfold REAC_SERVED_UNMARK_ALL_ASIDE; cbn [In]; right; right; left; reflexivity | cbn; lia]. }
  split.
  { intros a Ha. destruct (Hrd a Ha) as [H|H].
    - apply (ajw_mono B (um_G cx) (um_XO cx) (um_OUT cx) (um_STK cx) (um_sp0 cx) (um_FP cx) (um_ly cx) (um_S cx)
        (um_lyc cx) (um_Sc cx) (um_own cx) ly3 S3 ((UM_CID, fpos) :: um_own cx) a (Hajw a (Hgnl a H))).
      + intros b mm Hb. exact (Permutation_in _ (Permutation_sym Hperm) Hb).
      + intros x Hx. right. exact Hx.
      + exact Hfa.
    - apply (ajw_frame B (um_G cx) (um_XO cx) (um_OUT cx) (um_STK cx) (um_sp0 cx) (um_FP cx) (um_ly cx) (um_S cx)
        ly3 S3 ((UM_CID, fpos) :: um_own cx) UM_CID fpos a).
      + left. reflexivity.
      + rewrite Hfa. change (fs_frame_bytes UM_CID) with 512. unfold um_F in H. lia.
      + lia. }
  intros a Ha. destruct (Hrd a Ha) as [H|H].
  - exact (Hnro a (Hgnl a H)).
  - apply (not_ro_off_img SEGS PCAP_RLO PCAP_RHI a RELRO_IMG).
    exact (proj2 (urd_F_side a ltac:(lia))).
Qed.
(* ---- reac_link_alias_read's read set at the call: every byte is one its akept keeps ---- *)
Lemma urd_rd : forall c ly3 S3 W3 m1 md1 (regs1 : bvmap 5 word) kbs,
  Z.of_nat c < um_n cx ->
  AJ ly3 S3 W3 m1 md1 -> INV ly3 S3 W3 m1 md1 -> um_kinv cx (rdW W3 m1) kbs c ->
  aarg regs1 0 = um_mk cx + MK_NAME + MARK_LEN * Z.of_nat c -> spZ regs1 = um_sp1 cx ->
  forall a, reac_link_alias_read_ard SEGS regs1 (rdW W3 m1) a ->
    akb SEGS B ly3 S3 (spZ regs1 - REAC_LINK_ALIAS_READ_AK) (spZ regs1) a.
Proof.
  intros c ly3 S3 W3 m1 md1 regs1 kbs Hc HJ1 HI HKI A0 Hsp a Ha.
  pose proof HI as (_ & Hfrs & _ & Hperm & Hfa & _).
  pose proof HPRE as ((HJ & _) & _).
  destruct (rk_win SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W) as (W16 & Wc & Wlo & Whi & W47 & S1lo & S1al & _).
  pose proof (aj_stk_row_eq SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as (L1 & H1).
  pose proof (aj_stk_row_eq SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (L2 & H2).
  rewrite Hsp, REAC_LINK_ALIAS_READ_AK_val.
  destruct HKI as (NK1 & _ & IT1 & _).
  destruct Ha as [(Hn0 & s & HSa & Ha) | (bs & tab & i & n2 & ix & p & NKp & ITp & Hip & Pp & Cp & Ha)].
  - rewrite A0 in HSa, Ha.
    destruct (rk_name SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W c ly3 S3 W3 m1 md1 HI Hc)
      as (NM & NML & _ & NMin).
    pose proof (rk_acstr_unique SEGS _ _ _ _ HSa NM) as Es. subst s.
    apply (urd_mk_akb ly3 S3 W3 m1 md1 (um_sp1 cx - 8592) (um_sp1 cx) a HJ1 HI).
    + unfold REAC_SERVED_UNMARK_ALL_AK, REAC_SERVED_UNMARK_ALL_AFRAME, REAC_SERVED_UNMARK_ALL_ASLACK,
        AUN_ALIAS_READ_STK. lia.
    + lia.
    + unfold MK_NAME, MARK_LEN, MK_SIZE in *. lia.
  - assert (Ebs : bs = kbs) by exact (rk_anlk_unique SEGS _ _ _ _ NKp NK1). subst bs.
    assert (Etab : tab = um_tab cx) by exact (rk_aiftab_unique SEGS _ _ _ _ ITp IT1). subst tab.
    pose proof (rk_acstr_range SEGS _ _ _ Cp) as Rp.
    destruct (rk_tab_ptr SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W ly3 S3 W3 m1 md1 HI i n2 ix p Hip Pp
      ltac:(lia)) as (_ & _ & _ & _ & _ & _ & AKB).
    apply (akb_sub SEGS B (um_lyc cx) (um_Sc cx) ly3 S3 (um_sp cx - REAC_SERVED_UNMARK_ALL_AK) (um_sp cx)
      (um_sp1 cx - 8592) (um_sp1 cx) a (AKB a Ha)).
    + unfold REAC_SERVED_UNMARK_ALL_AK, REAC_SERVED_UNMARK_ALL_AFRAME, REAC_SERVED_UNMARK_ALL_ASLACK,
        AUN_ALIAS_READ_STK. lia.
    + lia.
    + congruence.
    + congruence.
    + intros b mm Hb. exact (Permutation_in _ (Permutation_sym Hperm) Hb).
    + intros c0 q Hcq. rewrite Hfrs. right. exact Hcq.
    + exact Hfa.
Qed.

(* ---- reac_link_alias_read_apre at the call: name c, no kind buffer, the alias buffer F + 32 of 256 bytes ---- *)
Lemma urd_pre : forall c ly3 S3 W3 m1 md1 (regs1 : bvmap 5 word) kbs,
  Z.of_nat c < um_n cx ->
  AJ ly3 S3 W3 m1 md1 -> INV ly3 S3 W3 m1 md1 -> um_kinv cx (rdW W3 m1) kbs c ->
  (forall i, 0 <= i < 32 -> aview SEGS (w_H W3) m1 (SH + 4 + i) = Some 0) ->
  aarg regs1 0 = um_mk cx + MK_NAME + MARK_LEN * Z.of_nat c -> aarg regs1 1 = 0 ->
  aarg regs1 3 = F + 32 -> aarg regs1 4 = 256 -> spZ regs1 = um_sp1 cx ->
  reac_link_alias_read_apre SEGS B regs1 (rdW W3 m1).
Proof.
  intros c ly3 S3 W3 m1 md1 regs1 kbs Hc HJ1 HI HKI HZ A0 A1 A3 A4 Hsp.
  pose proof HI as (_ & Hfrs & _ & Hperm & Hfa & _ & _ & _ & HK & _ & _ & _ & Hm & _).
  pose proof HPRE as ((HJ & HGX & _) & _ & (_ & _ & _ & N4 & N5 & _) & _).
  destruct (rk_win SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W) as (W16 & Wc & Wlo & Whi & W47 & S1lo & S1al & _).
  destruct (rk_F SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W) as (F1 & F2 & F3 & F4 & F5 & F6).
  unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in F5. unfold in_app, ASAN_CEIL in F4.
  destruct (rk_SH SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W) as (SH1 & SH2 & SH3 & SH4).
  destruct (rk_mk SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W Hm) as (M0 & M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
  destruct (rk_errno SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W) as (E1 & E2 & E3 & E4).
  destruct (rk_name SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W c ly3 S3 W3 m1 md1 HI Hc)
    as (NM & NML & _ & NMin).
  pose proof M8 as (MR & _). unfold MARKS_MAX in MR. unfold um_n in Hc.
  assert (HAR1 : AR SEGS B ly3 S3 W3 m1 md1) by (destruct HJ1 as (_ & _ & (memS & HJi & _) & _); exact (proj1 HJi)).
  assert (HinF3 : In (UM_CID, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  destruct (rk_frame_present SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W ly3 S3 W3 m1 md1 HAR1 HinF3
    (Hfa UM_CID fpos)) as (HFp & HSp).
  destruct HKI as (NK1 & WF1 & IT1 & _ & _ & _ & _ & OP1 & _ & OC1 & OB1).
  pose proof (aj_stk_row_eq SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as (L1 & H1).
  pose proof (aj_stk_row_eq SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (L2 & H2).
  assert (HB : forall b mm, In (b, mm) (ablocks B (um_lyc cx) (um_Sc cx)) -> In (b, mm) (ablocks B ly3 S3))
    by (intros b mm Hb; exact (Permutation_in _ (Permutation_sym Hperm) Hb)).
  assert (HFRi : forall c' q, In (c', q) (frames (um_Sc cx)) -> In (c', q) (frames S3))
    by (intros c' q Hq; rewrite Hfrs; right; exact Hq).
  pose proof (rk_errno_val SK B LAWS TB HSEGS RELRO_IMG) as Eerr.
  pose proof (rk_pre_ar SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W) as HAR0.
  pose proof (rk_fmiss SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W) as HFM.
  unfold apart_frame, REAC_SERVED_UNMARK_ALL_AK, REAC_SERVED_UNMARK_ALL_AFRAME, REAC_SERVED_UNMARK_ALL_ASLACK,
    AUN_ALIAS_READ_STK in M4, E2.
  change (spZ (um_regs cx)) with (um_sp cx) in M4, E2.
  (* a table pointer read at the call is the call's, or far from every byte the clauses name *)
  assert (HTP : forall i n2 ix p, nth_error (um_tab cx) i = Some (n2, ix) ->
     au64_at SEGS (rdW W3 m1) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
     exists p', p mod 2 ^ 64 = p' /\ astr_rt_ok SEGS (um_regs cx) REAC_SERVED_UNMARK_ALL_AK (um_m0 cx) p' n2 /\
       apart_gnl LA_G_NL p' (Z.of_nat (length n2) + 1) /\ apart (as_errno B) 4 p' (Z.of_nat (length n2) + 1) /\
       (forall x, p' <= x <= p' + Z.of_nat (length n2) ->
          akb SEGS B (um_lyc cx) (um_Sc cx) (um_sp cx - REAC_SERVED_UNMARK_ALL_AK) (um_sp cx) x) /\
       0 <= p' < 2 ^ 64 /\ au64_at SEGS (um_m0 cx) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p').
  { intros i n2 ix p Hi Hp.
    pose proof IT1 as (_ & _ & IT1').
    destruct (IT1' i n2 ix Hi) as (_ & p' & P' & _ & C' & _).
    pose proof (rk_acstr_range SEGS _ _ _ C') as Rp'.
    destruct (rk_tab_ptr SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W ly3 S3 W3 m1 md1 HI i n2 ix p' Hi P'
      ltac:(lia)) as (PM & _ & RT & AG & AE & _ & AKB).
    exists p'. split; [|split; [exact RT | split; [exact AG | split; [exact AE | split; [exact AKB | split; [lia | exact PM]]]]]].
    pose proof (rk_au64_unique SEGS _ _ _ _ Hp P') as Ep. rewrite (Z.mod_small p') in Ep by lia. exact Ep. }
  exists kbs, (um_tab cx), (Some (nth c (um_names cx) [])).
  split; [exact NK1|]. split; [exact WF1|]. split; [exact OP1|].
  split; [unfold MARKS_MAX in N4; lia|]. split; [unfold MARKS_MAX in N5; lia|].
  split; [exact IT1|].
  split; [exact (proj1 (zsh_gnl_ard B TB SEGS ly3 S3 W3 m1 md1 HAR1))|].
  split; [exact (proj2 (zsh_gnl_ard B TB SEGS ly3 S3 W3 m1 md1 HAR1))|].
  split.
  { split; [exact E1|].
    split; [intros i Hi; apply (rk_errno_writable SK B LAWS TB HSEGS RELRO_IMG); lia|].
    split; [exact (proj1 (zsh_errno_ard B TB SEGS ly3 S3 W3 m1 md1 HAR1))|].
    split; [|exact E3].
    unfold apart_frame. rewrite Hsp, REAC_LINK_ALIAS_READ_AK_val. lia. }
  split; [split; [rewrite A0; unfold MK_NAME, MARK_LEN; lia | rewrite A0; exact NM]|].
  split; [intros H; rewrite A1 in H; contradiction|].
  split.
  { intros _ _. rewrite A3, A4. apply urd_abuf_present; [lia | rk_consts; lia | lia |].
    intros x Hx. apply HFp. unfold UM_FB. lia. }
  split.
  { intros i n2 ix p Hi Hp.
    destruct (HTP i n2 ix p Hi Hp) as (p' & Ep & RT & AG & AE & AKB & Rp' & PM).
    destruct RT as (P0 & PL & AMR & RA & HV & _ & AF).
    unfold apart_frame, REAC_SERVED_UNMARK_ALL_AK, REAC_SERVED_UNMARK_ALL_AFRAME, REAC_SERVED_UNMARK_ALL_ASLACK,
      AUN_ALIAS_READ_STK in AF.
    change (spZ (um_regs cx)) with (um_sp cx) in AF.
    unfold amem_range in AMR. unfold apart_gnl, apart in AG, AE.
    rewrite Eerr in AE |- *.
    assert (Hpp : p = p' \/ 2 ^ 64 <= p \/ p + Z.of_nat (length n2) + 1 <= 0) by (rk_consts; lia).
    split; [unfold apart_frame; rewrite Hsp, REAC_LINK_ALIAS_READ_AK_val; destruct Hpp as [->|[Hp1|Hp1]]; lia|].
    split; [unfold apart_gnl; destruct Hpp as [->|[Hp1|Hp1]]; [exact AG | unfold LA_G_NL, NK_SIZE; lia | unfold LA_G_NL, NK_SIZE; lia]|].
    split; [unfold apart; destruct Hpp as [->|[Hp1|Hp1]]; unfold TFIB_ERRNO in *; lia|].
    split; [intros H; rewrite A1 in H; contradiction|].
    split.
    { intros _ _. rewrite A3, A4. destruct Hpp as [->|[Hp1|Hp1]]; [|unfold apart; lia|unfold apart; lia].
      apply rk_apart_of_pts; [lia | lia |]. intros x Hx Hf.
      apply (akb_not_side SK SEGS B pa_img_range (um_G cx) (um_XO cx) (um_OUT cx) (um_STK cx) (um_sp0 cx)
        (um_FP cx) (um_ly cx) (um_S cx) (um_W0 cx) (um_mem0 cx) (um_md0 cx) (um_own cx) (um_lyc cx) (um_Sc cx)
        (um_W cx) (um_memc cx) (um_mdc cx) (um_k cx) (um_sp cx - REAC_SERVED_UNMARK_ALL_AK) (um_sp cx) UM_CID fpos x
        HJ ltac:(unfold UM_CID; lia) F6 HNIN (AKB x ltac:(lia))).
      exact (proj1 (urd_F_side x ltac:(lia))). }
    intros Hrng. destruct Hpp as [->|[Hp1|Hp1]]; [|lia|lia].
    split; [exact P0|]. split; [lia|].
    split.
    { split; [unfold amem_range; lia|].
      destruct (shadow_transport_akb SEGS B LAWS TB pa_img_range (um_lyc cx) (um_Sc cx) (um_W cx) (um_memc cx)
        (um_mdc cx) ly3 S3 W3 m1 md1 (um_sp cx - REAC_SERVED_UNMARK_ALL_AK) (um_sp cx)
        (fun a => um_E cx a \/ aside_rng (um_lyc cx) UM_CID fpos a) p' (Z.of_nat (length n2) + 1)
        HAR0 HAR1 ltac:(congruence) ltac:(congruence) HB HK HFM ltac:(lia)
        ltac:(intros x Hx; apply AKB; lia) RA HV) as (RA1 & HV1).
      exact (conj RA1 HV1). }
    (* the strcmp tail: TailVis.v from the table's astr_rt_ok at the call *)
    intros a Ha.
    exact (utv_tab SK B LAWS HSEGS cx HPRE ly3 S3 W3 m1 md1 _ HAR1 HB HFRi Hfa HK i n2 ix p' Hi PM Hrng a Ha). }
  split.
  { intros s Es. injection Es as <-. split; [intros H; rewrite A1 in H; contradiction|].
    intros _ _. rewrite A0, A3, A4. apply rk_apart_of_pts; [lia | lia |].
    intros x Hx Hf. apply (rk_mk_not_side SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W x Hm ltac:(unfold MK_NAME, MARK_LEN, MK_SIZE in *; lia)).
    exact (proj1 (urd_F_side x ltac:(lia))). }
  split; [intros H; rewrite A1 in H; contradiction|].
  split; [intros H; rewrite A1 in H; contradiction|].
  split; [intros _; rewrite A3, A4, Eerr; unfold apart, TFIB_ERRNO; lia|].
  split.
  { intros s Es. injection Es as <-.
    split; [unfold apart_frame; rewrite A0, Hsp, REAC_LINK_ALIAS_READ_AK_val; unfold MK_NAME, MARK_LEN, MK_SIZE in *; lia|].
    split; [rewrite A0; unfold apart_gnl in *; unfold MK_NAME, MARK_LEN, MK_SIZE in *; lia|].
    split; [lia|].
    rewrite A0.
    split.
    { split; [unfold amem_range in *; unfold MK_NAME, MARK_LEN, MK_SIZE in *; lia|].
      destruct (shadow_transport SEGS B LAWS TB pa_img_range (um_lyc cx) (um_Sc cx) (um_W cx) (um_memc cx) (um_mdc cx)
        ly3 S3 W3 m1 md1 (um_sp cx - REAC_SERVED_UNMARK_ALL_AK) (um_sp cx)
        (fun a => um_E cx a \/ aside_rng (um_lyc cx) UM_CID fpos a) (um_mk cx) MK_SIZE
        HAR0 HAR1 ltac:(congruence) ltac:(congruence) HB HK HFM ltac:(unfold MK_SIZE; lia)
        ltac:(intros x Hx; apply (sclass_of_ajw SK SEGS B LAWS (um_G cx) (um_XO cx) (um_OUT cx) (um_STK cx)
           (um_sp0 cx) (um_FP cx) (um_ly cx) (um_S cx) (um_W0 cx) (um_mem0 cx) (um_md0 cx) (um_own cx) (um_lyc cx)
           (um_Sc cx) (um_W cx) (um_memc cx) (um_mdc cx) (um_k cx) x HGX HJ (rk_mk_ajw SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W x Hm Hx));
           unfold amem_range, MK_SIZE in *; rk_consts; lia)
        M2 M3) as (RA1 & HV1).
      split.
      - apply (rk_ra_sub _ (um_mk cx) MK_SIZE); [exact RA1 | |]; unfold MK_NAME, MARK_LEN, MK_SIZE in *; lia.
      - apply (rk_hull_sub _ (um_mk cx) MK_SIZE); [exact HV1 | | |]; unfold MK_NAME, MARK_LEN, MK_SIZE in *; lia. }
    (* the strcmp tail: TailVis.v from the marks block at the call *)
    intros a Ha.
    exact (utv_name SK B LAWS HSEGS cx HPRE ly3 S3 W3 m1 md1 _ HAR1 HB HFRi Hfa HK c Hm ltac:(unfold um_n; lia) a Ha). }
  split; [intros H; rewrite A1 in H; contradiction|].
  split.
  { intros _. rewrite A3. unfold apart_frame, apart_gnl. rewrite Hsp, REAC_LINK_ALIAS_READ_AK_val.
    split; rk_consts; unfold LA_G_NL, NK_SIZE; lia. }
  split; [intros H; rewrite A1 in H; contradiction|].
  intros _ _. rewrite A3, A4.
  split; [unfold amem_range; rk_consts; lia|].
  split.
  { intros x Hx. unfold shadow_of_addr. exists 0. split; [|left; reflexivity].
    pose proof (HZ (x / 8 - um_F cx fpos / 8 - 4) ltac:(lia)) as Hz.
    replace (um_SH cx fpos + 4 + (x / 8 - um_F cx fpos / 8 - 4)) with (SHADOW_OFF + x / 8) in Hz by (rewrite SH1; ring).
    exact Hz. }
  intros s Hs. change (aview SEGS (w_H W3) m1 s <> None).
  apply (rk_aview_present SEGS). apply HSp. unfold UM_SHN. rewrite SH1.
  unfold shadow_addr, SHADOW_OFF in *. lia.
Qed.

(* ---- the model step of round c from reac_link_alias_read's Post (link_spec.v unmark_walk's first two tests) ---- *)
Lemma urd_post : forall c (m1 m2 : word -> option byte) kbs (regs1 regs2 : bvmap 5 word),
  Z.of_nat c < um_n cx -> um_kinv cx m1 kbs c ->
  acstr_at SEGS m1 (aarg regs1 0) (nth c (um_names cx) []) -> aarg regs1 0 <> 0 ->
  aarg regs1 2 = 0 -> aarg regs1 3 = F + 32 -> aarg regs1 4 = 256 ->
  reac_link_alias_read_apost SEGS regs1 m1 regs2 m2 ->
  exists kbs' al,
    acstr_at SEGS m2 (F + 32) al /\
    (getr regs2 10 <> w64 0 -> um_kinv cx m2 kbs' (S c)) /\
    (getr regs2 10 = w64 0 -> bl_eqb al S_SERVED = false -> um_kinv cx m2 kbs' (S c)) /\
    (getr regs2 10 = w64 0 -> bl_eqb al S_SERVED = true -> um_kinv_mid cx m2 kbs' c).
Proof.
  intros c m1 m2 kbs regs1 regs2 Hc HKI NM Hn0 A2 A3 A4 HPS.
  destruct (rk_F SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE HNIN HS1W) as (F1 & _).
  pose proof HKI as (NK & WF & IT & CH & EE & NI & UW & OP & MS & OC & OB).
  assert (Hlen : (c < length (um_names cx))%nat).
  { unfold um_names, mk_names. rewrite length_map, length_seq. unfold um_n in Hc. lia. }
  pose proof (nth_error_nth' (um_names cx) [] Hlen) as Hn.
  destruct (HPS kbs (um_tab cx) (Some (nth c (um_names cx) [])) NK IT (conj Hn0 NM))
    as (Hrc & (kbs' & NK' & WF' & CH' & EE' & NI' & IT' & NX' & SO' & SE' & SN' & NS' & OP' & MS' & OC' & OB' & _)
        & _ & AL & _).
  rewrite A2, A4 in Hrc, NX', SO', SE', SN', NS', AL. rewrite A3 in AL.
  set (R := read_lib (um_tab cx) (Some (nth c (um_names cx) [])) 0 256 (nk_sent kbs) (nk_kstate kbs)) in *.
  assert (HRe : R = read_core (um_tab cx) (Some (nth c (um_names cx) [])) 0 ALIAS_MAX (nk_sent kbs) (nk_kstate kbs))
    by reflexivity.
  assert (KS : nk_kstate kbs' = r_state R).
  { destruct (rk_read_state_ce (um_tab cx) (Some (nth c (um_names cx) [])) 0 ALIAS_MAX (nk_sent kbs) (nk_kstate kbs))
      as [C1 E1']. rewrite <- HRe in C1, E1'.
    apply rk_nk_kstate_eq; [rewrite CH', C1; reflexivity | exact NX' | rewrite EE', E1'; reflexivity
                           | exact SO' | exact SE']. }
  assert (RR : - 2 ^ 32 < r_rc R < 2 ^ 32).
  { rewrite HRe. pose proof WF as (_ & _ & _ & _ & _ & _ & _ & _ & We & Wso & Wse & _).
    apply rk_read_rc_range; unfold nk_kstate; cbn [k_sock k_send k_end]; lia. }
  rewrite (rk_skipn_nth (um_names cx) c _ Hn) in UW. cbn [unmark_walk] in UW. rewrite <- HRe in UW.
  assert (Hrc0 : getr regs2 10 = w64 0 -> r_rc R = 0).
  { intros H0. rewrite Hrc in H0. exact (rk_w64_small_zero _ RR H0). }
  assert (Hrcn : getr regs2 10 <> w64 0 -> r_rc R <> 0).
  { intros H0 E. apply H0. rewrite Hrc, E. reflexivity. }
  assert (KI : unmark_walk (um_tab cx) (skipn (S c) (um_names cx)) (r_reqs R) (r_state R) = um_U cx ->
    um_kinv cx m2 kbs' (S c)).
  { intros UW2. split; [exact NK'|]. split; [exact WF'|]. split; [exact IT'|].
    split; [rewrite CH'; exact CH|]. split; [rewrite EE'; exact EE|]. split; [rewrite NI'; exact NI|].
    split; [rewrite SN', KS; exact UW2|].
    split; [exact OP'|]. split; [rewrite MS'; exact MS|]. split; [lia|]. lia. }
  exists kbs', (r_alias R).
  split; [apply AL; lia|].
  split.
  { intros H0. apply KI. rewrite (proj2 (Z.eqb_neq _ 0) (Hrcn H0)) in UW. cbn [negb] in UW. exact UW. }
  split.
  { intros H0 Hb. apply KI. rewrite (proj2 (Z.eqb_eq _ 0) (Hrc0 H0)), Hb in UW. cbn [negb] in UW. exact UW. }
  intros H0 Hb. rewrite (proj2 (Z.eqb_eq _ 0) (Hrc0 H0)), Hb in UW. cbn [negb] in UW.
  split; [exact NK'|]. split; [exact WF'|]. split; [exact IT'|].
  split; [rewrite CH'; exact CH|]. split; [rewrite EE'; exact EE|]. split; [rewrite NI'; exact NI|].
  split; [rewrite SN', KS; exact UW|].
  split; [exact OP'|]. split; [rewrite MS'; exact MS|]. split; [lia|]. lia.
Qed.
End c.

(* ==========================================================================
   THE STAGE: HEAD c -> the call of reac_link_alias_read -> its return at +0x270
   ========================================================================== *)
Theorem um_read_a : forall c, um_from SK B (fun cx => um_gi_rd cx c) -> um_head_obl SK B c.
Proof.
intros c HRB cx fpos ly3 S3 W3 ms3 md3 HPRE HGI.
destruct HGI as (Hpc & HLOOP & (kbs & HKI) & HBASE).
pose proof HBASE as HBASE0. pose proof HLOOP as HLOOP0.
destruct HBASE as (Zrsv & Zsvc & Zrom & Zfrg & Zfcsr & HJ3 & Hfrs3 & Hnin & HfsS3 & Hperm & HS1W & Hfa3
  & R2 & R9 & R8 & R18 & R19 & R25 & R20 & R3 & R4 & _ & _ & _ & HFpres & HSpres & _ & Hfds3 & Hfs3 & _).
destruct HLOOP as (Hm & Hc & R21 & R22 & R23 & R24 & R26 & R27 & _ & _ & _).
pose proof (rk_inv_of_base SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W c ly3 S3 W3 ms3 md3 HBASE0 HLOOP0)
  as HINV3.
destruct (rk_win SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W)
  as (W16 & Wc & Wlo & Whi & W47 & S1lo & S1al & S1al16).
destruct (rk_F SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W) as (F1 & F2 & F3 & F4 & F5 & F6).
destruct (rk_SH SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W) as (SH1 & SH2 & SH3 & SH4).
destruct (rk_mk SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W Hm) as (M0 & M1 & _ & _ & _ & _ & _ & _ & M8).
pose proof M8 as (MR & _). unfold MARKS_MAX in MR.
pose proof HPRE as ((HJ & HGX & _) & _).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
(* ---- the environment: the registers at the cut ---- *)
set (E := Eimg (Ereg (ms_regs ms3) [])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall n (r : Prelude.reg), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
{ intros n r Hr. subst E. rewrite Eimg_low; [exact (ew_Ereg_nat _ _ n r Hr)|].
  pose proof (u5_range r) as Hu. unfold A_TEXT. lia. }
assert (U18 : bv_unsigned (ew E 18) = um_SH cx fpos).
{ rewrite (EREG 18%nat 18%bv eq_refl), R18. unfold w64. apply unsigned_lit_small.
  unfold SHADOW_OFF, kHighMemBeg in *. lia. }
(* ---- the symbolic state at the cut ---- *)
assert (HS : st_ok_pi SEGS VAL E urd_ss0 (restrict (w_H W3) ms3)).
{ rewrite (urd_ms_eta ms3 Zfrg Zsvc Zrsv Zfcsr), Hpc, Zrom, restrict_mkst_fx.
  unfold urd_ss0, w64. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, urd_SHR.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U18.
    split; [unfold SHADOW_OFF, kHighMemBeg in *; lia|]. split; [unfold SHADOW_OFF, kHighMemBeg in *; lia|].
    split; [|apply Forall_nil].
    intros o Ho. apply (YCbq.apresent_writable SEGS). apply HSpres. unfold UM_SHN. lia.
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - split; [|split; [exact I | exact I]]. cbn [urd_facts f_atoms atoms_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite U18. change (2 ^ 3) with 8.
    unfold SHADOW_OFF, kHighMemBeg, kLowMemEnd in *. repeat split; lia. }
clearbody E.
(* ---- the run +0x1d8 .. +0x26c: the 32 shadow stores, the arguments, up to reac_link_alias_read ---- *)
pose proof (paj_run_call_plain_x SK B LAWS (um_G cx) HGX (um_XO cx) (um_OUT cx)) as RUNC.
urd_run_call RUNC HS HJ3.
{ intros a (r & Hr & Ha). cbn [In ss_mem urd_ss0] in Hr. destruct Hr as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val urd_SHR] in Ha. rewrite U18 in Ha. left.
  apply (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ UM_CID fpos a HJ3
    ltac:(left; reflexivity)).
  right. unfold in_zr. cbn [fst snd]. rewrite Hfa3. change (fs_frame_bytes UM_CID / 8) with 64.
  unfold um_SH, um_F in Ha. unfold shadow_addr. lia. }
intros ms1 mat1 HS1 HJ1 HFr1 HFr1' HG1.
set (md1 := with_vm_backing (m_vm_lazy md3) mat1 md3) in *.
destruct (urd_wvb_fds_fs (m_vm_lazy md3) mat1 md3) as (Efds1 & Efs1).
(* what the run changed: F's shadow bytes s2 + 4 .. s2 + 0x23 *)
assert (UN1 : forall a, 0 <= a < 2 ^ 64 -> ~ (um_SH cx fpos + 4 <= a < um_SH cx fpos + 36) ->
  aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha Hn. apply (YCbq.aview_eq_of SEGS). apply HFr1'.
  rewrite unsigned_lit_small by lia.
  intros (r & Hr & Hra). cbn [In ss_mem urd_ss0] in Hr. destruct Hr as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val urd_SHR] in Hra. rewrite U18 in Hra. apply Hn. lia. }
assert (HX1 : forall a, um_SH cx fpos + 4 <= a < um_SH cx fpos + 36 ->
  (um_sp cx - REAC_SERVED_UNMARK_ALL_AK <= a < um_sp1 cx) \/ (um_SH cx fpos <= a < um_SH cx fpos + 64))
  by (intros a Ha; right; lia).
assert (HINV1 : rk_inv SK B cx fpos ly3 S3 W3 (ms_mem ms1) md1).
{ apply (rk_step SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W ly3 S3 W3 (ms_mem ms3) md3 (ms_mem ms1) md1
    (fun a => um_SH cx fpos + 4 <= a < um_SH cx fpos + 36) HINV3 HJ1 UN1 HX1).
  - intros a Hp. exact (urd_apresent_grows (w_H W3) (ms_mem ms3) (ms_mem ms1) a HG1 Hp).
  - exact Efds1.
  - exact Efs1. }
pose proof (rk_kinv_step SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W ly3 S3 W3 (ms_mem ms3) md3 (ms_mem ms1)
  (fun a => um_SH cx fpos + 4 <= a < um_SH cx fpos + 36) kbs c HINV3 UN1 HX1 HKI) as HKI1.
(* the shadow bytes the run stored *)
lazymatch type of HS1 with st_ok _ _ ?ssx _ =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) urd_SHR) in
  pose proof (st_ok_region_nth E ssx _ 0 r0 HS1 ltac:(vm_compute; reflexivity)) as HR0 end.
cbn [ms_mem restrict] in HR0.
assert (HZ1 : forall i, 0 <= i < 32 -> aview SEGS (w_H W3) (ms_mem ms1) (um_SH cx fpos + 4 + i) = Some 0).
{ intros i Hi. unfold aview. replace (um_SH cx fpos + 4 + i) with (um_SH cx fpos + (4 + i)) by ring.
  erewrite (urd_zero_byte SEGS E _ 18 _ _ _ _ _ _ (4 + i) HR0 U18); [reflexivity|].
  apply urd_z1b_in.
  lazymatch goal with |- existsb _ ?cs = true =>
    assert (HB : forallb (fun k : nat => existsb (urd_z1b (Z.of_nat k)) cs) (seq 4 32) = true)
      by (vm_compute; reflexivity);
    rewrite forallb_forall in HB; specialize (HB (Z.to_nat (4 + i)) ltac:(apply in_seq; lia));
    rewrite Z2Nat.id in HB by lia; exact HB end. }
(* ---- the registers at the call ---- *)
prreg HS1 (10%bv : bv 5) Q10. prreg HS1 (11%bv : bv 5) Q11. prreg HS1 (12%bv : bv 5) Q12.
prreg HS1 (13%bv : bv 5) Q13. prreg HS1 (14%bv : bv 5) Q14. prreg HS1 (1%bv : bv 5) Q1.
prreg HS1 (2%bv : bv 5) Q2. prreg HS1 (3%bv : bv 5) Q3. prreg HS1 (4%bv : bv 5) Q4.
prreg HS1 (8%bv : bv 5) Q8. prreg HS1 (9%bv : bv 5) Q9. prreg HS1 (18%bv : bv 5) Q18.
prreg HS1 (19%bv : bv 5) Q19. prreg HS1 (20%bv : bv 5) Q20. prreg HS1 (21%bv : bv 5) Q21.
prreg HS1 (22%bv : bv 5) Q22. prreg HS1 (23%bv : bv 5) Q23. prreg HS1 (24%bv : bv 5) Q24.
prreg HS1 (25%bv : bv 5) Q25. prreg HS1 (26%bv : bv 5) Q26. prreg HS1 (27%bv : bv 5) Q27.
rewrite (EREG 22%nat 22%bv eq_refl) in Q10, Q22. rewrite (EREG 21%nat 21%bv eq_refl) in Q13, Q21.
rewrite (EREG 2%nat 2%bv eq_refl) in Q2. rewrite (EREG 3%nat 3%bv eq_refl) in Q3.
rewrite (EREG 4%nat 4%bv eq_refl) in Q4. rewrite (EREG 8%nat 8%bv eq_refl) in Q8.
rewrite (EREG 9%nat 9%bv eq_refl) in Q9. rewrite (EREG 18%nat 18%bv eq_refl) in Q18.
rewrite (EREG 19%nat 19%bv eq_refl) in Q19. rewrite (EREG 20%nat 20%bv eq_refl) in Q20.
rewrite (EREG 23%nat 23%bv eq_refl) in Q23. rewrite (EREG 24%nat 24%bv eq_refl) in Q24.
rewrite (EREG 25%nat 25%bv eq_refl) in Q25. rewrite (EREG 26%nat 26%bv eq_refl) in Q26.
rewrite (EREG 27%nat 27%bv eq_refl) in Q27.
assert (Hc32 : Z.of_nat c < 32) by (unfold um_n in Hc; lia).
assert (A0 : aarg (ms_regs ms1) 0 = um_mk cx + MK_NAME + MARK_LEN * Z.of_nat c).
{ unfold aarg, argZ. apply urd_bvu; [exact (eq_trans Q10 R22)|].
  unfold amem_range, MK_SIZE, MK_NAME, MARK_LEN, kHighMemEnd, kLowMemEnd in *. lia. }
assert (A1 : aarg (ms_regs ms1) 1 = 0) by (unfold aarg, argZ; apply urd_bvu; [exact Q11 | lia]).
assert (A2 : aarg (ms_regs ms1) 2 = 0) by (unfold aarg, argZ; apply urd_bvu; [exact Q12 | lia]).
assert (A3 : aarg (ms_regs ms1) 3 = um_F cx fpos + 32).
{ unfold aarg, argZ. apply urd_bvu; [exact (eq_trans Q13 R21) | lia]. }
assert (A4 : aarg (ms_regs ms1) 4 = 256) by (unfold aarg, argZ; apply urd_bvu; [exact Q14 | lia]).
assert (Hsp1 : spZ (ms_regs ms1) = um_sp1 cx) by (unfold spZ; apply urd_bvu; [exact (eq_trans Q2 R2) | lia]).
assert (Q1' : getr (ms_regs ms1) 1 = Z_to_bv 64 (BASE + UM_RET_RD)) by exact Q1.
assert (Q3' : getr (ms_regs ms1) 3 = getr (um_regs cx) 3) by exact (eq_trans Q3 R3).
assert (Q4' : getr (ms_regs ms1) 4 = getr (um_regs cx) 4) by exact (eq_trans Q4 R4).
pose proof (urd_apre cx fpos HPRE Hnin HS1W ly3 S3 W3 (ms_mem ms1) md1 (ms_regs ms1)
  HJ1 HINV1 A1 A3 A4 Hsp1 Q1' Q3' Q4') as HAP.
pose proof HAP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNRO).
pmkst HS1.
replace (Z_to_bv 64 (pa_sigma LS_reac_link_alias_read)) with (w64 REAC_LINK_ALIAS_READ_A)
  by (rewrite (lv_sigma LV); reflexivity).
(* ---- reac_link_alias_read ---- *)
eapply SRr_bind.
{ apply (HRD (um_G cx) (um_XO cx) (um_OUT cx) (um_STK cx) (um_sp0 cx) (um_FP cx) (um_ly cx) (um_S cx) (um_W0 cx)
    (um_mem0 cx) (um_md0 cx) ((UM_CID, fpos) :: um_own cx) ly3 S3 W3 (ms_mem ms1) md1 (um_k cx) (ms_regs ms1)).
  - exact HAP.
  - exact (urd_rd cx fpos HPRE Hnin HS1W c ly3 S3 W3 (ms_mem ms1) md1
      (ms_regs ms1) kbs Hc HJ1 HINV1 HKI1 A0 Hsp1).
  - exact (urd_pre cx fpos HPRE Hnin HS1W c ly3 S3 W3 (ms_mem ms1) md1
      (ms_regs ms1) kbs Hc HJ1 HINV1 HKI1 HZ1 A0 A1 A3 A4 Hsp1). }
cbv beta. intros W2 c2 HWle HPOST.
destruct HPOST as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hfr2 & Hfds2 & Hfs2 & HK2 & _
  & HS2 & Hperm2 & HPST).
rewrite Z.add_0_r in HJ2.
destruct (urd_inv_call cx fpos HPRE Hnin HS1W ly3 S3 W3 (ms_mem ms1) md1
  (ms_regs ms1) ly2 S2 W2 mem2 md2 HINV1 HJ1 Hsp1 A1 A3 A4 HJ2 Hfr2 HS2 Hperm2 Hfds2 Hfs2 HK2 HNRO) as (HINV2 & HSK2).
destruct (rk_name SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W c ly3 S3 W3 (ms_mem ms1) md1 HINV1 Hc)
  as (NM1 & _).
rewrite <- A0 in NM1.
destruct (urd_post cx fpos HPRE Hnin HS1W c (rdW W3 (ms_mem ms1)) (rdW W2 mem2)
  kbs (ms_regs ms1) regs2 Hc HKI1 NM1 ltac:(rewrite A0; unfold MK_NAME, MARK_LEN; lia) A2 A3 A4 HPST)
  as (kbs' & al & AL & K1 & K2 & K3).
(* the callee-saved registers after the call *)
assert (HPR : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms1) (Z_to_bv 5 r)) by exact HP2.
apply (HRB cx fpos ly2 S2 W2 (mkst regs2 (getr (ms_regs ms1) 1) mem2 (seg_rom SEGS)) md2 HPRE).
unfold um_gi_rd. cbn [ms_pc_val ms_regs ms_mem mkst].
split; [exact Q1'|].
split.
{ apply (rk_loop_of_inv SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W c ly2 S2 W2
    (mkst regs2 (getr (ms_regs ms1) 1) mem2 (seg_rom SEGS)) md2 Hc); cbn [ms_regs ms_mem mkst];
  [ exact (eq_trans (HPR 21 ltac:(unfold acallee_saved; lia)) (eq_trans Q21 R21))
  | exact (eq_trans (HPR 22 ltac:(unfold acallee_saved; lia)) (eq_trans Q22 R22))
  | exact (eq_trans (HPR 23 ltac:(unfold acallee_saved; lia)) (eq_trans Q23 R23))
  | exact (eq_trans (HPR 24 ltac:(unfold acallee_saved; lia)) (eq_trans Q24 R24))
  | exact (eq_trans (HPR 26 ltac:(unfold acallee_saved; lia)) (eq_trans Q26 R26))
  | exact (eq_trans (HPR 27 ltac:(unfold acallee_saved; lia)) (eq_trans Q27 R27))
  | exact HINV2 ]. }
split.
{ apply (rk_base_of_inv SK B LAWS TB HSEGS RELRO_IMG cx fpos HPRE Hnin HS1W ly2 S2 W2
    (mkst regs2 (getr (ms_regs ms1) 1) mem2 (seg_rom SEGS)) md2); cbn [ms_regs ms_mem ms_resv ms_svc_pending
    ms_rom ms_fregs ms_fcsr mkst];
  [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
  | exact (eq_trans (HPR 2 ltac:(unfold acallee_saved; lia)) (eq_trans Q2 R2))
  | exact (eq_trans (HPR 9 ltac:(unfold acallee_saved; lia)) (eq_trans Q9 R9))
  | exact (eq_trans (HPR 8 ltac:(unfold acallee_saved; lia)) (eq_trans Q8 R8))
  | exact (eq_trans (HPR 18 ltac:(unfold acallee_saved; lia)) (eq_trans Q18 R18))
  | exact (eq_trans (HPR 19 ltac:(unfold acallee_saved; lia)) (eq_trans Q19 R19))
  | exact (eq_trans (HPR 25 ltac:(unfold acallee_saved; lia)) (eq_trans Q25 R25))
  | exact (eq_trans (HPR 20 ltac:(unfold acallee_saved; lia)) (eq_trans Q20 R20))
  | exact (eq_trans (HPR 3 ltac:(unfold acallee_saved; lia)) Q3')
  | exact (eq_trans (HPR 4 ltac:(unfold acallee_saved; lia)) Q4')
  | exact HINV2 ]. }
split.
{ intros i Hi. rewrite (HSK2 (um_SH cx fpos + 4 + i) ltac:(lia)). exact (HZ1 i Hi). }
exists kbs', al. unfold UM_ALIAS. split; [exact AL|]. split; [exact K1|]. split; [exact K2 | exact K3].
Qed.

End b.
End a.
