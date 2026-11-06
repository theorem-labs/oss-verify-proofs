(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B twin of lib/A/Prog/PcapSourceClose.v: pcap_source_close (fuzz_pcap.asan-ubsan
   0x81d4c, listing offset AF_pcap_source_close = 0x15c4, 31 instructions) on libreac v1.9.0's ASan+UBSan build, walked
   against lib/A's contract.

   The code is lib/A's ASan code (fuzz_pcap.asan 0x81e90, 27 instructions) with two UBSan guards and a register swap
   (measured: pcap-ubsan-inventory.md (sha256 5b607b62e337; internal record), row G6 and the pcap_source_close row of (c)). After
   the 32-byte frame and the saves of ra, s0 and s1, 0x81d5c `beqz a0` branches to the `unimp` at 0x81db4 when ps is
   null, 0x81d60 `mv s0,a0` (above the GOT load here), and 0x81d64 `andi a0,a0,7` / 0x81d68 `bnez a0` branch to the same
   `unimp` when ps is not 8-aligned. The shadow base is then loaded through the GOT word 0x996f8 (object 1; through a0,
   where the ASan code uses a1) from the cell 0xa17b8 (object 15). The rest is the ASan code at other pcs: the shadow
   check of ps's 8 bytes (0x81d80 `lbu`, 0x81d84 `bnez` to the error path at 0x81db8), f = ps->f (0x81d88), the test of
   f (0x81d8c `beqz` to 0x81da0), the call of the fclose wrapper's 4-byte jump (0x81d90 `jal
   __interceptor_trampoline_fclose`, 0x4161c), the second shadow check (0x81d94, 0x81d98 `bnez` to the error path at
   0x81dc0), ps->f = NULL (0x81d9c `sd zero,0(s0)`), the restores and the return (0x81db0).

   THE GUARDS. The walk's first symbolic run decides both, from the facts on a0 = ps that cl_entry proves (atom 10: ps
   >= 4096 and ps mod 2^3 = 0; ps >= 4096 because ps lies in a frame of the caller (frames_bounds), which gives the
   statement's ps <> 0; the alignment is the statement's ps mod 8 = 0):
     0x81d5c: decide_cond2 (Reusable/YP0e.v:932) through decide_eq (Reusable/YP0m.v:658-672), whose SOff / SLit arm
              (:665-666) tests ranges_disjoint (:653): ps's range [4096, ...] is disjoint from 0, so the branch is not
              taken;
     0x81d68: s_and_ptr (Reusable/YP0m.v:969-980) rewrites ps & 7 to 0 from the alignment fact, so `bnez` sees 0 and is
              not taken.
   These are the decisions of the released UBSan proof for the v1.8 image (proofs/libreac/fuzz_pcap/lib/U/Prog/
   pcap_source_close.v on origin/ossv/recipes c8557374ad2e): close_closed :43 (if_false, premise bv_unsigned a0 <> 0 at
   :23) and :45-46 (ub_align A8, premise bv_unsigned a0 mod 8 = 0 at :23), close_pro :82 and :84-85 (premises :58).

   The contract is lib/A's, not a copy (the shared-text rule): pb_pcap_source_closeX proves lib/A's image-generic
   AC.tpcap_source_close_specX (with AC.tpcap_source_close_post and AC.tclose_kept) at this image's segments SEGS and
   relro window pa_relro_lo / pa_relro_hi of the lib/B PAImg instance (on the pin PcapRelro.PCAP_RLO /
   PcapRelro.PCAP_RHI, lib/B/Prog/PcapRelro.v), at a = BASE + AF_pcap_source_close of the lib/B listing. The image-free constants
   (TPCAP_SOURCE_CLOSE_STK, EV_CLOSE, tclose_fblk) and lemmas are lib/A's too, through AC. The fclose wrapper's contract
   is the Section hypothesis AFCLOSE, of lib/A/Stdio/PFclose.v's image-generic afclose_source_spec type at this image.
   There is no lib/B/Stdio/PFclose.v (that statement takes the image as parameters). AFCLOSE is discharged by the
   asan-ubsan instance of a Theorem Labs lane's fclose walk lib/A/Stdio/WFclose.v, whose lib/B walk twin is
   lib/B/Stdio/WFclose.v (lib/B/Stdio/PFcloseInstB.v's inst_AFCLOSE_U composes it with lib/B/Stdio/WFcloseI.v).
   getr / mkst / seg_rom come from YK11; nothing from lib/Lib is imported. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceClose.v, with its module names changed; 3497 of its 3557 lines of code are new or changed and 570 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessTail.v, with its module paths and module names changed; 346 of its 396 lines of code are new or changed and 3507 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_served_markDec.v, with its numbers changed; 461 of its 510 lines of code are new or changed and 347 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_served_markMidCall.v, with its module names changed; 294 of its 346 lines of code are new or changed and 458 lines of the source are left out. *)
(* reac_served_mark (fuzz_link.asan 0x895a8) on image A: the pieces the two wrapper_fprintf arms share (the VVLAN arm
   +0x510, 0x89aec `jal wrapper_fprintf` with .str.8 and the name; the VHOST arm +0x57c, 0x89b5c with .str.9, the name
   and the alias). Both arms run the same way: the cut, the g_say load (sink <> 0, so the stderr arm is
   not taken), the call of the fprintf wrapper 0x43084 on the memory FILE g_say holds, s5 := the verdict, `j` to the
   RESTORE cut +0x2cc.
   - `srm_mark_leave`: link_spec's mark_lib on a read that succeeded with a LEAVE verdict: the verdict, the marks and
     the kernel as the read left them.
   - `srm_base_move`: a cut's base at a state with the same memory and the twelve registers the base reads.
   - `srm_fprintf_step`: the call of wrapper_fprintf 0x43084 from a state whose base holds, over the closed fprintf
     contract (lib/A/Rt/LinkVfDefs.v afprintf_mf_realizes, as the Section hypothesis HFP at every FP state), on the
     caller's journal (lib/A/Prog/LinkWalkMkPrintf.v aj_gx_printf_mf_at): the base again at the return state, at the
     fx' the wrapper returns (the Kit's srm_call_back, through the contract's post read as an apost), the FILE with
     |T| more bytes pending, and every byte outside the FILE block and the wrapper's window kept.
   - `srm_arm_finish`: the RESTORE cut's obligation from a state there, with s5 = the verdict.
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFileSink AMemFile AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkVfDefs LinkVfInst.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkSide PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkMkPrintf LinkWalkMkFile LinkWalkMkCr.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_served_markDefs reac_served_markKit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_served_markPf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- link_spec: a read that succeeded, a LEAVE verdict ---- *)
Lemma srm_mark_leave : forall tab s gbs kbs v,
  s <> [] -> r_rc (srm_R s kbs tab) = 0 ->
  decide (Some (r_kind (srm_R s kbs tab))) (Some (r_alias (srm_R s kbs tab))) = v ->
  v = V_LEAVE_VLAN \/ v = V_LEAVE_HOST ->
  mark_lib tab (Some s) (mk_names gbs) (nk_sent kbs) (nk_kstate kbs) =
    Mres v (mk_names gbs) (r_reqs (srm_R s kbs tab)) (r_state (srm_R s kbs tab)).
Proof.
  intros tab s gbs kbs v Hs Hrc Hd Hv.
  unfold mark_lib, mark_core. destruct s as [|b s']; [exfalso; exact (Hs eq_refl)|].
  unfold srm_R, read_lib in Hrc, Hd |- *.
  cbn [length Nat.eqb]. rewrite Hrc. cbn [Z.eqb negb]. rewrite Hd.
  destruct Hv as [-> | ->]; reflexivity.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TB : PcapSyms B.
Hypothesis RELRO_IMG : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.
Hypothesis HSEGS : SEGS = tfibsegs.
(* wrapper_fprintf 0x43084 on link's memory FILE: the closed contract (LinkVfInst.v
   link_afprintf_contract) at the walk's segments, at every FP state *)
Hypothesis HFP : forall fx' : YK11.FPState,
  @afprintf_mf_realizes fx' rc SEGS B link_amf PCAP_RLO PCAP_RHI link_vf_FF LFP_STK LA_GOT_GUARD LA_GUARD
    LA_W_FPRINTF.

(* the twelve registers srm_base reads *)
Definition srm_kregs (R' R : bvmap 5 word) : Prop :=
  getr R' 2 = getr R 2 /\ getr R' 9 = getr R 9 /\ getr R' 8 = getr R 8 /\ getr R' 18 = getr R 18 /\
  getr R' 19 = getr R 19 /\ getr R' 25 = getr R 25 /\ getr R' 26 = getr R 26 /\ getr R' 20 = getr R 20 /\
  getr R' 22 = getr R 22 /\ getr R' 3 = getr R 3 /\ getr R' 4 = getr R 4 /\ getr R' 27 = getr R 27.

Lemma srm_base_move : forall cx fpos X ly3 S3 W3 (ms ms' : machine_state) md md',
  srm_base fx SK B cx fpos X ly3 S3 W3 ms md ->
  ms_resv ms' = None -> ms_svc_pending ms' = None -> ms_rom ms' = seg_rom SEGS ->
  ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  ms_mem ms' = ms_mem ms ->
  ajournal_gx SEGS B (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx) (sm_FP cx)
    (sm_ly cx) (sm_S cx) (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) ((SRM_CID, fpos) :: sm_own cx)
    ly3 S3 W3 (ms_mem ms') md' (sm_k cx) ->
  srm_kregs (ms_regs ms') (ms_regs ms) ->
  m_fds md' = m_fds md -> m_fs md' = m_fs md ->
  srm_base fx SK B cx fpos X ly3 S3 W3 ms' md'.
Proof.
  intros cx fpos X ly3 S3 W3 ms ms' md md' HB H1 H2 H3 H4 H5 Em HJ HR Hfd Hfs.
  unfold srm_base in *. cbv zeta in *. rewrite Em in HJ |- *.
  destruct HB as (_ & _ & _ & _ & _ & _ & B1 & B2 & B3 & B4 & B5 & R2 & R9 & R8 & R18 & R19 & R25 & R26 & R20
    & R22 & R3 & R4 & R27 & Sv1 & Sv & Fl & Fp & Sp & Ak & Fd & Fs & Ro & Fz).
  destruct HR as (E2 & E9 & E8 & E18 & E19 & E25 & E26 & E20 & E22 & E3 & E4 & E27).
  refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj HJ (conj B1 (conj B2 (conj B3 (conj B4 (conj B5 _))))))))))).
  refine (conj (eq_trans E2 R2) (conj (eq_trans E9 R9) (conj (eq_trans E8 R8) (conj (eq_trans E18 R18)
    (conj (eq_trans E19 R19) (conj (eq_trans E25 R25) (conj (eq_trans E26 R26) (conj (eq_trans E20 R20)
    (conj (eq_trans E22 R22) (conj (eq_trans E3 R3) (conj (eq_trans E4 R4) (conj (eq_trans E27 R27) _)))))))))))).
  refine (conj Sv1 (conj Sv (conj Fl (conj Fp (conj Sp (conj Ak (conj _ (conj _ (conj Ro Fz))))))))).
  - rewrite Hfd. exact Fd.
  - rewrite Hfs. exact Fs.
Qed.

(* a journal's state satisfies AR *)
Lemma srm_jAR : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k -> AR SEGS B ly' S' W' mem' md'.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k (_ & _ & (memS & HJi & _) & _).
  exact (proj1 HJi).
Qed.

(* materialising keeps the descriptors and the file system *)
Lemma srm_sbm_fds_fs : forall m m', same_but_materialized m m' -> m_fds m' = m_fds m /\ m_fs m' = m_fs m.
Proof. intros m m' H. rewrite H. apply wvb_fds_fs. Qed.

(* a byte of the FILE block is a byte of the contract's write set *)
Lemma srm_file_E : forall cx a, sm_sink cx <> 0 -> sm_sink cx <= a < sm_sink cx + AMF_BLOCK -> srm_E cx a.
Proof.
  intros cx a Hs Ha. unfold srm_E, srm_wr, reac_served_mark_awr, inFP.
  exists (aivl (sm_sink cx) AMF_BLOCK). split; [right; right; left; reflexivity|].
  unfold aivl. cbn [fst snd]. destruct (Z.eqb_spec (sm_sink cx) 0) as [E|E]; [contradiction | exact Ha].
Qed.

(* THE CALL of wrapper_fprintf 0x43084, from a state whose base holds *)
Lemma srm_fprintf_step : forall (cx : srmcx) fpos ly3 S3 W3 (ms3 : machine_state) md3
    (regsT : bvmap 5 word) md1 (fmt k0 : Z) (T : list Z) (Q : world SEGS -> config -> Prop),
  srm_pre SK B cx ->
  srm_base fx SK B cx fpos (srm_E cx) ly3 S3 W3 ms3 md3 ->
  ajournal_gx SEGS B (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx) (sm_FP cx)
    (sm_ly cx) (sm_S cx) (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) ((SRM_CID, fpos) :: sm_own cx)
    ly3 S3 W3 (ms_mem ms3) md1 (sm_k cx) ->
  m_fds md1 = m_fds md3 -> m_fs md1 = m_fs md3 ->
  srm_kregs regsT (ms_regs ms3) ->
  getr regsT 10 = w64 (sm_sink cx) -> getr regsT 11 = w64 fmt ->
  YK0s.ret_ok (getr regsT 1) -> 4096 <= raZ regsT ->
  amemfile_k SEGS (rdW W3 (ms_mem ms3)) (sm_sink cx) k0 ->
  k0 + Z.of_nat (length T) <= AMF_BUFSIZ ->
  link_vf_FF (aview SEGS (w_H W3) (ms_mem ms3)) (vmf_out LFP_STK (srm_sp1 cx) (sm_sink cx)) fmt
    (map (argZ regsT) [2; 3; 4; 5; 6; 7]) T ->
  Z.of_nat (length T) < 2 ^ 31 - 1 ->
  (forall (fx' : YK11.FPState) ly4 S4 regs2 mem2 md2,
     @BoxBase.fxr fx fx' ->
     srm_base fx' SK B cx fpos (srm_E cx) ly4 S4 W3 (@mkst fx' regs2 (getr regsT 1) mem2 (seg_rom SEGS)) md2 ->
     aregs_preserved regsT regs2 ->
     akept SEGS B ly3 S3 W3 (ms_mem ms3) W3 mem2 (srm_sp1 cx - LFP_STK) (srm_sp1 cx)
       (fun a => sm_sink cx <= a < sm_sink cx + AMF_BLOCK) ->
     amemfile_k SEGS (rdW W3 mem2) (sm_sink cx) (k0 + Z.of_nat (length T)) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sm_sink cx <= a < sm_sink cx + AMF_BLOCK) ->
        ~ (srm_sp1 cx - LFP_STK <= a < srm_sp1 cx) -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
     SRr SEGS W3 (mkCfg (@mkst fx' regs2 (getr regsT 1) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W3 (mkCfg (mkst regsT (Z_to_bv 64 LA_W_FPRINTF) (ms_mem ms3) (seg_rom SEGS)) md1) Q.
Proof.
  intros cx fpos ly3 S3 W3 ms3 md3 regsT md1 fmt k0 T Q HPRE HBASE HJ1 Hfd1 Hfs1 HKR Ha0 Ha1 Hret Hra
    HMF HkT HFF HT HK.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof srm_pow as (P47 & P64).
  set (ms1 := mkst regsT (Z_to_bv 64 LA_W_FPRINTF) (ms_mem ms3) (seg_rom SEGS)).
  assert (HB1 : srm_base fx SK B cx fpos (srm_E cx) ly3 S3 W3 ms1 md1).
  { apply (srm_base_move cx fpos (srm_E cx) ly3 S3 W3 ms3 ms1 md3 md1 HBASE); try reflexivity;
      [exact HJ1 | exact HKR | exact Hfd1 | exact Hfs1]. }
  pose proof (srm_sp_facts SK B LAWS TB RELRO_IMG HSEGS cx HPRE) as (Q1 & Q2 & Q3 & Q4 & Q5).
  unfold srm_sp in Q1, Q2, Q3, Q4.
  pose proof (srm_base_sp SK B LAWS TB RELRO_IMG HSEGS fx cx fpos (srm_E cx) ly3 S3 W3 ms1 md1 HPRE HB1) as Hsp.
  change (ms_regs ms1) with regsT in Hsp.
  pose proof REAC_SERVED_MARK_AK_val as HKv.
  assert (HLFP : LFP_STK = 5664) by reflexivity.
  assert (HKe : REAC_CODE_EMIT_AK = 9360) by reflexivity.
  destruct (srm_gsay_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos (srm_E cx) ly3 S3 W3 ms3 md3 HPRE HBASE
    (fun a H => H)) as (_ & Hs1 & Hs2 & Hs3).
  (* the callee's apre at the call: journal, gx_ok, arodata, gp / tp, window, the FILE's ajw *)
  assert (HWR : forall a, inFP [aivl (sm_sink cx) AMF_BLOCK] a -> srm_E cx a \/ srm_bufb cx fpos a).
  { intros a (r & Hr & Ha). destruct Hr as [<- | []]. left. apply srm_file_E; [lia|].
    unfold aivl in Ha. cbn [fst snd] in Ha. destruct (Z.eqb_spec (sm_sink cx) 0); [lia | exact Ha]. }
  pose proof (srm_call_apre SK B LAWS TB RELRO_IMG HSEGS fx cx fpos (srm_E cx) ly3 S3 W3 ms1 md1 LFP_STK []
    [aivl (sm_sink cx) AMF_BLOCK] HPRE HB1 (fun a H => H) ltac:(lia) Hret Hra
    ltac:(intros cd []) HWR) as HAPRE.
  destruct HAPRE as (HJa & HGX & HRO & Hretok & Hra' & Hgp & Htp & H16 & Hlo & Hhi & Hnev & Hside & Hajw & Hnro).
  change (ms_regs ms1) with regsT in *. change (ms_mem ms1) with (ms_mem ms3) in *.
  destruct (aj_gx_printf_pre SK SEGS B LFP_STK (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx) (sm_FP cx)
    (sm_ly cx) (sm_S cx) (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) ((SRM_CID, fpos) :: sm_own cx) ly3 S3 W3 (ms_mem ms3)
    md1 (sm_k cx) regsT HJ1 ltac:(unfold ESTACK; lia) H16 Hlo Hhi Hretok Hgp Htp) as (Hecall & Hstk & Hwin).
  rewrite Hsp in Hstk, Hwin, Hlo, Hhi.
  (* the FILE block *)
  assert (Hin : In (sm_sink cx, AMF_BLOCK) (ablocks B ly3 S3)).
  { pose proof HPRE as (_ & _ & (kbs' & tab' & nm' & k' & Hin0 & _)).
    pose proof HBASE as HB''. unfold srm_base in HB''. cbv zeta in HB''.
    destruct HB'' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hperm & _).
    eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hin0]. }
  pose proof (srm_jAR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR1.
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md1 (sm_sink cx) AMF_BLOCK HAR1 Hin)
    as (_ & _ & _ & _ & Hfpres & _ & _).
  destruct (amf_k_of_amemfile_k SEGS (rdW W3 (ms_mem ms3)) (sm_sink cx) k0 HMF) as (Hamf & Haw1 & Haw2).
  assert (Hk0 : 0 <= k0 <= AMF_BUFSIZ).
  { destruct Hamf as (_ & [(-> & _) | (Hk & _)]); unfold AMF_BUFSIZ in *; lia. }
  destruct (amf_k_facts SEGS link_amf (rdW W3 (ms_mem ms3)) (sm_sink cx) k0 Hamf) as
    (fl & om & wend & wpos & wbase & pos & len & pb & Hdyn & Hpend & Hlen).
  { intros i Hi. destruct (Hfpres (sm_sink cx + AMF_BUF + i)) as ((Hh & b & Hb) & _).
    { unfold req_size, AMF_BUF, AMF_BUFSIZ, AMF_BLOCK in *. cbn. lia. }
    unfold ard, mbyte, mrestrict. rewrite Hh, Hb. discriminate. }
  (* the guard *)
  pose proof (link_guard_got B TB HSEGS ly3 S3 W3 (ms_mem ms3) md1 HAR1) as Hgot.
  destruct (link_guard_val HSEGS W3 (ms_mem ms3)) as (cval & Hgv).
  destruct (link_guard_apart B LAWS HSEGS ly3 S3 W3 (ms_mem ms3) md1 LFP_STK (srm_sp1 cx) (sm_sink cx) HAR1 Hin
    ltac:(lia) ltac:(lia)) as (Hgd & Hvd).
  (* the contract at the call *)
  pose proof (HFP fx ly3 S3 W3 regsT (ms_mem ms3) md1 (sm_sink cx) fmt k0 fl om wend wpos wbase pos len pb []
    (map (argZ regsT) [2; 3; 4; 5; 6; 7]) T cval Hecall) as HC.
  rewrite Hsp in HC.
  specialize (HC Hstk Hwin Ha0 Ha1 Hin).
  assert (Hsep : sm_sink cx + AMF_BLOCK <= srm_sp1 cx - LFP_STK).
  { rewrite HLFP. rewrite HKv in Q2. clear - Hs2 Q2 Q4. lia. }
  assert (Hpw : pairwise zdisjoint (vmf_out LFP_STK (srm_sp1 cx) (sm_sink cx))).
  { unfold vmf_out. cbn [pairwise]. split; [apply Forall_cons; [|apply Forall_nil] | split; [apply Forall_nil | exact I]].
    unfold zdisjoint. cbn [fst snd]. right. exact Hsep. }
  specialize (HC Hpw).
  specialize (HC Hamf Hdyn Hpend Hlen HkT HRO Hgot Hgv ltac:(unfold LA_GOT_GUARD; lia) ltac:(unfold LA_GOT_GUARD; lia)
    ltac:(unfold LA_GUARD; lia) ltac:(unfold LA_GUARD; lia) Hgd Hvd).
  assert (Hfva : fva_words regsT (aview SEGS (w_H W3) (ms_mem ms3)) (srm_sp1 cx) []
    (map (argZ regsT) [2; 3; 4; 5; 6; 7])).
  { split; [rewrite app_nil_r; reflexivity|]. intros i Hi. cbn [length] in Hi. lia. }
  specialize (HC Hfva).
  assert (Hxs : srm_sp1 cx + 8 * Z.of_nat (@length Z []) <= 2 ^ 47) by (cbn [length Z.of_nat]; lia).
  specialize (HC Hxs).
  assert (Hxd : Forall (zdisjoint (srm_sp1 cx, 8 * Z.of_nat (@length Z []))) (vmf_out LFP_STK (srm_sp1 cx) (sm_sink cx))).
  { unfold vmf_out. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      unfold zdisjoint; cbn [fst snd length Z.of_nat]; right; clear - Hsep HLFP; rewrite HLFP in Hsep; lia. }
  specialize (HC Hxd).
  pose proof HBASE as HB'. unfold srm_base in HB'. cbv zeta in HB'.
  destruct HB' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & _ & _ & _ & _ & _ & Hfz).
  specialize (HC HFF HT Hfz).
  (* the step on the journal *)
  eapply SRr_bind.
  { apply (aj_gx_printf_mf_at SK SEGS B LAWS pa_segs_low LFP_STK LA_W_FPRINTF (sm_G cx) (sm_XO cx) (sm_OUT cx) W3
      regsT (ms_mem ms3) (sm_STK cx) (sm_sp0 cx) (sm_FP cx) (sm_ly cx) (sm_S cx) (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx)
      ((SRM_CID, fpos) :: sm_own cx) ly3 S3 md1 (sm_k cx) (getr regsT 1) (sm_sink cx) k0 pb T fl om wend pos len
      HGX HJ1 ltac:(lia) ltac:(rewrite Hsp; lia) ltac:(rewrite Hsp; lia) eq_refl).
    - intros a Ha. apply Hajw. exists (aivl (sm_sink cx) AMF_BLOCK). split; [left; reflexivity|].
      unfold aivl. cbn [fst snd]. destruct (Z.eqb_spec (sm_sink cx) 0); [lia | exact Ha].
    - rewrite Hsp. exact HC. }
  cbv beta. intros W2 c2 _ (-> & fx' & regs2 & mem2 & md2 & -> & Hfxr & HJ2 & HP2 & Hsbm & H10 & Hfp & Hkept & Hprs).
  rewrite Hsp in Hkept.
  destruct (srm_sbm_fds_fs md1 md2 Hsbm) as (Hfd2 & Hfs2).
  set (Ec := fun a => sm_sink cx <= a < sm_sink cx + AMF_BLOCK).
  (* the wrapper's post as an apost at fx' *)
  assert (HAK : akept SEGS B ly3 S3 W3 (ms_mem ms3) W3 mem2 (srm_sp1 cx - LFP_STK) (srm_sp1 cx) Ec).
  { apply (akept_step SK SEGS B LAWS pa_segs_low ly3 S3 W3 (ms_mem ms3) md1 W3 (ms_mem ms3) W3 mem2
      (srm_sp1 cx - LFP_STK) (srm_sp1 cx) Ec Ec
      (fun a => Ec a \/ (srm_sp1 cx - LFP_STK <= a < srm_sp1 cx)) HAR1 ltac:(lia) ltac:(lia)).
    - exact (akept_refl SK SEGS B LAWS pa_segs_low ly3 S3 W3 (ms_mem ms3) (srm_sp1 cx - LFP_STK) (srm_sp1 cx) Ec Hwin).
    - intros a Ha HX. apply Hkept; [exact Ha | intros H; exact (HX (or_introl H)) | intros H; exact (HX (or_intror H))].
    - intros a _ Hp. exact (Hprs a Hp).
    - intros a H. exact H.
    - intros a [H | H]; [left; exact H | right; exact H]. }
  assert (HSK : ashadow_kept SEGS B ly3 S3 ly3 S3 W3 (ms_mem ms3) W3 mem2).
  { intros b m a Hb _ Ha.
    destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md1 b m HAR1 Hb) as (_ & Hb1 & Hb2 & _).
    pose proof (shadow_addr_bounds a ltac:(lia)) as (Sh1 & Sh2).
    apply Hkept.
    - lia.
    - intros HF. assert (HE : srm_E cx (shadow_addr a)) by (apply srm_file_E; [lia | exact HF]).
      destruct (srm_E_app SK B LAWS TB RELRO_IMG HSEGS cx (shadow_addr a) HPRE HE) as (_ & [HL | HH]); lia.
    - lia. }
  destruct (srm_call_back SK B LAWS TB RELRO_IMG HSEGS fx fx' cx fpos (srm_E cx) ly3 S3 W3 ms1 md1 LFP_STK Ec
    (fun _ _ => True) W3 (mkCfg (@mkst fx' regs2 (getr regsT 1) mem2 (seg_rom SEGS)) md2) HPRE HB1 (fun a H => H)
    Hfxr ltac:(lia) ltac:(intros a Ha; left; apply srm_file_E; [lia | exact Ha])) as
    (ly4 & S4 & regs4 & mem4 & md4 & Ec4 & HB4 & HP4 & HK4 & _).
  { exists ly3, S3, regs2, mem2, md2.
    split; [reflexivity|]. split; [rewrite Z.add_0_r; exact HJ2|]. split; [exact HP2|]. split; [reflexivity|].
    split; [change (m_fds md2 = m_fds md1); exact Hfd2|]. split; [change (m_fs md2 = m_fs md1); exact Hfs2|].
    split; [change (spZ (ms_regs ms1)) with (spZ regsT); rewrite Hsp; exact HAK|]. split; [exact HSK|].
    split; [destruct S3; reflexivity|]. split; [apply Permutation_refl | exact I]. }
  injection Ec4 as Er Em Ed. subst regs4 mem4 md4.
  apply (HK fx' ly4 S4 regs2 mem2 md2 Hfxr HB4 HP4 HAK).
  - destruct (apf_file_post_parts SEGS link_amf (rdW W3 mem2) (sm_sink cx) k0 pb T fl om wend pos len Hfp)
      as (Hamf2 & _ & _).
    apply amemfile_k_of_amf_k; [exact Hamf2| |].
    + exact (awrange_grows SEGS W3 (ms_mem ms3) mem2 (sm_sink cx) AMF_BLOCK Hprs Haw1).
    + exact (awrange_grows SEGS W3 (ms_mem ms3) mem2 LA_G_SAID SAID_SIZE Hprs Haw2).
  - intros a Ha HnF Hnw. exact (Hkept a Ha HnF Hnw).
Qed.

(* THE RESTORE CUT from a LEAVE arm *)
Lemma srm_arm_finish : forall cx fpos ly5 S5 W5 (ms5 : machine_state) md5 s kbs tab gbs k0 kbs1 k' v,
  srm_restore_obl fx SK B ->
  srm_pre SK B cx -> srm_gspan_ok B cx ->
  ms_pc_val ms5 = w64 (BASE + SRM_CUT_RESTORE) -> getr (ms_regs ms5) 21 = w64 v ->
  srm_base fx SK B cx fpos (srm_E cx) ly5 S5 W5 ms5 md5 ->
  srm_ent cx s kbs tab gbs k0 ->
  r_rc (srm_R s kbs tab) = 0 ->
  decide (Some (r_kind (srm_R s kbs tab))) (Some (r_alias (srm_R s kbs tab))) = v ->
  v = V_LEAVE_VLAN \/ v = V_LEAVE_HOST ->
  srm_kern (rdW W5 (ms_mem ms5)) kbs kbs1 tab (r_state (srm_R s kbs tab)) (r_reqs (srm_R s kbs tab)) 1 ->
  amarks_at SEGS (rdW W5 (ms_mem ms5)) (srm_mk cx) gbs ->
  amemfile_k SEGS (rdW W5 (ms_mem ms5)) (sm_sink cx) k' -> k0 <= k' <= k0 + MARK_LINE_MAX ->
  SRr SEGS W5 (mkCfg ms5 md5) (srm_post fx SK B cx).
Proof.
  intros cx fpos ly5 S5 W5 ms5 md5 s kbs tab gbs k0 kbs1 k' v HREST HPRE HSP Hpc R21 HB HENT Hrc Hdec Hv HK HMK
    HMF Hk'.
  apply (HREST cx fpos ly5 S5 W5 ms5 md5 HPRE HSP).
  exists v. split; [exact Hpc|]. split; [exact R21|]. split; [|exact HB].
  pose proof HENT as (_ & _ & Hs & _ & _ & Hwf & _).
  pose proof (srm_mark_leave tab s gbs kbs v Hs Hrc Hdec Hv) as HM.
  change v with (m_rc (Mres v (mk_names gbs) (r_reqs (srm_R s kbs tab)) (r_state (srm_R s kbs tab)))).
  eapply srm_pf_of; [exact HENT | exact (eq_sym HM) | | exact HMK | exact Hwf | reflexivity | exact HMF | exact Hk'].
  eapply srm_kern_mono; [|exact HK]. lia.
Qed.

(* a machine state the engine certifies is its mkst *)
Lemma srm_pf_ms_eta : forall ms : machine_state,
  ms_fregs ms = fp_regs -> ms_svc_pending ms = None -> ms_resv ms = None -> ms_fcsr ms = fp_csr ->
  ms = mkst (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (ms_rom ms).
Proof. intros [] H1 H2 H3 H4; cbn in *; subst; reflexivity. Qed.

Lemma srm_pf_env_agree : forall regs, env_agree 32 (Ereg regs []) (Eimg (Ereg regs [])).
Proof. intros regs. split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

(* the twelve registers srm_base reads *)
Definition SRM_PF_KEEP : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 22%bv; 25%bv; 26%bv; 27%bv].

(* the plain symbolic state at a code offset: every register its own atom, no region, no fact *)
Definition srm_pf_ss (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).

Lemma srm_pf_ss_ok : forall (W : world SEGS) regs mem pc,
  st_ok_pi SEGS pa_val (Eimg (Ereg regs [])) (srm_pf_ss pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
  intros W regs mem pc. rewrite restrict_mkst_fx. unfold srm_pf_ss. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [exact I | split; exact I].
Qed.

(* THE TAIL of a LEAVE arm: from the return of wrapper_fprintf, `addi s5, zero, v` and `j` to the RESTORE cut (the
   engine run, whose result the arm computes), then the cut's obligation *)
Lemma srm_leave_tail : forall (retoff v : Z) (ss' : sstate) (st : prun_status lsym)
    cx fpos ly4 S4 W4 (ms4 : machine_state) md4 s kbs tab gbs k0 kbs1 k',
  sym_run_toN_pi pl_tpi FUEL SRM_CUT_RESTORE (srm_pf_ss retoff) = (ss', st) ->
  pi_plain_stop st -> ss_pc ss' = SRM_CUT_RESTORE -> ss_resv ss' = None ->
  sr_get (ss_regs ss') 21%bv = SLit v ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss') r) (SOff (Z.to_nat (bv_unsigned r)) 0)) SRM_PF_KEEP = true ->
  srm_restore_obl fx SK B -> srm_pre SK B cx -> srm_gspan_ok B cx ->
  ms_pc_val ms4 = w64 (BASE + retoff) ->
  srm_base fx SK B cx fpos (srm_E cx) ly4 S4 W4 ms4 md4 ->
  srm_ent cx s kbs tab gbs k0 ->
  r_rc (srm_R s kbs tab) = 0 ->
  decide (Some (r_kind (srm_R s kbs tab))) (Some (r_alias (srm_R s kbs tab))) = v ->
  v = V_LEAVE_VLAN \/ v = V_LEAVE_HOST ->
  srm_kern (rdW W4 (ms_mem ms4)) kbs kbs1 tab (r_state (srm_R s kbs tab)) (r_reqs (srm_R s kbs tab)) 1 ->
  amarks_at SEGS (rdW W4 (ms_mem ms4)) (srm_mk cx) gbs ->
  amemfile_k SEGS (rdW W4 (ms_mem ms4)) (sm_sink cx) k' -> k0 <= k' <= k0 + MARK_LINE_MAX ->
  SRr SEGS W4 (mkCfg ms4 md4) (srm_post fx SK B cx).
Proof.
  intros retoff v ss' st cx fpos ly4 S4 W4 ms4 md4 s kbs tab gbs k0 kbs1 k' Hrun Hst Hpc' Hrv' H21 HKS
    HREST HPRE HSP Hpc4 HB4 HENT Hrc Hdec Hv HK HMK HMF Hk'.
  pose proof HB4 as HB'. unfold srm_base in HB'. cbv zeta in HB'.
  destruct HB' as (Zrsv & Zsvc & Zrom & Zfrg & Zfcsr & HJ4 & _).
  pose proof HPRE as ((_ & HGX & _) & _).
  assert (HS : st_ok_pi SEGS pa_val (Eimg (Ereg (ms_regs ms4) [])) (srm_pf_ss retoff) (restrict (w_H W4) ms4)).
  { rewrite (srm_pf_ms_eta ms4 Zfrg Zsvc Zrsv Zfcsr) at 2. rewrite Hpc4, Zrom. apply srm_pf_ss_ok. }
  assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms4) []))) by apply Eimg_env.
  pose proof (srm_pf_env_agree (ms_regs ms4)) as HAE.
  remember (Eimg (Ereg (ms_regs ms4) [])) as E eqn:HEdef.
  eapply (paj_run_to_plain_x SK B LAWS (sm_G cx) HGX (sm_XO cx) (sm_OUT cx));
    [exact HEI | exact HS | exact Hrun | exact Hst | exact HJ4 | apply awr_ok_x_nil |].
  intros ms5 mat5 HS5 HJ5 HF5 _ _.
  pose proof (regs_kept_of_st_ok_pi _ _ _ _ _ SRM_PF_KEEP HS5 HAE HKS) as QK.
  cbn [ms_regs restrict] in QK.
  assert (Q21 : getr (ms_regs ms5) 21 = w64 v).
  { rewrite (st_ok_pi_restrict_reg (w_H W4) E ss' ms5 21%bv HS5), H21. reflexivity. }
  assert (Em5 : ms_mem ms5 = ms_mem ms4).
  { apply functional_extensionality. intros x. apply HF5. cbn [srm_pf_ss ss_mem]. intros (r & Hr & _). destruct Hr. }
  rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS5 Hrv'), Hpc'.
  set (ms5' := mkst (ms_regs ms5) (Z_to_bv 64 (BASE + SRM_CUT_RESTORE)) (ms_mem ms5) (seg_rom SEGS)).
  assert (HB5 : srm_base fx SK B cx fpos (srm_E cx) ly4 S4 W4 ms5' (with_vm_backing (m_vm_lazy md4) mat5 md4)).
  { refine (srm_base_move cx fpos (srm_E cx) ly4 S4 W4 ms4 ms5' md4 _ HB4 eq_refl eq_refl eq_refl eq_refl eq_refl
      Em5 HJ5 _ (proj1 (wvb_fds_fs _ _ _)) (proj2 (wvb_fds_fs _ _ _))).
    unfold srm_kregs. repeat split; apply QK; cbn [In SRM_PF_KEEP]; repeat (first [left; reflexivity | right]). }
  apply (srm_arm_finish cx fpos ly4 S4 W4 ms5' _ s kbs tab gbs k0 kbs1 k' v HREST HPRE HSP eq_refl Q21 HB5 HENT Hrc
    Hdec Hv); try (change (ms_mem ms5') with (ms_mem ms5); rewrite Em5); assumption.
Qed.

End a.

About srm_mark_leave. About srm_base_move. About srm_fprintf_step. About srm_arm_finish.
Print Assumptions srm_fprintf_step. Print Assumptions srm_arm_finish.
