(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B's walk of pcap_source_open in the asan-ubsan instance of fuzz_pcap
   (libreac v1.9.0; pin fuzz_pcap.asan-ubsan, sha256 9e66f771f22a...; function at 0x811e0 =
   BASE + AF_pcap_source_open, AF = 0xa58), proving lib/A's image-generic contract tpcap_source_open_specX
   (lib/A/Prog/PcapSourceOpenDefs.v) at SEGS = pa_segs, rlo / rhi = pa_relro_lo / pa_relro_hi,
   apath / alen / afile = VAL (A_OBJ 3) / VAL (A_OBJ 4) / VAL (A_OBJ 2) (0x20d00 "<fuzz-input>", g_file_len
   0x5d3e40, g_file 0x5d3e60), with FM_RA and roimg as parameters. At ossv/recipes 25e3d17bdb50 (2026-10-29), there was no released proof of this function at
   this image (rule 24 lookup, a Theorem Labs lane, 22:35Z): the v1.8 ubsan proof (lib/U/Prog/pcap_source_open.v at
   origin/ossv/recipes c8557374ad2e) serves only as the template for the UBSan guards.

   The code. Up to the fopen call it is lib/A's ASan code byte for byte at
   other pcs (asan 0x8145c.. = asan-ubsan 0x811e0..): the prologue saves ra, s0 .. s9 (0x811e0..0x81210) and
   realigns s1 = sp = (sp - 96) & -32 (0x81218); the use-after-return flag is read through the GOT (0x81228
   auipc / 0x8122c ld, listing object 0 = 0x99750) from the runtime cell at 0x81234 (object 16 = 0xa17c0): the
   walk takes it as 1 (the kit's AR_const_law through al_const, with uar_cell_regionP (A_OBJ 16) holding SLit 1;
   the pin's file holds 0 and the runtime sets 1 at init), so 0x81240 `beqz a2` is not taken;
   __asan_stack_malloc_1(0x60) at 0x81248 returns the class-1 frame F (aj_stack_malloc_atS, YC85.v:292), whose
   two caller premises are discharged at op_to_call's frame request: count_cid 1 (frames Sc) < fs_frames 1 from
   op_pre's length (frames Sc) <= 7 through count_cid_le_length and 8 <= fs_frames 1, and the apath premise by
   op_SMP (stack_malloc_progressP from lib/Reusable/YG05.v:70, as cgif_file_fuzzer lib/A/ACed.v:129-130), so
   F >= 4096, 0x8125c `bnez s2` is taken and the machine-frame arm 0x81260..0x81278 is dead; then *(s1) = F
   (0x8127c), the header (0x41b58ab3, objects 10 and 11; 0x812a4..0x812ac), the twelve shadow bytes
   (0x812b8..0x812e4: 0xf1 x4, 0xf8 x3, 0xf3 x5), the mode literal "rb" (object 12, 0x812e8 / 0x812ec; HMODE)
   and the call of libreac_fuzz_fopen (0x812f4) through cl_callS (YC85.v:383) with FOPEN as the callee.

   The cut. This file walks the head: entry -> op_to_call (a Qed checkpoint at the call, op_at_call) ->
   head_to_fopen, which makes the call and establishes PcapSourceOpenPhF.v's op_fopen_ret at the return
   0x812f8. From there PcapSourceOpenPhM.v (op_from_fopen) walks to the two cuts of PcapSourceOpenPh.v and
   PcapSourceOpenB.v (op_from_null / op_from_read) to the return; pb_pcap_source_openX composes the three.
   The three UBSan guards are therefore decided outside this file, at these pcs and against these template lines:
   in PcapSourceOpenPhM.v 0x812f8 `beqz s3` (ps = 0, not taken: ps >= 4096 from op_pre's frame bounds; template
   :114 / :334, premise :93 / :290) and 0x81300 / 0x81304 `andi a0,s3,7; bnez a0` (ps mod 8 <> 0, not taken:
   op_pre's ps mod 8 = 0; template :115 / :335); in PcapSourceOpenB.v 0x81390 / 0x81394 `addi a0,zero,-3;
   bgeu s4,a0` (F + 32 >=u 2^64 - 3, not taken: F + 128 <= alloc_ceiling < 2^47; template :408-412, premise
   :291 and :295-299); all three
   go to the `unimp` at 0x8153c, and every ASan report path 0x81540..0x815b4 is dead because ps's 24 bytes are
   addressable and ps mod 8 = 0. In the head, op_at_call carries what those walks need: ps unwritten and still
   range_addressable, and op_fopen_ret's FILE-block footprint fact for the fclose of the tail.

   The callee hypotheses, used at this image as Section hypotheses: FOPEN : tlibreac_fuzz_fopen_specX
   (lib/A/Prog/PcapFuzzFopenDefs.v), AFREAD : afread_spec (lib/A/Stdio/PFreadISpec.v:138), AFCLOSE :
   afclose_source_spec (lib/A/Stdio/PFclose.v:209), ASM1 : astack_malloc_realizes (lib/Reusable/YG0d.v:285),
   ASF : astack_free_law (lib/Reusable/YG0d.v:301) and FFL : frame_flag_lawP (lib/Reusable/YCbq.v:797), the meter laws MLAW / MLAWF /
   FM, ASIL : asource_img_laws, and the kit's LAWS / TL / TLF / ML. Four instance obligations beyond the kit:
   ROK (roimg reads only image bytes outside the runtime's statics, errno and the open-file list head; applied at
   the fopen call to carry roimg from the entry memory across the prologue and the frame setup), HPATH (the path
   literal's shadow, as a law of every AR state: the frame request's kept clauses do not keep a global's shadow,
   YG0n.v:241 makes it aowned; discharged by the instance through AR_zshadow_law, YG0d.v:435-438), HGX (g_file_len
   and g_file are image bytes outside the runtime's statics and errno; the gx_ok shape of
   lib/A/Prog/PcapEntryDefs.v:366, 395, discharged by the harness), and RO : ro_below_ofl (as
   lib/A/Prog/PcapHarnessTail.v:37). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceOpen.v, with its module paths, module names and numbers changed; 574 of its 653 lines of code are new or changed and 1472 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_writeHead.v, with its module names changed; 201 of its 248 lines of code are new or changed and 606 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: kernel's phase +0x194 -> +0x3b4 (a segment of kernel's walk,
   link-a/plan/kernel-lanes.md (internal record, sha256 18c8d69749d5)): THE PHASE LEMMA kn_flags, kin_poison -> kin_err.
   From +0x194 (kernel_flags_base.v kfl_start): the right redzone's 32 stores of 0xf3 into F's shadow
   (+0x19c .. +0x218), s8 := shadow(a0 + 8) and its check (+0x21c .. +0x22c), slot 0xb0 := a0 + 8 (+0x230),
   a6 := n, a2 := nl_errno.e, a1 := a0 >> 3, then
   - n = 0 (+0x244 taken): +0x2fc a3 := 0, a0 := 0, a5 := 105, on to +0x3b4;
   - n > 0: the cursor's two checks, [a0 + 8] := n - 1, [a0] := p + 1, the check of the input byte at p (+0x280;
     its slow path +0x21c8, (p & 7) < s, refuted when taken), `lbu a3` = the flags d[0], and +0x290
     (kernel_flags_s1.v kfl_mid1), then +0x324 (kernel_flags_s2.v) and +0x344 (kernel_flags_s3.v).
   The phase's cuts inside it are machine-level (kernel_flags_base.v kfl_at), each rebuilt as a symbolic state.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c kernel_img kernel_defs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_flags_base kernel_flags_s3 kernel_flags_s2 kernel_flags_s1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Set Default Proof Using "All".
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis LV : LinkVals.
Hypothesis TL : PALib B.
Hypothesis TB : PcapSyms B.

(* the windows of run 1 lie in the phase's write set (F's right redzone, the slot, the cursor) *)
Local Ltac winX :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Ha := fresh "Ha" in let Hq := fresh "Hq" in
  intros b wlo whi a Hin Ha; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin];
    [injection Hq as <- <- <-; cbn [base_val] in Ha; cbn [ew ewset Nat.eqb] in Ha;
     repeat match goal with Hu : bv_unsigned (ew _ _) = _ |- _ => progress rewrite Hu in Ha end;
     unfold kfl_X; lia | ]);
  try destruct Hin.

(* the first state of the phase: run 1 wrote F's right redzone *)
Lemma kfl_mid_first : forall POST cx fpos k2 ly3 S3 W3 ms0 md0 ms1 md1 E rs,
  kfl_C SK B POST cx fpos k2 ly3 S3 W3 ms0 md0 ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms1) md1 k2 ->
  m_fds md1 = m_fds md0 -> m_fs md1 = m_fs md0 ->
  frame_of E rs (rdW W3 (ms_mem ms0)) (rdW W3 (ms_mem ms1)) ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi ->
     kfl_X cx fpos a) ->
  mem_grows (rdW W3 (ms_mem ms0)) (rdW W3 (ms_mem ms1)) ->
  kfl_f3 cx fpos W3 ms1 ->
  kfl_mid SK B POST cx fpos k2 ly3 S3 W3 ms0 md0 ms1 md1.
Proof.
  intros POST cx fpos k2 ly3 S3 W3 ms0 md0 ms1 md1 E rs HC HJ Hfds Hfs HFr Hw HG HF3.
  pose proof (kept_of_frame (segs := SEGS) E rs (w_H W3) (ms_mem ms0) (ms_mem ms1) (kfl_X cx fpos) HFr Hw) as KX.
  exact (conj HC (conj HJ (conj Hfds (conj Hfs (conj (conj KX HG) HF3))))).
Qed.

(* the 32 one-byte chunks 0xf3 of F's right redzone *)
Lemma kfl_f3_of : forall E H (mm : word -> option byte) cs F,
  Forall (YP09.chunk_ok SEGS E (mrestrict H mm) F) cs ->
  (forall i, 0x428 <= i < 0x448 -> In (YP09.mkChunk i (CVal 1 (SLit 18446744073709551603))) cs) ->
  forall i, 0x428 <= i < 0x448 -> aview SEGS H mm (F + i) = Some 0xf3.
Proof.
  intros E H mm cs F Hcs Hin i Hi.
  destruct (proj1 (Forall_forall _ _) Hcs _ (Hin i Hi) 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
  cbn [YP09.c_off YP09.c_val cbyte] in Hb1, Hb2. rewrite Z.add_0_r in Hb2.
  unfold aview. rewrite Hb2. injection Hb1 as <-. vm_compute. reflexivity.
Qed.

Local Ltac step_first HC msa msb HF3 HMn :=
  lazymatch goal with
  | HJx : ajournal_gx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem msb) _ _,
    HFx : frame_of _ _ (mrestrict _ (ms_mem msa)) (mrestrict _ (ms_mem msb)),
    HGx : mem_grows (mrestrict _ (ms_mem msa)) (mrestrict _ (ms_mem msb)) |- _ =>
    pose proof (kfl_mid_first _ _ _ _ _ _ _ _ _ _ _ _ _ HC HJx
      ltac:(repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity)
      ltac:(repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity)
      HFx ltac:(winX) HGx HF3) as HMn
  end.

Theorem kn_flags : forall POST, kfrom SK B POST (kin_err B) -> kfrom SK B POST (kin_poison B).
Proof.
  intros POST HNEXT cx fpos k2 ly3 S3 W3 ms0 md0 HB HJ Hfrm HI.
  assert (HC : kfl_C SK B POST cx fpos k2 ly3 S3 W3 ms0 md0)
    by exact (conj HB (conj HJ (conj Hfrm (conj HI HNEXT)))).
  pose proof (kfl_nums SK B LAWS LV TL TB _ _ _ _ _ _ _ _ _ HC) as (Hsp & Hsp47 & Hs1a & Hs1b & Hs1m & Hwlo & Hwhi &
    HF4 & HFc & HF64 & HFSH & Ha0 & Ha0r & Hapf & Hwp0 & Hwpn & Hwn0 & HFapp & HFa0).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  rewrite C3, C5 in Ha0r.
  assert (Ha47 : 0 <= ka0 cx < 2 ^ 47) by lia.
  assert (HK : KERNEL_AK = 4640) by reflexivity.
  assert (HFSHr : 0 <= kFSH cx fpos < 2 ^ 64) by (rewrite HFSH; unfold SHADOW_OFF; lia).
  pose proof (kfl_start SK B LAWS LV TL TB _ _ _ _ _ _ _ _ _ HC) as HS.
  change (kfl_E0 cx W3 ms0) with (kfl_EM cx W3 ms0 ms0) in HS.
  pose proof HI as HI'. unfold kin_poison, kat in HI'.
  destruct HI' as (_ & (R2 & R9 & R8 & R3 & R4 & R18 & R20) & Hkrl & _).
  unfold kregs_eq in Hkrl. rewrite Forall_forall in Hkrl.
  assert (E2 : ew (kfl_EM cx W3 ms0 ms0) 2 = w64 (ksp1 cx))
    by (rewrite (kfl_EM_reg SK B LAWS LV TL TB cx W3 ms0 ms0 2 2%bv eq_refl); exact R2).
  assert (E9 : ew (kfl_EM cx W3 ms0 ms0) 9 = w64 (ksp1 cx))
    by (rewrite (kfl_EM_reg SK B LAWS LV TL TB cx W3 ms0 ms0 9 9%bv eq_refl); exact R9).
  assert (E8 : ew (kfl_EM cx W3 ms0 ms0) 8 = w64 (ksp cx))
    by (rewrite (kfl_EM_reg SK B LAWS LV TL TB cx W3 ms0 ms0 8 8%bv eq_refl); exact R8).
  assert (E3 : ew (kfl_EM cx W3 ms0 ms0) 3 = getr (k_regs cx) 3)
    by (rewrite (kfl_EM_reg SK B LAWS LV TL TB cx W3 ms0 ms0 3 3%bv eq_refl); exact R3).
  assert (E4 : ew (kfl_EM cx W3 ms0 ms0) 4 = getr (k_regs cx) 4)
    by (rewrite (kfl_EM_reg SK B LAWS LV TL TB cx W3 ms0 ms0 4 4%bv eq_refl); exact R4).
  assert (E18 : ew (kfl_EM cx W3 ms0 ms0) 18 = w64 (ka0 cx))
    by (rewrite (kfl_EM_reg SK B LAWS LV TL TB cx W3 ms0 ms0 18 18%bv eq_refl); exact R18).
  assert (E20 : ew (kfl_EM cx W3 ms0 ms0) 20 = w64 SHADOW_OFF)
    by (rewrite (kfl_EM_reg SK B LAWS LV TL TB cx W3 ms0 ms0 20 20%bv eq_refl); exact R20).
  assert (E19 : ew (kfl_EM cx W3 ms0 ms0) 19 = w64 (kF cx fpos))
    by (rewrite (kfl_EM_reg SK B LAWS LV TL TB cx W3 ms0 ms0 19 (Z_to_bv 5 (Z.of_nat 19))
          ltac:(vm_compute; reflexivity));
        exact (Hkrl (19%nat, kF cx fpos) ltac:(cbn [In]; repeat (first [left; reflexivity | right])))).
  assert (E21 : ew (kfl_EM cx W3 ms0 ms0) 21 = w64 (kF cx fpos))
    by (rewrite (kfl_EM_reg SK B LAWS LV TL TB cx W3 ms0 ms0 21 (Z_to_bv 5 (Z.of_nat 21))
          ltac:(vm_compute; reflexivity));
        exact (Hkrl (21%nat, kF cx fpos) ltac:(cbn [In]; repeat (first [left; reflexivity | right])))).
  assert (E22 : ew (kfl_EM cx W3 ms0 ms0) 22 = w64 (kFSH cx fpos))
    by (rewrite (kfl_EM_reg SK B LAWS LV TL TB cx W3 ms0 ms0 22 (Z_to_bv 5 (Z.of_nat 22))
          ltac:(vm_compute; reflexivity));
        exact (Hkrl (22%nat, kFSH cx fpos) ltac:(cbn [In]; repeat (first [left; reflexivity | right])))).
  destruct (kfl_EM_x SK B LAWS LV TL TB cx W3 ms0 ms0) as (E32 & E33 & E256 & EJ).
  change (A_OBJ 15) with 256%nat in E256.
  destruct (EJ 0%nat ltac:(lia)) as (E34 & E37 & E40). clear EJ.
  cbn [Nat.add] in E34, E37, E40. change (Z.of_nat 0) with 0 in E34, E37, E40.
  set (E := kfl_EM cx W3 ms0 ms0) in *.
  assert (U9 : bv_unsigned (ew E 9) = ksp1 cx) by (rewrite E9; apply (kfl_U SK B LAWS LV TL TB); [reflexivity | lia]).
  assert (U18 : bv_unsigned (ew E 18) = ka0 cx) by (rewrite E18; apply (kfl_U SK B LAWS LV TL TB); [reflexivity | lia]).
  assert (U22 : bv_unsigned (ew E 22) = kFSH cx fpos)
    by (rewrite E22; apply (kfl_U SK B LAWS LV TL TB); [reflexivity | lia]).
  assert (HEI : img_env pa_val A_LIM E) by (unfold E, kfl_EM; apply Eimg_env).
  assert (SHOK0 : sh_ok SEGS kfl_Bx [] E (mrestrict (w_H W3) (ms_mem ms0))) by apply Forall_nil.
  pose proof HB as ((_ & HGok & _) & _).
  pose (RUN := paj_run_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  pose (BR := paj_branch (PI := PI)).
  (* run 1: +0x194 .. +0x218, F's right redzone *)
  paj_run_to_tok RUNTO HS HJ SHOK0 kfl_span1 (kpc 0x21c).
  { kfl_wr (kfl_awr SK B LAWS LV TL TB) HC. }
  lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into msA end.
  spregion HS 0%nat HRF.
  assert (HF3 : kfl_f3 cx fpos W3 msA).
  { unfold region_ok in HRF. cbv zeta in HRF. destruct HRF as (_ & _ & _ & Hcs).
    cbn [YP09.r_base YP09.r_chunks base_val] in Hcs. cbn [ew ewset Nat.eqb] in Hcs. rewrite U22 in Hcs.
    intros i Hi. apply (kfl_f3_of _ (w_H W3) (ms_mem msA) _ (kFSH cx fpos) Hcs); [|exact Hi].
    intros j Hj. assert (Hk : exists k, (k < 32)%nat /\ j = 0x428 + Z.of_nat k)
      by (exists (Z.to_nat (j - 0x428)); split; lia).
    destruct Hk as (k & Hk & ->).
    do 32 (destruct k as [|k]; [cbn [In]; repeat (first [left; reflexivity | right]) |]). lia. }
  step_first HC ms0 msA HF3 HMA.
  lazymatch type of HS with st_ok_pi _ _ ?E' ?ss _ =>
    pose proof (st_ok_pi_submem E' ss _ [kfl_rS; kfl_rC] HS ltac:(cbn [ss_mem]; submem_tac)
      ltac:(vm_compute; reflexivity)) as HS1 end.
  clear HS.
  lazymatch type of HS1 with st_ok_pi _ _ ?E' _ _ =>
    assert (SHOK : sh_ok SEGS kfl_Bx kfl_SH E' (mrestrict (w_H W3) (ms_mem msA)))
      by exact (kfl_shok SK B LAWS LV TL TB _ _ _ _ _ _ _ _ _ _ _ E' HMA ltac:(kfl_ew; exact E18)
                  ltac:(kfl_ew; exact E20) ltac:(kfl_ew; exact E256)) end.
  (* run 2: +0x21c .. +0x240 *)
  paj_run_tok RUN HS1 HJ SHOK kfl_span.
  { kfl_wr (kfl_awr SK B LAWS LV TL TB) HC. }
  lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into msB end.
  kfl_step (kfl_mid_step SK B LAWS LV TL TB) HMA msA msB HMB.
  (* +0x244: beqz a6, n = 0 *)
  psrr_branch_tok RUN BR HS1 SHOK kfl_span.
  - (* n = 0: +0x2fc .. +0x308 *)
    paj_run_tok RUN HS1 HJ SHOK kfl_span.
    { kfl_wr (kfl_awr SK B LAWS LV TL TB) HC. }
    lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into msC end.
    kfl_step (kfl_mid_step SK B LAWS LV TL TB) HMB msB msC HMC.
    eapply (kfl_fin SK B LAWS LV TL TB _ _ _ _ _ _ _ _ _ 0 0 105 0);
      [kfl_exit_tac (kfl_exit SK B LAWS LV TL TB) HMC HS1 | lia
      | unfold nl_errno_tab; cbn [In]; repeat (first [left; reflexivity | right]) | lia | lia].
  - (* n > 0: the flags byte at p *)
    lazymatch goal with Hx : branch_taken BC_EQ (sv_denot ?E' (SOff 33 0)) _ = false |- _ =>
      rewrite (kfl_br_eq0 E' 33 (k_wn cx) 0 ltac:(kfl_ew; exact E33) ltac:(lia) ltac:(lia)) in Hx;
      apply Z.eqb_neq in Hx; rewrite Z.add_0_r in Hx; rename Hx into Hwnz
    end.
    paj_run_to_tok RUNTO HS1 HJ SHOK kfl_span (kpc 0x280).
    { kfl_wr (kfl_awr SK B LAWS LV TL TB) HC. }
    lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into msC end.
    kfl_step (kfl_mid_step SK B LAWS LV TL TB) HMB msB msC HMC.
    assert (Hs0 : saddr_ok (k_wp cx + 0) (kfl_s cx W3 ms0 0))
      by exact (proj2 (kfl_sbyte SK B LAWS LV TL TB _ _ _ _ _ _ _ _ _ _ _ 0 HMC ltac:(lia))).
    kfl_setreg HS1 13%nat (SOff 34 0).
    { transitivity (w64 (kfl_q cx 0));
        [apply kfl_d_q; [kfl_ew; exact E32 | kfl_ew; exact E20 | lia | lia | lia]
        | symmetry; apply kfl_d_reg; kfl_ew; exact E34]. }
    lazymatch type of HS1 with st_ok_pi _ _ ?E' ?ss _ =>
      pose proof (st_ok_pi_submem E' ss _ [kfl_rS1; kfl_rCa 1] HS1 ltac:(cbn [ss_mem]; submem_tac)
        ltac:(vm_compute; reflexivity)) as HS2 end.
    clear HS1.
    lazymatch type of HS2 with st_ok_pi _ _ ?E' _ _ =>
      pose proof (kfl_addq SK B LAWS LV TL TB _ _ _ _ _ _ _ _ _ _ _ E' _ _ _ 1 0%nat HMC HS2 ltac:(lia) ltac:(lia)
        ltac:(kfl_ew; exact E9) ltac:(kfl_ew; exact E18) ltac:(kfl_ew; exact E32)
        ltac:(kfl_ew; exact E34) ltac:(kfl_ew; exact E37) ltac:(kfl_ew; exact E40)) as HS end.
    clear HS2.
    paj_run_tok RUN HS HJ SHOK kfl_span.
    { kfl_wr (kfl_awr SK B LAWS LV TL TB) HC. }
    lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into msD end.
    kfl_step (kfl_mid_step SK B LAWS LV TL TB) HMC msC msD HMD.
    (* +0x284: beqz a3, the shadow byte of p *)
    psrr_branch_tok RUN BR HS SHOK kfl_span.
    + paj_run_tok RUN HS HJ SHOK kfl_span.
      { kfl_wr (kfl_awr SK B LAWS LV TL TB) HC. }
      lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into msE end.
      kfl_step (kfl_mid_step SK B LAWS LV TL TB) HMD msD msE HME.
      eapply (kfl_mid1 SK B LAWS LV TL TB).
      unfold kfl_rl1. kfl_exit_tac (kfl_exit SK B LAWS LV TL TB) HME HS.
    + (* s <> 0: the slow path +0x21c8 *)
      lazymatch goal with Hx : branch_taken BC_EQ (sv_denot ?E' (SOff 37 0)) _ = false |- _ =>
        rewrite (kfl_br_eq0 E' 37 (kfl_s cx W3 ms0 0) 0 ltac:(kfl_ew; exact E37)) in Hx;
        [ apply Z.eqb_neq in Hx; rewrite Z.add_0_r in Hx; rename Hx into Hsne
        | unfold saddr_ok in Hs0; lia
        | unfold saddr_ok in Hs0; lia ]
      end.
      paj_run_tok RUN HS HJ SHOK kfl_span.
      { kfl_wr (kfl_awr SK B LAWS LV TL TB) HC. }
      lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into msE end.
      kfl_step (kfl_mid_step SK B LAWS LV TL TB) HMD msD msE HME.
      psrr_branch_tok RUN BR HS SHOK kfl_span.
      * (* p & 7 >= s: the report, which range_addressable excludes *)
        exfalso. unfold saddr_ok in Hs0.
        lazymatch goal with Hx : branch_taken BC_GE (sv_denot ?E' (SAlu ALU_AND (SOff 32 0) _)) _ = true |- _ =>
          rewrite (kfl_br_ge E' 32 37 (k_wp cx) 0 (kfl_s cx W3 ms0 0) ltac:(kfl_ew; exact E32) ltac:(kfl_ew; exact E37))
            in Hx by lia;
          apply negb_true_iff, Z.ltb_ge in Hx
        end.
        lia.
      * paj_run_tok RUN HS HJ SHOK kfl_span.
        { kfl_wr (kfl_awr SK B LAWS LV TL TB) HC. }
        lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into msF end.
        kfl_step (kfl_mid_step SK B LAWS LV TL TB) HME msE msF HMF.
        eapply (kfl_mid1 SK B LAWS LV TL TB).
        unfold kfl_rl1. kfl_exit_tac (kfl_exit SK B LAWS LV TL TB) HMF HS.
Qed.

End b.
End a.

Print Assumptions kn_flags.
