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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_writeHead.v; 137 of its 179 lines of code are new or changed and 611 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: kernel's phase +0x194 -> +0x3b4, part 1: from +0x290 (the `beqz a5`
   after the flags byte; a3 = flags = d[0], a5 = n - 1, a6 = n, the cursor advanced by 1) to +0x3b4 (n = 1) or to
   +0x324 (n >= 2, kernel_flags_s2.v).
   - n = 1: +0x30c the check of s8, a0 := slot 0xb0 = a0 + 8, a6 := [a0 + 8] = 0, a0 := 0, the `lw` of
     nl_errno.e[0] = 105, +0x344 `beqz a6` taken (the engine decides it from the branch's condition), a0 := 0;
   - n >= 2: the cursor's two checks, [a0 + 8] := n - 2, [a0] := p + 2, the check of the input byte at p + 1
     (+0x2c8; its slow path +0x21fc, refuted when taken), `lbu` d[1], a0 := d[1] % 6 (+0x2d8 .. +0x2f4).
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_flags_base kernel_flags_s3 kernel_flags_s2.
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

(* +0x290's own registers: a3 = d[0], a5 = n - 1, a6 = n, a4 = shadow(a0) *)
Definition kfl_rl1 (cx : kcx) : list (nat * Z) :=
  [(13%nat, kfl_d cx 0); (15%nat, k_wn cx - 1); (16%nat, k_wn cx); (14%nat, kfl_a4 cx)].

Local Ltac ew_at HA r := exact (kfl_at_ew SK B LAWS LV TL TB _ _ _ _ _ _ _ _ _ _ _ _ _ _ r _ HA
  ltac:(unfold kfl_rl1; kfl_inl) ltac:(vm_compute; reflexivity)).

Lemma kfl_mid1 : forall POST cx fpos k2 ly3 S3 W3 ms0 md0 ms md,
  kfl_at SK B POST cx fpos k2 ly3 S3 W3 ms0 md0 0x290 1 (kfl_rl1 cx) ms md ->
  SRr SEGS W3 (mkCfg ms md) (POST cx).
Proof.
  intros POST cx fpos k2 ly3 S3 W3 ms0 md0 ms md HA.
  pose proof HA as (HM & _ & _ & _ & _ & Hadv & _).
  pose proof (proj1 HM) as HC.
  pose proof (kfl_nums SK B LAWS LV TL TB _ _ _ _ _ _ _ _ _ HC) as (Hsp & Hsp47 & Hs1a & Hs1b & Hs1m & Hwlo & Hwhi &
    HF4 & HFc & HF64 & HFSH & Ha0 & Ha0r & Hapf & Hwp0 & Hwpn & Hwn0 & HFapp & HFa0).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  rewrite C3, C5 in Ha0r.
  assert (Ha47 : 0 <= ka0 cx < 2 ^ 47) by lia.
  assert (HK : KERNEL_AK = 4640) by reflexivity.
  assert (Hd0 : 0 <= kfl_d cx 0 < 256)
    by exact (proj2 (kfl_dbyte SK B LAWS LV TL TB _ _ _ _ _ _ _ _ _ _ _ 0 HM ltac:(lia))).
  assert (Hd1 : 1 < k_wn cx -> 0 <= kfl_d cx 1 < 256)
    by (intros H1; exact (proj2 (kfl_dbyte SK B LAWS LV TL TB _ _ _ _ _ _ _ _ _ _ _ 1 HM ltac:(lia)))).
  assert (Hs1 : 1 < k_wn cx -> saddr_ok (k_wp cx + 1) (kfl_s cx W3 ms0 1))
    by (intros H1; exact (proj2 (kfl_sbyte SK B LAWS LV TL TB _ _ _ _ _ _ _ _ _ _ _ 1 HM ltac:(lia)))).
  pose proof (kfl_build SK B LAWS LV TL TB _ _ _ _ _ _ _ _ _ _ _ _ _ _ true HA) as HS.
  pose proof (kfl_at_gp SK B LAWS LV TL TB _ _ _ _ _ _ _ _ _ _ _ _ _ _ HA) as (E3 & E4).
  destruct (kfl_EM_x SK B LAWS LV TL TB cx W3 ms0 ms) as (E32 & E33 & E256 & EJ).
  change (A_OBJ 15) with 256%nat in E256.
  destruct (EJ 1%nat ltac:(lia)) as (E35 & E38 & E41). clear EJ.
  cbn [Nat.add] in E35, E38, E41. change (Z.of_nat 1) with 1 in E35, E38, E41.
  assert (E2 : ew (kfl_EM cx W3 ms0 ms) 2 = w64 (ksp1 cx)) by ew_at HA 2%nat.
  assert (E9 : ew (kfl_EM cx W3 ms0 ms) 9 = w64 (ksp1 cx)) by ew_at HA 9%nat.
  assert (E8 : ew (kfl_EM cx W3 ms0 ms) 8 = w64 (ksp cx)) by ew_at HA 8%nat.
  assert (E18 : ew (kfl_EM cx W3 ms0 ms) 18 = w64 (ka0 cx)) by ew_at HA 18%nat.
  assert (E20 : ew (kfl_EM cx W3 ms0 ms) 20 = w64 SHADOW_OFF) by ew_at HA 20%nat.
  assert (E19 : ew (kfl_EM cx W3 ms0 ms) 19 = w64 (kF cx fpos)) by ew_at HA 19%nat.
  assert (E21 : ew (kfl_EM cx W3 ms0 ms) 21 = w64 (kF cx fpos)) by ew_at HA 21%nat.
  assert (E22 : ew (kfl_EM cx W3 ms0 ms) 22 = w64 (kFSH cx fpos)) by ew_at HA 22%nat.
  assert (E24 : ew (kfl_EM cx W3 ms0 ms) 24 = w64 (kS8 cx)) by ew_at HA 24%nat.
  assert (E11 : ew (kfl_EM cx W3 ms0 ms) 11 = w64 (ka0 cx / 8)) by ew_at HA 11%nat.
  assert (E12 : ew (kfl_EM cx W3 ms0 ms) 12 = w64 LA_NL_ERRNO_E) by ew_at HA 12%nat.
  assert (E13 : ew (kfl_EM cx W3 ms0 ms) 13 = w64 (kfl_d cx 0)) by ew_at HA 13%nat.
  assert (E15 : ew (kfl_EM cx W3 ms0 ms) 15 = w64 (k_wn cx - 1)) by ew_at HA 15%nat.
  assert (E16 : ew (kfl_EM cx W3 ms0 ms) 16 = w64 (k_wn cx)) by ew_at HA 16%nat.
  assert (E14 : ew (kfl_EM cx W3 ms0 ms) 14 = w64 (kfl_a4 cx)) by ew_at HA 14%nat.
  set (E := kfl_EM cx W3 ms0 ms) in *.
  assert (U9 : bv_unsigned (ew E 9) = ksp1 cx) by (rewrite E9; apply (kfl_U SK B LAWS LV TL TB); [reflexivity | lia]).
  assert (U18 : bv_unsigned (ew E 18) = ka0 cx) by (rewrite E18; apply (kfl_U SK B LAWS LV TL TB); [reflexivity | lia]).
  assert (HEI : img_env pa_val A_LIM E) by (unfold E, kfl_EM; apply Eimg_env).
  (* s8, a5, a6, a4, a2 in the engine's forms *)
  kfl_setreg HS 24%nat (kfl_e_sh 18 8).
  { rewrite (kfl_d_reg E 24 _ E24). symmetry. exact (kfl_d_s8 E cx E18 E20 Ha47). }
  kfl_setreg HS 15%nat (SOff 33 (-1)).
  { rewrite (kfl_d_reg E 15 _ E15). symmetry. eapply kfl_d_off; [exact E33 | lia | lia]. }
  kfl_setreg HS 16%nat (SOff 33 0).
  { rewrite (kfl_d_reg E 16 _ E16). symmetry. apply kfl_d_reg. exact E33. }
  kfl_setreg HS 14%nat (kfl_e_sh 18 0).
  { rewrite (kfl_d_reg E 14 _ E14). symmetry. exact (kfl_d_a4 E cx E18 E20 Ha47). }
  kfl_setreg HS 12%nat (SOff 256 0).
  { rewrite (kfl_d_reg E 12 _ E12). symmetry. apply kfl_d_reg. exact E256. }
  assert (SHOK : sh_ok SEGS kfl_Bx kfl_SH E (mrestrict (w_H W3) (ms_mem ms)))
    by exact (kfl_shok SK B LAWS LV TL TB _ _ _ _ _ _ _ _ _ _ _ E HM E18 E20 E256).
  pose proof (proj1 (proj2 HM)) as HJ.
  pose proof HC as (HB & _). pose proof HB as ((_ & HGok & _) & _).
  pose (RUN := paj_run_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  pose (BR := paj_branch (PI := PI)).
  (* +0x290: beqz a5 *)
  psrr_branch_tok RUN BR HS SHOK kfl_span.
  - (* n = 1 *)
    paj_run_tok RUN HS HJ SHOK kfl_span.
    { kfl_wr (kfl_awr SK B LAWS LV TL TB) HC. }
    lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into msA end.
    kfl_step (kfl_mid_step SK B LAWS LV TL TB) HM ms msA HMA.
    eapply (kfl_fin SK B LAWS LV TL TB _ _ _ _ _ _ _ _ _ 1 (kfl_d cx 0) 105 0);
      [kfl_exit_tac (kfl_exit SK B LAWS LV TL TB) HMA HS | lia
      | unfold nl_errno_tab; cbn [In]; repeat (first [left; reflexivity | right]) | lia | lia].
  - (* n >= 2: the e-index byte at p + 1 *)
    rewrite (kfl_br_eq0 E 33 (k_wn cx) (-1) E33 ltac:(lia) ltac:(lia)) in Hc. apply Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK kfl_span (kpc 0x2c8).
    { kfl_wr (kfl_awr SK B LAWS LV TL TB) HC. }
    lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into msA end.
    kfl_step (kfl_mid_step SK B LAWS LV TL TB) HM ms msA HMA.
    kfl_setreg HS 15%nat (SOff 35 0).
    { transitivity (w64 (kfl_q cx 1));
        [apply kfl_d_q; [kfl_ew; exact E32 | kfl_ew; exact E20 | lia | lia | lia]
        | symmetry; apply kfl_d_reg; kfl_ew; exact E35]. }
    lazymatch type of HS with st_ok_pi _ _ ?E' ?ss _ =>
      pose proof (st_ok_pi_submem E' ss _ [kfl_rS1; kfl_rCa 2] HS ltac:(cbn [ss_mem]; submem_tac)
        ltac:(vm_compute; reflexivity)) as HS2 end.
    clear HS.
    lazymatch type of HS2 with st_ok_pi _ _ ?E' _ _ =>
      pose proof (kfl_addq SK B LAWS LV TL TB _ _ _ _ _ _ _ _ _ _ _ E' _ _ _ 2 1%nat HMA HS2 ltac:(lia) ltac:(lia)
        ltac:(kfl_ew; exact E9) ltac:(kfl_ew; exact E18) ltac:(kfl_ew; exact E32)
        ltac:(kfl_ew; exact E35) ltac:(kfl_ew; exact E38) ltac:(kfl_ew; exact E41)) as HS end.
    clear HS2.
    paj_run_tok RUN HS HJ SHOK kfl_span.
    { kfl_wr (kfl_awr SK B LAWS LV TL TB) HC. }
    lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into msB end.
    kfl_step (kfl_mid_step SK B LAWS LV TL TB) HMA msA msB HMB.
    pose proof (Hd1 ltac:(lia)) as Hd1'.
    (* +0x2cc: beqz a5, the shadow byte of p + 1 *)
    psrr_branch_tok RUN BR HS SHOK kfl_span.
    + paj_run_to_tok RUNTO HS HJ SHOK kfl_span (kpc 0x324).
      { kfl_wr (kfl_awr SK B LAWS LV TL TB) HC. }
      lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into msC end.
      kfl_step (kfl_mid_step SK B LAWS LV TL TB) HMB msB msC HMC.
      eapply (kfl_mid2 SK B LAWS LV TL TB _ _ _ _ _ _ _ _ _ (kfl_d cx 1 mod 6) (kfl_d cx 0));
        [unfold kfl_rl2; kfl_exit_tac (kfl_exit SK B LAWS LV TL TB) HMC HS | lia | lia | lia].
    + (* s <> 0: the slow path +0x21fc *)
      lazymatch goal with Hx : branch_taken BC_EQ (sv_denot ?E' (SOff 38 0)) _ = false |- _ =>
        rewrite (kfl_br_eq0 E' 38 (kfl_s cx W3 ms0 1) 0 ltac:(kfl_ew; exact E38)) in Hx;
        [ apply Z.eqb_neq in Hx; rewrite Z.add_0_r in Hx; rename Hx into Hsne
        | unfold saddr_ok in Hs1; specialize (Hs1 ltac:(lia)); lia
        | unfold saddr_ok in Hs1; specialize (Hs1 ltac:(lia)); lia ]
      end.
      paj_run_tok RUN HS HJ SHOK kfl_span.
      { kfl_wr (kfl_awr SK B LAWS LV TL TB) HC. }
      lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into msC end.
      kfl_step (kfl_mid_step SK B LAWS LV TL TB) HMB msB msC HMC.
      psrr_branch_tok RUN BR HS SHOK kfl_span.
      * (* (p + 1) & 7 >= s: the report, which range_addressable excludes *)
        exfalso. specialize (Hs1 ltac:(lia)). unfold saddr_ok in Hs1.
        lazymatch goal with Hx : branch_taken BC_GE (sv_denot ?E' (SAlu ALU_AND (SOff 32 1) _)) _ = true |- _ =>
          rewrite (kfl_br_ge E' 32 38 (k_wp cx) 1 (kfl_s cx W3 ms0 1) ltac:(kfl_ew; exact E32) ltac:(kfl_ew; exact E38))
            in Hx by lia;
          apply negb_true_iff, Z.ltb_ge in Hx
        end.
        lia.
      * paj_run_to_tok RUNTO HS HJ SHOK kfl_span (kpc 0x324).
        { kfl_wr (kfl_awr SK B LAWS LV TL TB) HC. }
        lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into msD end.
        kfl_step (kfl_mid_step SK B LAWS LV TL TB) HMC msC msD HMD.
        eapply (kfl_mid2 SK B LAWS LV TL TB _ _ _ _ _ _ _ _ _ (kfl_d cx 1 mod 6) (kfl_d cx 0));
          [unfold kfl_rl2; kfl_exit_tac (kfl_exit SK B LAWS LV TL TB) HMD HS | lia | lia | lia].
Qed.

End b.
End a.
