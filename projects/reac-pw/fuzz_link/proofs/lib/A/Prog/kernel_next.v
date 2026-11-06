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
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceOpen.v, with its module paths, module names and numbers changed; 501 of its 581 lines of code are new or changed and 1471 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_link_alias_writeHead.v, with its module names changed; 187 of its 233 lines of code are new or changed and 535 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the walk of kernel (fuzz_link.asan 0x83d30), the phase after a message
   (lib/A/Prog/kernel_defs.v kin_next, +0x1b84) to the message loop's head (kin_loop, +0x63c) or to the message path's
   end (kin_qmsg, +0x1e9c). Listing (internal path) (internal record, sha256 7bc02d6772b3):
     +0x1b84  addiw a4, a4, 1
     +0x1b88  beq   a4, s6, +0x1e9c
     +0x1b8c  j     +0x63c
   a4 = k (the message index) and s6 = m (the messages asked), 0 <= k < m <= 5. The phase reads and writes no memory.

   THE STATE REBUILD. From the cut `kat` at +0x1b84 the symbolic state is rebuilt with LinkPaLib's
   pa_entry_st_ok_full over the environment `Eimg (Ereg (ms_regs ms3) [])` (registers sr_atoms, no region): two
   atom facts (a4 in [0, 4], s6 in [1, 5]) make the engine read `addiw a4, a4, 1` as `SOff 14 1`, and one condition,
   `a4 + 1 = s6` or its negation, decides the `beq`. So the case split k + 1 = m is made on the concrete state
   before the run, and each case is ONE run (LinkWalk paj_run_to_x) to its cut pc.

   THE CUT RE-ESTABLISHED. The run has no region, so its frame_of says every byte is the byte it was: the memory
   at the end IS the memory at the start (functional extensionality), and every memory clause of `kat` (the saved
   words, F, its shadow, the slots, the kept clauses, the cursor, g_nl, long_alias) carries over unchanged
   (`kat_move`). The registers: every register but a4 keeps its atom (regs_kept_of_st_ok_pi), a4 = k + 1.

   Callees: none. Section hypothesis used: LAWS : AR_laws pa_segs B (the lib/A frame; the run instances need it).
   Released proofs (rule 24): none of kernel's walk (lookups/walk-lookups.md (internal record, sha256 98fff7967d93): disposition none, written new; confirmed by
   the rule-24 walk check at 14:56Z).
   Proves no function (kind: segment lemma of kernel's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkNlw.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c kernel_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* membership in a literal list (pairs of a register number and a value, register numbers, registers) *)
Ltac kn_in := cbn [In]; repeat (first [left; reflexivity | left; apply bv_eq; reflexivity | right]).

(* the registers kregs0 names (sp, s1, s0, gp, tp, s2, s4) and the cut registers the phase keeps (s5, s8, s9, s6) *)
Definition nx_keep0 : list (bv 5) := [2%bv; 9%bv; 8%bv; 3%bv; 4%bv; 18%bv; 20%bv].
Definition nx_keepN : list nat := [21; 24; 25; 22]%nat.
Lemma kn_in_map5 : forall (r : nat) l,
  In r l -> In (Z_to_bv 5 (Z.of_nat r)) (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) l).
Proof.
  intros r l H. induction l as [|a l IH]; [cbn [In] in H; destruct H|].
  cbn [map In] in *. destruct H as [<-|H]; [left; reflexivity | right; exact (IH H)].
Qed.

(* the symbolic state at +0x1b84: registers sr_atoms, no region; a4 = atom 14 in [0, 4], s6 = atom 22 in [1, 5], and
   the condition c on (a4 + 1, s6) that decides the beq at +0x1b88 *)
Definition nx_facts (c : branch_cond) : facts :=
  mkFacts [(14%nat, mkAF 0 4 0); (22%nat, mkAF 1 5 0)] [mkAC c (SOff 14 1) (SOff 22 0)] [].
Definition nx_ss (c : branch_cond) : sstate := mkSS (kpc KP_NEXT) sr_atoms [] None (nx_facts c).
Definition nx_Bx : sv := SLit SHADOW_OFF.
Definition nx_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.

(* ---- the cut's machine state, and its registers ---- *)

(* A machine state at a cut is the one `mkst` builds (attr_text.v at_ms_shape). *)
Lemma kn_ms_shape : forall (ms : machine_state) (pc : Z),
  ms_pc_val ms = w64 pc -> ms_resv ms = None -> ms_svc_pending ms = None ->
  ms_rom ms = seg_rom SEGS -> ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr ->
  ms = mkst (ms_regs ms) (Z_to_bv 64 pc) (ms_mem ms) (seg_rom SEGS).
Proof.
  intros [rg fr pcv sv rv fc mm rm] pc H1 H2 H3 H4 H5 H6.
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr] in H1, H2, H3, H4, H5, H6. subst. reflexivity.
Qed.

(* The fixed fields of a cut, off the symbolic state at the end of a run. *)
Lemma kn_kms_of : forall (H : word -> bool) E ss ms pc,
  st_ok_pi SEGS pa_val E ss (restrict H ms) -> ss_resv ss = None -> ss_pc ss = kpc pc -> kms pc ms.
Proof.
  intros H E ss ms pc HS Hrv Hpc.
  pose proof (st_ok_pi_restrict_mkst H E ss ms HS Hrv) as Hsh. rewrite Hpc in Hsh.
  unfold kms. rewrite Hsh. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
  do 5 (split; [reflexivity|]). reflexivity.
Qed.

(* A register a cut names. *)
Lemma kn_reg_in : forall ms rl (r : nat) v,
  kregs_eq ms rl -> In (r, v) rl -> getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat r)) = w64 v.
Proof. intros ms rl r v H Hin. unfold kregs_eq in H. rewrite Forall_forall in H. exact (H (r, v) Hin). Qed.

(* kregs0 holds of a state whose sp, s1, s0, gp, tp, s2, s4 are those of a state where it holds. *)
Lemma kregs0_keep : forall cx ms ms',
  (forall r, In r nx_keep0 -> getr (ms_regs ms') r = getr (ms_regs ms) r) ->
  kregs0 cx ms -> kregs0 cx ms'.
Proof.
  intros cx ms ms' HK (R2 & R9 & R8 & R3 & R4 & R18 & R20). unfold kregs0.
  rewrite !HK by (unfold nx_keep0; kn_in).
  exact (conj R2 (conj R9 (conj R8 (conj R3 (conj R4 (conj R18 R20)))))).
Qed.

(* THE CUT MOVED: a cut holds at a state with another pc and other cut registers when the memory is the same, the
   kept slots are among the cut's, and the model keeps the descriptors and the file system. *)
Lemma kat_move : forall cx fpos pc pc' rl rl' sl sl' sh live adv g k2 ly3 S3 W3 ms3 md3 ms' md',
  kat B cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 ->
  kms pc' ms' -> kregs0 cx ms' -> kregs_eq ms' rl' ->
  ms_mem ms' = ms_mem ms3 -> incl sl' sl ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  kat B cx fpos pc' rl' sl' sh live adv g k2 ly3 S3 W3 ms' md'.
Proof.
  intros cx fpos pc pc' rl rl' sl sl' sh live adv g k2 ly3 S3 W3 ms3 md3 ms' md'
    (_ & _ & _ & HSV & HFRM & HSH & HSL & HJB & HKP & HCU & HGN & HLA) HMS HR0 HRL Hmem Hincl Hfds Hfs.
  unfold kat.
  unfold ksaved, kframe, kshadow, kslots_eq, kjbk, kkept, kcursor, kgnl_at, kla_at in *.
  rewrite Hmem.
  split; [exact HMS|]. split; [exact HR0|]. split; [exact HRL|]. split; [exact HSV|].
  split; [exact HFRM|]. split; [exact HSH|].
  split.
  { rewrite Forall_forall in HSL |- *. intros ov Hov. exact (HSL ov (Hincl ov Hov)). }
  split.
  { destruct HJB as (J1 & J2 & J3 & J4 & J5 & J6 & J7).
    refine (conj J1 (conj J2 (conj J3 (conj J4 (conj J5 (conj _ _)))))).
    - rewrite Hfds. exact J6.
    - rewrite Hfs. exact J7. }
  exact (conj HKP (conj HCU (conj HGN HLA))).
Qed.

(* ---- the phase ---- *)

Lemma kn_next : forall POST (Rc Rm Rm' : kcx -> Z -> Prop),
  (forall cx v, Rm cx v -> 2 <= v -> Rm' cx (v - 1)) ->
  kfrom SK B POST (kin_loop B Rc Rm') -> kfrom SK B POST (kin_qmsg B Rc) -> kfrom SK B POST (kin_next B Rc Rm).
Proof.
  intros POST Rc Rm Rm' HR HLOOP HQ cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ HFR HI.
  destruct HI as (c & ci & j & m & k & n & f & adv & HRc & HRm & Hc & Hci & Hj & Hm & Hk & HW & HAT).
  pose proof HAT as (HMS & HR0 & HRL & _).
  destruct HMS as (Hpc & Hrv & Hsvc & Hrom & Hfr & Hfc).
  pose proof HB as ((_ & HGok & _) & _).
  (* the environment at +0x1b84: the registers, then the image atoms *)
  set (E := Eimg (Ereg (ms_regs ms3) [])).
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (HAG : env_agree 32 (Ereg (ms_regs ms3) []) E)
    by (subst E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (HRG : regs_ok E sr_atoms (ms_regs ms3)) by (subst E; apply regs_ok_Eimg_Ereg).
  assert (U14 : bv_unsigned (ew E 14) = k).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_lt by lia.
    rewrite (kn_reg_in ms3 _ 14 k HRL ltac:(kn_in)). apply unsigned_lit_small. lia. }
  assert (U22 : bv_unsigned (ew E 22) = m).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_lt by lia.
    rewrite (kn_reg_in ms3 _ 22 m HRL ltac:(kn_in)). apply unsigned_lit_small. lia. }
  clearbody E.
  assert (HSHP : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + kpc KP_NEXT)) (ms_mem ms3) (seg_rom SEGS))
    by exact (kn_ms_shape ms3 (BASE + kpc KP_NEXT) Hpc Hrv Hsvc Hrom Hfr Hfc).
  assert (HAT14 : afact_ok E 14 (mkAF 0 4 0)).
  { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U14.
    split; [lia|]. split; [change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
  assert (HAT22 : afact_ok E 22 (mkAF 1 5 0)).
  { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U22.
    split; [lia|]. split; [change (2 ^ 0) with 1; apply Z.mod_1_r | lia]. }
  assert (SHOK : sh_ok SEGS nx_Bx (@nil shent) E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  destruct (Z.eq_dec (k + 1) m) as [Hkm | Hkm].
  - (* k + 1 = m: the beq is taken, +0x1e9c *)
    assert (HS : st_ok_pi SEGS pa_val E (nx_ss BC_EQ) (restrict (w_H W3) ms3)).
    { rewrite HSHP. rewrite restrict_mkst_fx. unfold nx_ss. apply pa_entry_st_ok_full.
      - exact HRG.
      - vm_compute. reflexivity.
      - apply Forall_nil.
      - cbn [pairwise_disjoint all_disjoint]. tauto.
      - unfold facts_ok, nx_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
        split; [exact (conj HAT14 (conj HAT22 I))|]. split; [|exact I]. split; [|exact I].
        unfold acond_ok. cbn [ac_c ac_a ac_b sv_denot branch_taken].
        rewrite U14, U22, Z.add_0_r, Hkm. apply bv_eqb_refl. }
    paj_run_to_tok RUNTO HS HJ SHOK nx_span (kpc KP_QMSG); [apply awr_ok_x_nil|].
    lazymatch goal with
    | HS' : st_ok_pi _ _ _ ?ssx (restrict _ ?msn), HF' : frame_of _ _ (ms_mem ms3) (ms_mem ?msn)
      |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
      assert (Hmem : ms_mem msn = ms_mem ms3)
        by (apply functional_extensionality; intros x; apply HF'; intros Hw;
            destruct Hw as (rr & Hin & _); exact (False_ind _ Hin));
      assert (HMS' : kms KP_QMSG msn)
        by (apply (kn_kms_of _ E ssx msn KP_QMSG HS'); vm_compute; reflexivity);
      assert (HR0' : kregs0 cx msn)
        by (apply (kregs0_keep cx ms3 msn); [|exact HR0];
            exact (regs_kept_of_st_ok_pi E ssx (restrict (w_H W3) msn) (ms_regs ms3) [] nx_keep0 HS' HAG
                     ltac:(vm_compute; reflexivity)));
      assert (HKN : forall r, In r nx_keepN ->
                getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r)))
        by (intros r Hr;
            exact (regs_kept_of_st_ok_pi E ssx (restrict (w_H W3) msn) (ms_regs ms3) []
                     (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) nx_keepN) HS' HAG
                     ltac:(vm_compute; reflexivity) _ (kn_in_map5 r nx_keepN Hr)));
      assert (Hfds : m_fds mdn = m_fds md3) by exact (proj1 (wvb_fds_fs _ _ _));
      assert (Hfs : m_fs mdn = m_fs md3) by exact (proj2 (wvb_fds_fs _ _ _));
      apply (HQ cx fpos k2 ly3 S3 W3 msn mdn HB HJ HFR)
    end.
    exists c, ci, j, n, f, adv.
    split; [exact HRc|]. split; [exact Hc|]. split; [exact Hci|]. split; [exact Hj|].
    split; [unfold kw_at in *; rewrite Hmem; exact HW|].
    refine (kat_move cx fpos KP_NEXT KP_QMSG _ _ _ _ _ _ _ _ k2 ly3 S3 W3 ms3 md3 _ _ HAT HMS' HR0' _ Hmem _
      Hfds Hfs).
    + unfold kregs_eq. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
        (rewrite HKN by (unfold nx_keepN; kn_in)); apply (kn_reg_in ms3 _ _ _ HRL); kn_in.
    + intros x Hx. apply in_app_or in Hx. apply in_or_app. destruct Hx as [Hx|Hx]; [left; exact Hx|].
      right. cbn [In] in Hx |- *. tauto.
  - (* k + 1 <> m: the beq falls through to `j +0x63c` *)
    assert (HS : st_ok_pi SEGS pa_val E (nx_ss BC_NE) (restrict (w_H W3) ms3)).
    { rewrite HSHP. rewrite restrict_mkst_fx. unfold nx_ss. apply pa_entry_st_ok_full.
      - exact HRG.
      - vm_compute. reflexivity.
      - apply Forall_nil.
      - cbn [pairwise_disjoint all_disjoint]. tauto.
      - unfold facts_ok, nx_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
        split; [exact (conj HAT14 (conj HAT22 I))|]. split; [|exact I]. split; [|exact I].
        unfold acond_ok. cbn [ac_c ac_a ac_b sv_denot branch_taken].
        rewrite U14, U22, Z.add_0_r.
        assert (Hne : Z_to_bv 64 (k + 1) <> Z_to_bv 64 m).
        { intros Heq. apply (f_equal bv_unsigned) in Heq.
          rewrite !unsigned_lit_small in Heq by lia. lia. }
        rewrite (bv_eqb_neq _ _ Hne). reflexivity. }
    paj_run_to_tok RUNTO HS HJ SHOK nx_span (kpc KP_LOOP); [apply awr_ok_x_nil|].
    lazymatch goal with
    | HS' : st_ok_pi _ _ _ ?ssx (restrict _ ?msn), HF' : frame_of _ _ (ms_mem ms3) (ms_mem ?msn)
      |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
      assert (Hmem : ms_mem msn = ms_mem ms3)
        by (apply functional_extensionality; intros x; apply HF'; intros Hw;
            destruct Hw as (rr & Hin & _); exact (False_ind _ Hin));
      assert (HMS' : kms KP_LOOP msn)
        by (apply (kn_kms_of _ E ssx msn KP_LOOP HS'); vm_compute; reflexivity);
      assert (HR0' : kregs0 cx msn)
        by (apply (kregs0_keep cx ms3 msn); [|exact HR0];
            exact (regs_kept_of_st_ok_pi E ssx (restrict (w_H W3) msn) (ms_regs ms3) [] nx_keep0 HS' HAG
                     ltac:(vm_compute; reflexivity)));
      assert (HKN : forall r, In r nx_keepN ->
                getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r)))
        by (intros r Hr;
            exact (regs_kept_of_st_ok_pi E ssx (restrict (w_H W3) msn) (ms_regs ms3) []
                     (map (fun q : nat => Z_to_bv 5 (Z.of_nat q)) nx_keepN) HS' HAG
                     ltac:(vm_compute; reflexivity) _ (kn_in_map5 r nx_keepN Hr)));
      (* a4 = k + 1: the engine's `SOff 14 1` *)
      assert (H14 : getr (ms_regs msn) (Z_to_bv 5 (Z.of_nat 14)) = w64 (k + 1))
        by (rewrite (st_ok_pi_restrict_reg (w_H W3) E ssx msn (Z_to_bv 5 (Z.of_nat 14)) HS');
            replace (sr_get (ss_regs ssx) (Z_to_bv 5 (Z.of_nat 14))) with (SOff 14 1) by (vm_compute; reflexivity);
            cbn [sv_denot]; rewrite U14; reflexivity);
      assert (Hfds : m_fds mdn = m_fds md3) by exact (proj1 (wvb_fds_fs _ _ _));
      assert (Hfs : m_fs mdn = m_fs md3) by exact (proj2 (wvb_fds_fs _ _ _));
      apply (HLOOP cx fpos k2 ly3 S3 W3 msn mdn HB HJ HFR)
    end.
    exists c, ci, j, m, (k + 1), n, f, adv.
    split; [exact HRc|].
    split; [replace (m - (k + 1)) with (m - k - 1) by lia; apply HR; [exact HRm | lia]|].
    split; [exact Hc|]. split; [exact Hci|]. split; [exact Hj|]. split; [exact Hm|]. split; [lia|].
    split; [unfold kw_at in *; rewrite Hmem; exact HW|].
    refine (kat_move cx fpos KP_NEXT KP_LOOP _ _ _ _ _ _ _ _ k2 ly3 S3 W3 ms3 md3 _ _ HAT HMS' HR0' _ Hmem
      (incl_refl _) Hfds Hfs).
    unfold kregs_eq. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
    + rewrite HKN by (unfold nx_keepN; kn_in). apply (kn_reg_in ms3 _ _ _ HRL). kn_in.
    + rewrite HKN by (unfold nx_keepN; kn_in). apply (kn_reg_in ms3 _ _ _ HRL). kn_in.
    + rewrite HKN by (unfold nx_keepN; kn_in). apply (kn_reg_in ms3 _ _ _ HRL). kn_in.
    + exact H14.
    + rewrite HKN by (unfold nx_keepN; kn_in). apply (kn_reg_in ms3 _ _ _ HRL). kn_in.
Qed.

End b.
End a.
