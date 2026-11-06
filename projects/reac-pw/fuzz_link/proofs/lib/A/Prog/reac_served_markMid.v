(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v, with its module paths and module names changed; 1412 of its 1477 lines of code are new or changed and 1240 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_link_alias_writeSend.v, with its module names changed; 469 of its 528 lines of code are new or changed and 1418 lines of the source are left out. *)
(* reac_served_mark (fuzz_link.asan 0x895a8) on image A, the MID segment: from the MID cut (+0x1b4, `beqz s6`) to
   the EXIT cut (the three refusals, s5 = - E_INVAL) and to the RRET cut (+0x284, after reac_link_alias_read).
   Cuts and obligations: lib/A/Prog/reac_served_markDefs.v; the semantic halves: reac_served_markMidRef.v (the
   refusals, the base across a run that writes nothing) and reac_served_markMidCall.v (the call).

   The run, in three symbolic phases (each started from the cut base by `srm_mid_st`):
     A  +0x1b4 .. : `beqz s6` and `beqz s4` decided by two conditions on the entry state, then to the EXIT cut
        (+0x360) or to +0x1bc (token run, no region);
     B  +0x1bc .. +0x1d0 : the instrumented check of name[0] (a shadow entry of 1 byte on s4) and `lbu a0, 0(s4)`
        (a read-only region of 1 byte); `beqz a0` decided by a condition, then to the EXIT cut or to +0x1d4;
     C  +0x1d4 .. +0x280 : s8 := F + 0x20, s7 := F + 0x60, F's shadow SH + 4 .. SH + 43 := 0 (a writable region
        on s2), the arguments, `jal reac_link_alias_read` (plain run, stops at the callee's entry).
   The callee is applied at the walk's fx (`aleaf_rd`) under SRr_bind; its return is the RRET cut.

   Proves no function (kind: segment lemma of reac_served_mark's walk). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalkSide PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkPi LinkWalkZsh.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c nl_talk_c reac_link_alias_read_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
reac_served_markDefs reac_served_markKit reac_served_markKitAt reac_served_markMidRef reac_served_markMidCall.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   The symbolic states (closed)
   ========================================================================== *)
Definition SRM_PC_B : Z := AF_reac_served_mark + 0x1bc.    (* `srli a0, s4, 3`: the check of name[0] *)
Definition SRM_PC_C : Z := AF_reac_served_mark + 0x1d4.    (* `addi s8, s9, 0x20` *)
Definition srm_mBx : sv := SOff 26 0.                      (* s10, the shadow base *)
Definition srm_mspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition srm_ssA : sstate := mkSS SRM_CUT_MID sr_atoms [] None (mkFacts [] [] []).
(* name[0] is the extra atom 32 *)
Definition srm_nameR : YP09.region := YP09.mkRegion (Some 20%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition srm_SHB : list shent := [mkSHE 20 0 1].
Definition srm_ssB : sstate := mkSS SRM_PC_B sr_atoms [srm_nameR] None
  (mkFacts [(26%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (20%nat, mkAF 0 (2 ^ 47 - 1) 0); (32%nat, mkAF 0 255 0)] [] []).
(* F's 64 shadow bytes on s2, the buffers' 40 writable *)
Definition srm_shR : YP09.region := YP09.mkRegion (Some 18%nat) 0 64 4 44 [].
Definition srm_ssC : sstate := mkSS SRM_PC_C sr_atoms [srm_shR] None (mkFacts [] [] []).

(* a chunk list holds the zero byte at offset i *)
Definition srm_mid_zc (cs : list YP09.chunk) (i : Z) : bool :=
  existsb (fun c => (YP09.c_off c =? i) &&
    match YP09.c_val c with CVal w (SLit z) => (w =? 1)%N && (z =? 0) | _ => false end) cs.

Lemma srm_mid_zc_spec : forall cs i, srm_mid_zc cs i = true -> In (YP09.mkChunk i (CVal 1 (SLit 0))) cs.
Proof.
  intros cs i H. unfold srm_mid_zc in H. apply existsb_exists in H as ([off v] & Hin & Hc).
  cbn [YP09.c_off YP09.c_val] in Hc. apply andb_true_iff in Hc as [Ho Hv]. apply Z.eqb_eq in Ho. subst off.
  destruct v as [w e | | |]; try discriminate. destruct e; try discriminate.
  apply andb_true_iff in Hv as [Hw Hz]. apply N.eqb_eq in Hw. apply Z.eqb_eq in Hz. subst. exact Hin.
Qed.

(* every offset of the buffers' shadow holds the zero byte *)
Definition srm_mid_zall (cs : list YP09.chunk) : bool :=
  forallb (srm_mid_zc cs) (map Z.of_nat (seq 4 4) ++ map Z.of_nat (seq 12 32)).

Lemma srm_mid_zall_spec : forall cs i, srm_mid_zall cs = true -> srm_bufsh_off i ->
  In (YP09.mkChunk i (CVal 1 (SLit 0))) cs.
Proof.
  intros cs i H Hi. apply srm_mid_zc_spec. unfold srm_mid_zall in H. rewrite forallb_forall in H. apply H.
  apply in_or_app. unfold srm_bufsh_off in Hi.
  destruct Hi as [Hi | Hi]; [left | right]; replace i with (Z.of_nat (Z.to_nat i)) by lia;
    apply in_map; apply in_seq; lia.
Qed.

Section g.
Variable segs : list Segment.

(* a run whose regions have no writable window leaves the memory as it was *)
Lemma srm_mid_frame_ro : forall E rs (m m' : word -> option byte),
  frame_of E rs m m' -> (forall r, In r rs -> YP09.r_whi r <= YP09.r_wlo r) -> m' = m.
Proof.
  intros E rs m m' Hfr Hro. apply functional_extensionality. intros x. apply Hfr.
  intros (r & Hin & Hr). pose proof (Hro r Hin). lia.
Qed.

Lemma srm_mid_chunk_zero : forall E m base off,
  YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal 1 (SLit 0))) -> mbyte segs m (base + off) = Some (Z_to_bv 8 0).
Proof.
  intros E m base off Hc. destruct (Hc 0 ltac:(cbn; lia)) as (b & Hb & Hm).
  cbn [YP09.c_off YP09.c_val cbyte] in Hb, Hm. rewrite Z.add_0_r in Hm. rewrite Hm, <- Hb.
  all: try (f_equal; apply bv_eq; vm_compute; reflexivity).
Qed.

Lemma srm_mid_val_mem1 : forall (m : word -> option byte) a b,
  mbyte segs m a = Some b -> val_mem segs m a 1 (bv_unsigned b).
Proof.
  intros m a b H k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r, H.
  assert (L : le_byte (bv_unsigned b) 1 0 = bv_unsigned b).
  { unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
    pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with (2 ^ 8) in R.
    rewrite !Z.mod_small by lia. reflexivity. }
  transitivity (Some (Z_to_bv 8 (bv_unsigned b))); [rewrite Z_to_bv_bv_unsigned; reflexivity|].
  f_equal. f_equal. symmetry. exact L.
Qed.
End g.

(* ==========================================================================
   The runs: the token run (to a stop pc, or to its first undecided branch) and the plain run (to a stop pc,
   or to a call), each leaving the write-window goal and then the continuation
   ========================================================================== *)
Ltac srm_tok RUN HS HJ SHOK Bspan :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
    lazymatch type of SHOK with
    | sh_ok _ ?Bx ?SH _ _ =>
      lazymatch paj_tables RUN with (?tpi, ?tw) =>
        let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
        let r := eval vm_compute in (sym_runN_pi_tok tpi tw K Bx Bspan SH FUEL ss) in
        lazymatch r with
        | (?st', ?rs) =>
          let Hrun := fresh "Hrun" in
          assert (Hrun : sym_runN_pi_tok tpi tw K Bx Bspan SH FUEL ss = (st', rs)) by (vm_compute; reflexivity);
          let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI end in
          eapply (RUN W FUEL E K Bx Bspan SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _
                    ltac:(unfold A_LIM; cbn; lia) HEI HS SHOK ltac:(vm_compute; reflexivity) Hrun HJ);
          [ clear Hrun; cbn [sh_obls]; srr_obls | clear Hrun | clear Hrun ]
        end
      end
    end
  end.

Ltac srm_tok_to RUNTO HS HJ SHOK Bspan stop :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
    lazymatch type of SHOK with
    | sh_ok _ ?Bx ?SH _ _ =>
      lazymatch paj_tables RUNTO with (?tpi, ?tw) =>
        let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
        let r := eval vm_compute in (sym_run_toN_pi_tok tpi tw K Bx Bspan SH FUEL stop ss) in
        lazymatch r with
        | (?st', ?rs) =>
          let Hrun := fresh "Hrun" in
          assert (Hrun : sym_run_toN_pi_tok tpi tw K Bx Bspan SH FUEL stop ss = (st', rs)) by (vm_compute; reflexivity);
          let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI end in
          eapply (RUNTO W FUEL stop E K Bx Bspan SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _
                    ltac:(unfold A_LIM; cbn; lia) HEI HS SHOK ltac:(vm_compute; reflexivity) Hrun HJ);
          [ clear Hrun; cbn [sh_obls]; srr_obls | clear Hrun | clear Hrun ]
        end
      end
    end
  end.

Ltac srm_plain_to RUNP HS HJ stop :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
    let tpi := lazymatch type of RUNP with context [sym_run_toN_pi ?t _ _ _] => t end in
    let r := eval vm_compute in (sym_run_toN_pi tpi FUEL stop ss) in
    lazymatch r with
    | (?ss', ?st) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : sym_run_toN_pi tpi FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
      let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI end in
      eapply (RUNP W FUEL stop E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun I HJ); clear Hrun
    end
  end.

Ltac srm_plain_call RUNC HS HJ :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
    let tpi := lazymatch type of RUNC with context [sym_runN_pi ?t _ _] => t end in
    let r := eval vm_compute in (sym_runN_pi tpi FUEL ss) in
    lazymatch r with
    | (?ss', PRS_call ?s) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : sym_runN_pi tpi FUEL ss = (ss', PRS_call s)) by (vm_compute; reflexivity);
      let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI end in
      eapply (RUNC W FUEL E ss ss' s ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun HJ); clear Hrun
    end
  end.

(* the regions of a state have no writable window *)
Ltac srm_ro := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; vm_compute in Hr;
  repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_whi YP09.r_wlo]; lia|]); destruct Hr.

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
Hypothesis TB : PcapSyms B.
Hypothesis RELRO_IMG : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.
Hypothesis HSEGS : SEGS = tfibsegs.
Hypothesis HV : LinkVals.
(* reac_link_alias_read (0x8867c), reac_link_alias_read_aproof *)
Hypothesis HRD : forall fx' : YK11.FPState, @reac_link_alias_read_acontract fx' rc SK SEGS PCAP_RLO PCAP_RHI B.

Lemma srm_mid_ms_eta : forall ms : machine_state,
  ms_fregs ms = fp_regs -> ms_svc_pending ms = None -> ms_resv ms = None -> ms_fcsr ms = fp_csr ->
  ms = mkst (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (ms_rom ms).
Proof using LAWS TB RELRO_IMG HSEGS HV HRD.
  intros [] H1 H2 H3 H4; cbn in *; subst; reflexivity.
Qed.

(* a symbolic state at a cut, over the cut's registers (atoms 0 .. 31) *)
Lemma srm_mid_st : forall (W : world SEGS) (ms : machine_state) pc E rs G,
  ms_resv ms = None -> ms_svc_pending ms = None -> ms_rom ms = seg_rom SEGS ->
  ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr -> ms_pc_val ms = w64 (BASE + pc) ->
  regs_ok E sr_atoms (ms_regs ms) ->
  regions_wf rs = true -> Forall (region_ok SEGS E (rdW W (ms_mem ms))) rs -> pairwise_disjoint E rs ->
  facts_ok E G ->
  st_ok_pi SEGS VAL E (mkSS pc sr_atoms rs None G) (restrict (w_H W) ms).
Proof using LAWS TB RELRO_IMG HSEGS HV HRD.
  intros W ms pc E rs G H1 H2 H3 H4 H5 Hpc Hr Hwf Hrs Hpd HG.
  rewrite (srm_mid_ms_eta ms H4 H2 H1 H5), Hpc, H3, restrict_mkst_fx.
  apply pa_entry_st_ok_full; assumption.
Qed.

(* the base and s5 at a later state of a run that wrote nothing and kept the base registers *)
Lemma srm_mid_move_of : forall cx fpos ly3 S3 W3 (ms ms' : machine_state) md md' E' ss' extra,
  srm_base fx SK B cx fpos srm_X0 ly3 S3 W3 ms md ->
  st_ok_pi SEGS VAL E' ss' (restrict (w_H W3) ms') -> ss_resv ss' = None ->
  env_agree 32 (Ereg (ms_regs ms) extra) E' ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss') r) (SOff (Z.to_nat (bv_unsigned r)) 0)) srm_mid_rlist = true ->
  ms_mem ms' = ms_mem ms ->
  ajournal_gx SEGS B (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx) (sm_FP cx)
    (sm_ly cx) (sm_S cx) (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) ((SRM_CID, fpos) :: sm_own cx)
    ly3 S3 W3 (ms_mem ms') md' (sm_k cx) ->
  m_fds md' = m_fds md -> m_fs md' = m_fs md ->
  srm_base fx SK B cx fpos srm_X0 ly3 S3 W3 ms' md' /\ srm_mid_regs_same (ms_regs ms) (ms_regs ms') /\
  ms_pc_val ms' = w64 (BASE + ss_pc ss').
Proof using LAWS TB RELRO_IMG HSEGS HV HRD.
  intros cx fpos ly3 S3 W3 ms ms' md md' E' ss' extra HB HS Hrv HA Hl Hmem HJ Hfds Hfs.
  pose proof (st_ok_pi_restrict_mkst (w_H W3) E' ss' ms' HS Hrv) as Hms.
  pose proof (srm_mid_regs_same_of SK B LAWS TB RELRO_IMG HSEGS E' ss' ms ms' extra (w_H W3) HS HA Hl) as HRS.
  split; [|split; [exact HRS | rewrite Hms; reflexivity]].
  apply (srm_mid_base_move SK B LAWS TB RELRO_IMG HSEGS cx fpos srm_X0 srm_X0 ly3 S3 W3 ms ms' md md' HB
           (fun a H => H)); try (rewrite Hms; reflexivity); assumption.
Qed.

(* the EXIT cut after a refusal *)
Lemma srm_mid_exit_of : forall cx fpos ly3 S3 W3 (ms ms' : machine_state) md md' E' ss' extra,
  srm_pre SK B cx -> srm_base fx SK B cx fpos srm_X0 ly3 S3 W3 ms md -> getr (ms_regs ms) 21 = w64 (-22) ->
  (srm_mk cx = 0 \/ srm_name cx = 0 \/ aview SEGS (w_H W3) (ms_mem ms) (srm_name cx) = Some 0) ->
  st_ok_pi SEGS VAL E' ss' (restrict (w_H W3) ms') -> ss_resv ss' = None -> ss_pc ss' = SRM_CUT_EXIT ->
  env_agree 32 (Ereg (ms_regs ms) extra) E' ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss') r) (SOff (Z.to_nat (bv_unsigned r)) 0)) srm_mid_rlist = true ->
  ms_mem ms' = ms_mem ms ->
  ajournal_gx SEGS B (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx) (sm_FP cx)
    (sm_ly cx) (sm_S cx) (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) ((SRM_CID, fpos) :: sm_own cx)
    ly3 S3 W3 (ms_mem ms') md' (sm_k cx) ->
  m_fds md' = m_fds md -> m_fs md' = m_fs md ->
  exists rcv, ms_pc_val ms' = w64 (BASE + SRM_CUT_EXIT) /\ getr (ms_regs ms') 21 = w64 rcv /\
    srm_pf cx rcv (rdW W3 (ms_mem ms')) /\ srm_base fx SK B cx fpos (srm_E cx) ly3 S3 W3 ms' md'.
Proof using LAWS TB RELRO_IMG HSEGS HV HRD.
  intros cx fpos ly3 S3 W3 ms ms' md md' E' ss' extra HPRE HB H21 Hcase HS Hrv Hpc HA Hl Hmem HJ Hfds Hfs.
  pose proof (st_ok_pi_restrict_mkst (w_H W3) E' ss' ms' HS Hrv) as Hms. rewrite Hpc in Hms.
  pose proof (srm_mid_regs_same_of SK B LAWS TB RELRO_IMG HSEGS E' ss' ms ms' extra (w_H W3) HS HA Hl) as HRS.
  pose proof HRS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q21).
  exists (- E_INVAL). split; [rewrite Hms; reflexivity|]. split; [rewrite Q21, H21; reflexivity|].
  split; [rewrite Hmem; exact (srm_mid_refuse SK B LAWS TB RELRO_IMG HSEGS cx fpos ly3 S3 W3 ms md HPRE HB Hcase)|].
  apply (srm_mid_base_move SK B LAWS TB RELRO_IMG HSEGS cx fpos srm_X0 (srm_E cx) ly3 S3 W3 ms ms' md md' HB
           (fun a (H : srm_X0 a) => False_ind (srm_E cx a) H)); try (rewrite Hms; reflexivity); assumption.
Qed.

Lemma srm_mid_wvb2 : forall l1 X1 l2 X2 m,
  m_fds (with_vm_backing l1 X1 (with_vm_backing l2 X2 m)) = m_fds m /\
  m_fs (with_vm_backing l1 X1 (with_vm_backing l2 X2 m)) = m_fs m.
Proof using LAWS TB RELRO_IMG HSEGS HV HRD.
  intros l1 X1 l2 X2 m. destruct (wvb_fds_fs l1 X1 (with_vm_backing l2 X2 m)) as [A1 A2].
  destruct (wvb_fds_fs l2 X2 m) as [B1 B2]. split; congruence.
Qed.

(* ==========================================================================
   THE MID SEGMENT
   ========================================================================== *)
Theorem srm_mid : srm_exit_obl fx SK B -> srm_rret_obl fx SK B -> srm_mid_obl fx SK B.
Proof using LAWS TB RELRO_IMG HSEGS HV HRD.
intros HEXIT HRRET cx fpos ly3 S3 W3 ms3 md3 HPRE HGS (Hpc & R21 & HB).
pose proof HPRE as ((HJc & HGok & _) & _ & HP).
destruct HP as (kbs & tab & nm & k0 & Hsink & Hledg & HNLK & _ & _ & _ & _ & _ & _ & _ & HMF & Hk0 & _ & Hnm & _ & Hblk).
pose proof HB as (Hresv & Hsvc & Hrom & Hfrg & Hfcsr & HJ & _ & _ & _ & _ & _ & R2 & R9 & R8 & R18 & R19 & R25
  & R26 & R20 & R22 & R3 & R4 & R27 & _).
pose (RUN := paj_run_x SK B LAWS (sm_G cx) HGok (sm_XO cx) (sm_OUT cx)).
pose (RUNTO := paj_run_to_x SK B LAWS (sm_G cx) HGok (sm_XO cx) (sm_OUT cx)).
pose (RUNP := paj_run_to_plain_x SK B LAWS (sm_G cx) HGok (sm_XO cx) (sm_OUT cx)).
pose (RUNC := paj_run_call_plain_x SK B LAWS (sm_G cx) HGok (sm_XO cx) (sm_OUT cx)).
pose (BR := paj_branch (PI := PI)).
assert (HX0 : forall a, srm_X0 a -> srm_E cx a) by (intros a []).
assert (HKc : 0 <= REAC_LINK_ALIAS_READ_AK <= REAC_CODE_EMIT_AK)
  by (change REAC_LINK_ALIAS_READ_AK with 8592; change REAC_CODE_EMIT_AK with 9360; lia).
assert (Hmkr : 0 <= srm_mk cx < 2 ^ 64).
{ unfold srm_mk, aarg, argZ. pose proof (bv_unsigned_in_range 64 (getr (sm_regs cx) (Z_to_bv 5 (10 + 0)))) as Hr.
  change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr. }
assert (Hnamer : 0 <= srm_name cx < 2 ^ 64).
{ unfold srm_name, aarg, argZ. pose proof (bv_unsigned_in_range 64 (getr (sm_regs cx) (Z_to_bv 5 (10 + 1)))) as Hr.
  change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr. }
(* ---------------- phase A: the two refusals of NULL ---------------- *)
remember (Eimg (Ereg (ms_regs ms3) [])) as EA eqn:HEA.
assert (HEIA : img_env VAL A_LIM EA) by (subst EA; apply Eimg_env).
assert (HAA : env_agree 32 (Ereg (ms_regs ms3) []) EA)
  by (subst EA; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EA22 : ew EA 22 = w64 (srm_mk cx)).
{ subst EA. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat (ms_regs ms3) [] 22%nat 22%bv eq_refl).
  exact R22. }
assert (EA20 : ew EA 20 = w64 (srm_name cx)).
{ subst EA. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat (ms_regs ms3) [] 20%nat 20%bv eq_refl).
  exact R20. }
assert (HSA : st_ok_pi SEGS VAL EA srm_ssA (restrict (w_H W3) ms3)).
{ unfold srm_ssA. apply srm_mid_st; try assumption.
  - subst EA. apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - apply Forall_nil.
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - split; [cbn [f_atoms atoms_ok]; exact I | split; exact I]. }
assert (SHA : sh_ok SEGS srm_mBx [] EA (rdW W3 (ms_mem ms3))) by apply Forall_nil.
clear HEA.
apply (BR W3 EA srm_ssA ms3 md3 (srm_post fx SK B cx) BC_EQ (SOff 22 0) (SLit 0) HSA); intros Hc HS1;
  rewrite branch_eq_U, (U_atom EA 22%nat (srm_mk cx) EA22 Hmkr), (U_lit EA 0 ltac:(lia)) in Hc.
{ (* a NULL marks block: to the EXIT cut *)
  apply Z.eqb_eq in Hc.
  srm_tok_to RUNTO HS1 HJ SHA srm_mspan SRM_CUT_EXIT; [apply awr_ok_x_nil|].
  intros ws ms4 mat4 Hlen HEI4 HS4 SHOK4 HJ4 HF4 HFr4 HG4. cbn [sh_j sh_ss] in Hlen, HS4.
  destruct ws; [|discriminate Hlen]. cbn [extK] in HS4.
  pose proof (srm_mid_frame_ro _ _ _ _ HF4 ltac:(srm_ro)) as Hmem4.
  apply (HEXIT cx fpos ly3 S3 W3 ms4 _ HPRE HGS).
  exact (srm_mid_exit_of cx fpos ly3 S3 W3 ms3 ms4 md3 _ EA _ [] HPRE HB R21 (or_introl Hc) HS4
           eq_refl ltac:(vm_compute; reflexivity) HAA ltac:(vm_compute; reflexivity) Hmem4 HJ4
           (proj1 (wvb_fds_fs _ _ _)) (proj2 (wvb_fds_fs _ _ _))). }
apply Z.eqb_neq in Hc.
apply (BR W3 EA _ ms3 md3 (srm_post fx SK B cx) BC_EQ (SOff 20 0) (SLit 0) HS1); intros Hc2 HS2;
  rewrite branch_eq_U, (U_atom EA 20%nat (srm_name cx) EA20 Hnamer), (U_lit EA 0 ltac:(lia)) in Hc2.
{ (* a NULL name: to the EXIT cut *)
  apply Z.eqb_eq in Hc2.
  srm_tok_to RUNTO HS2 HJ SHA srm_mspan SRM_CUT_EXIT; [apply awr_ok_x_nil|].
  intros ws ms4 mat4 Hlen HEI4 HS4 SHOK4 HJ4 HF4 HFr4 HG4. cbn [sh_j sh_ss] in Hlen, HS4.
  destruct ws; [|discriminate Hlen]. cbn [extK] in HS4.
  pose proof (srm_mid_frame_ro _ _ _ _ HF4 ltac:(srm_ro)) as Hmem4.
  apply (HEXIT cx fpos ly3 S3 W3 ms4 _ HPRE HGS).
  exact (srm_mid_exit_of cx fpos ly3 S3 W3 ms3 ms4 md3 _ EA _ [] HPRE HB R21 (or_intror (or_introl Hc2)) HS4
           eq_refl ltac:(vm_compute; reflexivity) HAA ltac:(vm_compute; reflexivity) Hmem4 HJ4
           (proj1 (wvb_fds_fs _ _ _)) (proj2 (wvb_fds_fs _ _ _))). }
apply Z.eqb_neq in Hc2.
(* to +0x1bc *)
srm_tok_to RUNTO HS2 HJ SHA srm_mspan SRM_PC_B; [apply awr_ok_x_nil|].
intros ws msb matb Hlen HEIb HSb SHOKb HJb HFb HFrb HGb. cbn [sh_j sh_ss] in Hlen, HSb.
destruct ws; [|discriminate Hlen]. cbn [extK] in HSb.
pose proof (srm_mid_frame_ro _ _ _ _ HFb ltac:(srm_ro)) as Hmemb.
destruct (srm_mid_move_of cx fpos ly3 S3 W3 ms3 msb md3 _ EA _ [] HB HSb eq_refl HAA
            ltac:(vm_compute; reflexivity) Hmemb HJb (proj1 (wvb_fds_fs _ _ _)) (proj2 (wvb_fds_fs _ _ _)))
  as (HBb & HRSb & Hpcb).
set (mdb := with_vm_backing (m_vm_lazy md3) matb md3) in *.
(* ---------------- phase B: the check of name[0] and the empty name ---------------- *)
destruct nm as [s|]; [|exfalso; exact (Hc2 Hnm)].
change (aarg (sm_regs cx) 1) with (srm_name cx) in Hnm.
pose proof HRSb as (Qb2 & Qb9 & Qb8 & Qb18 & Qb19 & Qb25 & Qb26 & Qb20 & Qb22 & Qb3 & Qb4 & Qb27 & Qb21).
assert (Hspan1 : forall a, srm_name cx <= a <= srm_name cx + Z.of_nat (length s) ->
          akb SEGS B (sm_lyc cx) (sm_Sc cx) (srm_sp cx - REAC_SERVED_MARK_AK) (srm_sp cx) a)
  by (intros a Ha; exact (proj1 HGS s a Hnm Ha)).
destruct (srm_name_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos srm_X0 ly3 S3 W3 msb mdb REAC_LINK_ALIAS_READ_AK s
            HPRE HBb HX0 HKc Hnm Hspan1) as (Hncb & Hnrtb & _).
pose proof Hnrtb as (_ & _ & Hnamb & Hnrab & _).
destruct (nth_error (s ++ [zb 0]) 0) as [b0|] eqn:E0;
  [|exfalso; apply nth_error_None in E0; rewrite length_app in E0; cbn [length] in E0; lia].
assert (Hb0 : mbyte SEGS (rdW W3 (ms_mem msb)) (srm_name cx) = Some b0).
{ destruct Hncb as ((_ & _ & Hn) & _). specialize (Hn 0%nat ltac:(rewrite length_app; cbn [length]; lia)).
  cbn [Z.of_nat] in Hn. rewrite Z.add_0_r in Hn. rewrite Hn, E0. reflexivity. }
assert (Hb0r : 0 <= bv_unsigned b0 < 256)
  by (pose proof (bv_unsigned_in_range 8 b0) as R; change (bv_modulus 8) with 256 in R; exact R).
remember (Eimg (Ereg (ms_regs msb) [w64 (bv_unsigned b0)])) as EB eqn:HEB.
assert (HEIB : img_env VAL A_LIM EB) by (subst EB; apply Eimg_env).
assert (HAB : env_agree 32 (Ereg (ms_regs msb) [w64 (bv_unsigned b0)]) EB)
  by (subst EB; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EB26 : ew EB 26 = w64 SHADOW_OFF).
{ subst EB. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat (ms_regs msb) _ 26%nat 26%bv eq_refl), Qb26. exact R26. }
assert (EB20 : ew EB 20 = w64 (srm_name cx)).
{ subst EB. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat (ms_regs msb) _ 20%nat 20%bv eq_refl), Qb20. exact R20. }
assert (EB32 : ew EB 32 = w64 (bv_unsigned b0)).
{ subst EB. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ms_regs msb) _ 0). }
assert (UB26 : bv_unsigned (ew EB 26) = SHADOW_OFF)
  by (rewrite EB26; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (UB20 : bv_unsigned (ew EB 20) = srm_name cx) by (rewrite EB20; unfold w64; apply unsigned_lit_small; lia).
assert (UB32 : bv_unsigned (ew EB 32) = bv_unsigned b0) by (rewrite EB32; unfold w64; apply unsigned_lit_small; lia).
assert (Hn47 : srm_name cx <= 2 ^ 47 - 1)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hnamb; lia).
pose proof HBb as (Hresvb & Hsvcb & Hromb & Hfrgb & Hfcsrb & _).
assert (HSB : st_ok_pi SEGS VAL EB srm_ssB (restrict (w_H W3) msb)).
{ unfold srm_ssB. apply (srm_mid_st W3 msb SRM_PC_B EB _ _ Hresvb Hsvcb Hromb Hfrgb Hfcsrb Hpcb).
  - subst EB. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, srm_nameR.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite UB20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS EB _ (srm_name cx) 0 1%N (SOff 32 0) (bv_unsigned b0)).
    + cbn [sv_denot]. rewrite EB32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    + change (2 ^ (8 * Z.of_N 1%N)) with 256. lia.
    + change (Z.of_N 1%N) with 1. lia.
    + rewrite Z.add_0_r. exact (srm_mid_val_mem1 SEGS _ _ _ Hb0).
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite UB26, UB20, UB32. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia | unfold SHADOW_OFF; lia]. }
assert (SHB : sh_ok SEGS srm_mBx srm_SHB EB (rdW W3 (ms_mem msb))).
{ apply Forall_cons; [|apply Forall_nil]. unfold shent_ok, app_apart, srm_mBx. cbn [she_m she_lo she_hi].
  rewrite (U_atom EB 26%nat SHADOW_OFF EB26 ltac:(unfold SHADOW_OFF; lia)), (U_atom EB 20%nat (srm_name cx) EB20 Hnamer).
  split.
  - rewrite Z.add_0_r. intros x Hx. exact (Hnrab x ltac:(lia)).
  - intros a Ha. cbn [Z.min Z.max] in Ha.
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia. }
srm_tok RUN HSB HJb SHB srm_mspan.
{ apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros a Ha. cbn [srm_nameR YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
intros ws msB4 matB4 HlenB HEIB4 HSB4 SHB4 HJB4 HFB4 HFrB4 HGB4. cbn [sh_j sh_ss] in HlenB, HSB4.
lazymatch type of HSB4 with st_ok_pi _ _ (extK _ ?K _) _ _ =>
  pose proof (srm_mid_agree_ext SK B LAWS TB RELRO_IMG HSEGS _ EB K ws HAB ltac:(cbv; lia)) as HAB4;
  destruct (env_agree_extK EB K ws) as [AK _];
  assert (EB'32 : ew (extK EB K ws) 32 = w64 (bv_unsigned b0)) by (rewrite (AK 32%nat ltac:(cbv; lia)); exact EB32)
end.
pose proof (srm_mid_frame_ro _ _ _ _ HFB4 ltac:(srm_ro)) as HmemB4.
set (mdB4 := with_vm_backing (m_vm_lazy mdb) matB4 mdb) in *.
apply (BR W3 _ _ msB4 mdB4 (srm_post fx SK B cx) BC_EQ (SOff 32 0) (SLit 0) HSB4); intros Hc3 HS3;
  rewrite branch_eq_U, (U_atom _ 32%nat (bv_unsigned b0) EB'32 ltac:(lia)), (U_lit _ 0 ltac:(lia)) in Hc3.
{ (* the empty name: to the EXIT cut *)
  apply Z.eqb_eq in Hc3.
  srm_plain_to RUNP HS3 HJB4 SRM_CUT_EXIT.
  { apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. cbn [srm_nameR YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
  intros ms5 mat5 HS5 HJ5 HF5 HFr5 HG5.
  pose proof (srm_mid_frame_ro _ _ _ _ HF5 ltac:(srm_ro)) as Hmem5.
  assert (Hav : aview SEGS (w_H W3) (ms_mem msb) (srm_name cx) = Some 0)
    by (unfold aview; rewrite Hb0; cbn [option_map]; rewrite Hc3; reflexivity).
  apply (HEXIT cx fpos ly3 S3 W3 ms5 _ HPRE HGS).
  exact (srm_mid_exit_of cx fpos ly3 S3 W3 msb ms5 mdb _ _ _ [w64 (bv_unsigned b0)] HPRE HBb
           ltac:(rewrite Qb21; exact R21) (or_intror (or_intror Hav)) HS5 eq_refl ltac:(vm_compute; reflexivity)
           HAB4 ltac:(vm_compute; reflexivity) (eq_trans Hmem5 HmemB4) HJ5
           (proj1 (srm_mid_wvb2 _ _ _ _ _)) (proj2 (srm_mid_wvb2 _ _ _ _ _))). }
apply Z.eqb_neq in Hc3.
assert (Hs0 : s <> []).
{ intros ->. cbn [app nth_error] in E0. injection E0 as <-. apply Hc3. reflexivity. }
(* to +0x1d4 *)
srm_plain_to RUNP HS3 HJB4 SRM_PC_C.
{ apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros a Ha. cbn [srm_nameR YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
intros msc matc HSc HJc' HFmc HFrc HGc.
pose proof (srm_mid_frame_ro _ _ _ _ HFmc ltac:(srm_ro)) as Hmemc.
destruct (srm_mid_move_of cx fpos ly3 S3 W3 msb msc mdb _ _ _ [w64 (bv_unsigned b0)] HBb HSc eq_refl HAB4
            ltac:(vm_compute; reflexivity) (eq_trans Hmemc HmemB4) HJc'
            (proj1 (srm_mid_wvb2 _ _ _ _ _)) (proj2 (srm_mid_wvb2 _ _ _ _ _)))
  as (HBc & HRSc & Hpcc).
set (mdc := with_vm_backing (m_vm_lazy mdB4) matc mdB4) in *.
(* ---------------- phase C: the buffers' shadow, the arguments, the call ---------------- *)
pose proof HRSc as (Qc2 & Qc9 & Qc8 & Qc18 & Qc19 & Qc25 & Qc26 & Qc20 & Qc22 & Qc3 & Qc4 & Qc27 & Qc21).
destruct (srm_F_facts SK B LAWS TB RELRO_IMG HSEGS fx cx fpos srm_X0 ly3 S3 W3 msc mdc HPRE HBc)
  as (HF4096 & HFc & HF64 & HFapp & HFimg & HinF & HFaddr & _).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HSHv : srm_SH cx fpos = SHADOW_OFF + srm_F cx fpos / 8) by reflexivity.
unfold SRM_FB in HFc, HFapp, HFimg.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
assert (HF8 : srm_F cx fpos / 8 < 17592186044352)
  by (apply Z.div_lt_upper_bound; [lia | change (8 * 17592186044352) with 140737488354816; lia]).
assert (HF80 : 0 <= srm_F cx fpos / 8) by (apply Z.div_pos; lia).
remember (Eimg (Ereg (ms_regs msc) [])) as EC eqn:HEC.
assert (HEIC : img_env VAL A_LIM EC) by (subst EC; apply Eimg_env).
assert (HAC : env_agree 32 (Ereg (ms_regs msc) []) EC)
  by (subst EC; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (ECr : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew EC n = getr (ms_regs msc) r).
{ intros n r Hn Hr. subst EC. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat (ms_regs msc) [] n r Hr). }
assert (EC18 : ew EC 18 = w64 (srm_SH cx fpos))
  by (rewrite (ECr 18%nat 18%bv ltac:(lia) eq_refl), Qc18, Qb18; exact R18).
assert (EC20 : ew EC 20 = w64 (srm_name cx))
  by (rewrite (ECr 20%nat 20%bv ltac:(lia) eq_refl), Qc20, Qb20; exact R20).
assert (EC25 : ew EC 25 = w64 (srm_F cx fpos))
  by (rewrite (ECr 25%nat 25%bv ltac:(lia) eq_refl), Qc25, Qb25; exact R25).
assert (UC18 : bv_unsigned (ew EC 18) = srm_SH cx fpos)
  by (rewrite EC18; unfold w64; apply unsigned_lit_small; rewrite HSHv; unfold SHADOW_OFF; lia).
pose proof HBc as (Hresvc & Hsvcc & Hromc & Hfrgc & Hfcsrc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & _ & _ & _ & _ & _ & _ & HSHpresc & _).
assert (HSC : st_ok_pi SEGS VAL EC srm_ssC (restrict (w_H W3) msc)).
{ unfold srm_ssC. apply (srm_mid_st W3 msc SRM_PC_C EC _ _ Hresvc Hsvcc Hromc Hfrgc Hfcsrc Hpcc).
  - subst EC. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, srm_shR.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite UC18. split; [rewrite HSHv; unfold SHADOW_OFF; lia|]. split; [rewrite HSHv; unfold SHADOW_OFF; lia|].
    split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply HSHpresc. unfold SRM_SHN. lia.
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - split; [cbn [f_atoms atoms_ok]; exact I | split; exact I]. }
srm_plain_call RUNC HSC HJc'.
{ apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros a Ha. cbn [srm_shR YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite UC18 in Ha. left.
  apply (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SRM_CID fpos a HJc'
           (or_introl eq_refl)).
  right. unfold in_zr. cbn [fst snd]. rewrite HFaddr. change (fs_frame_bytes SRM_CID / 8) with 64.
  rewrite HSHv in Ha. unfold shadow_addr. lia. }
intros msD matD HSD HJD HFD HFrD HGD.
set (mdD := with_vm_backing (m_vm_lazy mdc) matD mdc) in *.
(* the callee's entry: the state, its registers, its memory *)
pose proof (st_ok_restrict_mkst SEGS (w_H W3) EC _ msD HSD eq_refl) as HmsD.
lazymatch type of HmsD with _ = mkst _ (Z_to_bv 64 ?p) _ _ =>
  assert (HpD : p = REAC_LINK_ALIAS_READ_A) by (cbn [setpc ss_pc]; rewrite (lv_sigma HV); reflexivity);
  rewrite HpD in HmsD
end.
sreg HSD (1%bv : bv 5) R1D. sreg HSD (10%bv : bv 5) R10D. sreg HSD (11%bv : bv 5) R11D. sreg HSD (12%bv : bv 5) R12D.
sreg HSD (13%bv : bv 5) R13D. sreg HSD (14%bv : bv 5) R14D. sreg HSD (23%bv : bv 5) R23D. sreg HSD (24%bv : bv 5) R24D.
cbn [ms_regs restrict] in R1D, R10D, R11D, R12D, R13D, R14D, R23D, R24D.
change (SOff 240 30304) with (SOff A_TEXT 30304) in R1D. rewrite (codeptr_val EC _ HEIC) in R1D.
cbn [sv_denot] in R10D, R11D, R12D, R13D, R14D, R23D, R24D.
rewrite EC20, Z.add_0_r in R10D. unfold w64 in R10D. rewrite Z_to_bv_bv_unsigned in R10D.
rewrite EC25 in R11D, R13D, R23D, R24D. unfold w64 in R11D, R13D, R23D, R24D.
rewrite unsigned_lit_small in R11D, R13D, R23D, R24D by lia.
pose proof (srm_mid_regs_same_abs SK B LAWS TB RELRO_IMG HSEGS EC _ msc msD [] (w_H W3) HSD HAC
              ltac:(vm_compute; reflexivity)) as HRSD.
pose proof HRSD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & QD21).
assert (HfrD : forall x : word, ~ (srm_SH cx fpos + 4 <= bv_unsigned x < srm_SH cx fpos + 44) ->
                ms_mem msD x = ms_mem msc x).
{ intros x Hx. apply HFD. intros (r & Hin & Hr). cbn [srm_ssC ss_mem In] in Hin. destruct Hin as [<- | []].
  cbn [srm_shR YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite UC18 in Hr. exact (Hx Hr). }
assert (HBD : srm_base fx SK B cx fpos srm_X0 ly3 S3 W3 msD mdD).
{ apply (srm_mid_base_side SK B LAWS TB RELRO_IMG HSEGS cx fpos ly3 S3 W3 msc msD mdc mdD HPRE HBc);
    try (rewrite HmsD; reflexivity).
  - exact HRSD.
  - exact HfrD.
  - exact HGD.
  - exact HJD.
  - exact (proj1 (wvb_fds_fs _ _ _)).
  - exact (proj2 (wvb_fds_fs _ _ _)). }
(* F's buffers' shadow is 0 at the call *)
assert (HZD : forall i, srm_bufsh_off i -> aview SEGS (w_H W3) (ms_mem msD) (srm_SH cx fpos + i) = Some 0).
{ sregion HSD 0%nat HRg. destruct HRg as (_ & _ & _ & HCs).
  cbn [YP09.r_chunks YP09.r_base base_val] in HCs. rewrite UC18 in HCs.
  lazymatch type of HCs with Forall _ ?cs =>
    intros i Hi;
    assert (Hin : In (YP09.mkChunk i (CVal 1 (SLit 0))) cs)
      by (apply (srm_mid_zall_spec cs i); [vm_compute; reflexivity | exact Hi])
  end.
  pose proof (proj1 (Forall_forall _ _) HCs _ Hin) as Hck.
  pose proof (srm_mid_chunk_zero SEGS EC _ _ i Hck) as Hz.
  unfold aview. rewrite Hz. reflexivity. }
(* the callee's Pre and the entry facts the RRET cut restates *)
destruct (Hblk Hc) as (_ & _ & _ & _ & gbs & Hg0 & Hgw).
assert (HENT : srm_ent cx s kbs tab gbs k0).
{ split; [exact Hc|]. split; [exact Hnm|]. split; [exact Hs0|]. split; [exact HNLK|].
  split; [exact Hg0|]. split; [exact Hgw|]. split; [exact HMF | exact Hk0]. }
destruct (srm_mid_call_pre SK B LAWS TB RELRO_IMG HSEGS cx fpos ly3 S3 W3 msD mdD s kbs tab HPRE HGS HBD HNLK Hnm
            R10D R11D R12D R13D R14D R1D HZD) as (Hapre & Hrd & Hpre).
(* the call, at the walk's fx *)
pose proof (HRD fx) as Hcall. unfold reac_link_alias_read_acontract, aleaf_rd in Hcall.
specialize (Hcall (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx) (sm_FP cx) (sm_ly cx) (sm_S cx)
  (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) ((SRM_CID, fpos) :: sm_own cx) ly3 S3 W3 (ms_mem msD) mdD (sm_k cx)
  (ms_regs msD) Hapre Hrd Hpre).
rewrite HmsD.
change (mkCfg (mkst (ms_regs msD) (Z_to_bv 64 REAC_LINK_ALIAS_READ_A) (ms_mem msD) (seg_rom SEGS)) mdD)
  with (cfg_at SEGS REAC_LINK_ALIAS_READ_A (ms_regs msD) (ms_mem msD) mdD).
eapply SRr_bind; [exact Hcall|]. intros W4 c4 _ Hpost.
destruct (srm_call_back SK B LAWS TB RELRO_IMG HSEGS fx fx cx fpos srm_X0 ly3 S3 W3 msD mdD
            REAC_LINK_ALIAS_READ_AK _ (reac_link_alias_read_apost SEGS (ms_regs msD) (rdW W3 (ms_mem msD))) W4 c4
            HPRE HBD HX0 (@BoxBase.fxr_refl fx) HKc
            (fun a Ha => srm_mid_call_wr SK B LAWS TB RELRO_IMG HSEGS cx fpos (ms_regs msD) _ a R11D R12D R13D R14D
                           ltac:(lia) ltac:(lia) Ha) Hpost)
  as (ly4 & S4 & regs4 & mem4 & md4 & -> & HB4 & HAP4 & HK4 & HP4).
apply (HRRET cx fpos ly4 S4 W4 _ md4 HPRE HGS).
exact (srm_mid_rret SK B LAWS TB RELRO_IMG HSEGS cx fpos ly3 S3 W3 msD mdD s kbs tab gbs k0 ly4 S4 W4 regs4 mem4 md4
         HPRE HBD HENT R10D R11D R12D R13D R14D R1D ltac:(rewrite QD21, Qc21, Qb21; exact R21) R23D R24D HZD
         HB4 HAP4 HK4 HP4).
Qed.

End b.
End a.

About srm_mid. Print Assumptions srm_mid.
