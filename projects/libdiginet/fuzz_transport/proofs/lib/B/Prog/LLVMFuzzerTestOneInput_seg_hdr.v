(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 1037 of its 1127 lines of code are new or changed and 1049 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_hdr: Lemma lc_hdr_ok : lc_hdr_stmt, the segment HDR of the image-B walk of
   fuzz_transport.asan-ubsan's LLVMFuzzerTestOneInput (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v), from the cut lc_st_sm
   (the return of __asan_stack_malloc_2, +0x074) to the cut lc_st_cfgd (the return of
   diginet_session_config_default, +0x358).
   rule 24: proves no function (segment lemma of LLVMFuzzerTestOneInput's walk, image B)

   It is proved from the statement's premises lp_prem, the slot's pre lc_base and the kit statement K1
   (segs.v lc_rom_view_stmt, an argument of the lemma), with the Qed bridges of lib/B/Prog/LLVMFuzzerTestOneInput_st.v
   (lc_geom, lc_core_kept_run, lc_core_kept, lc_sh_any, lc_rom_bytes, lc_garr8_kept, lc_spills_kept, lc_fsh_kept).
   Over the runs and __asan_memcpy, which write the slots above sp1, the frame and its shadow, the core moves by
   lh_core_step below (st.v lc_core_kept_run; the bytes the segment writes are lh_wr). The runs are the
   position-abstract runs of lib/B/Prog/TransportGRunB.v paj_run_x / paj_run_to_x over the walk's G journal (the
   cut's), in the idiom of image A's segment HDR (lib/A/Prog/LLVMFuzzerTestOneInput_seg_hdr.v):
     run A  +0x074 .. +0x0e0  `j`, `bnez a0` (decided: a0 = F >= 4096, so the real-stack arm +0x084 .. +0x09c is not
                              entered), F into 128(s1), 208(s1) and 136(s1), the frame's header (magic, descriptor,
                              the function's address) at F, s4 = F + 176, s2 = the frame's shadow address;
     run B  +0x0e4 .. +0x17c  the frame's 32 shadow bytes (lf_shm false false), a1 = io's image copy
                              (__const.LLVMFuzzerTestOneInput.io, object 4), a2 = 32, a0 = s4, up to
                              `jal __asan_memcpy`;
     +0x17c                   __asan_memcpy (F + 176, io, 32) by lp_memcpy through TransportGCg.v gx_intrin_at: the
                              destination is the own frame (shadow bytes 22 .. 25 are 0 since run B), the source is
                              TRANS_RO_RD (its bytes by K1, its shadow by st.v lc_sh_any);
     run C  +0x180 ..         the size test `srli a0, s5, 26; beqz a0` (s5 = n < 2 ^ 26 by lc_base: the fall-through
                              +0x188 into the epilogue is refuted), `beqz s5` at +0x244: n = 0 gives s7 = s8 = 0,
                              s3 = p (+0x33c .. +0x344); n > 0 (from +0x248, a state with the byte p[0] and the shadow
                              byte of p as read-only regions, the shadow address of p named by an alias fact):
                              s3 = p + 1, the UBSan cursor test `bltu a0, s3` (+0x250; the run decides it from the fact
                              p >= 4096 of atom 22, so its trap edge +0x254 is not taken), the shadow byte of p, whose
                              `beqz a0` and, on the slow path +0x1b54 .. +0x1b5c, `bge a1, a0` (a1 = p & 7 = 0) leave
                              the report call +0x1b64 unreached: p is 16-aligned and the byte is 0 or in (0, 8) by the
                              input block's shadow (AR's shadow law);
                              then the byte p[0] into s8 (+0x26c), s7 = n - 1; s5 = a0 = g_cfg (+0x34c) and
                              `jal diginet_session_config_default`;
     +0x354                   diginet_session_config_default by lp_scfg in the same G journal (lh_call), from the world
                              Bw0 at the entry memory (TWorldB.v tw_exists_B); its kept facts give the cut's core by
                              st.v lc_core_kept.
   The journal's frame-pointer list is never named: every fact about the core goes through segs.v lc_core. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0 YE2k YCfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require AsanCells TransportGB YF0x YE2y.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportGFrame TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB TransportGNoticeB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_config_default_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_init_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import LLVMFuzzerTestOneInput_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TCb TSess0 TOps TWorldLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TGNA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.TransportGNotice.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The tactics of the runs                                          *)
(* ------------------------------------------------------------------ *)

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac lh_reg HS r v H tac :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* Region i of the symbolic state HS, at the machine state's memory. *)
Ltac lh_region HS i HR :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (apply (can_region_nth Ex ssx (restrict Hh msx) i r0 HS); vm_compute; reflexivity)
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (let HS' := fresh in pose proof HS as HS'; unfold st_ok_pi in HS';
            eapply (can_region_nth Ex _ (restrict Hh msx) i r0 HS'); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.
(* The awr obligation's regions, computed. *)
Ltac lh_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* The awr obligation of a run whose regions write no byte. *)
Ltac lh_awr_ro :=
  lh_awr_rs;
  repeat (apply awr_ok_x_cons;
          [let a := fresh "a" in let Ha := fresh "Ha" in
           intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.
(* Name the machine state of HS. *)
Ltac lh_name HS x :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ _ _ (restrict _ ?m) => rename m into x
  | st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into x
  end.
(* Every byte outside the windows of the run's regions is kept (KD). *)
Ltac lh_kept W HFr HG Zs KD tac :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?Hh ?mp) (mrestrict ?Hh2 ?mn) =>
  assert (KD : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview tfibsegs (w_H W) mn a = aview tfibsegs (w_H W) mp a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
    intros a Ha Hn; apply (kept_of_frame _ _ _ _ _ Zs HFr); [| exact Ha | exact Hn];
    let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in
    let x := fresh "x" in let Hin := fresh "Hin" in let Hx := fresh "Hx" in
    intros b wlo whi x Hin Hx;
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
    cbn [In] in Hin;
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac | ]);
    try destruct Hin
  | ]
  end.
(* After a run whose regions write no byte: the running facts KV (the view at the current memory is the view at the
   reference memory) and GP (presence grows from the reference memory) move to the run's end. *)
Ltac lh_step W KV GP :=
  match goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _ |- _ =>
    let KD := fresh "KD" in lh_kept W HFr HG (fun _ : Z => False) KD ltac:(lia);
    let K2 := fresh "K" in let G2 := fresh "G" in
    pose proof (fun a Ha => eq_trans (KD a Ha (fun x => x)) (KV a Ha)) as K2;
    pose proof (fun a Ha => apresent_grows _ _ _ a HG (GP a Ha)) as G2;
    clear KD KV GP HFr HG; rename K2 into KV; rename G2 into GP;
    try match goal with HF0 : frame_of _ _ _ _ |- _ => clear HF0 end
  end.

(* ------------------------------------------------------------------ *)
(* 2. The symbolic states of the runs                                  *)
(* ------------------------------------------------------------------ *)

Definition LH_B0 : Z * Z := (0, 0).
(* The return offsets of the two calls. *)
Definition LH_RCPY : Z := AF_LLVMFuzzerTestOneInput + 0x180.
Definition LH_RCFG : Z := AF_LLVMFuzzerTestOneInput + 0x358.

(* run A, +0x074 .. +0x0e0: s1 (atom 9) is sp1, a0 (atom 10) is F, s10 (atom 26) the shadow base; the run writes the
   slots 128(s1), 208(s1), 136(s1) and the frame's 24-byte header, and stops at the first shadow store (+0x0e4). *)
Definition LH_CA : Z := AF_LLVMFuzzerTestOneInput + 0x74.
Definition lh_rg_slot : YP09.region := YP09.mkRegion (Some 9%nat) 128 216 128 216 [].
Definition lh_rg_hdr : YP09.region := YP09.mkRegion (Some 10%nat) 0 24 0 24 [].
Definition lh_factsA : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (10%nat, mkAF 4096 (2 ^ 47) 6); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_lhA : sstate := mkSS LH_CA sr_atoms [lh_rg_slot; lh_rg_hdr] None lh_factsA.

(* run B, +0x0e4 .. +0x17c: s2 (atom 18) holds the frame's shadow address; the run writes its 32 shadow bytes and
   stops at the call of __asan_memcpy. *)
Definition LH_CB : Z := AF_LLVMFuzzerTestOneInput + 0xe4.
Definition lh_rg_sh : YP09.region := YP09.mkRegion (Some 18%nat) 0 32 0 32 [].
Definition lh_factsB : facts := mkFacts [(18%nat, mkAF SHADOW_OFF (2 ^ 46) 0)] [] [].
Definition ss_lhB : sstate := mkSS LH_CB sr_atoms [lh_rg_sh] None lh_factsB.

(* run C1, +0x180 .. +0x244: s5 (atom 21) is n < 2 ^ 26; no region. *)
Definition lh_factsC : facts := mkFacts [(21%nat, mkAF 0 (2 ^ 26 - 1) 0)] [] [].
Definition ss_lhC : sstate := mkSS LH_RCPY sr_atoms [] None lh_factsC.

(* run C2, from +0x248 (n > 0): s6 (atom 22) is p (16-aligned), s10 (atom 26) the shadow base; atom 33 is the byte
   p[0], atom 34 the shadow address of p (the alias fact: (p >> 3) + s10), atom 35 its shadow byte. *)
Definition LH_CC : Z := AF_LLVMFuzzerTestOneInput + 0x248.
Definition lh_rg_in : YP09.region := YP09.mkRegion (Some 22%nat) 0 1 0 0 [YP09.mkChunk 0 (YP09.CVal 1 (SOff 33 0))].
Definition lh_rg_sp : YP09.region := YP09.mkRegion (Some 34%nat) 0 1 0 0 [YP09.mkChunk 0 (YP09.CVal 1 (SOff 35 0))].
Definition lh_factsC2 : facts :=
  mkFacts [(21%nat, mkAF 1 (2 ^ 26 - 1) 0); (22%nat, mkAF 4096 (2 ^ 47) 3); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 0 255 0); (34%nat, mkAF SHADOW_OFF (2 ^ 46) 0); (35%nat, mkAF 0 7 0)] []
    [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 22 0) (SLit 3)) (SOff 26 0), SOff 34 0)].
Definition ss_lhC2 : sstate := mkSS LH_CC sr_atoms [lh_rg_in; lh_rg_sp] None lh_factsC2.

(* The size test `srli a0, s5, 26; beqz a0` (+0x180 / +0x184) at n < 2 ^ 26: always taken. *)
Lemma lh_srl26 : forall E n, ew E 21 = Z_to_bv 64 n -> 0 <= n < 2 ^ 26 ->
  branch_taken BC_EQ (sv_denot E (SAlu ALU_SRL (SOff 21 0) (SLit 26))) (sv_denot E (SLit 0)) = true.
Proof.
intros E n H21 Hn.
rewrite (denot_lit_U E (SAlu _ _ _)), U_SAlu. cbn [zalu_raw].
rewrite U_SOff, H21, U_SLit, unsigned_lit_small by lia. rewrite Z.add_0_r, (zcanon_id n), (zcanon_id 26) by (unfold M64; lia).
change (Z.land 26 63) with 26. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia.
change (sv_denot E (SLit 0)) with (Z_to_bv 64 0). vm_compute. reflexivity.
Qed.

(* `beqz` on a register atom m holding n: the test n = 0. *)
Lemma lh_beqz : forall E (m : nat) n b, ew E m = Z_to_bv 64 n -> 0 <= n < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff m 0)) (sv_denot E (SLit 0)) = b -> (n =? 0) = b.
Proof.
intros E m n b Hm Hn Hb. rewrite <- Hb.
rewrite (denot_lit_U E (SOff m 0)), U_SOff, Hm, unsigned_lit_small by lia. rewrite Z.add_0_r, (zcanon_id n) by (unfold M64; lia).
change (sv_denot E (SLit 0)) with (Z_to_bv 64 0). cbn [branch_taken].
unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite !Z.mod_small by lia. reflexivity.
Qed.

(* The slow path's `bge a1, a0` (+0x1b58) with a1 = p & 7 = 0 and a0 the shadow byte of p, not 0: the shadow byte is
   in (0, 8) (the input block's shadow), so the branch to the report call +0x1b64 is not taken. *)
Lemma lh_bge : forall E sb b, ew E 35 = Z_to_bv 64 sb -> 0 < sb < 8 ->
  branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff 35 0)) = b -> b = false.
Proof.
intros E sb b H35 Hsb Hb. rewrite <- Hb.
rewrite (denot_lit_U E (SOff 35 0)), U_SOff, H35, unsigned_lit_small by lia. rewrite Z.add_0_r.
change (sv_denot E (SLit 0)) with (Z_to_bv 64 0).
assert (Hc : sb = 1 \/ sb = 2 \/ sb = 3 \/ sb = 4 \/ sb = 5 \/ sb = 6 \/ sb = 7) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]; vm_compute; reflexivity.
Qed.

(* The flags byte of a non-empty input and the cursor after it (+0x26c .. +0x270). *)
Lemma lh_c1_cons : forall (x : byte) l,
  lc_c1 (x :: l) = TOP.FuzzIn 1 (Z.of_nat (length (x :: l)) - 1) /\ lc_flags (x :: l) = bv_unsigned x.
Proof.
intros x l. unfold lc_c1, lc_flags, TOP.fuzz_u8_m, TOP.fuzz_in_m. cbn [TOP.fi_n TOP.fi_off].
replace (Z.of_nat (length (x :: l)) =? 0) with false by (symmetry; apply Z.eqb_neq; cbn [length]; lia).
cbn [fst snd]. split; reflexivity.
Qed.

Section ent. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The valuation of runs A, B and C1: the 32 registers at the run's start and the shadow base (atom 32). *)
Definition lh_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs [w64 SHADOW_OFF]).
Lemma lh_ew_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (lh_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold lh_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma lh_ew_32 : forall regs, ew (lh_E regs) 32 = Z_to_bv 64 SHADOW_OFF.
Proof. intros regs. unfold lh_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma lh_ew_obj : forall regs i, (i < 95)%nat -> ew (lh_E regs) (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)).
Proof. intros regs i Hi. unfold lh_E. apply Eimg_img. unfold A_OBJ, A_TEXT, A_LIM. lia. Qed.
Lemma lh_env_img : forall regs, img_env VAL A_LIM (lh_E regs).
Proof. intros regs. unfold lh_E. apply Eimg_env. Qed.

(* The two image objects the segment names: io's image copy (object 4) and g_cfg (object 5). *)
Lemma lh_obj4 : forall regs, sv_denot (lh_E regs) (SOff 245 0) = w64 TRANS_IO.
Proof.
intros regs. cbn [sv_denot]. change (ew (lh_E regs) 245) with (ew (lh_E regs) (A_OBJ 4)).
rewrite (lh_ew_obj regs 4 ltac:(lia)). vm_compute. reflexivity.
Qed.
Lemma lh_obj5 : forall regs, sv_denot (lh_E regs) (SOff 246 0) = w64 TB_g_cfg.
Proof.
intros regs. cbn [sv_denot]. change (ew (lh_E regs) 246) with (ew (lh_E regs) (A_OBJ 5)).
rewrite (lh_ew_obj regs 5 ltac:(lia)). vm_compute. reflexivity.
Qed.

(* The valuation of run C2: the registers, the shadow base (atom 32), p[0] (33), p's shadow address (34) and byte (35). *)
Definition lh_E2 (regs : bvmap 5 word) (b0 sa sb : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [w64 SHADOW_OFF; Z_to_bv 64 b0; Z_to_bv 64 sa; Z_to_bv 64 sb]).
Lemma lh_E2_reg : forall regs b0 sa sb n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (lh_E2 regs b0 sa sb) n = YK11.getr regs r.
Proof. intros regs b0 sa sb n r Hn. unfold lh_E2. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma lh_E2_x : forall regs b0 sa sb,
  ew (lh_E2 regs b0 sa sb) 32 = w64 SHADOW_OFF /\ ew (lh_E2 regs b0 sa sb) 33 = Z_to_bv 64 b0 /\
  ew (lh_E2 regs b0 sa sb) 34 = Z_to_bv 64 sa /\ ew (lh_E2 regs b0 sa sb) 35 = Z_to_bv 64 sb.
Proof.
intros regs b0 sa sb. unfold lh_E2.
rewrite !Eimg_low by (unfold A_TEXT; lia).
exact (conj (ew_Ereg_extra regs _ 0) (conj (ew_Ereg_extra regs _ 1) (conj (ew_Ereg_extra regs _ 2)
  (ew_Ereg_extra regs _ 3)))).
Qed.
Lemma lh_E2_env : forall regs b0 sa sb, img_env VAL A_LIM (lh_E2 regs b0 sa sb).
Proof. intros regs b0 sa sb. unfold lh_E2. apply Eimg_env. Qed.
Lemma lh_obj5_2 : forall regs b0 sa sb, sv_denot (lh_E2 regs b0 sa sb) (SOff 246 0) = w64 TB_g_cfg.
Proof.
intros regs b0 sa sb. cbn [sv_denot]. change (ew (lh_E2 regs b0 sa sb) 246) with (ew (lh_E2 regs b0 sa sb) (A_OBJ 5)).
unfold lh_E2. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). vm_compute. reflexivity.
Qed.

(* The entry state of run A: the slots 128(s1) .. 216(s1) and the frame's header. *)
Lemma lh_entryA : forall (W : world segs) regs mem (F spv : Z),
  YK11.getr regs 2 = w64 spv -> YK11.getr regs 9 = w64 spv ->
  YK11.getr regs 10 = w64 F -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  2 ^ 46 <= spv <= 2 ^ 47 -> spv mod 32 = 0 ->
  4096 <= F -> F + 24 <= spv -> F mod 64 = 0 ->
  (forall a, spv + 128 <= a < spv + 216 -> apresent (w_H W) mem a) ->
  (forall a, F <= a < F + 24 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (lh_E regs) ss_lhA
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + LH_CA)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem F spv R2 R9 R10 R26 Hsp Hsp32 HF0 HFsp HF64 Hpslot Hpframe.
  rewrite restrict_mkst_fx. unfold ss_lhA.
  assert (U2 : bv_unsigned (ew (lh_E regs) 2) = spv)
    by (rewrite (lh_ew_reg regs 2 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew (lh_E regs) 9) = spv)
    by (rewrite (lh_ew_reg regs 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (U10 : bv_unsigned (ew (lh_E regs) 10) = F)
    by (rewrite (lh_ew_reg regs 10 10%bv eq_refl), R10; apply unsigned_lit_small; lia).
  assert (U26 : bv_unsigned (ew (lh_E regs) 26) = SHADOW_OFF)
    by (rewrite (lh_ew_reg regs 26 26%bv eq_refl), R26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U32 : bv_unsigned (ew (lh_E regs) 32) = SHADOW_OFF)
    by (rewrite (lh_ew_32 regs); apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  apply (pa_entry_st_ok_full (L := transportb_listing) (PI := PI_transportb)).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [lh_rg_slot lh_rg_hdr YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpslot. lia.
    + rewrite U10. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpframe. lia.
  - apply pairwise_disjoint_of_extents.
    unfold lh_rg_slot, lh_rg_hdr, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9, U10. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  - unfold lh_factsA, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, U10, U26, U32.
    change (2 ^ 5) with 32. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

(* The entry state of run B: the frame's 32 shadow bytes. *)
Lemma lh_entryB : forall (W : world segs) regs mem (SH : Z),
  YK11.getr regs 18 = w64 SH -> SHADOW_OFF <= SH -> SH + 32 <= 2 ^ 46 ->
  (forall a, SH <= a < SH + 32 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (lh_E regs) ss_lhB
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + LH_CB)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem SH R18 Hlo Hhi Hpres.
  rewrite restrict_mkst_fx. unfold ss_lhB.
  assert (U18 : bv_unsigned (ew (lh_E regs) 18) = SH)
    by (rewrite (lh_ew_reg regs 18 18%bv eq_refl), R18; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
  apply (pa_entry_st_ok_full (L := transportb_listing) (PI := PI_transportb)).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold lh_rg_sh, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U18. split; [unfold SHADOW_OFF in *; lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents.
    unfold lh_rg_sh, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold lh_factsB, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U18. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia.
Qed.

(* The entry state of run C1 (the return of __asan_memcpy): no region, n < 2 ^ 26. *)
Lemma lh_entryC : forall (W : world segs) regs mem (n : Z),
  YK11.getr regs 21 = w64 n -> 0 <= n < 2 ^ 26 ->
  st_ok_pi segs VAL (lh_E regs) ss_lhC
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + LH_RCPY)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem n R21 Hn. rewrite restrict_mkst_fx. unfold ss_lhC.
  assert (U21 : bv_unsigned (ew (lh_E regs) 21) = n)
    by (rewrite (lh_ew_reg regs 21 21%bv eq_refl), R21; apply unsigned_lit_small; lia).
  apply (pa_entry_st_ok_full (L := transportb_listing) (PI := PI_transportb)).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold lh_factsC, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U21. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* The entry state of run C2 (n > 0, at +0x248): the byte p[0] and the shadow byte of p, read only, with the alias
   fact naming the shadow address of p. *)
Lemma lh_entryC2 : forall (W : world segs) regs mem (p n b0 sb : Z),
  YK11.getr regs 22 = w64 p -> YK11.getr regs 21 = w64 n -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  4096 <= p <= 2 ^ 47 -> p mod 8 = 0 -> 1 <= n < 2 ^ 26 -> 0 <= b0 < 256 -> 0 <= sb <= 7 ->
  (p + 1 <= kLowShadowBeg \/ kHighMemBeg <= p) ->
  val_mem segs (mrestrict (w_H W) mem) (p + 0) 1 b0 ->
  val_mem segs (mrestrict (w_H W) mem) (SHADOW_OFF + p / 8 + 0) 1 sb ->
  st_ok_pi segs VAL (lh_E2 regs b0 (SHADOW_OFF + p / 8) sb) ss_lhC2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + LH_CC)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem p n b0 sb R22 R21 R26 Hp Hp8 Hn Hb0 Hsb Happ V0 VS.
  rewrite restrict_mkst_fx. unfold ss_lhC2.
  destruct (lh_E2_x regs b0 (SHADOW_OFF + p / 8) sb) as (E32 & E33 & E34 & E35).
  pose proof (Z.div_mod p 8 ltac:(lia)) as DP.
  assert (HP8 : 0 <= p / 8 <= 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  assert (E22 : ew (lh_E2 regs b0 (SHADOW_OFF + p / 8) sb) 22 = w64 p)
    by (rewrite (lh_E2_reg regs b0 _ sb 22 22%bv eq_refl); exact R22).
  assert (E26 : ew (lh_E2 regs b0 (SHADOW_OFF + p / 8) sb) 26 = w64 SHADOW_OFF)
    by (rewrite (lh_E2_reg regs b0 _ sb 26 26%bv eq_refl); exact R26).
  assert (U22 : bv_unsigned (ew (lh_E2 regs b0 (SHADOW_OFF + p / 8) sb) 22) = p)
    by (rewrite E22; apply unsigned_lit_small; lia).
  assert (U21 : bv_unsigned (ew (lh_E2 regs b0 (SHADOW_OFF + p / 8) sb) 21) = n)
    by (rewrite (lh_E2_reg regs b0 _ sb 21 21%bv eq_refl), R21; apply unsigned_lit_small; lia).
  assert (U26 : bv_unsigned (ew (lh_E2 regs b0 (SHADOW_OFF + p / 8) sb) 26) = SHADOW_OFF)
    by (rewrite E26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U33 : bv_unsigned (ew (lh_E2 regs b0 (SHADOW_OFF + p / 8) sb) 33) = b0)
    by (rewrite E33; apply unsigned_lit_small; lia).
  assert (U34 : bv_unsigned (ew (lh_E2 regs b0 (SHADOW_OFF + p / 8) sb) 34) = SHADOW_OFF + p / 8)
    by (rewrite E34; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U35 : bv_unsigned (ew (lh_E2 regs b0 (SHADOW_OFF + p / 8) sb) 35) = sb)
    by (rewrite E35; apply unsigned_lit_small; lia).
  apply (pa_entry_st_ok_full (L := transportb_listing) (PI := PI_transportb)).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [lh_rg_in lh_rg_sp YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs _ _ p 0 1 (SOff 33 0) b0);
        [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | lia | lia | exact V0].
    + rewrite U34. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs _ _ (SHADOW_OFF + p / 8) 0 1 (SOff 35 0) sb);
        [cbn [sv_denot]; rewrite U35, Z.add_0_r; reflexivity | lia | lia | exact VS].
  - apply pairwise_disjoint_of_extents.
    unfold lh_rg_in, lh_rg_sp, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U22, U34. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
    repeat split; first [exact I | lia].
  - unfold lh_factsC2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U21, U22, U26, U33, U34, U35.
    change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SHADOW_OFF in *; lia).
    rewrite (can_denot_shadow _ 22 26 p SHADOW_OFF E22 E26 ltac:(lia) ltac:(unfold SHADOW_OFF; lia)
      ltac:(unfold SHADOW_OFF; lia)).
    cbn [sv_denot]. rewrite U34, Z.add_0_r. reflexivity.
Qed.

(* A region's 1-byte chunks, read through the view: lh_bytes_ok checks (by computation) that byte i of l is the chunk at
   offset i, whose value is a literal or an atom of vals (an atom whose value the caller knows). *)
Definition lh_val_of (vals : list (nat * Z)) (e : sv) : option Z :=
  match e with
  | SLit z => Some z
  | SOff n 0 => match find (fun q => Nat.eqb (fst q) n) vals with Some q => Some (snd q) | None => None end
  | _ => None
  end.
Definition lh_byte_isb (vals : list (nat * Z)) (c : YP09.chunk) (o v : Z) : bool :=
  match c with
  | YP09.mkChunk o' (CVal w e) =>
      N.eqb w 1 && (o' =? o) &&
      match lh_val_of vals e with Some z => bv_unsigned (byte_of_word (Z_to_bv 64 z) 0) =? v | None => false end
  | _ => false
  end.
Definition lh_bytes_ok (vals : list (nat * Z)) (cs : list YP09.chunk) (l : list Z) : bool :=
  forallb (fun i => existsb (fun c => lh_byte_isb vals c (Z.of_nat i) (nth i l 0)) cs) (seq 0 (length l)).
Lemma lh_val_of_ok : forall E vals e z, (forall n z0, In (n, z0) vals -> ew E n = Z_to_bv 64 z0) ->
  lh_val_of vals e = Some z -> sv_denot E e = Z_to_bv 64 z.
Proof.
intros E vals e z Hv He. destruct e as [z1 | n c | | | | | | | | | ]; cbn [lh_val_of] in He; try discriminate He.
all: try (injection He as <-; reflexivity).
destruct c; try discriminate He.
destruct (find (fun q => Nat.eqb (fst q) n) vals) as [[n1 z1]|] eqn:Ef; [|discriminate He].
injection He as <-. apply find_some in Ef as (Hin & Hn). cbn [fst snd] in *. apply Nat.eqb_eq in Hn. subst n1.
cbn [sv_denot]. rewrite (Hv n z1 Hin), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma lh_region_bytes : forall E (H : word -> bool) (m : word -> option byte) n b lo hi wlo whi cs vals (l : list Z),
  region_ok segs E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  (forall n0 z0, In (n0, z0) vals -> ew E n0 = Z_to_bv 64 z0) ->
  lh_bytes_ok vals cs l = true ->
  forall i, (i < length l)%nat -> aview segs H m (b + Z.of_nat i) = Some (nth i l 0).
Proof.
intros E H m n b lo hi wlo whi cs vals l HR Hb Hv Hok i Hi.
unfold lh_bytes_ok in Hok. rewrite forallb_forall in Hok.
specialize (Hok i (proj2 (in_seq _ _ _) (conj (Nat.le_0_l i) Hi))).
apply existsb_exists in Hok as (c & Hc & Hck).
destruct HR as (_ & _ & _ & Hcs). rewrite Forall_forall in Hcs. specialize (Hcs c Hc).
cbn [YP09.r_base base_val] in Hcs. rewrite Hb in Hcs.
destruct c as [o' cv]. destruct cv as [w e | len | len | d s0 len]; unfold lh_byte_isb in Hck; try discriminate Hck.
destruct (lh_val_of vals e) as [z|] eqn:Ez; [|rewrite andb_false_r in Hck; discriminate Hck].
apply andb_prop in Hck as [Hck H3]. apply andb_prop in Hck as [H1 H2].
apply N.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. subst w o'.
destruct (Hcs 0 ltac:(cbn; lia)) as (bb & Hcb & Hmb).
cbn [cbyte YP09.c_val YP09.c_off] in Hcb, Hmb. rewrite (lh_val_of_ok E vals e z Hv Ez) in Hcb. injection Hcb as <-.
rewrite Z.add_0_r in Hmb. unfold aview. rewrite Hmb. cbn [option_map]. rewrite H3. reflexivity.
Qed.
End ent.

(* A callee-saved register at the machine state of HS, from the equation Q of its value at the run's start, for a run
   whose valuation is lh_E over the start registers rg. *)
Ltac lh_kreg HS rg r n Q H :=
  lazymatch type of Q with _ = ?v =>
    lh_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (lh_ew_reg rg n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
(* The same for a run whose valuation is lh_E2 over the start registers rg. *)
Ltac lh_kreg2 HS rg b0 sa sb r n Q H :=
  lazymatch type of Q with _ = ?v =>
    lh_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (lh_E2_reg rg b0 sa sb n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.

(* ------------------------------------------------------------------ *)
(* 3. The core across the segment's writes and its call               *)
(* ------------------------------------------------------------------ *)

Section hdr. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* Every byte of the caller's stack window is present at any memory of the G journal. *)
Lemma lh_jpres : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' (W' : world segs) mem' md' k,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own
    ly' S' W' mem' md' k ->
  forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ.
pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact Hp.
Qed.

(* The bytes the segment writes before the call of diginet_session_config_default: the memcpy's window below sp1 and
   the slots above it, the frame's bytes but its last word, and the frame's shadow. *)
Definition lh_wr (cx : lcx) (a : Z) : Prop :=
  lc_sp1 cx - ESTACK <= a < lc_sp1 cx + 216 \/ lc_F cx <= a < lc_F cx + 248 \/ lc_SH cx <= a < lc_SH cx + 32.

(* The frame, its shadow, the input block and the stack, apart. *)
Lemma lh_apart : forall cx ly' S' (W' : world segs) regs' mem' md' e,
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx -> @lc_core rc B cx ly' S' W' regs' mem' md' e ->
  (* the saved words *)
  (forall a, lc_sp0 cx - 104 <= a < lc_sp0 cx -> ~ lh_wr cx a /\ 0 <= a < 2 ^ 64) /\
  (* the frame's last word *)
  (forall a, lc_F cx + 248 <= a < lc_F cx + 256 -> ~ lh_wr cx a /\ 0 <= a < 2 ^ 64) /\
  (* the input's bytes *)
  (0 < l_n cx -> forall a, l_p cx <= a < l_p cx + l_n cx -> ~ lh_wr cx a /\ 0 <= a < 2 ^ 64) /\
  (* the frame's bytes are outside the shadow band and the stack *)
  (forall a, lc_F cx <= a < lc_F cx + 256 -> ~ (lc_SH cx <= a < lc_SH cx + 32) /\ a < lc_sp1 cx - ESTACK) /\
  (* the frame's shadow is below the stack and above the image *)
  lc_SH cx + 32 < lc_sp1 cx - ESTACK /\ kLowMemEnd <= lc_SH cx.
Proof.
intros cx ly' S' W' regs' mem' md' e LAWS HB HC.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
destruct HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal & HFceil &
  HFpres & HFL & HIN).
pose proof asan_consts as ((CVlo & CVhi) & C2 & C3 & C4 & C5).
destruct Hstk as (Hceil & Hslo & Hshi & H47). change (2 ^ 47) with 140737488355328 in H47.
destruct (al_frames _ _ LAWS _ _ _ _ _ LF_CID (l_fpos cx) HARg HFin) as (_ & HFapp & _ & _).
rewrite HFaddr in HFapp. change (fs_frame_bytes LF_CID) with LF_FBYTES in HFapp.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
unfold lh_wr, lc_SH, LF_FBYTES, LF_FRAME, ESTACK, SHADOW_OFF, kLowMemEnd in *.
pose proof (Z.div_mod (lc_F cx) 8 ltac:(lia)) as DF. pose proof (Z.mod_pos_bound (lc_F cx) 8 ltac:(lia)) as MF.
assert (Hes : 0x7fff7f800000 <= alloc_ceiling) by lia.
split; [intros a Ha; split; [lia | lia]|].
split; [intros a Ha; split; [lia | lia]|].
split.
{ intros Hn0 a Ha. pose proof (HINg Hn0) as Hin.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARg Hin) as (_ & Hb4096 & Hbce & Hbapp & _).
  pose proof (sep_block_frame segs B LAWS _ _ _ _ _ _ _ LF_CID (l_fpos cx) HARg Hin HFin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFaddr in Hd. change (fs_frame_bytes LF_CID) with 256 in Hd.
  pose proof (req_size_pos (l_n cx) ltac:(lia)) as (Hq1 & Hq2).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
  split; [lia | lia]. }
split; [intros a Ha; split; lia|].
split; lia.
Qed.

(* A run or the memcpy, which keep the journal's frames and blocks, the bytes outside lh_wr, the registers sp, s0,
   s1, gp, tp and presence, keep the core (st.v lc_core_kept_run). *)
Lemma lh_core_step : forall cx ly' S' (W : world segs) regs' mem' md' e regs2 mem2 md2 e2,
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx -> @lc_core rc B cx ly' S' W regs' mem' md' e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] LLVMF_STK (lc_sp0 cx) []
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly' S' W mem2 md2 e2 ->
  YK11.getr regs2 2 = YK11.getr regs' 2 -> YK11.getr regs2 8 = YK11.getr regs' 8 ->
  YK11.getr regs2 9 = YK11.getr regs' 9 -> YK11.getr regs2 3 = YK11.getr regs' 3 ->
  YK11.getr regs2 4 = YK11.getr regs' 4 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ lh_wr cx a -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem' a) ->
  (forall a, apresent (w_H W) mem' a -> apresent (w_H W) mem2 a) ->
  @lc_core rc B cx ly' S' W regs2 mem2 md2 e2.
Proof.
intros cx ly' S' W regs' mem' md' e regs2 mem2 md2 e2 LAWS HB HC HJ2 E2 E8 E9 E3 E4 KP GP.
destruct (lh_apart cx ly' S' W regs' mem' md' e LAWS HB HC) as (AS & AF & AI & _ & _ & _).
apply (lc_core_kept_run B MT XL RLO RHI cx ly' S' W regs' mem' md' e ly' S' W regs2 mem2 md2 e2 HB HC HJ2 eq_refl
  (Permutation_refl _)).
- intros r Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | []]]]]]; [exact E2 | exact E3 | exact E4 | exact E8 | exact E9].
- intros a Ha. destruct (AS a Ha) as [Hw Hr]. exact (KP a Hr Hw).
- intros i Hi. destruct (AI ltac:(lia) (l_p cx + i) ltac:(lia)) as [Hw Hr]. exact (KP _ Hr Hw).
- intros a Ha. destruct (AF a ltac:(unfold LF_FBYTES in Ha; lia)) as [Hw Hr]. exact (KP a Hr Hw).
- intros a _ Hp. exact (GP a Hp).
Qed.

(* g_cfg's bytes, the range diginet_session_config_default writes, are image bytes (bytes of G). *)
Lemma lh_scfg_img : forall a, scfg_wr a -> in_img segs a.
Proof.
intros a Ha. apply trans_g_img. unfold inG. apply Exists_exists. eexists. split.
- exact (TMAP_B_in_G _ _ _ TMAP_B_g_cfg).
- unfold scfg_wr, SCFG_C in Ha. unfold in_zr. cbn [fst snd]. lia.
Qed.

(* +0x354: the call of diginet_session_config_default (lp_scfg) in the walk's G journal, from the world Bw0 of the
   entry memory; its post is the cut lc_st_cfgd (the core by st.v lc_core_kept over its acall_kept_g). *)
Lemma lh_call : forall (cx : lcx) ly' S' (W : world segs) regsF memF mdF Bw0,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_core rc B cx ly' S' W regsF memF mdF 0 -> lc_fr cx regsF ->
  lc_spills cx (lf_spill_sm (lc_F cx)) (aview segs (w_H W) memF) ->
  lc_fsh cx (aview segs (w_H W) memF) false false -> lc_io cx W memF -> lc_meter MT cx S' 0 ->
  lc_cur cx regsF 19 23 (lc_c1 (l_pl cx)) -> YK11.getr regsF 24 = w64 (lc_flags (l_pl cx)) ->
  YK11.getr regsF 21 = w64 TB_g_cfg -> YK11.getr regsF 20 = w64 (lc_F cx + 176) ->
  YK11.getr regsF 10 = w64 SCFG_C -> YK11.getr regsF 1 = Z_to_bv 64 (BASE + LH_RCFG) ->
  lc_w0 cx Bw0 -> lc_tw W memF Bw0 ->
  SRr segs W (mkCfg (@YK11.mkst (l_fx cx) regsF (Z_to_bv 64 (transportb_sigma TB_diginet_session_config_default))
    memF (YK11.seg_rom segs)) mdF) (@lc_st_cfgd rc B MT cx).
Proof.
intros cx ly' S' W regsF memF mdF Bw0 HP HB HC HFR HSP HFS HIO HMT HCUR R24 R21 R20 R10 R1 HW0 HTW.
destruct (TS0.diginet_session_config_default_m Bw0) as [[B1 []]|] eqn:EC;
  [| exfalso; unfold TS0.diginet_session_config_default_m in EC; discriminate EC].
pose proof HC as HC0.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W regsF memF mdF 0 HB HC0) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
destruct HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal & HFceil &
  HFpres & HFL & HIN).
pose proof HB as HB1. unfold lc_base, tfib_lib_pre_x in HB1.
destruct HB1 as (_ & _ & _ & _ & _ & _ & _ & _ & Hev & _).
pose proof asan_consts as ((CVlo & CVhi) & _).
destruct Hstk as (Hceil & Hslo & Hshi & H47). change (2 ^ 47) with 140737488355328 in H47.
assert (Usp : spZ regsF = lc_sp1 cx)
  by (unfold spZ; rewrite Rsp; apply unsigned_lit_small; unfold LF_FRAME in *; lia).
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (lp_meter_laws _ _ _ _ _ HP) as MTL.
assert (EBR : BASE + LH_RCFG = transportb_text + LO_CFGD) by (vm_compute; reflexivity).
eapply SRr_mono.
{ refine (lp_scfg _ _ _ _ _ HP (l_fx cx) LLVMF_STK (lc_sp0 cx) _ (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx)
    [(LF_CID, l_fpos cx)] ly' S' W memF mdF 0 regsF Bw0 B1 HJ _ _ Rgp Rtp R10 _ _ _ HTW EC _).
  - rewrite R1. apply (ret_ok_codeptr_v (PI := PI_transportb)); [unfold LH_RCFG, AF_LLVMFuzzerTestOneInput; lia | reflexivity].
  - unfold raZ. rewrite R1, EBR. unfold transportb_text, LO_CFGD. rewrite unsigned_lit_small by lia. lia.
  - rewrite Usp. rewrite <- (Z.mod_mod (lc_sp1 cx) 16) by lia.
    pose proof (Z.div_mod (lc_sp1 cx) 32 ltac:(lia)) as D. rewrite Hsp1al, Z.add_0_r in D. rewrite D.
    replace (32 * (lc_sp1 cx / 32)) with ((2 * (lc_sp1 cx / 32)) * 16) by ring. rewrite Z.mod_mul by lia. reflexivity.
  - rewrite Usp. unfold SCFG_STK, SCFG_FRAME, ESTACK, LLVMF_STK, LF_FRAME in *. lia.
  - rewrite Usp. unfold LF_FRAME in *. lia.
  - unfold SCFG_EV, EV_LIB in *. lia. }
intros W2 c2 _ HPOST.
unfold transport_scfg_post, transport_cg_post in HPOST.
destruct HPOST as (ly2 & S2 & regs2 & mem2 & md2 & e & Ec & He & HJ2 & HPR & Hfr2 & Hperm2 & HK & HMO & HTW2).
unfold SCFG_EV in He. assert (Ee : e = 0) by lia. subst e. cbn [Z.add] in HJ2.
rewrite Usp in HK.
destruct HK as (KA1 & KA2 & KA3 & KA4 & KA5 & KA6).
assert (Hin0 : In (LF_CID, l_fpos cx) (frames S')) by (rewrite Hfrs; left; reflexivity).
(* the frame's bytes and its shadow are not g_cfg's *)
assert (KF : forall a, lc_F cx <= a < lc_F cx + LF_FBYTES \/ lc_SH cx <= a < lc_SH cx + 32 ->
  aview segs (w_H W2) mem2 a = aview segs (w_H W) memF a).
{ intros a Ha. apply (KA4 LF_CID (l_fpos cx) a Hin0).
  - unfold in_zr, frame_rng. cbn [fst snd]. rewrite HFaddr. unfold shadow_addr.
    change (fs_frame_bytes LF_CID) with 256. unfold LF_FBYTES, lc_SH in *. lia.
  - intros Hw. destruct Ha as [Ha | Ha].
    + apply (frm_img segs B LAWS _ _ _ _ _ LF_CID (l_fpos cx) a HARg Hin0); [|exact (lh_scfg_img a Hw)].
      rewrite HFaddr. change (fs_frame_bytes LF_CID) with 256. unfold LF_FBYTES in *. lia.
    + unfold scfg_wr, SCFG_C, TB_g_cfg, TW.SZ_g_cfg, lc_SH, SHADOW_OFF in *.
      pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)). lia. }
assert (KS : forall a, lc_sp1 cx <= a < lc_sp1 cx + 216 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memF a).
{ intros a Ha. unfold LF_FRAME in *. apply KA1; lia. }
assert (HC2 : @lc_core rc B cx ly2 S2 W2 regs2 mem2 md2 0).
{ apply (lc_core_kept B MT XL RLO RHI cx ly' S' W regsF memF mdF 0 SCFG_STK ly2 S2 W2 regs2 mem2 md2 0 HB HC0
    HJ2 Hfr2 Hperm2 HPR).
  - unfold SCFG_STK, SCFG_FRAME, ESTACK, LLVMF_STK. lia.
  - intros a Ha Hn'. exact (KA1 a Ha Hn').
  - intros i Hi. pose proof (HINg ltac:(lia)) as InP. pose proof (req_size_pos (l_n cx) ltac:(lia)) as (Hq1 & Hq2).
    apply (KA2 (l_p cx) (l_n cx) i InP ltac:(lia)). intros Hw.
    exact (blk_img segs B LAWS _ _ _ _ _ (l_p cx) (l_n cx) (l_p cx + i) HARg InP ltac:(lia) (lh_scfg_img _ Hw)).
  - intros a Ha. apply KF. left. unfold LF_FBYTES in *. lia.
  - intros a Ha Hp. apply (apresent_transfer segs (w_H W) (w_H W2) memF mem2 a).
    + unfold LF_FBYTES in *. change (2 ^ 64) with 18446744073709551616. lia.
    + apply (frm_img segs B LAWS ly' S' W memF mdF LF_CID (l_fpos cx) a HARg Hin0).
      rewrite HFaddr. change (fs_frame_bytes LF_CID) with LF_FBYTES. exact Ha.
    + apply KF. left. exact Ha.
    + exact Hp. }
destruct HFR as (F18 & F26). destruct HCUR as (C19 & C23). destruct HMT as (HMle & HMok).
exists ly2, S2, regs2, mem2, md2, Bw0, B1.
split; [rewrite Ec, R1, EBR; reflexivity|].
split; [exact HC2|].
split; [split; [exact (eq_trans (HPR 18 ltac:(unfold acallee_saved; lia)) F18)
               | exact (eq_trans (HPR 26 ltac:(unfold acallee_saved; lia)) F26)]|].
split.
{ apply (lc_spills_kept cx _ (aview segs (w_H W) memF)); [| exact KS | exact HSP].
  intros o Ho. cbn [lf_spill_sm In] in Ho. destruct Ho as [<- | [<- | []]]; cbn; lia. }
split.
{ apply (lc_fsh_kept cx (aview segs (w_H W) memF)); [|exact HFS]. intros a Ha. apply KF. right. exact Ha. }
split.
{ unfold lc_io in *. apply (lc_garr8_kept (w_H W) (w_H W2) memF mem2 (lc_F cx + 176) _); [|exact HIO].
  intros j Hj.
  assert (Lio : length (TW.zs (sinit_io_bytes 0 (TI.ti_io_send timg_B) (TI.ti_io_recv timg_B)
    (TI.ti_io_now timg_B))) = 32%nat) by (vm_compute; reflexivity).
  rewrite Lio in Hj. apply KF. left. unfold LF_FBYTES. lia. }
split.
{ split.
  - pose proof (mo_le_trans MT MTL _ _ _ _ _ HMle HMO) as Hm. rewrite Z.add_0_r in Hm. exact Hm.
  - apply (mo_ok_step MT MTL S' S2 0); [rewrite Z.add_0_l; exact HMok | exact HMO]. }
split; [split; [exact (eq_trans (HPR 19 ltac:(unfold acallee_saved; lia)) C19)
               | exact (eq_trans (HPR 23 ltac:(unfold acallee_saved; lia)) C23)]|].
split; [exact (eq_trans (HPR 24 ltac:(unfold acallee_saved; lia)) R24)|].
split; [exact (eq_trans (HPR 21 ltac:(unfold acallee_saved; lia)) R21)|].
split; [exact (eq_trans (HPR 20 ltac:(unfold acallee_saved; lia)) R20)|].
split; [exact HW0|].
split; [exact EC | exact HTW2].
Qed.

(* ------------------------------------------------------------------ *)
(* 4. From the return of __asan_memcpy to the call                     *)
(* ------------------------------------------------------------------ *)

(* +0x180 .. +0x354: the size test, the flags byte and the call of diginet_session_config_default. *)
Lemma lh_runc : forall (cx : lcx) ly' S' (W : world segs) regs3 mem3 md3 Bw0,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_core rc B cx ly' S' W regs3 mem3 md3 0 -> lc_fr cx regs3 ->
  lc_spills cx (lf_spill_sm (lc_F cx)) (aview segs (w_H W) mem3) ->
  lc_fsh cx (aview segs (w_H W) mem3) false false -> lc_io cx W mem3 -> lc_meter MT cx S' 0 ->
  YK11.getr regs3 22 = w64 (l_p cx) -> YK11.getr regs3 21 = w64 (l_n cx) ->
  YK11.getr regs3 20 = w64 (lc_F cx + 176) ->
  lc_w0 cx Bw0 -> lc_tw W mem3 Bw0 ->
  SRr segs W (mkCfg (@YK11.mkst (l_fx cx) regs3 (Z_to_bv 64 (BASE + LH_RCPY)) mem3 (YK11.seg_rom segs)) md3)
    (@lc_st_cfgd rc B MT cx).
Proof.
intros cx ly' S' W regs3 mem3 md3 Bw0 HP HB HC HFR HSP HFS HIO HMT R22 R21 R20 HW0 HTW.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W regs3 mem3 md3 0 HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof HC as HC'.
destruct HC' as (HJ & _ & _ & _ & R2 & R8 & R9 & R3 & R4 & Hsp1 & _ & _ & HF4096 & HFal & HFceil & _).
pose proof asan_consts as ((CVlo & CVhi) & _).
destruct Hstk as (Hceil & Hslo & Hshi & H47). change (2 ^ 47) with 140737488355328 in H47.
unfold LF_FRAME, LF_FBYTES in *.
assert (HF8 : 0 <= lc_F cx / 8 <= lc_F cx) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
(* the call, from any of the paths: the cut's facts at a memory whose view is mem3's *)
assert (JOIN : forall regsF memF mdF,
  @lc_core rc B cx ly' S' W regsF memF mdF 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W) memF a = aview segs (w_H W) mem3 a) ->
  YK11.getr regsF 18 = YK11.getr regs3 18 -> YK11.getr regsF 26 = YK11.getr regs3 26 ->
  YK11.getr regsF 20 = YK11.getr regs3 20 ->
  lc_cur cx regsF 19 23 (lc_c1 (l_pl cx)) -> YK11.getr regsF 24 = w64 (lc_flags (l_pl cx)) ->
  YK11.getr regsF 21 = w64 TB_g_cfg -> YK11.getr regsF 10 = w64 SCFG_C ->
  YK11.getr regsF 1 = Z_to_bv 64 (BASE + LH_RCFG) ->
  SRr segs W (mkCfg (@YK11.mkst (l_fx cx) regsF (Z_to_bv 64 (transportb_sigma TB_diginet_session_config_default))
    memF (YK11.seg_rom segs)) mdF) (@lc_st_cfgd rc B MT cx)).
{ intros regsF memF mdF HCF KV E18 E26 E20 HCUR Q24 Q21 Q10 Q1.
  destruct HFR as (F18 & F26).
  apply (lh_call cx ly' S' W regsF memF mdF Bw0 HP HB HCF).
  - split; [rewrite E18; exact F18 | rewrite E26; exact F26].
  - apply (lc_spills_kept cx _ (aview segs (w_H W) mem3)); [| | exact HSP].
    + intros o Ho. cbn [lf_spill_sm In] in Ho. destruct Ho as [<- | [<- | []]]; cbn; lia.
    + intros a Ha. apply KV. lia.
  - apply (lc_fsh_kept cx (aview segs (w_H W) mem3)); [|exact HFS]. intros a Ha. apply KV.
    unfold lc_SH, SHADOW_OFF in *. lia.
  - unfold lc_io in *. apply (lc_garr8_kept (w_H W) (w_H W) mem3 memF (lc_F cx + 176) _); [|exact HIO].
    intros j Hj.
    assert (Lio : length (TW.zs (sinit_io_bytes 0 (TI.ti_io_send timg_B) (TI.ti_io_recv timg_B)
      (TI.ti_io_now timg_B))) = 32%nat) by (vm_compute; reflexivity).
    rewrite Lio in Hj. apply KV. lia.
  - exact HMT.
  - exact HCUR.
  - exact Q24.
  - exact Q21.
  - rewrite E20. exact R20.
  - exact Q10.
  - exact Q1.
  - exact HW0.
  - unfold lc_tw in *. apply (tw_kept TMAP_B (aview segs (w_H W) mem3)); [exact HTW|].
    intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
    apply KV. lia. }
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := l_fx cx) (PI := PI_transportb)) as BR.
assert (Hn26 : 0 <= l_n cx < 2 ^ 26) by lia.
pose proof (@lh_entryC (l_fx cx) rc W regs3 mem3 (l_n cx) R21 Hn26) as HS.
assert (HEI : img_env VAL A_LIM (lh_E regs3)) by apply lh_env_img.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (lh_E regs3) (mrestrict (w_H W) mem3)) by constructor.
assert (E21 : ew (lh_E regs3) 21 = Z_to_bv 64 (l_n cx)) by (rewrite (lh_ew_reg regs3 21 21%bv eq_refl); exact R21).
assert (KV : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W) mem3 a = aview segs (w_H W) mem3 a) by (intros; reflexivity).
assert (GP : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) mem3 a) by (intros a Ha; exact Ha).
(* +0x180 .. +0x184: the size test *)
paj_run_tok RUN HS HJ SHOK LH_B0.
{ lh_awr_ro. }
lh_step W KV GP.
psrr_branch_tok RUN BR HS SHOK LH_B0.
2: { exfalso. rewrite (lh_srl26 _ (l_n cx) E21 Hn26) in Hc. discriminate Hc. }
clear Hc.
(* +0x244: `beqz s5` *)
paj_run_tok RUN HS HJ SHOK LH_B0.
{ lh_awr_ro. }
lh_step W KV GP.
psrr_branch_tok RUN BR HS SHOK LH_B0.
- (* n = 0: flags = 0, the cursor at p with no byte (+0x33c .. +0x354) *)
  pose proof (lh_beqz _ 21 (l_n cx) true E21 ltac:(lia) Hc) as Hn0. apply Z.eqb_eq in Hn0. clear Hc.
  assert (Epl : l_pl cx = []).
  { destruct Hn as (_ & Hnl). destruct (l_pl cx) as [|b0 pl0]; [reflexivity|]. cbn [length] in Hnl. lia. }
  paj_run_tok RUN HS HJ SHOK LH_B0.
  { lh_awr_ro. }
  lh_step W KV GP.
  lh_name HS msF.
  lh_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + LH_RCFG)) Q1 ltac:(apply codeptr_val; exact HEI).
  lh_reg HS (10%bv : bv 5) (w64 TB_g_cfg) Q10 ltac:(exact (lh_obj5 regs3)).
  lh_reg HS (21%bv : bv 5) (w64 TB_g_cfg) Q21 ltac:(exact (lh_obj5 regs3)).
  lh_reg HS (24%bv : bv 5) (w64 0) Q24 ltac:(reflexivity).
  lh_reg HS (23%bv : bv 5) (w64 0) Q23 ltac:(reflexivity).
  lh_reg HS (19%bv : bv 5) (w64 (l_p cx)) Q19
    ltac:(cbn [sv_denot]; rewrite (lh_ew_reg regs3 22 22%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R22).
  lh_kreg HS regs3 (2%bv : bv 5) 2%nat R2 Q2. lh_kreg HS regs3 (8%bv : bv 5) 8%nat R8 Q8.
  lh_kreg HS regs3 (9%bv : bv 5) 9%nat R9 Q9. lh_kreg HS regs3 (3%bv : bv 5) 3%nat R3 Q3.
  lh_kreg HS regs3 (4%bv : bv 5) 4%nat R4 Q4. lh_kreg HS regs3 (20%bv : bv 5) 20%nat R20 Q20.
  lh_reg HS (18%bv : bv 5) (YK11.getr regs3 18) Q18
    ltac:(cbn [sv_denot]; rewrite (lh_ew_reg regs3 18 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  lh_reg HS (26%bv : bv 5) (YK11.getr regs3 26) Q26
    ltac:(cbn [sv_denot]; rewrite (lh_ew_reg regs3 26 26%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 (transportb_sigma TB_diginet_session_config_default))
      mm rom) mdx) Q) end.
  apply (JOIN (ms_regs msF) (ms_mem msF) _
    (lh_core_step cx ly' S' W regs3 mem3 md3 0 (ms_regs msF) (ms_mem msF) _ _ LAWS HB HC HJ
      (eq_trans Q2 (eq_sym R2)) (eq_trans Q8 (eq_sym R8)) (eq_trans Q9 (eq_sym R9)) (eq_trans Q3 (eq_sym R3))
      (eq_trans Q4 (eq_sym R4)) (fun a Ha _ => KV a Ha) GP)
    KV Q18 Q26 (eq_trans Q20 (eq_sym R20))).
  + unfold lc_cur, lc_c1. rewrite Epl. cbn. rewrite Z.add_0_r. exact (conj Q19 Q23).
  + unfold lc_flags. rewrite Epl. exact Q24.
  + exact Q21.
  + exact Q10.
  + exact Q1.
- (* n > 0 *)
  pose proof (lh_beqz _ 21 (l_n cx) false E21 ltac:(lia) Hc) as Hn0. apply Z.eqb_neq in Hn0. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK LH_B0 LH_CC.
  { lh_awr_ro. }
  lh_step W KV GP.
  lh_name HS msX.
  lh_kreg HS regs3 (22%bv : bv 5) 22%nat R22 X22. lh_kreg HS regs3 (21%bv : bv 5) 21%nat R21 X21.
  lh_kreg HS regs3 (2%bv : bv 5) 2%nat R2 X2. lh_kreg HS regs3 (8%bv : bv 5) 8%nat R8 X8.
  lh_kreg HS regs3 (9%bv : bv 5) 9%nat R9 X9. lh_kreg HS regs3 (3%bv : bv 5) 3%nat R3 X3.
  lh_kreg HS regs3 (4%bv : bv 5) 4%nat R4 X4. lh_kreg HS regs3 (20%bv : bv 5) 20%nat R20 X20.
  lh_reg HS (18%bv : bv 5) (YK11.getr regs3 18) X18
    ltac:(cbn [sv_denot]; rewrite (lh_ew_reg regs3 18 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  lh_reg HS (26%bv : bv 5) (YK11.getr regs3 26) X26
    ltac:(cbn [sv_denot]; rewrite (lh_ew_reg regs3 26 26%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  destruct HFR as (F18 & F26).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 (BASE + LH_CC)) mm rom) mdx) Q) end.
  clear HS SHOK.
  (* the input block: p 16-aligned, its first byte, and the shadow byte of its first granule *)
  pose proof (HINg ltac:(lia)) as Hin.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARg Hin) as (Hp16 & Hp4096 & Hpce & Hpapp & _).
  pose proof (req_size_pos (l_n cx) ltac:(lia)) as (Hq1 & Hq2).
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARX.
  destruct (al_shadow _ _ LAWS _ _ _ _ _ _ _ HARX Hin) as ((Hp8 & _ & HBS) & _).
  set (sb := if 0 <? req_size (l_n cx) / 8 then 0 else req_size (l_n cx) mod 8).
  assert (HSB : aview segs (w_H W) (ms_mem msX) (SHADOW_OFF + l_p cx / 8 + 0) = Some sb).
  { pose proof (HBS 0 ltac:(split; [lia | apply Z.div_str_pos; lia])) as H0. unfold shadow_of_addr in H0. exact H0. }
  assert (Hsbr : sb = 0 \/ 0 < sb < 8).
  { unfold sb. destruct (0 <? req_size (l_n cx) / 8) eqn:E; [left; reflexivity | right].
    apply Z.ltb_ge in E.
    assert (Hr8 : req_size (l_n cx) < 8).
    { destruct (Z_lt_le_dec (req_size (l_n cx)) 8) as [Hl | Hl]; [exact Hl|].
      pose proof (Z.div_le_mono 8 (req_size (l_n cx)) 8 ltac:(lia) Hl) as Hd. rewrite Z.div_same in Hd by lia. lia. }
    rewrite Z.mod_small by lia. lia. }
  pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HPAY & _)).
  assert (HPAYX : garr8 segs (mrestrict (w_H W) (ms_mem msX)) (l_p cx) (map (fun b : byte => bv_unsigned b) (l_pl cx))).
  { apply (lc_garr8_kept (w_H W) (w_H W) mem3 (ms_mem msX) (l_p cx) _); [|exact HPAY].
    intros j Hj. apply KV. rewrite length_map in Hj. destruct Hn as (_ & Hnl). lia. }
  set (b0 := nth 0 (map (fun b : byte => bv_unsigned b) (l_pl cx)) 0).
  assert (Hlen0 : (0 < length (map (fun b : byte => bv_unsigned b) (l_pl cx)))%nat)
    by (rewrite length_map; destruct Hn as (_ & Hnl); lia).
  destruct (HPAYX 0%nat Hlen0) as (V0 & Hb0).
  change (l_p cx + Z.of_nat 0) with (l_p cx + 0) in V0.
  pose proof (YE2y.val_mem1_of_aview (w_H W) (ms_mem msX) _ _ HSB) as VS.
  assert (Happ : l_p cx + 1 <= kLowShadowBeg \/ kHighMemBeg <= l_p cx).
  { unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
    destruct Hpapp as (_ & [H1 | (H1 & _)]); [left; unfold kLowShadowBeg; lia | right; unfold kHighMemBeg; exact H1]. }
  pose proof (@lh_entryC2 (l_fx cx) rc W (ms_regs msX) (ms_mem msX) (l_p cx) (l_n cx) b0 sb
    X22 X21 (eq_trans X26 F26) ltac:(lia) Hp8 ltac:(lia) Hb0
    ltac:(destruct Hsbr; lia) Happ V0 VS) as HS.
  repeat match goal with H : img_env _ _ _ |- _ => clear H end.
  assert (HEI : img_env VAL A_LIM (lh_E2 (ms_regs msX) b0 (SHADOW_OFF + l_p cx / 8) sb)) by apply lh_E2_env.
  assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (lh_E2 (ms_regs msX) b0 (SHADOW_OFF + l_p cx / 8) sb)
    (mrestrict (w_H W) (ms_mem msX))) by constructor.
  (* +0x248 .. +0x264: s3 = p + 1, the UBSan cursor test (decided), the shadow byte of p *)
  paj_run_tok RUN HS HJ SHOK LH_B0.
  { lh_awr_ro. }
  lh_step W KV GP.
  destruct (lh_E2_x (ms_regs msX) b0 (SHADOW_OFF + l_p cx / 8) sb) as (E32 & E33 & E34 & E35).
  (* the facts the call reads, from the input's first byte *)
  destruct (l_pl cx) as [|x pl0] eqn:Epl; [exfalso; destruct Hn as (_ & Hnl); cbn [length] in Hnl; lia|].
  destruct (lh_c1_cons x pl0) as (Ec1 & Efl).
  assert (Eb0 : b0 = bv_unsigned x) by reflexivity.
  assert (FIN : forall regsF memF mdF,
    @lc_core rc B cx ly' S' W regsF memF mdF 0 ->
    (forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W) memF a = aview segs (w_H W) mem3 a) ->
    YK11.getr regsF 18 = YK11.getr regs3 18 -> YK11.getr regsF 26 = YK11.getr regs3 26 ->
    YK11.getr regsF 20 = YK11.getr regs3 20 ->
    YK11.getr regsF 19 = w64 (l_p cx + 1) -> YK11.getr regsF 23 = w64 (l_n cx - 1) ->
    YK11.getr regsF 24 = w64 b0 ->
    YK11.getr regsF 21 = w64 TB_g_cfg -> YK11.getr regsF 10 = w64 SCFG_C ->
    YK11.getr regsF 1 = Z_to_bv 64 (BASE + LH_RCFG) ->
    SRr segs W (mkCfg (@YK11.mkst (l_fx cx) regsF (Z_to_bv 64 (transportb_sigma TB_diginet_session_config_default))
      memF (YK11.seg_rom segs)) mdF) (@lc_st_cfgd rc B MT cx)).
  { intros regsF memF mdF HCF KVF Y18 Y26 Y20 Y19 Y23 Y24 Y21 Y10 Y1.
    apply (JOIN regsF memF mdF HCF KVF Y18 Y26 Y20); [| | exact Y21 | exact Y10 | exact Y1].
    - unfold lc_cur. rewrite Ec1. cbn [TOP.fi_off TOP.fi_n]. destruct Hn as (_ & Hnl). rewrite <- Hnl.
      exact (conj Y19 Y23).
    - rewrite Efl, <- Eb0. exact Y24. }
  psrr_branch_tok RUN BR HS SHOK LH_B0.
  + (* the shadow byte of p is 0: the fast path *)
    clear Hc.
    paj_run_tok RUN HS HJ SHOK LH_B0.
    { lh_awr_ro. }
    lh_step W KV GP.
    lh_name HS msF.
    lh_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + LH_RCFG)) Y1 ltac:(apply codeptr_val; exact HEI).
    lh_reg HS (10%bv : bv 5) (w64 TB_g_cfg) Y10 ltac:(exact (lh_obj5_2 (ms_regs msX) b0 _ sb)).
    lh_reg HS (21%bv : bv 5) (w64 TB_g_cfg) Y21 ltac:(exact (lh_obj5_2 (ms_regs msX) b0 _ sb)).
    lh_reg HS (24%bv : bv 5) (w64 b0) Y24
      ltac:(cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
    lh_reg HS (19%bv : bv 5) (w64 (l_p cx + 1)) Y19
      ltac:(cbn [sv_denot]; rewrite (lh_E2_reg (ms_regs msX) b0 _ sb 22 22%bv eq_refl), X22; unfold w64;
            rewrite unsigned_lit_small by lia; reflexivity).
    lh_reg HS (23%bv : bv 5) (w64 (l_n cx - 1)) Y23
      ltac:(cbn [sv_denot]; rewrite (lh_E2_reg (ms_regs msX) b0 _ sb 21 21%bv eq_refl), X21; unfold w64;
            rewrite unsigned_lit_small by lia; reflexivity).
    lh_kreg2 HS (ms_regs msX) b0 (SHADOW_OFF + l_p cx / 8) sb (2%bv : bv 5) 2%nat X2 Y2.
    lh_kreg2 HS (ms_regs msX) b0 (SHADOW_OFF + l_p cx / 8) sb (8%bv : bv 5) 8%nat X8 Y8.
    lh_kreg2 HS (ms_regs msX) b0 (SHADOW_OFF + l_p cx / 8) sb (9%bv : bv 5) 9%nat X9 Y9.
    lh_kreg2 HS (ms_regs msX) b0 (SHADOW_OFF + l_p cx / 8) sb (3%bv : bv 5) 3%nat X3 Y3.
    lh_kreg2 HS (ms_regs msX) b0 (SHADOW_OFF + l_p cx / 8) sb (4%bv : bv 5) 4%nat X4 Y4.
    lh_kreg2 HS (ms_regs msX) b0 (SHADOW_OFF + l_p cx / 8) sb (18%bv : bv 5) 18%nat X18 Y18.
    lh_kreg2 HS (ms_regs msX) b0 (SHADOW_OFF + l_p cx / 8) sb (26%bv : bv 5) 26%nat X26 Y26.
    lh_kreg2 HS (ms_regs msX) b0 (SHADOW_OFF + l_p cx / 8) sb (20%bv : bv 5) 20%nat X20 Y20.
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg
        (Z_to_bv 64 (transportb_sigma TB_diginet_session_config_default)) mm rom) mdx) Q) end.
    exact (FIN (ms_regs msF) (ms_mem msF) _
      (lh_core_step cx ly' S' W regs3 mem3 md3 0 (ms_regs msF) (ms_mem msF) _ _ LAWS HB HC HJ
        (eq_trans Y2 (eq_sym R2)) (eq_trans Y8 (eq_sym R8)) (eq_trans Y9 (eq_sym R9)) (eq_trans Y3 (eq_sym R3))
        (eq_trans Y4 (eq_sym R4)) (fun a Ha _ => KV a Ha) GP)
      KV Y18 Y26 (eq_trans Y20 (eq_sym R20)) Y19 Y23 Y24 Y21 Y10 Y1).
  + (* the shadow byte of p is in (0, 8): the slow path +0x1b54 .. +0x1b5c *)
    pose proof (lh_beqz _ 35 sb false E35 ltac:(destruct Hsbr; lia) Hc) as Hs0. apply Z.eqb_neq in Hs0. clear Hc.
    assert (Hsb1 : 0 < sb < 8) by (destruct Hsbr; lia).
    paj_run_tok RUN HS HJ SHOK LH_B0.
    { lh_awr_ro. }
    lh_step W KV GP.
    psrr_branch_tok RUN BR HS SHOK LH_B0.
    { exfalso. pose proof (lh_bge _ sb true E35 Hsb1 Hc). discriminate. }
    clear Hc.
    paj_run_tok RUN HS HJ SHOK LH_B0.
    { lh_awr_ro. }
    lh_step W KV GP.
    lh_name HS msF.
    lh_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + LH_RCFG)) Y1 ltac:(apply codeptr_val; exact HEI).
    lh_reg HS (10%bv : bv 5) (w64 TB_g_cfg) Y10 ltac:(exact (lh_obj5_2 (ms_regs msX) b0 _ sb)).
    lh_reg HS (21%bv : bv 5) (w64 TB_g_cfg) Y21 ltac:(exact (lh_obj5_2 (ms_regs msX) b0 _ sb)).
    lh_reg HS (24%bv : bv 5) (w64 b0) Y24
      ltac:(cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
    lh_reg HS (19%bv : bv 5) (w64 (l_p cx + 1)) Y19
      ltac:(cbn [sv_denot]; rewrite (lh_E2_reg (ms_regs msX) b0 _ sb 22 22%bv eq_refl), X22; unfold w64;
            rewrite unsigned_lit_small by lia; reflexivity).
    lh_reg HS (23%bv : bv 5) (w64 (l_n cx - 1)) Y23
      ltac:(cbn [sv_denot]; rewrite (lh_E2_reg (ms_regs msX) b0 _ sb 21 21%bv eq_refl), X21; unfold w64;
            rewrite unsigned_lit_small by lia; reflexivity).
    lh_kreg2 HS (ms_regs msX) b0 (SHADOW_OFF + l_p cx / 8) sb (2%bv : bv 5) 2%nat X2 Y2.
    lh_kreg2 HS (ms_regs msX) b0 (SHADOW_OFF + l_p cx / 8) sb (8%bv : bv 5) 8%nat X8 Y8.
    lh_kreg2 HS (ms_regs msX) b0 (SHADOW_OFF + l_p cx / 8) sb (9%bv : bv 5) 9%nat X9 Y9.
    lh_kreg2 HS (ms_regs msX) b0 (SHADOW_OFF + l_p cx / 8) sb (3%bv : bv 5) 3%nat X3 Y3.
    lh_kreg2 HS (ms_regs msX) b0 (SHADOW_OFF + l_p cx / 8) sb (4%bv : bv 5) 4%nat X4 Y4.
    lh_kreg2 HS (ms_regs msX) b0 (SHADOW_OFF + l_p cx / 8) sb (18%bv : bv 5) 18%nat X18 Y18.
    lh_kreg2 HS (ms_regs msX) b0 (SHADOW_OFF + l_p cx / 8) sb (26%bv : bv 5) 26%nat X26 Y26.
    lh_kreg2 HS (ms_regs msX) b0 (SHADOW_OFF + l_p cx / 8) sb (20%bv : bv 5) 20%nat X20 Y20.
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg
        (Z_to_bv 64 (transportb_sigma TB_diginet_session_config_default)) mm rom) mdx) Q) end.
    exact (FIN (ms_regs msF) (ms_mem msF) _
      (lh_core_step cx ly' S' W regs3 mem3 md3 0 (ms_regs msF) (ms_mem msF) _ _ LAWS HB HC HJ
        (eq_trans Y2 (eq_sym R2)) (eq_trans Y8 (eq_sym R8)) (eq_trans Y9 (eq_sym R9)) (eq_trans Y3 (eq_sym R3))
        (eq_trans Y4 (eq_sym R4)) (fun a Ha _ => KV a Ha) GP)
      KV Y18 Y26 (eq_trans Y20 (eq_sym R20)) Y19 Y23 Y24 Y21 Y10 Y1).
Qed.

(* ------------------------------------------------------------------ *)
(* 5. The segment                                                      *)
(* ------------------------------------------------------------------ *)

Lemma lc_hdr_ok (K1 : lc_rom_view_stmt B MT XL RLO RHI) : lc_hdr_stmt B MT XL RLO RHI.
Proof.
unfold lc_hdr_stmt. intros HP cx W' c' HB HSM.
destruct HSM as (ly' & S' & regs' & mem' & md' & -> & HJ & Hfrs & HlyF & Eab & R2 & R8 & R9 & R3 & R4 & R10 & R22 & R21
  & R26 & Hsp1 & Hsp1al & HSAV & HF4096 & HFal & HFceil & HFpres & HFL & Hz & HGk & HIN & HMT).
assert (HC0 : @lc_core rc B cx ly' S' W' regs' mem' md' 0).
{ refine (conj HJ (conj Hfrs (conj HlyF (conj _ (conj R2 (conj R8 (conj R9 (conj R3 (conj R4 (conj Hsp1 (conj Hsp1al
    (conj HSAV (conj HF4096 (conj HFal (conj HFceil (conj HFpres (conj HFL HIN))))))))))))))))).
  rewrite Eab. apply Permutation_refl. }
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' 0 HB HC0) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof asan_consts as ((CVlo & CVhi) & _).
destruct Hstk as (Hceil & Hslo & Hshi & H47). change (2 ^ 47) with 140737488355328 in H47.
unfold LLVMF_STK in Hslo. unfold LF_FRAME, LF_FBYTES in Hsp1, HFceil.
(* the world at the entry memory (its G payload bytes are image bytes, visible) *)
destruct (tw_exists_B (aview segs (w_H (l_W cx)) (l_mem cx))) as (Bw0 & HTW0).
{ intros o b n i Hin Hi.
  assert (Hg : inG TG.G_HARNESS_B (b + i)).
  { unfold inG. apply Exists_exists. exists (b, n).
    split; [exact (TMAP_B_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia]. }
  pose proof (gx_rw_vis segs TG.G_HARNESS_B (b + i) G_HARNESS_B_rw Hg (w_H (l_W cx)) (l_mem cx)) as Hv.
  destruct (aview segs (w_H (l_W cx)) (l_mem cx) (b + i)) as [v|] eqn:Ev; [|exfalso; exact (Hv eq_refl)].
  exists v. split; [reflexivity|].
  destruct (aview_byte segs _ _ _ _ Ev) as (bb & _ & -> & Hr). exact Hr. }
assert (HW0 : lc_w0 cx Bw0) by exact (conj HTW0 (tw_len _ _ _ HTW0)).
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
(* run A, +0x074 .. +0x0e0 *)
assert (EA : BASE + LH_CA = transportb_text + LO_SM) by (vm_compute; reflexivity).
unfold lc_cfg. rewrite <- EA. unfold w64.
pose proof (@lh_entryA (l_fx cx) rc W' regs' mem' (lc_F cx) (lc_sp1 cx) R2 R9 R10 R26 ltac:(lia) Hsp1al HF4096
  ltac:(lia) HFal
  ltac:(intros a Ha; apply (lh_jpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); unfold LLVMF_STK; lia)
  ltac:(intros a Ha; apply HFpres; unfold LF_FBYTES; lia)) as HS.
assert (HEI : img_env VAL A_LIM (lh_E regs')) by apply lh_env_img.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (lh_E regs') (mrestrict (w_H W') mem')) by constructor.
assert (U9 : bv_unsigned (ew (lh_E regs') 9) = lc_sp1 cx)
  by (rewrite (lh_ew_reg regs' 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew (lh_E regs') 10) = lc_F cx)
  by (rewrite (lh_ew_reg regs' 10 10%bv eq_refl), R10; apply unsigned_lit_small; lia).
paj_run_to_tok RUNTO HS HJ SHOK LH_B0 LH_CB.
{ lh_awr_rs.
  apply awr_ok_x_cons;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9 in Ha;
    left; split; [unfold awr_byte; left; unfold LLVMF_STK; lia | lia] |].
  eapply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ LF_CID (l_fpos cx)); [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U10 in Ha.
  left. unfold in_zr. cbn [fst snd]. rewrite HFaddr. change (fs_frame_bytes LF_CID) with 256. lia. }
lh_name HS msA.
lh_kept W' HFr HG (fun x => lc_sp1 cx + 128 <= x < lc_sp1 cx + 216 \/ lc_F cx <= x < lc_F cx + 24) KA
  ltac:(rewrite ?U9, ?U10 in Hx; first [left; lia | right; lia]).
pose proof HG as GA. clear HF HFr HG.
assert (HF8 : 0 <= lc_F cx / 8 <= lc_F cx) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
assert (E10 : ew (lh_E regs') 10 = Z_to_bv 64 (lc_F cx)) by (rewrite (lh_ew_reg regs' 10 10%bv eq_refl); exact R10).
assert (E26 : ew (lh_E regs') 26 = Z_to_bv 64 SHADOW_OFF) by (rewrite (lh_ew_reg regs' 26 26%bv eq_refl); exact R26).
lh_reg HS (18%bv : bv 5) (Z_to_bv 64 (SHADOW_OFF + lc_F cx / 8)) A18
  ltac:(exact (can_denot_shadow (lh_E regs') 10 26 (lc_F cx) SHADOW_OFF E10 E26 ltac:(lia)
                 ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia))).
lh_reg HS (20%bv : bv 5) (w64 (lc_F cx + 176)) A20 ltac:(cbn [sv_denot]; rewrite U10; reflexivity).
lh_reg HS (10%bv : bv 5) (Z_to_bv 64 18446744073709551601) A10 ltac:(reflexivity).
lh_reg HS (14%bv : bv 5) (Z_to_bv 64 18446744073709551608) A14 ltac:(reflexivity).
lh_kreg HS regs' (2%bv : bv 5) 2%nat R2 A2. lh_kreg HS regs' (8%bv : bv 5) 8%nat R8 A8.
lh_kreg HS regs' (9%bv : bv 5) 9%nat R9 A9. lh_kreg HS regs' (3%bv : bv 5) 3%nat R3 A3.
lh_kreg HS regs' (4%bv : bv 5) 4%nat R4 A4. lh_kreg HS regs' (22%bv : bv 5) 22%nat R22 A22.
lh_kreg HS regs' (21%bv : bv 5) 21%nat R21 A21. lh_kreg HS regs' (26%bv : bv 5) 26%nat R26 A26.
(* the two slots of the frame *)
lh_region HS 0%nat HRsl.
assert (HSPA : lc_spills cx (lf_spill_sm (lc_F cx)) (aview segs (w_H W') (ms_mem msA))).
{ unfold lc_spills, lf_spill_sm. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  (apply (YF0x.val_mem_rdword (w_H W') (ms_mem msA) _ (lc_F cx) ltac:(lia));
   apply (can_field_of_region (lh_E regs') _ 9 (lc_sp1 cx) _ 128 216 128 216 _ 8%N (SOff 10 0) (lc_F cx) HRsl U9);
   [ cbn [In]; repeat (first [left; reflexivity | right])
   | cbn [sv_denot]; rewrite U10, Z.add_0_r; reflexivity | cbn; lia | cbn; lia ]). }
clear HRsl.
(* run B, +0x0e4 .. +0x17c *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 (BASE + LH_CB)) mm rom) mdx) Q) end.
clear HS SHOK.
destruct (al_frames _ _ LAWS _ _ _ _ _ LF_CID (l_fpos cx) HARg HFin) as (_ & HFapp & _ & HFsh).
rewrite HFaddr in HFapp, HFsh. change (fs_frame_bytes LF_CID / 8) with 32 in HFsh.
change (fs_frame_bytes LF_CID) with 256 in HFapp.
pose proof (@lh_entryB (l_fx cx) rc W' (ms_regs msA) (ms_mem msA) (lc_SH cx) A18 ltac:(unfold lc_SH; lia)
  ltac:(unfold lc_SH, SHADOW_OFF; lia)
  ltac:(intros a Ha; apply (apresent_grows _ _ _ a GA);
        replace a with (shadow_addr (lc_F cx) + (a - lc_SH cx)) by (unfold shadow_addr, lc_SH; lia);
        exact (proj1 (HFsh (a - lc_SH cx) ltac:(unfold lc_SH in *; lia))))) as HS.
repeat match goal with H : img_env _ _ _ |- _ => clear H end.
assert (HEI : img_env VAL A_LIM (lh_E (ms_regs msA))) by apply lh_env_img.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (lh_E (ms_regs msA)) (mrestrict (w_H W') (ms_mem msA)))
  by constructor.
assert (U18 : bv_unsigned (ew (lh_E (ms_regs msA)) 18) = lc_SH cx)
  by (rewrite (lh_ew_reg (ms_regs msA) 18 18%bv eq_refl), A18; apply unsigned_lit_small; unfold lc_SH, SHADOW_OFF; lia).
paj_run_tok RUN HS HJ SHOK LH_B0.
{ lh_awr_rs.
  eapply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ LF_CID (l_fpos cx)); [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U18 in Ha.
  right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes LF_CID / 8) with 32. rewrite HFaddr.
  unfold shadow_addr, lc_SH in *. lia. }
lh_name HS msB.
lh_kept W' HFr HG (fun x => lc_SH cx <= x < lc_SH cx + 32) KB ltac:(rewrite ?U18 in Hx; lia).
pose proof HG as GB. clear HF HFr HG.
(* the registers at the call of __asan_memcpy *)
lh_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + LH_RCPY)) V1 ltac:(apply codeptr_val; exact HEI).
lh_reg HS (10%bv : bv 5) (w64 (lc_F cx + 176)) V10
  ltac:(cbn [sv_denot]; rewrite (lh_ew_reg (ms_regs msA) 20 20%bv eq_refl), A20, Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
lh_reg HS (11%bv : bv 5) (w64 TRANS_IO) V11 ltac:(exact (lh_obj4 (ms_regs msA))).
lh_reg HS (12%bv : bv 5) (w64 32) V12 ltac:(reflexivity).
lh_kreg HS (ms_regs msA) (2%bv : bv 5) 2%nat A2 V2. lh_kreg HS (ms_regs msA) (8%bv : bv 5) 8%nat A8 V8.
lh_kreg HS (ms_regs msA) (9%bv : bv 5) 9%nat A9 V9. lh_kreg HS (ms_regs msA) (3%bv : bv 5) 3%nat A3 V3.
lh_kreg HS (ms_regs msA) (4%bv : bv 5) 4%nat A4 V4. lh_kreg HS (ms_regs msA) (22%bv : bv 5) 22%nat A22 V22.
lh_kreg HS (ms_regs msA) (21%bv : bv 5) 21%nat A21 V21. lh_kreg HS (ms_regs msA) (26%bv : bv 5) 26%nat A26 V26.
lh_kreg HS (ms_regs msA) (20%bv : bv 5) 20%nat A20 V20. lh_kreg HS (ms_regs msA) (18%bv : bv 5) 18%nat A18 V18.
(* the frame's 32 shadow bytes *)
lh_region HS 0%nat HRsh.
assert (HFSB : lc_fsh cx (aview segs (w_H W') (ms_mem msB)) false false).
{ intros i Hi.
  pose proof (lh_region_bytes _ (w_H W') (ms_mem msB) 18 (lc_SH cx) _ _ _ _ _
    [(10%nat, 18446744073709551601); (14%nat, 18446744073709551608)] (lf_shm false false) HRsh U18
    ltac:(intros n0 z0 Hin; cbn [In] in Hin;
          destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <-;
          [rewrite (lh_ew_reg (ms_regs msA) 10 10%bv eq_refl); exact A10
          | rewrite (lh_ew_reg (ms_regs msA) 14 14%bv eq_refl); exact A14])
    ltac:(vm_compute; reflexivity) (Z.to_nat i) ltac:(rewrite lf_shm_len; lia)) as Hb.
  rewrite Z2Nat.id in Hb by lia. exact Hb. }
clear HRsh.
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 (transportb_sigma TB___asan_memcpy)) mm rom) mdx) Q);
  set (mdB := mdx) in * end.
clear HS SHOK.
(* the core at the call: the runs wrote lh_wr bytes only *)
assert (KVB : forall a, 0 <= a < 2 ^ 64 -> ~ lh_wr cx a ->
  aview segs (w_H W') (ms_mem msB) a = aview segs (w_H W') mem' a).
{ intros a Ha Hw. unfold lh_wr in Hw.
  rewrite (KB a Ha ltac:(cbv beta; intros X; apply Hw; right; right; exact X)).
  apply (KA a Ha). cbv beta. intros [X | X]; apply Hw; [left; unfold ESTACK; lia | right; left; lia]. }
assert (GPB : forall a, apresent (w_H W') mem' a -> apresent (w_H W') (ms_mem msB) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a GB (apresent_grows _ _ _ a GA Ha))).
assert (HCB : @lc_core rc B cx ly' S' W' (ms_regs msB) (ms_mem msB) mdB 0)
  by exact (lh_core_step cx ly' S' W' regs' mem' md' 0 (ms_regs msB) (ms_mem msB) mdB 0 LAWS HB HC0 HJ
    (eq_trans V2 (eq_sym R2)) (eq_trans V8 (eq_sym R8)) (eq_trans V9 (eq_sym R9)) (eq_trans V3 (eq_sym R3))
    (eq_trans V4 (eq_sym R4)) KVB GPB).
pose proof (K1 HP cx ly' S' W' (ms_regs msB) (ms_mem msB) mdB 0 HB HCB) as HROM.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARB.
assert (Usp : spZ (ms_regs msB) = lc_sp1 cx) by (unfold spZ; rewrite V2; apply unsigned_lit_small; lia).
assert (Hsp16 : lc_sp1 cx mod 16 = 0).
{ pose proof (Z.div_mod (lc_sp1 cx) 32 ltac:(lia)) as D. rewrite Hsp1al, Z.add_0_r in D. rewrite D.
  replace (32 * (lc_sp1 cx / 32)) with ((2 * (lc_sp1 cx / 32)) * 16) by ring. apply Z.mod_mul. lia. }
assert (HF8m : lc_F cx mod 8 = 0).
{ pose proof (Z.div_mod (lc_F cx) 64 ltac:(lia)) as D. rewrite HFal, Z.add_0_r in D. rewrite D.
  replace (64 * (lc_F cx / 64)) with ((8 * (lc_F cx / 64)) * 8) by ring. apply Z.mod_mul. lia. }
assert (Lio : length (sinit_io_bytes 0 (TI.ti_io_send timg_B) (TI.ti_io_recv timg_B) (TI.ti_io_now timg_B)) = 32%nat)
  by (vm_compute; reflexivity).
assert (HIOR : forall a, TRANS_IO <= a < TRANS_IO + 32 -> trans_in_ro_rd a).
{ intros a Ha. unfold trans_in_ro_rd. apply Exists_exists. exists (TRANS_IO, 32). split; [|unfold in_zr; cbn [fst snd]; lia].
  unfold TRANS_RO_RD, TRANS_RO_GLOBALS. apply in_or_app. right. cbn [In]. repeat (first [left; reflexivity | right]). }
(* io's 32 image bytes, read at the call *)
assert (HIOB : forall i, (i < 32)%nat -> aview segs (w_H W') (ms_mem msB) (TRANS_IO + Z.of_nat i) =
  Some (bv_unsigned (nth i (sinit_io_bytes 0 (TI.ti_io_send timg_B) (TI.ti_io_recv timg_B) (TI.ti_io_now timg_B))
    (Z_to_bv 8 0)))).
{ intros i Hi. assert (Hiz : 0 <= Z.of_nat i < 32) by (split; [apply Nat2Z.is_nonneg | apply (Nat2Z.inj_lt i 32); exact Hi]).
  rewrite (HROM (TRANS_IO + Z.of_nat i) (HIOR (TRANS_IO + Z.of_nat i) ltac:(lia))).
  apply (lc_rom_bytes TRANS_IO _); [unfold lc_rom_tab; cbn [In]; do 6 right; left; reflexivity | rewrite Lio; exact Hi]. }
(* +0x17c: __asan_memcpy (F + 176, io, 32) *)
eapply SRr_bind.
{ apply (@gx_intrin_at (l_fx cx) rc tfib_sink_head segs B LAWS transportb_segs_low OCpy
    (transportb_sigma TB___asan_memcpy)
    (lp_memcpy _ _ _ _ _ HP (l_fx cx)) TG.G_HARNESS_B W' (ms_regs msB) (ms_mem msB) LLVMF_STK (lc_sp0 cx) _
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly' S' mdB 0
    (lc_F cx + 176) TRANS_IO 32 (lc_sp1 cx - lc_sp0 cx) (Z_to_bv 64 (BASE + LH_RCPY)) HGX G_HARNESS_B_rw HJ
    V10 V11 V12).
  - lia.
  - lia.
  - lia.
  - rewrite Usp. lia.
  - rewrite Zminus_mod, Hsp16, Hsp0al. reflexivity.
  - lia.
  - unfold ESTACK, LLVMF_STK. lia.
  - exact V3.
  - exact V4.
  - exact V1.
  - apply (ret_ok_codeptr_v (PI := PI_transportb)); [unfold LH_RCPY, AF_LLVMFuzzerTestOneInput; lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|].
    intros a Ha. left. split.
    + unfold awr_byte. right; right; right. exists LF_CID, (l_fpos cx). split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. rewrite HFaddr. change (fs_frame_bytes LF_CID) with 256. lia.
    + rewrite Usp. unfold ESTACK. lia.
  - unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
    unfold kLowMemEnd, kHighMemBeg, kHighMemEnd.
    destruct HFapp as (_ & [H1 | (H1 & H2)]); [left; lia | right; lia].
  - apply (TGNA.frame_ra_zero _ (lc_F cx) (lc_F cx + 176) 32 22 26); [lia | exact HF8m | lia | lia |].
    intros i Hi. change (SHADOW_OFF + lc_F cx / 8 + i) with (lc_SH cx + i). rewrite (HFSB i ltac:(lia)).
    assert (Hc : i = 22 \/ i = 23 \/ i = 24 \/ i = 25) by lia.
    destruct Hc as [-> | [-> | [-> | ->]]]; reflexivity.
  - intros _. apply (TGNA.frame_hull_vis _ (lc_F cx) 256 (lc_F cx + 176) 32); [lia | exact HFal | reflexivity | lia | lia | lia |].
    intros i Hi. change (256 / 8) with 32 in Hi. change (shadow_addr (lc_F cx) + i) with (lc_SH cx + i).
    rewrite (HFSB i Hi). discriminate.
  - split; [unfold TRANS_IO; lia|]. split; [unfold TRANS_IO; lia|].
    split.
    { intros a Ha. split.
      - replace a with (TRANS_IO + Z.of_nat (Z.to_nat (a - TRANS_IO))) by lia.
        rewrite (HIOB (Z.to_nat (a - TRANS_IO)) ltac:(lia)). discriminate.
      - rewrite Usp. unfold TRANS_IO, ESTACK in *. lia. }
    split.
    { destruct (Z_le_gt_dec (lc_F cx + 176 + 32) TRANS_IO) as [Hle | Hgt]; [left; exact Hle|].
      destruct (Z_le_gt_dec (TRANS_IO + 32) (lc_F cx + 176)) as [Hle2 | Hgt2]; [right; exact Hle2|].
      exfalso.
      apply (frm_img segs B LAWS _ _ _ _ _ LF_CID (l_fpos cx) (Z.max (lc_F cx + 176) TRANS_IO) HARg HFin).
      - rewrite HFaddr. change (fs_frame_bytes LF_CID) with 256. lia.
      - apply trans_ro_img. apply HIOR. lia. }
    split; [unfold amem_range, TRANS_IO, kLowMemEnd; left; lia|].
    destruct (lc_sh_any B (l_ly cx) (lp_cells _ _ _ _ _ HP) (lp_llvmf_cells _ _ _ _ _ HP) (TRANS_IO, 32)
      ltac:(unfold lc_ro_ranges; cbn [In]; repeat (first [left; reflexivity | right])) _ _ _ _ _ HARB) as [HRA HHV].
    split; [exact HRA | intros _; exact HHV]. }
cbv beta. intros W2 c2 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & H10 & Hcpy & Heff & Hgr).
cbv iota in Hcpy.
(* the cut's facts at the return of __asan_memcpy *)
assert (KV3 : forall a, 0 <= a < 2 ^ 64 -> ~ lh_wr cx a -> aview segs (w_H W') mem3 a = aview segs (w_H W') mem' a).
{ intros a Ha Hw. pose proof Hw as Hw'. unfold lh_wr in Hw'.
  rewrite (Heff a Ha ltac:(intros X; apply Hw'; right; left; lia)
    ltac:(intros X; apply Hw'; left; unfold ESTACK in *; lia)).
  exact (KVB a Ha Hw). }
assert (GP3 : forall a, apresent (w_H W') mem' a -> apresent (w_H W') mem3 a) by (intros a Ha; exact (Hgr a (GPB a Ha))).
assert (HC3 : @lc_core rc B cx ly' S' W' regs3 mem3 md3 0)
  by exact (lh_core_step cx ly' S' W' regs' mem' md' 0 regs3 mem3 md3 0 LAWS HB HC0 HJ3
    (eq_trans (HP3 2 ltac:(unfold acallee_saved; lia)) (eq_trans V2 (eq_sym R2)))
    (eq_trans (HP3 8 ltac:(unfold acallee_saved; lia)) (eq_trans V8 (eq_sym R8)))
    (eq_trans (HP3 9 ltac:(unfold acallee_saved; lia)) (eq_trans V9 (eq_sym R9)))
    (eq_trans (HP3 3 ltac:(unfold acallee_saved; lia)) (eq_trans V3 (eq_sym R3)))
    (eq_trans (HP3 4 ltac:(unfold acallee_saved; lia)) (eq_trans V4 (eq_sym R4))) KV3 GP3).
apply (lh_runc cx ly' S' W' regs3 mem3 md3 Bw0 HP HB HC3).
- split; [exact (eq_trans (HP3 18 ltac:(unfold acallee_saved; lia)) V18)
         | exact (eq_trans (HP3 26 ltac:(unfold acallee_saved; lia)) V26)].
- apply (lc_spills_kept cx _ (aview segs (w_H W') (ms_mem msA)));
    [intros o Ho; cbn [lf_spill_sm In] in Ho; destruct Ho as [<- | [<- | []]]; cbn; lia | | exact HSPA].
  intros a Ha. rewrite (Heff a ltac:(lia) ltac:(lia) ltac:(unfold ESTACK; lia)).
  apply (KB a ltac:(lia)). cbv beta. unfold lc_SH, SHADOW_OFF. lia.
- apply (lc_fsh_kept cx (aview segs (w_H W') (ms_mem msB))); [|exact HFSB].
  intros a Ha. apply Heff.
  + unfold lc_SH, SHADOW_OFF in *. lia.
  + intros X. pose proof (Z.div_mod (lc_F cx) 8 ltac:(lia)) as DF8.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, lc_SH, SHADOW_OFF in *. lia.
  + intros X. unfold lc_SH, SHADOW_OFF, ESTACK in *. lia.
- unfold lc_io. apply garr8_of_aview. intros j Hj.
  assert (Lz : length (TW.zs (sinit_io_bytes 0 (TI.ti_io_send timg_B) (TI.ti_io_recv timg_B) (TI.ti_io_now timg_B)))
    = 32%nat) by (vm_compute; reflexivity).
  rewrite Lz in Hj.
  assert (Hjz : 0 <= Z.of_nat j < 32) by (split; [apply Nat2Z.is_nonneg | apply (Nat2Z.inj_lt j 32); exact Hj]).
  rewrite (Hcpy (Z.of_nat j) ltac:(lia)). rewrite (HIOB j Hj).
  unfold TW.zs. rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map, Lio; exact Hj).
  rewrite map_nth. reflexivity.
- exact HMT.
- exact (eq_trans (HP3 22 ltac:(unfold acallee_saved; lia)) V22).
- exact (eq_trans (HP3 21 ltac:(unfold acallee_saved; lia)) V21).
- exact (eq_trans (HP3 20 ltac:(unfold acallee_saved; lia)) V20).
- exact HW0.
- unfold lc_tw. apply (tw_kept_GB (aview segs (w_H (l_W cx)) (l_mem cx))); [exact HTW0|].
  intros b n i Hin Hi.
  assert (Hg : inG TG.G_HARNESS_B (b + i)).
  { unfold inG. apply Exists_exists. exists (b, n). split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
  pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B _ HGX Hg) as Hl. unfold kLowMemEnd in Hl.
  rewrite (KV3 (b + i) ltac:(lia)).
  + exact (HGk (b + i) Hg).
  + unfold lh_wr, ESTACK. intros [X | [X | X]].
    * lia.
    * apply (frm_img segs B LAWS _ _ _ _ _ LF_CID (l_fpos cx) (b + i) HARg HFin);
        [rewrite HFaddr; change (fs_frame_bytes LF_CID) with 256; lia | exact (trans_g_img _ Hg)].
    * unfold lc_SH, SHADOW_OFF in X. lia.
Qed.

End hdr.

Print Assumptions lc_hdr_ok.
