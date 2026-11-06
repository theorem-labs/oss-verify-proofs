(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_calls_equal on the ASan build of plugin-hostd/fuzz_command
   (0x89968, 135 instructions), in the shape of cgif_file_fuzzer's walks (lib/A/AChc.v, ACh1.v..ACh8.v): the
   symbolic executor over the position-abstract listing (CmdPaLib.v), the inline checks removed by the shadow tokens
   (PaShadow.v), and the strcmp wrapper's call stepped through by its contract (PaArt.v aj_art_at). The two loops
   are cut at their heads (0x899dc, 0x89a6c) and at the outer latch (0x89ab0); each piece is re-seeded from the
   concrete state there and the loops are proved by induction. Every call is strcmp, which writes only its stack
   window, so the memory below the frame stays the entry's (kept_out) and the read-only bytes strcmp reads
   (rt_rom_view) follow from the statement's arodata_okP. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_calls_equal.v, with its module paths and module names changed; 517 of its 584 lines of code are new or changed and 1424 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): segment A8a of reac_segconf_parse_file's walk, the theorem
   pf_a8a_holds : S_A8a B of lib/A/Prog/pf_pieces.v (SEG 0x887a4 -> NEW 0x8890c, FOUND 0x88964 or CLR 0x880fc;
   49 instructions: 0x887a4-0x8883c, the check stubs 0x88b20-0x88b34 and 0x88ba8-0x88bb8, the error calls
   0x88d70-0x88d78). Segment A8a's proof, by the G3 walk owner, 2026-10-30. The functional template is the
   plain-build walk owner's plain piece lib/Prog/pf_p4.v at 16c6d72c0344 (w_segget / w_loop / w_notfound), the
   call steps those of the listing layer's owner's check_segments.v (strcmp through PaArt.aj_art_at) and of
   lib/A/Prog/reac_segconf_parse.v (a program callee through PaFx.cl_callSF, lifted by srr_apost_baseF_lift).
   The code (the unit's internal record, commit dfb49d6ad789, path records/segp/dis/
   reac_segconf_parse_file.fuzz_segconf.asan.s lines 845-883, 1068-1072, 1102-1105, 1216-1217):
     0x887a4 ld s4,0x60(s1); add s4,s4,s6; sd s4,0xb0(s1)     s4 = sh(&c->n) (slot 0x60 holds (c + RC_N) / 8)
     0x887b0 lb a0,0(s4); bnez a0,0x88b20                     check #29 (load4 of c->n), stub 0x88b20, error 0x88d70
     0x887b8 ld a0,0x80(s1); lw s3,0(a0); mv s4,s8; ld s7,0x28(s1); mv s8,s3; blez s3,NEW
     0x887d0 mv a0,s4; mv a1,s9; jal strcmp; beqz a0,FOUND    the search: s4 = &seg[j], s7 = &seg[j].seen_gen
     0x887e0 addi s8,-1; addi s7,0x164; addi s4,0x164; bnez s8,0x887d0
     0x887f0 li a0,0x20; blt s3,a0,NEW                       no entry has the name; room?
     0x887f8 ld a0,0x20(s1); srli/add/lb/bnez                 check #30 (c->overflow), stub 0x88ba8, error 0x88bb4
     0x8880c lw a1,0(a0); addi a1,1; sw a1,0(a0)              c->overflow++
     0x88818 a2 = F_bound; a4 = 32; s8 = c (slot 0x90); a0 = c; a1 = s10; a3 = s9; jal refuse; j CLR
   The two checks are passed by the token executor (lib/A/Prog/PaShadow.v): their address is (x >> 3) + s6 with
   s6 = SHADOW_OFF, x inside the block c, whose shadow entry covers both granules (8-aligned, inside the block),
   so the shadow byte is the literal 0 and the error arms are never reached.
   Internal cut points (each re-seeds a symbolic state from the concrete state): the loop head 0x887d0 (a8L j,
   the plain w_loop invariant: the names before j differ from name) and 0x887f0 (a8F: no name matched). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require pfA_facts check_segments.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegAddr SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase refuse_c
  reac_segconf_parse_file_c SegInstA pf_pieces pf_a5_k pf_a6_k pf_a8a_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require reac_segconf_parse.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(** ** The symbolic states *)
(* SEG 0x887a4: the slots s1 + 0x28 (&seg[0].seen_gen), 0x60 ((c + RC_N) / 8), 0x80 (&c->n), writable 0xb0; the
   field c->n (atom 32) of the block c = s8 *)
Definition a8_slots0 : YP09.region := YP09.mkRegion (Some 9%nat) 0x28 0xb8 0xb0 0xb8
  [YP09.mkChunk 0x28 (CVal 8 (SOff 24 seg_spec.RS_SEEN_GEN));
   YP09.mkChunk 0x60 (CVal 8 (SAlu ALU_SRL (SOff 24 seg_spec.RC_N) (SLit 3)));
   YP09.mkChunk 0x80 (CVal 8 (SOff 24 seg_spec.RC_N))].
Definition a8_creg0 : YP09.region := YP09.mkRegion (Some 24%nat) seg_spec.RC_N (seg_spec.RC_N + 4) 0 0
  [YP09.mkChunk seg_spec.RC_N (CVal 4 (SOff 32 0))].
Definition a8_F0 : facts := mkFacts [(2%nat, a8_spF); (9%nat, a8_spF); (22%nat, mkAF SB SB 0); (24%nat, PTR 4);
  (32%nat, mkAF 0 32 0)] [] [].
Definition ss_a8_seg : sstate := mkSS PF_SEG sr_atoms [a8_slots0; a8_creg0] None a8_F0.
Definition a8_SH0 : list shent := [mkSHE 24 0 seg_spec.SEG_C_SIZE].
(* the loop head 0x887d0: registers only *)
Definition ss_a8_loop : sstate := mkSS PF_A8L sr_atoms [] None (mkFacts [(2%nat, a8_spF)] [] []).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.


Definition a8_E0 (rX : bvmap 5 word) (N : Z) : env := Eimg (Ereg rX [w64 N]).
(* the state at SEG satisfies ss_a8_seg, and the block's shadow entry holds *)
Lemma a8_seed_seg : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name,
  a8c B n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name -> getr rX (Z_to_bv 5 24) = w64 (p_c v) ->
  st_ok_pi SEGS VAL (a8_E0 rX (Z.of_nat (length (rc_seg cf)))) ss_a8_seg
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_SEG)) memc (seg_rom SEGS))) /\
  sh_ok SEGS a8_Bx a8_SH0 (a8_E0 rX (Z.of_nat (length (rc_seg cf)))) (mrestrict (w_H Wc) memc).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name (HB & HM & HST & HS & HI & HL & HR) R24.
destruct HB as (HCX & HFI & HOB & HSL & HFSH).
destruct HFI as (HJ & Hly & HSc & HPm & HSV & HFL & HFRM & HRF).
destruct HOB as (OT & OTA & OTH & OCA & OCH & OCAT & OLIT & OROD & OSSP).
destruct HST as (SRC & SNM & SCNT).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof (a8_sp B v HCX) as (S1 & S2 & S3 & S4 & S5).
pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & _ & (fe & (RP & _)) & _).
pose proof RP as (C0 & C16 & _).
destruct OCH as (bc & mc & Hinc & Hbc1 & Hbc2).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc bc mc HAR Hinc) as (Hp16 & Hp4096 & Hpceil & Hpapp & _ & _ & Hkr).
pose proof (req_size_pos mc ltac:(lia)) as [_ Hreq].
pose proof asan_consts as (A1 & A2 & A3 & A4 & A5).
pose proof STK_values as (_ & _ & _ & SPF & _).
destruct SRC as (bs & HBs & Henc). pose proof Henc as (Lbs & L32 & _ & UN & _).
unfold seg_spec.SEG_C_SIZE in Lbs.
set (N := Z.of_nat (length (rc_seg cf))) in *.
set (E := a8_E0 rX N).
assert (U2 : bv_unsigned (ew E 2) = pf_s1 v)
  by (apply (a8_u_reg rX _ 2); [lia | exact (a5_rg_get rX _ 2 _ HRF ltac:(cbn; tauto)) | lia]).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (apply (a8_u_reg rX _ 9); [lia | exact (a5_rg_get rX _ 9 _ HRF ltac:(cbn; tauto)) | lia]).
assert (U22 : bv_unsigned (ew E 22) = SB)
  by (apply (a8_u_reg rX _ 22); [lia | exact (a5_rg_get rX _ 22 _ HRF ltac:(cbn; tauto)) | unfold SB; lia]).
unfold seg_spec.SEG_C_SIZE in Hbc2.
assert (U24 : bv_unsigned (ew E 24) = p_c v) by (apply (a8_u_reg rX _ 24); [lia | exact R24 | lia]).
assert (E32 : ew E 32 = w64 N) by (subst E; unfold a8_E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (U32 : bv_unsigned (ew E 32) = N) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
assert (VN : sa_val (rdW Wc memc) (p_c v + seg_spec.RC_N) 4 N)
  by (apply (a8_u32_at _ (p_c v) bs seg_spec.RC_N N HBs); [unfold seg_spec.RC_N; lia | unfold seg_spec.RC_N; lia | exact UN]).
split.
- rewrite restrict_mkst_fx. unfold ss_a8_seg. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * unfold region_ok, a8_slots0.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [lia|]. split; [lia|]. split.
      { intros o0 Ho0. apply (apresent_writable SEGS). apply Hpres. unfold pf_sp0 in *. lia. }
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      -- apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x28 8 _ (p_c v + seg_spec.RS_SEEN_GEN));
           [apply (a8_soff E 24 _ _ U24) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold seg_spec.RS_SEEN_GEN; lia | cbn; lia |].
         apply val_mem_of_rdword. apply (a8_sl_get _ _ (PF_SL v pos) _ _ HSL). unfold PF_SL. cbn [In]. tauto.
      -- apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x60 8 _ ((p_c v + seg_spec.RC_N) / 8));
           [apply (a8_srl3 E 24 _ _ ltac:(rewrite U24; reflexivity)); unfold seg_spec.RC_N; lia
           | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold seg_spec.RC_N;
             split; [apply Z.div_pos; lia | apply (Z.le_lt_trans _ (p_c v + 11392)); [apply Z.div_le_upper_bound; lia | lia]]
           | cbn; lia |].
         apply val_mem_of_rdword. apply (a8_sl_get _ _ (PF_SL v pos) _ _ HSL). unfold PF_SL. cbn [In]. tauto.
      -- apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x80 8 _ (p_c v + seg_spec.RC_N));
           [apply (a8_soff E 24 _ _ U24) | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold seg_spec.RC_N; lia | cbn; lia |].
         apply val_mem_of_rdword. apply (a8_sl_get _ _ (PF_SL v pos) _ _ HSL). unfold PF_SL. cbn [In]. tauto.
    * unfold region_ok, a8_creg0.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U24.
      unfold seg_spec.RC_N in *.
      split; [lia|]. split; [lia|]. split; [intros o0 Ho0; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (p_c v) 11392 4 (SOff 32 0) N);
        [rewrite (a8_soff E 32 0 N U32), Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      exact (a8_val_mem_of_sa SEGS _ _ _ _ _ VN).
  + apply pairwise_disjoint_of_extents. unfold a8_slots0, a8_creg0, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U24.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold seg_spec.RC_N. repeat split; lia.
  + split; [|split; exact I]. cbn [f_atoms atoms_ok a8_F0]. unfold afact_ok, a8_spF, PTR. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, U22, U24, U32. change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SB. repeat split; try lia.
- unfold sh_ok, a8_SH0. apply Forall_cons; [|apply Forall_nil].
  unfold shent_ok, app_apart, a8_Bx. cbn [she_m she_lo she_hi].
  assert (UB : U E (SOff 22 0) = SB) by (rewrite U_SOff, U22, Z.add_0_r; apply zcanon_small; unfold SB, M64; lia).
  assert (UC : U E (SOff 24 0) = p_c v) by (rewrite U_SOff, U24, Z.add_0_r; apply zcanon_small; unfold M64; lia).
  rewrite UB, UC. split.
  + rewrite Z.add_0_r, Z.sub_0_r. exact (proj1 (proj2 (proj2 (proj2 OCA)))).
  + intros y Hy. unfold seg_spec.SEG_C_SIZE in *. rewrite Z.min_l, Z.max_r in Hy by lia.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *. lia.
Qed.


Ltac a8_md :=
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?md2 _ |- _ =>
    lazymatch md2 with with_vm_backing _ _ _ => let m := fresh "mdv" in set (m := md2) in *; clearbody m | _ => idtac end end.
Ltac a8_kept_win HFr K lo hi Usp :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  assert (K : kept_out (aview SEGS H m1) (aview SEGS H m2) lo hi)
  by (intros x0 Hx0 Hn0; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun x => lo <= x < hi) HFr);
      [ intros b0 wlo whi a0 Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia|]); destruct Hin
      | exact Hx0 | exact Hn0 ]) end.
Ltac a8_kept_empty HFr K lo hi :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  assert (K : kept_out (aview SEGS H m1) (aview SEGS H m2) lo hi)
  by (intros x0 Hx0 Hn0; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
      [ intros b0 wlo whi a0 Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hin
      | exact Hx0 | tauto ]) end.
(* the registers a8c names keep their seeded values (each is still its own atom in the symbolic state) *)
Ltac a8_regs_kept HS EE :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; unfold A8_REGS in Hr; cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [ lazymatch goal with |- getr _ (Z_to_bv 5 ?kk) = _ =>
        let QX := fresh "QX" in prreg HS (Z_to_bv 5 kk : bv 5) QX; rewrite QX;
        rewrite ?ew_havoc_old by (cbn; lia); apply EE; reflexivity end |]);
  destruct Hr.
(* the same after a call, over the havocked environment's agreement EE3 on the atoms below 32 *)
Ltac a8_regs_kept3 HS EE3 :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; unfold A8_REGS in Hr; cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr];
    [ lazymatch goal with |- getr _ (Z_to_bv 5 ?kk) = _ =>
        let QX := fresh "QX" in prreg HS (Z_to_bv 5 kk : bv 5) QX; rewrite QX;
        apply EE3; [cbn; lia | reflexivity] end |]);
  destruct Hr.

Hypothesis TL : PALib B.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* SEG 0x887a4 .. 0x887cc: sh(&c->n) into slot 0xb0, check #29, n = c->n, s4 = &seg[0], s7 = &seg[0].seen_gen,
   s8 = n; `blez s3` to NEW (n = 0) or to the loop head *)
Lemma a8_seg_main : forall n, HA_NEW B n ->
  (forall v pos lyc Sc Wc rX memc mdc cf nm o ln d np name,
     a8L B n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name 0 ->
     SRr SEGS Wc (cfg_at SEGS (BASE + PF_A8L) rX memc mdc) (a8Q B v cf nm o ln name)) ->
  H_SEG B n.
Proof using TL.
intros n HNEW LOOP. unfold HA_NEW, H_NEW in HNEW. unfold H_SEG.
intros v pos lyc Sc Wc rX memc mdc cf nm o ln d np name HI.
pose proof (a8_of_seg B n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name HI) as HC.
assert (R24 : getr rX (Z_to_bv 5 24) = w64 (p_c v)).
{ destruct HI as (_ & _ & _ & _ & _ & _ & HRI). apply (a5_rg_get rX _ 24 _ HRI). unfold PF_RL. cbn. tauto. }
destruct (a8_seed_seg n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name HC R24) as [HS SHOK].
pose proof HC as ((HCX & HFI & HOB & HSL & HFSH) & HM & (SRC & SNM & SCNT) & HSs & HIb & HLn & HR).
pose proof HFI as (HJ & Hly & HSc & HPm & HSV & HFL & HFRM & HRF).
pose proof (a8_sp B v HCX) as (S1 & S2 & S3 & S4 & S5).
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof asan_consts as (A1 & A2 & A3 & A4 & A5).
pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & _ & (fe & (RP & _)) & _).
pose proof RP as (C0 & C16 & _).
pose proof SRC as (bs & HBs & Henc). pose proof Henc as (Lbs & L32 & _).
destruct HOB as (_ & _ & _ & _ & OCH & _).
destruct (a8_heap B lyc Sc Wc memc mdc _ _ (proj1 HJ) OCH ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (Cc1 & Cc2 & _).
unfold seg_spec.SEG_C_SIZE in Cc2.
set (N := Z.of_nat (length (rc_seg cf))) in *.
assert (HEI : img_env VAL A_LIM (a8_E0 rX N)) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (a8_E0 rX N) k = getr rX r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (U9 : bv_unsigned (ew (a8_E0 rX N) 9) = pf_s1 v)
  by (apply (a8_u_reg rX _ 9); [lia | exact (a5_rg_get rX _ 9 _ HRF ltac:(cbn; tauto)) | lia]).
assert (U22 : bv_unsigned (ew (a8_E0 rX N) 22) = SB)
  by (apply (a8_u_reg rX _ 22); [lia | exact (a5_rg_get rX _ 22 _ HRF ltac:(cbn; tauto)) | unfold SB; lia]).
assert (U24 : bv_unsigned (ew (a8_E0 rX N) 24) = p_c v) by (apply (a8_u_reg rX _ 24); [lia | exact R24 | lia]).
assert (E32 : ew (a8_E0 rX N) 32 = w64 N)
  by (unfold a8_E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
remember (a8_E0 rX N) as E eqn:HE. clear HE.
unfold cfg_at. change (w64 (BASE + PF_SEG)) with (Z_to_bv 64 (BASE + PF_SEG)).
paj_run_tok RUN HS HJ SHOK Bspan.
{ unfold ss_a8_seg; cbn [ss_mem].
  eapply awr_ok_cons_gen; [reflexivity | exact U9 | | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi a8_slots0] in Ha. left. unfold pf_sp0 in *. lia. }
a8_md.
a8_kept_win HFr KEEP0 (pf_s1 v + 0xb0) (pf_s1 v + 0xb8) U9. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* n <= 0: no entry; NEW 0x8890c *)
  assert (H0 : length (rc_seg cf) = 0%nat).
  { rewrite (a8_bge0 E 32 N E32) in Hc by lia. apply Z.leb_le in Hc. lia. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_NEW.
  { eapply awr_ok_cons_gen; [reflexivity | exact U9 | | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. left. unfold pf_sp0 in *. lia. }
  a8_md.
  a8_kept_win HFr KEEP1 (pf_s1 v + 0xb0) (pf_s1 v + 0xb8) U9. clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r := eval vm_compute in (nth 0 (ss_mem ssx) a8_slots0) in
    pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r HS ltac:(vm_compute; reflexivity)) as HRg;
    cbn [ms_mem restrict] in HRg end.
  pmkst HS.
  prreg HS (Z_to_bv 5 19 : bv 5) Q19.
  apply (HNEW fx v pos lyc Sc Wc _ _ _ cf nm o ln d np name). apply a8_new_ok.
  + apply (a8c_keep B _ _ _ _ _ _ rX memc mdc _ _ _ _ _ _ _ _ _ _ (pf_s1 v + 0xb0) (pf_s1 v + 0xb8) HC HJ);
      [apply (kept_out_trans _ _ _ _ _ _ _ KEEP0 KEEP1); lia | lia | right; lia |].
    a8_regs_kept HS EE.
  + unfold pf_sl. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    apply rdword_of_val_mem; [|unfold shadow_addr, SHADOW_OFF, seg_spec.RC_N;
      split; [pose proof (Z.div_pos (p_c v + 11392) 8 ltac:(lia) ltac:(lia)); lia
             | pose proof (Z.div_le_upper_bound (p_c v + 11392) 8 (p_c v + 11392) ltac:(lia) ltac:(lia)); lia]].
    apply (field_of_region E _ 9 (pf_s1 v) _ _ _ _ _ 0xb0 8 _ _ HRg U9 ltac:(cbn [In]; left; reflexivity));
      [| unfold shadow_addr, SHADOW_OFF, seg_spec.RC_N; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64);
         split; [pose proof (Z.div_pos (p_c v + 11392) 8 ltac:(lia) ltac:(lia)); lia
                | pose proof (Z.div_le_upper_bound (p_c v + 11392) 8 (p_c v + 11392) ltac:(lia) ltac:(lia)); lia]
       | cbn; lia].
    apply (a8_shaddr_den E 24 22 (p_c v)); [exact U24 | exact U22 | unfold seg_spec.RC_N; lia].
  + destruct (rc_seg cf) as [|g gs]; [reflexivity | discriminate H0].
  + lia.
  + rewrite Q19, E32. reflexivity.
- (* n > 0: the loop head 0x887d0 with j = 0 *)
  assert (H0 : (0 < length (rc_seg cf))%nat).
  { rewrite (a8_bge0 E 32 N E32) in Hc by lia. apply Z.leb_gt in Hc. lia. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_A8L.
  { eapply awr_ok_cons_gen; [reflexivity | exact U9 | | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. left. unfold pf_sp0 in *. lia. }
  a8_md.
  a8_kept_win HFr KEEP1 (pf_s1 v + 0xb0) (pf_s1 v + 0xb8) U9. clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r := eval vm_compute in (nth 0 (ss_mem ssx) a8_slots0) in
    pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r HS ltac:(vm_compute; reflexivity)) as HRg;
    cbn [ms_mem restrict] in HRg end.
  pmkst HS.
  prreg HS (Z_to_bv 5 19 : bv 5) Q19. prreg HS (Z_to_bv 5 20 : bv 5) Q20.
  prreg HS (Z_to_bv 5 23 : bv 5) Q23. prreg HS (Z_to_bv 5 24 : bv 5) Q24.
  apply (LOOP v pos lyc Sc Wc _ _ _ cf nm o ln d np name). split; [|split; [|split; [exact H0 | split; [reflexivity|]]]].
  + apply (a8c_keep B _ _ _ _ _ _ rX memc mdc _ _ _ _ _ _ _ _ _ _ (pf_s1 v + 0xb0) (pf_s1 v + 0xb8) HC HJ);
      [apply (kept_out_trans _ _ _ _ _ _ _ KEEP0 KEEP1); lia | lia | right; lia |].
    a8_regs_kept HS EE.
  + unfold pf_sl. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    apply rdword_of_val_mem; [|unfold shadow_addr, SHADOW_OFF, seg_spec.RC_N;
      split; [pose proof (Z.div_pos (p_c v + 11392) 8 ltac:(lia) ltac:(lia)); lia
             | pose proof (Z.div_le_upper_bound (p_c v + 11392) 8 (p_c v + 11392) ltac:(lia) ltac:(lia)); lia]].
    apply (field_of_region E _ 9 (pf_s1 v) _ _ _ _ _ 0xb0 8 _ _ HRg U9 ltac:(cbn [In]; left; reflexivity));
      [| unfold shadow_addr, SHADOW_OFF, seg_spec.RC_N; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64);
         split; [pose proof (Z.div_pos (p_c v + 11392) 8 ltac:(lia) ltac:(lia)); lia
                | pose proof (Z.div_le_upper_bound (p_c v + 11392) 8 (p_c v + 11392) ltac:(lia) ltac:(lia)); lia]
       | cbn; lia].
    apply (a8_shaddr_den E 24 22 (p_c v)); [exact U24 | exact U22 | unfold seg_spec.RC_N; lia].
  + unfold pf_rg. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    * rewrite Q19, E32. reflexivity.
    * rewrite Q20. replace (seg_spec.rseg_addr (p_c v) 0) with (bv_unsigned (ew E 24))
        by (rewrite U24; unfold seg_spec.rseg_addr; lia).
      unfold w64. symmetry. apply Z_to_bv_bv_unsigned.
    * rewrite Q23, U24. unfold seg_spec.rseg_addr, seg_spec.RS_SEEN_GEN, w64. f_equal. lia.
    * rewrite Q24, E32. unfold N. f_equal. lia.
Qed.

(* ---- the search loop ---- *)
(* a register-only seed at a pc (sp's fact only) *)
Lemma a8_seed_regs : forall pc rX (W : world SEGS) memc v,
  getr rX (Z_to_bv 5 2) = w64 (pf_s1 v) -> 2 ^ 46 <= pf_s1 v <= 2 ^ 47 -> pf_s1 v mod 32 = 0 ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [])) (mkSS pc sr_atoms [] None (mkFacts [(2%nat, a8_spF)] [] []))
    (restrict (w_H W) (mkst rX (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))) /\
  sh_ok SEGS a8_Bx [] (Eimg (Ereg rX [])) (mrestrict (w_H W) memc).
Proof.
intros pc rX W memc v R2 Hs Hal. split; [|apply Forall_nil].
assert (U2 : bv_unsigned (ew (Eimg (Ereg rX [])) 2) = pf_s1 v) by (apply (a8_u_reg rX _ 2); [lia | exact R2 | lia]).
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok, a8_spF. cbn [af_lo af_hi af_al2].
  rewrite U2. change (2 ^ 5) with 32. lia.
Qed.
(* the name in buf is a range the string wrappers may read (pf_a6_k's a6_buf_arg gives its sa_addr) *)
Lemma a8_buf_read : forall v pos lyc Sc Wc rX memc mdc stk (regs : bvmap 5 word) np name,
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  sa_str (rdW Wc memc) np name -> pf_inb (pf_F v pos + PF_O_BUF) np name ->
  alloc_ceiling <= spZ regs - stk ->
  aread_ok SEGS stk Wc regs memc np (Z.of_nat (length name) + 1).
Proof.
intros v pos lyc Sc Wc rX memc mdc stk regs np name HB HS HI Hst.
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & G & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof HI as [HI1 HI2]. unfold PF_O_BUF in HI1, HI2.
destruct (a6_buf_arg B v pos lyc Sc Wc rX memc mdc PF_SC_LINE np name [] HB eq_refl eq_refl HS HI (Forall_nil _))
  as [HVA _].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
cbn [sa_va_arg] in HVA. rewrite a6_w64_u in HVA by (unfold pf_inb, PF_O_BUF in *; lia).
destruct HVA as (_ & _ & HL & (A0 & A1 & A2 & A3 & A4) & _).
pose proof HS as ((Hz & _) & _).
unfold aread_ok. split; [exact A0|]. split; [exact A1|]. split; [lia|]. split.
- intros a Ha. split.
  + replace a with (np + Z.of_nat (Z.to_nat (a - np))) by lia.
    rewrite (Hz (Z.to_nat (a - np))) by (rewrite length_app; cbn [length]; lia). discriminate.
  + unfold ascratch_stk. lia.
- split; [exact A2|]. split; [exact A3 | exact A4].
Qed.

Hypothesis ASTRCMP : forall fx0 : YK11.FPState,
  @RtString.astrcmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcmp).

(* one pass of the search loop: 0x887d0 .. 0x887ec *)
Lemma a8_loop_step : forall n v pos lyc Sc Wc cf nm o ln d np name j rX memc mdc,
  HA_FOUND B n ->
  (forall rX' memc' mdc', a8F B n v pos lyc Sc Wc rX' memc' mdc' cf nm o ln d np name ->
     SRr SEGS Wc (cfg_at SEGS (BASE + PF_A8F) rX' memc' mdc') (a8Q B v cf nm o ln name)) ->
  ((S j < length (rc_seg cf))%nat -> forall rX' memc' mdc',
     a8L B n v pos lyc Sc Wc rX' memc' mdc' cf nm o ln d np name (S j) ->
     SRr SEGS Wc (cfg_at SEGS (BASE + PF_A8L) rX' memc' mdc') (a8Q B v cf nm o ln name)) ->
  a8L B n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name j ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_A8L) rX memc mdc) (a8Q B v cf nm o ln name).
Proof using TL ASTRCMP.
intros n v pos lyc Sc Wc cf nm o ln d np name j rX memc mdc HFOUND KF NXT (HC & HSL0 & Hj & HFG & HRL).
unfold HA_FOUND, H_FOUND in HFOUND.
pose proof HC as (HB & HM & (SRC & SNM & SCNT) & HSs & HIb & HLn & HR).
pose proof HB as (HCX & HFI & HOB & HSL & HFSH).
pose proof HFI as (HJ & Hly & HSc & HPm & HSV & HFL & HFRM & HRF).
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & _ & Hin5 & G & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (a5_rom B _ _ _ _ _ _ _ _ _ HB) as ROM0.
pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof asan_consts as (A1 & A2 & A3 & A4 & A5).
pose proof SRC as (bs & HBs & Henc). pose proof Henc as (Lbs & L32 & _).
unfold seg_spec.SEG_C_SIZE in Lbs.
pose proof HOB as (_ & _ & _ & _ & OCH & _).
destruct OCH as (bc & mc & Hinc & Hbc1 & Hbc2). unfold seg_spec.SEG_C_SIZE in Hbc2.
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc bc mc HAR Hinc) as (Hp16 & Hp4096 & Hpceil & Hpapp & _ & _ & Hkr).
pose proof (req_size_pos mc ltac:(lia)) as [_ Hreq].
rewrite SPF in G1.
pose proof HIb as [HI1 HI2]. unfold PF_O_BUF in HI1, HI2.
set (N := length (rc_seg cf)) in *.
(* entry j's name sx, and name as bytes *)
destruct (a8_rname (rdW Wc memc) (p_c v) cf j SRC Hj) as (sx & Bx & Nx & Zx & Lx).
destruct (a8_astr SEGS Wc memc np name HSs) as (STRy & Zy & Ny & Ly).
assert (RCS : forall a, p_c v <= a < p_c v + 16616 -> rdW Wc memc a <> None).
{ intros a Ha. replace a with (p_c v + Z.of_nat (Z.to_nat (a - p_c v))) by lia.
  rewrite (HBs (Z.to_nat (a - p_c v))) by lia. discriminate. }
assert (R2 : getr rX (Z_to_bv 5 2) = w64 (pf_s1 v)) by exact (a5_rg_get rX _ 2 _ HRF ltac:(cbn; tauto)).
destruct (a8_seed_regs PF_A8L rX Wc memc v R2 ltac:(lia) G5) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg rX []))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg rX [])) k = getr rX r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
remember (Eimg (Ereg rX [])) as E eqn:HE. clear HE.
assert (Usp : bv_unsigned (ew E 2) = pf_s1 v)
  by (rewrite (EE 2%nat (Z_to_bv 5 2) eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 (BASE + PF_A8L)) with (Z_to_bv 64 (BASE + PF_A8L)).
(* 0x887d0 .. 0x887d8: a0 := s4, a1 := s9, the call of the strcmp wrapper *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ cbn [ss_mem]. apply awr_ok_nil. }
a8_md.
a8_kept_empty HFr KEEP1 (pf_s1 v) (pf_s1 v). clear HF HFr HG.
pmkst HS.
prreg HS (Z_to_bv 5 1 : bv 5) P1. prreg HS (Z_to_bv 5 2 : bv 5) P2. prreg HS (Z_to_bv 5 3 : bv 5) P3.
prreg HS (Z_to_bv 5 4 : bv 5) P4. prreg HS (Z_to_bv 5 10 : bv 5) P10. prreg HS (Z_to_bv 5 11 : bv 5) P11.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) _) _ => set (rT0 := rT) in *; set (mT0 := mT) in * end.
assert (KV : forall a, 0 <= a < 2 ^ 64 -> rdW Wc mT0 a = rdW Wc memc a) by (intros a Ha; apply KEEP1; [exact Ha | lia]).
set (x := seg_spec.rseg_addr (p_c v) j) in *.
assert (Hx : p_c v <= x /\ x + 356 <= p_c v + 11392) by (subst x; unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE; lia).
assert (HspT : spZ rT0 = pf_sp0 v + (pf_s1 v - pf_sp0 v)).
{ unfold spZ. change (getr rT0 2) with (getr rT0 (Z_to_bv 5 2)). rewrite P2, Usp. lia. }
assert (Ho16 : (pf_s1 v - pf_sp0 v) mod 16 = 0).
{ pose proof (Z.div_mod (pf_s1 v) 32 ltac:(lia)) as D1. pose proof (Z.div_mod (pf_sp0 v) 16 ltac:(lia)) as D2.
  rewrite G5, Z.add_0_r in D1. rewrite G3, Z.add_0_r in D2.
  replace (pf_s1 v - pf_sp0 v) with ((2 * (pf_s1 v / 32) - pf_sp0 v / 16) * 16) by lia. apply Z_mod_mult. }
assert (P3' : getr rT0 3 = w64 (as_gp B)).
{ change (getr rT0 3) with (getr rT0 (Z_to_bv 5 3)). rewrite P3, (EE 3%nat (Z_to_bv 5 3) eq_refl).
  exact (a5_rg_get rX _ 3 _ HRF ltac:(cbn; tauto)). }
assert (P4' : getr rT0 4 = w64 (as_tp B)).
{ change (getr rT0 4) with (getr rT0 (Z_to_bv 5 4)). rewrite P4, (EE 4%nat (Z_to_bv 5 4) eq_refl).
  exact (a5_rg_get rX _ 4 _ HRF ltac:(cbn; tauto)). }
assert (P1' : getr rT0 1 = Z_to_bv 64 (BASE + PF_A8RA)).
{ change (getr rT0 1) with (getr rT0 (Z_to_bv 5 1)). rewrite P1. reflexivity. }
assert (HraT : YK0s.ret_ok (getr rT0 1))
  by (rewrite P1'; apply ret_ok_codeptr_v; [unfold PF_A8RA, AF_reac_segconf_parse_file; lia | reflexivity]).
assert (P10' : getr rT0 10 = w64 x).
{ change (getr rT0 10) with (getr rT0 (Z_to_bv 5 10)). rewrite P10, (EE 20%nat (Z_to_bv 5 20) eq_refl).
  exact (a5_rg_get rX _ 20 _ HRL ltac:(cbn; tauto)). }
assert (P11' : getr rT0 11 = w64 np).
{ change (getr rT0 11) with (getr rT0 (Z_to_bv 5 11)). rewrite P11, (EE 25%nat (Z_to_bv 5 25) eq_refl).
  apply (a5_rg_get rX _ 25 _ HR). cbn. tauto. }
(* the wrapper's premises *)
assert (STRc : astr_at SEGS Wc mT0 x sx).
{ split; [|exact Nx]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite KV by (subst x; unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE in *; lia).
  replace (x + Z.of_nat i) with (p_c v + 356 * Z.of_nat j + Z.of_nat i)
    by (subst x; unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE; lia).
  apply (Bx i). rewrite length_app. cbn [length]. lia. }
assert (STRm : astr_at SEGS Wc mT0 np (seg_spec.zb name)).
{ destruct STRy as [By Ny']. split; [|exact Ny']. intros i Hi. rewrite KV; [exact (By i Hi)|].
  rewrite length_app, Ly in Hi. cbn [length] in Hi. lia. }
assert (Hlo : alloc_ceiling <= spZ rT0 - 2 * ESTACK) by (rewrite HspT; change ESTACK with 4096; lia).
assert (RDc : aread_ok SEGS (2 * ESTACK) Wc rT0 mT0 x (astr_len sx + 1)).
{ unfold astr_len.
  apply (aread_ok_kept SEGS 0 (2 * ESTACK) Wc rT0 rT0 memc mT0 alloc_ceiling alloc_ceiling x _
    ltac:(intros a0 Ha0 _; apply KV; exact Ha0)); [| lia | lia | lia | lia | lia].
  apply (aread_ok_of_block SEGS B LAWS 0 lyc Sc Wc rT0 memc mdc bc mc x _ HAR Hinc); lia. }
assert (RDm : aread_ok SEGS (2 * ESTACK) Wc rT0 mT0 np (astr_len (seg_spec.zb name) + 1)).
{ unfold astr_len. rewrite Ly.
  apply (aread_ok_kept SEGS (2 * ESTACK) (2 * ESTACK) Wc rT0 rT0 memc mT0 alloc_ceiling alloc_ceiling np _
    ltac:(intros a0 Ha0 _; apply KV; exact Ha0)); [| lia | lia | lia | lia | lia].
  exact (a8_buf_read v pos lyc Sc Wc rX memc mdc (2 * ESTACK) rT0 np name HB HSs HIb Hlo). }
assert (TLc : atail_vis SEGS Wc mT0 (x + astr_len sx)).
{ unfold astr_len. intros a Ha. pose proof (Z.mod_pos_bound (x + Z.of_nat (length sx)) 8 ltac:(lia)).
  rewrite KV by lia. apply RCS. subst x; unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE in *; lia. }
assert (TLm : atail_vis SEGS Wc mT0 (np + astr_len (seg_spec.zb name))).
{ unfold astr_len. rewrite Ly. intros a Ha. pose proof (Z.mod_pos_bound (np + Z.of_nat (length name)) 8 ltac:(lia)).
  rewrite KV by lia. exact (proj2 HSs a Ha). }
assert (ROM : rt_rom_view SEGS B Wc mT0).
{ intros a Hro Ho He. pose proof Hro as (sg & Hsg & Hw & Hr).
  assert (Himg : in_img SEGS a) by (exists sg; split; [exact Hsg | exact Hr]).
  pose proof (pa_img_range _ Himg) as Hrg. unfold kImgEnd in Hrg.
  rewrite KV by lia. exact (ROM0 a Hro Ho He). }
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low errno_low (2 * ESTACK) (fun _ => False)
    (SIG SS___interceptor_trampoline_strcmp) Wc rT0 mT0 STK_reac_segconf_parse_file (pf_sp0 v)
    (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc _ 0
    (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + PF_A8RA)) _ HJ HspT Ho16
    ltac:(lia) ltac:(unfold ESTACK; lia) ltac:(rewrite SPF; change ESTACK with 4096; lia) P1' (fun a0 (H : False) => False_ind _ H)).
  apply (ASTRCMP fx lyc Sc Wc rT0 mT0 _ x np sx (seg_spec.zb name)).
  - exact (ecall_pre_stk_at SEGS B (2 * ESTACK) STK_reac_segconf_parse_file (pf_sp0 v) _ (p_ly v) (p_S v) (p_W v)
      (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc mT0 _ 0 rT0 (pf_s1 v - pf_sp0 v)
      HJ HspT Ho16 ltac:(lia) ltac:(change ESTACK with 4096; lia) ltac:(rewrite SPF; change ESTACK with 4096; lia)
      HraT P3' P4').
  - exact P10'. - exact P11'. - lia. - lia.
  - exact STRc. - exact STRm. - exact RDc. - exact RDm. - exact TLc. - exact TLm. - exact ROM. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HK2).
(* back at 0x887dc *)
jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H Wc) mem2) HP2 (@nil nat) HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ apply Forall_nil. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
assert (A52 : ew (havoc E 48 (map (getr regs2) CLOB)) 52 = getr regs2 10) by reflexivity.
remember (havoc E 48 (map (getr regs2) CLOB)) as Ec eqn:HEc.
assert (HEI3 : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD3 : forall k, (k < 48)%nat -> ew Ec k = ew E k) by (intros k Hk; rewrite HEc; apply YN3v.ew_havoc_old; exact Hk).
clear HEc.
assert (Usp3 : bv_unsigned (ew Ec 2) = pf_s1 v) by (rewrite OLD3 by lia; exact Usp).
assert (SHOK3 : sh_ok SEGS a8_Bx [] Ec (mrestrict (w_H Wc) mem2)) by apply Forall_nil.
assert (KEEPk : kept_out (rdW Wc memc) (rdW Wc mem2) (pf_s1 v - 2 * ESTACK) (pf_s1 v)).
{ intros a0 Ha0 Hn0. rewrite (HK2 a0 Ha0); [apply KV; exact Ha0 | lia | tauto]. }
clear HK2 KEEP1. clear HJ. rename HJ2 into HJ.
assert (EE3 : forall k (r : bv 5), (k < 32)%nat -> Z.of_nat k = bv_unsigned r -> ew Ec k = getr rX r)
  by (intros k r Hk Hk2; rewrite OLD3 by lia; apply EE; exact Hk2).
assert (KEEPx : forall memF, kept_out (rdW Wc mem2) (rdW Wc memF) (pf_s1 v) (pf_s1 v) ->
  kept_out (rdW Wc memc) (rdW Wc memF) (pf_s1 v - 2 * ESTACK) (pf_s1 v)).
{ intros memF K. apply (kept_out_trans _ _ _ _ _ _ _ KEEPk K); unfold ESTACK; lia. }
assert (Hlo8 : alloc_ceiling <= pf_s1 v - 2 * ESTACK) by (change ESTACK with 4096; lia).
assert (SL0 : forall memF, kept_out (rdW Wc memc) (rdW Wc memF) (pf_s1 v - 2 * ESTACK) (pf_s1 v) ->
  pf_sl (rdW Wc memF) (pf_s1 v) [(0xb0, shadow_addr (p_c v + seg_spec.RC_N))]).
{ intros memF K. apply (a8_sl_kept _ _ _ _ _ _ HSL0 K).
  intros ov Hov. cbn [In] in Hov. destruct Hov as [<- | []]. cbn [fst]. lia. }
change (BASE + PF_A8RA) with (BASE + 15016).
(* 0x887dc: beqz a0, FOUND *)
psrr_branch_tok RUN BR HS SHOK3 Bspan.
- (* strcmp returned 0: entry j has the name; FOUND 0x88964 *)
  assert (Z10 : getr regs2 10 = w64 0).
  { rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc. unfold U in Hc. apply bv_eq in Hc.
    cbn [sv_denot] in Hc. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, A52 in Hc. exact Hc. }
  clear Hc.
  assert (HFj : r_find_go (rc_seg cf) name 0 = Some j).
  { rewrite HFG, (a8_find_step _ name j j Hj), <- Zx, (proj1 HQ2 Z10), Zy, strcmp_refl. reflexivity. }
  paj_run_to_tok RUNTO HS HJ SHOK3 Bspan PF_FOUND.
  { apply awr_ok_nil. }
  a8_md.
  a8_kept_empty HFr KEEP4 (pf_s1 v) (pf_s1 v). clear HF HFr HG.
  pmkst HS.
  prreg HS (Z_to_bv 5 20 : bv 5) Q20. prreg HS (Z_to_bv 5 23 : bv 5) Q23.
  apply (HFOUND fx v pos lyc Sc Wc _ _ _ cf nm o ln d np name j). apply a8_found_ok.
  + apply (a8c_keep B _ _ _ _ _ _ rX memc mdc _ _ _ _ _ _ _ _ _ _ (pf_s1 v - 2 * ESTACK) (pf_s1 v) HC HJ);
      [exact (KEEPx _ KEEP4) | exact Hlo8 | left; lia |].
    a8_regs_kept3 HS EE3.
  + exact HFj.
  + rewrite Q20, (EE3 20%nat (Z_to_bv 5 20) ltac:(lia) eq_refl). exact (a5_rg_get rX _ 20 _ HRL ltac:(cbn; tauto)).
  + rewrite Q23, (EE3 23%nat (Z_to_bv 5 23) ltac:(lia) eq_refl). exact (a5_rg_get rX _ 23 _ HRL ltac:(cbn; tauto)).
- (* the names differ: 0x887e0 .. 0x887ec *)
  assert (Hne : sx <> seg_spec.zb name).
  { intros E0. apply (proj2 HQ2) in E0. rewrite branch_eq_U in Hc. apply Z.eqb_neq in Hc. apply Hc.
    unfold U. f_equal. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, A52, E0. reflexivity. }
  clear Hc.
  assert (HFj : r_find_go (skipn j (rc_seg cf)) name j = r_find_go (skipn (S j) (rc_seg cf)) name (S j)).
  { rewrite (a8_find_step _ name j j Hj), <- Zx.
    destruct (strcmp (seg_spec.zs sx) name =? 0) eqn:Es; [|reflexivity].
    exfalso. apply Hne. apply Z.eqb_eq in Es. rewrite <- Zy in Es.
    exact (proj1 (PCS.bridge_strcmp sx (seg_spec.zb name) Nx Ny) Es). }
  paj_run_tok RUN HS HJ SHOK3 Bspan.
  { apply awr_ok_nil. }
  a8_md.
  a8_kept_empty HFr KEEP3 (pf_s1 v) (pf_s1 v). clear HF HFr HG.
  assert (E24 : bv_unsigned (ew Ec 24) = Z.of_nat (N - j)).
  { rewrite (EE3 24%nat (Z_to_bv 5 24) ltac:(lia) eq_refl), (a5_rg_get rX _ 24 _ HRL ltac:(cbn; tauto)).
    unfold w64. apply unsigned_lit_small. lia. }
  psrr_branch_tok RUN BR HS SHOK3 Bspan.
  + (* entries left: back to 0x887d0 with j + 1 *)
    assert (HiS : (S j < N)%nat).
    { rewrite branch_ne_U, U_SOff, U_SLit in Hc. rewrite E24 in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
      rewrite zcanon_small in Hc by (unfold M64; lia). change (zcanon 0) with 0 in Hc. lia. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK3 Bspan PF_A8L.
    { apply awr_ok_nil. }
    a8_md.
    a8_kept_empty HFr KEEP4 (pf_s1 v) (pf_s1 v). clear HF HFr HG.
    pose proof (kept_out_trans _ _ _ _ _ _ _ KEEP3 KEEP4 ltac:(lia) ltac:(lia)) as KEEP5.
    pmkst HS.
    prreg HS (Z_to_bv 5 19 : bv 5) Q19. prreg HS (Z_to_bv 5 20 : bv 5) Q20.
    prreg HS (Z_to_bv 5 23 : bv 5) Q23. prreg HS (Z_to_bv 5 24 : bv 5) Q24.
    apply (NXT HiS). split; [|split; [|split; [exact HiS | split]]].
    * apply (a8c_keep B _ _ _ _ _ _ rX memc mdc _ _ _ _ _ _ _ _ _ _ (pf_s1 v - 2 * ESTACK) (pf_s1 v) HC HJ);
        [exact (KEEPx _ KEEP5) | exact Hlo8 | left; lia |].
      a8_regs_kept3 HS EE3.
    * exact (SL0 _ (KEEPx _ KEEP5)).
    * rewrite HFG. exact HFj.
    * unfold pf_rg. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      -- rewrite Q19, (EE3 19%nat (Z_to_bv 5 19) ltac:(lia) eq_refl). exact (a5_rg_get rX _ 19 _ HRL ltac:(cbn; tauto)).
      -- rewrite Q20, (EE3 20%nat (Z_to_bv 5 20) ltac:(lia) eq_refl), (a5_rg_get rX _ 20 _ HRL ltac:(cbn; tauto)).
         unfold w64. rewrite unsigned_lit_small by (subst x; unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE in *; lia).
         f_equal. subst x. unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE. lia.
      -- rewrite Q23, (EE3 23%nat (Z_to_bv 5 23) ltac:(lia) eq_refl), (a5_rg_get rX _ 23 _ HRL ltac:(cbn; tauto)).
         unfold w64. rewrite unsigned_lit_small
           by (subst x; unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RS_SEEN_GEN in *; lia).
         f_equal. subst x. unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE. lia.
      -- rewrite Q24, E24. unfold w64. f_equal. lia.
  + (* the last entry: 0x887f0 *)
    assert (HiS : S j = N).
    { rewrite branch_ne_U, U_SOff, U_SLit in Hc. rewrite E24 in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
      rewrite zcanon_small in Hc by (unfold M64; lia). change (zcanon 0) with 0 in Hc. lia. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK3 Bspan PF_A8F.
    { apply awr_ok_nil. }
    a8_md.
    a8_kept_empty HFr KEEP4 (pf_s1 v) (pf_s1 v). clear HF HFr HG.
    pose proof (kept_out_trans _ _ _ _ _ _ _ KEEP3 KEEP4 ltac:(lia) ltac:(lia)) as KEEP5.
    pmkst HS.
    prreg HS (Z_to_bv 5 19 : bv 5) Q19.
    apply KF. split; [|split; [|split; [|split]]].
    * apply (a8c_keep B _ _ _ _ _ _ rX memc mdc _ _ _ _ _ _ _ _ _ _ (pf_s1 v - 2 * ESTACK) (pf_s1 v) HC HJ);
        [exact (KEEPx _ KEEP5) | exact Hlo8 | left; lia |].
      a8_regs_kept3 HS EE3.
    * exact (SL0 _ (KEEPx _ KEEP5)).
    * rewrite HFG, HFj, HiS. unfold N. apply a8_find_end.
    * lia.
    * unfold pf_rg. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
      rewrite Q19, (EE3 19%nat (Z_to_bv 5 19) ltac:(lia) eq_refl). exact (a5_rg_get rX _ 19 _ HRL ltac:(cbn; tauto)).
Qed.

(* the search loop, by induction on the entries left *)
Lemma a8_loop_all : forall n v pos lyc Sc Wc cf nm o ln d np name,
  HA_FOUND B n ->
  (forall rX' memc' mdc', a8F B n v pos lyc Sc Wc rX' memc' mdc' cf nm o ln d np name ->
     SRr SEGS Wc (cfg_at SEGS (BASE + PF_A8F) rX' memc' mdc') (a8Q B v cf nm o ln name)) ->
  forall dd j, (j + dd = length (rc_seg cf))%nat -> forall rX memc mdc,
  a8L B n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name j ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_A8L) rX memc mdc) (a8Q B v cf nm o ln name).
Proof using TL ASTRCMP.
intros n v pos lyc Sc Wc cf nm o ln d np name HFOUND KF.
induction dd as [|dd IH]; intros j Hd rX memc mdc HL.
- exfalso. destruct HL as (_ & _ & Hj & _). lia.
- apply (a8_loop_step n v pos lyc Sc Wc cf nm o ln d np name j rX memc mdc HFOUND KF); [|exact HL].
  intros Hsj rX' memc' mdc' HL'. apply (IH (S j)); [lia | exact HL'].
Qed.

End e.
End f.
End d.
