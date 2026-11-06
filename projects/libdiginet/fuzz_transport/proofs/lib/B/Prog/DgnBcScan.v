(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 277 of its 318 lines of code are new or changed and 1883 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: reac-repacer/fuzz_uci's lib/A/Prog/UciCcRel.v (cc_rel, the release-and-return piece of check_clamp) ported to libdiginet/fuzz_frame's diginet_body_check at image A: the class-2 frame of 256 bytes, its 32 shadow bytes, the slot that holds the frame, the 13 saved words, and the walk's own journal ending at a later layout. *)
(* Modified by Theorem Labs, 2026-10: libdiginet/fuzz_frame image B's copy of this unit's image-A lib/A/Prog/DgnBcRel.v: module paths lib/B (the image-B core's YB1v / YE2k / YCbq / YC5d / AsanCells, lib/B/Prog/PaJournal.v, the listing files lib/B/Prog/FrameBSyms.v / FrameBList.v / FrameBAddr.v / FrameBPa.v / FrameBImg.v / FrameBPaLib.v / FrameBCJ.v, CanKit.v, DgnFrameCg.v, diginet_body_check_cg.v and DgnBcCut.v), the listing names (fbsym, frameb_listing, frameb_tpi, PI_frameb, PL_frameb, frameb_segs_low for dfsym, dgnframe_listing, dgnframe_tpi, PI_dgnframe, PL_dgnframe, dgnframe_segs_low), and image B's offsets (the cut at +0x2d0, the ret at +0x438: the same 91 instruction words as image A's +0x298 .. +0x400, two pc-relative targets moved). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/DgnBcRel.v; 674 of its 714 lines of code are new or changed and 278 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: image B's copy of lib/A/Prog/DgnBcScan.v: module paths lib/B, the listing frameb_listing / PI_frameb, image B's offsets (+0x1f8 .. +0x2cc / +0x43c, the release at +0x2d0), and image B's loop (the pointer body stays in s3 and i runs up in a2; each turn's state names body + i as an atom by two alias facts, and three condition facts and the range of body decide the five UBSan guard branches into the trap word +0x444). *)
(* DgnBcScan (image B): Lemma bc_scan : bc_rel_stmt -> bc_scan_stmt (lib/B/Prog/DgnBcCut.v), the prefix scan of
   diginet_body_check (fuzz_decode.asan-ubsan 0x82970 = dgndecb_sigma DDB_diginet_body_check), offsets +0x1f8 .. +0x2cc
   and +0x43c of the listing lib/B/Prog/DgnDecodeBList.v, up to the release at +0x2d0 (BC_REL, the premise).
   The code writes no memory and calls nothing:
     +0x1f8 .. +0x200  a0 = 4, s4 = the word at s1 + 16 (len), `bltu s4,a0` to +0x2cc;
     +0x204 .. +0x220  a2 = 0 (i), a3 = ~s3 (2^64 - 1 - body), s4 = len - 3, a4 = s3 + 1, a5 = (s3 <> 0) = 1,
                       a6 = 240, a7 = 19, t0 = 112;
     +0x224 .. +0x298  turn i (s3 = body, a2 = i): a0 = s3 + a2; the UBSan guards `bltu a0,s3` (+0x228),
                       `beqz a1` with a1 = a5 xor (a0 = 0) (+0x234) and `beqz s3` (+0x238), each to the trap word
                       +0x444; the instrumented check of the byte at a0, t1 = a4 + a2, the load of body[i] and
                       `bne a1,a6` to +0x29c; the guard `bgeu a2,a3` (+0x258), the check of a0 + 1, body[i + 1] and
                       `bne a1,a7` to +0x29c; a1 = a2 + 3 and the guard `bltu a3,a1` (+0x27c), the check of a0 + 3,
                       body[i + 3] and `beq a0,t0` to +0x43c (`li a0,-10`, `j +0x2d0`);
     +0x29c .. +0x2a4  a2 one up, `bne s4,a2` to +0x224; else `j +0x2cc`;
     +0x2cc            `li a0,0`, then +0x2d0.
   How it is proved. Three segments run on the PA engine with its token shadow checks (lib/A/Prog/PaShadow.v), each
   from a fresh symbolic state whose regions are read-only, so each run leaves the memory as it was
   (frame_of_read_only) and changes only the model's materialized part (ajournal_materialize keeps the journal):
     bcs_head  +0x1f8: the 8-byte slot at s1 + 16 holding len (atom 32) and the range of body (s3), split on `bltu`;
     bcs_body  +0x224: atom 32 = body + i, the three body bytes as a read-only region at atom 32 (atoms 33, 34, 35),
               the shadow entry of the four bytes at body + i (range_addressable of the body's heap block,
               lib/Reusable/YCbq.v range_addressable_of_block), so the engine decides the three checks; a5 pinned to 1;
               the alias facts s3 + a2 = atom 32 and a4 + a2 = atom 32 + 1 give the engine the addresses a0 and t1;
               the condition facts body + i >= body, i < 2^64 - 1 - body and 2^64 - 1 - body >= i + 3 (the heap
               block: 4096 <= body, body + len below the ceiling) and the range of body decide the five guards as not
               taken; split on the byte compares;
     bcs_bump  +0x29c: split on `bne s4,a2`.
   The loop is an induction on len - 3 - i (bcs_loop) with the invariant bcs_inv at +0x224 and sys_hit bb j = false
   for j < i; at the release a0 is body_check bb by body_check_spec, system_at_true and system_at_false. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0p YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YI08.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib DgnTransportBCJ.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require diginet_msg_next_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnBcCut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The symbolic states                                                 *)
(* ------------------------------------------------------------------ *)

(* Offsets of the scan from the listing's base. *)
Definition SC_AT (k : Z) : Z := AF_diginet_body_check + k.
(* s9 holds the shadow base; the shadow span the token engine checks against. *)
Definition bcs_Bx : sv := SOff 25 0.
Definition bcs_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* The shadow entry of turn i: the four bytes at atom 32 = body + i. *)
Definition bcs_SH : list shent := [mkSHE 32 0 4].
(* 2 ^ 47 - 4: the atom bound of a scan pointer p (s3) and of a1 = p + 1. The shadow entry of a turn covers
   [p, p + 4) and the engine checks its shadow addresses inside bcs_Bspan, which holds for p + 3 <= 2 ^ 47 - 1.
   Every body trans_src_ok places has body + len <= 2 ^ 47 - 1 (decode_rd_ok's amem_range), a machine-stack body
   included (S11-DECISIONS (b)), so a turn's p + 1 <= 2 ^ 47 - 4. *)
Definition bcs_PTRHI : Z := 140737488355324.
Definition bcs_PTR : afact := mkAF 4096 bcs_PTRHI 0.
(* Turn i at +0x224: s3 = body (atom 19), a2 = i (atom 12), a3 = 2^64 - 1 - body (atom 13), a4 = body + 1 (atom 14);
   atom 32 = body + i; body[i], body[i + 1], body[i + 3] as atoms 33, 34, 35. The condition facts decide the guards
   `bltu a0,s3` (+0x228), `bgeu a2,a3` (+0x258) and `bltu a3,a1` (+0x27c); the alias facts name s3 + a2 and a4 + a2. *)
Definition bcs_G : facts := mkFacts
  [(25%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (19%nat, bcs_PTR); (32%nat, bcs_PTR);
   (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0)]
  [mkAC BC_GEU (SOff 32 0) (SOff 19 0); mkAC BC_LTU (SOff 12 0) (SOff 13 0); mkAC BC_GEU (SOff 13 0) (SOff 12 3)]
  [(SAlu ALU_ADD (SOff 19 0) (SOff 12 0), SOff 32 0); (SAlu ALU_ADD (SOff 14 0) (SOff 12 0), SOff 32 1)].
Definition bcs_rg : YP09.region := YP09.mkRegion (Some 32%nat) 0 4 0 0
  [YP09.mkChunk 0 (CVal 1 (SOff 33 0)); YP09.mkChunk 1 (CVal 1 (SOff 34 0)); YP09.mkChunk 3 (CVal 1 (SOff 35 0))].
Definition bcs_ss0 : sstate := mkSS (SC_AT 0x224) sr_atoms [bcs_rg] None bcs_G.
(* a5 = 1 as a literal, so the engine decides the guard `beqz a1` (+0x234). *)
Definition bcs_ss : sstate := mkSS (SC_AT 0x224) (sr_set sr_atoms (15%bv : bv 5) (SLit 1)) [bcs_rg] None bcs_G.
(* The head at +0x1f8: the slot s1 + 16 holding len, as atom 32; the range of body (s3) decides `snez a5,s3`. *)
Definition bch_rg : YP09.region := YP09.mkRegion (Some 9%nat) 16 24 0 0 [YP09.mkChunk 16 (CVal 8 (SOff 32 0))].
Definition bch_ss : sstate := mkSS (SC_AT 0x1f8) sr_atoms [bch_rg] None (mkFacts [(19%nat, bcs_PTR)] [] []).
(* The head when len < 4: no fact on body (an empty body may hold any value); the code reads s3 only after the len
   test (+0x200). *)
Definition bch_ssl : sstate := mkSS (SC_AT 0x1f8) sr_atoms [bch_rg] None (mkFacts [] [] []).
(* The back edge at +0x29c. *)
Definition bcb_ss : sstate := mkSS (SC_AT 0x29c) sr_atoms [] None (mkFacts [] [] []).
(* Registers a run keeps: the ones the release reads, and the loop's own. *)
Definition kp_rel : list (bv 5) := [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 23%bv; 24%bv].
Definition kp_lp : list (bv 5) := [5%bv; 12%bv; 13%bv; 14%bv; 16%bv; 17%bv; 19%bv; 20%bv; 25%bv].
Definition kp_bp : list (bv 5) := [5%bv; 13%bv; 14%bv; 15%bv; 16%bv; 17%bv; 19%bv; 20%bv; 25%bv].
Definition kp_hd : list (bv 5) := [19%bv; 25%bv].

Ltac bcs_kin := unfold kp_rel, kp_lp, kp_bp, kp_hd; cbn [In]; repeat (first [left; reflexivity | right]).

(* ------------------------------------------------------------------ *)
(* Environments, bytes, the model of body_check                        *)
(* ------------------------------------------------------------------ *)

Lemma bcs_agree_ew : forall E0 E n, env_agree 512 E0 E -> (n < 512)%nat -> ew E n = ew E0 n.
Proof. intros E0 E n [H _] Hn. exact (H n Hn). Qed.

Lemma bcs_agree_extK : forall E0 E K ws, (512 <= K)%nat -> env_agree 512 E0 E -> env_agree 512 E0 (extK E K ws).
Proof.
  intros E0 E K ws HK [H1 H2]. destruct (env_agree_extK E K ws) as [A1 A2].
  split; [intros n Hn; rewrite (A1 n ltac:(lia)); exact (H1 n Hn) | rewrite A2; exact H2].
Qed.

Lemma bcs_U : forall E0 E n v, env_agree 512 E0 E -> (n < 512)%nat -> ew E0 n = w64 v -> 0 <= v < 2 ^ 64 ->
  U E (SOff n 0) = v.
Proof. intros E0 E n v HA Hn H Hv. apply U_atom; [rewrite (bcs_agree_ew E0 E n HA Hn); exact H | exact Hv]. Qed.

Lemma bcs_Uoff : forall E0 E n v c, env_agree 512 E0 E -> (n < 512)%nat -> ew E0 n = w64 v -> 0 <= v < 2 ^ 64 ->
  0 <= v + c < 2 ^ 64 -> U E (SOff n c) = v + c.
Proof.
  intros E0 E n v c HA Hn H Hv Hvc.
  apply U_atom_off; [rewrite (bcs_agree_ew E0 E n HA Hn); exact H | exact Hv | exact Hvc].
Qed.

Lemma bcs_den : forall E0 E n v c, env_agree 512 E0 E -> (n < 512)%nat -> ew E0 n = w64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n c) = w64 (v + c).
Proof.
  intros E0 E n v c HA Hn H Hv. cbn [sv_denot]. rewrite (bcs_agree_ew E0 E n HA Hn), H.
  unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* `not` of an atom: 2^64 - 1 - v. *)
Lemma bcs_U_not : forall E0 E n v, env_agree 512 E0 E -> (n < 512)%nat -> ew E0 n = w64 v -> 0 <= v < 2 ^ 64 ->
  U E (SAlu ALU_XOR (SOff n 0) (SLit (-1))) = 2 ^ 64 - 1 - v.
Proof.
  intros E0 E n v HA Hn H Hv. rewrite U_SAlu. cbn [zalu_raw]. rewrite (bcs_U E0 E n v HA Hn H Hv), U_SLit.
  change (zcanon (-1)) with (2 ^ 64 - 1). rewrite YI08.lxor_allones by lia. apply zcanon_id. unfold M64. lia.
Qed.

Lemma bcs_den_lit : forall E a z, U E a = z -> sv_denot E a = w64 z.
Proof.
  intros E a z H. unfold w64. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E a)). f_equal. exact H.
Qed.

Lemma bcs_rel_kept : forall regs r1 r2 sp1 F, bc_regs_rel regs r1 sp1 F ->
  (forall x, In x kp_rel -> YK11.getr r2 x = YK11.getr r1 x) -> bc_regs_rel regs r2 sp1 F.
Proof.
  intros regs r1 r2 sp1 F (H2 & H3 & H4 & H8 & H9 & H23 & H24) HK. unfold bc_regs_rel.
  split; [rewrite HK; [exact H2 | bcs_kin]|].
  split; [rewrite HK; [exact H3 | bcs_kin]|].
  split; [rewrite HK; [exact H4 | bcs_kin]|].
  split; [rewrite HK; [exact H8 | bcs_kin]|].
  split; [rewrite HK; [exact H9 | bcs_kin]|].
  split; [rewrite HK; [exact H23 | bcs_kin]|].
  rewrite HK; [exact H24 | bcs_kin].
Qed.

Lemma bcs_nth_bz : forall (l : list byte) j, nth j (map bz l) 0 = at8 l j.
Proof. intros l j. unfold at8. rewrite <- (map_nth bz l (b8 0) j). reflexivity. Qed.

Lemma bcs_hit0 : forall bb i, at8 bb i <> 240 -> sys_hit bb i = false.
Proof. intros bb i H. unfold sys_hit. apply Z.eqb_neq in H. rewrite H. reflexivity. Qed.

Lemma bcs_hit1 : forall bb i, at8 bb (S i) <> 19 -> sys_hit bb i = false.
Proof. intros bb i H. unfold sys_hit. apply Z.eqb_neq in H. rewrite H, andb_false_r. reflexivity. Qed.

Lemma bcs_hit3 : forall bb i, at8 bb (S (S (S i))) <> 112 -> sys_hit bb i = false.
Proof. intros bb i H. unfold sys_hit. apply Z.eqb_neq in H. rewrite H, andb_false_r. reflexivity. Qed.

Lemma bcs_hit_true : forall bb i, at8 bb i = 240 -> at8 bb (S i) = 19 -> at8 bb (S (S (S i))) = 112 ->
  sys_hit bb i = true.
Proof. intros bb i H0 H1 H3. unfold sys_hit. rewrite H0, H1, H3. reflexivity. Qed.

Lemma bcs_bc0 : forall bb, system_at bb = false -> body_check bb = 0.
Proof. intros bb H. rewrite body_check_spec, H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* One run of the engine over read-only regions                        *)
(* ------------------------------------------------------------------ *)

Section run. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).

(* The run writes no memory (its regions are read-only), so the memory after it is the memory before; the model
   after it is the model before with its materialized part replaced. *)
Lemma bcs_run : forall (Bx : sv) (Bspan : Z * Z) (SH : list shent) (W : world segs) (E : env) (ss : sstate)
    (ms : machine_state) (md : Model) (K : nat) (stop : Z) (st' : shst) (r : ptrun_status tbsym)
    (Q : world segs -> config -> Prop),
  (A_LIM <= K)%nat ->
  img_env VAL A_LIM E ->
  st_ok_pi segs VAL E ss (restrict (w_H W) ms) ->
  sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
  sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
  sym_run_toN_pi_tok transportb_tpi transportb_tw K Bx Bspan SH FUEL stop ss = (st', r) ->
  match r with PTS_call _ => False | PTS_ecall => False | _ => True end ->
  Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
  rs_read_only (ss_mem ss) = true ->
  (forall ws ms' mat,
     length ws = sh_j st' ->
     img_env VAL A_LIM (extK E K ws) ->
     st_ok_pi segs VAL (extK E K ws) (sh_ss st') (restrict (w_H W) ms') ->
     sh_ok segs Bx SH (extK E K ws) (mrestrict (w_H W) (ms_mem ms')) ->
     ms_mem ms' = ms_mem ms ->
     SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr segs W (mkCfg ms md) Q.
Proof.
  intros Bx Bspan SH W E ss ms md K stop st' r Q HK HE HS HSH Hchk Hrun Hnc Hobl Hro HKQ.
  assert (Hrun' : sym_run_toN_pi_tok (ptree_of_list transportb_listing) (tw_of 0 transportb_listing)
                    K Bx Bspan SH FUEL stop ss = (st', r))
    by (rewrite (@pl_tw_eq transportb_listing PL_transportb); exact Hrun).
  destruct (sym_run_to_pi_tok_sound tbsym _ _ VAL _ transportb_listing
     (pa_fetch_ok (PI := PI_transportb)) (@pa_cert _ transportb_listing PI_transportb)
     (@pa_B_ok _ transportb_listing PI_transportb)
     A_LIM A_LIM_text (@pl_lim transportb_listing PL_transportb) (@pl_len transportb_listing PL_transportb)
     K Bx Bspan SH HK FUEL stop E ss (restrict (w_H W) ms) st' r HE HS HSH Hchk Hrun' Hobl)
   as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
  apply (SRr_msteps segs (@pa_wx _ transportb_listing PI_transportb) W ms msr' md Q Hms).
  intros model' Hsame Hcl.
  rewrite (same_but_materialized_wvb md model' Hsame).
  pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
  pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
  assert (Hmem : ms_mem (unrestrict (w_H W) (ms_mem ms) msr') = ms_mem ms).
  { eapply frame_of_read_only; [exact Hro|].
    cbn [unrestrict ms_mem]. apply frame_of_unrestrict.
    cbn [restrict ms_mem] in Hfr. exact Hfr. }
  apply (HKQ ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen HE').
  - rewrite Hrr. destruct r as [ | | s | why]; cbn [ptok_post] in HP;
    [exact HP | destruct HP | destruct Hnc | exact HP].
  - rewrite Hmm. exact Hsh'.
  - exact Hmem.
Qed.

End run.

(* One run to the pc stop, or to the next branch the engine cannot decide. *)
Ltac bcs_step SH stop :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?E ?ss (restrict (w_H ?W) ?ms) |- SRr _ _ (mkCfg _ ?md) ?Q =>
    let K := eval vm_compute in (run_K A_LIM bcs_Bx SH ss) in
    let rr := eval vm_compute in (sym_run_toN_pi_tok transportb_tpi transportb_tw K bcs_Bx bcs_Bspan SH FUEL stop ss) in
    lazymatch rr with
    | (?st', ?res) =>
      lazymatch goal with
      | HSH : sh_ok _ _ _ E _, HEI : img_env _ _ E, HAG : env_agree 512 ?E0 E |- _ =>
        apply (bcs_run bcs_Bx bcs_Bspan SH W E ss ms md K stop st' res Q ltac:(unfold A_LIM; lia) HEI HS HSH
                 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) I
                 ltac:(apply Forall_nil) ltac:(vm_compute; reflexivity));
        clear HS HSH HEI;
        let ws := fresh "ws" in let msn := fresh "ms" in let mat := fresh "mat" in
        let Hlen := fresh "Hlen" in let Hm := fresh "Hmem" in
        intros ws msn mat Hlen HEI HS HSH Hm;
        rewrite ?wvb_collapse;
        apply (bcs_agree_extK E0 E K ws ltac:(lia)) in HAG
      end
    end
  end.

(* The two arms of the branch the state is stuck at. *)
Ltac bcs_branch SH :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?E ?ss (restrict (w_H ?W) ?ms) |- SRr _ _ (mkCfg _ ?md) ?Q =>
    let K := eval vm_compute in (run_K A_LIM bcs_Bx SH ss) in
    let why := psym_why_tok transportb_tpi transportb_tw K bcs_Bx bcs_Bspan SH (start K bcs_Bx bcs_Bspan SH ss) in
    lazymatch why with
    | SR_branch ?c ?a ?b =>
      apply (paj_branch (PI := PI_transportb) W E ss ms md Q c a b HS); clear HS;
      let Hc := fresh "Hc" in intros Hc HS
    end
  end.

(* The value of register r in the machine state HS describes. *)
Ltac bcs_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.

(* The machine state at the stop: its shape and its memory. *)
Ltac bcs_shape :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ => pmkst HS end;
  repeat match goal with H : ms_mem ?a = ms_mem ?b |- _ => rewrite H end;
  cbn [ms_mem YK11.mkst].

(* ------------------------------------------------------------------ *)
(* The scan                                                            *)
(* ------------------------------------------------------------------ *)

Section scan. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Definition bcs_E (r : bvmap 5 word) (p b0 b1 b3 : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg r [w64 p; w64 b0; w64 b1; w64 b3]).

Lemma bcs_ew_reg : forall (r : bvmap 5 word) extra n (x : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned x ->
  ew (Eimg (PI := PI_transportb) (Ereg r extra)) n = YK11.getr r x.
Proof. intros r extra n x Hn Hx. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hx. Qed.

Lemma bcs_E_ex : forall r p b0 b1 b3,
  ew (bcs_E r p b0 b1 b3) 32 = w64 p /\ ew (bcs_E r p b0 b1 b3) 33 = w64 b0 /\
  ew (bcs_E r p b0 b1 b3) 34 = w64 b1 /\ ew (bcs_E r p b0 b1 b3) 35 = w64 b3.
Proof.
  intros r p b0 b1 b3. unfold bcs_E. rewrite !Eimg_low by (unfold A_TEXT; lia).
  split; [exact (ew_Ereg_extra r _ 0) | split; [exact (ew_Ereg_extra r _ 1) |
    split; [exact (ew_Ereg_extra r _ 2) | exact (ew_Ereg_extra r _ 3)]]].
Qed.

Lemma bcs_agree32 : forall (r : bvmap 5 word) extra E,
  env_agree 512 (Eimg (PI := PI_transportb) (Ereg r extra)) E -> env_agree 32 (Ereg r extra) E.
Proof.
  intros r extra E [H1 H2]. split.
  - intros n Hn. rewrite (H1 n ltac:(lia)). apply Eimg_low. unfold A_TEXT. lia.
  - rewrite H2. reflexivity.
Qed.

(* The registers of l the run kept, from the entry registers r0 (env Eimg (Ereg r0 ex)). *)
Ltac bcs_kr r0 ex l KR :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?Wx) ?msx), HAG : env_agree 512 _ ?Ex |- _ =>
    pose proof (regs_kept_of_st_ok_pi Ex ssx (restrict (w_H Wx) msx) r0 ex l HS (bcs_agree32 r0 ex Ex HAG)
      ltac:(vm_compute; reflexivity)) as KR
  end.

Lemma bcs_chunk1 : forall (E : env) (m : word -> option byte) (k : nat) (b o a v : Z),
  ew E k = w64 v -> 0 <= v < 256 -> b + o = a -> val_mem segs m a 1 v ->
  YP09.chunk_ok segs E m b (YP09.mkChunk o (CVal 1 (SOff k 0))).
Proof.
  intros E m k b o a v Hk Hv Ha Hm.
  apply (chunk_ok_val segs E m b o 1 (SOff k 0) v).
  - cbn [sv_denot]. rewrite Hk, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - cbn. lia.
  - cbn. lia.
  - rewrite Ha. exact Hm.
Qed.

(* The seat of turn i at +0x224: s3 = body, a2 = i, a3 = 2^64 - 1 - body, a4 = body + 1, a5 = 1, s9 the shadow base,
   atom 32 = body + i, the three bytes in the region. *)
Lemma bcs_entry : forall (W : world segs) (r : bvmap 5 word) (mem : word -> option byte) (body i b0 b1 b3 : Z),
  YK11.getr r 19 = w64 body -> YK11.getr r 12 = w64 i -> YK11.getr r 13 = w64 (2 ^ 64 - 1 - body) ->
  YK11.getr r 14 = w64 (body + 1) -> YK11.getr r 15 = w64 1 -> YK11.getr r 25 = w64 SHADOW_OFF ->
  4096 <= body -> 0 <= i -> body + i + 1 <= bcs_PTRHI ->
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b3 < 256 ->
  val_mem segs (mrestrict (w_H W) mem) (body + i) 1 b0 ->
  val_mem segs (mrestrict (w_H W) mem) (body + i + 1) 1 b1 ->
  val_mem segs (mrestrict (w_H W) mem) (body + i + 3) 1 b3 ->
  st_ok_pi segs VAL (bcs_E r (body + i) b0 b1 b3) bcs_ss
    (restrict (w_H W) (@YK11.mkst fx r (Z_to_bv 64 (BASE + SC_AT 0x224)) mem (YK11.seg_rom segs))).
Proof.
  intros W r mem body i b0 b1 b3 R19 R12 R13 R14 R15 R25 Hb Hi Hp HB0 HB1 HB3 V0 V1 V3.
  unfold bcs_PTRHI in Hp.
  destruct (bcs_E_ex r (body + i) b0 b1 b3) as (E32 & E33 & E34 & E35).
  assert (A19 : ew (bcs_E r (body + i) b0 b1 b3) 19 = w64 body)
    by (unfold bcs_E; rewrite (bcs_ew_reg r _ 19 19%bv ltac:(lia) eq_refl); exact R19).
  assert (A12 : ew (bcs_E r (body + i) b0 b1 b3) 12 = w64 i)
    by (unfold bcs_E; rewrite (bcs_ew_reg r _ 12 12%bv ltac:(lia) eq_refl); exact R12).
  assert (A13 : ew (bcs_E r (body + i) b0 b1 b3) 13 = w64 (2 ^ 64 - 1 - body))
    by (unfold bcs_E; rewrite (bcs_ew_reg r _ 13 13%bv ltac:(lia) eq_refl); exact R13).
  assert (A14 : ew (bcs_E r (body + i) b0 b1 b3) 14 = w64 (body + 1))
    by (unfold bcs_E; rewrite (bcs_ew_reg r _ 14 14%bv ltac:(lia) eq_refl); exact R14).
  assert (A25 : ew (bcs_E r (body + i) b0 b1 b3) 25 = w64 SHADOW_OFF)
    by (unfold bcs_E; rewrite (bcs_ew_reg r _ 25 25%bv ltac:(lia) eq_refl); exact R25).
  assert (U19 : bv_unsigned (ew (bcs_E r (body + i) b0 b1 b3) 19) = body)
    by (rewrite A19; unfold w64; apply unsigned_lit_small; lia).
  assert (U25 : bv_unsigned (ew (bcs_E r (body + i) b0 b1 b3) 25) = SHADOW_OFF)
    by (rewrite A25; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U32 : bv_unsigned (ew (bcs_E r (body + i) b0 b1 b3) 32) = body + i)
    by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew (bcs_E r (body + i) b0 b1 b3) 33) = b0)
    by (rewrite E33; unfold w64; apply unsigned_lit_small; lia).
  assert (U34 : bv_unsigned (ew (bcs_E r (body + i) b0 b1 b3) 34) = b1)
    by (rewrite E34; unfold w64; apply unsigned_lit_small; lia).
  assert (U35 : bv_unsigned (ew (bcs_E r (body + i) b0 b1 b3) 35) = b3)
    by (rewrite E35; unfold w64; apply unsigned_lit_small; lia).
  assert (W19 : U (bcs_E r (body + i) b0 b1 b3) (SOff 19 0) = body) by (apply U_atom; [exact A19 | lia]).
  assert (W12 : U (bcs_E r (body + i) b0 b1 b3) (SOff 12 0) = i) by (apply U_atom; [exact A12 | lia]).
  assert (W12' : U (bcs_E r (body + i) b0 b1 b3) (SOff 12 3) = i + 3) by (apply U_atom_off; [exact A12 | lia | lia]).
  assert (W13 : U (bcs_E r (body + i) b0 b1 b3) (SOff 13 0) = 2 ^ 64 - 1 - body) by (apply U_atom; [exact A13 | lia]).
  assert (W14 : U (bcs_E r (body + i) b0 b1 b3) (SOff 14 0) = body + 1) by (apply U_atom; [exact A14 | lia]).
  assert (W32 : U (bcs_E r (body + i) b0 b1 b3) (SOff 32 0) = body + i) by (apply U_atom; [exact E32 | lia]).
  assert (W32' : U (bcs_E r (body + i) b0 b1 b3) (SOff 32 1) = body + i + 1)
    by (apply U_atom_off; [exact E32 | lia | lia]).
  rewrite restrict_mkst_fx. unfold bcs_ss.
  refine (st_ok_pi_pin_reg' _ bcs_ss0 _ (15%bv : bv 5) 1 _ _ eq_refl); [|exact R15].
  unfold bcs_ss0. apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold bcs_rg, YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + apply (bcs_chunk1 _ _ 33 (body + i) 0 (body + i) b0); [exact E33 | lia | lia | exact V0].
    + apply (bcs_chunk1 _ _ 34 (body + i) 1 (body + i + 1) b1); [exact E34 | lia | lia | exact V1].
    + apply (bcs_chunk1 _ _ 35 (body + i) 3 (body + i + 3) b3); [exact E35 | lia | lia | exact V3].
  - exact (conj I I).
  - unfold facts_ok, bcs_G. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split].
    + unfold afact_ok, bcs_PTR, bcs_PTRHI. cbn [af_lo af_hi af_al2].
      rewrite U25, U19, U32, U33, U34, U35. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF.
      repeat split; try exact I; lia.
    + unfold acond_ok. cbn [ac_c ac_a ac_b].
      rewrite !branch_geu_U, !branch_ltu_U, W32, W19, W12, W13, W12'.
      split; [apply negb_true_iff, Z.ltb_ge; lia|].
      split; [apply Z.ltb_lt; lia|].
      split; [apply negb_true_iff, Z.ltb_ge; lia | exact I].
    + split; [|split; [|exact I]]; apply U_inj; rewrite U_SAlu; cbn [zalu_raw].
      * rewrite W19, W12, W32. apply zcanon_id. unfold M64. lia.
      * rewrite W14, W12, W32'. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* The shadow entry of turn i: [p, p + 4) inside the addressable range [a, a + n). *)
Lemma bcs_shok : forall (W : world segs) (r : bvmap 5 word) (mem : word -> option byte) (p b0 b1 b3 a n : Z),
  YK11.getr r 25 = w64 SHADOW_OFF -> 0 <= p < 2 ^ 64 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n -> a <= p -> p + 4 <= a + n ->
  (forall x, a <= x < a + n -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)) ->
  sh_ok segs bcs_Bx bcs_SH (bcs_E r p b0 b1 b3) (mrestrict (w_H W) mem).
Proof.
  intros W r mem p b0 b1 b3 a n R25 Hp HRA Ha1 Ha2 Happ.
  destruct (bcs_E_ex r p b0 b1 b3) as (E32 & _ & _ & _).
  apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range segs (w_H W) mem (bcs_E r p b0 b1 b3) bcs_Bx 32%nat a n p 0 4).
  - exact HRA.
  - unfold bcs_Bx. apply U_atom; [|unfold SHADOW_OFF; lia].
    unfold bcs_E. rewrite (bcs_ew_reg r _ 25 25%bv ltac:(lia) eq_refl). exact R25.
  - apply U_atom; [exact E32 | lia].
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx. apply Happ. lia.
Qed.

(* The facts of the walk the scan uses: the body's bytes, their shadow (trans_src_ok at the cut's state), the slot of
   len, the release. The body's place is known when there are bytes (the scan reads them only when len >= 4). *)
Variables (W2 : world segs) (mem2 : word -> option byte) (regs : bvmap 5 word) (body : Z) (bb : list byte)
  (sp1 F : Z).
Variable Q : world segs -> config -> Prop.
Variable J : Model -> Prop.
Hypothesis HJmat : forall md X, J md -> J (with_vm_backing (m_vm_lazy md) X md).
Hypothesis HREL : forall (regs' : bvmap 5 word) (md' : Model),
  bc_regs_rel regs regs' sp1 F -> YK11.getr regs' 10 = w64 (body_check bb) -> J md' ->
  SRr segs W2 (mkCfg (@YK11.mkst fx regs' (Z_to_bv 64 (BASE + BC_REL)) mem2 (YK11.seg_rom segs)) md') Q.
Hypothesis Hb4096 : (0 < length bb)%nat -> 4096 <= body.
Hypothesis Hbhi : (0 < length bb)%nat -> body + Z.of_nat (length bb) <= 140737488355327.
Hypothesis HRA : range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF body (Z.of_nat (length bb)).
Hypothesis HAPP : forall x, body <= x < body + Z.of_nat (length bb) ->
  ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416).
Hypothesis HG : garr8 segs (mrestrict (w_H W2) mem2) body (map bz bb).
Hypothesis Hslot : rdword (aview segs (w_H W2) mem2) (sp1 + 16) = Some (Z.of_nat (length bb)).
Hypothesis Hsp1 : 0 <= sp1 <= 2 ^ 47.

Local Abbreviation bcs_at pc r md :=
  (mkCfg (@YK11.mkst fx r (Z_to_bv 64 (BASE + pc)) mem2 (YK11.seg_rom segs)) md).

Lemma bcs_byte : forall j, (j < length bb)%nat ->
  val_mem segs (mrestrict (w_H W2) mem2) (body + Z.of_nat j) 1 (at8 bb j) /\ 0 <= at8 bb j < 256.
Proof.
  intros j Hj. assert (Hj' : (j < length (map bz bb))%nat) by (rewrite length_map; exact Hj).
  destruct (HG j Hj') as [Hv Hr]. rewrite bcs_nth_bz in Hv, Hr. exact (conj Hv Hr).
Qed.

(* The registers at +0x224 before turn i. *)
Definition bcs_inv (r : bvmap 5 word) (i : nat) : Prop :=
  YK11.getr r 19 = w64 body /\ YK11.getr r 12 = w64 (Z.of_nat i) /\
  YK11.getr r 13 = w64 (2 ^ 64 - 1 - body) /\ YK11.getr r 20 = w64 (Z.of_nat (length bb) - 3) /\
  YK11.getr r 14 = w64 (body + 1) /\ YK11.getr r 15 = w64 1 /\
  YK11.getr r 16 = w64 240 /\ YK11.getr r 17 = w64 19 /\ YK11.getr r 5 = w64 112 /\
  YK11.getr r 25 = w64 SHADOW_OFF /\ bc_regs_rel regs r sp1 F.

(* What the next turn gives. *)
Definition bcs_K (i : nat) : Prop :=
  forall (r : bvmap 5 word) (md : Model), (S i + 3 < length bb)%nat ->
    (forall j, (j < S i)%nat -> sys_hit bb j = false) -> bcs_inv r (S i) -> J md ->
    SRr segs W2 (bcs_at (SC_AT 0x224) r md) Q.

Lemma bcs_inv_kept : forall r1 r2 i, bcs_inv r1 i ->
  (forall x, In x kp_rel -> YK11.getr r2 x = YK11.getr r1 x) ->
  (forall x, In x kp_lp -> YK11.getr r2 x = YK11.getr r1 x) ->
  YK11.getr r2 15 = w64 1 -> bcs_inv r2 i.
Proof.
  intros r1 r2 i (R19 & R12 & R13 & R20 & R14 & R15 & R16 & R17 & R5 & R25 & HRL) K1 K2 Q15. unfold bcs_inv.
  split; [rewrite K2; [exact R19 | bcs_kin]|].
  split; [rewrite K2; [exact R12 | bcs_kin]|].
  split; [rewrite K2; [exact R13 | bcs_kin]|].
  split; [rewrite K2; [exact R20 | bcs_kin]|].
  split; [rewrite K2; [exact R14 | bcs_kin]|].
  split; [exact Q15|].
  split; [rewrite K2; [exact R16 | bcs_kin]|].
  split; [rewrite K2; [exact R17 | bcs_kin]|].
  split; [rewrite K2; [exact R5 | bcs_kin]|].
  split; [rewrite K2; [exact R25 | bcs_kin]|].
  exact (bcs_rel_kept regs r1 r2 sp1 F HRL K1).
Qed.

(* +0x29c .. +0x2a4: a2 one up; `bne s4,a2` back to +0x224, else +0x2cc and the release. *)
Lemma bcs_bump : forall (i : nat) (r0 : bvmap 5 word) (md : Model),
  (i + 3 < length bb)%nat -> (forall j, (j <= i)%nat -> sys_hit bb j = false) -> bcs_inv r0 i -> J md -> bcs_K i ->
  SRr segs W2 (bcs_at (SC_AT 0x29c) r0 md) Q.
Proof.
  intros i r0 md Hi Hpre Hinv HJ HK. unfold bcs_K in HK.
  pose proof Hinv as (R19 & R12 & R13 & R20 & R14 & R15 & R16 & R17 & R5 & R25 & HRL).
  assert (HS : st_ok_pi segs VAL (Eimg (PI := PI_transportb) (Ereg r0 [])) bcb_ss
    (restrict (w_H W2) (@YK11.mkst fx r0 (Z_to_bv 64 (BASE + SC_AT 0x29c)) mem2 (YK11.seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold bcb_ss. apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_nil.
    - exact I.
    - exact (conj I (conj I I)). }
  assert (HSH : sh_ok segs bcs_Bx [] (Eimg (PI := PI_transportb) (Ereg r0 [])) (mrestrict (w_H W2) mem2))
    by apply Forall_nil.
  assert (HEI : img_env VAL A_LIM (Eimg (PI := PI_transportb) (Ereg r0 []))) by apply Eimg_env.
  pose proof (env_agree_refl 512 (Eimg (PI := PI_transportb) (Ereg r0 []))) as HAG.
  assert (X12 : ew (Eimg (PI := PI_transportb) (Ereg r0 [])) 12 = w64 (Z.of_nat i))
    by (rewrite (bcs_ew_reg r0 _ 12 12%bv ltac:(lia) eq_refl); exact R12).
  assert (X20 : ew (Eimg (PI := PI_transportb) (Ereg r0 [])) 20 = w64 (Z.of_nat (length bb) - 3))
    by (rewrite (bcs_ew_reg r0 _ 20 20%bv ltac:(lia) eq_refl); exact R20).
  bcs_step ([] : list shent) (SC_AT 0x224).
  bcs_branch ([] : list shent).
  - (* len - 3 <> i + 1: turn i + 1 *)
    rewrite branch_ne_U in Hc.
    rewrite (bcs_U _ _ 20 _ HAG ltac:(lia) X20 ltac:(lia)),
      (bcs_Uoff _ _ 12 _ 1 HAG ltac:(lia) X12 ltac:(lia) ltac:(lia)) in Hc.
    apply negb_true_iff, Z.eqb_neq in Hc.
    bcs_step ([] : list shent) (SC_AT 0x224).
    bcs_kr r0 ([] : list word) kp_rel KR1. bcs_kr r0 ([] : list word) kp_bp KR2.
    bcs_reg HS (12%bv : bv 5) (w64 (Z.of_nat (S i))) Q12
      ltac:(rewrite (bcs_den _ _ 12 _ 1 HAG ltac:(lia) X12 ltac:(lia)); f_equal; lia).
    bcs_shape.
    apply HK; [lia | intros j Hj; apply Hpre; lia | | apply HJmat; exact HJ].
    unfold bcs_inv.
    split; [etransitivity; [apply KR2; bcs_kin | exact R19]|].
    split; [exact Q12|].
    split; [etransitivity; [apply KR2; bcs_kin | exact R13]|].
    split; [etransitivity; [apply KR2; bcs_kin | exact R20]|].
    split; [etransitivity; [apply KR2; bcs_kin | exact R14]|].
    split; [etransitivity; [apply KR2; bcs_kin | exact R15]|].
    split; [etransitivity; [apply KR2; bcs_kin | exact R16]|].
    split; [etransitivity; [apply KR2; bcs_kin | exact R17]|].
    split; [etransitivity; [apply KR2; bcs_kin | exact R5]|].
    split; [etransitivity; [apply KR2; bcs_kin | exact R25]|].
    exact (bcs_rel_kept regs r0 _ sp1 F HRL KR1).
  - (* len - 3 = i + 1: the scan ends, a0 = 0 *)
    rewrite branch_ne_U in Hc.
    rewrite (bcs_U _ _ 20 _ HAG ltac:(lia) X20 ltac:(lia)),
      (bcs_Uoff _ _ 12 _ 1 HAG ltac:(lia) X12 ltac:(lia) ltac:(lia)) in Hc.
    apply negb_false_iff, Z.eqb_eq in Hc.
    assert (Hbc : body_check bb = 0)
      by (apply bcs_bc0, system_at_false; intros j Hj; apply Hpre; lia).
    bcs_step ([] : list shent) (SC_AT 0x2d0).
    bcs_kr r0 ([] : list word) kp_rel KR1.
    bcs_reg HS (10%bv : bv 5) (w64 (body_check bb)) Q10 ltac:(rewrite Hbc; reflexivity).
    bcs_shape.
    apply HREL; [exact (bcs_rel_kept regs r0 _ sp1 F HRL KR1) | exact Q10 | apply HJmat; exact HJ].
Qed.

(* +0x224 .. +0x298, turn i: the guards, the three checked loads and compares. *)
Lemma bcs_body : forall (i : nat) (r0 : bvmap 5 word) (md : Model),
  (i + 3 < length bb)%nat -> (forall j, (j < i)%nat -> sys_hit bb j = false) -> bcs_inv r0 i -> J md -> bcs_K i ->
  SRr segs W2 (bcs_at (SC_AT 0x224) r0 md) Q.
Proof.
  intros i r0 md Hi Hpre Hinv HJ HK.
  pose proof (Hb4096 ltac:(lia)) as Hb1. pose proof (Hbhi ltac:(lia)) as Hb2.
  destruct (bcs_byte i ltac:(lia)) as [V0 B0].
  destruct (bcs_byte (S i) ltac:(lia)) as [V1 B1].
  destruct (bcs_byte (S (S (S i))) ltac:(lia)) as [V3 B3].
  replace (body + Z.of_nat (S i)) with (body + Z.of_nat i + 1) in V1 by lia.
  replace (body + Z.of_nat (S (S (S i)))) with (body + Z.of_nat i + 3) in V3 by lia.
  remember (at8 bb i) as b0 eqn:Eb0. remember (at8 bb (S i)) as b1 eqn:Eb1.
  remember (at8 bb (S (S (S i)))) as b3 eqn:Eb3.
  pose proof Hinv as (R19 & R12 & R13 & R20 & R14 & R15 & R16 & R17 & R5 & R25 & HRL).
  pose proof (bcs_entry W2 r0 mem2 body (Z.of_nat i) b0 b1 b3 R19 R12 R13 R14 R15 R25 Hb1 ltac:(lia)
    ltac:(unfold bcs_PTRHI; lia) B0 B1 B3 V0 V1 V3) as HS.
  pose proof (bcs_shok W2 r0 mem2 (body + Z.of_nat i) b0 b1 b3 body (Z.of_nat (length bb)) R25 ltac:(lia)
    HRA ltac:(lia) ltac:(lia) HAPP) as HSH.
  assert (HEI : img_env VAL A_LIM (bcs_E r0 (body + Z.of_nat i) b0 b1 b3)) by apply Eimg_env.
  pose proof (env_agree_refl 512 (bcs_E r0 (body + Z.of_nat i) b0 b1 b3)) as HAG.
  destruct (bcs_E_ex r0 (body + Z.of_nat i) b0 b1 b3) as (X32 & X33 & X34 & X35).
  assert (X16 : ew (bcs_E r0 (body + Z.of_nat i) b0 b1 b3) 16 = w64 240)
    by (unfold bcs_E; rewrite (bcs_ew_reg r0 _ 16 16%bv ltac:(lia) eq_refl); exact R16).
  assert (X17 : ew (bcs_E r0 (body + Z.of_nat i) b0 b1 b3) 17 = w64 19)
    by (unfold bcs_E; rewrite (bcs_ew_reg r0 _ 17 17%bv ltac:(lia) eq_refl); exact R17).
  assert (X5 : ew (bcs_E r0 (body + Z.of_nat i) b0 b1 b3) 5 = w64 112)
    by (unfold bcs_E; rewrite (bcs_ew_reg r0 _ 5 5%bv ltac:(lia) eq_refl); exact R5).
  bcs_step bcs_SH (SC_AT 0x29c).
  bcs_branch bcs_SH.
  - (* body[i] <> 0xf0 *)
    rewrite branch_ne_U in Hc.
    rewrite (bcs_U _ _ 33 b0 HAG ltac:(lia) X33 ltac:(lia)), (bcs_U _ _ 16 240 HAG ltac:(lia) X16 ltac:(lia)) in Hc.
    apply negb_true_iff, Z.eqb_neq in Hc.
    bcs_step bcs_SH (SC_AT 0x29c).
    bcs_kr r0 [w64 (body + Z.of_nat i); w64 b0; w64 b1; w64 b3] kp_rel KR1.
    bcs_kr r0 [w64 (body + Z.of_nat i); w64 b0; w64 b1; w64 b3] kp_lp KR2.
    bcs_reg HS (15%bv : bv 5) (w64 1) Q15 ltac:(reflexivity).
    bcs_shape.
    apply (bcs_bump i _ _ Hi).
    + intros j Hj. destruct (Nat.eq_dec j i) as [->|Hne];
        [apply bcs_hit0; rewrite <- Eb0; exact Hc | apply Hpre; lia].
    + exact (bcs_inv_kept r0 _ i Hinv KR1 KR2 Q15).
    + apply HJmat. exact HJ.
    + exact HK.
  - (* body[i] = 0xf0 *)
    rewrite branch_ne_U in Hc.
    rewrite (bcs_U _ _ 33 b0 HAG ltac:(lia) X33 ltac:(lia)), (bcs_U _ _ 16 240 HAG ltac:(lia) X16 ltac:(lia)) in Hc.
    apply negb_false_iff, Z.eqb_eq in Hc.
    bcs_step bcs_SH (SC_AT 0x29c).
    bcs_branch bcs_SH.
    + (* body[i + 1] <> 0x13 *)
      rewrite branch_ne_U in Hc0.
      rewrite (bcs_U _ _ 34 b1 HAG ltac:(lia) X34 ltac:(lia)), (bcs_U _ _ 17 19 HAG ltac:(lia) X17 ltac:(lia))
        in Hc0.
      apply negb_true_iff, Z.eqb_neq in Hc0.
      bcs_step bcs_SH (SC_AT 0x29c).
      bcs_kr r0 [w64 (body + Z.of_nat i); w64 b0; w64 b1; w64 b3] kp_rel KR1.
      bcs_kr r0 [w64 (body + Z.of_nat i); w64 b0; w64 b1; w64 b3] kp_lp KR2.
      bcs_reg HS (15%bv : bv 5) (w64 1) Q15 ltac:(reflexivity).
      bcs_shape.
      apply (bcs_bump i _ _ Hi).
      * intros j Hj. destruct (Nat.eq_dec j i) as [->|Hne];
          [apply bcs_hit1; rewrite <- Eb1; exact Hc0 | apply Hpre; lia].
      * exact (bcs_inv_kept r0 _ i Hinv KR1 KR2 Q15).
      * apply HJmat. exact HJ.
      * exact HK.
    + (* body[i + 1] = 0x13 *)
      rewrite branch_ne_U in Hc0.
      rewrite (bcs_U _ _ 34 b1 HAG ltac:(lia) X34 ltac:(lia)), (bcs_U _ _ 17 19 HAG ltac:(lia) X17 ltac:(lia))
        in Hc0.
      apply negb_false_iff, Z.eqb_eq in Hc0.
      bcs_step bcs_SH (SC_AT 0x29c).
      bcs_branch bcs_SH.
      * (* body[i + 3] = 0x70: F0 13 xx 70 at i, a0 = -10 *)
        rewrite branch_eq_U in Hc1.
        rewrite (bcs_U _ _ 35 b3 HAG ltac:(lia) X35 ltac:(lia)), (bcs_U _ _ 5 112 HAG ltac:(lia) X5 ltac:(lia))
          in Hc1.
        apply Z.eqb_eq in Hc1.
        assert (Hhit : sys_hit bb i = true) by (apply bcs_hit_true; congruence).
        assert (Hbc : body_check bb = -10)
          by (apply (proj2 (body_check_refused bb)), (proj2 (system_at_true bb)); exists i; split; [lia | exact Hhit]).
        bcs_step bcs_SH (SC_AT 0x2d0).
        bcs_kr r0 [w64 (body + Z.of_nat i); w64 b0; w64 b1; w64 b3] kp_rel KR1.
        bcs_reg HS (10%bv : bv 5) (w64 (body_check bb)) Q10
          ltac:(cbn [sv_denot]; rewrite Hbc; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity).
        bcs_shape.
        apply HREL; [exact (bcs_rel_kept regs r0 _ sp1 F HRL KR1) | exact Q10 | apply HJmat; exact HJ].
      * (* body[i + 3] <> 0x70 *)
        rewrite branch_eq_U in Hc1.
        rewrite (bcs_U _ _ 35 b3 HAG ltac:(lia) X35 ltac:(lia)), (bcs_U _ _ 5 112 HAG ltac:(lia) X5 ltac:(lia))
          in Hc1.
        apply Z.eqb_neq in Hc1.
        bcs_step bcs_SH (SC_AT 0x29c).
        bcs_kr r0 [w64 (body + Z.of_nat i); w64 b0; w64 b1; w64 b3] kp_rel KR1.
        bcs_kr r0 [w64 (body + Z.of_nat i); w64 b0; w64 b1; w64 b3] kp_lp KR2.
        bcs_reg HS (15%bv : bv 5) (w64 1) Q15 ltac:(reflexivity).
        bcs_shape.
        apply (bcs_bump i _ _ Hi).
        -- intros j Hj. destruct (Nat.eq_dec j i) as [->|Hne];
             [apply bcs_hit3; rewrite <- Eb3; exact Hc1 | apply Hpre; lia].
        -- exact (bcs_inv_kept r0 _ i Hinv KR1 KR2 Q15).
        -- apply HJmat. exact HJ.
        -- exact HK.
Qed.

(* The loop, by induction on the turns left. *)
Lemma bcs_loop : forall (n i : nat) (r0 : bvmap 5 word) (md : Model),
  n = (length bb - 3 - i)%nat -> (i + 3 < length bb)%nat -> (forall j, (j < i)%nat -> sys_hit bb j = false) ->
  bcs_inv r0 i -> J md -> SRr segs W2 (bcs_at (SC_AT 0x224) r0 md) Q.
Proof.
  induction n as [|n IH]; intros i r0 md Hn Hi Hpre Hinv HJ; [lia|].
  apply (bcs_body i r0 md Hi Hpre Hinv HJ). unfold bcs_K.
  intros r1 md1 Hi1 Hpre1 Hinv1 HJ1. exact (IH (S i) r1 md1 ltac:(lia) Hi1 Hpre1 Hinv1 HJ1).
Qed.

(* +0x1f8: len from the slot; len < 4 gives a0 = 0 and the release, else the set-up and the loop from turn 0. *)
Lemma bcs_head : forall (r2 : bvmap 5 word) (md : Model),
  bc_regs_scan regs r2 body sp1 F -> J md -> SRr segs W2 (bcs_at BC_SCAN r2 md) Q.
Proof using HJmat HREL Hb4096 Hbhi HRA HAPP HG Hslot Hsp1.
  intros r2 md (HRL & R19 & R25) HJ.
  pose proof HRL as (R2 & R3 & R4 & R8 & R9 & R23 & R24).
  assert (U9 : bv_unsigned (ew (Eimg (PI := PI_transportb) (Ereg r2 [w64 (Z.of_nat (length bb))])) 9) = sp1)
    by (rewrite (bcs_ew_reg r2 _ 9 9%bv ltac:(lia) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (X32 : ew (Eimg (PI := PI_transportb) (Ereg r2 [w64 (Z.of_nat (length bb))])) 32
                = w64 (Z.of_nat (length bb)))
    by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra r2 _ 0)).
  assert (X19 : ew (Eimg (PI := PI_transportb) (Ereg r2 [w64 (Z.of_nat (length bb))])) 19 = w64 body)
    by (rewrite (bcs_ew_reg r2 _ 19 19%bv ltac:(lia) eq_refl); exact R19).
  assert (HSH : sh_ok segs bcs_Bx [] (Eimg (PI := PI_transportb) (Ereg r2 [w64 (Z.of_nat (length bb))]))
                  (mrestrict (w_H W2) mem2)) by apply Forall_nil.
  assert (HEI : img_env VAL A_LIM (Eimg (PI := PI_transportb) (Ereg r2 [w64 (Z.of_nat (length bb))])))
    by apply Eimg_env.
  pose proof (env_agree_refl 512 (Eimg (PI := PI_transportb) (Ereg r2 [w64 (Z.of_nat (length bb))]))) as HAG.
  destruct (Z_lt_le_dec (Z.of_nat (length bb)) 4) as [Hl4 | Hl4].
  - (* len < 4: a0 = 0 and the release; s3 is not read, so the head state has no fact on body *)
    assert (HS : st_ok_pi segs VAL (Eimg (PI := PI_transportb) (Ereg r2 [w64 (Z.of_nat (length bb))])) bch_ssl
      (restrict (w_H W2) (@YK11.mkst fx r2 (Z_to_bv 64 (BASE + BC_SCAN)) mem2 (YK11.seg_rom segs)))).
    { rewrite restrict_mkst_fx. unfold bch_ssl.
      apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
      - apply regs_ok_Eimg_Ereg.
      - vm_compute. reflexivity.
      - apply Forall_cons; [|apply Forall_nil]. unfold bch_rg, YP09.region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val segs _ _ sp1 16 8 (SOff 32 0) (Z.of_nat (length bb))).
        + cbn [sv_denot]. rewrite X32, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
        + cbn. lia.
        + cbn. lia.
        + apply val_mem_of_rdword. exact Hslot.
      - exact (conj I I).
      - exact (conj I (conj I I)). }
    bcs_step ([] : list shent) (SC_AT 0x224).
    bcs_branch ([] : list shent).
    + rewrite branch_ltu_U in Hc.
      rewrite (bcs_U _ _ 32 _ HAG ltac:(lia) X32 ltac:(lia)), U_lit in Hc by lia.
      apply Z.ltb_lt in Hc.
      assert (Hbc : body_check bb = 0) by (apply bcs_bc0, system_at_false; intros j Hj; lia).
      bcs_step ([] : list shent) (SC_AT 0x2d0).
      bcs_kr r2 [w64 (Z.of_nat (length bb))] kp_rel KR1.
      bcs_reg HS (10%bv : bv 5) (w64 (body_check bb)) Q10 ltac:(rewrite Hbc; reflexivity).
      bcs_shape.
      apply HREL; [exact (bcs_rel_kept regs r2 _ sp1 F HRL KR1) | exact Q10 | apply HJmat; exact HJ].
    + exfalso. rewrite branch_ltu_U in Hc.
      rewrite (bcs_U _ _ 32 _ HAG ltac:(lia) X32 ltac:(lia)), U_lit in Hc by lia.
      apply Z.ltb_ge in Hc. lia.
  - (* len >= 4: the body has bytes, so its place bounds s3 *)
    pose proof (Hb4096 ltac:(lia)) as Hb1. pose proof (Hbhi ltac:(lia)) as Hb2.
    assert (U19 : bv_unsigned (ew (Eimg (PI := PI_transportb) (Ereg r2 [w64 (Z.of_nat (length bb))])) 19) = body)
      by (rewrite (bcs_ew_reg r2 _ 19 19%bv ltac:(lia) eq_refl), R19; unfold w64; apply unsigned_lit_small; lia).
    assert (HS : st_ok_pi segs VAL (Eimg (PI := PI_transportb) (Ereg r2 [w64 (Z.of_nat (length bb))])) bch_ss
      (restrict (w_H W2) (@YK11.mkst fx r2 (Z_to_bv 64 (BASE + BC_SCAN)) mem2 (YK11.seg_rom segs)))).
    { rewrite restrict_mkst_fx. unfold bch_ss.
      apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
      - apply regs_ok_Eimg_Ereg.
      - vm_compute. reflexivity.
      - apply Forall_cons; [|apply Forall_nil]. unfold bch_rg, YP09.region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val segs _ _ sp1 16 8 (SOff 32 0) (Z.of_nat (length bb))).
        + cbn [sv_denot]. rewrite X32, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
        + cbn. lia.
        + cbn. lia.
        + apply val_mem_of_rdword. exact Hslot.
      - exact (conj I I).
      - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
        split; [|exact (conj I I)]. split; [|exact I].
        unfold afact_ok, bcs_PTR, bcs_PTRHI. cbn [af_lo af_hi af_al2].
        rewrite U19, Z.pow_0_r, Z.mod_1_r. repeat split; lia. }
    bcs_step ([] : list shent) (SC_AT 0x224).
    bcs_branch ([] : list shent).
    { exfalso. rewrite branch_ltu_U in Hc.
      rewrite (bcs_U _ _ 32 _ HAG ltac:(lia) X32 ltac:(lia)), U_lit in Hc by lia.
      apply Z.ltb_lt in Hc. lia. }
    (* the set-up, then the loop from turn 0 *)
    rewrite branch_ltu_U in Hc.
    rewrite (bcs_U _ _ 32 _ HAG ltac:(lia) X32 ltac:(lia)), U_lit in Hc by lia.
    apply Z.ltb_ge in Hc.
    bcs_step ([] : list shent) (SC_AT 0x224).
    bcs_kr r2 [w64 (Z.of_nat (length bb))] kp_rel KR1. bcs_kr r2 [w64 (Z.of_nat (length bb))] kp_hd KR2.
    bcs_reg HS (12%bv : bv 5) (w64 (Z.of_nat 0)) Q12 ltac:(reflexivity).
    bcs_reg HS (13%bv : bv 5) (w64 (2 ^ 64 - 1 - body)) Q13
      ltac:(apply bcs_den_lit; exact (bcs_U_not _ _ 19 body HAG ltac:(lia) X19 ltac:(lia))).
    bcs_reg HS (20%bv : bv 5) (w64 (Z.of_nat (length bb) - 3)) Q20
      ltac:(rewrite (bcs_den _ _ 32 _ (-3) HAG ltac:(lia) X32 ltac:(lia)); f_equal; lia).
    bcs_reg HS (14%bv : bv 5) (w64 (body + 1)) Q14
      ltac:(rewrite (bcs_den _ _ 19 _ 1 HAG ltac:(lia) X19 ltac:(lia)); reflexivity).
    bcs_reg HS (15%bv : bv 5) (w64 1) Q15 ltac:(reflexivity).
    bcs_reg HS (16%bv : bv 5) (w64 240) Q16 ltac:(reflexivity).
    bcs_reg HS (17%bv : bv 5) (w64 19) Q17 ltac:(reflexivity).
    bcs_reg HS (5%bv : bv 5) (w64 112) Q5 ltac:(reflexivity).
    bcs_shape.
    apply (bcs_loop (length bb - 3 - 0) 0 _ _ eq_refl); [lia | intros j Hj; lia | | apply HJmat; exact HJ].
    unfold bcs_inv.
    split; [etransitivity; [apply KR2; bcs_kin | exact R19]|].
    split; [exact Q12|]. split; [exact Q13|]. split; [exact Q20|]. split; [exact Q14|]. split; [exact Q15|].
    split; [exact Q16|]. split; [exact Q17|]. split; [exact Q5|].
    split; [etransitivity; [apply KR2; bcs_kin | exact R25]|].
    exact (bcs_rel_kept regs r2 _ sp1 F HRL KR1).
Qed.

End scan.

(* ------------------------------------------------------------------ *)
(* The cut                                                             *)
(* ------------------------------------------------------------------ *)

Section x. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.

Lemma bc_scan : @bc_rel_stmt fx rc B MT -> @bc_scan_stmt fx rc B MT.
Proof.
  intros HRELS. unfold bc_scan_stmt.
  intros HLAWS STK sp0 FP lyx Sx W0 mem0 md0 own lyc Sc W memc mdc k regs body bb pos sp1 F W2 regs2 mem2 md2
    ly2 S2 HFIX HCUR HRS.
  pose proof HLAWS as (_ & LAWS & _).
  pose proof HFIX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Esp1 & _).
  pose proof HCUR as (HJ & Hperm & _ & _ & Hslot & _ & _ & HG & HSRC).
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & HSTK0 & Hlo & Hlosp & Hsphi & Hhi47 & _).
  pose proof asan_consts as (C1 & _).
  (* the body, when there are bytes: decode_rd_ok and its place at the cut's state *)
  assert (HRD : (0 < length bb)%nat -> decode_rd_ok W2 mem2 body (Z.of_nat (length bb)))
    by (intros HL; exact (trans_src_ok_rd B LAWS ly2 S2 W2 mem2 md2 body _ HAR (HSRC HL) ltac:(lia))).
  assert (HPL : (0 < length bb)%nat -> 4096 <= body /\ body + Z.of_nat (length bb) <= 140737488355327).
  { intros HL. destruct (HRD HL) as (_ & _ & _ & Ham & H0 & _).
    pose proof (trans_src_ok_place B LAWS ly2 S2 W2 mem2 md2 body _ HAR (HSRC HL) ltac:(lia)) as Hp.
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham. destruct Hp as [Hp|Hp]; lia. }
  assert (HRA : range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF body (Z.of_nat (length bb))).
  { destruct (Nat.eq_dec (length bb) 0) as [E0|E0]; [intros x Hx; lia|].
    exact (proj1 (proj2 (HRD ltac:(lia)))). }
  assert (HAPP : forall x, body <= x < body + Z.of_nat (length bb) ->
                   ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)).
  { intros x Hx. destruct (HRD ltac:(lia)) as (_ & _ & _ & Ham & _).
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham. unfold SHADOW_OFF. lia. }
  assert (HFF : TRANS_BC_FRAME = 160) by reflexivity.
  assert (Hsp1 : 0 <= sp1 <= 2 ^ 47).
  { rewrite HFF in Esp1. subst sp1.
    pose proof (Z.div_pos (spZ regs - 160) 32 ltac:(lia) ltac:(lia)).
    pose proof (Z.mul_div_le (spZ regs - 160) 32 ltac:(lia)). lia. }
  lazymatch type of HCUR with ?Jf md2 =>
  lazymatch goal with |- SRr _ _ _ ?Qg =>
    refine (bcs_head W2 mem2 regs body bb sp1 F Qg Jf _ _ (fun HL => proj1 (HPL HL)) (fun HL => proj2 (HPL HL))
              HRA HAPP HG Hslot Hsp1
              regs2 md2 HRS HCUR)
  end end.
  - intros md X HJx. destruct HJx as (HJ' & Hrest).
    split; [|exact Hrest].
    apply ajournal_materialize; first [assumption | exact transportb_segs_low | exact (@pa_segs_low _ transportb_listing PI_transportb)].
  - intros regs' md' HR H10 HJ'.
    exact (HRELS HLAWS STK sp0 FP lyx Sx W0 mem0 md0 own lyc Sc W memc mdc k regs body bb pos sp1 F W2 regs' mem2 md'
             ly2 S2 HFIX HJ' HR H10).
Qed.

End x.
