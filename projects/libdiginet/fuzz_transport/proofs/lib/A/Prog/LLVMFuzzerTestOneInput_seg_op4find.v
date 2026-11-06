(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 861 of its 1029 lines of code are new or changed and 971 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/diginet_session_close_seg_head.v, with its module paths and module names changed; 664 of its 745 lines of code are new or changed and 948 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_op4find: Lemma lc_op4find_ok : lc_op4find_stmt of
   lib/A/Prog/LLVMFuzzerTestOneInput_segs.v, one turn of op 4's find loop over g_q in fuzz_transport.asan's
   LLVMFuzzerTestOneInput: from the cut FIND(i) (+0xee0) to FIND(i + 1) (+0xee0) or WANT (+0x1164). No call.

   The code (offsets from the entry 0x81264):
     +0xee0 .. +0xf00   the shadow check of the 4 bytes at a0 = g_q + 4 i (its slow path +0xf48, report 0x82c84),
                        a1 = g_q[i] (`lwu 0(a6)`), a1 = t2 + 40 a1 + 4 (t2 = g_cmd);
     +0xf04 .. +0xf1c   the shadow check of the 4 bytes at a1 (slow path +0xf58, report 0x82c8c),
                        a1 = g_cmd[g_q[i]].key, s3 = a4 = i, `beq a1, a2` (a2 = key); +0xf20 s3 = a7 when they differ;
     +0xf24             `bgeu a5, a3` (a5 = i + 1, a3 = g_nq): the last entry ends the loop at +0xe8c;
     +0xf28 .. +0xf40   a5, a4 + 1, a0, a6 + 4, a7 = s3, `bltz` on s3 sign-extended: -1 (not found) is the head of
                        turn i + 1, an index (found) goes to +0xe8c;
     +0xe8c .. +0xea4   `beqz s4` (the sys flag): sys gives s6 = -10; else `bltz` on s3: an index gives s6 = 0;
     +0x114c .. +0x1160 not found: s6 = (g_nq = 512 ? -5 : 0), g_nq by a plain load through the spill slot 24(s1).

   The model (TOps.v submit_find_at): the cut says the search from 0 answers as the search from i. LoopOk.op_ok at the
   operation's start facts (lc_opok) gives LLVMFuzzerTestOneInput_op_m = Some, which through lc_op4_eq and
   lc_submit_tag_eq gives lc_at = Some at (fd_model_some); one step of the search at i (i < g_nq, i < CMDS_MAX) then
   says g_q[i] < CMDS_MAX and either at = i (the key matches) or the search from i + 1 answers at, whose own step gives
   i + 1 < CMDS_MAX when i + 1 < g_nq and at = -1 otherwise.

   How it is proved. Two seats of PaShadow.v's token engine over the G journal (TransportGRunA.v paj_run_x /
   paj_run_to_x), both with read-only regions only, s10 (atom 26) the shadow base:
     seat A at +0xee0: atom 32 = g_q[i] in a region at a6, the shadow entry [a0, a0 + 4) (g_q's zero shadow,
       trans_settle_cells); one run to +0xf04;
     seat B at +0xf04: atom 32 = the key in a region at a1, the spill slot 24(s1) (atom 33 = g_nq's page) and g_nq at
       that page + 944 (atom 13's low 4 bytes), the shadow entry [a1, a1 + 4) (g_cmd's zero shadow); runs to the
       branches, each branch split by the engine's own condition, to WANT or to FIND.
   Every run writes nothing, so the memory after it is the memory before (fd_frame_ro, functional_extensionality) and
   the cut's facts carry over unchanged; the journal is the run's own at the run's model, used through lc_core's first
   conjunct only, whatever its footprint list. The registers lc_tag_common reads are kept (FD_KEEP). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA settle_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TOps TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Agree QueueFacts LoopOk LinksProof SubmitTag.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LOK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.LoopOk.
Module LP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.LinksProof.
Module STg := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.SubmitTag.

(* the model *)
Lemma fd_find_step : forall f Bw key i,
  TOP.submit_find_at (S f) Bw key i =
    (if i <? TW.g_nq Bw then
       if TC.CMDS_MAX <=? i then None
       else if TC.CMDS_MAX <=? TW.Q_at Bw i then None
       else if TW.Cmd_key Bw (TW.Q_at Bw i) =? key then Some i
       else TOP.submit_find_at f Bw key (i + 1)
     else Some (-1)).
Proof. intros. reflexivity. Qed.

Lemma fd_key_range : forall D c, 0 <= sv_key (lc_sub_kd D c) < 2 ^ 32.
Proof.
intros D c. unfold lc_sub_kd.
destruct (TOP.fuzz_u8_m D c) as [c1 kb]. destruct (TOP.fuzz_u8_m D c1) as [c2 ab].
destruct (TOP.fuzz_u8_m D c2) as [c3 db]. cbn [sv_key]. unfold DSpec.KEY.
apply STg.lor_lt32.
- pose proof (Z.mod_pos_bound kb 9 ltac:(lia)). lia.
- change 0xffff with (Z.ones 16). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound ab (2 ^ 16) ltac:(lia)). lia.
Qed.

Lemma fd_model_some : forall cx op B1,
  lc_opok cx op -> lc_opc (l_pl cx) (lo_c op) = 4 -> TC.op_begin_m (lo_B op) = Some (B1, tt) -> TW.g_raw B1 = 0 ->
  tg_serial (lc_tag_vals (l_pl cx) B1 (sv_c (lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op))))) < TC.CMDS_MAX ->
  exists at_, lc_at (lc_tag_vals (l_pl cx) B1 (sv_c (lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op)))))
                 (sv_key (lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op)))) = Some at_.
Proof.
intros cx op B1 (HA & Hops & Hc & Hn & Hk) Hopc Hob Hraw Hser.
destruct (LOK.op_ok LP.links_holds timg_A (lo_ops op) (lo_B op) (fun _ => 1) (l_pl cx) (lo_c op) (lo_k op)
  HA Hops Hc Hn ltac:(lia) ltac:(lia)) as (B' & c' & k' & E & _).
rewrite (lc_op4_eq timg_A (lo_B op) (fun _ => 1) (l_pl cx) (lo_c op) (lo_k op) Hopc) in E.
destruct (TOP.op_submit_m (lo_B op) (l_pl cx) (lc_oc (l_pl cx) (lo_c op))) as [x|] eqn:ES; [|discriminate E].
clear E. rewrite (lc_submit_tag_eq (lo_B op) B1 (l_pl cx) (lc_oc (l_pl cx) (lo_c op)) Hob Hraw) in ES.
cbv zeta in ES.
destruct (TC.CMDS_MAX <=? _) eqn:EC in ES; [apply Z.leb_le in EC; lia|].
destruct (lc_at _ _) as [at_|] in ES |- *; [exists at_; reflexivity | discriminate ES].
Qed.

(* the symbolic machine *)
Lemma fd_frame_ro : forall E rs (m m' : word -> option byte),
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> frame_of E rs m m' -> forall x, m' x = m x.
Proof.
intros E rs m m' Hro HF x. apply HF. intros (r & Hin & Hr).
rewrite forallb_forall in Hro. specialize (Hro r Hin). apply Z.leb_le in Hro. lia.
Qed.

Lemma fd_addr : forall E a q, ew E 7 = Z_to_bv 64 a -> ew E 32 = Z_to_bv 64 q -> 0 <= a < 2 ^ 32 -> 0 <= q < 1024 ->
  sv_denot E (SAlu ALU_ADD (SOff 7 4) (SMd M_MUL (SOff 32 0) (SLit 40))) = Z_to_bv 64 (a + 4 + 40 * q).
Proof.
intros E a q H7 H32 Ha Hq. rewrite denot_lit_U. f_equal.
assert (U7 : U E (SOff 7 4) = a + 4)
  by (rewrite U_SOff, H7, unsigned_lit_small by lia; apply zcanon_id; unfold M64; lia).
assert (U32 : U E (SOff 32 0) = q) by (apply U_atom; [exact H32 | lia]).
assert (U40 : U E (SLit 40) = 40) by (apply U_lit; lia).
assert (UM : U E (SMd M_MUL (SOff 32 0) (SLit 40)) = 40 * q)
  by (rewrite U_SMd, U32, U40; cbn [zmd_raw]; rewrite zcanon_id by (unfold M64; lia); lia).
rewrite U_SAlu, U7, UM. cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma fd_swrap32 : forall g, 0 <= g < 2 ^ 32 -> bv_swrap 32 g = (g + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31.
Proof. intros g Hg. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. reflexivity. Qed.

(* +0x114c .. +0x1160: s6 = (lw g_nq) - 512 = 0 ? -1 & -5 : 0 *)
Lemma fd_space : forall E g, ew E 13 = Z_to_bv 64 g -> 0 <= g < 2 ^ 32 ->
  sv_denot E (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0)
      (SAlu ALU_ADD (SExt true 32 (SOff 13 0)) (SLit (-512)))) (SLit (-1))) (SLit (-5)))
  = Z_to_bv 64 (if g =? 512 then -5 else 0).
Proof.
intros E g H13 Hg.
assert (UX : U E (SAlu ALU_ADD (SExt true 32 (SOff 13 0)) (SLit (-512))) =
  ((g + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31 - 512) mod 2 ^ 64).
{ rewrite U_SAlu, U_SExt, U_SLit. rewrite (U_atom E 13 g H13) by lia. cbn [zalu_raw].
  change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small g (2 ^ 32)) by lia.
  rewrite fd_swrap32 by lia. unfold zcanon, M64. rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r. reflexivity. }
pose proof (Z.mod_pos_bound (g + 2 ^ 31) (2 ^ 32) ltac:(lia)) as M1.
pose proof (Z.div_mod (g + 2 ^ 31) (2 ^ 32) ltac:(lia)) as D1.
set (r1 := (g + 2 ^ 31) mod 2 ^ 32) in *. set (q1 := (g + 2 ^ 31) / 2 ^ 32) in *.
pose proof (Z.mod_pos_bound (r1 - 2 ^ 31 - 512) (2 ^ 64) ltac:(lia)) as M2.
pose proof (Z.div_mod (r1 - 2 ^ 31 - 512) (2 ^ 64) ltac:(lia)) as D2.
set (r2 := (r1 - 2 ^ 31 - 512) mod 2 ^ 64) in *. set (q2 := (r1 - 2 ^ 31 - 512) / 2 ^ 64) in *.
rewrite denot_lit_U.
rewrite U_SAlu, U_SAlu, U_SAlu, UX, !U_SLit. cbn [zalu_raw].
change (zcanon 0) with 0. change (zcanon (-1)) with (2 ^ 64 - 1). change (zcanon (-5)) with (2 ^ 64 - 5).
destruct (Z.eqb_spec g 512) as [Eg | Eg].
- assert (Er : r2 = 0) by lia. rewrite Er. apply bv_eq. vm_compute. reflexivity.
- assert (Er : 0 < r2) by lia. rewrite (proj2 (Z.ltb_lt 0 r2) Er). apply bv_eq. vm_compute. reflexivity.
Qed.

Lemma fd_br_lt : forall E a b, branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (Sg E a <? Sg E b).
Proof. intros E a b. cbn [branch_taken]. unfold bv_lts, Sg. reflexivity. Qed.

Lemma fd_sextw : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  Sg E (SAluw ALU_ADD (SOff n 0) (SLit 0)) = (v + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31.
Proof.
intros E n v Hn Hv. rewrite S_SAluw, U_SLit. rewrite (U_atom E n v Hn) by lia. cbn [zalu_raw].
change (zcanon 0 mod 2 ^ 32) with 0. rewrite Z.add_0_r. rewrite (Z.mod_small v (2 ^ 32)) by lia.
apply fd_swrap32. exact Hv.
Qed.

Lemma fd_sg0 : forall E, Sg E (SLit 0) = 0.
Proof. intros E. rewrite S_SLit. reflexivity. Qed.

Lemma fd_soffk : forall E n k v w, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> v + k = w ->
  sv_denot E (SOff n k) = Z_to_bv 64 w.
Proof. intros E n k v w H Hv Hw. cbn [sv_denot]. rewrite H, unsigned_lit_small by exact Hv. rewrite Hw. reflexivity. Qed.

Lemma fd_qat : forall Bw i, TW.Q_at Bw i = TW.u_at Bw (TW.OFF_g_q + 4 * i) 4.
Proof. reflexivity. Qed.
Lemma fd_kat : forall Bw s, TW.Cmd_key Bw s = TW.u_at Bw (TW.OFF_g_cmd + (40 * s + 4)) 4.
Proof. intros Bw s. unfold TW.Cmd_key, TW.A_Cmd_key. f_equal. ring. Qed.
Lemma fd_nqat : forall Bw, TW.g_nq Bw = TW.u_at Bw (TW.OFF_g_nq + 0) 4.
Proof. intros Bw. rewrite Z.add_0_r. reflexivity. Qed.

(* The two seats: at FIND (+0xee0), the turn's g_q[i] (atom 32) in a read-only region at a6 and the shadow entry of
   a0 = g_q + 4 i; at +0xf04 (a1 = g_cmd + 40 g_q[i] + 4 computed), the key g_cmd[g_q[i]].key (atom 32) at a1, the
   spill slot 24(s1) (g_nq's page, atom 33) and g_nq at that page + 944, and the shadow entry of a1. s10 (atom 26)
   is the shadow base. *)
Definition FD_Bx : sv := SOff 26 0.
Definition FD_O_KEY : Z := 0xf04.
Definition fd_q_reg : YP09.region := YP09.mkRegion (Some 16%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))].
Definition fd_facts_a : facts :=
  mkFacts [(10%nat, mkAF TA_g_q (TA_g_q + 4092) 0); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF 0 1023 0)] [] [].
Definition fd_ss_a : sstate := mkSS LO_FIND sr_atoms [fd_q_reg] None fd_facts_a.
Definition FD_SH_A : list shent := [mkSHE 10 0 4].
Definition fd_key_reg : YP09.region := YP09.mkRegion (Some 11%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))].
Definition fd_spill_reg : YP09.region := YP09.mkRegion (Some 9%nat) 24 32 0 0 [YP09.mkChunk 24 (CVal 8 (SOff 33 0))].
Definition fd_nq_reg : YP09.region := YP09.mkRegion (Some 33%nat) 944 948 0 0 [YP09.mkChunk 944 (CVal 4 (SOff 13 0))].
Definition fd_facts_b : facts :=
  mkFacts [(11%nat, mkAF (TA_g_cmd + 4) (TA_g_cmd + 40 * 1023 + 4) 0); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition fd_ss_b : sstate := mkSS FD_O_KEY sr_atoms [fd_key_reg; fd_spill_reg; fd_nq_reg] None fd_facts_b.
Definition FD_SH_B : list shent := [mkSHE 11 0 4].
Definition fd_EA {rc : YM05.RunCeil} (regs : bvmap 5 word) (q : Z) : env :=
  Eimg (PI := PI_transport) (Ereg regs [w64 q]).
Definition fd_EB {rc : YM05.RunCeil} (regs : bvmap 5 word) (k : Z) : env :=
  Eimg (PI := PI_transport) (Ereg regs [w64 k; w64 (transport_hi 14)]).

Section fd. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.

(* The registers this stretch keeps: FD_KEEP (what lc_tag_common reads), FD_KA (all but a1 and t0, from FIND to
   +0xf04), FD_KW (to WANT), FD_KF (back to FIND). *)
Definition FD_KEEP : list (bv 5) := [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv].
Definition FD_KA : list (bv 5) :=
  FD_KEEP ++ [7%bv; 10%bv; 12%bv; 13%bv; 14%bv; 15%bv; 16%bv; 17%bv; 19%bv; 20%bv; 22%bv].
Definition FD_KW : list (bv 5) := FD_KEEP ++ [20%bv].
Definition FD_KF : list (bv 5) := FD_KEEP ++ [7%bv; 12%bv; 13%bv; 17%bv; 20%bv].

Ltac fd_in := cbn [In FD_KEEP FD_KA FD_KW FD_KF app]; repeat (first [left; reflexivity | right]).

Lemma fd_core_regs : forall cx ly' S' (W' : world segs) regs regs2 mem md e,
  @lc_core rc B cx ly' S' W' regs mem md e ->
  (forall r, In r FD_KEEP -> YK11.getr regs2 r = YK11.getr regs r) ->
  @lc_core rc B cx ly' S' W' regs2 mem md e.
Proof.
intros cx ly' S' W' regs regs2 mem md e HC KR.
destruct HC as (HJ & Hfr & HlyF & HP & R2 & R8 & R9 & R3 & R4 & Hrest).
split; [exact HJ|]. split; [exact Hfr|]. split; [exact HlyF|]. split; [exact HP|].
split; [etransitivity; [apply KR; unfold FD_KEEP; fd_in | exact R2]|].
split; [etransitivity; [apply KR; unfold FD_KEEP; fd_in | exact R8]|].
split; [etransitivity; [apply KR; unfold FD_KEEP; fd_in | exact R9]|].
split; [etransitivity; [apply KR; unfold FD_KEEP; fd_in | exact R3]|].
split; [etransitivity; [apply KR; unfold FD_KEEP; fd_in | exact R4]|].
exact Hrest.
Qed.

Lemma fd_tag_kept : forall cx op B1 ly' S' (W' : world segs) regs regs2 mem md md2 e,
  @lc_tag_common rc B MT cx op B1 ly' S' W' regs mem md e ->
  @lc_core rc B cx ly' S' W' regs mem md2 e ->
  (forall r, In r FD_KEEP -> YK11.getr regs2 r = YK11.getr regs r) ->
  @lc_tag_common rc B MT cx op B1 ly' S' W' regs2 mem md2 e.
Proof.
intros cx op B1 ly' S' W' regs regs2 mem md md2 e HT HC2 KR.
unfold lc_tag_common in HT |- *. cbv zeta in HT |- *.
destruct HT as (Hopc & HL & Hob & Hraw & Hser & Htw & Hcb & H144 & H56 & H64 & H72 & R24 & R25 & R27 & R23).
destruct HL as (HC & (R18 & R26) & Hsp & Hfsh & Hok & He & Hmt & R21).
split; [exact Hopc|].
split.
{ split; [exact (fd_core_regs cx ly' S' W' regs regs2 mem md2 e HC2 KR)|].
  split; [split; (etransitivity; [apply KR; unfold FD_KEEP; fd_in | assumption])|].
  split; [exact Hsp|]. split; [exact Hfsh|]. split; [exact Hok|]. split; [exact He|]. split; [exact Hmt|].
  etransitivity; [apply KR; unfold FD_KEEP; fd_in | exact R21]. }
split; [exact Hob|]. split; [exact Hraw|]. split; [exact Hser|]. split; [exact Htw|]. split; [exact Hcb|].
split; [exact H144|]. split; [exact H56|]. split; [exact H64|]. split; [exact H72|].
split; [etransitivity; [apply KR; unfold FD_KEEP; fd_in | exact R24]|].
split; [etransitivity; [apply KR; unfold FD_KEEP; fd_in | exact R25]|].
split; [etransitivity; [apply KR; unfold FD_KEEP; fd_in | exact R27]|].
etransitivity; [apply KR; unfold FD_KEEP; fd_in | exact R23].
Qed.

(* WANT and FIND (i + 1) from a read-only stretch: the memory as before, the journal at the stretch's model, the
   registers of FD_KEEP as before, and the cut's own registers. *)
Lemma fd_want_close : forall cx op B1 ly' S' (W' : world segs) regs regs2 mem md md2 e at_,
  @lc_tag_common rc B MT cx op B1 ly' S' W' regs mem md e ->
  @lc_core rc B cx ly' S' W' regs mem md2 e ->
  (forall r, In r FD_KEEP -> YK11.getr regs2 r = YK11.getr regs r) ->
  let D := l_pl cx in
  let kd := lc_sub_kd D (lc_oc D (lo_c op)) in
  let tv := lc_tag_vals D B1 (sv_c kd) in
  lc_at tv (sv_key kd) = Some at_ ->
  YK11.getr regs2 22 = w64 (lc_want tv at_) -> YK11.getr regs2 19 = w64 (at_ mod 2 ^ 32) ->
  YK11.getr regs2 20 = w64 (if lc_sys tv then 1 else 0) ->
  @lc_st_want rc B MT cx op W' (lc_cfg cx LO_WANT regs2 mem md2).
Proof.
intros cx op B1 ly' S' W' regs regs2 mem md md2 e at_ HT HC2 KR D kd tv HAt R22 R19 R20.
unfold lc_st_want. exists ly', S', regs2, mem, md2, e, B1, at_. cbv zeta.
split; [reflexivity|].
split; [exact (fd_tag_kept cx op B1 ly' S' W' regs regs2 mem md md2 e HT HC2 KR)|].
split; [exact HAt|]. split; [exact R22|]. split; [exact R19 | exact R20].
Qed.

Lemma fd_find_close : forall cx op B1 ly' S' (W' : world segs) regs regs2 mem md md2 e i,
  @lc_tag_common rc B MT cx op B1 ly' S' W' regs mem md e ->
  @lc_core rc B cx ly' S' W' regs mem md2 e ->
  (forall r, In r FD_KEEP -> YK11.getr regs2 r = YK11.getr regs r) ->
  let D := l_pl cx in
  let kd := lc_sub_kd D (lc_oc D (lo_c op)) in
  let tv := lc_tag_vals D B1 (sv_c kd) in
  TC.h_coalescable_m (sv_key kd) <> 0 ->
  0 <= i < TW.g_nq (tg_B2 tv) -> i < TC.CMDS_MAX ->
  TOP.submit_find_at (S (Z.to_nat TC.CMDS_MAX)) (tg_B2 tv) (sv_key kd) 0 =
    TOP.submit_find_at (S (Z.to_nat TC.CMDS_MAX) - Z.to_nat i) (tg_B2 tv) (sv_key kd) i ->
  YK11.getr regs2 10 = w64 (TA_g_q + 4 * i) -> YK11.getr regs2 16 = w64 (TA_g_q + 4 * i) ->
  YK11.getr regs2 14 = w64 i -> YK11.getr regs2 15 = w64 (i + 1) ->
  YK11.getr regs2 13 = w64 (TW.g_nq (tg_B2 tv)) -> YK11.getr regs2 17 = w64 (2 ^ 32 - 1) ->
  YK11.getr regs2 12 = w64 (sv_key kd) -> YK11.getr regs2 7 = w64 TA_g_cmd ->
  YK11.getr regs2 20 = w64 (if lc_sys tv then 1 else 0) ->
  @lc_st_find rc B MT cx op i W' (lc_cfg cx LO_FIND regs2 mem md2).
Proof.
intros cx op B1 ly' S' W' regs regs2 mem md md2 e i HT HC2 KR D kd tv Hco Hi HiC Hfa
  R10 R16 R14 R15 R13 R17 R12 R7 R20.
unfold lc_st_find. exists ly', S', regs2, mem, md2, e, B1. cbv zeta.
split; [reflexivity|].
split; [exact (fd_tag_kept cx op B1 ly' S' W' regs regs2 mem md md2 e HT HC2 KR)|].
repeat (split; [eassumption|]). exact R20.
Qed.

Section fx. Context {fx : YK11.FPState}.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma fd_entry_a : forall ly S (W : world segs) regs mem md i Bw,
  decode_zshadow_at B TA_g_q (TA_g_q + TW.SZ_g_q) -> @AR rc segs B ly S W mem md ->
  YK11.getr regs 10 = w64 (TA_g_q + 4 * i) -> YK11.getr regs 16 = w64 (TA_g_q + 4 * i) ->
  YK11.getr regs 26 = w64 SHADOW_OFF -> 0 <= i < 1024 -> 0 <= TW.Q_at Bw i < 1024 ->
  tw_at TMAP_A (aview segs (w_H W) mem) Bw ->
  st_ok_pi segs VAL (fd_EA regs (TW.Q_at Bw i)) fd_ss_a
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + LO_FIND)) mem (YK11.seg_rom segs))) /\
  sh_ok segs FD_Bx FD_SH_A (fd_EA regs (TW.Q_at Bw i)) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md i Bw HZ HAR R10 R16 R26 Hi Hq Htw.
set (E := fd_EA regs (TW.Q_at Bw i)).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, fd_EA; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = w64 (TW.Q_at Bw i))
  by (unfold E, fd_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
pose proof (EE 10%nat 10%bv eq_refl) as E10. rewrite R10 in E10.
pose proof (EE 16%nat 16%bv eq_refl) as E16. rewrite R16 in E16.
pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite R26 in E26.
assert (EC : TA_g_q = 6233088) by reflexivity.
assert (U10 : bv_unsigned (ew E 10) = TA_g_q + 4 * i) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U16 : bv_unsigned (ew E 16) = TA_g_q + 4 * i) by (rewrite E16; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF)
  by (rewrite E26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = TW.Q_at Bw i) by (rewrite E32; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold fd_ss_a.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil].
    unfold fd_q_reg, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U16. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ (TA_g_q + 4 * i) 0 4 (SOff 32 0) (TW.Q_at Bw i)).
    * cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * cbn. lia.
    * lia.
    * rewrite Z.add_0_r, fd_qat.
      exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_q TA_g_q TW.SZ_g_q (4 * i) 4 TMAP_A_ok Htw TMAP_A_g_q
        ltac:(lia) ltac:(unfold TW.SZ_g_q; lia)).
  + cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  + unfold fd_facts_a, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U10, U26, U32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
- unfold sh_ok, FD_SH_A. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem E FD_Bx 10 (TA_g_q + 4 * i) 4 (TA_g_q + 4 * i) 0 4).
  + exact (proj1 (decode_zshadow_ra B ly S W mem md TA_g_q (TA_g_q + TW.SZ_g_q) (TA_g_q + 4 * i) 4 HAR HZ
      ltac:(lia) ltac:(rewrite EC; lia) ltac:(rewrite EC; unfold TW.SZ_g_q; lia))).
  + unfold U, FD_Bx. cbn [sv_denot]. rewrite E26, Z.add_0_r, Z_to_bv_bv_unsigned.
    apply unsigned_lit_small. unfold SHADOW_OFF. lia.
  + apply U_atom; [exact E10 | lia].
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

Lemma fd_entry_b : forall ly S (W : world segs) regs mem md q sp1 Bw,
  decode_zshadow_at B TA_g_cmd (TA_g_cmd + TW.SZ_g_cmd) -> @AR rc segs B ly S W mem md ->
  YK11.getr regs 11 = w64 (TA_g_cmd + 4 + 40 * q) -> YK11.getr regs 9 = w64 sp1 ->
  YK11.getr regs 13 = w64 (TW.g_nq Bw) -> YK11.getr regs 26 = w64 SHADOW_OFF -> 0 <= q < 1024 ->
  2 ^ 40 <= sp1 <= 2 ^ 47 ->
  rdword (aview segs (w_H W) mem) (sp1 + 24) = Some (transport_hi 14) ->
  tw_at TMAP_A (aview segs (w_H W) mem) Bw ->
  st_ok_pi segs VAL (fd_EB regs (TW.Cmd_key Bw q)) fd_ss_b
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + FD_O_KEY)) mem (YK11.seg_rom segs))) /\
  sh_ok segs FD_Bx FD_SH_B (fd_EB regs (TW.Cmd_key Bw q)) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md q sp1 Bw HZ HAR R11 R9 R13 R26 Hq Hsp Hsl Htw.
set (E := fd_EB regs (TW.Cmd_key Bw q)).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, fd_EB; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = w64 (TW.Cmd_key Bw q))
  by (unfold E, fd_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 (transport_hi 14))
  by (unfold E, fd_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
pose proof (EE 11%nat 11%bv eq_refl) as E11. rewrite R11 in E11.
pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite R9 in E9.
pose proof (EE 13%nat 13%bv eq_refl) as E13. rewrite R13 in E13.
pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite R26 in E26.
assert (EC : TA_g_cmd = 6181888) by reflexivity.
assert (EH : transport_hi 14 = 6157744) by reflexivity.
assert (EN : TA_g_nq = 6158688) by reflexivity.
assert (Rk : 0 <= TW.Cmd_key Bw q < 2 ^ 32)
  by (pose proof (TWL.u_at_range Bw (TW.A_Cmd_key q) 4) as R; exact R).
assert (Rn : 0 <= TW.g_nq Bw < 2 ^ 32) by (pose proof (TWL.u_at_range Bw TW.OFF_g_nq 4) as R; exact R).
assert (U11 : bv_unsigned (ew E 11) = TA_g_cmd + 4 + 40 * q) by (rewrite E11; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF)
  by (rewrite E26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = TW.Cmd_key Bw q) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = transport_hi 14) by (rewrite E33; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold fd_ss_b.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    * unfold fd_key_reg, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U11. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ (TA_g_cmd + 4 + 40 * q) 0 4 (SOff 32 0) (TW.Cmd_key Bw q)).
      -- cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      -- cbn. lia.
      -- lia.
      -- rewrite fd_kat. replace (TA_g_cmd + 4 + 40 * q + 0) with (TA_g_cmd + (40 * q + 4)) by lia.
         exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_cmd TA_g_cmd TW.SZ_g_cmd (40 * q + 4) 4 TMAP_A_ok Htw
           TMAP_A_g_cmd ltac:(lia) ltac:(unfold TW.SZ_g_cmd; lia)).
    * unfold fd_spill_reg, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ sp1 24 8 (SOff 33 0) (transport_hi 14)).
      -- cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      -- rewrite EH. cbn. lia.
      -- lia.
      -- exact (val_mem_of_rdword segs (w_H W) mem _ _ Hsl).
    * unfold fd_nq_reg, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U33, EH. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ 6157744 944 4 (SOff 13 0) (TW.g_nq Bw)).
      -- cbn [sv_denot]. rewrite E13, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      -- cbn. lia.
      -- lia.
      -- rewrite fd_nqat. replace (6157744 + 944) with (TA_g_nq + 0) by (rewrite EN; reflexivity).
         exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_nq TA_g_nq TW.SZ_g_nq 0 4 TMAP_A_ok Htw
           TMAP_A_g_nq ltac:(lia) ltac:(unfold TW.SZ_g_nq; lia)).
  + apply pairwise_disjoint_of_extents.
    unfold fd_key_reg, fd_spill_reg, fd_nq_reg, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U11, U9, U33, EH.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  + unfold fd_facts_b, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U11, U26, U32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
- unfold sh_ok, FD_SH_B. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem E FD_Bx 11 (TA_g_cmd + 4 + 40 * q) 4 (TA_g_cmd + 4 + 40 * q) 0 4).
  + exact (proj1 (decode_zshadow_ra B ly S W mem md TA_g_cmd (TA_g_cmd + TW.SZ_g_cmd) (TA_g_cmd + 4 + 40 * q) 4
      HAR HZ ltac:(lia) ltac:(rewrite EC; lia) ltac:(rewrite EC; unfold TW.SZ_g_cmd; lia))).
  + unfold U, FD_Bx. cbn [sv_denot]. rewrite E26, Z.add_0_r, Z_to_bv_bv_unsigned.
    apply unsigned_lit_small. unfold SHADOW_OFF. lia.
  + apply U_atom; [exact E11 | lia].
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

End fx.

Lemma fd_pc : forall k, Z_to_bv 64 (@pa_val _ transport_listing PI_transport A_TEXT + k) = w64 (transport_text + k).
Proof. intros k. reflexivity. Qed.

(* the write rights of a run whose regions are all read-only *)
Ltac fd_awr_ro :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

(* the model after a run, named *)
Ltac fd_md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    let md := fresh "mdw" in set (md := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md; clear mt end.

(* after a read-only run: its memory is its start memory, and the machine state is put in mkst form *)
Ltac fd_norm HS HJ SHOK :=
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m1) =>
  lazymatch goal with HF : frame_of _ ?rs ?m0 (ms_mem m1) |- _ =>
    let KM := fresh "KM" in let MM := fresh "MM" in let Ems := fresh "Ems" in
    assert (KM : forall x, ms_mem m1 x = m0 x)
      by (exact (fd_frame_ro _ rs _ _ ltac:(vm_compute; reflexivity) HF));
    assert (MM : ms_mem m1 = m0) by (apply functional_extensionality; exact KM);
    pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as Ems; cbn [ss_pc] in Ems;
    rewrite Ems in HS; rewrite Ems; clear Ems KM;
    rewrite MM in HS, HJ |- *; try rewrite MM in SHOK; clear MM
  end end;
  lazymatch goal with HF : frame_of _ _ _ _, HFr : frame_of _ _ _ _, HG : mem_grows _ _ |- _ => clear HF HFr HG end.

(* the low atoms of the current valuation are those of E0 *)
Ltac fd_low HS E0 HEX :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (HEX : forall n, (n < 1024)%nat -> ew Ex n = ew E0 n)
      by (let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn;
          repeat rewrite ew_ewset_other by lia; reflexivity)
  end.

(* getr of HS's machine state at a register, as the denotation of its computed symbolic value *)
Ltac fd_rv HS :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
    refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx _ HS) _);
    lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end
  end.

(* lc_sys of the goal's tv rewritten by Hsys (stated at the set name tv) *)
Ltac fd_sys Hsys :=
  lazymatch type of Hsys with _ = ?b =>
  lazymatch goal with |- context [lc_sys ?t] =>
    let E := fresh "Esys" in assert (E : lc_sys t = b) by exact Hsys; rewrite E; clear E end end.

(* s6 at WANT: -10 (sys), 0 (at >= 0), or the space test of g_nq (+0x114c .. +0x1160, at = -1) *)
Ltac fd_want_s6 HEX Hsys i Hi nq :=
  first
  [ lazymatch goal with |- sv_denot _ (SLit _) = _ => idtac end;
    cbn [sv_denot]; unfold lc_want; fd_sys Hsys; cbv beta iota;
    try rewrite (proj2 (Z.ltb_ge i 0) (proj1 Hi)); cbn [andb];
    apply bv_eq; vm_compute; reflexivity
  | rewrite (fd_space _ nq) by (first [rewrite HEX by lia; assumption | lia]);
    unfold lc_want; fd_sys Hsys; cbv beta iota; change (-1 <? 0) with true; cbn [andb];
    reflexivity ].

(* the agreement of the current valuation with the seat's registers below 32 *)
Ltac fd_hae HEX HAE rg1 kq Ex :=
  assert (HAE : env_agree 32 (Ereg rg1 [w64 kq; w64 (transport_hi 14)]) Ex)
    by (split; [let nn := fresh "nn" in let Hnn := fresh "Hnn" in
                intros nn Hnn; rewrite (HEX nn) by lia; apply Eimg_low; unfold A_TEXT; lia
               | reflexivity]).

(* the cut WANT at the end of a run *)
Ltac fd_want_leaf HS HEX HT HJ HC KR0 KRA HAt EB14 EB17 R20 Hsys i Hi rg1 kq nq :=
  lazymatch goal with |- SRr _ _ (mkCfg (?mk ?rgF ?pcx ?mm ?rom) ?mdF) _ =>
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msr =>
  lazymatch type of HT with @lc_tag_common _ _ _ ?cx ?op ?B1 ?ly ?S ?W ?rg ?mem ?md ?e =>
    let HAE := fresh "HAE" in let KRB := fresh "KRB" in
    fd_hae HEX HAE rg1 kq Ex;
    assert (KRB : forall r, In r FD_KW -> YK11.getr rgF r = YK11.getr rg1 r)
      by (exact (regs_kept_of_st_ok_pi Ex ssx msr rg1 _ FD_KW HS HAE ltac:(vm_compute; reflexivity)));
    apply SRr_ret; right; rewrite fd_pc;
    eapply (fd_want_close cx op B1 ly S W rg rgF mem md mdF e _ HT (conj HJ (proj2 HC))
      (KR0 rgF (fun r Hr => KRB r (in_or_app _ _ _ (or_introl Hr)))));
    [ exact HAt
    | fd_rv HS; fd_want_s6 HEX Hsys i Hi nq
    | fd_rv HS;
      first [ apply (fd_soffk _ _ _ i); [rewrite HEX by lia; exact EB14 | lia | rewrite Z.mod_small by lia; lia]
            | apply (fd_soffk _ _ _ (2 ^ 32 - 1)); [rewrite HEX by lia; exact EB17 | lia | reflexivity] ]
    | rewrite KRB by fd_in; rewrite KRA by fd_in; exact R20 ]
  end end end.

(* the cut FIND at turn i + 1 at the end of a run *)
Ltac fd_find_leaf HS HEX HT HJ HC KR0 KRA Hco Hlt EC1 Hfa1 EB10 EB14 EB15 EB16 R7 R12 R13 R17 R20 i rg1 kq :=
  lazymatch goal with |- SRr _ _ (mkCfg (?mk ?rgF ?pcx ?mm ?rom) ?mdF) _ =>
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msr =>
  lazymatch type of HT with @lc_tag_common _ _ _ ?cx ?op ?B1 ?ly ?S ?W ?rg ?mem ?md ?e =>
    let HAE := fresh "HAE" in let KRB := fresh "KRB" in
    fd_hae HEX HAE rg1 kq Ex;
    assert (KRB : forall r, In r FD_KF -> YK11.getr rgF r = YK11.getr rg1 r)
      by (exact (regs_kept_of_st_ok_pi Ex ssx msr rg1 _ FD_KF HS HAE ltac:(vm_compute; reflexivity)));
    apply SRr_ret; left; rewrite fd_pc;
    eapply (fd_find_close cx op B1 ly S W rg rgF mem md mdF e (i + 1) HT (conj HJ (proj2 HC))
      (KR0 rgF (fun r Hr => KRB r (in_or_app _ _ _ (or_introl Hr)))));
    [ exact Hco | split; [lia | exact Hlt] | exact EC1 | exact Hfa1
    | fd_rv HS; apply (fd_soffk _ _ _ (TA_g_q + 4 * i)); [rewrite HEX by lia; exact EB10 | unfold TA_g_q; lia | lia]
    | fd_rv HS; apply (fd_soffk _ _ _ (TA_g_q + 4 * i)); [rewrite HEX by lia; exact EB16 | unfold TA_g_q; lia | lia]
    | fd_rv HS; apply (fd_soffk _ _ _ i); [rewrite HEX by lia; exact EB14 | lia | lia]
    | fd_rv HS; apply (fd_soffk _ _ _ (i + 1)); [rewrite HEX by lia; exact EB15 | lia | lia]
    | rewrite KRB by fd_in; rewrite KRA by fd_in; exact R13
    | rewrite KRB by fd_in; rewrite KRA by fd_in; exact R17
    | rewrite KRB by fd_in; rewrite KRA by fd_in; exact R12
    | rewrite KRB by fd_in; rewrite KRA by fd_in; exact R7
    | rewrite KRB by fd_in; rewrite KRA by fd_in; exact R20 ]
  end end end.

Lemma lc_op4find_ok : lc_op4find_stmt B MT XL RLO RHI.
Proof.
unfold lc_op4find_stmt.
intros HP cx op i W' c' HB HF.
destruct HF as (ly' & S' & regs & mem & md & e & B1 & HF). cbv zeta in HF.
destruct HF as (-> & HT & Hco & Hi & HiC & Hfa & R10 & R16 & R14 & R15 & R13 & R17 & R12 & R7 & R20).
pose proof HT as HT0. unfold lc_tag_common in HT0. cbv zeta in HT0.
destruct HT0 as (Hopc & HL & Hob & Hraw & Hser & Htw & _ & _ & _ & _ & _ & _ & _ & _ & _).
destruct HL as (HC & (R18 & R26) & Hsp & _ & Hok & _ & _ & _).
(* the model's Some *)
destruct (fd_model_some cx op B1 Hok Hopc Hob Hraw (proj2 Hser)) as (at_ & HAt).
set (D := l_pl cx) in *.
set (kd := lc_sub_kd D (lc_oc D (lo_c op))) in *.
set (tv := lc_tag_vals D B1 (sv_c kd)) in *.
set (Bw := tg_B2 tv) in *.
set (key := sv_key kd) in *.
assert (HF0 : TOP.submit_find_at (S (Z.to_nat TC.CMDS_MAX)) Bw key 0 = Some at_).
{ unfold lc_at in HAt. destruct (TC.h_coalescable_m key =? 0) eqn:Ec in HAt;
    [apply Z.eqb_eq in Ec; contradiction | exact HAt]. }
rewrite Hfa in HF0.
assert (Hf : (S (Z.to_nat TC.CMDS_MAX) - Z.to_nat i = S (Z.to_nat TC.CMDS_MAX - Z.to_nat i))%nat)
  by (unfold TC.CMDS_MAX in *; lia).
rewrite Hf in HF0. clear Hf.
rewrite fd_find_step in HF0.
rewrite (proj2 (Z.ltb_lt i (TW.g_nq Bw)) (proj2 Hi)), (proj2 (Z.leb_gt TC.CMDS_MAX i) HiC) in HF0.
destruct (TC.CMDS_MAX <=? TW.Q_at Bw i) eqn:EQ; [discriminate HF0|]. apply Z.leb_gt in EQ.
set (q := TW.Q_at Bw i) in *.
set (f := (Z.to_nat TC.CMDS_MAX - Z.to_nat i)%nat) in *.
assert (Hi1024 : 0 <= i < 1024) by (unfold TC.CMDS_MAX in HiC; lia).
assert (Hq1024 : 0 <= q < 1024)
  by (pose proof (TWL.u_at_range Bw (TW.OFF_g_q + 4 * i) 4) as Rq; unfold TC.CMDS_MAX in EQ;
      change (TW.u_at Bw (TW.OFF_g_q + 4 * i) 4) with q in Rq; lia).
assert (Rkey : 0 <= key < 2 ^ 32) by apply fd_key_range.
assert (Rnq : 0 <= TW.g_nq Bw < 2 ^ 32) by (pose proof (TWL.u_at_range Bw TW.OFF_g_nq 4) as R; exact R).
assert (Rkq : 0 <= TW.Cmd_key Bw q < 2 ^ 32) by (pose proof (TWL.u_at_range Bw (TW.A_Cmd_key q) 4) as R; exact R).
(* the kit *)
pose proof (lp_laws B MT XL RLO RHI HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned B MT XL RLO RHI HP)) as HGX.
pose proof (lp_settle_cells B MT XL RLO RHI HP) as (_ & _ & HZq & HZc).
destruct (lc_geom B MT XL RLO RHI cx ly' S' W' regs mem md e HB HC) as [HAR _ Hstk Hsp1c _ _ _ _ _].
pose proof HC as (HJ & _ & _ & _ & _ & _ & R9 & R3 & R4 & Hsp1r & _).
(* the seat at FIND *)
destruct (fd_entry_a (fx := l_fx cx) ly' S' W' regs mem md i Bw HZq HAR R10 R16 R26 Hi1024 Hq1024 Htw)
  as (HS & SHOK).
change (fd_EA regs (TW.Q_at Bw i)) with (fd_EA regs q) in HS, SHOK.
set (EA := fd_EA regs q) in HS, SHOK.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (HEI : img_env (@pa_val _ transport_listing PI_transport) A_LIM Ex) by (unfold EA, fd_EA; apply Eimg_env) end.
pose proof (@paj_run_x (l_fx cx) rc AE2k.tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUN.
pose proof (@paj_run_to_x (l_fx cx) rc AE2k.tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := l_fx cx) (PI := PI_transport)) as BR.
unfold lc_cfg. rewrite <- fd_pc.
(* +0xee0 .. +0xf00: the check of g_q[i]'s shadow (a0's 4 bytes), a1 = g_q[i], a1 = g_cmd + 40 a1 + 4 *)
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan FD_O_KEY.
{ fd_awr_ro. }
fd_md. fd_norm HS HJ SHOK. fd_low HS EA HEXA.
set (rg1 := ms_regs ms) in *.
assert (EAr : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew EA n = YK11.getr regs r)
  by (intros n r Hn; unfold EA, fd_EA; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EA32 : ew EA 32 = w64 q)
  by (unfold EA, fd_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (KRA : forall r, In r FD_KA -> YK11.getr rg1 r = YK11.getr regs r).
{ lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msr =>
    assert (HAE : env_agree 32 (Ereg regs [w64 q]) Ex)
      by (split; [intros nn Hnn; rewrite (HEXA nn) by lia; unfold EA, fd_EA; apply Eimg_low; unfold A_TEXT; lia
                 | reflexivity]);
    exact (regs_kept_of_st_ok_pi Ex ssx msr regs [w64 q] FD_KA HS HAE ltac:(vm_compute; reflexivity)) end. }
assert (A11 : YK11.getr rg1 11 = w64 (TA_g_cmd + 4 + 40 * q)).
{ fd_rv HS. apply fd_addr;
    [rewrite HEXA by lia; rewrite (EAr 7%nat 7%bv eq_refl); exact R7 | rewrite HEXA by lia; exact EA32
    | unfold TA_g_cmd; lia | lia]. }
assert (A9 : YK11.getr rg1 9 = w64 (lc_sp1 cx)) by (rewrite KRA by fd_in; exact R9).
assert (A13 : YK11.getr rg1 13 = w64 (TW.g_nq Bw)) by (rewrite KRA by fd_in; exact R13).
assert (A26 : YK11.getr rg1 26 = w64 SHADOW_OFF) by (rewrite KRA by fd_in; exact R26).
(* the seat at +0xf04 *)
assert (Hsl : rdword (aview segs (w_H W') mem) (lc_sp1 cx + 24) = Some (transport_hi 14)).
{ unfold lc_spills in Hsp. rewrite Forall_forall in Hsp. apply (Hsp (24, transport_hi 14)).
  unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm. cbn [app]. fd_in. }
assert (Hsp1b : 2 ^ 40 <= lc_sp1 cx <= 2 ^ 47).
{ pose proof YM05.alloc_ceiling_value as Hac. destruct Hstk as (_ & _ & H0 & H47). unfold LF_FRAME in Hsp1r. lia. }
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARw.
destruct (fd_entry_b (fx := l_fx cx) ly' S' W' rg1 mem mdw q (lc_sp1 cx) Bw HZc HARw A11 A9 A13 A26 Hq1024 Hsp1b
  Hsl Htw) as (HSb & SHOKb).
clear HS SHOK HEI HEXA. rename HSb into HS, SHOKb into SHOK. unfold FD_O_KEY in HS.
set (EB := fd_EB rg1 (TW.Cmd_key Bw q)) in HS, SHOK.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (HEI : img_env (@pa_val _ transport_listing PI_transport) A_LIM Ex) by (unfold EB, fd_EB; apply Eimg_env) end.
assert (EBr : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew EB n = YK11.getr rg1 r)
  by (intros n r Hn; unfold EB, fd_EB; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EB32 : ew EB 32 = w64 (TW.Cmd_key Bw q))
  by (unfold EB, fd_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rg1 _ 0)).
assert (EB7 : ew EB 7 = w64 TA_g_cmd) by (rewrite (EBr 7%nat 7%bv eq_refl), KRA by fd_in; exact R7).
assert (EB10 : ew EB 10 = w64 (TA_g_q + 4 * i)) by (rewrite (EBr 10%nat 10%bv eq_refl), KRA by fd_in; exact R10).
assert (EB12 : ew EB 12 = w64 key) by (rewrite (EBr 12%nat 12%bv eq_refl), KRA by fd_in; exact R12).
assert (EB13 : ew EB 13 = w64 (TW.g_nq Bw)) by (rewrite (EBr 13%nat 13%bv eq_refl), KRA by fd_in; exact R13).
assert (EB14 : ew EB 14 = w64 i) by (rewrite (EBr 14%nat 14%bv eq_refl), KRA by fd_in; exact R14).
assert (EB15 : ew EB 15 = w64 (i + 1)) by (rewrite (EBr 15%nat 15%bv eq_refl), KRA by fd_in; exact R15).
assert (EB16 : ew EB 16 = w64 (TA_g_q + 4 * i)) by (rewrite (EBr 16%nat 16%bv eq_refl), KRA by fd_in; exact R16).
assert (EB17 : ew EB 17 = w64 (2 ^ 32 - 1)) by (rewrite (EBr 17%nat 17%bv eq_refl), KRA by fd_in; exact R17).
assert (EB20 : ew EB 20 = w64 (if lc_sys tv then 1 else 0))
  by (rewrite (EBr 20%nat 20%bv eq_refl), KRA by fd_in; exact R20).
assert (Rsys : 0 <= (if lc_sys tv then 1 else 0) < 2 ^ 64) by (destruct (lc_sys tv); lia).
(* the closings: the journal at the last model, the registers of FD_KEEP as at the cut *)
assert (KR0 : forall rgF, (forall r, In r FD_KEEP -> YK11.getr rgF r = YK11.getr rg1 r) ->
  forall r, In r FD_KEEP -> YK11.getr rgF r = YK11.getr regs r).
{ intros rgF KRB r Hr. rewrite (KRB r Hr). apply KRA. unfold FD_KA. apply in_or_app. left. exact Hr. }
(* +0xf04 .. +0xf18: the check of the key's shadow, a1 = g_cmd[g_q[i]].key, s3 = i, `beq a1, a2` *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ fd_awr_ro. }
fd_md. fd_norm HS HJ SHOK. fd_low HS EB HEX.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* the key matches: at = i *)
  rewrite branch_eq_U, (U_atom _ 32 (TW.Cmd_key Bw q)), (U_atom _ 12 key) in Hc
    by (first [rewrite HEX by lia; assumption | lia]).
  rewrite Hc in HF0. injection HF0 as Hat. subst at_. clear Hc HEX.
  (* +0xf20 .. +0xf24: `bgeu a5, a3` *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { fd_awr_ro. }
  fd_md. fd_norm HS HJ SHOK. fd_low HS EB HEX.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  + (* i + 1 >= g_nq: the exit, `beqz s4` *)
    clear Hc HEX.
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { fd_awr_ro. }
    fd_md. fd_norm HS HJ SHOK. fd_low HS EB HEX.
    psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
    * (* not sys: `sext.w a0, s3; bltz a0` on s3 = i *)
      rewrite branch_eq_U, (U_atom _ 20 _) in Hc by (first [rewrite HEX by lia; eassumption | lia]).
      rewrite U_lit in Hc by lia. assert (Hsys : lc_sys tv = false) by (destruct (lc_sys tv); [discriminate Hc | reflexivity]).
      clear Hc HEX.
      paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
      { fd_awr_ro. }
      fd_md. fd_norm HS HJ SHOK. fd_low HS EB HEX.
      psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
      -- exfalso. rewrite fd_br_lt, (fd_sextw _ 14 i), fd_sg0 in Hc by (first [rewrite HEX by lia; assumption | lia]).
         rewrite (Z.mod_small (i + 2 ^ 31) (2 ^ 32)) in Hc by lia. apply Z.ltb_lt in Hc. lia.
      -- clear Hc HEX.
         paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_WANT.
         { fd_awr_ro. }
         fd_md. fd_norm HS HJ SHOK. fd_low HS EB HEX.
         fd_want_leaf HS HEX HT HJ HC KR0 KRA HAt EB14 EB17 R20 Hsys i Hi1024 rg1 (TW.Cmd_key Bw q) (TW.g_nq Bw).
    * (* sys: s6 = -10 *)
      rewrite branch_eq_U, (U_atom _ 20 _) in Hc by (first [rewrite HEX by lia; eassumption | lia]).
      rewrite U_lit in Hc by lia. assert (Hsys : lc_sys tv = true) by (destruct (lc_sys tv); [reflexivity | discriminate Hc]).
      clear Hc HEX.
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_WANT.
      { fd_awr_ro. }
      fd_md. fd_norm HS HJ SHOK. fd_low HS EB HEX.
      fd_want_leaf HS HEX HT HJ HC KR0 KRA HAt EB14 EB17 R20 Hsys i Hi1024 rg1 (TW.Cmd_key Bw q) (TW.g_nq Bw).
  + (* i + 1 < g_nq: `bltz` on s3 = i (not taken), then the exit, `beqz s4` *)
    clear Hc HEX.
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { fd_awr_ro. }
    fd_md. fd_norm HS HJ SHOK. fd_low HS EB HEX.
    psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
    * exfalso. rewrite fd_br_lt, (fd_sextw _ 14 i), fd_sg0 in Hc by (first [rewrite HEX by lia; assumption | lia]).
      rewrite (Z.mod_small (i + 2 ^ 31) (2 ^ 32)) in Hc by lia. apply Z.ltb_lt in Hc. lia.
    * clear Hc HEX.
      paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
      { fd_awr_ro. }
      fd_md. fd_norm HS HJ SHOK. fd_low HS EB HEX.
      psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
      -- rewrite branch_eq_U, (U_atom _ 20 _) in Hc by (first [rewrite HEX by lia; eassumption | lia]).
         rewrite U_lit in Hc by lia.
         assert (Hsys : lc_sys tv = false) by (destruct (lc_sys tv); [discriminate Hc | reflexivity]).
         clear Hc HEX.
         paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_WANT.
         { fd_awr_ro. }
         fd_md. fd_norm HS HJ SHOK. fd_low HS EB HEX.
         fd_want_leaf HS HEX HT HJ HC KR0 KRA HAt EB14 EB17 R20 Hsys i Hi1024 rg1 (TW.Cmd_key Bw q) (TW.g_nq Bw).
      -- rewrite branch_eq_U, (U_atom _ 20 _) in Hc by (first [rewrite HEX by lia; eassumption | lia]).
         rewrite U_lit in Hc by lia.
         assert (Hsys : lc_sys tv = true) by (destruct (lc_sys tv); [reflexivity | discriminate Hc]).
         clear Hc HEX.
         paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_WANT.
         { fd_awr_ro. }
         fd_md. fd_norm HS HJ SHOK. fd_low HS EB HEX.
         fd_want_leaf HS HEX HT HJ HC KR0 KRA HAt EB14 EB17 R20 Hsys i Hi1024 rg1 (TW.Cmd_key Bw q) (TW.g_nq Bw).
- (* the key differs: the search goes on at i + 1 *)
  rewrite branch_eq_U, (U_atom _ 32 (TW.Cmd_key Bw q)), (U_atom _ 12 key) in Hc
    by (first [rewrite HEX by lia; assumption | lia]).
  rewrite Hc in HF0. rename Hc into Hkey. clear HEX.
  assert (Hf1 : f = S (f - 1)) by (unfold f, TC.CMDS_MAX in *; lia).
  (* +0xf20 .. +0xf24: a7 into s3, `bgeu a5, a3` *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { fd_awr_ro. }
  fd_md. fd_norm HS HJ SHOK. fd_low HS EB HEX.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  + (* i + 1 >= g_nq: at = -1 *)
    rewrite branch_geu_U, (U_atom _ 15 (i + 1)), (U_atom _ 13 (TW.g_nq Bw)) in Hc
      by (first [rewrite HEX by lia; assumption | lia]).
    apply negb_true_iff, Z.ltb_ge in Hc.
    rewrite Hf1, fd_find_step, (proj2 (Z.ltb_ge (i + 1) (TW.g_nq Bw)) Hc) in HF0.
    injection HF0 as Hat. subst at_. clear Hc HEX.
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { fd_awr_ro. }
    fd_md. fd_norm HS HJ SHOK. fd_low HS EB HEX.
    psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
    * (* not sys: `bltz` on s3 = 2 ^ 32 - 1 sign-extended (taken), then g_nq's test *)
      rewrite branch_eq_U, (U_atom _ 20 _) in Hc by (first [rewrite HEX by lia; eassumption | lia]).
      rewrite U_lit in Hc by lia.
      assert (Hsys : lc_sys tv = false) by (destruct (lc_sys tv); [discriminate Hc | reflexivity]).
      clear Hc HEX.
      paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
      { fd_awr_ro. }
      fd_md. fd_norm HS HJ SHOK. fd_low HS EB HEX.
      psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
      -- clear Hc HEX.
         paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_WANT.
         { fd_awr_ro. }
         fd_md. fd_norm HS HJ SHOK. fd_low HS EB HEX.
         fd_want_leaf HS HEX HT HJ HC KR0 KRA HAt EB14 EB17 R20 Hsys i Hi1024 rg1 (TW.Cmd_key Bw q) (TW.g_nq Bw).
      -- exfalso. rewrite fd_br_lt, (fd_sextw _ 17 (2 ^ 32 - 1)), fd_sg0 in Hc
           by (first [rewrite HEX by lia; assumption | lia]).
         vm_compute in Hc. discriminate Hc.
    * rewrite branch_eq_U, (U_atom _ 20 _) in Hc by (first [rewrite HEX by lia; eassumption | lia]).
      rewrite U_lit in Hc by lia.
      assert (Hsys : lc_sys tv = true) by (destruct (lc_sys tv); [reflexivity | discriminate Hc]).
      clear Hc HEX.
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_WANT.
      { fd_awr_ro. }
      fd_md. fd_norm HS HJ SHOK. fd_low HS EB HEX.
      fd_want_leaf HS HEX HT HJ HC KR0 KRA HAt EB14 EB17 R20 Hsys i Hi1024 rg1 (TW.Cmd_key Bw q) (TW.g_nq Bw).
  + (* i + 1 < g_nq: `bltz` on a7 sign-extended (taken), back to the head at i + 1 *)
    rewrite branch_geu_U, (U_atom _ 15 (i + 1)), (U_atom _ 13 (TW.g_nq Bw)) in Hc
      by (first [rewrite HEX by lia; assumption | lia]).
    apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hlt. clear HEX.
    (* the model at i + 1: i + 1 < CMDS_MAX, and the search from 0 is the search from i + 1 *)
    rewrite Hf1, fd_find_step, (proj2 (Z.ltb_lt (i + 1) (TW.g_nq Bw)) Hlt) in HF0.
    destruct (TC.CMDS_MAX <=? i + 1) eqn:EC1 in HF0; [discriminate HF0|]. apply Z.leb_gt in EC1.
    assert (Hfa1 : TOP.submit_find_at (S (Z.to_nat TC.CMDS_MAX)) Bw key 0 =
                   TOP.submit_find_at (S (Z.to_nat TC.CMDS_MAX) - Z.to_nat (i + 1)) Bw key (i + 1)).
    { rewrite Hfa. replace (S (Z.to_nat TC.CMDS_MAX) - Z.to_nat i)%nat with (S f) by (unfold f, TC.CMDS_MAX in *; lia).
      rewrite fd_find_step, (proj2 (Z.ltb_lt i (TW.g_nq Bw)) (proj2 Hi)), (proj2 (Z.leb_gt TC.CMDS_MAX i) HiC).
      change (TW.Q_at Bw i) with q. rewrite (proj2 (Z.leb_gt TC.CMDS_MAX q) EQ), Hkey.
      f_equal. unfold f, TC.CMDS_MAX in *. lia. }
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { fd_awr_ro. }
    fd_md. fd_norm HS HJ SHOK. fd_low HS EB HEX.
    psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
    * clear HEX.
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_FIND.
      { fd_awr_ro. }
      fd_md. fd_norm HS HJ SHOK. fd_low HS EB HEX.
      fd_find_leaf HS HEX HT HJ HC KR0 KRA Hco Hlt EC1 Hfa1 EB10 EB14 EB15 EB16 R7 R12 R13 R17 R20 i rg1
        (TW.Cmd_key Bw q).
    * exfalso. rewrite fd_br_lt, (fd_sextw _ 17 (2 ^ 32 - 1)), fd_sg0 in Hc
        by (first [rewrite HEX by lia; assumption | lia]).
      vm_compute in Hc. discriminate Hc.
Qed.

End fd.
