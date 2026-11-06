(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACep.v, with its module paths and module names changed; 1031 of its 1086 lines of code are new or changed and 171 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_op4find: Lemma lc_op4find_ok : lc_op4find_stmt of
   lib/B/Prog/LLVMFuzzerTestOneInput_segs.v, one turn of op 4's find loop over g_q in fuzz_transport.asan-ubsan's
   LLVMFuzzerTestOneInput: from the cut FIND(i) (+0x11ec) to FIND(i + 1) (+0x11ec) or WANT (+0x1498). No call.

   The code (offsets from the entry 0x812a0):
     +0x11ec            `beq a5, s7` (a5 = i + 1, s7 = 0x401): UBSan's index check of g_q, to the trap +0x1b44;
     +0x11f0 .. +0x11fc the shadow check of the 4 bytes at a0 = g_q + 4 i (slow path +0x126c, report 0x82ef0);
     +0x1200 .. +0x121c a1 = g_q[i] (`lw 0(a6)`), `bltu 0x3ff, a1` (UBSan's index check of g_cmd), a1 = 40 a1 with
                        `not t0, s11; bltu t0, a1` (UBSan's overflow check of s11 + a1), a1 = s11 + a1 + 4 (s11 = g_cmd);
     +0x1224 .. +0x1240 the shadow check of the 4 bytes at a1 (slow path +0x127c, report 0x82ef4), a1 = the key,
                        s9 = a4 = i, `beq a1, a2` (a2 = key); +0x1240 s9 = a7 when they differ;
     +0x1244 .. +0x1248 s4 reloaded from 144(s1) (c = F + 32), `bgeu a5, a3` (a3 = g_nq): the last entry exits;
     +0x124c .. +0x1268 a5, a4 + 1, a0, a6 + 4, a7 = s9, `bltz` on s9 sign-extended: -1 (not found) is the head of
                        turn i + 1, an index (found) jumps to the exit;
     +0x1190 .. +0x11b0 the exit: `sd s5, 0(s1)` (g_cmd + 40 serial), s5 = t2 (sys), `beqz t2`: sys gives s6 = -10;
                        else `bltz` on s9: an index gives s6 = 0;
     +0x1480 .. +0x1494 not found: s6 = (g_nq = 512 ? -5 : 0), g_nq by a plain load through the page at 32(s1).

   The model (TOps.v submit_find_at): as the image-A twin (lib/A/Prog/LLVMFuzzerTestOneInput_seg_op4find.v):
   LoopOk.op_ok at lc_opok's facts gives lc_at = Some at (fd_model_some), and one step of the search at i says
   g_q[i] < CMDS_MAX and either at = i or the search from i + 1 answers at.

   How it is proved. Four seats of PaShadow.v's token engine over the G journal (TransportGRunB.v paj_run_x /
   paj_run_to_x), s10 (atom 26) the shadow base:
     A at FIND: g_q[i] (atom 32, 0 .. 1023) in a read-only region at a6, the shadow entry of a0 (g_q's zero shadow,
       trans_settle_cells), facts i + 1 in 1 .. 1024, s7 = 0x401, s11 = g_cmd; the engine decides the two index
       checks; the overflow check is split by hand (fd_ovf); runs to +0x1224;
     B at +0x1224: the key (atom 32) at a1, the slot 144(s1) (s4's own value), the shadow entry of a1 (g_cmd's zero
       shadow); its branches end at FIND (i + 1) or at the exit +0x1190 (fd_x_leaf);
     C at +0x1190 (fd_tail): the slot [sp1, sp1 + 8) writable; one run to +0x1198 stores g_cmd + 40 serial there and
       keeps every other byte (frame_of), so the cut's facts carry over (fd_tag_store: lc_core_kept_run, the spill
       slots at offsets >= 8, the frame's shadow, TMAP_B's rows and c below sp1);
     D at +0x1198: read-only, the page 32(s1) and g_nq at that page - 0x1a4; its branches end at WANT.
   Seats A, B and D write nothing: their memory after a run is the memory before (fd_frame_ro, functional
   extensionality). The registers lc_tag_common reads are kept (FD_KEEP). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YImgTop YB1v YE2k YCe5.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1i YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require AsanCells TransportGB YCfn YF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YFl3.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB settle_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TOps TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Agree QueueFacts LoopOk LinksProof SubmitTag.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
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
destruct (LOK.op_ok LP.links_holds timg_B (lo_ops op) (lo_B op) (fun _ => 1) (l_pl cx) (lo_c op) (lo_k op)
  HA Hops Hc Hn ltac:(lia) ltac:(lia)) as (B' & c' & k' & E & _).
rewrite (lc_op4_eq timg_B (lo_B op) (fun _ => 1) (l_pl cx) (lo_c op) (lo_k op) Hopc) in E.
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

Lemma fd_swrap32 : forall g, 0 <= g < 2 ^ 32 -> bv_swrap 32 g = (g + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31.
Proof. intros g Hg. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. reflexivity. Qed.

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

Lemma fd_addr : forall E a q, ew E 27 = Z_to_bv 64 a -> ew E 32 = Z_to_bv 64 q -> 0 <= a < 2 ^ 32 -> 0 <= q < 1024 ->
  sv_denot E (SAlu ALU_ADD (SOff 27 4) (SMd M_MUL (SOff 32 0) (SLit 40))) = Z_to_bv 64 (a + 4 + 40 * q).
Proof.
intros E a q H27 H32 Ha Hq. rewrite denot_lit_U. f_equal.
assert (U27 : U E (SOff 27 4) = a + 4)
  by (rewrite U_SOff, H27, unsigned_lit_small by lia; apply zcanon_id; unfold M64; lia).
assert (U32 : U E (SOff 32 0) = q) by (apply U_atom; [exact H32 | lia]).
assert (U40 : U E (SLit 40) = 40) by (apply U_lit; lia).
assert (UM : U E (SMd M_MUL (SOff 32 0) (SLit 40)) = 40 * q)
  by (rewrite U_SMd, U32, U40; cbn [zmd_raw]; rewrite zcanon_id by (unfold M64; lia); lia).
rewrite U_SAlu, U27, UM. cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma fd_ovf : forall E q, ew E 27 = w64 TB_g_cmd -> ew E 32 = w64 q -> 0 <= q < 1024 ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_XOR (SOff 27 0) (SLit (-1)))) (sv_denot E (SMd M_MUL (SOff 32 0) (SLit 40)))
  = false.
Proof.
intros E q H27 H32 Hq. rewrite branch_ltu_U, U_SAlu, U_SMd.
rewrite (U_atom E 27 TB_g_cmd H27) by (unfold TB_g_cmd; lia). rewrite (U_atom E 32 q H32) by lia.
rewrite (U_lit E 40) by lia. rewrite U_SLit. cbn [zmd_raw zalu_raw].
match goal with |- (?x <? _) = false => let v := eval vm_compute in x in change x with v end.
apply Z.ltb_ge. rewrite zcanon_id; unfold M64; lia.
Qed.


(* +0x1480 .. +0x1494: s6 = (lw g_nq) - 512 = 0 ? -1 & -5 : 0 *)
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

Lemma fd_valn : forall E n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (sv_denot E (SOff n 0)) mod 2 ^ (8 * Z.of_N 8) = v.
Proof.
intros E n v H Hv. cbn [sv_denot]. rewrite H. unfold w64.
assert (U1 : bv_unsigned (Z_to_bv 64 v) = v) by (apply unsigned_lit_small; exact Hv).
rewrite U1, Z.add_0_r, U1. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply Z.mod_small. exact Hv.
Qed.

Lemma fd_low_byte_mod : forall u n k, 0 <= u -> (k < n)%nat ->
  Z_to_bv 8 (Z.shiftr (u mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k)) = Z_to_bv 8 (Z.shiftr u (8 * Z.of_nat k)).
Proof.
intros u n k Hu Hk. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with (2 ^ 8).
apply Z.bits_inj'. intros i Hi.
destruct (Z_lt_le_dec i 8) as [Hl|Hge].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma fd_chunk_val : forall sg E mem base off (n : N) (e : sv),
  YP09.chunk_ok sg E mem base (YP09.mkChunk off (CVal n e)) -> (Z.of_N n <= 8) ->
  val_mem sg mem (base + off) (N.to_nat n) (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N n)).
Proof.
intros sg E mem base off n e H Hn k Hk. unfold YP09.chunk_ok in H. cbn [YP09.c_off YP09.c_val c_len cv_len] in H.
pose proof (N_nat_Z n) as Hnn.
destruct (H (Z.of_nat k) ltac:(lia)) as (b & Hb1 & Hb2). cbn [cbyte] in Hb1. unfold YP09.byte_of_word in Hb1.
injection Hb1 as <-. rewrite Hb2. f_equal.
pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as Hu. change (bv_modulus 64) with (2 ^ 64) in Hu.
set (u := bv_unsigned (sv_denot E e)) in *.
assert (Hm : 0 <= u mod 2 ^ (8 * Z.of_N n) < 2 ^ (8 * Z.of_nat (N.to_nat n))).
{ rewrite Hnn. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. }
rewrite (le_byte_small _ _ _ Hm Hk). rewrite <- Hnn. symmetry. apply fd_low_byte_mod; [lia | exact Hk].
Qed.
Lemma fd_field : forall sg E m n b cs lo hi wlo whi od (w : N) e,
  region_ok sg E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> (Z.of_N w <= 8) ->
  val_mem sg m (b + od) (N.to_nat w) (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N w)).
Proof.
intros sg E m n b cs lo hi wlo whi od w e (_ & _ & _ & Hcs) Hn Hc Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (fd_chunk_val sg E m b od w e Hck Hw).
Qed.

Lemma fd_qat : forall Bw i, TW.Q_at Bw i = TW.u_at Bw (TW.OFF_g_q + 4 * i) 4.
Proof. reflexivity. Qed.
Lemma fd_kat : forall Bw s, TW.Cmd_key Bw s = TW.u_at Bw (TW.OFF_g_cmd + (40 * s + 4)) 4.
Proof. intros Bw s. unfold TW.Cmd_key, TW.A_Cmd_key. f_equal. ring. Qed.
Lemma fd_nqat : forall Bw, TW.g_nq Bw = TW.u_at Bw (TW.OFF_g_nq + 0) 4.
Proof. intros Bw. rewrite Z.add_0_r. reflexivity. Qed.

(* The seats. A at FIND (+0x11ec): g_q[i] (atom 32) in a read-only region at a6 and the shadow entry of
   a0 = g_q + 4 i; s7 = 0x401 and s11 = g_cmd by facts. *)
Definition FD_Bx : sv := SOff 26 0.
Definition FD_O_KEY : Z := 0x1224.
Definition fd_q_reg : YP09.region := YP09.mkRegion (Some 16%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))].
Definition fd_facts_a : facts :=
  mkFacts [(10%nat, mkAF TB_g_q (TB_g_q + 4092) 0); (15%nat, mkAF 1 1024 0); (23%nat, mkAF 0x401 0x401 0);
           (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (27%nat, mkAF TB_g_cmd TB_g_cmd 0);
           (32%nat, mkAF 0 1023 0)] [] [].
Definition fd_ss_a : sstate := mkSS LO_FIND sr_atoms [fd_q_reg] None fd_facts_a.
Definition FD_SH_A : list shent := [mkSHE 10 0 4].
Definition fd_EA {rc : YM05.RunCeil} (regs : bvmap 5 word) (q : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [w64 q]).

(* B at +0x1224 (a1 = g_cmd + 40 g_q[i] + 4 computed): the key g_cmd[g_q[i]].key (atom 32) at a1, the spill slot
   144(s1) (c = F + 32, s4's own value) and the shadow entry of a1. *)
Definition fd_key_reg : YP09.region := YP09.mkRegion (Some 11%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))].
Definition fd_c_reg : YP09.region := YP09.mkRegion (Some 9%nat) 144 152 0 0 [YP09.mkChunk 144 (CVal 8 (SOff 20 0))].
Definition fd_facts_b : facts :=
  mkFacts [(11%nat, mkAF (TB_g_cmd + 4) (TB_g_cmd + 40 * 1023 + 4) 0); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition fd_ss_b : sstate := mkSS FD_O_KEY sr_atoms [fd_key_reg; fd_c_reg] None fd_facts_b.
Definition FD_SH_B : list shent := [mkSHE 11 0 4].
Definition fd_EB {rc : YM05.RunCeil} (regs : bvmap 5 word) (k : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [w64 k]).
Definition LO_X : Z := 0x1190.

(* C at the exit +0x1190: the slot 0(s1), written by `sd s5, 0(s1)`. *)
Definition fd_st_reg : YP09.region := YP09.mkRegion (Some 9%nat) 0 8 0 8 [].
Definition fd_ss_c : sstate := mkSS LO_X sr_atoms [fd_st_reg] None (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] []).
Definition fd_sp_reg : YP09.region :=
  YP09.mkRegion (Some 9%nat) 32 40 0 0 [YP09.mkChunk 32 (CVal 8 (SLit (transportb_hi 14)))].
Definition fd_nq_reg : YP09.region :=
  YP09.mkRegion None TB_g_nq (TB_g_nq + 4) 0 0 [YP09.mkChunk TB_g_nq (CVal 4 (SOff 13 0))].
Definition fd_ss_d : sstate := mkSS (LO_X + 8) sr_atoms [fd_sp_reg; fd_nq_reg] None (mkFacts [] [] []).
Definition fd_EC {rc : YM05.RunCeil} (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs []).

Section fd. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.

(* The registers this stretch keeps: FD_KEEP (what lc_tag_common reads), FD_KA (all but t0, t1 and a1, from FIND to
   +0x1224), FD_KT (to the exit +0x1190), FD_KF (back to FIND), FD_KW (from +0x1198 to WANT). *)
Definition FD_KEEP : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 23%bv; 24%bv; 26%bv; 27%bv].
Definition FD_KA : list (bv 5) :=
  FD_KEEP ++ [7%bv; 10%bv; 12%bv; 13%bv; 14%bv; 15%bv; 16%bv; 17%bv; 21%bv; 22%bv; 25%bv].
Definition FD_KT : list (bv 5) := FD_KEEP ++ [7%bv; 12%bv; 13%bv; 21%bv].
Definition FD_KS : list (bv 5) := FD_KEEP ++ [7%bv; 13%bv; 25%bv].
Definition FD_KF : list (bv 5) := FD_KEEP ++ [7%bv; 12%bv; 13%bv; 17%bv; 21%bv].
Definition FD_KW : list (bv 5) := FD_KEEP ++ [21%bv; 25%bv].

Ltac fd_in := cbn [In FD_KEEP FD_KA FD_KT FD_KS FD_KF FD_KW app]; repeat (first [left; reflexivity | right]).

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
destruct HT as (Hopc & HL & Hob & Hraw & Hser & Htw & Hcb & H24 & H16 & H8 & H64 & R24 & R27 & R20 & R23).
destruct HL as (HC & (R18 & R26) & Hsp & Hfsh & Hok & He & Hmt & R19).
split; [exact Hopc|].
split.
{ split; [exact (fd_core_regs cx ly' S' W' regs regs2 mem md2 e HC2 KR)|].
  split; [split; (etransitivity; [apply KR; unfold FD_KEEP; fd_in | assumption])|].
  split; [exact Hsp|]. split; [exact Hfsh|]. split; [exact Hok|]. split; [exact He|]. split; [exact Hmt|].
  etransitivity; [apply KR; unfold FD_KEEP; fd_in | exact R19]. }
split; [exact Hob|]. split; [exact Hraw|]. split; [exact Hser|]. split; [exact Htw|]. split; [exact Hcb|].
split; [exact H24|]. split; [exact H16|]. split; [exact H8|]. split; [exact H64|].
split; [etransitivity; [apply KR; unfold FD_KEEP; fd_in | exact R24]|].
split; [etransitivity; [apply KR; unfold FD_KEEP; fd_in | exact R27]|].
split; [etransitivity; [apply KR; unfold FD_KEEP; fd_in | exact R20]|].
etransitivity; [apply KR; unfold FD_KEEP; fd_in | exact R23].
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
  YK11.getr regs2 10 = w64 (TB_g_q + 4 * i) -> YK11.getr regs2 16 = w64 (TB_g_q + 4 * i) ->
  YK11.getr regs2 14 = w64 i -> YK11.getr regs2 15 = w64 (i + 1) ->
  YK11.getr regs2 13 = w64 (TW.g_nq (tg_B2 tv)) -> YK11.getr regs2 17 = w64 (2 ^ 32 - 1) ->
  YK11.getr regs2 12 = w64 (sv_key kd) -> YK11.getr regs2 7 = w64 (if lc_sys tv then 1 else 0) ->
  YK11.getr regs2 21 = w64 (TB_g_cmd + 40 * tg_serial tv) ->
  @lc_st_find rc B MT cx op i W' (lc_cfg cx LO_FIND regs2 mem md2).
Proof.
intros cx op B1 ly' S' W' regs regs2 mem md md2 e i HT HC2 KR D kd tv Hco Hi HiC Hfa
  R10 R16 R14 R15 R13 R17 R12 R7 R21.
unfold lc_st_find. exists ly', S', regs2, mem, md2, e, B1. cbv zeta.
split; [reflexivity|].
split; [exact (fd_tag_kept cx op B1 ly' S' W' regs regs2 mem md md2 e HT HC2 KR)|].
repeat (split; [eassumption|]). exact R21.
Qed.


(* the store at +0x1190 keeps every byte outside [sp1, sp1 + 8): the cut's facts carry over *)
Lemma fd_tgn_le : forall D B1 c3, tg_n (lc_tag_vals D B1 c3) <= 21.
Proof.
intros D B1 c3. unfold lc_tag_vals. destruct (TOP.fuzz_u8_m D c3) as [c4 lb].
unfold TOP.fuzz_take_m. cbv zeta. cbn [tg_n].
pose proof (Z.mod_pos_bound lb 22 ltac:(lia)).
destruct (lb mod 22 + 3 - 3 <? TOP.fi_n c4) eqn:E; [lia | apply Z.ltb_ge in E; lia].
Qed.

Lemma fd_cs_len : forall D B1 c3 len disp key, 0 <= tg_n (lc_tag_vals D B1 c3) ->
  (length (TW.zs (TOP.cmd_struct (tg_cbytes (lc_tag_vals D B1 c3)) len disp key)) <= 32)%nat.
Proof.
intros D B1 c3 len disp key Hn. pose proof (fd_tgn_le D B1 c3) as Hle. revert Hn Hle.
unfold lc_tag_vals. destruct (TOP.fuzz_u8_m D c3) as [c4 lb]. unfold TOP.fuzz_take_m. cbv zeta. cbn [tg_n tg_cbytes].
set (n := if lb mod 22 + 3 - 3 <? TOP.fi_n c4 then lb mod 22 + 3 - 3 else TOP.fi_n c4). intros Hn Hle.
unfold TW.zs, TOP.cmd_struct. rewrite length_map, !length_app, repeat_length, TWL.length_put. cbn [length].
pose proof (TWL.length_sub_le D (TOP.fi_off c4) (Z.to_nat n)). lia.
Qed.

Lemma fd_tag_store : forall cx op B1 ly' S' (W' : world segs) regs regs1 mem mem1 md md1 e,
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_tag_common rc B MT cx op B1 ly' S' W' regs mem md e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] YCfn.LLVMF_STK (lc_sp0 cx) []
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly' S' W' mem1 md1 e ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lc_sp1 cx <= a < lc_sp1 cx + 8) ->
     aview segs (w_H W') mem1 a = aview segs (w_H W') mem a) ->
  (forall a, apresent (w_H W') mem a -> apresent (w_H W') mem1 a) ->
  (forall r, In r FD_KEEP -> YK11.getr regs1 r = YK11.getr regs r) ->
  @lc_tag_common rc B MT cx op B1 ly' S' W' regs1 mem1 md1 e.
Proof.
intros cx op B1 ly' S' W' regs regs1 mem mem1 md md1 e LAWS HB HT HJ1 AV GA KR.
pose proof HT as HT0. unfold lc_tag_common in HT0 |- *. cbv zeta in HT0 |- *.
destruct HT0 as (Hopc & HL & Hob & Hraw & Hser & Htw & Hcb & H24 & H16 & H8 & H64 & R24 & R27 & R20 & R23).
destruct HL as (HC & (R18 & R26) & Hsp & Hfsh & Hok & He & Hmt & R19).
destruct (lc_geom B MT XL RLO RHI cx ly' S' W' regs mem md e HB HC) as [HAR Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVE].
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1r & Hsp1al & _ & HF4096 & _ & HFceil & _).
pose proof YM05.alloc_ceiling_value as Hac. pose proof YM05.alloc_ceiling_lt as Hlt.
unfold LF_FRAME in Hsp1r. unfold LF_FBYTES in HFceil.
destruct Hstk as (_ & _ & Hs0 & Hs47).
assert (RW : forall o, 8 <= o -> o + 8 <= 320 -> forall k, 0 <= k < 8 ->
  aview segs (w_H W') mem1 (lc_sp1 cx + o + k) = aview segs (w_H W') mem (lc_sp1 cx + o + k))
  by (intros o Ho1 Ho2 k Hk; apply AV; lia).
assert (RD : forall o v, 8 <= o -> o + 8 <= 320 ->
  rdword (aview segs (w_H W') mem) (lc_sp1 cx + o) = Some v -> rdword (aview segs (w_H W') mem1) (lc_sp1 cx + o) = Some v)
  by (intros o v Ho1 Ho2 Hv; rewrite (rdword_ext (aview segs (w_H W') mem) (aview segs (w_H W') mem1));
      [exact Hv | intros k Hk; exact (RW o Ho1 Ho2 k Hk)]).
assert (KR5 : forall r, In r [2; 3; 4; 8; 9] -> YK11.getr regs1 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; apply KR; cbn [In FD_KEEP]; repeat (first [left; apply bv_eq; reflexivity | right]). }
assert (HC1 : @lc_core rc B cx ly' S' W' regs1 mem1 md1 e).
{ apply (lc_core_kept_run B MT XL RLO RHI cx ly' S' W' regs mem md e ly' S' W' regs1 mem1 md1 e HB HC HJ1 eq_refl
    (Permutation_refl _) KR5).
  - intros a Ha. apply AV; lia.
  - intros i Hi. pose proof (HINg ltac:(lia)) as Hin.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hp4096 & Hpc & _).
    pose proof (req_size_pos (l_n cx) ltac:(lia)) as (_ & Hq2). apply AV; lia.
  - intros a Ha. unfold LF_FBYTES in Ha. apply AV; lia.
  - intros a Ha Hp. exact (GA a Hp). }
assert (HSH : 0 <= lc_SH cx /\ lc_SH cx + 32 <= lc_sp1 cx).
{ unfold lc_SH. pose proof (Z.div_le_upper_bound (lc_F cx) 8 (2 ^ 47) ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)). unfold SHADOW_OFF. lia. }
assert (HG8 : forall j, 0 <= j < 32 -> aview segs (w_H W') mem1 (lc_F cx + 32 + j) = aview segs (w_H W') mem (lc_F cx + 32 + j))
  by (intros j Hj; apply AV; lia).
split; [exact Hopc|].
split.
{ split; [exact HC1|].
  split; [split; (etransitivity; [apply KR; fd_in | assumption])|].
  split.
  { unfold lc_spills in Hsp |- *. rewrite Forall_forall in Hsp |- *. intros o Ho.
    pose proof (lf_spill_vals (lc_F cx) ltac:(lia) ltac:(unfold LF_FBYTES; lia)) as V. rewrite Forall_forall in V.
    destruct (V o Ho) as (_ & _ & V8 & V192). exact (RD (fst o) (snd o) V8 ltac:(lia) (Hsp o Ho)). }
  split; [apply (lc_fsh_kept cx (aview segs (w_H W') mem)); [intros a Ha; apply AV; lia | exact Hfsh]|].
  split; [exact Hok|]. split; [exact He|]. split; [exact Hmt|].
  etransitivity; [apply KR; fd_in | exact R19]. }
split; [exact Hob|]. split; [exact Hraw|]. split; [exact Hser|].
split.
{ unfold lc_tw in Htw |- *. apply (tw_kept TMAP_B (aview segs (w_H W') mem)); [exact Htw|].
  intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. apply AV; lia. }
split.
{ apply (lc_garr8_kept (w_H W') (w_H W') mem mem1 (lc_F cx + 32)); [|exact Hcb].
  intros j Hj. pose proof (rdword_range _ _ _ _ H8) as Rn.
  pose proof (fd_cs_len (l_pl cx) B1 (sv_c (lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op))))
    (tg_len (lc_tag_vals (l_pl cx) B1 (sv_c (lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op))))))
    (sv_display (lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op)))) (sv_key (lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op))))
    ltac:(lia)) as HLn.
  exact (HG8 j ltac:(lia)). }
split; [exact (RD 24 _ ltac:(lia) ltac:(lia) H24)|].
split; [exact (RD 16 _ ltac:(lia) ltac:(lia) H16)|].
split; [exact (RD 8 _ ltac:(lia) ltac:(lia) H8)|].
split; [exact (RD 64 _ ltac:(lia) ltac:(lia) H64)|].
split; [etransitivity; [apply KR; fd_in | exact R24]|].
split; [etransitivity; [apply KR; fd_in | exact R27]|].
split; [etransitivity; [apply KR; fd_in | exact R20]|].
etransitivity; [apply KR; fd_in | exact R23].
Qed.

Section fx. Context {fx : YK11.FPState}.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma fd_entry_a : forall ly S (W : world segs) regs mem md i Bw,
  decode_zshadow_at B TB_g_q (TB_g_q + TW.SZ_g_q) -> @AR rc segs B ly S W mem md ->
  YK11.getr regs 10 = w64 (TB_g_q + 4 * i) -> YK11.getr regs 16 = w64 (TB_g_q + 4 * i) ->
  YK11.getr regs 15 = w64 (i + 1) -> YK11.getr regs 23 = w64 0x401 -> YK11.getr regs 27 = w64 TB_g_cmd ->
  YK11.getr regs 26 = w64 SHADOW_OFF -> 0 <= i < 1024 -> 0 <= TW.Q_at Bw i < 1024 ->
  tw_at TMAP_B (aview segs (w_H W) mem) Bw ->
  st_ok_pi segs VAL (fd_EA regs (TW.Q_at Bw i)) fd_ss_a
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + LO_FIND)) mem (YK11.seg_rom segs))) /\
  sh_ok segs FD_Bx FD_SH_A (fd_EA regs (TW.Q_at Bw i)) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md i Bw HZ HAR R10 R16 R15 R23 R27 R26 Hi Hq Htw.
set (E := fd_EA regs (TW.Q_at Bw i)).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, fd_EA; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = w64 (TW.Q_at Bw i))
  by (unfold E, fd_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
pose proof (EE 10%nat 10%bv eq_refl) as E10. rewrite R10 in E10.
pose proof (EE 16%nat 16%bv eq_refl) as E16. rewrite R16 in E16.
pose proof (EE 15%nat 15%bv eq_refl) as E15. rewrite R15 in E15.
pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite R23 in E23.
pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite R27 in E27.
pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite R26 in E26.
assert (EC : TB_g_q = 6232192) by reflexivity.
assert (U10 : bv_unsigned (ew E 10) = TB_g_q + 4 * i) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U16 : bv_unsigned (ew E 16) = TB_g_q + 4 * i) by (rewrite E16; apply unsigned_lit_small; lia).
assert (U15 : bv_unsigned (ew E 15) = i + 1) by (rewrite E15; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = 0x401) by (rewrite E23; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = TB_g_cmd) by (rewrite E27; apply unsigned_lit_small; unfold TB_g_cmd; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF)
  by (rewrite E26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = TW.Q_at Bw i) by (rewrite E32; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold fd_ss_a.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil].
    unfold fd_q_reg, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U16. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ (TB_g_q + 4 * i) 0 4 (SOff 32 0) (TW.Q_at Bw i)).
    * cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * cbn. lia.
    * lia.
    * rewrite Z.add_0_r, fd_qat.
      exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_q TB_g_q TW.SZ_g_q (4 * i) 4 TMAP_B_ok Htw TMAP_B_g_q
        ltac:(lia) ltac:(unfold TW.SZ_g_q; lia)).
  + cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  + unfold fd_facts_a, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U10, U15, U23, U26, U27, U32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
- unfold sh_ok, FD_SH_A. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem E FD_Bx 10 (TB_g_q + 4 * i) 4 (TB_g_q + 4 * i) 0 4).
  + exact (proj1 (decode_zshadow_ra B ly S W mem md TB_g_q (TB_g_q + TW.SZ_g_q) (TB_g_q + 4 * i) 4 HAR HZ
      ltac:(lia) ltac:(rewrite EC; lia) ltac:(rewrite EC; unfold TW.SZ_g_q; lia))).
  + unfold U, FD_Bx. cbn [sv_denot]. rewrite E26, Z.add_0_r, Z_to_bv_bv_unsigned.
    apply unsigned_lit_small. unfold SHADOW_OFF. lia.
  + apply U_atom; [exact E10 | lia].
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.
Lemma fd_entry_b : forall ly S (W : world segs) regs mem md q sp1 c Bw,
  decode_zshadow_at B TB_g_cmd (TB_g_cmd + TW.SZ_g_cmd) -> @AR rc segs B ly S W mem md ->
  YK11.getr regs 11 = w64 (TB_g_cmd + 4 + 40 * q) -> YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 20 = w64 c ->
  YK11.getr regs 26 = w64 SHADOW_OFF -> 0 <= q < 1024 -> 2 ^ 40 <= sp1 <= 2 ^ 47 -> 0 <= c < 2 ^ 64 ->
  rdword (aview segs (w_H W) mem) (sp1 + 144) = Some c ->
  tw_at TMAP_B (aview segs (w_H W) mem) Bw ->
  st_ok_pi segs VAL (fd_EB regs (TW.Cmd_key Bw q)) fd_ss_b
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + FD_O_KEY)) mem (YK11.seg_rom segs))) /\
  sh_ok segs FD_Bx FD_SH_B (fd_EB regs (TW.Cmd_key Bw q)) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md q sp1 c Bw HZ HAR R11 R9 R20 R26 Hq Hsp Hc Hsl Htw.
set (E := fd_EB regs (TW.Cmd_key Bw q)).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, fd_EB; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = w64 (TW.Cmd_key Bw q))
  by (unfold E, fd_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
pose proof (EE 11%nat 11%bv eq_refl) as E11. rewrite R11 in E11.
pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite R9 in E9.
pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite R20 in E20.
pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite R26 in E26.
assert (EC : TB_g_cmd = 6180992) by reflexivity.
assert (Rk : 0 <= TW.Cmd_key Bw q < 2 ^ 32)
  by (pose proof (TWL.u_at_range Bw (TW.A_Cmd_key q) 4) as R; exact R).
assert (U11 : bv_unsigned (ew E 11) = TB_g_cmd + 4 + 40 * q) by (rewrite E11; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF)
  by (rewrite E26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = TW.Cmd_key Bw q) by (rewrite E32; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold fd_ss_b.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * unfold fd_key_reg, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U11. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ (TB_g_cmd + 4 + 40 * q) 0 4 (SOff 32 0) (TW.Cmd_key Bw q)).
      -- cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      -- cbn. lia.
      -- lia.
      -- rewrite fd_kat. replace (TB_g_cmd + 4 + 40 * q + 0) with (TB_g_cmd + (40 * q + 4)) by lia.
         exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_cmd TB_g_cmd TW.SZ_g_cmd (40 * q + 4) 4 TMAP_B_ok Htw
           TMAP_B_g_cmd ltac:(lia) ltac:(unfold TW.SZ_g_cmd; lia)).
    * unfold fd_c_reg, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ sp1 144 8 (SOff 20 0) c).
      -- cbn [sv_denot]. rewrite E20, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      -- cbn. lia.
      -- lia.
      -- exact (val_mem_of_rdword segs (w_H W) mem _ _ Hsl).
  + apply pairwise_disjoint_of_extents.
    unfold fd_key_reg, fd_c_reg, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U11, U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  + unfold fd_facts_b, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U11, U26, U32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
- unfold sh_ok, FD_SH_B. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem E FD_Bx 11 (TB_g_cmd + 4 + 40 * q) 4 (TB_g_cmd + 4 + 40 * q) 0 4).
  + exact (proj1 (decode_zshadow_ra B ly S W mem md TB_g_cmd (TB_g_cmd + TW.SZ_g_cmd) (TB_g_cmd + 4 + 40 * q) 4
      HAR HZ ltac:(lia) ltac:(rewrite EC; lia) ltac:(rewrite EC; unfold TW.SZ_g_cmd; lia))).
  + unfold U, FD_Bx. cbn [sv_denot]. rewrite E26, Z.add_0_r, Z_to_bv_bv_unsigned.
    apply unsigned_lit_small. unfold SHADOW_OFF. lia.
  + apply U_atom; [exact E11 | lia].
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.
Lemma fd_entry_c : forall (W : world segs) regs mem sp1,
  YK11.getr regs 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  (forall a, sp1 <= a < sp1 + 8 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (fd_EC regs) fd_ss_c
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + LO_X)) mem (YK11.seg_rom segs))) /\
  sh_ok segs FD_Bx [] (fd_EC regs) (mrestrict (w_H W) mem).
Proof.
intros W regs mem sp1 R9 Hsp Hal Psp.
assert (U9 : bv_unsigned (ew (fd_EC regs) 9) = sp1)
  by (unfold fd_EC; rewrite (ew_Eimg_Ereg_nat regs [] 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
split; [|constructor].
rewrite restrict_mkst_fx. unfold fd_ss_c.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold fd_st_reg, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable segs). apply Psp. lia.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9. change (2 ^ 5) with 32.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.
Lemma fd_entry_d : forall (W : world segs) regs mem sp1 Bw,
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 13 = w64 (TW.g_nq Bw) -> 2 ^ 40 <= sp1 <= 2 ^ 47 ->
  rdword (aview segs (w_H W) mem) (sp1 + 32) = Some (transportb_hi 14) ->
  tw_at TMAP_B (aview segs (w_H W) mem) Bw ->
  st_ok_pi segs VAL (fd_EC regs) fd_ss_d
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (LO_X + 8))) mem (YK11.seg_rom segs))) /\
  sh_ok segs FD_Bx [] (fd_EC regs) (mrestrict (w_H W) mem).
Proof.
intros W regs mem sp1 Bw R9 R13 Hsp Hsl Htw.
set (E := fd_EC regs).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, fd_EC; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite R9 in E9.
pose proof (EE 13%nat 13%bv eq_refl) as E13. rewrite R13 in E13.
assert (Rn : 0 <= TW.g_nq Bw < 2 ^ 32) by (pose proof (TWL.u_at_range Bw TW.OFF_g_nq 4) as R; exact R).
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (EN : TB_g_nq = 6157792) by reflexivity.
assert (EH : transportb_hi 14 = 6158212) by reflexivity.
split; [|constructor].
rewrite restrict_mkst_fx. unfold fd_ss_d.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold fd_sp_reg, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ sp1 32 8 (SLit (transportb_hi 14)) (transportb_hi 14)).
    * reflexivity.
    * rewrite EH. cbn. lia.
    * lia.
    * exact (val_mem_of_rdword segs (w_H W) mem _ _ Hsl).
  + unfold fd_nq_reg, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite EN. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ 0 6157792 4 (SOff 13 0) (TW.g_nq Bw)).
    * cbn [sv_denot]. rewrite E13, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * cbn. lia.
    * lia.
    * rewrite fd_nqat. replace (0 + 6157792) with (TB_g_nq + 0) by (rewrite EN; reflexivity).
      exact (tw_read_val segs _ TMAP_B Bw TW.OFF_g_nq TB_g_nq TW.SZ_g_nq 0 4 TMAP_B_ok Htw
        TMAP_B_g_nq ltac:(lia) ltac:(unfold TW.SZ_g_nq; lia)).
- apply pairwise_disjoint_of_extents.
  unfold fd_sp_reg, fd_nq_reg, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U9, EN.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | lia].
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split.
Qed.
End fx.

Lemma fd_pc : forall k, Z_to_bv 64 (@pa_val _ transportb_listing PI_transportb A_TEXT + k) = w64 (transportb_text + k).
Proof. intros k. reflexivity. Qed.

Ltac fd_awr_ro :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

Ltac fd_md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    let md := fresh "mdw" in set (md := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md; clear mt end.

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

Ltac fd_low HS E0 HEX :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (HEX : forall n, (n < 1024)%nat -> ew Ex n = ew E0 n)
      by (let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn;
          repeat rewrite ew_ewset_other by lia; reflexivity)
  end.

Ltac fd_rv HS :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
    refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx _ HS) _);
    lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end
  end.

Ltac fd_hae HEX HAE rg1 kq Ex :=
  assert (HAE : env_agree 32 (Ereg rg1 [w64 kq]) Ex)
    by (split; [let nn := fresh "nn" in let Hnn := fresh "Hnn" in
                intros nn Hnn; rewrite (HEX nn) by lia; apply Eimg_low; unfold A_TEXT; lia
               | reflexivity]).

Lemma fd_want_close : forall cx op B1 ly' S' (W' : world segs) regs regs2 mem md md2 e at_,
  @lc_tag_common rc B MT cx op B1 ly' S' W' regs mem md e ->
  @lc_core rc B cx ly' S' W' regs mem md2 e ->
  (forall r, In r FD_KEEP -> YK11.getr regs2 r = YK11.getr regs r) ->
  let D := l_pl cx in
  let kd := lc_sub_kd D (lc_oc D (lo_c op)) in
  let tv := lc_tag_vals D B1 (sv_c kd) in
  lc_at tv (sv_key kd) = Some at_ ->
  rdword (aview segs (w_H W') mem) (lc_sp1 cx) = Some (TB_g_cmd + 40 * tg_serial tv) ->
  YK11.getr regs2 22 = w64 (lc_want tv at_) -> YK11.getr regs2 25 = w64 (at_ mod 2 ^ 32) ->
  YK11.getr regs2 21 = w64 (if lc_sys tv then 1 else 0) ->
  @lc_st_want rc B MT cx op W' (lc_cfg cx LO_WANT regs2 mem md2).
Proof.
intros cx op B1 ly' S' W' regs regs2 mem md md2 e at_ HT HC2 KR D kd tv HAt Hsp R22 R25 R21.
unfold lc_st_want. exists ly', S', regs2, mem, md2, e, B1, at_. cbv zeta.
split; [reflexivity|].
split; [exact (fd_tag_kept cx op B1 ly' S' W' regs regs2 mem md md2 e HT HC2 KR)|].
split; [exact Hsp|]. split; [exact HAt|]. split; [exact R22|]. split; [exact R25 | exact R21].
Qed.

(* lc_sys of the goal's tv rewritten by Hsys (stated at the set name tv) *)
Ltac fd_sys Hsys :=
  lazymatch type of Hsys with _ = ?b =>
  lazymatch goal with |- context [lc_sys ?t] =>
    let E := fresh "E" in assert (E : lc_sys t = b) by exact Hsys; rewrite E; clear E end end.

(* the cut WANT at the end of a run of seat D *)
Ltac fd_want_leaf HS HEX HT1 HJ HC1 HAt RDW Q25 Q21 Hsys Hat0 nq rg1 :=
  lazymatch goal with |- SRr _ _ (mkCfg (?mk ?rgF ?pcx ?mm ?rom) ?mdF) _ =>
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msr =>
  lazymatch type of HT1 with @lc_tag_common _ _ _ ?cx ?op ?B1 ?ly ?S ?W ?rg ?mem ?md ?e =>
    let HAE := fresh "HAE" in let KRB := fresh "KRB" in
    assert (HAE : env_agree 32 (Ereg rg1 []) Ex)
      by (split; [let nn := fresh "nn" in let Hnn := fresh "Hnn" in
                  intros nn Hnn; try rewrite (HEX nn) by lia; apply Eimg_low; unfold A_TEXT; lia
                 | reflexivity]);
    assert (KRB : forall r, In r FD_KW -> YK11.getr rgF r = YK11.getr rg1 r)
      by (exact (regs_kept_of_st_ok_pi Ex ssx msr rg1 _ FD_KW HS HAE ltac:(vm_compute; reflexivity)));
    apply SRr_ret; right; rewrite fd_pc;
    eapply (fd_want_close cx op B1 ly S W rg rgF mem md mdF e _ HT1 (conj HJ (proj2 HC1))
      (fun r Hr => KRB r (in_or_app _ _ _ (or_introl Hr))));
    [ exact HAt | exact RDW
    | fd_rv HS;
      first
      [ lazymatch goal with |- sv_denot _ (SLit _) = _ => idtac end;
        cbn [sv_denot]; unfold lc_want; fd_sys Hsys; cbv beta iota;
        try rewrite (proj2 (Z.ltb_ge _ 0) Hat0); cbn [andb];
        apply bv_eq; vm_compute; reflexivity
      | rewrite (fd_space _ nq) by (first [assumption | rewrite HEX by lia; assumption | lia]);
        unfold lc_want; fd_sys Hsys; cbv beta iota; change (-1 <? 0) with true; cbn [andb];
        reflexivity ]
    | rewrite KRB by fd_in; exact Q25
    | rewrite KRB by fd_in; exact Q21 ]
  end end end.

(* +0x1190 .. WANT: `sd s5, 0(s1)`, s5 = t2 (sys), `beqz t2`, `bltz` on s9 sign-extended, the space test of g_nq. *)
Lemma fd_tail : lp_prem B MT XL RLO RHI ->
  forall cx op B1 ly' S' (W' : world segs) regs mem md e at_ (P : world segs -> config -> Prop),
  @lc_base rc B MT XL RLO RHI cx ->
  @lc_tag_common rc B MT cx op B1 ly' S' W' regs mem md e ->
  let D := l_pl cx in
  let kd := lc_sub_kd D (lc_oc D (lo_c op)) in
  let tv := lc_tag_vals D B1 (sv_c kd) in
  lc_at tv (sv_key kd) = Some at_ -> at_ = -1 \/ 0 <= at_ < TC.CMDS_MAX ->
  YK11.getr regs 25 = w64 (at_ mod 2 ^ 32) -> YK11.getr regs 7 = w64 (if lc_sys tv then 1 else 0) ->
  YK11.getr regs 21 = w64 (TB_g_cmd + 40 * tg_serial tv) -> YK11.getr regs 13 = w64 (TW.g_nq (tg_B2 tv)) ->
  SRr segs W' (mkCfg (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (@pa_val _ transportb_listing PI_transportb A_TEXT + LO_X))
                         mem (YK11.seg_rom segs)) md)
    (fun W2 c2 => P W2 c2 \/ @lc_st_want rc B MT cx op W2 c2).
Proof.
intros HP cx op B1 ly' S' W' regs mem md e at_ P HB HT D kd tv HAt Hatr R25 R7 R21 R13.
pose proof HT as HT0. unfold lc_tag_common in HT0. cbv zeta in HT0.
destruct HT0 as (Hopc & HL & Hob & Hraw & Hser & Htw & Hcb & H24 & H16 & H8 & H64 & R24 & R27 & R20 & R23).
destruct HL as (HC & (R18 & R26) & Hsp & Hfsh & Hok & He & Hmt & R19).
pose proof (lp_laws B MT XL RLO RHI HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned B MT XL RLO RHI HP)) as HGX.
destruct (lc_geom B MT XL RLO RHI cx ly' S' W' regs mem md e HB HC) as [HAR Hsp0al Hstk Hsp1c HFaddr HFin Hgn HINg HLIVE].
pose proof HC as (HJ & _ & _ & _ & _ & _ & R9 & R3 & R4 & Hsp1r & Hsp1al & _).
assert (Hsp1b : 2 ^ 40 <= lc_sp1 cx <= 2 ^ 47 - 320).
{ pose proof YM05.alloc_ceiling_value as Hac. destruct Hstk as (_ & _ & H0 & H47). unfold LF_FRAME in Hsp1r. lia. }
assert (Psp : forall a, lc_sp1 cx <= a < lc_sp1 cx + 8 -> apresent (w_H W') mem a).
{ intros a Ha. pose proof HJ as (HSTKJ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). apply Hpres.
  unfold LF_FRAME, YCfn.LLVMF_STK in *. lia. }
assert (Hsp46 : 2 ^ 46 <= lc_sp1 cx).
{ pose proof YM05.alloc_ceiling_value as Hac. lia. }
destruct (fd_entry_c (fx := l_fx cx) W' regs mem (lc_sp1 cx) R9 ltac:(lia) Hsp1al Psp) as (HS & SHOK).
set (EC := fd_EC regs) in HS, SHOK.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (HEI : img_env (@pa_val _ transportb_listing PI_transportb) A_LIM Ex) by (unfold EC, fd_EC; apply Eimg_env) end.
assert (U9 : bv_unsigned (ew EC 9) = lc_sp1 cx)
  by (unfold EC, fd_EC; rewrite (ew_Eimg_Ereg_nat regs [] 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
pose proof (@paj_run_to_x (l_fx cx) rc YE2k.tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
paj_run_to_tok RUNTO HS HJ SHOK YC1i.Bspan (LO_X + 8).
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U9 in Ha.
  left. split; [unfold awr_byte; left; unfold LF_FRAME, YCfn.LLVMF_STK in *; lia | lia]. }
fd_md.
lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ => set (EC1 := E1) in * end.
assert (HE1 : forall n, (n < 1024)%nat -> ew EC1 n = ew EC n)
  by (intros n Hn; unfold EC1; repeat rewrite ew_ewset_other by lia; reflexivity).
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m1) => set (ms1 := m1) in * end.
assert (KM : forall x : word, ~ (lc_sp1 cx <= bv_unsigned x < lc_sp1 cx + 8) -> ms_mem ms1 x = mem x).
{ intros x Hx. lazymatch goal with HFx : frame_of _ _ mem (ms_mem ms1) |- _ => apply HFx end.
  intros (r & Hin & Hr).
  lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change l with l' in Hin end.
  cbn [In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
  assert (U91 : bv_unsigned (ew EC1 9) = lc_sp1 cx) by (rewrite (HE1 9%nat) by lia; exact U9).
  lia. }
assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ (lc_sp1 cx <= a < lc_sp1 cx + 8) ->
  aview segs (w_H W') (ms_mem ms1) a = aview segs (w_H W') mem a).
{ intros a Ha Hn. unfold aview, mbyte, mrestrict. rewrite (KM (Z_to_bv 64 a)); [reflexivity|].
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; lia). rewrite Ua. exact Hn. }
assert (GA : forall a, apresent (w_H W') mem a -> apresent (w_H W') (ms_mem ms1) a)
  by (intros a Ha; eapply apresent_grows; [eassumption | exact Ha]).
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
assert (Rser : 0 <= TB_g_cmd + 40 * tg_serial tv < 2 ^ 64) by (unfold tv, kd, D; unfold TB_g_cmd, TC.CMDS_MAX in *; lia).
assert (V21 : bv_unsigned (sv_denot EC1 (SOff 21 0)) mod 2 ^ (8 * Z.of_N 8) = TB_g_cmd + 40 * tg_serial tv).
{ apply fd_valn; [|exact Rser]. rewrite (HE1 21%nat) by lia. unfold EC, fd_EC.
  rewrite (ew_Eimg_Ereg_nat regs [] 21 21%bv eq_refl). exact R21. }
pose proof (fd_field _ EC1 _ 9%nat (lc_sp1 cx) _ _ _ _ _ 0 8 (SOff 21 0) RG0
  ltac:(rewrite (HE1 9%nat) by lia; exact U9) ltac:(cbn [In]; left; reflexivity) ltac:(lia)) as VST.
rewrite V21, Z.add_0_r in VST. change (N.to_nat 8) with 8%nat in VST.
pose proof (YF0x.val_mem_rdword (w_H W') (ms_mem ms1) (lc_sp1 cx) _ Rser VST) as RDW.
assert (HAE1 : env_agree 32 (Ereg regs []) EC1)
  by (split; [intros nn Hnn; rewrite (HE1 nn) by lia; unfold EC, fd_EC; apply Eimg_low; unfold A_TEXT; lia
             | reflexivity]).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msr =>
  pose proof (regs_kept_of_st_ok_pi Ex ssx msr regs [] FD_KS HS HAE1 ltac:(vm_compute; reflexivity)) as KR1;
  assert (Q21 : YK11.getr (ms_regs ms1) 21 = w64 (if lc_sys tv then 1 else 0))
    by (fd_rv HS; apply (fd_soffk _ _ _ (if lc_sys tv then 1 else 0));
        [rewrite (HE1 7%nat) by lia; unfold EC, fd_EC; rewrite (ew_Eimg_Ereg_nat regs [] 7 7%bv eq_refl); exact R7
        | destruct (lc_sys tv); lia | lia]) end.
cbn [ms_regs restrict] in KR1, Q21.
pmkst HS.
set (rg1 := ms_regs ms1) in *. set (mem1 := ms_mem ms1) in *.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md1 := mdx) in * end.
assert (HT1 : @lc_tag_common rc B MT cx op B1 ly' S' W' rg1 mem1 md1 e).
{ apply (fd_tag_store cx op B1 ly' S' W' regs rg1 mem mem1 md md1 e LAWS HB HT HJ AV GA).
  intros r Hr. apply KR1. unfold FD_KS. apply in_or_app. left. exact Hr. }
assert (Q25 : YK11.getr rg1 25 = w64 (at_ mod 2 ^ 32)) by (rewrite KR1 by fd_in; exact R25).
assert (Q7 : YK11.getr rg1 7 = w64 (if lc_sys tv then 1 else 0)) by (rewrite KR1 by fd_in; exact R7).
assert (Q13 : YK11.getr rg1 13 = w64 (TW.g_nq (tg_B2 tv))) by (rewrite KR1 by fd_in; exact R13).
assert (Q9 : YK11.getr rg1 9 = w64 (lc_sp1 cx)) by (rewrite KR1 by fd_in; exact R9).
pose proof HT1 as HT10. unfold lc_tag_common in HT10. cbv zeta in HT10.
destruct HT10 as (_ & (HC1 & _ & Hsp1 & _) & _ & _ & _ & Htw1 & _).
assert (Hsl : rdword (aview segs (w_H W') mem1) (lc_sp1 cx + 32) = Some (transportb_hi 14)).
{ unfold lc_spills in Hsp1. rewrite Forall_forall in Hsp1. apply (Hsp1 (32, transportb_hi 14)).
  unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm. cbn [app]. fd_in. }
clear HS SHOK HEI.
destruct (fd_entry_d (fx := l_fx cx) W' rg1 mem1 (lc_sp1 cx) (tg_B2 tv) Q9 Q13 ltac:(lia) Hsl Htw1) as (HS & SHOK).
set (ED := fd_EC rg1) in HS, SHOK.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (HEI : img_env (@pa_val _ transportb_listing PI_transportb) A_LIM Ex) by (unfold ED, fd_EC; apply Eimg_env) end.
assert (EDr : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew ED n = YK11.getr rg1 r)
  by (intros n r Hnr; unfold ED, fd_EC; apply ew_Eimg_Ereg_nat; exact Hnr).
assert (ED7 : ew ED 7 = w64 (if lc_sys tv then 1 else 0)) by (rewrite (EDr 7%nat 7%bv eq_refl); exact Q7).
assert (ED13 : ew ED 13 = w64 (TW.g_nq (tg_B2 tv))) by (rewrite (EDr 13%nat 13%bv eq_refl); exact Q13).
assert (ED25 : ew ED 25 = w64 (at_ mod 2 ^ 32)) by (rewrite (EDr 25%nat 25%bv eq_refl); exact Q25).
assert (Rnq : 0 <= TW.g_nq (tg_B2 tv) < 2 ^ 32) by (pose proof (TWL.u_at_range (tg_B2 tv) TW.OFF_g_nq 4) as R; exact R).
assert (Rat : 0 <= at_ mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
pose proof (@paj_run_x (l_fx cx) rc YE2k.tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
pose proof (paj_branch (fx := l_fx cx) (PI := PI_transportb)) as BR.
unfold LO_X in HS. change (4496 + 8) with 4504 in HS.
(* +0x1198 `beqz t2` *)
psrr_branch_tok RUN BR HS SHOK YC1i.Bspan.
- (* t2 = 0: not sys; +0x11a4 `sext.w a0, s9; bltz a0` *)
  rewrite branch_eq_U, (U_atom _ 7 _ ED7) in Hc by (destruct (lc_sys tv); lia).
  rewrite U_lit in Hc by lia.
  assert (Hsys : lc_sys tv = false) by (destruct (lc_sys tv); [discriminate Hc | reflexivity]).
  clear Hc.
  paj_run_tok RUN HS HJ SHOK YC1i.Bspan.
  { fd_awr_ro. }
  fd_md. fd_norm HS HJ SHOK. fd_low HS ED HEX.
  psrr_branch_tok RUN BR HS SHOK YC1i.Bspan.
  + (* s9 < 0: at = -1, the space test of g_nq *)
    rewrite fd_br_lt, (fd_sextw _ 25 (at_ mod 2 ^ 32)), fd_sg0 in Hc
      by (first [assumption | rewrite HEX by lia; assumption | lia]).
    assert (Hat : at_ = -1).
    { destruct Hatr as [-> | Ha]; [reflexivity|].
      rewrite (Z.mod_small at_ (2 ^ 32)) in Hc by (unfold TC.CMDS_MAX in Ha; lia).
      rewrite (Z.mod_small (at_ + 2 ^ 31) (2 ^ 32)) in Hc by (unfold TC.CMDS_MAX in Ha; lia).
      apply Z.ltb_lt in Hc. lia. }
    subst at_. clear Hc HEX.
    paj_run_to_tok RUNTO HS HJ SHOK YC1i.Bspan LO_WANT.
    { fd_awr_ro. }
    fd_md. fd_norm HS HJ SHOK. fd_low HS ED HEX.
    assert (Hat0 : True) by exact I.
    fd_want_leaf HS HEX HT1 HJ HC1 HAt RDW Q25 Q21 Hsys Hat0 (TW.g_nq (tg_B2 tv)) rg1.
  + (* s9 >= 0: at >= 0, s6 = 0 *)
    rewrite fd_br_lt, (fd_sextw _ 25 (at_ mod 2 ^ 32)), fd_sg0 in Hc
      by (first [assumption | rewrite HEX by lia; assumption | lia]).
    assert (Hat0 : 0 <= at_).
    { destruct Hatr as [-> | Ha]; [vm_compute in Hc; discriminate Hc | lia]. }
    clear Hc HEX.
    paj_run_to_tok RUNTO HS HJ SHOK YC1i.Bspan LO_WANT.
    { fd_awr_ro. }
    fd_md. fd_norm HS HJ SHOK. fd_low HS ED HEX.
    fd_want_leaf HS HEX HT1 HJ HC1 HAt RDW Q25 Q21 Hsys Hat0 (TW.g_nq (tg_B2 tv)) rg1.
- (* sys: s6 = -10 *)
  rewrite branch_eq_U, (U_atom _ 7 _ ED7) in Hc by (destruct (lc_sys tv); lia).
  rewrite U_lit in Hc by lia.
  assert (Hsys : lc_sys tv = true) by (destruct (lc_sys tv); [reflexivity | discriminate Hc]).
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK YC1i.Bspan LO_WANT.
  { fd_awr_ro. }
  fd_md. fd_norm HS HJ SHOK. fd_low HS ED HEX.
  assert (Hat0 : True) by exact I.
  fd_want_leaf HS HEX HT1 HJ HC1 HAt RDW Q25 Q21 Hsys Hat0 (TW.g_nq (tg_B2 tv)) rg1.
Qed.

(* the exit +0x1190 at the end of a run: s9 holds at mod 2 ^ 32 *)
Ltac fd_x_leaf HP HB HS HEX HT HJ HC KR0 KRA HAt Hatr EB14 EB17 R7 R13 R21 i rg1 kq :=
  lazymatch goal with |- SRr _ _ (mkCfg (?mk ?rgF ?pcx ?mm ?rom) ?mdF) _ =>
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msr =>
  lazymatch type of HT with @lc_tag_common _ _ _ ?cx ?op ?B1 ?ly ?S ?W ?rg ?mem ?md ?e =>
    let HAE := fresh "HAE" in let KRB := fresh "KRB" in
    fd_hae HEX HAE rg1 kq Ex;
    assert (KRB : forall r, In r FD_KT -> YK11.getr rgF r = YK11.getr rg1 r)
      by (exact (regs_kept_of_st_ok_pi Ex ssx msr rg1 _ FD_KT HS HAE ltac:(vm_compute; reflexivity)));
    eapply (fd_tail HP cx op B1 ly S W rgF mem mdF e _ _ HB
      (fd_tag_kept cx op B1 ly S W rg rgF mem md mdF e HT (conj HJ (proj2 HC))
        (KR0 rgF (fun r Hr => KRB r (in_or_app _ _ _ (or_introl Hr))))));
    [ exact HAt | exact Hatr
    | fd_rv HS;
      first [ apply (fd_soffk _ _ _ i); [rewrite HEX by lia; exact EB14 | lia | rewrite Z.mod_small by lia; lia]
            | apply (fd_soffk _ _ _ (2 ^ 32 - 1)); [rewrite HEX by lia; exact EB17 | lia | reflexivity] ]
    | rewrite KRB by fd_in; rewrite KRA by fd_in; exact R7
    | rewrite KRB by fd_in; rewrite KRA by fd_in; exact R21
    | rewrite KRB by fd_in; rewrite KRA by fd_in; exact R13 ]
  end end end.

(* the cut FIND at turn i + 1 at the end of a run *)
Ltac fd_find_leaf HS HEX HT HJ HC KR0 KRA Hco Hlt EC1 Hfa1 EB10 EB14 EB15 EB16 R7 R12 R13 R17 R21 i rg1 kq :=
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
    | fd_rv HS; apply (fd_soffk _ _ _ (TB_g_q + 4 * i)); [rewrite HEX by lia; exact EB10 | unfold TB_g_q; lia | lia]
    | fd_rv HS; apply (fd_soffk _ _ _ (TB_g_q + 4 * i)); [rewrite HEX by lia; exact EB16 | unfold TB_g_q; lia | lia]
    | fd_rv HS; apply (fd_soffk _ _ _ i); [rewrite HEX by lia; exact EB14 | lia | lia]
    | fd_rv HS; apply (fd_soffk _ _ _ (i + 1)); [rewrite HEX by lia; exact EB15 | lia | lia]
    | rewrite KRB by fd_in; rewrite KRA by fd_in; exact R13
    | rewrite KRB by fd_in; rewrite KRA by fd_in; exact R17
    | rewrite KRB by fd_in; rewrite KRA by fd_in; exact R12
    | rewrite KRB by fd_in; rewrite KRA by fd_in; exact R7
    | rewrite KRB by fd_in; rewrite KRA by fd_in; exact R21 ]
  end end end.

Lemma lc_op4find_ok : lc_op4find_stmt B MT XL RLO RHI.
Proof.
unfold lc_op4find_stmt.
intros HP cx op i W' c' HB HF.
destruct HF as (ly' & S' & regs & mem & md & e & B1 & HF). cbv zeta in HF.
destruct HF as (-> & HT & Hco & Hi & HiC & Hfa & R10 & R16 & R14 & R15 & R13 & R17 & R12 & R7 & R21).
pose proof HT as HT0. unfold lc_tag_common in HT0. cbv zeta in HT0.
destruct HT0 as (Hopc & HL & Hob & Hraw & Hser & Htw & _ & _ & _ & _ & _ & R24 & R27 & R20 & R23).
destruct HL as (HC & (R18 & R26) & Hsp & _ & Hok & _ & _ & R19).
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
pose proof (lp_laws B MT XL RLO RHI HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned B MT XL RLO RHI HP)) as HGX.
pose proof (lp_settle_cells B MT XL RLO RHI HP) as (_ & _ & HZq & HZc).
destruct (lc_geom B MT XL RLO RHI cx ly' S' W' regs mem md e HB HC) as [HAR _ Hstk Hsp1c _ _ _ _ _].
pose proof HC as (HJ & _ & _ & _ & _ & _ & R9 & R3 & R4 & Hsp1r & _).
destruct (fd_entry_a (fx := l_fx cx) ly' S' W' regs mem md i Bw HZq HAR R10 R16 R15 R23 R27 R26 Hi1024 Hq1024 Htw)
  as (HS & SHOK).
change (fd_EA regs (TW.Q_at Bw i)) with (fd_EA regs q) in HS, SHOK.
set (EA := fd_EA regs q) in HS, SHOK.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (HEI : img_env (@pa_val _ transportb_listing PI_transportb) A_LIM Ex) by (unfold EA, fd_EA; apply Eimg_env) end.
pose proof (@paj_run_x (l_fx cx) rc YE2k.tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
pose proof (@paj_run_to_x (l_fx cx) rc YE2k.tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := l_fx cx) (PI := PI_transportb)) as BR.
unfold lc_cfg. rewrite <- fd_pc.
paj_run_tok RUN HS HJ SHOK YC1i.Bspan.
{ fd_awr_ro. }
fd_md. fd_norm HS HJ SHOK. fd_low HS EA HEXA.
assert (EAr : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew EA n = YK11.getr regs r)
  by (intros n r Hn; unfold EA, fd_EA; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EA32 : ew EA 32 = w64 q)
  by (unfold EA, fd_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (EA27 : ew EA 27 = w64 TB_g_cmd) by (rewrite (EAr 27%nat 27%bv eq_refl); exact R27).
psrr_branch_tok RUN BR HS SHOK YC1i.Bspan.
{ exfalso. rewrite (fd_ovf _ q) in Hc; [discriminate Hc | rewrite HEXA by lia; assumption | rewrite HEXA by lia; assumption | lia]. }
clear Hc HEXA.
paj_run_to_tok RUNTO HS HJ SHOK YC1i.Bspan FD_O_KEY.
{ fd_awr_ro. }
fd_md. fd_norm HS HJ SHOK. fd_low HS EA HEXA.
lazymatch type of HS with context [ms_regs ?m] => set (rg1 := ms_regs m) in * end.
assert (KRA : forall r, In r FD_KA -> YK11.getr rg1 r = YK11.getr regs r).
{ lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msr =>
    assert (HAE : env_agree 32 (Ereg regs [w64 q]) Ex)
      by (split; [intros nn Hnn; rewrite (HEXA nn) by lia; unfold EA, fd_EA; apply Eimg_low; unfold A_TEXT; lia
                 | reflexivity]);
    exact (regs_kept_of_st_ok_pi Ex ssx msr regs [w64 q] FD_KA HS HAE ltac:(vm_compute; reflexivity)) end. }
assert (A11 : YK11.getr rg1 11 = w64 (TB_g_cmd + 4 + 40 * q)).
{ fd_rv HS. apply fd_addr;
    [rewrite HEXA by lia; exact EA27 | rewrite HEXA by lia; exact EA32 | unfold TB_g_cmd; lia | lia]. }
assert (A9 : YK11.getr rg1 9 = w64 (lc_sp1 cx)) by (rewrite KRA by fd_in; exact R9).
assert (A20 : YK11.getr rg1 20 = w64 (lc_F cx + 32)) by (rewrite KRA by fd_in; exact R20).
assert (A26 : YK11.getr rg1 26 = w64 SHADOW_OFF) by (rewrite KRA by fd_in; exact R26).
assert (Hsl : rdword (aview segs (w_H W') mem) (lc_sp1 cx + 144) = Some (lc_F cx + 32)).
{ unfold lc_spills in Hsp. rewrite Forall_forall in Hsp. apply (Hsp (144, lc_F cx + 32)).
  unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm. cbn [app]. fd_in. }
assert (Hsp1b : 2 ^ 40 <= lc_sp1 cx <= 2 ^ 47).
{ pose proof YM05.alloc_ceiling_value as Hac. destruct Hstk as (_ & _ & H0 & H47). unfold LF_FRAME in Hsp1r. lia. }
assert (HFr : 0 <= lc_F cx + 32 < 2 ^ 64).
{ pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF4096 & _ & HFceil & _).
  pose proof YM05.alloc_ceiling_lt. unfold LF_FBYTES in HFceil. lia. }
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARw.
destruct (fd_entry_b (fx := l_fx cx) ly' S' W' rg1 mem _ q (lc_sp1 cx) (lc_F cx + 32) Bw HZc HARw A11 A9 A20 A26
  Hq1024 Hsp1b HFr Hsl Htw) as (HSb & SHOKb).
clear HS SHOK HEI HEXA. rename HSb into HS, SHOKb into SHOK. unfold FD_O_KEY in HS.
set (EB := fd_EB rg1 (TW.Cmd_key Bw q)) in HS, SHOK.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (HEI : img_env (@pa_val _ transportb_listing PI_transportb) A_LIM Ex) by (unfold EB, fd_EB; apply Eimg_env) end.
assert (EBr : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew EB n = YK11.getr rg1 r)
  by (intros n r Hn; unfold EB, fd_EB; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EB32 : ew EB 32 = w64 (TW.Cmd_key Bw q))
  by (unfold EB, fd_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rg1 _ 0)).
assert (EB7 : ew EB 7 = w64 (if lc_sys tv then 1 else 0)) by (rewrite (EBr 7%nat 7%bv eq_refl), KRA by fd_in; exact R7).
assert (EB10 : ew EB 10 = w64 (TB_g_q + 4 * i)) by (rewrite (EBr 10%nat 10%bv eq_refl), KRA by fd_in; exact R10).
assert (EB12 : ew EB 12 = w64 key) by (rewrite (EBr 12%nat 12%bv eq_refl), KRA by fd_in; exact R12).
assert (EB13 : ew EB 13 = w64 (TW.g_nq Bw)) by (rewrite (EBr 13%nat 13%bv eq_refl), KRA by fd_in; exact R13).
assert (EB14 : ew EB 14 = w64 i) by (rewrite (EBr 14%nat 14%bv eq_refl), KRA by fd_in; exact R14).
assert (EB15 : ew EB 15 = w64 (i + 1)) by (rewrite (EBr 15%nat 15%bv eq_refl), KRA by fd_in; exact R15).
assert (EB16 : ew EB 16 = w64 (TB_g_q + 4 * i)) by (rewrite (EBr 16%nat 16%bv eq_refl), KRA by fd_in; exact R16).
assert (EB17 : ew EB 17 = w64 (2 ^ 32 - 1)) by (rewrite (EBr 17%nat 17%bv eq_refl), KRA by fd_in; exact R17).
assert (KR0 : forall rgF, (forall r, In r FD_KEEP -> YK11.getr rgF r = YK11.getr rg1 r) ->
  forall r, In r FD_KEEP -> YK11.getr rgF r = YK11.getr regs r).
{ intros rgF KRB r Hr. rewrite (KRB r Hr). apply KRA. unfold FD_KA. apply in_or_app. left. exact Hr. }
(* +0x1224 .. +0x123c: the check of the key's shadow, a1 = g_cmd[g_q[i]].key, s9 = i, `beq a1, a2` *)
paj_run_tok RUN HS HJ SHOK YC1i.Bspan.
{ fd_awr_ro. }
fd_md. fd_norm HS HJ SHOK. fd_low HS EB HEX.
psrr_branch_tok RUN BR HS SHOK YC1i.Bspan.
- (* the key matches: at = i *)
  rewrite branch_eq_U, (U_atom _ 32 (TW.Cmd_key Bw q)), (U_atom _ 12 key) in Hc
    by (first [rewrite HEX by lia; assumption | lia]).
  rewrite Hc in HF0. injection HF0 as Hat. subst at_. clear Hc HEX.
  assert (Hatr : i = -1 \/ 0 <= i < TC.CMDS_MAX) by (right; lia).
  (* +0x1244 .. +0x1248: s4 reloaded, `bgeu a5, a3` *)
  paj_run_tok RUN HS HJ SHOK YC1i.Bspan.
  { fd_awr_ro. }
  fd_md. fd_norm HS HJ SHOK. fd_low HS EB HEX.
  psrr_branch_tok RUN BR HS SHOK YC1i.Bspan.
  + (* i + 1 >= g_nq: the exit *)
    clear Hc HEX.
    paj_run_to_tok RUNTO HS HJ SHOK YC1i.Bspan LO_X.
    { fd_awr_ro. }
    fd_md. fd_norm HS HJ SHOK. fd_low HS EB HEX.
    fd_x_leaf HP HB HS HEX HT HJ HC KR0 KRA HAt Hatr EB14 EB17 R7 R13 R21 i rg1 (TW.Cmd_key Bw q).
  + (* i + 1 < g_nq: `bltz` on s9 = i (not taken), then the exit *)
    clear Hc HEX.
    paj_run_tok RUN HS HJ SHOK YC1i.Bspan.
    { fd_awr_ro. }
    fd_md. fd_norm HS HJ SHOK. fd_low HS EB HEX.
    psrr_branch_tok RUN BR HS SHOK YC1i.Bspan.
    * exfalso. rewrite fd_br_lt, (fd_sextw _ 14 i), fd_sg0 in Hc by (first [rewrite HEX by lia; assumption | lia]).
      rewrite (Z.mod_small (i + 2 ^ 31) (2 ^ 32)) in Hc by lia. apply Z.ltb_lt in Hc. lia.
    * clear Hc HEX.
      paj_run_to_tok RUNTO HS HJ SHOK YC1i.Bspan LO_X.
      { fd_awr_ro. }
      fd_md. fd_norm HS HJ SHOK. fd_low HS EB HEX.
      fd_x_leaf HP HB HS HEX HT HJ HC KR0 KRA HAt Hatr EB14 EB17 R7 R13 R21 i rg1 (TW.Cmd_key Bw q).
- (* the key differs: the search goes on at i + 1 *)
  rewrite branch_eq_U, (U_atom _ 32 (TW.Cmd_key Bw q)), (U_atom _ 12 key) in Hc
    by (first [rewrite HEX by lia; assumption | lia]).
  rewrite Hc in HF0. rename Hc into Hkey. clear HEX.
  assert (Hf1 : f = S (f - 1)) by (unfold f, TC.CMDS_MAX in *; lia).
  (* +0x1240 .. +0x1248: s9 = a7, s4 reloaded, `bgeu a5, a3` *)
  paj_run_tok RUN HS HJ SHOK YC1i.Bspan.
  { fd_awr_ro. }
  fd_md. fd_norm HS HJ SHOK. fd_low HS EB HEX.
  psrr_branch_tok RUN BR HS SHOK YC1i.Bspan.
  + (* i + 1 >= g_nq: at = -1 *)
    rewrite branch_geu_U, (U_atom _ 15 (i + 1)), (U_atom _ 13 (TW.g_nq Bw)) in Hc
      by (first [rewrite HEX by lia; assumption | lia]).
    apply negb_true_iff, Z.ltb_ge in Hc.
    rewrite Hf1, fd_find_step, (proj2 (Z.ltb_ge (i + 1) (TW.g_nq Bw)) Hc) in HF0.
    injection HF0 as Hat. subst at_. clear Hc HEX.
    assert (Hatr : -1 = -1 \/ 0 <= -1 < TC.CMDS_MAX) by (left; reflexivity).
    paj_run_to_tok RUNTO HS HJ SHOK YC1i.Bspan LO_X.
    { fd_awr_ro. }
    fd_md. fd_norm HS HJ SHOK. fd_low HS EB HEX.
    fd_x_leaf HP HB HS HEX HT HJ HC KR0 KRA HAt Hatr EB14 EB17 R7 R13 R21 i rg1 (TW.Cmd_key Bw q).
  + (* i + 1 < g_nq: `bltz` on a7 sign-extended (taken), back to the head at i + 1 *)
    rewrite branch_geu_U, (U_atom _ 15 (i + 1)), (U_atom _ 13 (TW.g_nq Bw)) in Hc
      by (first [rewrite HEX by lia; assumption | lia]).
    apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hlt. clear HEX.
    rewrite Hf1, fd_find_step, (proj2 (Z.ltb_lt (i + 1) (TW.g_nq Bw)) Hlt) in HF0.
    destruct (TC.CMDS_MAX <=? i + 1) eqn:EC1 in HF0; [discriminate HF0|]. apply Z.leb_gt in EC1.
    assert (Hfa1 : TOP.submit_find_at (S (Z.to_nat TC.CMDS_MAX)) Bw key 0 =
                   TOP.submit_find_at (S (Z.to_nat TC.CMDS_MAX) - Z.to_nat (i + 1)) Bw key (i + 1)).
    { rewrite Hfa. replace (S (Z.to_nat TC.CMDS_MAX) - Z.to_nat i)%nat with (S f) by (unfold f, TC.CMDS_MAX in *; lia).
      rewrite fd_find_step, (proj2 (Z.ltb_lt i (TW.g_nq Bw)) (proj2 Hi)), (proj2 (Z.leb_gt TC.CMDS_MAX i) HiC).
      change (TW.Q_at Bw i) with q. rewrite (proj2 (Z.leb_gt TC.CMDS_MAX q) EQ), Hkey.
      f_equal. unfold f, TC.CMDS_MAX in *. lia. }
    paj_run_tok RUN HS HJ SHOK YC1i.Bspan.
    { fd_awr_ro. }
    fd_md. fd_norm HS HJ SHOK. fd_low HS EB HEX.
    psrr_branch_tok RUN BR HS SHOK YC1i.Bspan.
    * clear HEX.
      paj_run_to_tok RUNTO HS HJ SHOK YC1i.Bspan LO_FIND.
      { fd_awr_ro. }
      fd_md. fd_norm HS HJ SHOK. fd_low HS EB HEX.
      fd_find_leaf HS HEX HT HJ HC KR0 KRA Hco Hlt EC1 Hfa1 EB10 EB14 EB15 EB16 R7 R12 R13 R17 R21 i rg1
        (TW.Cmd_key Bw q).
    * exfalso. rewrite fd_br_lt, (fd_sextw _ 17 (2 ^ 32 - 1)), fd_sg0 in Hc
        by (first [rewrite HEX by lia; assumption | lia]).
      vm_compute in Hc. discriminate Hc.
Qed.
End fd.
