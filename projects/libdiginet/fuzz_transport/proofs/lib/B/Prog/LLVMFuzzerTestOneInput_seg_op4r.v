(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AFip.v (segA: the run of a
   wrapper over its own instruction table, the application of a runtime-entry contract at a call site and the
   rebuilding of the symbolic state after the call), A/AFis.v (at_ST's frame and window conjuncts,
   kept_of_frame, chunk_val_at) and A/AF0x.v (st_ok_pin_reg, the val_mem / apresent / fpchain helpers) to
   libreac/fuzz_decode's calloc wrapper in image A (fuzz_decode.asan); module paths changed, and every address,
   cell and offset below is decode's own. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/DecodeCallocWrap.v, with its module paths and module names changed; 3365 of its 3449 lines of code are new or changed and 788 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/LLVMFuzzerTestOneInput_seg_cfg.v, with its module paths and module names changed; 1064 of its 1161 lines of code are new or changed and 3352 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_op4r: Lemma lc_op4r_ok : lc_op4r_stmt (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v), the
   raw arm of op 4 of LLVMFuzzerTestOneInput in fuzz_transport.asan-ubsan, offsets +0x12bc .. +0x1344 of the listing
   lib/B/Prog/DgnTransportBList.v (0x8255c .. 0x825e4), from the cut SUBR to the cut S4.

   What the code does (at SUBR a1 holds the u16 w, s8 / s7 the cursor after it, s5 the queue length before).
     +0x12bc .. +0x12f0  w mod 25 by the compiler's multiply by 18351 and its shifts, `and` with 0xffff (the spill
                         slot at s1 + 120);
     +0x12f4 .. +0x12fc  `bltu a2, s7`: the take's min with the bytes left (t = a2);
     +0x1300             `bltu a0, a2` with a0 = the bitwise not of s8, the UBSan test of the take's end: not taken,
                         since s8 < 2 ^ 47 and t <= 24, so the trap word +0x1b44 (0x82de4) is not reached;
     +0x1304 .. +0x130c  s9 = s5, s5 = s8 + t, s11 = s7 - t;
     +0x1310 .. +0x1318  `sb a2, 24(s4)` (c.len = t, a byte of the class-2 frame), a0 = c, a1 = s8;
     +0x131c             the call of __asan_memcpy (c, the input bytes at the cursor, t);
     +0x1320 .. +0x1328  a0 = &g_s, a1 = c;
     +0x132c             the call of diginet_session_submit (a G-form callee, the same G journal);
     +0x1330 .. +0x1338  a1 = its result, a0 = c, a2 = s9 (the queue length before);
     +0x133c             the call of check_refusal_submit (a leaf);
     +0x1340 .. +0x1344  s8 = s5, `j` to the settle call at +0x1654 (S4).

   How it is proved. Runs of lib/A/Prog/PaShadow.v's token engine over the walk's own G journal
   (lib/B/Prog/TransportGRunB.v paj_run_x / paj_run_to_x, write obligation lib/A/W_journalG.v awr_ok_x), the memcpy
   through lib/A/Prog/TransportGCg.v gx_intrin_at, diginet_session_submit by its statement lp_submit, and
   check_refusal_submit through gx_call_leaf and lib/B/Prog/DgnTransportBLeafb.v decode_leafb_journal. The take's
   arithmetic is decided at the valuation (o4r_take_den: the multiply and the shifts give w mod 25 for every u16 w),
   the `bltu` of +0x12f4 is split (o4r_rv_eq names the take on each side) and the UBSan branch of +0x1300 is refuted
   from the cursor's bounds. The model's Some of the operation comes from TSim/LoopOk.v op_ok at the start facts
   lc_opok (the stream fun _ => 1: op 4 receives nothing), read through LLVMFuzzerTestOneInput_st.v lc_op4_eq,
   lc_submit_raw_eq and lc_raw_vals_eq; settle keeps its world (lc_settle_world). The core is carried across the
   store and the memcpy (the frame's bytes change only in c) by LLVMFuzzerTestOneInput_st.v lc_core_kept_run, and
   from the cut after the memcpy to S4 by the call kit of LLVMFuzzerTestOneInput_seg_op4sub.v (o4s_inv,
   o4s_inv_kept7 over lc_core_kept, o4s_leaf, o4s_c_ok, o4s_entry0, o4s_tw_csw, o4s_rng_hull, o4s_submit_rc). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop YO09 YE00 YE01 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaBase PaTable PaSym PaStep PaRun
  PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0 YCfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBCg TransportGRwB TransportGRunB DgnTransportBLeafb DgnTransportBCgRun.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg diginet_session_submit_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require
  LeafCgKit AsanKA check_refusal_submit_cg check_refusal_submit_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st LLVMFuzzerTestOneInput_seg_op4sub.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TImg TCb TSess0 TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Agree QueueFacts LoopOk LinksProof.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module AG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.Agree.
Module QF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.QueueFacts.
Module LOK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.LoopOk.
Module LP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.LinksProof.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LeafCgKit.
Module AKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.AsanKA.
Module LCRS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_refusal_submit_cg.
Module LCRSc := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_refusal_submit_c.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 0. The two inner pcs of the segment and its symbolic states         *)
(* ------------------------------------------------------------------ *)

(* +0x1310, the store of the length byte (its own symbolic state: the byte of c it writes is a region), and +0x1320,
   the return of __asan_memcpy. *)
Definition O4R_STORE : Z := 0x1310.
Definition O4R_CPY : Z := 0x1320.

(* The spill slot 120(s1) (the constant 0xffff the `and` of +0x12f0 reads), as atom 32 (s1 is atom 9). *)
Definition o4r_rgL : YP09.region := YP09.mkRegion (Some 9%nat) 120 128 0 0 [YP09.mkChunk 120 (CVal 8 (SOff 32 0))].
(* +0x12bc: a1 = w (atom 11, a u16), s7 = the bytes left (atom 23), s8 = the cursor (atom 24). *)
Definition o4r_ssR : sstate := mkSS LO_SUBR sr_atoms [o4r_rgL] None
  (mkFacts [(32%nat, mkAF 65535 65535 0); (11%nat, mkAF 0 65535 0);
            (24%nat, mkAF 4096 140737488355300 0); (23%nat, mkAF 0 67108864 0)] [] []).
(* +0x1310 with the length byte of c (s4 + 24, atom 20) writable. *)
Definition o4r_rgS : YP09.region := YP09.mkRegion (Some 20%nat) 24 25 24 25 [].
Definition o4r_ssS : sstate :=
  mkSS O4R_STORE sr_atoms [o4r_rgS] None (mkFacts [(20%nat, mkAF 4096 140737488355328 0)] [] []).

(* ------------------------------------------------------------------ *)
(* 1. The take's arithmetic                                            *)
(* ------------------------------------------------------------------ *)

(* a2 at the `bltu` of +0x12f4, as the engine leaves it from a1 = w (atom 11) and the spill slot 0xffff (atom 32):
   (w mod 25) & 0xffff, by the multiply by 18351 and the shifts of +0x12bc .. +0x12f0. *)
Definition o4r_W : sv := SOff 11 0.
Definition o4r_Q : sv := SAlu ALU_SRL (SMd M_MUL o4r_W (SLit 18351)) (SLit 16).
Definition o4r_TAKE : sv :=
  SAlu ALU_AND
    (SAlu ALU_SUB o4r_W
       (SMd M_MUL
          (SAlu ALU_SRL
             (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_SUB o4r_W o4r_Q) (SLit 48)) (SLit 49)) o4r_Q)
             (SLit 4))
          (SLit 25)))
    (SOff 32 0).

Definition o4r_Ew (w : Z) : env :=
  mkEnv (fun n => if (n =? 11)%nat then Z_to_bv 64 w else Z_to_bv 64 65535) (fun _ => []).
Definition o4r_take_chk : bool :=
  forallb (fun w => Z.eqb (bv_unsigned (sv_denot (o4r_Ew w) o4r_TAKE)) (w mod 25)) (map Z.of_nat (seq 0 65536)).
Lemma o4r_take_chk_ok : o4r_take_chk = true.
Proof. vm_compute. reflexivity. Qed.

Lemma o4r_take_den : forall (E : env) w,
  ew E 11 = Z_to_bv 64 w -> ew E 32 = Z_to_bv 64 65535 -> 0 <= w < 65536 ->
  sv_denot E o4r_TAKE = Z_to_bv 64 (w mod 25).
Proof.
intros E w H11 H32 Hw.
assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
pose proof (Z.mod_pos_bound w 25 ltac:(lia)) as M.
assert (Eq : sv_denot E o4r_TAKE = sv_denot (o4r_Ew w) o4r_TAKE).
{ unfold o4r_TAKE, o4r_Q, o4r_W. cbn [sv_denot ew o4r_Ew Nat.eqb]. rewrite H11, H32. reflexivity. }
assert (Hv : bv_unsigned (sv_denot (o4r_Ew w) o4r_TAKE) = w mod 25).
{ pose proof o4r_take_chk_ok as K. unfold o4r_take_chk in K. rewrite forallb_forall in K.
  assert (Iw : In w (map Z.of_nat (seq 0 65536))).
  { apply in_map_iff. exists (Z.to_nat w). split; [apply Z2Nat.id; lia|].
    apply in_seq. split; [apply Nat.le_0_l|].
    assert (HH : (Z.to_nat w < Z.to_nat 65536)%nat)
      by (apply (proj1 (Z2Nat.inj_lt w 65536 ltac:(lia) ltac:(lia))); lia).
    change (Z.to_nat 65536) with 65536%nat in HH. change (0 + 65536)%nat with 65536%nat. exact HH. }
  specialize (K w Iw). apply Z.eqb_eq in K. exact K. }
rewrite Eq. apply bv_eq. rewrite Hv, Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with 18446744073709551616.
rewrite (Z.mod_small (w mod 25)) by lia. reflexivity.
Qed.

(* The unsigned value of a2 at +0x12f4. *)
Lemma o4r_U_take : forall (E : env) w,
  ew E 11 = Z_to_bv 64 w -> ew E 32 = Z_to_bv 64 65535 -> 0 <= w < 65536 ->
  U E o4r_TAKE = w mod 25.
Proof.
intros E w H11 H32 Hw.
pose proof (Z.mod_pos_bound w 25 ltac:(lia)) as M.
unfold U. rewrite (o4r_take_den E w H11 H32 Hw).
apply unsigned_lit_small. change (2 ^ 64) with 18446744073709551616. lia.
Qed.

(* The branch of +0x12f4: the take's min with the bytes left. *)
Lemma o4r_br_take : forall (E : env) w n4,
  ew E 11 = Z_to_bv 64 w -> ew E 32 = Z_to_bv 64 65535 -> ew E 23 = Z_to_bv 64 n4 ->
  0 <= w < 65536 -> 0 <= n4 < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E o4r_TAKE) (sv_denot E (SOff 23 0)) = (w mod 25 <? n4).
Proof.
intros E w n4 H11 H32 H23 Hw Hn.
rewrite branch_ltu_U, (o4r_U_take E w H11 H32 Hw), (U_atom E 23 n4 H23 Hn). reflexivity.
Qed.

(* The UBSan branch of +0x1300 (a0 = the bitwise not of s8): never taken, since the cursor is below 2 ^ 47 and the
   take is at most 24 (or the bytes left, below 2 ^ 26). *)
Lemma o4r_br_trap : forall (E : env) q (a : sv) (v : Z),
  ew E 24 = Z_to_bv 64 q -> 4096 <= q <= 140737488355300 -> U E a = v -> 0 <= v <= 67108864 ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_XOR (SOff 24 0) (SLit (-1)))) (sv_denot E a) = false.
Proof.
intros E q a v H24 Hq HU Hv.
rewrite branch_ltu_U, (U_not E 24 q H24 ltac:(change (2 ^ 64) with 18446744073709551616; lia)), HU.
apply Z.ltb_ge. change (2 ^ 64) with 18446744073709551616. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The model                                                        *)
(* ------------------------------------------------------------------ *)

(* The cursor: the three bytes of lc_sub_kd keep it in range. *)
Lemma o4r_kd_ok : forall D c1, QF.fuzz_in_ok D c1 -> QF.fuzz_in_ok D (sv_c (lc_sub_kd D c1)).
Proof.
intros D c1 H. unfold lc_sub_kd.
destruct (QF.fuzz_u8_ok D c1 H) as (c1' & kb & E1 & H1 & _). rewrite E1.
destruct (QF.fuzz_u8_ok D c1' H1) as (c2 & ab & E2 & H2 & _). rewrite E2.
destruct (QF.fuzz_u8_ok D c2 H2) as (c3 & db & E3 & H3 & _). rewrite E3. exact H3.
Qed.

Lemma o4r_oc_ok : forall D c0, QF.fuzz_in_ok D c0 -> QF.fuzz_in_ok D (lc_oc D c0).
Proof.
intros D c0 H. unfold lc_oc. destruct (QF.fuzz_u8_ok D c0 H) as (c1 & v & E1 & H1 & _). rewrite E1. exact H1.
Qed.

(* The u16 the cut SUBR holds in a1, and the cursor after it. *)
Lemma o4r_w_ok : forall D c3, QF.fuzz_in_ok D c3 ->
  0 <= lc_raw_w D c3 < 65536 /\ QF.fuzz_in_ok D (lc_raw_c4 D c3).
Proof.
intros D c3 H. unfold lc_raw_w, lc_raw_c4.
destruct (QF.fuzz_u16_ok D c3 H) as (c4 & w & E & H4 & Hw). rewrite E. cbn [fst snd]. split; [exact Hw | exact H4].
Qed.

(* The raw arm's take: from the u16 and the cursor after it, t and the cursor after the take. *)
Lemma o4r_rv_eq : forall D c3 t, QF.fuzz_in_ok D c3 ->
  t = (if lc_raw_w D c3 mod 25 <? TOP.fi_n (lc_raw_c4 D c3) then lc_raw_w D c3 mod 25
       else TOP.fi_n (lc_raw_c4 D c3)) ->
  lc_raw_vals D c3 = mkLrw t (TOP.fi_off (lc_raw_c4 D c3)) t
    (TOP.FuzzIn (TOP.fi_off (lc_raw_c4 D c3) + t) (TOP.fi_n (lc_raw_c4 D c3) - t)).
Proof.
intros D c3 t Hc Ht.
destruct (o4r_w_ok D c3 Hc) as (Hw & Hc4). destruct Hc4 as (Ho4 & Hn4 & _).
pose proof (Z.mod_pos_bound (lc_raw_w D c3) 25 ltac:(lia)) as Hm.
assert (Ht0 : 0 <= t <= 24).
{ rewrite Ht. destruct (lc_raw_w D c3 mod 25 <? TOP.fi_n (lc_raw_c4 D c3)) eqn:E;
    [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; lia. }
rewrite lc_raw_vals_eq. unfold TOP.fuzz_take_m. change (DSpec.SPEC_CMD_MAX + 1) with 25.
cbv beta iota zeta. rewrite <- Ht.
rewrite (Z.mod_small t (2 ^ 8)) by (change (2 ^ 8) with 256; lia). reflexivity.
Qed.

(* The raw arm's model steps, from the Some LoopOk.op_ok gives at the start facts: diginet_session_submit,
   check_refusal_submit and settle 0 (which keeps its world), and the operation's equation at every stream. *)
Lemma o4r_model : forall (D B0 B1 : list byte) (c0 : TOP.fuzz_in) (ops : Z) (k0 : nat),
  AG.agree timg_B ops B0 -> 0 <= ops < TC.OPS_MAX -> QF.fuzz_in_ok D c0 -> TOP.fi_n c0 <> 0 ->
  Z.of_nat k0 <= ops -> lc_opc D c0 = 4 -> TC.op_begin_m B0 = Some (B1, tt) -> TW.g_raw B1 <> 0 ->
  let kd := lc_sub_kd D (lc_oc D c0) in
  let rv := lc_raw_vals D (sv_c kd) in
  let cs := lc_raw_cs D rv (sv_display kd) (sv_key kd) in
  exists B2 r B3, TS0.diginet_session_submit_m B1 cs = Some (B2, r) /\
    TC.check_refusal_submit_m B2 cs r (TW.S_queued B0) = Some (B3, tt) /\
    TC.settle_m B3 0 = Some (B3, tt) /\
    (forall A, TOP.LLVMFuzzerTestOneInput_op_m timg_B B0 A D c0 k0 = Some (B3, (rw_c rv, k0))).
Proof.
intros D B0 B1 c0 ops k0 HA Hops Hc Hn Hk Ho HOB HR kd rv cs.
destruct (LOK.op_ok LP.links_holds timg_B ops B0 (fun _ => 1) D c0 k0 HA Hops Hc Hn ltac:(lia) ltac:(lia))
  as (Bx & cx & kx & E & _).
rewrite (lc_op4_eq timg_B B0 (fun _ => 1) D c0 k0 Ho), (lc_submit_raw_eq B0 B1 D (lc_oc D c0) HOB HR) in E.
cbv zeta in E. fold kd rv cs in E.
destruct (TS0.diginet_session_submit_m B1 cs) as [[B2 r]|] eqn:E2; [|discriminate E].
destruct (TC.check_refusal_submit_m B2 cs r (TW.S_queued B0)) as [[B3 u3]|] eqn:E3; [|discriminate E].
destruct (TC.settle_m B3 0) as [[B4 u4]|] eqn:E4; [|discriminate E].
pose proof (lc_settle_world B3 B4 0 u4 E4) as EB. subst B4. destruct u3, u4.
exists B2, r, B3. split; [first [exact E2 | reflexivity]|]. split; [exact E3|]. split; [exact E4|].
intros A. rewrite (lc_op4_eq timg_B B0 A D c0 k0 Ho), (lc_submit_raw_eq B0 B1 D (lc_oc D c0) HOB HR).
cbv zeta. fold kd rv cs. rewrite E2, E3, E4. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. Bytes and the command struct                                     *)
(* ------------------------------------------------------------------ *)

Lemma o4r_le1 : forall v, 0 <= v < 256 -> le_byte v 1 0 = v.
Proof.
intros v Hv. unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma o4r_aview_vm1 : forall (H : word -> bool) (m : word -> option byte) a v,
  val_mem tfibsegs (mrestrict H m) a 1 v -> 0 <= v < 256 -> aview tfibsegs H m a = Some v.
Proof.
intros H m a v V Hv. specialize (V 0%nat ltac:(lia)). cbn [Z.of_nat] in V. rewrite Z.add_0_r in V.
unfold aview. rewrite V. cbn [option_map]. f_equal. rewrite o4r_le1 by exact Hv.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hv.
Qed.

Lemma o4r_garr8_aview : forall (H : word -> bool) (m : word -> option byte) base (l : list Z) j,
  garr8 tfibsegs (mrestrict H m) base l -> (j < length l)%nat ->
  aview tfibsegs H m (base + Z.of_nat j) = Some (nth j l 0).
Proof. intros H m base l j HG Hj. destruct (HG j Hj) as [V R]. exact (o4r_aview_vm1 H m _ _ V R). Qed.

Lemma o4r_garr8_of : forall (H : word -> bool) (m : word -> option byte) base (l : list Z),
  (forall j, (j < length l)%nat ->
     aview tfibsegs H m (base + Z.of_nat j) = Some (nth j l 0) /\ 0 <= nth j l 0 < 256) ->
  garr8 tfibsegs (mrestrict H m) base l.
Proof.
intros H m base l HA j Hj. destruct (HA j Hj) as [E R]. split; [|exact R]. intros k Hk.
assert (Ek : k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold aview in E. destruct (mbyte tfibsegs (mrestrict H m) (base + Z.of_nat j)) as [b|] eqn:Eb;
  cbn [option_map] in E; [|discriminate E].
injection E as E. f_equal. rewrite o4r_le1 by exact R. apply bv_eq. rewrite Z_to_bv_unsigned, <- E.
unfold bv_wrap. symmetry. apply Z.mod_small. exact (bv_unsigned_in_range 8 b).
Qed.

Lemma o4r_nth_zs : forall (l : list byte) j, nth j (TW.zs l) 0 = bv_unsigned (nth j l (DSpec.b8 0)).
Proof.
intros l j. unfold TW.zs. rewrite <- (map_nth (fun b : byte => bv_unsigned b) l (DSpec.b8 0) j). reflexivity.
Qed.

Lemma o4r_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. exact R. Qed.

(* The struct the raw arm hands diginet_session_submit against the one op 4's prologue left in c: the input bytes
   below t, the length byte at 24, the same bytes elsewhere. *)
Lemma o4r_cs_shape : forall (D : list byte) off t display key, 0 <= off -> 0 <= t <= 24 ->
  off + t <= Z.of_nat (length D) ->
  let cs := TOP.cmd_struct (TW.sub D off (Z.to_nat t) ++ repeat (DSpec.b8 0) (Z.to_nat (24 - t))) t display key in
  let cs0 := TOP.cmd_struct (repeat (DSpec.b8 0) 24) 0 display key in
  length cs = 32%nat /\ length cs0 = 32%nat /\
  (forall j, (j < Z.to_nat t)%nat -> nth j cs (DSpec.b8 0) = nth (Z.to_nat off + j) D (DSpec.b8 0)) /\
  nth 24 cs (DSpec.b8 0) = DSpec.b8 t /\
  (forall j, (Z.to_nat t <= j < 32)%nat -> j <> 24%nat -> nth j cs (DSpec.b8 0) = nth j cs0 (DSpec.b8 0)).
Proof.
intros D off t display key Ho Ht Hl cs cs0.
assert (LS : length (TW.sub D off (Z.to_nat t)) = Z.to_nat t) by (apply TWL.length_sub; lia).
assert (LP : length (TW.put 4 key) = 4%nat) by (apply TWL.length_put).
assert (LH : length (TW.sub D off (Z.to_nat t) ++ repeat (DSpec.b8 0) (Z.to_nat (24 - t))) = 24%nat)
  by (rewrite length_app, LS, repeat_length; lia).
assert (LR : length (repeat (DSpec.b8 0) 24) = 24%nat) by apply repeat_length.
assert (LT : forall a b, length ([DSpec.b8 a; DSpec.b8 b; DSpec.b8 0; DSpec.b8 0] ++ TW.put 4 key) = 8%nat)
  by (intros a b; cbn [length app]; rewrite LP; reflexivity).
unfold cs, cs0, TOP.cmd_struct.
split; [rewrite length_app, LH, LT; reflexivity|].
split; [rewrite length_app, LR, LT; reflexivity|].
split.
{ intros j Hj. rewrite app_nth1 by (rewrite LH; lia). rewrite app_nth1 by (rewrite LS; lia).
  apply TWorldG.tw_nth_sub; lia. }
split.
{ rewrite app_nth2 by (rewrite LH; lia). rewrite LH. reflexivity. }
intros j Hj H24. destruct (Nat.lt_ge_cases j 24) as [Hlt | Hge].
- rewrite app_nth1 by (rewrite LH; lia). rewrite app_nth2 by (rewrite LS; lia). rewrite LS, nth_repeat.
  rewrite app_nth1 by (rewrite LR; lia). rewrite nth_repeat. reflexivity.
- rewrite app_nth2 by (rewrite LH; lia). rewrite (app_nth2 (repeat (DSpec.b8 0) 24)) by (rewrite LR; lia).
  rewrite LH, LR.
  destruct (j - 24)%nat as [|k] eqn:Ek; [lia|]. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The denotations the runs leave                                   *)
(* ------------------------------------------------------------------ *)

Lemma o4r_den_alu : forall (E : env) op a b, sv_denot E (SAlu op a b) = alu64 op (sv_denot E a) (sv_denot E b).
Proof. reflexivity. Qed.

Lemma o4r_den_off : forall (E : env) n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof.
intros E n v H Hv. cbn [sv_denot]. rewrite H. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
Qed.

Lemma o4r_add_den : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
intros a b. apply bv_eq. cbn [alu64 alu]. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma o4r_sub_den : forall a b, alu64 ALU_SUB (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof.
intros a b. apply bv_eq. cbn [alu64 alu]. rewrite bv_sub_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap. rewrite <- Zminus_mod. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 5. The segment                                                      *)
(* ------------------------------------------------------------------ *)

Section seg. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* +0x12bc with the spill slot 120(s1) read-only (atom 32) and the four atom bounds the run reads. *)
Lemma o4r_entryR : forall (fx : YK11.FPState) (W : world segs) regs mem s1 q n4 w,
  YK11.getr regs 9 = w64 s1 -> YK11.getr regs 11 = w64 w ->
  YK11.getr regs (Z_to_bv 5 23) = w64 n4 -> YK11.getr regs (Z_to_bv 5 24) = w64 q ->
  0 <= s1 -> s1 + 128 <= 2 ^ 64 -> 0 <= w < 65536 -> 0 <= n4 <= 67108864 -> 4096 <= q <= 140737488355300 ->
  rdword (aview segs (w_H W) mem) (s1 + 120) = Some 65535 ->
  st_ok_pi segs VAL (o4s_E regs [w64 65535]) o4r_ssR
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + LO_SUBR)) mem (YK11.seg_rom segs))).
Proof.
  intros fx W regs mem s1 q n4 w R9 R11 R23 R24 Hs0 Hs1 Hw Hn4 Hq Rv.
  assert (U9 : bv_unsigned (ew (o4s_E regs [w64 65535]) 9) = s1)
    by (rewrite (o4s_ew_reg regs _ 9 9%bv ltac:(lia) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (U11 : bv_unsigned (ew (o4s_E regs [w64 65535]) 11) = w)
    by (rewrite (o4s_ew_reg regs _ 11 11%bv ltac:(lia) eq_refl), R11; unfold w64; apply unsigned_lit_small; lia).
  assert (U23 : bv_unsigned (ew (o4s_E regs [w64 65535]) 23) = n4)
    by (rewrite (o4s_ew_reg regs _ 23 (Z_to_bv 5 23) ltac:(lia) eq_refl), R23; unfold w64;
        apply unsigned_lit_small; lia).
  assert (U24 : bv_unsigned (ew (o4s_E regs [w64 65535]) 24) = q)
    by (rewrite (o4s_ew_reg regs _ 24 (Z_to_bv 5 24) ltac:(lia) eq_refl), R24; unfold w64;
        apply unsigned_lit_small; lia).
  assert (X32 : ew (o4s_E regs [w64 65535]) 32 = w64 65535) by exact (o4s_ew_extra regs [w64 65535] 0 ltac:(lia)).
  assert (U32 : bv_unsigned (ew (o4s_E regs [w64 65535]) 32) = 65535)
    by (rewrite X32; unfold w64; apply unsigned_lit_small; lia).
  rewrite restrict_mkst_fx. unfold o4r_ssR.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold o4r_rgL, YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs _ _ s1 120 8 (SOff 32 0) 65535).
    + cbn [sv_denot]. rewrite X32, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    + cbn. lia.
    + cbn. lia.
    + apply val_mem_of_rdword. exact Rv.
  - exact (conj I I).
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite U32, U11, U24, U23. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; try exact I; lia.
Qed.

(* +0x1310 with the length byte of c (s4 + 24) writable. *)
Lemma o4r_entryS : forall (fx : YK11.FPState) (W : world segs) regs mem cp,
  YK11.getr regs (Z_to_bv 5 20) = w64 cp -> 4096 <= cp <= 140737488355328 ->
  writable_at segs (mrestrict (w_H W) mem) (cp + 24) ->
  st_ok_pi segs VAL (o4s_E regs []) o4r_ssS
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + O4R_STORE)) mem (YK11.seg_rom segs))).
Proof.
  intros fx W regs mem cp R20 Hc Hw.
  assert (U20 : bv_unsigned (ew (o4s_E regs []) 20) = cp)
    by (rewrite (o4s_ew_reg regs _ 20 (Z_to_bv 5 20) ltac:(lia) eq_refl), R20; unfold w64;
        apply unsigned_lit_small; lia).
  rewrite restrict_mkst_fx. unfold o4r_ssS.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold o4r_rgS, YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U20.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. replace (cp + o) with (cp + 24) by lia. exact Hw.
  - exact (conj I I).
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite U20. rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; try exact I; lia.
Qed.

(* The model's names for the raw arm of operation op of the call cx. *)
Definition o4r_kd (cx : lcx) (op : lop) : lsv := lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op)).
Definition o4r_rvw (cx : lcx) (op : lop) : lrw := lc_raw_vals (l_pl cx) (sv_c (o4r_kd cx op)).
Definition o4r_cs (cx : lcx) (op : lop) : list byte :=
  lc_raw_cs (l_pl cx) (o4r_rvw cx op) (sv_display (o4r_kd cx op)) (sv_key (o4r_kd cx op)).

(* The callee-saved registers the cut S4 names, carried over the two calls. *)
Definition o4r_rv (cx : lcx) (op : lop) : list (Z * word) :=
  [(25, w64 (bv_swrap 32 (TW.S_queued (lo_B op))));
   (21, w64 (l_p cx + TOP.fi_off (rw_c (o4r_rvw cx op))));
   (27, w64 (TOP.fi_n (rw_c (o4r_rvw cx op))));
   (20, w64 (lc_F cx + 32)); (22, w64 1)].
Lemma o4r_rv_ok : forall cx op x, In x (o4r_rv cx op) -> acallee_saved (fst x).
Proof.
  intros cx op x Hx. unfold o4r_rv in Hx. cbn [In] in Hx.
  repeat (destruct Hx as [<- | Hx]; [cbn [fst]; unfold acallee_saved; lia|]). destruct Hx.
Qed.
Lemma o4r_sl_ok : forall o : Z * Z, In o (@nil (Z * Z)) -> 0 <= fst o /\ fst o + 8 <= 216.
Proof. intros o Ho. destruct Ho. Qed.

(* +0x1320, the return of __asan_memcpy: c holds the struct, the world op_begin's B1, s9 the queue length before,
   s5 / s11 the cursor after the take, s4 = c, s6 = 1. *)
Definition o4r_st_cpy (cx : lcx) (op : lop) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' e B1,
    c' = lc_cfg cx O4R_CPY regs' mem' md' /\
    lc_opc (l_pl cx) (lo_c op) = 4 /\
    TC.op_begin_m (lo_B op) = Some (B1, tt) /\ TW.g_raw B1 <> 0 /\ lc_tw W' mem' B1 /\
    length (o4r_cs cx op) = 32%nat /\
    o4s_inv B MT cx op (o4r_cs cx op) [] (o4r_rv cx op) ly' S' W' regs' mem' md' e.

(* +0x12bc .. +0x131c: the take, the UBSan test of its end, the store of the length byte and the memcpy. *)
Lemma o4r_seg_a : lp_prem B MT XL RLO RHI -> forall (cx : lcx) (op : lop) (W : world segs) (c : config),
  lc_base B MT XL RLO RHI cx -> lc_st_subr B MT cx op W c -> SRr segs W c (o4r_st_cpy cx op).
Proof.
intros HP cx op W c HB HSUB.
pose proof (lp_laws B MT XL RLO RHI HP) as LAWS.
pose proof (lp_meter_laws B MT XL RLO RHI HP) as MTL.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned B MT XL RLO RHI HP)) as HGX.
pose proof (@YM05.alloc_ceiling_val rc) as [CE1 CE2].
assert (EST : ESTACK = 4096) by reflexivity.
assert (ELS : LLVMF_STK = 32768) by (vm_compute; reflexivity).
destruct HSUB as (ly' & S' & regs0 & mem0 & md0 & e & B1 & HH). cbv zeta in HH.
destruct HH as (-> & HCOM & Hraw & R21 & R11 & HCUR & HS46).
unfold lc_sub_common in HCOM. cbv zeta in HCOM.
destruct HCOM as (Ho & HL & HOB & HTW & HC8).
destruct HL as (HC & HFR & HSP & HFSH & HOPOK & He & HMET & R19).
destruct HCUR as (R24 & R23). destruct HS46 as (R20 & R22). destruct HFR as (R18 & R26).
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W regs0 mem0 md0 e HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof HC as (HJ0 & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal &
  HFceil & HFpres & HFL & HIN).
destruct HIN as (HPAY & HPAYv).
destruct Hstk as (Hceil & Hslo & Hshi & H47).
destruct Hn as (Hn26 & Hlen).
change (2 ^ 47) with 140737488355328 in H47.
unfold LF_FBYTES in HFceil. unfold LF_FRAME in Hsp1. change (2 ^ 26) with 67108864 in Hn26.
pose proof HOPOK as (HAGR & Hops & HcI & Hn0 & Hk0).
assert (HDlen : (0 < length (l_pl cx))%nat) by (destruct HcI as (Ha & Hb & Hcc); lia).
assert (Hnpos : 0 < l_n cx) by lia.
pose proof (HINg Hnpos) as Hblk.
destruct (al_blocks segs B LAWS ly' S' W mem0 md0 (l_p cx) (l_n cx) HARg Hblk)
  as (_ & Hp4096 & Hpce & _ & _ & _ & _).
pose proof (req_size_pos (l_n cx) ltac:(lia)) as (Hq1 & Hq2).
(* the cursor and the u16 *)
pose proof (o4r_oc_ok (l_pl cx) (lo_c op) HcI) as Hoc.
pose proof (o4r_kd_ok (l_pl cx) (lc_oc (l_pl cx) (lo_c op)) Hoc) as Hc3.
destruct (o4r_w_ok (l_pl cx) (sv_c (lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op)))) Hc3) as (Hw & Hc4).
pose proof Hc4 as (Hoff4 & Hn4 & Hsum4).
set (kd := lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op))) in *.
set (w := lc_raw_w (l_pl cx) (sv_c kd)) in *.
set (c4 := lc_raw_c4 (l_pl cx) (sv_c kd)) in *.
assert (Hn4b : 0 <= TOP.fi_n c4 <= 67108864) by lia.
(* the spill slot the `and` of +0x12f0 reads *)
unfold lc_spills in HSP. rewrite Forall_forall in HSP.
pose proof (HSP (120, 0xffff) ltac:(unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm;
  cbn [app In]; tauto)) as W120. cbn [fst snd] in W120.
(* ---- +0x12bc .. +0x1300: the take and the UBSan test of its end ---- *)
unfold lc_cfg.
replace (w64 (transportb_text + LO_SUBR)) with (Z_to_bv 64 (BASE + LO_SUBR)) by (rewrite o4s_base; reflexivity).
set (fx := l_fx cx) in *.
pose proof (o4r_entryR fx W regs0 mem0 (lc_sp1 cx) (l_p cx + TOP.fi_off c4) (TOP.fi_n c4) w
  R9 R11 R23 R24 ltac:(lia) ltac:(change (2 ^ 64) with 18446744073709551616; lia) Hw Hn4b
  ltac:(lia) W120) as HS.
set (E := o4s_E regs0 [w64 65535]) in HS.
assert (HEI : img_env VAL A_LIM E) by apply o4s_env_img.
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E (mrestrict (w_H W) mem0)) by constructor.
assert (X11 : ew E 11 = Z_to_bv 64 w)
  by (unfold E; rewrite (o4s_ew_reg regs0 _ 11 11%bv ltac:(lia) eq_refl); exact R11).
assert (X23 : ew E 23 = Z_to_bv 64 (TOP.fi_n c4))
  by (unfold E; rewrite (o4s_ew_reg regs0 _ 23 (Z_to_bv 5 23) ltac:(lia) eq_refl); exact R23).
assert (X24 : ew E 24 = Z_to_bv 64 (l_p cx + TOP.fi_off c4))
  by (unfold E; rewrite (o4s_ew_reg regs0 _ 24 (Z_to_bv 5 24) ltac:(lia) eq_refl); exact R24).
assert (X32 : ew E 32 = Z_to_bv 64 65535) by exact (o4s_ew_extra regs0 [w64 65535] 0 ltac:(lia)).
pose proof (@paj_run_x fx rc YE2k.tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
pose proof (@paj_run_to_x fx rc YE2k.tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
(* +0x1310 .. +0x1320: the store of the length byte, the memcpy, and the cut it reaches. Both sides of the `bltu`
   of +0x12f4 run it, with their own take t. *)
assert (TAIL : forall (regsX : bvmap 5 word) (memX : word -> option byte) (mdX : Model) (t : Z),
  0 <= t <= 24 -> t <= TOP.fi_n c4 ->
  lc_raw_vals (l_pl cx) (sv_c kd) =
    mkLrw t (TOP.fi_off c4) t (TOP.FuzzIn (TOP.fi_off c4 + t) (TOP.fi_n c4 - t)) ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] LLVMF_STK (lc_sp0 cx) []
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly' S' W memX mdX e ->
  (forall a, aview segs (w_H W) memX a = aview segs (w_H W) mem0 a) ->
  (forall a, apresent (w_H W) mem0 a -> apresent (w_H W) memX a) ->
  YK11.getr regsX (Z_to_bv 5 20) = w64 (lc_F cx + 32) ->
  YK11.getr regsX (Z_to_bv 5 12) = w64 t ->
  YK11.getr regsX (Z_to_bv 5 24) = w64 (l_p cx + TOP.fi_off c4) ->
  YK11.getr regsX (Z_to_bv 5 21) = w64 (l_p cx + TOP.fi_off c4 + t) ->
  YK11.getr regsX (Z_to_bv 5 27) = w64 (TOP.fi_n c4 - t) ->
  YK11.getr regsX (Z_to_bv 5 25) = w64 (bv_swrap 32 (TW.S_queued (lo_B op))) ->
  YK11.getr regsX (Z_to_bv 5 22) = w64 1 ->
  (forall r : Z, In r [2; 3; 4; 8; 9; 18; 19; 26] ->
     YK11.getr regsX (Z_to_bv 5 r) = YK11.getr regs0 (Z_to_bv 5 r)) ->
  SRr segs W (mkCfg (@YK11.mkst fx regsX (Z_to_bv 64 (BASE + O4R_STORE)) memX (YK11.seg_rom segs)) mdX)
    (o4r_st_cpy cx op)).
{ clear HS SHOK HEI.
  intros regsX memX mdX t Ht Htn Erv HJX KX GX T20 T12 T24 T21 T27 T25 T22 TK.
  assert (Rsp' : YK11.getr regs0 (Z_to_bv 5 2) = w64 (lc_sp1 cx)) by exact Rsp.
  assert (Rgp' : YK11.getr regs0 (Z_to_bv 5 3) = w64 (as_gp B)) by exact Rgp.
  assert (Rtp' : YK11.getr regs0 (Z_to_bv 5 4) = w64 (as_tp B)) by exact Rtp.
  assert (HFpresX : forall a, lc_F cx <= a < lc_F cx + 256 -> apresent (w_H W) memX a)
    by (intros a Ha; apply GX; apply HFpres; unfold LF_FBYTES; lia).
  pose proof (o4r_entryS fx W regsX memX (lc_F cx + 32) T20 ltac:(lia)
    (apresent_writable segs _ _ _ (HFpresX (lc_F cx + 32 + 24) ltac:(lia)))) as HS2.
  set (E2 := o4s_E regsX (@nil word)) in HS2.
  assert (HEI2 : img_env VAL A_LIM E2) by apply o4s_env_img.
  assert (SHOK2 : sh_ok segs (SLit 0) (@nil shent) E2 (mrestrict (w_H W) memX)) by constructor.
  assert (U20e : bv_unsigned (ew E2 20) = lc_F cx + 32)
    by (unfold E2; rewrite (o4s_ew_reg regsX _ 20 (Z_to_bv 5 20) ltac:(lia) eq_refl), T20; unfold w64;
        apply unsigned_lit_small; lia).
  assert (U24e : bv_unsigned (ew E2 24) = l_p cx + TOP.fi_off c4)
    by (unfold E2; rewrite (o4s_ew_reg regsX _ 24 (Z_to_bv 5 24) ltac:(lia) eq_refl), T24; unfold w64;
        apply unsigned_lit_small; lia).
  assert (U12e : bv_unsigned (ew E2 12) = t)
    by (unfold E2; rewrite (o4s_ew_reg regsX _ 12 (Z_to_bv 5 12) ltac:(lia) eq_refl), T12; unfold w64;
        apply unsigned_lit_small; lia).
  assert (U2e : bv_unsigned (ew E2 2) = lc_sp1 cx)
    by (unfold E2; rewrite (o4s_ew_reg regsX _ 2 (Z_to_bv 5 2) ltac:(lia) eq_refl),
        (TK 2 ltac:(cbn [In]; tauto)), Rsp'; unfold w64; apply unsigned_lit_small; lia).
  paj_run_tok RUN HS2 HJX SHOK2 (0, 0).
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
    apply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ LF_CID (l_fpos cx));
      [left; reflexivity | | apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U20e in Ha.
    left. unfold in_zr. cbn [fst snd]. rewrite HFaddr, lf_fbytes. unfold LF_FBYTES. lia. }
  assert (GS : forall a, apresent (w_H W) memX a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  assert (KS : forall a, 0 <= a < 2 ^ 64 -> ~ (lc_F cx + 56 <= a < lc_F cx + 57) ->
    aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) memX a).
  { intros a Ha Hna. apply (YC4b.kept_of_frame _ _ _ _ _ (fun x => lc_F cx + 56 <= x < lc_F cx + 57) HFr);
      [| exact Ha | exact Hna].
    intros b wlo whi x Hin Hx. lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in
      change (In y l') in Hin end.
    cbn [In] in Hin. destruct Hin as [Hin | []]. injection Hin as <- <- <-. cbn [base_val] in Hx.
    rewrite U20e in Hx. lia. }
  pose proof (YC4b.st_ok_region_nth _ _ _ 0 _ HS2 eq_refl) as RG. cbn [ms_mem restrict] in RG.
  pose proof (field_of_region_any E2 _ 20%nat (lc_F cx + 32) _ _ _ _ _ 24 1%N (SOff 12 0) RG U20e
    ltac:(cbn; tauto) ltac:(cbn; lia)) as VS.
  assert (D12 : bv_unsigned (sv_denot E2 (SOff 12 0)) = t)
    by (cbn [sv_denot]; rewrite U12e, Z.add_0_r; apply unsigned_lit_small; lia).
  rewrite D12 in VS. change (8 * Z.of_N 1) with 8 in VS. change (N.to_nat 1) with 1%nat in VS.
  rewrite (Z.mod_small t (2 ^ 8)) in VS by (change (2 ^ 8) with 256; lia).
  replace (lc_F cx + 32 + 24) with (lc_F cx + 56) in VS by lia.
  clear RG HF HFr HG.
  unfold E2 in *.
  o4s_reg HS2 (Z_to_bv 5 10) (w64 (lc_F cx + 32)) Q10
    ltac:(cbn [sv_denot]; rewrite U20e, Z.add_0_r; reflexivity).
  o4s_reg HS2 (Z_to_bv 5 11) (w64 (l_p cx + TOP.fi_off c4)) Q11
    ltac:(cbn [sv_denot]; rewrite U24e, Z.add_0_r; reflexivity).
  o4s_reg HS2 (Z_to_bv 5 12) (w64 t) Q12 ltac:(cbn [sv_denot]; rewrite U12e, Z.add_0_r; reflexivity).
  o4s_reg HS2 (1%bv : bv 5) (Z_to_bv 64 (BASE + O4R_CPY)) Q1 ltac:(apply codeptr_val; exact HEI2).
  o4s_reg HS2 (Z_to_bv 5 2) (w64 (lc_sp1 cx)) Q2 ltac:(cbn [sv_denot]; rewrite U2e, Z.add_0_r; reflexivity).
  o4s_reg HS2 (3%bv : bv 5) (w64 (as_gp B)) Q3
    ltac:(o4s_atom regsX (eq_trans (TK 3 ltac:(cbn [In]; tauto)) Rgp')).
  o4s_reg HS2 (4%bv : bv 5) (w64 (as_tp B)) Q4
    ltac:(o4s_atom regsX (eq_trans (TK 4 ltac:(cbn [In]; tauto)) Rtp')).
  assert (QSP : spZ (ms_regs ms) = lc_sp1 cx).
  { transitivity (bv_unsigned (w64 (lc_sp1 cx))); [unfold spZ; f_equal; exact Q2
    | unfold w64; apply unsigned_lit_small; lia]. }
  assert (HP1 : aregs_preserved regsX (ms_regs ms)) by o4s_keep7 HS2 regsX.
  pmkst HS2.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_memcpy)) mm rom) mdx) Q)
  end.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJX) as HARs.
  assert (HINB : forall mm mdx, @AR rc segs B ly' S' W mm mdx -> decode_rd_ok W mm (l_p cx) (l_n cx)).
  { intros mm mdx HARx. apply (trans_src_ok_rd B LAWS ly' S' W mm mdx (l_p cx) (l_n cx) HARx); [|lia].
    left. exists (l_p cx), (l_n cx). split; [exact Hblk | lia]. }
  pose proof (trans_rd_ok_sub W (ms_mem ms) (l_p cx) (l_n cx) (l_p cx + TOP.fi_off c4) t (HINB _ _ HARs)
    ltac:(lia) ltac:(lia) ltac:(lia)) as (HVx & HRAx & HHVx & HAMx & Hx0 & Hx63).
  pose proof (sep_block_frame segs B LAWS ly' S' W mem0 md0 (l_p cx) (l_n cx) LF_CID (l_fpos cx) HARg Hblk HFin)
    as HSEP.
  unfold zdisjoint in HSEP. cbn [fst snd] in HSEP. rewrite HFaddr, lf_fbytes in HSEP. unfold LF_FBYTES in HSEP.
  destruct (frames_bounds segs B LAWS ly' S' W mem0 md0 LF_CID (l_fpos cx) HARg HFin) as (_ & _ & HFapp).
  rewrite HFaddr, lf_fbytes in HFapp. unfold in_app, LF_FBYTES in HFapp.
  assert (HFapp' : lc_F cx + 256 <= kLowShadowBeg \/ kHighMemBeg <= lc_F cx)
    by (destruct HFapp as (_ & [H | [H _]]); lia).
  assert (HF8 : lc_F cx mod 8 = 0).
  { pose proof (Z.div_mod (lc_F cx) 64 ltac:(lia)) as Dv. rewrite HFal, Z.add_0_r in Dv. rewrite Dv.
    replace (64 * (lc_F cx / 64)) with ((8 * (lc_F cx / 64)) * 8) by lia. apply Z_mod_mult. }
  pose proof (Z.div_mod (lc_F cx) 8 ltac:(lia)) as DF8. rewrite HF8, Z.add_0_r in DF8.
  pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)) as Hdp.
  (* the frame's shadow lies apart from c's length byte *)
  assert (HSHa : forall i, 0 <= i < 32 -> SHADOW_OFF + lc_F cx / 8 + i <> lc_F cx + 56 /\
    0 <= SHADOW_OFF + lc_F cx / 8 + i < 2 ^ 64).
  { intros i Hi. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. change (2 ^ 64) with 18446744073709551616.
    destruct HFapp' as [Hl | Hh]; lia. }
  (* the memcpy's destination: c in the class-2 frame, its shadow 0 while op 4 runs (o4s_c_ok) *)
  assert (HFSHs : lc_fsh cx (aview segs (w_H W) (ms_mem ms)) true false).
  { apply (lc_fsh_kept cx (aview segs (w_H W) mem0) (aview segs (w_H W) (ms_mem ms))); [|exact HFSH].
    intros a Ha. unfold lc_SH in Ha.
    destruct (HSHa (a - (SHADOW_OFF + lc_F cx / 8)) ltac:(lia)) as (Hne & Hrg).
    rewrite KS by lia. apply KX. }
  destruct (o4s_c_ok B cx ly' S' W (ms_mem ms) _ false (@nil byte) LAWS HARs HFin HFaddr HFal
    (fun a Ha => GS a (HFpresX a ltac:(unfold LF_FBYTES in Ha; lia))) HFSHs) as (_ & HRDc).
  pose proof (trans_rd_ok_sub W (ms_mem ms) (lc_F cx + 32) 32 (lc_F cx + 32) t HRDc
    ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & HRAd & HHVd & HAMd & _ & _).
  eapply SRr_bind.
  { apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transportb_segs_low OCpy
      (transportb_sigma TB___asan_memcpy) (lp_memcpy B MT XL RLO RHI HP fx) TG.G_HARNESS_B W (ms_regs ms)
      (ms_mem ms) LLVMF_STK (lc_sp0 cx) [] (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx)
      [(LF_CID, l_fpos cx)] ly' S' _ e (lc_F cx + 32) (l_p cx + TOP.fi_off c4) t (lc_sp1 cx - lc_sp0 cx)
      (Z_to_bv 64 (BASE + O4R_CPY)) HGX G_HARNESS_B_rw HJX Q10 Q11 Q12).
    - lia.
    - lia.
    - lia.
    - rewrite QSP. lia.
    - pose proof (Z.div_mod (lc_sp1 cx) 32 ltac:(lia)) as D1. rewrite Hsp1al, Z.add_0_r in D1.
      pose proof (Z.div_mod (lc_sp0 cx) 16 ltac:(lia)) as D0. rewrite Hsp0al, Z.add_0_r in D0.
      replace (lc_sp1 cx - lc_sp0 cx) with ((2 * (lc_sp1 cx / 32) - lc_sp0 cx / 16) * 16) by lia.
      apply Z_mod_mult.
    - lia.
    - rewrite EST, ELS. lia.
    - exact Q3.
    - exact Q4.
    - exact Q1.
    - apply (ret_ok_codeptr_v (PI := PI_transportb)); [unfold O4R_CPY; lia | reflexivity].
    - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJX|]. intros a Ha. left. split.
      + unfold awr_byte. right; right; right. unfold in_frames. exists LF_CID, (l_fpos cx).
        split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite HFaddr, lf_fbytes.
        unfold LF_FBYTES. lia.
      + rewrite QSP, EST. lia.
    - exact HAMd.
    - exact HRAd.
    - intros _. exact HHVd.
    - split; [lia|]. split; [lia|]. split.
      { intros a Ha. split; [apply HVx; lia | rewrite QSP, EST; lia]. }
      split; [lia|]. split; [exact HAMx|]. split; [exact HRAx | intros _; exact HHVx]. }
  cbv beta. intros W2 c2 _ (-> & regs3 & mem3 & md4 & -> & HJ3 & HP3 & _ & Hcpy & Heff & Hgr).
  cbv iota in Hcpy.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (lc_F cx + 32 <= a < lc_F cx + 32 + t) -> a <> lc_F cx + 56 ->
    ~ (lc_sp1 cx - ESTACK <= a < lc_sp1 cx) -> aview segs (w_H W) mem3 a = aview segs (w_H W) mem0 a).
  { intros a Ha H1 H2 H3. rewrite Heff by lia. rewrite KS by lia. apply KX. }
  assert (GM : forall a, apresent (w_H W) mem0 a -> apresent (w_H W) mem3 a)
    by (intros a Ha; exact (Hgr a (GS a (GX a Ha)))).
  assert (RK : forall z, In z [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 26; 27] ->
    YK11.getr regs3 (Z_to_bv 5 z) = YK11.getr regsX (Z_to_bv 5 z)).
  { intros z Hz. assert (Hcs : acallee_saved z)
      by (unfold acallee_saved; cbn [In] in Hz; repeat (destruct Hz as [<- | Hz]; [lia|]); destruct Hz).
    rewrite (HP3 z Hcs). exact (HP1 z Hcs). }
  apply SRr_ret.
  exists ly', S', regs3, mem3, md4, e, B1.
  split; [unfold lc_cfg; rewrite <- o4s_base; reflexivity|].
  split; [exact Ho|].
  split; [exact HOB|]. split; [exact Hraw|].
  split.
  { unfold lc_tw. apply (tw_kept TMAP_B (aview segs (w_H W) mem0)); [exact HTW|].
    intros x Hx. destruct Hx as (o & b & n & Hin & Hxr).
    assert (HGx : W_journalG.inG TG.G_HARNESS_B x).
    { unfold W_journalG.inG. apply Exists_exists. exists (b, n).
      split; [exact (TMAP_B_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia]. }
    pose proof (transportb_segs_low x (proj1 (HGX x HGx))) as Hlow. unfold kLowMemEnd in Hlow.
    assert (HnF : ~ (lc_F cx <= x < lc_F cx + 256)).
    { intros Hr. apply (frm_img segs B LAWS ly' S' W mem0 md0 LF_CID (l_fpos cx) x HARg HFin);
        [rewrite HFaddr, lf_fbytes; unfold LF_FBYTES; lia | exact (trans_g_img x HGx)]. }
    apply KM; lia. }
  unfold o4r_cs, o4r_rvw, o4r_kd. fold kd. rewrite Erv. unfold lc_raw_cs. cbn [rw_off rw_len].
  destruct (o4r_cs_shape (l_pl cx) (TOP.fi_off c4) t (sv_display kd) (sv_key kd)
    ltac:(lia) ltac:(lia) ltac:(lia)) as (L1 & L0 & S1 & S24 & S2).
  split; [exact L1|].
  split.
  { split.
    - apply (lc_core_kept_run B MT XL RLO RHI cx ly' S' W regs0 mem0 md0 e ly' S' W regs3 mem3 md4 e HB HC HJ3
        eq_refl (Permutation_refl _)).
      + intros r Hr. rewrite (RK r ltac:(cbn [In] in Hr |- *; tauto)).
        exact (TK r ltac:(cbn [In] in Hr |- *; tauto)).
      + intros a Ha. apply KM; lia.
      + intros i Hi. apply KM; lia.
      + intros a Ha. unfold LF_FBYTES in Ha. apply KM; lia.
      + intros a Ha Hp. apply GM. exact Hp.
    - split.
      { split.
        - exact (eq_trans (RK 18 ltac:(cbn [In]; tauto)) (eq_trans (TK 18 ltac:(cbn [In]; tauto)) R18)).
        - exact (eq_trans (RK 26 ltac:(cbn [In]; tauto)) (eq_trans (TK 26 ltac:(cbn [In]; tauto)) R26)). }
      split.
      { apply (lc_spills_kept cx (lf_spill_loop (lc_F cx)) (aview segs (w_H W) mem0) (aview segs (w_H W) mem3));
          [|intros a Ha; apply KM; lia|].
        - intros o Hoin. pose proof (lf_spill_vals (lc_F cx) ltac:(lia) ltac:(unfold LF_FBYTES; lia)) as SV.
          rewrite Forall_forall in SV. destruct (SV o Hoin) as (_ & _ & Ho1 & Ho2). lia.
        - unfold lc_spills. rewrite Forall_forall. exact HSP. }
      split.
      { apply (lc_fsh_kept cx (aview segs (w_H W) mem0) (aview segs (w_H W) mem3) true false); [|exact HFSH].
        intros a Ha. unfold lc_SH in Ha.
        destruct (HSHa (a - (SHADOW_OFF + lc_F cx / 8)) ltac:(lia)) as (Hne & Hrg).
        apply KM; [lia | | lia |];
          unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; try rewrite EST;
          destruct HFapp' as [Hl | Hh]; lia. }
      split; [exact HOPOK|]. split; [exact He|]. split; [exact HMET|].
      exact (eq_trans (RK 19 ltac:(cbn [In]; tauto)) (eq_trans (TK 19 ltac:(cbn [In]; tauto)) R19)). }
  split.
  { change (garr8 segs (mrestrict (w_H W) mem0) (lc_F cx + 32)
      (TW.zs (TOP.cmd_struct (repeat (DSpec.b8 0) 24) 0 (sv_display kd) (sv_key kd)))) in HC8.
    apply o4r_garr8_of. intros j Hj. unfold TW.zs in Hj. rewrite length_map, L1 in Hj.
    rewrite o4r_nth_zs. split; [|apply o4r_byte_range].
    destruct (Nat.lt_ge_cases j (Z.to_nat t)) as [Hjt | Hjt].
    - rewrite (S1 j Hjt). rewrite (Hcpy (Z.of_nat j) ltac:(lia)). rewrite KS by lia. rewrite KX.
      assert (Hjd : (Z.to_nat (TOP.fi_off c4) + j < length (map (fun b : byte => bv_unsigned b) (l_pl cx)))%nat)
        by (rewrite length_map; lia).
      pose proof (o4r_garr8_aview _ _ _ _ _ HPAY Hjd) as Vj.
      replace (l_p cx + Z.of_nat (Z.to_nat (TOP.fi_off c4) + j)) with (l_p cx + TOP.fi_off c4 + Z.of_nat j)
        in Vj by lia.
      rewrite Vj. change (map (fun b : byte => bv_unsigned b) (l_pl cx)) with (TW.zs (l_pl cx)).
      rewrite o4r_nth_zs. reflexivity.
    - destruct (Nat.eq_dec j 24) as [-> | Hj24].
      + rewrite S24. replace (lc_F cx + 32 + Z.of_nat 24) with (lc_F cx + 56) by lia.
        rewrite (Heff (lc_F cx + 56)) by lia.
        refine (eq_trans (o4r_aview_vm1 _ _ _ _ VS ltac:(lia)) _). f_equal.
        unfold DSpec.b8. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
        symmetry. apply Z.mod_small. lia.
      + rewrite (S2 j ltac:(lia) Hj24). rewrite KM by lia.
        assert (Hj0 : (j < length (TW.zs (TOP.cmd_struct (repeat (DSpec.b8 0) 24) 0 (sv_display kd)
          (sv_key kd))))%nat) by (unfold TW.zs; rewrite length_map, L0; lia).
        rewrite (o4r_garr8_aview _ _ _ _ _ HC8 Hj0). rewrite o4r_nth_zs. reflexivity. }
  split.
  { unfold lc_spills. apply Forall_nil. }
  unfold o4r_rv, o4r_rvw, o4r_kd. fold kd. rewrite Erv. cbn [rw_c TOP.fi_off TOP.fi_n].
  apply Forall_cons; [cbn [fst snd]; rewrite (RK 25 ltac:(cbn [In]; tauto)); exact T25|].
  apply Forall_cons; [cbn [fst snd]; rewrite (RK 21 ltac:(cbn [In]; tauto)), Z.add_assoc; exact T21|].
  apply Forall_cons; [cbn [fst snd]; rewrite (RK 27 ltac:(cbn [In]; tauto)); exact T27|].
  apply Forall_cons; [cbn [fst snd]; rewrite (RK 20 ltac:(cbn [In]; tauto)); exact T20|].
  apply Forall_cons; [cbn [fst snd]; rewrite (RK 22 ltac:(cbn [In]; tauto)); exact T22|].
  apply Forall_nil. }
paj_run_to_tok RUNTO HS HJ0 SHOK YC4b.Bspan O4R_STORE.
{ o4s_awr. }
assert (GR0 : forall a, apresent (w_H W) mem0 a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
o4s_kept HFr KR0 W mem0 ms.
pose proof (o4s_kept_all W mem0 (ms_mem ms) KR0) as KR0a. clear HF HFr HG KR0.
psrr_branch_tok RUNTO BR HS SHOK YC4b.Bspan.
- (* +0x12f4 taken: the take is w mod 25 *)
  change (branch_taken BC_LTU (sv_denot E o4r_TAKE) (sv_denot E (SOff 23 0)) = true) in Hc.
  rewrite (o4r_br_take E w (TOP.fi_n c4) X11 X32 X23 Hw ltac:(lia)) in Hc.
  apply Z.ltb_lt in Hc.
  pose proof (Z.mod_pos_bound w 25 ltac:(lia)) as M25.
  assert (Erv : lc_raw_vals (l_pl cx) (sv_c kd) =
    mkLrw (w mod 25) (TOP.fi_off c4) (w mod 25)
      (TOP.FuzzIn (TOP.fi_off c4 + w mod 25) (TOP.fi_n c4 - w mod 25))).
  { apply (o4r_rv_eq (l_pl cx) (sv_c kd) (w mod 25) Hc3).
    change (w mod 25 = (if w mod 25 <? TOP.fi_n c4 then w mod 25 else TOP.fi_n c4)).
    rewrite (proj2 (Z.ltb_lt _ _) Hc). reflexivity. }
  paj_run_to_tok RUNTO HS HJ0 SHOK YC4b.Bspan O4R_STORE.
  { o4s_awr. }
  assert (GR1 : forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) (ms_mem ms0) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  o4s_kept HFr KR1 W (ms_mem ms) ms0.
  pose proof (o4s_kept_all W (ms_mem ms) (ms_mem ms0) KR1) as KR1a. clear HF HFr HG KR1.
  psrr_branch_tok RUNTO BR HS SHOK YC4b.Bspan.
  + exfalso.
    change (branch_taken BC_LTU (sv_denot E (SAlu ALU_XOR (SOff 24 0) (SLit (-1))))
              (sv_denot E o4r_TAKE) = true) in Hc0.
    rewrite (o4r_br_trap E (l_p cx + TOP.fi_off c4) o4r_TAKE (w mod 25) X24 ltac:(lia)
      (o4r_U_take E w X11 X32 Hw) ltac:(lia)) in Hc0.
    discriminate Hc0.
  + paj_run_to_tok RUNTO HS HJ0 SHOK YC4b.Bspan O4R_STORE.
    { o4s_awr. }
    assert (GR2 : forall a, apresent (w_H W) (ms_mem ms0) a -> apresent (w_H W) (ms_mem ms1) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
    o4s_kept HFr KR2 W (ms_mem ms0) ms1.
    pose proof (o4s_kept_all W (ms_mem ms0) (ms_mem ms1) KR2) as KR2a. clear HF HFr HG KR2.
    unfold E in *.
    o4s_reg HS (Z_to_bv 5 20) (w64 (lc_F cx + 32)) T20 ltac:(o4s_atom regs0 R20).
    o4s_reg HS (Z_to_bv 5 12) (w64 (w mod 25)) T12
      ltac:(change (sv_denot E o4r_TAKE = w64 (w mod 25)); exact (o4r_take_den E w X11 X32 Hw)).
    o4s_reg HS (Z_to_bv 5 24) (w64 (l_p cx + TOP.fi_off c4)) T24 ltac:(o4s_atom regs0 R24).
    o4s_reg HS (Z_to_bv 5 21) (w64 (l_p cx + TOP.fi_off c4 + w mod 25)) T21
      ltac:(change (sv_denot E (SAlu ALU_ADD (SOff 24 0) o4r_TAKE) =
                    w64 (l_p cx + TOP.fi_off c4 + w mod 25));
            rewrite o4r_den_alu, (o4r_den_off E 24 (l_p cx + TOP.fi_off c4) X24 ltac:(lia)),
              (o4r_take_den E w X11 X32 Hw); apply o4r_add_den).
    o4s_reg HS (Z_to_bv 5 27) (w64 (TOP.fi_n c4 - w mod 25)) T27
      ltac:(change (sv_denot E (SAlu ALU_SUB (SOff 23 0) o4r_TAKE) = w64 (TOP.fi_n c4 - w mod 25));
            rewrite o4r_den_alu, (o4r_den_off E 23 (TOP.fi_n c4) X23 ltac:(lia)),
              (o4r_take_den E w X11 X32 Hw); apply o4r_sub_den).
    o4s_reg HS (Z_to_bv 5 25) (w64 (bv_swrap 32 (TW.S_queued (lo_B op)))) T25 ltac:(o4s_atom regs0 R21).
    o4s_reg HS (Z_to_bv 5 22) (w64 1) T22 ltac:(o4s_atom regs0 R22).
    assert (TK : forall r : Z, In r [2; 3; 4; 8; 9; 18; 19; 26] ->
      YK11.getr (ms_regs ms1) (Z_to_bv 5 r) = YK11.getr regs0 (Z_to_bv 5 r)).
    { intros r Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<- | Hr]; [o4s_kreg HS regs0|]). destruct Hr. }
    pmkst HS.
    exact (TAIL (ms_regs ms1) (ms_mem ms1) _ (w mod 25) ltac:(lia) ltac:(lia) Erv HJ0
      ltac:(intros a; rewrite (KR2a a), (KR1a a); exact (KR0a a))
      ltac:(intros a Ha; exact (GR2 a (GR1 a (GR0 a Ha))))
      T20 T12 T24 T21 T27 T25 T22 TK).
- (* +0x12f4 not taken: the take is the bytes left *)
  change (branch_taken BC_LTU (sv_denot E o4r_TAKE) (sv_denot E (SOff 23 0)) = false) in Hc.
  rewrite (o4r_br_take E w (TOP.fi_n c4) X11 X32 X23 Hw ltac:(lia)) in Hc.
  apply Z.ltb_ge in Hc.
  pose proof (Z.mod_pos_bound w 25 ltac:(lia)) as M25.
  assert (Erv : lc_raw_vals (l_pl cx) (sv_c kd) =
    mkLrw (TOP.fi_n c4) (TOP.fi_off c4) (TOP.fi_n c4)
      (TOP.FuzzIn (TOP.fi_off c4 + TOP.fi_n c4) (TOP.fi_n c4 - TOP.fi_n c4))).
  { apply (o4r_rv_eq (l_pl cx) (sv_c kd) (TOP.fi_n c4) Hc3).
    change (TOP.fi_n c4 = (if w mod 25 <? TOP.fi_n c4 then w mod 25 else TOP.fi_n c4)).
    rewrite (proj2 (Z.ltb_ge _ _) Hc). reflexivity. }
  paj_run_to_tok RUNTO HS HJ0 SHOK YC4b.Bspan O4R_STORE.
  { o4s_awr. }
  assert (GR1 : forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) (ms_mem ms0) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  o4s_kept HFr KR1 W (ms_mem ms) ms0.
  pose proof (o4s_kept_all W (ms_mem ms) (ms_mem ms0) KR1) as KR1a. clear HF HFr HG KR1.
  psrr_branch_tok RUNTO BR HS SHOK YC4b.Bspan.
  + exfalso.
    change (branch_taken BC_LTU (sv_denot E (SAlu ALU_XOR (SOff 24 0) (SLit (-1))))
              (sv_denot E (SOff 23 0)) = true) in Hc0.
    rewrite (o4r_br_trap E (l_p cx + TOP.fi_off c4) (SOff 23 0) (TOP.fi_n c4) X24 ltac:(lia)
      (U_atom E 23 (TOP.fi_n c4) X23 ltac:(lia)) ltac:(lia)) in Hc0.
    discriminate Hc0.
  + paj_run_to_tok RUNTO HS HJ0 SHOK YC4b.Bspan O4R_STORE.
    { o4s_awr. }
    assert (GR2 : forall a, apresent (w_H W) (ms_mem ms0) a -> apresent (w_H W) (ms_mem ms1) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
    o4s_kept HFr KR2 W (ms_mem ms0) ms1.
    pose proof (o4s_kept_all W (ms_mem ms0) (ms_mem ms1) KR2) as KR2a. clear HF HFr HG KR2.
    unfold E in *.
    o4s_reg HS (Z_to_bv 5 20) (w64 (lc_F cx + 32)) T20 ltac:(o4s_atom regs0 R20).
    o4s_reg HS (Z_to_bv 5 12) (w64 (TOP.fi_n c4)) T12 ltac:(o4s_atom regs0 R23).
    o4s_reg HS (Z_to_bv 5 24) (w64 (l_p cx + TOP.fi_off c4)) T24 ltac:(o4s_atom regs0 R24).
    o4s_reg HS (Z_to_bv 5 21) (w64 (l_p cx + TOP.fi_off c4 + TOP.fi_n c4)) T21
      ltac:(first
        [ change (sv_denot E (SAlu ALU_ADD (SOff 24 0) (SOff 23 0)) =
                  w64 (l_p cx + TOP.fi_off c4 + TOP.fi_n c4));
          rewrite o4r_den_alu, (o4r_den_off E 24 (l_p cx + TOP.fi_off c4) X24 ltac:(lia)),
            (o4r_den_off E 23 (TOP.fi_n c4) X23 ltac:(lia)); apply o4r_add_den
        | change (sv_denot E (SAlu ALU_ADD (SOff 23 0) (SOff 24 0)) =
                  w64 (l_p cx + TOP.fi_off c4 + TOP.fi_n c4));
          rewrite o4r_den_alu, (o4r_den_off E 24 (l_p cx + TOP.fi_off c4) X24 ltac:(lia)),
            (o4r_den_off E 23 (TOP.fi_n c4) X23 ltac:(lia)), o4r_add_den;
          apply (f_equal (Z_to_bv 64)); ring
        | lazymatch goal with |- ?G => fail 100 "T21GOAL" G end ]).
    o4s_reg HS (Z_to_bv 5 27) (w64 (TOP.fi_n c4 - TOP.fi_n c4)) T27
      ltac:(first
        [ change (sv_denot E (SAlu ALU_SUB (SOff 23 0) (SOff 23 0)) = w64 (TOP.fi_n c4 - TOP.fi_n c4));
          rewrite o4r_den_alu, (o4r_den_off E 23 (TOP.fi_n c4) X23 ltac:(lia)); apply o4r_sub_den
        | cbn [sv_denot]; rewrite Z.sub_diag; reflexivity
        | lazymatch goal with |- ?G => fail 100 "T27GOAL" G end ]).
    o4s_reg HS (Z_to_bv 5 25) (w64 (bv_swrap 32 (TW.S_queued (lo_B op)))) T25 ltac:(o4s_atom regs0 R21).
    o4s_reg HS (Z_to_bv 5 22) (w64 1) T22 ltac:(o4s_atom regs0 R22).
    assert (TK : forall r : Z, In r [2; 3; 4; 8; 9; 18; 19; 26] ->
      YK11.getr (ms_regs ms1) (Z_to_bv 5 r) = YK11.getr regs0 (Z_to_bv 5 r)).
    { intros r Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<- | Hr]; [o4s_kreg HS regs0|]). destruct Hr. }
    pmkst HS.
    exact (TAIL (ms_regs ms1) (ms_mem ms1) _ (TOP.fi_n c4) ltac:(lia) ltac:(lia) Erv HJ0
      ltac:(intros a; rewrite (KR2a a), (KR1a a); exact (KR0a a))
      ltac:(intros a Ha; exact (GR2 a (GR1 a (GR0 a Ha))))
      T20 T12 T24 T21 T27 T25 T22 TK).
Qed.

(* +0x1320 .. +0x1344: &g_s and c to diginet_session_submit; c, its result and the queue length before to
   check_refusal_submit; s8 = s5 and `j` to S4. *)
Lemma o4r_seg_b : lp_prem B MT XL RLO RHI -> forall (cx : lcx) (op : lop) (W1 : world segs) (c1 : config),
  lc_base B MT XL RLO RHI cx -> o4r_st_cpy cx op W1 c1 -> SRr segs W1 c1 (lc_st_s4 B MT cx op).
Proof.
intros HP cx op W1 c1 HB HCPY.
pose proof (lp_laws B MT XL RLO RHI HP) as LAWS. pose proof (lp_meter_laws B MT XL RLO RHI HP) as MTL.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned B MT XL RLO RHI HP)) as HGX.
destruct HCPY as (ly1 & S1 & regs1 & mem1 & md1 & e1 & B1 & Ec1 & Hopc & HOB & Hraw & HTW & Hcs & INV0).
set (cs := o4r_cs cx op) in *.
pose proof INV0 as (HLC & HGA & HSL & HRV).
pose proof HLC as (HCORE & HFR & HSPL & HFSH & HOPOK & He1 & HMET & R19).
(* the model *)
pose proof HOPOK as (HAG & Hops & Hcok & Hcn & Hk).
destruct (o4r_model (l_pl cx) (lo_B op) B1 (lo_c op) (lo_ops op) (lo_k op) HAG Hops Hcok Hcn Hk Hopc HOB Hraw)
  as (B2 & r & B3 & M2 & M3 & M4 & MOP).
change (TS0.diginet_session_submit_m B1 cs = Some (B2, r)) in M2.
change (TC.check_refusal_submit_m B2 cs r (TW.S_queued (lo_B op)) = Some (B3, tt)) in M3.
change (forall A, TOP.LLVMFuzzerTestOneInput_op_m timg_B (lo_B op) A (l_pl cx) (lo_c op) (lo_k op) =
  Some (B3, (rw_c (o4r_rvw cx op), lo_k op))) in MOP.
pose proof (o4s_submit_rc _ _ _ _ M2) as Hr.
(* the geometry *)
destruct (lc_geom B MT XL RLO RHI cx ly1 S1 W1 regs1 mem1 md1 e1 HB HCORE)
  as [HAR1 Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof HCORE as (HJ1 & Hfrs1 & HlyF1 & HPERM1 & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal &
  HFceil & HFpres & HFL & HIN).
pose proof (@YM05.alloc_ceiling_val rc) as [CE1 CE2].
destruct Hstk as (Hs1 & Hs2 & Hs3 & Hs4). unfold LF_FRAME in Hsp1. unfold LF_FBYTES in HFceil.
change (2 ^ 47) with 140737488355328 in Hs4.
assert (ESS : SSUBMIT_STK = 4320) by (vm_compute; reflexivity).
assert (ELS : LLVMF_STK = 32768) by (vm_compute; reflexivity).
assert (EST : ESTACK = 4096) by reflexivity.
assert (H16 : lc_sp1 cx mod 16 = 0).
{ apply Z.mod_divide in Hsp1al as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((q * 2) * 16) by ring.
  apply Z_mod_mult. }
assert (HF4 : (lc_F cx + 32) mod 4 = 0).
{ apply Z.mod_divide in HFal as [q Hq]; [|lia]. rewrite Hq. replace (q * 64 + 32) with ((q * 16 + 8) * 4) by ring.
  apply Z_mod_mult. }
pose proof (Z.mul_div_le (lc_F cx) 8 ltac:(lia)) as HF8.
pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)) as HF8p.
rewrite Forall_forall in HRV.
pose proof (HRV (20, w64 (lc_F cx + 32)) ltac:(unfold o4r_rv; cbn [In]; tauto)) as R20. cbn [fst snd] in R20.
(* ---- +0x1320 .. +0x132c: a0 = &g_s, a1 = c, the call of diginet_session_submit ---- *)
subst c1. unfold lc_cfg.
set (fx := l_fx cx) in *.
replace (w64 (transportb_text + O4R_CPY)) with (Z_to_bv 64 (BASE + O4R_CPY)) by (rewrite o4s_base; reflexivity).
pose proof (o4s_entry0 fx W1 regs1 (@nil word) mem1 O4R_CPY) as HS.
assert (HEI : img_env VAL A_LIM (o4s_E regs1 [])) by apply o4s_env_img.
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) (o4s_E regs1 []) (mrestrict (w_H W1) mem1)) by constructor.
pose proof (@paj_run_x fx rc YE2k.tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
pose proof (@paj_run_to_x fx rc YE2k.tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
paj_run_tok RUN HS HJ1 SHOK YC4b.Bspan.
{ o4s_awr. }
o4s_kept HFr KR1 W1 mem1 ms.
pose proof (o4s_kept_all W1 mem1 (ms_mem ms) KR1) as KR1a. clear HF HFr HG KR1.
assert (HK1 : aregs_preserved regs1 (ms_regs ms)) by o4s_keep7 HS regs1.
assert (INV1 : o4s_inv B MT cx op cs [] (o4r_rv cx op) ly1 S1 W1 (ms_regs ms) (ms_mem ms)
  (with_vm_backing (m_vm_lazy md1) mat md1) e1).
{ apply (o4s_inv_kept7 B MT XL RLO RHI cx op cs [] (o4r_rv cx op) ly1 S1 W1 regs1 mem1 md1 e1 0 ly1 S1 W1
    (ms_regs ms) (ms_mem ms) _ LAWS MTL HB INV0 HJ1 eq_refl (Permutation_refl _) HK1 (mo_le_refl MT MTL S1)).
  - rewrite ELS. lia.
  - intros a _ _. exact (KR1a a).
  - intros b m i _ _. exact (KR1a (b + i)).
  - intros a _. exact (KR1a a).
  - exact Hcs.
  - apply o4r_sl_ok.
  - apply o4r_rv_ok. }
o4s_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 4912)) Q1 ltac:(apply codeptr_val; exact HEI).
o4s_reg HS (2%bv : bv 5) (w64 (lc_sp1 cx)) Q2 ltac:(o4s_atom regs1 Rsp).
o4s_reg HS (3%bv : bv 5) (w64 (as_gp B)) Q3 ltac:(o4s_atom regs1 Rgp).
o4s_reg HS (4%bv : bv 5) (w64 (as_tp B)) Q4 ltac:(o4s_atom regs1 Rtp).
o4s_reg HS (11%bv : bv 5) (w64 (lc_F cx + 32)) Q11 ltac:(o4s_atom regs1 R20).
o4s_reg HS (10%bv : bv 5) (w64 SSUBMIT_S) Q10
  ltac:(first
    [ vm_compute; reflexivity
    | cbn [sv_denot]; erewrite img_env_atomP; [vm_compute; reflexivity | exact HEI | unfold A_TEXT, A_LIM; lia] ]).
assert (QSP : spZ (ms_regs ms) = lc_sp1 cx).
{ transitivity (bv_unsigned (w64 (lc_sp1 cx))); [unfold spZ; f_equal; exact Q2
  | unfold w64; apply unsigned_lit_small; lia]. }
assert (QRA : raZ (ms_regs ms) = BASE + 4912).
{ unfold raZ. transitivity (bv_unsigned (Z_to_bv 64 (BASE + 4912))); [f_equal; exact Q1|].
  apply unsigned_lit_small. rewrite o4s_base. unfold transportb_text. lia. }
pmkst HS.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HARc.
pose proof INV1 as (HLC1 & HGA1 & HSL1 & HRV1).
pose proof HLC1 as (HC1 & HFR1 & HSP1 & HFSH1 & _).
pose proof HC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFpresc & _).
destruct (o4s_c_ok B cx ly1 S1 W1 (ms_mem ms) _ false cs LAWS HARc HFin HFaddr HFal HFpresc HFSH1) as (HINF & HRD).
eapply SRr_bind.
{ refine (lp_submit B MT XL RLO RHI HP fx LLVMF_STK (lc_sp0 cx) [] (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx)
    [(LF_CID, l_fpos cx)] ly1 S1 W1 (ms_mem ms) (with_vm_backing (m_vm_lazy md1) mat md1) e1 (ms_regs ms)
    (lc_F cx + 32) r cs B1 B2 HJ1 _ _ Q3 Q4 Q10 Q11 _ _ _ _ M2 Hcs _ HF4 _ HGA1 _ _ _ _).
  - change (YK0s.ret_ok (YK11.getr (ms_regs ms) 1%bv)). rewrite Q1.
    apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity].
  - rewrite QRA, o4s_base. unfold transportb_text. lia.
  - rewrite QSP. exact H16.
  - rewrite QSP, ESS, ELS. lia.
  - rewrite QSP. lia.
  - apply (tw_kept TMAP_B (aview segs (w_H W1) mem1)); [exact HTW | intros x _; exact (KR1a x)].
  - lia.
  - right. split; [left; exact HINF | exact HRD].
  - unfold decode_off_win, SSUBMIT_CMD_LEN. left. rewrite QSP, ESS. lia.
  - intros x Hx. split; intros HX.
    + apply (frm_img segs B LAWS ly1 S1 W1 _ _ LF_CID (l_fpos cx) x HARc HFin);
        [rewrite HFaddr; change (fs_frame_bytes LF_CID) with 256; unfold SSUBMIT_CMD_LEN in Hx; lia
        | exact (trans_g_img x HX)].
    + apply (frm_img segs B LAWS ly1 S1 W1 _ _ LF_CID (l_fpos cx) x HARc HFin);
        [rewrite HFaddr; change (fs_frame_bytes LF_CID) with 256; unfold SSUBMIT_CMD_LEN in Hx; lia
        | exact (trans_ro_img x HX)].
  - rewrite Hfrs1. vm_compute. reflexivity.
  - pose proof HB as HB'. unfold lc_base, tfib_lib_pre_x in HB'.
    destruct HB' as (_ & _ & _ & _ & _ & _ & _ & _ & Hev & _).
    lazymatch type of Hev with _ + ?x <= _ => let v := eval vm_compute in x in change x with v in Hev end.
    assert (EOM : TC.OPS_MAX = 1024) by reflexivity.
    assert (ERV : receive_cg.RECV_EV = 2) by reflexivity.
    rewrite ERV in He1. unfold SSUBMIT_EV. lia. }
cbv beta. intros W2 c2 _ HPOST.
unfold transport_ssubmit_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly2 & S2 & regs2 & mem2 & md2 & e2 & Ec2 & He2 & HJ2 & HP2 & Hfr2 & Hperm2 & HK2 & Hmo2 &
  (HA0 & HTW2)).
assert (Ee2 : e2 = 0) by (unfold SSUBMIT_EV in He2; lia). subst e2. rewrite Z.add_0_r in HJ2.
change (YK11.getr (ms_regs ms) 1) with (YK11.getr (ms_regs ms) 1%bv) in Ec2. rewrite Q1 in Ec2. subst c2.
pose proof HK2 as (K21 & K22 & K23 & K24 & _).
assert (INV2 : o4s_inv B MT cx op cs [] (o4r_rv cx op) ly2 S2 W2 regs2 mem2 md2 e1).
{ apply (o4s_inv_kept7 B MT XL RLO RHI cx op cs [] (o4r_rv cx op) ly1 S1 W1 (ms_regs ms) (ms_mem ms) _ e1
    SSUBMIT_STK ly2 S2 W2 regs2 mem2 md2 LAWS MTL HB INV1 HJ2 Hfr2 Hperm2 HP2 Hmo2).
  - rewrite ESS, ELS. lia.
  - intros a Ha Hna. apply K21; [exact Ha | rewrite QSP; exact Hna].
  - intros b m i Hb Hi. apply (K22 b m i Hb Hi). intros Hw.
    exact (blk_img segs B LAWS ly1 S1 W1 _ _ b m (b + i) HARc Hb ltac:(lia) (o4s_wr_img _ Hw)).
  - intros a Ha. apply (K24 LF_CID (l_fpos cx) a HFin).
    + destruct Ha as [Ha | Ha]; [left | right]; unfold in_zr, frame_rng; cbn [fst snd]; rewrite HFaddr;
        change (fs_frame_bytes LF_CID) with 256; unfold lc_SH, LF_FBYTES, shadow_addr in *; lia.
    + intros Hw. destruct Ha as [Ha | Ha].
      * exact (frm_img segs B LAWS ly1 S1 W1 _ _ LF_CID (l_fpos cx) a HARc HFin
          ltac:(rewrite HFaddr; change (fs_frame_bytes LF_CID) with 256; unfold LF_FBYTES in Ha; lia)
          (o4s_wr_img _ Hw)).
      * pose proof (o4s_wr_gs a Hw) as Hg. unfold lc_SH, SHADOW_OFF in Ha.
        unfold TB_g_s, TW.SZ_g_s in Hg. lia.
  - exact Hcs.
  - apply o4r_sl_ok.
  - apply o4r_rv_ok. }
(* ---- +0x1330 .. +0x133c: a1 = rc, a0 = c, a2 = s9, the call of check_refusal_submit ---- *)
pose proof INV2 as (HLC2 & HGA2 & HSL2 & HRV2).
pose proof HLC2 as (HC2 & HFR2 & _).
pose proof HC2 as (_ & _ & _ & _ & R2_2 & R8_2 & R9_2 & R3_2 & R4_2 & _).
rewrite Forall_forall in HRV2.
pose proof (HRV2 (20, w64 (lc_F cx + 32)) ltac:(unfold o4r_rv; cbn [In]; tauto)) as R20_2.
pose proof (HRV2 (25, w64 (bv_swrap 32 (TW.S_queued (lo_B op)))) ltac:(unfold o4r_rv; cbn [In]; tauto)) as R25_2.
cbn [fst snd] in R20_2, R25_2.
pose proof (o4s_entry0 fx W2 regs2 (@nil word) mem2 4912) as HS2.
assert (HEI2 : img_env VAL A_LIM (o4s_E regs2 [])) by apply o4s_env_img.
assert (SHOK2 : sh_ok segs (SLit 0) (@nil shent) (o4s_E regs2 []) (mrestrict (w_H W2) mem2)) by constructor.
paj_run_tok RUN HS2 HJ2 SHOK2 YC4b.Bspan.
{ o4s_awr. }
o4s_kept HFr KR2 W2 mem2 ms0.
pose proof (o4s_kept_all W2 mem2 (ms_mem ms0) KR2) as KR2a. clear HF HFr HG KR2.
assert (HK3 : aregs_preserved regs2 (ms_regs ms0)) by o4s_keep7 HS2 regs2.
assert (INV3 : o4s_inv B MT cx op cs [] (o4r_rv cx op) ly2 S2 W2 (ms_regs ms0) (ms_mem ms0)
  (with_vm_backing (m_vm_lazy md2) mat0 md2) e1).
{ apply (o4s_inv_kept7 B MT XL RLO RHI cx op cs [] (o4r_rv cx op) ly2 S2 W2 regs2 mem2 md2 e1 0 ly2 S2 W2
    (ms_regs ms0) (ms_mem ms0) _ LAWS MTL HB INV2 HJ2 eq_refl (Permutation_refl _) HK3 (mo_le_refl MT MTL S2)).
  - rewrite ELS. lia.
  - intros a _ _. exact (KR2a a).
  - intros b m i _ _. exact (KR2a (b + i)).
  - intros a _. exact (KR2a a).
  - exact Hcs.
  - apply o4r_sl_ok.
  - apply o4r_rv_ok. }
o4s_reg HS2 (1%bv : bv 5) (Z_to_bv 64 (BASE + 4928)) P1 ltac:(apply codeptr_val; exact HEI2).
o4s_reg HS2 (Z_to_bv 5 2) (w64 (lc_sp1 cx)) P2 ltac:(o4s_atom regs2 R2_2).
o4s_reg HS2 (3%bv : bv 5) (w64 (as_gp B)) P3 ltac:(o4s_atom regs2 R3_2).
o4s_reg HS2 (4%bv : bv 5) (w64 (as_tp B)) P4 ltac:(o4s_atom regs2 R4_2).
o4s_reg HS2 (Z_to_bv 5 10) (w64 (lc_F cx + 32)) P10 ltac:(o4s_atom regs2 R20_2).
o4s_reg HS2 (Z_to_bv 5 11) (w64 r) P11 ltac:(o4s_atom regs2 HA0).
o4s_reg HS2 (Z_to_bv 5 12) (w64 (bv_swrap 32 (TW.S_queued (lo_B op)))) P12 ltac:(o4s_atom regs2 R25_2).
assert (PSP : spZ (ms_regs ms0) = lc_sp1 cx).
{ transitivity (bv_unsigned (w64 (lc_sp1 cx))); [unfold spZ; f_equal; exact P2
  | unfold w64; apply unsigned_lit_small; lia]. }
assert (PSPu : bv_unsigned (YK11.getr (ms_regs ms0) (Z_to_bv 5 2)) = lc_sp1 cx) by exact PSP.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HARc3.
destruct (gx_open segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as (memS & HJd & _ & _).
pose proof HJd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _). clear HJd memS.
pose proof INV3 as (HLC3 & HGA3 & HSL3 & HRV3).
pose proof HLC3 as (HC3 & HFR3 & HSP3 & HFSH3 & _).
pose proof HC3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFpres3 & _).
destruct (lc_geom B MT XL RLO RHI cx ly2 S2 W2 (ms_regs ms0) (ms_mem ms0) _ e1 HB HC3)
  as [_ _ _ _ HFaddr2 HFin2 _ _ _].
destruct (o4s_c_ok B cx ly2 S2 W2 (ms_mem ms0) _ false cs LAWS HARc3 HFin2 HFaddr2 HFal HFpres3 HFSH3)
  as (HINF3 & HRD3).
destruct (frames_bounds segs B LAWS ly2 S2 W2 (ms_mem ms0) _ LF_CID (l_fpos cx) HARc3 HFin2) as (_ & _ & Happ2).
rewrite HFaddr2 in Happ2. change (fs_frame_bytes LF_CID) with 256 in Happ2.
pmkst HS2.
assert (EPC1 : pa_sigma TB_check_refusal_submit = LCRSc.CHECK_REFUSAL_SUBMIT) by reflexivity.
rewrite EPC1.
eapply SRr_bind.
{ apply (o4s_leaf B fx W2 (ms_regs ms0) (ms_mem ms0) LLVMF_STK (lc_sp0 cx) [] (l_ly cx) (l_S cx) (l_W cx) (l_mem cx)
    (l_md cx) [(LF_CID, l_fpos cx)] ly2 S2 _ e1 (lc_sp1 cx - lc_sp0 cx) LCRSc.CHECK_REFUSAL_SUBMIT
    (fun _ => B3 = B2) LAWS HJ2).
  - rewrite PSP. ring.
  - rewrite Zminus_mod, H16, Hsp0al. reflexivity.
  - lia.
  - rewrite EST, ELS. lia.
  - change (YK0s.ret_ok (YK11.getr (ms_regs ms0) 1%bv)). rewrite P1.
    apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity].
  - exact P3.
  - exact P4.
  - intros HPRE.
    pose proof (lp_crs B MT XL RLO RHI HP fx) as LF.
    unfold transport_leaf_at, LCRS.transport_check_refusal_submit_cg in LF.
    specialize (LF ly2 S2 W2 (ms_regs ms0) (ms_mem ms0) _ (lc_sp1 cx - ESTACK) B2 B3 (lc_F cx + 32) cs r
      (TW.S_queued (lo_B op)) HPRE).
    cbv zeta in LF.
    destruct HRD3 as (_ & HRA3 & _ & _).
    apply LF; clear LF.
    + exact P10.
    + exact P11.
    + exact P12.
    + lia.
    + exact (TWL.u_at_range (lo_B op) TW.A_S_queued 4).
    + lia.
    + exact HF4.
    + apply (decode_leafb_bytes_garr8 W2 (ms_mem ms0) (lc_F cx + 32) cs); [exact HGA3 | lia |].
      rewrite Hcs. change (Z.of_nat 32) with 32. change (2 ^ 64) with 18446744073709551616. lia.
    + exact Hcs.
    + apply (o4s_tw_csw W2). apply (tw_kept TMAP_B (aview segs (w_H W2) mem2)); [exact HTW2 | intros x _;
        exact (KR2a x)].
    + exact M3.
    + rewrite PSPu. apply (decode_leafb_stk W2 (ms_mem ms0));
        [rewrite EST; lia | change (2 ^ 64) with 18446744073709551616; lia |].
      intros a Ha. apply Hpres3. rewrite EST in Ha. rewrite ELS. lia.
    + rewrite PSPu. unfold LCRSc.CHECK_REFUSAL_SUBMIT_FRAME. rewrite EST. lia.
    + unfold AKA.off_stk. rewrite PSPu.
      unfold LCRSc.CHECK_REFUSAL_SUBMIT_FRAME, TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI. lia.
    + exact (decode_leafb_asan_cells B (lp_cells B MT XL RLO RHI HP) ly2 S2 W2 (ms_mem ms0) _ HARc3).
    + rewrite PSPu. apply (@decode_leafb_app_stack rc).
      unfold LCRSc.CHECK_REFUSAL_SUBMIT_FRAME. lia.
    + rewrite PSPu. apply (@decode_leafb_app_stack rc). lia.
    + unfold AKA.off_stk. rewrite PSPu.
      unfold LCRSc.CHECK_REFUSAL_SUBMIT_FRAME, AsanCells.GOT_CELL_K. lia.
    + unfold AKA.off_stk. rewrite PSPu.
      unfold LCRSc.CHECK_REFUSAL_SUBMIT_FRAME, AsanCells.CELL_K. lia.
    + unfold AKA.off_stk. rewrite PSPu.
      unfold LCRSc.CHECK_REFUSAL_SUBMIT_FRAME. lia.
    + apply (decode_leafb_addressable W2 (ms_mem ms0) (lc_F cx + 32) 32 HRA3); [lia | lia | |].
      * pose proof (@decode_leafb_app_of_in_app rc (lc_F cx) 256 255 Happ2 ltac:(lia)) as HA.
        unfold AsanCells.app_mem in HA. unfold AsanCells.APPMEM_END.
        unfold AsanCells.LOWMEM_END, AsanCells.HIGHMEM_BEG, AsanCells.APPMEM_END in HA. lia.
      * intros i Hi. replace (lc_F cx + 32 + i) with (lc_F cx + (32 + i)) by ring.
        apply (@decode_leafb_app_of_in_app rc (lc_F cx) 256 (32 + i) Happ2). lia.
    + rewrite PSPu. unfold LCRSc.CHECK_REFUSAL_SUBMIT_FRAME.
      apply (decode_leafb_rng_vis W2 (ms_mem ms0)); [lia | change (2 ^ 64) with 18446744073709551616; lia |].
      intros a Ha. apply Hpres3. rewrite ELS. lia.
    + exact (proj1 (decode_leafb_rng_cells W2)).
    + exact (proj2 (decode_leafb_rng_cells W2)).
    + intros i Hi.
      pose proof (decode_leafb_rng_shadow W2 (ms_mem ms0) (lc_F cx + 32) 32 HRA3 ltac:(lia) ltac:(lia)
        ltac:(change (2 ^ 64) with 18446744073709551616; lia)) as HRS.
      apply (ExecF.rng_sub _ _ _ _ _ HRS); unfold AsanCells.shadow_addr.
      * pose proof (Z.div_le_mono (lc_F cx + 32) (lc_F cx + 32 + i) 8 ltac:(lia) ltac:(lia)). lia.
      * pose proof (Z.div_le_mono (lc_F cx + 32 + i) (lc_F cx + 32 + 32 - 1) 8 ltac:(lia) ltac:(lia)). lia.
    + apply (decode_leafb_rng_vis W2 (ms_mem ms0) (lc_F cx + 32) 32);
        [lia | change (2 ^ 64) with 18446744073709551616; lia |].
      intros a Ha. apply HFpres3. unfold LF_FBYTES. lia.
    + rewrite LCRSc.check_refusal_submit_queued_at. apply o4s_rng_hull;
        unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & Ec3 & HJ3 & HP3 & KE3 & Hgr3 & HX3).
cbv beta in HX3.
change (YK11.getr (ms_regs ms0) 1) with (YK11.getr (ms_regs ms0) 1%bv) in Ec3. rewrite P1 in Ec3. subst c3.
assert (INV4 : o4s_inv B MT cx op cs [] (o4r_rv cx op) ly2 S2 W2 regs3 mem3 md3 e1).
{ apply (o4s_inv_kept7 B MT XL RLO RHI cx op cs [] (o4r_rv cx op) ly2 S2 W2 (ms_regs ms0) (ms_mem ms0) _ e1 ESTACK
    ly2 S2 W2 regs3 mem3 md3 LAWS MTL HB INV3 HJ3 eq_refl (Permutation_refl _) HP3 (mo_le_refl MT MTL S2)).
  - rewrite EST, ELS. lia.
  - intros a Ha Hna. apply KE3; [lia | rewrite PSP; exact Hna].
  - intros b m i Hb Hi.
    destruct (al_blocks segs B LAWS ly2 S2 W2 (ms_mem ms0) _ b m HARc3 Hb) as (_ & H4096 & Hc & _).
    apply KE3; [change (2 ^ 64) with 18446744073709551616; lia | rewrite PSP, EST; lia].
  - intros a Ha. unfold lc_SH, LF_FBYTES, SHADOW_OFF in Ha.
    apply KE3; [change (2 ^ 64) with 18446744073709551616; lia | rewrite PSP, EST; lia].
  - exact Hcs.
  - apply o4r_sl_ok.
  - apply o4r_rv_ok. }
assert (HTW3 : lc_tw W2 mem3 B3).
{ rewrite HX3. unfold lc_tw. apply (tw_kept TMAP_B (aview segs (w_H W2) mem2)); [exact HTW2|].
  intros x Hx. pose proof Hx as (o & b & n & Hin & Hxr).
  assert (HGx : W_journalG.inG TG.G_HARNESS_B x).
  { unfold W_journalG.inG. apply Exists_exists. exists (b, n).
    split; [exact (TMAP_B_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia]. }
  pose proof (transportb_segs_low x (proj1 (HGX x HGx))) as Hlow. unfold kLowMemEnd in Hlow.
  rewrite (KE3 x ltac:(lia) ltac:(rewrite PSP, EST; lia)). exact (KR2a x). }
(* ---- +0x1340 .. +0x1344: s8 = s5, `j` to S4 ---- *)
pose proof (o4s_entry0 fx W2 regs3 (@nil word) mem3 4928) as HS3.
assert (HEI3 : img_env VAL A_LIM (o4s_E regs3 [])) by apply o4s_env_img.
assert (SHOK3 : sh_ok segs (SLit 0) (@nil shent) (o4s_E regs3 []) (mrestrict (w_H W2) mem3)) by constructor.
paj_run_to_tok RUNTO HS3 HJ3 SHOK3 YC4b.Bspan LO_S4.
{ o4s_awr. }
assert (GR5 : forall a, apresent (w_H W2) mem3 a -> apresent (w_H W2) (ms_mem ms1) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
o4s_kept HFr KR3 W2 mem3 ms1.
pose proof (o4s_kept_all W2 mem3 (ms_mem ms1) KR3) as KR3a. clear HF HFr HG KR3.
(* `mv s8, s5` writes s8, so this run keeps every callee-saved register but it *)
assert (HK5 : forall r0 : Z, In r0 [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 26; 27] ->
  YK11.getr (ms_regs ms1) (Z_to_bv 5 r0) = YK11.getr regs3 (Z_to_bv 5 r0)).
{ intros r0 Hr0. cbn [In] in Hr0.
  repeat (destruct Hr0 as [<- | Hr0]; [o4s_kreg HS3 regs3|]). destruct Hr0. }
lazymatch type of HJ3 with context [with_vm_backing (m_vm_lazy md3) ?mt md3] =>
  set (md5 := with_vm_backing (m_vm_lazy md3) mt md3) in * end.
destruct INV4 as (HLC4 & HGA4 & HSL4 & HRV4).
pose proof HLC4 as (HC4 & HFR4 & HSP4 & HFSH4 & HOPOK4 & He4 & HMET4 & R19_4).
assert (HLC5 : lc_lcore B MT cx op true false (lo_k op) ly2 S2 W2 (ms_regs ms1) (ms_mem ms1) md5 e1).
{ split.
  - apply (lc_core_kept_run B MT XL RLO RHI cx ly2 S2 W2 regs3 mem3 md3 e1 ly2 S2 W2 (ms_regs ms1) (ms_mem ms1)
      md5 e1 HB HC4 HJ3 eq_refl (Permutation_refl _)).
    + intros r0 Hr0. apply HK5. cbn [In] in Hr0 |- *. tauto.
    + intros a _. exact (KR3a a).
    + intros i _. exact (KR3a (l_p cx + i)).
    + intros a _. exact (KR3a a).
    + intros a _ Hp. exact (GR5 a Hp).
  - split.
    { destruct HFR4 as (F18 & F26). split.
      - exact (eq_trans (HK5 18 ltac:(cbn [In]; tauto)) F18).
      - exact (eq_trans (HK5 26 ltac:(cbn [In]; tauto)) F26). }
    split.
    { apply (lc_spills_kept cx (lf_spill_loop (lc_F cx)) (aview segs (w_H W2) mem3)
        (aview segs (w_H W2) (ms_mem ms1))); [|intros a _; exact (KR3a a) | exact HSP4].
      intros o Ho. pose proof (lf_spill_vals (lc_F cx) ltac:(lia) ltac:(unfold LF_FBYTES; lia)) as SV.
      rewrite Forall_forall in SV. destruct (SV o Ho) as (_ & _ & Ho1 & Ho2). lia. }
    split.
    { apply (lc_fsh_kept cx (aview segs (w_H W2) mem3) (aview segs (w_H W2) (ms_mem ms1)) true false);
        [intros a _; exact (KR3a a) | exact HFSH4]. }
    split; [exact HOPOK4|]. split; [exact He4|]. split; [exact HMET4|].
    exact (eq_trans (HK5 19 ltac:(cbn [In]; tauto)) R19_4). }
pmkst HS3.
apply SRr_ret.
rewrite Forall_forall in HRV4.
pose proof (HRV4 (21, w64 (l_p cx + TOP.fi_off (rw_c (o4r_rvw cx op)))) ltac:(unfold o4r_rv; cbn [In]; tauto))
  as U21.
pose proof (HRV4 (27, w64 (TOP.fi_n (rw_c (o4r_rvw cx op)))) ltac:(unfold o4r_rv; cbn [In]; tauto)) as U27.
pose proof (HRV4 (20, w64 (lc_F cx + 32)) ltac:(unfold o4r_rv; cbn [In]; tauto)) as U20.
pose proof (HRV4 (22, w64 1) ltac:(unfold o4r_rv; cbn [In]; tauto)) as U22.
cbn [fst snd] in U21, U27, U20, U22.
assert (V27 : YK11.getr (ms_regs ms1) (Z_to_bv 5 27) = w64 (TOP.fi_n (rw_c (o4r_rvw cx op))))
  by exact (eq_trans (HK5 27 ltac:(cbn [In]; tauto)) U27).
assert (V20 : YK11.getr (ms_regs ms1) 20 = w64 (lc_F cx + 32))
  by exact (eq_trans (HK5 20 ltac:(cbn [In]; tauto)) U20).
assert (V22 : YK11.getr (ms_regs ms1) 22 = w64 1)
  by exact (eq_trans (HK5 22 ltac:(cbn [In]; tauto)) U22).
o4s_reg HS3 (Z_to_bv 5 24) (w64 (l_p cx + TOP.fi_off (rw_c (o4r_rvw cx op)))) V24 ltac:(o4s_atom regs3 U21).
exists ly2, S2, (ms_regs ms1), (ms_mem ms1), md5, e1, B3, (rw_c (o4r_rvw cx op)).
split; [unfold lc_cfg; rewrite <- o4s_base; reflexivity|].
split; [exact Hopc|].
split; [exact HLC5|].
split.
{ unfold lc_tw. apply (tw_kept TMAP_B (aview segs (w_H W2) mem3)); [exact HTW3 | intros x _; exact (KR3a x)]. }
split; [exact M4|].
split; [exact MOP|].
split; [split; [exact V24 | exact V27]|].
split; [exact V20 | exact V22].
Qed.

Lemma lc_op4r_ok : lc_op4r_stmt B MT XL RLO RHI.
Proof.
intros HP cx op W c HB HSUB.
eapply SRr_bind; [exact (o4r_seg_a HP cx op W c HB HSUB)|].
intros W1 c1 _ HC. exact (o4r_seg_b HP cx op W1 c1 HB HC).
Qed.

End seg.
