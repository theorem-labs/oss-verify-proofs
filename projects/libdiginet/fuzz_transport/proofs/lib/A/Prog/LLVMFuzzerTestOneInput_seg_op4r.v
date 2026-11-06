(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths and module names changed; 1494 of its 1575 lines of code are new or changed and 1058 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_op4r: Lemma lc_op4r_ok : lc_op4r_stmt (lib/A/Prog/LLVMFuzzerTestOneInput_segs.v), the
   raw arm of op 4 of LLVMFuzzerTestOneInput in fuzz_transport.asan, offsets +0xb0c .. +0xc68 of the listing
   lib/A/Prog/DgnTransportList.v (0x81d70 .. 0x81ecc), from the cut SUBR to the cut S4.

   What the code does.
     +0xb0c .. +0xbe0  the u16: `beqz s3` (no byte left: lo = hi = 0); else the checked load of the byte at s8 and,
                       when a second byte is left (`bne s3, 1`), the checked load of the byte at s8 + 1; a1 = the
                       bytes left after it, s8 = the cursor after it;
     +0xbe4 .. +0xc34  w = hi << 8 | lo, w mod 25 by the compiler's multiply and shifts, `and` with 0xffff (the spill
                       slot at s1 + 136), `bltu a2, a1` (the take's min with the bytes left: t), s3 = s8 + t,
                       s7 = a1 - t, s6 = c (the spill slot at s1 + 168);
     +0xc38 .. +0xc44  `sb a2, 24(s6)` (c.len = t, a byte of the class-2 frame), a0 = c, a1 = s8, the call of
                       __asan_memcpy (c, the input bytes at the cursor, t);
     +0xc48 .. +0xc54  a0 = g_s, a1 = c, the call of diginet_session_submit (G-form callee, the same G journal);
     +0xc58 .. +0xc64  a1 = its result, a0 = c, a2 = the queue length before (the spill slot at s1 + 144), the call
                       of check_refusal_submit (a leaf);
     +0xc68            `j` to the settle call at +0x12c8 (S4).

   How it is proved. Runs of lib/A/Prog/PaShadow.v's token engine over the listing, the memcpy through
   TransportGCg.v gx_intrin_at, diginet_session_submit by its statement lp_submit, check_refusal_submit through
   TransportGCg.v gx_call_leaf and DgnTransportLeafb.v decode_leafb_journal. The runs of the u16 and of the take write
   nothing and are run by DgnBcScan.v bcs_run (the memory after the run is the memory before); the store and the runs
   between the calls are run over the G journal (TransportGRunA.v paj_run_x / paj_run_to_x). The two checked byte
   loads of the u16 are decided by the token engine from the shadow entry of the input bytes read (the input block's
   shadow, YCbq.v range_addressable_of_block' through DgnTransportCg.v trans_src_ok_rd), so the reports at 0x82c40 and
   0x82c64 are not reached. The model's Some of the operation comes from TSim/LoopOk.v op_ok at the start facts
   lc_opok (the stream fun _ => 1: op 4 receives nothing), read through LLVMFuzzerTestOneInput_st.v lc_op4_eq and
   lc_submit_raw_eq; settle keeps its world (lc_settle_world). The core is carried across the store and the memcpy
   (the frame's bytes change only in c) by o4_core_kept, the port of lc_core_kept whose frame clause is the frame's
   presence and its last word; from the cut after the memcpy to S4 by o4b_inv_kept, the call kit of
   LLVMFuzzerTestOneInput_seg_op4sub.v (o4s_inv_kept over lc_core_kept) with s7 carried. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YG0s YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0 ACfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA TWorldG TWorldA TransportGNotice TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnBcScan.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TCb TSess0 TOps TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Agree QueueFacts LoopOk LinksProof.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LLVMFuzzerTestOneInput_seg_op4sub.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module O4W := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module O4C := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module O4S0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module O4P := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module O4AG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.Agree.
Module O4QF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.QueueFacts.
Module O4LOK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.LoopOk.
Module O4LP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.LinksProof.
Module O4DS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module O4BY := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Bytes.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The model                                                        *)
(* ------------------------------------------------------------------ *)

(* The raw arm's model steps, from the Some LoopOk.op_ok gives at the start facts: diginet_session_submit,
   check_refusal_submit and settle 0 (which keeps its world), and the operation's equation at every stream. *)
Lemma o4_model : forall (D B0 B1 : list byte) (c0 : O4P.fuzz_in) (ops : Z) (k0 : nat),
  O4AG.agree timg_A ops B0 -> 0 <= ops < O4C.OPS_MAX -> O4QF.fuzz_in_ok D c0 -> O4P.fi_n c0 <> 0 ->
  Z.of_nat k0 <= ops -> lc_opc D c0 = 4 -> O4C.op_begin_m B0 = Some (B1, tt) -> O4W.g_raw B1 <> 0 ->
  let kd := lc_sub_kd D (lc_oc D c0) in
  let rv := lc_raw_vals D (sv_c kd) in
  let cs := lc_raw_cs D rv (sv_display kd) (sv_key kd) in
  exists B2 r B3, O4S0.diginet_session_submit_m B1 cs = Some (B2, r) /\
    O4C.check_refusal_submit_m B2 cs r (O4W.S_queued B0) = Some (B3, tt) /\
    O4C.settle_m B3 0 = Some (B3, tt) /\
    (forall A, O4P.LLVMFuzzerTestOneInput_op_m timg_A B0 A D c0 k0 = Some (B3, (rw_c rv, k0))).
Proof.
intros D B0 B1 c0 ops k0 HA Hops Hc Hn Hk Ho HOB HR kd rv cs.
destruct (O4LOK.op_ok O4LP.links_holds timg_A ops B0 (fun _ => 1) D c0 k0 HA Hops Hc Hn ltac:(lia) ltac:(lia))
  as (Bx & cx & kx & E & _).
rewrite (lc_op4_eq timg_A B0 (fun _ => 1) D c0 k0 Ho), (lc_submit_raw_eq B0 B1 D (lc_oc D c0) HOB HR) in E.
cbv zeta in E. fold kd rv cs in E.
destruct (O4S0.diginet_session_submit_m B1 cs) as [[B2 r]|] eqn:E2; [|discriminate E].
destruct (O4C.check_refusal_submit_m B2 cs r (O4W.S_queued B0)) as [[B3 u3]|] eqn:E3; [|discriminate E].
destruct (O4C.settle_m B3 0) as [[B4 u4]|] eqn:E4; [|discriminate E].
pose proof (lc_settle_world B3 B4 0 u4 E4) as EB. subst B4. destruct u3, u4.
exists B2, r, B3. split; [first [exact E2 | reflexivity]|]. split; [exact E3|]. split; [exact E4|].
intros A. rewrite (lc_op4_eq timg_A B0 A D c0 k0 Ho), (lc_submit_raw_eq B0 B1 D (lc_oc D c0) HOB HR).
cbv zeta. fold kd rv cs. rewrite E2, E3, E4. reflexivity.
Qed.

(* The cursor: the three bytes of lc_sub_kd keep it in range. *)
Lemma o4_kd_ok : forall D c1, O4QF.fuzz_in_ok D c1 -> O4QF.fuzz_in_ok D (sv_c (lc_sub_kd D c1)).
Proof.
intros D c1 H. unfold lc_sub_kd.
destruct (O4QF.fuzz_u8_ok D c1 H) as (c1' & kb & E1 & H1 & _). rewrite E1.
destruct (O4QF.fuzz_u8_ok D c1' H1) as (c2 & ab & E2 & H2 & _). rewrite E2.
destruct (O4QF.fuzz_u8_ok D c2 H2) as (c3 & db & E3 & H3 & _). rewrite E3. exact H3.
Qed.

Lemma o4_oc_ok : forall D c0, O4QF.fuzz_in_ok D c0 -> O4QF.fuzz_in_ok D (lc_oc D c0).
Proof.
intros D c0 H. unfold lc_oc. destruct (O4QF.fuzz_u8_ok D c0 H) as (c1 & v & E1 & H1 & _). rewrite E1. exact H1.
Qed.

Lemma o4_at8_range : forall (l : list byte) i, 0 <= O4DS.at8 l i < 256.
Proof.
intros l i. unfold O4DS.at8, O4DS.bz. pose proof (bv_unsigned_in_range 8 (nth i l (O4DS.b8 0))) as R.
change (bv_modulus 8) with 256 in R. exact R.
Qed.

(* fuzz_u16 at a cursor with 0, 1 and at least 2 bytes left. *)
Lemma o4_u16_0 : forall D c, O4P.fi_n c = 0 -> O4P.fuzz_u16_m D c = (c, 0).
Proof.
intros D c H. unfold O4P.fuzz_u16_m, O4P.fuzz_u8_m. rewrite H. cbn. rewrite H. reflexivity.
Qed.

Lemma o4_u16_1 : forall D c, O4P.fi_n c = 1 ->
  O4P.fuzz_u16_m D c = (O4P.FuzzIn (O4P.fi_off c + 1) 0, O4DS.at8 D (Z.to_nat (O4P.fi_off c))).
Proof.
intros D c H. unfold O4P.fuzz_u16_m, O4P.fuzz_u8_m. rewrite H. cbn [Z.eqb O4P.fi_n O4P.fi_off].
replace (1 - 1) with 0 by lia. cbn [Z.eqb].
pose proof (o4_at8_range D (Z.to_nat (O4P.fi_off c))) as R. unfold O4DS.at8 in *.
f_equal. rewrite Z.shiftl_0_l, Z.lor_0_r. apply Z.mod_small. lia.
Qed.

Lemma o4_u16_2 : forall D c, 2 <= O4P.fi_n c ->
  O4P.fuzz_u16_m D c = (O4P.FuzzIn (O4P.fi_off c + 2) (O4P.fi_n c - 2),
    O4DS.at8 D (Z.to_nat (O4P.fi_off c)) + 256 * O4DS.at8 D (Z.to_nat (O4P.fi_off c + 1))).
Proof.
intros D c H. unfold O4P.fuzz_u16_m, O4P.fuzz_u8_m.
rewrite (proj2 (Z.eqb_neq (O4P.fi_n c) 0) ltac:(lia)). cbn [O4P.fi_n O4P.fi_off].
rewrite (proj2 (Z.eqb_neq (O4P.fi_n c - 1) 0) ltac:(lia)).
pose proof (o4_at8_range D (Z.to_nat (O4P.fi_off c))) as R0.
pose proof (o4_at8_range D (Z.to_nat (O4P.fi_off c + 1))) as R1. unfold O4DS.at8 in *.
f_equal; [f_equal; lia|].
rewrite O4BY.lor_shiftl8_add by lia. apply Z.mod_small. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The take's arithmetic                                            *)
(* ------------------------------------------------------------------ *)

(* a2 at the `bltu` of +0xc24, as the engine leaves it from a2 = lo (atom 12), a3 = hi (atom 13) and the spill
   slot 0xffff (atom 32): ((hi << 8 | lo) mod 25) & 0xffff, by the multiply by 18351 and the shifts. *)
Definition o4_W : sv := SAlu ALU_OR (SAlu ALU_SLL (SOff 13 0) (SLit 8)) (SOff 12 0).
Definition o4_Q : sv := SAlu ALU_SRL (SMd M_MUL o4_W (SLit 18351)) (SLit 16).
Definition o4_TAKE : sv :=
  SAlu ALU_AND
    (SAlu ALU_SUB o4_W
       (SMd M_MUL
          (SAlu ALU_SRL
             (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_SUB o4_W o4_Q) (SLit 48)) (SLit 49)) o4_Q)
             (SLit 4))
          (SLit 25)))
    (SOff 32 0).

Definition o4_Elh (lo hi : Z) : env :=
  mkEnv (fun n => if (n =? 12)%nat then Z_to_bv 64 lo else if (n =? 13)%nat then Z_to_bv 64 hi
                  else Z_to_bv 64 65535) (fun _ => []).
Definition o4_take_chk : bool :=
  forallb (fun lo => forallb (fun hi =>
    Z.eqb (bv_unsigned (sv_denot (o4_Elh lo hi) o4_TAKE)) ((lo + 256 * hi) mod 25))
      (map Z.of_nat (seq 0 256))) (map Z.of_nat (seq 0 256)).
Lemma o4_take_chk_ok : o4_take_chk = true.
Proof. vm_compute. reflexivity. Qed.

Lemma o4_take_den : forall (E : env) lo hi,
  ew E 12 = Z_to_bv 64 lo -> ew E 13 = Z_to_bv 64 hi -> ew E 32 = Z_to_bv 64 65535 ->
  0 <= lo < 256 -> 0 <= hi < 256 ->
  sv_denot E o4_TAKE = Z_to_bv 64 ((lo + 256 * hi) mod 25).
Proof.
intros E lo hi H12 H13 H32 Hlo Hhi.
assert (Eq : sv_denot E o4_TAKE = sv_denot (o4_Elh lo hi) o4_TAKE).
{ unfold o4_TAKE, o4_Q, o4_W. cbn [sv_denot ew o4_Elh Nat.eqb]. rewrite H12, H13, H32. reflexivity. }
assert (Hv : bv_unsigned (sv_denot (o4_Elh lo hi) o4_TAKE) = (lo + 256 * hi) mod 25).
{ pose proof o4_take_chk_ok as K. unfold o4_take_chk in K. rewrite forallb_forall in K.
  assert (Il : In lo (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat lo). split; [lia | apply in_seq; lia]. }
  assert (Ih : In hi (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat hi). split; [lia | apply in_seq; lia]. }
  specialize (K lo Il). rewrite forallb_forall in K. specialize (K hi Ih). apply Z.eqb_eq in K. exact K. }
rewrite Eq. apply bv_eq. rewrite Hv, Z_to_bv_unsigned. unfold bv_wrap.
pose proof (Z.mod_pos_bound (lo + 256 * hi) 25 ltac:(lia)) as M. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small ((lo + 256 * hi) mod 25)) by lia. reflexivity.
Qed.

Lemma o4_den_alu : forall (E : env) op a b, sv_denot E (SAlu op a b) = alu64 op (sv_denot E a) (sv_denot E b).
Proof. reflexivity. Qed.

Lemma o4_add_den : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
intros a b. apply bv_eq. cbn [alu64 alu]. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma o4_sub_den : forall a b, alu64 ALU_SUB (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof.
intros a b. apply bv_eq. cbn [alu64 alu]. rewrite bv_sub_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap. rewrite <- Zminus_mod. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The engine segments that write nothing                           *)
(* ------------------------------------------------------------------ *)

(* s10 holds the shadow base; the shadow band the token engine is told about is DgnBcScan.v bcs_Bspan. *)
Definition o4_Bx : sv := SOff 26 0.
Definition o4_PTRHI : Z := 140737488355324.
Definition o4_PTR : afact := mkAF 4096 o4_PTRHI 0.

(* +0xb0c with no byte left. *)
Definition o4_ss0 : sstate := mkSS LO_SUBR sr_atoms [] None (mkFacts [(26%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []).
(* +0xb0c with one byte left: the byte at s8 as atom 32, the shadow entry of [s8, s8 + 1). *)
Definition o4_rg1 : YP09.region := YP09.mkRegion (Some 24%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition o4_G1 : facts := mkFacts [(26%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (24%nat, o4_PTR);
  (32%nat, mkAF 0 255 0)] [] [].
Definition o4_ss1 : sstate := mkSS LO_SUBR sr_atoms [o4_rg1] None o4_G1.
Definition o4_SH1 : list shent := [mkSHE 24 0 1].
(* +0xb0c with two bytes or more left: the bytes at s8 and s8 + 1 as atoms 32, 33, the shadow entry of
   [s8, s8 + 2). *)
Definition o4_rg2 : YP09.region := YP09.mkRegion (Some 24%nat) 0 2 0 0
  [YP09.mkChunk 0 (CVal 1 (SOff 32 0)); YP09.mkChunk 1 (CVal 1 (SOff 33 0))].
Definition o4_G2 : facts := mkFacts [(26%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (24%nat, o4_PTR);
  (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0)] [] [].
Definition o4_ss2 : sstate := mkSS LO_SUBR sr_atoms [o4_rg2] None o4_G2.
Definition o4_SH2 : list shent := [mkSHE 24 0 2].
(* +0xbe4, the join of the u16: a1, a2 = lo, a3 = hi as registers; the spill slots s1 + 136 (0xffff, atom 32) and
   s1 + 168 (c, atom 33). *)
Definition O4_JOIN : Z := 0xbe4.
Definition O4_STORE : Z := 0xc38.
Definition o4_rgJ : YP09.region := YP09.mkRegion (Some 9%nat) 136 176 0 0
  [YP09.mkChunk 136 (CVal 8 (SOff 32 0)); YP09.mkChunk 168 (CVal 8 (SOff 33 0))].
Definition o4_GJ : facts := mkFacts [(26%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (12%nat, mkAF 0 255 0);
  (13%nat, mkAF 0 255 0); (11%nat, mkAF 0 67108864 0); (32%nat, mkAF 65535 65535 0)] [] [].
Definition o4_ssJ : sstate := mkSS O4_JOIN sr_atoms [o4_rgJ] None o4_GJ.

(* The registers each segment keeps. *)
Definition o4_kU : list (bv 5) := [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 25%bv;
  26%bv; 27%bv].
Definition o4_kT : list (bv 5) := [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 24%bv; 25%bv; 26%bv; 27%bv].
Definition o4_keep (r r' : bvmap 5 word) (l : list (bv 5)) : Prop := forall x, In x l -> YK11.getr r' x = YK11.getr r x.
Lemma o4_kk : forall (r0 r1 r2 : bvmap 5 word) x, o4_keep r0 r1 o4_kU -> o4_keep r1 r2 o4_kT ->
  In x o4_kU -> In x o4_kT -> YK11.getr r2 x = YK11.getr r0 x.
Proof. intros r0 r1 r2 x K1 K2 H1 H2. rewrite (K2 x H2). exact (K1 x H1). Qed.

(* One run to the pc stop, or to the next branch the engine cannot decide (DgnBcScan.v bcs_step at s10's shadow
   base). *)
Ltac o4_step SH stop :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?E ?ss (restrict (w_H ?W) ?ms) |- SRr _ _ (mkCfg _ ?md) ?Q =>
    let K := eval vm_compute in (run_K A_LIM o4_Bx SH ss) in
    let rr := eval vm_compute in (sym_run_toN_pi_tok transport_tpi transport_tw K o4_Bx bcs_Bspan SH FUEL stop ss) in
    lazymatch rr with
    | (?st', ?res) =>
      lazymatch goal with
      | HSH : sh_ok _ _ _ E _, HEI : img_env _ _ E, HAG : env_agree 512 ?E0 E |- _ =>
        apply (bcs_run o4_Bx bcs_Bspan SH W E ss ms md K stop st' res Q ltac:(unfold A_LIM; lia) HEI HS HSH
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
Ltac o4_branch SH :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?E ?ss (restrict (w_H ?W) ?ms) |- SRr _ _ (mkCfg _ ?md) ?Q =>
    let K := eval vm_compute in (run_K A_LIM o4_Bx SH ss) in
    let why := psym_why_tok transport_tpi transport_tw K o4_Bx bcs_Bspan SH (start K o4_Bx bcs_Bspan SH ss) in
    lazymatch why with
    | SR_branch ?c ?a ?b =>
      apply (paj_branch (PI := PI_transport) W E ss ms md Q c a b HS); clear HS;
      let Hc := fresh "Hc" in intros Hc HS
    end
  end.

(* The registers of l a run kept, from the entry registers r0 (env Eimg (Ereg r0 ex)); DgnBcScan.v bcs_kr. *)
Ltac o4_kr r0 ex l KR :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?Wx) ?msx), HAG : env_agree 512 _ ?Ex |- _ =>
    pose proof (regs_kept_of_st_ok_pi Ex ssx (restrict (w_H Wx) msx) r0 ex l HS (bcs_agree32 r0 ex Ex HAG)
      ltac:(vm_compute; reflexivity)) as KR
  end.

Ltac o4_kin := unfold o4_kU, o4_kT; cbn [In];
  repeat (first [left; first [reflexivity | apply bv_eq; reflexivity] | right]).

Section ro. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).
Local Abbreviation o4_at pc r mem md :=
  (mkCfg (@YK11.mkst fx r (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs)) md).

Definition o4_E (r : bvmap 5 word) (ex : list word) : env := Eimg (PI := PI_transport) (Ereg r ex).

Lemma o4_E_ex : forall r ex i, (i < 8)%nat -> ew (o4_E r ex) (32 + i) = nth i ex (Z_to_bv 64 0).
Proof. intros r ex i Hi. unfold o4_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.

(* The entry states. *)
Lemma o4_entry0 : forall (W : world segs) r mem, YK11.getr r 26 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (o4_E r []) o4_ss0
    (restrict (w_H W) (@YK11.mkst fx r (Z_to_bv 64 (BASE + LO_SUBR)) mem (YK11.seg_rom segs))).
Proof.
intros W r mem R26.
assert (U26 : bv_unsigned (ew (o4_E r []) 26) = SHADOW_OFF)
  by (unfold o4_E; rewrite (bcs_ew_reg r _ 26 26%bv ltac:(lia) eq_refl), R26; unfold w64;
      apply unsigned_lit_small; unfold SHADOW_OFF; lia).
rewrite restrict_mkst_fx. unfold o4_ss0. apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U26. rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; try exact I; lia.
Qed.

Lemma o4_entry1 : forall (W : world segs) r mem a b0, YK11.getr r 26 = w64 SHADOW_OFF -> YK11.getr r 24 = w64 a ->
  4096 <= a -> a + 1 <= o4_PTRHI -> 0 <= b0 < 256 ->
  val_mem segs (mrestrict (w_H W) mem) a 1 b0 ->
  st_ok_pi segs VAL (o4_E r [w64 b0]) o4_ss1
    (restrict (w_H W) (@YK11.mkst fx r (Z_to_bv 64 (BASE + LO_SUBR)) mem (YK11.seg_rom segs))).
Proof.
intros W r mem a b0 R26 R24 Ha1 Ha2 HB0 V0. unfold o4_PTRHI in Ha2.
assert (E32 : ew (o4_E r [w64 b0]) 32 = w64 b0) by exact (o4_E_ex r [w64 b0] 0 ltac:(cbn; lia)).
assert (U26 : bv_unsigned (ew (o4_E r [w64 b0]) 26) = SHADOW_OFF)
  by (unfold o4_E; rewrite (bcs_ew_reg r _ 26 26%bv ltac:(lia) eq_refl), R26; unfold w64;
      apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U24 : bv_unsigned (ew (o4_E r [w64 b0]) 24) = a)
  by (unfold o4_E; rewrite (bcs_ew_reg r _ 24 24%bv ltac:(lia) eq_refl), R24; unfold w64;
      apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew (o4_E r [w64 b0]) 32) = b0) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold o4_ss1. apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold o4_rg1, YP09.region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U24.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (bcs_chunk1 _ _ 32 a 0 a b0); [exact E32 | lia | lia | exact V0].
- exact (conj I I).
- unfold facts_ok, o4_G1. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok, o4_PTR, o4_PTRHI. cbn [af_lo af_hi af_al2].
  rewrite U26, U24, U32. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF.
  repeat split; try exact I; lia.
Qed.

Lemma o4_entry2 : forall (W : world segs) r mem a b0 b1, YK11.getr r 26 = w64 SHADOW_OFF -> YK11.getr r 24 = w64 a ->
  4096 <= a -> a + 2 <= o4_PTRHI -> 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  val_mem segs (mrestrict (w_H W) mem) a 1 b0 -> val_mem segs (mrestrict (w_H W) mem) (a + 1) 1 b1 ->
  st_ok_pi segs VAL (o4_E r [w64 b0; w64 b1]) o4_ss2
    (restrict (w_H W) (@YK11.mkst fx r (Z_to_bv 64 (BASE + LO_SUBR)) mem (YK11.seg_rom segs))).
Proof.
intros W r mem a b0 b1 R26 R24 Ha1 Ha2 HB0 HB1 V0 V1. unfold o4_PTRHI in Ha2.
assert (E32 : ew (o4_E r [w64 b0; w64 b1]) 32 = w64 b0) by exact (o4_E_ex r [w64 b0; w64 b1] 0 ltac:(cbn; lia)).
assert (E33 : ew (o4_E r [w64 b0; w64 b1]) 33 = w64 b1) by exact (o4_E_ex r [w64 b0; w64 b1] 1 ltac:(cbn; lia)).
assert (U26 : bv_unsigned (ew (o4_E r [w64 b0; w64 b1]) 26) = SHADOW_OFF)
  by (unfold o4_E; rewrite (bcs_ew_reg r _ 26 26%bv ltac:(lia) eq_refl), R26; unfold w64;
      apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U24 : bv_unsigned (ew (o4_E r [w64 b0; w64 b1]) 24) = a)
  by (unfold o4_E; rewrite (bcs_ew_reg r _ 24 24%bv ltac:(lia) eq_refl), R24; unfold w64;
      apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew (o4_E r [w64 b0; w64 b1]) 32) = b0)
  by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew (o4_E r [w64 b0; w64 b1]) 33) = b1)
  by (rewrite E33; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold o4_ss2. apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold o4_rg2, YP09.region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U24.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + apply (bcs_chunk1 _ _ 32 a 0 a b0); [exact E32 | lia | lia | exact V0].
  + apply (bcs_chunk1 _ _ 33 a 1 (a + 1) b1); [exact E33 | lia | lia | exact V1].
- exact (conj I I).
- unfold facts_ok, o4_G2. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok, o4_PTR, o4_PTRHI. cbn [af_lo af_hi af_al2].
  rewrite U26, U24, U32, U33. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF.
  repeat split; try exact I; lia.
Qed.

(* The shadow entry [s8, s8 + k) inside the addressable range [a, a + n). *)
Lemma o4_shok : forall (W : world segs) r mem ex a n q k,
  YK11.getr r 24 = w64 q -> YK11.getr r 26 = w64 SHADOW_OFF -> 0 <= q < 2 ^ 64 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n -> a <= q -> q + k <= a + n -> 0 <= k ->
  (forall x, a <= x < a + n -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)) ->
  sh_ok segs o4_Bx [mkSHE 24 0 k] (o4_E r ex) (mrestrict (w_H W) mem).
Proof.
intros W r mem ex a n q k R24 R26 Hq HRA Ha1 Ha2 Hk Happ.
apply Forall_cons; [|apply Forall_nil].
apply (shent_ok_of_range segs (w_H W) mem (o4_E r ex) o4_Bx 24%nat a n q 0 k).
- exact HRA.
- unfold o4_Bx. apply U_atom; [|unfold SHADOW_OFF; lia].
  unfold o4_E. rewrite (bcs_ew_reg r _ 26 26%bv ltac:(lia) eq_refl). exact R26.
- apply U_atom; [|lia]. unfold o4_E. rewrite (bcs_ew_reg r _ 24 24%bv ltac:(lia) eq_refl). exact R24.
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. apply Happ. lia.
Qed.

(* +0xb0c .. +0xbe0: the u16 at the cursor (s8 / s3), up to +0xbe4 with a1 = the bytes left after it,
   a2 = lo, a3 = hi and s8 = the cursor after it. *)
Lemma o4_u16 : forall (W : world segs) (r : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (D : list byte) (p : Z) (c3 : O4P.fuzz_in) (Q : world segs -> config -> Prop),
  YK11.getr r 26 = w64 SHADOW_OFF -> YK11.getr r 24 = w64 (p + O4P.fi_off c3) ->
  YK11.getr r 19 = w64 (O4P.fi_n c3) ->
  O4QF.fuzz_in_ok D c3 -> 4096 <= p -> p + Z.of_nat (length D) <= o4_PTRHI ->
  (forall j, (j < length D)%nat -> val_mem segs (mrestrict (w_H W) mem) (p + Z.of_nat j) 1 (O4DS.at8 D j)) ->
  (0 < length D)%nat -> range_addressable (aview segs (w_H W) mem) SHADOW_OFF p (Z.of_nat (length D)) ->
  (forall x, p <= x < p + Z.of_nat (length D) -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)) ->
  (forall (r' : bvmap 5 word) mat lo hi, o4_keep r r' o4_kU -> 0 <= lo < 256 -> 0 <= hi < 256 ->
     snd (O4P.fuzz_u16_m D c3) = lo + 256 * hi ->
     YK11.getr r' 24 = w64 (p + O4P.fi_off (fst (O4P.fuzz_u16_m D c3))) ->
     YK11.getr r' 11 = w64 (O4P.fi_n (fst (O4P.fuzz_u16_m D c3))) ->
     YK11.getr r' 12 = w64 lo -> YK11.getr r' 13 = w64 hi ->
     SRr segs W (o4_at O4_JOIN r' mem (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr segs W (o4_at LO_SUBR r mem md) Q.
Proof.
intros W r mem md D p c3 Q R26 R24 R19 Hc3 Hp1 Hp2 HV HL HRA HAPP K.
destruct c3 as [off3 n3]. cbn [O4P.fi_off O4P.fi_n] in *.
destruct Hc3 as (Ho0 & Hn0 & Hon). cbn [O4P.fi_off O4P.fi_n] in Ho0, Hn0, Hon.
assert (Hn3 : n3 = 0 \/ n3 = 1 \/ 2 <= n3) by lia.
assert (Rn3 : 0 <= n3 < 2 ^ 64) by (unfold o4_PTRHI in Hp2; lia).
destruct Hn3 as [Hn3 | [Hn3 | Hn3]].
- (* no byte left: lo = hi = 0 *)
  rewrite (o4_u16_0 D (O4P.FuzzIn off3 n3) Hn3) in K. cbn [fst snd O4P.fi_off O4P.fi_n] in K.
  pose proof (o4_entry0 W r mem R26) as HS.
  assert (HSH : sh_ok segs o4_Bx [] (o4_E r []) (mrestrict (w_H W) mem)) by apply Forall_nil.
  assert (HEI : img_env VAL A_LIM (o4_E r [])) by apply Eimg_env.
  pose proof (env_agree_refl 512 (o4_E r [])) as HAG.
  assert (X19 : ew (o4_E r []) 19 = w64 n3)
    by (unfold o4_E; rewrite (bcs_ew_reg r _ 19 19%bv ltac:(lia) eq_refl); exact R19).
  assert (X24 : ew (o4_E r []) 24 = w64 (p + off3))
    by (unfold o4_E; rewrite (bcs_ew_reg r _ 24 24%bv ltac:(lia) eq_refl); exact R24).
  o4_step ([] : list shent) O4_JOIN.
  o4_branch ([] : list shent).
  + o4_step ([] : list shent) O4_JOIN.
    o4_kr r ([] : list word) o4_kU KR.
    bcs_reg HS (24%bv : bv 5) (w64 (p + off3)) Q24
      ltac:(rewrite (bcs_den _ _ 24 _ 0 HAG ltac:(lia) X24 ltac:(unfold o4_PTRHI in Hp2; lia)); f_equal; lia).
    bcs_reg HS (11%bv : bv 5) (w64 n3) Q11 ltac:(rewrite Hn3; reflexivity).
    bcs_reg HS (12%bv : bv 5) (w64 0) Q12 ltac:(reflexivity).
    bcs_reg HS (13%bv : bv 5) (w64 0) Q13 ltac:(reflexivity).
    bcs_shape.
    apply (K _ _ 0 0 KR ltac:(lia) ltac:(lia) ltac:(lia)); [exact Q24 | exact Q11 | exact Q12 | exact Q13].
  + exfalso. rewrite branch_eq_U, (bcs_U _ _ 19 n3 HAG ltac:(lia) X19 Rn3), U_lit in Hc by lia.
    apply Z.eqb_neq in Hc. lia.
- (* one byte left: lo = the byte, hi = 0 *)
  rewrite (o4_u16_1 D (O4P.FuzzIn off3 n3) Hn3) in K. cbn [fst snd O4P.fi_off O4P.fi_n] in K.
  assert (Hj : (Z.to_nat off3 < length D)%nat) by lia.
  pose proof (HV _ Hj) as V0. rewrite Z2Nat.id in V0 by lia.
  pose proof (o4_at8_range D (Z.to_nat off3)) as B0.
  set (b0 := O4DS.at8 D (Z.to_nat off3)) in *.
  pose proof (o4_entry1 W r mem (p + off3) b0 R26 R24 ltac:(lia) ltac:(lia) B0 V0) as HS.
  assert (HSH : sh_ok segs o4_Bx o4_SH1 (o4_E r [w64 b0]) (mrestrict (w_H W) mem))
    by (apply (o4_shok W r mem _ p (Z.of_nat (length D)) (p + off3) 1 R24 R26 ltac:(unfold o4_PTRHI in Hp2; lia)
          HRA ltac:(lia) ltac:(lia) ltac:(lia) HAPP)).
  assert (HEI : img_env VAL A_LIM (o4_E r [w64 b0])) by apply Eimg_env.
  pose proof (env_agree_refl 512 (o4_E r [w64 b0])) as HAG.
  assert (X19 : ew (o4_E r [w64 b0]) 19 = w64 n3)
    by (unfold o4_E; rewrite (bcs_ew_reg r _ 19 19%bv ltac:(lia) eq_refl); exact R19).
  assert (X24 : ew (o4_E r [w64 b0]) 24 = w64 (p + off3))
    by (unfold o4_E; rewrite (bcs_ew_reg r _ 24 24%bv ltac:(lia) eq_refl); exact R24).
  assert (X32 : ew (o4_E r [w64 b0]) 32 = w64 b0) by exact (o4_E_ex r [w64 b0] 0 ltac:(cbn; lia)).
  o4_step o4_SH1 O4_JOIN.
  o4_branch o4_SH1.
  + exfalso. rewrite branch_eq_U, (bcs_U _ _ 19 n3 HAG ltac:(lia) X19 Rn3), U_lit in Hc by lia.
    apply Z.eqb_eq in Hc. lia.
  + o4_step o4_SH1 O4_JOIN.
    o4_branch o4_SH1.
    * exfalso. rewrite branch_ne_U, (bcs_U _ _ 19 n3 HAG ltac:(lia) X19 Rn3), U_lit in Hc0 by lia.
      apply negb_true_iff, Z.eqb_neq in Hc0. lia.
    * o4_step o4_SH1 O4_JOIN.
      o4_kr r [w64 b0] o4_kU KR.
      bcs_reg HS (24%bv : bv 5) (w64 (p + (off3 + 1))) Q24
        ltac:(rewrite (bcs_den _ _ 24 _ 1 HAG ltac:(lia) X24 ltac:(unfold o4_PTRHI in Hp2; lia)); f_equal; lia).
      bcs_reg HS (11%bv : bv 5) (w64 0) Q11 ltac:(reflexivity).
      bcs_reg HS (12%bv : bv 5) (w64 b0) Q12
        ltac:(rewrite (bcs_den _ _ 32 _ 0 HAG ltac:(lia) X32 ltac:(lia)); f_equal; lia).
      bcs_reg HS (13%bv : bv 5) (w64 0) Q13 ltac:(reflexivity).
      bcs_shape.
      apply (K _ _ b0 0 KR B0 ltac:(lia) ltac:(lia)); [exact Q24 | exact Q11 | exact Q12 | exact Q13].
- (* two bytes or more left *)
  rewrite (o4_u16_2 D (O4P.FuzzIn off3 n3) Hn3) in K. cbn [fst snd O4P.fi_off O4P.fi_n] in K.
  assert (Hj0 : (Z.to_nat off3 < length D)%nat) by lia.
  assert (Hj1 : (Z.to_nat (off3 + 1) < length D)%nat) by lia.
  pose proof (HV _ Hj0) as V0. rewrite Z2Nat.id in V0 by lia.
  pose proof (HV _ Hj1) as V1. rewrite Z2Nat.id in V1 by lia.
  replace (p + (off3 + 1)) with (p + off3 + 1) in V1 by lia.
  pose proof (o4_at8_range D (Z.to_nat off3)) as B0.
  pose proof (o4_at8_range D (Z.to_nat (off3 + 1))) as B1.
  set (b0 := O4DS.at8 D (Z.to_nat off3)) in *.
  set (b1 := O4DS.at8 D (Z.to_nat (off3 + 1))) in *.
  pose proof (o4_entry2 W r mem (p + off3) b0 b1 R26 R24 ltac:(lia) ltac:(lia) B0 B1 V0 V1) as HS.
  assert (HSH : sh_ok segs o4_Bx o4_SH2 (o4_E r [w64 b0; w64 b1]) (mrestrict (w_H W) mem))
    by (apply (o4_shok W r mem _ p (Z.of_nat (length D)) (p + off3) 2 R24 R26 ltac:(unfold o4_PTRHI in Hp2; lia)
          HRA ltac:(lia) ltac:(lia) ltac:(lia) HAPP)).
  assert (HEI : img_env VAL A_LIM (o4_E r [w64 b0; w64 b1])) by apply Eimg_env.
  pose proof (env_agree_refl 512 (o4_E r [w64 b0; w64 b1])) as HAG.
  assert (X19 : ew (o4_E r [w64 b0; w64 b1]) 19 = w64 n3)
    by (unfold o4_E; rewrite (bcs_ew_reg r _ 19 19%bv ltac:(lia) eq_refl); exact R19).
  assert (X24 : ew (o4_E r [w64 b0; w64 b1]) 24 = w64 (p + off3))
    by (unfold o4_E; rewrite (bcs_ew_reg r _ 24 24%bv ltac:(lia) eq_refl); exact R24).
  assert (X32 : ew (o4_E r [w64 b0; w64 b1]) 32 = w64 b0) by exact (o4_E_ex r [w64 b0; w64 b1] 0 ltac:(cbn; lia)).
  assert (X33 : ew (o4_E r [w64 b0; w64 b1]) 33 = w64 b1) by exact (o4_E_ex r [w64 b0; w64 b1] 1 ltac:(cbn; lia)).
  o4_step o4_SH2 O4_JOIN.
  o4_branch o4_SH2.
  + exfalso. rewrite branch_eq_U, (bcs_U _ _ 19 n3 HAG ltac:(lia) X19 Rn3), U_lit in Hc by lia.
    apply Z.eqb_eq in Hc. lia.
  + o4_step o4_SH2 O4_JOIN.
    o4_branch o4_SH2.
    * o4_step o4_SH2 O4_JOIN.
      o4_kr r [w64 b0; w64 b1] o4_kU KR.
      bcs_reg HS (24%bv : bv 5) (w64 (p + (off3 + 2))) Q24
        ltac:(rewrite (bcs_den _ _ 24 _ 2 HAG ltac:(lia) X24 ltac:(unfold o4_PTRHI in Hp2; lia)); f_equal; lia).
      bcs_reg HS (11%bv : bv 5) (w64 (n3 - 2)) Q11
        ltac:(rewrite (bcs_den _ _ 19 _ (-2) HAG ltac:(lia) X19 Rn3); f_equal; lia).
      bcs_reg HS (12%bv : bv 5) (w64 b0) Q12
        ltac:(rewrite (bcs_den _ _ 32 _ 0 HAG ltac:(lia) X32 ltac:(lia)); f_equal; lia).
      bcs_reg HS (13%bv : bv 5) (w64 b1) Q13
        ltac:(rewrite (bcs_den _ _ 33 _ 0 HAG ltac:(lia) X33 ltac:(lia)); f_equal; lia).
      bcs_shape.
      apply (K _ _ b0 b1 KR B0 B1 eq_refl); [exact Q24 | exact Q11 | exact Q12 | exact Q13].
    * exfalso. rewrite branch_ne_U, (bcs_U _ _ 19 n3 HAG ltac:(lia) X19 Rn3), U_lit in Hc0 by lia.
      apply negb_false_iff, Z.eqb_eq in Hc0. lia.
Qed.

(* The join's entry state. *)
Lemma o4_entryJ : forall (W : world segs) r mem s1 F n4 lo hi,
  YK11.getr r 9 = w64 s1 -> YK11.getr r 26 = w64 SHADOW_OFF -> YK11.getr r 11 = w64 n4 ->
  YK11.getr r 12 = w64 lo -> YK11.getr r 13 = w64 hi ->
  0 <= s1 -> s1 + 176 <= 2 ^ 64 -> 0 <= F + 32 < 2 ^ 64 -> 0 <= lo < 256 -> 0 <= hi < 256 -> 0 <= n4 <= 67108864 ->
  val_mem segs (mrestrict (w_H W) mem) (s1 + 136) 8 65535 -> val_mem segs (mrestrict (w_H W) mem) (s1 + 168) 8 (F + 32) ->
  st_ok_pi segs VAL (o4_E r [w64 65535; w64 (F + 32)]) o4_ssJ
    (restrict (w_H W) (@YK11.mkst fx r (Z_to_bv 64 (BASE + O4_JOIN)) mem (YK11.seg_rom segs))).
Proof.
intros W r mem s1 F n4 lo hi R9 R26 R11 R12 R13 Hs0 Hs1 HF Hlo Hhi Hn V136 V168.
set (E := o4_E r [w64 65535; w64 (F + 32)]).
assert (E32 : ew E 32 = w64 65535) by exact (o4_E_ex r [w64 65535; w64 (F + 32)] 0 ltac:(cbn; lia)).
assert (E33 : ew E 33 = w64 (F + 32)) by exact (o4_E_ex r [w64 65535; w64 (F + 32)] 1 ltac:(cbn; lia)).
assert (EE : forall n (x : bv 5) v, (n < 32)%nat -> Z.of_nat n = bv_unsigned x -> YK11.getr r x = w64 v ->
  0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v).
{ intros n x v Hn32 Hx Hr Hv. unfold E, o4_E. rewrite (bcs_ew_reg r _ n x Hn32 Hx), Hr. unfold w64.
  apply unsigned_lit_small. exact Hv. }
pose proof (EE 9%nat 9%bv s1 ltac:(lia) eq_refl R9 ltac:(lia)) as U9.
pose proof (EE 26%nat 26%bv SHADOW_OFF ltac:(lia) eq_refl R26 ltac:(unfold SHADOW_OFF; lia)) as U26.
pose proof (EE 11%nat 11%bv n4 ltac:(lia) eq_refl R11 ltac:(lia)) as U11.
pose proof (EE 12%nat 12%bv lo ltac:(lia) eq_refl R12 ltac:(lia)) as U12.
pose proof (EE 13%nat 13%bv hi ltac:(lia) eq_refl R13 ltac:(lia)) as U13.
assert (U32 : bv_unsigned (ew E 32) = 65535) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold o4_ssJ. apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold o4_rgJ, YP09.region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + apply (chunk_ok_val segs E _ s1 136 8 (SOff 32 0) 65535).
    * cbn [sv_denot]. rewrite E32, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    * cbn. lia.
    * cbn. lia.
    * exact V136.
  + apply (chunk_ok_val segs E _ s1 168 8 (SOff 33 0) (F + 32)).
    * cbn [sv_denot]. rewrite E33, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    * cbn. lia.
    * cbn. lia.
    * exact V168.
- exact (conj I I).
- unfold facts_ok, o4_GJ. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U26, U12, U13, U11, U32. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF.
  repeat split; try exact I; lia.
Qed.

(* +0xbe4 .. +0xc34: w mod 25, the take's min with the bytes left (t), s3 = s8 + t, s7 = a1 - t, s6 = c, up to the
   store at +0xc38 with a2 = t. *)
Lemma o4_take : forall (W : world segs) (r : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (s1 F n4 lo hi q : Z) (Q : world segs -> config -> Prop),
  YK11.getr r 9 = w64 s1 -> YK11.getr r 26 = w64 SHADOW_OFF -> YK11.getr r 11 = w64 n4 ->
  YK11.getr r 12 = w64 lo -> YK11.getr r 13 = w64 hi -> YK11.getr r 24 = w64 q ->
  0 <= s1 -> s1 + 176 <= 2 ^ 64 -> 0 <= F + 32 < 2 ^ 64 -> 0 <= lo < 256 -> 0 <= hi < 256 -> 0 <= n4 <= 67108864 ->
  0 <= q -> q + n4 < 2 ^ 64 ->
  rdword (aview segs (w_H W) mem) (s1 + 136) = Some 65535 ->
  rdword (aview segs (w_H W) mem) (s1 + 168) = Some (F + 32) ->
  (forall (r' : bvmap 5 word) mat, o4_keep r r' o4_kT ->
     let t := if (lo + 256 * hi) mod 25 <? n4 then (lo + 256 * hi) mod 25 else n4 in
     YK11.getr r' 12 = w64 t -> YK11.getr r' 19 = w64 (q + t) -> YK11.getr r' 23 = w64 (n4 - t) ->
     YK11.getr r' 22 = w64 (F + 32) ->
     SRr segs W (o4_at O4_STORE r' mem (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr segs W (o4_at O4_JOIN r mem md) Q.
Proof.
intros W r mem md s1 F n4 lo hi q Q R9 R26 R11 R12 R13 R24 Hs0 Hs1 HF Hlo Hhi Hn Hq0 Hq1 W136 W168 K.
pose proof (o4_entryJ W r mem s1 F n4 lo hi R9 R26 R11 R12 R13 Hs0 Hs1 HF Hlo Hhi Hn
  (val_mem_of_rdword segs (w_H W) mem _ _ W136) (val_mem_of_rdword segs (w_H W) mem _ _ W168)) as HS.
set (E := o4_E r [w64 65535; w64 (F + 32)]) in HS.
assert (HSH : sh_ok segs o4_Bx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
pose proof (env_agree_refl 512 E) as HAG.
assert (X11 : ew E 11 = w64 n4) by (unfold E, o4_E; rewrite (bcs_ew_reg r _ 11 11%bv ltac:(lia) eq_refl); exact R11).
assert (X12 : ew E 12 = w64 lo) by (unfold E, o4_E; rewrite (bcs_ew_reg r _ 12 12%bv ltac:(lia) eq_refl); exact R12).
assert (X13 : ew E 13 = w64 hi) by (unfold E, o4_E; rewrite (bcs_ew_reg r _ 13 13%bv ltac:(lia) eq_refl); exact R13).
assert (X24 : ew E 24 = w64 q) by (unfold E, o4_E; rewrite (bcs_ew_reg r _ 24 24%bv ltac:(lia) eq_refl); exact R24).
assert (X32 : ew E 32 = w64 65535) by exact (o4_E_ex r [w64 65535; w64 (F + 32)] 0 ltac:(cbn; lia)).
assert (X33 : ew E 33 = w64 (F + 32)) by exact (o4_E_ex r [w64 65535; w64 (F + 32)] 1 ltac:(cbn; lia)).
remember ((lo + 256 * hi) mod 25) as m25 eqn:Em25 in K.
assert (R25 : 0 <= m25 < 25) by (rewrite Em25; apply Z.mod_pos_bound; lia).
o4_step ([] : list shent) O4_STORE.
o4_branch ([] : list shent).
- (* m25 < n4: t = m25 *)
  rewrite branch_ltu_U in Hc. fold o4_W o4_Q o4_TAKE in Hc.
  assert (DT : forall E', env_agree 512 E E' -> sv_denot E' o4_TAKE = w64 m25).
  { intros E' HA'. rewrite Em25. apply o4_take_den.
    - rewrite (bcs_agree_ew E E' 12 HA' ltac:(lia)). exact X12.
    - rewrite (bcs_agree_ew E E' 13 HA' ltac:(lia)). exact X13.
    - rewrite (bcs_agree_ew E E' 32 HA' ltac:(lia)). exact X32.
    - exact Hlo.
    - exact Hhi. }
  unfold U in Hc. rewrite (DT _ HAG), (bcs_den _ _ 11 _ 0 HAG ltac:(lia) X11 ltac:(lia)), Z.add_0_r in Hc.
  unfold w64 in Hc. rewrite !unsigned_lit_small in Hc by lia.
  o4_step ([] : list shent) O4_STORE.
  o4_kr r [w64 65535; w64 (F + 32)] o4_kT KR.
  bcs_reg HS (12%bv : bv 5) (w64 m25) Q12 ltac:(fold o4_W o4_Q o4_TAKE; exact (DT _ HAG)).
  bcs_reg HS (19%bv : bv 5) (w64 (q + m25)) Q19
    ltac:(fold o4_W o4_Q o4_TAKE; rewrite o4_den_alu, (DT _ HAG);
          rewrite (bcs_den _ _ 24 _ 0 HAG ltac:(lia) X24 ltac:(lia)), Z.add_0_r; apply o4_add_den).
  bcs_reg HS (23%bv : bv 5) (w64 (n4 - m25)) Q23
    ltac:(fold o4_W o4_Q o4_TAKE; rewrite o4_den_alu, (DT _ HAG);
          rewrite (bcs_den _ _ 11 _ 0 HAG ltac:(lia) X11 ltac:(lia)), Z.add_0_r; apply o4_sub_den).
  bcs_reg HS (22%bv : bv 5) (w64 (F + 32)) Q22
    ltac:(rewrite (bcs_den _ _ 33 _ 0 HAG ltac:(lia) X33 ltac:(lia)); f_equal; lia).
  bcs_shape.
  apply (K _ _ KR); cbv zeta; try rewrite Hc; [exact Q12 | exact Q19 | exact Q23 | exact Q22].
- (* n4 <= m25: t = n4 *)
  rewrite branch_ltu_U in Hc. fold o4_W o4_Q o4_TAKE in Hc.
  assert (DT : forall E', env_agree 512 E E' -> sv_denot E' o4_TAKE = w64 m25).
  { intros E' HA'. rewrite Em25. apply o4_take_den.
    - rewrite (bcs_agree_ew E E' 12 HA' ltac:(lia)). exact X12.
    - rewrite (bcs_agree_ew E E' 13 HA' ltac:(lia)). exact X13.
    - rewrite (bcs_agree_ew E E' 32 HA' ltac:(lia)). exact X32.
    - exact Hlo.
    - exact Hhi. }
  unfold U in Hc. rewrite (DT _ HAG), (bcs_den _ _ 11 _ 0 HAG ltac:(lia) X11 ltac:(lia)), Z.add_0_r in Hc.
  unfold w64 in Hc. rewrite !unsigned_lit_small in Hc by lia.
  o4_step ([] : list shent) O4_STORE.
  o4_kr r [w64 65535; w64 (F + 32)] o4_kT KR.
  bcs_reg HS (12%bv : bv 5) (w64 n4) Q12
    ltac:(rewrite (bcs_den _ _ 11 _ 0 HAG ltac:(lia) X11 ltac:(lia)); f_equal; lia).
  bcs_reg HS (19%bv : bv 5) (w64 (q + n4)) Q19
    ltac:(rewrite o4_den_alu, (bcs_den _ _ 24 _ 0 HAG ltac:(lia) X24 ltac:(lia));
          rewrite (bcs_den _ _ 11 _ 0 HAG ltac:(lia) X11 ltac:(lia)), !Z.add_0_r, o4_add_den; f_equal; lia).
  bcs_reg HS (23%bv : bv 5) (w64 (n4 - n4)) Q23 ltac:(cbn [sv_denot]; unfold w64; f_equal; lia).
  bcs_reg HS (22%bv : bv 5) (w64 (F + 32)) Q22
    ltac:(rewrite (bcs_den _ _ 33 _ 0 HAG ltac:(lia) X33 ltac:(lia)); f_equal; lia).
  bcs_shape.
  apply (K _ _ KR); cbv zeta; try rewrite Hc; [exact Q12 | exact Q19 | exact Q23 | exact Q22].
Qed.

End ro.

(* ------------------------------------------------------------------ *)
(* 4. Bytes and the command struct                                    *)
(* ------------------------------------------------------------------ *)

Lemma o4_le1 : forall v, 0 <= v < 256 -> le_byte v 1 0 = v.
Proof.
intros v Hv. unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma o4_aview_vm1 : forall (H : word -> bool) (m : word -> option byte) a v,
  val_mem tfibsegs (mrestrict H m) a 1 v -> 0 <= v < 256 -> aview tfibsegs H m a = Some v.
Proof.
intros H m a v V Hv. specialize (V 0%nat ltac:(lia)). cbn [Z.of_nat] in V. rewrite Z.add_0_r in V.
unfold aview. rewrite V. cbn [option_map]. f_equal. rewrite o4_le1 by exact Hv.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hv.
Qed.

Lemma o4_garr8_aview : forall (H : word -> bool) (m : word -> option byte) base (l : list Z) j,
  garr8 tfibsegs (mrestrict H m) base l -> (j < length l)%nat ->
  aview tfibsegs H m (base + Z.of_nat j) = Some (nth j l 0).
Proof. intros H m base l j HG Hj. destruct (HG j Hj) as [V R]. exact (o4_aview_vm1 H m _ _ V R). Qed.

Lemma o4_garr8_of : forall (H : word -> bool) (m : word -> option byte) base (l : list Z),
  (forall j, (j < length l)%nat -> aview tfibsegs H m (base + Z.of_nat j) = Some (nth j l 0) /\ 0 <= nth j l 0 < 256) ->
  garr8 tfibsegs (mrestrict H m) base l.
Proof.
intros H m base l HA j Hj. destruct (HA j Hj) as [E R]. split; [|exact R]. intros k Hk.
assert (Ek : k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold aview in E. destruct (mbyte tfibsegs (mrestrict H m) (base + Z.of_nat j)) as [b|] eqn:Eb;
  cbn [option_map] in E; [|discriminate E].
injection E as E. f_equal. rewrite o4_le1 by exact R. apply bv_eq. rewrite Z_to_bv_unsigned, <- E.
unfold bv_wrap. symmetry. apply Z.mod_small. exact (bv_unsigned_in_range 8 b).
Qed.

Lemma o4_nth_zs : forall (l : list byte) j, nth j (O4W.zs l) 0 = bv_unsigned (nth j l (O4DS.b8 0)).
Proof. intros l j. unfold O4W.zs. rewrite <- (map_nth (fun b : byte => bv_unsigned b) l (O4DS.b8 0) j). reflexivity. Qed.

Lemma o4_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. exact R. Qed.

(* The struct the raw arm hands diginet_session_submit against the one op 4's prologue left in c: the input bytes
   below t, the length byte at 24, the same bytes elsewhere. *)
Lemma o4_cs_shape : forall (D : list byte) off t display key, 0 <= off -> 0 <= t <= 24 ->
  off + t <= Z.of_nat (length D) ->
  let cs := O4P.cmd_struct (O4W.sub D off (Z.to_nat t) ++ repeat (O4DS.b8 0) (Z.to_nat (24 - t))) t display key in
  let cs0 := O4P.cmd_struct (repeat (O4DS.b8 0) 24) 0 display key in
  length cs = 32%nat /\ length cs0 = 32%nat /\
  (forall j, (j < Z.to_nat t)%nat -> nth j cs (O4DS.b8 0) = nth (Z.to_nat off + j) D (O4DS.b8 0)) /\
  nth 24 cs (O4DS.b8 0) = O4DS.b8 t /\
  (forall j, (Z.to_nat t <= j < 32)%nat -> j <> 24%nat -> nth j cs (O4DS.b8 0) = nth j cs0 (O4DS.b8 0)).
Proof.
intros D off t display key Ho Ht Hl cs cs0.
assert (LS : length (O4W.sub D off (Z.to_nat t)) = Z.to_nat t) by (apply TWL.length_sub; lia).
assert (LP : length (O4W.put 4 key) = 4%nat) by (apply TWL.length_put).
assert (LH : length (O4W.sub D off (Z.to_nat t) ++ repeat (O4DS.b8 0) (Z.to_nat (24 - t))) = 24%nat)
  by (rewrite length_app, LS, repeat_length; lia).
assert (LR : length (repeat (O4DS.b8 0) 24) = 24%nat) by apply repeat_length.
assert (LT : forall a b, length ([O4DS.b8 a; O4DS.b8 b; O4DS.b8 0; O4DS.b8 0] ++ O4W.put 4 key) = 8%nat)
  by (intros a b; cbn [length app]; rewrite LP; reflexivity).
unfold cs, cs0, O4P.cmd_struct.
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
- rewrite app_nth2 by (rewrite LH; lia). rewrite (app_nth2 (repeat (O4DS.b8 0) 24)) by (rewrite LR; lia).
  rewrite LH, LR.
  destruct (j - 24)%nat as [|k] eqn:Ek; [lia|]. reflexivity.
Qed.

(* The raw arm's take: from the u16's lo, hi and the cursor after it, t and the cursor after the take. *)
Lemma o4_rv_eq : forall D c3 lo hi c4 t, O4P.fuzz_u16_m D c3 = (c4, lo + 256 * hi) -> 0 <= lo < 256 ->
  0 <= hi < 256 -> 0 <= O4P.fi_n c4 ->
  t = (if (lo + 256 * hi) mod 25 <? O4P.fi_n c4 then (lo + 256 * hi) mod 25 else O4P.fi_n c4) ->
  lc_raw_vals D c3 = mkLrw t (O4P.fi_off c4) t (O4P.FuzzIn (O4P.fi_off c4 + t) (O4P.fi_n c4 - t)).
Proof.
intros D c3 lo hi c4 t E Hlo Hhi Hn Ht. unfold lc_raw_vals. rewrite E. unfold O4P.fuzz_take_m.
change (O4DS.SPEC_CMD_MAX + 1) with 25. cbv beta iota zeta. subst t.
assert (Hm : 0 <= (lo + 256 * hi) mod 25 < 25) by (apply Z.mod_pos_bound; lia).
f_equal. destruct ((lo + 256 * hi) mod 25 <? O4P.fi_n c4) eqn:Elt.
- apply Z.mod_small. lia.
- apply Z.ltb_ge in Elt. apply Z.mod_small. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 5. The core across a step that writes c                            *)
(* ------------------------------------------------------------------ *)

Section kept. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.

(* LLVMFuzzerTestOneInput_st.v lc_core_kept with its frame clause weakened to what lc_core reads of the frame: every
   byte present and the last word (the flag pointer) kept; c's bytes may change. *)
Lemma o4_core_kept : forall cx ly' S' W' regs' mem' md' e (X : Z) ly2 S2 (W2 : world segs) regs2 mem2 md2 e2,
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_core rc B cx ly' S' W' regs' mem' md' e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] LLVMF_STK (lc_sp0 cx) []
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly2 S2 W2 mem2 md2 e2 ->
  frames S2 = frames S' ->
  Permutation (ablocks B ly2 S2) (ablocks B ly' S') ->
  YK11.getr regs2 2 = YK11.getr regs' 2 -> YK11.getr regs2 3 = YK11.getr regs' 3 ->
  YK11.getr regs2 4 = YK11.getr regs' 4 -> YK11.getr regs2 8 = YK11.getr regs' 8 ->
  YK11.getr regs2 9 = YK11.getr regs' 9 ->
  0 <= X <= LLVMF_STK - 336 ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (lc_sp1 cx - X <= a < lc_sp1 cx) ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a) ->
  (forall b m i, In (b, m) (ablocks B ly' S') -> 0 <= i < req_size m ->
     aview segs (w_H W2) mem2 (b + i) = aview segs (w_H W') mem' (b + i)) ->
  (forall a, lc_F cx <= a < lc_F cx + LF_FBYTES -> apresent (w_H W2) mem2 a) ->
  (forall a, lc_F cx + LF_FBYTES - 8 <= a < lc_F cx + LF_FBYTES ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a) ->
  @lc_core rc B cx ly2 S2 W2 regs2 mem2 md2 e2.
Proof.
intros cx ly' S' W' regs' mem' md' e X ly2 S2 W2 regs2 mem2 md2 e2 LAWS HB HC HJ2 HFR2 HP2 Q2 Q3 Q4 Q8 Q9 HX
  KA KB KP KL.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
destruct HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal & HFceil &
  HFpres & HFL & HIN).
pose proof HJ2 as (_ & _ & (memS2 & HJd2 & _) & _).
pose proof HJd2 as (HAR2 & Hly2 & _).
destruct Hly2 as (_ & _ & _ & _ & _ & EF2 & _).
destruct Hstk as (Hceil & Hslo & Hshi & H47).
change (2 ^ 47) with 140737488355328 in H47.
pose proof asan_consts as ((CVlo & CVhi) & _).
assert (KAhi : forall a, lc_sp1 cx <= a <= lc_sp0 cx -> aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a).
{ intros a Ha. apply KA; [change (2 ^ 64) with 18446744073709551616; lia | lia]. }
split; [exact HJ2|].
split; [rewrite HFR2; exact Hfrs|].
split; [exact EF2|].
split; [exact (Permutation_trans HP2 HPERM)|].
split; [rewrite Q2; exact Rsp|].
split; [rewrite Q8; exact R8|].
split; [rewrite Q9; exact R9|].
split; [rewrite Q3; exact Rgp|].
split; [rewrite Q4; exact Rtp|].
split; [exact Hsp1|]. split; [exact Hsp1al|].
split.
{ unfold lc_saved in HSAV |- *. rewrite Forall_forall in HSAV |- *. intros o Ho.
  assert (Hor : 8 <= fst o <= 104).
  { unfold LF_SAVED in Ho. repeat (destruct Ho as [<- | Ho]; [cbn; lia|]). destruct Ho. }
  rewrite (rdword_ext (aview segs (w_H W') mem') (aview segs (w_H W2) mem2) (lc_sp0 cx - fst o))
    by (intros j Hj; apply KAhi; unfold LF_FRAME in Hsp1; lia).
  exact (HSAV o Ho). }
split; [exact HF4096|]. split; [exact HFal|]. split; [exact HFceil|].
split; [exact KP|].
split; [rewrite (rdword_ext (aview segs (w_H W') mem') (aview segs (w_H W2) mem2) (lc_F cx + LF_FBYTES - 8))
          by (intros j Hj; apply KL; lia); exact HFL|].
destruct HIN as (HPAYg & HPAYv).
destruct (Z_lt_le_dec 0 (l_n cx)) as [Hn0 | Hn0].
- pose proof (HINg Hn0) as InP.
  pose proof (req_size_pos (l_n cx) ltac:(lia)) as (Hq1 & Hq2).
  split.
  + apply (lc_garr8_kept (w_H W') (w_H W2) mem' mem2 (l_p cx) _); [|exact HPAYg].
    intros j Hj. rewrite length_map in Hj. destruct Hn as (_ & Hnl). rewrite <- Hnl in Hj.
    exact (KB _ _ j InP ltac:(lia)).
  + intros i Hi. rewrite (KB _ _ i InP ltac:(lia)). exact (HPAYv i Hi).
- destruct Hn as (Hn1 & Hnl). split.
  + destruct (l_pl cx) as [|b0 pl0] eqn:Epl; [apply garr8_nil|]. exfalso. cbn [length] in Hnl. lia.
  + intros i Hi. lia.
Qed.

End kept.

(* ------------------------------------------------------------------ *)
(* 6. The store and the memcpy: from SUBR to the cut after the memcpy *)
(* ------------------------------------------------------------------ *)

(* +0xc38 with the length byte of c (s6 + 24) writable. *)
Definition o4_rgS : YP09.region := YP09.mkRegion (Some 22%nat) 24 25 24 25 [].
(* c lies in application memory above the first page: its window is apart from the (empty) shadow span. *)
Definition o4_ssS : sstate :=
  mkSS O4_STORE sr_atoms [o4_rgS] None (mkFacts [(22%nat, mkAF 4096 140737488355328 0)] [] []).

(* The value of register r in the machine state of a state HS at a callee's entry (st_ok), from its symbolic value. *)
Ltac o4_creg HS r v H tac :=
  lazymatch type of HS with
  | st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg sg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.

Section st. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma o4_entryS : forall (W : world segs) r mem c, YK11.getr r 22 = w64 c -> 4096 <= c <= 140737488355328 ->
  writable_at segs (mrestrict (w_H W) mem) (c + 24) ->
  st_ok_pi segs VAL (o4_E r []) o4_ssS
    (restrict (w_H W) (@YK11.mkst fx r (Z_to_bv 64 (BASE + O4_STORE)) mem (YK11.seg_rom segs))).
Proof.
intros W r mem c R22 Hc0 Hw.
assert (U22 : bv_unsigned (ew (o4_E r []) 22) = c)
  by (unfold o4_E; rewrite (bcs_ew_reg r _ 22 22%bv ltac:(lia) eq_refl), R22; unfold w64;
      apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold o4_ssS. apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold o4_rgS, YP09.region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U22.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. replace (c + o) with (c + 24) by lia. exact Hw.
- exact (conj I I).
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U22. rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; try exact I; lia.
Qed.

End st.

Section seg. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The model's names for the raw arm of operation op of the call cx: the key and display bytes, the take, the struct
   handed to diginet_session_submit, and the queue length before the operation as 144(s1) holds it. *)
Definition o4_kd (cx : lcx) (op : lop) : lsv := lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op)).
Definition o4_rv (cx : lcx) (op : lop) : lrw := lc_raw_vals (l_pl cx) (sv_c (o4_kd cx op)).
Definition o4_cs (cx : lcx) (op : lop) : list byte :=
  lc_raw_cs (l_pl cx) (o4_rv cx op) (sv_display (o4_kd cx op)) (sv_key (o4_kd cx op)).
Definition o4_qv (B0 : list byte) : Z := bv_unsigned (Z_to_bv 64 (bv_swrap 32 (O4W.S_queued B0))).

(* +0xc48, the return of __asan_memcpy: c holds the struct o4_cs with its shadow in scope, the world op_begin's B1,
   144(s1) the queue length before, s3 / s7 the cursor after the take, s6 = c. *)
Definition O4_CPY : Z := 0xc48.
Definition o4_st_cpy (cx : lcx) (op : lop) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' e B1,
    c' = lc_cfg cx O4_CPY regs' mem' md' /\
    lc_opc (l_pl cx) (lo_c op) = 4 /\
    lc_lcore B MT cx op true false (lo_k op) ly' S' W' regs' mem' md' e /\
    O4C.op_begin_m (lo_B op) = Some (B1, tt) /\ O4W.g_raw B1 <> 0 /\ lc_tw W' mem' B1 /\
    garr8 segs (mrestrict (w_H W') mem') (lc_F cx + 32) (O4W.zs (o4_cs cx op)) /\ length (o4_cs cx op) = 32%nat /\
    rdword (aview segs (w_H W') mem') (lc_sp1 cx + 144) = Some (o4_qv (lo_B op)) /\
    lc_cur cx regs' 19 23 (rw_c (o4_rv cx op)) /\
    YK11.getr regs' 20 = w64 LF_S4 /\ YK11.getr regs' 22 = w64 (lc_F cx + 32).

Lemma o4_cfg : forall (cx : lcx) off (r : bvmap 5 word) m md,
  lc_cfg cx off r m md = mkCfg (@YK11.mkst (l_fx cx) r (Z_to_bv 64 (BASE + off)) m (YK11.seg_rom segs)) md.
Proof.
intros cx off r m md. unfold lc_cfg, w64. replace BASE with transport_text by (vm_compute; reflexivity).
reflexivity.
Qed.

(* The frame's shadow bytes lie outside the frame, below alloc_ceiling. *)
Lemma o4_sh_apart : forall F i, 4096 <= F -> F + 256 <= alloc_ceiling ->
  (F + 256 <= kLowShadowBeg \/ kHighMemBeg <= F) -> 0 <= i < 32 ->
  (SHADOW_OFF + F / 8 + i < F \/ F + 256 <= SHADOW_OFF + F / 8 + i) /\ SHADOW_OFF + F / 8 + i < alloc_ceiling.
Proof.
intros F i H0 H1 H2 Hi. pose proof asan_consts as ((CVlo & CVhi) & _).
pose proof (Z.div_mod F 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M.
unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

Lemma o4_shm4 : forall i, 4 <= i < 8 -> nth (Z.to_nat i) (lf_shm true false) 0 = 0.
Proof.
intros i Hi. assert (E : i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
destruct E as [-> | [-> | [-> | ->]]]; reflexivity.
Qed.

Lemma o4_seg_a : lp_prem B MT XL RLO RHI -> forall (cx : lcx) (op : lop) (W : world segs) (c : config),
  lc_base B MT XL RLO RHI cx -> lc_st_subr B MT cx op W c -> SRr segs W c (o4_st_cpy cx op).
Proof.
intros HP cx op W c HB HSUB.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof asan_consts as ((CVlo & CVhi) & _ & _ & _ & _).
assert (EST : ESTACK = 4096) by reflexivity.
destruct HSUB as (ly' & S' & regs0 & mem0 & md0 & e & B1 & -> & HCOM & Hraw & R20).
destruct HCOM as (Ho & HL & HOB & HTW & HC8 & HQ & HCUR).
destruct HL as (HC & HFR & HSP & HFSH & HOPOK & He & HMET & R21).
pose proof HOPOK as (HAGR & Hops & Hc0 & Hn0 & Hk0).
destruct HFR as (R18 & R26).
destruct HCUR as (R24 & R19).
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W regs0 mem0 md0 e HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof HC as (HJ0 & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal &
  HFceil & HFpres & HFL & HIN).
destruct HIN as (HPAY & HPAYv).
destruct Hstk as (Hceil & Hslo & Hshi & H47).
destruct Hn as (Hn26 & Hlen).
change (2 ^ 47) with 140737488355328 in H47.
unfold LF_FBYTES in HFceil. unfold LF_FRAME in Hsp1. change (2 ^ 26) with 67108864 in Hn26.
(* the cursor and the input block *)
change (O4QF.fuzz_in_ok (l_pl cx) (lo_c op)) in Hc0.
assert (HD : (0 < length (l_pl cx))%nat) by (destruct Hc0 as (Ha & Hb & Hc); lia).
pose proof (HINg ltac:(lia)) as Hblk.
destruct (al_blocks _ _ LAWS ly' S' W mem0 md0 (l_p cx) (l_n cx) HARg Hblk) as (_ & Hp4096 & Hpce & _ & _ & _ & _).
pose proof (req_size_pos (l_n cx) ltac:(lia)) as (Hq1 & Hq2).
assert (HINB : forall mm mdx, @AR rc segs B ly' S' W mm mdx -> decode_rd_ok W mm (l_p cx) (l_n cx)).
{ intros mm mdx HARx. apply (trans_src_ok_rd B LAWS ly' S' W mm mdx (l_p cx) (l_n cx) HARx); [|lia].
  left. exists (l_p cx), (l_n cx). split; [exact Hblk | lia]. }
destruct (HINB mem0 md0 HARg) as (HV0 & HRA0 & HHV0 & HAM0 & _ & _).
assert (HV : forall j, (j < length (l_pl cx))%nat ->
  val_mem segs (mrestrict (w_H W) mem0) (l_p cx + Z.of_nat j) 1 (O4DS.at8 (l_pl cx) j)).
{ intros j Hj. assert (Hj' : (j < length (map (fun b : byte => bv_unsigned b) (l_pl cx)))%nat)
    by (rewrite length_map; exact Hj).
  destruct (HPAY j Hj') as [V _]. change (map (fun b : byte => bv_unsigned b) (l_pl cx)) with (O4W.zs (l_pl cx)) in V.
  rewrite o4_nth_zs in V. exact V. }
assert (HAPP : forall x, l_p cx <= x < l_p cx + Z.of_nat (length (l_pl cx)) ->
  ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)).
{ intros x Hx. rewrite <- Hlen in Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAM0.
  unfold SHADOW_OFF. lia. }
pose proof (o4_kd_ok (l_pl cx) (lc_oc (l_pl cx) (lo_c op)) (o4_oc_ok (l_pl cx) (lo_c op) Hc0)) as Hc3.
change (YK11.getr regs0 (Z_to_bv 5 24) = w64 (l_p cx + O4P.fi_off (sv_c (o4_kd cx op)))) in R24.
change (YK11.getr regs0 (Z_to_bv 5 19) = w64 (O4P.fi_n (sv_c (o4_kd cx op)))) in R19.
change (O4QF.fuzz_in_ok (l_pl cx) (sv_c (o4_kd cx op))) in Hc3.
remember (sv_c (o4_kd cx op)) as c3 eqn:Ec3.
(* +0xb0c .. +0xbe0: the u16 *)
rewrite o4_cfg.
apply (@o4_u16 (l_fx cx) rc W regs0 mem0 md0 (l_pl cx) (l_p cx) c3 _ R26 R24 R19 Hc3 Hp4096
  ltac:(rewrite <- Hlen; unfold o4_PTRHI; lia) HV HD ltac:(rewrite <- Hlen; exact HRA0) HAPP).
intros r1 mat1 lo hi KR1 Hlo Hhi Hw Q24 Q11 Q12 Q13.
destruct (O4QF.fuzz_u16_ok (l_pl cx) c3 Hc3) as (c4 & w4 & E16 & Hc4 & _).
rewrite E16 in Hw, Q24, Q11. cbn [fst snd] in Hw, Q24, Q11. subst w4.
pose proof Hc4 as (Hc4a & Hc4b & Hc4c).
(* +0xbe4 .. +0xc34: the take *)
assert (R9' : YK11.getr r1 9 = w64 (lc_sp1 cx)) by exact (eq_trans (KR1 9%bv ltac:(o4_kin)) R9).
assert (R26' : YK11.getr r1 26 = w64 SHADOW_OFF) by exact (eq_trans (KR1 26%bv ltac:(o4_kin)) R26).
unfold lc_spills in HSP. rewrite Forall_forall in HSP.
pose proof (HSP (136, 0xffff) ltac:(unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm;
  cbn [app In]; tauto)) as W136. cbn [fst snd] in W136.
pose proof (HSP (168, lc_F cx + 32) ltac:(unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm;
  cbn [app In]; tauto)) as W168. cbn [fst snd] in W168.
assert (HS1a : 0 <= lc_sp1 cx) by lia.
assert (HS1b : lc_sp1 cx + 176 <= 2 ^ 64) by (change (2 ^ 64) with 18446744073709551616; lia).
assert (HF32 : 0 <= lc_F cx + 32 < 2 ^ 64) by (change (2 ^ 64) with 18446744073709551616; lia).
assert (Hn4 : 0 <= O4P.fi_n c4 <= 67108864) by lia.
assert (Hq4a : 0 <= l_p cx + O4P.fi_off c4) by lia.
assert (Hq4b : l_p cx + O4P.fi_off c4 + O4P.fi_n c4 < 2 ^ 64) by (change (2 ^ 64) with 18446744073709551616; lia).
apply (@o4_take (l_fx cx) rc W r1 mem0 _ (lc_sp1 cx) (lc_F cx) (O4P.fi_n c4) lo hi (l_p cx + O4P.fi_off c4) _
  R9' R26' Q11 Q12 Q13 Q24 HS1a HS1b HF32 Hlo Hhi Hn4 Hq4a Hq4b W136 W168).
intros r2 mat2 KR2 t Q12' Q19' Q23' Q22'.
assert (Ht : 0 <= t <= 24 /\ t <= O4P.fi_n c4).
{ unfold t. pose proof (Z.mod_pos_bound (lo + 256 * hi) 25 ltac:(lia)).
  destruct ((lo + 256 * hi) mod 25 <? O4P.fi_n c4) eqn:Elt; [apply Z.ltb_lt in Elt | apply Z.ltb_ge in Elt]; lia. }
assert (E16' : O4P.fuzz_u16_m (l_pl cx) c3 = (c4, lo + 256 * hi)) by (rewrite E16; reflexivity).
assert (Erv : o4_rv cx op = mkLrw t (O4P.fi_off c4) t (O4P.FuzzIn (O4P.fi_off c4 + t) (O4P.fi_n c4 - t))).
{ unfold o4_rv. rewrite <- Ec3. exact (o4_rv_eq (l_pl cx) c3 lo hi c4 t E16' Hlo Hhi Hc4b eq_refl). }
rewrite wvb_collapse.
pose proof HJ0 as HJ1. apply (ajournal_gx_materialize segs B LAWS transport_segs_low) with (X := mat2) in HJ1.
(* +0xc38 .. +0xc44: the store of the length byte, the memcpy's arguments, `jal __asan_memcpy` *)
pose proof (@o4_entryS (l_fx cx) rc W r2 mem0 (lc_F cx + 32) Q22' ltac:(lia)
  (apresent_writable segs _ _ _ (HFpres (lc_F cx + 32 + 24) ltac:(unfold LF_FBYTES; lia)))) as HS.
set (E := o4_E r2 []) in HS.
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E (mrestrict (w_H W) mem0)) by constructor.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EE : forall n (x : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned x -> ew E n = YK11.getr r2 x)
  by (intros n x Hn32 Hx; unfold E, o4_E; exact (bcs_ew_reg r2 _ n x Hn32 Hx)).
assert (U22 : bv_unsigned (ew E 22) = lc_F cx + 32)
  by (rewrite (EE 22%nat 22%bv ltac:(lia) eq_refl), Q22'; unfold w64; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = l_p cx + O4P.fi_off c4)
  by (rewrite (EE 24%nat 24%bv ltac:(lia) eq_refl), (KR2 24%bv ltac:(o4_kin)), Q24; unfold w64;
      apply unsigned_lit_small; lia).
assert (U12 : bv_unsigned (ew E 12) = t)
  by (rewrite (EE 12%nat 12%bv ltac:(lia) eq_refl), Q12'; unfold w64; apply unsigned_lit_small; lia).
assert (U2 : bv_unsigned (ew E 2) = lc_sp1 cx)
  by (rewrite (EE 2%nat 2%bv ltac:(lia) eq_refl),
        (eq_trans (KR2 2%bv ltac:(o4_kin)) (eq_trans (KR1 2%bv ltac:(o4_kin)) Rsp));
      unfold w64; apply unsigned_lit_small; lia).
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS
  HGX 0 []) as RUN.
paj_run_tok RUN HS HJ1 SHOK (0, 0).
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  apply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ LF_CID (l_fpos cx)); [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U22 in Ha.
  left. unfold in_zr. cbn [fst snd]. rewrite HFaddr, lf_fbytes. unfold LF_FBYTES. lia. }
(* the store wrote the length byte only *)
assert (KS : forall a, 0 <= a < 2 ^ 64 -> ~ (lc_F cx + 56 <= a < lc_F cx + 57) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem0 a).
{ intros a Ha Hna. apply (kept_of_frame _ _ _ _ _ (fun x => lc_F cx + 56 <= x < lc_F cx + 57) HFr);
    [| exact Ha | exact Hna].
  intros b wlo whi x Hin Hx. lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in
    change (In y l') in Hin end.
  cbn [In] in Hin. destruct Hin as [Hin | []]. injection Hin as <- <- <-. cbn [base_val] in Hx. rewrite U22 in Hx.
  lia. }
assert (GS : forall a, apresent (w_H W) mem0 a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (YC4b.st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG. cbn [ms_mem restrict] in RG.
pose proof (field_of_region_any E _ 22%nat (lc_F cx + 32) _ _ _ _ _ 24 1%N (SOff 12 0) RG U22
  ltac:(cbn; tauto) ltac:(cbn; lia)) as VS.
assert (D12 : bv_unsigned (sv_denot E (SOff 12 0)) = t)
  by (cbn [sv_denot]; rewrite U12, Z.add_0_r; apply unsigned_lit_small; lia).
rewrite D12 in VS. change (8 * Z.of_N 1) with 8 in VS. change (N.to_nat 1) with 1%nat in VS.
rewrite (Z.mod_small t (2 ^ 8)) in VS by lia. replace (lc_F cx + 32 + 24) with (lc_F cx + 56) in VS by lia.
clear RG HF HFr HG.
(* the registers at the call *)
o4_creg HS (10%bv : bv 5) (w64 (lc_F cx + 32)) Q10 ltac:(cbn [sv_denot]; rewrite U22, Z.add_0_r; reflexivity).
o4_creg HS (11%bv : bv 5) (w64 (l_p cx + O4P.fi_off c4)) Q11m ltac:(cbn [sv_denot]; rewrite U24, Z.add_0_r; reflexivity).
o4_creg HS (12%bv : bv 5) (w64 t) Q12m ltac:(cbn [sv_denot]; rewrite U12, Z.add_0_r; reflexivity).
o4_creg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + O4_CPY)) Q1 ltac:(apply codeptr_val; exact HEI).
o4_creg HS (2%bv : bv 5) (w64 (lc_sp1 cx)) Q2 ltac:(cbn [sv_denot]; rewrite U2, Z.add_0_r; reflexivity).
o4_creg HS (3%bv : bv 5) (w64 (as_gp B)) Q3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv ltac:(lia) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans (KR2 3%bv ltac:(o4_kin)) (eq_trans (KR1 3%bv ltac:(o4_kin)) Rgp))).
o4_creg HS (4%bv : bv 5) (w64 (as_tp B)) Q4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv ltac:(lia) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans (KR2 4%bv ltac:(o4_kin)) (eq_trans (KR1 4%bv ltac:(o4_kin)) Rtp))).
assert (HAG32 : env_agree 32 (Ereg r2 []) E)
  by (split; [intros n Hn32; unfold E, o4_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HP1 : aregs_preserved r2 (ms_regs ms))
  by (apply (aregs_preserved_of_st_ok segs (w_H W) E _ ms r2 [] HS HAG32); vm_compute; reflexivity).
assert (QSP : spZ (ms_regs ms) = lc_sp1 cx) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 (transport_sigma TS___asan_memcpy)) mm rom) mdx) Q)
end.
(* the memcpy's source: the input bytes at the cursor, inside the input block *)
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HAR1.
pose proof (trans_rd_ok_sub W (ms_mem ms) (l_p cx) (l_n cx) (l_p cx + O4P.fi_off c4) t (HINB _ _ HAR1)
  ltac:(lia) ltac:(lia) ltac:(lia)) as (HVx & HRAx & HHVx & HAMx & Hx0 & Hx63).
pose proof (sep_block_frame segs B LAWS ly' S' W mem0 md0 (l_p cx) (l_n cx) LF_CID (l_fpos cx) HARg Hblk HFin)
  as HSEP.
unfold zdisjoint in HSEP. cbn [fst snd] in HSEP. rewrite HFaddr, lf_fbytes in HSEP. unfold LF_FBYTES in HSEP.
destruct (frames_bounds segs B LAWS ly' S' W mem0 md0 LF_CID (l_fpos cx) HARg HFin) as (_ & _ & HFapp).
rewrite HFaddr, lf_fbytes in HFapp. unfold in_app, LF_FBYTES in HFapp.
assert (HFapp' : lc_F cx + 256 <= kLowShadowBeg \/ kHighMemBeg <= lc_F cx) by (destruct HFapp as (_ & [H | [H _]]); lia).
assert (HF8 : lc_F cx mod 8 = 0).
{ pose proof (Z.div_mod (lc_F cx) 64 ltac:(lia)) as Dv. rewrite HFal, Z.add_0_r in Dv. rewrite Dv.
  replace (64 * (lc_F cx / 64)) with ((8 * (lc_F cx / 64)) * 8) by lia. apply Z_mod_mult. }
(* the frame's shadow at the call memory *)
assert (HSH1 : forall i, 0 <= i < 32 ->
  aview segs (w_H W) (ms_mem ms) (SHADOW_OFF + lc_F cx / 8 + i) = Some (nth (Z.to_nat i) (lf_shm true false) 0)).
{ intros i Hi. destruct (o4_sh_apart (lc_F cx) i HF4096 HFceil HFapp' Hi) as (Ha & Hb).
  rewrite KS by (unfold SHADOW_OFF in *; pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)); lia).
  exact (HFSH i Hi). }
eapply SRr_bind.
{ apply (@gx_intrin_at (l_fx cx) rc tfib_sink_head segs B LAWS transport_segs_low OCpy
    (transport_sigma TS___asan_memcpy) (lp_memcpy _ _ _ _ _ HP (l_fx cx)) TG.G_HARNESS W (ms_regs ms) (ms_mem ms)
    LLVMF_STK (lc_sp0 cx) [] (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly' S' _ e
    (lc_F cx + 32) (l_p cx + O4P.fi_off c4) t (lc_sp1 cx - lc_sp0 cx) (Z_to_bv 64 (BASE + O4_CPY)) HGX
    G_HARNESS_rw HJ1 Q10 Q11m Q12m).
  - lia.
  - lia.
  - lia.
  - rewrite QSP. lia.
  - pose proof (Z.div_mod (lc_sp1 cx) 32 ltac:(lia)) as D1. rewrite Hsp1al, Z.add_0_r in D1.
    pose proof (Z.div_mod (lc_sp0 cx) 16 ltac:(lia)) as D0. rewrite Hsp0al, Z.add_0_r in D0.
    replace (lc_sp1 cx - lc_sp0 cx) with ((2 * (lc_sp1 cx / 32) - lc_sp0 cx / 16) * 16) by lia. apply Z_mod_mult.
  - lia.
  - rewrite EST. unfold LLVMF_STK. lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [unfold O4_CPY; lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ1|]. intros a Ha. left. split.
    + unfold awr_byte. right; right; right. unfold in_frames. exists LF_CID, (l_fpos cx).
      split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite HFaddr, lf_fbytes. unfold LF_FBYTES. lia.
    + rewrite QSP, EST. lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. unfold kLowShadowBeg, kHighMemBeg in HFapp'. lia.
  - apply (frame_ra_zero _ (lc_F cx) (lc_F cx + 32) t 4 7); [lia | exact HF8 | lia | lia |].
    intros i Hi. rewrite (HSH1 i ltac:(lia)). rewrite o4_shm4 by lia. reflexivity.
  - intros Ht0. apply (frame_hull_vis _ (lc_F cx) 256 (lc_F cx + 32) t); [lia | exact HFal | reflexivity | lia | lia | lia |].
    intros i Hi. change (256 / 8) with 32 in Hi. replace (shadow_addr (lc_F cx)) with (SHADOW_OFF + lc_F cx / 8)
      by reflexivity. rewrite (HSH1 i Hi). discriminate.
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. split; [apply HVx; lia | rewrite QSP, EST; lia]. }
    split; [lia|]. split; [exact HAMx|]. split; [exact HRAx | intros _; exact HHVx]. }
cbv beta. intros W2 c2 _ (-> & regs3 & mem3 & md4 & -> & HJ3 & HP3 & _ & Hcpy & Heff & Hgr).
cbv iota in Hcpy.
(* what the store and the memcpy kept *)
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (lc_F cx + 32 <= a < lc_F cx + 32 + t) -> a <> lc_F cx + 56 ->
  ~ (lc_sp1 cx - ESTACK <= a < lc_sp1 cx) -> aview segs (w_H W) mem3 a = aview segs (w_H W) mem0 a).
{ intros a Ha H1 H2 H3. rewrite Heff by lia. apply KS; lia. }
assert (GM : forall a, apresent (w_H W) mem0 a -> apresent (w_H W) mem3 a) by (intros a Ha; exact (Hgr a (GS a Ha))).
assert (RK : forall z, z = 2 \/ z = 3 \/ z = 4 \/ z = 8 \/ z = 9 \/ z = 18 \/ z = 20 \/ z = 21 \/ z = 26 ->
  YK11.getr regs3 (Z_to_bv 5 z) = YK11.getr regs0 (Z_to_bv 5 z)).
{ intros z Hz.
  assert (Hcs : acallee_saved z) by (unfold acallee_saved; lia).
  rewrite (HP3 z Hcs), (HP1 z Hcs).
  destruct Hz as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
    apply (o4_kk regs0 r1 r2 _ KR1 KR2); o4_kin. }
assert (HCS : length (o4_cs cx op) = 32%nat).
{ unfold o4_cs. rewrite Erv. unfold lc_raw_cs. cbn [rw_off rw_len].
  destruct (o4_cs_shape (l_pl cx) (O4P.fi_off c4) t (sv_display (o4_kd cx op)) (sv_key (o4_kd cx op))
    Hc4a ltac:(lia) ltac:(lia)) as (L1 & _). exact L1. }
apply SRr_ret.
exists ly', S', regs3, mem3, md4, e, B1.
split; [rewrite o4_cfg; reflexivity|].
split; [exact Ho|].
split.
{ split.
  - apply (o4_core_kept B MT XL RLO RHI cx ly' S' W regs0 mem0 md0 e ESTACK ly' S' W regs3 mem3 md4 e LAWS HB HC HJ3
      eq_refl (Permutation_refl _) (RK 2 ltac:(lia)) (RK 3 ltac:(lia)) (RK 4 ltac:(lia)) (RK 8 ltac:(lia))
      (RK 9 ltac:(lia)) ltac:(rewrite EST; unfold LLVMF_STK; lia)).
    + intros a Ha Hw. apply KM; lia.
    + intros b m i Hbm Hi. destruct (al_blocks _ _ LAWS ly' S' W mem0 md0 b m HARg Hbm) as (_ & Hb4096 & Hbce & _).
      pose proof (sep_block_frame segs B LAWS ly' S' W mem0 md0 b m LF_CID (l_fpos cx) HARg Hbm HFin) as HS2.
      unfold zdisjoint in HS2. cbn [fst snd] in HS2. rewrite HFaddr, lf_fbytes in HS2. unfold LF_FBYTES in HS2.
      apply KM; lia.
    + intros a Ha. apply GM. apply HFpres. exact Ha.
    + intros a Ha. unfold LF_FBYTES in Ha. apply KM; lia.
  - split; [split; [exact (eq_trans (RK 18 ltac:(lia)) R18) | exact (eq_trans (RK 26 ltac:(lia)) R26)]|].
    split.
    { apply (lc_spills_kept cx (lf_spill_loop (lc_F cx)) (aview segs (w_H W) mem0) (aview segs (w_H W) mem3)).
      - intros o Hoin. pose proof (lf_spill_vals (lc_F cx) ltac:(lia) ltac:(unfold LF_FBYTES; lia)) as SV.
        rewrite Forall_forall in SV. destruct (SV o Hoin) as (_ & _ & Ho1 & Ho2). lia.
      - intros a Ha. apply KM; lia.
      - unfold lc_spills. rewrite Forall_forall. exact HSP. }
    split.
    { apply (lc_fsh_kept cx (aview segs (w_H W) mem0) (aview segs (w_H W) mem3) true false); [|exact HFSH].
      intros a Ha. unfold lc_SH in Ha.
      assert (Hi : 0 <= a - (SHADOW_OFF + lc_F cx / 8) < 32) by lia.
      destruct (o4_sh_apart (lc_F cx) (a - (SHADOW_OFF + lc_F cx / 8)) HF4096 HFceil HFapp' Hi) as (Hx & Hy).
      pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)).
      apply KM; unfold SHADOW_OFF in *; lia. }
    split; [exact HOPOK|]. split; [exact He|]. split; [exact HMET|].
    exact (eq_trans (RK 21 ltac:(lia)) R21). }
split; [exact HOB|]. split; [exact Hraw|].
split.
{ apply (tw_kept TMAP_A (aview segs (w_H W) mem0)); [exact HTW|]. intros x Hx.
  destruct Hx as (o & b & n & Hin & Hx).
  assert (HGx : inG TG.G_HARNESS x).
  { unfold inG. apply Exists_exists. exists (b, n). split; [exact (TMAP_A_in_G o b n Hin) | unfold in_zr; cbn; lia]. }
  pose proof (transport_segs_low x (proj1 (HGX x HGx))) as Hlow. unfold kLowMemEnd in Hlow.
  assert (HnF : ~ (lc_F cx <= x < lc_F cx + 256)).
  { intros Hr. apply (frm_img segs B LAWS ly' S' W mem0 md0 LF_CID (l_fpos cx) x HARg HFin);
      [rewrite HFaddr, lf_fbytes; unfold LF_FBYTES; lia | exact (trans_g_img x HGx)]. }
  apply KM; lia. }
split.
{ unfold o4_cs. rewrite Erv. unfold lc_raw_cs. cbn [rw_off rw_len].
  change (garr8 segs (mrestrict (w_H W) mem0) (lc_F cx + 32)
    (O4W.zs (O4P.cmd_struct (repeat (O4DS.b8 0) 24) 0 (sv_display (o4_kd cx op)) (sv_key (o4_kd cx op))))) in HC8.
  destruct (o4_cs_shape (l_pl cx) (O4P.fi_off c4) t (sv_display (o4_kd cx op)) (sv_key (o4_kd cx op))
    Hc4a ltac:(lia) ltac:(lia)) as (L1 & L0 & S1 & S24 & S2).
  apply o4_garr8_of. intros j Hj. unfold O4W.zs in Hj. rewrite length_map, L1 in Hj.
  rewrite o4_nth_zs. split; [|apply o4_byte_range].
  destruct (Nat.lt_ge_cases j (Z.to_nat t)) as [Hjt | Hjt].
  - (* an input byte *)
    rewrite (S1 j Hjt).
    rewrite (Hcpy (Z.of_nat j) ltac:(lia)).
    rewrite KS by (lia).
    assert (Hjd : (Z.to_nat (O4P.fi_off c4) + j < length (map (fun b : byte => bv_unsigned b) (l_pl cx)))%nat)
      by (rewrite length_map; lia).
    pose proof (o4_garr8_aview _ _ _ _ _ HPAY Hjd) as Vj.
    replace (l_p cx + Z.of_nat (Z.to_nat (O4P.fi_off c4) + j)) with (l_p cx + O4P.fi_off c4 + Z.of_nat j) in Vj by lia.
    rewrite Vj. change (map (fun b : byte => bv_unsigned b) (l_pl cx)) with (O4W.zs (l_pl cx)).
    rewrite o4_nth_zs. reflexivity.
  - destruct (Nat.eq_dec j 24) as [-> | Hj24].
    + (* the length byte *)
      rewrite S24. replace (lc_F cx + 32 + Z.of_nat 24) with (lc_F cx + 56) by lia.
      rewrite (Heff (lc_F cx + 56)) by (unfold O4_CPY in *; lia).
      refine (eq_trans (o4_aview_vm1 _ _ _ _ VS ltac:(lia)) _). f_equal.
      unfold O4DS.b8. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
      symmetry. apply Z.mod_small. lia.
    + (* a byte op 4's prologue left *)
      rewrite (S2 j ltac:(lia) Hj24).
      rewrite KM by lia.
      assert (Hj0 : (j < length (O4W.zs (O4P.cmd_struct (repeat (O4DS.b8 0) 24) 0 (sv_display (o4_kd cx op))
        (sv_key (o4_kd cx op)))))%nat) by (unfold O4W.zs; rewrite length_map, L0; lia).
      rewrite (o4_garr8_aview _ _ _ _ _ HC8 Hj0). rewrite o4_nth_zs. reflexivity. }
split; [exact HCS|].
split.
{ rewrite (rdword_ext (aview segs (w_H W) mem0) (aview segs (w_H W) mem3) (lc_sp1 cx + 144))
    by (intros k Hk; apply KM; lia).
  exact HQ. }
split.
{ rewrite Erv. cbn [rw_c]. split.
  - transitivity (w64 (l_p cx + O4P.fi_off c4 + t)).
    + exact (eq_trans (HP3 19 ltac:(unfold acallee_saved; lia)) (eq_trans (HP1 19 ltac:(unfold acallee_saved; lia)) Q19')).
    + cbn [O4P.fi_off]. f_equal. lia.
  - transitivity (w64 (O4P.fi_n c4 - t)).
    + exact (eq_trans (HP3 23 ltac:(unfold acallee_saved; lia)) (eq_trans (HP1 23 ltac:(unfold acallee_saved; lia)) Q23')).
    + reflexivity. }
split.
{ exact (eq_trans (RK 20 ltac:(lia)) R20). }
exact (eq_trans (HP3 22 ltac:(unfold acallee_saved; lia)) (eq_trans (HP1 22 ltac:(unfold acallee_saved; lia)) Q22')).
Qed.

End seg.

(* ------------------------------------------------------------------ *)
(* 7. The two calls: from the cut after the memcpy to S4               *)
(* ------------------------------------------------------------------ *)

(* The kit of LLVMFuzzerTestOneInput_seg_op4sub.v (its o4s_ lemmas), whose segment makes the same two calls from the G
   journal, is used as it is: o4s_E, o4s_ew_reg, o4s_env_img, o4s_entry0, o4s_rg144, o4s_c_ok, the invariant o4s_inv
   and o4s_inv_kept, o4s_leaf, o4s_kept_all, o4s_wr_gs, o4s_wr_img, o4s_tw_csw and o4s_rng_hull (and o4s_submit_rc).
   The local pieces below are its Section-local tactics, and the places where this segment differs from it: it writes
   no callee-saved register, and its cut S4 names s7 (the bytes left after the take). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportLeafb diginet_session_submit_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require AsanKA check_refusal_submit_cg check_refusal_submit_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require ExecF MState.
Module O4AKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.AsanKA.
Module O4CRS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_refusal_submit_cg.
Module O4CRSc := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.check_refusal_submit_c.

(* The register, run and frame tactics of the kit. LLVMFuzzerTestOneInput_seg_op4sub.v defines them inside its
   Section, so they end with it; these are the same tactics, over its exported o4s_E and o4s_ew_reg. *)
Ltac o4b_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
Ltac o4b_atom regs0 Q :=
  cbn [sv_denot]; erewrite o4s_ew_reg; [rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact Q | lia | reflexivity].
Ltac o4b_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons; [intros ? ?; cbn [YP09.r_wlo YP09.r_whi] in *; lia|]);
  apply awr_ok_x_nil.
Ltac o4b_kept HFr KR W mold msn :=
  assert (KR : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) (ms_mem msn) a = aview tfibsegs (w_H W) mold a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []];
    let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
    let Hin := fresh "Hin" in let Hx := fresh "Hx" in
    intros b wlo whi x Hin Hx;
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
    cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; lia|]); destruct Hin
  | ].
Ltac o4b_kreg HS regs0 :=
  lazymatch goal with |- YK11.getr (ms_regs ?msx) ?rr = YK11.getr regs0 ?rr =>
  lazymatch type of HS with
  | st_ok ?sg ?Ex ?ssx (restrict ?Hh msx) =>
      refine (eq_trans (st_ok_restrict_reg sg Hh Ex ssx msx rr HS) _);
      let e := eval vm_compute in (sr_get (ss_regs ssx) rr) in change (sv_denot Ex e = YK11.getr regs0 rr);
      cbn [sv_denot]; erewrite o4s_ew_reg; [rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | reflexivity]
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh msx) =>
      refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx rr HS) _);
      let e := eval vm_compute in (sr_get (ss_regs ssx) rr) in change (sv_denot Ex e = YK11.getr regs0 rr);
      cbn [sv_denot]; erewrite o4s_ew_reg; [rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | reflexivity]
  end end.

(* Every callee-saved register a run keeps, as aregs_preserved. o4s_keep leaves s7 out (its segment writes s7); no run
   here writes a callee-saved register, and s7 must reach S4. *)
Ltac o4b_keep HS regs0 :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; unfold acallee_saved in Hr;
  assert (Er : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
               r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  repeat (destruct Er as [-> | Er]; [o4b_kreg HS regs0|]); subst r; o4b_kreg HS regs0.

Section calls. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* +0xc58 with the queue length before at 144(s1) (atom 32, s1 atom 9), read only: the state o4s_rg144 that
   LLVMFuzzerTestOneInput_seg_op4sub.v builds inline, at any pc. *)
Lemma o4b_entry144 : forall (fx : YK11.FPState) (W : world segs) regs mem s1 v (pc : Z),
  YK11.getr regs 9 = w64 s1 -> 0 <= s1 -> s1 + 152 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  rdword (aview segs (w_H W) mem) (s1 + 144) = Some v ->
  st_ok_pi segs VAL (o4s_E regs [w64 v]) (mkSS pc sr_atoms [o4s_rg144] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros fx W regs mem s1 v pc R9 Hs0 Hs1 Hv Rv.
  assert (U9 : bv_unsigned (ew (o4s_E regs [w64 v]) 9) = s1)
    by (rewrite (o4s_ew_reg regs _ 9 9%bv ltac:(lia) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (X32 : ew (o4s_E regs [w64 v]) 32 = w64 v).
  { unfold o4s_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
  rewrite restrict_mkst_fx. apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold o4s_rg144, YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs _ _ s1 144 8 (SOff 32 0) v).
    + cbn [sv_denot]. rewrite X32, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    + cbn. lia.
    + cbn. lia.
    + apply val_mem_of_rdword. exact Rv.
  - exact (conj I I).
  - exact (conj I (conj I I)).
Qed.

(* o4s_inv_kept with rv's registers carried whatever they are, s7 included: o4s_inv_kept carries rv only off s7
   (its segment writes s7), while every step of this segment keeps all callee-saved registers. *)
Lemma o4b_inv_kept : forall cx op cs sl rv ly' S' (W' : world segs) regs' mem' md' e (X : Z)
    ly2 S2 (W2 : world segs) regs2 mem2 md2,
  AR_laws segs B -> ameter_laws MT -> @lc_base rc B MT XL RLO RHI cx ->
  o4s_inv B MT cx op cs sl rv ly' S' W' regs' mem' md' e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] LLVMF_STK (lc_sp0 cx) []
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly2 S2 W2 mem2 md2 e ->
  frames S2 = frames S' ->
  Permutation (ablocks B ly2 S2) (ablocks B ly' S') ->
  aregs_preserved regs' regs2 ->
  mo_le MT S' S2 0 ->
  0 <= X <= LLVMF_STK - 336 ->
  (forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (lc_sp1 cx - X <= a < lc_sp1 cx) ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a) ->
  (forall b m i, In (b, m) (ablocks B ly' S') -> 0 <= i < req_size m ->
     aview segs (w_H W2) mem2 (b + i) = aview segs (w_H W') mem' (b + i)) ->
  (forall a, lc_F cx <= a < lc_F cx + LF_FBYTES \/ lc_SH cx <= a < lc_SH cx + 32 ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W') mem' a) ->
  length cs = 32%nat ->
  (forall o, In o sl -> 0 <= fst o /\ fst o + 8 <= 192) ->
  (forall x, In x rv -> acallee_saved (fst x)) ->
  o4s_inv B MT cx op cs sl rv ly2 S2 W2 regs2 mem2 md2 e.
Proof.
  intros cx op cs sl rv ly' S' W' regs' mem' md' e X ly2 S2 W2 regs2 mem2 md2 LAWS MTL HB HI HJ2 HFR2 HP2 HPR HMO HX
    KA KB KF HLC Hsl Hrv.
  destruct HI as (HLC0 & HGA & HSL & HRV).
  destruct (o4s_inv_kept B MT XL RLO RHI cx op cs sl [] ly' S' W' regs' mem' md' e X ly2 S2 W2 regs2 mem2 md2 LAWS MTL
    HB (conj HLC0 (conj HGA (conj HSL (Forall_nil _)))) HJ2 HFR2 HP2 (fun r Hr _ => HPR r Hr) HMO HX KA KB KF HLC Hsl
    (fun x Hx => False_ind _ Hx)) as (HLC2 & HGA2 & HSL2 & _).
  refine (conj HLC2 (conj HGA2 (conj HSL2 _))).
  rewrite Forall_forall in HRV |- *. intros x Hx. rewrite <- (HRV x Hx). exact (HPR (fst x) (Hrv x Hx)).
Qed.

(* The cut's spill slot and registers this segment carries. *)
Definition o4b_sl (op : lop) : list (Z * Z) := [(144, o4_qv (lo_B op))].
Definition o4b_rv (cx : lcx) (op : lop) : list (Z * word) :=
  [(19, w64 (l_p cx + O4P.fi_off (rw_c (o4_rv cx op)))); (23, w64 (O4P.fi_n (rw_c (o4_rv cx op))));
   (20, w64 LF_S4); (22, w64 (lc_F cx + 32))].
Lemma o4b_sl_ok : forall op o, In o (o4b_sl op) -> 0 <= fst o /\ fst o + 8 <= 192.
Proof. intros op o Ho. unfold o4b_sl in Ho. cbn [In] in Ho. destruct Ho as [<- | []]. cbn [fst]. lia. Qed.
Lemma o4b_rv_ok : forall cx op x, In x (o4b_rv cx op) -> acallee_saved (fst x).
Proof.
  intros cx op x Hx. unfold o4b_rv in Hx. cbn [In] in Hx.
  repeat (destruct Hx as [<- | Hx]; [cbn [fst]; unfold acallee_saved; lia|]). destruct Hx.
Qed.

(* +0xc48 .. +0xc68: g_s and c to diginet_session_submit; c, its result and the queue length before to
   check_refusal_submit; `j` to S4. *)
Lemma o4_seg_b : lp_prem B MT XL RLO RHI -> forall (cx : lcx) (op : lop) (W1 : world segs) (c1 : config),
  lc_base B MT XL RLO RHI cx -> o4_st_cpy B MT cx op W1 c1 -> SRr segs W1 c1 (lc_st_s4 B MT cx op).
Proof.
intros HP cx op W1 c1 HB HCPY.
pose proof (lp_laws B MT XL RLO RHI HP) as LAWS. pose proof (lp_meter_laws B MT XL RLO RHI HP) as MTL.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned B MT XL RLO RHI HP)) as HGX.
destruct HCPY as (ly1 & S1 & regs1 & mem1 & md1 & e1 & B1 & Ec1 & Hopc & HLC & HOB & Hraw & HTW & HGA & Hcs & Q144 &
  HCUR & R20 & R22).
destruct HCUR as (R19 & R23).
pose proof HLC as (HCORE & HFR & HSPL & HFSH & HOPOK & He1 & HMET & R21).
set (cs := o4_cs cx op) in *.
(* the model *)
pose proof HOPOK as (HAG & Hops & Hcok & Hcn & Hk).
destruct (o4_model (l_pl cx) (lo_B op) B1 (lo_c op) (lo_ops op) (lo_k op) HAG Hops Hcok Hcn Hk Hopc HOB Hraw)
  as (B2 & r & B3 & M2 & M3 & M4 & MOP).
change (O4S0.diginet_session_submit_m B1 cs = Some (B2, r)) in M2.
change (O4C.check_refusal_submit_m B2 cs r (O4W.S_queued (lo_B op)) = Some (B3, tt)) in M3.
change (forall A, O4P.LLVMFuzzerTestOneInput_op_m timg_A (lo_B op) A (l_pl cx) (lo_c op) (lo_k op) =
  Some (B3, (rw_c (o4_rv cx op), lo_k op))) in MOP.
pose proof (o4s_submit_rc _ _ _ _ M2) as Hr.
(* the geometry *)
destruct (lc_geom B MT XL RLO RHI cx ly1 S1 W1 regs1 mem1 md1 e1 HB HCORE)
  as [HAR1 Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof HCORE as (HJ1 & Hfrs1 & HlyF1 & HPERM1 & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal &
  HFceil & HFpres & HFL & HIN).
assert (INV0 : o4s_inv B MT cx op cs (o4b_sl op) (o4b_rv cx op) ly1 S1 W1 regs1 mem1 md1 e1).
{ split; [exact HLC|]. split; [exact HGA|]. split.
  - unfold lc_spills, o4b_sl. apply Forall_cons; [exact Q144 | apply Forall_nil].
  - unfold o4b_rv.
    apply Forall_cons; [exact R19|]. apply Forall_cons; [exact R23|]. apply Forall_cons; [exact R20|].
    apply Forall_cons; [exact R22|]. apply Forall_nil. }
pose proof (@YM05.alloc_ceiling_val rc) as [CE1 CE2].
destruct Hstk as (Hs1 & Hs2 & Hs3 & Hs4). unfold LF_FRAME in Hsp1.
assert (ESS : SSUBMIT_STK = 4448) by (vm_compute; reflexivity).
assert (ELS : LLVMF_STK = 32768) by (vm_compute; reflexivity).
assert (H16 : lc_sp1 cx mod 16 = 0).
{ apply Z.mod_divide in Hsp1al as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((q * 2) * 16) by ring.
  apply Z_mod_mult. }
assert (HF4 : (lc_F cx + 32) mod 4 = 0).
{ apply Z.mod_divide in HFal as [q Hq]; [|lia]. rewrite Hq. replace (q * 64 + 32) with ((q * 16 + 8) * 4) by ring.
  apply Z_mod_mult. }
(* ---- +0xc48 .. +0xc54: a0 = &g_s, a1 = c, the call of diginet_session_submit ---- *)
subst c1. rewrite o4_cfg.
set (fx := l_fx cx) in *.
pose proof (o4s_entry0 fx W1 regs1 [] mem1 O4_CPY) as HS.
assert (HEI : img_env VAL A_LIM (o4s_E regs1 [])) by apply o4s_env_img.
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) (o4s_E regs1 []) (mrestrict (w_H W1) mem1)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
paj_run_tok RUN HS HJ1 SHOK (0, 0).
{ o4b_awr. }
o4b_kept HFr KR1 W1 mem1 ms.
pose proof (o4s_kept_all W1 mem1 (ms_mem ms) KR1) as KR1a. clear HF HFr HG KR1.
assert (HK1 : aregs_preserved regs1 (ms_regs ms)) by o4b_keep HS regs1.
assert (INV1 : o4s_inv B MT cx op cs (o4b_sl op) (o4b_rv cx op) ly1 S1 W1 (ms_regs ms) (ms_mem ms)
  (with_vm_backing (m_vm_lazy md1) mat md1) e1).
{ apply (o4b_inv_kept cx op cs _ _ ly1 S1 W1 regs1 mem1 md1 e1 0 ly1 S1 W1 (ms_regs ms) (ms_mem ms) _ LAWS MTL HB
    INV0 HJ1 eq_refl (Permutation_refl _) HK1 (mo_le_refl MT MTL S1)).
  - rewrite ELS. lia.
  - intros a _ _. exact (KR1a a).
  - intros b m i _ _. exact (KR1a (b + i)).
  - intros a _. exact (KR1a a).
  - exact Hcs.
  - apply o4b_sl_ok.
  - apply o4b_rv_ok. }
(* the registers at the call *)
o4b_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 3160)) Q1 ltac:(apply codeptr_val; exact HEI).
o4b_reg HS (2%bv : bv 5) (w64 (lc_sp1 cx)) Q2 ltac:(o4b_atom regs1 Rsp).
o4b_reg HS (3%bv : bv 5) (w64 (as_gp B)) Q3 ltac:(o4b_atom regs1 Rgp).
o4b_reg HS (4%bv : bv 5) (w64 (as_tp B)) Q4 ltac:(o4b_atom regs1 Rtp).
o4b_reg HS (11%bv : bv 5) (w64 (lc_F cx + 32)) Q11 ltac:(o4b_atom regs1 R22).
o4b_reg HS (10%bv : bv 5) (w64 SSUBMIT_S) Q10
  ltac:(cbn [sv_denot]; rewrite (img_env_atomP (o4s_E regs1 []) 250%nat HEI) by (unfold A_TEXT; split; [lia | vm_compute; lia]);
        vm_compute; reflexivity).
assert (QSP : spZ (ms_regs ms) = lc_sp1 cx)
  by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
pmkst HS.
(* what the call reads at the call memory *)
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HARc.
pose proof INV1 as (HLC1 & HGA1 & HSL1 & HRV1).
pose proof HLC1 as (HC1 & HFR1 & HSP1 & HFSH1 & _).
pose proof HC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFpresc & _).
destruct (o4s_c_ok B cx ly1 S1 W1 (ms_mem ms) _ false cs LAWS HARc HFin HFaddr HFal HFpresc HFSH1) as (HINF & HRD).
(* +0xc54: the call of diginet_session_submit *)
eapply SRr_bind.
{ refine (lp_submit B MT XL RLO RHI HP fx LLVMF_STK (lc_sp0 cx) [] (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx)
    [(LF_CID, l_fpos cx)] ly1 S1 W1 (ms_mem ms) (with_vm_backing (m_vm_lazy md1) mat md1) e1 (ms_regs ms)
    (lc_F cx + 32) r cs B1 B2 HJ1 _ _ Q3 Q4 Q10 Q11 _ _ _ _ M2 Hcs _ HF4 _ HGA1 _ _ _ _).
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1. replace BASE with transport_text by (vm_compute; reflexivity).
    unfold transport_text. rewrite unsigned_lit_small by lia. lia.
  - rewrite QSP. exact H16.
  - rewrite QSP, ESS, ELS. lia.
  - rewrite QSP. lia.
  - apply (tw_kept TMAP_A (aview segs (w_H W1) mem1)); [exact HTW | intros x _; exact (KR1a x)].
  - lia.
  - right. split; [left; exact HINF | exact HRD].
  - unfold decode_off_win, SSUBMIT_CMD_LEN. left. rewrite QSP, ESS. unfold LF_FBYTES in HFceil. lia.
  - intros x Hx. split; intros HX.
    + apply (frm_img segs B LAWS ly1 S1 W1 _ _ LF_CID (l_fpos cx) x HARc HFin);
        [rewrite HFaddr; change (fs_frame_bytes LF_CID) with 256; unfold SSUBMIT_CMD_LEN in Hx; lia | exact (trans_g_img x HX)].
    + apply (frm_img segs B LAWS ly1 S1 W1 _ _ LF_CID (l_fpos cx) x HARc HFin);
        [rewrite HFaddr; change (fs_frame_bytes LF_CID) with 256; unfold SSUBMIT_CMD_LEN in Hx; lia | exact (trans_ro_img x HX)].
  - rewrite Hfrs1. vm_compute. reflexivity.
  - pose proof HB as HB'. unfold lc_base, tfib_lib_pre_x in HB'.
    destruct HB' as (_ & _ & _ & _ & _ & _ & _ & _ & Hev & _).
    assert (He1' : 0 <= e1 <= 2 * Z.of_nat (lo_k op)) by exact He1.
    assert (EEL : EV_LIB = 2048) by reflexivity. assert (EOM : O4C.OPS_MAX = 1024) by reflexivity.
    unfold SSUBMIT_EV. lia. }
cbv beta. intros W2 c2 _ HPOST.
unfold transport_ssubmit_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly2 & S2 & regs2 & mem2 & md2 & e2 & Ec2 & He2 & HJ2 & HP2 & Hfr2 & Hperm2 & HK2 & Hmo2 & (HA0 & HTW2)).
assert (Ee2 : e2 = 0) by (unfold SSUBMIT_EV in He2; lia). subst e2. rewrite Z.add_0_r in HJ2.
rewrite Q1 in Ec2. subst c2.
(* the invariant after the call *)
pose proof HK2 as (K21 & K22 & K23 & K24 & _).
assert (INV2 : o4s_inv B MT cx op cs (o4b_sl op) (o4b_rv cx op) ly2 S2 W2 regs2 mem2 md2 e1).
{ apply (o4b_inv_kept cx op cs _ _ ly1 S1 W1 (ms_regs ms) (ms_mem ms) _ e1 SSUBMIT_STK ly2 S2 W2 regs2 mem2 md2 LAWS
    MTL HB INV1 HJ2 Hfr2 Hperm2 HP2 Hmo2).
  - rewrite ESS, ELS. lia.
  - intros a Ha Hna. apply K21; [exact Ha | rewrite QSP; exact Hna].
  - intros b m i Hb Hi. apply (K22 b m i Hb Hi). intros Hw.
    exact (blk_img segs B LAWS ly1 S1 W1 _ _ b m (b + i) HARc Hb ltac:(lia) (o4s_wr_img XL RLO _ Hw)).
  - intros a Ha. apply (K24 LF_CID (l_fpos cx) a HFin).
    + destruct Ha as [Ha | Ha]; [left | right]; unfold in_zr, frame_rng; cbn [fst snd]; rewrite HFaddr;
        change (fs_frame_bytes LF_CID) with 256; unfold lc_SH, LF_FBYTES, shadow_addr in *; lia.
    + intros Hw. destruct Ha as [Ha | Ha].
      * exact (frm_img segs B LAWS ly1 S1 W1 _ _ LF_CID (l_fpos cx) a HARc HFin
          ltac:(rewrite HFaddr; change (fs_frame_bytes LF_CID) with 256; unfold LF_FBYTES in Ha; lia) (o4s_wr_img XL RLO _ Hw)).
      * pose proof (o4s_wr_gs a Hw) as Hg. unfold lc_SH, SHADOW_OFF in Ha. unfold TA_g_s, O4W.SZ_g_s in Hg.
        pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)). lia.
  - exact Hcs.
  - apply o4b_sl_ok.
  - apply o4b_rv_ok. }
(* ---- +0xc58 .. +0xc64: a1 = rc, a0 = c, a2 = 144(s1), the call of check_refusal_submit ---- *)
pose proof INV2 as (HLC2 & HGA2 & HSL2 & HRV2).
pose proof HLC2 as (HC2 & HFR2 & _).
pose proof HC2 as (_ & _ & _ & _ & R2_2 & R8_2 & R9_2 & R3_2 & R4_2 & _).
assert (R22_2 : YK11.getr regs2 (Z_to_bv 5 22) = w64 (lc_F cx + 32)).
{ rewrite Forall_forall in HRV2. exact (HRV2 (22, w64 (lc_F cx + 32)) ltac:(unfold o4b_rv; cbn; tauto)). }
set (v144 := o4_qv (lo_B op)) in *.
assert (HV144 : 0 <= v144 < 2 ^ 64)
  by (unfold v144, o4_qv; pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 (bv_swrap 32 (O4W.S_queued (lo_B op))))) as H;
      change (bv_modulus 64) with (2 ^ 64) in H; exact H).
assert (S144 : rdword (aview segs (w_H W2) mem2) (lc_sp1 cx + 144) = Some v144).
{ unfold lc_spills in HSL2. rewrite Forall_forall in HSL2. exact (HSL2 (144, v144) ltac:(unfold o4b_sl; cbn; tauto)). }
assert (X32 : ew (o4s_E regs2 [w64 v144]) 32 = w64 v144).
{ unfold o4s_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs2 _ 0). }
pose proof (o4b_entry144 fx W2 regs2 mem2 (lc_sp1 cx) v144 3160 R9_2 ltac:(lia)
  ltac:(change (2 ^ 64) with 18446744073709551616; lia) HV144 S144) as HS2.
assert (HEI2 : img_env VAL A_LIM (o4s_E regs2 [w64 v144])) by apply o4s_env_img.
assert (SHOK2 : sh_ok segs (SLit 0) (@nil shent) (o4s_E regs2 [w64 v144]) (mrestrict (w_H W2) mem2)) by constructor.
paj_run_tok RUN HS2 HJ2 SHOK2 (0, 0).
{ o4b_awr. }
o4b_kept HFr KR2 W2 mem2 ms0.
pose proof (o4s_kept_all W2 mem2 (ms_mem ms0) KR2) as KR2a. clear HF HFr HG KR2.
assert (HK3 : aregs_preserved regs2 (ms_regs ms0)) by o4b_keep HS2 regs2.
assert (INV3 : o4s_inv B MT cx op cs (o4b_sl op) (o4b_rv cx op) ly2 S2 W2 (ms_regs ms0) (ms_mem ms0)
  (with_vm_backing (m_vm_lazy md2) mat0 md2) e1).
{ apply (o4b_inv_kept cx op cs _ _ ly2 S2 W2 regs2 mem2 md2 e1 0 ly2 S2 W2 (ms_regs ms0) (ms_mem ms0) _ LAWS MTL HB
    INV2 HJ2 eq_refl (Permutation_refl _) HK3 (mo_le_refl MT MTL S2)).
  - rewrite ELS. lia.
  - intros a _ _. exact (KR2a a).
  - intros b m i _ _. exact (KR2a (b + i)).
  - intros a _. exact (KR2a a).
  - exact Hcs.
  - apply o4b_sl_ok.
  - apply o4b_rv_ok. }
(* the registers at the call *)
o4b_reg HS2 (1%bv : bv 5) (Z_to_bv 64 (BASE + 3176)) P1 ltac:(apply codeptr_val; exact HEI2).
o4b_reg HS2 (Z_to_bv 5 2) (w64 (lc_sp1 cx)) P2 ltac:(o4b_atom regs2 R2_2).
o4b_reg HS2 (3%bv : bv 5) (w64 (as_gp B)) P3 ltac:(o4b_atom regs2 R3_2).
o4b_reg HS2 (4%bv : bv 5) (w64 (as_tp B)) P4 ltac:(o4b_atom regs2 R4_2).
o4b_reg HS2 (Z_to_bv 5 10) (w64 (lc_F cx + 32)) P10 ltac:(o4b_atom regs2 R22_2).
o4b_reg HS2 (Z_to_bv 5 11) (w64 r) P11 ltac:(o4b_atom regs2 HA0).
o4b_reg HS2 (Z_to_bv 5 12) (w64 v144) P12 ltac:(cbn [sv_denot]; rewrite X32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (PSP : spZ (ms_regs ms0) = lc_sp1 cx).
{ transitivity (bv_unsigned (w64 (lc_sp1 cx))); [unfold spZ; f_equal; exact P2 | unfold w64; apply unsigned_lit_small; lia]. }
(* the facts the leaf reads at the call memory *)
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HARc3.
destruct (gx_open segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as (memS & HJd & _ & _).
pose proof HJd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _). clear HJd memS.
pose proof INV3 as (HLC3 & HGA3 & HSL3 & HRV3).
pose proof HLC3 as (HC3 & HFR3 & HSP3 & HFSH3 & _).
pose proof HC3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFpres3 & _).
destruct (lc_geom B MT XL RLO RHI cx ly2 S2 W2 (ms_regs ms0) (ms_mem ms0) _ e1 HB HC3)
  as [_ _ _ _ HFaddr2 HFin2 _ _ _].
destruct (o4s_c_ok B cx ly2 S2 W2 (ms_mem ms0) _ false cs LAWS HARc3 HFin2 HFaddr2 HFal HFpres3 HFSH3) as (HINF3 & HRD3).
destruct (frames_bounds segs B LAWS ly2 S2 W2 (ms_mem ms0) _ LF_CID (l_fpos cx) HARc3 HFin2) as (_ & _ & Happ2).
rewrite HFaddr2 in Happ2. change (fs_frame_bytes LF_CID) with 256 in Happ2.
(* +0xc64: the call of check_refusal_submit *)
pmkst HS2.
assert (EPC1 : pa_sigma TS_check_refusal_submit = O4CRSc.CHECK_REFUSAL_SUBMIT) by reflexivity.
rewrite EPC1.
eapply SRr_bind.
{ apply (o4s_leaf B fx W2 (ms_regs ms0) (ms_mem ms0) LLVMF_STK (lc_sp0 cx) [] (l_ly cx) (l_S cx) (l_W cx) (l_mem cx)
    (l_md cx) [(LF_CID, l_fpos cx)] ly2 S2 _ e1 (lc_sp1 cx - lc_sp0 cx) O4CRSc.CHECK_REFUSAL_SUBMIT (fun _ => B3 = B2)
    LAWS HJ2).
  - rewrite PSP. ring.
  - rewrite Zminus_mod, H16, Hsp0al. reflexivity.
  - lia.
  - unfold ESTACK. rewrite ELS. lia.
  - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact P3.
  - exact P4.
  - intros HPRE.
    pose proof (lp_crs B MT XL RLO RHI HP fx) as LF.
    unfold transport_leaf_at, O4CRS.transport_check_refusal_submit_cg in LF.
    specialize (LF ly2 S2 W2 (ms_regs ms0) (ms_mem ms0) _ (lc_sp1 cx - ESTACK) B2 B3 (lc_F cx + 32) cs r
      (O4W.S_queued (lo_B op)) HPRE).
    cbv zeta in LF.
    destruct HRD3 as (_ & HRA3 & _ & _).
    apply LF; clear LF.
    + exact P10.
    + exact P11.
    + rewrite P12. unfold w64, v144, o4_qv. apply Z_to_bv_bv_unsigned.
    + lia.
    + pose proof (TWL.u_at_range (lo_B op) O4W.A_S_queued 4) as HQ. exact HQ.
    + lia.
    + exact HF4.
    + apply (decode_leafb_bytes_garr8 W2 (ms_mem ms0) (lc_F cx + 32) cs); [exact HGA3 | lia |].
      rewrite Hcs. change (Z.of_nat 32) with 32. change (2 ^ 64) with 18446744073709551616.
      unfold LF_FBYTES in HFceil. lia.
    + exact Hcs.
    + apply (o4s_tw_csw W2). apply (tw_kept TMAP_A (aview segs (w_H W2) mem2)); [exact HTW2 | intros x _; exact (KR2a x)].
    + exact M3.
    + rewrite P2, MState.unsigned_lit by lia. apply (decode_leafb_stk W2 (ms_mem ms0));
        [unfold ESTACK; lia | change (2 ^ 64) with 18446744073709551616; change (2 ^ 47) with 140737488355328 in Hs4; lia |].
      intros a Ha. apply Hpres3. unfold ESTACK in Ha. rewrite ELS. lia.
    + rewrite P2, MState.unsigned_lit by lia. unfold O4CRSc.CHECK_REFUSAL_SUBMIT_FRAME, ESTACK. lia.
    + unfold O4AKA.off_stk. rewrite P2, MState.unsigned_lit by lia.
      unfold O4CRSc.CHECK_REFUSAL_SUBMIT_FRAME, TG.G_HARNESS_LO, TG.G_HARNESS_HI. lia.
    + exact (decode_leafb_asan_cells B (lp_cells B MT XL RLO RHI HP) ly2 S2 W2 (ms_mem ms0) _ HARc3).
    + rewrite P2, MState.unsigned_lit by lia. apply (@decode_leafb_app_stack rc). unfold O4CRSc.CHECK_REFUSAL_SUBMIT_FRAME. lia.
    + rewrite P2, MState.unsigned_lit by lia. apply (@decode_leafb_app_stack rc). lia.
    + unfold O4AKA.off_stk. rewrite P2, MState.unsigned_lit by lia.
      unfold O4CRSc.CHECK_REFUSAL_SUBMIT_FRAME, AsanCells.GOT_CELL_K. lia.
    + unfold O4AKA.off_stk. rewrite P2, MState.unsigned_lit by lia. unfold O4CRSc.CHECK_REFUSAL_SUBMIT_FRAME, AsanCells.CELL_K. lia.
    + unfold O4AKA.off_stk. rewrite P2, MState.unsigned_lit by lia. unfold O4CRSc.CHECK_REFUSAL_SUBMIT_FRAME, LF_FBYTES in *. lia.
    + apply (decode_leafb_addressable W2 (ms_mem ms0) (lc_F cx + 32) 32 HRA3); [lia | lia | |].
      * pose proof (@decode_leafb_app_of_in_app rc (lc_F cx) 256 255 Happ2 ltac:(lia)) as HA.
        unfold AsanCells.app_mem in HA. unfold AsanCells.APPMEM_END.
        unfold AsanCells.LOWMEM_END, AsanCells.HIGHMEM_BEG, AsanCells.APPMEM_END in HA. lia.
      * intros i Hi. replace (lc_F cx + 32 + i) with (lc_F cx + (32 + i)) by ring.
        apply (@decode_leafb_app_of_in_app rc (lc_F cx) 256 (32 + i) Happ2). lia.
    + rewrite P2, MState.unsigned_lit by lia. unfold O4CRSc.CHECK_REFUSAL_SUBMIT_FRAME.
      apply (decode_leafb_rng_vis W2 (ms_mem ms0)); [lia | change (2 ^ 64) with 18446744073709551616; lia |].
      intros a Ha. apply Hpres3. rewrite ELS. lia.
    + exact (proj1 (decode_leafb_rng_cells W2)).
    + exact (proj2 (decode_leafb_rng_cells W2)).
    + intros i Hi.
      pose proof (decode_leafb_rng_shadow W2 (ms_mem ms0) (lc_F cx + 32) 32 HRA3 ltac:(lia) ltac:(lia)
        ltac:(change (2 ^ 64) with 18446744073709551616; unfold LF_FBYTES in HFceil; lia)) as HRS.
      apply (ExecF.rng_sub _ _ _ _ _ HRS); unfold AsanCells.shadow_addr.
      * pose proof (Z.div_le_mono (lc_F cx + 32) (lc_F cx + 32 + i) 8 ltac:(lia) ltac:(lia)). lia.
      * pose proof (Z.div_le_mono (lc_F cx + 32 + i) (lc_F cx + 32 + 32 - 1) 8 ltac:(lia) ltac:(lia)). lia.
    + apply (decode_leafb_rng_vis W2 (ms_mem ms0) (lc_F cx + 32) 32);
        [lia | change (2 ^ 64) with 18446744073709551616; unfold LF_FBYTES in HFceil; lia |].
      intros a Ha. apply HFpres3. unfold LF_FBYTES. lia.
    + rewrite O4CRSc.check_refusal_submit_queued_at. apply o4s_rng_hull; unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI; lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & Ec3 & HJ3 & HP3 & KE3 & Hgr3 & HX3).
change (YK11.getr (ms_regs ms0) 1) with (YK11.getr (ms_regs ms0) 1%bv) in Ec3. rewrite P1 in Ec3. subst c3.
(* the invariant after the call *)
assert (HF8 : lc_F cx / 8 <= lc_F cx) by (apply Z.div_le_upper_bound; lia).
assert (INV4 : o4s_inv B MT cx op cs (o4b_sl op) (o4b_rv cx op) ly2 S2 W2 regs3 mem3 md3 e1).
{ apply (o4b_inv_kept cx op cs _ _ ly2 S2 W2 (ms_regs ms0) (ms_mem ms0) _ e1 ESTACK ly2 S2 W2 regs3 mem3 md3 LAWS MTL HB
    INV3 HJ3 eq_refl (Permutation_refl _) HP3 (mo_le_refl MT MTL S2)).
  - unfold ESTACK. rewrite ELS. lia.
  - intros a Ha Hna. apply KE3; [lia | rewrite PSP; exact Hna].
  - intros b m i Hb Hi.
    destruct (al_blocks segs B LAWS ly2 S2 W2 (ms_mem ms0) _ b m HARc3 Hb) as (_ & H4096 & Hc & _).
    apply KE3; [change (2 ^ 64) with 18446744073709551616; lia | rewrite PSP; unfold ESTACK; lia].
  - intros a Ha. unfold lc_SH, LF_FBYTES, SHADOW_OFF in Ha. unfold LF_FBYTES in HFceil.
    apply KE3; [change (2 ^ 64) with 18446744073709551616; lia | rewrite PSP; unfold ESTACK; lia].
  - exact Hcs.
  - apply o4b_sl_ok.
  - apply o4b_rv_ok. }
(* the world relation after the leaf: its bytes lie below the leaf's window, and check_refusal_submit keeps B2 *)
assert (HTW3 : lc_tw W2 mem3 B3).
{ rewrite HX3. unfold lc_tw. apply (tw_kept TMAP_A (aview segs (w_H W2) mem2)); [exact HTW2|].
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  rewrite (KE3 x ltac:(lia) ltac:(rewrite PSP; unfold ESTACK; lia)). exact (KR2a x). }
(* ---- +0xc68: `j` to S4 ---- *)
pose proof (o4s_entry0 fx W2 regs3 [] mem3 3176) as HS3.
assert (HEI3 : img_env VAL A_LIM (o4s_E regs3 [])) by apply o4s_env_img.
assert (SHOK3 : sh_ok segs (SLit 0) (@nil shent) (o4s_E regs3 []) (mrestrict (w_H W2) mem3)) by constructor.
paj_run_to_tok RUNTO HS3 HJ3 SHOK3 (0, 0) LO_S4.
{ o4b_awr. }
o4b_kept HFr KR3 W2 mem3 ms1.
pose proof (o4s_kept_all W2 mem3 (ms_mem ms1) KR3) as KR3a. clear HF HFr HG KR3.
assert (HK5 : aregs_preserved regs3 (ms_regs ms1)) by o4b_keep HS3 regs3.
lazymatch type of HJ3 with context [with_vm_backing (m_vm_lazy md3) ?mt md3] =>
  set (md5 := with_vm_backing (m_vm_lazy md3) mt md3) in * end.
assert (INV5 : o4s_inv B MT cx op cs (o4b_sl op) (o4b_rv cx op) ly2 S2 W2 (ms_regs ms1) (ms_mem ms1) md5 e1).
{ apply (o4b_inv_kept cx op cs _ _ ly2 S2 W2 regs3 mem3 md3 e1 0 ly2 S2 W2 (ms_regs ms1) (ms_mem ms1) _ LAWS MTL HB
    INV4 HJ3 eq_refl (Permutation_refl _) HK5 (mo_le_refl MT MTL S2)).
  - rewrite ELS. lia.
  - intros a _ _. exact (KR3a a).
  - intros b m i _ _. exact (KR3a (b + i)).
  - intros a _. exact (KR3a a).
  - exact Hcs.
  - apply o4b_sl_ok.
  - apply o4b_rv_ok. }
pmkst HS3.
apply SRr_ret.
destruct INV5 as (HLC5 & _ & _ & HRV5).
rewrite Forall_forall in HRV5.
pose proof (HRV5 (19, w64 (l_p cx + O4P.fi_off (rw_c (o4_rv cx op)))) ltac:(unfold o4b_rv; cbn; tauto)) as V19.
pose proof (HRV5 (23, w64 (O4P.fi_n (rw_c (o4_rv cx op)))) ltac:(unfold o4b_rv; cbn; tauto)) as V23.
pose proof (HRV5 (20, w64 LF_S4) ltac:(unfold o4b_rv; cbn; tauto)) as V20.
cbn [fst snd] in V19, V23, V20.
exists ly2, S2, (ms_regs ms1), (ms_mem ms1), md5, e1, B3, (rw_c (o4_rv cx op)).
split; [unfold lc_cfg; replace BASE with transport_text by (vm_compute; reflexivity); reflexivity|].
split; [exact Hopc|].
split; [exact HLC5|].
split.
{ unfold lc_tw. apply (tw_kept TMAP_A (aview segs (w_H W2) mem3)); [exact HTW3 | intros x _; exact (KR3a x)]. }
split; [exact M4|].
split; [exact MOP|].
split; [split; [exact V19 | exact V23]|].
exact V20.
Qed.

End calls.

(* ------------------------------------------------------------------ *)
(* 8. The segment                                                      *)
(* ------------------------------------------------------------------ *)

Section op4r. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.

Lemma lc_op4r_ok : lc_op4r_stmt B MT XL RLO RHI.
Proof.
unfold lc_op4r_stmt. intros HP cx op W' c' HB HS.
eapply SRr_bind; [exact (o4_seg_a B MT XL RLO RHI HP cx op W' c' HB HS)|].
intros W2 c2 _ HC. exact (o4_seg_b B MT XL RLO RHI HP cx op W2 c2 HB HC).
Qed.

End op4r.
