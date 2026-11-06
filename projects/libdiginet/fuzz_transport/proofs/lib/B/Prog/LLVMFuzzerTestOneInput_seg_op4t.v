(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AFip.v (segA: the run of a
   wrapper over its own instruction table, the application of a runtime-entry contract at a call site and the
   rebuilding of the symbolic state after the call), A/AFis.v (at_ST's frame and window conjuncts,
   kept_of_frame, chunk_val_at) and A/AF0x.v (st_ok_pin_reg, the val_mem / apresent / fpchain helpers) to
   libreac/fuzz_decode's calloc wrapper in image A (fuzz_decode.asan); module paths changed, and every address,
   cell and offset below is decode's own. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/DecodeCallocWrap.v, with its module paths and module names changed; 3365 of its 3449 lines of code are new or changed and 788 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/LLVMFuzzerTestOneInput_seg_cfg.v, with its module names and numbers changed; 1685 of its 1849 lines of code are new or changed and 3285 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_op4t: the segment OP4T of the image-B walk of fuzz_transport.asan-ubsan's
   LLVMFuzzerTestOneInput, `Lemma lc_op4t_ok : lc_op4t_stmt B MT XL RLO RHI` (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v),
   from the cut SUBT (+0xfa4, op 4 in the tagged mode) to the head of the spec_system_at loop SYSL 0 (+0x10b0) or, when
   len < 4, to SYSJ (+0x1170). Offsets are from the entry 0x812a0 (lib/B/Prog/DgnTransportBList.v, slot k at
   0x812a0 + 4 k).

   The code:
     +0xfa4 .. +0xfe0   56(s1) holds g_ncmd's page; serial = g_ncmd (the sign-extending `lw` at the page - 392),
                        64(s1) = serial, the UBSan index test `bgeu serial, 0x401` (+0xfb4, trap edge 0x82254),
                        s11 = g_cmd, s5 = g_cmd + 40 serial and its UBSan test `bltu s5, 40 serial` (+0xfd0, trap
                        edge 0x82270), `jal __asan_memset` (g_cmd[serial], 0, 40);
     +0xfe4 .. +0x1038  `beqz s6` (no byte left: +0x102c, a0 = 3, a6 = 0, a1 = s9), else the UBSan cursor test
                        `bgeu s4, s9 + 1` (s4 = 1; +0xfec, trap edge 0x8228c), the checked load of the len byte at s9
                        (its slow path +0x1790 .. +0x1798 rejoins at +0x1004; the report call 0x82f88 is not
                        reached), a0 = byte mod 22 + 3 through the constant at 0x103a8 (`mulhu`), a6 = s6 - 1,
                        a1 = s9 + 1; s4 = c (144(s1));
     +0x103c .. +0x109c the tag and the two serial bytes into c[0 .. 2], len into c[24], s6 = 3, s9 = 0xf0,
                        a2 = min (len - 3, a6), 16(s1) = a6, s8 = a1 + a2 with the UBSan take tests `bltu s8, a1`
                        and `beqz s8` (+0x108c / +0x1090, trap edges 0x8232c / 0x82330), 8(s1) = a2,
                        `jal __asan_memcpy` (c + 3, a1, a2);
     +0x10a0 .. +0x10ac `bltu len, 4` (to +0x115c: t2 = 0, `j` SYSJ), else a3 = 3 (SYSL 0).

   The proof: five symbolic runs of the PA token engine over the caller's G journal (lib/B/Prog/TransportGRunB.v
   paj_run_x / paj_run_to_x; the branches at +0x107c and +0x108c by DgnTransportBPaLib.v paj_branch) and the two
   runtime calls through lib/A/Prog/TransportGCg.v gx_intrin_at. The trap edges 0x82254, 0x82270, 0x8228c and 0x82330
   are decided by the runs from their start facts (serial <= 1023, g_cmd's address, s4 = 1 and the cursor's pointer
   at least 4096); the trap edge 0x8232c is the taken side of the split at +0x108c, refuted because a1 + n does not
   wrap. The constant at 0x103a8 is read through the kit statement K1 (lc_rom_view_stmt), lc_op4t_ok's one argument.
   Every point of the segment keeps ot_com (lc_lcore with c in scope, the tagged mode's model facts, 24(s1)); a step
   keeps it when it keeps the bytes ot_keep names (ot_lcore_kept), which every byte the segment writes avoids
   (ot_keep_wr). *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YI16 YE00 YE01 YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v YE2k YCfn Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB settle_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import LLVMFuzzerTestOneInput_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Agree QueueFacts LoopOk LinksProof.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module AG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.Agree.
Module QF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.QueueFacts.
Module LOK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.LoopOk.
Module LP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.LinksProof.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 0. The model                                                        *)
(* ------------------------------------------------------------------ *)

(* lc_tag_vals, field by field, from the len byte's read and the take. *)
Lemma ot_tv : forall (D B1 : list byte) (c3 : TOP.fuzz_in),
  let tv := lc_tag_vals D B1 c3 in
  let c4 := fst (TOP.fuzz_u8_m D c3) in
  let len := snd (TOP.fuzz_u8_m D c3) mod 22 + 3 in
  let n := if len - 3 <? TOP.fi_n c4 then len - 3 else TOP.fi_n c4 in
  tg_serial tv = TW.g_ncmd B1 /\
  tg_B2 tv = TW.upd B1 (TW.A_Cmd_st (TW.g_ncmd B1)) (repeat (DSpec.b8 0) (Z.to_nat TW.Cmd_ESZ)) /\
  tg_len tv = len /\ tg_c4 tv = c4 /\ tg_off tv = TOP.fi_off c4 /\ tg_n tv = n /\
  tg_cbytes tv = [DSpec.b8 TC.TAG; DSpec.b8 (Z.land (TW.g_ncmd B1) 0x7f);
                  DSpec.b8 (Z.land (Z.shiftr (TW.g_ncmd B1) 7) 0x7f)]
                 ++ TW.sub D (TOP.fi_off c4) (Z.to_nat n) ++ repeat (DSpec.b8 0) (Z.to_nat (21 - n)) /\
  tg_c tv = TOP.FuzzIn (TOP.fi_off c4 + n) (TOP.fi_n c4 - n).
Proof.
intros D B1 c3. cbv zeta. unfold lc_tag_vals.
destruct (TOP.fuzz_u8_m D c3) as [c4 lb]. cbn [fst snd]. cbv zeta.
unfold TOP.fuzz_take_m. cbn [tg_serial tg_B2 tg_len tg_c4 tg_off tg_n tg_cbytes tg_c].
repeat split.
Qed.

(* The cursor after the key, address and display bytes is a cursor of D. *)
Lemma ot_c3_ok : forall (D : list byte) (c : TOP.fuzz_in),
  QF.fuzz_in_ok D c -> QF.fuzz_in_ok D (sv_c (lc_sub_kd D (lc_oc D c))).
Proof.
intros D c Hc. unfold lc_oc.
destruct (QF.fuzz_u8_ok D c Hc) as (c1 & v1 & E1 & Hc1 & _). rewrite E1. cbn [fst].
unfold lc_sub_kd.
destruct (QF.fuzz_u8_ok D c1 Hc1) as (c2 & v2 & E2 & Hc2 & _). rewrite E2.
destruct (QF.fuzz_u8_ok D c2 Hc2) as (c3 & v3 & E3 & Hc3 & _). rewrite E3.
destruct (QF.fuzz_u8_ok D c3 Hc3) as (c4 & v4 & E4 & Hc4 & _). rewrite E4.
cbn [sv_c]. exact Hc4.
Qed.

(* ------------------------------------------------------------------ *)
(* 1. Byte and word helpers                                           *)
(* ------------------------------------------------------------------ *)

Lemma ot_zbv : forall x : word, Z_to_bv 64 (bv_unsigned x) = x.
Proof. intros x. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* Byte j < w (w <= 8) of a 64-bit word holding v is byte j of the w-byte little-endian v. *)
Lemma ot_bow : forall v (w j : nat), (j < w)%nat -> (w <= 8)%nat ->
  bv_unsigned (YP09.byte_of_word (Z_to_bv 64 v) (Z.of_nat j)) = YO0f.le_byte v w j.
Proof.
intros v w j Hj Hw. unfold YP09.byte_of_word, YO0f.le_byte. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with (2 ^ 8). change (2 ^ Z.of_N 64) with (2 ^ 64). change 256 with (2 ^ 8).
apply Z.bits_inj'. intros m Hm.
destruct (Z_lt_le_dec m 8) as [Hl|Hl].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
  rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* The w bytes (w <= 8) of a chunk of value v, read through the view. *)
Lemma ot_chunk_rd : forall (E : env) (H : word -> bool) (mm : word -> option byte) (base off : Z) (w : N) (e : sv)
    (v : Z),
  YP09.chunk_ok tfibsegs E (mrestrict H mm) base (YP09.mkChunk off (CVal w e)) -> sv_denot E e = Z_to_bv 64 v ->
  (N.to_nat w <= 8)%nat ->
  forall j, (j < N.to_nat w)%nat ->
    aview tfibsegs H mm (base + off + Z.of_nat j) = Some (YO0f.le_byte v (N.to_nat w) j).
Proof.
intros E H mm base off w e v HC He Hw j Hj. unfold YP09.chunk_ok in HC.
cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len] in HC.
destruct (HC (Z.of_nat j) ltac:(lia)) as (bt & Hb1 & Hb2). cbn [YP09.cbyte] in Hb1. rewrite He in Hb1.
injection Hb1 as <-.
change (aview tfibsegs H mm (base + off + Z.of_nat j))
  with (option_map (fun b : byte => bv_unsigned b) (YP09.mbyte tfibsegs (mrestrict H mm) (base + off + Z.of_nat j))).
rewrite Hb2. cbn [option_map]. f_equal. apply ot_bow; lia.
Qed.

(* Eight bytes of a value, read back as a word. *)
Lemma ot_rdword_of : forall (r : Z -> option Z) a v, 0 <= v < 2 ^ 64 ->
  (forall j, (j < 8)%nat -> r (a + Z.of_nat j) = Some (YO0f.le_byte v 8 j)) -> rdword r a = Some v.
Proof.
  intros r a v Hv H. unfold rdword.
  pose proof (H 0%nat ltac:(lia)) as H0. pose proof (H 1%nat ltac:(lia)) as H1.
  pose proof (H 2%nat ltac:(lia)) as H2. pose proof (H 3%nat ltac:(lia)) as H3.
  pose proof (H 4%nat ltac:(lia)) as H4. pose proof (H 5%nat ltac:(lia)) as H5.
  pose proof (H 6%nat ltac:(lia)) as H6. pose proof (H 7%nat ltac:(lia)) as H7.
  cbv [Z.of_nat Pos.of_succ_nat Pos.succ] in H0, H1, H2, H3, H4, H5, H6, H7.
  rewrite Z.add_0_r in H0.
  rewrite H0, H1, H2, H3, H4, H5, H6, H7. f_equal. apply le_bytes8. exact Hv.
Qed.

(* An 8-byte chunk of value v, read back as a word through the view. *)
Lemma ot_rdword_chunk : forall (E : env) (H : word -> bool) (mm : word -> option byte) (base off : Z) (e : sv) (v : Z),
  YP09.chunk_ok tfibsegs E (mrestrict H mm) base (YP09.mkChunk off (CVal 8 e)) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview tfibsegs H mm) (base + off) = Some v.
Proof.
intros E H mm base off e v HC He Hv. apply ot_rdword_of; [exact Hv|].
intros j Hj. exact (ot_chunk_rd E H mm base off 8 e v HC He ltac:(cbn; lia) j ltac:(cbn; lia)).
Qed.

(* A chunk of a region, from the region's facts. *)
Lemma ot_region_chunk : forall (E : env) (m : word -> option byte) n lo hi wlo whi cs c,
  YP09.region_ok tfibsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> In c cs ->
  YP09.chunk_ok tfibsegs E m (bv_unsigned (ew E n)) c.
Proof.
intros E m n lo hi wlo whi cs c (_ & _ & _ & Hcs) Hin. rewrite Forall_forall in Hcs. exact (Hcs c Hin).
Qed.

(* The value of a register in a symbolic state's machine state, as the denotation of its symbolic value. *)
Ltac ot_rv HS r H :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = sv_denot Ex e) by exact (st_ok_pi_restrict_reg Hh Ex ssx msx r HS)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = sv_denot Ex e) by exact (st_ok_restrict_reg segsx Hh Ex ssx msx r HS)
  end.

(* Normalise the symbolic state of HS. *)
Ltac ot_norm HS :=
  lazymatch type of HS with
  | st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ _ ?s _ =>
      let s' := eval vm_compute in s in change s with s' in HS
  end.

(* An atom's denotation. *)
Lemma ot_den_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small, Z.add_0_r by exact Hv. reflexivity. Qed.
Lemma ot_den_off : forall E n v k, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n k) = Z_to_bv 64 (v + k).
Proof. intros E n v k H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by exact Hv. reflexivity. Qed.
Lemma ot_den_same : forall E n (w : word), ew E n = w -> sv_denot E (SOff n 0) = w.
Proof. intros E n w H. cbn [sv_denot]. rewrite H, Z.add_0_r. apply ot_zbv. Qed.
(* A denotation from its unsigned value. *)
Lemma ot_den_U : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. rewrite <- H. unfold U. symmetry. apply ot_zbv. Qed.

(* An eight-byte word of a view kept where its bytes are. *)
Lemma ot_rdword_kept : forall (r r' : Z -> option Z) a v,
  rdword r a = Some v -> (forall i, 0 <= i < 8 -> r' (a + i) = r (a + i)) -> rdword r' a = Some v.
Proof. intros r r' a v H K. rewrite (rdword_ext r r' a K). exact H. Qed.

(* A register a run left as the start state's (its symbolic value is its own atom). *)
Ltac ot_same HS EE :=
  lazymatch goal with |- YK11.getr (ms_regs ?msx) ?r = YK11.getr ?regs0 ?r =>
    let H := fresh "Hr" in ot_rv HS r H; rewrite H; apply ot_den_same; apply EE; reflexivity end.

(* c's 32 bytes. *)
Lemma ot_cs_len : forall (l : list byte) len d k, length l = 24%nat ->
  length (TW.zs (TOP.cmd_struct l len d k)) = 32%nat.
Proof.
intros l len d k Hl. unfold TW.zs, TOP.cmd_struct. rewrite length_map, !length_app, Hl.
unfold TW.put. rewrite length_Z_to_le_bytes. reflexivity.
Qed.

Section op4t. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation rd W mem := (mrestrict (w_H W) mem).
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* serial = g_ncmd B1 is below CMDS_MAX: the operation's model answer is Some (LoopOk.op_ok at the stream
   fun _ => 1), op_submit_m answers Some (lc_op4_eq), and lc_submit_tag_eq's first test is serial < CMDS_MAX. *)
Lemma ot_serial : forall (cx : lcx) (op : lop) (B1 : list byte),
  lc_opok cx op -> lc_opc (l_pl cx) (lo_c op) = 4 -> TC.op_begin_m (lo_B op) = Some (B1, tt) -> TW.g_raw B1 = 0 ->
  0 <= TW.g_ncmd B1 < TC.CMDS_MAX.
Proof.
intros cx op B1 (HA & Hops & Hc & Hn & Hk) Ho HOB HR.
destruct (LOK.op_ok LP.links_holds timg_B (lo_ops op) (lo_B op) (fun _ => 1) (l_pl cx) (lo_c op) (lo_k op)
  HA Hops Hc Hn ltac:(lia) ltac:(lia)) as (B' & c' & k' & E & _).
rewrite (lc_op4_eq timg_B (lo_B op) (fun _ => 1) (l_pl cx) (lo_c op) (lo_k op) Ho) in E.
rewrite (lc_submit_tag_eq (lo_B op) B1 (l_pl cx) _ HOB HR) in E. cbv zeta in E.
pose proof (ot_tv (l_pl cx) B1 (sv_c (lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op))))) as TV. cbv zeta in TV.
destruct TV as (Eser & _). rewrite Eser in E.
split; [unfold TW.g_ncmd; apply QF.u_at_nonneg|].
destruct (TC.CMDS_MAX <=? TW.g_ncmd B1) eqn:EC; [discriminate E|].
apply Z.leb_gt. exact EC.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The geometry and the bytes the loop's facts read                 *)
(* ------------------------------------------------------------------ *)

(* lc_core's G journal (segs.v lc_core's first clause), at a memory and model. *)
Definition ot_J (cx : lcx) (ly' : alayout) (S' : astate) (W' : world segs) (mem' : word -> option byte) (md' : Model)
    (e : Z) : Prop :=
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] LLVMF_STK (lc_sp0 cx) [] (l_ly cx) (l_S cx)
    (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly' S' W' mem' md' e.

(* The bytes lc_lcore and the 24(s1) slot read: the 13 saved words, the frame's flag word, the input, the frame's
   32 shadow bytes, and the stack slots from 24(s1) up but 64(s1) .. 71(s1). *)
Definition ot_keep (cx : lcx) (a : Z) : Prop :=
  (lc_sp0 cx - 104 <= a < lc_sp0 cx) \/ (lc_F cx + 248 <= a < lc_F cx + 256) \/
  (l_p cx <= a < l_p cx + l_n cx) \/ (lc_SH cx <= a < lc_SH cx + 32) \/
  (lc_sp1 cx + 24 <= a < lc_sp1 cx + 64) \/ (lc_sp1 cx + 72 <= a < lc_sp1 cx + 192).

(* What the core and the slot's pre fix about the stack, the frame and the input. *)
Lemma ot_geo : forall cx ly' S' W' regs' mem' md' e,
  AR_laws segs B -> lc_base B MT XL RLO RHI cx -> lc_core B cx ly' S' W' regs' mem' md' e ->
  alloc_ceiling + 32432 <= lc_sp1 cx /\ lc_sp0 cx - 336 <= lc_sp1 cx <= lc_sp0 cx - 320 /\ lc_sp1 cx mod 32 = 0 /\
  lc_sp0 cx <= 2 ^ 47 /\
  4096 <= lc_F cx /\ lc_F cx mod 64 = 0 /\ lc_F cx + 256 <= alloc_ceiling /\ in_app (lc_F cx) 256 /\
  (forall a, lc_F cx <= a < lc_F cx + 256 -> ~ in_img segs a) /\
  0 <= l_n cx < 2 ^ 26 /\ l_n cx = Z.of_nat (length (l_pl cx)) /\
  (l_n cx = 0 -> l_p cx = A_EMPTY) /\
  (0 < l_n cx -> In (l_p cx, l_n cx) (ablocks B ly' S') /\ 4096 <= l_p cx /\ l_p cx + l_n cx <= alloc_ceiling /\
     in_app (l_p cx) (l_n cx) /\ (lc_F cx + 256 <= l_p cx \/ l_p cx + l_n cx <= lc_F cx) /\
     (forall a, l_p cx <= a < l_p cx + l_n cx -> ~ in_img segs a)).
Proof.
intros cx ly' S' W' regs' mem' md' e LAWS HB HC.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as G.
destruct G as [HAR Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & Hsp1al & _ & HF4096 & HFal & HFceil & _).
destruct Hstk as (Hceil & Hslo & Hshi & H47).
destruct (frames_bounds segs B LAWS ly' S' W' mem' md' LF_CID (l_fpos cx) HAR HFin) as (_ & _ & HFapp).
rewrite HFaddr in HFapp. change (fs_frame_bytes LF_CID) with 256 in HFapp.
unfold LF_FBYTES, LF_FRAME in *.
assert (Hpn : (l_n cx = 0 /\ l_p cx = A_EMPTY) \/ (0 < l_n cx < 2 ^ 26 /\ In (l_p cx, l_n cx) (ablocks B (l_ly cx) (l_S cx)))).
{ unfold lc_base, tfib_lib_pre_x in HB. destruct HB as (_ & _ & _ & _ & Hpn & _). exact Hpn. }
split; [exact Hsp1c|]. split; [lia|]. split; [exact Hsp1al|]. split; [lia|].
split; [exact HF4096|]. split; [exact HFal|]. split; [exact HFceil|]. split; [exact HFapp|].
split.
{ intros a Ha. apply (frm_img segs B LAWS ly' S' W' mem' md' LF_CID (l_fpos cx) a HAR HFin).
  rewrite HFaddr. change (fs_frame_bytes LF_CID) with 256. exact Ha. }
split; [exact (proj1 Hn)|]. split; [exact (proj2 Hn)|].
split; [intros H0; destruct Hpn as [(_ & Hp) | (Hn0 & _)]; [exact Hp | lia]|].
intros Hn0. pose proof (HINg Hn0) as Hin.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hp4 & Hpc & Hpapp & _).
assert (RQ : req_size (l_n cx) = l_n cx) by (unfold req_size; destruct (Z.eqb_spec (l_n cx) 0); lia).
rewrite RQ in Hpc, Hpapp.
pose proof (sep_block_frame segs B LAWS ly' S' W' mem' md' _ _ _ _ HAR Hin HFin) as Hd.
rewrite RQ, HFaddr in Hd. change (fs_frame_bytes LF_CID) with 256 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
split; [exact Hin|]. split; [exact Hp4|]. split; [exact Hpc|]. split; [exact Hpapp|]. split; [lia|].
intros a Ha. apply (blk_img segs B LAWS ly' S' W' mem' md' (l_p cx) (l_n cx) a HAR Hin). rewrite RQ. exact Ha.
Qed.

(* The input has a byte: the operation's cursor has bytes left. *)
Lemma ot_n_pos : forall cx op, lc_opok cx op -> 0 < Z.of_nat (length (l_pl cx)).
Proof. intros cx op (_ & _ & (H0 & H1 & H2) & Hn & _). lia. Qed.

(* lc_core across a step that keeps ly', S', W' and the journal (at the new memory and model), the registers sp, gp,
   tp, s0, s1, the presence of every byte and the bytes ot_keep names. *)
Lemma ot_core_kept : forall cx ly' S' W' regs' mem' md' e regs2 mem2 md2,
  l_n cx = Z.of_nat (length (l_pl cx)) ->
  lc_core B cx ly' S' W' regs' mem' md' e -> ot_J cx ly' S' W' mem2 md2 e ->
  YK11.getr regs2 2 = YK11.getr regs' 2 -> YK11.getr regs2 3 = YK11.getr regs' 3 ->
  YK11.getr regs2 4 = YK11.getr regs' 4 -> YK11.getr regs2 8 = YK11.getr regs' 8 ->
  YK11.getr regs2 9 = YK11.getr regs' 9 ->
  (forall a, apresent (w_H W') mem' a -> apresent (w_H W') mem2 a) ->
  (forall a, ot_keep cx a -> aview segs (w_H W') mem2 a = aview segs (w_H W') mem' a) ->
  lc_core B cx ly' S' W' regs2 mem2 md2 e.
Proof.
intros cx ly' S' W' regs' mem' md' e regs2 mem2 md2 Hnl HC HJ2 P2 P3 P4 P8 P9 HPR K.
destruct HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal & HFceil &
  HFpres & HFL & HIN).
split; [exact HJ2|]. split; [exact Hfrs|]. split; [exact HlyF|]. split; [exact HPERM|].
split; [rewrite P2; exact Rsp|]. split; [rewrite P8; exact R8|]. split; [rewrite P9; exact R9|].
split; [rewrite P3; exact Rgp|]. split; [rewrite P4; exact Rtp|].
split; [exact Hsp1|]. split; [exact Hsp1al|].
split.
{ unfold lc_saved in *. rewrite Forall_forall in HSAV |- *. intros o Ho.
  apply (ot_rdword_kept _ _ _ _ (HSAV o Ho)). intros i Hi. apply K. left.
  unfold LF_SAVED in Ho. cbn [In] in Ho.
  repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
split; [exact HF4096|]. split; [exact HFal|]. split; [exact HFceil|].
split; [intros a Ha; exact (HPR a (HFpres a Ha))|].
split.
{ apply (ot_rdword_kept _ _ _ _ HFL). intros i Hi. apply K. right; left. unfold LF_FBYTES. lia. }
destruct HIN as (HPAYg & HPAYv). split.
- apply (garr8_frame segs _ _ _ _ HPAYg). intros a Ha. apply (mbyte_of_aview segs). apply K. right; right; left.
  rewrite length_map in Ha. lia.
- intros i Hi. rewrite K by (right; right; left; lia). exact (HPAYv i Hi).
Qed.

(* lc_lcore (c in scope, body out) across such a step that also keeps s2, s3 and s10. *)
Lemma ot_lcore_kept : forall cx op k ly' S' W' regs' mem' md' e regs2 mem2 md2,
  l_n cx = Z.of_nat (length (l_pl cx)) ->
  lc_lcore B MT cx op true false k ly' S' W' regs' mem' md' e -> ot_J cx ly' S' W' mem2 md2 e ->
  YK11.getr regs2 2 = YK11.getr regs' 2 -> YK11.getr regs2 3 = YK11.getr regs' 3 ->
  YK11.getr regs2 4 = YK11.getr regs' 4 -> YK11.getr regs2 8 = YK11.getr regs' 8 ->
  YK11.getr regs2 9 = YK11.getr regs' 9 -> YK11.getr regs2 18 = YK11.getr regs' 18 ->
  YK11.getr regs2 19 = YK11.getr regs' 19 -> YK11.getr regs2 26 = YK11.getr regs' 26 ->
  (forall a, apresent (w_H W') mem' a -> apresent (w_H W') mem2 a) ->
  (forall a, ot_keep cx a -> aview segs (w_H W') mem2 a = aview segs (w_H W') mem' a) ->
  lc_lcore B MT cx op true false k ly' S' W' regs2 mem2 md2 e.
Proof.
intros cx op k ly' S' W' regs' mem' md' e regs2 mem2 md2 Hnl HL HJ2 P2 P3 P4 P8 P9 P18 P19 P26 HPR K.
destruct HL as (HC & (F18 & F26) & HSP & HFSH & HOK & He & HM & R19).
split; [exact (ot_core_kept cx ly' S' W' regs' mem' md' e regs2 mem2 md2 Hnl HC HJ2 P2 P3 P4 P8 P9 HPR K)|].
split; [split; [rewrite P18; exact F18 | rewrite P26; exact F26]|].
split.
{ unfold lc_spills in *. rewrite Forall_forall in HSP |- *. intros o Ho.
  apply (ot_rdword_kept _ _ _ _ (HSP o Ho)). intros i Hi. apply K.
  assert (Hf : In (fst o) (map fst (lf_spill_loop (lc_F cx)))) by (apply in_map; exact Ho).
  rewrite lf_spill_offsets in Hf. cbn [In] in Hf.
  repeat (destruct Hf as [Hf | Hf]; [rewrite <- Hf; right; right; right; right; lia|]). destruct Hf. }
split.
{ intros i Hi. rewrite K by (right; right; right; left; lia). exact (HFSH i Hi). }
split; [exact HOK|]. split; [exact He|]. split; [exact HM|]. rewrite P19. exact R19.
Qed.

(* The bytes this segment writes avoid the bytes ot_keep names: the stack window of a call below s1, the slots
   8(s1) .. 23(s1) and 64(s1) .. 71(s1), c, and the bytes of G. *)
Lemma ot_keep_wr : forall cx ly' S' W' regs' mem' md' e,
  AR_laws segs B -> lc_base B MT XL RLO RHI cx -> lc_core B cx ly' S' W' regs' mem' md' e ->
  forall a, ot_keep cx a ->
    0 <= a < 2 ^ 64 /\ ~ (lc_sp1 cx - ESTACK <= a < lc_sp1 cx) /\ ~ (lc_sp1 cx + 8 <= a < lc_sp1 cx + 24) /\
    ~ (lc_sp1 cx + 64 <= a < lc_sp1 cx + 72) /\ ~ (lc_F cx + 32 <= a < lc_F cx + 64) /\ ~ inG TG.G_HARNESS_B a.
Proof.
intros cx ly' S' W' regs' mem' md' e LAWS HB HC a Ha.
destruct (ot_geo cx ly' S' W' regs' mem' md' e LAWS HB HC) as (Gs1 & Gs01 & Gs1al & Gs047 & GF4 & GFal & GFc & GFapp &
  GFimg & Gn & Gnl & Gp0 & Gp).
pose proof alloc_ceiling_val as Hac.
assert (HGl : inG TG.G_HARNESS_B a -> 0 <= a < kLowMemEnd)
  by (intros HGa; exact (transportb_segs_low a (trans_g_img a HGa))).
unfold ESTACK, kLowMemEnd in *. unfold lc_SH, SHADOW_OFF in Ha.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in GFapp.
destruct Ha as [Ha | [Ha | [Ha | [Ha | [Ha | Ha]]]]].
- split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros HGa. pose proof (HGl HGa). lia.
- split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros HGa.
  exact (GFimg a ltac:(lia) (trans_g_img a HGa)).
- assert (Hn0 : 0 < l_n cx) by lia. destruct (Gp Hn0) as (_ & Gp4 & Gpc & Gpapp & GdpF & Gpimg).
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros HGa.
  exact (Gpimg a Ha (trans_g_img a HGa)).
- assert (HF8 : 0 <= lc_F cx / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  unfold lc_SH, SHADOW_OFF in Ha.
  remember (lc_F cx / 8) as f8 eqn:Ef8. clear Ef8.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros HGa. pose proof (HGl HGa). lia.
- split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros HGa. pose proof (HGl HGa). lia.
- split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros HGa. pose proof (HGl HGa). lia.
Qed.

(* A payload byte of the world lies off the stack, off the stack slots the segment writes and off c. *)
Lemma ot_tw_out : forall cx ly' S' W' regs' mem' md' e,
  AR_laws segs B -> lc_base B MT XL RLO RHI cx -> lc_core B cx ly' S' W' regs' mem' md' e ->
  forall x, tw_in TMAP_B x ->
    0 <= x < 2 ^ 64 /\ ~ (lc_sp1 cx - ESTACK <= x < lc_sp1 cx) /\ ~ (lc_sp1 cx + 8 <= x < lc_sp1 cx + 24) /\
    ~ (lc_sp1 cx + 64 <= x < lc_sp1 cx + 72) /\ ~ (lc_F cx + 32 <= x < lc_F cx + 64) /\ inG TG.G_HARNESS_B x.
Proof.
intros cx ly' S' W' regs' mem' md' e LAWS HB HC x Hx.
destruct (ot_geo cx ly' S' W' regs' mem' md' e LAWS HB HC) as (Gs1 & Gs01 & Gs1al & Gs047 & GF4 & GFal & GFc & GFapp &
  GFimg & _).
pose proof alloc_ceiling_val as Hac.
assert (HGx : inG TG.G_HARNESS_B x).
{ destruct Hx as (o & b & n & Hin & Hr). unfold inG. apply Exists_exists. exists (b, n).
  split; [exact (TMAP_B_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia]. }
pose proof (transportb_segs_low x (trans_g_img x HGx)) as Hl. unfold kLowMemEnd, ESTACK in *.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [|exact HGx].
intros Hc. exact (GFimg x ltac:(lia) (trans_g_img x HGx)).
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The cuts inside the segment                                      *)
(* ------------------------------------------------------------------ *)

Definition ot_kd (cx : lcx) (op : lop) : lsv := lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op)).
Definition ot_tvx (cx : lcx) (op : lop) (B1 : list byte) : ltg := lc_tag_vals (l_pl cx) B1 (sv_c (ot_kd cx op)).

(* What every point of the segment keeps: the loop's facts with c in scope, the model's facts of the tagged mode and
   24(s1) (segs.v lc_sub_common, lc_st_subt, lc_tag_common). *)
Definition ot_com (cx : lcx) (op : lop) (B1 : list byte) (ly' : alayout) (S' : astate) (W' : world segs)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (e : Z) : Prop :=
  lc_lcore B MT cx op true false (lo_k op) ly' S' W' regs' mem' md' e /\
  lc_opc (l_pl cx) (lo_c op) = 4 /\ TC.op_begin_m (lo_B op) = Some (B1, tt) /\ TW.g_raw B1 = 0 /\
  0 <= TW.g_ncmd B1 < TC.CMDS_MAX /\
  rdword (aview segs (w_H W') mem') (lc_sp1 cx + 24) =
    Some (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (TW.S_queued (lo_B op))))).

(* The registers serial's index test and the memset leave: s5 = g_cmd + 40 serial, s7 = 0x401, s11 = g_cmd. *)
Definition ot_rs (regs' : bvmap 5 word) (B1 : list byte) : Prop :=
  YK11.getr regs' 21 = w64 (TB_g_cmd + 40 * TW.g_ncmd B1) /\ YK11.getr regs' 23 = w64 0x401 /\
  YK11.getr regs' 27 = w64 TB_g_cmd.

(* The entry of __asan_memset (g_cmd[serial], 0, 40) (+0xfe0): a0 = s5, 64(s1) = serial; the world op_begin's B1,
   c as OP4A left it, s9 / s6 the cursor before the len byte, s4 = 1. *)
Definition ot_at_ms (cx : lcx) (op : lop) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' e B1,
    let kd := ot_kd cx op in
    c' = mkCfg (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (transportb_sigma TB___asan_memset)) mem'
      (YK11.seg_rom segs)) md' /\
    ot_com cx op B1 ly' S' W' regs' mem' md' e /\ lc_tw W' mem' B1 /\
    garr8 segs (rd W' mem') (lc_F cx + 32)
      (TW.zs (TOP.cmd_struct (repeat (DSpec.b8 0) 24) 0 (sv_display kd) (sv_key kd))) /\
    lc_cur cx regs' 25 22 (sv_c kd) /\ YK11.getr regs' 20 = w64 1 /\
    rdword (aview segs (w_H W') mem') (lc_sp1 cx + 64) = Some (TW.g_ncmd B1) /\
    ot_rs regs' B1 /\
    YK11.getr regs' 10 = w64 (TB_g_cmd + 40 * TW.g_ncmd B1) /\
    YK11.getr regs' 11 = w64 0 /\ YK11.getr regs' 12 = w64 40 /\
    YK11.getr regs' 1 = w64 (transportb_text + 0xfe4).

(* ------------------------------------------------------------------ *)
(* 4. Run A: +0xfa4 .. +0xfe0                                          *)
(* ------------------------------------------------------------------ *)

(* The environment of a run: the registers as atoms 0 .. 31, then the extra atoms from 32 up. *)
Definition ot_E (regs : bvmap 5 word) (extra : list word) : env := Eimg (PI := PI_transportb) (Ereg regs extra).

(* +0xfa4 .. +0xfe0: 56(s1) holds g_ncmd's page (transportb_hi 15), g_ncmd at page - 392 (atom 33 = serial, read by
   the sign-extending `lw`), the store of serial at 64(s1), s11 = g_cmd (object 19, atom 260), s5 = g_cmd + 40 serial,
   the memset's arguments. The two UBSan tests (+0xfb4: serial >= 0x401; +0xfd0: s5 < 40 serial) are decided by the
   facts on atoms 33 and 260. *)
Definition ot_spA : YP09.region :=
  YP09.mkRegion (Some 9%nat) 56 72 64 72 [YP09.mkChunk 56 (CVal 8 (SOff (A_HI 15) 0))].
Definition ot_ncmd : YP09.region :=
  YP09.mkRegion (Some (A_HI 15)) (-392) (-388) 0 0 [YP09.mkChunk (-392) (CVal 4 (SOff 33 0))].
Definition ot_factsA : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (33%nat, mkAF 0 1023 0);
  (260%nat, mkAF TB_g_cmd TB_g_cmd 0)] [] [].
Definition ot_ssA : sstate := mkSS 0xfa4 sr_atoms [ot_spA; ot_ncmd] None ot_factsA.

Lemma ot_den_cmd : forall E s, ew E 33 = w64 s -> ew E (A_OBJ 19) = Z_to_bv 64 TB_g_cmd -> 0 <= s < 1024 ->
  sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 33 0) (SLit 40)) (SOff 260 0)) = w64 (TB_g_cmd + 40 * s).
Proof.
intros E s H33 H260 Hs.
rewrite <- (ot_zbv (sv_denot E _)). unfold w64. f_equal.
change (U E (SAlu ALU_ADD (SMd M_MUL (SOff 33 0) (SLit 40)) (SOff 260 0)) = TB_g_cmd + 40 * s).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite !U_SOff, U_SLit.
change 260%nat with (A_OBJ 19). rewrite H33, H260. unfold w64.
rewrite !unsigned_lit_small by (unfold TB_g_cmd; lia). rewrite !Z.add_0_r.
unfold zcanon, M64, TB_g_cmd. rewrite !(Z.mod_small _ (2 ^ 64)) by lia. lia.
Qed.

Lemma ot_runA : forall cx op (W : world segs) c,
  lp_prem B MT XL RLO RHI -> lc_base B MT XL RLO RHI cx -> lc_st_subt B MT cx op W c -> SRr segs W c (ot_at_ms cx op).
Proof.
intros cx op W c HP HB (ly' & S' & regs' & mem' & md' & e & B1 & -> & HSC & Hraw & H24 & Hcur & R20).
destruct HSC as (Hopc & HL & Hob & Htw & Hcs).
pose proof (lp_laws B MT XL RLO RHI HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned B MT XL RLO RHI HP)) as HGX.
pose proof HL as (HC & (F18 & F26) & HSP & HFSH & HOK & He & HM & R19).
pose proof (ot_serial cx op B1 HOK Hopc Hob Hraw) as Hser.
assert (Hs1024 : 0 <= TW.g_ncmd B1 < 1024) by exact Hser.
pose proof (ot_geo cx ly' S' W regs' mem' md' e LAWS HB HC) as (Gs1 & Gs01 & Gs1al & Gs047 & GF4 & GFal & GFc & GFapp &
  GFimg & Gn & Gnl & Gp0 & Gp).
pose proof HC as (HJ & _ & _ & _ & Rsp & R8 & R9 & Rgp & Rtp & _).
pose proof alloc_ceiling_val as Hac.
pose proof lf_spill_pages as (_ & _ & _ & _ & _ & HP15).
set (E := ot_E regs' [w64 SHADOW_OFF; w64 (TW.g_ncmd B1)]).
assert (HEI : img_env VAL A_LIM E) by (unfold E, ot_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs' r)
  by (intros n r Hn; unfold E, ot_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E33 : ew E 33 = w64 (TW.g_ncmd B1))
  by (unfold E, ot_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs' _ 1)).
assert (EH15 : ew E (A_HI 15) = Z_to_bv 64 (transportb_hi 15))
  by (unfold E, ot_E; rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia); reflexivity).
assert (E260 : ew E (A_OBJ 19) = Z_to_bv 64 TB_g_cmd)
  by (unfold E, ot_E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); reflexivity).
pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite R9 in E9.
assert (U9 : bv_unsigned (ew E 9) = lc_sp1 cx) by (rewrite E9; apply unsigned_lit_small; lia).
assert (UH15 : bv_unsigned (ew E (A_HI 15)) = transportb_hi 15) by (rewrite EH15, HP15; reflexivity).
assert (U260 : bv_unsigned (ew E 260%nat) = TB_g_cmd) by (change 260%nat with (A_OBJ 19); rewrite E260; reflexivity).
destruct (gx_open segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & _ & _).
assert (HSTKW : forall a, lc_sp0 cx - LLVMF_STK <= a < lc_sp0 cx -> writable_at segs (rd W mem') a).
{ intros a Ha. apply (apresent_writable segs).
  refine (proj1 (awr_byte_present segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJi _)). left. exact Ha. }
assert (HS : @st_ok_pi segs VAL (l_fx cx) E ot_ssA
  (restrict (w_H W) (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (BASE + 0xfa4)) mem' (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. apply (@pa_entry_st_ok_full (l_fx cx) rc transportb_listing PI_transportb).
  - unfold E, ot_E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold ot_spA, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply HSTKW. unfold LLVMF_STK. lia.
      * apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val segs E _ (lc_sp1 cx) 56 8 (SOff (A_HI 15) 0) (transportb_hi 15));
          [apply ot_den_atom; [exact EH15 | rewrite HP15; lia] | rewrite HP15; lia | lia |].
        apply (val_mem_of_rdword segs).
        unfold lc_spills in HSP. rewrite Forall_forall in HSP.
        refine (HSP (56, transportb_hi 15) _).
        unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm. cbn [app].
        repeat (first [left; reflexivity | right]).
    + unfold ot_ncmd, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite UH15, HP15. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ 0x5df788 (-392) 4 (SOff 33 0) (TW.g_ncmd B1));
        [apply ot_den_atom; [exact E33 | unfold TC.CMDS_MAX in Hser; lia]
        | split; [apply QF.u_at_nonneg | exact (QF.u_at_bound B1 TW.OFF_g_ncmd 4)] | lia |].
      replace (0x5df788 + -392) with (TB_g_ncmd + 0) by reflexivity.
      pose proof (tw_read_val segs _ TMAP_B B1 TW.OFF_g_ncmd TB_g_ncmd TW.SZ_g_ncmd 0 4 TMAP_B_ok Htw TMAP_B_g_ncmd
        ltac:(lia) ltac:(unfold TW.SZ_g_ncmd; lia)) as V.
      rewrite Z.add_0_r in V. rewrite Z.add_0_r. exact V.
  - apply pairwise_disjoint_of_extents.
    unfold ot_spA, ot_ncmd, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9, UH15, HP15. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  - unfold ot_factsA, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, E33, U260. unfold w64. rewrite unsigned_lit_small by lia.
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold TB_g_cmd; lia. }
assert (SHOK : sh_ok segs (SOff 26 0) [] E (rd W mem')) by constructor.
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
unfold lc_cfg.
change (w64 (transportb_text + LO_SUBT)) with (Z_to_bv 64 (BASE + 0xfa4)).
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]].
  - intros a Ha. cbn [ot_spA YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U9 in Ha.
    left. split; [left; unfold LLVMF_STK; lia | lia].
  - intros a Ha. cbn [ot_ncmd YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
(* the run stopped at the call of __asan_memset *)
pmkst HS. ot_norm HS.
apply SRr_ret.
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (lc_sp1 cx + 64 <= a < lc_sp1 cx + 72) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem' a).
{ intros a Ha Hn.
  apply (YC4b.kept_of_frame E (ss_mem ot_ssA) (w_H W) mem' (ms_mem ms) (fun x => lc_sp1 cx + 64 <= x < lc_sp1 cx + 72)
    HFr); [|exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U9 in Hx; lia |]).
  destruct Hin. }
assert (Q2 : YK11.getr (ms_regs ms) 2 = YK11.getr regs' 2) by ot_same HS EE.
assert (Q3 : YK11.getr (ms_regs ms) 3 = YK11.getr regs' 3) by ot_same HS EE.
assert (Q4 : YK11.getr (ms_regs ms) 4 = YK11.getr regs' 4) by ot_same HS EE.
assert (Q8 : YK11.getr (ms_regs ms) 8 = YK11.getr regs' 8) by ot_same HS EE.
assert (Q9 : YK11.getr (ms_regs ms) 9 = YK11.getr regs' 9) by ot_same HS EE.
assert (Q18 : YK11.getr (ms_regs ms) 18 = YK11.getr regs' 18) by ot_same HS EE.
assert (Q19 : YK11.getr (ms_regs ms) 19 = YK11.getr regs' 19) by ot_same HS EE.
assert (Q20 : YK11.getr (ms_regs ms) 20 = YK11.getr regs' 20) by ot_same HS EE.
assert (Q22 : YK11.getr (ms_regs ms) 22 = YK11.getr regs' 22) by ot_same HS EE.
assert (Q25 : YK11.getr (ms_regs ms) 25 = YK11.getr regs' 25) by ot_same HS EE.
assert (Q26 : YK11.getr (ms_regs ms) 26 = YK11.getr regs' 26) by ot_same HS EE.
assert (HKEEP : forall a, ot_keep cx a -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem' a).
{ intros a Ha. destruct (ot_keep_wr cx ly' S' W regs' mem' md' e LAWS HB HC a Ha) as (H64 & _ & _ & Hsp & _ & _).
  exact (KR a H64 Hsp). }
assert (HPR : forall a, apresent (w_H W) mem' a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a; exact (apresent_grows _ _ _ a HG)).
pose proof (YC4b.st_ok_region_nth E _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
pose proof (ot_rdword_chunk E (w_H W) (ms_mem ms) _ 64 (SOff 33 0) (TW.g_ncmd B1)
  (ot_region_chunk E _ _ _ _ _ _ _ _ RG0 ltac:(left; reflexivity))
  ltac:(apply ot_den_atom; [exact E33 | lia]) ltac:(lia)) as V64.
rewrite U9 in V64.
ot_rv HS (Z_to_bv 5 10) Q10. ot_rv HS (Z_to_bv 5 21) Q21. ot_rv HS (Z_to_bv 5 23) Q23. ot_rv HS (Z_to_bv 5 27) Q27.
ot_rv HS (Z_to_bv 5 11) Q11. ot_rv HS (Z_to_bv 5 12) Q12. ot_rv HS (Z_to_bv 5 1) Q1.
unfold ot_at_ms. exists ly', S', (ms_regs ms), (ms_mem ms). eexists. exists e, B1. cbv zeta.
split; [reflexivity|].
split.
{ split; [exact (ot_lcore_kept cx op (lo_k op) ly' S' W regs' mem' md' e (ms_regs ms) (ms_mem ms) _ Gnl HL HJ
          Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q26 HPR HKEEP)|].
  split; [exact Hopc|]. split; [exact Hob|]. split; [exact Hraw|]. split; [exact Hser|].
  apply (ot_rdword_kept _ _ _ _ H24); intros i Hi; apply HKEEP; right; right; right; right; left; lia. }
split.
{ apply (tw_kept TMAP_B (aview segs (w_H W) mem') _ B1 Htw). intros x Hx.
  destruct (ot_tw_out cx ly' S' W regs' mem' md' e LAWS HB HC x Hx) as (H64 & _ & _ & Hsp & _ & _).
  exact (KR x H64 Hsp). }
split.
{ apply (lc_garr8_kept (w_H W) (w_H W) mem' (ms_mem ms) (lc_F cx + 32) _); [|exact Hcs]. intros j Hj.
  rewrite ot_cs_len in Hj by (rewrite repeat_length; reflexivity).
  apply KR; lia. }
split; [destruct Hcur as (C25 & C22); split; [exact (eq_trans Q25 C25) | exact (eq_trans Q22 C22)]|].
split; [exact (eq_trans Q20 R20)|].
split; [exact V64|].
split; [split; [exact (eq_trans Q21 (ot_den_cmd E (TW.g_ncmd B1) E33 E260 Hs1024))|]|].
{ split; [exact (eq_trans Q23 eq_refl)|]. exact (eq_trans Q27 (ot_den_atom E (A_OBJ 19) TB_g_cmd E260 ltac:(unfold TB_g_cmd; lia))). }
split; [exact (eq_trans Q10 (ot_den_cmd E (TW.g_ncmd B1) E33 E260 Hs1024))|].
split; [exact (eq_trans Q11 eq_refl)|]. split; [exact (eq_trans Q12 eq_refl)|].
exact (eq_trans Q1 (codeptr_val E 4068 HEI)).
Qed.

(* ------------------------------------------------------------------ *)
(* 5. __asan_memset (g_cmd[serial], 0, 40) at +0xfe0                   *)
(* ------------------------------------------------------------------ *)

(* The return of __asan_memset (+0xfe4): the world tg_B2, g_cmd[serial]'s 40 bytes zero. *)
Definition ot_st_fe4 (cx : lcx) (op : lop) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' e B1,
    let kd := ot_kd cx op in
    c' = lc_cfg cx 0xfe4 regs' mem' md' /\
    ot_com cx op B1 ly' S' W' regs' mem' md' e /\ lc_tw W' mem' (tg_B2 (ot_tvx cx op B1)) /\
    garr8 segs (rd W' mem') (lc_F cx + 32)
      (TW.zs (TOP.cmd_struct (repeat (DSpec.b8 0) 24) 0 (sv_display kd) (sv_key kd))) /\
    lc_cur cx regs' 25 22 (sv_c kd) /\ YK11.getr regs' 20 = w64 1 /\
    rdword (aview segs (w_H W') mem') (lc_sp1 cx + 64) = Some (TW.g_ncmd B1) /\
    ot_rs regs' B1.

(* The realigned sp is 16-aligned relative to the entry sp. *)
Lemma ot_sp16 : forall cx ly' S' W' regs' mem' md' e,
  lc_base B MT XL RLO RHI cx -> lc_core B cx ly' S' W' regs' mem' md' e -> (lc_sp1 cx - lc_sp0 cx) mod 16 = 0.
Proof.
intros cx ly' S' W' regs' mem' md' e HB HC.
destruct (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as [_ Hsp0al _ _ _ _ _ _ _].
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1al & _).
apply Z.mod_divide in Hsp1al; [|lia]. apply Z.mod_divide in Hsp0al; [|lia].
destruct Hsp1al as [k Hk]. destruct Hsp0al as [j Hj]. rewrite Hk, Hj.
replace (k * 32 - j * 16) with ((2 * k - j) * 16) by ring. apply Z.mod_mul. lia.
Qed.

(* g_cmd's payload is a range of G, 64-byte aligned, and an entry's granules of 64 bytes lie inside it. *)
Lemma ot_gcmd_inG : forall a, TB_g_cmd <= a < TB_g_cmd + TW.SZ_g_cmd -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (TB_g_cmd, TW.SZ_g_cmd).
split; [exact (TMAP_B_in_G _ _ _ TMAP_B_g_cmd) | unfold in_zr; cbn [fst snd]; lia].
Qed.
Lemma ot_gcmd_gran : forall s, 0 <= s < 1024 ->
  TB_g_cmd <= (TB_g_cmd + 40 * s) / 64 * 64 /\
  (TB_g_cmd + 40 * s + 40 - 1) / 64 * 64 + 64 <= TB_g_cmd + TW.SZ_g_cmd.
Proof.
intros s Hs. unfold TB_g_cmd, TW.SZ_g_cmd. split.
- assert (H : 96578 <= (6180992 + 40 * s) / 64) by (apply Z.div_le_lower_bound; lia). lia.
- assert (H : (6180992 + 40 * s + 40 - 1) / 64 < 97218) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

(* The memset's world: tg_B2 as the model writes it. *)
Lemma ot_B2_eq : forall cx op B1,
  tg_B2 (ot_tvx cx op B1) = TW.upd B1 (TW.OFF_g_cmd + 40 * TW.g_ncmd B1) (repeat (Z_to_bv 8 0) (Z.to_nat 40)).
Proof.
intros cx op B1. unfold ot_tvx.
pose proof (ot_tv (l_pl cx) B1 (sv_c (ot_kd cx op))) as T. cbv zeta in T. destruct T as (_ & EB2 & _).
rewrite EB2. unfold TW.A_Cmd_st, TW.Cmd_ESZ, DSpec.b8. rewrite Z.add_0_r. reflexivity.
Qed.

Lemma ot_call_ms : forall cx op (W : world segs) c,
  lp_prem B MT XL RLO RHI -> lc_base B MT XL RLO RHI cx -> ot_at_ms cx op W c -> SRr segs W c (ot_st_fe4 cx op).
Proof.
intros cx op W c HP HB H. destruct H as (ly' & S' & regs' & mem' & md' & e & B1 & H). cbv zeta in H.
destruct H as (-> & HCOM & Htw & Hcs & Hcur & R20 & V64 & (R21 & R23 & R27) & R10 & R11 & R12 & R1).
pose proof (lp_laws B MT XL RLO RHI HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned B MT XL RLO RHI HP)) as HGX.
pose proof HCOM as (HL & Hopc & Hob & Hraw & Hser & H24).
assert (Hs1024 : 0 <= TW.g_ncmd B1 < 1024) by exact Hser.
pose proof HL as (HC & (F18 & F26) & HSP & HFSH & HOK & He & HM & R19).
pose proof (ot_geo cx ly' S' W regs' mem' md' e LAWS HB HC) as (Gs1 & Gs01 & Gs1al & Gs047 & GF4 & GFal & GFc & GFapp &
  GFimg & Gn & Gnl & Gp0 & Gp).
pose proof HC as (HJ & _ & _ & _ & Rsp & R8 & R9 & Rgp & Rtp & _).
pose proof (ot_sp16 cx ly' S' W regs' mem' md' e HB HC) as Hsp16.
pose proof alloc_ceiling_val as Hac.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
destruct (ot_gcmd_gran (TW.g_ncmd B1) Hs1024) as (Gr1 & Gr2).
destruct (decode_zshadow_ra B ly' S' W mem' md' TB_g_cmd (TB_g_cmd + TW.SZ_g_cmd) (TB_g_cmd + 40 * TW.g_ncmd B1) 40 HAR
  (proj2 (proj2 (proj2 (lp_settle_cells B MT XL RLO RHI HP)))) ltac:(lia) Gr1 Gr2) as (HRA & HHULL).
eapply SRr_bind.
{ apply (@gx_intrin_at (l_fx cx) rc tfib_sink_head segs B LAWS transportb_segs_low OSet
    (transportb_sigma TB___asan_memset)
    (lp_memset B MT XL RLO RHI HP (l_fx cx)) TG.G_HARNESS_B W regs' mem' LLVMF_STK (lc_sp0 cx) [] (l_ly cx) (l_S cx)
    (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly' S' md' e (TB_g_cmd + 40 * TW.g_ncmd B1) 0 40
    (lc_sp1 cx - lc_sp0 cx) (w64 (transportb_text + 0xfe4)) HGX G_HARNESS_B_rw HJ R10 R11 R12).
  - lia.
  - unfold TB_g_cmd; lia.
  - unfold TB_g_cmd; lia.
  - unfold spZ. rewrite Rsp. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact Hsp16.
  - lia.
  - unfold ESTACK, LLVMF_STK. lia.
  - exact Rgp.
  - exact Rtp.
  - exact R1.
  - exact (ret_ok_codeptr_v (PI := PI_transportb) 0xfe4 ltac:(lia) eq_refl).
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|]. intros a Ha. right. apply ot_gcmd_inG.
    unfold TW.SZ_g_cmd. lia.
  - left. unfold kLowMemEnd, TB_g_cmd. lia.
  - exact HRA.
  - intros _. exact HHULL.
  - exact I. }
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HPR & Ra0 & Hset & Hkeep & Hpres2).
apply SRr_ret.
assert (P2 : YK11.getr regs2 2 = YK11.getr regs' 2) by exact (HPR 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : YK11.getr regs2 3 = YK11.getr regs' 3) by exact (HPR 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : YK11.getr regs2 4 = YK11.getr regs' 4) by exact (HPR 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : YK11.getr regs2 8 = YK11.getr regs' 8) by exact (HPR 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : YK11.getr regs2 9 = YK11.getr regs' 9) by exact (HPR 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : YK11.getr regs2 18 = YK11.getr regs' 18) by exact (HPR 18 ltac:(unfold acallee_saved; lia)).
assert (P19 : YK11.getr regs2 19 = YK11.getr regs' 19) by exact (HPR 19 ltac:(unfold acallee_saved; lia)).
assert (P20 : YK11.getr regs2 20 = YK11.getr regs' 20) by exact (HPR 20 ltac:(unfold acallee_saved; lia)).
assert (P21 : YK11.getr regs2 21 = YK11.getr regs' 21) by exact (HPR 21 ltac:(unfold acallee_saved; lia)).
assert (P22 : YK11.getr regs2 22 = YK11.getr regs' 22) by exact (HPR 22 ltac:(unfold acallee_saved; lia)).
assert (P23 : YK11.getr regs2 23 = YK11.getr regs' 23) by exact (HPR 23 ltac:(unfold acallee_saved; lia)).
assert (P25 : YK11.getr regs2 25 = YK11.getr regs' 25) by exact (HPR 25 ltac:(unfold acallee_saved; lia)).
assert (P26 : YK11.getr regs2 26 = YK11.getr regs' 26) by exact (HPR 26 ltac:(unfold acallee_saved; lia)).
assert (P27 : YK11.getr regs2 27 = YK11.getr regs' 27) by exact (HPR 27 ltac:(unfold acallee_saved; lia)).
(* every byte off g_cmd[serial] and off the call's stack window is kept *)
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ inG TG.G_HARNESS_B a -> ~ (lc_sp1 cx - ESTACK <= a < lc_sp1 cx) ->
  aview segs (w_H W) mem2 a = aview segs (w_H W) mem' a).
{ intros a Ha HnG Hns. apply Hkeep; [exact Ha | | lia].
  intros Hd. apply HnG. apply ot_gcmd_inG. unfold TW.SZ_g_cmd. lia. }
assert (HKEEP : forall a, ot_keep cx a -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem' a).
{ intros a Ha. destruct (ot_keep_wr cx ly' S' W regs' mem' md' e LAWS HB HC a Ha) as (H64 & Hst & _ & _ & _ & HnG).
  exact (KR a H64 HnG Hst). }
assert (KSP : forall a, lc_sp1 cx <= a < lc_sp1 cx + 192 -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem' a).
{ intros a Ha. apply KR; [lia | | unfold ESTACK; lia].
  intros HGa. pose proof (transportb_segs_low a (trans_g_img a HGa)). unfold kLowMemEnd in *. lia. }
unfold ot_st_fe4. exists ly', S', regs2, mem2, md2, e, B1. cbv zeta.
split; [reflexivity|].
split.
{ split; [exact (ot_lcore_kept cx op (lo_k op) ly' S' W regs' mem' md' e regs2 mem2 md2 Gnl HL HJ2
          P2 P3 P4 P8 P9 P18 P19 P26 Hpres2 HKEEP)|].
  split; [exact Hopc|]. split; [exact Hob|]. split; [exact Hraw|]. split; [exact Hser|].
  apply (ot_rdword_kept _ _ _ _ H24); intros i Hi; apply KSP; lia. }
split.
{ rewrite ot_B2_eq.
  apply (tw_fill_set TMAP_B (aview segs (w_H W) mem') (aview segs (w_H W) mem2) B1 TW.OFF_g_cmd TB_g_cmd TW.SZ_g_cmd
    (40 * TW.g_ncmd B1) 0 40 TMAP_B_ok Htw TMAP_B_g_cmd ltac:(lia) ltac:(lia) ltac:(unfold TW.SZ_g_cmd; lia)).
  - intros i Hi. exact (Hset i Hi).
  - intros x Hx Hn. destruct (ot_tw_out cx ly' S' W regs' mem' md' e LAWS HB HC x Hx) as (H64 & Hst & _ & _ & _ & _).
    apply Hkeep; [exact H64 | lia | lia]. }
split.
{ apply (lc_garr8_kept (w_H W) (w_H W) mem' mem2 (lc_F cx + 32) _); [|exact Hcs]. intros j Hj.
  rewrite ot_cs_len in Hj by (rewrite repeat_length; reflexivity).
  apply KR; [lia | | unfold ESTACK; lia].
  intros HGa. exact (GFimg (lc_F cx + 32 + j) ltac:(lia) (trans_g_img _ HGa)). }
split; [destruct Hcur as (C25 & C22); split; [exact (eq_trans P25 C25) | exact (eq_trans P22 C22)]|].
split; [exact (eq_trans P20 R20)|].
split; [apply (ot_rdword_kept _ _ _ _ V64); intros i Hi; apply KSP; lia|].
split; [exact (eq_trans P21 R21)|]. split; [exact (eq_trans P23 R23) | exact (eq_trans P27 R27)].
Qed.

(* ------------------------------------------------------------------ *)
(* 6. Run B: +0xfe4 .. +0x103c, the len byte                          *)
(* ------------------------------------------------------------------ *)

(* +0x103c: a0 = len, a1 = the cursor's pointer after the len byte (tg_c4), a6 its bytes left, s4 = c (reloaded from
   144(s1) at +0xffc / +0x1038). *)
Definition ot_st_103c (cx : lcx) (op : lop) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' e B1,
    let kd := ot_kd cx op in
    let tv := ot_tvx cx op B1 in
    c' = lc_cfg cx 0x103c regs' mem' md' /\
    ot_com cx op B1 ly' S' W' regs' mem' md' e /\ lc_tw W' mem' (tg_B2 tv) /\
    garr8 segs (rd W' mem') (lc_F cx + 32)
      (TW.zs (TOP.cmd_struct (repeat (DSpec.b8 0) 24) 0 (sv_display kd) (sv_key kd))) /\
    rdword (aview segs (w_H W') mem') (lc_sp1 cx + 64) = Some (TW.g_ncmd B1) /\
    ot_rs regs' B1 /\
    YK11.getr regs' 10 = w64 (tg_len tv) /\ YK11.getr regs' 11 = w64 (l_p cx + TOP.fi_off (tg_c4 tv)) /\
    YK11.getr regs' 16 = w64 (TOP.fi_n (tg_c4 tv)) /\ YK11.getr regs' 20 = w64 (lc_F cx + 32).

(* A run that writes nothing keeps every fact of +0xfe4 but the registers it sets. *)
Lemma ot_103c_mk : forall cx op (W : world segs) ly' S' regs' mem' md' e B1 regs2 mem2 md2,
  l_n cx = Z.of_nat (length (l_pl cx)) ->
  ot_com cx op B1 ly' S' W regs' mem' md' e -> lc_tw W mem' (tg_B2 (ot_tvx cx op B1)) ->
  garr8 segs (rd W mem') (lc_F cx + 32)
    (TW.zs (TOP.cmd_struct (repeat (DSpec.b8 0) 24) 0 (sv_display (ot_kd cx op)) (sv_key (ot_kd cx op)))) ->
  rdword (aview segs (w_H W) mem') (lc_sp1 cx + 64) = Some (TW.g_ncmd B1) ->
  ot_rs regs' B1 ->
  ot_J cx ly' S' W mem2 md2 e ->
  (forall a, aview segs (w_H W) mem2 a = aview segs (w_H W) mem' a) ->
  (forall a, apresent (w_H W) mem' a -> apresent (w_H W) mem2 a) ->
  YK11.getr regs2 2 = YK11.getr regs' 2 -> YK11.getr regs2 3 = YK11.getr regs' 3 ->
  YK11.getr regs2 4 = YK11.getr regs' 4 -> YK11.getr regs2 8 = YK11.getr regs' 8 ->
  YK11.getr regs2 9 = YK11.getr regs' 9 -> YK11.getr regs2 18 = YK11.getr regs' 18 ->
  YK11.getr regs2 19 = YK11.getr regs' 19 -> YK11.getr regs2 21 = YK11.getr regs' 21 ->
  YK11.getr regs2 23 = YK11.getr regs' 23 -> YK11.getr regs2 26 = YK11.getr regs' 26 ->
  YK11.getr regs2 27 = YK11.getr regs' 27 ->
  YK11.getr regs2 10 = w64 (tg_len (ot_tvx cx op B1)) ->
  YK11.getr regs2 11 = w64 (l_p cx + TOP.fi_off (tg_c4 (ot_tvx cx op B1))) ->
  YK11.getr regs2 16 = w64 (TOP.fi_n (tg_c4 (ot_tvx cx op B1))) -> YK11.getr regs2 20 = w64 (lc_F cx + 32) ->
  ot_st_103c cx op W (lc_cfg cx 0x103c regs2 mem2 md2).
Proof.
intros cx op W ly' S' regs' mem' md' e B1 regs2 mem2 md2 Hnl HCOM Htw Hcs V64 (R21 & R23 & R27) HJ2 KM HPR
  P2 P3 P4 P8 P9 P18 P19 P21 P23 P26 P27 R10 R11 R16 R20.
destruct HCOM as (HL & Hopc & Hob & Hraw & Hser & H24).
unfold ot_st_103c. exists ly', S', regs2, mem2, md2, e, B1. cbv zeta.
split; [reflexivity|].
split.
{ split; [exact (ot_lcore_kept cx op (lo_k op) ly' S' W regs' mem' md' e regs2 mem2 md2 Hnl HL HJ2
          P2 P3 P4 P8 P9 P18 P19 P26 HPR (fun a _ => KM a))|].
  split; [exact Hopc|]. split; [exact Hob|]. split; [exact Hraw|]. split; [exact Hser|].
  apply (ot_rdword_kept _ _ _ _ H24); intros i _; exact (KM _). }
split; [apply (tw_kept TMAP_B (aview segs (w_H W) mem') _ _ Htw); intros x _; exact (KM x)|].
split; [apply (lc_garr8_kept (w_H W) (w_H W) mem' mem2 _ _); [intros j _; exact (KM _) | exact Hcs]|].
split; [apply (ot_rdword_kept _ _ _ _ V64); intros i _; exact (KM _)|].
split; [split; [exact (eq_trans P21 R21)|]; split; [exact (eq_trans P23 R23) | exact (eq_trans P27 R27)]|].
split; [exact R10|]. split; [exact R11|]. split; [exact R16 | exact R20].
Qed.

(* A register of the start state set to a value the machine holds. *)
Lemma ot_regs_ok_pin : forall E sr regs (r : bv 5) e,
  regs_ok E sr regs -> bv_eqb r 0 = false -> sv_denot E e = YK11.getr regs r -> regs_ok E (sr_set sr r e) regs.
Proof.
  intros E sr regs r e H Hr0 He rr. destruct (decide (rr = r)) as [->|Hne].
  - rewrite sr_get_set_same by exact Hr0. symmetry. exact He.
  - rewrite sr_get_set_other by exact Hne. apply H.
Qed.

(* The 8 bytes at 0x103a8 the code multiplies by (`mulhu`, the division by 22): ceil (2 ^ 64 / 22), read through
   the image view of TRANS_RO_RD (K1). *)
Definition OT_KVAL : Z := 838488366986797801.
Lemma ot_kval : forall (W : world segs) mem, trans_rom_view_rd W mem ->
  val_mem segs (rd W mem) TRANS_K_LLVMF2 8 OT_KVAL.
Proof.
intros W mem HV k Hk.
assert (Hin : trans_in_ro_rd (TRANS_K_LLVMF2 + Z.of_nat k)).
{ unfold trans_in_ro_rd, TRANS_RO_RD. cbn [app]. apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd.
  unfold in_zr. cbn [fst snd]. lia. }
pose proof (HV _ Hin) as E1.
assert (E2 : option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom tfibsegs (Z_to_bv 64 (TRANS_K_LLVMF2 + Z.of_nat k)))
  = Some (YO0f.le_byte OT_KVAL 8 k)) by (do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); lia).
rewrite E2 in E1. unfold aview in E1.
destruct (YP09.mbyte segs (rd W mem) (TRANS_K_LLVMF2 + Z.of_nat k)) as [b|] eqn:Eb; [|discriminate E1].
cbn [option_map] in E1. injection E1 as E1. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, <- E1.
symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* a0 after +0x1024: byte mod 22 + 3, decided over the 256 bytes. *)
Definition ot_lenx : sv :=
  SAlu ALU_ADD (SAlu ALU_SUB (SOff 34 0) (SMd M_MUL (SMd M_MULHU (SOff 34 0) (SLit OT_KVAL)) (SLit 22))) (SLit 3).
Definition ot_lenw (w : word) : word := sv_denot (mkEnv (fun _ => w) (fun _ => [])) ot_lenx.
Lemma ot_lenw_ok :
  forallb (fun k => bv_eqb (ot_lenw (w64 (Z.of_nat k))) (w64 (Z.of_nat k mod 22 + 3))) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ot_len_den : forall E b, ew E 34 = w64 b -> 0 <= b < 256 -> sv_denot E ot_lenx = w64 (b mod 22 + 3).
Proof.
intros E b H Hb.
assert (Hl : sv_denot E ot_lenx = ot_lenw (w64 b)) by (unfold ot_lenw, ot_lenx; cbn [sv_denot ew]; rewrite H; reflexivity).
rewrite Hl. pose proof ot_lenw_ok as K. rewrite forallb_forall in K.
specialize (K (Z.to_nat b) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in K by lia.
unfold bv_eqb in K. apply Z.eqb_eq in K. apply bv_eq. exact K.
Qed.

(* The input byte at index j, as the model reads it. *)
Lemma ot_nth_map : forall (l : list byte) (j : nat), (j < length l)%nat ->
  nth j (map (fun b : byte => bv_unsigned b) l) 0 = DSpec.at8 l j.
Proof.
intros l j Hj. unfold DSpec.at8, DSpec.bz.
rewrite (nth_indep _ 0 (bv_unsigned (DSpec.b8 0))) by (rewrite length_map; exact Hj).
apply (map_nth (fun b : byte => bv_unsigned b)).
Qed.

(* The low atoms of a valuation after a run are those of E0. *)
Ltac ot_low HS E0 HEX :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex _ _ =>
      assert (HEX : forall n, (n < 1024)%nat -> ew Ex n = ew E0 n)
        by (let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn;
            repeat rewrite ew_ewset_other by lia; repeat rewrite ew_havoc_old by lia; reflexivity)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?Ex _ _ =>
      assert (HEX : forall n, (n < 1024)%nat -> ew Ex n = ew E0 n)
        by (let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn;
            repeat rewrite ew_ewset_other by lia; repeat rewrite ew_havoc_old by lia; reflexivity)
  end.

(* Run B regions: 144(s1) = c (atom 33), and when bytes are left the len byte at s9 (atom 34) and the constant at
   0x103a8 (object 20). The UBSan cursor test at +0xfec (`bgeu s4, a1`, s4 = 1, a1 = s9 + 1) is decided by the facts
   on atoms 20 and 25; the shadow test at +0x1000 and its slow path +0x1790 .. +0x1798 by the token engine over the
   shadow entry of the byte at s9 (the report call 0x82f88 is not reached). *)
Definition ot_spB : YP09.region := YP09.mkRegion (Some 9%nat) 144 152 0 0 [YP09.mkChunk 144 (CVal 8 (SOff 33 0))].
Definition ot_inB : YP09.region := YP09.mkRegion (Some 25%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))].
Definition ot_kB : YP09.region := YP09.mkRegion (Some (A_OBJ 20)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit OT_KVAL))].
Definition ot_factsB : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (20%nat, mkAF 1 1 0);
  (22%nat, mkAF 1 (2 ^ 26) 0); (25%nat, mkAF 4096 (2 ^ 47 - 8) 0); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
  (33%nat, mkAF 4096 (2 ^ 47 - 64) 5); (34%nat, mkAF 0 255 0)] [] [].
Definition ot_ssB : sstate := mkSS 0xfe4 sr_atoms [ot_inB; ot_kB; ot_spB] None ot_factsB.
Definition ot_factsB0 : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (33%nat, mkAF 4096 (2 ^ 47 - 64) 5)] [] [].
Definition ot_ssB0 : sstate := mkSS 0xfe4 (sr_set sr_atoms (Z_to_bv 5 22) (SLit 0)) [ot_spB] None ot_factsB0.

Lemma ot_runB : forall cx op (W : world segs) c,
  lc_rom_view_stmt B MT XL RLO RHI ->
  lp_prem B MT XL RLO RHI -> lc_base B MT XL RLO RHI cx -> ot_st_fe4 cx op W c -> SRr segs W c (ot_st_103c cx op).
Proof.
intros cx op W c K1 HP HB H. destruct H as (ly' & S' & regs' & mem' & md' & e & B1 & H). cbv zeta in H.
destruct H as (-> & HCOM & Htw & Hcs & Hcur & R20 & V64 & HRS).
pose proof (lp_laws B MT XL RLO RHI HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned B MT XL RLO RHI HP)) as HGX.
pose proof HCOM as (HL & Hopc & Hob & Hraw & Hser & H24).
pose proof HL as (HC & (F18 & F26) & HSP & HFSH & HOK & He & HM & R19).
pose proof HOK as (_ & _ & Hcok & _ & _).
pose proof (ot_c3_ok (l_pl cx) (lo_c op) Hcok) as Hc3.
pose proof (ot_geo cx ly' S' W regs' mem' md' e LAWS HB HC) as (Gs1 & Gs01 & Gs1al & Gs047 & GF4 & GFal & GFc & GFapp &
  GFimg & Gn & Gnl & Gp0 & Gp).
pose proof HC as (HJ & _ & _ & _ & Rsp & R8 & R9 & Rgp & Rtp & _ & _ & _ & _ & _ & _ & _ & _ & HIN).
pose proof alloc_ceiling_val as Hac.
pose proof (ot_tv (l_pl cx) B1 (sv_c (ot_kd cx op))) as TV. cbv zeta in TV.
destruct TV as (_ & _ & Elen & Ec4 & _).
change (lc_tag_vals (l_pl cx) B1 (sv_c (ot_kd cx op))) with (ot_tvx cx op B1) in Elen, Ec4.
change (lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op))) with (ot_kd cx op) in Hc3, Hcur.
destruct Hcur as (C25 & C22).
set (c3 := sv_c (ot_kd cx op)) in *.
pose proof Hc3 as (Hc3o & Hc3n & Hc3s).
assert (HF32 : rdword (aview segs (w_H W) mem') (lc_sp1 cx + 144) = Some (lc_F cx + 32)).
{ unfold lc_spills in HSP. rewrite Forall_forall in HSP. refine (HSP (144, lc_F cx + 32) _).
  unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm. cbn [app].
  repeat (first [left; reflexivity | right]). }
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
unfold lc_cfg.
change (w64 (transportb_text + 0xfe4)) with (Z_to_bv 64 (BASE + 0xfe4)).
destruct (Z.eq_dec (TOP.fi_n c3) 0) as [Hn0 | Hn0].
- (* no byte left: `beqz s6` to +0x102c, a0 = 3, a6 = 0, a1 = s9 *)
  assert (EU : TOP.fuzz_u8_m (l_pl cx) c3 = (c3, 0)) by (unfold TOP.fuzz_u8_m; rewrite Hn0; reflexivity).
  rewrite EU in Elen, Ec4. cbn [fst snd] in Elen, Ec4.
  set (E := ot_E regs' [w64 SHADOW_OFF; w64 (lc_F cx + 32)]).
  assert (HEI : img_env VAL A_LIM E) by (unfold E, ot_E; apply Eimg_env).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs' r)
    by (intros n r Hn; unfold E, ot_E; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (E33 : ew E 33 = w64 (lc_F cx + 32))
    by (unfold E, ot_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs' _ 1)).
  pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite R9 in E9.
  assert (U9 : bv_unsigned (ew E 9) = lc_sp1 cx) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (HS : @st_ok_pi segs VAL (l_fx cx) E ot_ssB0
    (restrict (w_H W) (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (BASE + 0xfe4)) mem' (YK11.seg_rom segs)))).
  { rewrite restrict_mkst_fx. apply (@pa_entry_st_ok_full (l_fx cx) rc transportb_listing PI_transportb).
    - apply ot_regs_ok_pin; [unfold E, ot_E; apply regs_ok_Eimg_Ereg | reflexivity |].
      cbn [sv_denot]. rewrite C22, Hn0. reflexivity.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil].
      unfold ot_spB, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ (lc_sp1 cx) 144 8 (SOff 33 0) (lc_F cx + 32));
        [apply ot_den_atom; [exact E33 | lia] | lia | lia |].
      apply (val_mem_of_rdword segs). exact HF32.
    - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
    - unfold ot_factsB0, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U9, E33. unfold w64. rewrite unsigned_lit_small by lia.
      change (2 ^ 5) with 32.
      repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
  assert (SHOK : sh_ok segs (SOff 26 0) [] E (rd W mem')) by constructor.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x103c.
  { apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. cbn [ot_spB YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
  pmkst HS. ot_norm HS. apply SRr_ret.
  assert (KM : forall a, aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem' a).
  { intros a. apply (aview_eq_of segs). apply HFr. intros (r & Hin & Hr). cbn [ot_ssB0 ss_mem In] in Hin.
    destruct Hin as [<- | []]. cbn [ot_spB YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia. }
  assert (Q2 : YK11.getr (ms_regs ms) 2 = YK11.getr regs' 2) by ot_same HS EE.
  assert (Q3 : YK11.getr (ms_regs ms) 3 = YK11.getr regs' 3) by ot_same HS EE.
  assert (Q4 : YK11.getr (ms_regs ms) 4 = YK11.getr regs' 4) by ot_same HS EE.
  assert (Q8 : YK11.getr (ms_regs ms) 8 = YK11.getr regs' 8) by ot_same HS EE.
  assert (Q9 : YK11.getr (ms_regs ms) 9 = YK11.getr regs' 9) by ot_same HS EE.
  assert (Q18 : YK11.getr (ms_regs ms) 18 = YK11.getr regs' 18) by ot_same HS EE.
  assert (Q19 : YK11.getr (ms_regs ms) 19 = YK11.getr regs' 19) by ot_same HS EE.
  assert (Q21 : YK11.getr (ms_regs ms) 21 = YK11.getr regs' 21) by ot_same HS EE.
  assert (Q23 : YK11.getr (ms_regs ms) 23 = YK11.getr regs' 23) by ot_same HS EE.
  assert (Q26 : YK11.getr (ms_regs ms) 26 = YK11.getr regs' 26) by ot_same HS EE.
  assert (Q27 : YK11.getr (ms_regs ms) 27 = YK11.getr regs' 27) by ot_same HS EE.
  ot_rv HS (Z_to_bv 5 10) Q10. ot_rv HS (Z_to_bv 5 11) Q11. ot_rv HS (Z_to_bv 5 16) Q16. ot_rv HS (Z_to_bv 5 20) Q20.
  refine (ot_103c_mk cx op W ly' S' regs' mem' md' e B1 (ms_regs ms) (ms_mem ms) _ Gnl HCOM Htw Hcs V64 HRS
    HJ KM (fun a => apresent_grows _ _ _ a HG) Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q21 Q23 Q26 Q27 _ _ _ _).
  + rewrite Elen. exact (eq_trans Q10 eq_refl).
  + rewrite Ec4. refine (eq_trans Q11 _). apply ot_den_same. rewrite (EE 25%nat 25%bv eq_refl). exact C25.
  + rewrite Ec4, Hn0. exact (eq_trans Q16 eq_refl).
  + exact (eq_trans Q20 (ot_den_atom E 33 _ E33 ltac:(lia))).
- (* one byte or more: the cursor test, the checked load at s9 and byte mod 22 + 3 *)
  assert (Hoff : 0 <= TOP.fi_off c3 < l_n cx) by lia.
  set (j := Z.to_nat (TOP.fi_off c3)).
  set (bt := DSpec.at8 (l_pl cx) j).
  assert (EU : TOP.fuzz_u8_m (l_pl cx) c3 = (TOP.FuzzIn (TOP.fi_off c3 + 1) (TOP.fi_n c3 - 1), bt))
    by (unfold TOP.fuzz_u8_m; rewrite (proj2 (Z.eqb_neq _ _) Hn0); reflexivity).
  rewrite EU in Elen, Ec4. cbn [fst snd] in Elen, Ec4.
  assert (Hbt : 0 <= bt < 256) by (unfold bt, DSpec.at8, DSpec.bz; apply bv_unsigned_in_range).
  destruct (Gp ltac:(lia)) as (Gpin & Gp4 & Gpc & Gpapp & GdpF & Gpimg).
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  set (E := ot_E regs' [w64 SHADOW_OFF; w64 (lc_F cx + 32); w64 bt]).
  assert (HEI : img_env VAL A_LIM E) by (unfold E, ot_E; apply Eimg_env).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs' r)
    by (intros n r Hn; unfold E, ot_E; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (E33 : ew E 33 = w64 (lc_F cx + 32))
    by (unfold E, ot_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs' _ 1)).
  assert (E34 : ew E 34 = w64 bt)
    by (unfold E, ot_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs' _ 2)).
  assert (EK : ew E (A_OBJ 20) = Z_to_bv 64 TRANS_K_LLVMF2)
    by (unfold E, ot_E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); reflexivity).
  pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite R9 in E9.
  pose proof (eq_trans (EE 20%nat 20%bv eq_refl) R20) as E20.
  pose proof (eq_trans (EE 22%nat 22%bv eq_refl) C22) as E22.
  pose proof (eq_trans (EE 25%nat 25%bv eq_refl) C25) as E25.
  pose proof (eq_trans (EE 26%nat 26%bv eq_refl) F26) as E26.
  assert (U9 : bv_unsigned (ew E 9) = lc_sp1 cx) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (U20 : bv_unsigned (ew E 20) = 1) by (rewrite E20; reflexivity).
  assert (U22 : bv_unsigned (ew E 22) = TOP.fi_n c3) by (rewrite E22; apply unsigned_lit_small; lia).
  assert (U25 : bv_unsigned (ew E 25) = l_p cx + TOP.fi_off c3) by (rewrite E25; apply unsigned_lit_small; lia).
  assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF) by (rewrite E26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (UK : bv_unsigned (ew E (A_OBJ 20)) = TRANS_K_LLVMF2) by (rewrite EK; reflexivity).
  assert (HKNI : forall a, l_p cx <= a < l_p cx + l_n cx -> ~ (TRANS_K_LLVMF2 <= a < TRANS_K_LLVMF2 + 8)).
  { intros a Ha Hk. apply (Gpimg a Ha). apply trans_ro_img. unfold trans_in_ro_rd, TRANS_RO_RD. cbn [app].
    apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. }
  assert (HS : @st_ok_pi segs VAL (l_fx cx) E ot_ssB
    (restrict (w_H W) (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (BASE + 0xfe4)) mem' (YK11.seg_rom segs)))).
  { rewrite restrict_mkst_fx. apply (@pa_entry_st_ok_full (l_fx cx) rc transportb_listing PI_transportb).
    - unfold E, ot_E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      + unfold ot_inB, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U25. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val segs E _ (l_p cx + TOP.fi_off c3) 0 1 (SOff 34 0) bt);
          [apply ot_den_atom; [exact E34 | lia] | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia |].
        destruct HIN as (HPAYg & _).
        assert (Hj : (j < length (map (fun b : byte => bv_unsigned b) (l_pl cx)))%nat)
          by (rewrite length_map; unfold j; lia).
        pose proof (proj1 (HPAYg j Hj)) as V.
        rewrite ot_nth_map in V by (rewrite length_map in Hj; exact Hj).
        unfold j in V. rewrite Z2Nat.id in V by lia. rewrite Z.add_0_r. exact V.
      + unfold ot_kB, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite UK. unfold TRANS_K_LLVMF2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val segs E _ TRANS_K_LLVMF2 0 8 (SLit OT_KVAL) OT_KVAL);
          [reflexivity | unfold OT_KVAL; lia | lia |].
        rewrite Z.add_0_r.
        exact (ot_kval W mem' (K1 HP cx ly' S' W regs' mem' md' e HB HC)).
      + unfold ot_spB, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val segs E _ (lc_sp1 cx) 144 8 (SOff 33 0) (lc_F cx + 32));
          [apply ot_den_atom; [exact E33 | lia] | lia | lia |].
        apply (val_mem_of_rdword segs). exact HF32.
    - apply pairwise_disjoint_of_extents.
      unfold ot_inB, ot_kB, ot_spB, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite U25, UK, U9. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      pose proof (HKNI (l_p cx + TOP.fi_off c3) ltac:(lia)). unfold TRANS_K_LLVMF2 in *.
      repeat split; first [exact I | lia].
    - unfold ot_factsB, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U9, U20, U22, U25, U26, E33, E34. unfold w64. rewrite !unsigned_lit_small by lia.
      change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF.
      repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
  assert (SHOK : sh_ok segs (SOff 26 0) [mkSHE 25 0 1] E (rd W mem')).
  { apply Forall_cons; [|apply Forall_nil]. split.
    - cbn [she_m she_lo she_hi]. unfold U. cbn [sv_denot]. rewrite U26, U25, !Z.add_0_r, !Z_to_bv_unsigned.
      rewrite !bv_wrap_small by (unfold bv_modulus, SHADOW_OFF; cbn [Z.of_N]; lia).
      exact (range_addressable_of_block segs B LAWS ly' S' W mem' md' (l_p cx) (l_n cx) (l_p cx + TOP.fi_off c3) 1 HAR
        Gpin ltac:(lia) ltac:(unfold req_size; destruct (Z.eqb_spec (l_n cx) 0); lia)).
    - intros a Ha. cbn [she_m she_lo she_hi Z.min Z.max] in Ha. unfold U in *. cbn [sv_denot] in *.
      rewrite U26, U25, !Z.add_0_r, !Z_to_bv_unsigned in *.
      rewrite !bv_wrap_small in * by (unfold bv_modulus, SHADOW_OFF; cbn [Z.of_N]; lia).
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x103c.
  { apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]]];
      intros a Ha; cbn [ot_inB ot_kB ot_spB YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia. }
  pmkst HS. ot_norm HS. apply SRr_ret.
  ot_low HS E HEX.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (EE' : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Ex n = YK11.getr regs' r)
      by (intros n r Hn; pose proof (bv_unsigned_in_range 5 r) as Hr; change (bv_modulus 5) with 32 in Hr;
          rewrite HEX by lia; exact (EE n r Hn));
    assert (E33' : ew Ex 33 = w64 (lc_F cx + 32)) by (rewrite HEX by lia; exact E33);
    assert (E34' : ew Ex 34 = w64 bt) by (rewrite HEX by lia; exact E34);
    assert (E22' : ew Ex 22 = w64 (TOP.fi_n c3)) by (rewrite HEX by lia; exact E22);
    assert (E25' : ew Ex 25 = w64 (l_p cx + TOP.fi_off c3)) by (rewrite HEX by lia; exact E25)
  end.
  assert (KM : forall a, aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem' a).
  { intros a. apply (aview_eq_of segs). apply HFr. intros (r & Hin & Hr). cbn [ot_ssB ss_mem In] in Hin.
    destruct Hin as [<- | [<- | [<- | []]]]; cbn [ot_inB ot_kB ot_spB YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      lia. }
  assert (Q2 : YK11.getr (ms_regs ms) 2 = YK11.getr regs' 2) by ot_same HS EE'.
  assert (Q3 : YK11.getr (ms_regs ms) 3 = YK11.getr regs' 3) by ot_same HS EE'.
  assert (Q4 : YK11.getr (ms_regs ms) 4 = YK11.getr regs' 4) by ot_same HS EE'.
  assert (Q8 : YK11.getr (ms_regs ms) 8 = YK11.getr regs' 8) by ot_same HS EE'.
  assert (Q9 : YK11.getr (ms_regs ms) 9 = YK11.getr regs' 9) by ot_same HS EE'.
  assert (Q18 : YK11.getr (ms_regs ms) 18 = YK11.getr regs' 18) by ot_same HS EE'.
  assert (Q19 : YK11.getr (ms_regs ms) 19 = YK11.getr regs' 19) by ot_same HS EE'.
  assert (Q21 : YK11.getr (ms_regs ms) 21 = YK11.getr regs' 21) by ot_same HS EE'.
  assert (Q23 : YK11.getr (ms_regs ms) 23 = YK11.getr regs' 23) by ot_same HS EE'.
  assert (Q26 : YK11.getr (ms_regs ms) 26 = YK11.getr regs' 26) by ot_same HS EE'.
  assert (Q27 : YK11.getr (ms_regs ms) 27 = YK11.getr regs' 27) by ot_same HS EE'.
  ot_rv HS (Z_to_bv 5 10) Q10. ot_rv HS (Z_to_bv 5 11) Q11. ot_rv HS (Z_to_bv 5 16) Q16. ot_rv HS (Z_to_bv 5 20) Q20.
  refine (ot_103c_mk cx op W ly' S' regs' mem' md' e B1 (ms_regs ms) (ms_mem ms) _ Gnl HCOM Htw Hcs V64 HRS
    HJ KM (fun a => apresent_grows _ _ _ a HG) Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q21 Q23 Q26 Q27 _ _ _ _).
  + rewrite Elen. exact (eq_trans Q10 (ot_len_den _ bt E34' Hbt)).
  + rewrite Ec4. cbn [TOP.fi_off]. refine (eq_trans Q11 _).
    rewrite (ot_den_off _ 25 _ 1 E25' ltac:(lia)). unfold w64. f_equal. lia.
  + rewrite Ec4. cbn [TOP.fi_n]. refine (eq_trans Q16 _).
    rewrite (ot_den_off _ 22 _ (-1) E22' ltac:(lia)). unfold w64. f_equal.
  + exact (eq_trans Q20 (ot_den_atom _ 33 _ E33' ltac:(lia))).
Qed.

(* ------------------------------------------------------------------ *)
(* 7. Run C: +0x103c .. +0x109c, c's header and len, the take          *)
(* ------------------------------------------------------------------ *)

(* 48(s1) = c + 3 (as s4 + 3), 64(s1) = serial (atom 33); 8(s1) .. 23(s1), c[0 .. 2] and c[24] writable. *)
Definition ot_spC : YP09.region :=
  YP09.mkRegion (Some 9%nat) 8 72 8 24
    [YP09.mkChunk 48 (CVal 8 (SOff 20 3)); YP09.mkChunk 64 (CVal 8 (SOff 33 0))].
Definition ot_c1 : YP09.region := YP09.mkRegion (Some 20%nat) 0 3 0 3 [].
Definition ot_c2 : YP09.region := YP09.mkRegion (Some 20%nat) 24 25 24 25 [].
Definition ot_factsC : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (10%nat, mkAF 3 24 0);
  (11%nat, mkAF 4096 (2 ^ 47) 0); (16%nat, mkAF 0 (2 ^ 26) 0); (20%nat, mkAF 4096 (2 ^ 47 - 64) 5);
  (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 1023 0)] [] [].
Definition ot_ssC : sstate := mkSS 0x103c sr_atoms [ot_spC; ot_c1; ot_c2] None ot_factsC.
(* c's 32 bytes, a shadow entry (their shadow is 0 while c is in scope): the windows in c are off the shadow span. *)
Definition OT_SHC : list shent := [mkSHE 20 0 32].

(* The memcpy's entry (+0x109c): c[0 .. 2] the tag and serial bytes, c[24] = len, 16(s1) the bytes left after the
   len byte, 8(s1) = n, s8 the cursor after the take, s6 = 3, s9 = 0xf0; a0 = c + 3, a1 = the input pointer, a2 = n. *)
Definition ot_hdr (s : Z) : list byte :=
  [DSpec.b8 TC.TAG; DSpec.b8 (Z.land s 0x7f); DSpec.b8 (Z.land (Z.shiftr s 7) 0x7f)].
Definition ot_at_mc (cx : lcx) (op : lop) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' e B1,
    let kd := ot_kd cx op in
    let tv := ot_tvx cx op B1 in
    c' = mkCfg (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (transportb_sigma TB___asan_memcpy)) mem'
      (YK11.seg_rom segs)) md' /\
    ot_com cx op B1 ly' S' W' regs' mem' md' e /\ lc_tw W' mem' (tg_B2 tv) /\
    garr8 segs (rd W' mem') (lc_F cx + 32)
      (TW.zs (TOP.cmd_struct (ot_hdr (TW.g_ncmd B1) ++ repeat (DSpec.b8 0) 21) (tg_len tv) (sv_display kd) (sv_key kd))) /\
    rdword (aview segs (w_H W') mem') (lc_sp1 cx + 64) = Some (TW.g_ncmd B1) /\
    rdword (aview segs (w_H W') mem') (lc_sp1 cx + 16) = Some (TOP.fi_n (tg_c4 tv)) /\
    rdword (aview segs (w_H W') mem') (lc_sp1 cx + 8) = Some (tg_n tv) /\
    ot_rs regs' B1 /\ YK11.getr regs' 20 = w64 (lc_F cx + 32) /\
    YK11.getr regs' 22 = w64 3 /\ YK11.getr regs' 25 = w64 0xf0 /\
    YK11.getr regs' 24 = w64 (l_p cx + TOP.fi_off (tg_c tv)) /\
    YK11.getr regs' 10 = w64 (lc_F cx + 35) /\ YK11.getr regs' 11 = w64 (l_p cx + TOP.fi_off (tg_c4 tv)) /\
    YK11.getr regs' 12 = w64 (tg_n tv) /\ YK11.getr regs' 1 = w64 (transportb_text + 0x10a0).

Lemma ot_le1 : forall v, 0 <= v < 256 -> YO0f.le_byte v 1 0 = v.
Proof.
intros v Hv. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small v 256 Hv). exact (Z.mod_small v 256 Hv).
Qed.
Lemma ot_b8 : forall x, 0 <= x < 256 -> bv_unsigned (DSpec.b8 x) = x.
Proof. intros x Hx. unfold DSpec.b8. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

(* A byte of the view, as val_mem reads it. *)
Lemma ot_val1 : forall (H : word -> bool) (m : word -> option byte) a v,
  aview segs H m a = Some v -> 0 <= v < 256 -> val_mem segs (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv Hr k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold aview in Hv. destruct (YP09.mbyte segs (mrestrict H m) a) as [b|] eqn:Eb; [|discriminate Hv].
cbn [option_map] in Hv. injection Hv as Hv. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
rewrite ot_le1 by exact Hr. rewrite <- Hv. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* A byte array whose bytes are kept but where P marks, and are given there. *)
Lemma ot_garr8_patch : forall (H : word -> bool) (m m2 : word -> option byte) base (l l2 : list Z) (P : nat -> Prop),
  length l2 = length l -> garr8 segs (mrestrict H m) base l ->
  (forall j, (j < length l)%nat -> P j \/
     (nth j l2 0 = nth j l 0 /\ aview segs H m2 (base + Z.of_nat j) = aview segs H m (base + Z.of_nat j))) ->
  (forall j, (j < length l)%nat -> P j ->
     aview segs H m2 (base + Z.of_nat j) = Some (nth j l2 0) /\ 0 <= nth j l2 0 < 256) ->
  garr8 segs (mrestrict H m2) base l2.
Proof.
intros H m m2 base l l2 P Hlen HG HK HP j Hj. rewrite Hlen in Hj.
destruct (HK j Hj) as [Pj | (Hn & Ha)].
- destruct (HP j Hj Pj) as (Hv & Hr). split; [exact (ot_val1 H m2 _ _ Hv Hr) | exact Hr].
- destruct (HG j Hj) as (Hv & Hr). rewrite Hn. split; [|exact Hr].
  intros k Hk. assert (k = 0%nat) by lia. subst k. pose proof (Hv 0%nat Hk) as V. cbn [Z.of_nat] in V |- *.
  rewrite Z.add_0_r in V |- *. rewrite <- V. apply (mbyte_of_aview segs). exact Ha.
Qed.

(* c's shadow while it is in scope: its four bytes 4 .. 7 of the frame's shadow are 0. *)
Lemma ot_c_shadow : forall cx (r : reader) x, lc_fsh cx r true false -> lc_F cx mod 64 = 0 -> 0 <= lc_F cx ->
  lc_F cx + 32 <= x < lc_F cx + 64 -> r (SHADOW_OFF + x / 8) = Some 0.
Proof.
intros cx r x Hsh HF64 HF0 Hx. unfold lc_fsh in Hsh.
set (k := lc_F cx / 64).
assert (EF : lc_F cx = 64 * k) by (unfold k; pose proof (Z.div_mod (lc_F cx) 64 ltac:(lia)); lia).
assert (Hx8 : 8 * k + 4 <= x / 8 < 8 * k + 8) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (EF8 : lc_F cx / 8 = 8 * k) by (rewrite EF; replace (64 * k) with ((8 * k) * 8) by ring; apply Z.div_mul; lia).
assert (E : SHADOW_OFF + x / 8 = lc_SH cx + (x / 8 - 8 * k)) by (unfold lc_SH; lia).
rewrite E, Hsh by lia.
assert (Hi : x / 8 - 8 * k = 4 \/ x / 8 - 8 * k = 5 \/ x / 8 - 8 * k = 6 \/ x / 8 - 8 * k = 7) by lia.
destruct Hi as [-> | [-> | [-> | ->]]]; reflexivity.
Qed.
Lemma ot_c_ra : forall cx (r : reader) q n, lc_fsh cx r true false -> lc_F cx mod 64 = 0 -> 0 <= lc_F cx ->
  lc_F cx + 32 <= q -> q + n <= lc_F cx + 64 -> range_addressable r SHADOW_OFF q n.
Proof.
intros cx r q n Hsh HF64 HF0 H1 H2 x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr. apply (ot_c_shadow cx r x Hsh HF64 HF0). lia.
Qed.
Lemma ot_c_hull : forall cx (r : reader) q n, lc_fsh cx r true false -> lc_F cx mod 64 = 0 -> 0 <= lc_F cx ->
  lc_F cx + 32 <= q -> q + n <= lc_F cx + 64 -> 0 < n -> shadow_hull_vis r q n.
Proof.
intros cx r q n Hsh HF64 HF0 H1 H2 Hn s Hs. unfold lc_fsh in Hsh. unfold shadow_addr in Hs.
set (k := lc_F cx / 64) in *.
assert (EF : lc_F cx = 64 * k) by (unfold k; pose proof (Z.div_mod (lc_F cx) 64 ltac:(lia)); lia).
assert (EF8 : lc_F cx / 8 = 8 * k) by (rewrite EF; replace (64 * k) with ((8 * k) * 8) by ring; apply Z.div_mul; lia).
set (y1 := q / 8) in *. set (y2 := (q + n - 1) / 8) in *.
assert (B1 : 8 * k + 4 <= y1 < 8 * k + 8) by (unfold y1; split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (B2 : 8 * k + 4 <= y2 < 8 * k + 8) by (unfold y2; split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (D1 : (SHADOW_OFF + y1) / 8 = 268431360 + k)
  by (unfold SHADOW_OFF; symmetry; apply Z.div_unique with (r := y1 - 8 * k); lia).
assert (D2 : (SHADOW_OFF + y2) / 8 = 268431360 + k)
  by (unfold SHADOW_OFF; symmetry; apply Z.div_unique with (r := y2 - 8 * k); lia).
rewrite D1, D2 in Hs.
assert (E : s = lc_SH cx + (s - lc_SH cx)) by lia. rewrite E, Hsh; [discriminate|].
unfold lc_SH, SHADOW_OFF in *. lia.
Qed.

(* c[1], c[2] (the serial's bytes, serial < 1024) and a2 = len - 3, decided over their values. *)
Definition ot_envw (w : word) : env := mkEnv (fun _ => w) (fun _ => []).
Definition ot_c1x : sv := SAlu ALU_AND (SOff 33 0) (SLit 127).
Definition ot_c2x : sv := SAlu ALU_SRL (SOff 33 0) (SLit 7).
Definition ot_s9x : sv := SAlu ALU_AND (SOff 10 4294967293) (SLit 4294967295).
Lemma ot_hdr_ok : forallb (fun k =>
    bv_eqb (sv_denot (ot_envw (w64 (Z.of_nat k))) ot_c1x) (w64 (Z.land (Z.of_nat k) 127)) &&
    bv_eqb (sv_denot (ot_envw (w64 (Z.of_nat k))) ot_c2x) (w64 (Z.land (Z.shiftr (Z.of_nat k) 7) 127)))
  (seq 0 1024) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ot_s9_ok : forallb (fun k => bv_eqb (sv_denot (ot_envw (w64 (Z.of_nat k))) ot_s9x) (w64 (Z.of_nat k - 3)))
  (seq 3 22) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ot_c1_den : forall E s, ew E 33 = w64 s -> 0 <= s < 1024 -> sv_denot E ot_c1x = w64 (Z.land s 127).
Proof.
intros E s H Hs.
assert (Hl : sv_denot E ot_c1x = sv_denot (ot_envw (w64 s)) ot_c1x)
  by (unfold ot_envw, ot_c1x; cbn [sv_denot ew]; rewrite H; reflexivity).
rewrite Hl. pose proof ot_hdr_ok as K. rewrite forallb_forall in K.
specialize (K (Z.to_nat s) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in K by lia.
apply andb_prop in K as [K _]. unfold bv_eqb in K. apply Z.eqb_eq in K. apply bv_eq. exact K.
Qed.
Lemma ot_c2_den : forall E s, ew E 33 = w64 s -> 0 <= s < 1024 ->
  sv_denot E ot_c2x = w64 (Z.land (Z.shiftr s 7) 127).
Proof.
intros E s H Hs.
assert (Hl : sv_denot E ot_c2x = sv_denot (ot_envw (w64 s)) ot_c2x)
  by (unfold ot_envw, ot_c2x; cbn [sv_denot ew]; rewrite H; reflexivity).
rewrite Hl. pose proof ot_hdr_ok as K. rewrite forallb_forall in K.
specialize (K (Z.to_nat s) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in K by lia.
apply andb_prop in K as [_ K]. unfold bv_eqb in K. apply Z.eqb_eq in K. apply bv_eq. exact K.
Qed.
Lemma ot_s9_den : forall E len, ew E 10 = w64 len -> 3 <= len <= 24 -> sv_denot E ot_s9x = w64 (len - 3).
Proof.
intros E len H Hl.
assert (Hd : sv_denot E ot_s9x = sv_denot (ot_envw (w64 len)) ot_s9x)
  by (unfold ot_envw, ot_s9x; cbn [sv_denot ew]; rewrite H; reflexivity).
rewrite Hd. pose proof ot_s9_ok as K. rewrite forallb_forall in K.
specialize (K (Z.to_nat len) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in K by lia.
unfold bv_eqb in K. apply Z.eqb_eq in K. apply bv_eq. exact K.
Qed.
Lemma ot_s9_U : forall E len, ew E 10 = w64 len -> 3 <= len <= 24 -> U E ot_s9x = len - 3.
Proof. intros E len H Hl. unfold U. rewrite (ot_s9_den E len H Hl). unfold w64. apply unsigned_lit_small. lia. Qed.

(* The UBSan take test at +0x108c (`bltu s8, a1`, s8 = a1 + n): no wrap, so not taken. *)
Lemma ot_ltu_add_l : forall E x y vx vy, U E x = vx -> U E y = vy -> vx + vy < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_ADD x y)) (sv_denot E y) = false.
Proof.
intros E x y vx vy Hx Hy Hs. rewrite branch_ltu_U, U_SAlu. cbn [zalu_raw]. rewrite Hx, Hy.
pose proof (U_range E x) as Rx. rewrite Hx in Rx. pose proof (U_range E y) as Ry. rewrite Hy in Ry.
unfold zcanon, M64 in *. rewrite Z.mod_small by lia. apply Z.ltb_ge. lia.
Qed.
Lemma ot_ltu_add_r : forall E x y vx vy, U E x = vx -> U E y = vy -> vx + vy < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_ADD y x)) (sv_denot E y) = false.
Proof.
intros E x y vx vy Hx Hy Hs. rewrite branch_ltu_U, U_SAlu. cbn [zalu_raw]. rewrite Hx, Hy.
pose proof (U_range E x) as Rx. rewrite Hx in Rx. pose proof (U_range E y) as Ry. rewrite Hy in Ry.
unfold zcanon, M64 in *. rewrite Z.mod_small by lia. apply Z.ltb_ge. lia.
Qed.
Lemma ot_add_den : forall E x y vx vy, U E x = vx -> U E y = vy -> vx + vy < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD x y) = w64 (vx + vy).
Proof.
intros E x y vx vy Hx Hy Hs. apply ot_den_U. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hx, Hy.
pose proof (U_range E x) as Rx. rewrite Hx in Rx. pose proof (U_range E y) as Ry. rewrite Hy in Ry.
unfold zcanon, M64 in *. apply Z.mod_small. lia.
Qed.

(* A byte of the frame is a byte the journal lets the walk write (the class-2 frame it owns). *)
Lemma ot_frame_awr : forall cx ly' S' (W : world segs) regs' mem' md' e bl0 blc a,
  lc_base B MT XL RLO RHI cx -> lc_core B cx ly' S' W regs' mem' md' e ->
  lc_F cx <= a < lc_F cx + 256 -> awr_byte LLVMF_STK (lc_sp0 cx) [] bl0 blc ly' [(LF_CID, l_fpos cx)] a.
Proof.
intros cx ly' S' W regs' mem' md' e bl0 blc a HB HC Ha.
destruct (lc_geom B MT XL RLO RHI cx ly' S' W regs' mem' md' e HB HC) as [_ _ _ _ HFaddr _ _ _ _].
right. right. right. exists LF_CID, (l_fpos cx). split; [left; reflexivity|].
left. unfold in_zr. cbn [fst snd]. rewrite HFaddr. change (fs_frame_bytes LF_CID) with 256. lia.
Qed.

(* The write right of a run whose writable bytes lie in the stack window or in c (U9, U20: the bases). *)
Ltac ot_awr U9 U20 HFAWR :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      repeat rewrite ew_ewset_other in Ha by lia; repeat rewrite ew_havoc_old in Ha by lia; rewrite ?U9, ?U20 in Ha;
      first [ lia | left; split; [apply HFAWR; lia | lia] | left; split; [left; unfold LLVMF_STK; lia | lia] ] |]);
  apply awr_ok_x_nil.

(* The bytes run C writes: c[0 .. 2], c[24] and 8(s1) .. 23(s1). *)
Ltac ot_win_C U9 U20 Zs :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hx := fresh "Hx" in
  intros b wlo whi x Hin Hx;
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin; unfold Zs;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx;
    repeat rewrite ew_ewset_other in Hx by lia; repeat rewrite ew_havoc_old in Hx by lia;
    rewrite ?U9, ?U20 in Hx; lia |]);
  destruct Hin.

Lemma ot_runC : forall cx op (W : world segs) c,
  lp_prem B MT XL RLO RHI -> lc_base B MT XL RLO RHI cx -> ot_st_103c cx op W c -> SRr segs W c (ot_at_mc cx op).
Proof.
intros cx op W c HP HB H. destruct H as (ly' & S' & regs' & mem' & md' & e & B1 & H). cbv zeta in H.
destruct H as (-> & HCOM & Htw & Hcs & V64 & HRS & R10 & R11 & R16 & R20).
pose proof (lp_laws B MT XL RLO RHI HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned B MT XL RLO RHI HP)) as HGX.
pose proof HCOM as (HL & Hopc & Hob & Hraw & Hser & H24).
assert (Hs1024 : 0 <= TW.g_ncmd B1 < 1024) by exact Hser.
pose proof HL as (HC & (F18 & F26) & HSP & HFSH & HOK & He & HM & R19).
pose proof (ot_geo cx ly' S' W regs' mem' md' e LAWS HB HC) as (Gs1 & Gs01 & Gs1al & Gs047 & GF4 & GFal & GFc & GFapp &
  GFimg & Gn & Gnl & Gp0 & Gp).
pose proof HC as (HJ & _ & _ & _ & Rsp & R8 & R9 & Rgp & Rtp & _).
pose proof alloc_ceiling_val as Hac.
pose proof (ot_n_pos cx op HOK) as Hnp. rewrite <- Gnl in Hnp.
destruct (Gp Hnp) as (Gpin & Gp4 & Gpc & Gpapp & GdpF & Gpimg).
pose proof (ot_tv (l_pl cx) B1 (sv_c (ot_kd cx op))) as TV. cbv zeta in TV.
destruct TV as (_ & _ & Elen & Ec4 & Eoff & En & _ & Ec).
change (lc_tag_vals (l_pl cx) B1 (sv_c (ot_kd cx op))) with (ot_tvx cx op B1) in Elen, Ec4, Eoff, En, Ec.
set (len := tg_len (ot_tvx cx op B1)) in *.
set (c4 := tg_c4 (ot_tvx cx op B1)) in *.
assert (Hlen : 3 <= len <= 24) by (rewrite Elen; pose proof (Z.mod_pos_bound (snd (TOP.fuzz_u8_m (l_pl cx)
  (sv_c (ot_kd cx op)))) 22 ltac:(lia)); lia).
assert (Hc4 : QF.fuzz_in_ok (l_pl cx) c4).
{ pose proof HOK as (_ & _ & Hcok & _ & _). pose proof (ot_c3_ok (l_pl cx) (lo_c op) Hcok) as Hc3.
  rewrite Ec4. destruct (QF.fuzz_u8_ok (l_pl cx) (sv_c (ot_kd cx op)) Hc3) as (c' & v & Eu & Hc' & _).
  rewrite Eu. exact Hc'. }
pose proof Hc4 as (Hc4o & Hc4n & Hc4s).
assert (Hn4 : 0 <= tg_n (ot_tvx cx op B1) <= 21 /\ tg_n (ot_tvx cx op B1) <= TOP.fi_n c4 /\
  tg_n (ot_tvx cx op B1) = (if len - 3 <? TOP.fi_n c4 then len - 3 else TOP.fi_n c4)).
{ rewrite En, <- Ec4, <- Elen. destruct (Z.ltb_spec (len - 3) (TOP.fi_n c4)); lia. }
assert (Ec' : TOP.fi_off (tg_c (ot_tvx cx op B1)) = TOP.fi_off c4 + tg_n (ot_tvx cx op B1))
  by (rewrite Ec, En; cbn [TOP.fi_off]; rewrite <- Ec4; reflexivity).
set (E := ot_E regs' [w64 SHADOW_OFF; w64 (TW.g_ncmd B1)]).
assert (HEI : img_env VAL A_LIM E) by (unfold E, ot_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs' r)
  by (intros n r Hn; unfold E, ot_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E33 : ew E 33 = w64 (TW.g_ncmd B1))
  by (unfold E, ot_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs' _ 1)).
pose proof (eq_trans (EE 9%nat 9%bv eq_refl) R9) as E9.
pose proof (eq_trans (EE 10%nat 10%bv eq_refl) R10) as E10.
pose proof (eq_trans (EE 11%nat 11%bv eq_refl) R11) as E11.
pose proof (eq_trans (EE 16%nat 16%bv eq_refl) R16) as E16.
pose proof (eq_trans (EE 20%nat 20%bv eq_refl) R20) as E20.
pose proof (eq_trans (EE 26%nat 26%bv eq_refl) F26) as E26.
assert (U9 : bv_unsigned (ew E 9) = lc_sp1 cx) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF) by (rewrite E26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U10 : bv_unsigned (ew E 10) = len) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E 11) = l_p cx + TOP.fi_off c4) by (rewrite E11; apply unsigned_lit_small; lia).
assert (U16 : bv_unsigned (ew E 16) = TOP.fi_n c4) by (rewrite E16; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = lc_F cx + 32) by (rewrite E20; apply unsigned_lit_small; lia).
destruct (gx_open segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & _ & _).
assert (HCW : forall a, lc_F cx + 32 <= a < lc_F cx + 64 -> writable_at segs (rd W mem') a).
{ intros a Ha. apply (apresent_writable segs).
  refine (proj1 (awr_byte_present segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJi _)).
  exact (ot_frame_awr cx ly' S' W regs' mem' md' e _ _ a HB HC ltac:(lia)). }
assert (HSTKW : forall a, lc_sp0 cx - LLVMF_STK <= a < lc_sp0 cx -> writable_at segs (rd W mem') a).
{ intros a Ha. apply (apresent_writable segs).
  refine (proj1 (awr_byte_present segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJi _)). left. exact Ha. }
pose proof (fun a Ha => ot_frame_awr cx ly' S' W regs' mem' md' e (ablocks B (l_ly cx) (l_S cx)) (ablocks B ly' S') a
  HB HC Ha) as HFAWR.
assert (HF35 : rdword (aview segs (w_H W) mem') (lc_sp1 cx + 48) = Some (lc_F cx + 35)).
{ unfold lc_spills in HSP. rewrite Forall_forall in HSP. refine (HSP (48, lc_F cx + 35) _).
  unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm. cbn [app].
  repeat (first [left; reflexivity | right]). }
assert (HS : @st_ok_pi segs VAL (l_fx cx) E ot_ssC
  (restrict (w_H W) (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (BASE + 0x103c)) mem' (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. apply (@pa_entry_st_ok_full (l_fx cx) rc transportb_listing PI_transportb).
  - unfold E, ot_E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + unfold ot_spC, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HSTKW; unfold LLVMF_STK; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val segs E _ (lc_sp1 cx) 48 8 (SOff 20 3) (lc_F cx + 35));
          [rewrite (ot_den_off E 20 (lc_F cx + 32) 3 E20 ltac:(lia)); f_equal; lia | lia | lia |].
        apply (val_mem_of_rdword segs). exact HF35.
      * apply (chunk_ok_val segs E _ (lc_sp1 cx) 64 8 (SOff 33 0) (TW.g_ncmd B1));
          [apply ot_den_atom; [exact E33 | lia] | lia | lia |].
        apply (val_mem_of_rdword segs). exact V64.
    + unfold ot_c1, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HCW; lia | apply Forall_nil].
    + unfold ot_c2, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HCW; lia | apply Forall_nil].
  - apply pairwise_disjoint_of_extents.
    unfold ot_spC, ot_c1, ot_c2, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9, U20. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  - unfold ot_factsC, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U10, U11, U16, U20, U26, E33. unfold w64. rewrite unsigned_lit_small by lia.
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
assert (SHOK : sh_ok segs (SOff 26 0) OT_SHC E (rd W mem')).
{ apply Forall_cons; [|apply Forall_nil].
  assert (V26 : U E (SOff 26 0) = SHADOW_OFF) by exact (U_atom E 26 SHADOW_OFF E26 ltac:(unfold SHADOW_OFF; lia)).
  assert (V20 : U E (SOff 20 0) = lc_F cx + 32) by exact (U_atom E 20 (lc_F cx + 32) E20 ltac:(lia)).
  split.
  - cbn [she_m she_lo she_hi]. rewrite V26, V20. replace (lc_F cx + 32 + 0) with (lc_F cx + 32) by lia.
    exact (ot_c_ra cx _ (lc_F cx + 32) (32 - 0) HFSH GFal ltac:(lia) ltac:(lia) ltac:(lia)).
  - intros a Ha. cbn [she_m she_lo she_hi Z.min Z.max] in Ha |- *. rewrite V26. rewrite V20 in Ha.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia. }
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
pose proof (paj_branch (fx := l_fx cx) (PI := PI_transportb)) as BR.
unfold lc_cfg.
change (w64 (transportb_text + 0x103c)) with (Z_to_bv 64 (BASE + 0x103c)).
set (Zs := fun a => lc_F cx + 32 <= a < lc_F cx + 35 \/ a = lc_F cx + 56 \/ lc_sp1 cx + 8 <= a < lc_sp1 cx + 24).
(* +0x103c .. +0x107c: c's header and len, s6 = 3, s9 = 0xf0, a2 = len - 3, to `bltu a2, a6` *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ ot_awr U9 U20 HFAWR. }
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem' a)
  by (intros a Ha HZ; apply (YC4b.kept_of_frame _ _ _ _ _ Zs HFr); [ot_win_C U9 U20 Zs | exact Ha | exact HZ]).
pose proof HG as HG1. clear HFr HG.
rename ms into ms1.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
all: change (SAlu ALU_AND (SOff 10 4294967293) (SLit 4294967295)) with ot_s9x in Hc.
all: rewrite branch_ltu_U, (ot_s9_U E len E10 Hlen), (U_atom E 16 (TOP.fi_n c4) E16 ltac:(lia)) in Hc.
(* +0x1080 (a2 = a6 when not taken) .. +0x108c: 16(s1) = a6, s8 = a2 + a1, to the take test `bltu s8, a1` *)
all: paj_run_tok RUN HS HJ SHOK YC4b.Bspan; [ot_awr U9 U20 HFAWR|].
all: assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem' a)
  by (intros a Ha HZ; rewrite <- (KM1 a Ha HZ);
      apply (YC4b.kept_of_frame _ _ _ _ _ Zs HFr); [ot_win_C U9 U20 Zs | exact Ha | exact HZ]).
all: pose proof (fun a H => apresent_grows _ _ _ a HG (apresent_grows _ _ _ a HG1 H)) as HG2.
all: clear HFr HG KM1.
all: rename ms into ms2.
all: psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
(* the take test is not taken: s8 = a1 + n does not wrap *)
1, 3: exfalso.
1: exact (diff_false_true (eq_trans (eq_sym (ot_ltu_add_l E ot_s9x (SOff 11 0) (len - 3) (l_p cx + TOP.fi_off c4)
     (ot_s9_U E len E10 Hlen) (U_atom E 11 _ E11 ltac:(lia)) ltac:(lia))) Hc0)).
1: exact (diff_false_true (eq_trans (eq_sym (ot_ltu_add_r E (SOff 16 0) (SOff 11 0) (TOP.fi_n c4)
     (l_p cx + TOP.fi_off c4) (U_atom E 16 _ E16 ltac:(lia)) (U_atom E 11 _ E11 ltac:(lia)) ltac:(lia))) Hc0)).
(* +0x1090 .. +0x109c: `beqz s8` (s8 >= 4096), 8(s1) = n, a0 = c + 3, to the call *)
all: paj_run_tok RUN HS HJ SHOK YC4b.Bspan; [ot_awr U9 U20 HFAWR|].
all: pmkst HS; ot_norm HS; apply SRr_ret.
all: assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem' a)
  by (intros a Ha HZ; rewrite <- (KM2 a Ha HZ);
      apply (YC4b.kept_of_frame _ _ _ _ _ Zs HFr); [ot_win_C U9 U20 Zs | exact Ha | exact HZ]).
all: pose proof (fun a H => apresent_grows _ _ _ a HG (HG2 a H)) as HPR.
all: assert (HKEEP : forall a, ot_keep cx a -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem' a)
  by (intros a Ha; destruct (ot_keep_wr cx ly' S' W regs' mem' md' e LAWS HB HC a Ha) as (H64 & _ & H8 & _ & Hcc & _);
      apply KM; [exact H64 | unfold Zs; lia]).
(* the regions at the call *)
all: pose proof (YC4b.st_ok_region_nth E _ _ 0 _ HS eq_refl) as RG0.
all: pose proof (YC4b.st_ok_region_nth E _ _ 1 _ HS eq_refl) as RG1.
all: pose proof (YC4b.st_ok_region_nth E _ _ 2 _ HS eq_refl) as RG2.
all: cbn [ms_mem restrict] in RG0, RG1, RG2.
all: pose proof (ot_chunk_rd E (w_H W) (ms_mem ms) _ 0 1 (SLit 160) 160
    (ot_region_chunk E _ _ _ _ _ _ _ (YP09.mkChunk 0 (CVal 1 (SLit 160))) RG1
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])))
    eq_refl ltac:(cbn; lia) 0 ltac:(cbn; lia)) as B0.
all: pose proof (ot_chunk_rd E (w_H W) (ms_mem ms) _ 1 1 ot_c1x (Z.land (TW.g_ncmd B1) 127)
    (ot_region_chunk E _ _ _ _ _ _ _ (YP09.mkChunk 1 (CVal 1 ot_c1x)) RG1
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])))
    (ot_c1_den E _ E33 Hs1024) ltac:(cbn; lia) 0 ltac:(cbn; lia)) as B1'.
all: pose proof (ot_chunk_rd E (w_H W) (ms_mem ms) _ 2 1 ot_c2x (Z.land (Z.shiftr (TW.g_ncmd B1) 7) 127)
    (ot_region_chunk E _ _ _ _ _ _ _ (YP09.mkChunk 2 (CVal 1 ot_c2x)) RG1
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])))
    (ot_c2_den E _ E33 Hs1024) ltac:(cbn; lia) 0 ltac:(cbn; lia)) as B2.
all: pose proof (ot_chunk_rd E (w_H W) (ms_mem ms) _ 24 1 (SOff 10 0) len
    (ot_region_chunk E _ _ _ _ _ _ _ (YP09.mkChunk 24 (CVal 1 (SOff 10 0))) RG2
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])))
    (ot_den_atom E 10 len E10 ltac:(lia)) ltac:(cbn; lia) 0 ltac:(cbn; lia)) as B24.
all: rewrite U20 in B0, B1', B2, B24.
all: assert (Hs7 : 0 <= Z.land (TW.g_ncmd B1) 127 < 256)
  by (rewrite (Z.land_ones _ 7) by lia; pose proof (Z.mod_pos_bound (TW.g_ncmd B1) (2 ^ 7) ltac:(lia)); lia).
all: assert (Hs8 : 0 <= Z.land (Z.shiftr (TW.g_ncmd B1) 7) 127 < 256)
  by (rewrite (Z.land_ones _ 7) by lia;
      pose proof (Z.mod_pos_bound (Z.shiftr (TW.g_ncmd B1) 7) (2 ^ 7) ltac:(lia)); lia).
all: rewrite ot_le1 in B0, B1', B2, B24 by lia.
all: replace (lc_F cx + 32 + 0 + Z.of_nat 0) with (lc_F cx + 32) in B0 by lia.
all: replace (lc_F cx + 32 + 1 + Z.of_nat 0) with (lc_F cx + 33) in B1' by lia.
all: replace (lc_F cx + 32 + 2 + Z.of_nat 0) with (lc_F cx + 34) in B2 by lia.
all: replace (lc_F cx + 32 + 24 + Z.of_nat 0) with (lc_F cx + 56) in B24 by lia.
all: pose proof (ot_rdword_chunk E (w_H W) (ms_mem ms) _ 16 (SOff 16 0) (TOP.fi_n c4)
  (ot_region_chunk E _ _ _ _ _ _ _ (YP09.mkChunk 16 (CVal 8 (SOff 16 0))) RG0
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])))
  (ot_den_atom E 16 _ E16 ltac:(lia)) ltac:(lia)) as V16.
all: rewrite U9 in V16.
all: assert (Q2 : YK11.getr (ms_regs ms) 2 = YK11.getr regs' 2) by ot_same HS EE.
all: assert (Q3 : YK11.getr (ms_regs ms) 3 = YK11.getr regs' 3) by ot_same HS EE.
all: assert (Q4 : YK11.getr (ms_regs ms) 4 = YK11.getr regs' 4) by ot_same HS EE.
all: assert (Q8 : YK11.getr (ms_regs ms) 8 = YK11.getr regs' 8) by ot_same HS EE.
all: assert (Q9 : YK11.getr (ms_regs ms) 9 = YK11.getr regs' 9) by ot_same HS EE.
all: assert (Q18 : YK11.getr (ms_regs ms) 18 = YK11.getr regs' 18) by ot_same HS EE.
all: assert (Q19 : YK11.getr (ms_regs ms) 19 = YK11.getr regs' 19) by ot_same HS EE.
all: assert (Q20 : YK11.getr (ms_regs ms) 20 = YK11.getr regs' 20) by ot_same HS EE.
all: assert (Q21 : YK11.getr (ms_regs ms) 21 = YK11.getr regs' 21) by ot_same HS EE.
all: assert (Q23 : YK11.getr (ms_regs ms) 23 = YK11.getr regs' 23) by ot_same HS EE.
all: assert (Q26 : YK11.getr (ms_regs ms) 26 = YK11.getr regs' 26) by ot_same HS EE.
all: assert (Q27 : YK11.getr (ms_regs ms) 27 = YK11.getr regs' 27) by ot_same HS EE.
all: ot_rv HS (Z_to_bv 5 10) X10; ot_rv HS (Z_to_bv 5 11) X11; ot_rv HS (Z_to_bv 5 12) X12;
  ot_rv HS (Z_to_bv 5 22) X22; ot_rv HS (Z_to_bv 5 24) X24; ot_rv HS (Z_to_bv 5 25) X25; ot_rv HS (Z_to_bv 5 1) X1.
(* n, a2 and s8 on each side of the min *)
1: assert (EN : tg_n (ot_tvx cx op B1) = len - 3)
     by (destruct Hn4 as (_ & _ & En4); rewrite En4; apply Z.ltb_lt in Hc; rewrite (proj2 (Z.ltb_lt _ _) Hc); reflexivity).
2: assert (EN : tg_n (ot_tvx cx op B1) = TOP.fi_n c4)
     by (destruct Hn4 as (_ & _ & En4); rewrite En4; apply Z.ltb_ge in Hc;
         destruct (Z.ltb_spec (len - 3) (TOP.fi_n c4)); [lia | reflexivity]).
1: assert (A12 : YK11.getr (ms_regs ms) 12 = w64 (tg_n (ot_tvx cx op B1)))
     by (rewrite EN; exact (eq_trans X12 (ot_s9_den E len E10 Hlen))).
2: assert (A12 : YK11.getr (ms_regs ms) 12 = w64 (tg_n (ot_tvx cx op B1)))
     by (rewrite EN; exact (eq_trans X12 (ot_den_atom E 16 _ E16 ltac:(lia)))).
1: assert (A24 : YK11.getr (ms_regs ms) 24 = w64 (l_p cx + TOP.fi_off (tg_c (ot_tvx cx op B1))))
     by (rewrite Ec', EN; refine (eq_trans X24 (eq_trans (ot_add_den E ot_s9x (SOff 11 0) (len - 3)
           (l_p cx + TOP.fi_off c4) (ot_s9_U E len E10 Hlen) (U_atom E 11 _ E11 ltac:(lia)) ltac:(lia)) _));
         unfold w64; f_equal; lia).
2: assert (A24 : YK11.getr (ms_regs ms) 24 = w64 (l_p cx + TOP.fi_off (tg_c (ot_tvx cx op B1))))
     by (rewrite Ec', EN; refine (eq_trans X24 (eq_trans (ot_add_den E (SOff 11 0) (SOff 16 0)
           (l_p cx + TOP.fi_off c4) (TOP.fi_n c4) (U_atom E 11 _ E11 ltac:(lia)) (U_atom E 16 _ E16 ltac:(lia))
           ltac:(lia)) _)); unfold w64; f_equal; lia).
1: pose proof (ot_rdword_chunk E (w_H W) (ms_mem ms) _ 8 ot_s9x (tg_n (ot_tvx cx op B1))
     (ot_region_chunk E _ _ _ _ _ _ _ (YP09.mkChunk 8 (CVal 8 ot_s9x)) RG0
       ltac:(cbn [In]; repeat (first [left; reflexivity | right])))
     ltac:(rewrite EN; exact (ot_s9_den E len E10 Hlen)) ltac:(lia)) as V8.
2: pose proof (ot_rdword_chunk E (w_H W) (ms_mem ms) _ 8 (SOff 16 0) (tg_n (ot_tvx cx op B1))
     (ot_region_chunk E _ _ _ _ _ _ _ (YP09.mkChunk 8 (CVal 8 (SOff 16 0))) RG0
       ltac:(cbn [In]; repeat (first [left; reflexivity | right])))
     ltac:(rewrite EN; exact (ot_den_atom E 16 _ E16 ltac:(lia))) ltac:(lia)) as V8.
all: rewrite U9 in V8.
all: unfold ot_at_mc. all: exists ly', S', (ms_regs ms), (ms_mem ms). all: eexists. all: exists e, B1. all: cbv zeta.
all: split; [reflexivity|].
all: split; [split; [exact (ot_lcore_kept cx op (lo_k op) ly' S' W regs' mem' md' e (ms_regs ms) (ms_mem ms) _ Gnl HL HJ
          Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q26 HPR HKEEP)|];
  split; [exact Hopc|]; split; [exact Hob|]; split; [exact Hraw|]; split; [exact Hser|];
  apply (ot_rdword_kept _ _ _ _ H24); intros i Hi; apply HKEEP; right; right; right; right; left; lia|].
all: split; [apply (tw_kept TMAP_B (aview segs (w_H W) mem') _ _ Htw); intros x Hx;
  destruct (ot_tw_out cx ly' S' W regs' mem' md' e LAWS HB HC x Hx) as (H64 & _ & H8 & _ & Hcx & _);
  apply KM; [exact H64 | unfold Zs; lia]|].
all: split.
all: try (refine (ot_garr8_patch (w_H W) mem' (ms_mem ms) (lc_F cx + 32) _ _ (fun j => (j < 3)%nat \/ j = 24%nat) _ Hcs _ _);
  [ rewrite !ot_cs_len; try reflexivity; rewrite ?length_app, ?repeat_length; reflexivity
  | intros j Hj; rewrite ot_cs_len in Hj by (rewrite repeat_length; reflexivity);
    destruct (lt_dec j 3) as [Hj3 | Hj3]; [left; left; exact Hj3|];
    destruct (Nat.eq_dec j 24) as [Hj24 | Hj24]; [left; right; exact Hj24|];
    right; split;
    [ do 32 (destruct j as [|j]; [first [exfalso; lia | reflexivity] |]); lia
    | apply KM; [lia | unfold Zs; lia] ]
  | intros j Hj [Hj3 | Hj24];
    [ destruct j as [|[|[|j]]]; [| | | lia]; cbn [nth TW.zs TOP.cmd_struct ot_hdr app map Z.of_nat];
      [ rewrite Z.add_0_r, B0, ot_b8 by (unfold TC.TAG; lia); unfold TC.TAG; split; [reflexivity | lia]
      | rewrite ot_b8 by exact Hs7; replace (lc_F cx + 32 + Z.of_nat 1) with (lc_F cx + 33) by lia;
        split; [exact B1' | exact Hs7]
      | rewrite ot_b8 by exact Hs8; replace (lc_F cx + 32 + Z.of_nat 2) with (lc_F cx + 34) by lia;
        split; [exact B2 | exact Hs8] ]
    | subst j; cbn [nth TW.zs TOP.cmd_struct ot_hdr app map repeat];
      replace (lc_F cx + 32 + Z.of_nat 24) with (lc_F cx + 56) by lia;
      rewrite ot_b8 by lia; split; [exact B24 | lia] ] ]).
all: split; [apply (ot_rdword_kept _ _ _ _ V64); intros i Hi; apply KM; [lia | unfold Zs; lia]|].
all: split; [exact V16|]. all: split; [exact V8|].
all: split; [destruct HRS as (R21 & R23 & R27);
  split; [exact (eq_trans Q21 R21)|]; split; [exact (eq_trans Q23 R23) | exact (eq_trans Q27 R27)]|].
all: split; [exact (eq_trans Q20 R20)|].
all: split; [exact (eq_trans X22 eq_refl)|]. all: split; [exact (eq_trans X25 eq_refl)|].
all: split; [exact A24|].
all: split; [refine (eq_trans X10 _); rewrite (ot_den_off E 20 (lc_F cx + 32) 3 E20 ltac:(lia)); unfold w64; f_equal; lia|].
all: split; [exact (eq_trans X11 (ot_den_atom E 11 _ E11 ltac:(lia)))|].
all: split; [exact A12|].
all: exact (eq_trans X1 (codeptr_val E 4256 HEI)).
Qed.

(* ------------------------------------------------------------------ *)
(* 8. __asan_memcpy (c + 3, a1, n) at +0x109c                          *)
(* ------------------------------------------------------------------ *)

(* The return of __asan_memcpy (+0x10a0): c holds cmd_struct cbytes len display key. *)
Definition ot_st_10a0 (cx : lcx) (op : lop) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' e B1,
    let kd := ot_kd cx op in
    let tv := ot_tvx cx op B1 in
    c' = lc_cfg cx 0x10a0 regs' mem' md' /\
    ot_com cx op B1 ly' S' W' regs' mem' md' e /\ lc_tw W' mem' (tg_B2 tv) /\
    garr8 segs (rd W' mem') (lc_F cx + 32) (TW.zs (TOP.cmd_struct (tg_cbytes tv) (tg_len tv) (sv_display kd) (sv_key kd))) /\
    rdword (aview segs (w_H W') mem') (lc_sp1 cx + 64) = Some (TW.g_ncmd B1) /\
    rdword (aview segs (w_H W') mem') (lc_sp1 cx + 16) = Some (TOP.fi_n (tg_c4 tv)) /\
    rdword (aview segs (w_H W') mem') (lc_sp1 cx + 8) = Some (tg_n tv) /\
    ot_rs regs' B1 /\ YK11.getr regs' 20 = w64 (lc_F cx + 32) /\
    YK11.getr regs' 22 = w64 3 /\ YK11.getr regs' 25 = w64 0xf0 /\
    YK11.getr regs' 24 = w64 (l_p cx + TOP.fi_off (tg_c tv)).

(* A byte of a byte array, through the view. *)
Lemma ot_garr8_view : forall (H : word -> bool) (m : word -> option byte) base (l : list Z) j,
  garr8 segs (mrestrict H m) base l -> (j < length l)%nat ->
  aview segs H m (base + Z.of_nat j) = Some (nth j l 0) /\ 0 <= nth j l 0 < 256.
Proof.
intros H m base l j HG Hj. destruct (HG j Hj) as (Hv & Hr). split; [|exact Hr].
pose proof (Hv 0%nat ltac:(lia)) as V. cbn [Z.of_nat] in V. rewrite Z.add_0_r in V.
change (aview segs H m (base + Z.of_nat j))
  with (option_map (fun b : byte => bv_unsigned b) (YP09.mbyte segs (mrestrict H m) (base + Z.of_nat j))).
rewrite V. cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned, ot_le1 by exact Hr.
apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

(* c's 24 bytes after the take: the header, the n bytes taken, zeros. *)
Lemma ot_cb_len : forall (h D : list byte) off n, length h = 3%nat -> 0 <= off -> 0 <= n <= 21 ->
  off + n <= Z.of_nat (length D) ->
  length (h ++ TW.sub D off (Z.to_nat n) ++ repeat (DSpec.b8 0) (Z.to_nat (21 - n))) = 24%nat.
Proof.
intros h D off n Hh Ho Hn HD. unfold TW.sub. rewrite !length_app, repeat_length, length_firstn, length_skipn, Hh. lia.
Qed.

Lemma ot_nth_firstn : forall (A : Type) (l : list A) i n d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
intros A l. induction l as [|a l IH]; intros i n d Hi.
- destruct n; cbn [firstn]; reflexivity.
- destruct n as [|n]; [lia|]. cbn [firstn]. destruct i as [|i]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.
Lemma ot_nth_skipn : forall (A : Type) (l : list A) m i d, nth i (skipn m l) d = nth (m + i) l d.
Proof.
intros A l m. revert l. induction m as [|m IH]; intros l i d; [reflexivity|].
destruct l as [|a l]; cbn [skipn]; [destruct i; reflexivity|]. cbn [Nat.add nth]. apply IH.
Qed.

Lemma ot_cb_in : forall (h D : list byte) off n len d k j, length h = 3%nat -> 0 <= off -> 0 <= n <= 21 ->
  off + n <= Z.of_nat (length D) -> (3 <= j < 3 + Z.to_nat n)%nat ->
  nth j (TW.zs (TOP.cmd_struct (h ++ TW.sub D off (Z.to_nat n) ++ repeat (DSpec.b8 0) (Z.to_nat (21 - n))) len d k)) 0 =
  nth (Z.to_nat off + (j - 3)) (TW.zs D) 0.
Proof.
intros h D off n len d k j Hh Ho Hn HD Hj.
pose proof (ot_cb_len h D off n Hh Ho Hn HD) as HL.
assert (Hs : length (TW.sub D off (Z.to_nat n)) = Z.to_nat n)
  by (unfold TW.sub; rewrite length_firstn, length_skipn; lia).
unfold TW.zs, TOP.cmd_struct.
set (L1 := h ++ TW.sub D off (Z.to_nat n) ++ repeat (DSpec.b8 0) (Z.to_nat (21 - n))) in *.
rewrite (map_app _ L1). rewrite (app_nth1 (map _ L1)) by (rewrite length_map; lia).
unfold L1. rewrite !map_app.
rewrite (app_nth2 (map _ h)) by (rewrite length_map; lia). rewrite length_map, Hh.
rewrite (app_nth1 (map _ (TW.sub D off (Z.to_nat n)))) by (rewrite length_map, Hs; lia).
rewrite (nth_indep (map _ (TW.sub D off (Z.to_nat n))) 0 (bv_unsigned (DSpec.b8 0))) by (rewrite length_map, Hs; lia).
rewrite (nth_indep (map _ D) 0 (bv_unsigned (DSpec.b8 0))) by (rewrite length_map; lia).
rewrite !map_nth. unfold TW.sub. rewrite ot_nth_firstn by lia. rewrite ot_nth_skipn. reflexivity.
Qed.

Lemma ot_cb_out : forall (h D : list byte) off n len d k j, length h = 3%nat -> 0 <= off -> 0 <= n <= 21 ->
  off + n <= Z.of_nat (length D) -> ~ (3 <= j < 3 + Z.to_nat n)%nat ->
  nth j (TW.zs (TOP.cmd_struct (h ++ TW.sub D off (Z.to_nat n) ++ repeat (DSpec.b8 0) (Z.to_nat (21 - n))) len d k)) 0 =
  nth j (TW.zs (TOP.cmd_struct (h ++ repeat (DSpec.b8 0) 21) len d k)) 0.
Proof.
intros h D off n len d k j Hh Ho Hn HD Hj.
pose proof (ot_cb_len h D off n Hh Ho Hn HD) as HL.
assert (HL0 : length (h ++ repeat (DSpec.b8 0) 21) = 24%nat) by (rewrite length_app, repeat_length, Hh; reflexivity).
assert (Hs : length (TW.sub D off (Z.to_nat n)) = Z.to_nat n)
  by (unfold TW.sub; rewrite length_firstn, length_skipn; lia).
unfold TW.zs, TOP.cmd_struct.
set (L1 := h ++ TW.sub D off (Z.to_nat n) ++ repeat (DSpec.b8 0) (Z.to_nat (21 - n))) in *.
set (L2 := h ++ repeat (DSpec.b8 0) 21) in *.
rewrite (map_app _ L1), (map_app _ L2).
destruct (lt_dec j 24) as [J24 | J24].
2: { rewrite (app_nth2 (map _ L1)) by (rewrite length_map; lia). rewrite (app_nth2 (map _ L2)) by (rewrite length_map; lia).
     rewrite !length_map, HL, HL0. reflexivity. }
rewrite (app_nth1 (map _ L1)) by (rewrite length_map; lia). rewrite (app_nth1 (map _ L2)) by (rewrite length_map; lia).
unfold L1, L2. rewrite !map_app.
destruct (lt_dec j 3) as [J3 | J3].
- rewrite (app_nth1 (map _ h)) by (rewrite length_map; lia). rewrite (app_nth1 (map _ h)) by (rewrite length_map; lia).
  reflexivity.
- rewrite (app_nth2 (map _ h)) by (rewrite length_map; lia). rewrite (app_nth2 (map _ h)) by (rewrite length_map; lia).
  rewrite !length_map, Hh.
  rewrite (app_nth2 (map _ (TW.sub D off (Z.to_nat n)))) by (rewrite length_map, Hs; lia). rewrite length_map, Hs.
  rewrite !map_repeat.
  rewrite (nth_indep (repeat _ (Z.to_nat (21 - n))) 0 (bv_unsigned (DSpec.b8 0))) by (rewrite repeat_length; lia).
  rewrite (nth_indep (repeat _ 21) 0 (bv_unsigned (DSpec.b8 0))) by (rewrite repeat_length; lia).
  rewrite !nth_repeat. reflexivity.
Qed.

Lemma ot_call_mc : forall cx op (W : world segs) c,
  lp_prem B MT XL RLO RHI -> lc_base B MT XL RLO RHI cx -> ot_at_mc cx op W c -> SRr segs W c (ot_st_10a0 cx op).
Proof.
intros cx op W c HP HB H. destruct H as (ly' & S' & regs' & mem' & md' & e & B1 & H). cbv zeta in H.
destruct H as (-> & HCOM & Htw & Hcs & V64 & V16 & V8 & HRS & R20 & R22 & R25 & R24 & R10 & R11 & R12 & R1).
pose proof (lp_laws B MT XL RLO RHI HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned B MT XL RLO RHI HP)) as HGX.
pose proof HCOM as (HL & Hopc & Hob & Hraw & Hser & H24).
assert (Hs1024 : 0 <= TW.g_ncmd B1 < 1024) by exact Hser.
pose proof HL as (HC & (F18 & F26) & HSP & HFSH & HOK & He & HM & R19).
pose proof (ot_geo cx ly' S' W regs' mem' md' e LAWS HB HC) as (Gs1 & Gs01 & Gs1al & Gs047 & GF4 & GFal & GFc & GFapp &
  GFimg & Gn & Gnl & Gp0 & Gp).
pose proof HC as (HJ & _ & _ & _ & Rsp & R8 & R9 & Rgp & Rtp & _ & _ & _ & _ & _ & _ & _ & _ & HIN).
destruct HIN as (HPAYg & _).
pose proof (ot_sp16 cx ly' S' W regs' mem' md' e HB HC) as Hsp16.
pose proof alloc_ceiling_val as Hac.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
pose proof (ot_n_pos cx op HOK) as Hnp. rewrite <- Gnl in Hnp.
destruct (Gp Hnp) as (Gpin & Gp4 & Gpc & Gpapp & GdpF & Gpimg).
pose proof (ot_tv (l_pl cx) B1 (sv_c (ot_kd cx op))) as TV. cbv zeta in TV.
destruct TV as (_ & _ & Elen & Ec4 & _ & En & Ecb & _).
rewrite <- En in Ecb. rewrite <- Ec4 in Ecb, En.
change (lc_tag_vals (l_pl cx) B1 (sv_c (ot_kd cx op))) with (ot_tvx cx op B1) in Elen, Ec4, En, Ecb.
set (len := tg_len (ot_tvx cx op B1)) in *.
set (c4 := tg_c4 (ot_tvx cx op B1)) in *.
set (n := tg_n (ot_tvx cx op B1)) in *.
assert (Hlen : 3 <= len <= 24) by (rewrite Elen; pose proof (Z.mod_pos_bound (snd (TOP.fuzz_u8_m (l_pl cx)
  (sv_c (ot_kd cx op)))) 22 ltac:(lia)); lia).
assert (Hc4 : QF.fuzz_in_ok (l_pl cx) c4).
{ pose proof HOK as (_ & _ & Hcok & _ & _). pose proof (ot_c3_ok (l_pl cx) (lo_c op) Hcok) as Hc3.
  rewrite Ec4. destruct (QF.fuzz_u8_ok (l_pl cx) (sv_c (ot_kd cx op)) Hc3) as (c' & v & Eu & Hc' & _).
  rewrite Eu. exact Hc'. }
pose proof Hc4 as (Hc4o & Hc4n & Hc4s).
assert (Hc4b : 0 <= TOP.fi_off c4 /\ 0 <= TOP.fi_n c4 /\ TOP.fi_off c4 + TOP.fi_n c4 <= l_n cx) by (rewrite Gnl; lia).
assert (Hn4 : 0 <= n <= 21 /\ n <= TOP.fi_n c4)
  by (rewrite En, <- Elen; destruct (Z.ltb_spec (len - 3) (TOP.fi_n c4)); lia).
set (x := l_p cx + TOP.fi_off c4).
assert (HXam : amem_range x n).
{ unfold amem_range, x. pose proof alloc_ceiling_val.
  unfold in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in Gpapp |- *. lia. }
assert (HSRC : forall i, 0 <= i < n -> aview segs (w_H W) mem' (x + i) =
    Some (nth (Z.to_nat (TOP.fi_off c4 + i)) (map (fun b : byte => bv_unsigned b) (l_pl cx)) 0) /\
    0 <= nth (Z.to_nat (TOP.fi_off c4 + i)) (map (fun b : byte => bv_unsigned b) (l_pl cx)) 0 < 256).
{ intros i Hi. pose proof (ot_garr8_view (w_H W) mem' (l_p cx) _ (Z.to_nat (TOP.fi_off c4 + i)) HPAYg
    ltac:(rewrite length_map; lia)) as (V & Vr).
  rewrite Z2Nat.id in V by lia. unfold x. rewrite <- Z.add_assoc. split; [exact V | exact Vr]. }
eapply SRr_bind.
{ apply (@gx_intrin_at (l_fx cx) rc tfib_sink_head segs B LAWS transportb_segs_low OCpy
    (transportb_sigma TB___asan_memcpy)
    (lp_memcpy B MT XL RLO RHI HP (l_fx cx)) TG.G_HARNESS_B W regs' mem' LLVMF_STK (lc_sp0 cx) [] (l_ly cx) (l_S cx)
    (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly' S' md' e (lc_F cx + 35) x n
    (lc_sp1 cx - lc_sp0 cx) (w64 (transportb_text + 0x10a0)) HGX G_HARNESS_B_rw HJ R10 R11 R12).
  - lia.
  - lia.
  - lia.
  - unfold spZ. rewrite Rsp. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact Hsp16.
  - lia.
  - unfold ESTACK, LLVMF_STK. lia.
  - exact Rgp.
  - exact Rtp.
  - exact R1.
  - exact (ret_ok_codeptr_v (PI := PI_transportb) 0x10a0 ltac:(lia) eq_refl).
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|]. intros a Ha. left.
    split; [exact (ot_frame_awr cx ly' S' W regs' mem' md' e _ _ a HB HC ltac:(lia))|].
    unfold spZ. rewrite Rsp. unfold w64. rewrite unsigned_lit_small by lia. unfold ESTACK. lia.
  - unfold amem_range. pose proof alloc_ceiling_val.
    unfold in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in GFapp |- *. lia.
  - exact (ot_c_ra cx _ (lc_F cx + 35) n HFSH GFal ltac:(lia) ltac:(lia) ltac:(lia)).
  - intros Hn0. exact (ot_c_hull cx _ (lc_F cx + 35) n HFSH GFal ltac:(lia) ltac:(lia) ltac:(lia) Hn0).
  - assert (RQ : req_size (l_n cx) = l_n cx) by (unfold req_size; destruct (Z.eqb_spec (l_n cx) 0); lia).
    split; [lia|]. split; [lia|].
    split.
    { intros a Ha. split.
      - replace a with (x + (a - x)) by lia. rewrite (proj1 (HSRC (a - x) ltac:(lia))). discriminate.
      - unfold spZ. rewrite Rsp. unfold w64. rewrite unsigned_lit_small by lia. unfold ESTACK. lia. }
    split; [unfold x; lia|]. split; [exact HXam|].
    split; [exact (range_addressable_of_block segs B LAWS ly' S' W mem' md' (l_p cx) (l_n cx) x n HAR Gpin
              ltac:(unfold x; lia) ltac:(rewrite RQ; unfold x; lia))|].
    intros Hn. exact (shadow_hull_vis_of_block segs B LAWS ly' S' W mem' md' (l_p cx) (l_n cx) x n HAR Gpin
              ltac:(unfold x; lia) ltac:(rewrite RQ; unfold x; lia) Hn). }
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HPR & Ra0 & Hcpy & Hkeep & Hpres2).
apply SRr_ret.
assert (P2 : YK11.getr regs2 2 = YK11.getr regs' 2) by exact (HPR 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : YK11.getr regs2 3 = YK11.getr regs' 3) by exact (HPR 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : YK11.getr regs2 4 = YK11.getr regs' 4) by exact (HPR 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : YK11.getr regs2 8 = YK11.getr regs' 8) by exact (HPR 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : YK11.getr regs2 9 = YK11.getr regs' 9) by exact (HPR 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : YK11.getr regs2 18 = YK11.getr regs' 18) by exact (HPR 18 ltac:(unfold acallee_saved; lia)).
assert (P19 : YK11.getr regs2 19 = YK11.getr regs' 19) by exact (HPR 19 ltac:(unfold acallee_saved; lia)).
assert (P20 : YK11.getr regs2 20 = YK11.getr regs' 20) by exact (HPR 20 ltac:(unfold acallee_saved; lia)).
assert (P21 : YK11.getr regs2 21 = YK11.getr regs' 21) by exact (HPR 21 ltac:(unfold acallee_saved; lia)).
assert (P22 : YK11.getr regs2 22 = YK11.getr regs' 22) by exact (HPR 22 ltac:(unfold acallee_saved; lia)).
assert (P23 : YK11.getr regs2 23 = YK11.getr regs' 23) by exact (HPR 23 ltac:(unfold acallee_saved; lia)).
assert (P24 : YK11.getr regs2 24 = YK11.getr regs' 24) by exact (HPR 24 ltac:(unfold acallee_saved; lia)).
assert (P25 : YK11.getr regs2 25 = YK11.getr regs' 25) by exact (HPR 25 ltac:(unfold acallee_saved; lia)).
assert (P26 : YK11.getr regs2 26 = YK11.getr regs' 26) by exact (HPR 26 ltac:(unfold acallee_saved; lia)).
assert (P27 : YK11.getr regs2 27 = YK11.getr regs' 27) by exact (HPR 27 ltac:(unfold acallee_saved; lia)).
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (lc_F cx + 32 <= a < lc_F cx + 64) -> ~ (lc_sp1 cx - ESTACK <= a < lc_sp1 cx) ->
  aview segs (w_H W) mem2 a = aview segs (w_H W) mem' a)
  by (intros a Ha H1 H2; apply Hkeep; [exact Ha | lia | lia]).
assert (HKEEP : forall a, ot_keep cx a -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem' a).
{ intros a Ha. destruct (ot_keep_wr cx ly' S' W regs' mem' md' e LAWS HB HC a Ha) as (H64 & Hst & _ & _ & Hcc & _).
  exact (KR a H64 Hcc Hst). }
assert (KSP : forall a, lc_sp1 cx <= a < lc_sp1 cx + 192 -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem' a)
  by (intros a Ha; apply KR; [lia | lia | unfold ESTACK; lia]).
unfold ot_st_10a0. exists ly', S', regs2, mem2, md2, e, B1. cbv zeta.
split; [reflexivity|].
split.
{ split; [exact (ot_lcore_kept cx op (lo_k op) ly' S' W regs' mem' md' e regs2 mem2 md2 Gnl HL HJ2
          P2 P3 P4 P8 P9 P18 P19 P26 Hpres2 HKEEP)|].
  split; [exact Hopc|]. split; [exact Hob|]. split; [exact Hraw|]. split; [exact Hser|].
  apply (ot_rdword_kept _ _ _ _ H24); intros i Hi; apply KSP; lia. }
split.
{ apply (tw_kept TMAP_B (aview segs (w_H W) mem') _ _ Htw). intros x0 Hx0.
  destruct (ot_tw_out cx ly' S' W regs' mem' md' e LAWS HB HC x0 Hx0) as (H64 & Hst & _ & _ & Hcc & _).
  exact (KR x0 H64 Hcc Hst). }
split.
{ rewrite Ecb. fold (ot_hdr (TW.g_ncmd B1)).
  assert (Hh : length (ot_hdr (TW.g_ncmd B1)) = 3%nat) by reflexivity.
  assert (HD : TOP.fi_off c4 + n <= Z.of_nat (length (l_pl cx))) by lia.
  refine (ot_garr8_patch (w_H W) mem' mem2 (lc_F cx + 32) _ _ (fun j => (3 <= j < 3 + Z.to_nat n)%nat) _ Hcs _ _).
  - rewrite !ot_cs_len by first [exact (ot_cb_len _ (l_pl cx) (TOP.fi_off c4) n Hh Hc4o (proj1 Hn4) HD) |
      rewrite length_app, repeat_length, Hh; reflexivity]. reflexivity.
  - intros j Hj. rewrite ot_cs_len in Hj by (rewrite length_app, repeat_length, Hh; reflexivity).
    destruct (le_lt_dec 3 j) as [J1 | J1]; [destruct (lt_dec j (3 + Z.to_nat n)) as [J2 | J2]|].
    + left. lia.
    + right. split; [exact (ot_cb_out _ (l_pl cx) (TOP.fi_off c4) n _ _ _ j Hh Hc4o (proj1 Hn4) HD ltac:(lia))|].
      apply Hkeep; [lia | lia | unfold ESTACK; lia].
    + right. split; [exact (ot_cb_out _ (l_pl cx) (TOP.fi_off c4) n _ _ _ j Hh Hc4o (proj1 Hn4) HD ltac:(lia))|].
      apply Hkeep; [lia | lia | unfold ESTACK; lia].
  - intros j Hj Pj. rewrite (ot_cb_in _ (l_pl cx) (TOP.fi_off c4) n _ _ _ j Hh Hc4o (proj1 Hn4) HD Pj).
    pose proof (Hcpy (Z.of_nat j - 3) ltac:(lia)) as Cj.
    replace (lc_F cx + 35 + (Z.of_nat j - 3)) with (lc_F cx + 32 + Z.of_nat j) in Cj by lia.
    rewrite Cj. pose proof (HSRC (Z.of_nat j - 3) ltac:(lia)) as (V & Vr).
    replace (Z.to_nat (TOP.fi_off c4 + (Z.of_nat j - 3))) with (Z.to_nat (TOP.fi_off c4) + (j - 3))%nat in V, Vr by lia.
    split; [exact V | exact Vr]. }
split; [apply (ot_rdword_kept _ _ _ _ V64); intros i Hi; apply KSP; lia|].
split; [apply (ot_rdword_kept _ _ _ _ V16); intros i Hi; apply KSP; lia|].
split; [apply (ot_rdword_kept _ _ _ _ V8); intros i Hi; apply KSP; lia|].
split; [destruct HRS as (R21 & R23 & R27);
  split; [exact (eq_trans P21 R21)|]; split; [exact (eq_trans P23 R23) | exact (eq_trans P27 R27)]|].
split; [exact (eq_trans P20 R20)|].
split; [exact (eq_trans P22 R22)|]. split; [exact (eq_trans P25 R25)|].
exact (eq_trans P24 R24).
Qed.

(* ------------------------------------------------------------------ *)
(* 9. Run D: +0x10a0 .. SYSL 0 (+0x10b0) or SYSJ (+0x1170)             *)
(* ------------------------------------------------------------------ *)

(* c[24] of cmd_struct is len. *)
Lemma ot_cs_len24 : forall (l : list byte) len d k, length l = 24%nat -> 0 <= len < 256 ->
  nth 24 (TW.zs (TOP.cmd_struct l len d k)) 0 = len.
Proof.
intros l len d k Hl Hr. unfold TW.zs, TOP.cmd_struct. rewrite map_app, app_nth2 by (rewrite length_map; lia).
rewrite length_map, Hl. cbn [Nat.sub map app nth]. apply ot_b8. exact Hr.
Qed.

(* cbytes has 24 bytes. *)
Lemma ot_cbl : forall cx op B1, QF.fuzz_in_ok (l_pl cx) (lo_c op) -> length (tg_cbytes (ot_tvx cx op B1)) = 24%nat.
Proof.
intros cx op B1 Hcok.
pose proof (ot_tv (l_pl cx) B1 (sv_c (ot_kd cx op))) as TV. cbv zeta in TV.
destruct TV as (_ & _ & Elen & Ec4 & _ & En & Ecb & _).
change (lc_tag_vals (l_pl cx) B1 (sv_c (ot_kd cx op))) with (ot_tvx cx op B1) in Elen, Ec4, En, Ecb.
rewrite <- En in Ecb. rewrite <- Ec4 in Ecb, En. rewrite Ecb.
pose proof (ot_c3_ok (l_pl cx) (lo_c op) Hcok) as Hc3.
assert (Hc4 : QF.fuzz_in_ok (l_pl cx) (tg_c4 (ot_tvx cx op B1))).
{ rewrite Ec4. destruct (QF.fuzz_u8_ok (l_pl cx) (sv_c (ot_kd cx op)) Hc3) as (c' & v & Eu & Hc' & _).
  rewrite Eu. exact Hc'. }
pose proof Hc4 as (Hc4o & Hc4n & Hc4s).
assert (Hlen : 3 <= tg_len (ot_tvx cx op B1) <= 24) by (rewrite Elen; pose proof (Z.mod_pos_bound (snd (TOP.fuzz_u8_m
  (l_pl cx) (sv_c (ot_kd cx op)))) 22 ltac:(lia)); lia).
assert (Hn4 : 0 <= tg_n (ot_tvx cx op B1) <= 21 /\ tg_n (ot_tvx cx op B1) <= TOP.fi_n (tg_c4 (ot_tvx cx op B1)))
  by (rewrite En, <- Elen; destruct (Z.ltb_spec (tg_len (ot_tvx cx op B1) - 3) (TOP.fi_n (tg_c4 (ot_tvx cx op B1))));
      lia).
apply ot_cb_len; [reflexivity | exact Hc4o | exact (proj1 Hn4) | lia].
Qed.

(* lc_tag_common after a stretch that writes nothing and keeps the registers it names. *)
Lemma ot_tagc_mk : forall cx op (W : world segs) ly' S' regs' mem' md' e B1 regs2 mem2 md2,
  lp_prem B MT XL RLO RHI -> lc_base B MT XL RLO RHI cx ->
  ot_com cx op B1 ly' S' W regs' mem' md' e -> lc_tw W mem' (tg_B2 (ot_tvx cx op B1)) ->
  garr8 segs (rd W mem') (lc_F cx + 32) (TW.zs (TOP.cmd_struct (tg_cbytes (ot_tvx cx op B1))
    (tg_len (ot_tvx cx op B1)) (sv_display (ot_kd cx op)) (sv_key (ot_kd cx op)))) ->
  rdword (aview segs (w_H W) mem') (lc_sp1 cx + 64) = Some (TW.g_ncmd B1) ->
  rdword (aview segs (w_H W) mem') (lc_sp1 cx + 16) = Some (TOP.fi_n (tg_c4 (ot_tvx cx op B1))) ->
  rdword (aview segs (w_H W) mem') (lc_sp1 cx + 8) = Some (tg_n (ot_tvx cx op B1)) ->
  ot_rs regs' B1 -> YK11.getr regs' 20 = w64 (lc_F cx + 32) ->
  YK11.getr regs' 24 = w64 (l_p cx + TOP.fi_off (tg_c (ot_tvx cx op B1))) ->
  ot_J cx ly' S' W mem2 md2 e ->
  (forall a, aview segs (w_H W) mem2 a = aview segs (w_H W) mem' a) ->
  (forall a, apresent (w_H W) mem' a -> apresent (w_H W) mem2 a) ->
  YK11.getr regs2 2 = YK11.getr regs' 2 -> YK11.getr regs2 3 = YK11.getr regs' 3 ->
  YK11.getr regs2 4 = YK11.getr regs' 4 -> YK11.getr regs2 8 = YK11.getr regs' 8 ->
  YK11.getr regs2 9 = YK11.getr regs' 9 -> YK11.getr regs2 18 = YK11.getr regs' 18 ->
  YK11.getr regs2 19 = YK11.getr regs' 19 -> YK11.getr regs2 20 = YK11.getr regs' 20 ->
  YK11.getr regs2 23 = YK11.getr regs' 23 -> YK11.getr regs2 24 = YK11.getr regs' 24 ->
  YK11.getr regs2 26 = YK11.getr regs' 26 -> YK11.getr regs2 27 = YK11.getr regs' 27 ->
  lc_tag_common B MT cx op B1 ly' S' W regs2 mem2 md2 e.
Proof.
intros cx op W ly' S' regs' mem' md' e B1 regs2 mem2 md2 HP HB HCOM Htw Hcs V64 V16 V8 (R21 & R23 & R27) R20 R24
  HJ2 KM HPR P2 P3 P4 P8 P9 P18 P19 P20 P23 P24 P26 P27.
destruct HCOM as (HL & Hopc & Hob & Hraw & Hser & H24).
pose proof HL as (HC & _).
pose proof (lp_laws B MT XL RLO RHI HP) as LAWS.
pose proof (ot_geo cx ly' S' W regs' mem' md' e LAWS HB HC) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Gnl & _).
pose proof (ot_tv (l_pl cx) B1 (sv_c (ot_kd cx op))) as TV. cbv zeta in TV. destruct TV as (Eser & _).
change (lc_tag_vals (l_pl cx) B1 (sv_c (ot_kd cx op))) with (ot_tvx cx op B1) in Eser.
unfold lc_tag_common. cbv zeta.
change (lc_tag_vals (l_pl cx) B1 (sv_c (lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op))))) with (ot_tvx cx op B1).
change (lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op))) with (ot_kd cx op).
rewrite Eser.
split; [exact Hopc|].
split; [exact (ot_lcore_kept cx op (lo_k op) ly' S' W regs' mem' md' e regs2 mem2 md2 Gnl HL HJ2
          P2 P3 P4 P8 P9 P18 P19 P26 HPR (fun a _ => KM a))|].
split; [exact Hob|]. split; [exact Hraw|]. split; [exact Hser|].
split; [apply (tw_kept TMAP_B (aview segs (w_H W) mem') _ _ Htw); intros x _; exact (KM x)|].
split; [apply (lc_garr8_kept (w_H W) (w_H W) mem' mem2 (lc_F cx + 32) _); [intros j _; exact (KM _) | exact Hcs]|].
split; [apply (ot_rdword_kept _ _ _ _ H24); intros i _; exact (KM _)|].
split; [apply (ot_rdword_kept _ _ _ _ V16); intros i _; exact (KM _)|].
split; [apply (ot_rdword_kept _ _ _ _ V8); intros i _; exact (KM _)|].
split; [apply (ot_rdword_kept _ _ _ _ V64); intros i _; exact (KM _)|].
split; [exact (eq_trans P24 R24)|]. split; [exact (eq_trans P27 R27)|].
split; [exact (eq_trans P20 R20) | exact (eq_trans P23 R23)].
Qed.

(* c[24] (len, atom 33), read only; nothing written. *)
Definition ot_cD : YP09.region := YP09.mkRegion (Some 20%nat) 24 25 0 0 [YP09.mkChunk 24 (CVal 1 (SOff 33 0))].
Definition ot_factsD (lo hi : Z) : facts := mkFacts [(20%nat, mkAF 4096 (2 ^ 47 - 64) 5); (33%nat, mkAF lo hi 0)] [] [].
Definition ot_ssD (lo hi : Z) : sstate := mkSS 0x10a0 sr_atoms [ot_cD] None (ot_factsD lo hi).

Lemma ot_runD : forall cx op (W : world segs) c,
  lp_prem B MT XL RLO RHI -> lc_base B MT XL RLO RHI cx -> ot_st_10a0 cx op W c ->
  SRr segs W c (fun W2 c2 => lc_st_sysl B MT cx op 0 W2 c2 \/ lc_st_sysj B MT cx op W2 c2).
Proof.
intros cx op W c HP HB H. destruct H as (ly' & S' & regs' & mem' & md' & e & B1 & H). cbv zeta in H.
destruct H as (-> & HCOM & Htw & Hcs & V64 & V16 & V8 & HRS & R20 & R22 & R25 & R24).
pose proof (lp_laws B MT XL RLO RHI HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned B MT XL RLO RHI HP)) as HGX.
pose proof HCOM as (HL & Hopc & Hob & Hraw & Hser & H24).
pose proof HL as (HC & (F18 & F26) & HSP & HFSH & HOK & He & HM & R19).
pose proof (ot_geo cx ly' S' W regs' mem' md' e LAWS HB HC) as (Gs1 & Gs01 & Gs1al & Gs047 & GF4 & GFal & GFc & GFapp &
  GFimg & Gn & Gnl & Gp0 & Gp).
pose proof HC as (HJ & _ & _ & _ & Rsp & R8 & R9 & Rgp & Rtp & _).
pose proof alloc_ceiling_val as Hac.
pose proof (ot_tv (l_pl cx) B1 (sv_c (ot_kd cx op))) as TV. cbv zeta in TV.
destruct TV as (Eser & _ & Elen & _).
change (lc_tag_vals (l_pl cx) B1 (sv_c (ot_kd cx op))) with (ot_tvx cx op B1) in Eser, Elen.
set (len := tg_len (ot_tvx cx op B1)) in *.
assert (Hlen : 3 <= len <= 24) by (rewrite Elen; pose proof (Z.mod_pos_bound (snd (TOP.fuzz_u8_m (l_pl cx)
  (sv_c (ot_kd cx op)))) 22 ltac:(lia)); lia).
set (E := ot_E regs' [w64 SHADOW_OFF; w64 len]).
assert (HEI : img_env VAL A_LIM E) by (unfold E, ot_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs' r)
  by (intros n r Hn; unfold E, ot_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E33 : ew E 33 = w64 len)
  by (unfold E, ot_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs' _ 1)).
pose proof (eq_trans (EE 20%nat 20%bv eq_refl) R20) as E20.
assert (U20 : bv_unsigned (ew E 20) = lc_F cx + 32) by (rewrite E20; apply unsigned_lit_small; lia).
pose proof HOK as (_ & _ & Hcok & _ & _). pose proof (ot_cbl cx op B1 Hcok) as Hcbl.
(* c[24] = len *)
assert (HL24 : val_mem segs (rd W mem') (lc_F cx + 32 + 24) 1 len).
{ destruct (Hcs 24%nat ltac:(rewrite ot_cs_len by exact Hcbl; lia)) as (Hv & _).
  rewrite ot_cs_len24 in Hv by (first [exact Hcbl | lia]). exact Hv. }
(* the start state, for len in [lo, hi] *)
assert (HSg : forall lo hi, lo <= len <= hi -> 0 <= lo -> hi <= 24 -> @st_ok_pi segs VAL (l_fx cx) E (ot_ssD lo hi)
  (restrict (w_H W) (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (BASE + 0x10a0)) mem' (YK11.seg_rom segs)))).
{ intros lo hi Hlh Hlo Hhi. rewrite restrict_mkst_fx.
  apply (@pa_entry_st_ok_full (l_fx cx) rc transportb_listing PI_transportb).
  - unfold E, ot_E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold ot_cD, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    exact (chunk_ok_val segs E _ (lc_F cx + 32) 24 1 (SOff 33 0) len
      (ot_den_atom E 33 len E33 ltac:(lia)) ltac:(change (2 ^ (8 * Z.of_N 1)) with 256; lia) ltac:(lia) HL24).
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold ot_factsD, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U20, E33. unfold w64. rewrite unsigned_lit_small by lia.
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
assert (SHOK : sh_ok segs (SOff 26 0) [] E (rd W mem')) by constructor.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
unfold lc_cfg.
change (w64 (transportb_text + 0x10a0)) with (Z_to_bv 64 (BASE + 0x10a0)).
destruct (Z.eq_dec len 3) as [L3 | L3]; [pose proof (HSg 3 3 ltac:(lia) ltac:(lia) ltac:(lia)) as HS |
  pose proof (HSg 4 24 ltac:(lia) ltac:(lia) ltac:(lia)) as HS].
(* len = 3: `bltu len, 4` to +0x115c, t2 = 0, `j` SYSJ; len >= 4: a3 = 3, SYSL 0 *)
1: paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x1170.
3: paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x10b0.
1, 3: apply awr_ok_x_cons; [|apply awr_ok_x_nil];
  intros a Ha; cbn [ot_cD YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia.
all: pmkst HS; ot_norm HS; apply SRr_ret.
all: assert (KM : forall a, aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem' a)
  by (intros a; apply (aview_eq_of segs); apply HFr; intros (r & Hin & Hr); cbn [ot_ssD ss_mem In] in Hin;
      destruct Hin as [<- | []]; cbn [ot_cD YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia).
all: assert (Q2 : YK11.getr (ms_regs ms) 2 = YK11.getr regs' 2) by ot_same HS EE.
all: assert (Q3 : YK11.getr (ms_regs ms) 3 = YK11.getr regs' 3) by ot_same HS EE.
all: assert (Q4 : YK11.getr (ms_regs ms) 4 = YK11.getr regs' 4) by ot_same HS EE.
all: assert (Q8 : YK11.getr (ms_regs ms) 8 = YK11.getr regs' 8) by ot_same HS EE.
all: assert (Q9 : YK11.getr (ms_regs ms) 9 = YK11.getr regs' 9) by ot_same HS EE.
all: assert (Q18 : YK11.getr (ms_regs ms) 18 = YK11.getr regs' 18) by ot_same HS EE.
all: assert (Q19 : YK11.getr (ms_regs ms) 19 = YK11.getr regs' 19) by ot_same HS EE.
all: assert (Q20 : YK11.getr (ms_regs ms) 20 = YK11.getr regs' 20) by ot_same HS EE.
all: assert (Q21 : YK11.getr (ms_regs ms) 21 = YK11.getr regs' 21) by ot_same HS EE.
all: assert (Q22 : YK11.getr (ms_regs ms) 22 = YK11.getr regs' 22) by ot_same HS EE.
all: assert (Q23 : YK11.getr (ms_regs ms) 23 = YK11.getr regs' 23) by ot_same HS EE.
all: assert (Q24 : YK11.getr (ms_regs ms) 24 = YK11.getr regs' 24) by ot_same HS EE.
all: assert (Q25 : YK11.getr (ms_regs ms) 25 = YK11.getr regs' 25) by ot_same HS EE.
all: assert (Q26 : YK11.getr (ms_regs ms) 26 = YK11.getr regs' 26) by ot_same HS EE.
all: assert (Q27 : YK11.getr (ms_regs ms) 27 = YK11.getr regs' 27) by ot_same HS EE.
all: pose proof (ot_tagc_mk cx op W ly' S' regs' mem' md' e B1 (ms_regs ms) (ms_mem ms) _ HP HB HCOM Htw Hcs
  V64 V16 V8 HRS R20 R24 HJ KM (fun a => apresent_grows _ _ _ a HG) Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q20 Q23 Q24 Q26 Q27) as TAG.
all: pose proof HRS as (R21 & _).
- (* SYSJ *)
  right. unfold lc_st_sysj. exists ly', S', (ms_regs ms), (ms_mem ms). eexists. exists e, B1. cbv zeta.
  split; [reflexivity|]. split; [exact TAG|].
  change (lc_tag_vals (l_pl cx) B1 (sv_c (lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op))))) with (ot_tvx cx op B1).
  assert (Hsys : lc_sys (ot_tvx cx op B1) = false).
  { unfold lc_sys. change (tg_len (ot_tvx cx op B1)) with len. rewrite L3. unfold DSpec.system_at.
    rewrite length_firstn, Hcbl. reflexivity. }
  rewrite Hsys, Eser. split; [|exact (eq_trans Q21 R21)].
  ot_rv HS (Z_to_bv 5 7) X7. exact (eq_trans X7 eq_refl).
- (* SYSL 0 *)
  left. unfold lc_st_sysl. exists ly', S', (ms_regs ms), (ms_mem ms). eexists. exists e, B1. cbv zeta.
  split; [reflexivity|]. split; [exact TAG|].
  change (lc_tag_vals (l_pl cx) B1 (sv_c (lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op))))) with (ot_tvx cx op B1).
  change (tg_len (ot_tvx cx op B1)) with len. rewrite Eser.
  ot_rv HS (Z_to_bv 5 12) X12. ot_rv HS (Z_to_bv 5 13) X13.
  split; [lia|]. split; [lia|].
  split; [intros j Hj; cbn in Hj; lia|].
  split; [exact (eq_trans X12 (ot_den_atom E 33 len E33 ltac:(lia)))|].
  split; [exact (eq_trans X13 eq_refl)|].
  split; [exact (eq_trans Q21 R21)|].
  split; [exact (eq_trans Q22 R22) | exact (eq_trans Q25 R25)].
Qed.

(* ------------------------------------------------------------------ *)
(* 10. The segment                                                     *)
(* ------------------------------------------------------------------ *)

Lemma lc_op4t_ok (K1 : lc_rom_view_stmt B MT XL RLO RHI) : lc_op4t_stmt B MT XL RLO RHI.
Proof.
intros HP cx op W c HB H.
eapply SRr_bind; [exact (ot_runA cx op W c HP HB H)|]. intros W1 c1 _ H1.
eapply SRr_bind; [exact (ot_call_ms cx op W1 c1 HP HB H1)|]. intros W2 c2 _ H2.
eapply SRr_bind; [exact (ot_runB cx op W2 c2 K1 HP HB H2)|]. intros W3 c3 _ H3.
eapply SRr_bind; [exact (ot_runC cx op W3 c3 HP HB H3)|]. intros W4 c4 _ H4.
eapply SRr_bind; [exact (ot_call_mc cx op W4 c4 HP HB H4)|]. intros W5 c5 _ H5.
exact (ot_runD cx op W5 c5 HP HB H5).
Qed.

End op4t.
