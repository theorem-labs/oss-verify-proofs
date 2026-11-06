(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module names changed; 1723 of its 1815 lines of code are new or changed and 938 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_op3a: Lemma lc_op3a_ok : lc_rom_view_stmt -> lc_op3a_stmt
   (lib/A/Prog/LLVMFuzzerTestOneInput_segs.v), the segment OP3A of the image-A walk of LLVMFuzzerTestOneInput,
   offsets +0x5b4 .. +0x96c of the listing lib/A/Prog/DgnTransportList.v (slot k at 0x81264 + 4k), from the cut ARM3
   (lc_st_arm cx op 3) to the cut TICK (lc_st_tick cx op). It takes the kit statement K1 (lc_rom_view_stmt) as its
   argument: the bytes of SCALE are read-only image bytes.

   What the code does (op 3, TOps.v :301-305: scale = SCALE[fuzz_u8 & 3], op_begin, g_now += scale * fuzz_u16):
     +0x5b4 .. +0x5d8, +0x750 .. +0x774   `beqz s7` (no byte left: 0), else the checked one-byte load of the scale
                                          byte at s8 (report 0x82cb4 on the slow path +0x1368) and s8 / s7 past it;
                                          the address of SCALE[byte & 3] and the check of its shadow byte (report
                                          0x82c00);
     +0x778 .. +0x788                     the 8-byte load of the entry into s3, OW into s6, a0 = OW, a1 = 0, a2 = 304;
     +0x78c, +0x790 .. +0x7a0             __asan_memset (OW, 0, 304) and __asan_memset (GOT, 0, 224), op_begin's two
                                          memsets: lp_memset (aintrin_realizes OSet at transport_sigma
                                          TS___asan_memset) through TransportGCg.v gx_intrin_at; both destinations
                                          are rows of G, their shadow is receive_cg.v trans_recv_cells (lp_recv_cells);
     +0x7a4 .. +0x7b4                     OW.desk_off = -1 and M.fail = g_fail_next (s4 - 1076, and M from the spill
                                          at 184(s1));
     +0x7b8 .. +0x7e8, +0x818, +0x938 .. +0x954   the u16: `beqz s7` (no byte left: 0), the checked load of its low
                                          byte (report 0x82ccc, slow path +0x138c) and, with two or more bytes left,
                                          of its high byte (report 0x82cf0, slow path +0x13ec);
     +0x958 .. +0x96c                     g_now += u16 * scale, through g_now's page spilled at 176(s1).
   Every checked load reads a byte of the input block (AR_shadow_law: its shadow marks the byte usable) or of SCALE (a
   zero-shadow row of transport_cells), so no report call is reached: each run of the token engine
   (TransportGRunA.v paj_run_x / paj_run_to_x) ends at its target pc.

   The world: op_begin's world (TCb.v op_begin_m) followed by the g_now store (lc_tick_w) is op3_wF of the arm's
   world, and the stores are bytes of G, so the world relation follows by TWorldG.v tw_upd. The core carries over by
   LLVMFuzzerTestOneInput_st.v lc_core_kept: the segment writes only bytes of G and the memsets' window below sp1. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0 ACfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TOps TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module ACells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 0. Symbolic values and states                                       *)
(* ------------------------------------------------------------------ *)

(* A register of a symbolic state replaced by another value of the same denotation (DgnTransportPaLib.v
   st_ok_pi_pin_reg' for any value). *)
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {L : ptable tsym} {PL : PAListing L} {PI : PAImg L}.
Lemma op3_set_reg : forall E ss ms (r : bv 5) v,
  st_ok_pi pa_segs pa_val E ss ms -> getr (ms_regs ms) r = sv_denot E v -> bv_eqb r 0 = false ->
  st_ok_pi pa_segs pa_val E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r v) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r v HS Hr Hr0. unfold st_ok_pi, abs_ss, setpc in *.
cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
apply (st_ok_regs pa_segs E (mkSST (pa_val A_TEXT + ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss)
  (ss_facts ss)) ms (sr_set (ss_regs ss) r v) HS).
intros rr. cbn [ss_regs]. destruct (decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. pose proof (st_ok_reg pa_segs E _ ms r HS) as Hq. cbn [ss_regs] in Hq.
  rewrite <- Hq, Hr. reflexivity.
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.
End g.

Lemma op3_den_atom : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma op3_den_off : forall E n c v, bv_unsigned (ew E n) = v -> sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E n c v H. cbn [sv_denot]. rewrite H. reflexivity. Qed.
Lemma op3_U_off : forall E n c v, bv_unsigned (ew E n) = v -> 0 <= v + c < 2 ^ 64 -> U E (SOff n c) = v + c.
Proof. intros E n c v H Hr. rewrite U_SOff, H. apply zcanon_id. unfold M64. lia. Qed.

(* The address of SCALE's entry `andi a0, a0, 3; slli a0, a0, 3; add a0, a1, a0` (+0x5d4, +0x754, +0x760). *)
Lemma op3_den_scale : forall E sb, ew E 32 = Z_to_bv 64 sb -> 0 <= sb < 256 ->
  bv_unsigned (ew E (A_OBJ 14)) = TRANS_SCALE ->
  sv_denot E (SAlu ALU_ADD (SOff (A_OBJ 14) 0) (SAlu ALU_SLL (SAlu ALU_AND (SOff 32 0) (SLit 3)) (SLit 3))) =
  Z_to_bv 64 (TRANS_SCALE + 8 * (sb mod 4)).
Proof.
intros E sb H32 Hsb H14. cbn [sv_denot alu64 alu]. rewrite H32, H14, !Z.add_0_r.
apply bv_eq.
rewrite bv_add_unsigned, bv_shiftl_unsigned, !bv_and_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
replace (sb mod 2 ^ 64 mod 2 ^ 64) with sb by (rewrite !(Z.mod_small sb (2 ^ 64)) by lia; reflexivity).
change (3 mod 2 ^ 64) with 3. change (63 mod 2 ^ 64) with 63. change (Z.land 3 63) with 3.
replace (Z.land sb 3) with (sb mod 4) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity).
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.mod_pos_bound sb 4 ltac:(lia)) as Hm.
unfold TRANS_SCALE. rewrite (Z.mod_small (sb mod 4 * 8) (2 ^ 64)) by lia.
rewrite (Z.mod_small 135168 (2 ^ 64)) by lia. f_equal. lia.
Qed.

(* `slli x, 8; or y`: the u16 the code assembles (m_rx_seg_head.v hd_den_or8's form). *)
Lemma op3_lor8 : forall x y, 0 <= x < 256 -> 0 <= y < 256 -> Z.lor (x * 2 ^ 8) y = x * 2 ^ 8 + y.
Proof.
intros x y Hx Hy. symmetry. apply Z.add_nocarry_lor.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z_lt_le_dec i 8) as [Hl|Hl].
- replace (x * 2 ^ 8) with (Z.shiftl x 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  rewrite Z.shiftl_spec by lia. rewrite (Z.testbit_neg_r x (i - 8)) by lia. reflexivity.
- rewrite <- (Z.mod_small y (2 ^ 8)) by lia. rewrite Z.mod_pow2_bits_high by lia.
  apply andb_false_r.
Qed.
Lemma op3_den_or8 : forall (E : env) (j k : nat) (x y : Z),
  ew E j = Z_to_bv 64 x -> ew E k = Z_to_bv 64 y -> 0 <= x < 256 -> 0 <= y < 256 ->
  sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SOff j 0) (SLit 8)) (SOff k 0)) = Z_to_bv 64 (x * 2 ^ 8 + y).
Proof.
intros E j k x y Hj Hk Hx Hy.
cbn [sv_denot alu64 alu].
rewrite Hj, Hk. rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r.
apply bv_eq.
rewrite bv_or_unsigned, bv_shiftl_unsigned, bv_and_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite (Z.mod_small x (2 ^ 64)) by lia.
rewrite (Z.mod_small y (2 ^ 64)) by lia.
rewrite (Z.mod_small 8 (2 ^ 64)) by lia.
rewrite (Z.mod_small 63 (2 ^ 64)) by lia.
change (Z.land 8 63) with 8.
rewrite Z.shiftl_mul_pow2 by lia.
rewrite (Z.mod_small (x * 2 ^ 8) (2 ^ 64)) by lia.
rewrite (Z.mod_small (x * 2 ^ 8 + y) (2 ^ 64)) by lia.
apply op3_lor8; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 1. The SCALE table (+0x75c: `auipc / addi` of SCALE, object 14)      *)
(* ------------------------------------------------------------------ *)

Lemma op3_scale_in_ro : forall a, TRANS_SCALE <= a < TRANS_SCALE + 32 -> trans_in_ro_rd a.
Proof.
intros a Ha. unfold trans_in_ro_rd. apply Exists_exists. exists (TRANS_SCALE, 32). split.
- unfold TRANS_RO_RD, TRANS_RO_GLOBALS. cbn [app In]. do 4 right. left. reflexivity.
- unfold in_zr. cbn [fst snd]. lia.
Qed.

(* SCALE's four 8-byte entries, read at a memory where the read-only view holds (K1). *)
Lemma op3_scale_rom : forall (W : world tfibsegs) mem, trans_rom_view_rd W mem -> forall i, (i < 4)%nat ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (TRANS_SCALE + 8 * Z.of_nat i) 8
    (nth i TOP.LLVMFuzzerTestOneInput_SCALE 0).
Proof.
intros W mem HR i Hi k Hk.
assert (Ha : trans_in_ro_rd (TRANS_SCALE + 8 * Z.of_nat i + Z.of_nat k)) by (apply op3_scale_in_ro; lia).
pose proof (HR _ Ha) as Hv.
assert (Hin : In (TRANS_SCALE, flat_map (TW.put 8) TOP.LLVMFuzzerTestOneInput_SCALE) lc_rom_tab)
  by (unfold lc_rom_tab; do 8 right; left; reflexivity).
assert (Hl : (8 * i + k < length (flat_map (TW.put 8) TOP.LLVMFuzzerTestOneInput_SCALE))%nat)
  by (change (length (flat_map (TW.put 8) TOP.LLVMFuzzerTestOneInput_SCALE)) with 32%nat; lia).
pose proof (lc_rom_bytes _ _ Hin (8 * i + k) Hl) as Hr.
replace (TRANS_SCALE + Z.of_nat (8 * i + k)) with (TRANS_SCALE + 8 * Z.of_nat i + Z.of_nat k) in Hr by lia.
rewrite Hr in Hv. unfold aview in Hv.
destruct (YP09.mbyte tfibsegs (mrestrict (w_H W) mem) (TRANS_SCALE + 8 * Z.of_nat i + Z.of_nat k)) as [b|] eqn:Eb;
  [|discriminate Hv].
cbn [option_map] in Hv. injection Hv as Hv.
f_equal. apply bv_eq. rewrite Hv, Z_to_bv_unsigned. clear - Hi Hk.
do 4 (destruct i as [|i]; [do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); lia|]). lia.
Qed.

(* SCALE's 32 bytes are addressable at every AR state: a zero-shadow row of transport_cells. *)
Lemma op3_scale_ra : forall {rc : YM05.RunCeil} B ly S (W : world tfibsegs) mem md, @AR rc tfibsegs B ly S W mem md ->
  decode_zshadow_at B TRANS_SCALE (TRANS_SCALE + 32) ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF TRANS_SCALE 32.
Proof.
intros rc B ly S W mem md HAR HZ x Hx.
pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
exists 0. split; [|left; reflexivity].
assert (Hz := decode_zshadow_rd B ly S W mem md TRANS_SCALE (TRANS_SCALE + 32) (8 * (x / 8)) HAR
  ltac:(rewrite Z.mul_comm; apply Z_mod_mult) ltac:(unfold TRANS_SCALE in *; lia) ltac:(unfold TRANS_SCALE in *; lia) HZ).
unfold shadow_of_addr. replace (SHADOW_OFF + x / 8) with (ACells.shadow_addr (8 * (x / 8))); [exact Hz|].
unfold ACells.shadow_addr, ACells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The symbolic state at the arm (+0x5b4)                           *)
(* ------------------------------------------------------------------ *)

(* Atoms: 0 .. 31 the registers at the arm, 32 the scale byte (read only when bytes are left). Regions: the scale byte
   at s8 (n1 > 0) and SCALE's 32 bytes (object 14); both read only. The shadow entries are the same two ranges; s10
   (atom 26) is the shadow base. *)
Definition op3_scale_r : YP09.region := YP09.mkRegion (Some (A_OBJ 14)) 0 32 0 0
  [YP09.mkChunk 0 (CVal 8 (SLit 1)); YP09.mkChunk 8 (CVal 8 (SLit 1000));
   YP09.mkChunk 16 (CVal 8 (SLit 100000)); YP09.mkChunk 24 (CVal 8 (SLit 1000000))].
Definition op3_in1_r : YP09.region := YP09.mkRegion (Some 24%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition op3_fa1 : facts := mkFacts
  [(26%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (24%nat, PTR 0); (32%nat, mkAF 0 255 0);
   (A_OBJ 14, mkAF TRANS_SCALE TRANS_SCALE 5)] [] [].
Definition op3_ss1 : sstate := mkSS 0x5b4 sr_atoms [op3_in1_r; op3_scale_r] None op3_fa1.
Definition op3_ss0 : sstate := mkSS 0x5b4 sr_atoms [op3_scale_r] None op3_fa1.
Definition op3_SH1 : list shent := [mkSHE 24 0 1; mkSHE (A_OBJ 14) 0 32].
Definition op3_SH0 : list shent := [mkSHE (A_OBJ 14) 0 32].
Definition op3_Bx : sv := SOff 26 0.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Definition op3_E1 (regs : bvmap 5 word) (sb : Z) : env := Eimg (PI := PI_transport) (Ereg regs [Z_to_bv 64 sb]).

Lemma op3_E1_reg : forall regs sb n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (op3_E1 regs sb) n = YK11.getr regs r.
Proof. intros regs sb n r Hn. unfold op3_E1. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma op3_E1_32 : forall regs sb, ew (op3_E1 regs sb) 32 = Z_to_bv 64 sb.
Proof. intros regs sb. unfold op3_E1. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma op3_E1_14 : forall regs sb, bv_unsigned (ew (op3_E1 regs sb) (A_OBJ 14)) = TRANS_SCALE.
Proof. intros regs sb. unfold op3_E1. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). vm_compute. reflexivity. Qed.

Lemma op3_scale_r_ok : forall (W : world tfibsegs) mem E, bv_unsigned (ew E (A_OBJ 14)) = TRANS_SCALE ->
  trans_rom_view_rd W mem -> region_ok tfibsegs E (mrestrict (w_H W) mem) op3_scale_r.
Proof.
intros W mem E U14 HR. unfold op3_scale_r, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U14.
split; [unfold TRANS_SCALE; lia|]. split; [unfold TRANS_SCALE; lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- apply (chunk_ok_val tfibsegs _ _ TRANS_SCALE 0 8 (SLit 1) 1); [reflexivity | cbn; lia | lia |].
  exact (op3_scale_rom W mem HR 0 ltac:(lia)).
- apply (chunk_ok_val tfibsegs _ _ TRANS_SCALE 8 8 (SLit 1000) 1000); [reflexivity | cbn; lia | lia |].
  exact (op3_scale_rom W mem HR 1 ltac:(lia)).
- apply (chunk_ok_val tfibsegs _ _ TRANS_SCALE 16 8 (SLit 100000) 100000); [reflexivity | cbn; lia | lia |].
  exact (op3_scale_rom W mem HR 2 ltac:(lia)).
- apply (chunk_ok_val tfibsegs _ _ TRANS_SCALE 24 8 (SLit 1000000) 1000000); [reflexivity | cbn; lia | lia |].
  exact (op3_scale_rom W mem HR 3 ltac:(lia)).
Qed.

(* The state at the arm, with the scale byte (n1 > 0). *)
Lemma op3_seat1 : forall (W : world tfibsegs) regs mem sb s8v,
  YK11.getr regs 26 = w64 SHADOW_OFF -> YK11.getr regs 24 = w64 s8v -> 4096 <= s8v <= 140737479966720 ->
  (s8v + 1 <= TRANS_SCALE \/ TRANS_SCALE + 32 <= s8v) ->
  0 <= sb < 256 -> val_mem tfibsegs (mrestrict (w_H W) mem) s8v 1 sb -> trans_rom_view_rd W mem ->
  st_ok_pi tfibsegs VAL (op3_E1 regs sb) op3_ss1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 0x5b4)) mem (YK11.seg_rom tfibsegs))).
Proof.
intros W regs mem sb s8v R26 R24 H8 Hd Hsb HV HR.
set (E := op3_E1 regs sb).
assert (U24 : bv_unsigned (ew E 24) = s8v)
  by (unfold E; rewrite (op3_E1_reg regs sb 24 24%bv eq_refl), R24; unfold w64; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF)
  by (unfold E; rewrite (op3_E1_reg regs sb 26 26%bv eq_refl), R26; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (E32 : ew E 32 = Z_to_bv 64 sb) by exact (op3_E1_32 regs sb).
assert (U14 : bv_unsigned (ew E (A_OBJ 14)) = TRANS_SCALE) by exact (op3_E1_14 regs sb).
rewrite restrict_mkst_fx. unfold op3_ss1.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold op3_in1_r, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U24. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ s8v 0 1 (SOff 32 0) sb);
      [exact (op3_den_atom E 32 sb E32) | cbn; lia | lia | rewrite Z.add_0_r; exact HV].
  + exact (op3_scale_r_ok W mem E U14 HR).
- apply pairwise_disjoint_of_extents. unfold extent_of_region, op3_in1_r, op3_scale_r.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U24, U14.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; try exact I; lia.
- unfold op3_fa1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
  rewrite U26, U24, U14, E32, unsigned_lit_small by lia.
  change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | unfold TRANS_SCALE; reflexivity].
Qed.

(* The state at the arm, no byte left (n1 = 0). *)
Lemma op3_seat0 : forall (W : world tfibsegs) regs mem s8v,
  YK11.getr regs 26 = w64 SHADOW_OFF -> YK11.getr regs 24 = w64 s8v -> 4096 <= s8v <= 140737479966720 ->
  trans_rom_view_rd W mem ->
  st_ok_pi tfibsegs VAL (op3_E1 regs 0) op3_ss0
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 0x5b4)) mem (YK11.seg_rom tfibsegs))).
Proof.
intros W regs mem s8v R26 R24 H8 HR.
set (E := op3_E1 regs 0).
assert (U24 : bv_unsigned (ew E 24) = s8v)
  by (unfold E; rewrite (op3_E1_reg regs 0 24 24%bv eq_refl), R24; unfold w64; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF)
  by (unfold E; rewrite (op3_E1_reg regs 0 26 26%bv eq_refl), R26; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (E32 : ew E 32 = Z_to_bv 64 0) by exact (op3_E1_32 regs 0).
assert (U14 : bv_unsigned (ew E (A_OBJ 14)) = TRANS_SCALE) by exact (op3_E1_14 regs 0).
rewrite restrict_mkst_fx. unfold op3_ss0.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [exact (op3_scale_r_ok W mem E U14 HR) | apply Forall_nil].
- cbn [pairwise_disjoint all_disjoint]. tauto.
- unfold op3_fa1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
  rewrite U26, U24, U14, E32, unsigned_lit_small by lia.
  change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | unfold TRANS_SCALE; reflexivity].
Qed.

(* The shadow entries of the arm's state. *)
Lemma op3_shok_scale : forall B ly S (W : world tfibsegs) mem md E, @AR rc tfibsegs B ly S W mem md ->
  decode_zshadow_at B TRANS_SCALE (TRANS_SCALE + 32) ->
  bv_unsigned (ew E 26) = SHADOW_OFF -> bv_unsigned (ew E (A_OBJ 14)) = TRANS_SCALE ->
  shent_ok tfibsegs op3_Bx E (mrestrict (w_H W) mem) (mkSHE (A_OBJ 14) 0 32).
Proof.
intros B ly S W mem md E HAR HZ U26 U14.
apply (shent_ok_of_range tfibsegs (w_H W) mem E op3_Bx (A_OBJ 14) TRANS_SCALE 32 TRANS_SCALE 0 32
  (op3_scale_ra B ly S W mem md HAR HZ)).
- unfold op3_Bx. rewrite (op3_U_off E 26 0 SHADOW_OFF U26) by (unfold SHADOW_OFF; lia). lia.
- rewrite (op3_U_off E (A_OBJ 14) 0 TRANS_SCALE U14) by (unfold TRANS_SCALE; lia). lia.
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold TRANS_SCALE, SHADOW_OFF in *. lia.
Qed.

Lemma op3_shok1 : forall B ly S (W : world tfibsegs) mem md regs sb s8v, @AR rc tfibsegs B ly S W mem md ->
  decode_zshadow_at B TRANS_SCALE (TRANS_SCALE + 32) ->
  YK11.getr regs 26 = w64 SHADOW_OFF -> YK11.getr regs 24 = w64 s8v -> 0 <= s8v < 2 ^ 63 ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF s8v 1 ->
  ~ (SHADOW_OFF <= s8v < SHADOW_OFF + 17592186044416) ->
  sh_ok tfibsegs op3_Bx op3_SH1 (op3_E1 regs sb) (mrestrict (w_H W) mem).
Proof.
intros B ly S W mem md regs sb s8v HAR HZ R26 R24 H8 HRA Hap.
set (E := op3_E1 regs sb).
assert (U24 : bv_unsigned (ew E 24) = s8v)
  by (unfold E; rewrite (op3_E1_reg regs sb 24 24%bv eq_refl), R24; unfold w64; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF)
  by (unfold E; rewrite (op3_E1_reg regs sb 26 26%bv eq_refl), R26; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
unfold sh_ok, op3_SH1. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range tfibsegs (w_H W) mem E op3_Bx 24 s8v 1 s8v 0 1 HRA).
  + unfold op3_Bx. rewrite (op3_U_off E 26 0 SHADOW_OFF U26) by (unfold SHADOW_OFF; lia). lia.
  + rewrite (op3_U_off E 24 0 s8v U24) by lia. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. replace x with s8v by lia. exact Hap.
- exact (op3_shok_scale B ly S W mem md E HAR HZ U26 (op3_E1_14 regs sb)).
Qed.

Lemma op3_shok0 : forall B ly S (W : world tfibsegs) mem md regs, @AR rc tfibsegs B ly S W mem md ->
  decode_zshadow_at B TRANS_SCALE (TRANS_SCALE + 32) -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  sh_ok tfibsegs op3_Bx op3_SH0 (op3_E1 regs 0) (mrestrict (w_H W) mem).
Proof.
intros B ly S W mem md regs HAR HZ R26.
assert (U26 : bv_unsigned (ew (op3_E1 regs 0) 26) = SHADOW_OFF)
  by (rewrite (op3_E1_reg regs 0 26 26%bv eq_refl), R26; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
unfold sh_ok, op3_SH0. constructor; [|constructor].
exact (op3_shok_scale B ly S W mem md _ HAR HZ U26 (op3_E1_14 regs 0)).
Qed.
End s.

(* ------------------------------------------------------------------ *)
(* 3. +0x5b4 .. +0x78c: the scale byte, SCALE's entry, the call of __asan_memset (OW) *)
(* ------------------------------------------------------------------ *)

(* A run whose regions have no write window changes no byte. *)
Lemma op3_ro_frame : forall E rs (m m' : word -> option byte),
  Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs -> frame_of E rs m m' -> forall x, m' x = m x.
Proof.
intros E rs m m' Hrs H x. apply H. intros (r & Hr & Ha).
rewrite Forall_forall in Hrs. pose proof (Hrs r Hr) as Hw. lia.
Qed.

Lemma op3_bv_eqb0 : forall v, 0 <= v < 2 ^ 64 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof. intros v Hv. unfold bv_eqb. rewrite !unsigned_lit_small by lia. reflexivity. Qed.

(* The value of register r in a symbolic state's machine: its symbolic value, computed. *)
Ltac op3_rd HS r H :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?msx) =>
      pose proof (st_ok_pi_restrict_reg Hh Ex ss msx r HS) as H;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H
  | st_ok ?sg ?Ex ?ss (restrict ?Hh ?msx) =>
      pose proof (st_ok_restrict_reg sg Hh Ex ss msx r HS) as H;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H
  end.

(* A run of read-only regions keeps the memory. *)
Ltac op3_ro HF M :=
  lazymatch type of HF with frame_of ?Ex ?rs ?m ?m' =>
    let rs' := eval vm_compute in rs in
    assert (M : forall x, m' x = m x);
    [ apply (op3_ro_frame Ex rs' m m'); [repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil | exact HF] |]
  end.

Ltac op3_awr_ro :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
     cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

Section a. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma op3_vals : BASE = transport_text /\
  VAL (A_OBJ 12) = TA_OW /\
  VAL (A_OBJ 13) = TA_GOT /\
  VAL (A_OBJ 14) = TRANS_SCALE /\
  transport_sigma TS___asan_memset = 0x5284c.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* The walk's G journal from the slot's entry with the frame owned (the first conjunct of lc_core), at a state of the
   segment; FP is the journal's, whatever lc_core puts there. *)
Definition op3_J (FP : list (Z * Z)) (cx : lcx) (ly : alayout) (S : astate) (W : world segs)
    (mem : word -> option byte) (md : Model) (e : Z) : Prop :=
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] LLVMF_STK (lc_sp0 cx) FP (l_ly cx) (l_S cx)
    (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly S W mem md e.

(* The registers the segment does not write: sp, gp, tp, s0, s1, s2, s4, s5, s9, s10, s11. *)
Definition op3_keep : list (bv 5) := [2; 3; 4; 8; 9; 18; 20; 21; 25; 26; 27]%bv.
Definition op3_kept (regs0 regs : bvmap 5 word) : Prop :=
  forall r, In r op3_keep -> YK11.getr regs r = YK11.getr regs0 r.

(* The call of __asan_memset (OW, 0, 304) at +0x78c: s3 = SCALE's entry, s6 = OW, s8 / s7 the cursor after the scale
   byte; the memory is the arm's. *)
Definition op3_PA (FP : list (Z * Z)) (cx : lcx) (ly : alayout) (S : astate) (W : world segs) (regs0 : bvmap 5 word)
    (mem : word -> option byte) (e scale o2 n2 : Z) : world segs -> config -> Prop :=
  fun W2 c2 => W2 = W /\ exists regs2 md2,
    c2 = mkCfg (@YK11.mkst (l_fx cx) regs2 (Z_to_bv 64 (transport_sigma TS___asan_memset)) mem (YK11.seg_rom segs)) md2 /\
    op3_J FP cx ly S W mem md2 e /\
    YK11.getr regs2 10 = w64 TA_OW /\ YK11.getr regs2 11 = w64 0 /\ YK11.getr regs2 12 = w64 304 /\
    YK11.getr regs2 1 = Z_to_bv 64 (BASE + 0x790) /\
    YK11.getr regs2 19 = w64 scale /\ YK11.getr regs2 22 = w64 TA_OW /\
    YK11.getr regs2 24 = w64 (l_p cx + o2) /\ YK11.getr regs2 23 = w64 n2 /\
    op3_kept regs0 regs2.

Lemma op3_den_img : forall E j, img_env VAL A_LIM E -> (A_TEXT <= j < A_LIM)%nat ->
  sv_denot E (SOff j 0) = Z_to_bv 64 (VAL j).
Proof. intros E j HE Hj. cbn [sv_denot]. rewrite (HE j Hj), Z.add_0_r. reflexivity. Qed.

Lemma op3_A1n : forall FP cx ly S W regs mem md e (o0 n0 sb : Z),
  AR_laws segs B -> W_journalG.gx_ok segs B TG.G_HARNESS ->
  decode_zshadow_at B TRANS_SCALE (TRANS_SCALE + 32) ->
  op3_J FP cx ly S W mem md e ->
  trans_rom_view_rd W mem ->
  YK11.getr regs 26 = w64 SHADOW_OFF ->
  YK11.getr regs 25 = w64 (l_p cx + o0) -> YK11.getr regs 27 = w64 n0 ->
  YK11.getr regs 24 = w64 (l_p cx + (o0 + 1)) -> YK11.getr regs 23 = w64 (n0 - 1) ->
  2 <= n0 -> 0 <= o0 -> 4096 <= l_p cx -> l_p cx + o0 + n0 <= 140737479966720 ->
  (l_p cx + o0 + 2 <= TRANS_SCALE \/ TRANS_SCALE + 32 <= l_p cx + o0 + 1) ->
  0 <= sb < 256 -> val_mem segs (mrestrict (w_H W) mem) (l_p cx + (o0 + 1)) 1 sb ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (l_p cx + (o0 + 1)) 1 ->
  ~ (SHADOW_OFF <= l_p cx + (o0 + 1) < SHADOW_OFF + 17592186044416) ->
  SRr segs W (lc_cfg cx 0x5b4 regs mem md)
    (op3_PA FP cx ly S W regs mem e (nth (Z.to_nat (sb mod 4)) TOP.LLVMFuzzerTestOneInput_SCALE 0) (o0 + 2) (n0 - 2)).
Proof.
intros FP cx ly S W regs mem md e o0 n0 sb LAWS HGX HZ HJ HR R26 R25 R27 R24 R23 Hn0 Ho0 Hp Hpn Hd Hsb HV HRA Hap.
pose proof (W_journalG.ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
pose proof (@op3_seat1 (l_fx cx) rc W regs mem sb (l_p cx + (o0 + 1)) R26 R24 ltac:(lia) ltac:(lia) Hsb HV HR) as HS.
pose proof (op3_shok1 B ly S W mem md regs sb (l_p cx + (o0 + 1)) HAR HZ R26 R24 ltac:(lia) HRA Hap) as SHOK.
set (E := op3_E1 regs sb) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (unfold E, op3_E1; apply Eimg_env).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF)
  by (unfold E; rewrite (op3_E1_reg regs sb 26 26%bv eq_refl), R26; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (E23 : ew E 23 = Z_to_bv 64 (n0 - 1)) by (unfold E; rewrite (op3_E1_reg regs sb 23 23%bv eq_refl); exact R23).
assert (E25 : ew E 25 = Z_to_bv 64 (l_p cx + o0)) by (unfold E; rewrite (op3_E1_reg regs sb 25 25%bv eq_refl); exact R25).
assert (E27 : ew E 27 = Z_to_bv 64 n0) by (unfold E; rewrite (op3_E1_reg regs sb 27 27%bv eq_refl); exact R27).
pose proof (op3_E1_32 regs sb) as E32. fold E in E32.
pose proof (op3_E1_14 regs sb) as U14. fold E in U14.
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_branch (l_fx cx) rc transport_listing PI_transport) as BR.
unfold lc_cfg.
change (w64 (transport_text + 0x5b4)) with (Z_to_bv 64 (BASE + 0x5b4)).
unfold op3_J in HJ.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* `beqz s7` taken: refuted, n1 = n0 - 1 > 0 *)
  exfalso. cbn [branch_taken] in Hc. rewrite (op3_den_atom E 23 (n0 - 1) E23) in Hc. cbn [sv_denot] in Hc.
  rewrite op3_bv_eqb0 in Hc by lia. apply Z.eqb_eq in Hc. lia.
- clear Hc.
  (* run 1, +0x5b8 .. +0x778: the checked load of the scale byte, SCALE's entry and the check of its shadow byte;
     it stops at the 8-byte load of the entry, whose address is open in the scale byte *)
  paj_run_tok RUN HS HJ SHOK Bspan.
  + unfold op3_Bx. rewrite (op3_U_off E 26 0 SHADOW_OFF U26) by (unfold SHADOW_OFF; lia). rewrite Z.add_0_r.
    unfold U. change (SOff 255 0) with (SOff (A_OBJ 14) 0). rewrite (op3_den_scale E sb E32 Hsb U14).
    pose proof (Z.mod_pos_bound sb 4 ltac:(lia)) as Hm.
    rewrite unsigned_lit_small by (unfold TRANS_SCALE; lia).
    exact (range_addressable_sub (aview segs (w_H W) mem) SHADOW_OFF TRANS_SCALE 32 (TRANS_SCALE + 8 * (sb mod 4)) 8
      (op3_scale_ra B ly S W mem md HAR HZ) ltac:(lia) ltac:(lia)).
  + op3_awr_ro.
  + lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (E1 := Ex) in * end.
    assert (E1lo : forall n, (n < 1024)%nat -> ew E1 n = ew E n)
      by (intros n Hn; unfold E1; repeat rewrite ew_ewset_other by lia; reflexivity).
    op3_rd HS (10%bv : bv 5) H10. change (SOff 255 0) with (SOff (A_OBJ 14) 0) in H10.
    rewrite (op3_den_scale E1 sb ltac:(rewrite E1lo by lia; exact E32) Hsb
      ltac:(rewrite E1lo by (unfold A_OBJ; lia); exact U14)) in H10.
    op3_ro HF M1.
    assert (Hk4 : sb mod 4 = 0 \/ sb mod 4 = 1 \/ sb mod 4 = 2 \/ sb mod 4 = 3)
      by (pose proof (Z.mod_pos_bound sb 4 ltac:(lia)); lia).
    pose proof (op3_set_reg E1 _ _ 10%bv (SOff (A_OBJ 14) (8 * (sb mod 4))) HS
      ltac:(etransitivity; [exact H10|]; symmetry; apply (op3_den_off E1 (A_OBJ 14) _ TRANS_SCALE);
            rewrite E1lo by (unfold A_OBJ; lia); exact U14) eq_refl) as HS1.
    clear HS H10.
    destruct Hk4 as [Hk|[Hk|[Hk|Hk]]]; rewrite Hk in HS1 |- *.
    all: lazymatch type of HS1 with st_ok_pi ?a ?b ?c ?ss ?d =>
           let ss' := eval vm_compute in ss in change ss with ss' in HS1 end.
    (* run 2, +0x778 .. +0x78c: the load of SCALE's entry, OW into s6 and the call *)
    all: paj_run_tok RUN HS1 HJ SHOK Bspan; [op3_awr_ro|].
    all: lazymatch type of HS1 with st_ok _ ?Ex _ _ => set (E2 := Ex) in * end.
    all: assert (E2lo : forall n, (n < 1024)%nat -> ew E2 n = ew E n)
           by (intros n Hn; unfold E2, E1; repeat rewrite ew_ewset_other by lia; reflexivity).
    all: op3_ro HF0 M2.
    all: assert (EM : ms_mem ms0 = mem) by (apply functional_extensionality; intros x; rewrite M2, M1; reflexivity).
    all: pose proof op3_vals as (VT & V12 & _ & _ & _).
    all: assert (D12 : sv_denot E2 (SOff (A_OBJ 12) 0) = w64 TA_OW)
           by (rewrite (op3_den_img E2 (A_OBJ 12) HEI1 ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), V12; reflexivity).
    all: assert (KR : forall r, In r op3_keep -> YK11.getr (ms_regs ms0) r = YK11.getr regs r).
    all: try (intros r Hr; refine (regs_kept_of_st_ok tfibsegs E2 _ (restrict (w_H W) ms0) regs [Z_to_bv 64 sb]
               op3_keep HS1 _ ltac:(vm_compute; reflexivity) r Hr);
              split; [intros n Hn; rewrite E2lo by lia; unfold E, op3_E1; rewrite Eimg_low by (unfold A_TEXT; lia);
                      reflexivity | reflexivity]).
    all: op3_rd HS1 (10%bv : bv 5) X10; op3_rd HS1 (11%bv : bv 5) X11; op3_rd HS1 (12%bv : bv 5) X12;
         op3_rd HS1 (1%bv : bv 5) X1; op3_rd HS1 (19%bv : bv 5) X19; op3_rd HS1 (22%bv : bv 5) X22;
         op3_rd HS1 (24%bv : bv 5) X24; op3_rd HS1 (23%bv : bv 5) X23.
    all: pmkst HS1; apply SRr_ret; unfold op3_PA; split; [reflexivity|].
    all: exists (ms_regs ms0), (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md) mat md)) mat0
                                 (with_vm_backing (m_vm_lazy md) mat md)).
    all: split; [rewrite EM; reflexivity|].
    all: split; [unfold op3_J; rewrite <- EM; exact HJ|].
    all: split; [rewrite X10; exact D12|].
    all: split; [rewrite X11; reflexivity|].
    all: split; [rewrite X12; reflexivity|].
    all: split; [rewrite X1; apply codeptr_val; exact HEI1|].
    all: split; [rewrite X19; reflexivity|].
    all: split; [rewrite X22; exact D12|].
    all: split; [rewrite X24; rewrite (op3_den_off E2 25 2 (l_p cx + o0)) by
           (rewrite E2lo by lia; rewrite E25; apply unsigned_lit_small; lia); unfold w64; f_equal; lia|].
    all: split; [rewrite X23; rewrite (op3_den_off E2 27 (-2) n0) by
           (rewrite E2lo by lia; rewrite E27; apply unsigned_lit_small; lia); unfold w64; f_equal; lia|].
    all: exact KR.
Qed.


Lemma op3_A1z : forall FP cx ly S W regs mem md e (o1 : Z),
  AR_laws segs B -> W_journalG.gx_ok segs B TG.G_HARNESS ->
  decode_zshadow_at B TRANS_SCALE (TRANS_SCALE + 32) ->
  op3_J FP cx ly S W mem md e ->
  trans_rom_view_rd W mem ->
  YK11.getr regs 26 = w64 SHADOW_OFF ->
  YK11.getr regs 24 = w64 (l_p cx + o1) -> YK11.getr regs 23 = w64 0 ->
  4096 <= l_p cx + o1 <= 140737479966720 ->
  SRr segs W (lc_cfg cx 0x5b4 regs mem md) (op3_PA FP cx ly S W regs mem e 1 o1 0).
Proof.
intros FP cx ly S W regs mem md e o1 LAWS HGX HZ HJ HR R26 R24 R23 Hp.
pose proof (W_journalG.ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
pose proof (@op3_seat0 (l_fx cx) rc W regs mem (l_p cx + o1) R26 R24 Hp HR) as HS.
pose proof (op3_shok0 B ly S W mem md regs HAR HZ R26) as SHOK.
set (E := op3_E1 regs 0) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (unfold E, op3_E1; apply Eimg_env).
assert (E23 : ew E 23 = Z_to_bv 64 0) by (unfold E; rewrite (op3_E1_reg regs 0 23 23%bv eq_refl); exact R23).
assert (E24 : ew E 24 = Z_to_bv 64 (l_p cx + o1)) by (unfold E; rewrite (op3_E1_reg regs 0 24 24%bv eq_refl); exact R24).
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_branch (l_fx cx) rc transport_listing PI_transport) as BR.
unfold lc_cfg.
change (w64 (transport_text + 0x5b4)) with (Z_to_bv 64 (BASE + 0x5b4)).
unfold op3_J in HJ.
psrr_branch_tok RUN BR HS SHOK Bspan.
2: { (* `beqz s7` not taken: refuted, n1 = 0 *)
  exfalso. cbn [branch_taken] in Hc. rewrite (op3_den_atom E 23 0 E23) in Hc. cbn [sv_denot] in Hc.
  rewrite op3_bv_eqb0 in Hc by lia. discriminate Hc. }
clear Hc.
(* +0x750 .. +0x78c: a0 = 0, SCALE[0], OW into s6 and the call *)
paj_run_tok RUN HS HJ SHOK Bspan; [op3_awr_ro|].
lazymatch type of HS with st_ok _ ?Ex _ _ => set (E2 := Ex) in * end.
assert (E2lo : forall n, (n < 1024)%nat -> ew E2 n = ew E n)
  by (intros n Hn; unfold E2; repeat rewrite ew_ewset_other by lia; reflexivity).
op3_ro HF M1.
assert (EM : ms_mem ms = mem) by (apply functional_extensionality; intros x; rewrite M1; reflexivity).
pose proof op3_vals as (VT & V12 & _ & _ & _).
assert (D12 : sv_denot E2 (SOff (A_OBJ 12) 0) = w64 TA_OW)
  by (rewrite (op3_den_img E2 (A_OBJ 12) HEI0 ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), V12; reflexivity).
assert (KR : forall r, In r op3_keep -> YK11.getr (ms_regs ms) r = YK11.getr regs r).
{ intros r Hr. refine (regs_kept_of_st_ok tfibsegs E2 _ (restrict (w_H W) ms) regs [Z_to_bv 64 0]
    op3_keep HS _ ltac:(vm_compute; reflexivity) r Hr).
  split; [intros n Hn; rewrite E2lo by lia; unfold E, op3_E1; rewrite Eimg_low by (unfold A_TEXT; lia);
          reflexivity | reflexivity]. }
op3_rd HS (10%bv : bv 5) X10; op3_rd HS (11%bv : bv 5) X11; op3_rd HS (12%bv : bv 5) X12;
op3_rd HS (1%bv : bv 5) X1; op3_rd HS (19%bv : bv 5) X19; op3_rd HS (22%bv : bv 5) X22;
op3_rd HS (24%bv : bv 5) X24; op3_rd HS (23%bv : bv 5) X23.
pmkst HS; apply SRr_ret; unfold op3_PA; split; [reflexivity|].
exists (ms_regs ms), (with_vm_backing (m_vm_lazy md) mat md).
split; [rewrite EM; reflexivity|].
split; [unfold op3_J; rewrite <- EM; exact HJ|].
split; [rewrite X10; exact D12|].
split; [rewrite X11; reflexivity|].
split; [rewrite X12; reflexivity|].
split; [rewrite X1; apply codeptr_val; exact HEI0|].
split; [rewrite X19; reflexivity|].
split; [rewrite X22; exact D12|].
split; [rewrite X24; rewrite (op3_den_off E2 24 0 (l_p cx + o1)) by
       (first [rewrite E24 | rewrite E2lo by lia; rewrite E24]; apply unsigned_lit_small; lia); unfold w64; f_equal; lia|].
split; [rewrite X23; rewrite (op3_den_off E2 23 0 0) by
       (first [rewrite E23 | rewrite E2lo by lia; rewrite E23]; reflexivity); reflexivity|].
exact KR.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The shadow of op_begin's two memsets (receive_cg.v trans_recv_cells) *)
(* ------------------------------------------------------------------ *)

(* The bytes of a zero-shadow row of the record are addressable. *)
Lemma op3_zero_ra : forall ly S (W : world segs) mem md lo hi q n, @AR rc segs B ly S W mem md ->
  decode_zshadow_at B lo hi -> lo mod 8 = 0 -> hi mod 8 = 0 -> lo <= q -> q + n <= hi ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF q n.
Proof.
intros ly S W mem md lo hi q n HAR HZ Hlo Hhi Hq Hn x Hx.
pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
pose proof (Z.div_mod lo 8 ltac:(lia)). pose proof (Z.div_mod hi 8 ltac:(lia)).
exists 0. split; [|left; reflexivity].
assert (Hz := decode_zshadow_rd B ly S W mem md lo hi (8 * (x / 8)) HAR
  ltac:(rewrite Z.mul_comm; apply Z_mod_mult) ltac:(lia) ltac:(lia) HZ).
unfold shadow_of_addr. replace (SHADOW_OFF + x / 8) with (ACells.shadow_addr (8 * (x / 8))); [exact Hz|].
unfold ACells.shadow_addr, ACells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* A granule's shadow byte of a zero-shadow row is visible. *)
Lemma op3_zero_vis : forall ly S (W : world segs) mem md lo hi T, @AR rc segs B ly S W mem md ->
  decode_zshadow_at B lo hi -> T mod 8 = 0 -> lo <= T -> T + 8 <= hi ->
  aview segs (w_H W) mem (SHADOW_OFF + T / 8) <> None.
Proof.
intros ly S W mem md lo hi T HAR HZ HT H1 H2.
pose proof (decode_zshadow_rd B ly S W mem md lo hi T HAR HT H1 H2 HZ) as Hz.
replace (SHADOW_OFF + T / 8) with (ACells.shadow_addr T) by (unfold ACells.shadow_addr, ACells.ASAN_K, SHADOW_OFF; lia).
rewrite Hz. discriminate.
Qed.

(* A one-byte constant cell of the record is visible. *)
Lemma op3_cell_vis : forall ly S (W : world segs) mem md a v, @AR rc segs B ly S W mem md ->
  In (z1 (ANum a) v) (as_const B ly) -> aview segs (w_H W) mem a <> None.
Proof.
intros ly S W mem md a v HAR HC. destruct HAR as (Mm & _).
pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mm) _ HC) as Hh.
unfold cell_holds in Hh. cbn [c_at c_w YG0f.c_val z1 c1 aeval] in Hh.
specialize (Hh 0%nat ltac:(lia)). cbn [Z.of_nat] in Hh. rewrite Z.add_0_r in Hh. rewrite Hh. discriminate.
Qed.

Lemma op3_ow_ra : forall ly S (W : world segs) mem md, @AR rc segs B ly S W mem md -> trans_recv_cells B ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF TA_OW 304 /\ shadow_hull_vis (aview segs (w_H W) mem) TA_OW 304.
Proof.
intros ly S W mem md HAR (HZo & _ & HZr & HC).
destruct (HC ly) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & _).
split; [exact (op3_zero_ra ly S W mem md TA_OW (TA_OW + TW.SZ_OW) TA_OW 304 HAR HZo
               ltac:(reflexivity) ltac:(reflexivity) ltac:(lia) ltac:(unfold TW.SZ_OW; lia))|].
intros s Hs. unfold shadow_addr, SHADOW_OFF, TA_OW in Hs. cbn in Hs.
assert (Hc : s = 0x800b6608 \/ s = 0x800b6609 \/ s = 0x800b660a \/ s = 0x800b660b \/
             (0x800b660c <= s < 0x800b6632) \/ s = 0x800b6632 \/ s = 0x800b6633 \/ s = 0x800b6634 \/
             s = 0x800b6635 \/ s = 0x800b6636 \/ s = 0x800b6637) by lia.
destruct Hc as [->|[->|[->|[->|[Hr|[->|[->|[->|[->|[->| ->]]]]]]]]]].
- exact (op3_zero_vis ly S W mem md TA_g_rx_len (TA_g_rx_len + TW.SZ_g_rx_len) 0x5f3040 HAR HZr
    ltac:(reflexivity) ltac:(unfold TA_g_rx_len; lia) ltac:(unfold TA_g_rx_len, TW.SZ_g_rx_len; lia)).
- exact (op3_cell_vis ly S W mem md _ _ HAR C1).
- exact (op3_cell_vis ly S W mem md _ _ HAR C2).
- exact (op3_cell_vis ly S W mem md _ _ HAR C3).
- replace s with (SHADOW_OFF + ((s - SHADOW_OFF) * 8) / 8) by (rewrite Z.div_mul by lia; lia).
  apply (op3_zero_vis ly S W mem md TA_OW (TA_OW + TW.SZ_OW) ((s - SHADOW_OFF) * 8) HAR HZo);
    [apply Z_mod_mult | unfold SHADOW_OFF, TA_OW; lia | unfold SHADOW_OFF, TA_OW, TW.SZ_OW; lia].
- exact (op3_cell_vis ly S W mem md _ _ HAR C4).
- exact (op3_cell_vis ly S W mem md _ _ HAR C5).
- exact (op3_cell_vis ly S W mem md _ _ HAR C6).
- exact (op3_cell_vis ly S W mem md _ _ HAR C7).
- exact (op3_cell_vis ly S W mem md _ _ HAR C8).
- exact (op3_cell_vis ly S W mem md _ _ HAR C9).
Qed.

Lemma op3_got_ra : forall ly S (W : world segs) mem md, @AR rc segs B ly S W mem md -> trans_recv_cells B ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF TA_GOT 224 /\ shadow_hull_vis (aview segs (w_H W) mem) TA_GOT 224.
Proof.
intros ly S W mem md HAR (_ & HZg & _ & HC).
destruct (HC ly) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & C10 & C11 & C12 & C13).
split; [exact (op3_zero_ra ly S W mem md TA_GOT (TA_GOT + TW.SZ_GOT) TA_GOT 224 HAR HZg
               ltac:(reflexivity) ltac:(reflexivity) ltac:(lia) ltac:(unfold TW.SZ_GOT; lia))|].
intros s Hs. unfold shadow_addr, SHADOW_OFF, TA_GOT in Hs. cbn in Hs.
assert (Hc : s = 0x800b4a58 \/ s = 0x800b4a59 \/ s = 0x800b4a5a \/ s = 0x800b4a5b \/
             (0x800b4a5c <= s < 0x800b4a78)) by lia.
destruct Hc as [->|[->|[->|[->|Hr]]]].
- exact (op3_cell_vis ly S W mem md _ _ HAR C10).
- exact (op3_cell_vis ly S W mem md _ _ HAR C11).
- exact (op3_cell_vis ly S W mem md _ _ HAR C12).
- exact (op3_cell_vis ly S W mem md _ _ HAR C13).
- replace s with (SHADOW_OFF + ((s - SHADOW_OFF) * 8) / 8) by (rewrite Z.div_mul by lia; lia).
  apply (op3_zero_vis ly S W mem md TA_GOT (TA_GOT + TW.SZ_GOT) ((s - SHADOW_OFF) * 8) HAR HZg);
    [apply Z_mod_mult | unfold SHADOW_OFF, TA_GOT; lia | unfold SHADOW_OFF, TA_GOT, TW.SZ_GOT; lia].
Qed.

(* ------------------------------------------------------------------ *)
(* 5. +0x78c .. +0x7a4: __asan_memset (OW, 0, 304), GOT into a0, __asan_memset (GOT, 0, 224) *)
(* ------------------------------------------------------------------ *)

Lemma op3_inG_row : forall o b n a, In (o, b, n) TMAP_A -> b <= a < b + n -> W_journalG.inG TG.G_HARNESS a.
Proof.
intros o b n a Hin Ha. unfold W_journalG.inG. apply Exists_exists. exists (b, n).
split; [exact (TMAP_A_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* A callee-saved register kept by a call (io_send_seg_ack.v iak_ap). *)
Lemma op3_ap : forall (R1 R2 : bvmap 5 word) (r : bv 5), aregs_preserved R1 R2 -> acallee_saved (bv_unsigned r) ->
  YK11.getr R2 r = YK11.getr R1 r.
Proof. intros R1 R2 r HP Hc. pose proof (HP _ Hc) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.

(* The registers the segment keeps, and s3, s6, s7, s8: all callee-saved. *)
Definition op3_cs : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma op3_cs_saved : forall r, In r op3_cs -> acallee_saved (bv_unsigned r).
Proof.
intros r Hr. unfold op3_cs in Hr. cbn [In] in Hr.
repeat (destruct Hr as [<- | Hr];
        [unfold acallee_saved;
         lazymatch goal with |- context [bv_unsigned ?x] =>
           let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end;
         lia |]).
destruct Hr.
Qed.
Lemma op3_cs_pres : forall R1 R2 : bvmap 5 word, aregs_preserved R1 R2 ->
  forall r, In r op3_cs -> YK11.getr R2 r = YK11.getr R1 r.
Proof. intros R1 R2 HP r Hr. exact (op3_ap R1 R2 r HP (op3_cs_saved r Hr)). Qed.
Lemma op3_keep_cs : forall r, In r op3_keep -> In r op3_cs.
Proof. intros r Hr. unfold op3_keep in Hr. unfold op3_cs. cbn [In] in *. tauto. Qed.

(* The state after the two memsets (+0x7a4): OW's and GOT's payloads zero, every other byte outside the memsets'
   window below sp1 the arm's. *)
Definition op3_PM (FP : list (Z * Z)) (cx : lcx) (ly : alayout) (S : astate) (W : world segs) (regs0 : bvmap 5 word)
    (mem0 : word -> option byte) (e scale o2 n2 : Z) : world segs -> config -> Prop :=
  fun W2 c2 => W2 = W /\ exists regs4 mem4 md4,
    c2 = mkCfg (@YK11.mkst (l_fx cx) regs4 (Z_to_bv 64 (BASE + 0x7a4)) mem4 (YK11.seg_rom segs)) md4 /\
    op3_J FP cx ly S W mem4 md4 e /\
    YK11.getr regs4 19 = w64 scale /\ YK11.getr regs4 22 = w64 TA_OW /\
    YK11.getr regs4 24 = w64 (l_p cx + o2) /\ YK11.getr regs4 23 = w64 n2 /\
    op3_kept regs0 regs4 /\
    (forall i, 0 <= i < 304 -> aview segs (w_H W) mem4 (TA_OW + i) = Some 0) /\
    (forall i, 0 <= i < 224 -> aview segs (w_H W) mem4 (TA_GOT + i) = Some 0) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (TA_OW <= a < TA_OW + 304) -> ~ (TA_GOT <= a < TA_GOT + 224) ->
       ~ (lc_sp1 cx - ESTACK <= a < lc_sp1 cx) -> aview segs (w_H W) mem4 a = aview segs (w_H W) mem0 a) /\
    (forall a, apresent (w_H W) mem0 a -> apresent (w_H W) mem4 a).

Lemma op3_seat_empty : forall (fx : YK11.FPState) (W : world segs) regs mem pc,
  st_ok_pi segs VAL (Eimg (PI := PI_transport) (Ereg regs [])) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros fx W regs mem pc. rewrite restrict_mkst_fx.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport);
  [apply regs_ok_Eimg_Ereg | reflexivity | constructor | exact I | split; [exact I | split; exact I]].
Qed.

Lemma op3_A2 : forall FP cx ly S W regs0 mem e scale o2 n2 W2 c2,
  AR_laws segs B -> W_journalG.gx_ok segs B TG.G_HARNESS ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OSet (transport_sigma TS___asan_memset)) ->
  trans_recv_cells B ->
  YK11.getr regs0 2 = w64 (lc_sp1 cx) -> YK11.getr regs0 3 = w64 (as_gp B) -> YK11.getr regs0 4 = w64 (as_tp B) ->
  lc_sp0 cx mod 16 = 0 -> lc_sp1 cx mod 32 = 0 -> lc_sp0 cx - 336 <= lc_sp1 cx <= lc_sp0 cx - 320 ->
  0x7fff7f800000 <= lc_sp1 cx <= 2 ^ 47 ->
  op3_PA FP cx ly S W regs0 mem e scale o2 n2 W2 c2 ->
  SRr segs W2 c2 (op3_PM FP cx ly S W regs0 mem e scale o2 n2).
Proof.
intros FP cx ly S W regs0 mem e scale o2 n2 W2 c2 LAWS HGX AMS HRC R2 R3 R4 Hsp0 Hsp1 Hsp Hsp1b HPA.
destruct HPA as (-> & regs2 & md2 & -> & HJ & R10 & R11 & R12 & R1 & R19 & R22 & R24 & R23 & KR).
pose proof (W_journalG.ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
assert (EST : ESTACK = 4096) by reflexivity.
assert (Hk2 : forall r, In r op3_keep -> YK11.getr regs2 r = YK11.getr regs0 r) by exact KR.
assert (Hsp2 : spZ regs2 = lc_sp1 cx).
{ unfold spZ. rewrite (Hk2 2%bv ltac:(cbn; tauto)), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (Ho16 : (lc_sp1 cx - lc_sp0 cx) mod 16 = 0)
  by (clear - Hsp0 Hsp1; Z.div_mod_to_equations; lia).
(* __asan_memset (OW, 0, 304) at +0x78c *)
eapply SRr_bind.
{ apply (@gx_intrin_at (l_fx cx) rc tfib_sink_head segs B LAWS transport_segs_low OSet
    (transport_sigma TS___asan_memset) (AMS (l_fx cx)) TG.G_HARNESS W regs2 mem LLVMF_STK (lc_sp0 cx) FP
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly S md2 e TA_OW 0 304
    (lc_sp1 cx - lc_sp0 cx) (Z_to_bv 64 (BASE + 0x790)) HGX G_HARNESS_rw HJ R10 R11 R12).
  - lia.
  - unfold TA_OW; lia.
  - unfold TA_OW; lia.
  - rewrite Hsp2. lia.
  - exact Ho16.
  - lia.
  - unfold LLVMF_STK. lia.
  - rewrite (Hk2 3%bv ltac:(cbn; tauto)). exact R3.
  - rewrite (Hk2 4%bv ltac:(cbn; tauto)). exact R4.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|]. intros a Ha. right.
    exact (op3_inG_row _ _ _ a TMAP_A_OW ltac:(unfold TW.SZ_OW; lia)).
  - left. unfold kLowMemEnd, TA_OW. lia.
  - exact (proj1 (op3_ow_ra _ _ _ _ _ HAR HRC)).
  - intros _. exact (proj2 (op3_ow_ra _ _ _ _ _ HAR HRC)).
  - exact I. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & _ & Hset3 & Heff3 & Hgr3).
(* +0x790 .. +0x7a0: GOT into a0, a1 = 0, a2 = 224, the call *)
pose proof (op3_seat_empty (l_fx cx) W regs3 mem3 0x790) as HS.
set (E := Eimg (PI := PI_transport) (Ereg regs3 [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (SHOK : sh_ok segs op3_Bx [] E (mrestrict (w_H W) mem3)) by constructor.
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
change (Z_to_bv 64 (BASE + 0x790)) with (Z_to_bv 64 (BASE + 1936)).
paj_run_tok RUN HS HJ3 SHOK Bspan; [op3_awr_ro|].
op3_ro HF M4.
assert (EM4 : ms_mem ms = mem3) by (apply functional_extensionality; intros x; rewrite M4; reflexivity).
pose proof op3_vals as (_ & _ & V13 & _ & _).
op3_rd HS (10%bv : bv 5) X10; op3_rd HS (11%bv : bv 5) X11; op3_rd HS (12%bv : bv 5) X12;
op3_rd HS (1%bv : bv 5) X1.
assert (KR4 : forall r, In r op3_cs -> YK11.getr (ms_regs ms) r = YK11.getr regs3 r).
{ intros r Hr. refine (regs_kept_of_st_ok segs _ _ (restrict (w_H W) ms) regs3 [] op3_cs HS _
    ltac:(vm_compute; reflexivity) r Hr).
  split; [intros n Hn; repeat rewrite ew_ewset_other by lia; unfold E; rewrite Eimg_low by (unfold A_TEXT; lia);
          reflexivity | reflexivity]. }
pmkst HS.
rewrite EM4 in HJ3 |- *.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md4 := mdx) in *; clearbody md4 end.
pose proof (W_journalG.ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR4.
assert (Hsp4 : spZ (ms_regs ms) = lc_sp1 cx).
{ unfold spZ. rewrite (KR4 2%bv ltac:(cbn; tauto)), (op3_cs_pres _ _ HP3 2%bv ltac:(cbn; tauto)),
    (Hk2 2%bv ltac:(cbn; tauto)), R2. unfold w64. apply unsigned_lit_small. lia. }
(* __asan_memset (GOT, 0, 224) at +0x7a0 *)
eapply SRr_bind.
{ apply (@gx_intrin_at (l_fx cx) rc tfib_sink_head segs B LAWS transport_segs_low OSet
    (transport_sigma TS___asan_memset) (AMS (l_fx cx)) TG.G_HARNESS W (ms_regs ms) mem3 LLVMF_STK (lc_sp0 cx) FP
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly S md4 e TA_GOT 0 224
    (lc_sp1 cx - lc_sp0 cx) (Z_to_bv 64 (BASE + 0x7a4)) HGX G_HARNESS_rw HJ3).
  - rewrite X10. change (SOff 254 0) with (SOff (A_OBJ 13) 0). rewrite (op3_den_img _ (A_OBJ 13) HEI0 ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), V13. reflexivity.
  - rewrite X11. reflexivity.
  - rewrite X12. reflexivity.
  - lia.
  - unfold TA_GOT; lia.
  - unfold TA_GOT; lia.
  - rewrite Hsp4. lia.
  - exact Ho16.
  - lia.
  - unfold LLVMF_STK. lia.
  - rewrite (KR4 3%bv ltac:(cbn; tauto)), (op3_cs_pres _ _ HP3 3%bv ltac:(cbn; tauto)),
      (Hk2 3%bv ltac:(cbn; tauto)). exact R3.
  - rewrite (KR4 4%bv ltac:(cbn; tauto)), (op3_cs_pres _ _ HP3 4%bv ltac:(cbn; tauto)),
      (Hk2 4%bv ltac:(cbn; tauto)). exact R4.
  - rewrite X1. apply codeptr_val. exact HEI0.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ3|]. intros a Ha. right.
    exact (op3_inG_row _ _ _ a TMAP_A_GOT ltac:(unfold TW.SZ_GOT; lia)).
  - left. unfold kLowMemEnd, TA_GOT. lia.
  - exact (proj1 (op3_got_ra _ _ _ _ _ HAR4 HRC)).
  - intros _. exact (proj2 (op3_got_ra _ _ _ _ _ HAR4 HRC)).
  - exact I. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & _ & Hset5 & Heff5 & Hgr5).
apply SRr_ret. unfold op3_PM. split; [reflexivity|]. exists regs5, mem5, md5.
assert (KR5 : forall r, In r op3_cs -> YK11.getr regs5 r = YK11.getr regs2 r).
{ intros r Hr. rewrite (op3_cs_pres _ _ HP5 r Hr), (KR4 r Hr), (op3_cs_pres _ _ HP3 r Hr). reflexivity. }
split; [reflexivity|].
split; [exact HJ5|].
split; [rewrite (KR5 19%bv ltac:(cbn; tauto)); exact R19|].
split; [rewrite (KR5 22%bv ltac:(cbn; tauto)); exact R22|].
split; [rewrite (KR5 24%bv ltac:(cbn; tauto)); exact R24|].
split; [rewrite (KR5 23%bv ltac:(cbn; tauto)); exact R23|].
split; [intros r Hr; rewrite (KR5 r (op3_keep_cs r Hr)); exact (Hk2 r Hr)|].
split.
{ intros i Hi. rewrite Heff5 by (unfold TA_OW, TA_GOT in *; lia).
  rewrite (Hset3 i Hi). reflexivity. }
split.
{ intros i Hi. rewrite (Hset5 i Hi). reflexivity. }
split.
{ intros a Ha H1 H2 H3. rewrite Heff5 by (rewrite ?Hsp4; lia). rewrite Heff3 by (rewrite ?Hsp2; lia). reflexivity. }
intros a Ha. apply Hgr5, Hgr3, Ha.
Qed.
End a.

(* ------------------------------------------------------------------ *)
(* 6. The symbolic state at +0x7a4                                     *)
(* ------------------------------------------------------------------ *)

(* Atoms: 0 .. 31 the registers, 32 g_fail_next's byte, 33 = M (the spill at 184(s1)), 34 = g_now's auipc page (the
   spill at 176(s1)), 35 = g_now, 36 / 37 the u16's two bytes (read only when left). Regions: g_fail_next's byte at
   s4 - 1076 (read only), OW.desk_off at s6 + 232, the two spills at s1 + 176 .. s1 + 192 (read only), M.fail at
   M + 88, g_now at the page - 1052, the u16's bytes at s8 (read only). *)
Definition op3_r_fail : YP09.region := YP09.mkRegion (Some 20%nat) (-1076) (-1075) 0 0
  [YP09.mkChunk (-1076) (CVal 1 (SOff 32 0))].
Definition op3_r_ow : YP09.region := YP09.mkRegion (Some 22%nat) 232 236 232 236 [].
Definition op3_r_spill : YP09.region := YP09.mkRegion (Some 9%nat) 176 192 0 0
  [YP09.mkChunk 176 (CVal 8 (SOff 34 0)); YP09.mkChunk 184 (CVal 8 (SOff 33 0))].
Definition op3_r_m : YP09.region := YP09.mkRegion (Some 33%nat) 88 92 88 92 [].
Definition op3_r_now : YP09.region := YP09.mkRegion (Some 34%nat) (-1052) (-1044) (-1052) (-1044)
  [YP09.mkChunk (-1052) (CVal 8 (SOff 35 0))].
Definition op3_r_in1 : YP09.region := YP09.mkRegion (Some 24%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 36 0))].
Definition op3_r_in2 : YP09.region := YP09.mkRegion (Some 24%nat) 0 2 0 0
  [YP09.mkChunk 0 (CVal 1 (SOff 36 0)); YP09.mkChunk 1 (CVal 1 (SOff 37 0))].
Definition op3_rin (m : Z) : list YP09.region := if m =? 0 then [] else if m =? 1 then [op3_r_in1] else [op3_r_in2].
Definition op3_fb : facts := mkFacts
  [(26%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (24%nat, PTR 0); (20%nat, mkAF LF_S4 LF_S4 2);
   (22%nat, mkAF TA_OW TA_OW 5); (33%nat, mkAF TA_M TA_M 5); (34%nat, mkAF (transport_hi 9) (transport_hi 9) 2);
   (32%nat, mkAF 0 255 0); (36%nat, mkAF 0 255 0); (37%nat, mkAF 0 255 0)] [] [].
Definition op3_ss2 (m : Z) : sstate :=
  mkSS 0x7a4 sr_atoms ([op3_r_fail; op3_r_ow; op3_r_spill; op3_r_m; op3_r_now] ++ op3_rin m) None op3_fb.
Definition op3_SH2 (m : Z) : list shent := if m =? 0 then [] else [mkSHE 24 0 m].

Lemma op3_apart_img : forall x m lo hi, 0 < m -> lo < hi ->
  (forall j, 0 <= j < m -> ~ in_img tfibsegs (x + j)) -> (forall a, lo <= a < hi -> in_img tfibsegs a) ->
  x + m <= lo \/ hi <= x.
Proof.
intros x m lo hi Hm Hl H1 H2.
destruct (Z_le_gt_dec (x + m) lo) as [Ha|Ha]; [left; exact Ha|]. apply Z.gt_lt in Ha.
destruct (Z_le_gt_dec hi x) as [Hb|Hb]; [right; exact Hb|]. apply Z.gt_lt in Hb.
exfalso. destruct (Z_le_gt_dec x lo) as [Hc|Hc]; [|apply Z.gt_lt in Hc].
- apply (H1 (lo - x)); [split; Lia.lia|]. replace (x + (lo - x)) with lo by Lia.lia. apply H2. split; Lia.lia.
- apply (H1 0); [split; Lia.lia|]. rewrite Z.add_0_r. apply H2. split; Lia.lia.
Qed.

Section s2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Definition op3_E2 (regs : bvmap 5 word) (gf now lo hi : Z) : env :=
  Eimg (PI := PI_transport) (Ereg regs [Z_to_bv 64 gf; Z_to_bv 64 TA_M; Z_to_bv 64 (transport_hi 9); Z_to_bv 64 now;
                                        Z_to_bv 64 lo; Z_to_bv 64 hi]).

Lemma op3_E2_reg : forall regs gf now lo hi n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (op3_E2 regs gf now lo hi) n = YK11.getr regs r.
Proof. intros. unfold op3_E2. apply ew_Eimg_Ereg_nat. assumption. Qed.
Lemma op3_E2_x : forall regs gf now lo hi j, (j < 6)%nat ->
  ew (op3_E2 regs gf now lo hi) (32 + j) =
  nth j [Z_to_bv 64 gf; Z_to_bv 64 TA_M; Z_to_bv 64 (transport_hi 9); Z_to_bv 64 now; Z_to_bv 64 lo; Z_to_bv 64 hi]
    (Z_to_bv 64 0).
Proof. intros. unfold op3_E2. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.

Lemma op3_seat2 : forall (W : world segs) regs mem (m gf now lo hi s8v sp1 : Z),
  m = 0 \/ m = 1 \/ m = 2 ->
  YK11.getr regs 26 = w64 SHADOW_OFF -> YK11.getr regs 24 = w64 s8v -> YK11.getr regs 9 = w64 sp1 ->
  YK11.getr regs 20 = w64 LF_S4 -> YK11.getr regs 22 = w64 TA_OW ->
  4096 <= s8v <= 140737479966720 -> s8v + m <= sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  0 <= gf < 256 -> 0 <= now < 2 ^ 64 -> 0 <= lo < 256 -> 0 <= hi < 256 ->
  val_mem segs (mrestrict (w_H W) mem) TA_g_fail_next 1 gf ->
  val_mem segs (mrestrict (w_H W) mem) TA_g_now 8 now ->
  val_mem segs (mrestrict (w_H W) mem) (sp1 + 176) 8 (transport_hi 9) ->
  val_mem segs (mrestrict (w_H W) mem) (sp1 + 184) 8 TA_M ->
  (0 < m -> val_mem segs (mrestrict (w_H W) mem) s8v 1 lo) ->
  (1 < m -> val_mem segs (mrestrict (w_H W) mem) (s8v + 1) 1 hi) ->
  (0 < m -> s8v + m <= TA_g_now \/ TA_g_fail_next + 1 <= s8v) ->
  (0 < m -> s8v + m <= TA_M + 88 \/ TA_M + 92 <= s8v) ->
  (0 < m -> s8v + m <= TA_OW + 232 \/ TA_OW + 236 <= s8v) ->
  st_ok_pi segs VAL (op3_E2 regs gf now lo hi) (op3_ss2 m)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 0x7a4)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem m gf now lo hi s8v sp1 Hm R26 R24 R9 R20 R22 H8 Hs8 Hsp Hsp32 Hgf Hnow Hlo Hhi
  Vgf Vnow V176 V184 Vlo Vhi D1 D2 D3.
set (E := op3_E2 regs gf now lo hi).
assert (U24 : bv_unsigned (ew E 24) = s8v)
  by (unfold E; rewrite (op3_E2_reg regs gf now lo hi 24 24%bv eq_refl), R24; unfold w64; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF)
  by (unfold E; rewrite (op3_E2_reg regs gf now lo hi 26 26%bv eq_refl), R26; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (U9 : bv_unsigned (ew E 9) = sp1)
  by (unfold E; rewrite (op3_E2_reg regs gf now lo hi 9 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = LF_S4)
  by (unfold E; rewrite (op3_E2_reg regs gf now lo hi 20 20%bv eq_refl), R20; unfold w64; apply unsigned_lit_small;
      unfold LF_S4; cbn; lia).
assert (U22 : bv_unsigned (ew E 22) = TA_OW)
  by (unfold E; rewrite (op3_E2_reg regs gf now lo hi 22 22%bv eq_refl), R22; unfold w64; apply unsigned_lit_small;
      unfold TA_OW; lia).
assert (E32 : ew E 32 = Z_to_bv 64 gf) by exact (op3_E2_x regs gf now lo hi 0 ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 TA_M) by exact (op3_E2_x regs gf now lo hi 1 ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 (transport_hi 9)) by exact (op3_E2_x regs gf now lo hi 2 ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 now) by exact (op3_E2_x regs gf now lo hi 3 ltac:(lia)).
assert (E36 : ew E 36 = Z_to_bv 64 lo) by exact (op3_E2_x regs gf now lo hi 4 ltac:(lia)).
assert (E37 : ew E 37 = Z_to_bv 64 hi) by exact (op3_E2_x regs gf now lo hi 5 ltac:(lia)).
assert (U33 : bv_unsigned (ew E 33) = TA_M) by (rewrite E33; apply unsigned_lit_small; unfold TA_M; lia).
assert (U34 : bv_unsigned (ew E 34) = transport_hi 9) by (rewrite E34; apply unsigned_lit_small; cbn; lia).
pose proof lf_spill_pages as (_ & P9 & P10 & _).
assert (HS4 : LF_S4 = 0x5df554) by exact P10.
assert (HGF : LF_S4 + -1076 = TA_g_fail_next) by (rewrite HS4; reflexivity).
assert (HNW : transport_hi 9 + -1052 = TA_g_now) by (rewrite P9; reflexivity).
assert (HOW : forall o, 232 <= o < 236 -> writable_at segs (mrestrict (w_H W) mem) (TA_OW + o)).
{ intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_OW + o) G_HARNESS_rw).
  apply (op3_inG_row _ _ _ _ TMAP_A_OW). unfold TW.SZ_OW. lia. }
assert (HMW : forall o, 88 <= o < 92 -> writable_at segs (mrestrict (w_H W) mem) (TA_M + o)).
{ intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (TA_M + o) G_HARNESS_rw).
  apply (op3_inG_row _ _ _ _ TMAP_A_M). unfold TW.SZ_M. lia. }
assert (HNWW : forall o, -1052 <= o < -1044 -> writable_at segs (mrestrict (w_H W) mem) (transport_hi 9 + o)).
{ intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (transport_hi 9 + o) G_HARNESS_rw).
  apply (op3_inG_row _ _ _ _ TMAP_A_g_now). rewrite P9. unfold TA_g_now, TW.SZ_g_now. lia. }
rewrite restrict_mkst_fx. unfold op3_ss2.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- destruct Hm as [-> | [-> | ->]]; vm_compute; reflexivity.
- apply Forall_app. split.
  + repeat apply Forall_cons; try apply Forall_nil.
    * unfold op3_r_fail, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U20. split; [unfold LF_S4; cbn; lia|]. split; [unfold LF_S4; cbn; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs _ _ LF_S4 (-1076) 1 (SOff 32 0) gf);
        [exact (op3_den_atom E 32 gf E32) | cbn; lia | lia | rewrite HGF; exact Vgf].
    * unfold op3_r_ow, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U22. split; [unfold TA_OW; lia|]. split; [unfold TA_OW; lia|]. split; [exact HOW|]. constructor.
    * unfold op3_r_spill, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val segs _ _ sp1 176 8 (SOff 34 0) (transport_hi 9));
           [exact (op3_den_atom E 34 _ E34) | rewrite P9; cbn; lia | lia | exact V176].
      -- apply (chunk_ok_val segs _ _ sp1 184 8 (SOff 33 0) TA_M);
           [exact (op3_den_atom E 33 _ E33) | unfold TA_M; cbn; lia | lia | exact V184].
    * unfold op3_r_m, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U33. split; [unfold TA_M; lia|]. split; [unfold TA_M; lia|]. split; [exact HMW|]. constructor.
    * unfold op3_r_now, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U34. split; [rewrite P9; lia|]. split; [rewrite P9; lia|]. split; [exact HNWW|].
      constructor; [|constructor].
      apply (chunk_ok_val segs _ _ (transport_hi 9) (-1052) 8 (SOff 35 0) now);
        [exact (op3_den_atom E 35 now E35) | cbn; lia | lia | rewrite HNW; exact Vnow].
  + destruct Hm as [-> | [-> | ->]]; unfold op3_rin; cbn [Z.eqb Pos.eqb]; repeat apply Forall_cons; try apply Forall_nil.
    * unfold op3_r_in1, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U24. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs _ _ s8v 0 1 (SOff 36 0) lo);
        [exact (op3_den_atom E 36 lo E36) | cbn; lia | lia | rewrite Z.add_0_r; exact (Vlo ltac:(lia))].
    * unfold op3_r_in2, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U24. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val segs _ _ s8v 0 1 (SOff 36 0) lo);
           [exact (op3_den_atom E 36 lo E36) | cbn; lia | lia | rewrite Z.add_0_r; exact (Vlo ltac:(lia))].
      -- apply (chunk_ok_val segs _ _ s8v 1 1 (SOff 37 0) hi);
           [exact (op3_den_atom E 37 hi E37) | cbn; lia | lia | exact (Vhi ltac:(lia))].
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  destruct Hm as [-> | [-> | ->]].
  2,3: specialize (D1 ltac:(lia)); specialize (D2 ltac:(lia)); specialize (D3 ltac:(lia)).
  all: unfold op3_rin; cbn [Z.eqb Pos.eqb app];
  unfold op3_r_fail, op3_r_ow, op3_r_spill, op3_r_m, op3_r_now, op3_r_in1, op3_r_in2;
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite U20, U22, U9, U33, U34; rewrite ?U24;
  cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
  rewrite HS4, P9 in *; unfold TA_OW, TA_M, TA_g_now, TA_g_fail_next in *;
  repeat split; try exact I; lia.
- unfold op3_fb, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
  rewrite U26, U24, U20, U22, U33, U34, E32, E36, E37, !unsigned_lit_small by lia.
  rewrite HS4, P9. change (2 ^ 5) with 32. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | unfold TA_OW, TA_M; reflexivity | reflexivity].
Qed.

Lemma op3_shok2 : forall B ly S (W : world segs) mem md regs gf now lo hi m s8v, @AR rc segs B ly S W mem md ->
  m = 0 \/ m = 1 \/ m = 2 ->
  YK11.getr regs 26 = w64 SHADOW_OFF -> YK11.getr regs 24 = w64 s8v -> 0 <= s8v -> s8v + m < 2 ^ 63 ->
  (0 < m -> range_addressable (aview segs (w_H W) mem) SHADOW_OFF s8v m) ->
  (forall x, s8v <= x < s8v + m -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)) ->
  sh_ok segs op3_Bx (op3_SH2 m) (op3_E2 regs gf now lo hi) (mrestrict (w_H W) mem).
Proof.
intros B ly S W mem md regs gf now lo hi m s8v HAR Hm R26 R24 H0 H1 HRA Hap.
set (E := op3_E2 regs gf now lo hi).
assert (U24 : bv_unsigned (ew E 24) = s8v)
  by (unfold E; rewrite (op3_E2_reg regs gf now lo hi 24 24%bv eq_refl), R24; unfold w64; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF)
  by (unfold E; rewrite (op3_E2_reg regs gf now lo hi 26 26%bv eq_refl), R26; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
destruct Hm as [-> | [-> | ->]]; unfold sh_ok, op3_SH2; cbn [Z.eqb Pos.eqb]; repeat constructor.
all: apply (shent_ok_of_range segs (w_H W) mem E op3_Bx 24 s8v _ s8v 0 _ (HRA ltac:(lia))).
all: try (unfold op3_Bx; rewrite (op3_U_off E 26 0 SHADOW_OFF U26) by (unfold SHADOW_OFF; lia); lia).
all: try (rewrite (op3_U_off E 24 0 s8v U24) by lia; lia).
all: try lia.
all: intros x Hx; cbn [Z.min Z.max] in Hx; apply Hap; lia.
Qed.
End s2.

(* ------------------------------------------------------------------ *)
(* 7. The world after the segment's G stores                            *)
(* ------------------------------------------------------------------ *)

Definition op3_in (lo n x : Z) : bool := (lo <=? x) && (x <? lo + n).
Lemma op3_in_t : forall lo n x, op3_in lo n x = true <-> lo <= x < lo + n.
Proof. intros lo n x. unfold op3_in. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.
Lemma op3_in_f : forall lo n x, op3_in lo n x = false <-> ~ (lo <= x < lo + n).
Proof. intros lo n x. split; intros H; [intros Hx; apply op3_in_t in Hx; congruence|].
destruct (op3_in lo n x) eqn:E; [apply op3_in_t in E; tauto | reflexivity]. Qed.

(* Two writes into the world's payload rows, in order, at disjoint addresses. *)
Lemma op3_tw_upd2 : forall (rd rd' : Z -> option Z) Bw o1 b1 n1 k1 v1 o2 b2 n2 k2 v2,
  tw_at TMAP_A rd Bw -> In (o1, b1, n1) TMAP_A -> In (o2, b2, n2) TMAP_A ->
  0 <= k1 -> k1 + Z.of_nat (length v1) <= n1 -> 0 <= k2 -> k2 + Z.of_nat (length v2) <= n2 ->
  (b1 + k1 + Z.of_nat (length v1) <= b2 + k2 \/ b2 + k2 + Z.of_nat (length v2) <= b1 + k1) ->
  (forall j, (j < length v1)%nat -> rd' (b1 + k1 + Z.of_nat j) = Some (bv_unsigned (nth j v1 (Z_to_bv 8 0)))) ->
  (forall j, (j < length v2)%nat -> rd' (b2 + k2 + Z.of_nat j) = Some (bv_unsigned (nth j v2 (Z_to_bv 8 0)))) ->
  (forall x, tw_in TMAP_A x -> ~ (b1 + k1 <= x < b1 + k1 + Z.of_nat (length v1)) ->
     ~ (b2 + k2 <= x < b2 + k2 + Z.of_nat (length v2)) -> rd' x = rd x) ->
  tw_at TMAP_A rd' (TW.upd (TW.upd Bw (o1 + k1) v1) (o2 + k2) v2).
Proof.
intros rd rd' Bw o1 b1 n1 k1 v1 o2 b2 n2 k2 v2 HT H1 H2 Hk1 Hn1 Hk2 Hn2 Hd V1 V2 Hfr.
set (rdA := fun x => if op3_in (b2 + k2) (Z.of_nat (length v2)) x then rd x else rd' x).
assert (HA : tw_at TMAP_A rdA (TW.upd Bw (o1 + k1) v1)).
{ apply (tw_upd TMAP_A rd rdA Bw o1 b1 n1 k1 v1 TMAP_A_ok HT H1 Hk1 Hn1).
  - intros j Hj. unfold rdA. rewrite (proj2 (op3_in_f _ _ _)) by lia. exact (V1 j Hj).
  - intros x Hx Hn. unfold rdA. destruct (op3_in (b2 + k2) (Z.of_nat (length v2)) x) eqn:E; [reflexivity|].
    apply op3_in_f in E. exact (Hfr x Hx Hn E). }
apply (tw_upd TMAP_A rdA rd' _ o2 b2 n2 k2 v2 TMAP_A_ok HA H2 Hk2 Hn2).
- exact V2.
- intros x Hx Hn. unfold rdA. rewrite (proj2 (op3_in_f _ _ _) Hn). reflexivity.
Qed.

Lemma op3_tw_upd3 : forall (rd rd' : Z -> option Z) Bw o1 b1 n1 k1 v1 o2 b2 n2 k2 v2 o3 b3 n3 k3 v3,
  tw_at TMAP_A rd Bw -> In (o1, b1, n1) TMAP_A -> In (o2, b2, n2) TMAP_A -> In (o3, b3, n3) TMAP_A ->
  0 <= k1 -> k1 + Z.of_nat (length v1) <= n1 -> 0 <= k2 -> k2 + Z.of_nat (length v2) <= n2 ->
  0 <= k3 -> k3 + Z.of_nat (length v3) <= n3 ->
  (b1 + k1 + Z.of_nat (length v1) <= b2 + k2 \/ b2 + k2 + Z.of_nat (length v2) <= b1 + k1) ->
  (b1 + k1 + Z.of_nat (length v1) <= b3 + k3 \/ b3 + k3 + Z.of_nat (length v3) <= b1 + k1) ->
  (b2 + k2 + Z.of_nat (length v2) <= b3 + k3 \/ b3 + k3 + Z.of_nat (length v3) <= b2 + k2) ->
  (forall j, (j < length v1)%nat -> rd' (b1 + k1 + Z.of_nat j) = Some (bv_unsigned (nth j v1 (Z_to_bv 8 0)))) ->
  (forall j, (j < length v2)%nat -> rd' (b2 + k2 + Z.of_nat j) = Some (bv_unsigned (nth j v2 (Z_to_bv 8 0)))) ->
  (forall j, (j < length v3)%nat -> rd' (b3 + k3 + Z.of_nat j) = Some (bv_unsigned (nth j v3 (Z_to_bv 8 0)))) ->
  (forall x, tw_in TMAP_A x -> ~ (b1 + k1 <= x < b1 + k1 + Z.of_nat (length v1)) ->
     ~ (b2 + k2 <= x < b2 + k2 + Z.of_nat (length v2)) -> ~ (b3 + k3 <= x < b3 + k3 + Z.of_nat (length v3)) ->
     rd' x = rd x) ->
  tw_at TMAP_A rd' (TW.upd (TW.upd (TW.upd Bw (o1 + k1) v1) (o2 + k2) v2) (o3 + k3) v3).
Proof.
intros rd rd' Bw o1 b1 n1 k1 v1 o2 b2 n2 k2 v2 o3 b3 n3 k3 v3 HT H1 H2 H3 Hk1 Hn1 Hk2 Hn2 Hk3 Hn3 D12 D13 D23
  V1 V2 V3 Hfr.
set (rdB := fun x => if op3_in (b3 + k3) (Z.of_nat (length v3)) x then rd x else rd' x).
assert (HB : tw_at TMAP_A rdB (TW.upd (TW.upd Bw (o1 + k1) v1) (o2 + k2) v2)).
{ apply (op3_tw_upd2 rd rdB Bw o1 b1 n1 k1 v1 o2 b2 n2 k2 v2 HT H1 H2 Hk1 Hn1 Hk2 Hn2 D12).
  - intros j Hj. unfold rdB. rewrite (proj2 (op3_in_f _ _ _)) by lia. exact (V1 j Hj).
  - intros j Hj. unfold rdB. rewrite (proj2 (op3_in_f _ _ _)) by lia. exact (V2 j Hj).
  - intros x Hx Ha Hb. unfold rdB. destruct (op3_in (b3 + k3) (Z.of_nat (length v3)) x) eqn:E; [reflexivity|].
    apply op3_in_f in E. exact (Hfr x Hx Ha Hb E). }
apply (tw_upd TMAP_A rdB rd' _ o3 b3 n3 k3 v3 TMAP_A_ok HB H3 Hk3 Hn3).
- exact V3.
- intros x Hx Hn. unfold rdB. rewrite (proj2 (op3_in_f _ _ _) Hn). reflexivity.
Qed.

(* The world after op_begin's two memsets, and after the segment's three stores (OW.desk_off = -1, M.fail =
   g_fail_next, g_now += u16 * SCALE). *)
Definition op3_w2 (Bw : list byte) : list byte :=
  TW.upd (TW.upd Bw (TW.OFF_OW + 0) (repeat (Z_to_bv 8 0) 304)) (TW.OFF_GOT + 0) (repeat (Z_to_bv 8 0) 224).
Definition op3_gf (Bw : list byte) : Z := TW.u_at (op3_w2 Bw) (TW.OFF_g_fail_next + 0) 1.
Definition op3_now (Bw : list byte) : Z := TW.u_at (op3_w2 Bw) (TW.OFF_g_now + 0) 8.
Definition op3_wF (Bw : list byte) (scale t : Z) : list byte :=
  TW.upd (TW.upd (TW.upd (op3_w2 Bw) (TW.OFF_OW + 232) (TW.put 4 (-1))) (TW.OFF_M + 88) (TW.put 4 (op3_gf Bw)))
    (TW.OFF_g_now + 0) (TW.put 8 (op3_now Bw + t * scale)).

(* Byte j < w (w <= 8) of a 64-bit word holding v (m_rx_seg_kit.v mrx_bow). *)
Lemma op3_bow : forall v (w j : nat), (j < w)%nat -> (w <= 8)%nat ->
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

(* The w bytes of a region's one chunk of value v (m_rx_seg_kit.v mrx_chunk_rd). *)
Lemma op3_chunk_rd : forall (E : env) (H : word -> bool) (mm : word -> option byte) n b lo hi wlo whi off (w : N)
    (e : sv) (v : Z),
  region_ok tfibsegs E (mrestrict H mm) (YP09.mkRegion (Some n) lo hi wlo whi [YP09.mkChunk off (CVal w e)]) ->
  bv_unsigned (ew E n) = b -> sv_denot E e = Z_to_bv 64 v -> (N.to_nat w <= 8)%nat ->
  forall j, (j < N.to_nat w)%nat -> aview tfibsegs H mm (b + off + Z.of_nat j) = Some (YO0f.le_byte v (N.to_nat w) j).
Proof.
intros E H mm n b lo hi wlo whi off w e v HR Hb He Hw j Hj.
destruct HR as (_ & _ & _ & HC). cbn [YP09.r_chunks YP09.r_base base_val] in HC. rewrite Hb in HC.
pose proof (Forall_inv HC) as HC1.
unfold YP09.chunk_ok in HC1. cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len] in HC1.
destruct (HC1 (Z.of_nat j) ltac:(lia)) as (bt & Hb1 & Hb2). cbn [YP09.cbyte] in Hb1. rewrite He in Hb1.
injection Hb1 as <-.
change (aview tfibsegs H mm (b + off + Z.of_nat j))
  with (option_map (fun y : byte => bv_unsigned y) (YP09.mbyte tfibsegs (mrestrict H mm) (b + off + Z.of_nat j))).
rewrite Hb2. cbn [option_map]. f_equal. apply op3_bow; lia.
Qed.

(* A heap block's bytes are addressable (TransportFevt.v decode_block_range_addressable). *)
Lemma op3_block_ra : forall (rd : Z -> option Z) p n q len,
  block_shadow rd SHADOW_OFF p (req_size n) -> 0 <= n -> p <= q -> 0 <= len -> q + len <= p + n ->
  range_addressable rd SHADOW_OFF q len.
Proof.
  intros rd p n q len (Hp8 & Hn0 & HB) Hn Hq Hl Hql x Hx.
  assert (Hreq : n <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
  set (i := (x - p) / 8).
  assert (Hi : 0 <= i < (req_size n + 7) / 8) by (unfold i; Z.div_mod_to_equations; lia).
  specialize (HB i Hi).
  assert (Ex : shadow_of_addr SHADOW_OFF p + i = shadow_of_addr SHADOW_OFF x).
  { unfold shadow_of_addr, i. Z.div_mod_to_equations. lia. }
  rewrite Ex in HB. eexists. split; [exact HB|].
  unfold saddr_ok. destruct (Z.ltb_spec i (req_size n / 8)) as [Hlt|Hge]; [left; reflexivity|].
  right. unfold i in *. Z.div_mod_to_equations. lia.
Qed.

Section b. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The bytes the segment may change: OW, GOT, M.fail, g_now and the window below sp1 of its two runtime calls. *)
Definition op3_wr (cx : lcx) (a : Z) : Prop :=
  TA_OW <= a < TA_OW + 304 \/ TA_GOT <= a < TA_GOT + 224 \/ TA_M + 88 <= a < TA_M + 92 \/
  TA_g_now <= a < TA_g_now + 8 \/ lc_sp1 cx - ESTACK <= a < lc_sp1 cx.
Definition op3_mem (cx : lcx) (W : world segs) (m0 m : word -> option byte) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ op3_wr cx a -> aview segs (w_H W) m a = aview segs (w_H W) m0 a) /\
  (forall a, apresent (w_H W) m0 a -> apresent (w_H W) m a).

(* The cut TICK's machine facts, at the world after the stores. *)
Definition op3_PT (FP : list (Z * Z)) (cx : lcx) (ly : alayout) (S : astate) (W : world segs) (regs0 : bvmap 5 word)
    (mem0 : word -> option byte) (e : Z) (Bw0 : list byte) (scale t o3 n3 : Z) : world segs -> config -> Prop :=
  fun W2 c2 => W2 = W /\ exists regs6 mem6 md6,
    c2 = lc_cfg cx LO_TICK regs6 mem6 md6 /\
    op3_J B FP cx ly S W mem6 md6 e /\
    lc_tw W mem6 (op3_wF Bw0 scale t) /\
    YK11.getr regs6 22 = w64 (op3_now Bw0 + t * scale) /\
    YK11.getr regs6 24 = w64 (l_p cx + o3) /\ YK11.getr regs6 23 = w64 n3 /\
    op3_kept regs0 regs6 /\ op3_mem cx W mem0 mem6.

Lemma op3_tw2 : forall cx (W : world segs) mem0 mem4 Bw0,
  lc_tw W mem0 Bw0 ->
  (forall i, 0 <= i < 304 -> aview segs (w_H W) mem4 (TA_OW + i) = Some 0) ->
  (forall i, 0 <= i < 224 -> aview segs (w_H W) mem4 (TA_GOT + i) = Some 0) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (TA_OW <= a < TA_OW + 304) -> ~ (TA_GOT <= a < TA_GOT + 224) ->
     ~ (lc_sp1 cx - ESTACK <= a < lc_sp1 cx) -> aview segs (w_H W) mem4 a = aview segs (w_H W) mem0 a) ->
  0x7fff7f800000 <= lc_sp1 cx ->
  lc_tw W mem4 (op3_w2 Bw0).
Proof.
intros cx W mem0 mem4 Bw0 HT ZO ZG KA Hsp. unfold lc_tw, op3_w2 in *.
assert (EST : ESTACK = 4096) by reflexivity.
apply (op3_tw_upd2 (aview segs (w_H W) mem0) _ Bw0 TW.OFF_OW TA_OW TW.SZ_OW 0 _ TW.OFF_GOT TA_GOT TW.SZ_GOT 0 _
  HT TMAP_A_OW TMAP_A_GOT); rewrite ?repeat_length; change (Z.of_nat 304) with 304; change (Z.of_nat 224) with 224.
- lia.
- unfold TW.SZ_OW; lia.
- lia.
- unfold TW.SZ_GOT; lia.
- unfold TA_OW, TA_GOT; lia.
- intros j Hj. rewrite nth_repeat, Z.add_0_r. apply ZO. lia.
- intros j Hj. rewrite nth_repeat, Z.add_0_r. apply ZG. lia.
- intros x Hx H1 H2. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  apply KA; [lia | lia | lia | lia].
Qed.

Lemma op3_B_end : forall FP cx ly S (W : world segs) regs0 mem0 e Bw0 scale t o3 n3 mem4 regs6 mem6 md6,
  lc_tw W mem0 Bw0 -> 0x7fff7f800000 <= lc_sp1 cx ->
  (forall i, 0 <= i < 304 -> aview segs (w_H W) mem4 (TA_OW + i) = Some 0) ->
  (forall i, 0 <= i < 224 -> aview segs (w_H W) mem4 (TA_GOT + i) = Some 0) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (TA_OW <= a < TA_OW + 304) -> ~ (TA_GOT <= a < TA_GOT + 224) ->
     ~ (lc_sp1 cx - ESTACK <= a < lc_sp1 cx) -> aview segs (w_H W) mem4 a = aview segs (w_H W) mem0 a) ->
  (forall a, apresent (w_H W) mem0 a -> apresent (w_H W) mem4 a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (TA_OW + 232 <= a < TA_OW + 236) -> ~ (TA_M + 88 <= a < TA_M + 92) ->
     ~ (TA_g_now <= a < TA_g_now + 8) -> aview segs (w_H W) mem6 a = aview segs (w_H W) mem4 a) ->
  (forall a, apresent (w_H W) mem4 a -> apresent (w_H W) mem6 a) ->
  (forall j, (j < 4)%nat -> aview segs (w_H W) mem6 (TA_OW + 232 + Z.of_nat j) = Some (YO0f.le_byte (-1) 4 j)) ->
  (forall j, (j < 4)%nat -> aview segs (w_H W) mem6 (TA_M + 88 + Z.of_nat j) = Some (YO0f.le_byte (op3_gf Bw0) 4 j)) ->
  (forall j, (j < 8)%nat ->
     aview segs (w_H W) mem6 (TA_g_now + Z.of_nat j) = Some (YO0f.le_byte (op3_now Bw0 + t * scale) 8 j)) ->
  op3_J B FP cx ly S W mem6 md6 e ->
  YK11.getr regs6 22 = w64 (op3_now Bw0 + t * scale) ->
  YK11.getr regs6 24 = w64 (l_p cx + o3) -> YK11.getr regs6 23 = w64 n3 -> op3_kept regs0 regs6 ->
  op3_PT FP cx ly S W regs0 mem0 e Bw0 scale t o3 n3 W (lc_cfg cx LO_TICK regs6 mem6 md6).
Proof.
intros FP cx ly S W regs0 mem0 e Bw0 scale t o3 n3 mem4 regs6 mem6 md6 HT Hsp ZO ZG KA4 GA4 KA6 GA6 VOW VM VN HJ6
  R22 R24 R23 KR.
assert (EST : ESTACK = 4096) by reflexivity.
unfold op3_PT. split; [reflexivity|]. exists regs6, mem6, md6.
split; [reflexivity|]. split; [exact HJ6|].
split.
{ pose proof (op3_tw2 cx W mem0 mem4 Bw0 HT ZO ZG KA4 Hsp) as H2. unfold lc_tw, op3_wF in *.
  apply (op3_tw_upd3 (aview segs (w_H W) mem4) _ (op3_w2 Bw0) TW.OFF_OW TA_OW TW.SZ_OW 232 _ TW.OFF_M TA_M TW.SZ_M 88 _
    TW.OFF_g_now TA_g_now TW.SZ_g_now 0 _ H2 TMAP_A_OW TMAP_A_M TMAP_A_g_now); rewrite ?TWL.length_put;
    change (Z.of_nat 4) with 4; change (Z.of_nat 8) with 8.
  - lia.
  - unfold TW.SZ_OW; lia.
  - lia.
  - unfold TW.SZ_M; lia.
  - lia.
  - unfold TW.SZ_g_now; lia.
  - unfold TA_OW, TA_M; lia.
  - unfold TA_OW, TA_g_now; lia.
  - unfold TA_M, TA_g_now; lia.
  - intros j Hj. rewrite tw_le_byte_put by exact Hj. exact (VOW j Hj).
  - intros j Hj. rewrite tw_le_byte_put by exact Hj. exact (VM j Hj).
  - intros j Hj. rewrite tw_le_byte_put by exact Hj. rewrite Z.add_0_r. exact (VN j Hj).
  - intros x Hx H1 H3 H4. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    apply KA6; [lia | lia | lia | lia]. }
split; [exact R22|]. split; [exact R24|]. split; [exact R23|]. split; [exact KR|].
split.
- intros a Ha Hn. unfold op3_wr in Hn.
  rewrite KA6 by (unfold TA_OW in *; lia). apply KA4; lia.
- intros a Ha. apply GA6, GA4, Ha.
Qed.
End b.

(* ------------------------------------------------------------------ *)
(* 8. +0x7a4 .. +0x96c: OW.desk_off, M.fail, the u16 and the g_now store *)
(* ------------------------------------------------------------------ *)

Lemma op3_nth_map : forall (D : list byte) i, nth i (map (fun b : byte => bv_unsigned b) D) 0 = DSpec.at8 D i.
Proof.
intros D. induction D as [|b D IH]; intros [|i]; cbn [nth map];
  first [reflexivity | vm_compute; reflexivity | exact (IH i)].
Qed.

Lemma op3_at8_range : forall D i, 0 <= DSpec.at8 D i < 256.
Proof.
intros D i. unfold DSpec.at8, DSpec.bz. pose proof (bv_unsigned_in_range 8 (nth i D (DSpec.b8 0))) as H.
change (bv_modulus 8) with 256 in H. exact H.
Qed.

Lemma op3_bv_eqb : forall v w, 0 <= v < 2 ^ 64 -> 0 <= w < 2 ^ 64 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 w) = (v =? w).
Proof. intros v w Hv Hw. unfold bv_eqb. rewrite !unsigned_lit_small by lia. reflexivity. Qed.

Lemma op3_den_madd : forall E X t (j k : nat) sc nw, sv_denot E X = Z_to_bv 64 t ->
  ew E j = Z_to_bv 64 sc -> ew E k = Z_to_bv 64 nw ->
  sv_denot E (SAlu ALU_ADD (SMd M_MUL X (SOff j 0)) (SOff k 0)) = Z_to_bv 64 (nw + t * sc).
Proof.
intros E X t j k sc nw HX Hj Hk.
change (sv_denot E (SAlu ALU_ADD (SMd M_MUL X (SOff j 0)) (SOff k 0))) with
  (alu64 ALU_ADD (mul_div M_MUL (sv_denot E X) (sv_denot E (SOff j 0))) (sv_denot E (SOff k 0))).
rewrite HX, (op3_den_atom E j sc Hj), (op3_den_atom E k nw Hk).
cbn [alu64 alu mul_div]. apply bv_eq.
rewrite bv_add_unsigned, bv_mul_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap. rewrite <- Zmult_mod, Zplus_mod_idemp_l, Zplus_mod_idemp_r. f_equal. ring.
Qed.

Lemma op3_den_or0 : forall E (k : nat) v, ew E k = Z_to_bv 64 v ->
  sv_denot E (SAlu ALU_OR (SLit 0) (SOff k 0)) = Z_to_bv 64 v.
Proof.
intros E k v Hk.
change (sv_denot E (SAlu ALU_OR (SLit 0) (SOff k 0))) with
  (alu64 ALU_OR (sv_denot E (SLit 0)) (sv_denot E (SOff k 0))).
rewrite (op3_den_atom E k v Hk). cbn [sv_denot alu64 alu]. apply bv_eq.
rewrite bv_or_unsigned, !Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. rewrite Z.lor_0_l. reflexivity.
Qed.

Lemma op3_le_m1 : forall j, (j < 4)%nat -> YO0f.le_byte 18446744073709551615 4 j = YO0f.le_byte (-1) 4 j.
Proof. intros j Hj. do 4 (destruct j as [|j]; [vm_compute; reflexivity|]). lia. Qed.

Lemma op3_apart_row : forall o b n x m lo hi, In (o, b, n) TMAP_A -> b <= lo -> hi <= b + n -> lo < hi -> 0 < m ->
  (forall j, 0 <= j < m -> ~ in_img tfibsegs (x + j)) -> x + m <= lo \/ hi <= x.
Proof.
intros o b n x m lo hi Hin H1 H2 H3 Hm Hx. apply (op3_apart_img x m lo hi Hm H3 Hx).
intros a Ha. apply trans_g_img, (op3_inG_row o b n a Hin). lia.
Qed.

(* g_now and g_fail_next lie in one loaded segment (with the bytes between them). *)
Lemma op3_gnow_img : forall a, TA_g_now <= a < TA_g_fail_next + 1 -> in_img tfibsegs a.
Proof.
intros a Ha. apply (decode_seg_covers_img [(TA_g_now, TA_g_fail_next + 1 - TA_g_now)] a); [vm_compute; reflexivity|].
apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.

Lemma op3_inG_any : forall a,
  TA_OW + 232 <= a < TA_OW + 236 \/ TA_M + 88 <= a < TA_M + 92 \/ TA_g_now <= a < TA_g_now + 8 ->
  W_journalG.inG TG.G_HARNESS a.
Proof.
intros a [Ha | [Ha | Ha]].
- apply (op3_inG_row _ _ _ a TMAP_A_OW). unfold TW.SZ_OW. lia.
- apply (op3_inG_row _ _ _ a TMAP_A_M). unfold TW.SZ_M. lia.
- apply (op3_inG_row _ _ _ a TMAP_A_g_now). unfold TW.SZ_g_now. lia.
Qed.

Definition op3_Zs (a : Z) : Prop :=
  TA_OW + 232 <= a < TA_OW + 236 \/ TA_M + 88 <= a < TA_M + 92 \/ TA_g_now <= a < TA_g_now + 8.

Section bk. Context {rc : YM05.RunCeil}.
Lemma op3_blk : forall (B : asyms) ly S (W : world tfibsegs) mem md p n,
  AR tfibsegs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  4096 <= p /\ p + req_size n <= YM05.alloc_ceiling /\ (p + req_size n <= kLowShadowBeg \/ kHighMemBeg <= p) /\
  n <= req_size n.
Proof.
intros B ly S W mem md p n (M & _) Hin.
apply In_ablocks in Hin as (k & Hk & _ & Hu & Hn).
pose proof (chunk_facts B ly S _ k M Hk) as (G1 & G2 & _ & G4 & G5 & _ & G7 & G8 & _).
rewrite Hn in G8, G7. rewrite Hu in G4. unfold in_app, ASAN_CEIL in *.
assert (n <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
lia.
Qed.
End bk.

(* The write rights of a run: an empty window, or a byte of OW.desk_off, M.fail or g_now (all in G). *)
Ltac op3_awr_g U22 U33 U34 HNW :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (first
    [ apply awr_ok_x_cons;
      [let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
       cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]
    | apply awr_ok_x_cons_g;
      [let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
       cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
       repeat rewrite ew_ewset_other in Ha by lia; rewrite ?U22, ?U33, ?U34 in Ha;
       apply op3_inG_any; lia |] ]);
  apply awr_ok_x_nil.

(* What a run kept: every byte outside op3_Zs. *)
Ltac op3_kf HFr U22 U33 U34 HNW K :=
  lazymatch type of HFr with frame_of ?Ex ?rs (mrestrict ?H ?m) (mrestrict ?H ?m') =>
    assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ op3_Zs a -> aview tfibsegs H m' a = aview tfibsegs H m a);
    [ apply (YC4b.kept_of_frame Ex rs H m m' op3_Zs HFr);
      let b := fresh "b" in let wl := fresh "wl" in let wh := fresh "wh" in let a := fresh "a" in
      let Hin := fresh "Hin" in let Hx := fresh "Hx" in
      intros b wl wh a Hin Hx;
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [Hin | Hin];
        [injection Hin as <- <- <-; cbn [base_val] in Hx;
         repeat rewrite ew_ewset_other in Hx by lia; rewrite ?U22, ?U33, ?U34 in Hx; unfold op3_Zs; lia |]);
      destruct Hin
    | ]
  end.

(* A branch on s7 the state's facts refute. *)
Ltac op3_refute Hc E23 :=
  exfalso;
  cbn [branch_taken sv_denot] in Hc; repeat rewrite ew_ewset_other in Hc by lia; rewrite E23 in Hc;
  rewrite ?unsigned_lit_small in Hc by lia; rewrite ?Z.add_0_r in Hc;
  rewrite ?op3_bv_eqb in Hc by lia;
  first [ discriminate Hc | cbn in Hc; discriminate Hc | apply Z.eqb_eq in Hc; lia | apply Z.eqb_neq in Hc; lia
        | apply negb_true_iff, Z.eqb_neq in Hc; lia | apply negb_false_iff, Z.eqb_eq in Hc; lia ].

Section b2. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma op3_B : forall FP cx ly S W regs0 mem0 e Bw0 scale o2 n2 W2 c2,
  AR_laws segs B -> W_journalG.gx_ok segs B TG.G_HARNESS ->
  op3_PM B FP cx ly S W regs0 mem0 e scale o2 n2 W2 c2 ->
  lc_tw W mem0 Bw0 ->
  YK11.getr regs0 9 = w64 (lc_sp1 cx) -> YK11.getr regs0 20 = w64 LF_S4 -> YK11.getr regs0 26 = w64 SHADOW_OFF ->
  YM05.alloc_ceiling + 32432 <= lc_sp1 cx -> lc_sp1 cx + 192 <= 2 ^ 47 -> lc_sp1 cx mod 32 = 0 ->
  rdword (aview segs (w_H W) mem0) (lc_sp1 cx + 176) = Some (transport_hi 9) ->
  rdword (aview segs (w_H W) mem0) (lc_sp1 cx + 184) = Some TA_M ->
  0 <= scale < 2 ^ 64 ->
  garr8 segs (mrestrict (w_H W) mem0) (l_p cx) (map (fun b : byte => bv_unsigned b) (l_pl cx)) ->
  l_n cx = Z.of_nat (length (l_pl cx)) -> 0 < l_n cx -> In (l_p cx, l_n cx) (ablocks B ly S) ->
  0 <= o2 -> 0 <= n2 -> o2 + n2 = l_n cx ->
  SRr segs W2 c2 (op3_PT B FP cx ly S W regs0 mem0 e Bw0 scale
    (snd (TOP.fuzz_u16_m (l_pl cx) (TOP.FuzzIn o2 n2))) (TOP.fi_off (fst (TOP.fuzz_u16_m (l_pl cx) (TOP.FuzzIn o2 n2))))
    (TOP.fi_n (fst (TOP.fuzz_u16_m (l_pl cx) (TOP.FuzzIn o2 n2))))).
Proof.
intros FP cx ly S W regs0 mem0 e Bw0 scale o2 n2 W2 c2 LAWS HGX HPM HT0 R9 R20 R26 Hsp1 Hsp1h Hsp1a S176 S184 Hsc
  HIN Hnl Hn0 HBLK Ho2 Hn2 Hon.
destruct HPM as (-> & regs4 & mem4 & md4 & -> & HJ & R19 & R22 & R24 & R23 & KR & ZO & ZG & KA4 & GA4).
unfold op3_J in HJ.
pose proof (W_journalG.ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR4.
assert (EST : ESTACK = 4096) by reflexivity.
pose proof ASAN_CEIL_range as (CL & _). unfold ASAN_CEIL in CL.
pose proof (op3_tw2 cx W mem0 mem4 Bw0 HT0 ZO ZG KA4 ltac:(lia)) as HT4.
assert (K9 : YK11.getr regs4 9 = w64 (lc_sp1 cx)) by (rewrite (KR 9%bv ltac:(cbn; tauto)); exact R9).
assert (K20 : YK11.getr regs4 20 = w64 LF_S4) by (rewrite (KR 20%bv ltac:(cbn; tauto)); exact R20).
assert (K26 : YK11.getr regs4 26 = w64 SHADOW_OFF) by (rewrite (KR 26%bv ltac:(cbn; tauto)); exact R26).
destruct (op3_blk B ly S W mem4 md4 _ _ HAR4 HBLK) as (Bp & Bc & Bsh & Brq).
assert (NIMG : forall a, l_p cx <= a < l_p cx + l_n cx -> ~ in_img segs a)
  by (intros a Ha; apply (blk_img segs B LAWS ly S W mem4 md4 (l_p cx) (l_n cx) a HAR4 HBLK); lia).
assert (OWimg : forall a, TA_OW <= a < TA_OW + 304 -> in_img segs a)
  by (intros a Ha; apply trans_g_img, (op3_inG_row _ _ _ a TMAP_A_OW); unfold TW.SZ_OW; lia).
assert (GOTimg : forall a, TA_GOT <= a < TA_GOT + 224 -> in_img segs a)
  by (intros a Ha; apply trans_g_img, (op3_inG_row _ _ _ a TMAP_A_GOT); unfold TW.SZ_GOT; lia).
assert (KI : forall a, l_p cx <= a < l_p cx + l_n cx -> aview segs (w_H W) mem4 a = aview segs (w_H W) mem0 a).
{ intros a Ha. apply KA4; [lia | intros Hx; exact (NIMG a Ha (OWimg a Hx)) | intros Hx; exact (NIMG a Ha (GOTimg a Hx))
  | lia]. }
assert (HIN4 : garr8 segs (mrestrict (w_H W) mem4) (l_p cx) (map (fun b : byte => bv_unsigned b) (l_pl cx))).
{ apply (garr8_frame segs _ _ _ _ HIN). intros a Ha. apply (mbyte_of_aview segs). apply KI.
  rewrite length_map in Ha. lia. }
assert (V176 : val_mem segs (mrestrict (w_H W) mem4) (lc_sp1 cx + 176) 8 (transport_hi 9)).
{ apply val_mem_of_rdword. rewrite <- S176. apply rdword_ext. intros k Hk. apply KA4; unfold TA_OW, TA_GOT; lia. }
assert (V184 : val_mem segs (mrestrict (w_H W) mem4) (lc_sp1 cx + 184) 8 TA_M).
{ apply val_mem_of_rdword. rewrite <- S184. apply rdword_ext. intros k Hk. apply KA4; unfold TA_OW, TA_GOT; lia. }
pose proof (tw_read_val segs (mrestrict (w_H W) mem4) TMAP_A (op3_w2 Bw0) TW.OFF_g_fail_next TA_g_fail_next 1 0 1
  TMAP_A_ok HT4 TMAP_A_g_fail_next ltac:(lia) ltac:(cbn; lia)) as VGF.
replace (TA_g_fail_next + 0) with TA_g_fail_next in VGF by lia.
pose proof (tw_read_val segs (mrestrict (w_H W) mem4) TMAP_A (op3_w2 Bw0) TW.OFF_g_now TA_g_now TW.SZ_g_now 0 8
  TMAP_A_ok HT4 TMAP_A_g_now ltac:(lia) ltac:(unfold TW.SZ_g_now; cbn; lia)) as VNW.
replace (TA_g_now + 0) with TA_g_now in VNW by lia.
change (TW.u_at (op3_w2 Bw0) (TW.OFF_g_fail_next + 0) 1) with (op3_gf Bw0) in VGF.
change (TW.u_at (op3_w2 Bw0) (TW.OFF_g_now + 0) 8) with (op3_now Bw0) in VNW.
assert (RGF : 0 <= op3_gf Bw0 < 256) by (pose proof (TWL.u_at_range (op3_w2 Bw0) (TW.OFF_g_fail_next + 0) 1) as H;
  exact H).
assert (RNW : 0 <= op3_now Bw0 < 2 ^ 64) by (pose proof (TWL.u_at_range (op3_w2 Bw0) (TW.OFF_g_now + 0) 8) as H;
  exact H).
pose proof lf_spill_pages as (_ & P9 & P10 & _).
assert (HNW : transport_hi 9 + -1052 = TA_g_now) by (rewrite P9; reflexivity).
destruct (al_shadow segs B LAWS ly S W mem4 md4 (l_p cx) (l_n cx) HAR4 HBLK) as (BSH & _).
pose proof (@paj_run_x (l_fx cx) rc AE2k.tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUN.
pose proof (@paj_run_to_x (l_fx cx) rc AE2k.tfib_sink_head transport_listing PL_transport PI_transport B LAWS
  TG.G_HARNESS HGX 0 []) as RUNTO.
pose proof (@paj_branch (l_fx cx) rc transport_listing PI_transport) as BR.
assert (Hm : n2 = 0 \/ n2 = 1 \/ 2 <= n2) by lia.
destruct Hm as [Hm | [Hm | Hm]].

- (* no byte left: t = 0 *)
  subst n2.
  assert (EU : TOP.fuzz_u16_m (l_pl cx) (TOP.FuzzIn o2 0) = (TOP.FuzzIn o2 0, 0)) by reflexivity.
  rewrite EU. cbn [fst snd TOP.fi_off TOP.fi_n].
  pose proof (@op3_seat2 (l_fx cx) rc W regs4 mem4 0 (op3_gf Bw0) (op3_now Bw0) 0 0 (l_p cx + o2) (lc_sp1 cx)
    ltac:(lia) K26 R24 K9 K20 R22 ltac:(lia) ltac:(lia) ltac:(lia) Hsp1a RGF RNW ltac:(lia) ltac:(lia) VGF VNW V176 V184
    ltac:(intros Hx; exfalso; lia) ltac:(intros Hx; exfalso; lia) ltac:(intros Hx; exfalso; lia)
    ltac:(intros Hx; exfalso; lia) ltac:(intros Hx; exfalso; lia)) as HS.
  pose proof (op3_shok2 B ly S W mem4 md4 regs4 (op3_gf Bw0) (op3_now Bw0) 0 0 0 (l_p cx + o2) HAR4 ltac:(lia) K26 R24
    ltac:(lia) ltac:(lia) ltac:(intros Hx; exfalso; lia) ltac:(intros x Hx; exfalso; lia)) as SHOK.

  set (E := op3_E2 regs4 (op3_gf Bw0) (op3_now Bw0) 0 0) in HS, SHOK.
  assert (HEI : img_env VAL A_LIM E) by (unfold E, op3_E2; apply Eimg_env).
  assert (U22 : bv_unsigned (ew E 22) = TA_OW)
    by (unfold E; rewrite (op3_E2_reg _ _ _ _ _ 22 22%bv eq_refl), R22; unfold w64; apply unsigned_lit_small;
        unfold TA_OW; lia).
  assert (E23 : ew E 23 = Z_to_bv 64 0) by (unfold E; rewrite (op3_E2_reg _ _ _ _ _ 23 23%bv eq_refl), R23; reflexivity).
  assert (E24 : ew E 24 = Z_to_bv 64 (l_p cx + o2))
    by (unfold E; rewrite (op3_E2_reg _ _ _ _ _ 24 24%bv eq_refl), R24; reflexivity).
  assert (E19 : ew E 19 = Z_to_bv 64 scale) by (unfold E; rewrite (op3_E2_reg _ _ _ _ _ 19 19%bv eq_refl), R19; reflexivity).
  assert (E32 : ew E 32 = Z_to_bv 64 (op3_gf Bw0)) by exact (op3_E2_x regs4 _ _ _ _ 0 ltac:(lia)).
  assert (E33 : ew E 33 = Z_to_bv 64 TA_M) by exact (op3_E2_x regs4 _ _ _ _ 1 ltac:(lia)).
  assert (E34 : ew E 34 = Z_to_bv 64 (transport_hi 9)) by exact (op3_E2_x regs4 _ _ _ _ 2 ltac:(lia)).
  assert (E35 : ew E 35 = Z_to_bv 64 (op3_now Bw0)) by exact (op3_E2_x regs4 _ _ _ _ 3 ltac:(lia)).
  assert (E36 : ew E 36 = Z_to_bv 64 0) by exact (op3_E2_x regs4 _ _ _ _ 4 ltac:(lia)).
  assert (E37 : ew E 37 = Z_to_bv 64 0) by exact (op3_E2_x regs4 _ _ _ _ 5 ltac:(lia)).
  assert (U33 : bv_unsigned (ew E 33) = TA_M) by (rewrite E33; apply unsigned_lit_small; unfold TA_M; lia).
  assert (U34 : bv_unsigned (ew E 34) = transport_hi 9) by (rewrite E34, P9; apply unsigned_lit_small; lia).

  (* +0x7a4 .. +0x7b8: OW.desk_off = -1, M.fail = g_fail_next, `beqz s7` *)
  paj_run_tok RUN HS HJ SHOK Bspan; [op3_awr_g U22 U33 U34 HNW|].
  op3_kf HFr U22 U33 U34 HNW K1.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  2: { op3_refute Hc E23. }
  clear Hc.
  (* +0x818 .. +0x96c: t = 0, g_now += 0 *)
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x970; [op3_awr_g U22 U33 U34 HNW|].
  op3_kf HFr0 U22 U33 U34 HNW K2.

  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (Ef := Ex) in * end.
  assert (Elo : forall n, (n < 1024)%nat -> ew Ef n = ew E n)
    by (intros n Hn; unfold Ef; repeat rewrite ew_ewset_other by lia; reflexivity).
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
  pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RG3. cbn [ms_mem restrict] in RG3.
  pose proof (st_ok_pi_region_nth _ _ _ 4 _ HS eq_refl) as RG4. cbn [ms_mem restrict] in RG4.
  pose proof (op3_chunk_rd Ef (w_H W) _ 22 TA_OW _ _ _ _ 232 4%N (SLit 18446744073709551615) 18446744073709551615 RG1
    ltac:(rewrite Elo by lia; exact U22) eq_refl ltac:(cbn; lia)) as VOW.
  pose proof (op3_chunk_rd Ef (w_H W) _ 33 TA_M _ _ _ _ 88 4%N (SOff 32 0) (op3_gf Bw0) RG3
    ltac:(rewrite Elo by lia; exact U33) ltac:(apply op3_den_atom; rewrite Elo by lia; exact E32) ltac:(cbn; lia)) as VM.
  pose proof (op3_chunk_rd Ef (w_H W) _ 34 (transport_hi 9) _ _ _ _ (-1052) 8%N _ (op3_now Bw0 + 0 * scale) RG4
    ltac:(rewrite Elo by lia; exact U34) ltac:(rewrite Z.mul_0_l, Z.add_0_r; apply op3_den_atom; rewrite Elo by lia; exact E35) ltac:(cbn; lia)) as VN.
  rewrite HNW in VN. cbn [N.to_nat Pos.to_nat] in VOW, VM, VN.
  op3_rd HS (22%bv : bv 5) X22. op3_rd HS (24%bv : bv 5) X24. op3_rd HS (23%bv : bv 5) X23.
  assert (KRf : forall r, In r op3_keep -> YK11.getr (ms_regs ms0) r = YK11.getr regs0 r).
  { intros r Hr. rewrite <- (KR r Hr).
    refine (regs_kept_of_st_ok segs Ef _ (restrict (w_H W) ms0) regs4 _ op3_keep HS _
      ltac:(vm_compute; reflexivity) r Hr).
    split; [intros n Hn; rewrite Elo by lia; unfold E, op3_E2; rewrite Eimg_low by (unfold A_TEXT; lia);
            reflexivity | reflexivity]. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ _ ?pc _ _) _) _ =>
    assert (EPC2 : pc = w64 (transport_text + LO_TICK)) by (unfold w64; f_equal; vm_compute; reflexivity);
    rewrite EPC2 end.
  apply SRr_ret.
  apply (op3_B_end B FP cx ly S W regs0 mem0 e Bw0 scale 0 o2 0 mem4 (ms_regs ms0) (ms_mem ms0) _ HT0
    ltac:(lia) ZO ZG KA4 GA4).
  + intros a Ha H1 H2 H3. rewrite K2 by (first [exact Ha | unfold op3_Zs; tauto]). rewrite K1 by (first [exact Ha | unfold op3_Zs; tauto]). reflexivity.
  + intros a Ha. apply (apresent_grows _ _ _ a HG0). apply (apresent_grows _ _ _ a HG). exact Ha.
  + intros j Hj. rewrite <- op3_le_m1 by exact Hj. exact (VOW j Hj).
  + exact VM.
  + exact VN.
  + unfold op3_J. exact HJ.
  + rewrite X22. rewrite Z.mul_0_l, Z.add_0_r. apply op3_den_atom. rewrite Elo by lia. exact E35.
  + rewrite X24. apply op3_den_atom. rewrite Elo by lia. exact E24.
  + rewrite X23. apply op3_den_atom. rewrite Elo by lia. exact E23.
  + exact KRf.

- (* one byte left: t = the byte *)
  subst n2.
  assert (U1 : TOP.fuzz_u8_m (l_pl cx) (TOP.FuzzIn o2 1) =
    (TOP.FuzzIn (o2 + 1) (1 - 1), DSpec.at8 (l_pl cx) (Z.to_nat o2))) by reflexivity.
  assert (U2 : TOP.fuzz_u8_m (l_pl cx) (TOP.FuzzIn (o2 + 1) (1 - 1)) = (TOP.FuzzIn (o2 + 1) (1 - 1), 0))
    by reflexivity.
  set (lo := DSpec.at8 (l_pl cx) (Z.to_nat o2)) in *.
  assert (EU : TOP.fuzz_u16_m (l_pl cx) (TOP.FuzzIn o2 1) = (TOP.FuzzIn (o2 + 1) 0, lo)).
  { unfold TOP.fuzz_u16_m. rewrite U1. cbv beta iota. rewrite U2. cbv beta iota. f_equal.
    rewrite Z.shiftl_0_l, Z.lor_0_r. apply Z.mod_small. pose proof (op3_at8_range (l_pl cx) (Z.to_nat o2)). unfold lo. lia. }
  rewrite EU. cbn [fst snd TOP.fi_off TOP.fi_n].

  pose proof (garr8_nthZ segs _ _ _ o2 HIN4 Ho2 ltac:(rewrite length_map; lia)) as (VLO & RLO).
  rewrite op3_nth_map in VLO, RLO.
  replace (l_p cx + o2) with (l_p cx + o2) in VLO by reflexivity.
  assert (NI : forall j, 0 <= j < 1 -> ~ in_img segs (l_p cx + o2 + j)) by (intros j Hj; apply NIMG; lia).
  pose proof (op3_apart_row _ _ _ (l_p cx + o2) 1 (TA_M + 88) (TA_M + 92) TMAP_A_M
    ltac:(lia) ltac:(unfold TW.SZ_M; lia) ltac:(lia) ltac:(lia) NI) as DM.
  pose proof (op3_apart_row _ _ _ (l_p cx + o2) 1 (TA_OW + 232) (TA_OW + 236) TMAP_A_OW
    ltac:(lia) ltac:(unfold TW.SZ_OW; lia) ltac:(lia) ltac:(lia) NI) as DOW.
  pose proof (op3_apart_img (l_p cx + o2) 1 TA_g_now (TA_g_fail_next + 1) ltac:(lia) ltac:(vm_compute; reflexivity)
    NI op3_gnow_img) as D1.
  pose proof (@op3_seat2 (l_fx cx) rc W regs4 mem4 1 (op3_gf Bw0) (op3_now Bw0) lo 0 (l_p cx + o2) (lc_sp1 cx)
    ltac:(lia) K26 R24 K9 K20 R22 ltac:(lia) ltac:(lia) ltac:(lia) Hsp1a RGF RNW RLO ltac:(lia) VGF VNW V176 V184
    (fun _ => VLO) ltac:(intros Hx; exfalso; lia)
    (fun _ => D1) (fun _ => DM) (fun _ => DOW)) as HS.
  pose proof (op3_shok2 B ly S W mem4 md4 regs4 (op3_gf Bw0) (op3_now Bw0) lo 0 1 (l_p cx + o2) HAR4 ltac:(lia)
    K26 R24 ltac:(lia) ltac:(lia)
    ltac:(intros _; exact (op3_block_ra _ (l_p cx) (l_n cx) (l_p cx + o2) 1 BSH ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)))
    ltac:(intros x Hx; unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia)) as SHOK.

  set (E := op3_E2 regs4 (op3_gf Bw0) (op3_now Bw0) lo 0) in HS, SHOK.
  assert (HEI : img_env VAL A_LIM E) by (unfold E, op3_E2; apply Eimg_env).
  assert (U22 : bv_unsigned (ew E 22) = TA_OW)
    by (unfold E; rewrite (op3_E2_reg _ _ _ _ _ 22 22%bv eq_refl), R22; unfold w64; apply unsigned_lit_small;
        unfold TA_OW; lia).
  assert (E23 : ew E 23 = Z_to_bv 64 1) by (unfold E; rewrite (op3_E2_reg _ _ _ _ _ 23 23%bv eq_refl), R23; reflexivity).
  assert (E24 : ew E 24 = Z_to_bv 64 (l_p cx + o2))
    by (unfold E; rewrite (op3_E2_reg _ _ _ _ _ 24 24%bv eq_refl), R24; reflexivity).
  assert (E19 : ew E 19 = Z_to_bv 64 scale) by (unfold E; rewrite (op3_E2_reg _ _ _ _ _ 19 19%bv eq_refl), R19; reflexivity).
  assert (E32 : ew E 32 = Z_to_bv 64 (op3_gf Bw0)) by exact (op3_E2_x regs4 _ _ _ _ 0 ltac:(lia)).
  assert (E33 : ew E 33 = Z_to_bv 64 TA_M) by exact (op3_E2_x regs4 _ _ _ _ 1 ltac:(lia)).
  assert (E34 : ew E 34 = Z_to_bv 64 (transport_hi 9)) by exact (op3_E2_x regs4 _ _ _ _ 2 ltac:(lia)).
  assert (E35 : ew E 35 = Z_to_bv 64 (op3_now Bw0)) by exact (op3_E2_x regs4 _ _ _ _ 3 ltac:(lia)).
  assert (E36 : ew E 36 = Z_to_bv 64 lo) by exact (op3_E2_x regs4 _ _ _ _ 4 ltac:(lia)).
  assert (E37 : ew E 37 = Z_to_bv 64 0) by exact (op3_E2_x regs4 _ _ _ _ 5 ltac:(lia)).
  assert (U33 : bv_unsigned (ew E 33) = TA_M) by (rewrite E33; apply unsigned_lit_small; unfold TA_M; lia).
  assert (U34 : bv_unsigned (ew E 34) = transport_hi 9) by (rewrite E34, P9; apply unsigned_lit_small; lia).

  paj_run_tok RUN HS HJ SHOK Bspan; [op3_awr_g U22 U33 U34 HNW|].
  op3_kf HFr U22 U33 U34 HNW K1.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  1: { op3_refute Hc E23. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [op3_awr_g U22 U33 U34 HNW|].
  op3_kf HFr0 U22 U33 U34 HNW K2.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  1: { op3_refute Hc E23. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x970; [op3_awr_g U22 U33 U34 HNW|].
  op3_kf HFr1 U22 U33 U34 HNW K3.

  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (Ef := Ex) in * end.
  assert (Elo : forall n, (n < 1024)%nat -> ew Ef n = ew E n)
    by (intros n Hn; unfold Ef; repeat rewrite ew_ewset_other by lia; reflexivity).
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
  pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RG3. cbn [ms_mem restrict] in RG3.
  pose proof (st_ok_pi_region_nth _ _ _ 4 _ HS eq_refl) as RG4. cbn [ms_mem restrict] in RG4.
  pose proof (op3_chunk_rd Ef (w_H W) _ 22 TA_OW _ _ _ _ 232 4%N (SLit 18446744073709551615) 18446744073709551615 RG1
    ltac:(rewrite Elo by lia; exact U22) eq_refl ltac:(cbn; lia)) as VOW.
  pose proof (op3_chunk_rd Ef (w_H W) _ 33 TA_M _ _ _ _ 88 4%N (SOff 32 0) (op3_gf Bw0) RG3
    ltac:(rewrite Elo by lia; exact U33) ltac:(apply op3_den_atom; rewrite Elo by lia; exact E32) ltac:(cbn; lia)) as VM.
  pose proof (op3_chunk_rd Ef (w_H W) _ 34 (transport_hi 9) _ _ _ _ (-1052) 8%N _ (op3_now Bw0 + lo * scale) RG4
    ltac:(rewrite Elo by lia; exact U34) ltac:(apply op3_den_madd; [apply op3_den_or0; rewrite Elo by lia; exact E36 | rewrite Elo by lia; exact E19 | rewrite Elo by lia; exact E35]) ltac:(cbn; lia)) as VN.
  rewrite HNW in VN. cbn [N.to_nat Pos.to_nat] in VOW, VM, VN.
  op3_rd HS (22%bv : bv 5) X22. op3_rd HS (24%bv : bv 5) X24. op3_rd HS (23%bv : bv 5) X23.
  assert (KRf : forall r, In r op3_keep -> YK11.getr (ms_regs ms1) r = YK11.getr regs0 r).
  { intros r Hr. rewrite <- (KR r Hr).
    refine (regs_kept_of_st_ok segs Ef _ (restrict (w_H W) ms1) regs4 _ op3_keep HS _
      ltac:(vm_compute; reflexivity) r Hr).
    split; [intros n Hn; rewrite Elo by lia; unfold E, op3_E2; rewrite Eimg_low by (unfold A_TEXT; lia);
            reflexivity | reflexivity]. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ _ ?pc _ _) _) _ =>
    assert (EPC2 : pc = w64 (transport_text + LO_TICK)) by (unfold w64; f_equal; vm_compute; reflexivity);
    rewrite EPC2 end.
  apply SRr_ret.
  apply (op3_B_end B FP cx ly S W regs0 mem0 e Bw0 scale lo (o2 + 1) 0 mem4 (ms_regs ms1) (ms_mem ms1) _ HT0
    ltac:(lia) ZO ZG KA4 GA4).
  + intros a Ha H1 H2 H3. rewrite K3 by (first [exact Ha | unfold op3_Zs; tauto]). rewrite K2 by (first [exact Ha | unfold op3_Zs; tauto]). rewrite K1 by (first [exact Ha | unfold op3_Zs; tauto]). reflexivity.
  + intros a Ha. apply (apresent_grows _ _ _ a HG1). apply (apresent_grows _ _ _ a HG0). apply (apresent_grows _ _ _ a HG). exact Ha.
  + intros j Hj. rewrite <- op3_le_m1 by exact Hj. exact (VOW j Hj).
  + exact VM.
  + exact VN.
  + unfold op3_J. exact HJ.
  + rewrite X22. apply op3_den_madd; [apply op3_den_or0; rewrite Elo by lia; exact E36 | rewrite Elo by lia; exact E19 | rewrite Elo by lia; exact E35].
  + rewrite X24. rewrite (op3_den_off Ef 24 1 (l_p cx + o2)) by (rewrite Elo by lia; rewrite E24; apply unsigned_lit_small; lia). unfold w64. f_equal. lia.
  + rewrite X23. reflexivity.
  + exact KRf.

- (* two bytes or more left: t = lo + 256 hi *)
  assert (U1 : TOP.fuzz_u8_m (l_pl cx) (TOP.FuzzIn o2 n2) =
    (TOP.FuzzIn (o2 + 1) (n2 - 1), DSpec.at8 (l_pl cx) (Z.to_nat o2))).
  { unfold TOP.fuzz_u8_m. cbn [TOP.fi_n TOP.fi_off]. rewrite (proj2 (Z.eqb_neq n2 0)) by lia. reflexivity. }
  assert (U2 : TOP.fuzz_u8_m (l_pl cx) (TOP.FuzzIn (o2 + 1) (n2 - 1)) =
    (TOP.FuzzIn (o2 + 1 + 1) (n2 - 1 - 1), DSpec.at8 (l_pl cx) (Z.to_nat (o2 + 1)))).
  { unfold TOP.fuzz_u8_m. cbn [TOP.fi_n TOP.fi_off]. rewrite (proj2 (Z.eqb_neq (n2 - 1) 0)) by lia. reflexivity. }
  set (lo := DSpec.at8 (l_pl cx) (Z.to_nat o2)) in *.
  set (hi := DSpec.at8 (l_pl cx) (Z.to_nat (o2 + 1))) in *.
  pose proof (op3_at8_range (l_pl cx) (Z.to_nat o2)) as RL0. pose proof (op3_at8_range (l_pl cx) (Z.to_nat (o2 + 1))) as RH0.
  fold lo in RL0. fold hi in RH0.
  assert (EU : TOP.fuzz_u16_m (l_pl cx) (TOP.FuzzIn o2 n2) = (TOP.FuzzIn (o2 + 2) (n2 - 2), hi * 2 ^ 8 + lo)).
  { unfold TOP.fuzz_u16_m. rewrite U1. cbv beta iota. rewrite U2. cbv beta iota. f_equal; [f_equal; lia|].
    rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.lor_comm, op3_lor8 by lia. apply Z.mod_small. lia. }
  rewrite EU. cbn [fst snd TOP.fi_off TOP.fi_n].
  pose proof (garr8_nthZ segs _ _ _ (o2 + 1) HIN4 ltac:(lia) ltac:(rewrite length_map; lia)) as (VHI & RHI).
  rewrite op3_nth_map in VHI, RHI. fold hi in VHI, RHI.
  replace (l_p cx + (o2 + 1)) with (l_p cx + o2 + 1) in VHI by lia.

  pose proof (garr8_nthZ segs _ _ _ o2 HIN4 Ho2 ltac:(rewrite length_map; lia)) as (VLO & RLO).
  rewrite op3_nth_map in VLO, RLO.
  replace (l_p cx + o2) with (l_p cx + o2) in VLO by reflexivity.
  assert (NI : forall j, 0 <= j < 2 -> ~ in_img segs (l_p cx + o2 + j)) by (intros j Hj; apply NIMG; lia).
  pose proof (op3_apart_row _ _ _ (l_p cx + o2) 2 (TA_M + 88) (TA_M + 92) TMAP_A_M
    ltac:(lia) ltac:(unfold TW.SZ_M; lia) ltac:(lia) ltac:(lia) NI) as DM.
  pose proof (op3_apart_row _ _ _ (l_p cx + o2) 2 (TA_OW + 232) (TA_OW + 236) TMAP_A_OW
    ltac:(lia) ltac:(unfold TW.SZ_OW; lia) ltac:(lia) ltac:(lia) NI) as DOW.
  pose proof (op3_apart_img (l_p cx + o2) 2 TA_g_now (TA_g_fail_next + 1) ltac:(lia) ltac:(vm_compute; reflexivity)
    NI op3_gnow_img) as D1.
  pose proof (@op3_seat2 (l_fx cx) rc W regs4 mem4 2 (op3_gf Bw0) (op3_now Bw0) lo hi (l_p cx + o2) (lc_sp1 cx)
    ltac:(lia) K26 R24 K9 K20 R22 ltac:(lia) ltac:(lia) ltac:(lia) Hsp1a RGF RNW RLO RHI VGF VNW V176 V184
    (fun _ => VLO) (fun _ => VHI)
    (fun _ => D1) (fun _ => DM) (fun _ => DOW)) as HS.
  pose proof (op3_shok2 B ly S W mem4 md4 regs4 (op3_gf Bw0) (op3_now Bw0) lo hi 2 (l_p cx + o2) HAR4 ltac:(lia)
    K26 R24 ltac:(lia) ltac:(lia)
    ltac:(intros _; exact (op3_block_ra _ (l_p cx) (l_n cx) (l_p cx + o2) 2 BSH ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)))
    ltac:(intros x Hx; unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia)) as SHOK.

  set (E := op3_E2 regs4 (op3_gf Bw0) (op3_now Bw0) lo hi) in HS, SHOK.
  assert (HEI : img_env VAL A_LIM E) by (unfold E, op3_E2; apply Eimg_env).
  assert (U22 : bv_unsigned (ew E 22) = TA_OW)
    by (unfold E; rewrite (op3_E2_reg _ _ _ _ _ 22 22%bv eq_refl), R22; unfold w64; apply unsigned_lit_small;
        unfold TA_OW; lia).
  assert (E23 : ew E 23 = Z_to_bv 64 n2) by (unfold E; rewrite (op3_E2_reg _ _ _ _ _ 23 23%bv eq_refl), R23; reflexivity).
  assert (E24 : ew E 24 = Z_to_bv 64 (l_p cx + o2))
    by (unfold E; rewrite (op3_E2_reg _ _ _ _ _ 24 24%bv eq_refl), R24; reflexivity).
  assert (E19 : ew E 19 = Z_to_bv 64 scale) by (unfold E; rewrite (op3_E2_reg _ _ _ _ _ 19 19%bv eq_refl), R19; reflexivity).
  assert (E32 : ew E 32 = Z_to_bv 64 (op3_gf Bw0)) by exact (op3_E2_x regs4 _ _ _ _ 0 ltac:(lia)).
  assert (E33 : ew E 33 = Z_to_bv 64 TA_M) by exact (op3_E2_x regs4 _ _ _ _ 1 ltac:(lia)).
  assert (E34 : ew E 34 = Z_to_bv 64 (transport_hi 9)) by exact (op3_E2_x regs4 _ _ _ _ 2 ltac:(lia)).
  assert (E35 : ew E 35 = Z_to_bv 64 (op3_now Bw0)) by exact (op3_E2_x regs4 _ _ _ _ 3 ltac:(lia)).
  assert (E36 : ew E 36 = Z_to_bv 64 lo) by exact (op3_E2_x regs4 _ _ _ _ 4 ltac:(lia)).
  assert (E37 : ew E 37 = Z_to_bv 64 hi) by exact (op3_E2_x regs4 _ _ _ _ 5 ltac:(lia)).
  assert (U33 : bv_unsigned (ew E 33) = TA_M) by (rewrite E33; apply unsigned_lit_small; unfold TA_M; lia).
  assert (U34 : bv_unsigned (ew E 34) = transport_hi 9) by (rewrite E34, P9; apply unsigned_lit_small; lia).

  paj_run_tok RUN HS HJ SHOK Bspan; [op3_awr_g U22 U33 U34 HNW|].
  op3_kf HFr U22 U33 U34 HNW K1.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  1: { op3_refute Hc E23. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [op3_awr_g U22 U33 U34 HNW|].
  op3_kf HFr0 U22 U33 U34 HNW K2.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  2: { op3_refute Hc E23. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x970; [op3_awr_g U22 U33 U34 HNW|].
  op3_kf HFr1 U22 U33 U34 HNW K3.

  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (Ef := Ex) in * end.
  assert (Elo : forall n, (n < 1024)%nat -> ew Ef n = ew E n)
    by (intros n Hn; unfold Ef; repeat rewrite ew_ewset_other by lia; reflexivity).
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
  pose proof (st_ok_pi_region_nth _ _ _ 3 _ HS eq_refl) as RG3. cbn [ms_mem restrict] in RG3.
  pose proof (st_ok_pi_region_nth _ _ _ 4 _ HS eq_refl) as RG4. cbn [ms_mem restrict] in RG4.
  pose proof (op3_chunk_rd Ef (w_H W) _ 22 TA_OW _ _ _ _ 232 4%N (SLit 18446744073709551615) 18446744073709551615 RG1
    ltac:(rewrite Elo by lia; exact U22) eq_refl ltac:(cbn; lia)) as VOW.
  pose proof (op3_chunk_rd Ef (w_H W) _ 33 TA_M _ _ _ _ 88 4%N (SOff 32 0) (op3_gf Bw0) RG3
    ltac:(rewrite Elo by lia; exact U33) ltac:(apply op3_den_atom; rewrite Elo by lia; exact E32) ltac:(cbn; lia)) as VM.
  pose proof (op3_chunk_rd Ef (w_H W) _ 34 (transport_hi 9) _ _ _ _ (-1052) 8%N _ (op3_now Bw0 + (hi * 2 ^ 8 + lo) * scale) RG4
    ltac:(rewrite Elo by lia; exact U34) ltac:(apply op3_den_madd; [apply op3_den_or8; first [rewrite Elo by lia; first [exact E37 | exact E36] | lia] | rewrite Elo by lia; exact E19 | rewrite Elo by lia; exact E35]) ltac:(cbn; lia)) as VN.
  rewrite HNW in VN. cbn [N.to_nat Pos.to_nat] in VOW, VM, VN.
  op3_rd HS (22%bv : bv 5) X22. op3_rd HS (24%bv : bv 5) X24. op3_rd HS (23%bv : bv 5) X23.
  assert (KRf : forall r, In r op3_keep -> YK11.getr (ms_regs ms1) r = YK11.getr regs0 r).
  { intros r Hr. rewrite <- (KR r Hr).
    refine (regs_kept_of_st_ok segs Ef _ (restrict (w_H W) ms1) regs4 _ op3_keep HS _
      ltac:(vm_compute; reflexivity) r Hr).
    split; [intros n Hn; rewrite Elo by lia; unfold E, op3_E2; rewrite Eimg_low by (unfold A_TEXT; lia);
            reflexivity | reflexivity]. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ _ ?pc _ _) _) _ =>
    assert (EPC2 : pc = w64 (transport_text + LO_TICK)) by (unfold w64; f_equal; vm_compute; reflexivity);
    rewrite EPC2 end.
  apply SRr_ret.
  apply (op3_B_end B FP cx ly S W regs0 mem0 e Bw0 scale (hi * 2 ^ 8 + lo) (o2 + 2) (n2 - 2) mem4 (ms_regs ms1) (ms_mem ms1) _ HT0
    ltac:(lia) ZO ZG KA4 GA4).
  + intros a Ha H1 H2 H3. rewrite K3 by (first [exact Ha | unfold op3_Zs; tauto]). rewrite K2 by (first [exact Ha | unfold op3_Zs; tauto]). rewrite K1 by (first [exact Ha | unfold op3_Zs; tauto]). reflexivity.
  + intros a Ha. apply (apresent_grows _ _ _ a HG1). apply (apresent_grows _ _ _ a HG0). apply (apresent_grows _ _ _ a HG). exact Ha.
  + intros j Hj. rewrite <- op3_le_m1 by exact Hj. exact (VOW j Hj).
  + exact VM.
  + exact VN.
  + unfold op3_J. exact HJ.
  + rewrite X22. apply op3_den_madd; [apply op3_den_or8; first [rewrite Elo by lia; first [exact E37 | exact E36] | lia] | rewrite Elo by lia; exact E19 | rewrite Elo by lia; exact E35].
  + rewrite X24. rewrite (op3_den_off Ef 24 2 (l_p cx + o2)) by (rewrite Elo by lia; rewrite E24; apply unsigned_lit_small; lia). unfold w64. f_equal. lia.
  + rewrite X23. rewrite (op3_den_off Ef 23 (-2) n2) by (rewrite Elo by lia; rewrite E23; apply unsigned_lit_small; lia). unfold w64. f_equal.
  + exact KRf.
Qed.
End b2.

(* ------------------------------------------------------------------ *)
(* 9. The model: op_begin's world and lc_tick_w                         *)
(* ------------------------------------------------------------------ *)

Lemma op3_scale_range : forall i, 0 <= nth i TOP.LLVMFuzzerTestOneInput_SCALE 0 < 2 ^ 64.
Proof. intros [|[|[|[|i]]]]; cbn; [lia | lia | lia | lia | destruct i; lia]. Qed.

Lemma op3_w2_eq : forall Bw,
  TW.upd (TW.upd Bw TW.OFF_OW (repeat (DSpec.b8 0) (Z.to_nat TW.SZ_OW))) TW.OFF_GOT
    (repeat (DSpec.b8 0) (Z.to_nat TW.SZ_GOT)) = op3_w2 Bw.
Proof. intros Bw. unfold op3_w2. rewrite !Z.add_0_r. reflexivity. Qed.

Lemma op3_model : forall (Bw D : list byte) (c1 c2 : TOP.fuzz_in) (sb : Z),
  length Bw = Z.to_nat TW.W_LEN -> TOP.fuzz_u8_m D c1 = (c2, sb) ->
  exists B1, TC.op_begin_m Bw = Some (B1, tt) /\
    lc_tick_w D c1 B1 = op3_wF Bw (nth (Z.to_nat (sb mod 4)) TOP.LLVMFuzzerTestOneInput_SCALE 0)
      (snd (TOP.fuzz_u16_m D c2)) /\
    TW.g_now (lc_tick_w D c1 B1) =
      (op3_now Bw + snd (TOP.fuzz_u16_m D c2) * nth (Z.to_nat (sb mod 4)) TOP.LLVMFuzzerTestOneInput_SCALE 0)
        mod 2 ^ 64 /\
    lc_tick_c D c1 = fst (TOP.fuzz_u16_m D c2).
Proof.
intros Bw D c1 c2 sb HL HU.
assert (C : TW.W_LEN = 65616 /\ TW.OFF_OW = 65312 /\ TW.OFF_GOT = 65084 /\ TW.OFF_M = 0 /\ TW.OFF_g_now = 65000 /\
  TW.OFF_g_fail_next = 64968) by (repeat split; reflexivity).
destruct C as (CW & COW & CGOT & CM & CN & CF).
assert (P4 : forall v, Z.of_nat (length (TW.put 4 v)) = 4) by (intros v; rewrite TWL.length_put; reflexivity).
assert (P8 : forall v, Z.of_nat (length (TW.put 8 v)) = 8) by (intros v; rewrite TWL.length_put; reflexivity).
assert (LW : Z.of_nat (length Bw) = TW.W_LEN) by (rewrite HL, CW; reflexivity).
assert (L1' : Z.of_nat (length (TW.upd Bw (TW.OFF_OW + 0) (repeat (Z_to_bv 8 0) 304))) = TW.W_LEN).
{ rewrite TWL.length_upd; [exact LW | lia |].
  change (Z.of_nat (length (repeat (Z_to_bv 8 0) 304))) with 304. lia. }
assert (L2 : Z.of_nat (length (op3_w2 Bw)) = TW.W_LEN).
{ unfold op3_w2. rewrite TWL.length_upd; [exact L1' | lia |].
  change (Z.of_nat (length (repeat (Z_to_bv 8 0) 224))) with 224. lia. }
set (scale := nth (Z.to_nat (sb mod 4)) TOP.LLVMFuzzerTestOneInput_SCALE 0).
set (t := snd (TOP.fuzz_u16_m D c2)).
set (B3 := TW.set_OW_desk_off (op3_w2 Bw) (-1)).
assert (L3 : Z.of_nat (length B3) = TW.W_LEN).
{ unfold B3, TW.set_OW_desk_off, TW.A_OW_desk_off. rewrite TWL.length_upd_put; [exact L2 | lia | lia]. }
assert (GF : TW.g_fail_next B3 = op3_gf Bw).
{ unfold TW.g_fail_next, op3_gf, B3, TW.set_OW_desk_off, TW.A_OW_desk_off. rewrite (Z.add_0_r TW.OFF_g_fail_next).
  apply TWL.u_at_upd_out; [lia | lia | rewrite P4; cbn [Z.of_nat Pos.of_succ_nat]; lia | rewrite P4; lia]. }
set (B1 := TW.set_M_fail B3 (op3_gf Bw)).
assert (NW : TW.g_now B1 = op3_now Bw).
{ unfold TW.g_now, op3_now, B1, TW.set_M_fail, TW.A_M_fail.
  rewrite TWL.u_at_upd_out; [| lia | lia | rewrite P4; cbn [Z.of_nat Pos.of_succ_nat]; lia | rewrite P4; lia].
  unfold B3, TW.set_OW_desk_off, TW.A_OW_desk_off. rewrite (Z.add_0_r TW.OFF_g_now).
  apply TWL.u_at_upd_out; [lia | lia | rewrite P4; cbn [Z.of_nat Pos.of_succ_nat]; lia | rewrite P4; lia]. }
assert (WF : lc_tick_w D c1 B1 = op3_wF Bw scale t).
{ unfold lc_tick_w. rewrite HU. cbv beta iota zeta. fold scale.
  destruct (TOP.fuzz_u16_m D c2) as [c3 t3] eqn:E16. unfold t. try rewrite E16. cbn [snd].
  unfold TW.set_g_now, op3_wF. rewrite NW, TWL.put_mod64 by lia. rewrite (Z.add_0_r TW.OFF_g_now).
  unfold B1, B3, TW.set_M_fail, TW.A_M_fail, TW.set_OW_desk_off, TW.A_OW_desk_off.
  f_equal. f_equal. ring. }
exists B1. split.
- unfold TC.op_begin_m. rewrite op3_w2_eq. fold B3. rewrite GF. reflexivity.
- split; [exact WF|]. split.
  + rewrite WF. unfold TW.g_now, op3_wF.
    assert (L4 : Z.of_nat (length (TW.upd (TW.upd (op3_w2 Bw) (TW.OFF_OW + 232) (TW.put 4 (-1))) (TW.OFF_M + 88)
      (TW.put 4 (op3_gf Bw)))) = TW.W_LEN).
    { rewrite !TWL.length_upd_put; [exact L2 | lia | lia | lia | rewrite TWL.length_upd_put; [lia | lia | lia]]. }
    rewrite (Z.add_0_r TW.OFF_g_now). rewrite TWL.u_at_upd_put; [reflexivity | lia | lia].
  + unfold lc_tick_c. rewrite HU. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 10. The segment                                                      *)
(* ------------------------------------------------------------------ *)

Section top. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.

(* lc_core reads sp, gp, tp, s0 and s1 only. *)
Lemma op3_core_regs : forall cx ly S W regs regs2 mem md e,
  @lc_core rc B cx ly S W regs mem md e ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9]%bv -> YK11.getr regs2 r = YK11.getr regs r) ->
  @lc_core rc B cx ly S W regs2 mem md e.
Proof.
intros cx ly S W regs regs2 mem md e HC KR. unfold lc_core in *.
destruct HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hrest).
rewrite <- (KR 2%bv) in Rsp by (cbn; tauto). rewrite <- (KR 8%bv) in R8 by (cbn; tauto).
rewrite <- (KR 9%bv) in R9 by (cbn; tauto). rewrite <- (KR 3%bv) in Rgp by (cbn; tauto).
rewrite <- (KR 4%bv) in Rtp by (cbn; tauto).
exact (conj HJ (conj Hfrs (conj HlyF (conj HPERM (conj Rsp (conj R8 (conj R9 (conj Rgp (conj Rtp Hrest))))))))).
Qed.

(* The arm's first run lands at the call of __asan_memset (OW) with the scale byte read (if any) and SCALE's entry. *)
Lemma op3_A1 : forall (HP : @lp_prem rc B MT XL RLO RHI) cx op ly S W regs mem md e,
  @lc_base rc B MT XL RLO RHI cx -> @lc_core rc B cx ly S W regs mem md e -> trans_rom_view_rd W mem ->
  lc_opok cx op -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  lc_cur cx regs 25 27 (lo_c op) -> lc_cur cx regs 24 23 (lc_oc (l_pl cx) (lo_c op)) ->
  exists sb o2 n2, TOP.fuzz_u8_m (l_pl cx) (lc_oc (l_pl cx) (lo_c op)) = (TOP.FuzzIn o2 n2, sb) /\
    0 <= o2 /\ 0 <= n2 /\ o2 + n2 = l_n cx /\
    SRr segs W (lc_cfg cx 0x5b4 regs mem md)
      (op3_PA B [] cx ly S W regs mem e (nth (Z.to_nat (sb mod 4)) TOP.LLVMFuzzerTestOneInput_SCALE 0) o2 n2).
Proof.
intros HP cx op ly S W regs mem md e HB HC HR Hopok R26 Hcur0 Hcur1.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HC as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HIN).
pose proof (lc_geom B MT XL RLO RHI cx ly S W regs mem md e HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof Hopok as (_ & _ & Hfin & Hn0 & _).
pose proof ASAN_CEIL_range as (CL & _). unfold ASAN_CEIL in CL.
destruct (lo_c op) as [o0 n0] eqn:Ec0. cbn [TOP.fi_off TOP.fi_n] in *.
destruct Hfin as (Ho0 & Hn0' & Hon0). cbn [TOP.fi_off TOP.fi_n] in Ho0, Hn0', Hon0.
destruct Hn as (Hn & HnD).
assert (EC1 : lc_oc (l_pl cx) (TOP.FuzzIn o0 n0) = TOP.FuzzIn (o0 + 1) (n0 - 1)).
{ unfold lc_oc, TOP.fuzz_u8_m. cbn [TOP.fi_off TOP.fi_n]. rewrite (proj2 (Z.eqb_neq n0 0)) by exact Hn0. reflexivity. }
rewrite EC1 in Hcur1 |- *.
destruct Hcur0 as (R25 & R27). destruct Hcur1 as (R24 & R23). cbn [TOP.fi_off TOP.fi_n] in R25, R27, R24, R23.
assert (Hnl : 0 < l_n cx) by lia.
pose proof (HINg Hnl) as HBLK.
destruct (op3_blk B ly S W mem md _ _ HARg HBLK) as (Bp & Bc & Bsh & Brq).
assert (HZ : decode_zshadow_at B TRANS_SCALE (TRANS_SCALE + 32)).
{ pose proof (lp_cells _ _ _ _ _ HP ly) as HCL. do 17 (destruct HCL as [_ HCL]). exact (proj1 HCL). }
assert (HJx : op3_J B [] cx ly S W mem md e) by exact HJ.
assert (Hm : n0 = 1 \/ 2 <= n0) by lia.
destruct Hm as [Hm | Hm].
- subst n0. exists 0, (o0 + 1), 0.
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
  exact (op3_A1z B [] cx ly S W regs mem md e (o0 + 1) LAWS HGX HZ HJx HR R26 R24 R23 ltac:(lia)).
- exists (DSpec.at8 (l_pl cx) (Z.to_nat (o0 + 1))), (o0 + 2), (n0 - 2).
  split.
  { unfold TOP.fuzz_u8_m. cbn [TOP.fi_off TOP.fi_n]. rewrite (proj2 (Z.eqb_neq (n0 - 1) 0)) by lia.
    f_equal. f_equal; lia. }
  split; [lia|]. split; [lia|]. split; [lia|].
  destruct HIN as (HG8 & _).
  pose proof (garr8_nthZ segs _ _ _ (o0 + 1) HG8 ltac:(lia) ltac:(rewrite length_map; lia)) as (HV & Hsb).
  rewrite op3_nth_map in HV, Hsb.
  assert (NI : forall j, 0 <= j < 1 -> ~ in_img segs (l_p cx + (o0 + 1) + j))
    by (intros j Hj; apply (blk_img segs B LAWS ly S W mem md (l_p cx) (l_n cx) _ HARg HBLK); lia).
  pose proof (op3_apart_img (l_p cx + (o0 + 1)) 1 TRANS_SCALE (TRANS_SCALE + 32) ltac:(lia) ltac:(lia) NI
    (fun a Ha => trans_ro_img a (op3_scale_in_ro a Ha))) as Hd.
  destruct (al_shadow segs B LAWS ly S W mem md (l_p cx) (l_n cx) HARg HBLK) as (BSH & _).
  apply (op3_A1n B [] cx ly S W regs mem md e o0 n0 _ LAWS HGX HZ HJx HR R26 R25 R27 R24 R23 Hm Ho0 ltac:(lia) ltac:(lia)
    ltac:(lia) Hsb HV).
  + exact (op3_block_ra _ (l_p cx) (l_n cx) (l_p cx + (o0 + 1)) 1 BSH ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  + unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

(* The segment OP3A, from ARM3 to TICK; K1 (lc_rom_view_stmt) gives SCALE's bytes. *)
Lemma lc_op3a_ok : @lc_rom_view_stmt rc B MT XL RLO RHI -> @lc_op3a_stmt rc B MT XL RLO RHI.
Proof.
intros K1. unfold lc_op3a_stmt. intros HP cx op W' c' HB HA.
destruct HA as (ly' & S' & regs' & mem' & md' & e & Ec & Ho & HL & Htw & Hcur0 & Hcur1 & R20 & R22). subst c'.
pose proof HL as (HC & Hfr & Hsp & Hfsh & Hopok & He & Hmet & R21).
pose proof HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal &
  HFceil & HFpres & HFL & HIN).
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof (K1 HP cx ly' S' W' regs' mem' md' e HB HC) as HROM.
pose proof ASAN_CEIL_range as (CL & _). unfold ASAN_CEIL in CL.
pose proof Hfr as (F18 & F26).
pose proof Hopok as (_ & _ & Hfin & Hn0 & _).
assert (EST : ESTACK = 4096) by reflexivity.
unfold LF_FRAME in Hsp1.
assert (Hnl : 0 < l_n cx).
{ destruct Hfin as (Hf1 & Hf2 & Hon). destruct Hn as (_ & HnD). lia. }
pose proof (HINg Hnl) as HBLK.
replace (lo_arm 3) with 0x5b4 by reflexivity.
(* +0x5b4 .. +0x78c *)
destruct (op3_A1 HP cx op ly' S' W' regs' mem' md' e HB HC HROM Hopok F26 Hcur0 Hcur1)
  as (sb & o2 & n2 & HU & Ho2 & Hn2 & Hon & HA1).
eapply SRr_bind; [exact HA1|]. intros W2 c2 _ HPA.
(* +0x78c .. +0x7a4: the two memsets *)
eapply SRr_bind.
{ exact (op3_A2 B [] cx ly' S' W' regs' mem' e _ o2 n2 W2 c2 LAWS HGX (lp_memset _ _ _ _ _ HP)
    (lp_recv_cells _ _ _ _ _ HP) Rsp Rgp Rtp Hsp0al Hsp1al ltac:(lia) ltac:(destruct Hstk as (_ & _ & Hs0 & H47); lia) HPA). }
intros W3 c3 _ HPM.
(* +0x7a4 .. +0x96c *)
eapply SRr_bind.
{ apply (op3_B B [] cx ly' S' W' regs' mem' e (lo_B op) _ o2 n2 W3 c3 LAWS HGX HPM Htw R9 R20 F26 Hsp1c
    ltac:(destruct Hstk as (_ & _ & Hs0 & H47); lia) Hsp1al).
  - pose proof Hsp as Hsp'. unfold lc_spills in Hsp'. rewrite Forall_forall in Hsp'. apply (Hsp' (176, transport_hi 9)).
    unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm. cbn [app In]. do 3 right. left. reflexivity.
  - pose proof Hsp as Hsp'. unfold lc_spills in Hsp'. rewrite Forall_forall in Hsp'. apply (Hsp' (184, TA_M)).
    unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm. cbn [app In]. do 6 right. left. reflexivity.
  - apply op3_scale_range.
  - exact (proj1 HIN).
  - exact (proj2 Hn).
  - exact Hnl.
  - exact HBLK.
  - exact Ho2.
  - exact Hn2.
  - exact Hon. }
intros W4 c4 _ HPT.
apply SRr_ret.
destruct HPT as (-> & regs6 & mem6 & md6 & -> & HJ6 & HT6 & R22' & R24' & R23' & KR6 & KM6 & GM6).
destruct (op3_model (lo_B op) (l_pl cx) (lc_oc (l_pl cx) (lo_c op)) (TOP.FuzzIn o2 n2) sb (tw_len _ _ _ Htw) HU)
  as (B1 & HOB & HWF & HGN & HTC).
assert (GIMG : forall a, TA_OW <= a < TA_OW + 304 \/ TA_GOT <= a < TA_GOT + 224 \/ TA_M + 88 <= a < TA_M + 92 \/
    TA_g_now <= a < TA_g_now + 8 -> in_img segs a).
{ intros a [Ha | [Ha | [Ha | Ha]]]; apply trans_g_img.
  - apply (op3_inG_row _ _ _ a TMAP_A_OW). unfold TW.SZ_OW. lia.
  - apply (op3_inG_row _ _ _ a TMAP_A_GOT). unfold TW.SZ_GOT. lia.
  - apply (op3_inG_row _ _ _ a TMAP_A_M). unfold TW.SZ_M. lia.
  - apply (op3_inG_row _ _ _ a TMAP_A_g_now). unfold TW.SZ_g_now. lia. }
assert (TAV : TA_OW = 6238304 /\ TA_GOT = 6181600 /\ TA_M = 6156640 /\ TA_g_now = 6156544) by (repeat split; reflexivity).
destruct TAV as (VOW & VGOT & VMV & VNV).
destruct Hstk as (_ & _ & Hs0 & H47).
assert (KA : forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (lc_sp1 cx - ESTACK <= a < lc_sp1 cx) ->
  aview segs (w_H W') mem6 a = aview segs (w_H W') mem' a).
{ intros a Ha Hw. apply KM6; [lia|]. unfold op3_wr. lia. }
assert (KB : forall b m i, In (b, m) (ablocks B ly' S') -> 0 <= i < req_size m ->
  aview segs (w_H W') mem6 (b + i) = aview segs (w_H W') mem' (b + i)).
{ intros b m i Hbm Hi. destruct (op3_blk B ly' S' W' mem' md' b m HARg Hbm) as (Bp' & Bc' & _ & _).
  apply KM6; [lia|]. unfold op3_wr. intros Hw.
  apply (blk_img segs B LAWS ly' S' W' mem' md' b m (b + i) HARg Hbm ltac:(lia)). apply GIMG. lia. }
assert (KF : forall a, lc_F cx <= a < lc_F cx + LF_FBYTES \/ lc_SH cx <= a < lc_SH cx + 32 ->
  aview segs (w_H W') mem6 a = aview segs (w_H W') mem' a).
{ intros a [Ha | Ha].
  - unfold LF_FBYTES in *. apply KM6; [lia|]. unfold op3_wr. intros Hw.
    apply (frm_img segs B LAWS ly' S' W' mem' md' LF_CID (l_fpos cx) a HARg HFin);
      [rewrite HFaddr; change (fs_frame_bytes LF_CID) with 256; lia | apply GIMG; lia].
  - unfold lc_SH, SHADOW_OFF, LF_FBYTES in *. pose proof (Z.mul_div_le (lc_F cx) 8 ltac:(lia)).
    pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)).
    apply KM6; [lia|]. unfold op3_wr. lia. }
unfold lc_st_tick.
exists ly', S', regs6, mem6, md6, e, B1.
split; [reflexivity|].
split; [exact (eq_sym Ho)|].
split.
{ unfold lc_lcore. split.
  { apply (op3_core_regs cx ly' S' W' regs' regs6 mem6 md6 e).
    - exact (lc_core_kept B MT XL RLO RHI cx ly' S' W' regs' mem' md' e ESTACK ly' S' W' regs' mem6 md6 e LAWS HB HC HJ6
        eq_refl (Permutation_refl _) (fun r _ => eq_refl) ltac:(unfold LLVMF_STK; lia) KA KB KF).
    - intros r Hr. apply KR6. unfold op3_keep. cbn [In] in *. tauto. }
  split; [split; [rewrite (KR6 18%bv ltac:(cbn; tauto)); exact F18 | rewrite (KR6 26%bv ltac:(cbn; tauto)); exact F26]|].
  split.
  { apply (lc_spills_kept cx _ (aview segs (w_H W') mem')); [| | exact Hsp].
    - intros o Hoo. pose proof (lf_spill_vals (lc_F cx) ltac:(lia) ltac:(unfold LF_FBYTES in *; lia)) as V.
      rewrite Forall_forall in V. destruct (V o Hoo) as (_ & _ & V1 & V2). lia.
    - intros a Ha. apply KM6; [lia|]. unfold op3_wr. lia. }
  split; [exact (lc_fsh_kept cx (aview segs (w_H W') mem') _ false false (fun a Ha => KF a (or_intror Ha)) Hfsh)|].
  split; [exact Hopok|]. split; [exact He|]. split; [exact Hmet|].
  rewrite (KR6 21%bv ltac:(cbn; tauto)). exact R21. }
split; [exact HOB|].
split; [rewrite HWF; exact HT6|].
split.
{ rewrite HGN, R22'. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Zmod_mod. reflexivity. }
split; [rewrite HTC; exact (conj R24' R23')|].
rewrite (KR6 20%bv ltac:(cbn; tauto)). exact R20.
Qed.
End top.
