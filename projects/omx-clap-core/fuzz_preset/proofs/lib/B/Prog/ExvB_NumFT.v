(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Does not rest on tex_word_specX. memnorm only as EXN_keepM / EXN_keepM_cur's step keep, which each run gives by
   YAkMemnorm.memnorm_msteps over its own msteps (kit 4f18c75d4900). *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (asan-ubsan, rebuilt pin f8f98a95bc52, unstripped twin 3b5e1a099b53),
   ex_value's NUMBER SEGMENT, sub-pieces T and F of lib/B/Prog/ExvB_NumCut.v:
     T  CT (exv_pc 0xa70, B 0x83f9c) -> CX (exv_pc 0xa7c, B 0x83fa8)          exn_T : EXN_T B ARx SK E pos
     F  CD (exv_pc 0x9a8, B 0x83ed4) -> CT (exv_pc 0xa70)                      exn_F : EXN_F B ARx SK E pos
   The code (neutral listing, the internal file ex_value.fuzz_preset.asan-ubsan.s, a Theorem Labs lane's listing of the B' pin, lines 620-624
   and 670-672):
     0x9a8  lbu  a0, 0(a3)      the shadow byte of q (a3 = shadow_addr q): the ASan check of the store to in->p
     0x9ac  bnez a0, +0x380     to 0xd2c (B 0x84258, the errpath_store8 report arm): NOT TAKEN, the byte reads 0
                                (EXB's range_addressable on [q, q + 40) and q mod 8 = 0: saddr_ok (q + 7) s forces s = 0)
     0x9b0  li   s5, 0          r = 0
     0x9b4  sd   s6, 0(s3)      in->p := x0 + j
     0x9b8  j    +0xb8          to CT
     0xa70  li   a0, -8
     0xa74  sb   a0, 4(s10)     the frame's `end` slot re-poisoned (shadow byte of f + 32)
     0xa78  sb   a0, 8(s10)     the frame's `num` slot re-poisoned (shadow byte of f + 64)
   Method: each instruction is stepped by hand (YK11 / YK14 / YK0v step lemmas); every instruction word is FETCHED
   FROM B_prog_tbl (PAImg_prog.v's decode table built from the image segments, table_ok B_prog_tbl_ok), so a wrong pin
   cannot pass; exnft_pins_listing checks the same eight words against B_prog_listing. One msteps per sub-piece, closed
   by YA0n's SRr_msteps. The journal is carried by YCbqG's ajournal_x_exec (the sd writes the caller window, the two
   sb write the own frame's shadow: awr_byte's in_frames arm with own = [(1, pos)]), EXB by the Section hypotheses
   EXN_keepM (T) / EXN_keepM_cur (F), the spills by EXN_keep_spill, and T ends in CUT_CX. The step's memnorm keep
   (the premise EXN_keepM / EXN_keepM_cur take) is the run's own: memnorm_mrestrict, memnorm_msteps over the msteps,
   memnorm_munrestrict (YAkMemnorm.v; exnft_mn_run).
   The two shadow bytes lie below alloc_ceiling (the frame is below it, frames_bounds_x), the cursor cells
   [q, q + 40) above it (q is on the real stack, astk_ok): so T keeps EXV_RES.
   F's functional post: exn_N (skipn i1 x) = Some (u, skipn j x) (EXN_CD_pre) makes the dispatch byte a '-' or a digit,
   so EXN_disp holds for it (exnft_disp) and exn_V_eq rewrites exv_V E to that reading.
   Rule 24: proves no function (kind: segment lemma).
   Numerals, classified: DERIVED - the offsets 0x9a8, 0x9ac, 0x9b0, 0x9b4, 0x9b8, 0xa70, 0xa74, 0xa78, 0xa7c
   (B address - B_prog_sigma AS_ex_value, from the listing); WORD - the instruction words 0x6c503, 0x38051063, 0xa93,
   0x169b023, 0xb80006f, 0xff800513, 0xad0223, 0xad0423, the register numbers 0, 10, 13, 19, 21, 22, 26, the
   immediates 0, 4, 8, 4088, 896, 184 decoded from those words, -8 (the byte 0xf8 the tail writes), 45 (ASCII '-');
   LENGTH - 4 (instruction bytes), 1, 8 (store widths), 7 (last byte of q's granule), 16, 128 (the class-1 frame's
   shadow bytes and size), 40 (struct ex), 5, 8, 12, 13, 21, 32, 64 (bit widths), 256 (byte modulus), 2 ^ 64
   (address-space bound). No ADDRESS: every pc is `exv_pc <offset>`. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK0h YK0i YK14 YK1b YK1a YK0j YK0v YK00 YN01 YP02 YP0a.
(* ExvB_NumCut.v's import set, in its order (YM05 last: alloc_ceiling is the RunCeil field) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require ExvB_Num_eng.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt ExvB_NumPure ExvB_NumCut ExvB_Open_kt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

(* ======== machine helpers (no image) ======== *)

Lemma exnft_v_addi_lit : forall v d, v_addi (Z_to_bv 64 v) d = Z_to_bv 64 (v + d).
Proof.
intros v d. unfold v_addi. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma exnft_bvs0 : bv_signed (0%bv : bv 12) = 0.
Proof. reflexivity. Qed.

Lemma exnft_bv_eqb_ne : forall u v, 0 <= u < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> u <> v ->
  bv_eqb (Z_to_bv 64 u) (Z_to_bv 64 v) = false.
Proof. intros u v Hu Hv Hne. unfold bv_eqb. rewrite !u64_lit by lia. apply Z.eqb_neq. exact Hne. Qed.

Lemma exnft_wbytes1 : forall (m : word -> option byte) (a : word) (b : byte) (x : word),
  wbytes m a [b] x = if bv_eqb x a then Some b else m x.
Proof. reflexivity. Qed.

Lemma exnft_keep_wr : forall (Hh : word -> bool) (mem m' : word -> option byte) x,
  m' x = mrestrict Hh mem x -> mrestrict Hh (munrestrict Hh mem m') x = mrestrict Hh mem x.
Proof. intros Hh mem m' x E. rewrite mrestrict_munrestrict. unfold mrestrict in *. destruct (Hh x); [reflexivity | exact E]. Qed.

Lemma exnft_grows_wr : forall (Hh : word -> bool) (mem m' : word -> option byte),
  mem_grows (mrestrict Hh mem) m' -> mem_grows (mrestrict Hh mem) (mrestrict Hh (munrestrict Hh mem m')).
Proof.
intros Hh mem m' G x Hx. pose proof (G x Hx) as Gx. rewrite mrestrict_munrestrict.
unfold mrestrict in *. destruct (Hh x); [exact Hx | exact Gx].
Qed.

Lemma exnft_wtl8_len : forall v : word, length (word_to_le_bytes 8 v) = 8%nat.
Proof. intros v. unfold word_to_le_bytes. apply length_Z_to_le_bytes. Qed.

(* the k-th byte of an 8-byte little-endian store is val_mem's k-th byte *)
Lemma exnft_wtl8_nth : forall v (kk : nat), (kk < 8)%nat ->
  nth_error (word_to_le_bytes 8 (Z_to_bv 64 v)) kk = Some (Z_to_bv 8 (le_byte v 8 kk)).
Proof.
intros v kk Hk. unfold word_to_le_bytes. rewrite nth_error_Z_to_le_bytes by exact Hk. f_equal.
apply bv_eq. unfold le_byte. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ (8 * Z.of_nat 8)).
rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* a store of n bytes at a is allowed when every byte is present and visible *)
Lemma exnft_store_ok : forall (Hh : word -> bool) (mem m : word -> option byte) a (n : nat),
  0 <= a < 2 ^ 64 -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> apresent Hh mem (a + i)) ->
  mem_grows (mrestrict Hh mem) m ->
  RiscvSemantics.store_ok rsegs m (Z_to_bv 64 a) n = true.
Proof.
intros Hh mem m a n Ha Hn Hp Hg.
pose proof (Nat2Z.is_nonneg n) as Hn0.
pose proof (u64_lit a Ha) as Ea.
apply (store_ok_mono rsegs n (mrestrict Hh mem) m _ Hg).
apply store_ok_of_all.
- rewrite Ea. exact Hn.
- intros x Hx. rewrite Ea in Hx.
  assert (Hi : 0 <= bv_unsigned x - a < Z.of_nat n) by lia.
  pose proof (apresent_writable rsegs Hh mem (a + (bv_unsigned x - a)) (Hp _ Hi)) as Hw.
  unfold writable_at in Hw. replace (a + (bv_unsigned x - a)) with (bv_unsigned x) in Hw by lia.
  rewrite Z_to_bv_bv_unsigned in Hw. exact Hw.
Qed.

Lemma exnft_mbyte_vis : forall (Hh : word -> bool) (m : word -> option byte) z,
  Hh (Z_to_bv 64 z) = false -> mbyte rsegs (mrestrict Hh m) z = mbyte rsegs m z.
Proof. intros Hh m z E. unfold mbyte, mrestrict. rewrite E. reflexivity. Qed.

(* the memnorm keep across a restricted run: the run starts from the visible part of memc, LPS's steps keep memnorm
   (YAkMemnorm.memnorm_msteps), and the merge with the hidden part keeps it *)
Lemma exnft_mn_run : forall (Hh : word -> bool) (memc : word -> option byte) (f : YK11.FPState) regs pc regs' pc' m',
  msteps rsegs (@YK11.mkst f regs pc (mrestrict Hh memc) (YK11.seg_rom rsegs))
               (@YK11.mkst f regs' pc' m' (YK11.seg_rom rsegs)) ->
  YAkMemnorm.memnorm rsegs memc -> YAkMemnorm.memnorm rsegs (munrestrict Hh memc m').
Proof.
intros Hh memc f regs pc regs' pc' m' Hms Hm.
apply YAkMemnorm.memnorm_munrestrict; [exact Hm|].
exact (YAkMemnorm.memnorm_msteps rsegs _ _ Hms (YAkMemnorm.memnorm_mrestrict rsegs Hh memc Hm)).
Qed.

(* ======== the eight instructions, fetched from B_prog_tbl ======== *)

(* the pc at offset off of ex_value *)
Definition exnft_w (off : Z) : word := Z_to_bv 64 (exv_pc off).

(* one instruction: the decode table of image B holds the word w at exv_pc off, and w decodes to i *)
Definition exnft_ins (off w : Z) (i : instr) : Prop :=
  clookup B_prog_tbl (exv_pc off) = Some w /\ is_ecall (Z_to_bv 32 w) = false /\
  decode_any (Z_to_bv 32 w) = Some (i, 4%Z).
Ltac exnft_ins_tac := refine (conj _ (conj _ _)); [vm_compute; reflexivity | vm_compute; reflexivity | vm_refl_bv].

Lemma I_9a8 : exnft_ins 0x9a8 0x6c503 (Load SZ1 false 10 13 0). Proof. exnft_ins_tac. Qed.
Lemma I_9ac : exnft_ins 0x9ac 0x38051063 (Branch BC_NE 10 0 896). Proof. exnft_ins_tac. Qed.
Lemma I_9b0 : exnft_ins 0x9b0 0xa93 (OpImm ALU_ADD 21 0 0). Proof. exnft_ins_tac. Qed.
Lemma I_9b4 : exnft_ins 0x9b4 0x169b023 (Store SZ8 19 22 0). Proof. exnft_ins_tac. Qed.
Lemma I_9b8 : exnft_ins 0x9b8 0xb80006f (Jal 0 184). Proof. exnft_ins_tac. Qed.
Lemma I_a70 : exnft_ins 0xa70 0xff800513 (OpImm ALU_ADD 10 0 4088). Proof. exnft_ins_tac. Qed.
Lemma I_a74 : exnft_ins 0xa74 0xad0223 (Store SZ1 26 10 4). Proof. exnft_ins_tac. Qed.
Lemma I_a78 : exnft_ins 0xa78 0xad0423 (Store SZ1 26 10 8). Proof. exnft_ins_tac. Qed.

(* the same eight words in h-verbs-1's listing of record (slot = (exv_pc off - B_prog_base) / 4) *)
Definition exnft_lst (off w : Z) : Prop := @plookup asym B_prog_tpi (exv_pc off - B_prog_base) = Some (@PW asym w).
Lemma exnft_pins_listing :
  exnft_lst 0x9a8 0x6c503 /\ exnft_lst 0x9ac 0x38051063 /\ exnft_lst 0x9b0 0xa93 /\ exnft_lst 0x9b4 0x169b023 /\
  exnft_lst 0x9b8 0xb80006f /\ exnft_lst 0xa70 0xff800513 /\ exnft_lst 0xa74 0xad0223 /\ exnft_lst 0xa78 0xad0423.
Proof. repeat split; vm_compute; reflexivity. Qed.

Lemma exnft_w_add : forall off d, v_addi (exnft_w off) d = exnft_w (off + d).
Proof. intros off d. unfold exnft_w, exv_pc. rewrite exnft_v_addi_lit, Z.add_assoc. reflexivity. Qed.

Lemma exnft_fetch : forall off w, clookup B_prog_tbl (exv_pc off) = Some w ->
  fetch_word rsegs (exnft_w off) = Some (Z_to_bv 32 w).
Proof. intros off w H. exact (B_prog_tbl_ok (exv_pc off) w H). Qed.

Lemma exnft_step_lbu : forall (f : YK11.FPState) regs mem off off' w rd rs (imm : bv 12) b,
  off' = off + 4 -> exnft_ins off w (Load SZ1 false rd rs imm) -> bv_eqb rd 0 = false ->
  rdn rsegs mem (v_addi (YK11.getr regs rs) (bv_signed imm)) 1%nat = Some [b] ->
  RiscvSemantics.step rsegs (@YK11.mkst f regs (exnft_w off) mem (YK11.seg_rom rsegs)) =
  MachineOk (@YK11.mkst f (YK11.regupd regs rd (Z_to_bv 64 (bv_unsigned b))) (exnft_w off') mem (YK11.seg_rom rsegs)).
Proof.
intros f regs mem off off' w rd rs imm b -> (HL & HE & HD) Hrd Hr.
rewrite (step_lbu (fx := f) rsegs regs (exnft_w off) mem (YK11.seg_rom rsegs) (Z_to_bv 32 w) rd rs imm b
  (exnft_fetch off w HL) HE HD Hr).
rewrite Hrd, exnft_w_add. reflexivity.
Qed.

Lemma exnft_step_bft : forall (f : YK11.FPState) regs mem off off' w c rs1 rs2 (imm : bv 13),
  off' = off + 4 -> exnft_ins off w (Branch c rs1 rs2 imm) ->
  branch_taken c (YK11.getr regs rs1) (YK11.getr regs rs2) = false ->
  RiscvSemantics.step rsegs (@YK11.mkst f regs (exnft_w off) mem (YK11.seg_rom rsegs)) =
  MachineOk (@YK11.mkst f regs (exnft_w off') mem (YK11.seg_rom rsegs)).
Proof.
intros f regs mem off off' w c rs1 rs2 imm -> (HL & HE & HD) Hc.
rewrite (step_branch_ft_gen (fx := f) rsegs regs (exnft_w off) mem (YK11.seg_rom rsegs) (Z_to_bv 32 w) c rs1 rs2 imm
  (exnft_fetch off w HL) HE HD Hc).
rewrite exnft_w_add. reflexivity.
Qed.

Lemma exnft_step_addi : forall (f : YK11.FPState) regs mem off off' w rd rs (imm : bv 12) v,
  off' = off + 4 -> exnft_ins off w (OpImm ALU_ADD rd rs imm) -> bv_eqb rd 0 = false ->
  v_addi (YK11.getr regs rs) (bv_signed imm) = v ->
  RiscvSemantics.step rsegs (@YK11.mkst f regs (exnft_w off) mem (YK11.seg_rom rsegs)) =
  MachineOk (@YK11.mkst f (YK11.regupd regs rd v) (exnft_w off') mem (YK11.seg_rom rsegs)).
Proof.
intros f regs mem off off' w rd rs imm v -> (HL & HE & HD) Hrd Hv.
rewrite (step_addi_at (fx := f) rsegs regs (exnft_w off) mem (YK11.seg_rom rsegs) (Z_to_bv 32 w) rd rs imm v
  (exnft_fetch off w HL) HE HD Hrd Hv).
rewrite exnft_w_add. reflexivity.
Qed.

Lemma exnft_step_sd : forall (f : YK11.FPState) regs mem off off' w rs1 rs2 (imm : bv 12) (a v : word),
  off' = off + 4 -> exnft_ins off w (Store SZ8 rs1 rs2 imm) ->
  v_addi (YK11.getr regs rs1) (bv_signed imm) = a -> YK11.getr regs rs2 = v ->
  RiscvSemantics.store_ok rsegs mem a 8%nat = true ->
  RiscvSemantics.step rsegs (@YK11.mkst f regs (exnft_w off) mem (YK11.seg_rom rsegs)) =
  MachineOk (@YK11.mkst f regs (exnft_w off') (wbytes mem a (word_to_le_bytes 8 v)) (YK11.seg_rom rsegs)).
Proof.
intros f regs mem off off' w rs1 rs2 imm a v -> (HL & HE & HD) Ha Hv Hok.
rewrite (step_sd_at (fx := f) rsegs regs (exnft_w off) mem (YK11.seg_rom rsegs) (Z_to_bv 32 w) rs1 rs2 imm a v
  (exnft_fetch off w HL) HE HD Ha Hv Hok).
rewrite exnft_w_add. reflexivity.
Qed.

Lemma exnft_step_sb : forall (f : YK11.FPState) regs mem off off' w rs1 rs2 (imm : bv 12) (a v : word) (b : byte),
  off' = off + 4 -> exnft_ins off w (Store SZ1 rs1 rs2 imm) ->
  v_addi (YK11.getr regs rs1) (bv_signed imm) = a -> YK11.getr regs rs2 = v -> Z_to_bv 8 (bv_unsigned v) = b ->
  RiscvSemantics.store_ok rsegs mem a 1%nat = true ->
  RiscvSemantics.step rsegs (@YK11.mkst f regs (exnft_w off) mem (YK11.seg_rom rsegs)) =
  MachineOk (@YK11.mkst f regs (exnft_w off') (wbytes mem a [b]) (YK11.seg_rom rsegs)).
Proof.
intros f regs mem off off' w rs1 rs2 imm a v b -> (HL & HE & HD) Ha Hv Hb Hok.
rewrite (step_sb_at (fx := f) rsegs regs (exnft_w off) mem (YK11.seg_rom rsegs) (Z_to_bv 32 w) rs1 rs2 imm a v b
  (exnft_fetch off w HL) HE HD Ha Hv Hb Hok).
rewrite exnft_w_add. reflexivity.
Qed.

Lemma exnft_step_j : forall (f : YK11.FPState) regs mem off off' w (imm : bv 21),
  off' = off + bv_signed imm -> exnft_ins off w (Jal 0 imm) ->
  RiscvSemantics.step rsegs (@YK11.mkst f regs (exnft_w off) mem (YK11.seg_rom rsegs)) =
  MachineOk (@YK11.mkst f regs (exnft_w off') mem (YK11.seg_rom rsegs)).
Proof.
intros f regs mem off off' w imm -> (HL & HE & HD).
rewrite (step_jal_link (fx := f) rsegs regs (exnft_w off) mem (YK11.seg_rom rsegs) (Z_to_bv 32 w) 0 imm
  (exnft_fetch off w HL) HE HD).
unfold btgt. rewrite (exnft_w_add off (bv_signed imm)). reflexivity.
Qed.

(* ======== the pure part: the reading F stores ======== *)

Section p. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variable E : exv_e.
Variable pos : Z.
Hypothesis HYP : EXV_HYP B ARx SK.
Hypothesis HX : forall fxc : YK11.FPState, CUT_CX (fx := fxc) B ARx SK (e_n E).
Hypothesis MK : EXN_keepM B ARx SK E pos.
Hypothesis MC : EXN_keepM_cur B ARx SK E pos.
Hypothesis KS : EXN_keep_spill E.

(* the number arm read a value at the dispatch byte: that byte is a '-' or a digit, so the dispatch facts hold *)
Lemma exnft_disp : forall p, 0 <= e_i0 E <= exv_len E -> exn_N (skipn (EXN_i1 E) (e_x E)) = Some p ->
  exists c, EXN_disp E c.
Proof.
intros p Hi0 HN.
pose proof (exn_i1_eq E Hi0) as Hsk.
revert Hsk HN. destruct (skipn (EXN_i1 E) (e_x E)) as [|b y] eqn:Esk; intros Hsk HN.
{ rewrite exn_N_unfold in HN. cbn in HN. discriminate HN. }
exists b. unfold EXN_disp.
split.
{ unfold exv_i1. rewrite <- Hsk. cbn [length]. lia. }
split; [exact (exn_nth_skipn (e_x E) (EXN_i1 E) b y Esk)|].
split; [|exact (exn_skip_head (exv_X E) b y (eq_sym Hsk))].
rewrite exn_N_unfold in HN. cbv zeta in HN.
destruct (Z.eqb_spec b 45) as [E45 | N45].
- subst b. reflexivity.
- cbn [skipn] in HN.
  case_eq (PjGrammar.digit b); intros Ed; [|rewrite Ed in HN; cbn in HN; discriminate HN].
  unfold PjGrammar.digit in Ed. apply andb_true_iff in Ed as [E1 E2].
  apply Z.leb_le in E1. apply Z.leb_le in E2.
  unfold exv_disp. repeat (rewrite (proj2 (Z.eqb_neq _ _)) by lia). reflexivity.
Qed.

(* F's functional post at r = 0 *)
Lemma exnft_res0 : forall (Wc : world rsegs) memc j u dl',
  0 <= e_i0 E <= exv_len E -> (j <= length (e_x E))%nat ->
  exn_N (skipn (EXN_i1 E) (e_x E)) = Some (u, skipn j (e_x E)) ->
  prhex_cur Wc memc (e_q E) (e_x0 E + Z.of_nat j) (e_x0 E + exv_len E) (e_dep E) (e_scr E) dl' ->
  (dl' = 0 \/ dl' = 1) -> (dl' = 1 <-> e_dl E = 1 \/ (e_v E <> 0 /\ e_t E <> u)) ->
  EXV_RES E Wc memc 0.
Proof.
intros Wc memc j u dl' Hi0 Hj HN Hcur Hdl01 Hdl.
destruct (exnft_disp _ Hi0 HN) as (c & Hc).
exists (Z.of_nat j), (e_dep E), dl'. split; [exact Hcur|]. split; [exact Hdl01|].
rewrite (exn_V_eq E c Hi0 Hc), HN.
split; [reflexivity|]. split; [|split; [reflexivity | exact Hdl]].
rewrite length_skipn. unfold exv_len. lia.
Qed.

(* EXV_RES reads only the cursor cells [q, q + 40) *)
Lemma exnft_res_keep : forall (Wc : world rsegs) memc memc' r,
  (forall z, e_q E <= z < e_q E + 40 -> aview rsegs (w_H Wc) memc' z = aview rsegs (w_H Wc) memc z) ->
  EXV_RES E Wc memc r -> EXV_RES E Wc memc' r.
Proof.
intros Wc memc memc' r HK (p' & dep' & dl' & (C0 & C8 & C16 & C24 & C32) & Hdl & HV).
exists p', dep', dl'. split; [|split; [exact Hdl | exact HV]].
split; [|split; [|split; [|split]]].
- eapply ExvB_Num_eng.exw_val_kept; [|exact C0]. intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply HK. lia.
- eapply ExvB_Num_eng.exw_val_kept; [|exact C8]. intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply HK. lia.
- eapply ExvB_Num_eng.exw_val_kept; [|exact C16]. intros x Hx. change (Z.of_nat 4) with 4 in Hx. apply HK. lia.
- eapply ExvB_Num_eng.exw_val_kept; [|exact C24]. intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply HK. lia.
- eapply ExvB_Num_eng.exw_val_kept; [|exact C32]. intros x Hx. change (Z.of_nat 4) with 4 in Hx. apply HK. lia.
Qed.

(* ======== T: CT (0xa70) -> CX (0xa7c) ======== *)
Lemma exn_T : EXN_T B ARx SK E pos.
Proof.
intros fxc lyc Sc Hpc Wc regs memc mdc k r HPRE ((HEXB & _ & _) & R21 & HRES).
change (exv_pc EXN_CT) with (exv_pc 0xa70).
pose proof (eh_laws B ARx SK HYP) as LAWS.
pose proof asan_consts as (C1 & _).
pose proof HPRE as HP. unfold EXV_PRE in HP. cbv zeta in HP.
destruct HP as (HFP & _ & _ & _ & _ & _ & Hq8 & _ & Hspq & Hqd & _).
destruct HFP as ((_ & _ & _ & _ & _ & Hastk & _) & _).
destruct Hastk as (_ & Hstk0 & Hceil & Hslo & _).
pose proof HEXB as HB. unfold EXB in HB. cbv zeta in HB.
destruct HB as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & R2 & R8 & R9 & R18 & R24 & R25 & R26 & R19 & R3 & R4 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
destruct Hstatic as (_ & _ & _ & _ & Hhi & H47 & _).
unfold exv_sp in *.
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds_x rsegs B ARx LAWS _ _ _ _ _ _ 1 pos HAR Hin) as (F0 & Fc & _).
destruct (alx_frames rsegs B ARx LAWS _ _ _ _ _ _ 1 pos HAR Hin) as (_ & _ & _ & Hshp).
change (fs_frame_bytes 1) with 128 in Fc. change (fs_frame_bytes 1 / 8) with 16 in Hshp.
set (fr := frame_addr lyc 1 pos) in *.
assert (Hsh : 0 <= shadow_addr fr /\ shadow_addr fr + 8 < alloc_ceiling) by (unfold shadow_addr, SHADOW_OFF; lia).
set (sh := shadow_addr fr) in *.
assert (P4 : apresent (w_H Wc) memc (sh + 4)) by exact (proj1 (Hshp 4 ltac:(lia))).
assert (P8 : apresent (w_H Wc) memc (sh + 8)) by exact (proj1 (Hshp 8 ltac:(lia))).
unfold YG0d.w64 in *.
set (b8 := Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-8)))).
set (m0 := mrestrict (w_H Wc) memc).
set (m1 := wbytes m0 (Z_to_bv 64 (sh + 4)) [b8]).
set (m2 := wbytes m1 (Z_to_bv 64 (sh + 8)) [b8]).
set (regs1 := YK11.regupd regs 10 (Z_to_bv 64 (-8))).
assert (G1 : forall r0 : bv 5, r0 <> 10%bv -> YK11.getr regs1 r0 = YK11.getr regs r0)
  by (intros r0 N; unfold regs1; rewrite getr_other by exact N; reflexivity).
assert (Hms : msteps rsegs (@YK11.mkst fxc regs (exnft_w 0xa70) m0 (YK11.seg_rom rsegs))
                           (@YK11.mkst fxc regs1 (exnft_w 0xa7c) m2 (YK11.seg_rom rsegs))).
{ eapply mst_step; [reflexivity | |].
  { refine (exnft_step_addi fxc regs m0 0xa70 0xa74 0xff800513 10 0 4088 (Z_to_bv 64 (-8)) eq_refl I_a70 eq_refl _).
    rewrite getr_zero, exnft_v_addi_lit. f_equal. }
  eapply mst_step; [reflexivity | |].
  { refine (exnft_step_sb fxc regs1 m0 0xa74 0xa78 0xad0223 26 10 4 (Z_to_bv 64 (sh + 4)) (Z_to_bv 64 (-8)) b8
      eq_refl I_a74 _ _ eq_refl _).
    - rewrite G1 by reg_neq_tac. rewrite R26, exnft_v_addi_lit. reflexivity.
    - unfold regs1. rewrite getr_same by reg_neq_tac. reflexivity.
    - apply (exnft_store_ok (w_H Wc) memc m0 (sh + 4) 1); [lia | lia | | apply mem_grows_refl].
      intros i Hi. replace (sh + 4 + i) with (sh + 4) by lia. exact P4. }
  eapply mst_step; [reflexivity | |].
  { refine (exnft_step_sb fxc regs1 m1 0xa78 0xa7c 0xad0423 26 10 8 (Z_to_bv 64 (sh + 8)) (Z_to_bv 64 (-8)) b8
      eq_refl I_a78 _ _ eq_refl _).
    - rewrite G1 by reg_neq_tac. rewrite R26, exnft_v_addi_lit. reflexivity.
    - unfold regs1. rewrite getr_same by reg_neq_tac. reflexivity.
    - apply (exnft_store_ok (w_H Wc) memc m1 (sh + 8) 1); [lia | lia | | apply wbytes_grows].
      intros i Hi. replace (sh + 8 + i) with (sh + 8) by lia. exact P8. }
  apply mst_refl. }
unfold cfg_at.
apply (SRr_msteps rsegs B_prog_wx Wc
  (@YK11.mkst fxc regs (Z_to_bv 64 (exv_pc 0xa70)) memc (YK11.seg_rom rsegs))
  (@YK11.mkst fxc regs1 (exnft_w 0xa7c) m2 (YK11.seg_rom rsegs)) mdc _ Hms).
intros md' Hsame _.
(* the memory after the two stores agrees with the cut's memory off the two shadow bytes *)
assert (Hkeep : forall z, 0 <= z < 2 ^ 64 -> z <> sh + 4 -> z <> sh + 8 ->
  mrestrict (w_H Wc) (munrestrict (w_H Wc) memc m2) (Z_to_bv 64 z) = mrestrict (w_H Wc) memc (Z_to_bv 64 z)).
{ intros z Hz N4 N8. apply exnft_keep_wr. unfold m2. rewrite exnft_wbytes1, (exnft_bv_eqb_ne z (sh + 8)) by lia.
  unfold m1. rewrite exnft_wbytes1, (exnft_bv_eqb_ne z (sh + 4)) by lia. reflexivity. }
assert (KEPT : forall z, 0 <= z < 2 ^ 64 -> z <> sh + 4 -> z <> sh + 8 ->
  aview rsegs (w_H Wc) (munrestrict (w_H Wc) memc m2) z = aview rsegs (w_H Wc) memc z)
  by (intros z Hz N4 N8; apply aview_eq_of; exact (Hkeep z Hz N4 N8)).
assert (MG : mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (munrestrict (w_H Wc) memc m2)))
  by (apply exnft_grows_wr; eapply mem_grows_trans; apply wbytes_grows).
assert (HJ' : ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (spZ (e_regs E) + e_d E) (exv_FP E)
    (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] lyc Sc Hpc Wc
    (munrestrict (w_H Wc) memc m2) md' k).
{ refine (ajournal_x_exec (SK := SK) rsegs B prh_pst ARx LAWS B_prog_segs_low
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun z => z = sh + 4 \/ z = sh + 8) HJ _ MG _ Hsame _).
  - intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). pose proof (u64_range x) as Hxr.
    apply Hkeep; [lia | intro Ex; apply Hx; left; exact Ex | intro Ex; apply Hx; right; exact Ex].
  - intros x Hx. unfold munrestrict. rewrite Hx. reflexivity.
  - intros z Hz. right; right; right. exists 1, pos. split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16.
    change (shadow_addr (frame_addr lyc 1 pos)) with sh.
    destruct Hz as [-> | ->]; lia. }
refine (HX fxc E lyc Sc Hpc Wc regs1 (munrestrict (w_H Wc) memc m2) md' k pos r eq_refl HPRE _ _ _).
- apply (MK fxc lyc Sc Hpc Wc regs memc mdc k regs1 (munrestrict (w_H Wc) memc m2) md' k HPRE HEXB HJ').
  + intros z Hz Hnw. apply KEPT; [exact Hz | |].
    * intro Ez. apply Hnw. unfold EXN_wz. right; right; right; left. exact Ez.
    * intro Ez. apply Hnw. unfold EXN_wz. right; right; right; right; left. exact Ez.
  + intros a Ha. eapply apresent_grows; [exact MG | exact Ha].
  + exact (exnft_mn_run (w_H Wc) memc fxc _ _ _ _ _ Hms).
  + unfold EXN_regs_kept. rewrite !G1 by reg_neq_tac. repeat split; reflexivity.
- rewrite G1 by reg_neq_tac. exact R21.
- apply (exnft_res_keep Wc memc); [|exact HRES].
  intros z Hz. apply KEPT; lia.
Qed.

(* ======== F: CD (0x9a8) -> CT (0xa70) ======== *)
Lemma exn_F : EXN_F B ARx SK E pos.
Proof.
intros fxc lyc Sc Hpc Wc regs memc mdc k j u HPRE HCD.
destruct HCD as ((HEXB & SP144 & SP152) & Hj & HN & R22 & R13 & dl' & Hcur & Hdl01 & Hdl).
change (exv_pc EXN_CD) with (exv_pc 0x9a8).
pose proof (eh_laws B ARx SK HYP) as LAWS.
pose proof asan_consts as (C1 & _).
pose proof HPRE as HP. unfold EXV_PRE in HP. cbv zeta in HP.
destruct HP as (HFP & _ & _ & _ & _ & _ & Hq8 & _ & Hspq & Hqd & _ & _ & _ & _ & Hi0 & _).
destruct HFP as ((_ & _ & _ & _ & _ & Hastk & _) & _).
destruct Hastk as (_ & Hstk0 & Hceil & Hslo & _).
pose proof HEXB as HB. unfold EXB in HB. cbv zeta in HB.
destruct HB as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & R2 & R8 & R9 & R18 & R24 & R25 & R26 & R19 & R3 & R4
  & _ & _ & _ & _ & _ & _ & _ & HQR & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
destruct Hstatic as (_ & _ & _ & _ & Hhi & H47 & _).
pose proof (exv_s1_le E) as ((S1a & S1b) & _).
unfold exv_sp in *.
unfold YG0d.w64 in *.
set (q := e_q E) in *.
assert (Hstk : forall a, q <= a < q + 8 -> apresent (w_H Wc) memc a) by (intros a Ha; apply Hpres; lia).
(* the shadow byte of q reads 0: EXB's range_addressable at q + 7, q 8-aligned *)
destruct (HQR (q + 7) ltac:(lia)) as (s & Hs & Hok).
replace (shadow_of_addr SHADOW_OFF (q + 7)) with (shadow_addr q) in Hs
  by (unfold shadow_of_addr, shadow_addr; lia).
assert (Hs0 : s = 0).
{ destruct Hok as [Hok | (Hm & Hs8)]; [exact Hok|]. exfalso.
  assert ((q + 7) mod 8 = 7) by lia. lia. }
subst s.
unfold aview in Hs.
destruct (mbyte rsegs (mrestrict (w_H Wc) memc) (shadow_addr q)) as [b|] eqn:Eb; [|discriminate Hs].
cbn in Hs. injection Hs as Hb0.
set (m0 := mrestrict (w_H Wc) memc).
set (bs := word_to_le_bytes 8 (Z_to_bv 64 (e_x0 E + Z.of_nat j))).
set (mF := wbytes m0 (Z_to_bv 64 q) bs).
set (regs1 := YK11.regupd regs 10 (Z_to_bv 64 (bv_unsigned b))).
set (regs2 := YK11.regupd regs1 21 (Z_to_bv 64 0)).
assert (G2 : forall r0 : bv 5, r0 <> 10%bv -> r0 <> 21%bv -> YK11.getr regs2 r0 = YK11.getr regs r0)
  by (intros r0 N1 N2; unfold regs2, regs1; rewrite !getr_other by assumption; reflexivity).
assert (Hms : msteps rsegs (@YK11.mkst fxc regs (exnft_w 0x9a8) m0 (YK11.seg_rom rsegs))
                           (@YK11.mkst fxc regs2 (exnft_w 0xa70) mF (YK11.seg_rom rsegs))).
{ eapply mst_step; [reflexivity | |].
  { refine (exnft_step_lbu fxc regs m0 0x9a8 0x9ac 0x6c503 10 13 0 b eq_refl I_9a8 eq_refl _).
    rewrite R13, exnft_bvs0, exnft_v_addi_lit, Z.add_0_r.
    apply (proj2 (rdn_mbytes rsegs m0 1 (shadow_addr q) [b])). split; [reflexivity|].
    intros i Hi. destruct i as [|i]; [|lia]. cbn [Z.of_nat nth_error]. rewrite Z.add_0_r. exact Eb. }
  eapply mst_step; [reflexivity | |].
  { (* bnez a0 to the errpath_store8 arm: not taken, the shadow byte is 0 *)
    refine (exnft_step_bft fxc regs1 m0 0x9ac 0x9b0 0x38051063 BC_NE 10 0 896 eq_refl I_9ac _).
    unfold regs1. rewrite getr_same by reg_neq_tac. rewrite getr_zero, Hb0. reflexivity. }
  eapply mst_step; [reflexivity | |].
  { refine (exnft_step_addi fxc regs1 m0 0x9b0 0x9b4 0xa93 21 0 0 (Z_to_bv 64 0) eq_refl I_9b0 eq_refl _).
    rewrite getr_zero, exnft_bvs0, exnft_v_addi_lit. reflexivity. }
  eapply mst_step; [reflexivity | |].
  { refine (exnft_step_sd fxc regs2 m0 0x9b4 0x9b8 0x169b023 19 22 0 (Z_to_bv 64 q)
      (Z_to_bv 64 (e_x0 E + Z.of_nat j)) eq_refl I_9b4 _ _ _).
    - rewrite G2 by reg_neq_tac. rewrite R19, exnft_bvs0, exnft_v_addi_lit, Z.add_0_r. reflexivity.
    - rewrite G2 by reg_neq_tac. exact R22.
    - apply (exnft_store_ok (w_H Wc) memc m0 q 8); [lia | lia | | apply mem_grows_refl].
      intros i Hi. apply Hstk. lia. }
  eapply mst_step; [reflexivity | |].
  { exact (exnft_step_j fxc regs2 mF 0x9b8 0xa70 0xb80006f 184 eq_refl I_9b8). }
  apply mst_refl. }
unfold cfg_at.
apply (SRr_msteps rsegs B_prog_wx Wc
  (@YK11.mkst fxc regs (Z_to_bv 64 (exv_pc 0x9a8)) memc (YK11.seg_rom rsegs))
  (@YK11.mkst fxc regs2 (exnft_w 0xa70) mF (YK11.seg_rom rsegs)) mdc _ Hms).
intros md' Hsame _.
(* the memory after the store agrees with the cut's memory off [q, q + 8) *)
assert (Hkeep : forall z, 0 <= z < 2 ^ 64 -> ~ (q <= z < q + 8) ->
  mrestrict (w_H Wc) (munrestrict (w_H Wc) memc mF) (Z_to_bv 64 z) = mrestrict (w_H Wc) memc (Z_to_bv 64 z)).
{ intros z Hz Hn. apply exnft_keep_wr. unfold mF.
  destruct (Z_lt_le_dec z q) as [Hlt | Hge].
  - apply wbytes_below; rewrite ?u64_lit by lia; try unfold bs; rewrite ?exnft_wtl8_len; lia.
  - apply wbytes_above; rewrite ?u64_lit by lia; try unfold bs; rewrite ?exnft_wtl8_len; lia. }
assert (KEPT : forall z, 0 <= z < 2 ^ 64 -> ~ (q <= z < q + 8) ->
  aview rsegs (w_H Wc) (munrestrict (w_H Wc) memc mF) z = aview rsegs (w_H Wc) memc z)
  by (intros z Hz Hn; apply aview_eq_of; exact (Hkeep z Hz Hn)).
assert (MG : mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (munrestrict (w_H Wc) memc mF)))
  by (apply exnft_grows_wr; apply wbytes_grows).
assert (HJ' : ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (spZ (e_regs E) + e_d E) (exv_FP E)
    (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] lyc Sc Hpc Wc
    (munrestrict (w_H Wc) memc mF) md' k).
{ refine (ajournal_x_exec (SK := SK) rsegs B prh_pst ARx LAWS B_prog_segs_low
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun z => q <= z < q + 8) HJ _ MG _ Hsame _).
  - intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). pose proof (u64_range x) as Hxr.
    apply Hkeep; [lia | exact Hx].
  - intros x Hx. unfold munrestrict. rewrite Hx. reflexivity.
  - intros z Hz. left. lia. }
(* in->p := x0 + j: the cursor *)
unfold EXN_cur in Hcur.
assert (Hcur' : prhex_cur Wc (munrestrict (w_H Wc) memc mF) q (e_x0 E + Z.of_nat j) (e_x0 E + exv_len E) (e_dep E)
    (e_scr E) dl').
{ destruct Hcur as (_ & C8 & C16 & C24 & C32).
  split; [|split; [|split; [|split]]].
  - intros kk Hk.
    rewrite mrestrict_munrestrict.
    rewrite exnft_mbyte_vis by exact (proj1 (Hstk (q + Z.of_nat kk) ltac:(lia))).
    unfold mF. rewrite wbytes_mbyte by (try unfold bs; rewrite ?exnft_wtl8_len; lia).
    unfold bs. rewrite exnft_wtl8_len.
    replace ((q <=? q + Z.of_nat kk) && (q + Z.of_nat kk <? q + Z.of_nat 8)) with true
      by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    replace (Z.to_nat (q + Z.of_nat kk - q)) with kk by lia.
    apply exnft_wtl8_nth. exact Hk.
  - eapply ExvB_Num_eng.exw_val_kept; [|exact C8]. intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply KEPT; lia.
  - eapply ExvB_Num_eng.exw_val_kept; [|exact C16]. intros x Hx. change (Z.of_nat 4) with 4 in Hx. apply KEPT; lia.
  - eapply ExvB_Num_eng.exw_val_kept; [|exact C24]. intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply KEPT; lia.
  - eapply ExvB_Num_eng.exw_val_kept; [|exact C32]. intros x Hx. change (Z.of_nat 4) with 4 in Hx. apply KEPT; lia. }
refine (exn_T fxc lyc Sc Hpc Wc regs2 (munrestrict (w_H Wc) memc mF) md' k 0 HPRE _).
split; [split; [|split]|split].
- apply (MC fxc lyc Sc Hpc Wc regs memc mdc k regs2 (munrestrict (w_H Wc) memc mF) md' k HPRE HEXB HJ').
  + intros z Hz _ Hn _. apply KEPT; [exact Hz | exact Hn].
  + intros a Ha. eapply apresent_grows; [exact MG | exact Ha].
  + exact (exnft_mn_run (w_H Wc) memc fxc _ _ _ _ _ Hms).
  + unfold EXN_regs_kept. rewrite !G2 by reg_neq_tac. repeat split; reflexivity.
- apply (KS Wc memc); [exact SP144|]. intros z Hz. apply KEPT; lia.
- apply (KS Wc memc); [exact SP152|]. intros z Hz. apply KEPT; lia.
- unfold regs2. rewrite getr_same by reg_neq_tac. reflexivity.
- apply (exnft_res0 Wc _ j u dl' Hi0 ltac:(lia) HN Hcur' Hdl01 Hdl).
Qed.
End p.

Print Assumptions exn_T.
Print Assumptions exn_F.
