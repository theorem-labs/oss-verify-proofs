(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image A' (#102 asan 1be0f53d, unstripped twin bff8519b), ex_value piece 5
   (ev_number), lane FT of S8aNumCut.v: the sub-pieces
     F  CD +0x9e4 -> CT +0x9f4   (0x83c88-0x83c94; report arm +0xd74 = 0x84018 not reached)
     T  CT +0x9f4 -> EV_EXIT +0xaa4   (0x83c98-0x83cac)
   (ev_F, ev_T) and the pure dispatch lemma ev_V_N: under ev_at_kind's dispatch facts the text's reading at the
   activation (prhex_V) is the number arm's (ev_N, PjGrammar.jrv's last arm, PjGrammar.v:285-300).
   Method: the ten instructions are stepped by hand (RiscvSemantics.step through YK11 / YK14 / YK0v's step lemmas, each
   word fetched from the program listing by YC1fP's pa_fetch_pw), one msteps per sub-piece, closed by YSRrMemnorm's
   SRr_msteps_inv (YA0n's SRr_msteps with the invariant P := YAkMemnorm.memnorm SEGS, laws srr_inv_laws_memnorm_k).
   The shadow byte of in (q) reads 0 by the allocator relation's zero-shadow law on the real stack
   (alx_zshadow); the three stores (in->p at q, the frame's shadow bytes +4 / +8) are inside the journal's write set
   (the caller window / the own frame's shadow), so YCbqG's ajournal_x_exec carries the journal, and ev_mid follows by
   lane M's ev_mid_cur_stmt / ev_mid_keep_stmt (Section Hypotheses MIDC / MIDK).
   MEMNORM (a state fact, ev_mid's last conjunct): the cut's MID gives YAkMemnorm.memnorm of the entry memory, which
   is YAkMemnorm.memnorm by conversion; SRr_msteps_inv returns memnorm of the memory after the run, and that is the
   memnorm premise of MIDC (F) / MIDK (T). No memnorm hypothesis.
   Numerals (layer brief rule 4): 7364 (DERIVED: ex_value's slot 1841 * 4, PAImg_prog.v A_entry_ex_value);
   0x9e4 .. 0xa08, 0xaa4 (LENGTH: offsets into ex_value, f0d2e8d4 listing, the same at #102); 4 (LENGTH: instruction bytes); 156, 908
   (WORD: the jump / branch distances encoded in the words); 0xd4503 0x38051663 0xa93 0x169b023 0xff800513 0xac8223
   0xac8423 0xb8b13 0xa8d93 0x9c0006f (WORD: the instruction words of listing slots 2474-2483); the register numbers
   0 10 19 21 22 23 25 26 27 and the immediates 0 4 8 4088 (WORD, decoded from those words); -8 (WORD: the byte 0xf8
   the tail writes, `li a0, -8`); 8, 16, 32, 40, 104, 112, 128, 256 (LENGTH: the granule, struct ex / frame / spill
   sizes and offsets, the save area); 2 ^ 47, 2 ^ 64 (LENGTH: address-space bounds); 34 91 123 102 110 116 (WORD:
   ASCII dispatch bytes). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0v YK00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YN01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallMx YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YSRrMemnorm YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S8aIface S8aNumCut.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S8aModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
(* lia in this import set (CJ/Lib/LiaTuning.v is loaded) needs the euclidean-division flag on *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======== the pure dispatch lemma ======== *)

Lemma ft_skipn_cons : forall (x : list Z) (i : nat), (i < length x)%nat -> skipn i x = nth i x 0 :: skipn (S i) x.
Proof. induction x as [|b x IH]; intros [|i] Hi; cbn in *; try lia; [reflexivity|]. apply IH. lia. Qed.

(* ev_at_kind's dispatch facts (the skip lands on byte c at i1; c is no opener, quote or word letter) make the text's
   reading at the activation the number arm's: WalkS8a's model lemmas S8aModel.prhex_V_skip (the blanks) and
   prhex_V_cons (PjGrammar.jrv's dispatch, PjGrammar.v:285-300), whose last arm is ev_N's jr_number *)
Lemma ev_V_N : forall (dep : Z) (x : list Z) (i0 i1 : nat) (c : Z),
  (i1 < length x)%nat -> nth i1 x 0 = c -> PjGrammar.ws c = false ->
  PjGrammar.skip (skipn i0 x) = skipn i1 x ->
  c <> 34 -> c <> 91 -> c <> 123 -> c <> 102 -> c <> 110 -> c <> 116 ->
  prhex_V dep (skipn i0 x) = ev_N (skipn i1 x).
Proof.
intros dep x i0 i1 c Hi Hc Hws Hsk H34 H91 H123 H102 H110 H116.
rewrite S8aModel.prhex_V_skip, Hsk, (ft_skipn_cons x i1 Hi), Hc.
rewrite (S8aModel.prhex_V_cons dep c (skipn (S i1) x) Hws).
rewrite (proj2 (Z.eqb_neq c 123) H123), (proj2 (Z.eqb_neq c 91) H91), (proj2 (Z.eqb_neq c 34) H34),
  (proj2 (Z.eqb_neq c 116) H116), (proj2 (Z.eqb_neq c 102) H102), (proj2 (Z.eqb_neq c 110) H110).
reflexivity.
Qed.

(* ======== machine helpers (no image) ======== *)

Lemma ft_v_addi_lit : forall v d, v_addi (Z_to_bv 64 v) d = Z_to_bv 64 (v + d).
Proof.
intros v d. unfold v_addi. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma ft_bvs0 : bv_signed (0%bv : bv 12) = 0.
Proof. reflexivity. Qed.

Lemma ft_bv_eqb_ne : forall u v, 0 <= u < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> u <> v ->
  bv_eqb (Z_to_bv 64 u) (Z_to_bv 64 v) = false.
Proof. intros u v Hu Hv Hne. unfold bv_eqb. rewrite !u64_lit by lia. apply Z.eqb_neq. exact Hne. Qed.

Lemma ft_wbytes1 : forall (m : word -> option byte) (a : word) (b : byte) (x : word),
  wbytes m a [b] x = if bv_eqb x a then Some b else m x.
Proof. reflexivity. Qed.

Lemma ft_keep_wr : forall (Hh : word -> bool) (mem m' : word -> option byte) x,
  m' x = mrestrict Hh mem x -> mrestrict Hh (munrestrict Hh mem m') x = mrestrict Hh mem x.
Proof. intros Hh mem m' x E. rewrite mrestrict_munrestrict. unfold mrestrict in *. destruct (Hh x); [reflexivity | exact E]. Qed.

Lemma ft_grows_wr : forall (Hh : word -> bool) (mem m' : word -> option byte),
  mem_grows (mrestrict Hh mem) m' -> mem_grows (mrestrict Hh mem) (mrestrict Hh (munrestrict Hh mem m')).
Proof.
intros Hh mem m' G x Hx. pose proof (G x Hx) as Gx. rewrite mrestrict_munrestrict.
unfold mrestrict in *. destruct (Hh x); [exact Hx | exact Gx].
Qed.

Lemma ft_zsh_idx : forall lo hi q, q mod 8 = 0 -> lo <= q -> q + 40 <= hi ->
  0 <= q / 8 - lo / 8 < (hi - lo) / 8.
Proof. intros lo hi q Hq Hlo Hhi. Z.div_mod_to_equations. lia. Qed.

Lemma ft_sh_bound : forall x, 0 <= x <= 2 ^ 47 -> 0 <= shadow_addr x /\ shadow_addr x + 16 < 2 ^ 64.
Proof. intros x Hx. unfold shadow_addr, SHADOW_OFF. Z.div_mod_to_equations. lia. Qed.

Lemma ft_wtl8_len : forall v : word, length (word_to_le_bytes 8 v) = 8%nat.
Proof. intros v. unfold word_to_le_bytes. apply length_Z_to_le_bytes. Qed.

(* the k-th byte of an 8-byte little-endian store is val_mem's k-th byte *)
Lemma ft_wtl8_nth : forall v (kk : nat), (kk < 8)%nat ->
  nth_error (word_to_le_bytes 8 (Z_to_bv 64 v)) kk = Some (Z_to_bv 8 (le_byte v 8 kk)).
Proof.
intros v kk Hk. unfold word_to_le_bytes. rewrite nth_error_Z_to_le_bytes by exact Hk. f_equal.
apply bv_eq. cbv beta delta [YG0f.le_byte YO0f.le_byte]. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ (8 * Z.of_nat 8)).
rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* one instruction of the listing: slot (7364 + off) / 4 holds the plain word w, which decodes to i *)
Definition ev_ins (off w : Z) (i : instr) : Prop :=
  plookup A_prog_tpi (7364 + off) = Some (PW w) /\ is_ecall (Z_to_bv 32 w) = false /\
  decode_any (Z_to_bv 32 w) = Some (i, 4%Z).
Ltac ev_ins_tac := refine (conj _ (conj _ _)); [vm_compute; reflexivity | vm_compute; reflexivity | vm_refl_bv].

Lemma I_9e4 : ev_ins 0x9e4 0xd4503 (Load SZ1 false 10 26 0). Proof. ev_ins_tac. Qed.
Lemma I_9e8 : ev_ins 0x9e8 0x38051663 (Branch BC_NE 10 0 908). Proof. ev_ins_tac. Qed.
Lemma I_9ec : ev_ins 0x9ec 0xa93 (OpImm ALU_ADD 21 0 0). Proof. ev_ins_tac. Qed.
Lemma I_9f0 : ev_ins 0x9f0 0x169b023 (Store SZ8 19 22 0). Proof. ev_ins_tac. Qed.
Lemma I_9f4 : ev_ins 0x9f4 0xff800513 (OpImm ALU_ADD 10 0 4088). Proof. ev_ins_tac. Qed.
Lemma I_9f8 : ev_ins 0x9f8 0xac8223 (Store SZ1 25 10 4). Proof. ev_ins_tac. Qed.
Lemma I_9fc : ev_ins 0x9fc 0xac8423 (Store SZ1 25 10 8). Proof. ev_ins_tac. Qed.
Lemma I_a00 : ev_ins 0xa00 0xb8b13 (OpImm ALU_ADD 22 23 0). Proof. ev_ins_tac. Qed.
Lemma I_a04 : ev_ins 0xa04 0xa8d93 (OpImm ALU_ADD 27 21 0). Proof. ev_ins_tac. Qed.
Lemma I_a08 : ev_ins 0xa08 0x9c0006f (Jal 0 156). Proof. ev_ins_tac. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams} {PI : PrhImg} {RL : PrhRoomLive}.
Context {PA : PAImg A_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* the entry of ex_value in the listing (DERIVED: slot 1841 * 4; discharged at PI_prog_A by A_entry_ex_value) *)
Hypothesis Hent : SIGMA AS_ex_value = BASE + 7364.
(* lane M's ev_mid preservation statements (S8aNumCut.v:204-216) *)
Hypothesis MIDK : forall a, ev_mid_keep_stmt B ARx SK a.
Hypothesis MIDC : forall a, ev_mid_cur_stmt B ARx SK a.
(* the pc at offset off of ex_value *)
Definition evw (off : Z) : word := Z_to_bv 64 (SIGMA AS_ex_value + off).

Lemma evw_add : forall off d, v_addi (evw off) d = evw (off + d).
Proof. intros off d. unfold evw. rewrite ft_v_addi_lit, Z.add_assoc. reflexivity. Qed.

Lemma ev_fetch : forall off w, plookup A_prog_tpi (7364 + off) = Some (PW w) ->
  fetch_word SEGS (evw off) = Some (Z_to_bv 32 w).
Proof.
intros off w H. unfold evw. rewrite Hent, <- Z.add_assoc.
exact (pa_fetch_pw (PL := PL_prog_A) (PI := PA) (7364 + off) w H).
Qed.

Lemma ev_step_lbu : forall (f : YK11.FPState) regs mem off off' w rd rs (imm : bv 12) b,
  off' = off + 4 -> ev_ins off w (Load SZ1 false rd rs imm) -> bv_eqb rd 0 = false ->
  rdn SEGS mem (v_addi (getr regs rs) (bv_signed imm)) 1%nat = Some [b] ->
  RiscvSemantics.step SEGS (@YK11.mkst f regs (evw off) mem (YK11.seg_rom SEGS)) =
  MachineOk (@YK11.mkst f (regupd regs rd (Z_to_bv 64 (bv_unsigned b))) (evw off') mem (YK11.seg_rom SEGS)).
Proof.
intros f regs mem off off' w rd rs imm b -> (HL & HE & HD) Hrd Hr.
rewrite (step_lbu (fx := f) SEGS regs (evw off) mem (YK11.seg_rom SEGS) (Z_to_bv 32 w) rd rs imm b (ev_fetch off w HL) HE HD Hr).
rewrite Hrd, evw_add. reflexivity.
Qed.

Lemma ev_step_bft : forall (f : YK11.FPState) regs mem off off' w c rs1 rs2 (imm : bv 13),
  off' = off + 4 -> ev_ins off w (Branch c rs1 rs2 imm) -> branch_taken c (getr regs rs1) (getr regs rs2) = false ->
  RiscvSemantics.step SEGS (@YK11.mkst f regs (evw off) mem (YK11.seg_rom SEGS)) =
  MachineOk (@YK11.mkst f regs (evw off') mem (YK11.seg_rom SEGS)).
Proof.
intros f regs mem off off' w c rs1 rs2 imm -> (HL & HE & HD) Hc.
rewrite (step_branch_ft_gen (fx := f) SEGS regs (evw off) mem (YK11.seg_rom SEGS) (Z_to_bv 32 w) c rs1 rs2 imm (ev_fetch off w HL) HE HD Hc).
rewrite evw_add. reflexivity.
Qed.

Lemma ev_step_addi : forall (f : YK11.FPState) regs mem off off' w rd rs (imm : bv 12) v,
  off' = off + 4 -> ev_ins off w (OpImm ALU_ADD rd rs imm) -> bv_eqb rd 0 = false ->
  v_addi (getr regs rs) (bv_signed imm) = v ->
  RiscvSemantics.step SEGS (@YK11.mkst f regs (evw off) mem (YK11.seg_rom SEGS)) =
  MachineOk (@YK11.mkst f (regupd regs rd v) (evw off') mem (YK11.seg_rom SEGS)).
Proof.
intros f regs mem off off' w rd rs imm v -> (HL & HE & HD) Hrd Hv.
rewrite (step_addi_at (fx := f) SEGS regs (evw off) mem (YK11.seg_rom SEGS) (Z_to_bv 32 w) rd rs imm v (ev_fetch off w HL) HE HD Hrd Hv).
rewrite evw_add. reflexivity.
Qed.

Lemma ev_step_sd : forall (f : YK11.FPState) regs mem off off' w rs1 rs2 (imm : bv 12) (a v : word),
  off' = off + 4 -> ev_ins off w (Store SZ8 rs1 rs2 imm) ->
  v_addi (getr regs rs1) (bv_signed imm) = a -> getr regs rs2 = v ->
  RiscvSemantics.store_ok SEGS mem a 8%nat = true ->
  RiscvSemantics.step SEGS (@YK11.mkst f regs (evw off) mem (YK11.seg_rom SEGS)) =
  MachineOk (@YK11.mkst f regs (evw off') (wbytes mem a (word_to_le_bytes 8 v)) (YK11.seg_rom SEGS)).
Proof.
intros f regs mem off off' w rs1 rs2 imm a v -> (HL & HE & HD) Ha Hv Hok.
rewrite (step_sd_at (fx := f) SEGS regs (evw off) mem (YK11.seg_rom SEGS) (Z_to_bv 32 w) rs1 rs2 imm a v (ev_fetch off w HL) HE HD Ha Hv Hok).
rewrite evw_add. reflexivity.
Qed.

Lemma ev_step_sb : forall (f : YK11.FPState) regs mem off off' w rs1 rs2 (imm : bv 12) (a v : word) (b : byte),
  off' = off + 4 -> ev_ins off w (Store SZ1 rs1 rs2 imm) ->
  v_addi (getr regs rs1) (bv_signed imm) = a -> getr regs rs2 = v -> Z_to_bv 8 (bv_unsigned v) = b ->
  RiscvSemantics.store_ok SEGS mem a 1%nat = true ->
  RiscvSemantics.step SEGS (@YK11.mkst f regs (evw off) mem (YK11.seg_rom SEGS)) =
  MachineOk (@YK11.mkst f regs (evw off') (wbytes mem a [b]) (YK11.seg_rom SEGS)).
Proof.
intros f regs mem off off' w rs1 rs2 imm a v b -> (HL & HE & HD) Ha Hv Hb Hok.
rewrite (step_sb_at (fx := f) SEGS regs (evw off) mem (YK11.seg_rom SEGS) (Z_to_bv 32 w) rs1 rs2 imm a v b (ev_fetch off w HL) HE HD Ha Hv Hb Hok).
rewrite evw_add. reflexivity.
Qed.

Lemma ev_step_j : forall (f : YK11.FPState) regs mem off off' w (imm : bv 21),
  off' = off + bv_signed imm -> ev_ins off w (Jal 0 imm) ->
  RiscvSemantics.step SEGS (@YK11.mkst f regs (evw off) mem (YK11.seg_rom SEGS)) =
  MachineOk (@YK11.mkst f regs (evw off') mem (YK11.seg_rom SEGS)).
Proof.
intros f regs mem off off' w imm -> (HL & HE & HD).
rewrite (step_jal_link (fx := f) SEGS regs (evw off) mem (YK11.seg_rom SEGS) (Z_to_bv 32 w) 0 imm (ev_fetch off w HL) HE HD).
unfold btgt. rewrite (evw_add off (bv_signed imm)). reflexivity.
Qed.

(* a store of n bytes at a is allowed when every byte is present and visible *)
Lemma ft_store_ok : forall (Hh : word -> bool) (mem m : word -> option byte) a (n : nat),
  0 <= a < 2 ^ 64 -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> apresent Hh mem (a + i)) ->
  mem_grows (mrestrict Hh mem) m ->
  RiscvSemantics.store_ok SEGS m (Z_to_bv 64 a) n = true.
Proof.
intros Hh mem m a n Ha Hn Hp Hg.
pose proof (Nat2Z.is_nonneg n) as Hn0.
pose proof (u64_lit a Ha) as Ea.
apply (store_ok_mono SEGS n (mrestrict Hh mem) m _ Hg).
apply store_ok_of_all.
- rewrite Ea. exact Hn.
- intros x Hx. rewrite Ea in Hx.
  assert (Hi : 0 <= bv_unsigned x - a < Z.of_nat n) by lia.
  pose proof (apresent_writable SEGS Hh mem (a + (bv_unsigned x - a)) (Hp _ Hi)) as Hw.
  unfold writable_at in Hw. replace (a + (bv_unsigned x - a)) with (bv_unsigned x) in Hw by lia.
  rewrite Z_to_bv_bv_unsigned in Hw. exact Hw.
Qed.

Lemma ft_mbyte_vis : forall (Hh : word -> bool) (m : word -> option byte) z,
  Hh (Z_to_bv 64 z) = false -> mbyte SEGS (mrestrict Hh m) z = mbyte SEGS m z.
Proof. intros Hh m z E. unfold mbyte, mrestrict. rewrite E. reflexivity. Qed.

Lemma ft_val_mem_keep : forall (m m' : word -> option byte) a (n : nat) v,
  (forall kk, (kk < n)%nat -> mbyte SEGS m' (a + Z.of_nat kk) = mbyte SEGS m (a + Z.of_nat kk)) ->
  val_mem SEGS m a n v -> val_mem SEGS m' a n v.
Proof. intros m m' a n v E H kk Hk. rewrite (E kk Hk). exact (H kk Hk). Qed.

(* ======== T: CT +0x9f4 -> EV_EXIT +0xaa4 ========
   +0x9f4 li a0, -8; +0x9f8 sb a0, 4(s9); +0x9fc sb a0, 8(s9) (the frame's shadow bytes +4, +8 := 0xf8);
   +0xa00 mv s6, s7 (the frame); +0xa04 mv s11, s5 (r); +0xa08 j +0xaa4 *)
Lemma ev_T : ev_T_stmt B ARx SK.
Proof.
intros _ a fxc W regs mem md ly S Hp k i1 c Hpre Hfx HCT.
destruct HCT as (Hbase & r & p' & dl' & R21 & Hmid & Hdl01 & Hout).
pose proof Hbase as (Hregs & R23 & Hi1 & Hc & Hws & Hsk & H34 & H91 & H123 & H102 & H110 & H116 & _).
pose proof Hregs as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
pose proof Hmid as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMN).
(* MID's memnorm, the run's invariant P := YAkMemnorm.memnorm SEGS (by conversion) *)
assert (HPM : YAkMemnorm.memnorm SEGS mem) by exact HMN. clear HMN.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hdep & _).
unfold YG0d.w64 in *.
pose proof asan_consts as (C1 & _).
assert (LF : ly_F ly = ly_F (ea_ly a)) by (destruct Hly as (_ & _ & _ & _ & _ & E & _); exact E).
assert (Hin : In (1, ea_pos a) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (Efr : frame_addr ly 1 (ea_pos a) = ea_fr a) by (unfold ea_fr, frame_addr; rewrite LF; reflexivity).
pose proof (alx_frames SEGS B ARx LAWS ly S Hp W mem md 1 (ea_pos a) HAR Hin) as (_ & _ & _ & Hshp).
pose proof (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md 1 (ea_pos a) HAR Hin) as (Hf0 & Hfc & _).
rewrite Efr in Hshp, Hf0, Hfc. change (fs_frame_bytes 1) with 128 in Hfc. change (fs_frame_bytes 1 / 8) with 16 in Hshp.
set (fr := ea_fr a) in *.
pose proof (ft_sh_bound fr ltac:(lia)) as Hshr.
set (sh := shadow_addr fr) in *.
assert (P4 : apresent (w_H W) mem (sh + 4)) by exact (proj1 (Hshp 4 ltac:(lia))).
assert (P8 : apresent (w_H W) mem (sh + 8)) by exact (proj1 (Hshp 8 ltac:(lia))).
set (b8 := Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-8)))).
set (m0 := mrestrict (w_H W) mem).
set (m1 := wbytes m0 (Z_to_bv 64 (sh + 4)) [b8]).
set (m2 := wbytes m1 (Z_to_bv 64 (sh + 8)) [b8]).
set (regs1 := regupd regs 10 (Z_to_bv 64 (-8))).
set (regs4 := regupd regs1 22 (Z_to_bv 64 fr)).
set (regs5 := regupd regs4 27 (Z_to_bv 64 r)).
assert (G1 : forall r0 : bv 5, r0 <> 10%bv -> getr regs1 r0 = getr regs r0)
  by (intros r0 N; unfold regs1; rewrite getr_other by exact N; reflexivity).
assert (G5 : forall r0 : bv 5, r0 <> 10%bv -> r0 <> 22%bv -> r0 <> 27%bv -> getr regs5 r0 = getr regs r0)
  by (intros r0 N1 N2 N3; unfold regs5, regs4, regs1; rewrite !getr_other by assumption; reflexivity).
assert (Hms : msteps SEGS (@YK11.mkst fxc regs (evw 0x9f4) m0 (YK11.seg_rom SEGS))
                          (@YK11.mkst fxc regs5 (evw 0xaa4) m2 (YK11.seg_rom SEGS))).
{ eapply mst_step; [reflexivity | |].
  { refine (ev_step_addi fxc regs m0 0x9f4 0x9f8 0xff800513 10 0 4088 (Z_to_bv 64 (-8)) eq_refl I_9f4 eq_refl _).
    rewrite getr_zero, ft_v_addi_lit. f_equal. }
  eapply mst_step; [reflexivity | |].
  { refine (ev_step_sb fxc regs1 m0 0x9f8 0x9fc 0xac8223 25 10 4 (Z_to_bv 64 (sh + 4)) (Z_to_bv 64 (-8)) b8
      eq_refl I_9f8 _ _ eq_refl _).
    - rewrite G1 by reg_neq_tac. rewrite R25, ft_v_addi_lit. reflexivity.
    - unfold regs1. rewrite getr_same by reg_neq_tac. reflexivity.
    - apply (ft_store_ok (w_H W) mem m0 (sh + 4) 1); [lia | lia | | apply mem_grows_refl].
      intros i Hi. replace (sh + 4 + i) with (sh + 4) by lia. exact P4. }
  eapply mst_step; [reflexivity | |].
  { refine (ev_step_sb fxc regs1 m1 0x9fc 0xa00 0xac8423 25 10 8 (Z_to_bv 64 (sh + 8)) (Z_to_bv 64 (-8)) b8
      eq_refl I_9fc _ _ eq_refl _).
    - rewrite G1 by reg_neq_tac. rewrite R25, ft_v_addi_lit. reflexivity.
    - unfold regs1. rewrite getr_same by reg_neq_tac. reflexivity.
    - apply (ft_store_ok (w_H W) mem m1 (sh + 8) 1); [lia | lia | | apply wbytes_grows].
      intros i Hi. replace (sh + 8 + i) with (sh + 8) by lia. exact P8. }
  eapply mst_step; [reflexivity | |].
  { refine (ev_step_addi fxc regs1 m2 0xa00 0xa04 0xb8b13 22 23 0 (Z_to_bv 64 fr) eq_refl I_a00 eq_refl _).
    rewrite G1 by reg_neq_tac. rewrite R23, ft_bvs0, ft_v_addi_lit, Z.add_0_r. reflexivity. }
  eapply mst_step; [reflexivity | |].
  { refine (ev_step_addi fxc regs4 m2 0xa04 0xa08 0xa8d93 27 21 0 (Z_to_bv 64 r) eq_refl I_a04 eq_refl _).
    unfold regs4. rewrite getr_other by reg_neq_tac. rewrite G1 by reg_neq_tac.
    rewrite R21, ft_bvs0, ft_v_addi_lit, Z.add_0_r. reflexivity. }
  eapply mst_step; [reflexivity | |].
  { exact (ev_step_j fxc regs5 m2 0xa08 0xaa4 0x9c0006f 156 eq_refl I_a08). }
  apply mst_refl. }
unfold ev_cfg.
apply (YC80x.SRr_msteps_inv SEGS (@pa_wx _ A_prog_listing PA) (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS) W
  (@YK11.mkst fxc regs (Z_to_bv 64 (ev_pc 0x9f4)) mem (YK11.seg_rom SEGS))
  (@YK11.mkst fxc regs5 (evw 0xaa4) m2 (YK11.seg_rom SEGS)) md _ Hms HPM).
intros md' Hsame _ HPM'.
change (YAkMemnorm.memnorm SEGS (munrestrict (w_H W) mem m2)) in HPM'.
apply SRr_ret.
(* the memory after the two stores agrees with the entry memory off the two shadow bytes *)
assert (Hkeep : forall z, 0 <= z < 2 ^ 64 -> z <> sh + 4 -> z <> sh + 8 ->
  mrestrict (w_H W) (munrestrict (w_H W) mem m2) (Z_to_bv 64 z) = mrestrict (w_H W) mem (Z_to_bv 64 z)).
{ intros z Hz N4 N8. apply ft_keep_wr. unfold m2. rewrite ft_wbytes1, (ft_bv_eqb_ne z (sh + 8)) by lia.
  unfold m1. rewrite ft_wbytes1, (ft_bv_eqb_ne z (sh + 4)) by lia. reflexivity. }
assert (HJ' : ajournal_x (SK := SK) SEGS B prh_pst ARx (ea_STK a + ea_d a) (ea_sp0 a + ea_d a) (ea_FP a)
    (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)] ly S Hp W
    (munrestrict (w_H W) mem m2) md' k).
{ apply (ajournal_x_exec (SK := SK) SEGS B prh_pst ARx LAWS (@pa_segs_low _ A_prog_listing PA)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun z => z = sh + 4 \/ z = sh + 8) HJ).
  - intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). pose proof (u64_range x) as Hxr.
    apply Hkeep; [lia | intro E; apply Hx; left; exact E | intro E; apply Hx; right; exact E].
  - apply ft_grows_wr. eapply mem_grows_trans; apply wbytes_grows.
  - intros x Hx. unfold munrestrict. rewrite Hx. reflexivity.
  - exact Hsame.
  - intros z Hz. right; right; right. exists 1, (ea_pos a). split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite Efr. change (shadow_addr fr) with sh. change (fs_frame_bytes 1 / 8) with 16.
    destruct Hz as [-> | ->]; lia. }
exists fxc, regs5, (munrestrict (w_H W) mem m2), md', ly, S, Hp, k, r, p', (ea_dep a), dl'.
split; [reflexivity|]. split; [exact Hfx|].
split.
{ apply (MIDK a ly S Hp W mem md k (ea_x0 a + p') (ea_dep a) dl' (munrestrict (w_H W) mem m2) md' k Hpre Hmid HJ');
    [|exact HPM'].
  intros z Hz Hnw. apply aview_eq_of. apply Hkeep; [exact Hz | |].
  - intro E. apply Hnw. unfold ev_wz. right; right; right; left. exact E.
  - intro E. apply Hnw. unfold ev_wz. right; right; right; right; left. exact E. }
split.
{ unfold ev_regs. rewrite !G5 by reg_neq_tac. exact Hregs. }
split.
{ unfold regs5. rewrite getr_other by reg_neq_tac. unfold regs4. rewrite getr_same by reg_neq_tac. reflexivity. }
split.
{ unfold regs5. rewrite getr_same by reg_neq_tac. reflexivity. }
unfold ev_out. split; [exact Hdl01|].
rewrite (ev_V_N (ea_dep a) (ea_x a) (Z.to_nat (ea_i0 a)) i1 c Hi1 Hc Hws Hsk H34 H91 H123 H102 H110 H116).
revert Hout. destruct (ev_N (skipn i1 (ea_x a))) as [[u rest]|]; intros (Er & Ep & Edl).
- exact (conj Er (conj Ep (conj eq_refl Edl))).
- split; [exact Er|]. split; [unfold ea_len; lia | lia].
Qed.

(* ======== F: CD +0x9e4 -> CT +0x9f4 ========
   +0x9e4 lbu a0, 0(s10) (the shadow byte of q); +0x9e8 bnez a0, +0xd74 (not taken: it reads 0); +0x9ec li s5, 0;
   +0x9f0 sd s6, 0(s3) (in->p := x0 + j) *)
Lemma ev_F : ev_F_stmt B ARx SK.
Proof.
intros _ a KTa fxc W regs mem md ly S Hp k i1 c j u Hpre Hfx HCD.
destruct HCD as (Hbase & R22 & Hj & HN & dl' & Hmid & Hdl01 & Hdl).
pose proof Hbase as (Hregs & R23 & Hi1 & Hc & Hws & Hsk & H34 & H91 & H123 & H102 & H110 & H116 & Hv).
pose proof Hregs as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
pose proof Hmid as (HJ & _ & _ & _ & _ & Hcur & _ & _ & _ & _ & _ & _ & _ & HMN).
(* MID's memnorm, the run's invariant P := YAkMemnorm.memnorm SEGS (by conversion) *)
assert (HPM : YAkMemnorm.memnorm SEGS mem) by exact HMN. clear HMN.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp & Hastk & _).
pose proof Hpre as (Hfpre & _ & _ & _ & _ & _ & Hq8 & _ & Hspq & Hqd & _).
destruct Hfpre as ((_ & _ & _ & _ & _ & Hastk0 & _) & _).
destruct Hastk as (_ & HSTK' & Hlo & HloS & Hhi & H47 & _).
destruct Hastk0 as (_ & HSTK & _ & HloS0 & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
change (spZ (ea_regs a)) with (ea_sp0 a) in *.
unfold YG0d.w64 in *.
pose proof asan_consts as (C1 & _).
set (q := ea_q a) in *.
assert (Hqr : ly_stk_lo ly <= q /\ q + 40 <= ly_stk_hi ly) by (rewrite Elo, Ehi; lia).
(* the shadow byte of q reads 0: the real stack's zero shadow (alx_zshadow) *)
pose proof (alx_zshadow SEGS B ARx LAWS ly S Hp W mem md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR
  ltac:(left; reflexivity) (q / 8 - ly_stk_lo ly / 8)
  (ft_zsh_idx (ly_stk_lo ly) (ly_stk_hi ly) q Hq8 (proj1 Hqr) (proj2 Hqr))) as Hz.
cbn [fst snd] in Hz.
replace (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (q / 8 - ly_stk_lo ly / 8)) with (shadow_addr q) in Hz
  by (unfold shadow_of_addr, shadow_addr; lia).
unfold aview in Hz.
destruct (mbyte SEGS (mrestrict (w_H W) mem) (shadow_addr q)) as [b|] eqn:Eb; [|discriminate Hz].
cbn in Hz. injection Hz as Hb0.
set (m0 := mrestrict (w_H W) mem).
set (bs := word_to_le_bytes 8 (Z_to_bv 64 (ea_x0 a + Z.of_nat j))).
set (mF := wbytes m0 (Z_to_bv 64 q) bs).
set (regs1 := regupd regs 10 (Z_to_bv 64 (bv_unsigned b))).
set (regs2 := regupd regs1 21 (Z_to_bv 64 0)).
assert (G2 : forall r0 : bv 5, r0 <> 10%bv -> r0 <> 21%bv -> getr regs2 r0 = getr regs r0)
  by (intros r0 N1 N2; unfold regs2, regs1; rewrite !getr_other by assumption; reflexivity).
assert (Hms : msteps SEGS (@YK11.mkst fxc regs (evw 0x9e4) m0 (YK11.seg_rom SEGS))
                          (@YK11.mkst fxc regs2 (evw 0x9f4) mF (YK11.seg_rom SEGS))).
{ eapply mst_step; [reflexivity | |].
  { refine (ev_step_lbu fxc regs m0 0x9e4 0x9e8 0xd4503 10 26 0 b eq_refl I_9e4 eq_refl _).
    rewrite R26, ft_bvs0, ft_v_addi_lit, Z.add_0_r.
    apply (proj2 (rdn_mbytes SEGS m0 1 (shadow_addr q) [b])). split; [reflexivity|].
    intros i Hi. destruct i as [|i]; [|lia]. cbn [Z.of_nat nth_error]. rewrite Z.add_0_r. exact Eb. }
  eapply mst_step; [reflexivity | |].
  { refine (ev_step_bft fxc regs1 m0 0x9e8 0x9ec 0x38051663 BC_NE 10 0 908 eq_refl I_9e8 _).
    unfold regs1. rewrite getr_same by reg_neq_tac. rewrite getr_zero, Hb0. reflexivity. }
  eapply mst_step; [reflexivity | |].
  { refine (ev_step_addi fxc regs1 m0 0x9ec 0x9f0 0xa93 21 0 0 (Z_to_bv 64 0) eq_refl I_9ec eq_refl _).
    rewrite getr_zero, ft_bvs0, ft_v_addi_lit. reflexivity. }
  eapply mst_step; [reflexivity | |].
  { refine (ev_step_sd fxc regs2 m0 0x9f0 0x9f4 0x169b023 19 22 0 (Z_to_bv 64 q)
      (Z_to_bv 64 (ea_x0 a + Z.of_nat j)) eq_refl I_9f0 _ _ _).
    - rewrite G2 by reg_neq_tac. rewrite R19, ft_bvs0, ft_v_addi_lit, Z.add_0_r. reflexivity.
    - rewrite G2 by reg_neq_tac. exact R22.
    - apply (ft_store_ok (w_H W) mem m0 q 8); [lia | lia | | apply mem_grows_refl].
      intros i Hi. apply Hstkp. lia. }
  apply mst_refl. }
unfold ev_cfg.
apply (YC80x.SRr_msteps_inv SEGS (@pa_wx _ A_prog_listing PA) (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS) W
  (@YK11.mkst fxc regs (Z_to_bv 64 (ev_pc 0x9e4)) mem (YK11.seg_rom SEGS))
  (@YK11.mkst fxc regs2 (evw 0x9f4) mF (YK11.seg_rom SEGS)) md _ Hms HPM).
intros md' Hsame _ HPM'.
change (YAkMemnorm.memnorm SEGS (munrestrict (w_H W) mem mF)) in HPM'.
(* the memory after the store agrees with the entry memory off [q, q + 8) *)
assert (Hkeep : forall z, 0 <= z < 2 ^ 64 -> ~ (q <= z < q + 8) ->
  mrestrict (w_H W) (munrestrict (w_H W) mem mF) (Z_to_bv 64 z) = mrestrict (w_H W) mem (Z_to_bv 64 z)).
{ intros z Hz Hn. apply ft_keep_wr. unfold mF.
  destruct (Z_lt_le_dec z q) as [Hlt | Hge].
  - apply wbytes_below; rewrite ?u64_lit by lia; try unfold bs; rewrite ?ft_wtl8_len; lia.
  - apply wbytes_above; rewrite ?u64_lit by lia; try unfold bs; rewrite ?ft_wtl8_len; lia. }
assert (Hmb : forall z, 0 <= z < 2 ^ 64 -> ~ (q <= z < q + 8) ->
  mbyte SEGS (mrestrict (w_H W) (munrestrict (w_H W) mem mF)) z = mbyte SEGS (mrestrict (w_H W) mem) z)
  by (intros z Hz Hn; unfold mbyte; rewrite (Hkeep z Hz Hn); reflexivity).
assert (HJ' : ajournal_x (SK := SK) SEGS B prh_pst ARx (ea_STK a + ea_d a) (ea_sp0 a + ea_d a) (ea_FP a)
    (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)] ly S Hp W
    (munrestrict (w_H W) mem mF) md' k).
{ apply (ajournal_x_exec (SK := SK) SEGS B prh_pst ARx LAWS (@pa_segs_low _ A_prog_listing PA)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun z => q <= z < q + 8) HJ).
  - intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). pose proof (u64_range x) as Hxr.
    apply Hkeep; [lia | exact Hx].
  - apply ft_grows_wr. apply wbytes_grows.
  - intros x Hx. unfold munrestrict. rewrite Hx. reflexivity.
  - exact Hsame.
  - intros z Hz. left. lia. }
(* in->p := x0 + j: the cursor *)
assert (Hcur' : prhex_cur W (munrestrict (w_H W) mem mF) q (ea_x0 a + Z.of_nat j) (ea_x0 a + ea_len a) (ea_dep a)
    (ea_scr a) dl').
{ destruct Hcur as (_ & C8 & C16 & C24 & C32).
  split; [|split; [|split; [|split]]].
  - intros kk Hk.
    rewrite mrestrict_munrestrict.
    rewrite ft_mbyte_vis by exact (proj1 (Hstkp (q + Z.of_nat kk) ltac:(lia))).
    unfold mF. rewrite wbytes_mbyte by (try unfold bs; rewrite ?ft_wtl8_len; lia).
    unfold bs. rewrite ft_wtl8_len.
    replace ((q <=? q + Z.of_nat kk) && (q + Z.of_nat kk <? q + Z.of_nat 8)) with true
      by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    replace (Z.to_nat (q + Z.of_nat kk - q)) with kk by lia.
    apply ft_wtl8_nth. exact Hk.
  - eapply (ft_val_mem_keep _ _ _ 8 _); [intros kk Hk; apply Hmb; lia | exact C8].
  - eapply (ft_val_mem_keep _ _ _ 4 _); [intros kk Hk; apply Hmb; lia | exact C16].
  - eapply (ft_val_mem_keep _ _ _ 8 _); [intros kk Hk; apply Hmb; lia | exact C24].
  - eapply (ft_val_mem_keep _ _ _ 4 _); [intros kk Hk; apply Hmb; lia | exact C32]. }
assert (HCT : ev_CT B ARx SK a W regs2 (munrestrict (w_H W) mem mF) md' ly S Hp k i1 c).
{ split.
  - refine (conj _ (conj _ (conj Hi1 (conj Hc (conj Hws (conj Hsk (conj H34 (conj H91 (conj H123 (conj H102
      (conj H110 (conj H116 _)))))))))))).
    + unfold ev_regs. rewrite !G2 by reg_neq_tac. exact Hregs.
    + rewrite G2 by reg_neq_tac. exact R23.
    + pose proof (Z.mod_pos_bound (ea_SA a) 32 ltac:(lia)) as Hm32.
      assert (HS1 : 0 <= ea_S1 a /\ ea_S1 a + 112 <= q) by (unfold ea_S1, ea_SA in *; lia).
      eapply (ft_val_mem_keep _ _ _ 8 _); [intros kk Hk; apply Hmb; lia | exact Hv].
  - exists 0, (Z.of_nat j), dl'. split; [unfold regs2; rewrite getr_same by reg_neq_tac; reflexivity|].
    split.
    { apply (MIDC a ly S Hp W mem md k (ea_x0 a + Z.of_nat i1) (ea_dep a) dl' (munrestrict (w_H W) mem mF) md' k
        (ea_x0 a + Z.of_nat j) dl' Hpre Hmid HJ').
      - intros z Hz _ Hn _. apply aview_eq_of. apply Hkeep; [exact Hz | exact Hn].
      - exact Hcur'.
      - exact HPM'. }
    split; [exact Hdl01|].
    rewrite HN. split; [reflexivity|]. split; [|exact Hdl].
    rewrite length_skipn. unfold ea_len. lia. }
exact (KTa fxc W regs2 (munrestrict (w_H W) mem mF) md' ly S Hp k i1 c Hpre Hfx HCT).
Qed.
End d.
