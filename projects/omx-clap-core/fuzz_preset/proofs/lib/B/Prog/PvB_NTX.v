(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumFT.v, with its module paths and module names changed; 304 of its 392 lines of code are new or changed and 343 lines of the source are left out. *)
(* fuzz_preset image B (asan-ubsan), parse_value 0x8637c, SEGMENT N (the number arm), sub-piece TX of
   PvB_NCut.v: the arm's
   common tail T (B 0x8688c) to the shared exit X (B 0x8664c), pnTX_stmt.
   rule 24: no function proved
   rule 24: proves no function (kind: segment lemma). Reuse search: `proof-index parse_value` (04:10Z, EXIT=0
   unpiped, index built 2026-10-29T04:26:29Z): "parse_value: 14 file(s) named for it, 35 file(s) use its address, 0
   related; in the delivery 58 named for it and 794 name(s) that hold it, in 68 tree(s)"; second-agent CONFIRM
   (04:21Z): no released srealizes-form proof of this program's parse_value; image A's
   S8aNumFT.v (ex_value, a different function) is read as a pattern only.
   WHAT THE CODE DOES (the neutral listing, the internal file parse_value.fuzz_preset.asan-ubsan.s:326-328):
     0x8688c li a0, -8;  0x86890 sb a0, 4(s11) (the fake frame's shadow byte 4 back to 0xf8);  0x86894 j 0x8664c.
   HOW IT IS PROVED: the three instructions are stepped by hand (RiscvSemantics.step through YK14 / YK0v's step lemmas,
   each word fetched from the B program listing by YC1fP's pa_fetch_pw), one msteps, closed by YA0n's SRr_msteps and
   the exit continuation. The one store is the own frame's shadow byte, inside the journal's write set, so YCbqG's
   ajournal_x_exec carries the journal. pv_frame's other bytes, the caller window, and every byte the post pv_Qm
   reads are kept, because each of them is (a) an application byte (the real stack at or above alloc_ceiling, an
   allocator block, a fake frame, the text or node in app memory) or (b) below the shadow band (the alloc.c statics
   prh_pst, image bytes): the class tx_cl, which never holds the shadow byte (tx_sh_ncl). The outcome pn_out becomes
   pv_Qm by PvB_NCut.v's pnQ_stmt (Section hypothesis QN), at the memory before the store; tx_Qm_move moves it across. Its
   allocator-state and model conjuncts (room_live_cf S', the room post rp_post, the outcome pv_outc, the ledger move,
   the bytes bound blocks_bytes S' <= blocks_bytes (pe_S en) + prh_held tr, Ledger.lsum D = PjGrammar.held tr) read
   no memory and are carried unchanged; the free-order tie pv_ftie and the node's capacity words pj_ncapR read the
   node and its blocks D only (PRH_PjOrder.pj_foR_frame, PvB_Frees.pvf_ncap_frame), as PvB_X.v moves them.
   pv_frame states no word at sp0 - 160 (PvB_Defs.v: the prologue's store there is a stack probe), so pv_at_exit's
   body is pn_at_T's with the shadow byte 4 back to 0xf8: no CUTFIX here. The exit cut's body is BUDGETED
   (PvB_Defs.v pv_body_x, the batch kit's tip 240b06ed4fd4); the number arm made no budgeted call (fuzz_malloc and strtod are
   unbudgeted), so it is pv_body at no wild trace (PvB_Defs.pv_body_x_of).
   pv_at_exit's room post lives in pv_Qm (PvB_Defs.v rp_post, the conjunct after room_live_cf S', keyed on the trace):
   PvB_NQ.v's pnQ gives it from T's outcome pn_out at Sc, and tx_Qm_move carries it across the store (it reads no memory).
   pv_at_exit's last conjunct, the exit memory's normal form, is T's aj_memnorm (YAkMemnorm.memnorm by conversion)
   across the one store, by YAkMemnorm's memnorm_mrestrict / memnorm_msteps / memnorm_munrestrict over the run's msteps.
   Numerals: 20928 20932 20936 (DERIVED: listing offsets, B pc - B_prog_base 0x816cc); 0xff800513 0xad8223 0xdb9ff06f
   (WORD: the three instruction words of the listing at those offsets); 10 0 27 4088 4 2096568 (WORD: the register
   numbers and immediates decoded from those words; 4088 = -8 and 2096568 = -584 in 12 / 21 bits); -8, 248 (WORD: the
   byte 0xf8 the tail writes); 4 8 24 56 64 160 176 512 (LENGTH: instruction bytes, shadow-byte index, the granule,
   the cursor / node / class-0 frame sizes, real-frame offsets, 4096 / 8); 1 (LENGTH: one byte); 2 ^ 47, 2 ^ 64
   (LENGTH: address-space bounds). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YK00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI16 YK06 YM05 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqG YC80x YC1fPx YG0p FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_FnParse PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CallerJ PRW_PjExt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PvB_Defs PvB_X_Tree PvB_NCut.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PvB_Frees.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Instance PIBtx : PrhImg := prh_img_B.

(* ======== machine helpers (no image) ======== *)

Lemma tx_v_addi_lit : forall v d, v_addi (Z_to_bv 64 v) d = Z_to_bv 64 (v + d).
Proof.
intros v d. unfold v_addi. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma tx_bv_eqb_ne : forall u v, 0 <= u < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> u <> v ->
  bv_eqb (Z_to_bv 64 u) (Z_to_bv 64 v) = false.
Proof. intros u v Hu Hv Hne. unfold bv_eqb. rewrite !u64_lit by lia. apply Z.eqb_neq. exact Hne. Qed.

Lemma tx_bv_eqb_refl : forall x : word, bv_eqb x x = true.
Proof. intros x. unfold bv_eqb. apply Z.eqb_refl. Qed.

Lemma tx_wbytes1 : forall (m : word -> option byte) (a : word) (b : byte) (x : word),
  wbytes m a [b] x = if bv_eqb x a then Some b else m x.
Proof. reflexivity. Qed.

Lemma tx_keep_wr : forall (Hh : word -> bool) (mem m' : word -> option byte) x,
  m' x = mrestrict Hh mem x -> mrestrict Hh (munrestrict Hh mem m') x = mrestrict Hh mem x.
Proof. intros Hh mem m' x E. rewrite mrestrict_munrestrict. unfold mrestrict in *. destruct (Hh x); [reflexivity | exact E]. Qed.

Lemma tx_grows_wr : forall (Hh : word -> bool) (mem m' : word -> option byte),
  mem_grows (mrestrict Hh mem) m' -> mem_grows (mrestrict Hh mem) (mrestrict Hh (munrestrict Hh mem m')).
Proof.
intros Hh mem m' G x Hx. pose proof (G x Hx) as Gx. rewrite mrestrict_munrestrict.
unfold mrestrict in *. destruct (Hh x); [exact Hx | exact Gx].
Qed.

(* one instruction of the listing: offset off holds the plain word w, which decodes to i *)
Definition tx_ins (off w : Z) (i : instr) : Prop :=
  plookup B_prog_tpi off = Some (PW w) /\ is_ecall (Z_to_bv 32 w) = false /\
  decode_any (Z_to_bv 32 w) = Some (i, 4%Z).
Ltac tx_ins_tac := refine (conj _ (conj _ _)); [vm_compute; reflexivity | vm_compute; reflexivity | vm_refl_bv].

Lemma I_39c : tx_ins 20928 0xff800513 (OpImm ALU_ADD 10 0 4088). Proof. tx_ins_tac. Qed.
Lemma I_3a0 : tx_ins 20932 0xad8223 (Store SZ1 27 10 4). Proof. tx_ins_tac. Qed.
Lemma I_3a4 : tx_ins 20936 0xdb9ff06f (Jal 0 2096568). Proof. tx_ins_tac. Qed.

(* ======== the address classes (no image but the ASan layout constants) ======== *)
Section cl. Context {rc : YM05.RunCeil}.

(* the bytes the tail keeps: below the shadow band, or at or above the high application memory *)
Definition tx_cl (x : Z) : Prop := (0 <= x < SHADOW_OFF) \/ (kHighMemBeg <= x < 2 ^ 64).

Lemma tx_cl_app : forall x, app_addr x -> tx_cl x.
Proof.
intros x (H0 & [H1 | (H2 & H3)]); pose proof asan_consts as (C1 & _); unfold tx_cl;
  unfold ASAN_CEIL, kLowShadowBeg, SHADOW_OFF, kHighMemBeg in *; lia.
Qed.

Lemma tx_cl_amem : forall p n x, 0 <= p -> amem_range p n -> p <= x < p + n -> tx_cl x.
Proof.
intros p n x Hp [H | (H1 & H2)] Hx; unfold tx_cl; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *; lia.
Qed.

(* the eight bytes from the base of an allocator block in app memory (its head word) *)
Lemma tx_cl_blk8 : forall b rs x, in_app b rs -> 1 <= rs -> b <= x < b + 8 -> tx_cl x.
Proof.
intros b rs x (H0 & [H1 | (H2 & H3)]) Hrs Hx; pose proof asan_consts as (C1 & _); unfold tx_cl;
  unfold ASAN_CEIL, kLowShadowBeg, SHADOW_OFF, kHighMemBeg in *; lia.
Qed.

(* the shadow byte the tail writes is in neither class *)
Lemma tx_sh_ncl : forall fa, in_app fa 64 -> ~ tx_cl (SHADOW_OFF + fa / 8 + 4).
Proof.
intros fa (H0 & [H1 | (H2 & H3)]) Hc; pose proof asan_consts as (C1 & _); unfold tx_cl in Hc;
  unfold ASAN_CEIL, kLowShadowBeg, SHADOW_OFF, kHighMemBeg in *; lia.
Qed.

Lemma tx_sh_bounds : forall fa, in_app fa 64 -> SHADOW_OFF + 512 <= SHADOW_OFF + fa / 8 /\
  SHADOW_OFF + fa / 8 + 8 <= kHighMemBeg.
Proof.
intros fa (H0 & [H1 | (H2 & H3)]); pose proof asan_consts as (C1 & _);
  unfold ASAN_CEIL, kLowShadowBeg, SHADOW_OFF, kHighMemBeg in *; lia.
Qed.
End cl.

(* the alloc.c statics of image B lie below the shadow band (computed from prh_img_B) *)
Lemma tx_pst_lo : forall a n, In (a, n) (@prh_pst PIBtx) -> 0 <= a /\ a + n <= SHADOW_OFF.
Proof.
intros a n H. vm_compute in H.
repeat (destruct H as [H | H]; [injection H; intros; subst; unfold SHADOW_OFF; lia |]). destruct H.
Qed.

Section c. Context {fx0 : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- Section hypotheses: the allocator laws (at any harness-block head length hl), and PvB_NCut.v's pnQ_stmt (PvB_NQ.v's
   pnQ proves it) ---- *)
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis QN : pnQ_stmt B ARx.

(* ---- steps over the B listing ---- *)
Lemma tx_fetch : forall off w, plookup B_prog_tpi off = Some (PW w) ->
  fetch_word SEGS (Z_to_bv 64 (BASE + off)) = Some (Z_to_bv 32 w).
Proof. intros off w H. exact (pa_fetch_pw (PL := PL_prog_B) (PI := PA) off w H). Qed.

Lemma tx_pc_add : forall k d, v_addi (Z_to_bv 64 (BASE + k)) d = Z_to_bv 64 (BASE + (k + d)).
Proof. intros k d. rewrite tx_v_addi_lit, Z.add_assoc. reflexivity. Qed.

Lemma tx_step_addi : forall (f : YK11.FPState) regs mem off off' w rd rs (imm : bv 12) v,
  off' = off + 4 -> tx_ins off w (OpImm ALU_ADD rd rs imm) -> bv_eqb rd 0 = false ->
  v_addi (getr regs rs) (bv_signed imm) = v ->
  RiscvSemantics.step SEGS (@YK11.mkst f regs (Z_to_bv 64 (BASE + off)) mem (YK11.seg_rom SEGS)) =
  MachineOk (@YK11.mkst f (regupd regs rd v) (Z_to_bv 64 (BASE + off')) mem (YK11.seg_rom SEGS)).
Proof.
intros f regs mem off off' w rd rs imm v -> (HL & HE & HD) Hrd Hv.
rewrite (step_addi_at (fx := f) SEGS regs _ mem (YK11.seg_rom SEGS) (Z_to_bv 32 w) rd rs imm v
  (tx_fetch off w HL) HE HD Hrd Hv).
rewrite tx_pc_add. reflexivity.
Qed.

Lemma tx_step_sb : forall (f : YK11.FPState) regs mem off off' w rs1 rs2 (imm : bv 12) (a v : word) (b : byte),
  off' = off + 4 -> tx_ins off w (Store SZ1 rs1 rs2 imm) ->
  v_addi (getr regs rs1) (bv_signed imm) = a -> getr regs rs2 = v -> Z_to_bv 8 (bv_unsigned v) = b ->
  RiscvSemantics.store_ok SEGS mem a 1%nat = true ->
  RiscvSemantics.step SEGS (@YK11.mkst f regs (Z_to_bv 64 (BASE + off)) mem (YK11.seg_rom SEGS)) =
  MachineOk (@YK11.mkst f regs (Z_to_bv 64 (BASE + off')) (wbytes mem a [b]) (YK11.seg_rom SEGS)).
Proof.
intros f regs mem off off' w rs1 rs2 imm a v b -> (HL & HE & HD) Ha Hv Hb Hok.
rewrite (YK0v.step_sb_at (fx := f) SEGS regs _ mem (YK11.seg_rom SEGS) (Z_to_bv 32 w) rs1 rs2 imm a v b
  (tx_fetch off w HL) HE HD Ha Hv Hb Hok).
rewrite tx_pc_add. reflexivity.
Qed.

Lemma tx_step_j : forall (f : YK11.FPState) regs mem off off' w (imm : bv 21),
  off' = off + bv_signed imm -> tx_ins off w (Jal 0 imm) ->
  RiscvSemantics.step SEGS (@YK11.mkst f regs (Z_to_bv 64 (BASE + off)) mem (YK11.seg_rom SEGS)) =
  MachineOk (@YK11.mkst f regs (Z_to_bv 64 (BASE + off')) mem (YK11.seg_rom SEGS)).
Proof.
intros f regs mem off off' w imm -> (HL & HE & HD).
rewrite (step_jal_link (fx := f) SEGS regs _ mem (YK11.seg_rom SEGS) (Z_to_bv 32 w) 0 imm (tx_fetch off w HL) HE HD).
unfold btgt. rewrite (tx_pc_add off (bv_signed imm)). reflexivity.
Qed.

(* a store of n bytes at a is allowed when every byte is present and visible *)
Lemma tx_store_ok : forall (Hh : word -> bool) (mem m : word -> option byte) a (n : nat),
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

(* ---- the post's memory part across a store outside tx_cl ---- *)

(* the ledger: its statics (below the shadow band; the kit's seven, g_most and g_own_ran_out included) and its heads (the
   first eight bytes of app blocks) *)
Lemma tx_ledger_move : forall ly S Hp W mem md mem' Lam peak cnt fail ran most own,
  ARx ly S Hp W mem md ->
  (forall x, tx_cl x -> mbyte SEGS (rdW W mem') x = mbyte SEGS (rdW W mem) x) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> prh_ledger B ly S Hp W mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem md mem' Lam peak cnt fail ran most own HAR Hmb (HG & HND & HF & HP).
assert (VK : forall a n v, (forall x, a <= x < a + Z.of_nat n -> tx_cl x) ->
  val_mem SEGS (rdW W mem) a n v -> val_mem SEGS (rdW W mem') a n v).
{ intros a n v Hc Hv. apply (pjx_val SEGS _ _ a n v Hv). intros x Hx. apply Hmb. exact (Hc x Hx). }
assert (Hst : forall a n, In (a, Z.of_nat n) (@prh_pst PIBtx) -> forall x, a <= x < a + Z.of_nat n -> tx_cl x).
{ intros a n Hin x Hx. pose proof (tx_pst_lo a (Z.of_nat n) Hin) as (H0 & H1). left. lia. }
split; [|split; [exact HND | split; [|exact HP]]].
- destruct HG as (V1 & V2 & V3 & V4 & V5 & (V6 & R6) & (V7 & R7) & HR).
  split; [apply (VK _ _ _ (Hst _ _ ltac:(left; reflexivity)) V1)|].
  split; [apply (VK _ _ _ (Hst _ _ ltac:(right; left; reflexivity)) V2)|].
  split; [apply (VK _ _ _ (Hst _ _ ltac:(right; right; left; reflexivity)) V3)|].
  split; [apply (VK _ _ _ (Hst _ _ ltac:(right; right; right; left; reflexivity)) V4)|].
  split; [apply (VK _ _ _ (Hst _ _ ltac:(right; right; right; right; left; reflexivity)) V5)|].
  split; [split; [apply (VK _ _ _ (Hst _ _ ltac:(do 5 right; left; reflexivity)) V6) | exact R6]|].
  split; [split; [apply (VK _ _ _ (Hst _ _ ltac:(do 6 right; left; reflexivity)) V7) | exact R7]|].
  exact HR.
- rewrite Forall_forall in HF |- *. intros [a kk] Hin.
  destruct (HF _ Hin) as (Hk0 & Hab & Hhp & Ha16 & Hv). cbn [fst snd] in *.
  refine (conj Hk0 (conj Hab (conj Hhp (conj Ha16 _)))).
  apply (VK _ _ _); [|exact Hv].
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & _ & _ & Happ & _).
  pose proof cf_head_nonneg as Hch.
  assert (Hn : 0 <= kk + cf_head) by lia.
  pose proof (req_size_pos _ Hn) as (Hrs & _).
  intros x Hx. apply (tx_cl_blk8 _ _ x Happ Hrs). lia.
Qed.

(* THE MOVE of pv_Qm: every byte it reads is in tx_cl (the cursor q in the caller's stack, the text and the node in
   app memory by rd_pre, the subtree's blocks D and the ledger's heads in allocator blocks, the statics); its room, bytes
   and ledger-sum conjuncts read no memory *)
Lemma tx_Qm_move : forall en fr code ly S Hp W mem md mem',
  pv_pre B ARx en -> ARx ly S Hp W mem md ->
  (forall x, tx_cl x -> mbyte SEGS (rdW W mem') x = mbyte SEGS (rdW W mem) x) ->
  mem_grows (rdW W mem) (rdW W mem') ->
  pv_Qm B en fr code ly S Hp W mem -> pv_Qm B en fr code ly S Hp W mem'.
Proof.
intros en fr code ly S Hp W mem md mem' HPRE HAR Hmb Hg HQ.
pose proof HPRE as (HFPRE & _ & _ & _ & _ & _ & _ & _ & HRDP & _).
destruct HFPRE as ((_ & _ & _ & _ & _ & Hstk0 & _) & _).
pose proof HRDP as (_ & _ & _ & _ & _ & Hwin & Hqlo & Hqhi & _ & Hsrc & _ & _ & Hnode & _).
destruct Hstk0 as (_ & HS0 & Hceil & Hlo & _ & H47 & _ & _ & Htop).
destruct Hwin as (He0 & _ & Hetop & _).
destruct Hsrc as (_ & Ht4096 & _ & Htam & _).
destruct Hnode as (Hv4096 & _ & _ & _ & _ & Hvam & _).
pose proof asan_consts as (C1 & _).
assert (Hq : forall x, pe_q en <= x < pe_q en + 24 -> tx_cl x).
{ intros x Hx. right. unfold kHighMemBeg. lia. }
assert (Ht : forall x, pe_text en <= x < pe_text en + Z.of_nat (length (pe_tb en)) -> tx_cl x)
  by (intros x Hx; refine (tx_cl_amem _ _ x _ Htam Hx); lia).
assert (Hv : forall x, pe_v en <= x < pe_v en + 56 -> tx_cl x)
  by (intros x Hx; refine (tx_cl_amem _ _ x _ Hvam Hx); lia).
assert (HW : forall x, writable_at SEGS (rdW W mem) x -> writable_at SEGS (rdW W mem') x)
  by (intros x Hx; eapply writable_at_grows; [exact Hg | exact Hx]).
apply pvQ_R_of in HQ. destruct HQ as (ok & res & tr & okr & D & Lam' & peak' & cnt' & fail' & ran' & HR).
assert (HB : forall x, pjx_foot (pe_v en) D x -> mbyte SEGS (rdW W mem') x = mbyte SEGS (rdW W mem) x).
{ intros x [Hx | ([a kk] & Hb & Hx)]; apply Hmb; [exact (Hv x Hx)|].
  unfold pj_holdsR in Hx; cbn [fst snd] in Hx.
  assert (Hin : In (a - cf_head, kk + cf_head) (ablocks B ly S)).
  { apply (Permutation_in _ (Permutation_sym (pvq_perm HR))). apply in_or_app. left. unfold prhReader_ab.
    exact (in_map (fun ak => (fst ak - cf_head, snd ak + cf_head)) D (a, kk) Hb). }
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hin) as (_ & _ & _ & Happ & _).
  pose proof cf_head_nonneg as Hch.
  assert (Hn : 0 <= kk + cf_head) by lia.
  pose proof (req_size_pos _ Hn) as (_ & Hrs).
  apply tx_cl_app. apply (in_app_addr _ _ x Happ). lia. }
(* the free order across the store: the same order F of the same blocks D, the footprint's bytes kept *)
assert (FT : forall nlo, pv_ftie en nlo Lam' W mem D ok -> pv_ftie en nlo Lam' W mem' D ok).
{ intros nlo Hft Hhd n Hn. destruct (Hft Hhd n Hn) as (F & HF & HFm). exists F. split; [|exact HFm].
  apply (PRH_PjOrder.pj_foR_frame SEGS n _ _ _ _ _ _ _ HF);
    [exact (PRH_PjOrder.pj_foR_lblk SEGS _ _ _ _ _ _ HF)
    |apply (pjx_agree_of_bytes SEGS); [exact HB | exact HW]]. }
eapply pvQ_of_R.
refine {| pvq_run := pvq_run HR;
  pvq_ledger := tx_ledger_move ly S Hp W mem md mem' Lam' peak' cnt' fail' ran' (pe_most en) (pe_own en) HAR Hmb
    (pvq_ledger HR);
  pvq_room := pvq_room HR; pvq_hull := pvq_hull HR; pvq_rp := pvq_rp HR; pvq_outc := pvq_outc HR;
  pvq_inj := pvq_inj HR; pvq_move := pvq_move HR; pvq_fresh := pvq_fresh HR; pvq_perm := pvq_perm HR;
  pvq_fr := pvq_fr HR; pvq_peak := pvq_peak HR; pvq_bytes := pvq_bytes HR; pvq_lsum := pvq_lsum HR;
  pvq_arm := _ |}.
pose proof (pvq_arm HR) as Hres.
destruct res as [[t r]|].
- destruct Hres as (Hc0 & Hft & Hin & Hnd & Hnc & Hls0).
  split; [exact Hc0|]. split; [exact (FT _ Hft)|].
  split; [|split; [|split; [|exact Hls0]]].
  + apply (pjx_in_ok_frame SEGS _ _ _ _ _ _ _ _ Hin).
    * intros x Hx. apply Hmb. exact (Hq x Hx).
    * intros x _ Hx. exact (HW x Hx).
    * intros x Hx. apply Hmb. exact (Ht x Hx).
  + apply (pj_nodeR_frame SEGS _ _ _ _ _ _ Hnd). apply (pjx_agree_of_bytes SEGS); [exact HB | exact HW].
  + apply (PvB_Frees.pvf_ncap_frame SEGS t (w_H W) mem (rdW W mem') _ (pe_v en) D Hnd); [|exact Hnc].
    apply (pjx_agree_of_bytes SEGS); [exact HB | exact HW].
- destruct Hres as (Hc1 & Hft & Haf & Hfd).
  split; [exact Hc1|]. split; [exact (FT _ Hft)|]. split.
  + apply (pjx_in_after_frame SEGS _ _ _ _ _ _ _ Haf).
    * intros x Hx. apply Hmb. exact (Hq x Hx).
    * intros x _ Hx. exact (HW x Hx).
  + apply (pjx_fd_frame SEGS _ _ _ _ _ _ Hfd). apply (pjx_agree_of_bytes SEGS); [exact HB | exact HW].
Qed.

(* ======== TX: T 0x8688c -> X 0x8664c ======== *)
Lemma pvn_TX : pnTX_stmt (SK := SK) B ARx.
Proof.
intros en HPRE KX W' ms mdc HT.
(* T's last conjunct (aj_memnorm at T's memory) gives pv_at_exit's last; the run position is inside pn_out / pv_Qm *)
destruct HT as (fx' & regs & mem & Y & fa & fl & pos & lyc & Sc & Hpc & k & code &
  Ems & HFZ & HFK & HKR & Hcode & HBODY & HOUT & HMN).
pose proof (QN en pos code lyc Sc Hpc W' mem HPRE HOUT) as HQM.
pose proof HBODY as (HFRM & HinF & Efa & Efl & HJ & HWIN).
pose proof HJ as (HAR & _).
pose proof HKR as (R2 & R8 & R18 & R26 & R27 & R23 & R3 & R4).
pose proof HFRM as (HY1 & HY32 & HPR0 & Vsav & Vfa48 & Vmagic & Vdesc & Vpc & Vfl & HPRfa & Hshlen & Gsh).
pose proof HPRE as (HFPRE & _ & _ & _ & _ & _ & _ & _ & HRDP & _).
destruct HFPRE as ((_ & _ & _ & _ & _ & Hstk0 & _) & _).
pose proof HRDP as (_ & _ & _ & _ & _ & Hwin & _).
destruct Hstk0 as (_ & HS0 & Hceil & Hlo & _ & H47 & _ & _ & Htop).
destruct Hwin as (He0 & _ & Hetop & _).
pose proof asan_consts as (C1 & _).
unfold YG0d.w64 in *.
(* the entry sp: at or above alloc_ceiling, its window below 2 ^ 47 *)
assert (Hsp : kHighMemBeg + 176 <= pe_sp en /\ pe_sp en + pe_e en <= 2 ^ 47)
  by (unfold pe_sp, kHighMemBeg; lia).
(* the fake frame and its shadow *)
assert (Efb : fs_frame_bytes 0 = 64) by reflexivity.
destruct (frames_bounds_x SEGS B ARx LAWS lyc Sc Hpc W' mem mdc 0 pos HAR HinF) as (Hfa0 & _ & Hfapp).
rewrite <- Efa in Hfa0. rewrite <- Efa, Efb in Hfapp.
destruct (alx_frames SEGS B ARx LAWS lyc Sc Hpc W' mem mdc 0 pos HAR HinF) as (_ & _ & _ & Hfsh).
rewrite Efb in Hfsh. change (64 / 8) with 8 in Hfsh.
set (sh := SHADOW_OFF + fa / 8) in *.
assert (Esh : shadow_addr (frame_addr lyc 0 pos) = sh) by (rewrite <- Efa; reflexivity).
rewrite Esh in Hfsh.
pose proof (tx_sh_bounds fa Hfapp) as (Hsh_lo & Hsh_hi). fold sh in Hsh_lo, Hsh_hi.
pose proof (tx_sh_ncl fa Hfapp) as Hsh_ncl. fold sh in Hsh_ncl.
assert (P4 : apresent (w_H W') mem (sh + 4)) by exact (proj1 (Hfsh 4 ltac:(lia))).
pose proof asan_consts as (_ & _ & C3 & _).
assert (CS : 0 <= SHADOW_OFF) by (unfold SHADOW_OFF; lia).
assert (Hsh64 : 0 <= sh /\ sh + 8 <= 2 ^ 64) by lia.
(* ---- the run: li a0, -8; sb a0, 4(s11); j 0x8664c ---- *)
set (b8 := Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-8)))).
set (m0 := mrestrict (w_H W') mem).
set (m1 := wbytes m0 (Z_to_bv 64 (sh + 4)) [b8]).
set (regs1 := regupd regs 10 (Z_to_bv 64 (-8))).
assert (G1 : forall r0 : bv 5, r0 <> 10%bv -> getr regs1 r0 = getr regs r0)
  by (intros r0 N; unfold regs1; rewrite getr_other by exact N; reflexivity).
assert (Hms : msteps SEGS (@YK11.mkst fx' regs (Z_to_bv 64 (BASE + 20928)) m0 (YK11.seg_rom SEGS))
                          (@YK11.mkst fx' regs1 (Z_to_bv 64 (BASE + 20352)) m1 (YK11.seg_rom SEGS))).
{ eapply mst_step; [reflexivity | |].
  { refine (tx_step_addi fx' regs m0 20928 20932 0xff800513 10 0 4088 (Z_to_bv 64 (-8)) eq_refl I_39c eq_refl _).
    rewrite getr_zero, tx_v_addi_lit. reflexivity. }
  eapply mst_step; [reflexivity | |].
  { refine (tx_step_sb fx' regs1 m0 20932 20936 0xad8223 27 10 4 (Z_to_bv 64 (sh + 4)) (Z_to_bv 64 (-8)) b8
      eq_refl I_3a0 _ _ eq_refl _).
    - rewrite G1 by reg_neq_tac. rewrite R27, tx_v_addi_lit. reflexivity.
    - unfold regs1. rewrite getr_same by reg_neq_tac. reflexivity.
    - apply (tx_store_ok (w_H W') mem m0 (sh + 4) 1); [lia | lia | | apply mem_grows_refl].
      intros i Hi. replace (sh + 4 + i) with (sh + 4) by lia. exact P4. }
  eapply mst_step; [reflexivity | |].
  { exact (tx_step_j fx' regs1 m1 20936 20352 0xdb9ff06f 2096568 eq_refl I_3a4). }
  apply mst_refl. }
rewrite Ems.
apply (SRr_msteps SEGS (@pa_wx _ B_prog_listing PA) W'
  (@YK11.mkst fx' regs (Z_to_bv 64 (BASE + AF_pn_tail)) mem (YK11.seg_rom SEGS))
  (@YK11.mkst fx' regs1 (Z_to_bv 64 (BASE + 20352)) m1 (YK11.seg_rom SEGS)) mdc _ Hms).
intros md' Hsame _.
apply KX.
set (mem' := munrestrict (w_H W') mem m1).
(* ---- the memory after the store: kept off the shadow byte ---- *)
assert (Hkeep : forall z, 0 <= z < 2 ^ 64 -> z <> sh + 4 ->
  mrestrict (w_H W') mem' (Z_to_bv 64 z) = mrestrict (w_H W') mem (Z_to_bv 64 z)).
{ intros z Hz N4. apply tx_keep_wr. unfold m1. rewrite tx_wbytes1, (tx_bv_eqb_ne z (sh + 4)) by lia.
  reflexivity. }
assert (Hmb0 : forall x, 0 <= x < 2 ^ 64 -> x <> sh + 4 -> mbyte SEGS (rdW W' mem') x = mbyte SEGS (rdW W' mem) x)
  by (intros x Hx N; unfold mbyte; rewrite (Hkeep x Hx N); reflexivity).
assert (Hmr : forall x, tx_cl x -> mrestrict (w_H W') mem' (Z_to_bv 64 x) = mrestrict (w_H W') mem (Z_to_bv 64 x)).
{ intros x Hx. apply Hkeep; [unfold tx_cl in Hx; lia | intros E; apply Hsh_ncl; rewrite <- E; exact Hx]. }
assert (Hmb : forall x, tx_cl x -> mbyte SEGS (rdW W' mem') x = mbyte SEGS (rdW W' mem) x)
  by (intros x Hx; unfold mbyte; rewrite (Hmr x Hx); reflexivity).
assert (Hgrow : mem_grows (rdW W' mem) (rdW W' mem')) by (apply tx_grows_wr; apply wbytes_grows).
assert (Hnew : mbyte SEGS (rdW W' mem') (sh + 4) = Some b8).
{ unfold mem'. rewrite mrestrict_munrestrict. unfold mbyte, mrestrict.
  rewrite (proj1 P4). unfold m1. rewrite tx_wbytes1, tx_bv_eqb_refl. reflexivity. }
assert (VK : forall a n v, (forall x, a <= x < a + Z.of_nat n -> tx_cl x) ->
  val_mem SEGS (rdW W' mem) a n v -> val_mem SEGS (rdW W' mem') a n v).
{ intros a n v Hc Hv. apply (pjx_val SEGS _ _ a n v Hv). intros x Hx. apply Hmb. exact (Hc x Hx). }
assert (Hhi : forall x, pe_sp en - 176 <= x < pe_sp en + pe_e en -> tx_cl x) by (intros x Hx; right; lia).
assert (Hfa_cl : forall x, fa <= x < fa + 64 -> tx_cl x)
  by (intros x Hx; exact (tx_cl_app x (in_app_addr fa 64 x Hfapp Hx))).
(* ---- the exit cut ---- *)
unfold pv_at_exit.
exists fx', regs1, mem', Y, fa, fl, pos, lyc, Sc, Hpc, k, code.
split; [reflexivity|]. split; [exact HFZ|]. split; [exact HFK|].
split.
{ unfold pv_keep_regs. rewrite !G1 by reg_neq_tac. exact HKR. }
split; [rewrite G1 by reg_neq_tac; exact Hcode|].
split.
{ apply pv_body_x_of. split.
  { (* pv_frame with the shadow bytes back to pv_shadow_live *)
    split; [exact HY1|]. split; [exact HY32|].
    split; [intros a Ha; eapply apresent_grows; [exact Hgrow | exact (HPR0 a Ha)]|].
    split.
    { rewrite Forall_forall in Vsav |- *. intros oc Hoc.
      assert (Hb : -104 <= fst oc <= -8)
        by (unfold pv_saved in Hoc; repeat (destruct Hoc as [<- | Hoc]; [cbn; lia |]); destruct Hoc).
      apply (VK _ _ _); [|exact (Vsav oc Hoc)]. intros x Hx. apply Hhi. cbn in Hx. lia. }
    split; [apply VK; [intros x Hx; apply Hhi; cbn in Hx; lia | exact Vfa48]|].
    split; [apply VK; [intros x Hx; apply Hfa_cl; cbn in Hx; lia | exact Vmagic]|].
    split; [apply VK; [intros x Hx; apply Hfa_cl; cbn in Hx; lia | exact Vdesc]|].
    split; [apply VK; [intros x Hx; apply Hfa_cl; cbn in Hx; lia | exact Vpc]|].
    split; [apply VK; [intros x Hx; apply Hfa_cl; cbn in Hx; lia | exact Vfl]|].
    split; [intros a Ha; eapply apresent_grows; [exact Hgrow | exact (HPRfa a Ha)]|].
    split; [reflexivity|].
    intros j Hj. fold sh. change (length pv_shadow_live) with 8%nat in Hj.
    destruct (Nat.eq_dec j 4) as [-> | Hne].
    - split; [|cbn; lia]. intros kk Hk. assert (kk = 0%nat) as -> by lia.
      replace (sh + Z.of_nat 4 + Z.of_nat 0) with (sh + 4) by lia. rewrite Hnew. unfold b8.
      f_equal. apply bv_eq. vm_compute. reflexivity.
    - assert (Ej : nth j pv_shadow_live 0 = nth j pv_shadow_open 0).
      { destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; try lia; reflexivity. }
      rewrite Ej. destruct (Gsh j ltac:(cbn; lia)) as (Gv & Gr). split; [|exact Gr].
      apply (pjx_val SEGS _ _ _ 1 _ Gv). intros x Hx. apply Hmb0; [lia | lia]. }
  split; [exact HinF|]. split; [exact Efa|]. split; [exact Efl|].
  split.
  { (* the journal: the one store is the own frame's shadow byte *)
    apply (ajournal_x_exec (SK := SK) SEGS B prh_pst ARx LAWS pa_segs_low
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun z => z = sh + 4) HJ).
    - intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). pose proof (u64_range x) as Hxr.
      apply Hkeep; [lia | exact Hx].
    - exact Hgrow.
    - intros x Hx. unfold mem', munrestrict. rewrite Hx. reflexivity.
    - exact Hsame.
    - intros z ->. right; right; right. exists 0, pos. split; [left; reflexivity|]. right.
      unfold in_zr. cbn [fst snd]. rewrite Esh, Efb. change (64 / 8) with 8. lia. }
  (* the caller window: above the shadow band *)
  intros a Ha Hnf. rewrite <- (HWIN a Ha Hnf). apply (aview_eq_of SEGS (w_H W')).
  apply Hmr. apply Hhi. lia. }
(* the post: pnQ_stmt (QN) at the memory before the store, moved across it *)
split; [exact (tx_Qm_move en _ code lyc Sc Hpc W' mem mdc mem' HPRE HAR Hmb Hgrow HQM)|].
(* the exit memory's normal form: T's (aj_memnorm, YAkMemnorm.memnorm by conversion) across the one store, by the
   hidden / visible split: the restricted run keeps it (YAkMemnorm.memnorm_mrestrict, memnorm_msteps) and the merge
   with the hidden bytes of mem keeps it (memnorm_munrestrict) *)
exact (YAkMemnorm.memnorm_munrestrict SEGS (w_H W') mem m1 HMN
  (YAkMemnorm.memnorm_msteps SEGS _ _ Hms (YAkMemnorm.memnorm_mrestrict SEGS (w_H W') mem HMN))).
Qed.

End c.
