(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1dg X1df X1ck X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05q X05l X05j X05k X05b X082 X09f X069 X09e
X06n X06m X091 X08x X090 X08l.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X12b X0z5 X0wg X0wh X0w8 X0yt X0x2 X0xf X0zp X0zs X0zc.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0z5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wg OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wh OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w8 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xf OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zp OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zs OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zc.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac slia ::= (try unfold BITS_SIZEOF in * ); first [ exact I | lia | split; [lia|exact I] ].
Local Notation mem := (word -> option byte).

Section TailPure.
Context {ptr : Type}.
Definition search_tail (fuel : nat) (sc : bool) (bm : bits_st ptr) : search_out :=
if speex_bits_remaining bm <? 4 then SOret (-1) bm else
let m := uv bm 4 in let b6 := ub bm 4 in
if m =? 15 then SOret (-1) b6
else if m =? 14 then search_pure fuel sc (inband_bits sc b6)
else if m =? 13 then search_pure fuel sc (user_handler_bits b6)
else if 8 <? m then SOnotify false b6
else SOmode m b6.

Definition search_head (b : bits_st ptr) : bits_st ptr + search_out :=
let w1 := uv b 1 in let b1 := ub b 1 in
if negb (w1 =? 0) then
let b2 := skip_bits b1 in
if speex_bits_remaining b2 <? 5 then inr (SOret (-1) b2) else
let w2 := uv b2 1 in let b3 := ub b2 1 in
if negb (w2 =? 0) then
let b4 := skip_bits b3 in
let w3 := uv b4 1 in let b5 := ub b4 1 in
if negb (w3 =? 0) then inr (SOnotify true b5) else inl b5
else inl b3
else inl b1.
Lemma search_pure_S : forall fuel sc (b : bits_st ptr),
search_pure (S fuel) sc b =
if speex_bits_remaining b <? 5 then SOret (-1) b else
match search_head b with inr o => o | inl bm => search_tail fuel sc bm end.
Proof. reflexivity. Qed.
Lemma search_pure_lt5 : forall fuel sc (b : bits_st ptr), speex_bits_remaining b < 5 ->
search_pure fuel sc b = SOunr \/ search_pure fuel sc b = SOret (-1) b.
Proof.
intros [|fuel] sc b H; [left; reflexivity | right].
rewrite search_pure_S. replace (speex_bits_remaining b <? 5) with true by (symmetry; apply Z.ltb_lt; exact H). reflexivity.
Qed.
End TailPure.
Definition PC_wrap_fprintf : Z := 0x56d08.
Definition RA_nbd_fprintf : Z := 0xa466c.
Definition NBD_GOT_STDERR : Z := 0xfcd78.
Definition NBD_STDERR_VAR : Z := 0xfc010.
Definition NBD_FMT_NOTIFY : Z := 0x23ee0.
Definition NBD_MSG_INVALID : Z := 0x23ce0.
Definition NBD_MSG_TWOWB : Z := 0x23d40.
Definition PC_NBD_B : Z := 0xa1cdc.

Lemma cbs_cells_wf : forall k sf sd bb js, Forall (fun p => length (fst p) = 8%nat /\ length (snd p) = 16%nat) js ->
cells_wf (cbs_cells k sf sd bb js).
Proof.
induction k as [|k IH]; intros sf sd bb js F; [exact I|].
destruct js as [|j0 js]; [exact I|]. cbn [cbs_cells]. cbv zeta. inversion F; subst.
apply cells_wf_app. split; [| apply IH; assumption].
destruct H1 as [L1 L2]. destruct (_ && _); cbn; repeat split; assumption.
Qed.

Section Loop.
Context {ptr : Type}.
Variables (usp lo ST A D OUT STEREO f sf BSZ errf : Z).
Variables gp tp : word.
Variable sc : bool.
Variable js : list (list byte * list byte).
Variable cbs : list byte.
Variable ju : list byte * list byte.
Variables (ja jb jc jd je jf jg jh1 jh2 : list byte) (sv : list cell).
Variable m : mem.
Hypothesis LO : lo <= usp - 576 - 96.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis ALO : A + BITS_SIZEOF <= lo.
Hypothesis ATOP : IMG_TOP_B <= A.
Hypothesis ASH : hidp (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A).
Hypothesis DLO : D + BSZ <= lo.
Hypothesis ST8 : ST mod 8 = 0.
Hypothesis SB : 0 < ST /\ ST + 2968 <= 140737488355328.
Hypothesis STLO : ST + 2968 <= lo.
Hypothesis SE4 : STEREO mod 4 = 0.
Hypothesis SELO : STEREO + 8 <= lo.
Hypothesis SETOP : IMG_TOP_B <= STEREO.
Hypothesis SESH : hidp (STEREO + 8 <= SH_LO \/ SH_HI <= STEREO).
Hypothesis AP_ST_A : hidp (ST + 2968 <= A \/ A + BITS_SIZEOF <= ST).
Hypothesis AP_ST_SE : hidp (ST + 2968 <= STEREO \/ STEREO + 8 <= ST).
Hypothesis AP_SE_A : hidp (STEREO + 8 <= A \/ A + BITS_SIZEOF <= STEREO).
Hypothesis AP_SE_D : hidp (STEREO + 8 <= D \/ D + BSZ <= STEREO).
Hypothesis LJS : length js = 16%nat.
Hypothesis FJS : Forall (fun p => length (fst p) = 8%nat /\ length (snd p) = 16%nat) js.
Hypothesis ECBS : cbs = cells_bytes (cbs_cells 16 A_speex_std_stereo_request_handler STEREO sc js).
Hypothesis OBA : aobj bsegs m A BITS_SIZEOF.
Hypothesis OBD : aobj bsegs m D BSZ.
Hypothesis OBST : aobj bsegs m ST 2968.
Hypothesis OBSE : aobj bsegs m STEREO 8.
Hypothesis OBT : aobj bsegs m A_wb_skip_table 32.
Hypothesis OBE : aobj bsegs m A_e_ratio_quant 16.
Hypothesis OBV : aobj bsegs m NBD_STDERR_VAR 8.

Hypothesis UHB : forall ptr, @user_handler_stmtA ptr.
Hypothesis IHB : forall ptr, @inband_handler_stmtA ptr.

Definition nbA_W : list (Z * Z) := [(A, A + 48); (STEREO, STEREO + 8); (usp + -672, usp + -576)].
Definition nbA_ctx (m1 : mem) (b : bits_st ptr) (sws : list word) : Prop :=
munch nbA_W m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -576) /\ client_constsB m1
/\ bits_rep bsegs m1 A D b /\ bits_ok b /\ sb_buf_size b = BSZ
/\ rw_cells bsegs m1 STEREO (f32 sws) /\ length sws = 2%nat
/\ rw_cells bsegs m1 (usp + -576) (nbd_frame_A ST A OUT f sf ja jb jc jd je jf jg jh1 jh2 sv)
/\ rw_cells bsegs m1 (ST + 2256) [CB 640 cbs]
/\ rw_cells bsegs m1 (ST + 2896) (cb_cells A_speex_default_user_handler 0 ju)
/\ ro_cells bsegs m1 NBD_GOT_STDERR [C8 (Z_to_bv 64 NBD_STDERR_VAR)] /\ ro_cells bsegs m1 NBD_STDERR_VAR [C8 (Z_to_bv 64 errf)].

Definition R_AX (rv : Z) (xra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) a0 a1 (Z_to_bv 64 sf) a3 a4 a5 a6 a7
(Z_to_bv 64 rv) (Z_to_bv 64 (ST + 2912)) (Z_to_bv 64 A) (Z_to_bv 64 (ST + 32)) (Z_to_bv 64 SHB) (Z_to_bv 64 18446744073709405023) (Z_to_bv 64 5)
(Z_to_bv 64 (Z.shiftr (ST + 2904) 3 + SHB)) (Z_to_bv 64 0x23ca0) (Z_to_bv 64 (Z.shiftr (ST + 2912) 3 + SHB)) t3 t4 t5 t6.
Definition R_AB (mo : Z) (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576)) (Z_to_bv 64 mo) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (-1)) (Z_to_bv 64 (ST + 2912)) (Z_to_bv 64 A) (Z_to_bv 64 (ST + 32)) (Z_to_bv 64 SHB) (Z_to_bv 64 18446744073709405023) (Z_to_bv 64 5)
(Z_to_bv 64 (Z.shiftr (ST + 2904) 3 + SHB)) (Z_to_bv 64 0x23ca0) (Z_to_bv 64 (ST + 2184)) t3 t4 t5 t6.
Definition R_AN (msg : Z) (t0 t1 t2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR (Z_to_bv 64 RA_nbd_fprintf) (Z_to_bv 64 (usp + -576)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -576))
(Z_to_bv 64 errf) (Z_to_bv 64 NBD_FMT_NOTIFY) (Z_to_bv 64 msg) a3 a4 a5 a6 a7
(Z_to_bv 64 (-1)) (Z_to_bv 64 (ST + 2912)) (Z_to_bv 64 A) (Z_to_bv 64 (ST + 32)) (Z_to_bv 64 SHB) (Z_to_bv 64 18446744073709405023) (Z_to_bv 64 5)
(Z_to_bv 64 (Z.shiftr (ST + 2904) 3 + SHB)) (Z_to_bv 64 0x23ca0) s11 t3 t4 t5 t6.

Definition nbA_post (o : @search_out ptr) : machine_state -> Prop := fun ms =>
match o with
| SOunr => True
| SOret rv b' => exists (m' : mem) (sws' : list word) F' fc' (xra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
ms = MS (R_AX rv xra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6) F' (Z_to_bv 64 PC_NBD_X) fc' None m' (seg_rom bsegs)
/\ frm0 fc' /\ nbA_ctx m' b' sws'
| SOmode mo b' => exists (m' : mem) (sws' : list word) F' fc' (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
ms = MS (R_AB mo xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F' (Z_to_bv 64 PC_NBD_B) fc' None m' (seg_rom bsegs)
/\ frm0 fc' /\ nbA_ctx m' b' sws' /\ 0 <= mo <= 8
| SOnotify tw b' => exists (m' : mem) (sws' : list word) F' fc' (t0 t1 t2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word),
ms = MS (R_AN (if tw then NBD_MSG_TWOWB else NBD_MSG_INVALID) t0 t1 t2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6) F' (Z_to_bv 64 PC_wrap_fprintf) fc' None m' (seg_rom bsegs)
/\ frm0 fc' /\ nbA_ctx m' b' sws'
end.
Local Notation RA := (R_A usp ST A gp tp).

Lemma nbA_exit_m1 : forall (b : bits_st ptr) sws (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc m1,
nbA_ctx m1 b sws -> frm0 fc ->
evt bsegs (nbA_post (SOret (-1) b)) (MS (RA xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa444c) fc None m1 (seg_rom bsegs)).
Proof.
intros b sws xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m1 CTX FRM.
pose proof CTX as (MU & WM & MI & ST0 & CC & REP & OKB & SZ & SW & LSW & FR & CBS & UCB & GOTE & VARE).
unfold R_A, nbd_frame_A in *. cbn [app] in FR.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof ST0 as (STa & STb & _).
bato 0xa4450.
apply evt_done. cbn [nbA_post]. do 19 eexists. split; [reflexivity|]. split; [exact FRM| exact CTX].
Qed.
Lemma nbA_offsh : offsh nbA_W.
Proof using LO LOS SPH ASH SESH.
clear - LO LOS SPH ASH SESH. unfold nbA_W, BITS_SIZEOF in *. pose proof (ASH : _ \/ _) as H1. pose proof (SESH : _ \/ _) as H2.
cbn. unfold SH_LO, SH_HI in *. lia.
Qed.

Lemma nbA_exit_n2 : forall (b : bits_st ptr) sws (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc m1,
nbA_ctx m1 b sws -> frm0 fc ->
evt bsegs (nbA_post (SOnotify true b)) (MS (RA xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa463c) fc None m1 (seg_rom bsegs)).
Proof.
intros b sws xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m1 CTX FRM.
pose proof CTX as (MU & WM & MI & ST0 & CC & REP & OKB & SZ & SW & LSW & FR & CBS & UCB & GOTE & VARE).
pose proof nbA_offsh as OF.
pose proof (aobj_munch bsegs _ m m1 _ _ OBV MU (shfree_of_aobj bsegs _ m _ _ OF OBV)) as OBV1.
unfold R_A, nbd_frame_A, NBD_GOT_STDERR, NBD_STDERR_VAR in *. cbn [app] in FR.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof ST0 as (STa & STb & _).
pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
assert (V8 : 1032208 mod 8 = 0) by reflexivity.
bato 0xa4668. astep.
apply evt_done. cbn [nbA_post]. do 17 eexists. split; [reflexivity|]. split; [exact FRM| exact CTX].
Qed.

Lemma nbA_exit_disp : forall (b : bits_st ptr) sws mv (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc m1,
nbA_ctx m1 b sws -> frm0 fc -> 0 <= mv < 16 ->
evt bsegs (nbA_post (if mv =? 15 then SOret (-1) b else if 8 <? mv then SOnotify false b else SOmode mv b))
(MS (RA xra t0 t1 t2 (Z_to_bv 64 mv) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa43fc) fc None m1 (seg_rom bsegs)).
Proof.
intros b sws mv xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m1 CTX FRM MV.
pose proof CTX as (MU & WM & MI & ST0 & CC & REP & OKB & SZ & SW & LSW & FR & CBS & UCB & GOTE & VARE).
pose proof nbA_offsh as OF.
pose proof (aobj_munch bsegs _ m m1 _ _ OBV MU (shfree_of_aobj bsegs _ m _ _ OF OBV)) as OBV1.
unfold R_A, nbd_frame_A, NBD_GOT_STDERR, NBD_STDERR_VAR in *. cbn [app] in FR.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof ST0 as (STa & STb & _).
pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
assert (V8 : 1032208 mod 8 = 0) by reflexivity.
bato 0xa4404. astep.
destruct (mv =? 15) eqn:K15; [apply Z.eqb_eq in K15 | apply Z.eqb_neq in K15].
- sh_if. apply evt_done. cbn [nbA_post]. do 19 eexists. split; [reflexivity|]. split; [exact FRM| exact CTX].
- sh_if. bato 0xa4410. astep.
destruct (8 <? mv) eqn:K9; [apply Z.ltb_lt in K9 | apply Z.ltb_ge in K9].
+ sh_if. bato 0xa4668. astep.
apply evt_done. cbn [nbA_post]. do 17 eexists. split; [reflexivity|]. split; [exact FRM| exact CTX].
+ sh_if. astep.
apply evt_done. cbn [nbA_post]. do 19 eexists. split; [reflexivity|]. split; [exact FRM|]. split; [exact CTX| lia].
Qed.
Ltac nbA_unf := unfold R_A, nbA_W, cb_cells, NBD_GOT_STDERR, NBD_STDERR_VAR, A_wb_skip_table, A_e_ratio_quant,
gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
Ltac nbA_close G1 G2 G3 G4 :=
unfold nbA_ctx, nbA_W, client_constsB, cb_cells, NBD_GOT_STDERR, NBD_STDERR_VAR,
gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return;
refine (conj _ (conj _ (conj _ (conj _ (conj (conj G1 (conj G2 (conj G3 G4))) (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))))));
first [eassumption | lia | congruence].

Ltac slia1 := first [ lia | match goal with H : hidp (_ \/ _) |- _ => unfold hidp in H; lia end ].
Ltac slia_c := lazymatch goal with |- _ /\ _ => split; [slia1 | slia_c] | |- True => exact I | |- _ => slia1 end.
Local Ltac slia ::= (try unfold BITS_SIZEOF, USERH_DEPTH, INBAND_DEPTH in * ); slia_c.

Lemma nbA_back : forall fuel (b : bits_st ptr) sws (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc m1,
(forall (b' : bits_st ptr) sws' (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m2,
nbA_ctx m2 b' sws' -> frm0 fc' -> 5 <= speex_bits_remaining b' ->
evt bsegs (nbA_post (search_pure fuel sc b')) (MS (RA xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F' (Z_to_bv 64 0xa1b18) fc' None m2 (seg_rom bsegs))) ->
nbA_ctx m1 b sws -> frm0 fc ->
evt bsegs (nbA_post (search_pure fuel sc b)) (MS (RA xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa1c88) fc None m1 (seg_rom bsegs)).
Proof.
intros fuel b sws xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m1 IH CTX FRM.
pose proof CTX as (MU0 & WM0 & MI & ST0 & CC & REP & OKB & SZ & SW & LSW & FR & CBS & UCB & GOTE & VARE).
pose proof nbA_offsh as OF.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof ST0 as (STa & STb & _).
pose proof OBA as (OA0 & OA1 & _). unfold APP_TOP, BITS_SIZEOF in *.
pose proof ATOP as ATOP'. unfold IMG_TOP_B in ATOP'.
pose proof CC as (G1 & G2 & G3 & G4).
nbA_unf.
pose proof (aobj_munch bsegs _ m m1 A 48 OBA MU0 (shfree_of_aobj bsegs _ m A 48 OF OBA)) as OBA1.
assert (DLO' : D + sb_buf_size b <= lo) by (rewrite SZ; exact DLO).
assert (CC1 : client_constsB m1) by (unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4)))).
pose proof (munch_refl [(A, A + 48); (STEREO, STEREO + 8); (usp + -672, usp + -576)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
astep. astep.
call (speex_bits_remaining_walk A D (usp + -576) lo b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 REP OKB OBA1 ST0 ltac:(lia) LOS ltac:(lia) ALO DLO' CC1).
all: try eassumption.
match goal with H : ?x = Z_to_bv 64 (speex_bits_remaining b) |- _ => subst x end.
pose proof REP as (_ & _ & SIDE). pose proof (remaining_range A D b OKB SIDE) as RR. change (2^31) with 2147483648 in RR.
astep.
destruct (speex_bits_remaining b <? 5) eqn:K; [apply Z.ltb_lt in K | apply Z.ltb_ge in K].
- sh_if. astep.
destruct (search_pure_lt5 fuel sc b K) as [E|E]; rewrite E.
+ apply evt_done. exact I.
+ eapply nbA_exit_m1; [| exact FRM]. nbA_close G1 G2 G3 G4.
- sh_if. eapply IH; [| exact FRM | exact K]. nbA_close G1 G2 G3 G4.
Qed.
Lemma nbA_tail : forall fuel (b : bits_st ptr) sws (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc m1,
(forall (b' : bits_st ptr) sws' (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m2,
nbA_ctx m2 b' sws' -> frm0 fc' -> 5 <= speex_bits_remaining b' ->
evt bsegs (nbA_post (search_pure fuel sc b')) (MS (RA xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F' (Z_to_bv 64 0xa1b18) fc' None m2 (seg_rom bsegs))) ->
nbA_ctx m1 b sws -> frm0 fc ->
evt bsegs (nbA_post (search_tail fuel sc b)) (MS (RA xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa1bfc) fc None m1 (seg_rom bsegs)).
Proof.
intros fuel b sws xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m1 IH CTX FRM.
pose proof CTX as (MU0 & WM0 & MI & ST0 & CC & REP & OKB & SZ & SW & LSW & FR & CBS & UCB & GOTE & VARE).
pose proof nbA_offsh as OF.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof ST0 as (STa & STb & _).
pose proof OBA as (OA0 & OA1 & _). unfold APP_TOP, BITS_SIZEOF in *.
pose proof ATOP as ATOP'. unfold IMG_TOP_B in ATOP'. pose proof SETOP as SETOP'. unfold IMG_TOP_B in SETOP'.
pose proof CC as (G1 & G2 & G3 & G4).
nbA_unf.
pose proof (aobj_munch bsegs _ m m1 A 48 OBA MU0 (shfree_of_aobj bsegs _ m A 48 OF OBA)) as OBA1.
assert (OBD' : aobj bsegs m D (sb_buf_size b)) by (rewrite SZ; exact OBD).
pose proof (aobj_munch bsegs _ m m1 D _ OBD' MU0 (shfree_of_aobj bsegs _ m D _ OF OBD')) as OBD1.
assert (DLO' : D + sb_buf_size b <= lo) by (rewrite SZ; exact DLO).
assert (CC1 : client_constsB m1) by (unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4)))).
pose proof (munch_refl [(A, A + 48); (STEREO, STEREO + 8); (usp + -672, usp + -576)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
astep. astep.
call (speex_bits_remaining_walk A D (usp + -576) lo b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 REP OKB OBA1 ST0 ltac:(lia) LOS ltac:(lia) ALO DLO' CC1).
all: try eassumption.
match goal with H : ?x = Z_to_bv 64 (speex_bits_remaining b) |- _ => subst x end.
pose proof REP as (_ & _ & SIDE). pose proof (remaining_range A D b OKB SIDE) as RR. change (2^31) with 2147483648 in RR.
bato 0xa1c08. astep. unfold search_tail.
destruct (speex_bits_remaining b <? 4) eqn:K4; [apply Z.ltb_lt in K4 | apply Z.ltb_ge in K4].
{ sh_if. astep.
eapply nbA_exit_m1; [| exact FRM].
nbA_close G1 G2 G3 G4. }
sh_if.
clear OBA1 OBD1 REP. rename POST into REP.
lazymatch goal with MU0 : munch ?W m ?mc |- _ =>
pose proof (aobj_munch bsegs W m mc _ _ OBA MU0 (shfree_of_aobj bsegs W m _ _ OF OBA)) as OBA1;
pose proof (aobj_munch bsegs W m mc _ _ OBD' MU0 (shfree_of_aobj bsegs W m _ _ OF OBD')) as OBD1 end.
bato 0xa1c18. astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -576) lo b 4 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP OKB ltac:(lia) OBA1 OBD1 ASH ltac:(lia) LOS ltac:(lia) ALO DLO').
all: try eassumption.
{ unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))). }
match goal with H : ?x = Z_to_bv 64 (fst (speex_bits_unpack_unsigned b 4)) |- _ => subst x end. set (mv := fst (speex_bits_unpack_unsigned b 4)) in *. set (b1 := snd (speex_bits_unpack_unsigned b 4)) in *.
assert (UE : speex_bits_unpack_unsigned b 4 = (mv, b1)) by (unfold mv, b1; destruct (speex_bits_unpack_unsigned b 4); reflexivity).
pose proof (speex_bits_unpack_unsigned_ok b 4 mv b1 OKB ltac:(lia) UE) as (OK1 & VR & _ & _ & SZ1 & _). change (2^4) with 16 in VR.
change (uv b 4) with mv. change (ub b 4) with b1.
clear OBA1 OBD1 REP. rename POST into REP.
assert (SZ1' : sb_buf_size b1 = BSZ) by congruence.
assert (DLO1 : D + sb_buf_size b1 <= lo) by (rewrite SZ1; exact DLO').
lazymatch goal with MU0 : munch ?W m ?mc |- _ =>
pose proof (aobj_munch bsegs W m mc _ _ OBA MU0 (shfree_of_aobj bsegs W m _ _ OF OBA)) as OBA1;
pose proof (aobj_munch bsegs W m mc _ _ OBD' MU0 (shfree_of_aobj bsegs W m _ _ OF OBD')) as OBD1;
pose proof (aobj_munch bsegs W m mc _ _ OBST MU0 (shfree_of_aobj bsegs W m _ _ OF OBST)) as OBST1;
pose proof (aobj_munch bsegs W m mc _ _ OBSE MU0 (shfree_of_aobj bsegs W m _ _ OF OBSE)) as OBSE1;
pose proof (aobj_munch bsegs W m mc _ _ OBE MU0 (shfree_of_aobj bsegs W m _ _ OF OBE)) as OBE1 end.
rewrite <- SZ1 in OBD1.
unfold nbd_frame_A in FR. cbn [app] in FR.
pose proof SB as (SB0 & SB1).
bato 0xa1c20. astep.
destruct (mv =? 13) eqn:K13; [apply Z.eqb_eq in K13 | apply Z.eqb_neq in K13]; sh_if.
{
replace (mv =? 15) with false by (symmetry; apply Z.eqb_neq; lia).
replace (mv =? 14) with false by (symmetry; apply Z.eqb_neq; lia).
bato 0xa1c7c. astep.
replace (ret_pc (Z_to_bv 64 A_speex_default_user_handler)) with (Z_to_bv 64 A_speex_default_user_handler)
by (unfold A_speex_default_user_handler; symmetry; apply ret_pc_even; [lia| reflexivity]).
call (UHB ptr A D ST (usp + -576) lo b1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP OK1 OBA1 OBD1 ASH ATOP ALO DLO1).
all: try eassumption. all: try (unfold USERH_DEPTH; lia).
{ unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))). }
replace (ret_pc (Z_to_bv 64 662656)) with (Z_to_bv 64 662656) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (adv_size (ub b1 4) (5 + 8 * uv b1 4)) as SZ2. rewrite ub_size in SZ2. fold (user_handler_bits b1) in SZ2.
bato 0xa1c88.
eapply nbA_back; [exact IH | | eassumption].
nbA_close G1 G2 G3 G4. }
bato 0xa1c28. astep.
destruct (mv =? 14) eqn:K14; [apply Z.eqb_eq in K14 | apply Z.eqb_neq in K14]; sh_if.
2: { astep. eapply nbA_exit_disp; [| exact FRM | exact VR]. nbA_close G1 G2 G3 G4. }
replace (mv =? 15) with false by (symmetry; apply Z.eqb_neq; lia).

bato 0xa1c40. astep.
assert (CBH : rw_cells bsegs x20 (ST + 2256) (cbs_cells 16 A_speex_std_stereo_request_handler STEREO sc js)).
{ eapply rw_cells_recast; [exact CBS | apply cbs_cells_wf; exact FJS | cbn [cells_bytes cbytes]; rewrite app_nil_r; symmetry; exact ECBS]. }
pose proof (aobj_sub bsegs x20 ST 2968 (ST + 2256) 640 OBST1 ltac:(lia) ltac:(lia)) as OBC1.
assert (AP1 : hidp (ST + 2256 + 640 <= A \/ A + BITS_SIZEOF <= ST + 2256)) by (clear - AP_ST_A; unfold hidp, BITS_SIZEOF in *; lia).
assert (AP2 : hidp (ST + 2256 + 640 <= STEREO \/ STEREO + 8 <= ST + 2256)) by (clear - AP_ST_SE; unfold hidp in *; lia).
assert (AP3 : hidp (STEREO + 8 <= D \/ D + sb_buf_size b1 <= STEREO)) by (rewrite SZ1'; exact AP_SE_D).
assert (CA8 : (ST + 2256) mod 8 = 0) by (clear - ST8; Z.div_mod_to_equations; lia).
callc (IHB ptr sc A D (ST + 2256) ST STEREO (usp + -576) lo b1 js sws _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
REP OK1 CBH LJS FJS SW LSW OBA1 OBD1 OBC1 OBSE1 OBE1 CA8 SE4 ASH SESH ATOP SETOP ALO DLO1 ltac:(lia) SELO AP1 AP2 AP_SE_A AP3) (clear CBH).
all: try eassumption. all: try (unfold INBAND_DEPTH; lia).
all: try eassumption. all: try (unfold INBAND_DEPTH; lia).
{ unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))). }
replace (ret_pc (Z_to_bv 64 662596)) with (Z_to_bv 64 662596) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
assert (SZ2 : sb_buf_size (inband_bits sc b1) = sb_buf_size b1).
{ unfold inband_bits, stereo_handler_bits. destruct (_ && _); rewrite ?adv_size, ?ub_size; reflexivity. }
bato 0xa1c88.
eapply nbA_back; [exact IH | | eassumption].
nbA_close G1 G2 G3 G4.
Qed.

Lemma frame_A_288 : forall m1, rw_cells bsegs m1 (usp + -576) (nbd_frame_A ST A OUT f sf ja jb jc jd je jf jg jh1 jh2 sv) ->
rw_cells bsegs m1 (usp + -288) [C8 (Z_to_bv 64 A)].
Proof.
intros m1 H. unfold nbd_frame_A in H. cbn [app] in H.
lazymatch type of H with rw_cells _ _ _ ?cs =>
assert (E0 : nth_error cs 16 = Some (C8 (Z_to_bv 64 A))) by reflexivity;
apply nth_error_split in E0 as (l1 & l2 & E & L1) end.
rewrite E in H. apply rw_cells_app in H as [_ H]. apply rw_cells_uncons in H as [H _].
assert (S1 : cells_size l1 = 288%nat).
{ assert (E2 : firstn 16 (l1 ++ C8 (Z_to_bv 64 A) :: l2) = l1)
by (rewrite firstn_app, L1, Nat.sub_diag, firstn_O, app_nil_r, <- L1, firstn_all; reflexivity).
rewrite <- E in E2. rewrite <- E2. reflexivity. }
rewrite S1 in H. replace (usp + -576 + Z.of_nat 288) with (usp + -288) in H by lia. exact H.
Qed.
Lemma nbA_head : forall fuel (b : bits_st ptr) sws (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc m1,
(forall (b' : bits_st ptr) sws' (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m2,
nbA_ctx m2 b' sws' -> frm0 fc' ->
evt bsegs (nbA_post (search_tail fuel sc b')) (MS (RA xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F' (Z_to_bv 64 0xa1bfc) fc' None m2 (seg_rom bsegs))) ->
nbA_ctx m1 b sws -> frm0 fc -> 5 <= speex_bits_remaining b ->
evt bsegs (nbA_post (match search_head b with inr o => o | inl bm => search_tail fuel sc bm end))
(MS (RA xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa1b18) fc None m1 (seg_rom bsegs)).
Proof.
intros fuel b sws xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m1 TL CTX FRM REM.
pose proof CTX as (MU0 & WM0 & MI & ST0 & CC & REP & OKB & SZ & SW & LSW & FR & CBS & UCB & GOTE & VARE).
pose proof nbA_offsh as OF.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof ST0 as (STa & STb & _).
pose proof OBA as (OA0 & OA1 & _). unfold APP_TOP, BITS_SIZEOF in *.
pose proof ATOP as ATOP'. unfold IMG_TOP_B in ATOP'. pose proof SETOP as SETOP'. unfold IMG_TOP_B in SETOP'.
pose proof CC as (G1 & G2 & G3 & G4).
nbA_unf.
assert (OBD' : aobj bsegs m D (sb_buf_size b)) by (rewrite SZ; exact OBD).
assert (DLO' : D + sb_buf_size b <= lo) by (rewrite SZ; exact DLO).
pose proof (aobj_munch bsegs _ m m1 A 48 OBA MU0 (shfree_of_aobj bsegs _ m A 48 OF OBA)) as OBA1.
pose proof (aobj_munch bsegs _ m m1 D _ OBD' MU0 (shfree_of_aobj bsegs _ m D _ OF OBD')) as OBD1.
assert (CC1 : client_constsB m1) by (unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4)))).
pose proof (munch_refl [(A, A + 48); (STEREO, STEREO + 8); (usp + -672, usp + -576)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
bato 0xa1b20. astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -576) lo b 1 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP OKB ltac:(lia) OBA1 OBD1 ASH ltac:(lia) LOS ltac:(lia) ALO DLO').
all: try eassumption.
match goal with H : ?x = Z_to_bv 64 (fst (speex_bits_unpack_unsigned b 1)) |- _ => subst x end. set (w1 := fst (speex_bits_unpack_unsigned b 1)) in *. set (b1 := snd (speex_bits_unpack_unsigned b 1)) in *.
assert (UE : speex_bits_unpack_unsigned b 1 = (w1, b1)) by (unfold w1, b1; destruct (speex_bits_unpack_unsigned b 1); reflexivity).
pose proof (speex_bits_unpack_unsigned_ok b 1 w1 b1 OKB ltac:(lia) UE) as (OK1 & VR & _ & _ & SZ1 & _). change (2^1) with 2 in VR.
pose proof (ub_exact b 1 OKB ltac:(lia) ltac:(lia)) as (_ & POS1 & _ & REM1). cbv [A.X082.ub] in POS1, REM1. fold b1 in POS1, REM1.
unfold search_head. change (uv b 1) with w1. change (ub b 1) with b1. cbv zeta.
clear OBA1 OBD1 REP. rename POST into REP.
assert (SZ1' : sb_buf_size b1 = BSZ) by congruence.
astep.
destruct (w1 =? 0) eqn:K1; [apply Z.eqb_eq in K1 | apply Z.eqb_neq in K1]; sh_if; cbn [negb].
{ eapply TL; [| exact FRM]. nbA_close G1 G2 G3 G4. }
pose proof REP as (_ & _ & SIDE0).
assert (POS0 : 0 <= bits_pos b).
{ pose proof CTX as (_ & _ & _ & _ & _ & (_ & _ & SIDEb) & _). pose proof (bits_ints A D b OKB SIDEb) as (In & Ic & Ib & Io & Iv & Is & Rc & Rb & Rp & Rn & Rs & R1 & Rov).
unfold bits_pos, int31 in *. lia. }
assert (OFS : offsh [(A, A + 48); (usp + -672, usp + -576)]).
{ clear - LO LOS SPH ASH. pose proof (ASH : _ \/ _) as H1. cbn. unfold SH_LO, SH_HI in *. lia. }
lazymatch goal with MU0 : munch ?W m ?mc |- _ =>
pose proof (aobj_munch bsegs W m mc _ _ OBA MU0 (shfree_of_aobj bsegs W m _ _ OF OBA)) as OBA1;
pose proof (aobj_munch bsegs W m mc _ _ OBD' MU0 (shfree_of_aobj bsegs W m _ _ OF OBD')) as OBD1;
pose proof (aobj_munch bsegs W m mc _ _ OBT MU0 (shfree_of_aobj bsegs W m _ _ OF OBT)) as OBT1 end.
rewrite <- SZ1 in OBD1.
assert (DLO1 : D + sb_buf_size b1 <= lo) by (rewrite SZ1; exact DLO').
pose proof (frame_A_288 _ FR) as SLB.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
call (nbA_skip1 usp lo ST A D gp tp mc LO LOS SPH OBA1 OBT1 ALO ASH ATOP b1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mc REP OK1 OBD1 DLO1 ltac:(lia) ltac:(lia)
(munch_refl _ mc) OFS (wmono_refl bsegs mc)) end.
all: try eassumption.
{ unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))). }
unfold R_A.
clear OBA1 OBD1 OBT1 REP POST. rename PC0 into REP. rename PC1 into OK2. rename PC2 into SZ2. rename PC into ST1.
set (b2 := skip_bits b1) in *.
assert (SZ2' : sb_buf_size b2 = BSZ) by congruence.
assert (DLO2 : D + sb_buf_size b2 <= lo) by (rewrite SZ2'; exact DLO).
assert (OBD2' : aobj bsegs m D (sb_buf_size b2)) by (rewrite SZ2'; exact OBD).
lazymatch goal with MU0 : munch ?W m ?mc |- _ =>
pose proof (aobj_munch bsegs W m mc _ _ OBA MU0 (shfree_of_aobj bsegs W m _ _ OF OBA)) as OBA1 end.
bato 0xa1b7c. astep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
call (speex_bits_remaining_walk A D (usp + -576) lo b2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc REP OK2 OBA1 ST1 ltac:(lia) LOS ltac:(lia) ALO DLO2) end.
all: try eassumption.
{ unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))). }
match goal with H : ?x = Z_to_bv 64 (speex_bits_remaining b2) |- _ => subst x end.
pose proof REP as (_ & _ & SIDE2). pose proof (remaining_range A D b2 OK2 SIDE2) as RR2. change (2^31) with 2147483648 in RR2.
clear OBA1 REP. rename POST into REP.
astep.
destruct (speex_bits_remaining b2 <? 5) eqn:K2; [apply Z.ltb_lt in K2 | apply Z.ltb_ge in K2]; sh_if.
{ astep. eapply nbA_exit_m1; [| exact FRM]. nbA_close G1 G2 G3 G4. }
lazymatch goal with MU0 : munch ?W m ?mc |- _ =>
pose proof (aobj_munch bsegs W m mc _ _ OBA MU0 (shfree_of_aobj bsegs W m _ _ OF OBA)) as OBA1;
pose proof (aobj_munch bsegs W m mc _ _ OBD2' MU0 (shfree_of_aobj bsegs W m _ _ OF OBD2')) as OBD1 end.
bato 0xa1b90. astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -576) lo b2 1 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP OK2 ltac:(lia) OBA1 OBD1 ASH ltac:(lia) LOS ltac:(lia) ALO DLO2).
all: try eassumption.
{ unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))). }
match goal with H : ?x = Z_to_bv 64 (fst (speex_bits_unpack_unsigned b2 1)) |- _ => subst x end. set (w2 := fst (speex_bits_unpack_unsigned b2 1)) in *. set (b3 := snd (speex_bits_unpack_unsigned b2 1)) in *.
assert (UE2 : speex_bits_unpack_unsigned b2 1 = (w2, b3)) by (unfold w2, b3; destruct (speex_bits_unpack_unsigned b2 1); reflexivity).
pose proof (speex_bits_unpack_unsigned_ok b2 1 w2 b3 OK2 ltac:(lia) UE2) as (OK3 & VR2 & _ & _ & SZ3 & _). change (2^1) with 2 in VR2.
pose proof (ub_exact b2 1 OK2 ltac:(lia) ltac:(lia)) as (_ & POS3 & _ & REM3). cbv [A.X082.ub] in POS3, REM3. fold b3 in POS3, REM3.
change (uv b2 1) with w2. change (ub b2 1) with b3.
clear OBA1 OBD1 REP. rename POST into REP.
assert (SZ3' : sb_buf_size b3 = BSZ) by congruence.
astep.
destruct (w2 =? 0) eqn:K3; [apply Z.eqb_eq in K3 | apply Z.eqb_neq in K3]; sh_if; cbn [negb].
{ eapply TL; [| exact FRM]. nbA_close G1 G2 G3 G4. }
assert (POS2 : 0 <= bits_pos b2).
{ pose proof (bits_ints A D b2 OK2 SIDE2) as (In & Ic & Ib & Io & Iv & Is & Rc & Rb & Rp & Rn & Rs & R1 & Rov). unfold bits_pos, int31 in *. lia. }
assert (DLO3 : D + sb_buf_size b3 <= lo) by (rewrite SZ3'; exact DLO).
assert (OBD3' : aobj bsegs m D (sb_buf_size b3)) by (rewrite SZ3'; exact OBD).
lazymatch goal with MU0 : munch ?W m ?mc |- _ =>
pose proof (aobj_munch bsegs W m mc _ _ OBA MU0 (shfree_of_aobj bsegs W m _ _ OF OBA)) as OBA1;
pose proof (aobj_munch bsegs W m mc _ _ OBD3' MU0 (shfree_of_aobj bsegs W m _ _ OF OBD3')) as OBD1;
pose proof (aobj_munch bsegs W m mc _ _ OBT MU0 (shfree_of_aobj bsegs W m _ _ OF OBT)) as OBT1 end.
try clear SLB. pose proof (frame_A_288 _ FR) as SLB.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
call (nbA_skip2 usp lo ST A D gp tp mc LO LOS SPH OBA1 OBT1 ALO ASH ATOP b3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mc REP OK3 OBD1 DLO3 ltac:(lia) ltac:(lia)
(munch_refl _ mc) OFS (wmono_refl bsegs mc)) end.
all: try eassumption.
{ unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))). }
unfold R_A.
clear OBA1 OBD1 OBT1 REP POST. rename PC0 into REP. rename PC1 into OK4. rename PC2 into SZ4. rename PC into ST2.
set (b4 := skip_bits b3) in *.
assert (SZ4' : sb_buf_size b4 = BSZ) by congruence.
assert (DLO4 : D + sb_buf_size b4 <= lo) by (rewrite SZ4'; exact DLO).
assert (OBD4' : aobj bsegs m D (sb_buf_size b4)) by (rewrite SZ4'; exact OBD).
lazymatch goal with MU0 : munch ?W m ?mc |- _ =>
pose proof (aobj_munch bsegs W m mc _ _ OBA MU0 (shfree_of_aobj bsegs W m _ _ OF OBA)) as OBA1;
pose proof (aobj_munch bsegs W m mc _ _ OBD4' MU0 (shfree_of_aobj bsegs W m _ _ OF OBD4')) as OBD1 end.
bato 0xa1bf0. astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -576) lo b4 1 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP OK4 ltac:(lia) OBA1 OBD1 ASH ltac:(lia) LOS ltac:(lia) ALO DLO4).
all: try eassumption.
{ unfold client_constsB, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))). }
match goal with H : ?x = Z_to_bv 64 (fst (speex_bits_unpack_unsigned b4 1)) |- _ => subst x end.
set (w3 := fst (speex_bits_unpack_unsigned b4 1)) in *. set (b5 := snd (speex_bits_unpack_unsigned b4 1)) in *.
assert (UE4 : speex_bits_unpack_unsigned b4 1 = (w3, b5)) by (unfold w3, b5; destruct (speex_bits_unpack_unsigned b4 1); reflexivity).
pose proof (speex_bits_unpack_unsigned_ok b4 1 w3 b5 OK4 ltac:(lia) UE4) as (OK5 & VR4 & _ & _ & SZ5 & _). change (2^1) with 2 in VR4.
change (uv b4 1) with w3. change (ub b4 1) with b5.
clear OBA1 OBD1 REP. rename POST into REP.
assert (SZ5' : sb_buf_size b5 = BSZ) by congruence.
astep.
destruct (w3 =? 0) eqn:K5; [apply Z.eqb_eq in K5 | apply Z.eqb_neq in K5]; sh_if; cbn [negb].
{ eapply TL; [| exact FRM]. nbA_close G1 G2 G3 G4. }
astep. eapply nbA_exit_n2; [| exact FRM]. nbA_close G1 G2 G3 G4.
Qed.

Theorem nbA_loop : forall fuel (b : bits_st ptr) sws (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc m1,
nbA_ctx m1 b sws -> frm0 fc -> 5 <= speex_bits_remaining b ->
evt bsegs (nbA_post (search_pure fuel sc b)) (MS (RA xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa1b18) fc None m1 (seg_rom bsegs)).
Proof.
induction fuel as [|fuel IH]; intros b sws xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m1 CTX FRM REM.
- apply evt_done. exact I.
- rewrite search_pure_S. replace (speex_bits_remaining b <? 5) with false by (symmetry; apply Z.ltb_ge; exact REM).
eapply nbA_head; [| exact CTX | exact FRM | exact REM].
intros b' sws' xra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m2 CTX' FRM'.
eapply nbA_tail; [| exact CTX' | exact FRM'].
intros b'' sws'' xra'' t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F'' fc'' m3 CTX'' FRM'' REM''.
eapply IH; eassumption.
Qed.
End Loop.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac slia ::= (try unfold BITS_SIZEOF in * ); first [ exact I | lia | split; [lia|exact I] ].
Local Notation mem := (word -> option byte).

Section TailPure.
Context {ptr : Type}.
Definition search_tail (fuel : nat) (sc : bool) (bm : bits_st ptr) : search_out :=
if speex_bits_remaining bm <? 4 then SOret (-1) bm else
let m := uv bm 4 in let b6 := ub bm 4 in
if m =? 15 then SOret (-1) b6
else if m =? 14 then search_pure fuel sc (inband_bits sc b6)
else if m =? 13 then search_pure fuel sc (user_handler_bits b6)
else if 8 <? m then SOnotify false b6
else SOmode m b6.

Definition search_head (b : bits_st ptr) : bits_st ptr + search_out :=
let w1 := uv b 1 in let b1 := ub b 1 in
if negb (w1 =? 0) then
let b2 := skip_bits b1 in
if speex_bits_remaining b2 <? 5 then inr (SOret (-1) b2) else
let w2 := uv b2 1 in let b3 := ub b2 1 in
if negb (w2 =? 0) then
let b4 := skip_bits b3 in
let w3 := uv b4 1 in let b5 := ub b4 1 in
if negb (w3 =? 0) then inr (SOnotify true b5) else inl b5
else inl b3
else inl b1.
Lemma search_pure_S : forall fuel sc (b : bits_st ptr),
search_pure (S fuel) sc b =
if speex_bits_remaining b <? 5 then SOret (-1) b else
match search_head b with inr o => o | inl bm => search_tail fuel sc bm end.
Proof. reflexivity. Qed.
Lemma search_pure_lt5 : forall fuel sc (b : bits_st ptr), speex_bits_remaining b < 5 ->
search_pure fuel sc b = SOunr \/ search_pure fuel sc b = SOret (-1) b.
Proof.
intros [|fuel] sc b H; [left; reflexivity | right].
rewrite search_pure_S. replace (speex_bits_remaining b <? 5) with true by (symmetry; apply Z.ltb_lt; exact H). reflexivity.
Qed.
End TailPure.
Definition PC_wrap_fprintf : Z := 0x56c1c.
Definition RA_nbd_fprintf : Z := 0xa1bcc.
Definition NBD_GOT_STDERR : Z := 0xf44f8.
Definition NBD_STDERR_VAR : Z := 0xf3790.
Definition NBD_FMT_NOTIFY : Z := 0x23ec0.
Definition NBD_MSG_INVALID : Z := 0x23cc0.
Definition NBD_MSG_TWOWB : Z := 0x23d20.
Definition PC_NBD_B : Z := 0x9fbdc.

Lemma cbs_cells_wf : forall k sf sd bb js, Forall (fun p => length (fst p) = 8%nat /\ length (snd p) = 16%nat) js ->
cells_wf (cbs_cells k sf sd bb js).
Proof.
induction k as [|k IH]; intros sf sd bb js F; [exact I|].
destruct js as [|j0 js]; [exact I|]. cbn [cbs_cells]. cbv zeta. inversion F; subst.
apply cells_wf_app. split; [| apply IH; assumption].
destruct H1 as [L1 L2]. destruct (_ && _); cbn; repeat split; assumption.
Qed.

Section Loop.
Context {ptr : Type}.
Variables (usp lo ST A D OUT STEREO f sf BSZ errf : Z).
Variables gp tp : word.
Variable sc : bool.
Variable js : list (list byte * list byte).
Variable cbs : list byte.
Variable ju : list byte * list byte.
Variables (ja jb jc jd je jf jg jh : list byte) (sv : list cell).
Variable m : mem.
Hypothesis LO : lo <= usp - 544 - 96.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis ALO : A + BITS_SIZEOF <= lo.
Hypothesis ATOP : IMG_TOP <= A.
Hypothesis ASH : hidp (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A).
Hypothesis DLO : D + BSZ <= lo.
Hypothesis ST8 : ST mod 8 = 0.
Hypothesis SB : 0 < ST /\ ST + 2968 <= 140737488355328.
Hypothesis STLO : ST + 2968 <= lo.
Hypothesis SE4 : STEREO mod 4 = 0.
Hypothesis SELO : STEREO + 8 <= lo.
Hypothesis SETOP : IMG_TOP <= STEREO.
Hypothesis SESH : hidp (STEREO + 8 <= SH_LO \/ SH_HI <= STEREO).
Hypothesis AP_ST_A : hidp (ST + 2968 <= A \/ A + BITS_SIZEOF <= ST).
Hypothesis AP_ST_SE : hidp (ST + 2968 <= STEREO \/ STEREO + 8 <= ST).
Hypothesis AP_SE_A : hidp (STEREO + 8 <= A \/ A + BITS_SIZEOF <= STEREO).
Hypothesis AP_SE_D : hidp (STEREO + 8 <= D \/ D + BSZ <= STEREO).
Hypothesis LJS : length js = 16%nat.
Hypothesis FJS : Forall (fun p => length (fst p) = 8%nat /\ length (snd p) = 16%nat) js.
Hypothesis ECBS : cbs = cells_bytes (cbs_cells 16 A_speex_std_stereo_request_handler STEREO sc js).
Hypothesis OBA : aobj asegs m A BITS_SIZEOF.
Hypothesis OBD : aobj asegs m D BSZ.
Hypothesis OBST : aobj asegs m ST 2968.
Hypothesis OBSE : aobj asegs m STEREO 8.
Hypothesis OBT : aobj asegs m A_wb_skip_table 32.
Hypothesis OBE : aobj asegs m A_e_ratio_quant 16.
Hypothesis OBV : aobj asegs m NBD_STDERR_VAR 8.

Definition nbA_W : list (Z * Z) := [(A, A + 48); (STEREO, STEREO + 8); (usp + -640, usp + -544)].
Definition nbA_ctx (m1 : mem) (b : bits_st ptr) (sws : list word) : Prop :=
munch nbA_W m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -544) /\ client_consts m1
/\ bits_rep asegs m1 A D b /\ bits_ok b /\ sb_buf_size b = BSZ
/\ rw_cells asegs m1 STEREO (f32 sws) /\ length sws = 2%nat
/\ rw_cells asegs m1 (usp + -544) (nbd_frame_A ST A OUT f ja jb jc jd je jf jg jh sv)
/\ rw_cells asegs m1 (ST + 2256) [CB 640 cbs]
/\ rw_cells asegs m1 (ST + 2896) (cb_cells A_speex_default_user_handler 0 ju)
/\ ro_cells asegs m1 NBD_GOT_STDERR [C8 (Z_to_bv 64 NBD_STDERR_VAR)] /\ ro_cells asegs m1 NBD_STDERR_VAR [C8 (Z_to_bv 64 errf)].

Definition R_AX (rv : Z) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 sf) (Z_to_bv 64 rv) (Z_to_bv 64 f) (Z_to_bv 64 A) (Z_to_bv 64 (ST + 2912)) (Z_to_bv 64 5) (Z_to_bv 64 ST)
(Z_to_bv 64 f) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.shiftr (ST + 2912) 3 + SHB)) t3 t4 t5 t6.
Definition R_AB (mo : Z) (xra t0 t1 t2 a1 a2 a3 a5 a6 a7 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) (Z_to_bv 64 mo) a1 a2 a3 (Z_to_bv 64 (ST + 32)) a5 a6 a7
(Z_to_bv 64 sf) (Z_to_bv 64 0) (Z_to_bv 64 f) (Z_to_bv 64 (ST + 2120)) (Z_to_bv 64 (ST + 2047)) (Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB)) (Z_to_bv 64 ST)
(Z_to_bv 64 f) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2032)) t3 t4 t5 t6.
Definition R_AN (msg : Z) (t0 t1 t2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s11 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR (Z_to_bv 64 RA_nbd_fprintf) (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544))
(Z_to_bv 64 errf) (Z_to_bv 64 NBD_FMT_NOTIFY) (Z_to_bv 64 msg) a3 a4 a5 a6 a7
(Z_to_bv 64 sf) s3 (Z_to_bv 64 f) s5 s6 s7 (Z_to_bv 64 ST) (Z_to_bv 64 f) (Z_to_bv 64 SHB) s11 t3 t4 t5 t6.

Definition nbA_post (o : @search_out ptr) : machine_state -> Prop := fun ms =>
match o with
| SOunr => True
| SOret rv b' => exists (m' : mem) (sws' : list word) F' fc' (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
ms = MS (R_AX rv xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F' (Z_to_bv 64 PC_NBD_X) fc' None m' (seg_rom asegs)
/\ frm0 fc' /\ nbA_ctx m' b' sws'
| SOmode mo b' => exists (m' : mem) (sws' : list word) F' fc' (xra t0 t1 t2 a1 a2 a3 a5 a6 a7 t3 t4 t5 t6 : word),
ms = MS (R_AB mo xra t0 t1 t2 a1 a2 a3 a5 a6 a7 t3 t4 t5 t6) F' (Z_to_bv 64 PC_NBD_B) fc' None m' (seg_rom asegs)
/\ frm0 fc' /\ nbA_ctx m' b' sws' /\ 0 <= mo <= 8
| SOnotify tw b' => exists (m' : mem) (sws' : list word) F' fc' (t0 t1 t2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s11 t3 t4 t5 t6 : word),
ms = MS (R_AN (if tw then NBD_MSG_TWOWB else NBD_MSG_INVALID) t0 t1 t2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s11 t3 t4 t5 t6) F' (Z_to_bv 64 PC_wrap_fprintf) fc' None m' (seg_rom asegs)
/\ frm0 fc' /\ nbA_ctx m' b' sws'
end.
Local Notation RA := (R_A usp ST A sf gp tp).

Lemma nbA_exit_m1 : forall (b : bits_st ptr) sws (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc m1,
nbA_ctx m1 b sws -> frm0 fc ->
evt asegs (nbA_post (SOret (-1) b)) (MS (RA xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa1a14) fc None m1 (seg_rom asegs)).
Proof.
intros b sws xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m1 CTX FRM.
pose proof CTX as (MU & WM & MI & ST0 & CC & REP & OKB & SZ & SW & LSW & FR & CBS & UCB & GOTE & VARE).
unfold R_A, nbd_frame_A in *. cbn [app] in FR.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof ST0 as (STa & STb & _).
ato 0xa1a1c.
apply evt_done. cbn [nbA_post]. do 20 eexists. split; [reflexivity|]. split; [exact FRM| exact CTX].
Qed.
Lemma nbA_offsh : offsh nbA_W.
Proof using LO LOS SPH ASH SESH.
clear - LO LOS SPH ASH SESH. unfold nbA_W, BITS_SIZEOF in *. pose proof (ASH : _ \/ _) as H1. pose proof (SESH : _ \/ _) as H2.
cbn. unfold SH_LO, SH_HI in *. lia.
Qed.

Lemma nbA_exit_n2 : forall (b : bits_st ptr) sws (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc m1,
nbA_ctx m1 b sws -> frm0 fc ->
evt asegs (nbA_post (SOnotify true b)) (MS (RA xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa1b94) fc None m1 (seg_rom asegs)).
Proof.
intros b sws xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m1 CTX FRM.
pose proof CTX as (MU & WM & MI & ST0 & CC & REP & OKB & SZ & SW & LSW & FR & CBS & UCB & GOTE & VARE).
pose proof nbA_offsh as OF.
pose proof (aobj_munch asegs _ m m1 _ _ OBV MU (shfree_of_aobj asegs _ m _ _ OF OBV)) as OBV1.
unfold R_A, nbd_frame_A, NBD_GOT_STDERR, NBD_STDERR_VAR in *. cbn [app] in FR.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof ST0 as (STa & STb & _).
pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
assert (V8 : 997264 mod 8 = 0) by reflexivity.
ato 0xa1bc8. astep.
apply evt_done. cbn [nbA_post]. do 21 eexists. split; [reflexivity|]. split; [exact FRM| exact CTX].
Qed.

Lemma nbA_exit_disp : forall (b : bits_st ptr) sws mv (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc m1,
nbA_ctx m1 b sws -> frm0 fc -> 0 <= mv < 16 ->
evt asegs (nbA_post (if mv =? 15 then SOret (-1) b else if 8 <? mv then SOnotify false b else SOmode mv b))
(MS (RA xra t0 t1 t2 (Z_to_bv 64 mv) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa19ac) fc None m1 (seg_rom asegs)).
Proof.
intros b sws mv xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m1 CTX FRM MV.
pose proof CTX as (MU & WM & MI & ST0 & CC & REP & OKB & SZ & SW & LSW & FR & CBS & UCB & GOTE & VARE).
pose proof nbA_offsh as OF.
pose proof (aobj_munch asegs _ m m1 _ _ OBV MU (shfree_of_aobj asegs _ m _ _ OF OBV)) as OBV1.
unfold R_A, nbd_frame_A, NBD_GOT_STDERR, NBD_STDERR_VAR in *. cbn [app] in FR.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof ST0 as (STa & STb & _).
pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
assert (V8 : 997264 mod 8 = 0) by reflexivity.
ato 0xa19b8. astep.
destruct (mv =? 15) eqn:K15; [apply Z.eqb_eq in K15 | apply Z.eqb_neq in K15].
- sh_if. apply evt_done. cbn [nbA_post]. do 20 eexists. split; [reflexivity|]. split; [exact FRM| exact CTX].
- sh_if. ato 0xa19d8. astep.
destruct (8 <? mv) eqn:K9; [apply Z.ltb_lt in K9 | apply Z.ltb_ge in K9].
+ sh_if. ato 0xa1a0c. astep. astep.
apply evt_done. cbn [nbA_post]. do 21 eexists. split; [reflexivity|]. split; [exact FRM| exact CTX].
+ sh_if. astep.
apply evt_done. cbn [nbA_post]. do 18 eexists. split; [reflexivity|]. split; [exact FRM|]. split; [exact CTX| lia].
Qed.
Ltac nbA_unf := unfold R_A, nbA_W, cb_cells, NBD_GOT_STDERR, NBD_STDERR_VAR, A_wb_skip_table, A_e_ratio_quant,
g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
Ltac nbA_close G1 G2 G3 G4 :=
unfold nbA_ctx, nbA_W, client_consts, cb_cells, NBD_GOT_STDERR, NBD_STDERR_VAR,
g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return;
refine (conj _ (conj _ (conj _ (conj _ (conj (conj G1 (conj G2 (conj G3 G4))) (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))))));
first [eassumption | lia | congruence].

Ltac slia1 := first [ lia | match goal with H : hidp (_ \/ _) |- _ => unfold hidp in H; lia end ].
Ltac slia_c := lazymatch goal with |- _ /\ _ => split; [slia1 | slia_c] | |- True => exact I | |- _ => slia1 end.
Local Ltac slia ::= (try unfold BITS_SIZEOF, USERH_DEPTH, INBAND_DEPTH in * ); slia_c.

Lemma nbA_back : forall fuel (b : bits_st ptr) sws (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc m1,
(forall (b' : bits_st ptr) sws' (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m2,
nbA_ctx m2 b' sws' -> frm0 fc' -> 5 <= speex_bits_remaining b' ->
evt asegs (nbA_post (search_pure fuel sc b')) (MS (RA xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F' (Z_to_bv 64 0x9fa50) fc' None m2 (seg_rom asegs))) ->
nbA_ctx m1 b sws -> frm0 fc ->
evt asegs (nbA_post (search_pure fuel sc b)) (MS (RA xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0x9fb88) fc None m1 (seg_rom asegs)).
Proof.
intros fuel b sws xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m1 IH CTX FRM.
pose proof CTX as (MU0 & WM0 & MI & ST0 & CC & REP & OKB & SZ & SW & LSW & FR & CBS & UCB & GOTE & VARE).
pose proof nbA_offsh as OF.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof ST0 as (STa & STb & _).
pose proof OBA as (OA0 & OA1 & _). unfold APP_TOP, BITS_SIZEOF in *.
pose proof ATOP as ATOP'. unfold IMG_TOP in ATOP'.
pose proof CC as (G1 & G2 & G3 & G4).
nbA_unf.
pose proof (aobj_munch asegs _ m m1 A 48 OBA MU0 (shfree_of_aobj asegs _ m A 48 OF OBA)) as OBA1.
assert (DLO' : D + sb_buf_size b <= lo) by (rewrite SZ; exact DLO).
assert (CC1 : client_consts m1) by (unfold client_consts, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4)))).
pose proof (munch_refl [(A, A + 48); (STEREO, STEREO + 8); (usp + -640, usp + -544)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
astep. astep.
call (speex_bits_remaining_walk A D (usp + -544) lo b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 REP OKB OBA1 ST0 ltac:(lia) LOS ltac:(lia) ALO DLO' CC1).
all: try eassumption.
match goal with H : ?x = Z_to_bv 64 (speex_bits_remaining b) |- _ => subst x end.
pose proof REP as (_ & _ & SIDE). pose proof (remaining_range A D b OKB SIDE) as RR. change (2^31) with 2147483648 in RR.
astep.
destruct (speex_bits_remaining b <? 5) eqn:K; [apply Z.ltb_lt in K | apply Z.ltb_ge in K].
- sh_if. astep.
destruct (search_pure_lt5 fuel sc b K) as [E|E]; rewrite E.
+ apply evt_done. exact I.
+ eapply nbA_exit_m1; [| exact FRM]. nbA_close G1 G2 G3 G4.
- sh_if. eapply IH; [| exact FRM | exact K]. nbA_close G1 G2 G3 G4.
Qed.
Lemma nbA_tail : forall fuel (b : bits_st ptr) sws (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc m1,
(forall (b' : bits_st ptr) sws' (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m2,
nbA_ctx m2 b' sws' -> frm0 fc' -> 5 <= speex_bits_remaining b' ->
evt asegs (nbA_post (search_pure fuel sc b')) (MS (RA xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F' (Z_to_bv 64 0x9fa50) fc' None m2 (seg_rom asegs))) ->
nbA_ctx m1 b sws -> frm0 fc ->
evt asegs (nbA_post (search_tail fuel sc b)) (MS (RA xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0x9fafc) fc None m1 (seg_rom asegs)).
Proof.
intros fuel b sws xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m1 IH CTX FRM.
pose proof CTX as (MU0 & WM0 & MI & ST0 & CC & REP & OKB & SZ & SW & LSW & FR & CBS & UCB & GOTE & VARE).
pose proof nbA_offsh as OF.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof ST0 as (STa & STb & _).
pose proof OBA as (OA0 & OA1 & _). unfold APP_TOP, BITS_SIZEOF in *.
pose proof ATOP as ATOP'. unfold IMG_TOP in ATOP'. pose proof SETOP as SETOP'. unfold IMG_TOP in SETOP'.
pose proof CC as (G1 & G2 & G3 & G4).
nbA_unf.
pose proof (aobj_munch asegs _ m m1 A 48 OBA MU0 (shfree_of_aobj asegs _ m A 48 OF OBA)) as OBA1.
assert (OBD' : aobj asegs m D (sb_buf_size b)) by (rewrite SZ; exact OBD).
pose proof (aobj_munch asegs _ m m1 D _ OBD' MU0 (shfree_of_aobj asegs _ m D _ OF OBD')) as OBD1.
assert (DLO' : D + sb_buf_size b <= lo) by (rewrite SZ; exact DLO).
assert (CC1 : client_consts m1) by (unfold client_consts, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4)))).
pose proof (munch_refl [(A, A + 48); (STEREO, STEREO + 8); (usp + -640, usp + -544)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
astep. astep.
call (speex_bits_remaining_walk A D (usp + -544) lo b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 REP OKB OBA1 ST0 ltac:(lia) LOS ltac:(lia) ALO DLO' CC1).
all: try eassumption.
match goal with H : ?x = Z_to_bv 64 (speex_bits_remaining b) |- _ => subst x end.
pose proof REP as (_ & _ & SIDE). pose proof (remaining_range A D b OKB SIDE) as RR. change (2^31) with 2147483648 in RR.
ato 0x9fb08. astep. unfold search_tail.
destruct (speex_bits_remaining b <? 4) eqn:K4; [apply Z.ltb_lt in K4 | apply Z.ltb_ge in K4].
{ sh_if. astep.
eapply nbA_exit_m1; [| exact FRM].
nbA_close G1 G2 G3 G4. }
sh_if.
clear OBA1 OBD1 REP. rename POST into REP.
lazymatch goal with MU0 : munch ?W m ?mc |- _ =>
pose proof (aobj_munch asegs W m mc _ _ OBA MU0 (shfree_of_aobj asegs W m _ _ OF OBA)) as OBA1;
pose proof (aobj_munch asegs W m mc _ _ OBD' MU0 (shfree_of_aobj asegs W m _ _ OF OBD')) as OBD1 end.
ato 0x9fb18. astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -544) lo b 4 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP OKB ltac:(lia) OBA1 OBD1 ASH ltac:(lia) LOS ltac:(lia) ALO DLO').
all: try eassumption.
{ unfold client_consts, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))). }
match goal with H : ?x = Z_to_bv 64 (fst (speex_bits_unpack_unsigned b 4)) |- _ => subst x end. set (mv := fst (speex_bits_unpack_unsigned b 4)) in *. set (b1 := snd (speex_bits_unpack_unsigned b 4)) in *.
assert (UE : speex_bits_unpack_unsigned b 4 = (mv, b1)) by (unfold mv, b1; destruct (speex_bits_unpack_unsigned b 4); reflexivity).
pose proof (speex_bits_unpack_unsigned_ok b 4 mv b1 OKB ltac:(lia) UE) as (OK1 & VR & _ & _ & SZ1 & _). change (2^4) with 16 in VR.
change (uv b 4) with mv. change (ub b 4) with b1.
clear OBA1 OBD1 REP. rename POST into REP.
assert (SZ1' : sb_buf_size b1 = BSZ) by congruence.
assert (DLO1 : D + sb_buf_size b1 <= lo) by (rewrite SZ1; exact DLO').
lazymatch goal with MU0 : munch ?W m ?mc |- _ =>
pose proof (aobj_munch asegs W m mc _ _ OBA MU0 (shfree_of_aobj asegs W m _ _ OF OBA)) as OBA1;
pose proof (aobj_munch asegs W m mc _ _ OBD' MU0 (shfree_of_aobj asegs W m _ _ OF OBD')) as OBD1;
pose proof (aobj_munch asegs W m mc _ _ OBST MU0 (shfree_of_aobj asegs W m _ _ OF OBST)) as OBST1;
pose proof (aobj_munch asegs W m mc _ _ OBSE MU0 (shfree_of_aobj asegs W m _ _ OF OBSE)) as OBSE1;
pose proof (aobj_munch asegs W m mc _ _ OBE MU0 (shfree_of_aobj asegs W m _ _ OF OBE)) as OBE1 end.
rewrite <- SZ1 in OBD1.
unfold nbd_frame_A in FR. cbn [app] in FR.
pose proof SB as (SB0 & SB1).
ato 0x9fb20. astep.
destruct (mv =? 13) eqn:K13; [apply Z.eqb_eq in K13 | apply Z.eqb_neq in K13]; sh_if.
{
replace (mv =? 15) with false by (symmetry; apply Z.eqb_neq; lia).
replace (mv =? 14) with false by (symmetry; apply Z.eqb_neq; lia).
ato 0x9fb7c. astep.
replace (ret_pc (Z_to_bv 64 A_speex_default_user_handler)) with (Z_to_bv 64 A_speex_default_user_handler)
by (unfold A_speex_default_user_handler; symmetry; apply ret_pc_even; [lia| reflexivity]).
call (user_handler_proofA ptr A D ST (usp + -544) lo b1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP OK1 OBA1 OBD1 ASH ATOP ALO DLO1).
all: try eassumption. all: try (unfold USERH_DEPTH; lia).
{ unfold client_consts, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))). }
replace (ret_pc (Z_to_bv 64 654208)) with (Z_to_bv 64 654208) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (adv_size (ub b1 4) (5 + 8 * uv b1 4)) as SZ2. rewrite ub_size in SZ2. fold (user_handler_bits b1) in SZ2.
ato 0x9fb88.
eapply nbA_back; [exact IH | | eassumption].
nbA_close G1 G2 G3 G4. }
ato 0x9fb28. astep.
destruct (mv =? 14) eqn:K14; [apply Z.eqb_eq in K14 | apply Z.eqb_neq in K14]; sh_if.
2: { astep. eapply nbA_exit_disp; [| exact FRM | exact VR]. nbA_close G1 G2 G3 G4. }
replace (mv =? 15) with false by (symmetry; apply Z.eqb_neq; lia).

ato 0x9fb40. astep.
assert (CBH : rw_cells asegs x20 (ST + 2256) (cbs_cells 16 A_speex_std_stereo_request_handler STEREO sc js)).
{ eapply rw_cells_recast; [exact CBS | apply cbs_cells_wf; exact FJS | cbn [cells_bytes cbytes]; rewrite app_nil_r; symmetry; exact ECBS]. }
pose proof (aobj_sub asegs x20 ST 2968 (ST + 2256) 640 OBST1 ltac:(lia) ltac:(lia)) as OBC1.
assert (AP1 : hidp (ST + 2256 + 640 <= A \/ A + BITS_SIZEOF <= ST + 2256)) by (clear - AP_ST_A; unfold hidp, BITS_SIZEOF in *; lia).
assert (AP2 : hidp (ST + 2256 + 640 <= STEREO \/ STEREO + 8 <= ST + 2256)) by (clear - AP_ST_SE; unfold hidp in *; lia).
assert (AP3 : hidp (STEREO + 8 <= D \/ D + sb_buf_size b1 <= STEREO)) by (rewrite SZ1'; exact AP_SE_D).
assert (CA8 : (ST + 2256) mod 8 = 0) by (clear - ST8; Z.div_mod_to_equations; lia).
callc (inband_handler_proofA ptr sc A D (ST + 2256) ST STEREO (usp + -544) lo b1 js sws _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
REP OK1 CBH LJS FJS SW LSW OBA1 OBD1 OBC1 OBSE1 OBE1 CA8 SE4 ASH SESH ATOP SETOP ALO DLO1 ltac:(lia) SELO AP1 AP2 AP_SE_A AP3) (clear CBH).
all: try eassumption. all: try (unfold INBAND_DEPTH; lia).
all: try eassumption. all: try (unfold INBAND_DEPTH; lia).
{ unfold client_consts, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))). }
replace (ret_pc (Z_to_bv 64 654148)) with (Z_to_bv 64 654148) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
assert (SZ2 : sb_buf_size (inband_bits sc b1) = sb_buf_size b1).
{ unfold inband_bits, stereo_handler_bits. destruct (_ && _); rewrite ?adv_size, ?ub_size; reflexivity. }
ato 0x9fb88.
eapply nbA_back; [exact IH | | eassumption].
nbA_close G1 G2 G3 G4.
Qed.
Lemma nbA_head : forall fuel (b : bits_st ptr) sws (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc m1,
(forall (b' : bits_st ptr) sws' (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' m2,
nbA_ctx m2 b' sws' -> frm0 fc' ->
evt asegs (nbA_post (search_tail fuel sc b')) (MS (RA xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F' (Z_to_bv 64 0x9fafc) fc' None m2 (seg_rom asegs))) ->
nbA_ctx m1 b sws -> frm0 fc -> 5 <= speex_bits_remaining b ->
evt asegs (nbA_post (match search_head b with inr o => o | inl bm => search_tail fuel sc bm end))
(MS (RA xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0x9fa50) fc None m1 (seg_rom asegs)).
Proof.
intros fuel b sws xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m1 TL CTX FRM REM.
pose proof CTX as (MU0 & WM0 & MI & ST0 & CC & REP & OKB & SZ & SW & LSW & FR & CBS & UCB & GOTE & VARE).
pose proof nbA_offsh as OF.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof ST0 as (STa & STb & _).
pose proof OBA as (OA0 & OA1 & _). unfold APP_TOP, BITS_SIZEOF in *.
pose proof ATOP as ATOP'. unfold IMG_TOP in ATOP'. pose proof SETOP as SETOP'. unfold IMG_TOP in SETOP'.
pose proof CC as (G1 & G2 & G3 & G4).
nbA_unf.
assert (OBD' : aobj asegs m D (sb_buf_size b)) by (rewrite SZ; exact OBD).
assert (DLO' : D + sb_buf_size b <= lo) by (rewrite SZ; exact DLO).
pose proof (aobj_munch asegs _ m m1 A 48 OBA MU0 (shfree_of_aobj asegs _ m A 48 OF OBA)) as OBA1.
pose proof (aobj_munch asegs _ m m1 D _ OBD' MU0 (shfree_of_aobj asegs _ m D _ OF OBD')) as OBD1.
assert (CC1 : client_consts m1) by (unfold client_consts, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4)))).
pose proof (munch_refl [(A, A + 48); (STEREO, STEREO + 8); (usp + -640, usp + -544)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
ato 0x9fa58. astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -544) lo b 1 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP OKB ltac:(lia) OBA1 OBD1 ASH ltac:(lia) LOS ltac:(lia) ALO DLO').
all: try eassumption.
match goal with H : ?x = Z_to_bv 64 (fst (speex_bits_unpack_unsigned b 1)) |- _ => subst x end. set (w1 := fst (speex_bits_unpack_unsigned b 1)) in *. set (b1 := snd (speex_bits_unpack_unsigned b 1)) in *.
assert (UE : speex_bits_unpack_unsigned b 1 = (w1, b1)) by (unfold w1, b1; destruct (speex_bits_unpack_unsigned b 1); reflexivity).
pose proof (speex_bits_unpack_unsigned_ok b 1 w1 b1 OKB ltac:(lia) UE) as (OK1 & VR & _ & _ & SZ1 & _). change (2^1) with 2 in VR.
pose proof (ub_exact b 1 OKB ltac:(lia) ltac:(lia)) as (_ & POS1 & _ & REM1). unfold ub in POS1, REM1. fold b1 in POS1, REM1.
unfold search_head. change (uv b 1) with w1. change (ub b 1) with b1. cbv zeta.
clear OBA1 OBD1 REP. rename POST into REP.
assert (SZ1' : sb_buf_size b1 = BSZ) by congruence.
astep.
destruct (w1 =? 0) eqn:K1; [apply Z.eqb_eq in K1 | apply Z.eqb_neq in K1]; sh_if; cbn [negb].
{ eapply TL; [| exact FRM]. nbA_close G1 G2 G3 G4. }
pose proof REP as (_ & _ & SIDE0).
assert (POS0 : 0 <= bits_pos b).
{ pose proof CTX as (_ & _ & _ & _ & _ & (_ & _ & SIDEb) & _). pose proof (bits_ints A D b OKB SIDEb) as (In & Ic & Ib & Io & Iv & Is & Rc & Rb & Rp & Rn & Rs & R1 & Rov).
unfold bits_pos, int31 in *. lia. }
assert (OFS : offsh [(A, A + 48); (usp + -640, usp + -544)]).
{ clear - LO LOS SPH ASH. pose proof (ASH : _ \/ _) as H1. cbn. unfold SH_LO, SH_HI in *. lia. }
lazymatch goal with MU0 : munch ?W m ?mc |- _ =>
pose proof (aobj_munch asegs W m mc _ _ OBA MU0 (shfree_of_aobj asegs W m _ _ OF OBA)) as OBA1;
pose proof (aobj_munch asegs W m mc _ _ OBD' MU0 (shfree_of_aobj asegs W m _ _ OF OBD')) as OBD1;
pose proof (aobj_munch asegs W m mc _ _ OBT MU0 (shfree_of_aobj asegs W m _ _ OF OBT)) as OBT1 end.
rewrite <- SZ1 in OBD1.
assert (DLO1 : D + sb_buf_size b1 <= lo) by (rewrite SZ1; exact DLO').
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
call (nbA_skip1 usp lo ST A D sf gp tp mc LO LOS SPH OBA1 OBT1 ALO ASH ATOP b1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mc REP OK1 OBD1 DLO1 ltac:(lia) ltac:(lia)
(munch_refl _ mc) OFS (wmono_refl asegs mc)) end.
all: try eassumption.
{ unfold client_consts, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))). }
unfold R_A.
clear OBA1 OBD1 OBT1 REP POST. rename PC0 into REP. rename PC1 into OK2. rename PC2 into SZ2. rename PC into ST1.
set (b2 := skip_bits b1) in *.
assert (SZ2' : sb_buf_size b2 = BSZ) by congruence.
assert (DLO2 : D + sb_buf_size b2 <= lo) by (rewrite SZ2'; exact DLO).
assert (OBD2' : aobj asegs m D (sb_buf_size b2)) by (rewrite SZ2'; exact OBD).
lazymatch goal with MU0 : munch ?W m ?mc |- _ =>
pose proof (aobj_munch asegs W m mc _ _ OBA MU0 (shfree_of_aobj asegs W m _ _ OF OBA)) as OBA1 end.
ato 0x9fa98. astep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
call (speex_bits_remaining_walk A D (usp + -544) lo b2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc REP OK2 OBA1 ST1 ltac:(lia) LOS ltac:(lia) ALO DLO2) end.
all: try eassumption.
{ unfold client_consts, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))). }
match goal with H : ?x = Z_to_bv 64 (speex_bits_remaining b2) |- _ => subst x end.
pose proof REP as (_ & _ & SIDE2). pose proof (remaining_range A D b2 OK2 SIDE2) as RR2. change (2^31) with 2147483648 in RR2.
clear OBA1 REP. rename POST into REP.
astep.
destruct (speex_bits_remaining b2 <? 5) eqn:K2; [apply Z.ltb_lt in K2 | apply Z.ltb_ge in K2]; sh_if.
{ astep. eapply nbA_exit_m1; [| exact FRM]. nbA_close G1 G2 G3 G4. }
lazymatch goal with MU0 : munch ?W m ?mc |- _ =>
pose proof (aobj_munch asegs W m mc _ _ OBA MU0 (shfree_of_aobj asegs W m _ _ OF OBA)) as OBA1;
pose proof (aobj_munch asegs W m mc _ _ OBD2' MU0 (shfree_of_aobj asegs W m _ _ OF OBD2')) as OBD1 end.
ato 0x9faac. astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -544) lo b2 1 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP OK2 ltac:(lia) OBA1 OBD1 ASH ltac:(lia) LOS ltac:(lia) ALO DLO2).
all: try eassumption.
{ unfold client_consts, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))). }
match goal with H : ?x = Z_to_bv 64 (fst (speex_bits_unpack_unsigned b2 1)) |- _ => subst x end. set (w2 := fst (speex_bits_unpack_unsigned b2 1)) in *. set (b3 := snd (speex_bits_unpack_unsigned b2 1)) in *.
assert (UE2 : speex_bits_unpack_unsigned b2 1 = (w2, b3)) by (unfold w2, b3; destruct (speex_bits_unpack_unsigned b2 1); reflexivity).
pose proof (speex_bits_unpack_unsigned_ok b2 1 w2 b3 OK2 ltac:(lia) UE2) as (OK3 & VR2 & _ & _ & SZ3 & _). change (2^1) with 2 in VR2.
pose proof (ub_exact b2 1 OK2 ltac:(lia) ltac:(lia)) as (_ & POS3 & _ & REM3). unfold ub in POS3, REM3. fold b3 in POS3, REM3.
change (uv b2 1) with w2. change (ub b2 1) with b3.
clear OBA1 OBD1 REP. rename POST into REP.
assert (SZ3' : sb_buf_size b3 = BSZ) by congruence.
astep.
destruct (w2 =? 0) eqn:K3; [apply Z.eqb_eq in K3 | apply Z.eqb_neq in K3]; sh_if; cbn [negb].
{ eapply TL; [| exact FRM]. nbA_close G1 G2 G3 G4. }
assert (POS2 : 0 <= bits_pos b2).
{ pose proof (bits_ints A D b2 OK2 SIDE2) as (In & Ic & Ib & Io & Iv & Is & Rc & Rb & Rp & Rn & Rs & R1 & Rov). unfold bits_pos, int31 in *. lia. }
assert (DLO3 : D + sb_buf_size b3 <= lo) by (rewrite SZ3'; exact DLO).
assert (OBD3' : aobj asegs m D (sb_buf_size b3)) by (rewrite SZ3'; exact OBD).
lazymatch goal with MU0 : munch ?W m ?mc |- _ =>
pose proof (aobj_munch asegs W m mc _ _ OBA MU0 (shfree_of_aobj asegs W m _ _ OF OBA)) as OBA1;
pose proof (aobj_munch asegs W m mc _ _ OBD3' MU0 (shfree_of_aobj asegs W m _ _ OF OBD3')) as OBD1;
pose proof (aobj_munch asegs W m mc _ _ OBT MU0 (shfree_of_aobj asegs W m _ _ OF OBT)) as OBT1 end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
call (nbA_skip2 usp lo ST A D sf gp tp mc LO LOS SPH OBA1 OBT1 ALO ASH ATOP b3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mc REP OK3 OBD1 DLO3 ltac:(lia) ltac:(lia)
(munch_refl _ mc) OFS (wmono_refl asegs mc)) end.
all: try eassumption.
{ unfold client_consts, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))). }
unfold R_A.
clear OBA1 OBD1 OBT1 REP POST. rename PC0 into REP. rename PC1 into OK4. rename PC2 into SZ4. rename PC into ST2.
set (b4 := skip_bits b3) in *.
assert (SZ4' : sb_buf_size b4 = BSZ) by congruence.
assert (DLO4 : D + sb_buf_size b4 <= lo) by (rewrite SZ4'; exact DLO).
assert (OBD4' : aobj asegs m D (sb_buf_size b4)) by (rewrite SZ4'; exact OBD).
lazymatch goal with MU0 : munch ?W m ?mc |- _ =>
pose proof (aobj_munch asegs W m mc _ _ OBA MU0 (shfree_of_aobj asegs W m _ _ OF OBA)) as OBA1;
pose proof (aobj_munch asegs W m mc _ _ OBD4' MU0 (shfree_of_aobj asegs W m _ _ OF OBD4')) as OBD1 end.
ato 0x9faf0. astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -544) lo b4 1 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP OK4 ltac:(lia) OBA1 OBD1 ASH ltac:(lia) LOS ltac:(lia) ALO DLO4).
all: try eassumption.
{ unfold client_consts, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))). }
match goal with H : ?x = Z_to_bv 64 (fst (speex_bits_unpack_unsigned b4 1)) |- _ => subst x end.
set (w3 := fst (speex_bits_unpack_unsigned b4 1)) in *. set (b5 := snd (speex_bits_unpack_unsigned b4 1)) in *.
assert (UE4 : speex_bits_unpack_unsigned b4 1 = (w3, b5)) by (unfold w3, b5; destruct (speex_bits_unpack_unsigned b4 1); reflexivity).
pose proof (speex_bits_unpack_unsigned_ok b4 1 w3 b5 OK4 ltac:(lia) UE4) as (OK5 & VR4 & _ & _ & SZ5 & _). change (2^1) with 2 in VR4.
change (uv b4 1) with w3. change (ub b4 1) with b5.
clear OBA1 OBD1 REP. rename POST into REP.
assert (SZ5' : sb_buf_size b5 = BSZ) by congruence.
astep.
destruct (w3 =? 0) eqn:K5; [apply Z.eqb_eq in K5 | apply Z.eqb_neq in K5]; sh_if; cbn [negb].
{ eapply TL; [| exact FRM]. nbA_close G1 G2 G3 G4. }
astep. eapply nbA_exit_n2; [| exact FRM]. nbA_close G1 G2 G3 G4.
Qed.

Theorem nbA_loop : forall fuel (b : bits_st ptr) sws (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc m1,
nbA_ctx m1 b sws -> frm0 fc -> 5 <= speex_bits_remaining b ->
evt asegs (nbA_post (search_pure fuel sc b)) (MS (RA xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0x9fa50) fc None m1 (seg_rom asegs)).
Proof.
induction fuel as [|fuel IH]; intros b sws xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m1 CTX FRM REM.
- apply evt_done. exact I.
- rewrite search_pure_S. replace (speex_bits_remaining b <? 5) with false by (symmetry; apply Z.ltb_ge; exact REM).
eapply nbA_head; [| exact CTX | exact FRM | exact REM].
intros b' sws' xra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m2 CTX' FRM'.
eapply nbA_tail; [| exact CTX' | exact FRM'].
intros b'' sws'' xra'' t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F'' fc'' m3 CTX'' FRM'' REM''.
eapply IH; eassumption.
Qed.
End Loop.
