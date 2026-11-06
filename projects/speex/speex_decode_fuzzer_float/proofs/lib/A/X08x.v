(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X081 X05l X09f X069 X09e X082 X08y X091.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).

Definition NBD_FRAME : Z := 544.
Definition NBD_FSIZE : Z := 1088.
Definition NBD_FCLASS : nat := 5.
Definition PC_NBD_E : Z := 0xa0420.
Definition PC_NBD_X : Z := 0xa1a1c.
Definition O_pitch : Z := 32.   Definition O_pitch_gain : Z := 48.  Definition O_lpc : Z := 80.    Definition O_qlsp : Z := 160.  Definition O_ak : Z := 240.
Definition O_innov : Z := 320.  Definition O_exc32 : Z := 544.      Definition O_innov2 : Z := 768. Definition O_iqlsp : Z := 992.

Record smrec := SMR {
smr_sm : submode;
smr_ptr : Z;
smr_lsp_quant : Z; smr_ltp_quant : Z; smr_innov_quant : Z;
smr_ltp_par : Z;
smr_innov_par : Z;
smr_comb_gain : Z }.
Definition smrec_cells (r : smrec) : list cell :=
let sm := smr_sm r in
[C4 (Z_to_bv 64 (sm_lbr_pitch sm)); C4 (Z_to_bv 64 (sm_forced_pitch_gain sm));
C4 (Z_to_bv 64 (sm_have_subframe_gain sm)); C4 (Z_to_bv 64 (sm_double_codebook sm));
C8 (Z_to_bv 64 (smr_lsp_quant r)); C8 (Z_to_bv 64 (lsp_entryA (sm_lsp_unquant sm)));
C8 (Z_to_bv 64 (smr_ltp_quant r));
C8 (Z_to_bv 64 (match sm_ltp_unquant sm with Some k => ltp_entryA k | None => 0 end));
C8 (Z_to_bv 64 (smr_ltp_par r));
C8 (Z_to_bv 64 (smr_innov_quant r));
C8 (Z_to_bv 64 (match sm_innovation_unquant sm with Some k => innov_entryA k | None => 0 end));
C8 (Z_to_bv 64 (smr_innov_par r));
C4 (Z_to_bv 64 (smr_comb_gain r)); C4 (Z_to_bv 64 (sm_bits_per_frame sm))].
Definition nb_smrec1 := SMR nb_submode1 A_nb_submode1 0xae0a0 0xa8564 0xacad0 0       0       0xbf800000.
Definition nb_smrec2 := SMR nb_submode2 A_nb_submode2 0xae0a0 0xa6be8 0xa9ed4 A_ltp_params_vlbr A_split_cb_nb_vlbr 0x3f19999a.
Definition nb_smrec3 := SMR nb_submode3 A_nb_submode3 0xae0a0 0xa6be8 0xa9ed4 A_ltp_params_lbr  A_split_cb_nb_lbr  0x3f0ccccd.
Definition nb_smrec4 := SMR nb_submode4 A_nb_submode4 0xae0a0 0xa6be8 0xa9ed4 A_ltp_params_med  A_split_cb_nb_med  0x3ee66666.
Definition nb_smrec5 := SMR nb_submode5 A_nb_submode5 0xacf0c 0xa6be8 0xa9ed4 A_ltp_params_nb   A_split_cb_nb      0x3e800000.
Definition nb_smrec6 := SMR nb_submode6 A_nb_submode6 0xacf0c 0xa6be8 0xa9ed4 A_ltp_params_nb   A_split_cb_sb      0x3e19999a.
Definition nb_smrec7 := SMR nb_submode7 A_nb_submode7 0xacf0c 0xa6be8 0xa9ed4 A_ltp_params_nb   A_split_cb_nb      0x3d4ccccd.
Definition nb_smrec8 := SMR nb_submode8 A_nb_submode8 0xae0a0 0xa8564 0xa9ed4 0       A_split_cb_nb_ulbr 0x3f000000.
Definition nb_smrecs : list smrec := [nb_smrec1; nb_smrec2; nb_smrec3; nb_smrec4; nb_smrec5; nb_smrec6; nb_smrec7; nb_smrec8].
Definition smrec_at (m : Z) : option smrec := if m <? 1 then None else nth_error nb_smrecs (Z.to_nat (m - 1)).

Record nbslots := NBS { v0 : word; v8 : word; v16 : word; v24 : word; v32 : word; v40 : word; v48 : word; v56 : word; v64 : word; v72 : word; v80 : word; v88 : word; v96 : word; v104 : word; v112 : word; v120 : word; v128 : word; v136 : word; v144 : word; v152 : word; v160 : word; v168 : word; v176 : word; v184 : word; v192 : word; v200 : word; v208 : word; v216 : word; v224 : word; v232 : word; v240 : word; v248 : word; v256 : word; v264 : word; v272 : word; v280 : word; v288 : word; v296 : word; v304 : word; v312 : word; v320 : word; v328 : word; v336 : word }.
Definition slot_cells (s : nbslots) : list cell :=
[C8 (v0 s); C8 (v8 s); C8 (v16 s); C8 (v24 s); C8 (v32 s); C8 (v40 s); C8 (v48 s); C8 (v56 s); C8 (v64 s); C8 (v72 s); C8 (v80 s); C8 (v88 s); C8 (v96 s); C8 (v104 s); C8 (v112 s); C8 (v120 s); C8 (v128 s); C8 (v136 s); C8 (v144 s); C8 (v152 s); C8 (v160 s); C8 (v168 s); C8 (v176 s); C8 (v184 s); C8 (v192 s); C8 (v200 s); C8 (v208 s); C8 (v216 s); C8 (v224 s); C8 (v232 s); C8 (v240 s); C8 (v248 s); C8 (v256 s); C8 (v264 s); C8 (v272 s); C8 (v280 s); C8 (v288 s); C8 (v296 s); C8 (v304 s); C8 (v312 s); C8 (v320 s); C8 (v328 s); C8 (v336 s)].

Definition slots_E (ST OUT A FF : Z) (s : nbslots) : Prop :=
v0 s = Z_to_bv 64 (3)
/\ v8 s = Z_to_bv 64 (ST + 8)
/\ v16 s = Z_to_bv 64 (ST)
/\ v24 s = Z_to_bv 64 (FF)
/\ v32 s = Z_to_bv 64 (FF)
/\ v40 s = Z_to_bv 64 (ST + 2047)
/\ v48 s = Z_to_bv 64 (ST + 2120)
/\ v56 s = Z_to_bv 64 (ST + 2948)
/\ v64 s = Z_to_bv 64 (0xfce8)
/\ v80 s = Z_to_bv 64 (FF + 992)
/\ v88 s = Z_to_bv 64 (FF + 48)
/\ v96 s = Z_to_bv 64 (ST + 2208)
/\ v104 s = Z_to_bv 64 (Z.shiftr (ST + 2184) 3 + SHB)
/\ v112 s = Z_to_bv 64 (FF + 240)
/\ v120 s = Z_to_bv 64 (ST + 2184)
/\ v128 s = Z_to_bv 64 (ST + 12)
/\ v136 s = Z_to_bv 64 (ST + 2032)
/\ v144 s = Z_to_bv 64 (Z.shiftr (ST + 12) 3 + SHB)
/\ v152 s = Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB)
/\ v160 s = Z_to_bv 64 (FF + 160)
/\ v168 s = Z_to_bv 64 (OUT)
/\ v176 s = Z_to_bv 64 (FF + 768)
/\ v184 s = Z_to_bv 64 (ST + 2228)
/\ v192 s = Z_to_bv 64 (40)
/\ v224 s = Z_to_bv 64 (FF + 544)
/\ v240 s = Z_to_bv 64 (0)
/\ v248 s = Z_to_bv 64 (FF + 32)
/\ v256 s = Z_to_bv 64 (A)
/\ v264 s = Z_to_bv 64 (0)
/\ v272 s = Z_to_bv 64 (0)
/\ v280 s = Z_to_bv 64 (FF + 320)
/\ v288 s = Z_to_bv 64 (ST + 2248)
/\ v296 s = Z_to_bv 64 (Z.shiftr (ST + 2240) 3 + SHB)
/\ v304 s = Z_to_bv 64 (ST + 2240)
/\ v312 s = Z_to_bv 64 (Z.shiftr (ST + 2248) 3 + SHB)
/\ v336 s = Z_to_bv 64 (FF).

Record nbff := NBF { f_pitch : word; f_pg : list word; f_lpc : list word; f_qlsp : list word; f_ak : list word;
f_innov : list word; f_exc32 : list word; f_innov2 : list word; f_iq : list word }.
Definition ff_ok (ff : nbff) : Prop :=
length (f_pg ff) = 3%nat /\ length (f_lpc ff) = 10%nat /\ length (f_qlsp ff) = 10%nat /\ length (f_ak ff) = 10%nat /\
length (f_innov ff) = 40%nat /\ length (f_exc32 ff) = 40%nat /\ length (f_innov2 ff) = 40%nat /\ length (f_iq ff) = 10%nat.
Definition fframe_at (m : mem) (FF : Z) (ff : nbff) : Prop :=
rw_cells asegs m FF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x20595); C8 (Z_to_bv 64 0x9f634)]
/\ rw_cells asegs m (FF + 32) [C4 (f_pitch ff)]
/\ rw_cells asegs m (FF + 48) (f32 (f_pg ff))
/\ rw_cells asegs m (FF + 80) (f32 (f_lpc ff))
/\ rw_cells asegs m (FF + 160) (f32 (f_qlsp ff))
/\ rw_cells asegs m (FF + 240) (f32 (f_ak ff))
/\ rw_cells asegs m (FF + 320) (f32 (f_innov ff))
/\ rw_cells asegs m (FF + 544) (f32 (f_exc32 ff))
/\ rw_cells asegs m (FF + 768) (f32 (f_innov2 ff))
/\ rw_cells asegs m (FF + 992) (f32 (f_iq ff)).

Definition bF1 : byte := Z_to_bv 8 (-15).  Definition bF2 : byte := Z_to_bv 8 (-14).  Definition bF3 : byte := Z_to_bv 8 (-13).
Definition bF8 : byte := Z_to_bv 8 (-8).   Definition b04 : byte := Z_to_bv 8 4.
Record nbscope := NBSC { sc_top : bool  ; sc_lpc : bool; sc_main : bool  ; sc_innov2 : bool; sc_iq : bool }.
Definition sh_run (on : bool) (n : nat) : list byte := repeat (if on then z8 else bF8) n.
Definition nbd_shadow_bytes (s : nbscope) : list byte :=
repeat bF1 4 ++ [if sc_top s then b04 else bF8] ++ [bF2] ++ (if sc_top s then [z8; b04] else [bF8; bF8]) ++ repeat bF2 2
++ sh_run (sc_lpc s) 5 ++ repeat bF2 5 ++ sh_run (sc_main s) 5 ++ repeat bF2 5 ++ sh_run (sc_main s) 5 ++ repeat bF2 5
++ sh_run (sc_main s) 20 ++ repeat bF2 8 ++ sh_run (sc_main s) 20 ++ repeat bF2 8 ++ sh_run (sc_innov2 s) 20 ++ repeat bF2 8
++ sh_run (sc_iq s) 5 ++ repeat bF3 7.
Definition nbd_shadow (s : nbscope) (rest : list byte) : list cell := map C1 (nbd_shadow_bytes s) ++ [CB 120 rest].
Lemma nbd_shadow_bytes_len : forall s, length (nbd_shadow_bytes s) = 136%nat.
Proof. intros [[] [] [] [] []]; reflexivity. Qed.
Definition SC_E : nbscope := NBSC true false true false false.
Definition SC_X : nbscope := NBSC true false false false false.

Section Cuts.
Context {ptr : Type}.
Record nbinvA := NBX {
x_st : Z; x_out : Z; x_nout : nat; x_A : Z; x_D : Z; x_dsz : Z; x_stereo : Z; x_lo : Z; x_usp : Z;
x_ff : Z; x_sf : Z;
x_gp : word; x_tp : word; x_ra : word; x_s0 : word; x_s1 : word; x_s2 : word; x_s3 : word; x_s4 : word; x_s5 : word; x_s6 : word;
x_s7 : word; x_s8 : word; x_s9 : word; x_s10 : word; x_s11 : word; x_F : bvmap 5 word;
x_m0 : mem; x_st0 : nb_state ptr; x_b0 : bits_st ptr }.
Variable X : nbinvA.
Local Notation ST := (x_st X). Local Notation OUT := (x_out X). Local Notation A := (x_A X). Local Notation D := (x_D X).
Local Notation STEREO := (x_stereo X). Local Notation lo := (x_lo X). Local Notation usp := (x_usp X).
Local Notation FF := (x_ff X). Local Notation SF := (x_sf X).
Local Notation NBP := (nb_pieces asegs A_speex_nb_mode NB_SUBMODES_PTR A_speex_default_user_handler).

Definition nbx_ok : Prop :=
usp mod 32 = 0 /\ usp < 2^63 /\ SH_HI <= lo /\ lo <= usp - NBD_FRAME
/\ 0 < FF /\ FF mod 64 = 0 /\ SF = Z.shiftr FF 3 + SHB /\ FF + 2048 <= lo /\ IMG_TOP <= FF /\ hidp (FF + 2048 <= SH_LO \/ SH_HI <= FF)
/\ SH_LO <= SF /\ SF + 256 <= SH_HI /\ SF + 256 <= lo
/\ ST mod 8 = 0 /\ 0 < ST /\ ST + NBSTATE_SIZEOF <= lo /\ hidp (ST + NBSTATE_SIZEOF <= SH_LO \/ SH_HI <= ST) /\ hidp (ST + NBSTATE_SIZEOF <= 0x10000 \/ IMG_TOP <= ST)
/\ OUT mod 4 = 0 /\ IMG_TOP <= OUT /\ OUT + 4 * Z.of_nat (x_nout X) <= lo /\ (160 <= x_nout X)%nat /\ hidp (OUT + 4 * Z.of_nat (x_nout X) <= SH_LO \/ SH_HI <= OUT)
/\ A mod 8 = 0 /\ IMG_TOP <= A /\ A + BITS_SIZEOF <= lo /\ hidp (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A)
/\ 0 < D /\ D + x_dsz X <= lo /\ x_dsz X = sb_buf_size (x_b0 X)
/\ STEREO mod 4 = 0 /\ IMG_TOP <= STEREO /\ STEREO + 8 <= lo /\ hidp (STEREO + 8 <= SH_LO \/ SH_HI <= STEREO)
/\ match nb_innov_save (x_st0 X) with Some k => k + 160 <= Z.of_nat (x_nout X) | None => True end
/\ hidp (ST + NBSTATE_SIZEOF <= OUT \/ OUT + 4 * Z.of_nat (x_nout X) <= ST)
/\ hidp (ST + NBSTATE_SIZEOF <= A \/ A + BITS_SIZEOF <= ST)
/\ hidp (ST + NBSTATE_SIZEOF <= D \/ D + x_dsz X <= ST)
/\ hidp (ST + NBSTATE_SIZEOF <= STEREO \/ STEREO + 8 <= ST)
/\ hidp (ST + NBSTATE_SIZEOF <= FF \/ FF + 2048 <= ST)
/\ hidp (ST + NBSTATE_SIZEOF <= SF \/ SF + 256 <= ST)
/\ hidp (OUT + 4 * Z.of_nat (x_nout X) <= A \/ A + BITS_SIZEOF <= OUT)
/\ hidp (OUT + 4 * Z.of_nat (x_nout X) <= D \/ D + x_dsz X <= OUT)
/\ hidp (OUT + 4 * Z.of_nat (x_nout X) <= STEREO \/ STEREO + 8 <= OUT)
/\ hidp (OUT + 4 * Z.of_nat (x_nout X) <= FF \/ FF + 2048 <= OUT)
/\ hidp (OUT + 4 * Z.of_nat (x_nout X) <= SF \/ SF + 256 <= OUT)
/\ hidp (A + BITS_SIZEOF <= D \/ D + x_dsz X <= A)
/\ hidp (A + BITS_SIZEOF <= STEREO \/ STEREO + 8 <= A)
/\ hidp (A + BITS_SIZEOF <= FF \/ FF + 2048 <= A)
/\ hidp (A + BITS_SIZEOF <= SF \/ SF + 256 <= A)
/\ hidp (D + x_dsz X <= STEREO \/ STEREO + 8 <= D)
/\ hidp (D + x_dsz X <= FF \/ FF + 2048 <= D)
/\ hidp (D + x_dsz X <= SF \/ SF + 256 <= D)
/\ hidp (STEREO + 8 <= FF \/ FF + 2048 <= STEREO)
/\ hidp (STEREO + 8 <= SF \/ SF + 256 <= STEREO)
/\ hidp (FF + 2048 <= SF \/ SF + 256 <= FF).

Definition nbx_aobj : Prop :=
aobj asegs (x_m0 X) ST NBSTATE_SIZEOF /\ aobj asegs (x_m0 X) OUT (4 * Z.of_nat (x_nout X)) /\ aobj asegs (x_m0 X) A BITS_SIZEOF
/\ aobj asegs (x_m0 X) D (x_dsz X) /\ aobj asegs (x_m0 X) STEREO 8.

Definition fr_saves : list cell :=
let F0 := x_F X in
[C8 (reg_get F0 (Z_to_bv 5 27)); C8 (reg_get F0 (Z_to_bv 5 26)); C8 (reg_get F0 (Z_to_bv 5 25)); C8 (reg_get F0 (Z_to_bv 5 24));
C8 (reg_get F0 (Z_to_bv 5 23)); C8 (reg_get F0 (Z_to_bv 5 22)); C8 (reg_get F0 (Z_to_bv 5 21)); C8 (reg_get F0 (Z_to_bv 5 20));
C8 (reg_get F0 (Z_to_bv 5 19)); C8 (reg_get F0 (Z_to_bv 5 18)); C8 (reg_get F0 (Z_to_bv 5 9)); C8 (reg_get F0 (Z_to_bv 5 8));
C8 (x_s11 X); C8 (x_s10 X); C8 (x_s9 X); C8 (x_s8 X); C8 (x_s7 X); C8 (x_s6 X); C8 (x_s5 X); C8 (x_s4 X);
C8 (x_s3 X); C8 (x_s2 X); C8 (x_s1 X); C8 (x_s0 X); C8 (x_ra X)].
Definition frame_at (m : mem) (s : nbslots) : Prop :=
rw_cells asegs m (usp + -544) (slot_cells s) /\ rw_cells asegs m (usp + -200) fr_saves.

Definition nbctx (m : mem) (st : nb_state ptr) (b : bits_st ptr) (j : nb_junk) (ows sws : list word) (s : nbslots) (ff : nbff) (sc : nbscope) : Prop :=
mem_inv asegs m /\ stk asegs m lo (usp + -544)
/\ NBP m ST OUT STEREO st j /\ nb_junk_ok j /\ cbs_ok A_speex_std_stereo_request_handler STEREO (nb_stereo_cb st) (j_cbs j) /\ nb_inv st
/\ bits_rep asegs m A D b /\ bits_ok b /\ sb_buf_size b = sb_buf_size (x_b0 X)
/\ rw_cells asegs m OUT (f32 ows) /\ length ows = x_nout X
/\ rw_cells asegs m STEREO (f32 sws) /\ length sws = 2%nat
/\ frame_at m s /\ fframe_at m FF ff /\ ff_ok ff /\ (exists rest, rw_cells asegs m SF (nbd_shadow sc rest))
/\ client_consts m /\ lib_consts m
/\ j_exc j = ST + 1368 /\ nb_innov_save st = nb_innov_save (x_st0 X).

Definition R_E (olp sub : Z) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -544)) (x_gp X) (x_tp X) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0 a1 a2 a3 a4 a5 (Z_to_bv 64 (ST + 2208)) (Z_to_bv 64 sub)
(Z_to_bv 64 SF) (Z_to_bv 64 0) (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936)) (Z_to_bv 64 40) (Z_to_bv 64 olp)
(Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2032)) t3 t4 t5 t6.
Definition at_E_A (r : smrec) (mo olp bp sub : Z) (st : nb_state ptr) (b : bits_st ptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 t3 t4 t5 t6 : word)
(j : nb_junk) (ows sws : list word) (s : nbslots) (ff : nbff),
ms = MS (R_E olp sub xra t0 t1 t2 a0 a1 a2 a3 a4 a5 t3 t4 t5 t6) Fx (Z_to_bv 64 PC_NBD_E) fc None m (seg_rom asegs)
/\ frm0 fc /\ nbctx m st b j ows sws s ff SC_E /\ slots_E ST OUT A FF s
/\ smrec_at mo = Some r /\ nb_submodeID st = mo /\ 17 <= bp <= 144
/\ (sm_lbr_pitch (smr_sm r) = -1 /\ olp = 0 \/ sm_lbr_pitch (smr_sm r) <> -1 /\ 17 <= olp <= 144)
/\ 0 <= sub <= 4.

Definition R_X (rv : Z) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s11 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -544)) (x_gp X) (x_tp X) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SF) (Z_to_bv 64 rv) (Z_to_bv 64 FF) s5 s6 s7 s8 (Z_to_bv 64 FF) (Z_to_bv 64 SHB) s11 t3 t4 t5 t6.
Definition at_X_A (rv : Z) (st : nb_state ptr) (b : bits_st ptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s11 t3 t4 t5 t6 : word)
(j : nb_junk) (ows sws : list word) (s : nbslots) (ff : nbff),
ms = MS (R_X rv xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s11 t3 t4 t5 t6) Fx (Z_to_bv 64 PC_NBD_X) fc None m (seg_rom asegs)
/\ frm0 fc /\ nbctx m st b j ows sws s ff SC_X.
End Cuts.

Lemma nb_smrec_cells_ok :
smrec_cells nb_smrec1 = LC_nb_submode1 /\ smrec_cells nb_smrec2 = LC_nb_submode2 /\ smrec_cells nb_smrec3 = LC_nb_submode3 /\ smrec_cells nb_smrec4 = LC_nb_submode4
/\ smrec_cells nb_smrec5 = LC_nb_submode5 /\ smrec_cells nb_smrec6 = LC_nb_submode6 /\ smrec_cells nb_smrec7 = LC_nb_submode7 /\ smrec_cells nb_smrec8 = LC_nb_submode8.
Proof. repeat split; reflexivity. Qed.
