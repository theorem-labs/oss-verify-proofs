(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1dg X1df X1ck X1cu X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05q X05l X05m X09f X06d.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr X12b X0z5 X0ys X0x2 X0yt X0zq X11l
X0wh X0yu X124 X0yd X0wk.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X11w.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section FLDB.
Variables (usp S OUT A f sf MODE fsz : Z) (v : sb_vslots).
Variables (EX LIB OFF LI FG NW : Z) (lis : list word).
Variable spv : Z.
Variables rav gp tp s4v s5v s8v s10v t4v t6v : word.
Hypothesis EX8 : EX mod 8 = 0.
Hypothesis LIB4 : LIB mod 4 = 0.
Hypothesis FG8 : FG mod 8 = 0.
Hypothesis LIL : Z.of_nat (length lis) = NW.
Hypothesis NWB : 0 < NW < 2^20.
Hypothesis OFFB : 0 <= OFF < 2^20.
Hypothesis LIBP : 0 < LIB.
Hypothesis OUTP : 0 < OUT < 2^63.
Hypothesis USP : usp < 2^63.
Hypothesis ELI : LI = LIB + 4 * OFF.
Definition RFLB (i : Z) (t0x t1x t2x a0x a1x : word) : bvmap 5 word :=
R_LB usp spv gp tp rav t0x t1x t2x a0x a1x (Z_to_bv 64 NW) (Z_to_bv 64 i) (Z_to_bv 64 (4 * i)) (Z_to_bv 64 i) (Z_to_bv 64 (18446744073709551615 - EX)) (Z_to_bv 64 (EX + 4))
(Z_to_bv 64 OFF) (Z_to_bv 64 EX) s4v s5v s8v (Z_to_bv 64 NW) s10v (Z_to_bv 64 LIB) t4v (Z_to_bv 64 FG) t6v.
Definition fldB_post (mI : mem) : machine_state -> Prop :=
fun ms' => exists t0' t1' t2' a0' a1' F' (fc' : bv 32) m' (ys' : list word),
ms' = MS (RFLB NW t0' t1' t2' a0' a1') F' (Z_to_bv 64 0xbfcc4) fc' None m' (seg_rom bsegs)
/\ munch [(EX, EX + 4 * NW)] mI m' /\ wmono bsegs mI m' /\ mem_inv bsegs m' /\ frm0 fc'
/\ Z.of_nat (length ys') = NW /\ rw_cells bsegs m' EX (f32 ys') /\ rw_cells bsegs m' LI (f32 lis).
Lemma sblB_fold_loop : forall (k : nat) (mI : mem) (rest done : list word) (fgw : word) (i : Z) (t0x t1x t2x a0x a1x : word) F fc mc,
length rest = (2 * Datatypes.S k)%nat -> i = Z.of_nat (length done) -> i + Z.of_nat (length rest) = NW ->
aobj bsegs mI EX (4 * NW) -> aobj bsegs mI LI (4 * NW) -> aobj bsegs mI FG 4 -> offsh [(EX, EX + 4 * NW)] ->
(EX + 4 * NW <= LI \/ LI + 4 * NW <= EX) -> (EX + 4 * NW <= FG \/ FG + 4 <= EX) -> EX + 4 * NW <= usp + -736 ->
mem_inv bsegs mc -> munch [(EX, EX + 4 * NW)] mI mc -> wmono bsegs mI mc -> frm0 fc ->
rw_cells bsegs mc (usp + -736) (sb_slots usp S OUT A f sf MODE fsz v) ->
rw_cells bsegs mc EX (f32 done) -> rw_cells bsegs mc (EX + 4 * i) (f32 rest) -> rw_cells bsegs mc LI (f32 lis) -> ro_cells bsegs mc FG [C4 fgw] ->
evt bsegs (fldB_post mI) (MS (RFLB i t0x t1x t2x a0x a1x) F (Z_to_bv 64 0xbfb38) fc None mc (seg_rom bsegs)).
Proof using EX8 LIB4 FG8 LIL NWB OFFB LIBP OUTP USP ELI.
induction k as [|k IH]; intros mI rest done fgw i t0x t1x t2x a0x a1x F fc mc LR Hi HN OBX OBL OBF OF SEPL SEPF EXSL MI MU WM FRM SL XD XC LC FGC;
pose proof OBX as (OX0 & OX1 & _); pose proof OBL as (OL0 & OL1 & _); pose proof OBF as (OF0 & OF1 & _); unfold APP_TOP in *;
destruct rest as [|c0 [|c1 rest']]; cbn [length] in LR, HN; try lia;
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
destruct (sblB_rw_f32_nth mc LI lis i LC ltac:(cbn [length] in *; lia)) as (wl0 & WL0);
destruct (sblB_rw_f32_nth mc LI lis (i + 1) LC ltac:(cbn [length] in *; lia)) as (wl1 & WL1);
assert (AL0 : (LIB + (OFF + i) * 4) mod 4 = 0) by (rewrite Z_mod_plus_full; exact LIB4);
assert (AL1 : (LIB + (OFF + i + 1) * 4) mod 4 = 0) by (rewrite Z_mod_plus_full; exact LIB4);
pose proof SL as SL0; unfold sb_slots, sha in SL;
unfold RFLB, R_LB; rewrite !f32_cons in XC;
(let X0 := fresh "X0c" in chunk_uncons XC as X0);
(let X1 := fresh "X1c" in chunk_uncons XC as X1).
- bato 0xbfb44. astep. chk_merge OBF 4.
bato 0xbfb94. replace (LIB + (OFF + i) * 4) with (LI + 4 * i) by lia.
bato 0xbfb9c. astep. chk_merge OBL 4.
bato 0xbfbbc. astep. chk_merge OBX 4.
bato 0xbfbd0. astep. chk_merge OBF 4.
bato 0xbfc04. replace ((OFF + i + 1) * 4 + LIB) with (LI + 4 * i + 4) by lia. replace (LI + 4 * (i + 1)) with (LI + 4 * i + 4) in WL1 by lia.
bato 0xbfc0c. astep. chk_merge OBL 4.
bato 0xbfc34. astep. chk_merge OBX 4.
bato 0xbfc48. replace (EX + 4 + 4 * i) with (EX + 4 * i + 4) by lia. astep.
bato 0xbfc5c.
astep. sh_if.
bato 0xbfcc4.
rewrite (swrap32_small (i + 2)) by lia.
chunk_snoc XD X0c. rewrite sblB_f32_snoc in XD. chunk_snoc XD X1c. rewrite sblB_f32_snoc in XD.
replace (4 * i + 8) with (4 * NW) by lia. replace (i + 2) with NW by lia.
apply evt_done. unfold fldB_post, RFLB, R_LB. do 8 eexists. lazymatch type of XD with rw_cells _ _ _ (f32 ?l) => exists l end.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|].
split; [rewrite !length_app; cbn [length]; lia|]. split; [exact XD| exact LC].
- bato 0xbfb44. astep. chk_merge OBF 4.
bato 0xbfb94. replace (LIB + (OFF + i) * 4) with (LI + 4 * i) by lia.
bato 0xbfb9c. astep. chk_merge OBL 4.
bato 0xbfbbc. astep. chk_merge OBX 4.
bato 0xbfbd0. astep. chk_merge OBF 4.
bato 0xbfc04. replace ((OFF + i + 1) * 4 + LIB) with (LI + 4 * i + 4) by lia. replace (LI + 4 * (i + 1)) with (LI + 4 * i + 4) in WL1 by lia.
bato 0xbfc0c. astep. chk_merge OBL 4.
bato 0xbfc34. astep. chk_merge OBX 4.
bato 0xbfc48. replace (EX + 4 + 4 * i) with (EX + 4 * i + 4) by lia. astep.
bato 0xbfc5c. astep. sh_if.
rewrite (swrap32_small (i + 2)) by lia.
chunk_snoc XD X0c. rewrite sblB_f32_snoc in XD. chunk_snoc XD X1c. rewrite sblB_f32_snoc in XD.
clear WL0 WL1 AL0 AL1.
replace (4 * i + 8) with (4 * (i + 2)) by lia.
replace (EX + 4 * i + 4 + 4) with (EX + 4 * (i + 2)) in XC by lia.
lazymatch type of SL with rw_cells ?sg ?mm _ _ => change (rw_cells sg mm (usp + -736) (sb_slots usp S OUT A f sf MODE fsz v)) in SL end.
eapply (IH mI rest' _ fgw (i + 2)); try eassumption; try reflexivity;
try (rewrite ?length_app; cbn [length] in *; lia).
Qed.
End FLDB.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0xe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma sblB_ro_cell_at : forall (m : mem) A (cs : list cell) (k : nat) (d : cell), ro_cells bsegs m A cs -> (k < length cs)%nat ->
ro_cells bsegs m (A + Z.of_nat (cells_size (firstn k cs))) [nth k cs d].
Proof.
intros m A cs k d H Hk. rewrite <- (firstn_skipn k cs) in H. apply ro_cells_app in H as [_ H2].
destruct (skipn k cs) as [|c r] eqn:E.
- exfalso. assert (L : length (skipn k cs) = 0%nat) by (rewrite E; reflexivity). rewrite length_skipn in L. lia.
- assert (EN : nth k cs d = c).
{ rewrite <- (firstn_skipn k cs), E. rewrite app_nth2; rewrite length_firstn; [|lia]. replace (k - Nat.min k (length cs))%nat with 0%nat by lia. reflexivity. }
rewrite EN. change (c :: r) with ([c] ++ r) in H2. apply ro_cells_app in H2 as [H3 _]. exact H3.
Qed.

Lemma sblB_e5n : forall (usp lo hb S OUT A D f sf MODE fsz FS sub LI : Z) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs) (pad1 : list byte)
(b : bits_st bptr) (lis exs : list word) (xs4 xs10 : word)
(gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m (usp + -736) (sb_slots usp S OUT A f sf MODE fsz v) ->
rw_cells bsegs m S (sbp_hdr s a) -> sbd_subframeSize s = FS ->
rw_cells bsegs m (S + 136) (sbp_cfg s pad1) -> rw_cells bsegs m (S + 152) [C4 (Z_to_bv 64 1)] ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> (S + 160 <= SH_LO \/ SH_HI <= S) -> S + 160 <= lo ->
((sbd_mode s = ModeWB /\ FS = 40) \/ (sbd_mode s = ModeUWB /\ FS = 80)) -> MODE = sbmode_struct (sbd_mode s) -> aobj bsegs m MODE 216 ->
aobj bsegs m (sb_sub_addr 1) 88 -> lib_consts m -> 0 <= sub < 4 ->
bits_rep bsegs m A D b -> bits_ok b -> aobj bsegs m A BITS_SIZEOF -> aobj bsegs m D (sb_buf_size b) ->
(A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A) -> A + BITS_SIZEOF <= lo -> D + sb_buf_size b <= lo -> IMG_TOP_B <= A -> (S + 160 <= A \/ A + BITS_SIZEOF <= S) ->
LI = OUT + 4 * fsz + 4 * (FS * sub) -> rw_cells bsegs m LI (f32 lis) -> Z.of_nat (length lis) = FS -> aobj bsegs m LI (4 * FS) -> LI mod 4 = 0 -> LI + 4 * FS <= lo ->
(S + 160 <= LI \/ LI + 4 * FS <= S) -> (A + BITS_SIZEOF <= LI \/ LI + 4 * FS <= A) -> 0 < OUT < 2^63 -> OUT mod 4 = 0 -> 0 <= fsz < 2^16 ->
rw_cells bsegs m (hb + 32) (f32 exs) -> Z.of_nat (length exs) = FS -> aobj bsegs m (hb + 32) (4 * FS) ->
client_constsB m -> stk bsegs m lo hb -> lo <= hb - 48 -> hb + 32 + 4 * FS <= usp + -1216 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 -> hb mod 32 = 0 ->
mem_inv bsegs m -> frm0 fc ->
evt bsegs (fun ms => exists (m1 : mem) (xra xt0 xt1 xt2 xa0 xa1 xt3 : word) (F' : bvmap 5 word) (fc' : bv 32) (exs' : list word),
ms = MS (R_LB usp hb gp tp xra xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 FS) (Z_to_bv 64 FS) (Z_to_bv 64 (4 * FS)) (Z_to_bv 64 FS)
(Z_to_bv 64 (18446744073709551615 - (hb + 32))) (Z_to_bv 64 (hb + 32 + 4))
(Z_to_bv 64 (FS * sub)) (Z_to_bv 64 (hb + 32)) xs4 (Z_to_bv 64 0x10360) (Z_to_bv 64 (4 * FS)) (Z_to_bv 64 FS) xs10
(Z_to_bv 64 (OUT + 4 * fsz)) (Z_to_bv 64 (S + 72)) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 (S + 88))) F' (Z_to_bv 64 SBLB_PC_J) fc' None m1 (seg_rom bsegs)
/\ munch [(A, A + BITS_SIZEOF); (hb + -48, hb); (hb + 32, hb + 32 + 4 * FS)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo hb /\ frm0 fc'
/\ bits_rep bsegs m1 A D (ub b 5) /\ rw_cells bsegs m1 (hb + 32) (f32 exs') /\ Z.of_nat (length exs') = FS)
(MS (R_LB usp hb gp tp (Z_to_bv 64 RA_sblB_memset2) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (FS * sub)) (Z_to_bv 64 (hb + 32)) xs4 (Z_to_bv 64 0x10360) (Z_to_bv 64 (4 * FS)) (Z_to_bv 64 FS) xs10 t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sblB_memset2)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros SL HD EFS CFG IDC OBS S8 SPOS SOFF SLO HMO EMODE OBM OBSM LC SUB REP OK OBA OBD ASH ALO DLO ATOP SEPSA
ELI LIC LLI OBLI LI4 LILO SEPSL SEPAL OUTP OUT4 FSZ EXC LEX OBEX CC ST LO HB LOS SPH U32 HB32 MI FRM.
unfold R_LB, RA_sblB_memset2, SBLB_PC_J in *. unfold SH_LO, SH_HI in SOFF. pose proof LOS as LOS'. unfold SH_HI in LOS'.
replace (ret_pc (Z_to_bv 64 0xbf4b8)) with (Z_to_bv 64 0xbf4b8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold IMG_TOP_B in ATOP. pose proof SEPSA as SEPSA'. unfold BITS_SIZEOF in SEPSA'.
pose proof ST as (STa & STb & _). pose proof CC as (G1 & G2 & G3 & G4).
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof (munch_refl [(A, A + BITS_SIZEOF); (hb + -48, hb); (hb + 32, hb + 32 + 4 * FS)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (FSB : 40 <= FS <= 80) by (clear - HMO; lia).
assert (OF : offsh [(A, A + BITS_SIZEOF); (hb + -48, hb); (hb + 32, hb + 32 + 4 * FS)]) by (pose proof ASH as Y; clear - Y LOS LO FSB; cbn; unfold SH_LO, SH_HI, BITS_SIZEOF in *; lia).
pose proof SL as SL0. unfold sb_slots, sha in SL. unfold sbp_hdr in HD. rewrite EFS in HD. unfold sbp_cfg in CFG. unfold sha.
assert (EX8 : (hb + 32) mod 8 = 0) by (clear - HB32; Z.div_mod_to_equations; lia).
remember (hb + 32) as EX eqn:EEX.
destruct HMO as [[EMO EFS'] | [EMO EFS']]; rewrite EMO in *; cbn [sbmode_struct] in EMODE; subst FS.
- assert (ESUB : sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR ModeWB = MODE + 40) by (subst MODE; reflexivity).
rewrite ESUB in CFG.
assert (M8 : MODE mod 8 = 0) by (subst MODE; reflexivity).
pose proof (lib_const m A_sb_wb_mode LC_sb_wb_mode LC ltac:(lc_in)) as MTAB. rewrite <- EMODE in MTAB. unfold LC_sb_wb_mode in MTAB. unfold A_sb_wb_mode in EMODE.
pose proof (sblB_ro_cell_at m MODE _ 7 (C1 (Z_to_bv 8 0)) MTAB ltac:(cbn; lia)) as FGC0.
lazymatch type of FGC0 with ro_cells _ _ (MODE + ?t) [?c] => let t' := eval vm_compute in t in let c' := eval cbn [nth] in c in change t with t' in FGC0; change c with c' in FGC0 end.
pose proof (lib_const m A_wb_submode1 LC_wb_submode1 LC ltac:(lc_in)) as T1. unfold LC_wb_submode1 in T1.
cbn [sb_sub_addr Z.eqb Pos.eqb] in OBSM.
set (SM := A_wb_submode1) in *. assert (ESM : SM = 0xf8c40) by reflexivity. assert (SM8 : SM mod 8 = 0) by reflexivity. clearbody SM.
bato 0xbf4e4. rewrite sx32_small by (unfold int31; lia). bato 0xbf540. rewrite <- ESM.
bato 0xbfab8. astep.
rewrite ?EFS' in *.
call (speex_bits_unpack_unsigned_walk A D hb lo b 5 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP OK ltac:(lia) OBA OBD ASH ltac:(lia) LOS ltac:(lia) ALO DLO).
1: exact ST. 1: exact CC. 1: exact MI.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
change (snd (speex_bits_unpack_unsigned b 5)) with (ub b 5) in *. change (fst (speex_bits_unpack_unsigned b 5)) with (uv b 5) in *.
pose proof (ub_ok b 5 OK ltac:(lia)) as (OK1 & SZ1 & V1R). change (2 ^ 5) with 32 in V1R.
bato 0xbfad0.
destruct POST as ((rj2 & Lrj2 & OBJ) & (bs2 & DAT & Hbs2) & SIDE2). unfold bits_cells in OBJ.
assert (Lbs2 : Z.of_nat (length bs2) = sb_buf_size (ub b 5)).
{ pose proof OK1 as OK'. unfold bits_ok in OK'. rewrite Hbs2, zlength_map_unsigned in OK'. lia. }
rewrite SZ1 in Lbs2.
pose proof ALO as ALO'. unfold BITS_SIZEOF in ALO'.
destruct (stk_split bsegs _ lo (hb + -16) hb PC ltac:(lia)) as [STKa STKb]. clear PC.
astep.
call (exp_specZ (hb + -16) hb).
1: exact STKb. 1: lia. 1: lia. 1: eassumption. 1: eassumption.
match goal with H : stk bsegs _ (hb + -16) hb |- _ => pose proof (stk_merge bsegs _ lo (hb + -16) hb STKa H ltac:(lia)) as STK3; clear H STKa end.
replace (ret_pc (Z_to_bv 64 785108)) with (Z_to_bv 64 785108) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
bato 0xbfae8. astep. joinyb 0xbfaf4 1 2.
bato 0xbfb0c. rewrite sx32_small by (unfold int31; lia).
bato 0xbfb38.
pose proof OBEX as (OE0 & OE1 & _). unfold APP_TOP in OE1.
rewrite OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1ch.lnot_mod64 by lia. unfold Z.lnot.
replace (Z.pred (- EX) mod 2 ^ 64) with (18446744073709551615 - EX)
by (rewrite <- Z.sub_1_r; replace (- EX - 1) with ((18446744073709551615 - EX) + (-1) * 2^64) by (cbn; lia); rewrite Z_mod_plus_full; symmetry; apply Z.mod_small; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (aobj_munch bsegs _ m mc EX (4 * 40) OBEX MU (shfree_of_aobj bsegs _ m EX (4 * 40) OF OBEX)) as OBEX1;
pose proof (aobj_munch bsegs _ m mc LI (4 * 40) OBLI MU (shfree_of_aobj bsegs _ m LI (4 * 40) OF OBLI)) as OBLI1;
let OBF0 := fresh in pose proof (aobj_sub bsegs m MODE 216 (MODE + 32) 4 OBM ltac:(lia) ltac:(lia)) as OBF0; pose proof (aobj_munch bsegs _ m mc (MODE + 32) 4 OBF0 MU (shfree_of_aobj bsegs _ m (MODE + 32) 4 OF OBF0)) as OBFG1;
pose proof (munch_refl [(EX, EX + 4 * 40)] mc) as MUL; pose proof (wmono_refl bsegs mc) as WML;
assert (XD0 : rw_cells bsegs mc EX (f32 [])) by (apply rw_cells_nil; pose proof OBEX1 as (OY0 & OY1 & _); unfold APP_TOP in OY1; lia)
end.
assert (OFL : offsh [(EX, EX + 4 * 40)]) by (cbn; unfold SH_LO, SH_HI; lia).
rewrite <- (Z.add_0_r EX) in EXC at 1. replace (EX + 0) with (EX + 4 * 0) in EXC by lia.
hide_disj.
call (sblB_fold_loop usp S OUT A f sf MODE fsz v EX (OUT + 4 * fsz) (40 * sub) LI (MODE + 32) 40 lis hb _ gp tp _ _ _ _ _ _ EX8
ltac:(replace (OUT + 4 * fsz) with (OUT + fsz * 4) by lia; rewrite Z_mod_plus_full; exact OUT4) ltac:(rewrite EMODE; reflexivity) LLI ltac:(lia) ltac:(lia) ltac:(lia) OUTP SPH ltac:(rewrite ELI; lia)
19 _ exs [] _ 0 _ _ _ _ _ _ _ _
ltac:(lia) eq_refl ltac:(cbn [length]; lia) OBEX1 OBLI1 OBFG1 OFL ltac:(right; lia) ltac:(right; rewrite EMODE; lia) ltac:(lia)
MI MUL WML FRM SL0 XD0 EXC LIC FGC0).
replace (EX + 4 * 0) with EX by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (REP2 : bits_rep bsegs mc A D (ub b 5)) by (split; [exists rj2; split; [assumption| exact OBJ]| split; [exists bs2; split; [exact DAT| assumption]| assumption]])
end.
apply evt_done. do 8 eexists. exact (Z_to_bv 64 0). do 2 eexists. lazymatch goal with H : rw_cells _ _ EX (f32 ?l) |- _ => exists l end.
split; [unfold R_LB, sha; reflexivity|].
split; [exact MU|]. split; [eassumption|]. split; [eassumption|]. split; [exact STK3|]. split; [eassumption|].
split; [exact REP2|]. split; [eassumption| eassumption].
- assert (ESUB : sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR ModeUWB = MODE + 40) by (subst MODE; reflexivity).
rewrite ESUB in CFG.
assert (M8 : MODE mod 8 = 0) by (subst MODE; reflexivity).
pose proof (lib_const m A_sb_uwb_mode LC_sb_uwb_mode LC ltac:(lc_in)) as MTAB. rewrite <- EMODE in MTAB. unfold LC_sb_uwb_mode in MTAB. unfold A_sb_uwb_mode in EMODE.
pose proof (sblB_ro_cell_at m MODE _ 7 (C1 (Z_to_bv 8 0)) MTAB ltac:(cbn; lia)) as FGC0.
lazymatch type of FGC0 with ro_cells _ _ (MODE + ?t) [?c] => let t' := eval vm_compute in t in let c' := eval cbn [nth] in c in change t with t' in FGC0; change c with c' in FGC0 end.
pose proof (lib_const m A_wb_submode1 LC_wb_submode1 LC ltac:(lc_in)) as T1. unfold LC_wb_submode1 in T1.
cbn [sb_sub_addr Z.eqb Pos.eqb] in OBSM.
set (SM := A_wb_submode1) in *. assert (ESM : SM = 0xf8c40) by reflexivity. assert (SM8 : SM mod 8 = 0) by reflexivity. clearbody SM.
bato 0xbf4e4. rewrite sx32_small by (unfold int31; lia). bato 0xbf540. rewrite <- ESM.
bato 0xbfab8. astep.
rewrite ?EFS' in *.
call (speex_bits_unpack_unsigned_walk A D hb lo b 5 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP OK ltac:(lia) OBA OBD ASH ltac:(lia) LOS ltac:(lia) ALO DLO).
1: exact ST. 1: exact CC. 1: exact MI.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
change (snd (speex_bits_unpack_unsigned b 5)) with (ub b 5) in *. change (fst (speex_bits_unpack_unsigned b 5)) with (uv b 5) in *.
pose proof (ub_ok b 5 OK ltac:(lia)) as (OK1 & SZ1 & V1R). change (2 ^ 5) with 32 in V1R.
bato 0xbfad0.
destruct POST as ((rj2 & Lrj2 & OBJ) & (bs2 & DAT & Hbs2) & SIDE2). unfold bits_cells in OBJ.
assert (Lbs2 : Z.of_nat (length bs2) = sb_buf_size (ub b 5)).
{ pose proof OK1 as OK'. unfold bits_ok in OK'. rewrite Hbs2, zlength_map_unsigned in OK'. lia. }
rewrite SZ1 in Lbs2.
pose proof ALO as ALO'. unfold BITS_SIZEOF in ALO'.
destruct (stk_split bsegs _ lo (hb + -16) hb PC ltac:(lia)) as [STKa STKb]. clear PC.
astep.
call (exp_specZ (hb + -16) hb).
1: exact STKb. 1: lia. 1: lia. 1: eassumption. 1: eassumption.
match goal with H : stk bsegs _ (hb + -16) hb |- _ => pose proof (stk_merge bsegs _ lo (hb + -16) hb STKa H ltac:(lia)) as STK3; clear H STKa end.
replace (ret_pc (Z_to_bv 64 785108)) with (Z_to_bv 64 785108) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
bato 0xbfae8. astep. joinyb 0xbfaf4 1 2.
bato 0xbfb0c. rewrite sx32_small by (unfold int31; lia).
bato 0xbfb38.
pose proof OBEX as (OE0 & OE1 & _). unfold APP_TOP in OE1.
rewrite OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1ch.lnot_mod64 by lia. unfold Z.lnot.
replace (Z.pred (- EX) mod 2 ^ 64) with (18446744073709551615 - EX)
by (rewrite <- Z.sub_1_r; replace (- EX - 1) with ((18446744073709551615 - EX) + (-1) * 2^64) by (cbn; lia); rewrite Z_mod_plus_full; symmetry; apply Z.mod_small; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (aobj_munch bsegs _ m mc EX (4 * 80) OBEX MU (shfree_of_aobj bsegs _ m EX (4 * 80) OF OBEX)) as OBEX1;
pose proof (aobj_munch bsegs _ m mc LI (4 * 80) OBLI MU (shfree_of_aobj bsegs _ m LI (4 * 80) OF OBLI)) as OBLI1;
let OBF0 := fresh in pose proof (aobj_sub bsegs m MODE 216 (MODE + 32) 4 OBM ltac:(lia) ltac:(lia)) as OBF0; pose proof (aobj_munch bsegs _ m mc (MODE + 32) 4 OBF0 MU (shfree_of_aobj bsegs _ m (MODE + 32) 4 OF OBF0)) as OBFG1;
pose proof (munch_refl [(EX, EX + 4 * 80)] mc) as MUL; pose proof (wmono_refl bsegs mc) as WML;
assert (XD0 : rw_cells bsegs mc EX (f32 [])) by (apply rw_cells_nil; pose proof OBEX1 as (OY0 & OY1 & _); unfold APP_TOP in OY1; lia)
end.
assert (OFL : offsh [(EX, EX + 4 * 80)]) by (cbn; unfold SH_LO, SH_HI; lia).
rewrite <- (Z.add_0_r EX) in EXC at 1. replace (EX + 0) with (EX + 4 * 0) in EXC by lia.
hide_disj.
call (sblB_fold_loop usp S OUT A f sf MODE fsz v EX (OUT + 4 * fsz) (80 * sub) LI (MODE + 32) 80 lis hb _ gp tp _ _ _ _ _ _ EX8
ltac:(replace (OUT + 4 * fsz) with (OUT + fsz * 4) by lia; rewrite Z_mod_plus_full; exact OUT4) ltac:(rewrite EMODE; reflexivity) LLI ltac:(lia) ltac:(lia) ltac:(lia) OUTP SPH ltac:(rewrite ELI; lia)
39 _ exs [] _ 0 _ _ _ _ _ _ _ _
ltac:(lia) eq_refl ltac:(cbn [length]; lia) OBEX1 OBLI1 OBFG1 OFL ltac:(right; lia) ltac:(right; rewrite EMODE; lia) ltac:(lia)
MI MUL WML FRM SL0 XD0 EXC LIC FGC0).
replace (EX + 4 * 0) with EX by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (REP2 : bits_rep bsegs mc A D (ub b 5)) by (split; [exists rj2; split; [assumption| exact OBJ]| split; [exists bs2; split; [exact DAT| assumption]| assumption]])
end.
apply evt_done. do 8 eexists. exact (Z_to_bv 64 0). do 2 eexists. lazymatch goal with H : rw_cells _ _ EX (f32 ?l) |- _ => exists l end.
split; [unfold R_LB, sha; reflexivity|].
split; [exact MU|]. split; [eassumption|]. split; [eassumption|]. split; [exact STK3|]. split; [eassumption|].
split; [exact REP2|]. split; [eassumption| eassumption].
Qed.
