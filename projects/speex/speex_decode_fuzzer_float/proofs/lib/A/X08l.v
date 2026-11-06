(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1dg X1df X1ck X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05l X05j X05k X05b X082 X09f X069 X09e
X091 X08x X090.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Local Ltac slia ::= (try unfold BITS_SIZEOF in * ); first [ exact I | lia | split; [lia|exact I] ].
Local Notation mem := (word -> option byte).

Definition nbd_frame_A (ST A OUT f : Z) (ja jb jc jd je jf jg jh : list byte) (sv : list cell) : list cell :=
[C8 (Z_to_bv 64 0); CB 16 ja; C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 (ST + 2047)); C8 (Z_to_bv 64 (ST + 2120)); CB 80 jb;
C8 (Z_to_bv 64 (ST + 2032)); CB 8 jc; C8 (Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB)); CB 8 jd; C8 (Z_to_bv 64 OUT); CB 64 je; C8 (Z_to_bv 64 0); CB 8 jf;
C8 (Z_to_bv 64 A); CB 32 jg; C8 (Z_to_bv 64 (ST + 32)); C8 (Z_to_bv 64 (Z.shiftr (ST + 2904) 3 + SHB)); C8 (Z_to_bv 64 (ST + 2256)); CB 16 jh; C8 (Z_to_bv 64 f)] ++ sv.

Lemma remaining_range : forall {ptr} A D (b : bits_st ptr), bits_ok b -> bits_side A D b -> -1 <= speex_bits_remaining b < 2^31.
Proof.
intros ptr A D b OK SD. pose proof (bits_ints A D b OK SD) as (In & Ic & Ib & Io & Iv & Is & Rc & Rb & Rp & Rn & Rs & R1 & Rov).
unfold speex_bits_remaining, int31, bits_pos in *. destruct (negb (sb_overflow b =? 0)); lia.
Qed.

Section A.
Context {ptr : Type}.
Variables (usp lo ST A D OUT f sf : Z).
Variables gp tp : word.
Hypothesis LO : lo <= usp - 544 - 96.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis ALO : A + BITS_SIZEOF <= lo.
Hypothesis A8 : A mod 8 = 0.
Hypothesis SB : 0 < ST /\ ST + 2968 <= 140737488355328.

Definition R_A (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 sf) (Z_to_bv 64 (-1)) (Z_to_bv 64 (ST + 2904)) (Z_to_bv 64 A) (Z_to_bv 64 (ST + 2912)) (Z_to_bv 64 5) (Z_to_bv 64 ST)
(Z_to_bv 64 0x23c80) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.shiftr (ST + 2912) 3 + SHB)) t3 t4 t5 t6.

Lemma nbA_pre : forall (b : bits_st ptr) (t0 t1 t2 a1 a6 a7 t3 t4 t5 t6 : word) (ja jb jc jd je jf jg : list byte) (sv : list cell) F fc (m : mem),
bits_rep asegs m A D b -> bits_ok b -> aobj asegs m A BITS_SIZEOF -> D + sb_buf_size b <= lo ->
length sv = 25%nat ->
stk asegs m lo (usp + -544) -> rw_cells asegs m (usp + -544) (nbd_frame_w2 ST A OUT f ja jb jc jd je jf jg sv) ->
client_consts m -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (xra t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
munch [(usp + -640, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -544) /\ bits_rep asegs m1 A D b
/\ if speex_bits_remaining b <? 5
then ms = MS (mkR xra (Z_to_bv 64 (usp + -544)) gp tp t0' t1' t2' (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0' a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 sf) (Z_to_bv 64 (-1)) (Z_to_bv 64 f) (Z_to_bv 64 (ST + 2120)) (Z_to_bv 64 (ST + 2047)) (Z_to_bv 64 5)
(Z_to_bv 64 ST) (Z_to_bv 64 f) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2032)) t3' t4' t5' t6')
F (Z_to_bv 64 PC_NBD_X) fc None m1 (seg_rom asegs)
/\ rw_cells asegs m1 (usp + -544) (nbd_frame_w2 ST A OUT f ja jb jc jd je jf jg sv)
else ms = MS (R_A xra t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6') F (Z_to_bv 64 0x9fa50) fc None m1 (seg_rom asegs)
/\ exists ja' jb' jc' jh', rw_cells asegs m1 (usp + -544) (nbd_frame_A ST A OUT f ja' jb' jc' jc jd je jf jh' sv))
(MS (mkR (Z_to_bv 64 RA_nbd_smalloc) (Z_to_bv 64 (usp + -544)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544))
(Z_to_bv 64 A) a1 (Z_to_bv 64 (-8)) (Z_to_bv 64 4) (Z_to_bv 64 (ST + 32)) (Z_to_bv 64 0x9f634) a6 a7
(Z_to_bv 64 sf) (Z_to_bv 64 0) (Z_to_bv 64 f) (Z_to_bv 64 (ST + 2120)) (Z_to_bv 64 (ST + 2047)) (Z_to_bv 64 (Z.shiftr (ST + 2032) 3 + SHB))
(Z_to_bv 64 ST) (Z_to_bv 64 f) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2032)) t3 t4 t5 t6)
F (Z_to_bv 64 0x9f9f8) fc None m (seg_rom asegs)).
Proof.
intros b t0 t1 t2 a1 a6 a7 t3 t4 t5 t6 ja jb jc jd je jf jg sv F fc m REP OKB OBA DLO LSV ST0 FR CC MI.
unfold nbd_frame_w2, nbd_frame_A, R_A, PC_NBD_X, RA_nbd_smalloc in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof ST0 as (STa & STb & _).
pose proof (munch_refl [(usp + -640, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
astep.
call (speex_bits_remaining_walk A D (usp + -544) lo b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m REP OKB OBA ST0 ltac:(lia) LOS ltac:(lia) ALO DLO CC).
all: try eassumption.
match goal with H : ?x = Z_to_bv 64 (speex_bits_remaining b) |- _ => subst x end.
pose proof SB as (SB0 & SB1).
pose proof REP as (_ & _ & SIDE). pose proof (remaining_range A D b OKB SIDE) as RR. change (2^31) with 2147483648 in RR.
ato 0x9fa04. astep.
destruct (speex_bits_remaining b <? 5) eqn:K; [apply Z.ltb_lt in K | apply Z.ltb_ge in K].
- sh_if. ato 0xa1a1c.
apply evt_done. do 17 eexists. split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact PC|]. split; [exact POST|].
split; [reflexivity| exact FR].
- sh_if.
destruct POST as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE'). unfold bits_cells in OBJ.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b) by (pose proof OKB as OK'; unfold bits_ok in OK'; rewrite Hbs, zlength_map_unsigned in OK'; lia).
pose proof ALO as ALO'. unfold BITS_SIZEOF in ALO'.
ato 0x9fa50.
apply evt_done. do 17 eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption|].
split; [split; [exists rj; split; [exact Lrj| exact OBJ]| split; [exists bs; split; [exact DAT| exact Hbs]| exact SIDE']]|].
split; [reflexivity|]. do 4 eexists. exact FR.
Qed.
End A.

Definition A_wb_skip_table : Z := 0x23c80.

Lemma wb_skip_read : forall (m : mem) i, mem_inv asegs m -> 0 <= i < 8 ->
ov_read_bytes asegs m (wa (A_wb_skip_table + 4 * i)) 4 = Some (le4 (Z_to_bv 64 (znth wb_skip_table i))).
Proof.
intros m i MI Hi. unfold A_wb_skip_table.
assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]];
match goal with |- ov_read_bytes _ _ (wa ?a) 4 = Some (le4 (Z_to_bv 64 ?v)) =>
let av := eval vm_compute in a in let vv := eval vm_compute in v in
change a with av; change v with vv;
pose proof (ro_cells_image asegs m av (le4 (Z_to_bv 64 vv)) MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite length_le4; cbn; lia)) as RO;
exact (ro_cells_read_at asegs m av _ 0%nat _ 4 _ RO ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity))
end.
Qed.
Lemma wb_skip_range : forall i, 0 <= i < 8 -> 0 <= znth wb_skip_table i <= 352.
Proof.
intros i Hi.
assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]];
match goal with |- 0 <= ?x <= 352 => let v := eval vm_compute in x in change x with v end; lia.
Qed.

Section Skip.
Context {ptr : Type}.
Variables (usp lo ST A D sf : Z).
Variables gp tp : word.
Variable m : mem.
Hypothesis LO : lo <= usp - 544 - 96.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis OBA : aobj asegs m A BITS_SIZEOF.
Hypothesis OBT : aobj asegs m A_wb_skip_table 32.
Hypothesis ALO : A + BITS_SIZEOF <= lo.
Hypothesis ASH : hidp (A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A).
Hypothesis ATOP : IMG_TOP <= A.
Local Notation W := [(A, A + 48); (usp + -640, usp + -544)].
Local Notation RA := (R_A usp ST A sf gp tp).

Lemma nbA_skip1 : forall (b : bits_st ptr) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc m1,
bits_rep asegs m1 A D b -> bits_ok b -> aobj asegs m D (sb_buf_size b) -> D + sb_buf_size b <= lo ->
4 <= speex_bits_remaining b -> 1 <= bits_pos b ->
munch W m m1 -> offsh W -> wmono asegs m m1 ->
stk asegs m1 lo (usp + -544) -> client_consts m1 -> mem_inv asegs m1 ->
evt asegs (fun ms => exists (m2 : mem) (xra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
ms = MS (RA xra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6') F (Z_to_bv 64 0x9fa94) fc None m2 (seg_rom asegs)
/\ munch W m1 m2 /\ wmono asegs m1 m2 /\ mem_inv asegs m2 /\ stk asegs m2 lo (usp + -544)
/\ bits_rep asegs m2 A D (skip_bits b) /\ bits_ok (skip_bits b) /\ sb_buf_size (skip_bits b) = sb_buf_size b /\ client_consts m2)
(MS (RA xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0x9fa60) fc None m1 (seg_rom asegs)).
Proof.
intros b xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m1 REP OKB OBD DLO REM POS MU0 OF WM0 ST0 CC MI.
unfold R_A, A_wb_skip_table in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof ST0 as (STa & STb & _).
pose proof OBA as (OA0 & OA1 & _). pose proof OBT as (OT0 & OT1 & _). unfold APP_TOP, BITS_SIZEOF in *.
pose proof ATOP as ATOP'. unfold IMG_TOP in ATOP'.
pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof (munch_refl W m1) as MU. pose proof (wmono_refl asegs m1) as WM.
pose proof (aobj_munch asegs _ m m1 A 48 OBA MU0 (shfree_of_aobj asegs _ m A 48 OF OBA)) as OBA1.
pose proof (aobj_munch asegs _ m m1 D _ OBD MU0 (shfree_of_aobj asegs _ m D _ OF OBD)) as OBD1.
pose proof (aobj_munch asegs _ m m1 146560 32 OBT MU0 (shfree_of_aobj asegs _ m 146560 32 OF OBT)) as OBT1.
assert (CC1 : client_consts m1) by (unfold client_consts, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4)))).
ato 0x9fa68. astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -544) lo b 3 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP OKB ltac:(lia) OBA1 OBD1 ASH ltac:(lia) LOS ltac:(lia) ALO DLO).
all: try eassumption.
subst x. set (v := fst (speex_bits_unpack_unsigned b 3)) in *. set (b1 := snd (speex_bits_unpack_unsigned b 3)) in *.
assert (UE : speex_bits_unpack_unsigned b 3 = (v, b1)) by (unfold v, b1; destruct (speex_bits_unpack_unsigned b 3); reflexivity).
pose proof (speex_bits_unpack_unsigned_ok b 3 v b1 OKB ltac:(lia) UE) as (OK1 & VR & _ & _ & SZ1 & _). change (2^3) with 8 in VR.
pose proof (ub_exact b 3 OKB ltac:(lia) ltac:(lia)) as (_ & POS3 & _ & _). unfold ub in POS3. fold b1 in POS3.
ato 0x9fa74. rewrite ?(Z.mod_small v) by lia. rewrite ?Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
ato 0x9fa80. astep. chk_merge OBT1 4.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => match goal with MIc : mem_inv asegs mc |- _ => pose proof (wb_skip_read mc v MIc VR) as RD end end.
unfold A_wb_skip_table in RD. replace (146560 + 4 * v) with (146560 + v * 4) in RD by lia.
pose proof (wb_skip_range v VR) as TR.
ato 0x9fa90. rewrite sx32_small by (unfold int31; lia). rewrite unsigned_lit by lia. rewrite swrap32_small by lia.
match goal with R1 : bits_rep asegs ?mc A D b1 |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (aobj_munch asegs _ m1 mc A 48 OBA1 MU (shfree_of_aobj asegs _ m1 A 48 OF OBA1)) as OBA2;
astep;
call (speex_bits_advance_walk A D (usp + -544) lo b1 (znth wb_skip_table v + -4) _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc R1 OK1 ltac:(lia) OBA2 ASH)
end.
all: try eassumption. all: try lia.
{ unfold client_consts, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))). }
replace (ret_pc (Z_to_bv 64 653972)) with (Z_to_bv 64 653972) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
assert (ESK : speex_bits_advance b1 (znth wb_skip_table v + -4) = skip_bits b).
{ unfold skip_bits, ub, uv, SB_SUBMODE_BITS. fold v b1. f_equal; lia. }
rewrite ESK in *.
apply evt_done. do 17 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption|].
split; [eassumption|]. split; [rewrite <- ESK; apply (speex_bits_advance_ok b1 _ OK1); lia|]. split; [rewrite <- ESK, adv_size; exact SZ1|].
unfold client_consts, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))).
Qed.

Lemma nbA_skip2 : forall (b : bits_st ptr) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc m1,
bits_rep asegs m1 A D b -> bits_ok b -> aobj asegs m D (sb_buf_size b) -> D + sb_buf_size b <= lo ->
4 <= speex_bits_remaining b -> 1 <= bits_pos b ->
munch W m m1 -> offsh W -> wmono asegs m m1 ->
stk asegs m1 lo (usp + -544) -> client_consts m1 -> mem_inv asegs m1 ->
evt asegs (fun ms => exists (m2 : mem) (xra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
ms = MS (RA xra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6') F (Z_to_bv 64 0x9fae8) fc None m2 (seg_rom asegs)
/\ munch W m1 m2 /\ wmono asegs m1 m2 /\ mem_inv asegs m2 /\ stk asegs m2 lo (usp + -544)
/\ bits_rep asegs m2 A D (skip_bits b) /\ bits_ok (skip_bits b) /\ sb_buf_size (skip_bits b) = sb_buf_size b /\ client_consts m2)
(MS (RA xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0x9fab4) fc None m1 (seg_rom asegs)).
Proof.
intros b xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m1 REP OKB OBD DLO REM POS MU0 OF WM0 ST0 CC MI.
unfold R_A, A_wb_skip_table in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. pose proof ST0 as (STa & STb & _).
pose proof OBA as (OA0 & OA1 & _). pose proof OBT as (OT0 & OT1 & _). unfold APP_TOP, BITS_SIZEOF in *.
pose proof ATOP as ATOP'. unfold IMG_TOP in ATOP'.
pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof (munch_refl W m1) as MU. pose proof (wmono_refl asegs m1) as WM.
pose proof (aobj_munch asegs _ m m1 A 48 OBA MU0 (shfree_of_aobj asegs _ m A 48 OF OBA)) as OBA1.
pose proof (aobj_munch asegs _ m m1 D _ OBD MU0 (shfree_of_aobj asegs _ m D _ OF OBD)) as OBD1.
pose proof (aobj_munch asegs _ m m1 146560 32 OBT MU0 (shfree_of_aobj asegs _ m 146560 32 OF OBT)) as OBT1.
assert (CC1 : client_consts m1) by (unfold client_consts, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4)))).
ato 0x9fabc. astep.
call (speex_bits_unpack_unsigned_walk A D (usp + -544) lo b 3 _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP OKB ltac:(lia) OBA1 OBD1 ASH ltac:(lia) LOS ltac:(lia) ALO DLO).
all: try eassumption.
subst x. set (v := fst (speex_bits_unpack_unsigned b 3)) in *. set (b1 := snd (speex_bits_unpack_unsigned b 3)) in *.
assert (UE : speex_bits_unpack_unsigned b 3 = (v, b1)) by (unfold v, b1; destruct (speex_bits_unpack_unsigned b 3); reflexivity).
pose proof (speex_bits_unpack_unsigned_ok b 3 v b1 OKB ltac:(lia) UE) as (OK1 & VR & _ & _ & SZ1 & _). change (2^3) with 8 in VR.
pose proof (ub_exact b 3 OKB ltac:(lia) ltac:(lia)) as (_ & POS3 & _ & _). unfold ub in POS3. fold b1 in POS3.
ato 0x9fac8. rewrite ?(Z.mod_small v) by lia. rewrite ?Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
ato 0x9fad4. astep. chk_merge OBT1 4.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => match goal with MIc : mem_inv asegs mc |- _ => pose proof (wb_skip_read mc v MIc VR) as RD end end.
unfold A_wb_skip_table in RD. replace (146560 + 4 * v) with (146560 + v * 4) in RD by lia.
pose proof (wb_skip_range v VR) as TR.
ato 0x9fae4. rewrite sx32_small by (unfold int31; lia). rewrite unsigned_lit by lia. rewrite swrap32_small by lia.
match goal with R1 : bits_rep asegs ?mc A D b1 |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (aobj_munch asegs _ m1 mc A 48 OBA1 MU (shfree_of_aobj asegs _ m1 A 48 OF OBA1)) as OBA2;
astep;
call (speex_bits_advance_walk A D (usp + -544) lo b1 (znth wb_skip_table v + -4) _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc R1 OK1 ltac:(lia) OBA2 ASH)
end.
all: try eassumption. all: try lia.
{ unfold client_consts, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))). }
replace (ret_pc (Z_to_bv 64 654056)) with (Z_to_bv 64 654056) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
assert (ESK : speex_bits_advance b1 (znth wb_skip_table v + -4) = skip_bits b).
{ unfold skip_bits, ub, uv, SB_SUBMODE_BITS. fold v b1. f_equal; lia. }
rewrite ESK in *.
apply evt_done. do 17 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [eassumption|].
split; [eassumption|]. split; [rewrite <- ESK; apply (speex_bits_advance_ok b1 _ OK1); lia|]. split; [rewrite <- ESK, adv_size; exact SZ1|].
unfold client_consts, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4))).
Qed.
End Skip.
