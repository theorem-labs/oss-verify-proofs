(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1ch X1cg X1cr X1cs X1dg X1df X1ck X1co.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05q X05l X05k X082 X089 X0bn X0bk.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac tlia ::= (try unfold BITS_SIZEOF in * ); tlia_one.
Local Ltac slia ::= (try unfold BITS_SIZEOF in * ); first [ exact I | lia | split; [lia|exact I] ].
Local Notation mem := (word -> option byte).
Section Dec.
Context {ptr : Type}.
Implicit Types b : bits_st ptr.

Definition wbnd (hi : Z) (w : word) : Prop := exists v, w = Z_to_bv 64 v /\ 0 <= v < hi.

Definition scb_dec_post (zgp ztp zs0 zs2 : word) (F : bvmap 5 word) (fc : bv 32) (SP FB IND SGN A D PAR lo hs sbits : Z) (n : nat) (bF : bits_st ptr) (mI : mem) : machine_state -> Prop :=
fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s8' s11' t3' t4' t5' t6' : word) (m' : mem) (iws sws : list word),
ms' = MS (mkR ra' (Z_to_bv 64 SP) zgp ztp t0' t1' t2' zs0 (Z_to_bv 64 FB) a0' a1' a2' a3' a4' a5' a6' a7'
zs2 (Z_to_bv 64 hs) (Z_to_bv 64 (Z.shiftr (PAR + 16) 3 + SHB)) s5' (Z_to_bv 64 (PAR + 16))
s7' s8' (Z_to_bv 64 SHB) (Z_to_bv 64 0) s11' t3' t4' t5' t6')
F (Z_to_bv 64 0xac8d8) fc None m' (seg_rom asegs)
/\ munch [(SP + -32, SP); (SGN, SGN + 4 * Z.of_nat n); (IND, IND + 4 * Z.of_nat n); (A, A + 48)] mI m' /\ wmono asegs mI m' /\ mem_inv asegs m' /\ stk asegs m' lo SP
/\ rw_cells asegs m' IND (f32 iws) /\ length iws = n /\ Forall (wbnd (2 ^ sbits)) iws
/\ rw_cells asegs m' SGN (f32 sws) /\ length sws = n /\ Forall (wbnd 2) sws
/\ bits_rep asegs m' A D bF /\ bits_ok bF.

Lemma scb_dec_loop : forall (zgp ztp zs0 zs2 : word) (F : bvmap 5 word) (fc : bv 32) (SP FB IND SGN A D PAR lo ssz nbz scb hs sbits bsz : Z) (n : nat) (bF : bits_st ptr) (mI : mem),
FB = SP + 192 -> IND = SP + 128 -> SGN = SP + 32 -> SP mod 4 = 0 -> (n <= 8)%nat ->
hs = 0 \/ hs = 1 -> 1 <= sbits <= 8 ->
aobj asegs mI PAR 24 -> PAR mod 8 = 0 -> 0x10000 <= PAR -> PAR + 24 <= IMG_TOP ->
aobj asegs mI IND (4 * Z.of_nat n) -> aobj asegs mI SGN (4 * Z.of_nat n) ->
aobj asegs mI A 48 -> aobj asegs mI D bsz ->
(A + 48 <= SH_LO \/ SH_HI <= A) -> A + 48 <= lo -> D + bsz <= lo -> IMG_TOP <= A ->
lo <= SP - 32 -> SH_HI <= lo -> SP + 384 < 2^63 ->
forall (resti rests idw sdw : list word) (xi xs : word) (off kz : Z) b (zra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mc : mem),
off = 4 * Z.of_nat (length idw) -> kz = Z.of_nat (S (length resti)) -> length rests = length resti -> length sdw = length idw -> (length idw + 1 + length resti = n)%nat ->
bF = scbb (S (length resti)) hs sbits b ->
bits_rep asegs mc A D b -> bits_ok b -> sb_buf_size b = bsz ->
ro_cells asegs mc PAR (scb_par_cells ssz nbz scb sbits hs) -> rw_cells asegs mc (FB + 56) [C8 (Z_to_bv 64 A)] ->
rw_cells asegs mc IND (f32 idw) -> rw_cells asegs mc (IND + off) (f32 (xi :: resti)) ->
rw_cells asegs mc SGN (f32 sdw) -> rw_cells asegs mc (SGN + off) (f32 (xs :: rests)) ->
Forall (wbnd (2 ^ sbits)) idw -> Forall (wbnd 2) sdw ->
stk asegs mc lo SP -> client_consts mc -> mem_inv asegs mc ->
munch [(SP + -32, SP); (SGN, SGN + 4 * Z.of_nat n); (IND, IND + 4 * Z.of_nat n); (A, A + 48)] mI mc -> wmono asegs mI mc ->
evt asegs (scb_dec_post zgp ztp zs0 zs2 F fc SP FB IND SGN A D PAR lo hs sbits n bF mI)
(MS (mkR zra (Z_to_bv 64 SP) zgp ztp t0 t1 t2 zs0 (Z_to_bv 64 FB) a0 a1 a2 a3 a4 a5 a6 a7
zs2 (Z_to_bv 64 hs) (Z_to_bv 64 (Z.shiftr (PAR + 16) 3 + SHB)) (Z_to_bv 64 (SGN + off)) (Z_to_bv 64 (PAR + 16))
(Z_to_bv 64 (IND + off)) (Z_to_bv 64 (SGN + off)) (Z_to_bv 64 SHB) (Z_to_bv 64 kz) (Z_to_bv 64 (IND + off)) t3 t4 t5 t6)
F (Z_to_bv 64 0xac838) fc None mc (seg_rom asegs)).
Proof.
intros zgp ztp zs0 zs2 F fc SP FB IND SGN A D PAR lo ssz nbz scb hs sbits bsz n bF mI EFB EIND ESGN SP4 N8 HHS HSB OBP P8 PLO PHI OBI OBS OBA OBD ASH ALO DLO ATOP LO LOS SPH resti.
pose proof OBA as (OA0 & OA1 & _). pose proof OBD as (OD0 & OD1 & _). pose proof OBI as (OI0 & OI1 & _). pose proof OBS as (OS0 & OS1 & _). unfold APP_TOP in *.
pose proof LOS as LOS'. unfold SH_HI in LOS'. unfold IMG_TOP in *.
assert (OF : offsh [(SP + -32, SP); (SGN, SGN + 4 * Z.of_nat n); (IND, IND + 4 * Z.of_nat n); (A, A + 48)]).
{ clear - ASH LOS LO EIND ESGN N8. cbn. unfold SH_LO, SH_HI in *. lia. }
assert (P2 : 2 <= 2 ^ sbits <= 256).
{ clear - HSB. split; [change 2 with (2 ^ 1) at 1| change 256 with (2 ^ 8)]; apply Z.pow_le_mono_r; lia. }
assert (I4 : IND mod 4 = 0) by (clear - EIND SP4; Z.div_mod_to_equations; lia).
assert (S4 : SGN mod 4 = 0) by (clear - ESGN SP4; Z.div_mod_to_equations; lia).
hide_disj.
unfold hid in HHS. destruct HHS as [-> | ->].
2:{
induction resti as [|xi' resti IH]; intros rests idw sdw xi xs off kz b zra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mc
Hoff Hkz LRS LSV HN EBF REP OK SZ RPAR SLOT IDONE IX SDONE SX FI FS ST CC MI MU WM.
2:{
destruct rests as [|xs' rests]; [cbn [length] in LRS; lia|].
pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, scb_par_cells in *.
pose proof REP as ((rj0 & Lrj0 & OBJ) & (bs0 & DAT & Hbs0) & SIDE0). unfold bits_cells in OBJ.
pose proof ST as (STa & STb & _).
pose proof (rw_cells_bound _ _ _ _ IX) as BIX; rewrite cells_size_f32 in BIX; cbn [length] in BIX.
pose proof (rw_cells_bound _ _ _ _ SX) as BSX; rewrite cells_size_f32 in BSX; cbn [length] in BSX.
subst kz. cbn [length] in HN, LRS.
ato 0xac844.
rebase_bits A D b rj0 bs0. rewrite <- SZ in OBD1.
astep.
call (speex_bits_unpack_unsigned_walk A D SP lo b 1 _ zgp ztp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK ltac:(lia) OBA1 OBD1 (ASH : _ \/ _) ltac:(lia) LOS ltac:(lia) ALO ltac:(rewrite SZ; exact DLO)).
all: try eassumption.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
match goal with H : stk asegs _ lo _ |- _ => rename H into ST1 end.
change (snd (speex_bits_unpack_unsigned b 1)) with (ub b 1) in *. change (fst (speex_bits_unpack_unsigned b 1)) with (uv b 1) in *.
pose proof (ub_ok b 1 OK ltac:(lia)) as (OK1 & SZ1 & V1R). change (2 ^ 1) with 2 in V1R.
clear REP1 OBA1 OBD1 CC1.
match goal with H : bits_rep asegs _ A D (ub b 1) |- _ => destruct H as ((rj1 & Lrj1 & OBJ) & (bs1 & DAT & Hbs1) & SIDE1); unfold bits_cells in OBJ end.
assert (Lbs1 : Z.of_nat (length bs1) = bsz).
{ pose proof OK1 as OK'. unfold bits_ok in OK'. rewrite Hbs1, zlength_map_unsigned in OK'. lia. }
ato 0xac85c.
astep. chk_merge OBS 4.
rewrite f32_cons in SX. chunk_uncons SX as SX1.
ato 0xac874.
rewrite sx32_small by (unfold int31; lia).
rebase_bits A D (ub b 1) rj1 bs1. rewrite <- SZ, <- SZ1 in OBD1.
astep.
call (speex_bits_unpack_unsigned_walk A D SP lo (ub b 1) sbits _ zgp ztp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK1 ltac:(lia) OBA1 OBD1 (ASH : _ \/ _) ltac:(lia) LOS ltac:(lia) ALO ltac:(rewrite SZ1, SZ; exact DLO)).
all: try eassumption.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
match goal with H : stk asegs _ lo _ |- _ => rename H into ST2 end.
change (snd (speex_bits_unpack_unsigned (ub b 1) sbits)) with (ub (ub b 1) sbits) in *. change (fst (speex_bits_unpack_unsigned (ub b 1) sbits)) with (uv (ub b 1) sbits) in *.
pose proof (ub_ok (ub b 1) sbits OK1 ltac:(lia)) as (OK2 & SZ2 & V2R).
clear REP1 OBA1 OBD1 CC1.
ato 0xac884.
match goal with H : bits_rep asegs _ A D (ub (ub b 1) sbits) |- _ => destruct H as ((rj2 & Lrj2 & OBJ) & (bs2 & DAT & Hbs2) & SIDE2); unfold bits_cells in OBJ end.
assert (Lbs2 : Z.of_nat (length bs2) = bsz).
{ pose proof OK2 as OK'. unfold bits_ok in OK'. rewrite Hbs2, zlength_map_unsigned in OK'. lia. }
astep. chk_merge OBI 4.
rewrite f32_cons in IX. chunk_uncons IX as IX1.
ato 0xac8a0. astep.
cbn [length]. sh_if.
chunk_snoc IDONE IX1. rewrite f32_snoc in IDONE. chunk_snoc SDONE SX1. rewrite f32_snoc in SDONE.
replace (SGN + off + 4) with (SGN + (off + 4)) in * by lia. replace (IND + off + 4) with (IND + (off + 4)) in * by lia.
eapply (IH rests (idw ++ [_]) (sdw ++ [_]) xi' xs' (off + 4) _ (ub (ub b 1) sbits)).
1: (rewrite length_app; cbn [length]; lia).
1: (cbn [length]; lia).
1: lia.
1: (rewrite !length_app; cbn [length]; lia).
1: (rewrite length_app; cbn [length]; lia).
1: (rewrite EBF; reflexivity).
1: (split; [exists rj2; split; [exact Lrj2| exact OBJ]| split; [exists bs2; split; [exact DAT| exact Hbs2]| exact SIDE2]]).
1: exact OK2.
1: (rewrite SZ2, SZ1; exact SZ).
1: exact RPAR. 1: exact SLOT. 1: exact IDONE. 1: exact IX. 1: exact SDONE. 1: exact SX.
1: (apply Forall_app; split; [exact FI| constructor; [exists (uv (ub b 1) sbits); split; [reflexivity| exact V2R]| constructor]]).
1: (apply Forall_app; split; [exact FS| constructor; [exists (uv b 1); split; [reflexivity| exact V1R]| constructor]]).
1: exact ST2.
1: (unfold client_consts, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4)))).
1: assumption. 1: exact MU. 1: exact WM.
}
{
destruct rests as [|xs' rests]; [|cbn [length] in LRS; lia].
pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, scb_par_cells in *.
pose proof REP as ((rj0 & Lrj0 & OBJ) & (bs0 & DAT & Hbs0) & SIDE0). unfold bits_cells in OBJ.
pose proof ST as (STa & STb & _).
pose proof (rw_cells_bound _ _ _ _ IX) as BIX; rewrite cells_size_f32 in BIX; cbn [length] in BIX.
pose proof (rw_cells_bound _ _ _ _ SX) as BSX; rewrite cells_size_f32 in BSX; cbn [length] in BSX.
subst kz. cbn [length] in HN, LRS.
ato 0xac844.
rebase_bits A D b rj0 bs0. rewrite <- SZ in OBD1.
astep.
call (speex_bits_unpack_unsigned_walk A D SP lo b 1 _ zgp ztp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK ltac:(lia) OBA1 OBD1 (ASH : _ \/ _) ltac:(lia) LOS ltac:(lia) ALO ltac:(rewrite SZ; exact DLO)).
all: try eassumption.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
match goal with H : stk asegs _ lo _ |- _ => rename H into ST1 end.
change (snd (speex_bits_unpack_unsigned b 1)) with (ub b 1) in *. change (fst (speex_bits_unpack_unsigned b 1)) with (uv b 1) in *.
pose proof (ub_ok b 1 OK ltac:(lia)) as (OK1 & SZ1 & V1R). change (2 ^ 1) with 2 in V1R.
clear REP1 OBA1 OBD1 CC1.
match goal with H : bits_rep asegs _ A D (ub b 1) |- _ => destruct H as ((rj1 & Lrj1 & OBJ) & (bs1 & DAT & Hbs1) & SIDE1); unfold bits_cells in OBJ end.
assert (Lbs1 : Z.of_nat (length bs1) = bsz).
{ pose proof OK1 as OK'. unfold bits_ok in OK'. rewrite Hbs1, zlength_map_unsigned in OK'. lia. }
ato 0xac85c.
astep. chk_merge OBS 4.
rewrite f32_cons, f32_nil in SX.
ato 0xac874.
rewrite sx32_small by (unfold int31; lia).
rebase_bits A D (ub b 1) rj1 bs1. rewrite <- SZ, <- SZ1 in OBD1.
astep.
call (speex_bits_unpack_unsigned_walk A D SP lo (ub b 1) sbits _ zgp ztp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK1 ltac:(lia) OBA1 OBD1 (ASH : _ \/ _) ltac:(lia) LOS ltac:(lia) ALO ltac:(rewrite SZ1, SZ; exact DLO)).
all: try eassumption.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
match goal with H : stk asegs _ lo _ |- _ => rename H into ST2 end.
change (snd (speex_bits_unpack_unsigned (ub b 1) sbits)) with (ub (ub b 1) sbits) in *. change (fst (speex_bits_unpack_unsigned (ub b 1) sbits)) with (uv (ub b 1) sbits) in *.
pose proof (ub_ok (ub b 1) sbits OK1 ltac:(lia)) as (OK2 & SZ2 & V2R).
clear REP1 OBA1 OBD1 CC1.
ato 0xac884.
match goal with H : bits_rep asegs _ A D (ub (ub b 1) sbits) |- _ => destruct H as ((rj2 & Lrj2 & OBJ) & (bs2 & DAT & Hbs2) & SIDE2); unfold bits_cells in OBJ end.
assert (Lbs2 : Z.of_nat (length bs2) = bsz).
{ pose proof OK2 as OK'. unfold bits_ok in OK'. rewrite Hbs2, zlength_map_unsigned in OK'. lia. }
astep. chk_merge OBI 4.
rewrite f32_cons, f32_nil in IX.
ato 0xac8a0. astep.
cbn [length]. sh_if.
ato 0xac8d8.
chunk_snoc IDONE IX. rewrite f32_snoc in IDONE. chunk_snoc SDONE SX. rewrite f32_snoc in SDONE.
unfold scb_dec_post.
finish.
1: exact IDONE.
1: (rewrite length_app; cbn [length]; lia).
1: (apply Forall_app; split; [exact FI| constructor; [exists (uv (ub b 1) sbits); split; [reflexivity| exact V2R]| constructor]]).
1: exact SDONE.
1: (rewrite length_app; cbn [length]; lia).
1: (apply Forall_app; split; [exact FS| constructor; [exists (uv b 1); split; [reflexivity| exact V1R]| constructor]]).
1: (rewrite EBF; split; [exists rj2; split; [exact Lrj2| exact OBJ]| split; [exists bs2; split; [exact DAT| exact Hbs2]| exact SIDE2]]).
1: (rewrite EBF; exact OK2).
}
}
induction resti as [|xi' resti IH]; intros rests idw sdw xi xs off kz b zra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mc
Hoff Hkz LRS LSV HN EBF REP OK SZ RPAR SLOT IDONE IX SDONE SX FI FS ST CC MI MU WM.
{
destruct rests as [|xs' rests]; [|cbn [length] in LRS; lia].
pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, scb_par_cells in *.
pose proof REP as ((rj1 & Lrj1 & OBJ) & (bs1 & DAT & Hbs1) & SIDE1). unfold bits_cells in OBJ.
assert (Lbs1 : Z.of_nat (length bs1) = bsz).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs1, zlength_map_unsigned in OK'. lia. }
pose proof ST as (STa & STb & _).
pose proof (rw_cells_bound _ _ _ _ IX) as BIX; rewrite cells_size_f32 in BIX; cbn [length] in BIX.
pose proof (rw_cells_bound _ _ _ _ SX) as BSX; rewrite cells_size_f32 in BSX; cbn [length] in BSX.
subst kz. cbn [length] in HN, LRS.
ato 0xac85c.
astep. chk_merge OBS 4.
rewrite f32_cons, f32_nil in SX.
ato 0xac874.
rewrite sx32_small by (unfold int31; lia).
rebase_bits A D b rj1 bs1. rewrite <- SZ in OBD1.
astep.
call (speex_bits_unpack_unsigned_walk A D SP lo b sbits _ zgp ztp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK ltac:(lia) OBA1 OBD1 (ASH : _ \/ _) ltac:(lia) LOS ltac:(lia) ALO ltac:(rewrite SZ; exact DLO)).
all: try eassumption.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
match goal with H : stk asegs _ lo _ |- _ => rename H into ST2 end.
change (snd (speex_bits_unpack_unsigned b sbits)) with (ub b sbits) in *. change (fst (speex_bits_unpack_unsigned b sbits)) with (uv b sbits) in *.
pose proof (ub_ok b sbits OK ltac:(lia)) as (OK2 & SZ2 & V2R).
clear REP1 OBA1 OBD1 CC1.
ato 0xac884.
match goal with H : bits_rep asegs _ A D (ub b sbits) |- _ => destruct H as ((rj2 & Lrj2 & OBJ) & (bs2 & DAT & Hbs2) & SIDE2); unfold bits_cells in OBJ end.
assert (Lbs2 : Z.of_nat (length bs2) = bsz).
{ pose proof OK2 as OK'. unfold bits_ok in OK'. rewrite Hbs2, zlength_map_unsigned in OK'. lia. }
astep. chk_merge OBI 4.
rewrite f32_cons, f32_nil in IX.
ato 0xac8a0. astep.
cbn [length]. sh_if.
ato 0xac8d8.
chunk_snoc IDONE IX. rewrite f32_snoc in IDONE. chunk_snoc SDONE SX. rewrite f32_snoc in SDONE.
unfold scb_dec_post.
finish.
1: exact IDONE.
1: (rewrite length_app; cbn [length]; lia).
1: (apply Forall_app; split; [exact FI| constructor; [exists (uv b sbits); split; [reflexivity| exact V2R]| constructor]]).
1: exact SDONE.
1: (rewrite length_app; cbn [length]; lia).
1: (apply Forall_app; split; [exact FS| constructor; [exists 0; split; [reflexivity| lia]| constructor]]).
1: (rewrite EBF; split; [exists rj2; split; [exact Lrj2| exact OBJ]| split; [exists bs2; split; [exact DAT| exact Hbs2]| exact SIDE2]]).
1: (rewrite EBF; exact OK2).
}
{
destruct rests as [|xs' rests]; [cbn [length] in LRS; lia|].
pose proof CC as (G1 & G2 & G3 & G4).
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, scb_par_cells in *.
pose proof REP as ((rj1 & Lrj1 & OBJ) & (bs1 & DAT & Hbs1) & SIDE1). unfold bits_cells in OBJ.
assert (Lbs1 : Z.of_nat (length bs1) = bsz).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs1, zlength_map_unsigned in OK'. lia. }
pose proof ST as (STa & STb & _).
pose proof (rw_cells_bound _ _ _ _ IX) as BIX; rewrite cells_size_f32 in BIX; cbn [length] in BIX.
pose proof (rw_cells_bound _ _ _ _ SX) as BSX; rewrite cells_size_f32 in BSX; cbn [length] in BSX.
subst kz. cbn [length] in HN, LRS.
ato 0xac85c.
astep. chk_merge OBS 4.
rewrite f32_cons in SX. chunk_uncons SX as SX1.
ato 0xac874.
rewrite sx32_small by (unfold int31; lia).
rebase_bits A D b rj1 bs1. rewrite <- SZ in OBD1.
astep.
call (speex_bits_unpack_unsigned_walk A D SP lo b sbits _ zgp ztp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP1 OK ltac:(lia) OBA1 OBD1 (ASH : _ \/ _) ltac:(lia) LOS ltac:(lia) ALO ltac:(rewrite SZ; exact DLO)).
all: try eassumption.
match goal with H : ?v = Z_to_bv 64 (fst (speex_bits_unpack_unsigned _ _)) |- _ => subst v end.
match goal with H : stk asegs _ lo _ |- _ => rename H into ST2 end.
change (snd (speex_bits_unpack_unsigned b sbits)) with (ub b sbits) in *. change (fst (speex_bits_unpack_unsigned b sbits)) with (uv b sbits) in *.
pose proof (ub_ok b sbits OK ltac:(lia)) as (OK2 & SZ2 & V2R).
clear REP1 OBA1 OBD1 CC1.
ato 0xac884.
match goal with H : bits_rep asegs _ A D (ub b sbits) |- _ => destruct H as ((rj2 & Lrj2 & OBJ) & (bs2 & DAT & Hbs2) & SIDE2); unfold bits_cells in OBJ end.
assert (Lbs2 : Z.of_nat (length bs2) = bsz).
{ pose proof OK2 as OK'. unfold bits_ok in OK'. rewrite Hbs2, zlength_map_unsigned in OK'. lia. }
astep. chk_merge OBI 4.
rewrite f32_cons in IX. chunk_uncons IX as IX1.
ato 0xac8a0. astep.
cbn [length]. sh_if.
chunk_snoc IDONE IX1. rewrite f32_snoc in IDONE. chunk_snoc SDONE SX1. rewrite f32_snoc in SDONE.
replace (SGN + off + 4) with (SGN + (off + 4)) in * by lia. replace (IND + off + 4) with (IND + (off + 4)) in * by lia.
eapply (IH rests (idw ++ [_]) (sdw ++ [_]) xi' xs' (off + 4) _ (ub b sbits)).
1: (rewrite length_app; cbn [length]; lia).
1: (cbn [length]; lia).
1: lia.
1: (rewrite !length_app; cbn [length]; lia).
1: (rewrite length_app; cbn [length]; lia).
1: (rewrite EBF; reflexivity).
1: (split; [exists rj2; split; [exact Lrj2| exact OBJ]| split; [exists bs2; split; [exact DAT| exact Hbs2]| exact SIDE2]]).
1: exact OK2.
1: (rewrite SZ2; exact SZ).
1: exact RPAR. 1: exact SLOT. 1: exact IDONE. 1: exact IX. 1: exact SDONE. 1: exact SX.
1: (apply Forall_app; split; [exact FI| constructor; [exists (uv b sbits); split; [reflexivity| exact V2R]| constructor]]).
1: (apply Forall_app; split; [exact FS| constructor; [exists 0; split; [reflexivity| lia]| constructor]]).
1: exact ST2.
1: (unfold client_consts, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return; exact (conj G1 (conj G2 (conj G3 G4)))).
1: assumption. 1: exact MU. 1: exact WM.
}
Qed.
End Dec.
