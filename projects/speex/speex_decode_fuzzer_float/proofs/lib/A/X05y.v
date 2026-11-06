(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1dg X1df X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X081 X05l X05m X09f X06d X069.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition nbctl_armpc (c : Z) : Z :=
if c =? 0 then 0x9f054 else if c =? 3 then 0x9efc0 else if c =? 20 then 0x9f160 else if c =? 24 then 0x9f090
else if c =? 25 then 0x9f018 else if c =? 39 then 0x9eec8 else if c =? 100 then 0x9ec5c else if c =? 101 then 0x9f270
else if c =? 103 then 0x9f2f8 else if c =? 104 then 0x9f2dc else 0x9f20c.
Definition nbctl_code_ok (c : Z) : Prop :=
c = 0 \/ c = 3 \/ c = 20 \/ c = 24 \/ c = 25 \/ c = 39 \/ c = 100 \/ c = 101 \/ c = 103 \/ c = 104 \/ c = 105.

Definition nbctl_frame (v9 v8 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
[C8 v9; C8 v8; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition nbctl_at_arm (ra gp tp t0 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (S P c lo usp : Z) (m : mem) : machine_state -> Prop :=
fun ms1 => exists (t1 a0 a1 a2 a4 a5 : word) (m1 : mem),
ms1 = MS (mkR ra (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 S)
a0 a1 a2 (Z_to_bv 64 c) a4 a5 a6 a7 (Z_to_bv 64 (S + 2168)) (Z_to_bv 64 SHB) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (nbctl_armpc c)) fc None m1 (seg_rom asegs)
/\ rw_cells asegs m1 (usp + -80) (nbctl_frame (reg_get F 9) (reg_get F 8) s6 s5 s4 s3 s2 s1 s0 ra)
/\ munch [(usp + -80, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ stk asegs m1 lo (usp + -80)
/\ (c <> 39 -> a1 = Z_to_bv 64 (S + 2047)).

Lemma nbctl_entry : forall (S P c lo usp : Z) (hrest : list cell)
(ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
rw_cells asegs m S (C8 (Z_to_bv 64 A_speex_nb_mode) :: hrest) -> Z.of_nat (cells_size hrest) = 24 ->
aobj asegs m S 2968 -> S mod 8 = 0 -> aobj asegs m A_speex_nb_mode 96 ->
stk asegs m lo usp -> lo <= usp - 80 -> SH_HI <= lo -> usp < 2^63 ->
(S + 2968 <= lo \/ usp <= S) -> 0 < S -> S + 2968 < 2^63 ->
nbctl_code_ok c ->
client_consts m -> lib_consts m -> mem_inv asegs m ->
evt asegs (nbctl_at_arm ra gp tp t0 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc S P c lo usp m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 c) (Z_to_bv 64 P) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decoder_ctl) fc None m (seg_rom asegs)).
Proof.
intros until m. intros P0 HR OBS S8 OBM ST LO LOS SPH AP GS SB CODE (G1 & G2 & _) LC MI.
unfold A_speex_decoder_ctl, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof (lib_const m A_speex_nb_mode LC_speex_nb_mode LC ltac:(lc_in)) as ND. unfold LC_speex_nb_mode in ND.
assert (AL8 : A_speex_nb_mode mod 8 = 0) by reflexivity.
assert (MPR : 0x10000 <= A_speex_nb_mode < 0x652000) by (unfold A_speex_nb_mode; lia).
set (MP := A_speex_nb_mode) in *. clearbody MP.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'.
pose proof (munch_refl [(usp + -80, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -80, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 80%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 80 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0x9eb7c.
ato 0x9ebcc.
destruct CODE as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]].
1: ato 0x9f054. 2: ato 0x9efc0. 3: ato 0x9f160. 4: ato 0x9f090. 5: ato 0x9f018. 6: ato 0x9eec8.
7: ato 0x9ec5c. 8: ato 0x9f270. 9: ato 0x9f2f8. 10: ato 0x9f2dc. 11: ato 0x9f20c.
all: apply evt_done; unfold nbctl_at_arm, nbctl_armpc, nbctl_frame; cbn [Z.eqb Pos.eqb];
do 7 eexists; split; [reflexivity|]; split; [eassumption|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [assumption|];
intros NE; first [reflexivity | exfalso; apply NE; reflexivity].
Qed.

Lemma nbctl_exit : forall (SP : Z) (v9 v8 xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 : word)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
80 <= SP < 2^63 -> sp = Z_to_bv 64 (SP + -80) ->
rw_cells asegs m (SP + -80) (nbctl_frame v9 v8 xs6 xs5 xs4 xs3 xs2 xs1 xs0 xra) -> mem_inv asegs m ->
evt asegs (fun ms' => exists F', ms' = MS (mkR xra (Z_to_bv 64 SP) gp tp t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc xra) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9f328) fc None m (seg_rom asegs)).
Proof.
intros until m. intros HSP -> FR MI. unfold nbctl_frame in FR.
ato 0x9f354. astep.
apply evt_done. eexists. rewrite ?unsigned_lit by lia. replace (SP + -80 + 80) with SP by lia. reflexivity.
Qed.

Lemma nbctl_exit_get : forall (SP P : Z) (w : word) (v9 v8 xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 : word)
(ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
80 <= SP < 2^63 -> sp = Z_to_bv 64 (SP + -80) ->
rw_cells asegs m (SP + -80) (nbctl_frame v9 v8 xs6 xs5 xs4 xs3 xs2 xs1 xs0 xra) -> rw_cells asegs m P [C4 w] ->
(P + 4 <= SP + -80 \/ SP <= P) -> mem_inv asegs m ->
evt asegs (fun ms' => exists F' m', ms' = MS (mkR xra (Z_to_bv 64 SP) gp tp t0 t1 t2 xs0 xs1 a0 a1 a2 a3 a4 a5 a6 a7 xs2 xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc xra) fc None m' (seg_rom asegs)
/\ munch [(P, P + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' P [C4 a1]
/\ rw_cells asegs m' (SP + -80) (nbctl_frame v9 v8 xs6 xs5 xs4 xs3 xs2 xs1 xs0 xra))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 P) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9f324) fc None m (seg_rom asegs)).
Proof.
intros until m. intros HSP -> FR ARG AP MI. unfold nbctl_frame in FR.
pose proof (rw_cells_bound _ _ _ _ ARG) as B. cbn [cells_size csize Nat.add] in B.
pose proof (munch_refl [(P, P + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
astep.
ato 0x9f354. astep.
apply evt_done. do 2 eexists. rewrite ?unsigned_lit by lia. replace (SP + -80 + 80) with SP by lia.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; assumption.
Qed.

Section ARMS.
Variables (S P : Z) (ra sp gp tp t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
Let R (xa0 xa1 xa2 xa3 xa4 xa5 : word) : bvmap 5 word :=
mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 S) xa0 xa1 xa2 xa3 xa4 xa5 a6 a7 (Z_to_bv 64 (S + 2168)) (Z_to_bv 64 SHB) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.
Hypothesis MI : mem_inv asegs m.
Hypothesis SB : 0 < S /\ S + 2968 < 2^63.
Hypothesis PB : 0 <= P /\ P + 24 < 2^63.
Hypothesis OBS : aobj asegs m S 2968.
Hypothesis S8 : S mod 8 = 0.
Hypothesis SOFF : S + 2968 <= SH_LO \/ SH_HI <= S.

Lemma nbarm_get_frame_size : aobj asegs m P 4 -> P mod 4 = 0 ->
evt asegs (fun ms' => exists xa2 xa4 xa5, ms' = MS (R (Z_to_bv 64 0) (Z_to_bv 64 160) xa2 (Z_to_bv 64 3) xa4 xa5) F (Z_to_bv 64 0x9f324) fc None m (seg_rom asegs))
(MS (R a0 a1 a2 (Z_to_bv 64 3) a4 a5) F (Z_to_bv 64 (nbctl_armpc 3)) fc None m (seg_rom asegs)).
Proof using All.
intros OBP P4. unfold nbctl_armpc, R. cbn [Z.eqb Pos.eqb].
astep. astep. astep. astep. chk_merge OBP 4.
ato 0x9f324. apply evt_done. do 3 eexists. reflexivity.
Qed.

Lemma nbarm_get_lookahead : aobj asegs m P 4 -> P mod 4 = 0 ->
evt asegs (fun ms' => exists xa2 xa4 xa5, ms' = MS (R (Z_to_bv 64 0) (Z_to_bv 64 40) xa2 (Z_to_bv 64 39) xa4 xa5) F (Z_to_bv 64 0x9f324) fc None m (seg_rom asegs))
(MS (R a0 a1 a2 (Z_to_bv 64 39) a4 a5) F (Z_to_bv 64 (nbctl_armpc 39)) fc None m (seg_rom asegs)).
Proof using All.
intros OBP P4. unfold nbctl_armpc, R. cbn [Z.eqb Pos.eqb].
astep. astep. astep. astep. chk_merge OBP 4.
ato 0x9f324. apply evt_done. do 3 eexists. reflexivity.
Qed.

Lemma nbarm_get_sampling_rate : forall (MP c1 c2 c4 c5 : word) (sr : Z), aobj asegs m P 4 -> P mod 4 = 0 ->
rw_cells asegs m S [C8 MP; C4 c1; C4 c2; C4 (Z_to_bv 64 sr); C4 c4; C8 c5] -> - 2^31 <= sr < 2^31 ->
evt asegs (fun ms' => exists xa2 xa4 xa5, ms' = MS (R (Z_to_bv 64 0) (Z_to_bv 64 sr) xa2 (Z_to_bv 64 25) xa4 xa5) F (Z_to_bv 64 0x9f324) fc None m (seg_rom asegs))
(MS (R a0 a1 a2 (Z_to_bv 64 25) a4 a5) F (Z_to_bv 64 (nbctl_armpc 25)) fc None m (seg_rom asegs)).
Proof using All.
intros MP c1 c2 c4 c5 sr OBP P4 P0 SR. unfold nbctl_armpc, R. cbn [Z.eqb Pos.eqb].
ato 0x9f03c. astep. chk_merge OBP 4. astep. rewrite sx32_lit by lia.
apply evt_done. do 3 eexists. reflexivity.
Qed.

Lemma nbarm_set_enh : forall (w e1 : word) (pad : list byte) (sm sid lpc : word), aobj asegs m P 4 -> P mod 4 = 0 ->
rw_cells asegs m P [C4 w] -> rw_cells asegs m (S + 2232) [C4 e1; CB 4 pad; C8 sm; C4 sid; C4 lpc] ->
(P + 4 <= S \/ S + 2968 <= P) ->
evt asegs (fun ms' => exists m' xa1 xa2 xa4 xa5, ms' = MS (R (Z_to_bv 64 0) xa1 xa2 (Z_to_bv 64 0) xa4 xa5) F (Z_to_bv 64 0x9f328) fc None m' (seg_rom asegs)
/\ rw_cells asegs m' (S + 2232) [C4 e1; CB 4 pad; C8 sm; C4 sid; C4 (sx32 w)] /\ rw_cells asegs m' P [C4 w]
/\ munch [(S + 2252, S + 2256)] m m' /\ wmono asegs m m' /\ mem_inv asegs m')
(MS (R a0 a1 a2 (Z_to_bv 64 0) a4 a5) F (Z_to_bv 64 (nbctl_armpc 0)) fc None m (seg_rom asegs)).
Proof using All.
intros w e1 pad sm sid lpc OBP P4 ARG CFG AP. unfold nbctl_armpc, R. cbn [Z.eqb Pos.eqb].
pose proof (rw_cells_bound _ _ _ _ ARG) as B. cbn [cells_size csize Nat.add] in B.
pose proof (munch_refl [(S + 2252, S + 2256)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(S + 2252, S + 2256)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
astep. astep. astep. astep. chk_merge OBP 4.
ato 0x9f328.
apply evt_done. do 5 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). assumption.
Qed.

Lemma nbarm_set_sampling_rate : forall (w MP c1 c2 c3 c4 c5 : word), aobj asegs m P 4 -> P mod 4 = 0 ->
rw_cells asegs m P [C4 w] -> rw_cells asegs m S [C8 MP; C4 c1; C4 c2; C4 c3; C4 c4; C8 c5] ->
(P + 4 <= S \/ S + 2968 <= P) ->
evt asegs (fun ms' => exists m' xs1 xa1 xa2 xa4 xa5,
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 P) xs1 (Z_to_bv 64 0) xa1 xa2 (Z_to_bv 64 24) xa4 xa5 a6 a7 (Z_to_bv 64 (S + 2168)) (Z_to_bv 64 SHB)
s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x9f328) fc None m' (seg_rom asegs)
/\ rw_cells asegs m' S [C8 MP; C4 c1; C4 c2; C4 (sx32 w); C4 c4; C8 c5] /\ rw_cells asegs m' P [C4 w]
/\ munch [(S + 16, S + 20)] m m' /\ wmono asegs m m' /\ mem_inv asegs m')
(MS (R a0 a1 a2 (Z_to_bv 64 24) a4 a5) F (Z_to_bv 64 (nbctl_armpc 24)) fc None m (seg_rom asegs)).
Proof using All.
intros w MP c1 c2 c3 c4 c5 OBP P4 ARG P0 AP. unfold nbctl_armpc, R. cbn [Z.eqb Pos.eqb].
pose proof (rw_cells_bound _ _ _ _ ARG) as B. cbn [cells_size csize Nat.add] in B.
pose proof (munch_refl [(S + 16, S + 20)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(S + 16, S + 20)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
astep. astep. astep. astep. chk_merge OBP 4.
ato 0x9f328.
apply evt_done. do 6 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). assumption.
Qed.

Lemma nbarm_set_wideband : forall (w c1 c2 c3 c4 : word) (pad : list byte), aobj asegs m P 4 -> P mod 4 = 0 ->
rw_cells asegs m P [C4 w] -> rw_cells asegs m (S + 2948) [C4 c1; C4 c2; C4 c3; C4 c4; CB 4 pad] ->
(P + 4 <= S \/ S + 2968 <= P) ->
evt asegs (fun ms' => exists m' xa1 xa2 xa4 xa5, ms' = MS (R (Z_to_bv 64 0) xa1 xa2 (Z_to_bv 64 105) xa4 xa5) F (Z_to_bv 64 0x9f328) fc None m' (seg_rom asegs)
/\ rw_cells asegs m' (S + 2948) [C4 c1; C4 c2; C4 (sx32 w); C4 c4; CB 4 pad] /\ rw_cells asegs m' P [C4 w]
/\ munch [(S + 2956, S + 2960)] m m' /\ wmono asegs m m' /\ mem_inv asegs m')
(MS (R a0 a1 a2 (Z_to_bv 64 105) a4 a5) F (Z_to_bv 64 (nbctl_armpc 105)) fc None m (seg_rom asegs)).
Proof using All.
intros w c1 c2 c3 c4 pad OBP P4 ARG TL AP. unfold nbctl_armpc, R. cbn [Z.eqb Pos.eqb].
pose proof (rw_cells_bound _ _ _ _ ARG) as B. cbn [cells_size csize Nat.add] in B.
pose proof (munch_refl [(S + 2956, S + 2960)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(S + 2956, S + 2960)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
astep. astep. astep. astep. chk_merge OBP 4.
ato 0x9f328.
apply evt_done. do 5 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). assumption.
Qed.

Lemma nbarm_set_handler : forall (pad : word) (SH SD : Z) (cbs : list byte), aobj asegs m P 24 -> P mod 8 = 0 ->
rw_cells asegs m P [C4 (Z_to_bv 64 9); C4 pad; C8 (Z_to_bv 64 SH); C8 (Z_to_bv 64 SD)] ->
rw_cells asegs m (S + 2256) [CB 640 cbs] ->
(P + 24 <= S \/ S + 2968 <= P) ->
a1 = Z_to_bv 64 (S + 2047) ->
evt asegs (fun ms' => exists m' xa1 xa2 xa3 xa4 xa5, ms' = MS (R (Z_to_bv 64 0) xa1 xa2 xa3 xa4 xa5) F (Z_to_bv 64 0x9f328) fc None m' (seg_rom asegs)
/\ rw_cells asegs m' (S + 2256) [CB 360 (firstn 360 cbs); C4 (Z_to_bv 64 9); CB 4 (firstn 4 (skipn 364 cbs));
C8 (Z_to_bv 64 SH); C8 (Z_to_bv 64 SD); CB 256 (skipn 8 (skipn 12 (skipn 364 cbs)))]
/\ rw_cells asegs m' P [C4 (Z_to_bv 64 9); C4 pad; C8 (Z_to_bv 64 SH); C8 (Z_to_bv 64 SD)]
/\ munch [(S + 2616, S + 2640)] m m' /\ wmono asegs m m' /\ mem_inv asegs m')
(MS (R a0 a1 a2 (Z_to_bv 64 20) a4 a5) F (Z_to_bv 64 (nbctl_armpc 20)) fc None m (seg_rom asegs)).
Proof using All.
intros pad SH SD cbs OBP P8 ARG BL AP ->. unfold nbctl_armpc, R. cbn [Z.eqb Pos.eqb].
pose proof (rw_cells_bound _ _ _ _ ARG) as B. cbn [cells_size csize Nat.add] in B.
pose proof BL as BL0. destruct BL0 as [[[LEN _] _] _].
pose proof (munch_refl [(S + 2616, S + 2640)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(S + 2616, S + 2640)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
ato 0x9f18c. rewrite sx32_lit by lia.
ato 0x9f328.

replace (firstn 360 (firstn 368 cbs)) with (firstn 360 cbs) in BL by (rewrite firstn_firstn; reflexivity).
replace (skipn 364 (firstn 368 cbs)) with (firstn 4 (skipn 364 cbs)) in BL by (rewrite skipn_firstn_comm; reflexivity).
replace (skipn 376 cbs) with (skipn 12 (skipn 364 cbs)) in BL by (rewrite skipn_skipn; reflexivity).
apply evt_done. do 6 eexists. split; [reflexivity|]. repeat (split; [eassumption|]). assumption.
Qed.
End ARMS.
