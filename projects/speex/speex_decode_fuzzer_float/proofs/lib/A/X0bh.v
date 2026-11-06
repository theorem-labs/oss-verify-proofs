(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation mem := (word -> option byte).
Local Notation "# x" := (nan_box (low32 x)) (at level 9, format "# x").

Definition smul (scale x : word) : word := fmul_s RNE scale (nan_box (low32 x)).

Definition A_signal_mul : Z := 0xa3314.

Definition signal_mul_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(usp lo p : Z) (xs : list word) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 f15 fc' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 15 f15 F) (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(p, p + 4 * Z.of_nat (length xs)); (usp + -16, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp
/\ frm0 fc'
/\ rw_cells asegs m' p (f32 (map (smul (reg_get F 10)) xs)).

Section SI.
Variables (xs : list word) (p usp lo : Z).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable m : mem.
Local Notation scale := (reg_get F 10).
Local Notation n := (Z.of_nat (length xs)).
Hypothesis N1 : 1 <= n < 2^31.
Hypothesis OBX : aobj asegs m p (4 * n).
Hypothesis X4 : p mod 4 = 0.
Hypothesis LO : lo <= usp - 16.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis XSH : p + 4 * n <= SH_LO \/ SH_HI <= p.
Hypothesis XAP : p + 4 * n <= lo \/ usp <= p.
Local Notation POST := (signal_mul_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F usp lo p xs m).
Local Notation W := [(p, p + 4 * n); (usp + -16, usp)].

Lemma sm_head : forall (Q : machine_state -> Prop) (off kz : Z) (x : word) (F0 : bvmap 5 word)
(zra t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) fc m1,
0 <= off -> off + 4 <= 4 * n -> off mod 4 = 0 ->
munch W m m1 -> offsh W ->
rw_cells asegs m1 (p + off) (f32 [x]) ->
(forall a6' a7',
evt asegs Q
(MS (mkR zra (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (p + off)) (Z_to_bv 64 (p + off)) (Z_to_bv 64 kz)
(Z_to_bv 64 (p + off)) (Z_to_bv 64 (p + off)) (Z_to_bv 64 SHB) a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 15 (# x) F0) (Z_to_bv 64 0xa3358) fc None m1 (seg_rom asegs))) ->
evt asegs Q
(MS (mkR zra (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (p + off)) (Z_to_bv 64 (p + off)) (Z_to_bv 64 kz)
(Z_to_bv 64 (p + off)) (Z_to_bv 64 (p + off)) (Z_to_bv 64 SHB) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F0 (Z_to_bv 64 0xa3334) fc None m1 (seg_rom asegs)).
Proof using OBX X4.
clear N1 LO LOS SPH XSH XAP.
intros Q off kz x F0 zra t0 t1 t2 a6 a7 t3 t4 t5 t6 fc m1 O0 O1 O4 MU OF X K.
pose proof OBX as (OX0 & OX1 & _). unfold APP_TOP in *.
rewrite !f32_cons, ?f32_nil in X.
ato 0xa3340. astep. chk_merge OBX 4.
ato 0xa3354. astep. chk_merge OBX 4.
apply K.
Qed.

Lemma sm_loop : forall rest done dn x (kz off : Z) (j0 : list byte) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) fc m1,
xs = done ++ x :: rest -> dn = map (smul scale) done -> length dn = length done ->
kz = Z.of_nat (S (length rest)) -> off = 4 * Z.of_nat (length done) ->
frm0 fc -> munch W m m1 -> offsh W -> wmono asegs m m1 -> mem_inv asegs m1 ->
stk asegs m1 lo (usp + -16) -> rw_cells asegs m1 (usp + -16) [CB 8 j0; C8 ra] ->
rw_cells asegs m1 p (f32 dn) -> rw_cells asegs m1 (p + off) (f32 (x :: rest)) ->
evt asegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (p + off)) (Z_to_bv 64 (p + off)) (Z_to_bv 64 kz)
(Z_to_bv 64 (p + off)) (Z_to_bv 64 (p + off)) (Z_to_bv 64 SHB) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 15 (# x) F)
(Z_to_bv 64 0xa3358) fc None m1 (seg_rom asegs)).
Proof using N1 OBX X4 LO SPH XAP XSH.
induction rest as [|x' rest IH]; intros done dn x kz off j0 t0 t1 t2 a6 a7 t3 t4 t5 t6 fc m1 Hxs Hdn LDN Hkz Hoff FRM MU OF WM MI ST FR DONE X;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (f_equal (@length word) Hxs) as HL; rewrite length_app in HL; cbn [length] in HL;
pose proof OBX as (OX0 & OX1 & _); unfold APP_TOP in *;
pose proof ST as (STa & STb & _); subst kz;
rewrite !f32_cons, ?f32_nil in X.
- ato 0xa3374. astep. try sh_if.
ato 0xa33a0. astep. release_frame FR ST usp. astep. astep.
unfold signal_mul_post. finish.
chunk_snoc DONE X. subst xs dn. rewrite map_app, f32_app. cbn [map]. rewrite f32_cons, f32_nil. exact DONE.
- ato 0xa3374. astep. cbn [length]. sh_if.
chunk_uncons X as X1. chunk_snoc DONE X1.
replace (p + off + 4) with (p + (off + 4)) in * by lia.
pose proof X as XF. rewrite <- f32_cons in XF. chunk_split_f32 XF at 1%nat as X1'. clear XF.
apply (sm_head _ (off + 4) (Z.of_nat (S (S (length rest))) + -1) x'); [lia | lia | | exact MU | exact OF | exact X1' | ].
{ subst off. clear. Z.div_mod_to_equations. lia. }
intros a6' a7'. norm_fchain.
eapply (IH (done ++ [x]) (dn ++ [smul scale x]) x' _ (off + 4)); try eassumption.
all: try (rewrite Hxs, <- app_assoc; reflexivity).
all: try (rewrite ?length_app; cbn [length]; lia).
all: try (subst dn; rewrite map_app; reflexivity).
all: try (rewrite !length_app, LDN; reflexivity).
all: try (rewrite f32_app, f32_cons, f32_nil; exact DONE).
Qed.

Lemma signal_mul_walk : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) fc,
rw_cells asegs m p (f32 xs) -> frm0 fc ->
stk asegs m lo usp -> IMG_TOP <= p ->
client_consts m -> mem_inv asegs m ->
a2 = Z_to_bv 64 n ->
evt asegs POST
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 p) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_signal_mul) fc None m (seg_rom asegs)).
Proof using N1 OBX X4 LO LOS SPH XSH XAP.
intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc X FRM ST PTOP (G1 & G2 & _) MI ->.
unfold A_signal_mul, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'. pose proof XSH as XSH'. unfold SH_LO, SH_HI in XSH'. unfold IMG_TOP in PTOP.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX.
pose proof ST as (STa & STb & _).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh W) by (cbn; unfold SH_LO, SH_HI; lia).
destruct xs as [|x rest] eqn:Exs; [cbn [length] in N1; lia|]. rewrite <- Exs in *.
carve_frame 16%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
astep. astep. astep. rewrite ?signed_small64 by lia. try sh_if.
ato 0xa3334.
replace (Z_to_bv 64 p) with (Z_to_bv 64 (p + 0)) by (rewrite Z.add_0_r; reflexivity).
replace p with (p + 0) in X at 1 by lia. rewrite Exs in X.
pose proof X as XF. chunk_split_f32 XF at 1%nat as X1. clear XF.
apply (sm_head _ 0 n x); [lia | lia | reflexivity | exact MU | exact OF | exact X1 | ].
intros a6' a7'.
eapply (sm_loop rest [] [] x _ 0); try eassumption; try reflexivity.
all: try (rewrite Exs; cbn [length]; lia).
all: try (rewrite f32_nil; apply rw_cells_nil; lia).
Qed.
End SI.
