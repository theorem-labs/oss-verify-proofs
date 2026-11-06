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

Fixpoint bw_tmp (gamma : word) (i : nat) : word :=
match i with O => fmv_s gamma | S i' => fmul_s RNE gamma (bw_tmp gamma i') end.
Definition bw_out (gamma : word) (i : nat) (x : word) : word := fmul_s RNE (bw_tmp gamma i) (nan_box (low32 x)).
Fixpoint bw_outs (gamma : word) (i : nat) (xs : list word) : list word :=
match xs with [] => [] | x :: xs' => bw_out gamma i x :: bw_outs gamma (S i) xs' end.
Lemma bw_outs_app : forall g a b i, bw_outs g i (a ++ b) = bw_outs g i a ++ bw_outs g (i + length a) b.
Proof. induction a as [|x a IH]; intros b i; cbn [bw_outs app length]; [rewrite Nat.add_0_r; reflexivity|]. rewrite IH, Nat.add_succ_r. reflexivity. Qed.
Lemma length_bw_outs : forall g xs i, length (bw_outs g i xs) = length xs.
Proof. intros g xs; induction xs; intros; cbn; [reflexivity|]. rewrite IHxs. reflexivity. Qed.
#[local] Hint Rewrite length_bw_outs : chunk_sizes.

Local Notation mem := (word -> option byte).
Definition A_bw_lpc : Z := 0xa2f34.

Definition bw_lpc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(usp lo pin pout : Z) (xs : list word) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 f14 f15 fc' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 14 f14 (bvmap_set 15 f15 F)) (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(pout, pout + 4 * Z.of_nat (length xs)); (usp + -16, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp
/\ frm0 fc'
/\ rw_cells asegs m' pout (f32 (bw_outs (reg_get F 10) 0 xs))
/\ (pin <> pout -> rw_cells asegs m' pin (f32 xs)).

Local Notation "# x" := (nan_box (low32 x)) (at level 9, format "# x").

Section S.
Variables (xs : list word) (pin pout usp lo : Z).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable m : mem.
Local Notation gamma := (reg_get F 10).
Local Notation n := (Z.of_nat (length xs)).
Hypothesis N1 : 1 <= n < 2^31.
Hypothesis OBX : aobj asegs m pin (4 * n).
Hypothesis OBY : aobj asegs m pout (4 * n).
Hypothesis X4 : pin mod 4 = 0.
Hypothesis Y4 : pout mod 4 = 0.
Hypothesis LO : lo <= usp - 16.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis YSH : pout + 4 * n <= SH_LO \/ SH_HI <= pout.
Hypothesis YAP : pout + 4 * n <= lo \/ usp <= pout.
Local Notation POST := (bw_lpc_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F usp lo pin pout xs m).
Local Notation W := [(pout, pout + 4 * n); (usp + -16, usp)].

Lemma bw_head : forall (Q : machine_state -> Prop) (off kz : Z) (x : word) (F0 : bvmap 5 word)
(zra t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) fc m1,
0 <= off -> off + 4 <= 4 * n -> off mod 4 = 0 ->
munch W m m1 -> offsh W ->
rw_cells asegs m1 (pin + off) (f32 [x]) ->
(forall a6' a7',
evt asegs Q
(MS (mkR zra (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (pin + off)) (Z_to_bv 64 (pout + off)) (Z_to_bv 64 kz)
(Z_to_bv 64 (pin + off)) (Z_to_bv 64 (pout + off)) (Z_to_bv 64 SHB) a6' a7'
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 14 (# x) F0) (Z_to_bv 64 0xa2f7c) fc None m1 (seg_rom asegs))) ->
evt asegs Q
(MS (mkR zra (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (pin + off)) (Z_to_bv 64 (pout + off)) (Z_to_bv 64 kz)
(Z_to_bv 64 (pin + off)) (Z_to_bv 64 (pout + off)) (Z_to_bv 64 SHB) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F0 (Z_to_bv 64 0xa2f58) fc None m1 (seg_rom asegs)).
Proof using OBX OBY X4 Y4.
clear N1 LO LOS SPH YSH YAP.
intros Q off kz x F0 zra t0 t1 t2 a6 a7 t3 t4 t5 t6 fc m1 O0 O1 O4 MU OF X K.
pose proof OBX as (OX0 & OX1 & _). pose proof OBY as (OY0 & OY1 & _). unfold APP_TOP in *.
rewrite !f32_cons, ?f32_nil in X.
ato 0xa2f64. astep. chk_merge OBX 4.
ato 0xa2f78. astep. chk_merge OBY 4.
apply K.
Qed.
End S.

Section SI.
Variables (xs : list word) (p usp lo : Z).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable m : mem.
Local Notation gamma := (reg_get F 10).
Local Notation n := (Z.of_nat (length xs)).
Hypothesis N1 : 1 <= n < 2^31.
Hypothesis OBX : aobj asegs m p (4 * n).
Hypothesis X4 : p mod 4 = 0.
Hypothesis LO : lo <= usp - 16.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis XSH : p + 4 * n <= SH_LO \/ SH_HI <= p.
Hypothesis XAP : p + 4 * n <= lo \/ usp <= p.
Local Notation POST := (bw_lpc_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F usp lo p p xs m).
Local Notation W := [(p, p + 4 * n); (usp + -16, usp)].

Lemma bw_loop_inplace : forall rest done dn x (kz off : Z) (j0 : list byte) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) fc m1,
xs = done ++ x :: rest -> dn = bw_outs gamma 0 done -> length dn = length done ->
kz = Z.of_nat (S (length rest)) -> off = 4 * Z.of_nat (length done) ->
frm0 fc -> munch W m m1 -> offsh W -> wmono asegs m m1 -> mem_inv asegs m1 ->
stk asegs m1 lo (usp + -16) -> rw_cells asegs m1 (usp + -16) [CB 8 j0; C8 ra] ->
rw_cells asegs m1 p (f32 dn) -> rw_cells asegs m1 (p + off) (f32 (x :: rest)) ->
evt asegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (p + off)) (Z_to_bv 64 (p + off)) (Z_to_bv 64 kz)
(Z_to_bv 64 (p + off)) (Z_to_bv 64 (p + off)) (Z_to_bv 64 SHB) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 14 (# x) (bvmap_set 15 (bw_tmp gamma (length done)) F))
(Z_to_bv 64 0xa2f7c) fc None m1 (seg_rom asegs)).
Proof using N1 OBX X4 LO SPH XAP XSH.
induction rest as [|x' rest IH]; intros done dn x kz off j0 t0 t1 t2 a6 a7 t3 t4 t5 t6 fc m1 Hxs Hdn LDN Hkz Hoff FRM MU OF WM MI ST FR DONE X;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (f_equal (@length word) Hxs) as HL; rewrite length_app in HL; cbn [length] in HL;
pose proof OBX as (OX0 & OX1 & _); unfold APP_TOP in *;
pose proof ST as (STa & STb & _); subst kz;
rewrite !f32_cons, ?f32_nil in X.
- ato 0xa2f9c. astep. try sh_if.
ato 0xa2fc8. astep. release_frame FR ST usp. astep. astep.
unfold bw_lpc_post. finish.
+ chunk_snoc DONE X. subst xs dn. rewrite bw_outs_app, f32_app. cbn [bw_outs Nat.add]. rewrite f32_cons, f32_nil. exact DONE.
+ intros Hne. exfalso. exact (Hne eq_refl).
- ato 0xa2f9c. astep. cbn [length]. sh_if.
chunk_uncons X as X1. chunk_snoc DONE X1.
replace (fmul_s RNE gamma (bw_tmp gamma (length done))) with (bw_tmp gamma (length (done ++ [x])))
by (rewrite length_app; cbn [length]; rewrite Nat.add_1_r; reflexivity).
replace (p + off + 4) with (p + (off + 4)) in * by lia.
pose proof X as XF. rewrite <- f32_cons in XF. chunk_split_f32 XF at 1%nat as X1'. clear XF.
apply (bw_head xs p p usp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m OBX OBX X4 X4 _ (off + 4) (Z.of_nat (S (S (length rest))) + -1) x');
[lia | lia | | exact MU | exact OF | exact X1' | ].
{ subst off. clear. Z.div_mod_to_equations. lia. }
intros a6' a7'. norm_fchain.
eapply (IH (done ++ [x]) (dn ++ [bw_out gamma (length done) x]) x' _ (off + 4)); try eassumption.
all: try (rewrite Hxs, <- app_assoc; reflexivity).
all: try (subst dn; rewrite bw_outs_app; cbn [bw_outs Nat.add]; reflexivity).
all: try (rewrite !length_app, LDN; reflexivity).
all: try (rewrite ?length_app; cbn [length]; lia).
all: try (rewrite f32_app, f32_cons, f32_nil; exact DONE).
Qed.

Lemma bw_lpc_walk_inplace : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) fc,
rw_cells asegs m p (f32 xs) -> frm0 fc ->
stk asegs m lo usp -> IMG_TOP <= p ->
client_consts m -> mem_inv asegs m ->
a2 = Z_to_bv 64 n ->
evt asegs POST
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 p) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_bw_lpc) fc None m (seg_rom asegs)).
Proof using N1 OBX X4 LO LOS SPH XSH XAP.
intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc X FRM ST PTOP (G1 & G2 & _) MI ->.
unfold A_bw_lpc, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'. pose proof XSH as XSH'. unfold SH_LO, SH_HI in XSH'. unfold IMG_TOP in PTOP.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX.
pose proof ST as (STa & STb & _).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh W) by (cbn; unfold SH_LO, SH_HI; lia).
destruct xs as [|x rest] eqn:Exs; [cbn [length] in N1; lia|]. rewrite <- Exs in *.
carve_frame 16%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
astep. astep. astep. rewrite ?signed_small64 by lia. try sh_if.
ato 0xa2f58.
replace (Z_to_bv 64 p) with (Z_to_bv 64 (p + 0)) by (rewrite Z.add_0_r; reflexivity).
replace p with (p + 0) in X at 1 by lia. rewrite Exs in X.
pose proof X as XF. chunk_split_f32 XF at 1%nat as X1. clear XF.
apply (bw_head xs p p usp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m OBX OBX X4 X4 _ 0 n x); [lia | lia | reflexivity | exact MU | exact OF | exact X1 | ].
intros a6' a7'.
eapply (bw_loop_inplace rest [] [] x _ 0); try eassumption; try reflexivity.
all: try (rewrite Exs; cbn [length]; lia).
all: try (rewrite f32_nil; apply rw_cells_nil; lia).
Qed.
End SI.

Section SD.
Variables (xs : list word) (pin pout usp lo : Z).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable m : mem.
Local Notation gamma := (reg_get F 10).
Local Notation n := (Z.of_nat (length xs)).
Hypothesis N1 : 1 <= n < 2^31.
Hypothesis OBX : aobj asegs m pin (4 * n).
Hypothesis OBY : aobj asegs m pout (4 * n).
Hypothesis X4 : pin mod 4 = 0.
Hypothesis Y4 : pout mod 4 = 0.
Hypothesis LO : lo <= usp - 16.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis YSH : pout + 4 * n <= SH_LO \/ SH_HI <= pout.
Hypothesis YAP : pout + 4 * n <= lo \/ usp <= pout.
Hypothesis XAP : pin + 4 * n <= lo \/ usp <= pin.
Hypothesis SEP : pin + 4 * n <= pout \/ pout + 4 * n <= pin.
Local Notation POST := (bw_lpc_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F usp lo pin pout xs m).
Local Notation W := [(pout, pout + 4 * n); (usp + -16, usp)].

Lemma bw_loop : forall rest orest done dn x o (kz off : Z) (j0 : list byte) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) fc m1,
xs = done ++ x :: rest -> dn = bw_outs gamma 0 done -> length dn = length done -> length orest = length rest ->
kz = Z.of_nat (S (length rest)) -> off = 4 * Z.of_nat (length done) ->
frm0 fc -> munch W m m1 -> offsh W -> wmono asegs m m1 -> mem_inv asegs m1 ->
stk asegs m1 lo (usp + -16) -> rw_cells asegs m1 (usp + -16) [CB 8 j0; C8 ra] ->
rw_cells asegs m1 pin (f32 done) -> rw_cells asegs m1 (pin + off) (f32 (x :: rest)) ->
rw_cells asegs m1 pout (f32 dn) -> rw_cells asegs m1 (pout + off) (f32 (o :: orest)) ->
evt asegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (pin + off)) (Z_to_bv 64 (pout + off)) (Z_to_bv 64 kz)
(Z_to_bv 64 (pin + off)) (Z_to_bv 64 (pout + off)) (Z_to_bv 64 SHB) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 14 (# x) (bvmap_set 15 (bw_tmp gamma (length done)) F))
(Z_to_bv 64 0xa2f7c) fc None m1 (seg_rom asegs)).
Proof using N1 OBX OBY X4 Y4 LO SPH YSH YAP XAP SEP.
induction rest as [|x' rest IH]; intros orest done dn x o kz off j0 t0 t1 t2 a6 a7 t3 t4 t5 t6 fc m1 Hxs Hdn LDN Lor Hkz Hoff FRM MU OF WM MI ST FR IDONE X ODONE Y;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ Y) as BY; rewrite cells_size_f32 in BY; cbn [length] in BY;
pose proof (f_equal (@length word) Hxs) as HL; rewrite length_app in HL; cbn [length] in HL;
pose proof OBX as (OX0 & OX1 & _); pose proof OBY as (OY0 & OY1 & _); unfold APP_TOP in *;
pose proof ST as (STa & STb & _); subst kz;
rewrite !f32_cons in Y.
- destruct orest; [|cbn in Lor; lia]. rewrite f32_nil in Y.
ato 0xa2f9c. astep. try sh_if.
ato 0xa2fc8. astep. release_frame FR ST usp. astep. astep.
rewrite !f32_cons, ?f32_nil in X.
unfold bw_lpc_post. finish.
+ chunk_snoc ODONE Y. subst xs dn. rewrite bw_outs_app, f32_app. cbn [bw_outs Nat.add]. rewrite f32_cons, f32_nil. exact ODONE.
+ intros _. chunk_snoc IDONE X. subst xs. rewrite f32_app, f32_cons, f32_nil. exact IDONE.
- destruct orest as [|o' orest]; [cbn in Lor; lia|]. rewrite f32_cons in Y.
ato 0xa2f9c. astep. cbn [length]. sh_if.
rewrite !f32_cons in X.
chunk_uncons X as X1. chunk_snoc IDONE X1.
chunk_uncons Y as Y1. chunk_snoc ODONE Y1.
replace (fmul_s RNE gamma (bw_tmp gamma (length done))) with (bw_tmp gamma (length (done ++ [x])))
by (rewrite length_app; cbn [length]; rewrite Nat.add_1_r; reflexivity).
replace (pin + off + 4) with (pin + (off + 4)) in * by lia. replace (pout + off + 4) with (pout + (off + 4)) in * by lia.
pose proof X as XF. rewrite <- f32_cons in XF. chunk_split_f32 XF at 1%nat as X1'. clear XF.
apply (bw_head xs pin pout usp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m OBX OBY X4 Y4 _ (off + 4) (Z.of_nat (S (S (length rest))) + -1) x');
[lia | lia | | exact MU | exact OF | exact X1' | ].
{ subst off. clear. Z.div_mod_to_equations. lia. }
intros a6' a7'. norm_fchain.
eapply (IH orest (done ++ [x]) (dn ++ [bw_out gamma (length done) x]) x' o' _ (off + 4)); try eassumption.
all: try (rewrite Hxs, <- app_assoc; reflexivity).
all: try (subst dn; rewrite bw_outs_app; cbn [bw_outs Nat.add]; reflexivity).
all: try (rewrite !length_app, LDN; reflexivity).
all: try (cbn in Lor; rewrite ?length_app; cbn [length]; lia).
all: try (rewrite f32_app, f32_cons, f32_nil; first [exact ODONE | exact IDONE]).
Qed.

Lemma bw_lpc_walk : forall (olds : list word) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) fc,
rw_cells asegs m pin (f32 xs) -> rw_cells asegs m pout (f32 olds) -> length olds = length xs -> frm0 fc ->
stk asegs m lo usp -> IMG_TOP <= pout ->
client_consts m -> mem_inv asegs m ->
a2 = Z_to_bv 64 n ->
evt asegs POST
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 pin) (Z_to_bv 64 pout) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_bw_lpc) fc None m (seg_rom asegs)).
Proof using N1 OBX OBY X4 Y4 LO LOS SPH YSH YAP XAP SEP.
intros olds t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc X Y LOL FRM ST PTOP (G1 & G2 & _) MI ->.
unfold A_bw_lpc, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'. pose proof YSH as YSH'. unfold SH_LO, SH_HI in YSH'. unfold IMG_TOP in PTOP.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX.
pose proof (rw_cells_bound _ _ _ _ Y) as BY; rewrite cells_size_f32 in BY.
pose proof ST as (STa & STb & _).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh W) by (cbn; unfold SH_LO, SH_HI; lia).
destruct xs as [|x rest] eqn:Exs; [cbn [length] in N1; lia|]. rewrite <- Exs in *.
destruct olds as [|o orest] eqn:Eolds; [rewrite Exs in LOL; cbn in LOL; lia|]. rewrite <- Eolds in *.
carve_frame 16%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
astep. astep. astep. rewrite ?signed_small64 by lia. try sh_if.
ato 0xa2f58.
replace (Z_to_bv 64 pin) with (Z_to_bv 64 (pin + 0)) by (rewrite Z.add_0_r; reflexivity).
replace (Z_to_bv 64 pout) with (Z_to_bv 64 (pout + 0)) by (rewrite Z.add_0_r; reflexivity).
replace pin with (pin + 0) in X at 1 by lia. replace pout with (pout + 0) in Y at 1 by lia. rewrite Exs in X. rewrite Eolds in Y, LOL.
pose proof X as XF. chunk_split_f32 XF at 1%nat as X1. clear XF.
apply (bw_head xs pin pout usp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m OBX OBY X4 Y4 _ 0 n x); [lia | lia | reflexivity | exact MU | exact OF | exact X1 | ].
intros a6' a7'.
eapply (bw_loop rest orest [] [] x o _ 0); try eassumption; try reflexivity.
all: try (rewrite Exs in *; cbn [length] in *; lia).
all: try (rewrite f32_nil; apply rw_cells_nil; lia).
Qed.
End SD.
