(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X05n.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

#[local] Hint Rewrite length_bw_outs : chunk_sizes.

Local Notation mem := (word -> option byte).
Definition B_bw_lpc : Z := 0xa5b5c.

Definition bw_lpc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(usp lo pin pout : Z) (xs : list word) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 f14 f15 fc' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 14 f14 (bvmap_set 15 f15 F)) (ret_pc ra) fc' None m' (seg_rom bsegs)
/\ munch [(pout, pout + 4 * Z.of_nat (length xs)); (usp + -16, usp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp
/\ frm0 fc'
/\ rw_cells bsegs m' pout (f32 (bw_outs (reg_get F 10) 0 xs))
/\ (pin <> pout -> rw_cells bsegs m' pin (f32 xs)).

Local Notation "# x" := (nan_box (low32 x)) (at level 9, format "# x").

Section S.
Variables (xs : list word) (pin pout usp lo : Z).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable m : mem.
Local Notation gamma := (reg_get F 10).
Local Notation n := (Z.of_nat (length xs)).
Hypothesis N1 : 1 <= n < 2^31.
Hypothesis OBX : aobj bsegs m pin (4 * n).
Hypothesis OBY : aobj bsegs m pout (4 * n).
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
(zra t4 t5 t6 : word) fc m1,
0 <= off -> off + 4 <= 4 * n -> off mod 4 = 0 -> 0 < pin -> 0 < pout ->
munch W m m1 -> offsh W ->
rw_cells bsegs m1 (pin + off) (f32 [x]) ->
(forall t4' t5',
evt bsegs Q
(MS (mkR zra (Z_to_bv 64 (usp + -16)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 (pin + off)) s0 s1 (Z_to_bv 64 pin) (Z_to_bv 64 pout) (Z_to_bv 64 kz)
(Z_to_bv 64 (pout + off)) (Z_to_bv 64 (pin + off)) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 SHB)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (pout + off)) t4' t5' t6)
(bvmap_set 14 (# x) F0) (Z_to_bv 64 0xa5bf4) fc None m1 (seg_rom bsegs))) ->
evt bsegs Q
(MS (mkR zra (Z_to_bv 64 (usp + -16)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 (pin + off)) s0 s1 (Z_to_bv 64 pin) (Z_to_bv 64 pout) (Z_to_bv 64 kz)
(Z_to_bv 64 (pout + off)) (Z_to_bv 64 (pin + off)) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 SHB)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (pout + off)) t4 t5 t6)
F0 (Z_to_bv 64 0xa5ba8) fc None m1 (seg_rom bsegs)).
Proof using OBX OBY X4 Y4.
clear N1 LO LOS SPH YSH YAP.
intros Q off kz x F0 zra t4 t5 t6 fc m1 O0 O1 O4 PX0 PY0 MU OF X K.
pose proof OBX as (OX0 & OX1 & _). pose proof OBY as (OY0 & OY1 & _). unfold APP_TOP in *.
rewrite !f32_cons, ?f32_nil in X.
assert (NZX : (pin + off <? 1) = false) by (apply Z.ltb_ge; lia).
assert (NZY : (pout + off <? 1) = false) by (apply Z.ltb_ge; lia).
astep. sh_if. astep. rewrite NZX. cbn [Z.b2z].
ato 0xa5bc8. astep. chk_merge OBX 4.
astep. sh_if. astep. rewrite NZY. cbn [Z.b2z].
ato 0xa5bf0. astep. chk_merge OBY 4.
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
Hypothesis OBX : aobj bsegs m p (4 * n).
Hypothesis X4 : p mod 4 = 0.
Hypothesis LO : lo <= usp - 16.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis XSH : p + 4 * n <= SH_LO \/ SH_HI <= p.
Hypothesis XAP : p + 4 * n <= lo \/ usp <= p.
Local Notation POST := (bw_lpc_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F usp lo p p xs m).
Local Notation W := [(p, p + 4 * n); (usp + -16, usp)].

Lemma bw_loop_inplace : forall rest done dn x (kz off : Z) (j0 : list byte) (t4 t5 t6 : word) fc m1,
xs = done ++ x :: rest -> dn = bw_outs gamma 0 done -> length dn = length done ->
kz = Z.of_nat (S (length rest)) -> off = 4 * Z.of_nat (length done) -> 0 < p ->
frm0 fc -> munch W m m1 -> offsh W -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
stk bsegs m1 lo (usp + -16) -> rw_cells bsegs m1 (usp + -16) [CB 8 j0; C8 ra] ->
rw_cells bsegs m1 p (f32 dn) -> rw_cells bsegs m1 (p + off) (f32 (x :: rest)) ->
evt bsegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 (p + off)) s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 p) (Z_to_bv 64 kz)
(Z_to_bv 64 (p + off)) (Z_to_bv 64 (p + off)) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 SHB)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (p + off)) t4 t5 t6)
(bvmap_set 14 (# x) (bvmap_set 15 (bw_tmp gamma (length done)) F))
(Z_to_bv 64 0xa5bf4) fc None m1 (seg_rom bsegs)).
Proof using N1 OBX X4 LO SPH XAP XSH.
induction rest as [|x' rest IH]; intros done dn x kz off j0 t4 t5 t6 fc m1 Hxs Hdn LDN Hkz Hoff P0 FRM MU OF WM MI ST FR DONE X;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (f_equal (@length word) Hxs) as HL; rewrite length_app in HL; cbn [length] in HL;
pose proof OBX as (OX0 & OX1 & _); unfold APP_TOP in *;
pose proof ST as (STa & STb & _); subst kz;
rewrite !f32_cons, ?f32_nil in X.
- ato 0xa5c14. astep. try sh_if.
ato 0xa5c40. astep. release_frame FR ST usp. astep. astep.
unfold bw_lpc_post. finish.
+ chunk_snoc DONE X. subst xs dn. rewrite bw_outs_app, f32_app. cbn [bw_outs Nat.add]. rewrite f32_cons, f32_nil. exact DONE.
+ intros Hne. exfalso. exact (Hne eq_refl).
- ato 0xa5c14. astep. cbn [length]. sh_if.
chunk_uncons X as X1. chunk_snoc DONE X1.
replace (fmul_s RNE gamma (bw_tmp gamma (length done))) with (bw_tmp gamma (length (done ++ [x])))
by (rewrite length_app; cbn [length]; rewrite Nat.add_1_r; reflexivity).
replace (p + off + 4) with (p + (off + 4)) in * by lia.
pose proof X as XF. rewrite <- f32_cons in XF. chunk_split_f32 XF at 1%nat as X1'. clear XF.
apply (bw_head xs p p usp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m OBX OBX X4 X4 _ (off + 4) (Z.of_nat (S (S (length rest))) + -1) x');
[lia | lia | | exact P0 | exact P0 | exact MU | exact OF | exact X1' | ].
{ subst off. clear. Z.div_mod_to_equations. lia. }
intros t4' t5'. norm_fchain.
eapply (IH (done ++ [x]) (dn ++ [bw_out gamma (length done) x]) x' _ (off + 4)); try eassumption.
all: try (rewrite Hxs, <- app_assoc; reflexivity).
all: try (subst dn; rewrite bw_outs_app; cbn [bw_outs Nat.add]; reflexivity).
all: try (rewrite !length_app, LDN; reflexivity).
all: try (rewrite ?length_app; cbn [length]; lia).
all: try (rewrite f32_app, f32_cons, f32_nil; exact DONE).
Qed.

Lemma bw_lpc_walk_inplace : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) fc,
rw_cells bsegs m p (f32 xs) -> frm0 fc ->
stk bsegs m lo usp -> IMG_TOP_B <= p ->
client_constsB m -> mem_inv bsegs m ->
a2 = Z_to_bv 64 n ->
evt bsegs POST
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 p) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 B_bw_lpc) fc None m (seg_rom bsegs)).
Proof using N1 OBX X4 LO LOS SPH XSH XAP.
intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc X FRM ST PTOP (G1 & G2 & _) MI ->.
unfold B_bw_lpc, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'. pose proof XSH as XSH'. unfold SH_LO, SH_HI in XSH'. unfold IMG_TOP_B in PTOP.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX.
pose proof ST as (STa & STb & _).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh W) by (cbn; unfold SH_LO, SH_HI; lia).
destruct xs as [|x rest] eqn:Exs; [cbn [length] in N1; lia|]. rewrite <- Exs in *.
carve_frame 16%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
astep. astep. astep. rewrite ?signed_small64 by lia. try sh_if.
assert (P0 : (0 <? p) = true) by (apply Z.ltb_lt; lia).
assert (P3 : (Z.land p 3 <? 1) = true) by (apply Z.ltb_lt; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; clear - X4; Z.div_mod_to_equations; lia).
ato 0xa5ba8. rewrite ?P0, ?P3. cbn [Z.b2z]. change (Z.land 1 1) with 1.
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
replace R with (mkR ra (Z_to_bv 64 (usp + -16)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 (p + 0)) s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 p) (Z_to_bv 64 n)
(Z_to_bv 64 (p + 0)) (Z_to_bv 64 (p + 0)) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 SHB)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (p + 0)) t4 t5 t6) by (rewrite Z.add_0_r; reflexivity)
end.
replace p with (p + 0) in X at 1 by lia. rewrite Exs in X.
pose proof X as XF. chunk_split_f32 XF at 1%nat as X1. clear XF.
apply (bw_head xs p p usp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m OBX OBX X4 X4 _ 0 n x); [lia | lia | reflexivity | lia | lia | exact MU | exact OF | exact X1 | ].
intros t4' t5'.
eapply (bw_loop_inplace rest [] [] x _ 0); try eassumption; try reflexivity.
all: try (rewrite Exs; cbn [length]; lia).
all: try (rewrite f32_nil; apply rw_cells_nil; lia).
all: try lia.
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
Hypothesis OBX : aobj bsegs m pin (4 * n).
Hypothesis OBY : aobj bsegs m pout (4 * n).
Hypothesis X4 : pin mod 4 = 0.
Hypothesis Y4 : pout mod 4 = 0.
Hypothesis LO : lo <= usp - 16.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis YSH : pout + 4 * n <= SH_LO \/ SH_HI <= pout.
Hypothesis YAP : pout + 4 * n <= lo \/ usp <= pout.
Hypothesis XAP : pin + 4 * n <= lo \/ usp <= pin.
Hypothesis SEP : pin + 4 * n <= pout \/ pout + 4 * n <= pin.
Hypothesis XPOS : 0 < pin.
Local Notation POST := (bw_lpc_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F usp lo pin pout xs m).
Local Notation W := [(pout, pout + 4 * n); (usp + -16, usp)].

Lemma bw_loop : forall rest orest done dn x o (kz off : Z) (j0 : list byte) (t4 t5 t6 : word) fc m1,
xs = done ++ x :: rest -> dn = bw_outs gamma 0 done -> length dn = length done -> length orest = length rest ->
kz = Z.of_nat (S (length rest)) -> off = 4 * Z.of_nat (length done) -> 0 < pin -> 0 < pout ->
frm0 fc -> munch W m m1 -> offsh W -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
stk bsegs m1 lo (usp + -16) -> rw_cells bsegs m1 (usp + -16) [CB 8 j0; C8 ra] ->
rw_cells bsegs m1 pin (f32 done) -> rw_cells bsegs m1 (pin + off) (f32 (x :: rest)) ->
rw_cells bsegs m1 pout (f32 dn) -> rw_cells bsegs m1 (pout + off) (f32 (o :: orest)) ->
evt bsegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 (pin + off)) s0 s1 (Z_to_bv 64 pin) (Z_to_bv 64 pout) (Z_to_bv 64 kz)
(Z_to_bv 64 (pout + off)) (Z_to_bv 64 (pin + off)) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 SHB)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (pout + off)) t4 t5 t6)
(bvmap_set 14 (# x) (bvmap_set 15 (bw_tmp gamma (length done)) F))
(Z_to_bv 64 0xa5bf4) fc None m1 (seg_rom bsegs)).
Proof using N1 OBX OBY X4 Y4 LO SPH YSH YAP XAP SEP.
induction rest as [|x' rest IH]; intros orest done dn x o kz off j0 t4 t5 t6 fc m1 Hxs Hdn LDN Lor Hkz Hoff PX0 PY0 FRM MU OF WM MI ST FR IDONE X ODONE Y;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ Y) as BY; rewrite cells_size_f32 in BY; cbn [length] in BY;
pose proof (f_equal (@length word) Hxs) as HL; rewrite length_app in HL; cbn [length] in HL;
pose proof OBX as (OX0 & OX1 & _); pose proof OBY as (OY0 & OY1 & _); unfold APP_TOP in *;
pose proof ST as (STa & STb & _); subst kz;
rewrite !f32_cons in Y.
- destruct orest; [|cbn in Lor; lia]. rewrite f32_nil in Y.
ato 0xa5c14. astep. try sh_if.
ato 0xa5c40. astep. release_frame FR ST usp. astep. astep.
rewrite !f32_cons, ?f32_nil in X.
unfold bw_lpc_post. finish.
+ chunk_snoc ODONE Y. subst xs dn. rewrite bw_outs_app, f32_app. cbn [bw_outs Nat.add]. rewrite f32_cons, f32_nil. exact ODONE.
+ intros _. chunk_snoc IDONE X. subst xs. rewrite f32_app, f32_cons, f32_nil. exact IDONE.
- destruct orest as [|o' orest]; [cbn in Lor; lia|]. rewrite f32_cons in Y.
ato 0xa5c14. astep. cbn [length]. sh_if.
rewrite !f32_cons in X.
chunk_uncons X as X1. chunk_snoc IDONE X1.
chunk_uncons Y as Y1. chunk_snoc ODONE Y1.
replace (fmul_s RNE gamma (bw_tmp gamma (length done))) with (bw_tmp gamma (length (done ++ [x])))
by (rewrite length_app; cbn [length]; rewrite Nat.add_1_r; reflexivity).
replace (pin + off + 4) with (pin + (off + 4)) in * by lia. replace (pout + off + 4) with (pout + (off + 4)) in * by lia.
pose proof X as XF. rewrite <- f32_cons in XF. chunk_split_f32 XF at 1%nat as X1'. clear XF.
apply (bw_head xs pin pout usp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m OBX OBY X4 Y4 _ (off + 4) (Z.of_nat (S (S (length rest))) + -1) x');
[lia | lia | | exact PX0 | exact PY0 | exact MU | exact OF | exact X1' | ].
{ subst off. clear. Z.div_mod_to_equations. lia. }
intros t4' t5'. norm_fchain.
eapply (IH orest (done ++ [x]) (dn ++ [bw_out gamma (length done) x]) x' o' _ (off + 4)); try eassumption.
all: try (rewrite Hxs, <- app_assoc; reflexivity).
all: try (subst dn; rewrite bw_outs_app; cbn [bw_outs Nat.add]; reflexivity).
all: try (rewrite !length_app, LDN; reflexivity).
all: try (cbn in Lor; rewrite ?length_app; cbn [length]; lia).
all: try (rewrite f32_app, f32_cons, f32_nil; first [exact ODONE | exact IDONE]).
Qed.

Lemma bw_lpc_walk : forall (olds : list word) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) fc,
rw_cells bsegs m pin (f32 xs) -> rw_cells bsegs m pout (f32 olds) -> length olds = length xs -> frm0 fc ->
stk bsegs m lo usp -> IMG_TOP_B <= pout ->
client_constsB m -> mem_inv bsegs m ->
a2 = Z_to_bv 64 n ->
evt bsegs POST
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 pin) (Z_to_bv 64 pout) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 B_bw_lpc) fc None m (seg_rom bsegs)).
Proof using N1 OBX OBY X4 Y4 LO LOS SPH YSH YAP XAP SEP XPOS.
intros olds t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc X Y LOL FRM ST PTOP (G1 & G2 & _) MI ->.
unfold B_bw_lpc, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'. pose proof YSH as YSH'. unfold SH_LO, SH_HI in YSH'. unfold IMG_TOP_B in PTOP.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX.
pose proof (rw_cells_bound _ _ _ _ Y) as BY; rewrite cells_size_f32 in BY.
pose proof ST as (STa & STb & _).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh W) by (cbn; unfold SH_LO, SH_HI; lia).
destruct xs as [|x rest] eqn:Exs; [cbn [length] in N1; lia|]. rewrite <- Exs in *.
destruct olds as [|o orest] eqn:Eolds; [rewrite Exs in LOL; cbn in LOL; lia|]. rewrite <- Eolds in *.
carve_frame 16%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
astep. astep. astep. rewrite ?signed_small64 by lia. try sh_if.
assert (PX0 : (0 <? pin) = true) by (apply Z.ltb_lt; lia).
assert (PY0 : (0 <? pout) = true) by (apply Z.ltb_lt; lia).
assert (PX3 : (Z.land pin 3 <? 1) = true) by (apply Z.ltb_lt; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; clear - X4; Z.div_mod_to_equations; lia).
assert (PY3 : (Z.land pout 3 <? 1) = true) by (apply Z.ltb_lt; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; clear - Y4; Z.div_mod_to_equations; lia).
ato 0xa5ba8. rewrite ?PX0, ?PY0, ?PX3, ?PY3. cbn [Z.b2z]. change (Z.land 1 1) with 1.
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
replace R with (mkR ra (Z_to_bv 64 (usp + -16)) gp tp (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 (pin + 0)) s0 s1 (Z_to_bv 64 pin) (Z_to_bv 64 pout) (Z_to_bv 64 n)
(Z_to_bv 64 (pout + 0)) (Z_to_bv 64 (pin + 0)) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 SHB)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (pout + 0)) t4 t5 t6) by (rewrite !Z.add_0_r; reflexivity)
end.
replace pin with (pin + 0) in X at 1 by lia. replace pout with (pout + 0) in Y at 1 by lia. rewrite Exs in X. rewrite Eolds in Y, LOL.
pose proof X as XF. chunk_split_f32 XF at 1%nat as X1. clear XF.
apply (bw_head xs pin pout usp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m OBX OBY X4 Y4 _ 0 n x); [lia | lia | reflexivity | lia | lia | exact MU | exact OF | exact X1 | ].
intros t4' t5'.
eapply (bw_loop rest orest [] [] x o _ 0); try eassumption; try reflexivity.
all: try (rewrite Exs in *; cbn [length] in *; lia).
all: try (rewrite f32_nil; apply rw_cells_nil; lia).
all: try lia.
Qed.
End SD.
