(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1df X1ck X1co.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Notation mem := (word -> option byte).

Definition san1 (mn mx x : word) : word :=
let v := nan_box (low32 x) in
if fle_s mn v && fle_s v mx then x
else if flt_s v mn then fmv_s mn
else if flt_s mx v then fmv_s mx
else fzero_s.

Definition A_sanitize_values32 : Z := 0xa2fdc.

Definition sanitize_values32_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F0 : bvmap 5 word)
(usp lo p : Z) (xs : list word) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 g13 g14 fc' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 13 g13 (bvmap_set 14 g14 (bvmap_set 15 fzero_s F0))) (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(p, p + 4 * Z.of_nat (length xs)); (usp + -16, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp
/\ frm0 fc'
/\ rw_cells asegs m' p (f32 (map (san1 (reg_get F0 10) (reg_get F0 11)) xs)).

Ltac idx_norm B :=
repeat match type of B with
| context [@BV ?n ?z ?pf] =>
lazymatch pf with
| I => fail
| _ => replace (@BV n z pf) with (@BV n z I) in B by (apply bv_eq; reflexivity)
end
end.
Ltac san_leaf K :=
try (match goal with
| X : rw_cells _ _ _ (C4 _ :: C4 _ :: _) |- _ => chunk_uncons X as X1
| X : rw_cells _ _ _ (C4 _ :: f32 (_ :: _)) |- _ => chunk_uncons X as X1
end);
eapply K; try eassumption; unfold san1; cbv zeta;
(match goal with |- _ = _ => idtac | _ => fail 2 "not an eq goal" end);
repeat match goal with
| B : fle_s _ _ = _ |- _ => idx_norm B; rewrite B; clear B
| B : flt_s _ _ = _ |- _ => idx_norm B; rewrite B; clear B
end; cbn [andb]; reflexivity.
Ltac san_store K :=
norm_fchain; ato 0xa3040; astep;
match goal with OB : aobj _ _ _ _ |- _ => chk_merge OB 4 end;
ato 0xa3048; san_leaf K.
Ltac san_low K :=
ato 0xa3028; astep; let B3 := fresh "B3" in if_cases B3; bfact B3;
[ san_store K
| ato 0xa3034; astep; let B4 := fresh "B4" in if_cases B4; bfact B4; [ san_store K | san_store K ] ].
Ltac san_elem K :=
ato 0xa3008; astep;
match goal with OB : aobj _ _ _ _ |- _ => chk_merge OB 4 end;
ato 0xa3014; astep; let B1 := fresh "B1" in if_cases B1; bfact B1;
[ san_low K
| ato 0xa301c; astep; let B2 := fresh "B2" in if_cases B2; bfact B2;
[ ato 0xa3048; san_leaf K | san_low K ] ].

Section SI.
Variables (xs : list word) (p usp lo : Z).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F0 : bvmap 5 word.
Variable m : mem.
Local Notation mn := (reg_get F0 10).
Local Notation mx := (reg_get F0 11).
Local Notation n := (Z.of_nat (length xs)).
Hypothesis N1 : 1 <= n < 2^31.
Hypothesis OBX : aobj asegs m p (4 * n).
Hypothesis X4 : p mod 4 = 0.
Hypothesis LO : lo <= usp - 16.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis XSH : p + 4 * n <= SH_LO \/ SH_HI <= p.
Hypothesis XAP : p + 4 * n <= lo \/ usp <= p.
Local Notation POST := (sanitize_values32_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F0 usp lo p xs m).
Local Notation W := [(p, p + 4 * n); (usp + -16, usp)].

Lemma san_loop : forall rest done dn x (kz off : Z) (j0 : list byte) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 g13 g14 : word) fc m1,
xs = done ++ x :: rest -> dn = map (san1 mn mx) done -> length dn = length done ->
kz = Z.of_nat (S (length rest)) -> off = 4 * Z.of_nat (length done) ->
frm0 fc -> munch W m m1 -> offsh W -> wmono asegs m m1 -> mem_inv asegs m1 ->
stk asegs m1 lo (usp + -16) -> rw_cells asegs m1 (usp + -16) [CB 8 j0; C8 ra] ->
rw_cells asegs m1 p (f32 dn) -> rw_cells asegs m1 (p + off) (f32 (x :: rest)) ->
evt asegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (p + off)) (Z_to_bv 64 kz) (Z_to_bv 64 (p + off)) (Z_to_bv 64 SHB) a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 13 g13 (bvmap_set 14 g14 (bvmap_set 15 fzero_s F0)))
(Z_to_bv 64 0xa2ffc) fc None m1 (seg_rom asegs)).
Proof using N1 OBX X4 LO SPH XAP XSH.
induction rest as [|x' rest IH]; intros done dn x kz off j0 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 g13 g14 fc m1 Hxs Hdn LDN Hkz Hoff FRM MU OF WM MI ST FR DONE X;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (f_equal (@length word) Hxs) as HL; rewrite length_app in HL; cbn [length] in HL;
pose proof OBX as (OX0 & OX1 & _); unfold APP_TOP in *;
pose proof ST as (STa & STb & _); subst kz.
-
assert (TAIL : forall (y4 y5 y6 y7 h13 h14 : word) fc' m' (w : word),
frm0 fc' -> mem_inv asegs m' -> munch W m m' -> wmono asegs m m' ->
stk asegs m' lo (usp + -16) -> rw_cells asegs m' (usp + -16) [CB 8 j0; C8 ra] ->
rw_cells asegs m' p (f32 dn) -> rw_cells asegs m' (p + off) [C4 w] -> w = san1 mn mx x ->
evt asegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (p + off)) (Z_to_bv 64 (Z.of_nat (S (length (@nil word))))) (Z_to_bv 64 (p + off)) (Z_to_bv 64 SHB) y4 y5 y6 y7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 13 h13 (bvmap_set 14 h14 (bvmap_set 15 fzero_s F0)))
(Z_to_bv 64 0xa3048) fc' None m' (seg_rom asegs))).
{ clear FRM MI MU WM ST FR DONE X BX fc m1 STa STb. intros y4 y5 y6 y7 h13 h14 fc m1 w FRM MI MU WM ST FR DONE X ->.
pose proof ST as (STa & STb & _).
ato 0xa3054. astep. try sh_if.
ato 0xa3080. astep. release_frame FR ST usp. astep. astep.
unfold sanitize_values32_post. finish.
chunk_snoc DONE X. subst xs dn. rewrite map_app, f32_app. cbn [map]. rewrite f32_cons, f32_nil. exact DONE. }
rewrite !f32_cons, ?f32_nil in X.
san_elem TAIL.
-
assert (TAIL : forall (y4 y5 y6 y7 h13 h14 : word) fc' m' (w : word),
frm0 fc' -> mem_inv asegs m' -> munch W m m' -> wmono asegs m m' ->
stk asegs m' lo (usp + -16) -> rw_cells asegs m' (usp + -16) [CB 8 j0; C8 ra] ->
rw_cells asegs m' p (f32 dn) -> rw_cells asegs m' (p + off) [C4 w] -> w = san1 mn mx x ->
rw_cells asegs m' (p + off + 4) (f32 (x' :: rest)) ->
evt asegs POST
(MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (p + off)) (Z_to_bv 64 (Z.of_nat (S (length (x' :: rest))))) (Z_to_bv 64 (p + off)) (Z_to_bv 64 SHB) y4 y5 y6 y7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 13 h13 (bvmap_set 14 h14 (bvmap_set 15 fzero_s F0)))
(Z_to_bv 64 0xa3048) fc' None m' (seg_rom asegs))).
{ clear FRM MI MU WM ST FR DONE X BX fc m1 STa STb. intros y4 y5 y6 y7 h13 h14 fc m1 w FRM MI MU WM ST FR DONE X -> X'.
pose proof ST as (STa & STb & _).
pose proof (rw_cells_bound _ _ _ _ X') as BX'. rewrite cells_size_f32 in BX'. cbn [length] in BX'.
ato 0xa3054. astep. cbn [length]. sh_if.
chunk_snoc DONE X.
replace (p + off + 4) with (p + (off + 4)) in * by lia.
eapply (IH (done ++ [x]) (dn ++ [san1 mn mx x]) x' _ (off + 4)); try eassumption.
all: try (rewrite Hxs, <- app_assoc; reflexivity).
all: try (subst dn; rewrite map_app; reflexivity).
all: try (rewrite !length_app, LDN; reflexivity).
all: try (rewrite ?length_app; cbn [length]; lia).
all: try (rewrite f32_app, f32_cons, f32_nil; exact DONE). }
rewrite f32_cons in X.
san_elem TAIL.
Qed.

Lemma sanitize_values32_walk : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 f13 f14 f15 : word) fc,
rw_cells asegs m p (f32 xs) -> frm0 fc ->
stk asegs m lo usp -> IMG_TOP <= p ->
client_consts m -> mem_inv asegs m ->
evt asegs POST
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 13 f13 (bvmap_set 14 f14 (bvmap_set 15 f15 F0))) (Z_to_bv 64 A_sanitize_values32) fc None m (seg_rom asegs)).
Proof using N1 OBX X4 LO LOS SPH XSH XAP.
intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 f13 f14 f15 fc X FRM ST PTOP (G1 & G2 & _) MI.
unfold A_sanitize_values32, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'. pose proof XSH as XSH'. unfold SH_LO, SH_HI in XSH'. unfold IMG_TOP in PTOP.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX.
pose proof ST as (STa & STb & _).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh W) by (cbn; unfold SH_LO, SH_HI; lia).
destruct xs as [|x rest] eqn:Exs; [cbn [length] in N1; lia|]. rewrite <- Exs in *.
carve_frame 16%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
astep. astep. astep. rewrite ?signed_small64 by lia. try sh_if.
ato 0xa2ffc. norm_fchain.
replace (Z_to_bv 64 p) with (Z_to_bv 64 (p + 0)) by (rewrite Z.add_0_r; reflexivity).
replace p with (p + 0) in X at 1 by lia. rewrite Exs in X.
eapply (san_loop rest [] [] x _ 0); try eassumption; try reflexivity.
all: try (rewrite Exs; cbn [length]; lia).
all: try (rewrite f32_nil; apply rw_cells_nil; lia).
Qed.
End SI.
