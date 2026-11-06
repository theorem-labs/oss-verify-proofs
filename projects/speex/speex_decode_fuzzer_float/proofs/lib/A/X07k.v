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
Local Notation "# x" := (nan_box (low32 x)) (at level 9, format "# x").

Record hpc := HPC { hc_n0 : word; hc_n1 : word; hc_n2 : word; hc_d1 : word; hc_d2 : word }.
Definition hp_coefs (filtID : Z) : hpc :=
if (filtID =? 0)%Z then HPC (Z_to_bv 64 18446744070479208398) (Z_to_bv 64 18446744072635080738) (Z_to_bv 64 18446744070479208398) (Z_to_bv 64 18446744070487581236) (Z_to_bv 64 18446744072625994785)
else if (filtID =? 1)%Z then HPC (Z_to_bv 64 18446744070479341274) (Z_to_bv 64 18446744072635212439) (Z_to_bv 64 18446744070479341274) (Z_to_bv 64 18446744070487712350) (Z_to_bv 64 18446744072626258691)
else if (filtID =? 2)%Z then HPC (Z_to_bv 64 18446744070479387747) (Z_to_bv 64 18446744072635259919) (Z_to_bv 64 18446744070479387747) (Z_to_bv 64 18446744070487767295) (Z_to_bv 64 18446744072626339557)
else if (filtID =? 3)%Z then HPC (Z_to_bv 64 18446744070479710205) (Z_to_bv 64 18446744072635581370) (Z_to_bv 64 18446744070479710205) (Z_to_bv 64 18446744070488093444) (Z_to_bv 64 18446744072626973568)
else HPC (Z_to_bv 64 18446744070477924270) (Z_to_bv 64 18446744072633796526) (Z_to_bv 64 18446744070477924270) (Z_to_bv 64 18446744070483041321) (Z_to_bv 64 18446744072615643578).

Definition hp_v (c : hpc) (st : word * word) (x : word) : word := fmadd_s RNE (hc_n0 c) (# x) (# (fst st)).
Definition hp_next (c : hpc) (st : word * word) (x : word) : word * word :=
(fmadd_s RNE (hc_d1 c) (hp_v c st x) (fmadd_s RNE (hc_n1 c) (# x) (# (snd st))),
fmadd_s RNE (hc_n2 c) (# x) (fmul_s RNE (hp_v c st x) (hc_d2 c))).
Fixpoint hp_st (c : hpc) (st : word * word) (xs : list word) : word * word :=
match xs with [] => st | x :: xs' => hp_st c (hp_next c st x) xs' end.
Fixpoint hp_ys (c : hpc) (st : word * word) (xs : list word) : list word :=
match xs with [] => [] | x :: xs' => hp_v c st x :: hp_ys c (hp_next c st x) xs' end.
Lemma hp_st_app : forall c a b st, hp_st c st (a ++ b) = hp_st c (hp_st c st a) b.
Proof. induction a; intros; cbn; [reflexivity| apply IHa]. Qed.
Lemma hp_ys_app : forall c a b st, hp_ys c st (a ++ b) = hp_ys c st a ++ hp_ys c (hp_st c st a) b.
Proof. induction a; intros; cbn; [reflexivity|]. rewrite IHa. reflexivity. Qed.
Lemma length_hp_ys : forall c xs st, length (hp_ys c st xs) = length xs.
Proof. induction xs; intros; cbn; [reflexivity|]. now rewrite IHxs. Qed.

Definition A_highpass : Z := 0xa3094.

Definition highpass_post (c : hpc) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(usp lo p pm : Z) (m0 m1 : word) (xs : list word) (m : mem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 g0 g1 g10 fc' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 0 g0 (bvmap_set 1 g1 (bvmap_set 10 g10 (bvmap_set 11 (hc_d2 c) (bvmap_set 12 (hc_d1 c) (bvmap_set 13 (hc_n2 c)
(bvmap_set 14 (hc_n1 c) (bvmap_set 15 (hc_n0 c) F))))))))
(ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch [(p, p + 4 * Z.of_nat (length xs)); (pm, pm + 8); (usp + -16, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp
/\ frm0 fc'
/\ rw_cells asegs m' p (f32 (hp_ys c (m0, m1) xs))
/\ rw_cells asegs m' pm (f32 [fst (hp_st c (m0, m1) xs); snd (hp_st c (m0, m1) xs)]).

Section SI.
Variables (xs : list word) (m0 m1 : word) (p pm usp lo : Z).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable F : bvmap 5 word.
Variable m : mem.
Local Notation n := (Z.of_nat (length xs)).
Hypothesis N1 : 1 <= n < 2^31.
Hypothesis OBX : aobj asegs m p (4 * n).
Hypothesis OBM : aobj asegs m pm 8.
Hypothesis OBP : aobj asegs m 0x24780 60.
Hypothesis OBZ : aobj asegs m 0x24720 60.
Hypothesis X4 : p mod 4 = 0.
Hypothesis M4 : pm mod 4 = 0.
Hypothesis LO : lo <= usp - 16.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis XSH : p + 4 * n <= SH_LO \/ SH_HI <= p.
Hypothesis MSH : pm + 8 <= SH_LO \/ SH_HI <= pm.
Hypothesis XAP : p + 4 * n <= lo \/ usp <= p.
Hypothesis MAP : pm + 8 <= lo \/ usp <= pm.
Hypothesis SEP : p + 4 * n <= pm \/ pm + 8 <= p.
Local Notation W := [(p, p + 4 * n); (pm, pm + 8); (usp + -16, usp)].

Lemma hp_head : forall (Q : machine_state -> Prop) (off kz : Z) (x ma mb : word) (F0 : bvmap 5 word)
(zra t4 t5 t6 : word) fc mc,
0 <= off -> off + 4 <= 4 * n -> off mod 4 = 0 ->
munch W m mc -> offsh W ->
rw_cells asegs mc (p + off) (f32 [x]) -> rw_cells asegs mc pm [C4 ma; C4 mb] ->
(forall t5' t6',
evt asegs Q
(MS (mkR zra (Z_to_bv 64 (usp + -16)) gp tp (Z_to_bv 64 (Z.shiftr pm 3 + SHB)) (Z_to_bv 64 (Z.land pm 7 + 3)) (Z_to_bv 64 (Z.shiftr (pm + 4) 3 + SHB)) s0 s1
(Z_to_bv 64 (p + off)) (Z_to_bv 64 (p + off)) (Z_to_bv 64 (p + off)) (Z_to_bv 64 (p + off))
(Z_to_bv 64 pm) (Z_to_bv 64 (pm + 4)) (Z_to_bv 64 kz) (Z_to_bv 64 SHB)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (Z.land (pm + 4) 7 + 3)) (Z_to_bv 64 (Z.shiftr (p + off) 3 + SHB)) t5' t6')
(bvmap_set 0 (# x) (bvmap_set 1 (# mb) (bvmap_set 10 (# ma) F0))) (Z_to_bv 64 0xa31c0) fc None mc (seg_rom asegs))) ->
evt asegs Q
(MS (mkR zra (Z_to_bv 64 (usp + -16)) gp tp (Z_to_bv 64 (Z.shiftr pm 3 + SHB)) (Z_to_bv 64 (Z.land pm 7 + 3)) (Z_to_bv 64 (Z.shiftr (pm + 4) 3 + SHB)) s0 s1
(Z_to_bv 64 (p + off)) (Z_to_bv 64 (p + off)) (Z_to_bv 64 (p + off)) (Z_to_bv 64 (p + off))
(Z_to_bv 64 pm) (Z_to_bv 64 (pm + 4)) (Z_to_bv 64 kz) (Z_to_bv 64 SHB)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (Z.land (pm + 4) 7 + 3)) t4 t5 t6)
F0 (Z_to_bv 64 0xa318c) fc None mc (seg_rom asegs)).
Proof using OBX OBM X4 M4.
clear N1 LO LOS SPH XAP MAP XSH MSH SEP OBP OBZ.
intros Q off kz x ma mb F0 zra t4 t5 t6 fc mc O0 O1 O4 MU OF X PM K.
pose proof OBX as (OX0 & OX1 & _). pose proof OBM as (OM0 & OM1 & _). unfold APP_TOP in *.
rewrite !f32_cons, ?f32_nil in X.
ato 0xa3198. astep. chk_merge OBX 4.
ato 0xa31a4. astep. chk_merge OBM 4.
ato 0xa31b0. astep. chk_merge OBM 4.
ato 0xa31bc. astep. chk_merge OBM 4.
apply K.
Qed.

Lemma hp_loop : forall (c : hpc) rest done dn x (sa sb : word) (kz off : Z) (j0 : list byte) (t5 t6 : word) fc mc,
xs = done ++ x :: rest -> dn = hp_ys c (m0, m1) done -> length dn = length done -> (sa, sb) = hp_st c (m0, m1) done ->
kz = Z.of_nat (S (length rest)) -> off = 4 * Z.of_nat (length done) ->
frm0 fc -> munch W m mc -> offsh W -> wmono asegs m mc -> mem_inv asegs mc ->
stk asegs mc lo (usp + -16) -> rw_cells asegs mc (usp + -16) [CB 8 j0; C8 ra] ->
rw_cells asegs mc p (f32 dn) -> rw_cells asegs mc (p + off) (f32 (x :: rest)) -> rw_cells asegs mc pm (f32 [sa; sb]) ->
evt asegs (highpass_post c ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F usp lo p pm m0 m1 xs m)
(MS (mkR ra (Z_to_bv 64 (usp + -16)) gp tp (Z_to_bv 64 (Z.shiftr pm 3 + SHB)) (Z_to_bv 64 (Z.land pm 7 + 3)) (Z_to_bv 64 (Z.shiftr (pm + 4) 3 + SHB)) s0 s1
(Z_to_bv 64 (p + off)) (Z_to_bv 64 (p + off)) (Z_to_bv 64 (p + off)) (Z_to_bv 64 (p + off))
(Z_to_bv 64 pm) (Z_to_bv 64 (pm + 4)) (Z_to_bv 64 kz) (Z_to_bv 64 SHB)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (Z.land (pm + 4) 7 + 3)) (Z_to_bv 64 (Z.shiftr (p + off) 3 + SHB)) t5 t6)
(bvmap_set 0 (# x) (bvmap_set 1 (# sb) (bvmap_set 10 (# sa) (bvmap_set 11 (hc_d2 c) (bvmap_set 12 (hc_d1 c) (bvmap_set 13 (hc_n2 c)
(bvmap_set 14 (hc_n1 c) (bvmap_set 15 (hc_n0 c) F))))))))
(Z_to_bv 64 0xa31c0) fc None mc (seg_rom asegs)).
Proof using N1 OBX OBM X4 M4 LO SPH XAP MAP XSH MSH SEP.
clear OBP OBZ.
intros c. induction rest as [|x' rest IH]; intros done dn x sa sb kz off j0 t5 t6 fc mc Hxs Hdn LDN Hst Hkz Hoff FRM MU OF WM MI ST FR DONE X PM;
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ PM) as BPM; rewrite cells_size_f32 in BPM; cbn [length] in BPM;
pose proof (f_equal (@length word) Hxs) as HL; rewrite length_app in HL; cbn [length] in HL;
pose proof OBX as (OX0 & OX1 & _); pose proof OBM as (OM0 & OM1 & _); unfold APP_TOP in *;
pose proof ST as (STa & STb & _); subst kz;
chunk_split_f32 X at 1%nat as X1; rewrite f32_cons, f32_nil in X1; rewrite !f32_cons, ?f32_nil in PM.
- clear X. ato 0xa31d4. astep. chk_merge OBX 4.
ato 0xa31e0. astep. chk_merge OBM 4.
ato 0xa31fc. astep. chk_merge OBX 4.
ato 0xa3218. astep. try sh_if.
ato 0xa3274. astep. release_frame FR ST usp. astep. astep.
unfold highpass_post. finish.
+ chunk_snoc DONE X1. subst xs dn. rewrite hp_ys_app, f32_app, <- Hst. cbn [hp_ys hp_v fst snd]. rewrite f32_cons, f32_nil. exact DONE.
+ subst xs. rewrite hp_st_app, <- Hst. cbn [hp_st hp_next hp_v fst snd]. rewrite !f32_cons, f32_nil. exact PM.
- ato 0xa31d4. astep. chk_merge OBX 4.
ato 0xa31e0. astep. chk_merge OBM 4.
ato 0xa31fc. astep. chk_merge OBX 4.
ato 0xa3218. astep. cbn [length]. sh_if.
chunk_snoc DONE X1.
replace (p + off + 4) with (p + (off + 4)) in * by lia.
pose proof X as XF. chunk_split_f32 XF at 1%nat as X1'. clear XF.
eapply (hp_head _ (off + 4) (Z.of_nat (S (S (length rest))) + -1) x'); [lia | lia | | exact MU | exact OF | exact X1' | exact PM | ].
{ subst off. clear. Z.div_mod_to_equations. lia. }
intros t5' t6'. norm_fchain.
eapply (IH (done ++ [x]) (dn ++ [hp_v c (sa, sb) x]) x' _ _ _ (off + 4)); try eassumption.
all: try (rewrite Hxs, <- app_assoc; reflexivity).
all: try (subst dn; rewrite hp_ys_app, <- Hst; cbn [hp_ys]; reflexivity).
all: try (rewrite !length_app, LDN; reflexivity).
all: try (rewrite hp_st_app, <- Hst; cbn [hp_st hp_next hp_v fst snd]; reflexivity).
all: try (rewrite ?length_app; cbn [length]; lia).
all: try (rewrite f32_app, f32_cons, f32_nil; exact DONE).
Qed.

Lemma highpass_walk : forall (filtID : Z) (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) fc,
rw_cells asegs m p (f32 xs) -> rw_cells asegs m pm (f32 [m0; m1]) -> frm0 fc ->
stk asegs m lo usp -> IMG_TOP <= p -> IMG_TOP <= pm ->
client_consts m -> mem_inv asegs m ->
filtID = 1 \/ filtID = 3 ->
evt asegs (highpass_post (hp_coefs filtID) ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F usp lo p pm m0 m1 xs m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 p) (Z_to_bv 64 n) (Z_to_bv 64 filtID) (Z_to_bv 64 pm) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_highpass) fc None m (seg_rom asegs)).
Proof using N1 OBX OBM OBP OBZ X4 M4 LO LOS SPH XSH MSH XAP MAP SEP.
intros filtID t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 fc X PM FRM ST PTOP MTOP (G1 & G2 & _) MI FID.
unfold A_highpass, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'. pose proof XSH as XSH'. unfold SH_LO, SH_HI in XSH'. pose proof MSH as MSH'. unfold SH_LO, SH_HI in MSH'.
unfold IMG_TOP in PTOP, MTOP.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX.
pose proof (rw_cells_bound _ _ _ _ PM) as BPM; rewrite cells_size_f32 in BPM; cbn [length] in BPM.
pose proof ST as (STa & STb & _).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh W) by (cbn; unfold SH_LO, SH_HI; lia).
destruct xs as [|x rest] eqn:Exs; [cbn [length] in N1; lia|]. rewrite <- Exs in *.
carve_frame 16%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
assert (ALP : 149376 mod 8 = 0) by reflexivity. assert (ALZ : 149280 mod 8 = 0) by reflexivity.
astep. astep. astep. rewrite ?signed_small64 by lia. try sh_if.
destruct FID as [-> | ->]; [ set (C := hp_coefs 1) | set (C := hp_coefs 3) ].
all: ato 0xa318c; rewrite (Z.mod_small n) by lia;
replace (Z_to_bv 64 p) with (Z_to_bv 64 (p + 0)) by (rewrite Z.add_0_r; reflexivity);
replace p with (p + 0) in X at 1 by lia; rewrite Exs in X;
pose proof X as XF; chunk_split_f32 XF at 1%nat as X1; clear XF;
pose proof PM as PM'; rewrite !f32_cons, f32_nil in PM';
(eapply (hp_head _ 0 n x m0 m1); [lia | lia | reflexivity | exact MU | exact OF | exact X1 | exact PM' | ]);
intros t5' t6'; norm_fchain;
eapply (hp_loop C rest [] [] x m0 m1 _ 0); try eassumption; try reflexivity.
all: try (rewrite Exs; cbn [length]; lia).
all: try (rewrite f32_nil; apply rw_cells_nil; lia).
Qed.
End SI.
