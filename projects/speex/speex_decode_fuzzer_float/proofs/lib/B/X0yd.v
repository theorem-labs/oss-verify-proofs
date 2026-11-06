(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1df X1ck X1co X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0yr.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac tlia ::= tlia_one.
Local Notation mem := (word -> option byte).

Definition B_iir_mem16 : Z := 0xa6ad8.

Section SI.
Variables (xs den mem0 : list word) (px pden pm usp lo : Z).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable m : mem.
Local Notation N := (Z.of_nat (length xs)).
Local Notation ord := (Z.of_nat (length den)).
Hypothesis LMEM : length mem0 = length den.
Hypothesis N1 : 1 <= N < 2^31.
Hypothesis ORD : 2 <= ord < 2^31.
Hypothesis OBX : aobj bsegs m px (4 * N).
Hypothesis OBD : aobj bsegs m pden (4 * ord).
Hypothesis OBM : aobj bsegs m pm (4 * ord).
Hypothesis X4 : px mod 4 = 0.
Hypothesis D4 : pden mod 4 = 0.
Hypothesis M4 : pm mod 4 = 0.
Hypothesis XPOS : 0 < px.
Hypothesis DPOS : 0 < pden.
Hypothesis MPOS : 0 < pm.
Hypothesis LO : lo <= usp - 128.
Hypothesis LOS : SH_HI <= lo.
Hypothesis SPH : usp < 2^63.
Hypothesis XSH : px + 4 * N <= SH_LO \/ SH_HI <= px.
Hypothesis MSH : pm + 4 * ord <= SH_LO \/ SH_HI <= pm.
Hypothesis XAP : px + 4 * N <= lo \/ usp <= px.
Hypothesis MAP : pm + 4 * ord <= lo \/ usp <= pm.
Hypothesis DAP : pden + 4 * ord <= lo \/ usp <= pden.
Hypothesis SEPDM : pden + 4 * ord <= pm \/ pm + 4 * ord <= pden.
Hypothesis SEPXM : px + 4 * N <= pm \/ pm + 4 * ord <= px.
Hypothesis SEPXD : px + 4 * N <= pden \/ pden + 4 * ord <= px.
Local Notation W := [(px, px + 4 * N); (pm, pm + 4 * ord); (usp + -128, usp)].

Local Notation K := (ord + -1).
Ltac bnorm P0x P0m P0d A3x A3d A3xm A3dl P0y A3y :=
rewrite ?(swrap32_small K) by lia;
rewrite ?(Z.mod_small K 18446744073709551616) by lia;
replace (Z.shiftl K 2) with (4 * (ord - 1)) by (rewrite Z.shiftl_mul_pow2 by lia; lia);
rewrite ?(Z.mod_small (pden + 4 * (ord - 1)) 18446744073709551616) by lia;
rewrite ?(Z.mod_small (pm + 4 * (ord - 1)) 18446744073709551616) by lia;
rewrite ?(Z.mod_small (4 * (ord - 1)) 18446744073709551616) by lia;
change 9223372036854775808 with (2 ^ 63);
rewrite ?(zb_lxor_pow2_small K 63) by lia; rewrite ?(zb_lxor_pow2_small ord 63) by lia;
replace (K + 2 ^ 63 <? 2 ^ 63) with false by (symmetry; apply Z.ltb_ge; lia);
replace (2 ^ 63 <? K + 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia);
replace (K + 2 ^ 63 <? ord + 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia);
replace (pm + 4 * (ord - 1) <? 4 * (ord - 1)) with false by (symmetry; apply Z.ltb_ge; lia);
replace (pden + 4 * (ord - 1) <? 4 * (ord - 1)) with false by (symmetry; apply Z.ltb_ge; lia);
replace (0 <? pm + 4 * (ord - 1)) with true by (symmetry; apply Z.ltb_lt; lia);
replace (pden + 4 * (ord - 1) <? 1) with false by (symmetry; apply Z.ltb_ge; lia);
rewrite ?P0x, ?P0m, ?P0d, ?A3x, ?A3d, ?A3xm, ?A3dl, ?P0y, ?A3y;
cbn [Z.b2z];
change (Z.lxor (Z.lxor 0 1) 0) with 1; change (Z.lxor 1 1) with 0; change (Z.lxor 1 0) with 1; change (Z.land 1 1) with 1; change (Z.land 1 1) with 1;
change ((0 - 1) mod 18446744073709551616) with 18446744073709551615;
replace (Z.land 18446744073709551615 K) with K
by (change 18446744073709551615 with (2 ^ 64 - 1); rewrite zb_land_mask_l by lia; rewrite Z.mod_small by lia; reflexivity);
replace (Z.shiftl K 2) with (4 * (ord - 1)) by (rewrite Z.shiftl_mul_pow2 by lia; lia);
rewrite ?(zb_lxor_ones pm) by lia.

Definition RIB (py : Z) (rav t0v iv a3v a7v s9v s11v : word) : bvmap 5 word :=
mkR rav (Z_to_bv 64 (usp + -128)) gp tp t0v iv (Z_to_bv 64 px) (Z_to_bv 64 0) (Z_to_bv 64 1)
(Z_to_bv 64 (pm + 4 * (ord - 1))) (Z_to_bv 64 pden) (Z_to_bv 64 py) a3v (Z_to_bv 64 (pden + 4 * (ord - 1))) (Z_to_bv 64 (pm + 4)) (Z_to_bv 64 pm) a7v
(Z_to_bv 64 1) (Z_to_bv 64 SHB) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 (4 * (ord - 1))) s9v
(Z_to_bv 64 (Z.shiftr pm 3 + SHB)) s11v
(Z_to_bv 64 1) (Z_to_bv 64 (18446744073709551615 - pm)) (Z_to_bv 64 1) (Z_to_bv 64 K).

Definition iir_inner_post (py : Z) (iv s11v : word) (mI : mem) : machine_state -> Prop :=
fun ms' => exists rav' t0' a3' a7' s9' F' fc' m' (md : list word) (ml : word),
ms' = MS (RIB py rav' t0' iv a3' a7' s9' s11v) F' (Z_to_bv 64 0xa6cdc) fc' None m' (seg_rom bsegs)
/\ munch [(pm, pm + 4 * ord)] mI m' /\ wmono bsegs mI m' /\ mem_inv bsegs m'
/\ frm0 fc'
/\ Z.of_nat (length md) = ord - 1 /\ rw_cells bsegs m' pm (f32 md) /\ rw_cells bsegs m' (pm + 4 * (ord - 1)) [C4 ml].

Lemma iir_inner : forall (py : Z) (iv s11v : word) (mI : mem) mrest mdone (mj mj1 dj : word) drest (off : Z) (rav a3v a7v s9v : word) F1 fc mc,
off = 4 * Z.of_nat (length mdone) ->
Z.of_nat (length mdone) + 2 + Z.of_nat (length mrest) = ord -> length drest = S (length mrest) ->
aobj bsegs mI pden (4 * ord) -> aobj bsegs mI pm (4 * ord) -> offsh [(pm, pm + 4 * ord)] ->
frm0 fc -> mem_inv bsegs mc -> munch [(pm, pm + 4 * ord)] mI mc -> wmono bsegs mI mc ->
rw_cells bsegs mc (pden + off) (f32 (dj :: drest)) ->
rw_cells bsegs mc pm (f32 mdone) -> rw_cells bsegs mc (pm + off) (f32 (mj :: mj1 :: mrest)) ->
evt bsegs (iir_inner_post py iv s11v mI)
(MS (RIB py rav (Z_to_bv 64 off) iv a3v a7v s9v s11v) F1 (Z_to_bv 64 0xa6c38) fc None mc (seg_rom bsegs)).
Proof using ORD OBD OBM D4 M4 DPOS SEPDM.
clear N1 OBX X4 LO LOS SPH XSH MSH XAP MAP DAP SEPXM SEPXD LMEM XPOS MPOS.
intros py iv s11v mI mrest.
induction mrest as [|mj2 mrest IH]; intros mdone mj mj1 dj drest off rav a3v a7v s9v F1 fc mc Hoff HORD Ldr OBDI OBMI OF FRM MI MU WM DCUR MDONE MJ;
pose proof OBD as (OD0 & OD1 & _); pose proof OBM as (OM0 & OM1 & _); unfold APP_TOP in *;
pose proof (rw_cells_bound _ _ _ _ DCUR) as BD; rewrite cells_size_f32 in BD; cbn [length] in BD;
pose proof (rw_cells_bound _ _ _ _ MJ) as BM; rewrite cells_size_f32 in BM; cbn [length] in BM;
pose proof (rw_cells_bound _ _ _ _ MDONE) as BMD; rewrite cells_size_f32 in BMD;
assert (NZD : (pden + off <? 1) = false) by (apply Z.ltb_ge; lia);
unfold RIB; rewrite !f32_cons in MJ;
pose proof DCUR as DJ; chunk_split_f32 DJ at 1%nat as DJ1; rewrite ?f32_cons, ?f32_nil in DJ1; clear DJ;
hide_disj.
-
cbn [length] in HORD, Ldr. rewrite f32_nil in MJ.
astep. astep. sh_if.
ato 0xa6c54. astep. chk_merge OBMI 4.
ato 0xa6c5c. astep. sh_if. astep. rewrite NZD. cbn [Z.b2z].
ato 0xa6c80. astep. chk_merge OBDI 4.
ato 0xa6c94. astep. chk_merge OBMI 4.
ato 0xa6ca4. astep. sh_if.
ato 0xa6cdc.
chunk_uncons MJ as M1. chunk_snoc MDONE M1. rewrite <- f32_nil, <- f32_cons, <- f32_app in MDONE.
replace (pm + off + 4) with (pm + 4 * (ord - 1)) in MJ by lia.
unfold iir_inner_post, RIB. finish; [ | exact MDONE | exact MJ ].
rewrite length_app. cbn [length]. lia.
-
cbn [length] in HORD, Ldr. destruct drest as [|dj1 drest]; [cbn in Ldr; lia|]. cbn [length] in Ldr, BD.
astep. astep. sh_if.
ato 0xa6c54. astep. chk_merge OBMI 4.
ato 0xa6c5c. astep. sh_if. astep. rewrite NZD. cbn [Z.b2z].
ato 0xa6c80. astep. chk_merge OBDI 4.
ato 0xa6c94. astep. chk_merge OBMI 4.
ato 0xa6ca4. astep. sh_if.
chunk_uncons MJ as M1. chunk_snoc MDONE M1. rewrite <- f32_nil, <- f32_cons, <- f32_app in MDONE.
rewrite <- !f32_cons in MJ.
chunk_split_f32 DCUR at 1%nat as D1. clear D1.
replace (pden + off + 4) with (pden + (off + 4)) in * by lia.
replace (pm + off + 4) with (pm + (off + 4)) in * by lia.
eapply (IH _ mj1 mj2 dj1 drest (off + 4)); try eassumption; try reflexivity.
all: try (rewrite length_app; cbn [length] in *; lia).
all: try (cbn [length] in *; lia).
Qed.

Definition iir_post (inplace : bool) (py : Z) (W : list (Z * Z)) : machine_state -> Prop :=
fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' (ys mv : list word),
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (ret_pc ra) fc' None m' (seg_rom bsegs)
/\ munch W m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo usp
/\ frm0 fc'
/\ length ys = length xs /\ rw_cells bsegs m' py (f32 ys)
/\ length mv = length den /\ rw_cells bsegs m' pm (f32 mv)
/\ rw_cells bsegs m' pden (f32 den)
/\ (inplace = false -> rw_cells bsegs m' px (f32 xs)).

Definition FRL (j0 : list byte) : list cell :=
[CB 8 j0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 N); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Ltac iir_body pyv x i mc mv0 mv1 mvtt de0 de1 det rav a3v a7v s9v :=
astep; replace (Z.shiftl i 2) with (4 * i) by (rewrite Z.shiftl_mul_pow2 by lia; lia);
astep; astep;
(lazymatch goal with NZX : (px + 4 * i <? 1) = false |- _ => rewrite NZX end); cbn [Z.b2z];
ato 0xa6bfc; astep; sh_if;
ato 0xa6c10; astep;
(lazymatch goal with OBX : aobj _ m px _ |- _ => chk_merge OBX 4 end);
ato 0xa6c1c; astep;
(lazymatch goal with OBM : aobj _ m pm _ |- _ => chk_merge OBM 4 end);
(lazymatch goal with MEM : rw_cells _ mc pm _ |- _ => rewrite !f32_cons in MEM end);
ato 0xa6c30; astep; sh_if;
ato 0xa6c38;
(lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
lazymatch R with
| context [TNode] =>
let r := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in
unify R r;
lazymatch r with
| mkR ?rav' _ _ _ _ _ _ _ _ _ _ _ ?a3' _ _ _ ?a7' _ _ _ _ _ _ _ ?s9' _ _ _ _ _ _ =>
change R with (RIB pyv rav' (Z_to_bv 64 0) (Z_to_bv 64 i) a3' a7' s9' (Z_to_bv 64 (4 * i)))
end
end
end);
(lazymatch goal with
| OBD : aobj _ m pden _, OBM : aobj _ m pm _, MU : munch _ m mc, OF : offsh _, MEM : rw_cells _ mc pm _, DEN : rw_cells _ mc pden _ , Eden : den = _ |- _ =>
let OBDc := fresh "OBDc" in let OBMc := fresh "OBMc" in let OFc := fresh "OFc" in let MU0 := fresh "MU0" in let WM0 := fresh "WM0" in
let MD0 := fresh "MD0" in let DC := fresh "DC" in
pose proof (aobj_munch bsegs _ m mc pden (4 * ord) OBD MU (shfree_of_aobj bsegs _ m pden (4 * ord) OF OBD)) as OBDc;
pose proof (aobj_munch bsegs _ m mc pm (4 * ord) OBM MU (shfree_of_aobj bsegs _ m pm (4 * ord) OF OBM)) as OBMc;
assert (OFc : offsh [(pm, pm + 4 * ord)]) by (pose proof MSH as MSH'; unfold hid in MSH'; clear - MSH'; cbn; unfold SH_LO, SH_HI in *; lia);
pose proof (munch_refl [(pm, pm + 4 * ord)] mc) as MU0; pose proof (wmono_refl bsegs mc) as WM0;
assert (MD0 : rw_cells bsegs mc pm (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia);
pose proof DEN as DC; rewrite Eden in DC; replace pden with (pden + 0) in DC at 1 by lia;
replace pm with (pm + 0) in MEM at 1 by lia;
call (iir_inner pyv (Z_to_bv 64 i) (Z_to_bv 64 (4 * i)) mc mvtt [] mv0 mv1 de0 (de1 :: det) 0);
[ reflexivity | cbn [length] in *; lia | cbn [length] in *; lia | exact OBDc | exact OBMc | exact OFc
| eassumption | eassumption | exact MU0 | exact WM0 | exact DC | exact MD0 | exact MEM | ];
clear MU0 WM0 OBDc OBMc OFc; try clear MD0; try clear DC
end);
try unfold RIB;
(match goal with H : rw_cells _ _ (pm + 4 * (ord - 1)) [C4 _] |- _ => rename H into ML end);
(match goal with H : rw_cells _ _ pm (f32 _) |- _ => rename H into MD end);
(match goal with H : Z.of_nat (length _) = ord - 1 |- _ => rename H into LMD end);
ato 0xa6cf4; astep;
(lazymatch goal with OBD : aobj _ m pden _ |- _ => chk_merge OBD 4 end);
ato 0xa6d08; astep;
(lazymatch goal with OBM : aobj _ m pm _ |- _ => chk_merge OBM 4 end);
ato 0xa6d14; astep;
(lazymatch goal with NZY : (pyv + 4 * i <? 1) = false |- _ => rewrite NZY end); cbn [Z.b2z];
ato 0xa6d20; astep; sh_if;
ato 0xa6d34; astep;
(lazymatch goal with OBY : aobj _ m pyv _ |- _ => chk_merge OBY 4 end).

Lemma iir_outer_ip : forall rest done dn x mv (dl : word) (i : Z) (j0 : list byte) (rav t0v a3v a7v s9v s11v : word) F1 fc mc,
xs = done ++ x :: rest -> length dn = length done -> i = Z.of_nat (length done) -> length mv = length den ->
frm0 fc -> munch W m mc -> offsh W -> wmono bsegs m mc -> mem_inv bsegs mc ->
stk bsegs mc lo (usp + -128) ->
rw_cells bsegs mc (usp + -128) (FRL j0) ->
rw_cells bsegs mc px (f32 dn) -> rw_cells bsegs mc (px + 4 * i) (f32 (x :: rest)) ->
rw_cells bsegs mc pm (f32 mv) -> rw_cells bsegs mc pden (f32 den) -> rw_cells bsegs mc (pden + 4 * (ord - 1)) [C4 dl] ->
evt bsegs (iir_post true px W)
(MS (RIB px rav t0v (Z_to_bv 64 i) a3v a7v s9v s11v) F1 (Z_to_bv 64 0xa6be8) fc None mc (seg_rom bsegs)).
Proof using N1 ORD OBX OBD OBM X4 D4 M4 XPOS DPOS MPOS LO SPH XSH MSH XAP MAP DAP SEPDM SEPXM SEPXD.
clear LMEM.
induction rest as [|x' rest IH]; intros done dn x mv dl i j0 rav t0v a3v a7v s9v s11v F1 fc mc Hxs LDN Hi Lmv FRM MU OF WM MI ST FR DONE X MEM DEN DL;
pose proof (f_equal (@length word) Hxs) as HL; rewrite length_app in HL; cbn [length] in HL;
pose proof OBX as (OX0 & OX1 & _); pose proof OBD as (OD0 & OD1 & _); pose proof OBM as (OM0 & OM1 & _); unfold APP_TOP in *;
pose proof ST as (STa & STb & _);
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ MEM) as BM; rewrite cells_size_f32, Lmv in BM;
pose proof (rw_cells_bound _ _ _ _ DEN) as BD; rewrite cells_size_f32 in BD;
pose proof (rw_cells_bound _ _ _ _ DONE) as BDO; rewrite cells_size_f32, LDN in BDO;
destruct mv as [|mv0 [|mv1 mvtt]] eqn:Emv; try (cbn [length] in Lmv; lia);
destruct den as [|de0 [|de1 det]] eqn:Eden; try (cbn [length] in ORD; lia); rewrite <- Eden in *;
pose proof (f_equal (@length word) Eden) as LD; cbn [length] in LD;
chunk_split_f32 X at 1%nat as X1; rewrite ?f32_cons, ?f32_nil in X1;
assert (NZX : (px + 4 * i <? 1) = false) by (apply Z.ltb_ge; lia);
unfold RIB, FRL in *; hide_disj.
-
iir_body px x i mc mv0 mv1 mvtt de0 de1 det rav a3v a7v s9v.
ato 0xa6d44. astep. sh_if.
ato 0xa6dd4. release_frame FR ST usp. astep. astep.
chunk_snoc MD ML. rewrite <- f32_nil, <- f32_cons, <- f32_app in MD.
chunk_snoc DONE X1. rewrite <- f32_nil, <- f32_cons, <- f32_app in DONE.
unfold iir_post. finish; [ | exact DONE | | exact MD | intros; discriminate ].
+ rewrite Hxs, !length_app. cbn [length]. lia.
+ rewrite length_app. cbn [length]. lia.
-
iir_body px x i mc mv0 mv1 mvtt de0 de1 det rav a3v a7v s9v.
ato 0xa6d44. astep. sh_if.
chunk_snoc MD ML. rewrite <- f32_nil, <- f32_cons, <- f32_app in MD.
chunk_snoc DONE X1. rewrite <- f32_nil, <- f32_cons, <- f32_app in DONE.
replace (px + 4 * i + 4) with (px + 4 * (i + 1)) in * by lia.
clear Lmv BM.
eapply (IH (done ++ [x]) _ x' _ dl (i + 1) j0); try eassumption.
all: try (rewrite Hxs, <- app_assoc; reflexivity).
all: try (rewrite !length_app; cbn [length]; lia).
Qed.

Lemma den_last : forall mc, rw_cells bsegs mc pden (f32 den) -> exists dl, rw_cells bsegs mc (pden + 4 * (ord - 1)) [C4 dl].
Proof using ORD.
clear - ORD. intros mc DEN.
destruct (exists_last (l := den)) as (dinit & dl & E); [intros ->; cbn [length] in ORD; lia|].
exists dl. rewrite E, f32_app in DEN. apply rw_cells_app in DEN. destruct DEN as [_ D]. rewrite cells_size_f32 in D.
rewrite f32_cons, f32_nil in D.
replace (pden + 4 * (ord - 1)) with (pden + Z.of_nat (4 * length dinit)); [exact D|].
rewrite E, length_app. cbn [length]. lia.
Qed.

Ltac iir_prologue pyv P0y A3y :=
ato 0xa6b14; astep; rewrite ?signed_small64 by lia; try sh_if;
ato 0xa6be8;
(let P0x := fresh "P0x" in let P0m := fresh "P0m" in let P0d := fresh "P0d" in let A3x := fresh "A3x" in let A3d := fresh "A3d" in
let A3xm := fresh "A3xm" in let A3dl := fresh "A3dl" in
assert (P0x : (0 <? px) = true) by (apply Z.ltb_lt; lia);
assert (P0m : (0 <? pm) = true) by (apply Z.ltb_lt; lia);
assert (P0d : (0 <? pden) = true) by (apply Z.ltb_lt; lia);
assert (A3x : (Z.land px 3 <? 1) = true) by (apply Z.ltb_lt; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; clear - X4; Z.div_mod_to_equations; lia);
assert (A3d : (Z.land pden 3 <? 1) = true) by (apply Z.ltb_lt; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; clear - D4; Z.div_mod_to_equations; lia);
assert (A3xm : (Z.land (Z.lor px pm) 3 <? 1) = true)
by (apply Z.ltb_lt; rewrite zb_land_lor_distr_l; change 3 with (Z.ones 2); rewrite !Z.land_ones by lia;
replace (px mod 2 ^ 2) with 0 by (clear - X4; Z.div_mod_to_equations; lia);
replace (pm mod 2 ^ 2) with 0 by (clear - M4; Z.div_mod_to_equations; lia); reflexivity);
assert (A3dl : (Z.land (pden + 4 * (ord - 1)) 3 <? 1) = true)
by (apply Z.ltb_lt; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; clear - D4; Z.div_mod_to_equations; lia);
bnorm P0x P0m P0d A3x A3d A3xm A3dl P0y A3y;
(lazymatch goal with FR : rw_cells _ _ (usp + -128) _ |- _ => rewrite ?P0x in FR; cbn [Z.b2z] in FR end)).

Lemma iir_mem16_walk_ip : forall (F : bvmap 5 word) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) fc,
rw_cells bsegs m px (f32 xs) -> rw_cells bsegs m pden (f32 den) -> rw_cells bsegs m pm (f32 mem0) -> frm0 fc ->
stk bsegs m lo usp -> IMG_TOP_B <= px -> IMG_TOP_B <= pm ->
client_constsB m -> mem_inv bsegs m ->
evt bsegs (iir_post true px W)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 px) (Z_to_bv 64 pden) (Z_to_bv 64 px) (Z_to_bv 64 N) (Z_to_bv 64 ord) (Z_to_bv 64 pm) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 B_iir_mem16) fc None m (seg_rom bsegs)).
Proof using LMEM N1 ORD OBX OBD OBM X4 D4 M4 XPOS DPOS MPOS LO LOS SPH XSH MSH XAP MAP DAP SEPDM SEPXM SEPXD.
intros F t0 t1 t2 a6 a7 t3 t4 t5 t6 fc X DEN MEM FRM ST PTOP MTOP (G1 & G2 & _) MI.
unfold B_iir_mem16, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'. pose proof XSH as XSH'. unfold SH_LO, SH_HI in XSH'. pose proof MSH as MSH'. unfold SH_LO, SH_HI in MSH'.
unfold IMG_TOP_B in PTOP, MTOP.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX.
pose proof (rw_cells_bound _ _ _ _ DEN) as BD; rewrite cells_size_f32 in BD.
pose proof (rw_cells_bound _ _ _ _ MEM) as BM; rewrite cells_size_f32, LMEM in BM.
destruct (den_last m DEN) as (dl & DL).
pose proof OBD as (OD0 & OD1 & _); pose proof OBM as (OM0 & OM1 & _); unfold APP_TOP in *.
pose proof ST as (STa & STb & _).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh W) by (cbn; unfold SH_LO, SH_HI; lia).
destruct xs as [|x rest] eqn:Exs; [cbn [length] in N1; lia|]. rewrite <- Exs in *.
hide_disj.
carve_frame 128%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 128 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
iir_prologue px XPOS XPOS.
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
change R with (RIB px ra (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 K) s11)
end.
replace px with (px + 4 * 0) in X at 1 by lia. rewrite Exs in X.
eapply (iir_outer_ip rest [] [] x mem0 dl 0 (firstn 8 junk)); try eassumption; try reflexivity.
all: try (rewrite f32_nil; apply rw_cells_nil; lia).
Qed.

Section DJ.
Variable py : Z.
Hypothesis OBY : aobj bsegs m py (4 * N).
Hypothesis Y4 : py mod 4 = 0.
Hypothesis YPOS : 0 < py.
Hypothesis YSH : py + 4 * N <= SH_LO \/ SH_HI <= py.
Hypothesis YAP : py + 4 * N <= lo \/ usp <= py.
Hypothesis SEPXY : px + 4 * N <= py \/ py + 4 * N <= px.
Hypothesis SEPYM : py + 4 * N <= pm \/ pm + 4 * ord <= py.
Hypothesis SEPYD : py + 4 * N <= pden \/ pden + 4 * ord <= py.
Local Notation WD := [(py, py + 4 * N); (pm, pm + 4 * ord); (usp + -128, usp)].

Lemma iir_outer_dj : forall rest done x yd y yrest mv (dl : word) (i : Z) (j0 : list byte) (rav t0v a3v a7v s9v s11v : word) F1 fc mc,
xs = done ++ x :: rest -> length yd = length done -> length yrest = length rest -> i = Z.of_nat (length done) -> length mv = length den ->
frm0 fc -> munch WD m mc -> offsh WD -> wmono bsegs m mc -> mem_inv bsegs mc ->
stk bsegs mc lo (usp + -128) ->
rw_cells bsegs mc (usp + -128) (FRL j0) ->
rw_cells bsegs mc px (f32 xs) -> rw_cells bsegs mc (px + 4 * i) (f32 (x :: rest)) ->
rw_cells bsegs mc py (f32 yd) -> rw_cells bsegs mc (py + 4 * i) (f32 (y :: yrest)) ->
rw_cells bsegs mc pm (f32 mv) -> rw_cells bsegs mc pden (f32 den) -> rw_cells bsegs mc (pden + 4 * (ord - 1)) [C4 dl] ->
evt bsegs (iir_post false py WD)
(MS (RIB py rav t0v (Z_to_bv 64 i) a3v a7v s9v s11v) F1 (Z_to_bv 64 0xa6be8) fc None mc (seg_rom bsegs)).
Proof using N1 ORD OBX OBD OBM OBY X4 D4 M4 Y4 XPOS DPOS MPOS YPOS LO SPH MSH YSH XAP MAP DAP YAP SEPDM SEPXM SEPXD SEPXY SEPYM SEPYD.
clear LMEM XSH.
induction rest as [|x' rest IH]; intros done x yd y yrest mv dl i j0 rav t0v a3v a7v s9v s11v F1 fc mc Hxs LYD LYR Hi Lmv FRM MU OF WM MI ST FR XS XC YDONE Y MEM DEN DL;
pose proof (f_equal (@length word) Hxs) as HL; rewrite length_app in HL; cbn [length] in HL;
pose proof OBX as (OX0 & OX1 & _); pose proof OBD as (OD0 & OD1 & _); pose proof OBM as (OM0 & OM1 & _); pose proof OBY as (OY0 & OY1 & _); unfold APP_TOP in *;
pose proof ST as (STa & STb & _);
pose proof (rw_cells_bound _ _ _ _ XC) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ Y) as BY; rewrite cells_size_f32 in BY; cbn [length] in BY;
pose proof (rw_cells_bound _ _ _ _ MEM) as BM; rewrite cells_size_f32, Lmv in BM;
pose proof (rw_cells_bound _ _ _ _ DEN) as BD; rewrite cells_size_f32 in BD;
pose proof (rw_cells_bound _ _ _ _ YDONE) as BDO; rewrite cells_size_f32, LYD in BDO;
destruct mv as [|mv0 [|mv1 mvtt]] eqn:Emv; try (cbn [length] in Lmv; lia);
destruct den as [|de0 [|de1 det]] eqn:Eden; try (cbn [length] in ORD; lia); rewrite <- Eden in *;
pose proof (f_equal (@length word) Eden) as LD; cbn [length] in LD;
chunk_split_f32 XC at 1%nat as X1; rewrite ?f32_cons, ?f32_nil in X1;
assert (NZX : (px + 4 * i <? 1) = false) by (apply Z.ltb_ge; lia);
assert (NZY : (py + 4 * i <? 1) = false) by (apply Z.ltb_ge; lia);
unfold RIB, FRL in *; hide_disj.
-
destruct yrest; [|cbn [length] in LYR; lia]. cbn [length] in BY.
chunk_split_f32 Y at 1%nat as Y1; rewrite ?f32_cons, ?f32_nil in Y1.
iir_body py x i mc mv0 mv1 mvtt de0 de1 det rav a3v a7v s9v.
ato 0xa6d44. astep. sh_if.
ato 0xa6dd4. release_frame FR ST usp. astep. astep.
chunk_snoc MD ML. rewrite <- f32_nil, <- f32_cons, <- f32_app in MD.
chunk_snoc YDONE Y1. rewrite <- f32_nil, <- f32_cons, <- f32_app in YDONE.
unfold iir_post. finish; [ | exact YDONE | | exact MD | intros _; exact XS ].
+ rewrite Hxs, !length_app. cbn [length]. lia.
+ rewrite length_app. cbn [length]. lia.
-
destruct yrest as [|y' yrest]; [cbn [length] in LYR; lia|]. cbn [length] in LYR, BY.
chunk_split_f32 Y at 1%nat as Y1; rewrite ?f32_cons, ?f32_nil in Y1.
iir_body py x i mc mv0 mv1 mvtt de0 de1 det rav a3v a7v s9v.
ato 0xa6d44. astep. sh_if.
chunk_snoc MD ML. rewrite <- f32_nil, <- f32_cons, <- f32_app in MD.
chunk_snoc YDONE Y1. rewrite <- f32_nil, <- f32_cons, <- f32_app in YDONE.
replace (px + 4 * i + 4) with (px + 4 * (i + 1)) in * by lia.
replace (py + 4 * i + 4) with (py + 4 * (i + 1)) in * by lia.
clear Lmv BM X1.
eapply (IH (done ++ [x]) x' _ y' yrest _ dl (i + 1) j0); try eassumption.
all: try (rewrite Hxs, <- app_assoc; reflexivity).
all: try (rewrite !length_app; cbn [length]; lia).
all: try lia.
Qed.

Lemma iir_mem16_walk_dj : forall (ys : list word) (F : bvmap 5 word) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) fc,
rw_cells bsegs m px (f32 xs) -> rw_cells bsegs m pden (f32 den) -> rw_cells bsegs m pm (f32 mem0) ->
rw_cells bsegs m py (f32 ys) -> length ys = length xs -> frm0 fc ->
stk bsegs m lo usp -> IMG_TOP_B <= py -> IMG_TOP_B <= pm ->
client_constsB m -> mem_inv bsegs m ->
evt bsegs (iir_post false py WD)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 px) (Z_to_bv 64 pden) (Z_to_bv 64 py) (Z_to_bv 64 N) (Z_to_bv 64 ord) (Z_to_bv 64 pm) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 B_iir_mem16) fc None m (seg_rom bsegs)).
Proof using LMEM N1 ORD OBX OBD OBM OBY X4 D4 M4 Y4 XPOS DPOS MPOS YPOS LO LOS SPH MSH YSH XAP MAP DAP YAP SEPDM SEPXM SEPXD SEPXY SEPYM SEPYD.
clear XSH.
intros ys F t0 t1 t2 a6 a7 t3 t4 t5 t6 fc X DEN MEM Y LYS FRM ST PTOP MTOP (G1 & G2 & _) MI.
unfold B_iir_mem16, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'. pose proof YSH as YSH'. unfold SH_LO, SH_HI in YSH'. pose proof MSH as MSH'. unfold SH_LO, SH_HI in MSH'.
unfold IMG_TOP_B in PTOP, MTOP.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX.
pose proof (rw_cells_bound _ _ _ _ Y) as BY; rewrite cells_size_f32, LYS in BY.
pose proof (rw_cells_bound _ _ _ _ DEN) as BD; rewrite cells_size_f32 in BD.
pose proof (rw_cells_bound _ _ _ _ MEM) as BM; rewrite cells_size_f32, LMEM in BM.
destruct (den_last m DEN) as (dl & DL).
pose proof OBD as (OD0 & OD1 & _); pose proof OBM as (OM0 & OM1 & _); unfold APP_TOP in *.
pose proof ST as (STa & STb & _).
pose proof (munch_refl WD m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh WD) by (cbn; unfold SH_LO, SH_HI; lia).
assert (P0y : (0 <? py) = true) by (apply Z.ltb_lt; lia).
assert (A3y : (Z.land py 3 <? 1) = true) by (apply Z.ltb_lt; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; clear - Y4; Z.div_mod_to_equations; lia).
destruct xs as [|x rest] eqn:Exs; [cbn [length] in N1; lia|]. rewrite <- Exs in *.
destruct ys as [|y yrest] eqn:Eys; [rewrite Exs in LYS; cbn [length] in LYS; lia|]. cbn [length] in LYS, BY.
hide_disj.
carve_frame 128%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 128 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
iir_prologue py P0y A3y.
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
change R with (RIB py ra (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 K) s11)
end.
pose proof X as XC. replace px with (px + 4 * 0) in XC at 1 by lia. rewrite Exs in XC.
replace py with (py + 4 * 0) in Y at 1 by lia.
eapply (iir_outer_dj rest [] x [] y yrest mem0 dl 0 (firstn 8 junk)); try eassumption; try reflexivity.
all: try (rewrite f32_nil; apply rw_cells_nil; lia).
all: try (rewrite Exs in LYS; cbn [length] in LYS; lia).
Qed.
End DJ.
End SI.
