(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1df X1ck X1co X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).

Definition lhide (P : Prop) : Prop := P.
Ltac hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (lhide (A \/ B)) in H end.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1ct X1d5.
Local Ltac tlia ::= olia ltac:(
sf_clear_big;
first [ Zify.zify; xlia zchecker
| match goal with H : lhide (_ \/ _) |- _ => unfold lhide in H; Zify.zify; xlia zchecker end
| unfold lhide in *; sf_unhide;
first [ zify_prune_neg; Zify.zify; xlia zchecker | zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ]).

Definition A_iir_mem16 : Z := 0xa3860.

Section SI.
Variables (xs den mem0 : list word) (px pden pm usp lo : Z).
Variables ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variable m : mem.
Local Notation N := (Z.of_nat (length xs)).
Local Notation ord := (Z.of_nat (length den)).
Hypothesis LMEM : length mem0 = length den.
Hypothesis N1 : 1 <= N < 2^31.
Hypothesis ORD : 2 <= ord < 2^31.
Hypothesis OBX : aobj asegs m px (4 * N).
Hypothesis OBD : aobj asegs m pden (4 * ord).
Hypothesis OBM : aobj asegs m pm (4 * ord).
Hypothesis X4 : px mod 4 = 0.
Hypothesis D4 : pden mod 4 = 0.
Hypothesis M4 : pm mod 4 = 0.
Hypothesis LO : lo <= usp - 80.
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
Local Notation W := [(px, px + 4 * N); (pm, pm + 4 * ord); (usp + -80, usp)].

Definition RI (py : Z) (t0v t1v t2v s2v s3v s4v s5v s6v s7v s8v : word) : bvmap 5 word :=
mkR ra (Z_to_bv 64 (usp + -80)) gp tp t0v t1v t2v (Z_to_bv 64 (Z.shiftr pm 3 + SHB)) (Z_to_bv 64 2)
(Z_to_bv 64 px) (Z_to_bv 64 pden) (Z_to_bv 64 py) (Z_to_bv 64 N) (Z_to_bv 64 ord) (Z_to_bv 64 pm)
(Z_to_bv 64 (pden + 4 * (ord - 1))) (Z_to_bv 64 (pm + 4 * (ord - 1)))
s2v s3v s4v s5v s6v s7v s8v s9 s10 s11
(Z_to_bv 64 (pm + 4)) (Z_to_bv 64 (Z.land pm 7 + 3)) (Z_to_bv 64 SHB) (Z_to_bv 64 (ord + -1)).

Definition iir_inner_post (py : Z) (t2v s2v : word) (mI : mem) : machine_state -> Prop :=
fun ms' => exists t0' t1' s3' s4' s5' s6' s7' s8' F' fc' m' (md : list word) (ml : word),
ms' = MS (RI py t0' t1' t2v s2v s3' s4' s5' s6' s7' s8') F' (Z_to_bv 64 0xa39a8) fc' None m' (seg_rom asegs)
/\ munch [(pm, pm + 4 * ord)] mI m' /\ wmono asegs mI m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ Z.of_nat (length md) = ord - 1 /\ rw_cells asegs m' pm (f32 md) /\ rw_cells asegs m' (pm + 4 * (ord - 1)) [C4 ml].

Lemma iir_inner : forall (py : Z) (t2v s2v : word) (mI : mem) mrest mdone (mj mj1 dj : word) drest (off kz : Z) (s6v s7v s8v : word) F1 fc mc,
off = 4 * Z.of_nat (length mdone) -> kz = Z.of_nat (S (length mrest)) ->
Z.of_nat (length mdone) + 2 + Z.of_nat (length mrest) = ord -> length drest = S (length mrest) ->
aobj asegs mI pden (4 * ord) -> aobj asegs mI pm (4 * ord) -> offsh [(pm, pm + 4 * ord)] ->
frm0 fc -> mem_inv asegs mc -> munch [(pm, pm + 4 * ord)] mI mc -> wmono asegs mI mc ->
rw_cells asegs mc (pden + off) (f32 (dj :: drest)) ->
rw_cells asegs mc pm (f32 mdone) -> rw_cells asegs mc (pm + off) (f32 (mj :: mj1 :: mrest)) ->
evt asegs (iir_inner_post py t2v s2v mI)
(MS (RI py (Z_to_bv 64 (pden + off)) (Z_to_bv 64 (pm + off)) t2v s2v (Z_to_bv 64 kz) (Z_to_bv 64 (pden + off)) (Z_to_bv 64 (pm + off + 4)) s6v s7v s8v)
F1 (Z_to_bv 64 0xa3918) fc None mc (seg_rom asegs)).
Proof using ORD OBD OBM D4 M4 SEPDM.
clear N1 OBX X4 LO LOS SPH XSH MSH XAP MAP DAP SEPXM SEPXD LMEM.
intros py t2v s2v mI mrest.
induction mrest as [|mj2 mrest IH]; intros mdone mj mj1 dj drest off kz s6v s7v s8v F1 fc mc Hoff Hkz HORD Ldr OBDI OBMI OF FRM MI MU WM DCUR MDONE MJ;
pose proof OBD as (OD0 & OD1 & _); pose proof OBM as (OM0 & OM1 & _); unfold APP_TOP in *;
pose proof (rw_cells_bound _ _ _ _ DCUR) as BD; rewrite cells_size_f32 in BD; cbn [length] in BD;
pose proof (rw_cells_bound _ _ _ _ MJ) as BM; rewrite cells_size_f32 in BM; cbn [length] in BM;
pose proof (rw_cells_bound _ _ _ _ MDONE) as BMD; rewrite cells_size_f32 in BMD;
unfold RI; rewrite !f32_cons in MJ;
pose proof DCUR as DJ; chunk_split_f32 DJ at 1%nat as DJ1; rewrite ?f32_cons, ?f32_nil in DJ1; clear DJ;
hide_disj.
-
cbn [length] in HORD, Ldr. rewrite f32_nil in MJ.
astep.
ato 0xa3928. astep. chk_merge OBMI 4.
ato 0xa393c. astep. chk_merge OBDI 4.
ato 0xa3950. astep. chk_merge OBMI 4.
ato 0xa3970. astep. subst kz. cbn [length]. sh_if.
ato 0xa39a8.
chunk_uncons MJ as M1. chunk_snoc MDONE M1. rewrite <- f32_nil, <- f32_cons, <- f32_app in MDONE.
replace (pm + off + 4) with (pm + 4 * (ord - 1)) in MJ by lia.
unfold iir_inner_post, RI. finish; [ | exact MDONE | exact MJ ].
rewrite length_app. cbn [length]. lia.
-
cbn [length] in HORD, Ldr. destruct drest as [|dj1 drest]; [cbn in Ldr; lia|]. cbn [length] in Ldr, BD.
astep.
ato 0xa3928. astep. chk_merge OBMI 4.
ato 0xa393c. astep. chk_merge OBDI 4.
ato 0xa3950. astep. chk_merge OBMI 4.
ato 0xa3970. astep. subst kz. cbn [length]. sh_if.
chunk_uncons MJ as M1. chunk_snoc MDONE M1. rewrite <- f32_nil, <- f32_cons, <- f32_app in MDONE.
rewrite <- !f32_cons in MJ.
chunk_split_f32 DCUR at 1%nat as D1. clear D1.
replace (pden + off + 4) with (pden + (off + 4)) in * by lia.
replace (pm + off + 4) with (pm + (off + 4)) in * by lia.
replace (pm + off + 8) with (pm + (off + 4) + 4) by lia.
replace (Z.of_nat (S (S (length mrest))) + -1) with (Z.of_nat (S (length mrest))) by lia.
eapply (IH _ mj1 mj2 dj1 drest (off + 4)); try eassumption; try reflexivity.
all: try (rewrite length_app; cbn [length] in *; lia).
all: try (cbn [length] in *; lia).
Qed.

Definition iir_post (inplace : bool) (py : Z) (W : list (Z * Z)) : machine_state -> Prop :=
fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' (ys mv : list word),
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp
/\ frm0 fc'
/\ length ys = length xs /\ rw_cells asegs m' py (f32 ys)
/\ length mv = length den /\ rw_cells asegs m' pm (f32 mv)
/\ rw_cells asegs m' pden (f32 den)
/\ (inplace = false -> rw_cells asegs m' px (f32 xs)).

Ltac iir_body pyv x i mc mv0 mv1 mvtt de0 de1 det s6v s7v s8v :=
astep; replace (Z.shiftl i 2) with (4 * i) by (rewrite Z.shiftl_mul_pow2 by lia; lia);
ato 0xa38e4; astep;
(lazymatch goal with OBX : aobj _ _ px _ |- _ => chk_merge OBX 4 end);
ato 0xa38f0; astep;
(lazymatch goal with OBM : aobj _ _ pm _ |- _ => chk_merge OBM 4 end);
(lazymatch goal with MEM : rw_cells _ mc pm _ |- _ => rewrite !f32_cons in MEM end);
ato 0xa3900; astep; sh_if;
ato 0xa3918;
(lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
replace R with (RI pyv (Z_to_bv 64 (pden + 0)) (Z_to_bv 64 (pm + 0)) (Z_to_bv 64 i) (Z_to_bv 64 (4 * i)) (Z_to_bv 64 (Z.of_nat (S (length mvtt))))
(Z_to_bv 64 (pden + 0)) (Z_to_bv 64 (pm + 0 + 4)) s6v s7v s8v)
by (unfold RI; rewrite !Z.add_0_r; replace (Z.of_nat (S (length mvtt))) with (ord + -1) by (cbn [length] in *; lia); reflexivity)
end);
(lazymatch goal with
| OBD : aobj _ m pden _, OBM : aobj _ m pm _, MU : munch _ m mc, OF : offsh _, MEM : rw_cells _ mc pm _, DEN : rw_cells _ mc pden _ , Eden : den = _ |- _ =>
let OBDc := fresh "OBDc" in let OBMc := fresh "OBMc" in let OFc := fresh "OFc" in let MU0 := fresh "MU0" in let WM0 := fresh "WM0" in
let MD0 := fresh "MD0" in let DC := fresh "DC" in
pose proof (aobj_munch asegs _ m mc pden (4 * ord) OBD MU (shfree_of_aobj asegs _ m pden (4 * ord) OF OBD)) as OBDc;
pose proof (aobj_munch asegs _ m mc pm (4 * ord) OBM MU (shfree_of_aobj asegs _ m pm (4 * ord) OF OBM)) as OBMc;
assert (OFc : offsh [(pm, pm + 4 * ord)]) by (pose proof MSH as MSH'; unfold lhide in MSH'; clear - MSH'; cbn; unfold SH_LO, SH_HI in *; lia);
pose proof (munch_refl [(pm, pm + 4 * ord)] mc) as MU0; pose proof (wmono_refl asegs mc) as WM0;
assert (MD0 : rw_cells asegs mc pm (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia);
pose proof DEN as DC; rewrite Eden in DC; replace pden with (pden + 0) in DC at 1 by lia;
replace pm with (pm + 0) in MEM at 1 by lia;
call (iir_inner pyv (Z_to_bv 64 i) (Z_to_bv 64 (4 * i)) mc mvtt [] mv0 mv1 de0 (de1 :: det) 0 _ s6v s7v s8v);
[ reflexivity | reflexivity | cbn [length] in *; lia | cbn [length] in *; lia | exact OBDc | exact OBMc | exact OFc
| eassumption | eassumption | exact MU0 | exact WM0 | exact DC | exact MD0 | exact MEM | ];
clear MU0 WM0 OBDc OBMc OFc; try clear MD0; try clear DC
end);
try unfold RI;
(match goal with H : rw_cells _ _ (pm + 4 * (ord - 1)) [C4 _] |- _ => rename H into ML end);
(match goal with H : rw_cells _ _ pm (f32 _) |- _ => rename H into MD end);
(match goal with H : Z.of_nat (length _) = ord - 1 |- _ => rename H into LMD end);
ato 0xa39b4; astep;
(lazymatch goal with OBD : aobj _ m pden _ |- _ => chk_merge OBD 4 end);
ato 0xa39c8; astep;
(lazymatch goal with OBM : aobj _ m pm _ |- _ => chk_merge OBM 4 end);
ato 0xa39e4; astep;
(lazymatch goal with OBY : aobj _ m pyv _ |- _ => chk_merge OBY 4 end).

Lemma iir_outer_ip : forall rest done dn x mv (dl : word) (i : Z) (t0v t1v s2v s3v s4v s5v s6v s7v s8v : word) F1 fc mc,
xs = done ++ x :: rest -> length dn = length done -> i = Z.of_nat (length done) -> length mv = length den ->
frm0 fc -> munch W m mc -> offsh W -> wmono asegs m mc -> mem_inv asegs mc ->
stk asegs mc lo (usp + -80) ->
rw_cells asegs mc (usp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mc px (f32 dn) -> rw_cells asegs mc (px + 4 * i) (f32 (x :: rest)) ->
rw_cells asegs mc pm (f32 mv) -> rw_cells asegs mc pden (f32 den) -> rw_cells asegs mc (pden + 4 * (ord - 1)) [C4 dl] ->
evt asegs (iir_post true px W)
(MS (RI px t0v t1v (Z_to_bv 64 i) s2v s3v s4v s5v s6v s7v s8v) F1 (Z_to_bv 64 0xa38d0) fc None mc (seg_rom asegs)).
Proof using N1 ORD OBX OBD OBM X4 D4 M4 LO SPH XSH MSH XAP MAP DAP SEPDM SEPXM SEPXD.
clear LMEM.
induction rest as [|x' rest IH]; intros done dn x mv dl i t0v t1v s2v s3v s4v s5v s6v s7v s8v F1 fc mc Hxs LDN Hi Lmv FRM MU OF WM MI ST FR DONE X MEM DEN DL;
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
unfold RI; hide_disj.
-
iir_body px x i mc mv0 mv1 mvtt de0 de1 det s6v s7v s8v.
ato 0xa39f0. astep. sh_if.
ato 0xa3a6c. release_frame FR ST usp. astep. astep.
chunk_snoc MD ML. rewrite <- f32_nil, <- f32_cons, <- f32_app in MD.
chunk_snoc DONE X1. rewrite <- f32_nil, <- f32_cons, <- f32_app in DONE.
unfold iir_post. finish; [ | exact DONE | | exact MD | intros; discriminate ].
+ rewrite Hxs, !length_app. cbn [length]. lia.
+ rewrite length_app. cbn [length]. lia.
-
iir_body px x i mc mv0 mv1 mvtt de0 de1 det s6v s7v s8v.
ato 0xa39f0. astep. sh_if.
chunk_snoc MD ML. rewrite <- f32_nil, <- f32_cons, <- f32_app in MD.
chunk_snoc DONE X1. rewrite <- f32_nil, <- f32_cons, <- f32_app in DONE.
replace (px + 4 * i + 4) with (px + 4 * (i + 1)) in * by lia.
clear Lmv BM.
eapply (IH (done ++ [x]) _ x' _ dl (i + 1)); try eassumption.
all: try (rewrite Hxs, <- app_assoc; reflexivity).
all: try (rewrite !length_app; cbn [length]; lia).
Qed.

Lemma den_last : forall mc, rw_cells asegs mc pden (f32 den) -> exists dl, rw_cells asegs mc (pden + 4 * (ord - 1)) [C4 dl].
Proof using ORD.
clear - ORD. intros mc DEN.
destruct (exists_last (l := den)) as (dinit & dl & E); [intros ->; cbn [length] in ORD; lia|].
exists dl. rewrite E, f32_app in DEN. apply rw_cells_app in DEN. destruct DEN as [_ D]. rewrite cells_size_f32 in D.
rewrite f32_cons, f32_nil in D.
replace (pden + 4 * (ord - 1)) with (pden + Z.of_nat (4 * length dinit)); [exact D|].
rewrite E, length_app. cbn [length]. lia.
Qed.

Lemma iir_mem16_walk_ip : forall (F : bvmap 5 word) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) fc,
rw_cells asegs m px (f32 xs) -> rw_cells asegs m pden (f32 den) -> rw_cells asegs m pm (f32 mem0) -> frm0 fc ->
stk asegs m lo usp -> IMG_TOP <= px -> IMG_TOP <= pm ->
client_consts m -> mem_inv asegs m ->
evt asegs (iir_post true px W)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 px) (Z_to_bv 64 pden) (Z_to_bv 64 px) (Z_to_bv 64 N) (Z_to_bv 64 ord) (Z_to_bv 64 pm) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_iir_mem16) fc None m (seg_rom asegs)).
Proof using LMEM N1 ORD OBX OBD OBM X4 D4 M4 LO LOS SPH XSH MSH XAP MAP DAP SEPDM SEPXM SEPXD.
intros F t0 t1 t2 a6 a7 t3 t4 t5 t6 fc X DEN MEM FRM ST PTOP MTOP (G1 & G2 & _) MI.
unfold A_iir_mem16, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'. pose proof XSH as XSH'. unfold SH_LO, SH_HI in XSH'. pose proof MSH as MSH'. unfold SH_LO, SH_HI in MSH'.
unfold IMG_TOP in PTOP, MTOP.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX.
pose proof (rw_cells_bound _ _ _ _ DEN) as BD; rewrite cells_size_f32 in BD.
pose proof (rw_cells_bound _ _ _ _ MEM) as BM; rewrite cells_size_f32, LMEM in BM.
destruct (den_last m DEN) as (dl & DL).
pose proof ST as (STa & STb & _).
pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh W) by (cbn; unfold SH_LO, SH_HI; lia).
destruct xs as [|x rest] eqn:Exs; [cbn [length] in N1; lia|]. rewrite <- Exs in *.
hide_disj.
carve_frame 80%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 80 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xa388c. astep. rewrite ?signed_small64 by lia. try sh_if.
ato 0xa38d0.
rewrite (swrap32_small (ord + -1)) by lia.
rewrite ?(Z.mod_small (ord + -1) 18446744073709551616) by lia.
rewrite ?(Z.mod_small (ord + -1) 4294967296) by lia.
replace (Z.shiftl (ord + -1) 2) with (4 * (ord - 1)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
replace R with (RI px (Z_to_bv 64 (4 * (ord - 1))) (Z_to_bv 64 (Z.shiftl (ord + -1) 32)) (Z_to_bv 64 0) s2 s3 s4 s5 s6 s7 s8) by (unfold RI; reflexivity)
end.
replace px with (px + 4 * 0) in X at 1 by lia. rewrite Exs in X.
eapply (iir_outer_ip rest [] [] x mem0 dl 0); try eassumption; try reflexivity.
all: try (rewrite f32_nil; apply rw_cells_nil; lia).
Qed.

Section DJ.
Variable py : Z.
Hypothesis OBY : aobj asegs m py (4 * N).
Hypothesis Y4 : py mod 4 = 0.
Hypothesis YSH : py + 4 * N <= SH_LO \/ SH_HI <= py.
Hypothesis YAP : py + 4 * N <= lo \/ usp <= py.
Hypothesis SEPXY : px + 4 * N <= py \/ py + 4 * N <= px.
Hypothesis SEPYM : py + 4 * N <= pm \/ pm + 4 * ord <= py.
Hypothesis SEPYD : py + 4 * N <= pden \/ pden + 4 * ord <= py.
Local Notation WD := [(py, py + 4 * N); (pm, pm + 4 * ord); (usp + -80, usp)].

Lemma iir_outer_dj : forall rest done x yd y yrest mv (dl : word) (i : Z) (t0v t1v s2v s3v s4v s5v s6v s7v s8v : word) F1 fc mc,
xs = done ++ x :: rest -> length yd = length done -> length yrest = length rest -> i = Z.of_nat (length done) -> length mv = length den ->
frm0 fc -> munch WD m mc -> offsh WD -> wmono asegs m mc -> mem_inv asegs mc ->
stk asegs mc lo (usp + -80) ->
rw_cells asegs mc (usp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mc px (f32 xs) -> rw_cells asegs mc (px + 4 * i) (f32 (x :: rest)) ->
rw_cells asegs mc py (f32 yd) -> rw_cells asegs mc (py + 4 * i) (f32 (y :: yrest)) ->
rw_cells asegs mc pm (f32 mv) -> rw_cells asegs mc pden (f32 den) -> rw_cells asegs mc (pden + 4 * (ord - 1)) [C4 dl] ->
evt asegs (iir_post false py WD)
(MS (RI py t0v t1v (Z_to_bv 64 i) s2v s3v s4v s5v s6v s7v s8v) F1 (Z_to_bv 64 0xa38d0) fc None mc (seg_rom asegs)).
Proof using N1 ORD OBX OBD OBM OBY X4 D4 M4 Y4 LO SPH MSH YSH XAP MAP DAP YAP SEPDM SEPXM SEPXD SEPXY SEPYM SEPYD.
clear LMEM XSH.
induction rest as [|x' rest IH]; intros done x yd y yrest mv dl i t0v t1v s2v s3v s4v s5v s6v s7v s8v F1 fc mc Hxs LYD LYR Hi Lmv FRM MU OF WM MI ST FR XS XC YDONE Y MEM DEN DL;
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
unfold RI; hide_disj.
-
destruct yrest; [|cbn [length] in LYR; lia]. cbn [length] in BY.
chunk_split_f32 Y at 1%nat as Y1; rewrite ?f32_cons, ?f32_nil in Y1.
iir_body py x i mc mv0 mv1 mvtt de0 de1 det s6v s7v s8v.
ato 0xa39f0. astep. sh_if.
ato 0xa3a6c. release_frame FR ST usp. astep. astep.
chunk_snoc MD ML. rewrite <- f32_nil, <- f32_cons, <- f32_app in MD.
chunk_snoc YDONE Y1. rewrite <- f32_nil, <- f32_cons, <- f32_app in YDONE.
unfold iir_post. finish; [ | exact YDONE | | exact MD | intros _; exact XS ].
+ rewrite Hxs, !length_app. cbn [length]. lia.
+ rewrite length_app. cbn [length]. lia.
-
destruct yrest as [|y' yrest]; [cbn [length] in LYR; lia|]. cbn [length] in LYR, BY.
chunk_split_f32 Y at 1%nat as Y1; rewrite ?f32_cons, ?f32_nil in Y1.
iir_body py x i mc mv0 mv1 mvtt de0 de1 det s6v s7v s8v.
ato 0xa39f0. astep. sh_if.
chunk_snoc MD ML. rewrite <- f32_nil, <- f32_cons, <- f32_app in MD.
chunk_snoc YDONE Y1. rewrite <- f32_nil, <- f32_cons, <- f32_app in YDONE.
replace (px + 4 * i + 4) with (px + 4 * (i + 1)) in * by lia.
replace (py + 4 * i + 4) with (py + 4 * (i + 1)) in * by lia.
clear Lmv BM X1.
eapply (IH (done ++ [x]) x' _ y' yrest _ dl (i + 1)); try eassumption.
all: try (rewrite Hxs, <- app_assoc; reflexivity).
all: try (rewrite !length_app; cbn [length]; lia).
all: try lia.
Qed.

Lemma iir_mem16_walk_dj : forall (ys : list word) (F : bvmap 5 word) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) fc,
rw_cells asegs m px (f32 xs) -> rw_cells asegs m pden (f32 den) -> rw_cells asegs m pm (f32 mem0) ->
rw_cells asegs m py (f32 ys) -> length ys = length xs -> frm0 fc ->
stk asegs m lo usp -> IMG_TOP <= py -> IMG_TOP <= pm ->
client_consts m -> mem_inv asegs m ->
evt asegs (iir_post false py WD)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 px) (Z_to_bv 64 pden) (Z_to_bv 64 py) (Z_to_bv 64 N) (Z_to_bv 64 ord) (Z_to_bv 64 pm) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_iir_mem16) fc None m (seg_rom asegs)).
Proof using LMEM N1 ORD OBX OBD OBM OBY X4 D4 M4 Y4 LO LOS SPH MSH YSH XAP MAP DAP YAP SEPDM SEPXM SEPXD SEPXY SEPYM SEPYD.
clear XSH.
intros ys F t0 t1 t2 a6 a7 t3 t4 t5 t6 fc X DEN MEM Y LYS FRM ST PTOP MTOP (G1 & G2 & _) MI.
unfold A_iir_mem16, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'. pose proof YSH as YSH'. unfold SH_LO, SH_HI in YSH'. pose proof MSH as MSH'. unfold SH_LO, SH_HI in MSH'.
unfold IMG_TOP in PTOP, MTOP.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX.
pose proof (rw_cells_bound _ _ _ _ Y) as BY; rewrite cells_size_f32, LYS in BY.
pose proof (rw_cells_bound _ _ _ _ DEN) as BD; rewrite cells_size_f32 in BD.
pose proof (rw_cells_bound _ _ _ _ MEM) as BM; rewrite cells_size_f32, LMEM in BM.
destruct (den_last m DEN) as (dl & DL).
pose proof ST as (STa & STb & _).
pose proof (munch_refl WD m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh WD) by (cbn; unfold SH_LO, SH_HI; lia).
destruct xs as [|x rest] eqn:Exs; [cbn [length] in N1; lia|]. rewrite <- Exs in *.
destruct ys as [|y yrest] eqn:Eys; [rewrite Exs in LYS; cbn [length] in LYS; lia|]. cbn [length] in LYS, BY.
hide_disj.
carve_frame 80%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 80 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xa388c. astep. rewrite ?signed_small64 by lia. try sh_if.
ato 0xa38d0.
rewrite (swrap32_small (ord + -1)) by lia.
rewrite ?(Z.mod_small (ord + -1) 18446744073709551616) by lia.
rewrite ?(Z.mod_small (ord + -1) 4294967296) by lia.
replace (Z.shiftl (ord + -1) 2) with (4 * (ord - 1)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
replace R with (RI py (Z_to_bv 64 (4 * (ord - 1))) (Z_to_bv 64 (Z.shiftl (ord + -1) 32)) (Z_to_bv 64 0) s2 s3 s4 s5 s6 s7 s8) by (unfold RI; reflexivity)
end.
pose proof X as XC. replace px with (px + 4 * 0) in XC at 1 by lia. rewrite Exs in XC.
replace py with (py + 4 * 0) in Y at 1 by lia.
eapply (iir_outer_dj rest [] x [] y yrest mem0 dl 0); try eassumption; try reflexivity.
all: try (rewrite f32_nil; apply rw_cells_nil; lia).
all: try (rewrite Exs in LYS; cbn [length] in LYS; lia).
Qed.
End DJ.
End SI.
