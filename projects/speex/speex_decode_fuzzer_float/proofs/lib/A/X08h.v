(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg X1df X1ck X1co.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05l.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac tlia ::= tlia_one.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).

Lemma f32_snoc l x : f32 l ++ [C4 x] = f32 (l ++ [x]).
Proof. rewrite f32_app, f32_cons, f32_nil. reflexivity. Qed.

Section L1.
Variables (EO XB I1 I2 NE : Z).
Variables rav spv gp tp t1v t2v s0v s1v s2v s3v s4v s7v s8v s10v s11v t3v t4v t5v t6v : word.
Hypothesis E4 : EO mod 4 = 0.
Hypothesis I4 : I1 mod 4 = 0.
Hypothesis N4 : NE mod 4 = 0.
Hypothesis XBR : EO <= XB /\ XB + 320 <= EO + 2000 /\ (XB - EO) mod 4 = 0.
Hypothesis SEPE : NE + 320 <= EO \/ EO + 2000 <= NE.
Hypothesis SEPI : NE + 320 <= I1 \/ I1 + 640 <= NE.
Hypothesis NI : IMG_TOP <= NE.

Definition R1 (xa ia ja na cnt : Z) (t0v a7v : word) : bvmap 5 word :=
mkR rav spv gp tp t0v t1v t2v s0v s1v (Z_to_bv 64 xa) (Z_to_bv 64 na) (Z_to_bv 64 cnt) (Z_to_bv 64 xa) (Z_to_bv 64 ia) (Z_to_bv 64 na) (Z_to_bv 64 ja) a7v
s2v s3v s4v (Z_to_bv 64 ia) (Z_to_bv 64 ja) s7v s8v (Z_to_bv 64 SHB) s10v s11v t3v t4v t5v t6v.

Definition l1_post (mI : mem) : machine_state -> Prop :=
fun ms' => exists t0' a7' F' fc' m' (ns' : list word),
ms' = MS (R1 (XB + 320) (I1 + 320) (I1 + 640) (NE + 320) 0 t0' a7') F' (Z_to_bv 64 0xa5768) fc' None m' (seg_rom asegs)
/\ munch [(NE, NE + 320)] mI m' /\ wmono asegs mI m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ length ns' = 80%nat /\ rw_cells asegs m' NE (f32 ns').

Lemma mc_L1 : forall (mI : mem) (rest xr ir jr done : list word) (cw xw iw jw : word) (i xa ia ja na cnt : Z) (t0v a7v : word) F1 fc mc,
xa = XB + 4 * i -> ia = I1 + 4 * i -> ja = I1 + 320 + 4 * i -> na = NE + 4 * i -> cnt = 1 + Z.of_nat (length rest) ->
i = Z.of_nat (length done) -> i + 1 + Z.of_nat (length rest) = 80 -> length xr = length rest -> length ir = length rest -> length jr = length rest ->
aobj asegs mI EO 2000 -> aobj asegs mI I1 640 -> aobj asegs mI NE 320 -> offsh [(NE, NE + 320)] ->
frm0 fc -> mem_inv asegs mc -> munch [(NE, NE + 320)] mI mc -> wmono asegs mI mc ->
rw_cells asegs mc xa (f32 (xw :: xr)) -> rw_cells asegs mc ia (f32 (iw :: ir)) -> rw_cells asegs mc ja (f32 (jw :: jr)) ->
rw_cells asegs mc NE (f32 done) -> rw_cells asegs mc na (f32 (cw :: rest)) ->
evt asegs (l1_post mI) (MS (R1 xa ia ja na cnt t0v a7v) F1 (Z_to_bv 64 0xa569c) fc None mc (seg_rom asegs)).
Proof using E4 I4 N4 XBR SEPE SEPI NI.
intros mI rest.
induction rest as [|cw' rest IH]; intros xr ir jr done cw xw iw jw i xa ia ja na cnt t0v a7v F1 fc mc -> -> -> -> -> Hi HN LX LI LJ OBE OBI OBN OF FRM MI MU WM XX XI XJ XD XC;
pose proof OBE as (OE0 & OE1 & _); pose proof OBI as (OI0 & OI1 & _); pose proof OBN as (ON0 & ON1 & _); unfold APP_TOP in *;
pose proof NI as NI'; unfold IMG_TOP in NI';
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
unfold R1; rewrite !f32_cons in XC; cbn [length] in *;
replace (XB + 4 * i) with (EO + (XB - EO + 4 * i)) in * by lia;
hide_disj.
- destruct xr; [|cbn in LX; lia]. destruct ir; [|cbn in LI; lia]. destruct jr; [|cbn in LJ; lia]. rewrite f32_nil in XC.
pose proof XX as X1h. pose proof XI as I1h. pose proof XJ as J1h. rewrite f32_cons, f32_nil in X1h, I1h, J1h.
ato 0xa56a8. astep. chk_merge OBE 4.
ato 0xa56bc. astep. chk_merge OBI 4.
ato 0xa56d0. astep. chk_merge OBI 4.
ato 0xa56e4. astep. chk_merge OBN 4.
clear X1h I1h J1h XX XI XJ.
ato 0xa571c. astep. sh_if. astep.
chunk_snoc XD XC. rewrite f32_snoc in XD.
replace (EO + (XB - EO + 4 * i) + 4) with (XB + 320) by lia. replace (I1 + 4 * i + 4) with (I1 + 320) by lia.
replace (I1 + 320 + 4 * i + 4) with (I1 + 640) by lia. replace (NE + 4 * i + 4) with (NE + 320) by lia.
replace (1 + Z.of_nat 0 + -1) with 0 by lia.
unfold l1_post, R1. finish; [ | exact XD ]. rewrite length_app. cbn [length]. lia.
- destruct xr as [|xw' xr]; [cbn in LX; lia|]. destruct ir as [|iw' ir]; [cbn in LI; lia|]. destruct jr as [|jw' jr]; [cbn in LJ; lia|]. cbn [length] in LX, LI, LJ.
pose proof XX as X1h. chunk_split_f32 X1h at 1%nat as X1c. rewrite ?f32_cons, ?f32_nil in X1c. clear X1h.
pose proof XI as I1h. chunk_split_f32 I1h at 1%nat as I1c. rewrite ?f32_cons, ?f32_nil in I1c. clear I1h.
pose proof XJ as J1h. chunk_split_f32 J1h at 1%nat as J1c. rewrite ?f32_cons, ?f32_nil in J1c. clear J1h.
ato 0xa56a8. astep. chk_merge OBE 4.
ato 0xa56bc. astep. chk_merge OBI 4.
ato 0xa56d0. astep. chk_merge OBI 4.
ato 0xa56e4. astep. chk_merge OBN 4.
clear X1c I1c J1c.
ato 0xa571c. astep. sh_if.
apply rw_f32_uncons in XX. apply rw_f32_uncons in XI. apply rw_f32_uncons in XJ.
chunk_uncons XC as C1c. chunk_snoc XD C1c. rewrite f32_snoc in XD. rewrite <- ?f32_cons in XC.
replace (1 + Z.of_nat (S (length rest)) + -1) with (1 + Z.of_nat (length rest)) by lia.
eapply (IH xr ir jr _ cw' xw' iw' jw' (i + 1)); try eassumption;
try (rewrite length_app; cbn [length] in *; lia); try (cbn [length] in *; lia).
Qed.
End L1.

Section L23.
Variables (m : mem) (OB : Z) (ON : Z).
Hypothesis OBJ : aobj asegs m OB ON.
Hypothesis O4 : OB mod 4 = 0.

Section L2.
Variables rav spv gp tp t0v t1v t2v s0v s1v a5v a6v a7v s2v s3v s4v s5v s6v s7v s8v s10v s11v t3v t4v t5v t6v : word.
Definition R2 (na cnt : Z) (a3v a4v : word) : bvmap 5 word :=
mkR rav spv gp tp t0v t1v t2v s0v s1v (Z_to_bv 64 na) (Z_to_bv 64 cnt) (Z_to_bv 64 na) a3v a4v a5v a6v a7v
s2v s3v s4v s5v s6v s7v s8v (Z_to_bv 64 SHB) s10v s11v t3v t4v t5v t6v.
Definition l2_post (W : Z) : machine_state -> Prop :=
fun ms' => exists a3' a4' F' fc', ms' = MS (R2 (W + 320) 0 a3' a4') F' (Z_to_bv 64 0xa57b8) fc' None m (seg_rom asegs) /\ frm0 fc'.
Lemma mc_L2 : forall (k : nat) (xr : list word) (xw : word) (W i na cnt : Z) (a3v a4v : word) F1 fc,
na = W + 4 * i -> cnt = 1 + Z.of_nat k -> length xr = k -> i + 1 + Z.of_nat k = 80 -> 0 <= i ->
OB <= W -> W + 320 <= OB + ON -> (W - OB) mod 4 = 0 ->
frm0 fc -> mem_inv asegs m -> rw_cells asegs m na (f32 (xw :: xr)) ->
evt asegs (l2_post W) (MS (R2 na cnt a3v a4v) F1 (Z_to_bv 64 0xa577c) fc None m (seg_rom asegs)).
Proof using OBJ O4.
pose proof OBJ as (OO0 & OO1 & _). unfold APP_TOP in *.
induction k as [|k IH]; intros xr xw W i na cnt a3v a4v F1 fc -> -> LX HN Hi0 HW0 HW1 HW4 FRM MI XX;
unfold R2; replace (W + 4 * i) with (OB + (W - OB + 4 * i)) in * by lia.
- destruct xr; [|cbn in LX; lia]. rewrite f32_cons, f32_nil in XX.
ato 0xa5788. astep. chk_merge OBJ 4.
ato 0xa57a0. astep. sh_if. astep.
replace (OB + (W - OB + 4 * i) + 4) with (W + 320) by lia. replace (1 + Z.of_nat 0 + -1) with 0 by lia.
apply evt_done; unfold l2_post, R2. do 4 eexists. split; [reflexivity| assumption].
- destruct xr as [|xw' xr]; [cbn in LX; lia|]. cbn [length] in LX. rewrite !f32_cons in XX.
ato 0xa5788. astep. chk_merge OBJ 4.
ato 0xa57a0. astep. sh_if.
rewrite <- !f32_cons in XX. apply rw_f32_uncons in XX.
replace (1 + Z.of_nat (S k) + -1) with (1 + Z.of_nat k) by lia.
eapply (IH xr xw' W (i + 1)); try eassumption; try lia.
Qed.
End L2.

Section L3.
Variables rav spv gp tp t0v t1v t2v s0v s1v a4v a5v a6v a7v s2v s3v s5v s6v s7v s8v s10v s11v t3v t4v t5v t6v : word.
Definition R3 (xa cnt : Z) (a2v a3v : word) : bvmap 5 word :=
mkR rav spv gp tp t0v t1v t2v s0v s1v (Z_to_bv 64 xa) (Z_to_bv 64 cnt) a2v a3v a4v a5v a6v a7v
s2v s3v (Z_to_bv 64 xa) s5v s6v s7v s8v (Z_to_bv 64 SHB) s10v s11v t3v t4v t5v t6v.
Definition l3_post (W : Z) : machine_state -> Prop :=
fun ms' => exists a2' a3' F' fc', ms' = MS (R3 (W + 320) 0 a2' a3') F' (Z_to_bv 64 0xa5804) fc' None m (seg_rom asegs) /\ frm0 fc'.
Lemma mc_L3 : forall (k : nat) (xr : list word) (xw : word) (W i xa cnt : Z) (a2v a3v : word) F1 fc,
xa = W + 4 * i -> cnt = 1 + Z.of_nat k -> length xr = k -> i + 1 + Z.of_nat k = 80 -> 0 <= i ->
OB <= W -> W + 320 <= OB + ON -> (W - OB) mod 4 = 0 ->
frm0 fc -> mem_inv asegs m -> rw_cells asegs m xa (f32 (xw :: xr)) ->
evt asegs (l3_post W) (MS (R3 xa cnt a2v a3v) F1 (Z_to_bv 64 0xa57c8) fc None m (seg_rom asegs)).
Proof using OBJ O4.
pose proof OBJ as (OO0 & OO1 & _). unfold APP_TOP in *.
induction k as [|k IH]; intros xr xw W i xa cnt a2v a3v F1 fc -> -> LX HN Hi0 HW0 HW1 HW4 FRM MI XX;
unfold R3; replace (W + 4 * i) with (OB + (W - OB + 4 * i)) in * by lia.
- destruct xr; [|cbn in LX; lia]. rewrite f32_cons, f32_nil in XX.
ato 0xa57d4. astep. chk_merge OBJ 4.
ato 0xa57ec. astep. sh_if. astep.
replace (OB + (W - OB + 4 * i) + 4) with (W + 320) by lia. replace (1 + Z.of_nat 0 + -1) with 0 by lia.
apply evt_done; unfold l3_post, R3. do 4 eexists. split; [reflexivity| assumption].
- destruct xr as [|xw' xr]; [cbn in LX; lia|]. cbn [length] in LX. rewrite !f32_cons in XX.
ato 0xa57d4. astep. chk_merge OBJ 4.
ato 0xa57ec. astep. sh_if.
rewrite <- !f32_cons in XX. apply rw_f32_uncons in XX.
replace (1 + Z.of_nat (S k) + -1) with (1 + Z.of_nat k) by lia.
eapply (IH xr xw' W (i + 1)); try eassumption; try lia.
Qed.
End L3.
End L23.

Section L4.
Variables (NE : Z).
Variables rav spv gp tp t0v t1v t2v s0v s1v a3v a4v a5v a6v a7v s4v s5v s6v s7v s8v s10v s11v t3v t4v t5v t6v : word.
Hypothesis N4 : NE mod 4 = 0.
Hypothesis NI : IMG_TOP <= NE.
Definition R4 (na cnt : Z) (a1v a2v : word) : bvmap 5 word :=
mkR rav spv gp tp t0v t1v t2v s0v s1v (Z_to_bv 64 na) a1v a2v a3v a4v a5v a6v a7v
(Z_to_bv 64 cnt) (Z_to_bv 64 na) s4v s5v s6v s7v s8v (Z_to_bv 64 SHB) s10v s11v t3v t4v t5v t6v.
Definition l4_post (mI : mem) : machine_state -> Prop :=
fun ms' => exists a1' a2' F' fc' m' (ns' : list word),
ms' = MS (R4 (NE + 320) 0 a1' a2') F' (Z_to_bv 64 0xa58b8) fc' None m' (seg_rom asegs)
/\ munch [(NE, NE + 320)] mI m' /\ wmono asegs mI m' /\ mem_inv asegs m'
/\ frm0 fc'
/\ length ns' = 80%nat /\ rw_cells asegs m' NE (f32 ns').
Lemma mc_L4 : forall (mI : mem) (rest done : list word) (cw : word) (i na cnt : Z) (a1v a2v : word) F1 fc mc,
na = NE + 4 * i -> cnt = 1 + Z.of_nat (length rest) -> i = Z.of_nat (length done) -> i + 1 + Z.of_nat (length rest) = 80 ->
aobj asegs mI NE 320 -> offsh [(NE, NE + 320)] ->
frm0 fc -> mem_inv asegs mc -> munch [(NE, NE + 320)] mI mc -> wmono asegs mI mc ->
rw_cells asegs mc NE (f32 done) -> rw_cells asegs mc na (f32 (cw :: rest)) ->
evt asegs (l4_post mI) (MS (R4 na cnt a1v a2v) F1 (Z_to_bv 64 0xa5878) fc None mc (seg_rom asegs)).
Proof using N4 NI.
intros mI rest.
induction rest as [|cw' rest IH]; intros done cw i na cnt a1v a2v F1 fc mc -> -> Hi HN OBN OF FRM MI MU WM XD XC;
pose proof OBN as (ON0 & ON1 & _); unfold APP_TOP in *; pose proof NI as NI'; unfold IMG_TOP in NI';
pose proof (rw_cells_bound _ _ _ _ XC) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC;
unfold R4; rewrite !f32_cons in XC; cbn [length] in *.
- rewrite f32_nil in XC.
ato 0xa5884. astep. chk_merge OBN 4.
ato 0xa58a0. astep. sh_if. astep.
chunk_snoc XD XC. rewrite f32_snoc in XD.
replace (NE + 4 * i + 4) with (NE + 320) by lia. replace (1 + Z.of_nat 0 + -1) with 0 by lia.
unfold l4_post, R4. finish; [ | exact XD ]. rewrite length_app. cbn [length]. lia.
- ato 0xa5884. astep. chk_merge OBN 4.
ato 0xa58a0. astep. sh_if.
chunk_uncons XC as C1c. chunk_snoc XD C1c. rewrite f32_snoc in XD. rewrite <- ?f32_cons in XC.
replace (1 + Z.of_nat (S (length rest)) + -1) with (1 + Z.of_nat (length rest)) by lia.
eapply (IH _ cw' (i + 1)); try eassumption;
try (rewrite length_app; cbn [length] in *; lia); try (cbn [length] in *; lia).
Qed.
End L4.
