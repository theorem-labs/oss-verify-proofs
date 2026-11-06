(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05l.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition A_speex_bits_read_from : Z := 0x97988.
Definition A_readfrom_join : Z := 0x979f0.
Definition A_readfrom_loop : Z := 0x97a08.
Definition A_readfrom_tail : Z := 0x97a9c.

Lemma firstn_S_nth {T} : forall (l : list T) i d, (i < length l)%nat -> firstn (S i) l = firstn i l ++ [nth i l d].
Proof.
induction l as [|x l IH]; intros [|i] d H; cbn in *; try lia; [reflexivity|].
f_equal. apply IH. lia.
Qed.
Lemma upd_prefix_step : forall (pb ds : list byte) (i : nat),
(i < length pb)%nat -> (i < length ds)%nat ->
upd (firstn i pb ++ skipn i ds) i (nth i pb (Z_to_bv 8 0)) = firstn (S i) pb ++ skipn (S i) ds.
Proof.
intros pb ds i Hp Hd.
destruct (upd_app_split (firstn i pb ++ skipn i ds) i (nth i pb (Z_to_bv 8 0))
ltac:(rewrite length_app, length_firstn, length_skipn; lia)) as (pre & y & post & E & Hlen & Hupd).
rewrite Hupd.
assert (Epre : pre = firstn i pb).
{ apply (f_equal (firstn i)) in E. rewrite firstn_app, firstn_firstn, Nat.min_id, length_firstn in E.
replace (i - Nat.min i (length pb))%nat with 0%nat in E by lia. cbn in E. rewrite app_nil_r in E.
rewrite E, firstn_app, Hlen, Nat.sub_diag, firstn_all2 by lia. cbn. rewrite app_nil_r. reflexivity. }
assert (Epost : post = skipn (S i) ds).
{ apply (f_equal (skipn (S i))) in E. rewrite skipn_app, length_firstn in E.
replace (S i - Nat.min i (length pb))%nat with 1%nat in E by lia.
rewrite skipn_all2 in E by (rewrite length_firstn; lia). cbn [app] in E. rewrite skipn_skipn in E.
replace (1 + i)%nat with (S i) in E by lia. rewrite E.
rewrite skipn_app, Hlen. replace (S i - i)%nat with 1%nat by lia. rewrite skipn_all2 by lia. reflexivity. }
rewrite Epre, Epost. rewrite (firstn_S_nth pb i (Z_to_bv 8 0)) by lia. rewrite <- app_assoc. reflexivity.
Qed.

Lemma map_unsigned_app_take : forall (n : Z) (pb ds0 : list byte) (d : list Z),
0 <= n -> d = map bv_unsigned (skipn (Z.to_nat n) ds0) ->
ztake n (map bv_unsigned pb) ++ d = map bv_unsigned (firstn (Z.to_nat n) pb ++ skipn (Z.to_nat n) ds0).
Proof. intros n pb ds0 d Hn ->. unfold ztake. rewrite map_app, firstn_map. reflexivity. Qed.

Section Body.
Context {ptr : Type}.
Variables (A P : Z) (pb : list byte).
Variables (gp tp s4 s7 s8 s9 s10 s11 : word).

Lemma readfrom_loop : forall (k : nat) (i pa nchars D' : Z) (ds0 cur : list byte) (b1 : bits_st ptr) (rj : list byte)
(rav spv s3v s6v a1v a5v a6v a7v t0 t1 t2 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc1 : bv 32)
(W : list (Z * Z)) (m0 m1 : mem),
Z.of_nat k = nchars - i -> 0 <= i < nchars -> pa = P + i ->
nchars <= Z.of_nat (length ds0) -> nchars <= Z.of_nat (length pb) -> Z.of_nat (length ds0) < 2^24 -> nchars < 2^31 ->
length rj = 16%nat -> rw_cells bsegs m1 A (bits_cells D' b1 rj) ->
cur = firstn (Z.to_nat i) pb ++ skipn (Z.to_nat i) ds0 -> length cur = length ds0 -> u8arr bsegs m1 D' cur ->
u8ro bsegs m1 P pb ->
(P + Z.of_nat (length pb) <= D' \/ D' + Z.of_nat (length ds0) <= P) ->
(A + 48 <= D' \/ D' + Z.of_nat (length ds0) <= A) ->
0 < D' -> 0 < A -> 0 < P -> A mod 8 = 0 ->
aobj bsegs m0 A 48 -> aobj bsegs m0 P (Z.of_nat (length pb)) -> aobj bsegs m0 D' (Z.of_nat (length ds0)) ->
offsh ((D', D' + Z.of_nat (length ds0)) :: W) ->
munch ((D', D' + Z.of_nat (length ds0)) :: W) m0 m1 -> wmono bsegs m0 m1 -> mem_inv bsegs m1 ->
evt bsegs (fun ms' => exists (a0' a1' a5' a6' a7' : word) (m2 : mem),
ms' = MS (mkR rav spv gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 P) a0' a1' (Z_to_bv 64 nchars) (Z_to_bv 64 1) (Z_to_bv 64 (Z.shiftr A 3 + SHB)) a5' a6' a7'
(Z_to_bv 64 nchars) s3v s4 (Z_to_bv 64 SHB) s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (Z_to_bv 64 A_readfrom_tail) fc1 None m2 (seg_rom bsegs)
/\ rw_cells bsegs m2 A (bits_cells D' b1 rj)
/\ u8arr bsegs m2 D' (firstn (Z.to_nat nchars) pb ++ skipn (Z.to_nat nchars) ds0)
/\ u8ro bsegs m2 P pb
/\ munch ((D', D' + Z.of_nat (length ds0)) :: W) m0 m2 /\ wmono bsegs m0 m2 /\ mem_inv bsegs m2)
(MS (mkR rav spv gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 P) (Z_to_bv 64 pa) a1v (Z_to_bv 64 i) (Z_to_bv 64 1) (Z_to_bv 64 (Z.shiftr A 3 + SHB)) a5v a6v a7v
(Z_to_bv 64 nchars) s3v s4 (Z_to_bv 64 SHB) s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (Z_to_bv 64 A_readfrom_loop) fc1 None m1 (seg_rom bsegs)).

Proof.
induction k as [|k IH]; intros i pa nchars D' ds0 cur b1 rj rav spv s3v s6v a1v a5v a6v a7v t0 t1 t2 t3 t4 t5 t6 Ft fc1 W m0 m1
Hk Hi Hpa Hnd Hnp Hds Hn31 Lrj OBJ Ecur Lcur CUR SRC SEP1 SEP2 Dpos Apos Ppos A8 OBA OBP OBD OF MU WM MI; [lia|].
subst pa. unfold bits_cells in OBJ. unfold A_readfrom_loop, A_readfrom_tail.
pose proof (rw_cells_bound _ _ _ _ OBJ) as GB. cbn [cells_size csize Nat.add length] in GB.
pose proof (u8arr_bound _ _ _ _ CUR) as DB. rewrite Lcur in DB.
pose proof (bytes_at_bound _ _ _ _ SRC) as PB.
pose proof OBP as (OP0 & OP1 & _). pose proof OBD as (OD0 & OD1 & _). unfold APP_TOP in *.
assert (Hnth : nth_error pb (Z.to_nat i) = Some (nth (Z.to_nat i) pb (Z_to_bv 8 0))) by (apply nth_error_nth'; lia).
pose proof (u8ro_read _ _ _ _ i _ _ SRC Hnth ltac:(lia) eq_refl) as RD.
astep. sh_if.
ato 0x97a14. replace (P + i <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.lxor].
ato 0x97a18. astep. sh_if.
ato 0x97a28. astep. chk_merge OBP 1.
ato 0x97a3c. astep. sh_if.
ato 0x97a4c. replace (0 <? D') with true by (symmetry; apply Z.ltb_lt; lia).
replace (D' + i <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.lxor].
ato 0x97a50. astep. sh_if.
ato 0x97a68. astep. chk_merge OBD 1.
pose proof (u8arr_store_ok bsegs _ _ _ i _ CUR ltac:(lia) eq_refl) as SOK.
astep. replace (le1 (Z_to_bv 64 (bv_unsigned (nth (Z.to_nat i) pb (Z_to_bv 8 0))))) with [nth (Z.to_nat i) pb (Z_to_bv 8 0)] by (symmetry; apply le1_zxb).
pose proof (u8arr_write bsegs _ _ _ i (nth (Z.to_nat i) pb (Z_to_bv 8 0)) CUR ltac:(lia)) as CUR'.
clear CUR. store_done. try clear SOK.
assert (Ecur' : upd cur (Z.to_nat i) (nth (Z.to_nat i) pb (Z_to_bv 8 0)) = firstn (Z.to_nat (i + 1)) pb ++ skipn (Z.to_nat (i + 1)) ds0).
{ rewrite Ecur. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. apply upd_prefix_step; lia. }
ato 0x97a78.
astep. if_cases K; zify_cond K.
-
eapply (IH (i + 1) _ nchars D' ds0); try eassumption; try lia.
rewrite upd_length. exact Lcur.
-
astep.
replace nchars with (i + 1) by lia. rewrite <- Ecur'.
apply evt_done. do 6 eexists. split; [reflexivity|].
refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); eassumption.
Qed.

Lemma readfrom_tail : forall (nchars D' usp lo : Z) (ds0 : list byte) (b1 : bits_st ptr) (rj j0 : list byte)
(rav s6v a0v a1v a2v a3v a4v a5v a6 a7 t0 t1 t2 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 cra : word) (Ft : bvmap 5 word) (fc1 : bv 32) (m1 : mem),
length rj = 16%nat -> rw_cells bsegs m1 A (bits_cells D' b1 rj) ->
u8arr bsegs m1 D' ds0 -> Z.of_nat (length ds0) = sb_buf_size b1 ->
u8ro bsegs m1 P pb ->
0 <= nchars <= sb_buf_size b1 -> nchars <= Z.of_nat (length pb) -> 1 <= sb_buf_size b1 < 2^24 ->
zdrop nchars (sb_data b1) = map bv_unsigned (skipn (Z.to_nat nchars) ds0) ->
0 <= sb_owner b1 <= 1 -> 0 < D' -> 0 < P -> 0 < A -> A mod 8 = 0 ->
(P + Z.of_nat (length pb) <= D' \/ D' + Z.of_nat (length ds0) <= P) ->
(P + Z.of_nat (length pb) <= A \/ A + 48 <= P) ->
(A + 48 <= D' \/ D' + Z.of_nat (length ds0) <= A) ->
rw_cells bsegs m1 (usp + -80) [CB 8 j0; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra] ->
stk bsegs m1 lo (usp + -80) -> lo <= usp + -80 -> SH_HI <= lo -> usp < 2^63 ->
A + 48 <= lo -> D' + Z.of_nat (length ds0) <= lo -> P + Z.of_nat (length pb) <= lo ->
(A + 48 <= SH_LO \/ SH_HI <= A) -> (D' + Z.of_nat (length ds0) <= SH_LO \/ SH_HI <= D') ->
aobj bsegs m1 A 48 -> aobj bsegs m1 P (Z.of_nat (length pb)) -> aobj bsegs m1 D' (Z.of_nat (length ds0)) ->
mem_inv bsegs m1 ->
evt bsegs (fun ms' => exists (a0' a1' a2' a3' a4' a5' a6' a7' : word) (m2 : mem),
ms' = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 a0' a1' a2' a3' a4' a5' a6' a7' c2 c3 c4 c5 c6 c7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc cra) fc1 None m2 (seg_rom bsegs)
/\ munch [(D', D' + Z.of_nat (length ds0)); (A, A + 48); (usp + -80, usp)] m1 m2 /\ wmono bsegs m1 m2 /\ mem_inv bsegs m2 /\ stk bsegs m2 lo usp
/\ bits_rep bsegs m2 A D' (mkBits (sb_chars b1) (ztake nchars (map bv_unsigned pb) ++ zdrop nchars (sb_data b1)) (nchars * 8) 0 0 (sb_owner b1) 0 (sb_buf_size b1))
/\ bits_ok (mkBits (sb_chars b1) (ztake nchars (map bv_unsigned pb) ++ zdrop nchars (sb_data b1)) (nchars * 8) 0 0 (sb_owner b1) 0 (sb_buf_size b1))
/\ u8ro bsegs m2 P pb)
(MS (mkR rav (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 P) a0v a1v a2v a3v a4v a5v a6 a7
(Z_to_bv 64 nchars) (Z_to_bv 64 (A + 28)) s4 (Z_to_bv 64 SHB) s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (Z_to_bv 64 A_readfrom_join) fc1 None m1 (seg_rom bsegs)).

Proof.
intros until m1. intros Lrj OBJ DST Lds SRC Hn Hnp Hbuf Hdrop OWN Dpos Ppos Apos AL SEP1 SEP3 SEP2 FR ST LO LOS SPH ALO DLO PLO ASH DSH OBA OBP OBD MI.
pose proof LOS as LOS'. pose proof ASH as ASH'. pose proof DSH as DSH'. unfold SH_LO, SH_HI in LOS', ASH', DSH'.
pose proof (rw_cells_bound _ _ _ _ OBJ) as GB. rewrite bits_cells_size in GB by exact Lrj.
pose proof (u8arr_bound _ _ _ _ DST) as DB. pose proof (bytes_at_bound _ _ _ _ SRC) as PB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(D', D' + Z.of_nat (length ds0))] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
assert (OF : offsh [(D', D' + Z.of_nat (length ds0))]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold A_readfrom_join.

eapply evt_cut with (P := fun ms' => exists (a0' a1' a2' a3' a4' a5' a6' a7' : word) (m2 : mem),
ms' = MS (mkR rav (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 P) a0' a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 nchars) (Z_to_bv 64 (A + 28)) s4 (Z_to_bv 64 SHB) s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (Z_to_bv 64 A_readfrom_tail) fc1 None m2 (seg_rom bsegs)
/\ rw_cells bsegs m2 A (bits_cells D' b1 rj)
/\ u8arr bsegs m2 D' (firstn (Z.to_nat nchars) pb ++ skipn (Z.to_nat nchars) ds0)
/\ munch [(D', D' + Z.of_nat (length ds0))] m1 m2 /\ wmono bsegs m1 m2 /\ mem_inv bsegs m2).
{ astep. if_cases K; zify_cond K.
-
assert (N0 : nchars = 0) by (apply andb_false_iff in K; destruct K as [K|K]; [apply Z.ltb_ge in K| apply Z.ltb_ge in K]; lia).
replace (Z.to_nat nchars) with 0%nat by lia. cbn [firstn skipn app]. unfold A_readfrom_tail.
apply evt_done. do 9 eexists. split; [reflexivity|].
refine (conj _ (conj _ (conj _ (conj _ _)))); eassumption.
- ato 0x97a08. replace (0 <? P) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
eapply evt_mono.
+ eapply (readfrom_loop (Z.to_nat nchars) 0 P nchars D' ds0 ds0 b1 rj); try eassumption; try lia; try reflexivity.
+ cbv beta. intros ms' (a0' & a1' & a5' & a6' & a7' & m2 & -> & OBJ2 & DST2 & _ & MU2 & WM2 & MI2).
do 9 eexists. split; [reflexivity|].
refine (conj _ (conj _ (conj _ (conj _ _)))); eassumption. }
cbv beta. intros ms' (a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m2 & -> & OBJ2 & DST2 & MU2 & WM2 & MI2).
pose proof (aobj_munch bsegs _ m1 m2 A 48 OBA MU2 (shfree_of_aobj bsegs _ m1 A 48 OF OBA)) as OBA2.
clear MU WM OF. unfold A_readfrom_tail. unfold bits_cells in OBJ2.
pose proof (rw_cells_transport bsegs _ m1 m2 _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FR2.
pose proof (stk_transport_disjoint bsegs _ m1 m2 _ _ ST MU2 WM2 ltac:(cbn [disjoint_from]; lia)) as ST2.
pose proof (bytes_at_transport bsegs _ m1 m2 _ _ SRC MU2 ltac:(cbn [disjoint_from]; lia)) as SRC2.
clear FR ST DST SRC OBJ MI.
assert (MU : munch [(D', D' + Z.of_nat (length ds0)); (A, A + 48); (usp + -80, usp)] m1 m2)
by (apply (munch_weaken [(D', D' + Z.of_nat (length ds0))]); [intros x Hx; cbn [outside] in *; tauto| exact MU2]).
assert (OF : offsh [(D', D' + Z.of_nat (length ds0)); (A, A + 48); (usp + -80, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
clear MU2. rename WM2 into WM.
remember (firstn (Z.to_nat nchars) pb ++ skipn (Z.to_nat nchars) ds0) as cur2 eqn:Ecur2.
assert (Lc2 : length cur2 = length ds0) by (rewrite Ecur2, length_app, length_firstn, length_skipn; lia).
assert (N28 : Z.shiftr nchars 28 = 0) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
ato 0x97aa0. rewrite wrap32_small by lia. rewrite N28. change (bv_swrap 32 0) with 0.
ato 0x97abc. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
ato 0x97b2c. release_frame FR2 ST2 usp. astep. astep.
apply evt_done. do 9 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST2|].
split; [| split].
- split; [|split].
+ exists rj. split; [exact Lrj|]. unfold bits_cells; cbn [sb_nbBits sb_charPtr sb_bitPtr sb_owner sb_overflow sb_buf_size sb_chars]. eassumption.
+ exists cur2. split; [eassumption|]. cbn [sb_data]. rewrite Ecur2. apply map_unsigned_app_take; [lia| exact Hdrop].
+ unfold bits_side; cbn. unfold BITS_BUF_MAX, BITS_SIZEOF. repeat split; try lia.
- unfold bits_ok, bits_pos; cbn.
rewrite (map_unsigned_app_take nchars pb ds0 _ ltac:(lia) Hdrop), zlength_map_unsigned, <- Ecur2, Lc2.
repeat split; try lia.
- eassumption.
Qed.

Lemma read_from_fits_walk : forall (D len usp lo : Z) (b : bits_st ptr)
(ra t0 t1 t2 s0 s1 s2 s3 s5 s6 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
bits_rep bsegs m A D b -> bits_ok b -> u8ro bsegs m P pb -> 0 <= len <= Z.of_nat (length pb) -> len <= sb_buf_size b ->
0 < P -> (P + Z.of_nat (length pb) <= D \/ D + sb_buf_size b <= P) -> (P + Z.of_nat (length pb) <= A \/ A + 48 <= P) ->
aobj bsegs m A 48 -> aobj bsegs m P (Z.of_nat (length pb)) -> aobj bsegs m D (sb_buf_size b) ->
(A + 48 <= SH_LO \/ SH_HI <= A) -> (D + sb_buf_size b <= SH_LO \/ SH_HI <= D) ->
stk bsegs m lo usp -> lo <= usp - 80 -> SH_HI <= lo -> usp < 2^63 ->
A + 48 <= lo -> D + sb_buf_size b <= lo -> P + Z.of_nat (length pb) <= lo ->
client_constsB m -> mem_inv bsegs m ->
evt bsegs (fun ms' => exists (a0' a1' a2' a3' a4' a5' a6' a7' : word) (m2 : mem),
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m2 (seg_rom bsegs)
/\ munch [(D, D + sb_buf_size b); (A, A + 48); (usp + -80, usp)] m m2 /\ wmono bsegs m m2 /\ mem_inv bsegs m2 /\ stk bsegs m2 lo usp
/\ bits_rep bsegs m2 A D (mkBits (sb_chars b) (ztake len (map bv_unsigned pb) ++ zdrop len (sb_data b)) (len * 8) 0 0 (sb_owner b) 0 (sb_buf_size b))
/\ bits_ok (mkBits (sb_chars b) (ztake len (map bv_unsigned pb) ++ zdrop len (sb_data b)) (len * 8) 0 0 (sb_owner b) 0 (sb_buf_size b))
/\ u8ro bsegs m2 P pb)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 P) (Z_to_bv 64 len) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_bits_read_from) fc None m (seg_rom bsegs)).

Proof.
intros until m. intros REP OK SRC Hlen FITS Ppos SEP1 SEP3 OBA OBP OBD ASH DSH ST LO LOS SPH ALO DLO PLO CC MI.
destruct CC as (G1 & G2 & _).
unfold A_speex_bits_read_from, gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address in *.
pose proof REP as ((rj & Lrj & OBJ) & (bs & ARR & Hbs) & SIDE).
pose proof (bits_ints A D b OK SIDE) as (In & Ic & Ib & Io & Iv & Is & Rc & Rb & Rp & Rn & Rs & R1 & Rov).
pose proof SIDE as (AL & Apos & Dpos & _ & OWN & SEP).
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. lia. }
unfold int31, BITS_BUF_MAX, BITS_SIZEOF in *.
pose proof LOS as LOS'. pose proof ASH as ASH'. pose proof DSH as DSH'. unfold SH_LO, SH_HI in LOS', ASH', DSH'.
pose proof (u8arr_bound _ _ _ _ ARR) as DB. pose proof (bytes_at_bound _ _ _ _ SRC) as PB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -80, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -80, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 80%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 80 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
pose proof OBJ as OBJ0. unfold bits_cells in OBJ.
ato 0x979b0. astep. sh_if.
ato 0x979bc. astep. sh_if.
ato 0x979ec. rewrite sx32_small by (unfold int31; lia).
astep. sh_if.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => set (m1 := mc) in * end.
assert (OBA1 : aobj bsegs m1 A 48) by exact (aobj_munch bsegs _ m m1 A 48 OBA MU (shfree_of_aobj bsegs _ m A 48 OF OBA)).
assert (OBP1 : aobj bsegs m1 P (Z.of_nat (length pb))) by exact (aobj_munch bsegs _ m m1 P _ OBP MU (shfree_of_aobj bsegs _ m P _ OF OBP)).
assert (OBD1 : aobj bsegs m1 D (Z.of_nat (length bs))) by (rewrite Lbs; exact (aobj_munch bsegs _ m m1 D _ OBD MU (shfree_of_aobj bsegs _ m D _ OF OBD))).
eapply evt_mono.
- eapply (readfrom_tail len D usp lo bs b rj) with (m1 := m1); try eassumption; try lia.
+ unfold zdrop. rewrite Hbs. apply skipn_map.
- cbv beta. intros ms' (a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m2 & -> & MU2 & WM2 & MI2 & ST2 & REP2 & OK2 & SRC2).
do 9 eexists. split; [reflexivity|].
split. { rewrite <- Lbs. apply (munch_trans _ m m1 m2); [| exact MU2].
apply (munch_weaken [(usp + -80, usp)]); [intros x Hx; cbn [outside] in *; tauto| exact MU]. }
split; [exact (wmono_trans _ _ _ _ WM WM2)|]. split; [exact MI2|]. split; [exact ST2|].
split; [exact REP2|]. split; [exact OK2| exact SRC2].
Qed.
End Body.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition A_speex_bits_read_from : Z := 0x976b4.
Definition A_readfrom_join : Z := 0x97710.
Definition A_readfrom_loop : Z := 0x97720.
Definition A_readfrom_tail : Z := 0x97784.

Lemma firstn_S_nth {T} : forall (l : list T) i d, (i < length l)%nat -> firstn (S i) l = firstn i l ++ [nth i l d].
Proof.
induction l as [|x l IH]; intros [|i] d H; cbn in *; try lia; [reflexivity|].
f_equal. apply IH. lia.
Qed.
Lemma upd_prefix_step : forall (pb ds : list byte) (i : nat),
(i < length pb)%nat -> (i < length ds)%nat ->
upd (firstn i pb ++ skipn i ds) i (nth i pb (Z_to_bv 8 0)) = firstn (S i) pb ++ skipn (S i) ds.
Proof.
intros pb ds i Hp Hd.
destruct (upd_app_split (firstn i pb ++ skipn i ds) i (nth i pb (Z_to_bv 8 0))
ltac:(rewrite length_app, length_firstn, length_skipn; lia)) as (pre & y & post & E & Hlen & Hupd).
rewrite Hupd.
assert (Epre : pre = firstn i pb).
{ apply (f_equal (firstn i)) in E. rewrite firstn_app, firstn_firstn, Nat.min_id, length_firstn in E.
replace (i - Nat.min i (length pb))%nat with 0%nat in E by lia. cbn in E. rewrite app_nil_r in E.
rewrite E, firstn_app, Hlen, Nat.sub_diag, firstn_all2 by lia. cbn. rewrite app_nil_r. reflexivity. }
assert (Epost : post = skipn (S i) ds).
{ apply (f_equal (skipn (S i))) in E. rewrite skipn_app, length_firstn in E.
replace (S i - Nat.min i (length pb))%nat with 1%nat in E by lia.
rewrite skipn_all2 in E by (rewrite length_firstn; lia). cbn [app] in E. rewrite skipn_skipn in E.
replace (1 + i)%nat with (S i) in E by lia. rewrite E.
rewrite skipn_app, Hlen. replace (S i - i)%nat with 1%nat by lia. rewrite skipn_all2 by lia. reflexivity. }
rewrite Epre, Epost. rewrite (firstn_S_nth pb i (Z_to_bv 8 0)) by lia. rewrite <- app_assoc. reflexivity.
Qed.

Lemma map_unsigned_app_take : forall (n : Z) (pb ds0 : list byte) (d : list Z),
0 <= n -> d = map bv_unsigned (skipn (Z.to_nat n) ds0) ->
ztake n (map bv_unsigned pb) ++ d = map bv_unsigned (firstn (Z.to_nat n) pb ++ skipn (Z.to_nat n) ds0).
Proof. intros n pb ds0 d Hn ->. unfold ztake. rewrite map_app, firstn_map. reflexivity. Qed.

Section Body.
Context {ptr : Type}.
Variables (A P : Z) (pb : list byte).
Variables (gp tp s4 s7 s8 s9 s10 s11 : word).

Lemma readfrom_loop : forall (k : nat) (i nchars D' : Z) (ds0 cur : list byte) (b1 : bits_st ptr) (rj : list byte)
(rav spv s3v s6v a0v a1v a4v a5v a6 a7 t0 t1 t2 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc1 : bv 32)
(W : list (Z * Z)) (m0 m1 : mem),
Z.of_nat k = nchars - i -> 0 <= i < nchars ->
nchars <= Z.of_nat (length ds0) -> nchars <= Z.of_nat (length pb) -> Z.of_nat (length ds0) < 2^24 -> nchars < 2^31 ->
length rj = 16%nat -> rw_cells asegs m1 A (bits_cells D' b1 rj) ->
cur = firstn (Z.to_nat i) pb ++ skipn (Z.to_nat i) ds0 -> length cur = length ds0 -> u8arr asegs m1 D' cur ->
u8ro asegs m1 P pb ->
(P + Z.of_nat (length pb) <= D' \/ D' + Z.of_nat (length ds0) <= P) ->
(A + 48 <= D' \/ D' + Z.of_nat (length ds0) <= A) ->
0 < D' -> 0 < A -> 0 < P -> A mod 8 = 0 ->
aobj asegs m0 A 48 -> aobj asegs m0 P (Z.of_nat (length pb)) -> aobj asegs m0 D' (Z.of_nat (length ds0)) ->
offsh ((D', D' + Z.of_nat (length ds0)) :: W) ->
munch ((D', D' + Z.of_nat (length ds0)) :: W) m0 m1 -> wmono asegs m0 m1 -> mem_inv asegs m1 ->
evt asegs (fun ms' => exists (a0' a1' a4' a5' : word) (m2 : mem),
ms' = MS (mkR rav spv gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 P) a0' a1' (Z_to_bv 64 nchars) (Z_to_bv 64 (Z.shiftr A 3 + SHB)) a4' a5' a6 a7
(Z_to_bv 64 nchars) s3v s4 (Z_to_bv 64 SHB) s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (Z_to_bv 64 A_readfrom_tail) fc1 None m2 (seg_rom asegs)
/\ rw_cells asegs m2 A (bits_cells D' b1 rj)
/\ u8arr asegs m2 D' (firstn (Z.to_nat nchars) pb ++ skipn (Z.to_nat nchars) ds0)
/\ u8ro asegs m2 P pb
/\ munch ((D', D' + Z.of_nat (length ds0)) :: W) m0 m2 /\ wmono asegs m0 m2 /\ mem_inv asegs m2)
(MS (mkR rav spv gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 P) a0v a1v (Z_to_bv 64 i) (Z_to_bv 64 (Z.shiftr A 3 + SHB)) a4v a5v a6 a7
(Z_to_bv 64 nchars) s3v s4 (Z_to_bv 64 SHB) s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (Z_to_bv 64 A_readfrom_loop) fc1 None m1 (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros i nchars D' ds0 cur b1 rj rav spv s3v s6v a0v a1v a4v a5v a6 a7 t0 t1 t2 t3 t4 t5 t6 Ft fc1 W m0 m1
Hk Hi Hnd Hnp Hds Hn31 Lrj OBJ Ecur Lcur CUR SRC SEP1 SEP2 Dpos Apos Ppos A8 OBA OBP OBD OF MU WM MI; [lia|].
unfold bits_cells in OBJ. unfold A_readfrom_loop, A_readfrom_tail.
pose proof (rw_cells_bound _ _ _ _ OBJ) as GB. cbn [cells_size csize Nat.add length] in GB.
pose proof (u8arr_bound _ _ _ _ CUR) as DB. rewrite Lcur in DB.
pose proof (bytes_at_bound _ _ _ _ SRC) as PB.
pose proof OBP as (OP0 & OP1 & _). pose proof OBD as (OD0 & OD1 & _). unfold APP_TOP in *.
assert (Hnth : nth_error pb (Z.to_nat i) = Some (nth (Z.to_nat i) pb (Z_to_bv 8 0))) by (apply nth_error_nth'; lia).
pose proof (u8ro_read _ _ _ _ i _ _ SRC Hnth ltac:(lia) eq_refl) as RD.
ato 0x97730. astep. chk_merge OBP 1.
ato 0x97754. astep. chk_merge OBD 1.
astep.
pose proof (u8arr_store_ok asegs _ _ _ i _ CUR ltac:(lia) eq_refl) as SOK.
astep. replace (le1 (Z_to_bv 64 (bv_unsigned (nth (Z.to_nat i) pb (Z_to_bv 8 0))))) with [nth (Z.to_nat i) pb (Z_to_bv 8 0)] by (symmetry; apply le1_zxb).
pose proof (u8arr_write asegs _ _ _ i (nth (Z.to_nat i) pb (Z_to_bv 8 0)) CUR ltac:(lia)) as CUR'.
clear CUR. store_done. try clear SOK.
assert (Ecur' : upd cur (Z.to_nat i) (nth (Z.to_nat i) pb (Z_to_bv 8 0)) = firstn (Z.to_nat (i + 1)) pb ++ skipn (Z.to_nat (i + 1)) ds0).
{ rewrite Ecur. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. apply upd_prefix_step; lia. }
astep. if_cases K; zify_cond K.
-
eapply (IH (i + 1) nchars D' ds0); try eassumption; try lia.
rewrite upd_length. exact Lcur.
-
astep.
replace nchars with (i + 1) by lia. rewrite <- Ecur'.
apply evt_done. do 5 eexists. split; [reflexivity|].
refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); eassumption.
Qed.

Lemma readfrom_tail : forall (nchars D' usp lo : Z) (ds0 : list byte) (b1 : bits_st ptr) (rj j0 : list byte)
(rav s6v a0v a1v a2v a3v a4v a5v a6 a7 t0 t1 t2 t3 t4 t5 t6 c0 c1 c2 c3 c4 c5 c6 c7 cra : word) (Ft : bvmap 5 word) (fc1 : bv 32) (m1 : mem),
length rj = 16%nat -> rw_cells asegs m1 A (bits_cells D' b1 rj) ->
u8arr asegs m1 D' ds0 -> Z.of_nat (length ds0) = sb_buf_size b1 ->
u8ro asegs m1 P pb ->
0 <= nchars <= sb_buf_size b1 -> nchars <= Z.of_nat (length pb) -> 1 <= sb_buf_size b1 < 2^24 ->
zdrop nchars (sb_data b1) = map bv_unsigned (skipn (Z.to_nat nchars) ds0) ->
0 <= sb_owner b1 <= 1 -> 0 < D' -> 0 < P -> 0 < A -> A mod 8 = 0 ->
(P + Z.of_nat (length pb) <= D' \/ D' + Z.of_nat (length ds0) <= P) ->
(P + Z.of_nat (length pb) <= A \/ A + 48 <= P) ->
(A + 48 <= D' \/ D' + Z.of_nat (length ds0) <= A) ->
rw_cells asegs m1 (usp + -80) [CB 8 j0; C8 c7; C8 c6; C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra] ->
stk asegs m1 lo (usp + -80) -> lo <= usp + -80 -> SH_HI <= lo -> usp < 2^63 ->
A + 48 <= lo -> D' + Z.of_nat (length ds0) <= lo -> P + Z.of_nat (length pb) <= lo ->
(A + 48 <= SH_LO \/ SH_HI <= A) -> (D' + Z.of_nat (length ds0) <= SH_LO \/ SH_HI <= D') ->
aobj asegs m1 A 48 -> aobj asegs m1 P (Z.of_nat (length pb)) -> aobj asegs m1 D' (Z.of_nat (length ds0)) ->
mem_inv asegs m1 ->
evt asegs (fun ms' => exists (a0' a1' a2' a3' a4' a5' a6' a7' : word) (m2 : mem),
ms' = MS (mkR cra (Z_to_bv 64 usp) gp tp t0 t1 t2 c0 c1 a0' a1' a2' a3' a4' a5' a6' a7' c2 c3 c4 c5 c6 c7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc cra) fc1 None m2 (seg_rom asegs)
/\ munch [(D', D' + Z.of_nat (length ds0)); (A, A + 48); (usp + -80, usp)] m1 m2 /\ wmono asegs m1 m2 /\ mem_inv asegs m2 /\ stk asegs m2 lo usp
/\ bits_rep asegs m2 A D' (mkBits (sb_chars b1) (ztake nchars (map bv_unsigned pb) ++ zdrop nchars (sb_data b1)) (nchars * 8) 0 0 (sb_owner b1) 0 (sb_buf_size b1))
/\ bits_ok (mkBits (sb_chars b1) (ztake nchars (map bv_unsigned pb) ++ zdrop nchars (sb_data b1)) (nchars * 8) 0 0 (sb_owner b1) 0 (sb_buf_size b1))
/\ u8ro asegs m2 P pb)
(MS (mkR rav (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 P) a0v a1v a2v a3v a4v a5v a6 a7
(Z_to_bv 64 nchars) (Z_to_bv 64 (A + 28)) s4 (Z_to_bv 64 SHB) s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (Z_to_bv 64 A_readfrom_join) fc1 None m1 (seg_rom asegs)).
Proof.
intros until m1. intros Lrj OBJ DST Lds SRC Hn Hnp Hbuf Hdrop OWN Dpos Ppos Apos AL SEP1 SEP3 SEP2 FR ST LO LOS SPH ALO DLO PLO ASH DSH OBA OBP OBD MI.
pose proof LOS as LOS'. pose proof ASH as ASH'. pose proof DSH as DSH'. unfold SH_LO, SH_HI in LOS', ASH', DSH'.
pose proof (rw_cells_bound _ _ _ _ OBJ) as GB. rewrite bits_cells_size in GB by exact Lrj.
pose proof (u8arr_bound _ _ _ _ DST) as DB. pose proof (bytes_at_bound _ _ _ _ SRC) as PB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(D', D' + Z.of_nat (length ds0))] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
assert (OF : offsh [(D', D' + Z.of_nat (length ds0))]) by (cbn; unfold SH_LO, SH_HI; lia).
unfold A_readfrom_join.

eapply evt_cut with (P := fun ms' => exists (a0' a1' a2' a3' a4' a5' a6' a7' : word) (m2 : mem),
ms' = MS (mkR rav (Z_to_bv 64 (usp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 P) a0' a1' a2' a3' a4' a5' a6' a7'
(Z_to_bv 64 nchars) (Z_to_bv 64 (A + 28)) s4 (Z_to_bv 64 SHB) s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (Z_to_bv 64 A_readfrom_tail) fc1 None m2 (seg_rom asegs)
/\ rw_cells asegs m2 A (bits_cells D' b1 rj)
/\ u8arr asegs m2 D' (firstn (Z.to_nat nchars) pb ++ skipn (Z.to_nat nchars) ds0)
/\ munch [(D', D' + Z.of_nat (length ds0))] m1 m2 /\ wmono asegs m1 m2 /\ mem_inv asegs m2).
{ astep. if_cases K; zify_cond K.
-
assert (N0 : nchars = 0) by (apply andb_false_iff in K; destruct K as [K|K]; [apply Z.ltb_ge in K| apply Z.ltb_ge in K]; lia).
replace (Z.to_nat nchars) with 0%nat by lia. cbn [firstn skipn app]. unfold A_readfrom_tail.
apply evt_done. do 9 eexists. split; [reflexivity|].
refine (conj _ (conj _ (conj _ (conj _ _)))); eassumption.
- ato 0x97720.
eapply evt_mono.
+ eapply (readfrom_loop (Z.to_nat nchars) 0 nchars D' ds0 ds0 b1 rj); try eassumption; try lia; try reflexivity.
+ cbv beta. intros ms' (a0' & a1' & a4' & a5' & m2 & -> & OBJ2 & DST2 & _ & MU2 & WM2 & MI2).
do 9 eexists. split; [reflexivity|].
refine (conj _ (conj _ (conj _ (conj _ _)))); eassumption. }
cbv beta. intros ms' (a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m2 & -> & OBJ2 & DST2 & MU2 & WM2 & MI2).
pose proof (aobj_munch asegs _ m1 m2 A 48 OBA MU2 (shfree_of_aobj asegs _ m1 A 48 OF OBA)) as OBA2.
clear MU WM OF. unfold A_readfrom_tail. unfold bits_cells in OBJ2.
pose proof (rw_cells_transport asegs _ m1 m2 _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FR2.
pose proof (stk_transport_disjoint asegs _ m1 m2 _ _ ST MU2 WM2 ltac:(cbn [disjoint_from]; lia)) as ST2.
pose proof (bytes_at_transport asegs _ m1 m2 _ _ SRC MU2 ltac:(cbn [disjoint_from]; lia)) as SRC2.
clear FR ST DST SRC OBJ MI.
assert (MU : munch [(D', D' + Z.of_nat (length ds0)); (A, A + 48); (usp + -80, usp)] m1 m2)
by (apply (munch_weaken [(D', D' + Z.of_nat (length ds0))]); [intros x Hx; cbn [outside] in *; tauto| exact MU2]).
assert (OF : offsh [(D', D' + Z.of_nat (length ds0)); (A, A + 48); (usp + -80, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
clear MU2. rename WM2 into WM.
remember (firstn (Z.to_nat nchars) pb ++ skipn (Z.to_nat nchars) ds0) as cur2 eqn:Ecur2.
assert (Lc2 : length cur2 = length ds0) by (rewrite Ecur2, length_app, length_firstn, length_skipn; lia).
ato 0x9779c. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
ato 0x9780c. release_frame FR2 ST2 usp. astep. astep.
apply evt_done. do 9 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST2|].
split; [| split].
- split; [|split].
+ exists rj. split; [exact Lrj|]. unfold bits_cells; cbn [sb_nbBits sb_charPtr sb_bitPtr sb_owner sb_overflow sb_buf_size sb_chars]. eassumption.
+ exists cur2. split; [eassumption|]. cbn [sb_data]. rewrite Ecur2. apply map_unsigned_app_take; [lia| exact Hdrop].
+ unfold bits_side; cbn. unfold BITS_BUF_MAX, BITS_SIZEOF. repeat split; try lia.
- unfold bits_ok, bits_pos; cbn.
rewrite (map_unsigned_app_take nchars pb ds0 _ ltac:(lia) Hdrop), zlength_map_unsigned, <- Ecur2, Lc2.
repeat split; try lia.
- eassumption.
Qed.

Lemma read_from_fits_walk : forall (D len usp lo : Z) (b : bits_st ptr)
(ra t0 t1 t2 s0 s1 s2 s3 s5 s6 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
bits_rep asegs m A D b -> bits_ok b -> u8ro asegs m P pb -> 0 <= len <= Z.of_nat (length pb) -> len <= sb_buf_size b ->
0 < P -> (P + Z.of_nat (length pb) <= D \/ D + sb_buf_size b <= P) -> (P + Z.of_nat (length pb) <= A \/ A + 48 <= P) ->
aobj asegs m A 48 -> aobj asegs m P (Z.of_nat (length pb)) -> aobj asegs m D (sb_buf_size b) ->
(A + 48 <= SH_LO \/ SH_HI <= A) -> (D + sb_buf_size b <= SH_LO \/ SH_HI <= D) ->
stk asegs m lo usp -> lo <= usp - 80 -> SH_HI <= lo -> usp < 2^63 ->
A + 48 <= lo -> D + sb_buf_size b <= lo -> P + Z.of_nat (length pb) <= lo ->
client_consts m -> mem_inv asegs m ->
evt asegs (fun ms' => exists (a0' a1' a2' a3' a4' a5' a6' a7' : word) (m2 : mem),
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m2 (seg_rom asegs)
/\ munch [(D, D + sb_buf_size b); (A, A + 48); (usp + -80, usp)] m m2 /\ wmono asegs m m2 /\ mem_inv asegs m2 /\ stk asegs m2 lo usp
/\ bits_rep asegs m2 A D (mkBits (sb_chars b) (ztake len (map bv_unsigned pb) ++ zdrop len (sb_data b)) (len * 8) 0 0 (sb_owner b) 0 (sb_buf_size b))
/\ bits_ok (mkBits (sb_chars b) (ztake len (map bv_unsigned pb) ++ zdrop len (sb_data b)) (len * 8) 0 0 (sb_owner b) 0 (sb_buf_size b))
/\ u8ro asegs m2 P pb)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 P) (Z_to_bv 64 len) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_bits_read_from) fc None m (seg_rom asegs)).
Proof.
intros until m. intros REP OK SRC Hlen FITS Ppos SEP1 SEP3 OBA OBP OBD ASH DSH ST LO LOS SPH ALO DLO PLO CC MI.
destruct CC as (G1 & G2 & _).
unfold A_speex_bits_read_from, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof REP as ((rj & Lrj & OBJ) & (bs & ARR & Hbs) & SIDE).
pose proof (bits_ints A D b OK SIDE) as (In & Ic & Ib & Io & Iv & Is & Rc & Rb & Rp & Rn & Rs & R1 & Rov).
pose proof SIDE as (AL & Apos & Dpos & _ & OWN & SEP).
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b).
{ pose proof OK as OK'. unfold bits_ok in OK'. rewrite Hbs, zlength_map_unsigned in OK'. lia. }
unfold int31, BITS_BUF_MAX, BITS_SIZEOF in *.
pose proof LOS as LOS'. pose proof ASH as ASH'. pose proof DSH as DSH'. unfold SH_LO, SH_HI in LOS', ASH', DSH'.
pose proof (u8arr_bound _ _ _ _ ARR) as DB. pose proof (bytes_at_bound _ _ _ _ SRC) as PB.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -80, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -80, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 80%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 80 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
pose proof OBJ as OBJ0. unfold bits_cells in OBJ.
ato 0x9770c. rewrite sx32_small by (unfold int31; lia).
astep. sh_if.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => set (m1 := mc) in * end.
assert (OBA1 : aobj asegs m1 A 48) by exact (aobj_munch asegs _ m m1 A 48 OBA MU (shfree_of_aobj asegs _ m A 48 OF OBA)).
assert (OBP1 : aobj asegs m1 P (Z.of_nat (length pb))) by exact (aobj_munch asegs _ m m1 P _ OBP MU (shfree_of_aobj asegs _ m P _ OF OBP)).
assert (OBD1 : aobj asegs m1 D (Z.of_nat (length bs))) by (rewrite Lbs; exact (aobj_munch asegs _ m m1 D _ OBD MU (shfree_of_aobj asegs _ m D _ OF OBD))).
eapply evt_mono.
- eapply (readfrom_tail len D usp lo bs b rj) with (m1 := m1); try eassumption; try lia.
+ unfold zdrop. rewrite Hbs. apply skipn_map.
- cbv beta. intros ms' (a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m2 & -> & MU2 & WM2 & MI2 & ST2 & REP2 & OK2 & SRC2).
do 9 eexists. split; [reflexivity|].
split. { rewrite <- Lbs. apply (munch_trans _ m m1 m2); [| exact MU2].
apply (munch_weaken [(usp + -80, usp)]); [intros x Hx; cbn [outside] in *; tauto| exact MU]. }
split; [exact (wmono_trans _ _ _ _ WM WM2)|]. split; [exact MI2|]. split; [exact ST2|].
split; [exact REP2|]. split; [exact OK2| exact SRC2].
Qed.
End Body.
