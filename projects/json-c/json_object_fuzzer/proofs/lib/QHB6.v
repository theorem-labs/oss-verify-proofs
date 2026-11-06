(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 Q5Rg Qfw3_c1 QWxq_c1 Qc3B Lib.GwApply QsjA QZAi QdBa QfYR QfcC Ql2m Lib.SepCache QnDM_c1 QDUx Q9Ay Qy5Y QPUx Q7wb Qbf8 QSzV QcAG QX7A QhY6 QIsN QYaS QrvG QQbX QwyL QhHa QN1y Q48O QGmo QTS6 QvBB QnkH Qi8L QmBS QKwd Qlfl QjhR QCqH QTp6.
From Ltac2 Require Ltac2 Constr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qfw3_c1.Mq2 QWxq_c1.Mq0 Qc3B.

Import QZAi.Mq1 QZAi QdBa QfYR QfcC Ql2m Ql2m.Mq0.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y QPUx.
Import Q7wb.
Import Qbf8 QSzV QcAG QX7A QhY6 QIsN QYaS QrvG QQbX.Mq0 QwyL QhHa QN1y Q48O QGmo QTS6 QvBB.Mq1 QnkH.Mq1 Qi8L.Mq1 QmBS.Mq0 QKwd Qlfl.Mq0 QnkH.Mq0 Qi8L.Mq0 QjhR.Mq0.
Import QCqH.
Import QTp6.
Import ListNotations. Unset Keyed Unification.
Open Scope bv_scope.

Import Ltac2.Ltac2 Ltac2.Constr.
Set Default Proof Mode "Classic".
Ltac2 rec zt_plain_arith' (t : constr) : bool :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.App h args =>
match Constr.Unsafe.kind h with
| Constr.Unsafe.Constant _ _ =>
if Constr.equal h '@Z.le then true else if Constr.equal h '@Z.lt then true
else if Constr.equal h '@Z.ge then true else if Constr.equal h '@Z.gt then true
else if Constr.equal h '@lt then true else if Constr.equal h '@ge then true
else if Constr.equal h '@gt then true else if Constr.equal h '@N.le then true
else if Constr.equal h '@N.lt then true else if Constr.equal h '@Z.divide then true
else false
| Constr.Unsafe.Ind _ _ =>
if Constr.equal h '@and then (if zt_plain_arith' (Array.get args 0) then zt_plain_arith' (Array.get args 1) else false)
else if Constr.equal h '@eq then true else if Constr.equal h '@le then true
else false
| _ => false
end
| Constr.Unsafe.Ind _ _ => if Constr.equal t 'True then true else Constr.equal t 'False
| _ => false
end.
Ltac2 rec zt_codomain (t : constr) : constr :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.Prod _ b => zt_codomain b
| Constr.Unsafe.LetIn _ _ b => zt_codomain b
| Constr.Unsafe.Cast c _ _ => zt_codomain c
| _ => t
end.
Ltac2 rec zt_head (t : constr) : constr :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.App f _ => zt_head f
| Constr.Unsafe.Cast c _ _ => zt_head c
| _ => t
end.
Ltac2 zt_sort_is_prop (ty : constr) : bool :=
lazy_match! zt_codomain ty with Prop => true | _ => false end.
Ltac2 zt_is_prop_fast (ty : constr) : bool :=
let h := zt_head (zt_codomain ty) in
match Constr.Unsafe.kind h with
| Constr.Unsafe.Constant _ _ => zt_sort_is_prop (Constr.type h)
| Constr.Unsafe.Ind _ _ => zt_sort_is_prop (Constr.type h)
| Constr.Unsafe.Var _ => zt_sort_is_prop (Constr.type h)
| _ => false
end.
Ltac2 zt_is_local' (id : ident) : bool :=
match Env.get [id] with None => true | Some _ => false end.
Ltac2 zt_prune_fast () : unit :=
let hs := Control.hyps () in
let ids := List.map_filter (fun h => let (id, body, ty) := h in
match body with
| Some _ => None
| None => if zt_plain_arith' ty then None
else if Bool.and (zt_is_local' id) (zt_is_prop_fast ty) then Some id else None
end) hs in
match ids with [] => () | _ :: _ => Std.clear ids end.
Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Ltac showt := let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in
idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31.
Ltac showall := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in let x2 := getreg 2%Z in let x1 := getreg 1%Z in
idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31; idtac "sp=" x2; idtac "ra=" x1.
Ltac show_hyp H := let T := type of H in idtac H ":" T.
Ltac dlia := first [lia | match goal with |- ?g => idtac "LIA FAILED:"; idtac g; fail 1 end].
Ltac plia := unfold zlength, got_ssp, ssp_guard in *; lia.

Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.

Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

Lemma land_mask_range : forall a m, (0 <= m)%Z -> (0 <= Z.land a m <= m)%Z.
Proof.
intros a m Hm. split; [apply Z.land_nonneg; right; exact Hm|].
pose proof (Z.sub_land_same_l m a) as E. rewrite (Z.land_comm a m).
assert (0 <= Z.land m (Z.lnot a))%Z by (apply Z.land_nonneg; left; exact Hm). lia.
Qed.

Ltac fix_idx := repeat match goal with
| |- context [Z_to_bv 64 (?A + Z.shiftl ?k 2)] =>
replace (Z_to_bv 64 (A + Z.shiftl k 2)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia)
| |- context [Z_to_bv 64 (Z.shiftl ?k 2 + ?A)] =>
replace (Z_to_bv 64 (Z.shiftl k 2 + A)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia) end.

Lemma sx32_wval : forall ws i t, wval ws i = t -> (0 <= t < 2^31)%Z -> sx32 (wnth ws i) = Z_to_bv 64 t.
Proof.
intros ws i t Hw Ht. unfold sx32. f_equal. unfold wval in Hw. rewrite swrap32_eq.
pose proof (bv_unsigned_in_range 64 (wnth ws i)) as R.
rewrite <- Hw. rewrite <- Hw in Ht. Z.div_mod_to_equations. lia.
Qed.

Lemma zx32_wval : forall ws i, zx32 (wnth ws i) = Z_to_bv 64 (wval ws i).
Proof. intros. unfold zx32, wval. reflexivity. Qed.

Lemma srlw_small : forall t sh, (0 <= t < 2^31)%Z -> (0 <= sh < 32)%Z ->
bv_swrap 32 (Z.shiftr (bv_wrap 32 t) (sh mod 32)) = Z.shiftr t sh.
Proof.
intros t sh Ht Hsh. rewrite (Z.mod_small sh 32) by lia.
replace (bv_wrap 32 t) with t by (unfold bv_wrap, bv_modulus; symmetry; apply Z.mod_small; cbn; lia).
assert (0 <= Z.shiftr t sh <= t)%Z.
{ split; [apply Z.shiftr_nonneg; lia|]. rewrite Z.shiftr_div_pow2 by lia.
apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|]. assert (1 <= 2 ^ sh)%Z by (change 1%Z with (2^0)%Z; apply Z.pow_le_mono_r; lia). nia. }
apply swrap32_small. lia.
Qed.

Ltac eval_swraps := repeat match goal with |- context [bv_swrap 32 ?e] =>
let v := eval vm_compute in (bv_swrap 32 e) in lazymatch isZcst v with true => change (bv_swrap 32 e) with v end end.

Lemma divu_lit : forall a b, (0 <= a < 2^64)%Z -> (0 < b < 2^64)%Z ->
mul_div M_DIVU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a / b).
Proof.
intros a b Ha Hb. unfold mul_div. rewrite (unsigned_lit b) by lia.
replace (b =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
assert (R : (0 <= a / b <= a)%Z). { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
apply bv_eq. rewrite bv_divu_unsigned. rewrite !unsigned_lit by lia. reflexivity.
Qed.
Lemma remu_lit : forall a b, (0 <= a < 2^64)%Z -> (0 < b < 2^64)%Z ->
mul_div M_REMU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a mod b).
Proof.
intros a b Ha Hb. unfold mul_div. rewrite (unsigned_lit b) by lia.
replace (b =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
pose proof (Z.mod_pos_bound a b ltac:(lia)) as R.
apply bv_eq. rewrite bv_modu_unsigned. rewrite !unsigned_lit by lia. reflexivity.
Qed.

Section DivW.
Local Open Scope Z_scope.
#[using="Type"] Lemma divw_small : forall v i, (0 <= v < 2^31)%Z -> (0 < i < 2^31)%Z -> v_divw (Z_to_bv 64 v) (Z_to_bv 64 i) = Z_to_bv 64 (v / i)%Z.
Proof.
intros v i Hv Hi. unfold v_divw. rewrite !unsigned_lit by lia.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with 4294967296%Z.
rewrite (Z.mod_small i) by lia. destruct (Z.eqb_spec i 0); [lia|]. f_equal.
rewrite (swrap32_small v), (swrap32_small i) by lia. rewrite Z.quot_div_nonneg by lia.
assert (0 <= v / i <= v)%Z by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia|]; nia]).
apply swrap32_small. lia.
Qed.
#[using="Type"] Lemma p10s_range : forall j, 0 <= j <= 7 -> 10 <= znth p10s j <= 100000000 /\ (znth p10s j * (1000000000 / znth p10s j) = 1000000000)%Z.
Proof.
intros j Hj.
assert (H : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia.
destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
match goal with |- context [znth p10s ?j] => let v := eval vm_compute in (znth p10s j) in change (znth p10s j) with v end; (split; [lia | reflexivity]).
Qed.
End DivW.

Definition RATP : Z := 0x622e60.
Definition RERRNO : Z := 0x622dbc.
Definition ERRNO_LOC : Z := 0xcc3a4.

Lemma errno_loc_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
mem_inv rsegs m ->
evt rsegs (fun ms' => exists m', ms' = MS (mkR ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 RERRNO) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m')
(MS (mkR ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ERRNO_LOC) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros MI. unfold ERRNO_LOC, RATP, RERRNO.
zs. zs. zs.
apply evt_done. eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl | exact MI].
Qed.

Section CallE.
Local Open Scope Z_scope.
Definition DS : divtf3_stmt := QYaS.divtf3_spec.
#[using="Type"] Lemma mul_callE : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q al ah bl bh X Y : Z),
stk rsegs m (q - 80) q -> mem_inv rsegs m -> (4096 <= q < 2^64)%Z ->
al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
evt rsegs (call2_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 80 (f128_mul X Y) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcf768) fc None m (seg_rom rsegs)).
Proof. intros until Y. intros ST MI Hq -> -> -> ->. apply multf3_callq; assumption. Qed.
#[using="Type"] Lemma div_callE : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q al ah bl bh X Y : Z),
stk rsegs m (q - 112) q -> mem_inv rsegs m -> (4096 <= q < 2^64)%Z ->
al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
evt rsegs (call2_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 112 (f128_div X Y) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd09b4) fc None m (seg_rom rsegs)).
Proof. intros until Y. intros ST MI Hq -> -> -> ->. apply (divtf3_callq DS); assumption. Qed.
#[using="Type"] Lemma add_callE : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q al ah bl bh X Y : Z),
stk rsegs m (q - 48) q -> mem_inv rsegs m -> frm0 fc -> (48 <= q < 2^64)%Z ->
al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
evt rsegs (calla_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (f128_add X Y) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd0094) fc None m (seg_rom rsegs)).
Proof. intros until Y. intros ST MI FRM Hq -> -> -> ->. apply addtf3_callq; assumption. Qed.
#[using="Type"] Lemma sub_callE : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q al ah bl bh X Y : Z),
stk rsegs m (q - 48) q -> mem_inv rsegs m -> frm0 fc -> (48 <= q < 2^64)%Z ->
al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
evt rsegs (calla_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (f128_sub X Y) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd089c) fc None m (seg_rom rsegs)).
Proof. intros until Y. intros ST MI FRM Hq -> -> -> ->. apply subtf3_callq; assumption. Qed.
#[using="Type"] Lemma letf2_callE : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (al ah bl bh X Y : Z),
mem_inv rsegs m -> al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
evt rsegs (leaf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_le X Y) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcf5e4) fc None m (seg_rom rsegs)).
Proof. intros until Y. intros MI -> -> -> ->. apply letf2_callv; assumption. Qed.
#[using="Type"] Lemma getf2_callE : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (al ah bl bh X Y : Z),
mem_inv rsegs m -> al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
evt rsegs (leaf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_ge X Y) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcf6ac) fc None m (seg_rom rsegs)).
Proof.
intros until Y. intros MI -> -> -> ->. eapply evt_mono. { eapply getf2_spec. exact MI. }
intros ms' P. unfold getf2_post in P. unfold leaf1_post. rewrite !ulit_lo64, !ulit_hi64 in P.
change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. change (lo64 Y + 2 ^ 64 * hi64 Y)%Z with (canon Y) in P.
rewrite Q9Ay.f128_ge_canon in P. exact P.
Qed.

#[using="Type"] Lemma scalbn_callE : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (n : Z),
mem_inv rsegs m -> frm0 fc -> (-2^31 <= n < 2^31)%Z ->
evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (f15 : word) fc' m',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
(bvmap_set 10 (scalbn_model (reg_get F 10) n) (bvmap_set 15 f15 F)) (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ frm0 fc')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd12b8) fc None m (seg_rom rsegs)).
Proof.
intros until n. intros MI FRM Hn. eapply evt_mono. { eapply scalbn_spec; [exact MI | exact FRM | | exact Hn]. apply signed_of_Z; lia. }
intros ms' P. unfold scalbn_post in P. exact P.
Qed.
#[using="Type"] Lemma fabsl_callE : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (al ah X : Z),
mem_inv rsegs m -> al = lo64 X -> ah = hi64 X ->
evt rsegs (leafq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (m_fabsl X) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 FABSL) fc None m (seg_rom rsegs)).
Proof. intros until X. intros MI -> ->. apply fabsl_spec; assumption. Qed.
#[using="Type"] Lemma copysignl_callE : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (al ah bl bh X Y : Z),
mem_inv rsegs m -> al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
evt rsegs (leafq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (m_copysignl X Y) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 COPYSIGNL) fc None m (seg_rom rsegs)).
Proof. intros until Y. intros MI -> -> -> ->. apply copysignl_spec; assumption. Qed.

#[using="Type"] Lemma fmodl_callE : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q lo al ah bl bh X Y r : Z),
stk rsegs m lo q -> mem_inv rsegs m -> (lo <= q - 192) -> (4288 <= q < 2^63) ->
al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
m_fmodl X Y = Some r ->
evt rsegs (fun ms' => exists t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (lo64 r)) (Z_to_bv 64 (hi64 r)) a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(q - 192, q)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo q /\ (forall k : bv 5, bv_unsigned k <> 10%Z -> reg_get F' k = reg_get F k))
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 FMODL) fc None m (seg_rom rsegs)).
Proof.
intros until r. intros ST MI Hlo Hq -> -> -> -> HMr.
destruct (stk_split _ _ _ (q - 192) _ ST ltac:(lia)) as [ST1 ST2].
eapply evt_mono. { eapply (rfmodl_spec ra q); unfold RFMODL_DEPTH; eauto; lia. }
intros ms' P. unfold rfmodl_post, RFMODL_DEPTH in P.
destruct P as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & m' & -> & MU & WM & MI' & ST' & FOK).
repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [|exact FOK].
eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU | exact WM | cbn [disjoint_from]; lia] | exact ST' | lia ].
Qed.
End CallE.

Definition FS_DEPTH : Z := 8656.
Definition FLOATSCAN : Z := 0xd6394.

Section Floatscan.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Variables (ra : word) (q : Z) (gp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
(Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z)
(fR : shfile) (yR : Z).
Hypothesis HM : floatscan fuelc f0 1 pok = Some (fR, yR).
Hypothesis Hpok : pok = 0%Z \/ pok = 1%Z.
Hypothesis ST0 : sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre.
Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
Hypothesis Hp : (0 <= p < zlength txt)%Z.
Hypothesis Hnul : znth txt p = 0%Z.
Hypothesis Hnum : forall i, (0 <= i < p)%Z -> is_numch (znth txt i) = true.
Hypothesis HP30 : (p < 2^31)%Z.
Hypothesis T0 : (0 < T)%Z.
Hypothesis T1 : (T + 2^41 <= 2^63)%Z.
Hypothesis SEP : (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z.
Hypothesis SE_T : (T + zlength txt <= RERRNO \/ RERRNO + 4 <= T)%Z.
Hypothesis SPLO : (4096 <= q - FS_DEPTH)%Z.
Hypothesis SPF : (q <= Fp)%Z.
Hypothesis SPF2 : (Fp + 232 <= 2^63)%Z.
Hypothesis SPT : (T + zlength txt <= q - FS_DEPTH \/ q <= T)%Z.
Hypothesis SG1 : (ssp_guard + 8 <= q - FS_DEPTH)%Z.
Hypothesis SG2 : (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z.
Hypothesis SG3 : (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z.
Hypothesis Q1 : (q < 2^63)%Z.
Hypothesis FRM : frm0 fc.

Definition ctx_all : unit :=
let _ := (ra, q, gp, s0e, s1e, s2e, s3e, s4e, s5e, s6e, s7e, s8e, s9e, s10e, s11e, F, fc, m0,
Fp, T, p, J, txt, pre, post, canary, pok, fuelc, f0, kmin0, c0, fR, yR) in tt.

Definition Wfs : list (Z * Z) := [(q - FS_DEPTH, q); (Fp, Fp + 232); (RERRNO, RERRNO + 4)]%Z.
Notation TPv := (Z_to_bv 64 RATP).
Notation SPv := (Z_to_bv 64 (q + -8416)).
Notation XA := (q + -8312)%Z.
Notation RFJ' := (RFJ T txt p true J).
Definition zero0 : Z := f128_of_i32 0.

Definition FokR (F' : bvmap 5 word) : Prop :=
forall k : bv 5, bv_unsigned k <> 10%Z -> bv_unsigned k <> 14%Z -> bv_unsigned k <> 15%Z -> reg_get F' k = reg_get F k.

Definition Fok (F' : bvmap 5 word) : Prop :=
forall k : bv 5, bv_unsigned k <> 8%Z -> bv_unsigned k <> 10%Z -> bv_unsigned k <> 14%Z -> bv_unsigned k <> 15%Z -> reg_get F' k = reg_get F k.
#[using="Type"] Lemma Fok_refl : Fok F. Proof. intros k _ _ _ _. reflexivity. Qed.
#[using="Type"] Lemma Fok_set : forall F' (r : bv 5) v, Fok F' -> (bv_unsigned r = 8 \/ bv_unsigned r = 10 \/ bv_unsigned r = 14 \/ bv_unsigned r = 15)%Z -> Fok (bvmap_set r v F').
Proof.
intros F' r v H Hr k H8 H10 H14 H15. rewrite reg_get_set_other. { apply H; assumption. }
intros E. rewrite <- E in *. lia.
Qed.
#[using="Type"] Lemma Fok_trans10 : forall F1 F2, Fok F1 -> (forall k : bv 5, bv_unsigned k <> 10%Z -> reg_get F2 k = reg_get F1 k) -> Fok F2.
Proof. intros F1 F2 H1 H2 k H8 H10 H14 H15. rewrite H2 by exact H10. apply H1; assumption. Qed.

Definition fs_post (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' k' c' (ev' : word),
ms' = MS (mkR ra (Z_to_bv 64 q) gp TPv t0 t1 t2 s0e s1e (Z_to_bv 64 (lo64 yR)) (Z_to_bv 64 (hi64 yR)) a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch Wfs m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (q - FS_DEPTH) q
/\ rw_cells rsegs m' Fp (rf_cells T p true fR J)
/\ RFJ' k' c' fR /\ (0 <= k')%Z
/\ bytes_at rsegs m' T (zbytes txt)
/\ ssp_cells m' canary
/\ rw_cells rsegs m' RERRNO [C4 ev']
/\ FokR F' /\ frm0 fc'.

Definition hi_cells : list cell :=
[C8 canary; C8 (reg_get F 8); C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra].

Definition finv (m : word -> option byte) : Prop :=
mem_inv rsegs m /\ munch Wfs m0 m /\ wmono rsegs m0 m
/\ rw_cells rsegs m (q + -120) hi_cells
/\ stk rsegs m (q - FS_DEPTH) (q + -8416)
/\ bytes_at rsegs m T (zbytes txt)
/\ rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells rsegs m ssp_guard [C8 canary].
#[using="Type"] Lemma zbytes_len : length (zbytes txt) = length txt.
Proof. unfold zbytes. apply length_map. Qed.
Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let TXT := fresh "BY" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
destruct H as (MI & MU & WM & FRhi & ST & TXT & SSP1 & SSP2); unfold Wfs, FS_DEPTH, RERRNO in MU; unfold hi_cells in FRhi;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold FS_DEPTH in ST;
unfold FS_DEPTH, got_ssp, ssp_guard, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.

Definition framL (j0 : list byte) (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) (ev : word) (m : word -> option byte) : Prop :=
rw_cells rsegs m (q + -8416) [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; CB 8 b96]
/\ rw_cells rsegs m RERRNO [C4 ev].
Ltac dest_framL H := let LOW := fresh "LOW" in let ERR := fresh "ERR" in destruct H as (LOW & ERR); unfold RERRNO in ERR.

#[using="Type"] Lemma rw_cells_C8_CB8 : forall m A pre (v : word) post,
rw_cells rsegs m A (pre ++ C8 v :: post) <-> rw_cells rsegs m A (pre ++ CB 8 (le8 v) :: post).
Proof.
clear. intros m A pre v post. unfold rw_cells, cells_at.
rewrite !cells_wf_app, !cells_bytes_app, !cells_size_app. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize].
rewrite length_le8. tauto.
Qed.
#[using="Type"] Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
clear. intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
pose proof (bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in HR.
rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.
#[using="Type"] Lemma cb8_c8_in : forall m A pre post bs, rw_cells rsegs m A (pre ++ CB 8 bs :: post) -> rw_cells rsegs m A (pre ++ C8 (le_bytes_to_word bs) :: post).
Proof.
clear. intros m A pre post bs [[Hwf Hb] Hw].
apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn in H2.
split; [split|].
- apply cells_wf_app. split; [exact H1|]. split; [exact I | exact H3].
- rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb |- *. rewrite le8_of_bytes by exact H2. exact Hb.
- rewrite !cells_size_app in *. cbn [cells_size csize] in Hw |- *. exact Hw.
Qed.

Definition xrel (ws : list word) (x : list Z) (P : Z -> Prop) : Prop :=
length ws = 2048%nat /\ length x = 2048%nat /\ forall i, (0 <= i < 2048)%Z -> P i -> znth x i = wval ws i.

Notation POST := (fs_post m0).

#[using="BYT"] Lemma txt_char : forall i, (0 <= i < zlength txt)%Z -> (0 <= znth txt i < 256)%Z.
Proof.
intros i Hi. pose proof (proj1 (Forall_forall _ _) BYT (znth txt i) (Qy5Y.znth_In' txt i Hi)) as R. exact R.
Qed.
#[using="Hnum"] Lemma numch_nz : forall i, (0 <= i < p)%Z -> (43 <= znth txt i <= 101)%Z.
Proof.
intros i Hi. pose proof (Hnum i Hi) as E. unfold is_numch in E.
repeat (apply Bool.orb_true_iff in E; destruct E as [E|E]);
try (apply Z.eqb_eq in E; lia). apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.

#[using="pre"] Lemma frame_release : forall m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws,
finv m -> framL j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev m -> u32arr rsegs m XA ws -> length ws = 2048%nat ->
stk rsegs m (q - FS_DEPTH) q.
Proof.
intros until ws. intros FI FL XW LW. dest_finv FI. dest_framL FL.
apply u8arr_of_u32arr in XW. apply rw_cells_of_u8arr in XW. rewrite u32s_length, LW in XW.
release_frame LOW ST (q + -8312)%Z.
release_frame XW ST (q + -120)%Z.
release_frame FRhi ST q.
unfold FS_DEPTH. exact ST.
Qed.

#[using="pre Hp SE_T SPF SPT SG1 SG3"] Lemma post_tail : forall m m' K F' fc' k c ev,
finv m -> rw_cells rsegs m Fp (rf_cells T p true fR J) -> RFJ' k c fR -> (0 <= k)%Z -> rw_cells rsegs m RERRNO [C4 ev] ->
FokR F' -> frm0 fc' -> (0 <= K <= FS_DEPTH)%Z ->
munch [(q - K, q)]%Z m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
stk rsegs m' (q - FS_DEPTH) q ->
forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
POST (MS (mkR ra (Z_to_bv 64 q) gp TPv t0 t1 t2 s0e s1e (Z_to_bv 64 (lo64 yR)) (Z_to_bv 64 (hi64 yR)) a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom rsegs)).
Proof.
intros until ev. intros FI FC RJ Hk ERR FOK FRM' HK MU2 WM2 MI2 ST2. intros. dest_finv FI. unfold FS_DEPTH in HK, SPLO, SPT, SG1. unfold RERRNO in *.
unfold got_ssp, ssp_guard in SG1, SG2, SG3.
pose proof (rw_cells_bound _ _ _ _ FC) as B1. cbn [cells_size csize Nat.add rf_cells] in B1.
unfold fs_post, Wfs, FS_DEPTH, RERRNO, ssp_cells, got_ssp, ssp_guard. repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split.
{ eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
split; [eapply wmono_trans; [exact WM | exact WM2]|]. split; [exact MI2|]. split; [exact ST2|].
split. { eapply rw_cells_transport; [exact FC | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize rf_cells length Nat.add]; lia]. }
split; [exact RJ|]. split; [exact Hk|].
split. { eapply bytes_at_transport; [exact BY | exact MU2 | cbn [disjoint_from]; rewrite ?LTX; lia]. }
split. { split.
- eapply rw_cells_transport; [exact SSP1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize length Nat.add]; lia].
- eapply rw_cells_transport; [exact SSP2 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize length Nat.add]; lia]. }
split. { eapply rw_cells_transport; [exact ERR | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize length Nat.add]; lia]. }
split; [exact FOK | exact FRM'].
Qed.

#[using="Hp SE_T SPF SPT SG1 SG3"] Lemma L_RET34 : forall m (x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws k c (r : Z),
let _ := ctx_all in
finv m -> framL j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev m -> u32arr rsegs m XA ws -> length ws = 2048%nat ->
rw_cells rsegs m Fp (rf_cells T p true fR J) -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
yR = r ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (lo64 r)) (Z_to_bv 64 (hi64 r)) canary x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6e64) fct None m (seg_rom rsegs)).
Proof.
intros until r. intros _ FI FL XW LW FC RJ Hk FOK FRM' Hy.
pose proof FI as FI0. pose proof FL as FL0. dest_finv FI. dest_framL FL. unfold FS_DEPTH in SPLO. pose proof (lo64_range r). pose proof (hi64_range r).
zs. zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ exfalso; lia | ]).
zs. zs. zs. zs. do 14 zs. zs.
pose proof (frame_release _ j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws FI0 FL0 XW LW) as STK.
subst r. apply evt_done. eapply (post_tail _ _ 0%Z); try eassumption.
- intros kk H10 H14 H15. destruct (Z.eq_dec (bv_unsigned kk) 8) as [E8|N8].
+ rewrite freg_get_same by (rewrite E8; vm_compute; reflexivity). f_equal. apply bv_eq. rewrite E8. vm_compute. reflexivity.
+ rewrite reg_get_set_other by (intros E; apply N8; rewrite <- E; reflexivity). apply FOK; assumption.
- unfold FS_DEPTH; lia.
- apply munch_refl.
- apply wmono_refl.
Qed.

#[using="Hp SE_T SPF SPT SG1 SG3"] Lemma L_RET1 : forall m (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 b96 ev ws k c (r : Z),
let _ := ctx_all in
finv m -> framL j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 (Z_to_bv 64 ssp_guard) b96 ev m -> u32arr rsegs m XA ws -> length ws = 2048%nat ->
rw_cells rsegs m Fp (rf_cells T p true fR J) -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
yR = r ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (lo64 r)) (Z_to_bv 64 (hi64 r)) x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6d04) fct None m (seg_rom rsegs)).
Proof.
intros until r. intros _ FI FL XW LW FC RJ Hk FOK FRM' Hy.
pose proof FI as FI0. dest_finv FI. pose proof FL as FL0. dest_framL FL. unfold ssp_guard in LOW.
zs. zs. zs.
eapply L_RET34; eassumption.
Qed.

#[using="Hp SE_T SPF SPT SG1 SG3"] Lemma L_RET30 : forall m (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws k c (r : Z),
let _ := ctx_all in
finv m -> framL j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev m -> u32arr rsegs m XA ws -> length ws = 2048%nat ->
rw_cells rsegs m Fp (rf_cells T p true fR J) -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
yR = r ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (lo64 r)) (Z_to_bv 64 (hi64 r)) x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6e60) fct None m (seg_rom rsegs)).
Proof.
intros until r. intros _ FI FL XW LW FC RJ Hk FOK FRM' Hy.
pose proof FI as FI0. dest_finv FI. unfold ssp_guard.
zs.
eapply L_RET34; eassumption.
Qed.

#[using="Hp SE_T SPLO SPF SPT SG1 SG3 Q1"] Lemma L_SCL : forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws k c (Y e2 : Z),
let _ := ctx_all in
finv m -> framL j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev m -> u32arr rsegs m XA ws -> length ws = 2048%nat ->
rw_cells rsegs m Fp (rf_cells T p true fR J) -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(-2^31 <= e2 < 2^31)%Z ->
yR = m_scalbnl Y e2 ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 (lo64 Y)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 ssp_guard) x19 (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 e2) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7958) fct None m (seg_rom rsegs)).
Proof.
intros until e2. intros _ FI FL XW LW FC RJ Hk FOK FRM' He2 Hy.
pose proof FI as FI0. pose proof FL as FL0. dest_finv FI. dest_framL FL. unfold FS_DEPTH in SPLO. unfold ssp_guard.
pose proof (lo64_range Y). pose proof (hi64_range Y).
zs. zs. zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ exfalso; lia | ]).
zs. zs. zs.
zs. zs. zs. zs. do 14 zs. zs.
pose proof (frame_release _ j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws FI0 FL0 XW LW) as STK. unfold FS_DEPTH in STK.
destruct (stk_split _ _ _ (q - 112)%Z _ STK ltac:(lia)) as [ST1 ST2].
pose proof scalbnl_spec as SS. unfold scalbnl_stmt in SS.
eapply evt_mono. { eapply SS; [exact ST2 | lia | lia | exact He2 | exact MI]. }
intros ms' P. unfold scalbnl_post in P.
destruct P as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU2 & WM2 & MI2 & ST3).
rewrite <- Hy. eapply (post_tail m m' 112%Z); try eassumption.
- intros kk H10 H14 H15. rewrite reg_get_set_other by (intros E; apply H10; rewrite <- E; reflexivity).
destruct (Z.eq_dec (bv_unsigned kk) 8) as [E8|N8].
+ rewrite freg_get_same by (rewrite E8; vm_compute; reflexivity). f_equal. apply bv_eq. rewrite E8. vm_compute. reflexivity.
+ rewrite reg_get_set_other by (intros E; apply N8; rewrite <- E; reflexivity). apply FOK; assumption.
- unfold FS_DEPTH; lia.
- unfold FS_DEPTH. eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU2 | exact WM2 | cbn [disjoint_from]; lia] | exact ST3 | lia ].
Qed.

#[using="Type"] Lemma b2z_land : forall a b, Z.land (Z.b2z a) (Z.b2z b) = Z.b2z (a && b). Proof. clear. destruct a, b; reflexivity. Qed.
#[using="Type"] Lemma b2z_lt1 : forall c, (Z.b2z c <? 1) = negb c. Proof. clear. destruct c; reflexivity. Qed.

Definition hide (P : Prop) := P.

#[using="Type"] Lemma swrap32_landW_r : forall a c, bv_swrap 32 (c + Z.land a 18446744073709551615) = bv_swrap 32 (c + a).
Proof. clear. intros. rewrite (Z.add_comm c (Z.land a _)), swrap32_landW. f_equal. lia. Qed.

Definition hide2 (P : Prop) := P.

Definition dfinv (m : word -> option byte) (j0 : list byte) (w16 w24 : word) (b96 : list byte) (ev : word) (ws : list word) (sign : Z) (f : shfile) : Prop :=
finv m
/\ framL j0 (Z_to_bv 64 1021) w16 w24 (Z_to_bv 64 1) (Z_to_bv 64 (-1074)) (Z_to_bv 64 1074) (Z_to_bv 64 53)
(Z_to_bv 64 pok) (Z_to_bv 64 sign) (Z_to_bv 64 18396) (Z_to_bv 64 ssp_guard) b96 ev m
/\ u32arr rsegs m XA ws /\ length ws = 2048%nat /\ rw_cells rsegs m Fp (rf_cells T p true f J).

Definition dfinvG (m : word -> option byte) (j0 : list byte) (w16 w24 w80 : word) (b96 : list byte) (ev : word) (ws : list word) (sign : Z) (f : shfile) : Prop :=
finv m
/\ framL j0 (Z_to_bv 64 1021) w16 w24 (Z_to_bv 64 1) (Z_to_bv 64 (-1074)) (Z_to_bv 64 1074) (Z_to_bv 64 53)
(Z_to_bv 64 pok) (Z_to_bv 64 sign) w80 (Z_to_bv 64 ssp_guard) b96 ev m
/\ u32arr rsegs m XA ws /\ length ws = 2048%nat /\ rw_cells rsegs m Fp (rf_cells T p true f J).
#[using="Type"] Lemma dfinvG_dfinv : forall m j0 w16 w24 b96 ev ws sign f,
dfinvG m j0 w16 w24 (Z_to_bv 64 18396) b96 ev ws sign f = dfinv m j0 w16 w24 b96 ev ws sign f.
Proof. reflexivity. Qed.

Definition inring (a z i : Z) : Prop := ((i - a) mod 2048 < (z - a) mod 2048)%Z.
#[using="Type"] Lemma land2047 : forall v, Z.land v 2047 = (v mod 2048)%Z.
Proof. clear. intros. change 2047%Z with (Z.ones 11). rewrite Z.land_ones by lia. reflexivity. Qed.
#[using="Type"] Lemma landW_mod2048 : forall v, ((Z.land v 18446744073709551615) mod 2048 = v mod 2048)%Z.
Proof. clear. intros. rewrite land_W64. apply Z.mod_mod_divide. exists (2^53)%Z. reflexivity. Qed.
#[using="Type"] Lemma inring_plus : forall a z d, (0 <= z < 2048)%Z -> (0 <= d < 2048)%Z -> (d <= (z - a) mod 2048)%Z -> Z.land (a + d) 2047 <> z ->
inring a z (Z.land (a + d) 2047) /\ (d + 1 <= (z - a) mod 2048)%Z.
Proof. clear.
intros a z d Hz Hd Hle Hne. rewrite land2047 in *. unfold inring.
rewrite Zminus_mod_idemp_l. replace (a + d - a)%Z with d by lia. rewrite (Z.mod_small d 2048) by lia.
pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(lia)).
assert ((z - a) mod 2048 <> d)%Z; [|lia].
intros Ed. apply Hne. rewrite <- (Z.mod_small z 2048) by lia.
rewrite <- Ed. rewrite Zplus_mod_idemp_r. f_equal. lia.
Qed.
#[using="Type"] Lemma inring_hit : forall a z d, (0 <= z < 2048)%Z -> (0 <= d < 2048)%Z -> Z.land (a + d) 2047 = z -> ((z - a) mod 2048 = d)%Z.
Proof. clear.
intros a z d Hz Hd E. rewrite land2047 in E. rewrite <- E. rewrite Zminus_mod_idemp_l.
replace (a + d - a)%Z with d by lia. apply Z.mod_small. lia.
Qed.
#[using="Type"] Lemma inring_grow : forall a z i, (0 <= z)%Z -> ((z - a) mod 2048 < 2047)%Z ->
inring a (z + 1) i <-> (inring a z i \/ (i - a) mod 2048 = (z - a) mod 2048)%Z.
Proof. clear.
intros a z i Hz Hlt. unfold inring.
replace (z + 1 - a)%Z with ((z - a) + 1)%Z by lia. rewrite <- (Zplus_mod_idemp_l (z - a)).
pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(lia)). pose proof (Z.mod_pos_bound (i - a) 2048 ltac:(lia)).
rewrite (Z.mod_small ((z - a) mod 2048 + 1)) by lia. lia.
Qed.
#[using="Type"] Lemma mod_eq_idx : forall a z i, (0 <= z < 2048)%Z -> (0 <= i < 2048)%Z -> ((i - a) mod 2048 = (z - a) mod 2048)%Z -> i = z.
Proof. clear.
intros a z i Hz Hi E.
rewrite <- (Z.mod_small i 2048), <- (Z.mod_small z 2048) by lia.
transitivity (((i - a) mod 2048 + a) mod 2048)%Z. { rewrite Zplus_mod_idemp_l. f_equal. lia. }
rewrite E. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.
#[using="Type"] Lemma inring_mod : forall a z i, inring a (z mod 2048) i <-> inring a z i.
Proof. clear. intros. unfold inring. rewrite Zminus_mod_idemp_l. reflexivity. Qed.
#[using="Type"] Lemma xrel_iff : forall ws x (P Q : Z -> Prop), (forall i, (0 <= i < 2048)%Z -> Q i -> P i) -> xrel ws x P -> xrel ws x Q.
Proof. clear. intros ws x P Q HPQ (L1 & L2 & R). split; [exact L1|]. split; [exact L2|]. intros i Hi Hq. apply R; [exact Hi | apply HPQ; [exact Hi | exact Hq]]. Qed.

Definition zone (h w : bool) (a z : Z) (i : Z) : Prop := inring a z i \/ (h = true /\ (z <= i)%Z) \/ (w = true /\ (a <= i)%Z).
#[using="Type"] Lemma zone_in : forall h w a z i, inring a z i -> zone h w a z i.
Proof. clear. intros. left. assumption. Qed.
#[using="Type"] Lemma xrel_window : forall ws x h w a z, xrel ws x (zone h w a z) -> xrel ws x (inring a z).
Proof. clear. intros until z. apply xrel_iff. intros i _ Hi. left. exact Hi. Qed.

Definition X31 (x : list Z) : Prop := forall i, (0 <= znth x i < 2^31)%Z.

Definition S_F3 : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word) Ft fct
j0 w16 w24 b96 ev ws sign k c (Y FR BI e2 bits' : Z),
let _ := ctx_all in
dfinv m j0 w16 w24 b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= bits' <= 53)%Z ->
fin_K3 1024 Y FR BI e2 = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (e2 + 113)) (Z_to_bv 64 (hi64 FR)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (lo64 FR)) (Z_to_bv 64 1021) (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 e2) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (lo64 BI)) (Z_to_bv 64 (hi64 BI))
(Z_to_bv 64 (e2 + 1187)) (Z_to_bv 64 bits') x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7844) fct None m (seg_rom rsegs)).

#[using="Type"] Lemma f128_ge_range : forall a b, (-1 <= f128_ge a b <= 1)%Z.
Proof.
clear. intros a b. unfold f128_ge.
repeat (lazymatch goal with |- context [if ?c then _ else _] => destruct c | _ => fail end; try (cbn; lia)).
all: try (unfold nez64, b2z; destruct (negb _); cbn; lia).
Qed.

Tactic Notation "call_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 8656)%Z (q + -8416)%Z |- _ =>
let ST1 := fresh "ST1" in
destruct (stk_split _ _ _ (q + -8416 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -8416 - K)%Z (q + -8416)%Z |- _ =>
lazymatch goal with ST1' : stk _ m' (q - 8656)%Z (q + -8416 - K)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
end.

#[using="Type"] Lemma extenddftf2_callF : forall ra' sp' gp' tp' t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F' : bvmap 5 word) fc' (m : word -> option byte) (D : Z),
mem_inv rsegs m -> bv_unsigned (reg_get F' 10) = D ->
evt rsegs (leaf2_post ra' sp' gp' tp' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F' fc' (f128_of_d D) m)
(MS (mkR ra' sp' gp' tp' t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0xcb77c) fc' None m (seg_rom rsegs)).
Proof.
clear. intros until D. intros MI HD. eapply evt_mono. { eapply extenddftf2_spec. exact MI. }
intros ms' P. unfold extenddftf2_post in P. rewrite HD in P. exact P.
Qed.

Definition S_F2 : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (a z Y FR BI e2 bits' : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 FR)) (Z_to_bv 64 (hi64 FR)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= bits' <= 53)%Z ->
xrel ws x (inring a z) -> X31 x -> (0 <= a < 2048)%Z -> (0 <= z < 2048)%Z ->
(Z.land (a + 4) MASK <> z -> inring a z (Z.land (a + 4) MASK)) ->
fin_K2 sign 1024 a z x 4 bits' Y FR BI e2 = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (e2 + 113)) (Z_to_bv 64 (a + 4)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 e2) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (lo64 BI)) (Z_to_bv 64 (hi64 BI))
(Z_to_bv 64 (e2 + 1187)) (Z_to_bv 64 bits') x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd771c) fct None m (seg_rom rsegs)).

#[using="Type"] Lemma floatsitf_callsg : forall ra' sp' gp' tp' t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F' : bvmap 5 word) fc' (m : word -> option byte) (sg : Z),
mem_inv rsegs m -> (sg = 1 \/ sg = -1)%Z ->
evt rsegs (leaf2_post ra' sp' gp' tp' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F' fc' (f128_of_i32 sg) m)
(MS (mkR ra' sp' gp' tp' t0 t1 t2 s0 s1 (Z_to_bv 64 sg) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0xd08ac) fc' None m (seg_rom rsegs)).
Proof.
clear. intros until sg. intros MI [-> | ->].
- apply floatsitf_callp; [exact MI | lia].
- replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
apply floatsitf_callv; [exact MI | lia | rewrite sext32_eq; reflexivity].
Qed.

Definition S_F1 : Prop := forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (a z Y e2 : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z ->
xrel ws x (inring a z) -> X31 x -> (0 <= a < 2048)%Z -> (0 <= z < 2048)%Z ->
(Z.land (a + 4) MASK <> z -> inring a z (Z.land (a + 4) MASK)) ->
fin_K1 53 (-1074) sign 1024 zero0 a z x 4 Y e2 = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 (a + 4)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) x24
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7630) fct None m (seg_rom rsegs)).

#[using="Type"] Lemma lxor_sign_small : forall e, (-2^62 <= e < 2^62)%Z ->
Z.lxor (Z.land e 18446744073709551615) 9223372036854775808 = (e + 2^63)%Z.
Proof.
clear. intros e He. rewrite land_W64. change 9223372036854775808%Z with (2^63)%Z.
rewrite zb_lxor_sign by (apply Z.mod_pos_bound; lia). Z.div_mod_to_equations; lia.
Qed.

#[using="Type"] Lemma clamp0_idiom : forall v, (-2^62 <= v < 2^62)%Z ->
Z.land (Z.land (0 - Z.b2z (9223372036854775808 <? Z.lxor (Z.land v 18446744073709551615) 9223372036854775808)) 18446744073709551615)
(Z.land v 18446744073709551615) = (if v <? 0 then 0 else v)%Z.
Proof.
clear. intros v Hv. rewrite lxor_sign_small by lia.
destruct (Z.ltb_spec 9223372036854775808 (v + 2^63)); destruct (Z.ltb_spec v 0); try lia; cbn [Z.b2z].
- change (Z.land (0 - 1) 18446744073709551615)%Z with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. rewrite land_W64, Z.mod_mod by lia. apply Z.mod_small. lia.
- change (Z.land (0 - 0) 18446744073709551615)%Z with 0%Z. apply Z.land_0_l.
- assert (E : v = 0%Z) by lia. rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma cb44_merge : forall m A pre (bs : list byte) (w : word),
rw_cells rsegs m A (pre ++ [CB 4 bs; C4 w]) -> rw_cells rsegs m A (pre ++ [CB 8 (bs ++ le4 w)]).
Proof.
clear. intros m A pre bs w [[Hwf Hb] Hw].
apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 _]]. cbn in H2.
split; [split|].
- apply cells_wf_app. split; [exact H1|]. split; [|exact I]. cbn -[le4]. rewrite length_app, H2, length_le4. reflexivity.
- rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb |- *. rewrite <- app_assoc, app_nil_r in *. exact Hb.
- rewrite !cells_size_app in *. cbn [cells_size csize] in Hw |- *. exact Hw.
Qed.
Definition C1E9HI : Z := 0x401cdcd650000000.

Definition ainv (ws : list word) (x : list Z) (h w : bool) (a z i : Z) : Prop :=
xrel ws x (zone h w a z) /\ X31 x /\ (0 <= z < 2048)%Z /\ (h = false -> z + (4 - i) <= 2052)%Z /\ (i <= (z - a) mod 2048)%Z /\ (w = false -> a <= 60)%Z.

Definition S_A69C : Prop := forall m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (a z Y e2 : Z) (f : nat) sres,
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= a < 2048)%Z ->
ainv ws x h w a z 3 ->
df_asm_loop f a (mkAS 3 Y z x) = Some sres -> (2 <= f)%nat ->
fin_K1 53 (-1074) sign 1024 zero0 a (as_z sres) (as_x sres) (as_i sres) (as_y sres) e2 = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (a + 3)) x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 C1E9HI) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd75cc) fct None m (seg_rom rsegs)).

Definition S_A62C : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (a z Y e2 : Z) (f : nat) sres,
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= a < 2048)%Z ->
ainv ws x h w a z 2 ->
df_asm_loop f a (mkAS 2 Y z x) = Some sres -> (3 <= f)%nat ->
fin_K1 53 (-1074) sign 1024 zero0 a (as_z sres) (as_x sres) (as_i sres) (as_y sres) e2 = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (a + 2)) (Z_to_bv 64 XA) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 C1E9HI) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd755c) fct None m (seg_rom rsegs)).

Definition S_A5C4 : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (a z Y e2 : Z) (f : nat) sres,
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= a < 2048)%Z ->
ainv ws x h w a z 1 ->
df_asm_loop f a (mkAS 1 Y z x) = Some sres -> (4 <= f)%nat ->
fin_K1 53 (-1074) sign 1024 zero0 a (as_z sres) (as_x sres) (as_i sres) (as_y sres) e2 = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 C1E9HI) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd74f4) fct None m (seg_rom rsegs)).

Definition fin_K0 (sign a z : Z) (x : list Z) (e2 : Z) : option Z := df_final a z x e2 53 (-1074) sign 1024 zero0 zero0.

Definition S_A568 : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (a z e2 xa : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= a < 2048)%Z ->
ainv ws x h w a z 0 -> a <> z -> xa = znth x a ->
fin_K0 sign a z x e2 = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 xa) x23 x24
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7498) fct None m (seg_rom rsegs)).

Definition S_A534 : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (a z e2 S1 : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= a < 2048)%Z ->
ainv ws x h w a z 0 -> a = z -> S1 = (4 * ((z + 1) mod 2048))%Z ->
fin_K0 sign a z x e2 = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 ((z + 1) mod 2048)) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 x23 x24
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7464) fct None m (seg_rom rsegs)).

Definition SN324 (fo : nat) : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (rp a z e2 i0 Z0 S1 A6 : Z) s',
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (0 <= a < 2048)%Z ->
xrel ws x (zone h w a z) -> X31 x -> (0 <= z < 2048)%Z -> (h = false -> z + Z.of_nat fo <= 4100)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> (Z.of_nat fo <= 2000)%Z ->
(-2^26 + 18450 * Z.of_nat fo <= rp <= 560)%Z -> (-2^20 <= e2 <= 2^17 - 9 * Z.of_nat fo)%Z ->
Z0 = ((z + 1) mod 2048)%Z -> S1 = (4 * Z0)%Z -> A6 = (XA + 4 * ((z - 1) mod 2048))%Z ->
df_dn_loop fo (mkDS rp a z e2 x i0) = Some s' ->
fin_K0 sign (ds_a s') (ds_z s') (ds_x s') (ds_e2 s') = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 Z0) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 A6) x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7254) fct None m (seg_rom rsegs)).
Definition S_N324 : Prop := forall fo, SN324 fo.

Definition S_N2D4 : Prop := forall (fo : nat) m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (rp a z e2 i0 : Z) s',
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (0 <= a < 2048)%Z ->
xrel ws x (zone h w a z) -> X31 x -> (0 <= z < 2048)%Z -> (h = false -> z + Z.of_nat fo <= 4100)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> (Z.of_nat fo <= 2000)%Z ->
(-2^26 + 18450 * Z.of_nat fo <= rp <= 560)%Z -> (-2^20 <= e2 <= 2^17 - 9 * Z.of_nat fo)%Z ->
df_dn_loop fo (mkDS rp a z e2 x i0) = Some s' ->
fin_K0 sign (ds_a s') (ds_z s') (ds_x s') (ds_e2 s') = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7204) fct None m (seg_rom rsegs)).

Definition up_K (sign rp a z e2 : Z) (x : list Z) : option Z :=
match df_dn_loop FUEL_SCALE (mkDS rp a z e2 x 0) with
| None => None
| Some s' => fin_K0 sign (ds_a s') (ds_z s') (ds_x s') (ds_e2 s')
end.
Definition MAGIC : Z := 19342813113834067.

Definition S_U1A8 : Prop := forall (fo : nat) m (x1 x5 x6 x7 x8 x9 x16 x17 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (rp a z e2 : Z) s',
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (0 <= a < 2048)%Z ->
xrel ws x (zone h w a z) -> X31 x -> (0 <= z < 2048)%Z -> (h = false -> z <= 2047)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> a <> z ->
(-2^20 <= rp <= 560)%Z -> (-2^20 + 29 * Z.of_nat fo <= e2 <= 0)%Z ->
df_up_loop fo (mkUS rp a z e2 x) = Some s' ->
up_K sign (us_rp s') (us_a s') (us_z s') (us_e2 s') (us_x s') = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 XA) (Z_to_bv 64 36) (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) (Z_to_bv 64 10384592) x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd70d8) fct None m (seg_rom rsegs)).

#[using="Type"] Lemma df_dn_loop_step : forall n s, df_dn_loop (S n) s = match df_dn_body s with None => None | Some (inl s') => df_dn_loop n s' | Some (inr s') => Some s' end.
Proof. reflexivity. Qed.
#[using="Type"] Lemma df_dni_loop_step : forall n a z x i, df_dni_loop (S n) a z x i =
if (i <? LD_B1B_DIG)%Z then match df_dni_body a z x i with inl i' => df_dni_loop n a z x i' | inr i' => Some i' end else Some i.
Proof. reflexivity. Qed.
#[using="Type"] Lemma df_dnk_loop_step : forall n z sh s, df_dnk_loop (S n) z sh s = if negb (dk_k s =? z)%Z then df_dnk_loop n z sh (df_dnk_body z sh s) else Some s.
Proof. reflexivity. Qed.
#[using="Type"] Lemma dn_carry_bound : forall sh tmp, (sh = 1 \/ sh = 9)%Z -> (0 <= tmp <= 2^sh - 1)%Z -> (0 <= Z.shiftr 1000000000 sh * tmp < 2^30)%Z.
Proof. clear. intros sh tmp [-> | ->] H; [change (Z.shiftr 1000000000 1) with 500000000%Z | change (Z.shiftr 1000000000 9) with 1953125%Z]; cbn in H; lia. Qed.
#[using="Type"] Lemma shr_half : forall t sh, (0 <= t)%Z -> (1 <= sh)%Z -> (0 <= Z.shiftr t sh <= t / 2)%Z.
Proof.
clear. intros t sh Ht Hsh. split; [apply Z.shiftr_nonneg; lia|]. rewrite Z.shiftr_div_pow2 by lia.
apply Z.div_le_compat_l; [lia|]. split; [lia|]. change 2%Z with (2^1)%Z at 1. apply Z.pow_le_mono_r; lia.
Qed.
#[using="Type"] Lemma lor_lxor_zero : forall k a v, (0 <= k)%Z -> (0 <= a)%Z -> (0 <= v)%Z ->
Z.lor (Z.lxor k a) v = 0%Z <-> (k = a /\ v = 0%Z).
Proof.
clear. intros k a v Hk Ha Hv. split.
- intros H. apply Z.lor_eq_0_iff in H. destruct H as [H1 H2]. split; [|exact H2]. apply Z.lxor_eq_0_iff. exact H1.
- intros [-> ->]. rewrite Z.lxor_nilpotent. reflexivity.
Qed.
#[using="Type"] Lemma lor_lxor_nonneg : forall k a v, (0 <= k)%Z -> (0 <= a)%Z -> (0 <= v)%Z -> (0 <= Z.lor (Z.lxor k a) v)%Z.
Proof. clear. intros. apply Z.lor_nonneg. split; [apply Z.lxor_nonneg; lia | lia]. Qed.
#[using="Type"] Lemma rp_upd : forall rp (c : bool),
Z_to_bv 64 (rp + Z.land (Z.land (Z.b2z c + -1) 18446744073709551615) 18446744073709551607) = Z_to_bv 64 (if c then rp else rp - 9)%Z.
Proof.
clear. intros rp [|].
- change (Z.land (Z.land (Z.b2z true + -1) 18446744073709551615) 18446744073709551607) with 0%Z. rewrite Z.add_0_r. reflexivity.
- change (Z.land (Z.land (Z.b2z false + -1) 18446744073709551615) 18446744073709551607) with 18446744073709551607%Z.
apply Z_to_bv_eqm. Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma dn_az_none : forall fo rp z e2 x i0, (0 <= z < 2048)%Z -> rp <> 36%Z -> df_dn_loop fo (mkDS rp z z e2 x i0) = None.
Proof.
clear. induction fo as [|fo IH]; intros rp z e2 x i0 Hz Hrp; [reflexivity|].
rewrite df_dn_loop_step. unfold df_dn_body. cbn [ds_a ds_z ds_x ds_rp ds_e2].
change (df_dni_loop 6 z z x 0) with (if (0 <? LD_B1B_DIG)%Z then match df_dni_body z z x 0 with inl i' => df_dni_loop 5 z z x i' | inr i' => Some i' end else Some 0%Z).
change (0 <? LD_B1B_DIG)%Z with true. unfold df_dni_body. rewrite Z.add_0_r. change MASK with 2047%Z. rewrite land2047, Z.mod_small, Z.eqb_refl by lia. cbn [orb].
change LD_B1B_DIG with 4%Z. change (4 =? 4)%Z with true. replace (rp =? 9 * 4)%Z with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
cbv zeta. unfold FUEL_RING. rewrite df_dnk_loop_step. cbn [dk_k]. rewrite Z.eqb_refl. cbn [negb nz Z.eqb].
apply IH; assumption.
Qed.

Definition S_NK : Prop := forall (fi : nat) m (x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x20 x22 x24 x25 x26 x27 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign (x : list Z) (h w : bool) (k carry a i rp z sh e2 B : Z) (s1 : st_dnk),
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> Fok Ft -> frm0 fct ->
xrel ws x (zone h w a z) -> X31 x ->
(0 <= a < 2048)%Z -> (0 <= z < 2048)%Z -> (0 <= k < 2048)%Z -> ((k - a) mod 2048 <= (z - a) mod 2048)%Z -> k <> z ->
(0 <= carry < 2^30)%Z -> (sh = 1 \/ sh = 9)%Z -> (B + 9 * Z.of_nat fi <= rp <= 560)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> (-2^27 <= B)%Z -> (-2^21 <= e2 <= 2^21)%Z ->
df_dnk_loop fi z sh (mkDK k carry a i rp x) = Some s1 ->
(forall m' ws' b96' (x17' x28' x29' x30' x31' : word) (w' : bool),
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96' ev ws' sign fR ->
xrel ws' (dk_x s1) (zone h w' (dk_a s1) z) -> X31 (dk_x s1) ->
(0 <= dk_a s1 < 2048)%Z -> (0 <= dk_carry s1 < 2^30)%Z -> (B <= dk_rp s1 <= 560)%Z -> (w' = false -> 9 * dk_a s1 + dk_rp s1 <= 560)%Z -> dk_k s1 = z ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 sh) (Z_to_bv 64 (dk_carry s1)) (Z_to_bv 64 (Z.shiftr 1000000000 sh)) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17'
(Z_to_bv 64 z) (Z_to_bv 64 (dk_a s1)) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 (dk_rp s1)) x24 x25 x26 x27 x28' x29' x30' x31')
Ft (Z_to_bv 64 0xd73b4) fct None m' (seg_rom rsegs))) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 sh) (Z_to_bv 64 carry) (Z_to_bv 64 (Z.shiftr 1000000000 sh)) x8 x9 x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (2^sh - 1))
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 (Z_to_bv 64 k) x29 x30 x31)
Ft (Z_to_bv 64 0xd7380) fct None m (seg_rom rsegs)).

Definition S_N484 : Prop := forall (fo : nat), SN324 fo ->
forall (s1 : st_dnk) m (x1 x10 x11 x12 x13 x14 x15 x17 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (h w : bool) (rp z e2 Z0 S1 A6 sh : Z) s',
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z ->
xrel ws (dk_x s1) (zone h w (dk_a s1) z) -> X31 (dk_x s1) ->
(0 <= dk_a s1 < 2048)%Z -> (0 <= dk_carry s1 < 2^30)%Z -> dk_k s1 = z -> (sh = 1 \/ sh = 9)%Z ->
(0 <= z < 2048)%Z -> (h = false -> z + Z.of_nat (S fo) <= 4100)%Z -> (w = false -> 9 * dk_a s1 + dk_rp s1 <= 560)%Z -> (Z.of_nat (S fo) <= 2000)%Z ->
(-2^26 + 18450 * Z.of_nat (S fo) <= rp <= 560)%Z -> (rp - 18450 <= dk_rp s1 <= 560)%Z -> (-2^20 <= e2 <= 2^17 - 9 * Z.of_nat (S fo))%Z ->
Z0 = ((z + 1) mod 2048)%Z -> S1 = (4 * Z0)%Z -> A6 = (XA + 4 * ((z - 1) mod 2048))%Z ->
(let 'mkDK _ carry a1 i rp1 xx := s1 in
let '(z', x') := if nz carry then
if negb ((z + 1) mod 2048 =? a1)%Z then ((z + 1) mod 2048, zupd xx z carry)%Z
else (z, zupd xx ((z - 1) mod 2048) (Z.lor (znth xx ((z - 1) mod 2048)) 1))%Z
else (z, xx) in
df_dn_loop fo (mkDS rp1 a1 z' (e2 + sh) x' i) = Some s') ->
fin_K0 sign (ds_a s') (ds_z s') (ds_x s') (ds_e2 s') = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 sh) (Z_to_bv 64 (dk_carry s1)) (Z_to_bv 64 (Z.shiftr 1000000000 sh)) (Z_to_bv 64 Z0) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 A6) x17
(Z_to_bv 64 z) (Z_to_bv 64 (dk_a s1)) x20 (Z_to_bv 64 (e2 + sh)) x22 (Z_to_bv 64 (dk_rp s1)) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd73b4) fct None m (seg_rom rsegs)).

Definition S_N3E8 : Prop := forall (fo : nat), SN324 fo ->
forall (iq : Z) m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (rp a z e2 Z0 S1 A6 : Z) s',
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (0 <= a < 2048)%Z ->
xrel ws x (zone h w a z) -> X31 x -> (0 <= z < 2048)%Z -> (h = false -> z + Z.of_nat (S fo) <= 4100)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> (Z.of_nat (S fo) <= 2000)%Z ->
(-2^26 + 18450 * Z.of_nat (S fo) <= rp <= 560)%Z -> (-2^20 <= e2 <= 2^17 - 9 * Z.of_nat (S fo))%Z ->
Z0 = ((z + 1) mod 2048)%Z -> S1 = (4 * Z0)%Z -> A6 = (XA + 4 * ((z - 1) mod 2048))%Z -> a <> z ->
match
match df_dnk_loop FUEL_RING z (if 45 <? rp then 9%Z else 1%Z) (mkDK a 0 a iq rp x) with
| Some (mkDK _ carry a1 i rp1 xx) =>
let '(z', x') := (if nz carry then
if negb ((z + 1) mod 2048 =? a1)%Z then ((z + 1) mod 2048, zupd xx z carry)%Z
else (z, zupd xx ((z - 1) mod 2048) (Z.lor (znth xx ((z - 1) mod 2048)) 1))%Z
else (z, xx)) in
Some (inl (mkDS rp1 a1 z' (e2 + (if 45 <? rp then 9%Z else 1%Z)) x' i))
| None => None
end
with
| Some (inl s'') => df_dn_loop fo s''
| Some (inr s'') => Some s''
| None => None
end = Some s' ->
fin_K0 sign (ds_a s') (ds_z s') (ds_x s') (ds_e2 s') = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 Z0) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 A6) x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd7318) fct None m (seg_rom rsegs)).

#[using="Type"] Lemma df_up_loop_step : forall n s, df_up_loop (S n) s = if df_up_cond s then match df_up_body s with None => None | Some s' => df_up_loop n s' end else Some s.
Proof. reflexivity. Qed.
#[using="Type"] Lemma df_upk_loop_step : forall n a s, df_upk_loop (S n) a s = match df_upk_body a s with inl s' => df_upk_loop n a s' | inr s' => Some s' end.
Proof. reflexivity. Qed.
#[using="Type"] Lemma mod_add2047 : forall u, ((u + 2047) mod 2048 = (u - 1) mod 2048)%Z.
Proof. clear. intros u. rewrite <- (Z.mod_add (u - 1) 1 2048) by lia. f_equal. lia. Qed.

#[using="Type"] Lemma magic_div_1e9 : forall tmp, (0 <= tmp < 2^61)%Z ->
(Z.shiftr ((Z.shiftr tmp 9 * MAGIC) / 2^64) 11 = tmp / 1000000000)%Z.
Proof.
clear. intros tmp Ht. unfold MAGIC. rewrite !Z.shiftr_div_pow2 by lia.
rewrite Z.div_div by lia. change (2^64 * 2^11)%Z with (2^75)%Z.
replace (tmp / 1000000000)%Z with ((tmp / 2^9) / 1953125)%Z by (rewrite Z.div_div by lia; f_equal).
set (u := (tmp / 2^9)%Z). assert (Hu : (0 <= u < 2^52)%Z) by (subst u; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
clearbody u. clear Ht tmp. Z.div_mod_to_equations. nia.
Qed.

#[using="Type"] Lemma magic_div_1e9_reg : forall tmp, (0 <= tmp < 2^61)%Z ->
Z.shiftr (Z.land (Z.shiftr (Z.shiftr tmp 9 * Z.land MAGIC 18446744073709551615) 64) 18446744073709551615) 11 = (tmp / 1000000000)%Z.
Proof.
clear. intros tmp Ht. change (Z.land MAGIC 18446744073709551615) with MAGIC.
assert (R1 : (0 <= Z.shiftr tmp 9 < 2^52)%Z) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (R2 : (0 <= Z.shiftr (Z.shiftr tmp 9 * MAGIC) 64 < 2^64)%Z).
{ unfold MAGIC. rewrite (Z.shiftr_div_pow2 _ 64) by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia|]]. nia. }
rewrite land_W64, (Z.mod_small _ _ R2). rewrite (Z.shiftr_div_pow2 _ 64) by lia. apply magic_div_1e9. exact Ht.
Qed.
#[using="Type"] Lemma u32_id : forall v, (0 <= v < 2^32)%Z -> u32 v = v.
Proof. clear. intros. unfold u32. apply Z.mod_small. lia. Qed.
#[using="Type"] Lemma inring_front : forall a z i, (0 <= a < 2048)%Z -> (0 <= i < 2048)%Z -> (0 <= z < 2048)%Z ->
inring ((a - 1) mod 2048) z i -> i <> ((a - 1) mod 2048)%Z -> z <> ((a - 1) mod 2048)%Z -> inring a z i.
Proof. clear. intros a z i Ha Hi Hz H Hne Hzne. unfold inring in *. Z.div_mod_to_equations. nia. Qed.

Definition S_UK : Prop := forall (n : nat) m (x1 x5 x6 x8 x9 x11 x15 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign (x : list Z) (h w : bool) (k carry a z : Z) (s1 : st_upk),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> Fok Ft -> frm0 fct ->
xrel ws x (zone h w a z) -> X31 x ->
(0 <= a < 2048)%Z -> (0 <= z < 2048)%Z -> (0 <= k < 2048)%Z -> inring a z k ->
(0 <= carry < 2^31)%Z ->
df_upk_loop n a (mkUK k carry z x) = Some s1 ->
(forall m' ws' (x7' x18' x29' x30' x31' : word) (h' : bool),
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws' sign fR ->
xrel ws' (uk_x s1) (zone h' w a (uk_z s1)) -> X31 (uk_x s1) ->
uk_k s1 = a -> (0 <= uk_carry s1 < 2^31)%Z -> (0 <= uk_z s1 < 2048)%Z -> (h' = false -> h = false /\ uk_z s1 <= z)%Z -> a <> uk_z s1 ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 (Z_to_bv 64 (uk_z s1)) x7' x8 x9 (Z_to_bv 64 XA) x11 (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) x15 (Z_to_bv 64 (uk_carry s1)) x17
x18' (Z_to_bv 64 a) x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 ((uk_z s1 - 1) mod 2048)) x29' x30' x31')
Ft (Z_to_bv 64 0xd70e8) fct None m' (seg_rom rsegs))) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 (Z_to_bv 64 k) x8 x9 (Z_to_bv 64 XA) x11 (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) x15 (Z_to_bv 64 carry) x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd711c) fct None m (seg_rom rsegs)).

Definition SU1C4 (fo : nat) : Prop := forall m (x1 x6 x7 x8 x9 x16 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (rp a z e2 : Z) s',
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (0 <= a < 2048)%Z ->
xrel ws x (zone h w a z) -> X31 x -> (0 <= z < 2048)%Z -> (h = false -> z <= 2047)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> a <> z ->
(-2^20 <= rp <= 560)%Z -> (-2^20 + 29 * Z.of_nat fo <= e2 <= 0)%Z ->
df_up_loop fo (mkUS rp a z e2 x) = Some s' ->
up_K sign (us_rp s') (us_a s') (us_z s') (us_e2 s') (us_x s') = Some yR ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 rp) x6 x7 x8 x9 (Z_to_bv 64 XA) (Z_to_bv 64 36) (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) (Z_to_bv 64 10384592) x16 (Z_to_bv 64 (XA + 4 * a))
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd70f4) fct None m (seg_rom rsegs)).
Definition S_U1C4 : Prop := forall fo, SU1C4 fo.

Definition S_T : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (rp kz : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z ->
xrel ws x (inring 0 kz) -> X31 x -> (1 <= kz <= 2046)%Z -> znth x 0 <> 0%Z -> (-2^15 <= rp <= 537)%Z ->
dfK_tz 53 (-1074) sign fR rp kz x = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6f5c) fct None m (seg_rom rsegs)).

Definition S_DD0 : Prop := forall m (x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (X Y : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
yR = f128_mul X Y ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6d00) fct None m (seg_rom rsegs)).

Definition S_DD24 : Prop := forall m (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (X u : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(0 <= u < 2^31)%Z -> yR = f128_mul X (f128_of_u32 u) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 u) x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6c54) fct None m (seg_rom rsegs)).

Definition S_M : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (rp lnz kz : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z ->
xrel ws x (inring 0 kz) -> X31 x -> (1 <= kz <= 2046)%Z -> znth x 0 <> 0%Z -> (1 <= lnz < 2^31)%Z -> (-1300 <= rp <= 537)%Z ->
dfK_mid 53 (-1074) sign fR rp lnz kz x = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 lnz) x14 x15 x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6d8c) fct None m (seg_rom rsegs)).

Definition digz (k j : Z) (i : Z) : Prop := (i < k)%Z \/ i = 0%Z \/ (i = k /\ j <> 0%Z).

Definition S_P : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 ev ws sign k c (x : list Z) (lrp lnz j kz : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) (le8 (Z_to_bv 64 lnz)) ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z ->
xrel ws x (digz kz j) -> X31 x ->
(0 <= j <= 8)%Z -> (0 <= kz <= 2045)%Z -> znth x 0 <> 0%Z -> (1 <= lnz < 2^31)%Z -> (-1300 <= lrp <= 537)%Z ->
(j <> 0%Z -> znth x kz < 10 ^ j)%Z -> (kz = 0%Z -> j = 0%Z -> znth x 0 = 0%Z) -> (kz = 2045%Z -> j = 0%Z) ->
dfK_pad 53 (-1074) sign fR lrp lnz j kz x = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 lrp) (Z_to_bv 64 kz) x25 (Z_to_bv 64 j) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6d10) fct None m (seg_rom rsegs)).

Definition S_R : Prop := forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w80 : word) ev ws sign k c (x : list Z) (lrp dc lnz j kz : Z),
let _ := ctx_all in
dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 (le8 (Z_to_bv 64 lnz)) ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z ->
xrel ws x (digz kz j) -> X31 x ->
(0 <= j <= 8)%Z -> (0 <= kz <= 2045)%Z -> (0 <= dc < 2^31)%Z -> (0 <= lnz < 2^31)%Z -> (znth x 0 <> 0%Z -> 1 <= lnz)%Z ->
(j <> 0%Z -> znth x kz < 10 ^ j)%Z -> (kz = 0%Z -> j = 0%Z -> znth x 0 = 0%Z) -> (kz = 2045%Z -> j = 0%Z) -> (-2^62 <= lrp < 2^62)%Z ->
(znth x 0 <> 0%Z -> w80 = Z_to_bv 64 18396) ->
dfK_rng 53 (-1074) sign fR lrp dc lnz j kz x = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 dc) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 lrp) (Z_to_bv 64 kz) x25 (Z_to_bv 64 j) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6c14) fct None m (seg_rom rsegs)).

Definition dig_facts (ws : list word) (x : list Z) (j kz dc lnz : Z) : Prop :=
xrel ws x (digz kz j) /\ X31 x /\
(0 <= j <= 8)%Z /\ (0 <= kz <= 2045)%Z /\ (0 <= dc < 2^31)%Z /\ (0 <= lnz < 2^31)%Z /\ (znth x 0 <> 0%Z -> 1 <= lnz)%Z /\
(j <> 0%Z -> znth x kz < 10 ^ j)%Z /\ (kz = 0%Z -> j = 0%Z -> znth x 0 = 0%Z) /\ (kz = 2045%Z -> j = 0%Z).

Definition S_C38 : Prop := forall m (x1 x5 x6 x7 x8 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w80 : word) ev ws sign kmin c (x : list Z) (f : shfile) (lrp dc lnz j kz gotdig ng : Z),
let _ := ctx_all in
dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 (le8 (Z_to_bv 64 lnz)) ev ws sign f -> RFJ' kmin c f -> (0 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
dig_facts ws x j kz dc lnz -> (znth x 0 <> 0%Z -> w80 = Z_to_bv 64 18396) ->
(0 <= gotdig <= 1)%Z -> ng = Z.b2z (gotdig =? 0)%Z -> (-2^62 <= lrp < 2^62)%Z ->
(if negb (nz gotdig) then Some (sh_lim0 f, f128_of_i32 0) else dfK_rng 53 (-1074) sign f lrp dc lnz j kz x) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 dc) x10 (Z_to_bv 64 ng) x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 Fp) x22 (Z_to_bv 64 lrp) (Z_to_bv 64 kz) x25 (Z_to_bv 64 j) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6b68) fct None m (seg_rom rsegs)).

Definition S_C2C : Prop := forall m (x1 x5 x6 x7 x8 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w80 : word) ev ws sign kmin c (x : list Z) (f : shfile) (lrp dc lnz j kz gotdig ng : Z),
let _ := ctx_all in
dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 (le8 (Z_to_bv 64 lnz)) ev ws sign f -> RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> sh_shlim_neg f = false ->
dig_facts ws x j kz dc lnz -> (znth x 0 <> 0%Z -> w80 = Z_to_bv 64 18396) ->
(0 <= gotdig <= 1)%Z -> ng = Z.b2z (gotdig =? 0)%Z -> (-2^62 <= lrp < 2^62)%Z ->
(if negb (nz gotdig) then Some (sh_lim0 (sh_unget f), f128_of_i32 0) else dfK_rng 53 (-1074) sign (sh_unget f) lrp dc lnz j kz x) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 dc) x10 (Z_to_bv 64 ng) x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 Fp) x22 (Z_to_bv 64 lrp) (Z_to_bv 64 kz) x25 (Z_to_bv 64 j) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6b5c) fct None m (seg_rom rsegs)).

Definition S_E : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w80 : word) ev ws sign kmin c (x : list Z) (f : shfile) (lrp dc lnz j kz gotdig gotrad : Z),
let _ := ctx_all in
dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 (le8 (Z_to_bv 64 lnz)) ev ws sign f -> RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
dig_facts ws x j kz dc lnz -> (znth x 0 <> 0%Z -> w80 = Z_to_bv 64 18396) ->
(0 <= gotdig <= 1)%Z -> (0 <= gotrad <= 1)%Z -> (- 2^31 <= lrp < 2^31)%Z ->
dfK_exp fuelc 53 (-1074) sign pok (mkDL f c j kz lrp dc lnz gotdig gotrad x) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 dc) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) x22 x23 (Z_to_bv 64 kz) (Z_to_bv 64 lrp) (Z_to_bv 64 j) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd69e4) fct None m (seg_rom rsegs)).

Definition digI (ws : list word) (x : list Z) (f : shfile) (c j k lrp dc lnz gotdig gotrad : Z) : Prop :=
xrel ws x (digz k j) /\ X31 x /\ (0 <= j <= 8)%Z /\ (0 <= k)%Z /\ (9 * k + j <= dc)%Z /\
(0 <= dc <= sh_rpos f)%Z /\ (c <> (-1)%Z -> dc + 1 <= sh_rpos f)%Z /\
(0 <= lnz <= dc)%Z /\ (znth x 0 <> 0%Z -> 1 <= lnz)%Z /\ (j <> 0%Z -> znth x k < 10 ^ j)%Z /\ (k = 0%Z -> j = 0%Z -> znth x 0 = 0%Z) /\
(- 2^31 <= lrp < 2^31)%Z /\ (0 <= gotdig <= 1)%Z /\ (0 <= gotrad <= 1)%Z /\
(k <= 2045)%Z /\ (k = 2045%Z -> j = 0%Z).

Definition SDn (n : nat) : Prop := forall m (x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) Ft fct
j0 ev ws sign kmin c (x : list Z) (f : shfile) (j k lrp dc lnz gotdig gotrad : Z) (s' : st_dig),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) (le8 (Z_to_bv 64 lnz)) ev ws sign f -> RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
digI ws x f c j k lrp dc lnz gotdig gotrad ->
(isdigitc c || (c =? 46))%Z = true ->
df_dig_loop n (mkDL f c j k lrp dc lnz gotdig gotrad x) = Some s' ->
dfK_exp fuelc 53 (-1074) sign pok s' = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 48) (Z_to_bv 64 dc) (Z_to_bv 64 c) (Z_to_bv 64 (c + -48)) (Z_to_bv 64 (Z.b2z (c =? 46)%Z)) x13 x14 x15 x16 x17
(Z_to_bv 64 (q + -136)) (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 46) (Z_to_bv 64 k) (Z_to_bv 64 lrp) (Z_to_bv 64 j) (Z_to_bv 64 2044) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6a9c) fct None m (seg_rom rsegs)).
Definition S_D : Prop := forall n, SDn n.

Definition winv (m : word -> option byte) (j0 : list byte) (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) (ev : word)
(ws : list word) (f : shfile) : Prop :=
finv m /\ framL j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev m
/\ u32arr rsegs m XA ws /\ length ws = 2048%nat /\ rw_cells rsegs m Fp (rf_cells T p true f J).
#[using="Type"] Lemma winv_dfinvG : forall m j0 w16 w24 w80 b96 ev ws sign f,
winv m j0 (Z_to_bv 64 1021) w16 w24 (Z_to_bv 64 1) (Z_to_bv 64 (-1074)) (Z_to_bv 64 1074) (Z_to_bv 64 53) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w80 (Z_to_bv 64 ssp_guard) b96 ev ws f
= dfinvG m j0 w16 w24 w80 b96 ev ws sign f.
Proof. reflexivity. Qed.

Definition X0 : list Z := zupd (zrepeat 0 KMAX) 0 0.

Definition fch (c : Z) : Prop := is_numch c = true \/ c = 0%Z \/ c = (-1)%Z.

Definition S_B0C : Prop := forall m (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x22 x24 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w80 : word) (b96 : list byte) ev ws sign kmin c (f : shfile) (lrp gotdig gotrad : Z),
let _ := ctx_all in
dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 b96 ev ws sign f -> RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> wval ws 0 = 0%Z ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> (- sh_rpos f <= lrp <= 0)%Z -> (0 <= gotdig <= 1)%Z -> (0 <= gotrad <= 1)%Z ->
(isdigitc c || (c =? 46))%Z = true ->
dfK_dig fuelc 53 (-1074) sign pok (mkDL f c 0 0 lrp 0 0 gotdig gotrad X0) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 c) (Z_to_bv 64 (c + -48)) x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 46) x24 (Z_to_bv 64 lrp) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6a3c) fct None m (seg_rom rsegs)).

Definition S_A9C : Prop := forall m (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x22 x24 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w80 : word) (b96 : list byte) ev ws sign kmin c (f : shfile) (lrp gotdig gotrad : Z),
let _ := ctx_all in
dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 b96 ev ws sign f -> RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> wval ws 0 = 0%Z ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> (- sh_rpos f <= lrp <= 0)%Z -> (0 <= gotdig <= 1)%Z -> (0 <= gotrad <= 1)%Z ->
c <> 46%Z ->
dfK_dig fuelc 53 (-1074) sign pok (mkDL f c 0 0 lrp 0 0 gotdig gotrad X0) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 c) (Z_to_bv 64 (c + -48)) x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 46) x24 (Z_to_bv 64 lrp) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd69cc) fct None m (seg_rom rsegs)).

Definition S_A44 : Prop := forall m (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x23 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w32 w48 w80 : word) (b96 : list byte) ev ws sign kmin c (f : shfile) (lrp gotdig : Z),
let _ := ctx_all in
winv m j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 (Z_to_bv 64 (-1074)) w48 (Z_to_bv 64 53) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w80 (Z_to_bv 64 ssp_guard) b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> (- sh_rpos f <= lrp <= 0)%Z -> (0 <= gotdig <= 1)%Z -> c <> 48%Z ->
dfK_dig fuelc 53 (-1074) sign pok (mkDL f c 0 0 lrp 0 0 gotdig 1 X0) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 gotdig) x20 (Z_to_bv 64 Fp) x22 x23 (Z_to_bv 64 1) (Z_to_bv 64 lrp) (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6974) fct None m (seg_rom rsegs)).

#[using="Type"] Lemma df_dig_loop_step : forall n s, df_dig_loop (S n) s = if df_dig_cond s then match df_dig_body s with inl s' => df_dig_loop n s' | inr s' => Some s' end else Some s.
Proof. reflexivity. Qed.
#[using="Type"] Lemma df_rz_loop_step : forall n g l c f, df_rz_loop (S n) (g, l, c, f) =
(if c =? 48 then df_rz_loop n (1, l - 1, fst (sh_getc f), snd (sh_getc f)) else Some (g, l, c, f))%Z.
Proof. clear. intros. cbn [df_rz_loop df_rz_body]. destruct (sh_getc f). reflexivity. Qed.
#[using="Type"] Lemma df_lz_loop_step : forall n g c f, df_lz_loop (S n) (g, c, f) =
(if c =? 48 then df_lz_loop n (1, fst (sh_getc f), snd (sh_getc f)) else Some (g, c, f))%Z.
Proof. clear. intros. cbn [df_lz_loop df_lz_body]. destruct (sh_getc f). reflexivity. Qed.

Definition SRZn (n : nat) : Prop := forall m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w32 w48 w80 : word) (b96 : list byte) ev ws sign kmin (f : shfile) (lrp g : Z) (g' lrp' c' : Z) (f' : shfile),
let _ := ctx_all in
winv m j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 (Z_to_bv 64 (-1074)) w48 (Z_to_bv 64 53) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w80 (Z_to_bv 64 ssp_guard) b96 ev ws f ->
RFJ' kmin 48 f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(1 - sh_rpos f <= lrp <= 0)%Z ->
df_rz_loop n (g, lrp, 48, f)%Z = Some (g', lrp', c', f') ->
dfK_dig fuelc 53 (-1074) sign pok (mkDL f' c' 0 0 lrp' 0 0 g' 1 X0) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 48) x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 Fp) x22 x23 (Z_to_bv 64 1) (Z_to_bv 64 lrp) (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6950) fct None m (seg_rom rsegs)).
Definition S_RZ : Prop := forall n, SRZn n.

Definition S_9EC : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile) (gotdig : Z) (g' lrp' c' : Z) (f' : shfile),
let _ := ctx_all in
winv m j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> (0 <= gotdig <= 1)%Z ->
df_rz_loop fuelc (gotdig, 0, c, f)%Z = Some (g', lrp', c', f') ->
dfK_dig fuelc 53 (-1074) sign pok (mkDL f' c' 0 0 lrp' 0 0 g' 1 X0) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) (Z_to_bv 64 gotdig) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd691c) fct None m (seg_rom rsegs)).

Definition S_A64 : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> c <> 46%Z ->
dfK_dig fuelc 53 (-1074) sign pok (mkDL f c 0 0 0 0 0 1 0 X0) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6994) fct None m (seg_rom rsegs)).

Definition S_7F4 : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> c <> 46%Z ->
dfK_dig fuelc 53 (-1074) sign pok (mkDL f c 0 0 0 0 0 0 0 X0) = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 c) (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6724) fct None m (seg_rom rsegs)).

Definition S_9C8 : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 w8 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> c <> 48%Z ->
dfK_rz fuelc 53 (-1074) sign pok 1 c f = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) (Z_to_bv 64 1021) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd68f8) fct None m (seg_rom rsegs)).

Definition SLZn (n : nat) : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin (f : shfile) (g : Z) (g' c' : Z) (f' : shfile),
let _ := ctx_all in
winv m j0 w8 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin 48 f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
df_lz_loop n (g, 48, f)%Z = Some (g', c', f') ->
dfK_rz fuelc 53 (-1074) sign pok g' c' f' = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 48) (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) (Z_to_bv 64 1021) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd68dc) fct None m (seg_rom rsegs)).
Definition S_LZ : Prop := forall n, SLZn n.

Definition S_990 : Prop := forall (n : nat) m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile) (g' c' : Z) (f' : shfile),
let _ := ctx_all in
winv m j0 w8 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z ->
df_lz_loop n (1, c, f)%Z = Some (g', c', f') ->
dfK_rz fuelc 53 (-1074) sign pok g' c' f' = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd68c0) fct None m (seg_rom rsegs)).

Definition S_848 : Prop := forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (2 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
decfloat fuelc (sh_unget f) 48 53 (-1074) sign pok = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6778) fct None m (seg_rom rsegs)).

Definition S_6F8 : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> c <> 48%Z ->
decfloat fuelc f c 53 (-1074) sign pok = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6628) fct None m (seg_rom rsegs)).

Definition FS_tail (sign c : Z) (f : shfile) : option (shfile * Z) :=
if (c =? 48)%Z then
let '(c2, f2) := sh_getc f in
if (Z.lor c2 32 =? 120)%Z then None else decfloat fuelc (sh_unget f2) 48 53 (-1074) sign pok
else decfloat fuelc f c 53 (-1074) sign pok.

Definition S_618 : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z ->
FS_tail sign c f = Some (fR, yR) ->
evt rsegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd6548) fct None m (seg_rom rsegs)).
End Floatscan.
End Mq0.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QlEo_c1 Q2qa Q4J3 QytA Qnxq QJE4 QWTl QPjm QUZl Q7S0 QGeV QLsg QkQT QlkP QyjG QTyG QM7w QNAo QCwx QFqQ Q98Z QkLq QdZ1 Qv4L Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq Q4J3.Mq3 QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QyjG QTyG.Mq0 QM7w QNAo.Mq0.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq1 Q98Z.Mq2 QkLq.Mq0 QkLq.Mq1 QdZ1.Mq3 Qv4L.Mqa QQbX.Mq3 Qv4L.Mq0 QnkH.Mq2.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rgmf_of_facts st LB sc g :
RISTF st LB -> lmem st g -> m_sizeclass (get_meta_rec st g) = sc -> 0 <= sc < 48 -> gmf st sc g.
Proof.
intros F (MEM & NX & PV) GSC SCR. assert (SC48 : m_sizeclass (get_meta_rec st g) < 48) by lia.
pose proof (isf_mf _ _ F) as MF. pose proof (isf_lf _ _ F) as LF. pose proof (isf_ghdr _ _ F) as GU.
destruct (m_mem (get_meta_rec st g)) as [b|] eqn:Hmem; [|congruence].
pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
specialize (FG g b Hmem). cbv zeta in FG.
destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh & AI & AVAI) & _).
pose proof (lf_mw _ (isf_lf _ _ F) g) as (MW & _ & _). change (get_meta_rec (strip st) g) with (get_meta_rec st g) in MW.
pose proof (mf_masks _ _ MF) as FM. change (fact_masks (strip st)) with (fact_masks st) in FM.
constructor.
- exact MSL.
- exact AVr.
- exact FRr.
- exact MW.
- exact SC48.
- exact GSC.
- exists b, (mkGhdr (Some g) ai). split; [exact Hmem|]. split; [exact Hgh|]. split; [reflexivity|]. split; [cbn; lia|]. split.
+ intros S0. cbn. pose proof (lf_sc0_full _ LF g b (mkGhdr (Some g) ai)) as X.
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in X. change (s_groups (strip st)) with (s_groups st) in X.
exact (X Hmem Hgh S0).
+ intros o Ho. exact (GU b _ o Hgh Ho).
- intros i Hi Hb. destruct (FM g b Hmem) as (F1 & F2 & _). exact (F2 i Hi Hb).
- intros i Hi Hb. destruct (FM g b Hmem) as (F1 & F2 & _). exact (F1 i Hi Hb).
- destruct (m_next (get_meta_rec st g)) as [n|] eqn:En; [|congruence]. destruct (m_prev (get_meta_rec st g)) as [p|] eqn:Ep; [|congruence].
exists n, p. split; reflexivity.
Qed.

#[using="Type"] Lemma rtaf_of_facts st LB sc : RISTF st LB -> 0 <= sc < 48 -> taf st sc.
Proof.
intros F SC. pose proof (isf_mf _ _ F) as MF. pose proof (isf_lf _ _ F) as LF.
pose proof (lf_lists _ LF) as (L1 & L2 & L3).
change (fact_active (strip st)) with (fact_active st).
pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
pose proof (lf_links _ LF) as LK.
constructor.
- intros g Hg. destruct (FA sc g Hg) as (_ & GSC & _). pose proof (L1 sc g Hg) as LM.
change (lmem (strip st) g) with (lmem st g) in LM.
split; [| exact GSC]. eapply rgmf_of_facts; [exact F| exact LM| exact GSC| exact SC].
- intros g n GM Hn. destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & _).
destruct (L2 g n ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); rewrite Hmem; discriminate) Hn) as [LMn SCn].
change (lmem (strip st) n) with (lmem st n) in LMn. change (get_meta_rec (strip st) n) with (get_meta_rec st n) in SCn.
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SCn.
split; [eapply rgmf_of_facts; [exact F| exact LMn| rewrite SCn; exact (gmf_cls _ _ _ GM)| exact SC]|].
split; [exact SCn|].
destruct (gmf_links _ _ _ GM) as (n' & p' & En & Ep).
destruct (LK g ltac:(split; [rewrite Hmem; discriminate| split; [rewrite En| rewrite Ep]; discriminate])) as [LKn _].
exact (LKn n Hn).
- intros g p GM Hp. destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & _).
destruct (L3 g p ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); rewrite Hmem; discriminate) Hp) as [LMp SCp].
change (lmem (strip st) p) with (lmem st p) in LMp. change (get_meta_rec (strip st) p) with (get_meta_rec st p) in SCp.
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SCp.
split; [eapply rgmf_of_facts; [exact F| exact LMp| rewrite SCp; exact (gmf_cls _ _ _ GM)| exact SC]|].
destruct (gmf_links _ _ _ GM) as (n' & p' & En & Ep).
destruct (LK g ltac:(split; [rewrite Hmem; discriminate| split; [rewrite En| rewrite Ep]; discriminate])) as [_ LKp].
exact (LKp p Hp).
- pose proof (mf_ctx _ _ MF) as (_ & _ & _ & _ & B & _). intros i. exact (B i).
Qed.

Section FPER.
Variables (st0 st : mstate) (m : mem).
Hypothesis MR : rmrep st m.
Hypothesis ER : ENTRY_REL st0 st.

#[using="st m MR ER"] Lemma rst0_region rid r : (s_regions st0) !! rid = Some r ->
0 <= r_base r /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
/\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x3d000 <= r_base r)
/\ (r_base r + round_up_pg (r_len r) <= 0x3d000 \/ 0xe2000 <= r_base r)
/\ (r_base r + round_up_pg (r_len r) <= 0xe2000 \/ 0xe7000 <= r_base r)
/\ (r_base r + round_up_pg (r_len r) <= 0xe7000 \/ 0x645000 <= r_base r).
Proof.
intros Hr. destruct (mrel_regions _ _ (er_mrel _ _ ER) rid r Hr) as (r' & Hr' & K' & B' & L').
pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
destruct (WR rid r' Hr') as (RB0 & RBAL & RL0 & RBC & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4).
pose proof (round_up_pg_mono _ _ L'). pose proof (round_up_pg_ge (r_len r)). rewrite B' in *. unfold alloc_ceiling in *. lia.
Qed.

#[using="st m MR ER"] Lemma rmalloc_fp_cases_ER stE mE lo sp a :
rmrep stE mE -> rmalloc_fp st0 stE lo sp a -> lo <= a < sp \/ a < alloc_ceiling.
Proof.
intros (WF2 & _) H. pose proof WF2 as (_ & WR2 & _).
unfold alloc_ceiling in *.
destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC _]]]]].
- left; exact H.
- right. rewrite unsigned_lit in H by lia. lia.
- right. unfold RCTX in H. lia.
- right. destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). unfold alloc_ceiling in RC. lia.
- right. destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). unfold alloc_ceiling in RC. lia.
- right. destruct (rst0_region (fst b) r Hr) as (_ & RC & _). unfold alloc_ceiling in RC. lia.
- right. destruct (rst0_region (fst b) r Hr) as (_ & RC & _). unfold alloc_ceiling in RC. lia.
- right. unfold alloc_ceiling in FC. lia.
Qed.

#[using="st m MR ER"] Lemma rmalloc_fp_image_ER stE mE lo sp a :
rmrep stE mE -> rmalloc_fp st0 stE lo sp a -> alloc_ceiling <= lo ->
0x10000 <= a < 0x645000 -> RCTX <= a < RCTX + 928 \/ 0x622dbc <= a < 0x622dc0.
Proof.
intros (WF2 & _) H CLO HA. pose proof WF2 as (_ & WR2 & _). pose proof MR as ((RS1 & _) & _).
unfold alloc_ceiling in *.
destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC FR]]]]].
- exfalso. lia.
- right. rewrite unsigned_lit in H by lia. lia.
- left. exact H.
- exfalso. destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4). pose proof (lr_lo_ge r). lia.
- exfalso. destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4). pose proof (lr_lo_ge r). lia.
- exfalso. destruct (rst0_region (fst b) r Hr) as (_ & _ & W1 & W2 & W3 & W4). lia.
- exfalso. destruct (rst0_region (fst b) r Hr) as (_ & _ & W1 & W2 & W3 & W4). lia.
- exfalso. pose proof (rfresh_image st0 a (conj FC FR) ltac:(rewrite <- (mrel_reserved _ _ (er_mrel _ _ ER)); exact RS1)). lia.
Qed.

#[using="st m MR ER"] Lemma rauxv_ok_malloc_fp_ER stE mE lo sp m1 m' B :
rmrep stE mE -> rauxv_ok m1 B -> rpres_except (rmalloc_fp st0 stE lo sp) m1 m' ->
alloc_ceiling <= lo -> sp <= B -> rauxv_ok m' B.
Proof.
intros; constructor; exact I.
Qed.

#[using="st m MR ER"] Lemma rframe_keep_ER stE mE lo sp m1 m' A cs :
rmrep stE mE -> rpres_except (rmalloc_fp st0 stE lo sp) m1 m' -> rw_cells rsegs m1 A cs ->
sp <= A -> alloc_ceiling <= A -> rw_cells rsegs m' A cs.
Proof.
intros MRE PE H HA HC. eapply rpres_except_rw_cells; [exact PE| exact H|].
intros a Ha Hfp. destruct (rmalloc_fp_cases_ER stE mE lo sp a MRE Hfp); lia.
Qed.
End FPER.

End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnOf Qn9M Qkaz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w QDUx.Mq0 Q9Ay.Mq3 Q9Ay.Mq4 Q9Ay.Mq5 Q9Ay.Mq6 Q9Ay.Mq7 Q9Ay.Mq8 QyjG QJE4.Mq3.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq1 Q98Z.Mq2 QkLq.Mq0 QkLq.Mq1 QnOf.Mq0 QdZ1.Mq3 Qv4L.Mqa QQbX.Mq3 Qn9M.Mq0 Qv4L.Mq8 Qi8L.Mq4 QdZ1.Mq2 QQbX.Mq2 Qv4L.Mq0 QnkH.Mq2 QnkH.Mqb.
Import QmBS.Mq1 Qlfl.Mq3 Qkaz.Mq7.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rta_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
lo <= a < sp
\/ RCTX <= a < RCTX + 928
\/ (exists q, meta_slot st q /\ conc st q <= a < conc st q + 40)
\/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 9).

#[using="Type"] Lemma rta_fp_stack st lo sp a : lo <= a < sp -> rta_fp st lo sp a. Proof. intros; left; assumption. Qed.
#[using="Type"] Lemma rta_fp_ctx st lo sp a : RCTX <= a < RCTX + 928 -> rta_fp st lo sp a. Proof. intros; right; left; assumption. Qed.
#[using="Type"] Lemma rta_fp_meta st lo sp a q : meta_slot st q -> conc st q <= a < conc st q + 40 -> rta_fp st lo sp a.
Proof. intros; do 2 right; left. exists q; auto. Qed.
#[using="Type"] Lemma rta_fp_grp st lo sp a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 9 -> rta_fp st lo sp a.
Proof. intros; do 3 right. exists b, gh; auto. Qed.

Section PHASE.
Context {R : Type}.
Variables (K : mstate -> Z -> QUZl.M R) (bail : QUZl.M R).
Variables (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (st : mstate) (m : mem) (sc lo : Z).

Variables (ra sp gp tp t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Hypothesis TAF : taf st sc.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 144.
Let spv := bv_unsigned sp.
Let RR (t0 t1 a0 a1' a2 a3 a4 a5 a6 a7 : word) :=
rt1_regs sc ra (Z_to_bv 64 (spv + -144)) gp tp t0 t1 t2 s1 a0 a1' a2 a3 a4 a5 a6 a7 a1 s3 s8 s9 s10 s11 t3 t4 t5 t6.
Let FRM (junk : list byte) := rta_frame junk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra.

Hypothesis HK1 : forall stX g3 msk k m' (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word),
ta_rel sc st stX -> active stX sc = Some g3 -> gmf st sc g3 ->
msk = m_avail (get_meta_rec stX g3) -> 0 < msk < 2^32 -> lowbit msk = 2 ^ k -> 0 <= k < 32 ->
rmrep (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) m' -> mem_inv rsegs m' -> stk rsegs m' lo spv ->
rpres_except (rta_fp st lo spv) m m' ->
rimplT o (K (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) (lowbit msk)) s Q
(MS (mkR ra sp gp tp t0' t1' t2 s0 s1 (wz k) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)).

#[using="CLO LO HK1"] Lemma rfin_block : forall stX g3 msk mZ (t0 t1 a2 a3 a4 a5 a6 a7 : word) (junk : list byte),
ta_rel sc st stX -> active stX sc = Some g3 -> gmf st sc g3 ->
msk = m_avail (get_meta_rec stX g3) -> 0 < msk < 2^32 ->
rmrep stX mZ -> mem_inv rsegs mZ -> rw_cells rsegs mZ (spv + -144) (FRM junk) -> stk rsegs mZ lo (spv + -144) ->
rpres_except (rta_fp st lo spv) m mZ ->
rimplT o (ta_fin stX g3 msk K) s Q
(MS (RR t0 t1 (Z_to_bv 64 (conc st g3)) (wz (sxv msk)) a2 a3 a4 a5 a6 a7) F (Z_to_bv 64 0xceb40) fc None mZ (seg_rom rsegs)).
Proof.
intros until junk. intros TR HA GM HM MR0 MRZ MIZ FRZ STZ PEZ.
destruct (gmf_geom st stX sc g3 TR GM) as (MSZ & RAZ & RFZ & MWZ & EM & ELI & ESC & EFB & ECONC).
pose proof (rmeta_slot_bounds st m g3) as GB0.
pose proof (rmeta_slot_bounds stX mZ g3 MRZ MSZ) as (Gpos & GC & GI & _ & _).
destruct (lowbit_facts msk ltac:(lia)) as (k & Hk & LB).
unfold ta_fin. riprefixT. unfold RR, rt1_regs.
eapply evt_mono.
{ eapply (rfin_walk stX mZ g3 msk lo MRZ MSZ ltac:(lia) CLO); [| exact FRZ| exact STZ| unfold spv; lia| exact MIZ].
rewrite unsigned_lit by lia. symmetry; exact ECONC. }
cbv beta. intros ms' (a1' & a2' & a3' & m' & k' & Hk' & LB' & -> & MU & WM & MI' & ST' & MR').
assert (k' = k) by (rewrite LB in LB'; apply Z.pow_inj_r in LB'; lia). subst k'.
eapply (HK1 stX g3 msk k m'); try eassumption; try lia.
eapply rpres_except_trans; [exact PEZ|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
cbn [ivs_covered]. split; [|split; [|exact I]].
- intros x Hx. apply rta_fp_stack. unfold spv in *; lia.
- intros x Hx. eapply rta_fp_meta; [exact (gmf_slot _ _ _ GM)|]. rewrite <- ECONC. lia.
Qed.

#[using="TAF SC CLO LO HK1"] Lemma ravz_block : forall (pc : Z) stZ g3 mZ (t0 t1 a1' a2 a3 a4 a5 a6 a7 : word) (junk : list byte),
(pc = 0xceabc \/ pc = 0xceac8) ->
ta_rel sc st stZ -> active stZ sc = Some g3 -> gmf st sc g3 ->
rmrep stZ mZ -> mem_inv rsegs mZ -> rw_cells rsegs mZ (spv + -144) (FRM junk) -> stk rsegs mZ lo (spv + -144) ->
rpres_except (rta_fp st lo spv) m mZ ->
rimplT o (ta_avz K bail stZ g3) s Q
(MS (RR t0 t1 (Z_to_bv 64 (conc st g3)) a1' a2 a3 a4 a5 a6 a7) F (Z_to_bv 64 pc) fc None mZ (seg_rom rsegs)).
Proof.
intros until junk. intros PC TR HA GM MRZ MIZ FRZ STZ PEZ.
destruct (gmf_geom st stZ sc g3 TR GM) as (MSZ & RAZ & RFZ & MWZ & EM & ELI & ESC & EFB & ECONC).
pose proof (rmeta_slot_bounds stZ mZ g3 MRZ MSZ) as (Gpos & GC & GI & _ & _).
destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & Hgh & GMg & AIR & SC0 & UNK).
destruct (proj2 (tr_groups _ _ _ TR b) (ex_intro _ gh Hgh)) as [gh1 Hgh1].
destruct (tr_gmeta _ _ _ TR b gh1 Hgh1) as (gh' & Hgh' & GM1 & AI1). rewrite Hgh in Hgh'. inversion Hgh'; subst gh'.
pose proof (gmf_mw _ _ _ GM) as (LI0 & _ & _ & _).
assert (AI1R : 0 <= g_active_idx gh1 <= 31) by (destruct AI1 as [?|[? ?]]; lia).
unfold ta_avz, activate_group.
destruct (m_avail (get_meta_rec stZ g3) =? 0) eqn:AV0; [|unfold guard; apply rimplT_undef].
apply Z.eqb_eq in AV0. unfold guard at 1. cbv beta.
rewrite EM, Hmem. cbn [default].
replace (group_active_idx stZ b) with (g_active_idx gh1).
2:{ unfold group_active_idx, get_group. rewrite Hgh1. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity. }
set (act := mask_upto (g_active_idx gh1)). set (f := m_freed (get_meta_rec stZ g3)).
destruct (Z.land f act =? 0) eqn:MZ; unfold guard; cbn [negb]; [apply rimplT_undef|].
apply Z.eqb_neq in MZ.
rewrite get_meta_rec_upd_same. cbn [m_sizeclass m_set_avail m_set_freed].
assert (EMb : m_mem (get_meta_rec stZ g3) = Some b) by (rewrite EM; exact Hmem).
assert (HG : bv_unsigned (Z_to_bv 64 (conc st g3)) = conc stZ g3) by (rewrite unsigned_lit by lia; symmetry; exact ECONC).

unfold RR.
eapply (rimplT_evt o _ _ _ (fun ms' => exists a1x : word, ms' = MS (rt1_regs sc ra (Z_to_bv 64 (spv + -144)) gp tp t0 t1 t2 s1 (Z_to_bv 64 (conc st g3)) a1x a2 a3 a4 a5 a6 a7 a1 s3 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xceac8) fc None mZ (seg_rom rsegs))).
{ destruct PC as [-> | ->].
- eapply evt_mono. { eapply (ravz_pre_walk stZ mZ g3 sc MRZ MSZ AV0); [exact HG| exact MIZ]. } cbv beta. intros ms' ->. eexists. reflexivity.
- apply evt_done. eexists. reflexivity. }
intros ms0 [a1x ->].
riprefixT. eapply evt_mono.
{ eapply (ravz_walk stZ mZ g3 b gh1 sc MRZ MSZ AV0 EMb Hgh1 AI1R RFZ MWZ MZ); [| exact SC| exact HG| exact MIZ].
intros i. pose proof (taf_bnc _ _ TAF i) as B0. pose proof (tr_bounces _ _ _ TR i ltac:(lia)). lia. }
cbv beta. intros ms' (a2' & a3' & a4' & a5' & a6' & a7' & m5 & -> & MU & WM & MI5 & MR5).
set (st4 := upd_meta g3 (fun r : meta => m_set_avail (Z.land f act) (m_set_freed (Z.ldiff f act) r)) stZ) in *.
set (st5 := decay_bounces (m_sizeclass (get_meta_rec stZ g3)) st4) in *.
assert (TR4 : ta_rel sc st st4).
{ eapply ta_rel_trans; [exact TR|]. unfold st4. rewrite upd_meta_put. apply ta_rel_put_meta.
- repeat split; reflexivity.
- cbn [m_avail m_freed m_set_avail m_set_freed]. intros i Hi Hb. fold f.
apply orb_prop in Hb. rewrite AV0, Z.bits_0. cbn [orb].
destruct Hb as [Hb|Hb]; [rewrite Z.land_spec in Hb| rewrite Z.ldiff_spec in Hb]; apply andb_prop in Hb; destruct Hb as [Hb _]; exact Hb.
- cbn [m_avail m_freed m_set_avail m_set_freed]. fold f. intros _ Hf.
pose proof (land_upper f act ltac:(lia) ltac:(unfold act, mask_upto; pose proof (Z.pow_pos_nonneg 2 (g_active_idx gh1 + 1)); lia)).
pose proof (ldiff_le f act ltac:(lia) ltac:(unfold act, mask_upto; pose proof (Z.pow_pos_nonneg 2 (g_active_idx gh1 + 1)); lia)).
pose proof (Z.ldiff_nonneg f act). lia. }
assert (TR5 : ta_rel sc st st5).
{ eapply ta_rel_trans; [exact TR4|]. unfold st5. apply ta_rel_decay.
pose proof (taf_bnc _ _ TAF (m_sizeclass (get_meta_rec stZ g3) - 7)). pose proof (tr_bounces _ _ _ TR4 (m_sizeclass (get_meta_rec stZ g3) - 7) ltac:(lia)). lia. }
assert (FR5 : rw_cells rsegs m5 (spv + -144) (FRM junk)).
{ eapply rw_cells_transport; [exact FRZ| exact MU| exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia. }
assert (ST5 : stk rsegs m5 lo (spv + -144)).
{ eapply stk_transport_disjoint; [exact STZ| exact MU| exact WM|]. apply disjoint_high; [|lia].
intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia. }
eapply (rfin_block st5 g3 (Z.land f act) m5 t0 t1 a2' a3' a4' a5' a6' a7' junk);
[exact TR5| | exact GM| | | exact MR5| exact MI5| exact FR5| exact ST5|].
- unfold st5. rewrite active_decay. unfold st4. rewrite active_upd_meta. exact HA.
- unfold st5. rewrite rec_decay. unfold st4. rewrite get_meta_rec_upd_same. reflexivity.
- pose proof (land_upper f act ltac:(lia) ltac:(unfold act, mask_upto; pose proof (Z.pow_pos_nonneg 2 (g_active_idx gh1 + 1)); lia)). lia.
- eapply rpres_except_trans; [exact PEZ|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
cbn [ivs_covered]. split; [|split; [|exact I]].
+ intros x Hx. eapply rta_fp_meta; [exact (gmf_slot _ _ _ GM)|]. rewrite <- ECONC. lia.
+ intros x Hx. apply rta_fp_ctx. unfold RCTX in *. lia.
Qed.

#[using="TAF SC CLO LO HK1"] Lemma ract_block : forall stY g2 msk mY (t0 t1 a1' a2 a5 a6 a7 : word) (junk : list byte),
ta_rel sc st stY -> active stY sc = Some g2 -> gmf st sc g2 ->
msk = m_freed (get_meta_rec stY g2) ->
(forall mn, m_next (get_meta_rec stY g2) = Some mn -> gmf st sc mn) ->
m_next (get_meta_rec stY g2) <> None ->
rmrep stY mY -> mem_inv rsegs mY -> rw_cells rsegs mY (spv + -144) (FRM junk) -> stk rsegs mY lo (spv + -144) ->
rpres_except (rta_fp st lo spv) m mY ->
rimplT o (ta_act sc K bail stY g2 msk) s Q
(MS (RR t0 t1 (Z_to_bv 64 (conc st g2)) a1' a2 (wz (sxv msk)) (Z_to_bv 64 2) a5 a6 a7) F (Z_to_bv 64 0xcea94) fc None mY (seg_rom rsegs)).
Proof.
intros until junk. intros TR HA GM HM GN NN MRY MIY FRY STY PEY.
destruct (gmf_geom st stY sc g2 TR GM) as (MSY & RAY & RFY & MWY & EM & ELI & ESC & EFB & ECONC).
pose proof (rmeta_slot_bounds stY mY g2 MRY MSY) as (Gpos & GC & GI & _ & _).
destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & Hgh & GMg & AIR & SC0 & UNK).
destruct (proj2 (tr_groups _ _ _ TR b) (ex_intro _ gh Hgh)) as [gh1 Hgh1].
destruct (tr_gmeta _ _ _ TR b gh1 Hgh1) as (gh' & Hgh' & GM1 & AI1). rewrite Hgh in Hgh'. inversion Hgh'; subst gh'.
pose proof (gmf_mw _ _ _ GM) as (LI0 & _ & SCR0 & _).
assert (AI1R : 0 <= g_active_idx gh1 <= 31) by (destruct AI1 as [?|[? ?]]; lia).
assert (EMb : m_mem (get_meta_rec stY g2) = Some b) by (rewrite EM; exact Hmem).
assert (MSKR : 0 <= msk < 2^32) by (rewrite HM; exact RFY).
assert (HG : bv_unsigned (Z_to_bv 64 (conc st g2)) = conc stY g2) by (rewrite unsigned_lit by lia; symmetry; exact ECONC).
unfold ta_act. rewrite EMb. cbn [default].
replace (group_active_idx stY b) with (g_active_idx gh1).
2:{ unfold group_active_idx, get_group. rewrite Hgh1. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity. }
unfold RR.
destruct (Z.land msk (mask_upto (g_active_idx gh1)) =? 0) eqn:ZR.
-
apply Z.eqb_eq in ZR.
destruct (m_next (get_meta_rec stY g2)) as [mn|] eqn:GNY; [|exfalso; apply NN; reflexivity].
cbn [optr_eqb]. destruct (aptr_eqb mn g2) eqn:EQ; cbn [negb].
+
apply aptr_eqb_eq in EQ. subst mn.
destruct (Z.eq_dec (m_sizeclass (get_meta_rec st g2)) 0) as [SCZ|SCNZ].
*
assert (AIE : g_active_idx gh1 = m_last_idx (get_meta_rec st g2)).
{ destruct AI1 as [E|[_ P]]; [rewrite E; apply SC0; exact SCZ| exfalso; exact (P g2 GMg SCZ)]. }
assert (MZ : msk = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0.
destruct (Z.testbit msk i) eqn:Ti; [|reflexivity]. exfalso.
assert (IL : i <= m_last_idx (get_meta_rec st g2)).
{ pose proof (tr_bits _ _ _ TR g2 i Hi) as TB. rewrite <- HM, Ti in TB. rewrite orb_true_r in TB. specialize (TB eq_refl).
apply orb_prop in TB. destruct TB as [TB|TB]; [exact (gmf_abits _ _ _ GM i Hi TB)| exact (gmf_fbits _ _ _ GM i Hi TB)]. }
assert (TB2 : Z.testbit (Z.land msk (mask_upto (g_active_idx gh1))) i = true).
{ rewrite Z.land_spec, Ti. unfold mask_upto. replace (2 ^ (g_active_idx gh1 + 1) - 1) with (Z.ones (g_active_idx gh1 + 1)) by (rewrite Z.ones_equiv; lia).
rewrite Z.testbit_ones_nonneg by lia. cbn [andb]. apply Z.ltb_lt. lia. }
rewrite ZR, Z.bits_0 in TB2. discriminate. }

cbv zeta iota beta. unfold ta_avz, activate_group. rewrite rec_set_gai.
destruct (m_avail (get_meta_rec stY g2) =? 0); unfold guard; [|apply rimplT_undef].
cbv beta. rewrite <- HM, MZ, Z.land_0_l. cbn [Z.eqb negb]. apply rimplT_undef.
*
destruct (m_avail (get_meta_rec stY g2) =? 0) eqn:AV0.
2:{ cbv zeta iota beta. unfold ta_avz, activate_group. rewrite rec_set_gai, AV0. unfold guard. apply rimplT_undef. }
apply Z.eqb_eq in AV0.
assert (SCY : 1 <= m_sizeclass (get_meta_rec stY g2) < 48) by (rewrite ESC; pose proof (gmf_sc48 _ _ _ GM); lia).
rewrite <- ECONC. riprefixT. eapply evt_mono.
{ eapply (ract_span_walk stY mY g2 b gh1 sc msk MRY MSY EMb Hgh1 AI1R); [exact ZR| exact GNY| exact MWY| exact SCY| | rewrite GM1; exact GMg| exact AV0| exact MIY].
intros o' Ho'. rewrite (tr_get_shadow _ _ _ _ TR). apply UNK. exact Ho'. }
cbv beta. intros ms' (t0' & t1' & a1'' & a2' & a3' & a4' & a5' & a6' & a7' & m5 & -> & MU & WM & MI5 & MR5).
cbv zeta iota beta.
match goal with |- rimplT _ (ta_avz _ _ ?st3 _) _ _ _ => set (stG := st3) in * end.
assert (TRG : ta_rel sc st stG).
{ eapply ta_rel_trans; [exact TR|]. apply ta_rel_set_gai.
- apply land31_range.
- intros h g' Hh Hg'. rewrite Hgh1 in Hh. inversion Hh; subst h. rewrite GM1 in Hg'. rewrite GMg in Hg'. inversion Hg'; subst g'. lia. }
rewrite (tr_conc _ _ _ g2 TR).
eapply (ravz_block 0xceac8 stG g2 m5); [right; reflexivity| exact TRG| | exact GM| exact MR5| exact MI5| | |].
-- unfold stG. rewrite active_set_gai. exact HA.
-- eapply rw_cells_transport; [exact FRY| exact MU| exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
pose proof (rgroup_bounds stY mY b gh1 MRY Hgh1) as (B0 & BC & _).
intros lo' hi' [E|[]]; inversion E; subst; unfold alloc_ceiling in *; lia.
-- eapply stk_transport_disjoint; [exact STY| exact MU| exact WM|]. apply disjoint_high; [|lia].
pose proof (rgroup_bounds stY mY b gh1 MRY Hgh1) as (B0 & BC & _).
intros lo' hi' [E|[]]; inversion E; subst; unfold alloc_ceiling in *; lia.
-- eapply rpres_except_trans; [exact PEY|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
cbn [ivs_covered]. split; [|exact I]. intros x Hx. eapply (rta_fp_grp st lo spv x b gh Hgh). rewrite <- (tr_conc _ _ _ b TR). lia.
+
assert (NE : mn <> g2) by (intros ->; rewrite (proj2 (aptr_eqb_eq g2 g2) eq_refl) in EQ; discriminate).
pose proof (GN mn eq_refl) as GMn.
destruct (gmf_geom st stY sc mn TR GMn) as (MSn & _ & _ & _ & _ & _ & _ & _ & ECONCn).
rewrite <- ECONC. riprefixT. eapply evt_mono.
{ eapply (ract_next_walk stY mY g2 b gh1 sc msk MRY MSY SC EMb Hgh1 AI1R); [exact ZR| exact GNY| exact NE| exact MSn| exact MIY]. }
cbv beta. intros ms' (a1'' & a2' & a3' & a4' & m5 & -> & MU & WM & MI5 & MR5).
assert (TRN : ta_rel sc st (set_active sc (Some mn) stY)) by (eapply ta_rel_trans; [exact TR| apply ta_rel_set_active]).
rewrite ECONCn.
eapply (ravz_block 0xceabc (set_active sc (Some mn) stY) mn m5); [left; reflexivity| exact TRN| | exact GMn| exact MR5| exact MI5| | |].
-- rewrite active_set_active, Z.eqb_refl. reflexivity.
-- eapply rw_cells_transport; [exact FRY| exact MU| exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia.
-- eapply stk_transport_disjoint; [exact STY| exact MU| exact WM|]. apply disjoint_high; [|lia].
intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia.
-- eapply rpres_except_trans; [exact PEY|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rta_fp_ctx. unfold RCTX in *. lia.
-
apply Z.eqb_neq in ZR.
rewrite <- ECONC. riprefixT. eapply evt_mono.
{ eapply (ract_skip_walk stY mY g2 b gh1 sc msk MRY MSY EMb Hgh1 AI1R MSKR); [exact ZR| exact MIY]. }
cbv beta. intros ms' (a1'' & a2' & a3' & a4' & ->). rewrite ECONC.
eapply (ravz_block 0xceabc stY g2 mY); [left; reflexivity| ..]; eassumption.
Qed.

Definition rnclosed (stX : mstate) (P : aptr -> Prop) : Prop :=
forall q, P q -> gmf st sc q /\ exists t, m_next (get_meta_rec stX q) = Some t /\ P t.

#[using="TAF SC CLO LO HK1"] Lemma rm_block : forall stX g1 mX (P : aptr -> Prop) (t0 t1 a1' a2 a3 a4 a5 a6 a7 : word) (junk : list byte),
ta_rel sc st stX -> active stX sc = Some g1 -> rnclosed stX P -> P g1 ->
rmrep stX mX -> mem_inv rsegs mX -> rw_cells rsegs mX (spv + -144) (FRM junk) -> stk rsegs mX lo (spv + -144) ->
rpres_except (rta_fp st lo spv) m mX ->
rimplT o (ta_m sc K bail stX g1) s Q
(MS (RR t0 t1 (Z_to_bv 64 (conc st g1)) a1' a2 a3 a4 a5 a6 a7) F (Z_to_bv 64 0xcea68) fc None mX (seg_rom rsegs)).
Proof.
intros until junk. intros TR HA NC P1 MRX MIX FRX STX PEX.
destruct (NC g1 P1) as (GM & mn & GN1 & Pmn).
destruct (gmf_geom st stX sc g1 TR GM) as (MSX & RAX & RFX & MWX & EM & ELI & ESC & EFB & ECONC).
pose proof (rmeta_slot_bounds stX mX g1 MRX MSX) as (Gpos & GC & GI & _ & _).
destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & Hgh & GMg & AIR & SC0 & UNK).
pose proof (gmf_mw _ _ _ GM) as (LI0 & FB0 & SCR0 & _).
unfold ta_m, RR.
set (f := m_freed (get_meta_rec stX g1)).
destruct ((f =? mask_upto (m_last_idx (get_meta_rec stX g1))) && negb (m_freeable (get_meta_rec stX g1) =? 0)) eqn:FSK.
-
pose proof FSK as FSK'. apply andb_prop in FSK'. destruct FSK' as [FE FB]. apply Z.eqb_eq in FE. apply Bool.negb_true_iff in FB. apply Z.eqb_neq in FB.
rewrite GN1.
destruct (NC mn Pmn) as (GMn & mn2 & GN2 & Pmn2).
destruct (gmf_geom st stX sc mn TR GMn) as (MSn & RAn & RFn & MWn & EMn & _ & _ & _ & ECONCn).
rewrite <- ECONC. riprefixT. eapply evt_mono.
{ eapply (rm_skip_walk stX mX g1 sc MRX MSX SC RFX MWX); [exact FSK| exact GN1| exact MSn| exact RFn| exact MIX]. }
cbv beta. intros ms' (a1'' & a2' & m5 & -> & MU & WM & MI5 & MR5).
assert (TRN : ta_rel sc st (set_active sc (Some mn) stX)) by (eapply ta_rel_trans; [exact TR| apply ta_rel_set_active]).
rewrite ECONCn.
eapply (ract_block (set_active sc (Some mn) stX) mn (m_freed (get_meta_rec stX mn)) m5); try eassumption.
+ rewrite active_set_active, Z.eqb_refl. reflexivity.
+ reflexivity.
+ intros q Hq. rewrite rec_set_active in Hq. rewrite GN2 in Hq. inversion Hq; subst q. exact (proj1 (NC _ Pmn2)).
+ rewrite rec_set_active, GN2. discriminate.
+ eapply rw_cells_transport; [exact FRX| exact MU| exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia.
+ eapply stk_transport_disjoint; [exact STX| exact MU| exact WM|]. apply disjoint_high; [|lia].
intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia.
+ eapply rpres_except_trans; [exact PEX|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rta_fp_ctx. unfold RCTX in *. lia.
-
rewrite <- ECONC. riprefixT. eapply evt_mono.
{ eapply (rm_act_walk stX mX g1 sc MRX MSX RFX MWX); [exact FSK| exact MIX]. }
cbv beta. intros ms' (a1'' & a2' & ->). rewrite ECONC.
eapply (ract_block stX g1 f mX); try eassumption.
+ reflexivity.
+ intros q Hq. rewrite GN1 in Hq. inversion Hq; subst q. exact (proj1 (NC _ Pmn)).
+ rewrite GN1. discriminate.
Qed.

#[using="TAF SC CLO LO HK1"] Lemma rta_phase : forall (t0 t1 a0 a2 a3 a4 a5 a6 a7 : word),
a0 = Z_to_bv 64 sc ->
rmrep st m -> mem_inv rsegs m -> stk rsegs m lo spv ->
(forall st1 m' (t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' : word) (junk : list byte),
ta_fail sc st st1 -> ta_rel sc st st1 -> active st1 sc = None ->
rmrep st1 m' -> mem_inv rsegs m' -> rw_cells rsegs m' (spv + -144) (FRM junk) -> stk rsegs m' lo (spv + -144) ->
rpres_except (rta_fp st lo spv) m m' ->
rimplT o (K st1 0) s Q (MS (RR t0' t1' a0' a1' a2' a3' a4' a5' a6' a7') F (Z_to_bv 64 0xceb80) fc None m' (seg_rom rsegs))) ->
rimplT o (try_avail sc st K bail) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom rsegs)).
Proof.
intros until a7. intros A0 MR MI ST HK0.
assert (AMS : forall g, active st sc = Some g -> meta_slot st g) by (intros g Hg; exact (gmf_slot _ _ _ (proj1 (taf_head _ _ TAF g Hg)))).
riprefixT. eapply evt_mono.
{ eapply (ras_entry_walk st m sc lo MR SC CLO AMS); [exact A0| exact ST| exact LO| exact MI]. }
cbv beta. intros ms' (a1x & m1 & junk & -> & FR1 & ST1 & MU1 & WM1 & MI1 & MR1).
assert (PE1 : rpres_except (rta_fp st lo spv) m m1).
{ eapply rpres_except_of_munch_cov; [exact MU1| exact WM1|]. cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rta_fp_stack. unfold spv; lia. }
clear MU1 WM1.
rewrite (try_avail_eq sc K bail st).
destruct (active st sc) as [g|] eqn:HA.
2:{
eapply (HK0 st m1); [| apply ta_rel_refl| exact HA| exact MR1| exact MI1| exact FR1| exact ST1| exact PE1].
unfold ta_fail, try_avail. rewrite HA. reflexivity. }
destruct (taf_head _ _ TAF g HA) as [GM GSC].
pose proof (gmf_slot _ _ _ GM) as MSg. pose proof (gmf_avail _ _ _ GM) as RAg. pose proof (gmf_freed _ _ _ GM) as RFg.
pose proof (rmeta_slot_bounds st m1 g MR1 MSg) as (Gpos & GC & GI & _ & _).
unfold pw. cbn [oconc]. unfold wz.
destruct (m_avail (get_meta_rec st g) =? 0) eqn:AV; cbn [negb].
2:{
apply Z.eqb_neq in AV.
riprefixT. eapply evt_mono.
{ eapply (rt1_fin_walk st m1 g sc MR1 MSg RAg); [exact AV| exact MI1]. }
cbv beta. intros ms' ->.
eapply (rfin_block st g (m_avail (get_meta_rec st g)) m1); [apply ta_rel_refl| exact HA| exact GM| reflexivity| lia| exact MR1| exact MI1| exact FR1| exact ST1| exact PE1]. }
apply Z.eqb_eq in AV.
destruct (gmf_links _ _ _ GM) as (nx & pv & GN & GP).
destruct (taf_next _ _ TAF g nx GM GN) as (GMn & SCn & PRn).
destruct (taf_prev _ _ TAF g pv GM GP) as (GMp & NXp).
destruct (m_freed (get_meta_rec st g) =? 0) eqn:FZ.
-
apply Z.eqb_eq in FZ.
riprefixT. eapply evt_mono.
{ eapply (rt1_deq_walk st m1 g sc MR1 MSg); [exact AV| exact FZ| exact MI1]. }
cbv beta. intros ms' ->.
destruct (decide (nx = g)) as [->|NEn].
+
rewrite (dequeue_self_eq sc g st GN).
replace (active (put_meta g (clr (get_meta_rec st g)) (set_active sc None st)) sc) with (@None aptr)
by (change (active (put_meta g (clr (get_meta_rec st g)) (set_active sc None st)) sc) with (active (set_active sc None st) sc); rewrite active_set_active, Z.eqb_refl; reflexivity).
cbn [Z.eqb].
riprefixT. eapply evt_mono.
{ eapply (rdeq_self_walk st m1 g sc MR1 MSg SC); [exact GN| exact MI1]. }
cbv beta. intros ms' (m2 & -> & MU & WM & MI2 & MR2).
eapply (HK0 _ m2).
* unfold ta_fail. rewrite (try_avail_eq sc kS bS st), HA, AV, FZ. cbn [Z.eqb negb].
rewrite (dequeue_self_eq sc g st GN).
change (active (put_meta g (clr (get_meta_rec st g)) (set_active sc None st)) sc) with (active (set_active sc None st) sc).
rewrite active_set_active, Z.eqb_refl. reflexivity.
* eapply ta_rel_trans; [apply ta_rel_set_active|]. unfold clr.
replace (get_meta_rec st g) with (get_meta_rec (set_active sc None st) g) by reflexivity. apply ta_rel_put_links.
* change (active (put_meta g (clr (get_meta_rec st g)) (set_active sc None st)) sc) with (active (set_active sc None st) sc).
rewrite active_set_active, Z.eqb_refl. reflexivity.
* exact MR2.
* exact MI2.
* eapply rw_cells_transport; [exact FR1| exact MU| exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia.
* eapply stk_transport_disjoint; [exact ST1| exact MU| exact WM|]. apply disjoint_high; [|lia].
intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia.
* eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
cbn [ivs_covered]. split; [|split; [|exact I]]; intros x Hx; [apply rta_fp_ctx; unfold RCTX in *; lia| eapply rta_fp_meta; [exact MSg| lia]].
+
assert (NEp : pv <> g).
{ intros ->. rewrite NXp in GN. inversion GN. subst nx. apply NEn. reflexivity. }
rewrite (dequeue_other_eq sc g nx pv st GN GP NEn NEp HA). cbv zeta.
match goal with |- context [active ?stq sc] => set (st1 := stq) in * end.
assert (HA1 : active st1 sc = Some nx).
{ unfold st1. unfold active, put_meta, set_metas, set_active, upd_ctx. cbn [s_ctx ctx c_active set_active_map]. apply lookup_insert_eq. }
rewrite HA1.
pose proof (gmf_slot _ _ _ GMn) as MSn. pose proof (gmf_slot _ _ _ GMp) as MSp.
riprefixT. eapply evt_mono.
{ eapply (rdeq_other_walk st m1 g sc MR1 MSg SC HA); [exact GN| exact GP| exact NEn| exact NEp| exact MSn| exact MSp| exact MI1]. }
cbv beta. intros ms' (a1'' & m2 & -> & MU & WM & MI2 & MR2). fold st1 in MR2.
assert (TR1 : ta_rel sc st st1).
{ unfold st1.
lazymatch goal with |- ta_rel _ _ (put_meta _ _ ?sC) =>
lazymatch sC with set_active _ _ ?sB =>
lazymatch sB with put_meta _ _ ?sA =>
apply (ta_rel_trans sc st sC); [apply (ta_rel_trans sc st sB); [apply (ta_rel_trans sc st sA); [apply ta_rel_put_next| apply ta_rel_put_prev] | apply ta_rel_set_active] |];
unfold clr; replace (get_meta_rec st g) with (get_meta_rec sC g); [apply ta_rel_put_links|]
end end end.
rewrite rec_set_active. rewrite (get_meta_rec_put_other _ nx) by (intros E; apply NEn; symmetry; exact E).
rewrite (get_meta_rec_put_other _ pv) by (intros E; apply NEp; symmetry; exact E). reflexivity. }

assert (REC1 : forall q, q <> g -> get_meta_rec st1 q =
if aptr_eqb q nx then m_set_prev (Some pv) (if aptr_eqb nx pv then m_set_next (Some nx) (get_meta_rec st pv) else get_meta_rec st nx)
else if aptr_eqb q pv then m_set_next (Some nx) (get_meta_rec st pv) else get_meta_rec st q).
{ intros q Hq. unfold st1. rewrite (get_meta_rec_put_other _ g) by exact Hq. rewrite rec_set_active.
rewrite get_meta_rec_put. destruct (aptr_eqb q nx) eqn:E1.
- apply aptr_eqb_eq in E1. subst q. f_equal. rewrite get_meta_rec_put. destruct (aptr_eqb nx pv) eqn:E2; [apply aptr_eqb_eq in E2; subst; reflexivity| reflexivity].
- rewrite get_meta_rec_put. reflexivity. }
eapply (rm_block st1 nx m2 (fun q => gmf st sc q /\ q <> g)); [exact TR1| exact HA1| | split; [exact GMn| exact NEn] | exact MR2| exact MI2| | |].
* intros q [GMq NEq]. split; [exact GMq|]. rewrite (REC1 q NEq).
destruct (gmf_links _ _ _ GMq) as (qn & qp & QN & QP). destruct (taf_next _ _ TAF q qn GMq QN) as (GMqn & _ & PRqn).
destruct (aptr_eqb q nx) eqn:E1.
-- apply aptr_eqb_eq in E1. subst q. cbn [m_next m_set_prev].
destruct (aptr_eqb nx pv) eqn:E2.
++ exists nx. cbn. split; [reflexivity|]. split; [exact GMn| exact NEn].
++ exists qn. split; [exact QN|]. split; [exact GMqn|]. intros ->.
rewrite PRqn in GP. inversion GP. subst pv. rewrite (proj2 (aptr_eqb_eq nx nx) eq_refl) in E2. discriminate.
-- destruct (aptr_eqb q pv) eqn:E2.
++ apply aptr_eqb_eq in E2. subst q. cbn. exists nx. split; [reflexivity|]. split; [exact GMn| exact NEn].
++ exists qn. split; [exact QN|]. split; [exact GMqn|]. intros ->. rewrite PRqn in GP. inversion GP. subst pv.
rewrite (proj2 (aptr_eqb_eq q q) eq_refl) in E2. discriminate.
* eapply rw_cells_transport; [exact FR1| exact MU| exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
pose proof (rmeta_slot_bounds st m1 nx MR1 MSn) as (? & ? & _). pose proof (rmeta_slot_bounds st m1 pv MR1 MSp) as (? & ? & _).
intros lo' hi' [E|[E|[E|[E|[]]]]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia.
* eapply stk_transport_disjoint; [exact ST1| exact MU| exact WM|]. apply disjoint_high; [|lia].
pose proof (rmeta_slot_bounds st m1 nx MR1 MSn) as (? & ? & _). pose proof (rmeta_slot_bounds st m1 pv MR1 MSp) as (? & ? & _).
intros lo' hi' [E|[E|[E|[E|[]]]]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia.
* eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
cbn [ivs_covered]. split; [|split; [|split; [|split; [|exact I]]]]; intros x Hx;
[apply rta_fp_ctx; unfold RCTX in *; lia| eapply rta_fp_meta; [exact MSg| lia]| eapply rta_fp_meta; [exact MSp| lia]| eapply rta_fp_meta; [exact MSn| lia]].
-
apply Z.eqb_neq in FZ. rewrite GN.
riprefixT. eapply evt_mono.
{ eapply (rt1_next_walk st m1 g sc MR1 MSg SC RFg); [exact AV| exact FZ| exact MI1]. }
cbv beta. intros ms' (m2 & -> & MU & WM & MI2 & MR2). rewrite GN in MR2 |- *. unfold pw. cbn [oconc]. unfold wz.
eapply (rm_block (set_active sc (Some nx) st) nx m2 (gmf st sc)); [| | | exact GMn| exact MR2| exact MI2| | |].
+ apply ta_rel_set_active.
+ rewrite active_set_active, Z.eqb_refl. reflexivity.
+ intros q GMq. split; [exact GMq|]. rewrite rec_set_active. destruct (gmf_links _ _ _ GMq) as (qn & qp & QN & QP).
exists qn. split; [exact QN|]. exact (proj1 (taf_next _ _ TAF q qn GMq QN)).
+ eapply rw_cells_transport; [exact FR1| exact MU| exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia.
+ eapply stk_transport_disjoint; [exact ST1| exact MU| exact WM|]. apply disjoint_high; [|lia].
intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia.
+ eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rta_fp_ctx. unfold RCTX in *. lia.
Qed.
End PHASE.

End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeTw Q1BE Q5JI QkAv QvVw QNtS QXzy Q1Yb QFef QW7x Qra5 Q7ap QuEo Quzq QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qfw3_c1.Mq2 QWxq_c1.Mq0 Qc3B.

Import QZAi.Mq1 QZAi QdBa QfYR QfcC Ql2m Ql2m.Mq0.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y QPUx.
Import Q7wb.
Import QeTw Q1BE Q5JI QkAv QvVw QNtS QXzy Q1Yb QQbX.Mq4 QFef QW7x QCwx Qra5 Q7ap QuEo QvBB.Mq2 QnkH.Mqd Qi8L.Mq7 QmBS.Mq5 Quzq Qlfl.Mq5 QnkH.Mqc Qi8L.Mq6 QjhR.
Import QCqH.
Import QBpX.
Import ListNotations. Unset Keyed Unification.
Open Scope bv_scope.

Import Ltac2.Ltac2 Ltac2.Constr.
Set Default Proof Mode "Classic".
Ltac2 rec zt_plain_arith' (t : constr) : bool :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.App h args =>
match Constr.Unsafe.kind h with
| Constr.Unsafe.Constant _ _ =>
if Constr.equal h '@Z.le then true else if Constr.equal h '@Z.lt then true
else if Constr.equal h '@Z.ge then true else if Constr.equal h '@Z.gt then true
else if Constr.equal h '@lt then true else if Constr.equal h '@ge then true
else if Constr.equal h '@gt then true else if Constr.equal h '@N.le then true
else if Constr.equal h '@N.lt then true else if Constr.equal h '@Z.divide then true
else false
| Constr.Unsafe.Ind _ _ =>
if Constr.equal h '@and then (if zt_plain_arith' (Array.get args 0) then zt_plain_arith' (Array.get args 1) else false)
else if Constr.equal h '@eq then true else if Constr.equal h '@le then true
else false
| _ => false
end
| Constr.Unsafe.Ind _ _ => if Constr.equal t 'True then true else Constr.equal t 'False
| _ => false
end.
Ltac2 rec zt_codomain (t : constr) : constr :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.Prod _ b => zt_codomain b
| Constr.Unsafe.LetIn _ _ b => zt_codomain b
| Constr.Unsafe.Cast c _ _ => zt_codomain c
| _ => t
end.
Ltac2 rec zt_head (t : constr) : constr :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.App f _ => zt_head f
| Constr.Unsafe.Cast c _ _ => zt_head c
| _ => t
end.
Ltac2 zt_sort_is_prop (ty : constr) : bool :=
lazy_match! zt_codomain ty with Prop => true | _ => false end.
Ltac2 zt_is_prop_fast (ty : constr) : bool :=
let h := zt_head (zt_codomain ty) in
match Constr.Unsafe.kind h with
| Constr.Unsafe.Constant _ _ => zt_sort_is_prop (Constr.type h)
| Constr.Unsafe.Ind _ _ => zt_sort_is_prop (Constr.type h)
| Constr.Unsafe.Var _ => zt_sort_is_prop (Constr.type h)
| _ => false
end.
Ltac2 zt_is_local' (id : ident) : bool :=
match Env.get [id] with None => true | Some _ => false end.
Ltac2 zt_prune_fast () : unit :=
let hs := Control.hyps () in
let ids := List.map_filter (fun h => let (id, body, ty) := h in
match body with
| Some _ => None
| None => if zt_plain_arith' ty then None
else if Bool.and (zt_is_local' id) (zt_is_prop_fast ty) then Some id else None
end) hs in
match ids with [] => () | _ :: _ => Std.clear ids end.
Ltac zify_prune_fast := ltac2:(Control.enter zt_prune_fast).

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Ltac showt := let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in
idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31.
Ltac showall := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in let x2 := getreg 2%Z in let x1 := getreg 1%Z in
idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31; idtac "sp=" x2; idtac "ra=" x1.
Ltac show_hyp H := let T := type of H in idtac H ":" T.
Ltac dlia := first [lia | match goal with |- ?g => idtac "LIA FAILED:"; idtac g; fail 1 end].
Ltac plia := unfold zlength, got_ssp, ssp_guard in *; lia.

Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.

Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

Lemma land_mask_range : forall a m, (0 <= m)%Z -> (0 <= Z.land a m <= m)%Z.
Proof.
intros a m Hm. split; [apply Z.land_nonneg; right; exact Hm|].
pose proof (Z.sub_land_same_l m a) as E. rewrite (Z.land_comm a m).
assert (0 <= Z.land m (Z.lnot a))%Z by (apply Z.land_nonneg; left; exact Hm). lia.
Qed.

Ltac fix_idx := repeat match goal with
| |- context [Z_to_bv 64 (?A + Z.shiftl ?k 2)] =>
replace (Z_to_bv 64 (A + Z.shiftl k 2)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia)
| |- context [Z_to_bv 64 (Z.shiftl ?k 2 + ?A)] =>
replace (Z_to_bv 64 (Z.shiftl k 2 + A)%Z) with (Z_to_bv 64 (A + 4 * k)%Z) by (rewrite (Z.shiftl_mul_pow2 k 2) by lia; f_equal; lia) end.

Lemma sx32_wval : forall ws i t, wval ws i = t -> (0 <= t < 2^31)%Z -> sx32 (wnth ws i) = Z_to_bv 64 t.
Proof.
intros ws i t Hw Ht. unfold sx32. f_equal. unfold wval in Hw. rewrite swrap32_eq.
pose proof (bv_unsigned_in_range 64 (wnth ws i)) as R.
rewrite <- Hw. rewrite <- Hw in Ht. Z.div_mod_to_equations. lia.
Qed.

Lemma zx32_wval : forall ws i, zx32 (wnth ws i) = Z_to_bv 64 (wval ws i).
Proof. intros. unfold zx32, wval. reflexivity. Qed.

Lemma srlw_small : forall t sh, (0 <= t < 2^31)%Z -> (0 <= sh < 32)%Z ->
bv_swrap 32 (Z.shiftr (bv_wrap 32 t) (sh mod 32)) = Z.shiftr t sh.
Proof.
intros t sh Ht Hsh. rewrite (Z.mod_small sh 32) by lia.
replace (bv_wrap 32 t) with t by (unfold bv_wrap, bv_modulus; symmetry; apply Z.mod_small; cbn; lia).
assert (0 <= Z.shiftr t sh <= t)%Z.
{ split; [apply Z.shiftr_nonneg; lia|]. rewrite Z.shiftr_div_pow2 by lia.
apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|]. assert (1 <= 2 ^ sh)%Z by (change 1%Z with (2^0)%Z; apply Z.pow_le_mono_r; lia). nia. }
apply swrap32_small. lia.
Qed.

Ltac eval_swraps := repeat match goal with |- context [bv_swrap 32 ?e] =>
let v := eval vm_compute in (bv_swrap 32 e) in lazymatch isZcst v with true => change (bv_swrap 32 e) with v end end.

Lemma divu_lit : forall a b, (0 <= a < 2^64)%Z -> (0 < b < 2^64)%Z ->
mul_div M_DIVU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a / b).
Proof.
intros a b Ha Hb. unfold mul_div. rewrite (unsigned_lit b) by lia.
replace (b =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
assert (R : (0 <= a / b <= a)%Z). { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
apply bv_eq. rewrite bv_divu_unsigned. rewrite !unsigned_lit by lia. reflexivity.
Qed.
Lemma remu_lit : forall a b, (0 <= a < 2^64)%Z -> (0 < b < 2^64)%Z ->
mul_div M_REMU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a mod b).
Proof.
intros a b Ha Hb. unfold mul_div. rewrite (unsigned_lit b) by lia.
replace (b =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
pose proof (Z.mod_pos_bound a b ltac:(lia)) as R.
apply bv_eq. rewrite bv_modu_unsigned. rewrite !unsigned_lit by lia. reflexivity.
Qed.

Section DivW.
Local Open Scope Z_scope.
#[using="Type"] Lemma divw_small : forall v i, (0 <= v < 2^31)%Z -> (0 < i < 2^31)%Z -> v_divw (Z_to_bv 64 v) (Z_to_bv 64 i) = Z_to_bv 64 (v / i)%Z.
Proof.
intros v i Hv Hi. unfold v_divw. rewrite !unsigned_lit by lia.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32)%Z with 4294967296%Z.
rewrite (Z.mod_small i) by lia. destruct (Z.eqb_spec i 0); [lia|]. f_equal.
rewrite (swrap32_small v), (swrap32_small i) by lia. rewrite Z.quot_div_nonneg by lia.
assert (0 <= v / i <= v)%Z by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia|]; nia]).
apply swrap32_small. lia.
Qed.
#[using="Type"] Lemma p10s_range : forall j, 0 <= j <= 7 -> 10 <= znth p10s j <= 100000000 /\ (znth p10s j * (1000000000 / znth p10s j) = 1000000000)%Z.
Proof.
intros j Hj.
assert (H : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia.
destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
match goal with |- context [znth p10s ?j] => let v := eval vm_compute in (znth p10s j) in change (znth p10s j) with v end; (split; [lia | reflexivity]).
Qed.
End DivW.

Definition RATP : Z := 0x625520.
Definition RERRNO : Z := 0x62547c.
Definition ERRNO_LOC : Z := 0xcea68.

Lemma errno_loc_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
mem_inv usegs m ->
evt usegs (fun ms' => exists m', ms' = MS (mkR ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 RERRNO) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [] m m' /\ wmono usegs m m' /\ mem_inv usegs m')
(MS (mkR ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ERRNO_LOC) fc None m (seg_rom usegs)).
Proof.
intros until m. intros MI. unfold ERRNO_LOC, RATP, RERRNO.
zs. zs. zs.
apply evt_done. eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl | exact MI].
Qed.

Section CallE.
Local Open Scope Z_scope.
Definition DS : divtf3_stmt := QXzy.divtf3_spec.
#[using="Type"] Lemma mul_callE : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q al ah bl bh X Y : Z),
stk usegs m (q - 80) q -> mem_inv usegs m -> (4096 <= q < 2^64)%Z ->
al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
evt usegs (call2_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 80 (f128_mul X Y) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1e2c) fc None m (seg_rom usegs)).
Proof. intros until Y. intros ST MI Hq -> -> -> ->. apply multf3_callq; assumption. Qed.
#[using="Type"] Lemma div_callE : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q al ah bl bh X Y : Z),
stk usegs m (q - 112) q -> mem_inv usegs m -> (4096 <= q < 2^64)%Z ->
al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
evt usegs (call2_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 112 (f128_div X Y) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd3078) fc None m (seg_rom usegs)).
Proof. intros until Y. intros ST MI Hq -> -> -> ->. apply (divtf3_callq DS); assumption. Qed.
#[using="Type"] Lemma add_callE : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q al ah bl bh X Y : Z),
stk usegs m (q - 48) q -> mem_inv usegs m -> frm0 fc -> (48 <= q < 2^64)%Z ->
al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
evt usegs (calla_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (f128_add X Y) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd2758) fc None m (seg_rom usegs)).
Proof. intros until Y. intros ST MI FRM Hq -> -> -> ->. apply addtf3_callq; assumption. Qed.
#[using="Type"] Lemma sub_callE : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q al ah bl bh X Y : Z),
stk usegs m (q - 48) q -> mem_inv usegs m -> frm0 fc -> (48 <= q < 2^64)%Z ->
al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
evt usegs (calla_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (f128_sub X Y) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd2f60) fc None m (seg_rom usegs)).
Proof. intros until Y. intros ST MI FRM Hq -> -> -> ->. apply subtf3_callq; assumption. Qed.
#[using="Type"] Lemma letf2_callE : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (al ah bl bh X Y : Z),
mem_inv usegs m -> al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
evt usegs (leaf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_le X Y) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1ca8) fc None m (seg_rom usegs)).
Proof. intros until Y. intros MI -> -> -> ->. apply letf2_callv; assumption. Qed.
#[using="Type"] Lemma getf2_callE : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (al ah bl bh X Y : Z),
mem_inv usegs m -> al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
evt usegs (leaf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_ge X Y) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1d70) fc None m (seg_rom usegs)).
Proof.
intros until Y. intros MI -> -> -> ->. eapply evt_mono. { eapply getf2_spec. exact MI. }
intros ms' P. unfold getf2_post in P. unfold leaf1_post. rewrite !ulit_lo64, !ulit_hi64 in P.
change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. change (lo64 Y + 2 ^ 64 * hi64 Y)%Z with (canon Y) in P.
rewrite Q9Ay.f128_ge_canon in P. exact P.
Qed.

#[using="Type"] Lemma scalbn_callE : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (n : Z),
mem_inv usegs m -> frm0 fc -> (-2^31 <= n < 2^31)%Z ->
evt usegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (f15 : word) fc' m',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
(bvmap_set 10 (scalbn_model (reg_get F 10) n) (bvmap_set 15 f15 F)) (ret_pc ra) fc' None m' (seg_rom usegs)
/\ munch [] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ frm0 fc')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd397c) fc None m (seg_rom usegs)).
Proof.
intros until n. intros MI FRM Hn. eapply evt_mono. { eapply scalbn_spec; [exact MI | exact FRM | | exact Hn]. apply signed_of_Z; lia. }
intros ms' P. unfold scalbn_post in P. exact P.
Qed.
#[using="Type"] Lemma fabsl_callE : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (al ah X : Z),
mem_inv usegs m -> al = lo64 X -> ah = hi64 X ->
evt usegs (leafq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (m_fabsl X) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 FABSL) fc None m (seg_rom usegs)).
Proof. intros until X. intros MI -> ->. apply fabsl_spec; assumption. Qed.
#[using="Type"] Lemma copysignl_callE : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (al ah bl bh X Y : Z),
mem_inv usegs m -> al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
evt usegs (leafq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (m_copysignl X Y) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 COPYSIGNL) fc None m (seg_rom usegs)).
Proof. intros until Y. intros MI -> -> -> ->. apply copysignl_spec; assumption. Qed.

#[using="Type"] Lemma fmodl_callE : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q lo al ah bl bh X Y r : Z),
stk usegs m lo q -> mem_inv usegs m -> (lo <= q - 192) -> (4288 <= q < 2^63) ->
al = lo64 X -> ah = hi64 X -> bl = lo64 Y -> bh = hi64 Y ->
m_fmodl X Y = Some r ->
evt usegs (fun ms' => exists t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (lo64 r)) (Z_to_bv 64 (hi64 r)) a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F' (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(q - 192, q)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo q /\ (forall k : bv 5, bv_unsigned k <> 10%Z -> reg_get F' k = reg_get F k))
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 al) (Z_to_bv 64 ah) (Z_to_bv 64 bl) (Z_to_bv 64 bh) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 FMODL) fc None m (seg_rom usegs)).
Proof.
intros until r. intros ST MI Hlo Hq -> -> -> -> HMr.
destruct (stk_split _ _ _ (q - 192) _ ST ltac:(lia)) as [ST1 ST2].
eapply evt_mono. { eapply (rfmodl_spec ra q); unfold RFMODL_DEPTH; eauto; lia. }
intros ms' P. unfold rfmodl_post, RFMODL_DEPTH in P.
destruct P as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & m' & -> & MU & WM & MI' & ST' & FOK).
repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [|exact FOK].
eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU | exact WM | cbn [disjoint_from]; lia] | exact ST' | lia ].
Qed.
End CallE.

Definition FS_DEPTH : Z := 8656.
Definition FLOATSCAN : Z := 0xd8a58.

Section Floatscan.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Variables (ra : word) (q : Z) (gp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
(Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z)
(fR : shfile) (yR : Z).
Hypothesis HM : floatscan fuelc f0 1 pok = Some (fR, yR).
Hypothesis Hpok : pok = 0%Z \/ pok = 1%Z.
Hypothesis ST0 : sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre.
Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
Hypothesis Hp : (0 <= p < zlength txt)%Z.
Hypothesis Hnul : znth txt p = 0%Z.
Hypothesis Hnum : forall i, (0 <= i < p)%Z -> is_numch (znth txt i) = true.
Hypothesis HP30 : (p < 2^31)%Z.
Hypothesis T0 : (0 < T)%Z.
Hypothesis T1 : (T + 2^41 <= 2^63)%Z.
Hypothesis SEP : (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z.
Hypothesis SE_T : (T + zlength txt <= RERRNO \/ RERRNO + 4 <= T)%Z.
Hypothesis SPLO : (4096 <= q - FS_DEPTH)%Z.
Hypothesis SPF : (q <= Fp)%Z.
Hypothesis SPF2 : (Fp + 232 <= 2^63)%Z.
Hypothesis SPT : (T + zlength txt <= q - FS_DEPTH \/ q <= T)%Z.
Hypothesis SG1 : (ssp_guard + 8 <= q - FS_DEPTH)%Z.
Hypothesis SG2 : (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z.
Hypothesis SG3 : (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z.
Hypothesis Q1 : (q < 2^63)%Z.
Hypothesis FRM : frm0 fc.

Definition ctx_all : unit :=
let _ := (ra, q, gp, s0e, s1e, s2e, s3e, s4e, s5e, s6e, s7e, s8e, s9e, s10e, s11e, F, fc, m0,
Fp, T, p, J, txt, pre, post, canary, pok, fuelc, f0, kmin0, c0, fR, yR) in tt.

Definition Wfs : list (Z * Z) := [(q - FS_DEPTH, q); (Fp, Fp + 232); (RERRNO, RERRNO + 4)]%Z.
Notation TPv := (Z_to_bv 64 RATP).
Notation SPv := (Z_to_bv 64 (q + -8416)).
Notation XA := (q + -8312)%Z.
Notation RFJ' := (RFJ T txt p true J).
Definition zero0 : Z := f128_of_i32 0.

Definition FokR (F' : bvmap 5 word) : Prop :=
forall k : bv 5, bv_unsigned k <> 10%Z -> bv_unsigned k <> 14%Z -> bv_unsigned k <> 15%Z -> reg_get F' k = reg_get F k.

Definition Fok (F' : bvmap 5 word) : Prop :=
forall k : bv 5, bv_unsigned k <> 8%Z -> bv_unsigned k <> 10%Z -> bv_unsigned k <> 14%Z -> bv_unsigned k <> 15%Z -> reg_get F' k = reg_get F k.
#[using="Type"] Lemma Fok_refl : Fok F. Proof. intros k _ _ _ _. reflexivity. Qed.
#[using="Type"] Lemma Fok_set : forall F' (r : bv 5) v, Fok F' -> (bv_unsigned r = 8 \/ bv_unsigned r = 10 \/ bv_unsigned r = 14 \/ bv_unsigned r = 15)%Z -> Fok (bvmap_set r v F').
Proof.
intros F' r v H Hr k H8 H10 H14 H15. rewrite reg_get_set_other. { apply H; assumption. }
intros E. rewrite <- E in *. lia.
Qed.
#[using="Type"] Lemma Fok_trans10 : forall F1 F2, Fok F1 -> (forall k : bv 5, bv_unsigned k <> 10%Z -> reg_get F2 k = reg_get F1 k) -> Fok F2.
Proof. intros F1 F2 H1 H2 k H8 H10 H14 H15. rewrite H2 by exact H10. apply H1; assumption. Qed.

Definition fs_post (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m' k' c' (ev' : word),
ms' = MS (mkR ra (Z_to_bv 64 q) gp TPv t0 t1 t2 s0e s1e (Z_to_bv 64 (lo64 yR)) (Z_to_bv 64 (hi64 yR)) a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom usegs)
/\ munch Wfs m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' (q - FS_DEPTH) q
/\ rw_cells usegs m' Fp (rf_cells T p true fR J)
/\ RFJ' k' c' fR /\ (0 <= k')%Z
/\ bytes_at usegs m' T (zbytes txt)
/\ ssp_cells m' canary
/\ rw_cells usegs m' RERRNO [C4 ev']
/\ FokR F' /\ frm0 fc'.

Definition hi_cells : list cell :=
[C8 canary; C8 (reg_get F 8); C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra].

Definition finv (m : word -> option byte) : Prop :=
mem_inv usegs m /\ munch Wfs m0 m /\ wmono usegs m0 m
/\ rw_cells usegs m (q + -120) hi_cells
/\ stk usegs m (q - FS_DEPTH) (q + -8416)
/\ bytes_at usegs m T (zbytes txt)
/\ rw_cells usegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells usegs m ssp_guard [C8 canary].
#[using="Type"] Lemma zbytes_len : length (zbytes txt) = length txt.
Proof. unfold zbytes. apply length_map. Qed.
Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let TXT := fresh "BY" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
destruct H as (MI & MU & WM & FRhi & ST & TXT & SSP1 & SSP2); unfold Wfs, FS_DEPTH, RERRNO in MU; unfold hi_cells in FRhi;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold FS_DEPTH in ST;
unfold FS_DEPTH, got_ssp, ssp_guard, RERRNO in SPLO, SPT, SG1, SG2, SG3, SE_T;
try (let LT := fresh "LTX" in pose proof zbytes_len as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
unfold zlength in *.

Definition framL (j0 : list byte) (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) (ev : word) (m : word -> option byte) : Prop :=
rw_cells usegs m (q + -8416) [CB 8 j0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; CB 8 b96]
/\ rw_cells usegs m RERRNO [C4 ev].
Ltac dest_framL H := let LOW := fresh "LOW" in let ERR := fresh "ERR" in destruct H as (LOW & ERR); unfold RERRNO in ERR.

#[using="Type"] Lemma rw_cells_C8_CB8 : forall m A pre (v : word) post,
rw_cells usegs m A (pre ++ C8 v :: post) <-> rw_cells usegs m A (pre ++ CB 8 (le8 v) :: post).
Proof.
clear. intros m A pre v post. unfold rw_cells, cells_at.
rewrite !cells_wf_app, !cells_bytes_app, !cells_size_app. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize].
rewrite length_le8. tauto.
Qed.
#[using="Type"] Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
clear. intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
pose proof (bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in HR.
rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.
#[using="Type"] Lemma cb8_c8_in : forall m A pre post bs, rw_cells usegs m A (pre ++ CB 8 bs :: post) -> rw_cells usegs m A (pre ++ C8 (le_bytes_to_word bs) :: post).
Proof.
clear. intros m A pre post bs [[Hwf Hb] Hw].
apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn in H2.
split; [split|].
- apply cells_wf_app. split; [exact H1|]. split; [exact I | exact H3].
- rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb |- *. rewrite le8_of_bytes by exact H2. exact Hb.
- rewrite !cells_size_app in *. cbn [cells_size csize] in Hw |- *. exact Hw.
Qed.

Definition xrel (ws : list word) (x : list Z) (P : Z -> Prop) : Prop :=
length ws = 2048%nat /\ length x = 2048%nat /\ forall i, (0 <= i < 2048)%Z -> P i -> znth x i = wval ws i.

Notation POST := (fs_post m0).

#[using="BYT"] Lemma txt_char : forall i, (0 <= i < zlength txt)%Z -> (0 <= znth txt i < 256)%Z.
Proof.
intros i Hi. pose proof (proj1 (Forall_forall _ _) BYT (znth txt i) (Qy5Y.znth_In' txt i Hi)) as R. exact R.
Qed.
#[using="Hnum"] Lemma numch_nz : forall i, (0 <= i < p)%Z -> (43 <= znth txt i <= 101)%Z.
Proof.
intros i Hi. pose proof (Hnum i Hi) as E. unfold is_numch in E.
repeat (apply Bool.orb_true_iff in E; destruct E as [E|E]);
try (apply Z.eqb_eq in E; lia). apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.

#[using="pre"] Lemma frame_release : forall m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws,
finv m -> framL j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev m -> u32arr usegs m XA ws -> length ws = 2048%nat ->
stk usegs m (q - FS_DEPTH) q.
Proof.
intros until ws. intros FI FL XW LW. dest_finv FI. dest_framL FL.
apply u8arr_of_u32arr in XW. apply rw_cells_of_u8arr in XW. rewrite u32s_length, LW in XW.
release_frame LOW ST (q + -8312)%Z.
release_frame XW ST (q + -120)%Z.
release_frame FRhi ST q.
unfold FS_DEPTH. exact ST.
Qed.

#[using="pre Hp SE_T SPF SPT SG1 SG3"] Lemma post_tail : forall m m' K F' fc' k c ev,
finv m -> rw_cells usegs m Fp (rf_cells T p true fR J) -> RFJ' k c fR -> (0 <= k)%Z -> rw_cells usegs m RERRNO [C4 ev] ->
FokR F' -> frm0 fc' -> (0 <= K <= FS_DEPTH)%Z ->
munch [(q - K, q)]%Z m m' -> wmono usegs m m' -> mem_inv usegs m' ->
stk usegs m' (q - FS_DEPTH) q ->
forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
POST (MS (mkR ra (Z_to_bv 64 q) gp TPv t0 t1 t2 s0e s1e (Z_to_bv 64 (lo64 yR)) (Z_to_bv 64 (hi64 yR)) a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom usegs)).
Proof.
intros until ev. intros FI FC RJ Hk ERR FOK FRM' HK MU2 WM2 MI2 ST2. intros. dest_finv FI. unfold FS_DEPTH in HK, SPLO, SPT, SG1. unfold RERRNO in *.
unfold got_ssp, ssp_guard in SG1, SG2, SG3.
pose proof (rw_cells_bound _ _ _ _ FC) as B1. cbn [cells_size csize Nat.add rf_cells] in B1.
unfold fs_post, Wfs, FS_DEPTH, RERRNO, ssp_cells, got_ssp, ssp_guard. repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split.
{ eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
split; [eapply wmono_trans; [exact WM | exact WM2]|]. split; [exact MI2|]. split; [exact ST2|].
split. { eapply rw_cells_transport; [exact FC | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize rf_cells length Nat.add]; lia]. }
split; [exact RJ|]. split; [exact Hk|].
split. { eapply bytes_at_transport; [exact BY | exact MU2 | cbn [disjoint_from]; rewrite ?LTX; lia]. }
split. { split.
- eapply rw_cells_transport; [exact SSP1 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize length Nat.add]; lia].
- eapply rw_cells_transport; [exact SSP2 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize length Nat.add]; lia]. }
split. { eapply rw_cells_transport; [exact ERR | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize length Nat.add]; lia]. }
split; [exact FOK | exact FRM'].
Qed.

#[using="Hp SE_T SPF SPT SG1 SG3"] Lemma L_RET34 : forall m (x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws k c (r : Z),
let _ := ctx_all in
finv m -> framL j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev m -> u32arr usegs m XA ws -> length ws = 2048%nat ->
rw_cells usegs m Fp (rf_cells T p true fR J) -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
yR = r ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (lo64 r)) (Z_to_bv 64 (hi64 r)) canary x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9528) fct None m (seg_rom usegs)).
Proof.
intros until r. intros _ FI FL XW LW FC RJ Hk FOK FRM' Hy.
pose proof FI as FI0. pose proof FL as FL0. dest_finv FI. dest_framL FL. unfold FS_DEPTH in SPLO. pose proof (lo64_range r). pose proof (hi64_range r).
zs. zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ exfalso; lia | ]).
zs. zs. zs. zs. do 14 zs. zs.
pose proof (frame_release _ j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws FI0 FL0 XW LW) as STK.
subst r. apply evt_done. eapply (post_tail _ _ 0%Z); try eassumption.
- intros kk H10 H14 H15. destruct (Z.eq_dec (bv_unsigned kk) 8) as [E8|N8].
+ rewrite freg_get_same by (rewrite E8; vm_compute; reflexivity). f_equal. apply bv_eq. rewrite E8. vm_compute. reflexivity.
+ rewrite reg_get_set_other by (intros E; apply N8; rewrite <- E; reflexivity). apply FOK; assumption.
- unfold FS_DEPTH; lia.
- apply munch_refl.
- apply wmono_refl.
Qed.

#[using="Hp SE_T SPF SPT SG1 SG3"] Lemma L_RET1 : forall m (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 b96 ev ws k c (r : Z),
let _ := ctx_all in
finv m -> framL j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 (Z_to_bv 64 ssp_guard) b96 ev m -> u32arr usegs m XA ws -> length ws = 2048%nat ->
rw_cells usegs m Fp (rf_cells T p true fR J) -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
yR = r ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (lo64 r)) (Z_to_bv 64 (hi64 r)) x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd93c8) fct None m (seg_rom usegs)).
Proof.
intros until r. intros _ FI FL XW LW FC RJ Hk FOK FRM' Hy.
pose proof FI as FI0. dest_finv FI. pose proof FL as FL0. dest_framL FL. unfold ssp_guard in LOW.
zs. zs. zs.
eapply L_RET34; eassumption.
Qed.

#[using="Hp SE_T SPF SPT SG1 SG3"] Lemma L_RET30 : forall m (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws k c (r : Z),
let _ := ctx_all in
finv m -> framL j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev m -> u32arr usegs m XA ws -> length ws = 2048%nat ->
rw_cells usegs m Fp (rf_cells T p true fR J) -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
yR = r ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (lo64 r)) (Z_to_bv 64 (hi64 r)) x12 x13 x14 x15 x16 x17
x18 x19 (Z_to_bv 64 ssp_guard) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9524) fct None m (seg_rom usegs)).
Proof.
intros until r. intros _ FI FL XW LW FC RJ Hk FOK FRM' Hy.
pose proof FI as FI0. dest_finv FI. unfold ssp_guard.
zs.
eapply L_RET34; eassumption.
Qed.

#[using="Hp SE_T SPLO SPF SPT SG1 SG3 Q1"] Lemma L_SCL : forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws k c (Y e2 : Z),
let _ := ctx_all in
finv m -> framL j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev m -> u32arr usegs m XA ws -> length ws = 2048%nat ->
rw_cells usegs m Fp (rf_cells T p true fR J) -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(-2^31 <= e2 < 2^31)%Z ->
yR = m_scalbnl Y e2 ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 (lo64 Y)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 ssp_guard) x19 (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 e2) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xda01c) fct None m (seg_rom usegs)).
Proof.
intros until e2. intros _ FI FL XW LW FC RJ Hk FOK FRM' He2 Hy.
pose proof FI as FI0. pose proof FL as FL0. dest_finv FI. dest_framL FL. unfold FS_DEPTH in SPLO. unfold ssp_guard.
pose proof (lo64_range Y). pose proof (hi64_range Y).
zs. zs. zs. zs. zs. (if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia); [ exfalso; lia | ]).
zs. zs. zs.
zs. zs. zs. zs. do 14 zs. zs.
pose proof (frame_release _ j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws FI0 FL0 XW LW) as STK. unfold FS_DEPTH in STK.
destruct (stk_split _ _ _ (q - 112)%Z _ STK ltac:(lia)) as [ST1 ST2].
pose proof scalbnl_spec as SS. unfold scalbnl_stmt in SS.
eapply evt_mono. { eapply SS; [exact ST2 | lia | lia | exact He2 | exact MI]. }
intros ms' P. unfold scalbnl_post in P.
destruct P as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU2 & WM2 & MI2 & ST3).
rewrite <- Hy. eapply (post_tail m m' 112%Z); try eassumption.
- intros kk H10 H14 H15. rewrite reg_get_set_other by (intros E; apply H10; rewrite <- E; reflexivity).
destruct (Z.eq_dec (bv_unsigned kk) 8) as [E8|N8].
+ rewrite freg_get_same by (rewrite E8; vm_compute; reflexivity). f_equal. apply bv_eq. rewrite E8. vm_compute. reflexivity.
+ rewrite reg_get_set_other by (intros E; apply N8; rewrite <- E; reflexivity). apply FOK; assumption.
- unfold FS_DEPTH; lia.
- unfold FS_DEPTH. eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU2 | exact WM2 | cbn [disjoint_from]; lia] | exact ST3 | lia ].
Qed.

#[using="Type"] Lemma b2z_land : forall a b, Z.land (Z.b2z a) (Z.b2z b) = Z.b2z (a && b). Proof. clear. destruct a, b; reflexivity. Qed.
#[using="Type"] Lemma b2z_lt1 : forall c, (Z.b2z c <? 1) = negb c. Proof. clear. destruct c; reflexivity. Qed.

Definition hide (P : Prop) := P.

#[using="Type"] Lemma swrap32_landW_r : forall a c, bv_swrap 32 (c + Z.land a 18446744073709551615) = bv_swrap 32 (c + a).
Proof. clear. intros. rewrite (Z.add_comm c (Z.land a _)), swrap32_landW. f_equal. lia. Qed.

Definition hide2 (P : Prop) := P.

Definition dfinv (m : word -> option byte) (j0 : list byte) (w16 w24 : word) (b96 : list byte) (ev : word) (ws : list word) (sign : Z) (f : shfile) : Prop :=
finv m
/\ framL j0 (Z_to_bv 64 1021) w16 w24 (Z_to_bv 64 1) (Z_to_bv 64 (-1074)) (Z_to_bv 64 1074) (Z_to_bv 64 53)
(Z_to_bv 64 pok) (Z_to_bv 64 sign) (Z_to_bv 64 18396) (Z_to_bv 64 ssp_guard) b96 ev m
/\ u32arr usegs m XA ws /\ length ws = 2048%nat /\ rw_cells usegs m Fp (rf_cells T p true f J).

Definition dfinvG (m : word -> option byte) (j0 : list byte) (w16 w24 w80 : word) (b96 : list byte) (ev : word) (ws : list word) (sign : Z) (f : shfile) : Prop :=
finv m
/\ framL j0 (Z_to_bv 64 1021) w16 w24 (Z_to_bv 64 1) (Z_to_bv 64 (-1074)) (Z_to_bv 64 1074) (Z_to_bv 64 53)
(Z_to_bv 64 pok) (Z_to_bv 64 sign) w80 (Z_to_bv 64 ssp_guard) b96 ev m
/\ u32arr usegs m XA ws /\ length ws = 2048%nat /\ rw_cells usegs m Fp (rf_cells T p true f J).
#[using="Type"] Lemma dfinvG_dfinv : forall m j0 w16 w24 b96 ev ws sign f,
dfinvG m j0 w16 w24 (Z_to_bv 64 18396) b96 ev ws sign f = dfinv m j0 w16 w24 b96 ev ws sign f.
Proof. reflexivity. Qed.

Definition inring (a z i : Z) : Prop := ((i - a) mod 2048 < (z - a) mod 2048)%Z.
#[using="Type"] Lemma land2047 : forall v, Z.land v 2047 = (v mod 2048)%Z.
Proof. clear. intros. change 2047%Z with (Z.ones 11). rewrite Z.land_ones by lia. reflexivity. Qed.
#[using="Type"] Lemma landW_mod2048 : forall v, ((Z.land v 18446744073709551615) mod 2048 = v mod 2048)%Z.
Proof. clear. intros. rewrite land_W64. apply Z.mod_mod_divide. exists (2^53)%Z. reflexivity. Qed.
#[using="Type"] Lemma inring_plus : forall a z d, (0 <= z < 2048)%Z -> (0 <= d < 2048)%Z -> (d <= (z - a) mod 2048)%Z -> Z.land (a + d) 2047 <> z ->
inring a z (Z.land (a + d) 2047) /\ (d + 1 <= (z - a) mod 2048)%Z.
Proof. clear.
intros a z d Hz Hd Hle Hne. rewrite land2047 in *. unfold inring.
rewrite Zminus_mod_idemp_l. replace (a + d - a)%Z with d by lia. rewrite (Z.mod_small d 2048) by lia.
pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(lia)).
assert ((z - a) mod 2048 <> d)%Z; [|lia].
intros Ed. apply Hne. rewrite <- (Z.mod_small z 2048) by lia.
rewrite <- Ed. rewrite Zplus_mod_idemp_r. f_equal. lia.
Qed.
#[using="Type"] Lemma inring_hit : forall a z d, (0 <= z < 2048)%Z -> (0 <= d < 2048)%Z -> Z.land (a + d) 2047 = z -> ((z - a) mod 2048 = d)%Z.
Proof. clear.
intros a z d Hz Hd E. rewrite land2047 in E. rewrite <- E. rewrite Zminus_mod_idemp_l.
replace (a + d - a)%Z with d by lia. apply Z.mod_small. lia.
Qed.
#[using="Type"] Lemma inring_grow : forall a z i, (0 <= z)%Z -> ((z - a) mod 2048 < 2047)%Z ->
inring a (z + 1) i <-> (inring a z i \/ (i - a) mod 2048 = (z - a) mod 2048)%Z.
Proof. clear.
intros a z i Hz Hlt. unfold inring.
replace (z + 1 - a)%Z with ((z - a) + 1)%Z by lia. rewrite <- (Zplus_mod_idemp_l (z - a)).
pose proof (Z.mod_pos_bound (z - a) 2048 ltac:(lia)). pose proof (Z.mod_pos_bound (i - a) 2048 ltac:(lia)).
rewrite (Z.mod_small ((z - a) mod 2048 + 1)) by lia. lia.
Qed.
#[using="Type"] Lemma mod_eq_idx : forall a z i, (0 <= z < 2048)%Z -> (0 <= i < 2048)%Z -> ((i - a) mod 2048 = (z - a) mod 2048)%Z -> i = z.
Proof. clear.
intros a z i Hz Hi E.
rewrite <- (Z.mod_small i 2048), <- (Z.mod_small z 2048) by lia.
transitivity (((i - a) mod 2048 + a) mod 2048)%Z. { rewrite Zplus_mod_idemp_l. f_equal. lia. }
rewrite E. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.
#[using="Type"] Lemma inring_mod : forall a z i, inring a (z mod 2048) i <-> inring a z i.
Proof. clear. intros. unfold inring. rewrite Zminus_mod_idemp_l. reflexivity. Qed.
#[using="Type"] Lemma xrel_iff : forall ws x (P Q : Z -> Prop), (forall i, (0 <= i < 2048)%Z -> Q i -> P i) -> xrel ws x P -> xrel ws x Q.
Proof. clear. intros ws x P Q HPQ (L1 & L2 & R). split; [exact L1|]. split; [exact L2|]. intros i Hi Hq. apply R; [exact Hi | apply HPQ; [exact Hi | exact Hq]]. Qed.

Definition zone (h w : bool) (a z : Z) (i : Z) : Prop := inring a z i \/ (h = true /\ (z <= i)%Z) \/ (w = true /\ (a <= i)%Z).
#[using="Type"] Lemma zone_in : forall h w a z i, inring a z i -> zone h w a z i.
Proof. clear. intros. left. assumption. Qed.
#[using="Type"] Lemma xrel_window : forall ws x h w a z, xrel ws x (zone h w a z) -> xrel ws x (inring a z).
Proof. clear. intros until z. apply xrel_iff. intros i _ Hi. left. exact Hi. Qed.

Definition X31 (x : list Z) : Prop := forall i, (0 <= znth x i < 2^31)%Z.

Definition S_F3 : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word) Ft fct
j0 w16 w24 b96 ev ws sign k c (Y FR BI e2 bits' : Z),
let _ := ctx_all in
dfinv m j0 w16 w24 b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= bits' <= 53)%Z ->
fin_K3 1024 Y FR BI e2 = Some yR ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (e2 + 113)) (Z_to_bv 64 (hi64 FR)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (lo64 FR)) (Z_to_bv 64 1021) (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 e2) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (lo64 BI)) (Z_to_bv 64 (hi64 BI))
(Z_to_bv 64 (e2 + 1187)) (Z_to_bv 64 bits') x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9f08) fct None m (seg_rom usegs)).

#[using="Type"] Lemma f128_ge_range : forall a b, (-1 <= f128_ge a b <= 1)%Z.
Proof.
clear. intros a b. unfold f128_ge.
repeat (lazymatch goal with |- context [if ?c then _ else _] => destruct c | _ => fail end; try (cbn; lia)).
all: try (unfold nez64, b2z; destruct (negb _); cbn; lia).
Qed.

Tactic Notation "call_split" constr(K) tactic3(tac) :=
lazymatch goal with ST : stk _ ?m (q - 8656)%Z (q + -8416)%Z |- _ =>
let ST1 := fresh "ST1" in
destruct (stk_split _ _ _ (q + -8416 - K)%Z _ ST ltac:(lia)) as [ST1 ?ST2];
callw tac;
lazymatch goal with STn : stk _ ?m' (q + -8416 - K)%Z (q + -8416)%Z |- _ =>
lazymatch goal with ST1' : stk _ m' (q - 8656)%Z (q + -8416 - K)%Z |- _ =>
pose proof (stk_merge _ _ _ _ _ ST1' STn ltac:(lia)) as ST; clear ST1' STn end end
end.

#[using="Type"] Lemma extenddftf2_callF : forall ra' sp' gp' tp' t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F' : bvmap 5 word) fc' (m : word -> option byte) (D : Z),
mem_inv usegs m -> bv_unsigned (reg_get F' 10) = D ->
evt usegs (leaf2_post ra' sp' gp' tp' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F' fc' (f128_of_d D) m)
(MS (mkR ra' sp' gp' tp' t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0xcde40) fc' None m (seg_rom usegs)).
Proof.
clear. intros until D. intros MI HD. eapply evt_mono. { eapply extenddftf2_spec. exact MI. }
intros ms' P. unfold extenddftf2_post in P. rewrite HD in P. exact P.
Qed.

Definition S_F2 : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (a z Y FR BI e2 bits' : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 FR)) (Z_to_bv 64 (hi64 FR)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= bits' <= 53)%Z ->
xrel ws x (inring a z) -> X31 x -> (0 <= a < 2048)%Z -> (0 <= z < 2048)%Z ->
(Z.land (a + 4) MASK <> z -> inring a z (Z.land (a + 4) MASK)) ->
fin_K2 sign 1024 a z x 4 bits' Y FR BI e2 = Some yR ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (e2 + 113)) (Z_to_bv 64 (a + 4)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) (Z_to_bv 64 (hi64 Y)) (Z_to_bv 64 e2) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (lo64 BI)) (Z_to_bv 64 (hi64 BI))
(Z_to_bv 64 (e2 + 1187)) (Z_to_bv 64 bits') x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9de0) fct None m (seg_rom usegs)).

#[using="Type"] Lemma floatsitf_callsg : forall ra' sp' gp' tp' t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F' : bvmap 5 word) fc' (m : word -> option byte) (sg : Z),
mem_inv usegs m -> (sg = 1 \/ sg = -1)%Z ->
evt usegs (leaf2_post ra' sp' gp' tp' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F' fc' (f128_of_i32 sg) m)
(MS (mkR ra' sp' gp' tp' t0 t1 t2 s0 s1 (Z_to_bv 64 sg) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0xd2f70) fc' None m (seg_rom usegs)).
Proof.
clear. intros until sg. intros MI [-> | ->].
- apply floatsitf_callp; [exact MI | lia].
- replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
apply floatsitf_callv; [exact MI | lia | rewrite sext32_eq; reflexivity].
Qed.

Definition S_F1 : Prop := forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (a z Y e2 : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z ->
xrel ws x (inring a z) -> X31 x -> (0 <= a < 2048)%Z -> (0 <= z < 2048)%Z ->
(Z.land (a + 4) MASK <> z -> inring a z (Z.land (a + 4) MASK)) ->
fin_K1 53 (-1074) sign 1024 zero0 a z x 4 Y e2 = Some yR ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 (a + 4)) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) x24
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9cf4) fct None m (seg_rom usegs)).

#[using="Type"] Lemma lxor_sign_small : forall e, (-2^62 <= e < 2^62)%Z ->
Z.lxor (Z.land e 18446744073709551615) 9223372036854775808 = (e + 2^63)%Z.
Proof.
clear. intros e He. rewrite land_W64. change 9223372036854775808%Z with (2^63)%Z.
rewrite zb_lxor_sign by (apply Z.mod_pos_bound; lia). Z.div_mod_to_equations; lia.
Qed.

#[using="Type"] Lemma clamp0_idiom : forall v, (-2^62 <= v < 2^62)%Z ->
Z.land (Z.land (0 - Z.b2z (9223372036854775808 <? Z.lxor (Z.land v 18446744073709551615) 9223372036854775808)) 18446744073709551615)
(Z.land v 18446744073709551615) = (if v <? 0 then 0 else v)%Z.
Proof.
clear. intros v Hv. rewrite lxor_sign_small by lia.
destruct (Z.ltb_spec 9223372036854775808 (v + 2^63)); destruct (Z.ltb_spec v 0); try lia; cbn [Z.b2z].
- change (Z.land (0 - 1) 18446744073709551615)%Z with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. rewrite land_W64, Z.mod_mod by lia. apply Z.mod_small. lia.
- change (Z.land (0 - 0) 18446744073709551615)%Z with 0%Z. apply Z.land_0_l.
- assert (E : v = 0%Z) by lia. rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma cb44_merge : forall m A pre (bs : list byte) (w : word),
rw_cells usegs m A (pre ++ [CB 4 bs; C4 w]) -> rw_cells usegs m A (pre ++ [CB 8 (bs ++ le4 w)]).
Proof.
clear. intros m A pre bs w [[Hwf Hb] Hw].
apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 _]]. cbn in H2.
split; [split|].
- apply cells_wf_app. split; [exact H1|]. split; [|exact I]. cbn -[le4]. rewrite length_app, H2, length_le4. reflexivity.
- rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb |- *. rewrite <- app_assoc, app_nil_r in *. exact Hb.
- rewrite !cells_size_app in *. cbn [cells_size csize] in Hw |- *. exact Hw.
Qed.
Definition C1E9HI : Z := 0x401cdcd650000000.

Definition ainv (ws : list word) (x : list Z) (h w : bool) (a z i : Z) : Prop :=
xrel ws x (zone h w a z) /\ X31 x /\ (0 <= z < 2048)%Z /\ (h = false -> z + (4 - i) <= 2052)%Z /\ (i <= (z - a) mod 2048)%Z /\ (w = false -> a <= 60)%Z.

Definition S_A69C : Prop := forall m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (a z Y e2 : Z) (f : nat) sres,
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= a < 2048)%Z ->
ainv ws x h w a z 3 ->
df_asm_loop f a (mkAS 3 Y z x) = Some sres -> (2 <= f)%nat ->
fin_K1 53 (-1074) sign 1024 zero0 a (as_z sres) (as_x sres) (as_i sres) (as_y sres) e2 = Some yR ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (a + 3)) x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 C1E9HI) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9c90) fct None m (seg_rom usegs)).

Definition S_A62C : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (a z Y e2 : Z) (f : nat) sres,
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= a < 2048)%Z ->
ainv ws x h w a z 2 ->
df_asm_loop f a (mkAS 2 Y z x) = Some sres -> (3 <= f)%nat ->
fin_K1 53 (-1074) sign 1024 zero0 a (as_z sres) (as_x sres) (as_i sres) (as_y sres) e2 = Some yR ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (a + 2)) (Z_to_bv 64 XA) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 C1E9HI) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9c20) fct None m (seg_rom usegs)).

Definition S_A5C4 : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (a z Y e2 : Z) (f : nat) sres,
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= a < 2048)%Z ->
ainv ws x h w a z 1 ->
df_asm_loop f a (mkAS 1 Y z x) = Some sres -> (4 <= f)%nat ->
fin_K1 53 (-1074) sign 1024 zero0 a (as_z sres) (as_x sres) (as_i sres) (as_y sres) e2 = Some yR ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 C1E9HI) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y))
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9bb8) fct None m (seg_rom usegs)).

Definition fin_K0 (sign a z : Z) (x : list Z) (e2 : Z) : option Z := df_final a z x e2 53 (-1074) sign 1024 zero0 zero0.

Definition S_A568 : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (a z e2 xa : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= a < 2048)%Z ->
ainv ws x h w a z 0 -> a <> z -> xa = znth x a ->
fin_K0 sign a z x e2 = Some yR ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) (Z_to_bv 64 xa) x23 x24
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9b5c) fct None m (seg_rom usegs)).

Definition S_A534 : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (a z e2 S1 : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (-2^24 <= e2 <= 2^24)%Z -> (0 <= a < 2048)%Z ->
ainv ws x h w a z 0 -> a = z -> S1 = (4 * ((z + 1) mod 2048))%Z ->
fin_K0 sign a z x e2 = Some yR ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 ((z + 1) mod 2048)) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 x23 x24
x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9b28) fct None m (seg_rom usegs)).

Definition SN324 (fo : nat) : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (rp a z e2 i0 Z0 S1 A6 : Z) s',
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (0 <= a < 2048)%Z ->
xrel ws x (zone h w a z) -> X31 x -> (0 <= z < 2048)%Z -> (h = false -> z + Z.of_nat fo <= 4100)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> (Z.of_nat fo <= 2000)%Z ->
(-2^26 + 18450 * Z.of_nat fo <= rp <= 560)%Z -> (-2^20 <= e2 <= 2^17 - 9 * Z.of_nat fo)%Z ->
Z0 = ((z + 1) mod 2048)%Z -> S1 = (4 * Z0)%Z -> A6 = (XA + 4 * ((z - 1) mod 2048))%Z ->
df_dn_loop fo (mkDS rp a z e2 x i0) = Some s' ->
fin_K0 sign (ds_a s') (ds_z s') (ds_x s') (ds_e2 s') = Some yR ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 Z0) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 A6) x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9918) fct None m (seg_rom usegs)).
Definition S_N324 : Prop := forall fo, SN324 fo.

Definition S_N2D4 : Prop := forall (fo : nat) m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (rp a z e2 i0 : Z) s',
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (0 <= a < 2048)%Z ->
xrel ws x (zone h w a z) -> X31 x -> (0 <= z < 2048)%Z -> (h = false -> z + Z.of_nat fo <= 4100)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> (Z.of_nat fo <= 2000)%Z ->
(-2^26 + 18450 * Z.of_nat fo <= rp <= 560)%Z -> (-2^20 <= e2 <= 2^17 - 9 * Z.of_nat fo)%Z ->
df_dn_loop fo (mkDS rp a z e2 x i0) = Some s' ->
fin_K0 sign (ds_a s') (ds_z s') (ds_x s') (ds_e2 s') = Some yR ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd98c8) fct None m (seg_rom usegs)).

Definition up_K (sign rp a z e2 : Z) (x : list Z) : option Z :=
match df_dn_loop FUEL_SCALE (mkDS rp a z e2 x 0) with
| None => None
| Some s' => fin_K0 sign (ds_a s') (ds_z s') (ds_x s') (ds_e2 s')
end.
Definition MAGIC : Z := 19342813113834067.

Definition S_U1A8 : Prop := forall (fo : nat) m (x1 x5 x6 x7 x8 x9 x16 x17 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (rp a z e2 : Z) s',
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (0 <= a < 2048)%Z ->
xrel ws x (zone h w a z) -> X31 x -> (0 <= z < 2048)%Z -> (h = false -> z <= 2047)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> a <> z ->
(-2^20 <= rp <= 560)%Z -> (-2^20 + 29 * Z.of_nat fo <= e2 <= 0)%Z ->
df_up_loop fo (mkUS rp a z e2 x) = Some s' ->
up_K sign (us_rp s') (us_a s') (us_z s') (us_e2 s') (us_x s') = Some yR ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 XA) (Z_to_bv 64 36) (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) (Z_to_bv 64 10384592) x16 x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd979c) fct None m (seg_rom usegs)).

#[using="Type"] Lemma df_dn_loop_step : forall n s, df_dn_loop (S n) s = match df_dn_body s with None => None | Some (inl s') => df_dn_loop n s' | Some (inr s') => Some s' end.
Proof. reflexivity. Qed.
#[using="Type"] Lemma df_dni_loop_step : forall n a z x i, df_dni_loop (S n) a z x i =
if (i <? LD_B1B_DIG)%Z then match df_dni_body a z x i with inl i' => df_dni_loop n a z x i' | inr i' => Some i' end else Some i.
Proof. reflexivity. Qed.
#[using="Type"] Lemma df_dnk_loop_step : forall n z sh s, df_dnk_loop (S n) z sh s = if negb (dk_k s =? z)%Z then df_dnk_loop n z sh (df_dnk_body z sh s) else Some s.
Proof. reflexivity. Qed.
#[using="Type"] Lemma dn_carry_bound : forall sh tmp, (sh = 1 \/ sh = 9)%Z -> (0 <= tmp <= 2^sh - 1)%Z -> (0 <= Z.shiftr 1000000000 sh * tmp < 2^30)%Z.
Proof. clear. intros sh tmp [-> | ->] H; [change (Z.shiftr 1000000000 1) with 500000000%Z | change (Z.shiftr 1000000000 9) with 1953125%Z]; cbn in H; lia. Qed.
#[using="Type"] Lemma shr_half : forall t sh, (0 <= t)%Z -> (1 <= sh)%Z -> (0 <= Z.shiftr t sh <= t / 2)%Z.
Proof.
clear. intros t sh Ht Hsh. split; [apply Z.shiftr_nonneg; lia|]. rewrite Z.shiftr_div_pow2 by lia.
apply Z.div_le_compat_l; [lia|]. split; [lia|]. change 2%Z with (2^1)%Z at 1. apply Z.pow_le_mono_r; lia.
Qed.
#[using="Type"] Lemma lor_lxor_zero : forall k a v, (0 <= k)%Z -> (0 <= a)%Z -> (0 <= v)%Z ->
Z.lor (Z.lxor k a) v = 0%Z <-> (k = a /\ v = 0%Z).
Proof.
clear. intros k a v Hk Ha Hv. split.
- intros H. apply Z.lor_eq_0_iff in H. destruct H as [H1 H2]. split; [|exact H2]. apply Z.lxor_eq_0_iff. exact H1.
- intros [-> ->]. rewrite Z.lxor_nilpotent. reflexivity.
Qed.
#[using="Type"] Lemma lor_lxor_nonneg : forall k a v, (0 <= k)%Z -> (0 <= a)%Z -> (0 <= v)%Z -> (0 <= Z.lor (Z.lxor k a) v)%Z.
Proof. clear. intros. apply Z.lor_nonneg. split; [apply Z.lxor_nonneg; lia | lia]. Qed.
#[using="Type"] Lemma rp_upd : forall rp (c : bool),
Z_to_bv 64 (rp + Z.land (Z.land (Z.b2z c + -1) 18446744073709551615) 18446744073709551607) = Z_to_bv 64 (if c then rp else rp - 9)%Z.
Proof.
clear. intros rp [|].
- change (Z.land (Z.land (Z.b2z true + -1) 18446744073709551615) 18446744073709551607) with 0%Z. rewrite Z.add_0_r. reflexivity.
- change (Z.land (Z.land (Z.b2z false + -1) 18446744073709551615) 18446744073709551607) with 18446744073709551607%Z.
apply Z_to_bv_eqm. Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma dn_az_none : forall fo rp z e2 x i0, (0 <= z < 2048)%Z -> rp <> 36%Z -> df_dn_loop fo (mkDS rp z z e2 x i0) = None.
Proof.
clear. induction fo as [|fo IH]; intros rp z e2 x i0 Hz Hrp; [reflexivity|].
rewrite df_dn_loop_step. unfold df_dn_body. cbn [ds_a ds_z ds_x ds_rp ds_e2].
change (df_dni_loop 6 z z x 0) with (if (0 <? LD_B1B_DIG)%Z then match df_dni_body z z x 0 with inl i' => df_dni_loop 5 z z x i' | inr i' => Some i' end else Some 0%Z).
change (0 <? LD_B1B_DIG)%Z with true. unfold df_dni_body. rewrite Z.add_0_r. change MASK with 2047%Z. rewrite land2047, Z.mod_small, Z.eqb_refl by lia. cbn [orb].
change LD_B1B_DIG with 4%Z. change (4 =? 4)%Z with true. replace (rp =? 9 * 4)%Z with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
cbv zeta. unfold FUEL_RING. rewrite df_dnk_loop_step. cbn [dk_k]. rewrite Z.eqb_refl. cbn [negb nz Z.eqb].
apply IH; assumption.
Qed.

Definition S_NK : Prop := forall (fi : nat) m (x1 x8 x9 x10 x11 x12 x13 x14 x15 x16 x20 x22 x24 x25 x26 x27 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign (x : list Z) (h w : bool) (k carry a i rp z sh e2 B : Z) (s1 : st_dnk),
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> Fok Ft -> frm0 fct ->
xrel ws x (zone h w a z) -> X31 x ->
(0 <= a < 2048)%Z -> (0 <= z < 2048)%Z -> (0 <= k < 2048)%Z -> ((k - a) mod 2048 <= (z - a) mod 2048)%Z -> k <> z ->
(0 <= carry < 2^30)%Z -> (sh = 1 \/ sh = 9)%Z -> (B + 9 * Z.of_nat fi <= rp <= 560)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> (-2^27 <= B)%Z -> (-2^21 <= e2 <= 2^21)%Z ->
df_dnk_loop fi z sh (mkDK k carry a i rp x) = Some s1 ->
(forall m' ws' b96' (x17' x28' x29' x30' x31' : word) (w' : bool),
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96' ev ws' sign fR ->
xrel ws' (dk_x s1) (zone h w' (dk_a s1) z) -> X31 (dk_x s1) ->
(0 <= dk_a s1 < 2048)%Z -> (0 <= dk_carry s1 < 2^30)%Z -> (B <= dk_rp s1 <= 560)%Z -> (w' = false -> 9 * dk_a s1 + dk_rp s1 <= 560)%Z -> dk_k s1 = z ->
evt usegs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 sh) (Z_to_bv 64 (dk_carry s1)) (Z_to_bv 64 (Z.shiftr 1000000000 sh)) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17'
(Z_to_bv 64 z) (Z_to_bv 64 (dk_a s1)) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 (dk_rp s1)) x24 x25 x26 x27 x28' x29' x30' x31')
Ft (Z_to_bv 64 0xd9a78) fct None m' (seg_rom usegs))) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 sh) (Z_to_bv 64 carry) (Z_to_bv 64 (Z.shiftr 1000000000 sh)) x8 x9 x10 x11 x12 x13 x14 x15 x16 (Z_to_bv 64 (2^sh - 1))
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 (Z_to_bv 64 k) x29 x30 x31)
Ft (Z_to_bv 64 0xd9a44) fct None m (seg_rom usegs)).

Definition S_N484 : Prop := forall (fo : nat), SN324 fo ->
forall (s1 : st_dnk) m (x1 x10 x11 x12 x13 x14 x15 x17 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (h w : bool) (rp z e2 Z0 S1 A6 sh : Z) s',
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z ->
xrel ws (dk_x s1) (zone h w (dk_a s1) z) -> X31 (dk_x s1) ->
(0 <= dk_a s1 < 2048)%Z -> (0 <= dk_carry s1 < 2^30)%Z -> dk_k s1 = z -> (sh = 1 \/ sh = 9)%Z ->
(0 <= z < 2048)%Z -> (h = false -> z + Z.of_nat (S fo) <= 4100)%Z -> (w = false -> 9 * dk_a s1 + dk_rp s1 <= 560)%Z -> (Z.of_nat (S fo) <= 2000)%Z ->
(-2^26 + 18450 * Z.of_nat (S fo) <= rp <= 560)%Z -> (rp - 18450 <= dk_rp s1 <= 560)%Z -> (-2^20 <= e2 <= 2^17 - 9 * Z.of_nat (S fo))%Z ->
Z0 = ((z + 1) mod 2048)%Z -> S1 = (4 * Z0)%Z -> A6 = (XA + 4 * ((z - 1) mod 2048))%Z ->
(let 'mkDK _ carry a1 i rp1 xx := s1 in
let '(z', x') := if nz carry then
if negb ((z + 1) mod 2048 =? a1)%Z then ((z + 1) mod 2048, zupd xx z carry)%Z
else (z, zupd xx ((z - 1) mod 2048) (Z.lor (znth xx ((z - 1) mod 2048)) 1))%Z
else (z, xx) in
df_dn_loop fo (mkDS rp1 a1 z' (e2 + sh) x' i) = Some s') ->
fin_K0 sign (ds_a s') (ds_z s') (ds_x s') (ds_e2 s') = Some yR ->
evt usegs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 sh) (Z_to_bv 64 (dk_carry s1)) (Z_to_bv 64 (Z.shiftr 1000000000 sh)) (Z_to_bv 64 Z0) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 A6) x17
(Z_to_bv 64 z) (Z_to_bv 64 (dk_a s1)) x20 (Z_to_bv 64 (e2 + sh)) x22 (Z_to_bv 64 (dk_rp s1)) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9a78) fct None m (seg_rom usegs)).

Definition S_N3E8 : Prop := forall (fo : nat), SN324 fo ->
forall (iq : Z) m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (rp a z e2 Z0 S1 A6 : Z) s',
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (0 <= a < 2048)%Z ->
xrel ws x (zone h w a z) -> X31 x -> (0 <= z < 2048)%Z -> (h = false -> z + Z.of_nat (S fo) <= 4100)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> (Z.of_nat (S fo) <= 2000)%Z ->
(-2^26 + 18450 * Z.of_nat (S fo) <= rp <= 560)%Z -> (-2^20 <= e2 <= 2^17 - 9 * Z.of_nat (S fo))%Z ->
Z0 = ((z + 1) mod 2048)%Z -> S1 = (4 * Z0)%Z -> A6 = (XA + 4 * ((z - 1) mod 2048))%Z -> a <> z ->
match
match df_dnk_loop FUEL_RING z (if 45 <? rp then 9%Z else 1%Z) (mkDK a 0 a iq rp x) with
| Some (mkDK _ carry a1 i rp1 xx) =>
let '(z', x') := (if nz carry then
if negb ((z + 1) mod 2048 =? a1)%Z then ((z + 1) mod 2048, zupd xx z carry)%Z
else (z, zupd xx ((z - 1) mod 2048) (Z.lor (znth xx ((z - 1) mod 2048)) 1))%Z
else (z, xx)) in
Some (inl (mkDS rp1 a1 z' (e2 + (if 45 <? rp then 9%Z else 1%Z)) x' i))
| None => None
end
with
| Some (inl s'') => df_dn_loop fo s''
| Some (inr s'') => Some s''
| None => None
end = Some s' ->
fin_K0 sign (ds_a s') (ds_z s') (ds_x s') (ds_e2 s') = Some yR ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 Z0) (Z_to_bv 64 S1) x10 x11 x12 x13 x14 x15 (Z_to_bv 64 A6) x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd99dc) fct None m (seg_rom usegs)).

#[using="Type"] Lemma df_up_loop_step : forall n s, df_up_loop (S n) s = if df_up_cond s then match df_up_body s with None => None | Some s' => df_up_loop n s' end else Some s.
Proof. reflexivity. Qed.
#[using="Type"] Lemma df_upk_loop_step : forall n a s, df_upk_loop (S n) a s = match df_upk_body a s with inl s' => df_upk_loop n a s' | inr s' => Some s' end.
Proof. reflexivity. Qed.
#[using="Type"] Lemma mod_add2047 : forall u, ((u + 2047) mod 2048 = (u - 1) mod 2048)%Z.
Proof. clear. intros u. rewrite <- (Z.mod_add (u - 1) 1 2048) by lia. f_equal. lia. Qed.

#[using="Type"] Lemma magic_div_1e9 : forall tmp, (0 <= tmp < 2^61)%Z ->
(Z.shiftr ((Z.shiftr tmp 9 * MAGIC) / 2^64) 11 = tmp / 1000000000)%Z.
Proof.
clear. intros tmp Ht. unfold MAGIC. rewrite !Z.shiftr_div_pow2 by lia.
rewrite Z.div_div by lia. change (2^64 * 2^11)%Z with (2^75)%Z.
replace (tmp / 1000000000)%Z with ((tmp / 2^9) / 1953125)%Z by (rewrite Z.div_div by lia; f_equal).
set (u := (tmp / 2^9)%Z). assert (Hu : (0 <= u < 2^52)%Z) by (subst u; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
clearbody u. clear Ht tmp. Z.div_mod_to_equations. nia.
Qed.

#[using="Type"] Lemma magic_div_1e9_reg : forall tmp, (0 <= tmp < 2^61)%Z ->
Z.shiftr (Z.land (Z.shiftr (Z.shiftr tmp 9 * Z.land MAGIC 18446744073709551615) 64) 18446744073709551615) 11 = (tmp / 1000000000)%Z.
Proof.
clear. intros tmp Ht. change (Z.land MAGIC 18446744073709551615) with MAGIC.
assert (R1 : (0 <= Z.shiftr tmp 9 < 2^52)%Z) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (R2 : (0 <= Z.shiftr (Z.shiftr tmp 9 * MAGIC) 64 < 2^64)%Z).
{ unfold MAGIC. rewrite (Z.shiftr_div_pow2 _ 64) by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia|]]. nia. }
rewrite land_W64, (Z.mod_small _ _ R2). rewrite (Z.shiftr_div_pow2 _ 64) by lia. apply magic_div_1e9. exact Ht.
Qed.
#[using="Type"] Lemma u32_id : forall v, (0 <= v < 2^32)%Z -> u32 v = v.
Proof. clear. intros. unfold u32. apply Z.mod_small. lia. Qed.
#[using="Type"] Lemma inring_front : forall a z i, (0 <= a < 2048)%Z -> (0 <= i < 2048)%Z -> (0 <= z < 2048)%Z ->
inring ((a - 1) mod 2048) z i -> i <> ((a - 1) mod 2048)%Z -> z <> ((a - 1) mod 2048)%Z -> inring a z i.
Proof. clear. intros a z i Ha Hi Hz H Hne Hzne. unfold inring in *. Z.div_mod_to_equations. nia. Qed.

Definition S_UK : Prop := forall (n : nat) m (x1 x5 x6 x8 x9 x11 x15 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign (x : list Z) (h w : bool) (k carry a z : Z) (s1 : st_upk),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> Fok Ft -> frm0 fct ->
xrel ws x (zone h w a z) -> X31 x ->
(0 <= a < 2048)%Z -> (0 <= z < 2048)%Z -> (0 <= k < 2048)%Z -> inring a z k ->
(0 <= carry < 2^31)%Z ->
df_upk_loop n a (mkUK k carry z x) = Some s1 ->
(forall m' ws' (x7' x18' x29' x30' x31' : word) (h' : bool),
dfinv m' j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws' sign fR ->
xrel ws' (uk_x s1) (zone h' w a (uk_z s1)) -> X31 (uk_x s1) ->
uk_k s1 = a -> (0 <= uk_carry s1 < 2^31)%Z -> (0 <= uk_z s1 < 2048)%Z -> (h' = false -> h = false /\ uk_z s1 <= z)%Z -> a <> uk_z s1 ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 (Z_to_bv 64 (uk_z s1)) x7' x8 x9 (Z_to_bv 64 XA) x11 (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) x15 (Z_to_bv 64 (uk_carry s1)) x17
x18' (Z_to_bv 64 a) x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 ((uk_z s1 - 1) mod 2048)) x29' x30' x31')
Ft (Z_to_bv 64 0xd97ac) fct None m' (seg_rom usegs))) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 (Z_to_bv 64 k) x8 x9 (Z_to_bv 64 XA) x11 (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) x15 (Z_to_bv 64 carry) x17
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd97e0) fct None m (seg_rom usegs)).

Definition SU1C4 (fo : nat) : Prop := forall m (x1 x6 x7 x8 x9 x16 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (h w : bool) (rp a z e2 : Z) s',
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> (0 <= a < 2048)%Z ->
xrel ws x (zone h w a z) -> X31 x -> (0 <= z < 2048)%Z -> (h = false -> z <= 2047)%Z -> (w = false -> 9 * a + rp <= 560)%Z -> a <> z ->
(-2^20 <= rp <= 560)%Z -> (-2^20 + 29 * Z.of_nat fo <= e2 <= 0)%Z ->
df_up_loop fo (mkUS rp a z e2 x) = Some s' ->
up_K sign (us_rp s') (us_a s') (us_z s') (us_e2 s') (us_x s') = Some yR ->
evt usegs POST
(MS (mkR x1 SPv gp TPv (Z_to_bv 64 rp) x6 x7 x8 x9 (Z_to_bv 64 XA) (Z_to_bv 64 36) (Z_to_bv 64 1000000001) (Z_to_bv 64 MAGIC) (Z_to_bv 64 1000000000) (Z_to_bv 64 10384592) x16 (Z_to_bv 64 (XA + 4 * a))
(Z_to_bv 64 z) (Z_to_bv 64 a) x20 (Z_to_bv 64 e2) x22 (Z_to_bv 64 rp) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd97b8) fct None m (seg_rom usegs)).
Definition S_U1C4 : Prop := forall fo, SU1C4 fo.

Definition S_T : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (rp kz : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z ->
xrel ws x (inring 0 kz) -> X31 x -> (1 <= kz <= 2046)%Z -> znth x 0 <> 0%Z -> (-2^15 <= rp <= 537)%Z ->
dfK_tz 53 (-1074) sign fR rp kz x = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9620) fct None m (seg_rom usegs)).

Definition S_DD0 : Prop := forall m (x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (X Y : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
yR = f128_mul X Y ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd93c4) fct None m (seg_rom usegs)).

Definition S_DD24 : Prop := forall m (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (X u : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(0 <= u < 2^31)%Z -> yR = f128_mul X (f128_of_u32 u) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 u) x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9318) fct None m (seg_rom usegs)).

Definition S_M : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x14 x15 x16 x17 x18 x19 x20 x21 x22 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 b96 ev ws sign k c (x : list Z) (rp lnz kz : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) b96 ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z ->
xrel ws x (inring 0 kz) -> X31 x -> (1 <= kz <= 2046)%Z -> znth x 0 <> 0%Z -> (1 <= lnz < 2^31)%Z -> (-1300 <= rp <= 537)%Z ->
dfK_mid 53 (-1074) sign fR rp lnz kz x = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 lnz) x14 x15 x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 rp) (Z_to_bv 64 kz) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9450) fct None m (seg_rom usegs)).

Definition digz (k j : Z) (i : Z) : Prop := (i < k)%Z \/ i = 0%Z \/ (i = k /\ j <> 0%Z).

Definition S_P : Prop := forall m (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 ev ws sign k c (x : list Z) (lrp lnz j kz : Z),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) (le8 (Z_to_bv 64 lnz)) ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z ->
xrel ws x (digz kz j) -> X31 x ->
(0 <= j <= 8)%Z -> (0 <= kz <= 2045)%Z -> znth x 0 <> 0%Z -> (1 <= lnz < 2^31)%Z -> (-1300 <= lrp <= 537)%Z ->
(j <> 0%Z -> znth x kz < 10 ^ j)%Z -> (kz = 0%Z -> j = 0%Z -> znth x 0 = 0%Z) -> (kz = 2045%Z -> j = 0%Z) ->
dfK_pad 53 (-1074) sign fR lrp lnz j kz x = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 lrp) (Z_to_bv 64 kz) x25 (Z_to_bv 64 j) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd93d4) fct None m (seg_rom usegs)).

Definition S_R : Prop := forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w80 : word) ev ws sign k c (x : list Z) (lrp dc lnz j kz : Z),
let _ := ctx_all in
dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 (le8 (Z_to_bv 64 lnz)) ev ws sign fR -> RFJ' k c fR -> (0 <= k)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z ->
xrel ws x (digz kz j) -> X31 x ->
(0 <= j <= 8)%Z -> (0 <= kz <= 2045)%Z -> (0 <= dc < 2^31)%Z -> (0 <= lnz < 2^31)%Z -> (znth x 0 <> 0%Z -> 1 <= lnz)%Z ->
(j <> 0%Z -> znth x kz < 10 ^ j)%Z -> (kz = 0%Z -> j = 0%Z -> znth x 0 = 0%Z) -> (kz = 2045%Z -> j = 0%Z) -> (-2^62 <= lrp < 2^62)%Z ->
(znth x 0 <> 0%Z -> w80 = Z_to_bv 64 18396) ->
dfK_rng 53 (-1074) sign fR lrp dc lnz j kz x = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 dc) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 lrp) (Z_to_bv 64 kz) x25 (Z_to_bv 64 j) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd92d8) fct None m (seg_rom usegs)).

Definition dig_facts (ws : list word) (x : list Z) (j kz dc lnz : Z) : Prop :=
xrel ws x (digz kz j) /\ X31 x /\
(0 <= j <= 8)%Z /\ (0 <= kz <= 2045)%Z /\ (0 <= dc < 2^31)%Z /\ (0 <= lnz < 2^31)%Z /\ (znth x 0 <> 0%Z -> 1 <= lnz)%Z /\
(j <> 0%Z -> znth x kz < 10 ^ j)%Z /\ (kz = 0%Z -> j = 0%Z -> znth x 0 = 0%Z) /\ (kz = 2045%Z -> j = 0%Z).

Definition S_C38 : Prop := forall m (x1 x5 x6 x7 x8 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w80 : word) ev ws sign kmin c (x : list Z) (f : shfile) (lrp dc lnz j kz gotdig ng : Z),
let _ := ctx_all in
dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 (le8 (Z_to_bv 64 lnz)) ev ws sign f -> RFJ' kmin c f -> (0 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
dig_facts ws x j kz dc lnz -> (znth x 0 <> 0%Z -> w80 = Z_to_bv 64 18396) ->
(0 <= gotdig <= 1)%Z -> ng = Z.b2z (gotdig =? 0)%Z -> (-2^62 <= lrp < 2^62)%Z ->
(if negb (nz gotdig) then Some (sh_lim0 f, f128_of_i32 0) else dfK_rng 53 (-1074) sign f lrp dc lnz j kz x) = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 dc) x10 (Z_to_bv 64 ng) x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 Fp) x22 (Z_to_bv 64 lrp) (Z_to_bv 64 kz) x25 (Z_to_bv 64 j) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd922c) fct None m (seg_rom usegs)).

Definition S_C2C : Prop := forall m (x1 x5 x6 x7 x8 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w80 : word) ev ws sign kmin c (x : list Z) (f : shfile) (lrp dc lnz j kz gotdig ng : Z),
let _ := ctx_all in
dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 (le8 (Z_to_bv 64 lnz)) ev ws sign f -> RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> sh_shlim_neg f = false ->
dig_facts ws x j kz dc lnz -> (znth x 0 <> 0%Z -> w80 = Z_to_bv 64 18396) ->
(0 <= gotdig <= 1)%Z -> ng = Z.b2z (gotdig =? 0)%Z -> (-2^62 <= lrp < 2^62)%Z ->
(if negb (nz gotdig) then Some (sh_lim0 (sh_unget f), f128_of_i32 0) else dfK_rng 53 (-1074) sign (sh_unget f) lrp dc lnz j kz x) = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 dc) x10 (Z_to_bv 64 ng) x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 Fp) x22 (Z_to_bv 64 lrp) (Z_to_bv 64 kz) x25 (Z_to_bv 64 j) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9220) fct None m (seg_rom usegs)).

Definition S_E : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w80 : word) ev ws sign kmin c (x : list Z) (f : shfile) (lrp dc lnz j kz gotdig gotrad : Z),
let _ := ctx_all in
dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 (le8 (Z_to_bv 64 lnz)) ev ws sign f -> RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
dig_facts ws x j kz dc lnz -> (znth x 0 <> 0%Z -> w80 = Z_to_bv 64 18396) ->
(0 <= gotdig <= 1)%Z -> (0 <= gotrad <= 1)%Z -> (- 2^31 <= lrp < 2^31)%Z ->
dfK_exp fuelc 53 (-1074) sign pok (mkDL f c j kz lrp dc lnz gotdig gotrad x) = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 dc) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) x22 x23 (Z_to_bv 64 kz) (Z_to_bv 64 lrp) (Z_to_bv 64 j) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd90a8) fct None m (seg_rom usegs)).

Definition digI (ws : list word) (x : list Z) (f : shfile) (c j k lrp dc lnz gotdig gotrad : Z) : Prop :=
xrel ws x (digz k j) /\ X31 x /\ (0 <= j <= 8)%Z /\ (0 <= k)%Z /\ (9 * k + j <= dc)%Z /\
(0 <= dc <= sh_rpos f)%Z /\ (c <> (-1)%Z -> dc + 1 <= sh_rpos f)%Z /\
(0 <= lnz <= dc)%Z /\ (znth x 0 <> 0%Z -> 1 <= lnz)%Z /\ (j <> 0%Z -> znth x k < 10 ^ j)%Z /\ (k = 0%Z -> j = 0%Z -> znth x 0 = 0%Z) /\
(- 2^31 <= lrp < 2^31)%Z /\ (0 <= gotdig <= 1)%Z /\ (0 <= gotrad <= 1)%Z /\
(k <= 2045)%Z /\ (k = 2045%Z -> j = 0%Z).

Definition SDn (n : nat) : Prop := forall m (x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) Ft fct
j0 ev ws sign kmin c (x : list Z) (f : shfile) (j k lrp dc lnz gotdig gotrad : Z) (s' : st_dig),
let _ := ctx_all in
dfinv m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) (le8 (Z_to_bv 64 lnz)) ev ws sign f -> RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
digI ws x f c j k lrp dc lnz gotdig gotrad ->
(isdigitc c || (c =? 46))%Z = true ->
df_dig_loop n (mkDL f c j k lrp dc lnz gotdig gotrad x) = Some s' ->
dfK_exp fuelc 53 (-1074) sign pok s' = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 48) (Z_to_bv 64 dc) (Z_to_bv 64 c) (Z_to_bv 64 (c + -48)) (Z_to_bv 64 (Z.b2z (c =? 46)%Z)) x13 x14 x15 x16 x17
(Z_to_bv 64 (q + -136)) (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) (Z_to_bv 64 10) (Z_to_bv 64 46) (Z_to_bv 64 k) (Z_to_bv 64 lrp) (Z_to_bv 64 j) (Z_to_bv 64 2044) x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9160) fct None m (seg_rom usegs)).
Definition S_D : Prop := forall n, SDn n.

Definition winv (m : word -> option byte) (j0 : list byte) (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) (ev : word)
(ws : list word) (f : shfile) : Prop :=
finv m /\ framL j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev m
/\ u32arr usegs m XA ws /\ length ws = 2048%nat /\ rw_cells usegs m Fp (rf_cells T p true f J).
#[using="Type"] Lemma winv_dfinvG : forall m j0 w16 w24 w80 b96 ev ws sign f,
winv m j0 (Z_to_bv 64 1021) w16 w24 (Z_to_bv 64 1) (Z_to_bv 64 (-1074)) (Z_to_bv 64 1074) (Z_to_bv 64 53) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w80 (Z_to_bv 64 ssp_guard) b96 ev ws f
= dfinvG m j0 w16 w24 w80 b96 ev ws sign f.
Proof. reflexivity. Qed.

Definition X0 : list Z := zupd (zrepeat 0 KMAX) 0 0.

Definition fch (c : Z) : Prop := is_numch c = true \/ c = 0%Z \/ c = (-1)%Z.

Definition S_B0C : Prop := forall m (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x22 x24 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w80 : word) (b96 : list byte) ev ws sign kmin c (f : shfile) (lrp gotdig gotrad : Z),
let _ := ctx_all in
dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 b96 ev ws sign f -> RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> wval ws 0 = 0%Z ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> (- sh_rpos f <= lrp <= 0)%Z -> (0 <= gotdig <= 1)%Z -> (0 <= gotrad <= 1)%Z ->
(isdigitc c || (c =? 46))%Z = true ->
dfK_dig fuelc 53 (-1074) sign pok (mkDL f c 0 0 lrp 0 0 gotdig gotrad X0) = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 c) (Z_to_bv 64 (c + -48)) x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 46) x24 (Z_to_bv 64 lrp) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9100) fct None m (seg_rom usegs)).

Definition S_A9C : Prop := forall m (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x22 x24 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w80 : word) (b96 : list byte) ev ws sign kmin c (f : shfile) (lrp gotdig gotrad : Z),
let _ := ctx_all in
dfinvG m j0 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w80 b96 ev ws sign f -> RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 -> wval ws 0 = 0%Z ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> (- sh_rpos f <= lrp <= 0)%Z -> (0 <= gotdig <= 1)%Z -> (0 <= gotrad <= 1)%Z ->
c <> 46%Z ->
dfK_dig fuelc 53 (-1074) sign pok (mkDL f c 0 0 lrp 0 0 gotdig gotrad X0) = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 c) (Z_to_bv 64 (c + -48)) x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 gotdig) (Z_to_bv 64 gotrad) (Z_to_bv 64 Fp) x22 (Z_to_bv 64 46) x24 (Z_to_bv 64 lrp) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9090) fct None m (seg_rom usegs)).

Definition S_A44 : Prop := forall m (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x22 x23 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w32 w48 w80 : word) (b96 : list byte) ev ws sign kmin c (f : shfile) (lrp gotdig : Z),
let _ := ctx_all in
winv m j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 (Z_to_bv 64 (-1074)) w48 (Z_to_bv 64 53) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w80 (Z_to_bv 64 ssp_guard) b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> (- sh_rpos f <= lrp <= 0)%Z -> (0 <= gotdig <= 1)%Z -> c <> 48%Z ->
dfK_dig fuelc 53 (-1074) sign pok (mkDL f c 0 0 lrp 0 0 gotdig 1 X0) = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 x9 (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 gotdig) x20 (Z_to_bv 64 Fp) x22 x23 (Z_to_bv 64 1) (Z_to_bv 64 lrp) (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9038) fct None m (seg_rom usegs)).

#[using="Type"] Lemma df_dig_loop_step : forall n s, df_dig_loop (S n) s = if df_dig_cond s then match df_dig_body s with inl s' => df_dig_loop n s' | inr s' => Some s' end else Some s.
Proof. reflexivity. Qed.
#[using="Type"] Lemma df_rz_loop_step : forall n g l c f, df_rz_loop (S n) (g, l, c, f) =
(if c =? 48 then df_rz_loop n (1, l - 1, fst (sh_getc f), snd (sh_getc f)) else Some (g, l, c, f))%Z.
Proof. clear. intros. cbn [df_rz_loop df_rz_body]. destruct (sh_getc f). reflexivity. Qed.
#[using="Type"] Lemma df_lz_loop_step : forall n g c f, df_lz_loop (S n) (g, c, f) =
(if c =? 48 then df_lz_loop n (1, fst (sh_getc f), snd (sh_getc f)) else Some (g, c, f))%Z.
Proof. clear. intros. cbn [df_lz_loop df_lz_body]. destruct (sh_getc f). reflexivity. Qed.

Definition SRZn (n : nat) : Prop := forall m (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w32 w48 w80 : word) (b96 : list byte) ev ws sign kmin (f : shfile) (lrp g : Z) (g' lrp' c' : Z) (f' : shfile),
let _ := ctx_all in
winv m j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 (Z_to_bv 64 (-1074)) w48 (Z_to_bv 64 53) (Z_to_bv 64 pok) (Z_to_bv 64 sign) w80 (Z_to_bv 64 ssp_guard) b96 ev ws f ->
RFJ' kmin 48 f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(1 - sh_rpos f <= lrp <= 0)%Z ->
df_rz_loop n (g, lrp, 48, f)%Z = Some (g', lrp', c', f') ->
dfK_dig fuelc 53 (-1074) sign pok (mkDL f' c' 0 0 lrp' 0 0 g' 1 X0) = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 48) x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 Fp) x22 x23 (Z_to_bv 64 1) (Z_to_bv 64 lrp) (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9014) fct None m (seg_rom usegs)).
Definition S_RZ : Prop := forall n, SRZn n.

Definition S_9EC : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile) (gotdig : Z) (g' lrp' c' : Z) (f' : shfile),
let _ := ctx_all in
winv m j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> (0 <= gotdig <= 1)%Z ->
df_rz_loop fuelc (gotdig, 0, c, f)%Z = Some (g', lrp', c', f') ->
dfK_dig fuelc 53 (-1074) sign pok (mkDL f' c' 0 0 lrp' 0 0 g' 1 X0) = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) (Z_to_bv 64 gotdig) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd8fe0) fct None m (seg_rom usegs)).

Definition S_A64 : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> c <> 46%Z ->
dfK_dig fuelc 53 (-1074) sign pok (mkDL f c 0 0 0 0 0 1 0 X0) = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd9058) fct None m (seg_rom usegs)).

Definition S_7F4 : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 (Z_to_bv 64 1021) (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> c <> 46%Z ->
dfK_dig fuelc 53 (-1074) sign pok (mkDL f c 0 0 0 0 0 0 0 X0) = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 c) (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd8de8) fct None m (seg_rom usegs)).

Definition S_9C8 : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 w8 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> c <> 48%Z ->
dfK_rz fuelc 53 (-1074) sign pok 1 c f = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) (Z_to_bv 64 1021) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd8fbc) fct None m (seg_rom usegs)).

Definition SLZn (n : nat) : Prop := forall m (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin (f : shfile) (g : Z) (g' c' : Z) (f' : shfile),
let _ := ctx_all in
winv m j0 w8 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin 48 f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
df_lz_loop n (g, 48, f)%Z = Some (g', c', f') ->
dfK_rz fuelc 53 (-1074) sign pok g' c' f' = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 (Z_to_bv 64 48) (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) (Z_to_bv 64 1021) (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd8fa0) fct None m (seg_rom usegs)).
Definition S_LZ : Prop := forall n, SLZn n.

Definition S_990 : Prop := forall (n : nat) m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x25 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile) (g' c' : Z) (f' : shfile),
let _ := ctx_all in
winv m j0 w8 (Z_to_bv 64 (lo64 zero0)) (Z_to_bv 64 (hi64 zero0)) w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z ->
df_lz_loop n (1, c, f)%Z = Some (g', c', f') ->
dfK_rz fuelc 53 (-1074) sign pok g' c' f' = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 (Z_to_bv 64 1074) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd8f84) fct None m (seg_rom usegs)).

Definition S_848 : Prop := forall m (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (2 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
decfloat fuelc (sh_unget f) 48 53 (-1074) sign pok = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd8e3c) fct None m (seg_rom usegs)).

Definition S_6F8 : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z -> c <> 48%Z ->
decfloat fuelc f c 53 (-1074) sign pok = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd8cec) fct None m (seg_rom usegs)).

Definition FS_tail (sign c : Z) (f : shfile) : option (shfile * Z) :=
if (c =? 48)%Z then
let '(c2, f2) := sh_getc f in
if (Z.lor c2 32 =? 120)%Z then None else decfloat fuelc (sh_unget f2) 48 53 (-1074) sign pok
else decfloat fuelc f c 53 (-1074) sign pok.

Definition S_618 : Prop := forall m (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x25 x26 x27 x28 x29 x30 x31 : word) Ft fct
j0 (w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 : word) (b96 : list byte) ev ws sign kmin c (f : shfile),
let _ := ctx_all in
winv m j0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 b96 ev ws f ->
RFJ' kmin c f -> (1 <= kmin)%Z -> Fok Ft -> frm0 fct ->
(sign = 1 \/ sign = -1)%Z -> sh_stdio f = sh_stdio f0 ->
(c <> (-1)%Z -> 1 <= sh_rpos f)%Z ->
FS_tail sign c f = Some (fR, yR) ->
evt usegs POST
(MS (mkR x1 SPv gp TPv x5 x6 x7 x8 (Z_to_bv 64 sign) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 53) x19 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 Fp) (Z_to_bv 64 (-1074)) (Z_to_bv 64 pok) (Z_to_bv 64 1) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0xd8c0c) fct None m (seg_rom usegs)).
End Floatscan.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w QDUx.Mq0 Q9Ay.Mq3 Q9Ay.Mq4 Q9Ay.Mq5 Q9Ay.Mq6 Q9Ay.Mq7 Q9Ay.Mq8 QyjG QJE4.Mq3.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq4 Q98Z.Mq5 QkLq QkLq.Mq3 QnOf QdZ1 Qv4L.Mqk QQbX Qn9M Qv4L Qi8L.Mq9 QdZ1.Mq7 QQbX.Mq6 Qv4L.Mqb QnkH QnkH.Mqm.
Import QmBS.Mq6 Qlfl Qkaz.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rta_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
lo <= a < sp
\/ RCTX <= a < RCTX + 928
\/ (exists q, meta_slot st q /\ conc st q <= a < conc st q + 40)
\/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 9).

#[using="Type"] Lemma rta_fp_stack st lo sp a : lo <= a < sp -> rta_fp st lo sp a. Proof. intros; left; assumption. Qed.
#[using="Type"] Lemma rta_fp_ctx st lo sp a : RCTX <= a < RCTX + 928 -> rta_fp st lo sp a. Proof. intros; right; left; assumption. Qed.
#[using="Type"] Lemma rta_fp_meta st lo sp a q : meta_slot st q -> conc st q <= a < conc st q + 40 -> rta_fp st lo sp a.
Proof. intros; do 2 right; left. exists q; auto. Qed.
#[using="Type"] Lemma rta_fp_grp st lo sp a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 9 -> rta_fp st lo sp a.
Proof. intros; do 3 right. exists b, gh; auto. Qed.

Section PHASE.
Context {R : Type}.
Variables (K : mstate -> Z -> QUZl.M R) (bail : QUZl.M R).
Variables (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (st : mstate) (m : mem) (sc lo : Z).

Variables (ra sp gp tp t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Hypothesis TAF : taf st sc.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 144.
Let spv := bv_unsigned sp.
Let RR (t0 t1 a0 a1' a2 a3 a4 a5 a6 a7 : word) :=
rt1_regs sc ra (Z_to_bv 64 (spv + -144)) gp tp t0 t1 t2 s1 a0 a1' a2 a3 a4 a5 a6 a7 a1 s3 s8 s9 s10 s11 t3 t4 t5 t6.
Let FRM (junk : list byte) := rta_frame junk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra.

Hypothesis HK1 : forall stX g3 msk k m' (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word),
ta_rel sc st stX -> active stX sc = Some g3 -> gmf st sc g3 ->
msk = m_avail (get_meta_rec stX g3) -> 0 < msk < 2^32 -> lowbit msk = 2 ^ k -> 0 <= k < 32 ->
rmrep (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) m' -> mem_inv usegs m' -> stk usegs m' lo spv ->
rpres_except (rta_fp st lo spv) m m' ->
rimplT o (K (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) (lowbit msk)) s Q
(MS (mkR ra sp gp tp t0' t1' t2 s0 s1 (wz k) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)).

#[using="CLO LO HK1"] Lemma rfin_block : forall stX g3 msk mZ (t0 t1 a2 a3 a4 a5 a6 a7 : word) (junk : list byte),
ta_rel sc st stX -> active stX sc = Some g3 -> gmf st sc g3 ->
msk = m_avail (get_meta_rec stX g3) -> 0 < msk < 2^32 ->
rmrep stX mZ -> mem_inv usegs mZ -> rw_cells usegs mZ (spv + -144) (FRM junk) -> stk usegs mZ lo (spv + -144) ->
rpres_except (rta_fp st lo spv) m mZ ->
rimplT o (ta_fin stX g3 msk K) s Q
(MS (RR t0 t1 (Z_to_bv 64 (conc st g3)) (wz (sxv msk)) a2 a3 a4 a5 a6 a7) F (Z_to_bv 64 0xd1204) fc None mZ (seg_rom usegs)).
Proof.
intros until junk. intros TR HA GM HM MR0 MRZ MIZ FRZ STZ PEZ.
destruct (gmf_geom st stX sc g3 TR GM) as (MSZ & RAZ & RFZ & MWZ & EM & ELI & ESC & EFB & ECONC).
pose proof (rmeta_slot_bounds st m g3) as GB0.
pose proof (rmeta_slot_bounds stX mZ g3 MRZ MSZ) as (Gpos & GC & GI & _ & _).
destruct (lowbit_facts msk ltac:(lia)) as (k & Hk & LB).
unfold ta_fin. riprefixT. unfold RR, rt1_regs.
eapply evt_mono.
{ eapply (rfin_walk stX mZ g3 msk lo MRZ MSZ ltac:(lia) CLO); [| exact FRZ| exact STZ| unfold spv; lia| exact MIZ].
rewrite unsigned_lit by lia. symmetry; exact ECONC. }
cbv beta. intros ms' (a1' & a2' & a3' & m' & k' & Hk' & LB' & -> & MU & WM & MI' & ST' & MR').
assert (k' = k) by (rewrite LB in LB'; apply Z.pow_inj_r in LB'; lia). subst k'.
eapply (HK1 stX g3 msk k m'); try eassumption; try lia.
eapply rpres_except_trans; [exact PEZ|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
cbn [ivs_covered]. split; [|split; [|exact I]].
- intros x Hx. apply rta_fp_stack. unfold spv in *; lia.
- intros x Hx. eapply rta_fp_meta; [exact (gmf_slot _ _ _ GM)|]. rewrite <- ECONC. lia.
Qed.

#[using="TAF SC CLO LO HK1"] Lemma ravz_block : forall (pc : Z) stZ g3 mZ (t0 t1 a1' a2 a3 a4 a5 a6 a7 : word) (junk : list byte),
(pc = 0xd1180 \/ pc = 0xd118c) ->
ta_rel sc st stZ -> active stZ sc = Some g3 -> gmf st sc g3 ->
rmrep stZ mZ -> mem_inv usegs mZ -> rw_cells usegs mZ (spv + -144) (FRM junk) -> stk usegs mZ lo (spv + -144) ->
rpres_except (rta_fp st lo spv) m mZ ->
rimplT o (ta_avz K bail stZ g3) s Q
(MS (RR t0 t1 (Z_to_bv 64 (conc st g3)) a1' a2 a3 a4 a5 a6 a7) F (Z_to_bv 64 pc) fc None mZ (seg_rom usegs)).
Proof.
intros until junk. intros PC TR HA GM MRZ MIZ FRZ STZ PEZ.
destruct (gmf_geom st stZ sc g3 TR GM) as (MSZ & RAZ & RFZ & MWZ & EM & ELI & ESC & EFB & ECONC).
pose proof (rmeta_slot_bounds stZ mZ g3 MRZ MSZ) as (Gpos & GC & GI & _ & _).
destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & Hgh & GMg & AIR & SC0 & UNK).
destruct (proj2 (tr_groups _ _ _ TR b) (ex_intro _ gh Hgh)) as [gh1 Hgh1].
destruct (tr_gmeta _ _ _ TR b gh1 Hgh1) as (gh' & Hgh' & GM1 & AI1). rewrite Hgh in Hgh'. inversion Hgh'; subst gh'.
pose proof (gmf_mw _ _ _ GM) as (LI0 & _ & _ & _).
assert (AI1R : 0 <= g_active_idx gh1 <= 31) by (destruct AI1 as [?|[? ?]]; lia).
unfold ta_avz, activate_group.
destruct (m_avail (get_meta_rec stZ g3) =? 0) eqn:AV0; [|unfold guard; apply rimplT_undef].
apply Z.eqb_eq in AV0. unfold guard at 1. cbv beta.
rewrite EM, Hmem. cbn [default].
replace (group_active_idx stZ b) with (g_active_idx gh1).
2:{ unfold group_active_idx, get_group. rewrite Hgh1. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity. }
set (act := mask_upto (g_active_idx gh1)). set (f := m_freed (get_meta_rec stZ g3)).
destruct (Z.land f act =? 0) eqn:MZ; unfold guard; cbn [negb]; [apply rimplT_undef|].
apply Z.eqb_neq in MZ.
rewrite get_meta_rec_upd_same. cbn [m_sizeclass m_set_avail m_set_freed].
assert (EMb : m_mem (get_meta_rec stZ g3) = Some b) by (rewrite EM; exact Hmem).
assert (HG : bv_unsigned (Z_to_bv 64 (conc st g3)) = conc stZ g3) by (rewrite unsigned_lit by lia; symmetry; exact ECONC).

unfold RR.
eapply (rimplT_evt o _ _ _ (fun ms' => exists a1x : word, ms' = MS (rt1_regs sc ra (Z_to_bv 64 (spv + -144)) gp tp t0 t1 t2 s1 (Z_to_bv 64 (conc st g3)) a1x a2 a3 a4 a5 a6 a7 a1 s3 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xd118c) fc None mZ (seg_rom usegs))).
{ destruct PC as [-> | ->].
- eapply evt_mono. { eapply (ravz_pre_walk stZ mZ g3 sc MRZ MSZ AV0); [exact HG| exact MIZ]. } cbv beta. intros ms' ->. eexists. reflexivity.
- apply evt_done. eexists. reflexivity. }
intros ms0 [a1x ->].
riprefixT. eapply evt_mono.
{ eapply (ravz_walk stZ mZ g3 b gh1 sc MRZ MSZ AV0 EMb Hgh1 AI1R RFZ MWZ MZ); [| exact SC| exact HG| exact MIZ].
intros i. pose proof (taf_bnc _ _ TAF i) as B0. pose proof (tr_bounces _ _ _ TR i ltac:(lia)). lia. }
cbv beta. intros ms' (a2' & a3' & a4' & a5' & a6' & a7' & m5 & -> & MU & WM & MI5 & MR5).
set (st4 := upd_meta g3 (fun r : meta => m_set_avail (Z.land f act) (m_set_freed (Z.ldiff f act) r)) stZ) in *.
set (st5 := decay_bounces (m_sizeclass (get_meta_rec stZ g3)) st4) in *.
assert (TR4 : ta_rel sc st st4).
{ eapply ta_rel_trans; [exact TR|]. unfold st4. rewrite upd_meta_put. apply ta_rel_put_meta.
- repeat split; reflexivity.
- cbn [m_avail m_freed m_set_avail m_set_freed]. intros i Hi Hb. fold f.
apply orb_prop in Hb. rewrite AV0, Z.bits_0. cbn [orb].
destruct Hb as [Hb|Hb]; [rewrite Z.land_spec in Hb| rewrite Z.ldiff_spec in Hb]; apply andb_prop in Hb; destruct Hb as [Hb _]; exact Hb.
- cbn [m_avail m_freed m_set_avail m_set_freed]. fold f. intros _ Hf.
pose proof (land_upper f act ltac:(lia) ltac:(unfold act, mask_upto; pose proof (Z.pow_pos_nonneg 2 (g_active_idx gh1 + 1)); lia)).
pose proof (ldiff_le f act ltac:(lia) ltac:(unfold act, mask_upto; pose proof (Z.pow_pos_nonneg 2 (g_active_idx gh1 + 1)); lia)).
pose proof (Z.ldiff_nonneg f act). lia. }
assert (TR5 : ta_rel sc st st5).
{ eapply ta_rel_trans; [exact TR4|]. unfold st5. apply ta_rel_decay.
pose proof (taf_bnc _ _ TAF (m_sizeclass (get_meta_rec stZ g3) - 7)). pose proof (tr_bounces _ _ _ TR4 (m_sizeclass (get_meta_rec stZ g3) - 7) ltac:(lia)). lia. }
assert (FR5 : rw_cells usegs m5 (spv + -144) (FRM junk)).
{ eapply rw_cells_transport; [exact FRZ| exact MU| exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia. }
assert (ST5 : stk usegs m5 lo (spv + -144)).
{ eapply stk_transport_disjoint; [exact STZ| exact MU| exact WM|]. apply disjoint_high; [|lia].
intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia. }
eapply (rfin_block st5 g3 (Z.land f act) m5 t0 t1 a2' a3' a4' a5' a6' a7' junk);
[exact TR5| | exact GM| | | exact MR5| exact MI5| exact FR5| exact ST5|].
- unfold st5. rewrite active_decay. unfold st4. rewrite active_upd_meta. exact HA.
- unfold st5. rewrite rec_decay. unfold st4. rewrite get_meta_rec_upd_same. reflexivity.
- pose proof (land_upper f act ltac:(lia) ltac:(unfold act, mask_upto; pose proof (Z.pow_pos_nonneg 2 (g_active_idx gh1 + 1)); lia)). lia.
- eapply rpres_except_trans; [exact PEZ|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
cbn [ivs_covered]. split; [|split; [|exact I]].
+ intros x Hx. eapply rta_fp_meta; [exact (gmf_slot _ _ _ GM)|]. rewrite <- ECONC. lia.
+ intros x Hx. apply rta_fp_ctx. unfold RCTX in *. lia.
Qed.

#[using="TAF SC CLO LO HK1"] Lemma ract_block : forall stY g2 msk mY (t0 t1 a1' a2 a5 a6 a7 : word) (junk : list byte),
ta_rel sc st stY -> active stY sc = Some g2 -> gmf st sc g2 ->
msk = m_freed (get_meta_rec stY g2) ->
(forall mn, m_next (get_meta_rec stY g2) = Some mn -> gmf st sc mn) ->
m_next (get_meta_rec stY g2) <> None ->
rmrep stY mY -> mem_inv usegs mY -> rw_cells usegs mY (spv + -144) (FRM junk) -> stk usegs mY lo (spv + -144) ->
rpres_except (rta_fp st lo spv) m mY ->
rimplT o (ta_act sc K bail stY g2 msk) s Q
(MS (RR t0 t1 (Z_to_bv 64 (conc st g2)) a1' a2 (wz (sxv msk)) (Z_to_bv 64 2) a5 a6 a7) F (Z_to_bv 64 0xd1158) fc None mY (seg_rom usegs)).
Proof.
intros until junk. intros TR HA GM HM GN NN MRY MIY FRY STY PEY.
destruct (gmf_geom st stY sc g2 TR GM) as (MSY & RAY & RFY & MWY & EM & ELI & ESC & EFB & ECONC).
pose proof (rmeta_slot_bounds stY mY g2 MRY MSY) as (Gpos & GC & GI & _ & _).
destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & Hgh & GMg & AIR & SC0 & UNK).
destruct (proj2 (tr_groups _ _ _ TR b) (ex_intro _ gh Hgh)) as [gh1 Hgh1].
destruct (tr_gmeta _ _ _ TR b gh1 Hgh1) as (gh' & Hgh' & GM1 & AI1). rewrite Hgh in Hgh'. inversion Hgh'; subst gh'.
pose proof (gmf_mw _ _ _ GM) as (LI0 & _ & SCR0 & _).
assert (AI1R : 0 <= g_active_idx gh1 <= 31) by (destruct AI1 as [?|[? ?]]; lia).
assert (EMb : m_mem (get_meta_rec stY g2) = Some b) by (rewrite EM; exact Hmem).
assert (MSKR : 0 <= msk < 2^32) by (rewrite HM; exact RFY).
assert (HG : bv_unsigned (Z_to_bv 64 (conc st g2)) = conc stY g2) by (rewrite unsigned_lit by lia; symmetry; exact ECONC).
unfold ta_act. rewrite EMb. cbn [default].
replace (group_active_idx stY b) with (g_active_idx gh1).
2:{ unfold group_active_idx, get_group. rewrite Hgh1. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity. }
unfold RR.
destruct (Z.land msk (mask_upto (g_active_idx gh1)) =? 0) eqn:ZR.
-
apply Z.eqb_eq in ZR.
destruct (m_next (get_meta_rec stY g2)) as [mn|] eqn:GNY; [|exfalso; apply NN; reflexivity].
cbn [optr_eqb]. destruct (aptr_eqb mn g2) eqn:EQ; cbn [negb].
+
apply aptr_eqb_eq in EQ. subst mn.
destruct (Z.eq_dec (m_sizeclass (get_meta_rec st g2)) 0) as [SCZ|SCNZ].
*
assert (AIE : g_active_idx gh1 = m_last_idx (get_meta_rec st g2)).
{ destruct AI1 as [E|[_ P]]; [rewrite E; apply SC0; exact SCZ| exfalso; exact (P g2 GMg SCZ)]. }
assert (MZ : msk = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0.
destruct (Z.testbit msk i) eqn:Ti; [|reflexivity]. exfalso.
assert (IL : i <= m_last_idx (get_meta_rec st g2)).
{ pose proof (tr_bits _ _ _ TR g2 i Hi) as TB. rewrite <- HM, Ti in TB. rewrite orb_true_r in TB. specialize (TB eq_refl).
apply orb_prop in TB. destruct TB as [TB|TB]; [exact (gmf_abits _ _ _ GM i Hi TB)| exact (gmf_fbits _ _ _ GM i Hi TB)]. }
assert (TB2 : Z.testbit (Z.land msk (mask_upto (g_active_idx gh1))) i = true).
{ rewrite Z.land_spec, Ti. unfold mask_upto. replace (2 ^ (g_active_idx gh1 + 1) - 1) with (Z.ones (g_active_idx gh1 + 1)) by (rewrite Z.ones_equiv; lia).
rewrite Z.testbit_ones_nonneg by lia. cbn [andb]. apply Z.ltb_lt. lia. }
rewrite ZR, Z.bits_0 in TB2. discriminate. }

cbv zeta iota beta. unfold ta_avz, activate_group. rewrite rec_set_gai.
destruct (m_avail (get_meta_rec stY g2) =? 0); unfold guard; [|apply rimplT_undef].
cbv beta. rewrite <- HM, MZ, Z.land_0_l. cbn [Z.eqb negb]. apply rimplT_undef.
*
destruct (m_avail (get_meta_rec stY g2) =? 0) eqn:AV0.
2:{ cbv zeta iota beta. unfold ta_avz, activate_group. rewrite rec_set_gai, AV0. unfold guard. apply rimplT_undef. }
apply Z.eqb_eq in AV0.
assert (SCY : 1 <= m_sizeclass (get_meta_rec stY g2) < 48) by (rewrite ESC; pose proof (gmf_sc48 _ _ _ GM); lia).
rewrite <- ECONC. riprefixT. eapply evt_mono.
{ eapply (ract_span_walk stY mY g2 b gh1 sc msk MRY MSY EMb Hgh1 AI1R); [exact ZR| exact GNY| exact MWY| exact SCY| | rewrite GM1; exact GMg| exact AV0| exact MIY].
intros o' Ho'. rewrite (tr_get_shadow _ _ _ _ TR). apply UNK. exact Ho'. }
cbv beta. intros ms' (t0' & t1' & a1'' & a2' & a3' & a4' & a5' & a6' & a7' & m5 & -> & MU & WM & MI5 & MR5).
cbv zeta iota beta.
match goal with |- rimplT _ (ta_avz _ _ ?st3 _) _ _ _ => set (stG := st3) in * end.
assert (TRG : ta_rel sc st stG).
{ eapply ta_rel_trans; [exact TR|]. apply ta_rel_set_gai.
- apply land31_range.
- intros h g' Hh Hg'. rewrite Hgh1 in Hh. inversion Hh; subst h. rewrite GM1 in Hg'. rewrite GMg in Hg'. inversion Hg'; subst g'. lia. }
rewrite (tr_conc _ _ _ g2 TR).
eapply (ravz_block 0xd118c stG g2 m5); [right; reflexivity| exact TRG| | exact GM| exact MR5| exact MI5| | |].
-- unfold stG. rewrite active_set_gai. exact HA.
-- eapply rw_cells_transport; [exact FRY| exact MU| exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
pose proof (rgroup_bounds stY mY b gh1 MRY Hgh1) as (B0 & BC & _).
intros lo' hi' [E|[]]; inversion E; subst; unfold alloc_ceiling in *; lia.
-- eapply stk_transport_disjoint; [exact STY| exact MU| exact WM|]. apply disjoint_high; [|lia].
pose proof (rgroup_bounds stY mY b gh1 MRY Hgh1) as (B0 & BC & _).
intros lo' hi' [E|[]]; inversion E; subst; unfold alloc_ceiling in *; lia.
-- eapply rpres_except_trans; [exact PEY|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
cbn [ivs_covered]. split; [|exact I]. intros x Hx. eapply (rta_fp_grp st lo spv x b gh Hgh). rewrite <- (tr_conc _ _ _ b TR). lia.
+
assert (NE : mn <> g2) by (intros ->; rewrite (proj2 (aptr_eqb_eq g2 g2) eq_refl) in EQ; discriminate).
pose proof (GN mn eq_refl) as GMn.
destruct (gmf_geom st stY sc mn TR GMn) as (MSn & _ & _ & _ & _ & _ & _ & _ & ECONCn).
rewrite <- ECONC. riprefixT. eapply evt_mono.
{ eapply (ract_next_walk stY mY g2 b gh1 sc msk MRY MSY SC EMb Hgh1 AI1R); [exact ZR| exact GNY| exact NE| exact MSn| exact MIY]. }
cbv beta. intros ms' (a1'' & a2' & a3' & a4' & m5 & -> & MU & WM & MI5 & MR5).
assert (TRN : ta_rel sc st (set_active sc (Some mn) stY)) by (eapply ta_rel_trans; [exact TR| apply ta_rel_set_active]).
rewrite ECONCn.
eapply (ravz_block 0xd1180 (set_active sc (Some mn) stY) mn m5); [left; reflexivity| exact TRN| | exact GMn| exact MR5| exact MI5| | |].
-- rewrite active_set_active, Z.eqb_refl. reflexivity.
-- eapply rw_cells_transport; [exact FRY| exact MU| exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia.
-- eapply stk_transport_disjoint; [exact STY| exact MU| exact WM|]. apply disjoint_high; [|lia].
intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia.
-- eapply rpres_except_trans; [exact PEY|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rta_fp_ctx. unfold RCTX in *. lia.
-
apply Z.eqb_neq in ZR.
rewrite <- ECONC. riprefixT. eapply evt_mono.
{ eapply (ract_skip_walk stY mY g2 b gh1 sc msk MRY MSY EMb Hgh1 AI1R MSKR); [exact ZR| exact MIY]. }
cbv beta. intros ms' (a1'' & a2' & a3' & a4' & ->). rewrite ECONC.
eapply (ravz_block 0xd1180 stY g2 mY); [left; reflexivity| ..]; eassumption.
Qed.

Definition rnclosed (stX : mstate) (P : aptr -> Prop) : Prop :=
forall q, P q -> gmf st sc q /\ exists t, m_next (get_meta_rec stX q) = Some t /\ P t.

#[using="TAF SC CLO LO HK1"] Lemma rm_block : forall stX g1 mX (P : aptr -> Prop) (t0 t1 a1' a2 a3 a4 a5 a6 a7 : word) (junk : list byte),
ta_rel sc st stX -> active stX sc = Some g1 -> rnclosed stX P -> P g1 ->
rmrep stX mX -> mem_inv usegs mX -> rw_cells usegs mX (spv + -144) (FRM junk) -> stk usegs mX lo (spv + -144) ->
rpres_except (rta_fp st lo spv) m mX ->
rimplT o (ta_m sc K bail stX g1) s Q
(MS (RR t0 t1 (Z_to_bv 64 (conc st g1)) a1' a2 a3 a4 a5 a6 a7) F (Z_to_bv 64 0xd112c) fc None mX (seg_rom usegs)).
Proof.
intros until junk. intros TR HA NC P1 MRX MIX FRX STX PEX.
destruct (NC g1 P1) as (GM & mn & GN1 & Pmn).
destruct (gmf_geom st stX sc g1 TR GM) as (MSX & RAX & RFX & MWX & EM & ELI & ESC & EFB & ECONC).
pose proof (rmeta_slot_bounds stX mX g1 MRX MSX) as (Gpos & GC & GI & _ & _).
destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & Hgh & GMg & AIR & SC0 & UNK).
pose proof (gmf_mw _ _ _ GM) as (LI0 & FB0 & SCR0 & _).
unfold ta_m, RR.
set (f := m_freed (get_meta_rec stX g1)).
destruct ((f =? mask_upto (m_last_idx (get_meta_rec stX g1))) && negb (m_freeable (get_meta_rec stX g1) =? 0)) eqn:FSK.
-
pose proof FSK as FSK'. apply andb_prop in FSK'. destruct FSK' as [FE FB]. apply Z.eqb_eq in FE. apply Bool.negb_true_iff in FB. apply Z.eqb_neq in FB.
rewrite GN1.
destruct (NC mn Pmn) as (GMn & mn2 & GN2 & Pmn2).
destruct (gmf_geom st stX sc mn TR GMn) as (MSn & RAn & RFn & MWn & EMn & _ & _ & _ & ECONCn).
rewrite <- ECONC. riprefixT. eapply evt_mono.
{ eapply (rm_skip_walk stX mX g1 sc MRX MSX SC RFX MWX); [exact FSK| exact GN1| exact MSn| exact RFn| exact MIX]. }
cbv beta. intros ms' (a1'' & a2' & m5 & -> & MU & WM & MI5 & MR5).
assert (TRN : ta_rel sc st (set_active sc (Some mn) stX)) by (eapply ta_rel_trans; [exact TR| apply ta_rel_set_active]).
rewrite ECONCn.
eapply (ract_block (set_active sc (Some mn) stX) mn (m_freed (get_meta_rec stX mn)) m5); try eassumption.
+ rewrite active_set_active, Z.eqb_refl. reflexivity.
+ reflexivity.
+ intros q Hq. rewrite rec_set_active in Hq. rewrite GN2 in Hq. inversion Hq; subst q. exact (proj1 (NC _ Pmn2)).
+ rewrite rec_set_active, GN2. discriminate.
+ eapply rw_cells_transport; [exact FRX| exact MU| exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia.
+ eapply stk_transport_disjoint; [exact STX| exact MU| exact WM|]. apply disjoint_high; [|lia].
intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia.
+ eapply rpres_except_trans; [exact PEX|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rta_fp_ctx. unfold RCTX in *. lia.
-
rewrite <- ECONC. riprefixT. eapply evt_mono.
{ eapply (rm_act_walk stX mX g1 sc MRX MSX RFX MWX); [exact FSK| exact MIX]. }
cbv beta. intros ms' (a1'' & a2' & ->). rewrite ECONC.
eapply (ract_block stX g1 f mX); try eassumption.
+ reflexivity.
+ intros q Hq. rewrite GN1 in Hq. inversion Hq; subst q. exact (proj1 (NC _ Pmn)).
+ rewrite GN1. discriminate.
Qed.

#[using="TAF SC CLO LO HK1"] Lemma rta_phase : forall (t0 t1 a0 a2 a3 a4 a5 a6 a7 : word),
a0 = Z_to_bv 64 sc ->
rmrep st m -> mem_inv usegs m -> stk usegs m lo spv ->
(forall st1 m' (t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' : word) (junk : list byte),
ta_fail sc st st1 -> ta_rel sc st st1 -> active st1 sc = None ->
rmrep st1 m' -> mem_inv usegs m' -> rw_cells usegs m' (spv + -144) (FRM junk) -> stk usegs m' lo (spv + -144) ->
rpres_except (rta_fp st lo spv) m m' ->
rimplT o (K st1 0) s Q (MS (RR t0' t1' a0' a1' a2' a3' a4' a5' a6' a7') F (Z_to_bv 64 0xd1244) fc None m' (seg_rom usegs))) ->
rimplT o (try_avail sc st K bail) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom usegs)).
Proof.
intros until a7. intros A0 MR MI ST HK0.
assert (AMS : forall g, active st sc = Some g -> meta_slot st g) by (intros g Hg; exact (gmf_slot _ _ _ (proj1 (taf_head _ _ TAF g Hg)))).
riprefixT. eapply evt_mono.
{ eapply (ras_entry_walk st m sc lo MR SC CLO AMS); [exact A0| exact ST| exact LO| exact MI]. }
cbv beta. intros ms' (a1x & m1 & junk & -> & FR1 & ST1 & MU1 & WM1 & MI1 & MR1).
assert (PE1 : rpres_except (rta_fp st lo spv) m m1).
{ eapply rpres_except_of_munch_cov; [exact MU1| exact WM1|]. cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rta_fp_stack. unfold spv; lia. }
clear MU1 WM1.
rewrite (try_avail_eq sc K bail st).
destruct (active st sc) as [g|] eqn:HA.
2:{
eapply (HK0 st m1); [| apply ta_rel_refl| exact HA| exact MR1| exact MI1| exact FR1| exact ST1| exact PE1].
unfold ta_fail, try_avail. rewrite HA. reflexivity. }
destruct (taf_head _ _ TAF g HA) as [GM GSC].
pose proof (gmf_slot _ _ _ GM) as MSg. pose proof (gmf_avail _ _ _ GM) as RAg. pose proof (gmf_freed _ _ _ GM) as RFg.
pose proof (rmeta_slot_bounds st m1 g MR1 MSg) as (Gpos & GC & GI & _ & _).
unfold pw. cbn [oconc]. unfold wz.
destruct (m_avail (get_meta_rec st g) =? 0) eqn:AV; cbn [negb].
2:{
apply Z.eqb_neq in AV.
riprefixT. eapply evt_mono.
{ eapply (rt1_fin_walk st m1 g sc MR1 MSg RAg); [exact AV| exact MI1]. }
cbv beta. intros ms' ->.
eapply (rfin_block st g (m_avail (get_meta_rec st g)) m1); [apply ta_rel_refl| exact HA| exact GM| reflexivity| lia| exact MR1| exact MI1| exact FR1| exact ST1| exact PE1]. }
apply Z.eqb_eq in AV.
destruct (gmf_links _ _ _ GM) as (nx & pv & GN & GP).
destruct (taf_next _ _ TAF g nx GM GN) as (GMn & SCn & PRn).
destruct (taf_prev _ _ TAF g pv GM GP) as (GMp & NXp).
destruct (m_freed (get_meta_rec st g) =? 0) eqn:FZ.
-
apply Z.eqb_eq in FZ.
riprefixT. eapply evt_mono.
{ eapply (rt1_deq_walk st m1 g sc MR1 MSg); [exact AV| exact FZ| exact MI1]. }
cbv beta. intros ms' ->.
destruct (decide (nx = g)) as [->|NEn].
+
rewrite (dequeue_self_eq sc g st GN).
replace (active (put_meta g (clr (get_meta_rec st g)) (set_active sc None st)) sc) with (@None aptr)
by (change (active (put_meta g (clr (get_meta_rec st g)) (set_active sc None st)) sc) with (active (set_active sc None st) sc); rewrite active_set_active, Z.eqb_refl; reflexivity).
cbn [Z.eqb].
riprefixT. eapply evt_mono.
{ eapply (rdeq_self_walk st m1 g sc MR1 MSg SC); [exact GN| exact MI1]. }
cbv beta. intros ms' (m2 & -> & MU & WM & MI2 & MR2).
eapply (HK0 _ m2).
* unfold ta_fail. rewrite (try_avail_eq sc kS bS st), HA, AV, FZ. cbn [Z.eqb negb].
rewrite (dequeue_self_eq sc g st GN).
change (active (put_meta g (clr (get_meta_rec st g)) (set_active sc None st)) sc) with (active (set_active sc None st) sc).
rewrite active_set_active, Z.eqb_refl. reflexivity.
* eapply ta_rel_trans; [apply ta_rel_set_active|]. unfold clr.
replace (get_meta_rec st g) with (get_meta_rec (set_active sc None st) g) by reflexivity. apply ta_rel_put_links.
* change (active (put_meta g (clr (get_meta_rec st g)) (set_active sc None st)) sc) with (active (set_active sc None st) sc).
rewrite active_set_active, Z.eqb_refl. reflexivity.
* exact MR2.
* exact MI2.
* eapply rw_cells_transport; [exact FR1| exact MU| exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia.
* eapply stk_transport_disjoint; [exact ST1| exact MU| exact WM|]. apply disjoint_high; [|lia].
intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia.
* eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
cbn [ivs_covered]. split; [|split; [|exact I]]; intros x Hx; [apply rta_fp_ctx; unfold RCTX in *; lia| eapply rta_fp_meta; [exact MSg| lia]].
+
assert (NEp : pv <> g).
{ intros ->. rewrite NXp in GN. inversion GN. subst nx. apply NEn. reflexivity. }
rewrite (dequeue_other_eq sc g nx pv st GN GP NEn NEp HA). cbv zeta.
match goal with |- context [active ?stq sc] => set (st1 := stq) in * end.
assert (HA1 : active st1 sc = Some nx).
{ unfold st1. unfold active, put_meta, set_metas, set_active, upd_ctx. cbn [s_ctx ctx c_active set_active_map]. apply lookup_insert_eq. }
rewrite HA1.
pose proof (gmf_slot _ _ _ GMn) as MSn. pose proof (gmf_slot _ _ _ GMp) as MSp.
riprefixT. eapply evt_mono.
{ eapply (rdeq_other_walk st m1 g sc MR1 MSg SC HA); [exact GN| exact GP| exact NEn| exact NEp| exact MSn| exact MSp| exact MI1]. }
cbv beta. intros ms' (a1'' & m2 & -> & MU & WM & MI2 & MR2). fold st1 in MR2.
assert (TR1 : ta_rel sc st st1).
{ unfold st1.
lazymatch goal with |- ta_rel _ _ (put_meta _ _ ?sC) =>
lazymatch sC with set_active _ _ ?sB =>
lazymatch sB with put_meta _ _ ?sA =>
apply (ta_rel_trans sc st sC); [apply (ta_rel_trans sc st sB); [apply (ta_rel_trans sc st sA); [apply ta_rel_put_next| apply ta_rel_put_prev] | apply ta_rel_set_active] |];
unfold clr; replace (get_meta_rec st g) with (get_meta_rec sC g); [apply ta_rel_put_links|]
end end end.
rewrite rec_set_active. rewrite (get_meta_rec_put_other _ nx) by (intros E; apply NEn; symmetry; exact E).
rewrite (get_meta_rec_put_other _ pv) by (intros E; apply NEp; symmetry; exact E). reflexivity. }

assert (REC1 : forall q, q <> g -> get_meta_rec st1 q =
if aptr_eqb q nx then m_set_prev (Some pv) (if aptr_eqb nx pv then m_set_next (Some nx) (get_meta_rec st pv) else get_meta_rec st nx)
else if aptr_eqb q pv then m_set_next (Some nx) (get_meta_rec st pv) else get_meta_rec st q).
{ intros q Hq. unfold st1. rewrite (get_meta_rec_put_other _ g) by exact Hq. rewrite rec_set_active.
rewrite get_meta_rec_put. destruct (aptr_eqb q nx) eqn:E1.
- apply aptr_eqb_eq in E1. subst q. f_equal. rewrite get_meta_rec_put. destruct (aptr_eqb nx pv) eqn:E2; [apply aptr_eqb_eq in E2; subst; reflexivity| reflexivity].
- rewrite get_meta_rec_put. reflexivity. }
eapply (rm_block st1 nx m2 (fun q => gmf st sc q /\ q <> g)); [exact TR1| exact HA1| | split; [exact GMn| exact NEn] | exact MR2| exact MI2| | |].
* intros q [GMq NEq]. split; [exact GMq|]. rewrite (REC1 q NEq).
destruct (gmf_links _ _ _ GMq) as (qn & qp & QN & QP). destruct (taf_next _ _ TAF q qn GMq QN) as (GMqn & _ & PRqn).
destruct (aptr_eqb q nx) eqn:E1.
-- apply aptr_eqb_eq in E1. subst q. cbn [m_next m_set_prev].
destruct (aptr_eqb nx pv) eqn:E2.
++ exists nx. cbn. split; [reflexivity|]. split; [exact GMn| exact NEn].
++ exists qn. split; [exact QN|]. split; [exact GMqn|]. intros ->.
rewrite PRqn in GP. inversion GP. subst pv. rewrite (proj2 (aptr_eqb_eq nx nx) eq_refl) in E2. discriminate.
-- destruct (aptr_eqb q pv) eqn:E2.
++ apply aptr_eqb_eq in E2. subst q. cbn. exists nx. split; [reflexivity|]. split; [exact GMn| exact NEn].
++ exists qn. split; [exact QN|]. split; [exact GMqn|]. intros ->. rewrite PRqn in GP. inversion GP. subst pv.
rewrite (proj2 (aptr_eqb_eq q q) eq_refl) in E2. discriminate.
* eapply rw_cells_transport; [exact FR1| exact MU| exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
pose proof (rmeta_slot_bounds st m1 nx MR1 MSn) as (? & ? & _). pose proof (rmeta_slot_bounds st m1 pv MR1 MSp) as (? & ? & _).
intros lo' hi' [E|[E|[E|[E|[]]]]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia.
* eapply stk_transport_disjoint; [exact ST1| exact MU| exact WM|]. apply disjoint_high; [|lia].
pose proof (rmeta_slot_bounds st m1 nx MR1 MSn) as (? & ? & _). pose proof (rmeta_slot_bounds st m1 pv MR1 MSp) as (? & ? & _).
intros lo' hi' [E|[E|[E|[E|[]]]]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia.
* eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
cbn [ivs_covered]. split; [|split; [|split; [|split; [|exact I]]]]; intros x Hx;
[apply rta_fp_ctx; unfold RCTX in *; lia| eapply rta_fp_meta; [exact MSg| lia]| eapply rta_fp_meta; [exact MSp| lia]| eapply rta_fp_meta; [exact MSn| lia]].
-
apply Z.eqb_neq in FZ. rewrite GN.
riprefixT. eapply evt_mono.
{ eapply (rt1_next_walk st m1 g sc MR1 MSg SC RFg); [exact AV| exact FZ| exact MI1]. }
cbv beta. intros ms' (m2 & -> & MU & WM & MI2 & MR2). rewrite GN in MR2 |- *. unfold pw. cbn [oconc]. unfold wz.
eapply (rm_block (set_active sc (Some nx) st) nx m2 (gmf st sc)); [| | | exact GMn| exact MR2| exact MI2| | |].
+ apply ta_rel_set_active.
+ rewrite active_set_active, Z.eqb_refl. reflexivity.
+ intros q GMq. split; [exact GMq|]. rewrite rec_set_active. destruct (gmf_links _ _ _ GMq) as (qn & qp & QN & QP).
exists qn. split; [exact QN|]. exact (proj1 (taf_next _ _ TAF q qn GMq QN)).
+ eapply rw_cells_transport; [exact FR1| exact MU| exact WM|]. apply disjoint_high; [|unfold spv in *; lia].
intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia.
+ eapply stk_transport_disjoint; [exact ST1| exact MU| exact WM|]. apply disjoint_high; [|lia].
intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX, alloc_ceiling in *; lia.
+ eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_of_munch_cov; [exact MU| exact WM|].
cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rta_fp_ctx. unfold RCTX in *. lia.
Qed.
End PHASE.

End RC__1.
End Mq4.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpX.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLsg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkQT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkQT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlkP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlkP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyjG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyjG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTyG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTyG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QM7w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QM7w. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNAo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNAo.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCwx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCwx.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFqQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFqQ.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q98Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q98Z.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q98Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q98Z.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkLq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkLq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkLq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkLq.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdZ1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdZ1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv4L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv4L.Mqk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQbX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQbX. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv4L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv4L.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnkH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnkH.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rgmf_of_facts st LB sc g :
RISTF st LB -> lmem st g -> m_sizeclass (get_meta_rec st g) = sc -> 0 <= sc < 48 -> gmf st sc g.
Proof.
intros F (MEM & NX & PV) GSC SCR. assert (SC48 : m_sizeclass (get_meta_rec st g) < 48) by lia.
pose proof (isf_mf _ _ F) as MF. pose proof (isf_lf _ _ F) as LF. pose proof (isf_ghdr _ _ F) as GU.
destruct (m_mem (get_meta_rec st g)) as [b|] eqn:Hmem; [|congruence].
pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
specialize (FG g b Hmem). cbv zeta in FG.
destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh & AI & AVAI) & _).
pose proof (lf_mw _ (isf_lf _ _ F) g) as (MW & _ & _). change (get_meta_rec (strip st) g) with (get_meta_rec st g) in MW.
pose proof (mf_masks _ _ MF) as FM. change (fact_masks (strip st)) with (fact_masks st) in FM.
constructor.
- exact MSL.
- exact AVr.
- exact FRr.
- exact MW.
- exact SC48.
- exact GSC.
- exists b, (mkGhdr (Some g) ai). split; [exact Hmem|]. split; [exact Hgh|]. split; [reflexivity|]. split; [cbn; lia|]. split.
+ intros S0. cbn. pose proof (lf_sc0_full _ LF g b (mkGhdr (Some g) ai)) as X.
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in X. change (s_groups (strip st)) with (s_groups st) in X.
exact (X Hmem Hgh S0).
+ intros o Ho. exact (GU b _ o Hgh Ho).
- intros i Hi Hb. destruct (FM g b Hmem) as (F1 & F2 & _). exact (F2 i Hi Hb).
- intros i Hi Hb. destruct (FM g b Hmem) as (F1 & F2 & _). exact (F1 i Hi Hb).
- destruct (m_next (get_meta_rec st g)) as [n|] eqn:En; [|congruence]. destruct (m_prev (get_meta_rec st g)) as [p|] eqn:Ep; [|congruence].
exists n, p. split; reflexivity.
Qed.

#[using="Type"] Lemma rtaf_of_facts st LB sc : RISTF st LB -> 0 <= sc < 48 -> taf st sc.
Proof.
intros F SC. pose proof (isf_mf _ _ F) as MF. pose proof (isf_lf _ _ F) as LF.
pose proof (lf_lists _ LF) as (L1 & L2 & L3).
change (fact_active (strip st)) with (fact_active st).
pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
pose proof (lf_links _ LF) as LK.
constructor.
- intros g Hg. destruct (FA sc g Hg) as (_ & GSC & _). pose proof (L1 sc g Hg) as LM.
change (lmem (strip st) g) with (lmem st g) in LM.
split; [| exact GSC]. eapply rgmf_of_facts; [exact F| exact LM| exact GSC| exact SC].
- intros g n GM Hn. destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & _).
destruct (L2 g n ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); rewrite Hmem; discriminate) Hn) as [LMn SCn].
change (lmem (strip st) n) with (lmem st n) in LMn. change (get_meta_rec (strip st) n) with (get_meta_rec st n) in SCn.
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SCn.
split; [eapply rgmf_of_facts; [exact F| exact LMn| rewrite SCn; exact (gmf_cls _ _ _ GM)| exact SC]|].
split; [exact SCn|].
destruct (gmf_links _ _ _ GM) as (n' & p' & En & Ep).
destruct (LK g ltac:(split; [rewrite Hmem; discriminate| split; [rewrite En| rewrite Ep]; discriminate])) as [LKn _].
exact (LKn n Hn).
- intros g p GM Hp. destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & _).
destruct (L3 g p ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); rewrite Hmem; discriminate) Hp) as [LMp SCp].
change (lmem (strip st) p) with (lmem st p) in LMp. change (get_meta_rec (strip st) p) with (get_meta_rec st p) in SCp.
change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SCp.
split; [eapply rgmf_of_facts; [exact F| exact LMp| rewrite SCp; exact (gmf_cls _ _ _ GM)| exact SC]|].
destruct (gmf_links _ _ _ GM) as (n' & p' & En & Ep).
destruct (LK g ltac:(split; [rewrite Hmem; discriminate| split; [rewrite En| rewrite Ep]; discriminate])) as [_ LKp].
exact (LKp p Hp).
- pose proof (mf_ctx _ _ MF) as (_ & _ & _ & _ & B & _). intros i. exact (B i).
Qed.

Section FPER.
Variables (st0 st : mstate) (m : mem).
Hypothesis MR : rmrep st m.
Hypothesis ER : ENTRY_REL st0 st.

#[using="st m MR ER"] Lemma rst0_region rid r : (s_regions st0) !! rid = Some r ->
0 <= r_base r /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
/\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x3e000 <= r_base r)
/\ (r_base r + round_up_pg (r_len r) <= 0x3e000 \/ 0xe4000 <= r_base r)
/\ (r_base r + round_up_pg (r_len r) <= 0xe4000 \/ 0xea000 <= r_base r)
/\ (r_base r + round_up_pg (r_len r) <= 0xea000 \/ 0x647000 <= r_base r).
Proof.
intros Hr. destruct (mrel_regions _ _ (er_mrel _ _ ER) rid r Hr) as (r' & Hr' & K' & B' & L').
pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
destruct (WR rid r' Hr') as (RB0 & RBAL & RL0 & RBC & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4).
pose proof (round_up_pg_mono _ _ L'). pose proof (round_up_pg_ge (r_len r)). rewrite B' in *. unfold alloc_ceiling in *. lia.
Qed.

#[using="st m MR ER"] Lemma rmalloc_fp_cases_ER stE mE lo sp a :
rmrep stE mE -> rmalloc_fp st0 stE lo sp a -> lo <= a < sp \/ a < alloc_ceiling.
Proof.
intros (WF2 & _) H. pose proof WF2 as (_ & WR2 & _).
unfold alloc_ceiling in *.
destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC _]]]]].
- left; exact H.
- right. rewrite unsigned_lit in H by lia. lia.
- right. unfold RCTX in H. lia.
- right. destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). unfold alloc_ceiling in RC. lia.
- right. destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _). unfold alloc_ceiling in RC. lia.
- right. destruct (rst0_region (fst b) r Hr) as (_ & RC & _). unfold alloc_ceiling in RC. lia.
- right. destruct (rst0_region (fst b) r Hr) as (_ & RC & _). unfold alloc_ceiling in RC. lia.
- right. unfold alloc_ceiling in FC. lia.
Qed.

#[using="st m MR ER"] Lemma rmalloc_fp_image_ER stE mE lo sp a :
rmrep stE mE -> rmalloc_fp st0 stE lo sp a -> alloc_ceiling <= lo ->
0x10000 <= a < 0x647000 -> RCTX <= a < RCTX + 928 \/ 0x62547c <= a < 0x625480.
Proof.
intros (WF2 & _) H CLO HA. pose proof WF2 as (_ & WR2 & _). pose proof MR as ((RS1 & _) & _).
unfold alloc_ceiling in *.
destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC FR]]]]].
- exfalso. lia.
- right. rewrite unsigned_lit in H by lia. lia.
- left. exact H.
- exfalso. destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4). pose proof (lr_lo_ge r). lia.
- exfalso. destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4). pose proof (lr_lo_ge r). lia.
- exfalso. destruct (rst0_region (fst b) r Hr) as (_ & _ & W1 & W2 & W3 & W4). lia.
- exfalso. destruct (rst0_region (fst b) r Hr) as (_ & _ & W1 & W2 & W3 & W4). lia.
- exfalso. pose proof (rfresh_image st0 a (conj FC FR) ltac:(rewrite <- (mrel_reserved _ _ (er_mrel _ _ ER)); exact RS1)). lia.
Qed.

#[using="st m MR ER"] Lemma rauxv_ok_malloc_fp_ER stE mE lo sp m1 m' B :
rmrep stE mE -> rauxv_ok m1 B -> rpres_except (rmalloc_fp st0 stE lo sp) m1 m' ->
alloc_ceiling <= lo -> sp <= B -> rauxv_ok m' B.
Proof.
intros; constructor; exact I.
Qed.

#[using="st m MR ER"] Lemma rframe_keep_ER stE mE lo sp m1 m' A cs :
rmrep stE mE -> rpres_except (rmalloc_fp st0 stE lo sp) m1 m' -> rw_cells usegs m1 A cs ->
sp <= A -> alloc_ceiling <= A -> rw_cells usegs m' A cs.
Proof.
intros MRE PE H HA HC. eapply rpres_except_rw_cells; [exact PE| exact H|].
intros a Ha Hfp. destruct (rmalloc_fp_cases_ER stE mE lo sp a MRE Hfp); lia.
Qed.
End FPER.

End RC__1.
