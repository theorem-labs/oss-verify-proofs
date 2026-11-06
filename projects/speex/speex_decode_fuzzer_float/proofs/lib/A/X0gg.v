(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cg X1dj X1cr.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.MallocA Require Import X1dn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0j2 X0hi X0j3 X0gi X0hr
X0j1 X0hh X046 X0j6 X0j8 X0gp X0gd X0g8 X0hs X0hf X0gf X0go X0ge.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1dg.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19l X183 X19m X173 X18c X182 X0v4 X19p X19r X17a X16y X16t X18d X180 X170 X179 X16z.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X182 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v4 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19r OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18d OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X180 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X170 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X179 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16z.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA.X1dg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
lazymatch type of t with
| (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
| ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
end.
Local Ltac zhide :=
repeat match goal with
| H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
end;
repeat match goal with
| H : (?x mod ?k = ?r)%Z |- _ =>
let q := fresh "zq" in let Hq := fresh "Hzq" in
destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
| H : context [(?x mod ?k = ?r)%Z] |- _ =>
lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
(try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
end;
repeat match goal with
| H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
end.

Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
repeat match goal with
| H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
| H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
| H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
| H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
| H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
| H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
| H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
end
end.
Local Ltac zidle_nspZ H A q := lazymatch A with context [q] => fail | _ => zidle1 H end.
Local Ltac zidle_beginZ q n MUz WMz :=
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
pose proof (munch_refl [(q - n, q)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
repeat match goal with
| H : rw_cells segs m ?A _ |- _ => zidle_nspZ H A q
| H : u8arr segs m ?A _ |- _ => zidle_nspZ H A q
| H : u32arr segs m ?A _ |- _ => zidle_nspZ H A q
| H : u64arr segs m ?A _ |- _ => zidle_nspZ H A q
| H : bytes_at segs m ?A _ |- _ => zidle_nspZ H A q
end
end.
Local Ltac zidle_end MUz WMz :=
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
lazymatch type of MUz with munch _ ?m _ =>
try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Local Ltac zidle_end_m m :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
unfold zidle in *; transport_after_call bsegs m mm MU WM end end.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition realloc_pc : Z := 0x68700.
Definition wrap_realloc_entry : Z := 0x67f8c.

Lemma pim_realloc_spec : forall (Q : machine_state -> Prop) (m : mem) (p : Z)
ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc,
(0 <= p < 2 ^ 47)%Z ->
u8arr bsegs m (IAP + 8) (repeat (Z_to_bv 8 0) (Z.to_nat 0x40000)) -> mem_inv bsegs m ->
(forall a1' a2' a3', evt bsegs Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 IAP) a1' a2' a3' a4 a5 a6 a7 (Z_to_bv 64 p) s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6) F (Z_to_bv 64 0x68698) fc None m (seg_rom bsegs))) ->
evt bsegs Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 IAP) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 p) s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6) F (Z_to_bv 64 0x68608) fc None m (seg_rom bsegs)).
Proof.
intros until fc. intros HP MAP MI K. unfold IAP in *.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (E47 : Z.shiftr p 47 = 0%Z) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
zstep. rewrite E47. zstep. ifF.
assert (HQ : (0 <= Z.shiftr p 32 < 32768)%Z).
{ rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
do 3 zstep.
assert (SH3 : ((p ≫ 32) ≪ 3 = 8 * (p ≫ 32))%Z) by (rewrite Z.shiftl_mul_pow2 by lia; lia). rewrite SH3.
pose proof (zero_run_read8 m (1076416 + 8) 262144 (8 * (p ≫ 32)) MAP ltac:(lia) ltac:(lia)) as RD.
replace (1076416 + 8 + 8 * (p ≫ 32))%Z with (1076416 + 8 * (p ≫ 32) + 8)%Z in RD by lia.
zstep. change (le_bytes_to_word (repeat (Z_to_bv 8 0) 8)) with (Z_to_bv 64 0).
zstep. zstep. ifT.
apply K.
Qed.

Definition realloc_A_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(p n T lo : Z) (rc rd : word) (tr : list Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (tb : list word) (jp jq jr j0 : list byte) (m' : mem),
ms' = MS (mkR (Z_to_bv 64 0x45e8c) (Z_to_bv 64 (bv_unsigned sp + -2336)) gp (Z_to_bv 64 tpA) t0' t1' t2'
(Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 (T + 208))
(Z_to_bv 64 (needed2 n)) (Z_to_bv 64 8) a4' a5' a6' a7' (Z_to_bv 64 8) (Z_to_bv 64 (needed2 n))
(Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 (bv_unsigned sp + -2136))
(Z_to_bv 64 (0 + - (8))) (Z_to_bv 64 7) (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6')
F (Z_to_bv 64 0x4a424) fc None m' (seg_rom bsegs)
/\ munch [(T + 3168, T + 3169); (1660232, 1660236); (1076416, 1604848); (T + 2856, T + 2872); (bv_unsigned sp - 2352, bv_unsigned sp)]%Z m m'
/\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ ia_state true m'
/\ rw_cells bsegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ rw_cells bsegs m' (bv_unsigned sp + -72) [CB 8 jp]
/\ rw_cells bsegs m' (bv_unsigned sp + -80) [C8 (Z_to_bv 64 (bv_unsigned sp))]
/\ u64arr bsegs m' (bv_unsigned sp + -2120) (wr_trace tr tb) /\ length tb = 255%nat
/\ rw_cells bsegs m' (bv_unsigned sp + -2136)
[C8 (Z_to_bv 64 (bv_unsigned sp + -2120)); C8 (Z_to_bv 64 (Z.of_nat (length tr)))]
/\ rw_cells bsegs m' (bv_unsigned sp + -2144) [CB 8 jq]
/\ rw_cells bsegs m' (bv_unsigned sp + -2160) [CB 8 jr; C8 (Z_to_bv 64 0x68770)]
/\ rw_cells bsegs m' (bv_unsigned sp + -2208)
[C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 realloc_pc); C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (bv_unsigned sp)); C8 (Z_to_bv 64 0x466f0)]
/\ alloc_frame m' (bv_unsigned sp + -2336) (Z_to_bv 64 0x4676c) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 p) (Z_to_bv 64 INST)
(Z_to_bv 64 n) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (bv_unsigned sp + -89)) s7 s8 s9 s10 s11
/\ rw_cells bsegs m' (bv_unsigned sp + -2336) [CB 8 j0]
/\ rw_cells bsegs m' (T + 3168) [C1 (Z_to_bv 8 0)]
/\ rw_cells bsegs m' (T + 2856) [C8 (Z_to_bv 64 (bv_unsigned rc + 1)); C8 (Z_to_bv 64 (bv_unsigned rd + n))]
/\ stk bsegs m' lo (bv_unsigned sp + -2336).

Lemma realloc_A_spec : forall ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (p n TCX T top bot lo : Z) (b : bool) (ch : list (Z * Z)) (tr : list Z) (rc rd : word),
(0 < p < 2^47)%Z -> (1 <= n <= 2^31)%Z ->
stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2352)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
(bv_unsigned sp <= 2^47)%Z ->
(0 <= bot < top)%Z -> (top < 2^64)%Z ->
chain_cells [(0, bv_unsigned sp)]%Z m (bv_unsigned s0) ch ->
unwind_trace realloc_pc 4096 bot top 30 (bv_unsigned sp) ((bv_unsigned ra, bv_unsigned s0) :: ch) = Some tr ->
ia_state b m ->
rw_cells bsegs m 0xfc0f8 [C8 (Z_to_bv 64 0x195560)] ->
rw_cells bsegs m g_GOT_common_flags [C8 (Z_to_bv 64 g_common_flags)] ->
rw_cells bsegs m i_max_user [C8 (Z_to_bv 64 (2^40))] -> rw_cells bsegs m i_min_rz [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)] ->
rw_cells bsegs m g_asan_inited [C1 (Z_to_bv 8 1)] ->
rw_cells bsegs m g_malloc_context_size_cell [C4 (Z_to_bv 64 30)] ->
rw_cells bsegs m g_rss_limit_exceeded [C1 (Z_to_bv 8 0)] ->
rw_cells bsegs m 0x195560 [C8 (Z_to_bv 64 4096)] ->
rw_cells bsegs m (g_common_flags + 34) [C1 (Z_to_bv 8 1)] ->
thread_cells TCX T m -> (0 < TCX)%Z -> (TCX + 0xa0 <= 0x10000 \/ 0x65b000 <= TCX)%Z -> (TCX + 0xa0 <= lo)%Z ->
(0 < T)%Z -> (T + 4096 <= 0x10000 \/ 0x65b000 <= T)%Z -> (T + 4096 <= lo)%Z ->
(TCX + 0xa0 <= T \/ T + 4096 <= TCX)%Z ->
stack_cells T top bot m -> rw_cells bsegs m (T + 3168) [C1 (Z_to_bv 8 0)] ->
rw_cells bsegs m (T + 2856) [C8 rc; C8 rd] ->
mem_inv bsegs m ->
evt bsegs (realloc_A_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p n T lo rc rd tr m)
(MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6)
F (Z_to_bv 64 wrap_realloc_entry) fc None m (seg_rom bsegs)).
Proof.
intros until rd. intros Hp Hn ST HLO HLOH HSP Hbt Htop CH TR IS G60 GCF MX RZ AI MCS RSS PSC FUM TC HTCX HTCXi HTCXl HT0 HT HTl HTT SC UW STS MI.
apply box in CH.
unfold wrap_realloc_entry, kHighShadowEnd, g_GOT_common_flags, g_common_flags, g_asan_inited, g_malloc_context_size_cell,
g_rss_limit_exceeded in *.
change (1668584 + 34)%Z with 1668618%Z in FUM.
destruct TC as [(KI & K0 & TS & T0) TT]. unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in *.
destruct SC as (SC1 & SC2). unfold off_t_stack_top, off_t_stack_switching in *.
move G60 at bottom. move GCF at bottom. move MX at bottom. move RZ at bottom. move KI at bottom. move K0 at bottom.
move AI at bottom. move MCS at bottom. move RSS at bottom. move PSC at bottom. move FUM at bottom. move TS at bottom.
move T0 at bottom.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
pose proof (munch_refl [(T + 3168, T + 3169); (1660232, 1660236); (1076416, 1604848); (T + 2856, T + 2872); (SP - 2352, SP)]%Z m) as MU.
pose proof (munch_refl [(SP - 2352, SP)]%Z m) as MUs.
pose proof (wmono_refl bsegs m) as WM.
carve_frame 64%nat ST. carve_frame 8%nat ST. carve_frame 8%nat ST. carve_frame 2040%nat ST. carve_frame 8%nat ST.
carve_frame 8%nat ST. carve_frame 8%nat ST.
zhide.
zidle_beginZ SP 2144%Z MUz WMz.
zstep.
do 9 zstep.
do 5 zstep. zstep.
zidle_end MUz WMz.
sp_factsZ SP.
call (try_init_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo).
all: rewrite ?Esp in *; try lia; try eassumption.
zstep. ifF.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (ia_state_frame b _ m mm IS MUs WM ltac:(cbn [disjoint_from]; lia)) as IS' end.
clear MUs IS.
sp_factsZ SP.
call (intalloc_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ b lo).
all: rewrite ?Esp in *; try lia; try eassumption.
lazymatch goal with H : ia_state true ?mm |- _ =>
pose proof H as (IW & MAP); apply box in H; rename H into IST;
pose proof (munch_refl [(T + 3168, T + 3169); (T + 2856, T + 2872); (SP - 2352, SP)]%Z mm) as MUa; pose proof (wmono_refl bsegs mm) as WMa end.
eapply pim_realloc_spec; [lia| exact MAP| eassumption|]. intros a1' a2' a3'. clear IW MAP.
do 7 zstep.
zstep; fix_lit_store.
zstep.
zstep; fix_lit_store.
zstep.
call (malloc_ctx_size_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 30).
all: try lia; try eassumption.
zstep. zstep. ifT.
zstep. zstep. zstep.
do 5 zstep.
call (malloc_ctx_size_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 30).
all: try lia; try eassumption.
do 5 zstep.
assert (EB : Z.land (Z.land (Z.b2z (30 <? 1) + -1) 18446744073709551615) SP = SP).
{ change (Z.land (Z.b2z (30 <? 1) + -1) 18446744073709551615) with (Z.ones 64).
rewrite Z.land_comm, Z.land_ones, Z.mod_small by lia. reflexivity. }
rewrite EB. clear EB.
zstep. zstep. ifT.
do 6 zstep.
zstep.

apply (rw_cells_c8_split _ _ [] [] 0 ltac:(lia)) in FR3. cbn [app] in FR3.
apply (rwc_app bsegs _ _ [C4 (Z_to_bv 64 0)] [C4 (Z_to_bv 64 0)]) in FR3. destruct FR3 as (FR3a & FR3b).
cbn [cells_size csize] in FR3b. replace (SP + -2128 + Z.of_nat (4 + 0))%Z with (SP + -2124)%Z in FR3b by lia.
change 2040%nat with (8 * 255)%nat in FR2. apply ma_rw_cells_u64arr in FR2.
apply (rwc_app bsegs _ _ [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra]) in FR. destruct FR as (FRa & FRb).
cbn [cells_size csize Nat.add] in FRb. replace (SP + -64 + Z.of_nat 48)%Z with (SP + -16)%Z in FRb by lia.
pose proof (bv_unsigned_in_range 64 ra) as RRA. pose proof (bv_unsigned_in_range 64 s0) as RS0.
unfold bv_modulus in RRA, RS0. cbn [Z.of_N] in RRA, RS0.
sp_factsZ SP.
lazymatch goal with H : rw_cells bsegs ?mm (SP + -16) _ |- _ =>
assert (CHm : chain_cells [(T + 3168, T + 3169); (1660232, 1660236); (1076416, 1604848); (T + 2856, T + 2872); (SP - 2352, SP)]%Z m (bv_unsigned s0) ch)
by (apply (chain_cells_weaken [(0, SP)]%Z); [intros a HDa; cbn [disjoint_from] in *; lia | exact (unbox _ CH)]);
apply (fun X => chain_cells_frame _ m mm _ _ X MU WM) in CHm;
apply (chain_cells_weaken _ (uwi_W (SP + -2136) T (SP + -2144))) in CHm;
[| intros a HDa; unfold uwi_W; cbn [disjoint_from] in *; lia];
assert (CC : chain_cells (uwi_W (SP + -2136) T (SP + -2144)) mm SP ((bv_unsigned ra, bv_unsigned s0) :: ch))
by (cbn [chain_cells]; rewrite !Z_to_bv_bv_unsigned; split; [exact H|];
split; [lia|]; split; [unfold uwi_W; cbn [disjoint_from]; lia| exact CHm]) end.
call (unwindimpl_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (SP + -2136) 427776 SP top bot 30 lo TCX T
((bv_unsigned ra, bv_unsigned s0) :: ch) (ma_dec64 255 junk2) (Z_to_bv 64 0) _ tr).
all: rewrite ?Esp; try lia; try eassumption; try apply ma_dec64_length.
all: lazymatch goal with
| |- thread_cells _ _ _ =>
unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main;
split; [split; [exact KI| split; [exact K0| split; [exact TS| exact T0]]]| exact TT]
| |- stack_cells _ _ _ _ => unfold stack_cells, off_t_stack_top, off_t_stack_switching; split; assumption
| |- rw_cells _ _ (?X + -2136 + 8)%Z _ => replace (X + -2136 + 8)%Z with (X + -2128)%Z by lia; exact FR3a
| |- u64arr _ _ (?X + -2136 + 16)%Z _ => replace (X + -2136 + 16)%Z with (X + -2120)%Z by lia; exact FR2
| |- rw_cells _ _ (?X + -2136 + 2056)%Z _ => replace (X + -2136 + 2056)%Z with (X + -80)%Z by lia; exact FR1
| |- evt _ _ _ => idtac
end.
rewrite ?Esp in *.
do 5 zstep.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
match goal with H : stk bsegs mm _ _ |- _ => carve_frame 8%nat H; carve_frame 8%nat H end end.
zstep. zstep; fix_lit_store.
do 2 zstep.
zstep. ifF.
zstep.
zstep. ifT.
do 5 zstep.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
match goal with H : stk bsegs mm _ _ |- _ => carve_frame 48%nat H end end.
zstep. do 6 (zstep; fix_lit_store).
zstep. ifF.
zstep.
zstep. ifF.
do 3 zstep.
zstep.
sp_factsZ SP.
call (gcts_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ TCX T lo).
all: rewrite ?Esp, ?Esp0, ?Esp1, ?Esp2, ?Esp3; try lia; try eassumption.
all: lazymatch goal with
| |- thread_cells _ _ _ =>
unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main;
split; [split; [exact KI| split; [exact K0| split; [exact TS| exact T0]]]| exact TT]
| |- evt _ _ _ => idtac
end.
rewrite ?Esp, ?Esp0, ?Esp1, ?Esp2, ?Esp3 in *.
do 4 zstep.
zstep; fix_lit_store. zstep; fix_lit_store.
do 6 zstep.
zstep.
sp_factsZ SP.
call (allocate_p1_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ n (SP + -2136) TCX T lo).
all: rewrite ?Esp, ?Esp0, ?Esp1, ?Esp2, ?Esp3, ?Esp4; try lia; try eassumption.
all: lazymatch goal with
| |- thread_cells _ _ _ =>
unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main;
split; [split; [exact KI| split; [exact K0| split; [exact TS| exact T0]]]| exact TT]
| |- evt _ _ _ => idtac
end.
unfold realloc_A_post, realloc_pc. rewrite (unsigned_lit SP) by lia.
rewrite ?Esp, ?Esp0, ?Esp1, ?Esp2, ?Esp3, ?Esp4 in *.
replace (SP + -2208 + -128)%Z with (SP + -2336)%Z in * by lia.
apply evt_done.
lazymatch goal with H : exists j, rw_cells bsegs _ _ [CB 8 j] |- _ => destruct H as (j0 & HJ0) end.
do 11 eexists. exists (ma_dec64 255 junk2), junk0, junk5, junk7, j0. eexists.
split; [reflexivity|].
pose proof (unwind_trace_length _ _ _ _ _ _ _ _ TR ltac:(lia)) as LT.
split; [assumption|]. split; [assumption|]. split; [assumption|].
split.
{ lazymatch goal with |- ia_state true ?mm =>
lazymatch type of MUa with munch _ ?m0 _ =>
exact (ia_state_frame true _ m0 mm (unbox _ IST) MUa WMa ltac:(cbn [disjoint_from]; lia)) end end. }
split.
{ apply (proj2 (rwc_app bsegs _ _ [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra])).
split; [exact_addr|]. cbn [cells_size csize Nat.add]. exact_addr. }
split; [exact_addr|]. split; [exact_addr|]. split; [exact_addr|]. split; [apply ma_dec64_length|].
split.
{ apply (proj2 (rwc_app bsegs _ _ [C8 (Z_to_bv 64 (SP + -2120))] [C8 (Z_to_bv 64 (Z.of_nat (length tr)))])).
split; [exact_addr|]. cbn [cells_size csize Nat.add].
apply (rw_cells_c44_join _ _ [] [] (Z.of_nat (length tr))); [lia|]. cbn [app].
apply (proj2 (rwc_app bsegs _ _ [C4 (Z_to_bv 64 (Z.of_nat (length tr)))] [C4 (Z_to_bv 64 0)])).
split; [exact_addr|]. cbn [cells_size csize Nat.add]. exact_addr. }
split; [exact_addr|].
split.
{ apply (proj2 (rwc_app bsegs _ _ [CB 8 junk7] [C8 (Z_to_bv 64 427888)])).
split; [exact_addr|]. cbn [cells_size csize Nat.add]. exact_addr. }
split; [exact_addr|].
split; [unfold alloc_frame, INST, g_instance in *; exact_addr|].
split; [exact_addr|]. split; [exact_addr|]. split; [exact_addr|]. exact_addr.
Qed.
End B_TWIN.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.

Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
lazymatch type of t with
| (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
| ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
end.
Local Ltac zhide :=
repeat match goal with
| H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
end;
repeat match goal with
| H : (?x mod ?k = ?r)%Z |- _ =>
let q := fresh "zq" in let Hq := fresh "Hzq" in
destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
| H : context [(?x mod ?k = ?r)%Z] |- _ =>
lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
(try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
end;
repeat match goal with
| H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
end.

Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
repeat match goal with
| H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
| H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
| H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
| H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
| H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
| H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
| H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
end
end.
Local Ltac zidle_nspZ H A q := lazymatch A with context [q] => fail | _ => zidle1 H end.
Local Ltac zidle_beginZ q n MUz WMz :=
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
pose proof (munch_refl [(q - n, q)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
repeat match goal with
| H : rw_cells segs m ?A _ |- _ => zidle_nspZ H A q
| H : u8arr segs m ?A _ |- _ => zidle_nspZ H A q
| H : u32arr segs m ?A _ |- _ => zidle_nspZ H A q
| H : u64arr segs m ?A _ |- _ => zidle_nspZ H A q
| H : bytes_at segs m ?A _ |- _ => zidle_nspZ H A q
end
end.
Local Ltac zidle_end MUz WMz :=
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
lazymatch type of MUz with munch _ ?m _ =>
try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.

Local Ltac zidle_end_m m :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
unfold zidle in *; transport_after_call asegs m mm MU WM end end.
Notation mem := (word -> option byte).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Definition realloc_pc : Z := 0x68614.
Definition wrap_realloc_entry : Z := 0x67ea0.

Lemma pim_realloc_spec : forall (Q : machine_state -> Prop) (m : mem) (p : Z)
ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc,
(0 <= p < 2 ^ 47)%Z ->
u8arr asegs m (IAP + 8) (repeat (Z_to_bv 8 0) (Z.to_nat 0x40000)) -> mem_inv asegs m ->
(forall a1' a2' a3', evt asegs Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 IAP) a1' a2' a3' a4 a5 a6 a7 (Z_to_bv 64 p) s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6) F (Z_to_bv 64 0x685ac) fc None m (seg_rom asegs))) ->
evt asegs Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 IAP) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 p) s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6) F (Z_to_bv 64 0x6851c) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros HP MAP MI K. unfold IAP in *.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (E47 : Z.shiftr p 47 = 0%Z) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
zstep. rewrite E47. zstep. ifF.
assert (HQ : (0 <= Z.shiftr p 32 < 32768)%Z).
{ rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
do 3 zstep.
assert (SH3 : ((p ≫ 32) ≪ 3 = 8 * (p ≫ 32))%Z) by (rewrite Z.shiftl_mul_pow2 by lia; lia). rewrite SH3.
pose proof (zero_run_read8 m (1041536 + 8) 262144 (8 * (p ≫ 32)) MAP ltac:(lia) ltac:(lia)) as RD.
replace (1041536 + 8 + 8 * (p ≫ 32))%Z with (1041536 + 8 * (p ≫ 32) + 8)%Z in RD by lia.
zstep. change (le_bytes_to_word (repeat (Z_to_bv 8 0) 8)) with (Z_to_bv 64 0).
zstep. zstep. ifT.
apply K.
Qed.

Definition realloc_A_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(p n T lo : Z) (rc rd : word) (tr : list Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (tb : list word) (jp jq jr j0 : list byte) (m' : mem),
ms' = MS (mkR (Z_to_bv 64 0x45da0) (Z_to_bv 64 (bv_unsigned sp + -2336)) gp (Z_to_bv 64 tpA) t0' t1' t2'
(Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 (T + 208))
(Z_to_bv 64 (needed2 n)) (Z_to_bv 64 8) a4' a5' a6' a7' (Z_to_bv 64 8) (Z_to_bv 64 (needed2 n))
(Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 (bv_unsigned sp + -2136))
(Z_to_bv 64 (0 + - (8))) (Z_to_bv 64 7) (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6')
F (Z_to_bv 64 0x4a338) fc None m' (seg_rom asegs)
/\ munch [(T + 3168, T + 3169); (1625352, 1625356); (1041536, 1569968); (T + 2856, T + 2872); (bv_unsigned sp - 2352, bv_unsigned sp)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ ia_state true m'
/\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ rw_cells asegs m' (bv_unsigned sp + -72) [CB 8 jp]
/\ rw_cells asegs m' (bv_unsigned sp + -80) [C8 (Z_to_bv 64 (bv_unsigned sp))]
/\ u64arr asegs m' (bv_unsigned sp + -2120) (wr_trace tr tb) /\ length tb = 255%nat
/\ rw_cells asegs m' (bv_unsigned sp + -2136)
[C8 (Z_to_bv 64 (bv_unsigned sp + -2120)); C8 (Z_to_bv 64 (Z.of_nat (length tr)))]
/\ rw_cells asegs m' (bv_unsigned sp + -2144) [CB 8 jq]
/\ rw_cells asegs m' (bv_unsigned sp + -2160) [CB 8 jr; C8 (Z_to_bv 64 0x68684)]
/\ rw_cells asegs m' (bv_unsigned sp + -2208)
[C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 realloc_pc); C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (bv_unsigned sp)); C8 (Z_to_bv 64 0x46604)]
/\ alloc_frame m' (bv_unsigned sp + -2336) (Z_to_bv 64 0x46680) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 p) (Z_to_bv 64 INST)
(Z_to_bv 64 n) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (bv_unsigned sp + -89)) s7 s8 s9 s10 s11
/\ rw_cells asegs m' (bv_unsigned sp + -2336) [CB 8 j0]
/\ rw_cells asegs m' (T + 3168) [C1 (Z_to_bv 8 0)]
/\ rw_cells asegs m' (T + 2856) [C8 (Z_to_bv 64 (bv_unsigned rc + 1)); C8 (Z_to_bv 64 (bv_unsigned rd + n))]
/\ stk asegs m' lo (bv_unsigned sp + -2336).

Lemma realloc_A_spec : forall ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : mem) (p n TCX T top bot lo : Z) (b : bool) (ch : list (Z * Z)) (tr : list Z) (rc rd : word),
(0 < p < 2^47)%Z -> (1 <= n <= 2^31)%Z ->
stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2352)%Z -> (kHighShadowEnd + 8 <= lo)%Z ->
(bv_unsigned sp <= 2^47)%Z ->
(0 <= bot < top)%Z -> (top < 2^64)%Z ->
chain_cells [(0, bv_unsigned sp)]%Z m (bv_unsigned s0) ch ->
unwind_trace realloc_pc 4096 bot top 30 (bv_unsigned sp) ((bv_unsigned ra, bv_unsigned s0) :: ch) = Some tr ->
ia_state b m ->
rw_cells asegs m 0xf3878 [C8 (Z_to_bv 64 0x18cd20)] ->
rw_cells asegs m g_GOT_common_flags [C8 (Z_to_bv 64 g_common_flags)] ->
rw_cells asegs m i_max_user [C8 (Z_to_bv 64 (2^40))] -> rw_cells asegs m i_min_rz [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)] ->
rw_cells asegs m g_asan_inited [C1 (Z_to_bv 8 1)] ->
rw_cells asegs m g_malloc_context_size_cell [C4 (Z_to_bv 64 30)] ->
rw_cells asegs m g_rss_limit_exceeded [C1 (Z_to_bv 8 0)] ->
rw_cells asegs m 0x18cd20 [C8 (Z_to_bv 64 4096)] ->
rw_cells asegs m (g_common_flags + 34) [C1 (Z_to_bv 8 1)] ->
thread_cells TCX T m -> (0 < TCX)%Z -> (TCX + 0xa0 <= 0x10000 \/ 0x652000 <= TCX)%Z -> (TCX + 0xa0 <= lo)%Z ->
(0 < T)%Z -> (T + 4096 <= 0x10000 \/ 0x652000 <= T)%Z -> (T + 4096 <= lo)%Z ->
(TCX + 0xa0 <= T \/ T + 4096 <= TCX)%Z ->
stack_cells T top bot m -> rw_cells asegs m (T + 3168) [C1 (Z_to_bv 8 0)] ->
rw_cells asegs m (T + 2856) [C8 rc; C8 rd] ->
mem_inv asegs m ->
evt asegs (realloc_A_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p n T lo rc rd tr m)
(MS (mkR ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6)
F (Z_to_bv 64 wrap_realloc_entry) fc None m (seg_rom asegs)).
Proof.
intros until rd. intros Hp Hn ST HLO HLOH HSP Hbt Htop CH TR IS G60 GCF MX RZ AI MCS RSS PSC FUM TC HTCX HTCXi HTCXl HT0 HT HTl HTT SC UW STS MI.
apply box in CH.
unfold wrap_realloc_entry, kHighShadowEnd, g_GOT_common_flags, g_common_flags, g_asan_inited, g_malloc_context_size_cell,
g_rss_limit_exceeded in *.
change (1633704 + 34)%Z with 1633738%Z in FUM.
destruct TC as [(KI & K0 & TS & T0) TT]. unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in *.
destruct SC as (SC1 & SC2). unfold off_t_stack_top, off_t_stack_switching in *.
move G60 at bottom. move GCF at bottom. move MX at bottom. move RZ at bottom. move KI at bottom. move K0 at bottom.
move AI at bottom. move MCS at bottom. move RSS at bottom. move PSC at bottom. move FUM at bottom. move TS at bottom.
move T0 at bottom.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
pose proof (munch_refl [(T + 3168, T + 3169); (1625352, 1625356); (1041536, 1569968); (T + 2856, T + 2872); (SP - 2352, SP)]%Z m) as MU.
pose proof (munch_refl [(SP - 2352, SP)]%Z m) as MUs.
pose proof (wmono_refl asegs m) as WM.
carve_frame 64%nat ST. carve_frame 8%nat ST. carve_frame 8%nat ST. carve_frame 2040%nat ST. carve_frame 8%nat ST.
carve_frame 8%nat ST. carve_frame 8%nat ST.
zhide.
zidle_beginZ SP 2144%Z MUz WMz.
zstep.
do 9 zstep.
do 5 zstep. zstep.
zidle_end MUz WMz.
sp_factsZ SP.
call (try_init_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo).
all: rewrite ?Esp in *; try lia; try eassumption.
zstep. ifF.
zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (ia_state_frame b _ m mm IS MUs WM ltac:(cbn [disjoint_from]; lia)) as IS' end.
clear MUs IS.
sp_factsZ SP.
call (intalloc_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ b lo).
all: rewrite ?Esp in *; try lia; try eassumption.
lazymatch goal with H : ia_state true ?mm |- _ =>
pose proof H as (IW & MAP); apply box in H; rename H into IST;
pose proof (munch_refl [(T + 3168, T + 3169); (T + 2856, T + 2872); (SP - 2352, SP)]%Z mm) as MUa; pose proof (wmono_refl asegs mm) as WMa end.
eapply pim_realloc_spec; [lia| exact MAP| eassumption|]. intros a1' a2' a3'. clear IW MAP.
do 7 zstep.
zstep; fix_lit_store.
zstep.
zstep; fix_lit_store.
zstep.
call (malloc_ctx_size_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 30).
all: try lia; try eassumption.
zstep. zstep. ifT.
zstep. zstep. zstep.
do 5 zstep.
call (malloc_ctx_size_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ 30).
all: try lia; try eassumption.
do 5 zstep.
assert (EB : Z.land (Z.land (Z.b2z (30 <? 1) + -1) 18446744073709551615) SP = SP).
{ change (Z.land (Z.b2z (30 <? 1) + -1) 18446744073709551615) with (Z.ones 64).
rewrite Z.land_comm, Z.land_ones, Z.mod_small by lia. reflexivity. }
rewrite EB. clear EB.
zstep. zstep. ifT.
do 6 zstep.
zstep.

apply (rw_cells_c8_split _ _ [] [] 0 ltac:(lia)) in FR3. cbn [app] in FR3.
apply (rwc_app asegs _ _ [C4 (Z_to_bv 64 0)] [C4 (Z_to_bv 64 0)]) in FR3. destruct FR3 as (FR3a & FR3b).
cbn [cells_size csize] in FR3b. replace (SP + -2128 + Z.of_nat (4 + 0))%Z with (SP + -2124)%Z in FR3b by lia.
change 2040%nat with (8 * 255)%nat in FR2. apply ma_rw_cells_u64arr in FR2.
apply (rwc_app asegs _ _ [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra]) in FR. destruct FR as (FRa & FRb).
cbn [cells_size csize Nat.add] in FRb. replace (SP + -64 + Z.of_nat 48)%Z with (SP + -16)%Z in FRb by lia.
pose proof (bv_unsigned_in_range 64 ra) as RRA. pose proof (bv_unsigned_in_range 64 s0) as RS0.
unfold bv_modulus in RRA, RS0. cbn [Z.of_N] in RRA, RS0.
sp_factsZ SP.
lazymatch goal with H : rw_cells asegs ?mm (SP + -16) _ |- _ =>
assert (CHm : chain_cells [(T + 3168, T + 3169); (1625352, 1625356); (1041536, 1569968); (T + 2856, T + 2872); (SP - 2352, SP)]%Z m (bv_unsigned s0) ch)
by (apply (chain_cells_weaken [(0, SP)]%Z); [intros a HDa; cbn [disjoint_from] in *; lia | exact (unbox _ CH)]);
apply (fun X => chain_cells_frame _ m mm _ _ X MU WM) in CHm;
apply (chain_cells_weaken _ (uwi_W (SP + -2136) T (SP + -2144))) in CHm;
[| intros a HDa; unfold uwi_W; cbn [disjoint_from] in *; lia];
assert (CC : chain_cells (uwi_W (SP + -2136) T (SP + -2144)) mm SP ((bv_unsigned ra, bv_unsigned s0) :: ch))
by (cbn [chain_cells]; rewrite !Z_to_bv_bv_unsigned; split; [exact H|];
split; [lia|]; split; [unfold uwi_W; cbn [disjoint_from]; lia| exact CHm]) end.
call (unwindimpl_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (SP + -2136) 427540 SP top bot 30 lo TCX T
((bv_unsigned ra, bv_unsigned s0) :: ch) (ma_dec64 255 junk2) (Z_to_bv 64 0) _ tr).
all: rewrite ?Esp; try lia; try eassumption; try apply ma_dec64_length.
all: lazymatch goal with
| |- thread_cells _ _ _ =>
unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main;
split; [split; [exact KI| split; [exact K0| split; [exact TS| exact T0]]]| exact TT]
| |- stack_cells _ _ _ _ => unfold stack_cells, off_t_stack_top, off_t_stack_switching; split; assumption
| |- rw_cells _ _ (?X + -2136 + 8)%Z _ => replace (X + -2136 + 8)%Z with (X + -2128)%Z by lia; exact FR3a
| |- u64arr _ _ (?X + -2136 + 16)%Z _ => replace (X + -2136 + 16)%Z with (X + -2120)%Z by lia; exact FR2
| |- rw_cells _ _ (?X + -2136 + 2056)%Z _ => replace (X + -2136 + 2056)%Z with (X + -80)%Z by lia; exact FR1
| |- evt _ _ _ => idtac
end.
rewrite ?Esp in *.
do 5 zstep.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
match goal with H : stk asegs mm _ _ |- _ => carve_frame 8%nat H; carve_frame 8%nat H end end.
zstep. zstep; fix_lit_store.
do 2 zstep.
zstep. ifF.
zstep.
zstep. ifT.
do 5 zstep.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
match goal with H : stk asegs mm _ _ |- _ => carve_frame 48%nat H end end.
zstep. do 6 (zstep; fix_lit_store).
zstep. ifF.
zstep.
zstep. ifF.
do 3 zstep.
zstep.
sp_factsZ SP.
call (gcts_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ TCX T lo).
all: rewrite ?Esp, ?Esp0, ?Esp1, ?Esp2, ?Esp3; try lia; try eassumption.
all: lazymatch goal with
| |- thread_cells _ _ _ =>
unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main;
split; [split; [exact KI| split; [exact K0| split; [exact TS| exact T0]]]| exact TT]
| |- evt _ _ _ => idtac
end.
rewrite ?Esp, ?Esp0, ?Esp1, ?Esp2, ?Esp3 in *.
do 4 zstep.
zstep; fix_lit_store. zstep; fix_lit_store.
do 6 zstep.
zstep.
sp_factsZ SP.
call (allocate_p1_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ n (SP + -2136) TCX T lo).
all: rewrite ?Esp, ?Esp0, ?Esp1, ?Esp2, ?Esp3, ?Esp4; try lia; try eassumption.
all: lazymatch goal with
| |- thread_cells _ _ _ =>
unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main;
split; [split; [exact KI| split; [exact K0| split; [exact TS| exact T0]]]| exact TT]
| |- evt _ _ _ => idtac
end.
unfold realloc_A_post, realloc_pc. rewrite (unsigned_lit SP) by lia.
rewrite ?Esp, ?Esp0, ?Esp1, ?Esp2, ?Esp3, ?Esp4 in *.
replace (SP + -2208 + -128)%Z with (SP + -2336)%Z in * by lia.
apply evt_done.
lazymatch goal with H : exists j, rw_cells asegs _ _ [CB 8 j] |- _ => destruct H as (j0 & HJ0) end.
do 11 eexists. exists (ma_dec64 255 junk2), junk0, junk5, junk7, j0. eexists.
split; [reflexivity|].
pose proof (unwind_trace_length _ _ _ _ _ _ _ _ TR ltac:(lia)) as LT.
split; [assumption|]. split; [assumption|]. split; [assumption|].
split.
{ lazymatch goal with |- ia_state true ?mm =>
lazymatch type of MUa with munch _ ?m0 _ =>
exact (ia_state_frame true _ m0 mm (unbox _ IST) MUa WMa ltac:(cbn [disjoint_from]; lia)) end end. }
split.
{ apply (proj2 (rwc_app asegs _ _ [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra])).
split; [exact_addr|]. cbn [cells_size csize Nat.add]. exact_addr. }
split; [exact_addr|]. split; [exact_addr|]. split; [exact_addr|]. split; [apply ma_dec64_length|].
split.
{ apply (proj2 (rwc_app asegs _ _ [C8 (Z_to_bv 64 (SP + -2120))] [C8 (Z_to_bv 64 (Z.of_nat (length tr)))])).
split; [exact_addr|]. cbn [cells_size csize Nat.add].
apply (rw_cells_c44_join _ _ [] [] (Z.of_nat (length tr))); [lia|]. cbn [app].
apply (proj2 (rwc_app asegs _ _ [C4 (Z_to_bv 64 (Z.of_nat (length tr)))] [C4 (Z_to_bv 64 0)])).
split; [exact_addr|]. cbn [cells_size csize Nat.add]. exact_addr. }
split; [exact_addr|].
split.
{ apply (proj2 (rwc_app asegs _ _ [CB 8 junk7] [C8 (Z_to_bv 64 427652)])).
split; [exact_addr|]. cbn [cells_size csize Nat.add]. exact_addr. }
split; [exact_addr|].
split; [unfold alloc_frame, INST, g_instance in *; exact_addr|].
split; [exact_addr|]. split; [exact_addr|]. split; [exact_addr|]. exact_addr.
Qed.
