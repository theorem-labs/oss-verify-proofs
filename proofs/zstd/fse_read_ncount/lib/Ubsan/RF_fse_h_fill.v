(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseHarness.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImg RF_fse_iface RF_fse_h_model.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Lemma sext16_small : forall n, - 32768 <= n < 32768 ->
Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl (n mod 18446744073709551616) 48))) 48 = n.
Proof.
intros n Hn. rewrite Z_to_bv_signed. Local Ltac2 Set LiaHints.tbl := fun () => "0020>22538139632.2 68258611286.2300000100CSS2Hn1H2H02H42H52H9".
rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
change (18446744073709551616 / 2) with 9223372036854775808. change (2^48) with 281474976710656.
Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma rw_update_val : forall n rw, -1 <= n <= rw -> rw <= 4095 ->
bv_swrap 32 (Z.lor (Z.shiftr (bv_signed (Z_to_bv 64 n)) 63 mod 18446744073709551616)
(bv_swrap 32 (0 - n mod 18446744073709551616) mod 18446744073709551616) + rw)
= (if n <? 0 then rw - 1 else rw - n).
Proof.
intros n rw Hn Hrw. destruct (Z.ltb_spec n 0) as [L|G].
- Local Ltac2 Set LiaHints.tbl := fun () => "00;0>13303274085.4 18932863565.5 32976101927.5 34855310397.5 36544257460.5 4034194092.5  44392491954.5 51382735643.5 51593067380.5 66151426447.1166151427842.1900000800900:00B00L00T00^00h00n01401=S2Hn3HrwSSS2Hn3HrwS2Hn3Hrw1GS2Hn3HrwS2Hn3Hrw1GS2Hn3Hrw1GS2Hn1LS1H2H0S1H2H02H4".
assert (n = -1) by lia. subst n.
change (Z.lor (Z.shiftr (bv_signed (Z_to_bv 64 (-1))) 63 mod 18446744073709551616)
(bv_swrap 32 (0 - -1 mod 18446744073709551616) mod 18446744073709551616)) with 18446744073709551615.
apply swrap32_eqm; [lia|]. Z.div_mod_to_equations. lia.
- rewrite signed_lit by lia. rewrite (Z.shiftr_div_pow2 n 63) by lia. rewrite (Z.div_small n (2^63)) by lia.
rewrite Z.mod_0_l by lia. rewrite Z.lor_0_l. rewrite (Z.mod_small n) by lia.
rewrite (swrap32_small (0 - n)) by lia.
apply swrap32_eqm; [lia|]. Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section Fill.
Hypothesis I32R : prod_i32r_stmt.
Variables (gp tp s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : fmem) (SP P D NC : Z) (pl : list Z) (msv tl lo : Z).
Variable POST : machine_state -> Prop.
Hypothesis RSP : 0 <= SP < 2^64.
Hypothesis LO : lo <= SP - 32.
Hypothesis PLO : P + 16 <= lo.
Hypothesis DLO : D + zlen pl <= lo.
Hypothesis DP : D + zlen pl <= P \/ P + 16 <= D.
Hypothesis NCR : SP <= NC /\ NC + 512 < 2^64.
Hypothesis PPOS : 0 < P.
Hypothesis PAL : P mod 8 = 0.
Hypothesis DPOS : 0 < D.
Hypothesis MSV : 0 <= msv <= 255.
Notation W := [(P + 8, P + 16); (NC, NC + 512); (SP - 32, SP)].
Definition nc_arr (acc : list Z) : list byte := u16s (map (Z_to_bv 64) (acc ++ repeat 0 (256 - length acc))).
Definition FINV (m1 : fmem) (acc : list Z) (size : Z) : Prop :=
u8arr usegs m1 NC (nc_arr acc)
/\ prod_at m1 P D size /\ bytes_at usegs m1 D (map (Z_to_bv 8) pl)
/\ stk usegs m1 lo SP
/\ munch W m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1.
Notation STpc pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x28 x29 x30 x31 :=
(MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 tl) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 msv) x19 x20 x21 (Z_to_bv 64 msv) (Z_to_bv 64 257) s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
#[using="I32R RSP LO PLO DLO DP NCR PPOS PAL DPOS MSV"] Lemma fill_loop : forall f s rw size acc m1 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
0 <= s < msv -> 0 < rw <= 4095 -> Z.of_nat (length acc) = s -> msv - s <= Z.of_nat f ->
Forall (fun c => 0 <= c < 256) pl -> 0 <= size <= zlen pl ->
FINV m1 acc size ->
(forall m2 pre rwF r3 (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y28 y29 y30 y31 : word),
fse_fill f pl size s msv rw acc = (pre, rwF, r3) ->
FINV m2 pre r3 -> 0 <= rwF <= 4095 ->
evt usegs POST (STpc 0x13604 m2 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 rwF) y20 y21 y28 y29 y30 y31)) ->
evt usegs POST (STpc 0x135c4 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 rw)
(Z_to_bv 64 (s + 1)) (Z_to_bv 64 (NC + 2 * s)) x28 x29 x30 x31).
Proof.
induction f as [|f IH]; intros s rw size acc m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
HS HRW HL HF PLB SZ (ARR & PR & PAY & ST & MU & WM & MI) K.
{ exfalso. cbn in HF. lia. }
assert (LENP : zlen (map (Z_to_bv 8) pl) = zlen pl) by (rewrite length_map; reflexivity).
zstep. zstep. zstep. zstep.
unfold prod_i32r_stmt, PPROD_I32R in I32R.
call (I32R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SP P D pl size (-1) rw lo);
[ first [ assumption | split; assumption | reflexivity | lia | change (2^31) with 2147483648; lia | change (2^24) with 16777216; lia ] .. | ].
clear PR. rename POST0 into PR. rename PC into ST. rename MI0 into MI. unfold prod_at in PR.
pose proof (int32Range_spec pl size (-1) rw ltac:(apply Forall_all_bytes; exact PLB) ltac:(lia)
ltac:(change (2^31) with 2147483648; lia) ltac:(change (2^31) with 2147483648; lia)) as IR.
rewrite (fse_fill_step f pl size s msv rw acc) in K by lia.
destruct (int32Range pl size (-1) rw) as [n size'] eqn:EI. cbn [fst snd] in *. destruct IR as [NR SZ'].
zstep. if_cases B0; zify_cond B0; [exfalso; lia|]. clear B0.
unfold nc_arr in ARR.
assert (LWS : length (map (Z_to_bv 64) (acc ++ repeat 0 (256 - length acc))) = 256%nat)
by (rewrite length_map, length_app, repeat_length; lia).
pose proof (u16arr_store_ok usegs _ NC _ s (wa (NC + 2 * s)) ARR ltac:(rewrite LWS; lia) eq_refl) as SOK.
zstep.
pose proof (u16arr_write usegs _ NC _ s (Z_to_bv 64 n) ARR ltac:(rewrite LWS; lia)) as ARR2.
clear ARR. store_done.
replace (Z.to_nat s) with (length acc) in ARR2 by lia.
rewrite upd_map_upd_nat, upd_nat_app_zero in ARR2 by lia.
replace (256 - length acc - 1)%nat with (256 - length (acc ++ [n]))%nat in ARR2 by (rewrite length_app; cbn; lia).
fold (nc_arr (acc ++ [n])) in ARR2.
zstep. zstep. rewrite sext16_small by lia.
zstep. zstep. zstep. zstep. rewrite rw_update_val by lia.
set (rw' := if n <? 0 then rw - 1 else rw - n) in *.
assert (RW' : 0 <= rw' <= 4095) by (subst rw'; destruct (Z.ltb_spec n 0); lia).
zstep.
assert (INV2 : FINV m0 (acc ++ [n]) size').
{ split; [exact ARR2|]. split; [exact PR|]. split; [exact PAY|]. split; [exact ST|]. split; [exact MU|]. split; [exact WM| exact MI]. }
assert (LEN2 : zlen (acc ++ [n]) = s + 1) by (rewrite length_app; cbn; lia).
if_cases B; zify_cond B.
-
eapply K; [| exact INV2| exact RW'].
apply fse_fill_stop. left. lia.
- zstep. zstep. zstep.
if_cases B2; zify_cond B2.
+
replace (s + 2) with (s + 1 + 1) by lia.
replace (NC + 2 * s + 2) with (NC + 2 * (s + 1)) by lia.
eapply (IH (s + 1) rw' size' (acc ++ [n])); try lia; [exact PLB| exact INV2|].
intros. eapply K; eassumption.
+
eapply K; [| exact INV2| exact RW'].
apply fse_fill_stop. right. lia.
Qed.
End Fill.
