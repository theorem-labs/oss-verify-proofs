(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseHarness.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import PImg RF_fse_iface RF_fse_h_model.
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
u8arr psegs m1 NC (nc_arr acc)
/\ prod_at m1 P D size /\ bytes_at psegs m1 D (map (Z_to_bv 8) pl)
/\ stk psegs m1 lo SP
/\ munch W m m1 /\ wmono psegs m m1 /\ mem_inv psegs m1.
Notation STpc pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x28 x29 x30 x31 :=
(MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 msv) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 tl) x19 (Z_to_bv 64 NC) (Z_to_bv 64 msv) x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
#[using="I32R RSP LO PLO DLO DP NCR PPOS PAL DPOS MSV"] Lemma fill_loop : forall f s rw size acc m1 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
0 <= s < msv -> 0 < rw <= 4095 -> Z.of_nat (length acc) = s -> msv - s <= Z.of_nat f ->
Forall (fun c => 0 <= c < 256) pl -> 0 <= size <= zlen pl ->
FINV m1 acc size ->
(forall m2 pre rwF r3 (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y23 y28 y29 y30 y31 : word),
fse_fill f pl size s msv rw acc = (pre, rwF, r3) ->
FINV m2 pre r3 -> 0 <= rwF <= 4095 ->
evt psegs POST (STpc 0x135d4 m2 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 rwF) y22 y23 y28 y29 y30 y31)) ->
evt psegs POST (STpc 0x13598 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 rw)
(Z_to_bv 64 (NC + 2 * s)) (Z_to_bv 64 (s + 1)) x28 x29 x30 x31).
Proof.
induction f as [|f IH]; intros s rw size acc m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
HS HRW HL HF PLB SZ (ARR & PR & PAY & ST & MU & WM & MI) K.
{ exfalso. cbn in HF. Local Ltac2 Set LiaHints.tbl := fun () => "00h0>10675614223.9412430247196.8613476481703.8714089503157.9414939502105.9915680798813.9416214116254.6716478252705.8317980497287.821948619306.86 19615371042.9424407430900.9126261676838.9826507259922.8929253947345.8629415147168.9330450768249.8631827797969.9432682932504.9433180453167.8634801810709.9437431315235.8939872418915.8839924302033.674063864516.86 40678983547.8740922303549.8940922712101.8841569925556.8843117189587.8247444606363.944747969479.88 50038735451.8950384383099.8850477826617.8853567811687.895461258125.88 5468053843.94 54950719482.8956299285676.9456818256961.8758389400689.8958503544174.6759314923118.6459439839391.9459586081466.9861336826000.9461937685145.9961937685147.9764003347697.836458892537.89 67142665296.9368396635340.827606247776.93 8300723466.86 9672631602.83 00000800900<00=00>00K00P00U00Y00^00_00j01601S01[01e01f01n01o02<02K02^02j02o03=03K03Z03i04404904H04Z04_04n05905C05U05b06=06B06E06[06`06g06k07307;07<07=07D07Z07i07n08:08I08JS2HF3LWSFS1HFFS2HF3LWS4LEN2S3HRWS3HRWS2SZS3PLOFS2HL2HF3LWSS3HRW2HF3LWSS2LO3PLO3NCR3MSV2HS2HL2HF3LWSS3NCR2HFS2HF3LWS1BFS2HF3LWSFS2LO3DLO4LENPS2HF3LWS3RW'2B2S3NCR3MSV2HS2HF3LWSS3HRW2HF3LWSS3HRWS2DP4PPOS4LENPS3MSV2HS2HL2HFS3MSV2HS2HF3LWSS3MSV2HS2HF3LWSS2HF2NR3LWSS3HRWS2HF2SZ3SZ'3LWSS3MSV2HS2HL2HF3LWSS3HRWS3HRW2HF2NR3LWSS2HL2HF3LWSS3HRW2NR1HS3MSV2HS2HL2HF3LWSS2HS2HF3LWS1BS2LO3PLO3NCR4PPOS2HL2HF3LWSS3RW'S1HS2LO3DLO3NCR2HL2HF3LWSS3HRWS2HS2HFS2B2S2HF3LWSS2HF3LWSFFS2HS2HFS2LO3PLO3NCR2HL2HF3LWSS3MSV2HS2HF3LWSS3HRWS3MSV2HF3LWSS2LO3PLO3NCR2HFS".
lia. }
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
unfold nc_arr in ARR.
assert (LWS : length (map (Z_to_bv 64) (acc ++ repeat 0 (256 - length acc))) = 256%nat)
by (rewrite length_map, length_app, repeat_length; lia).
pose proof (u16arr_store_ok psegs _ NC _ s (wa (NC + 2 * s)) ARR ltac:(rewrite LWS; lia) eq_refl) as SOK.
zstep.
pose proof (u16arr_write psegs _ NC _ s (Z_to_bv 64 n) ARR ltac:(rewrite LWS; lia)) as ARR2.
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
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Fill.
