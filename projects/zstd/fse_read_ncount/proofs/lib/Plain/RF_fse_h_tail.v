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
Lemma upd_app_mid : forall {X} (l1 : list X) (x v : X) (l2 : list X), upd (l1 ++ x :: l2) (length l1) v = l1 ++ v :: l2.
Proof. induction l1 as [|a l1 IH]; intros x v l2; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Section Tail.
Hypothesis U32R : prod_u32r_stmt.
Variables (gp tp s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : fmem) (SP P D BUFF : Z) (pl data : list Z) (msv tl dsz bsz lo : Z).
Variable POST : machine_state -> Prop.
Hypothesis RSP : 0 <= SP < 2^64.
Hypothesis LO : lo <= SP - 16.
Hypothesis PLO : P + 16 <= lo.
Hypothesis DLO : D + zlen pl <= lo.
Hypothesis DP : D + zlen pl <= P \/ P + 16 <= D.
Hypothesis BLO : 0 <= BUFF /\ BUFF + bsz <= lo.
Hypothesis BP : BUFF + bsz <= P \/ P + 16 <= BUFF.
Hypothesis BD : BUFF + bsz <= D \/ D + zlen pl <= BUFF.
Hypothesis DSZ : zlen data = dsz.
Hypothesis PLB : Forall (fun c => 0 <= c < 256) pl.
Hypothesis PPOS : 0 < P.
Hypothesis PAL : P mod 8 = 0.
Hypothesis DPOS : 0 < D.
Notation W := [(P + 8, P + 16); (BUFF, BUFF + bsz); (SP - 16, SP)].
Definition TINV (m1 : fmem) (filled : list Z) (rest : list byte) (size : Z) : Prop :=
u8arr psegs m1 BUFF (map (Z_to_bv 8) filled ++ rest)
/\ prod_at m1 P D size /\ bytes_at psegs m1 D (map (Z_to_bv 8) pl)
/\ stk psegs m1 lo SP
/\ munch W m m1 /\ wmono psegs m m1 /\ mem_inv psegs m1.
Notation STpc pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31 :=
(MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 msv) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 tl) (Z_to_bv 64 BUFF) (Z_to_bv 64 dsz) (Z_to_bv 64 bsz) x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
#[using="U32R RSP LO PLO DLO DP BLO BP BD DSZ PLB PPOS PAL DPOS"] Lemma tail_loop : forall f size acc rest m1 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
(1 <= f)%nat -> length rest = f -> dsz + zlen acc + Z.of_nat f = bsz -> 0 <= size <= zlen pl -> 0 <= dsz ->
TINV m1 (data ++ acc) rest size ->
(forall m2 junkF remF (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y23 y28 y29 y30 y31 : word),
fseB_tail_loop f pl size acc = (junkF, remF) ->
TINV m2 (data ++ junkF) [] remF -> 0 <= remF <= size ->
evt psegs POST (STpc 0x136a8 m2 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y23 y28 y29 y30 y31)) ->
evt psegs POST (STpc 0x13688 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (Z.of_nat f)) (Z_to_bv 64 (BUFF + (dsz + zlen acc))) x28 x29 x30 x31).
Proof.
induction f as [|f IH]; intros size acc rest m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
HF HR HB SZ DS0 (BA & PR & PAY & ST & MU & WM & MI) K.
{ exfalso. Local Ltac2 Set LiaHints.tbl := fun () => "00X0?11433930176.97 12430247196.93 13476481703.94 14266301866.97 16012967864.95 17980497287.89 1948619306.93  19617478418.97 22214649138.90 26492565650.96 29049263737.93 29052640235.93 30388921758.95 3413639356.97  3512322914.74  3516842969.89  36940895164.96 36940895768.95 3746428605.95  38532374547.72 4063864516.93  47102024239.93 47438300587.97 51317269556.93 55142473048.89 55268463181.12156818256961.94 57208007268.95 57547325170.95 59314923118.68 59350764616.96 59568192801.97 6059836484.97  60942693686.96 62843005514.97 63645443404.96 65527147462.97 8993187595.93  9208585610.97  9467378092.96  00000?00@00Q00b00o01A01T01U01d02F02G02]02l03=03L03[03n04A04S04a05805S05i06;06J06`07107D07S07]08708808G08^08j09@09S09b0:@0:VS2HF2HR2HB4LBA'FS2HF2HR2HB4LBA'1HS2HF2HR2HB4LBA'1BS2HB4LBA'3SZ'S2HF2HR2HB2SZ4LBA'S3PLO2HF2HR2HB4LBA'FS2HF2HR2HB4LBA'S2LO3PLO3BLO3DSZ2HF2HR2HB3LBA4LBA'FS2LO3BLO2HF2HR2HB4LBA'S2HF2HR2HB4LBA'S2HF2HR2HB4LBA'1BS2HF2HR2HB4LBA'S2HF2HR2HB4LBA'S3DSZ2HF2HR2HB4LBA'S3DSZ2HF2HR2HB4LBA'S2HF2HR2HB4LBA'2CRS3DSZ2HF2HR2HBS2DP2HF2HR2HB4LENP4LBA'S2LO3DLO2HF2HR2HB4LENP4LBA'S2HF2HR2HB2SZ4LBA'3SZ'S2BP2HF2HR2HB4LBA'S2HF2HR2HB4LBA'S2HF2HR2HB4LBA'3SZ'2H1S2HF2HR2HB4LBA'1HS3DSZ2HF2HR2HB4LBA'S2HF2HR2HB4LBA'S2HF2HR2HBS3RSP2LO3BLO2HF2HR2HB4LBA'FS2HF2HR2HB4LBA'S3BLO3DSZ2HF2HR2HB4LBA'S2HB2HR4LBA'S2BP3DSZ2HF2HR2HB4LBA'S2HF2HR2HB3DS04LBA'S2HF2HR2HB4LBA'S3RSP2LO3BLO3DSZ2HF2HR2HB4LBA'S2BD3DSZ2HF2HR2HB4LBA'".
lia. }
assert (LENP : zlen (map (Z_to_bv 8) pl) = zlen pl) by (rewrite length_map; reflexivity).
assert (AB : all_bytes pl) by (apply Forall_all_bytes; exact PLB).
zstep. zstep. zstep. zstep.
unfold prod_u32r_stmt, PPROD_U32R in U32R.
assert (LBA : zlen (map (Z_to_bv 8) (data ++ acc) ++ rest) = bsz).
{ rewrite length_app, length_map, length_app. lia. }
assert (LBA' : Z.of_nat (length (map (Z_to_bv 8) (data ++ acc)) + length rest) = bsz) by (rewrite <- length_app; exact LBA).
call (U32R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SP P D pl size 0 255 lo);
[ first [ assumption | split; assumption | reflexivity | lia | change (2^31) with 2147483648; lia | change (2^24) with 16777216; lia ] .. | ].
clear PR. rename POST0 into PR. rename PC into ST. rename MI0 into MI. unfold prod_at in PR.
pose proof (uint32Range_spec pl size 0 255 AB ltac:(lia) ltac:(lia) ltac:(change (2^32) with 4294967296; lia)) as UR.
rewrite fseB_tail_loop_step in K.
destruct (uint32Range pl size 0 255) as [c size'] eqn:EU. cbn [fst snd] in *. destruct UR as (CR & SZ' & _).
destruct rest as [|r0 rest']; [cbn in HR; lia|]. cbn [length] in HR.
pose proof (u8arr_store_ok psegs _ BUFF _ (dsz + zlen acc) (wa (BUFF + (dsz + zlen acc))) BA ltac:(rewrite LBA; lia) eq_refl) as SOK.
zstep. rewrite le1_lit.
pose proof (u8arr_write psegs _ BUFF _ (dsz + zlen acc) (Z_to_bv 8 c) BA ltac:(rewrite LBA; lia)) as BA2.
clear BA. store_done.
replace (Z.to_nat (dsz + zlen acc)) with (length (map (Z_to_bv 8) (data ++ acc))) in BA2 by (rewrite length_map, length_app; lia).
rewrite upd_app_mid in BA2.
replace (map (Z_to_bv 8) (data ++ acc) ++ Z_to_bv 8 c :: rest') with (map (Z_to_bv 8) (data ++ (acc ++ [to_byte c])) ++ rest') in BA2.
2:{ rewrite (app_assoc data acc), map_app. cbn [map]. rewrite <- app_assoc. cbn [app].
unfold to_byte. rewrite (Z.mod_small c 256) by lia. reflexivity. }
zstep. zstep.
replace (Z.of_nat (S f) + -1) with (Z.of_nat f) by lia.
replace (BUFF + (dsz + zlen acc) + 1) with (BUFF + (dsz + zlen (acc ++ [to_byte c]))) by (rewrite length_app; cbn [length]; lia).
assert (INV2 : TINV m0 (data ++ (acc ++ [to_byte c])) rest' size').
{ split; [exact BA2|]. split; [exact PR|]. split; [exact PAY|]. split; [exact ST|]. split; [exact MU|]. split; [exact WM| exact MI]. }
zstep. if_cases B; zify_cond B.
-
eapply (IH size' (acc ++ [to_byte c]) rest'); try lia; [rewrite length_app; cbn [length]; lia| exact INV2|].
intros. eapply K; try eassumption. lia.
-
assert (f = 0%nat) by lia. subst f. destruct rest'; [|cbn in HR; lia].
eapply K; [reflexivity| exact INV2| lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Tail.
