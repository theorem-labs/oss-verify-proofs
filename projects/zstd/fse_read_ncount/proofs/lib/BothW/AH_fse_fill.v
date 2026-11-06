(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseHarness.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase RtCells AF_fse_iface AH_fse_pure.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import RF_fse_h_model.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKitF.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common.FseWalkKit.simpl_arr_sizes_fwk_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.
Section CANSEC1. Context {rc : runConstT}.
Section Fill.
Hypothesis I32R : prod_i32r_stmtA.
Variables (RNG : footprint) (gp tp s0 s10 : word) (FR : bvmap 5 word) (fc : bv 32).
Variables (m : amem) (SPA NC P D : Z) (pl : list Z) (msv lo : Z).
Variable POST : machine_state -> Prop.
Hypothesis RSPA : 0 <= SPA < 2^64.
Hypothesis LO : lo <= SPA - 32.
Hypothesis LOK : KHIGH <= lo.
Hypothesis PLO : P + 16 <= lo.
Hypothesis DLO : D + zlen pl <= lo.
Hypothesis DP : D + zlen pl <= P \/ P + 16 <= D.
Hypothesis NCB : ablk NC (NC + 512).
Hypothesis NC8 : NC mod 8 = 0.
Hypothesis NCLO : NC + 512 <= lo.
Hypothesis NCP : NC + 512 <= P \/ P + 16 <= NC.
Hypothesis DNC : D + zlen pl <= NC \/ NC + 512 <= D.
Hypothesis P0 : 0 < P.
Hypothesis P8 : P mod 8 = 0.
Hypothesis D0 : 0 < D.
Hypothesis D8 : D mod 8 = 0.
Hypothesis BLKP : ablk P (P + 16).
Hypothesis BLKD : 0 < zlen pl -> ablk D (D + zlen pl).
Hypothesis MSV : 0 <= msv <= 255.
Hypothesis RI : rng_aimg RNG.
Hypothesis RSTK : rng RNG lo (SPA - lo).
Hypothesis RP : rng RNG P 16.
Hypothesis RPS : rng RNG (shad P) 2.
Hypothesis RD : rng RNG D (zlen pl).
Hypothesis RDS : rng RNG (shad D) (nshad (zlen pl)).
Hypothesis RNC : rng RNG NC 512.
Hypothesis RNCS : rng RNG (shad NC) 64.
Hypothesis UNP : unpoisoned m P (P + 16).
Hypothesis UND : unpoisoned m D (D + zlen pl).
Hypothesis UNC : unpoisoned m NC (NC + 512).
Notation W := [(P + 8, P + 16); (NC, NC + 512); (SPA - 32, SPA)].
Definition nc_arrA (acc : list Z) : list byte := u16s (map (Z_to_bv 64) (acc ++ repeat 0 (256 - length acc))).
Definition FINVA (m1 : amem) (acc : list Z) (size : Z) : Prop :=
u8arr bsegs m1 NC (nc_arrA acc)
/\ prod_atA m1 P D size /\ bytes_at bsegs m1 D (map (Z_to_bv 8) pl)
/\ rw_cells bsegs m1 0x99900 [C8 (Z_to_bv 64 0x134068); C8 (Z_to_bv 64 0x9fd38); C8 (Z_to_bv 64 0xa2538);
C8 (Z_to_bv 64 0xa3228); C8 (Z_to_bv 64 0xa3230); C8 (Z_to_bv 64 0xa3220)]
/\ rw_cells bsegs m1 0xa2538 [C8 (Z_to_bv 64 0x7fff8000)]
/\ stk bsegs m1 lo SPA
/\ munch W m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1.
#[using="rc lo RSPA LO LOK PLO DLO DP NCB NC8 NCLO NCP DNC P0 P8 D0 D8 BLKP BLKD UNP UND UNC"] Lemma inv_shadow_fill : forall m1, munch W m m1 ->
unpoisoned m1 P (P + 16) /\ unpoisoned m1 D (D + zlen pl) /\ unpoisoned m1 NC (NC + 512).
Proof.
intros m1 MU. pose proof (ablk_lin _ _ BLKP) as LP. pose proof (ablk_lin _ _ NCB) as LN.
pose proof (ablk_disj_band _ _ BLKP) as DBP. pose proof (ablk_disj_band _ _ NCB) as DBN. unfold KHIGH, KLS, AIMG_HI in *.
split; [| split].
- Local Ltac2 Set LiaHints.tbl := fun () => "0090>13449311261.5523492641683.5532813024925.8232813024925.8438879299635.5543182417634.8243182417634.8454217928338.8254217928338.8400000400800b01N01l02_03P04:04fS2E0S2N0S2DP3NCP3DNC2P83DBP3DBN1H2H42H53NC82LN3H19S2DP3NCP3DNC2D82LN3DBP3DBN2N02LD1H2H42H53H19S4RSPA2LO3DLO2P02D02LP2LN2E01HS2LO3LOK3PLO2DP4NCLO3NCP3DNC2P83DBP3DBN1H2H42H53NC8S2LO3LOK3PLO3DLO2DP4NCLO3NCP3DNC3DBP3DBN2N02H42H5S2DP3NCP3DNC2P82LP3DBP3DBN1H2H42H53H193NC8S2DP3NCP3DNC2D82LP3DBP3DBN2N02LD1H2H42H53H19".
(eapply unpoisoned_munch; [eassumption| exact MU|]); rewrite !shad_div; unfold ASHOFF; cbn [disjoint_from];
(split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia| exact I]).
- destruct (Z.eq_dec (zlen pl) 0) as [E0|N0].
+ replace (D + zlen pl) with D by lia. apply unpoisoned_nil. change (2^64) with 18446744073709551616 in *. lia.
+ pose proof (ablk_lin _ _ (BLKD ltac:(lia))) as LD. unfold AIMG_HI in LD.
(eapply unpoisoned_munch; [eassumption| exact MU|]); rewrite !shad_div; unfold ASHOFF; cbn [disjoint_from];
(split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia| exact I]).
- (eapply unpoisoned_munch; [eassumption| exact MU|]); rewrite !shad_div; unfold ASHOFF; cbn [disjoint_from];
(split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia| exact I]).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Notation STpc pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x27 x28 x29 x30 x31 :=
(MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 s0 (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 2147450880) x20 x21 (Z_to_bv 64 msv) (Z_to_bv 64 P) (Z_to_bv 64 NC) (Z_to_bv 64 257)
s10 x27 x28 x29 x30 x31)
FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
#[using="rc I32R RSPA LO LOK PLO DLO DP NCB NC8 NCLO NCP DNC P0 P8 D0 D8 BLKP BLKD MSV RI RSTK RP RPS RD RDS RNC RNCS UNP UND UNC"] Lemma fill_loopA : forall f s rw size acc m1 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
0 <= s < msv -> 0 < rw <= 4095 -> Z.of_nat (length acc) = s -> msv - s <= Z.of_nat f ->
Forall (fun c => 0 <= c < 256) pl -> 0 <= size <= zlen pl ->
FINVA m1 acc size ->
(forall m2 pre rwF r3 (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y21 y27 y28 y29 y30 y31 : word),
fse_fill f pl size s msv rw acc = (pre, rwF, r3) ->
FINVA m2 pre r3 -> 0 <= rwF <= 4095 ->
evtF bsegs RNG POST (STpc 0x80fcc m2 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 (Z_to_bv 64 rwF) y21 y27 y28 y29 y30 y31)) ->
evtF bsegs RNG POST (STpc 0x80f60 m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (NC + 2 * s))
(Z_to_bv 64 rw) (Z_to_bv 64 (s + 1)) (Z_to_bv 64 (NC + 2 * s)) x28 x29 x30 x31).
Proof.
induction f as [|f IH]; intros s rw size acc m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
HS HRW HL HF PLB SZ (ARR & PR & PAY & GOT & SHB & ST & MU & WM & MI) K.
{ exfalso. cbn in HF. Local Ltac2 Set LiaHints.tbl := fun () => "0120?10673606453.12312430247196.11314087519375.12314939502105.12715682813287.12316220341382.95 16480363451.11116750069139.11317982984349.1101948619306.113 19617313304.12323683590488.20 24143684617.11824401123790.12026263773998.12826507259922.11829414982570.12229501631497.11829782367974.11629782367974.12431834184427.12332689308706.12334799861807.12336277103318.12937431315235.11838170691122.11039866243417.11739913882569.95 40683621978.93 40926838968.11840926838968.11941563518094.11742187540944.11343110765769.11045241786759.11347438200993.1234758572797.117 50045042275.11850390819137.11750467229443.11753561511007.1185455110839.117 5461597289.123 54893511902.12354950719482.11856299285676.12256561430791.11357622410744.11458389400689.11858513964662.95 59314873579.11759314923118.84 59433371045.12359435130667.12759588178610.12861330623914.12361937685140.12461937685145.12763997073899.1116458892537.118 64607965438.12367142665296.12167148956123.11668394932694.1107606247776.121 9178932959.20  00000=00>00?00@00k01<01M02C02S02d02e03903R04;04L05H05W06006=06J06W06X06l07\08A08N08_09009U0:B0:o0;?0;l0<=0<b0=O0>?0>P0>m0?V0@E0A50AG0B;0BT0Be0CJ0CY0DD0DU0EE0EL0E\0FD0FQ0F^0F_0F`0G00G`0Ga0H>0H[0Hl0I=0IMS2HF4LWS03LWSFFFS2DP3NCP3DNC2P02D02HF4LENP2LN4LWS03LWS4LEN2S3HRW2HF4LWS03LWSS3HRW2HF4LWS03LWSS2LO3PLO3DLO2DP4NCLO3NCP3DNC2P02D02HF4LENP2LN4LWS03LWSS2HF2SZ4LWS03LWSS3PLO2HF4LWS03LWSFS3NC83MSV2HS1H2H02H4S2P02D02HL2HF2LN4LWS03LWSS2DP3NCP3DNC2P02D02HL2HF4LENP2LN4LWS03LWSS3HRW2HF4LWS03LWSS2LO3PLO2DP4NCLO3NCP3DNC2P02D03MSV2HS2HL2HF4LENP2LN4LWS03LWSS2HF4LWS03LWS1BS2P02D02HL2HF2LN4LWS03LWSS2HF4LWS03LWSS2HF4LWS03LWSS2HF4LWS03LWSFS2HF4LWS03LWS3RW'2B2S2DP3NCP3DNC2P02D03MSV2HS2HL2HF4LENP2LN4LWS03LWSS2P02D03MSV2HS2HF4LENP2LP2LN4LWS03LWSS2HF4LWS03LWSS3HRW2HF4LWS03LWSS3HRW2HF4LWS03LWSS2DP3NCP3DNC2P02D03MSV2HS2HL2HF2SZ2LNS2DP3NCP3DNC2P02D03MSV2HS2HF4LENP2LN4LWS03LWSS2DP3NCP3DNC2P02D03MSV2HS2HF4LENP2LN4LWS03LWSS2HF4LWS03LWS2NRS2LO3PLO2DP4NCLO3NCP3DNC2P02D02HF2LN4LWS03LWSS3HRW2HF4LWS03LWSS2LO3PLO4NCLO2P02D02HF2LP2LN4LWS03LWSS2DP3NCP3DNC2P02D02HF2SZ4LENP2LN4LWS03LWS3SZ'S2DP3NCP3DNC2P02D03MSV2HS2HL2HF4LENP2LN4LWS03LWSS3HRW2HF4LWS03LWSS2P02D03HRW2HF2LN4LWS03LWS2NRS2DP3NCP3DNC2P02D02HL2HF4LENP2LN4LWS03LWSS2DP3NCP3DNC2P02D03HRW2HF4LENP2LN4LWS03LWS2NR1HS2DP3NCP3DNC2P02D03MSV2HS2HL2HF4LENP2LN4LWS03LWSS2HS2HF4LWS03LWS1BS2DP3NC83NCP3DNC2P02D03MSV2HS2HL2HF4LENP2LN4LWS03LWSS2P02D02HL2HF2LN4LWS03LWSS2HF4LWS03LWS3RW'S2LO3PLO4NCLO2P02D02HF2LP2LN4LWS03LWSS2HF4LWS03LWS1HS2DP3NCP3DNC2P02D03MSV2HS2HL2HF2LN4LWS03LWSS3HRW2HF4LWS03LWSS2DP3NCP3DNC2P02D03MSV2HS2HF4LENP2LN4LWS03LWS2BGS2HS2HFS2HF4LWS03LWS2B2S2P02D03MSV2HS2HL2HF4LENP2LP2LN4LWS03LWSS2HF4LWS03LWSS2HF4LWS03LWSFFS2HS2HF4LWS03LWSS2DP3NCP3DNC2P02D03MSV2HS2HL2HF4LENP2LN4LWS03LWSFS2P02D03MSV2HS2HF2LN4LWS03LWSS2P02D03MSV2HS2HF2LN4LWS03LWSS3HRW2HF4LWS03LWSS3MSV2HF4LWS03LWSS3NC82HS1H2H42H5".
lia. }
assert (LENP : zlen (map (Z_to_bv 8) pl) = zlen pl) by (rewrite length_map; reflexivity).
destruct (inv_shadow_fill m1 MU) as (UNP1 & UND1 & UNC1).
pose proof (ablk_lin _ _ BLKP) as LP. pose proof (ablk_lin _ _ NCB) as LN. unfold AIMG_HI in LP, LN.
unfold nc_arrA in ARR.
assert (LWS0 : length (acc ++ repeat 0 (256 - length acc)) = 256%nat) by (rewrite length_app, repeat_length; lia).
assert (LWS : length (map (Z_to_bv 64) (acc ++ repeat 0 (256 - length acc))) = 256%nat) by (rewrite length_map; exact LWS0).
zstep. zstep. zstep. zstep.
unfold prod_i32r_stmtA, APROD_I32R in I32R.
eapply evtF_cut; [ eapply I32R with (SPV := SPA) (P := P) (D := D) (pl := pl) (size := size) (mn := -1) (mx := rw) (lo := lo)
| post_call bsegs m1 ];
[ first [ assumption | split; assumption | reflexivity | lia | (unfold KHIGH in *; lia)
| change (2^31) with 2147483648; lia | change (2^24) with 16777216; lia | solve_rng ] .. | ].
try clear PR. rename POST0 into PR. rename PC into ST. rename MI0 into MI. unfold prod_atA in PR.
pose proof (int32Range_spec pl size (-1) rw ltac:(apply Forall_all_bytes; exact PLB) ltac:(lia)
ltac:(change (2^31) with 2147483648; lia) ltac:(change (2^31) with 2147483648; lia)) as IR.
rewrite (fse_fill_step f pl size s msv rw acc) in K by lia.
destruct (int32Range pl size (-1) rw) as [n size'] eqn:EI. cbn [fst snd] in *. destruct IR as [NR SZ'].
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
assert (RD0 : ov_read_bytes bsegs mx (wa (Z.shiftr (NC + 2 * s) 3 + 2147450880)) 1 = Some [Z_to_bv 8 0])
by (destruct (inv_shadow_fill mx MU) as (_ & _ & UNC0);
apply (unpoisoned_full_rd bsegs mx NC (NC + 512)); [exact UNC0| |];
rewrite ?shad_div, ?Z.shiftr_div_pow2 by lia; unfold ASHOFF; change (2^3) with 8; clear - NC8 HS MSV; Z.div_mod_to_equations; lia)
end.
zstep. if_cases BG; zify_cond BG; [exfalso; rewrite ?unsigned_lit in BG by lia; lia|].
zstep. zstep. zstep.
zstep. if_cases B0; zify_cond B0; [exfalso; apply B0; reflexivity|].
pose proof (u16arr_store_ok bsegs _ NC _ s (wa (NC + 2 * s)) ARR ltac:(rewrite LWS; lia) eq_refl) as SOK.
zstep.
pose proof (u16arr_write bsegs _ NC _ s (Z_to_bv 64 n) ARR ltac:(rewrite LWS; lia)) as ARR2.
clear ARR. store_done.
replace (Z.to_nat s) with (length acc) in ARR2 by lia.
rewrite upd_map_upd_nat, upd_nat_app_zero in ARR2 by lia.
replace (256 - length acc - 1)%nat with (256 - length (acc ++ [n]))%nat in ARR2 by (rewrite length_app; cbn; lia).
fold (nc_arrA (acc ++ [n])) in ARR2.
zstep. zstep. rewrite sext16_smallA by lia.
zstep. zstep. zstep. zstep. rewrite rw_update_valA by lia.
set (rw' := if n <? 0 then rw - 1 else rw - n) in *.
assert (RW' : 0 <= rw' <= 4095) by (subst rw'; destruct (Z.ltb_spec n 0); lia).
zstep.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => assert (INV2 : FINVA mx (acc ++ [n]) size') end.
{ split; [exact ARR2|]. split; [exact PR|]. split; [exact PAY|]. split; [exact GOT|]. split; [exact SHB|].
split; [exact ST|]. split; [exact MU|]. split; [exact WM| exact MI]. }
assert (LEN2 : zlen (acc ++ [n]) = s + 1) by (rewrite length_app; cbn; lia).
if_cases B; zify_cond B.
-
eapply K; [| exact INV2| exact RW'].
apply fse_fill_stop. left. lia.
- zstep. zstep. zstep. zstep.
if_cases B2; zify_cond B2.
+
replace (s + 2) with (s + 1 + 1) by lia.
replace (NC + 2 * s + 2) with (NC + 2 * (s + 1)) by lia.
eapply (IH (s + 1) rw' size' (acc ++ [n])); try lia; [exact PLB| exact INV2|].
intros. eapply K; eassumption.
+
zstep.
eapply K; [| exact INV2| exact RW'].
apply fse_fill_stop. right. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Fill.
End CANSEC1.
