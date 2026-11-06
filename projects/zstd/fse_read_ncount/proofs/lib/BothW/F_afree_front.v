(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode Arr InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg AProto ABase ABytes AQConst ADepot_iface.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import AKit AKit2 AKitQ F_aalloc_s F_aalloc1 F_aalloc3 F_aunwind F_aunwind2 F_afree_s F_aintal F_afree_iseg F_adealloc F_aqchunk.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac band_lin :=
repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6254592 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
exists k, 0 <= k <= 1 /\ 6254592 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
let G1 := fresh "G" in let G2 := fresh "G" in
lazymatch type of H with
| sclr ?a ?n =>
assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
| iclr ?a ?n =>
assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
| 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>
assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
| ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
end.
Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
Section CANSEC1. Context {rc : runConstT}.
Section WithDepot.
Variable DI : ADepotIface.
Notation front_W L sp t hm :=
([(bv_unsigned sp - 4096, bv_unsigned sp); (0xa3740, 0xa3740 + 0x81030); (0x131fc8, 0x131fc8 + 4);
(t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
(ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).
Definition free_front_post (L : alayout) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(t hm n b1 actx lo : Z) (trt : list Z) (m : amem) : machine_state -> Prop :=
fun ms' => exists (id : Z) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m' (sj' tb' : list word) (junk2 : list byte),
ms' = MS (mkR (Z_to_bv 64 0x5336c) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2
sp (Z_to_bv 64 (hm + 16))
(Z_to_bv 64 0x9f1b0) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (bv_unsigned sp + -2128))
(Z_to_bv 64 hm) (Z_to_bv 64 n) a6 a7
(Z_to_bv 64 0x532fc) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81))
s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x36488) fc None m' (seg_rom bsegs)
/\ munch (front_W L sp t hm) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp + -2128)
/\ 0 < id < 2^31
/\ rw_cells bsegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
/\ rw_cells bsegs m' (hm + 16) [C8 (Z_to_bv 64 id)]
/\ u64arr bsegs m' (t + 2800) sj' /\ length sj' = 46%nat
/\ rw_cells bsegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
/\ rw_cells bsegs m' 0x131fc8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
/\ stk bsegs m' 0xa3740 (0xa3740 + 0x81030)
/\ (forall j, 0 <= j < 32768 -> bytes_at bsegs m' (0xa3748 + 8 * j) (le8 (Z_to_bv 64 0)))
/\ rw_cells bsegs m' (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)]
/\ u64arr bsegs m' (bv_unsigned sp + -2128 + 16) tb' /\ length tb' = 255%nat
/\ rw_cells bsegs m' (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ ADEPOT DI L m'.
#[using="Type"] Lemma free_front_spec : forall (L : alayout) (ia : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem)
(t ctx hm n b1 actx lo top bot : Z) (uw : word) (sj : list word) (trt : list Z),
stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
mem_inv bsegs m ->
tp = Z_to_bv 64 ATP ->
a0 = Z_to_bv 64 (hm + 16) ->
bv_unsigned sp mod 16 = 0 ->
allocA_cells m ctx t ->
rw_cells bsegs m 0x99900 [C8 (Z_to_bv 64 0x134068); C8 (Z_to_bv 64 0x9fd38); C8 (Z_to_bv 64 0xa2538);
C8 (Z_to_bv 64 0xa3228); C8 (Z_to_bv 64 0xa3230); C8 (Z_to_bv 64 0xa3220)] ->
rw_cells bsegs m 0xa323c [C4 (Z_to_bv 64 30)] ->
rw_cells bsegs m 0x13408a [C1 (Z_to_bv 8 1)] ->
rw_cells bsegs m 0x998f0 [C8 (Z_to_bv 64 0x131fe0)] -> rw_cells bsegs m 0x131fe0 [C8 (Z_to_bv 64 4096)] ->
rw_cells bsegs m 0x134008 [C8 (Z_to_bv 64 0)] ->
rw_cells bsegs m 0x131fc8 [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
stk bsegs m 0xa3740 (0xa3740 + 0x81030) ->
(ia = true -> forall j, 0 <= j < 32768 -> bytes_at bsegs m (0xa3748 + 8 * j) (le8 (Z_to_bv 64 0))) ->
rw_cells bsegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
rw_cells bsegs m t [C8 (Z_to_bv 64 ctx); C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
rw_cells bsegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells bsegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->
0 < ctx -> AIMG_HI <= ctx -> ctx + 4096 <= ATOP ->
iclr t 4096 -> t + 4096 <= ATOP -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
rw_cells bsegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
rw_cells bsegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= n < 2^32 -> hm mod 16 = 0 ->
ablk hm (hm + 16 + rup n 8) -> hm + 24 <= ATOP ->
(hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) ->
ADEPOT DI L m ->
AIMG_HI <= al_nodes L -> al_nodes L + 1048576 <= ATOP -> AIMG_HI <= al_store L -> al_store L + 8388608 <= ATOP ->
(hm + 24 <= al_nodes L \/ al_nodes L + 1048576 <= hm) -> (hm + 24 <= al_store L \/ al_store L + 8388608 <= hm) ->
(t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
(ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) ->
afree_unw RNG lo m top sp s0 ra trt ->
bv_unsigned s0 <> bv_unsigned sp + 8 ->
In (AFREE_PC :: trt) (al_U L) ->
0 <= bot -> bot < bv_unsigned sp -> bot < top -> 4096 <= top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG hm 24 ->
evtF bsegs RNG (free_front_post L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n b1 actx lo trt m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).
Proof.
intros until trt.
intros ST CEIL LO MI TP Ha0 SP16 AC GOT6 MCS CF34 GPG PGC HK FL IAS IAM CT8 TT0 SW UW STATS LSJ CX0 C0 C1 T0 T1 CT2
HD HUW B1 B13 NR AL HLO HHI DHT DHC DEP N0 N1 R0 R1 DHN DHS DTN DTS DCN DCS
UNW S0NE TRU B0 BB BOTOP TOP RA4 RANE RIMG RSTK RCTX RT RNO RST RH. band_lin.
pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO.
pose proof (afree_unw_length _ _ _ _ _ _ _ _ UNW) as LTRT.
Local Ltac2 Set LiaHints.tbl := fun () => "01Y0?11767339402.17712217537535.16813748778845.19813993462363.17214966552394.14215256076689.16915819558015.1671744903108.165 19590291912.16620550700810.17720550700810.18022081276064.16523302269856.16524056314984.22024786325331.2002529570720.165 26359334394.19926496924968.16527165323987.20027165323987.21827176698494.16927393365820.16928575982988.17228575982988.23828686419730.20128686419730.23829147777627.17230229009457.16930632115488.16531870100064.16532106802715.16533688774939.16933725192209.16933747012490.19933824905934.16634445441386.14235005089235.20035005089235.21835005089235.23636166301066.17736166301066.18037592147547.17237592147547.19838377103120.17738377103120.18038377103120.22141024469503.20041024469503.2194109368127.221 42877022815.17742877022815.18043119154323.20043119154323.21843185090954.20043229261695.17244503560193.22145898310432.16546173415533.16946173415533.18047078357070.22148155618387.20048155618387.21848486878908.16949265311904.16549921929014.17549921929014.20049921929014.22150540877779.20050540877779.21851234294911.19752450093533.20052569147371.20052569147371.20152569147371.21852569147371.21952569147371.22052569147371.23652569147371.23956170256219.19956170256219.22056759370246.17257993619733.22159310676432.19559310676438.1986027852627.200 6027852627.218 6027852627.236 60657043208.16964949347711.16665285823486.16965285823486.18065450282016.1656562149469.2   6566541509.180 66260016006.20466260016006.22266260016006.24067469470029.16767469470029.20467469470029.2248800126135.201 8800126135.204 8800126135.222 8800126135.238 8800126135.240 00000700800900:00>00U00V01801901:01;01F01Q01U02>02I02J03:03c04U04^04_05005O06E07H07I07J07U07`08108508608708808C08l09^0:30:;0:C0:D0:E0:J0:O0:T0:`0;S0;[0;\0;]0<F0=80=@0=A0=L0=W0=n0>M0>X0?A0@30@40@?0@O0@_0@o0AX0BE0BF0BG0BS0CL0C\0DO0EH0E]0F_0Fd0Fi0G>0GD0Gj0HP0I90Ik0J@0JE0JF0JK0JP0J[0J`0Je0Jl0K30K:0KT0LP0M]0N70Ne0O^0P=0PZS5TOPLESSSS2LOS3LSJ4RANE3HL24LTRT3SPRSS4CEIL2LO3LSJ2T02T13HL24LTRT3SPR1HSSSS4CEIL2LO1HS4CEIL2LO1HS2LOS4CEIL2LO4SP163LSJ2T03HL24LTRT3LTB4LTB21HS4CEIL2LO1HSS4CEIL2LO2C02C13LSJ2T02T13HL24LTRT3SPR1H3HHI3HL1S4CEIL2LO4SP163LSJ2T03HL24LTRT3LTB4LTB21HS4CEIL2LO4SP163LSJ2T03HL13HL24LTRT3LTB4LTB24LSJ31HS3RA43RARFS4CEIL2LO2GE2Ha1HS3LSJ3HL24LTRT3LTB4LTB24LSJ32HqS4CEIL2LO4SP163LSJ2T12AL3HHI3HL24LTRT3SPR3LTB4LTB21Y1HS4CEIL2LO4SP163LSJ2AL3HHI2N12R13HL13HL24LTRT3SPR3LTB4LTB24LSJ31Y2Y0SSS4CEIL2LO1HS4CEIL2LO1HS4CEIL2LO3HHI3HL1S2BBFSSS3HHI3HL11HS4CEIL2LO4SP163LSJ2T03HL24LTRT3LTB4LTB21HS4CEIL2LO4SP163LSJ2T03HL13HL24LTRT3LTB4LTB24LSJ31HS4CEIL2LO2N02R03HL11HS2LO3HspS2LO3HspSSS3HspS3HspS3HspS4CEIL2LO2T1S4CEIL2LO3LSJ2T13HHI3HL24LTRT3SPR3LTB4LTB24LSJ31Y1HS2LO3HspSSS4CEIL2LO4SP163LSJ2T03HL24LTRT3LTB4LTB21HS4CEIL2LO4SP163LSJ2T03HL13HL24LTRT3LTB4LTB24LSJ31HS2LO3HspSS4LTRT4LTB2S4CEIL2LO1HS4SP163LSJ3HL24LTRT3SPRS4SP163LSJ3LTR3HL24LTRT3SPR3LTBS4LTRT4LTB2S4CEIL2LO4SP163LSJ2T03HL24LTRT3LTB4LTB21HS4CEIL2LO4SP163LSJ2T03HL13HL24LTRT3LTB4LTB24LSJ31HFS4CEIL2LO1HS4CEIL2LO4SP471HS4CEIL2LO4SP471HS4CEIL2LO4SP471HS4CEIL2LO4SP163LSJ2T03HL24LTRT3LTB4LTB21HS4CEIL2LO3LSJ2T03HL13HL24LTRT3LTB4LTB24LSJ31HSSS4CEIL2LO2T1S4CEIL2LO3LSJ2C12T13HL24LTRT3SPR3LTB4LTB21Y1H4SP162AL3HHIS4CEIL2LO2T13HHIS4CEIL2LO3LSJ2T13HHI3HL24LTRT3SPR3LTB4LTB24LSJ31Y1HS4CEIL2LO3LSJ2C12T13HHI3HL24LTRT3SPR3LTB4LTB24LSJ31Y2Y01HS4CEIL2LO3HHI2N12R11HS4CEIL2LO3LSJ2T02T13HHI2N12R13HL24LTRT3SPR3LTB4LTB24LSJ31Y2Y02Y11HS3HspS3HspS4CEIL2LO3TOP2GE2Ha1HS4SP47S4SP163LSJ4S0NE4LTRT2LT1H2H12H22H63H16S4SP163LSJ4S0NE4LTRT2LT1H2H12H22H83H18S4CEIL2LO4SP163LSJ2T03HL24LTRT3LTB4LTB21HS4CEIL2LO4SP163LSJ2T03HL13HL24LTRT3LTB4LTB24LSJ31HS4CEIL2LO2N02R03HL11HS3S0RSS3BTXS3BTXS4CEIL2LO1HS3TOPS3TOPS2Hj2HiS2Hj2HiS2Hj2HiS4CEIL2LO2N12R12Hq1H2N02R0S4CEIL2LO2N12R12Hq1H3LSJ2T02N02R03HL24LTRT3SPR3LTB4LTB21Y2Y0S4CEIL2LO2N12R12Hq1H3LSJ2N02R03HL25KBHLO4LTRT3SPR3LTB4LTB24LSJ31Y2Y02Y12Y22T0S3LSJ3HL24LTRT3LTB4LTB22HqS4CEIL2LO3LSJ2T03HL24LTRT3SPR3LTB4LTB22Hj2Hi1HS4CEIL2LO3LSJ2T03HL25KBHLO4LTRT3SPR3LTB4LTB24LSJ32Hj2Hi1HS3LSJ3HL24LTRT3LTB4LTB24LSJ32HqS4CEIL2LO2N02R05KBHLO2Hj2Hi1H".
pose proof (afree_unw_sp47 _ _ _ _ _ _ _ _ UNW ltac:(clear -TOP; lia)) as SP47.
pose proof AC as AC'. destruct AC' as (INI & RSS & IMAX & TI & TK & T88 & TSD & CT).
unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM, GOT_PGSZ, APGSZ, AFREE_SYM, AFREE_PC in *.
word_range sp SPR. word_range s0 S0R. word_range ra RAR.
box DHT. box DHC. box DHN. box DHS. box DTN. box DTS. box DCN. box DCS. box CT2.
pose proof TT0 as TTx. rw_split TTx 1%nat TTc TT. clear TTc.
eapply evtF_cut.
{ eapply (ficptA_spec (hm + 16) ia RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo);
try eassumption; try (unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1; lia).
all: try lazymatch goal with
| |- rw_cells _ _ AIA_FLAG _ => exact FL
| |- stk _ _ AIA_BASE _ => exact IAS
| |- _ = true -> _ => exact IAM
| |- rng _ _ _ => solve_rng
end.
all: match goal with |- ?G => idtac "REMA" G end. }
cbv beta. intros ms1 PA. unfold ficptA_post in PA.
destruct PA as (t0a & t1a & t2a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & junk1 & junk2 & -> & MUa & WMa & MIa & STa & FRA & FRt & FRs & FL1 & IAS1 & IAM1).
pose proof FRs as FRs0. rw_split FRs0 7%nat FRsx FRsr. clear FRsx.
destruct FRsr as [[_ BSR] _]. cbn [cells_bytes cbytes app] in BSR. rewrite app_nil_r in BSR.
apply bytes_at_app in BSR. destruct BSR as [BS0 BRA]. rewrite length_le8 in BRA.
replace (bv_unsigned sp + -16 + Z.of_nat 8) with (bv_unsigned sp - 8) in BRA by lia.
replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) in BS0 by lia.
assert (UC1 : forall tr, trt = bv_unsigned ra :: tr -> uchain m top 340732 (bv_unsigned sp) (bv_unsigned s0) 28%nat tr -> bv_unsigned sp + 16 < top ->
uchain m1 top 340732 bot (bv_unsigned sp) 29%nat ([bv_unsigned ra] ++ tr)).
{ intros tr _ UC BTX. replace ([bv_unsigned ra] ++ tr) with ((if bv_unsigned ra =? 340732 then [] else [bv_unsigned ra]) ++ tr)
by (replace (bv_unsigned ra =? 340732) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
eapply (uc_step m1 top 340732 bot (bv_unsigned sp) 29%nat (bv_unsigned s0) (bv_unsigned ra) tr); try lia.
- rewrite Z_to_bv_bv_unsigned. exact BS0.
- rewrite Z_to_bv_bv_unsigned. exact BRA.
- replace (bv_unsigned ra =? 340732) with false by (symmetry; apply Z.eqb_neq; lia). cbn [Nat.pred].
destruct (Z_le_gt_dec (bv_unsigned sp + 16) (bv_unsigned s0)) as [GE|LT].
+ eapply uchain_frame; [exact UC|]. intros a Ha. apply MUa. cbn [outside]. rewrite unsigned_lit by lia. lia.
+ inversion UC; subst; [apply uc_stop; assumption | exfalso | exfalso]; Z.div_mod_to_equations; lia. }
clear BS0 BRA.
xport TI MUa WMa ltac:(lia). xport TK MUa WMa ltac:(lia). xport T88 MUa WMa ltac:(lia). xport TSD MUa WMa ltac:(lia).
xport CT MUa WMa ltac:(lia). xport GPG MUa WMa ltac:(lia). xport PGC MUa WMa ltac:(lia). xport TT MUa WMa ltac:(lia).
xport TT0 MUa WMa ltac:(lia). xport CT8 MUa WMa ltac:(lia).
xport SW MUa WMa ltac:(lia). xport UW MUa WMa ltac:(lia). xport INI MUa WMa ltac:(lia).
xport HD MUa WMa ltac:(lia). xport HUW MUa WMa ltac:(lia). xport HK MUa WMa ltac:(lia). xport STATS MUa WMa ltac:(rewrite LSJ; lia).
assert (DEP1 : ADEPOT DI L m1).
{ eapply (adi_frame DI); [exact DEP | exact MUa | exact WMa |].
repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; lia|]). apply Forall_nil. }
clear DEP.
pose proof FRA as FRA0. rw_split FRA0 1%nat FRp FRz. rw_split FRz 1%nat SZC TAG.
change 2040%nat with (8 * 255)%nat in FRt. destruct (u64arr_of_CB _ _ 255%nat _ FRt) as [TB LTB].
pose proof FRs as FRs1. rw_split FRs1 1%nat BPJ REST.
replace (bv_unsigned sp + -2120) with (bv_unsigned sp + -2128 + 8) in SZC by lia.
replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) in TB by lia.
replace (bv_unsigned sp + -72) with (bv_unsigned sp + -2128 + 2056) in BPJ by lia.
step.
name_sp sp (-2128).
eapply evtF_cut with (P := unwind_impl_post (bv_unsigned sp + -2128) 340732 (bv_unsigned sp) t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc lo trt m1).
{ destruct UNW as [(tr & Etr & UC & LTR & BTX & RTOP)|(Etr & TOPLE & SPLT)]; rewrite Etr.
- eapply (unwind_impl_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp + -2128) 340732 (bv_unsigned sp) ctx t top bot lo (words_of_bytes junk1) ([bv_unsigned ra] ++ tr)).
all: try lazymatch goal with
| |- stk _ _ _ _ => rewrite Hsp; exact STa
| |- mem_inv _ _ => exact MIa
| |- @eq word _ _ => rewrite ?Esp; first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
| |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
| |- u64arr _ _ _ _ => exact TB
| |- uchain _ _ _ _ _ _ _ => exact (UC1 tr Etr UC BTX)
| |- _ \/ _ => unboxed CT2
| |- rng _ _ _ => solve_rng
| |- rw_cells _ _ (_ + 152) _ => exact CT
| |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
| |- rw_cells _ _ (_ + 40) _ => exact SW
| |- rw_cells _ _ (_ + 3168) _ => exact UW
end.
all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
all: match goal with |- ?G => idtac "REMU" G end.
- eapply (unwind_impl_spec0 RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (bv_unsigned sp + -2128) 340732 (bv_unsigned sp) ctx t top bot lo (words_of_bytes junk1)).
all: try lazymatch goal with
| |- stk _ _ _ _ => rewrite Hsp; exact STa
| |- mem_inv _ _ => exact MIa
| |- @eq word _ _ => rewrite ?Esp; first [reflexivity | exact TP | rewrite Z_to_bv_bv_unsigned; reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
| |- ex _ => first [eexists; exact SZC | eexists; exact BPJ]
| |- u64arr _ _ _ _ => exact TB
| |- _ \/ _ => unboxed CT2
| |- rng _ _ _ => solve_rng
| |- rw_cells _ _ (_ + 152) _ => exact CT
| |- rw_cells _ _ (_ + 8) [C8 _; C8 _] => exact TT
| |- rw_cells _ _ (_ + 40) _ => exact SW
| |- rw_cells _ _ (_ + 3168) _ => exact UW
end.
all: try eassumption. all: try (unfold AIMG_HI; lia). all: try (Z.div_mod_to_equations; lia).
all: match goal with |- ?G => idtac "REMU0" G end. }
cbv beta. intros ms2 PU. unfold unwind_impl_post in PU.
destruct PU as (t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2 & tb2
& -> & MUu & WMu & MIu & STu & SZ2 & TB2 & LTB2 & TRF2 & BP2 & UW2).
unname_sp. rewrite ?unsigned_lit in MUu by lia. rewrite ?unsigned_lit in STu by lia.
replace (ret_pc (Z_to_bv 64 340824)) with (Z_to_bv 64 340824) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
assert (MU12 : munch [(bv_unsigned sp - 2288, bv_unsigned sp - 2128); (bv_unsigned sp - 2120, bv_unsigned sp - 2116); (bv_unsigned sp - 2112, bv_unsigned sp - 64); (t + 3168, t + 3169)]%Z m1 m2).
{ eapply munch_weaken; [| exact MUu]. unfold sub_fp; cbn [outside]; intros q Hq; lia. }
xport TI MU12 WMu ltac:(lia). xport TK MU12 WMu ltac:(lia). xport T88 MU12 WMu ltac:(lia).
xport TSD MU12 WMu ltac:(lia). xport CT MU12 WMu ltac:(ub CT2; lia). xport CT8 MU12 WMu ltac:(ub CT2; lia). xport TT0 MU12 WMu ltac:(lia).
xport FRp MU12 WMu ltac:(lia). xport TAG MU12 WMu ltac:(lia). xport REST MU12 WMu ltac:(lia).
xport HD MU12 WMu ltac:(ub DHT; lia). xport HUW MU12 WMu ltac:(ub DHT; lia). xport HK MU12 WMu ltac:(lia).
xport STATS MU12 WMu ltac:(rewrite LSJ; lia).
xport FL1 MU12 WMu ltac:(lia). xport IAS1 MU12 WMu ltac:(lia).
assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at bsegs m2 (0xa3748 + 8 * j) (le8 (Z_to_bv 64 0))).
{ intros j Hj. eapply bytes_at_agree; [exact (IAM1 j Hj)|].
intros i Hi. apply MU12. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }
clear IAM1.
assert (DEP2 : ADEPOT DI L m2).
{ eapply (adi_frame DI); [exact DEP1 | exact MU12 | exact WMu |].
repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; ub DTN; ub DTS; lia|]). apply Forall_nil. }
clear DEP1.
rw_join SZ2 TAG SZT. rw_join FRp SZT SS.
replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) in SS by lia.
rewrite Z_to_bv_bv_unsigned in BP2. rw_join BP2 REST FRS.
replace (bv_unsigned sp + -2128 + 2056) with (bv_unsigned sp + -72) in FRS by lia.
zstep. zstep. step. step.
step.
name_sp sp (-2128).
eapply evtF_cut.
{ eapply (dealloc_spec t hm (bv_unsigned sp + -2128) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 n b1 actx ctx lo uw sj).
all: try lazymatch goal with
| |- stk _ _ _ _ => rewrite Hsp; exact STu
| |- mem_inv _ _ => exact MIu
| |- @eq word _ _ => rewrite ?Esp; first [reflexivity | exact TP | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
| |- u64arr _ _ _ _ => exact STATS
| |- _ \/ _ => first [unboxed DHT | unboxed DHC | unboxed CT2]
| |- rng _ _ _ => solve_rng
| |- rw_cells _ _ (_ + 152) _ => exact CT
| |- rw_cells _ _ (_ + 16) _ => exact HUW
| |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
| |- rw_cells _ _ AFHOOK _ => exact HK
end.
all: try eassumption. all: try (unfold AIMG_HI; lia).
all: match goal with |- ?G => idtac "REMD" G end. }
cbv beta. intros ms3 PD. unfold dealloc_post in PD.
destruct PD as (t0c & t1c & t2c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m3 & sj3
& -> & MUd & WMd & MId & STd & HD3 & FC3 & STATS3 & LSJ3).
unname_sp. rewrite ?unsigned_lit in MUd by lia. rewrite ?unsigned_lit in STd by lia.
xport TI MUd WMd ltac:(lia). xport TK MUd WMd ltac:(lia). xport T88 MUd WMd ltac:(lia). xport TSD MUd WMd ltac:(lia).
xport CT MUd WMd ltac:(ub DHC; ub CT2; lia). xport CT8 MUd WMd ltac:(ub DHC; ub CT2; lia). xport TT0 MUd WMd ltac:(ub DHT; lia).
xport SS MUd WMd ltac:(lia). xport TB2 MUd WMd ltac:(rewrite LTB2; lia). xport FRS MUd WMd ltac:(lia).
xport UW2 MUd WMd ltac:(ub DHT; lia). xport FL1 MUd WMd ltac:(lia). xport IAS1 MUd WMd ltac:(lia).
assert (IAM3 : forall j, 0 <= j < 32768 -> bytes_at bsegs m3 (0xa3748 + 8 * j) (le8 (Z_to_bv 64 0))).
{ intros j Hj. eapply bytes_at_agree; [exact (IAM2 j Hj)|].
intros i Hi. apply MUd. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }
clear IAM2.
assert (DEP3 : ADEPOT DI L m3).
{ eapply (adi_frame DI); [exact DEP2 | exact MUd | exact WMd |].
repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; ub DTN; ub DTS; ub DHN; ub DHS; lia|]). apply Forall_nil. }
clear DEP2.
name_sp sp (-2128).
eapply evtF_cut.
{ eapply (qchunk_spec DI L t hm (bv_unsigned sp + -2128) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 n ctx b1 actx lo
(1 + Z.of_nat (length trt)) 340732 (Z_to_bv 64 18446744069414584320) (Z_to_bv 64 top) (Z_to_bv 64 bot) tb2 trt).
all: try lazymatch goal with
| |- stk _ _ _ _ => rewrite Hsp; exact STd
| |- mem_inv _ _ => exact MId
| |- ADEPOT _ _ _ => exact DEP3
| |- @eq word _ _ => rewrite ?Esp; first [reflexivity | exact TP | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
| |- u64arr _ _ _ _ => exact TB2
| |- In _ _ => exact TRU
| |- map _ _ = _ => exact TRF2
| |- _ \/ _ => first [unboxed DHN | unboxed DHS | unboxed DHT | unboxed DHC | unboxed DTN | unboxed DTS | unboxed DCN | unboxed DCS | unboxed CT2]
| |- rng _ _ _ => solve_rng
| |- rw_cells _ _ (_ + 152) _ => exact CT
| |- rw_cells _ _ (_ + 8) _ => exact CT8
| |- rw_cells _ _ (_ + 16) _ => exact FC3
| |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD3
| |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact TT0
| |- rw_cells _ _ (_ + -2128) _ => exact SS
end.
all: try eassumption. all: try (unfold AIMG_HI; cbn [length]; lia).
all: match goal with |- ?G => idtac "REMQ" G end. }
cbv beta. intros ms4 PQ. unfold qchunk_post in PQ.
destruct PQ as (id & t0d & t1d & t2d & a6d & a7d & t3d & t4d & t5d & t6d & m4
& -> & MUq & WMq & MIq & STq & FC4 & IDR & DEP4).
unname_sp. rewrite ?unsigned_lit in MUq by lia. rewrite ?unsigned_lit in STq by lia.
xport HD3 MUq WMq ltac:(ub DHN; ub DHS; lia). xport STATS3 MUq WMq ltac:(rewrite LSJ3; ub DHT; ub DTN; ub DTS; lia).
xport UW2 MUq WMq ltac:(ub DHT; ub DTN; ub DTS; lia). xport FL1 MUq WMq ltac:(lia). xport IAS1 MUq WMq ltac:(lia).
xport SS MUq WMq ltac:(lia). xport TB2 MUq WMq ltac:(rewrite LTB2; lia). xport FRS MUq WMq ltac:(lia).
assert (IAM4 : forall j, 0 <= j < 32768 -> bytes_at bsegs m4 (0xa3748 + 8 * j) (le8 (Z_to_bv 64 0))).
{ intros j Hj. eapply bytes_at_agree; [exact (IAM3 j Hj)|].
intros i Hi. apply MUq. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia. }
clear IAM3.
assert (MU : munch (front_W L sp t hm) m m4).
{ eapply munch_trans; [| eapply munch_weaken; [| exact MUq]].
eapply munch_trans; [| eapply munch_weaken; [| exact MUd]].
eapply munch_trans; [| eapply munch_weaken; [| exact MUu]].
eapply munch_weaken; [| exact MUa].
all: unfold sub_fp; cbn [outside]; intros q Hq; lia. }
assert (WM : wmono bsegs m m4).
{ eapply wmono_trans; [exact WMa|]. eapply wmono_trans; [exact WMu|]. eapply wmono_trans; [exact WMd| exact WMq]. }
apply evtF_done. unfold free_front_post.
exists id. do 9 eexists. exists m4, sj3, tb2, junk2.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MIq|]. split; [exact STq|]. split; [exact IDR|].
split; [exact HD3|]. split; [exact FC4|]. split; [exact STATS3|]. split; [exact LSJ3|]. split; [exact UW2|].
split; [exact FL1|]. split; [exact IAS1|]. split; [exact IAM4|].
split; [exact SS|]. split; [exact TB2|]. split; [exact LTB2|].
split; [exact FRS|]. exact DEP4.
Unshelve. all: try exact STa; try exact STu; try exact STd.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End WithDepot.
End CANSEC1.
