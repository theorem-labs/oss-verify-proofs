(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode Arr InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg AProto ABase ABytes AQConst ADepot_iface.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AKit AKit2 AKitQ F_apoison F_aalloc_s F_aalloc1 F_afree_iseg F_afree_front F_afree_tail
F_aenqueueR F_afree_tailR F_afree_icpt.
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
Local Ltac qlia := first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
| LiaTuning.zify_prune; Zify.zify; xlia zchecker ].
Local Ltac leaf2 := first [ left; qlia | right; qlia | qlia ].
Local Ltac band_leaf :=
first [ leaf2
| match goal with B : sclr ?a _ |- context [?a] =>
let B' := fresh "BB" in pose proof B as B'; unfold sclr, KLS in B'; destruct B' as [B'|B']; leaf2 end
| match goal with B : iclr ?a _ |- context [?a] =>
let B' := fresh "BB" in pose proof B as B'; unfold iclr, AIMG_LO, AIMG_HI in B'; destruct B' as [_ [B'|B']]; leaf2 end
| match goal with B : ablk ?a _ |- context [?a] =>
let B' := fresh "BB" in pose proof B as B'; unfold ablk, KLS, AIMG_HI in B'; destruct B' as [[? B']|[B' ?]]; leaf2 end
| lia ].
Local Ltac band_disj := cbn [disjoint_from fst snd]; repeat match goal with |- _ /\ _ => split end; first [exact I | band_leaf].
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. Local Ltac2 Set LiaHints.tbl := fun () => "0020=25807200586.548752807258.500000600<S1H2G1S1H2G2".
destruct H; [exists 0 | exists 1]; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
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
Notation free_W L sp t hm n lst ek g :=
([(bv_unsigned sp - 4096, bv_unsigned sp); (0xa3680, 0xa3680 + 0x81030); (0x131f08, 0x131f08 + 4);
(t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
(ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
(shad (hm + 16), shad (hm + 16) + shlen (rup n 8)); (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
(lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
(0x9f188, 0x9f188 + 4); (0x9f190, 0x9f190 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z) (only parsing).
Notation toref_W L sp t hm n :=
([(bv_unsigned sp - 4096, bv_unsigned sp); (0xa3680, 0xa3680 + 0x81030); (0x131f08, 0x131f08 + 4);
(t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
(ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
(shad (hm + 16), shad (hm + 16) + shlen (rup n 8))]%Z) (only parsing).
Definition free_to_refill_post (L : alayout) (full : bool)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(t hm n b1 actx lo lst nx bsz : Z) (hs : list word) (trt : list Z) (m : amem) : machine_state -> Prop :=
fun ms' => exists (id : Z) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m' (sj' tb' : list word) (junk2 j0 : list byte),
ms' = MS (mkR (Z_to_bv 64 0x368a0) (Z_to_bv 64 (bv_unsigned sp + -2272)) gp tp t0 t1 t2
(Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
(Z_to_bv 64 (t + 208)) (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 0x9ee18) (Z_to_bv 64 K_BATCH_CLASS) a4 a5 a6 a7
(Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE)
s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x37080) fc None m' (seg_rom asegs)
/\ munch (toref_W L sp t hm n) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp + -2272)
/\ 0 < id < 2^31
/\ rw_cells asegs m' hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)]
/\ rw_cells asegs m' (hm + 16) [C8 (Z_to_bv 64 id)]
/\ rw_cells asegs m' (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))]
/\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
/\ rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)]
/\ rw_cells asegs m' 0x131f08 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
/\ stk asegs m' 0xa3680 (0xa3680 + 0x81030)
/\ (forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xa3688 + 8 * j) (le8 (Z_to_bv 64 0)))
/\ rw_cells asegs m' (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)]
/\ u64arr asegs m' (bv_unsigned sp + -2128 + 16) tb' /\ length tb' = 255%nat
/\ rw_cells asegs m' (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ rw_cells asegs m' (bv_unsigned sp + -2208)
[C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 s6; C8 (Z_to_bv 64 (bv_unsigned sp + -81));
C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0x53410); C8 (Z_to_bv 64 (hm + 16)); C8 sp; C8 (Z_to_bv 64 0x53480)]
/\ rw_cells asegs m' (bv_unsigned sp + -2272)
[CB 8 j0; C8 (Z_to_bv 64 hm); C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 n);
C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0x9f0f0); C8 (Z_to_bv 64 0x36740)]
/\ (if full then rw_cells asegs m' lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)] /\ u64arr asegs m' (lst + 24) hs else True)
/\ ADEPOT DI L m'.
#[using="Type"] Lemma free_to_refill_spec : forall (L : alayout) (ia full : bool) RNG
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem)
(t ctx hm n b1 actx lo top bot nb fst0 lst qb nx bsz : Z) (uw maxc csz : word) (sj hs : list word) (sjunk : list byte) (trt : list Z),
stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
mem_inv asegs m ->
tp = Z_to_bv 64 ATP ->
a0 = Z_to_bv 64 (hm + 16) ->
bv_unsigned sp mod 16 = 0 ->
allocA_cells m ctx t -> poison_cells m ->
rw_cells asegs m 0xa317c [C4 (Z_to_bv 64 30)] ->
rw_cells asegs m 0x133fca [C1 (Z_to_bv 8 1)] ->
rw_cells asegs m 0x99760 [C8 (Z_to_bv 64 0x131f20)] -> rw_cells asegs m 0x131f20 [C8 (Z_to_bv 64 4096)] ->
rw_cells asegs m 0x133f48 [C8 (Z_to_bv 64 0)] ->
rw_cells asegs m 0x9f130 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
rw_cells asegs m 0x99778 [C8 (Z_to_bv 64 AFLAGS)] ->
rw_cells asegs m 0x9fca4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
rw_cells asegs m 0x131f08 [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
stk asegs m 0xa3680 (0xa3680 + 0x81030) ->
(ia = true -> forall j, 0 <= j < 32768 -> bytes_at asegs m (0xa3688 + 8 * j) (le8 (Z_to_bv 64 0))) ->
rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
rw_cells asegs m t [C8 (Z_to_bv 64 ctx); C8 (Z_to_bv 64 top); C8 (Z_to_bv 64 bot)] ->
rw_cells asegs m (t + 40) [C1 (Z_to_bv 8 0)] -> rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
0 < ctx -> sclr ctx 65536 -> ctx + 4096 <= ATOP ->
sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
rw_cells asegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 1 <= n <= Q_MAX -> hm mod 16 = 0 ->
ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) sjunk] ->
(hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) ->
(if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
/\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
/\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat /\ rng RNG lst 8192
else nb = 0 /\ lst = 0) ->
rw_cells asegs m (t + 2128) [C4 (Z_to_bv 64 0); C4 maxc; C8 csz] ->
(t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (hm + 24 <= lst \/ lst + 8192 <= hm) ->
(al_nodes L + 1048576 <= lst \/ lst + 8192 <= al_nodes L) -> (al_store L + 8388608 <= lst \/ lst + 8192 <= al_store L) ->
ADEPOT DI L m ->
sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
(hm + 24 <= al_nodes L \/ al_nodes L + 1048576 <= hm) -> (hm + 24 <= al_store L \/ al_store L + 8388608 <= hm) ->
(t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
(ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) ->
afree_unw RNG lo m top sp s0 ra trt ->
bv_unsigned s0 <> bv_unsigned sp + 8 ->
In (AFREE_PC :: trt) (al_U L) ->
0 <= bot -> bot < bv_unsigned sp -> bot < top -> 4096 <= top <= 2^47 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
AIMG_HI <= ctx -> AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->
evtF asegs RNG (free_to_refill_post L full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n b1 actx lo lst nx bsz hs trt m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Proof.
intros until trt.
intros ST CEIL LO MI TP Ha0 SP16 AC PC MCS CF34 GPG PGC HK QK GF FLG FL IAS IAM CT8 TT0 SW UW STATS LSJ QC NB QB QBN FST LST
CX0 C0 C1 T0 T1 TAL CT2 HD HUW B1 B13 N AL HLO HHI HCE SH DHT DHC FULL CR0 DTL DHL DNL DSL DEP N0 N1 R0 R1 DHN DHS DTN DTS DCN DCS
UNW S0NE TRU B0 BB BOTOP TOP RA4 RANE RIMG RSTK RCTX RT RNO RST RH RSH CI NI SI TI. band_lin.
Local Ltac2 Set LiaHints.tbl := fun () => "01M0?10645443711.23111060090622.2  1255475127.3   13046525288.30 13171924154.4  13441573651.2  13720796066.2421390114094.221 14706613971.22115242187732.3  19169306520.22119177178279.22119915692355.3  20000433825.2  21801979053.22522054635580.2  23309850646.2  24126170433.2  24860604070.22125065190167.24225293933061.1  26326327891.22127011549143.2  27579900502.2  27773123129.3  29782367974.9  30381635537.24233896070369.2  35123122104.2  35670038479.2  35694103779.2  36646331050.18936878576353.2  36891763600.2  37074209399.3  37303860646.22137378317842.16 37838061989.2253806676972.4   39340564468.2  40864623135.17640864623135.18041480320778.17141488967566.1  41593613785.1  42598764294.3  43358680699.15243358680699.17243413626285.22543945325701.22344433698769.24247098605663.22147113197791.22147253246550.3  47271575018.3  4751365310.1   48202942602.2244828235070.2   48408455303.2  48918274667.3  49163223467.3  49425192486.16749921929014.22450090862160.2  50462328133.1  50948243273.2  51789411931.3  52569147371.22452569147371.23153028877591.16853091131576.1  54969794426.17554969794426.17955159062625.2  5538953482.3   56170256219.22356957627706.2  57063652016.2  57622410744.2465807335231.242 58916756809.2246120909188.3   61957014541.4  65006792167.2216562149469.2   66260016006.2466685735426.3   67469470029.24467604605006.1  68172974227.2217549760641.2   9074498759.221 944710335.242  00001<01=01>01_01`01a02D02I02h02i03403503603703Q03R03S03T03_04Q04R05105205305405505605705805905:05=05>05?05@05K05W06506606706=06C06I06J06K06L06R06X07207307407507607707807907A07B07C07D07E07J07Z07[07\07]07^08e0:70:=0:>0:B0:F0:G0:H0:M0:N0:O0:d0;30;80;90;:0;?0;D0;K0;L0<80<90<X0<Y0<`0<oS4CEIL2LO3LSJ2T13HCE2L02L14LEN02N12R12TI3HL24LTRT3SPR4LSJ14LTB11Y2Y02Y12Y21HFFS1N3HHI3HL11H2H02H42H52H93H103H14FFS4CEIL2LO1N3HCE5KEHLO5KCHLO3RUP3SHBS3HL1S4CEIL2LO2NI2SI4KCTI4KDTI3HL11HFS4CEIL2LO1HSFFS3LSJ3HL24LTRT4LSJ14LTB11YFFFS4KCTI4KDTIS4CEIL2LO1N3HCE5KEHLO5KCHLO3RUP3SHB2T14KBT04KCT01HFS4CEIL2LO2NI2SI4KCTI4KDTI3HL11HFFFSSFFFFS1NFFFS4KCTI4KDTIS1H2H02H42H5S3LSJ3LST3HL24LTRT4LSJ14LTB11YFFS2N11HS2R11HS4KBTIFFFS2T11HS2T11HS3LSJ3HL24LTRT4LSJ14LTB11YSSSSFFSS2LO3HspFFFFS3CX0S4CEIL2LO4SP471HFFFFS4CEIL2LO4SP163LSJ2T13TAL3HCE2N12R12TI3HL24LTRT3SPR4LSJ14LTB11Y2Y02Y11HS4CEIL2LO3LSJ2T11N3HCE2L02L14LEN02N12R12TI3HL24LTRT3RUP3SPR4LSJ14LTB11Y2Y02Y12Y21HS2C11HFS2NIS2SIFFS3HspFFS4CEIL2LO3SHB2Hj2Hi1HS4CEIL2LO3SHB1HS3HCEFFS3HL1S3TOPS2Hj2HiFS4CEIL2LO2N12R12Hq1H4KBN04KCN04KBR04KCR03SHBFS4CEIL2LO2NI2SI4KCTI4KDTI3HL11HFS2NI2SIS4CEIL2LO3SHB1H".
band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_int C0. band_int T0. band_int N0. band_int R0.
pose proof (afree_unw_length _ _ _ _ _ _ _ _ UNW) as LTRT.
pose proof (afree_unw_sp47 _ _ _ _ _ _ _ _ UNW ltac:(clear -TOP; lia)) as SP47.
pose proof PC as PC'. destruct PC' as (GOT6 & _).
assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear -N; unfold rup; Z.div_mod_to_equations; lia).
assert (SHB : 2148232704 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000 /\ 0 < shlen (rup n 8)).
{ clear -N HLO HL1 HHI HCE. unfold shad, shlen, ASHOFF, rup in *. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in *. Z.div_mod_to_equations. lia. }
unfold AIMG_HI, AFREE_SYM, AFREE_PC in *.
word_range sp SPR.
box DHT. box DHC. box DHN. box DHS. box DTN. box DTS. box DCN. box DCS. box CT2. box DTL. box DHL. box DNL. box DSL.
eapply evtF_cut.
{ eapply (free_front_spec DI L ia RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
t ctx hm n b1 actx lo top bot uw sj trt).
all: try lazymatch goal with
| |- stk _ _ _ _ => first [exact ST | exact IAS]
| |- mem_inv _ _ => exact MI
| |- allocA_cells _ _ _ => exact AC
| |- ADEPOT _ _ _ => exact DEP
| |- afree_unw _ _ _ _ _ _ => exact UNW
| |- In _ _ => exact TRU
| |- u64arr _ _ _ _ => exact STATS
| |- _ = true -> _ => exact IAM
| |- _ \/ _ => first [unboxed DHT | unboxed DHC | unboxed DHN | unboxed DHS | unboxed DTN | unboxed DTS | unboxed DCN | unboxed DCS | unboxed CT2]
| |- rng _ _ _ => solve_rng
| |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
| |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact TT0
| |- rw_cells _ _ (_ + 16) _ => exact HUW
| |- rw_cells _ _ (_ + 8) _ => exact CT8
| |- rw_cells _ _ (_ + 40) _ => exact SW
| |- rw_cells _ _ (_ + 3168) _ => exact UW
end.
all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
all: match goal with |- ?G => idtac "REMF" G end. }
cbv beta. intros ms1 PFR. unfold free_front_post in PFR.
destruct PFR as (id & t0a & t1a & t2a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & sj1 & tb1 & junk2
& -> & MUf & WMf & MIf & STf & IDR & HD1 & FC1 & STATS1 & LSJ1 & UW1 & FL1 & IAS1 & IAM1 & SS1 & TB1 & LTB1 & FRS1 & DEP1).
xport QK MUf WMf ltac:(lia). xport GF MUf WMf ltac:(lia). xport FLG MUf WMf ltac:(lia).
xport QC MUf WMf ltac:(ub DHT; ub DTN; ub DTS; lia).
xport SH MUf WMf ltac:(band_disj).
xport CR0 MUf WMf ltac:(ub DHT; ub DTN; ub DTS; lia).
assert (PC1 : poison_cells m1).
{ eapply poison_cells_frame2; [exact PC | exact MUf | exact WMf |].
repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
assert (FULL1 : if full then 0 < nb /\ rw_cells asegs m1 lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
/\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
/\ u64arr asegs m1 (lst + 24) hs /\ length hs = 1021%nat /\ rng RNG lst 8192
else nb = 0 /\ lst = 0).
{ destruct full; [| exact FULL]. destruct FULL as (NB1 & LB & L0 & L1 & LA0 & LEN0 & RL).
xport LB MUf WMf ltac:(ub DTL; ub DHL; ub DNL; ub DSL; lia). xport LA0 MUf WMf ltac:(rewrite LEN0; ub DTL; ub DHL; ub DNL; ub DSL; lia).
split; [exact NB1|]. split; [exact LB|]. split; [exact L0|]. split; [exact L1|]. split; [exact LA0|]. split; [exact LEN0| exact RL]. }
clear FULL PC.
name_sp sp (-2128).
eapply evtF_cut.
{ eapply (put_to_refill_spec full t hm lst RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 n nb fst0 qb b1 actx lo nx bsz maxc csz hs sjunk).
all: try lazymatch goal with
| |- stk _ _ _ _ => rewrite Hsp; exact STf
| |- mem_inv _ _ => exact MIf
| |- poison_cells _ => exact PC1
| |- @eq word _ _ => rewrite ?Esp; first [reflexivity | apply Z_to_bv_eqm; rewrite ?unsigned_lit by lia; lia]
| |- if _ then _ else _ => exact FULL1
| |- _ \/ _ => first [ub DHT; lia | ub DTL; lia | ub DHL; lia]
| |- rng _ _ _ => solve_rng
| |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
| |- rw_cells _ _ (shad _) _ => exact SH
| |- rw_cells _ _ (_ + 80) _ => exact QC
| |- rw_cells _ _ (_ + 2128) _ => exact CR0
| |- iclr _ _ => exact TI
end.
all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
all: match goal with |- ?G => idtac "REMP" G end. }
cbv beta. intros ms2 PP. unfold put_to_refill_post in PP.
destruct PP as (t0b & t1b & t2b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2 & j0
& -> & MUp & WMp & MIp & STp & SH2 & FRP & FRE & LBS).
unname_sp. rewrite ?unsigned_lit in MUp by lia. rewrite ?unsigned_lit in STp by lia.
rewrite ?unsigned_lit in FRP by lia. rewrite ?unsigned_lit in FRE by lia.
replace (bv_unsigned sp + -2128 + -80) with (bv_unsigned sp + -2208) in * by lia.
replace (bv_unsigned sp + -2128 + -144) with (bv_unsigned sp + -2272) in * by lia.
xport HD1 MUp WMp ltac:(lia). xport FC1 MUp WMp ltac:(lia).
xport STATS1 MUp WMp ltac:(rewrite LSJ1; lia).
xport UW1 MUp WMp ltac:(lia).
xport FL1 MUp WMp ltac:(lia). xport IAS1 MUp WMp ltac:(lia).
xport SS1 MUp WMp ltac:(lia). xport TB1 MUp WMp ltac:(rewrite LTB1; lia). xport FRS1 MUp WMp ltac:(lia).
assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m2 (0xa3688 + 8 * j) (le8 (Z_to_bv 64 0))).
{ (intros j Hj; eapply bytes_at_agree; [exact (IAM1 j Hj)|];
intros i Hi; apply MUp; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; lia). }
clear IAM1.
assert (DEP2 : ADEPOT DI L m2).
{ eapply (adi_frame DI); [exact DEP1 | exact MUp | exact WMp |].
(repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; first [lia | ub DTN; ub DTS; lia] |]); apply Forall_nil). }
clear DEP1.
assert (MU : munch (toref_W L sp t hm n) m m2).
{ eapply munch_trans; [| eapply munch_weaken; [| exact MUp]].
eapply munch_weaken; [| exact MUf].
all: solve_sub_fp sp. }
assert (WM : wmono asegs m m2) by (eapply wmono_trans; [exact WMf| exact WMp]).
apply evtF_done. unfold free_to_refill_post. exists id. do 11 eexists. exists m2, sj1, tb1, junk2, j0.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MIp|]. split; [exact STp|]. split; [exact IDR|].
split; [exact HD1|]. split; [exact FC1|]. split; [exact SH2|].
split; [exact STATS1|]. split; [exact LSJ1|]. split; [exact UW1|]. split; [exact FL1|]. split; [exact IAS1|]. split; [exact IAM2|].
split; [exact SS1|]. split; [exact TB1|]. split; [exact LTB1|]. split; [exact FRS1|]. split; [exact FRP|]. split; [exact FRE|].
split; [exact LBS|]. exact DEP2.
Unshelve. all: try exact STf; try exact STp.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma free_from_refill_spec : forall (L : alayout) (full : bool) (g : gqd) RNG
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(F : bvmap 5 word) fc (m : amem)
(t hm n b1 actx lo nb fst0 lst qb nx bsz cnt spacebeg id b : Z) (maxc csz stj idxw : word) (sj tb chunks hs : list word)
(junk2 j0 : list byte) (trt : list Z),
let ek := EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs in
stk asegs m lo (bv_unsigned sp + -2272) -> ATOP <= lo -> lo <= bv_unsigned sp - 4096 ->
mem_inv asegs m ->
rw_cells asegs m (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
u64arr asegs m (bv_unsigned sp + -2128 + 16) tb -> length tb = 255%nat ->
rw_cells asegs m (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs m (bv_unsigned sp + -2208)
[C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 s6; C8 (Z_to_bv 64 (bv_unsigned sp + -81));
C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0x53410); C8 (Z_to_bv 64 (hm + 16)); C8 sp; C8 (Z_to_bv 64 0x53480)] ->
rw_cells asegs m (bv_unsigned sp + -2272)
[CB 8 j0; C8 (Z_to_bv 64 hm); C8 (Z_to_bv 64 (t + 208)); C8 (Z_to_bv 64 (bv_unsigned sp + -2128)); C8 (Z_to_bv 64 n);
C8 (Z_to_bv 64 (t + 80)); C8 (Z_to_bv 64 0x9f0f0); C8 (Z_to_bv 64 0x36740)] ->
rw_cells asegs m 0x9f130 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
rw_cells asegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
rw_cells asegs m (hm + 16) [C8 (Z_to_bv 64 id)] -> 0 < id < 2^31 ->
1 <= n <= Q_MAX -> hm mod 16 = 0 -> ablk hm (hm + 16 + rup n 8) -> hm + 16 + rup n 8 <= ATOP -> hm + 24 <= ATOP ->
rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (repeat (Z_to_bv 8 253) (Z.to_nat (shlen (rup n 8))))] ->
rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
0 <= nb < 2^62 -> 0 <= qb -> qb + n + 8192 < 2^62 -> 0 <= fst0 < 2^64 -> 0 <= lst < 2^64 ->
sclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> (hm + 24 <= t \/ t + 4096 <= hm) ->
u64arr asegs m (t + 2800) sj -> length sj = 46%nat -> rw_cells asegs m (t + 3168) [C1 (Z_to_bv 8 0)] ->
rw_cells asegs m 0x131f08 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
stk asegs m 0xa3680 (0xa3680 + 0x81030) ->
(forall j, 0 <= j < 32768 -> bytes_at asegs m (0xa3688 + 8 * j) (le8 (Z_to_bv 64 0))) ->
(if full then 0 < nb /\ rw_cells asegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
/\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP
/\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat
/\ rng RNG lst 8192
else nb = 0 /\ lst = 0) ->
rw_cells asegs m 0x9ee38 [C8 (Z_to_bv 64 spacebeg)] ->
rw_cells asegs m (t + 2128) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
u32arr asegs m (t + 2128 + 16) chunks -> length chunks = 16%nat ->
0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
rw_cells asegs m (t + 2784) [C8 stj] ->
b = spacebeg + 24 * 2^32 + 16 * bv_unsigned idxw ->
(exists bs, rw_cells asegs m b [CB (Z.to_nat 8192) bs]) ->
0 < spacebeg -> 0x10007fff8000 <= b -> b + 8192 <= ATOP ->
(t + 4096 <= b \/ b + 8192 <= t) -> (t + 4096 <= lst \/ lst + 8192 <= t \/ lst = 0) -> (b + 8192 <= lst \/ lst + 8192 <= b) ->
(hm + 24 <= b \/ b + 8192 <= hm) -> (hm + 24 <= lst \/ lst + 8192 <= hm) ->
rng RNG b 8192 ->
ek_seps ek L hm lst ->
dk_pre ek g RNG t lst hm (qb + ek_delta ek n) m -> dk_seps g L hm ->
ADEPOT DI L m ->
sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
(t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
bv_unsigned sp < 2^47 ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> rng RNG hm 24 -> rng RNG (shad (hm + 16)) (shlen (rup n 8)) ->
AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L -> iclr t 4096 ->
evtF asegs RNG (free_fast_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n nb fst0 lst qb b1 actx lo m)
(MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -2272)) gp tp t0 t1 t2 (Z_to_bv 64 (t + 2128)) (Z_to_bv 64 (t + 208))
(Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 n) (Z_to_bv 64 Q_CACHE)
s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x368a0) fc None m (seg_rom asegs)).
Proof.
intros until trt. cbv zeta.
intros ST CEIL LO MI SS TB LTB FRS FRP FRE QK HD FC IDR N AL HLO HHI HCE SH QC NB QB QBN FST LST T0 T1 TAL DHT STATS LSJ UW FL IAS IAM
FULL SB CR CH LCH CNT NTH IXS STS HBE BJ SBP B0 BL1 DTB DTL DBL DHB DHL RB ES DK DS DEP N0 N1 R0 R1 DTN DTS SP47
RIMG RSTK RT RH RSH NI SI TI. band_lin.
Local Ltac2 Set LiaHints.tbl := fun () => "02[0?10026075202.3  10407789017.19310565049817.1  11207336246.2  11534118595.2  11622444022.2  11632340914.3  11644051538.3  11647585701.3  11711269523.3  1255475127.3   126030821.3    12920915338.17112924979120.2  13046525288.30 13171924154.4  14053207280.2  14851276904.19215043033658.16915272476639.4  15658595530.2  15692873387.19215809938180.4  15972425402.3  16247440464.3  1660769515.4   16948956174.1711727484261.193 17986879152.21618408691376.2  18526284000.2  18784504933.3  18954152602.17219870094916.4  20494573215.2  21472501613.4  21801979053.19322215373883.2  22464085422.2  2257333806.2   23369301651.3  23859455507.3  24051917616.2  24089546548.4  24215609177.1  24380870084.4  24926455156.16925911274470.4  28318239534.2  28449663237.1  28849653061.1  28950556505.1  29082502020.4  29782367974.9  3034442478.2   32787630625.3  32879528455.2  33541229294.2  35101742124.1  3555280912.3   35735543767.2  36042427018.3  36914764179.3  37074209399.3  37094085257.19337245297491.21937378317842.16 37592147547.21637812975851.2  37838061989.1933806676972.4   3961376427.2   40055865143.2  40597752022.3  40657273671.2  40733060795.2  40864623135.16340864623135.16741290547714.3  41480320778.15841891655969.3  43184287682.3  43358680699.14343358680699.15943413626285.19343730231044.4  43945325701.19144747532908.1  45094126240.2  45208558218.21745833759639.2  45987499258.3  46362715440.2  4698444865.172 46990720185.2  47055514183.2  47253150440.2  47271575018.3  47339931304.2  47415749499.2  4751365310.1   47621016616.2  48111092867.2  4857928327.2   49163223467.3  49414143204.3  49453834573.4  49928213262.19049928213262.21650277201561.1  50833179883.2  51085951050.21651789411931.3  52153578606.2  52569147371.21752569147371.22052569147371.22152709879913.3  5307885885.3   53268388889.1  53490602323.3  53618232787.21953828428115.3  54266276843.5  54270651197.3  54271727728.2  54720370244.4  54969794426.16254969794426.16655598955172.3  5604732209.169 56170256219.19156458374290.3  57077293120.3  5720899184.2   57550243242.2  58572900859.2  58589404061.4  58838074567.2  58916756809.19258924715895.2  59145736912.3  61577305210.3  61711920891.2  61767725267.3  61957014541.4  62404581666.2  62451272951.2  62700287515.19264179488666.4  64348013483.2  64931727967.2  65102030884.3  65525877443.2  66260016006.221668166890.169  668166890.182  6685735426.3   67445600229.19267469470029.21867469470029.21967469470029.22067469470029.22167469470029.2226836352405.3   7354943850.2   8568483284.3   8663608162.4   8800126135.223 8827389611.192 9559012651.2   00000100D00E00F00G00H00I00J00K00L00M00N00W00\01=01>01?01G01L01M01N01W01X01Y01Z01[01c02602@02A02B02C02K02L02M02N02a02b02c02d02e02f02g02h02i02j02o03603703803903:03;03<03=03>03?03@03A03B03C03D03E03F03Y04O04[04`04a05805905:05;05<05=05>05H05R05S05]05^05_05i06306F06G06L06M06N06S06T06U06V06_06`06a06b06c06d06e06f06g06h06i06j06k06l07@07T07U07V07^07_07`08N0:30;e0;f0;g0;h0;i0<_0<`0<a0<b0<c0<d0<l0=40=50=@0=I0=J0=K0=L0=M0=N0=O0=P0=Y0=Z0=[0=\0=]0=^0=_0=`0=a0=m0=n0=o0>00>10>20>=0>D0>K0>L0>U0?00?j0@]0AH0B30B40B50B60B70C30C<0C=FS3LTB3LSJ3LCH3HL21YFFFFFFFFFFS3LST3LCHS3PL2S1N3HHI3HL11H2H02H42H52H93H103H14FFS2AL3LCHS3LCHFFS3LCH3HspFFFFS2L03LCHS3LTB3LSJ3LCH3HL21YS4CEIL3LCHFFFS2L13LCHFFFS3LTB3LSJ3LCH3HL21YFFFFFFFFFS3LCHS3PLB1HFFFFFSFFFFFFFFFFS3LTB3LSJ3LCH3HL21YS4CEIL2LO3LTB3LSJ3LCH2B02TI3HL23SHB3QZ13QZ23Hsp1Y2Y01HS1H2H02H42H5S3LCHFS3LTB3LST3LSJ3LCH3HL21YFFFFFFS3LCH2N11HS3LCH2R11HFS3LCH4KBTIFFS2T13LCH1HS2T13LCH1HS3LTB3LSJ3LCH3HL21YFS3LCHFFS3LCHFFFS3LCH3HL1FFFFFFSFFFFFFS4CEIL2LO3LCH4SP471HS4CEIL2LO3LCH4SP471HFFS2LO3LCHFFS4CEIL2LO2T13LCH3BL13SHB3DG13PLB3QZ03QZ13Hsp1HS4CEIL2LO3LTB1N2T13TAL3LSJ3LCH2B03BL12TI4KBTI3HL24KBT04KCT03RUP3SHB3DG13PLB3QZ03QZ13QZ23Hsp1Y2Y02Y11HS4CEIL2LO3LTB1N2AL3HCE2T13TAL3LSJ3LCH2B03BL12TI3HL13HL25KBHLO5KEHLO5KCHLO3RUP3SHB3DG13PLB3QZ03QZ13Hsp1Y2Y02Y12Y21HFFFFS4CEIL2LO3LTB3LSJ3LCH2B02TI3HL23SHB3QZ13QZ23Hsp1Y2Y01HFFFFFS3LCH2NIS3LCH2SIFS3LCH2NI2SIS3LCH3HspFFFFFFFS3HCE3LCHFFFFFFFFS2LO3LCH3HspFFFFFS3LCH2Hj2HiS3LCH1HS3LCH1HFS3TAL3LCHS4LST03LCH2NI2SI3QZ13QZ22HqS4CEIL2LO3LCH2N12R13Hsp2Hq1H4KBN04KCN04KBR04KCR03SHB2NI2SIS3LTB1N3LSJ4FULL3LCH2SL2TI3HL23RUP3QZ03QZ12Hq2S62S7S3LTB3LSJ3LCH2NI2SI2TI3HL22Hq1Y2Y01N2B03RUPS3LTB1N3LSJ3LCH2NI2SI2TI3HL23RUP2Hq1Y2Y02Y1FFFFS4CEIL2LO3LTB3LSJ3LCH2B02TI3HL23SHB3QZ13QZ23Hsp2Hj2Hi1Y2Y01HS3LCH3HspF".
band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_int T0. band_int N0. band_int R0.
assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear -N; unfold rup; Z.div_mod_to_equations; lia).
assert (SHB : 2148232704 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000 /\ 0 < shlen (rup n 8)).
{ clear -N HLO HL1 HHI HCE. unfold shad, shlen, ASHOFF, rup in *. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in *. Z.div_mod_to_equations. lia. }
pose proof (dk_pre_pure _ g RNG L t lst hm (qb + (n + 8192)) m DK DS TI ltac:(unfold AIMG_HI; lia) NI SI
DHL DTL ltac:(cbn [ek_seps] in ES; destruct full; [destruct ES as (_ & _ & _ & S4); destruct FULL as (_ & _ & _ & _ & L0 & _); exact (proj1 (proj2 (S4 eq_refl))) | destruct FULL as [_ ->]; unfold AIMG_HI in *; lia])
ltac:(cbn [ek_seps] in ES; destruct full; [destruct ES as (_ & _ & _ & S4); exact (proj2 (proj2 (S4 eq_refl))) | destruct FULL as [_ ->]; unfold AIMG_HI in *; lia])
ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _) | destruct FULL as [_ ->]]; unfold AIMG_HI in *; lia)
ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & L1 & _) | destruct FULL as [_ ->]]; unfold AIMG_HI in *; atop_facts; lia)
ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _); right | destruct FULL as [_ ->]; left]; unfold AIMG_HI in *; lia))
as (DF1 & DF2 & DF3 & DF4 & DG0 & DG1 & DG2).
cbn [ek_seps] in ES. destruct ES as (SB1 & SB2 & SB3 & SL).
assert (PL2 : lst = 0 \/ 0x10007fff8000 <= lst) by (destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _); right; exact L0 | destruct FULL as [_ E0]; left; exact E0]).
assert (PLB : lst + 8192 <= ATOP) by (destruct full; [destruct FULL as (_ & _ & _ & _ & _ & L1 & _); exact L1 | destruct FULL as [_ E0]; rewrite E0; atop_facts; lia]).
pose proof (qsz_int lst ltac:(clear -PL2; lia) ltac:(clear -PLB; atop_facts; lia)) as (zq & QZ0 & QZ1 & QZ2 & QZ3).
unfold AIMG_HI, AFREE_SYM, AFREE_PC in *.
word_range sp SPR.
box DHT. box DTN. box DTS. box DTB. box DTL. box DBL. box DHB. box DHL. box SB1. box SB2. box SB3. box DF1. box DF2. box DF3. box DF4. box DG2. box PL2.
set (sp1 := Z_to_bv 64 (bv_unsigned sp + -2128)) in *.
assert (Hsp : bv_unsigned sp1 = bv_unsigned sp + -2128) by (subst sp1; apply unsigned_lit; lia).
replace (bv_unsigned sp + -2272) with (bv_unsigned sp1 + -144) in * by lia.
replace (bv_unsigned sp + -2208) with (bv_unsigned sp1 + -80) in * by lia.
eapply evtF_cut.
{ eapply (put_from_refill_spec full g t hm lst b RNG (Z_to_bv 64 0x53480) sp1 gp tp sp (Z_to_bv 64 (hm + 16)) (Z_to_bv 64 (t + 208)) sp1
(Z_to_bv 64 0x53410) (Z_to_bv 64 1) sp1 (Z_to_bv 64 (bv_unsigned sp + -81)) s6 s7 s8 s9 s10 s11
ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m n nb fst0 qb b1 actx lo nx bsz cnt spacebeg maxc csz stj idxw chunks hs j0).
all: try lazymatch goal with
| |- stk _ _ _ _ => first [exact ST | exact IAS]
| |- mem_inv _ _ => exact MI
| |- if _ then _ else _ => exact FULL
| |- dk_pre _ _ _ _ _ _ _ _ => exact DK
| |- @eq word _ _ => reflexivity
| |- @eq Z _ _ => first [exact HBE | lia]
| |- ex _ => exact BJ
| |- _ \/ _ => first [ub DHT; lia | ub DTB; lia | ub DTL; lia | ub DBL; lia | ub DHB; lia | ub DHL; lia]
| |- rng _ _ _ => solve_rng
| |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
| |- rw_cells _ _ (shad _) _ => exact SH
| |- rw_cells _ _ (_ + 80) _ => exact QC
| |- rw_cells _ _ (_ + 2128) _ => exact CR
| |- rw_cells _ _ (_ + 2784) _ => exact STS
| |- rw_cells _ _ (_ + -80) _ => exact FRP
| |- iclr _ _ => exact TI
| |- rw_cells _ _ (_ + -144) _ => exact FRE
| |- u32arr _ _ _ _ => exact CH
| |- nth_error _ _ = _ => exact NTH
end.
all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
all: match goal with |- ?G => idtac "REMQ" G end. }
cbv beta. intros ms2 PP. unfold put_tail_post in PP.
destruct PP as (t0b & t1b & t2b & a0b & a1b & a2b & a3b & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2
& -> & MUp & WMp & MIp & STp & SH2 & HD2 & QC2 & EKP & DKP).
replace (ret_pc (Z_to_bv 64 341120)) with (Z_to_bv 64 341120) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
cbn [ek_b] in MUp.
xport FC MUp WMp ltac:(ub DHT; ub DHB; ub DHL; ub DF1; lia).
xport STATS MUp WMp ltac:(rewrite LSJ; ub DTB; ub DTL; ub DF2; lia).
xport UW MUp WMp ltac:(ub DTB; ub DTL; ub DF2; lia).
xport FL MUp WMp ltac:(ub DG2; ub PL2; lia). xport IAS MUp WMp ltac:(ub DG2; ub PL2; lia).
xport SS MUp WMp ltac:(lia). xport TB MUp WMp ltac:(rewrite LTB; lia). xport FRS MUp WMp ltac:(lia).
assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m2 (0xa3688 + 8 * j) (le8 (Z_to_bv 64 0))).
{ (intros j Hj; eapply bytes_at_agree; [exact (IAM j Hj)|];
intros i Hi; apply MUp; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; ub DG2; ub PL2; lia). }
clear IAM.
assert (DEP2 : ADEPOT DI L m2).
{ eapply (adi_frame DI); [exact DEP | exact MUp | exact WMp |].
(repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
first [lia | ub DTN; ub DTS; lia | ub SB2; ub SB3; lia | ub DF3; ub DF4; ub DG2; lia
| destruct full; [destruct (SL eq_refl) as (_ & S6 & S7); lia | destruct FULL as [_ LST0]; lia] ] |]); apply Forall_nil). }
clear DEP.
subst sp1. rewrite ?unsigned_lit in STp by lia. rewrite ?unsigned_lit in MUp by lia.
apply rw_cells_of_u64arr in TB. rewrite LTB in TB.
eapply evtF_mono.
{ (eapply (ficptD_spec RNG sp gp tp); [exact STp | atop_facts; lia | lia | exact MIp
| eexists; split; [exact SS | reflexivity]
| eexists; split; [replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) by lia; exact TB | reflexivity]
| exact FRS | exact RIMG | solve_rng ]). }
cbv beta. intros ms3 [-> ST3].
assert (MU : munch (free_W L sp t hm n lst (EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs) g) m m2).
{ eapply munch_weaken; [| exact MUp]. cbn [ek_b]. solve_sub_fp sp. }
unfold free_fast_post. exists id. do 15 eexists. exists m2, sj.
split; [reflexivity|].
split; [exact MU|]. split; [exact WMp|]. split; [exact MIp|]. split; [exact ST3|]. split; [exact IDR|].
split; [exact HD2|]. split; [exact FC|]. split; [exact SH2|]. split; [exact QC2|]. split; [exact EKP|]. split; [exact DKP|].
split; [exact STATS|]. split; [exact LSJ|]. split; [exact UW|]. split; [exact FL|]. split; [exact IAS|]. split; [exact IAM2|].
exact DEP2.
Unshelve. all: try exact ST; try exact STp.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End WithDepot.
End CANSEC1.
