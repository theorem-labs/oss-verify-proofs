(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode Arr InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg AProto ABase.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AKit AKit2 ABytes AModelFacts APrimFacts F_memsetZ F_aunwind F_aalloc_s F_aalloc3 F_acache3 F_aclass2.
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
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma cb_take : forall m A n k bs,
rw_cells asegs m A [CB (Z.to_nat n) bs] -> 0 <= k <= n ->
rw_cells asegs m A [CB (Z.to_nat k) (firstn (Z.to_nat k) bs)] /\ rw_cells asegs m (A + k) [CB (Z.to_nat (n - k)) (skipn (Z.to_nat k) bs)].
Proof.
intros m A n k bs H HK.
assert (L : length bs = Z.to_nat n) by (destruct H as [[[WF _] _] _]; cbn in WF; exact WF).
assert (H2 : rw_cells asegs m A [CB (Z.to_nat k) (firstn (Z.to_nat k) bs); CB (Z.to_nat (n - k)) (skipn (Z.to_nat k) bs)]).
{ eapply rw_cells_recast; [exact H | | |].
- cbn. rewrite length_firstn, length_skipn. Local Ltac2 Set LiaHints.tbl := fun () => "0040>17399603340.9 35959516864.9 51794591773.1164625611341.9 00000600<00B00HS2HK1LS2HK1LS2HK1LS2HK1L".
repeat split; lia.
- cbn [cells_bytes cbytes]. rewrite !app_nil_r, firstn_skipn. reflexivity.
- cbn [cells_size csize]. lia. }
lazymatch type of H2 with rw_cells _ _ _ [?x; ?y] => change [x; y] with ([x] ++ [y]) in H2 end.
apply rw_cells_app in H2. destruct H2 as [HA HR]. cbn [cells_size csize] in HR. rewrite Nat.add_0_r, Z2Nat.id in HR by lia.
split; [exact HA | exact HR].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma cb_app2 : forall m A n1 bs1 n2 bs2,
rw_cells asegs m A [CB n1 bs1] -> rw_cells asegs m (A + Z.of_nat n1) [CB n2 bs2] ->
rw_cells asegs m A [CB (n1 + n2) (bs1 ++ bs2)].
Proof.
intros m A n1 bs1 n2 bs2 H1 H2.
assert (H : rw_cells asegs m A ([CB n1 bs1] ++ [CB n2 bs2])).
{ apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize]. rewrite Nat.add_0_r. exact H2. }
cbn [app] in H. eapply rw_cells_recast; [exact H | | |].
- destruct H1 as [[[W1 _] _] _]. destruct H2 as [[[W2 _] _] _]. cbn in W1, W2 |- *. rewrite length_app. Local Ltac2 Set LiaHints.tbl := fun () => "0020>12519147942.1041065774016.10000007008S2W12W2S".
repeat split; lia.
- cbn [cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
- cbn [cells_size csize]. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma stats_class_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (X size : Z),
a0 = Z_to_bv 64 X -> 0 <= X -> X + 112 < 2^64 ->
24 <= size <= 65536 -> size mod 8 = 0 ->
rng_aimg RNG ->
evtF asegs RNG (fun ms' => exists a2' a3' a4' a5' a6',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (X + 112)) (Z_to_bv 64 (class_id size)) a2' a3' a4' a5' a6' a7 s2 (Z_to_bv 64 size) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x32b2c) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 size) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x32a38) fc None m (seg_rom asegs)).
Proof.
intros until size. intros -> X0 X1 SZ M8 RIMG.
Local Ltac2 Set LiaHints.tbl := fun () => "0050>16021673688.4823689357298.4134834872776.4835243812325.5565106454549.4800000400800?00C00GS2K1S2SZS2SZ2K1S2SZS2SZ".
pose proof (class_facts size ltac:(lia)) as CF. cbv zeta in CF. destruct CF as (C1 & CS1 & CS2 & CS3 & CSM & CBG).
step. zstep.
step. if_cases K1; zify_cond K1.
- eapply evtF_mono; [eapply (classblock2_spec RNG); [lia | exact M8 | exact RIMG] |].
cbv beta. intros ms' P. destruct P as (a2' & a3' & a4' & a5' & a6' & ->). do 5 eexists. reflexivity.
- zstep. zstep. rewrite <- (CSM ltac:(lia)). step.
apply evtF_done. do 5 eexists. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma fill_len_spec : forall RNG ra sp gp tp t0 t1 t2 s0 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (n : Z),
0 <= n < 2^40 ->
rng_aimg RNG ->
evtF asegs RNG (fun ms' =>
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 (Z_to_bv 64 4096) (Z_to_bv 64 (Z.min n 4096)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x32b64) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 (Z_to_bv 64 4096) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x32b58) fc None m (seg_rom asegs)).
Proof.
intros until n. intros N RIMG.
step. step. Local Ltac2 Set LiaHints.tbl := fun () => "0030>2210563924.38 40904327378.3861927706159.38000003006009S1KS1KS1N".
if_cases K; zify_cond K.
- replace (Z.min n 4096) with n by lia. apply evtF_done. reflexivity.
- step. replace (Z.min n 4096) with 4096 by lia. apply evtF_done. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
Local Ltac aload ST8 i AEXPR :=
lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
let RD := fresh "RD" in
pose proof (u64arr_read asegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
step; clear RD
end.
Local Ltac astore ST8 i :=
lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
let SOK := fresh "SOK" in
pose proof (u64arr_store_ok asegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
step;
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) (le8 ?v)) _) =>
let S2 := fresh "STATS" in
pose proof (u64arr_write asegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
replace (A + 8 * i)%Z with E in S2 by lia;
clear ST8; store_done; try clear SOK; rename S2 into ST8
end
end.
Section CANSEC2. Context {rc : runConstT}.
Definition allocD_postG (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32)
(n t AB UB lo b1m id : Z) (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) (uj : list byte) (m : amem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' sj',
ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
F (ret_pc ra0) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168); (UB - 16, UB + n); (AB, AB + 16)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
/\ rw_cells asegs m' UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat (Z.min n 4096)) ++ skipn (Z.to_nat (Z.min n 4096)) uj)]
/\ rw_cells asegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 (Z.lor (Z.land b1m 243) 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
/\ (16 < rz_size n -> rw_cells asegs m' AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]).
#[using="Type"] Lemma allocD_gen : forall (L : alayout) RNG sp gp tp (F : bvmap 5 word) fc (m : amem)
(n t c AB UB lo b0 b1m id S : Z) (sj : list word) (uj : list byte) (j1 j2 : word)
(fr0 : list byte) (raX ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6x t3 t4 t5 t6 : word),
stk asegs m lo (bv_unsigned sp + -128) -> ATOP <= lo -> lo <= bv_unsigned sp + -128 - 32 ->
mem_inv asegs m ->
tp = Z_to_bv 64 ATP ->
1 <= n -> is_primary n = true ->
UB = AB + rz_size n -> 0x10007fff8000 <= AB -> UB + n <= ATOP -> AB mod 16 = 0 ->
class_id (needed_size n) = c ->
(t + 4096 <= AB \/ AB + 65536 <= t) ->
rw_cells asegs m (bv_unsigned sp + -128)
[CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v;
C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
rw_cells asegs m 0xa1ce0 [C1 (Z_to_bv 8 1)] -> rw_cells asegs m 0xa1ce4 [C4 (Z_to_bv 64 0)] ->
rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 (al_ctx L))] ->
rw_cells asegs m (al_ctx L + 152) [C8 (Z_to_bv 64 t)] ->
0 < al_ctx L -> al_ctx L + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->
rw_cells asegs m 0x9fca4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
rw_cells asegs m 0x99770 [C8 (Z_to_bv 64 0x133fa8); C8 (Z_to_bv 64 0x9fc78); C8 (Z_to_bv 64 0xa2478);
C8 (Z_to_bv 64 0xa3168); C8 (Z_to_bv 64 0xa3170); C8 (Z_to_bv 64 0xa3160)] ->
rw_cells asegs m 0x997a0 [C8 (Z_to_bv 64 0x9b5e8)] ->
rw_cells asegs m 0x9b5e0 [C8 (Z_to_bv 64 0x92ab0); C8 (Z_to_bv 64 0x92eb4)] ->
rw_cells asegs m 0x9a3d8 [C8 (Z_to_bv 64 0x10)] -> rw_cells asegs m 0x5d5420 [C4 (Z_to_bv 64 0)] ->
rw_cells asegs m 0x133f40 [C8 (Z_to_bv 64 0)] ->
rw_cells asegs m UB [CB (Z.to_nat n) uj] ->
rw_cells asegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1m); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)] ->
0 <= b1m < 256 -> 0 < id < 2^31 ->
(16 < rz_size n -> rw_cells asegs m AB [C8 j1; C8 j2]) ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG t 4096 ->
rng RNG (UB - 16) (n + 16) -> rng RNG AB 16 ->
evtF asegs RNG (allocD_postG sp gp tp F fc n t AB UB lo b1m id ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v uj m)
(MS (mkR raX (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
(Z_to_bv 64 1) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 UB) (Z_to_bv 64 (UB + -16)) s6x
(Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 (UB + n)) (Z_to_bv 64 t) (Z_to_bv 64 1)
t3 t4 t5 t6)
F (Z_to_bv 64 0x329e8) fc None m (seg_rom asegs)).
Proof.
intros until t6.
intros ST CEIL LO MI TP N PRIM HUB ABLO UBHI AB16 HC DJT FR STATS LSJ TI TK T88 TSD CT CX0 CX1 T0 T1
FLG GOT GOT80 REAL LS1 LS2 HK UJ HDR B1M IDR LH RIMG RSTK RCTX RT RU RAB. band_lin.
unfold AIMG_HI, ATP88, ATSD in *.
pose proof (prim_facts n N PRIM) as (NS & RZR & RZE & RZM & RLR & RSR & RSM & NSR).
pose proof (prim_class_facts n c N PRIM HC) as (C16 & NSZ2 & SM16 & SMALL & MC2).
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168); (UB - 16, UB + n); (AB, AB + 16)]%Z m) as MU.
pose proof (wmono_refl asegs m) as WM.
box DJT. box LH.
snapshot [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168)]%Z MUs WMs.
box UJ. box HDR.
step. Local Ltac2 Set LiaHints.tbl := fun () => "05_0?10028172029.12410028172029.14910028172029.15110167497279.15110456434697.1541047820382.116 10587903613.11710640816421.11810640816421.11910911084698.14111077664131.14911077664131.15111462352626.1171162083375.148 1162083375.150 11801586693.12411801586693.14911801586693.15112308886460.14912341586989.11712373220886.14412373220886.14612406238321.15012560013042.11713086827028.13013118011600.1171324746171.152 13496907890.118137287794.118  14208485765.11714208485765.1181428302706.117 14335039570.1501454307978.141 1503082802.152 15043033658.11815051124456.15415077021426.1171533820803.149 1533820803.151 15588165249.12515588165249.1421561637052.149 15636037571.14415813913903.13115924740850.11716200246386.11816210300264.15416263107213.14916482458097.14116703780397.11816866801769.1231740683122.117 17776320431.14817776320431.15017986879152.11617986879152.14017986879152.14218048262588.14918504928616.15418748206397.12418748206397.14918748206397.1511898977476.142 19123199200.15119125296361.1541937063194.116 19372886979.14420609531986.15020880379370.15021250035837.12421250035837.14921250035837.15121355937650.1172150086885.150 2172922258.149 21857976067.14421873284733.12421873284733.14921873284733.15121924557829.11721924557829.11822026868477.12422026868477.14922026868477.15122632813821.12422632813821.14922632813821.15122675801219.15022675801219.15222700267513.12522700267513.14622700267513.15022700267513.15223586406368.12024205896189.12424205896189.14924205896189.15124559885231.14824559885231.15024566790608.12324904914272.11724924589988.13024984467862.1202499582526.141 25029166211.14925029166211.15125065190167.12425071629079.14125071629079.15025080282415.11725080282415.12325195294056.1542521654632.154 25676588393.11825787632170.12525878270254.15125878270255.14826494647592.14126494647592.14926494647592.15026494647592.15426496924968.14226496924968.14426734967870.14126778510268.14926868428163.14826868428163.15026879533652.12926879533652.13027188338533.12527408782894.14927408782894.15127576757255.12427576757255.14927576757255.15127730847314.15028335534850.12528738030430.14128767007858.11828789365712.12329782367974.12329811175882.12329983937266.1173017725367.154 30233406450.11730507153671.14030518562691.14830518562691.15030719730331.12630719730331.14130876703602.11731218985776.11731407249106.15031498151784.15432377474162.1173289508284.149 33333358812.12833542888562.11833558212378.15033722085182.14133765134616.14033765134616.14233890036527.14833890036527.15034170950174.14135101720189.12435101720189.14935101720189.15135148913011.15435933558651.13136033352946.11736115622446.14936115622446.15136254216601.15236254216601.15537031786322.15037283284082.11837386977061.11637386977061.14037386977061.14237429491794.15037585159586.14937763307450.15337774388668.14938074103656.15438163290814.14138168113982.14138212704797.12338212704797.1243894281273.118 39407463154.14139771339708.14939932046344.11739938772490.13140091925676.14740091925676.14940277673936.12340326235777.12441422282358.11842389998958.15442445826608.11742445826608.1184258490819.144 42817532658.11742831019478.15042967766376.15443059454659.14443082390590.14143987951406.14943987951406.15143995329413.14944158664835.15044158664835.15244311304733.11844395637586.15044484923210.12444484923210.14944484923210.15144602107843.14444767421808.14944824048191.14944824048191.15144833359747.14944833359747.15145288596498.12645327509712.12345451326843.13345666356082.11745944259164.11845962238104.12946019491907.14446238494928.12346501843261.12446501843261.14946501843261.15146625963587.14447089684979.14447089684979.14547154292033.12347557849085.11747836262864.1234798910125.117 49294572020.1194936038867.145 49433673850.14149433673979.14049578074883.14449696399402.12349793197630.14149801462716.14950092199005.118502630133.136  50362574674.15050457931440.11750461111123.12650582100210.11750689918696.15450750500979.11850893982834.11851678667180.14751678667180.1495173701827.144 51816630506.14151868145084.14952357022834.11752567164907.14152567164907.14952567164907.15052567164907.15452575291859.11752575291859.12352586760667.14952682867945.14152987902756.1195300105810.150 53442040214.14153532296636.14953693616498.11753767577775.14853767577775.15053810878302.13553938471742.14154078910070.13454129336050.11754636957394.15054753862002.11754761860978.11754969794426.11655110451570.11755338958788.13655460634391.14956091204670.14156170256219.11856172410654.13956172415395.1415684463747.132 56993309444.14156993309444.14357196545107.12657232203216.12357751108064.14857821142078.14158505212776.15458655119491.14958655119491.15259276314076.12559314873579.11859314873579.14259314873579.14359887912515.14459907387523.15059907387523.15260634079619.14860634079619.15061270615504.12361694112329.14561875611762.11761917199020.14761917199020.14961939782288.13162976134100.12962976134102.1326313882541.117 6313882541.118 63177324496.1236319832469.118 63235321900.14763235321900.14963670697722.14863745434493.11763974833010.11765485175549.12465485175549.14965485175549.15165797088788.12665983638659.14965983638659.15166028155702.11966028155702.14366028155702.14566149329551.25 66357861087.1506653728088.144 66701037743.1296758013062.118 68049033064.15468309604434.15068314709456.1237070580924.149 7563807307.123 7628953458.117 7780899791.149 7848643581.124 7848643581.149 7848643581.151 7882758244.154 8179223683.148 8179223683.150 8299458000.123 8346267669.123 8664102002.117 896064190.141  908653554.117  917434854.150  9196977948.127 9666466205.150 00000=00J00W00n01201701C01H01M01N01O01P01X01\01`02802L02`02f02n02o03003103903:03;03<03D03L03Q03V03^03l03m03n03o04504=04>04?05R06106706E06I06Q06Y06_06c06f06k07X07`07d07h07n08408:08@08F08S08`08m0:00:30:60::0:H0:V0:W0:d0;10;>0;F0;G0;J0;X0;e0<20<?0<D0<I0<V0<c0=00==0=J0=W0=X0=Y0>j0@90AQ0Bl0Bm0C:0CG0CT0CX0C\0DI0DJ0DK0DL0DZ0D[0D\0F10F40F70F80FH0FN0FT0FY0Fl0G00G40G70G80G;0G<0HM0If0J40J:0J;0J<0J=0JB0JE0JI0JM0JN0JO0JP0J^0J_0Jd0Jl0KY0KZ0K_0Kg0Km0L50LU0LV0LW0LZ0L]0Le0Li0M70M=0ME0MK0MP0MX0M\0Mj0Mk0Ml0N00N40N80NE0NR0N_0O20O70O?0OC0OG0OH0OI0OW0O_0Oc0Og0Ok0P90P=0P>0PD0PJ0PX0Pf0Po0Q80Q=0Q]0Qc0Qh0Qm0R10R50Rb0T:0T;0T?0TC0TG0TU0T]0Ta0Tg0U50UC0UG0UK0UL0UM0UN0US0Ua0Ub0Uc0Ud0V20V60VJ0V^0V_0V`0Va0WN0WS0W[0W\0W]0Wk0XX0Xe0Y20Y?0YM0Y[0Y\0Y]0Yi0ZV0Z^0Z_0Z`0[50[J0[X0[`0[n0\40\:0\;0\I0\M0\U0\]0\c0\d0\l0]00]40]B0]F0]L0]T0]W0]X0][0]\0]]0^B0^H0^X0^Y0^g0^h0^n0_60_:0_>0_G0_U0_V0_^0_l0`40`<0`A0`I0`N0`a0`o0a40a50a60a70a;0a?0a@0am0b20b@0bF0bG0bH0bI0bQ0b`0cf0d40d50d60d70d80de0df0dn0e20e60eH0eI0eN0eV0e^0fK0fS0fW0f[0f\0fh0g00g=0gJ0gW0ge0gf0gg0h60hE0hT0hh0hi0i40i90i:0i@0iN0j;0jA0jQ0jY0jZ0jg0k40kA0kE0kF0kG0l40l=0lE0lS0l[0l\0l]0lmS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO1N4UBHI2K43HspS2K4S3CX1S4CEIL2LO2T1S3LSJS3LSJSSSS3LSJ2T0S2LOS2LOS4CEIL2LO3CX13Hsp3LSJ2T1S4CEIL2LO1N4UBHI3HspS4CEIL2LO1N4UBHI3HspS4ABLOS3LSJ2T0SSSS3LSJ2T0SSSS3LSJ2T0S3LSJ2T0S3LSJS3LSJS3LSJ2T0S3HUB4ABLO3RZRSSSS4ABLOS3LSJ2T0SSS4CEIL2LO1N3HUB4ABLO4UBHI3LSJ2T12NS3RZR3RZE3RLR3RSR3RSM3NSR4NSZ24SM165SMALL2RZ2DX1HS4CEIL2LO1N3HUB4UBHI3RZR3RZE2RZS4ABLOS3HUB4ABLO3RZRS2LOS3LSJ2T0S3LSJ2T0S4ABLOS2K4S1NS3LSJS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S3LSJ2T0S2LOS2LOS4CEILS4CEILS4CEILS4ABLOS4ABLOS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS3HUB4ABLO3LSJ2NS3RZR3RZE3RLR3RSR3RSM3NSR3C164NSZ24SM165SMALL2K32DXS1NS1NS2T1S3HUB4ABLO3RZRS3HUB4ABLO3RZRSS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS3LSJ2T0SS1NS3HUB4ABLO3RZRS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS3LSJS3LSJS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspSSS4CEIL2LO4ABLO3LSJ2T12NS3RZR3RZE3RLR3RSR3RSM3NSR4NSZ24SM165SMALL3Hsp1H1N3HUB4UBHIS4CEIL2LO4ABLO4UBHI3LSJ2NS3RZR3RZE3RLR3RSR3RSM3NSR3C164NSZ24SM165SMALL1H3HUB2T1S4CEIL2LO1N3HUB4ABLO4UBHI3LSJ2NS3RZR3RZE3RLR3RSR3RSM3NSR3C164NSZ24SM165SMALL2K33Hsp1H2T1S4CEIL2LO1N3HUB4ABLO4UBHI3LSJ2NS3RZR3RZE3RLR3RSR3RSM3NSR3C164NSZ24SM165SMALL2K32K43Hsp1H2T1SS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS2LOS2LOS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2SSSS3HUB4ABLO3RZRSSS4CEIL2LO1N3HUB4ABLO4UBHI4AB163LSJ2T12NS3RZR3RZE3RLR3RSR3RSM3NSR4NSZ24SM165SMALL2DX1HS1NS1NSS4CEIL2LO2T13C16S4ABLOS4ABLOS3NSRS1N2NS3RZR3RSR4NSZ2S2LOS2LOS1NSS1NSS4CEIL2LO1N3HUB4ABLO4UBHI3LSJ2T12NS3RZR3RZE3RLR3RSR3RSM3C164NSZ25SMALL2K02K32DX1HS4CEIL2LO1N3HUB4ABLO4UBHI4AB163LSJ2T12NS3RZR3RZE3RLR3RSR3RSM3C164NSZ25SMALL2K02K32K42DX1HS3HUB4ABLO3RZRS4ABLOSSSS3LSJS1NS2LOS2LOFFFS3HUB4ABLO3RZRSS3B1MS3LSJ2T0S4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2SS3C16S3LSJ2T0S4ABLOS3LSJ2T0S1N3HUB4ABLO4UBHI2NS3RZR3RSR3NSRSSS1NS1NS3LSJ2T0S2T1S3HUB4ABLO3RZRS4ABLOS3LSJ2T0S4ABLOS3LSJS3LSJ2T0S2HBS3HUB4ABLO3RZRSSS2LOS2LOS2HBS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO1N4UBHI2K4S3LSJS3LSJ2T0S2LOS2LOSSS3HUB4ABLO3RZRS3LSJ2T0S2LOS2LOS2LOS3HUB4ABLO3RZRS2HBSS4ABLOS4ABLOS3HUB4ABLO3RZRS3HUB4ABLO3RZRS3LSJ3C16S3LSJ3C16S3LSJS1N3HUB4ABLO4UBHI2NS3RZR3RSR3NSRS4ABLOS3NSRS3NSRS2LOS2LOS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S4CEIL2LO1N3HUB4ABLO4UBHI4AB163LSJ2T12NS3RZR3RZE3RLR3RSR3RSM3NSR4NSZ24SM165SMALL2K02DX1HSS2HBS2T1S2T1S3HUB4ABLO3RZRS3LSJ2T0S2HBS4ABLOS3HUB4ABLO3RZRS3HUB4ABLO3RZRS2LOS2LOSSSS3LSJS3HUB4ABLO3RZRFFFS3HUB4ABLO3RZRS2K4S4CEIL2LO1N4UBHI3HspS4CEIL2LO1N4UBHI3HspSSSS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S3LSJS3LSJ2T0SSS3HUB4ABLO3RZRS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS3HUB4ABLO3RZRS4CEIL2LO4UBHISSS4CEIL2LO2T1S4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S3LSJ2T0SFS1N3HUB4ABLO4UBHI3RZRS1N3HUB4ABLO4UBHI3RZRS3HUB4ABLO3RZRS2T13C16S3HUB4ABLO3RZRS4ABLOS2T11HSS3HUB4ABLO3RZRS2T1S4UBHI1HS3LSJ2T0S4ABLOFS3LSJ2T0S2LOS2LOS3HUB4ABLO3RZRS2HBS4ABLOS3LSJ2T0S1NSS1NSSS4CEIL2LO1N3HUB2T12NS3RZR3RSR3NSR3C16S4ABLOS4CEIL2LO1N4UBHISS3HUB4ABLO3RZRSS4ABLOS3LSJ2T0S2LOS2LOS3LSJ3C16S3HUB4ABLO3RZRSS3LSJ2T0S3HUB4ABLO3RZRS3LSJ2T0S3LSJ2T0S3CX0S3LSJ2T0S3C16S4CEIL2LO1N4UBHI2K4S3HUB4ABLO3RZRS3HspSSSS2LOS2LOSS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S3B1MS3HUB4ABLO3RZRS4ABLOSSSS3NSR2K0S3HUB3RZE2K32RZS3HUB4ABLO3LSJ2NS3RZR3RZE3RLR3RSR3RSM3NSR3C164NSZ24SM165SMALL2K32K42DXS3HUB4ABLO3RZRSSSSS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2FS3LSJ2T0S2LOS2LOS1N2NS3RZR3RSR3NSRSS3LSJS3LSJ2T0S3LSJ2T0S4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S3LSJ2T0S2LOS2LOSS4CEIL2LO2T1S3LSJ2T0S4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS3HUB4ABLO3RZRSSS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS3RZM3RSM1H2H02H42H9SS4CEIL4UBHIS3LSJSS4ABLOS3HUB4ABLO3RZRS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S4ABLOS4CEIL2LO2T13C16S3LSJ2T0SS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS2K4SSS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S3LSJ3C16S3LSJ2T0S3HUB4ABLO3RZRS3LSJ2T0SSS4CEIL2LO1N4UBHI".
call_sp (thread_stats_spec RNG (al_ctx L) t lo).
all: try lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption
| |- stk _ _ _ _ => eassumption
| |- mem_inv _ _ => assumption
| |- @eq word _ _ => first [reflexivity | exact TP]
| |- rw_cells _ _ (_ + 152) _ => exact CT
| |- rw_cells _ _ _ _ => assumption
end.
all: try lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption
| |- rng _ _ _ => solve_rng
| |- _ => unfold AIMG_HI; lia
end.
rename POST into ST.
aload STATS 2 (t + 2800 + 16).
aload STATS 0 (t + 2800 + 0).
aload STATS 1 (t + 2800 + 8).
zstep. zstep. step. zstep. zstep. zstep.
astore STATS 0.
astore STATS 1.
astore STATS 2.
step. if_cases K0; zify_cond K0. 2: { exfalso. lia. }
eapply evtF_cut; [eapply (stats_class_spec RNG); [reflexivity | lia | lia | lia | clear -NS RSM RZM; rewrite NS; Z.div_mod_to_equations; lia | exact RIMG] |].
cbv beta. intros msS PS. destruct PS as (a2s & a3s & a4s & a5s & a6s & ->). rewrite HC.
zstep. zstep.
rewrite (Z.shiftl_mul_pow2 c 3) by lia. change (2^3) with 8.
aload STATS (14 + c) (t + 2912 + c * 8).
zstep.
astore STATS (14 + c).
carry UJ MUs WMs ltac:(with_box DJT lia). carry HDR MUs WMs ltac:(with_box DJT lia).
unbox LH.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (LH' : 16 < rz_size n -> rw_cells asegs mm AB [C8 j1; C8 j2]) end.
{ intros RZ. specialize (LH RZ). box LH. carry LH MUs WMs ltac:(with_box DJT lia). exact LH. }
clear LH MUs WMs. box LH'. box STATS.
snapshot [(UB - 16, UB + n); (AB, AB + 16); (bv_unsigned sp + -128 - 32, bv_unsigned sp + -128)]%Z MUc WMc.
snapshot [(UB - 16, UB + n); (bv_unsigned sp + -128 - 32, bv_unsigned sp + -128)]%Z MUl WMl.
step. step. if_lit.
step. step. lstep. step. if_lit.
eapply evtF_cut; [eapply (fill_len_spec RNG); [lia | exact RIMG] |]. cbv beta. intros msF ->.
set (fl := Z.min n 4096) in *.
destruct (cb_take _ _ n fl uj UJ ltac:(subst fl; lia)) as [UJ1 UJ2]. clear UJ.
step. step. step. lstep. step.
step. call (memset_specZ RNG UB 0xbe fl (firstn (Z.to_nat fl) uj)).
all: try lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption
| |- mem_inv _ _ => assumption
| |- @eq word _ _ => reflexivity
| |- rw_cells _ _ _ [CB _ _] => exact UJ1
| |- rng _ _ _ => eapply rng_sub'; [exact RU|]; subst fl; lia
| |- _ => subst fl; atop_facts; lia
end.
rename POST into UF1.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (UF : rw_cells asegs mm UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat fl) ++ skipn (Z.to_nat fl) uj)]) end.
{ replace (Z.to_nat n) with (Z.to_nat fl + Z.to_nat (n - fl))%nat by (subst fl; lia).
apply cb_app2; [exact UF1|]. rewrite Z2Nat.id by (subst fl; lia). exact UJ2. }
clear UF1 UJ2.
step. callp lsan_disabled_spec; [exact TP | exact LS1 | exact LS2 |].
lstep. zstep. zstep. zstep. zstep. step.
sstep. step. step.
unbox LH'.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (LH : 16 < rz_size n -> rw_cells asegs mm AB [C8 j1; C8 j2]) end.
{ intros RZ. specialize (LH' RZ). box LH'. carry LH' MUl WMl ltac:(lia). exact LH'. }
clear LH' MUl WMl.
pose proof (rz_size_cases n) as RZC. box RZC.
step. if_cases K3; zify_cond K3.
-
clear LH.
step. step. step. call_sp (run_malloc_hooks_spec RNG).
all: try lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption
| |- stk _ _ _ _ => eassumption
| |- mem_inv _ _ => assumption
| |- rw_cells _ _ _ _ => exact HK
| |- rng _ _ _ => solve_rng
| |- _ => atop_facts; lia
end.
rename POST into ST.
do 16 step.
release_frame FR ST (bv_unsigned sp).
carry STATS MUc WMc ltac:(with_box DJT lia).
apply evtF_done. unfold allocD_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
split; [exact STATS|]. split; [rewrite !upd_length; exact LSJ|]. split; [exact UF|]. split; [exact HDR|].
intros RZ. exfalso. lia.
-
specialize (LH ltac:(with_box RZC lia)).
zstep. step. if_cases K4; zify_cond K4. { exfalso. with_box RZC lia. }
step. step.
step. step. step.
step. step. step. call_sp (run_malloc_hooks_spec RNG).
all: try lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption
| |- stk _ _ _ _ => eassumption
| |- mem_inv _ _ => assumption
| |- rw_cells _ _ _ _ => exact HK
| |- rng _ _ _ => solve_rng
| |- _ => atop_facts; lia
end.
rename POST into ST.
do 16 step.
release_frame FR ST (bv_unsigned sp).
carry STATS MUc WMc ltac:(with_box DJT lia).
apply evtF_done. unfold allocD_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
split; [exact STATS|]. split; [rewrite !upd_length; exact LSJ|]. split; [exact UF|]. split; [exact HDR|].
intros _. exact LH.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC2.
