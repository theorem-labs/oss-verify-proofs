(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode Arr InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg AProto ABase.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import AKit AKit2 ABytes AModelFacts APrimFacts F_memsetZ F_aunwind F_aalloc_s F_aalloc3 F_acache3 F_aclass2.
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
rw_cells bsegs m A [CB (Z.to_nat n) bs] -> 0 <= k <= n ->
rw_cells bsegs m A [CB (Z.to_nat k) (firstn (Z.to_nat k) bs)] /\ rw_cells bsegs m (A + k) [CB (Z.to_nat (n - k)) (skipn (Z.to_nat k) bs)].
Proof.
intros m A n k bs H HK.
assert (L : length bs = Z.to_nat n) by (destruct H as [[[WF _] _] _]; cbn in WF; exact WF).
assert (H2 : rw_cells bsegs m A [CB (Z.to_nat k) (firstn (Z.to_nat k) bs); CB (Z.to_nat (n - k)) (skipn (Z.to_nat k) bs)]).
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
rw_cells bsegs m A [CB n1 bs1] -> rw_cells bsegs m (A + Z.of_nat n1) [CB n2 bs2] ->
rw_cells bsegs m A [CB (n1 + n2) (bs1 ++ bs2)].
Proof.
intros m A n1 bs1 n2 bs2 H1 H2.
assert (H : rw_cells bsegs m A ([CB n1 bs1] ++ [CB n2 bs2])).
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
evtF bsegs RNG (fun ms' => exists a2' a3' a4' a5' a6',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (X + 112)) (Z_to_bv 64 (class_id size)) a2' a3' a4' a5' a6' a7 s2 (Z_to_bv 64 size) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x32a18) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 size) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x32924) fc None m (seg_rom bsegs)).
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
evtF bsegs RNG (fun ms' =>
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 (Z_to_bv 64 4096) (Z_to_bv 64 (Z.min n 4096)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x32a50) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 (Z_to_bv 64 4096) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x32a44) fc None m (seg_rom bsegs)).
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
pose proof (u64arr_read bsegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
step; clear RD
end.
Local Ltac astore ST8 i :=
lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
let SOK := fresh "SOK" in
pose proof (u64arr_store_ok bsegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
step;
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) (le8 ?v)) _) =>
let S2 := fresh "STATS" in
pose proof (u64arr_write bsegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
replace (A + 8 * i)%Z with E in S2 by lia;
clear ST8; store_done; try clear SOK; rename S2 into ST8
end
end.
Section CANSEC2. Context {rc : runConstT}.
Definition allocD_postG (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32)
(n t AB UB lo b1m id : Z) (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) (uj : list byte) (m : amem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' sj',
ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
F (ret_pc ra0) fc None m' (seg_rom bsegs)
/\ munch [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168); (UB - 16, UB + n); (AB, AB + 16)]%Z m m'
/\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ stk bsegs m' lo (bv_unsigned sp)
/\ u64arr bsegs m' (t + 2800) sj' /\ length sj' = 46%nat
/\ rw_cells bsegs m' UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat (Z.min n 4096)) ++ skipn (Z.to_nat (Z.min n 4096)) uj)]
/\ rw_cells bsegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 (Z.lor (Z.land b1m 243) 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
/\ (16 < rz_size n -> rw_cells bsegs m' AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]).
#[using="Type"] Lemma allocD_gen : forall (L : alayout) RNG sp gp tp (F : bvmap 5 word) fc (m : amem)
(n t c AB UB lo b0 b1m id S : Z) (sj : list word) (uj : list byte) (j1 j2 : word)
(fr0 : list byte) (raX ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6x t3 t4 t5 t6 : word),
stk bsegs m lo (bv_unsigned sp + -128) -> ATOP <= lo -> lo <= bv_unsigned sp + -128 - 32 ->
mem_inv bsegs m ->
tp = Z_to_bv 64 ATP ->
1 <= n -> is_primary n = true ->
UB = AB + rz_size n -> 0x10007fff8000 <= AB -> UB + n <= ATOP -> AB mod 16 = 0 ->
class_id (needed_size n) = c ->
(t + 4096 <= AB \/ AB + 65536 <= t) ->
rw_cells bsegs m (bv_unsigned sp + -128)
[CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v;
C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->
rw_cells bsegs m 0xa1da0 [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m 0xa1da4 [C4 (Z_to_bv 64 0)] ->
rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 (al_ctx L))] ->
rw_cells bsegs m (al_ctx L + 152) [C8 (Z_to_bv 64 t)] ->
0 < al_ctx L -> al_ctx L + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->
rw_cells bsegs m 0x9fd64 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
rw_cells bsegs m 0x99900 [C8 (Z_to_bv 64 0x134068); C8 (Z_to_bv 64 0x9fd38); C8 (Z_to_bv 64 0xa2538);
C8 (Z_to_bv 64 0xa3228); C8 (Z_to_bv 64 0xa3230); C8 (Z_to_bv 64 0xa3220)] ->
rw_cells bsegs m 0x99930 [C8 (Z_to_bv 64 0x9b778)] ->
rw_cells bsegs m 0x9b770 [C8 (Z_to_bv 64 0x92c40); C8 (Z_to_bv 64 0x93044)] ->
rw_cells bsegs m 0x9a568 [C8 (Z_to_bv 64 0x10)] -> rw_cells bsegs m 0x5d54e0 [C4 (Z_to_bv 64 0)] ->
rw_cells bsegs m 0x134000 [C8 (Z_to_bv 64 0)] ->
rw_cells bsegs m UB [CB (Z.to_nat n) uj] ->
rw_cells bsegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1m); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)] ->
0 <= b1m < 256 -> 0 < id < 2^31 ->
(16 < rz_size n -> rw_cells bsegs m AB [C8 j1; C8 j2]) ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG t 4096 ->
rng RNG (UB - 16) (n + 16) -> rng RNG AB 16 ->
evtF bsegs RNG (allocD_postG sp gp tp F fc n t AB UB lo b1m id ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v uj m)
(MS (mkR raX (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
(Z_to_bv 64 1) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 UB) (Z_to_bv 64 (UB + -16)) s6x
(Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 (UB + n)) (Z_to_bv 64 t) (Z_to_bv 64 1)
t3 t4 t5 t6)
F (Z_to_bv 64 0x328d4) fc None m (seg_rom bsegs)).
Proof.
intros until t6.
intros ST CEIL LO MI TP N PRIM HUB ABLO UBHI AB16 HC DJT FR STATS LSJ TI TK T88 TSD CT CX0 CX1 T0 T1
FLG GOT GOT80 REAL LS1 LS2 HK UJ HDR B1M IDR LH RIMG RSTK RCTX RT RU RAB. band_lin.
unfold AIMG_HI, ATP88, ATSD in *.
pose proof (prim_facts n N PRIM) as (NS & RZR & RZE & RZM & RLR & RSR & RSM & NSR).
pose proof (prim_class_facts n c N PRIM HC) as (C16 & NSZ2 & SM16 & SMALL & MC2).
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168); (UB - 16, UB + n); (AB, AB + 16)]%Z m) as MU.
pose proof (wmono_refl bsegs m) as WM.
box DJT. box LH.
snapshot [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168)]%Z MUs WMs.
box UJ. box HDR.
step. Local Ltac2 Set LiaHints.tbl := fun () => "05_0?10028172029.12410028172029.14910028172029.15110167497279.15110456434697.1541047820382.116 10587903613.11710640816421.11810640816421.11910900051222.12010911084698.14111077664131.14911077664131.15111118462589.12411118462589.14911118462589.15111415763152.12311462352626.1171162083375.148 1162083375.150 11765624680.15411801586693.12411801586693.14911801586693.15112308886460.14912341586989.11712406238321.15013086827028.13013118011600.11713166236520.1541324746171.152 13303947452.14913596006226.15014208485765.11714208485765.11814335039570.1501503082802.152 15043033658.1181533820803.149 1533820803.151 15588165249.12515588165249.14215813913903.13115995719016.15416263107213.14916482458097.14116703780397.11816865227715.14416866801769.1231750798787.144 17758972368.12317776320431.14817776320431.15017967033458.11717986879152.11617986879152.14017986879152.14218436191427.14418803398514.1171898977476.142 19123199200.15119125296361.15419350300419.1441937063194.116 20880379370.15020970059894.13421077578749.12421077578749.14921077578749.15121282393832.15421490588786.1182150086885.150 2172922258.149 21924557829.11721924557829.11822182730578.15022675801219.15022675801219.15222700267513.12522700267513.14622700267513.15022700267513.15223182051176.15423586406368.12024559885231.14824559885231.15024904914272.11724924589988.1302497990096.123 25029166211.14925029166211.15125065190167.12425071629079.14125071629079.15025080282415.11725080282415.12325676588393.11825787632170.12525878270254.15125878270255.1482589182834.117 25896079568.12326170477810.11726494647592.14126494647592.14926494647592.15026494647592.15426496924968.14226496924968.14426868428163.14826868428163.15026879533652.12926879533652.1302699564227.144 27171665174.14127188338533.12527396617680.12327408782894.14927408782894.15127576757255.12427576757255.14927576757255.15128335534850.12528360709362.11728738030430.14128754851922.15028767007858.11828832574270.14129782367974.12329811175882.12329877002610.1173017725367.154 30420195523.14430507153671.14030518562691.14830518562691.15030608897138.11830719730331.12630719730331.14130876703602.11731218985776.11731423336146.15031521058898.15032162886226.15032418465650.11733333358812.12833558212378.15033765134616.14033765134616.14233890036527.14833890036527.15034022839870.14134170950174.14134811111154.11735148913011.15435256347600.12335376095986.11735587884146.11735933558651.13136115622446.14936115622446.15136254216601.15236254216601.15536814730237.12436814730237.14936814730237.15137386977061.11637386977061.14037386977061.14237585159586.14937763307450.15338074103656.15438212704797.12338212704797.12438465254514.1173894281273.118 39407463154.14139932046344.11739938772490.13140091925676.14740091925676.14940326235777.12440458636732.14941422282358.1184158230386.117 42389998958.15442445826608.11742445826608.11842831019478.15043041729214.14143372435176.15443509719107.14443987951406.14943987951406.15143995329413.14944158664835.15044158664835.15244305789522.15044311304733.11844484923210.12444484923210.14944484923210.15144602107843.14444631646014.14144767421808.14944824048191.14944824048191.15144833359747.14944833359747.15145201937650.11745288596498.12645451326843.13345944259164.11845962238104.12946148965950.14146368229782.14446368229782.14646562743228.14947089684979.14447089684979.14547103961859.14447154292033.12347420759102.14147557849085.11747747814717.12447747814717.14947747814717.1514798910125.117 49294572020.1194936038867.145 49433673850.14149433673979.14049696399402.12349890836722.11750056715216.12350092199005.118502630133.136  50457931440.11750461111123.12650750500979.11850964623824.12350993995517.12450993995517.14950993995517.15151136181618.11751191184446.14151515740530.11751633495293.12451633495293.14951633495293.15151678667180.14751678667180.14951816630506.14152297866226.11752458472562.11852567164907.14152567164907.14952567164907.15052567164907.15452575291859.11752575291859.12352586760667.14952682867945.14152987902756.11953442112190.14153767577775.14853767577775.15053810878302.13553826772850.11754833884274.11854969794426.11655338958788.13655460634391.14955860948746.14156170256219.11856172410654.13956172415395.14156371079120.12356590202216.1545684463747.132 56993309444.14156993309444.14357054875198.14157196545107.12657232203216.12357378147907.14457708384067.14457751108064.14857821142078.14157866941884.14958023386994.117586216434.117  58655119491.14958655119491.15258910293436.14958956747506.11759192378728.15459276314076.12559314873579.11859314873579.14259314873579.14359442793916.14959907387523.15059907387523.1526055995506.118 60634079619.14860634079619.15060685297596.14961694112329.14561917199020.14761917199020.14961939782288.1316293724274.118 62976134100.12962976134102.1326313882541.117 6313882541.118 63143451580.1496319832469.118 63235321900.14763235321900.14963620834110.14163670697722.14863745434493.11763923647848.1546398474066.150 64393308029.12464393308029.14964393308029.15164548988925.12464548988925.14964548988925.15165644234482.11765797088788.12665952741501.12465952741501.14965952741501.15165983638659.14965983638659.15166028155702.11966028155702.14366028155702.14566037852624.12366149329551.25 66357861087.1506653728088.144 66701037743.1296748444989.124 6748444989.149 6748444989.151 6758013062.118 692741842.150  7021785682.150 7563807307.123 7780899791.149 7795003580.149 7882758244.154 8179223683.148 8179223683.150 8346267669.123 8601557106.117 917434854.150  9196977948.127 9457190248.154 9522874812.149 9632634738.117 9666466205.150 00000=00J00W00n01201701C01H01M01N01O01P01Q01^01k02802e02m03103503;03S03g04;04A04I04J04K04L04R04S04Y04g04l05105?05@05A05B05C06V07507907?07C07F07K07Y08F08T09A09E09I09Q09W09]09c0:10:90;<0;?0;B0;P0;T0;U0;V0;c0<00<=0<C0<K0<L0<O0<T0<Y0<g0<h0<i0>:0?I0@a0B<0BB0BC0BG0BK0BL0BM0C:0C;0C<0DQ0DT0DW0DX0Dh0Dm0E@0ED0EH0EP0F=0FE0FH0FI0FL0FM0G^0I70I80I90I:0I?0IM0IN0IQ0J>0JB0JF0JG0JH0JI0JJ0JR0JW0Je0Jm0K;0K<0KA0KI0KO0K]0L=0L>0L?0LG0LJ0LM0LU0LY0Lg0M50MC0MK0MP0MT0MU0MV0MZ0M^0Ml0N00N80NK0O80O@0OH0OM0OQ0OU0OV0OW0Od0P10P>0PB0PF0PJ0PN0PO0PU0P^0Pg0Po0Q40QT0QY0Q^0Qb0Qf0S>0SD0SE0SM0SQ0SU0SY0S]0Sk0T10T?0TC0TG0TH0TI0TJ0TX0T]0T^0T_0T`0Tn0U<0U@0UT0Uh0Ui0Uj0V20V30V80V90V:0VH0VI0VJ0VP0V^0V_0Vm0Vn0W<0WH0WU0Wb0Wo0X70X80X90XN0Xc0Xk0Y30Y`0Yf0Yg0Yk0Z30Z40Za0Zn0[;0[H0[P0[^0[f0\30\@0\M0\Q0\U0\Y0\a0\i0\l0\m0]00]10]20]W0]]0]m0]n0^<0^@0^D0^M0^U0^]0^b0^g0_:0_;0_@0_A0_B0_o0`50`60`:0`>0`L0`M0a:0aH0aV0a[0ai0ao0b70b?0b@0bA0bG0bO0bU0bV0b^0bm0d30d90d:0d;0dC0dD0dE0dK0dL0dP0dT0df0dn0do0e40e<0eD0eJ0eR0eV0eZ0eh0ei0f50f;0fI0fV0fc0g00g=0gJ0gW0g_0gm0h:0hG0hT0hU0hV0he0i40iC0j00jD0jE0jP0jU0jb0jo0k<0k=0kK0kY0ki0kj0l00l40l50l60l?0lG0lH0lI0lO0lU0l]0lmS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO1N4UBHI2K43HspS2K4S3CX1S4CEIL2LO2T1S3LSJS3LSJSSSSS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S3LSJ2T0S2LOS2LOS4ABLOS4CEIL2LO3CX13Hsp3LSJ2T1S4CEIL2LO1N4UBHI3HspS4CEIL2LO1N4UBHI3HspS4ABLOS3LSJ2T0SSSS4ABLOSS4ABLOS3HUB4ABLO3RZRS3LSJS3LSJS3HUB4ABLO3RZRSSSSS4CEIL2LO1N3HUB4ABLO4UBHI3LSJ2T12NS3RZR3RZE3RLR3RSR3RSM3NSR4NSZ24SM165SMALL2RZ2DX1HS4CEIL2LO1N3HUB4UBHI3RZR3RZE2RZS2LOS4ABLOS2K4S1NS3LSJS3HUB4ABLO3RZRS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S3HUB4ABLO3RZRS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S2LOS2LOS3LSJ2T0S4CEILS4CEILS4CEILS3HUB4ABLO3RZRS3LSJ2T0S3HUB4ABLO3LSJ2NS3RZR3RZE3RLR3RSR3RSM3NSR3C164NSZ24SM165SMALL2K32DXS1NS1NS3HUB4ABLO3RZRS2T1SSS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4ABLOS3LSJ2T0SS1NS3LSJS3LSJS3HUB4ABLO3RZRSSS4CEIL2LO4ABLO3LSJ2T12NS3RZR3RZE3RLR3RSR3RSM3NSR4NSZ24SM165SMALL3Hsp1H1N3HUB4UBHIS4CEIL2LO4ABLO4UBHI3LSJ2NS3RZR3RZE3RLR3RSR3RSM3NSR3C164NSZ24SM165SMALL1H3HUB2T1S4CEIL2LO1N3HUB4ABLO4UBHI3LSJ2NS3RZR3RZE3RLR3RSR3RSM3NSR3C164NSZ24SM165SMALL2K33Hsp1H2T1S4CEIL2LO1N3HUB4ABLO4UBHI3LSJ2NS3RZR3RZE3RLR3RSR3RSM3NSR3C164NSZ24SM165SMALL2K32K43Hsp1H2T1S4ABLOSS2LOS2LOSSS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2SSS4CEIL2LO1N3HUB4ABLO4UBHI4AB163LSJ2T12NS3RZR3RZE3RLR3RSR3RSM3NSR4NSZ24SM165SMALL2DX1HS1NS1NSS4CEIL2LO2T13C16S3NSRS1N2NS3RZR3RSR4NSZ2S2LOS2LOS3LSJ2T0S4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S3LSJ2T0S1NSS1NSS4CEIL2LO1N3HUB4ABLO4UBHI3LSJ2T12NS3RZR3RZE3RLR3RSR3RSM3C164NSZ25SMALL2K02K32DX1HS4CEIL2LO1N3HUB4ABLO4UBHI4AB163LSJ2T12NS3RZR3RZE3RLR3RSR3RSM3C164NSZ25SMALL2K02K32K42DX1HSSSS3LSJS3HUB4ABLO3RZRSS1NS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S2LOS2LOFFFSS3LSJ2T0S3B1MS3HUB4ABLO3RZRS3LSJ2T0S3HUB4ABLO3RZRSS3C16S3LSJ2T0S4ABLOS3HUB4ABLO3RZRS1N3HUB4ABLO4UBHI2NS3RZR3RSR3NSRSSS3LSJ2T0S1NS1NS3LSJ2T0S2T1S3HUB4ABLO3RZRS3HUB4ABLO3RZRS3HUB4ABLO3RZRS3LSJ2T0S3LSJS2HBSSS2LOS2LOS3HUB4ABLO3RZRS2HBS3LSJ2T0S4CEIL2LO1N4UBHI2K4S4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S3LSJ2T0S3LSJ2T0S3LSJS2LOS2LOSSS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS2LOS2LOS2LOS2HBSS4ABLOS3LSJ3C16S3LSJ3C16S3LSJ2T0S3LSJS1N3HUB4ABLO4UBHI2NS3RZR3RSR3NSRS3NSRS3NSRS2LOS2LOS4CEIL2LO1N3HUB4ABLO4UBHI4AB163LSJ2T12NS3RZR3RZE3RLR3RSR3RSM3NSR4NSZ24SM165SMALL2K02DX1HS4ABLOSS3LSJ2T0S2HBS2T1S2T1S2HBS3HUB4ABLO3RZRS4ABLOS3HUB4ABLO3RZRS2LOS2LOSSSS3HUB4ABLO3RZRS3LSJFFFS3HUB4ABLO3RZRS3HUB4ABLO3RZRS2K4S4CEIL2LO1N4UBHI3HspS4CEIL2LO1N4UBHI3HspSSS3LSJ2T0SS3LSJSSS3HUB4ABLO3RZRSSS4ABLOS4CEIL2LO4UBHISS3HUB4ABLO3RZRSS3HUB4ABLO3RZRS4CEIL2LO2T1S4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS3LSJ2T0SFS1N3HUB4ABLO4UBHI3RZRS1N3HUB4ABLO4UBHI3RZRS2T13C16S3LSJ2T0S4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S2T11HSS2T1S4UBHI1HFS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS3LSJ2T0S3HUB4ABLO3RZRS3LSJ2T0S4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS2LOS2LOS2HBS3LSJ2T0S3LSJ2T0S1NSS1NSSS4CEIL2LO1N3HUB2T12NS3RZR3RSR3NSR3C16S4ABLOS4CEIL2LO1N4UBHISS3HUB4ABLO3RZRS2LOS2LOS3LSJ3C16S3LSJ2T0S3LSJ2T0S3CX0S3C16S4CEIL2LO1N4UBHI2K4SS3HspSSS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S4ABLOSS2LOS2LOS3HUB4ABLO3RZRSS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S3HUB4ABLO3RZRS3HUB4ABLO3RZRS3B1MS3HUB4ABLO3RZRS4ABLOS3LSJ2T0S3LSJ2T0SSS4ABLOS3LSJ2T0S4ABLOSS3NSR2K0S3HUB3RZE2K32RZS3HUB4ABLO3LSJ2NS3RZR3RZE3RLR3RSR3RSM3NSR3C164NSZ24SM165SMALL2K32K42DXS4ABLOSSS3LSJ2T0SSS4ABLOFS2LOS2LOS1N2NS3RZR3RSR3NSRS3LSJ2T0SS3LSJS3LSJ2T0S3LSJ2T0S4ABLOS3LSJ2T0S2LOS2LOS3HUB4ABLO3RZRSS4CEIL2LO2T1S4ABLOS3HUB4ABLO3RZRS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS3LSJ2T0S3HUB4ABLO3RZRS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspSSS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S3RZM3RSM1H2H02H42H9SS4CEIL4UBHIS3LSJS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspSS3HUB4ABLO3RZRS3HUB4ABLO3RZRS4CEIL2LO2T13C16SS4ABLOS2K4SSS3LSJ3C16S3LSJ2T0SSS4ABLOS4ABLOS3LSJ2T0S4CEIL2LO1N4UBHI".
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
assert (LH' : 16 < rz_size n -> rw_cells bsegs mm AB [C8 j1; C8 j2]) end.
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
assert (UF : rw_cells bsegs mm UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat fl) ++ skipn (Z.to_nat fl) uj)]) end.
{ replace (Z.to_nat n) with (Z.to_nat fl + Z.to_nat (n - fl))%nat by (subst fl; lia).
apply cb_app2; [exact UF1|]. rewrite Z2Nat.id by (subst fl; lia). exact UJ2. }
clear UF1 UJ2.
step. callp lsan_disabled_spec; [exact TP | exact LS1 | exact LS2 |].
lstep. zstep. zstep. zstep. zstep. step.
sstep. step. step.
unbox LH'.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (LH : 16 < rz_size n -> rw_cells bsegs mm AB [C8 j1; C8 j2]) end.
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
