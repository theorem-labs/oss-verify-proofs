(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode Arr InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg AProto ABase.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AKit AKit2 ABytes AModelFacts APrimFacts F_memsetZ F_aunwind F_aalloc_s F_aalloc3 F_acache3 F_aclass2.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma stats_class_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (X size : Z),
  a0 = Z_to_bv 64 X -> 0 <= X -> X + 112 < 2^64 ->
  24 <= size <= 65536 -> size mod 8 = 0 ->
  rng_aimg RNG ->
  evtF asegs RNG (fun ms' => exists a2' a3' a4' a5' a6',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (X + 112)) (Z_to_bv 64 (class_id size)) a2' a3' a4' a5' a6' a7 s2 (Z_to_bv 64 size) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x318bc) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 size) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x317c8) fc None m (seg_rom asegs)).
Proof.
  intros until size. intros -> X0 X1 SZ M8 RIMG.
  Local Ltac2 Set LiaHints.tbl := fun () => "0050>16021673688.4823689357298.4134834872776.4835243812325.5565106454549.4800000400800?00C00GS2K1S2SZS2SZ2K1S2SZS2SZ".
pose proof (class_facts size ltac:(lia)) as CF. cbv zeta in CF. destruct CF as (C1 & CS1 & CS2 & CS3 & CSM & CBG).
  step. zstep.                                                   (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1.                               (* [comment removed for export] *)
  - eapply evtF_mono; [eapply (classblock2_spec RNG); [lia | exact M8 | exact RIMG] |].
    cbv beta. intros ms' P. destruct P as (a2' & a3' & a4' & a5' & a6' & ->). do 5 eexists. reflexivity.
  - zstep. zstep. rewrite <- (CSM ltac:(lia)). step.            (* [comment removed for export] *)
    apply evtF_done. do 5 eexists. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma fill_len_spec : forall RNG ra sp gp tp t0 t1 t2 s0 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n : Z),
  0 <= n < 2^40 ->
  rng_aimg RNG ->
  evtF asegs RNG (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 (Z_to_bv 64 4096) (Z_to_bv 64 (Z.min n 4096)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x318f4) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 (Z_to_bv 64 4096) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x318e8) fc None m (seg_rom asegs)).
Proof.
  intros until n. intros N RIMG.
  step. step. Local Ltac2 Set LiaHints.tbl := fun () => "0030>2210563924.38 40904327378.3861927706159.38000003006009S1KS1KS1N".
if_cases K; zify_cond K.                           (* [comment removed for export] *)
  - replace (Z.min n 4096) with n by lia. apply evtF_done. reflexivity.
  - step. replace (Z.min n 4096) with 4096 by lia. apply evtF_done. reflexivity.   (* [comment removed for export] *)
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp + -128)
     [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v;
      C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
  (* [comment removed for export] *)
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m 0xa06e0 [C1 (Z_to_bv 8 1)] -> rw_cells asegs m 0xa06e4 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 (al_ctx L))] ->
  rw_cells asegs m (al_ctx L + 152) [C8 (Z_to_bv 64 t)] ->
  0 < al_ctx L -> al_ctx L + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m 0x9e6a4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells asegs m 0x98e28 [C8 (Z_to_bv 64 0x1329a8); C8 (Z_to_bv 64 0x9e678); C8 (Z_to_bv 64 0xa0e78);
                             C8 (Z_to_bv 64 0xa1b68); C8 (Z_to_bv 64 0xa1b70); C8 (Z_to_bv 64 0xa1b60)] ->
  rw_cells asegs m 0x98e58 [C8 (Z_to_bv 64 0x9acc0)] ->
  rw_cells asegs m 0x9acb8 [C8 (Z_to_bv 64 0x92164); C8 (Z_to_bv 64 0x92568)] ->
  rw_cells asegs m 0x99a90 [C8 (Z_to_bv 64 0x10)] -> rw_cells asegs m 0x5d3e20 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m 0x132940 [C8 (Z_to_bv 64 0)] ->
  (* [comment removed for export] *)
  rw_cells asegs m UB [CB (Z.to_nat n) uj] ->
  rw_cells asegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1m); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)] ->
  0 <= b1m < 256 -> 0 < id < 2^31 ->
  (16 < rz_size n -> rw_cells asegs m AB [C8 j1; C8 j2]) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG t 4096 ->
  rng RNG (UB - 16) (n + 16) -> rng RNG AB 16 ->
  evtF asegs RNG (allocD_postG sp gp tp F fc n t AB UB lo b1m id ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v uj m)
    (MS (mkR raX (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
              (Z_to_bv 64 1) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 UB) (Z_to_bv 64 (UB + -16)) s6x
              (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 (UB + n)) (Z_to_bv 64 t) (Z_to_bv 64 1)
              t3 t4 t5 t6)
        F (Z_to_bv 64 0x31778) fc None m (seg_rom asegs)).
Proof.
  intros until t6.
  intros ST CEIL LO MI TP N PRIM HUB ABLO UBHI AB16 HC DJT FR STATS LSJ TI TK T88 TSD CT CX0 CX1 T0 T1
         FLG GOT GOT80 REAL LS1 LS2 HK UJ HDR B1M IDR LH RIMG RSTK RCTX RT RU RAB. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, ATP88, ATSD in *.
  pose proof (prim_facts n N PRIM) as (NS & RZR & RZE & RZM & RLR & RSR & RSM & NSR).
  pose proof (prim_class_facts n c N PRIM HC) as (C16 & NSZ2 & SM16 & SMALL & MC2).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168); (UB - 16, UB + n); (AB, AB + 16)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  box DJT. box LH.
  snapshot [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168)]%Z MUs WMs.
  box UJ. box HDR.
  step. Local Ltac2 Set LiaHints.tbl := fun () => "05_0?10167497279.15110397311164.14910456434697.1541047820382.116 10587903613.11710640816421.11810640816421.11910911084698.14111077664131.14911077664131.1511162083375.148 1162083375.150 11801586693.12411801586693.14911801586693.15111956477810.11712341586989.11712406238321.15013086827028.13013118011600.1171324746171.152 13329794408.15414208485765.11714208485765.11814484648690.11714684412918.13414817767632.1231503082802.152 15043033658.1181533820803.149 1533820803.151 15517843049.4  15588165249.12515588165249.14215813913903.13115845511538.11715969700978.11816263107213.14916482458097.14116622434386.15016703780397.11816866801769.12317487950275.14417658312259.14417776320431.14817776320431.15017986879152.11617986879152.14017986879152.14218260229182.1411838634856.154 18392534760.1541898977476.142 19123199200.15119125296361.15419155925874.11719241987666.1501937063194.116 19591727510.12020010950973.12420010950973.14920010950973.15120880379370.1502150086885.150 21597125182.1412172922258.149 21924557829.11721924557829.11822675801219.15022675801219.15222700267513.12522700267513.14622700267513.15022700267513.15222737361138.11723586406368.12024411702716.14924435358672.12324559885231.14824559885231.15024566790608.12324885861438.14124904914272.11724924589988.13025029166211.14925029166211.15125065190167.12425071629079.14125071629079.15025080282415.11725080282415.12325676588393.11825787632170.12525878270254.15125878270255.14826310013116.14926494647592.14126494647592.14926494647592.15026494647592.15426496924968.14226496924968.14426649897404.14926775167848.15426868428163.14826868428163.15026879533652.12926879533652.13027188338533.12527408782894.14927408782894.15127576757255.12427576757255.14927576757255.15128014704080.12328176765800.15428335534850.12528738030430.14128941393650.11729782367974.12329811175882.1233017725367.154 30475885500.14930507153671.14030518562691.14830518562691.15030719730331.12630719730331.14130750431683.14431042920131.14431218985776.11731665118403.14431748732880.12333333358812.12833558212378.15033765134616.14033765134616.14233890036527.14833890036527.15034170950174.14134357674738.11734509983550.14134601944178.11735148913011.15435895327997.12435895327997.14935895327997.15135933558651.13136033352946.11736115622446.14936115622446.15136254216601.15236254216601.15536268652402.11736911535464.15437179231090.11737386977061.11637386977061.14037386977061.14237585159586.14937763307450.15337774388668.1493789875267.144 38212704797.12338212704797.12438769580476.1493894281273.118 39146469490.11839203822524.14939407463154.14139779905342.14139932046344.11739938772490.13140091925676.14740091925676.14940226033084.14940326235777.12440462318706.11840830974416.12341422282358.11842389998958.15442445826608.11742445826608.11842831019478.15042967766376.15443186039794.11743472444776.15443493603410.15043987951406.14943987951406.15143995329413.14944158664835.15044158664835.15244225934142.14144227402430.14144311304733.11844484923210.12444484923210.14944484923210.15144610219890.11744767421808.14944824048191.14944824048191.15144833359747.14944833359747.15145288596498.12645354402162.11745451326843.13345944259164.11845962238104.12946162087634.15046187576784.12346742050768.12347089684979.14447089684979.14547154292033.12347353497150.1414738246770.117 47406429554.11747557849085.1174798910125.117 48348884739.1444881215427.144 48841878642.11849294572020.1194936038867.145 49433673850.14149433673979.14049696399402.12349793197630.14150077211645.12450077211645.14950077211645.15150092199005.118502630133.136  50457931440.11750461111123.12650470234962.15050750500979.11851548755826.11751678667180.14751678667180.1495173701827.144 51816630506.14151902411762.1175234660466.117 52567164907.14152567164907.14952567164907.15052567164907.15452575291859.11752575291859.12352586760667.14952682867945.14152987902756.11952994560594.1505300105810.150 53767577775.14853767577775.15053810878302.13554124535740.14954761860978.11754969794426.11655338958788.13655460634391.14956170256219.11856172410654.13956172415395.14156426686290.1505684463747.132 56952260048.12356993309444.14156993309444.14357196545107.12657751108064.14857945953128.15458147165938.11758331630915.14458343875516.14958655119491.14958655119491.15259276314076.12559314873579.11859314873579.14259314873579.1435932235838.141 59681117426.11759743357778.15059784840306.11859907387523.15059907387523.15259961997718.14160634079619.14860634079619.15060976774461.12460976774461.14960976774461.15161587499216.12361694112329.14561917199020.14761917199020.14961939782288.13162947240400.12362976134100.12962976134102.1326313882541.117 6313882541.118 6319832469.118 63235321900.14763235321900.14963297025046.14463297025046.14663478620285.12463478620285.14963478620285.15163670697722.14863745434493.11764227055474.11764349369458.11864560625362.15064666605650.15064794176872.15464862446845.12464862446845.14964862446845.15165016030589.12465016030589.14965016030589.15165188488701.12465188488701.14965188488701.15165683728114.11765797088788.12665983638659.14965983638659.15166028155702.11966028155702.14366028155702.14566357861087.1506653728088.144 66701037743.1296698781810.117 6718686952.154 6758013062.118 6955981502.141 6967372938.141 7349490435.144 7518407421.124 7518407421.149 7518407421.151 7563807307.123 7780899791.149 7848643581.124 7848643581.149 7848643581.151 7882758244.154 8179223683.148 8179223683.150 8346267669.123 8610795133.124 8610795133.149 8610795133.151 8664102002.118 880821490.117  917434854.150  9196977948.127 9666466205.150 00000G00M00Q00V00b00g00l00m00n00o01301701O01c02702?02G02H02I02J02K02Q02V02[02c02d03Q03R03S03T03U03^05105P05T05\05d05h05k06906>06k07907G07K07O07U07[07a07o08508;09>09A09D09L09Z09^09_09l0:90:F0:G0:H0:V0:Y0:^0:c0:d0:e0<60=E0>]0@80@@0@A0@G0A40A80A<0Ai0B70B80B90B:0B;0CP0CS0CV0CW0Cg0Cl0D?0DC0DG0DM0DP0DQ0DT0DU0Ef0G?0GE0GK0GL0GM0GN0GS0GV0GZ0G^0G_0G`0Ga0HN0HT0HU0HZ0Hb0Hc0Hh0Hn0I40IT0IU0IV0IY0I\0Ij0J80J<0JJ0K70K<0K@0KA0KB0KF0KJ0KN0KV0Kd0Kl0L?0LL0LY0Lf0Lk0M30M70M;0M<0M=0ME0MK0MS0MW0M[0M_0Mc0Md0Mj0N80NA0NJ0NP0NU0N]0Nc0OC0OQ0OV0O[0O_0Oc0Oi0QA0QI0R60R70R;0R?0RC0RG0RM0RU0R[0Ri0Rm0S10S20S30S40SB0SP0SU0SV0SW0SX0S`0Sd0T80TL0TM0TN0TO0TW0T\0T]0T^0Tl0UY0VF0VT0VU0VV0Vd0Vl0W40W@0WH0WV0Wd0Wl0Wm0Wn0XC0XX0X`0Xn0Y;0YH0YU0Y[0Y\0Y`0Yh0Z60Z70Z?0ZC0ZG0ZU0ZY0Za0Zi0Zl0Zm0[00[10[20[W0[]0[m0[n0\<0\J0\N0\R0\[0\a0\i0\n0]30]F0]K0]L0]M0][0]\0^I0^M0^Q0^R0^W0^]0^e0_30_90_:0_;0_<0_D0_S0`Y0`g0`o0a=0aE0aF0aG0aH0aI0aJ0aW0ad0b10b^0b_0bc0bg0c90cf0cg0cl0d40d<0dD0dH0dL0dM0dN0d[0dh0e50e60eB0eJ0eR0e`0en0f40fA0fN0f[0fh0g50gB0gO0g\0gi0h10h?0h@0hA0hP0h_0hn0ho0i:0i?0iG0iM0iN0i\0i]0ik0j80jE0jR0jb0jc0k00k=0kJ0kN0kO0kP0kY0kf0l30l@0lH0lP0lQ0lR0lbS4CEIL2LO1N4UBHI2K43HspS4ABLOS2K4S3CX1S4CEIL2LO2T1S3LSJS3LSJSSSS2LOS2LOS4CEIL2LO3CX13Hsp3LSJ2T1S4CEIL2LO1N4UBHI3HspS4CEIL2LO1N4UBHI3HspS3LSJ2T0S3LSJ2T0SSSSS4ABLOS3LSJS3LSJS3LSJ2T0SS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2SSSSS3RZM3RSMS4CEIL2LO1N3HUB4ABLO4UBHI3LSJ2T12NS3RZR3RZE3RLR3RSR3RSM3NSR4NSZ24SM165SMALL2RZ2DX1HS4CEIL2LO1N3HUB4UBHI3RZR3RZE2RZS2LOS3LSJ2T0S3LSJ2T0S2K4S1NS3HUB4ABLO3RZRS3LSJS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S3HUB4ABLO3RZRS3HUB4ABLO3RZRS2LOS2LOS4CEILS4CEILS4CEILS3HUB4ABLO3RZRS4ABLOS4ABLOS3HUB4ABLO3LSJ2NS3RZR3RZE3RLR3RSR3RSM3NSR3C164NSZ24SM165SMALL2K32DXS1NS1NS3LSJ2T0S3HUB4ABLO3RZRS2T1SS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspSSS3HUB4ABLO3RZRS1NS3LSJS3LSJSSS4CEIL2LO4ABLO3LSJ2T12NS3RZR3RZE3RLR3RSR3RSM3NSR4NSZ24SM165SMALL3Hsp1H1N3HUB4UBHIS4CEIL2LO4ABLO4UBHI3LSJ2NS3RZR3RZE3RLR3RSR3RSM3NSR3C164NSZ24SM165SMALL1H3HUB2T1S4CEIL2LO1N3HUB4ABLO4UBHI3LSJ2NS3RZR3RZE3RLR3RSR3RSM3NSR3C164NSZ24SM165SMALL2K33Hsp1H2T1S4CEIL2LO1N3HUB4ABLO4UBHI3LSJ2NS3RZR3RZE3RLR3RSR3RSM3NSR3C164NSZ24SM165SMALL2K32K43Hsp1H2T1S3LSJ2T0SS4ABLOS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S2LOS2LOS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S3HUB4ABLO3RZRSSSSS4CEIL2LO1N3HUB4ABLO4UBHI4AB163LSJ2T12NS3RZR3RZE3RLR3RSR3RSM3NSR4NSZ24SM165SMALL2DX1HS1NS1NSS4CEIL2LO2T13C16S3NSRS1N2NS3RZR3RSR4NSZ2S2LOS2LOS4ABLOS1NSS1NSS4CEIL2LO1N3HUB4ABLO4UBHI3LSJ2T12NS3RZR3RZE3RLR3RSR3RSM3C164NSZ25SMALL2K02K32DX1HS4CEIL2LO1N3HUB4ABLO4UBHI4AB163LSJ2T12NS3RZR3RZE3RLR3RSR3RSM3C164NSZ25SMALL2K02K32K42DX1HS4ABLOS4ABLOSSSS3LSJS1NS2LOS2LOFFFS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S4ABLOSS3B1MS3LSJ2T0SS3C16S4ABLOS4ABLOS1N3HUB4ABLO4UBHI2NS3RZR3RSR3NSRSSS1NS1NS3HUB4ABLO3RZRS3HUB4ABLO3RZRS2T1S3HUB4ABLO3RZRS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S3LSJS2HBSSS2LOS2LOS2HBS3LSJ2T0S3HUB4ABLO3RZRS3LSJ2T0S4CEIL2LO1N4UBHI2K4S4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS3LSJS3LSJ2T0S2LOS2LOSSS3LSJ2T0S4ABLOS3LSJ2T0S2LOS2LOS2LOS2HBSS4ABLOS3HUB4ABLO3RZRS3LSJ3C16S3LSJ3C16S4ABLOS3LSJS3LSJ2T0S4ABLOS1N3HUB4ABLO4UBHI2NS3RZR3RSR3NSRS3HUB4ABLO3RZRS3NSRS3NSRS2LOS2LOS4ABLOS4CEIL2LO1N3HUB4ABLO4UBHI4AB163LSJ2T12NS3RZR3RZE3RLR3RSR3RSM3NSR4NSZ24SM165SMALL2K02DX1HS3LSJ2T0S4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2SS2HBS2T1S2T1S2HBS4ABLOS3LSJ2T0S4ABLOS3HUB4ABLO3RZRS2LOS2LOSSSS3HUB4ABLO3RZRS3HUB4ABLO3RZRS3LSJFFFS3LSJ2T0S2K4S4CEIL2LO1N4UBHI3HspS4CEIL2LO1N4UBHI3HspSSSS3LSJ2T0S3LSJSSS3HUB4ABLO3RZRS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S4CEIL2LO4UBHISSS3HUB4ABLO3RZRS3LSJ2T0S3LSJ2T0S4CEIL2LO2T1S3LSJ2T0S3HUB4ABLO3RZRS3HUB4ABLO3RZRS3LSJ2T0SFS1N3HUB4ABLO4UBHI3RZRS1N3HUB4ABLO4UBHI3RZRS2T13C16S3HUB4ABLO3RZRS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS2T11HSS2T1S4UBHI1HS3HUB4ABLO3RZRFS3LSJ2T0S2LOS2LOS3HUB4ABLO3RZRS2HBS3LSJ2T0S3LSJ2T0S1NSS1NSSS4CEIL2LO1N3HUB2T12NS3RZR3RSR3NSR3C16S4ABLOS4CEIL2LO1N4UBHISS3HUB4ABLO3RZRS3HUB4ABLO3RZRS2LOS2LOS3LSJ3C16S4ABLOS3LSJ2T0S3CX0S3C16S4CEIL2LO1N4UBHI2K4S3HspSSS3HUB4ABLO3RZRSS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S2LOS2LOSS3B1MS4ABLOS3LSJ2T0S3HUB4ABLO3RZRS4ABLOSSSS3NSR2K0S3HUB3RZE2K32RZS3HUB4ABLO3LSJ2NS3RZR3RZE3RLR3RSR3RSM3NSR3C164NSZ24SM165SMALL2K32K42DXS3HUB4ABLO3RZRS3LSJ2T0S3HUB4ABLO3RZRS3LSJ2T0SSSSSS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2FS2LOS2LOS1N2NS3RZR3RSR3NSRS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2SS3LSJS3LSJ2T0S3LSJ2T0S3LSJ2T0S2LOS2LOSSS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspSS4CEIL2LO2T1S3LSJ2T0S3LSJ2T0S3HUB4ABLO3RZRS3HUB4ABLO3RZRS4ABLOS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS3LSJ2T0S3HUB4ABLO3RZRSSS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HSS4CEIL4UBHIS3LSJS3LSJ2T0S4ABLOSS3HUB4ABLO3RZRSS3HUB4ABLO3RZRS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO2T13C16SS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS2K4SSS3LSJ3C16S4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS3LSJ2T0S3LSJ2T0SSS4CEIL2LO1N4UBHI".
call_sp (thread_stats_spec RNG (al_ctx L) t lo).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => first [ match goal with HH__ : stk _ _ _ _ |- _ => eexact HH__ end | eassumption ]
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- rw_cells _ _ (_ + 152) _ => exact CT
       | |- rw_cells _ _ _ _ => assumption
       end.
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- rng _ _ _ => solve_rng
       | |- _ => unfold AIMG_HI; lia
       end.
  rename POST into ST.
  aload STATS 2 (t + 2800 + 16).                                 (* [comment removed for export] *)
  aload STATS 0 (t + 2800 + 0).                                  (* [comment removed for export] *)
  aload STATS 1 (t + 2800 + 8).                                  (* [comment removed for export] *)
  zstep. zstep. step. zstep. zstep. zstep.                       (* [comment removed for export] *)
  astore STATS 0.                                                (* [comment removed for export] *)
  astore STATS 1.                                                (* [comment removed for export] *)
  astore STATS 2.                                                (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. 2: { exfalso. lia. }          (* [comment removed for export] *)
  (* [comment removed for export] *)
  eapply evtF_cut; [eapply (stats_class_spec RNG); [reflexivity | lia | lia | lia | clear -NS RSM RZM; rewrite NS; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia | exact RIMG] |].
  cbv beta. intros msS PS. destruct PS as (a2s & a3s & a4s & a5s & a6s & ->). rewrite HC.
  zstep. zstep.                                                  (* [comment removed for export] *)
  rewrite (Z.shiftl_mul_pow2 c 3) by lia. change (2^3) with 8.
  aload STATS (14 + c) (t + 2912 + c * 8).                       (* [comment removed for export] *)
  zstep.                                                         (* [comment removed for export] *)
  astore STATS (14 + c).                                         (* [comment removed for export] *)
  (* [comment removed for export] *)
  carry UJ MUs WMs ltac:(with_box DJT lia). carry HDR MUs WMs ltac:(with_box DJT lia).
  unbox LH.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (LH' : 16 < rz_size n -> rw_cells asegs mm AB [C8 j1; C8 j2]) end.
  { intros RZ. specialize (LH RZ). box LH. carry LH MUs WMs ltac:(with_box DJT lia). exact LH. }
  clear LH MUs WMs. box LH'. box STATS.
  snapshot [(UB - 16, UB + n); (AB, AB + 16); (bv_unsigned sp + -128 - 32, bv_unsigned sp + -128)]%Z MUc WMc.
  snapshot [(UB - 16, UB + n); (bv_unsigned sp + -128 - 32, bv_unsigned sp + -128)]%Z MUl WMl.
  (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  step. step. lstep. step. if_lit.                               (* [comment removed for export] *)
  eapply evtF_cut; [eapply (fill_len_spec RNG); [lia | exact RIMG] |]. cbv beta. intros msF ->.   (* [comment removed for export] *)
  set (fl := Z.min n 4096) in *.
  destruct (cb_take _ _ n fl uj UJ ltac:(subst fl; lia)) as [UJ1 UJ2]. clear UJ.
  step. step. step. lstep. step.                                 (* [comment removed for export] *)
  step. call (memset_specZ RNG UB 0xbe fl (firstn (Z.to_nat fl) uj)).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ _ [CB _ _] => exact UJ1
       | |- rng _ _ _ => eapply rng_sub'; [exact RU|]; subst fl; lia
       | |- _ => subst fl; atop_facts; lia
       end.
  rename POST into UF1.
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (UF : rw_cells asegs mm UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat fl) ++ skipn (Z.to_nat fl) uj)]) end.
  { replace (Z.to_nat n) with (Z.to_nat fl + Z.to_nat (n - fl))%nat by (subst fl; lia).
    apply cb_app2; [exact UF1|]. rewrite Z2Nat.id by (subst fl; lia). exact UJ2. }
  clear UF1 UJ2.
  (* [comment removed for export] *)
  step. callp lsan_disabled_spec; [exact TP | exact LS1 | exact LS2 |].
  lstep. zstep. zstep. zstep. zstep. step.                       (* [comment removed for export] *)
  sstep. step. step.                                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  unbox LH'.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (LH : 16 < rz_size n -> rw_cells asegs mm AB [C8 j1; C8 j2]) end.
  { intros RZ. specialize (LH' RZ). box LH'. carry LH' MUl WMl ltac:(lia). exact LH'. }
  clear LH' MUl WMl.
  pose proof (rz_size_cases n) as RZC. box RZC.
  step. if_cases K3; zify_cond K3.                               (* [comment removed for export] *)
  - (* [comment removed for export] *)
    clear LH.
    step. step. step. call_sp (run_malloc_hooks_spec RNG).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
         | |- stk _ _ _ _ => first [ match goal with HH__ : stk _ _ _ _ |- _ => eexact HH__ end | eassumption ]
         | |- mem_inv _ _ => assumption
         | |- rw_cells _ _ _ _ => exact HK
         | |- rng _ _ _ => solve_rng
         | |- _ => atop_facts; lia
         end.
    rename POST into ST.
    do 16 step.                                                  (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    carry STATS MUc WMc ltac:(with_box DJT lia).
    apply evtF_done. unfold allocD_post. do 16 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
    split; [exact STATS|]. split; [rewrite !upd_length; exact LSJ|]. split; [exact UF|]. split; [exact HDR|].
    intros RZ. exfalso. lia.
  - (* [comment removed for export] *)
    specialize (LH ltac:(with_box RZC lia)).
    zstep. step. if_cases K4; zify_cond K4. { exfalso. with_box RZC lia. }   (* [comment removed for export] *)
    step. step.                                                  (* [comment removed for export] *)
    step. step. step.                                            (* [comment removed for export] *)
    step. step. step. call_sp (run_malloc_hooks_spec RNG).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
         | |- stk _ _ _ _ => first [ match goal with HH__ : stk _ _ _ _ |- _ => eexact HH__ end | eassumption ]
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
(* [comment removed for export] *)
