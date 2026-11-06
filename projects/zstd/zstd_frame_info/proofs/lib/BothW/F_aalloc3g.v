(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode Arr InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg AProto ABase.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import AKit AKit2 ABytes AModelFacts APrimFacts F_memsetZ F_aunwind F_aalloc_s F_aalloc3 F_acache3 F_aclass2.
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma stats_class_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (X size : Z),
  a0 = Z_to_bv 64 X -> 0 <= X -> X + 112 < 2^64 ->
  24 <= size <= 65536 -> size mod 8 = 0 ->
  rng_aimg RNG ->
  evtF bsegs RNG (fun ms' => exists a2' a3' a4' a5' a6',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (X + 112)) (Z_to_bv 64 (class_id size)) a2' a3' a4' a5' a6' a7 s2 (Z_to_bv 64 size) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x318c0) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 size) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x317cc) fc None m (seg_rom bsegs)).
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
  evtF bsegs RNG (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 (Z_to_bv 64 4096) (Z_to_bv 64 (Z.min n 4096)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x318f8) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 (Z_to_bv 64 4096) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x318ec) fc None m (seg_rom bsegs)).
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
  (* [comment removed for export] *)
  rw_cells bsegs m (bv_unsigned sp + -128)
     [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v;
      C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
  (* [comment removed for export] *)
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->
  rw_cells bsegs m 0xa08a0 [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m 0xa08a4 [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells bsegs m ATSD [C8 (Z_to_bv 64 (al_ctx L))] ->
  rw_cells bsegs m (al_ctx L + 152) [C8 (Z_to_bv 64 t)] ->
  0 < al_ctx L -> al_ctx L + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->
  (* [comment removed for export] *)
  rw_cells bsegs m 0x9e864 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells bsegs m 0x99000 [C8 (Z_to_bv 64 0x132b68); C8 (Z_to_bv 64 0x9e838); C8 (Z_to_bv 64 0xa1038);
                             C8 (Z_to_bv 64 0xa1d28); C8 (Z_to_bv 64 0xa1d30); C8 (Z_to_bv 64 0xa1d20)] ->
  rw_cells bsegs m 0x99030 [C8 (Z_to_bv 64 0x9ae98)] ->
  rw_cells bsegs m 0x9ae90 [C8 (Z_to_bv 64 0x92340); C8 (Z_to_bv 64 0x92744)] ->
  rw_cells bsegs m 0x99c68 [C8 (Z_to_bv 64 0x10)] -> rw_cells bsegs m 0x5d3fe0 [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x132b00 [C8 (Z_to_bv 64 0)] ->
  (* [comment removed for export] *)
  rw_cells bsegs m UB [CB (Z.to_nat n) uj] ->
  rw_cells bsegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1m); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)] ->
  0 <= b1m < 256 -> 0 < id < 2^31 ->
  (16 < rz_size n -> rw_cells bsegs m AB [C8 j1; C8 j2]) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG t 4096 ->
  rng RNG (UB - 16) (n + 16) -> rng RNG AB 16 ->
  evtF bsegs RNG (allocD_postG sp gp tp F fc n t AB UB lo b1m id ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v uj m)
    (MS (mkR raX (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
              (Z_to_bv 64 1) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 UB) (Z_to_bv 64 (UB + -16)) s6x
              (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 (UB + n)) (Z_to_bv 64 t) (Z_to_bv 64 1)
              t3 t4 t5 t6)
        F (Z_to_bv 64 0x3177c) fc None m (seg_rom bsegs)).
Proof.
  intros until t6.
  intros ST CEIL LO MI TP N PRIM HUB ABLO UBHI AB16 HC DJT FR STATS LSJ TI TK T88 TSD CT CX0 CX1 T0 T1
         FLG GOT GOT80 REAL LS1 LS2 HK UJ HDR B1M IDR LH RIMG RSTK RCTX RT RU RAB. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, ATP88, ATSD in *.
  pose proof (prim_facts n N PRIM) as (NS & RZR & RZE & RZM & RLR & RSR & RSM & NSR).
  pose proof (prim_class_facts n c N PRIM HC) as (C16 & NSZ2 & SM16 & SMALL & MC2).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168); (UB - 16, UB + n); (AB, AB + 16)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  (* [comment removed for export] *)
  box DJT. box LH.
  snapshot [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168)]%Z MUs WMs.
  box UJ. box HDR.
  step. Local Ltac2 Set LiaHints.tbl := fun () => "05_0?10167497279.15110456434697.1541047820382.116 10495213693.12410495213693.14910495213693.15110587903613.11710640816421.11810640816421.11910911084698.14111077664131.14911077664131.15111480366910.1411162083375.148 1162083375.150 11801586693.12411801586693.14911801586693.15112115366258.11712270362430.14112341586989.11712406238321.15013086827028.13013118011600.1171324746171.152 14208485765.11714208485765.1181503082802.152 15043033658.1181533820803.149 1533820803.151 15517843049.4  15578933362.11715588165249.12515588165249.14215696294482.15015813913903.13115928523971.14416263107213.14916482458097.14116584980432.12316703780397.11816866801769.12317018810435.14417086648040.15417776320431.14817776320431.15017986879152.11617986879152.14017986879152.14218365406014.1411898977476.142 19123199200.15119125296361.1541921160771.144 1937063194.116 20501024188.14920670856254.14120880379370.15021006689010.1172150086885.150 2172922258.149 21905638514.11821924557829.11721924557829.1182267550066.117 22675801219.15022675801219.15222700267513.12522700267513.14622700267513.15022700267513.15223100797699.14423257131773.12423257131773.14923257131773.15123586406368.12023724173437.12423724173437.14923724173437.15123815175120.12324346898045.12424346898045.14924346898045.15124492166258.11724559885231.14824559885231.15024904914272.11724924589988.13025029166211.14925029166211.15125065190167.12425071629079.14125071629079.15025080282415.11725080282415.12325676588393.11825765569650.11825787632170.12525845764028.1492587562448.123 25878270254.15125878270255.14826494647592.14126494647592.14926494647592.15026494647592.15426496924968.14226496924968.14426868428163.14826868428163.15026879533652.12926879533652.13027188338533.12527408782894.14927408782894.15127576757255.12427576757255.14927576757255.15128335534850.12528738030430.14128862602600.15429331998019.14429782367974.12329811175882.1233017725367.154 30240964978.11730507153671.14030518562691.14830518562691.15030719730331.12630719730331.14130990269904.12331040122832.12331218985776.11731361185874.15032094984894.14132096683286.12032346218354.11732598658622.14132927862979.14433333358812.12833525351794.11733558212378.15033753433366.14133765134616.14033765134616.14233890036527.14833890036527.15033953449074.11734170950174.14135148913011.15435376310130.1173542266866.117 35568762877.12435568762877.14935568762877.15135933558651.13136053481878.14436053481878.14636115622446.14936115622446.15136147869116.14936254216601.15236254216601.15536509566416.12336822615400.15437018278974.14137369278270.14137386977061.11637386977061.14037386977061.14237585159586.14937728604022.13437763307450.15338212704797.12338212704797.1243894281273.118 39025939570.11739119749992.15439295571186.11739407463154.14139833992144.12339932046344.11739938772490.13140091925676.14740091925676.14940326235777.12440730098802.11841279206130.11741422282358.11842078147432.15442389998958.15442445826608.11742445826608.1184272226621.124 4272226621.149 4272226621.151 42770728680.15442831019478.15042886996547.14443360954812.14943609253714.15043987951406.14943987951406.15143995329413.14944158664835.15044158664835.15244288370640.12344311304733.11844398238652.14944484923210.12444484923210.14944484923210.15144551111922.11744702716274.11744767421808.14944824048191.14944824048191.15144833359747.14944833359747.15145238050109.12445238050109.14945238050109.15145288596498.12645451326843.13345464690442.14145944259164.11845962238104.12946486534595.1444664361714.117 46696544720.12347037521138.11747089684979.14447089684979.14547154292033.12347557849085.11747917573052.1494798910125.117 48577040082.15049123722493.12449123722493.14949123722493.15149294572020.1194936038867.145 49433673850.14149433673979.14049696399402.12350092199005.118502630133.136  50457931440.11750461111123.12650575413842.15050750500979.11851678667180.14751678667180.14951787079037.12451787079037.14951787079037.15151816630506.14152436596434.15052567164907.14152567164907.14952567164907.15052567164907.15452575291859.11752575291859.12352586760667.14952666310076.14952682867945.14152766889320.15452987902756.11953735224680.15453767577775.14853767577775.15053810878302.13554011733842.15054876624626.11754969794426.11655338958788.13655460634391.14956170256219.11856172410654.13956172415395.14156358351678.14156630081394.11756772200515.1445684463747.132 56993309444.14156993309444.14357196545107.12657750928210.15057751108064.14857864589251.14458241330536.15458439414514.11758536729426.15058655119491.14958655119491.152587405170.117  59276314076.12559314873579.11859314873579.14259314873579.14359475428926.14159783765746.11759907387523.15059907387523.15260129843048.15460406065266.11860634079619.14860634079619.15061694112329.14561917199020.14761917199020.14961939782288.13162251784274.15062368215228.14962602652498.15062976134100.12962976134102.1326313882541.117 6313882541.118 63188354408.1546319832469.118 63235321900.14763235321900.14963551429310.14163581023218.11763670697722.14863745434493.11764083382019.14465346271869.12465346271869.14965346271869.15165526597052.14965797088788.12665811741693.12465811741693.14965811741693.15165983638659.14965983638659.15166028155702.11966028155702.14366028155702.14566357861087.1506653728088.144 66701037743.1296671039602.118 67138201714.1186758013062.118 68021603186.11768043442620.1497563807307.123 7780899791.149 7882758244.154 8028629200.123 8179223683.148 8179223683.150 8346267669.123 8943415504.123 9087230140.149 917434854.150  9196977948.127 9494050930.118 9666466205.150 9674157938.117 00000G00K00P00]00j01701C01H01M01N01O01P01^01b01f02>02R02f02n03<03D03E03F03G03H03M03R03S03T03U03V03_03g05:05Y05g05k06906=06@06m07207_07m08308708;08A08G08M08[09^09a09d0:20:60:<0:J0:K0:S0:T0:W0:_0:d0:i0;10;20;30<D0=S0>k0@F0@T0@a0@n0A;0A<0AI0AV0Ac0BP0B]0Bj0C70C?0CC0CG0CH0CI0CJ0CK0D`0Dc0Df0Dg0E70E<0ED0EW0E]0FJ0FN0FR0FU0FV0FY0FZ0Gk0ID0IE0IF0IG0IL0IO0IS0IW0IX0IY0IZ0I[0I`0If0J40J50J:0J@0JH0Jh0Ji0Jj0Jm0K00K]0LJ0LN0L\0Lj0Lk0M30MA0MO0MT0M\0M`0Ma0Mb0Mc0Mg0Mk0N30N70NJ0NR0NZ0Ng0O40OA0OF0OG0OH0OL0OP0OV0OW0OX0PE0PK0PY0Pg0Pk0Po0Q30Q70Q80Q90QB0QK0QP0QX0Q^0Qf0RF0S30S80S=0SA0SE0T]0Te0Tm0Tn0U40U80U<0U@0UM0UZ0Ug0Um0V10V?0VE0VS0VW0V[0V\0V]0V^0WK0WP0WV0WW0WX0WY0Wa0Wi0Wm0XA0XU0XV0XW0Xd0Y10Y>0Y?0YD0YE0YF0YG0YU0Y]0ZJ0ZR0Z`0Za0Zb0Zn0[40[<0[J0[W0[d0\10\20\30\H0\]0\e0\k0\l0]00]80]F0]G0]K0]O0]\0]i0^60^:0^H0^K0^L0^O0^P0^Q0_60_<0_B0_R0_X0_Y0__0_c0_g0`00`>0`F0`K0`P0`c0`h0`i0`j0a80a@0aN0aO0aS0aW0aX0af0ak0b90b?0bG0bU0bV0bW0b_0b`0bh0c70d=0dK0dS0dT0dU0d[0dc0dd0de0df0dj0dn0e@0eN0eT0eb0ec0eh0f00f80f>0fF0fJ0fN0f\0fd0fe0g10g?0gL0gY0gf0gl0h:0hG0hT0ha0hb0hc0i20iA0iP0iQ0i\0ia0ii0j10j20j:0j@0jP0jQ0jU0kB0kC0kD0kM0l:0l@0lA0lB0lJ0lZ0lbS4CEIL2LO1N4UBHI2K43HspS2K4S3CX1S4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO2T1S3LSJS3LSJSSSS3HUB4ABLO3RZRS2LOS2LOS4CEIL2LO3CX13Hsp3LSJ2T1S4CEIL2LO1N4UBHI3HspS4CEIL2LO1N4UBHI3HspS3LSJ2T0S3HUB4ABLO3RZRS3LSJ2T0SSSSS3LSJS3LSJSSSSS3RZM3RSMS3LSJ2T0S4CEIL2LO1N3HUB4ABLO4UBHI3LSJ2T12NS3RZR3RZE3RLR3RSR3RSM3NSR4NSZ24SM165SMALL2RZ2DX1HS4CEIL2LO1N3HUB4UBHI3RZR3RZE2RZS3HUB4ABLO3RZRS2LOS3HUB4ABLO3RZRS2K4S1NS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S3LSJS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S3HUB4ABLO3RZRS4ABLOS2LOS2LOS4CEILS4CEILS4CEILS3HUB4ABLO3RZRS3HUB4ABLO3LSJ2NS3RZR3RZE3RLR3RSR3RSM3NSR3C164NSZ24SM165SMALL2K32DXS1NS1NS3HUB4ABLO3RZRS2T1S4ABLOS3HUB4ABLO3RZRSS3LSJ2T0SS1NS3LSJ2T0S3LSJS3LSJS3LSJ2T0SSS4CEIL2LO4ABLO3LSJ2T12NS3RZR3RZE3RLR3RSR3RSM3NSR4NSZ24SM165SMALL3Hsp1H1N3HUB4UBHIS4CEIL2LO4ABLO4UBHI3LSJ2NS3RZR3RZE3RLR3RSR3RSM3NSR3C164NSZ24SM165SMALL1H3HUB2T1S4CEIL2LO1N3HUB4ABLO4UBHI3LSJ2NS3RZR3RZE3RLR3RSR3RSM3NSR3C164NSZ24SM165SMALL2K33Hsp1H2T1S4CEIL2LO1N3HUB4ABLO4UBHI3LSJ2NS3RZR3RZE3RLR3RSR3RSM3NSR3C164NSZ24SM165SMALL2K32K43Hsp1H2T1S3HUB4ABLO3RZRS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspSS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS3LSJ2T0S2LOS2LOSSSSS4CEIL2LO1N3HUB4ABLO4UBHI4AB163LSJ2T12NS3RZR3RZE3RLR3RSR3RSM3NSR4NSZ24SM165SMALL2DX1HS1NS1NSS4CEIL2LO2T13C16S3NSRS3LSJ2T0S1N2NS3RZR3RSR4NSZ2S4ABLOS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S2LOS2LOS1NSS1NSS4CEIL2LO1N3HUB4ABLO4UBHI3LSJ2T12NS3RZR3RZE3RLR3RSR3RSM3C164NSZ25SMALL2K02K32DX1HS4CEIL2LO1N3HUB4ABLO4UBHI4AB163LSJ2T12NS3RZR3RZE3RLR3RSR3RSM3C164NSZ25SMALL2K02K32K42DX1HSSSS3LSJS1NS2LOS2LOFFFSS3B1MS4ABLOS3HUB4ABLO3RZRSS3C16S4ABLOS3LSJ2T0S1N3HUB4ABLO4UBHI2NS3RZR3RSR3NSRSSS1NS1NS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S2T1S3HUB4ABLO3RZRS3HUB4ABLO3RZRSS3LSJ2T0S3HUB4ABLO3RZRS3HUB4ABLO3RZRS3LSJS3LSJ2T0S2HBSSSS2LOS2LOS3LSJ2T0S2HBS4CEIL2LO1N4UBHI2K4S3LSJ2T0S3LSJ2T0S4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS3LSJSSS2LOS2LOS4ABLOSSS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S4ABLOS3HUB4ABLO3RZRS3HUB4ABLO3RZRS2LOS2LOS2LOS2HBSSS3LSJ3C16S3LSJ3C16S3LSJS3LSJ2T0S4ABLOS3LSJ2T0S1N3HUB4ABLO4UBHI2NS3RZR3RSR3NSRS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S3NSRS3NSRS2LOS2LOS4CEIL2LO1N3HUB4ABLO4UBHI4AB163LSJ2T12NS3RZR3RZE3RLR3RSR3RSM3NSR4NSZ24SM165SMALL2K02DX1HS3LSJ2T0S3LSJ2T0SS4ABLOS2HBS2T1S2T1S4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4ABLOS2HBS3HUB4ABLO3RZRS4ABLOS3HUB4ABLO3RZRS2LOS2LOSSSS4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S3LSJS4ABLOFFFS3LSJ2T0S3LSJ2T0S2K4S4CEIL2LO1N4UBHI3HspS4CEIL2LO1N4UBHI3HspSSS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspSS3LSJSSSS3HUB4ABLO3RZRS3LSJ2T0S4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S3LSJ2T0S4CEIL2LO4UBHISSS4CEIL2LO2T1S4ABLOS3LSJ2T0S3HUB4ABLO3RZRS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspSFS1N3HUB4ABLO4UBHI3RZRS1N3HUB4ABLO4UBHI3RZRS2T13C16S2T11HSS2T1S4UBHI1HS3HUB4ABLO3RZRFS2LOS2LOS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS2HBS3HUB4ABLO3RZRS1NSS1NSSS4CEIL2LO1N3HUB2T12NS3RZR3RSR3NSR3C16S4ABLOS4ABLOS4CEIL2LO1N4UBHIS4ABLOSS4ABLOS2LOS2LOS3LSJ3C16S3HUB4ABLO3RZRS3LSJ2T0S3CX0S3C16S4CEIL2LO1N4UBHI2K4S3HspSSS3HUB4ABLO3RZRS3LSJ2T0S3HUB4ABLO3RZRSS2LOS2LOSS3HUB4ABLO3RZRS3B1MS3HUB4ABLO3RZRS4ABLOS3LSJ2T0S3HUB4ABLO3RZRSSS3LSJ2T0SS3NSR2K0S3HUB3RZE2K32RZS3HUB4ABLO3LSJ2NS3RZR3RZE3RLR3RSR3RSM3NSR3C164NSZ24SM165SMALL2K32K42DXS3HUB4ABLO3RZRS3LSJ2T0SSS4ABLOS3LSJ2T0SSFS2LOS2LOS1N2NS3RZR3RSR3NSRS3HUB4ABLO3RZRS4ABLOS3HUB4ABLO3RZRSS3LSJS3LSJ2T0S3LSJ2T0S4ABLOS3LSJ2T0S2LOS2LOS3HUB4ABLO3RZRS3LSJ2T0SS4CEIL2LO2T1S3HUB4ABLO3RZRS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4ABLOS3HUB4ABLO3RZRS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspSSS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HSS4CEIL4UBHIS3LSJS3LSJ2T0S3LSJ2T0SS3LSJ2T0S4ABLOS4CEIL2LO2T13C16SS2K4S4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2SSS3LSJ3C16S4ABLO3LSJ2T02NS3RZR3RZE3RLR3RSR3NSR3C164NSZ2S4ABLOSSS3LSJ2T0S4CEIL2LO1N4UBHIS3LSJ2T0".
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
    assert (LH' : 16 < rz_size n -> rw_cells bsegs mm AB [C8 j1; C8 j2]) end.
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
    assert (UF : rw_cells bsegs mm UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat fl) ++ skipn (Z.to_nat fl) uj)]) end.
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
    assert (LH : 16 < rz_size n -> rw_cells bsegs mm AB [C8 j1; C8 j2]) end.
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
