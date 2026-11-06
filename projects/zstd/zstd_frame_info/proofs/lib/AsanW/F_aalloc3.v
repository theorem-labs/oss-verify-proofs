(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg AProto ABase.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AKit AKit2 AModelFacts F_memsetZ F_aunwind F_aalloc_s.
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
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma thread_stats_spec : forall RNG (ctx t lo : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 32 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  rw_cells asegs m 0xa06e0 [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xa06e4 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] ->
  rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  0 < ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 ->
  evtF asegs RNG (fun ms' => exists a1' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (t + 2800)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5a758) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST CEIL LO MI TP TI TK T88 TSD CT CX0 CX1 T0 T1 RIMG RSTK RCTX. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, ATP88, ATSD in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  Local Ltac2 Set LiaHints.tbl := fun () => "00R0>11801586693.7111805467289.6712429510126.6715449178405.6317986879152.6320433961190.6122284289799.7122700267513.7226730776422.6331399144472.6332600174396.673525607222.66 36635088338.6437317216127.673830242848.64 40653749742.6743061431595.5944484923210.7145221239098.6749425192486.6350077211645.7152198366190.6753089759638.6654164510851.6754164510851.7056172315833.6258057019758.6759314873579.6560976774461.7163235321901.6663235321901.6964862446845.7167081926311.678610795133.71 00000A00B00K00O00U00V00W00^00c00d00h01701>01K01O01X01\01]01b01g02402=02>02?02@02A02J02Q02^02b02f03303403AS3Hsp4CEIL2LO3CX1SS4CEIL2LOS2LOS4CEILSFS3Hsp1HS3CX1SS2HBS4CEIL2LO3SPR1HS2T02T1S4CEIL2LO3CX1S2LOS4CEIL2LOS2LOFS3SPRS3CX0S4CEIL2LO3HspS4CEIL2LOSSSSS4CEIL2LOS2T02K0S4CEIL2LO3HspS2LOS2LOS4CEIL2LO3HspSS4CEIL2LO3Hsp".
carve_frame 16%nat ST.
  do 2 step.                                                     (* [comment removed for export] *)
  step. call_sp (get_current_thread_spec RNG).
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
       | |- _ => atop_facts; lia
       end.
  rename POST into ST.
  step. if_cases K0; zify_cond K0. { exfalso. lia. }             (* [comment removed for export] *)
  zstep. zstep.                                                  (* [comment removed for export] *)
  do 3 step.                                                     (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). finish.
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
Definition allocD_post (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (n t AB UB lo b1m id : Z) (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' sj',
    ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
             F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168); (UB - 16, UB + n); (AB, AB + 16)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells asegs m' UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat n))]
    /\ rw_cells asegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 (Z.lor (Z.land b1m 243) 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
    /\ (16 < rz_size n -> rw_cells asegs m' AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]).

#[using="Type"] Lemma allocD_spec : forall (L : alayout) RNG sp gp tp (F : bvmap 5 word) fc (m : amem)
    (n t c AB UB lo b0 b1m id S : Z) (sj : list word) (uj : list byte) (j1 j2 : word)
    (fr0 : list byte) (raX ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6x t3 t4 t5 t6 : word),
  stk asegs m lo (bv_unsigned sp + -128) -> ATOP <= lo -> lo <= bv_unsigned sp + -128 - 32 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  1 <= n <= 448 ->
  UB = AB + rz_size n -> 0x10007fff8000 <= AB -> UB + n <= ATOP -> AB mod 16 = 0 ->
  Z.shiftr (needed_size n + 31) 5 = c ->
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
  evtF asegs RNG (allocD_post sp gp tp F fc n t AB UB lo b1m id ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v m)
    (MS (mkR raX (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
              (Z_to_bv 64 1) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 UB) (Z_to_bv 64 (UB + -16)) s6x
              (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 (UB + n)) (Z_to_bv 64 t) (Z_to_bv 64 1)
              t3 t4 t5 t6)
        F (Z_to_bv 64 0x31778) fc None m (seg_rom asegs)).
Proof.
  intros until t6.
  intros ST CEIL LO MI TP N HUB ABLO UBHI AB16 HC DJT FR STATS LSJ TI TK T88 TSD CT CX0 CX1 T0 T1
         FLG GOT GOT80 REAL LS1 LS2 HK UJ HDR B1M IDR LH RIMG RSTK RCTX RT RU RAB. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, ATP88, ATSD in *.
  pose proof (small_facts n N) as (PRIM & NS & RZR & RZE & RSR & RSM & NSR).
  Local Ltac2 Set LiaHints.tbl := fun () => "05^0?10167497279.14110397311164.13910456434697.1441047820382.110 10587903613.11110640816421.11210640816421.11310911084698.13111077664131.13911077664131.1411162083375.138 1162083375.140 11801586693.11811801586693.13911801586693.14111956477810.11112341586989.11112406238321.14013086827028.12413118011600.1111324746171.142 13329794408.14414208485765.11114208485765.11214484648690.11114684412918.12314817767632.1131503082802.142 15043033658.1121533820803.139 1533820803.141 15588165249.11515588165249.13215813913903.12115845511538.11115969700978.11216263107213.13916622434386.14016703780397.11216866801769.11317487950275.13317658312259.13317776320431.13817776320431.14017986879152.11017986879152.13017986879152.13218260229182.1311838634856.144 18392534760.1441898977476.132 19123199200.14119125296361.14419155925874.11119241987666.1401937063194.110 19591727510.11420010950973.11820010950973.13920010950973.14120880379370.1402150086885.140 21597125182.1312172922258.139 21924557829.11121924557829.11222675801219.14022675801219.14222700267513.11922700267513.13522700267513.14022700267513.14222737361138.11123586406368.1142431248216.116 24411702716.13924435358672.11324559885231.13824559885231.14024566790608.11324885861438.13124904914272.11124924589988.12425029166211.13925029166211.14125065190167.11425071629079.13125071629079.14025080282415.11125080282415.11325878270254.14125878270255.13826310013116.13926494647592.13126494647592.13926494647592.14026494647592.14426496924968.13226496924968.13426649897404.13926775167848.14426868428163.13826868428163.14026879533652.12326879533652.12427408782894.13927408782894.14127576757255.11827576757255.13927576757255.14128014704080.11328176765800.14428335534850.11528738030430.13128941393650.11129311285958.10429782367974.11329811175882.1133017725367.144 30475885500.13930507153671.13030518562691.13830518562691.14030750431683.13331042920131.13331218985776.11131665118403.13331748732880.11333333358812.12233558212378.14033765134616.13033765134616.13233890036527.13833890036527.14034170950174.13134357674738.11134509983550.13134601944178.11135148913011.14435895327997.11835895327997.13935895327997.14135933558651.12536033352946.11136115622446.13936115622446.14136254216601.14236254216601.14536268652402.11136911535464.14437179231090.1113722934160.116 37386977061.11037386977061.13037386977061.13237585159586.13937763307450.14337774388668.1393789875267.133 38212704797.11338212704797.11438769580476.1393894281273.112 39146469490.11239203822524.13939407463154.13139779905342.13139932046344.11139932046731.11239938772490.12540091925676.13740091925676.13940226033084.13940326235777.11440462318706.11240830974416.11341422282358.11242389998958.14442445826608.11142445826608.11242735827499.12142831019478.14042967766376.14443186039794.11143472444776.14443493603410.14043987951406.13943987951406.14143995329413.13944158664835.14044158664835.14244225934142.13144227402430.13144311304733.11244484923210.11844484923210.13944484923210.14144610219890.11144767421808.13944824048191.13944824048191.14144833359747.13944833359747.14145354402162.11145416504009.13445451326843.12745944259164.11245962238104.12346162087634.14046187576784.11346742050768.11347089684979.13347089684979.13447154292033.11347353497150.1314738246770.111 47406429554.11147557849085.1114798910125.111 48348884739.1334881215427.133 48841878642.11249294572020.11349433673850.13149433673979.13049696399402.11349793197630.13150077211645.11850077211645.13950077211645.141502630133.126  50457931440.11150470234962.14050750500979.11251548755826.11151678667180.13751678667180.1395173701827.133 51816630506.13151902411762.1115234660466.111 52567164907.13152567164907.13952567164907.14052567164907.14452575291859.11152575291859.11352586760667.13952682867945.13152956645176.11552987902756.11352994560594.1405300105810.140 53767577775.13853767577775.14053810878302.12554124535740.13954761860978.11154969794426.11055336861632.12055460634391.13956170256219.11256172410654.12956172415395.13156426686290.1405684463747.122 56952260048.11356993309444.13156993309444.13357196545107.11657751108064.13857945953128.14458147165938.11158331630915.13358343875516.13958655119491.13958655119491.14259276314076.11559314873579.11259314873579.11359314873579.11659314873579.13259314873579.1335932235838.131 59681117426.11159743357778.14059784840306.11259907387523.14059907387523.14259961997718.13060634079619.13860634079619.14060976774461.11860976774461.13960976774461.14161587499216.11361694112329.13461917199020.13761917199020.13961929812368.11561939782288.12562947240400.11362976134100.12362976134102.1266313882541.111 6313882541.112 63235321900.13763235321900.13963297025046.13463297025046.13663478620285.11863478620285.13963478620285.14163670697722.13863745434493.11164227055474.11164349369458.11264560625362.14064666605650.14064794176872.14464862446845.11864862446845.13964862446845.14165016030589.11865016030589.13965016030589.14165188488701.11865188488701.13965188488701.14165683728114.11165797088788.11665983638659.13965983638659.14166028155702.11366028155702.13366028155702.13566357861087.1406653728088.133 66701037743.1236698781810.111 67100501013.1036718686952.144 6758013062.112 6955981502.131 6967372938.131 7349490435.133 7518407421.118 7518407421.139 7518407421.141 7563807307.113 7780899791.139 7848643581.118 7848643581.139 7848643581.141 7882758244.144 8179223683.138 8179223683.140 8346267669.113 8610795133.118 8610795133.139 8610795133.141 8664102002.112 880821490.111  917434854.140  9196977948.116 9666466205.140 00000G00M00Q00V00b00g00l00m00n00o01301701O01c02702?02G02H02I02J02K02Q02V02[02c02d03503603703803903m04L04P04X04`04d05205705H05V05d05h05l06206806>06L06R06X07007307607>07L07P07Q07^07k08808908:08H08K08P08U08V08W09I09P0:D0;40;<0;=0;@0;F0;W0;[0;_0<00<>0<?0<@0<A0<B0=30=60=90=:0=J0=N0=R0=X0=[0=\0=_0=`0>R0?<0?B0?H0?I0?J0?K0?P0?T0?X0?Y0?Z0?[0?l0@20@30@80@@0@A0@B0@G0@M0@S0A30A40A50AC0AQ0AU0Ac0B40B90B=0B>0B?0BC0BG0BK0BS0Ba0Bi0C<0CI0CV0Cc0Ch0D00D40D80D90D:0DB0DH0DP0DX0D\0D`0Dd0Dh0Di0Do0E=0EF0EO0EU0EZ0Eb0Eh0FH0FV0F[0F`0Fe0Fi0Fm0G30Gd0Gl0H=0H>0HB0HF0HJ0HO0HS0HY0Ha0Hg0I50I90I=0I>0I?0I@0IN0I\0Ia0Ib0Ic0Id0Il0J00JD0JX0JY0JZ0Jb0Jc0Jh0Ji0Jj0K80KI0KZ0Kh0Ki0Kj0L80L@0LH0LT0L\0Lj0M80M@0MA0MV0Mk0N30NA0NN0N[0Nh0Ni0Nm0O;0O<0OD0OH0OL0OZ0O^0Of0On0P10P20P50P60P70PG0PM0P]0P^0P_0Pm0Q;0Q?0QC0QL0QR0QZ0Q_0Qd0R70R<0R=0R>0RL0RM0R^0Rb0Rf0Rg0Rl0S20S:0SH0SN0SO0SP0SQ0SY0Sa0Sg0T60TQ0T_0Tg0U50U=0U>0U?0U@0UA0UB0UO0U\0Ui0V:0V;0V?0VC0VF0VI0VZ0V[0V`0Vh0W00W40W80W90W:0WG0WT0Wa0Wb0Wn0X60X>0XL0XZ0X`0Xm0Y:0YG0YT0Ya0Yn0Z;0ZH0ZU0Z]0Zk0Zl0Zm0[<0[K0[Z0[[0[f0[k0\30\T0\Z0\[0\i0\j0]80]E0]R0]_0]o0^00^=0^J0^W0^[0^\0^]0^f0_30_@0_M0_U0_]0_^0__0_oS4CEIL2LO1N4UBHI2K43HspS4ABLOS2K4S3CX1S4CEIL2LO2T1S3LSJS3LSJSSSS2LOS2LOS4CEIL2LO3CX13Hsp3LSJ2T1S4CEIL2LO1N4UBHI3HspS4CEIL2LO1N4UBHI3HspS3LSJ2T0S3LSJ2T0SSSSS4ABLOS3LSJS3LSJS3LSJ2T0SS4ABLO3LSJ2T03C16SSSSS4CEIL2LO1N3HUB4ABLO4UBHI3LSJ2T12NS3RZR3RSM3NSR2DX1HS4CEIL2LO1N3HUB4UBHI3RZR3RZE2RZS2LOS3LSJ2T0S3LSJ2T0S2K4S3HUB4ABLO3RZRS3LSJS4ABLO3LSJ2T03C16S3HUB4ABLO3RZRS3HUB4ABLO3RZRS2LOS2LOS4CEILS4CEILS4CEILS3HUB4ABLO3RZRS4ABLOS4ABLOS3HUB4ABLO3LSJ3RZE2K32DXS1NS1NS3LSJ2T0S3HUB4ABLO3RZRS2T1SS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspSSS3HUB4ABLO3RZRS1NS3LSJS3LSJSSS4CEIL2LO4ABLO3LSJ2T13RSR3RSM3Hsp1H1N3HUB4UBHI3RZRS3LSJ1HS4CEIL2LO1N3HUB4ABLO4UBHI3LSJ2NS3RSM3NSR2K33Hsp1H2T1S4CEIL2LO1N4ABLO4UBHI3LSJ3RSR3RSM2K32K43Hsp1H2T1S3LSJ2T0SS1NS4ABLOS4ABLO3LSJ2T03C16S2LOS2LOS4ABLO3LSJ2T03C16S3HUB4ABLO3RZRSSSSS4CEIL2LO1N3HUB4ABLO4UBHI3LSJ2T13RZR3RSR3RSM2DX1HS1NS1NSS4CEIL2LO2T13C16S2LOS2LOS4ABLOS1NSS1NSS4CEIL2LO1N3HUB4ABLO4UBHI3LSJ2T12NS3RSR2K12K32DX1HS4CEIL2LO1N3HUB4ABLO3LSJ2T13RZR2K32K42DX1HS4ABLOS4ABLOSSSS3LSJS2LOS2LOFFFS4ABLO3LSJ2T03C16S4ABLOSS3B1MS3LSJ2T0SSS3C16S4ABLOS4ABLOS1N3HUB4ABLO4UBHI2NS3RZR3RSR3NSRSSS3HUB4ABLO3RZRS3HUB4ABLO3RZRS2T1S3HUB4ABLO3RZRS4ABLO3LSJ2T03C16S3LSJS2HBSSS2LOS2LOS2HBS3LSJ2T0S3HUB4ABLO3RZRS3LSJ2T0S4CEIL2LO1N4UBHI2K4S4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS3LSJS3LSJ2T0S2LOS2LOSSS3LSJ2T0S4ABLOS3LSJ2T0S4UBHI1HS2LOS2LOS2LOS2HBSS4ABLOS3HUB4ABLO3RZRS3LSJ3C16S3LSJ3C16S4ABLOS3LSJS3LSJ2T0S4ABLOS1N3HUB4ABLO4UBHI2NS3RZR3RSR3NSRS3HUB4ABLO3RZRS3NSRS3NSRS3NSRS2LOS2LOS4ABLOS4CEIL2LO1N3HUB4ABLO4UBHI3LSJ2T13RZR3RSR3RSM2DX1HS3LSJ2T0S4ABLO3LSJ2T03C16SS2HBS2T1S2T1S3NSRS2HBS4ABLOS3LSJ2T0S4ABLOS3HUB4ABLO3RZRS2LOS2LOSSSS3HUB4ABLO3RZRS3HUB4ABLO3RZRS3LSJFFFS3LSJ2T0S2K4S4CEIL2LO1N4UBHI3HspS4CEIL2LO1N4UBHI3HspSSS3LSJ2T0FS3LSJSSS3HUB4ABLO3RZRS4ABLO3LSJ2T03C16S4ABLO3LSJ2T03C16S4CEIL2LO4UBHISSS3HUB4ABLO3RZRS3LSJ2T0S3LSJ2T0S4CEIL2LO2T1S3LSJ2T0S3HUB4ABLO3RZRS3HUB4ABLO3RZRS3LSJ2T0SS1N3HUB4ABLO4UBHI3RZRS1N3HUB4ABLO4UBHI3RZRS2T13C16S3HUB4ABLO3RZRS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspSS2T1S3HUB4ABLO3RZRFS3LSJ2T0S2LOS2LOS3HUB4ABLO3RZRS2HBS3LSJ2T0S3LSJ2T0S1NSS1NSSS4CEIL2LO2T13C16S4ABLOS4CEIL2LO1N4UBHISSS3HUB4ABLO3RZRS3HUB4ABLO3RZRS2LOS2LOS3LSJ3C16S4ABLOS3LSJ2T0S3CX0S3C16S4CEIL2LO1N4UBHI2K4S3HspSSS3HUB4ABLO3RZRSS4ABLO3LSJ2T03C16S2LOS2LOSS3B1MS4ABLOS3LSJ2T0S3HUB4ABLO3RZRS4ABLOSSSS3NSR2K0S3NSR2K1S1N2K2S3HUB3RZE2K32RZS3HUB4ABLO3LSJ3RZE2K32K42DXS3HUB4ABLO3RZRS3LSJ2T0S3HUB4ABLO3RZRS3LSJ2T0SSSSSS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4ABLO3LSJ2T03C16FS2LOS2LOS1NS1NS4ABLO3LSJ2T03C16SS3LSJS3LSJ2T0S3LSJ2T0S2LOS2LOSSS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspSS4CEIL2LO2T1S3LSJ2T0S3LSJ2T0S3HUB4ABLO3RZRS3HUB4ABLO3RZRS4ABLOS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS3LSJ2T0S3HUB4ABLO3RZRSSS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HSS4CEIL4UBHIS3LSJS3LSJ2T0S4ABLO3LSJ2NS3RZR3RZE3RSR3RSM3NSRS4ABLOSS3HUB4ABLO3RZRSS3HUB4ABLO3RZRS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO2T13C16SS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS2K4SSS3LSJ3C16S4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS3LSJ2T0S3LSJ2T0SSS4CEIL2LO1N4UBHI".
assert (C16 : 1 <= c <= 16) by (rewrite <- HC; rewrite Z.shiftr_div_pow2 by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168); (UB - 16, UB + n); (AB, AB + 16)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  box DJT. box LH.
  snapshot [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168)]%Z MUs WMs.
  box UJ. box HDR.
  step. call_sp (thread_stats_spec RNG (al_ctx L) t lo).
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
  step. zstep. step. if_cases K1; zify_cond K1. { exfalso. lia. }   (* [comment removed for export] *)
  zstep. zstep. rewrite HC. step.                                (* [comment removed for export] *)
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
  step. step. if_cases K2; zify_cond K2. 2: { exfalso. lia. }    (* [comment removed for export] *)
  step. step. step. lstep. step.                                 (* [comment removed for export] *)
  step. call (memset_specZ RNG UB 0xbe n uj).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ _ [CB _ _] => exact UJ
       | |- rng _ _ _ => solve_rng
       | |- _ => atop_facts; lia
       end.
  rename POST into UF.
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
  pose proof (rz_size_small_cases n N) as RZC. box RZC.
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
