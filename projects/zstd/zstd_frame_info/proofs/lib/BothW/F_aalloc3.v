(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg AProto ABase.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import AKit AKit2 AModelFacts F_memsetZ F_aunwind F_aalloc_s.
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
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 32 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  rw_cells bsegs m 0xa08a0 [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m 0xa08a4 [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] ->
  rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  0 < ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 ->
  evtF bsegs RNG (fun ms' => exists a1' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (t + 2800)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5a75c) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST CEIL LO MI TP TI TK T88 TSD CT CX0 CX1 T0 T1 RIMG RSTK RCTX. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, ATP88, ATSD in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  word_range sp SPR.
  Local Ltac2 Set LiaHints.tbl := fun () => "00R0>11801586693.7111805467289.6715449178405.6317986879152.6320433961190.6122284289799.7122700267513.7224346898045.7124559830510.6726730776422.6331399144472.6332600174396.673525607222.66 36635088338.6437317216127.6738238797294.673830242848.64 40059657198.6743061431595.5944484923210.7145221239098.6745238050109.7149123722493.7149425192486.6354164510851.6754164510851.7054316719638.6656172315833.6259314873579.6560471841134.6763235321901.6663235321901.6965811741693.7167081926311.6700000A00B00F00L00M00N00U00b00k01001101501D01K01X01a01e01n02202302802E02R02W02X02Y02Z02[02b02k02o03303@03AS3Hsp4CEIL2LO3CX1SS2LOS4CEILSFS3Hsp1HS4CEIL2LO3HspS4CEIL2LOS3CX1SS2HBS4CEIL2LO3SPR1HS2T02T1S4CEIL2LO3CX1S4CEIL2LOS2LOS4CEIL2LOS2LOFS3SPRS4CEIL2LO3HspS4CEIL2LO3HspS3CX0SSSSS2T02K0S4CEIL2LOS2LOS2LOS4CEIL2LO3HspS".
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
Definition allocD_post (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (n t AB UB lo b1m id : Z) (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' sj',
    ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
             F (ret_pc ra0) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168); (UB - 16, UB + n); (AB, AB + 16)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ u64arr bsegs m' (t + 2800) sj' /\ length sj' = 46%nat
    /\ rw_cells bsegs m' UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat n))]
    /\ rw_cells bsegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 (Z.lor (Z.land b1m 243) 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
    /\ (16 < rz_size n -> rw_cells bsegs m' AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))]).

#[using="Type"] Lemma allocD_spec : forall (L : alayout) RNG sp gp tp (F : bvmap 5 word) fc (m : amem)
    (n t c AB UB lo b0 b1m id S : Z) (sj : list word) (uj : list byte) (j1 j2 : word)
    (fr0 : list byte) (raX ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6x t3 t4 t5 t6 : word),
  stk bsegs m lo (bv_unsigned sp + -128) -> ATOP <= lo -> lo <= bv_unsigned sp + -128 - 32 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  1 <= n <= 448 ->
  UB = AB + rz_size n -> 0x10007fff8000 <= AB -> UB + n <= ATOP -> AB mod 16 = 0 ->
  Z.shiftr (needed_size n + 31) 5 = c ->
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
  evtF bsegs RNG (allocD_post sp gp tp F fc n t AB UB lo b1m id ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v m)
    (MS (mkR raX (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
              (Z_to_bv 64 1) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 UB) (Z_to_bv 64 (UB + -16)) s6x
              (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 (UB + n)) (Z_to_bv 64 t) (Z_to_bv 64 1)
              t3 t4 t5 t6)
        F (Z_to_bv 64 0x3177c) fc None m (seg_rom bsegs)).
Proof.
  intros until t6.
  intros ST CEIL LO MI TP N HUB ABLO UBHI AB16 HC DJT FR STATS LSJ TI TK T88 TSD CT CX0 CX1 T0 T1
         FLG GOT GOT80 REAL LS1 LS2 HK UJ HDR B1M IDR LH RIMG RSTK RCTX RT RU RAB. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, ATP88, ATSD in *.
  pose proof (small_facts n N) as (PRIM & NS & RZR & RZE & RSR & RSM & NSR).
  Local Ltac2 Set LiaHints.tbl := fun () => "05^0?10167497279.14110456434697.1441047820382.110 10495213693.11810495213693.13910495213693.14110587903613.11110640816421.11210640816421.11310911084698.13111077664131.13911077664131.14111480366910.1311162083375.138 1162083375.140 11801586693.11811801586693.13911801586693.14112115366258.11112270362430.13112341586989.11112406238321.14013086827028.12413118011600.1111324746171.142 14208485765.11114208485765.1121503082802.142 15043033658.1121533820803.139 1533820803.141 15578933362.11115588165249.11515588165249.13215696294482.14015813913903.12115928523971.13316263107213.13916584980432.11316703780397.11216866801769.11317018810435.13317086648040.14417776320431.13817776320431.14017986879152.11017986879152.13017986879152.13218365406014.1311898977476.132 19123199200.14119125296361.1441921160771.133 1937063194.110 20501024188.13920670856254.13120880379370.14021006689010.1112150086885.140 2172922258.139 21905638514.11221924557829.11121924557829.1122267550066.111 22675801219.14022675801219.14222700267513.11922700267513.13522700267513.14022700267513.14223100797699.13323257131773.11823257131773.13923257131773.14123586406368.11423724173437.11823724173437.13923724173437.14123815175120.1132431248216.116 24346898045.11824346898045.13924346898045.14124492166258.11124559885231.13824559885231.14024904914272.11124924589988.12425029166211.13925029166211.14125065190167.11425071629079.13125071629079.14025080282415.11125080282415.11325765569650.11225845764028.1392587562448.113 25878270254.14125878270255.13826494647592.13126494647592.13926494647592.14026494647592.14426496924968.13226496924968.13426868428163.13826868428163.14026879533652.12326879533652.12427408782894.13927408782894.14127576757255.11827576757255.13927576757255.14128335534850.11528738030430.13128862602600.14429311285958.10429331998019.13329782367974.11329811175882.1133017725367.144 30240964978.11130507153671.13030518562691.13830518562691.14030990269904.11331040122832.11331218985776.11131361185874.14032094984894.13132096683286.11432346218354.11132598658622.13132927862979.13333333358812.12233525351794.11133558212378.14033753433366.13033765134616.13033765134616.13233890036527.13833890036527.14033953449074.11134170950174.13135148913011.14435376310130.1113542266866.111 35568762877.11835568762877.13935568762877.14135933558651.12536053481878.13436053481878.13636115622446.13936115622446.14136147869116.13936254216601.14236254216601.14536509566416.11336822615400.14437018278974.1313722934160.116 37369278270.13137386977061.11037386977061.13037386977061.13237585159586.13937728604022.12337763307450.14338212704797.11338212704797.1143894281273.112 39025939570.11139119749992.14439295571186.11139407463154.13139833992144.11339932046344.11139932046731.11239938772490.12540091925676.13740091925676.13940326235777.11440730098802.11241279206130.11141422282358.11242078147432.14442389998958.14442445826608.11142445826608.1124272226621.118 4272226621.139 4272226621.141 42735827499.12142770728680.14442831019478.14042886996547.13343360954812.13943609253714.14043987951406.13943987951406.14143995329413.13944158664835.14044158664835.14244288370640.11344311304733.11244398238652.13944484923210.11844484923210.13944484923210.14144551111922.11144702716274.11144767421808.13944824048191.13944824048191.14144833359747.13944833359747.14145238050109.11845238050109.13945238050109.14145416504009.13445451326843.12745464690442.13145944259164.11245962238104.12346486534595.1334664361714.111 46696544720.11347037521138.11147089684979.13347089684979.13447154292033.11347557849085.11147917573052.1394798910125.111 48577040082.14049123722493.11849123722493.13949123722493.14149294572020.11349433673850.13149433673979.13049696399402.113502630133.126  50457931440.11150575413842.14050750500979.11251678667180.13751678667180.13951787079037.11851787079037.13951787079037.14151816630506.13152436596434.14052567164907.13152567164907.13952567164907.14052567164907.14452575291859.11152575291859.11352586760667.13952666310076.13952682867945.13152766889320.14452956645176.11552987902756.11353735224680.14453767577775.13853767577775.14053810878302.12554011733842.14054876624626.11154969794426.11055336861632.12055460634391.13956170256219.11256172410654.12956172415395.13156358351678.13156630081394.11156772200515.1335684463747.122 56993309444.13156993309444.13357196545107.11657750928210.14057751108064.13857864589251.13358241330536.14458439414514.11158536729426.14058655119491.13958655119491.142587405170.111  59276314076.11559314873579.11259314873579.11359314873579.11659314873579.13259314873579.13359475428926.13159783765746.11159907387523.14059907387523.14260129843048.14460406065266.11260634079619.13860634079619.14061694112329.13461917199020.13761917199020.13961929812368.11561939782288.12562251784274.14062368215228.13962602652498.14062976134100.12362976134102.1266313882541.111 6313882541.112 63188354408.14463235321900.13763235321900.13963551429310.13163581023218.11163670697722.13863745434493.11164083382019.13365346271869.11865346271869.13965346271869.14165526597052.13965797088788.11665811741693.11865811741693.13965811741693.14165983638659.13965983638659.14166028155702.11366028155702.13366028155702.13566357861087.1406653728088.133 66701037743.1236671039602.112 67100501013.10367138201714.1126758013062.112 68021603186.11168043442620.1397563807307.113 7780899791.139 7882758244.144 8028629200.113 8179223683.138 8179223683.140 8346267669.113 8943415504.113 9087230140.139 917434854.140  9196977948.116 9494050930.112 9666466205.140 9674157938.111 00000G00K00P00]00j01701C01H01M01N01O01P01^01b01f02>02R02f02n03<03D03E03F03G03H03M03R03S03T03U03V03^04R05105?05C05Q05U05f05k06<06J06P06T06X06^06d06j07807P07S07V07d07h07n08<08=08E08F08I08Q08V08[08c08d08e09W09^0:R0;B0;P0;]0;j0<70<80<E0<R0<_0=00=30=@0=M0=Z0=b0=f0=j0=k0=l0=m0=n0>_0>b0>e0>f0?60?>0?D0?U0?Y0?]0?`0?a0?d0?e0@W0AA0AB0AC0AD0AI0AM0AQ0AR0AS0AT0AU0AZ0A`0Aa0Ao0B00B50B;0BC0Bc0Bd0Be0C60CG0CK0CY0Cg0Ch0D00D>0DL0DQ0DY0D]0D^0D_0D`0Dd0Dh0E00E40EG0EO0EW0Ed0F10F>0FC0FD0FE0FI0FM0FS0FT0FU0Ff0Fl0G:0GB0GP0GT0GX0G\0G`0Ga0Gb0Gk0H40H90HA0HG0HO0Ho0I@0IE0IJ0IO0IS0IW0JH0JP0JX0JY0J_0Jc0Jg0Jk0K80KE0KR0KW0K]0Ka0Ko0L50LC0LG0LK0LL0LM0LN0L_0Ld0Lj0Lk0Ll0Lm0M50M=0MA0MU0Mi0Mj0Mk0N80NE0NR0NS0NX0NY0NZ0N[0Ni0O10OB0OJ0OX0OY0OZ0Of0Ol0P40PB0PO0P\0Pi0Pj0Q?0QT0Q\0Q]0Qa0Qo0R00R40R80RE0RR0R_0Rc0S10S40S50S80S90S:0SJ0SP0SV0Sf0Sl0Sm0Sn0T40T80T<0TE0TS0T[0T`0Te0U80U=0U>0U?0UM0UU0Uc0Ud0Uh0Ul0Um0V;0V@0VN0VT0V\0Vj0Vk0Vl0W40W50W=0WE0WK0WZ0X50XC0XK0XL0XM0XS0X[0X\0X]0X^0Xb0Xf0Xi0Xl0Y:0Y@0YN0YO0YT0Y\0Yd0Yj0Yn0Z20Z@0ZH0ZI0ZU0Zc0[00[=0[J0[P0[^0[k0\80\E0\F0\G0\V0\e0]40]50]@0]E0]M0]n0^60^70^?0^E0^U0^V0^Z0^k0^l0^m0_60_G0_M0_N0_O0_W0_g0_oS4CEIL2LO1N4UBHI2K43HspS2K4S3CX1S4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO2T1S3LSJS3LSJSSSS3HUB4ABLO3RZRS2LOS2LOS4CEIL2LO3CX13Hsp3LSJ2T1S4CEIL2LO1N4UBHI3HspS4CEIL2LO1N4UBHI3HspS3LSJ2T0S3HUB4ABLO3RZRS3LSJ2T0SSSSS3LSJS3LSJSSSSS3LSJ2T0S4CEIL2LO1N3HUB4ABLO4UBHI3LSJ2T12NS3RZR3RSM3NSR2DX1HS4CEIL2LO1N3HUB4UBHI3RZR3RZE2RZS3HUB4ABLO3RZRS2LOS3HUB4ABLO3RZRS2K4S4ABLO3LSJ2T03C16S3LSJS4ABLO3LSJ2T03C16S3HUB4ABLO3RZRS4ABLOS2LOS2LOS4CEILS4CEILS4CEILS3HUB4ABLO3RZRS3HUB4ABLO3LSJ3RZE2K32DXS1NS1NS3HUB4ABLO3RZRS2T1S4ABLOS3HUB4ABLO3RZRSS3LSJ2T0SS1NS3LSJ2T0S3LSJS3LSJS3LSJ2T0SSS4CEIL2LO4ABLO3LSJ2T13RSR3RSM3Hsp1H1N3HUB4UBHI3RZRS3LSJ1HS4CEIL2LO1N3HUB4ABLO4UBHI3LSJ2NS3RSM3NSR2K33Hsp1H2T1S4CEIL2LO1N4ABLO4UBHI3LSJ3RSR3RSM2K32K43Hsp1H2T1S3HUB4ABLO3RZRS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspSS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4ABLO3LSJ2T03C16S1NS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS3LSJ2T0S2LOS2LOSSSSS4CEIL2LO1N3HUB4ABLO4UBHI3LSJ2T13RZR3RSR3RSM2DX1HS1NS1NSS4CEIL2LO2T13C16S3LSJ2T0S4ABLOS4ABLO3LSJ2T03C16S2LOS2LOS1NSS1NSS4CEIL2LO1N3HUB4ABLO4UBHI3LSJ2T12NS3RSR2K12K32DX1HS4CEIL2LO1N3HUB4ABLO3LSJ2T13RZR2K32K42DX1HSSSS3LSJS2LOS2LOFFFSS3B1MS4ABLOSS3HUB4ABLO3RZRSS3C16S4ABLOS3LSJ2T0S1N3HUB4ABLO4UBHI2NS3RZR3RSR3NSRSSS4ABLO3LSJ2T03C16S4ABLO3LSJ2T03C16S2T1S3HUB4ABLO3RZRS3HUB4ABLO3RZRSS3LSJ2T0S3HUB4ABLO3RZRS3HUB4ABLO3RZRS3LSJS3LSJ2T0S2HBSSSS2LOS2LOS3LSJ2T0S2HBS4CEIL2LO1N4UBHI2K4S3LSJ2T0S3LSJ2T0S4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS3LSJSSS2LOS2LOS4ABLOSSS4ABLO3LSJ2T03C16S4ABLOS3HUB4ABLO3RZRS4UBHI1HS3HUB4ABLO3RZRS2LOS2LOS2LOS2HBSSS3LSJ3C16S3LSJ3C16S3LSJS3LSJ2T0S4ABLOS3LSJ2T0S1N3HUB4ABLO4UBHI2NS3RZR3RSR3NSRS4ABLO3LSJ2T03C16S3NSRS3NSRS3NSRS2LOS2LOS4CEIL2LO1N3HUB4ABLO4UBHI3LSJ2T13RZR3RSR3RSM2DX1HS3LSJ2T0S3LSJ2T0SS4ABLOS2HBS2T1S2T1S4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS3NSRS4ABLOS2HBS3HUB4ABLO3RZRS4ABLOS3HUB4ABLO3RZRS2LOS2LOSSSS4ABLO3LSJ2T03C16S3LSJS4ABLOFFFS3LSJ2T0S3LSJ2T0S2K4S4CEIL2LO1N4UBHI3HspS4CEIL2LO1N4UBHI3HspSSS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspFS3LSJSSSS3HUB4ABLO3RZRS3LSJ2T0S4ABLO3LSJ2T03C16S3LSJ2T0S4CEIL2LO4UBHISSS4CEIL2LO2T1S4ABLOS3LSJ2T0S3HUB4ABLO3RZRS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspSS1N3HUB4ABLO4UBHI3RZRS1N3HUB4ABLO4UBHI3RZRS2T13C16SS2T1S3HUB4ABLO3RZRFS2LOS2LOS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS2HBS3HUB4ABLO3RZRS1NSS1NSSS4CEIL2LO2T13C16S4ABLOS4ABLOS4CEIL2LO1N4UBHIS4ABLOSSS4ABLOS2LOS2LOS3LSJ3C16S3HUB4ABLO3RZRS3LSJ2T0S3CX0S3C16S4CEIL2LO1N4UBHI2K4S3HspSSS3HUB4ABLO3RZRS3LSJ2T0S3HUB4ABLO3RZRSS2LOS2LOSS3HUB4ABLO3RZRS3B1MS3HUB4ABLO3RZRS4ABLOS3LSJ2T0S3HUB4ABLO3RZRSSS3LSJ2T0SS3NSR2K0S3NSR2K1S1N2K2S3HUB3RZE2K32RZS3HUB4ABLO3LSJ3RZE2K32K42DXS3HUB4ABLO3RZRS3LSJ2T0SSS4ABLOS3LSJ2T0SSFS2LOS2LOS1NS1NS3HUB4ABLO3RZRS4ABLOS3HUB4ABLO3RZRSS3LSJS3LSJ2T0S3LSJ2T0S4ABLOS2LOS2LOS3HUB4ABLO3RZRS3LSJ2T0SS4CEIL2LO2T1S3HUB4ABLO3RZRS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4ABLOS3HUB4ABLO3RZRS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspSSS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HSS4CEIL4UBHIS3LSJS3LSJ2T0S4ABLO3LSJ2NS3RZR3RZE3RSR3RSM3NSRS3LSJ2T0SS3LSJ2T0S4ABLOS4CEIL2LO2T13C16SS2K4S4ABLO3LSJ2T03C16SSS3LSJ3C16S4ABLO3LSJ2T03C16S4ABLOSSS3LSJ2T0S4CEIL2LO1N4UBHIS3LSJ2T0".
assert (C16 : 1 <= c <= 16) by (rewrite <- HC; rewrite Z.shiftr_div_pow2 by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp + -128 - 32, bv_unsigned sp + -128); (t + 2800, t + 3168); (UB - 16, UB + n); (AB, AB + 16)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
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
    assert (LH' : 16 < rz_size n -> rw_cells bsegs mm AB [C8 j1; C8 j2]) end.
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
    assert (LH : 16 < rz_size n -> rw_cells bsegs mm AB [C8 j1; C8 j2]) end.
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
